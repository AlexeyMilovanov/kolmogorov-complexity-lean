/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.StateMachine

/-!
# Computability of the Fighter Construction Operations

Part of blueprint node `fighter_event_transition_computable`, the computability of the
fighter's event transition. This module proves that the individual operations the
transition is assembled from are computable:

* `computable_fighterStageConstruction`: the initialization `fighter_construction` of a phase
  (retained coordinates, extension prices, backed initial indices, winning role and dummy),
  built from private computability lemmas for the referee preprocessing, the price table,
  the initial index lists, the stage outputs, the role selection, and the request funding;
* `computable_fighterAllocate`: the guarded allocator `fighterAllocate`;
* `computable_fighterSafe`: the safety test `fighterSafe`;
* `computable_fighterPayoff` and `computable_fighterFulfillReady`: a single payoff request
  and the fold of payoff requests over the pending list;
* `computable_counterGameTargetReached`: the test whether a decoded counter game's referee
  reaches its target.

The modules `Allocations` and `GameTransitions` import these facts to assemble the
computability of the full event transition and of the game strategy.
-/

namespace Kolmogorov.Milovanov

/-- From the level and the padding, the query list, the encoded normalized referee tree,
and the retained coordinates of the family's referee are computable, using the family's
computable referee code and the level scales. No admissibility assumption is needed, and
zero padding is included. -/
private theorem computable_constructionPreprocess
    (P : FighterParams) :
    Computable (fun a : ℕ × ℕ =>
      let m := levelInput a.1 a.2
      let tree := P.family.tree a.1 a.2 m
      (tree.queries, (tree.normalize (constructedLiteralConstant P.literal a.1)).encode,
        retainedCoordinateList (constructedLiteralConstant P.literal a.1) m tree)) := by
  let step (stack : List (List Coordinate)) (i : ℕ ⊕ Coordinate) : List (List Coordinate) :=
    Sum.casesOn i (fun _ => [] :: stack)
      (fun q => (q :: (stack.getD 1 [] ++ stack.getD 0 [])) :: stack.drop 2)
  have hstep : Primrec₂ step := by
    change Primrec (fun a : List (List Coordinate) × (ℕ ⊕ Coordinate) =>
      (Sum.casesOn a.2 (fun _ => [] :: a.1)
        (fun q => (q :: (a.1.getD 1 [] ++ a.1.getD 0 [])) :: a.1.drop 2) :
          List (List Coordinate)))
    apply Primrec.sumCasesOn Primrec.snd
    · exact (Primrec.list_cons.comp (Primrec.const [])
        (Primrec.fst.comp Primrec.fst)).to₂
    · have hs : Primrec (fun a :
          (List (List Coordinate) × (ℕ ⊕ Coordinate)) × Coordinate => a.1.1) :=
        Primrec.fst.comp Primrec.fst
      have hn := (Primrec.list_getD ([] : List Coordinate)).comp hs (Primrec.const 1)
      have hy := (Primrec.list_getD ([] : List Coordinate)).comp hs (Primrec.const 0)
      exact (Primrec.list_cons.comp
        (Primrec.list_cons.comp Primrec.snd (Primrec.list_append.comp hn hy))
        (Primrec.list_drop.comp (Primrec.const 2) hs)).to₂
  have hfold (tree : QueryTree) (stack : List (List Coordinate)) :
      tree.encode.foldl step stack = tree.queries :: stack := by
    induction tree generalizing stack with
    | leaf out => rfl
    | node q no yes ihno ihyes =>
      simp only [QueryTree.encode, List.foldl_append, ihno, ihyes,
        List.foldl_cons, List.foldl_nil]
      simp [step, QueryTree.queries]
  have hrun : Primrec (fun code : QueryTree.Code => (code.foldl step []).getD 0 []) := by
    have hs : Primrec₂ (fun (_ : QueryTree.Code)
        (u : List (List Coordinate) × (ℕ ⊕ Coordinate)) => step u.1 u.2) :=
      (hstep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
    exact (Primrec.list_getD []).comp
      (Primrec.list_foldl Primrec.id (Primrec.const []) hs) (Primrec.const 0)
  have hm : Computable (fun a : ℕ × ℕ => levelInput a.1 a.2) :=
    Primrec.nat_add.to_comp.comp
      (primrec_levelScale.to_comp.comp Computable.snd) Computable.fst
  have ht := P.family.tree_computable.comp
    (Computable.fst.pair (Computable.snd.pair hm))
  have hqueries : Computable (fun a : ℕ × ℕ =>
      (P.family.tree a.1 a.2 (levelInput a.1 a.2)).queries) := by
    refine (hrun.to_comp.comp ht).of_eq ?_
    intro a
    simp only [hfold, List.getD_cons_zero]
  have hc : Computable (fun a : ℕ × ℕ => constructedLiteralConstant P.literal a.1) :=
    Primrec.nat_add.to_comp.comp Computable.fst (Computable.const P.literal.cV)
  have hpre := referee_preprocessing_computable.comp (hc.pair (hm.pair ht))
  refine (hqueries.pair hpre).of_eq ?_
  intro a
  simp only [QueryTree.decode_encode, Option.getD_some]

/-- The table of extension prices of a supplied coordinate list is computable: deduplicate
the list and map the total extension-price algorithm over it, using the level scale and
the natural subtraction of padding from each threshold. This includes the algorithm's
defaults for malformed candidates and small scales. -/
private theorem computable_coordinatePrices
    (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × Candidate × List Coordinate =>
      coordinatePriceTable P.B P.lam P.n₀ (levelScale a.2.1)
        a.1 a.2.2.1 a.2.2.2) := by
  let A := ℕ × ℕ × Candidate × List Coordinate
  have hlist : Computable (fun a : A => a.2.2.2.eraseDups) :=
    primrec_eraseDups.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hn : Computable (fun a : A × Coordinate => levelScale a.1.2.1) :=
    primrec_levelScale.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hc : Computable (fun a : A × Coordinate => a.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hx : Computable (fun a : A × Coordinate => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hq : Computable (fun a : A × Coordinate => a.2.2 - a.1.1) :=
    Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.fst)
  exact Computable.list_map hlist
    ((compute_extension_price_computable P.B).comp
      ((Computable.const P.lam).pair ((Computable.const P.n₀).pair
        (hn.pair (hc.pair (hx.pair hq)))))).to₂

/-- The initial index list of one coordinate is computable from the verified candidate's
finite past-extension table and a supplied permanent allocation list: decode, check the
curried pair encoding and the input-length bound, and deduplicate. Invalid candidates are
allowed. -/
private theorem computable_fighterInitialIndices
    (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × Candidate × List AllocatedDirective × Coordinate =>
      fighterInitialIndices P a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) := by
  let A := ℕ × ℕ × Candidate × List AllocatedDirective × Coordinate
  have hd : Computable (fun a : A => a.1) := Computable.fst
  have hl : Computable (fun a : A => a.2.1) := Computable.fst.comp Computable.snd
  have hc : Computable (fun a : A => a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have ha : Computable (fun a : A => a.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hq : Computable (fun a : A => a.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hn := primrec_levelScale.to_comp.comp hl
  have hN := primrec_levelUpper.to_comp.comp hl
  have ht := Computable.snd.comp hc
  let base (a : A) := triple a.2.2.2.2.1 (a.2.2.2.2.2 - a.1) a.2.2.1.1
  have hbaseArgs : Computable (fun a : A =>
      (a.2.2.2.2.1, a.2.2.2.2.2 - a.1, a.2.2.1.1)) :=
    ((Computable.fst.comp hq).pair
      ((Primrec.nat_sub.to_comp.comp (Computable.snd.comp hq) hd).pair
        (Computable.fst.comp hc)))
  have hbase := triple_computable.1.comp hbaseArgs
  have hstage := (canonical_enumeration_spec_outputs P.B).1.comp hN ht
  have hvalid := (canonical_enumeration_spec_prefix_computable P.B).1.comp hn hc
  have hpair := Computable₂.comp pairCode_computable
    (hbase.comp (Computable.fst : Computable (Prod.fst : A × BitString → A))) Computable.snd
  have hmem := (canonical_enumeration_spec_outputs P.B).2.2.comp
    ((hN.comp Computable.fst).pair ((ht.comp Computable.fst).pair hpair))
  have holdPred : Computable (fun a : A × BitString =>
      decide (a.2 ∈ pastExtensionIndices P.B (levelScale a.1.2.1) a.1.2.2.1
        (levelScale a.1.2.1) (base a.1))) := by
    refine (Primrec.and.to_comp.comp (hvalid.comp Computable.fst) hmem).of_eq ?_
    intro a
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    change (validCandidate P.B (levelScale a.1.2.1) a.1.2.2.1 = true ∧
      pairCode (base a.1) a.2 ∈
        stageOutputs P.B (levelUpper a.1.2.1) a.1.2.2.1.2) ↔ _
    cases hv : validCandidate P.B (levelScale a.1.2.1) a.1.2.2.1 with
    | false => simp [pastExtensionIndices, hv]
    | true =>
      constructor
      · intro h
        exact (mem_past_extension_indices P.B (levelScale a.1.2.1) a.1.2.2.1
          (levelScale a.1.2.1) (base a.1) a.2 hv).mpr h.2
      · intro h
        exact ⟨rfl, (mem_past_extension_indices P.B (levelScale a.1.2.1) a.1.2.2.1
          (levelScale a.1.2.1) (base a.1) a.2 hv).mp h⟩
  have hold := computable_filter
    (Computable.list_map hstage (decodeSecond_computable.comp Computable.snd).to₂) holdPred.to₂
  have houtput : Primrec AllocatedDirective.output :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv
        (e := AllocatedDirective.equivProd)))))))
  let pred (a : A) (e : AllocatedDirective) : Prop :=
    e.input.length + 1 ≤ levelUpper a.2.1 + a.1 ∧
      pairCode (base a) (decodeSecond e.output) = e.output
  have he : Computable (fun a : A × AllocatedDirective => a.2.output) :=
    houtput.to_comp.comp Computable.snd
  have hlength := Computable.list_length.comp
    (AllocatedDirective.primrec_input.to_comp.comp
      (Computable.snd : Computable (Prod.snd : A × AllocatedDirective → AllocatedDirective)))
  have hlimit : Computable (fun a : A × AllocatedDirective => levelUpper a.1.2.1 + a.1.1) :=
    (Primrec.nat_add.to_comp.comp hN hd).comp Computable.fst
  have heq := Primrec.eq.decide.to_comp.comp
    (Computable₂.comp pairCode_computable (hbase.comp Computable.fst)
      (decodeSecond_computable.comp he)) he
  have hp : Computable (fun a : A × AllocatedDirective => decide (pred a.1 a.2)) :=
    (Primrec.and.to_comp.comp
      (Primrec.nat_le.decide.to_comp.comp (Computable.succ.comp hlength) hlimit) heq).of_eq
        (fun a => by
          apply Bool.eq_iff_iff.mpr
          simp [pred, base])
  have haddedMap := Computable.list_map
    (computable_filter ha hp.to₂)
    (decodeSecond_computable.comp he).to₂
  have hadded : Computable (fun a : A => a.2.2.2.1.filterMap (fun e =>
      if pred a e then some (decodeSecond e.output) else none)) := by
    refine haddedMap.of_eq ?_
    intro a
    induction a.2.2.2.1 with
    | nil => rfl
    | cons e es ih =>
      by_cases h : pred a e <;> simp [h, ih]
  exact primrec_eraseDups.to_comp.comp
    (Computable.list_append.comp hold hadded)

/-- The finite unconditional output list at any threshold and tick is computable: combine
the base-machine stage table with the length-filtered permanent allocations, respecting
both branch guards, and deduplicate the result. -/
private theorem computable_fighterStageOutputs
    (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × ℕ × List AllocatedDirective =>
      fighterStageOutputList P a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  let A := ℕ × ℕ × ℕ × List AllocatedDirective
  have hd : Computable (fun a : A => a.1) := Computable.fst
  have hk : Computable (fun a : A => a.2.1) := Computable.fst.comp Computable.snd
  have ht : Computable (fun a : A => a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have ha : Computable (fun a : A => a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hb := (canonical_enumeration_spec_outputs P.B).1.comp
    (Primrec.nat_sub.to_comp.comp hk hd) ht
  have hbase := computable_ite_decide
    (Primrec.nat_le.decide.to_comp.comp hd hk) hb (Computable.const [])
  have hp : Computable₂ (fun (a : A) (e : AllocatedDirective) =>
      decide (e.input.length ≤ a.2.1 - 1)) :=
    (Primrec.nat_le.decide.to_comp.comp
      (Computable.list_length.comp
        (AllocatedDirective.primrec_input.to_comp.comp Computable.snd))
      (Primrec.nat_sub.to_comp.comp (hk.comp Computable.fst) (Computable.const 1))).to₂
  have houtput : Primrec AllocatedDirective.output :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv
        (e := AllocatedDirective.equivProd)))))))
  have hadded := Computable.list_map (computable_filter ha hp)
    (houtput.to_comp.comp Computable.snd).to₂
  have hguard : Computable (fun a : A => decide (1 ≤ a.2.1 ∧ 1 ≤ a.1)) :=
    (Primrec.and.to_comp.comp
      (Primrec.nat_le.decide.to_comp.comp (Computable.const 1) hk)
      (Primrec.nat_le.decide.to_comp.comp (Computable.const 1) hd)).of_eq
        (fun a => by simp)
  exact primrec_eraseDups.to_comp.comp
    (Computable.list_append.comp hbase
      (computable_ite_decide hguard hadded (Computable.const [])))

/-- For a family of semantic games with computable encodings, the initial winner, the
role-selected game code, and its initial position code are computable, by the encoded
solver and its agreement theorem. All games are allowed, including zero budgets and empty
tables. -/
private theorem computable_gameRoles
    {α : Type*} [Primcodable α] (game : α → FiniteCounterGame)
    (hgame : Computable (fun a => (game a).encode)) :
    Computable (fun a => ((game a).controlWinningPlayer.encode,
      (game a).controlWinningPlayer.initialPosition.encode,
      (game a).winner (game a).initialPosition)) := by
  have h0 := Computable.fst.comp hgame
  have h1 := Computable.fst.comp (Computable.snd.comp hgame)
  have h2 := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hgame))
  have h3 := Computable.fst.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp hgame)))
  have h4 := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp hgame))))
  have h5 := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hgame)))))
  have h6 := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hgame))))))
  have h7 := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hgame))))))
  have hpos : Computable (fun a => (game a).initialPosition.encode) := h2.pair (h4.pair h4)
  have hwinner : Computable (fun a => (game a).winner (game a).initialPosition) := by
    refine (Computable.fst.comp
      (finite_counter_game_computable_winner.1.comp (hgame.pair hpos))).of_eq ?_
    intro a
    rw [solve_counter_game_code_agrees]
    rfl
  have hexchange : Computable (fun a => (game a).exchangeRoles.encode) :=
    h0.pair (h1.pair (h2.pair (h3.pair (h4.pair (h5.pair
      (h6.pair (Primrec.not.to_comp.comp h7)))))))
  have hchosen : Computable (fun a => (game a).controlWinningPlayer.encode) := by
    refine (Computable.cond hwinner hexchange hgame).of_eq ?_
    intro a
    cases h : (game a).winner (game a).initialPosition <;>
      simp [FiniteCounterGame.controlWinningPlayer, h]
  have hcounters := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hchosen))
  have hbudget := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp hchosen))))
  have hchosenPos : Computable (fun a =>
      (game a).controlWinningPlayer.initialPosition.encode) := hcounters.pair (hbudget.pair hbudget)
  exact hchosen.pair (hchosenPos.pair hwinner)

/-- Funding the requests of an arbitrary finite phase is computable: compare the encoded
prices with the cardinalities of the index lists, removing fulfilled coordinates and
duplicates. Padding is unused by this operation. No backing or reachability invariant is
assumed. -/
private theorem computable_fundRequests :
    Computable (fun a : FighterPhase × List Coordinate => a.1.fundRequests 0 a.2) := by
  have hc : Primrec (fun p : FighterPhase => (p.game 0).coordinates) :=
    primrec_eraseDups.comp
      (Primrec.fst.comp FighterPhase.primrec_gameCode)
  have hidx : Primrec₂ (fun (q : Coordinate) (l : List Coordinate) => l.idxOf q) := by
    have hb : (instBEqOfDecidableEq : BEq Coordinate) = (inferInstance : BEq Coordinate) :=
      lawful_beq_subsingleton _ _
    refine (Primrec.list_idxOf :
      Primrec₂ (@List.idxOf Coordinate instBEqOfDecidableEq)).of_eq ?_
    intro q l
    change @List.idxOf Coordinate instBEqOfDecidableEq q l =
      @List.idxOf Coordinate (inferInstance : BEq Coordinate) q l
    rw [hb]
  have hi := hidx.comp Primrec.snd (hc.comp
    (Primrec.fst : Primrec (Prod.fst : FighterPhase × Coordinate → FighterPhase)))
  have hm : Primrec (fun a : FighterPhase × Coordinate =>
      decide (a.2 ∈ (a.1.game 0).coordinates)) :=
    (list_mem_decide_primrec.comp Primrec.snd (hc.comp Primrec.fst)).of_eq
      (fun a => by apply decide_eq_decide.mpr; rfl)
  have hlist := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (FighterPhase.primrec_indices.comp Primrec.fst) hi) (Primrec.const [])
  have hcard : Primrec (fun xs : List BitString => xs.toFinset.card) := by
    refine (Primrec.list_length.comp primrec_eraseDups).of_eq ?_
    intro xs
    have he : xs.toFinset = xs.eraseDups.toFinset := by
      ext x
      simp only [List.mem_toFinset, mem_eraseDups_list]
    rw [he, List.toFinset_card_of_nodup (nodup_eraseDups_list xs)]
  have hcount : Primrec (fun a : FighterPhase × Coordinate =>
      (a.1.indicesAt 0 a.2).card) := by
    refine (Primrec.ite hm.primrecPred (hcard.comp hlist) (Primrec.const 0)).of_eq ?_
    intro a
    by_cases h : a.2 ∈ (a.1.game 0).coordinates <;>
      simp only [FighterPhase.indicesAt, h, ↓reduceIte, Finset.card_empty]
  have hprices : Primrec (fun a : FighterPhase × Coordinate => (a.1.game 0).prices) :=
    Primrec.fst.comp (Primrec.snd.comp
      (FighterPhase.primrec_gameCode.comp Primrec.fst))
  have hvalue := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp hprices hi) (Primrec.const 0)
  have hprice : Primrec (fun a : FighterPhase × Coordinate => (a.1.game 0).price a.2) :=
    (Primrec.ite hm.primrecPred hvalue (Primrec.const 0)).of_eq (fun a => rfl)
  have hargs : Primrec (fun a : (FighterPhase × List Coordinate) × Coordinate => (a.1.1, a.2)) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  have hfund := Primrec.list_filter (hc.comp Primrec.fst)
    ((Primrec.nat_le.comp (hprice.comp hargs) (hcount.comp hargs)).decide).to₂
  have hpend := Primrec.list_append.comp
    (FighterPhase.primrec_pending.comp Primrec.fst) hfund
  have hp : Primrec₂ (fun (a : FighterPhase × List Coordinate) (q : Coordinate) =>
      decide (q ∉ a.2)) :=
    (Primrec.not.comp (list_mem_decide_primrec.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst))).to₂.of_eq (fun a q => by simp)
  have hnew := primrec_eraseDups.comp (Primrec.list_filter hpend hp)
  exact ((FighterPhase.primrec_mk
    (FighterPhase.primrec_level.comp Primrec.fst)
    (FighterPhase.primrec_candidate.comp Primrec.fst)
    (FighterPhase.primrec_snapshot.comp Primrec.fst)
    (FighterPhase.primrec_initialAllocations.comp Primrec.fst)
    (FighterPhase.primrec_gameCode.comp Primrec.fst)
    (FighterPhase.primrec_indices.comp Primrec.fst)
    (FighterPhase.primrec_officialCode.comp Primrec.fst)
    (FighterPhase.primrec_liveCounters.comp Primrec.fst)
    (FighterPhase.primrec_controlledRemaining.comp Primrec.fst)
    (FighterPhase.primrec_opponentRemaining.comp Primrec.fst)
    (FighterPhase.primrec_buffer.comp Primrec.fst) hnew
    (FighterPhase.primrec_dummy.comp Primrec.fst)
    (FighterPhase.primrec_dummyIssued.comp Primrec.fst)
    (FighterPhase.primrec_controlledPlayer.comp Primrec.fst)).of_eq
      (fun a => rfl)).to_comp

/-- Blueprint node `fighter_event_transition_computable`, phase initialization: the
construction `fighter_construction` of one phase from its finite snapshot and permanent
allocation table is computable. It computes the retained coordinates, prices, backed initial
indices, and the winning role and dummy, using the encoded solver's computability and
agreement theorems for role selection. This statement covers every input record, including
malformed candidates and zero padding. -/
theorem computable_fighterStageConstruction (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × Candidate × FighterState =>
      fighter_construction P a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  let A := ℕ × ℕ × Candidate × FighterState
  have hd : Computable (fun a : A => a.1) := Computable.fst
  have hl : Computable (fun a : A => a.2.1) := Computable.fst.comp Computable.snd
  have hc : Computable (fun a : A => a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun a : A => a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ht := FighterState.primrec_tick.to_comp.comp hs
  have ha := FighterState.primrec_allocated.to_comp.comp hs
  have hf := FighterState.primrec_fulfilled.to_comp.comp hs
  have hn := primrec_levelScale.to_comp.comp hl
  have hm : Computable (fun a : A => levelInput a.1 a.2.1) :=
    Primrec.nat_add.to_comp.comp hn hd
  let tree (a : A) := P.family.tree a.1 a.2.1 (levelInput a.1 a.2.1)
  let coords (a : A) := retainedCoordinateList
    (constructedLiteralConstant P.literal a.1) (levelInput a.1 a.2.1) (tree a)
  have hpre := (computable_constructionPreprocess P).comp
    (hd.pair hl)
  have hqueries : Computable (fun a : A => (tree a).queries) := Computable.fst.comp hpre
  have htree : Computable (fun a : A =>
      ((tree a).normalize (constructedLiteralConstant P.literal a.1)).encode) :=
    Computable.fst.comp (Computable.snd.comp hpre)
  have hcoords : Computable coords := Computable.snd.comp (Computable.snd.comp hpre)
  have hprices := (computable_coordinatePrices P).comp
    (hd.pair (hl.pair (hc.pair hcoords)))
  let indices (a : A) := coords a |>.map
    (fighterInitialIndices P a.1 a.2.1 a.2.2.1 a.2.2.2.allocated)
  have hindices : Computable indices := Computable.list_map hcoords
    ((computable_fighterInitialIndices P).comp
      ((hd.comp Computable.fst).pair ((hl.comp Computable.fst).pair
        ((hc.comp Computable.fst).pair ((ha.comp Computable.fst).pair Computable.snd))))).to₂
  have hcard : Computable (fun xs : List BitString => xs.toFinset.card) := by
    refine (Computable.list_length.comp
      primrec_eraseDups.to_comp).of_eq ?_
    intro xs
    have he : xs.toFinset = xs.eraseDups.toFinset := by
      ext x
      simp only [List.mem_toFinset, mem_eraseDups_list]
    rw [he, List.toFinset_card_of_nodup (nodup_eraseDups_list xs)]
  let counters (a : A) := (indices a).map (fun xs => xs.toFinset.card)
  have hcounters : Computable counters :=
    Computable.list_map hindices (hcard.comp Computable.snd).to₂
  have hout := (computable_fighterStageOutputs P).comp
    (hd.pair (hm.pair (ht.pair ha)))
  have hyes : Computable (fun a : A => (tree a).queries.filter (fun q =>
      decide (q.1 ∈ fighterStageOutputs P a.1 q.2 a.2.2.2.tick a.2.2.2.allocated))) := by
    have hargs : Computable (fun a : A × Coordinate =>
        (a.1.1, a.2.2, a.1.2.2.2.tick, a.1.2.2.2.allocated)) :=
      ((hd.comp Computable.fst).pair ((Computable.snd.comp Computable.snd).pair
        ((ht.comp Computable.fst).pair (ha.comp Computable.fst))))
    have hout' := (computable_fighterStageOutputs P).comp hargs
    have hmem := list_mem_decide_primrec.to_comp.comp
      (Computable.fst.comp Computable.snd) hout'
    have hpred : Computable (fun a : A × Coordinate =>
        decide (a.2.1 ∈ fighterStageOutputs P a.1.1 a.2.2
          a.1.2.2.2.tick a.1.2.2.2.allocated)) := by
      refine hmem.of_eq ?_
      intro a
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, fighterStageOutputs, List.mem_toFinset]
    exact computable_filter hqueries hpred.to₂
  have hK : Computable (fun a : A =>
      (fighterStageOutputs P a.1 (levelInput a.1 a.2.1)
        a.2.2.2.tick a.2.2.2.allocated).card) := hcard.comp hout
  let R (a : A) := P.c₁ * 2 ^ (levelUpper a.2.1 - levelScale a.2.1)
  have hR : Computable R := Primrec.nat_mul.to_comp.comp (Computable.const P.c₁)
    (primrec_two_pow_aux.to_comp.comp (Primrec.nat_sub.to_comp.comp
      (primrec_levelUpper.to_comp.comp hl) hn))
  let original (a : A) := finite_counter_game (coords a)
    (coordinatePriceTable P.B P.lam P.n₀ (levelScale a.2.1) a.1 a.2.2.1 (coords a))
    (counters a) ((tree a).queries.filter (fun q =>
      decide (q.1 ∈ fighterStageOutputs P a.1 q.2 a.2.2.2.tick a.2.2.2.allocated)))
    (R a) ((tree a).normalize (constructedLiteralConstant P.literal a.1))
    (fighterStageOutputs P a.1 (levelInput a.1 a.2.1)
      a.2.2.2.tick a.2.2.2.allocated).card
  have hgame : Computable (fun a => (original a).encode) :=
    hcoords.pair (hprices.pair (hcounters.pair (hyes.pair
      (hR.pair (htree.pair (hK.pair (Computable.const true)))))))
  have hroles := computable_gameRoles original hgame
  have hchosen := Computable.fst.comp hroles
  have hposition := Computable.fst.comp (Computable.snd.comp hroles)
  have hwinner := Computable.snd.comp (Computable.snd.comp hroles)
  have hfresh : Computable (fun a : A => fighterFreshString a.1
      ((tree a).queries.map Prod.fst ++ fighterStageOutputList P a.1
        (levelInput a.1 a.2.1) a.2.2.2.tick a.2.2.2.allocated)) := by
    have hlist := Computable.list_append.comp
      (Computable.list_map hqueries (Computable.fst.comp Computable.snd).to₂) hout
    have hstep : Computable₂ (fun (_ : A) (u : ℕ × BitString) => max u.1 u.2.length) :=
      (Primrec.nat_max.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.list_length.comp (Computable.snd.comp Computable.snd))).to₂
    exact Primrec.list_replicate.to_comp.comp
      (Computable.succ.comp (Computable.list_foldl hlist (Computable.const 0) hstep))
      (Computable.const false)
  let dummy (a : A) := if (original a).winner (original a).initialPosition then
    some (fighterFreshString a.1 ((tree a).queries.map Prod.fst ++
      fighterStageOutputList P a.1 (levelInput a.1 a.2.1) a.2.2.2.tick a.2.2.2.allocated))
    else none
  have hdummy : Computable dummy := by
    refine (Computable.cond hwinner (Computable.option_some.comp hfresh)
      (Computable.const none)).of_eq ?_
    intro a
    cases h : (original a).winner (original a).initialPosition <;> simp [dummy, h]
  let phase (a : A) : FighterPhase := ⟨a.2.1, a.2.2.1, a.2.2.2.schedule,
    a.2.2.2.allocated, (original a).controlWinningPlayer.encode, indices a,
    (original a).controlWinningPlayer.initialPosition.encode, counters a, R a, R a,
    List.replicate (coords a).length 0, [], dummy a, false, false⟩
  have hphaseRaw :=
    (Primrec.of_equiv_symm (e := FighterPhase.equivProd)).to_comp.comp
      (hl.pair (hc.pair ((FighterState.primrec_schedule.to_comp.comp hs).pair
        (ha.pair (hchosen.pair (hindices.pair (hposition.pair (hcounters.pair (hR.pair
          (hR.pair ((Primrec.list_replicate.to_comp.comp
            (Computable.list_length.comp hcoords) (Computable.const 0)).pair
              ((Computable.const []).pair (hdummy.pair
                ((Computable.const false).pair (Computable.const false)))))))))))))))
  have hphase : Computable phase := hphaseRaw.of_eq (fun a => rfl)
  exact ((computable_fundRequests).comp
    (hphase.pair hf)).of_eq (fun a => rfl)

private theorem primrec_fighterInputs : Primrec₂ fighterInputs := by
  have hf : Primrec (fun xs : List BitString => xs.map (false :: ·)) :=
    Primrec.list_map Primrec.id
      (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂
  have ht : Primrec (fun xs : List BitString => xs.map (true :: ·)) :=
    Primrec.list_map Primrec.id
      (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂
  have hstep : Primrec (fun xs : List BitString => xs.map (false :: ·) ++ xs.map (true :: ·)) :=
    Primrec.list_append.comp hf ht
  have hrec := Primrec.nat_rec (f := fun _ : ℕ => ([[]] : List BitString))
    (g := fun _ u => u.2.map (false :: ·) ++ u.2.map (true :: ·))
    (Primrec.const [[]]) (hstep.comp (Primrec.snd.comp Primrec.snd)).to₂
  exact hrec.of_eq (fun d n => by
    induction n with
    | zero => rfl
    | succ n ih => simp only [fighterInputs, ih])

private theorem primrec_freshInput :
    Primrec (fun a : ℕ × ℕ × List AllocatedDirective =>
      if a.2.1 = 0 then none else
        (fighterInputs a.1 (a.2.1 - 1)).find? (fun p =>
          !a.2.2.any (fun e => e.input == p))) := by
  have hentries : Primrec (fun a : (ℕ × ℕ × List AllocatedDirective) × BitString => a.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hp : Primrec₂ (fun (a : (ℕ × ℕ × List AllocatedDirective) × BitString)
      (e : AllocatedDirective) => e.input == a.2) :=
    (primrec₂_beq.comp
      (AllocatedDirective.primrec_input.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have hany := list_any_primrec hentries hp
  have hlist : Primrec (fun a : ℕ × ℕ × List AllocatedDirective =>
      fighterInputs a.1 (a.2.1 - 1)) :=
    primrec_fighterInputs.comp Primrec.fst
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    (Primrec.const none) (list_find?_primrec hlist (Primrec.not.comp hany).to₂)

private theorem primrec_stateFail :
    Primrec (fun s : FighterState => { s with failed := true }) := by
  exact (FighterState.primrec_mk
    FighterState.primrec_tick
    FighterState.primrec_schedule
    FighterState.primrec_allocated
    FighterState.primrec_fulfilled (Primrec.const true)
    FighterState.primrec_active
    FighterState.primrec_started
    FighterState.primrec_ended).of_eq (fun s => rfl)

private theorem primrec_stateAppendAllocation :
    Primrec (fun a : FighterState × AllocatedDirective =>
      { a.1 with allocated := a.1.allocated ++ [a.2] }) := by
  exact (FighterState.primrec_mk
    (FighterState.primrec_tick.comp Primrec.fst)
    (FighterState.primrec_schedule.comp Primrec.fst)
    (Primrec.list_concat.comp (FighterState.primrec_allocated.comp Primrec.fst)
      Primrec.snd)
    (FighterState.primrec_fulfilled.comp Primrec.fst)
    (FighterState.primrec_failed.comp Primrec.fst)
    (FighterState.primrec_active.comp Primrec.fst)
    (FighterState.primrec_started.comp Primrec.fst)
    (FighterState.primrec_ended.comp Primrec.fst)).of_eq (fun s => rfl)

private theorem primrec_allocateSuccess :
    Primrec (fun a : ((ℕ × ℕ × DirectiveKind × ℕ × BitString) × FighterState) ×
        (FighterPhase × BitString) =>
      (fighterAbortAbove a.1.1.1 a.1.1.2.1
        { a.1.2 with allocated := a.1.2.allocated ++
          [AllocatedDirective.mk a.1.1.2.1 a.2.1.candidate a.1.2.tick a.1.1.2.2.1
            a.1.1.2.2.2.1 a.2.2 a.1.1.2.2.2.2] }, true)) := by
  have ht : Primrec (fun a : ((ℕ × ℕ × DirectiveKind × ℕ × BitString) × FighterState) ×
      (FighterPhase × BitString) => a.1.1) := Primrec.fst.comp Primrec.fst
  have hd := Primrec.fst.comp ht
  have hl := Primrec.fst.comp (Primrec.snd.comp ht)
  have hk := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ht))
  have hr := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ht)))
  have hout := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ht)))
  have hs : Primrec (fun a : ((ℕ × ℕ × DirectiveKind × ℕ × BitString) × FighterState) ×
      (FighterPhase × BitString) => a.1.2) := Primrec.snd.comp Primrec.fst
  have hc : Primrec (fun a : ((ℕ × ℕ × DirectiveKind × ℕ × BitString) × FighterState) ×
      (FighterPhase × BitString) => a.2.1.candidate) :=
    FighterPhase.primrec_candidate.comp (Primrec.fst.comp Primrec.snd)
  have hp : Primrec (fun a : ((ℕ × ℕ × DirectiveKind × ℕ × BitString) × FighterState) ×
      (FighterPhase × BitString) => a.2.2) := Primrec.snd.comp Primrec.snd
  have he := AllocatedDirective.primrec_mk hl hc
    (FighterState.primrec_tick.comp hs) hk hr hp hout
  have hn := primrec_stateAppendAllocation.comp (hs.pair he)
  exact (primrec_fighterAbortAbove.comp (hd.pair (hl.pair hn))).pair
    (Primrec.const true)

/-- Blueprint node `fighter_event_transition_computable`, allocation: the guarded allocator
`fighterAllocate` is computable. It enumerates strings of the requested length, finds the
first unused input in the permanent graph, and either cancels on saturation or appends an
assignment and aborts larger levels. No phase initialization, payoff, or game strategy is
performed. -/
theorem computable_fighterAllocate :
    Computable (fun a : ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState =>
      fighterAllocate a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2) := by
  apply Primrec.to_comp
  have hd : Primrec (fun a : ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState =>
      a.1) := Primrec.fst
  have hl : Primrec (fun a : ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState => a.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun a : ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun a : ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState => a.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hout : Primrec (fun a : ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState =>
      a.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hs : Primrec (fun a : ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState => a.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have ho := primrec_activeAt.comp (hd.pair (hl.pair hs))
  have hbranch : Primrec (fun a : (ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState) ×
        FighterPhase =>
      let fresh := if a.1.2.2.2.1 = 0 then none else
        (fighterInputs a.1.1 (a.1.2.2.2.1 - 1)).find? (fun p =>
          !a.1.2.2.2.2.2.allocated.any (fun e => e.input == p))
      match fresh with
      | none => (fighterCancel a.1.1 a.1.2.1 .saturated a.1.2.1
          { a.1.2.2.2.2.2 with failed := true }, false)
      | some p => (fighterAbortAbove a.1.1 a.1.2.1
          { a.1.2.2.2.2.2 with allocated := a.1.2.2.2.2.2.allocated ++
            [AllocatedDirective.mk a.1.2.1 a.2.candidate a.1.2.2.2.2.2.tick a.1.2.2.1
              a.1.2.2.2.1 p a.1.2.2.2.2.1] }, true)) := by
    have hd' : Primrec (fun a : (ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState) ×
        FighterPhase => a.1.1) := hd.comp Primrec.fst
    have hl' : Primrec (fun a : (ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState) ×
        FighterPhase => a.1.2.1) := hl.comp Primrec.fst
    have hr' : Primrec (fun a : (ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState) ×
        FighterPhase => a.1.2.2.2.1) := hr.comp Primrec.fst
    have hs' : Primrec (fun a : (ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState) ×
        FighterPhase => a.1.2.2.2.2.2) := hs.comp Primrec.fst
    have hfresh := primrec_freshInput.comp
      (hd'.pair (hr'.pair (FighterState.primrec_allocated.comp hs')))
    have hfailed := primrec_stateFail.comp hs'
    have hnone := (primrec_fighterCancel.comp
      (hd'.pair (hl'.pair ((Primrec.const PhaseEnd.saturated).pair (hl'.pair hfailed))))).pair
        (Primrec.const false)
    have ht : Primrec (fun a : ((ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState) ×
        FighterPhase) × BitString => a.1.1) := Primrec.fst.comp Primrec.fst
    have hparams := (hd.comp ht).pair ((hl.comp ht).pair
      ((hk.comp ht).pair ((hr.comp ht).pair (hout.comp ht))))
    have hsuccess := primrec_allocateSuccess.comp
      ((hparams.pair (hs.comp ht)).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
    exact (Primrec.option_casesOn hfresh hnone hsuccess.to₂).of_eq (fun a => by
      dsimp only
      cases h : (if a.1.2.2.2.1 = 0 then none else
        (fighterInputs a.1.1 (a.1.2.2.2.1 - 1)).find? (fun p =>
          !a.1.2.2.2.2.2.allocated.any (fun e => e.input == p))) <;> rfl)
  exact (Primrec.option_casesOn ho (hs.pair (Primrec.const false)) hbranch.to₂).of_eq
    (fun a => by unfold fighterAllocate; cases a.2.2.2.2.2.activeAt a.1 a.2.1 <;> rfl)

/-- The safety test `fighterSafe P` is computable in the padding, the tick, and the
coordinate: the half padding must not exceed the coordinate's threshold, and its string
must already be an output of the base machine's stage table at the shifted threshold. -/
theorem computable_fighterSafe (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × Coordinate => fighterSafe P a.1 a.2.1 a.2.2) := by
  have hd : Primrec (fun a : ℕ × ℕ × Coordinate => halfPadding a.1) :=
    Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have hr : Primrec (fun a : ℕ × ℕ × Coordinate => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ht : Computable (fun a : ℕ × ℕ × Coordinate => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hx : Computable (fun a : ℕ × ℕ × Coordinate => a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hm := (canonical_enumeration_spec_outputs P.B).2.2.comp
    ((Primrec.nat_sub.comp hr hd).to_comp.pair (ht.pair hx))
  exact (Primrec.and.to_comp.comp ((Primrec.nat_le.comp hd hr).decide.to_comp) hm).of_eq
    (fun a => by apply Bool.eq_iff_iff.mpr; simp [fighterSafe])

private theorem primrec_removeRequest :
    Primrec (fun a : FighterPhase × Coordinate =>
      { a.1 with pending := a.1.pending.filter (fun r => r != a.2) }) := by
  have hp : Primrec₂ (fun (a : FighterPhase × Coordinate) (r : Coordinate) => r != a.2) :=
    (Primrec.not.comp (primrec₂_beq.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst))).to₂
  have hpend := Primrec.list_filter
    (FighterPhase.primrec_pending.comp Primrec.fst) hp
  exact (FighterPhase.primrec_mk
    (FighterPhase.primrec_level.comp Primrec.fst)
    (FighterPhase.primrec_candidate.comp Primrec.fst)
    (FighterPhase.primrec_snapshot.comp Primrec.fst)
    (FighterPhase.primrec_initialAllocations.comp Primrec.fst)
    (FighterPhase.primrec_gameCode.comp Primrec.fst)
    (FighterPhase.primrec_indices.comp Primrec.fst)
    (FighterPhase.primrec_officialCode.comp Primrec.fst)
    (FighterPhase.primrec_liveCounters.comp Primrec.fst)
    (FighterPhase.primrec_controlledRemaining.comp Primrec.fst)
    (FighterPhase.primrec_opponentRemaining.comp Primrec.fst)
    (FighterPhase.primrec_buffer.comp Primrec.fst) hpend
    (FighterPhase.primrec_dummy.comp Primrec.fst)
    (FighterPhase.primrec_dummyIssued.comp Primrec.fst)
    (FighterPhase.primrec_controlledPlayer.comp Primrec.fst)).of_eq (fun a => rfl)

private theorem primrec_recordPayoff :
    Primrec (fun a : FighterState × Coordinate =>
      { a.1 with
        fulfilled := a.1.fulfilled ++ [a.2]
        active := a.1.active.map (fun (p : FighterPhase) =>
          { p with pending := p.pending.filter (fun r => r != a.2) }) }) := by
  have hp : Primrec₂ (fun (a : FighterState × Coordinate) (p : FighterPhase) =>
      { p with pending := p.pending.filter (fun r => r != a.2) }) :=
    (primrec_removeRequest.comp
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂
  have hm := Primrec.list_map (FighterState.primrec_active.comp Primrec.fst) hp
  exact (FighterState.primrec_mk
    (FighterState.primrec_tick.comp Primrec.fst)
    (FighterState.primrec_schedule.comp Primrec.fst)
    (FighterState.primrec_allocated.comp Primrec.fst)
    (Primrec.list_concat.comp
      (FighterState.primrec_fulfilled.comp Primrec.fst) Primrec.snd)
    (FighterState.primrec_failed.comp Primrec.fst) hm
    (FighterState.primrec_started.comp Primrec.fst)
    (FighterState.primrec_ended.comp Primrec.fst)).of_eq (fun a => rfl)

/-- Blueprint node `fighter_event_transition_computable`, payoff: given a computable guarded
allocator, `fighterPayoff`, which tests and fulfills one pending safe payoff request, is
computable. Only successful allocation appends the coordinate to the fulfilled table and
removes it from remaining pending lists. This is one request, without phase initialization
or closure. -/
theorem computable_fighterPayoff (P : FighterParams)
    (halloc : Computable (fun a : ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState =>
      fighterAllocate a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2)) :
    Computable (fun a : ℕ × ℕ × Coordinate × FighterState =>
      fighterPayoff P a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hd : Computable (fun a : ℕ × ℕ × Coordinate × FighterState => a.1) := Computable.fst
  have hl : Computable (fun a : ℕ × ℕ × Coordinate × FighterState => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hq : Computable (fun a : ℕ × ℕ × Coordinate × FighterState => a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun a : ℕ × ℕ × Coordinate × FighterState => a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ho := primrec_activeAt.to_comp.comp (hd.pair (hl.pair hs))
  have hbranch : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase =>
      if a.1.2.2.1 ∈ a.2.pending ∧ a.1.2.2.1 ∉ a.1.2.2.2.fulfilled ∧
          fighterSafe P a.1.1 a.1.2.2.2.tick a.1.2.2.1 = true then
        let (next, success) := fighterAllocate a.1.1 a.1.2.1 .payoff
          a.1.2.2.1.2 a.1.2.2.1.1 a.1.2.2.2
        if success then
          { next with
            fulfilled := next.fulfilled ++ [a.1.2.2.1]
            active := next.active.map (fun (p : FighterPhase) =>
              { p with pending := p.pending.filter (fun r => r != a.1.2.2.1) }) }
        else next
      else a.1.2.2.2) := by
    have hd' : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase => a.1.1) :=
      hd.comp Computable.fst
    have hl' : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase => a.1.2.1) :=
      hl.comp Computable.fst
    have hq' : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase =>
        a.1.2.2.1) :=
      hq.comp Computable.fst
    have hs' : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase =>
        a.1.2.2.2) :=
      hs.comp Computable.fst
    have hmem := list_mem_decide_primrec.to_comp.comp hq'
      (FighterPhase.primrec_pending.to_comp.comp Computable.snd)
    have hfulfilled := list_mem_decide_primrec.to_comp.comp hq'
      (FighterState.primrec_fulfilled.to_comp.comp hs')
    have hsafe := (computable_fighterSafe P).comp
      (hd'.pair ((FighterState.primrec_tick.to_comp.comp hs').pair hq'))
    have hguard : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase =>
        decide (a.1.2.2.1 ∈ a.2.pending ∧ a.1.2.2.1 ∉ a.1.2.2.2.fulfilled ∧
          fighterSafe P a.1.1 a.1.2.2.2.tick a.1.2.2.1 = true)) :=
      (Primrec.and.to_comp.comp hmem (Primrec.and.to_comp.comp
        (Primrec.not.to_comp.comp hfulfilled)
        (Primrec.eq.decide.to_comp.comp hsafe (Computable.const true)))).of_eq
          (fun a => by apply Bool.eq_iff_iff.mpr; simp)
    have ha := halloc.comp (hd'.pair (hl'.pair ((Computable.const DirectiveKind.payoff).pair
      ((Computable.snd.comp hq').pair ((Computable.fst.comp hq').pair hs')))))
    have hn := Computable.fst.comp ha
    have hy := Computable.snd.comp ha
    have hout := primrec_recordPayoff.to_comp.comp (hn.pair hq')
    have hcomputed := computable_ite_decide
      (Primrec.eq.decide.to_comp.comp hy (Computable.const true)) hout hn
    have hresult : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase =>
        let (next, success) := fighterAllocate a.1.1 a.1.2.1 .payoff
          a.1.2.2.1.2 a.1.2.2.1.1 a.1.2.2.2
        if success then
          { next with
            fulfilled := next.fulfilled ++ [a.1.2.2.1]
            active := next.active.map (fun (p : FighterPhase) =>
              { p with pending := p.pending.filter (fun r => r != a.1.2.2.1) }) }
        else next) :=
      hcomputed.of_eq (fun a => by
        cases fighterAllocate a.1.1 a.1.2.1 .payoff a.1.2.2.1.2 a.1.2.2.1.1 a.1.2.2.2
        rfl)
    exact (computable_ite_decide hguard hresult hs').of_eq (fun a => rfl)
  exact (Computable.option_casesOn (α := ℕ × ℕ × Coordinate × FighterState)
    (β := FighterPhase) (σ := FighterState) ho hs hbranch.to₂).of_eq
      (fun a => by unfold fighterPayoff; cases a.2.2.2.activeAt a.1 a.2.1 <;> rfl)

/-- Blueprint node `fighter_event_transition_computable`, fulfillment: given computability of
a single payoff test, `fighterFulfillReady`, which folds it over the current phase's pending
list, is computable. Cancellation during the fold makes later request tests inert; no
enabled-action closure or game calculation is performed. -/
theorem computable_fighterFulfillReady (P : FighterParams)
    (hpay : Computable (fun a : ℕ × ℕ × Coordinate × FighterState =>
      fighterPayoff P a.1 a.2.1 a.2.2.1 a.2.2.2)) :
    Computable (fun a : ℕ × ℕ × FighterState => fighterFulfillReady P a.1 a.2.1 a.2.2) := by
  have hd : Computable (fun a : ℕ × ℕ × FighterState => a.1) := Computable.fst
  have hl : Computable (fun a : ℕ × ℕ × FighterState => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hs : Computable (fun a : ℕ × ℕ × FighterState => a.2.2) :=
    Computable.snd.comp Computable.snd
  have hh : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase =>
      a.2.pending.foldl (fun s q => fighterPayoff P a.1.1 a.1.2.1 q s) a.1.2.2) := by
    have hpend : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase => a.2.pending) :=
      FighterPhase.primrec_pending.to_comp.comp Computable.snd
    have hstate : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase => a.1.2.2) :=
      hs.comp Computable.fst
    have hstep : Computable₂ (fun (a : (ℕ × ℕ × FighterState) × FighterPhase)
        (u : FighterState × Coordinate) => fighterPayoff P a.1.1 a.1.2.1 u.2 u.1) :=
      (hpay.comp ((hd.comp (Computable.fst.comp Computable.fst)).pair
      ((hl.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp Computable.snd).pair (Computable.fst.comp Computable.snd))))).to₂
    exact @Computable.list_foldl ((ℕ × ℕ × FighterState) × FighterPhase) Coordinate
      FighterState _ _ _ (fun a => a.2.pending) (fun a => a.1.2.2)
      (fun a u => fighterPayoff P a.1.1 a.1.2.1 u.2 u.1) hpend hstate hstep
  exact (Computable.option_casesOn
    (o := fun a : ℕ × ℕ × FighterState => a.2.2.activeAt a.1 a.2.1)
    (f := fun a => a.2.2)
    (g := fun a phase => phase.pending.foldl (fun s q => fighterPayoff P a.1 a.2.1 q s) a.2.2)
    primrec_activeAt.to_comp hs hh.to₂).of_eq
      (fun a => by
        unfold fighterFulfillReady
        cases a.2.2.activeAt a.1 a.2.1 <;> rfl)

/-- A counter game with zero budget has no legal move, so its solver reports that the
active player does not win and returns no move. -/
private theorem FiniteCounterGame.solve_eq_of_budget_eq_zero
    (game : FiniteCounterGame) (hbudget : game.budget = 0) (position : CounterPosition game) :
    game.solve position = (!game.activePlayer position, none) := by
  have hl : position.leftBudget = 0 := by have := position.left_le; omega
  have hr : position.rightBudget = 0 := by have := position.right_le; omega
  have hn : ∀ move, ¬game.LegalMove position move := by
    intro move h
    have hp := h.2.1
    have hb := h.2.2.1
    simp only [CounterPosition.remaining, hl, hr, ite_self] at hb
    omega
  rw [FiniteCounterGame.solve.eq_1]
  have hh : ∀ move, (if _h : game.LegalMove position move then
      (game.solve (game.afterMove position move)).1 == game.activePlayer position
    else false) = false := fun move => dite_eq_right (hn move)
  simp only [hh]
  have hf : (counterMoveBox game.budget game.coordinates.length).find?
      (fun _ => false) = none := by
    apply List.find?_eq_none.mpr
    intro move h
    decide
  rw [hf]

/-- For an encoded counter game and a list of answers, the test whether the decoded game's
referee, run on the counter answer of the list, outputs the game's target is computable
in the pair (game code, list). It is the objective test used by the game transitions. -/
theorem computable_counterGameTargetReached :
    Computable (fun a : CounterGameCode × List ℕ =>
      decide ((decodeCounterGame a.1).referee.eval
        ((decodeCounterGame a.1).counterAnswer a.2) = (decodeCounterGame a.1).target)) := by
  have hc : Primrec (fun a : CounterGameCode × List ℕ => a.1) := Primrec.fst
  have h0 := Primrec.fst.comp hc
  have h1 := Primrec.fst.comp (Primrec.snd.comp hc)
  have h2 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have h3 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc)))
  have h5 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp hc)))))
  have h6 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc))))))
  have hz : Primrec (fun a : CounterGameCode × List ℕ =>
      ((a.1.1, a.1.2.1, a.1.2.2.1, a.1.2.2.2.1, (0 : ℕ), a.1.2.2.2.2.2.1,
        a.1.2.2.2.2.2.2.1, true), (a.2, (0 : ℕ), (0 : ℕ)))) :=
    (h0.pair (h1.pair (h2.pair (h3.pair ((Primrec.const 0).pair
      (h5.pair (h6.pair (Primrec.const true)))))))).pair
        (Primrec.snd.pair ((Primrec.const 0).pair (Primrec.const 0)))
  have hsolve := finite_counter_game_computable_winner.1.comp hz.to_comp
  refine (Computable.fst.comp hsolve).of_eq ?_
  intro a
  let game := decodeCounterGame
    (a.1.1, a.1.2.1, a.1.2.2.1, a.1.2.2.2.1, (0 : ℕ), a.1.2.2.2.2.2.1,
      a.1.2.2.2.2.2.2.1, true)
  let position := decodeCounterPosition game (a.2, 0, 0)
  change (game.solve position).1 = _
  rw [FiniteCounterGame.solve_eq_of_budget_eq_zero game rfl position]
  have hout : game.output position =
      (decodeCounterGame a.1).referee.eval ((decodeCounterGame a.1).counterAnswer a.2) := rfl
  have htarget : game.target = (decodeCounterGame a.1).target := rfl
  have hequality : game.equalityPlayer = true := rfl
  simp only [FiniteCounterGame.activePlayer, hout, htarget, hequality]
  split_ifs <;> simp_all

end Kolmogorov.Milovanov
