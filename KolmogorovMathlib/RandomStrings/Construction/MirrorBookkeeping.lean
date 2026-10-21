/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.MirrorPrimrec

/-!
# The remaining bookkeeping of the mirrored stage

The remaining bookkeeping functions of the mirrored stage and their primitive recursiveness,
which complete the effective simulation of the construction used for `Flim_re`.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-! #### Remaining bookkeeping -/

omit [Family] in
/-- The primitive recursiveness of the cost function `kCostC`. -/
theorem kCostC_primrec :
    Primrec fun p : StateC × StateC × List BitString => kCostC p.1 p.2.1 p.2.2 := by
  have h := Primrec.list_flatMap (dedup_primrec.comp (Primrec.snd.comp Primrec.snd) :
      Primrec fun p : StateC × StateC × List BitString => p.2.2.dedup)
    ((Primrec.list_cons.comp (Primrec.pair (Primrec.const true)
        (hvalTab_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
      (Primrec.list_cons.comp (Primrec.pair (Primrec.const false)
        (hvalTab_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
        (Primrec.const []))).to₂ :
      Primrec₂ fun (p : StateC × StateC × List BitString) (z : BitString) =>
        [(true, hvalTab p.2.1 z), (false, hvalTab p.1 z)])
  refine h.of_eq fun p => ?_
  unfold kCostC
  congr 1
  funext z
  rw [hval_eq_hvalTab, hval_eq_hvalTab]

/-- The score of the player to move, as a formal sum. -/
def moverC (st : GStC) : FSum := if st.2.2.2 = true then st.2.1 else st.2.2.1

omit [Family] in
/-- The primitive recursiveness of `moverC`. -/
theorem moverC_primrec : Primrec moverC := by
  have h := Primrec.cond (Primrec.snd.comp (Primrec.snd.comp Primrec.snd) :
      Primrec fun st : GStC => st.2.2.2)
    (Primrec.fst.comp Primrec.snd : Primrec fun st : GStC => st.2.1)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd) : Primrec fun st : GStC => st.2.2.1)
  refine h.of_eq fun st => ?_
  unfold moverC
  cases st.2.2.2 <;> rfl

omit [Family] in
/-- The condition that a player cheats is equivalent to a comparison of formal sums. -/
theorem cheats_iff_fsLt (m : ℕ) (st : GStC) (c : FSum) :
    Cheats ((2 : ℝ)⁻¹ ^ m) st.toG (FSum.val c) ↔ fsLt [(true, m)] (moverC st ++ c) = true := by
  rw [fsLt_spec, decide_eq_true_iff, FSum.val_append]
  have h1 : FSum.val [(true, m)] = (2 : ℝ)⁻¹ ^ m := by simp [FSum.val]
  have h2 : FSum.val (moverC st) = st.toG.moverScore := by
    unfold moverC GStC.toG GState.moverScore
    cases st.2.2.2 <;> rfl
  rw [h1, h2]
  rfl

/-- The newly non-random strings of a play list, from the tables. -/
def flipListC (σC : StateC) (X : List BitString) : List BitString :=
  X.filter fun z => decide (hvalTab σC z < z.length)

omit [Family] in
/-- The finite set of strings returned by `flipListC` matches the abstract `flipped` set. -/
theorem flipListC_toFinset (σC : StateC) (X : List BitString) :
    (flipListC σC X).toFinset = flipped σC.toState X.toFinset := by
  ext z
  simp [flipListC, flipped, hval_eq_hvalTab]

omit [Family] in
/-- The primitive recursiveness of `flipListC`. -/
theorem flipListC_primrec : Primrec fun p : StateC × List BitString => flipListC p.1 p.2 := by
  have h := primrec_filter_param (Primrec.snd : Primrec fun p : StateC × List BitString => p.2)
    ((Primrec.nat_lt.decide.comp (hvalTab_primrec.comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd) (Primrec.list_length.comp Primrec.snd)).to₂ :
      Primrec₂ fun (p : StateC × List BitString) (z : BitString) =>
        decide (hvalTab p.1 z < z.length))
  exact h.of_eq fun p => rfl

/-- `F ⊆ S` for lists, as a Boolean. -/
def allMemC (F S : List BitString) : Bool := F.foldr (fun z b => memStr z S && b) true

section

omit [Family]

/-- The Boolean list inclusion `allMemC` is true if and only if all elements of the first list are
in the second list. -/
theorem allMemC_iff (F S : List BitString) : allMemC F S = true ↔ ∀ z ∈ F, z ∈ S := by
  induction F with
  | nil => simp [allMemC]
  | cons a F ih =>
    change (memStr a S && allMemC F S) = true ↔ _
    rw [Bool.and_eq_true, ih, memStr_iff]
    simp

/-- The primitive recursiveness of `allMemC`. -/
theorem allMemC_primrec : Primrec₂ allMemC := by
  have h := Primrec.list_foldr (σ := Bool)
    (Primrec.fst : Primrec fun p : List BitString × List BitString => p.1)
    (Primrec.const true)
    ((Primrec.and.comp (memStr_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq fun p => rfl

/-- The abstract condition that no new strings are flipped is equivalent to `allMemC` being true. -/
theorem noNewFlip_iff (σC : StateC) (S X : List BitString) :
    S.toFinset ∪ flipped σC.toState X.toFinset = S.toFinset ↔
      allMemC (flipListC σC X) S = true := by
  rw [← flipListC_toFinset, Finset.union_eq_left, allMemC_iff]
  constructor
  · intro h z hz
    exact List.mem_toFinset.1 (h (List.mem_toFinset.2 hz))
  · intro h z hz
    exact List.mem_toFinset.2 (h z (List.mem_toFinset.1 hz))

/-- The primitive recursiveness of charging a finite game state. -/
theorem GStC.charge_primrec : Primrec₂ GStC.charge := by
  have hst : Primrec fun p : GStC × FSum => p.1 := Primrec.fst
  have hc : Primrec fun p : GStC × FSum => p.2 := Primrec.snd
  have h1 : Primrec fun p : GStC × FSum => p.1.1 := Primrec.fst.comp hst
  have h21 : Primrec fun p : GStC × FSum => p.1.2.1 := Primrec.fst.comp (Primrec.snd.comp hst)
  have h221 : Primrec fun p : GStC × FSum => p.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have h222 : Primrec fun p : GStC × FSum => p.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have hy0 := h1.pair ((Primrec.list_append.comp h21 hc).pair (h221.pair h222))
  have hy : Primrec fun p : GStC × FSum =>
      ((p.1.1, p.1.2.1 ++ p.2, p.1.2.2.1, p.1.2.2.2) : GStC) := hy0
  have hn0 := h1.pair (h21.pair ((Primrec.list_append.comp h221 hc).pair h222))
  have hn : Primrec fun p : GStC × FSum =>
      ((p.1.1, p.1.2.1, p.1.2.2.1 ++ p.2, p.1.2.2.2) : GStC) := hn0
  have h := Primrec.cond h222 hy hn
  refine h.of_eq fun p => ?_
  change (bif p.1.2.2.2 then _ else _) = GStC.charge p.1 p.2
  unfold GStC.charge
  cases p.1.2.2.2 <;> rfl

/-- The primitive recursiveness of processing a move of `K` on a finite game state. -/
theorem GStC.kMove_primrec :
    Primrec fun p : GStC × List BitString × FSum => GStC.kMove p.1 p.2.1 p.2.2 := by
  have hp1 : Primrec fun p : GStC × List BitString × FSum => p.1 := Primrec.fst
  have hp21 : Primrec fun p : GStC × List BitString × FSum => p.2.1 := Primrec.fst.comp Primrec.snd
  have hp22 : Primrec fun p : GStC × List BitString × FSum => p.2.2 := Primrec.snd.comp Primrec.snd
  have hch0 := GStC.charge_primrec.comp hp1 hp22
  have hch : Primrec fun p : GStC × List BitString × FSum => GStC.charge p.1 p.2.2 := hch0
  have h0 := hp21.pair ((Primrec.fst.comp (Primrec.snd.comp hch)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hch))).pair
      (Primrec.not.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp1))))))
  have h : Primrec fun p : GStC × List BitString × FSum => ((p.2.1, (GStC.charge p.1 p.2.2).2.1,
      (GStC.charge p.1 p.2.2).2.2.1, !p.1.2.2.2) : GStC) := h0
  exact h.of_eq fun p => rfl

end

/-- The finite data of `curGame A (reqγ γ) σC.toState e g.toRec`, from a query-list function. -/
def curGameDataC (q : ℕ → BitString → List BitString) (e : ℕ) (g : GameC)
    (σC : StateC) : GameDataC :=
  (e - 1, g.1, g.2.1, (q (e - 1) g.1 ++ g.2.1).map (fun z => (z, hvalTab σC z)), g.2.2.1)

/-- The finite game data matches the abstract live game definition. -/
theorem curGameDataC_spec (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (q : ℕ → BitString → List BitString)
    (hq : ∀ e x, (q e x).toFinset = qsetF (γ e).1 (γ e).2 x)
    (e : ℕ) (g : GameC) (σC : StateC) :
    (curGameDataC q e g σC).Describes γ σC.toState.hval ∧
      gameOfF A (γ (curGameDataC q e g σC).1).1 (γ (curGameDataC q e g σC).1).2
        (curGameDataC q e g σC).2.1 σC.toState.hval
        ((2 : ℝ)⁻¹ ^ (curGameDataC q e g σC).2.2.2.2) (curGameDataC q e g σC).2.2.1.toFinset =
        curGame A (reqγ γ) σC.toState e g.toRec := by
  refine ⟨⟨q (e - 1) g.1 ++ g.2.1, ?_, ?_, ?_⟩, rfl⟩
  · change List.map _ _ = List.map _ _
    congr 1
    funext z
    rw [hval_eq_hvalTab]
  · intro z hz
    have hz' : z ∈ (q (e - 1) g.1).toFinset := by rw [hq]; exact hz
    exact List.mem_append_left _ (List.mem_toFinset.1 hz')
  · intro z hz
    exact List.mem_append_right _ hz

omit [Family] in
/-- The computability of `curGameDataC`. -/
theorem curGameDataC_computable (q : ℕ → BitString → List BitString) (hqc : Computable₂ q) :
    Computable fun a : ℕ × GameC × StateC => curGameDataC q a.1 a.2.1 a.2.2 := by
  have hsub : Computable fun a : ℕ × GameC × StateC => a.1 - 1 :=
    (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)).to_comp
  have hx : Computable fun a : ℕ × GameC × StateC => a.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hX : Computable fun a : ℕ × GameC × StateC => a.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hm : Computable fun a : ℕ × GameC × StateC => a.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.snd)))
  have hQ0 := hqc.comp hsub hx
  have hQ : Computable fun a : ℕ × GameC × StateC => q (a.1 - 1) a.2.1.1 := hQ0
  have hT : Primrec fun b : List BitString × StateC => b.1.map fun z => (z, hvalTab b.2 z) :=
    Primrec.list_map Primrec.fst ((Primrec.snd.pair
      (hvalTab_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)
  have hT0 := hT.to_comp.comp ((Computable.list_append.comp hQ hX).pair
    (Computable.snd.comp Computable.snd))
  exact hsub.pair (hx.pair (hX.pair (hT0.pair hm)))

/-- The processing of a live game on finite states is computable. -/
theorem processGameC_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    Computable fun q : StateC × ℕ × GameC × StateC =>
      processGameC A (reqγ γ) q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  classical
  obtain ⟨q, hqc, hq⟩ := queryList_computable γ hγ
  obtain ⟨r, hrc, hr⟩ := replyC_computable A hA γ hγ
  have hσ₀ : Computable fun a : StateC × ℕ × GameC × StateC => a.1 := Computable.fst
  have he : Computable fun a : StateC × ℕ × GameC × StateC => a.2.1 :=
    Computable.fst.comp Computable.snd
  have hg : Computable fun a : StateC × ℕ × GameC × StateC => a.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hσ : Computable fun a : StateC × ℕ × GameC × StateC => a.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hX : Computable fun a : StateC × ℕ × GameC × StateC => a.2.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hg)
  have hm : Computable fun a : StateC × ℕ × GameC × StateC => a.2.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hg))
  have hst : Computable fun a : StateC × ℕ × GameC × StateC => a.2.2.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hg))
  have hS : Computable fun a : StateC × ℕ × GameC × StateC => a.2.2.1.2.2.2.1 :=
    Computable.fst.comp hst
  -- the charge of `K`
  have hc0 := kCostC_primrec.to_comp.comp (hσ₀.pair (hσ.pair hX))
  have hc : Computable fun a : StateC × ℕ × GameC × StateC =>
      kCostC a.1 a.2.2.2 a.2.2.1.2.1 := hc0
  -- the cheating test
  have hch0 := fsLt_primrec.to_comp.comp
    (Computable.list_cons.comp (Computable.pair (Computable.const true) hm)
      (Computable.const ([] : FSum)))
    (Computable.list_append.comp (moverC_primrec.to_comp.comp hst) hc)
  have hch : Computable fun a : StateC × ℕ × GameC × StateC =>
      fsLt [(true, a.2.2.1.2.2.1)] (moverC a.2.2.1.2.2.2 ++ kCostC a.1 a.2.2.2 a.2.2.1.2.1) :=
    hch0
  -- the test for a new flip
  have hF0 := flipListC_primrec.to_comp.comp (hσ.pair hX)
  have hF : Computable fun a : StateC × ℕ × GameC × StateC =>
      flipListC a.2.2.2 a.2.2.1.2.1 := hF0
  have hnf0 := allMemC_primrec.to_comp.comp hF hS
  have hnf : Computable fun a : StateC × ℕ × GameC × StateC =>
      allMemC (flipListC a.2.2.2 a.2.2.1.2.1) a.2.2.1.2.2.2.1 := hnf0
  -- branch 1: cheat
  have hb10 := injureC_primrec.to_comp.comp he (destroyC_primrec.to_comp.comp he hσ)
  have hb1 : Computable fun a : StateC × ℕ × GameC × StateC =>
      (injureC a.2.1 (destroyC a.2.1 a.2.2.2), true) := hb10.pair (Computable.const true)
  -- branch 2: charge
  have hrec20 := (Computable.fst.comp hg).pair (hX.pair (hm.pair
    (GStC.charge_primrec.to_comp.comp hst hc)))
  have hrec2 : Computable fun a : StateC × ℕ × GameC × StateC =>
      ((a.2.2.1.1, a.2.2.1.2.1, a.2.2.1.2.2.1, a.2.2.1.2.2.2.charge (kCostC a.1 a.2.2.2
        a.2.2.1.2.1)) : GameC) := hrec20
  have hb20 := setGameC_primrec.to_comp.comp (he.pair (hrec2.pair hσ))
  have hb2 : Computable fun a : StateC × ℕ × GameC × StateC =>
      (setGameC a.2.1 (a.2.2.1.1, a.2.2.1.2.1, a.2.2.1.2.2.1,
        a.2.2.1.2.2.2.charge (kCostC a.1 a.2.2.2 a.2.2.1.2.1)) a.2.2.2, false) :=
    hb20.pair (Computable.const false)
  -- branch 3: move of `K` and our answer
  have hU0 := sortStr_toFinset_primrec.to_comp.comp (Computable.list_append.comp hS hF)
  have hU : Computable fun a : StateC × ℕ × GameC × StateC =>
      sortStr (a.2.2.1.2.2.2.1 ++ flipListC a.2.2.2 a.2.2.1.2.1).toFinset := hU0
  have hK0 := GStC.kMove_primrec.to_comp.comp (hst.pair (hU.pair hc))
  have hK : Computable fun a : StateC × ℕ × GameC × StateC =>
      a.2.2.1.2.2.2.kMove (sortStr (a.2.2.1.2.2.2.1 ++ flipListC a.2.2.2 a.2.2.1.2.1).toFinset)
        (kCostC a.1 a.2.2.2 a.2.2.1.2.1) := hK0
  have hD0 := (curGameDataC_computable q hqc).comp (he.pair (hg.pair hσ))
  have hD : Computable fun a : StateC × ℕ × GameC × StateC =>
      curGameDataC q a.2.1 a.2.2.1 a.2.2.2 := hD0
  have hwe : Computable fun a : StateC × ℕ × GameC × StateC => !a.2.2.1.2.2.2.2.2.2 :=
    Primrec.not.to_comp.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hst)))
  have hR0 := hrc.comp (hD.pair (hwe.pair hK))
  have hR : Computable fun a : StateC × ℕ × GameC × StateC =>
      r (curGameDataC q a.2.1 a.2.2.1 a.2.2.2, !a.2.2.1.2.2.2.2.2.2,
        a.2.2.1.2.2.2.kMove (sortStr (a.2.2.1.2.2.2.1 ++ flipListC a.2.2.2 a.2.2.1.2.1).toFinset)
          (kCostC a.1 a.2.2.2 a.2.2.1.2.1)) := hR0
  have hFL0 := (primrec_filter_param
      (Primrec.fst : Primrec fun p : List BitString × List BitString => p.1)
      ((Primrec.not.comp (memStr_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂ :
        Primrec₂ fun (p : List BitString × List BitString) (z : BitString) =>
          !memStr z p.2)).to_comp.comp
      (hR.pair (Computable.list_append.comp hS hF))
  have hFL := sortStr_toFinset_primrec.to_comp.comp hFL0
  have hAM := GStC.applyMove_primrec.to_comp.comp (hσ.pair (hK.pair hR))
  have hrec3 := (Computable.fst.comp hg).pair (hX.pair (hm.pair hAM))
  have hset3 := setGameC_primrec.to_comp.comp (he.pair (hrec3.pair hσ))
  have hflip3 := applyFlipsC_primrec.to_comp.comp hFL hset3
  have hb30 := injureC_primrec.to_comp.comp he hflip3
  have hb3 := hb30.pair (Computable.const true)
  have hall := Computable.cond hch hb1 (Computable.cond hnf hb2 hb3)
  refine hall.of_eq fun a => ?_
  obtain ⟨σ₀C, e, g, σC⟩ := a
  -- the abbreviations of the computed form
  have hcheat : Cheats ((2 : ℝ)⁻¹ ^ g.toRec.2.2.1) g.toRec.2.2.2
      (kCost σ₀C.toState σC.toState g.toRec.2.1) ↔
      fsLt [(true, g.2.2.1)] (moverC g.2.2.2 ++ kCostC σ₀C σC g.2.1) = true := by
    rw [← cheats_iff_fsLt, kCostC_val]; rfl
  have hnew : g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1 = g.toRec.2.2.2.S ↔
      allMemC (flipListC σC g.2.1) g.2.2.2.1 = true := noNewFlip_iff σC g.2.2.2.1 g.2.1
  have hU : sortStr (g.2.2.2.1 ++ flipListC σC g.2.1).toFinset =
      sortStr (g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1) := by
    rw [List.toFinset_append, flipListC_toFinset]; rfl
  have hspec := curGameDataC_spec A γ q hq e g σC
  have hRr : ∀ st : GStC, r (curGameDataC q e g σC, !g.2.2.2.2.2.2, st) =
      sortStr (ourReply (curGame A (reqγ γ) σC.toState e g.toRec) (!g.toRec.2.2.2.yesTurn)
        st.toG) := fun st => by
    rw [hr _ _ _ _ hspec.1, hspec.2]; rfl
  have hfl : ∀ R : List BitString, ∀ T : Finset BitString, R.toFinset = T →
      sortStr ((R.filter fun z => !memStr z (g.2.2.2.1 ++ flipListC σC g.2.1)).toFinset) =
      sortStr (T \ (g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1)) := by
    intro R T hRT
    congr 1
    ext z
    rw [List.mem_toFinset, List.mem_filter, Finset.mem_sdiff, ← hRT, List.mem_toFinset]
    have hz : z ∈ g.2.2.2.1 ++ flipListC σC g.2.1 ↔
        z ∈ g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1 := by
      rw [← List.mem_toFinset, List.toFinset_append, flipListC_toFinset]; rfl
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h3 => ?_⟩
      rw [(memStr_iff z _).2 (hz.2 h3)] at h2
      simp at h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      cases hb : memStr z (g.2.2.2.1 ++ flipListC σC g.2.1)
      · rfl
      · exact absurd (hz.1 ((memStr_iff z _).1 hb)) h2
  change (bif fsLt [(true, g.2.2.1)] (moverC g.2.2.2 ++ kCostC σ₀C σC g.2.1) then _ else _) =
    processGameC A (reqγ γ) σ₀C e g σC
  unfold processGameC
  by_cases h1 : Cheats ((2 : ℝ)⁻¹ ^ g.toRec.2.2.1) g.toRec.2.2.2
      (kCost σ₀C.toState σC.toState g.toRec.2.1)
  · rw [ite_eq_left h1, hcheat.1 h1, Bool.cond_true]
  · have h1' : fsLt [(true, g.2.2.1)] (moverC g.2.2.2 ++ kCostC σ₀C σC g.2.1) = false := by
      cases hb : fsLt [(true, g.2.2.1)] (moverC g.2.2.2 ++ kCostC σ₀C σC g.2.1)
      · rfl
      · exact absurd (hcheat.2 hb) h1
    rw [ite_eq_right h1, h1', Bool.cond_false]
    by_cases h2 : g.toRec.2.2.2.S ∪ flipped σC.toState g.toRec.2.1 = g.toRec.2.2.2.S
    · rw [ite_eq_left h2, hnew.1 h2, Bool.cond_true]
    · have h2' : allMemC (flipListC σC g.2.1) g.2.2.2.1 = false := by
        cases hb : allMemC (flipListC σC g.2.1) g.2.2.2.1
        · rfl
        · exact absurd (hnew.2 hb) h2
      rw [ite_eq_right h2, h2', Bool.cond_false]
      change (injureC e (applyFlipsC
        (sortStr ((r (curGameDataC q e g σC, !g.2.2.2.2.2.2,
          g.2.2.2.kMove (sortStr (g.2.2.2.1 ++ flipListC σC g.2.1).toFinset)
            (kCostC σ₀C σC g.2.1))).filter
              fun z => !memStr z (g.2.2.2.1 ++ flipListC σC g.2.1)).toFinset)
        (setGameC e (g.1, g.2.1, g.2.2.1, GStC.applyMove σC
          (g.2.2.2.kMove (sortStr (g.2.2.2.1 ++ flipListC σC g.2.1).toFinset)
            (kCostC σ₀C σC g.2.1))
          (r (curGameDataC q e g σC, !g.2.2.2.2.2.2,
            g.2.2.2.kMove (sortStr (g.2.2.2.1 ++ flipListC σC g.2.1).toFinset)
              (kCostC σ₀C σC g.2.1)))) σC)), true) = _
      rw [hU, hRr, hfl _ _ (sortStr_toFinset _)]

/-- The computability of starting a game. -/
theorem startGameC_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hW : ∀ γ', WitnessesExist A γ') (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    Computable₂ fun (e : ℕ) (σC : StateC) => startGameC A (reqγ γ) e σC := by
  have hw0 := (chooseWitnessC_computable A hA hW γ hγ).comp
    (Computable.snd : Computable fun q : ℕ × StateC => q.2)
    (Computable.fst : Computable fun q : ℕ × StateC => q.1)
  have hw : Computable fun q : ℕ × StateC => chooseWitness A (reqγ γ) q.2.toState q.1 := hw0
  have hn : Computable fun q : ℕ × StateC => (q.2, false) :=
    Computable.snd.pair (Computable.const false)
  have hs0 := (startOnC_computable A hA γ hγ).comp (((Computable.snd.comp Computable.fst).pair
      ((Computable.fst.comp Computable.fst).pair Computable.snd)) :
        Computable fun q : (ℕ × StateC) × BitString => (q.1.2, q.1.1, q.2))
  have hs : Computable₂ fun (q : ℕ × StateC) (x : BitString) => startOnC A (reqγ γ) q.1 q.2 x := hs0
  have h0 := Computable.option_casesOn hw hn hs
  refine h0.of_eq fun q => ?_
  change _ = startGameC A (reqγ γ) q.1 q.2
  unfold startGameC
  cases chooseWitness A (reqγ γ) q.2.toState q.1 <;> rfl

/-- Processing a requirement is computable. -/
theorem processReqC_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hW : ∀ γ', WitnessesExist A γ') (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    Computable fun q : StateC × ℕ × (StateC × Bool) =>
      processReqC A (reqγ γ) q.1 q.2.1 q.2.2 := by
  have hl0 := gLook_primrec.to_comp.comp
    (StateC.games_primrec.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp Computable.snd) :
        Computable fun q : StateC × ℕ × (StateC × Bool) => q.2.2.1))
    (Computable.fst.comp Computable.snd :
        Computable fun q : StateC × ℕ × (StateC × Bool) => q.2.1)
  have hlook : Computable fun q : StateC × ℕ × (StateC × Bool) =>
      gLook q.2.2.1.games q.2.1 := hl0
  have hs0 := (startGameC_computable A hA hW γ hγ).comp
    (Computable.fst.comp Computable.snd :
        Computable fun q : StateC × ℕ × (StateC × Bool) => q.2.1)
    (Computable.fst.comp (Computable.snd.comp Computable.snd) :
        Computable fun q : StateC × ℕ × (StateC × Bool) => q.2.2.1)
  have hs : Computable fun q : StateC × ℕ × (StateC × Bool) =>
      startGameC A (reqγ γ) q.2.1 q.2.2.1 := hs0
  have hp0 := (processGameC_computable A hA γ hγ).comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.snd.pair
          (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))) :
      Computable fun p : (StateC × ℕ × (StateC × Bool)) × GameC =>
        (p.1.1, p.1.2.1, p.2, p.1.2.2.1))
  have hp : Computable₂ fun (q : StateC × ℕ × (StateC × Bool)) (g : GameC) =>
      processGameC A (reqγ γ) q.1 q.2.1 g q.2.2.1 := hp0
  have hm := Computable.option_casesOn hlook hs hp
  have hc : Computable fun q : StateC × ℕ × (StateC × Bool) => q.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hid : Computable fun q : StateC × ℕ × (StateC × Bool) => q.2.2 :=
    Computable.snd.comp Computable.snd
  refine (Computable.cond hc hid hm).of_eq fun q => ?_
  unfold processReqC
  cases hq : q.2.2.2
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    cases gLook q.2.2.1.games q.2.1 <;> rfl
  · simp only [Bool.cond_true, ite_true]

omit [Family] in
/-- The fold of a stage as a recursion on the number of processed requirements. -/
theorem foldl_range_succ {σ : Type} (F : σ → ℕ → σ) (a : σ) (n : ℕ) :
    (List.range (n + 1)).foldl F a = F ((List.range n).foldl F a) n := by
  rw [List.range_succ, List.foldl_append]; rfl

omit [Family] in
/-- The fold over a list of range elements equals a recursion step by step. -/
theorem foldl_range_eq_rec {σ : Type} (F : σ → ℕ → σ) (a : σ) (n : ℕ) :
    (List.range n).foldl F a = Nat.rec (motive := fun _ => σ) a (fun y IH => F IH y) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [foldl_range_succ, ih]

/-- One mirrored stage is computable: the fold over `List.range s` is a `Nat.rec` of the
computable `processReqC` (`processReqC_computable`), started from `updateKC`. -/
theorem stageStepC_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hW : ∀ γ', WitnessesExist A γ') (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ)
    (enumK : ℕ → BitString × ℕ)
    (hK : Computable enumK) :
    Computable₂ fun (s : ℕ) (σC : StateC) => stageStepC A γ enumK s σC := by
  have hP := processReqC_computable A hA hW γ hγ
  have hU := updateKC_computable enumK hK
  have hg0 := hU.comp
    ((Primrec.nat_sub.to_comp.comp Computable.fst (Computable.const 1)) :
      Computable fun a : ℕ × StateC => a.1 - 1)
    (Computable.snd : Computable fun a : ℕ × StateC => a.2)
  have hg1 : Computable fun a : ℕ × StateC => updateKC enumK (a.1 - 1) a.2 := hg0
  have hg : Computable fun a : ℕ × StateC => (updateKC enumK (a.1 - 1) a.2, false) :=
    hg1.pair (Computable.const false)
  have hh0 := hP.comp ((Computable.snd.comp Computable.fst).pair
      ((Computable.succ.comp (Computable.fst.comp Computable.snd)).pair
        (Computable.snd.comp Computable.snd)) :
      Computable fun q : (ℕ × StateC) × (ℕ × (StateC × Bool)) => (q.1.2, q.2.1 + 1, q.2.2))
  have hh : Computable₂ fun (a : ℕ × StateC) (p : ℕ × (StateC × Bool)) =>
      processReqC A (reqγ γ) a.2 (p.1 + 1) p.2 := hh0
  have hrec := Computable.nat_rec (Computable.fst : Computable fun a : ℕ × StateC => a.1) hg hh
  refine (Computable.fst.comp hrec).of_eq fun a => ?_
  change _ = stageStepC A γ enumK a.1 a.2
  unfold stageStepC
  rw [foldl_range_eq_rec]

/-- The mirrored stages are computable. -/
theorem stageC_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hW : ∀ γ', WitnessesExist A γ') (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ)
    (enumK : ℕ → BitString × ℕ)
    (hK : Computable enumK) : Computable (stageC A γ enumK) := by
  have hstep := stageStepC_computable A hA hW γ hγ enumK hK
  have hh : Computable₂ fun (_ : ℕ) (p : ℕ × StateC) => stageStepC A γ enumK (p.1 + 1) p.2 :=
    hstep.comp (Computable.succ.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  have h : Computable fun s : ℕ => Nat.rec (motive := fun _ => StateC) StateC.init
      (fun y IH => stageStepC A γ enumK (y + 1) IH) s :=
    Computable.nat_rec Computable.id (Computable.const _) hh
  refine h.of_eq fun s => ?_
  induction s with
  | zero => rfl
  | succ s ih =>
    change stageStepC A γ enumK (s + 1) (Nat.rec (motive := fun _ => StateC) StateC.init
      (fun y IH => stageStepC A γ enumK (y + 1) IH) s) = stageC A γ enumK (s + 1)
    rw [ih]; rfl

/-- `F*` is computable as a function of the stage and the string. -/
theorem stage_Fstar_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hW : ∀ γ', WitnessesExist A γ') (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ)
    (enumK : ℕ → BitString × ℕ)
    (hK : Computable enumK) :
    Computable fun q : ℕ × BitString => (stage A γ enumK q.1).Fstar q.2 := by
  have h := stageC_computable A hA hW γ hγ enumK hK
  have h2 : Computable fun q : ℕ × BitString => fLook (stageC A γ enumK q.1).fTab q.2 :=
    fLook_primrec.to_comp.comp (StateC.fTab_primrec.to_comp.comp (h.comp Computable.fst))
      Computable.snd
  exact h2.of_eq fun q => (stage_Fstar_eq_fLook A γ enumK q.1 q.2).symm

omit [Family] in
/-- A computable sequence of functions has a c.e. "eventual overgraph". -/
theorem REPred_exists_le_of_computable (G : ℕ × BitString → ℕ) (hG : Computable G) :
    REPred fun p : BitString × ℕ => ∃ n, G (n, p.1) ≤ p.2 := by
  have hdec : Computable fun q : ℕ × (BitString × ℕ) => decide (G (q.1, q.2.1) ≤ q.2.2) :=
    (Primrec.nat_le.decide.to_comp).comp
      (hG.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)
  have hp : REPred fun q : ℕ × (BitString × ℕ) => G (q.1, q.2.1) ≤ q.2.2 :=
    (ComputablePred.to_re (Computable.computablePred hdec)).of_eq fun q => Iff.rfl
  exact REPred_exists_nat (p := fun n (p : BitString × ℕ) => G (n, p.1) ≤ p.2) hp

/-- Property 1: the overgraph of `F` is computably enumerable, for an effective enumeration `γ`
of the clocked machines and a computable enumeration of `ov K`.  Each stage is a finite
computation (the game values are decidable finite game trees, real numbers occurring are dyadic
rationals, `A` is decidable, and the witness search terminates by `WitnessesExist`), so
`s ↦ stage s` restricted to the finitely many relevant strings is computable, and
`(x, y) ∈ ov F` iff some stage has `F*(x) ≤ y`. -/
theorem Flim_re (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hW : ∀ γ', WitnessesExist A γ')
    (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) (enumK : ℕ → BitString × ℕ) (hK : Computable enumK) :
    REPred fun p : BitString × ℕ => p ∈ ov (Flim A γ enumK) := by
  refine (REPred_exists_le_of_computable _
    (stage_Fstar_computable A hA hW γ hγ enumK hK)).of_eq fun p => ?_
  change (∃ n, (stage A γ enumK n).Fstar p.1 ≤ p.2) ↔ Flim A γ enumK p.1 ≤ p.2
  constructor
  · rintro ⟨n, hn⟩
    exact (ciInf_le (OrderBot.bddBelow _) n).trans hn
  · intro h
    obtain ⟨n, hn⟩ := Nat.sInf_mem (Set.range_nonempty fun s => (stage A γ enumK s).Fstar p.1)
    exact ⟨n, (le_of_eq hn).trans h⟩

end Kolmogorov.RandomStrings
