/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LibraryAPI
import KolmogorovMathlib.Complexity.Applications.TapeMachine

/-!
# Crossing Sequence Bound

The main declaration is `rightComplexity`, the plain complexity of the content of the tape cells
to the right of a border `b`.  The auxiliary lemmas bound this complexity by the length of the
crossing sequence through the border plus a constant: the content on the right of the border is
recovered from the crossing sequence alone by a finite simulation of the machine restricted to
the right of the border.  This is the crossing-sequence argument used in the lower bounds on the
running time of one-tape Turing machines.
-/

namespace Kolmogorov.Applications

open TuringMachine

variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [Encodable Γ]

/-- The complexity of the content of the cells after `b`, in the plain complexity of `V`. -/
noncomputable def rightComplexity (V : Map) (M : TuringMachine Q Γ) (tape : ℤ → Γ) (b : ℤ) : ℝ :=
  ((plainK V (wordBits Γ (M.rightContents tape b))).toNat : ℝ)

omit [Fintype Q] [Fintype Γ] [Encodable Γ] in
/-- Step 0 of the proof of `rightComplexity_le_crossingSequence`: the content `R` of the
cells after `b` depends only on the cells after `b`. -/
private lemma rightComplexity_le_crossingSequence_rightContents_congr
    (M : TuringMachine Q Γ) {τ τ' : ℤ → Γ} {b : ℤ} (h : ∀ i, b < i → τ i = τ' i) :
    M.rightContents τ b = M.rightContents τ' b := by
  classical
  have h' : ∀ k : ℕ, τ (b + 1 + k) = τ' (b + 1 + k) := fun k => h _ (by omega)
  have key : ∀ K : ℕ, (∀ k : ℕ, K ≤ k → τ (b + 1 + k) = M.blank) ↔
      (∀ k : ℕ, K ≤ k → τ' (b + 1 + k) = M.blank) := fun K => by simp only [h']
  have hcl : M.contentLength τ b = M.contentLength τ' b := by
    unfold TuringMachine.contentLength
    by_cases hex : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → τ (b + 1 + k) = M.blank
    · have hex' : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → τ' (b + 1 + k) = M.blank :=
        hex.imp fun K hK => (key K).1 hK
      rw [dite_eq_left hex, dite_eq_left hex']
      exact le_antisymm (Nat.find_min' hex ((key _).2 (Nat.find_spec hex')))
        (Nat.find_min' hex' ((key _).1 (Nat.find_spec hex)))
    · have hex' : ¬ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → τ' (b + 1 + k) = M.blank :=
        fun ⟨K, hK⟩ => hex ⟨K, (key K).2 hK⟩
      rw [dite_eq_right hex, dite_eq_right hex']
  unfold TuringMachine.rightContents
  rw [hcl]
  refine List.map_congr_left fun k hk => ?_
  have hk0 : 0 ≤ k := by
    have hk' : ∃ a : ℕ, a < M.contentLength τ' b ∧ k = (a : ℤ) := by simpa using hk
    obtain ⟨a, _, rfl⟩ := hk'
    exact Int.natCast_nonneg a
  exact h _ (by omega)

/-- The word of ranks with its trailing `b0`s removed. -/
private def rightComplexity_le_crossingSequence_trim (b0 : ℕ) (l : List ℕ) : List ℕ :=
  (l.reverse.dropWhile (fun x => x == b0)).reverse

/-- One step of the finite simulation of the replay on the right of a border, on ranks. The state is
`(tape, flag, state, head, pending)`: `tape` is the list of the ranks of the cells `p + 1, p + 2, …`
(a window of fixed length), `flag = 1` iff the head is on the right of the border, in which case
`state` is the rank of the state and `head` the offset of the head cell from `p + 1`, and `pending`
is the list of the ranks of the unused crossing states.  `T q a = (1, q', a', mv)` if the machine
in the state of rank `q` reading the symbol of rank `a` goes to the state `q'`, writes `a'` and
moves by `mv - 1`, and `T q a = (0, _, _, _)` if it halts. -/
private def rightComplexity_le_crossingSequence_simStep (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) (b0 : ℕ)
    (st : List ℕ × ℕ × ℕ × ℕ × List ℕ) : List ℕ × ℕ × ℕ × ℕ × List ℕ :=
  if st.2.1 = 0 then
    if st.2.2.2.2 = [] then st
    else (st.1, 1, st.2.2.2.2.headD 0, 0, st.2.2.2.2.tail)
  else if (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).1 = 0 then st
  else
    (st.1.take st.2.2.2.1 ++ (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.1 ::
        st.1.drop (st.2.2.2.1 + 1),
      if st.2.2.2.1 + (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.2 = 0 then 0 else 1,
      (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.1,
      st.2.2.2.1 + (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.2 - 1,
      st.2.2.2.2)

/-- The finite simulation: `s` steps of `simStep` from the blank window of length `s`, with the
crossing states `A` pending; the result is the content of the cells after the cell at offset
`min d s`, without its trailing blanks (the rank of the blank is `b0`). -/
private def rightComplexity_le_crossingSequence_simulate (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) (b0 : ℕ)
    (A : List ℕ) (s d : ℕ) : List ℕ :=
  rightComplexity_le_crossingSequence_trim b0
    ((((rightComplexity_le_crossingSequence_simStep T b0)^[s]
      (List.replicate s b0, 0, 0, 0, A)).1).drop (min d s))

/-- Step 1 of the proof of `rightComplexity_le_crossingSequence`: the word of the ranks
of the letters is encoded into the bit string `wordBits` by a primitive recursive function. -/
private lemma rightComplexity_le_crossingSequence_enc :
    ∃ enc : List ℕ → BitString, Primrec enc ∧
      ∀ l : List Γ, enc (l.map (alphabetIndex Γ)) = wordBits Γ l := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow
  have hnbf : ∀ k : ℕ, natBitsFixed (alphabetWidth Γ) k =
      (List.range (alphabetWidth Γ)).map (fun i => Nat.testBit k i) := by
    intro k
    apply List.ext_getElem
    · simp [natBitsFixed]
    · intro i h1 h2
      simp [natBitsFixed]
  have htb : Primrec₂ (fun (k i : ℕ) => Nat.testBit k i) := by
    have h1 : Primrec (fun x : ℕ × ℕ => decide (x.1 / 2 ^ x.2 % 2 = 1)) := by
      refine PrimrecPred.decide (p := fun x : ℕ × ℕ => x.1 / 2 ^ x.2 % 2 = 1) ?_
      exact Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.fst
        (hpow.comp (Primrec.const 2) Primrec.snd)) (Primrec.const 2)) (Primrec.const 1)
    exact h1.of_eq fun x => Nat.testBit_eq_decide_div_mod_eq.symm
  have hbit : Primrec (natBitsFixed (alphabetWidth Γ)) := by
    have h2 : Primrec (fun k : ℕ => (List.range (alphabetWidth Γ)).map
        (fun i => Nat.testBit k i)) :=
      Primrec.list_map (Primrec.const (List.range (alphabetWidth Γ))) htb
    exact h2.of_eq fun k => (hnbf k).symm
  refine ⟨fun r => r.flatMap (natBitsFixed (alphabetWidth Γ)), ?_, ?_⟩
  · exact Primrec.list_flatMap Primrec.id (hbit.comp Primrec.snd).to₂
  · intro l
    change ((l.map (alphabetIndex Γ)).map (natBitsFixed (alphabetWidth Γ))).flatten =
      (l.map (alphabetCode Γ)).flatten
    rw [List.map_map]
    rfl

/-- Step 2 of the proof of `rightComplexity_le_crossingSequence`: the transition function
of `M` as a primitive recursive table on ranks: the states are numbered injectively by numbers below
`|Q|`, the letters by `alphabetIndex Γ`, and `T q a = (1, q', a', mv)` where `mv = delta + 1` if
`M.step` moves to `q'`, writes `a'` and moves by `delta`, and `T q a = (0, 0, 0, 0)` if `M` halts.
-/
private lemma rightComplexity_le_crossingSequence_table (M : TuringMachine Q Γ) :
    ∃ (qr : Q → ℕ) (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ),
      Function.Injective qr ∧ (∀ q, qr q < Fintype.card Q) ∧
      Primrec (fun x : ℕ × ℕ => T x.1 x.2) ∧
      ∀ (q : Q) (a : Γ), T (qr q) (alphabetIndex Γ a) =
        match M.step q a with
        | none => (0, 0, 0, 0)
        | some (q', a', d) => (1, qr q', alphabetIndex Γ a', (d.delta + 1).toNat) := by
  classical
  let eQ : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  have hbij : Function.Bijective
      (fun a : Γ => (⟨alphabetIndex Γ a, alphabetIndex_lt_card a⟩ : Fin (Fintype.card Γ))) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun a b h => alphabetIndex_injective (congrArg Fin.val h), by simp⟩
  let eΓ : Γ ≃ Fin (Fintype.card Γ) := Equiv.ofBijective _ hbij
  have heΓ : ∀ a, (eΓ a : ℕ) = alphabetIndex Γ a := fun a => rfl
  let value : Q → Γ → ℕ × ℕ × ℕ × ℕ := fun q a =>
    match M.step q a with
    | none => (0, 0, 0, 0)
    | some (q', a', d) => (1, (eQ q' : ℕ), alphabetIndex Γ a', (d.delta + 1).toNat)
  let tab : List (List (ℕ × ℕ × ℕ × ℕ)) :=
    List.ofFn fun i : Fin (Fintype.card Q) => List.ofFn fun j : Fin (Fintype.card Γ) =>
      value (eQ.symm i) (eΓ.symm j)
  refine ⟨fun q => (eQ q : ℕ), fun i j => (tab.getD i []).getD j (0, 0, 0, 0), ?_, ?_, ?_, ?_⟩
  · intro q q' h
    exact eQ.injective (Fin.ext h)
  · intro q
    exact (eQ q).isLt
  · exact (Primrec.list_getD (0, 0, 0, 0)).comp
      ((Primrec.list_getD ([] : List (ℕ × ℕ × ℕ × ℕ))).comp (Primrec.const tab) Primrec.fst)
      Primrec.snd
  · intro q a
    have hi : (eQ q : ℕ) < tab.length := by simp [tab]
    have hrow : tab.getD (eQ q) [] =
        List.ofFn fun j : Fin (Fintype.card Γ) => value (eQ.symm (eQ q)) (eΓ.symm j) := by
      rw [List.getD_eq_getElem _ _ hi]
      simp [tab]
    have hj : (alphabetIndex Γ a) < (List.ofFn fun j : Fin (Fintype.card Γ) =>
        value (eQ.symm (eQ q)) (eΓ.symm j)).length := by
      simpa using alphabetIndex_lt_card a
    change (tab.getD (eQ q) []).getD (alphabetIndex Γ a) (0, 0, 0, 0) = _
    rw [hrow, List.getD_eq_getElem _ _ hj]
    simp [value, eQ, eΓ]

private lemma rightComplexity_le_crossingSequence_aux_primrec_trim (b0 : ℕ) :
    Primrec (rightComplexity_le_crossingSequence_trim b0) := by
  have hp : Primrec (fun x : ℕ => x == b0) :=
    Primrec.beq.comp Primrec.id (Primrec.const b0)
  exact Primrec.list_reverse.comp ((Primrec.list_dropWhile hp).comp Primrec.list_reverse)

private lemma rightComplexity_le_crossingSequence_aux_primrec_replicate (b0 : ℕ) :
    Primrec (fun n : ℕ => List.replicate n b0) := by
  have h : Primrec (fun n : ℕ => (List.range n).map (fun _ => b0)) :=
    Primrec.list_map Primrec.list_range (Primrec.const b0).to₂
  refine h.of_eq fun n => ?_
  simp

private lemma rightComplexity_le_crossingSequence_aux_primrec_headD :
    Primrec (fun l : List ℕ => l.headD 0) := by
  refine (Primrec.list_headI (α := ℕ)).of_eq fun l => ?_
  cases l <;> rfl

private lemma rightComplexity_le_crossingSequence_aux_primrec_simStep
    (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) (hT : Primrec (fun x : ℕ × ℕ => T x.1 x.2)) (b0 : ℕ) :
    Primrec (rightComplexity_le_crossingSequence_simStep T b0) := by
  -- projections of the state
  have hTape : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ => st.1) := Primrec.fst
  have hFlag : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ => st.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hQ : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ => st.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hH : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ => st.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hPend : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ => st.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  -- the symbol under the head and the transition found in the table
  have hRead : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ => st.1.getD st.2.2.2.1 b0) :=
    (Primrec.list_getD b0).comp hTape hH
  have hr : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      T st.2.2.1 (st.1.getD st.2.2.2.1 b0)) :=
    hT.comp (hQ.pair hRead)
  have hr1 : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).1) := Primrec.fst.comp hr
  have hr2 : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hr)
  have hr3 : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hr))
  have hr4 : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hr))
  -- the conditions
  have hc1 : PrimrecPred (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ => st.2.1 = 0) :=
    Primrec.eq.comp hFlag (Primrec.const 0)
  have hc2 : PrimrecPred (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ => st.2.2.2.2 = []) :=
    Primrec.eq.comp hPend (Primrec.const [])
  have hc3 : PrimrecPred (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).1 = 0) :=
    Primrec.eq.comp hr1 (Primrec.const 0)
  have hc4 : PrimrecPred (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      st.2.2.2.1 + (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.2 = 0) :=
    Primrec.eq.comp (Primrec.nat_add.comp hH hr4) (Primrec.const 0)
  -- the outside branch
  have hOut : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      (st.1, 1, st.2.2.2.2.headD 0, 0, st.2.2.2.2.tail)) :=
    hTape.pair ((Primrec.const 1).pair
      ((rightComplexity_le_crossingSequence_aux_primrec_headD.comp hPend).pair
        ((Primrec.const 0).pair (Primrec.list_tail.comp hPend))))
  -- the inside branch
  have hTape' : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      st.1.take st.2.2.2.1 ++ (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.1 ::
        st.1.drop (st.2.2.2.1 + 1)) :=
    Primrec.list_append.comp (Primrec.list_take.comp hH hTape)
      (Primrec.list_cons.comp hr3
        (Primrec.list_drop.comp (Primrec.nat_add.comp hH (Primrec.const 1)) hTape))
  have hFlag' : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      if st.2.2.2.1 + (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.2 = 0 then 0 else 1) :=
    Primrec.ite hc4 (Primrec.const 0) (Primrec.const 1)
  have hHead' : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      st.2.2.2.1 + (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.2 - 1) :=
    Primrec.nat_sub.comp (Primrec.nat_add.comp hH hr4) (Primrec.const 1)
  have hIn : Primrec (fun st : List ℕ × ℕ × ℕ × ℕ × List ℕ =>
      (st.1.take st.2.2.2.1 ++ (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.1 ::
          st.1.drop (st.2.2.2.1 + 1),
        if st.2.2.2.1 + (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.2 = 0 then 0 else 1,
        (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.1,
        st.2.2.2.1 + (T st.2.2.1 (st.1.getD st.2.2.2.1 b0)).2.2.2 - 1,
        st.2.2.2.2)) :=
    hTape'.pair (hFlag'.pair (hr2.pair (hHead'.pair hPend)))
  unfold rightComplexity_le_crossingSequence_simStep
  exact Primrec.ite hc1 (Primrec.ite hc2 Primrec.id hOut) (Primrec.ite hc3 Primrec.id hIn)

/-- Step 3 of the proof of `rightComplexity_le_crossingSequence`: the finite simulation is
a primitive recursive function of the crossing states, the number of steps and the offset, when the
transition table is primitive recursive. -/
private lemma rightComplexity_le_crossingSequence_primrec_simulate
    (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) (hT : Primrec (fun x : ℕ × ℕ => T x.1 x.2)) (b0 : ℕ) :
    Primrec (fun x : List ℕ × ℕ × ℕ =>
      rightComplexity_le_crossingSequence_simulate T b0 x.1 x.2.1 x.2.2) := by
  have hstep := rightComplexity_le_crossingSequence_aux_primrec_simStep T hT b0
  have hs : Primrec (fun x : List ℕ × ℕ × ℕ => x.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun x : List ℕ × ℕ × ℕ => x.2.2) := Primrec.snd.comp Primrec.snd
  have hA : Primrec (fun x : List ℕ × ℕ × ℕ => x.1) := Primrec.fst
  have hinit : Primrec (fun x : List ℕ × ℕ × ℕ => (List.replicate x.2.1 b0, 0, 0, 0, x.1)) :=
    ((rightComplexity_le_crossingSequence_aux_primrec_replicate b0).comp hs).pair
      ((Primrec.const 0).pair ((Primrec.const 0).pair ((Primrec.const 0).pair hA)))
  have hiter : Primrec (fun x : List ℕ × ℕ × ℕ =>
      (rightComplexity_le_crossingSequence_simStep T b0)^[x.2.1]
        (List.replicate x.2.1 b0, 0, 0, 0, x.1)) :=
    Primrec.nat_iterate hs hinit (hstep.comp₂ Primrec₂.right)
  have hdrop : Primrec (fun x : List ℕ × ℕ × ℕ =>
      ((rightComplexity_le_crossingSequence_simStep T b0)^[x.2.1]
        (List.replicate x.2.1 b0, 0, 0, 0, x.1)).1.drop (min x.2.2 x.2.1)) :=
    Primrec.list_drop.comp (Primrec.nat_min.comp hd hs) (Primrec.fst.comp hiter)
  unfold rightComplexity_le_crossingSequence_simulate
  exact (rightComplexity_le_crossingSequence_aux_primrec_trim b0).comp hdrop

/-- The invariant relating a state `r` of the replay after `j` steps to a state `st` of the finite
simulation with a window of length `s`. -/
private def rightComplexity_le_crossingSequence_aux_Rel (M : TuringMachine Q Γ)
    (qr : Q → ℕ) (p : ℤ) (s j : ℕ) (r : ReplayState Q Γ)
    (st : List ℕ × ℕ × ℕ × ℕ × List ℕ) : Prop :=
  st.1.length = s ∧
  (∀ i : ℕ, i < s →
    st.1.getD i (alphabetIndex Γ M.blank) = alphabetIndex Γ (r.tape (p + 1 + i))) ∧
  (∀ i : ℤ, p + j ≤ i → r.tape i = M.blank) ∧
  st.2.2.2.2 = r.pending.map qr ∧
  (r.inside = none → st.2.1 = 0) ∧
  (∀ (q' : Q) (h' : ℤ), r.inside = some (q', h') →
    st.2.1 ≠ 0 ∧ st.2.2.1 = qr q' ∧ h' = p + 1 + st.2.2.2.1 ∧ st.2.2.2.1 + 1 ≤ j)

omit [Fintype Q] in
/-- One step of the induction of Step 4a: `simStep` commutes with `replayStep` for the invariant
`Rel`, as long as the number of steps stays below the length `s` of the window. -/
private lemma rightComplexity_le_crossingSequence_aux_step (M : TuringMachine Q Γ)
    (qr : Q → ℕ) (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ)
    (hT : ∀ (q : Q) (a : Γ), T (qr q) (alphabetIndex Γ a) =
        match M.step q a with
        | none => (0, 0, 0, 0)
        | some (q', a', d) => (1, qr q', alphabetIndex Γ a', (d.delta + 1).toNat))
    (p : ℤ) (s j : ℕ) (hj : j < s) (r : ReplayState Q Γ) (st : List ℕ × ℕ × ℕ × ℕ × List ℕ)
    (hrel : rightComplexity_le_crossingSequence_aux_Rel M qr p s j r st) :
    rightComplexity_le_crossingSequence_aux_Rel M qr p s (j + 1) (M.replayStep p r)
      (rightComplexity_le_crossingSequence_simStep T (alphabetIndex Γ M.blank) st) := by
  obtain ⟨rt, ri, rp⟩ := r
  obtain ⟨tp, fl, q, h, pend⟩ := st
  obtain ⟨hlen, hwin, hblank, hpend, hnone, hsome⟩ := hrel
  simp only at hlen hwin hblank hpend hnone hsome
  rcases ri with _ | ⟨q0, h0⟩
  · -- the head is on the left of the border
    have hfl : fl = 0 := hnone rfl
    subst hfl
    rcases rp with _ | ⟨q1, rest⟩
    · -- no crossing state left: nothing happens
      have hp : pend = [] := by simpa using hpend
      subst hp
      have h1 : M.replayStep p ⟨rt, none, []⟩ = ⟨rt, none, []⟩ := rfl
      have h2 : rightComplexity_le_crossingSequence_simStep T (alphabetIndex Γ M.blank)
          (tp, 0, q, h, []) = (tp, 0, q, h, []) := by
        simp [rightComplexity_le_crossingSequence_simStep]
      rw [h1, h2]
      refine ⟨hlen, hwin, fun i hi => hblank i (by omega), hpend, fun _ => rfl, ?_⟩
      intro q' h' hh
      exact absurd hh (by simp)
    · -- the next crossing state puts the head on `p + 1`
      have hp : pend = qr q1 :: rest.map qr := by simpa using hpend
      subst hp
      have h1 : M.replayStep p ⟨rt, none, q1 :: rest⟩ = ⟨rt, some (q1, p + 1), rest⟩ := rfl
      have h2 : rightComplexity_le_crossingSequence_simStep T (alphabetIndex Γ M.blank)
          (tp, 0, q, h, qr q1 :: rest.map qr) = (tp, 1, qr q1, 0, rest.map qr) := by
        simp [rightComplexity_le_crossingSequence_simStep]
      rw [h1, h2]
      refine ⟨hlen, hwin, fun i hi => hblank i (by omega), rfl, fun hh => absurd hh (by simp), ?_⟩
      intro q' h' hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      refine ⟨by simp, rfl, by simp, by simp⟩
  · -- the head is on the right of the border, at the cell `h0`
    obtain ⟨hfl, hq, hh0, hhj⟩ := hsome q0 h0 rfl
    have hread : tp.getD h (alphabetIndex Γ M.blank) = alphabetIndex Γ (rt h0) := by
      rw [hwin h (by omega), hh0]
    rcases hstep : M.step q0 (rt h0) with _ | ⟨q', a, d⟩
    · -- the machine halts: nothing changes
      have hTv : T q (tp.getD h (alphabetIndex Γ M.blank)) = (0, 0, 0, 0) := by
        rw [hread, hq, hT, hstep]
      have h1 : M.replayStep p ⟨rt, some (q0, h0), rp⟩ = ⟨rt, some (q0, h0), rp⟩ := by
        simp [replayStep, hstep]
      have h2 : rightComplexity_le_crossingSequence_simStep T (alphabetIndex Γ M.blank)
          (tp, fl, q, h, pend) = (tp, fl, q, h, pend) := by
        unfold rightComplexity_le_crossingSequence_simStep
        dsimp only
        rw [ite_eq_right hfl, hTv]
        simp
      rw [h1, h2]
      refine ⟨hlen, hwin, fun i hi => hblank i (by omega), hpend, hnone, ?_⟩
      intro q' h' hh
      obtain ⟨a1, a2, a3, a4⟩ := hsome q' h' hh
      exact ⟨a1, a2, a3, by simp only at a4 ⊢; omega⟩
    · -- the machine makes a step
      have hd : (-1 : ℤ) ≤ d.delta ∧ d.delta ≤ 1 := by cases d <;> simp [TapeMove.delta]
      have hTv : T q (tp.getD h (alphabetIndex Γ M.blank)) =
          (1, qr q', alphabetIndex Γ a, (d.delta + 1).toNat) := by
        rw [hread, hq, hT, hstep]
      have h1 : M.replayStep p ⟨rt, some (q0, h0), rp⟩ =
          ⟨Function.update rt h0 a,
            if h0 + d.delta ≤ p then none else some (q', h0 + d.delta), rp⟩ := by
        simp [replayStep, hstep]
      have h2 : rightComplexity_le_crossingSequence_simStep T (alphabetIndex Γ M.blank)
          (tp, fl, q, h, pend) =
          (tp.take h ++ alphabetIndex Γ a :: tp.drop (h + 1),
            if h + (d.delta + 1).toNat = 0 then 0 else 1, qr q',
            h + (d.delta + 1).toNat - 1, pend) := by
        unfold rightComplexity_le_crossingSequence_simStep
        dsimp only
        rw [ite_eq_right hfl, hTv]
        simp
      rw [h1, h2]
      have hlt' : h < tp.length := by omega
      refine ⟨?_, ?_, ?_, hpend, ?_, ?_⟩
      · -- the window keeps its length
        simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
        omega
      · -- the window
        intro i hi
        dsimp only
        have hset : tp.take h ++ alphabetIndex Γ a :: tp.drop (h + 1) =
            tp.set h (alphabetIndex Γ a) := by
          rw [List.set_eq_take_append_cons_drop, ite_eq_left hlt']
        rw [hset, List.getD_eq_getElem?_getD, List.getElem?_set]
        by_cases hih : h = i
        · rw [← hih, ← hh0, Function.update_self]
          simp [hlt']
        · have hne : p + 1 + (i : ℤ) ≠ h0 := by omega
          rw [Function.update_of_ne hne, ite_eq_right hih, ← List.getD_eq_getElem?_getD]
          exact hwin i hi
      · -- the cells from `p + j + 1` on are blank
        intro i hi
        dsimp only
        have hne : i ≠ h0 := by omega
        rw [Function.update_of_ne hne]
        exact hblank i (by omega)
      · -- the head is on the left of the border again
        intro hh
        dsimp only at hh ⊢
        by_cases hc : h0 + d.delta ≤ p
        · rw [ite_eq_left (show h + (d.delta + 1).toNat = 0 by omega)]
        · rw [ite_eq_right hc] at hh
          exact absurd hh (by simp)
      · -- the head is on the right of the border
        intro q'' h'' hh
        dsimp only at hh ⊢
        by_cases hc : h0 + d.delta ≤ p
        · rw [ite_eq_left hc] at hh
          exact absurd hh (by simp)
        · rw [ite_eq_right hc] at hh
          simp only [Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          have hne : h + (d.delta + 1).toNat ≠ 0 := by omega
          rw [ite_eq_right hne]
          refine ⟨by simp, rfl, by omega, by omega⟩

omit [Fintype Q] in
/-- The induction of Step 4a: the invariant `Rel` holds after `j ≤ s` steps. -/
private lemma rightComplexity_le_crossingSequence_aux_iter (M : TuringMachine Q Γ)
    (qr : Q → ℕ) (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ)
    (hT : ∀ (q : Q) (a : Γ), T (qr q) (alphabetIndex Γ a) =
        match M.step q a with
        | none => (0, 0, 0, 0)
        | some (q', a', d) => (1, qr q', alphabetIndex Γ a', (d.delta + 1).toNat))
    (p : ℤ) (S : List Q) (s : ℕ) :
    ∀ j ≤ s, rightComplexity_le_crossingSequence_aux_Rel M qr p s j
      (M.replayRight p (fun _ => M.blank) S j)
      ((rightComplexity_le_crossingSequence_simStep T (alphabetIndex Γ M.blank))^[j]
        (List.replicate s (alphabetIndex Γ M.blank), 0, 0, 0, S.map qr)) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨by simp, ?_, fun i _ => rfl, rfl, fun _ => rfl, ?_⟩
    · intro i hi
      change (List.replicate s (alphabetIndex Γ M.blank)).getD i (alphabetIndex Γ M.blank) =
        alphabetIndex Γ M.blank
      exact List.getD_replicate _ hi
    · intro q' h' hh
      exact absurd hh (by simp [replayRight])
  | succ j ih =>
    intro hj
    have hrel := ih (by omega)
    have hr : M.replayRight p (fun _ => M.blank) S (j + 1) =
        M.replayStep p (M.replayRight p (fun _ => M.blank) S j) :=
      Function.iterate_succ_apply' _ _ _
    rw [hr, Function.iterate_succ_apply']
    exact rightComplexity_le_crossingSequence_aux_step M qr T hT p s j (by omega) _ _ hrel

omit [Fintype Q] in
/-- Step 4a of the proof of `rightComplexity_le_crossingSequence`: after `s` steps the
window of the finite simulation (a list of length `s`) holds the ranks of the cells `p + 1, …, p +
s`
of the replay on the right of the border `p` from the blank tape and the crossing sequence `S`,
and the cells after `p + s` of the replay are blank (the head moves by at most one cell per step,
and the first step puts it on `p + 1`).  The proof is an induction on the number of steps `j ≤ s`:
`simStep` commutes with `replayStep`, with the invariants that the head offset is below `j` and the
cells from `p + j` on are blank. -/
private lemma rightComplexity_le_crossingSequence_window (M : TuringMachine Q Γ)
    (qr : Q → ℕ) (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ)
    (hT : ∀ (q : Q) (a : Γ), T (qr q) (alphabetIndex Γ a) =
        match M.step q a with
        | none => (0, 0, 0, 0)
        | some (q', a', d) => (1, qr q', alphabetIndex Γ a', (d.delta + 1).toNat))
    (p : ℤ) (S : List Q) (s : ℕ) :
    ((rightComplexity_le_crossingSequence_simStep T (alphabetIndex Γ M.blank))^[s]
        (List.replicate s (alphabetIndex Γ M.blank), 0, 0, 0, S.map qr)).1.length = s ∧
    (∀ i : ℕ, i < s →
      ((rightComplexity_le_crossingSequence_simStep T (alphabetIndex Γ M.blank))^[s]
        (List.replicate s (alphabetIndex Γ M.blank), 0, 0, 0, S.map qr)).1.getD i
          (alphabetIndex Γ M.blank) =
        alphabetIndex Γ ((M.replayRight p (fun _ => M.blank) S s).tape (p + 1 + i))) ∧
    (∀ i : ℤ, p + s < i → (M.replayRight p (fun _ => M.blank) S s).tape i = M.blank) := by
  obtain ⟨hlen, hwin, hblank, -⟩ :=
    rightComplexity_le_crossingSequence_aux_iter M qr T hT p S s s le_rfl
  exact ⟨hlen, hwin, fun i hi => hblank i hi.le⟩

/-- Trimming a trailing `b0` removes it. -/
private lemma rightComplexity_le_crossingSequence_aux_trim_concat_pos (b0 : ℕ)
    (l : List ℕ) : rightComplexity_le_crossingSequence_trim b0 (l ++ [b0]) =
      rightComplexity_le_crossingSequence_trim b0 l := by
  simp [rightComplexity_le_crossingSequence_trim]

/-- Trimming a list that ends with a letter other than `b0` changes nothing. -/
private lemma rightComplexity_le_crossingSequence_aux_trim_concat_neg (b0 x : ℕ)
    (l : List ℕ) (h : x ≠ b0) :
    rightComplexity_le_crossingSequence_trim b0 (l ++ [x]) = l ++ [x] := by
  simp [rightComplexity_le_crossingSequence_trim, h]

/-- Trimming the trailing `b0`s of the first `n` values of `f`, when `f` is `b0` from `K` on and
`f (K - 1) ≠ b0`, keeps the first `K` values. -/
private lemma rightComplexity_le_crossingSequence_aux_trim_map_range (b0 : ℕ) (f : ℕ → ℕ) :
    ∀ (n K : ℕ), K ≤ n → (∀ k, K ≤ k → k < n → f k = b0) → (K = 0 ∨ f (K - 1) ≠ b0) →
      rightComplexity_le_crossingSequence_trim b0 ((List.range n).map f) =
        (List.range K).map f := by
  intro n
  induction n with
  | zero =>
    intro K hK _ _
    have hK0 : K = 0 := by omega
    subst hK0
    simp [rightComplexity_le_crossingSequence_trim]
  | succ n ih =>
    intro K hK hz hnz
    have hr : (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by
      rw [List.range_succ, List.map_append]
      rfl
    rw [hr]
    by_cases hKn : K = n + 1
    · subst hKn
      have hne : f n ≠ b0 := by
        rcases hnz with h | h
        · omega
        · simpa using h
      rw [rightComplexity_le_crossingSequence_aux_trim_concat_neg b0 (f n) _ hne, ← hr]
    · have hKn' : K ≤ n := by omega
      have hfn : f n = b0 := hz n hKn' (Nat.lt_succ_self n)
      rw [hfn, rightComplexity_le_crossingSequence_aux_trim_concat_pos]
      exact ih K hKn' (fun k hk hkn => hz k hk (Nat.lt_succ_of_lt hkn)) hnz

omit [Fintype Q] [Fintype Γ] [Encodable Γ] in
/-- `rightContents` with the natural-number index written out (its definition goes through a
coercion of the list `List.range _` to a list of integers). -/
lemma rightComplexity_le_crossingSequence_aux_rightContents
    (M : TuringMachine Q Γ) (τ : ℤ → Γ) (b : ℤ) :
    M.rightContents τ b =
      (List.range (M.contentLength τ b)).map (fun k : ℕ => τ (b + 1 + (k : ℤ))) := by
  simp [TuringMachine.rightContents, ← List.map_eq_flatMap, List.map_map]

omit [Fintype Q] in
/-- Step 4b of the proof of `rightComplexity_le_crossingSequence`: reading the content
`R` of the cells after `p + d` from a window `tp` of length `s` holding the ranks of the cells
`p + 1, …, p + s`, when the cells after `p + s` are blank: it is `tp` after the offset `min d s`,
without the trailing blanks (the rank of the blank is `b0`; the cells after `p + d` are
`τ (p + d + 1 + k)`, and `contentLength` is the position of the last non-blank cell). -/
private lemma rightComplexity_le_crossingSequence_readout (M : TuringMachine Q Γ)
    (p : ℤ) (τ : ℤ → Γ) (s d : ℕ) (tp : List ℕ) (hlen : tp.length = s)
    (htp : ∀ i : ℕ, i < s → tp.getD i (alphabetIndex Γ M.blank) =
      alphabetIndex Γ (τ (p + 1 + i)))
    (hblank : ∀ i : ℤ, p + s < i → τ i = M.blank) :
    rightComplexity_le_crossingSequence_trim (alphabetIndex Γ M.blank) (tp.drop (min d s)) =
      (M.rightContents τ (p + d)).map (alphabetIndex Γ) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ,
      f = fun k : ℕ => alphabetIndex Γ (τ (p + (d : ℤ) + 1 + (k : ℤ))) := ⟨_, rfl⟩
  have hfb : ∀ k : ℕ, f k = alphabetIndex Γ M.blank ↔ τ (p + (d : ℤ) + 1 + (k : ℤ)) = M.blank := by
    intro k
    rw [hf]
    exact alphabetIndex_injective.eq_iff
  have hW : tp.drop (min d s) = (List.range (s - d)).map f := by
    apply List.ext_getElem
    · simp only [List.length_drop, List.length_map, List.length_range, hlen]
      omega
    · intro i h1 h2
      have hi : i < s - d := by simpa using h2
      have hds : d < s := by omega
      have hmin : min d s = d := min_eq_left hds.le
      have hlt : d + i < s := by omega
      have h3 := htp (d + i) hlt
      rw [List.getD_eq_getElem _ _ (by omega)] at h3
      simp only [List.getElem_drop, List.getElem_map, List.getElem_range, hmin]
      rw [h3, hf]
      simp only
      congr 2
      push_cast
      ring
  have hex : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → τ (p + (d : ℤ) + 1 + (k : ℤ)) = M.blank :=
    ⟨s - d, fun k hk => hblank _ (by omega)⟩
  have hCL : M.contentLength τ (p + d) = Nat.find hex := by
    unfold TuringMachine.contentLength
    simp only [hex, ↓reduceDIte]
  have hspec : ∀ k : ℕ, Nat.find hex ≤ k → τ (p + (d : ℤ) + 1 + (k : ℤ)) = M.blank :=
    Nat.find_spec hex
  have hle : Nat.find hex ≤ s - d :=
    Nat.find_min' hex (fun k hk => hblank _ (by omega))
  have hnz : Nat.find hex = 0 ∨ f (Nat.find hex - 1) ≠ alphabetIndex Γ M.blank := by
    by_cases h0 : Nat.find hex = 0
    · exact Or.inl h0
    · right
      have hm := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      push Not at hm
      obtain ⟨k, hk, hk'⟩ := hm
      have hkeq : k = Nat.find hex - 1 := by
        by_contra hne
        exact hk' (hspec k (by omega))
      subst hkeq
      intro hfeq
      exact hk' ((hfb _).1 hfeq)
  rw [hW, rightComplexity_le_crossingSequence_aux_trim_map_range _ f (s - d) _ hle
    (fun k hk _ => (hfb k).2 (hspec k hk)) hnz,
    rightComplexity_le_crossingSequence_aux_rightContents, hCL, List.map_map, hf]
  rfl

omit [Fintype Q] in
/-- Step 4 of the proof of `rightComplexity_le_crossingSequence`: the finite simulation
computes, in ranks, the content of the cells after `p + d` of the replay on the right of the border
`p` from the blank tape and the crossing sequence `S`. -/
private lemma rightComplexity_le_crossingSequence_simulate_eq (M : TuringMachine Q Γ)
    (qr : Q → ℕ) (T : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ)
    (hT : ∀ (q : Q) (a : Γ), T (qr q) (alphabetIndex Γ a) =
        match M.step q a with
        | none => (0, 0, 0, 0)
        | some (q', a', d) => (1, qr q', alphabetIndex Γ a', (d.delta + 1).toNat))
    (p : ℤ) (S : List Q) (s d : ℕ) :
    rightComplexity_le_crossingSequence_simulate T (alphabetIndex Γ M.blank) (S.map qr) s d =
      (M.rightContents (M.replayRight p (fun _ => M.blank) S s).tape (p + d)).map
        (alphabetIndex Γ) := by
  obtain ⟨hlen, htp, hblank⟩ :=
    rightComplexity_le_crossingSequence_window M qr T hT p S s
  exact rightComplexity_le_crossingSequence_readout M p _ s d _ hlen htp hblank

/-- Auxiliary for Step 5a: the base-`m` numeral of a list of digits below `m` is below `m ^ |A|`. -/
private lemma rightComplexity_le_crossingSequence_aux_lt (m : ℕ) :
    ∀ A : List ℕ, (∀ x ∈ A, x < m) →
      A.foldr (fun x acc => x + m * acc) 0 < m ^ A.length := by
  intro A
  induction A with
  | nil => intro _; simp
  | cons x A ih =>
    intro h
    have hx : x < m := h x (by simp)
    have hA : ∀ y ∈ A, y < m := fun y hy => h y (by simp [hy])
    have ih' := ih hA
    simp only [List.foldr_cons, List.length_cons]
    set n := A.foldr (fun x acc => x + m * acc) 0 with hn
    calc x + m * n < m + m * n := by omega
      _ = m * (n + 1) := by ring
      _ ≤ m * m ^ A.length := Nat.mul_le_mul_left m ih'
      _ = m ^ (A.length + 1) := by ring

/-- Auxiliary for Step 5a: the `i`-th digit of the base-`m` numeral is the `i`-th entry. -/
private lemma rightComplexity_le_crossingSequence_aux_digit (m : ℕ) :
    ∀ A : List ℕ, (∀ x ∈ A, x < m) → ∀ (i : ℕ) (hi : i < A.length),
      A.foldr (fun x acc => x + m * acc) 0 / m ^ i % m = A[i] := by
  intro A
  induction A with
  | nil => intro _ i hi; simp at hi
  | cons x A ih =>
    intro h i hi
    have hx : x < m := h x (by simp)
    have hA : ∀ y ∈ A, y < m := fun y hy => h y (by simp [hy])
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le x) hx
    simp only [List.foldr_cons]
    set n := A.foldr (fun x acc => x + m * acc) 0 with hn
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one, List.getElem_cons_zero]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hx
    | succ j =>
      have hj : j < A.length := by simpa using hi
      simp only [List.getElem_cons_succ]
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hm,
        Nat.div_eq_of_lt hx, zero_add]
      exact ih hA j hj

/-- Step 5a of the proof of `rightComplexity_le_crossingSequence`: lists of numbers below
`m` are coded by base-`m` numerals: `num A < m ^ |A|`, and `A` is recovered from `|A|` and `num A`
by
a primitive recursive function of `(l, N)`: its digits `N / m ^ i % m`, `i < l`. -/
private lemma rightComplexity_le_crossingSequence_numeral (m : ℕ) :
    ∃ (num : List ℕ → ℕ) (dig : ℕ → ℕ → List ℕ),
      Primrec (fun x : ℕ × ℕ => dig x.1 x.2) ∧
      ∀ A : List ℕ, (∀ x ∈ A, x < m) → num A < m ^ A.length ∧ dig A.length (num A) = A := by
  refine ⟨fun A => A.foldr (fun x acc => x + m * acc) 0,
    fun l N => (List.range l).map (fun i => N / m ^ i % m), ?_, ?_⟩
  · have hpow : Primrec₂ (fun (a b : ℕ) => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow
    refine Primrec.list_map (Primrec.list_range.comp Primrec.fst) ?_
    exact (Primrec.nat_mod.comp (Primrec.nat_div.comp (Primrec.snd.comp Primrec.fst)
      (hpow.comp (Primrec.const m) Primrec.snd)) (Primrec.const m)).to₂
  · intro A hA
    refine ⟨rightComplexity_le_crossingSequence_aux_lt m A hA, ?_⟩
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact rightComplexity_le_crossingSequence_aux_digit m A hA i h2

/- A fixed-width block of a number below `2 ^ w` reads back as that number. -/
private lemma rightComplexity_le_crossingSequence_aux_bitsToNat_natBitsFixed (w : ℕ) :
    ∀ k, k < 2 ^ w → bitsToNat (natBitsFixed w k) = k := by
  induction w with
  | zero => intro k hk; obtain rfl : k = 0 := (by simpa using hk); rfl
  | succ w ih =>
    intro k hk
    have hk2 : k / 2 < 2 ^ w := by rw [pow_succ] at hk; omega
    have hsplit : natBitsFixed (w + 1) k = Nat.testBit k 0 :: natBitsFixed w (k / 2) := by
      simp [natBitsFixed, List.ofFn_succ, Nat.testBit_succ]
    rw [hsplit]
    simp only [bitsToNat, List.foldr_cons]
    change 2 * bitsToNat (natBitsFixed w (k / 2)) + _ = k
    rw [ih _ hk2]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [Nat.testBit_zero, h] <;> omega

/- The binary length of a positive number is at most `log₂ n + 1`. -/
private lemma rightComplexity_le_crossingSequence_aux_size_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.size n : ℝ) ≤ Real.logb 2 n + 1 := by
  have hpos : 0 < Nat.size n := Nat.size_pos.mpr (by omega)
  have h1 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
  have h3 : (2 : ℝ) ^ (Nat.size n - 1) ≤ n := by exact_mod_cast h1
  have h2 : ((Nat.size n - 1 : ℕ) : ℝ) ≤ Real.logb 2 n := by
    calc ((Nat.size n - 1 : ℕ) : ℝ) = Real.logb 2 ((2 : ℝ) ^ (Nat.size n - 1)) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
      _ ≤ Real.logb 2 n := Real.logb_le_logb_of_le (by norm_num) (by positivity) h3
  have h4 : ((Nat.size n - 1 : ℕ) : ℝ) = (Nat.size n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  linarith

/- The unary prefix is read back. -/
private lemma rightComplexity_le_crossingSequence_aux_takeWhile (w : ℕ) (r : BitString) :
    (List.replicate w true ++ false :: r).takeWhile id = List.replicate w true := by
  induction w with
  | zero => simp
  | succ w ih => simp [List.replicate_succ, ih]

/- The unary prefix and the separator are dropped. -/
private lemma rightComplexity_le_crossingSequence_aux_drop (w : ℕ) (r : BitString) :
    (List.replicate w true ++ false :: r).drop (w + 1) = r := by
  induction w with
  | zero => simp
  | succ w ih => simpa [List.replicate_succ] using ih

/-- Step 5 of the proof of `rightComplexity_le_crossingSequence`: a code for a list `A`
of numbers below `m`, a number of steps `s` and an offset `e ≤ s`, when `|A| ≤ t` and `s ≤ 2 t`: the
code has length at most `|A| log m + 4 log t + c₀`: the unary width `w = size (2 t)` and a
separator,
the three numbers `|A|`, `s`, `e` of `w` bits each, and the base-`m` numeral of `A` in
`size (m ^ |A|) ≤ |A| log m + 1` bits.  It is decoded by a primitive recursive function. -/
private lemma rightComplexity_le_crossingSequence_code (m : ℕ) :
    ∃ (parse : BitString → List ℕ × ℕ × ℕ) (prog : List ℕ → ℕ → ℕ → ℕ → BitString) (c₀ : ℝ),
      Primrec parse ∧
      ∀ (A : List ℕ), (∀ x ∈ A, x < m) → ∀ (s e t : ℕ), A.length ≤ t → s ≤ 2 * t → e ≤ s →
        parse (prog A s e t) = (A, s, e) ∧
        ((prog A s e t).length : ℝ) ≤ A.length * Real.logb 2 m + 4 * Real.logb 2 t + c₀ := by
  obtain ⟨num, dig, hdig, hnum⟩ := rightComplexity_le_crossingSequence_numeral m
  obtain ⟨g, hg_eq⟩ : ∃ g : ℕ × BitString → List ℕ × ℕ × ℕ, ∀ x : ℕ × BitString, g x =
      (dig (bitsToNat (x.2.take x.1)) (bitsToNat (((x.2.drop x.1).drop x.1).drop x.1)),
        bitsToNat ((x.2.drop x.1).take x.1),
        bitsToNat (((x.2.drop x.1).drop x.1).take x.1)) := ⟨_, fun _ => rfl⟩
  have hg : Primrec g := by
    have hd1 : Primrec (fun x : ℕ × BitString => x.2.drop x.1) :=
      Primrec.list_drop.comp Primrec.fst Primrec.snd
    have hd2 : Primrec (fun x : ℕ × BitString => (x.2.drop x.1).drop x.1) :=
      Primrec.list_drop.comp Primrec.fst hd1
    have hd3 : Primrec (fun x : ℕ × BitString => ((x.2.drop x.1).drop x.1).drop x.1) :=
      Primrec.list_drop.comp Primrec.fst hd2
    have hl : Primrec (fun x : ℕ × BitString => bitsToNat (x.2.take x.1)) :=
      bitsToNat_primrec.comp (Primrec.list_take.comp Primrec.fst Primrec.snd)
    have hs : Primrec (fun x : ℕ × BitString => bitsToNat ((x.2.drop x.1).take x.1)) :=
      bitsToNat_primrec.comp (Primrec.list_take.comp Primrec.fst hd1)
    have he : Primrec (fun x : ℕ × BitString =>
        bitsToNat (((x.2.drop x.1).drop x.1).take x.1)) :=
      bitsToNat_primrec.comp (Primrec.list_take.comp Primrec.fst hd2)
    have hN : Primrec (fun x : ℕ × BitString =>
        bitsToNat (((x.2.drop x.1).drop x.1).drop x.1)) :=
      bitsToNat_primrec.comp hd3
    exact Primrec.of_eq (Primrec.pair (hdig.comp (Primrec.pair hl hN)) (Primrec.pair hs he))
      fun x => (hg_eq x).symm
  refine ⟨fun p => g ((p.takeWhile id).length, p.drop ((p.takeWhile id).length + 1)),
    fun A s e t => List.replicate (Nat.size (2 * t)) true ++ false ::
      (natBitsFixed (Nat.size (2 * t)) A.length ++ (natBitsFixed (Nat.size (2 * t)) s ++
        (natBitsFixed (Nat.size (2 * t)) e ++ natBitsFixed (Nat.size (m ^ A.length)) (num A)))),
    10, ?_, ?_⟩
  · have hw : Primrec (fun p : BitString => (p.takeWhile id).length) :=
      Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id)
    have hrest : Primrec (fun p : BitString => p.drop ((p.takeWhile id).length + 1)) :=
      Primrec.list_drop.comp (Primrec.nat_add.comp hw (Primrec.const 1)) Primrec.id
    exact hg.comp (Primrec.pair hw hrest)
  · intro A hA s e t hAt hst hes
    obtain ⟨hnumlt, hdigeq⟩ := hnum A hA
    have hlw : A.length < 2 ^ Nat.size (2 * t) :=
      lt_of_le_of_lt (by omega) (Nat.lt_size_self (2 * t))
    have hsw : s < 2 ^ Nat.size (2 * t) := lt_of_le_of_lt hst (Nat.lt_size_self (2 * t))
    have hew : e < 2 ^ Nat.size (2 * t) :=
      lt_of_le_of_lt (hes.trans hst) (Nat.lt_size_self (2 * t))
    have hNB : num A < 2 ^ Nat.size (m ^ A.length) := lt_trans hnumlt (Nat.lt_size_self _)
    refine ⟨?_, ?_⟩
    · simp only [rightComplexity_le_crossingSequence_aux_takeWhile,
        rightComplexity_le_crossingSequence_aux_drop, List.length_replicate]
      rw [hg_eq]
      simp only [List.take_left' (length_natBitsFixed _ _), List.drop_left' (length_natBitsFixed _
          _),
        rightComplexity_le_crossingSequence_aux_bitsToNat_natBitsFixed _ _ hlw,
        rightComplexity_le_crossingSequence_aux_bitsToNat_natBitsFixed _ _ hsw,
        rightComplexity_le_crossingSequence_aux_bitsToNat_natBitsFixed _ _ hew,
        rightComplexity_le_crossingSequence_aux_bitsToNat_natBitsFixed _ _ hNB, hdigeq]
    · have hlen : (List.replicate (Nat.size (2 * t)) true ++ false ::
          (natBitsFixed (Nat.size (2 * t)) A.length ++ (natBitsFixed (Nat.size (2 * t)) s ++
            (natBitsFixed (Nat.size (2 * t)) e ++
              natBitsFixed (Nat.size (m ^ A.length)) (num A))))).length =
          4 * Nat.size (2 * t) + 1 + Nat.size (m ^ A.length) := by
        simp only [List.length_append, List.length_replicate, List.length_cons,
          length_natBitsFixed]
        omega
      rw [hlen]
      have hwle : (Nat.size (2 * t) : ℝ) ≤ Real.logb 2 t + 2 := by
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht
          simp
        · have h := rightComplexity_le_crossingSequence_aux_size_le (2 * t) (by omega)
          have h2 : Real.logb 2 ((2 * t : ℕ) : ℝ) = 1 + Real.logb 2 t := by
            push_cast
            rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
          linarith
      have hBle : (Nat.size (m ^ A.length) : ℝ) ≤ A.length * Real.logb 2 m + 1 := by
        rcases Nat.eq_zero_or_pos A.length with hl | hl
        · rw [hl]
          simp
        · obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hl
          have hm : 1 ≤ m := by have := hA x hx; omega
          have h := rightComplexity_le_crossingSequence_aux_size_le (m ^ A.length)
            (Nat.one_le_pow _ _ (by omega))
          have h2 : Real.logb 2 ((m ^ A.length : ℕ) : ℝ) = A.length * Real.logb 2 m := by
            push_cast
            rw [Real.logb_pow]
          linarith
      push_cast
      linarith

/-- Step 6 of the proof of `rightComplexity_le_crossingSequence`: if a bit string depends
primitive recursively on `(A, s, e)`, then its complexity is at most `|A| log m + 4 log t + c`
for `A` a list of numbers below `m`, `|A| ≤ t`, `e ≤ s ≤ 2 t`. -/
private lemma rightComplexity_le_crossingSequence_assembly (V : Map)
    (hV : isOptimalConditional V) (m : ℕ) (sim : List ℕ × ℕ × ℕ → BitString) (hsim : Primrec sim) :
    ∃ c : ℝ, ∀ (A : List ℕ), (∀ x ∈ A, x < m) → ∀ (s e t : ℕ), A.length ≤ t → s ≤ 2 * t →
      e ≤ s → ((plainK V (sim (A, s, e))).toNat : ℝ) ≤
        A.length * Real.logb 2 m + 4 * Real.logb 2 t + c := by
  obtain ⟨parse, prog, c₀, hparse, hprog⟩ := rightComplexity_le_crossingSequence_code m
  have hdec : Computable (fun p : BitString => sim (parse p)) := (hsim.comp hparse).to_comp
  obtain ⟨c1, hc1⟩ := plainK_map_le V hV (fun p => sim (parse p)) hdec
  obtain ⟨c2, hc2⟩ := plainK_le_length V hV
  refine ⟨c₀ + c1 + c2, fun A hA s e t hAt hst hes => ?_⟩
  obtain ⟨hp1, hp2⟩ := hprog A hA s e t hAt hst hes
  have h1 : plainK V (sim (A, s, e)) ≤ (((prog A s e t).length + c2 + c1 : ℕ) : ℕ∞) := by
    have h := hc1 (prog A s e t)
    have h' := hc2 (prog A s e t)
    simp only [hp1] at h
    calc plainK V (sim (A, s, e)) ≤ plainK V (prog A s e t) + (c1 : ℕ∞) := h
      _ ≤ ((prog A s e t).length : ℕ∞) + (c2 : ℕ∞) + (c1 : ℕ∞) := by gcongr
      _ = (((prog A s e t).length + c2 + c1 : ℕ) : ℕ∞) := by push_cast; rfl
  have h2 : (plainK V (sim (A, s, e))).toNat ≤ (prog A s e t).length + c2 + c1 :=
    ENat.toNat_le_of_le_natCast h1
  have h3 : ((plainK V (sim (A, s, e))).toNat : ℝ) ≤ ((prog A s e t).length : ℝ) + c2 + c1 := by
    exact_mod_cast h2
  linarith

/-- **SUV p. 234**, the inequality of the proof of Theorem 152.  For each of the `b + 1` borders of
the buffer, between the cells `a + k` and `a + k + 1` with `k ≤ b`, one has
`C(R(t)) ≤ l(S) log m + 4 log t + c`, with `S` the sequence of left-to-right crossings of that
border up to `t`, exactly as defined on p. 234 in both editions.  The constant
may depend on the fixed `M`, optimal decompressor `V`, and alphabet encoding. -/
theorem rightComplexity_le_crossingSequence (V : Map) (hV : isOptimalConditional V)
    (M : TuringMachine Q Γ) :
    ∃ c : ℝ, ∀ (a : ℤ) (b : ℕ) (k : ℕ), k ≤ b → ∀ c₀ : TapeConfig Q Γ, c₀.head ≤ a →
      (∀ i, a < i → c₀.tape i = M.blank) → ∀ t : ℕ,
        rightComplexity V M (M.run c₀ t).tape (a + b) ≤
          (M.crossingSequence c₀ (a + k) t).length * Real.logb 2 (Fintype.card Q) +
            4 * Real.logb 2 t + c := by
  obtain ⟨qr, T, hqr, hqrlt, hTp, hTspec⟩ :=
    rightComplexity_le_crossingSequence_table M
  obtain ⟨enc, henc, hencspec⟩ := rightComplexity_le_crossingSequence_enc (Γ := Γ)
  have hsim : Primrec (fun x : List ℕ × ℕ × ℕ => enc
      (rightComplexity_le_crossingSequence_simulate T (alphabetIndex Γ M.blank)
        x.1 x.2.1 x.2.2)) :=
    henc.comp (rightComplexity_le_crossingSequence_primrec_simulate T hTp _)
  obtain ⟨c, hc⟩ := rightComplexity_le_crossingSequence_assembly V hV (Fintype.card Q) _ hsim
  refine ⟨c, fun a b k hk c₀ hhead hblank t => ?_⟩
  have hp : c₀.head ≤ a + k := by omega
  obtain ⟨s, hs, htape⟩ := M.run_right_eq_replayRight c₀ hp (τ := fun _ => M.blank)
    (fun i hi => (hblank i (by omega)).symm) t
  have hlen : (M.crossingSequence c₀ (a + k) t).length ≤ t := by
    unfold crossingSequence
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  have hcont : M.rightContents (M.run c₀ t).tape (a + b) =
      M.rightContents (M.replayRight (a + k) (fun _ => M.blank)
        (M.crossingSequence c₀ (a + k) t) s).tape (a + b) :=
    rightComplexity_le_crossingSequence_rightContents_congr M
      (fun i hi => (htape i (by omega)).symm)
  have hab : a + (b : ℤ) = (a + k) + ((b - k : ℕ) : ℤ) := by omega
  have hword : wordBits Γ (M.rightContents (M.run c₀ t).tape (a + b)) =
      enc (rightComplexity_le_crossingSequence_simulate T (alphabetIndex Γ M.blank)
        ((M.crossingSequence c₀ (a + k) t).map qr) s (min (b - k) s)) := by
    rw [hcont, hab, ← hencspec]
    congr 1
    rw [← rightComplexity_le_crossingSequence_simulate_eq M qr T hTspec (a + k)
      (M.crossingSequence c₀ (a + k) t) s (b - k)]
    unfold rightComplexity_le_crossingSequence_simulate
    rw [min_assoc, min_self]
  have h := hc ((M.crossingSequence c₀ (a + k) t).map qr)
    (fun x hx => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
      exact hqrlt q)
    s (min (b - k) s) t (by simpa using hlen) (by omega) (min_le_right _ _)
  unfold rightComplexity
  rw [hword]
  simpa using h

end Kolmogorov.Applications
