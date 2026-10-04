/-
Copyright (c) 2024 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Authors
-/
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.MonotoneComplexity.APrioriAtoms.Basic
import KolmogorovMathlib.MonotoneComplexity.Omega.Exercises
import KolmogorovMathlib.Prefix.Encoding

/-!
# The computable sequences with an unpredictable last zero

Fix a code `c` for an optimal prefix decompressor.  For a parameter `n` the sequence
`haltStream c n` prints the self-delimiting code `natCode n` of `n` and then, at every stage
`t = 0, 1, 2, …`, a zero if some program of length at most `n` is discovered to halt exactly at
stage `t` and a one otherwise.  The stage `t = 0` is declared a discovery stage by fiat, which
is the note's initial zero: it guarantees that the sequence has at least one and only finitely
many zeros, so that `haltStream c n = x01^∞` for a unique finite word `x = haltWord c n`.

The stage of the last discovery is `lastStage c n`, and the note's identity
`T = |x_n| - |e(n)|` is `lastStage_eq_length_sub`: reading `haltWord c n` one recovers both `n`
and a stage by which every halting program of length at most `n` has halted.

Source: the note `apriori-atoms.md`, section "Почему обратная оценка неверна"; SUV Chapter 5,
§5.2.
-/

open scoped ENNReal

namespace Kolmogorov

open Nat.Partrec (Code)

/-- A program of length at most `n` is discovered to halt at stage `t`: it halts within `t`
steps but not within `t - 1` steps.  Stage `0` counts as a discovery stage by convention — this
is the note's initial zero, which makes the set of discovery stages nonempty.

Source: the note `apriori-atoms.md`, section "Почему обратная оценка неверна"; SUV Chapter 5,
§5.2. -/
def discoveryStage (c : Code) (n t : ℕ) : Bool :=
  decide (t = 0) ||
    decide (0 < (boundedPrograms n).countP
      (fun p => haltsWithin c t p && !haltsWithin c (t - 1) p))

/-- Stage `0` is a discovery stage. -/
@[simp] theorem discoveryStage_zero (c : Code) (n : ℕ) : discoveryStage c n 0 = true := by
  simp [discoveryStage]

/-- No computation has returned after zero steps. -/
@[simp] theorem haltsWithin_zero (c : Code) (p : BitString) : haltsWithin c 0 p = false := by
  by_contra hcon
  have h1 : haltsWithin c 0 p = true := by simpa using hcon
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h1
  exact absurd (Nat.Partrec.Code.evaln_bound (Option.mem_def.mpr hx)) (Nat.not_lt_zero _)

/-- A discovery stage other than `0` carries a witness: a short program whose computation
returns exactly then. -/
theorem exists_haltsWithin_of_discoveryStage {c : Code} {n t : ℕ}
    (h : discoveryStage c n t = true) (ht : t ≠ 0) :
    ∃ p ∈ boundedPrograms n, haltsWithin c t p = true ∧ haltsWithin c (t - 1) p = false := by
  simp only [discoveryStage, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h ht
  · rw [List.countP_pos_iff] at h
    obtain ⟨p, hp, hpt⟩ := h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpt
    exact ⟨p, hp, hpt.1, hpt.2⟩

/-- Halting within `t` steps is a primitive recursive property of `t` and the program. -/
private theorem primrec_haltsWithin (c : Code) :
    Primrec₂ (fun (t : ℕ) (p : BitString) => haltsWithin c t p) :=
  Primrec.option_isSome.comp ((evaln_primrec c).comp Primrec.fst
    (Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.const ([] : BitString)))))

/-- The discovery stages are decidable uniformly in the parameter and the stage: `evaln` runs
the finitely many programs of length at most `n` for the two step budgets `t` and `t - 1`.

Source: the note `apriori-atoms.md`, section "Почему обратная оценка неверна"; SUV Chapter 5,
§5.2. -/
theorem computable_discoveryStage (c : Code) : Computable₂ (discoveryStage c) := by
  have hlist : Primrec (fun q : ℕ × ℕ => boundedPrograms q.1) :=
    primrec_boundedPrograms.comp Primrec.fst
  have h1 : Primrec (fun r : (ℕ × ℕ) × BitString => haltsWithin c r.1.2 r.2) :=
    (primrec_haltsWithin c).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have h2 : Primrec (fun r : (ℕ × ℕ) × BitString => haltsWithin c (r.1.2 - 1) r.2) :=
    (primrec_haltsWithin c).comp
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)) Primrec.snd
  have hstep : Primrec₂ (fun (q : ℕ × ℕ) (p : BitString) =>
      haltsWithin c q.2 p && !haltsWithin c (q.2 - 1) p) :=
    Primrec.and.comp h1 (Primrec.not.comp h2)
  have hcount : Primrec (fun q : ℕ × ℕ => (boundedPrograms q.1).countP
      (fun p => haltsWithin c q.2 p && !haltsWithin c (q.2 - 1) p)) :=
    list_countP_primrec hlist hstep
  have hpos : Primrec (fun q : ℕ × ℕ => decide (0 < (boundedPrograms q.1).countP
      (fun p => haltsWithin c q.2 p && !haltsWithin c (q.2 - 1) p))) :=
    (PrimrecRel.decide Primrec.nat_lt).comp (Primrec.const 0) hcount
  have hzero : Primrec (fun q : ℕ × ℕ => decide (q.2 = 0)) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 0))
  exact (Primrec.or.comp hzero hpos).to_comp

/-- The sequence `α_n` of the note: the code of `n`, then a zero at every discovery stage and a
one at every other stage.

Source: the note `apriori-atoms.md`, section "Почему обратная оценка неверна"; SUV Chapter 5,
§5.2. -/
def haltStream (c : Code) (n : ℕ) : CantorSeq :=
  prependCantor (natCode n) (fun t => !discoveryStage c n t)

/-- Prepending reads the finite string where it has an entry and the tail beyond it. -/
private theorem prependCantor_apply (x : BitString) (rest : CantorSeq) (i : ℕ) :
    prependCantor x rest i = (x[i]?).getD (rest (i - x.length)) := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    simp [prependCantor, h]
  · rw [List.getElem?_eq_none (by omega)]
    simp [prependCantor, h]

/-- The sequences `α_n` are computable uniformly in `n`.

Source: the note `apriori-atoms.md`, section "Большая масса атома"; SUV Chapter 5, §5.2. -/
theorem computable_haltStream (c : Code) :
    Computable₂ (fun (n i : ℕ) => haltStream c n i) := by
  have hcode : Primrec (fun q : ℕ × ℕ => natCode q.1) := primrec_natCode.comp Primrec.fst
  have hget : Primrec (fun q : ℕ × ℕ => (natCode q.1)[q.2]?) :=
    Primrec.list_getElem?.comp hcode Primrec.snd
  have hlen : Primrec (fun q : ℕ × ℕ => q.2 - (natCode q.1).length) :=
    Primrec.nat_sub.comp Primrec.snd (Primrec.list_length.comp hcode)
  have hds : Computable (fun q : ℕ × ℕ =>
      discoveryStage c q.1 (q.2 - (natCode q.1).length)) :=
    Computable₂.comp (computable_discoveryStage c) Computable.fst hlen.to_comp
  have hrest : Computable (fun q : ℕ × ℕ =>
      !discoveryStage c q.1 (q.2 - (natCode q.1).length)) :=
    Primrec.not.to_comp.comp hds
  refine (Computable.option_getD hget.to_comp hrest).of_eq (fun q => ?_)
  simp only [haltStream]
  rw [prependCantor_apply]

/-- Every discovery stage is bounded by the maximal halting time of the programs of length at
most `n`: at a discovery stage some such program returns for the first time.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem discoveryStage_le_maxHaltTime {c : Code} {n t : ℕ} (h : discoveryStage c n t = true) :
    t ≤ maxHaltTime c n := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact Nat.zero_le _
  obtain ⟨p, hp, h1, h2⟩ := exists_haltsWithin_of_discoveryStage h (by omega)
  have hmem : t ∈ haltStepSet c p := h1
  have hne : (haltStepSet c p).Nonempty := ⟨t, hmem⟩
  have hinf : sInf (haltStepSet c p) = t := by
    refine le_antisymm (Nat.sInf_le hmem) ?_
    by_contra hlt
    push Not at hlt
    have hmem2 : haltsWithin c (sInf (haltStepSet c p)) p = true := Nat.sInf_mem hne
    have hprev : haltsWithin c (t - 1) p = true :=
      haltsWithin_mono c (by omega) p hmem2
    rw [h2] at hprev
    exact Bool.noConfusion hprev
  have hhalt : haltTime c p = some t := by simp [haltTime, hne, hinf]
  exact le_maxHaltTime hp hhalt

/-- The discovery stages of the parameter `n`, a finite set containing `0`.

Source: the note `apriori-atoms.md`, section "Почему обратная оценка неверна"; SUV Chapter 5,
§5.2. -/
noncomputable def discoverySet (c : Code) (n : ℕ) : Finset ℕ :=
  (Finset.range (maxHaltTime c n + 1)).filter fun t => discoveryStage c n t = true

/-- The set of discovery stages is nonempty. -/
theorem zero_mem_discoverySet (c : Code) (n : ℕ) : 0 ∈ discoverySet c n := by
  simp [discoverySet]

/-- The stage `T` of the last discovery, `0` if no program of length at most `n` halts.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
noncomputable def lastStage (c : Code) (n : ℕ) : ℕ :=
  (discoverySet c n).max' ⟨0, zero_mem_discoverySet c n⟩

/-- The last stage is a discovery stage. -/
theorem discoveryStage_lastStage (c : Code) (n : ℕ) :
    discoveryStage c n (lastStage c n) = true := by
  have hmem := (discoverySet c n).max'_mem ⟨0, zero_mem_discoverySet c n⟩
  simp only [discoverySet, Finset.mem_filter] at hmem
  exact hmem.2

/-- No discovery happens after the last stage. -/
theorem le_lastStage {c : Code} {n t : ℕ} (h : discoveryStage c n t = true) :
    t ≤ lastStage c n := by
  refine Finset.le_max' _ t ?_
  simp only [discoverySet, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (discoveryStage_le_maxHaltTime h), h⟩

/-- **Every halting program of length at most `n` has returned by the last stage.**  Reading
the last stage off the word `haltWord c n` therefore yields all their outputs.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem haltsWithin_lastStage {c : Code} {n t : ℕ} {p : BitString}
    (hp : p ∈ boundedPrograms n) (h : haltsWithin c t p = true) :
    haltsWithin c (lastStage c n) p = true := by
  classical
  have hex : ∃ s, haltsWithin c s p = true := ⟨t, h⟩
  have hs : haltsWithin c (Nat.find hex) p = true := Nat.find_spec hex
  have hs0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, haltsWithin_zero] at hs
    exact Bool.noConfusion hs
  have hprev : haltsWithin c (Nat.find hex - 1) p = false := by
    have hlt := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    simpa using hlt
  have hdisc : discoveryStage c n (Nat.find hex) = true := by
    simp only [discoveryStage, Bool.or_eq_true, decide_eq_true_eq]
    refine Or.inr ?_
    rw [List.countP_pos_iff]
    exact ⟨p, hp, by simp [hs, hprev]⟩
  exact haltsWithin_mono c (le_lastStage hdisc) p hs

/-- The word `x_n` of the note: the finite part of `haltStream c n` before its last zero.

Source: the note `apriori-atoms.md`, section "Почему обратная оценка неверна"; SUV Chapter 5,
§5.2. -/
noncomputable def haltWord (c : Code) (n : ℕ) : BitString :=
  cantorPrefix (haltStream c n) (n + 1 + lastStage c n)

/-- The length of `x_n`. -/
@[simp] theorem length_haltWord (c : Code) (n : ℕ) :
    (haltWord c n).length = n + 1 + lastStage c n := by
  simp [haltWord]

/-- **`T = |x_n| - |e(n)|`.**  The last stage is recovered from the length of the word.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem lastStage_eq_length_sub (c : Code) (n : ℕ) :
    lastStage c n = (haltWord c n).length - (natCode n).length := by
  simp

/-- **The code of `n` is a prefix of `x_n`.**  The forced zero of stage `0` sits behind it, so
the word is long enough; hence `n` is recovered from `x_n`.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem natCode_prefix_haltWord (c : Code) (n : ℕ) : natCode n <+: haltWord c n := by
  have h1 : cantorPrefix (haltStream c n) (natCode n).length = natCode n :=
    cantorPrefix_prepend (natCode n) _
  rw [length_natCode] at h1
  have h2 : cantorPrefix (haltStream c n) (n + 1) <+:
      cantorPrefix (haltStream c n) (n + 1 + lastStage c n) :=
    cantorPrefix_mono _ (by omega)
  rwa [h1] at h2

/-- **`α_n = x_n01^∞`.**  The sequence has a zero at stage `0` and only finitely many zeros,
and `haltWord c n` is the part before the last one.

Source: the note `apriori-atoms.md`, section "Почему обратная оценка неверна"; SUV Chapter 5,
§5.2. -/
theorem haltStream_eq_atomSeq (c : Code) (n : ℕ) :
    haltStream c n = atomSeq (haltWord c n) := by
  have hlen : (haltWord c n).length = n + 1 + lastStage c n := length_haltWord c n
  have hstream : ∀ j, n + 1 ≤ j → haltStream c n j = !discoveryStage c n (j - (n + 1)) := by
    intro j hj
    simp only [haltStream]
    rw [prependCantor_apply, List.getElem?_eq_none (by simp; omega)]
    simp
  funext i
  rcases lt_trichotomy i (haltWord c n).length with h | h | h
  · rw [atomSeq_of_lt h]
    simp [haltWord]
  · rw [h, atomSeq_length, hstream _ (by omega)]
    have h2 : (haltWord c n).length - (n + 1) = lastStage c n := by omega
    rw [h2, discoveryStage_lastStage]
    rfl
  · rw [atomSeq_of_gt h, hstream i (by omega)]
    have hns : discoveryStage c n (i - (n + 1)) = false := by
      by_contra hcon
      have htrue : discoveryStage c n (i - (n + 1)) = true := by simpa using hcon
      have := le_lastStage htrue
      omega
    rw [hns]
    rfl

/-- The word `x_n` is the unique finite word with `α_n = x01^∞`.

Source: the note `apriori-atoms.md`, section "Почему обратная оценка неверна"; SUV Chapter 5,
§5.2. -/
theorem existsUnique_haltStream_eq_atomSeq (c : Code) (n : ℕ) :
    ∃! x : BitString, haltStream c n = atomSeq x := by
  refine ⟨haltWord c n, haltStream_eq_atomSeq c n, fun y hy => ?_⟩
  exact atomSeq_injective (hy.symm.trans (haltStream_eq_atomSeq c n))

end Kolmogorov
