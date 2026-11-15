/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison

/-!
# Countable Families

The stages of Ville's example (Shen, Uspensky and Vereshchagin, Section 9.4, pp. 268-269):
sequences on which given selection rules produce finite or balanced outputs.  The module defines
the counts `onesCount` and `zerosCount` of a prefix and the properties `ZerosDominate` and
`ZerosStrictlyDominate`.  The main results are `exists_alternating_selection` (for one rule the
selected bits alternate `0101…`), `exists_finite_family_balanced` (for `m` rules every output is
finite or balanced, and in each of its prefixes the zeros exceed the ones by at most `2^{m-1}`
and are never fewer) and `exists_countable_family_balanced` (for countably many rules every
output is finite or balanced and every prefix of the sequence has at least as many zeros as
ones).
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology

/-- The number of ones among the first `n` terms. -/
def onesCount (w : CantorSeq) (n : ℕ) : ℕ := (cantorPrefix w n).count true

/-- The number of zeros among the first `n` terms. -/
def zerosCount (w : CantorSeq) (n : ℕ) : ℕ := (cantorPrefix w n).count false

/-- Every prefix has at least as many zeros as ones (Theorem 172). -/
def ZerosDominate (w : CantorSeq) : Prop := ∀ n, onesCount w n ≤ zerosCount w n

/-- Every non-empty prefix has strictly more zeros than ones (Theorem 203(b)). -/
def ZerosStrictlyDominate (w : CantorSeq) : Prop := ∀ n, 0 < n → onesCount w n < zerosCount w n

/-- **SUV p. 268**, one rule: for every `R` there is `ω` such that the output `S_R(ω)` alternates
`0101…`, as far as it goes; the terms outside the selection are arbitrary. -/
private noncomputable def exists_alternating_selection_seqAux (R : Set BitString) (n : ℕ) : 
  Σ' (p : BitString), p.length = n :=
  Nat.recOn n ⟨[], rfl⟩ fun k ⟨prev, hlen⟩ =>
    let nextBit := decide ((selectedBits R prev).length % 2 = 1)
    have : Decidable (prev ∈ R) := Classical.propDecidable _
    ⟨prev ++ [if prev ∈ R then nextBit else false], by simp [hlen]⟩

private noncomputable def exists_alternating_selection_seq (R : Set BitString) : CantorSeq :=
  fun n => (exists_alternating_selection_seqAux R (n + 1)).1[n]!

private lemma exists_alternating_selection_cantorPrefix (R : Set BitString) (n : ℕ) :
    cantorPrefix (exists_alternating_selection_seq R) n = (exists_alternating_selection_seqAux R
        n).1 := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cantorPrefix_succ, ih]
    have h1 : (exists_alternating_selection_seqAux R (n + 1)).1 =
      (exists_alternating_selection_seqAux R n).1 ++ [if (exists_alternating_selection_seqAux R n).1
          ∈ R then
        decide ((selectedBits R (exists_alternating_selection_seqAux R n).1).length % 2 = 1) else
          false] := rfl
    have h2 : exists_alternating_selection_seq R n = (exists_alternating_selection_seqAux R
        (n + 1)).1[n]! := by rfl
    have h_len : (exists_alternating_selection_seqAux R n).1.length = n :=
        (exists_alternating_selection_seqAux R n).2
    rw [h2, h1]
    have h_get : ∀ (l : List Bool) (x : Bool), (l ++ [x])[l.length]! = x := fun l x => by simp
    have h_get2 := h_get (exists_alternating_selection_seqAux R n).1
      (if (exists_alternating_selection_seqAux R n).1 ∈ R then
        decide ((selectedBits R (exists_alternating_selection_seqAux R n).1).length % 2 = 1) else
          false)
    revert h_get2
    rw [h_len]
    intro h_get2
    rw [h_get2]

private lemma exists_alternating_selection_ind (R : Set BitString) (t : ℕ) :
    ∀ (k : ℕ) (hk : k < (selectedBits R (cantorPrefix (exists_alternating_selection_seq R)
        t)).length),
      (selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t))[k] = decide (k % 2 = 1)
          := by
  classical
  induction t with
  | zero =>
    intro k hk
    have h1 : cantorPrefix (exists_alternating_selection_seq R) 0 = [] := rfl
    rw [h1] at hk
    have h2 : selectedBits R [] = [] := rfl
    rw [h2] at hk
    simp at hk
  | succ t ih =>
    intro k hk
    have hh1 : cantorPrefix (exists_alternating_selection_seq R) (t + 1) =
      cantorPrefix (exists_alternating_selection_seq R) t ++ [exists_alternating_selection_seq R t]
          := cantorPrefix_succ _ _
    have hh2 : cantorPrefix (exists_alternating_selection_seq R) t =
        (exists_alternating_selection_seqAux R t).1 :=
        exists_alternating_selection_cantorPrefix R t
    have ht : selectedBits R (cantorPrefix (exists_alternating_selection_seq R) (t + 1)) =
      selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t ++
          [exists_alternating_selection_seq R t]) := by rw [hh1]
    have ht2 : selectedBits R (cantorPrefix (exists_alternating_selection_seq R) (t + 1)) =
      selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t) ++
        (if cantorPrefix (exists_alternating_selection_seq R) t ∈
            R then [exists_alternating_selection_seq R t] else []) := by
      rw [ht, selectedBits_append_singleton]
    revert hk
    rw [ht2]
    intro hk
    by_cases h : cantorPrefix (exists_alternating_selection_seq R) t ∈ R
    · have h_if : (if cantorPrefix (exists_alternating_selection_seq R) t ∈ R then
        [exists_alternating_selection_seq R t] else []) = [exists_alternating_selection_seq R t] :=
          ite_eq_left_iff.mpr (fun h_contra => (h_contra h).elim)
      have h1 : exists_alternating_selection_seq R t =
          decide ((selectedBits R (exists_alternating_selection_seqAux R t).1).length % 2 = 1) := by
        have : exists_alternating_selection_seq R t = (exists_alternating_selection_seqAux R
            (t + 1)).1[t]! := rfl
        rw [this]
        have h2 : (exists_alternating_selection_seqAux R (t + 1)).1 =
          (exists_alternating_selection_seqAux R t).1 ++
              [if (exists_alternating_selection_seqAux R t).1 ∈ R then
            decide ((selectedBits R (exists_alternating_selection_seqAux R t).1).length % 2 = 1)
                else false] := rfl
        rw [h2]
        have h_get : ∀ (l : List Bool) (x : Bool), (l ++ [x])[l.length]! = x := fun l x => by simp
        have h_len : (exists_alternating_selection_seqAux R t).1.length = t :=
            (exists_alternating_selection_seqAux R t).2
        have h3 := h_get (exists_alternating_selection_seqAux R t).1
          (if (exists_alternating_selection_seqAux R t).1 ∈ R then
            decide ((selectedBits R (exists_alternating_selection_seqAux R t).1).length % 2 = 1)
                else false)
        rw [h_len] at h3
        have h4 : (exists_alternating_selection_seqAux R t).1 ∈ R := by
          rwa [hh2] at h
        rw [h3]
        exact ite_eq_left_iff.mpr (fun h_contra => (h_contra h4).elim)
      have h_val : exists_alternating_selection_seq R t =
        decide ((selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t)).length % 2 =
            1) := by
        rw [h1]
        have heq_len : (selectedBits R (exists_alternating_selection_seqAux R t).1).length =
            (selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t)).length := by
              rw [hh2]
        rw [heq_len]
      have ht4 : selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t) ++
        (if cantorPrefix (exists_alternating_selection_seq R) t ∈ R then
          [exists_alternating_selection_seq R t] else []) =
            selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t) ++
              [decide ((selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t)).length
                  % 2 = 1)] := by
        rw [h_if, h_val]
      revert hk
      rw [ht4]
      intro hk
      rw [List.length_append, List.length_singleton] at hk
      by_cases hk_lt : k < (selectedBits R (cantorPrefix (exists_alternating_selection_seq R)
          t)).length
      · have h_get_l : (selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t) ++
          [decide (List.length (selectedBits R (cantorPrefix (exists_alternating_selection_seq R)
              t)) % 2 = 1)])[k] =
            (selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t))[k] :=
                List.getElem_append_left hk_lt
        rw [h_get_l]
        exact ih k hk_lt
      · have hk_eq : k = (selectedBits R (cantorPrefix (exists_alternating_selection_seq R)
          t)).length := by omega
        have h_get_r : ∀ (l : List Bool) (x : Bool), (l ++ [x])[l.length] = x := by
          intro l x
          have hh2 : (l ++ [x])[l.length] = [x][l.length - l.length] := List.getElem_append_right
              (by omega)
          have hh3 : l.length - l.length = 0 := Nat.sub_self _
          have hh4 : [x][l.length - l.length] = [x][0] := by
            congr
          rw [hh4] at hh2
          exact hh2
        subst hk_eq
        exact h_get_r _ _
    · have h_if2 : (if cantorPrefix (exists_alternating_selection_seq R) t ∈ R then
        [exists_alternating_selection_seq R t] else []) = [] :=
                                                      ite_eq_right_iff.mpr (fun h_contra =>
                                                        (h h_contra).elim)
      have ht4 : selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t) ++
          (if cantorPrefix (exists_alternating_selection_seq R) t ∈
              R then [exists_alternating_selection_seq R t] else []) =
            selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t) := by
              rw [h_if2, List.append_nil]
      revert hk
      rw [ht4]
      intro hk
      exact ih k hk

/-- **SUV p. 268**, one rule: for every `R` there is `ω` such that the output `S_R(ω)` alternates
`0101…`, as far as it goes; the terms outside the selection are arbitrary. -/
theorem exists_alternating_selection (R : Set BitString) :
    ∃ w : CantorSeq, ∀ (t k : ℕ) (hk : k < (selectChain R w t).length),
      (selectChain R w t)[k] = decide (k % 2 = 1) := by
  use exists_alternating_selection_seq R
  intro t k hk
  have hlen : (selectChain R (exists_alternating_selection_seq R) t).length =
    (selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t)).length := rfl
  have h_eq_get : ∀ i (hi : i < (selectChain R (exists_alternating_selection_seq R) t).length),
    (selectChain R (exists_alternating_selection_seq R) t)[i] =
      (selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t))[i] := fun _ _ => rfl
  have h_eq_get2 : (selectChain R (exists_alternating_selection_seq R) t)[k] =
    (selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t))[k] := h_eq_get k hk
  rw [h_eq_get2]
  have hk2 : k < (selectedBits R (cantorPrefix (exists_alternating_selection_seq R) t)).length := by
    rw [← hlen]
    exact hk
  exact exists_alternating_selection_ind R t k hk2

open Classical in
private noncomputable def exists_finite_family_balanced_prefixAux {m : ℕ} (R : Fin m →
    Set BitString) (n : ℕ) :
    Σ' (p : BitString), p.length = n :=
  Nat.recOn n ⟨[], rfl⟩ fun k ⟨prev, hlen⟩ =>
    let v := fun (i : Fin m) => prev ∈ R i
    let count := (List.range prev.length).countP
        (fun j => decide ((fun i => prev.take j ∈ R i) = v))
    let nextBit := count % 2 == 1
    ⟨prev ++ [nextBit], by simp [hlen]⟩

private noncomputable def exists_finite_family_balanced_prefix {m : ℕ} (R : Fin m → Set BitString)
    (n : ℕ) : BitString :=
  (exists_finite_family_balanced_prefixAux R n).1

private noncomputable def exists_finite_family_balanced_seq {m : ℕ} (R : Fin m → Set BitString) :
    CantorSeq :=
  fun n => (exists_finite_family_balanced_prefix R (n + 1))[n]!

/-- Step 1 of the proof of exists_finite_family_balanced: sequence prefixes are as
constructed. -/
private lemma exists_finite_family_balanced_cantorPrefix {m : ℕ} (R : Fin m → Set BitString)
    (n : ℕ) :
    cantorPrefix (exists_finite_family_balanced_seq R) n = exists_finite_family_balanced_prefix R
        n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cantorPrefix_succ, ih]
    have h1 : exists_finite_family_balanced_prefix R (n + 1) =
        (exists_finite_family_balanced_prefixAux R (n + 1)).1 := rfl
    have h2 : exists_finite_family_balanced_seq R n = (exists_finite_family_balanced_prefixAux R
        (n + 1)).1[n]! := by rfl
    have h_rec :
        (exists_finite_family_balanced_prefixAux R (n + 1)).1 =
          (exists_finite_family_balanced_prefixAux R n).1 ++
            [((List.range (exists_finite_family_balanced_prefixAux R n).1.length).countP
              (fun j => decide
                ((fun i => (exists_finite_family_balanced_prefixAux R n).1.take j ∈ R i) =
                  (fun i => (exists_finite_family_balanced_prefixAux R n).1 ∈ R i))) % 2 == 1)] :=
                      by
      rw [Nat.add_one]
      rfl
    have h_len : (exists_finite_family_balanced_prefixAux R n).1.length = n :=
        (exists_finite_family_balanced_prefixAux R n).2
    rw [h1, h_rec]
    have h_pref : exists_finite_family_balanced_prefix R n =
        (exists_finite_family_balanced_prefixAux R n).1 := rfl
    rw [h_pref]
    congr 2
    rw [h2, h_rec]
    have h_get : ∀ (l : List Bool) (x : Bool), (l ++ [x])[l.length]! = x := fun l x => by simp
    have h_get2 := h_get (exists_finite_family_balanced_prefixAux R n).1
        (((List.range (exists_finite_family_balanced_prefixAux R n).1.length).countP
        (fun j => decide ((fun i => (exists_finite_family_balanced_prefixAux R n).1.take j ∈ R i) =
                    (fun i => (exists_finite_family_balanced_prefixAux R n).1 ∈ R i))) % 2 == 1))
    have h_len2 : (exists_finite_family_balanced_prefixAux R n).1.length = n := h_len
    revert h_get2
    rw [h_len2]
    intro h_get2
    exact h_get2

open Classical in
private noncomputable def exists_finite_family_balanced_counts_type {m : ℕ} (R : Fin m →
    Set BitString) (x : BitString) : Finset (Fin m) :=
  Finset.univ.filter (fun i => x ∈ R i)

open Classical in
private noncomputable def exists_finite_family_balanced_counts_cn {m : ℕ} (R : Fin m →
    Set BitString) (w : CantorSeq) (n : ℕ) (T : Finset (Fin m)) : ℕ :=
  (List.range n).countP (fun k => decide (exists_finite_family_balanced_counts_type R
                                    (cantorPrefix w k) = T))

/-- The constructed bit is the parity of earlier occurrences of its selection type. -/
private lemma exists_finite_family_balanced_identity_bit_parity
    {m : ℕ} (R : Fin m → Set BitString) (n : ℕ) :
    exists_finite_family_balanced_seq R n = true ↔
      exists_finite_family_balanced_counts_cn R
        (exists_finite_family_balanced_seq R) n
        (exists_finite_family_balanced_counts_type R
          (cantorPrefix (exists_finite_family_balanced_seq R) n)) % 2 = 1 := by
  classical
  let p := exists_finite_family_balanced_prefix R n
  let c := (List.range p.length).countP (fun j =>
    decide ((fun i => p.take j ∈ R i) = (fun i => p ∈ R i)))
  have hlen : p.length = n := (exists_finite_family_balanced_prefixAux R n).2
  have hrec : exists_finite_family_balanced_prefix R (n + 1) =
      p ++ [c % 2 == 1] := by
    rfl
  have hb : exists_finite_family_balanced_seq R n = (c % 2 == 1) := by
    unfold exists_finite_family_balanced_seq
    rw [hrec, ← hlen]
    simp
  have htype (x y : BitString) :
      ((fun i => x ∈ R i) = (fun i => y ∈ R i)) ↔
        exists_finite_family_balanced_counts_type R x =
          exists_finite_family_balanced_counts_type R y := by
    constructor
    · intro h
      ext j
      simp only [exists_finite_family_balanced_counts_type, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact (congrFun h j).to_iff
    · intro h
      funext j
      apply propext
      have hj := Finset.ext_iff.mp h j
      simpa [exists_finite_family_balanced_counts_type] using hj
  have hc : c = exists_finite_family_balanced_counts_cn R
      (exists_finite_family_balanced_seq R) n
      (exists_finite_family_balanced_counts_type R
        (cantorPrefix (exists_finite_family_balanced_seq R) n)) := by
    dsimp [c]
    rw [hlen]
    unfold exists_finite_family_balanced_counts_cn
    apply List.countP_congr
    intro j hj
    have hjn : j ≤ n := by
      have := List.mem_range.mp hj
      omega
    have hp : p = cantorPrefix (exists_finite_family_balanced_seq R) n :=
      (exists_finite_family_balanced_cantorPrefix R n).symm
    rw [hp, cantorPrefix_take _ j n hjn]
    simpa only [decide_eq_true_eq] using
      htype (cantorPrefix (exists_finite_family_balanced_seq R) j)
        (cantorPrefix (exists_finite_family_balanced_seq R) n)
  rw [hb, hc]
  simp

/-- Only the type of the current prefix acquires one new occurrence. -/
private lemma exists_finite_family_balanced_identity_cn_succ
    {m : ℕ} (R : Fin m → Set BitString) (w : CantorSeq) (n : ℕ)
    (T : Finset (Fin m)) :
    exists_finite_family_balanced_counts_cn R w (n + 1) T =
      exists_finite_family_balanced_counts_cn R w n T +
        if exists_finite_family_balanced_counts_type R (cantorPrefix w n) = T
        then 1 else 0 := by
  classical
  simp [exists_finite_family_balanced_counts_cn, List.range_succ]

/-- The relevant odd-type set changes only at the type of the current prefix. -/
private lemma exists_finite_family_balanced_identity_odd_types_succ
    {m : ℕ} (R : Fin m → Set BitString) (w : CantorSeq) (i : Fin m) (n : ℕ) :
    let T₀ := exists_finite_family_balanced_counts_type R (cantorPrefix w n)
    let S := Finset.univ.filter (fun T : Finset (Fin m) =>
      i ∈ T ∧ exists_finite_family_balanced_counts_cn R w n T % 2 = 1)
    (Finset.univ.filter (fun T : Finset (Fin m) =>
      i ∈ T ∧ exists_finite_family_balanced_counts_cn R w (n + 1) T % 2 = 1)) =
      if i ∈ T₀ then
        if exists_finite_family_balanced_counts_cn R w n T₀ % 2 = 1
        then S.erase T₀ else insert T₀ S
      else S := by
  classical
  dsimp only
  split_ifs with hi ho
  all_goals
    ext T
    by_cases hT : exists_finite_family_balanced_counts_type R (cantorPrefix w n) = T
    · subst T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, Finset.mem_insert, ne_eq, not_true_eq_false, false_and,
        true_or, exists_finite_family_balanced_identity_cn_succ,
        ite_true]
      simp only [hi, true_and, false_and, iff_true, iff_false]
      -- this closes the case `i ∉ T₀`; otherwise a parity statement about the count remains
      all_goals omega
    · simp [exists_finite_family_balanced_identity_cn_succ,
        hT, Ne.symm hT]

/-- Step 1 of the proof of `exists_finite_family_balanced_counts`: the identity
between counts and odd types. -/
private lemma exists_finite_family_balanced_identity
    {m : ℕ} (R : Fin m → Set BitString) (i : Fin m) (n : ℕ) :
    (selectChain (R i) (exists_finite_family_balanced_seq R) n).count true +
      (Finset.univ.filter (fun T : Finset (Fin m) =>
        i ∈ T ∧
          exists_finite_family_balanced_counts_cn R
            (exists_finite_family_balanced_seq R) n T % 2 = 1)).card =
    (selectChain (R i) (exists_finite_family_balanced_seq R) n).count false := by
  classical
  let w := exists_finite_family_balanced_seq R
  change (selectChain (R i) w n).count true +
    (Finset.univ.filter (fun T : Finset (Fin m) =>
      i ∈ T ∧ exists_finite_family_balanced_counts_cn R w n T % 2 = 1)).card =
    (selectChain (R i) w n).count false
  induction n with
  | zero =>
    simp [selectChain, selectedBits, selectedAux, cantorPrefix,
      exists_finite_family_balanced_counts_cn]
  | succ n ih =>
    let T₀ := exists_finite_family_balanced_counts_type R (cantorPrefix w n)
    let S := Finset.univ.filter (fun T : Finset (Fin m) =>
      i ∈ T ∧ exists_finite_family_balanced_counts_cn R w n T % 2 = 1)
    have hsel : selectChain (R i) w (n + 1) =
        selectChain (R i) w n ++ (if i ∈ T₀ then [w n] else []) := by
      simp [selectChain, cantorPrefix_succ, selectedBits_append_singleton,
        T₀, exists_finite_family_balanced_counts_type]
    have hset := exists_finite_family_balanced_identity_odd_types_succ
      R w i n
    change (Finset.univ.filter (fun T : Finset (Fin m) =>
      i ∈ T ∧ exists_finite_family_balanced_counts_cn R w (n + 1) T % 2 = 1)) =
      (if i ∈ T₀ then
        if exists_finite_family_balanced_counts_cn R w n T₀ % 2 = 1
        then S.erase T₀ else insert T₀ S
      else S) at hset
    have hpar : w n = true ↔
        exists_finite_family_balanced_counts_cn R w n T₀ % 2 = 1 :=
      exists_finite_family_balanced_identity_bit_parity R n
    have hmem : T₀ ∈ S ↔
        i ∈ T₀ ∧ exists_finite_family_balanced_counts_cn R w n T₀ % 2 = 1 := by
      simp [S]
    change (selectChain (R i) w n).count true + S.card =
      (selectChain (R i) w n).count false at ih
    rw [hsel, hset]
    by_cases hi : i ∈ T₀
    · rw [ite_eq_left hi, ite_eq_left hi]
      by_cases ho : exists_finite_family_balanced_counts_cn R w n T₀ % 2 = 1
      · have hb := hpar.mpr ho
        have hcard := Finset.card_erase_add_one (hmem.mpr ⟨hi, ho⟩)
        simp [ho, hb]
        omega
      · have hb : w n = false := by
          cases hbit : w n
          · rfl
          · exact False.elim (ho (hpar.mp hbit))
        have hnot : T₀ ∉ S := fun h => ho (hmem.mp h).2
        have hcard := Finset.card_insert_of_notMem hnot
        simp [ho, hb]
        omega
    · simp only [ite_eq_right hi, List.append_nil]
      exact ih

private lemma exists_finite_family_balanced_bound_cancel {α : Type _}
    [DecidableEq α] (s t : Finset α) :
    symmDiff (symmDiff s t) t = s := by
  ext x
  simp only [Finset.mem_symmDiff]
  tauto

/-- Step 2 of the proof of `exists_finite_family_balanced_counts`: the bound on the
number of types containing a specific index. -/
private lemma exists_finite_family_balanced_bound
    {m : ℕ} (i : Fin m) :
    (Finset.univ.filter (fun T : Finset (Fin m) => i ∈ T)).card ≤ 2 ^ (m - 1) := by
  let f : Finset (Fin m) ↪ Finset (Fin m) := ⟨fun T => symmDiff T {i}, by
    intro a b h
    have h' : symmDiff a {i} = symmDiff b {i} := h
    have : symmDiff (symmDiff a {i}) {i} = symmDiff (symmDiff b {i}) {i} := by rw [h']
    rw [exists_finite_family_balanced_bound_cancel,
      exists_finite_family_balanced_bound_cancel] at this
    exact this⟩
  let S := Finset.univ.filter (fun T : Finset (Fin m) => i ∈ T)
  let S' := Finset.univ.filter (fun T : Finset (Fin m) => i ∉ T)
  have h1 : S.card = S'.card := by
    rw [← Finset.card_map f]
    congr 1
    ext x
    simp only [S, S', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨a, h_mem, rfl⟩
      change i ∉ symmDiff a {i}
      rw [Finset.mem_symmDiff]
      intro h
      cases h with
      | inl h_inl =>
        have ⟨_, h2⟩ := h_inl
        exact h2 (Finset.mem_singleton_self i)
      | inr h_inr =>
        have ⟨_, h2⟩ := h_inr
        exact h2 h_mem
    · rintro h_not_mem
      use symmDiff x {i}
      constructor
      · rw [Finset.mem_symmDiff]
        right
        constructor
        · exact Finset.mem_singleton_self i
        · exact h_not_mem
      · exact exists_finite_family_balanced_bound_cancel x {i}
  have h2 : S.card + S'.card = (Finset.univ : Finset (Finset (Fin m))).card := by
    have h_disj : Disjoint S S' := by
      rw [Finset.disjoint_filter]
      intro x hx
      exact not_not_intro
    have h_union : S ∪ S' = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, S, S']
      exact iff_true_intro (Classical.em (i ∈ x))
    rw [← Finset.card_union_of_disjoint h_disj, h_union]
  have h3 : (Finset.univ : Finset (Finset (Fin m))).card = 2 ^ m := by
    simp
  have hm : m > 0 := by
    have := i.isLt
    omega
  have h4 : 2 * S.card = 2 ^ m := by omega
  have h5 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h5] at h4
  
  exact Nat.eq_of_mul_eq_mul_left (by decide) h4 |>.le

/-- Step 3 of the proof of `exists_finite_family_balanced_counts`: the parity link
explicitly. -/
private lemma exists_finite_family_balanced_bit_parity
    {m : ℕ} (R : Fin m → Set BitString) (n : ℕ) :
    exists_finite_family_balanced_seq R n = true ↔
      exists_finite_family_balanced_counts_cn R
        (exists_finite_family_balanced_seq R) n
        (exists_finite_family_balanced_counts_type R
          (cantorPrefix (exists_finite_family_balanced_seq R) n)) % 2 = 1 := by
  classical
  have h_seq : exists_finite_family_balanced_seq R n =
    (exists_finite_family_balanced_prefixAux R (n + 1)).1[n]! := rfl
  have h_rec : (exists_finite_family_balanced_prefixAux R (n + 1)).1 =
      (exists_finite_family_balanced_prefixAux R n).1 ++
        [((List.range (exists_finite_family_balanced_prefixAux R n).1.length).countP
          (fun j => decide ((fun i => (exists_finite_family_balanced_prefixAux R n).1.take j ∈ R i)
                      =
            (fun i => (exists_finite_family_balanced_prefixAux R n).1 ∈ R i))) % 2 == 1)] := rfl
  have h_len : (exists_finite_family_balanced_prefixAux R n).1.length = n :=
    (exists_finite_family_balanced_prefixAux R n).2
  have h_pref : cantorPrefix (exists_finite_family_balanced_seq R) n =
      (exists_finite_family_balanced_prefixAux R n).1 :=
    exists_finite_family_balanced_cantorPrefix R n
  
  have h_get : ∀ (l : List Bool) (x : Bool), (l ++ [x])[l.length]! = x := fun l x => by simp
  have h_get2 := h_get (exists_finite_family_balanced_prefixAux R n).1
    (((List.range (exists_finite_family_balanced_prefixAux R n).1.length).countP
      (fun j => decide ((fun i => (exists_finite_family_balanced_prefixAux R n).1.take j ∈ R i) =
        (fun i => (exists_finite_family_balanced_prefixAux R n).1 ∈ R i))) % 2 == 1))
  
  rw [h_seq, h_rec]
  have h_len_subst : (exists_finite_family_balanced_prefixAux R n).1.length = n := h_len
  simp only [h_len_subst]
  simp only [h_len_subst] at h_get2
  rw [h_get2]
  rw [←h_pref]
  
  have h_countP_eq : (List.range (cantorPrefix (exists_finite_family_balanced_seq R)
      n).length).countP
    (fun j => decide
      ((fun i => (cantorPrefix (exists_finite_family_balanced_seq R) n).take j ∈ R i) =
        fun i => cantorPrefix (exists_finite_family_balanced_seq R) n ∈ R i)) =
      exists_finite_family_balanced_counts_cn R (exists_finite_family_balanced_seq R) n
        (exists_finite_family_balanced_counts_type R
          (cantorPrefix (exists_finite_family_balanced_seq R) n)) := by
    unfold exists_finite_family_balanced_counts_cn
    rw [cantorPrefix_length]
    refine List.countP_congr ?_
    intro k hk
    rw [List.mem_range] at hk
    have hk_lt : k ≤ n := le_of_lt hk
    have h_take : (cantorPrefix (exists_finite_family_balanced_seq R) n).take k =
      cantorPrefix (exists_finite_family_balanced_seq R) k := by
      exact cantorPrefix_take (exists_finite_family_balanced_seq R) k n hk_lt
    rw [h_take]
    unfold exists_finite_family_balanced_counts_type
    have h_iff : ((fun i => cantorPrefix (exists_finite_family_balanced_seq R) k ∈ R i) =
        fun i => cantorPrefix (exists_finite_family_balanced_seq R) n ∈ R i) ↔
      (Finset.univ.filter (fun i => cantorPrefix (exists_finite_family_balanced_seq R) k ∈ R i) =
        Finset.univ.filter (fun i => cantorPrefix (exists_finite_family_balanced_seq R) n ∈ R i)) :=
            by
      constructor
      · intro h
        ext i
        have h1 := congrFun h i
        have h1' : cantorPrefix (exists_finite_family_balanced_seq R) k ∈ R i ↔ cantorPrefix
            (exists_finite_family_balanced_seq R) n ∈ R i := iff_of_eq h1
        rw [Finset.mem_filter, Finset.mem_filter]
        exact and_congr_right_iff.mpr (fun _ => h1')
      · intro h
        ext i
        have h1 : i ∈ Finset.univ.filter (fun i => cantorPrefix (exists_finite_family_balanced_seq
                                                     R) k ∈ R i) ↔
          i ∈ Finset.univ.filter (fun i => cantorPrefix (exists_finite_family_balanced_seq R) n ∈
                                             R i) := by
          rw [h]
        rw [Finset.mem_filter, Finset.mem_filter] at h1
        have h2 := and_congr_right_iff.mp h1 (Finset.mem_univ i)
        exact h2
    by_cases H : ((fun i => cantorPrefix (exists_finite_family_balanced_seq R) k ∈ R i) =
      fun i => cantorPrefix (exists_finite_family_balanced_seq R) n ∈ R i)
    · rw [decide_eq_true H, decide_eq_true (h_iff.mp H)]
    · rw [decide_eq_false H, decide_eq_false (fun h => H (h_iff.mpr h))]
  rw [cantorPrefix_length] at h_countP_eq
  rw [h_countP_eq]
  have h_dec_mod : ∀ (x : ℕ), (x % 2 == 1) = true ↔ x % 2 = 1 := by
    intro x
    exact beq_iff_eq
  rw [h_dec_mod]

/-- Step 2 of the proof of exists_finite_family_balanced: prove the bounds on counting
true and false. -/
private lemma exists_finite_family_balanced_counts {m : ℕ} (R : Fin m → Set BitString) :
    ∀ i n, (selectChain (R i) (exists_finite_family_balanced_seq R) n).count true ≤
        (selectChain (R i) (exists_finite_family_balanced_seq R) n).count false ∧
      (selectChain (R i) (exists_finite_family_balanced_seq R) n).count false ≤
        (selectChain (R i) (exists_finite_family_balanced_seq R) n).count true + 2 ^ (m - 1) := by
  intro i n
  have h1 := exists_finite_family_balanced_identity R i n
  have h2 := exists_finite_family_balanced_bound (m := m) i
  have h3 : (Finset.univ.filter (fun (T : Finset (Fin m)) =>
    i ∈ T ∧ exists_finite_family_balanced_counts_cn R (exists_finite_family_balanced_seq R) n
    T % 2 = 1)).card ≤ (Finset.univ.filter (fun (T : Finset (Fin m)) => i ∈ T)).card := by
    apply Finset.card_le_card
    intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨hT.1, hT.2.1⟩
  constructor
  · omega
  · omega

private lemma count_true_add_count_false_eq_length (s : List Bool) : s.count true + s.count false =
    s.length := by
  induction s with
  | nil => simp
  | cons b tail ih => cases b <;> simp <;> omega

open Classical in
private lemma exists_finite_family_balanced_finiteOrFreq_selectChain_succ (R : Set BitString)
    (w : CantorSeq) (t : ℕ) :
    selectChain R w (t + 1)
      = selectChain R w t ++ (if cantorPrefix w t ∈ R then [w t] else []) := by
  unfold selectChain
  rw [cantorPrefix_succ, selectedBits_append_singleton]

private lemma exists_finite_family_balanced_finiteOrFreq_selectChain_zero (R : Set BitString)
    (w : CantorSeq) : selectChain R w 0 = [] := by
  simp [selectChain, selectedBits, selectedAux, cantorPrefix]

private lemma exists_finite_family_balanced_finiteOrFreq_ofPrefixSet_infinite
    {T : Set BitString}
    (hT : IsStreamPrefixSet T) (h_unbdd : ¬ ∃ M, ∀ x ∈ T, x.length ≤ M) :
    ∃ u : CantorSeq, BitStream.ofPrefixSet T hT = .infinite u ∧ ∀ x ∈ T, IsCantorPrefix x u := by
  classical
  refine ⟨fun i => (Classical.choose (exists_mem_length_gt h_unbdd i)).get
      ⟨i, (Classical.choose_spec (exists_mem_length_gt h_unbdd i)).2⟩, ?_,
    isCantorPrefix_of_mem hT h_unbdd⟩
  unfold BitStream.ofPrefixSet
  rw [dite_eq_right h_unbdd]

open Classical in
private lemma exists_finite_family_balanced_finiteOrFreq_chain_freq (R : Set BitString)
    (w : CantorSeq)
    (h : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ t : ℕ, L ≤ (selectChain R w t).length →
      |((selectChain R w t).count true : ℝ) - ((selectChain R w t).length : ℝ) / 2|
        ≤ ε * ((selectChain R w t).length : ℝ)) :
    FiniteOrFreq (1 / 2) (selectStream R w) := by
  classical
  have hT : IsStreamPrefixSet (chainPrefixSet (selectChain R w)) :=
    isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)
  have hsel : selectStream R w
      = BitStream.ofPrefixSet (chainPrefixSet (selectChain R w)) hT := rfl
  rw [hsel]
  by_cases hb : ∃ M, ∀ x ∈ chainPrefixSet (selectChain R w), x.length ≤ M
  · unfold BitStream.ofPrefixSet
    rw [dite_eq_left hb]
    trivial
  · obtain ⟨u, hu, hpre⟩ :=
      exists_finite_family_balanced_finiteOrFreq_ofPrefixSet_infinite hT hb
    rw [hu]
    change Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 (1 / 2))
    have hunb : ∀ M : ℕ, ∃ t, M < (selectChain R w t).length := by
      intro M
      obtain ⟨x, ⟨t, hxt⟩, hxM⟩ := exists_mem_length_gt hb M
      exact ⟨t, lt_of_lt_of_le hxM hxt.length_le⟩
    have hstep : ∀ t, (selectChain R w (t + 1)).length ≤ (selectChain R w t).length + 1 := by
      intro t
      rw [exists_finite_family_balanced_finiteOrFreq_selectChain_succ]
      split_ifs <;> simp
    have hattain : ∀ n : ℕ, ∃ t, (selectChain R w t).length = n := by
      intro n
      have hex : ∃ t, n ≤ (selectChain R w t).length := by
        obtain ⟨t, ht⟩ := hunb n
        exact ⟨t, ht.le⟩
      obtain ⟨t₀, ht₀, hmin⟩ : ∃ t₀, n ≤ (selectChain R w t₀).length ∧
          ∀ s < t₀, (selectChain R w s).length < n :=
        ⟨Nat.find hex, Nat.find_spec hex, fun s hs => lt_of_not_ge (Nat.find_min hex hs)⟩
      rcases t₀ with _ | t₁
      · refine ⟨0, ?_⟩
        rw [exists_finite_family_balanced_finiteOrFreq_selectChain_zero] at ht₀ ⊢
        simp at ht₀ ⊢
        omega
      · refine ⟨t₁ + 1, ?_⟩
        have h1 := hmin t₁ (Nat.lt_succ_self t₁)
        have h2 := hstep t₁
        omega
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L, hL⟩ := h (ε / 2) (by positivity)
    refine ⟨max L 1, fun n hn => ?_⟩
    obtain ⟨t, ht⟩ := hattain n
    have hcp : cantorPrefix u n = selectChain R w t := by
      have hmem : selectChain R w t ∈ chainPrefixSet (selectChain R w) := ⟨t, List.prefix_rfl⟩
      have := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 (hpre _ hmem)
      rw [ht] at this
      exact this
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hnL : L ≤ (selectChain R w t).length := by
      rw [ht]
      exact le_trans (le_max_left _ _) hn
    have hbound := hL t hnL
    rw [ht] at hbound
    have hfreq : (freqOne u n : ℝ) = ((selectChain R w t).count true : ℝ) / n := by
      unfold freqOne
      rw [hcp]
      push_cast
      rfl
    rw [Real.dist_eq, hfreq]
    have halg : ((selectChain R w t).count true : ℝ) / n - 1 / 2
        = (((selectChain R w t).count true : ℝ) - (n : ℝ) / 2) / n := by
      field_simp
    rw [halg, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
    have := mul_pos hε hnpos
    linarith

/-- Step 3 of the proof of exists_finite_family_balanced: prove the frequency limit. -/
private lemma exists_finite_family_balanced_finiteOrFreq {m : ℕ} (R : Fin m → Set BitString) :
    ∀ i, FiniteOrFreq (1 / 2) (selectStream (R i) (exists_finite_family_balanced_seq R)) := by
  intro i
  have hcounts := exists_finite_family_balanced_counts R i
  apply exists_finite_family_balanced_finiteOrFreq_chain_freq
  intro ε hε
  obtain ⟨L, hL⟩ := exists_nat_ge (((2 ^ (m - 1) : ℕ) : ℝ) / (2 * ε))
  use L
  intro t htL
  have h1 := (hcounts t).1
  have h2 := (hcounts t).2
  have h3 := count_true_add_count_false_eq_length
      (selectChain (R i) (exists_finite_family_balanced_seq R) t)
  have htR : (L : ℝ) ≤ ((selectChain (R i) (exists_finite_family_balanced_seq R) t).length : ℝ) :=
      by exact_mod_cast htL
  have h2ε : (0 : ℝ) ≤ 2 * ε := by positivity
  have hK_le : ((2 ^ (m - 1) : ℕ) : ℝ) ≤ 2 *
      (ε * ((selectChain (R i) (exists_finite_family_balanced_seq R) t).length : ℝ)) := by
    have hl1 : (((2 ^ (m - 1) : ℕ) : ℝ) / (2 * ε)) ≤ (L : ℝ) := hL
    have hl2 : (((2 ^ (m - 1) : ℕ) : ℝ) / (2 * ε)) ≤
        ((selectChain (R i) (exists_finite_family_balanced_seq R) t).length : ℝ) := le_trans hl1 htR
    rw [div_le_iff₀ (by positivity)] at hl2
    have : ((selectChain (R i) (exists_finite_family_balanced_seq R) t).length : ℝ) * (2 * ε) = 2 *
        (ε * ((selectChain (R i) (exists_finite_family_balanced_seq R) t).length : ℝ)) := by ring
    rwa [this] at hl2
  have h_epsN : 0 ≤ ε * ((selectChain (R i) (exists_finite_family_balanced_seq R) t).length : ℝ) :=
      by
    apply mul_nonneg (by linarith) (by positivity)
  have h1R : ((selectChain (R i) (exists_finite_family_balanced_seq R) t).count true : ℝ) ≤
      ((selectChain (R i) (exists_finite_family_balanced_seq R) t).count false : ℝ) := by
        exact_mod_cast h1
  have h2R : ((selectChain (R i) (exists_finite_family_balanced_seq R) t).count false : ℝ) ≤
      ((selectChain (R i) (exists_finite_family_balanced_seq R) t).count true : ℝ) +
      ((2 ^ (m - 1) : ℕ) : ℝ) := by exact_mod_cast h2
  have h3R : ((selectChain (R i) (exists_finite_family_balanced_seq R) t).count true : ℝ) +
      ((selectChain (R i) (exists_finite_family_balanced_seq R) t).count false : ℝ) =
      ((selectChain (R i) (exists_finite_family_balanced_seq R) t).length : ℝ) := by
        exact_mod_cast h3
  rw [abs_le]
  constructor <;> linarith
/-- **SUV p. 268**, `m` rules: there is `ω` such that all `S_{R_i}(ω)` are finite or balanced and,
in every prefix of each output, the zeros exceed the ones by at most `2^{m-1}` and are never fewer.
The bound is the one the book records for the mixture of `2^{m-1}` alternating subsequences. -/
theorem exists_finite_family_balanced {m : ℕ} (_hm : 0 < m) (R : Fin m → Set BitString) :
    ∃ w : CantorSeq, ∀ i, FiniteOrFreq (1 / 2) (selectStream (R i) w) ∧
      ∀ n, (selectChain (R i) w n).count true ≤ (selectChain (R i) w n).count false ∧
        (selectChain (R i) w n).count false ≤
          (selectChain (R i) w n).count true + 2 ^ (m - 1) := by
  use exists_finite_family_balanced_seq R
  intro i
  constructor
  · exact exists_finite_family_balanced_finiteOrFreq R i
  · exact exists_finite_family_balanced_counts R i

open Classical in
private noncomputable def exists_countable_family_balanced_construction_pat
    (R : ℕ → Set BitString) (p : BitString) (l : ℕ) : BitString :=
  (List.range l).map (fun j => decide (p ∈ R j))

open Classical in
private noncomputable def exists_countable_family_balanced_construction_stateAux
    (R : ℕ → Set BitString) (n : ℕ) : BitString × List BitString :=
  Nat.recOn n ([], []) fun k ⟨p, H⟩ =>
    let l_k := Nat.find (show ∃ l, (H.count (exists_countable_family_balanced_construction_pat
        R p l)) < 2^(2^l) by
      use H.length
      have h1 : H.count (exists_countable_family_balanced_construction_pat R p H.length) ≤
          H.length := List.count_le_length
          (a := exists_countable_family_balanced_construction_pat R p H.length) (l := H)
      have h2 : H.length < 2^H.length := Nat.lt_two_pow_self
      have h3 : 2^H.length ≤ 2^(2^H.length) := Nat.pow_le_pow_right (by omega)
          (Nat.lt_two_pow_self).le
      omega
    )
    let a_k := exists_countable_family_balanced_construction_pat R p l_k
    let w_k := decide (H.count a_k % 2 = 1)
    (p ++ [w_k], H ++ [a_k])

open Classical in
private noncomputable def exists_countable_family_balanced_construction_seq
    (R : ℕ → Set BitString) : CantorSeq :=
  fun n => (exists_countable_family_balanced_construction_stateAux R (n+1)).1[n]!

open Classical in
private noncomputable def exists_countable_family_balanced_construction_act
    (R : ℕ → Set BitString) (n : ℕ) : BitString :=
  (exists_countable_family_balanced_construction_stateAux R (n+1)).2[n]!

/-- One step of the construction appends a pattern `a` to the history and, to the prefix, the
parity of the number of earlier occurrences of `a`. -/
private lemma exists_countable_family_balanced_state_succ
    (R : ℕ → Set BitString) (n : ℕ) :
    ∃ a : BitString,
      (exists_countable_family_balanced_construction_stateAux R (n + 1)).1 =
          (exists_countable_family_balanced_construction_stateAux R n).1 ++
            [decide
              ((exists_countable_family_balanced_construction_stateAux R n).2.count a % 2 = 1)] ∧
        (exists_countable_family_balanced_construction_stateAux R (n + 1)).2 =
          (exists_countable_family_balanced_construction_stateAux R n).2 ++ [a] :=
  ⟨_, rfl, rfl⟩

private lemma exists_countable_family_balanced_state_length
    (R : ℕ → Set BitString) (n : ℕ) :
    (exists_countable_family_balanced_construction_stateAux R n).1.length = n ∧
        (exists_countable_family_balanced_construction_stateAux R n).2.length = n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    obtain ⟨a, h1, h2⟩ := exists_countable_family_balanced_state_succ R n
    rw [h1, h2, List.length_append, List.length_append, List.length_singleton,
        List.length_singleton, ih1, ih2]
    exact ⟨rfl, rfl⟩

private lemma exists_countable_family_balanced_history_lemma {α : Type}
    [Inhabited α] (l : List α) (x : α) (n : ℕ) (h : l.length = n) :
    (l ++ [x])[n]! = x := by
  subst h
  induction l with
  | nil => rfl
  | cons a l ih => exact ih

private lemma exists_countable_family_balanced_history
    (R : ℕ → Set BitString) (n : ℕ) :
    (exists_countable_family_balanced_construction_stateAux R n).2 = (List.range n).map
        (exists_countable_family_balanced_construction_act R) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton]
    change (exists_countable_family_balanced_construction_stateAux R n).2 ++ _ = _
    rw [ih]
    congr 1
    dsimp [exists_countable_family_balanced_construction_act]
    change [_] = [((exists_countable_family_balanced_construction_stateAux R n).2 ++
        [ _ ])[n]!]
    congr 1
    have h_len : (exists_countable_family_balanced_construction_stateAux R n).2.length = n :=
        (exists_countable_family_balanced_state_length R n).2
    apply Eq.symm
    apply exists_countable_family_balanced_history_lemma _ _ _ h_len

private lemma exists_countable_family_balanced_prefix
    (R : ℕ → Set BitString) (n : ℕ) :
    cantorPrefix (exists_countable_family_balanced_construction_seq R) n =
        (exists_countable_family_balanced_construction_stateAux R n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cantorPrefix_succ]
    rw [ih]
    have hlen := (exists_countable_family_balanced_state_length R n).1
    obtain ⟨a, h_step, -⟩ := exists_countable_family_balanced_state_succ R n
    have hseq : exists_countable_family_balanced_construction_seq R n =
        (exists_countable_family_balanced_construction_stateAux R (n + 1)).1[n]! := rfl
    rw [hseq, h_step, exists_countable_family_balanced_history_lemma _ _ _ hlen]

private lemma exists_countable_family_balanced_count_eq
    (R : ℕ → Set BitString) (n : ℕ) :
    (List.range n).countP (fun m => exists_countable_family_balanced_construction_act R m =
        exists_countable_family_balanced_construction_act R n) =
      ((exists_countable_family_balanced_construction_stateAux R n).2).count
        (exists_countable_family_balanced_construction_act R n) := by
  rw [exists_countable_family_balanced_history]
  rw [List.count_eq_countP, List.countP_map]
  congr 1
  ext m
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff, @beq_iff_eq _ (_), decide_eq_true_iff]

private lemma exists_countable_family_balanced_w
    (R : ℕ → Set BitString) (n : ℕ) :
    exists_countable_family_balanced_construction_seq R n =
        decide (((exists_countable_family_balanced_construction_stateAux R n).2).count
        (exists_countable_family_balanced_construction_act R n) % 2 = 1) := by
  have h1 : exists_countable_family_balanced_construction_seq R n =
      (exists_countable_family_balanced_construction_stateAux R (n+1)).1[n]! := rfl
  have h2 : exists_countable_family_balanced_construction_act R n =
      (exists_countable_family_balanced_construction_stateAux R (n+1)).2[n]! := rfl
  have h_rec : (exists_countable_family_balanced_construction_stateAux R (n+1)) =
    let p := (exists_countable_family_balanced_construction_stateAux R n).1
    let H := (exists_countable_family_balanced_construction_stateAux R n).2
    let l_k := Nat.find (show ∃ l, (H.count (exists_countable_family_balanced_construction_pat
        R p l)) < 2^(2^l) by
      use H.length
      have h1 : H.count (exists_countable_family_balanced_construction_pat R p H.length) ≤
          H.length := List.count_le_length
          (a := exists_countable_family_balanced_construction_pat R p H.length) (l := H)
      have h2 : H.length < 2^H.length := Nat.lt_two_pow_self
      have h3 : 2^H.length ≤ 2^(2^H.length) := Nat.pow_le_pow_right (by omega)
          (Nat.lt_two_pow_self).le
      omega
    )
    let a_k := exists_countable_family_balanced_construction_pat R p l_k
    let w_k := decide (H.count a_k % 2 = 1)
    (p ++ [w_k], H ++ [a_k]) := rfl
  
  have h_get : ∀ (l : List Bool) (x : Bool), (l ++ [x])[l.length]! = x := fun l x => by simp
  have h_get_list : ∀ (l : List (List Bool)) (x : List Bool), (l ++ [x])[l.length]! = x :=
      fun l x => by simp
  have h_len : (exists_countable_family_balanced_construction_stateAux R n).1.length = n :=
      (exists_countable_family_balanced_state_length R n).1
  have h_len2 : (exists_countable_family_balanced_construction_stateAux R n).2.length = n :=
      (exists_countable_family_balanced_state_length R n).2
  
  rw [h1, h_rec]
  have h_len_subst : (exists_countable_family_balanced_construction_stateAux R n).1.length =
      n := h_len
  
  let p := (exists_countable_family_balanced_construction_stateAux R n).1
  let H := (exists_countable_family_balanced_construction_stateAux R n).2
  let l_k := Nat.find (show ∃ l, (H.count (exists_countable_family_balanced_construction_pat R
      p l)) < 2^(2^l) by
      use H.length
      have h1 : H.count (exists_countable_family_balanced_construction_pat R p H.length) ≤
          H.length := List.count_le_length
          (a := exists_countable_family_balanced_construction_pat R p H.length) (l := H)
      have h2 : H.length < 2^H.length := Nat.lt_two_pow_self
      have h3 : 2^H.length ≤ 2^(2^H.length) := Nat.pow_le_pow_right (by omega)
          (Nat.lt_two_pow_self).le
      omega
    )
  let a_k := exists_countable_family_balanced_construction_pat R p l_k
  let w_k := decide (H.count a_k % 2 = 1)
  
  have h3 : (p ++ [w_k])[n]! = w_k := by
    have h_get2 := h_get p w_k
    rw [h_len_subst] at h_get2
    exact h_get2
  
  dsimp only at h3 ⊢
  rw [h3]
  
  have h4 : exists_countable_family_balanced_construction_act R n = a_k := by
    rw [h2, h_rec]
    dsimp only
    have h_get3 := h_get_list H a_k
    have h_len_subst2 : H.length = n := h_len2
    rw [h_len_subst2] at h_get3
    exact h_get3
    
  rw [h4]

private lemma exists_countable_family_balanced_act_get
    (R : ℕ → Set BitString) (n : ℕ) (j : ℕ)
        (hj : j < (exists_countable_family_balanced_construction_act R n).length) :
    (exists_countable_family_balanced_construction_act R n).get ⟨j, hj⟩ = true ↔ cantorPrefix
        (exists_countable_family_balanced_construction_seq R) n ∈ R j := by
  classical
  have p_n_eq : cantorPrefix (exists_countable_family_balanced_construction_seq R) n =
      (exists_countable_family_balanced_construction_stateAux R n).1 :=
      exists_countable_family_balanced_prefix R n
  rw [p_n_eq]
  let state_n := exists_countable_family_balanced_construction_stateAux R n
  let p_n := state_n.1
  let H_n := state_n.2
  have h_ex_l : ∃ l, H_n.count (exists_countable_family_balanced_construction_pat R p_n l) <
      2 ^ 2 ^ l := by
    use H_n.length
    have h1 : H_n.count (exists_countable_family_balanced_construction_pat R p_n H_n.length) ≤
        H_n.length := List.count_le_length
        (a := exists_countable_family_balanced_construction_pat R p_n H_n.length) (l := H_n)
    have h2 : H_n.length < 2^H_n.length := Nat.lt_two_pow_self
    have h3 : 2^H_n.length ≤ 2^(2^H_n.length) := Nat.pow_le_pow_right (by omega)
        (Nat.le_of_lt (Nat.lt_two_pow_self))
    omega
  have get_n : exists_countable_family_balanced_construction_act R n =
      exists_countable_family_balanced_construction_pat R p_n (Nat.find h_ex_l) := by
    have H_n_len : H_n.length = n :=
        (exists_countable_family_balanced_state_length R n).2
    dsimp [exists_countable_family_balanced_construction_act]
    have H_n_succ_eq : (exists_countable_family_balanced_construction_stateAux R (n+1)).2 =
        H_n ++ [exists_countable_family_balanced_construction_pat R p_n (Nat.find h_ex_l)] :=
        rfl
    rw [H_n_succ_eq]
    exact exists_countable_family_balanced_history_lemma _ _ _ H_n_len
  have hj_pat : j < (exists_countable_family_balanced_construction_pat R p_n
      (Nat.find h_ex_l)).length := by
    rw [← get_n]
    exact hj
  have h_act_get :
      (exists_countable_family_balanced_construction_act R n).get ⟨j, hj⟩ =
        (exists_countable_family_balanced_construction_pat R p_n
          (Nat.find h_ex_l)).get ⟨j, hj_pat⟩ := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact getElem_congr get_n (rfl : j = j) hj
  have hlookup :
      (exists_countable_family_balanced_construction_pat R p_n
        (Nat.find h_ex_l)).get ⟨j, hj_pat⟩ = decide (p_n ∈ R j) := by
    simp [exists_countable_family_balanced_construction_pat]
  rw [h_act_get, hlookup]
  exact decide_eq_true_iff


private lemma exists_countable_family_balanced_bound
    (R : ℕ → Set BitString) (n : ℕ) :
    ((exists_countable_family_balanced_construction_stateAux R n).2).count
        (exists_countable_family_balanced_construction_act R n) <
        2 ^ (2 ^ (exists_countable_family_balanced_construction_act R n).length) := by
  have hl := (exists_countable_family_balanced_state_length R n).2
  set state_n := exists_countable_family_balanced_construction_stateAux R n
  set p_n := state_n.1
  set H_n := state_n.2
  have H_n_len : H_n.length = n := hl
  
  have h_ex_l : ∃ l, H_n.count (exists_countable_family_balanced_construction_pat R p_n l) <
      2 ^ 2 ^ l := by
    use H_n.length
    have h1 : H_n.count (exists_countable_family_balanced_construction_pat R p_n H_n.length) ≤
        H_n.length := List.count_le_length
        (a := exists_countable_family_balanced_construction_pat R p_n H_n.length) (l := H_n)
    have h2 : H_n.length < 2^H_n.length := Nat.lt_two_pow_self
    have h3 : 2^H_n.length ≤ 2^(2^H_n.length) := Nat.pow_le_pow_right (by omega)
        (Nat.le_of_lt (Nat.lt_two_pow_self))
    omega
  have H_n_succ_eq : (exists_countable_family_balanced_construction_stateAux R (n+1)).2 =
      H_n ++ [exists_countable_family_balanced_construction_pat R p_n (Nat.find h_ex_l)] :=
      rfl
  have get_n : exists_countable_family_balanced_construction_act R n =
      exists_countable_family_balanced_construction_pat R p_n (Nat.find h_ex_l) := by
    dsimp [exists_countable_family_balanced_construction_act]
    rw [H_n_succ_eq]
    exact exists_countable_family_balanced_history_lemma _ _ _ H_n_len
  have h_len : (exists_countable_family_balanced_construction_pat R p_n
      (Nat.find h_ex_l)).length = Nat.find h_ex_l := by
    dsimp [exists_countable_family_balanced_construction_pat]
    rw [List.length_map, List.length_range]
  
  rw [get_n, h_len]
  exact Nat.find_spec h_ex_l

/-- Step 1 of the proof of
`exists_countable_family_balanced_lower`: extract the actual Nat.find
witness. -/
private theorem exists_countable_family_balanced_unfold
    (R : ℕ → Set BitString) (n : ℕ) :
    ∃ h : ∃ l : ℕ,
        ((exists_countable_family_balanced_construction_stateAux R n).2).count
          (exists_countable_family_balanced_construction_pat R
            (exists_countable_family_balanced_construction_stateAux R n).1 l) < 2 ^ (2 ^ l),
      exists_countable_family_balanced_construction_act R n =
        exists_countable_family_balanced_construction_pat R
          (exists_countable_family_balanced_construction_stateAux R n).1 (Nat.find h) ∧
      (exists_countable_family_balanced_construction_act R n).length = Nat.find h := by
  have hl := (exists_countable_family_balanced_state_length R n).2
  set state_n := exists_countable_family_balanced_construction_stateAux R n
  set p_n := state_n.1
  set H_n := state_n.2
  have H_n_len : H_n.length = n := hl
  have h_ex_l : ∃ l, H_n.count (exists_countable_family_balanced_construction_pat R p_n l) <
      2 ^ 2 ^ l := by
    use H_n.length
    have h1 : H_n.count (exists_countable_family_balanced_construction_pat R p_n H_n.length) ≤
        H_n.length := List.count_le_length
        (a := exists_countable_family_balanced_construction_pat R p_n H_n.length) (l := H_n)
    have h2 : H_n.length < 2^H_n.length := Nat.lt_two_pow_self
    have h3 : 2^H_n.length ≤ 2^(2^H_n.length) := Nat.pow_le_pow_right (by omega)
        (Nat.le_of_lt (Nat.lt_two_pow_self))
    omega
  use h_ex_l
  have H_n_succ_eq : (exists_countable_family_balanced_construction_stateAux R (n+1)).2 =
      H_n ++ [exists_countable_family_balanced_construction_pat R p_n (Nat.find h_ex_l)] :=
      rfl
  have get_n : exists_countable_family_balanced_construction_act R n =
      exists_countable_family_balanced_construction_pat R p_n (Nat.find h_ex_l) := by
    dsimp [exists_countable_family_balanced_construction_act]
    rw [H_n_succ_eq]
    exact exists_countable_family_balanced_history_lemma _ _ _ H_n_len
  have h_len : (exists_countable_family_balanced_construction_pat R p_n
      (Nat.find h_ex_l)).length = Nat.find h_ex_l := by
    dsimp [exists_countable_family_balanced_construction_pat]
    rw [List.length_map, List.length_range]
  exact ⟨get_n, by rw [get_n, h_len]⟩

private theorem exists_countable_family_balanced_dropLast_map
    {α β : Type} (f : α → β) (xs : List α) : (xs.map f).dropLast = xs.dropLast.map f := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs => 
      have h1 : (a :: b :: bs).map f = f a :: (b :: bs).map f := rfl
      rw [h1]
      have h2 : (f a :: (b :: bs).map f).dropLast = f a :: ((b :: bs).map f).dropLast := by
        exact List.dropLast_cons_of_ne_nil (by simp)
      rw [h2]
      rw [ih]
      have h3 : (a :: b :: bs).dropLast = a :: (b :: bs).dropLast := by
        exact List.dropLast_cons_of_ne_nil (by simp)
      rw [h3]
      rfl

/-- Step 2 of the proof of
`exists_countable_family_balanced_lower`: prove the pattern-prefix identity
for positive length. -/
private theorem exists_countable_family_balanced_dropLast
    (R : ℕ → Set BitString) (p : BitString) (l : ℕ) (hl : 0 < l) :
    (exists_countable_family_balanced_construction_pat R p l).dropLast =
      exists_countable_family_balanced_construction_pat R p (l - 1) := by
  dsimp [exists_countable_family_balanced_construction_pat]
  rw [exists_countable_family_balanced_dropLast_map]
  have h_range : (List.range l).dropLast = List.range (l - 1) := by
    cases l with
    | zero => contradiction
    | succ l =>
      simp [List.range_succ]
  rw [h_range]

/-- Step 3 of the proof of
`exists_countable_family_balanced_lower`: state the Nat.find_min
consequence. -/
private theorem exists_countable_family_balanced_find_failure
    (R : ℕ → Set BitString) (p : BitString) (H : List BitString)
    (h : ∃ l : ℕ, H.count (exists_countable_family_balanced_construction_pat R p l) <
        2 ^ (2 ^ l))
    (hl : 0 < Nat.find h) :
    2 ^ (2 ^ (Nat.find h - 1)) ≤
      H.count (exists_countable_family_balanced_construction_pat R p (Nat.find h - 1)) := by
  have h1 := Nat.find_min h (show Nat.find h - 1 < Nat.find h by omega)
  omega

private lemma exists_countable_family_balanced_lower
    (R : ℕ → Set BitString) (n : ℕ) (h_not_empty :
        exists_countable_family_balanced_construction_act R n ≠ []) :
    2 ^ (2 ^ ((exists_countable_family_balanced_construction_act R n).length - 1)) ≤
        ((exists_countable_family_balanced_construction_stateAux R n).2).count
        ((exists_countable_family_balanced_construction_act R n).dropLast) := by
  obtain ⟨h_bound, h_act_eq, h_len⟩ :=
      exists_countable_family_balanced_unfold R n
  have h_len_pos : 0 < Nat.find h_bound := by
    cases h_a : exists_countable_family_balanced_construction_act R n
    · contradiction
    · rw [← h_len]
      rw [h_a]
      exact Nat.zero_lt_succ _
  have h_subst1 : 2 ^ 2 ^ ((exists_countable_family_balanced_construction_act R n).length - 1)
      = 2 ^ 2 ^ (Nat.find h_bound - 1) := by rw [h_len]
  rw [h_subst1]
  have h_dropLast : (exists_countable_family_balanced_construction_act R n).dropLast =
      exists_countable_family_balanced_construction_pat R
        (exists_countable_family_balanced_construction_stateAux R n).1 (Nat.find h_bound - 1) := by
    rw [h_act_eq]
    exact exists_countable_family_balanced_dropLast R _ _
        h_len_pos
  have h_subst2 : ((exists_countable_family_balanced_construction_stateAux R n).2).count
        (exists_countable_family_balanced_construction_act R n).dropLast =
      ((exists_countable_family_balanced_construction_stateAux R n).2).count
        (exists_countable_family_balanced_construction_pat R
          (exists_countable_family_balanced_construction_stateAux R n).1
          (Nat.find h_bound - 1)) := by
    change ((exists_countable_family_balanced_construction_stateAux R n).2).count _ = _
    rw [h_dropLast]
  rw [h_subst2]
  exact exists_countable_family_balanced_find_failure R
      (exists_countable_family_balanced_construction_stateAux R n).1
      (exists_countable_family_balanced_construction_stateAux R n).2 h_bound h_len_pos

private lemma exists_countable_family_balanced_lower_countP
    (R : ℕ → Set BitString) (n : ℕ) :
    ((exists_countable_family_balanced_construction_stateAux R n).2).count
        ((exists_countable_family_balanced_construction_act R n).dropLast) = (List.range n).countP
        (fun m => exists_countable_family_balanced_construction_act R m =
                    (exists_countable_family_balanced_construction_act R n).dropLast) := by
  rw [exists_countable_family_balanced_history]
  rw [List.count_eq_countP, List.countP_map]
  congr 1
  ext m
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff, @beq_iff_eq _ (_), decide_eq_true_iff]

/-- Step 1 of the proof of `exists_countable_family_balanced`: construction of sequence
with specific properties. -/
private lemma exists_countable_family_balanced_construction (R : ℕ → Set BitString) :
    ∃ (w : CantorSeq) (a : ℕ → BitString),
      (∀ n, w n = decide ((List.range n).countP (fun m => a m = a n) % 2 = 1)) ∧
      (∀ n j (hj : j < (a n).length), (a n).get ⟨j, hj⟩ = true ↔ cantorPrefix w n ∈ R j) ∧
      (∀ n, (List.range n).countP (fun m => a m = a n) < 2 ^ (2 ^ (a n).length)) ∧
      (∀ n, (a n) ≠ [] → 2 ^ (2 ^ ((a n).length - 1)) ≤ (List.range n).countP
          (fun m => a m = (a n).dropLast)) := by
  use exists_countable_family_balanced_construction_seq R
  use exists_countable_family_balanced_construction_act R
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rw [exists_countable_family_balanced_count_eq R n]
    exact exists_countable_family_balanced_w R n
  · intro n j hj
    exact exists_countable_family_balanced_act_get R n j hj
  · intro n
    rw [exists_countable_family_balanced_count_eq R n]
    exact exists_countable_family_balanced_bound R n
  · intro n h_not_empty
    rw [← exists_countable_family_balanced_lower_countP R n]
    exact exists_countable_family_balanced_lower R n h_not_empty

/-- Step 1 of the proof of `exists_countable_family_balanced_analysis`: the
activations of a fixed vertex alternate, so its number of ones is half its activation count,
rounded down. -/
private lemma exists_countable_family_balanced_ones_fiber
    (v : ℕ → List Bool) (bit : ℕ → Bool)
    (hpar : ∀ j, bit j = decide ((((Finset.range j).filter fun j' => v j' = v j).card) % 2 = 1))
    (x : List Bool) (t : ℕ) :
    ((Finset.range t).filter fun j => v j = x ∧ bit j = true).card
      = ((Finset.range t).filter fun j => v j = x).card / 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    by_cases hx : v t = x
    · subst hx
      have hb := hpar t
      have hnot : t ∉ (Finset.range t).filter fun j => v j = v t := by simp
      have hnot2 : t ∉ (Finset.range t).filter fun j => v j = v t ∧ bit j = true := by simp
      by_cases hbt : bit t = true
      · rw [ite_eq_left ⟨rfl, hbt⟩, ite_eq_left rfl, Finset.card_insert_of_notMem hnot2,
          Finset.card_insert_of_notMem hnot]
        rw [hbt] at hb
        have hmod : (((Finset.range t).filter fun j' => v j' = v t).card) % 2 = 1 := by
          simpa using hb.symm
        omega
      · rw [ite_eq_right (fun h => hbt h.2), ite_eq_left rfl, Finset.card_insert_of_notMem hnot]
        have hbf : bit t = false := by simpa using hbt
        rw [hbf] at hb
        have hmod : ¬ (((Finset.range t).filter fun j' => v j' = v t).card) % 2 = 1 := by
          simpa using hb.symm
        omega
    · rw [ite_eq_right hx, ite_eq_right (fun h => hx h.1)]
      exact ih

/-- Step 2 of the proof of `exists_countable_family_balanced_analysis`: the
capacity invariant bounds the total number of activations of any fixed vertex. -/
private lemma exists_countable_family_balanced_fiber_le
    (v : ℕ → List Bool)
    (hcap : ∀ j, ((Finset.range j).filter fun j' => v j' = v j).card < 2 ^ (2 ^ (v j).length))
    (x : List Bool) (t : ℕ) :
    ((Finset.range t).filter fun j => v j = x).card ≤ 2 ^ (2 ^ x.length) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hx : v t = x
    · subst hx
      have := hcap t
      rw [ite_eq_left rfl, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [ite_eq_right hx]
      exact ih

/-- Step 3 of the proof of `exists_countable_family_balanced_analysis`: there
are fewer than `2 ^ (n + 1)` binary strings of length at most `n`. -/
private lemma exists_countable_family_balanced_lists (n : ℕ) :
    ∃ W : Finset (List Bool), W.card + 1 ≤ 2 ^ (n + 1) ∧ (∀ x : List Bool, x.length ≤ n → x ∈ W) ∧
      ∀ x ∈ W, x.length ≤ n := by
  induction n with
  | zero =>
    refine ⟨{[]}, by simp, ?_, ?_⟩
    · intro x hx
      have : x = [] := List.length_eq_zero_iff.mp (by omega)
      simp [this]
    · intro x hx
      simp at hx
      simp [hx]
  | succ n ih =>
    obtain ⟨W, hW, hmem, hlen⟩ := ih
    refine ⟨insert [] ((W.image (List.cons true)) ∪ (W.image (List.cons false))), ?_, ?_, ?_⟩
    · have h1 := Finset.card_insert_le ([] : List Bool)
        ((W.image (List.cons true)) ∪ (W.image (List.cons false)))
      have h2 := Finset.card_union_le (W.image (List.cons true)) (W.image (List.cons false))
      have h3 := Finset.card_image_le (s := W) (f := List.cons true)
      have h4 := Finset.card_image_le (s := W) (f := List.cons false)
      have h5 : (2 : ℕ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      rw [h5]
      omega
    · intro x hx
      cases x with
      | nil => simp
      | cons b y =>
        have hy : y.length ≤ n := by simpa using hx
        have hyW := hmem y hy
        cases b
        · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inr ⟨y, hyW, rfl⟩)
        · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inl ⟨y, hyW, rfl⟩)
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · simp
      · have := hlen y hy
        simp only [List.length_cons]
        omega
      · have := hlen y hy
        simp only [List.length_cons]
        omega

/-- Step 4 of the proof of `exists_countable_family_balanced_analysis`: the
total number of activations of vertices of length at most `i` is bounded independently of time.
-/
private lemma exists_countable_family_balanced_type1
    (v : ℕ → List Bool)
    (hcap : ∀ j, ((Finset.range j).filter fun j' => v j' = v j).card < 2 ^ (2 ^ (v j).length))
    (i t : ℕ) :
    ((Finset.range t).filter fun j => (v j).length ≤ i).card ≤ 2 ^ (i + 1) * 2 ^ (2 ^ i) := by
  obtain ⟨W, hW, hmem, hlen⟩ := exists_countable_family_balanced_lists i
  have hmaps : ∀ j ∈ (Finset.range t).filter fun j => (v j).length ≤ i, v j ∈ W := by
    intro j hj
    exact hmem _ (Finset.mem_filter.mp hj).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ x ∈ W, (((Finset.range t).filter fun j => (v j).length ≤ i).filter fun j => v j = x).card
      ≤ ∑ _x ∈ W, 2 ^ (2 ^ i) := by
        apply Finset.sum_le_sum
        intro x hx
        have hsub : (((Finset.range t).filter fun j => (v j).length ≤ i).filter fun j => v j = x)
            ⊆ (Finset.range t).filter fun j => v j = x := by
          intro j hj
          simp only [Finset.mem_filter] at hj ⊢
          exact ⟨hj.1.1, hj.2⟩
        calc _ ≤ ((Finset.range t).filter fun j => v j = x).card := Finset.card_le_card hsub
          _ ≤ 2 ^ (2 ^ x.length) :=
            exists_countable_family_balanced_fiber_le v hcap x t
          _ ≤ 2 ^ (2 ^ i) := Nat.pow_le_pow_right (by norm_num)
              (Nat.pow_le_pow_right (by norm_num) (hlen x hx))
    _ = W.card * 2 ^ (2 ^ i) := by simp
    _ ≤ 2 ^ (i + 1) * 2 ^ (2 ^ i) := Nat.mul_le_mul_right _ (by omega)

/-- Step 5 of the proof of `exists_countable_family_balanced_analysis`: the
double exponential capacity eventually dominates the number of vertices at a given height. -/
private lemma exists_countable_family_balanced_numeric (ε : ℝ) (hε : 0 < ε)
    (C : ℕ) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → (C : ℝ) + 2 ^ (m + 2) ≤ 2 * ε * 2 ^ (2 ^ m) := by
  have hsmall : ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
      (C : ℝ) + 2 ^ (m + 2) ≤ 2 * ε * 4 ^ m := by
    refine ⟨⌈((C : ℝ) + 4) / (2 * ε)⌉₊, fun m hm => ?_⟩
    have h1 : ((C : ℝ) + 4) / (2 * ε) ≤ (m : ℝ) := by
      calc ((C : ℝ) + 4) / (2 * ε) ≤ (⌈((C : ℝ) + 4) / (2 * ε)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (m : ℝ) := by exact_mod_cast hm
    have h2 : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
    have h3 : (C : ℝ) + 4 ≤ 2 * ε * 2 ^ m := by
      have := le_trans h1 h2
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have ha : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    have e1 : (2 : ℝ) ^ (m + 2) = 4 * 2 ^ m := by ring
    have e2 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 ^ m),
      mul_nonneg (sub_nonneg.2 ha) hC]
  obtain ⟨K, hK⟩ := hsmall
  refine ⟨K, fun m hm => (hK m hm).trans ?_⟩
  have hpow : (4 : ℝ) ^ m ≤ 2 ^ (2 ^ m) := by
    calc (4 : ℝ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
         _ ≤ 2 ^ (2 ^ m) := pow_le_pow_right₀ (by norm_num)
           (Nat.mul_le_pow (by decide : 2 ≠ 1) m)
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Step 6 of the proof of `exists_countable_family_balanced_analysis`: a
selected vertex of length at least `i + 2` has a fully used, selected parent, forcing many
selected terms. -/
private lemma exists_countable_family_balanced_parent
    (v : ℕ → List Bool) (sel : ℕ → Bool) (i : ℕ)
    (htired : ∀ j, v j ≠ [] →
      2 ^ (2 ^ ((v j).length - 1)) ≤
        ((Finset.range j).filter fun j' => v j' = (v j).dropLast).card)
    (hsel : ∀ j, i < (v j).length → (sel j = true ↔ (v j)[i]? = some true))
    (t j0 : ℕ) (hj0 : j0 < t) (hlen : i + 2 ≤ (v j0).length) (hx : (v j0)[i]? = some true) :
    2 ^ (2 ^ ((v j0).length - 1)) ≤ ((Finset.range t).filter fun j => sel j = true).card := by
  have hne : v j0 ≠ [] := by
    intro heq
    simp [heq] at hlen
  have h1 := htired j0 hne
  refine le_trans h1 (Finset.card_le_card ?_)
  intro j' hj'
  simp only [Finset.mem_filter, Finset.mem_range] at hj' ⊢
  obtain ⟨hj'0, hv⟩ := hj'
  have hlen' : (v j').length = (v j0).length - 1 := by
    rw [hv]
    simp only [List.length_dropLast]
  have hil : i < (v j').length := by omega
  refine ⟨by omega, (hsel j' hil).2 ?_⟩
  rw [hv, List.dropLast_eq_take, List.getElem?_take]
  rw [ite_eq_left (by omega)]
  exact hx

/-- Step 7 of the proof of `exists_countable_family_balanced_analysis`: the long
selected vertices contribute alternating subsequences, with imbalance at most one per vertex. -/
private lemma exists_countable_family_balanced_type2
    (v : ℕ → List Bool) (bit sel : ℕ → Bool) (i : ℕ)
    (hpar : ∀ j, bit j = decide ((((Finset.range j).filter fun j' => v j' = v j).card) % 2 = 1))
    (hsel : ∀ j, i < (v j).length → (sel j = true ↔ (v j)[i]? = some true))
    (t : ℕ) (Y : Finset (List Bool))
    (hY : Y = ((Finset.range t).image v).filter fun x => i < x.length ∧ x[i]? = some true) :
    2 * ((Finset.range t).filter fun j => (sel j = true ∧ bit j = true) ∧ i < (v j).length).card
      ≤ ((Finset.range t).filter fun j => sel j = true ∧ i < (v j).length).card ∧
    ((Finset.range t).filter fun j => sel j = true ∧ i < (v j).length).card
      ≤ 2 * ((Finset.range t).filter fun j =>
          (sel j = true ∧ bit j = true) ∧ i < (v j).length).card + Y.card := by
  have hmemY : ∀ j, j < t → (v j ∈ Y ↔ i < (v j).length ∧ (v j)[i]? = some true) := by
    intro j hj
    rw [hY, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨⟨j, Finset.mem_range.mpr hj, rfl⟩, h⟩
  have hS2 : ((Finset.range t).filter fun j => sel j = true ∧ i < (v j).length)
      = (Finset.range t).filter fun j => v j ∈ Y := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hs, hl⟩
      exact ⟨hj, (hmemY j hj).2 ⟨hl, (hsel j hl).1 hs⟩⟩
    · rintro ⟨hj, hy⟩
      obtain ⟨hl, hx⟩ := (hmemY j hj).1 hy
      exact ⟨hj, (hsel j hl).2 hx, hl⟩
  have hO2 : ((Finset.range t).filter fun j => (sel j = true ∧ bit j = true) ∧ i < (v j).length)
      = (Finset.range t).filter fun j => v j ∈ Y ∧ bit j = true := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, ⟨hs, hb⟩, hl⟩
      exact ⟨hj, (hmemY j hj).2 ⟨hl, (hsel j hl).1 hs⟩, hb⟩
    · rintro ⟨hj, hy, hb⟩
      obtain ⟨hl, hx⟩ := (hmemY j hj).1 hy
      exact ⟨hj, ⟨(hsel j hl).2 hx, hb⟩, hl⟩
  rw [hS2, hO2]
  have hmaps1 : ∀ j ∈ (Finset.range t).filter (fun j => v j ∈ Y), v j ∈ Y :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hmaps2 : ∀ j ∈ (Finset.range t).filter (fun j => v j ∈ Y ∧ bit j = true), v j ∈ Y :=
    fun j hj => (Finset.mem_filter.mp hj).2.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps1, Finset.card_eq_sum_card_fiberwise hmaps2]
  have e1 : ∀ x ∈ Y, (((Finset.range t).filter fun j => v j ∈ Y).filter fun j => v j = x).card
      = ((Finset.range t).filter fun j => v j = x).card := by
    intro x hx
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hj, _⟩, h⟩
      exact ⟨hj, h⟩
    · rintro ⟨hj, h⟩
      exact ⟨⟨hj, by rw [h]; exact hx⟩, h⟩
  have e2 : ∀ x ∈ Y,
      (((Finset.range t).filter fun j => v j ∈ Y ∧ bit j = true).filter fun j => v j = x).card
      = ((Finset.range t).filter fun j => v j = x).card / 2 := by
    intro x hx
    rw [← exists_countable_family_balanced_ones_fiber v bit hpar x t]
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hj, _, hb⟩, h⟩
      exact ⟨hj, h, hb⟩
    · rintro ⟨hj, h, hb⟩
      exact ⟨⟨hj, by rw [h]; exact hx, hb⟩, h⟩
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    omega
  · calc ∑ x ∈ Y, ((Finset.range t).filter fun j => v j = x).card
        ≤ ∑ x ∈ Y, (2 * (((Finset.range t).filter fun j => v j = x).card / 2) + 1) := by
          apply Finset.sum_le_sum
          intro x _
          omega
      _ = 2 * (∑ x ∈ Y, ((Finset.range t).filter fun j => v j = x).card / 2) + Y.card := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp

/-- Step 8 of the proof of `exists_countable_family_balanced_analysis`:
splitting into short and long vertices bounds the total imbalance by a fixed constant plus the
number of long selected vertices. -/
private lemma exists_countable_family_balanced_nat_bounds
    (v : ℕ → List Bool) (bit sel : ℕ → Bool) (i : ℕ)
    (hpar : ∀ j, bit j = decide ((((Finset.range j).filter fun j' => v j' = v j).card) % 2 = 1))
    (hcap : ∀ j, ((Finset.range j).filter fun j' => v j' = v j).card < 2 ^ (2 ^ (v j).length))
    (hsel : ∀ j, i < (v j).length → (sel j = true ↔ (v j)[i]? = some true))
    (t : ℕ) (Y : Finset (List Bool))
    (hY : Y = ((Finset.range t).image v).filter fun x => i < x.length ∧ x[i]? = some true) :
    2 * ((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card
        ≤ ((Finset.range t).filter fun j => sel j = true).card + 2 ^ (i + 1) * 2 ^ (2 ^ i) ∧
      ((Finset.range t).filter fun j => sel j = true).card
        ≤ 2 * ((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card
          + 2 ^ (i + 1) * 2 ^ (2 ^ i) + Y.card := by
  obtain ⟨hT2a, hT2b⟩ :=
    exists_countable_family_balanced_type2 v bit sel i hpar hsel t Y hY
  have hT1 := exists_countable_family_balanced_type1 v hcap i t
  have hS := Finset.card_filter_add_card_filter_not
    (s := (Finset.range t).filter fun j => sel j = true) (fun j => i < (v j).length)
  have hO := Finset.card_filter_add_card_filter_not
    (s := (Finset.range t).filter fun j => sel j = true ∧ bit j = true)
    (fun j => i < (v j).length)
  simp only [Finset.filter_filter] at hS hO
  have hS1 : ((Finset.range t).filter fun a => sel a = true ∧ ¬ i < (v a).length).card
      ≤ 2 ^ (i + 1) * 2 ^ (2 ^ i) := by
    refine le_trans (Finset.card_le_card ?_) hT1
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, not_lt.mp hj.2.2⟩
  have hO1 : ((Finset.range t).filter fun a =>
        (sel a = true ∧ bit a = true) ∧ ¬ i < (v a).length).card
      ≤ ((Finset.range t).filter fun a => sel a = true ∧ ¬ i < (v a).length).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.1.1, hj.2.2⟩
  generalize 2 ^ (i + 1) * 2 ^ (2 ^ i) = C at *
  omega

/-- Step 9 of the proof of `exists_countable_family_balanced_analysis`: the
quantitative imbalance and the parent activation bound make relative imbalance tend to zero. -/
private lemma exists_countable_family_balanced_abs
    (v : ℕ → List Bool) (bit sel : ℕ → Bool) (i : ℕ)
    (hpar : ∀ j, bit j = decide ((((Finset.range j).filter fun j' => v j' = v j).card) % 2 = 1))
    (hcap : ∀ j, ((Finset.range j).filter fun j' => v j' = v j).card < 2 ^ (2 ^ (v j).length))
    (htired : ∀ j, v j ≠ [] →
      2 ^ (2 ^ ((v j).length - 1)) ≤
        ((Finset.range j).filter fun j' => v j' = (v j).dropLast).card)
    (hsel : ∀ j, i < (v j).length → (sel j = true ↔ (v j)[i]? = some true)) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ t : ℕ,
      L ≤ ((Finset.range t).filter fun j => sel j = true).card →
      |(((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card : ℝ)
          - (((Finset.range t).filter fun j => sel j = true).card : ℝ) / 2|
        ≤ ε * (((Finset.range t).filter fun j => sel j = true).card : ℝ) := by
  intro ε hε
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = 2 ^ (i + 1) * 2 ^ (2 ^ i) := ⟨_, rfl⟩
  obtain ⟨K', hK'⟩ := exists_countable_family_balanced_numeric ε hε C
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = max K' (i + 1) := ⟨_, rfl⟩
  have hK1 : K' ≤ K := by rw [hK]; exact le_max_left _ _
  have hK2 : i + 1 ≤ K := by rw [hK]; exact le_max_right _ _
  refine ⟨⌈((C : ℝ) + 2 ^ (K + 1)) / (2 * ε)⌉₊, fun t ht => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Finset (List Bool), Y = ((Finset.range t).image v).filter
      fun x => i < x.length ∧ x[i]? = some true := ⟨_, rfl⟩
  obtain ⟨ha, hb⟩ := exists_countable_family_balanced_nat_bounds v bit sel i
      hpar hcap
    hsel t Y hY
  rw [← hCdef] at ha hb
  have hclaim : (C : ℝ) + (Y.card : ℝ)
      ≤ 2 * ε * (((Finset.range t).filter fun j => sel j = true).card : ℝ) := by
    by_cases hcase : ∀ y ∈ Y, y.length ≤ K
    · obtain ⟨W, hW, hmem, hlen⟩ := exists_countable_family_balanced_lists K
      have hYW : Y ⊆ W := fun y hy => hmem y (hcase y hy)
      have hYc : Y.card + 1 ≤ 2 ^ (K + 1) :=
        le_trans (Nat.succ_le_succ (Finset.card_le_card hYW)) hW
      have hYc' : Y.card ≤ 2 ^ (K + 1) := by omega
      have hYr : (Y.card : ℝ) ≤ 2 ^ (K + 1) := by exact_mod_cast hYc'
      have hL : ((C : ℝ) + 2 ^ (K + 1)) / (2 * ε)
          ≤ (⌈((C : ℝ) + 2 ^ (K + 1)) / (2 * ε)⌉₊ : ℝ) := Nat.le_ceil _
      have hLS : (⌈((C : ℝ) + 2 ^ (K + 1)) / (2 * ε)⌉₊ : ℝ)
          ≤ (((Finset.range t).filter fun j => sel j = true).card : ℝ) := by exact_mod_cast ht
      have h3 := le_trans hL hLS
      rw [div_le_iff₀ (by positivity)] at h3
      linarith
    · have hcase' : ∃ y ∈ Y, K < y.length := by
        by_contra hcon
        exact hcase fun y hy => not_lt.mp fun hlt => hcon ⟨y, hy, hlt⟩
      obtain ⟨y0, hy0, hy0len⟩ := hcase'
      obtain ⟨y, hyY, hymax⟩ := Finset.exists_max_image Y List.length ⟨y0, hy0⟩
      have hMK : K < y.length := lt_of_lt_of_le hy0len (hymax y0 hy0)
      have hyY' := hyY
      rw [hY, Finset.mem_filter, Finset.mem_image] at hyY'
      obtain ⟨⟨j0, hj0, hvj0⟩, hiy, hxy⟩ := hyY'
      rw [Finset.mem_range] at hj0
      rw [← hvj0] at hMK hxy hiy
      have hpar' := exists_countable_family_balanced_parent v sel i htired hsel
          t j0 hj0
        (by omega) hxy
      obtain ⟨W, hW, hmem, hlen⟩ :=
        exists_countable_family_balanced_lists (v j0).length
      have hYW : Y ⊆ W := fun z hz => hmem z (by rw [hvj0]; exact hymax z hz)
      have hYc : Y.card + 1 ≤ 2 ^ ((v j0).length + 1) :=
        le_trans (Nat.succ_le_succ (Finset.card_le_card hYW)) hW
      obtain ⟨m, hm⟩ : ∃ m, (v j0).length = m + 1 := ⟨(v j0).length - 1, by omega⟩
      have hnum := hK' m (by omega)
      rw [hm] at hYc hpar'
      rw [Nat.add_sub_cancel] at hpar'
      have hYc' : Y.card ≤ 2 ^ (m + 1 + 1) := by omega
      have hYr : (Y.card : ℝ) ≤ 2 ^ (m + 2) := by exact_mod_cast hYc'
      have h4 : (2 : ℝ) ^ (2 ^ m)
          ≤ (((Finset.range t).filter fun j => sel j = true).card : ℝ) := by exact_mod_cast hpar'
      have hε2 : (0 : ℝ) ≤ 2 * ε := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 hε2]
  have ha' : (2 * ((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card : ℝ)
      ≤ (((Finset.range t).filter fun j => sel j = true).card : ℝ) + C := by exact_mod_cast ha
  have hb' : (((Finset.range t).filter fun j => sel j = true).card : ℝ)
      ≤ 2 * (((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card : ℝ) + C
        + Y.card := by exact_mod_cast hb
  have hY0 : (0 : ℝ) ≤ (Y.card : ℝ) := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Step 10 of the proof of `exists_countable_family_balanced_analysis`: list
counts over a range equal cardinalities of filtered finite ranges. -/
private lemma exists_countable_family_balanced_countP
    (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    (List.range n).countP (fun m => decide (p m)) =
      ((Finset.range n).filter p).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    by_cases hp : p n <;> simp [hp]

open Classical in
/-- Step 11 of the proof of `exists_countable_family_balanced_analysis`: the
length and number of ones in the selected chain are counts of selected positions. -/
private lemma exists_countable_family_balanced_selectChain_counts
    (R : Set BitString)
    (w : CantorSeq) (t : ℕ) :
    (selectChain R w t).length
        = ((Finset.range t).filter fun j => decide (cantorPrefix w j ∈ R) = true).card ∧
      (selectChain R w t).count true
        = ((Finset.range t).filter fun j =>
            decide (cantorPrefix w j ∈ R) = true ∧ w j = true).card := by
  induction t with
  | zero =>
    rw [exists_finite_family_balanced_finiteOrFreq_selectChain_zero]
    simp
  | succ t ih =>
    rw [exists_finite_family_balanced_finiteOrFreq_selectChain_succ, Finset.range_add_one,
      Finset.filter_insert, Finset.filter_insert]
    by_cases hR : cantorPrefix w t ∈ R
    · cases hw : w t <;> simp [hR, ih.1, ih.2]
    · simp [hR, ih.1, ih.2]

/-- Step 2 of the proof of `exists_countable_family_balanced`: the constructed sequence
has the desired finite or frequency limit property. -/
private lemma exists_countable_family_balanced_analysis (R : ℕ → Set BitString)
    (w : CantorSeq) (a : ℕ → BitString)
    (h1 : ∀ n, w n = decide ((List.range n).countP (fun m => a m = a n) % 2 = 1))
    (h2 : ∀ n j (hj : j < (a n).length), (a n).get ⟨j, hj⟩ = true ↔ cantorPrefix w n ∈ R j)
    (h3 : ∀ n, (List.range n).countP (fun m => a m = a n) < 2 ^ (2 ^ (a n).length))
    (h4 : ∀ n, (a n) ≠ [] → 2 ^ (2 ^ ((a n).length - 1)) ≤ (List.range n).countP
        (fun m => a m = (a n).dropLast)) :
    ∀ i, FiniteOrFreq (1 / 2) (selectStream (R i) w) := by
  classical
  intro i
  have hpar : ∀ j, w j = decide (((Finset.range j).filter fun j' => a j' = a j).card % 2 = 1) := by
    intro j
    rw [h1 j, exists_countable_family_balanced_countP]
  have hcap : ∀ j, ((Finset.range j).filter fun j' => a j' = a j).card < 2 ^ (2 ^ (a j).length) :=
      by
    intro j
    simpa only [exists_countable_family_balanced_countP] using h3 j
  have htired : ∀ j, a j ≠ [] →
      2 ^ (2 ^ ((a j).length - 1)) ≤
        ((Finset.range j).filter fun j' => a j' = (a j).dropLast).card := by
    intro j hj
    simpa only [exists_countable_family_balanced_countP] using h4 j hj
  have hsel : ∀ j, i < (a j).length →
      (decide (cantorPrefix w j ∈ R i) = true ↔ (a j)[i]? = some true) := by
    intro j hj
    rw [decide_eq_true_iff, List.getElem?_eq_getElem hj]
    simpa using (h2 j i hj).symm
  have habs := exists_countable_family_balanced_abs a w
    (fun j => decide (cantorPrefix w j ∈ R i)) i hpar hcap htired hsel
  apply exists_finite_family_balanced_finiteOrFreq_chain_freq
  intro ε hε
  obtain ⟨L, hL⟩ := habs ε hε
  refine ⟨L, fun t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ :=
    exists_countable_family_balanced_selectChain_counts (R i) w t
  rw [ht1] at ht
  rw [ht2, ht1]
  exact hL t ht

/-- Step 3 of the proof of `exists_countable_family_balanced`: the constructed sequence
has at least as many zeros as ones. -/
private lemma exists_countable_family_balanced_zeros (w : CantorSeq) (a : ℕ → BitString)
    (h1 : ∀ n, w n = decide ((List.range n).countP (fun m => a m = a n) % 2 = 1)) :
    ZerosDominate w := by
  classical
  have hpar : ∀ j, w j = decide (((Finset.range j).filter fun j' => a j' = a j).card % 2 = 1) := by
    intro j
    rw [h1 j, exists_countable_family_balanced_countP]
  have hcount (n : ℕ) : (cantorPrefix w n).count true =
      ((Finset.range n).filter fun j => w j = true).card := by
    induction n with
    | zero => simp [cantorPrefix]
    | succ n ih =>
      rw [cantorPrefix_succ, List.count_append, ih, Finset.range_add_one,
        Finset.filter_insert]
      cases hb : w n <;> simp [hb]
  intro t
  let A := (Finset.range t).image a
  have hmaps : ∀ j ∈ (Finset.range t).filter (fun j => w j = true), a j ∈ A := by
    intro j hj
    exact Finset.mem_image_of_mem a (Finset.mem_filter.mp hj).1
  have hbound : 2 * ((Finset.range t).filter fun j => w j = true).card ≤ t := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.mul_sum]
    calc
      ∑ x ∈ A, 2 * (((Finset.range t).filter fun j => w j = true).filter
          fun j => a j = x).card
          ≤ ∑ x ∈ A, ((Finset.range t).filter fun j => a j = x).card := by
        apply Finset.sum_le_sum
        intro x hx
        have hfiber : (((Finset.range t).filter fun j => w j = true).filter
            fun j => a j = x) =
            (Finset.range t).filter fun j => a j = x ∧ w j = true := by
          ext j
          simp only [Finset.mem_filter]
          tauto
        rw [hfiber, exists_countable_family_balanced_ones_fiber a w hpar x t]
        omega
      _ = t := by
        simpa only [Finset.card_range] using (Finset.card_eq_sum_card_image a (Finset.range t)).symm
  have hsum := count_true_add_count_false_eq_length (cantorPrefix w t)
  rw [cantorPrefix_length, hcount t] at hsum
  change (cantorPrefix w t).count true ≤ (cantorPrefix w t).count false
  rw [hcount t]
  omega

/-- **SUV p. 269**, countably many rules: there is `ω` such that all `S_{R_i}(ω)` are finite or
balanced and every prefix of `ω` has at least as many zeros as ones. -/
theorem exists_countable_family_balanced (R : ℕ → Set BitString) :
    ∃ w : CantorSeq, (∀ i, FiniteOrFreq (1 / 2) (selectStream (R i) w)) ∧ ZerosDominate w := by
  obtain ⟨w, a, h1, h2, h3, h4⟩ := exists_countable_family_balanced_construction R
  exact ⟨w, exists_countable_family_balanced_analysis R w a h1 h2 h3 h4,
      exists_countable_family_balanced_zeros w a h1⟩

end Kolmogorov.FrequencyGames
