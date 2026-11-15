/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Computability.Halting
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.List
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Foundation.UnboundedSearch

/-!
# Biinfinite Sequences

Sequences that avoid all long substrings from a set `F` of forbidden strings.

For a one-sided infinite sequence `w : ℕ → Bool` we define the substring `seqFactor w i n`, the
occurrence predicate `OccursIn`, and `AvoidsLong F c w` (no string of `F` of length at least `c`
occurs in `w`).  The hypotheses of the forbidden-substring theorems are the counting conditions
`IsAtMostForbidden` (at most `2^{αn}` strings of length `n`) and `IsLessForbidden` (fewer than
`2^{αn}` such strings).

## Main results

* `exists_seq_avoiding_iff_arbitrarily_long`: the compactness argument showing that a sequence
  avoiding `F` exists if and only if there are arbitrarily long finite strings avoiding `F`.
* `exists_decidable_counterexample`: if the statement of SUV Theorem 157 fails for some set `F`,
  it fails for a decidable set (SUV Theorem 159).
* `exists_biinfinite_avoiding`: a one-sided sequence with no substring from `F` yields a
  bi-infinite sequence with none (SUV Problem 247).

This formalizes part of the chapter of Shen, Uspensky and Vereshchagin, "Kolmogorov complexity
and algorithmic randomness", on applications of Kolmogorov complexity to forbidden substrings.
-/

namespace Kolmogorov.Applications

open scoped ENNReal

/-- The string of length `n` that starts at position `i` of `ω`. -/
def seqFactor (w : ℕ → Bool) (i n : ℕ) : List Bool := List.ofFn fun j : Fin n => w (i + j)

/-- The string `u` occurs in `ω`: it is a substring of consecutive bits. -/
def OccursIn (u : List Bool) (w : ℕ → Bool) : Prop := ∃ i, seqFactor w i u.length = u

/-- Finitely many strings have a given length. -/
lemma finite_length_eq (n : ℕ) : {x : List Bool | x.length = n}.Finite :=
  List.finite_length_eq Bool n

/-- **SUV Theorem 157, hypothesis.**  At most `2^{αn}` strings of `F` have length `n`, for each
`n`. -/
def IsAtMostForbidden (α : ℝ) (F : Set (List Bool)) : Prop :=
  ∀ n : ℕ, (({x ∈ F | x.length = n} : Set (List Bool)).ncard : ℝ) ≤ (2 : ℝ) ^ (α * n)

/-- **SUV Theorem 159, hypothesis.**  Fewer than `2^{αn}` strings of `F` have length `n`, for each
`n`.  For `n = 0` this says that the empty string is not in `F`. -/
def IsLessForbidden (α : ℝ) (F : Set (List Bool)) : Prop :=
  ∀ n : ℕ, (({x ∈ F | x.length = n} : Set (List Bool)).ncard : ℝ) < (2 : ℝ) ^ (α * n)

/-- The sequence `ω` has no substring of `F` of length `c` or more. -/
def AvoidsLong (F : Set (List Bool)) (c : ℕ) (w : ℕ → Bool) : Prop :=
  ∀ u ∈ F, c ≤ u.length → ¬ OccursIn u w

/-- One more bit of a factor of a sequence. -/
lemma seqFactor_succ (w : ℕ → Bool) (i n : ℕ) :
    seqFactor w i (n + 1) = seqFactor w i n ++ [w (i + n)] := by
  simp only [seqFactor, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

/-- A factor of a sequence splits into two consecutive factors. -/
lemma seqFactor_add (w : ℕ → Bool) (i j n : ℕ) :
    seqFactor w i (j + n) = seqFactor w i j ++ seqFactor w (i + j) n := by
  induction n with
  | zero => simp [seqFactor]
  | succ n ih =>
    rw [← Nat.add_assoc, seqFactor_succ, ih, seqFactor_succ, List.append_assoc, Nat.add_assoc]

/-- The length of a factor. -/
lemma length_seqFactor (w : ℕ → Bool) (i n : ℕ) : (seqFactor w i n).length = n := by
  simp [seqFactor]

/-- The bits of a factor. -/
lemma getElem?_seqFactor (w : ℕ → Bool) (i n j : ℕ) :
    (seqFactor w i n)[j]? = if j < n then some (w (i + j)) else none := by
  simp [seqFactor, List.getElem?_ofFn]

/-- A substring of a prefix of a sequence occurs in the sequence. -/
private lemma occursIn_of_infix {u : List Bool} {w : ℕ → Bool} {n : ℕ}
    (h : u <:+: seqFactor w 0 n) : OccursIn u w := by
  obtain ⟨s, t, hst⟩ := h
  have hlen : s.length + u.length + t.length = n := by
    have := congrArg List.length hst
    simp only [List.length_append, length_seqFactor] at this
    omega
  refine ⟨s.length, List.ext_getElem? fun j => ?_⟩
  rw [getElem?_seqFactor]
  by_cases hj : j < u.length
  · have hjn : s.length + j < n := by omega
    have hat := congrArg (fun l => l[s.length + j]?) hst
    simp only [getElem?_seqFactor, hjn, ite_true, Nat.zero_add] at hat
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_append_left hj] at hat
    rw [ite_eq_left hj, ← hat]
  · rw [ite_eq_right hj, List.getElem?_eq_none (not_lt.mp hj)]

/-- **SUV p. 247, the compactness argument.**  There is an infinite sequence with no substring in
`F` exactly when there are arbitrarily long strings with no substring in `F`. -/
theorem exists_seq_avoiding_iff_arbitrarily_long (F : Set (List Bool)) :
    (∃ w, ∀ u ∈ F, ¬ OccursIn u w) ↔ ∀ n, ∃ x : List Bool, x.length = n ∧ ∀ u ∈ F, ¬ u <:+: x := by
  constructor
  · rintro ⟨w, hw⟩ n
    exact ⟨seqFactor w 0 n, length_seqFactor w 0 n, fun u hu h => hw u hu (occursIn_of_infix h)⟩
  · intro hlong
    let C : ℕ → Set (ℕ → Bool) := fun n => {w | ∀ u ∈ F, ¬ u <:+: seqFactor w 0 n}
    have hclosed : ∀ n, IsClosed (C n) := by
      intro n
      have hcont : Continuous fun w : ℕ → Bool => fun i : Fin n => w (0 + i) :=
        continuous_pi fun i => continuous_apply _
      exact (isClosed_discrete {y : Fin n → Bool | ∀ u ∈ F, ¬ u <:+: List.ofFn y}).preimage hcont
    have hanti : ∀ n, C (n + 1) ⊆ C n := by
      intro n w hw u hu hinf
      refine hw u hu (hinf.trans ?_)
      rw [seqFactor_succ]
      exact (List.prefix_append _ _).isInfix
    have hne : ∀ n, (C n).Nonempty := by
      intro n
      obtain ⟨x, hx, hxF⟩ := hlong n
      refine ⟨fun i => x[i]?.getD false, fun u hu hinf => hxF u hu ?_⟩
      have hfac : seqFactor (fun i => x[i]?.getD false) 0 n = x := by
        refine List.ext_getElem? fun j => ?_
        rw [getElem?_seqFactor, Nat.zero_add]
        by_cases hj : j < n
        · rw [ite_eq_left hj, List.getElem?_eq_getElem (hx ▸ hj)]
          simp
        · rw [ite_eq_right hj, List.getElem?_eq_none (by omega)]
      rwa [hfac] at hinf
    obtain ⟨w, hw⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hanti hne
      (hclosed 0).isCompact hclosed
    refine ⟨w, fun u hu ⟨i, hi⟩ => ?_⟩
    have hmem := Set.mem_iInter.mp hw (i + u.length)
    refine hmem u hu ?_
    rw [seqFactor_add, Nat.zero_add, hi]
    exact (List.suffix_append _ _).isInfix


private def exists_decidable_counterexample_GoodFinset
    (α : ℝ) (c N : ℕ) (E : Finset (List Bool)) : Prop :=
  (∀ x ∈ E, c ≤ x.length) ∧
  (∀ n, ((E.filter (·.length = n)).card : ℝ) < (2 : ℝ) ^ (α * n)) ∧
  (∀ w : List Bool, w.length = N → ∃ u ∈ E, u <:+: w)

/-- Step 1 of the proof of `exists_decidable_counterexample`: The standard argument
(compactness, König's lemma) shows that every sufficiently long string has at least one substring
in F_c, so one can find finite F_c with the same properties. -/
private lemma exists_decidable_counterexample_exists_good (α : ℚ)
    (F : Set (List Bool)) (hF : IsLessForbidden (α : ℝ) F)
    (hfail : ¬ ∃ c w, AvoidsLong F c w) (c : ℕ) :
    ∃ N E, c ≤ N ∧ exists_decidable_counterexample_GoodFinset (α : ℝ) c N E := by
  let Fc := {u ∈ F | c ≤ u.length}
  have hfail2 : ¬ ∀ n, ∃ x : List Bool, x.length = n ∧ ∀ u ∈ Fc, ¬ u <:+: x := by
    intro h
    have h3 : ∃ w, ∀ u ∈ Fc, ¬ OccursIn u w :=
      (exists_seq_avoiding_iff_arbitrarily_long Fc).mpr h
    obtain ⟨w, hw⟩ := h3
    apply hfail
    use c, w
    intro u hu hc
    exact hw u ⟨hu, hc⟩
  simp only [not_forall, not_exists, not_and, not_forall, not_not] at hfail2
  obtain ⟨N0, hN0⟩ := hfail2
  let N := max N0 c
  
  have h_finite : {x ∈ F | c ≤ x.length ∧ x.length ≤ N}.Finite := by
    have : {x ∈ F | c ≤ x.length ∧ x.length ≤ N} ⊆ {x : List Bool | x.length ≤ N} :=
      fun x h => h.2.2
    exact (List.finite_length_le Bool N).subset this
  let E_set := {x ∈ F | c ≤ x.length ∧ x.length ≤ N}
  let E : Finset (List Bool) := Set.Finite.toFinset h_finite
  use N, E
  refine ⟨le_max_right N0 c, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx2 : x ∈ E_set := (Set.Finite.mem_toFinset _).mp hx
    exact hx2.2.1
  · intro n
    have hsub : (E.filter (·.length = n) : Set (List Bool)) ⊆ {x ∈ F | x.length = n} := by
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      have hx2 : x ∈ E_set := (Set.Finite.mem_toFinset _).mp hx.1
      exact ⟨hx2.1, hx.2⟩
    have hcard : ((E.filter (·.length = n)).card : ℝ) ≤
        (({x ∈ F | x.length = n} : Set (List Bool)).ncard : ℝ) := by
      norm_cast
      have hc : (E.filter (·.length = n)).card =
          ((E.filter (·.length = n) : Set (List Bool))).ncard := by
        exact (Set.ncard_coe_finset _).symm
      rw [hc]
      refine Set.ncard_le_ncard hsub ?_
      have : {x ∈ F | x.length = n} ⊆ {x : List Bool | x.length = n} := fun x h => h.2
      exact (finite_length_eq n).subset this
    calc ((E.filter (·.length = n)).card : ℝ) ≤
        (({x ∈ F | x.length = n} : Set (List Bool)).ncard : ℝ) := hcard
      _ < (2 : ℝ) ^ ((α : ℝ) * (n : ℝ)) := hF n
  · intro w hw
    have hpre : (w.take N0).length = N0 := by
      rw [List.length_take, hw]
      exact min_eq_left (le_max_left N0 c)
    obtain ⟨u, hu, hu_inf⟩ := hN0 (w.take N0) hpre
    use u
    constructor
    · have h_in : u ∈ E_set := by
        refine ⟨hu.1, hu.2, ?_⟩
        have : u.length ≤ (w.take N0).length := List.IsInfix.length_le hu_inf
        rw [hpre] at this
        exact this.trans (le_max_left N0 c)
      exact (Set.Finite.mem_toFinset _).mpr h_in
    · exact hu_inf.trans (List.take_prefix N0 w).isInfix

/-- Step 2a_1 of the proof:
The rational budget check is equivalent to an integer check. -/
private lemma exists_decidable_counterexample_step2a1_budget (α : ℚ) (hα0 : 0 < α)
    (E : Finset (List Bool)) (n : ℕ) :
    ((E.filter (·.length = n)).card : ℝ) < (2 : ℝ) ^ ((α : ℝ) * n) ↔
    (E.filter (·.length = n)).card ^ (α.den : ℕ) < 2 ^ (α.num.toNat * n) := by
  set k := (E.filter (·.length = n)).card
  set t := (2 : ℝ) ^ ((α : ℝ) * n)
  have ht_pos : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  
  have h_num_pos : 0 < α.num := Rat.num_pos.mpr hα0
  have h_num_toNat : (α.num.toNat : ℝ) = (α.num : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (le_of_lt h_num_pos))
  have h_den_pos : 0 < (α.den : ℕ) := α.den_pos
  have h_alpha : (α : ℝ) = (α.num : ℝ) / (α.den : ℝ) := Rat.cast_def α
  
  have ht_pow : t ^ (α.den : ℕ) = (2 : ℝ) ^ (α.num.toNat * n) := by
    change ((2 : ℝ) ^ ((α : ℝ) * n)) ^ (α.den : ℕ) = _
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num)]
    have h_den_real_pos : (0 : ℝ) < α.den := by exact_mod_cast h_den_pos
    have eq1 : (α : ℝ) * n * (α.den : ℕ) = (α.num : ℝ) * n := by
      rw [h_alpha]
      have : ((α.den : ℕ) : ℝ) = (α.den : ℝ) := by rfl
      rw [this]
      calc (α.num : ℝ) / (α.den : ℝ) * n * (α.den : ℝ)
        _ = (α.num : ℝ) * n / (α.den : ℝ) * (α.den : ℝ) := by ring
        _ = (α.num : ℝ) * n := div_mul_cancel₀ _ (ne_of_gt h_den_real_pos)
    have eq2 : (α.num.toNat : ℝ) * n = (α.num : ℝ) * n := by rw [h_num_toNat]
    have eq3 : (α : ℝ) * n * (α.den : ℕ) = (α.num.toNat * n : ℕ) := by 
      push_cast
      rw [eq1, ← eq2]
    rw [eq3]
    exact Real.rpow_natCast 2 (α.num.toNat * n)
    
  have hk_cast : ((k ^ (α.den : ℕ) : ℕ) : ℝ) = (k : ℝ) ^ (α.den : ℕ) := by
    push_cast; rfl
  have h2_cast : ((2 ^ (α.num.toNat * n) : ℕ) : ℝ) = (2 : ℝ) ^ (α.num.toNat * n) := by
    push_cast; rfl
  
  rw [← Nat.cast_lt (α := ℝ)]
  rw [hk_cast, h2_cast]
  rw [← ht_pow]
  
  exact (pow_lt_pow_iff_left₀ (Nat.cast_nonneg k) (le_of_lt ht_pos)
    (ne_of_gt h_den_pos)).symm

/-- The list of all bit strings of length `n`. -/
private def exists_decidable_counterexample_step2a2_test_allStr : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (exists_decidable_counterexample_step2a2_test_allStr n).flatMap
      fun w => [false :: w, true :: w]

/-- The list `allStr n` consists of exactly the strings of length `n`. -/
private lemma exists_decidable_counterexample_step2a2_test_mem_allStr (n : ℕ) (w : List Bool) :
    w ∈ exists_decidable_counterexample_step2a2_test_allStr n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [exists_decidable_counterexample_step2a2_test_allStr]
  | succ n ih =>
    cases w with
    | nil => simp [exists_decidable_counterexample_step2a2_test_allStr]
    | cons b w =>
      cases b <;> simp [exists_decidable_counterexample_step2a2_test_allStr, ih]

/-- The list of all strings of a given length is primitive recursive in the length. -/
private lemma exists_decidable_counterexample_step2a2_test_primrec_allStr :
    Primrec exists_decidable_counterexample_step2a2_test_allStr := by
  have h : exists_decidable_counterexample_step2a2_test_allStr =
      Nat.rec [[]] (fun _ L => L.flatMap fun w => [false :: w, true :: w]) := by
    funext n; induction n with
    | zero => rfl
    | succ n ih => simp only [exists_decidable_counterexample_step2a2_test_allStr, ih]
  rw [h]
  refine Primrec.nat_rec₁ [[]] (Primrec.list_flatMap Primrec.snd ?_)
  exact Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
    (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
      (Primrec.const []))

/-- A substring is a block `take |u| (drop i w)` for some position `i ≤ |w|`. -/
private lemma exists_decidable_counterexample_step2a2_test_infix_iff (u w : List Bool) :
    u <:+: w ↔ ∃ i ∈ List.range (w.length + 1), (w.drop i).take u.length = u := by
  constructor
  · rintro ⟨s, t, rfl⟩
    refine ⟨s.length, List.mem_range.mpr (by simp), ?_⟩
    simp
  · rintro ⟨i, -, h⟩
    refine ⟨w.take i, (w.drop i).drop u.length, ?_⟩
    conv_rhs => rw [← List.take_append_drop i w, ← List.take_append_drop u.length (w.drop i), h]
    simp

/-- The substring relation is primitive recursive. -/
private lemma exists_decidable_counterexample_step2a2_test_primrec_isInfix :
    Primrec₂ (fun u w : List Bool => decide (u <:+: w)) := by
  have h : ∀ p : List Bool × List Bool, decide (p.1 <:+: p.2) =
      (List.range (p.2.length + 1)).any (fun i => decide ((p.2.drop i).take p.1.length = p.1)) := by
    intro p
    rw [Bool.eq_iff_iff]
    simp [exists_decidable_counterexample_step2a2_test_infix_iff]
  refine Primrec.of_eq ?_ (fun p => (h p).symm)
  exact list_any_primrec (f := fun p : List Bool × List Bool => List.range (p.2.length + 1))
    (p := fun p i => decide ((p.2.drop i).take p.1.length = p.1))
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.snd)))
    (Primrec.eq.comp (Primrec.list_take.comp (Primrec.list_length.comp
        (Primrec.fst.comp Primrec.fst))
      (Primrec.list_drop.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp Primrec.fst)).decide

/-- The list-level version of the goodness conditions, with the integer budget test. -/
private def exists_decidable_counterexample_step2a2_test_GoodList (α : ℚ) (c N : ℕ)
    (L : List (List Bool)) : Prop :=
  (∀ x ∈ L, c ≤ x.length) ∧
  (∀ x ∈ L, ((L.filter (fun y => decide (y.length = x.length))).length) ^ α.den <
      2 ^ (α.num.toNat * x.length)) ∧
  (∀ w : List Bool, w.length = N → ∃ u ∈ L, u <:+: w)

/-- The Boolean goodness test, for `α = p / q`. -/
private def exists_decidable_counterexample_step2a2_test_goodB (p q c N : ℕ)
    (L : List (List Bool)) : Bool :=
  L.all (fun x => decide (c ≤ x.length)) &&
  L.all (fun x => decide (((L.filter (fun y => decide (y.length = x.length))).length) ^ q <
      2 ^ (p * x.length))) &&
  (exists_decidable_counterexample_step2a2_test_allStr N).all
    (fun w => L.any (fun u => decide (u <:+: w)))

/-- The Boolean test decides the list-level goodness conditions. -/
private lemma exists_decidable_counterexample_step2a2_test_goodB_iff (α : ℚ) (c N : ℕ)
    (L : List (List Bool)) :
    exists_decidable_counterexample_step2a2_test_goodB α.num.toNat α.den c N L = true ↔
      exists_decidable_counterexample_step2a2_test_GoodList α c N L := by
  simp only [exists_decidable_counterexample_step2a2_test_goodB,
    exists_decidable_counterexample_step2a2_test_GoodList, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, List.any_eq_true, exists_decidable_counterexample_step2a2_test_mem_allStr]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun w hw => h3 w hw⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun w hw => h3 w hw⟩

/-- The Boolean test is primitive recursive. -/
private lemma exists_decidable_counterexample_step2a2_test_primrec_goodB (p q : ℕ) :
    Primrec (fun r : ℕ × ℕ × List (List Bool) =>
      exists_decidable_counterexample_step2a2_test_goodB p q r.1 r.2.1 r.2.2) := by
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec.nat_iff.mpr Nat.Primrec.pow
  have h1 : Primrec (fun r : ℕ × ℕ × List (List Bool) =>
      r.2.2.all (fun x => decide (r.1 ≤ x.length))) :=
    list_all_primrec (f := fun r : ℕ × ℕ × List (List Bool) => r.2.2)
      (p := fun r x => decide (r.1 ≤ x.length))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd)).decide
  have h2 : Primrec (fun r : ℕ × ℕ × List (List Bool) =>
      r.2.2.all (fun x =>
        decide (((r.2.2.filter (fun y => decide (y.length = x.length))).length) ^ q <
          2 ^ (p * x.length)))) := by
    refine list_all_primrec (f := fun r : ℕ × ℕ × List (List Bool) => r.2.2)
      (p := fun r x =>
        decide (((r.2.2.filter (fun y => decide (y.length = x.length))).length) ^ q <
          2 ^ (p * x.length))) (Primrec.snd.comp Primrec.snd) ?_
    have hfil : Primrec (fun a : (ℕ × ℕ × List (List Bool)) × List Bool =>
        (a.1.2.2.filter (fun y => decide (y.length = a.2.length)))) :=
      Primrec.list_filter (l := fun a : (ℕ × ℕ × List (List Bool)) × List Bool => a.1.2.2)
        (p := fun a y => decide (y.length = a.2.length))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))).decide
    exact (Primrec.nat_lt.comp
      (hpow.comp (Primrec.list_length.comp hfil) (Primrec.const q))
      (hpow.comp (Primrec.const 2)
        (Primrec.nat_mul.comp (Primrec.const p) (Primrec.list_length.comp Primrec.snd)))).decide
  have h3 : Primrec (fun r : ℕ × ℕ × List (List Bool) =>
      (exists_decidable_counterexample_step2a2_test_allStr r.2.1).all
        (fun w => r.2.2.any (fun u => decide (u <:+: w)))) :=
    list_all_primrec
      (f := fun r : ℕ × ℕ × List (List Bool) =>
        exists_decidable_counterexample_step2a2_test_allStr r.2.1)
      (p := fun r w => r.2.2.any (fun u => decide (u <:+: w)))
      (exists_decidable_counterexample_step2a2_test_primrec_allStr.comp
        (Primrec.fst.comp Primrec.snd))
      (list_any_primrec (f := fun a : (ℕ × ℕ × List (List Bool)) × List Bool => a.1.2.2)
        (p := fun a u => decide (u <:+: a.2))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (exists_decidable_counterexample_step2a2_test_primrec_isInfix.comp Primrec.snd
          (Primrec.snd.comp Primrec.fst)))
  exact (Primrec.and.comp (Primrec.and.comp h1 h2) h3)

/-- Membership in a list is a primitive recursive relation. -/
private theorem exists_decidable_counterexample_step2a2_test_primrecRel_mem {β : Type*}
    [Primcodable β] : PrimrecRel fun (L : List β) (x : β) => x ∈ L :=
  Primrec.eq.exists_mem_list.of_eq fun L x => by simp

/-- Removing duplicates is primitive recursive (a copy of the private `primrec_dedup` of
`StoppingComplexity/Repacking.lean`). -/
private theorem exists_decidable_counterexample_step2a2_test_primrec_dedup {β : Type*}
    [Primcodable β] [DecidableEq β] : Primrec (List.dedup : List β → List β) := by
  have hstep : Primrec₂ fun (_ : List β) (p : β × List β) =>
      if p.1 ∈ p.2 then p.2 else p.1 :: p.2 :=
    (Primrec.ite (exists_decidable_counterexample_step2a2_test_primrecRel_mem.comp
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂
  refine (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [id, List.foldr_cons] at ih ⊢
    rw [ih]
    by_cases h : a ∈ l
    · rw [ite_eq_left (List.mem_dedup.2 h), List.dedup_cons_of_mem h]
    · rw [ite_eq_right (mt List.mem_dedup.1 h), List.dedup_cons_of_notMem h]

/-- A list passing the list-level test gives a good finite set (counts in a list bound the
cardinalities of the filtered finset). -/
private lemma exists_decidable_counterexample_step2a2_test_goodFinset_of_goodList (α : ℚ)
    (hα : 0 < α) (c N : ℕ) (L : List (List Bool))
    (h : exists_decidable_counterexample_step2a2_test_GoodList α c N L) :
    exists_decidable_counterexample_GoodFinset (α : ℝ) c N L.toFinset := by
  refine ⟨fun x hx => h.1 x (List.mem_toFinset.mp hx), fun n => ?_, fun w hw => ?_⟩
  · by_cases hn : ∃ x ∈ L, x.length = n
    · obtain ⟨x, hx, rfl⟩ := hn
      have h2 : (L.toFinset.filter (·.length = x.length)).card ≤
          (L.filter (fun y => decide (y.length = x.length))).length := by
        have : L.toFinset.filter (·.length = x.length) =
            (L.filter (fun y => decide (y.length = x.length))).toFinset := by
          ext y
          simp
        rw [this]
        exact List.toFinset_card_le _
      exact (exists_decidable_counterexample_step2a1_budget α hα L.toFinset x.length).mpr
        (lt_of_le_of_lt (Nat.pow_le_pow_left h2 _) (h.2.1 x hx))
    · push Not at hn
      have hempty : L.toFinset.filter (·.length = n) = ∅ := by
        ext x
        simp only [Finset.mem_filter, List.mem_toFinset, Finset.notMem_empty, iff_false, not_and]
        exact fun hx hxn => hn x hx hxn
      rw [hempty, Finset.card_empty]
      simpa using Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((α : ℝ) * n)
  · obtain ⟨u, hu, hinf⟩ := h.2.2 w hw
    exact ⟨u, List.mem_toFinset.mpr hu, hinf⟩

/-- A good finite set `L.toFinset` makes the duplicate-free list `L.dedup` pass the list-level
test (in a nodup list the counts are the cardinalities of the filtered finset). -/
private lemma exists_decidable_counterexample_step2a2_test_goodList_dedup (α : ℚ) (hα : 0 < α)
    (c N : ℕ) (L : List (List Bool))
    (h : exists_decidable_counterexample_GoodFinset (α : ℝ) c N L.toFinset) :
    exists_decidable_counterexample_step2a2_test_GoodList α c N L.dedup := by
  refine ⟨fun x hx => h.1 x (List.mem_toFinset.mpr (List.mem_dedup.mp hx)), ?_, fun w hw => ?_⟩
  · intro x hx
    have hcount : (L.dedup.filter (fun y => decide (y.length = x.length))).length =
        (L.toFinset.filter (·.length = x.length)).card := by
      have hnd : (L.dedup.filter (fun y => decide (y.length = x.length))).Nodup :=
        (List.nodup_dedup L).filter _
      rw [← List.toFinset_card_of_nodup hnd, List.toFinset_filter, List.toFinset_dedup]
      simp
    rw [hcount]
    exact (exists_decidable_counterexample_step2a1_budget α hα L.toFinset x.length).mp
      (h.2.1 x.length)
  · obtain ⟨u, hu, hinf⟩ := h.2.2 w hw
    exact ⟨u, List.mem_dedup.mpr (List.mem_toFinset.mp hu), hinf⟩

/-- Goodness of `L.toFinset` is decided by the Boolean test on `L.dedup`. -/
private lemma exists_decidable_counterexample_step2a2_test_iff_goodB (α : ℚ) (hα : 0 < α)
    (c N : ℕ) (L : List (List Bool)) :
    exists_decidable_counterexample_GoodFinset (α : ℝ) c N L.toFinset ↔
      exists_decidable_counterexample_step2a2_test_goodB α.num.toNat α.den c N L.dedup = true := by
  rw [exists_decidable_counterexample_step2a2_test_goodB_iff]
  constructor
  · exact exists_decidable_counterexample_step2a2_test_goodList_dedup α hα c N L
  · intro h
    have := exists_decidable_counterexample_step2a2_test_goodFinset_of_goodList α hα c N L.dedup h
    rwa [List.toFinset_dedup] at this

/-- Step 2a_2 of the proof: The GoodFinset condition is computably decidable. -/
private lemma exists_decidable_counterexample_step2a2_test (α : ℚ) (hα0 : 0 < α) :
    ComputablePred (fun p : ℕ × ℕ × List (List Bool) =>
      exists_decidable_counterexample_GoodFinset (α : ℝ) p.1 p.2.1 p.2.2.toFinset) := by
  classical
  have hcomp : Computable (fun p : ℕ × ℕ × List (List Bool) =>
      exists_decidable_counterexample_step2a2_test_goodB α.num.toNat α.den p.1 p.2.1
        p.2.2.dedup) :=
    ((exists_decidable_counterexample_step2a2_test_primrec_goodB α.num.toNat α.den).comp
      (Primrec.pair Primrec.fst (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (exists_decidable_counterexample_step2a2_test_primrec_dedup.comp
          (Primrec.snd.comp Primrec.snd))))).to_comp
  exact ComputablePred.computable_iff.mpr ⟨_, hcomp, funext fun p =>
    propext (exists_decidable_counterexample_step2a2_test_iff_goodB α hα0 p.1 p.2.1 p.2.2)⟩

/-- Step 2a_3 of the proof: Computable search for GoodFinset. -/
private lemma exists_decidable_counterexample_step2a3_search (α : ℚ) (hα0 : 0 < α)
    (h_exists : ∀ c, ∃ N E, c ≤ N ∧ exists_decidable_counterexample_GoodFinset (α : ℝ) c N E) :
    ∃ Lof : ℕ → List (List Bool), Computable Lof ∧
      ∀ c, ∃ N, c ≤ N ∧
        exists_decidable_counterexample_GoodFinset (α : ℝ) c N (Lof c).toFinset := by
  classical
  obtain ⟨f, hf, hfp⟩ := ComputablePred.computable_iff.mp
    (exists_decidable_counterexample_step2a2_test α hα0)
  have hiff : ∀ c N (L : List (List Bool)),
      exists_decidable_counterexample_GoodFinset (α : ℝ) c N L.toFinset ↔ f (c, N, L) = true :=
    fun c N L => (congrFun hfp (c, N, L)).to_iff
  -- The test on `(c, n)`: `n` decodes to a pair `(N, L)` with `c ≤ N` and `(c, N, set L)` good.
  let T : ℕ × ℕ → Bool := fun cn =>
    match (Encodable.decode cn.2 : Option (ℕ × List (List Bool))) with
    | none => false
    | some r => decide (cn.1 ≤ r.1) && f (cn.1, r.1, r.2)
  have hT : Computable T := by
    have hg : Computable (fun x : (ℕ × ℕ) × (ℕ × List (List Bool)) =>
        decide (x.1.1 ≤ x.2.1) && f (x.1.1, x.2.1, x.2.2)) :=
      Primrec.and.to_comp.comp
        (Primrec.to_comp (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd)).decide)
        (hf.comp (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.pair (Computable.fst.comp Computable.snd)
            (Computable.snd.comp Computable.snd))))
    have h : Computable (fun cn : ℕ × ℕ => Option.casesOn (motive := fun _ => Bool)
        (Encodable.decode cn.2 : Option (ℕ × List (List Bool))) false
        (fun r => decide (cn.1 ≤ r.1) && f (cn.1, r.1, r.2))) :=
      Computable.option_casesOn (o := fun cn : ℕ × ℕ => (Encodable.decode cn.2 :
        Option (ℕ × List (List Bool)))) (Primrec.decode.to_comp.comp Computable.snd)
        (Computable.const false) hg
    refine h.of_eq (fun cn => ?_)
    show _ = T cn
    simp only [T]
    cases (Encodable.decode cn.2 : Option (ℕ × List (List Bool))) <;> rfl
  -- What a successful test says about an arbitrary `n`.
  have T_spec : ∀ c n, T (c, n) = true →
      ∃ r : ℕ × List (List Bool), (Encodable.decode n : Option (ℕ × List (List Bool))) = some r ∧
        c ≤ r.1 ∧ f (c, r.1, r.2) = true := by
    intro c n h
    simp only [T] at h
    cases hd : (Encodable.decode n : Option (ℕ × List (List Bool))) with
    | none => rw [hd] at h; simp at h
    | some r =>
      rw [hd] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨r, rfl, h.1, h.2⟩
  -- The test succeeds at the code of a good pair given by the hypothesis.
  have hex : ∀ c, ∃ n, T (c, n) = true := by
    intro c
    obtain ⟨N, E, hcN, hE⟩ := h_exists c
    refine ⟨Encodable.encode (N, E.toList), ?_⟩
    simp only [T, Encodable.encodek]
    have : f (c, N, E.toList) = true := by
      rw [← hiff, Finset.toList_toFinset]; exact hE
    simp [hcN, this]
  have hP : Computable (fun pr : ℕ × ℕ => decide (T (pr.1, pr.2) = true)) :=
    hT.of_eq (fun pr => by simp)
  have hfind := Computable.natFind (P := fun c n => T (c, n) = true) hP hex
  refine ⟨fun c => ((Encodable.decode (Nat.find (hex c)) : Option (ℕ × List (List Bool))).getD
    (0, [])).2, ?_, ?_⟩
  · exact Computable.snd.comp
      (Computable.option_getD (Primrec.decode.to_comp.comp hfind) (Computable.const (0, [])))
  · intro c
    obtain ⟨r, hr, hcN, hgood⟩ := T_spec c _ (Nat.find_spec (hex c))
    refine ⟨r.1, hcN, ?_⟩
    simp only [hr, Option.getD_some]
    exact (hiff c r.1 r.2).mpr hgood

private def exists_decidable_counterexample_assembly_c_seq (Lof : ℕ → List (List Bool)) : ℕ →
    ℕ :=
  fun i => Nat.rec 0 (fun _ ci => ci + 1 + ((Lof ci).map (List.length)).sum) i

private def exists_decidable_counterexample_assembly_F_set (Lof : ℕ → List (List Bool)) : Set
    (List Bool) :=
  ⋃ i, {x | x ∈ Lof (exists_decidable_counterexample_assembly_c_seq Lof i)}

/-- Step 1 of the proof of `exists_decidable_counterexample_assembly`: c_seq. -/
private lemma exists_decidable_counterexample_c_seq
    (Lof : ℕ → List (List Bool)) :
    StrictMono (exists_decidable_counterexample_assembly_c_seq Lof) ∧
    (∀ i, i ≤ exists_decidable_counterexample_assembly_c_seq Lof i) ∧
      ∀ i, ∀ y ∈ Lof (exists_decidable_counterexample_assembly_c_seq Lof i),
        y.length < exists_decidable_counterexample_assembly_c_seq Lof (i + 1) := by
  let c_seq := exists_decidable_counterexample_assembly_c_seq Lof
  have h_mono : StrictMono c_seq := by
    apply strictMono_nat_of_lt_succ
    intro i
    change c_seq i < c_seq i + 1 + ((Lof (c_seq i)).map (List.length)).sum
    omega
  refine ⟨h_mono, StrictMono.id_le h_mono, ?_⟩
  intro i y hy
  change y.length < c_seq i + 1 + ((Lof (c_seq i)).map (List.length)).sum
  have h_le : y.length ≤ ((Lof (c_seq i)).map (List.length)).sum := by
    have h_mem : y.length ∈ (Lof (c_seq i)).map (List.length) := List.mem_map_of_mem (f :=
        List.length) hy
    exact List.single_le_sum (fun _ _ => by omega) _ h_mem
  omega

/-- Step 2 of the proof of `exists_decidable_counterexample_assembly`:
Decidability. -/
private lemma exists_decidable_counterexample_decidable
    (Lof : ℕ → List (List Bool))
    (hLof : Computable Lof) (h_le : ∀ i, i ≤ exists_decidable_counterexample_assembly_c_seq
        Lof i)
    (h_Good_c : ∀ c, ∀ y ∈ Lof c, c ≤ y.length) :
    ComputablePred (· ∈ exists_decidable_counterexample_assembly_F_set Lof) := by
  have hsum : Computable (fun c : ℕ => ((Lof c).map List.length).sum) := by
    have h1 : Computable (fun c : ℕ => (Lof c).map List.length) :=
      Computable.list_map hLof (Primrec.list_length.to_comp.comp Computable.snd).to₂
    have hadd : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) => p.1 + p.2) :=
      (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)).to₂
    refine (Computable.list_foldr h1 (Computable.const 0) hadd).of_eq ?_
    intro c
    induction (Lof c).map List.length with
    | nil => rfl
    | cons a l ih => simp [List.foldr_cons, ih]
  have hc : Computable (exists_decidable_counterexample_assembly_c_seq Lof) := by
    unfold exists_decidable_counterexample_assembly_c_seq
    exact Computable.nat_rec (f := fun i : ℕ => i) (g := fun _ : ℕ => (0 : ℕ))
      (h := fun (_ : ℕ) (p : ℕ × ℕ) => p.2 + 1 + ((Lof p.2).map List.length).sum)
      Computable.id (Computable.const 0)
      (Primrec.nat_add.to_comp.comp
        (Computable.succ.comp (Computable.snd.comp Computable.snd))
        (hsum.comp (Computable.snd.comp Computable.snd))).to₂
  have hmem : Computable (fun p : List Bool × ℕ =>
      decide (p.1 ∈ Lof (exists_decidable_counterexample_assembly_c_seq Lof p.2))) := by
    have h := Computable₂.comp (listMemDecide_primrec (β := List Bool)).to_comp
      (Computable.fst : Computable fun p : List Bool × ℕ => p.1)
      (hLof.comp (hc.comp Computable.snd))
    exact h.of_eq fun p => by simp
  have hany : Computable (fun x : List Bool =>
      (List.range (x.length + 1)).foldr
        (fun i acc => decide (x ∈ Lof (exists_decidable_counterexample_assembly_c_seq Lof i))
            || acc)
        false) := by
    have hl : Computable (fun x : List Bool => List.range (x.length + 1)) :=
      Primrec.list_range.to_comp.comp (Computable.succ.comp Primrec.list_length.to_comp)
    have hh : Computable₂ (fun (x : List Bool) (p : ℕ × Bool) =>
        decide (x ∈ Lof (exists_decidable_counterexample_assembly_c_seq Lof p.1)) || p.2) :=
      (Primrec.or.to_comp.comp
        (hmem.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd)))
        (Computable.snd.comp Computable.snd)).to₂
    exact Computable.list_foldr hl (Computable.const false) hh
  refine ComputablePred.computable_iff.mpr ⟨_, hany, ?_⟩
  funext x
  apply propext
  have hfold : ∀ (P : ℕ → Prop) [DecidablePred P] (l : List ℕ),
      (l.foldr (fun i acc => decide (P i) || acc) false = true) ↔ ∃ i ∈ l, P i := by
    intro P _ l
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  rw [hfold (fun i => x ∈ Lof (exists_decidable_counterexample_assembly_c_seq Lof i))]
  simp only [exists_decidable_counterexample_assembly_F_set, Set.mem_iUnion,
    Set.mem_ofPred_eq, List.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Nat.lt_succ_of_le ((h_le i).trans (h_Good_c _ x hi)), hi⟩
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi⟩

/-- Step 3 of the proof of `exists_decidable_counterexample_assembly`: Counting. -/
private lemma exists_decidable_counterexample_count (α : ℝ)
    (Lof : ℕ → List (List Bool))
    (h_mono : StrictMono (exists_decidable_counterexample_assembly_c_seq Lof))
    (h_Good_c : ∀ c, ∀ y ∈ Lof c, c ≤ y.length)
    (h_Good_len : ∀ i, ∀ y ∈ Lof (exists_decidable_counterexample_assembly_c_seq Lof i),
      y.length < exists_decidable_counterexample_assembly_c_seq Lof (i + 1))
    (h_Good_card : ∀ c n, (((Lof c).toFinset.filter (·.length = n)).card : ℝ) < (2 : ℝ) ^ (α * n)) :
    Kolmogorov.Applications.IsLessForbidden α (exists_decidable_counterexample_assembly_F_set
        Lof) := by
  intro n
  let c_seq := exists_decidable_counterexample_assembly_c_seq Lof
  have Hcard : ∀ c, (({x | x ∈ Lof c ∧ x.length = n} : Set (List Bool)).ncard : ℝ) < (2 : ℝ) ^ (α *
      n) := by
    intro c
    have Hc : ({x | x ∈ Lof c ∧ x.length = n} : Set (List Bool)) = (Lof c).toFinset.filter (·.length
        = n) := by
      ext x
      simp only [Set.mem_ofPred_eq, List.mem_toFinset, Finset.mem_filter, Finset.mem_coe]
    rw [Hc, Set.ncard_coe_finset]
    exact h_Good_card c n
  let F_n := {x ∈ exists_decidable_counterexample_assembly_F_set Lof | x.length = n}
  
  rcases Set.eq_empty_or_nonempty F_n with hE | hNE
  · have H0 : (F_n.ncard : ℝ) = 0 := by rw [hE, Set.ncard_empty, Nat.cast_zero]
    have H_pos : (0 : ℝ) < 2 ^ (α * n) := by positivity
    calc (F_n.ncard : ℝ) = 0 := H0
      _ < 2 ^ (α * n) := H_pos
  · obtain ⟨x0, hx0_mem, hx0_len⟩ := hNE
    have hx0_mem' : x0 ∈ exists_decidable_counterexample_assembly_F_set Lof := hx0_mem
    simp only [exists_decidable_counterexample_assembly_F_set, Set.mem_iUnion,
        Set.mem_ofPred_eq] at hx0_mem'
    obtain ⟨i0, hi0⟩ := hx0_mem'
    have Hsubset : F_n ⊆ {x | x ∈ Lof (c_seq i0) ∧ x.length = n} := by
      intro x hx
      obtain ⟨hx_mem, hx_len⟩ := hx
      simp only [exists_decidable_counterexample_assembly_F_set, Set.mem_iUnion,
          Set.mem_ofPred_eq] at hx_mem
      obtain ⟨i, hi⟩ := hx_mem
      have h1 : c_seq i ≤ n := by
        have : c_seq i ≤ x.length := h_Good_c (c_seq i) x hi
        omega
      have h2 : n < c_seq (i + 1) := by
        have : x.length < c_seq (i + 1) := h_Good_len i x hi
        omega
      have h3 : c_seq i0 ≤ n := by
        have : c_seq i0 ≤ x0.length := h_Good_c (c_seq i0) x0 hi0
        omega
      have h4 : n < c_seq (i0 + 1) := by
        have : x0.length < c_seq (i0 + 1) := h_Good_len i0 x0 hi0
        omega
      have H_eq : i = i0 := by
        rcases lt_trichotomy i i0 with hl | he | hr
        · have : c_seq (i + 1) ≤ c_seq i0 := h_mono.monotone hl
          omega
        · exact he
        · have : c_seq (i0 + 1) ≤ c_seq i := h_mono.monotone hr
          omega
      subst H_eq
      exact ⟨hi, hx_len⟩
    
    have Hc : ({x | x ∈ Lof (c_seq i0) ∧ x.length = n} : Set (List Bool)) = (Lof (c_seq
        i0)).toFinset.filter (·.length = n) := by
      ext x
      simp only [Set.mem_ofPred_eq, List.mem_toFinset, Finset.mem_filter, Finset.mem_coe]
    
    have Hfin : ({x | x ∈ Lof (c_seq i0) ∧ x.length = n} : Set (List Bool)).Finite := by
      rw [Hc]
      exact Finset.finite_toSet _
    have Hle : F_n.ncard ≤ {x | x ∈ Lof (c_seq i0) ∧ x.length = n}.ncard := by
      apply Set.ncard_le_ncard Hsubset Hfin
    have Hle' : (F_n.ncard : ℝ) ≤ ({x | x ∈ Lof (c_seq i0) ∧ x.length = n}.ncard : ℝ) := by
        exact_mod_cast Hle
    calc (F_n.ncard : ℝ) ≤ ({x | x ∈ Lof (c_seq i0) ∧ x.length = n}.ncard : ℝ) := Hle'
      _ < 2 ^ (α * n) := Hcard (c_seq i0)

/-- Step 4 of the proof of `exists_decidable_counterexample_assembly`: No avoiding
sequence. -/
private lemma exists_decidable_counterexample_avoids
    (Lof : ℕ → List (List Bool))
    (h_le : ∀ i, i ≤ exists_decidable_counterexample_assembly_c_seq Lof i)
    (h_Good_c : ∀ c, ∀ y ∈ Lof c, c ≤ y.length)
    (h_Good_Occurs : ∀ c, ∃ N, c ≤ N ∧ ∀ w : List Bool, w.length = N → ∃ u ∈ (Lof c).toFinset, u
        <:+: w) :
    ¬ ∃ c w, Kolmogorov.Applications.AvoidsLong
        (exists_decidable_counterexample_assembly_F_set Lof) c w := by
  rintro ⟨k, w, hw⟩
  let c_k := exists_decidable_counterexample_assembly_c_seq Lof k
  obtain ⟨N, _hN_ge, hN_occur⟩ := h_Good_Occurs c_k
  let w_prefix := seqFactor w 0 N
  have hw_len : w_prefix.length = N := length_seqFactor w 0 N
  obtain ⟨u, hu_in, hu_infix⟩ := hN_occur w_prefix hw_len
  have hu_occurs : OccursIn u w := occursIn_of_infix hu_infix
  have hu_len_ge : c_k ≤ u.length := by
    apply h_Good_c
    exact List.mem_toFinset.mp hu_in
  have hu_in_F : u ∈ exists_decidable_counterexample_assembly_F_set Lof := by
    simp only [exists_decidable_counterexample_assembly_F_set, Set.mem_iUnion,
        Set.mem_ofPred_eq]
    use k
    exact List.mem_toFinset.mp hu_in
  have hk_le : k ≤ c_k := h_le k
  have h_len_ge_k : k ≤ u.length := le_trans hk_le hu_len_ge
  exact hw u hu_in_F h_len_ge_k hu_occurs

/-- Step 2b of the proof: Assembly for an arbitrary real `α`. -/
private lemma exists_decidable_counterexample_assembly (α : ℝ)
    (Lof : ℕ → List (List Bool)) (hLof : Computable Lof)
    (hGood : ∀ c, ∃ N, c ≤ N ∧
      exists_decidable_counterexample_GoodFinset α c N (Lof c).toFinset) :
    ∃ F' : Set (List Bool), ComputablePred (· ∈ F') ∧ IsLessForbidden α F' ∧
      ¬ ∃ c w, AvoidsLong F' c w := by
  use exists_decidable_counterexample_assembly_F_set Lof
  have h1 := exists_decidable_counterexample_c_seq Lof
  have h_Good_c : ∀ c, ∀ y ∈ Lof c, c ≤ y.length := by
    intro c y hy
    obtain ⟨N, _, hG⟩ := hGood c
    apply hG.1 y
    simp only [List.mem_toFinset]
    exact hy
  have h_Good_card : ∀ c n, (((Lof c).toFinset.filter (·.length = n)).card : ℝ) < (2 : ℝ) ^ (α * n)
      := by
    intro c n
    obtain ⟨N, _, hG⟩ := hGood c
    exact hG.2.1 n
  have h_Good_Occurs : ∀ c, ∃ N, c ≤ N ∧ ∀ w : List Bool, w.length = N → ∃ u ∈ (Lof c).toFinset, u
      <:+: w := by
    intro c
    obtain ⟨N, hN, hG⟩ := hGood c
    exact ⟨N, hN, hG.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · exact exists_decidable_counterexample_decidable Lof hLof h1.2.1 h_Good_c
  · exact exists_decidable_counterexample_count α Lof h1.1 h_Good_c h1.2.2
      h_Good_card
  · exact exists_decidable_counterexample_avoids Lof h1.2.1 h_Good_c
      h_Good_Occurs

/-- **SUV Theorem 159, p. 243.**  If for some rational `α` and some set `F` the statement of
Theorem 157 fails, then it fails for a decidable set.  The set `F` is required to satisfy the strict
bound of the theorem, and the new set satisfies the same bound. -/
theorem exists_decidable_counterexample {α : ℚ} (hα0 : 0 < α) (_hα1 : α < 1) {F : Set (List Bool)}
    (hF : IsLessForbidden α F) (hfail : ¬ ∃ c w, AvoidsLong F c w) :
    ∃ F' : Set (List Bool), ComputablePred (· ∈ F') ∧ IsLessForbidden α F' ∧
      ¬ ∃ c w, AvoidsLong F' c w := by
  have h1 := exists_decidable_counterexample_exists_good α F hF hfail
  have h2 := exists_decidable_counterexample_step2a3_search α hα0 h1
  obtain ⟨Lof, hLof, hGood⟩ := h2
  exact exists_decidable_counterexample_assembly α Lof hLof hGood

/-- A string occurs in a bi-infinite sequence. -/
def OccursInBi (u : List Bool) (z : ℤ → Bool) : Prop :=
  ∃ i : ℤ, ∀ j : Fin u.length, z (i + (j : ℕ)) = u[j]

/-- **SUV Problem 247, p. 243.**  If some one-sided infinite sequence has no substring from `F`,
then some bidirectional sequence has none: the shifts of the sequence have a limit point in the
compact space of bidirectional sequences. -/
theorem exists_biinfinite_avoiding (F : Set (List Bool))
    (h : ∃ w, ∀ u ∈ F, ¬ OccursIn u w) : ∃ z, ∀ u ∈ F, ¬ OccursInBi u z := by
  obtain ⟨w, hw⟩ := h
  -- The bidirectional sequences with no substring of `F` inside the window `[-n, n]`.
  let C : ℕ → Set (ℤ → Bool) := fun n => {z | ∀ u ∈ F, ∀ i : ℤ,
    -(n : ℤ) ≤ i → i + u.length ≤ n → ¬ ∀ j : Fin u.length, z (i + (j : ℕ)) = u[j]}
  have hclosed : ∀ n, IsClosed (C n) := by
    intro n
    simp only [C, Set.ofPred_forall]
    refine isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_iInter fun i =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    have hopen : IsOpen {z : ℤ → Bool | ∀ j : Fin u.length, z (i + (j : ℕ)) = u[j]} := by
      simp only [Set.ofPred_forall]
      refine isOpen_iInter_of_finite fun j => ?_
      have hc : Continuous fun z : ℤ → Bool => z (i + ((j : ℕ) : ℤ)) := continuous_apply _
      exact hc.isOpen_preimage _ (isOpen_discrete ({u[j]} : Set Bool))
    exact hopen.isClosed_compl
  have hanti : ∀ n, C (n + 1) ⊆ C n := by
    intro n z hz u hu i h1 h2
    refine hz u hu i ?_ ?_ <;> push_cast <;> omega
  have hne : ∀ n, (C n).Nonempty := by
    intro n
    -- The sequence `w`, shifted so that its start is at `-n`.
    refine ⟨fun i => w (i + n).toNat, fun u hu i h1 h2 hmatch => hw u hu ?_⟩
    refine ⟨(i + n).toNat, List.ext_getElem (by simp [seqFactor]) fun j hj hj' => ?_⟩
    have hj'' : j < u.length := hj'
    have := hmatch ⟨j, hj''⟩
    simp only [seqFactor, List.getElem_ofFn]
    rw [show (i + n).toNat + j = (i + ((j : ℕ) : ℤ) + n).toNat by omega]
    exact this
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hanti hne
    (hclosed 0).isCompact hclosed
  refine ⟨z, fun u hu ⟨i, hi⟩ => ?_⟩
  have hmem := Set.mem_iInter.mp hz (i.toNat + (-i).toNat + u.length)
  refine hmem u hu i ?_ ?_ hi <;> omega

end Kolmogorov.Applications
