/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.AlphabetComplexity

/-!
# Complexity inside an enumerable family of controlled growth

`plainK_le_log_card_of_isEnumerableFamily_of_growth`: if the sets `A i` of an enumerable
family have sizes bounded by a computable, strictly increasing `f` of controlled
multiplicative growth, then every member of `A i` has complexity at most
`log |A i| + O(log i)` — it is named by its index in the enumeration.

`enumFound` and `enumAccum` are the stage-wise enumeration and its accumulation, which is
duplicate-free, only grows, and is a prefix of every later stage
(`enum_accum_nodup`, `enum_accum_prefix`, `enum_accum_getElem`), so an index identifies a
string independently of the stage.  `growthDecompressor` reads that index, partial computably,
and `growth_sum_le` is the growth estimate that keeps the index short.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- A function of controlled multiplicative growth dominates the sum of its earlier values
up to a constant factor. -/
lemma growth_sum_le (f : ℕ → ℕ) (hmono : StrictMono f)
    (r : ℝ) (hr : 1 < r) (N : ℕ) (hgrowth : ∀ n, N ≤ n → r * (f n : ℝ) ≤ (f (n + 1) : ℝ)) :
    ∃ K : ℕ, ∀ n : ℕ, ((List.range (n + 1)).map f).sum ≤ K * f n := by
  have hf_ge (n : ℕ) : n ≤ f n := hmono.id_le n
  set S : ℕ → ℕ := fun n => ((List.range (n + 1)).map f).sum
  have hS_succ (n : ℕ) : S (n + 1) = S n + f (n + 1) := by
    dsimp [S]
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  have hS_mono : Monotone S := by
    intro a b hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      change S a ≤ S (a + d + 1)
      rw [hS_succ (a + d)]
      omega
  obtain ⟨C, hC⟩ : ∃ C : ℕ, (1 / (r - 1) : ℝ) ≤ (C : ℝ) := exists_nat_ge (1 / (r - 1))
  have hr_sub : 0 < r - 1 := sub_pos.mpr hr
  have h_step (n : ℕ) (hn : N ≤ n) : (f n : ℝ) ≤ (C : ℝ) * ((f (n + 1) : ℝ) - (f n : ℝ)) := by
    have hg := hgrowth n hn
    have h1 : (r - 1) * (f n : ℝ) ≤ (f (n + 1) : ℝ) - (f n : ℝ) := by linarith
    have h2 : (f n : ℝ) ≤ (1 / (r - 1)) * ((f (n + 1) : ℝ) - (f n : ℝ)) := by
      rw [one_div]
      exact (le_inv_mul_iff₀ hr_sub).mpr h1
    have h3 : 0 ≤ (f (n + 1) : ℝ) - (f n : ℝ) := by
      have hlt : f n < f (n + 1) := hmono (Nat.lt_succ_self n)
      exact sub_nonneg.mpr (by exact_mod_cast le_of_lt hlt)
    nlinarith
  have h_sum_tail (n : ℕ) (hn : N ≤ n) :
      (S n : ℝ) ≤ (S N : ℝ) + (C : ℝ) * ((f n : ℝ) - (f N : ℝ)) + (f n : ℝ) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction d with
    | zero =>
      simp only [add_zero, sub_self, mul_zero]
      have : 0 ≤ (f N : ℝ) := by positivity
      linarith
    | succ d ih =>
      have ih_app := ih (Nat.le_add_right N d)
      have hstep_k := h_step (N + d) (Nat.le_add_right N d)
      change (S (N + d + 1) : ℝ) ≤
        (S N : ℝ) + (C : ℝ) * ((f (N + d + 1) : ℝ) - (f N : ℝ)) + (f (N + d + 1) : ℝ)
      rw [hS_succ (N + d), Nat.cast_add]
      linarith
  set K := S N + C + 1
  use K
  intro n
  by_cases hfn : f n = 0
  · have hn0 : n = 0 := by
      by_contra hneq
      have hpos : 0 < n := Nat.pos_of_ne_zero hneq
      have : 0 < f n := lt_of_lt_of_le hpos (hf_ge n)
      omega
    subst hn0
    dsimp [S]
    rw [hfn, mul_zero]
    simp [hfn]
  · have hfn1 : 1 ≤ f n := Nat.one_le_iff_ne_zero.mpr hfn
    by_cases hn : n < N
    · have hSn : S n ≤ S N := hS_mono (le_of_lt hn)
      have hK1 : S N ≤ K * f n := by
        calc S N ≤ K * 1 := by dsimp [K]; omega
        _ ≤ K * f n := Nat.mul_le_mul_left K hfn1
      exact le_trans hSn hK1
    · push Not at hn
      have htail := h_sum_tail n hn
      have h_sum_real : (S n : ℝ) ≤ (K : ℝ) * (f n : ℝ) := by
        calc (S n : ℝ) ≤ (S N : ℝ) + (C : ℝ) * ((f n : ℝ) - (f N : ℝ)) + (f n : ℝ) := htail
        _ ≤ (S N : ℝ) * (f n : ℝ) + (C : ℝ) * (f n : ℝ) + 1 * (f n : ℝ) := by
          have : (1 : ℝ) ≤ (f n : ℝ) := by exact_mod_cast hfn1
          have : 0 ≤ (S N : ℝ) := by positivity
          have : 0 ≤ (f N : ℝ) := by positivity
          nlinarith
        _ = ((S N : ℝ) + (C : ℝ) + 1) * (f n : ℝ) := by ring
        _ = (K : ℝ) * (f n : ℝ) := by dsimp [K]; push_cast; ring
      exact_mod_cast h_sum_real

/-- The programs of length at most `S` accepted by the code `c` for the parameter `i`
within `S` steps. -/
def enumFound (c : Code) (i S : ℕ) : List BitString :=
  (boundedPrograms S).filter (fun z =>
    (Nat.Partrec.Code.evaln S c (Encodable.encode (i, z))).isSome)

/-- The strings accumulated by the stage-wise enumeration up to stage `S`, in the order in
which they were found. -/
def enumAccum (c : Code) (i : ℕ) : ℕ → List BitString
  | 0 => enumFound c i 0
  | S + 1 => enumAccum c i S ++
      (enumFound c i (S + 1)).filter (fun z => !(decide (z ∈ enumAccum c i S)))

/-- The accumulated enumeration lists no string twice. -/
lemma enum_accum_nodup (c : Code) (i S : ℕ) : (enumAccum c i S).Nodup := by
  induction S with
  | zero =>
    dsimp [enumAccum, enumFound]
    exact (boundedPrograms_nodup 0).filter _
  | succ S ih =>
    dsimp [enumAccum]
    apply List.Nodup.append ih
    · exact ((boundedPrograms_nodup (S + 1)).filter _).filter _
    · intro z hz1 hz2
      rw [List.mem_filter] at hz2
      have hnot : z ∉ enumAccum c i S := by
        have hdec := hz2.2
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hdec
        exact hdec
      exact hnot hz1

/-- The accumulated enumeration only grows with the stage. -/
lemma enum_accum_length_le (c : Code) (i S d : ℕ) :
    (enumAccum c i S).length ≤ (enumAccum c i (S + d)).length := by
  induction d with
  | zero => rw [add_zero]
  | succ d ih =>
    have h1 : enumAccum c i (S + d + 1) = enumAccum c i (S + d) ++
        (enumFound c i (S + d + 1)).filter
          (fun z => !(decide (z ∈ enumAccum c i (S + d)))) := rfl
    have h2 : S + (d + 1) = S + d + 1 := by omega
    rw [h2, h1, List.length_append]
    omega

/-- The accumulated enumeration at a stage is a prefix of every later one. -/
lemma enum_accum_prefix (c : Code) (i S d : ℕ) :
    (enumAccum c i (S + d)).take (enumAccum c i S).length = enumAccum c i S := by
  induction d with
  | zero => rw [add_zero, List.take_length]
  | succ d ih =>
    have h1 : enumAccum c i (S + d + 1) = enumAccum c i (S + d) ++
        (enumFound c i (S + d + 1)).filter
          (fun z => !(decide (z ∈ enumAccum c i (S + d)))) := rfl
    have h2 : S + (d + 1) = S + d + 1 := by omega
    rw [h2, h1]
    rw [List.take_append_of_le_length (enum_accum_length_le c i S d)]
    exact ih

/-- An entry of the accumulated enumeration does not depend on the stage at which it is
read. -/
lemma enum_accum_getElem (c : Code) (i k S S' : ℕ) (h1 : k < (enumAccum c i S).length)
    (h2 : k < (enumAccum c i S').length) :
    (enumAccum c i S)[k] = (enumAccum c i S')[k] := by
  wlog hle : S ≤ S'
  · exact (this c i k S' S h2 h1 (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hprefix := enum_accum_prefix c i S d
  have h_lt : k < ((enumAccum c i (S + d)).take (enumAccum c i S).length).length := by
    rw [hprefix]; exact h1
  have h_elem : ((enumAccum c i (S + d)).take (enumAccum c i S).length)[k]'h_lt =
      (enumAccum c i S)[k] :=
    List.getElem_of_eq hprefix h_lt
  have h_take : ((enumAccum c i (S + d)).take (enumAccum c i S).length)[k]'h_lt =
      (enumAccum c i (S + d))[k] :=
    List.getElem_take
  exact h_elem.symm.trans h_take

/-- Every string accumulated for the parameter `i` belongs to the `i`-th set of the family. -/
lemma enum_accum_mem_A {A : ℕ → Set BitString} {cA : Code}
    (hcA : ∀ (p : ℕ × BitString), (cA.eval (Encodable.encode p)).Dom ↔ p.2 ∈ A p.1)
    (i S : ℕ) (x : BitString) (hx : x ∈ enumAccum cA i S) : x ∈ A i := by
  induction S with
  | zero =>
    dsimp [enumAccum, enumFound] at hx
    rw [List.mem_filter] at hx
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hx.2
    have h_eval := Nat.Partrec.Code.evaln_sound hr
    have h_dom : (cA.eval (Encodable.encode (i, x))).Dom := Part.dom_iff_mem.mpr ⟨r, h_eval⟩
    exact (hcA (i, x)).mp h_dom
  | succ S ih =>
    dsimp [enumAccum] at hx
    rw [List.mem_append] at hx
    rcases hx with h1 | h2
    · exact ih h1
    · rw [List.mem_filter] at h2
      dsimp [enumFound] at h2
      rw [List.mem_filter] at h2
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h2.1.2
      have h_eval := Nat.Partrec.Code.evaln_sound hr
      have h_dom : (cA.eval (Encodable.encode (i, x))).Dom := Part.dom_iff_mem.mpr ⟨r, h_eval⟩
      exact (hcA (i, x)).mp h_dom

/-- The accumulated enumeration of the `i`-th set is no longer than that set. -/
lemma enum_accum_length_le_ncard {A : ℕ → Set BitString} (hfin : ∀ n, (A n).Finite)
    {cA : Code} (hcA : ∀ (p : ℕ × BitString), (cA.eval (Encodable.encode p)).Dom ↔ p.2 ∈ A p.1)
    (i S : ℕ) : (enumAccum cA i S).length ≤ (A i).ncard := by
  have hnodup := enum_accum_nodup cA i S
  have hsub : (enumAccum cA i S).toFinset ⊆ (hfin i).toFinset := by
    intro y hy
    rw [List.mem_toFinset] at hy
    have hyA : y ∈ A i := enum_accum_mem_A hcA i S y hy
    exact (hfin i).mem_toFinset.mpr hyA
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnodup] at hcard
  rw [Set.ncard_eq_toFinset_card (A i) (hfin i)]
  exact hcard

/-- The unbounded search returns the least witness of a decidable predicate. -/
lemma rfind_eq_of_spec {P : ℕ → Bool} (n : ℕ) (hn : P n = true) (hmin : ∀ i < n, P i = false) :
    Nat.rfind (fun i => Part.some (P i)) = Part.some n := by
  apply Part.eq_some_iff.mpr
  refine Nat.mem_rfind.mpr ?_
  refine ⟨by simp [hn], fun {m} hm => ?_⟩
  simp [hmin m hm]

/-- The decompressor of the growth exercise: it reads the index of a string in the
enumeration of a member of the family and returns that string. -/
def growthDecompressor (f : ℕ → ℕ) (cA : Code) (pr : BitString × BitString) : Part BitString :=
  let p := pr.1
  let L := p.length
  let m := (exactLengthPrograms L).idxOf p
  (Nat.rfind (fun i => Part.some (decide (m < ((List.range (i + 1)).map f).sum)))).bind fun i =>
    let W_i := ((List.range i).map f).sum
    let k := m - W_i
    (Nat.rfind (fun S => Part.some (decide (k < (enumAccum cA i S).length)))).bind fun S =>
      Part.ofOption ((enumAccum cA i S)[k]?)

/-- A string found at stage `S` belongs to the enumeration accumulated by that stage. -/
lemma mem_enum_accum_of_mem_found (c : Code) (i S : ℕ) (x : BitString)
    (hx : x ∈ enumFound c i S) : x ∈ enumAccum c i S := by
  induction S with
  | zero => exact hx
  | succ S ih =>
    dsimp [enumAccum]
    rw [List.mem_append]
    by_cases h_prev : x ∈ enumAccum c i S
    · exact Or.inl h_prev
    · right
      rw [List.mem_filter]
      refine ⟨hx, ?_⟩
      simp [h_prev]

private lemma decide_mem_primrec_BS :
    Primrec (fun (p : List BitString × BitString) => decide (p.2 ∈ p.1)) := by
  have h_fold : Primrec (fun (p : List BitString × BitString) =>
      p.1.foldr (fun x acc => (p.2 == x) || acc) false) := by
    have hf : Primrec (fun (p : List BitString × BitString) => p.1) := Primrec.fst
    have hg : Primrec (fun (_ : List BitString × BitString) => false) := Primrec.const false
    have h_eq : Primrec (fun (q : (List BitString × BitString) × BitString × Bool) =>
        decide (q.1.2 = q.2.1)) :=
      (PrimrecPred.decide (PrimrecRel.comp Primrec.eq (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)))
    have hh : Primrec (fun (q : (List BitString × BitString) × BitString × Bool) =>
        (q.1.2 == q.2.1) || q.2.2) :=
      Primrec.or.comp (h_eq.of_eq (by intro _; simp [Bool.beq_eq_decide_eq]))
        (Primrec.snd.comp Primrec.snd)
    exact Primrec.list_foldr hf hg hh.to₂
  have h_eq (p : List BitString × BitString) :
      p.1.foldr (fun x acc => (p.2 == x) || acc) false = decide (p.2 ∈ p.1) := by
    induction p.1 with
    | nil => rfl
    | cons a t ih =>
      dsimp [List.foldr]
      rw [ih]
      simp [Bool.beq_eq_decide_eq]
  exact h_fold.of_eq h_eq

/-- The strings found at a stage are primitive recursive in the parameter and the stage. -/
lemma enum_found_primrec (cA : Code) : Primrec₂ (enumFound cA) := by
  change Primrec₂ (fun i S => (boundedPrograms S).filter (fun z =>
      (Code.evaln S cA (Encodable.encode (i, z))).isSome))
  have h1 : Primrec (fun p : ℕ × ℕ => boundedPrograms p.2) :=
    primrec_boundedPrograms.comp Primrec.snd
  have h2 : Primrec₂ (fun (p : ℕ × ℕ) (z : BitString) =>
      (Code.evaln p.2 cA (Encodable.encode (p.1, z))).isSome) := by
    have h_eval : Primrec (fun q : (ℕ × ℕ) × BitString =>
        Code.evaln q.1.2 cA (Encodable.encode (q.1.1, q.2))) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (Primrec.pair
          (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.const cA))
          (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)))
    exact (Primrec.option_isSome.comp h_eval).to₂
  exact list_filter_primrec h1 h2

private lemma enum_accum_step_primrec (cA : Code) :
    Primrec (fun (r : (ℕ × ℕ) × ℕ × List BitString) =>
      r.2.2 ++ (enumFound cA r.1.1 (r.2.1 + 1)).filter (fun z => !(decide (z ∈ r.2.2)))) := by
  have h_found := enum_found_primrec cA
  have h_found_next : Primrec (fun (r : (ℕ × ℕ) × ℕ × List BitString) =>
      enumFound cA r.1.1 (r.2.1 + 1)) :=
    h_found.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  have h_filt : Primrec (fun (r : (ℕ × ℕ) × ℕ × List BitString) =>
      (enumFound cA r.1.1 (r.2.1 + 1)).filter (fun z => !(decide (z ∈ r.2.2)))) := by
    have h_pred : Primrec₂ (fun (r : (ℕ × ℕ) × ℕ × List BitString) (z : BitString) =>
        !(decide (z ∈ r.2.2))) := by
      have h_mem : Primrec (fun q : ((ℕ × ℕ) × ℕ × List BitString) × BitString =>
          decide (q.2 ∈ q.1.2.2)) :=
        decide_mem_primrec_BS.comp
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
      exact (Primrec.not.comp h_mem).to₂
    exact list_filter_primrec h_found_next h_pred
  exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd) h_filt

/-- The accumulated enumeration is primitive recursive in the parameter and the stage. -/
lemma enum_accum_primrec (cA : Code) : Primrec₂ (enumAccum cA) := by
  have h_found := enum_found_primrec cA
  have h_step := enum_accum_step_primrec cA
  have h_rec := Primrec.nat_rec'
    (hf := Primrec.snd)
    (hg := h_found.comp Primrec.fst (Primrec.const 0))
    (hh := h_step.to₂)
  have h_eq (i S : ℕ) : enumAccum cA i S = Nat.rec (enumFound cA i 0)
      (fun S acc => acc ++ (enumFound cA i (S + 1)).filter
        (fun z => !(decide (z ∈ acc)))) S := by
    induction S with
    | zero => rfl
    | succ S ih =>
      rw [enumAccum, ih]
  exact (h_rec.of_eq (fun p => (h_eq p.1 p.2).symm)).to₂

/-- Summing a computable function over an initial segment is computable. -/
lemma sum_range_computable (f : ℕ → ℕ) (hf : Computable f) :
    Computable (fun i : ℕ => ((List.range i).map f).sum) := by
  have h_f_pair : Computable (fun p : ℕ × ℕ × ℕ => f p.2.1) :=
    @Computable.comp (ℕ × ℕ × ℕ) ℕ ℕ _ _ _ f (fun p => p.2.1) hf
      (Computable.fst.comp Computable.snd)
  have h_add : Computable (fun p : ℕ × ℕ × ℕ => p.2.2 + f p.2.1) :=
    @Computable.comp (ℕ × ℕ × ℕ) (ℕ × ℕ) ℕ _ _ _
      (fun q => q.1 + q.2) (fun p => (p.2.2, f p.2.1))
      Primrec.nat_add.to_comp
      (@Computable.pair (ℕ × ℕ × ℕ) ℕ ℕ _ _ _
        (fun p => p.2.2) (fun p => f p.2.1)
        (Computable.snd.comp Computable.snd) h_f_pair)
  have h_rec := Computable.nat_rec Computable.id (Primrec.const 0).to_comp h_add.to₂
  have h_eq (i : ℕ) : Nat.rec 0 (fun y IH => (i, y, IH).2.2 + f (i, y, IH).2.1) (id i) =
      ((List.range i).map f).sum := by
    change Nat.rec 0 (fun y IH => IH + f y) i = ((List.range i).map f).sum
    induction i with
    | zero => rfl
    | succ i ih =>
      change Nat.rec 0 (fun y IH => IH + f y) i + f i = _
      rw [ih, List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
  exact h_rec.of_eq h_eq

/-- Computing the index of the first string parameter in exactLengthPrograms is computable. -/
private lemma exact_length_idxOf_computable :
    Computable (fun pr : BitString × BitString =>
      (exactLengthPrograms pr.1.length).idxOf pr.1) := by
  have h_elem : Primrec (fun pr : BitString × BitString => pr.1) := Primrec.fst
  have h_list : Primrec (fun pr : BitString × BitString =>
      exactLengthPrograms pr.1.length) :=
    primrec_exactLengthPrograms.comp (Primrec.list_length.comp Primrec.fst)
  have h_pair : Primrec (fun pr : BitString × BitString =>
      (pr.1, exactLengthPrograms pr.1.length)) :=
    h_elem.pair h_list
  exact (Primrec.comp Primrec.list_idxOf h_pair).of_eq
    (by intro pr; dsimp; exact idxOf_eq_idxOf pr.1 _) |>.to_comp

/-- The search step for the index `i` in `growthDecompressor` is partial recursive. -/
private lemma growth_decompressor_rfind1_partrec (f : ℕ → ℕ) (hf : Computable f) :
    Partrec (fun pr : BitString × BitString =>
      Nat.rfind (fun i => Part.some (decide
        ((exactLengthPrograms pr.1.length).idxOf pr.1 <
          ((List.range (i + 1)).map f).sum)))) := by
  have h_sum := sum_range_computable f hf
  have h_idx := exact_length_idxOf_computable
  have h_s : Computable (fun p : (BitString × BitString) × ℕ =>
      ((List.range (p.2 + 1)).map f).sum) :=
    @Computable.comp ((BitString × BitString) × ℕ) ℕ ℕ _ _ _
      (fun i => ((List.range i).map f).sum) (fun p => p.2 + 1)
      h_sum (Computable.succ.comp Computable.snd)
  have h_check1 : Computable₂ (fun (pr : BitString × BitString) (i : ℕ) =>
      decide ((exactLengthPrograms pr.1.length).idxOf pr.1 <
        ((List.range (i + 1)).map f).sum)) :=
    (@Computable.comp ((BitString × BitString) × ℕ) (ℕ × ℕ) Bool _ _ _
      (fun q => decide (q.1 < q.2))
      (fun p => ((exactLengthPrograms p.1.1.length).idxOf p.1.1,
        ((List.range (p.2 + 1)).map f).sum))
      (PrimrecPred.decide Primrec.nat_lt).to_comp
      (@Computable.pair ((BitString × BitString) × ℕ) ℕ ℕ _ _ _
        (fun p => (exactLengthPrograms p.1.1.length).idxOf p.1.1)
        (fun p => ((List.range (p.2 + 1)).map f).sum)
        (h_idx.comp Computable.fst) h_s)).to₂
  exact Partrec.rfind h_check1.partrec₂

/-- The index offset `k` within stage `i` is computable. -/
private lemma growth_decompressor_k_p_computable (f : ℕ → ℕ) (hf : Computable f) :
    Computable (fun p : (BitString × BitString) × ℕ =>
      (exactLengthPrograms p.1.1.length).idxOf p.1.1 - ((List.range p.2).map f).sum) := by
  have h_sum := sum_range_computable f hf
  have h_elem_p : Primrec (fun p : (BitString × BitString) × ℕ => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have h_list_p : Primrec (fun p : (BitString × BitString) × ℕ =>
      exactLengthPrograms p.1.1.length) :=
    primrec_exactLengthPrograms.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
  have h_pair_p : Primrec (fun p : (BitString × BitString) × ℕ =>
      (p.1.1, exactLengthPrograms p.1.1.length)) :=
    h_elem_p.pair h_list_p
  have h1_p : Computable (fun p : (BitString × BitString) × ℕ =>
      (exactLengthPrograms p.1.1.length).idxOf p.1.1) :=
    (Primrec.comp Primrec.list_idxOf h_pair_p).of_eq
      (by intro p; dsimp; exact idxOf_eq_idxOf p.1.1 _) |>.to_comp
  have h2_p : Computable (fun p : (BitString × BitString) × ℕ =>
      ((List.range p.2).map f).sum) :=
    @Computable.comp ((BitString × BitString) × ℕ) ℕ ℕ _ _ _
      (fun i => ((List.range i).map f).sum) (fun p => p.2)
      h_sum Computable.snd
  exact @Computable.comp ((BitString × BitString) × ℕ) (ℕ × ℕ) ℕ _ _ _
    (fun q => q.1 - q.2)
    (fun p => ((exactLengthPrograms p.1.1.length).idxOf p.1.1, ((List.range p.2).map f).sum))
    Primrec.nat_sub.to_comp
    (@Computable.pair ((BitString × BitString) × ℕ) ℕ ℕ _ _ _
      (fun p => (exactLengthPrograms p.1.1.length).idxOf p.1.1)
      (fun p => ((List.range p.2).map f).sum) h1_p h2_p)

/-- Finding the stage `S` at which the target index appears in `enumAccum` is partial recursive. -/
private lemma growth_decompressor_rfind2_partrec (f : ℕ → ℕ) (hf : Computable f) (cA : Code) :
    Partrec (fun p : (BitString × BitString) × ℕ =>
      Nat.rfind (fun S => Part.some (decide (
        (exactLengthPrograms p.1.1.length).idxOf p.1.1 -
        ((List.range p.2).map f).sum < (enumAccum cA p.2 S).length)))) := by
  have h_k_p := growth_decompressor_k_p_computable f hf
  have h_len_q : Computable (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      (enumAccum cA q.1.2 q.2).length) :=
    @Computable.comp (((BitString × BitString) × ℕ) × ℕ) (List BitString) ℕ _ _ _
      List.length (fun q => enumAccum cA q.1.2 q.2)
      Primrec.list_length.to_comp
      (@Computable.comp (((BitString × BitString) × ℕ) × ℕ) (ℕ × ℕ) (List BitString) _ _ _
        (fun p => enumAccum cA p.1 p.2) (fun q => (q.1.2, q.2))
        (enum_accum_primrec cA).to_comp
        (@Computable.pair (((BitString × BitString) × ℕ) × ℕ) ℕ ℕ _ _ _
          (fun q => q.1.2) (fun q => q.2)
          (Computable.snd.comp Computable.fst) Computable.snd))
  have h_check2 : Computable₂ (fun (p : (BitString × BitString) × ℕ) (S : ℕ) =>
      decide ((exactLengthPrograms p.1.1.length).idxOf p.1.1 -
        ((List.range p.2).map f).sum < (enumAccum cA p.2 S).length)) :=
    (@Computable.comp (((BitString × BitString) × ℕ) × ℕ) (ℕ × ℕ) Bool _ _ _
      (fun q => decide (q.1 < q.2))
      (fun q => ((exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1 -
        ((List.range q.1.2).map f).sum, (enumAccum cA q.1.2 q.2).length))
      (PrimrecPred.decide Primrec.nat_lt).to_comp
      (@Computable.pair (((BitString × BitString) × ℕ) × ℕ) ℕ ℕ _ _ _
        (fun q => (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1 -
          ((List.range q.1.2).map f).sum)
        (fun q => (enumAccum cA q.1.2 q.2).length)
        (h_k_p.comp Computable.fst) h_len_q)).to₂
  exact Partrec.rfind h_check2.partrec₂

/-- Fetching the `k`-th string from `enumAccum` after finding stage `S` is partial recursive. -/
private lemma growth_decompressor_get_partrec (f : ℕ → ℕ) (hf : Computable f) (cA : Code) :
    Partrec (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      Part.ofOption ((enumAccum cA q.1.2 q.2)[
        (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1 -
        ((List.range q.1.2).map f).sum]?)) := by
  have h_sum := sum_range_computable f hf
  have h_elem_q : Primrec (fun q : ((BitString × BitString) × ℕ) × ℕ => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have h_list_q : Primrec (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      exactLengthPrograms q.1.1.1.length) :=
    primrec_exactLengthPrograms.comp
      (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have h_pair_q : Primrec (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      (q.1.1.1, exactLengthPrograms q.1.1.1.length)) :=
    h_elem_q.pair h_list_q
  have h1_q : Computable (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1) :=
    (Primrec.comp Primrec.list_idxOf h_pair_q).of_eq
      (by intro q; dsimp; exact idxOf_eq_idxOf q.1.1.1 _) |>.to_comp
  have h2_q : Computable (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      ((List.range q.1.2).map f).sum) :=
    @Computable.comp (((BitString × BitString) × ℕ) × ℕ) ℕ ℕ _ _ _
      (fun i => ((List.range i).map f).sum) (fun q => q.1.2)
      h_sum (Computable.snd.comp Computable.fst)
  have h_k_q : Computable (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1 - ((List.range q.1.2).map f).sum) :=
    @Computable.comp (((BitString × BitString) × ℕ) × ℕ) (ℕ × ℕ) ℕ _ _ _
      (fun q => q.1 - q.2)
      (fun q => ((exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1,
        ((List.range q.1.2).map f).sum))
      Primrec.nat_sub.to_comp
      (@Computable.pair (((BitString × BitString) × ℕ) × ℕ) ℕ ℕ _ _ _
        (fun q => (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1)
        (fun q => ((List.range q.1.2).map f).sum) h1_q h2_q)
  have h_list_acc : Computable (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      enumAccum cA q.1.2 q.2) :=
    @Computable.comp (((BitString × BitString) × ℕ) × ℕ) (ℕ × ℕ) (List BitString) _ _ _
      (fun p => enumAccum cA p.1 p.2) (fun q => (q.1.2, q.2))
      (enum_accum_primrec cA).to_comp
      (@Computable.pair (((BitString × BitString) × ℕ) × ℕ) ℕ ℕ _ _ _
        (fun q => q.1.2) (fun q => q.2)
        (Computable.snd.comp Computable.fst) Computable.snd)
  have h_get_pair : Computable (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      (enumAccum cA q.1.2 q.2,
        (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1 -
        ((List.range q.1.2).map f).sum)) :=
    @Computable.pair (((BitString × BitString) × ℕ) × ℕ) (List BitString) ℕ _ _ _
      (fun q => enumAccum cA q.1.2 q.2)
      (fun q => (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1 -
        ((List.range q.1.2).map f).sum)
      h_list_acc h_k_q
  have h_get_opt : Computable (fun q : ((BitString × BitString) × ℕ) × ℕ =>
      (enumAccum cA q.1.2 q.2)[
        (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1 -
        ((List.range q.1.2).map f).sum]?) :=
    @Computable.comp (((BitString × BitString) × ℕ) × ℕ) (List BitString × ℕ)
      (Option BitString) _ _ _
      (fun p => p.1[p.2]?)
      (fun q => (enumAccum cA q.1.2 q.2,
        (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1 -
        ((List.range q.1.2).map f).sum))
      Computable.list_getElem? h_get_pair
  exact @Computable.ofOption (((BitString × BitString) × ℕ) × ℕ) BitString _ _
    (fun q => (enumAccum cA q.1.2 q.2)[
      (exactLengthPrograms q.1.1.1.length).idxOf q.1.1.1 -
      ((List.range q.1.2).map f).sum]?) h_get_opt

/-- The decompressor of the growth exercise is partial computable. -/
lemma growthDecompressor_partrec (f : ℕ → ℕ) (hf : Computable f) (cA : Code) :
    Partrec (growthDecompressor f cA) := by
  have h_rfind1 := growth_decompressor_rfind1_partrec f hf
  have h_rfind2 := growth_decompressor_rfind2_partrec f hf cA
  have h_get := growth_decompressor_get_partrec f hf cA
  have h_step2 : Partrec (fun p : (BitString × BitString) × ℕ =>
      (Nat.rfind (fun S => Part.some (decide (
        (exactLengthPrograms p.1.1.length).idxOf p.1.1 -
        ((List.range p.2).map f).sum < (enumAccum cA p.2 S).length)))).bind (fun S =>
        Part.ofOption ((enumAccum cA p.2 S)[
          (exactLengthPrograms p.1.1.length).idxOf p.1.1 -
          ((List.range p.2).map f).sum]?))) :=
    Partrec.bind h_rfind2 h_get.to₂
  unfold growthDecompressor
  exact Partrec.bind h_rfind1 h_step2.to₂

/-- For a computable, strictly increasing `f` of controlled multiplicative growth and an
enumerable family whose members have at most `f n` elements, every element of the `n`-th
member has complexity at most `log f n + O(1)`. SUV Exercise 6. -/
theorem plainK_le_log_card_of_isEnumerableFamily_of_growth (U : Map) (hU : isOptimalConditional U)
    (f : ℕ → ℕ) (hf : Computable f) (hmono : StrictMono f)
    (r : ℝ) (hr : 1 < r) (N : ℕ) (hgrowth : ∀ n, N ≤ n → r * (f n : ℝ) ≤ (f (n + 1) : ℝ))
    (A : ℕ → Set BitString) (hA : IsEnumerableFamily A)
    (hfin : ∀ n, (A n).Finite) (hcard : ∀ n, (A n).ncard ≤ f n) :
    ∃ k : ℕ, ∀ (n : ℕ) (x : BitString), x ∈ A n →
      plainK U x ≤ ((Nat.log 2 (f n) + k : ℕ) : ℕ∞) := by
  obtain ⟨K, hK_sum⟩ := growth_sum_le f hmono r hr N hgrowth
  obtain ⟨gA, hgA_partrec, hgA_dom⟩ := hA
  obtain ⟨cA, hcA⟩ := Nat.Partrec.Code.exists_code.mp hgA_partrec
  have hcA_iff (p : ℕ × BitString) : (cA.eval (Encodable.encode p)).Dom ↔ p.2 ∈ A p.1 := by
    have h_eval : cA.eval (Encodable.encode p) = (gA p).map Encodable.encode := by
      rw [hcA]
      dsimp [Part.ofOption]
      rw [Encodable.encodek]
      dsimp
      exact Part.bind_some p (fun a => Part.map Encodable.encode (gA a))
    rw [h_eval]
    dsimp [Part.map]
    exact hgA_dom p
  set K_shift := K + 2
  have hK_shift : K + 1 ≤ 2 ^ K_shift := by
    dsimp [K_shift]
    have h1 : K + 1 ≤ 2 ^ (K + 1) := le_of_lt (Nat.lt_pow_self (n := K + 1) (by decide))
    have h2 : 2 ^ (K + 1) ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    exact h1.trans h2
  have hM_partrec : Partrec (growthDecompressor f cA) := growthDecompressor_partrec f hf cA
  obtain ⟨c_M, hc_M⟩ := hU.2 (growthDecompressor f cA) hM_partrec
  use K_shift + 1 + c_M
  intro n x hxA
  have h_dom : (cA.eval (Encodable.encode (n, x))).Dom := (hcA_iff (n, x)).mpr hxA
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp h_dom
  obtain ⟨S0, hS0⟩ := Nat.Partrec.Code.evaln_complete.mp hy
  set S1 := max S0 x.length
  have hS1_eval : (Nat.Partrec.Code.evaln S1 cA (Encodable.encode (n, x))).isSome = true := by
    have h_mono := Nat.Partrec.Code.evaln_mono (le_max_left S0 x.length) hS0
    exact Option.isSome_iff_exists.mpr ⟨y, h_mono⟩
  have h_mem_bounded : x ∈ boundedPrograms S1 := by
    rw [mem_boundedPrograms_iff]
    exact le_max_right S0 x.length
  have h_found : x ∈ enumFound cA n S1 := by
    dsimp [enumFound]
    rw [List.mem_filter]
    exact ⟨h_mem_bounded, hS1_eval⟩
  have h_accum : x ∈ enumAccum cA n S1 := mem_enum_accum_of_mem_found cA n S1 x h_found
  set k_x := (enumAccum cA n S1).idxOf x
  have hk_x_lt : k_x < (enumAccum cA n S1).length := List.idxOf_lt_length_iff.mpr h_accum
  have hk_x_fn : k_x < f n := by
    have h_le := enum_accum_length_le_ncard hfin hcA_iff n S1
    have h_card := hcard n
    omega
  set W_n := ((List.range n).map f).sum
  set m := W_n + k_x
  have h_m_lt : m < ((List.range (n + 1)).map f).sum := by
    dsimp [m, W_n]
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    omega
  have h_m_K : m < K * f n := lt_of_lt_of_le h_m_lt (hK_sum n)
  set L := Nat.log 2 (f n) + K_shift + 1
  have h_mL : m < 2 ^ L := by
    by_cases hfn : f n = 0
    · omega
    · have hfn1 : 1 ≤ f n := Nat.one_le_iff_ne_zero.mpr hfn
      have h1 : f n < 2 ^ (Nat.log 2 (f n) + 1) := Nat.lt_pow_succ_log_self (by decide) (f n)
      have h2 : K * f n < 2 ^ K_shift * 2 ^ (Nat.log 2 (f n) + 1) := by
        calc K * f n < (K + 1) * f n := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self K) (by omega)
        _ ≤ 2 ^ K_shift * 2 ^ (Nat.log 2 (f n) + 1) := Nat.mul_le_mul hK_shift (le_of_lt h1)
      have h3 : 2 ^ K_shift * 2 ^ (Nat.log 2 (f n) + 1) = 2 ^ L := by
        dsimp [L]
        rw [← pow_add]
        congr 1
        omega
      rw [h3] at h2
      omega
  have h_exact_len : (exactLengthPrograms L).length = 2 ^ L := length_exactLengthPrograms L
  have hp_mem : m < (exactLengthPrograms L).length := by rw [h_exact_len]; exact h_mL
  have hp_nodup : (exactLengthPrograms L).Nodup := exactLengthPrograms_nodup L
  set p := (exactLengthPrograms L)[m]'hp_mem
  have hp_len : p.length = L := exactLengthPrograms_length_eq L p (List.getElem_mem hp_mem)
  have hp_idx : (exactLengthPrograms L).idxOf p = m := hp_nodup.idxOf_getElem m hp_mem
  have h_rfind1_eq :
      Nat.rfind (fun i => Part.some (decide (m < ((List.range (i + 1)).map f).sum))) =
        Part.some n := by
    apply rfind_eq_of_spec n
    · simp [h_m_lt]
    · intro i hi
      simp only [decide_eq_false_iff_not]
      push Not
      have h_le_n : i + 1 ≤ n := hi
      obtain ⟨d, hd⟩ : ∃ d, n = i + 1 + d := Nat.exists_eq_add_of_le h_le_n
      have h1 : List.range (i + 1 + d) = List.take (i + 1) (List.range (i + 1 + d)) ++
          List.drop (i + 1) (List.range (i + 1 + d)) :=
        (List.take_append_drop (i + 1) (List.range (i + 1 + d))).symm
      rw [List.take_range, min_eq_left (by omega)] at h1
      have h_range : ((List.range (i + 1)).map f).sum ≤ ((List.range (i + 1 + d)).map f).sum := by
        rw [h1, List.map_append, List.sum_append]
        omega
      dsimp [m, W_n]
      rw [hd]
      exact h_range.trans (Nat.le_add_right _ k_x)
  have h_check2_S1 : k_x < (enumAccum cA n S1).length := hk_x_lt
  obtain ⟨S_found, hS_found⟩ := Part.dom_iff_mem.mp (
    show (Nat.rfind (fun S => Part.some (decide (k_x < (enumAccum cA n S).length)))).Dom by
      refine Nat.rfind_dom.mpr ⟨S1, ?_, fun _ => Part.some_dom _⟩
      simp [h_check2_S1])
  have hS_found_spec := (Nat.mem_rfind).mp hS_found
  have hS_found_check : k_x < (enumAccum cA n S_found).length := by
    have h1 := hS_found_spec.1
    simp only [Part.mem_some_iff] at h1
    exact of_decide_eq_true h1.symm
  have h_elem_eq : (enumAccum cA n S_found)[k_x] = x := by
    have h2 := enum_accum_getElem cA n k_x S1 S_found hk_x_lt hS_found_check
    have h3 : (enumAccum cA n S1)[k_x] = x := List.getElem_idxOf hk_x_lt
    rw [← h2, h3]
  have hM_prod : x ∈ growthDecompressor f cA (p, []) := by
    unfold growthDecompressor
    dsimp
    rw [hp_len, hp_idx, h_rfind1_eq, Part.bind_some]
    have h_sub : m - W_n = k_x := by dsimp [m]; omega
    rw [h_sub, Part.eq_some_iff.mpr hS_found, Part.bind_some]
    rw [List.getElem?_eq_getElem hS_found_check, h_elem_eq]
    exact Part.mem_some x
  have h_cond : condK (growthDecompressor f cA) x [] ≤ (L : ℕ∞) := by
    refine (condK_le_iff (growthDecompressor f cA) x [] L).mpr ⟨p, ?_, hM_prod⟩
    change p.length ≤ L
    rw [hp_len]
  have h_plain : plainK U x ≤ (L + c_M : ℕ∞) := by
    have h_opt := hc_M x []
    change plainK U x ≤ condK (growthDecompressor f cA) x [] + (c_M : ℕ∞) at h_opt
    have h2 : condK (growthDecompressor f cA) x [] + (c_M : ℕ∞) ≤ (L : ℕ∞) + (c_M : ℕ∞) := by gcongr
    have h3 : (L : ℕ∞) + (c_M : ℕ∞) = ((L + c_M : ℕ) : ℕ∞) := by push_cast; rfl
    exact h_opt.trans (h2.trans_eq h3)
  calc plainK U x ≤ (L + c_M : ℕ∞) := h_plain
  _ = ((Nat.log 2 (f n) + (K_shift + 1 + c_M) : ℕ) : ℕ∞) := by
    dsimp [L]
    push_cast
    ring

-- `exercise07_hamming_neighbour` (ch01-exercise-7) is archived; see `docs/ARCHIVED_TARGETS.md`.

end Kolmogorov
