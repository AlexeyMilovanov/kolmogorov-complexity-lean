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
import KolmogorovMathlib.Complexity.EnumerableFamilies.Enumeration
import KolmogorovMathlib.Complexity.EnumerableFamilies.CalibratedBlocks

/-!
# Complexity is characterised by three properties

`plainK_within_const_of_calibrated`: a natural-valued function that is upper semicomputable,
does not grow along partial computable maps, and has sublevel sets of the right size agrees
with plain complexity up to an additive constant.  The lower bound comes from the block
decompressor of `CalibratedBlocks`.

The module also records the enumerability facts used there and elsewhere: `IsRE.and_decidable`,
`evalnIsSome` and `enumeratedLongString` with their computability, and — as a worked instance —
`isEnumerableSet_two_mul_plainK_lt_length` and
`infinite_compl_two_mul_plainK_lt_length`, that `{x : 2·C(x) < |x|}` is enumerable and its
complement infinite.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- A natural-valued function that is upper semicomputable, does not grow along partial
computable maps and has sublevel sets of the calibrated size agrees with plain
complexity up to an additive constant. SUV Theorem 9. -/
theorem plainK_within_const_of_calibrated (U : Map) (hU : isOptimalConditional U)
    (k : BitString → ℕ)
    (henum : IsUpperSemicomputable (fun x => (k x : ℕ∞)))
    (hnongrowth : ∀ A : BitString →. BitString, Partrec A →
      ∃ c : ℕ, ∀ x y : BitString, y ∈ A x → k y ≤ k x + c)
    (c₁ c₂ : ℕ)
    (hcalib : ∀ n : ℕ, {x : BitString | k x < n}.Finite ∧
      (c₁ ≤ n → 2 ^ (n - c₁) ≤ {x : BitString | k x < n}.ncard) ∧
      {x : BitString | k x < n}.ncard ≤ 2 ^ (n + c₂)) :
    ∃ c : ℕ, ∀ x : BitString,
      plainK U x ≤ (k x : ℕ∞) + (c : ℕ∞) ∧ (k x : ℕ∞) ≤ plainK U x + (c : ℕ∞) := by
  have hfin : ∀ n : ℕ, {x : BitString | k x < n}.Finite := fun n => (hcalib n).1
  have hcard_lower : ∀ n : ℕ, c₁ ≤ n → 2 ^ (n - c₁) ≤ {x : BitString | k x < n}.ncard :=
    fun n => (hcalib n).2.1
  have hcard_upper : ∀ n : ℕ, {x : BitString | k x < n}.ncard ≤ 2 ^ (n + c₂) :=
    fun n => (hcalib n).2.2
  obtain ⟨c_1, hc_1⟩ :=
    plainK_le_of_isUpperSemicomputable_of_card_le_two_pow U hU k henum c₂ hcard_upper hfin
  obtain ⟨c_2, hc_2⟩ :=
    le_plainK_of_two_pow_le_card_of_nonGrowth U hU k hnongrowth c₁ hcard_lower henum hfin
  refine ⟨max c_1 c_2, fun x => ⟨?_, ?_⟩⟩
  · calc plainK U x ≤ (k x : ℕ∞) + (c_1 : ℕ∞) := hc_1 x
      _ ≤ (k x : ℕ∞) + ((max c_1 c_2 : ℕ) : ℕ∞) := by
        have : (c_1 : ℕ∞) ≤ ((max c_1 c_2 : ℕ) : ℕ∞) := WithTop.coe_le_coe.mpr (le_max_left c_1 c_2)
        exact add_le_add_right this (k x : ℕ∞)
  · calc (k x : ℕ∞) ≤ plainK U x + (c_2 : ℕ∞) := hc_2 x
      _ ≤ plainK U x + ((max c_1 c_2 : ℕ) : ℕ∞) := by
        have : (c_2 : ℕ∞) ≤ ((max c_1 c_2 : ℕ) : ℕ∞) :=
          WithTop.coe_le_coe.mpr (le_max_right c_1 c_2)
        exact add_le_add_right this (plainK U x)

/-- The conjunction of a recursively enumerable predicate with a computable Boolean test
is recursively enumerable. -/
lemma IsRE.and_decidable {α : Type*} [Primcodable α] {R : α → Prop} (hR : IsRE R)
    {b : α → Bool} (hb : Computable b) :
    IsRE (fun x => R x ∧ b x = true) := by
  obtain ⟨f, hf_part, hf_dom⟩ := hR
  let g : α →. Unit := fun a => (f a).bind (fun _ => ↑(if b a = true then some () else none))
  have h_step : Computable (fun p : α × Unit => if b p.1 = true then some () else none) := by
    have h_b : Computable (fun p : α × Unit => b p.1) := hb.comp Computable.fst
    have h_cond := Computable.cond h_b (Computable.const (some ())) (Computable.const none)
    exact Computable.of_eq h_cond (by intro p; cases b p.1 <;> rfl)
  have hg_part : Partrec g := Partrec.bind hf_part (Computable.ofOption h_step).to₂
  use g
  refine ⟨hg_part, fun a => ?_⟩
  simp only [g, Part.bind_dom, Part.ofOption_dom]
  rw [hf_dom]
  constructor
  · rintro ⟨h1, h2⟩
    split_ifs at h2 with h
    · exact ⟨h1, h⟩
    · contradiction
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [if_pos h2]
    trivial

/-- Whether the code `cB` accepts the string `x` within `s` steps. -/
def evalnIsSome (cB : Code) (s : ℕ) (x : BitString) : Bool :=
  (Nat.Partrec.Code.evaln s cB (Encodable.encode x)).isSome

/-- Acceptance within a stage read off the first component of the input is computable. -/
lemma evalnIsSome_computable (cB : Code) :
    Computable (fun (p : ℕ × BitString) => evalnIsSome cB (p.1.unpair.2 + 1) p.2) := by
  have h_k : Computable (fun (p : ℕ × BitString) => p.1.unpair.2 + 1) :=
    Computable.succ.comp (Computable.snd.comp (Computable.unpair.comp Computable.fst))
  have h_x : Computable (fun (p : ℕ × BitString) => Encodable.encode p.2) :=
    Computable.encode.comp Computable.snd
  have h_core : Computable (fun (p : (ℕ × Nat.Partrec.Code) × ℕ) =>
                             Nat.Partrec.Code.evaln p.1.1 p.1.2 p.2) :=
    Primrec.to_comp Nat.Partrec.Code.primrec_evaln
  have h_arg : Computable (fun (p : ℕ × BitString) => ((p.1.unpair.2 + 1, cB),
                                                        Encodable.encode p.2)) :=
    Computable.pair (Computable.pair h_k (Computable.const cB)) h_x
  exact (Primrec.to_comp Primrec.option_isSome).comp (h_core.comp h_arg)

/-- Whether the number `m` codes a pair `(x, t)` such that `cB` accepts `x` within `t + 1`
steps and `x` is longer than `2 * 2 ^ k`. -/
def enumeratedLongString (cB : Code) (k : ℕ) (m : ℕ) : Bool :=
  let p := m.unpair
  match (Encodable.decode p.1 : Option BitString) with
  | some x =>
    evalnIsSome cB (p.2 + 1) x && decide (2 * 2^k < x.length)
  | none => false

/-- The set of strings `x` with `2 * C(x) < |x|` is enumerable. -/
lemma isEnumerableSet_two_mul_plainK_lt_length (U : Map) (hU : isOptimalConditional U) :
    IsEnumerableSet {x : BitString | 2 * plainK U x < (x.length : ℕ∞)} := by
  let A := {x : BitString | 2 * plainK U x < (x.length : ℕ∞)}
  have h_equiv : (fun x : BitString => x ∈ A) =
      (fun x : BitString => ∃ p ∈ List.range x.length,
        plainK U x ≤ (p : ℕ∞) ∧ 2 * p < x.length) := by
    ext x
    simp only [Set.mem_ofPred_eq, A]
    constructor
    · intro hx
      have hK : plainK U x ≠ ⊤ := by
        intro htop
        rw [htop] at hx
        exact not_top_lt hx
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hK
      have hx' : 2 * k < x.length := by
        have h_hx := hx
        rw [← hk] at h_hx
        have hx'' : ((2 * k : ℕ) : ℕ∞) < (x.length : ℕ∞) := by
          calc ((2 * k : ℕ) : ℕ∞) = 2 * (k : ℕ∞) := by push_cast; rfl
            _ < (x.length : ℕ∞) := h_hx
        exact ENat.natCast_lt_natCast.mp hx''
      refine ⟨k, List.mem_range.mpr (by omega), le_of_eq hk.symm, hx'⟩
    · rintro ⟨p, _, hp_le, hp_lt⟩
      calc 2 * plainK U x ≤ 2 * (p : ℕ∞) := by gcongr
        _ = ((2 * p : ℕ) : ℕ∞) := by push_cast; rfl
        _ < (x.length : ℕ∞) := ENat.natCast_lt_natCast.mpr hp_lt
  change IsRE (fun x => x ∈ A)
  rw [h_equiv]
  have h_bound : Computable (fun x : BitString => List.range x.length) :=
    Computable.comp (Primrec.to_comp Primrec.list_range) Computable.list_length
  have h_K_le : IsRE (fun p : BitString × ℕ => plainK U p.1 ≤ (p.2 : ℕ∞)) := by
    obtain ⟨f, hf_part, hf_dom⟩ := condK_le_isRE U hU
    use fun p => f (p.1, [], p.2)
    constructor
    · exact Partrec.comp hf_part (Computable.pair Computable.fst
        (Computable.pair (Computable.const []) Computable.snd))
    · intro p
      rw [hf_dom]
      rfl
  have h_test_bool : Computable (fun p : BitString × ℕ => decide (2 * p.2 < p.1.length)) := by
    have h1 : Computable (fun p : BitString × ℕ => 2 * p.2) :=
      (Primrec.to_comp Primrec.nat_mul).comp (Computable.pair (Computable.const 2) Computable.snd)
    have h2 : Computable (fun p : BitString × ℕ => p.1.length) :=
      Computable.comp Computable.list_length Computable.fst
    exact Computable.natLt.comp (Computable.pair h1 h2)
  have h_rel := IsRE.and_decidable h_K_le h_test_bool
  simp_rw [decide_eq_true_iff] at h_rel
  exact IsRE.existsInList h_rel _ h_bound

/-- Infinitely many strings fail `2 * C(x) < |x|`. -/
lemma infinite_compl_two_mul_plainK_lt_length (U : Map) :
    {x : BitString | 2 * plainK U x < (x.length : ℕ∞)}ᶜ.Infinite := by
  let A := {x : BitString | 2 * plainK U x < (x.length : ℕ∞)}
  intro h_fin
  let S := h_fin.toFinset.image List.length
  by_cases hS : S = ∅
  · obtain ⟨s0, hs0_len, hs0_K⟩ := exists_incompressible_string U [] 0
    have hs0 : s0 ∈ Aᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, A]
      rw [hs0_len]
      exact zero_le
    have h0 : 0 ∈ S := by
      simp only [S, Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨s0, hs0, hs0_len⟩
    rw [hS] at h0
    cases h0
  · let M := S.max' (Finset.nonempty_iff_ne_empty.mpr hS)
    obtain ⟨sM, hsM_len, hsM_K⟩ := exists_incompressible_string U [] (M + 1)
    have hsM : sM ∈ Aᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, A]
      have h_len_eq : (sM.length : ℕ∞) = ((M + 1 : ℕ) : ℕ∞) := by exact_mod_cast hsM_len
      rw [h_len_eq]
      calc ((M + 1 : ℕ) : ℕ∞) ≤ plainK U sM := hsM_K
        _ ≤ 1 * plainK U sM := by rw [one_mul]
        _ ≤ 2 * plainK U sM := by gcongr; norm_num
    have h_mem_S : (M + 1) ∈ S := by
      simp only [S, Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨sM, hsM, hsM_len⟩
    have h_le := S.le_max' (M + 1) h_mem_S
    omega

end Kolmogorov
