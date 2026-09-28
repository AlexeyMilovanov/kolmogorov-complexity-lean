import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.CommonInformation.ConditionalIndependence
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.PairComplexity.LogarithmicTerms

/-!
# Total conditional complexity, and refinements of Kolmogorov–Levin

`totalCondComplexity x y` is the minimal length of a *total* program mapping `y` to `x`.  It
sits between the two usual quantities: `condK_le_totalCondComplexity` and
`totalCondComplexity_le_plainK`, the first through the evaluator `D_eval` and the second
through the constant program `codeConst`.

The rest of the module sharpens the Kolmogorov–Levin theorem along SUV Exercises 35–40:
`plainK_add_condK_le_plainK_pair_add_three_log` (Exercise 35) reduces the error term to
`3 log`, with `exists_plainK_add_condK_le_of_cPairVal` isolating the coupling step, and the
padding lemmas `padTo`, `length_padTo`, `bitsToNat_append_single_false` supply the fixed-width
encodings the sharper bound needs.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

/-- The minimal plain complexity of a *total* program mapping `y` to `x`: the
total conditional complexity `CT(x | y)`. -/
noncomputable def totalCondComplexity (U : Map) (x y : BitString) : ℕ∞ :=
  sInf {v : ℕ∞ | ∃ e : ℕ, (∀ w : ℕ, ((Denumerable.ofNat Code e).eval w).Dom) ∧
    Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y) ∧
      plainKNat U e = v}

private def D_eval (U : Map) : Map := fun (p, y) =>
  (U (p, [])).bind (fun s =>
    ((Denumerable.ofNat Code (decodeBits s)).eval (Encodable.encode y)).bind (fun n =>
      Part.ofOption (Encodable.decode n)))

private theorem D_eval_partrec (U : Map) (hU : isDecompressor U) : isDecompressor (D_eval U) := by
  have h1 : Partrec (fun (py : BitString × BitString) => U (py.1, [])) :=
    Partrec.comp hU (Computable.pair Computable.fst (Computable.const []))
  have h_eval : Partrec (fun (p : ℕ × ℕ) => (Denumerable.ofNat Code p.1).eval p.2) := Code.eval_part
  have h_decode : Partrec (fun (n : ℕ) => Part.ofOption (Encodable.decode (α := BitString) n)) :=
    Computable.ofOption Computable.decode
  have h2 : Partrec (fun (pys : (BitString × BitString) × BitString) =>
      ((Denumerable.ofNat Code (decodeBits pys.2)).eval (Encodable.encode pys.1.2)).bind (fun n =>
        Part.ofOption (Encodable.decode (α := BitString) n))) := by
    have h_dec : Computable (fun (pys : (BitString × BitString) × BitString) => decodeBits pys.2) :=
      decodeBits_computable.comp Computable.snd
    have h_pair : Computable (fun (pys : (BitString × BitString) × BitString) =>
        (decodeBits pys.2, Encodable.encode pys.1.2)) :=
      Computable.pair h_dec (Computable.encode.comp (Computable.snd.comp Computable.fst))
    have h_ev : Partrec (fun (pys : (BitString × BitString) × BitString) =>
        (Denumerable.ofNat Code (decodeBits pys.2)).eval (Encodable.encode pys.1.2)) :=
      Partrec.comp h_eval h_pair
    exact Partrec.bind h_ev (h_decode.comp Computable.snd)
  exact Partrec.bind h1 h2

private lemma produces_D_eval (U : Map) (p y x : BitString) (s : BitString)
    (h_s : s ∈ U (p, []))
    (h_eval : Encodable.encode x ∈
      (Denumerable.ofNat Code (decodeBits s)).eval (Encodable.encode y)) :
    x ∈ D_eval U (p, y) := by
  unfold D_eval
  rw [Part.mem_bind_iff]
  refine ⟨s, h_s, ?_⟩
  rw [Part.mem_bind_iff]
  refine ⟨Encodable.encode x, h_eval, ?_⟩
  simp [Encodable.encodek]

private lemma condK_D_eval_le_plainKNat (U : Map) (x y : BitString) (e : ℕ)
    (h_eval : Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y)) :
    condK (D_eval U) x y ≤ plainKNat U e := by
  unfold condK plainKNat plainK candidateLengths
  apply sInf_le_sInf
  rintro n ⟨p, hp_prod, rfl⟩
  refine ⟨p, produces_D_eval U p y x (Nat.bits e) hp_prod ?_, rfl⟩
  rw [decodeBits_natBits]
  exact h_eval

private theorem condK_le_totalCondComplexity (U : Map) (hU : isOptimalConditional U) :
    ∃ k1 : ℕ, ∀ x y : BitString, condK U x y ≤ totalCondComplexity U x y + (k1 : ℕ∞) := by
  have hD : isDecompressor (D_eval U) := D_eval_partrec U hU.1
  obtain ⟨c, hc⟩ := hU.2 (D_eval U) hD
  use c
  intro x y
  unfold totalCondComplexity
  have h_le : condK (D_eval U) x y ≤
      sInf {v : ℕ∞ | ∃ e : ℕ, (∀ w : ℕ, ((Denumerable.ofNat Code e).eval w).Dom) ∧
        Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y) ∧
          plainKNat U e = v} := by
    apply le_sInf
    rintro v ⟨e, _htotal, h_eval, rfl⟩
    exact condK_D_eval_le_plainKNat U x y e h_eval
  have h_hc := hc x y
  exact le_trans h_hc (by gcongr)

private def codeConst (x : BitString) : ℕ := Encodable.encode (Code.const (Encodable.encode x))

private lemma codeConst_eval (x : BitString) (w : ℕ) :
    ((Denumerable.ofNat Code (codeConst x)).eval w) = Part.some (Encodable.encode x) := by
  unfold codeConst
  rw [Denumerable.ofNat_encode]
  exact Code.eval_const (Encodable.encode x) w

private lemma codeConst_total (x : BitString) (w : ℕ) :
    ((Denumerable.ofNat Code (codeConst x)).eval w).Dom := by
  rw [codeConst_eval]
  exact trivial

private lemma codeConst_eval_mem (x : BitString) (y : BitString) :
    Encodable.encode x ∈ (Denumerable.ofNat Code (codeConst x)).eval (Encodable.encode y) := by
  rw [codeConst_eval]
  exact Part.mem_some _

private theorem totalCondComplexity_le_plainK (U : Map) (hU : isOptimalConditional U) :
    ∃ k2 : ℕ, ∀ x y : BitString, totalCondComplexity U x y ≤ plainK U x + (k2 : ℕ∞) := by
  let f_const : BitString → BitString := fun x => Nat.bits (codeConst x)
  have h_const_comp : Computable f_const := by
    unfold f_const codeConst
    have h1 : Computable (fun x : BitString => Encodable.encode x) := Computable.encode
    have h2 : Computable (fun n : ℕ => Code.const n) := Code.primrec_const.to_comp
    have h3 : Computable (fun c : Code => Encodable.encode c) := Computable.encode
    have h4 : Computable (fun n : ℕ => Nat.bits n) := natBits_computable
    exact h4.comp (h3.comp (h2.comp h1))
  obtain ⟨c, hc⟩ := plainK_map_le U hU f_const h_const_comp
  use c
  intro x y
  unfold totalCondComplexity
  have h_mem : plainKNat U (codeConst x) ∈
      {v : ℕ∞ | ∃ e : ℕ, (∀ w : ℕ, ((Denumerable.ofNat Code e).eval w).Dom) ∧
        Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y) ∧
          plainKNat U e = v} := by
    exact ⟨codeConst x, codeConst_total x, codeConst_eval_mem x y, rfl⟩
  have h_inf_le : sInf {v : ℕ∞ | ∃ e : ℕ, (∀ w : ℕ, ((Denumerable.ofNat Code e).eval w).Dom) ∧
      Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y) ∧
        plainKNat U e = v} ≤ plainKNat U (codeConst x) :=
    sInf_le h_mem
  have h_eq : plainK U (f_const x) = plainKNat U (codeConst x) := rfl
  calc
    sInf {v : ℕ∞ | ∃ e : ℕ, (∀ w : ℕ, ((Denumerable.ofNat Code e).eval w).Dom) ∧
      Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y) ∧
        plainKNat U e = v}
      ≤ plainKNat U (codeConst x) := h_inf_le
    _ = plainK U (f_const x) := h_eq.symm
    _ ≤ plainK U x + (c : ℕ∞) := hc x

/-- **Exercise 29.** `C(x | y) ≤ CT(x | y) ≤ C(x) + O(1)`. -/
theorem condK_le_totalCondK_le_plainK (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      condK U x y ≤ totalCondComplexity U x y + (k : ℕ∞) ∧
        totalCondComplexity U x y ≤ plainK U x + (k : ℕ∞) := by
  obtain ⟨k1, hk1⟩ := condK_le_totalCondComplexity U hU
  obtain ⟨k2, hk2⟩ := totalCondComplexity_le_plainK U hU
  use max k1 k2
  intro x y
  constructor
  · calc
      condK U x y ≤ totalCondComplexity U x y + (k1 : ℕ∞) := hk1 x y
      _           ≤ totalCondComplexity U x y + ((max k1 k2 : ℕ) : ℕ∞) := by
        gcongr
        exact le_max_left k1 k2
  · calc
      totalCondComplexity U x y ≤ plainK U x + (k2 : ℕ∞) := hk2 x y
      _                         ≤ plainK U x + ((max k1 k2 : ℕ) : ℕ∞) := by
        gcongr
        exact le_max_right k1 k2

-- `exercise30_total_gap` (ch02-exercise-30) is archived; see `docs/ARCHIVED_TARGETS.md`.

-- `exercise31_permutation` (ch02-exercise-31) is archived; see `docs/ARCHIVED_TARGETS.md`.

-- `exercise32_permutation_lower_bound` (ch02-exercise-32) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

/-- **Exercise 33.** For any two conditions there is a string of length `n` that
is incompressible relative to both, up to one bit. -/
theorem exists_incompressible_two_conditions (U : Map) (hU : isOptimalConditional U)
    (y z : BitString) (n : ℕ) :
    ∃ x : BitString, x.length = n ∧
      ((n - 1 : ℕ) : ℕ∞) ≤ condK U x y ∧ ((n - 1 : ℕ) : ℕ∞) ≤ condK U x z := by
  classical
  have _ := hU
  rcases n with _ | _ | m
  · refine ⟨[], rfl, ?_, ?_⟩ <;> exact zero_le _
  · refine ⟨[false], rfl, ?_, ?_⟩ <;> exact zero_le _
  · set S := compressibleWords U y m ∪ compressibleWords U z m
    have h_card_S : S.card < 2 ^ (m + 2) := by
      calc
        S.card ≤ (compressibleWords U y m).card + (compressibleWords U z m).card :=
          Finset.card_union_le _ _
        _ < 2 ^ (m + 1) + 2 ^ (m + 1) := by
          gcongr
          · exact card_compressibleWordsLt U y m
          · exact card_compressibleWordsLt U z m
        _ = 2 ^ (m + 2) := by ring
    have h_not_subset : ¬ (stringsOfLength (m + 2) ⊆ S) := by
      intro h_sub
      have h_le := Finset.card_le_card h_sub
      rw [card_stringsOfLength] at h_le
      omega
    rw [Finset.not_subset] at h_not_subset
    obtain ⟨x, hx_str, hx_not_S⟩ := h_not_subset
    rw [mem_stringsOfLength] at hx_str
    rw [Finset.mem_union, not_or] at hx_not_S
    refine ⟨x, hx_str, ?_, ?_⟩
    · have h_not_comp : x ∉ compressibleWords U y m := hx_not_S.1
      have h_lt : (m : ℕ∞) < condK U x y := by
        by_contra! h_le
        apply h_not_comp
        rw [compressibleWords, Finset.mem_filter]
        refine ⟨?_, h_le⟩
        obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U x y m).mp h_le
        rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
        exact ⟨p, mem_programsLe m p hp_len, progToOut_eq_some.mpr hp_prod⟩
      have h_le : (m + 1 : ℕ∞) ≤ condK U x y := (ENat.add_one_le_iff (ENat.coe_ne_top m)).mpr h_lt
      have h_eq : (m + 2 - 1 : ℕ) = m + 1 := rfl
      rw [h_eq]
      exact h_le
    · have h_not_comp : x ∉ compressibleWords U z m := hx_not_S.2
      have h_lt : (m : ℕ∞) < condK U x z := by
        by_contra! h_le
        apply h_not_comp
        rw [compressibleWords, Finset.mem_filter]
        refine ⟨?_, h_le⟩
        obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U x z m).mp h_le
        rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
        exact ⟨p, mem_programsLe m p hp_len, progToOut_eq_some.mpr hp_prod⟩
      have h_le : (m + 1 : ℕ∞) ≤ condK U x z := (ENat.add_one_le_iff (ENat.coe_ne_top m)).mpr h_lt
      have h_eq : (m + 2 - 1 : ℕ) = m + 1 := rfl
      rw [h_eq]
      exact h_le

/-- Custom decompressor for the triangle inequality
`C(x|z) ≤ C(x|y) + C(y|z) + 2 log C(x|y) + O(1)`. -/
def triangleDecoder (U : Map) : Map := fun pr =>
  let r := pr.1
  let z := pr.2
  let a := decodeFirst r
  let n := bitsToNat a
  let rest := decodeSecond r
  let p := rest.take n
  let q := rest.drop n
  (U (q, z)).bind (fun y => U (p, y))

/-- The decompressor behind the triangle inequality is a decompressor whenever `U` is. -/
theorem triangleDecoder_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (triangleDecoder U) := by
  have ha : Computable (fun pr : BitString × BitString => decodeFirst pr.1) :=
    decodeFirst_computable.comp Computable.fst
  have hn : Computable (fun pr : BitString × BitString => bitsToNat (decodeFirst pr.1)) :=
    bitsToNat_computable.comp ha
  have hrest : Computable (fun pr : BitString × BitString => decodeSecond pr.1) :=
    decodeSecond_computable.comp Computable.fst
  have hp : Computable (fun pr : BitString × BitString =>
      (decodeSecond pr.1).take (bitsToNat (decodeFirst pr.1))) :=
    primrec_list_take.to_comp.comp hrest hn
  have hq : Computable (fun pr : BitString × BitString =>
      (decodeSecond pr.1).drop (bitsToNat (decodeFirst pr.1))) :=
    primrec_list_drop.to_comp.comp hrest hn
  have hq_z : Computable (fun pr : BitString × BitString =>
      ((decodeSecond pr.1).drop (bitsToNat (decodeFirst pr.1)), pr.2)) :=
    hq.pair Computable.snd
  have hf : Partrec (fun pr : BitString × BitString =>
      U ((decodeSecond pr.1).drop (bitsToNat (decodeFirst pr.1)), pr.2)) :=
    hU.comp hq_z.partrec
  have hp_y : Computable (fun p : (BitString × BitString) × BitString =>
      ((decodeSecond p.1.1).take (bitsToNat (decodeFirst p.1.1)), p.2)) :=
    (hp.comp Computable.fst).pair Computable.snd
  have hg : Partrec (fun p : (BitString × BitString) × BitString =>
      U ((decodeSecond p.1.1).take (bitsToNat (decodeFirst p.1.1)), p.2)) :=
    hU.comp hp_y.partrec
  exact Partrec.bind hf hg

/-- Concatenating a self-delimiting program for `x` given `y` with a program for `y` given `z`
produces `x` from `z` under the triangle decompressor. -/
theorem triangleDecoder_produces (U : Map) {p q x y z : BitString}
    (hp : produces U p y x) (hq : produces U q z y) :
    produces (triangleDecoder U)
      (pairCode (Nat.bits p.length) p ++ q) z x := by
  unfold triangleDecoder produces
  dsimp
  have h_append : pairCode (Nat.bits p.length) p ++ q =
      pairCode (Nat.bits p.length) (p ++ q) := by
    unfold pairCode
    simp [List.append_assoc]
  rw [h_append]
  rw [decodeFirst_pairCode, bitsToNat_bits, decodeSecond_pairCode]
  rw [List.take_left, List.drop_left]
  exact Part.mem_bind hq hp

/-- **Exercise 34.** Triangle inequality for conditional complexity. -/
theorem condK_triangle (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y z : BitString,
      condK U x z ≤ condK U x y + condK U y z +
        ((2 * Nat.log 2 (condCVal U x y) + k : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := hU.2 (triangleDecoder U) (triangleDecoder_isDecompressor U hU.1)
  use 3 + c
  intro x y z
  by_cases hxy : condK U x y = ⊤
  · rw [hxy, top_add]
    exact le_top
  by_cases hyz : condK U y z = ⊤
  · rw [hyz, add_top]
    exact le_top
  have hxy_fin : condK U x y = (condCVal U x y : ℕ∞) := by
    unfold condCVal
    cases h_eq : condK U x y
    · contradiction
    · rfl
  have hyz_fin : condK U y z = (condCVal U y z : ℕ∞) := by
    unfold condCVal
    cases h_eq : condK U y z
    · contradiction
    · rfl
  have hxy_le : condK U x y ≤ (condCVal U x y : ℕ∞) := by rw [hxy_fin]
  have hyz_le : condK U y z ≤ (condCVal U y z : ℕ∞) := by rw [hyz_fin]
  rw [condK_le_iff] at hxy_le hyz_le
  obtain ⟨p, hp_len, hp_prod⟩ := hxy_le
  obtain ⟨q, hq_len, hq_prod⟩ := hyz_le
  have hprod : produces (triangleDecoder U) (pairCode (Nat.bits p.length) p ++ q) z x :=
    triangleDecoder_produces U hp_prod hq_prod
  have h_condK_D : condK (triangleDecoder U) x z ≤
      ((pairCode (Nat.bits p.length) p ++ q).length : ℕ∞) := by
    rw [condK_le_iff]
    exact ⟨pairCode (Nat.bits p.length) p ++ q, rfl.le, hprod⟩
  have h_condK_U : condK U x z ≤
      ((pairCode (Nat.bits p.length) p ++ q).length : ℕ∞) + (c : ℕ∞) := calc
    condK U x z ≤ condK (triangleDecoder U) x z + (c : ℕ∞) := hc x z
    _ ≤ ((pairCode (Nat.bits p.length) p ++ q).length : ℕ∞) + (c : ℕ∞) :=
      add_le_add h_condK_D (le_refl (c : ℕ∞))
  have h_len : (pairCode (Nat.bits p.length) p ++ q).length =
      2 * (Nat.bits p.length).length + 1 + p.length + q.length := by
    have h_append : pairCode (Nat.bits p.length) p ++ q =
        pairCode (Nat.bits p.length) (p ++ q) := by
      unfold pairCode
      simp [List.append_assoc]
    rw [h_append, length_pairCode]
    simp [List.length_append]
    omega
  have h_bits_len : (Nat.bits p.length).length ≤ Nat.log 2 p.length + 1 :=
    length_natBits_le_log p.length
  have h_log_mono : Nat.log 2 p.length ≤ Nat.log 2 (condCVal U x y) :=
    Nat.log_mono_right hp_len
  have h_bound_nat : (pairCode (Nat.bits p.length) p ++ q).length + c ≤
      condCVal U x y + condCVal U y z + (2 * Nat.log 2 (condCVal U x y) + (3 + c)) := by
    rw [h_len]
    set L := (Nat.bits p.length).length
    set lg1 := Nat.log 2 p.length
    set lg2 := Nat.log 2 (condCVal U x y)
    set plen := p.length
    set qlen := q.length
    set c1 := condCVal U x y
    set c2 := condCVal U y z
    have h1 : L ≤ lg1 + 1 := h_bits_len
    have h2 : lg1 ≤ lg2 := h_log_mono
    have h3 : plen ≤ c1 := hp_len
    have h4 : qlen ≤ c2 := hq_len
    omega
  have h_bound_enat : (((pairCode (Nat.bits p.length) p ++ q).length + c : ℕ) : ℕ∞) ≤
      (condCVal U x y : ℕ∞) + (condCVal U y z : ℕ∞) +
        ((2 * Nat.log 2 (condCVal U x y) + (3 + c) : ℕ) : ℕ∞) := by
    exact_mod_cast h_bound_nat
  rw [← hxy_fin, ← hyz_fin] at h_bound_enat
  exact le_trans h_condK_U h_bound_enat

/-! ### Exercises 35–40: the Kolmogorov–Levin theorem, refinements -/

/-- Twice the number of digits of the digit count of `a` is at most `2 log log a + 6`. -/
lemma nat_bits_length_log_log_bound (a : ℕ) :
    2 * (Nat.bits a).length.bits.length ≤ 2 * Nat.log 2 (Nat.log 2 a) + 6 := by
  have h1 : (Nat.bits a).length ≤ Nat.log 2 a + 1 := length_natBits_le_log a
  have h2 : (Nat.bits (Nat.bits a).length).length ≤ Nat.log 2 ((Nat.bits a).length) + 1 :=
    length_natBits_le_log (Nat.bits a).length
  have h3 : Nat.log 2 ((Nat.bits a).length) ≤ Nat.log 2 (Nat.log 2 a + 1) :=
    Nat.log_mono_right h1
  have h4 : Nat.log 2 (Nat.log 2 a + 1) ≤ Nat.log 2 (Nat.log 2 a) + 1 :=
    log_succ_le (Nat.log 2 a)
  omega

/-- A number bounded by `a + log a + 2 log log a + C₀` has at most `log a + O(log C₀)` digits,
in the explicit form `2 |bits p| ≤ 2 log a + (2 log (C₀ + 12) + 8)`. -/
lemma nat_bits_length_p_bound (a C0 p : ℕ)
    (hp : p ≤ a + (Nat.bits a).length + 2 * (Nat.bits (Nat.bits a).length).length + C0) :
    2 * (Nat.bits p).length ≤ 2 * Nat.log 2 a + (2 * Nat.log 2 (C0 + 12) + 8) := by
  by_cases ha : a = 0
  · subst ha
    have h1 : (Nat.bits 0).length = 0 := rfl
    rw [h1, h1] at hp
    have hp0 : p ≤ C0 := by omega
    have hp_bits : (Nat.bits p).length ≤ (Nat.bits (C0 + 12)).length :=
      length_natBits_mono (by omega)
    have h_log : (Nat.bits (C0 + 12)).length ≤ Nat.log 2 (C0 + 12) + 1 :=
      length_natBits_le_log (C0 + 12)
    have h_log0 : Nat.log 2 0 = 0 := rfl
    rw [h_log0]
    omega
  · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
    by_cases hp0 : p = 0
    · subst hp0
      have : (Nat.bits 0).length = 0 := rfl
      omega
    · have hp_pos : 0 < p := Nat.pos_of_ne_zero hp0
      have h1 : (Nat.bits a).length ≤ Nat.log 2 a + 1 := length_natBits_le_log a
      have h2 : 2 * (Nat.bits (Nat.bits a).length).length ≤ 2 * Nat.log 2 (Nat.log 2 a) + 6 :=
        nat_bits_length_log_log_bound a
      have h_mul1 : Nat.log 2 a ≤ a := Nat.log_le_self 2 a
      have h_mul2 : Nat.log 2 (Nat.log 2 a) ≤ a := (Nat.log_le_self 2 (Nat.log 2 a)).trans h_mul1
      have h_mul3 : C0 + 7 ≤ (C0 + 7) * a := Nat.le_mul_of_pos_right (C0 + 7) ha_pos
      have hp_linear : p ≤ (C0 + 12) * a := by nlinarith
      have hp_log_p : Nat.log 2 p ≤ Nat.log 2 ((C0 + 12) * a) := Nat.log_mono_right hp_linear
      have hK_pos : 0 < C0 + 12 := by omega
      have h_K : (C0 + 12) < 2 ^ (Nat.log 2 (C0 + 12) + 1) :=
        Nat.lt_pow_succ_log_self (by decide) (C0 + 12)
      have h_a : a < 2 ^ (Nat.log 2 a + 1) :=
        Nat.lt_pow_succ_log_self (by decide) a
      have h_Ka_lt : (C0 + 12) * a < 2 ^ (Nat.log 2 (C0 + 12) + Nat.log 2 a + 2) := by
        have h_pow : 2 ^ (Nat.log 2 (C0 + 12) + 1) * 2 ^ (Nat.log 2 a + 1) =
            2 ^ (Nat.log 2 (C0 + 12) + Nat.log 2 a + 2) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        have h_mul : (C0 + 12) * a < 2 ^ (Nat.log 2 (C0 + 12) + 1) * 2 ^ (Nat.log 2 a + 1) := by
          nlinarith [h_K, h_a]
        exact h_mul.trans_eq h_pow
      have h_log_Ka : Nat.log 2 ((C0 + 12) * a) ≤ Nat.log 2 (C0 + 12) + Nat.log 2 a + 1 := by
        by_contra h_contra
        have h_ge : Nat.log 2 (C0 + 12) + Nat.log 2 a + 2 ≤ Nat.log 2 ((C0 + 12) * a) := by omega
        have h_pow_le : 2 ^ (Nat.log 2 (C0 + 12) + Nat.log 2 a + 2) ≤
            2 ^ Nat.log 2 ((C0 + 12) * a) :=
          Nat.pow_le_pow_right (by decide) h_ge
        have h_pow_self : 2 ^ Nat.log 2 ((C0 + 12) * a) ≤ (C0 + 12) * a :=
          Nat.pow_log_le_self 2 (by positivity)
        omega
      have hp_bits_len : (Nat.bits p).length ≤ Nat.log 2 p + 1 := length_natBits_le_log p
      omega

/-- The coupling bounds between the plain/conditional machine `U` and the prefix machine
`U_pref`, with their constants: `U`-complexity is below prefix complexity up to `cPlain` and
`cCond`; the prefix pair complexity splits (`cLower`), tolerates removing a short piece of the
condition (`cRem`) and dominates its left component (`cProj`); the prefix complexity of a
number is logarithmic (`cNat`), of any string at most its length plus a logarithm (`cLog`);
and a conditional description of exact length is available at cost `cExact`.

This is an *assumption* about the pair of machines, not a proved fact: it is discharged for an
optimal `U` and an optimal prefix machine `U_pref` inside
`plainK_add_condK_le_plainK_pair_add_three_log`, from the eight named library results listed
there. -/
private structure PrefixCouplingBounds (U U_pref : Map)
    (cPlain cCond cLower cRem cNat cProj cExact cLog : ℕ) : Prop where
  /-- `U`-complexity is below plain prefix complexity up to `cPlain`. -/
  plain_le : ∀ x : BitString, plainK U x ≤ KPPlain U_pref x + (cPlain : ℕ∞)
  /-- `U`-conditional complexity is below conditional prefix complexity up to `cCond`. -/
  cond_le : ∀ y x : BitString, condK U y x ≤ KP U_pref y x + (cCond : ℕ∞)
  /-- The prefix pair complexity splits, up to `cLower`. -/
  pair_chain_lower : ∀ (x y : BitString) (p : ℕ), HasPrefixComplexityValue U_pref x p →
    KPPlain U_pref x + KP U_pref y (prefixComplexityContext x p) ≤
      KPPair U_pref x y + (cLower : ℕ∞)
  /-- Removing a piece of the condition costs its plain prefix complexity plus `cRem`. -/
  cond_remove : ∀ x y s : BitString, KP U_pref x y ≤
    KP U_pref x (pairCode y s) + KPPlain U_pref s + (cRem : ℕ∞)
  /-- The prefix complexity of a number code is logarithmic, with constant `cNat`. -/
  natCode_le : ∀ n : ℕ, KPPlain U_pref (natCode n) ≤ 2 * ((Nat.bits n).length : ℕ∞) + (cNat : ℕ∞)
  /-- The pair complexity dominates its left component, up to `cProj`. -/
  left_le_pair : ∀ x y : BitString, KPPlain U_pref x ≤ KPPair U_pref x y + (cProj : ℕ∞)
  /-- A conditional description of exact length is available at cost `cExact`. -/
  exact_length : ∀ (x y : BitString) (n : ℕ), condK U x y = (n : ℕ∞) →
    KP U_pref x (pairCode y (Nat.bits n)) ≤ ((n + cExact : ℕ) : ℕ∞)
  /-- The prefix complexity of a string is at most its length plus a logarithm and `cLog`. -/
  plain_le_length_add_log : ∀ s : BitString, KPPlain U_pref s ≤
    (s.length : ℕ∞) + 2 * ((Nat.bits s.length).length : ℕ∞) + (cLog : ℕ∞)

/-- Upper bound on pair prefix complexity `KPPair U_pref x y` in terms of the
finite value `a = cPairVal U x y`.  The hypotheses `h_exact`, `h_rem`, `h_log` are the fields
`exact_length`, `cond_remove` and `plain_le_length_add_log` of `PrefixCouplingBounds`. -/
private lemma kp_pair_bound_of_cPairVal (U U_pref : Map)
    (c_exact c_rem c_log : ℕ)
    (h_exact : ∀ (z w : BitString) (n : ℕ), condK U z w = ↑n →
      KP U_pref z (pairCode w (Nat.bits n)) ≤ ↑(n + c_exact))
    (h_rem : ∀ (z w s : BitString), KP U_pref z w ≤
      KP U_pref z (pairCode w s) + KPPlain U_pref s + ↑c_rem)
    (h_log : ∀ (s : BitString), KPPlain U_pref s ≤
      ↑s.length + 2 * ↑(Nat.bits s.length).length + ↑c_log)
    (x y : BitString) (a : ℕ) (ha : cPair U x y = ↑a) :
    KPPair U_pref x y ≤ ↑(a + (Nat.bits a).length +
      2 * (Nat.bits (Nat.bits a).length).length + (c_exact + c_rem + c_log)) := by
  have h_cond_a : condK U (pairCode x y) [] = ↑a := by
    rw [← ha]
    rfl
  have h_exact_a := h_exact (pairCode x y) [] a h_cond_a
  have h_rem_pair := h_rem (pairCode x y) [] (Nat.bits a)
  have h_kp_pair : KPPair U_pref x y ≤
      ↑(a + c_exact) + KPPlain U_pref (Nat.bits a) + ↑c_rem := by
    dsimp [KPPair]
    have h_rem_app := h_rem (pairCode x y) [] (Nat.bits a)
    have h1 : KP U_pref (pairCode x y) (pairCode [] (Nat.bits a)) +
        KPPlain U_pref (Nat.bits a) + ↑c_rem ≤
        ↑(a + c_exact) + KPPlain U_pref (Nat.bits a) + ↑c_rem := by
      gcongr
    exact h_rem_app.trans h1
  have h1 : KPPlain U_pref (Nat.bits a) ≤
      ↑((Nat.bits a).length + 2 * (Nat.bits (Nat.bits a).length).length + c_log) := by
    have h_log_bits := h_log (Nat.bits a)
    push_cast at h_log_bits ⊢
    exact h_log_bits
  have h3 : ↑(a + c_exact) + KPPlain U_pref (Nat.bits a) + ↑c_rem ≤
      ↑(a + c_exact) +
      ↑((Nat.bits a).length + 2 * (Nat.bits (Nat.bits a).length).length + c_log) +
        ↑c_rem := by
    gcongr
  have h4 : ↑(a + c_exact) +
      ↑((Nat.bits a).length + 2 * (Nat.bits (Nat.bits a).length).length + c_log) +
      ↑c_rem = (↑(a + (Nat.bits a).length + 2 * (Nat.bits (Nat.bits a).length).length +
        (c_exact + c_rem + c_log)) : ℕ∞) := by push_cast; ring
  rw [h4] at h3
  exact h_kp_pair.trans h3

/-- The plain prefix complexity of a natural-number code is finite.  The hypothesis `h_nat` is
the field `natCode_le` of `PrefixCouplingBounds`. -/
private lemma kpPlain_natCode_ne_top (U_pref : Map) (cNat : ℕ)
    (h_nat : ∀ (n : ℕ), KPPlain U_pref (natCode n) ≤ 2 * ↑(Nat.bits n).length + ↑cNat)
    (p : ℕ) :
    KPPlain U_pref (natCode p) ≠ ⊤ := by
  intro h_contra
  have h_nat_p := h_nat p
  rw [h_contra] at h_nat_p
  have h_top_le : (⊤ : ℕ∞) ≤ ↑(2 * (Nat.bits p).length + cNat) := by
    calc (⊤ : ℕ∞) ≤ 2 * ↑(Nat.bits p).length + ↑cNat := h_nat_p
    _ = ↑(2 * (Nat.bits p).length + cNat) := by push_cast; rfl
  exact ENat.coe_ne_top (2 * (Nat.bits p).length + cNat) (top_unique h_top_le)

/-- `y` has a finite description given `x` together with the complexity of `x`, as soon as
the pair `(x, y)` has one: this is what the chain rule gives when `p` is the complexity of
`x`.  The hypothesis `h_lower` is the field `pair_chain_lower` of `PrefixCouplingBounds`. -/
private lemma kp_context_ne_top (U_pref : Map) (c_lower : ℕ)
    (h_lower : ∀ (x y : BitString) (p : ℕ), HasPrefixComplexityValue U_pref x p →
      KPPlain U_pref x + KP U_pref y (prefixComplexityContext x p) ≤
        KPPair U_pref x y + ↑c_lower)
    (x y : BitString) (p : ℕ) (hpval_eq : ↑p = KPPlain U_pref x)
    (h_kp_pair_top : KPPair U_pref x y ≠ ⊤) :
    KP U_pref y (pairCode x (natCode p)) ≠ ⊤ := by
  intro h_contra
  have h_c := h_lower x y p hpval_eq
  rw [prefixComplexityContext_eq_pairCode] at h_c
  rw [h_contra, add_top] at h_c
  have h_top_le : (⊤ : ℕ∞) ≤ ↑((KPPair U_pref x y).toNat + c_lower) := by
    calc (⊤ : ℕ∞) ≤ KPPair U_pref x y + ↑c_lower := h_c
    _ = ↑(KPPair U_pref x y).toNat + ↑c_lower := by rw [ENat.coe_toNat h_kp_pair_top]
    _ = ↑((KPPair U_pref x y).toNat + c_lower) := by push_cast; rfl
  exact ENat.coe_ne_top ((KPPair U_pref x y).toNat + c_lower) (top_unique h_top_le)

/-- The chain rule in `ℕ`: the complexity `p` of `x` plus the complexity of `y` given `x`
and `p` is at most the pair complexity, up to the chain-rule constant.  The hypothesis
`h_lower` is the field `pair_chain_lower` of `PrefixCouplingBounds`. -/
private lemma kp_chain_toNat (U_pref : Map) (c_lower : ℕ)
    (h_lower : ∀ (x y : BitString) (p : ℕ), HasPrefixComplexityValue U_pref x p →
      KPPlain U_pref x + KP U_pref y (prefixComplexityContext x p) ≤
        KPPair U_pref x y + ↑c_lower)
    (x y : BitString) (p : ℕ) (hpval_eq : ↑p = KPPlain U_pref x)
    (h_kp_pair_top : KPPair U_pref x y ≠ ⊤) :
    p + (KP U_pref y (pairCode x (natCode p))).toNat ≤ (KPPair U_pref x y).toNat + c_lower := by
  have h_chain := h_lower x y p hpval_eq
  rw [prefixComplexityContext_eq_pairCode] at h_chain
  have h_ctx_ne := kp_context_ne_top U_pref c_lower h_lower x y p hpval_eq h_kp_pair_top
  have h1 : (↑(p + (KP U_pref y (pairCode x (natCode p))).toNat) : ℕ∞) ≤
      ↑((KPPair U_pref x y).toNat + c_lower) := by
    calc (↑(p + (KP U_pref y (pairCode x (natCode p))).toNat) : ℕ∞)
      _ = ↑p + ↑(KP U_pref y (pairCode x (natCode p))).toNat := by push_cast; rfl
      _ = KPPlain U_pref x + ↑(KP U_pref y (pairCode x (natCode p))).toNat := by rw [hpval_eq]
      _ = KPPlain U_pref x + KP U_pref y (pairCode x (natCode p)) := by
        rw [ENat.coe_toNat h_ctx_ne]
      _ ≤ KPPair U_pref x y + ↑c_lower := h_chain
      _ = ↑(KPPair U_pref x y).toNat + ↑c_lower := by rw [ENat.coe_toNat h_kp_pair_top]
      _ = ↑((KPPair U_pref x y).toNat + c_lower) := by push_cast; rfl
  exact WithTop.coe_le_coe.mp h1

/-- Removal of short information in `ℕ`: dropping the complexity `p` of `x` from the
condition costs at most the complexity of its code, up to the removal constant.  The
hypothesis `h_rem` is the field `cond_remove` of `PrefixCouplingBounds`. -/
private lemma kp_rem_toNat (U_pref : Map) (c_rem : ℕ)
    (h_rem : ∀ (x y s : BitString), KP U_pref x y ≤
      KP U_pref x (pairCode y s) + KPPlain U_pref s + ↑c_rem)
    (x y : BitString) (p : ℕ)
    (h_ctx_ne : KP U_pref y (pairCode x (natCode p)) ≠ ⊤)
    (h_p_nat_ne : KPPlain U_pref (natCode p) ≠ ⊤) :
    (KP U_pref y x).toNat ≤ (KP U_pref y (pairCode x (natCode p))).toNat +
      (KPPlain U_pref (natCode p)).toNat + c_rem := by
  have h1 : KP U_pref y x ≤ ↑((KP U_pref y (pairCode x (natCode p))).toNat +
      (KPPlain U_pref (natCode p)).toNat + c_rem) := by
    calc KP U_pref y x ≤ KP U_pref y (pairCode x (natCode p)) +
        KPPlain U_pref (natCode p) + ↑c_rem := h_rem y x (natCode p)
    _ = ↑(KP U_pref y (pairCode x (natCode p))).toNat +
        ↑(KPPlain U_pref (natCode p)).toNat + ↑c_rem := by
      rw [ENat.coe_toNat h_ctx_ne, ENat.coe_toNat h_p_nat_ne]
    _ = ↑((KP U_pref y (pairCode x (natCode p))).toNat +
        (KPPlain U_pref (natCode p)).toNat + c_rem) := by push_cast; rfl
  exact ENat.toNat_le_of_le_coe h1

/-- Boundedness of conditional prefix complexity `KP U_pref y x ≠ ⊤` when `x` has finite
complexity.  The hypotheses `h_lower`, `h_rem`, `h_nat` are the fields `pair_chain_lower`,
`cond_remove` and `natCode_le` of `PrefixCouplingBounds`. -/
private lemma kp_rem_ne_top (U_pref : Map) (c_lower c_rem cNat : ℕ)
    (h_lower : ∀ (x y : BitString) (p : ℕ), HasPrefixComplexityValue U_pref x p →
      KPPlain U_pref x + KP U_pref y (prefixComplexityContext x p) ≤
        KPPair U_pref x y + ↑c_lower)
    (h_rem : ∀ (x y s : BitString), KP U_pref x y ≤
      KP U_pref x (pairCode y s) + KPPlain U_pref s + ↑c_rem)
    (h_nat : ∀ (n : ℕ), KPPlain U_pref (natCode n) ≤ 2 * ↑(Nat.bits n).length + ↑cNat)
    (x y : BitString) (p : ℕ) (hpval_eq : ↑p = KPPlain U_pref x)
    (h_kp_pair_top : KPPair U_pref x y ≠ ⊤) :
    KP U_pref y x ≠ ⊤ := by
  intro h_contra
  have h_ctx_ne := kp_context_ne_top U_pref c_lower h_lower x y p hpval_eq h_kp_pair_top
  have h_p_nat_ne := kpPlain_natCode_ne_top U_pref cNat h_nat p
  have h1 : (⊤ : ℕ∞) ≤ ↑((KP U_pref y (pairCode x (natCode p))).toNat +
      (KPPlain U_pref (natCode p)).toNat + c_rem) := by
    calc (⊤ : ℕ∞) = KP U_pref y x := h_contra.symm
    _ ≤ KP U_pref y (pairCode x (natCode p)) + KPPlain U_pref (natCode p) + ↑c_rem :=
      h_rem y x (natCode p)
    _ = ↑(KP U_pref y (pairCode x (natCode p))).toNat +
        ↑(KPPlain U_pref (natCode p)).toNat + ↑c_rem := by
      rw [ENat.coe_toNat h_ctx_ne, ENat.coe_toNat h_p_nat_ne]
    _ = ↑((KP U_pref y (pairCode x (natCode p))).toNat +
        (KPPlain U_pref (natCode p)).toNat + c_rem) := by push_cast; rfl
  exact ENat.coe_ne_top ((KP U_pref y (pairCode x (natCode p))).toNat +
      (KPPlain U_pref (natCode p)).toNat + c_rem) (top_unique h1)

/-- From the coupling bounds alone there is a constant `k` such that
`plainK U x + condK U y x ≤ a + 3 * log₂ a + k * (log₂ log₂ a + 1)` for every pair `(x, y)`
whose pair complexity has the finite value `a`. -/
private lemma exists_plainK_add_condK_le_of_cPairVal (U U_pref : Map)
    (c_plain c_cond c_lower c_rem cNat c_proj c_exact c_log : ℕ)
    (hb : PrefixCouplingBounds U U_pref c_plain c_cond c_lower c_rem cNat c_proj
      c_exact c_log) :
    ∃ k : ℕ, ∀ (x y : BitString) (a : ℕ), cPair U x y = ↑a →
      plainK U x + condK U y x ≤ ↑a +
        ((3 * Nat.log 2 a + k * (Nat.log 2 (Nat.log 2 a) + 1) : ℕ) : ℕ∞) := by
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℕ, C0 = c_exact + c_rem + c_log + c_proj + 1 := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ : ∃ Cp : ℕ, Cp = 2 * Nat.log 2 (C0 + 12) + 8 := ⟨_, rfl⟩
  obtain ⟨C_const, hC_const⟩ : ∃ C : ℕ,
      C = C0 + c_lower + c_rem + c_plain + c_cond + cNat + Cp + 15 := ⟨_, rfl⟩
  refine ⟨C_const, fun x y a ha => ?_⟩
  have h_plain := hb.plain_le
  have h_cond := hb.cond_le
  have h_lower := hb.pair_chain_lower
  have h_rem := hb.cond_remove
  have h_nat := hb.natCode_le
  have h_proj := hb.left_le_pair
  have h_exact := hb.exact_length
  have h_log := hb.plain_le_length_add_log
  have h_kp_pair_bound := kp_pair_bound_of_cPairVal U U_pref c_exact c_rem c_log
    h_exact h_rem h_log x y a ha
  have h_kp_pair_top : KPPair U_pref x y ≠ ⊤ := by
    intro h_contra
    have h1 : (⊤ : ℕ∞) ≤ ↑(a + (Nat.bits a).length +
        2 * (Nat.bits (Nat.bits a).length).length + (c_exact + c_rem + c_log)) := by
      rw [← h_contra]
      exact h_kp_pair_bound
    exact ENat.coe_ne_top (a + (Nat.bits a).length +
        2 * (Nat.bits (Nat.bits a).length).length + (c_exact + c_rem + c_log))
      (top_unique h1)
  have h_kp_pair_bound_nat : (KPPair U_pref x y).toNat ≤
      a + (Nat.bits a).length + 2 * (Nat.bits (Nat.bits a).length).length +
      (c_exact + c_rem + c_log) :=
    ENat.toNat_le_of_le_coe h_kp_pair_bound
  have hKPxTop : KPPlain U_pref x ≠ ⊤ := by
    intro h_contra
    have h_proj_x := h_proj x y
    rw [h_contra] at h_proj_x
    have h_top_le : (⊤ : ℕ∞) ≤ ↑((KPPair U_pref x y).toNat + c_proj) := by
      calc (⊤ : ℕ∞) ≤ KPPair U_pref x y + ↑c_proj := h_proj_x
      _ = ↑(KPPair U_pref x y).toNat + ↑c_proj := by rw [ENat.coe_toNat h_kp_pair_top]
      _ = ↑((KPPair U_pref x y).toNat + c_proj) := by push_cast; rfl
    exact ENat.coe_ne_top ((KPPair U_pref x y).toNat + c_proj) (top_unique h_top_le)
  set p := (KPPlain U_pref x).toNat with hpdef
  have hpval_eq : ↑p = KPPlain U_pref x := ENat.coe_toNat hKPxTop
  have hp_proj := h_proj x y
  have hp_proj_nat : p ≤ (KPPair U_pref x y).toNat + c_proj := by
    have h1 : (↑p : ℕ∞) ≤ ↑((KPPair U_pref x y).toNat + c_proj) := by
      calc (↑p : ℕ∞) = KPPlain U_pref x := hpval_eq
      _ ≤ KPPair U_pref x y + ↑c_proj := hp_proj
      _ = ↑(KPPair U_pref x y).toNat + ↑c_proj := by rw [ENat.coe_toNat h_kp_pair_top]
      _ = ↑((KPPair U_pref x y).toNat + c_proj) := by push_cast; rfl
    exact WithTop.coe_le_coe.mp h1
  have hp_bound : p ≤ a + (Nat.bits a).length +
      2 * (Nat.bits (Nat.bits a).length).length + C0 := by
    subst hC0
    omega
  have hp_bits_len : 2 * (Nat.bits p).length ≤
      2 * Nat.log 2 a + (2 * Nat.log 2 (C0 + 12) + 8) :=
    nat_bits_length_p_bound a C0 p hp_bound
  have h_chain_nat := kp_chain_toNat U_pref c_lower h_lower x y p hpval_eq h_kp_pair_top
  have h_rem_y_nat := kp_rem_toNat U_pref c_rem h_rem x y p
    (kp_context_ne_top U_pref c_lower h_lower x y p hpval_eq h_kp_pair_top)
    (kpPlain_natCode_ne_top U_pref cNat h_nat p)
  have h_nat_p_nat : (KPPlain U_pref (natCode p)).toNat ≤
      2 * (Nat.bits p).length + cNat := by
    have h1 : KPPlain U_pref (natCode p) ≤ ↑(2 * (Nat.bits p).length + cNat) := h_nat p
    exact ENat.toNat_le_of_le_coe h1
  have h_plain_x := h_plain x
  have h_plain_nat : (plainK U x).toNat ≤ p + c_plain := by
    have h1 : plainK U x ≤ ↑(p + c_plain) := by
      calc plainK U x ≤ KPPlain U_pref x + ↑c_plain := h_plain_x
      _ = ↑p + ↑c_plain := by rw [← hpval_eq]
      _ = ↑(p + c_plain) := by push_cast; rfl
    exact ENat.toNat_le_of_le_coe h1
  have h_rem_y_top := kp_rem_ne_top U_pref c_lower c_rem cNat h_lower h_rem h_nat
    x y p hpval_eq h_kp_pair_top
  have h_cond_y := h_cond y x
  have h_cond_nat : (condK U y x).toNat ≤ (KP U_pref y x).toNat + c_cond := by
    have h1 : condK U y x ≤ ↑((KP U_pref y x).toNat + c_cond) := by
      calc condK U y x ≤ KP U_pref y x + ↑c_cond := h_cond_y
      _ = ↑(KP U_pref y x).toNat + ↑c_cond := by rw [ENat.coe_toNat h_rem_y_top]
      _ = ↑((KP U_pref y x).toNat + c_cond) := by push_cast; rfl
    exact ENat.toNat_le_of_le_coe h1
  have h_s1 : (Nat.bits a).length ≤ Nat.log 2 a + 1 := length_natBits_le_log a
  have h_s2 : 2 * (Nat.bits (Nat.bits a).length).length ≤ 2 * Nat.log 2 (Nat.log 2 a) + 6 :=
    nat_bits_length_log_log_bound a
  have hC_const_expanded : C_const = C0 + c_lower + c_rem + c_plain + c_cond + cNat +
      (2 * Nat.log 2 (C0 + 12) + 8) + 15 := by
    rw [hCp] at hC_const
    exact hC_const
  have h_s5 : (plainK U x).toNat + (condK U y x).toNat ≤
      a + 3 * Nat.log 2 a + C_const * (Nat.log 2 (Nat.log 2 a) + 1) := by
    have h1 : (plainK U x).toNat + (condK U y x).toNat ≤
        a + 3 * Nat.log 2 a + 2 * Nat.log 2 (Nat.log 2 a) + C_const := by omega
    have h2 : 2 * Nat.log 2 (Nat.log 2 a) + C_const ≤
        C_const * (Nat.log 2 (Nat.log 2 a) + 1) := by
      calc 2 * Nat.log 2 (Nat.log 2 a) + C_const
        _ ≤ C_const * Nat.log 2 (Nat.log 2 a) + C_const := by
          have : 2 ≤ C_const := by omega
          gcongr
        _ = C_const * (Nat.log 2 (Nat.log 2 a) + 1) := by ring
    omega
  have h_px : plainK U x ≠ ⊤ := by
    intro h_c
    have h1 : (⊤ : ℕ∞) ≤ ↑(p + c_plain) := by
      calc (⊤ : ℕ∞) = plainK U x := h_c.symm
      _ ≤ KPPlain U_pref x + ↑c_plain := h_plain x
      _ = ↑p + ↑c_plain := by rw [← hpval_eq]
      _ = ↑(p + c_plain) := by push_cast; rfl
    exact ENat.coe_ne_top (p + c_plain) (top_unique h1)
  have h_cy : condK U y x ≠ ⊤ := by
    intro h_c
    have h1 : (⊤ : ℕ∞) ≤ ↑((KP U_pref y x).toNat + c_cond) := by
      calc (⊤ : ℕ∞) = condK U y x := h_c.symm
      _ ≤ KP U_pref y x + ↑c_cond := h_cond y x
      _ = ↑(KP U_pref y x).toNat + ↑c_cond := by rw [ENat.coe_toNat h_rem_y_top]
      _ = ↑((KP U_pref y x).toNat + c_cond) := by push_cast; rfl
    exact ENat.coe_ne_top ((KP U_pref y x).toNat + c_cond) (top_unique h1)
  have h_sum_coe : plainK U x + condK U y x =
      ↑((plainK U x).toNat + (condK U y x).toNat) := by
    nth_rw 1 [← ENat.coe_toNat h_px]
    nth_rw 1 [← ENat.coe_toNat h_cy]
    push_cast
    rfl
  have h5_coe : ↑((plainK U x).toNat + (condK U y x).toNat) ≤
      ((a + 3 * Nat.log 2 a + C_const * (Nat.log 2 (Nat.log 2 a) + 1) : ℕ) : ℕ∞) := by
    exact_mod_cast h_s5
  have h_cast : ((a + 3 * Nat.log 2 a + C_const * (Nat.log 2 (Nat.log 2 a) + 1) : ℕ) : ℕ∞) =
      ↑a + ((3 * Nat.log 2 a + C_const * (Nat.log 2 (Nat.log 2 a) + 1) : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [h_sum_coe]
  rwa [h_cast] at h5_coe

/-- **Exercise 35.** Sharpened error term in the Kolmogorov–Levin theorem:
`C(x) + C(y | x) ≤ C(x, y) + 3 log C(x, y) + O(log log C(x, y))`. -/
theorem plainK_add_condK_le_plainK_pair_add_three_log (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      plainK U x + condK U y x ≤ cPair U x y +
        ((3 * Nat.log 2 (cPairVal U x y) +
          k * (Nat.log 2 (Nat.log 2 (cPairVal U x y)) + 1) : ℕ) : ℕ∞) := by
  obtain ⟨U_pref, hU_pref⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c_plain, h_plain⟩ := plain_le_prefix U U_pref hU hU_pref.isPrefixDecompressor
  obtain ⟨c_cond, h_cond⟩ := condK_le_KP U U_pref hU hU_pref.isPrefixDecompressor
  obtain ⟨c_lower, h_lower⟩ := KPPair_chain_lower U_pref hU_pref
  obtain ⟨c_rem, h_rem⟩ := KP_cond_remove_short_info U_pref hU_pref
  obtain ⟨cNat, h_nat⟩ := KPPlain_natCode_le_log U_pref hU_pref
  obtain ⟨c_proj, h_proj⟩ := KPPlain_left_le_KPPair U_pref hU_pref
  obtain ⟨c_exact, h_exact⟩ := KP_le_condK_given_plain_program_length U U_pref hU hU_pref
  obtain ⟨c_log, h_log⟩ := KPPlain_le_length_add_log U_pref hU_pref
  obtain ⟨k, hk⟩ := exists_plainK_add_condK_le_of_cPairVal U U_pref c_plain c_cond c_lower
    c_rem cNat c_proj c_exact c_log
    ⟨h_plain, h_cond, h_lower, h_rem, h_nat, h_proj, h_exact, h_log⟩
  refine ⟨k, fun x y => ?_⟩
  by_cases h_top : cPair U x y = ⊤
  · rw [h_top]; exact le_top
  · set a := cPairVal U x y
    have ha_eq : cPair U x y = ↑a := (ENat.coe_toNat h_top).symm
    rw [ha_eq]
    exact hk x y a ha_eq

open StagedEnumeration CodedFiniteDistribution

/-- Pad a bitstring to length `n` by appending `false`. -/
def padTo (n : ℕ) (bs : BitString) : BitString :=
  bs ++ List.replicate (n - bs.length) false

/-- Padding a string of length at most `n` with zeros gives a string of length `n`. -/
lemma length_padTo (n : ℕ) (bs : BitString) (h : bs.length ≤ n) :
    (padTo n bs).length = n := by
  dsimp [padTo]
  rw [List.length_append, List.length_replicate]
  omega

/-- Appending one zero bit does not change the number a string is read as. -/
lemma bitsToNat_append_single_false (bs : BitString) :
    bitsToNat (bs ++ [false]) = bitsToNat bs := by
  dsimp [bitsToNat]
  rw [List.foldr_append]
  rfl

end Kolmogorov
