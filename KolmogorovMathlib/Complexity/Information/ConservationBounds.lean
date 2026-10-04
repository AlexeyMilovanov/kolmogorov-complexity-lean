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
import Mathlib.Basic.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Information.RandomConservation

/-!
# Conservation of information

Information cannot be created, deterministically or probabilistically.
`relativized_conservation_compose` is the relativized deterministic statement, and
`levin_information_conservation` (SUV Exercise 59) the probabilistic one: for a uniformly
random `n`-bit `r`, the probability that `r` carries much information about a fixed string is
small.  Its core is `probabilistic_conservation_core`, restated in the book's form by
`probabilistic_conservation_book_form`.

`info_asymmetric_example` (Exercise 60) is the complementary example, showing the asymmetry of
the situation for an incompressible `x`.  `plainK_sub_le` — `C(a - d) ≤ C(a) + 2 C(d) + O(1)`,
by the decompressor `differenceDecompressor` — is the coding lemma used along the way.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution
variable (Q : ℕ × ℕ × BitString → Bool)

private theorem relativizedConservationDecompressor_isDecompressor (U : Map) (hU : isDecompressor U)
    (f : BitString × BitString →. BitString) (hf : Partrec f) :
    isDecompressor (relativizedConservationDecompressor U f) := by
  have h1 : Partrec (fun p : BitString × BitString =>
      f (decodeSecond p.2, decodeFirst p.2)) := by
    have hp : Computable (fun p : BitString × BitString =>
        (decodeSecond p.2, decodeFirst p.2)) :=
      Computable.pair (decodeSecond_computable.comp Computable.snd)
        (decodeFirst_computable.comp Computable.snd)
    exact Partrec.comp hf hp
  have h2 : Partrec (fun q : (BitString × BitString) × BitString =>
      U (q.1.1, q.2)) :=
    Partrec.comp hU (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  exact Partrec.bind h1 h2

/-- **Deterministic conservation, relativized.**  If `v` is one of the values of
the computable `f (x, r)`, then `C(y | ⟨r, x⟩) ≤ C(y | v) + O(1)`, with a
constant depending only on `f`. -/
theorem relativized_conservation_compose (U : Map) (hU : isOptimalConditional U)
    (f : BitString × BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ (x r v y : BitString), v ∈ f (x, r) →
      condK U y (pairCode r x) ≤ condK U y v + (c : ℕ∞) := by
  let D := relativizedConservationDecompressor U f
  have hD : isDecompressor D := relativizedConservationDecompressor_isDecompressor U hU.1 f hf
  obtain ⟨c, hc⟩ := hU.2 D hD
  refine ⟨c, ?_⟩
  intro x r v y hv
  calc condK U y (pairCode r x) ≤ condK D y (pairCode r x) + (c : ℕ∞) := hc y (pairCode r x)
    _ ≤ condK U y v + (c : ℕ∞) := by
        gcongr
        apply sInf_le_sInf
        rintro N ⟨p, hp, rfl⟩
        refine ⟨p, ?_, rfl⟩
        dsimp [D, relativizedConservationDecompressor, produces]
        rw [decodeFirst_pairCode, decodeSecond_pairCode, Part.mem_bind_iff]
        exact ⟨v, hv, hp⟩

/-- Decompressor for `plainK_sub_le`: the program is `pairCode qd qa`,
where `qd` computes `d` and `qa` computes `a`; the output is `a - d`. -/
def differenceDecompressor (U : Map) : Map :=
  fun p => (U (decodeFirst p.1, [])).bind (fun sd =>
    (U (decodeSecond p.1, [])).map (fun sa => Nat.bits (bitsToNat sa - bitsToNat sd)))

private theorem differenceDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (differenceDecompressor U) := by
  have h1 : Partrec (fun p : BitString × BitString => U (decodeFirst p.1, [])) := by
    have hp : Computable (fun p : BitString × BitString =>
        (decodeFirst p.1, ([] : BitString))) :=
      Computable.pair (decodeFirst_computable.comp Computable.fst) (Computable.const [])
    exact Partrec.comp hU hp
  have h2 : Partrec (fun q : (BitString × BitString) × BitString =>
      (U (decodeSecond q.1.1, [])).map
        (fun sa => Nat.bits (bitsToNat sa - bitsToNat q.2))) := by
    have hinner : Partrec (fun q : (BitString × BitString) × BitString =>
        U (decodeSecond q.1.1, ([] : BitString))) := by
      have hp : Computable (fun q : (BitString × BitString) × BitString =>
          (decodeSecond q.1.1, ([] : BitString))) :=
        Computable.pair
          (decodeSecond_computable.comp (Computable.fst.comp Computable.fst))
          (Computable.const [])
      exact Partrec.comp hU hp
    have hg : Computable₂ (fun (q : (BitString × BitString) × BitString) (sa : BitString) =>
        Nat.bits (bitsToNat sa - bitsToNat q.2)) := by
      have hsub : Computable (fun p : ((BitString × BitString) × BitString) × BitString =>
          bitsToNat p.2 - bitsToNat p.1.2) :=
        (Primrec₂.comp Primrec.nat_sub (bitsToNat_primrec.comp Primrec.snd)
          (bitsToNat_primrec.comp (Primrec.snd.comp Primrec.fst))).to_comp
      exact natBits_computable.comp hsub
    exact Partrec.map hinner hg
  exact Partrec.bind h1 h2

/-- **Complexity of a difference.**  `C(a - d) ≤ C(a) + 2 C(d) + O(1)`, where
naturals are coded by `Nat.bits`. -/
private theorem plainK_sub_le (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ (a d : ℕ),
      cVal U (Nat.bits (a - d)) ≤ cVal U (Nat.bits a) + 2 * cVal U (Nat.bits d) + k := by
  have plainKNeTopAux : ∀ (U : Map), isOptimalConditional U → ∀ (y : BitString),
      plainK U y ≠ ⊤ := by
    intro U hU y h
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    have h_le := hc y
    rw [h] at h_le
    cases h_le
  let D := differenceDecompressor U
  have hD : isDecompressor D := differenceDecompressor_isDecompressor U hU.1
  obtain ⟨c2, hc2⟩ := hU.2 D hD
  refine ⟨c2 + 1, ?_⟩
  intro a d
  have ha_top := plainKNeTopAux U hU (Nat.bits a)
  have hd_top := plainKNeTopAux U hU (Nat.bits d)
  have h_eq_a : plainK U (Nat.bits a) = (cVal U (Nat.bits a) : ℕ∞) :=
    (ENat.natCast_toNat ha_top).symm
  have h_eq_d : plainK U (Nat.bits d) = (cVal U (Nat.bits d) : ℕ∞) :=
    (ENat.natCast_toNat hd_top).symm
  have h_le_a : condK U (Nat.bits a) [] ≤ (cVal U (Nat.bits a) : ℕ∞) := by
    change plainK U (Nat.bits a) ≤ (cVal U (Nat.bits a) : ℕ∞)
    rw [h_eq_a]
  have h_le_d : condK U (Nat.bits d) [] ≤ (cVal U (Nat.bits d) : ℕ∞) := by
    change plainK U (Nat.bits d) ≤ (cVal U (Nat.bits d) : ℕ∞)
    rw [h_eq_d]
  rw [condK_le_iff] at h_le_a h_le_d
  obtain ⟨qa, hqa_len, hqa_prod⟩ := h_le_a
  obtain ⟨qd, hqd_len, hqd_prod⟩ := h_le_d
  change qa.length ≤ cVal U (Nat.bits a) at hqa_len
  change qd.length ≤ cVal U (Nat.bits d) at hqd_len
  have h_prod_D : produces D (pairCode qd qa) [] (Nat.bits (a - d)) := by
    dsimp [D, differenceDecompressor, produces]
    rw [decodeFirst_pairCode, decodeSecond_pairCode, Part.mem_bind_iff]
    refine ⟨Nat.bits d, hqd_prod, ?_⟩
    rw [Part.mem_map_iff]
    refine ⟨Nat.bits a, hqa_prod, ?_⟩
    rw [bitsToNat_bits, bitsToNat_bits]
  have h_D_le : plainK D (Nat.bits (a - d)) ≤ ((pairCode qd qa).length : ℕ∞) := by
    change condK D (Nat.bits (a - d)) [] ≤ ((pairCode qd qa).length : ℕ∞)
    rw [condK_le_iff]
    exact ⟨pairCode qd qa, le_rfl, h_prod_D⟩
  have h_len_bound : (pairCode qd qa).length ≤
      cVal U (Nat.bits a) + 2 * cVal U (Nat.bits d) + 1 := by
    rw [length_pairCode]
    omega
  have h_final : plainK U (Nat.bits (a - d)) ≤
      ((cVal U (Nat.bits a) + 2 * cVal U (Nat.bits d) + (c2 + 1) : ℕ) : ℕ∞) := by
    calc plainK U (Nat.bits (a - d)) ≤ plainK D (Nat.bits (a - d)) + (c2 : ℕ∞) :=
          hc2 (Nat.bits (a - d)) []
      _ ≤ ((pairCode qd qa).length : ℕ∞) + (c2 : ℕ∞) := by gcongr
      _ ≤ ((cVal U (Nat.bits a) + 2 * cVal U (Nat.bits d) + 1 : ℕ) : ℕ∞) + (c2 : ℕ∞) := by
          gcongr
      _ = ((cVal U (Nat.bits a) + 2 * cVal U (Nat.bits d) + (c2 + 1) : ℕ) : ℕ∞) := by
          push_cast
          ring
  have hsub_top := plainKNeTopAux U hU (Nat.bits (a - d))
  rw [← ENat.natCast_toNat hsub_top] at h_final
  exact_mod_cast h_final

open Classical in
/-- **Core of Exercise 59.**  If, among the `n`-bit strings `r`, the fraction of
those for which some value `v` of `f (x, r)` satisfies `I (v : y) > I (x : y) + l`
is at least `2 ^ (-l'')`, then `l ≤ l'' + 2 C(n) + 2 C(l'') + O(1)`.

This is the conditional Problem 41 (`hA`) combined with the relativized
deterministic conservation `relativized_conservation_compose` and two applications of
`condK_le_condK_pair_add_two_plainK`. -/
private theorem probabilistic_conservation_core (U : Map) (hU : isOptimalConditional U)
    (f : BitString × BitString →. BitString) (hf : Partrec f)
    (hA : ∃ c : ℕ, ∀ (x y : BitString) (n k l : ℕ),
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ l *
          (((allStrings n).filter
            (fun r => decide (condK U y (pairCode r x) ≤ (k : ℕ∞)))).length : ℝ) →
        condK U y (pairCode (Nat.bits n) (pairCode (Nat.bits l) x)) ≤ ((k + l + c : ℕ) : ℕ∞)) :
    ∃ c : ℕ, ∀ (x y : BitString) (n l l'' : ℕ),
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ l'' *
        ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
            info U x y + (l : ℤ) < info U v y))).length : ℝ)) →
        l ≤ l'' + 2 * cVal U (Nat.bits n) + 2 * cVal U (Nat.bits l'') + c := by
  have condKNeTopAux : ∀ (U : Map), isOptimalConditional U → ∀ (x y : BitString),
      condK U x y ≠ ⊤ := by
    intro U hU x y h
    obtain ⟨c, hc⟩ := condK_le_plainK U hU
    have h_le := hc x y
    have h_plain : plainK U x ≠ ⊤ := by
      obtain ⟨c', hc'⟩ := plainK_le_length U hU
      have h_le' := hc' x
      intro h'
      rw [h'] at h_le'
      cases h_le'
    have h_top_le : (⊤ : ℕ∞) ≤ plainK U x + (c : ℕ∞) := by
      calc (⊤ : ℕ∞) = condK U x y := h.symm
      _             ≤ plainK U x + (c : ℕ∞) := h_le
    have hc_ne : (c : ℕ∞) ≠ ⊤ := WithTop.coe_ne_top
    have hsum : plainK U x + (c : ℕ∞) ≠ ⊤ := WithTop.add_ne_top.mpr ⟨h_plain, hc_ne⟩
    exact hsum (top_unique h_top_le)
  obtain ⟨cA, hcA⟩ := hA
  obtain ⟨cB, hcB⟩ := condK_le_condK_pair_add_two_plainK U hU
  obtain ⟨cC, hcC⟩ := relativized_conservation_compose U hU f hf
  refine ⟨cA + cC + 2 * cB, ?_⟩
  intro x y n l l'' hcount
  -- the event list is nonempty
  set Finfo := (allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
      info U x y + (l : ℤ) < info U v y)) with hFinfo
  have hpos : 0 < Finfo.length := by
    by_contra hzero
    have hz : Finfo.length = 0 := by omega
    rw [hz] at hcount
    simp only [Nat.cast_zero, mul_zero] at hcount
    have : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    linarith
  obtain ⟨r₀, hr₀⟩ := List.exists_mem_of_length_pos hpos
  -- from any member of the event list we read off the complexity gap
  have hevent : ∀ r ∈ Finfo, ∃ v ∈ f (x, r), condCVal U y v + l < condCVal U y x := by
    intro r hr
    rw [hFinfo, List.mem_filter] at hr
    obtain ⟨v, hv, hlt⟩ := of_decide_eq_true hr.2
    refine ⟨v, hv, ?_⟩
    have h1 : info U x y = (cVal U y : ℤ) - (condCVal U y x : ℤ) := rfl
    have h2 : info U v y = (cVal U y : ℤ) - (condCVal U y v : ℤ) := rfl
    rw [h1, h2] at hlt
    have : (condCVal U y v : ℤ) + (l : ℤ) < (condCVal U y x : ℤ) := by linarith
    exact_mod_cast this
  obtain ⟨v₀, _, hgap₀⟩ := hevent r₀ hr₀
  obtain ⟨k0, hk0⟩ : ∃ k0, condCVal U y x = k0 + l + 1 :=
    ⟨condCVal U y x - l - 1, by omega⟩
  -- every member of the event list gives a short program for `y` from `⟨r, x⟩`
  have hshort : ∀ r ∈ Finfo, condK U y (pairCode r x) ≤ ((k0 + cC : ℕ) : ℕ∞) := by
    intro r hr
    obtain ⟨v, hv, hgap⟩ := hevent r hr
    have hvtop := condKNeTopAux U hU y v
    have hveq : condK U y v = ((condCVal U y v : ℕ) : ℕ∞) := (ENat.natCast_toNat hvtop).symm
    have hbound : condCVal U y v ≤ k0 := by omega
    calc condK U y (pairCode r x) ≤ condK U y v + (cC : ℕ∞) := hcC x r v y hv
      _ = ((condCVal U y v : ℕ) : ℕ∞) + (cC : ℕ∞) := by rw [hveq]
      _ ≤ ((k0 : ℕ) : ℕ∞) + (cC : ℕ∞) := by
          gcongr
      _ = ((k0 + cC : ℕ) : ℕ∞) := by push_cast; ring
  -- hence the `condK`-filter is at least as long
  have hlen_le : Finfo.length ≤
      ((allStrings n).filter
        (fun r => decide (condK U y (pairCode r x) ≤ ((k0 + cC : ℕ) : ℕ∞)))).length := by
    rw [hFinfo]
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply list_countP_mono
    intro r hr hdec
    refine decide_eq_true (hshort r ?_)
    rw [hFinfo, List.mem_filter]
    exact ⟨hr, hdec⟩
  -- feed the conditional Problem 41
  have hA_hyp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ l'' *
      (((allStrings n).filter
        (fun r => decide (condK U y (pairCode r x) ≤ ((k0 + cC : ℕ) : ℕ∞)))).length : ℝ) := by
    refine le_trans hcount ?_
    gcongr
  have hA_out := hcA x y n (k0 + cC) l'' hA_hyp
  -- drop the two extra conditions
  have hdrop1 : condK U y (pairCode (Nat.bits l'') x) ≤
      condK U y (pairCode (Nat.bits n) (pairCode (Nat.bits l'') x)) +
        ((2 * cVal U (Nat.bits n) + cB : ℕ) : ℕ∞) :=
    hcB y (Nat.bits n) (pairCode (Nat.bits l'') x)
  have hdrop2 : condK U y x ≤
      condK U y (pairCode (Nat.bits l'') x) + ((2 * cVal U (Nat.bits l'') + cB : ℕ) : ℕ∞) :=
    hcB y (Nat.bits l'') x
  have hchain : condK U y x ≤
      ((k0 + cC + l'' + cA + (2 * cVal U (Nat.bits n) + cB) +
        (2 * cVal U (Nat.bits l'') + cB) : ℕ) : ℕ∞) := by
    calc condK U y x
        ≤ condK U y (pairCode (Nat.bits l'') x) +
            ((2 * cVal U (Nat.bits l'') + cB : ℕ) : ℕ∞) := hdrop2
      _ ≤ (condK U y (pairCode (Nat.bits n) (pairCode (Nat.bits l'') x)) +
            ((2 * cVal U (Nat.bits n) + cB : ℕ) : ℕ∞)) +
            ((2 * cVal U (Nat.bits l'') + cB : ℕ) : ℕ∞) := by gcongr
      _ ≤ (((k0 + cC + l'' + cA : ℕ) : ℕ∞) +
            ((2 * cVal U (Nat.bits n) + cB : ℕ) : ℕ∞)) +
            ((2 * cVal U (Nat.bits l'') + cB : ℕ) : ℕ∞) := by gcongr
      _ = ((k0 + cC + l'' + cA + (2 * cVal U (Nat.bits n) + cB) +
            (2 * cVal U (Nat.bits l'') + cB) : ℕ) : ℕ∞) := by push_cast; ring
  have hxtop := condKNeTopAux U hU y x
  rw [← ENat.natCast_toNat hxtop] at hchain
  have hnat : condCVal U y x ≤
      k0 + cC + l'' + cA + (2 * cVal U (Nat.bits n) + cB) +
        (2 * cVal U (Nat.bits l'') + cB) := by exact_mod_cast hchain
  omega

private lemma probabilistic_conservation_log_mul_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  have h1 : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
  have h2 : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self (by norm_num) b
  have h3 : a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
    Nat.mul_lt_mul_of_lt_of_lt h1 h2
  have h4 : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    rw [← pow_add] at h3
    have he : Nat.log 2 a + 1 + (Nat.log 2 b + 1) = Nat.log 2 a + Nat.log 2 b + 2 := by omega
    rwa [he] at h3
  have h5 : a * b ≠ 0 := by positivity
  have := Nat.log_lt_of_lt_pow h5 h4
  omega

open Classical in
/-- **Exercise 59, the book's form.**  For a uniformly random `n`-bit `r` the
probability of the event `I (f (x, r) : y) > I (x : y) + l` is at most
`2 ^ (-l + O (C n + C l))`.

This is the statement of Problem 59 on p. 45 of Shen–Uspensky–Vereshchagin,
whose exponent is `2 ^ (-l + O(C(n) + C(l)))`.  The summand `C l` is necessary:
see `information_conservation_Cn_only_exponent_false`. -/
private theorem probabilistic_conservation_book_form (U : Map) (hU : isOptimalConditional U)
    (f : BitString × BitString →. BitString) (hf : Partrec f)
    (hA : ∃ c : ℕ, ∀ (x y : BitString) (n k l : ℕ),
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ l *
          (((allStrings n).filter
            (fun r => decide (condK U y (pairCode r x) ≤ (k : ℕ∞)))).length : ℝ) →
        condK U y (pairCode (Nat.bits n) (pairCode (Nat.bits l) x)) ≤ ((k + l + c : ℕ) : ℕ∞)) :
    ∃ c : ℕ, ∀ (x y : BitString) (n l : ℕ),
      ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
            info U x y + (l : ℤ) < info U v y))).length : ℝ)) / (2 : ℝ) ^ n
        ≤ (2 : ℝ) ^ (-(l : ℤ) + (c : ℤ) *
            ((cVal U (Nat.bits n) : ℤ) + (cVal U (Nat.bits l) : ℤ) + 1)) := by
  obtain ⟨c₀, hc₀⟩ := probabilistic_conservation_core U hU f hf hA
  obtain ⟨cD, hcD⟩ := plainK_sub_le U hU
  obtain ⟨c_len, hc_len⟩ := plainK_le_length U hU
  have hCle : ∀ s : BitString, cVal U s ≤ s.length + c_len := by
    intro s
    have hne : plainK U s ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top _⟩)
        (hc_len s)
    have h := hc_len s
    rw [← ENat.natCast_toNat hne] at h
    exact_mod_cast h
  -- the constant
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = 8 + 4 * c_len + 2 * cD + c₀ := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ, c = 2 ^ (E + 20) := ⟨_, rfl⟩
  have hlogc : Nat.log 2 c = E + 20 := by rw [hcdef]; exact Nat.log_pow (by norm_num) _
  have hcbig : 5 * E + 100 ≤ c := by
    obtain ⟨X, hX⟩ : ∃ X : ℕ, X = 2 ^ E := ⟨_, rfl⟩
    have hXge : E + 1 ≤ X := by rw [hX]; exact Nat.lt_two_pow_self
    have hcX : c = 1048576 * X := by
      rw [hcdef, hX, pow_add]
      ring
    omega
  clear hcdef
  refine ⟨c, ?_⟩
  intro x y n l
  obtain ⟨Cn, hCn⟩ : ∃ a : ℕ, a = cVal U (Nat.bits n) := ⟨_, rfl⟩
  obtain ⟨Cl, hCl⟩ : ∃ a : ℕ, a = cVal U (Nat.bits l) := ⟨_, rfl⟩
  obtain ⟨A, hA'⟩ : ∃ a : ℕ, a = Cn + Cl + 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ a : ℕ, a = c * A := ⟨_, rfl⟩
  have hApos : 0 < A := by omega
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hexp_nat : (c : ℤ) * ((cVal U (Nat.bits n) : ℤ) + (cVal U (Nat.bits l) : ℤ) + 1)
      = (T : ℤ) := by
    rw [← hCn, ← hCl, hT, hA']
    push_cast
    ring
  rw [hexp_nat]
  have hFle : ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
      info U x y + (l : ℤ) < info U v y))).length : ℕ)) ≤ 2 ^ n := by
    calc ((allStrings n).filter _).length ≤ (allStrings n).length := List.length_filter_le _ _
      _ = 2 ^ n := length_allStrings n
  by_cases hlT : l ≤ T
  · -- the bound is at least `1`
    have hLHS : ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
        info U x y + (l : ℤ) < info U v y))).length : ℝ)) / (2 : ℝ) ^ n ≤ 1 := by
      rw [div_le_one h2n]
      exact_mod_cast hFle
    have hnn : (0 : ℤ) ≤ -(l : ℤ) + (T : ℤ) := by
      have : (l : ℤ) ≤ (T : ℤ) := by exact_mod_cast hlT
      omega
    have hRHS : (1 : ℝ) ≤ (2 : ℝ) ^ (-(l : ℤ) + (T : ℤ)) := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnn
      simpa using h
    linarith
  · push Not at hlT
    by_contra hgt
    push Not at hgt
    obtain ⟨l'', hl''⟩ : ∃ a : ℕ, a = l - T := ⟨_, rfl⟩
    have hexp_eq : -(l : ℤ) + (T : ℤ) = -((l'' : ℕ) : ℤ) := by
      have : (l'' : ℤ) = (l : ℤ) - (T : ℤ) := by
        rw [hl'']
        push_cast [Nat.cast_sub (le_of_lt hlT)]
        ring
      omega
    rw [hexp_eq] at hgt
    have hzp : (2 : ℝ) ^ (-((l'' : ℕ) : ℤ)) = ((2 : ℝ) ^ (l'' : ℕ))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [hzp] at hgt
    have hl2 : (0 : ℝ) < (2 : ℝ) ^ (l'' : ℕ) := by positivity
    rw [inv_eq_one_div, div_lt_div_iff₀ hl2 h2n] at hgt
    have hcore_hyp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (l'' : ℕ) *
        ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
          info U x y + (l : ℤ) < info U v y))).length : ℝ)) := by
      have hmul : (2 : ℝ) ^ n < ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
          info U x y + (l : ℤ) < info U v y))).length : ℝ)) * (2 : ℝ) ^ (l'' : ℕ) := by
        linarith
      calc (2 : ℝ) ^ n ≤ ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
            info U x y + (l : ℤ) < info U v y))).length : ℝ)) * (2 : ℝ) ^ (l'' : ℕ) :=
            le_of_lt hmul
        _ = (2 : ℝ) ^ (l'' : ℕ) * ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
              info U x y + (l : ℤ) < info U v y))).length : ℝ)) := by ring
    have hres := hc₀ x y n l l'' hcore_hyp
    -- now the arithmetic
    have hsub : cVal U (Nat.bits l'') ≤ Cl + 2 * cVal U (Nat.bits T) + cD := by
      have := hcD l T
      rw [← hl''] at this
      omega
    have hCT : cVal U (Nat.bits T) ≤ Nat.log 2 T + 1 + c_len := by
      have h1 := hCle (Nat.bits T)
      have h2 := length_natBits_le_log T
      omega
    have hlogT : Nat.log 2 T ≤ Nat.log 2 c + A + 1 := by
      have hcpos : 0 < c := by omega
      have h1 : Nat.log 2 T ≤ Nat.log 2 c + Nat.log 2 A + 1 := by
        rw [hT]
        exact probabilistic_conservation_log_mul_le c A hcpos hApos
      have h2 : Nat.log 2 A ≤ A := Nat.log_le_self 2 A
      omega
    have hmulraw : (5 * E + 100) * A ≤ T := by
      rw [hT]
      exact Nat.mul_le_mul_right A hcbig
    have hl_eq : l = l'' + T := by omega
    have hCn' : cVal U (Nat.bits n) = Cn := hCn.symm
    rw [hCn'] at hres
    clear hT hcore_hyp hgt hexp_eq hzp
    have hderived : T ≤ 6 * A + 5 * E + 78 := by omega
    obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = 5 * E * A := ⟨_, rfl⟩
    have hEA : 5 * E ≤ Q := by
      rw [hQ]
      have h := Nat.mul_le_mul_left (5 * E) hApos
      simpa using h
    have hmul2 : Q + 100 * A ≤ T := by
      have h2 : (5 * E + 100) * A = Q + 100 * A := by rw [hQ]; ring
      rw [h2] at hmulraw
      exact hmulraw
    omega

open Classical in
/-- **Exercise 59.** Probabilistic conservation of information: for a uniformly
random `n`-bit `r`, the probability that `I(f (x, r) : y) > I(x : y) + l` is at
most `2 ^ (-l + O(C n + C l))`, with the constant depending on `f` only.  This is
Levin's conservation law; the book states it on p. 45 and cites [100].

Both terms in the exponent are necessary, and this statement has been wrong twice.

* With `O(1)` in place of `O(C n + C l)` it is false: take `f (x, r) = r`,
  `x = []`, `y = Nat.bits n`.  Then `I(x : y) = 0`, while every `r` of length `n`
  determines `n` and hence `y`, so `I(f (x, r) : y) = C n - O(1)` for *every* `r`
  of length `n` -- the event has probability `1` whenever `l < C n - O(1)`, and
  `C n` is unbounded.  The randomness hands the algorithm the number `n` for free.
* With `O(C n)` alone it is still false, and `information_conservation_Cn_only_exponent_false`
  below refutes it in Lean.  The witness is again `f (x, r) = r` and `x = []`, now
  with `n = 2 ^ m`: among the strings `pairCode (Nat.bits k) w` with `k < n` and
  `|w| = n - 1` -- each produced from `2 ^ (k + 1)` of the conditions `r` by a
  program of length `k` -- some `y` has `C y >= n - 2 + m`, and taking
  `l = C y - k - O(1)` forces `C y <= n + O(C n)`.  Since `C (2 ^ m) = O(log m)`
  while `m` is unbounded, that fails; the gap is exactly the missing `C l`.

The book's `O(C(n) + C(l))` is read here as `c * (C n + C l + 1)`. -/
theorem levin_information_conservation (U : Map) (hU : isOptimalConditional U)
    (f : BitString × BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ (x y : BitString) (n l : ℕ),
      ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
            info U x y + (l : ℤ) < info U v y))).length : ℝ)) / (2 : ℝ) ^ n
        ≤ (2 : ℝ) ^ (-(l : ℤ) + (c : ℤ) *
            ((cVal U (Nat.bits n) : ℤ) + (cVal U (Nat.bits l) : ℤ) + 1)) :=
  probabilistic_conservation_book_form U hU f hf (randomPair_probability_bound U hU)

/-- **Exercise 60.** The asymmetric example: for `x` of length `n` incompressible
relative to `n`, `I(x : n) = C(n) + O(1)` while `I(n : x) = O(1)`. -/
theorem info_asymmetric_example (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : BitString), x.length = n → (n : ℕ∞) ≤ condK U x (Nat.bits n) →
      |info U x (Nat.bits n) - (cVal U (Nat.bits n) : ℤ)| ≤ (c : ℤ) ∧
        |info U (Nat.bits n) x| ≤ (c : ℤ) := by
  obtain ⟨c_f, hc_f⟩ := condK_comp U hU (fun x => Nat.bits x.length)
    (natBits_computable.comp Computable.list_length)
  obtain ⟨c_len, hc_len⟩ := plainK_le_length U hU
  obtain ⟨c_drop, hc_drop⟩ := condK_le_plainK U hU
  let c := max c_f (max c_len c_drop)
  use c
  intro n x hlen hincomp
  have h_ne_top : condK U x (Nat.bits n) ≠ ⊤ := by
    have hbound : condK U x (Nat.bits n) ≤ ((x.length + c_len + c_drop : ℕ) : ℕ∞) := by
      calc condK U x (Nat.bits n) ≤ plainK U x + (c_drop : ℕ∞) := hc_drop x (Nat.bits n)
      _ ≤ ((x.length : ℕ) : ℕ∞) + (c_len : ℕ∞) + (c_drop : ℕ∞) := by gcongr; exact hc_len x
      _ = ((x.length + c_len + c_drop : ℕ) : ℕ∞) := by push_cast; rfl
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbound
  have h_plainK_ne_top : plainK U x ≠ ⊤ := by
    have hbound : plainK U x ≤ ((x.length + c_len : ℕ) : ℕ∞) := by
      have h1 := hc_len x
      dsimp [programLength] at h1
      exact h1
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbound
  have h_f_x : condK U (Nat.bits n) x ≤ (c_f : ℕ∞) := by
    have h_comp := hc_f x
    rw [hlen] at h_comp
    exact h_comp
  have h_condCVal_bits : condCVal U (Nat.bits n) x ≤ c_f := by
    dsimp [condCVal]
    exact ENat.toNat_le_of_le_natCast h_f_x
  have h_cVal_x : cVal U x ≤ n + c_len := by
    dsimp [cVal]
    have h1 := hc_len x
    dsimp [programLength] at h1
    rw [hlen] at h1
    exact ENat.toNat_le_of_le_natCast h1
  have h_n_le_condCVal : n ≤ condCVal U x (Nat.bits n) := by
    dsimp [condCVal]
    have h_eq : condK U x (Nat.bits n) = ((condK U x (Nat.bits n)).toNat : ℕ∞) :=
      (ENat.natCast_toNat h_ne_top).symm
    have hincomp' := hincomp
    rw [h_eq] at hincomp'
    exact_mod_cast hincomp'
  have h_condCVal_le_cVal : condCVal U x (Nat.bits n) ≤ cVal U x + c_drop := by
    dsimp [condCVal, cVal]
    have h1 := hc_drop x (Nat.bits n)
    have h_eq : plainK U x = ((plainK U x).toNat : ℕ∞) := (ENat.natCast_toNat h_plainK_ne_top).symm
    rw [h_eq] at h1
    have h_sum : ((plainK U x).toNat : ℕ∞) + (c_drop : ℕ∞) =
        (((plainK U x).toNat + c_drop : ℕ) : ℕ∞) := by push_cast; rfl
    rw [h_sum] at h1
    exact ENat.toNat_le_of_le_natCast h1
  have h_part1 : |info U x (Nat.bits n) - (cVal U (Nat.bits n) : ℤ)| ≤ (c : ℤ) := by
    dsimp [info]
    have : (cVal U (Nat.bits n) : ℤ) - (condCVal U (Nat.bits n) x : ℤ) - (cVal U (Nat.bits n) : ℤ) =
        - (condCVal U (Nat.bits n) x : ℤ) := by ring
    rw [this, abs_neg, abs_of_nonneg (by positivity)]
    have : condCVal U (Nat.bits n) x ≤ c := le_trans h_condCVal_bits (le_max_left _ _)
    exact_mod_cast this
  have h_part2 : |info U (Nat.bits n) x| ≤ (c : ℤ) := by
    dsimp [info]
    have h_upper : (cVal U x : ℤ) - (condCVal U x (Nat.bits n) : ℤ) ≤ (c : ℤ) := by
      have h_le : cVal U x ≤ condCVal U x (Nat.bits n) + c := by
        calc cVal U x ≤ n + c_len := h_cVal_x
        _ ≤ condCVal U x (Nat.bits n) + c_len := Nat.add_le_add_right h_n_le_condCVal _
        _ ≤ condCVal U x (Nat.bits n) + c := by
          gcongr; exact le_trans (le_max_left _ _) (le_max_right _ _)
      linarith
    have h_lower : - (c : ℤ) ≤ (cVal U x : ℤ) - (condCVal U x (Nat.bits n) : ℤ) := by
      have h_le : condCVal U x (Nat.bits n) ≤ cVal U x + c := by
        calc condCVal U x (Nat.bits n) ≤ cVal U x + c_drop := h_condCVal_le_cVal
        _ ≤ cVal U x + c := by gcongr; exact le_trans (le_max_right _ _) (le_max_right _ _)
      linarith
    rw [abs_le]
    exact ⟨h_lower, h_upper⟩
  exact ⟨h_part1, h_part2⟩

private lemma sum_indicator_bound (M : ℕ) (z : ℤ) (hz : z ≤ (M : ℤ)) :
    (z : ℝ) ≤ ∑ k ∈ Finset.range M, if (k : ℤ) + 1 ≤ z then (1 : ℝ) else 0 := by
  by_cases hz0 : z ≤ 0
  · calc (z : ℝ) ≤ 0 := by exact_mod_cast hz0
    _ ≤ ∑ k ∈ Finset.range M, if (k : ℤ) + 1 ≤ z then (1 : ℝ) else 0 := by
      apply Finset.sum_nonneg
      intro i _
      split_ifs <;> positivity
  · push Not at hz0
    lift z to ℕ using by omega
    have hzM : z ≤ M := by omega
    have h1 : ∑ k ∈ Finset.range z, (if (k : ℤ) + 1 ≤ (z : ℤ) then (1 : ℝ) else 0) = (z : ℝ) := by
      have : ∀ k ∈ Finset.range z, (if (k : ℤ) + 1 ≤ (z : ℤ) then (1 : ℝ) else 0) = 1 := by
        intro k hk
        rw [Finset.mem_range] at hk
        have h_cond : (k : ℤ) + 1 ≤ (z : ℤ) := by omega
        rw [ite_eq_left h_cond]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have h2 : ∑ k ∈ Finset.Ico z M, (if (k : ℤ) + 1 ≤ (z : ℤ) then (1 : ℝ) else 0) = 0 := by
      have : ∀ k ∈ Finset.Ico z M, (if (k : ℤ) + 1 ≤ (z : ℤ) then (1 : ℝ) else 0) = 0 := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        have h_cond : ¬ ((k : ℤ) + 1 ≤ (z : ℤ)) := by omega
        rw [ite_eq_right h_cond]
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
    rw [← Finset.sum_range_add_sum_Ico _ hzM, h1, h2, add_zero]
    rfl

private lemma sum_pow_two_reverse (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 : ℝ) ^ (n - j) + 2 = (2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h_split : ∑ j ∈ Finset.range n, (2 : ℝ) ^ (n + 1 - j) =
        2 * ∑ j ∈ Finset.range n, (2 : ℝ) ^ (n - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have : n + 1 - j = (n - j) + 1 := by omega
      rw [this, pow_succ']
    have h_self : n + 1 - n = 1 := by omega
    rw [h_split, h_self, pow_one]
    calc 2 * ∑ j ∈ Finset.range n, (2 : ℝ) ^ (n - j) + 2 + 2
      _ = 2 * (∑ j ∈ Finset.range n, (2 : ℝ) ^ (n - j) + 2) := by ring
      _ = 2 * (2 : ℝ) ^ (n + 1) := by rw [ih]
      _ = (2 : ℝ) ^ (n + 1 + 1) := by ring

private lemma list_sum_eq_finset_sum {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup)
    (f : α → ℝ) :
    (l.map f).sum = ∑ y ∈ l.toFinset, f y := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    have ha : a ∉ l.toFinset := by
      intro h
      exact hl.1 (List.mem_toFinset.mp h)
    rw [Finset.sum_insert ha, ih hl.2]

private lemma sum_Ico_shift (n c : ℕ) :
    ∑ k ∈ Finset.Ico c (c + n), (2 : ℝ) ^ (c + n - k) =
      ∑ j ∈ Finset.range n, (2 : ℝ) ^ (n - j) := by
  have h_add := Finset.sum_Ico_add (fun k => (2 : ℝ) ^ (c + n - k)) 0 n c
  have h_0c : 0 + c = c := by omega
  have h_nc : n + c = c + n := by omega
  rw [h_0c, h_nc] at h_add
  rw [← h_add, Finset.range_eq_Ico]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  omega

/-- **Exercise 61.** For a uniformly random `n`-bit `y` the expected mutual
information with a fixed `x` of length at most `n` is `O(log n)`. -/
theorem expected_info_le_log (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : BitString), x.length ≤ n →
      (((allStrings n).map (fun y => (info U x y : ℝ))).sum) / (2 : ℝ) ^ n
        ≤ ((logSlack c n : ℕ) : ℝ) := by
  obtain ⟨c_plain, hc_plain⟩ := plainK_le_length U hU
  use c_plain + 2
  intro n x _hx
  have h_len : (allStrings n).length = 2 ^ n := length_allStrings n
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h_cplain_slack : (c_plain + 2 : ℝ) ≤ ((logSlack (c_plain + 2) n : ℕ) : ℝ) := by
    unfold logSlack
    have : c_plain + 2 ≤ (c_plain + 2) * (Nat.bits n).length + (c_plain + 2) := by omega
    exact_mod_cast this
  rw [div_le_iff₀ h_pow_pos]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h_cplain_slack (by positivity))
  rw [mul_comm]
  -- Change list sum to finset sum
  have h_sum_eq : ((allStrings n).map (fun y => (info U x y : ℝ))).sum =
      ∑ y ∈ (allStrings n).toFinset, (info U x y : ℝ) :=
        list_sum_eq_finset_sum (allStrings n) (allStrings_nodup n) _
  rw [h_sum_eq]
  have h_info_bound (y : BitString) (hy : y ∈ (allStrings n).toFinset) :
      (info U x y : ℝ) ≤ ∑ k ∈ Finset.range (n + c_plain),
        if (k : ℤ) + 1 ≤ (n + c_plain : ℤ) - (condCVal U y x : ℤ) then (1 : ℝ) else 0 := by
    rw [List.mem_toFinset, mem_allStrings] at hy
    have h_plain := hc_plain y
    have hy_prog : (programLength y : ℕ∞) = (n : ℕ∞) := by
      exact_mod_cast hy
    rw [hy_prog] at h_plain
    have h_cval : cVal U y ≤ n + c_plain := by
      unfold cVal
      exact ENat.toNat_le_of_le_natCast h_plain
    have h_info_le : (info U x y : ℝ) ≤ (((n + c_plain : ℤ) - (condCVal U y x : ℤ) : ℤ) : ℝ) := by
      unfold info
      push_cast
      have : (cVal U y : ℝ) ≤ (n + c_plain : ℝ) := by exact_mod_cast h_cval
      linarith
    exact h_info_le.trans
      (sum_indicator_bound (n + c_plain) ((n + c_plain : ℤ) - (condCVal U y x : ℤ)) (by omega))
  have h_sum_le := Finset.sum_le_sum h_info_bound
  refine h_sum_le.trans ?_
  rw [Finset.sum_comm]
  have h_add_n : n + c_plain = c_plain + n := by omega
  rw [h_add_n]
  have h_inner (k : ℕ) (hk : k ∈ Finset.range (c_plain + n)) :
      (∑ y ∈ (allStrings n).toFinset,
        if (k : ℤ) + 1 ≤ (n + c_plain : ℤ) - (condCVal U y x : ℤ) then (1 : ℝ) else 0) ≤
      (if k < c_plain then (2 : ℝ) ^ n else (2 : ℝ) ^ (c_plain + n - k)) := by
    rw [Finset.mem_range] at hk
    have h_filter : (∑ y ∈ (allStrings n).toFinset,
          if (k : ℤ) + 1 ≤ (n + c_plain : ℤ) - (condCVal U y x : ℤ) then (1 : ℝ) else 0) =
        (((allStrings n).toFinset.filter
          (fun y => (k : ℤ) + 1 ≤ (n + c_plain : ℤ) - (condCVal U y x : ℤ))).card : ℝ) := by
      exact Finset.sum_boole _ _
    rw [h_filter]
    by_cases hkc : k < c_plain
    · rw [ite_eq_left hkc]
      have h_card_le : ((allStrings n).toFinset.filter
          (fun y => (k : ℤ) + 1 ≤ (n + c_plain : ℤ) - (condCVal U y x : ℤ))).card ≤
          (allStrings n).toFinset.card := Finset.card_filter_le _ _
      rw [List.toFinset_card_of_nodup (allStrings_nodup n), h_len] at h_card_le
      exact_mod_cast h_card_le
    · push Not at hkc
      rw [ite_eq_right (not_lt.mpr hkc)]
      have hm_eq : c_plain + n - k = (n + c_plain - k - 1) + 1 := by
        have : k < c_plain + n := hk
        have : c_plain ≤ k := hkc
        omega
      rw [hm_eq]
      set m := n + c_plain - k - 1
      have h_sub : (allStrings n).toFinset.filter
          (fun y => (k : ℤ) + 1 ≤ (n + c_plain : ℤ) - (condCVal U y x : ℤ)) ⊆
          compressibleWords U x m := by
        intro y hy
        rw [mem_compressibleWords_iff]
        have h_mem := Finset.mem_filter.mp hy
        have h_ineq : (k : ℤ) + 1 ≤ (n + c_plain : ℤ) - (condCVal U y x : ℤ) := h_mem.2
        have h_in : y ∈ (allStrings n).toFinset := h_mem.1
        have h_cond_le : condCVal U y x ≤ m := by
          have h_m_eq : m = n + c_plain - (k + 1) := rfl
          rw [h_m_eq]
          have h_k1_le : k + 1 ≤ n + c_plain := by omega
          have h_sub_nat : (n + c_plain - (k + 1) : ℤ) =
              (n + c_plain : ℤ) - ((k : ℤ) + 1) := by exact_mod_cast Nat.sub_sub (n + c_plain) k 1
          have : (condCVal U y x : ℤ) ≤ (n + c_plain - (k + 1) : ℤ) := by
            rw [h_sub_nat]
            omega
          exact_mod_cast this
        have h_top : condK U y x ≠ ⊤ := by
          obtain ⟨c_cond, hc_cond⟩ := condK_le_plainK U hU
          have h1 := hc_cond y x
          have h2 := hc_plain y
          have hy1 := h_in
          rw [List.mem_toFinset, mem_allStrings] at hy1
          have hy_prog : (programLength y : ℕ∞) = (n : ℕ∞) := by exact_mod_cast hy1
          rw [hy_prog] at h2
          intro htop
          rw [htop] at h1
          have h_add : plainK U y + (c_cond : ℕ∞) ≤ (n : ℕ∞) + (c_plain : ℕ∞) + (c_cond : ℕ∞) := by
            rw [add_comm (plainK U y), add_comm ((n : ℕ∞) + (c_plain : ℕ∞))]
            exact add_le_add_right h2 (c_cond : ℕ∞)
          have h_le : ⊤ ≤ ((n + c_plain + c_cond : ℕ) : ℕ∞) := h1.trans h_add
          rw [top_le_iff] at h_le
          exact ENat.natCast_ne_top (n + c_plain + c_cond) h_le
        have h_coe : condCVal U y x ≤ m → condK U y x ≤ (m : ℕ∞) := by
          intro h
          have : condK U y x = ((condCVal U y x : ℕ) : ℕ∞) := (ENat.natCast_toNat h_top).symm
          rw [this]
          exact_mod_cast h
        exact h_coe h_cond_le
      have h_card := (Finset.card_le_card h_sub).trans_lt (card_compressibleWordsLt U x m)
      exact_mod_cast h_card.le
  have h_sum_inner := Finset.sum_le_sum h_inner
  refine h_sum_inner.trans ?_
  have h_part1 : ∑ k ∈ Finset.range c_plain,
        (if k < c_plain then (2 : ℝ) ^ n else (2 : ℝ) ^ (c_plain + n - k)) =
      c_plain * (2 : ℝ) ^ n := by
    have : ∀ k ∈ Finset.range c_plain,
        (if k < c_plain then (2 : ℝ) ^ n else (2 : ℝ) ^ (c_plain + n - k)) = (2 : ℝ) ^ n := by
      intro k hk
      rw [Finset.mem_range] at hk
      exact ite_eq_left hk
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h_part2 : ∑ k ∈ Finset.Ico c_plain (c_plain + n),
        (if k < c_plain then (2 : ℝ) ^ n else (2 : ℝ) ^ (c_plain + n - k)) ≤ 2 * (2 : ℝ) ^ n := by
    have h_ico_eq : ∑ k ∈ Finset.Ico c_plain (c_plain + n),
          (if k < c_plain then (2 : ℝ) ^ n else (2 : ℝ) ^ (c_plain + n - k)) =
        ∑ k ∈ Finset.Ico c_plain (c_plain + n), (2 : ℝ) ^ (c_plain + n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      have : ¬ (k < c_plain) := by omega
      exact ite_eq_right this
    rw [h_ico_eq]
    rw [sum_Ico_shift n c_plain]
    have h_rev := sum_pow_two_reverse n
    have h21 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
    linarith
  have h_split := (Finset.sum_range_add_sum_Ico
    (fun k => if k < c_plain then (2 : ℝ) ^ n else (2 : ℝ) ^ (c_plain + n - k))
    (Nat.le_add_right c_plain n)).symm
  rw [h_split, h_part1]
  linarith

/-- **Exercise 62.** Theorem 25 holds under the weaker hypotheses that `C(x | z)`
and `C(y | x, z)` are bounded by `n`. -/
theorem mutual_information_weaker_hypotheses (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n : ℕ) (x y z : BitString),
      condK U x z ≤ (n : ℕ∞) → condK U y (pairCode x z) ≤ (n : ℕ∞) →
      (cCondPair U x y z ≤ condK U x z + condK U y (pairCode x z) +
          ((logSlack c n : ℕ) : ℕ∞)) ∧
        (condK U x z + condK U y (pairCode x z) ≤
          cCondPair U x y z + ((logSlack c n : ℕ) : ℕ∞)) := by
  obtain ⟨U_pref, hU_pref⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cPair, hPair⟩ := condK_le_KP U U_pref hU hU_pref.isPrefixDecompressor
  obtain ⟨cChain, hChain⟩ := KPCondPair_chain_upper U_pref hU_pref
  obtain ⟨cCond, hCond⟩ := KP_le_condK_add_log_of_value U_pref U hU_pref hU
  obtain ⟨cDropPrefix, hDropPrefix⟩ := KP_cond_drop_right_le U_pref hU_pref
  obtain ⟨cReassoc, hReassoc⟩ :=
    KP_cond_map_le U_pref hU_pref condContextReassociate condContextReassociate_computable
  obtain ⟨cLower, hLower⟩ := condK_pairCode_chain_lower_values U hU
  let cFixed := cDropPrefix + cReassoc + cChain + cPair
  obtain ⟨C1, hC1⟩ := logSlack_linear_bound (2 * cCond) 1 1
  let Cup := C1 + cFixed
  obtain ⟨Cfold, hFold⟩ := logSlack_fold_level cLower Cup
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound Cfold 2 1
  let C := Cup + C2
  refine ⟨C, fun n x y z hxz hyxz => ?_⟩
  have hxz_fin : condK U x z ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hxz
  obtain ⟨kx, hkx⟩ := ENat.ne_top_iff_exists.mp hxz_fin
  have hkx_val : HasPlainConditionalComplexityValue U x z kx := hkx.symm
  have hkx_le : kx ≤ n := by rw [← hkx] at hxz; exact_mod_cast hxz
  have hyxz_fin : condK U y (pairCode x z) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hyxz
  obtain ⟨kyx, hkyx⟩ := ENat.ne_top_iff_exists.mp hyxz_fin
  have hkyx_val : HasPlainConditionalComplexityValue U y (pairCode x z) kyx := hkyx.symm
  have hkyx_le : kyx ≤ n := by rw [← hkyx] at hyxz; exact_mod_cast hyxz
  obtain ⟨kxy, hkxy⟩ := exists_plainConditionalComplexityValue U hU (pairCode x y) z
  have hkxy_val : HasPlainConditionalComplexityValue U (pairCode x y) z kxy := hkxy
  have hkpxFinite : KP U_pref x z ≠ ⊤ := by
    have h := hCond x z kx hkx_val
    refine ne_top_of_le_ne_top ?_ h
    exact ENat.natCast_ne_top _
  obtain ⟨kpx, hkpx⟩ := ENat.ne_top_iff_exists.mp hkpxFinite
  have hkpxValue : HasCondPrefixComplexityValue U_pref x z kpx := hkpx
  have hyPrefix :
      KP U_pref y (prefixCondComplexityContext z x kpx) ≤
        (kyx : ENat) + (logSlack cCond (kyx + 1) : ENat) +
          (cDropPrefix + cReassoc : Nat) := by
    calc
      KP U_pref y (prefixCondComplexityContext z x kpx)
          ≤ KP U_pref y (condContextReassociate
              (prefixCondComplexityContext z x kpx)) + (cReassoc : ENat) :=
        hReassoc y (prefixCondComplexityContext z x kpx)
      _ = KP U_pref y (pairCode (pairCode x z) (natCode kpx)) +
          (cReassoc : ENat) := by rw [condContextReassociate_prefixCondComplexityContext]
      _ ≤ (KP U_pref y (pairCode x z) + (cDropPrefix : ENat)) +
          (cReassoc : ENat) := by
        gcongr
        exact hDropPrefix y (pairCode x z) (natCode kpx)
      _ ≤ (((kyx : ENat) + (logSlack cCond (kyx + 1) : ENat)) +
          (cDropPrefix : ENat)) + (cReassoc : ENat) := by
        gcongr
        exact hCond y (pairCode x z) kyx hkyx_val
      _ = (kyx : ENat) + (logSlack cCond (kyx + 1) : ENat) +
          (cDropPrefix + cReassoc : Nat) := by push_cast; ring
  have hMainNat :
      kxy ≤ kx + kyx + logSlack cCond (kx + 1) + logSlack cCond (kyx + 1) + cFixed := by
    have h1 : (kxy : ENat) ≤ KP U_pref (pairCode x y) z + (cPair : ENat) := by
      rw [← hkxy_val]; exact hPair (pairCode x y) z
    have h2 : KPCondPair U_pref x y z ≤ KP U_pref x z +
        KP U_pref y (prefixCondComplexityContext z x kpx) + (cChain : ENat) :=
      hChain x y z kpx hkpxValue
    have h3 : KP U_pref x z ≤ (kx : ENat) + (logSlack cCond (kx + 1) : ENat) :=
      hCond x z kx hkx_val
    have h4 : KP U_pref y (prefixCondComplexityContext z x kpx) ≤
        (kyx : ENat) + (logSlack cCond (kyx + 1) : ENat) +
          ((cDropPrefix + cReassoc : ℕ) : ENat) := hyPrefix
    have hENat : (kxy : ENat) ≤
        ((kx + kyx + logSlack cCond (kx + 1) + logSlack cCond (kyx + 1) +
            cFixed : ℕ) : ENat) := by
      calc (kxy : ENat)
        _ ≤ KPCondPair U_pref x y z + (cPair : ENat) := h1
        _ ≤ (KP U_pref x z + KP U_pref y (prefixCondComplexityContext z x kpx) +
              (cChain : ENat)) + (cPair : ENat) := by gcongr
        _ ≤ (((kx : ENat) + (logSlack cCond (kx + 1) : ENat)) +
              ((kyx : ENat) + (logSlack cCond (kyx + 1) : ENat) +
                ((cDropPrefix + cReassoc : ℕ) : ENat)) + (cChain : ENat)) +
                  (cPair : ENat) := by gcongr
        _ = ((kx + kyx + logSlack cCond (kx + 1) + logSlack cCond (kyx + 1) +
              cFixed : ℕ) : ENat) := by
          dsimp [cFixed]
          push_cast
          generalize (logSlack cCond (kx + 1) : ENat) = S1
          generalize (logSlack cCond (kyx + 1) : ENat) = S2
          generalize (kx : ENat) = K1
          generalize (kyx : ENat) = K2
          generalize (cDropPrefix : ENat) = C1'
          generalize (cReassoc : ENat) = C2'
          generalize (cChain : ENat) = C3'
          generalize (cPair : ENat) = C4'
          ring
    exact_mod_cast hENat
  have hSlack2 : logSlack cCond (kx + 1) + logSlack cCond (kyx + 1) + cFixed ≤
      logSlack Cup n := by
    have hkx1 : kx + 1 ≤ n + 1 := by omega
    have hkyx1 : kyx + 1 ≤ n + 1 := by omega
    have h1 : logSlack cCond (kx + 1) ≤ logSlack cCond (n + 1) :=
      logSlack_mono_right cCond hkx1
    have h2 : logSlack cCond (kyx + 1) ≤ logSlack cCond (n + 1) :=
      logSlack_mono_right cCond hkyx1
    have h3 : logSlack cCond (kx + 1) + logSlack cCond (kyx + 1) ≤
        2 * logSlack cCond (n + 1) := by omega
    have h4 : 2 * logSlack cCond (n + 1) = logSlack (2 * cCond) (1 * n + 1) := by
      rw [logSlack_nsmul]; unfold logSlack; ring_nf
    have h5 : logSlack (2 * cCond) (1 * n + 1) ≤ logSlack C1 n := hC1 n
    have h6 : logSlack C1 n + cFixed ≤ logSlack Cup n := logSlack_add_nat_le C1 cFixed n
    omega
  have hkxy_upper : kxy ≤ kx + kyx + logSlack Cup n := by omega
  have hLowerBound : kx + kyx ≤ kxy + logSlack C n := by
    have hLowVal := hLower x y z kx kyx kxy hkx_val hkyx_val hkxy_val
    have hkxy_bound : kxy + 1 ≤ n + (n + 1) + logSlack Cup n := by omega
    have hFoldApplied : logSlack cLower (kxy + 1) ≤ logSlack Cfold (2 * n + 1) := by
      have h := hFold n 0 (n + 1) (kxy + 1) hkxy_bound
      have h_eq : n + 0 + (n + 1) = 2 * n + 1 := by omega
      rwa [h_eq] at h
    have hLin2 := hC2 n
    have hSlackLower : logSlack cLower (kxy + 1) ≤ logSlack C n := by
      calc logSlack cLower (kxy + 1)
          ≤ logSlack Cfold (2 * n + 1) := hFoldApplied
        _ ≤ logSlack C2 n := hLin2
        _ ≤ logSlack C n := logSlack_mono_left (Nat.le_add_left C2 Cup) n
    omega
  have hkxy_upper_C : kxy ≤ kx + kyx + logSlack C n := by
    exact hkxy_upper.trans
      (Nat.add_le_add_left (logSlack_mono_left (Nat.le_add_right Cup C2) n) (kx + kyx))
  constructor
  · calc
      cCondPair U x y z = (kxy : ℕ∞) := hkxy_val
      _ ≤ ((kx + kyx + logSlack C n : ℕ) : ℕ∞) := by exact_mod_cast hkxy_upper_C
      _ = condK U x z + condK U y (pairCode x z) + ((logSlack C n : ℕ) : ℕ∞) := by
        rw [hkx.symm, hkyx.symm]
        push_cast
        ring
  · calc
      condK U x z + condK U y (pairCode x z) = ((kx + kyx : ℕ) : ℕ∞) := by
        rw [hkx.symm, hkyx.symm]
        push_cast
        rfl
      _ ≤ ((kxy + logSlack C n : ℕ) : ℕ∞) := by exact_mod_cast hLowerBound
      _ = cCondPair U x y z + ((logSlack C n : ℕ) : ℕ∞) := by
        dsimp [cCondPair]
        rw [hkxy_val]
        push_cast
        rfl

/-- Swapping the two components of a paired *condition* costs only a constant:
`C(z | ⟨y, x⟩) ≤ C(z | ⟨x, y⟩) + O(1)` for an optimal conditional decompressor. -/
lemma condK_cond_swapPairCode_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ z x y : BitString,
      condK V z (pairCode y x) ≤ condK V z (pairCode x y) + (c : ℕ∞) := by
  set D : Map := fun pr => V (pr.1, swapPairCode pr.2) with hDdef
  have hDdec : isDecompressor D :=
    hV.1.comp (Computable.fst.pair (swapPairCode_computable.comp Computable.snd))
  obtain ⟨c, hc⟩ := hV.2 D hDdec
  refine ⟨c, fun z x y => ?_⟩
  have hset : candidateLengths D z (pairCode y x) = candidateLengths V z (pairCode x y) := by
    ext n
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, by simpa [hDdef, produces, swapPairCode_pairCode] using hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, by simpa [hDdef, produces, swapPairCode_pairCode] using hp, rfl⟩
  have hcond : condK D z (pairCode y x) = condK V z (pairCode x y) := by
    unfold condK
    rw [hset]
  calc
    condK V z (pairCode y x)
        ≤ condK D z (pairCode y x) + (c : ℕ∞) := hc z (pairCode y x)
    _ = condK V z (pairCode x y) + (c : ℕ∞) := by rw [hcond]

end Kolmogorov
