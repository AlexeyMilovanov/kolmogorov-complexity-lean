/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.ComputableMetric.Presentation

/-!
# Admissible base oracles and static point dimensions

For a fixed metric presentation `P` (a dense sequence of ideal points) this module proves
that the metric table, a continuous map `T` and finitely many continuous potentials are
simultaneously computable above one base oracle (`exists_admissible_base`, blueprint node
`metric:admissible`).  Every stronger oracle is then admissible for the same data.

It then defines the oracle-relative precision complexity
`precisionComplexity P A x δ = inf {K^A(i) | dist (ι i) x < δ}`, its normalization by the
number of bits `-log₂ δ` of the radius, and the static lower and upper point dimensions
`staticPointDimensions` as the `liminf` and `limsup` of this ratio along `δ ↓ 0`
(blueprint node `metric:static-dimension`).  The infimum is attained at positive radii and
is antitone in the radius.

Finally `presentation_change` shows that, above an oracle computing the mixed distances of
two presentations, the static lower dimension does not depend on the chosen dense
sequence (blueprint node `metric:change`).  The later modules on dimension along scales,
pressure and the Barreira–Schmeling dimension use these definitions and the admissible base
oracle.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-! ### An admissible base oracle -/

/-- The relation between pairs of basic balls asserting that both radii are positive and
`f` maps the first ball into the second. -/
private def IsSoundBallPair (P : Presentation X) (Q : Presentation Y) (f : X → Y)
    (bc : (ℕ × ℚ) × (ℕ × ℚ)) : Prop :=
  0 < bc.1.2 ∧ 0 < bc.2.2 ∧ f '' basicBall P bc.1 ⊆ basicBall Q bc.2

/-- For a continuous map `f`, every basic ball around `f x` contains the image of some basic
ball around `x`, and this pair of balls is sound. -/
private lemma exists_isSoundBallPair_of_continuous (P : Presentation X) (Q : Presentation Y)
    (f : X → Y) (hf : Continuous f) (x : X) (c : ℕ × ℚ) (hx : f x ∈ basicBall Q c) :
    ∃ b : ℕ × ℚ, IsSoundBallPair P Q f (b, c) ∧ x ∈ basicBall P b := by
  have hx' : dist (Q.ι c.1) (f x) < (c.2 : ℝ) := Metric.mem_ball'.mp hx
  have hc : (0 : ℚ) < c.2 := by exact_mod_cast dist_nonneg.trans_lt hx'
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.mp (hf.isOpen_preimage (basicBall Q c) Metric.isOpen_ball) x hx
  obtain ⟨b, hb⟩ := Metric.denseRange_iff.mp P.dense x (ε / 4) (by positivity)
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
  refine ⟨(b, q), ⟨?_, hc, ?_⟩, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < ε / 4 by positivity).trans hq₁
  · rintro _ ⟨z, hz, rfl⟩
    refine hεsub (Metric.mem_ball'.mpr ?_)
    have hz' : dist (P.ι b) z < q := Metric.mem_ball'.mp hz
    calc dist x z ≤ dist x (P.ι b) + dist (P.ι b) z := dist_triangle _ _ _
      _ < ε / 4 + ε / 2 := add_lt_add hb (hz'.trans hq₂)
      _ < ε := by linarith
  · exact Metric.mem_ball'.mpr (by rw [dist_comm]; exact hb.trans hq₁)

/-- Every metric presentation has rational approximations of all distances between ideal
points, with error `< 2⁻ᵖ` at precision `p`. -/
private lemma exists_rat_approx_dist (P : Presentation X) :
    ∃ q : (ℕ × ℕ) × ℕ → ℚ, ∀ ij p,
      |(q (ij, p) : ℝ) - dist (P.ι ij.1) (P.ι ij.2)| < (2 : ℝ)⁻¹ ^ p := by
  have h : ∀ t : (ℕ × ℕ) × ℕ, ∃ q : ℚ,
      |(q : ℝ) - dist (P.ι t.1.1) (P.ι t.1.2)| < (2 : ℝ)⁻¹ ^ t.2 := fun t ↦ by
    obtain ⟨q, hq⟩ := exists_rat_near (dist (P.ι t.1.1) (P.ι t.1.2))
      (show 0 < (2 : ℝ)⁻¹ ^ t.2 by positivity)
    exact ⟨q, by simpa only [abs_sub_comm] using hq⟩
  choose q hq using h
  exact ⟨q, fun ij p ↦ hq (ij, p)⟩

/-- Decoding a rational from an `A`-computable integer table indexed by pairs of indices is
`A`-computable. -/
private lemma computableIn_decode_pair_table (v : ℕ → ℕ → ℤ) (A : Set ℕ)
    (hv : ComputableIn {charOracle A} (fun p : ℕ × ℕ ↦ v p.1 p.2)) :
    ComputableIn {charOracle A}
      (fun p : (ℕ × ℕ) × ℕ ↦
        (Encodable.decode (α := ℚ) (v (Nat.pair p.1.1 p.1.2) p.2).toNat).getD 0) := by
  have hdecode (n : ℕ) : ratOfCode n = (Encodable.decode (α := ℚ) n).getD 0 := by
    by_cases h : IsRatCode n
    · have hn : @Encodable.encode ℚ Rat.instEncodable (ratOfCode n) = n :=
        ratCode_ratOfCode h
      conv_rhs => rw [← hn, Encodable.encodek, Option.getD_some]
    · have h' : ¬ (0 < n.unpair.2 ∧
          (Denumerable.ofNat ℤ n.unpair.1).natAbs.Coprime n.unpair.2) := by
        simpa only [IsRatCode, int_natAbs_ofNat] using h
      have hint (k : ℕ) : Equiv.intEquivNat.symm k = Denumerable.ofNat ℤ k := by
        apply Encodable.encode_injective
        change Equiv.intEquivNat (Equiv.intEquivNat.symm k) = _
        rw [Equiv.apply_symm_apply]
        exact (Denumerable.encode_ofNat k).symm
      have hnone : Encodable.decode (α := ℚ) n = none := by
        simp only [Encodable.decode, Encodable.decodeSigma, Encodable.decodeSubtype,
          Option.bind_some, Function.comp_apply]
        simp only [hint, dite_eq_right h', Option.map_none, Option.bind_none]
      simp [ratOfCode, h, hnone]
  have hd : Computable (fun n : ℕ ↦ (Encodable.decode (α := ℚ) n).getD 0) :=
    computable_ratOfCode.of_eq hdecode
  have hi : Computable (fun p : (ℕ × ℕ) × ℕ ↦ (Nat.pair p.1.1 p.1.2, p.2)) :=
    ((Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd).to_comp
  have hv' := ComputableIn.comp
    (f := fun p : ℕ × ℕ ↦ v p.1 p.2)
    (g := fun p : (ℕ × ℕ) × ℕ ↦ (Nat.pair p.1.1 p.1.2, p.2))
    hv (hi.computableIn (O := {charOracle A}))
  have hn : ComputableIn {charOracle A}
      (fun p : (ℕ × ℕ) × ℕ ↦ (v (Nat.pair p.1.1 p.1.2) p.2).toNat) :=
    ComputableIn.comp ComputableReals.primrec_intToNat.to_comp.computableIn hv'
  exact ComputableIn.comp hd.computableIn hn

/-- The metric table of a presentation is encoded by an integer table: every oracle
computing that table computes the metric table of the presentation. -/
private lemma exists_int_table_computablePresentationIn (P : Presentation X) :
    ∃ v : ℕ → ℕ → ℤ, ∀ A : Set ℕ,
      ComputableIn {charOracle A} (fun p : ℕ × ℕ ↦ v p.1 p.2) →
        ComputablePresentationIn P A := by
  classical
  obtain ⟨q, hq⟩ := exists_rat_approx_dist P
  refine ⟨fun n p ↦ (Encodable.encode (q (Nat.unpair n, p)) : ℤ), fun A hv ↦ ?_⟩
  have hr := computableIn_decode_pair_table
    (fun n p ↦ (Encodable.encode (q (Nat.unpair n, p)) : ℤ)) A hv
  exact ⟨_, hr, fun ij p ↦ by simpa [Nat.unpair_pair] using hq ij p⟩

/-- A single oracle `C` such that every oracle computing `C` computes the metric table of `P`
and enumerates the sound ball relations of `T` and of each potential `v j`. -/
private lemma exists_oracle_computable_and_isREIn {k : ℕ} (P : Presentation X) (T : X → X)
    (v : Fin k → X → ℝ) :
    ∃ C : Set ℕ, ∀ A : Set ℕ, charOracle C ≤ᵀ charOracle A →
      ComputablePresentationIn P A ∧ IsREIn A (IsSoundBallPair P P T) ∧
      ∀ j : Fin k, IsREIn A (IsSoundBallPair P realPresentation (v j)) := by
  obtain ⟨vInt, hvInt⟩ := exists_int_table_computablePresentationIn P
  obtain ⟨CT, hCT⟩ := exists_oracle_isREIn (IsSoundBallPair P P T)
  have hCv : ∀ j : Fin k, ∃ Cj : Set ℕ, ∀ A : Set ℕ, charOracle Cj ≤ᵀ charOracle A →
      IsREIn A (IsSoundBallPair P realPresentation (v j)) :=
    fun j ↦ exists_oracle_isREIn _
  choose Cv hCv using hCv
  let S : ℕ → Set ℕ := fun n ↦ if n = 0 then CT else if h : n - 1 < k then Cv ⟨n - 1, h⟩ else ∅
  obtain ⟨B, -, hSB, hvB⟩ := oracle_joins_tables ∅ S vInt
  refine ⟨B, fun A hBA ↦ ⟨hvInt A (RecursiveIn.subst hvB (by simpa using hBA)), ?_, fun j ↦ ?_⟩⟩
  · refine hCT A ?_
    simpa [S] using (hSB 0).trans hBA
  · refine hCv j A ?_
    have hSj : S (j.val + 1) = Cv j := by simp [S, j.isLt]
    simpa [hSj] using (hSB (j.val + 1)).trans hBA

/-- For the same fixed ideal sequence, continuous dynamical data are represented above
some base oracle. No effective uniform-continuity modulus is required.
Blueprint node `metric:admissible`. -/
theorem exists_admissible_base {k : ℕ} (P : Presentation X) (T : X → X)
    (hT : Continuous T) (v : Fin k → X → ℝ) (hv : ∀ j, Continuous (v j)) :
    ∃ C : Set ℕ, ∀ A : Set ℕ, charOracle C ≤ᵀ charOracle A → IsAdmissible P T v A := by
  obtain ⟨C, hC⟩ := exists_oracle_computable_and_isREIn P T v
  refine ⟨C, fun A hA ↦ ?_⟩
  obtain ⟨hP, hTRE, hvRE⟩ := hC A hA
  exact ⟨hP, ⟨_, hTRE, fun _ _ h ↦ h,
      fun x c hx ↦ exists_isSoundBallPair_of_continuous P P T hT x c hx⟩,
    fun j ↦ ⟨_, hvRE j, fun _ _ h ↦ h,
      fun x c hx ↦ exists_isSoundBallPair_of_continuous P realPresentation (v j) (hv j) x c hx⟩⟩

/-! ### Precision complexity and static point dimensions -/

/-- Precision complexity is an infimum of extended natural costs, so an empty candidate
set has value infinity. Blueprint node `metric:static-dimension`. -/
noncomputable def precisionComplexity (P : Presentation X) (A : Set ℕ) (x : X)
    (δ : ℝ) : ENat :=
  ⨅ i : ℕ, ⨅ (_ : dist (P.ι i) x < δ), (oracleNatComplexity A i : ENat)

/-- At positive radii the precision infimum is finite and attained by an ideal index.
Blueprint node `metric:static-dimension`. -/
theorem staticPointDimensions_attained (P : Presentation X) (A : Set ℕ) (x : X)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ i, dist (P.ι i) x < δ ∧
      precisionComplexity P A x δ = (oracleNatComplexity A i : ENat) := by
  obtain ⟨i₀, hi₀⟩ := Metric.denseRange_iff.mp P.dense x δ hδ
  let S : Set ℕ := {m | ∃ i, dist (P.ι i) x < δ ∧ oracleNatComplexity A i = m}
  obtain ⟨i, hi, hmin⟩ := Nat.sInf_mem (s := S) ⟨_, i₀, by rwa [dist_comm], rfl⟩
  refine ⟨i, hi, le_antisymm (iInf₂_le_of_le i hi le_rfl) (le_iInf₂ fun j hj ↦ ?_)⟩
  rw [hmin]
  exact_mod_cast Nat.sInf_le (s := S) ⟨j, hj, rfl⟩

/-- The finite natural shadow of precision complexity is used only at positive radii.
Blueprint node `metric:static-dimension`. -/
noncomputable def precisionComplexityNat (P : Presentation X) (A : Set ℕ) (x : X)
    (δ : ℝ) : ℕ := (precisionComplexity P A x δ).toNat

/-- Normalized precision complexity takes nonnegative extended real values; dimensions
only inspect its positive-radius tail below one. Blueprint node `metric:static-dimension`. -/
noncomputable def normalizedPrecisionComplexity (P : Presentation X) (A : Set ℕ)
    (x : X) (δ : ℝ) : ℝ≥0∞ :=
  (precisionComplexityNat P A x δ : ℝ≥0∞) / ENNReal.ofReal (-Real.logb 2 δ)

/-- Lower and upper static point dimensions are respectively the lower and upper limits
along all positive radii tending to zero, for every oracle.
Blueprint node `metric:static-dimension`. -/
noncomputable def staticPointDimensions (P : Presentation X) (A : Set ℕ) (x : X) :
    ℝ≥0∞ × ℝ≥0∞ :=
  (liminf (normalizedPrecisionComplexity P A x) (𝓝[>] (0 : ℝ)),
    limsup (normalizedPrecisionComplexity P A x) (𝓝[>] (0 : ℝ)))

/-- Decreasing a radius can only increase its precision complexity.
Blueprint node `metric:static-dimension`. -/
theorem staticPointDimensions_antitone (P : Presentation X) (A : Set ℕ) (x : X) :
    Antitone (precisionComplexity P A x) := fun _ _ h ↦
  iInf_mono fun _ ↦ iInf_mono' fun h₁ ↦ ⟨h₁.trans_le h, le_rfl⟩

/-! ### Changing the presentation -/

/-- Given a mixed distance table `dist (P.ι i) (Q.ι j)` and a computable metric table of `Q`,
some partial recursive function finds, from an index `i` and a precision `p`, an ideal point
of `Q` within `2⁻ᵖ` of `P.ι i`. -/
private lemma exists_search_close_ideal_point (P Q : Presentation X) (A : Set ℕ)
    (hmixed : IsComputableRealFamilyIn A (fun ij : ℕ × ℕ ↦ dist (P.ι ij.1) (Q.ι ij.2))) :
    ∃ E : ℕ × ℕ →. ℕ, PartrecIn {charOracle A} E ∧
      ∀ i p, ∃ j, j ∈ E (i, p) ∧ dist (P.ι i) (Q.ι j) < (2 : ℝ)⁻¹ ^ p := by
  obtain ⟨q, hq, hqerr⟩ := hmixed
  have hr : Computable (fun p : ℕ ↦ (2 : ℚ)⁻¹ ^ (p + 1)) := by
    have hc := ComputableReals.computable_invSucc.comp
      ((Primrec.nat_sub.comp
        (primrec_two_pow_aux.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))
        (Primrec.const 1)).to_comp)
    refine hc.of_eq fun p ↦ ?_
    have heq : ((2 ^ (p + 1) - 1 : ℕ) : ℚ) + 1 = (2 : ℚ) ^ (p + 1) := by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]
      push_cast
      ring
    change 1 / (((2 ^ (p + 1) - 1 : ℕ) : ℚ) + 1) = _
    rw [heq, one_div, inv_pow]
  let test (ip : ℕ × ℕ) (j : ℕ) : Bool :=
    decide (q ((ip.1, j), ip.2 + 2) < (2 : ℚ)⁻¹ ^ (ip.2 + 1))
  have ht : ComputableIn₂ {charOracle A} test := by
    have hi : Computable (fun z : (ℕ × ℕ) × ℕ ↦ ((z.1.1, z.2), z.1.2 + 2)) :=
      ((Computable.fst.comp Computable.fst).pair Computable.snd).pair
        ((Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 2)).to_comp)
    have hright : ComputableIn {charOracle A}
        (fun z : (ℕ × ℕ) × ℕ ↦ (2 : ℚ)⁻¹ ^ (z.1.2 + 1)) :=
      hr.computableIn.comp (Computable.snd.comp Computable.fst).computableIn
    exact (ComputableReals.primrec_ratLt.decide.to_comp.computableIn.comp
      ((hq.comp hi.computableIn).pair hright)).to₂
  refine ⟨fun ip ↦ Nat.rfind fun j ↦ Part.some (test ip j), PartrecIn.rfind ht.partrecIn₂,
    fun i p ↦ ?_⟩
  have hpos : 0 < dyadicRadius (p + 2) := by
    unfold dyadicRadius
    positivity
  obtain ⟨j₀, hj₀⟩ := Metric.denseRange_iff.mp Q.dense (P.ι i) _ hpos
  have htest : test (i, p) j₀ = true := by
    have herr := (abs_lt.mp (hqerr (i, j₀) (p + 2))).2
    have hlt : (q ((i, j₀), p + 2) : ℝ) < (2 : ℝ)⁻¹ ^ (p + 1) := by
      dsimp [dyadicRadius] at hj₀
      simp only [pow_succ] at hj₀ herr ⊢
      norm_num at hj₀ herr ⊢
      linarith
    simp only [test, decide_eq_true_eq]
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat] using hlt
  have hdom : (Nat.rfind fun j ↦ Part.some (test (i, p) j)).Dom :=
    Nat.rfind_dom.mpr ⟨j₀, by simp [htest], fun _ ↦ trivial⟩
  obtain ⟨j, hjmem⟩ := Part.dom_iff_mem.mp hdom
  refine ⟨j, hjmem, ?_⟩
  have hlt : (q ((i, j), p + 2) : ℝ) < (2 : ℝ)⁻¹ ^ (p + 1) := by
    have h : q ((i, j), p + 2) < (2 : ℚ)⁻¹ ^ (p + 1) := by
      simpa [test] using Nat.rfind_spec hjmem
    simpa only [Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr h
  have herr := (abs_lt.mp (hqerr (i, j) (p + 2))).1
  simp only [pow_succ] at hlt herr
  norm_num at hlt herr
  linarith [pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) p]

/-- An `A`-partial recursive function on pairs of naturals lifts to an `A`-partial recursive
function on lists of bit strings, acting on the singleton list containing the pair code. -/
private lemma exists_operation_on_strings (A : Set ℕ) (E : ℕ × ℕ →. ℕ)
    (hE : PartrecIn {charOracle A} E) :
    ∃ F : List BitString →. BitString, PartrecIn {charOracle A} F ∧
      ∀ i p j, j ∈ E (i, p) → natBits j ∈ F [pairCode (natBits i) (natBits p)] := by
  let d : List BitString → ℕ × ℕ := fun ws ↦
    (decodeBits (decodeFirst (ws.getD 0 [])), decodeBits (decodeSecond (ws.getD 0 [])))
  refine ⟨fun ws ↦ (E (d ws)).map natBits, ?_, fun i p j hj ↦ ?_⟩
  · have hhead : Computable fun ws : List BitString ↦ ws.getD 0 [] :=
      ((Primrec.list_getD ([] : BitString)).to_comp : Computable₂ _).comp
        Computable.id (Computable.const 0)
    have hd : Computable d :=
      (decodeBits_computable.comp (decodeFirst_computable.comp hhead)).pair
        (decodeBits_computable.comp (decodeSecond_computable.comp hhead))
    exact (hE.comp hd.computableIn).map
      (natBits_computable.comp Computable.snd).computableIn.to₂
  · dsimp only [d]
    have hi : decodeBits (natBits i) = i := decodeBits_natBits i
    have hp : decodeBits (natBits p) = p := decodeBits_natBits p
    rw [List.getD_cons_zero, decodeFirst_pairCode, decodeSecond_pairCode, hi, hp]
    exact Part.mem_map _ hj

/-- A search procedure for `Q`-ideal points near `P`-ideal points costs, for the found index
`j`, at most `K(i) + 2 log₂ (p + 1) + c` bits of oracle complexity, for some constant `c`. -/
private lemma exists_complexity_bound_of_search (A : Set ℕ) (E : ℕ × ℕ →. ℕ)
    (hE : PartrecIn {charOracle A} E) :
    ∃ c : ℝ, ∀ i p j, j ∈ E (i, p) →
      (oracleNatComplexity A j : ℝ) ≤
        oracleNatComplexity A i + 2 * Real.logb 2 (p + 1) + c := by
  obtain ⟨F, hF, hFspec⟩ := exists_operation_on_strings A E hE
  obtain ⟨c, hc⟩ := oracle_tuple_bounds_composition A 1 F hF
  obtain ⟨d, hd⟩ := oracle_tuple_bounds_overhead A
  refine ⟨(d : ℝ) + c, fun i p j hj ↦ ?_⟩
  have h₁ := hc [pairCode (natBits i) (natBits p)] (natBits j) rfl (hFspec i p j hj)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h₁
  have h₂ : oracleNatComplexity A j ≤ oraclePairComplexity A i p + c := h₁
  have h₃ : (oracleNatComplexity A j : ℝ) ≤ oraclePairComplexity A i p + c := by
    exact_mod_cast h₂
  linarith [hd i p]

/-- The `2⁻ᵖ` bound at the smallest precision `p = ⌈-log₂ δ⌉` is at most `δ`. -/
private lemma inv_two_pow_ceil_neg_logb_le {δ : ℝ} (hδ : 0 < δ) :
    (2 : ℝ)⁻¹ ^ ⌈-Real.logb 2 δ⌉₊ ≤ δ := by
  have h : (2 : ℝ)⁻¹ ^ (-Real.logb 2 δ) = δ := by
    rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv,
      Real.rpow_logb (by norm_num) (by norm_num) hδ]
  calc (2 : ℝ)⁻¹ ^ ⌈-Real.logb 2 δ⌉₊
      = (2 : ℝ)⁻¹ ^ ((⌈-Real.logb 2 δ⌉₊ : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ)⁻¹ ^ (-Real.logb 2 δ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (Nat.le_ceil _)
    _ = δ := h

/-- Passing from `t` to `⌈t⌉₊` costs at most one extra bit inside `2 log₂ (· + 1)`. -/
private lemma two_mul_logb_ceil_add_one_le {t : ℝ} (ht : 0 ≤ t) :
    2 * Real.logb 2 (⌈t⌉₊ + 1) ≤ 2 * Real.logb 2 (t + 1) + 2 := by
  have hlt : (⌈t⌉₊ : ℝ) + 1 ≤ 2 * (t + 1) := by linarith [Nat.ceil_lt_add_one ht]
  have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hlt
  rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at hmono
  linarith

/-- The `log`-overhead term `2 log₂ (-log₂ (δ / 4) + 1) + C` in the comparison of the
precision complexities at radii `δ` and `δ / 4`. -/
private noncomputable def precisionOverhead (C δ : ℝ) : ℝ :=
  2 * Real.logb 2 (-Real.logb 2 (δ / 4) + 1) + C

/-- If a partial recursive search finds `Q`-ideal points near every `P`-ideal point at a
logarithmic cost, then for small radii `δ` the precision complexity of `Q` at `δ` is at most
that of `P` at `δ / 4` plus a logarithmic overhead. -/
private lemma precisionComplexityNat_le_of_search (P Q : Presentation X) (A : Set ℕ) (x : X)
    (E : ℕ × ℕ →. ℕ)
    (hsearch : ∀ i p, ∃ j, j ∈ E (i, p) ∧ dist (P.ι i) (Q.ι j) < (2 : ℝ)⁻¹ ^ p)
    (c : ℝ) (hcost : ∀ i p j, j ∈ E (i, p) →
      (oracleNatComplexity A j : ℝ) ≤ oracleNatComplexity A i + 2 * Real.logb 2 (p + 1) + c) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (precisionComplexityNat Q A x δ : ℝ) ≤
      precisionComplexityNat P A x (δ / 4) + precisionOverhead (c + 2) δ := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 4 by norm_num)] with δ hδ
  have hd : 0 < δ / 4 := by linarith [hδ.1]
  have ht : 0 ≤ -Real.logb 2 (δ / 4) :=
    neg_nonneg.2 (Real.logb_nonpos (by norm_num) hd.le (by linarith [hδ.2]))
  obtain ⟨i, hiP, hiK⟩ := staticPointDimensions_attained P A x (δ / 4) hd
  obtain ⟨j, hjmem, hdist⟩ := hsearch i ⌈-Real.logb 2 (δ / 4)⌉₊
  have hQ : dist (Q.ι j) x < δ :=
    calc dist (Q.ι j) x ≤ dist (Q.ι j) (P.ι i) + dist (P.ι i) x := dist_triangle _ _ _
      _ < δ / 4 + δ / 4 :=
        add_lt_add ((dist_comm _ _).trans_lt
          (hdist.trans_le (inv_two_pow_ceil_neg_logb_le hd))) hiP
      _ < δ := by linarith [hδ.1]
  have hle : precisionComplexityNat Q A x δ ≤ oracleNatComplexity A j :=
    (ENat.toNat_le_toNat (iInf₂_le_of_le j hQ le_rfl) (ENat.natCast_ne_top _)).trans_eq
      (ENat.toNat_natCast _)
  have hPK : precisionComplexityNat P A x (δ / 4) = oracleNatComplexity A i := by
    simp [precisionComplexityNat, hiK]
  have hlog := two_mul_logb_ceil_add_one_le ht
  have hcast : (precisionComplexityNat Q A x δ : ℝ) ≤ oracleNatComplexity A j := by
    exact_mod_cast hle
  have hjcost := hcost i ⌈-Real.logb 2 (δ / 4)⌉₊ j hjmem
  rw [hPK, precisionOverhead]
  linarith

/-- The number of bits `-log₂ δ` of a radius, as an extended nonnegative real. -/
private noncomputable abbrev bitScale (δ : ℝ) : ℝ≥0∞ := ENNReal.ofReal (-Real.logb 2 δ)

/-- The ratio of the bit scales at the radii `δ / 4` and `δ`. -/
private noncomputable abbrev scaleRatio (δ : ℝ) : ℝ≥0∞ := bitScale (δ / 4) / bitScale δ

/-- Dividing a radius by four adds two bits. -/
private lemma neg_logb_div_four {δ : ℝ} (hδ : 0 < δ) :
    -Real.logb 2 (δ / 4) = -Real.logb 2 δ + 2 := by
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [Real.logb_div hδ.ne' (by norm_num), h4]
  ring

/-- The number of bits `-log₂ δ` tends to infinity as `δ ↓ 0`. -/
private lemma tendsto_neg_logb_nhdsGT_zero :
    Tendsto (fun δ : ℝ ↦ -Real.logb 2 δ) (𝓝[>] (0 : ℝ)) atTop :=
  tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num))

/-- Eventually (as `δ ↓ 0`) the number of bits `-log₂ δ` of the radius is positive. -/
private lemma eventually_bitScale_pos :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < -Real.logb 2 δ :=
  tendsto_neg_logb_nhdsGT_zero.eventually_gt_atTop 0

/-- The ratio of the bit scales at `δ / 4` and `δ` tends to one as `δ ↓ 0`. -/
private lemma tendsto_scaleRatio : Tendsto scaleRatio (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hlim : Tendsto (fun L : ℝ ↦ 1 + 2 / L) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (tendsto_id (α := ℝ)))
  have h := ENNReal.tendsto_ofReal (hlim.comp tendsto_neg_logb_nhdsGT_zero)
  rw [ENNReal.ofReal_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_bitScale_pos, self_mem_nhdsWithin] with δ hL hδ
  simp only [Function.comp_apply, scaleRatio, bitScale]
  rw [← ENNReal.ofReal_div_of_pos hL, neg_logb_div_four hδ, add_div, div_self hL.ne']

/-- A logarithmic overhead divided by the number of bits tends to zero. -/
private lemma tendsto_log_overhead_div (C : ℝ) :
    Tendsto (fun L : ℝ ↦ (2 * Real.logb 2 (L + 3) + C) / L) atTop (𝓝 0) := by
  have hbase : Tendsto (fun u : ℝ ↦ Real.logb 2 u / u) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero
  have hshift : Tendsto (fun L : ℝ ↦ Real.logb 2 (L + 3) / (L + 3)) atTop (𝓝 0) :=
    hbase.comp (tendsto_atTop_add_const_right atTop 3 tendsto_id)
  have hratio : Tendsto (fun L : ℝ ↦ (L + 3) / L) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun L : ℝ ↦ 1 + 3 / L) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (tendsto_id (α := ℝ)))
    refine hdiv.congr' (eventually_atTop.mpr ⟨1, fun x hx ↦ ?_⟩)
    dsimp only
    rw [add_div, div_self (by linarith)]
  have hlog : Tendsto (fun L : ℝ ↦ Real.logb 2 (L + 3) / L) atTop (𝓝 0) := by
    have hprod := hshift.mul hratio
    rw [zero_mul] at hprod
    refine hprod.congr' (eventually_atTop.mpr ⟨0, fun x hx ↦ ?_⟩)
    rw [mul_div_assoc', div_mul_cancel₀ _ (by linarith : x + 3 ≠ 0)]
  have hconst : Tendsto (fun L : ℝ ↦ C / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum := (hlog.const_mul 2).add hconst
  rw [mul_zero, add_zero] at hsum
  refine hsum.congr' (eventually_atTop.mpr ⟨1, fun x hx ↦ ?_⟩)
  dsimp only
  rw [add_div, mul_div_assoc']

/-- The overhead term divided by the number of bits tends to zero as `δ ↓ 0`. -/
private lemma tendsto_precisionOverhead_div (C : ℝ) :
    Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (precisionOverhead C δ) / bitScale δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hreal : Tendsto (fun δ : ℝ ↦ precisionOverhead C δ / -Real.logb 2 δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine ((tendsto_log_overhead_div C).comp tendsto_neg_logb_nhdsGT_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [Function.comp_apply, precisionOverhead]
    rw [neg_logb_div_four hδ]
    ring_nf
  have h := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_bitScale_pos] with δ hδ
  exact ENNReal.ofReal_div_of_pos hδ

/-- A comparison of precision complexities at radii `δ` and `δ / 4` with additive overhead
gives a comparison of the normalized complexities with a multiplicative scale ratio and an
overhead divided by the number of bits. -/
private lemma normalizedPrecisionComplexity_le_of_le (P Q : Presentation X) (A : Set ℕ)
    (x : X) (C : ℝ)
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (precisionComplexityNat Q A x δ : ℝ) ≤
      precisionComplexityNat P A x (δ / 4) + precisionOverhead C δ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), normalizedPrecisionComplexity Q A x δ ≤
      normalizedPrecisionComplexity P A x (δ / 4) * scaleRatio δ +
        ENNReal.ofReal (precisionOverhead C δ) / bitScale δ := by
  filter_upwards [h, eventually_bitScale_pos, self_mem_nhdsWithin] with δ hδ hL hδ0
  have hL' : 0 < -Real.logb 2 (δ / 4) := by rw [neg_logb_div_four hδ0]; linarith
  have hne : bitScale (δ / 4) ≠ 0 := (ENNReal.ofReal_pos.mpr hL').ne'
  have hQ : ENNReal.ofReal (precisionComplexityNat Q A x δ) ≤
      ENNReal.ofReal (precisionComplexityNat P A x (δ / 4)) +
        ENNReal.ofReal (precisionOverhead C δ) :=
    (ENNReal.ofReal_le_ofReal hδ).trans ENNReal.ofReal_add_le
  calc normalizedPrecisionComplexity Q A x δ
      = ENNReal.ofReal (precisionComplexityNat Q A x δ) / bitScale δ := by
        rw [normalizedPrecisionComplexity, ENNReal.ofReal_natCast]
    _ ≤ (ENNReal.ofReal (precisionComplexityNat P A x (δ / 4)) +
          ENNReal.ofReal (precisionOverhead C δ)) / bitScale δ := by gcongr
    _ = normalizedPrecisionComplexity P A x (δ / 4) * scaleRatio δ +
          ENNReal.ofReal (precisionOverhead C δ) / bitScale δ := by
        rw [ENNReal.add_div, normalizedPrecisionComplexity, ← ENNReal.ofReal_natCast,
          scaleRatio, ENNReal.div_mul_div_cancel hne ENNReal.ofReal_ne_top]

/-- Dividing the radius by four does not change the filter of small positive radii. -/
private lemma map_div_four_nhdsGT_zero : map (· / 4) (𝓝[>] (0 : ℝ)) = 𝓝[>] 0 := by
  have hmul : ∀ {c : ℝ}, 0 < c → Tendsto (c * ·) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := fun hc ↦
    tendsto_iff_comap.mpr (comap_mulLeft_nhdsGT_zero hc).ge
  have hdiv : Tendsto (· / 4) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    simpa only [div_eq_inv_mul] using hmul (inv_pos.mpr (by norm_num : (0 : ℝ) < 4))
  refine le_antisymm hdiv ?_
  calc 𝓝[>] (0 : ℝ) = map (· / 4) (map (4 * ·) (𝓝[>] 0)) := by
        rw [map_map]
        simp only [Function.comp_def, mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0), map_id']
    _ ≤ map (· / 4) (𝓝[>] 0) := map_mono (hmul (by norm_num))

/-- If the precision complexities of `Q` are eventually bounded by those of `P` at a quarter of
the radius plus a logarithmic overhead, the lower static dimension of `Q` is at most that of
`P`. -/
private lemma liminf_normalizedPrecisionComplexity_le (P Q : Presentation X) (A : Set ℕ)
    (x : X) (C : ℝ)
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (precisionComplexityNat Q A x δ : ℝ) ≤
      precisionComplexityNat P A x (δ / 4) + precisionOverhead C δ) :
    liminf (normalizedPrecisionComplexity Q A x) (𝓝[>] 0) ≤
      liminf (normalizedPrecisionComplexity P A x) (𝓝[>] 0) := by
  have hmul : liminf (fun δ ↦ normalizedPrecisionComplexity P A x (δ / 4) * scaleRatio δ)
      (𝓝[>] 0) ≤ liminf (fun δ ↦ normalizedPrecisionComplexity P A x (δ / 4)) (𝓝[>] 0) := by
    simp only [mul_comm (normalizedPrecisionComplexity P A x _)]
    have hlim : limsup scaleRatio (𝓝[>] (0 : ℝ)) = 1 := tendsto_scaleRatio.limsup_eq
    have := ENNReal.liminf_mul_le (u := scaleRatio)
      (v := fun δ ↦ normalizedPrecisionComplexity P A x (δ / 4)) (f := 𝓝[>] (0 : ℝ))
      (Or.inl (by rw [hlim]; exact one_ne_zero)) (Or.inl (by rw [hlim]; exact ENNReal.one_ne_top))
    rwa [hlim, one_mul] at this
  have hcomp : liminf (fun δ ↦ normalizedPrecisionComplexity P A x (δ / 4)) (𝓝[>] 0) =
      liminf (normalizedPrecisionComplexity P A x) (𝓝[>] 0) := by
    change liminf (normalizedPrecisionComplexity P A x ∘ (· / 4)) _ = _
    rw [liminf_comp, map_div_four_nhdsGT_zero]
  calc liminf (normalizedPrecisionComplexity Q A x) (𝓝[>] 0)
      ≤ liminf (fun δ ↦ normalizedPrecisionComplexity P A x (δ / 4) * scaleRatio δ +
          ENNReal.ofReal (precisionOverhead C δ) / bitScale δ) (𝓝[>] 0) :=
        liminf_le_liminf (normalizedPrecisionComplexity_le_of_le P Q A x C h)
    _ = liminf (fun δ ↦ normalizedPrecisionComplexity P A x (δ / 4) * scaleRatio δ)
          (𝓝[>] 0) :=
        ENNReal.liminf_add_of_right_tendsto_zero (tendsto_precisionOverhead_div C) _
    _ ≤ _ := hmul.trans_eq hcomp

/-- Mixed distances between `P` and `Q` and between `Q` and `P` are interchangeable. -/
theorem isComputableRealFamilyIn_dist_swap (P Q : Presentation X) (A : Set ℕ)
    (hmixed : IsComputableRealFamilyIn A (fun ij : ℕ × ℕ ↦ dist (P.ι ij.1) (Q.ι ij.2))) :
    IsComputableRealFamilyIn A (fun ij : ℕ × ℕ ↦ dist (Q.ι ij.1) (P.ι ij.2)) := by
  obtain ⟨q, hq, hqerr⟩ := hmixed
  refine ⟨fun ip ↦ q ((ip.1.2, ip.1.1), ip.2), hq.comp (Computable.computableIn
    (((Computable.snd.comp Computable.fst).pair (Computable.fst.comp Computable.fst)).pair
      Computable.snd)), fun ij p ↦ ?_⟩
  simpa only [dist_comm (P.ι ij.2)] using hqerr (ij.2, ij.1) p

/-- The static lower dimension for `Q` is at most that for `P`, once `Q` has a computable
metric table and the mixed distances are computable. -/
private lemma staticPointDimensions_fst_le (P Q : Presentation X) (A : Set ℕ)
    (hmixed : IsComputableRealFamilyIn A (fun ij : ℕ × ℕ ↦ dist (P.ι ij.1) (Q.ι ij.2)))
    (x : X) : (staticPointDimensions Q A x).1 ≤ (staticPointDimensions P A x).1 := by
  obtain ⟨E, hE, hsearch⟩ := exists_search_close_ideal_point P Q A hmixed
  obtain ⟨c, hcost⟩ := exists_complexity_bound_of_search A E hE
  exact liminf_normalizedPrecisionComplexity_le P Q A x (c + 2)
    (precisionComplexityNat_le_of_search P Q A x E hsearch c hcost)

/-- Static lower point dimension is independent of the fixed presentation above an oracle
computing the mixed distances between the two ideal sequences. Blueprint node
`metric:change`. -/
theorem presentation_change (P Q : Presentation X) (A : Set ℕ)
    (hmixed : IsComputableRealFamilyIn A
      (fun ij : ℕ × ℕ => dist (P.ι ij.1) (Q.ι ij.2))) (x : X) :
    (staticPointDimensions P A x).1 = (staticPointDimensions Q A x).1 := by
  exact le_antisymm
    (staticPointDimensions_fst_le Q P A (isComputableRealFamilyIn_dist_swap P Q A hmixed) x)
    (staticPointDimensions_fst_le P Q A hmixed x)

end Kolmogorov.PointToSet
