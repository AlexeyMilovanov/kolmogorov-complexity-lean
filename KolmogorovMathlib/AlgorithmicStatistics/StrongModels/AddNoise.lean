import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UniformNoiseExtension
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.DistributionProjection

/-!
# Add-noise deficiency bookkeeping

This file starts the proof infrastructure for VS40 `prop:add-noise`.  It keeps
the hard information-theoretic step explicit: the theorem below assumes the
conditional pair-complexity lower bound and discharges only the exact product
mass and multiplicative-deficiency calculation.
-/

namespace Kolmogorov
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- Algebraic extension half of add-noise.  If the conditional complexity of
`(a,u)` under the canonical product model contains the complexity of `a` plus
all `m` noise bits, up to `delta`, then uniformly extending a deficiency-`beta`
model for `a` gives deficiency at most `beta + delta` for `(a,u)`. -/
theorem deficiency_pairUniformExtension_of_complexity
    (U : Map) (P : CodedFiniteDistribution)
    (a u : BitString) (m beta delta : Nat)
    (hu : u.length = m)
    (hcomplexity :
      KP U a P.code + (m : ENat) ≤
        KP U (pairCode a u) (codedPairUniformExtension P m).code +
          (delta : ENat))
    (hdef : DeficiencyLe U P a beta) :
    DeficiencyLe U (codedPairUniformExtension P m)
      (pairCode a u) (beta + delta) := by
  have hweight :
      complexityWeight
          (KP U (pairCode a u) (codedPairUniformExtension P m).code) *
          (2 : ENNReal)⁻¹ ^ delta ≤
        complexityWeight (KP U a P.code) * (2 : ENNReal)⁻¹ ^ m := by
    simpa only [complexityWeight_add_nat] using
      (complexityWeight_le_of_le hcomplexity)
  have hcancel :
      (2 : ENNReal)⁻¹ ^ delta * (2 : ENNReal) ^ delta = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  unfold DeficiencyLe CodedFiniteDistribution.DeficiencyLe at *
  rw [codedPairUniformExtension_mass_pairCode P m a u hu]
  calc
    complexityWeight
        (KP U (pairCode a u) (codedPairUniformExtension P m).code)
        = (complexityWeight
            (KP U (pairCode a u) (codedPairUniformExtension P m).code) *
              (2 : ENNReal)⁻¹ ^ delta) * (2 : ENNReal) ^ delta := by
            rw [mul_assoc, hcancel, mul_one]
    _ ≤ (complexityWeight (KP U a P.code) * (2 : ENNReal)⁻¹ ^ m) *
          (2 : ENNReal) ^ delta := by
            gcongr
    _ ≤ (((2 : ENNReal) ^ beta * P.mass a) *
          (2 : ENNReal)⁻¹ ^ m) * (2 : ENNReal) ^ delta := by
            gcongr
    _ = (2 : ENNReal) ^ (beta + delta) *
          (P.mass a * (2 : ENNReal)⁻¹ ^ m) := by
            rw [pow_add]
            ring

/-- Run the ordinary conditional decompressor `V`, but accept only programs
whose length is encoded in the second component of the context.  For every
fixed context all halting programs therefore have the same length. -/
def conditionalPlainLengthDecompressor (V : Map) : Map := fun pr =>
  bif (pr.1.length == decodeBits (decodeSecond pr.2))
    then V (pr.1, decodeFirst pr.2)
    else Part.none

/-- The fixed-length wrapper remains a partial recursive decompressor. -/
theorem conditionalPlainLengthDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (conditionalPlainLengthDecompressor V) := by
  unfold conditionalPlainLengthDecompressor isDecompressor
  have hcond : Computable (fun (pr : BitString × BitString) =>
      pr.1.length == decodeBits (decodeSecond pr.2)) := by
    apply Primrec.to_comp
    apply Primrec₂.comp Primrec.beq
    · apply Primrec.list_length.comp Primrec.fst
    · apply primrecDecodeBits.comp (decodeSecond_primrec'.comp Primrec.snd)
  have hbody : Partrec (fun (pr : BitString × BitString) => V (pr.1, decodeFirst pr.2)) := by
    apply hV.comp
    apply Computable.pair
    · exact Computable.fst
    · apply Primrec.to_comp (decodeFirst_primrec'.comp Primrec.snd)
  exact Partrec.cond hcond hbody Partrec.none

/-- At each context, the fixed-length wrapper has prefix-free domain. -/
theorem conditionalPlainLengthDecompressor_isPrefixMachine
    (V : Map) :
    IsPrefixMachine (conditionalPlainLengthDecompressor V) := by
  intro y p hp q hq hpre
  unfold domainAt conditionalPlainLengthDecompressor at hp hq
  dsimp at hp hq
  have hp_cond : p.length == decodeBits (decodeSecond y) := by
    cases h : p.length == decodeBits (decodeSecond y)
    · rw [h] at hp; change False at hp; exact False.elim hp
    · rfl
  have hq_cond : q.length == decodeBits (decodeSecond y) := by
    cases h : q.length == decodeBits (decodeSecond y)
    · rw [h] at hq; change False at hq; exact False.elim hq
    · rfl
  have hlen : p.length = q.length := by
    have h1 := beq_iff_eq.mp hp_cond
    have h2 := beq_iff_eq.mp hq_cond
    omega
  exact hpre.eq_of_length hlen

/-- A `V`-program is accepted when its exact length is supplied in the
context. -/
theorem conditionalPlainLengthDecompressor_produces
    {V : Map} {p y x : BitString} {k : Nat}
    (hprod : produces V p y x) (hlen : p.length = k) :
    produces (conditionalPlainLengthDecompressor V) p
      (pairCode y (Nat.bits k)) x := by
  unfold produces conditionalPlainLengthDecompressor
  dsimp
  have hlen' : p.length == decodeBits (decodeSecond (pairCode y (Nat.bits k))) := by
    rw [decodeSecond_pairCode, decodeBits_natBits, hlen]
    exact beq_self_eq_true k
  rw [hlen', cond_true, decodeFirst_pairCode]
  exact hprod

/-- Exact conditional plain complexity becomes an upper bound for conditional
prefix complexity when that exact program length is included in the context.
The additive constant is uniform in the strings and in the complexity value. -/
theorem KP_le_condK_given_plain_program_length
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (k : Nat),
      condK V x y = (k : ENat) →
      KP U x (pairCode y (Nat.bits k)) ≤ (k + c : Nat) := by
  have hM : IsPrefixDecompressor (conditionalPlainLengthDecompressor V) :=
    ⟨conditionalPlainLengthDecompressor_partrec V hV.1,
      conditionalPlainLengthDecompressor_isPrefixMachine V⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, ?_⟩
  intro x y k hk
  have hfinite : KP V x y ≠ ⊤ := by
    rw [KP_eq_condK, hk]
    exact ENat.natCast_ne_top k
  obtain ⟨p, hp, hpLen⟩ :=
    exists_program_of_KP_ne_top (M := V) (x := x) (y := y) hfinite
  have hpLenNat : p.length = k := by
    have : (p.length : ENat) = (k : ENat) := by
      rw [hpLen, KP_eq_condK, hk]
    exact_mod_cast this
  have hpWrapped : produces (conditionalPlainLengthDecompressor V) p
      (pairCode y (Nat.bits k)) x :=
    conditionalPlainLengthDecompressor_produces hp hpLenNat
  calc
    KP U x (pairCode y (Nat.bits k))
        ≤ KP (conditionalPlainLengthDecompressor V) x
            (pairCode y (Nat.bits k)) + (c : ENat) :=
          hc x (pairCode y (Nat.bits k))
    _ ≤ (p.length : ENat) + (c : ENat) := by
          gcongr
          exact KP_le_programLength_of_produces hpWrapped
    _ = (k + c : Nat) := by
          rw [hpLenNat]
          norm_cast

/-- Algebraic projection half of add-noise.  The hypothesis explicitly
accounts for the information lost by first-coordinate projection; point-mass
domination then converts it into the stated deficiency loss. -/
theorem deficiency_fstPushforward_of_complexity
    (U : Map) (P : CodedFiniteDistribution)
    (z : BitString) (beta delta : Nat)
    (hcomplexity :
      KP U z P.code ≤
        KP U (decodeFirst z) (codedFstPushforward P).code + delta)
    (hdef : DeficiencyLe U P z beta) :
    DeficiencyLe U (codedFstPushforward P)
      (decodeFirst z) (beta + delta) := by
  have hweight :
      complexityWeight (KP U (decodeFirst z) (codedFstPushforward P).code) *
          (2 : ENNReal)⁻¹ ^ delta ≤
        complexityWeight (KP U z P.code) := by
    simpa only [complexityWeight_add_nat] using
      (complexityWeight_le_of_le hcomplexity)
  have hcancel : (2 : ENNReal)⁻¹ ^ delta * (2 : ENNReal) ^ delta = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  unfold DeficiencyLe CodedFiniteDistribution.DeficiencyLe at *
  calc
    complexityWeight (KP U (decodeFirst z) (codedFstPushforward P).code)
        = complexityWeight (KP U (decodeFirst z) (codedFstPushforward P).code) * 1 := by
          rw [mul_one]
    _ = (complexityWeight (KP U (decodeFirst z) (codedFstPushforward P).code) *
          (2 : ENNReal)⁻¹ ^ delta) * (2 : ENNReal) ^ delta := by
          rw [mul_assoc, hcancel, mul_one]
    _ ≤ complexityWeight (KP U z P.code) * (2 : ENNReal) ^ delta := by
          gcongr
    _ ≤ ((2 : ENNReal) ^ beta * P.mass z) * (2 : ENNReal) ^ delta := by
          gcongr
    _ = (2 : ENNReal) ^ (beta + delta) * P.mass z := by
          rw [pow_add]
          ring
    _ ≤ (2 : ENNReal) ^ (beta + delta) * (codedFstPushforward P).mass (decodeFirst z) := by
          gcongr
          exact codedFstPushforward_mass_ge P z

/-- Replacing the executable source condition `(P.code,m)` by the canonical
uniform-extension code costs only a uniform machine constant. -/
theorem KP_sourceCondition_le_pairUniformExtension
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ P m z,
      KP U z (pairCode P.code (natCode m)) ≤
        KP U z (codedPairUniformExtension P m).code + c := by
  obtain ⟨c, hc⟩ := KP_cond_map_le U hU codedPairUniformExtensionCode
    codedPairUniformExtensionCode_computable
  refine ⟨c, fun P m z => ?_⟩
  rw [← codedPairUniformExtensionCode_eq P m]
  exact hc z (pairCode P.code (natCode m))

/-- The extension deficiency lemma can consume a lower bound stated at the
natural executable source condition `(P.code,m)`; changing to the canonical
extension code costs only the uniform constant above. -/
theorem deficiency_pairUniformExtension_of_sourceCondition
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (P : CodedFiniteDistribution) (a u : BitString)
      (m beta delta : Nat),
      u.length = m →
      KP U a P.code + (m : ENat) ≤
        KP U (pairCode a u) (pairCode P.code (natCode m)) +
          (delta : ENat) →
      DeficiencyLe U P a beta →
      DeficiencyLe U (codedPairUniformExtension P m)
        (pairCode a u) (beta + delta + c) := by
  obtain ⟨c, hc⟩ := KP_sourceCondition_le_pairUniformExtension U hU
  refine ⟨c, ?_⟩
  intro P a u m beta delta hu hcomplexity hdef
  have hcomplexity' :
      KP U a P.code + (m : ENat) ≤
        KP U (pairCode a u) (codedPairUniformExtension P m).code +
          ((delta + c : Nat) : ENat) := by
    calc
      KP U a P.code + (m : ENat)
          ≤ KP U (pairCode a u) (pairCode P.code (natCode m)) +
              (delta : ENat) := hcomplexity
      _ ≤ (KP U (pairCode a u) (codedPairUniformExtension P m).code +
              (c : ENat)) + (delta : ENat) := by
            gcongr
            exact hc P m (pairCode a u)
      _ = KP U (pairCode a u) (codedPairUniformExtension P m).code +
              ((delta + c : Nat) : ENat) := by
            rw [Nat.cast_add]
            ac_rfl
  simpa [Nat.add_assoc] using
    deficiency_pairUniformExtension_of_complexity U P a u m beta
      (delta + c) hu hcomplexity' hdef

/-- Replacing a distribution-code condition by its canonical projected code
costs only a uniform machine constant.  This changes the condition, not the
output; it deliberately does not claim the missing projection information
inequality. -/
theorem KP_sourceCondition_le_fstPushforward
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ P z,
      KP U z P.code ≤
        KP U z (codedFstPushforward P).code + c := by
  obtain ⟨c, hc⟩ := KP_cond_map_le U hU codedFstPushforwardCode codedFstPushforwardCode_computable
  refine ⟨c, fun P z => ?_⟩
  rw [← codedFstPushforwardCode_eq P]
  exact hc z P.code


/-- A source-model conditional complexity bound yields stochasticity of the pair
under the canonical uniform extension, with uniform logarithmic model-complexity
slack and deficiency slack. -/
theorem pairUniformExtension_stochasticity_of_condition_bound
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (P : CodedFiniteDistribution) (a u : BitString)
      (m alpha beta delta : Nat),
      u.length = m →
      P.IsProbability →
      P.complexity U ≤ (alpha : ENat) →
      DeficiencyLe U P a beta →
      KP U a P.code + (m : ENat) ≤
        KP U (pairCode a u)
          (pairCode P.code (natCode m)) + (delta : ENat) →
      IsStochastic U (pairCode a u)
        (alpha + logSlack c m) (beta + delta + c) := by
  obtain ⟨c, hc_source⟩ := deficiency_pairUniformExtension_of_sourceCondition U hU
  obtain ⟨c', hc_complexity⟩ := codedPairUniformExtension_complexity_le U hU
  refine ⟨c + c', fun P a u m alpha beta delta hu hP hPcomp hdef hcomplexity => ?_⟩
  have hdef' := hc_source P a u m beta delta hu hcomplexity hdef
  have hdef'' :
      DeficiencyLe U (codedPairUniformExtension P m) (pairCode a u)
        (beta + delta + (c + c')) := by
    exact hdef'.mono_beta (by omega : beta + delta + c ≤ beta + delta + (c + c'))
  have hprob : (codedPairUniformExtension P m).IsProbability :=
    codedPairUniformExtension_isProbability P m hP
  have hcomp : (codedPairUniformExtension P m).complexity U ≤
      P.complexity U + (logSlack c' m : ENat) := hc_complexity P m
  refine isStochastic_of_model U (pairCode a u) (codedPairUniformExtension P m)
    (alpha + logSlack (c + c') m) (beta + delta + (c + c')) hprob ?_ hdef''
  calc
    (codedPairUniformExtension P m).complexity U
        ≤ P.complexity U + (logSlack c' m : ENat) := hcomp
    _ ≤ (alpha : ENat) + (logSlack c' m : ENat) := by gcongr
    _ ≤ (alpha + logSlack (c + c') m : ENat) := by
        have : logSlack c' m ≤ logSlack (c + c') m := by
          exact logSlack_mono_left (by omega : c' ≤ c + c') m
        gcongr

end Kolmogorov
