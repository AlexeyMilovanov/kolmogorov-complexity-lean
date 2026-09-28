import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LchLemma
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropMinHereditary
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Part01

/-!
# The arithmetic of the hereditary slack budget

Every overhead of the hereditary construction has to be paid out of a single budget, the
hereditary slack `hereditarySlack c delta epsilon n`.  This module is the arithmetic of that
budget.  The slack of a constant is exactly that constant times the unit `hereditaryUnit`, so
an overhead fits the slack of some constant precisely when it is a constant multiple of the
unit.  The module absorbs a logarithmic shift into the slack
(`hereditary_shift_slack_absorb`), bounds the Omega chain (`hereditary_omega_chain`), collects
the powers-of-`b` bookkeeping of the `G -> L -> M -> M1 -> F1 -> F` construction
(`hereditary_core_budget_sum`, `hereditary_core_budget_strength`, `hereditary_core_arith`) and
records the budget of every step of the assembly, from `hereditary_lch_step_budget` to
`hereditary_family_step_budget`.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- One logarithmic shift term is absorbed by the hereditary slack: for all `cOut, cShift`
there is a `cNormal` such that `hereditarySlack cOut δ ε n + logSlack cShift r` is at most
`hereditarySlack cNormal δ ε n`, for every `r` bounded by `n + δ + 2·hereditarySlack cOut δ ε n`.
The hereditary slack is linear in its constant, the shift only logarithmic in `r`. -/
lemma hereditary_shift_slack_absorb (cOut cShift : Nat) :
    ∃ cNormal : Nat, ∀ delta epsilon n r : Nat,
      r ≤ n + delta + 2 * hereditarySlack cOut delta epsilon n →
      hereditarySlack cOut delta epsilon n + logSlack cShift r ≤
        hereditarySlack cNormal delta epsilon n := by
  -- `hereditarySlack c` is LINEAR in `c`, and `logSlack cShift r` is LOGARITHMIC
  -- in `r`.  Bounding `|bits r|` by the *sizes* of the summands of `r` keeps the
  -- whole shift cost inside the √n-scale slack (unlike the linear bound
  -- `|bits r| ≤ r`, which would introduce an unabsorbable `cShift * n` term).
  -- The `2 *` on the shift-cost budget `r` covers the `O(log n)` gap between the
  -- interesting condition `i + S < C(A)` and `C(A) ≤ n + delta + O(log n)`.
  refine ⟨(2 * cShift + 1) * cOut + 4 * cShift + 4, ?_⟩
  intro delta epsilon n r hr
  have hbr : (Nat.bits r).length ≤
      (Nat.bits n).length + delta + 2 * hereditarySlack cOut delta epsilon n + 2 := by
    have h1 : (Nat.bits r).length
        ≤ (Nat.bits (n + delta + 2 * hereditarySlack cOut delta epsilon n)).length :=
      length_natBits_mono hr
    have h2 : (Nat.bits (n + delta + 2 * hereditarySlack cOut delta epsilon n)).length ≤
        (Nat.bits (n + delta)).length
          + (Nat.bits (2 * hereditarySlack cOut delta epsilon n)).length + 1 :=
      length_natBits_add_le (n + delta) (2 * hereditarySlack cOut delta epsilon n)
    have h3 : (Nat.bits (n + delta)).length ≤
        (Nat.bits n).length + (Nat.bits delta).length + 1 :=
      length_natBits_add_le n delta
    have h4 : (Nat.bits delta).length ≤ delta := length_natBits_le delta
    have h5 : (Nat.bits (2 * hereditarySlack cOut delta epsilon n)).length
        ≤ 2 * hereditarySlack cOut delta epsilon n := length_natBits_le _
    omega
  have hlog : logSlack cShift r ≤
      cShift * ((Nat.bits n).length + delta + 2 * hereditarySlack cOut delta epsilon n + 2)
        + cShift := by
    unfold logSlack
    have := Nat.mul_le_mul_left cShift hbr
    omega
  have hbnP : (Nat.bits n).length ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n := by
    by_cases hn0 : n = 0
    · subst hn0; simp
    · have hsq : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (Nat.zero_lt_of_ne_zero hn0)
      calc (Nat.bits n).length ≤ epsilon + (Nat.bits n).length := Nat.le_add_left _ _
        _ = (epsilon + (Nat.bits n).length) * 1 := (Nat.mul_one _).symm
        _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n := Nat.mul_le_mul_left _ hsq
  unfold hereditarySlack at hlog ⊢
  set bn := (Nat.bits n).length with hbndef
  set P := (epsilon + bn) * Nat.sqrt n with hPdef
  have hassoc : ∀ c : Nat, c * (epsilon + bn) * Nat.sqrt n = c * P := by
    intro c; rw [hPdef]; ring
  rw [hassoc cOut, hassoc ((2 * cShift + 1) * cOut + 4 * cShift + 4)] at *
  nlinarith [hbnP, hlog, Nat.zero_le delta, Nat.zero_le P, Nat.zero_le bn,
    Nat.zero_le cShift, Nat.zero_le cOut,
    Nat.mul_le_mul_left cShift hbnP, Nat.mul_le_mul_left (2 * cShift) hbnP]

/-- Both codes of the hereditary chain have finite plain complexity, and their values obey the
three bounds the chain uses: the model `A` is inside the visible budget `n + delta + b`, the set
`M` exceeds it by at most `delta`, and `M` is inside the doubled budget `n + 2 delta + b`. -/
lemma plainK_codes_bounds_of_setComplexity_le {V : Map} {A M : Finset BitString}
    {hA : A.Nonempty} {hM : M.Nonempty} {n delta b : Nat}
    (hABound : plainSetComplexity V A hA ≤ ((n + delta + b : Nat) : ENat))
    (hMA : plainSetComplexity V M hM ≤ plainSetComplexity V A hA + (delta : ENat)) :
    plainK V (codedUniformOn A hA).code =
        (((plainK V (codedUniformOn A hA).code).toNat : Nat) : ENat) ∧
      plainK V (codedUniformOn M hM).code =
        (((plainK V (codedUniformOn M hM).code).toNat : Nat) : ENat) ∧
      (plainK V (codedUniformOn A hA).code).toNat ≤ n + delta + b ∧
      (plainK V (codedUniformOn M hM).code).toNat ≤
        (plainK V (codedUniformOn A hA).code).toNat + delta ∧
      (plainK V (codedUniformOn M hM).code).toNat ≤ n + 2 * delta + b := by
  have hAFinite : plainK V (codedUniformOn A hA).code ≠ ⊤ := by
    change plainSetComplexity V A hA ≠ ⊤
    exact ne_top_of_le_ne_top (ENat.coe_ne_top (n + delta + b)) hABound
  have hMBound : plainSetComplexity V M hM ≤ ((n + 2 * delta + b : Nat) : ENat) := by
    calc
      plainSetComplexity V M hM ≤ plainSetComplexity V A hA + (delta : ENat) := hMA
      _ ≤ ((n + delta + b : Nat) : ENat) + (delta : ENat) := by
          push_cast
          exact add_le_add hABound le_rfl
      _ = ((n + 2 * delta + b : Nat) : ENat) := by
          push_cast
          ring
  have hMFinite : plainK V (codedUniformOn M hM).code ≠ ⊤ := by
    change plainSetComplexity V M hM ≠ ⊤
    exact ne_top_of_le_ne_top (ENat.coe_ne_top (n + 2 * delta + b)) hMBound
  have haValue := (ENat.coe_toNat hAFinite).symm
  have hmValue := (ENat.coe_toNat hMFinite).symm
  refine ⟨haValue, hmValue, ?_, ?_, ?_⟩
  · have h : (((plainK V (codedUniformOn A hA).code).toNat : Nat) : ENat) ≤
        ((n + delta + b : Nat) : ENat) := by
      rw [← haValue]
      exact hABound
    exact_mod_cast h
  · have h : (((plainK V (codedUniformOn M hM).code).toNat : Nat) : ENat) ≤
        (((plainK V (codedUniformOn A hA).code).toNat : Nat) : ENat) + (delta : ENat) := by
      rw [← haValue, ← hmValue]
      exact hMA
    exact_mod_cast h
  · have h : (((plainK V (codedUniformOn M hM).code).toNat : Nat) : ENat) ≤
        ((n + 2 * delta + b : Nat) : ENat) := by
      rw [← hmValue]
      exact hMBound
    exact_mod_cast h

/-- The `Ω`-fixed-code chain of the hereditary assembly: if `A` is a minimal model of `x`
within logarithmic precision and `M` is a set whose complexity does not exceed that of `A`
by more than `delta`, then `M` is described from `A` at cost
`cOut·delta + cOut·√n + O(log n)`, provided the code of `M` is described from the
`Ω`-fixed code of its own complexity at the LCH cost `cLch·√n + O(log n)`. -/
lemma hereditary_omega_chain
    (V T : Map) (hV : isOptimalConditional V) (_hT : IsOptimalTotalConditional T)
    (cLch : Nat) :
    ∃ cKappa cOut : Nat,
      ∀ x n A (hA : A.Nonempty) M (hM : M.Nonempty) delta
        (q : Nat.Partrec.Code) (_hq : IsCodeFor q V),
        x.length = n →
        IsMinimalModel V x A hA delta (logSlack cKappa n) →
        plainSetComplexity V M hM ≤ plainSetComplexity V A hA + (delta : ENat) →
        condK V (codedUniformOn M hM).code
          (omegaFixedCode q (plainK V (codedUniformOn M hM).code).toNat) ≤
            (cLch * Nat.sqrt n + logSlack cLch n : ENat) →
        condK V (codedUniformOn M hM).code (codedUniformOn A hA).code ≤
          (cOut * delta + cOut * Nat.sqrt n + logSlack cOut n : ENat) := by
  obtain ⟨cKappaMin, cMin, hMin⟩ := prop_min_hereditary V hV
  obtain ⟨cKappaBound, cBound, hBound⟩ :=
    minimalModel_plainSetComplexity_le V hV
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cBridge, hBridge⟩ :=
    omegaFixedCode_bridge_linear V hV c hc 0
  obtain ⟨cBridgeLin, hBridgeLin⟩ :=
    logSlack_linear_bound cBridge (cBound + 3) cBound
  obtain ⟨cTrans, hTrans⟩ := condK_trans_nat V hV
  obtain ⟨cDrop, hDrop⟩ := condK_le_plainK V hV
  let cKappa := cKappaMin + cKappaBound
  let cOut :=
    4 * cMin + 2 * cBridgeLin + cLch +
      3 * cTrans + 2 * cBound + cDrop + 10
  refine ⟨cKappa, cOut, ?_⟩
  intro x n A hA M hM delta q hq hn hMinimal hMA hLch
  have hMinForMin :
      IsMinimalModel V x A hA delta (logSlack cKappaMin n) :=
    IsMinimalModel.mono le_rfl
      (logSlack_mono_left (by dsimp [cKappa]; omega) n) hMinimal
  have hMinForBound :
      IsMinimalModel V x A hA delta (logSlack cKappaBound n) :=
    IsMinimalModel.mono le_rfl
      (logSlack_mono_left (by dsimp [cKappa]; omega) n) hMinimal
  have hABound := hBound x n A hA delta hn hMinForBound
  let codeA := (codedUniformOn A hA).code
  let codeM := (codedUniformOn M hM).code
  let a := (plainK V codeA).toNat
  let m := (plainK V codeM).toNat
  obtain ⟨haV, hmV, haB, hmG, hmB⟩ := plainK_codes_bounds_of_setComplexity_le hABound hMA
  have haValue : plainK V codeA = (a : ENat) := haV
  have hmValue : plainK V codeM = (m : ENat) := hmV
  have haBound : a ≤ n + delta + logSlack cBound n := haB
  have hmGap : m ≤ a + delta := hmG
  have hmBound : m ≤ n + 2 * delta + logSlack cBound n := hmB
  have hMBound : plainK V codeM ≤ ((n + 2 * delta + logSlack cBound n : Nat) : ENat) := by
    rw [hmValue]
    exact_mod_cast hmBound
  by_cases hDelta : delta < n
  · let visible := n + 2 * delta + logSlack cBound n
    have hVisibleLinear : visible ≤ (cBound + 3) * n + cBound := by
      dsimp [visible]
      unfold logSlack
      have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
      nlinarith
    have hBridgeSlack : logSlack cBridge visible ≤
        logSlack cBridgeLin n :=
      (logSlack_mono_right cBridge hVisibleLinear).trans (hBridgeLin n)
    have haVisible : a ≤ visible := by
      dsimp [visible]
      omega
    have hmVisible : m ≤ visible := by
      simpa [visible] using hmBound
    have hOmegaRaw := hBridge visible m a
      (by simpa [logSlack] using hmVisible)
      (by simpa [logSlack] using haVisible)
    have hOmega :
        condK V (omegaFixedCode c m) (omegaFixedCode c a) ≤
          ((delta + logSlack cBridgeLin n : Nat) : ENat) := by
      calc
        condK V (omegaFixedCode c m) (omegaFixedCode c a)
            ≤ (((m - a) + logSlack cBridge visible : Nat) : ENat) := hOmegaRaw
        _ ≤ ((delta + logSlack cBridgeLin n : Nat) : ENat) := by
              exact_mod_cast (show m - a + logSlack cBridge visible ≤
                delta + logSlack cBridgeLin n by omega)
    have hMinCond :
        condK V (omegaFixedCode c a) codeA ≤
          ((cMin * delta + logSlack cMin n : Nat) : ENat) := by
      simpa [codeA, a] using
        hMin x n A hA delta c hc hn hMinForMin
    have hCodeSwap : omegaFixedCode q m = omegaFixedCode c m :=
      omegaFixedCode_eq_of_isCodeFor hq hc m
    have hLchFixed : condK V codeM (omegaFixedCode c m) ≤
        ((cLch * Nat.sqrt n + logSlack cLch n : Nat) : ENat) := by
      change condK V codeM (omegaFixedCode q m) ≤
        ((cLch * Nat.sqrt n + logSlack cLch n : Nat) : ENat) at hLch
      rw [hCodeSwap] at hLch
      exact hLch
    have hFirst := hTrans codeA (omegaFixedCode c a)
      (omegaFixedCode c m)
      (cMin * delta + logSlack cMin n)
      (delta + logSlack cBridgeLin n) hMinCond hOmega
    have hFinal := hTrans codeA (omegaFixedCode c m) codeM
      (2 * (cMin * delta + logSlack cMin n) +
        (delta + logSlack cBridgeLin n) + cTrans)
      (cLch * Nat.sqrt n + logSlack cLch n) hFirst hLchFixed
    calc
      condK V codeM codeA
          ≤ ((2 * (2 * (cMin * delta + logSlack cMin n) +
                (delta + logSlack cBridgeLin n) + cTrans) +
              (cLch * Nat.sqrt n + logSlack cLch n) + cTrans : Nat) : ENat) :=
            hFinal
      _ ≤ ((cOut * delta + cOut * Nat.sqrt n + logSlack cOut n : Nat) : ENat) := by
            apply Nat.cast_le.mpr
            dsimp [cOut]
            unfold logSlack
            nlinarith [Nat.zero_le (Nat.bits n).length, Nat.zero_le (Nat.sqrt n)]
  · have hLarge : n ≤ delta := Nat.le_of_not_gt hDelta
    calc
      condK V codeM codeA ≤ plainK V codeM + (cDrop : ENat) := hDrop _ _
      _ ≤ ((n + 2 * delta + logSlack cBound n : Nat) : ENat) +
            (cDrop : ENat) := by gcongr
      _ = ((n + 2 * delta + logSlack cBound n + cDrop : Nat) : ENat) := by
            push_cast
            ring
      _ ≤ ((cOut * delta + cOut * Nat.sqrt n + logSlack cOut n : Nat) : ENat) := by
            apply Nat.cast_le.mpr
            dsimp [cOut]
            unfold logSlack
            have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
            nlinarith [Nat.zero_le (Nat.sqrt n)]

/-- The LCH two-part overhead `cLch * (epsilon + log n) * sqrt n` is linear in
the visible budget `U`. -/
lemma budget_lch_pow {b U W n eps c : Nat} (hb : 3 ≤ b)
    (hW : W = (eps + (Nat.bits n).length) * Nat.sqrt n) (hWU : W ≤ U)
    (hLb1 : 1 ≤ (Nat.bits n).length) (hc : c ≤ b) :
    c * (eps + logSlack c n) * Nat.sqrt n ≤ b ^ 3 * U := by
  have hb2 : 2 ≤ b := by omega
  have h1 : eps + logSlack c n ≤ 2 * b * (eps + (Nat.bits n).length) := by
    unfold logSlack
    nlinarith [hLb1, hc, hb]
  have h2 : c * (eps + logSlack c n) * Nat.sqrt n ≤ 2 * b ^ 2 * W := by
    rw [hW]
    calc c * (eps + logSlack c n) * Nat.sqrt n
        ≤ (b * (2 * b * (eps + (Nat.bits n).length))) * Nat.sqrt n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hc h1)
      _ = 2 * b ^ 2 * ((eps + (Nat.bits n).length) * Nat.sqrt n) := by ring
  have h3 : 2 * b ^ 2 * W ≤ b ^ 3 * U := by
    calc 2 * b ^ 2 * W ≤ b * b ^ 2 * W :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb2)
      _ = b ^ 3 * W := by ring
      _ ≤ b ^ 3 * U := Nat.mul_le_mul_left _ hWU
  omega

private lemma budget_mono_pow {b U a k m : Nat} (hb : 1 ≤ b) (hk : k ≤ m)
    (h : a ≤ b ^ k * U) : a ≤ b ^ m * U :=
  h.trans (Nat.mul_le_mul_right U (Nat.pow_le_pow_right hb hk))

private lemma budget_add_pow {b U a1 a2 k : Nat} (hb : 2 ≤ b)
    (h1 : a1 ≤ b ^ k * U) (h2 : a2 ≤ b ^ k * U) : a1 + a2 ≤ b ^ (k + 1) * U := by
  have h : b ^ k * U + b ^ k * U ≤ b ^ (k + 1) * U := by
    calc b ^ k * U + b ^ k * U = 2 * (b ^ k * U) := by ring
      _ ≤ b * (b ^ k * U) := Nat.mul_le_mul_right _ hb
      _ = b ^ (k + 1) * U := by ring
  omega

private lemma budget_mul_pow {b U a c k : Nat} (hc : c ≤ b)
    (h : a ≤ b ^ k * U) : c * a ≤ b ^ (k + 1) * U := by
  calc c * a ≤ b * (b ^ k * U) := Nat.mul_le_mul hc h
    _ = b ^ (k + 1) * U := by ring

private lemma budget_const_pow {b U c : Nat} (hU : 1 ≤ U) (hc : c ≤ b) :
    c ≤ b ^ 1 * U := by
  calc c ≤ b := hc
    _ = b ^ 1 * 1 := by ring
    _ ≤ b ^ 1 * U := Nat.mul_le_mul_left _ hU

private lemma budget_logSlack_pow {b U c k a : Nat} (hb : 2 ≤ b) (hU : 1 ≤ U)
    (hc : c ≤ b) (h : (Nat.bits a).length ≤ b ^ k * U) :
    logSlack c a ≤ b ^ (k + 2) * U := by
  have h1 : c * (Nat.bits a).length ≤ b ^ (k + 1) * U := budget_mul_pow hc h
  have h2 : c ≤ b ^ (k + 1) * U :=
    budget_mono_pow (by omega) (by omega) (budget_const_pow hU hc)
  unfold logSlack
  exact budget_add_pow hb h1 h2

/-- Binary length of a quantity that is polynomial in `n`: it is logarithmic in
`n`, hence absorbed by two factors of the base constant. -/
private lemma budget_bits_of_le_two_mul {b U n m : Nat} (hb : 3 ≤ b) (hU : 1 ≤ U)
    (hLbU : (Nat.bits n).length ≤ U) (hm : m ≤ 2 * n + b) :
    (Nat.bits m).length ≤ b ^ 2 * U := by
  have h1 : (Nat.bits m).length ≤ (Nat.bits (2 * n + b)).length :=
    length_natBits_mono hm
  have h2 : (Nat.bits (2 * n + b)).length ≤
      (Nat.bits (2 * n)).length + (Nat.bits b).length + 1 :=
    length_natBits_add_le _ _
  have h3 : (Nat.bits (2 * n)).length ≤
      (Nat.bits n).length + (Nat.bits n).length + 1 := by
    simpa [two_mul] using length_natBits_add_le n n
  have h4 : (Nat.bits b).length ≤ b := length_natBits_le b
  have e1 : 2 * (Nat.bits n).length ≤ 2 * U := Nat.mul_le_mul_left 2 hLbU
  have e2 : b ≤ b * U := Nat.le_mul_of_pos_right _ hU
  have e3 : 2 ≤ 2 * U := Nat.le_mul_of_pos_right _ hU
  have e4 : (b + 4) * U = b * U + 2 * U + 2 * U := by ring
  have e5 : (b + 4) * U ≤ b ^ 2 * U := by
    have hle : b + 4 ≤ b ^ 2 := by nlinarith [hb]
    exact Nat.mul_le_mul_right _ hle
  omega

/-- Binary length of a quantity that is the sum of something polynomial in `n`
and something already inside the slack budget. -/
private lemma budget_bits_mix {b U n m k : Nat} (hb : 3 ≤ b) (hU : 1 ≤ U)
    (hLbU : (Nat.bits n).length ≤ U) (hm : m ≤ 2 * n + b + b ^ k * U) :
    (Nat.bits m).length ≤ b ^ (k + 3) * U := by
  have hb1 : 1 ≤ b := by omega
  have h1 : (Nat.bits m).length ≤ (Nat.bits (2 * n + b + b ^ k * U)).length :=
    length_natBits_mono hm
  have h2 : (Nat.bits (2 * n + b + b ^ k * U)).length ≤
      (Nat.bits (2 * n + b)).length + (Nat.bits (b ^ k * U)).length + 1 :=
    length_natBits_add_le _ _
  have h3 : (Nat.bits (2 * n + b)).length ≤ b ^ 2 * U :=
    budget_bits_of_le_two_mul hb hU hLbU le_rfl
  have h4 : (Nat.bits (b ^ k * U)).length ≤ b ^ k * U :=
    length_natBits_le _
  have h5 : b ^ 2 * U ≤ b ^ (k + 2) * U :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hb1 (by omega))
  have h6 : b ^ k * U ≤ b ^ (k + 2) * U :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hb1 (by omega))
  have h7 : 1 ≤ b ^ (k + 2) * U :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h8 : 3 * (b ^ (k + 2) * U) ≤ b ^ (k + 3) * U := by
    calc 3 * (b ^ (k + 2) * U) ≤ b * (b ^ (k + 2) * U) :=
          Nat.mul_le_mul_right _ hb
      _ = b ^ (k + 3) * U := by ring
  omega

private lemma budget_transport_pow {b U c e s k : Nat} (hb : 3 ≤ b) (hU : 1 ≤ U)
    (hc : c ≤ b) (he : e ≤ b ^ k * U) (hs : s ≤ b ^ k * U) :
    hereditaryStrongTransportStrength c e s ≤ b ^ (k + 9) * U := by
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hes : e + s ≤ b ^ (k + 1) * U := budget_add_pow hb2 he hs
  have hesbits : (Nat.bits (e + s)).length ≤ b ^ (k + 1) * U :=
    (length_natBits_le _).trans hes
  have hlog1 : logSlack c (e + s) ≤ b ^ (k + 3) * U :=
    budget_logSlack_pow hb2 hU hc hesbits
  have hfirst : e + s + logSlack c (e + s) ≤ b ^ (k + 4) * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hes) hlog1
  have hec : e + c ≤ b ^ (k + 2) * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) he)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU hc))
  have hinner : e + s + logSlack c (e + s) + e + c ≤ b ^ (k + 6) * U := by
    have h1 : e + s + logSlack c (e + s) + e ≤ b ^ (k + 5) * U :=
      budget_add_pow hb2 hfirst (budget_mono_pow hb1 (by omega) he)
    exact budget_add_pow hb2 h1
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU hc))
  have hlog2 : logSlack c (e + s + logSlack c (e + s) + e + c) ≤ b ^ (k + 8) * U :=
    budget_logSlack_pow hb2 hU hc ((length_natBits_le _).trans hinner)
  have hsum : e + s + logSlack c (e + s) + (e + c) ≤ b ^ (k + 8) * U :=
    budget_mono_pow hb1 (by omega)
      (budget_add_pow hb2 hfirst (budget_mono_pow hb1 (by omega) hec))
  change e + s + logSlack c (e + s) + (e + c) +
      logSlack c (e + s + logSlack c (e + s) + e + c) ≤ b ^ (k + 9) * U
  exact budget_add_pow hb2 hsum hlog2

/-- The intersection branch of the assembly — the ordinary chain `A₁ → A → M →
M₁`, the two-stage transfer to `A₁`, and the intersection estimate — stays
inside the visible budget. -/
lemma budget_deltaOrig_pow
    {b U n eps delta aComp a1Comp pF1 pPlain dOmega dChain a1Over deltaInter
      deltaOrig NOrig cPart cSimT cTwo cInter cChain cOmegaOut cSuff : Nat}
    (hb : 3 ≤ b) (hU1 : 1 ≤ U)
    (hepsU : eps ≤ U) (hdeltaU : delta ≤ U) (hsqrtU : Nat.sqrt n ≤ U)
    (hLbU : (Nat.bits n).length ≤ U)
    (hcPart : cPart ≤ b) (hcSimT : cSimT ≤ b) (hcTwo : cTwo ≤ b)
    (hcInter : cInter ≤ b) (hcChain : cChain ≤ b) (hcOmegaOut : cOmegaOut ≤ b)
    (hcSuff : cSuff ≤ b)
    (haComp : aComp ≤ 2 * n + b)
    (hpF1 : pF1 = eps + logSlack cPart n)
    (hpPlain : pPlain = pF1 + cSimT)
    (hdOmega : dOmega =
      cOmegaOut * delta + cOmegaOut * Nat.sqrt n + logSlack cOmegaOut n)
    (hdChain : dChain = cChain * (pF1 + dOmega) + cChain)
    (ha1Over : a1Over = pPlain + 2 * (Nat.bits aComp).length + cTwo)
    (hdeltaInter : deltaInter = dChain + 2 * (Nat.bits a1Comp).length + cInter)
    (hdeltaOrig : deltaOrig = a1Over + deltaInter)
    (hNOrig : NOrig = aComp + deltaOrig)
    (ha1CompLe : a1Comp ≤ aComp + a1Over) :
    pF1 ≤ b ^ 3 * U ∧ pPlain ≤ b ^ 4 * U ∧ deltaOrig ≤ b ^ 13 * U ∧
      logSlack cSuff NOrig ≤ b ^ 18 * U ∧
      eps + deltaOrig + logSlack cSuff NOrig ≤ b ^ 20 * U := by
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hepsP : eps ≤ b ^ 0 * U := by simpa using hepsU
  have hdeltaP : delta ≤ b ^ 0 * U := by simpa using hdeltaU
  have hsqrtP : Nat.sqrt n ≤ b ^ 0 * U := by simpa using hsqrtU
  have hbitsnP : (Nat.bits n).length ≤ b ^ 0 * U := by simpa using hLbU
  have hbitsA : (Nat.bits aComp).length ≤ b ^ 2 * U :=
    budget_bits_of_le_two_mul hb hU1 hLbU haComp
  have hpF1U : pF1 ≤ b ^ 3 * U := by
    rw [hpF1]
    exact budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hepsP)
      (budget_logSlack_pow hb2 hU1 hcPart hbitsnP)
  have hpPlainU : pPlain ≤ b ^ 4 * U := by
    rw [hpPlain]
    exact budget_add_pow hb2 hpF1U
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcSimT))
  have hdOmegaU : dOmega ≤ b ^ 4 * U := by
    rw [hdOmega]
    exact budget_add_pow hb2
      (budget_add_pow hb2
        (budget_mono_pow hb1 (by omega) (budget_mul_pow hcOmegaOut hdeltaP))
        (budget_mono_pow hb1 (by omega) (budget_mul_pow hcOmegaOut hsqrtP)))
      (budget_mono_pow hb1 (by omega)
        (budget_logSlack_pow hb2 hU1 hcOmegaOut hbitsnP))
  have hdChainU : dChain ≤ b ^ 7 * U := by
    rw [hdChain]
    have h1 : pF1 + dOmega ≤ b ^ 5 * U :=
      budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpF1U) hdOmegaU
    exact budget_add_pow hb2 (budget_mul_pow hcChain h1)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcChain))
  have ha1OverU : a1Over ≤ b ^ 6 * U := by
    rw [ha1Over]
    exact budget_add_pow hb2
      (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpPlainU)
        (budget_mono_pow hb1 (by omega)
          (budget_mul_pow (by omega : 2 ≤ b) hbitsA)))
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcTwo))
  have hbitsA1 : (Nat.bits a1Comp).length ≤ b ^ 9 * U :=
    budget_bits_mix hb hU1 hLbU
      (ha1CompLe.trans (Nat.add_le_add haComp ha1OverU))
  have hdeltaInterU : deltaInter ≤ b ^ 12 * U := by
    rw [hdeltaInter]
    exact budget_add_pow hb2
      (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hdChainU)
        (budget_mul_pow (by omega : 2 ≤ b) hbitsA1))
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcInter))
  have hdeltaOrigU : deltaOrig ≤ b ^ 13 * U := by
    rw [hdeltaOrig]
    exact budget_add_pow hb2 (budget_mono_pow hb1 (by omega) ha1OverU)
      hdeltaInterU
  have hlogNU : logSlack cSuff NOrig ≤ b ^ 18 * U :=
    budget_logSlack_pow hb2 hU1 hcSuff
      (budget_bits_mix hb hU1 hLbU
        (by rw [hNOrig]; exact Nat.add_le_add haComp hdeltaOrigU))
  refine ⟨hpF1U, hpPlainU, hdeltaOrigU, hlogNU, ?_⟩
  exact budget_add_pow hb2
    (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hepsP)
      (budget_mono_pow hb1 (by omega) hdeltaOrigU))
    (budget_mono_pow hb1 (by omega) hlogNU)

/-- The ordinary-complexity constants of the assembly stay inside the visible
budget. -/
lemma hereditary_core_budget_sum
    {b U n eps i mComp cardA cardA1 pF1 pPlain deltaOrig logN c5
      cLift cPart cFam cTrans cTwo : Nat}
    (hb : 3 ≤ b) (hU1 : 1 ≤ U) (hepsU : eps ≤ U)
    (hLbU : (Nat.bits n).length ≤ U)
    (hcLift : cLift ≤ b) (hcFam : cFam ≤ b)
    (hcTrans : cTrans ≤ b) (hcTwo : cTwo ≤ b)
    (hcardA : cardA ≤ 2 * n + b) (hcardA1 : cardA1 ≤ 2 * n + b)
    (hi : i ≤ 2 * n + b)
    (hpF1 : pF1 = eps + logSlack cPart n)
    (hpF1U : pF1 ≤ b ^ 3 * U) (hpPlainU : pPlain ≤ b ^ 4 * U)
    (hc6U : eps + deltaOrig + logN ≤ b ^ 20 * U)
    (hc5U : c5 ≤ b ^ 3 * U)
    (hmCompLe : mComp ≤ i + (logSlack cLift cardA + eps)) :
    (2 * (eps + logSlack cPart n) + cTrans) +
        (cFam * pF1 + logSlack cFam cardA1) +
        (pPlain + 2 * (Nat.bits mComp).length + cTwo) +
        logSlack cLift cardA + c5 +
        (eps + deltaOrig + logN) + eps + 2 ≤ b ^ 27 * U := by
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hepsP : eps ≤ b ^ 0 * U := by simpa using hepsU
  have hlogcardA : ∀ c : Nat, c ≤ b → logSlack c cardA ≤ b ^ 4 * U := fun c hc =>
    budget_logSlack_pow hb2 hU1 hc (budget_bits_of_le_two_mul hb hU1 hLbU hcardA)
  have hc1U : 2 * (eps + logSlack cPart n) + cTrans ≤ b ^ 5 * U := by
    have h1 : eps + logSlack cPart n ≤ b ^ 3 * U := by rw [← hpF1]; exact hpF1U
    exact budget_add_pow hb2 (budget_mul_pow (by omega : 2 ≤ b) h1)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcTrans))
  have hc2U : cFam * pF1 + logSlack cFam cardA1 ≤ b ^ 5 * U :=
    budget_add_pow hb2 (budget_mul_pow hcFam hpF1U)
      (budget_logSlack_pow hb2 hU1 hcFam
        (budget_bits_of_le_two_mul hb hU1 hLbU hcardA1))
  have hc4U : logSlack cLift cardA ≤ b ^ 4 * U := hlogcardA cLift hcLift
  have hbitsM : (Nat.bits mComp).length ≤ b ^ 8 * U := by
    refine budget_bits_mix hb hU1 hLbU ?_
    refine hmCompLe.trans (Nat.add_le_add hi ?_)
    exact budget_add_pow hb2 hc4U (budget_mono_pow hb1 (by omega) hepsP)
  have hc3U : pPlain + 2 * (Nat.bits mComp).length + cTwo ≤ b ^ 11 * U := by
    have h2 : 2 * (Nat.bits mComp).length ≤ b ^ 9 * U :=
      budget_mul_pow (by omega : 2 ≤ b) hbitsM
    exact budget_add_pow hb2
      (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpPlainU) h2)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcTwo))
  have t1 := budget_add_pow (a1 := 2 * (eps + logSlack cPart n) + cTrans)
    (a2 := cFam * pF1 + logSlack cFam cardA1) (k := 20) hb2
    (budget_mono_pow hb1 (by omega) hc1U) (budget_mono_pow hb1 (by omega) hc2U)
  have t2 := budget_add_pow (a2 := pPlain + 2 * (Nat.bits mComp).length + cTwo)
    (k := 21) hb2 (budget_mono_pow hb1 (by omega) t1)
    (budget_mono_pow hb1 (by omega) hc3U)
  have t3 := budget_add_pow (a2 := logSlack cLift cardA) (k := 22) hb2
    (budget_mono_pow hb1 (by omega) t2) (budget_mono_pow hb1 (by omega) hc4U)
  have t4 := budget_add_pow (a2 := c5) (k := 23) hb2
    (budget_mono_pow hb1 (by omega) t3) (budget_mono_pow hb1 (by omega) hc5U)
  have t5 := budget_add_pow (a2 := eps + deltaOrig + logN) (k := 24) hb2
    (budget_mono_pow hb1 (by omega) t4) (budget_mono_pow hb1 (by omega) hc6U)
  have t6 := budget_add_pow (a2 := eps) (k := 25) hb2
    (budget_mono_pow hb1 (by omega) t5) (budget_mono_pow hb1 (by omega) hepsP)
  exact budget_add_pow (a2 := 2) (k := 26) hb2
    (budget_mono_pow hb1 (by omega) t6)
    (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 (by omega : 2 ≤ b)))

/-- The transported strength of the assembly stays inside the visible budget. -/
lemma hereditary_core_budget_strength
    {b U n cardA gap pF1 cGap cFam cTrans : Nat}
    (hb : 3 ≤ b) (hU1 : 1 ≤ U) (hLbU : (Nat.bits n).length ≤ U)
    (hcGap : cGap ≤ b) (hcFam : cFam ≤ b) (hcTrans : cTrans ≤ b)
    (hcardA : cardA ≤ 2 * n + b)
    (hpF1U : pF1 ≤ b ^ 3 * U) (hgapU : gap ≤ b ^ 20 * U) :
    hereditaryStrongTransportStrength cTrans pF1
      (cFam * (pF1 + (cGap * pF1 + gap + logSlack cGap cardA)) + cFam) ≤ b ^ 34 * U := by
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hsF1U : cGap * pF1 + gap + logSlack cGap cardA ≤ b ^ 22 * U :=
    budget_add_pow hb2
      (budget_add_pow hb2
        (budget_mono_pow hb1 (by omega) (budget_mul_pow hcGap hpF1U)) hgapU)
      (budget_mono_pow hb1 (by omega)
        (budget_logSlack_pow hb2 hU1 hcGap
          (budget_bits_of_le_two_mul hb hU1 hLbU hcardA)))
  have hstrengthU :
      cFam * (pF1 + (cGap * pF1 + gap + logSlack cGap cardA)) + cFam ≤ b ^ 25 * U := by
    have h1 : pF1 + (cGap * pF1 + gap + logSlack cGap cardA) ≤ b ^ 23 * U :=
      budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpF1U) hsF1U
    exact budget_add_pow hb2 (budget_mul_pow hcFam h1)
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hcFam))
  exact budget_transport_pow hb hU1 hcTrans
    (budget_mono_pow hb1 (by omega) hpF1U) hstrengthU

/-- Final linear bookkeeping of the hereditary assembly: the ordinary
complexity bound and the two-part bound for the transported family, given the
numeric form of every step of the `G → L → M → M₁ → F₁ → F` construction. -/
lemma hereditary_core_arith
    {fComp f1Comp m1Comp mComp lComp gComp c1 c2 c3 c4 c5 c6 eps i j S
      cardF cardF1 cardM cardM1 cardL cardG cardA r : Nat}
    (n1 : fComp ≤ f1Comp + c1) (n2 : f1Comp ≤ m1Comp + c2)
    (n3 : m1Comp ≤ mComp + c3) (n4 : mComp + cardM ≤ lComp + cardL + c5)
    (n5 : lComp ≤ gComp + c4) (n6 : gComp ≤ i)
    (n7 : cardL ≤ cardG + cardA) (n8 : cardG ≤ j)
    (n9 : cardF ≤ cardF1) (n10 : cardF1 + r ≤ cardM1 + 2)
    (n11 : cardM1 ≤ cardM) (n12 : cardA ≤ r + c6)
    (n13 : mComp ≤ lComp + eps)
    (hbud : c1 + c2 + c3 + c4 + c5 + c6 + eps + 2 ≤ S) :
    fComp ≤ i + S ∧ fComp + cardF ≤ i + j + S := by
  omega

/-! ### The unit of the hereditary slack budget -/

/-- The unit of the hereditary slack: `delta + (epsilon + log n) * sqrt n + 1`.  The
hereditary slack of a constant `c` is exactly `c` times this unit, so an overhead lies
inside the slack of some constant exactly when it is a constant multiple of the unit. -/
def hereditaryUnit (delta epsilon n : Nat) : Nat :=
  delta + (epsilon + (Nat.bits n).length) * Nat.sqrt n + 1

/-- The hereditary slack of a constant is that constant times the unit budget. -/
lemma hereditarySlack_eq_mul_unit (c delta epsilon n : Nat) :
    hereditarySlack c delta epsilon n = c * hereditaryUnit delta epsilon n := by
  unfold hereditarySlack hereditaryUnit
  ring

/-- The hereditary slack is additive in its constant. -/
lemma hereditarySlack_add_c (c1 c2 delta epsilon n : Nat) :
    hereditarySlack (c1 + c2) delta epsilon n =
      hereditarySlack c1 delta epsilon n + hereditarySlack c2 delta epsilon n := by
  simp only [hereditarySlack_eq_mul_unit]
  ring

/-- The unit budget is positive. -/
lemma one_le_hereditaryUnit (delta epsilon n : Nat) :
    1 ≤ hereditaryUnit delta epsilon n := by
  unfold hereditaryUnit
  omega

/-- The minimality deficiency is inside the unit budget. -/
lemma delta_le_hereditaryUnit (delta epsilon n : Nat) :
    delta ≤ hereditaryUnit delta epsilon n := by
  unfold hereditaryUnit
  omega

/-- A string length with a positive integer square root has a positive binary length. -/
lemma one_le_bits_length_of_sqrt_pos {n : Nat} (h : 1 ≤ Nat.sqrt n) :
    1 ≤ (Nat.bits n).length := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  simpa [Nat.size_eq_bits_len] using Nat.size_pos.mpr hn

/-- The two-part product `(epsilon + log n) * sqrt n` is inside the unit budget. -/
lemma mul_sqrt_le_hereditaryUnit (delta epsilon n : Nat) :
    (epsilon + (Nat.bits n).length) * Nat.sqrt n ≤ hereditaryUnit delta epsilon n := by
  unfold hereditaryUnit
  omega

/-- The sufficiency parameter is inside the unit budget, for `n` with positive square root. -/
lemma epsilon_le_hereditaryUnit {n : Nat} (delta epsilon : Nat) (h : 1 ≤ Nat.sqrt n) :
    epsilon ≤ hereditaryUnit delta epsilon n := by
  refine le_trans ?_ (mul_sqrt_le_hereditaryUnit delta epsilon n)
  calc epsilon ≤ epsilon * Nat.sqrt n := Nat.le_mul_of_pos_right _ h
    _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n :=
        Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- The binary length of `n` is inside the unit budget, for `n` with positive square root. -/
lemma bitsLength_le_hereditaryUnit {n : Nat} (delta epsilon : Nat) (h : 1 ≤ Nat.sqrt n) :
    (Nat.bits n).length ≤ hereditaryUnit delta epsilon n := by
  refine le_trans ?_ (mul_sqrt_le_hereditaryUnit delta epsilon n)
  calc (Nat.bits n).length ≤ (Nat.bits n).length * Nat.sqrt n :=
        Nat.le_mul_of_pos_right _ h
    _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n :=
        Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- The square root of `n` is inside the unit budget, for `n` with positive square root. -/
lemma sqrt_le_hereditaryUnit {n : Nat} (delta epsilon : Nat) (h : 1 ≤ Nat.sqrt n) :
    Nat.sqrt n ≤ hereditaryUnit delta epsilon n := by
  refine le_trans ?_ (mul_sqrt_le_hereditaryUnit delta epsilon n)
  calc Nat.sqrt n ≤ (Nat.bits n).length * Nat.sqrt n :=
        Nat.le_mul_of_pos_left _ (one_le_bits_length_of_sqrt_pos h)
    _ ≤ (epsilon + (Nat.bits n).length) * Nat.sqrt n :=
        Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- The overhead of the lifting and LCH steps — the lift's logarithmic term in the
log-cardinality of the model, the sufficiency parameter and the LCH two-part cost — lies
inside the hereditary slack of `b ^ 5`, whenever all constants involved are at most `b`
and the model has log-cardinality at most `2 * n + b`. -/
lemma hereditary_lch_step_budget {b n eps delta cardA cLift cLch : Nat}
    (hb : 3 ≤ b) (hsqrt : 1 ≤ Nat.sqrt n) (hcardA : cardA ≤ 2 * n + b)
    (hcLift : cLift ≤ b) (hcLch : cLch ≤ b) :
    logSlack cLift cardA + eps + cLch * (eps + logSlack cLch n) * Nat.sqrt n ≤
      hereditarySlack (b ^ 5) delta eps n := by
  set U := hereditaryUnit delta eps n with hU
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hU1 : 1 ≤ U := one_le_hereditaryUnit delta eps n
  have hLbU : (Nat.bits n).length ≤ U := bitsLength_le_hereditaryUnit delta eps hsqrt
  have hepsU : eps ≤ U := epsilon_le_hereditaryUnit delta eps hsqrt
  have hlift : logSlack cLift cardA ≤ b ^ 4 * U :=
    budget_logSlack_pow hb2 hU1 hcLift (budget_bits_of_le_two_mul hb hU1 hLbU hcardA)
  have hlch : cLch * (eps + logSlack cLch n) * Nat.sqrt n ≤ b ^ 3 * U :=
    budget_lch_pow hb rfl (mul_sqrt_le_hereditaryUnit delta eps n)
      (one_le_bits_length_of_sqrt_pos hsqrt) hcLch
  have heps : eps ≤ b ^ 4 * U := by
    refine hepsU.trans ?_
    calc U = 1 * U := (Nat.one_mul U).symm
      _ ≤ b ^ 4 * U := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ (by omega))
  have hlch' : cLch * (eps + logSlack cLch n) * Nat.sqrt n ≤ b ^ 4 * U :=
    budget_mono_pow hb1 (by omega) hlch
  have hsum : b ^ 4 * U + b ^ 4 * U + b ^ 4 * U ≤ b ^ 5 * U := by
    have h3 : 3 * (b ^ 4 * U) ≤ b * (b ^ 4 * U) := Nat.mul_le_mul_right _ hb
    have : b * (b ^ 4 * U) = b ^ 5 * U := by ring
    omega
  rw [hereditarySlack_eq_mul_unit, ← hU]
  omega

/-- The `Ω`-chain bound on the conditional complexity of a model's code — linear in the
deficiency and in `sqrt n`, logarithmic in `n` — lies inside the hereditary slack of
`b ^ 3`, whenever its constant is at most `b`. -/
lemma hereditary_omega_step_budget {b n eps delta cOmega : Nat}
    (hb : 3 ≤ b) (hsqrt : 1 ≤ Nat.sqrt n) (hc : cOmega ≤ b) :
    cOmega * delta + cOmega * Nat.sqrt n + logSlack cOmega n ≤
      hereditarySlack (b ^ 3) delta eps n := by
  set U := hereditaryUnit delta eps n with hU
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hU1 : 1 ≤ U := one_le_hereditaryUnit delta eps n
  have hLbU : (Nat.bits n).length ≤ b ^ 0 * U := by
    simpa using bitsLength_le_hereditaryUnit delta eps hsqrt
  have hdeltaP : delta ≤ b ^ 0 * U := by simpa using delta_le_hereditaryUnit delta eps n
  have hsqrtP : Nat.sqrt n ≤ b ^ 0 * U := by
    simpa using sqrt_le_hereditaryUnit delta eps hsqrt
  have h1 : cOmega * delta ≤ b ^ 1 * U := budget_mul_pow hc hdeltaP
  have h2 : cOmega * Nat.sqrt n ≤ b ^ 1 * U := budget_mul_pow hc hsqrtP
  have h3 : logSlack cOmega n ≤ b ^ 2 * U := budget_logSlack_pow hb2 hU1 hc hLbU
  have h12 : cOmega * delta + cOmega * Nat.sqrt n ≤ b ^ 2 * U := budget_add_pow hb2 h1 h2
  rw [hereditarySlack_eq_mul_unit, ← hU]
  exact budget_add_pow hb2 h12 h3

/-- The costs of the partition step — the partition parameter `epsilon + logSlack c n` and
the same parameter with one extra constant charge — are inside the unit budget. -/
lemma hereditary_partition_cost_budget {b n eps delta c c' : Nat}
    (hb : 3 ≤ b) (hsqrt : 1 ≤ Nat.sqrt n) (hc : c ≤ b) (hc' : c' ≤ b) :
    eps + logSlack c n ≤ b ^ 3 * hereditaryUnit delta eps n ∧
      eps + logSlack c n + c' ≤ b ^ 4 * hereditaryUnit delta eps n := by
  set U := hereditaryUnit delta eps n with hU
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hU1 : 1 ≤ U := one_le_hereditaryUnit delta eps n
  have hepsP : eps ≤ b ^ 0 * U := by
    simpa using epsilon_le_hereditaryUnit delta eps hsqrt
  have hLbP : (Nat.bits n).length ≤ b ^ 0 * U := by
    simpa using bitsLength_le_hereditaryUnit delta eps hsqrt
  have hlog : logSlack c n ≤ b ^ 2 * U := budget_logSlack_pow hb2 hU1 hc hLbP
  have hfirst : eps + logSlack c n ≤ b ^ 3 * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hepsP) hlog
  refine ⟨hfirst, ?_⟩
  exact budget_add_pow hb2 hfirst
    (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hc'))

/-- The chain cost `c * (p + d) + c`, built from a partition cost `p` inside the budget and
an input bound `d` that is itself a hereditary slack, is inside the unit budget. -/
lemma hereditary_chain_cost_budget {b n eps delta p c cIn : Nat}
    (hb : 3 ≤ b) (hc : c ≤ b) (hcIn : cIn ≤ b)
    (hp : p ≤ b ^ 3 * hereditaryUnit delta eps n) :
    c * (p + hereditarySlack cIn delta eps n) + c ≤ b ^ 7 * hereditaryUnit delta eps n := by
  set U := hereditaryUnit delta eps n with hU
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hU1 : 1 ≤ U := one_le_hereditaryUnit delta eps n
  have hslack : hereditarySlack cIn delta eps n ≤ b ^ 3 * U := by
    rw [hereditarySlack_eq_mul_unit, ← hU]
    exact Nat.mul_le_mul_right _ (hcIn.trans (Nat.le_self_pow (by norm_num) b))
  have hsum : p + hereditarySlack cIn delta eps n ≤ b ^ 4 * U := budget_add_pow hb2 hp hslack
  have hmul : c * (p + hereditarySlack cIn delta eps n) ≤ b ^ 5 * U := budget_mul_pow hc hsum
  exact budget_mono_pow hb1 (by omega)
    (budget_add_pow hb2 hmul (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hc)))

/-- The intersection branch — the two-stage transfer of the partition class of `A` and the
intersection estimate against the partition class of the model — is inside the unit budget,
once the plain transfer cost and the chain cost are. -/
lemma hereditary_intersection_step_budget {b n eps delta aComp a1Comp pPlain dChain c c' : Nat}
    (hb : 3 ≤ b) (hsqrt : 1 ≤ Nat.sqrt n) (hc : c ≤ b) (hc' : c' ≤ b)
    (haComp : aComp ≤ 2 * n + b)
    (ha1Comp : a1Comp ≤ aComp + (pPlain + 2 * (Nat.bits aComp).length + c))
    (hpPlain : pPlain ≤ b ^ 4 * hereditaryUnit delta eps n)
    (hdChain : dChain ≤ b ^ 7 * hereditaryUnit delta eps n) :
    pPlain + 2 * (Nat.bits aComp).length + c +
        (dChain + 2 * (Nat.bits a1Comp).length + c') ≤
      b ^ 13 * hereditaryUnit delta eps n := by
  set U := hereditaryUnit delta eps n with hU
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hU1 : 1 ≤ U := one_le_hereditaryUnit delta eps n
  have hLbU : (Nat.bits n).length ≤ U := bitsLength_le_hereditaryUnit delta eps hsqrt
  have hbitsA : (Nat.bits aComp).length ≤ b ^ 2 * U :=
    budget_bits_of_le_two_mul hb hU1 hLbU haComp
  have ha1Over : pPlain + 2 * (Nat.bits aComp).length + c ≤ b ^ 6 * U := by
    refine budget_add_pow hb2 (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpPlain)
      (budget_mono_pow hb1 (by omega) (budget_mul_pow (by omega : 2 ≤ b) hbitsA))) ?_
    exact budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hc)
  have hbitsA1 : (Nat.bits a1Comp).length ≤ b ^ 9 * U :=
    budget_bits_mix hb hU1 hLbU (ha1Comp.trans (Nat.add_le_add haComp ha1Over))
  have hInter : dChain + 2 * (Nat.bits a1Comp).length + c' ≤ b ^ 12 * U := by
    refine budget_add_pow hb2 (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hdChain)
      (budget_mul_pow (by omega : 2 ≤ b) hbitsA1)) ?_
    exact budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hc')
  exact budget_add_pow hb2 (budget_mono_pow hb1 (by omega) ha1Over) hInter

/-- The sufficiency gap charged by the intersection estimate — the sufficiency parameter, the
total intersection overhead and the logarithmic charge for the resulting size — is inside the
unit budget. -/
lemma hereditary_gap_step_budget {b n eps delta aComp deltaOrig c : Nat}
    (hb : 3 ≤ b) (hsqrt : 1 ≤ Nat.sqrt n) (hc : c ≤ b) (haComp : aComp ≤ 2 * n + b)
    (hdeltaOrig : deltaOrig ≤ b ^ 13 * hereditaryUnit delta eps n) :
    eps + deltaOrig + logSlack c (aComp + deltaOrig) ≤
      b ^ 20 * hereditaryUnit delta eps n := by
  set U := hereditaryUnit delta eps n with hU
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hU1 : 1 ≤ U := one_le_hereditaryUnit delta eps n
  have hLbU : (Nat.bits n).length ≤ U := bitsLength_le_hereditaryUnit delta eps hsqrt
  have hepsP : eps ≤ b ^ 0 * U := by
    simpa using epsilon_le_hereditaryUnit delta eps hsqrt
  have hbitsN : (Nat.bits (aComp + deltaOrig)).length ≤ b ^ 16 * U :=
    budget_bits_mix hb hU1 hLbU (Nat.add_le_add haComp hdeltaOrig)
  have hlog : logSlack c (aComp + deltaOrig) ≤ b ^ 18 * U :=
    budget_logSlack_pow hb2 hU1 hc hbitsN
  have hfirst : eps + deltaOrig ≤ b ^ 14 * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hepsP) hdeltaOrig
  exact budget_mono_pow hb1 (by omega)
    (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hfirst) hlog)

/-- The ordinary-complexity overhead of the partition, family and transport steps — the
transport charge, the family charge, the two-stage transfer of the model to its partition
class, the sufficiency gap `b ^ 20 * hereditaryUnit delta eps n` and the two extra bits of the
partition — lies inside the hereditary slack of `b ^ 27`, whenever the partition log-cardinality
is at most `2 * n + b`, the model complexity at most `2 * n + b + hereditaryUnit delta eps n`,
the family charge at most `b ^ 3` and the plain charge at most `b ^ 4` hereditary units. -/
lemma hereditary_family_step_budget {b n eps delta cardA1 mComp pF1 pPlain : Nat}
    (hb : 3 ≤ b) (hsqrt : 1 ≤ Nat.sqrt n) (hcardA1 : cardA1 ≤ 2 * n + b)
    (hmComp : mComp ≤ 2 * n + b + hereditaryUnit delta eps n)
    (hpF1 : pF1 ≤ b ^ 3 * hereditaryUnit delta eps n)
    (hpPlain : pPlain ≤ b ^ 4 * hereditaryUnit delta eps n) :
    2 * pF1 + b + (b * pF1 + logSlack b cardA1) +
        (pPlain + 2 * (Nat.bits mComp).length + b) +
        b ^ 20 * hereditaryUnit delta eps n + 2 ≤
      hereditarySlack (b ^ 27) delta eps n := by
  set U := hereditaryUnit delta eps n with hU
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hU1 : 1 ≤ U := one_le_hereditaryUnit delta eps n
  have hLbU : (Nat.bits n).length ≤ U := bitsLength_le_hereditaryUnit delta eps hsqrt
  have hc1 : 2 * pF1 + b ≤ b ^ 5 * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) (budget_mul_pow (by omega : 2 ≤ b) hpF1))
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 le_rfl))
  have hc2 : b * pF1 + logSlack b cardA1 ≤ b ^ 5 * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) (budget_mul_pow le_rfl hpF1))
      (budget_logSlack_pow hb2 hU1 le_rfl (budget_bits_of_le_two_mul hb hU1 hLbU hcardA1))
  have hbitsM : (Nat.bits mComp).length ≤ b ^ 3 * U := by
    refine budget_bits_mix hb hU1 hLbU ?_
    simpa using hmComp
  have hc3 : pPlain + 2 * (Nat.bits mComp).length + b ≤ b ^ 6 * U := by
    refine budget_add_pow hb2 (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpPlain)
      (budget_mono_pow hb1 (by omega) (budget_mul_pow (by omega : 2 ≤ b) hbitsM))) ?_
    exact budget_mono_pow hb1 (by omega) (budget_const_pow hU1 le_rfl)
  have t1 : 2 * pF1 + b + (b * pF1 + logSlack b cardA1) ≤ b ^ 6 * U :=
    budget_add_pow hb2 hc1 hc2
  have t2 : 2 * pF1 + b + (b * pF1 + logSlack b cardA1) +
      (pPlain + 2 * (Nat.bits mComp).length + b) ≤ b ^ 7 * U :=
    budget_add_pow hb2 t1 hc3
  have t3 : 2 * pF1 + b + (b * pF1 + logSlack b cardA1) +
      (pPlain + 2 * (Nat.bits mComp).length + b) + b ^ 20 * U ≤ b ^ 21 * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) t2)
      (budget_mono_pow hb1 (by omega) le_rfl)
  have t4 := budget_add_pow (a2 := 2) hb2 t3
    (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 (by omega : 2 ≤ b)))
  rw [hereditarySlack_eq_mul_unit, ← hU]
  exact budget_mono_pow hb1 (by omega) t4

end Kolmogorov
