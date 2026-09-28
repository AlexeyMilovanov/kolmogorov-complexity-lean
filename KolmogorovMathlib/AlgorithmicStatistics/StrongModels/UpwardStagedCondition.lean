import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.OrdinalPlainRandomness
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StochasticTotalReduction
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWiseTotal.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWiseTotal

/-!
# Staged conditions for the pair-condition bound

The conditional symmetry chain of `KPCondPair` is stated relative to a *staged* condition
`prefixCondComplexityContext z x kx`.  This module collects the two computable rearrangements
of such a condition, the cost of passing from the model-side staged condition to the
string-side one, the resulting randomness transport, and the two size estimates (the advice
pair and a linear budget for the conditional complexity of the base string) that the pair
bound consumes.
-/

namespace Kolmogorov

/-- The rearrangement sending a staged condition `⟨x, ⟨p, k⟩⟩` to the plain pair `⟨x, p⟩`. -/
def pairConditionCore (w : BitString) : BitString :=
  pairCode (decodeFirst w) (decodeFirst (decodeSecond w))

/-- The core rearrangement of conditions is computable. -/
lemma pairConditionCore_computable : Computable pairConditionCore := by
  have hPair : Computable₂ (fun (a b : BitString) => pairCode a b) := pairCode_computable
  have hSecond : Computable (fun w : BitString => decodeFirst (decodeSecond w)) :=
    decodeFirst_computable.comp decodeSecond_computable
  exact hPair.comp decodeFirst_computable hSecond

/-- On a staged condition the core rearrangement returns the underlying pair. -/
lemma pairConditionCore_prefixCondComplexityContext (x p : BitString) (k : Nat) :
    pairConditionCore (prefixCondComplexityContext x p k) = pairCode x p := by
  simp [pairConditionCore, prefixCondComplexityContext, decodeFirst_pairCode,
    decodeSecond_pairCode]

/-- The rearrangement sending `⟨⟨x, p⟩, ⟨nn, k⟩⟩` to the staged condition
`⟨⟨p, nn⟩, ⟨x, k⟩⟩`. -/
def pairConditionEnriched (w : BitString) : BitString :=
  pairCode
    (pairCode (decodeSecond (decodeFirst w)) (decodeFirst (decodeSecond w)))
    (pairCode (decodeFirst (decodeFirst w)) (decodeSecond (decodeSecond w)))

/-- The enriched rearrangement of conditions is computable. -/
lemma pairConditionEnriched_computable : Computable pairConditionEnriched := by
  have hPair : Computable₂ (fun (a b : BitString) => pairCode a b) := pairCode_computable
  have hP : Computable (fun w : BitString => decodeSecond (decodeFirst w)) :=
    decodeSecond_computable.comp decodeFirst_computable
  have hN : Computable (fun w : BitString => decodeFirst (decodeSecond w)) :=
    decodeFirst_computable.comp decodeSecond_computable
  have hX : Computable (fun w : BitString => decodeFirst (decodeFirst w)) :=
    decodeFirst_computable.comp decodeFirst_computable
  have hK : Computable (fun w : BitString => decodeSecond (decodeSecond w)) :=
    decodeSecond_computable.comp decodeSecond_computable
  have hLeft : Computable (fun w : BitString =>
      pairCode (decodeSecond (decodeFirst w)) (decodeFirst (decodeSecond w))) :=
    hPair.comp hP hN
  have hRight : Computable (fun w : BitString =>
      pairCode (decodeFirst (decodeFirst w)) (decodeSecond (decodeSecond w))) :=
    hPair.comp hX hK
  exact hPair.comp hLeft hRight

/-- On a pair of a base condition and an advice pair the enriched rearrangement returns the
staged condition of `x` relative to `⟨p, nn⟩`. -/
lemma pairConditionEnriched_pairCode (x p : BitString) (nn k : Nat) :
    pairConditionEnriched (pairCode (pairCode x p) (pairCode (natCode nn) (natCode k))) =
      prefixCondComplexityContext (pairCode p (natCode nn)) x k := by
  simp [pairConditionEnriched, prefixCondComplexityContext, decodeFirst_pairCode,
    decodeSecond_pairCode]

/-- **Cost of restaging a condition.**  Passing from the condition `⟨x, ⟨p, kP⟩⟩` to the
condition `⟨⟨p, nn⟩, ⟨x, kx⟩⟩` costs the plain complexity of the advice pair `⟨nn, kx⟩` and a
constant. -/
lemma KP_stagedCondition_change (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x p y : BitString) (nn kx kP : Nat),
      KP U y (prefixCondComplexityContext x p kP) ≤
        KP U y (prefixCondComplexityContext (pairCode p (natCode nn)) x kx) +
          KPPlain U (pairCode (natCode nn) (natCode kx)) + (c : ENat) := by
  obtain ⟨cRemove, hRemove⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cCore, hCore⟩ :=
    KP_cond_map_le U hU pairConditionCore pairConditionCore_computable
  obtain ⟨cEnriched, hEnriched⟩ :=
    KP_cond_map_le U hU pairConditionEnriched pairConditionEnriched_computable
  refine ⟨cCore + cRemove + cEnriched, ?_⟩
  intro x p y nn kx kP
  calc
    KP U y (prefixCondComplexityContext x p kP)
        ≤ KP U y (pairConditionCore (prefixCondComplexityContext x p kP)) + (cCore : ENat) :=
          hCore y (prefixCondComplexityContext x p kP)
    _ = KP U y (pairCode x p) + (cCore : ENat) := by
          rw [pairConditionCore_prefixCondComplexityContext]
    _ ≤ (KP U y (pairCode (pairCode x p) (pairCode (natCode nn) (natCode kx))) +
          KPPlain U (pairCode (natCode nn) (natCode kx)) + (cRemove : ENat)) +
          (cCore : ENat) := by
          gcongr
          exact hRemove y (pairCode x p) (pairCode (natCode nn) (natCode kx))
    _ ≤ ((KP U y (pairConditionEnriched
            (pairCode (pairCode x p) (pairCode (natCode nn) (natCode kx)))) +
            (cEnriched : ENat)) +
          KPPlain U (pairCode (natCode nn) (natCode kx)) + (cRemove : ENat)) +
          (cCore : ENat) := by
          gcongr
          exact hEnriched y (pairCode (pairCode x p) (pairCode (natCode nn) (natCode kx)))
    _ = KP U y (prefixCondComplexityContext (pairCode p (natCode nn)) x kx) +
          KPPlain U (pairCode (natCode nn) (natCode kx)) +
          (cCore + cRemove + cEnriched : Nat) := by
          rw [pairConditionEnriched_pairCode, Nat.cast_add, Nat.cast_add]
          abel

/-- **Randomness against a staged condition.**  If `y` is random given `x` up to `epsilon` and
the code `p` has conditional complexity at most `P_cond_x` given `x`, then `y` stays random
given the staged condition `⟨⟨p, nn⟩, ⟨x, kx⟩⟩`, at the extra cost of the advice pair. -/
lemma random_given_stagedCondition (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y p : BitString) (nn kx kP epsilon P_cond_x : Nat),
      HasCondPrefixComplexityValue U p x kP →
      KP U p x ≤ (P_cond_x : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      (y.length : ENat) ≤
        KP U y (prefixCondComplexityContext (pairCode p (natCode nn)) x kx) +
          (epsilon + P_cond_x : Nat) +
          KPPlain U (pairCode (natCode nn) (natCode kx)) + (c : ENat) := by
  obtain ⟨cPlain, hPlain⟩ := condK_le_KP V U hV hU.isPrefixDecompressor
  obtain ⟨cProject, hProject⟩ := KP_map_le U hU decodeSecond decodeSecond_computable
  obtain ⟨cUpper, hUpper⟩ := KPCondPair_chain_upper U hU
  obtain ⟨cChange, hChange⟩ := KP_stagedCondition_change U hU
  refine ⟨cPlain + cProject + cUpper + cChange, ?_⟩
  intro x y p nn kx kP epsilon P_cond_x hkP hPCond hyRandom
  have hProjection : KP U y x ≤ KPCondPair U p y x + (cProject : ENat) := by
    simpa [KPCondPair, decodeSecond_pairCode] using hProject (pairCode p y) x
  calc
    (y.length : ENat) ≤ condK V y x + (epsilon : ENat) := hyRandom
    _ ≤ (KP U y x + (cPlain : ENat)) + (epsilon : ENat) := by
          gcongr
          exact hPlain y x
    _ ≤ ((KPCondPair U p y x + (cProject : ENat)) + (cPlain : ENat)) + (epsilon : ENat) := by
          gcongr
    _ ≤ (((KP U p x + KP U y (prefixCondComplexityContext x p kP) + (cUpper : ENat)) +
          (cProject : ENat)) + (cPlain : ENat)) + (epsilon : ENat) := by
          gcongr
          exact hUpper p y x kP hkP
    _ ≤ ((((P_cond_x : ENat) +
          (KP U y (prefixCondComplexityContext (pairCode p (natCode nn)) x kx) +
            KPPlain U (pairCode (natCode nn) (natCode kx)) + (cChange : ENat)) +
          (cUpper : ENat)) + (cProject : ENat)) + (cPlain : ENat)) + (epsilon : ENat) := by
          gcongr
          exact hChange x p y nn kx kP
    _ = KP U y (prefixCondComplexityContext (pairCode p (natCode nn)) x kx) +
          (epsilon + P_cond_x : Nat) +
          KPPlain U (pairCode (natCode nn) (natCode kx)) +
          (cPlain + cProject + cUpper + cChange : Nat) := by
          simp only [Nat.cast_add]
          simp [add_comm, add_left_comm, add_assoc]

/-- **Size of the advice pair.**  The code of the pair of two numbers has plain prefix
complexity at most twice the sum of their binary lengths, up to a constant. -/
lemma KPPlain_advicePair_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ nn kx : Nat,
      KPPlain U (pairCode (natCode nn) (natCode kx)) ≤
        ((2 * (Nat.bits nn).length + 2 * (Nat.bits kx).length + c : Nat) : ENat) := by
  obtain ⟨cPair, hPair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨cNat, hNat⟩ := KPPlain_natCode_le_log U hU
  refine ⟨2 * cNat + cPair, ?_⟩
  intro nn kx
  calc
    KPPlain U (pairCode (natCode nn) (natCode kx)) = KPPair U (natCode nn) (natCode kx) := rfl
    _ ≤ KPPlain U (natCode nn) + KPPlain U (natCode kx) + (cPair : ENat) :=
        hPair (natCode nn) (natCode kx)
    _ ≤ ((2 * (Nat.bits nn).length + cNat : Nat) : ENat) +
          ((2 * (Nat.bits kx).length + cNat : Nat) : ENat) + (cPair : ENat) :=
        add_le_add (add_le_add (hNat nn) (hNat kx)) le_rfl
    _ = ((2 * (Nat.bits nn).length + 2 * (Nat.bits kx).length + (2 * cNat + cPair) : Nat) :
          ENat) := by
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          ring

/-- **A linear budget for a conditional complexity.**  A plain-complexity budget for `x` bounds
the conditional prefix complexity of `x` given any condition linearly in that budget, and in
particular makes it finite. -/
lemma exists_condPrefixComplexityValue_linear_in_budget (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ b : Nat, ∀ (x w : BitString) (baseBudget : Nat), plainK V x ≤ (baseBudget : ENat) →
      ∃ kx : Nat, HasCondPrefixComplexityValue U x w kx ∧ kx ≤ 3 * baseBudget + b := by
  obtain ⟨cLiteral, hLiteral⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨cCondition, hCondition⟩ := KP_le_KPPlain U hU
  obtain ⟨cPlainBridge, hPlainBridge⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  refine ⟨cLiteral + cPlainBridge + cCondition, ?_⟩
  intro x w baseBudget hxBudget
  have hPlainFinite : plainK V x ≠ ⊤ := condK_ne_top_of_optimal V hV x []
  obtain ⟨kC, hkC⟩ := ENat.ne_top_iff_exists.mp hPlainFinite
  have hkCBound : kC ≤ baseBudget := by
    have hcast : (kC : ENat) ≤ (baseBudget : ENat) := by
      rw [hkC]
      exact hxBudget
    exact_mod_cast hcast
  have hbound :
      KP U x w ≤ ((kC + 2 * (Nat.bits kC).length + cLiteral +
        cPlainBridge + cCondition : Nat) : ENat) := by
    calc
      KP U x w ≤ KPPlain U x + (cCondition : ENat) := hCondition x w
      _ ≤ ((kC : ENat) + KPPlain U (Nat.bits kC) + (cPlainBridge : ENat)) +
            (cCondition : ENat) := by
            gcongr
            exact hPlainBridge x kC hkC.symm
      _ ≤ ((kC : ENat) + (2 * (Nat.bits kC).length + cLiteral : Nat) +
            (cPlainBridge : ENat)) + (cCondition : ENat) := by
            gcongr
            exact hLiteral (Nat.bits kC)
      _ = ((kC + 2 * (Nat.bits kC).length + cLiteral +
            cPlainBridge + cCondition : Nat) : ENat) := by
            push_cast
            ring
  obtain ⟨kx, hkx⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top _) hbound)
  refine ⟨kx, hkx, ?_⟩
  have hkxNat : kx ≤ kC + 2 * (Nat.bits kC).length + cLiteral + cPlainBridge + cCondition := by
    have hcast : (kx : ENat) ≤ ((kC + 2 * (Nat.bits kC).length + cLiteral +
        cPlainBridge + cCondition : Nat) : ENat) := by
      rw [hkx]
      exact hbound
    exact_mod_cast hcast
  have hbits := length_natBits_le kC
  omega

/-- **The bookkeeping behind the pair-condition bound.**  From a decomposition of the two sides
into a conditional part, a staged part and two code sizes, together with a budget covering all
constants, the pair inequality follows. -/
lemma enat_pair_condition_assembly
    (Kxp Kxz Kyz Kpair Knat Kadv : ENat) (m e c₁ c₂ c₃ cn ca cost : Nat)
    (h₁ : Kxp ≤ Kxz + Knat + (c₁ : ENat))
    (h₂ : (m : ENat) ≤ Kyz + (e : ENat) + Kadv + (c₂ : ENat))
    (h₃ : Kxz + Kyz ≤ Kpair + (c₃ : ENat))
    (hn : Knat ≤ (cn : ENat)) (hadv : Kadv ≤ (ca : ENat))
    (hcost : c₁ + c₂ + c₃ + cn + ca ≤ cost) :
    Kxp + (m : ENat) ≤ Kpair + ((e : ENat) + (cost : ENat)) := by
  have hstep : Kxp + (m : ENat) ≤
      (Kxz + Kyz) + ((e : ENat) + ((c₁ : ENat) + (c₂ : ENat) + (cn : ENat) + (ca : ENat))) := by
    calc
      Kxp + (m : ENat) ≤ (Kxz + Knat + (c₁ : ENat)) +
          (Kyz + (e : ENat) + Kadv + (c₂ : ENat)) := add_le_add h₁ h₂
      _ ≤ (Kxz + (cn : ENat) + (c₁ : ENat)) +
          (Kyz + (e : ENat) + (ca : ENat) + (c₂ : ENat)) := by gcongr
      _ = (Kxz + Kyz) +
          ((e : ENat) + ((c₁ : ENat) + (c₂ : ENat) + (cn : ENat) + (ca : ENat))) := by abel
  refine hstep.trans ?_
  calc
    (Kxz + Kyz) + ((e : ENat) + ((c₁ : ENat) + (c₂ : ENat) + (cn : ENat) + (ca : ENat)))
        ≤ (Kpair + (c₃ : ENat)) +
          ((e : ENat) + ((c₁ : ENat) + (c₂ : ENat) + (cn : ENat) + (ca : ENat))) := by gcongr
    _ = Kpair + ((e : ENat) + ((c₁ + c₂ + c₃ + cn + ca : Nat) : ENat)) := by
          push_cast
          abel
    _ ≤ Kpair + ((e : ENat) + (cost : ENat)) := by gcongr

end Kolmogorov
