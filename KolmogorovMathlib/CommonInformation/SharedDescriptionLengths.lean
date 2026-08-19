import KolmogorovMathlib.CommonInformation.Interfaces
import KolmogorovMathlib.CommonInformation.OverlapGeometry
import KolmogorovMathlib.CommonInformation.SharedDescription

/-!
# Common Information: raw shared-description length arithmetic

The quantitative bridge from the `ExtractableCommonInformationWithin` hypotheses
to the raw block-length estimates of `RawSharedDescriptionWithin`.  Everything
here is exact-value plain complexity plus `Nat` arithmetic; no new decoder is
built (the operational content lives in `SharedDescription.lean`).

The single reusable estimate is `extractable_chain_length_close`: with exact
plain values `C(x)`, `C(z)`, `C(x|z)`, both pair values `C(z,x)`, `C(x,z)`, and
`C(z|x) ≤ d`, the raw block length `C(x|z) + C(z)` is within `d + O(log)` of
`C(x)`.  Applied to `x` it gives the left block estimate; applied to `y` it gives
the right block estimate — the statement is symmetric, so one lemma serves both.

Combined with `sharedDescriptionLengths_close` (in `OverlapGeometry.lean`) and
the mutual-information closeness hypothesis, these yield the total-length
estimate `C(x|z) + C(z) + C(y|z) ≈ C(x,y)` needed for the raw witness.
-/

namespace Kolmogorov

/-- Raw block-length estimate for a shared description.  With exact plain values
`C(x) = kx`, `C(z) = kz`, `C(x|z) = kxz`, the two pair values
`C(pairCode z x) = kzxPair`, `C(pairCode x z) = kxzPair`, and `C(z|x) = kzx ≤ d`
(the extractability hypothesis that `z` is `d`-simple given `x`), the block
length `C(x|z) + C(z)` is within `d + O(log)` of `C(x)`.  The two logarithmic
terms are in the actual pair complexities, so the estimate composes without any
circular self-reference.

Applying this with `x := y` gives the symmetric right-block estimate; there is no
separate `_right` lemma. -/
theorem extractable_chain_length_close (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x z : BitString) (kx kz kxz kzx kzxPair kxzPair d : Nat),
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V x z kxz →
      HasPlainConditionalComplexityValue V z x kzx →
      HasPlainComplexityValue V (pairCode z x) kzxPair →
      HasPlainComplexityValue V (pairCode x z) kxzPair →
      kzx ≤ d →
      NatCloseWithin (kxz + kz) kx
        (d + logSlack c (kzxPair + 1) + logSlack c (kxzPair + 1)) := by
  obtain ⟨cUpper, hUpper⟩ := pairPlainK_chain_upper_values V hV
  obtain ⟨cLower, hLower⟩ := pairPlainK_chain_lower_values V hV
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le V hV
  obtain ⟨cSwap, hSwap⟩ := pairPlainK_swap_le V hV
  refine ⟨cUpper + cLower + cRight + cSwap,
    fun x z kx kz kxz kzx kzxPair kxzPair d hx hz hxz hzx hzxPair hxzPair hd => ?_⟩
  set C := cUpper + cLower + cRight + cSwap with hCdef
  -- Symmetry of information on the two pair orderings.
  have h1 : kz + kxz ≤ kzxPair + logSlack cLower (kzxPair + 1) :=
    hLower z x kz kxz kzxPair hz hxz hzxPair
  have h5 : kzxPair ≤ kz + kxz + logSlack cUpper (kzxPair + 1) :=
    hUpper z x kz kxz kzxPair hz hxz hzxPair
  have h2 : kxzPair ≤ kx + kzx + logSlack cUpper (kxzPair + 1) :=
    hUpper x z kx kzx kxzPair hx hzx hxzPair
  -- The two pair orderings are close; `C(x)` projects out of the pair.
  have h3 : kzxPair ≤ kxzPair + cSwap := by
    have h := hSwap x z
    rw [pairPlainK, pairPlainK, hzxPair, hxzPair] at h
    exact_mod_cast h
  have h4 : kx ≤ kzxPair + cRight := by
    have h := hRight z x
    rw [pairPlainK, hx, hzxPair] at h
    exact_mod_cast h
  -- Fold the auxiliary constants into the two visible log-slack budgets.
  have hLzx : logSlack cLower (kzxPair + 1) + cSwap ≤ logSlack C (kzxPair + 1) :=
    (logSlack_add_nat_le cLower cSwap (kzxPair + 1)).trans
      (logSlack_mono_left (by omega) (kzxPair + 1))
  have hLzx' : logSlack cUpper (kzxPair + 1) + cRight ≤ logSlack C (kzxPair + 1) :=
    (logSlack_add_nat_le cUpper cRight (kzxPair + 1)).trans
      (logSlack_mono_left (by omega) (kzxPair + 1))
  have hLxz : logSlack cUpper (kxzPair + 1) ≤ logSlack C (kxzPair + 1) :=
    logSlack_mono_left (by omega) (kxzPair + 1)
  refine ⟨?_, ?_⟩
  · -- kxz + kz ≤ kx + (d + logSlack C (kzxPair+1) + logSlack C (kxzPair+1))
    omega
  · -- kx ≤ kxz + kz + (d + logSlack C (kzxPair+1) + logSlack C (kxzPair+1))
    omega

/-- Visible-parameter form of `extractable_chain_length_close`.  The auxiliary
pair complexities in that theorem are bounded by explicit plain two-stage
programs, so both logarithms can be folded into a single
`O(d + log (C(x) + C(z)))` budget. -/
theorem extractable_chain_length_close_visible
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ (x z : BitString) (kx kz kxz kzx d : Nat),
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V x z kxz →
      HasPlainConditionalComplexityValue V z x kzx →
      kzx ≤ d →
      NatCloseWithin (kxz + kz) kx
        (commonInformationSlack C d (kx + kz + 1)) := by
  obtain ⟨cRaw, hRaw⟩ := extractable_chain_length_close V hV
  obtain ⟨cCrude, hCrude⟩ := pairPlainK_twoStage_crude_values V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  let b := cCond + cCrude
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cRaw 3 b
  let cLogs := cFold + cFold
  let C := cLogs + cLogs + 1
  refine ⟨C, fun x z kx kz kxz kzx d hx hz hxz hzx hd => ?_⟩
  obtain ⟨kzxPair, hzxPair, hzxPairBound⟩ :=
    hCrude z x kz kxz hz hxz
  obtain ⟨kxzPair, hxzPair, hxzPairBound⟩ :=
    hCrude x z kx kzx hx hzx
  have hkxzBound : kxz ≤ kx + cCond := by
    have h := hCond x z
    rw [hxz, hx] at h
    exact_mod_cast h
  have hzxPairLinear :
      kzxPair + 1 ≤ 3 * (kx + kz + d + 1) + b := by
    dsimp [b]
    omega
  have hxzPairLinear :
      kxzPair + 1 ≤ 3 * (kx + kz + d + 1) + b := by
    dsimp [b]
    omega
  have hzxLog :
      logSlack cRaw (kzxPair + 1) ≤
        logSlack cFold (kx + kz + d + 1) :=
    (logSlack_mono_right cRaw hzxPairLinear).trans
      (hFold (kx + kz + d + 1))
  have hxzLog :
      logSlack cRaw (kxzPair + 1) ≤
        logSlack cFold (kx + kz + d + 1) :=
    (logSlack_mono_right cRaw hxzPairLinear).trans
      (hFold (kx + kz + d + 1))
  have hRawClose :
      NatCloseWithin (kxz + kz) kx
        (d + logSlack cRaw (kzxPair + 1) +
          logSlack cRaw (kxzPair + 1)) :=
    hRaw x z kx kz kxz kzx kzxPair kxzPair d
      hx hz hxz hzx hzxPair hxzPair hd
  have hLogs :
      logSlack cRaw (kzxPair + 1) +
          logSlack cRaw (kxzPair + 1) ≤
        logSlack cLogs (kx + kz + d + 1) := by
    calc
      logSlack cRaw (kzxPair + 1) +
          logSlack cRaw (kxzPair + 1)
          ≤ logSlack cFold (kx + kz + d + 1) +
              logSlack cFold (kx + kz + d + 1) :=
        Nat.add_le_add hzxLog hxzLog
      _ = logSlack cLogs (kx + kz + d + 1) := by
        dsimp [cLogs]
        exact logSlack_add_const _ _ _
  have hVisibleLog :
      logSlack cLogs (kx + kz + d + 1) ≤
        logSlack cLogs (kx + kz + 1) +
          cLogs * d + cLogs := by
    calc
      logSlack cLogs (kx + kz + d + 1)
          = logSlack cLogs ((kx + kz + 1) + d) := by
            congr 1
            omega
      _ ≤ logSlack cLogs (kx + kz + 1) + logSlack cLogs d :=
        logSlack_add_le cLogs (kx + kz + 1) d
      _ ≤ logSlack cLogs (kx + kz + 1) +
            cLogs * d + cLogs := by
        unfold logSlack
        have := length_natBits_le d
        nlinarith
  have hLogConst :
      logSlack cLogs (kx + kz + 1) + cLogs ≤
        logSlack C (kx + kz + 1) := by
    calc
      logSlack cLogs (kx + kz + 1) + cLogs
          ≤ logSlack (cLogs + cLogs) (kx + kz + 1) :=
        logSlack_add_nat_le cLogs cLogs (kx + kz + 1)
      _ ≤ logSlack C (kx + kz + 1) := by
        apply logSlack_mono_left
        dsimp [C]
        omega
  have hLinear :
      (1 + cLogs) * d ≤ C * d := by
    apply Nat.mul_le_mul_right
    dsimp [C]
    omega
  have hBudget :
      d + logSlack cRaw (kzxPair + 1) +
          logSlack cRaw (kxzPair + 1) ≤
        commonInformationSlack C d (kx + kz + 1) := by
    unfold commonInformationSlack
    calc
      d + logSlack cRaw (kzxPair + 1) +
          logSlack cRaw (kxzPair + 1)
          = d + (logSlack cRaw (kzxPair + 1) +
              logSlack cRaw (kxzPair + 1)) := by omega
      _ ≤ d + logSlack cLogs (kx + kz + d + 1) :=
        Nat.add_le_add_left hLogs d
      _ ≤ d + (logSlack cLogs (kx + kz + 1) +
            cLogs * d + cLogs) :=
        Nat.add_le_add_left hVisibleLog d
      _ = (1 + cLogs) * d +
            (logSlack cLogs (kx + kz + 1) + cLogs) := by
        ring
      _ ≤ C * d + logSlack C (kx + kz + 1) :=
        Nat.add_le_add hLinear hLogConst
  exact hRawClose.mono hBudget

/-- Assemble one literal raw shared description from an extractable common
string.  The witnesses are genuine shortest plain programs: one program `p`
for `z`, one program `a` for `x` conditional on `z`, and one program `b` for
`y` conditional on `z`.  In particular, the exact same syntactic `p` occurs in
both represented blocks; no equivalence or incompressibility conclusion is
assumed by the raw predicate. -/
theorem exists_rawSharedDescription_of_extractableCommonInformation
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ (x y z : BitString) (kx ky kxy m d : Nat),
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V y ky →
      HasPlainComplexityValue V (pairCode x y) kxy →
      MutualInformationWithin V x y m d →
      ExtractableCommonInformationWithin V x y z m d →
      ∃ a p b,
        RawSharedDescriptionWithin V x y z a p b
          kx ky kxy m
          (commonInformationSlack C d (kxy + 1)) := by
  obtain ⟨cChain, hChain⟩ :=
    extractable_chain_length_close_visible V hV
  obtain ⟨cLeft, hLeft⟩ := pairPlainK_left_le V hV
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le V hV
  let bVisible := 2 * (cLeft + cRight)
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cChain 3 bVisible
  let cBase := cChain + 2 * cFold
  let C := 2 * cBase + 2
  refine ⟨C, fun x y z kx ky kxy m d hx hy hxy hI hExtract => ?_⟩
  obtain ⟨kz, hz⟩ := exists_plainComplexityValue V hV z
  obtain ⟨kxz, hxz⟩ :=
    exists_plainConditionalComplexityValue V hV x z
  obtain ⟨kyz, hyz⟩ :=
    exists_plainConditionalComplexityValue V hV y z
  obtain ⟨kzx, hzx⟩ :=
    exists_plainConditionalComplexityValue V hV z x
  obtain ⟨kzy, hzy⟩ :=
    exists_plainConditionalComplexityValue V hV z y
  have hkzxLe : kzx ≤ d := by
    have h := hExtract.1
    rw [hzx] at h
    exact_mod_cast h
  have hkzyLe : kzy ≤ d := by
    have h := hExtract.2.1
    rw [hzy] at h
    exact_mod_cast h
  have hkzUpper : kz ≤ m + d := by
    have h := hExtract.2.2.1
    rw [hz] at h
    exact_mod_cast h
  have hkzLower : m ≤ kz + d := by
    have h := hExtract.2.2.2
    rw [hz] at h
    exact_mod_cast h
  have hzClose : NatCloseWithin kz m d :=
    ⟨hkzUpper, hkzLower⟩
  have hIClose : NatCloseWithin (kxy + m) (kx + ky) d := by
    unfold MutualInformationWithin at hI
    constructor
    · have h := hI.1
      rw [pairPlainK, hxy, hx, hy] at h
      exact_mod_cast h
    · have h := hI.2
      rw [pairPlainK, hxy, hx, hy] at h
      exact_mod_cast h
  have hkxVisible : kx ≤ kxy + cLeft := by
    have h := hLeft x y
    rw [pairPlainK, hx, hxy] at h
    exact_mod_cast h
  have hkyVisible : ky ≤ kxy + cRight := by
    have h := hRight x y
    rw [pairPlainK, hy, hxy] at h
    exact_mod_cast h
  have hmVisible : m ≤ kxy + cLeft + cRight + d := by
    unfold NatCloseWithin at hIClose
    omega
  have hkzVisible : kz ≤ kxy + cLeft + cRight + 2 * d := by
    omega
  have hxArg :
      kx + kz + 1 ≤
        3 * (kxy + d + 1) + bVisible := by
    dsimp [bVisible]
    omega
  have hyArg :
      ky + kz + 1 ≤
        3 * (kxy + d + 1) + bVisible := by
    dsimp [bVisible]
    omega
  have hxCloseRaw :
      NatCloseWithin (kxz + kz) kx
        (commonInformationSlack cChain d (kx + kz + 1)) :=
    hChain x z kx kz kxz kzx d hx hz hxz hzx hkzxLe
  have hyCloseRaw :
      NatCloseWithin (kyz + kz) ky
        (commonInformationSlack cChain d (ky + kz + 1)) :=
    hChain y z ky kz kyz kzy d hy hz hyz hzy hkzyLe
  have hVisibleLog :
      logSlack cFold (kxy + d + 1) ≤
        logSlack cFold (kxy + 1) + cFold * d + cFold := by
    calc
      logSlack cFold (kxy + d + 1)
          = logSlack cFold ((kxy + 1) + d) := by
            congr 1
            omega
      _ ≤ logSlack cFold (kxy + 1) + logSlack cFold d :=
        logSlack_add_le cFold (kxy + 1) d
      _ ≤ logSlack cFold (kxy + 1) + cFold * d + cFold := by
        unfold logSlack
        have := length_natBits_le d
        nlinarith
  have hBaseLog :
      logSlack cFold (kxy + 1) + cFold ≤
        logSlack cBase (kxy + 1) := by
    calc
      logSlack cFold (kxy + 1) + cFold
          ≤ logSlack (cFold + cFold) (kxy + 1) :=
        logSlack_add_nat_le cFold cFold (kxy + 1)
      _ ≤ logSlack cBase (kxy + 1) := by
        apply logSlack_mono_left
        dsimp [cBase]
        omega
  have hBaseLinear :
      (cChain + cFold) * d ≤ cBase * d := by
    apply Nat.mul_le_mul_right
    dsimp [cBase]
    omega
  have hChainBudget :
      ∀ {arg : Nat},
        arg ≤ 3 * (kxy + d + 1) + bVisible →
        commonInformationSlack cChain d arg ≤
          commonInformationSlack cBase d (kxy + 1) := by
    intro arg harg
    unfold commonInformationSlack
    calc
      cChain * d + logSlack cChain arg
          ≤ cChain * d +
              logSlack cChain
                (3 * (kxy + d + 1) + bVisible) :=
        Nat.add_le_add_left (logSlack_mono_right cChain harg) _
      _ ≤ cChain * d + logSlack cFold (kxy + d + 1) :=
        Nat.add_le_add_left (hFold (kxy + d + 1)) _
      _ ≤ cChain * d +
            (logSlack cFold (kxy + 1) + cFold * d + cFold) :=
        Nat.add_le_add_left hVisibleLog _
      _ = (cChain + cFold) * d +
            (logSlack cFold (kxy + 1) + cFold) := by
        ring
      _ ≤ cBase * d + logSlack cBase (kxy + 1) :=
        Nat.add_le_add hBaseLinear hBaseLog
  let e := commonInformationSlack cBase d (kxy + 1)
  have hxClose : NatCloseWithin (kxz + kz) kx e :=
    hxCloseRaw.mono (hChainBudget hxArg)
  have hyClose : NatCloseWithin (kz + kyz) ky e := by
    have h := hyCloseRaw.mono (hChainBudget hyArg)
    simpa [add_comm] using h
  have hTotalClose :
      NatCloseWithin (kxz + kz + kyz) kxy (2 * e + 2 * d) :=
    sharedDescriptionLengths_close hxClose hyClose hzClose hIClose
  have hFinalLog :
      2 * logSlack cBase (kxy + 1) ≤
        logSlack C (kxy + 1) := by
    calc
      2 * logSlack cBase (kxy + 1)
          = logSlack cBase (kxy + 1) +
              logSlack cBase (kxy + 1) := by ring
      _ = logSlack (cBase + cBase) (kxy + 1) :=
        logSlack_add_const _ _ _
      _ ≤ logSlack C (kxy + 1) := by
        apply logSlack_mono_left
        dsimp [C]
        omega
  have hFinalBudget :
      2 * e + 2 * d ≤ commonInformationSlack C d (kxy + 1) := by
    dsimp [e]
    unfold commonInformationSlack
    calc
      2 * (cBase * d + logSlack cBase (kxy + 1)) + 2 * d
          = (2 * cBase + 2) * d +
              2 * logSlack cBase (kxy + 1) := by
        ring
      _ ≤ C * d + logSlack C (kxy + 1) := by
        apply Nat.add_le_add
        · dsimp [C]
          exact le_rfl
        · exact hFinalLog
  have heFinal :
      e ≤ commonInformationSlack C d (kxy + 1) :=
    (by omega : e ≤ 2 * e + 2 * d).trans hFinalBudget
  have hdFinal :
      d ≤ commonInformationSlack C d (kxy + 1) :=
    (by omega : d ≤ 2 * e + 2 * d).trans hFinalBudget
  obtain ⟨p, hp, hpLen⟩ := hz.exists_program
  obtain ⟨a, ha, haLen⟩ := hxz.exists_program
  obtain ⟨b, hb, hbLen⟩ := hyz.exists_program
  refine ⟨a, p, b, hp, ha, hb, ?_, ?_, ?_, ?_⟩
  · simpa [hpLen] using hzClose.mono hdFinal
  · simpa [haLen, hpLen] using hxClose.mono heFinal
  · simpa [hpLen, hbLen] using hyClose.mono heFinal
  · simpa [haLen, hpLen, hbLen] using hTotalClose.mono hFinalBudget


/-! ### Budget-folding arithmetic for the normalization step -/

/-- The common-information slack is monotone in its visible-parameter argument. -/
lemma commonInformationSlack_mono_right {c d n n' : Nat} (h : n ≤ n') :
    commonInformationSlack c d n ≤ commonInformationSlack c d n' := by
  unfold commonInformationSlack
  exact Nat.add_le_add_left (logSlack_mono_right c h) _

/-- Fold a decoder budget `commonInformationSlack c (3*d) arg` (with a
linearly-bounded argument) into a single `commonInformationSlack C d N`.  This is
the arithmetic used to absorb the resized-decoder slacks, whose closeness error
is `3*d` and whose visible parameters are `O(kxy + d)`. -/
lemma commonInformationSlack_threeD_fold (c : Nat) :
    ∃ C, ∀ d N arg, arg ≤ 3 * (N + d) →
      commonInformationSlack c (3 * d) arg ≤ commonInformationSlack C d N := by
  obtain ⟨cF, hF⟩ := logSlack_linear_bound c 3 0
  refine ⟨3 * c + 2 * cF, fun d N arg harg => ?_⟩
  have hlog1 : logSlack c arg ≤ logSlack cF (N + d) := by
    calc logSlack c arg ≤ logSlack c (3 * (N + d)) := logSlack_mono_right c harg
      _ = logSlack c (3 * (N + d) + 0) := by rw [Nat.add_zero]
      _ ≤ logSlack cF (N + d) := hF (N + d)
  have hlog2 : logSlack cF (N + d) ≤ logSlack cF N + logSlack cF d :=
    logSlack_add_le cF N d
  have hlog3 : logSlack cF d ≤ cF * d + cF := by
    unfold logSlack
    have := length_natBits_le d
    nlinarith
  have hlogFold : logSlack cF N + cF ≤ logSlack (3 * c + 2 * cF) N :=
    (logSlack_add_nat_le cF cF N).trans (logSlack_mono_left (by omega) N)
  have hlin : (3 * c + cF) * d ≤ (3 * c + 2 * cF) * d :=
    Nat.mul_le_mul_right d (by omega)
  unfold commonInformationSlack
  calc c * (3 * d) + logSlack c arg
      ≤ c * (3 * d) + (logSlack cF N + logSlack cF d) :=
        Nat.add_le_add_left (hlog1.trans hlog2) _
    _ ≤ c * (3 * d) + (logSlack cF N + (cF * d + cF)) :=
        Nat.add_le_add_left (Nat.add_le_add_left hlog3 _) _
    _ = (3 * c + cF) * d + (logSlack cF N + cF) := by ring
    _ ≤ (3 * c + 2 * cF) * d + logSlack (3 * c + 2 * cF) N :=
        Nat.add_le_add hlin hlogFold

/-- Combine two decoder budgets and a logarithmic index cost into a single
budget.  This absorbs the `2*a + b + O(log)` produced by the visible-budget pair
decoder. -/
lemma commonInformationSlack_pairCombine_fold (cx cy cpair : Nat) :
    ∃ C, 2 ≤ C ∧ ∀ d N,
      2 * commonInformationSlack cx d N + commonInformationSlack cy d N
          + logSlack cpair N ≤ commonInformationSlack C d N := by
  refine ⟨2 * cx + cy + cpair + 2, by omega, fun d N => ?_⟩
  have hlogsum : 2 * logSlack cx N + logSlack cy N + logSlack cpair N
      = logSlack (2 * cx + cy + cpair) N := by unfold logSlack; ring
  have e4 : logSlack (2 * cx + cy + cpair) N
      ≤ logSlack (2 * cx + cy + cpair + 2) N :=
    logSlack_mono_left (by omega) N
  have e5 : (2 * cx + cy) * d ≤ (2 * cx + cy + cpair + 2) * d :=
    Nat.mul_le_mul_right d (by omega)
  unfold commonInformationSlack
  calc 2 * (cx * d + logSlack cx N) + (cy * d + logSlack cy N) + logSlack cpair N
      = (2 * cx + cy) * d
          + (2 * logSlack cx N + logSlack cy N + logSlack cpair N) := by ring
    _ = (2 * cx + cy) * d + logSlack (2 * cx + cy + cpair) N := by rw [hlogsum]
    _ ≤ (2 * cx + cy + cpair + 2) * d + logSlack (2 * cx + cy + cpair + 2) N :=
        Nat.add_le_add e5 e4

/-- Fold a nested slack `commonInformationSlack cNL (commonInformationSlack cP d N) (N + e)`
into one `commonInformationSlack C d N`.  This is the arithmetic used to absorb
the `nearLength` budget (whose closeness error is itself a decoder slack) at the
three represented blocks, whose complexity values differ from `kxy` by the
constants `e`. -/
lemma commonInformationSlack_nested_fold (cNL cP e : Nat) :
    ∃ C, 2 ≤ C ∧ ∀ d N,
      commonInformationSlack cNL (commonInformationSlack cP d N) (N + e) ≤
        commonInformationSlack C d N := by
  refine ⟨cNL * cP + cNL + logSlack cNL e + 2, by omega, fun d N => ?_⟩
  have e1 : cNL * logSlack cP N = logSlack (cNL * cP) N := by unfold logSlack; ring
  have e2 : logSlack cNL (N + e) ≤ logSlack cNL N + logSlack cNL e :=
    logSlack_add_le cNL N e
  have e3 : logSlack (cNL * cP) N + logSlack cNL N = logSlack (cNL * cP + cNL) N :=
    logSlack_add_const (cNL * cP) cNL N
  have e4 : logSlack (cNL * cP + cNL) N + logSlack cNL e
      ≤ logSlack (cNL * cP + cNL + logSlack cNL e) N :=
    logSlack_add_nat_le (cNL * cP + cNL) (logSlack cNL e) N
  have e5 : logSlack (cNL * cP + cNL + logSlack cNL e) N
      ≤ logSlack (cNL * cP + cNL + logSlack cNL e + 2) N :=
    logSlack_mono_left (by omega) N
  have e6 : cNL * cP * d ≤ (cNL * cP + cNL + logSlack cNL e + 2) * d :=
    Nat.mul_le_mul_right d (by omega)
  unfold commonInformationSlack
  calc cNL * (cP * d + logSlack cP N) + logSlack cNL (N + e)
      = cNL * cP * d + (cNL * logSlack cP N + logSlack cNL (N + e)) := by ring
    _ ≤ cNL * cP * d + (logSlack (cNL * cP) N + (logSlack cNL N + logSlack cNL e)) := by
        rw [e1]; exact Nat.add_le_add_left (Nat.add_le_add_left e2 _) _
    _ = cNL * cP * d + ((logSlack (cNL * cP) N + logSlack cNL N) + logSlack cNL e) := by
        ring
    _ = cNL * cP * d + (logSlack (cNL * cP + cNL) N + logSlack cNL e) := by rw [e3]
    _ ≤ cNL * cP * d + logSlack (cNL * cP + cNL + logSlack cNL e) N :=
        Nat.add_le_add_left e4 _
    _ ≤ (cNL * cP + cNL + logSlack cNL e + 2) * d
          + logSlack (cNL * cP + cNL + logSlack cNL e + 2) N :=
        Nat.add_le_add e6 e5

theorem normalize_rawSharedBlockRepresentation
    (V : Map) (hV : isOptimalConditional V) :
  ∃ C, ∀ x y z a p b kx ky kxy m d,
    HasPlainComplexityValue V x kx →
    HasPlainComplexityValue V y ky →
    HasPlainComplexityValue V (pairCode x y) kxy →
    MutualInformationWithin V x y m d →
    RawSharedDescriptionWithin V x y z a p b kx ky kxy m d →
    ∃ u, OverlapRepresentationWithin V x y u kx ky kxy
      (commonInformationSlack C d (kxy + 1)) := by
  obtain ⟨CRev, hRev⟩ := condK_output_given_resized_reverseConcat_le V hV
  obtain ⟨CFwd, hFwd⟩ := condK_output_given_resized_forwardConcat_le V hV
  obtain ⟨CPair, hPairDec⟩ := condK_pair_from_prefix_suffix_visible_le V hV
  obtain ⟨cNL, hNL⟩ := nearLength_decodable_is_equivalent_incompressible V hV
  obtain ⟨cLeft, hLeftC⟩ := pairPlainK_left_le V hV
  obtain ⟨cRight, hRightC⟩ := pairPlainK_right_le V hV
  obtain ⟨Cx, hDecFoldX⟩ := commonInformationSlack_threeD_fold CRev
  obtain ⟨Cy, hDecFoldY⟩ := commonInformationSlack_threeD_fold CFwd
  obtain ⟨cP, hcP2, hPairCombine⟩ := commonInformationSlack_pairCombine_fold Cx Cy CPair
  obtain ⟨Cfinal, hCfinal2, hNestFold⟩ :=
    commonInformationSlack_nested_fold cNL cP (cLeft + cRight)
  refine ⟨Cfinal, fun x y z a p b kx ky kxy m d hx hy hxy hI hRaw => ?_⟩
  obtain ⟨hp, ha, hb, hpm, haxp, hpby, htotal⟩ := hRaw
  -- Geometry of the normalized string.
  obtain ⟨hCompA, hCompP, hCompB⟩ :=
    normalizedSharedComponentLengths_close haxp hpby htotal
  obtain ⟨hTgtLx, hTgtLy, hArgX, hArgY⟩ :=
    normalizedSharedTargetLengths_close haxp hpby htotal
  obtain ⟨hSum, hLeftShared, hSharedRight⟩ :=
    normalized_overlap_gap_lengths kx ky kxy
  obtain ⟨hULen, hUTake, hUDrop⟩ :=
    normalizedSharedDescription_shape a p b kx ky kxy
  set lx := min kx kxy with hlxdef
  set ly := min ky kxy with hlydef
  set shared := lx + ly - kxy with hshareddef
  set gap := kxy - (lx + ly) with hgapdef
  set left := lx - shared with hleftdef
  set right := ly - shared with hrightdef
  set u := resizeToLength a left ++ resizeToLength p shared ++
    List.replicate gap false ++ resizeToLength b right with hudef
  -- Elementary length facts.
  have hlxKxy : lx ≤ kxy := by rw [hlxdef]; exact Nat.min_le_right kx kxy
  have hlyKxy : ly ≤ kxy := by rw [hlydef]; exact Nat.min_le_right ky kxy
  have hlxU : lx ≤ u.length := by rw [hULen]; exact hlxKxy
  have hlyU : ly ≤ u.length := by rw [hULen]; exact hlyKxy
  have hTakeLen : (u.take lx).length = lx := by
    rw [List.length_take, hULen, Nat.min_eq_left hlxKxy]
  have hDropLen : (u.drop (u.length - ly)).length = ly := by
    rw [List.length_drop, hULen]; omega
  -- Complexity offsets of the endpoints relative to the pair.
  have hkxKxy : kx ≤ kxy + cLeft := by
    have h := hLeftC x y
    rw [hx, pairPlainK, hxy] at h
    exact_mod_cast h
  have hkyKxy : ky ≤ kxy + cRight := by
    have h := hRightC x y
    rw [hy, pairPlainK, hxy] at h
    exact_mod_cast h
  -- Positivity of the decoder budget and target budget.
  have h2dDbig : 2 * d ≤ commonInformationSlack cP d (kxy + 1) := by
    unfold commonInformationSlack
    have := Nat.mul_le_mul_right d hcP2
    omega
  have h2dDtarget : 2 * d ≤ commonInformationSlack Cfinal d (kxy + 1) := by
    unfold commonInformationSlack
    have := Nat.mul_le_mul_right d hCfinal2
    omega
  have hAxDbig :
      commonInformationSlack Cx d (kxy + 1) ≤ commonInformationSlack cP d (kxy + 1) := by
    have h := hPairCombine d (kxy + 1); omega
  have hAyDbig :
      commonInformationSlack Cy d (kxy + 1) ≤ commonInformationSlack cP d (kxy + 1) := by
    have h := hPairCombine d (kxy + 1); omega
  -- The three decoder bounds, folded to the uniform decoder budget.
  have hAA : condK V x (u.take lx) ≤ (commonInformationSlack Cx d (kxy + 1) : ENat) := by
    have h := hRev a p z x left shared (3 * d) hp ha hCompA hCompP
    rw [← hUTake] at h
    refine h.trans ?_
    exact_mod_cast hDecFoldX d (kxy + 1) _ (by omega)
  have hBB : condK V y (u.drop (u.length - ly)) ≤
      (commonInformationSlack Cy d (kxy + 1) : ENat) := by
    have h := hFwd p b z y shared right (3 * d) hp hb hCompP hCompB
    rw [← hUDrop] at h
    refine h.trans ?_
    exact_mod_cast hDecFoldY d (kxy + 1) _ (by omega)
  have hPP : condK V (pairCode x y) u ≤
      (commonInformationSlack cP d (kxy + 1) : ENat) := by
    have h := hPairDec u x y lx ly (commonInformationSlack Cx d (kxy + 1))
      (commonInformationSlack Cy d (kxy + 1)) hlxU hlyU hAA hBB
    rw [hULen] at h
    refine h.trans ?_
    exact_mod_cast hPairCombine d (kxy + 1)
  -- The three near-length applications.
  have hAA' : condK V x (u.take lx) ≤ (commonInformationSlack cP d (kxy + 1) : ENat) :=
    hAA.trans (by exact_mod_cast hAxDbig)
  have hBB' : condK V y (u.drop (u.length - ly)) ≤
      (commonInformationSlack cP d (kxy + 1) : ENat) :=
    hBB.trans (by exact_mod_cast hAyDbig)
  have hCloseTakeX :
      NatCloseWithin (u.take lx).length kx (commonInformationSlack cP d (kxy + 1)) := by
    rw [hTakeLen]; exact hTgtLx.mono h2dDbig
  have hCloseDropY :
      NatCloseWithin (u.drop (u.length - ly)).length ky
        (commonInformationSlack cP d (kxy + 1)) := by
    rw [hDropLen]; exact hTgtLy.mono h2dDbig
  have hClosePairU :
      NatCloseWithin u.length kxy (commonInformationSlack cP d (kxy + 1)) := by
    rw [hULen]; exact ⟨Nat.le_add_right kxy _, Nat.le_add_right kxy _⟩
  obtain ⟨hEqX, _⟩ :=
    hNL x (u.take lx) kx (commonInformationSlack cP d (kxy + 1)) hx hCloseTakeX hAA'
  obtain ⟨hEqY, _⟩ :=
    hNL y (u.drop (u.length - ly)) ky (commonInformationSlack cP d (kxy + 1)) hy
      hCloseDropY hBB'
  obtain ⟨hEqPair, hIncU⟩ :=
    hNL (pairCode x y) u kxy (commonInformationSlack cP d (kxy + 1)) hxy hClosePairU hPP
  -- Fold every near-length budget to the final target.
  have hFoldTo : ∀ k, k ≤ (kxy + 1) + (cLeft + cRight) →
      commonInformationSlack cNL (commonInformationSlack cP d (kxy + 1)) k ≤
        commonInformationSlack Cfinal d (kxy + 1) := fun k hk =>
    (commonInformationSlack_mono_right hk).trans (hNestFold d (kxy + 1))
  exact ⟨u, lx, ly, hULen, hlxU, hlyU,
    hTgtLx.mono h2dDtarget, hTgtLy.mono h2dDtarget,
    hEqX.mono (hFoldTo (kx + 1) (by omega)),
    hEqY.mono (hFoldTo (ky + 1) (by omega)),
    hEqPair.mono (hFoldTo (kxy + 1) (by omega)),
    hIncU.mono (hFoldTo (kxy + 1) (by omega))⟩

theorem exists_overlapRepresentation_of_extractableCommonInformation
    (V : Map) (hV : isOptimalConditional V) :
  ∃ C, ∀ x y z kx ky kxy m d,
    HasPlainComplexityValue V x kx →
    HasPlainComplexityValue V y ky →
    HasPlainComplexityValue V (pairCode x y) kxy →
    MutualInformationWithin V x y m d →
    ExtractableCommonInformationWithin V x y z m d →
    ∃ u, OverlapRepresentationWithin V x y u kx ky kxy
      (commonInformationSlack C d (kxy + 1)) := by
  obtain ⟨cRaw, hRaw⟩ :=
    exists_rawSharedDescription_of_extractableCommonInformation V hV
  obtain ⟨cNorm, hNorm⟩ :=
    normalize_rawSharedBlockRepresentation V hV
  let cRaw' := cRaw + 1
  obtain ⟨C, hComp⟩ :=
    commonInformationSlack_comp cNorm cRaw'
  refine ⟨C, fun x y z kx ky kxy m d hx hy hxy hI hExtract => ?_⟩
  let dRaw := commonInformationSlack cRaw' d (kxy + 1)
  have hdRaw : d ≤ dRaw := by
    dsimp [dRaw, cRaw']
    unfold commonInformationSlack
    nlinarith
  have hRawMono :
      commonInformationSlack cRaw d (kxy + 1) ≤ dRaw := by
    dsimp [dRaw, cRaw']
    exact commonInformationSlack_mono_left (by omega)
  obtain ⟨a, p, b, hDesc⟩ :=
    hRaw x y z kx ky kxy m d hx hy hxy hI hExtract
  have hDesc' :
      RawSharedDescriptionWithin V x y z a p b
        kx ky kxy m dRaw :=
    hDesc.mono hRawMono
  obtain ⟨u, hu⟩ :=
    hNorm x y z a p b kx ky kxy m dRaw
      hx hy hxy (hI.mono hdRaw) hDesc'
  refine ⟨u, hu.mono ?_⟩
  exact hComp d (kxy + 1)

theorem exists_overlapRepresentation_of_extractableCommonInformation_log
    (V : Map) (hV : isOptimalConditional V) (a : Nat) :
  ∃ C, ∀ x y z kx ky kxy m,
    HasPlainComplexityValue V x kx →
    HasPlainComplexityValue V y ky →
    HasPlainComplexityValue V (pairCode x y) kxy →
    MutualInformationWithin V x y m (logSlack a (kxy + 1)) →
    ExtractableCommonInformationWithin V x y z m (logSlack a (kxy + 1)) →
    ∃ u, OverlapRepresentationWithin V x y u kx ky kxy
      (logSlack C (kxy + 1)) := by
  obtain ⟨c, hc⟩ :=
    exists_overlapRepresentation_of_extractableCommonInformation V hV
  refine ⟨c * (a + 1), fun x y z kx ky kxy m hx hy hxy hI hExtract => ?_⟩
  obtain ⟨u, hu⟩ :=
    hc x y z kx ky kxy m (logSlack a (kxy + 1))
      hx hy hxy hI hExtract
  refine ⟨u, hu.mono ?_⟩
  unfold commonInformationSlack logSlack
  ring_nf
  exact le_rfl

end Kolmogorov
