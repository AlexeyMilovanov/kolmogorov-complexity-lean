import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

namespace Kolmogorov

/-- Run a plain conditional decompressor only on programs whose length is
encoded in the second component of the condition. -/
def conditionalProgramLengthContextDecompressor (V : Map) : Map := fun pr =>
  bif (pr.1.length == decodeBits (decodeSecond pr.2)) then
    V (pr.1, decodeFirst pr.2)
  else
    Part.none

lemma conditionalProgramLengthContextDecompressor_isDecompressor
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (conditionalProgramLengthContextDecompressor V) := by
  have hLen : Computable (fun pr : BitString × BitString => pr.1.length) :=
    Computable.list_length.comp Computable.fst
  have hDecodedLen :
      Computable
        (fun pr : BitString × BitString =>
          decodeBits (decodeSecond pr.2)) :=
    decodeBitsComputable.comp
      (decodeSecond_computable.comp Computable.snd)
  have hGuard :
      Computable
        (fun pr : BitString × BitString =>
          (pr.1.length == decodeBits (decodeSecond pr.2))) :=
    (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp
      (hLen.pair hDecodedLen)
  have hCall :
      Partrec
        (fun pr : BitString × BitString =>
          V (pr.1, decodeFirst pr.2)) :=
    Partrec.comp hV
      (Computable.pair Computable.fst
        (decodeFirst_computable.comp Computable.snd))
  exact (Partrec.cond hGuard hCall Partrec.none).of_eq fun pr => by
    unfold conditionalProgramLengthContextDecompressor
    cases h : (pr.1.length == decodeBits (decodeSecond pr.2)) <;> rfl

lemma conditionalProgramLengthContextDecompressor_isPrefixMachine
    (V : Map) :
    IsPrefixMachine (conditionalProgramLengthContextDecompressor V) := by
  intro y p hp q hq hpre
  change (conditionalProgramLengthContextDecompressor V (p, y)).Dom at hp
  change (conditionalProgramLengthContextDecompressor V (q, y)).Dom at hq
  unfold conditionalProgramLengthContextDecompressor at hp hq
  cases hpEq : (p.length == decodeBits (decodeSecond y)) <;>
      rw [hpEq] at hp
  · exact False.elim hp
  cases hqEq : (q.length == decodeBits (decodeSecond y)) <;>
      rw [hqEq] at hq
  · exact False.elim hq
  have hpLen : p.length = decodeBits (decodeSecond y) :=
    beq_iff_eq.mp hpEq
  have hqLen : q.length = decodeBits (decodeSecond y) :=
    beq_iff_eq.mp hqEq
  exact hpre.eq_of_length (by rw [hpLen, hqLen])

lemma conditionalProgramLengthContextDecompressor_produces
    {V : Map} {p x y : BitString} {k : Nat}
    (hp : produces V p y x) (hlen : p.length = k) :
    produces (conditionalProgramLengthContextDecompressor V) p
      (pairCode y (Nat.bits k)) x := by
  unfold produces conditionalProgramLengthContextDecompressor
  simp only [decodeSecond_pairCode, decodeBits_natBits, hlen, beq_self_eq_true,
    decodeFirst_pairCode]
  exact hp

/-- An exact plain conditional description becomes a fixed-length prefix
description when its length is supplied in the condition. -/
theorem KP_le_condK_value_given_value_code
    (U V : Map) (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString, ∀ k : Nat,
      HasPlainConditionalComplexityValue V x y k →
      KP U x (pairCode y (Nat.bits k)) ≤
        (k : ENat) + (c : ENat) := by
  have hM :
      IsPrefixDecompressor
        (conditionalProgramLengthContextDecompressor V) :=
    ⟨conditionalProgramLengthContextDecompressor_isDecompressor V hV.1,
      conditionalProgramLengthContextDecompressor_isPrefixMachine V⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, fun x y k hk => ?_⟩
  obtain ⟨p, hp, hpLen⟩ := hk.exists_program
  have hprod :
      produces (conditionalProgramLengthContextDecompressor V) p
        (pairCode y (Nat.bits k)) x :=
    conditionalProgramLengthContextDecompressor_produces hp hpLen
  calc
    KP U x (pairCode y (Nat.bits k))
        ≤ KP (conditionalProgramLengthContextDecompressor V) x
            (pairCode y (Nat.bits k)) + (c : ENat) :=
      hc x (pairCode y (Nat.bits k))
    _ ≤ (p.length : ENat) + (c : ENat) := by
      simpa [add_comm] using
        add_le_add_right (KP_le_programLength_of_produces hprod) (c : ENat)
    _ = (k : ENat) + (c : ENat) := by rw [hpLen]

/-- Conditional plain-to-prefix bridge with logarithmic overhead at an exact
plain conditional complexity value. -/
theorem KP_le_condK_add_log_of_value
    (U V : Map) (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString, ∀ k : Nat,
      HasPlainConditionalComplexityValue V x y k →
      KP U x y ≤
        (k : ENat) + (logSlack c (k + 1) : ENat) := by
  obtain ⟨cFixed, hFixed⟩ :=
    KP_le_condK_value_given_value_code U V hU hV
  obtain ⟨cRemove, hRemove⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  let C := 2 + (cFixed + cBits + cRemove)
  refine ⟨C, fun x y k hk => ?_⟩
  have hBitsMono :
      (Nat.bits k).length ≤ (Nat.bits (k + 1)).length :=
    length_natBits_mono (Nat.le_succ k)
  have hCoef : 2 ≤ C := by dsimp [C]; omega
  have hConst : cFixed + cBits + cRemove ≤ C := by
    dsimp [C]
    omega
  have hSlack :
      2 * (Nat.bits k).length + (cFixed + cBits + cRemove) ≤
        logSlack C (k + 1) := by
    unfold logSlack
    calc
      2 * (Nat.bits k).length + (cFixed + cBits + cRemove)
          ≤ 2 * (Nat.bits (k + 1)).length +
              (cFixed + cBits + cRemove) := by omega
      _ ≤ C * (Nat.bits (k + 1)).length + C :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hCoef) hConst
  calc
    KP U x y
        ≤ KP U x (pairCode y (Nat.bits k)) +
            KPPlain U (Nat.bits k) + (cRemove : ENat) :=
      hRemove x y (Nat.bits k)
    _ ≤ ((k : ENat) + (cFixed : ENat)) +
          (2 * (Nat.bits k).length + (cBits : ENat)) +
          (cRemove : ENat) := by
      gcongr
      · exact hFixed x y k hk
      · exact hBits (Nat.bits k)
    _ = (k : ENat) +
          ((2 * (Nat.bits k).length +
            (cFixed + cBits + cRemove) : Nat) : ENat) := by
      push_cast
      ring
    _ ≤ (k : ENat) + (logSlack C (k + 1) : ENat) := by
      have hs :
          ((2 * (Nat.bits k).length +
            (cFixed + cBits + cRemove) : Nat) : ENat) ≤
            (logSlack C (k + 1) : ENat) := by
        exact_mod_cast hSlack
      exact add_le_add_right hs _

/-- Two logarithmic terms whose arguments are each within a fixed additive
distance of a common budget fold into one logarithmic slack at that budget. -/
theorem logSlack_two_values_le_pair
    (c₁ c₂ b₁ b₂ : Nat) :
    ∃ C : Nat, ∀ k₁ k₂ kxy : Nat,
      k₁ ≤ kxy + b₁ →
      k₂ ≤ kxy + b₂ →
      logSlack c₁ (k₁ + 1) + logSlack c₂ (k₂ + 1) ≤
        logSlack C (kxy + 1) := by
  let A := logSlack c₁ b₁ + logSlack c₂ b₂
  refine ⟨c₁ + c₂ + A, ?_⟩
  intro k₁ k₂ kxy hk₁ hk₂
  have harg₁ : k₁ + 1 ≤ (kxy + 1) + b₁ := by omega
  have harg₂ : k₂ + 1 ≤ (kxy + 1) + b₂ := by omega
  have h₁ :
      logSlack c₁ (k₁ + 1) ≤
        logSlack c₁ (kxy + 1) + logSlack c₁ b₁ :=
    (logSlack_mono_right c₁ harg₁).trans
      (logSlack_add_le c₁ (kxy + 1) b₁)
  have h₂ :
      logSlack c₂ (k₂ + 1) ≤
        logSlack c₂ (kxy + 1) + logSlack c₂ b₂ :=
    (logSlack_mono_right c₂ harg₂).trans
      (logSlack_add_le c₂ (kxy + 1) b₂)
  calc
    logSlack c₁ (k₁ + 1) + logSlack c₂ (k₂ + 1)
        ≤ logSlack (c₁ + c₂) (kxy + 1) + A := by
      rw [← logSlack_add_const]
      dsimp [A]
      omega
    _ ≤ logSlack (c₁ + c₂ + A) (kxy + 1) :=
      logSlack_add_nat_le (c₁ + c₂) A (kxy + 1)

/-- Prefix complexity has an exact natural value for an optimal prefix
machine. -/
theorem exists_prefixComplexityValue
    (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
    ∃ k : Nat, HasPrefixComplexityValue U x k := by
  obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
  have hfinite : KPPlain U x ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hc x)
    rw [WithTop.add_ne_top]
    exact ⟨WithTop.mul_ne_top (by norm_num) (ENat.coe_ne_top _),
      ENat.coe_ne_top _⟩
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite
  exact ⟨k, hk⟩

theorem pairPlainK_chain_lower_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString, ∀ kx kyx kxy : Nat,
      HasPlainComplexityValue V x kx →
      HasPlainConditionalComplexityValue V y x kyx →
      HasPlainComplexityValue V (pairCode x y) kxy →
      kx + kyx ≤ kxy + logSlack c (kxy + 1) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cPlain, hPlain⟩ :=
    plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨cCond, hCond⟩ :=
    condK_le_KP V U hV hU.isPrefixDecompressor
  obtain ⟨cRemove, hRemove⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cLower, hLower⟩ := KPPair_chain_lower U hU
  obtain ⟨cPair, hPair⟩ :=
    KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨cNatCode, hNatCode⟩ := KPPlain_natCode_le_log U hU
  obtain ⟨cProj, hProj⟩ := KPPlain_left_le_KPPair U hU
  let bPrefix := cBits + cPair + cProj
  let cNatRaw := 2 + cNatCode
  obtain ⟨cNatFold, hNatFold⟩ :=
    logSlack_linear_bound cNatRaw 4 (4 + bPrefix)
  let cPairRaw := 2 + cBits
  let cFixed := cPlain + cCond + cRemove + cLower + cPair
  let C := cNatFold + cPairRaw + cFixed
  refine ⟨C, fun x y kx kyx kxy hx hyx hxy => ?_⟩
  obtain ⟨kpx, hkpx⟩ := exists_prefixComplexityValue U hU x
  have hkpxBoundENat :
      (kpx : ENat) ≤
        ((kxy + 2 * (Nat.bits kxy).length + bPrefix : Nat) : ENat) := by
    calc
      (kpx : ENat) = KPPlain U x := hkpx
      _ ≤ KPPair U x y + (cProj : ENat) := hProj x y
      _ ≤ ((kxy : ENat) + KPPlain U (Nat.bits kxy) +
            (cPair : ENat)) + (cProj : ENat) := by
        gcongr
        exact hPair (pairCode x y) kxy hxy
      _ ≤ ((kxy : ENat) +
            (2 * (Nat.bits kxy).length + (cBits : ENat)) +
            (cPair : ENat)) + (cProj : ENat) := by
        gcongr
        exact hBits (Nat.bits kxy)
      _ = ((kxy + 2 * (Nat.bits kxy).length +
            bPrefix : Nat) : ENat) := by
        dsimp [bPrefix]
        push_cast
        ring
  have hkpxBound :
      kpx ≤ kxy + 2 * (Nat.bits kxy).length + bPrefix := by
    exact_mod_cast hkpxBoundENat
  have hkpxLinear :
      kpx ≤ 4 * (kxy + 1) + bPrefix := by
    have hlen := length_natBits_le kxy
    omega
  have hNatRaw :
      2 * (Nat.bits kpx).length + cNatCode ≤
        logSlack cNatRaw kpx := by
    dsimp [cNatRaw]
    unfold logSlack
    nlinarith [Nat.zero_le (cNatCode * (Nat.bits kpx).length)]
  have hNatFolded :
      2 * (Nat.bits kpx).length + cNatCode ≤
        logSlack cNatFold (kxy + 1) := by
    calc
      2 * (Nat.bits kpx).length + cNatCode
          ≤ logSlack cNatRaw kpx := hNatRaw
      _ ≤ logSlack cNatRaw (4 * (kxy + 1) + bPrefix) :=
        logSlack_mono_right cNatRaw hkpxLinear
      _ ≤ logSlack cNatRaw
            (4 * (kxy + 1) + (4 + bPrefix)) :=
        logSlack_mono_right cNatRaw (by omega)
      _ ≤ logSlack cNatFold (kxy + 1) :=
        hNatFold (kxy + 1)
  have hPairRaw :
      2 * (Nat.bits kxy).length + cBits ≤
        logSlack cPairRaw (kxy + 1) := by
    have hmono :
        (Nat.bits kxy).length ≤ (Nat.bits (kxy + 1)).length :=
      length_natBits_mono (Nat.le_succ kxy)
    dsimp [cPairRaw]
    unfold logSlack
    nlinarith [Nat.zero_le (cBits * (Nat.bits (kxy + 1)).length)]
  have hLogs :
      (2 * (Nat.bits kpx).length + cNatCode) +
          (2 * (Nat.bits kxy).length + cBits) ≤
        logSlack (cNatFold + cPairRaw) (kxy + 1) := by
    calc
      (2 * (Nat.bits kpx).length + cNatCode) +
            (2 * (Nat.bits kxy).length + cBits)
          ≤ logSlack cNatFold (kxy + 1) +
              logSlack cPairRaw (kxy + 1) :=
        Nat.add_le_add hNatFolded hPairRaw
      _ = logSlack (cNatFold + cPairRaw) (kxy + 1) :=
        logSlack_add_const cNatFold cPairRaw (kxy + 1)
  have hOverhead :
      (2 * (Nat.bits kpx).length + cNatCode) +
          (2 * (Nat.bits kxy).length + cBits) + cFixed ≤
        logSlack C (kxy + 1) := by
    calc
      (2 * (Nat.bits kpx).length + cNatCode) +
            (2 * (Nat.bits kxy).length + cBits) + cFixed
          ≤ logSlack (cNatFold + cPairRaw) (kxy + 1) + cFixed := by
        omega
      _ ≤ logSlack C (kxy + 1) := by
        simpa [C] using
          logSlack_add_nat_le (cNatFold + cPairRaw) cFixed (kxy + 1)
  have hMain :
      ((kx + kyx : Nat) : ENat) ≤
        ((kxy + logSlack C (kxy + 1) : Nat) : ENat) := by
    calc
      ((kx + kyx : Nat) : ENat)
          = (kx : ENat) + (kyx : ENat) := by push_cast; rfl
      _ ≤ (KPPlain U x + (cPlain : ENat)) +
            (KP U y x + (cCond : ENat)) := by
        gcongr
        · rw [← hx]
          exact hPlain x
        · rw [← hyx]
          exact hCond y x
      _ ≤ (KPPlain U x + (cPlain : ENat)) +
            (KP U y (pairCode x (natCode kpx)) +
              KPPlain U (natCode kpx) + (cRemove : ENat) +
              (cCond : ENat)) := by
        gcongr
        exact hRemove y x (natCode kpx)
      _ = (KPPlain U x + KP U y (pairCode x (natCode kpx))) +
            KPPlain U (natCode kpx) +
            ((cPlain + cCond + cRemove : Nat) : ENat) := by
        push_cast
        ac_rfl
      _ ≤ (KPPair U x y + (cLower : ENat)) +
            KPPlain U (natCode kpx) +
            ((cPlain + cCond + cRemove : Nat) : ENat) := by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right
            (add_le_add_right (hLower x y kpx hkpx)
              (KPPlain U (natCode kpx)))
            ((cPlain + cCond + cRemove : Nat) : ENat)
      _ ≤ (((kxy : ENat) + KPPlain U (Nat.bits kxy) +
              (cPair : ENat)) + (cLower : ENat)) +
            KPPlain U (natCode kpx) +
            ((cPlain + cCond + cRemove : Nat) : ENat) := by
        gcongr
        exact hPair (pairCode x y) kxy hxy
      _ ≤ (((kxy : ENat) + KPPlain U (Nat.bits kxy) +
              (cPair : ENat)) + (cLower : ENat)) +
            (2 * (Nat.bits kpx).length + (cNatCode : ENat)) +
            ((cPlain + cCond + cRemove : Nat) : ENat) := by
        gcongr
        exact hNatCode kpx
      _ ≤ (((kxy : ENat) +
              (2 * (Nat.bits kxy).length + (cBits : ENat)) +
              (cPair : ENat)) + (cLower : ENat)) +
            (2 * (Nat.bits kpx).length + (cNatCode : ENat)) +
            ((cPlain + cCond + cRemove : Nat) : ENat) := by
        gcongr
        exact hBits (Nat.bits kxy)
      _ = ((kxy +
            ((2 * (Nat.bits kpx).length + cNatCode) +
              (2 * (Nat.bits kxy).length + cBits) +
              cFixed) : Nat) : ENat) := by
        dsimp [cFixed]
        push_cast
        ring
      _ ≤ ((kxy + logSlack C (kxy + 1) : Nat) : ENat) := by
        exact_mod_cast Nat.add_le_add_left hOverhead kxy
  exact_mod_cast hMain

theorem pairPlainK_chain_upper_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString, ∀ kx kyx kxy : Nat,
      HasPlainComplexityValue V x kx →
      HasPlainConditionalComplexityValue V y x kyx →
      HasPlainComplexityValue V (pairCode x y) kxy →
      kxy ≤ kx + kyx + logSlack c (kxy + 1) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_KPPair V U hV hU
  obtain ⟨cChain, hChain⟩ := KPPair_chain_upper_weak U hU
  obtain ⟨cPlain, hPlain⟩ :=
    KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨cCond, hCond⟩ := KP_le_condK_add_log_of_value U V hU hV
  obtain ⟨cLeft, hLeft⟩ := pairPlainK_left_le V hV
  obtain ⟨cRight, hRight⟩ := condK_right_le_pairPlainK V hV
  obtain ⟨cLogs, hLogs⟩ :=
    logSlack_two_values_le_pair 2 cCond cLeft cRight
  let cConst := cBits + cPlain + cChain + cPair
  let C := cLogs + cConst
  refine ⟨C, fun x y kx kyx kxy hx hyx hxy => ?_⟩
  have hkxBoundENat :
      (kx : ENat) ≤ (kxy : ENat) + (cLeft : ENat) := by
    calc
      (kx : ENat) = plainK V x := hx.symm
      _ ≤ pairPlainK V x y + (cLeft : ENat) := hLeft x y
      _ = (kxy : ENat) + (cLeft : ENat) := by
        rw [pairPlainK, hxy]
  have hkyxBoundENat :
      (kyx : ENat) ≤ (kxy : ENat) + (cRight : ENat) := by
    calc
      (kyx : ENat) = condK V y x := hyx.symm
      _ ≤ pairPlainK V x y + (cRight : ENat) := hRight x y
      _ = (kxy : ENat) + (cRight : ENat) := by
        rw [pairPlainK, hxy]
  have hkxBound : kx ≤ kxy + cLeft := by
    exact_mod_cast hkxBoundENat
  have hkyxBound : kyx ≤ kxy + cRight := by
    exact_mod_cast hkyxBoundENat
  have hTwoLogs :
      logSlack 2 (kx + 1) + logSlack cCond (kyx + 1) ≤
        logSlack cLogs (kxy + 1) :=
    hLogs kx kyx kxy hkxBound hkyxBound
  have hBitsSlack :
      2 * (Nat.bits kx).length ≤ logSlack 2 (kx + 1) := by
    have hmono :
        (Nat.bits kx).length ≤ (Nat.bits (kx + 1)).length :=
      length_natBits_mono (Nat.le_succ kx)
    unfold logSlack
    omega
  have hConstFold :
      logSlack cLogs (kxy + 1) + cConst ≤
        logSlack C (kxy + 1) := by
    simpa [C] using logSlack_add_nat_le cLogs cConst (kxy + 1)
  have hOverhead :
      2 * (Nat.bits kx).length + cBits + cPlain +
          logSlack cCond (kyx + 1) + cChain + cPair ≤
        logSlack C (kxy + 1) := by
    dsimp [cConst] at hConstFold
    omega
  have hMain :
      (kxy : ENat) ≤
        ((kx + kyx + logSlack C (kxy + 1) : Nat) : ENat) := by
    calc
      (kxy : ENat) = plainK V (pairCode x y) := hxy.symm
      _ ≤ KPPair U x y + (cPair : ENat) := hPair x y
      _ ≤ (KPPlain U x + KP U y x + (cChain : ENat)) +
            (cPair : ENat) := by
        gcongr
        exact hChain x y
      _ ≤ (((kx : ENat) + KPPlain U (Nat.bits kx) +
              (cPlain : ENat)) +
            ((kyx : ENat) + (logSlack cCond (kyx + 1) : ENat)) +
            (cChain : ENat)) + (cPair : ENat) := by
        gcongr
        · exact hPlain x kx hx
        · exact hCond y x kyx hyx
      _ ≤ (((kx : ENat) +
              (2 * (Nat.bits kx).length + (cBits : ENat)) +
              (cPlain : ENat)) +
            ((kyx : ENat) + (logSlack cCond (kyx + 1) : ENat)) +
            (cChain : ENat)) + (cPair : ENat) := by
        gcongr
        exact hBits (Nat.bits kx)
      _ = ((kx + kyx +
            (2 * (Nat.bits kx).length + cBits + cPlain +
              logSlack cCond (kyx + 1) + cChain + cPair) : Nat) : ENat) := by
        push_cast
        ring
      _ ≤ ((kx + kyx + logSlack C (kxy + 1) : Nat) : ENat) := by
        exact_mod_cast Nat.add_le_add_left hOverhead (kx + kyx)
  exact_mod_cast hMain

/-- Arithmetic closure used after the lower plain chain inequality: if the pair
complexity is only a fixed amount above `k`, its conditional remainder is
logarithmic in `k`. -/
theorem chain_lower_close_conditional
    (cPair cChain : Nat) :
    ∃ C : Nat, ∀ k q r : Nat,
      r ≤ k + cPair →
      k + q ≤ r + logSlack cChain (r + 1) →
      q ≤ logSlack C (k + 1) := by
  let A := cPair + logSlack cChain cPair
  refine ⟨cChain + A, ?_⟩
  intro k q r hr hchain
  have hrArg : r + 1 ≤ (k + 1) + cPair := by omega
  have hrLog :
      logSlack cChain (r + 1) ≤
        logSlack cChain ((k + 1) + cPair) :=
    logSlack_mono_right cChain hrArg
  have hsplit :
      logSlack cChain ((k + 1) + cPair) ≤
        logSlack cChain (k + 1) + logSlack cChain cPair :=
    logSlack_add_le cChain (k + 1) cPair
  have hq :
      q ≤ cPair + logSlack cChain (k + 1) +
        logSlack cChain cPair := by
    omega
  have hq' : q ≤ logSlack cChain (k + 1) + A := by
    dsimp [A]
    omega
  calc
    q ≤ logSlack cChain (k + 1) + A := hq'
    _ ≤ logSlack (cChain + A) (k + 1) := by
      unfold logSlack
      calc
        cChain * (Nat.bits (k + 1)).length + cChain + A
            ≤ cChain * (Nat.bits (k + 1)).length + cChain +
                (A * (Nat.bits (k + 1)).length + A) := by
              gcongr
              exact Nat.le_add_left A _
        _ = (cChain + A) * (Nat.bits (k + 1)).length +
              (cChain + A) := by ring

theorem pairPlainK_symmetryOfInformation_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString, ∀ kx kyx kxy : Nat,
      HasPlainComplexityValue V x kx →
      HasPlainConditionalComplexityValue V y x kyx →
      HasPlainComplexityValue V (pairCode x y) kxy →
      (kxy ≤ kx + kyx + logSlack c (kxy + 1)) ∧
      (kx + kyx ≤ kxy + logSlack c (kxy + 1)) := by
  obtain ⟨cUpper, hUpper⟩ := pairPlainK_chain_upper_values V hV
  obtain ⟨cLower, hLower⟩ := pairPlainK_chain_lower_values V hV
  refine ⟨cUpper + cLower, ?_⟩
  intro x y kx kyx kxy hx hyx hxy
  have hu := hUpper x y kx kyx kxy hx hyx hxy
  have hl := hLower x y kx kyx kxy hx hyx hxy
  constructor
  · exact hu.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_add_right cUpper cLower) (kxy + 1))
      (kx + kyx))
  · exact hl.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_add_left cLower cUpper) (kxy + 1))
      kxy)

end Kolmogorov
