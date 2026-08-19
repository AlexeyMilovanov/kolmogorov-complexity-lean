import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun

namespace Kolmogorov

/-!
# Arithmetic leaves for the `t1` chronological run

These lemmas contain only the cancellation and power arithmetic used after a
reachable run has supplied its event-count and charging inequalities.  They do
not quantify over an unconstrained run state.
-/

/-- External rebuilds are logarithmically absorbable once they are charged to
the `B` events and `C″` batches. -/
theorem t1_external_rebuilds_lt
    (epsilon d external : Nat)
    (hExternal :
      external ≤ 2 ^ (epsilon + 1) + 2 ^ (epsilon + d + 1)) :
    external < 2 ^ (epsilon + d + 3) := by
  have hmono :
      2 ^ (epsilon + 1) ≤ 2 ^ (epsilon + d + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum :
      2 ^ (epsilon + 1) + 2 ^ (epsilon + d + 1) ≤
        2 ^ (epsilon + d + 2) := by
    calc
      2 ^ (epsilon + 1) + 2 ^ (epsilon + d + 1)
          ≤ 2 ^ (epsilon + d + 1) +
              2 ^ (epsilon + d + 1) :=
        Nat.add_le_add hmono le_rfl
      _ = 2 ^ (epsilon + d + 2) := by
        rw [show epsilon + d + 2 = epsilon + d + 1 + 1 by omega,
          pow_succ]
        ring
  have hstrict :
      2 ^ (epsilon + d + 2) < 2 ^ (epsilon + d + 3) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact hExternal.trans_lt (hsum.trans_lt hstrict)

/-- Cancel the size `2^(k-epsilon)` of a current model from the source's
saturation charging inequality. -/
theorem t1_saturation_rebuilds_le
    (epsilon k saturation t : Nat)
    (hEpsilon : epsilon ≤ k)
    (hCharge :
      saturation * 2 ^ (k - epsilon) ≤
        2 ^ (k + 1) * t + 2 ^ k) :
    saturation ≤ 2 ^ epsilon * (2 * t + 1) := by
  have hfactorPos : 0 < 2 ^ (k - epsilon) := by positivity
  have hk :
      2 ^ k = 2 ^ (k - epsilon) * 2 ^ epsilon := by
    calc
      2 ^ k = 2 ^ ((k - epsilon) + epsilon) := by
        congr 1
        omega
      _ = 2 ^ (k - epsilon) * 2 ^ epsilon := pow_add _ _ _
  have hCharge' :
      saturation * 2 ^ (k - epsilon) ≤
        (2 ^ epsilon * (2 * t + 1)) * 2 ^ (k - epsilon) := by
    calc
      saturation * 2 ^ (k - epsilon)
          ≤ 2 ^ (k + 1) * t + 2 ^ k := hCharge
      _ = (2 ^ epsilon * (2 * t + 1)) *
          2 ^ (k - epsilon) := by
        rw [pow_succ, hk]
        ring
  exact Nat.le_of_mul_le_mul_right hCharge' hfactorPos

/-- The preceding cancellation lemma with the `C′`-mark and `D`-mark totals
kept as separate reachable-run premises. -/
theorem t1_saturation_rebuilds_le_of_totals
    (epsilon k saturation totalC totalD t : Nat)
    (hEpsilon : epsilon ≤ k)
    (hC : totalC ≤ 2 ^ (k + 1) * t)
    (hD : totalD ≤ 2 ^ k)
    (hCharge :
      saturation * 2 ^ (k - epsilon) ≤ totalC + totalD) :
    saturation ≤ 2 ^ epsilon * (2 * t + 1) := by
  apply t1_saturation_rebuilds_le epsilon k saturation t hEpsilon
  exact hCharge.trans (Nat.add_le_add hC hD)

end Kolmogorov

namespace Kolmogorov

/-- The external and saturation rebuild bounds combine into a single
logarithmic-width version counter. -/
theorem t1_change_count_arith :
  ∀ cDesc cSparse, ∃ cRun, ∀ n k epsilon external saturation totalC totalD,
    epsilon ≤ k →
    k + 4 ≤ n →
    external ≤
      2 ^ (epsilon + 1) +
      2 ^ (epsilon + logSlack cDesc n + 1) →
    totalC ≤ 2 ^ (k + 1) * (cSparse * n + cSparse) →
    totalD ≤ 2 ^ k →
    saturation * 2 ^ (k - epsilon) ≤ totalC + totalD →
    external + saturation <
      2 ^ (epsilon + logSlack cRun n) := by
  intro cDesc cSparse
  use cDesc + cSparse + 20
  intro n k epsilon external saturation totalC totalD hepsilon hk external_h
    totalC_h totalD_h saturation_h
  -- Bound external using t1_external_rebuilds_lt
  have external_lt :=
    t1_external_rebuilds_lt epsilon (logSlack cDesc n) external external_h
  -- Bound saturation using t1_saturation_rebuilds_le_of_totals
  have totalC_bound : totalC ≤ 2 ^ (k + 1) * (cSparse * n + cSparse) := totalC_h
  have saturation_le :=
    t1_saturation_rebuilds_le_of_totals epsilon k saturation totalC totalD
      (cSparse * n + cSparse) hepsilon totalC_bound totalD_h saturation_h
  -- Factor out 2^epsilon
  have h1 : external < 2 ^ epsilon * 2 ^ (logSlack cDesc n + 3) := by
    rw [← pow_add]
    exact external_lt
  -- Bound n from below
  have hn : n ≥ 4 := by omega
  -- Bound (Nat.bits n).length ≥ 2
  have hbits_len : (Nat.bits n).length ≥ 2 := by
    have hn4 : n ≥ 4 := hn
    calc (Nat.bits n).length = Nat.size n := by rw [Nat.size_eq_bits_len]
      _ ≥ Nat.size 4 := Nat.size_le_size hn4
      _ = 3 := by decide
      _ ≥ 2 := by norm_num
  -- The value `n + 1` fits within one more bit.
  have hbound : n + 1 ≤ 2 ^ ((Nat.bits n).length + 1) := by
    have h := Nat.lt_size_self n
    rw [← Nat.size_eq_bits_len] at h
    calc n + 1 ≤ 2 ^ (Nat.bits n).length := Nat.succ_le_of_lt h
      _ = 2 ^ ((Nat.bits n).length + 1) / 2 := by rw [Nat.pow_succ]; omega
      _ ≤ 2 ^ ((Nat.bits n).length + 1) := Nat.div_le_self _ _
  -- Main arithmetic: show the sum is bounded
  -- Use an enlarged bit width and exponent.
  set m := (Nat.bits n).length + 1 with hm
  have hm_ge : m ≥ 3 := by omega
  set E := (cDesc + cSparse + 20) * m with hE_def
  have h20m : (cDesc + cSparse + 20) * m ≥ 20 * m :=
    Nat.mul_le_mul_right m (by omega)
  have h60 : 20 * m ≥ 60 := Nat.mul_le_mul_left 20 hm_ge
  have hE_ge : E ≥ 60 := by linarith
  have hE_pos : E > 0 := by linarith
  have hE_sub : E - 1 + 1 = E := Nat.sub_add_cancel hE_pos
  -- External bound: cDesc * m + 3 < E - 1
  have hext_half : cDesc * m + 3 < E - 1 := by
    change cDesc * m + 3 < (cDesc + cSparse + 20) * m - 1
    have hm3 : m ≥ 3 := hm_ge
    have hcD_ge : cDesc + cSparse + 20 ≥ cDesc + 20 := by omega
    nlinarith
  -- Saturation bound: cSparse + m + 2 < E - 1
  have hexp3 : cSparse + m + 2 < E - 1 := by
    change cSparse + m + 2 < (cDesc + cSparse + 20) * m - 1
    have hm3 : m ≥ 3 := hm_ge
    have hcD_ge : cDesc + cSparse + 20 ≥ cSparse + 20 := by omega
    nlinarith
  have hext_lt_half : 2 ^ (cDesc * m + 3) < 2 ^ (E - 1) :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) hext_half
  -- Saturation term bound
  have hsatab : 2 * (cSparse * n + cSparse) + 1 ≤ 2 * cSparse * 2 ^ m + 1 := by
    have := Nat.mul_le_mul_left cSparse hbound; linarith
  have hcsparse_bound : cSparse ≤ 2 ^ cSparse :=
    Nat.le_of_lt (Nat.lt_pow_self one_lt_two)
  have hsat_step1 : 2 * cSparse * 2 ^ m ≤ 2 ^ (cSparse + m + 2) := by
    have h1 : 2 * cSparse * 2 ^ m = cSparse * 2 ^ (m + 1) := by ring
    have h2 : cSparse * 2 ^ (m + 1) ≤ 2 ^ cSparse * 2 ^ (m + 1) :=
      Nat.mul_le_mul_right _ hcsparse_bound
    have h3 : 2 ^ cSparse * 2 ^ (m + 1) = 2 ^ (cSparse + m + 1) := by
      rw [← pow_add]
      ring_nf
    have h4 : 2 ^ (cSparse + m + 1) ≤ 2 ^ (cSparse + m + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    linarith
  have hsat_step2 : 2 * cSparse * 2 ^ m + 1 < 2 ^ (cSparse + m + 3) := by
    have hpow : 2 ^ (cSparse + m + 3) = 2 * 2 ^ (cSparse + m + 2) := by ring
    rw [hpow]
    have hge : 1 < 2 ^ (cSparse + m + 2) := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hsat_half : 2 * cSparse * 2 ^ m + 1 < 2 ^ (E - 1) :=
    Nat.lt_of_lt_of_le hsat_step2
      (Nat.pow_le_pow_right (by norm_num) hexp3)
  -- Combine: need hsum
  have hsum :
      2 ^ (cDesc * m + 3) + (2 * (cSparse * n + cSparse) + 1) < 2 ^ E := by
    have hadd : 2 ^ (E - 1) + 2 ^ (E - 1) = 2 ^ E := by
      have : E = (E - 1) + 1 := hE_sub
      conv_rhs => rw [this, pow_succ]
      ring
    linarith [hext_lt_half, hsat_half, hsatab]
  -- logSlack (cDesc + cSparse + 20) n = E
  have hlog : logSlack (cDesc + cSparse + 20) n = E := by
    unfold logSlack
    ring
  -- Final bound
  have hext_lt' : external < 2 ^ epsilon * 2 ^ (logSlack cDesc n + 3) := by
    rw [← pow_add]
    exact external_lt
  have hsat_le' :
      saturation ≤ 2 ^ epsilon * (2 * (cSparse * n + cSparse) + 1) :=
    saturation_le
  have hadd_lt :
      external + saturation < 2 ^ epsilon * 2 ^ (logSlack cDesc n + 3) +
        2 ^ epsilon * (2 * (cSparse * n + cSparse) + 1) := by
    apply Nat.add_lt_add_of_lt_of_le hext_lt' hsat_le'
  have hfactor :
      2 ^ epsilon * 2 ^ (logSlack cDesc n + 3) +
        2 ^ epsilon * (2 * (cSparse * n + cSparse) + 1) =
      2 ^ epsilon *
        (2 ^ (logSlack cDesc n + 3) + (2 * (cSparse * n + cSparse) + 1)) := by
    ring
  have hmul_lt :
      2 ^ epsilon *
          (2 ^ (logSlack cDesc n + 3) + (2 * (cSparse * n + cSparse) + 1)) <
        2 ^ epsilon * 2 ^ E :=
    Nat.mul_lt_mul_of_pos_left hsum (pow_pos (by norm_num : 0 < 2) _)
  calc
    external + saturation <
        2 ^ epsilon * 2 ^ (logSlack cDesc n + 3) +
          2 ^ epsilon * (2 * (cSparse * n + cSparse) + 1) := hadd_lt
    _ = 2 ^ epsilon *
        (2 ^ (logSlack cDesc n + 3) +
          (2 * (cSparse * n + cSparse) + 1)) := hfactor
    _ < 2 ^ epsilon * 2 ^ E := hmul_lt
    _ = 2 ^ (epsilon + logSlack (cDesc + cSparse + 20) n) := by rw [← pow_add, hlog]

/-- A self-delimiting header followed by a fixed-width version address. -/
def t1VersionProgram
    (cWidth n k epsilon version : Nat) : BitString :=
  pairCode
    (listCode [Nat.bits n, Nat.bits k, Nat.bits epsilon])
    (chunkAddress version (epsilon + logSlack cWidth n))

/-- Both the parameter header and version number can be recovered from a
well-ranged version program. The range premise certifies the intended fixed
width, though decoding the padded address itself does not require it. -/
theorem t1VersionProgram_roundtrip
    (cWidth n k epsilon version : Nat)
    (hv : version < 2 ^ (epsilon + logSlack cWidth n)) :
    decodeListCode (decodeFirst
      (t1VersionProgram cWidth n k epsilon version)) =
        [Nat.bits n, Nat.bits k, Nat.bits epsilon] ∧
    bitsToNat (decodeSecond
      (t1VersionProgram cWidth n k epsilon version)) = version := by
  have hwidth := chunkAddress_length version (epsilon + logSlack cWidth n) hv
  clear hwidth
  constructor
  · rw [t1VersionProgram, decodeFirst_pairCode, decodeListCode_listCode]
  · simp [t1VersionProgram, decodeSecond_pairCode, bitsToNat_chunkAddress]

/-- The framing overhead is absorbed by increasing the logarithmic constant
by twenty. -/
theorem t1VersionProgram_length_le
    (cWidth n k epsilon version : Nat)
    (hk : k ≤ n) (hepsilon : epsilon ≤ n)
    (hv : version < 2 ^ (epsilon + logSlack cWidth n)) :
    (t1VersionProgram cWidth n k epsilon version).length ≤
      epsilon + logSlack (cWidth + 20) n := by
  unfold t1VersionProgram
  rw [length_pairCode]
  rw [chunkAddress_length version (epsilon + logSlack cWidth n) hv]
  have hlistCode : (listCode [Nat.bits n, Nat.bits k, Nat.bits epsilon]).length =
      2 * (Nat.bits n).length + 2 * (Nat.bits k).length + 2 * (Nat.bits epsilon).length + 3 := by
    simp [listCode_cons, length_pairCode]
    ring
  rw [hlistCode]
  have hbitsK : (Nat.bits k).length ≤ (Nat.bits n).length := length_natBits_mono hk
  have hbitsE : (Nat.bits epsilon).length ≤ (Nat.bits n).length := length_natBits_mono hepsilon
  unfold logSlack
  nlinarith [Nat.zero_le ((Nat.bits n).length), Nat.zero_le ((Nat.bits k).length),
    Nat.zero_le ((Nat.bits epsilon).length)]

end Kolmogorov
