import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SeparationWitness
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SeparationStepWise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SeparationBlockBound
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4

namespace Kolmogorov

lemma lemma_4_standardBlock_at_member
    (V T : Map) (c : Nat)
    (hc : ∀ (q : Nat.Partrec.Code) (_hq : IsCodeFor q V) m j y
        (hB : (standardBlock q m j []).Nonempty) n
        (_hn : n = max y.length m),
      min (plainK V (codedUniformOn (standardBlock q m j []) hB).code)
          ((m - y.length : Nat) : ENat) ≤
        totalCondK T (codedUniformOn (standardBlock q m j []) hB).code y +
          (c : ENat) * plainK V (standardEnumeratorCode q) +
          (logSlack c n : ENat))
    (q : Nat.Partrec.Code) (hq : IsCodeFor q V)
    (m j : Nat) (x y : BitString)
    (hx : x ∈ standardBlock q m j x) (n : Nat)
    (hn : n = max y.length m) :
    let B := standardBlock q m j x
    let hB : B.Nonempty := ⟨x, hx⟩
    min (plainK V (codedUniformOn B hB).code) ((m - y.length : Nat) : ENat)
      ≤ totalCondK T (codedUniformOn B hB).code y +
          (c : ENat) * plainK V (standardEnumeratorCode q) + (logSlack c n : ENat) := by
  dsimp
  exact hc q hq m j y ⟨x, hx⟩ n hn

lemma standardBlock_residual_lower_at_witness
    (c k m : Nat)
    (h_m : (3 * k : ENat) ≤ m + logSlack c (4 * k)) :
    (k : ENat) ≤ (m - 2 * k : Nat) + (logSlack c (4 * k) : ENat) := by
  have h_m_nat : 3 * k ≤ m + logSlack c (4 * k) := by
    exact_mod_cast h_m
  exact_mod_cast (show
    k ≤ (m - 2 * k : Nat) + logSlack c (4 * k) by omega)

/-- **VS40 Theorem (Section 7): separation of minimal sufficient statistics.**

For all large `k` there is a string `x` of length `4 * k` whose plain
description profile is `O(log n)`-close to the Figure-4 gray region, which is
`O(log n)`-normal, which has an `O(log n)`-strong set model of complexity
`k ± O(log n)` and log-cardinality `2 * k`, and for which *every* standard
block containing `x` has a large four-way maximum: either the block is
expensive given `x` under total complexity, or the enumerator itself is
complex, or the block's parameters are far from the corner `(k, 2 * k)`.

The four-way bound is proved by contradiction.  If the maximum `M` were small,
then the block's parameters would sit near `(k, 2 * k)`, so the reconstruction
of `Ω_m` from the block (`enumerationBound_le_standardBlock_complexity`) bounds
the enumeration bound `m` linearly in `k`; this is what makes the Lemma-4 error
term `O(log (max |y| m))` genuinely logarithmic in `k`.  The step-wise theorem
then makes the block cheap given the head `y` of the witness, while Lemma 4
forces `min (C(B), m - |y|)` to be at least `k - O(M + log k)`, a
contradiction. -/
theorem thm_separation
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ThmSeparationStatement V T := by
  classical
  obtain ⟨cW, hW⟩ := exists_separation_witness_core V T hV hT
  obtain ⟨cTot, cSlk, hTotY⟩ := separation_standardBlock_totalCondK_y_le V T hV hT
  obtain ⟨c4, h4⟩ := lemma_4 V T hV hT
  obtain ⟨cLow, hLowProf⟩ := plainK_lower_of_separationGrayProfile_neighborhood V hV
  obtain ⟨cM, hMB⟩ := enumerationBound_le_standardBlock_complexity V hV
  obtain ⟨bAbs, hAbs⟩ := le_two_mul_of_le_add_logSlack cM
  obtain ⟨cFin, hFin⟩ := totalCondK_le_plainK V T hV.1 hT
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  set aLin := 8 + 2 * (2 + cM) with haLin
  obtain ⟨cLin, hLin⟩ := logSlack_linear_bound c4 aLin bAbs
  set CS := (2 * cW + cLow) + (cTot * cW + cSlk) + cLin with hCSdef
  obtain ⟨CS', hCS'⟩ := logSlack_linear_bound (2 * CS) 4 0
  obtain ⟨k1, hk1⟩ := logSlack_lt_self_of_large CS'
  refine ⟨cW, 2 * (cTot + c4 + 1), max k1 1, by omega, ?_⟩
  intro k hk
  have hkpos : 0 < k := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right k1 1) hk)
  -- the total logarithmic slack is below `k / 2`
  have hslack_small : 2 * logSlack CS (4 * k) < k := by
    have h1 : logSlack (2 * CS) (4 * k) ≤ logSlack CS' k := by
      have h := hCS' k
      simpa using h
    have h2 : logSlack CS' k < k := hk1 k (le_trans (le_max_left _ _) hk)
    have h3 : 2 * logSlack CS (4 * k) = logSlack (2 * CS) (4 * k) := by
      unfold logSlack; ring
    omega
  obtain ⟨y, z, hy, hz, hxlen, hProf, hNormal, hA, hxA, hStrong, hALow, hAUp,
    hACard, _hEqA⟩ := hW k hkpos
  refine ⟨y ++ z, hxlen, hProf, hNormal,
    ⟨cylinder (4 * k) y, hA, hxA, hStrong, hALow, hAUp, hACard⟩, ?_⟩
  intro q hq m hm j hxB B hB
  set x := y ++ z with hxdef
  set M := max (totalCondK T (codedUniformOn B hB).code x).toNat
      (max (plainK V (standardEnumeratorCode q)).toNat
        (natPairLInfDistance ((plainSetComplexity V B hB).toNat, finiteSetLogCard B)
          (k, 2 * k))) with hMdef
  by_contra hcon
  push_neg at hcon
  have hMk : M < k := by
    have hle : M ≤ 2 * (cTot + c4 + 1) * M :=
      Nat.le_mul_of_pos_left M (by omega)
    omega
  -- the three components of the four-way maximum
  have hKTle : (totalCondK T (codedUniformOn B hB).code x).toNat ≤ M :=
    le_max_left _ _
  have hQle : (plainK V (standardEnumeratorCode q)).toNat ≤ M :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hDist : natPairLInfDistance
      ((plainSetComplexity V B hB).toNat, finiteSetLogCard B) (k, 2 * k) ≤ M :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  -- finiteness
  have hcodefin : plainK V (codedUniformOn B hB).code ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top ((codedUniformOn B hB).code.length + cLen)))
      (hLen (codedUniformOn B hB).code)
  have hKTfin : totalCondK T (codedUniformOn B hB).code x ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hFin (codedUniformOn B hB).code x)
    rw [Ne, WithTop.add_eq_top]
    push_neg
    exact ⟨hcodefin, ENat.coe_ne_top cFin⟩
  have hKT : totalCondK T (codedUniformOn B hB).code x ≤ (M : ENat) := by
    calc totalCondK T (codedUniformOn B hB).code x
        = (((totalCondK T (codedUniformOn B hB).code x).toNat : Nat) : ENat) :=
          (ENat.coe_toNat hKTfin).symm
      _ ≤ (M : ENat) := by exact_mod_cast hKTle
  have hQfin : plainK V (standardEnumeratorCode q) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top ((standardEnumeratorCode q).length + cLen)))
      (hLen (standardEnumeratorCode q))
  have hQE : plainK V (standardEnumeratorCode q) ≤ (M : ENat) := by
    calc plainK V (standardEnumeratorCode q)
        = (((plainK V (standardEnumeratorCode q)).toNat : Nat) : ENat) :=
          (ENat.coe_toNat hQfin).symm
      _ ≤ (M : ENat) := by exact_mod_cast hQle
  -- the block parameters are near the corner `(k, 2 * k)`
  set CB := (plainSetComplexity V B hB).toNat with hCBdef
  have hjcard : finiteSetLogCard B = j :=
    finiteSetLogCard_standardBlock_of_mem q m j x hxB
  have hd1 : (CB - k) + (k - CB) ≤ M := (Nat.le_max_left _ _).trans hDist
  have hd2 : (finiteSetLogCard B - 2 * k) + (2 * k - finiteSetLogCard B) ≤ M :=
    (Nat.le_max_right _ _).trans hDist
  rw [hjcard] at hd2
  have hCBup : CB ≤ k + M := by omega
  have hCBlow : k ≤ CB + M := by omega
  have hjup : j ≤ 2 * k + M := by omega
  -- Step A: the enumeration bound `m` is linear in `k`
  have hmA : m ≤ CB + j + cM * (plainK V (standardEnumeratorCode q)).toNat +
      logSlack cM m := hMB q hq m j x hxB
  have hm1 : m ≤ (3 * k + (2 + cM) * M) + logSlack cM m := by
    have hQ' : cM * (plainK V (standardEnumeratorCode q)).toNat ≤ cM * M :=
      Nat.mul_le_mul_left _ hQle
    have hexp : 3 * k + (2 + cM) * M = (k + M) + (2 * k + M) + cM * M := by ring
    omega
  have hm2 : m ≤ 2 * (3 * k + (2 + cM) * M) + bAbs :=
    hAbs m (3 * k + (2 + cM) * M) hm1
  have hm3 : m ≤ aLin * k + bAbs := by
    have hMle : (2 + cM) * M ≤ (2 + cM) * k :=
      Nat.mul_le_mul_left _ (le_of_lt hMk)
    have hexp : aLin * k = 8 * k + 2 * ((2 + cM) * k) := by rw [haLin]; ring
    omega
  -- Step B: the Lemma-4 slack is logarithmic in `k`
  set n := max (2 * k) m with hndef
  have hnle : n ≤ aLin * (4 * k) + bAbs := by
    have hbig : aLin * k ≤ aLin * (4 * k) :=
      Nat.mul_le_mul_left _ (by omega)
    have h8 : 8 * (4 * k) ≤ aLin * (4 * k) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2k : 2 * k ≤ aLin * (4 * k) + bAbs := by omega
    exact max_le h2k (by omega)
  have hS3 : logSlack c4 n ≤ logSlack cLin (4 * k) :=
    le_trans (logSlack_mono_right c4 hnle) (hLin (4 * k))
  -- Step C: the step-wise bound on `KT(B | y)`
  have hbudget : cTot * M + logSlack (cTot * cW + cSlk) (4 * k) < k := by
    have h1 : 2 * (cTot * M) ≤ 2 * (cTot + c4 + 1) * M := by
      have : 2 * (cTot * M) = (2 * cTot) * M := by ring
      rw [this]
      exact Nat.mul_le_mul_right _ (by omega)
    have h2 : logSlack (cTot * cW + cSlk) (4 * k) ≤ logSlack CS (4 * k) :=
      logSlack_mono_left (by rw [hCSdef]; omega) _
    omega
  have hTot := hTotY (4 * k) k M cW x y z B hB hA hxB hy hz hxdef rfl hProf hDist
    hKT hALow hAUp hbudget
  -- Step D: Lemma 4 at the witness head
  have hnmax : n = max y.length m := by rw [hndef, hy]
  have hL4 := lemma_4_standardBlock_at_member V T c4 h4 q hq m j x y hxB n hnmax
  dsimp only at hL4
  have hRHS : totalCondK T (codedUniformOn B hB).code y +
        (c4 : ENat) * plainK V (standardEnumeratorCode q) + (logSlack c4 n : ENat) ≤
      ((cTot * M + logSlack (cTot * cW + cSlk) (4 * k) + c4 * M +
        logSlack cLin (4 * k) : Nat) : ENat) := by
    have hS3' : ((logSlack c4 n : Nat) : ENat) ≤ ((logSlack cLin (4 * k) : Nat) : ENat) := by
      exact_mod_cast hS3
    have hTot' : totalCondK T (codedUniformOn B hB).code y ≤
        ((cTot * M + logSlack (cTot * cW + cSlk) (4 * k) : Nat) : ENat) := by
      refine hTot.trans (le_of_eq ?_)
      push_cast
      ring
    calc totalCondK T (codedUniformOn B hB).code y +
          (c4 : ENat) * plainK V (standardEnumeratorCode q) + (logSlack c4 n : ENat)
        ≤ ((cTot * M + logSlack (cTot * cW + cSlk) (4 * k) : Nat) : ENat) +
            (c4 : ENat) * (M : ENat) + ((logSlack cLin (4 * k) : Nat) : ENat) := by
          gcongr
      _ = ((cTot * M + logSlack (cTot * cW + cSlk) (4 * k) + c4 * M +
            logSlack cLin (4 * k) : Nat) : ENat) := by push_cast; ring
  have hCBE : plainK V (codedUniformOn B hB).code = (CB : ENat) := by
    rw [hCBdef]
    exact (ENat.coe_toNat hcodefin).symm
  rw [hCBE] at hL4
  have hmin : min CB (m - y.length) ≤
      cTot * M + logSlack (cTot * cW + cSlk) (4 * k) + c4 * M +
        logSlack cLin (4 * k) := by
    have hcast : ((min CB (m - y.length) : Nat) : ENat) =
        min ((CB : Nat) : ENat) ((m - y.length : Nat) : ENat) := by
      push_cast
      rfl
    have := hL4.trans hRHS
    rw [← hcast] at this
    exact_mod_cast this
  -- Step E: the residual lower bound
  have hLowE : (3 * k : ENat) ≤ plainK V x + (logSlack (2 * cW + cLow) (4 * k) : ENat) :=
    hLowProf (4 * k) k cW x hProf
  have hLowNat : 3 * k ≤ m + logSlack (2 * cW + cLow) (4 * k) := by
    have h : (3 * k : ENat) ≤ (m : ENat) + (logSlack (2 * cW + cLow) (4 * k) : ENat) :=
      hLowE.trans (by gcongr)
    exact_mod_cast h
  -- final arithmetic
  have hS1 : logSlack (2 * cW + cLow) (4 * k) ≤ logSlack CS (4 * k) :=
    logSlack_mono_left (by rw [hCSdef]; omega) _
  have hSsum : logSlack (2 * cW + cLow) (4 * k) + logSlack (cTot * cW + cSlk) (4 * k) +
      logSlack cLin (4 * k) = logSlack CS (4 * k) := by
    rw [hCSdef]; unfold logSlack; ring
  have hcon2 : 2 * (cTot * M + c4 * M + M) < k := by
    have hexp : 2 * (cTot * M + c4 * M + M) = 2 * (cTot + c4 + 1) * M := by ring
    omega
  have hylen : y.length = 2 * k := hy
  rw [hylen] at hmin
  omega

end Kolmogorov
