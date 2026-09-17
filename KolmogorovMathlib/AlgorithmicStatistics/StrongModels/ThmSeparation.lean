import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SeparationWitness
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SeparationStepWise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SeparationBlockBound
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4

/-!
# Separation of minimal sufficient statistics

`thm_separation` (VS40 §7): for all large `k` there is a string whose minimal sufficient
statistic in the plain sense and in the strong sense differ.  The witness comes from
`SeparationWitness`; what is added here is the lower bound that separates the two, obtained
from Lemma 4.

`lemma_4_standardBlock_at_member` states Lemma 4 at a member of a standard block,
`standardBlock_lemma4_rhs_le` and `exists_standardBlock_enumerationBound_linear` bound its
right-hand side and the enumeration bound `m` linearly in `k`, and
`standardBlock_residual_lower_at_witness` and `double_logSlack_lt_self` are the arithmetic
that makes the residual positive for large `k`.
-/

namespace Kolmogorov

/-- The Lemma 4 bound for standard blocks, stated at a member `x` of the block: the block through
`x` obeys the same minimum bound as the block through the empty string. -/
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

/-- Arithmetic of the separation witness: from `3 * k ≤ m + logSlack c (4 * k)` one gets
`k ≤ (m - 2 * k) + logSlack c (4 * k)`. -/
lemma standardBlock_residual_lower_at_witness
    (c k m : Nat)
    (h_m : (3 * k : ENat) ≤ m + logSlack c (4 * k)) :
    (k : ENat) ≤ (m - 2 * k : Nat) + (logSlack c (4 * k) : ENat) := by
  have h_m_nat : 3 * k ≤ m + logSlack c (4 * k) := by
    exact_mod_cast h_m
  exact_mod_cast (show
    k ≤ (m - 2 * k : Nat) + logSlack c (4 * k) by omega)

/-- Bounds an `ENat` value by a natural number given an upper bound on its `toNat`. -/
private lemma enat_le_of_toNat_le {e : ENat} {M : Nat} (hfin : e ≠ ⊤)
    (h : e.toNat ≤ M) : e ≤ (M : ENat) := by
  calc e = (((e.toNat : Nat) : ENat)) := (ENat.natCast_toNat hfin).symm
       _ ≤ (M : ENat) := by exact_mod_cast h

/-- Bound on double logarithmic slack `2 * logSlack CS (4 * k) < k` for large `k`, given that
the slack of `2 * CS` at `4 * k` never exceeds the slack of `CS'` at `k` and that the latter
stays below `k` from `k1` on. -/
private lemma double_logSlack_lt_self (CS CS' k k1 : Nat)
    (hCS' : logSlack (2 * CS) (4 * k) ≤ logSlack CS' k)
    (hk1 : k1 ≤ k → logSlack CS' k < k)
    (hk : max k1 1 ≤ k) :
    2 * logSlack CS (4 * k) < k := by
  have h2 : logSlack CS' k < k := hk1 (le_trans (le_max_left _ _) hk)
  have h3 : 2 * logSlack CS (4 * k) = logSlack (2 * CS) (4 * k) := by
    unfold logSlack; ring
  omega

/-- Linear upper bound on the enumeration bound `m` in terms of `k` when the parameters sit near
`(k, 2 * k)`: there are constants `aLin ≥ 8` and `bAbs` with `m ≤ aLin * k + bAbs` whenever
`m ≤ CB + j + cM * qK + logSlack cM m` with `CB ≤ k + M`, `j ≤ 2 * k + M`, `qK ≤ M` and
`M < k`.  The constants are produced here, from `le_two_mul_of_le_add_logSlack cM`. -/
private lemma exists_standardBlock_enumerationBound_linear (cM : Nat) :
    ∃ aLin bAbs : Nat, 8 ≤ aLin ∧
      ∀ k M CB j m qK : Nat,
        m ≤ CB + j + cM * qK + logSlack cM m →
        CB ≤ k + M → j ≤ 2 * k + M → qK ≤ M → M < k →
        m ≤ aLin * k + bAbs := by
  obtain ⟨bAbs, hAbs⟩ := le_two_mul_of_le_add_logSlack cM
  refine ⟨8 + 2 * (2 + cM), bAbs, by omega, ?_⟩
  intro k M CB j m qK hMB hCBup hjup hqK hMk
  have hm1 : m ≤ (3 * k + (2 + cM) * M) + logSlack cM m := by
    have hQ' : cM * qK ≤ cM * M := Nat.mul_le_mul_left _ hqK
    have hexp : 3 * k + (2 + cM) * M = (k + M) + (2 * k + M) + cM * M := by ring
    omega
  have hm2 : m ≤ 2 * (3 * k + (2 + cM) * M) + bAbs :=
    hAbs m (3 * k + (2 + cM) * M) hm1
  have hMle : (2 + cM) * M ≤ (2 + cM) * k :=
    Nat.mul_le_mul_left _ (le_of_lt hMk)
  have hexp : (8 + 2 * (2 + cM)) * k = 8 * k + 2 * ((2 + cM) * k) := by ring
  omega

/-- Bound on the right-hand side of Lemma 4 for standard blocks. -/
private lemma standardBlock_lemma4_rhs_le
    (V T : Map) (q : Nat.Partrec.Code) (c4 M cTot cW cSlk cLin k n : Nat)
    (B : Finset BitString) (hB : B.Nonempty) (y : BitString)
    (hS3 : logSlack c4 n ≤ logSlack cLin (4 * k))
    (hTot : totalCondK T (codedUniformOn B hB).code y ≤
      ((cTot * M + logSlack (cTot * cW + cSlk) (4 * k) : Nat) : ENat))
    (hQE : plainK V (standardEnumeratorCode q) ≤ (M : ENat)) :
    totalCondK T (codedUniformOn B hB).code y +
        (c4 : ENat) * plainK V (standardEnumeratorCode q) + (logSlack c4 n : ENat) ≤
      ((cTot * M + logSlack (cTot * cW + cSlk) (4 * k) + c4 * M +
        logSlack cLin (4 * k) : Nat) : ENat) := by
  have hS3' : ((logSlack c4 n : Nat) : ENat) ≤ ((logSlack cLin (4 * k) : Nat) : ENat) := by
    exact_mod_cast hS3
  calc totalCondK T (codedUniformOn B hB).code y +
        (c4 : ENat) * plainK V (standardEnumeratorCode q) + (logSlack c4 n : ENat)
      ≤ ((cTot * M + logSlack (cTot * cW + cSlk) (4 * k) : Nat) : ENat) +
          (c4 : ENat) * (M : ENat) + ((logSlack cLin (4 * k) : Nat) : ENat) := by
        gcongr
    _ = ((cTot * M + logSlack (cTot * cW + cSlk) (4 * k) + c4 * M +
          logSlack cLin (4 * k) : Nat) : ENat) := by push_cast; ring

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
  obtain ⟨aLin, bAbs, haLin8, hEnumLinear⟩ :=
    exists_standardBlock_enumerationBound_linear cM
  obtain ⟨cFin, hFin⟩ := totalCondK_le_plainK V T hV.1 hT
  obtain ⟨cLen, hLen⟩ := plainK_le_length V hV
  obtain ⟨cLin, hLin⟩ := logSlack_linear_bound c4 aLin bAbs
  set CS := (2 * cW + cLow) + (cTot * cW + cSlk) + cLin with hCSdef
  obtain ⟨CS', hCS'⟩ := logSlack_linear_bound (2 * CS) 4 0
  obtain ⟨k1, hk1⟩ := logSlack_lt_self_of_large CS'
  refine ⟨cW, 2 * (cTot + c4 + 1), max k1 1, by omega, ?_⟩
  intro k hk
  have hkpos : 0 < k := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right k1 1) hk)
  have hslack_small : 2 * logSlack CS (4 * k) < k :=
    double_logSlack_lt_self CS CS' k k1 (hCS' k) (hk1 k) hk
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
  have hMk : M < k := by
    have hle : M ≤ 2 * (cTot + c4 + 1) * M :=
      Nat.le_mul_of_pos_left M (by omega)
    omega
  have hKTle : (totalCondK T (codedUniformOn B hB).code x).toNat ≤ M := le_max_left _ _
  have hQle : (plainK V (standardEnumeratorCode q)).toNat ≤ M :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hDist : natPairLInfDistance
      ((plainSetComplexity V B hB).toNat, finiteSetLogCard B) (k, 2 * k) ≤ M :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hcodefin : plainK V (codedUniformOn B hB).code ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.natCast_ne_top ((codedUniformOn B hB).code.length + cLen)))
      (hLen (codedUniformOn B hB).code)
  have hKTfin : totalCondK T (codedUniformOn B hB).code x ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hFin (codedUniformOn B hB).code x)
    exact WithTop.add_ne_top.mpr ⟨hcodefin, ENat.natCast_ne_top cFin⟩
  have hKT : totalCondK T (codedUniformOn B hB).code x ≤ (M : ENat) :=
    enat_le_of_toNat_le hKTfin hKTle
  have hQfin : plainK V (standardEnumeratorCode q) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.natCast_ne_top ((standardEnumeratorCode q).length + cLen)))
      (hLen (standardEnumeratorCode q))
  have hQE : plainK V (standardEnumeratorCode q) ≤ (M : ENat) :=
    enat_le_of_toNat_le hQfin hQle
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
  have hmA : m ≤ CB + j + cM * (plainK V (standardEnumeratorCode q)).toNat +
      logSlack cM m := hMB q hq m j x hxB
  have hm3 : m ≤ aLin * k + bAbs :=
    hEnumLinear k M CB j m
      (plainK V (standardEnumeratorCode q)).toNat hmA hCBup hjup hQle hMk
  set n := max (2 * k) m with hndef
  have hnle : n ≤ aLin * (4 * k) + bAbs := by
    have hbig : aLin * k ≤ aLin * (4 * k) := Nat.mul_le_mul_left aLin (by omega)
    have h8k : 8 * (4 * k) ≤ aLin * (4 * k) := Nat.mul_le_mul_right (4 * k) haLin8
    rw [hndef]
    exact max_le (by omega) (by omega)
  have hS3 : logSlack c4 n ≤ logSlack cLin (4 * k) :=
    logSlack_le_of_linear_bound hLin hnle
  have hbudget : cTot * M + logSlack (cTot * cW + cSlk) (4 * k) < k := by
    have hmul : 2 * (cTot * M) = (2 * cTot) * M := by ring
    have h1 : 2 * (cTot * M) ≤ 2 * (cTot + c4 + 1) * M := by
      rw [hmul]; exact Nat.mul_le_mul_right _ (by omega)
    have h2 : logSlack (cTot * cW + cSlk) (4 * k) ≤ logSlack CS (4 * k) :=
      logSlack_mono_left (by rw [hCSdef]; omega) _
    omega
  have hTot := hTotY (4 * k) k M cW x y z B hB hA hxB hy hz hxdef rfl hProf hDist
    hKT hALow hAUp hbudget
  have hnmax : n = max y.length m := by rw [hndef, hy]
  have hL4 := lemma_4_standardBlock_at_member V T c4 h4 q hq m j x y hxB n hnmax
  dsimp only at hL4
  have hRHS := standardBlock_lemma4_rhs_le V T q c4 M cTot cW cSlk cLin k n B hB y
    hS3 hTot hQE
  have hCBE : plainK V (codedUniformOn B hB).code = (CB : ENat) := by
    rw [hCBdef]
    exact (ENat.natCast_toNat hcodefin).symm
  rw [hCBE] at hL4
  have hmin : min CB (m - y.length) ≤
      cTot * M + logSlack (cTot * cW + cSlk) (4 * k) + c4 * M +
        logSlack cLin (4 * k) := by
    have hcast : ((min CB (m - y.length) : Nat) : ENat) =
        min ((CB : Nat) : ENat) ((m - y.length : Nat) : ENat) := by
      push_cast; rfl
    have := hL4.trans hRHS
    rw [← hcast] at this
    exact_mod_cast this
  have hLowE : (3 * k : ENat) ≤ plainK V x + (logSlack (2 * cW + cLow) (4 * k) : ENat) :=
    hLowProf (4 * k) k cW x hProf
  have hLowNat : 3 * k ≤ m + logSlack (2 * cW + cLow) (4 * k) := by
    have h : (3 * k : ENat) ≤ (m : ENat) + (logSlack (2 * cW + cLow) (4 * k) : ENat) :=
      hLowE.trans (by gcongr)
    exact_mod_cast h
  have hmin2 : min CB (m - 2 * k) ≤
      cTot * M + logSlack (cTot * cW + cSlk) (4 * k) + c4 * M +
        logSlack cLin (4 * k) := by
    rwa [hy] at hmin
  have hs1_slack : logSlack (2 * cW + cLow) (4 * k) ≤ logSlack CS (4 * k) :=
    logSlack_mono_left (by rw [hCSdef]; omega) _
  have hsum_slack : logSlack (2 * cW + cLow) (4 * k) +
      logSlack (cTot * cW + cSlk) (4 * k) + logSlack cLin (4 * k) =
      logSlack CS (4 * k) := by
    rw [hCSdef]; unfold logSlack; ring
  have hcon2 : 2 * (cTot * M + c4 * M + M) < k := by
    have hexp : 2 * (cTot * M + c4 * M + M) = 2 * (cTot + c4 + 1) * M := by ring
    omega
  omega

end Kolmogorov
