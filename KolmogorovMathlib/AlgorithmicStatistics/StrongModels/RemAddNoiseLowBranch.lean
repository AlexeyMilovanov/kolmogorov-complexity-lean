import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseFibreIndex
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseHeavySymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseRankIndex
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MinimalModelBounds
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation

/-!
# Projecting a model of a noisy pair to a model of its first coordinate

This file proves the combinatorial heart of the low-coordinate branch of VS40
`rem:add-noise`: if `B` is an ordinary plain `(i, j)`-model of `pairCode x y`
and `y` is conditionally `epsilon`-random given `x`, then `x` has an ordinary
plain model of complexity `i + epsilon + O(log N)` and log-size
`j - |y| + O(log N)`.

The argument combines four ingredients.

* The *heavy truncation* `H` of `B` at the log-size `F` of the fibre of `B`
  over `x` is a model of `x` of log-size `log #B - F` and complexity at most
  `C(B) - C(B | [H]) + O(log N)` (finite-set symmetry of information,
  `finiteSetFstHeavyTruncation_plainSetComplexity_symmetry`).
* Conditional randomness of `y` forces the fibre to be large:
  `|y| ≤ epsilon + C([H] | x) + C(B | [H]) + F + O(log N)`
  (`finiteSetFstFiber_logCard_lower_of_random`).
* `C([H] | x)` is bounded by the logarithm of the number of descriptions of `x`
  with the parameters of `H` (`condK_description_code_le_of_not_many`).
* That same number of descriptions produces a description of `x` whose
  complexity is smaller by exactly that logarithm
  (`exists_description_smaller_complexity_of_many_logSlack`).

Chunking the resulting description down to the target log-size
(`inPlainDescriptionProfile_shift`) makes the two conditional terms cancel, and
only the randomness loss `epsilon` remains.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- **Fibre projection of a pair model.**  An ordinary plain `(i, j)`-model of
`pairCode x y`, together with conditional `epsilon`-randomness of `y` given `x`,
yields an ordinary plain model of `x` of complexity `i + epsilon + O(log N)` and
log-size `j - |y| + O(log N)`, where `N` bounds `|x| + |y|`, `i` and `j`. -/
theorem inPlainDescriptionProfile_fst_of_pair_model
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon i j N : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      x.length + y.length ≤ N →
      i ≤ N →
      j ≤ N →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c N) (j - y.length + logSlack c N) := by
  obtain ⟨cSym, hSym⟩ :=
    finiteSetFstHeavyTruncation_plainSetComplexity_symmetry V U hV hU
  obtain ⟨cPre, hPre⟩ :=
    setComplexity_le_plainSetComplexity_of_logSlack_budget V U hV hU
  obtain ⟨cRank, hRank⟩ := condK_description_code_le_of_not_many V U hV hU
  obtain ⟨cFib, hFibLower⟩ := finiteSetFstFiber_logCard_lower_of_random V hV
  obtain ⟨cDrop, hDrop⟩ := exists_description_smaller_complexity_of_many_logSlack U hU
  obtain ⟨cBridge, hBridge⟩ := inPlainDescriptionProfile_of_inDescriptionProfile V U hV hU
  obtain ⟨cShift, hShift⟩ := inPlainDescriptionProfile_shift V hV
  -- Fold every auxiliary slack argument back into a slack in `N`.
  obtain ⟨bSym, hbSym⟩ := logSlack_le_add_const cSym
  obtain ⟨cPre2, hcPre2⟩ := logSlack_linear_bound cPre 2 bSym
  obtain ⟨bPre2, hbPre2⟩ := logSlack_le_add_const cPre2
  obtain ⟨cRank2, hcRank2⟩ := logSlack_linear_bound cRank 4 (bSym + bPre2 + 1)
  obtain ⟨bRank2, hbRank2⟩ := logSlack_le_add_const cRank2
  obtain ⟨cDrop2, hcDrop2⟩ := logSlack_linear_bound cDrop 5 (bSym + bPre2 + 1)
  obtain ⟨cFib2, hcFib2⟩ :=
    logSlack_linear_bound cFib 4 (bSym + bPre2 + 2 + bRank2 + bSym)
  refine ⟨cSym + cPre2 + cRank2 + cDrop2 + cFib2 + cShift + cBridge + 2, ?_⟩
  intro x y epsilon i j N hprofile hrandom hlenN hiN hjN
  set c : Nat :=
    cSym + cPre2 + cRank2 + cDrop2 + cFib2 + cShift + cBridge + 2 with hc
  obtain ⟨B, hB, hpair, hcompl, hcard⟩ := hprofile
  set l := y.length with hl
  set F := finiteSetLogCard (finiteSetFstFiber B x) with hF
  set H := finiteSetFstHeavyTruncation B F with hH
  have hxH : x ∈ H := finiteSetFstHeavyTruncation_mem hpair le_rfl
  have hHne : H.Nonempty := ⟨x, hxH⟩
  -- Basic size bookkeeping.
  have hlogB : finiteSetLogCard B ≤ j := (finiteSetLogCard_le_iff B j).mpr hcard
  have hFj : F ≤ j := by
    refine le_trans ?_ hlogB
    refine finiteSetLogCard_mono ?_
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hlN : l ≤ N := by omega
  have hxlenN : x.length ≤ N := by omega
  -- The conditional complexity of `B` given the heavy truncation.
  have hqfin : condK V (codedUniformOn B hB).code (codedUniformOn H hHne).code ≠ ⊤ :=
    condK_ne_top_of_optimal V hV _ _
  set q := (condK V (codedUniformOn B hB).code (codedUniformOn H hHne).code).toNat with hqdef
  have hq : condK V (codedUniformOn B hB).code (codedUniformOn H hHne).code = (q : ENat) :=
    (ENat.coe_toNat hqfin).symm
  -- Finite-set symmetry of information for the heavy truncation.
  have hBN : plainSetComplexity V B hB ≤ (N : ENat) :=
    hcompl.trans (by exact_mod_cast hiN)
  have hsym := hSym B hB F N hHne hBN (by omega)
  have hHle : plainSetComplexity V H hHne ≤ ((i + logSlack cSym N : Nat) : ENat) := by
    refine le_trans le_self_add (hsym.trans ?_)
    calc
      plainSetComplexity V B hB + (logSlack cSym N : ENat)
          ≤ (i : ENat) + (logSlack cSym N : ENat) := by gcongr
      _ = ((i + logSlack cSym N : Nat) : ENat) := by push_cast; ring
  have hHfin : plainSetComplexity V H hHne ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hHle
  set iH := (plainSetComplexity V H hHne).toNat with hiHdef
  have hiH : plainSetComplexity V H hHne = (iH : ENat) := (ENat.coe_toNat hHfin).symm
  have hiHq : iH + q ≤ i + logSlack cSym N := by
    rw [hiH, hq] at hsym
    have hsym' : ((iH + q : Nat) : ENat) ≤ ((i + logSlack cSym N : Nat) : ENat) := by
      refine le_trans (le_of_eq ?_) (hsym.trans ?_)
      · push_cast; ring
      · calc
          plainSetComplexity V B hB + (logSlack cSym N : ENat)
              ≤ (i : ENat) + (logSlack cSym N : ENat) := by gcongr
          _ = ((i + logSlack cSym N : Nat) : ENat) := by push_cast; ring
    exact_mod_cast hsym'
  -- Prefix set complexity of the heavy truncation.
  have hHleN : plainSetComplexity V H hHne ≤ ((i + logSlack cSym N : Nat) : ENat) := hHle
  have hpre := hPre H hHne (i + logSlack cSym N) hHleN
  have hi1le0 : setComplexity U H hHne ≤
      ((iH + logSlack cPre (i + logSlack cSym N) : Nat) : ENat) := by
    refine hpre.trans ?_
    rw [hiH]
    push_cast
    exact le_rfl
  have hi1fin : setComplexity U H hHne ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hi1le0
  set i1 := (setComplexity U H hHne).toNat with hi1def
  have hi1 : setComplexity U H hHne = (i1 : ENat) := (ENat.coe_toNat hi1fin).symm
  have hSymBound : logSlack cSym N ≤ N + bSym := hbSym N
  have hPreFold : logSlack cPre (i + logSlack cSym N) ≤ logSlack cPre2 N := by
    refine le_trans (logSlack_mono_right cPre ?_) (hcPre2 N)
    omega
  have hi1le : i1 ≤ iH + logSlack cPre2 N := by
    have h : (i1 : ENat) ≤ ((iH + logSlack cPre (i + logSlack cSym N) : Nat) : ENat) := by
      rw [← hi1]; exact hi1le0
    have h' : i1 ≤ iH + logSlack cPre (i + logSlack cSym N) := by exact_mod_cast h
    omega
  have hPre2Bound : logSlack cPre2 N ≤ N + bPre2 := hbPre2 N
  have hiHle : iH ≤ i + logSlack cSym N := by omega
  have hi1N : i1 ≤ 3 * N + (bSym + bPre2) := by omega
  -- The size parameter of the heavy truncation.
  set j1 := finiteSetLogCard H with hj1def
  have hHcard : H.card ≤ 2 ^ j1 := (finiteSetLogCard_le_iff H j1).mp le_rfl
  have hj1le : j1 ≤ j - F + 1 := by
    have h : finiteSetLogCard H ≤ finiteSetLogCard B - F + 1 := by
      rw [hH]
      exact finiteSetFstHeavyTruncation_logCard_le B F
    omega
  have hj1N : j1 ≤ N + 1 := by omega
  -- The description family of `x` with the parameters of `H`.
  set fam := (descriptionsWithComplexityLeAndSizeLe U i1 j1).filter (fun S => x ∈ S) with hfam
  have hHfam : H ∈ fam := by
    rw [hfam, Finset.mem_filter]
    refine ⟨?_, hxH⟩
    rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
    exact ⟨mem_descriptionsWithComplexityLe_of_complexity hHne (le_of_eq hi1), hHcard⟩
  have hcntpos : 0 < fam.card := Finset.card_pos.mpr ⟨H, hHfam⟩
  set k := Nat.log 2 fam.card with hkdef
  have hk1 : 2 ^ k ≤ fam.card := Nat.pow_log_le_self 2 (by omega)
  have hk2 : fam.card < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hmany : ManyIJDescriptions U x i1 j1 k := hk1
  have hnotmany : ¬ ManyIJDescriptions U x i1 j1 (k + 1) := by
    rw [ManyIJDescriptions, not_le]
    exact hk2
  -- The heavy truncation is cheap given `x`.
  have hrank := hRank H hHne x i1 j1 (k + 1) hxH hi1 hHcard hnotmany
  have hgfin : condK V (codedUniformOn H hHne).code x ≠ ⊤ :=
    condK_ne_top_of_optimal V hV _ _
  set g := (condK V (codedUniformOn H hHne).code x).toNat with hgdef
  have hg : condK V (codedUniformOn H hHne).code x = (g : ENat) :=
    (ENat.coe_toNat hgfin).symm
  have hRankFold : logSlack cRank (i1 + j1) ≤ logSlack cRank2 N := by
    refine le_trans (logSlack_mono_right cRank ?_) (hcRank2 N)
    omega
  have hgle : g ≤ k + 1 + logSlack cRank2 N := by
    rw [hg] at hrank
    have h : g ≤ k + 1 + logSlack cRank (i1 + j1) := by exact_mod_cast hrank
    omega
  have hkle : k ≤ i1 + 1 := hmany.le_succ
  have hRank2Bound : logSlack cRank2 N ≤ N + bRank2 := hbRank2 N
  -- Conditional randomness forces a large fibre.
  set N3 := 4 * N + (bSym + bPre2 + 2 + bRank2 + bSym) with hN3
  have hqN3 : q ≤ N3 := by omega
  have hgN3 : g ≤ N3 := by omega
  have hfib := hFibLower B H hB hHne x y epsilon g q N3 hpair hrandom
    (le_of_eq hg) (le_of_eq hq) hqN3 hgN3
  have hFibFold : logSlack cFib N3 ≤ logSlack cFib2 N := by
    refine le_trans (logSlack_mono_right cFib ?_) (hcFib2 N)
    omega
  have hfibNat : l ≤ epsilon + g + q + F + logSlack cFib2 N := by
    have := hfib
    omega
  -- Many descriptions produce a simpler one.
  set k' := min k i1 with hk'
  have hmany' : ManyIJDescriptions U x i1 j1 k' := hmany.mono_k (min_le_left _ _)
  have hdrop := hDrop x x.length i1 j1 k' rfl hmany' (min_le_right _ _)
  have hDropFold : logSlack cDrop (x.length + i1 + j1) ≤ logSlack cDrop2 N := by
    refine le_trans (logSlack_mono_right cDrop ?_) (hcDrop2 N)
    omega
  set SD := logSlack cDrop (x.length + i1 + j1) with hSD
  have hplain : InPlainDescriptionProfile V x (i1 - k' + SD + cBridge) (j1 + SD) :=
    hBridge x (i1 - k' + SD) (j1 + SD) hdrop
  -- Chunk the description down to the target log-size.
  set s := l - F with hs
  have hchunk := hShift x (i1 - k' + SD + cBridge) (j1 + SD) s hplain
  have hShiftFold : logSlack cShift s ≤ logSlack cShift N :=
    logSlack_mono_right cShift (by omega)
  -- Collect the slack budget.
  have hslackSum :
      logSlack cSym N + logSlack cPre2 N + logSlack cRank2 N + logSlack cDrop2 N +
        logSlack cFib2 N + logSlack cShift N + cBridge + 2 ≤ logSlack c N := by
    have h1 : logSlack cSym N + logSlack cPre2 N + logSlack cRank2 N + logSlack cDrop2 N +
        logSlack cFib2 N + logSlack cShift N =
        logSlack (cSym + cPre2 + cRank2 + cDrop2 + cFib2 + cShift) N := by
      simp only [logSlack_add_const]
    have h2 : logSlack (cSym + cPre2 + cRank2 + cDrop2 + cFib2 + cShift) N + (cBridge + 2) ≤
        logSlack (cSym + cPre2 + cRank2 + cDrop2 + cFib2 + cShift + (cBridge + 2)) N :=
      logSlack_add_const_le _ _ _
    have h3 : logSlack (cSym + cPre2 + cRank2 + cDrop2 + cFib2 + cShift + (cBridge + 2)) N ≤
        logSlack c N := logSlack_mono_left (by omega) N
    omega
  refine (hchunk.mono_i ?_).mono_j ?_
  · -- complexity coordinate
    have hk'k : i1 - k' + k ≤ i1 + 1 := by omega
    omega
  · -- size coordinate
    omega

end Kolmogorov
