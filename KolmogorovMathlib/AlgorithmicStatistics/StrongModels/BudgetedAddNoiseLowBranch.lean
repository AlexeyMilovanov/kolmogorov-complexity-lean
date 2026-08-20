import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseFibreIndex
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseHeavySymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseRankIndex
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MinimalModelBounds
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseGain
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedSectionThree
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedAddNoiseArith

/-!
# Budgeted low-coordinate add-noise branch

This file isolates the exact budget-scale analogue of
`inPlainDescriptionProfile_fst_of_pair_model`: every logarithmic overhead is
measured against the complexity budget `baseBudget` and the noise length
`l(y)`, never against the length of `x` or the size coordinate `j`.

The branch splits on the size of the fibre of the pair model `B` over `x`.

* If the fibre is at least `l(y)` long, the heavy truncation of `B` at
  threshold `l(y)` is already the required model of `x`; this is proved
  outright in `inPlainDescriptionProfile_fst_of_heavy_fibre_budgeted`, its only
  slack being the `O(log l(y))` advice for the threshold.
* Otherwise the truncation is taken at the actual fibre threshold `F < l(y)`,
  and the fibre deficit `l(y) - F` is paid by conditional randomness of `y`:
  `l(y) ≤ epsilon + C([H] | x) + C(B | [H]) + F + O(log(baseBudget + l(y)))`.
  The term `C(B | [H])` is recovered from the finite-set symmetry of
  information for the heavy truncation, and the term `C([H] | x)` from a
  budget-scale compression of `H`, packaged as
  `BudgetedConditionalCompressionStatement`.  Chunking the result back down by
  the deficit (which is at most `l(y)`, hence budget-scale) makes both
  conditional terms cancel and leaves exactly the randomness loss `epsilon`.

`inPlainDescriptionProfile_fst_of_pair_model_budgeted_core` carries out this
reduction in full.  The exact conclusion is retained below as the unproved
proposition-valued target `BudgetedPairProjectionStatement`; it follows from
`BudgetedConditionalCompressionStatement`, but that generic compression is
only a research reduction and is not asserted.  The proved §3 route (many
descriptions of `x` with the parameters of `H`, plus improving descriptions) is available as
`inPlainDescriptionProfile_of_condK_compression_size_scale`, but it pays
`O(log (C(H) + log #H))`, and the residual dependence on the size coordinate is
precisely what the length-scale argument removes.

Consequently the branch is proved outright whenever the size coordinate also
fits inside the budget:
`inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le` needs no
unproved input.  Only the regime `j ≫ baseBudget` is open.

The theorem below is a reverse ordinary-profile projection.  Even once proved,
it does not by itself imply the forward stochasticity transport
`BudgetedRandomNoiseTransportStatement`; a separate, source-faithful bridge is
still required.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- A charge-balanced multiplicity witness can be passed through the
length-free complexity-drop theorem without leaving the charge in the final
complexity coordinate.  This is the proved final arithmetic/combinatorial step
required from the still-missing stratified multiplicity construction. -/
theorem inDescriptionProfile_of_charged_many_length_free
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x : BitString) (i j gain charge loss : Nat),
      ManyIJDescriptions U x (i + charge) j (gain + charge - loss) →
      gain + charge - loss ≤ i + charge →
      InDescriptionProfile U x
        (i - gain + loss + logSlack c (i + charge + j))
        (j + logSlack c (i + charge + j)) := by
  obtain ⟨c, hdrop⟩ := improvingDescriptionsComplexity_length_free U hU
  refine ⟨c, ?_⟩
  intro x i j gain charge loss hmany hle
  have hprofile := hdrop x (i + charge) j
    (gain + charge - loss) hmany hle
  refine hprofile.mono_i ?_
  have hcancel := addNoise_charge_cancels i charge gain loss
  simpa only [Nat.add_assoc] using
    Nat.add_le_add_right hcancel (logSlack c (i + charge + j))

/-- **Heavy-fibre case of the budgeted fibre projection.**  If the fibre of the
pair model `B` over `x` already has logarithmic cardinality at least `l(y)`,
then the heavy truncation of `B` at threshold `l(y)` is itself the required
model of `x`: it contains `x`, its plain set complexity exceeds that of `B` by
at most `O(log l(y))`, and its log-cardinality is at most `j - l(y) + 1`.

Note that the whole slack is logarithmic in the *noise length* `l(y)` alone —
neither the size coordinate `j` nor the length of `x` occurs — so this is a
genuinely budget-scale statement. -/
theorem inPlainDescriptionProfile_fst_of_heavy_fibre_budgeted
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (B : Finset BitString) (hB : B.Nonempty) (x y : BitString)
        (i j : Nat),
      pairCode x y ∈ B →
      plainSetComplexity V B hB ≤ (i : ENat) →
      B.card ≤ 2 ^ j →
      y.length ≤ finiteSetLogCard (finiteSetFstFiber B x) →
      InPlainDescriptionProfile V x
        (i + logSlack c y.length) (j - y.length + logSlack c y.length) := by
  obtain ⟨c, hc⟩ := finiteSetFstHeavyTruncation_plainSetComplexity_le V hV
  refine ⟨c + 1, ?_⟩
  intro B hB x y i j hpair hcompl hcard hheavy
  have hslack : logSlack c y.length + 1 ≤ logSlack (c + 1) y.length := by
    unfold logSlack
    have hexp : (c + 1) * (Nat.bits y.length).length + (c + 1) =
        (c * (Nat.bits y.length).length + c) + ((Nat.bits y.length).length + 1) := by
      ring
    omega
  set H := finiteSetFstHeavyTruncation B y.length with hH
  have hxH : x ∈ H := finiteSetFstHeavyTruncation_mem hpair hheavy
  have hHne : H.Nonempty := ⟨x, hxH⟩
  refine ⟨H, hHne, hxH, ?_, ?_⟩
  · calc
      plainSetComplexity V H hHne
          ≤ plainSetComplexity V B hB + (logSlack c y.length : ENat) :=
            hc B hB y.length hHne
      _ ≤ (i : ENat) + (logSlack c y.length : ENat) := by gcongr
      _ = ((i + logSlack c y.length : Nat) : ENat) := by push_cast; ring
      _ ≤ ((i + logSlack (c + 1) y.length : Nat) : ENat) := by
            exact_mod_cast Nat.add_le_add_left (by omega : logSlack c y.length ≤
              logSlack (c + 1) y.length) i
  · have hlogB : finiteSetLogCard B ≤ j := (finiteSetLogCard_le_iff B j).mpr hcard
    refine le_trans (finiteSetFstHeavyTruncation_card_le B y.length) ?_
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Conditional compression of a model, at the size scale.**  A model `H` of
`x` of plain set complexity at most `iH` and log-size at most `j1` can be
replaced by a model of `x` whose complexity drops by the full conditional
complexity `C([H] | x)`, at the price of a slack logarithmic in the *visible
parameters* `iH + j1`.

This is exactly `BudgetedConditionalCompressionStatement` except that the slack
is measured against `iH + j1` instead of a complexity budget: the multiplicity
family used to compress `H` is indexed by the size coordinate `j1`, which has
to be encoded.  Removing that dependence is precisely the remaining gap in the
budgeted low add-noise branch. -/
theorem inPlainDescriptionProfile_of_condK_compression_size_scale
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (H : Finset BitString) (hH : H.Nonempty) (x : BitString)
        (iH j1 g : Nat),
      x ∈ H →
      plainSetComplexity V H hH ≤ (iH : ENat) →
      H.card ≤ 2 ^ j1 →
      condK V (codedUniformOn H hH).code x = (g : ENat) →
      InPlainDescriptionProfile V x
        (iH - g + logSlack c (iH + j1)) (j1 + logSlack c (iH + j1)) := by
  obtain ⟨cPre, hPre⟩ :=
    setComplexity_le_plainSetComplexity_of_logSlack_budget V U hV hU
  obtain ⟨cRank, hRank⟩ := condK_description_code_le_of_not_many V U hV hU
  obtain ⟨cDrop, hDrop⟩ := improvingDescriptionsComplexity_length_free U hU
  obtain ⟨cBridge, hBridge⟩ := inPlainDescriptionProfile_of_inDescriptionProfile V U hV hU
  obtain ⟨bPre, hbPre⟩ := logSlack_le_add_const cPre
  obtain ⟨cRank2, hcRank2⟩ := logSlack_linear_bound cRank 2 bPre
  obtain ⟨cDrop2, hcDrop2⟩ := logSlack_linear_bound cDrop 2 bPre
  refine ⟨cPre + cRank2 + cDrop2 + cBridge + 1, ?_⟩
  intro H hH x iH j1 g hxH hcompl hHcard hg
  set c := cPre + cRank2 + cDrop2 + cBridge + 1 with hc
  -- Prefix set complexity of `H`.
  have hpre := hPre H hH iH hcompl
  have hi1le0 : setComplexity U H hH ≤ ((iH + logSlack cPre iH : Nat) : ENat) := by
    refine hpre.trans ?_
    calc
      plainSetComplexity V H hH + (logSlack cPre iH : ENat)
          ≤ (iH : ENat) + (logSlack cPre iH : ENat) := by gcongr
      _ = ((iH + logSlack cPre iH : Nat) : ENat) := by push_cast; ring
  have hi1fin : setComplexity U H hH ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hi1le0
  set i1 := (setComplexity U H hH).toNat with hi1def
  have hi1 : setComplexity U H hH = (i1 : ENat) := (ENat.coe_toNat hi1fin).symm
  have hi1le : i1 ≤ iH + logSlack cPre iH := by
    have h : (i1 : ENat) ≤ ((iH + logSlack cPre iH : Nat) : ENat) := by
      rw [← hi1]; exact hi1le0
    exact_mod_cast h
  -- The multiplicity of `x` at the parameters of `H`.
  set fam := (descriptionsWithComplexityLeAndSizeLe U i1 j1).filter (fun S => x ∈ S)
    with hfam
  have hHfam : H ∈ fam := by
    rw [hfam, Finset.mem_filter]
    refine ⟨?_, hxH⟩
    rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
    exact ⟨mem_descriptionsWithComplexityLe_of_complexity hH (le_of_eq hi1), hHcard⟩
  have hcntpos : 0 < fam.card := Finset.card_pos.mpr ⟨H, hHfam⟩
  set k := Nat.log 2 fam.card with hkdef
  have hk1 : 2 ^ k ≤ fam.card := Nat.pow_log_le_self 2 (by omega)
  have hk2 : fam.card < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hmany : ManyIJDescriptions U x i1 j1 k := hk1
  have hnotmany : ¬ ManyIJDescriptions U x i1 j1 (k + 1) := by
    rw [ManyIJDescriptions, not_le]
    exact hk2
  -- The rank bound: `H` is cheap given `x` only through the multiplicity.
  have hrank := hRank H hH x i1 j1 (k + 1) hxH hi1 hHcard hnotmany
  have hgle : g ≤ k + 1 + logSlack cRank (i1 + j1) := by
    rw [hg] at hrank
    exact_mod_cast hrank
  have hkle : k ≤ i1 + 1 := hmany.le_succ
  -- The complexity drop provided by the multiplicity.
  set k' := min k i1 with hk'
  have hk'k : k' ≤ k := min_le_left _ _
  have hk'i : k' ≤ i1 := min_le_right _ _
  have hk'cases : k' = k ∨ k' = i1 := by
    rcases le_total k i1 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hmany' : ManyIJDescriptions U x i1 j1 k' := hmany.mono_k hk'k
  have hdrop := hDrop x i1 j1 k' hmany' hk'i
  have hplain := hBridge x (i1 - k' + logSlack cDrop (i1 + j1))
    (j1 + logSlack cDrop (i1 + j1)) hdrop
  -- Slack bookkeeping.
  have hbPre' : logSlack cPre iH ≤ iH + bPre := hbPre iH
  have hsum : i1 + j1 ≤ 2 * (iH + j1) + bPre := by omega
  have hRankFold : logSlack cRank (i1 + j1) ≤ logSlack cRank2 (iH + j1) :=
    le_trans (logSlack_mono_right cRank hsum) (hcRank2 (iH + j1))
  have hDropFold : logSlack cDrop (i1 + j1) ≤ logSlack cDrop2 (iH + j1) :=
    le_trans (logSlack_mono_right cDrop hsum) (hcDrop2 (iH + j1))
  have hPreFold : logSlack cPre iH ≤ logSlack cPre (iH + j1) :=
    logSlack_mono_right cPre (by omega)
  have hslackSum :
      logSlack cPre (iH + j1) + logSlack cRank2 (iH + j1) +
          logSlack cDrop2 (iH + j1) + (cBridge + 1) ≤ logSlack c (iH + j1) := by
    have h1 : logSlack cPre (iH + j1) + logSlack cRank2 (iH + j1) +
        logSlack cDrop2 (iH + j1) = logSlack (cPre + cRank2 + cDrop2) (iH + j1) := by
      unfold logSlack; ring
    have h2 := logSlack_add_const_le (cPre + cRank2 + cDrop2) (cBridge + 1) (iH + j1)
    have h3 : logSlack (cPre + cRank2 + cDrop2 + (cBridge + 1)) (iH + j1) ≤
        logSlack c (iH + j1) := logSlack_mono_left (by omega) _
    omega
  refine (hplain.mono_i ?_).mono_j ?_
  · omega
  · omega

/-- **Budget-scale conditional compression of a finite model.**  A model `H` of
`x` of plain set complexity at most `iH` and log-size at most `j1` which is
cheap given `x`, say `C([H] | x) ≤ g`, should be replaceable by a model of `x`
of complexity `iH - g` and log-size `j1`, up to a slack logarithmic in a
complexity budget dominating `iH`.

This is the *single* remaining input of the budgeted low add-noise branch: the
reduction `inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_conditionalCompression`
below derives the whole branch from it.  At the length scale the statement is
classical (many descriptions of `x` with the parameters of `H`, plus the
improving-descriptions theorem); the open point is that the proved route pays
`O(log (iH + j1))`, i.e. it also charges the *size* coordinate, which here may
be exponentially larger than the complexity budget. -/
def BudgetedConditionalCompressionStatement (V : Map) : Prop :=
  ∃ c : Nat, ∀ (H : Finset BitString) (hH : H.Nonempty) (x : BitString)
      (iH j1 g budget : Nat),
    x ∈ H →
    plainSetComplexity V H hH ≤ (iH : ENat) →
    H.card ≤ 2 ^ j1 →
    condK V (codedUniformOn H hH).code x = (g : ENat) →
    iH ≤ budget →
    InPlainDescriptionProfile V x
      (iH - g + logSlack c budget) (j1 + logSlack c budget)

/-- **Core of the budgeted low branch.**  The compression input is taken as an
explicit hypothesis, which is only ever used at size parameters bounded by
`budget + jCap`; correspondingly the conclusion is restricted to
`j ≤ baseBudget + jCap`.  Taking `jCap := j` recovers the unrestricted branch,
and `jCap := 0` the small-size regime.

The argument splits on whether the fibre of the pair model over `x` is at
least `l(y)` long:

* heavy fibre: `inPlainDescriptionProfile_fst_of_heavy_fibre_budgeted` already
  gives the conclusion, with a slack logarithmic in `l(y)` alone;
* light fibre: the heavy truncation `H` at the actual fibre threshold `F`
  satisfies `C(H) + C(B | [H]) ≤ C(B) + O(log(baseBudget + l(y)))` (finite-set
  symmetry of information) and `l(y) ≤ epsilon + C([H] | x) + C(B | [H]) + F +
  O(log(baseBudget + l(y)))` (conditional randomness of `y`).  Compressing `H`
  by `C([H] | x)` and chunking the result down by the fibre deficit
  `l(y) - F ≤ l(y)` makes both conditional terms cancel, leaving exactly the
  randomness loss `epsilon`.

Every slack produced here is logarithmic in `baseBudget` and `l(y)` only. -/
theorem inPlainDescriptionProfile_fst_of_pair_model_budgeted_core
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (cCC : Nat) :
    ∃ c : Nat, ∀ (jCap : Nat),
      (∀ (H : Finset BitString) (hH : H.Nonempty) (x : BitString)
          (iH j1 g budget : Nat),
        x ∈ H →
        plainSetComplexity V H hH ≤ (iH : ENat) →
        H.card ≤ 2 ^ j1 →
        condK V (codedUniformOn H hH).code x = (g : ENat) →
        iH ≤ budget →
        j1 ≤ budget + jCap →
        InPlainDescriptionProfile V x
          (iH - g + logSlack cCC budget) (j1 + logSlack cCC budget)) →
      ∀ (x y : BitString) (epsilon i j baseBudget : Nat),
        InPlainDescriptionProfile V (pairCode x y) i j →
        (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
        i ≤ baseBudget →
        j ≤ baseBudget + jCap →
        InPlainDescriptionProfile V x
          (i + epsilon + logSlack c baseBudget + logSlack c y.length)
          (j - y.length + logSlack c baseBudget + logSlack c y.length) := by
  obtain ⟨cHeavy, hHeavy⟩ := inPlainDescriptionProfile_fst_of_heavy_fibre_budgeted V hV
  obtain ⟨cSym, hSym⟩ :=
    finiteSetFstHeavyTruncation_plainSetComplexity_symmetry V U hV hU
  obtain ⟨cFib, hFib⟩ := finiteSetFstFiber_logCard_lower_of_random V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  obtain ⟨cShift, hShift⟩ := inPlainDescriptionProfile_shift V hV
  obtain ⟨bSym, hbSym⟩ := logSlack_le_add_const cSym
  obtain ⟨cFib2, hcFib2⟩ := logSlack_linear_bound cFib 2 (bSym + cCond + 1)
  obtain ⟨cCC2, hcCC2⟩ := logSlack_linear_bound cCC 2 (bSym + cCond + 1)
  obtain ⟨bCC2, hbCC2⟩ := logSlack_le_add_const cCC2
  obtain ⟨cShift2, hcShift2⟩ := logSlack_linear_bound cShift 2 (1 + bCC2)
  refine ⟨cHeavy + cSym + cFib2 + 2 * cCC2 + cShift2 + cCond + 1, ?_⟩
  intro jCap hCCb x y epsilon i j baseBudget hprofile hrandom hbudget hjcap
  set c := cHeavy + cSym + cFib2 + 2 * cCC2 + cShift2 + cCond + 1 with hc
  obtain ⟨B, hB, hpair, hcompl, hcard⟩ := hprofile
  by_cases hheavy : y.length ≤ finiteSetLogCard (finiteSetFstFiber B x)
  · -- Heavy fibre: the heavy truncation of `B` at threshold `l(y)` is already
    -- the required model of `x`.
    have hle : logSlack cHeavy y.length ≤ logSlack c y.length :=
      logSlack_mono_left (by omega) _
    exact ((hHeavy B hB x y i j hpair hcompl hcard hheavy).mono_i (by omega)).mono_j
      (by omega)
  · -- Light fibre.
    push_neg at hheavy
    set F := finiteSetLogCard (finiteSetFstFiber B x) with hF
    have hxH : x ∈ finiteSetFstHeavyTruncation B F :=
      finiteSetFstHeavyTruncation_mem hpair le_rfl
    set H := finiteSetFstHeavyTruncation B F with hH
    have hHne : H.Nonempty := ⟨x, hxH⟩
    set M := baseBudget + y.length with hM
    have hlogB : finiteSetLogCard B ≤ j := (finiteSetLogCard_le_iff B j).mpr hcard
    have hfibsub : finiteSetFstFiber B x ⊆ B := Finset.filter_subset _ _
    have hFj : F ≤ j :=
      le_trans (finiteSetLogCard_mono (Finset.card_le_card hfibsub)) hlogB
    have hcomplM : plainSetComplexity V B hB ≤ (M : ENat) :=
      hcompl.trans (by exact_mod_cast (by omega : i ≤ M))
    have hsym := hSym B hB F M hHne hcomplM (by omega)
    -- Exact natural values of the three complexities involved.
    have hHfin : plainSetComplexity V H hHne ≠ ⊤ :=
      condK_ne_top_of_optimal V hV _ _
    set iH := (plainSetComplexity V H hHne).toNat with hiHdef
    have hiH : plainSetComplexity V H hHne = (iH : ENat) := (ENat.coe_toNat hHfin).symm
    have hqfin : condK V (codedUniformOn B hB).code (codedUniformOn H hHne).code ≠ ⊤ :=
      condK_ne_top_of_optimal V hV _ _
    set q := (condK V (codedUniformOn B hB).code (codedUniformOn H hHne).code).toNat
      with hqdef
    have hq : condK V (codedUniformOn B hB).code (codedUniformOn H hHne).code = (q : ENat) :=
      (ENat.coe_toNat hqfin).symm
    have hgfin : condK V (codedUniformOn H hHne).code x ≠ ⊤ :=
      condK_ne_top_of_optimal V hV _ _
    set g := (condK V (codedUniformOn H hHne).code x).toNat with hgdef
    have hg : condK V (codedUniformOn H hHne).code x = (g : ENat) :=
      (ENat.coe_toNat hgfin).symm
    -- Finite-set symmetry of information, in natural numbers.
    have hiHq : iH + q ≤ i + logSlack cSym M := by
      rw [hiH, hq] at hsym
      have hcast : ((iH + q : Nat) : ENat) ≤ ((i + logSlack cSym M : Nat) : ENat) := by
        refine le_trans (le_of_eq (by push_cast; ring)) (hsym.trans ?_)
        calc
          plainSetComplexity V B hB + (logSlack cSym M : ENat)
              ≤ (i : ENat) + (logSlack cSym M : ENat) := by gcongr
          _ = ((i + logSlack cSym M : Nat) : ENat) := by push_cast; ring
      exact_mod_cast hcast
    -- Both conditional complexities are budget-scale.
    have hgle : g ≤ iH + cCond := by
      have h := hCond (codedUniformOn H hHne).code x
      rw [hg] at h
      have h' : ((g : Nat) : ENat) ≤ ((iH + cCond : Nat) : ENat) := by
        refine h.trans ?_
        have hplain : plainK V (codedUniformOn H hHne).code = (iH : ENat) := hiH
        rw [hplain]
        push_cast
        exact le_rfl
      exact_mod_cast h'
    have hqle : q ≤ i + cCond := by
      have h := hCond (codedUniformOn B hB).code (codedUniformOn H hHne).code
      rw [hq] at h
      have h' : ((q : Nat) : ENat) ≤ ((i + cCond : Nat) : ENat) := by
        refine h.trans ?_
        have hplain : plainK V (codedUniformOn B hB).code ≤ (i : ENat) := hcompl
        calc
          plainK V (codedUniformOn B hB).code + (cCond : ENat)
              ≤ (i : ENat) + (cCond : ENat) := by gcongr
          _ = ((i + cCond : Nat) : ENat) := by push_cast; ring
      exact_mod_cast h'
    set N3 := M + logSlack cSym M + cCond + 1 with hN3
    have hgN3 : g ≤ N3 := by omega
    have hqN3 : q ≤ N3 := by omega
    -- Conditional randomness of `y` bounds the fibre deficit.
    have hfib := hFib B H hB hHne x y epsilon g q N3 hpair hrandom
      (le_of_eq hg) (le_of_eq hq) hqN3 hgN3
    -- The heavy truncation is small.
    have hHcard : H.card ≤ 2 ^ (j - F + 1) :=
      le_trans (finiteSetFstHeavyTruncation_card_le B F)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    -- Compress the heavy truncation by its conditional complexity given `x`.
    have hprof := hCCb H hHne x iH (j - F + 1) g N3 hxH (le_of_eq hiH) hHcard
      hg (by omega) (by omega)
    set L := logSlack cCC N3 with hL
    set t := (y.length - F) + 1 + L with ht
    have hchunk := hShift x (iH - g + L) (j - F + 1 + L) t hprof
    -- Slack bookkeeping: everything is logarithmic in `baseBudget` and `l(y)`.
    have hSymM : logSlack cSym M ≤ M + bSym := hbSym M
    have hN3le : N3 ≤ 2 * M + (bSym + cCond + 1) := by omega
    have hFibFold : logSlack cFib N3 ≤ logSlack cFib2 M :=
      le_trans (logSlack_mono_right cFib hN3le) (hcFib2 M)
    have hLfold : L ≤ logSlack cCC2 M :=
      le_trans (logSlack_mono_right cCC hN3le) (hcCC2 M)
    have hCC2b : logSlack cCC2 M ≤ M + bCC2 := hbCC2 M
    have htle : t ≤ 2 * M + (1 + bCC2) := by omega
    have hShiftFold : logSlack cShift t ≤ logSlack cShift2 M :=
      le_trans (logSlack_mono_right cShift htle) (hcShift2 M)
    have hslackSum :
        logSlack cSym M + logSlack cFib2 M + 2 * logSlack cCC2 M +
            logSlack cShift2 M + cCond + 1 ≤
          logSlack c baseBudget + logSlack c y.length := by
      set A := cSym + cFib2 + 2 * cCC2 + cShift2 with hA
      have h1 : logSlack cSym M + logSlack cFib2 M + 2 * logSlack cCC2 M +
          logSlack cShift2 M = logSlack A M := by
        unfold logSlack
        rw [hA]
        ring
      have h2 : logSlack A M ≤ logSlack A baseBudget + logSlack A y.length :=
        logSlack_add_le A baseBudget y.length
      have h3 : logSlack A baseBudget + (cCond + 1) ≤ logSlack c baseBudget :=
        le_trans (logSlack_add_const_le A (cCond + 1) baseBudget)
          (logSlack_mono_left (by omega) baseBudget)
      have h4 : logSlack A y.length ≤ logSlack c y.length :=
        logSlack_mono_left (by omega) y.length
      omega
    refine (hchunk.mono_i ?_).mono_j ?_
    · omega
    · omega

/-- **The budgeted low branch from the unrestricted conditional-compression
statement.**  Instantiating the core reduction at `jCap := j` makes its size
side condition vacuous. -/
theorem inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_conditionalCompression
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hCC : BudgetedConditionalCompressionStatement V) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon i j baseBudget : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      i ≤ baseBudget →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c baseBudget + logSlack c y.length)
        (j - y.length + logSlack c baseBudget + logSlack c y.length) := by
  obtain ⟨cCC, hCCb⟩ := hCC
  obtain ⟨c, hc⟩ := inPlainDescriptionProfile_fst_of_pair_model_budgeted_core V U hV hU cCC
  refine ⟨c, fun x y epsilon i j baseBudget hprofile hrandom hbudget => ?_⟩
  exact hc j (fun H hH x' iH j1 g budget hx' hcompl hcard hg hiH _ =>
      hCCb H hH x' iH j1 g budget hx' hcompl hcard hg hiH)
    x y epsilon i j baseBudget hprofile hrandom hbudget (by omega)

/-- **The budgeted low branch in the small-size regime.**  If the size
coordinate of the pair model also fits inside the complexity budget, the branch
is proved outright: the size-scale conditional compression
`inPlainDescriptionProfile_of_condK_compression_size_scale` is then already
budget-scale.  Only the regime where `j` is much larger than `baseBudget`
remains open. -/
theorem inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon i j baseBudget : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      i ≤ baseBudget →
      j ≤ baseBudget →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c baseBudget + logSlack c y.length)
        (j - y.length + logSlack c baseBudget + logSlack c y.length) := by
  obtain ⟨cSize, hSize⟩ := inPlainDescriptionProfile_of_condK_compression_size_scale V U hV hU
  obtain ⟨cSize2, hcSize2⟩ := logSlack_linear_bound cSize 2 0
  obtain ⟨c, hc⟩ := inPlainDescriptionProfile_fst_of_pair_model_budgeted_core V U hV hU cSize2
  refine ⟨c, fun x y epsilon i j baseBudget hprofile hrandom hbudget hjbudget => ?_⟩
  refine hc 0 (fun H hH x' iH j1 g budget hx' hcompl hcard hg hiH hj1 => ?_)
    x y epsilon i j baseBudget hprofile hrandom hbudget (by omega)
  have hfold : logSlack cSize (iH + j1) ≤ logSlack cSize2 budget := by
    refine le_trans (logSlack_mono_right cSize ?_) (hcSize2 budget)
    omega
  exact ((hSize H hH x' iH j1 g hx' hcompl hcard hg).mono_i (by omega)).mono_j (by omega)

/-- **Budgeted fibre projection of a pair model.**  This is the exact
low-coordinate target after the charged-stratum multiplicity/compression
bridge described in the module documentation has been proved.

The generic reduction
`budgetedPairProjection_of_conditionalCompression` derives it from
`BudgetedConditionalCompressionStatement V`.  The direct route required by the
chapter plan instead goes through `BudgetedPairProjectionManyStatement`, whose
certificate has exactly the coordinates consumed by the length-free
complexity-drop theorem.  Neither proposition is asserted here. -/
def BudgetedPairProjectionStatement (V : Map) : Prop :=
  ∃ c : Nat, ∀ (x y : BitString) (epsilon i j baseBudget : Nat),
    InPlainDescriptionProfile V (pairCode x y) i j →
    (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
    i ≤ baseBudget →
    InPlainDescriptionProfile V x
      (i + epsilon + logSlack c baseBudget + logSlack c y.length)
      (j - y.length + logSlack c baseBudget + logSlack c y.length)

/-- **Direct multiplicity target for the budgeted pair projection.**  For the
fixed constants of the length-free complexity-drop theorem and the
prefix-to-plain bridge, produce a genuine `ManyIJDescriptions` certificate
whose two displayed inequalities already absorb both costs into the visible
budgets `baseBudget` and `y.length`.

This is the exact consumer-shaped obligation for the mandated
truncation/multiplicity route.  In particular, neither `j` nor `x.length`
occurs in either final slack term. -/
def BudgetedPairProjectionManyStatement (V U : Map) : Prop :=
  ∀ cDrop cBridge : Nat, ∃ c : Nat,
    ∀ (x y : BitString) (epsilon i j baseBudget : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      i ≤ baseBudget →
      ∃ I J K : Nat,
        ManyIJDescriptions U x I J K ∧
        K ≤ I ∧
        I - K + logSlack cDrop (I + J) + cBridge ≤
          i + epsilon + logSlack c baseBudget + logSlack c y.length ∧
        J + logSlack cDrop (I + J) ≤
          j - y.length + logSlack c baseBudget + logSlack c y.length

theorem budgetedPairProjection_of_conditionalCompression
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hCond : BudgetedConditionalCompressionStatement V) :
    BudgetedPairProjectionStatement V := by
  exact inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_conditionalCompression
    V U hV hU hCond

/-- A certificate satisfying `BudgetedPairProjectionManyStatement` proves the
exact budgeted pair projection by the length-free complexity drop followed by
the constant-cost prefix-to-plain bridge. -/
theorem budgetedPairProjection_of_many
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hMany : BudgetedPairProjectionManyStatement V U) :
    BudgetedPairProjectionStatement V := by
  obtain ⟨cDrop, hDrop⟩ := improvingDescriptionsComplexity_length_free U hU
  obtain ⟨cBridge, hBridge⟩ :=
    inPlainDescriptionProfile_of_inDescriptionProfile V U hV hU
  obtain ⟨c, hMany⟩ := hMany cDrop cBridge
  refine ⟨c, ?_⟩
  intro x y epsilon i j baseBudget hProfile hRandom hBudget
  obtain ⟨I, J, K, hDescriptions, hKI, hComplexity, hSize⟩ :=
    hMany x y epsilon i j baseBudget hProfile hRandom hBudget
  have hPrefix := hDrop x I J K hDescriptions hKI
  have hPlain := hBridge x
    (I - K + logSlack cDrop (I + J))
    (J + logSlack cDrop (I + J)) hPrefix
  exact (hPlain.mono_i hComplexity).mono_j hSize

end Kolmogorov
