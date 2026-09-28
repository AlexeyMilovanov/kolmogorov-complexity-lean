import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock.Part03
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile
import KolmogorovMathlib.Restricted.EffectiveSelection.Part01

/-!
# Conditional complexity of a standard block and of the Omega prefix

A standard block of the completed bound-`m` list and the corresponding prefix of `Omega_m`
determine one another: one uniform partial-recursive selector reconstructs the block from the
prefix, another reconstructs the prefix from any member of the block.  The two conditional
bounds are `condK_standardBlock_le_omegaPrefix` and `condK_omegaPrefix_le_standardBlock`, their
combination is `standardBlock_omegaPrefix_equiv`, and the endpoint is `prop_better_std`: a
genuine standard block that is simple given the original model (VS40 Section 4, Milestone B7).
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- The partial selector `sel` reconstructs its output from the code it is given at conditional
cost at most the length of the advice plus `Ccond`. -/
private def SelectorCondBound (V : Map) (sel : BitString → BitString →. BitString)
    (Ccond : ℕ) : Prop :=
  ∀ x y z : BitString, z ∈ sel x y → condK V z x ≤ (y.length : ENat) + (Ccond : ENat)

/-- Conditional complexity bound for standard block recovery from advice in `prop_better_std`. -/
private theorem prop_better_std_cond_block (V : Map) (c : Code) (Ccond0 C : ℕ) (hC : Ccond0 + 4 ≤ C)
    (hcond0 : SelectorCondBound V (betterStandardBlockSelector c) Ccond0)
    (m : ℕ) (x : BitString) (A : Finset BitString) (hA : A.Nonempty) (hxA : x ∈ A)
    (hmem : ∀ y ∈ A, y ∈ completedBoundedOutput c m) (r : ℕ) (hxB : x ∈ standardBlock c m r x) :
    condK V (codedUniformOn (standardBlock c m r x) ⟨x, hxB⟩).code (codedUniformOn A hA).code ≤
      (logSlack C m : ENat) := by
  have hrm : r ≤ m := standardBlock_exponent_le c m r x hxB
  obtain ⟨flag, hrec⟩ := betterStandardBlockSelector_recovers c m r x A hA hxA hmem hxB
  refine (hcond0 (codedUniformOn A hA).code (betterStandardBlockAdvice m r flag) _ hrec).trans ?_
  rw [betterStandardBlockAdvice_length]
  have hLr := length_natBits_mono hrm
  have hCL : 4 * (Nat.bits m).length ≤ C * (Nat.bits m).length :=
    Nat.mul_le_mul (show 4 ≤ C by omega) (le_refl _)
  have hnat : 2 * (Nat.bits m).length + 2 * (Nat.bits r).length + 3 + Ccond0 ≤ logSlack C m := by
    rw [show logSlack C m = C * (Nat.bits m).length + C from rfl]; omega
  exact_mod_cast hnat

/-- Conditional complexity bound for length-filtered standard block recovery in
`prop_better_std`. -/
private theorem prop_better_std_cond_filter (V : Map) (c : Code) (Ccond1 C : ℕ)
    (hC : Ccond1 + 9 ≤ C)
    (hcond1 : SelectorCondBound V (betterStandardFilterSelector c) Ccond1)
    (m n : ℕ) (hmn : n ≤ m) (x : BitString) (hn : x.length = n) (A : Finset BitString)
    (hA : A.Nonempty) (hxA : x ∈ A)
    (hMsub : ∀ y ∈ lengthFilteredModel A n, y ∈ completedBoundedOutput c m)
    (r : ℕ) (hxB : x ∈ standardBlock c m r x) :
    condK V (codedUniformOn (standardBlock c m r x) ⟨x, hxB⟩).code (codedUniformOn A hA).code ≤
      (logSlack C m : ENat) := by
  have hxmem : x ∈ lengthFilteredModel A n := Finset.mem_filter.mpr ⟨hxA, hn⟩
  have hA' : (lengthFilteredModel A n).Nonempty := ⟨x, hxmem⟩
  have hrm : r ≤ m := standardBlock_exponent_le c m r x hxB
  obtain ⟨flag, hrec⟩ := betterStandardBlockSelector_recovers c m r x
    (lengthFilteredModel A n) hA' hxmem hMsub hxB
  have hAcode : (codedUniformOn (lengthFilteredModel A n) hA').code =
      lengthFilterUniformCode (pairCode (codedUniformOn A hA).code (Nat.bits n)) :=
    (lengthFilterUniformCode_eq A hA x n hxA hn).symm
  have hrec2 : (codedUniformOn (standardBlock c m r x) ⟨x, hxB⟩).code ∈
      betterStandardFilterSelector c (codedUniformOn A hA).code
        (pairCode (betterStandardBlockAdvice m r flag) (Nat.bits n)) := by
    unfold betterStandardFilterSelector
    rw [decodeFirst_pairCode, decodeSecond_pairCode, ← hAcode]; exact hrec
  refine (hcond1 (codedUniformOn A hA).code _ _ hrec2).trans ?_
  rw [length_pairCode, betterStandardBlockAdvice_length]
  have hLr := length_natBits_mono hrm
  have hLn := length_natBits_mono hmn
  have hCL : 9 * (Nat.bits m).length ≤ C * (Nat.bits m).length :=
    Nat.mul_le_mul (show 9 ≤ C by omega) (le_refl _)
  have hnat : (2 * (Nat.bits m).length + 2 * (Nat.bits r).length + 3) + 1 +
      (2 * (Nat.bits m).length + 2 * (Nat.bits r).length + 3) + (Nat.bits n).length + Ccond1 ≤
      logSlack C m := by unfold logSlack; omega
  exact_mod_cast hnat

/-- The three pointwise estimates for the standard block `standardBlock c mm r x`: its exponent
gap `mm - r` is below the plain complexity of its code up to `logSlack Cpos mm`, and both that
plain complexity and its set complexity are below `mm - r + logSlack Cpos mm`. -/
private def StandardBlockEstimates (V U : Map) (c : Code) (Cpos mm r : ℕ) (x : BitString)
    (hxB : x ∈ standardBlock c mm r x) : Prop :=
  (((mm - r : ℕ) : ENat) ≤
      plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code +
        (logSlack Cpos mm : ENat)) ∧
    (plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code ≤
      ((mm - r + logSlack Cpos mm : ℕ) : ENat)) ∧
    setComplexity U (standardBlock c mm r x) ⟨x, hxB⟩ ≤
      ((mm - r + logSlack Cpos mm : ℕ) : ENat)

/-- Assembly of the better-standard-description package from the pointwise estimates for a
single standard block: given the plain- and set-complexity bounds for `standardBlock c mm r x`,
the slack-absorbed gap bound and the conditional bound relative to `A`, the block witnesses the
conclusion of `prop_better_std`. -/
private theorem standardBlock_better_of_pointwise_bounds (V U : Map) (c : Code)
    (Cpos C i j n mm r : ℕ) (x : BitString) (A : Finset BitString) (hA : A.Nonempty)
    (hxB : x ∈ standardBlock c mm r x) (hrm : r ≤ mm) (hCpos : Cpos ≤ C)
    (hest : StandardBlockEstimates V U c Cpos mm r x hxB)
    (hnat2 : mm - r + logSlack Cpos mm ≤ i + logSlack C mm)
    (hmMin : mm ≤ min n (i + j) + logSlack C n)
    (hcondC : condK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code
      (codedUniformOn A hA).code ≤ (logSlack C mm : ENat)) :
    ∃ (m r : ℕ) (hxB : x ∈ standardBlock c m r x),
      m ≤ min n (i + j) + logSlack C n ∧
      (let B := standardBlock c m r x
       let hB : B.Nonempty := ⟨x, hxB⟩
       B.card = 2 ^ r ∧
       plainK V (codedUniformOn B hB).code ≤ ((i + logSlack C m : ℕ) : ENat) ∧
       setComplexity U B hB ≤ ((i + logSlack C m : ℕ) : ENat) ∧
       (m : ENat) ≤ plainK V (codedUniformOn B hB).code + (r : ENat) + (logSlack C m : ENat) ∧
       plainK V (codedUniformOn B hB).code + (r : ENat) ≤ (m : ENat) + (logSlack C m : ENat) ∧
       condK V (codedUniformOn B hB).code (codedUniformOn A hA).code ≤ (logSlack C m : ENat)) := by
  obtain ⟨hP1, hP2, hP4⟩ := hest
  have hslCpos : (logSlack Cpos mm : ENat) ≤ (logSlack C mm : ENat) := by
    exact_mod_cast logSlack_mono_left hCpos mm
  refine ⟨mm, r, hxB, hmMin, card_standardBlock_of_mem c mm r x hxB,
    le_trans hP2 (by exact_mod_cast hnat2), le_trans hP4 (by exact_mod_cast hnat2), ?_, ?_,
    hcondC⟩
  · have h4a : (mm : ENat) ≤ plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code +
          (logSlack Cpos mm : ENat) + (r : ENat) := by
      have h := add_le_add hP1 (le_refl (r : ENat))
      rwa [← Nat.cast_add, Nat.sub_add_cancel hrm] at h
    calc (mm : ENat)
        ≤ plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code
            + (logSlack Cpos mm : ENat) + (r : ENat) := h4a
      _ = plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code + (r : ENat) +
            (logSlack Cpos mm : ENat) := by rw [add_right_comm]
      _ ≤ plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code + (r : ENat) +
            (logSlack C mm : ENat) := add_le_add le_rfl hslCpos
  · calc plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code + (r : ENat)
        ≤ ((mm - r + logSlack Cpos mm : ℕ) : ENat) + (r : ENat) := add_le_add hP2 le_rfl
      _ = ((mm + logSlack Cpos mm : ℕ) : ENat) := by rw [← Nat.cast_add]; congr 1; omega
      _ = (mm : ENat) + (logSlack Cpos mm : ENat) := by rw [Nat.cast_add]
      _ ≤ (mm : ENat) + (logSlack C mm : ENat) := add_le_add le_rfl hslCpos

/-- Proposition 4.11 (prop:better-std): For every description A for x there is a better
standard description that is simple given A. -/
theorem prop_better_std
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (n i j : ℕ)
      (A : Finset BitString) (hA : A.Nonempty),
      x.length = n →
      IsIJDescription U x A hA i j →
      ∃ (m r : ℕ) (hxB : x ∈ standardBlock c m r x),
        m ≤ min n (i + j) + logSlack C n ∧
        let B := standardBlock c m r x
        let hB : B.Nonempty := ⟨x, hxB⟩
        B.card = 2 ^ r ∧
        plainK V (codedUniformOn B hB).code ≤
          ((i + logSlack C m : ℕ) : ENat) ∧
        setComplexity U B hB ≤
          ((i + logSlack C m : ℕ) : ENat) ∧
        (m : ENat) ≤
          plainK V (codedUniformOn B hB).code + (r : ENat) +
            (logSlack C m : ENat) ∧
        plainK V (codedUniformOn B hB).code + (r : ENat) ≤
          (m : ENat) + (logSlack C m : ENat) ∧
        condK V (codedUniformOn B hB).code
          (codedUniformOn A hA).code ≤
            (logSlack C m : ENat) := by
  obtain ⟨Cpos, hpos⟩ := prop_std_pos V U hV hU c hc
  obtain ⟨Csuff, hsuff⟩ := suffixCoordinate_lower_of_model_code V hV c hc
  obtain ⟨Cmem, hmemC⟩ := mem_completed_of_isIJDescription V U hV hU c hc
  obtain ⟨Cbridge, hbridge⟩ := plain_le_prefix V U hV hU.isPrefixDecompressor
  obtain ⟨Cfilter, hfilterC⟩ := setComplexity_lengthFilteredModel_le U hU
  obtain ⟨Clen, hlenC⟩ := plainK_le_length V hV
  obtain ⟨Ccond0, hcond0⟩ := condK_partrec_cond_map_le V hV
    (betterStandardBlockSelector c) (betterStandardBlockSelector_partrec c)
  obtain ⟨Ccond1, hcond1⟩ := condK_partrec_cond_map_le V hV
    (betterStandardFilterSelector c) (betterStandardFilterSelector_partrec c)
  set Cq := Cfilter + Cbridge + 1 with hCq
  set C := Cpos + Csuff + Cq + Cmem + Cbridge + Cfilter + Clen + Ccond0 + Ccond1 + 20 with hC
  refine ⟨C, fun x n i j A hA hn hdesc => ?_⟩
  obtain ⟨hxA, hcompA, hcardA⟩ := hdesc
  by_cases hcase : i + j ≤ n
  · set mm := i + j + logSlack Cmem j with hmm
    have hMsub : ∀ y ∈ A, y ∈ completedBoundedOutput c mm :=
      fun y hy => hmemC x y i j A hA ⟨hxA, hcompA, hcardA⟩ hy
    obtain ⟨r, hxB⟩ := exists_standardBlock_of_mem_completed c mm x (hMsub x hxA)
    obtain ⟨hP1, hP2, -, hP4, -, -⟩ := hpos mm r x hxB
    have hqM : plainK V (codedUniformOn A hA).code ≤ ((i + Cbridge : ℕ) : ENat) := by
      calc plainK V (codedUniformOn A hA).code
          ≤ setComplexity U A hA + (Cbridge : ENat) := hbridge (codedUniformOn A hA).code
        _ ≤ (i : ENat) + (Cbridge : ENat) := add_le_add hcompA le_rfl
        _ = ((i + Cbridge : ℕ) : ENat) := by rw [Nat.cast_add]
    have hgap : mm - r ≤ (i + Cbridge) + logSlack Csuff mm :=
      standardBlock_gap_le_of_suffix_lower c mm r (i + Cbridge) (logSlack Csuff mm) x hxB
        (hsuff mm (i + Cbridge) x A hA hxA hMsub hqM)
    have hqi : i + Cbridge ≤ i + logSlack Cq mm :=
      Nat.add_le_add_left (const_le_logSlack (by rw [hCq]; omega)) i
    have hmMin : mm ≤ min n (i + j) + logSlack C n := by
      have h1 : logSlack Cmem j ≤ logSlack C n :=
        (logSlack_mono_right Cmem (by omega)).trans (logSlack_mono_left (by omega) n)
      rw [min_eq_right (by omega)]; omega
    exact standardBlock_better_of_pointwise_bounds V U c Cpos C i j n mm r x A hA hxB
      (standardBlock_exponent_le c mm r x hxB) (by omega) ⟨hP1, hP2, hP4⟩
      (logSlack_add_le_of_gap_bounds (by omega) hgap hqi) hmMin
      (prop_better_std_cond_block V c Ccond0 C (by omega) hcond0 mm x A hA hxA hMsub r hxB)
  · push_neg at hcase
    set mm := n + Clen with hmm
    have hxmem : x ∈ lengthFilteredModel A n := Finset.mem_filter.mpr ⟨hxA, hn⟩
    have hA' : (lengthFilteredModel A n).Nonempty := ⟨x, hxmem⟩
    have hMsub : ∀ y ∈ lengthFilteredModel A n, y ∈ completedBoundedOutput c mm := by
      intro y hy
      have hyn : y.length = n := (Finset.mem_filter.mp hy).2
      have hyk : plainK V y ≤ ((n + Clen : ℕ) : ENat) := by
        calc plainK V y ≤ (programLength y : ENat) + (Clen : ENat) := hlenC y
          _ = ((n + Clen : ℕ) : ENat) := by simp only [programLength, hyn]; rw [Nat.cast_add]
      exact (mem_completedBoundedOutput_iff_plainK_le hc (n + Clen) y).mpr hyk
    obtain ⟨r, hxB⟩ := exists_standardBlock_of_mem_completed c mm x (hMsub x hxmem)
    obtain ⟨hP1, hP2, -, hP4, -, -⟩ := hpos mm r x hxB
    have hqM : plainK V (codedUniformOn (lengthFilteredModel A n) hA').code ≤
        ((i + logSlack Cfilter n + Cbridge : ℕ) : ENat) := by
      have hfilt : setComplexity U (lengthFilteredModel A n) hA'
          ≤ setComplexity U A hA + (logSlack Cfilter n : ENat) := hfilterC A hA x n hxA hn
      calc plainK V (codedUniformOn (lengthFilteredModel A n) hA').code
          ≤ setComplexity U (lengthFilteredModel A n) hA' + (Cbridge : ENat) :=
            hbridge (codedUniformOn (lengthFilteredModel A n) hA').code
        _ ≤ (setComplexity U A hA + (logSlack Cfilter n : ENat)) + (Cbridge : ENat) :=
            add_le_add hfilt le_rfl
        _ ≤ ((i : ENat) + (logSlack Cfilter n : ENat)) + (Cbridge : ENat) :=
            add_le_add (add_le_add hcompA le_rfl) le_rfl
        _ = ((i + logSlack Cfilter n + Cbridge : ℕ) : ENat) := by rw [Nat.cast_add, Nat.cast_add]
    have hgap : mm - r ≤ (i + logSlack Cfilter n + Cbridge) + logSlack Csuff mm :=
      standardBlock_gap_le_of_suffix_lower c mm r (i + logSlack Cfilter n + Cbridge)
        (logSlack Csuff mm) x hxB
        (hsuff mm (i + logSlack Cfilter n + Cbridge) x (lengthFilteredModel A n) hA' hxmem
          hMsub hqM)
    have hqi : i + logSlack Cfilter n + Cbridge ≤ i + logSlack Cq mm := by
      have h1 : logSlack Cfilter n ≤ logSlack Cfilter mm := logSlack_mono_right Cfilter (by omega)
      have h2 : Cbridge ≤ logSlack Cbridge mm := const_le_logSlack (le_refl _)
      have h3 := logSlack_add_same Cfilter Cbridge mm
      have h4 := logSlack_mono_left (by omega : Cfilter + Cbridge ≤ Cq) mm
      omega
    have hmMin : mm ≤ min n (i + j) + logSlack C n := by
      have h1 : Clen ≤ logSlack C n := const_le_logSlack (by omega)
      rw [min_eq_left (by omega)]; omega
    exact standardBlock_better_of_pointwise_bounds V U c Cpos C i j n mm r x A hA hxB
      (standardBlock_exponent_le c mm r x hxB) (by omega) ⟨hP1, hP2, hP4⟩
      (logSlack_add_le_of_gap_bounds (by omega) hgap hqi) hmMin
      (prop_better_std_cond_filter V c Ccond1 C (by omega) hcond1 mm n (by omega) x hn A hA
        hxA hMsub r hxB)

/-- The high `m-j` bits of `Ω_m` identify the source-standard block containing
`x`.  They decode to the quotient by `2^(j+1)`; multiplying that quotient by
two gives the aligned `2^j`-block index used by `completedDyadicBlockSelector`.
The factor of two is essential: the set `j` bit is the low bit of the block
index and is not present in the strict high prefix. -/
theorem completedDyadicBlockIndex_eq_two_mul_omegaPrefix
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    completedDyadicBlockIndex c m j x =
      2 * decodeFixedWidthNatCode
        ((omegaFixedCode c m).take (m - j)) := by
  let L := completedBoundedOutput c m
  let p := 2 ^ j
  let q := omegaCount c m / 2 ^ (j + 1)
  let start := q * 2 ^ (j + 1)
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hxList : x ∈ (L.drop start).take p := by
    unfold standardBlock at hx
    rw [if_pos hbit, List.mem_toFinset] at hx
    simpa [L, p, q, start] using hx
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hxList
  have hklt : k < p := lt_of_lt_of_le hk (List.length_take_le p (L.drop start))
  have hglobal : start + k < L.length := by
    simp only [List.length_take, List.length_drop] at hk
    omega
  have hget : L[start + k] = x := by
    simpa only [List.getElem_take, List.getElem_drop] using hkx
  have hnodup : L.Nodup := by
    dsimp [L, completedBoundedOutput]
    exact boundedOutputStage_nodup c m (maxHaltingStage c m)
  have hidx : L.findIdx (· == x) = start + k := by
    change L.idxOf x = start + k
    rw [← hget]
    exact hnodup.idxOf_getElem (start + k) hglobal
  have hstart : start = (2 * q) * p := by
    dsimp [start, p]
    rw [pow_succ']
    ring
  have hquot : L.findIdx (· == x) / p = 2 * q := by
    apply Nat.div_eq_of_lt_le
    · rw [hidx, ← hstart]
      omega
    · rw [hidx]
      calc
        start + k < start + p := by omega
        _ = (2 * q + 1) * p := by rw [hstart]; ring
  have hjm := standardBlock_exponent_le c m j x hx
  have hdecode : decodeFixedWidthNatCode
          ((omegaFixedCode c m).take (m - j)) =
        q := by
    rw [decode_take_omegaFixedCode]
    have hsub : m + 1 - (m - j) = j + 1 := by omega
    rw [hsub]
  change L.findIdx (· == x) / p =
    2 * decodeFixedWidthNatCode
      ((omegaFixedCode c m).take (m - j))
  simpa [hdecode] using hquot

/-- From the high `m-j` bits of `Ω_m` and logarithmic advice `(m,j)`, build the
exact input expected by the completed-dyadic-block selector. -/
noncomputable def standardBlockFromOmegaPrefixSelector
    (c : Code) : BitString → BitString →. BitString := fun pref z =>
  completedDyadicBlockSelector c
    (completedDyadicBlockInput
      (standardBlockAdviceM z)
      (standardBlockAdviceJ z)
      (2 * decodeFixedWidthNatCode pref)
      (pref.length + 1))

/-- Building a standard block from the high bits of `Ω_m` and advice `(m, j)` is partrec. -/
theorem standardBlockFromOmegaPrefixSelector_partrec
    (c : Code) :
    Partrec (fun q : BitString × BitString =>
      standardBlockFromOmegaPrefixSelector c q.1 q.2) := by
  have hm : Primrec (fun q : BitString × BitString =>
      standardBlockAdviceM q.2) :=
    (bitsToNat_primrec.comp decodeFirst_primrec).comp Primrec.snd
  have hj : Primrec (fun q : BitString × BitString =>
      standardBlockAdviceJ q.2) :=
    (bitsToNat_primrec.comp decodeSecond_primrec).comp Primrec.snd
  have hdecode : Primrec (fun q : BitString × BitString =>
      decodeFixedWidthNatCode q.1) :=
    decodeFixedWidthNatCode_primrec.comp Primrec.fst
  have hidx : Primrec (fun q : BitString × BitString =>
      2 * decodeFixedWidthNatCode q.1) :=
    Primrec.nat_mul.comp (Primrec.const 2) hdecode
  have hwidth : Primrec (fun q : BitString × BitString =>
      q.1.length + 1) :=
    Primrec.nat_add.comp
      (Primrec.list_length.comp Primrec.fst)
      (Primrec.const 1)
  have hinput : Computable (fun q : BitString × BitString =>
      completedDyadicBlockInput
        (standardBlockAdviceM q.2)
        (standardBlockAdviceJ q.2)
        (2 * decodeFixedWidthNatCode q.1)
        (q.1.length + 1)) := by
    unfold completedDyadicBlockInput
    exact (pairCode_primrec.comp
      (pairCode_primrec.comp
        (primrec_natBits.comp hm)
        (primrec_natBits.comp hj))
      (fixedWidthNatCode_primrec.comp
        (Primrec.pair hidx hwidth))).to_comp
  unfold standardBlockFromOmegaPrefixSelector
  exact Partrec.comp (completedDyadicBlockSelector_partrec c) hinput

/-- From the high `m - j` bits of `Ω_m` and advice `(m, j)` the selector outputs the code
of the uniform distribution on the standard block of `x`. -/
theorem standardBlockFromOmegaPrefixSelector_recovers
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
    (codedUniformOn (standardBlock c m j x) hA).code ∈
      standardBlockFromOmegaPrefixSelector c
        ((omegaFixedCode c m).take (m - j))
        (standardBlockAdvice m j) := by
  intro hA
  have hjm := standardBlock_exponent_le c m j x hx
  have hprefixLength : ((omegaFixedCode c m).take (m - j)).length = m - j := by
    rw [List.length_take, omegaFixedCode_length, Nat.min_eq_left]
    omega
  have hidx := completedDyadicBlockIndex_eq_two_mul_omegaPrefix
      c m j x hx
  unfold standardBlockFromOmegaPrefixSelector
  simp only [standardBlockAdviceM_advice,
    standardBlockAdviceJ_advice, hprefixLength]
  rw [← hidx]
  simpa using
    (completedDyadicBlockSelector_recovers_standardBlock
      c m j x hx)

/-- The forward half of the block/high-prefix equivalence.  The high
`m-j`-bit prefix of `Ω_m`, together with self-delimiting advice `(m,j)`,
reconstructs the canonical standard-block code with logarithmic cost. -/
theorem condK_standardBlock_le_omegaPrefix
    (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      condK V
          (codedUniformOn (standardBlock c m j x) hA).code
          ((omegaFixedCode c m).take (m - j)) ≤
        (logSlack C m : ENat) := by
  obtain ⟨Cmap, hmap⟩ := condK_partrec_cond_map_le V hV
      (standardBlockFromOmegaPrefixSelector c)
      (standardBlockFromOmegaPrefixSelector_partrec c)
  let C := Cmap + 4
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  have hjm := standardBlock_exponent_le c m j x hx
  have hjBits : (Nat.bits j).length ≤ (Nat.bits m).length :=
    length_natBits_mono hjm
  have hrecover := standardBlockFromOmegaPrefixSelector_recovers c m j x hx
  calc
    condK V
        (codedUniformOn (standardBlock c m j x) hA).code
        ((omegaFixedCode c m).take (m - j))
      ≤ ((standardBlockAdvice m j).length : ENat) +
          (Cmap : ENat) :=
        hmap ((omegaFixedCode c m).take (m - j))
          (standardBlockAdvice m j)
          (codedUniformOn (standardBlock c m j x) hA).code
          hrecover
    _ = (((standardBlockAdvice m j).length + Cmap : ℕ) : ENat) := by
      rw [Nat.cast_add]
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast (show
        (standardBlockAdvice m j).length + Cmap ≤
          logSlack C m by
        rw [standardBlockAdvice_length]
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits m).length)])

/-- Once a stage contains every member of a genuine standard block, its prefix
has reached at least the end of that block. -/
theorem standardBlock_end_le_stage_of_cover
    (c : Code) (m j t : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x)
    (hcover : ∀ y ∈ standardBlock c m j x,
      y ∈ boundedOutputStage c m t) :
    (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1) +
        2 ^ j ≤ (boundedOutputStage c m t).length := by
  let L := completedBoundedOutput c m
  let S := boundedOutputStage c m t
  let p := 2 ^ j
  let start := (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1)
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hfit : start + p ≤ L.length := by
    change
      (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1) +
          2 ^ j ≤ omegaCount c m
    exact standardBlock_start_add_size_le hbit
  have hpPos : 0 < p := by
    dsimp [p]
    positivity
  let k := p - 1
  have hk : k < ((L.drop start).take p).length := by
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    · dsimp [k, p]
      omega
    · omega
  let y := ((L.drop start).take p)[k]
  have hySlice : y ∈ (L.drop start).take p := List.getElem_mem hk
  have hyBlock : y ∈ standardBlock c m j x := by
    unfold standardBlock
    rw [if_pos hbit, List.mem_toFinset]
    simpa [L, start, p] using hySlice
  have hyS : y ∈ S := hcover y hyBlock
  have hprefix : S <+: L := boundedOutputStage_prefix_completed c m t
  have hyIdxLt : L.idxOf y < S.length := (hprefix.mem_iff_idxOf_lt_length y).mp hyS
  have hglobal : start + k < L.length := by
    have hkDrop : k < (L.drop start).length := lt_of_lt_of_le hk (by simp)
    simp only [List.length_drop] at hkDrop
    omega
  have hyGet : L[start + k] = y := by
    dsimp [y]
    simp only [List.getElem_take, List.getElem_drop]
  have hnodup : L.Nodup := by
    dsimp [L, completedBoundedOutput]
    exact boundedOutputStage_nodup c m
      (maxHaltingStage c m)
  have hidx : L.idxOf y = start + k := by
    rw [← hyGet]
    exact hnodup.idxOf_getElem (start + k) hglobal
  change start + p ≤ S.length
  rw [hidx] at hyIdxLt
  dsimp [k] at hyIdxLt
  omega

/-- Given a canonical standard-block code and advice `(m,j)`, wait until every
block member has appeared and emit the final high quotient of `Ω_m`. -/
noncomputable def omegaPrefixFromStandardBlockSelector
    (c : Code) : BitString → BitString →. BitString := fun SCode z =>
  let SList := (decodeDistributionData SCode).map
      CodedDistributionEntry.point
  (Nat.rfind (fun t => Part.some
    (SList.all (fun y =>
      decide
        (y ∈ boundedOutputStage c
          (standardBlockAdviceM z) t))))).bind
    (fun t => Part.some
      (fixedWidthNatCode
        ((boundedOutputStage c
          (standardBlockAdviceM z) t).length /
            2 ^ (standardBlockAdviceJ z + 1))
        (standardBlockAdviceM z - standardBlockAdviceJ z)))

/-- Recovering the high bits of `Ω_m` from a standard-block code is partial recursive. -/
theorem omegaPrefixFromStandardBlockSelector_partrec
    (c : Code) :
    Partrec (fun q : BitString × BitString =>
      omegaPrefixFromStandardBlockSelector c q.1 q.2) := by
  have hm : Primrec standardBlockAdviceM := bitsToNat_primrec.comp decodeFirst_primrec
  have hj : Primrec standardBlockAdviceJ := bitsToNat_primrec.comp decodeSecond_primrec
  have hSList : Primrec (fun q : BitString × BitString =>
      (decodeDistributionData q.1).map
        CodedDistributionEntry.point) :=
    Primrec.list_map
      (decodeDistributionData_primrec.comp Primrec.fst)
      (entry_point_primrec.comp Primrec.snd).to₂
  have hstage : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        boundedOutputStage c
          (standardBlockAdviceM q.1.2) q.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair
        ((hm.comp Primrec.snd).comp Primrec.fst)
        Primrec.snd)
  have hcheck : Computable₂
      (fun (q : BitString × BitString) (t : ℕ) =>
        (decodeDistributionData q.1).map
            CodedDistributionEntry.point |>.all
          (fun y =>
            decide (y ∈ boundedOutputStage c
              (standardBlockAdviceM q.2) t))) := by
    have hpred : Primrec₂
        (fun (q : (BitString × BitString) × ℕ)
          (y : BitString) =>
          decide (y ∈ boundedOutputStage c
            (standardBlockAdviceM q.1.2) q.2)) :=
      (bitString_mem_primrec.comp Primrec.snd
        (hstage.comp Primrec.fst)).to₂
    have hall : Primrec
        (fun q : (BitString × BitString) × ℕ =>
          (decodeDistributionData q.1.1).map
              CodedDistributionEntry.point |>.all
            (fun y => decide
              (y ∈ boundedOutputStage c
                (standardBlockAdviceM q.1.2) q.2))) :=
      list_all_primrec (hSList.comp Primrec.fst) hpred
    exact hall.to_comp.to₂
  have hsearch : Partrec (fun q : BitString × BitString =>
      Nat.rfind (fun t => Part.some
        ((decodeDistributionData q.1).map
            CodedDistributionEntry.point |>.all
          (fun y =>
            decide (y ∈ boundedOutputStage c
              (standardBlockAdviceM q.2) t))))) :=
    Partrec.rfind hcheck.partrec₂
  have hlen : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        (boundedOutputStage c
          (standardBlockAdviceM q.1.2) q.2).length) :=
    Primrec.list_length.comp hstage
  have hjSucc : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        standardBlockAdviceJ q.1.2 + 1) :=
    Primrec.nat_add.comp
      ((hj.comp Primrec.snd).comp Primrec.fst)
      (Primrec.const 1)
  have hpow : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        2 ^ (standardBlockAdviceJ q.1.2 + 1)) :=
    Kolmogorov.primrec_two_pow_aux.comp
      hjSucc
  have hquot : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        (boundedOutputStage c
          (standardBlockAdviceM q.1.2) q.2).length /
            2 ^ (standardBlockAdviceJ q.1.2 + 1)) :=
    Primrec.nat_div.comp hlen hpow
  have hwidth : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        standardBlockAdviceM q.1.2 -
          standardBlockAdviceJ q.1.2) :=
    Primrec.nat_sub.comp
      ((hm.comp Primrec.snd).comp Primrec.fst)
      ((hj.comp Primrec.snd).comp Primrec.fst)
  have hresult : Computable₂
      (fun (q : BitString × BitString) (t : ℕ) =>
        fixedWidthNatCode
          ((boundedOutputStage c
            (standardBlockAdviceM q.2) t).length /
              2 ^ (standardBlockAdviceJ q.2 + 1))
          (standardBlockAdviceM q.2 -
            standardBlockAdviceJ q.2)) :=
    (fixedWidthNatCode_primrec.comp
      (Primrec.pair hquot hwidth)).to_comp.to₂
  unfold omegaPrefixFromStandardBlockSelector
  exact Partrec.bind hsearch hresult.partrec₂

/-- Given the code of the standard block of `x` and advice `(m, j)`, the selector outputs
the high `m - j` bits of `Ω_m`. -/
theorem omegaPrefixFromStandardBlockSelector_recovers
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
    (omegaFixedCode c m).take (m - j) ∈
      omegaPrefixFromStandardBlockSelector c
        (codedUniformOn (standardBlock c m j x) hA).code
        (standardBlockAdvice m j) := by
  intro hA
  let B := standardBlock c m j x
  let SCode := (codedUniformOn B hA).code
  let SList := canonicalFinsetList B
  have hSList : SList =
        (decodeDistributionData SCode).map
          CodedDistributionEntry.point :=
    (dataPoints_codedUniformOn B hA).symm
  have hsubset : ∀ y ∈ SList, y ∈ completedBoundedOutput c m := by
    intro y hy
    apply List.mem_toFinset.mp
    exact standardBlock_subset_completed c m j x
      (mem_canonicalFinsetList.mp hy)
  have hex : ∃ t, SList.all (fun y =>
        decide (y ∈ boundedOutputStage c m t)) = true := by
    obtain ⟨t, ht⟩ := exists_stage_covering_finset c m B
        (fun y hy => hsubset y
          (mem_canonicalFinsetList.mpr hy))
    refine ⟨t, ?_⟩
    rw [List.all_eq_true]
    intro y hy
    exact decide_eq_true
      (ht y (mem_canonicalFinsetList.mp hy))
  let t₀ := Nat.find hex
  have ht₀spec : SList.all (fun y =>
        decide (y ∈ boundedOutputStage c m t₀)) = true :=
    Nat.find_spec hex
  have ht₀mem : t₀ ∈ Nat.rfind (fun t => Part.some
        (SList.all (fun y =>
          decide (y ∈ boundedOutputStage c m t)))) := by
    rw [Nat.mem_rfind]
    refine ⟨by simpa using ht₀spec, ?_⟩
    intro t ht
    simpa using Nat.find_min hex ht
  have hcover : ∀ y ∈ standardBlock c m j x,
        y ∈ boundedOutputStage c m t₀ := by
    rw [List.all_eq_true] at ht₀spec
    intro y hy
    simpa using
      ht₀spec y (mem_canonicalFinsetList.mpr hy)
  have hendAt := standardBlock_end_le_stage_of_cover
      c m j t₀ x hx hcover
  have hstageLe : (boundedOutputStage c m t₀).length ≤
        omegaCount c m :=
    (boundedOutputStage_prefix_completed c m t₀).length_le
  let q := omegaCount c m / 2 ^ (j + 1)
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hdecomp := standardBlock_end_add_tail c m j hbit
  have htailLt : standardBlockTail c m j < 2 ^ j := by
    have h := standardBlockTail_add_one_le c m j
    omega
  have hlower : q * 2 ^ (j + 1) + 2 ^ j ≤
        (boundedOutputStage c m t₀).length := by
    simpa [q] using hendAt
  have hupper : (boundedOutputStage c m t₀).length <
        (q + 1) * 2 ^ (j + 1) := by
    have homega : omegaCount c m =
          q * 2 ^ (j + 1) + 2 ^ j +
            standardBlockTail c m j := by
      simpa [q] using hdecomp.symm
    calc
      (boundedOutputStage c m t₀).length
          ≤ omegaCount c m := hstageLe
      _ = q * 2 ^ (j + 1) + 2 ^ j +
          standardBlockTail c m j := homega
      _ < q * 2 ^ (j + 1) + 2 ^ j + 2 ^ j := Nat.add_lt_add_left htailLt _
      _ = (q + 1) * 2 ^ (j + 1) := by
        rw [pow_succ']
        ring
  have hquot : (boundedOutputStage c m t₀).length /
          2 ^ (j + 1) =
        q := by
    apply Nat.div_eq_of_lt_le
    · omega
    · exact hupper
  have hjm := standardBlock_exponent_le c m j x hx
  have hsub : m + 1 - (m - j) = j + 1 := by omega
  have hpref : (omegaFixedCode c m).take (m - j) =
        fixedWidthNatCode q (m - j) := by
    rw [omegaFixedCode_take_eq c m (show m - j ≤ m + 1 by omega)]
    rw [hsub]
  unfold omegaPrefixFromStandardBlockSelector
  rw [Part.mem_bind_iff]
  refine ⟨t₀, ?_, ?_⟩
  · simpa [SCode, B, hSList] using ht₀mem
  · simp only [standardBlockAdviceM_advice,
      standardBlockAdviceJ_advice]
    rw [hquot, ← hpref]
    exact Part.mem_some _

/-- The reverse half of the block/high-prefix equivalence. -/
theorem condK_omegaPrefix_le_standardBlock
    (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      condK V
          ((omegaFixedCode c m).take (m - j))
          (codedUniformOn (standardBlock c m j x) hA).code ≤
        (logSlack C m : ENat) := by
  obtain ⟨Cmap, hmap⟩ := condK_partrec_cond_map_le V hV
      (omegaPrefixFromStandardBlockSelector c)
      (omegaPrefixFromStandardBlockSelector_partrec c)
  let C := Cmap + 4
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  have hjm := standardBlock_exponent_le c m j x hx
  have hjBits : (Nat.bits j).length ≤ (Nat.bits m).length :=
    length_natBits_mono hjm
  have hrecover := omegaPrefixFromStandardBlockSelector_recovers c m j x hx
  calc
    condK V
        ((omegaFixedCode c m).take (m - j))
        (codedUniformOn (standardBlock c m j x) hA).code
      ≤ ((standardBlockAdvice m j).length : ENat) +
          (Cmap : ENat) :=
        hmap
          (codedUniformOn (standardBlock c m j x) hA).code
          (standardBlockAdvice m j)
          ((omegaFixedCode c m).take (m - j))
          hrecover
    _ = (((standardBlockAdvice m j).length + Cmap : ℕ) : ENat) := by
      rw [Nat.cast_add]
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast (show
        (standardBlockAdvice m j).length + Cmap ≤
          logSlack C m by
        rw [standardBlockAdvice_length]
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits m).length)])

/-- A genuine standard block and the high `m-j` bits of the same finite Omega
count determine one another with uniform logarithmic advice. -/
theorem standardBlock_omegaPrefix_equiv
    (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      condK V
          (codedUniformOn (standardBlock c m j x) hA).code
          ((omegaFixedCode c m).take (m - j)) ≤
          (logSlack C m : ENat) ∧
      condK V
          ((omegaFixedCode c m).take (m - j))
          (codedUniformOn (standardBlock c m j x) hA).code ≤
          (logSlack C m : ENat) := by
  obtain ⟨C₁, hforward⟩ := condK_standardBlock_le_omegaPrefix V hV c
  obtain ⟨C₂, hreverse⟩ := condK_omegaPrefix_le_standardBlock V hV c
  refine ⟨C₁ + C₂, fun m j x hx => ?_⟩
  intro hA
  have hslack₁ : logSlack C₁ m ≤ logSlack (C₁ + C₂) m :=
    logSlack_mono_left (Nat.le_add_right C₁ C₂) m
  have hslack₂ : logSlack C₂ m ≤ logSlack (C₁ + C₂) m :=
    logSlack_mono_left (Nat.le_add_left C₂ C₁) m
  constructor
  · exact (hforward m j x hx).trans (by
      exact_mod_cast hslack₁)
  · exact (hreverse m j x hx).trans (by
      exact_mod_cast hslack₂)

/-- Plain-machine-only form of the standard-block index estimate.  Unlike the
profile-facing `standardBlock_plainK_index_close` below, this lemma needs no
prefix machine: its lower bound is the direct finite-Omega reconstruction
inequality and its upper bound is the explicit standard-block encoder. -/
theorem standardBlock_plainK_index_close_plain
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j i : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code =
            (i : ENat) →
      i ≤ m - j + logSlack C m ∧
      m - j ≤ i + logSlack C m := by
  obtain ⟨Ccoding, hcoding⟩ := standardBlock_omega_coding_bound V hV c hc
  obtain ⟨Cplain, hplain⟩ := plainK_standardBlock_upper V hV c hc
  let C := Ccoding + Cplain
  refine ⟨C, fun m j i x hx => ?_⟩
  intro hA hplainEq
  have htailLt : standardBlockTail c m j < 2 ^ j := by
    have h := standardBlockTail_add_one_le c m j
    omega
  have htailBits : (Nat.bits (standardBlockTail c m j)).length ≤ j :=
    length_natBits_lt_pow htailLt
  have hcodingNat : m ≤ i +
        (Nat.bits (standardBlockTail c m j)).length +
        logSlack Ccoding m := by
    have h := hcoding m j x hx
    rw [hplainEq] at h
    exact_mod_cast h
  have hupperNat : i ≤ m - j + logSlack Cplain m := by
    have h := hplain m j x hx
    change plainK V
      (codedUniformOn (standardBlock c m j x) hA).code ≤
        ((m - j + logSlack Cplain m : ℕ) : ENat) at h
    rw [hplainEq] at h
    exact_mod_cast h
  have hcodingSlack : logSlack Ccoding m ≤ logSlack C m :=
    logSlack_mono_left (by dsimp [C]; omega) m
  have hplainSlack : logSlack Cplain m ≤ logSlack C m :=
    logSlack_mono_left (by dsimp [C]; omega) m
  exact ⟨by omega, by omega⟩

/-- If the canonical code of a genuine standard block has exact plain
complexity `i`, then `i` is logarithmically close to its position parameter
`m-j`. -/
theorem standardBlock_plainK_index_close
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j i : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code =
            (i : ENat) →
      i ≤ m - j + logSlack C m ∧
      m - j ≤ i + logSlack C m := by
  obtain ⟨C, hpos⟩ := prop_std_pos V U hV hU c hc
  refine ⟨C, fun m j i x hx => ?_⟩
  intro hA hplain
  have hbounds := hpos m j x hx
  change
      ((m - j : ℕ) : ENat) ≤
          plainK V
            (codedUniformOn (standardBlock c m j x) hA).code +
            (logSlack C m : ENat) ∧
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code ≤
            ((m - j + logSlack C m : ℕ) : ENat) ∧
      _ at hbounds
  rw [hplain] at hbounds
  have hlower : m - j ≤ i + logSlack C m := by
    exact_mod_cast hbounds.1
  have hupper : i ≤ m - j + logSlack C m := by
    exact_mod_cast hbounds.2.1
  exact ⟨hupper, hlower⟩

/-- A two-stage plain conditional decompressor.  Its program is a concrete
pair of programs: the first produces an intermediate string from the original
condition and the second produces the final string from that intermediate
condition. -/
def conditionalComposeDecompressor (V : Map) : Map := fun pr =>
  (V (decodeFirst pr.1, pr.2)).bind fun y =>
    V (decodeSecond pr.1, y)

/-- The two-stage conditional machine is partial recursive. -/
theorem conditionalComposeDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    Partrec (conditionalComposeDecompressor V) := by
  have hfirst : Partrec (fun pr : BitString × BitString =>
        V (decodeFirst pr.1, pr.2)) :=
    Partrec.comp hV
      (Computable.pair
        (decodeFirst_computable.comp Computable.fst)
        Computable.snd)
  have hsecond : Partrec (fun q : (BitString × BitString) × BitString =>
        V (decodeSecond q.1.1, q.2)) :=
    Partrec.comp hV
      (Computable.pair
        (decodeSecond_computable.comp
          (Computable.fst.comp Computable.fst))
        Computable.snd)
  exact Partrec.bind hfirst hsecond

/-- Plain conditional complexity is transitive with the explicit overhead of
the concrete self-delimiting pair of the two witness programs.  The factor two
on the first bound is the unary length header in `pairCode`. -/
theorem condK_trans_nat
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (x y z : BitString) (a b : ℕ),
      condK V y x ≤ (a : ENat) →
      condK V z y ≤ (b : ENat) →
      condK V z x ≤ ((2 * a + b + C : ℕ) : ENat) := by
  obtain ⟨C, hC⟩ := hV.2 (conditionalComposeDecompressor V)
      (conditionalComposeDecompressor_partrec V hV.1)
  refine ⟨C + 1, fun x y z a b hxy hyz => ?_⟩
  obtain ⟨p, hpLen, hp⟩ := (condK_le_iff V y x a).mp hxy
  obtain ⟨q, hqLen, hq⟩ := (condK_le_iff V z y b).mp hyz
  change p.length ≤ a at hpLen
  change q.length ≤ b at hqLen
  change y ∈ V (p, x) at hp
  change z ∈ V (q, y) at hq
  have hprod : produces (conditionalComposeDecompressor V)
        (pairCode p q) x z := by
    unfold produces conditionalComposeDecompressor
    rw [Part.mem_bind_iff]
    refine ⟨y, ?_, ?_⟩
    · rw [decodeFirst_pairCode]
      exact hp
    · rw [decodeSecond_pairCode]
      exact hq
  calc
    condK V z x ≤
        condK (conditionalComposeDecompressor V) z x +
          (C : ENat) := hC z x
    _ ≤ ((pairCode p q).length : ENat) + (C : ENat) := by
      gcongr
      exact sInf_le ⟨pairCode p q, hprod, rfl⟩
    _ ≤ ((2 * a + b + (C + 1) : ℕ) : ENat) := by
      rw [length_pairCode]
      exact_mod_cast (show
        p.length + 1 + p.length + q.length + C ≤
          2 * a + b + (C + 1) by omega)

/-- A condition can be truncated to any requested prefix using only the binary
code of the requested length as advice. -/
def takePrefixSelector (y p : BitString) : Part BitString :=
  Part.some (y.take (bitsToNat p))

/-- Truncating a condition to the length named by the program is partial recursive. -/
theorem takePrefixSelector_partrec :
    Partrec (fun q : BitString × BitString =>
      takePrefixSelector q.1 q.2) := by
  exact (Primrec.list_take.comp Primrec.fst
    (bitsToNat_primrec.comp Primrec.snd)).to_comp.partrec

/-- A prefix of `y` has conditional complexity given `y` logarithmic in the prefix length. -/
theorem condK_take_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (y : BitString) (k : ℕ),
      condK V (y.take k) y ≤
        (((Nat.bits k).length + C : ℕ) : ENat) := by
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV
      takePrefixSelector takePrefixSelector_partrec
  refine ⟨C, fun y k => ?_⟩
  have hmem : y.take k ∈ takePrefixSelector y (Nat.bits k) := by
    simp [takePrefixSelector, bitsToNat_bits]
  simpa [Nat.cast_add] using hC y (Nat.bits k) (y.take k) hmem

/-- A string is reconstructible from one of its prefixes by supplying the
literal remaining suffix as the plain advice program. -/
def appendSuffixSelector (y p : BitString) : Part BitString :=
  Part.some (y ++ p)

/-- Appending the program to the condition is partial recursive. -/
theorem appendSuffixSelector_partrec :
    Partrec (fun q : BitString × BitString =>
      appendSuffixSelector q.1 q.2) := by
  exact (Primrec.list_append.comp Primrec.fst Primrec.snd).to_comp.partrec

/-- A string given its length-`k` prefix costs at most the suffix length plus a constant. -/
theorem condK_of_take_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (y : BitString) (k : ℕ),
      condK V y (y.take k) ≤
        (((y.drop k).length + C : ℕ) : ENat) := by
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV
      appendSuffixSelector appendSuffixSelector_partrec
  refine ⟨C, fun y k => ?_⟩
  have hmem : y ∈ appendSuffixSelector (y.take k) (y.drop k) := by
    simp [appendSuffixSelector]
  simpa [Nat.cast_add] using
    hC (y.take k) (y.drop k) y hmem
end Kolmogorov
