/-
Copyright (c) 2024 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Authors
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.MonotoneComplexity.APrioriAtoms.HaltStream
import KolmogorovMathlib.MonotoneComplexity.APrioriAtoms.LowerBound
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.Prefix.Properties

/-!
# The gap: no converse bound, and the atom masses are not lower semicomputable

The word `haltWord c n` has prefix complexity at least `n - O(1)`: from it one reads the
parameter `n` and a stage by which every halting program of length at most `n` has halted, hence
all their outputs, hence the first word `missingWord` of length `n + 1` that is none of them —
a word of complexity above `n`.  Its atom, on the other hand, has mass at least `c / (n+1)(n+2)`,
because the sequences `haltStream c n` are computable uniformly in `n` and can be mixed with the
computable weights `1/(n+1)(n+2)`.  The two bounds together show that no constant `C` satisfies
`atomMass x ≤ C * m x`, and therefore that `atomMass` — a discrete semimeasure by
`tsum_atomMass_le_one` — is **not** lower semicomputable: passing to the limit along an infinite
branch does not preserve that property.

Source: the note `apriori-atoms.md`, sections "Почему обратная оценка неверна", "Неограниченный
разрыв" and "Почему нельзя применить максимальность m"; SUV Chapter 5, §5.2.
-/

open scoped ENNReal

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### A word that no short program prints -/

/-- The word `y` is none of the outputs that the programs of length at most `n` produce within
`t` stages.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
def notSnapshotOutput (c : Code) (n t : ℕ) (y : BitString) : Bool :=
  decide ((snapshotCodes c n t).countP (fun z => decide (z = y)) = 0)

/-- The predicate `notSnapshotOutput` says what its name says. -/
theorem notSnapshotOutput_iff {c : Code} {n t : ℕ} {y : BitString} :
    notSnapshotOutput c n t y = true ↔ y ∉ snapshotCodes c n t := by
  simp only [notSnapshotOutput, decide_eq_true_eq, List.countP_eq_zero, decide_eq_true_eq]
  constructor
  · intro h hy
    exact h y hy rfl
  · intro h z hz hzy
    exact h (hzy ▸ hz)

/-- The first word of length `n + 1` that no program of length at most `n` produces within `t`
stages.  "First" is the order of `exactLengthPrograms (n + 1)`, not the lexicographic order of
the note: any fixed computable order does, and no statement below depends on the choice.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
def missingWord (c : Code) (n t : ℕ) : BitString :=
  (exactLengthPrograms (n + 1)).getD
    ((exactLengthPrograms (n + 1)).findIdx (notSnapshotOutput c n t)) []

/-- Fewer than `2 ^ (n + 1)` words are produced within `t` stages by the programs of length at
most `n`. -/
theorem length_snapshotCodes_lt (c : Code) (n t : ℕ) :
    (snapshotCodes c n t).length < 2 ^ (n + 1) := by
  have h1 : (snapshotCodes c n t).length ≤ (boundedPrograms n).length := by
    simpa [snapshotCodes] using List.length_filterMap_le (runOut c t) (boundedPrograms n)
  exact lt_of_le_of_lt h1 (length_boundedPrograms_lt n)

/-- **Pigeonhole.**  There are `2 ^ (n + 1)` words of length `n + 1` and fewer produced words,
so some word of length `n + 1` is missing from the snapshot.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem exists_notSnapshotOutput (c : Code) (n t : ℕ) :
    ∃ y ∈ exactLengthPrograms (n + 1), notSnapshotOutput c n t y = true := by
  by_contra hall
  push Not at hall
  have hsub : exactLengthPrograms (n + 1) ⊆ snapshotCodes c n t := by
    intro y hy
    by_contra hmiss
    exact hall y hy (notSnapshotOutput_iff.mpr hmiss)
  have hle := ((exactLengthPrograms_nodup (n + 1)).subperm hsub).length_le
  rw [length_exactLengthPrograms] at hle
  exact (Nat.not_lt.mpr hle) (length_snapshotCodes_lt c n t)

/-- The chosen word has length `n + 1` and is one of the words of that length. -/
theorem missingWord_mem (c : Code) (n t : ℕ) :
    missingWord c n t ∈ exactLengthPrograms (n + 1) := by
  have hex := exists_notSnapshotOutput c n t
  have hlt : (exactLengthPrograms (n + 1)).findIdx (notSnapshotOutput c n t) <
      (exactLengthPrograms (n + 1)).length := List.findIdx_lt_length_of_exists hex
  rw [missingWord, List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

/-- The chosen word is not among the outputs of the short programs. -/
theorem missingWord_notSnapshotOutput (c : Code) (n t : ℕ) :
    notSnapshotOutput c n t (missingWord c n t) = true := by
  have hex := exists_notSnapshotOutput c n t
  have hlt : (exactLengthPrograms (n + 1)).findIdx (notSnapshotOutput c n t) <
      (exactLengthPrograms (n + 1)).length := List.findIdx_lt_length_of_exists hex
  rw [missingWord, List.getD_eq_getElem _ _ hlt]
  exact List.findIdx_getElem

/-- The chosen word has length `n + 1`. -/
@[simp] theorem length_missingWord (c : Code) (n t : ℕ) :
    (missingWord c n t).length = n + 1 :=
  exactLengthPrograms_length_eq _ _ (missingWord_mem c n t)

/-- The predicate behind `missingWord` is primitive recursive in all of its arguments. -/
private theorem primrec_notSnapshotOutput (c : Code) :
    Primrec₂ (fun (q : ℕ × ℕ) (y : BitString) => notSnapshotOutput c q.1 q.2 y) := by
  have hsnap : Primrec (fun r : (ℕ × ℕ) × BitString => snapshotCodes c r.1.1 r.1.2) :=
    (snapshotCodes_primrec c).comp Primrec.fst
  have heq : Primrec₂ (fun (r : (ℕ × ℕ) × BitString) (z : BitString) => decide (z = r.2)) :=
    (PrimrecRel.decide Primrec.eq).comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  have hcount := list_countP_primrec hsnap heq
  exact (PrimrecRel.decide Primrec.eq).comp hcount (Primrec.const 0)

/-- **The missing word is computable from the parameter and the stage.**

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem computable_missingWord (c : Code) : Computable₂ (missingWord c) := by
  have hlist : Primrec (fun q : ℕ × ℕ => exactLengthPrograms (q.1 + 1)) :=
    primrec_exactLengthPrograms.comp (Primrec.succ.comp Primrec.fst)
  have hidx : Primrec (fun q : ℕ × ℕ =>
      (exactLengthPrograms (q.1 + 1)).findIdx (notSnapshotOutput c q.1 q.2)) :=
    Primrec.list_findIdx hlist (primrec_notSnapshotOutput c)
  exact ((Primrec.list_getD ([] : BitString)).comp hlist hidx).to_comp

/-! ### The complexity of the halting word -/

/-- Stage `t` has seen every halting program of length at most `n`: simulating the short
programs for `t` stages produces all of their outputs.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
def StageComplete (c : Code) (n t : ℕ) : Prop :=
  ∀ p ∈ boundedPrograms n, (∃ s, haltsWithin c s p = true) → haltsWithin c t p = true

/-- The last discovery stage of the parameter `n` has seen every halting program of length at
most `n`. -/
theorem stageComplete_lastStage (c : Code) (n : ℕ) : StageComplete c n (lastStage c n) :=
  fun _ hp hs => haltsWithin_lastStage hp hs.choose_spec

private lemma runOut_eq_of_haltsWithin {c : Code} {s t : ℕ} {p y : BitString}
    (hs : runOut c s p = some y) (ht : haltsWithin c t p = true) :
    runOut c t p = some y := by
  unfold runOut at hs ⊢
  rw [Option.bind_eq_some_iff] at hs
  obtain ⟨a, ha, hay⟩ := hs
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ht
  have hab : a = b := by
    have ha' := Code.evaln_mono (le_max_left s t) ha
    have hb' := Code.evaln_mono (le_max_right s t) hb
    exact Option.some.inj (ha'.symm.trans hb')
  rw [hb, ← hab]
  exact hay

/-- **`K(y_n) > n`.**  A word of length `n + 1` that no program of length at most `n` prints has
prefix complexity above `n`.  Stated for the prefix complexity `KPPlain` of an optimal prefix
decompressor whose code is `c`.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem KPPlain_missingWord_gt (U : Map) (hU : IsOptimalPrefixConditional U) (c : Code)
    (hc : IsCodeFor c U) (n t : ℕ) (ht : StageComplete c n t) :
    (n : ℕ∞) < KPPlain U (missingWord c n t) := by
  have _hU := hU
  rw [KPPlain, KP, condK_gt_iff]
  intro p hp hprod
  have hpmem : p ∈ boundedPrograms n := (mem_boundedPrograms_iff p n).mpr hp
  obtain ⟨s, hs⟩ := runOut_complete hc hprod
  have hhalt : haltsWithin c t p = true := by
    apply ht p hpmem
    refine ⟨s, ?_⟩
    unfold haltsWithin
    unfold runOut at hs
    rw [Option.bind_eq_some_iff] at hs
    exact Option.isSome_iff_exists.mpr ⟨hs.choose, hs.choose_spec.1⟩
  have hrun : runOut c t p = some (missingWord c n t) :=
    runOut_eq_of_haltsWithin hs hhalt
  have hmem : missingWord c n t ∈ snapshotCodes c n t := by
    rw [snapshotCodes, List.mem_filterMap]
    exact ⟨p, hpmem, hrun⟩
  exact (notSnapshotOutput_iff.mp (missingWord_notSnapshotOutput c n t)) hmem

private def leadingNat (x : BitString) : ℕ :=
  (x.takeWhile id).length

private theorem primrec_leadingNat : Primrec leadingNat := by
  exact Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id)

private theorem leadingNat_eq_of_natCode_prefix {n : ℕ} {x : BitString}
    (h : natCode n <+: x) : leadingNat x = n := by
  obtain ⟨p, rfl⟩ := h
  simp [leadingNat, natCode]

private def missingWordDecoder (c : Code) (x : BitString) : BitString :=
  missingWord c (leadingNat x) (x.length - (natCode (leadingNat x)).length)

private theorem computable_missingWordDecoder (c : Code) :
    Computable (missingWordDecoder c) := by
  have hlen : Primrec (fun x : BitString => x.length) := Primrec.list_length
  have hcodeLen : Primrec (fun x : BitString => (natCode (leadingNat x)).length) :=
    Primrec.list_length.comp (primrec_natCode.comp primrec_leadingNat)
  have hstage : Computable (fun x : BitString =>
      x.length - (natCode (leadingNat x)).length) :=
    (Primrec.nat_sub.comp hlen hcodeLen).to_comp
  exact (Computable₂.comp (computable_missingWord c) primrec_leadingNat.to_comp hstage).of_eq
    (fun _ => rfl)

/-- **`y_n` is computed from `x_n` by one fixed algorithm.**  The word `x_n` carries the code of
`n` in front and its length gives the last stage, so the missing word is a computable function
of `x_n` alone.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem exists_computable_missingWord_of_haltWord (c : Code) :
    ∃ g : BitString → BitString, Computable g ∧
      ∀ n, g (haltWord c n) = missingWord c n (lastStage c n) := by
  refine ⟨missingWordDecoder c, computable_missingWordDecoder c, fun n => ?_⟩
  rw [missingWordDecoder, leadingNat_eq_of_natCode_prefix (natCode_prefix_haltWord c n),
    lastStage_eq_length_sub]

/-- **`K(x_n) ≥ n - O(1)`.**  The prefix complexity of the halting word is at least `n` up to an
additive constant.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem exists_const_KPPlain_haltWord_ge (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c U) :
    ∃ k : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ KPPlain U (haltWord c n) + (k : ℕ∞) := by
  obtain ⟨g, hg, hgn⟩ := exists_computable_missingWord_of_haltWord c
  obtain ⟨k, hk⟩ := KPPlain_map_le U hU g hg
  refine ⟨k, fun n => ?_⟩
  have h1 : (n : ℕ∞) < KPPlain U (missingWord c n (lastStage c n)) :=
    KPPlain_missingWord_gt U hU c hc n (lastStage c n) (stageComplete_lastStage c n)
  have h2 : KPPlain U (missingWord c n (lastStage c n)) ≤ KPPlain U (haltWord c n) + (k : ℕ∞) := by
    rw [← hgn n]
    exact hk (haltWord c n)
  exact le_trans (le_of_lt h1) h2

private lemma prefixComplexityWeight_le_of_le_add (U : Map) (x : BitString) (n k : ℕ)
    (h : (n : ℕ∞) ≤ KPPlain U x + (k : ℕ∞)) :
    prefixComplexityWeight U x ≤
      (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ n := by
  have hw := complexityWeight_le_of_le h
  rw [complexityWeight_add_nat, complexityWeight_coe] at hw
  have hcancel : (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ k = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow]
  rw [prefixComplexityWeight, ← KPPlain_eq_KP]
  calc
    complexityWeight (KPPlain U x) = ((2 : ℝ≥0∞) ^ k *
        (2 : ℝ≥0∞)⁻¹ ^ k) * complexityWeight (KPPlain U x) := by
      rw [hcancel, one_mul]
    _ = (2 : ℝ≥0∞) ^ k *
        (complexityWeight (KPPlain U x) * (2 : ℝ≥0∞)⁻¹ ^ k) := by ring
    _ ≤ (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ n := by gcongr

/-- **`m(x_n) ≤ 2^{-n+O(1)}`.**  Through the coding theorem the complexity lower bound becomes
an upper bound on the discrete a priori probability of the halting word.

Source: the note `apriori-atoms.md`, section "Большая сложность конечного слова"; SUV
Chapter 5, §5.2. -/
theorem exists_const_universalSemimeasure_haltWord_le (m : BitString → ℝ≥0∞)
    (hm : IsUniversalSemimeasure m) (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c U) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, m (haltWord c n) ≤ C * (2 : ℝ≥0∞)⁻¹ ^ n := by
  obtain ⟨k, hk⟩ := exists_const_KPPlain_haltWord_ge U hU c hc
  obtain ⟨d, hd⟩ := lowerSemicomputableSemimeasure_le_prefixComplexityWeight hm.1 hU
  refine ⟨(2 : ℝ≥0∞) ^ (d + k), ENNReal.pow_ne_top (by simp), fun n => ?_⟩
  have hcancel : (2 : ℝ≥0∞) ^ d * (2 : ℝ≥0∞)⁻¹ ^ d = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow]
  calc
    m (haltWord c n) = (2 : ℝ≥0∞) ^ d *
        ((2 : ℝ≥0∞)⁻¹ ^ d * m (haltWord c n)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ d * prefixComplexityWeight U (haltWord c n) := by
      gcongr
      exact hd (haltWord c n)
    _ ≤ (2 : ℝ≥0∞) ^ d *
        ((2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ n) := by
      gcongr
      exact prefixComplexityWeight_le_of_le_add U (haltWord c n) n k (hk n)
    _ = (2 : ℝ≥0∞) ^ (d + k) * (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [pow_add]
      ring

/-! ### The mass of the atom of the halting word -/

/-- The computable weights `1/(n+1)(n+2)`, which sum to one.

Source: the note `apriori-atoms.md`, section "Неограниченный разрыв"; SUV Chapter 5, §5.2. -/
noncomputable def natWeight (n : ℕ) : ℝ≥0∞ := 1 / ((n + 1) * (n + 2))

/-- Every weight is positive. -/
theorem natWeight_ne_zero (n : ℕ) : natWeight n ≠ 0 := by
  have h : ((n : ℝ≥0∞) + 1) * ((n : ℝ≥0∞) + 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  simp [natWeight, h]

private lemma sum_range_natWeight (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (1 : ℝ) / (((n + 1) * (n + 2) : ℕ) : ℝ)) = 1 - 1 / (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : ((N : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((N : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

/-- The weights `1/(n+1)(n+2)` sum to **at most** one, which is what the mixture needs; the
telescoping sum is in fact exactly one, but only the inequality is recorded here.

Source: the note `apriori-atoms.md`, section "Неограниченный разрыв"; SUV Chapter 5, §5.2. -/
theorem tsum_natWeight_le_one : ∑' n : ℕ, natWeight n ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  have hterm : ∀ n : ℕ, natWeight n =
      ENNReal.ofReal (1 / (((n + 1) * (n + 2) : ℕ) : ℝ)) := by
    intro n
    have hpos : (0 : ℝ) < (((n + 1) * (n + 2) : ℕ) : ℝ) := by positivity
    rw [one_div, ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]
    simp [natWeight]
  calc
    (∑ n ∈ Finset.range N, natWeight n) =
        ENNReal.ofReal (∑ n ∈ Finset.range N,
          (1 : ℝ) / (((n + 1) * (n + 2) : ℕ) : ℝ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
      exact Finset.sum_congr rfl fun n _ => hterm n
    _ ≤ 1 := by
      rw [sum_range_natWeight N, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      apply ENNReal.ofReal_le_ofReal
      have hpos : (0 : ℝ) < 1 / (N + 1) := by positivity
      linarith

/-- The weights are lower semicomputable, read as a function of a bit string through
`decodeIndex`: the key `indexKey n = natCode n` carries the weight `1/(n+1)(n+2)` and every
other string carries `0`.

Source: the note `apriori-atoms.md`, section "Неограниченный разрыв"; SUV Chapter 5, §5.2. -/
theorem natWeight_isLSC : IsLSC fun (x : BitString) (_ : BitString) => indexWeight natWeight x := by
  let r : ℕ → ℚ := fun n => 1 / (n + 1) - 1 / (n + 2)
  have hr : Computable r := by
    have hfirst : Computable (fun n : ℕ => (1 / ((n : ℚ) + 1) : ℚ)) :=
      ComputableReals.computable_invSucc
    have hsecond : Computable (fun n : ℕ =>
        (1 / (((n + 1 : ℕ) : ℚ) + 1) : ℚ)) :=
      ComputableReals.computable_invSucc.comp Primrec.succ.to_comp
    have hsub : Computable (fun n : ℕ =>
        (1 / ((n : ℚ) + 1) : ℚ) - 1 / (((n + 1 : ℕ) : ℚ) + 1)) :=
      Computable₂.comp ComputableReals.computable_ratSub hfirst hsecond
    exact hsub.of_eq (fun n => by simp [r]; ring)
  have hv : IsLSC fun (x _ : BitString) =>
      ENNReal.ofReal ((r (bitStringToNat x) : ℚ) : ℝ) :=
    isLSC_ofReal_of_computable hr
  let φ : BitString → Option BitString := fun x =>
    (decodeIndex ℕ x).map natToBitString
  have hφ : Computable φ := by
    exact Computable.option_map (computable_decodeIndex ℕ)
      (computable_natToBitString.comp Computable.snd).to₂
  have hout := isLSC_option_elim hv hφ
  convert hout using 1
  funext x ctx
  simp only [φ, indexWeight]
  cases h : decodeIndex ℕ x with
  | none => simp
  | some n =>
      simp only [Option.elim_some, Option.map_some, bitStringToNat_natToBitString]
      rw [show r n = 1 / (((n + 1) * (n + 2) : ℕ) : ℚ) by
        dsimp [r]
        push_cast
        field_simp
        ring]
      rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
      have hpos : (0 : ℝ) < (((n + 1) * (n + 2) : ℕ) : ℝ) := by positivity
      rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_one, ENNReal.ofReal_natCast]
      simp [natWeight]

/-- The mixture of the sequences `α_n` with the weights `1/(n+1)(n+2)`.

Source: the note `apriori-atoms.md`, section "Неограниченный разрыв"; SUV Chapter 5, §5.2. -/
noncomputable def haltMixture (c : Code) : BitString → ℝ≥0∞ :=
  branchMixture natWeight (haltStream c)

/-- The mixture of the halting streams carries at most mass one at the root. -/
theorem haltMixture_root_le_one (c : Code) : haltMixture c [] ≤ 1 := by
  rw [haltMixture, branchMixture_root]
  exact tsum_natWeight_le_one

/-- The mixture of the halting streams is lower semicomputable. -/
theorem haltMixture_isLSC (c : Code) : IsLSC fun u _ => haltMixture c u :=
  branchMixture_isLSC natWeight (haltStream c) natWeight_isLSC (computable_haltStream c)

/-- **`f(x_n) ≥ c/(n+1)(n+2)`.**  The atom of the halting word is heavy: a probabilistic
algorithm draws `n` with probability `1/(n+1)(n+2)` and prints the computable sequence `α_n`.

Source: the note `apriori-atoms.md`, section "Неограниченный разрыв"; SUV Chapter 5, §5.2. -/
theorem exists_const_atomMass_haltWord_ge (c : Code) :
    ∃ d : ℝ≥0∞, d ≠ 0 ∧ ∀ n, d * natWeight n ≤ atomMass (haltWord c n) := by
  obtain ⟨d, hd0, _hdtop, hd⟩ := exists_const_le_universalContinuousSemimeasure
    (haltMixture_root_le_one c) (branchMixture_child_le natWeight (haltStream c))
    (haltMixture_isLSC c)
  refine ⟨d, hd0, fun n => ?_⟩
  refine le_atomMass fun k => ?_
  refine le_trans ?_ (hd (tailOnes (haltWord c n) k))
  gcongr
  refine le_branchMixture natWeight (haltStream c) n ?_
  rw [length_tailOnes, haltStream_eq_atomSeq]
  exact cantorPrefix_atomSeq _ k

/-! ### The gap and its two corollaries -/

private lemma sq_add_one_le_two_pow : ∀ t : ℕ, 5 ≤ t → t ^ 2 + 1 ≤ 2 ^ t := by
  intro t
  induction t with
  | zero => omega
  | succ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 5 with h5 | h5
    · interval_cases k <;> norm_num at *
    · have h1 := ih h5
      have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      nlinarith

private lemma pow_succ_le_two_pow (k : ℕ) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → (s + 1) ^ k ≤ 2 ^ s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, fun s _ => by simpa using Nat.one_le_two_pow⟩
  refine ⟨k * (2 * k + 6), fun s hs => ?_⟩
  set t := s / k with ht
  have hdm : k * (s / k) + s % k = s := Nat.div_add_mod s k
  have hmod : s % k < k := Nat.mod_lt s hk
  have hts : k * t ≤ s := by rw [ht]; omega
  have hst : s < k * (t + 1) := by
    rw [ht, Nat.mul_add, Nat.mul_one]
    omega
  have ht_ge : 2 * k + 6 ≤ t := by
    by_contra hcon
    push Not at hcon
    have : s < k * (2 * k + 6) := by
      calc
        s < k * (t + 1) := hst
        _ ≤ k * (2 * k + 6) := Nat.mul_le_mul_left k (by omega)
    omega
  have hpow := sq_add_one_le_two_pow t (by omega)
  have hbig : s + 1 ≤ 2 ^ t := by
    have hk2 : 2 * k ≤ t := by omega
    have h1 : k * (t + 1) ≤ t ^ 2 := by nlinarith
    omega
  calc
    (s + 1) ^ k ≤ (2 ^ t) ^ k := Nat.pow_le_pow_left hbig k
    _ = 2 ^ (t * k) := by rw [← pow_mul]
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; exact hts)

private lemma exists_const_mul_quadratic_lt_two_pow (C : ℕ) :
    ∃ n : ℕ, C * ((n + 1) * (n + 2)) < 2 ^ n := by
  obtain ⟨s₀, hs₀⟩ := pow_succ_le_two_pow 3
  let n := max s₀ (2 * C + 1)
  refine ⟨n, lt_of_lt_of_le ?_ (hs₀ n (le_max_left _ _))⟩
  have hn : 2 * C + 1 ≤ n := le_max_right _ _
  have hfactor : C * (n + 2) < (n + 1) ^ 2 := by nlinarith
  calc
    C * ((n + 1) * (n + 2)) = (n + 1) * (C * (n + 2)) := by ring
    _ < (n + 1) * (n + 1) ^ 2 := Nat.mul_lt_mul_of_pos_left hfactor (by omega)
    _ = (n + 1) ^ 3 := by ring

/-- The exponential beats the quadratic: for any finite `A` and any positive `d` some index has
`A · 2^{-n} < d/(n+1)(n+2)`.

Source: the note `apriori-atoms.md`, section "Неограниченный разрыв"; SUV Chapter 5, §5.2. -/
theorem exists_mul_inv_two_pow_lt_natWeight (A d : ℝ≥0∞) (hA : A ≠ ⊤) (hd : d ≠ 0) :
    ∃ n : ℕ, A * (2 : ℝ≥0∞)⁻¹ ^ n < d * natWeight n := by
  by_cases hdtop : d = ⊤
  · refine ⟨0, ?_⟩
    calc
      A * (2 : ℝ≥0∞)⁻¹ ^ 0 = A := by simp
      _ < ⊤ := lt_top_iff_ne_top.mpr hA
      _ = d * natWeight 0 := by simp [hdtop, natWeight]
  obtain ⟨C, hC⟩ := exists_nat_gt (A.toReal / d.toReal)
  obtain ⟨n, hn⟩ := exists_const_mul_quadratic_lt_two_pow C
  refine ⟨n, ?_⟩
  have hleft : A * (2 : ℝ≥0∞)⁻¹ ^ n ≠ ⊤ :=
    ENNReal.mul_ne_top hA (ENNReal.pow_ne_top (by simp))
  have hright : d * natWeight n ≠ ⊤ :=
    ENNReal.mul_ne_top hdtop (by simp [natWeight])
  rw [← ENNReal.toReal_lt_toReal hleft hright]
  have hdreal : 0 < d.toReal := ENNReal.toReal_pos hd hdtop
  have hCmul : A.toReal < (C : ℝ) * d.toReal := (div_lt_iff₀ hdreal).mp hC
  have hnreal : (C : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 2)) < 2 ^ n := by
    exact_mod_cast hn
  have hq : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hwreal : (natWeight n).toReal =
      1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    norm_num [natWeight, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_add]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, hwreal]
  simp only [one_div, inv_pow]
  change A.toReal / 2 ^ n < d.toReal /
    (((n : ℝ) + 1) * ((n : ℝ) + 2))
  apply (div_lt_div_iff₀ hpow hq).mpr
  calc
    A.toReal * (((n : ℝ) + 1) * ((n : ℝ) + 2)) <
        ((C : ℝ) * d.toReal) * (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      gcongr
    _ = d.toReal * ((C : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by ring
    _ < d.toReal * 2 ^ n := by
      gcongr
      nlinarith [hnreal]

/-- **No converse bound.**  For every constant `C` there is a string whose atom is heavier than
`C` times its discrete a priori probability; in particular `sup_x f(x)/m(x) = ∞`.

Source: the note `apriori-atoms.md`, section "Неограниченный разрыв"; SUV Chapter 5, §5.2. -/
theorem forall_const_exists_lt_atomMass (m : BitString → ℝ≥0∞) (hm : IsUniversalSemimeasure m) :
    ∀ C : ℝ≥0∞, C ≠ ⊤ → ∃ x : BitString, C * m x < atomMass x := by
  intro C hC
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c, hc⟩ : ∃ c : Code, IsCodeFor c U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨C₂, hC₂, hle⟩ := exists_const_universalSemimeasure_haltWord_le m hm U hU c hc
  obtain ⟨d, hd0, hd⟩ := exists_const_atomMass_haltWord_ge c
  obtain ⟨n, hn⟩ :=
    exists_mul_inv_two_pow_lt_natWeight (C * C₂) d (ENNReal.mul_ne_top hC hC₂) hd0
  refine ⟨haltWord c n, ?_⟩
  calc C * m (haltWord c n) ≤ C * (C₂ * (2 : ℝ≥0∞)⁻¹ ^ n) := by gcongr; exact hle n
    _ = C * C₂ * (2 : ℝ≥0∞)⁻¹ ^ n := by rw [mul_assoc]
    _ < d * natWeight n := hn
    _ ≤ atomMass (haltWord c n) := hd n

/-- **The atom masses are not lower semicomputable.**  They form a discrete semimeasure
(`tsum_atomMass_le_one`), so lower semicomputability would give a constant `C` with
`atomMass x ≤ C * m x`, which the gap forbids.

Source: the note `apriori-atoms.md`, section "Почему нельзя применить максимальность m"; SUV
Chapter 5, §5.2. -/
theorem not_isLowerSemicomputableSemimeasure_atomMass :
    ¬ IsLowerSemicomputableSemimeasure atomMass := by
  intro hlsc
  obtain ⟨m, hm⟩ := exists_universalSemimeasure
  obtain ⟨c, hc0, hdom⟩ := hm.2 atomMass hlsc
  have hc1 : min c 1 ≠ 0 := (lt_min hc0 (by norm_num)).ne'
  have hctop : min c 1 ≠ ⊤ := by
    have : min c 1 ≤ 1 := min_le_right c 1
    exact ne_top_of_le_ne_top ENNReal.one_ne_top this
  have hdom' : ∀ x, min c 1 * atomMass x ≤ m x := by
    intro x
    refine le_trans ?_ (hdom x)
    gcongr
    exact min_le_left c 1
  obtain ⟨x, hx⟩ := forall_const_exists_lt_atomMass m hm (min c 1)⁻¹
    (ENNReal.inv_ne_top.mpr hc1)
  have h2 : atomMass x ≤ (min c 1)⁻¹ * m x := by
    calc atomMass x = (min c 1)⁻¹ * (min c 1 * atomMass x) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc1 hctop, one_mul]
      _ ≤ (min c 1)⁻¹ * m x := by gcongr; exact hdom' x
  exact absurd hx (not_lt.mpr h2)

end Kolmogorov
