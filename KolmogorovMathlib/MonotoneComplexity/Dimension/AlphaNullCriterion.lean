/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.LSCAux
import KolmogorovMathlib.MonotoneComplexity.Dimension.LowComplexityCover
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Infra
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison
import KolmogorovMathlib.MonotoneComplexity.SharedCoding

/-!
# The prefix-complexity criterion for effective `α`-nullness (SUV §5.8, p. 173)

**SUV Problem 169.**  The largest effectively `α`-null set consists of the
sequences `ω` for which the difference `α n - K((ω)_n)` has no upper bound.

Both halves are proved here, each as a statement about a single sequence.

* `isEffectiveAlphaNull_setOf_unbounded_gap`: the set of all sequences with
  unbounded gap *is* effectively `α`-null.  Its level-`ε` cover consists of the
  strings `x` with `K(x) < ⌊α l(x)⌋ - (den ε + 1)`, each emitted once, at the
  first stage at which a short program for it appears; the Kraft inequality for
  prefix complexity (`KPPlain_kraft_sum_le_one`) bounds the total `α`-weight of
  that cover by `∑_x 2^{-K(x)} · 2^{-(den ε + 1)} ≤ 2^{-(den ε + 1)} < ε`.
* `exists_lt_alpha_mul_sub_KPPlain_of_isEffectiveAlphaNull`: a sequence covered
  by effectively `α`-null covers has unbounded gap.  The covers of accuracy
  `2^{-(2m+2)}`, for all `m` at once, are turned into one Kraft-Chaitin request
  stream that asks for a code of length `⌊α l(z)⌋ - m` for the `m`-th level: the
  total weight is `∑_m 2^{m+1} · 2^{-(2m+2)} = 1`, so
  `exists_const_KPPlain_le_of_kraft_le_one` gives `K(z) ≤ ⌊α l(z)⌋ - m + O(1)`
  for every interval `Ω_z` of every level, and the intervals of the `m`-th level
  containing `ω` witness a gap of at least `m - O(1)`.

The source's hint is the Levin-Schnorr criterion; the proof above is the same
argument with the a priori probability replaced by its Kraft-Chaitin form, which
is what the repository provides for prefix complexity.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ## Dyadic estimates -/

/-- Every power of two in `ℝ≥0∞` is at least `1`. -/
lemma one_le_two_pow_enn (k : ℕ) : (1 : ℝ≥0∞) ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ 2 ^ k * 2 := by (gcongr; norm_num)

/-- Truncated subtraction in the exponent only increases the dyadic weight. -/
lemma inv_two_pow_sub_le_alphaNull (a m : ℕ) :
    ((2 : ℝ≥0∞)⁻¹) ^ (a - m) ≤ 2 ^ m * ((2 : ℝ≥0∞)⁻¹) ^ a := by
  by_cases h : m ≤ a
  · have hsplit : a = m + (a - m) := by omega
    calc ((2 : ℝ≥0∞)⁻¹) ^ (a - m)
        = (2 ^ m * ((2 : ℝ≥0∞)⁻¹) ^ m) * ((2 : ℝ≥0∞)⁻¹) ^ (a - m) := by
          rw [two_pow_mul_inv_two_pow, one_mul]
      _ = 2 ^ m * (((2 : ℝ≥0∞)⁻¹) ^ m * ((2 : ℝ≥0∞)⁻¹) ^ (a - m)) := by ring
      _ = 2 ^ m * ((2 : ℝ≥0∞)⁻¹) ^ a := by rw [← pow_add, ← hsplit]
      _ ≤ 2 ^ m * ((2 : ℝ≥0∞)⁻¹) ^ a := le_rfl
  · have hlt : a < m := by omega
    have h0 : a - m = 0 := by omega
    have hsplit : m = a + (m - a) := by omega
    rw [h0, pow_zero]
    calc (1 : ℝ≥0∞) = 2 ^ a * ((2 : ℝ≥0∞)⁻¹) ^ a := (two_pow_mul_inv_two_pow a).symm
      _ = (2 ^ a * 1) * ((2 : ℝ≥0∞)⁻¹) ^ a := by rw [mul_one]
      _ ≤ (2 ^ a * 2 ^ (m - a)) * ((2 : ℝ≥0∞)⁻¹) ^ a := by
          gcongr
          exact one_le_two_pow_enn _
      _ = 2 ^ m * ((2 : ℝ≥0∞)⁻¹) ^ a := by rw [← pow_add, ← hsplit]

/-- The extended-real value of `1 / 2 ^ k` is `2 ^ (-k)`. -/
lemma ofReal_one_div_two_pow (k : ℕ) :
    ENNReal.ofReal ((1 : ℝ) / 2 ^ k) = ((2 : ℝ≥0∞)⁻¹) ^ k := by
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  rw [one_div, ← inv_pow, ENNReal.ofReal_pow (by norm_num)]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The `α`-weight of an interval whose string has prefix complexity below
`⌊α l(x)⌋ - d` is at most `2^{-K(x)} · 2^{-d}`. -/
lemma intervalAlphaMass_le_complexityWeight_mul {α : ℚ} (hα : 0 < α) {U : Map} {x : BitString}
    {d : ℕ} (h : KPPlain U x < ((alphaFloor α x.length - d : ℕ) : ℕ∞)) :
    intervalAlphaMass ((α : ℚ) : ℝ) x
      ≤ complexityWeight (KPPlain U x) * ((2 : ℝ≥0∞)⁻¹) ^ d := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, KPPlain U x = (k : ℕ∞) := by
    rcases eq_or_ne (KPPlain U x) ⊤ with htop | hne
    · rw [htop] at h; simp at h
    · exact (WithTop.ne_top_iff_exists.mp hne).imp fun k hk => hk.symm
  rw [hk] at h ⊢
  have hkl : k < alphaFloor α x.length - d := by exact_mod_cast h
  have hsum : k + d ≤ alphaFloor α x.length := by omega
  have hfloor : ((alphaFloor α x.length : ℕ) : ℝ) ≤ (x.length : ℝ) * ((α : ℚ) : ℝ) := by
    have := (alphaFloor_spec α hα x.length).1
    rw [mul_comm]
    exact this
  have hmass : intervalAlphaMass ((α : ℚ) : ℝ) x ≤ ((2 : ℝ≥0∞)⁻¹) ^ alphaFloor α x.length :=
    intervalAlphaMass_le_inv_two_pow hfloor
  have hsplit : alphaFloor α x.length = (k + d) + (alphaFloor α x.length - (k + d)) := by omega
  calc intervalAlphaMass ((α : ℚ) : ℝ) x ≤ ((2 : ℝ≥0∞)⁻¹) ^ alphaFloor α x.length := hmass
    _ = ((2 : ℝ≥0∞)⁻¹) ^ (k + d) * ((2 : ℝ≥0∞)⁻¹) ^ (alphaFloor α x.length - (k + d)) := by
        rw [← pow_add, ← hsplit]
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ (k + d) * 1 := by gcongr; exact inv_two_pow_le_one _
    _ = complexityWeight ((k : ℕ∞)) * ((2 : ℝ≥0∞)⁻¹) ^ d := by
        rw [mul_one, complexityWeight_coe, pow_add]

/-! ## The stage approximation of prefix complexity -/

/-- The stage function for prefix complexity, in the `(threshold, string)` order
that `firstStage` expects. -/
lemma exists_stage_KPPlain_lt (U : Map) (hU : isDecompressor U) :
    ∃ chk : ℕ × BitString → ℕ → Bool, Computable₂ chk ∧
      (∀ q s t, s ≤ t → chk q s = true → chk q t = true) ∧
      (∀ q : ℕ × BitString, KPPlain U q.2 < (q.1 : ℕ∞) ↔ ∃ s, chk q s = true) := by
  have hswap : Computable (fun p : ℕ × BitString => (p.2, p.1)) :=
    Computable.pair Computable.snd Computable.fst
  exact ((isRE_KPPlain_lt hU).comp_computable hswap).exists_stageApprox

/-! ## The cover of the set of unbounded gap -/

/-- The level-`ε` cover of SUV Problem 169: the string coded by the first
component of `j` is emitted at the stage coded by the second component, provided
that stage is the first one at which a program for it of length below
`⌊α l(x)⌋ - (den ε + 1)` appears. -/
def gapCover (chk : ℕ × BitString → ℕ → Bool) (α : ℚ) (ε : ℚ) (j : ℕ) : Option BitString :=
  bif firstStage chk
        (alphaFloor α (natToBitString (Nat.unpair j).1).length - (ε.den + 1))
        (natToBitString (Nat.unpair j).1) (Nat.unpair j).2 then
    some (natToBitString (Nat.unpair j).1)
  else none

/-- The string component of the gap cover, read off the first component of the unpaired index, is
computable. -/
lemma computable_gapCoverString :
    Computable (fun p : ℚ × ℕ => natToBitString (Nat.unpair p.2).1) :=
  computable_natToBitString.comp ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd)

/-- The complexity threshold used by the gap cover at a given precision and index is computable. -/
lemma computable_gapCoverThreshold (α : ℚ) :
    Computable (fun p : ℚ × ℕ =>
      alphaFloor α (natToBitString (Nat.unpair p.2).1).length - (p.1.den + 1)) := by
  have hlen : Computable (fun p : ℚ × ℕ => (natToBitString (Nat.unpair p.2).1).length) :=
    Primrec.list_length.to_comp.comp computable_gapCoverString
  have hfloor : Computable (fun n : ℕ => alphaFloor α n) :=
    (Primrec.nat_div.comp (Primrec.nat_mul.comp (Primrec.const α.num.toNat) Primrec.id)
      (Primrec.const α.den)).to_comp
  have hden : Computable (fun p : ℚ × ℕ => p.1.den + 1) :=
    Primrec.nat_add.to_comp.comp (computable_ratDen.comp Computable.fst) (Computable.const 1)
  exact Primrec.nat_sub.to_comp.comp (hfloor.comp hlen) hden

/-- For a computable membership check the gap cover is computable in the precision and the index. -/
lemma computable₂_gapCover {chk : ℕ × BitString → ℕ → Bool} (hchk : Computable₂ chk) (α : ℚ) :
    Computable₂ (gapCover chk α) := by
  have hstage : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
  have hfs : Computable (fun p : ℚ × ℕ =>
      firstStage chk (alphaFloor α (natToBitString (Nat.unpair p.2).1).length - (p.1.den + 1))
        (natToBitString (Nat.unpair p.2).1) (Nat.unpair p.2).2) :=
    ((computable_firstStage hchk).comp
      (Computable.pair (Computable.pair (computable_gapCoverThreshold α)
        computable_gapCoverString) hstage)).of_eq fun p => rfl
  exact (Computable.cond hfs (Computable.option_some.comp computable_gapCoverString)
    (Computable.const none)).of_eq fun p => rfl

/-- The value of the cover at the index `⟨a, b⟩`. -/
lemma coverAlphaMass_gapCover_pair {chk : ℕ × BitString → ℕ → Bool} {α ε : ℚ} (a b : ℕ) :
    coverAlphaMass ((α : ℚ) : ℝ) (gapCover chk α ε (Nat.pair a b))
      = if firstStage chk (alphaFloor α (natToBitString a).length - (ε.den + 1))
            (natToBitString a) b = true then
          intervalAlphaMass ((α : ℚ) : ℝ) (natToBitString a) else 0 := by
  cases hb : firstStage chk (alphaFloor α (natToBitString a).length - (ε.den + 1))
      (natToBitString a) b <;>
    simp [gapCover, Nat.unpair_pair, hb]

/-- **The total `α`-weight of the level-`ε` cover** is at most `2^{-(den ε + 1)}`:
the Kraft inequality for prefix complexity. -/
lemma tsum_coverAlphaMass_gapCover_le {chk : ℕ × BitString → ℕ → Bool} {U : Map}
    (hU : IsOptimalPrefixConditional U)
    (hmono : ∀ q s t, s ≤ t → chk q s = true → chk q t = true)
    (hspec : ∀ q : ℕ × BitString, KPPlain U q.2 < (q.1 : ℕ∞) ↔ ∃ s, chk q s = true)
    {α : ℚ} (hα : 0 < α) (ε : ℚ) :
    (∑' j, coverAlphaMass ((α : ℚ) : ℝ) (gapCover chk α ε j))
      ≤ ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) := by
  have hstep : ∀ a : ℕ,
      (∑' b, coverAlphaMass ((α : ℚ) : ℝ) (gapCover chk α ε (Nat.pair a b)))
        ≤ complexityWeight (KPPlain U (natToBitString a)) * ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) := by
    intro a
    refine tsum_le_of_subsingleton_support ?_ ?_
    · intro b
      rw [coverAlphaMass_gapCover_pair]
      split_ifs with hb
      · have hlt : KPPlain U (natToBitString a)
            < ((alphaFloor α (natToBitString a).length - (ε.den + 1) : ℕ) : ℕ∞) :=
          (hspec (alphaFloor α (natToBitString a).length - (ε.den + 1), natToBitString a)).2
            ⟨b, firstStage_imp hb⟩
        exact intervalAlphaMass_le_complexityWeight_mul hα hlt
      · exact zero_le
    · intro b b' hb hb'
      have key : ∀ u : ℕ, coverAlphaMass ((α : ℚ) : ℝ) (gapCover chk α ε (Nat.pair a u)) ≠ 0 →
          firstStage chk (alphaFloor α (natToBitString a).length - (ε.den + 1))
            (natToBitString a) u = true := by
        intro u hu
        by_contra hcon
        exact hu (by rw [coverAlphaMass_gapCover_pair]; simp [hcon])
      exact firstStage_unique hmono (key b hb) (key b' hb')
  calc (∑' j, coverAlphaMass ((α : ℚ) : ℝ) (gapCover chk α ε j))
      = ∑' a, ∑' b, coverAlphaMass ((α : ℚ) : ℝ) (gapCover chk α ε (Nat.pair a b)) :=
        tsum_nat_pair _
    _ ≤ ∑' a, complexityWeight (KPPlain U (natToBitString a)) * ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) :=
        ENNReal.tsum_le_tsum hstep
    _ = (∑' a, complexityWeight (KPPlain U (natToBitString a))) * ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) :=
        ENNReal.tsum_mul_right
    _ = (∑' x : BitString, complexityWeight (KPPlain U x)) * ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) := by
        congr 1
        exact tsum_comp_natToBitString (fun x => complexityWeight (KPPlain U x))
    _ ≤ 1 * ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) := by
        gcongr
        exact KPPlain_kraft_sum_le_one U hU.isPrefixDecompressor
    _ = ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) := one_mul _

/-- **The level-`ε` cover covers every sequence of unbounded gap.** -/
lemma mem_iUnion_gapCover {chk : ℕ × BitString → ℕ → Bool} {U : Map}
    (hU : IsOptimalPrefixConditional U)
    (hspec : ∀ q : ℕ × BitString, KPPlain U q.2 < (q.1 : ℕ∞) ↔ ∃ s, chk q s = true)
    {α : ℚ} (hα : 0 < α) (ε : ℚ) {w : CantorSeq}
    (hw : ∀ C : ℝ, ∃ n : ℕ, C < ((α : ℚ) : ℝ) * n - ((KPPlain U (cantorPrefix w n)).toNat : ℝ)) :
    w ∈ ⋃ j, (gapCover chk α ε j).elim (∅ : Set CantorSeq) cantorCylinder := by
  obtain ⟨n, hn⟩ := hw ((ε.den : ℝ) + 2)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, KPPlain U (cantorPrefix w n) = (k : ℕ∞) :=
    (WithTop.ne_top_iff_exists.mp
      (KPPlain_ne_top_of_isOptimalPrefixConditional hU (cantorPrefix w n))).imp
      fun k hk => hk.symm
  have hkn : ((KPPlain U (cantorPrefix w n)).toNat : ℝ) = (k : ℝ) := by rw [hk]; simp
  rw [hkn] at hn
  have hfloor : ((α : ℚ) : ℝ) * n < ((alphaFloor α n : ℕ) : ℝ) + 1 :=
    (alphaFloor_spec α hα n).2
  have hnat : k + ε.den + 2 ≤ alphaFloor α n := by
    have hcast : ((k + ε.den + 2 : ℕ) : ℝ) < ((alphaFloor α n : ℕ) : ℝ) + 1 := by
      push_cast
      linarith
    have h2 : (k + ε.den + 2 : ℕ) < alphaFloor α n + 1 := by exact_mod_cast hcast
    omega
  have hxlen : (cantorPrefix w n).length = n := cantorPrefix_length w n
  have hlt : KPPlain U (cantorPrefix w n)
      < ((alphaFloor α (cantorPrefix w n).length - (ε.den + 1) : ℕ) : ℕ∞) := by
    rw [hk, hxlen]
    have hkk : k < alphaFloor α n - (ε.den + 1) := by omega
    exact_mod_cast hkk
  obtain ⟨t, ht⟩ := exists_firstStage
    ((hspec (alphaFloor α (cantorPrefix w n).length - (ε.den + 1), cantorPrefix w n)).1 hlt)
  refine Set.mem_iUnion.2 ⟨Nat.pair (bitStringToNat (cantorPrefix w n)) t, ?_⟩
  have hval : gapCover chk α ε (Nat.pair (bitStringToNat (cantorPrefix w n)) t)
      = some (cantorPrefix w n) := by
    simp only [gapCover, Nat.unpair_pair, natToBitString_bitStringToNat, ht, cond_true]
  rw [hval]
  exact mem_cantorCylinder_cantorPrefix w n

/-- **SUV Problem 169, first half** (§5.8, p. 173).  The set of sequences whose
gap `α n - K((ω)_n)` is unbounded is effectively `α`-null. -/
theorem isEffectiveAlphaNull_setOf_unbounded_gap (U : Map) (hU : IsOptimalPrefixConditional U)
    (α : ℚ) (hα : 0 < α) :
    IsEffectiveAlphaNull ((α : ℚ) : ℝ)
      {w : CantorSeq | ∀ C : ℝ, ∃ n : ℕ,
        C < ((α : ℚ) : ℝ) * n - ((KPPlain U (cantorPrefix w n)).toNat : ℝ)} := by
  obtain ⟨chk, hchkc, hmono, hspec⟩ := exists_stage_KPPlain_lt U hU.isDecompressor
  refine ⟨gapCover chk α, computable₂_gapCover hchkc α, fun ε hε => ⟨?_, ?_⟩⟩
  · intro w hw
    exact mem_iUnion_gapCover hU hspec hα ε hw
  · have hne0 : ((2 : ℝ≥0∞)⁻¹) ^ ε.den ≠ 0 :=
      pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by norm_num))
    have hnetop : ((2 : ℝ≥0∞)⁻¹) ^ ε.den ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by norm_num))
    have hhalf : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by norm_num)
    calc (∑' j, coverAlphaMass ((α : ℚ) : ℝ) (gapCover chk α ε j))
        ≤ ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + 1) := tsum_coverAlphaMass_gapCover_le hU hmono hspec hα ε
      _ = ((2 : ℝ≥0∞)⁻¹) ^ ε.den * (2 : ℝ≥0∞)⁻¹ := pow_succ _ _
      _ < ((2 : ℝ≥0∞)⁻¹) ^ ε.den * 1 := ENNReal.mul_lt_mul_right hne0 hnetop hhalf
      _ = ((2 : ℝ≥0∞)⁻¹) ^ ε.den := mul_one _
      _ ≤ ENNReal.ofReal (ε : ℝ) := by
          rw [← dyadicValue_one_eq_inv_two_pow']
          exact dyadicValue_den_le_rat hε

/-! ## From covers of all accuracies to the complexity bound -/

/-- The accuracy used at the `m`-th level of the cover: `2^{-(2m+2)}`. -/
def gapAcc (m : ℕ) : ℚ := (1 : ℚ) / 2 ^ (2 * m + 2)

/-- The accuracy parameter used at stage `m` is a positive rational. -/
lemma gapAcc_pos (m : ℕ) : 0 < gapAcc m := by
  unfold gapAcc
  positivity

/-- The stage-wise accuracy parameter is computable. -/
lemma computable_gapAcc : Computable gapAcc := by
  have hexp : Computable (fun m : ℕ => 2 * m + 2) :=
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 2)).to_comp
  refine (lscComputable_dyadicRat.comp (Computable.pair (Computable.const 1) hexp)).of_eq ?_
  intro m
  unfold gapAcc
  norm_num

/-- The accuracy parameter at stage `m` has value `2 ^ (-(2m + 2))`. -/
lemma ofReal_gapAcc (m : ℕ) :
    ENNReal.ofReal ((gapAcc m : ℚ) : ℝ) = ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2) := by
  have hcast : ((gapAcc m : ℚ) : ℝ) = (1 : ℝ) / 2 ^ (2 * m + 2) := by
    unfold gapAcc
    push_cast
    ring
  rw [hcast, ofReal_one_div_two_pow]

/-- All the levels of a cover, enumerated by one computable function. -/
def gapStream (I : ℚ → ℕ → Option BitString) (j : ℕ) : Option BitString :=
  I (gapAcc (Nat.unpair j).1) (Nat.unpair j).2

/-- The code length requested for the `j`-th interval: `⌊α l(z)⌋` shortened by
the level of the interval. -/
def gapLen (α : ℚ) (I : ℚ → ℕ → Option BitString) (j : ℕ) : ℕ :=
  alphaFloor α ((gapStream I j).elim 0 List.length) - (Nat.unpair j).1

/-- The merged enumeration at index `⟨m, k⟩` returns the `k`-th string of the cover at accuracy
`gapAcc m`. -/
lemma gapStream_pair (I : ℚ → ℕ → Option BitString) (m k : ℕ) :
    gapStream I (Nat.pair m k) = I (gapAcc m) k := by
  simp [gapStream, Nat.unpair_pair]

/-- The length budget attached to index `⟨m, k⟩` is the `α`-scaled length of the enumerated string
minus `m`. -/
lemma gapLen_pair (α : ℚ) (I : ℚ → ℕ → Option BitString) (m k : ℕ) :
    gapLen α I (Nat.pair m k)
      = alphaFloor α ((I (gapAcc m) k).elim 0 List.length) - m := by
  simp [gapLen, gapStream_pair, Nat.unpair_pair]

/-- For a computable family of covers the merged enumeration is computable. -/
lemma computable_gapStream {I : ℚ → ℕ → Option BitString} (hI : Computable₂ I) :
    Computable (gapStream I) :=
  (hI.comp (computable_gapAcc.comp (Primrec.fst.comp Primrec.unpair).to_comp)
    (Primrec.snd.comp Primrec.unpair).to_comp).of_eq fun _j => rfl

/-- For a computable family of covers the length budget of the merged enumeration is computable. -/
lemma computable_gapLen (α : ℚ) {I : ℚ → ℕ → Option BitString} (hI : Computable₂ I) :
    Computable (gapLen α I) := by
  have hmap : Computable (fun j : ℕ => (gapStream I j).map List.length) :=
    Computable.option_map (computable_gapStream hI)
      (Primrec.list_length.to_comp.comp Computable.snd)
  have hlen : Computable (fun j : ℕ => (gapStream I j).elim 0 List.length) :=
    (Computable.option_getD hmap (Computable.const 0)).of_eq fun j => by
      cases h : gapStream I j <;> simp
  have hfloor : Computable (fun n : ℕ => alphaFloor α n) :=
    (Primrec.nat_div.comp (Primrec.nat_mul.comp (Primrec.const α.num.toNat) Primrec.id)
      (Primrec.const α.den)).to_comp
  exact Primrec.nat_sub.to_comp.comp (hfloor.comp hlen)
    (Primrec.fst.comp Primrec.unpair).to_comp

/-- **The Kraft weight of the shortened requests is at most `1`.**  The `m`-th
level has `α`-weight below `2^{-(2m+2)}`, its dyadic `⌊α l⌋`-weight is therefore
below `2^{-(2m+1)}`, and shortening the requests by `m` multiplies it by `2^m`,
leaving `2^{-(m+1)}`; these sum to `1`. -/
lemma kraft_gapStream {I : ℚ → ℕ → Option BitString} {α : ℚ} (hα : 0 < α)
    (hI : ∀ ε : ℚ, 0 < ε →
      (∑' k, coverAlphaMass ((α : ℚ) : ℝ) (I ε k)) < ENNReal.ofReal (ε : ℝ)) :
    (∑' j, (gapStream I j).elim 0 (fun _ => ((2 : ℝ≥0∞)⁻¹) ^ gapLen α I j)) ≤ 1 := by
  have hlevel : ∀ m : ℕ,
      (∑' k, (gapStream I (Nat.pair m k)).elim 0
        (fun _ => ((2 : ℝ≥0∞)⁻¹) ^ gapLen α I (Nat.pair m k)))
          ≤ ((2 : ℝ≥0∞)⁻¹) ^ (m + 1) := by
    intro m
    have hterm : ∀ k : ℕ, (gapStream I (Nat.pair m k)).elim 0
        (fun _ => ((2 : ℝ≥0∞)⁻¹) ^ gapLen α I (Nat.pair m k))
          ≤ 2 ^ m * ((I (gapAcc m) k).elim 0 (alphaFloorMass α)) := by
      intro k
      rw [gapStream_pair, gapLen_pair]
      cases hIk : I (gapAcc m) k with
      | none => simp
      | some z =>
          simp only [Option.elim, alphaFloorMass]
          exact inv_two_pow_sub_le_alphaNull _ _
    have hfloormass : (∑' k, ((I (gapAcc m) k).elim 0 (alphaFloorMass α)))
        ≤ 2 * ∑' k, coverAlphaMass ((α : ℚ) : ℝ) (I (gapAcc m) k) := by
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun k => ?_
      cases hIk : I (gapAcc m) k with
      | none => simp
      | some z =>
          simpa [coverAlphaMass, intervalAlphaMass] using alphaFloorMass_le_two_mul α hα z
    have hacc : (∑' k, coverAlphaMass ((α : ℚ) : ℝ) (I (gapAcc m) k))
        ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2) := by
      rw [← ofReal_gapAcc m]
      exact le_of_lt (hI (gapAcc m) (gapAcc_pos m))
    have halg : (2 : ℝ≥0∞) ^ m * (2 * ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2))
        = ((2 : ℝ≥0∞)⁻¹) ^ (m + 1) := by
      have h1 : (2 : ℝ≥0∞) ^ m * (2 * ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2))
          = (2 ^ (m + 1) * ((2 : ℝ≥0∞)⁻¹) ^ (m + 1)) * ((2 : ℝ≥0∞)⁻¹) ^ (m + 1) := by
        rw [show 2 * m + 2 = (m + 1) + (m + 1) by ring, pow_add, pow_succ]
        ring
      rw [h1, two_pow_mul_inv_two_pow, one_mul]
    calc (∑' k, (gapStream I (Nat.pair m k)).elim 0
        (fun _ => ((2 : ℝ≥0∞)⁻¹) ^ gapLen α I (Nat.pair m k)))
        ≤ ∑' k, 2 ^ m * ((I (gapAcc m) k).elim 0 (alphaFloorMass α)) :=
          ENNReal.tsum_le_tsum hterm
      _ = 2 ^ m * ∑' k, ((I (gapAcc m) k).elim 0 (alphaFloorMass α)) := ENNReal.tsum_mul_left
      _ ≤ 2 ^ m * (2 * ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2)) := by
          gcongr
          exact le_trans hfloormass (by gcongr)
      _ = ((2 : ℝ≥0∞)⁻¹) ^ (m + 1) := halg
  calc (∑' j, (gapStream I j).elim 0 (fun _ => ((2 : ℝ≥0∞)⁻¹) ^ gapLen α I j))
      = ∑' m, ∑' k, (gapStream I (Nat.pair m k)).elim 0
          (fun _ => ((2 : ℝ≥0∞)⁻¹) ^ gapLen α I (Nat.pair m k)) := tsum_nat_pair _
    _ ≤ ∑' m : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (m + 1) := ENNReal.tsum_le_tsum hlevel
    _ = (∑' m : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ m) * (2 : ℝ≥0∞)⁻¹ := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun m => pow_succ _ _
    _ = 1 := by
        rw [tsum_geometric_inv_two]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- **SUV Problem 169, second half** (§5.8, p. 173).  A sequence whose singleton
is effectively `α`-null has unbounded gap `α n - K((ω)_n)`. -/
theorem exists_lt_alpha_mul_sub_KPPlain_of_isEffectiveAlphaNull (U : Map)
    (hU : IsOptimalPrefixConditional U) (α : ℚ) (hα : 0 < α) {w : CantorSeq}
    (h : IsEffectiveAlphaNull ((α : ℚ) : ℝ) {w}) (C : ℝ) :
    ∃ n : ℕ, C < ((α : ℚ) : ℝ) * n - ((KPPlain U (cantorPrefix w n)).toNat : ℝ) := by
  obtain ⟨I, hIcomp, hI⟩ := h
  obtain ⟨c, hc⟩ := exists_const_KPPlain_le_of_kraft_le_one U hU (gapStream I)
    (computable_gapStream hIcomp) (gapLen α I) (computable_gapLen α hIcomp)
    (kraft_gapStream hα (fun ε hε => (hI ε hε).2))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, C + (c : ℝ) < (m : ℝ) := exists_nat_gt (C + (c : ℝ))
  obtain ⟨k, z, hIk, hmem⟩ :
      ∃ (k : ℕ) (z : BitString), I (gapAcc m) k = some z ∧ w ∈ cantorCylinder z := by
    have hw : w ∈ ⋃ k, (I (gapAcc m) k).elim (∅ : Set CantorSeq) cantorCylinder :=
      (hI (gapAcc m) (gapAcc_pos m)).1 rfl
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hw
    cases hIk : I (gapAcc m) k with
    | none => rw [hIk] at hk; simp at hk
    | some z => exact ⟨k, z, hIk, by rw [hIk] at hk; exact hk⟩
  have hz : cantorPrefix w z.length = z := (isCantorPrefix_iff_cantorPrefix_eq z w).1 hmem
  have hmass : intervalAlphaMass ((α : ℚ) : ℝ) z < ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2) := by
    calc intervalAlphaMass ((α : ℚ) : ℝ) z
        = coverAlphaMass ((α : ℚ) : ℝ) (I (gapAcc m) k) := by rw [hIk]; rfl
      _ ≤ ∑' k', coverAlphaMass ((α : ℚ) : ℝ) (I (gapAcc m) k') := ENNReal.le_tsum k
      _ < ENNReal.ofReal ((gapAcc m : ℚ) : ℝ) := (hI (gapAcc m) (gapAcc_pos m)).2
      _ = ((2 : ℝ≥0∞)⁻¹) ^ (2 * m + 2) := ofReal_gapAcc m
  have hlong : ((2 * m + 2 : ℕ) : ℝ) < (z.length : ℝ) * ((α : ℚ) : ℝ) :=
    lt_mul_length_of_intervalAlphaMass_lt hmass
  have hfloorle : ((alphaFloor α z.length : ℕ) : ℝ) ≤ ((α : ℚ) : ℝ) * (z.length : ℝ) :=
    (alphaFloor_spec α hα z.length).1
  have hfloorgt : ((α : ℚ) : ℝ) * (z.length : ℝ) < ((alphaFloor α z.length : ℕ) : ℝ) + 1 :=
    (alphaFloor_spec α hα z.length).2
  have hmle : m ≤ alphaFloor α z.length := by
    have hcomm : (z.length : ℝ) * ((α : ℚ) : ℝ) = ((α : ℚ) : ℝ) * (z.length : ℝ) :=
      mul_comm _ _
    have h1 : ((2 * m + 2 : ℕ) : ℝ) < ((alphaFloor α z.length : ℕ) : ℝ) + 1 := by
      linarith [hcomm, hlong, hfloorgt]
    have h2 : (2 * m + 2 : ℕ) < alphaFloor α z.length + 1 := by exact_mod_cast h1
    omega
  have hKP : KPPlain U z ≤ ((gapLen α I (Nat.pair m k) + c : ℕ) : ℕ∞) :=
    hc (Nat.pair m k) z (by rw [gapStream_pair]; exact hIk)
  have hLval : gapLen α I (Nat.pair m k) = alphaFloor α z.length - m := by
    rw [gapLen_pair, hIk]
    rfl
  rw [hLval] at hKP
  obtain ⟨kk, hkk⟩ : ∃ kk : ℕ, KPPlain U z = (kk : ℕ∞) :=
    (WithTop.ne_top_iff_exists.mp
      (KPPlain_ne_top_of_isOptimalPrefixConditional hU z)).imp fun kk hkk => hkk.symm
  have hkkle : kk ≤ (alphaFloor α z.length - m) + c := by
    rw [hkk] at hKP
    exact_mod_cast hKP
  refine ⟨z.length, ?_⟩
  rw [hz, hkk]
  have htoNat : ((kk : ℕ∞).toNat : ℝ) = (kk : ℝ) := by simp
  rw [htoNat]
  have hsub : ((alphaFloor α z.length - m : ℕ) : ℝ)
      = ((alphaFloor α z.length : ℕ) : ℝ) - (m : ℝ) := Nat.cast_sub hmle
  have hkkreal : (kk : ℝ) ≤ ((alphaFloor α z.length : ℕ) : ℝ) - (m : ℝ) + (c : ℝ) := by
    have : ((kk : ℕ) : ℝ) ≤ (((alphaFloor α z.length - m) + c : ℕ) : ℝ) := by exact_mod_cast hkkle
    rw [Nat.cast_add, hsub] at this
    linarith
  linarith

end Kolmogorov
