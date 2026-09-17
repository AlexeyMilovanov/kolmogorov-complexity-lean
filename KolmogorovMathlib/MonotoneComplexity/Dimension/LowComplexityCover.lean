/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.Basic
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinOnline

/-!
# Covers by strings of low plain complexity (SUV §5.8, pp. 174-175)

The `≤` half of Theorem 120 covers a singleton `{ω}` by the intervals `Ω_z` of
the strings `z` of length `n ≥ N` whose plain complexity is below `r·n`:

> "For each `n` we consider all `n`-bit strings that have complexity less than
> `rn`.  There are at most `O(2^{rn})` such strings.  The condition about
> lim inf guarantees that for infinitely many `n` the `n`-bit prefix of `ω` is
> in the corresponding list. … there are `O(2^{rn})` terms and each is
> `2^{-r'n}`, so the sum is `O(2^{(r-r')n})`, and we get a converging geometric
> series."  (SUV §5.8, pp. 174-175)

This module supplies that cover and its estimates, and - for the converse
inequality - the Kraft-Chaitin bound `C(x_k) ≤ r·l(x_k) + O(1)` for a computable
family of intervals of finite `r`-weight.  The `liminf` bookkeeping of both
inequalities lives in `Dimension/Hausdorff.lean`.

## Contents

* `exists_computable₂_plainKStage` — the *stage approximation* of the relation
  `plain complexity of `x` is below `k``: a computable, stage-monotone Boolean
  test whose union over the stages is the relation.  Proved from
  `MonotoneComplexity/REClosure.lean` (`IsRE.exists_stageApprox`), the
  r.e.-ness being `Partrec.graphIsRe` for the decompressor.
* `card_lowPlainK_level_le` — the counting bound: at most `2^k` strings of a
  fixed length have plain complexity below `k` (the source's `O(2^{rn})`).
* `tsum_inv_two_pow_natDiv` — the value `2·M` of the geometric-type series
  `∑_m (1/2)^{⌊m/M⌋}`, which is the "converging geometric series" of the source
  once the ratio `2^{r-r'}` is replaced by the dyadic `2^{-1/M}`, `M` an integer
  with `1/M ≤ r' - r`.
-/

namespace Kolmogorov

open MeasureTheory Encodable
open scoped ENNReal

/-! ## The stage approximation of "plain complexity below `k`" -/

/-- Plain complexity below a bound is the existence of a short program: this is
`sInf_lt_iff` for the set of program lengths. -/
lemma plainK_lt_iff_exists_program {V : Map} {x : BitString} {k : ℕ} :
    plainK V x < (k : ℕ∞) ↔ ∃ p : BitString, x ∈ V (p, []) ∧ p.length < k := by
  rw [plainK, condK, sInf_lt_iff]
  constructor
  · rintro ⟨n, ⟨p, hp, rfl⟩, hlt⟩
    exact ⟨p, hp, by exact_mod_cast hlt⟩
  · rintro ⟨p, hp, hlt⟩
    exact ⟨(p.length : ℕ∞), ⟨p, hp, rfl⟩, by exact_mod_cast hlt⟩

/-- The relation "`x` has plain complexity below `k`" is recursively enumerable,
uniformly in `k`: it is the projection of the graph of the decompressor along
the computable side condition `l(p) < k`. -/
lemma isRE_plainK_lt (V : Map) (hV : isDecompressor V) :
    IsRE (fun q : ℕ × BitString => plainK V q.2 < (q.1 : ℕ∞)) := by
  have hgraph : IsRE (fun p : (BitString × BitString) × BitString => p.2 ∈ V p.1) :=
    Partrec.graphIsRe V hV
  have hg : Computable (fun z : (ℕ × BitString) × BitString =>
      (((z.2, ([] : BitString)) : BitString × BitString), z.1.2)) := by
    exact Computable.pair
      (Computable.pair Computable.snd (Computable.const ([] : BitString)))
      (Computable.snd.comp Computable.fst)
  have hstep : IsRE (fun z : (ℕ × BitString) × BitString => z.1.2 ∈ V (z.2, [])) :=
    hgraph.comp_computable hg
  have hbool : Computable (fun z : (ℕ × BitString) × BitString =>
      decide (z.2.length < z.1.1)) :=
    (PrimrecRel.comp Primrec.nat_lt (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).decide.to_comp
  have hand : IsRE (fun z : (ℕ × BitString) × BitString =>
      decide (z.2.length < z.1.1) = true ∧ z.1.2 ∈ V (z.2, [])) :=
    hstep.and_computable hbool
  have hex : IsRE (fun q : ℕ × BitString => ∃ p : BitString,
      decide (p.length < q.1) = true ∧ q.2 ∈ V (p, [])) :=
    IsRE.exists_encodable (α := ℕ × BitString) (β := BitString)
      (R := fun q p => decide (p.length < q.1) = true ∧ q.2 ∈ V (p, [])) hand
  refine hex.of_iff ?_
  intro q
  rw [plainK_lt_iff_exists_program]
  constructor
  · rintro ⟨p, hlen, hp⟩
    exact ⟨p, hp, by simpa using hlen⟩
  · rintro ⟨p, hp, hlen⟩
    exact ⟨p, by simpa using hlen, hp⟩

/-- **The stage function for plain complexity** (the piece of SUV's proof of
Theorem 120 that "we consider all `n`-bit strings that have complexity less than
`rn`" needs in order to be an *algorithm*).

There is a computable Boolean test `chk (k, x) s`, monotone in the stage `s`,
which becomes true at some stage exactly for the strings `x` of plain complexity
below `k`.  Uniform in `k` and `x`. -/
theorem exists_computable₂_plainKStage (V : Map) (hV : isDecompressor V) :
    ∃ chk : ℕ × BitString → ℕ → Bool, Computable₂ chk ∧
      (∀ q s t, s ≤ t → chk q s = true → chk q t = true) ∧
      (∀ q : ℕ × BitString, plainK V q.2 < (q.1 : ℕ∞) ↔ ∃ s, chk q s = true) :=
  (isRE_plainK_lt V hV).exists_stageApprox

/-! ## The counting bound -/

open Classical in
/-- The strings of length `n` whose plain complexity is below `k`. -/
noncomputable def lowPlainKLevel (V : Map) (k n : ℕ) : Finset BitString :=
  (levelFinset n).filter (fun x => plainK V x < (k : ℕ∞))

/-- The level-`n` low-complexity set consists of the strings of length `n` with plain complexity
below `k`. -/
lemma mem_lowPlainKLevel {V : Map} {k n : ℕ} {x : BitString} :
    x ∈ lowPlainKLevel V k n ↔ x.length = n ∧ plainK V x < (k : ℕ∞) := by
  classical
  simp [lowPlainKLevel, mem_levelFinset]

/-- The powers of two below `2 ^ k` sum to `2 ^ k - 1`. -/
lemma sum_range_two_pow (k : ℕ) : (∑ j ∈ Finset.range k, 2 ^ j) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- **SUV §5.8, p. 174**: "There are at most `O(2^{rn})` such strings."  At most
`2^k` strings of any fixed length have plain complexity below `k`: a string of
complexity below `k` has a program of length `< k`, distinct strings have
distinct programs, and there are `2^k - 1` strings of length `< k`. -/
theorem card_lowPlainK_level_le (V : Map) (k n : ℕ) :
    (lowPlainKLevel V k n).card ≤ 2 ^ k := by
  classical
  set P : Finset BitString := (Finset.range k).biUnion levelFinset with hP
  have hcardP : P.card ≤ 2 ^ k := by
    refine le_trans Finset.card_biUnion_le ?_
    have hcongr : (∑ j ∈ Finset.range k, (levelFinset j).card)
        = ∑ j ∈ Finset.range k, 2 ^ j :=
      Finset.sum_congr rfl (fun j _ => card_levelFinset j)
    rw [hcongr]
    have h := sum_range_two_pow k
    omega
  have hwit : ∀ x ∈ lowPlainKLevel V k n,
      ∃ p : BitString, x ∈ V (p, []) ∧ p.length < k := by
    intro x hx
    exact plainK_lt_iff_exists_program.1 (mem_lowPlainKLevel.1 hx).2
  choose! f hf using hwit
  refine le_trans (Finset.card_le_card_of_injOn f ?_ ?_) hcardP
  · intro x hx
    exact Finset.mem_biUnion.2 ⟨(f x).length, Finset.mem_range.2 (hf x hx).2,
      mem_levelFinset.2 rfl⟩
  · intro x hx y hy hxy
    have hmx := (hf x hx).1
    have hmy := (hf y hy).1
    rw [hxy] at hmx
    exact Part.mem_unique hmx hmy

/-! ## The dyadic geometric series -/

/-- The geometric series of ratio `1/2` sums to `2`. -/
lemma tsum_geometric_inv_two : (∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ j) = 2 := by
  have h2 : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have h1 : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    rw [← h2, ENNReal.add_sub_cancel_right (by simp)]
  rw [ENNReal.tsum_geometric, h1, inv_inv]

/-- `∑_m (1/2)^{⌊m/M⌋} = 2M`: each value `(1/2)^j` occurs exactly `M` times.
This is SUV's "converging geometric series" (p. 175) in the form in which the
ratio `2^{r-r'}` has been replaced by the dyadic `2^{-1/M}` for an integer `M`
with `1/M ≤ r' - r`. -/
theorem tsum_inv_two_pow_natDiv (M : ℕ) (hM : 0 < M) :
    (∑' m : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (m / M)) = (M : ℝ≥0∞) * 2 := by
  have : NeZero M := ⟨hM.ne'⟩
  have hEq := (Nat.divModEquiv M).symm.tsum_eq (fun m : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ (m / M))
  rw [← hEq]
  have hfun : ∀ p : ℕ × Fin M,
      ((2 : ℝ≥0∞)⁻¹) ^ (((Nat.divModEquiv M).symm p) / M) = ((2 : ℝ≥0∞)⁻¹) ^ p.1 := by
    rintro ⟨j, i⟩
    congr 1
    have key : (j * M + (i : ℕ)) / M = j := by
      have h : ((i : ℕ) + M * j) / M = (i : ℕ) / M + j := Nat.add_mul_div_left _ _ hM
      rw [Nat.div_eq_of_lt i.isLt, Nat.zero_add] at h
      rw [show j * M + (i : ℕ) = (i : ℕ) + M * j from by ring]
      exact h
    simpa [Nat.divModEquiv] using key
  have hprod : (∑' p : ℕ × Fin M, ((2 : ℝ≥0∞)⁻¹) ^ p.1)
      = ∑' (a : ℕ), ∑' (_ : Fin M), ((2 : ℝ≥0∞)⁻¹) ^ a :=
    ENNReal.tsum_prod (f := fun (a : ℕ) (_ : Fin M) => ((2 : ℝ≥0∞)⁻¹) ^ a)
  rw [tsum_congr hfun, hprod]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left, tsum_geometric_inv_two]

/-! ## Elementary `ENNReal` facts used by the geometric estimate -/

/-- The product `2 ^ i * 2 ^ (-i)` is `1` in the extended reals. -/
lemma two_pow_mul_inv_two_pow (i : ℕ) :
    (2 : ℝ≥0∞) ^ i * ((2 : ℝ≥0∞)⁻¹) ^ i = 1 := by
  rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]

/-- `2^a · 2^{-b} ≤ 2^{-d}` whenever `a + d ≤ b`.  This is the level-by-level
form of the source's `O(2^{(r-r')n})`. -/
lemma two_pow_mul_inv_two_pow_le {a b d : ℕ} (h : a + d ≤ b) :
    (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞)⁻¹) ^ b ≤ ((2 : ℝ≥0∞)⁻¹) ^ d := by
  obtain ⟨e, he⟩ := Nat.le.dest h
  calc (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞)⁻¹) ^ b
      = (2 : ℝ≥0∞) ^ a * (((2 : ℝ≥0∞)⁻¹) ^ a * ((2 : ℝ≥0∞)⁻¹) ^ (d + e)) := by
        rw [← pow_add, show a + (d + e) = b from by omega]
    _ = ((2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞)⁻¹) ^ a) * ((2 : ℝ≥0∞)⁻¹) ^ (d + e) := by ring
    _ = ((2 : ℝ≥0∞)⁻¹) ^ (d + e) := by rw [two_pow_mul_inv_two_pow, one_mul]
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ d := inv_two_pow_antitone (Nat.le_add_right d e)

/-- The `α`-weight of an interval of length `n` is at most `2^{-b}` whenever
`b ≤ n·α`. -/
lemma intervalAlphaMass_le_inv_two_pow {α : ℝ} {x : BitString} {b : ℕ}
    (h : (b : ℝ) ≤ (x.length : ℝ) * α) :
    intervalAlphaMass α x ≤ ((2 : ℝ≥0∞)⁻¹) ^ b := by
  rw [intervalAlphaMass_eq_inv_two_pow, ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) x.length,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) b]
  exact ENNReal.rpow_le_rpow_of_exponent_ge (by norm_num) h

/-- A series with at most one nonzero term is bounded by that term's bound. -/
lemma tsum_le_of_subsingleton_support {f : ℕ → ℝ≥0∞} {v : ℝ≥0∞}
    (hle : ∀ t, f t ≤ v) (huniq : ∀ t t', f t ≠ 0 → f t' ≠ 0 → t = t') :
    (∑' t, f t) ≤ v := by
  by_cases hz : ∀ t, f t = 0
  · simp [hz]
  · push Not at hz
    obtain ⟨t₀, ht₀⟩ := hz
    rw [tsum_eq_single t₀ (fun b hb => by
      by_contra hcon
      exact hb (huniq b t₀ hcon ht₀))]
    exact hle t₀

/-- Splitting a series over `ℕ` along the Cantor pairing. -/
lemma tsum_nat_pair (f : ℕ → ℝ≥0∞) : (∑' j, f j) = ∑' a, ∑' b, f (Nat.pair a b) := by
  have h1 : (∑' p : ℕ × ℕ, f (Nat.pairEquiv p)) = ∑' j, f j := Nat.pairEquiv.tsum_eq f
  have h2 : (∑' p : ℕ × ℕ, f (Nat.pairEquiv p)) = ∑' p : ℕ × ℕ, f (Nat.pair p.1 p.2) :=
    tsum_congr (fun p => rfl)
  rw [← h1, h2]
  exact ENNReal.tsum_prod (f := fun a b => f (Nat.pair a b))

/-- `1/den q ≤ q` for a positive rational: the numerator is at least `1`. -/
lemma one_div_den_le_rat {q : ℚ} (hq : 0 < q) : (1 : ℝ) / (q.den : ℝ) ≤ (q : ℝ) := by
  have hden : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  have hnum : (1 : ℝ) ≤ (q.num : ℝ) := by exact_mod_cast Rat.num_pos.2 hq
  rw [Rat.cast_def, div_le_div_iff_of_pos_right hden]
  exact hnum

/-! ## The cover -/

/-- The test "`t` is the first stage at which `x` is found to have complexity
below `k`". -/
def firstStage (chk : ℕ × BitString → ℕ → Bool) (k : ℕ) (x : BitString) (t : ℕ) : Bool :=
  chk (k, x) t && (decide (t = 0) || decide (chk (k, x) (t - 1) = false))

/-- For a computable check the first stage at which it succeeds is computable. -/
lemma computable_firstStage {chk : ℕ × BitString → ℕ → Bool} (hchk : Computable₂ chk) :
    Computable (fun q : (ℕ × BitString) × ℕ => firstStage chk q.1.1 q.1.2 q.2) := by
  have hpair : Computable (fun q : (ℕ × BitString) × ℕ => ((q.1.1, q.1.2) : ℕ × BitString)) :=
    Computable.pair (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.fst)
  have h1 : Computable (fun q : (ℕ × BitString) × ℕ => chk (q.1.1, q.1.2) q.2) :=
    hchk.comp hpair Computable.snd
  have h2 : Computable (fun q : (ℕ × BitString) × ℕ => chk (q.1.1, q.1.2) (q.2 - 1)) :=
    hchk.comp hpair (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const 1))
  have h3 : Computable (fun q : (ℕ × BitString) × ℕ => decide (q.2 = 0)) :=
    ((PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 0)).decide).to_comp
  have h4 : Computable (fun q : (ℕ × BitString) × ℕ =>
      decide (chk (q.1.1, q.1.2) (q.2 - 1) = false)) := by
    refine (Computable.cond h2 (Computable.const false) (Computable.const true)).of_eq ?_
    intro q
    cases hb : chk (q.1.1, q.1.2) (q.2 - 1) <;> simp
  exact (Primrec₂.to_comp Primrec.and).comp h1 ((Primrec₂.to_comp Primrec.or).comp h3 h4)

/-- A first-stage success is in particular a success of the underlying check. -/
lemma firstStage_imp {chk : ℕ × BitString → ℕ → Bool} {k : ℕ} {x : BitString} {t : ℕ}
    (h : firstStage chk k x t = true) : chk (k, x) t = true := by
  unfold firstStage at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- At most one stage is the first one. -/
lemma firstStage_unique {chk : ℕ × BitString → ℕ → Bool}
    (hmono : ∀ q s t, s ≤ t → chk q s = true → chk q t = true) {k : ℕ} {x : BitString}
    {t t' : ℕ} (h : firstStage chk k x t = true) (h' : firstStage chk k x t' = true) :
    t = t' := by
  have key : ∀ u u' : ℕ, u < u' → firstStage chk k x u = true →
      firstStage chk k x u' = true → False := by
    intro u u' hlt hu hu'
    unfold firstStage at hu'
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hu'
    rcases hu'.2 with hz | hfalse
    · omega
    · have hmm : chk (k, x) (u' - 1) = true :=
        hmono (k, x) u (u' - 1) (by omega) (firstStage_imp hu)
      rw [hmm] at hfalse
      exact Bool.noConfusion hfalse
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd (key t t' hlt h h') (fun x => x)
  · exact heq
  · exact absurd (key t' t hgt h' h) (fun x => x)

/-- Some stage is the first one, as soon as the test ever succeeds. -/
lemma exists_firstStage {chk : ℕ × BitString → ℕ → Bool} {k : ℕ} {x : BitString}
    (h : ∃ s, chk (k, x) s = true) : ∃ t, firstStage chk k x t = true := by
  classical
  refine ⟨Nat.find h, ?_⟩
  have hspec := Nat.find_spec h
  unfold firstStage
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨hspec, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find h) with hz | hpos
  · exact Or.inl hz
  · refine Or.inr ?_
    have hlt : Nat.find h - 1 < Nat.find h := by omega
    have hmin := Nat.find_min h hlt
    simpa using hmin

/-- **The cover of SUV Theorem 120's first inequality** (§5.8, pp. 174-175):
for the accuracy `ε` it enumerates the strings of length `n ≥ M·(den ε + m₀)`
whose plain complexity is below `⌊r·n⌋`, each exactly once (at the first stage
at which its short program is found). -/
def lowCover (chk : ℕ × BitString → ℕ → Bool) (r : ℚ) (M m₀ : ℕ) (ε : ℚ) (j : ℕ) :
    Option BitString :=
  (levelEnum (M * (ε.den + m₀) + (Nat.unpair j).1) (Nat.unpair (Nat.unpair j).2).2).bind
    fun x => bif firstStage chk (alphaFloor r (M * (ε.den + m₀) + (Nat.unpair j).1)) x
      (Nat.unpair (Nat.unpair j).2).1 then some x else none

/-- For a computable check the low-complexity cover is computable in its two indices. -/
lemma computable₂_lowCover {chk : ℕ × BitString → ℕ → Bool} (hchk : Computable₂ chk)
    (r : ℚ) (M m₀ : ℕ) : Computable₂ (lowCover chk r M m₀) := by
  have hlevel : Computable (fun p : ℚ × ℕ => M * (p.1.den + m₀) + (Nat.unpair p.2).1) := by
    refine Primrec.nat_add.to_comp.comp ?_ ?_
    · exact Primrec.nat_mul.to_comp.comp (Computable.const M)
        (Primrec.nat_add.to_comp.comp (computable_ratDen.comp Computable.fst)
          (Computable.const m₀))
    · exact (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
  have hcode : Computable (fun p : ℚ × ℕ => (Nat.unpair (Nat.unpair p.2).2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp.comp
      Computable.snd
  have hstage : Computable (fun p : ℚ × ℕ => (Nat.unpair (Nat.unpair p.2).2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp.comp
      Computable.snd
  have hthr : Computable (fun p : ℚ × ℕ =>
      alphaFloor r (M * (p.1.den + m₀) + (Nat.unpair p.2).1)) := by
    have : Computable (fun n : ℕ => alphaFloor r n) :=
      (Primrec.nat_div.comp (Primrec.nat_mul.comp (Primrec.const r.num.toNat) Primrec.id)
        (Primrec.const r.den)).to_comp
    exact this.comp hlevel
  have hbase : Computable (fun p : ℚ × ℕ =>
      levelEnum (M * (p.1.den + m₀) + (Nat.unpair p.2).1)
        (Nat.unpair (Nat.unpair p.2).2).2) :=
    computable₂_levelEnum.comp hlevel hcode
  have hbranch : Computable₂ (fun (p : ℚ × ℕ) (x : BitString) =>
      bif firstStage chk (alphaFloor r (M * (p.1.den + m₀) + (Nat.unpair p.2).1)) x
        (Nat.unpair (Nat.unpair p.2).2).1 then some x else none) := by
    have htest : Computable (fun q : (ℚ × ℕ) × BitString =>
        firstStage chk (alphaFloor r (M * (q.1.1.den + m₀) + (Nat.unpair q.1.2).1)) q.2
          (Nat.unpair (Nat.unpair q.1.2).2).1) :=
      (computable_firstStage hchk).comp
        (Computable.pair (Computable.pair (hthr.comp Computable.fst) Computable.snd)
          (hstage.comp Computable.fst))
    exact (Computable.cond htest (Computable.option_some.comp Computable.snd)
      (Computable.const none)).to₂
  exact (Computable.option_bind hbase hbranch).to₂

/-! ## The `α`-weight of the cover -/

/-- `⌊r·n⌋ + ⌊n/den(r'-r)⌋ ≤ ⌊r'·n⌋`: the exponent gap of the source's
`2^{(r-r')n}`, in the dyadic form used here. -/
lemma alphaFloor_add_natDiv_le {r r' : ℚ} (hr : 0 < r) (hrr' : r < r') (n : ℕ) :
    alphaFloor r n + n / (r' - r).den ≤ alphaFloor r' n := by
  have hr' : 0 < r' := lt_trans hr hrr'
  have hδ : 0 < r' - r := sub_pos.2 hrr'
  set D : ℕ := (r' - r).den with hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (r' - r).pos
  have h1 : ((alphaFloor r n : ℕ) : ℝ) ≤ (r : ℝ) * n := (alphaFloor_spec r hr n).1
  have h2 : (r' : ℝ) * n < ((alphaFloor r' n : ℕ) : ℝ) + 1 := (alphaFloor_spec r' hr' n).2
  have h3 : (((n / D : ℕ)) : ℝ) ≤ (n : ℝ) / (D : ℝ) := Nat.cast_div_le
  have h4 : (1 : ℝ) / (D : ℝ) ≤ ((r' - r : ℚ) : ℝ) := one_div_den_le_rat hδ
  have h5 : (n : ℝ) / (D : ℝ) ≤ ((r' : ℝ) - (r : ℝ)) * n := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have := mul_le_mul_of_nonneg_left h4 hn
    rw [mul_one_div] at this
    calc (n : ℝ) / (D : ℝ) ≤ (n : ℝ) * ((r' - r : ℚ) : ℝ) := this
      _ = ((r' : ℝ) - (r : ℝ)) * n := by push_cast; ring
  have hkey : ((alphaFloor r n : ℕ) : ℝ) + (((n / D : ℕ)) : ℝ)
      < ((alphaFloor r' n : ℕ) : ℝ) + 1 := by
    have : ((alphaFloor r n : ℕ) : ℝ) + (((n / D : ℕ)) : ℝ) ≤ (r' : ℝ) * n := by
      calc ((alphaFloor r n : ℕ) : ℝ) + (((n / D : ℕ)) : ℝ)
          ≤ (r : ℝ) * n + ((r' : ℝ) - (r : ℝ)) * n := by
            exact add_le_add h1 (le_trans h3 h5)
        _ = (r' : ℝ) * n := by ring
    linarith
  have : alphaFloor r n + n / D < alphaFloor r' n + 1 := by exact_mod_cast hkey
  omega

section Weight

variable {V : Map} {chk : ℕ × BitString → ℕ → Bool}

/-- The `t`-sum over one code: at most one stage emits, and only for strings of
low complexity. -/
lemma tsum_stage_le (hmono : ∀ q s t, s ≤ t → chk q s = true → chk q t = true)
    (hspec : ∀ q : ℕ × BitString, plainK V q.2 < (q.1 : ℕ∞) ↔ ∃ s, chk q s = true)
    (α : ℝ) (r : ℚ) (M m₀ : ℕ) (ε : ℚ) (m c : ℕ) :
    (∑' t, coverAlphaMass α (lowCover chk r M m₀ ε (Nat.pair m (Nat.pair t c))))
      ≤ (levelEnum (M * (ε.den + m₀) + m) c).elim 0
          (fun x => if plainK V x < ((alphaFloor r (M * (ε.den + m₀) + m) : ℕ) : ℕ∞)
            then intervalAlphaMass α x else 0) := by
  set n := M * (ε.den + m₀) + m with hn
  set k := alphaFloor r n with hk
  have hunf : ∀ t, lowCover chk r M m₀ ε (Nat.pair m (Nat.pair t c))
      = (levelEnum n c).bind fun x => bif firstStage chk k x t then some x else none := by
    intro t
    unfold lowCover
    simp only [Nat.unpair_pair]
    rfl
  cases hlev : levelEnum n c with
  | none =>
    have : ∀ t, coverAlphaMass α (lowCover chk r M m₀ ε (Nat.pair m (Nat.pair t c))) = 0 := by
      intro t; rw [hunf t, hlev]; simp
    simp [this]
  | some x =>
    simp only [Option.elim_some]
    by_cases hlow : plainK V x < (k : ℕ∞)
    · rw [if_pos hlow]
      refine tsum_le_of_subsingleton_support (fun t => ?_) (fun t t' ht ht' => ?_)
      · rw [hunf t, hlev]
        simp only [Option.bind_some]
        cases hf : firstStage chk k x t <;> simp
      · have hne : ∀ u : ℕ,
            coverAlphaMass α (lowCover chk r M m₀ ε (Nat.pair m (Nat.pair u c))) ≠ 0 →
            firstStage chk k x u = true := by
          intro u hu
          cases hff : firstStage chk k x u with
          | true => rfl
          | false =>
            exfalso
            rw [hunf u, hlev] at hu
            simp only [Option.bind_some, hff, cond_false] at hu
            simp at hu
        exact firstStage_unique hmono (hne t ht) (hne t' ht')
    · rw [if_neg hlow]
      have : ∀ t, coverAlphaMass α (lowCover chk r M m₀ ε (Nat.pair m (Nat.pair t c))) = 0 := by
        intro t
        rw [hunf t, hlev]
        simp only [Option.bind_some]
        cases hf : firstStage chk k x t
        · simp
        · exact absurd ((hspec (k, x)).2 ⟨t, firstStage_imp hf⟩) hlow
      simp [this]

/-- The `c`-sum over one level: at most `2^k` strings, each of weight at most
`2^{-⌊r'·n⌋}` (the source's "`O(2^{rn})` terms and each is `2^{-r'n}`"). -/
lemma tsum_level_le (α : ℝ) (k n b : ℕ) (hb : (b : ℝ) ≤ (n : ℝ) * α) :
    (∑' c, (levelEnum n c).elim 0
        (fun x => if plainK V x < (k : ℕ∞) then intervalAlphaMass α x else 0))
      ≤ (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞)⁻¹) ^ b := by
  classical
  set S : Finset ℕ := (lowPlainKLevel V k n).image encode with hS
  set G : ℕ → ℝ≥0∞ := fun c => (levelEnum n c).elim 0
    (fun x => if plainK V x < (k : ℕ∞) then intervalAlphaMass α x else 0) with hG
  have hzero : ∀ c ∉ S, G c = 0 := by
    intro c hc
    cases hlev : levelEnum n c with
    | none => simp [hG, hlev]
    | some x =>
      simp only [hG, hlev, Option.elim_some]
      by_cases hlow : plainK V x < (k : ℕ∞)
      · exfalso
        obtain ⟨hlen, hcode⟩ := levelEnum_eq_some_iff.1 hlev
        exact hc (Finset.mem_image.2 ⟨x, mem_lowPlainKLevel.2 ⟨hlen, hlow⟩, hcode⟩)
      · rw [if_neg hlow]
  have hval : ∀ c ∈ S, G c ≤ ((2 : ℝ≥0∞)⁻¹) ^ b := by
    intro c hc
    cases hlev : levelEnum n c with
    | none => simp [hG, hlev]
    | some x =>
      simp only [hG, hlev, Option.elim_some]
      have hlen : x.length = n := (levelEnum_eq_some_iff.1 hlev).1
      have hbnd : intervalAlphaMass α x ≤ ((2 : ℝ≥0∞)⁻¹) ^ b := by
        refine intervalAlphaMass_le_inv_two_pow ?_
        rw [hlen]; exact hb
      by_cases hlow : plainK V x < (k : ℕ∞)
      · rw [if_pos hlow]; exact hbnd
      · rw [if_neg hlow]; exact zero_le
  rw [tsum_eq_sum hzero]
  refine le_trans (Finset.sum_le_card_nsmul S G _ hval) ?_
  rw [nsmul_eq_mul]
  have hcard : S.card ≤ 2 ^ k := by
    rw [hS, Finset.card_image_of_injective _ encode_injective]
    exact card_lowPlainK_level_le V k n
  have hcard' : (S.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ k := by
    calc (S.card : ℝ≥0∞) ≤ ((2 ^ k : ℕ) : ℝ≥0∞) := by exact_mod_cast hcard
      _ = (2 : ℝ≥0∞) ^ k := by push_cast; ring
  exact mul_le_mul' hcard' le_rfl

end Weight

/-! ## The cover of a singleton -/

/-- **SUV Theorem 120, the first inequality (§5.8, pp. 174-175)**, in the form
that isolates its effective content: if arbitrarily long prefixes of `ω` have
plain complexity below `⌊r·n⌋`, then `{ω}` is an effective `r'`-null set for
every rational `r' > r`.

The cover is the source's: for the accuracy `ε` take all strings of length
`n ≥ M·(den ε + m₀)` whose complexity is below `⌊r·n⌋`, where `M = den(r'-r)`.
Level `n` carries at most `2^{⌊rn⌋}` strings of weight `2^{-⌊r'n⌋}` each, so it
weighs at most `2^{-⌊n/M⌋}`, and `∑_m 2^{-⌊m/M⌋} = 2M` is the source's
"converging geometric series". -/
theorem isEffectiveAlphaNull_singleton_of_forall_exists_low (V : Map)
    (hV : isDecompressor V) (w : CantorSeq) (r r' : ℚ) (hr : 0 < r) (hrr' : r < r')
    (hcov : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      plainK V (cantorPrefix w n) < ((alphaFloor r n : ℕ) : ℕ∞)) :
    IsEffectiveAlphaNull ((r' : ℚ) : ℝ) {w} := by
  classical
  obtain ⟨chk, hchk, hmono, hspec⟩ := exists_computable₂_plainKStage V hV
  have hr' : 0 < r' := lt_trans hr hrr'
  have hδ : 0 < r' - r := sub_pos.2 hrr'
  set M : ℕ := (r' - r).den with hMdef
  have hMpos : 0 < M := (r' - r).pos
  set m₀ : ℕ := 2 * M + 2 with hm₀def
  refine ⟨lowCover chk r M m₀, computable₂_lowCover hchk r M m₀, fun ε hε => ⟨?_, ?_⟩⟩
  · -- the cover really covers `ω`
    obtain ⟨n, hnN, hlow⟩ := hcov (M * (ε.den + m₀))
    obtain ⟨t, ht⟩ := exists_firstStage
      ((hspec (alphaFloor r n, cantorPrefix w n)).1 hlow)
    refine Set.singleton_subset_iff.2 (Set.mem_iUnion.2
      ⟨Nat.pair (n - M * (ε.den + m₀)) (Nat.pair t (encode (cantorPrefix w n))), ?_⟩)
    have hn : M * (ε.den + m₀) + (n - M * (ε.den + m₀)) = n := by omega
    have hval : lowCover chk r M m₀ ε
        (Nat.pair (n - M * (ε.den + m₀)) (Nat.pair t (encode (cantorPrefix w n))))
        = some (cantorPrefix w n) := by
      unfold lowCover
      simp only [Nat.unpair_pair, hn]
      rw [levelEnum_encode (cantorPrefix_length w n)]
      simp only [Option.bind_some, ht, cond_true]
    rw [hval]
    exact mem_cantorCylinder_cantorPrefix w n
  · -- the `r'`-weight of the cover is below `ε`
    set F : ℕ → ℝ≥0∞ :=
      fun j => coverAlphaMass ((r' : ℚ) : ℝ) (lowCover chk r M m₀ ε j) with hF
    have hstep1 : (∑' j, F j) = ∑' m, ∑' s, F (Nat.pair m s) := tsum_nat_pair F
    have hstep2 : ∀ m : ℕ,
        (∑' s, F (Nat.pair m s)) = ∑' t, ∑' c, F (Nat.pair m (Nat.pair t c)) :=
      fun m => tsum_nat_pair (fun s => F (Nat.pair m s))
    have hstep3 : ∀ m : ℕ,
        (∑' t, ∑' c, F (Nat.pair m (Nat.pair t c)))
          = ∑' c, ∑' t, F (Nat.pair m (Nat.pair t c)) :=
      fun m => ENNReal.tsum_comm
    have hlevel : ∀ m : ℕ,
        (∑' c, ∑' t, F (Nat.pair m (Nat.pair t c)))
          ≤ ((2 : ℝ≥0∞)⁻¹) ^ ((M * (ε.den + m₀) + m) / M) := by
      intro m
      set n := M * (ε.den + m₀) + m with hn
      refine le_trans (ENNReal.tsum_le_tsum (fun c => tsum_stage_le hmono hspec _ r M m₀ ε m c))
        (le_trans (tsum_level_le (V := V) ((r' : ℚ) : ℝ) (alphaFloor r n) n
          (alphaFloor r' n) ?_) ?_)
      · have h := (alphaFloor_spec r' hr' n).1
        calc ((alphaFloor r' n : ℕ) : ℝ) ≤ (r' : ℝ) * n := h
          _ = (n : ℝ) * ((r' : ℚ) : ℝ) := by ring
      · exact two_pow_mul_inv_two_pow_le (alphaFloor_add_natDiv_le hr hrr' n)
    have hdiv : ∀ m : ℕ, (M * (ε.den + m₀) + m) / M = m / M + (ε.den + m₀) := by
      intro m
      rw [show M * (ε.den + m₀) + m = m + M * (ε.den + m₀) from by ring]
      exact Nat.add_mul_div_left _ _ hMpos
    have hsum : (∑' j, F j) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + m₀) * ((M : ℝ≥0∞) * 2) := by
      calc (∑' j, F j) = ∑' m, ∑' c, ∑' t, F (Nat.pair m (Nat.pair t c)) := by
            rw [hstep1]; exact tsum_congr (fun m => (hstep2 m).trans (hstep3 m))
        _ ≤ ∑' m : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ ((M * (ε.den + m₀) + m) / M) :=
            ENNReal.tsum_le_tsum hlevel
        _ = ∑' m : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (m / M) * ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + m₀) := by
            refine tsum_congr (fun m => ?_)
            rw [hdiv m, pow_add]
        _ = (∑' m : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (m / M)) * ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + m₀) :=
            ENNReal.tsum_mul_right
        _ = ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + m₀) * ((M : ℝ≥0∞) * 2) := by
            rw [tsum_inv_two_pow_natDiv M hMpos]; ring
    -- the numeric estimate
    have hMle : M ≤ 2 ^ (2 * M) := le_trans (by omega) (le_of_lt (Nat.lt_two_pow_self))
    have hMbound : (M : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * M) ≤ 1 := by
      have h1 : (M : ℝ≥0∞) ≤ ((2 ^ (2 * M) : ℕ) : ℝ≥0∞) := by exact_mod_cast hMle
      calc (M : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * M)
          ≤ ((2 ^ (2 * M) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * M) := mul_le_mul' h1 le_rfl
        _ = 1 := nat_two_pow_mul_inv_two_pow (2 * M)
    have hfinal : ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + m₀) * ((M : ℝ≥0∞) * 2)
        ≤ ((2 : ℝ≥0∞)⁻¹) ^ ε.den * (2 : ℝ≥0∞)⁻¹ := by
      have hexp : ε.den + m₀ = ε.den + (2 * M + 1) + 1 := by rw [hm₀def]; ring
      calc ((2 : ℝ≥0∞)⁻¹) ^ (ε.den + m₀) * ((M : ℝ≥0∞) * 2)
          = ((2 : ℝ≥0∞)⁻¹) ^ ε.den *
              ((M : ℝ≥0∞) * (2 * ((2 : ℝ≥0∞)⁻¹) ^ (2 * M + 2))) := by
            rw [hm₀def, pow_add]; ring
        _ = ((2 : ℝ≥0∞)⁻¹) ^ ε.den *
              ((M : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * M + 1)) := by
            rw [two_mul_inv_two_pow_succ]
        _ = ((2 : ℝ≥0∞)⁻¹) ^ ε.den *
              ((M : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * M) * (2 : ℝ≥0∞)⁻¹) := by
            rw [pow_succ]; ring
        _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ ε.den * (1 * (2 : ℝ≥0∞)⁻¹) :=
            mul_le_mul' le_rfl (mul_le_mul' hMbound le_rfl)
        _ = ((2 : ℝ≥0∞)⁻¹) ^ ε.den * (2 : ℝ≥0∞)⁻¹ := by rw [one_mul]
    have hstrict : ((2 : ℝ≥0∞)⁻¹) ^ ε.den * (2 : ℝ≥0∞)⁻¹ < ((2 : ℝ≥0∞)⁻¹) ^ ε.den := by
      have hne0 : ((2 : ℝ≥0∞)⁻¹) ^ ε.den ≠ 0 :=
        pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by norm_num))
      have hnetop : ((2 : ℝ≥0∞)⁻¹) ^ ε.den ≠ ⊤ :=
        ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by norm_num))
      have hhalf : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by norm_num)
      calc ((2 : ℝ≥0∞)⁻¹) ^ ε.den * (2 : ℝ≥0∞)⁻¹
          < ((2 : ℝ≥0∞)⁻¹) ^ ε.den * 1 := ENNReal.mul_lt_mul_right hne0 hnetop hhalf
        _ = ((2 : ℝ≥0∞)⁻¹) ^ ε.den := mul_one _
    have hden : ((2 : ℝ≥0∞)⁻¹) ^ ε.den ≤ ENNReal.ofReal (ε : ℝ) := by
      rw [← dyadicValue_one_eq_inv_two_pow']
      exact dyadicValue_den_le_rat hε
    exact lt_of_le_of_lt (le_trans hsum hfinal) (lt_of_lt_of_le hstrict hden)

/-! ### The Kraft-Chaitin machine of a cover of finite `r`-weight -/

/-- The request stream of a cover: for the `k`-th interval `Ω_z` ask for a
prefix-free code of length `⌊r·l(z)⌋ + B`. -/
private def coverRequest (r : ℚ) (B : ℕ) (E : ℕ → Option BitString) (k : ℕ) : Option ℕ :=
  (E k).map fun z => alphaFloor r z.length + B

private lemma computable_coverRequest (r : ℚ) (B : ℕ) {E : ℕ → Option BitString}
    (hE : Computable E) : Computable (coverRequest r B E) := by
  refine Computable.option_map hE ?_
  have h : Computable fun p : ℕ × BitString => alphaFloor r p.2.length + B :=
    (Primrec.nat_add.comp
      (Primrec.nat_div.comp
        (Primrec.nat_mul.comp (Primrec.const r.num.toNat)
          (Primrec.list_length.comp Primrec.snd))
        (Primrec.const r.den))
      (Primrec.const B)).to_comp
  exact h

/-- The Kraft weight of the request stream is `2^{-B}` times the dyadic
`⌊r·l⌋`-weight of the cover. -/
private lemma requestKraftWeight_coverRequest (r : ℚ) (B : ℕ) (E : ℕ → Option BitString) :
    requestKraftWeight (coverRequest r B E)
      = ((2 : ℝ≥0∞)⁻¹) ^ B * ∑' k, (E k).elim 0 (alphaFloorMass r) := by
  rw [requestKraftWeight, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  cases hEk : E k with
  | none => simp [coverRequest, hEk]
  | some z => simp [coverRequest, hEk, alphaFloorMass, pow_add, mul_comm]

/-- The decompressor read off an online Kraft-Chaitin allocation: the code
allocated to the `k`-th request is decompressed to the `k`-th string of the
cover.  Its domain is the set of allocated codes, which is prefix-free. -/
private def coverMachineDim (E alloc : ℕ → Option BitString) : Map :=
  fun q => (Nat.rfind fun n => Part.some (decide (alloc n = some q.1))).map
    fun n => (E n).getD ([] : BitString)

private lemma partrec_coverMachine {E alloc : ℕ → Option BitString}
    (hE : Computable E) (halloc : Computable alloc) :
    Partrec (coverMachineDim E alloc) := by
  have hp : Primrec fun p : Option BitString × Option BitString => decide (p.1 = p.2) := by
    have ⟨_, H⟩ : PrimrecRel (@Eq (Option BitString)) := Primrec.eq
    convert H
  have heq : Computable₂ fun o₁ o₂ : Option BitString => decide (o₁ = o₂) := hp.to_comp
  have hchk : Computable₂ fun (q : BitString × BitString) (n : ℕ) =>
      decide (alloc n = some q.1) :=
    heq.comp (halloc.comp Computable.snd)
      (Computable.option_some.comp (Computable.fst.comp Computable.fst))
  have hrfind : Partrec fun q : BitString × BitString =>
      Nat.rfind fun n => Part.some (decide (alloc n = some q.1)) :=
    Partrec.rfind hchk.partrec
  have hout : Computable₂ fun (_ : BitString × BitString) (n : ℕ) =>
      (E n).getD ([] : BitString) :=
    Computable.option_getD (hE.comp Computable.snd) (Computable.const [])
  exact hrfind.map hout

/-- Every allocated code decompresses to the string it was allocated for: the
allocation is injective (distinct requests get incomparable codes), so the
unbounded search finds exactly the index of that request. -/
private lemma coverMachine_produces {E alloc : ℕ → Option BitString}
    (hpf : ∀ n m cn cm, alloc n = some cn → alloc m = some cm → n ≠ m →
      ¬ List.IsPrefix cn cm)
    {k : ℕ} {z c : BitString} (hEk : E k = some z) (hck : alloc k = some c) (y : BitString) :
    produces (coverMachineDim E alloc) c y z := by
  have hinj : ∀ n, alloc n = some c → n = k := by
    intro n hn
    by_contra hne
    exact hpf n k c c hn hck hne (List.prefix_refl c)
  have hmem : k ∈ Nat.rfind fun n => Part.some (decide (alloc n = some c)) := by
    refine Nat.mem_rfind.2 ⟨?_, ?_⟩
    · simp [hck]
    · intro m hm
      have hne : alloc m ≠ some c := by
        intro h
        have := hinj m h
        omega
      simp [hne]
  have h2 := Part.mem_map (fun n => (E n).getD ([] : BitString)) hmem
  simpa [produces, coverMachineDim, hEk] using h2

private lemma isPrefixMachine_coverMachine {E alloc : ℕ → Option BitString}
    (hpf : ∀ n m cn cm, alloc n = some cn → alloc m = some cm → n ≠ m →
      ¬ List.IsPrefix cn cm) :
    IsPrefixMachine (coverMachineDim E alloc) := by
  have hdom : ∀ y p : BitString, p ∈ domainAt (coverMachineDim E alloc) y →
      ∃ n, alloc n = some p := by
    intro y p hp
    have hdomrf : (Nat.rfind fun n => Part.some (decide (alloc n = some p))).Dom := hp
    obtain ⟨n, hn, -⟩ := Nat.rfind_dom.1 hdomrf
    exact ⟨n, by simpa using hn⟩
  intro y p hp q hq hpre
  obtain ⟨n, hn⟩ := hdom y p hp
  obtain ⟨m, hm⟩ := hdom y q hq
  by_cases hnm : n = m
  · subst hnm
    exact Option.some_injective _ (hn.symm.trans hm)
  · exact absurd hpre (hpf n m p q hn hm hnm)

/-! ## From a cover to a complexity bound (SUV Theorem 120, second inequality) -/

/-- **SUV §5.8, p. 175** (the whole content of the second inequality of
Theorem 120):

> "The first statement implies that `m(i) ≥ c·2^{-r·l(x_i)}` for some `c` and for
> all `i` (where `m` is the discrete a priori probability of natural numbers
> considered in Chapter 4).  Taking the logarithms, we get the bound for prefix
> complexity, `K(x_i) ≤ K(i) + O(1) ≤ r·l(x_i) + O(1)` … and the plain
> complexity does not exceed the prefix one."

*Clean simple leaf* (~250 lines), Kraft-Chaitin form; every ingredient it needs
is already in the repository, so nothing is hidden behind it:

* `alphaFloorMass_le_two_mul` (`Dimension/AlphaTrim.lean`) bounds
  `2^{-⌊r·l(x)⌋}` by `2·μ(Ω_x)^r`, so the finiteness of `∑ₖ μ(Ω_{x_k})^r` gives a
  natural `B` with `∑ₖ 2^{-(⌊r·l(x_k)⌋+B)} ≤ 1`;
* `exists_online_prefixFree_of_kraft_le_one`
  (`AlgorithmicProbability/KraftChaitinOnline.lean`) then allocates, computably
  and online, prefix-free codes of exactly the lengths `⌊r·l(x_k)⌋ + B`;
* the map sending an allocated code to the string it was requested for is a
  prefix decompressor `M` (its domain is the prefix-free allocated set), so
  `KPPlain M (x_k) ≤ ⌊r·l(x_k)⌋ + B` by definition of `KPPlain`;
* `plain_le_prefix` (`Prefix/Properties.lean`) - which needs only
  `IsPrefixDecompressor M`, not optimality - turns that into the plain-complexity
  bound below.

Note that the `O(1)` here is genuinely additive: no `O(log)` term appears,
because the coding is done by Kraft-Chaitin rather than by spelling out an
index. -/
theorem exists_const_plainK_le_of_tsum_ne_top (V : Map) (hV : isOptimalConditional V)
    (r : ℚ) (hr : 0 < r) (E : ℕ → Option BitString) (hE : Computable E)
    (hsum : (∑' k, coverAlphaMass ((r : ℚ) : ℝ) (E k)) ≠ ⊤) :
    ∃ c : ℕ, ∀ (k : ℕ) (z : BitString), E k = some z →
      plainK V z ≤ ((alphaFloor r z.length + c : ℕ) : ℕ∞) := by
  classical
  -- the dyadic `⌊r·l⌋`-weight of the cover is finite, since it is at most twice
  -- the `r`-weight (`alphaFloorMass_le_two_mul`)
  have hle : (∑' k, (E k).elim 0 (alphaFloorMass r))
      ≤ 2 * ∑' k, coverAlphaMass ((r : ℚ) : ℝ) (E k) := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    cases hEk : E k with
    | none => simp
    | some z =>
        simpa [coverAlphaMass, intervalAlphaMass] using alphaFloorMass_le_two_mul r hr z
  have hfloor : (∑' k, (E k).elim 0 (alphaFloorMass r)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hsum) hle
  -- so it is below some power of two, and the request stream has Kraft weight ≤ 1
  obtain ⟨B, hB⟩ : ∃ B : ℕ, (∑' k, (E k).elim 0 (alphaFloorMass r)) ≤ (2 : ℝ≥0∞) ^ B := by
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfloor
    refine ⟨n, le_of_lt (lt_of_lt_of_le hn ?_)⟩
    have hnat : (n : ℕ) ≤ 2 ^ n := le_of_lt Nat.lt_two_pow_self
    calc (n : ℝ≥0∞) ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
      _ = (2 : ℝ≥0∞) ^ n := by push_cast; ring
  have hweight : requestKraftWeight (coverRequest r B E) ≤ 1 := by
    rw [requestKraftWeight_coverRequest]
    calc ((2 : ℝ≥0∞)⁻¹) ^ B * ∑' k, (E k).elim 0 (alphaFloorMass r)
        ≤ ((2 : ℝ≥0∞)⁻¹) ^ B * (2 : ℝ≥0∞) ^ B := by gcongr
      _ = 1 := by rw [mul_comm]; exact two_pow_mul_inv_two_pow B
  -- the online allocator supplies prefix-free codes of the requested lengths
  obtain ⟨alloc, halloc, hlen, -, hpf⟩ :=
    exists_online_prefixFree_of_kraft_le_one (coverRequest r B E)
      (computable_coverRequest r B hE) hweight
  -- reading off the allocation is a prefix decompressor
  have hMdec : isDecompressor (coverMachineDim E alloc) := partrec_coverMachine hE halloc
  have hMpf : IsPrefixMachine (coverMachineDim E alloc) := isPrefixMachine_coverMachine hpf
  obtain ⟨c₀, hc₀⟩ := plain_le_prefix V (coverMachineDim E alloc) hV ⟨hMdec, hMpf⟩
  refine ⟨B + c₀, fun k z hEk => ?_⟩
  obtain ⟨cw, hcw, hcwlen⟩ :=
    hlen k (alphaFloor r z.length + B) (by simp [coverRequest, hEk])
  have hprod : produces (coverMachineDim E alloc) cw [] z :=
    coverMachine_produces hpf hEk hcw []
  have hKP : KPPlain (coverMachineDim E alloc) z ≤ ((alphaFloor r z.length + B : ℕ) : ℕ∞) := by
    have hbound := KP_le_programLength_of_produces hprod
    rw [← hcwlen]
    exact hbound
  calc plainK V z ≤ KPPlain (coverMachineDim E alloc) z + (c₀ : ℕ∞) := hc₀ z
    _ ≤ ((alphaFloor r z.length + B : ℕ) : ℕ∞) + (c₀ : ℕ∞) := add_le_add hKP le_rfl
    _ = ((alphaFloor r z.length + (B + c₀) : ℕ) : ℕ∞) := by push_cast; ring

/-- An interval of small `r`-weight is long: `μ(Ω_z)^r < 2^{-j}` forces
`r·l(z) > j`.  This is the source's "the lengths of `x_i` tend to infinity
(since the series is convergent)" in the sharp form the covers give. -/
lemma lt_mul_length_of_intervalAlphaMass_lt {r : ℚ} {z : BitString} {j : ℕ}
    (h : intervalAlphaMass ((r : ℚ) : ℝ) z < ((2 : ℝ≥0∞)⁻¹) ^ j) :
    (j : ℝ) < (z.length : ℝ) * ((r : ℚ) : ℝ) := by
  by_contra hcon
  push Not at hcon
  have hle : ((2 : ℝ≥0∞)⁻¹) ^ j ≤ intervalAlphaMass ((r : ℚ) : ℝ) z := by
    rw [intervalAlphaMass_eq_inv_two_pow, ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) z.length,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) j]
    exact ENNReal.rpow_le_rpow_of_exponent_ge (by norm_num) hcon
  exact absurd h (not_lt.2 hle)

/-! ### Kraft-Chaitin for prefix complexity -/

/-- The request stream asking, for the `k`-th string of a partial enumeration, a
code of the prescribed length `L k`. -/
private def lenRequest (L : ℕ → ℕ) (E : ℕ → Option BitString) (k : ℕ) : Option ℕ :=
  (E k).map fun _ => L k

private lemma computable_lenRequest {L : ℕ → ℕ} (hL : Computable L)
    {E : ℕ → Option BitString} (hE : Computable E) : Computable (lenRequest L E) :=
  Computable.option_map hE (hL.comp Computable.fst)

private lemma requestKraftWeight_lenRequest (L : ℕ → ℕ) (E : ℕ → Option BitString) :
    requestKraftWeight (lenRequest L E)
      = ∑' k, (E k).elim 0 (fun _ => ((2 : ℝ≥0∞)⁻¹) ^ L k) := by
  rw [requestKraftWeight]
  refine tsum_congr fun k => ?_
  cases hEk : E k with
  | none => simp [lenRequest, hEk]
  | some z => simp [lenRequest, hEk]

/-- **Kraft-Chaitin for prefix complexity.**  A computable partial enumeration of
strings, together with computable requested code lengths of total Kraft weight at
most `1`, bounds the prefix complexity of every enumerated string by its
requested length, up to an additive constant.

This is the machine half of the second inequality of SUV Theorem 120 (p. 175),
stated for the prefix complexity itself and for an arbitrary length request; it
is `exists_const_plainK_le_of_tsum_ne_top` with `⌊r·l(z)⌋ + B` replaced by an
arbitrary computable `L`, and it is what SUV Problem 169 (p. 173) needs, where
the requested length has to decrease with the level of the cover. -/
theorem exists_const_KPPlain_le_of_kraft_le_one (U : Map) (hU : IsOptimalPrefixConditional U)
    (E : ℕ → Option BitString) (hE : Computable E) (L : ℕ → ℕ) (hL : Computable L)
    (hkraft : (∑' k, (E k).elim 0 (fun _ => ((2 : ℝ≥0∞)⁻¹) ^ L k)) ≤ 1) :
    ∃ c : ℕ, ∀ (k : ℕ) (z : BitString), E k = some z → KPPlain U z ≤ ((L k + c : ℕ) : ℕ∞) := by
  obtain ⟨alloc, halloc, hlen, -, hpf⟩ :=
    exists_online_prefixFree_of_kraft_le_one (lenRequest L E) (computable_lenRequest hL hE)
      (by rw [requestKraftWeight_lenRequest]; exact hkraft)
  have hMdec : isDecompressor (coverMachineDim E alloc) := partrec_coverMachine hE halloc
  have hMpf : IsPrefixMachine (coverMachineDim E alloc) := isPrefixMachine_coverMachine hpf
  obtain ⟨c₀, hc₀⟩ := hU.invariance (M := coverMachineDim E alloc) ⟨hMdec, hMpf⟩
  refine ⟨c₀, fun k z hEk => ?_⟩
  obtain ⟨cw, hcw, hcwlen⟩ := hlen k (L k) (by simp [lenRequest, hEk])
  have hprod : produces (coverMachineDim E alloc) cw [] z :=
    coverMachine_produces hpf hEk hcw []
  have hKP : KPPlain (coverMachineDim E alloc) z ≤ ((L k : ℕ) : ℕ∞) := by
    have hbound := KP_le_programLength_of_produces hprod
    rw [← hcwlen]
    exact hbound
  have hinv : KPPlain U z ≤ KPPlain (coverMachineDim E alloc) z + (c₀ : ℕ∞) := hc₀ z []
  calc KPPlain U z ≤ KPPlain (coverMachineDim E alloc) z + (c₀ : ℕ∞) := hinv
    _ ≤ ((L k : ℕ) : ℕ∞) + (c₀ : ℕ∞) := add_le_add hKP le_rfl
    _ = ((L k + c₀ : ℕ) : ℕ∞) := by push_cast; ring

end Kolmogorov
