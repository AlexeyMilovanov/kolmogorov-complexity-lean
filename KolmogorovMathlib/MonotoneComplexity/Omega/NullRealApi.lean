/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.ProbabilityBounded
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable

/-!
# An API for effectively null sets of reals

`IsEffectivelyNullReal` (`Omega/Basic.lean`) is the SUV p. 157 notion "there is an
algorithm that for every rational `ε > 0` enumerates a cover of `X` by rational
intervals of total length at most `ε`".  This module supplies the API around it:
monotonicity, closure under countable unions, and ways of building such a cover,
which is what the Martin-Löf tests on the reals of SUV pp. 170–171 need.

## Contents

* `IsEffectivelyNullReal.mono`, `isEffectivelyNullReal_empty`;
* **budget normalisation** — `isEffectivelyNullReal_of_pow_cover` and
  `IsEffectivelyNullReal.exists_pow_cover`: an effectively null set is exactly one with a
  computable family of covers of total length `≤ 2^{-n}` indexed by `n : ℕ`.  Every
  construction of Section 5.7 produces the dyadic form, and keeping the index set inside
  `ℕ` also keeps the `Computable` elaboration cheap;
* `isEffectivelyNullReal_iUnion` (uniform countable union) and
  `IsEffectivelyNullReal.union`;
* `isEffectivelyNullReal_iInter_ball` — the **test builder** behind SUV pp. 170–171: a
  computably enumerated family of rational centres `qᵢ` carrying weights `2^{-eᵢ}` of
  total mass at most `1` makes the shrinking neighbourhoods
  `Bad n = {x | ∃ i, |x - qᵢ| < 2^{-(eᵢ+n)}}` an effectively null intersection.  This is
  the Kraft-inequality covering argument of p. 170 in reusable form.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ### Elementary closure properties -/

/-- Monotonicity: a subset of an effectively null set of reals is effectively null
(the very same cover works). -/
theorem IsEffectivelyNullReal.mono {X Y : Set ℝ} (hX : IsEffectivelyNullReal X)
    (hYX : Y ⊆ X) : IsEffectivelyNullReal Y := by
  obtain ⟨cover, hcov, hspec⟩ := hX
  exact ⟨cover, hcov, fun ε hε => ⟨hYX.trans (hspec ε hε).1, (hspec ε hε).2⟩⟩

/-- The empty set of reals is effectively null. -/
theorem isEffectivelyNullReal_empty : IsEffectivelyNullReal (∅ : Set ℝ) := by
  refine ⟨fun _ _ => none, Computable.const none, fun ε _ => ⟨Set.empty_subset _, ?_⟩⟩
  simp

/-! ### Budget normalisation -/

/-- For a positive rational `ε`, the dyadic budget `2^{-ε.den}` is at most `ε`. -/
theorem inv_two_pow_den_le {ε : ℚ} (hε : 0 < ε) : ((2 : ℚ)⁻¹) ^ ε.den ≤ ε := by
  have hd : (0 : ℚ) < (ε.den : ℚ) := by exact_mod_cast ε.pos
  have h1 : (1 : ℚ) / (ε.den : ℚ) ≤ ε := by
    nth_rw 2 [← Rat.num_div_den ε]
    apply div_le_div_of_nonneg_right
    · have hp : 0 < ε.num := Rat.num_pos.mpr hε
      exact_mod_cast hp
    · exact_mod_cast (le_of_lt ε.pos)
  refine le_trans ?_ h1
  rw [inv_pow, ← one_div]
  refine one_div_le_one_div_of_le hd ?_
  have h2 : (ε.den : ℕ) ≤ 2 ^ ε.den := k_le_two_pow_k ε.den
  exact_mod_cast h2

/-- **Budget normalisation, `⇐`.**  To prove a set of reals effectively null it is enough
to give, computably in `n : ℕ`, a cover of total length at most `2^{-n}`: the rational
budget `ε` is met by running the cover at level `ε.den` (`inv_two_pow_den_le`). -/
theorem isEffectivelyNullReal_of_pow_cover {X : Set ℝ} (cover : ℕ → ℕ → Option (ℚ × ℚ))
    (hcov : Computable₂ cover)
    (hsub : ∀ n : ℕ, X ⊆ ⋃ i, (cover n i).elim ∅ ratInterval)
    (hlen : ∀ n : ℕ, (∑' i, (cover n i).elim 0 ratIntervalLength) ≤ (2 : ℝ≥0∞)⁻¹ ^ n) :
    IsEffectivelyNullReal X := by
  refine ⟨fun ε i => cover ε.den i, ?_, fun ε hε => ⟨hsub _, ?_⟩⟩
  · exact hcov.comp (computable_ratDen.comp Computable.fst) Computable.snd
  · refine le_trans (hlen ε.den) ?_
    rw [← ofReal_rat_inv_two_pow]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast inv_two_pow_den_le hε)

/-- **Budget normalisation, `⇒`.**  Conversely, an effectively null set of reals has a
computable family of covers of total length at most `2^{-n}`: run the given cover at the
rational budget `2^{-n}`. -/
theorem IsEffectivelyNullReal.exists_pow_cover {X : Set ℝ} (hX : IsEffectivelyNullReal X) :
    ∃ cover : ℕ → ℕ → Option (ℚ × ℚ), Computable₂ cover ∧
      (∀ n : ℕ, X ⊆ ⋃ i, (cover n i).elim ∅ ratInterval) ∧
      (∀ n : ℕ, (∑' i, (cover n i).elim 0 ratIntervalLength) ≤ (2 : ℝ≥0∞)⁻¹ ^ n) := by
  obtain ⟨cover, hcov, hspec⟩ := hX
  have hpos : ∀ n : ℕ, (0 : ℚ) < ((2 : ℚ)⁻¹) ^ n := fun n => pow_pos (by norm_num) n
  refine ⟨fun n i => cover (((2 : ℚ)⁻¹) ^ n) i, ?_, fun n => (hspec _ (hpos n)).1,
    fun n => ?_⟩
  · exact hcov.comp (computable_inv_two_pow_rat.comp Computable.fst) Computable.snd
  · have h := (hspec _ (hpos n)).2
    rwa [ofReal_rat_inv_two_pow] at h

/-! ### The countable union -/

/-- The merged cover of a countable union: at level `k` the index `i` decodes as a pair
`(n, j)` and the `n`-th cover is run at level `k + n + 1`. -/
def unionCover (cover : ℕ → ℕ → ℕ → Option (ℚ × ℚ)) (k i : ℕ) : Option (ℚ × ℚ) :=
  cover i.unpair.1 (k + i.unpair.1 + 1) i.unpair.2

/-- Value of the merged cover at a packed index: the `j`-th interval of the `n`-th cover at
budget level `k + n + 1`. -/
theorem unionCover_pair (cover : ℕ → ℕ → ℕ → Option (ℚ × ℚ)) (k n j : ℕ) :
    unionCover cover k (Nat.pair n j) = cover n (k + n + 1) j := by
  simp only [unionCover, Nat.unpair_pair]

/-- The merged cover of a computable family of covers is computable. -/
theorem computable₂_unionCover {cover : ℕ → ℕ → ℕ → Option (ℚ × ℚ)}
    (hcov : Computable fun p : (ℕ × ℕ) × ℕ => cover p.1.1 p.1.2 p.2) :
    Computable₂ (unionCover cover) := by
  have hadd : Computable₂ (fun a b : ℕ => a + b) := Primrec.nat_add.to_comp
  have hu1 : Computable (fun p : ℕ × ℕ => p.2.unpair.1) :=
    ((Primrec.fst.comp Primrec.unpair).to_comp).comp Computable.snd
  have hu2 : Computable (fun p : ℕ × ℕ => p.2.unpair.2) :=
    ((Primrec.snd.comp Primrec.unpair).to_comp).comp Computable.snd
  have hlev : Computable (fun p : ℕ × ℕ => p.1 + p.2.unpair.1 + 1) :=
    hadd.comp (hadd.comp Computable.fst hu1) (Computable.const 1)
  exact Computable.comp hcov (Computable.pair (Computable.pair hu1 hlev) hu2)

/-- **Countable union.**  A *uniformly* computable family of covers gives an effectively
null union: at level `k` the `n`-th set is covered at level `k + n + 1` and the
enumerations are merged along `Nat.pair`.  Uniformity cannot be dropped:
`IsEffectivelyNullReal Xₙ` for each `n` separately gives no single algorithm. -/
theorem isEffectivelyNullReal_iUnion {X : ℕ → Set ℝ} (cover : ℕ → ℕ → ℕ → Option (ℚ × ℚ))
    (hcov : Computable fun p : (ℕ × ℕ) × ℕ => cover p.1.1 p.1.2 p.2)
    (hsub : ∀ n k : ℕ, X n ⊆ ⋃ i, (cover n k i).elim ∅ ratInterval)
    (hlen : ∀ n k : ℕ, (∑' i, (cover n k i).elim 0 ratIntervalLength) ≤ (2 : ℝ≥0∞)⁻¹ ^ k) :
    IsEffectivelyNullReal (⋃ n, X n) := by
  classical
  refine isEffectivelyNullReal_of_pow_cover (unionCover cover)
    (computable₂_unionCover hcov) (fun k => ?_) (fun k => ?_)
  · rintro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    have hmem := hsub n (k + n + 1) hn
    rw [Set.mem_iUnion] at hmem
    obtain ⟨j, hj⟩ := hmem
    rw [Set.mem_iUnion]
    exact ⟨Nat.pair n j, by rw [unionCover_pair]; exact hj⟩
  · calc (∑' i : ℕ, (unionCover cover k i).elim 0 ratIntervalLength)
        = ∑' p : ℕ × ℕ, (unionCover cover k (Nat.pair p.1 p.2)).elim 0 ratIntervalLength := by
          rw [← Equiv.tsum_eq Nat.pairEquiv
            (fun i => (unionCover cover k i).elim (0 : ℝ≥0∞) ratIntervalLength)]
          rfl
      _ = ∑' n : ℕ, ∑' j : ℕ, (unionCover cover k (Nat.pair n j)).elim 0 ratIntervalLength :=
          ENNReal.tsum_prod
            (f := fun n j => (unionCover cover k (Nat.pair n j)).elim 0 ratIntervalLength)
      _ ≤ ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + n + 1) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          have heq : ∀ j : ℕ,
              (unionCover cover k (Nat.pair n j)).elim (0 : ℝ≥0∞) ratIntervalLength
                = (cover n (k + n + 1) j).elim 0 ratIntervalLength := by
            intro j; rw [unionCover_pair]
          rw [tsum_congr heq]
          exact hlen n (k + n + 1)
      _ = (2 : ℝ≥0∞)⁻¹ ^ k := tsum_inv_two_pow_shift k

/-- The union of two effectively null sets of reals is effectively null. -/
theorem IsEffectivelyNullReal.union {X Y : Set ℝ} (hX : IsEffectivelyNullReal X)
    (hY : IsEffectivelyNullReal Y) : IsEffectivelyNullReal (X ∪ Y) := by
  classical
  obtain ⟨cX, hcX, hsubX, hlenX⟩ := hX.exists_pow_cover
  obtain ⟨cY, hcY, hsubY, hlenY⟩ := hY.exists_pow_cover
  have hfam : IsEffectivelyNullReal
      (⋃ n : ℕ, (fun n : ℕ => Nat.casesOn (motive := fun _ => Set ℝ) n X (fun _ => Y)) n) := by
    refine isEffectivelyNullReal_iUnion
      (fun n k i => Nat.casesOn (motive := fun _ => Option (ℚ × ℚ)) n (cX k i)
        (fun _ => cY k i)) ?_ ?_ ?_
    · have hproj : Computable (fun p : (ℕ × ℕ) × ℕ => (p.1.2, p.2)) :=
        Computable.pair (Computable.snd.comp Computable.fst) Computable.snd
      have hcX' : Computable (fun p : (ℕ × ℕ) × ℕ => cX p.1.2 p.2) :=
        Computable.comp (show Computable (fun p : ℕ × ℕ => cX p.1 p.2) from hcX) hproj
      have hcY' : Computable (fun p : (ℕ × ℕ) × ℕ => cY p.1.2 p.2) :=
        Computable.comp (show Computable (fun p : ℕ × ℕ => cY p.1 p.2) from hcY) hproj
      exact Computable.nat_casesOn (Computable.fst.comp Computable.fst) hcX'
        (hcY'.comp Computable.fst)
    · intro n k
      cases n with
      | zero => exact hsubX k
      | succ m => exact hsubY k
    · intro n k
      cases n with
      | zero => exact hlenX k
      | succ m => exact hlenY k
  refine hfam.mono ?_
  intro x hx
  rcases hx with hx | hx
  · exact Set.mem_iUnion.2 ⟨0, hx⟩
  · exact Set.mem_iUnion.2 ⟨1, hx⟩

/-! ### The Kraft test builder (SUV pp. 170–171) -/

/-- The rational interval of radius `2^{-k}` around the rational centre `q`. -/
def centreInterval (q : ℚ) (k : ℕ) : ℚ × ℚ :=
  (q - ((2 : ℚ)⁻¹) ^ k, q + ((2 : ℚ)⁻¹) ^ k)

/-- The interval of radius `2 ^ -k` around a rational centre is computable in both arguments. -/
theorem computable₂_centreInterval : Computable₂ centreInterval := by
  have hr : Computable (fun p : ℚ × ℕ => ((2 : ℚ)⁻¹) ^ p.2) :=
    computable_inv_two_pow_rat.comp Computable.snd
  exact Computable.pair (computable₂_ratSub.comp Computable.fst hr)
    (computable₂_ratAdd.comp Computable.fst hr)

/-- The interval of radius `2 ^ -k` has length `2 * 2 ^ -k`. -/
theorem ratIntervalLength_centreInterval (q : ℚ) (k : ℕ) :
    ratIntervalLength (centreInterval q k) = 2 * (2 : ℝ≥0∞)⁻¹ ^ k := by
  rw [ratIntervalLength, centreInterval]
  have h : ((q + ((2 : ℚ)⁻¹) ^ k : ℚ) : ℝ) - ((q - ((2 : ℚ)⁻¹) ^ k : ℚ) : ℝ)
      = 2 * (((((2 : ℚ)⁻¹) ^ k : ℚ)) : ℝ) := by push_cast; ring
  rw [h, ENNReal.ofReal_mul (by norm_num), ofReal_rat_inv_two_pow]
  norm_num

/-- A real within `2 ^ -k` of the centre lies in the interval of radius `2 ^ -k`. -/
theorem mem_centreInterval {x : ℝ} {q : ℚ} {k : ℕ}
    (h : |x - (q : ℝ)| < ((2 : ℝ)⁻¹) ^ k) : x ∈ ratInterval (centreInterval q k) := by
  rw [ratInterval, centreInterval]
  rw [abs_lt] at h
  refine Set.mem_Ioo.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith [h.1, h.2]

/-- **The test builder of SUV p. 170.**  Let `c` computably enumerate pairs
"(rational centre `q`, weight exponent `e`)" whose weights `2^{-e}` have total mass at
most `1` — the shape produced by the Kraft inequality for a prefix-free machine, with
`q` the output and `e` the length of a program.  Then the shrinking neighbourhoods
`Bad n = {x | ∃ i, |x - qᵢ| < 2^{-(eᵢ+n)}}` have an effectively null intersection.

Consequently a Martin-Löf random real avoids `Bad n` for **some** `n`, which is the
"`|α - q| ≥ 2^{-K(q)-c}` for every rational `q`" of p. 170. -/
theorem isEffectivelyNullReal_iInter_ball {c : ℕ → Option (ℚ × ℕ)} (hc : Computable c)
    (hmass : (∑' i, (c i).elim 0 (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2)) ≤ 1) :
    IsEffectivelyNullReal (⋂ n : ℕ,
      {x : ℝ | ∃ i : ℕ, ∃ p : ℚ × ℕ, c i = some p ∧
        |x - (p.1 : ℝ)| < ((2 : ℝ)⁻¹) ^ (p.2 + n)}) := by
  classical
  refine isEffectivelyNullReal_of_pow_cover
    (fun n i => (c i).map (fun p : ℚ × ℕ => centreInterval p.1 (p.2 + n + 1))) ?_ ?_ ?_
  · have hci : Computable (fun q : ℕ × ℕ => c q.2) := hc.comp Computable.snd
    have hadd : Computable₂ (fun a b : ℕ => a + b) := Primrec.nat_add.to_comp
    have hmap : Computable₂ (fun (q : ℕ × ℕ) (p : ℚ × ℕ) =>
        centreInterval p.1 (p.2 + q.1 + 1)) := by
      refine computable₂_centreInterval.comp (Computable.fst.comp Computable.snd) ?_
      exact hadd.comp
        (hadd.comp (Computable.snd.comp Computable.snd) (Computable.fst.comp Computable.fst))
        (Computable.const 1)
    exact Computable.option_map hci hmap
  · intro n x hx
    have hxn := Set.mem_iInter.1 hx (n + 1)
    obtain ⟨i, p, hp, hdist⟩ := hxn
    rw [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [hp]
    change x ∈ ratInterval (centreInterval p.1 (p.2 + n + 1))
    exact mem_centreInterval (by rw [show p.2 + n + 1 = p.2 + (n + 1) by ring]; exact hdist)
  · intro n
    have hterm : ∀ i : ℕ,
        ((c i).map (fun p : ℚ × ℕ => centreInterval p.1 (p.2 + n + 1))).elim
            (0 : ℝ≥0∞) ratIntervalLength
          = 2 * (2 : ℝ≥0∞)⁻¹ ^ (n + 1) * (c i).elim 0 (fun p : ℚ × ℕ => (2 : ℝ≥0∞)⁻¹ ^ p.2) := by
      intro i
      rcases hcase : c i with _ | p
      · simp
      · simp only [Option.map_some, Option.elim]
        rw [ratIntervalLength_centreInterval, show p.2 + n + 1 = p.2 + (n + 1) by ring, pow_add]
        ring
    rw [tsum_congr hterm, ENNReal.tsum_mul_left]
    calc 2 * (2 : ℝ≥0∞)⁻¹ ^ (n + 1)
            * (∑' i, (c i).elim 0 (fun p : ℚ × ℕ => (2 : ℝ≥0∞)⁻¹ ^ p.2))
        ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ (n + 1) * 1 := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ n := by
          rw [mul_one, pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞) _, mul_assoc,
            ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

end Kolmogorov
