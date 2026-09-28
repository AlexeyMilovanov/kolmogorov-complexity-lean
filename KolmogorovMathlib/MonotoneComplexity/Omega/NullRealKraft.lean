/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealApi
import KolmogorovMathlib.MonotoneComplexity.REClosure

/-!
# The Kraft covering argument of SUV p. 170

SUV p. 170 (proof of Theorem 114) uses the following covering test on the reals: for a
constant `c`, let `Uc` be the union over all objects `q` of the interval of radius
`2^{-K(q)-c}` centred at `q`.  Since `K` is upper semicomputable, `Uc` is an effectively
open set, and by the Kraft inequality its total length is `O(2^{-c})`, so the intersection
over `c` is an effectively null set.  A Martin-Löf random real therefore keeps its distance
`2^{-K(q)-c}` from every `q`, for some constant `c`.

This module carries out that argument for a *computable sequence of rationals* `a`, which
is the shape SUV p. 170 needs (`q = aᵢ`, and the index `i` is what the prefix complexity is
measured on).  The test itself is built with `isEffectivelyNullReal_iInter_ball`
(`Omega/NullRealApi.lean`); what is added here is the enumeration:

* `reFirstStage` — the first stage at which a monotone stage test fires, which turns the
  r.e. set `{(i,k) | K(i) < k}` (`isRE_KPPlain_lt` + `IsRE.exists_stageApprox`) into an
  enumeration that lists every member **exactly once**, so that the weights `2^{-k}` are
  not counted twice;
* `tsum_ite_gt_inv_two_pow` — `∑_{k > κ} 2^{-k} = 2^{-κ}`, which turns the Kraft
  inequality `∑ᵢ 2^{-K(i)} ≤ 1` into the mass bound the test builder wants.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ### First stages of a monotone stage test -/

/-- `reNotBefore chk q s` says that the stage test has not yet fired strictly before `s`. -/
def reNotBefore {α : Type*} (chk : α → ℕ → Bool) (q : α) (s : ℕ) : Bool :=
  Nat.casesOn (motive := fun _ => Bool) s true (fun t => !(chk q t))

/-- The stage test fires at `s` for the first time. -/
def reFirstStage {α : Type*} (chk : α → ℕ → Bool) (q : α) (s : ℕ) : Bool :=
  chk q s && reNotBefore chk q s

/-- A stage at which the test fires for the first time is a stage at which it fires. -/
theorem chk_of_reFirstStage {α : Type*} {chk : α → ℕ → Bool} {q : α} {s : ℕ}
    (h : reFirstStage chk q s = true) : chk q s = true := by
  rw [reFirstStage, Bool.and_eq_true] at h
  exact h.1

/-- If the test ever fires, it has a first firing stage. -/
theorem exists_reFirstStage {α : Type*} (chk : α → ℕ → Bool) {q : α} (h : ∃ s, chk q s = true) :
    ∃ s, reFirstStage chk q s = true := by
  classical
  refine ⟨Nat.find h, ?_⟩
  rw [reFirstStage, Bool.and_eq_true]
  refine ⟨Nat.find_spec h, ?_⟩
  rcases hz : Nat.find h with _ | t
  · rfl
  · have hmin : ¬ chk q t = true := Nat.find_min h (by omega)
    simp [reNotBefore, hmin]

/-- For a monotone test, the first firing stage is unique. -/
theorem reFirstStage_unique {α : Type*} {chk : α → ℕ → Bool}
    (hmono : ∀ (q : α) (s t : ℕ), s ≤ t → chk q s = true → chk q t = true) {q : α} {s t : ℕ}
    (hs : reFirstStage chk q s = true) (ht : reFirstStage chk q t = true) : s = t := by
  by_contra hne
  rcases Nat.lt_or_ge s t with hlt | hge
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    have h1 : chk q u = true := hmono q s u (by omega) (chk_of_reFirstStage hs)
    rw [reFirstStage, Bool.and_eq_true] at ht
    simp [reNotBefore, h1] at ht
  · have hlt : t < s := by omega
    obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
    have h1 : chk q u = true := hmono q t u (by omega) (chk_of_reFirstStage ht)
    rw [reFirstStage, Bool.and_eq_true] at hs
    simp [reNotBefore, h1] at hs

/-- Summing a weight over the stages picks it up exactly once when the test fires. -/
theorem tsum_ite_reFirstStage {α : Type*} {chk : α → ℕ → Bool}
    (hmono : ∀ (q : α) (s t : ℕ), s ≤ t → chk q s = true → chk q t = true) (q : α)
    (v : ℝ≥0∞) (hex : ∃ s, chk q s = true) :
    (∑' s : ℕ, if reFirstStage chk q s = true then v else 0) = v := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_reFirstStage chk hex
  rw [tsum_eq_single s₀ (fun s hs => ?_), if_pos hs₀]
  by_cases hcase : reFirstStage chk q s = true
  · exact absurd (reFirstStage_unique hmono hcase hs₀) hs
  · simp [hcase]

/-- If the test never fires the sum is zero. -/
theorem tsum_ite_reFirstStage_of_not {α : Type*} {chk : α → ℕ → Bool} (q : α) (v : ℝ≥0∞)
    (hex : ¬ ∃ s, chk q s = true) :
    (∑' s : ℕ, if reFirstStage chk q s = true then v else 0) = 0 := by
  classical
  have hz : ∀ s : ℕ, (if reFirstStage chk q s = true then v else 0) = 0 := by
    intro s
    have hns : ¬ reFirstStage chk q s = true := fun h => hex ⟨s, chk_of_reFirstStage h⟩
    simp [hns]
  simp [hz]

/-- `∑_{k > κ} 2^{-k} = 2^{-κ}`. -/
theorem tsum_ite_gt_inv_two_pow (κ : ℕ) :
    (∑' k : ℕ, if κ < k then (2 : ℝ≥0∞)⁻¹ ^ k else 0) = (2 : ℝ≥0∞)⁻¹ ^ κ := by
  classical
  have hinj : Function.Injective (fun j : ℕ => κ + 1 + j) := add_right_injective (κ + 1)
  have hsupp : Function.support (fun k : ℕ => if κ < k then (2 : ℝ≥0∞)⁻¹ ^ k else 0)
      ⊆ Set.range (fun j : ℕ => κ + 1 + j) := by
    intro k hk
    rw [Function.mem_support] at hk
    have hlt : κ < k := by
      by_contra hnot
      exact hk (by simp [hnot])
    refine ⟨k - (κ + 1), ?_⟩
    change κ + 1 + (k - (κ + 1)) = k
    omega
  rw [← hinj.tsum_eq hsupp]
  have hterm : ∀ j : ℕ, (if κ < κ + 1 + j then (2 : ℝ≥0∞)⁻¹ ^ (κ + 1 + j) else 0)
      = (2 : ℝ≥0∞)⁻¹ ^ (κ + j + 1) := by
    intro j
    rw [if_pos (by omega)]
    congr 1
    omega
  rw [tsum_congr hterm, tsum_inv_two_pow_shift]

/-! ### The enumeration of `{(i,k) | K(i) < k}` with its weights -/

/-- The enumeration used by the p. 170 test: the index `j` decodes as `((i, k), s)`, and
`(aᵢ, k)` is emitted exactly when `s` is the first stage witnessing `K(i) < k`. -/
def kraftEnum (chk : BitString × ℕ → ℕ → Bool) (a : ℕ → ℚ) (j : ℕ) : Option (ℚ × ℕ) :=
  if reFirstStage chk (natToBitString j.unpair.1.unpair.1, j.unpair.1.unpair.2) j.unpair.2 then
    some (a j.unpair.1.unpair.1, j.unpair.1.unpair.2)
  else none

/-- Value of the Kraft enumeration at a packed index: the request `(a i, k)` is emitted exactly
at the first stage at which its test fires. -/
theorem kraftEnum_pair (chk : BitString × ℕ → ℕ → Bool) (a : ℕ → ℚ) (i k s : ℕ) :
    kraftEnum chk a (Nat.pair (Nat.pair i k) s) =
      if reFirstStage chk (natToBitString i, k) s then some (a i, k) else none := by
  simp only [kraftEnum, Nat.unpair_pair]

/-- The Kraft enumeration built from a computable test and a computable sequence is computable. -/
theorem computable_kraftEnum {chk : BitString × ℕ → ℕ → Bool} (hchk : Computable₂ chk)
    {a : ℕ → ℚ} (ha : Computable a) : Computable (kraftEnum chk a) := by
  have hf : Computable (fun n : ℕ => n.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
  have hs : Computable (fun n : ℕ => n.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
  have hi : Computable (fun j : ℕ => j.unpair.1.unpair.1) := hf.comp hf
  have hk : Computable (fun j : ℕ => j.unpair.1.unpair.2) := hs.comp hf
  have hst : Computable (fun j : ℕ => j.unpair.2) := hs
  have hq : Computable (fun j : ℕ => ((natToBitString j.unpair.1.unpair.1,
      j.unpair.1.unpair.2) : BitString × ℕ)) :=
    Computable.pair (computable_natToBitString.comp hi) hk
  have hchk1 : Computable (fun j : ℕ =>
      chk (natToBitString j.unpair.1.unpair.1, j.unpair.1.unpair.2) j.unpair.2) :=
    hchk.comp hq hst
  have hpred : Computable (fun j : ℕ => j.unpair.2 - 1) :=
    (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)).to_comp
  have hnb : Computable (fun j : ℕ =>
      reNotBefore chk (natToBitString j.unpair.1.unpair.1, j.unpair.1.unpair.2) j.unpair.2) := by
    have hbody : Computable₂ (fun (j : ℕ) (t : ℕ) =>
        !(chk (natToBitString j.unpair.1.unpair.1, j.unpair.1.unpair.2) t)) := by
      have h1 : Computable (fun z : ℕ × ℕ =>
          chk (natToBitString z.1.unpair.1.unpair.1, z.1.unpair.1.unpair.2) z.2) :=
        hchk.comp (hq.comp Computable.fst) Computable.snd
      exact (Primrec.dom_bool (fun b : Bool => !b)).to_comp.comp h1
    exact Computable.nat_casesOn hst (Computable.const true) hbody
  have hfs : Computable (fun j : ℕ =>
      reFirstStage chk (natToBitString j.unpair.1.unpair.1, j.unpair.1.unpair.2) j.unpair.2) :=
    (Primrec.dom_bool₂ (fun x y : Bool => x && y)).to_comp.comp hchk1 hnb
  have hval : Computable (fun j : ℕ =>
      some ((a j.unpair.1.unpair.1, j.unpair.1.unpair.2) : ℚ × ℕ)) :=
    Computable.option_some.comp (Computable.pair (ha.comp hi) hk)
  refine (Computable.cond hfs hval (Computable.const none)).of_eq fun j => ?_
  rw [kraftEnum]
  cases reFirstStage chk (natToBitString j.unpair.1.unpair.1, j.unpair.1.unpair.2) j.unpair.2 <;>
    simp

/-! ### The distance bound of SUV p. 170 -/

/-- **SUV p. 170, the covering argument.**  For a Martin-Löf random real `α` and a
computable sequence of rationals `a`, there is a constant `c` such that `aᵢ` never
approximates `α` to within `2^{-(k+c)}` once `K(i) < k`.  Equivalently: an index whose
term is `2^{-k}`-close to `α` has prefix complexity at least `k - c`. -/
theorem exists_const_inv_two_pow_le_dist_of_KPNat_lt {U : Map}
    (hU : IsOptimalPrefixConditional U) {a : ℕ → ℚ} (ha : Computable a)
    {α : ℝ} (hα : IsMartinLofRandomReal α) :
    ∃ c : ℕ, ∀ (i k : ℕ), KPNat U i < (k : ℕ∞) →
      ((2 : ℝ)⁻¹) ^ (k + c) ≤ |α - (a i : ℝ)| := by
  classical
  obtain ⟨chk, hchk, hmono, hspec⟩ :=
    (isRE_KPPlain_lt hU.isDecompressor).exists_stageApprox
  have hlt : ∀ i k : ℕ, KPNat U i < (k : ℕ∞) ↔ ∃ s, chk (natToBitString i, k) s = true := by
    intro i k
    rw [← hspec (natToBitString i, k)]
    exact Iff.rfl
  -- the total mass of the enumerated weights is at most `1`
  have hmass : (∑' j : ℕ, (kraftEnum chk a j).elim 0
      (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2)) ≤ 1 := by
    have hinner : ∀ i k : ℕ,
        (∑' s : ℕ, (kraftEnum chk a (Nat.pair (Nat.pair i k) s)).elim 0
          (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2))
          = if KPNat U i < (k : ℕ∞) then (2 : ℝ≥0∞)⁻¹ ^ k else 0 := by
      intro i k
      have hcongr : ∀ s : ℕ, (kraftEnum chk a (Nat.pair (Nat.pair i k) s)).elim 0
          (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2)
          = if reFirstStage chk (natToBitString i, k) s = true then (2 : ℝ≥0∞)⁻¹ ^ k else 0 := by
        intro s
        rw [kraftEnum_pair]
        cases reFirstStage chk (natToBitString i, k) s <;> simp
      rw [tsum_congr hcongr]
      by_cases h : ∃ s, chk (natToBitString i, k) s = true
      · rw [tsum_ite_reFirstStage hmono _ _ h, if_pos ((hlt i k).2 h)]
      · rw [tsum_ite_reFirstStage_of_not _ _ h, if_neg (fun hc => h ((hlt i k).1 hc))]
    have hmid : ∀ i : ℕ, (∑' k : ℕ, if KPNat U i < (k : ℕ∞) then (2 : ℝ≥0∞)⁻¹ ^ k else 0)
        = complexityWeight (KPNat U i) := by
      intro i
      have hne := KPNat_ne_top hU i
      set κ := (KPNat U i).toNat with hκ
      have hcoe : KPNat U i = (κ : ℕ∞) := (ENat.coe_toNat hne).symm
      have hcongr : ∀ k : ℕ, (if KPNat U i < (k : ℕ∞) then (2 : ℝ≥0∞)⁻¹ ^ k else 0)
          = if κ < k then (2 : ℝ≥0∞)⁻¹ ^ k else 0 := by
        intro k
        congr 1
        simp only [eq_iff_iff, hcoe]
        exact_mod_cast Iff.rfl
      rw [tsum_congr hcongr, tsum_ite_gt_inv_two_pow]
      rw [hcoe]
      rfl
    calc (∑' j : ℕ, (kraftEnum chk a j).elim 0 (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2))
        = ∑' z : ℕ × ℕ, (kraftEnum chk a (Nat.pair z.1 z.2)).elim 0
            (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2) := by
          rw [← Equiv.tsum_eq Nat.pairEquiv
            (fun j => (kraftEnum chk a j).elim (0 : ℝ≥0∞)
              (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2))]
          rfl
      _ = ∑' m : ℕ, ∑' s : ℕ, (kraftEnum chk a (Nat.pair m s)).elim 0
            (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2) :=
          ENNReal.tsum_prod (f := fun m s => (kraftEnum chk a (Nat.pair m s)).elim 0
            (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2))
      _ = ∑' z : ℕ × ℕ, ∑' s : ℕ,
            (kraftEnum chk a (Nat.pair (Nat.pair z.1 z.2) s)).elim 0
              (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2) := by
          rw [← Equiv.tsum_eq Nat.pairEquiv
            (fun m => ∑' s : ℕ, (kraftEnum chk a (Nat.pair m s)).elim (0 : ℝ≥0∞)
              (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2))]
          rfl
      _ = ∑' i : ℕ, ∑' k : ℕ, if KPNat U i < (k : ℕ∞) then (2 : ℝ≥0∞)⁻¹ ^ k else 0 := by
          rw [ENNReal.tsum_prod (f := fun i k => ∑' s : ℕ,
            (kraftEnum chk a (Nat.pair (Nat.pair i k) s)).elim (0 : ℝ≥0∞)
              (fun p : ℚ × ℕ => ((2 : ℝ≥0∞)⁻¹) ^ p.2))]
          exact tsum_congr fun i => tsum_congr fun k => hinner i k
      _ = ∑' i : ℕ, complexityWeight (KPNat U i) := tsum_congr hmid
      _ = ∑' x : BitString, complexityWeight (KPPlain U x) :=
          tsum_comp_natToBitString (fun x => complexityWeight (KPPlain U x))
      _ ≤ 1 := KPPlain_kraft_sum_le_one U hU.isPrefixDecompressor
  have hnull := isEffectivelyNullReal_iInter_ball (computable_kraftEnum hchk ha) hmass
  have hout := hα _ hnull
  rw [Set.mem_iInter] at hout
  push_neg at hout
  obtain ⟨c, hc⟩ := hout
  refine ⟨c, fun i k hik => ?_⟩
  obtain ⟨s₀, hs₀⟩ := exists_reFirstStage chk ((hlt i k).1 hik)
  have hmem : kraftEnum chk a (Nat.pair (Nat.pair i k) s₀) = some (a i, k) := by
    rw [kraftEnum_pair, if_pos hs₀]
  have := hc
  simp only [Set.mem_setOf_eq, not_exists] at this
  have hbound := this (Nat.pair (Nat.pair i k) s₀) (a i, k)
  simp only [hmem, true_and, not_lt] at hbound
  exact hbound

end Kolmogorov
