/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Bunches.FiniteStageSelection

/-!
# Bunch Covers

This module proves standard cover results for bunches and semi-bunches of strings under
relativized Kolmogorov complexity. It formalizes Lemma 5 and the finite-stage enumeration and
cover arguments for Lemma 6 of Muchnik and Romashchenko, “Stability of properties of Kolmogorov
complexity under relativization.”
-/

namespace Kolmogorov.Relativization

/-- Use completeness of the input enumeration to
input enumeration to turn the greedy algorithm's kept-or-rejected decision for each output into
a cover for every `P`-set. A kept set covers itself by `hSelf`; a rejected set has the required
large intersection by the rejection witness. -/
private theorem lemma5_cover_from_decisions
    (P : ℕ → ℕ → ℕ → Finset BitString → Prop)
    (E : ℕ × ℕ × ℕ × ℕ →. BitString)
    (hComplete : ∀ α β γ (X : Finset BitString), P α β γ X →
      ∃ i, finsetListCode X ∈ E (α, β, γ, i))
    (F : ℕ × ℕ × ℕ × ℕ →. BitString)
    (U : ℕ → ℕ → ℕ → ℕ → Finset BitString)
    (c : ℕ)
    (hSelf : ∀ α β γ (X : Finset BitString), P α β γ X →
      2 ^ (2 * α) ≤ X.card * 2 ^ (β + c))
    (hRejects : ∀ α β γ i (X : Finset BitString),
      finsetListCode X ∈ E (α, β, γ, i) →
        (∃ j, (F (α, β, γ, j)).Dom ∧ X = U α β γ j) ∨
        (∃ j, (F (α, β, γ, j)).Dom ∧
          2 ^ (2 * α) ≤ (X ∩ U α β γ j).card * 2 ^ (β + c))) :
    ∀ α β γ (X : Finset BitString), P α β γ X →
      ∃ i, (F (α, β, γ, i)).Dom ∧
        2 ^ (2 * α) ≤ (X ∩ U α β γ i).card * 2 ^ (β + c) := by
  intro α β γ X hX
  obtain ⟨i, hi⟩ := hComplete α β γ X hX
  rcases hRejects α β γ i X hi with ⟨j, hj, hEq⟩ | ⟨j, hj, hLarge⟩
  · refine ⟨j, hj, ?_⟩
    have hself := hSelf α β γ X hX
    simpa [hEq] using hself
  · exact ⟨j, hj, hLarge⟩

/-- The greedy selection argument gives a standard cover from an enumeration and packing bound:
let `P` be a class of finite sets of strings, enumerated by a partial recursive `E` (every output
is the code of a `P`-set, every `P`-set is output), such that every `P`-set covers itself
(`2 ^ (2α) ≤ |X| · 2 ^ (β + c)`) and every family of `P`-sets with pairwise intersections
`|X ∩ Y| · 2 ^ (β + c) < 2 ^ (2α)` has size at most `2 ^ (β + γ + c - 2α)` (packing bound).
Then `P` has a standard cover with the same constant `c`: run through the outputs of `E`
(dovetailing), keep a set iff its intersection with every previously kept set is below the
threshold.  The kept family is separated, hence finite and of the packing size; every `P`-set is
either kept (and then covers itself) or has a large intersection with an earlier kept set. -/
private theorem lemma5_greedy_enumeration
    (P : ℕ → ℕ → ℕ → Finset BitString → Prop)
    (E : ℕ × ℕ × ℕ × ℕ →. BitString) (hE : Partrec E)
    (hSound : ∀ α β γ i s, s ∈ E (α, β, γ, i) →
      ∃ X : Finset BitString, s = finsetListCode X ∧ P α β γ X)
    (hComplete : ∀ α β γ (X : Finset BitString), P α β γ X →
      ∃ i, finsetListCode X ∈ E (α, β, γ, i))
    (c : ℕ)
    (hSelf : ∀ α β γ (X : Finset BitString), P α β γ X →
      2 ^ (2 * α) ≤ X.card * 2 ^ (β + c))
    (hPack : ∀ α β γ (S : Finset (Finset BitString)),
      (∀ X ∈ S, P α β γ X) →
      (∀ X ∈ S, ∀ Y ∈ S, X ≠ Y →
        (X ∩ Y).card * 2 ^ (β + c) < 2 ^ (2 * α)) →
      S.card * 2 ^ (2 * α) ≤ 2 ^ (β + γ + c)) :
    HasStandardCover P := by
  classical
  obtain ⟨F, U, hF, hPrefix, hListed, hSeparated, hRejects⟩ :=
    lemma5_effective_selection P E hE hSound c hSelf
  have hCovers := lemma5_cover_from_decisions
    P E hComplete F U c hSelf hRejects
  have hNoDom : ∀ α β γ, ¬ (F (α, β, γ, 2 ^ (β + γ + c))).Dom := by
    intro α β γ hDom
    let m := 2 ^ (β + γ + c)
    have hDoms : ∀ i, i ≤ m → (F (α, β, γ, i)).Dom := by
      intro i hi
      by_cases heq : i = m
      · simpa [heq] using hDom
      · exact hPrefix α β γ m hDom i (by omega)
    let S := (Finset.range (m + 1)).image (U α β γ)
    have hS : ∀ X ∈ S, P α β γ X := by
      intro X hX
      rcases Finset.mem_image.mp hX with ⟨i, hi, rfl⟩
      have hi' : i ≤ m := by simp only [Finset.mem_range] at hi; omega
      exact (hListed α β γ i (hDoms i hi')).1
    have hSep : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y →
        (X ∩ Y).card * 2 ^ (β + c) < 2 ^ (2 * α) := by
      intro X hX Y hY hXY
      rcases Finset.mem_image.mp hX with ⟨i, hi, rfl⟩
      rcases Finset.mem_image.mp hY with ⟨j, hj, rfl⟩
      have hi' : i ≤ m := by simp only [Finset.mem_range] at hi; omega
      have hj' : j ≤ m := by simp only [Finset.mem_range] at hj; omega
      have hij : i ≠ j := by
        intro heq
        subst j
        exact hXY rfl
      exact hSeparated α β γ i j hij (hDoms i hi') (hDoms j hj')
    have hinj : Set.InjOn (U α β γ) (↑(Finset.range (m + 1))) := by
      intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_range] at hi hj
      by_contra hne
      have hsep := hSeparated α β γ i j hne
        (hDoms i (by omega)) (hDoms j (by omega))
      have hself := hSelf α β γ (U α β γ i)
        ((hListed α β γ i (hDoms i (by omega))).1)
      have hge : 2 ^ (2 * α) ≤
          (U α β γ i ∩ U α β γ j).card * 2 ^ (β + c) := by
        simpa [hij] using hself
      exact (not_le_of_gt hsep hge)
    have hcard : S.card = m + 1 := by
      dsimp [S]
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hpack := hPack α β γ S hS hSep
    rw [hcard] at hpack
    have hp : 0 < 2 ^ (2 * α) := Nat.pow_pos (by omega)
    have hpone : 1 ≤ 2 ^ (2 * α) := hp
    have hmul : m + 1 ≤ (m + 1) * 2 ^ (2 * α) := by
      simpa using Nat.mul_le_mul_left (m + 1) hpone
    have hgt : m < (m + 1) * 2 ^ (2 * α) :=
      (Nat.lt_succ_self m).trans_le hmul
    dsimp [m] at hgt hpack
    omega
  let cnt : ℕ → ℕ → ℕ → ℕ := fun α β γ =>
    Nat.find (show ∃ i, ¬ (F (α, β, γ, i)).Dom from
      ⟨2 ^ (β + γ + c), hNoDom α β γ⟩)
  have hNoAtCnt : ∀ α β γ, ¬ (F (α, β, γ, cnt α β γ)).Dom := by
    intro α β γ
    exact Nat.find_spec (show ∃ i, ¬ (F (α, β, γ, i)).Dom from
      ⟨2 ^ (β + γ + c), hNoDom α β γ⟩)
  have hDomIff : ∀ α β γ i,
      (F (α, β, γ, i)).Dom ↔ i < cnt α β γ := by
    intro α β γ i
    constructor
    · intro hi
      by_contra hnot
      have hle : cnt α β γ ≤ i := Nat.le_of_not_gt hnot
      apply hNoAtCnt α β γ
      by_cases heq : i = cnt α β γ
      · simpa [heq] using hi
      · exact hPrefix α β γ i hi (cnt α β γ) (by omega)
    · intro hi
      by_contra hnot
      have hle : cnt α β γ ≤ i := by
        dsimp [cnt]
        exact Nat.find_min' (show ∃ j, ¬ (F (α, β, γ, j)).Dom from
          ⟨2 ^ (β + γ + c), hNoDom α β γ⟩) hnot
      omega
  have hP : ∀ α β γ, ∀ i < cnt α β γ, P α β γ (U α β γ i) := by
    intro α β γ i hi
    exact (hListed α β γ i ((hDomIff α β γ i).2 hi)).1
  have hBound : ∀ α β γ, cnt α β γ * 2 ^ (2 * α) ≤ 2 ^ (β + γ + c) := by
    intro α β γ
    let S := (Finset.range (cnt α β γ)).image (U α β γ)
    have hS : ∀ X ∈ S, P α β γ X := by
      intro X hX
      rcases Finset.mem_image.mp hX with ⟨i, hi, rfl⟩
      exact hP α β γ i (by simpa only [Finset.mem_range] using hi)
    have hSep : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y →
        (X ∩ Y).card * 2 ^ (β + c) < 2 ^ (2 * α) := by
      intro X hX Y hY hXY
      rcases Finset.mem_image.mp hX with ⟨i, hi, rfl⟩
      rcases Finset.mem_image.mp hY with ⟨j, hj, rfl⟩
      have hij : i ≠ j := by
        intro heq
        subst j
        exact hXY rfl
      exact hSeparated α β γ i j hij
        ((hDomIff α β γ i).2 (by simpa only [Finset.mem_range] using hi))
        ((hDomIff α β γ j).2 (by simpa only [Finset.mem_range] using hj))
    have hinj : Set.InjOn (U α β γ) (↑(Finset.range (cnt α β γ))) := by
      intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_range] at hi hj
      by_contra hne
      have hsep := hSeparated α β γ i j hne
        ((hDomIff α β γ i).2 (by omega)) ((hDomIff α β γ j).2 (by omega))
      have hself := hSelf α β γ (U α β γ i) (hP α β γ i (by omega))
      have hge : 2 ^ (2 * α) ≤
          (U α β γ i ∩ U α β γ j).card * 2 ^ (β + c) := by
        simpa [hij] using hself
      exact (not_le_of_gt hsep hge)
    have hcard : S.card = cnt α β γ := by
      dsimp [S]
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hpack := hPack α β γ S hS hSep
    simpa [hcard] using hpack
  refine ⟨c, cnt, U, ?_, ?_⟩
  · refine ⟨F, hF, ?_⟩
    intro α β γ i s
    constructor
    · intro hs
      have hd : (F (α, β, γ, i)).Dom := Part.dom_iff_mem.mpr ⟨s, hs⟩
      refine ⟨(hDomIff α β γ i).mp hd, ?_⟩
      exact (hListed α β γ i hd).2 s hs
    · rintro ⟨hi, rfl⟩
      have hd := (hDomIff α β γ i).2 hi
      have hv := Part.get_mem hd
      have heq := (hListed α β γ i hd).2 _ hv
      have hval : (F (α, β, γ, i)).get hd = finsetListCode (U α β γ i) := heq
      rw [← hval]
      exact hv
  · intro α β γ
    refine ⟨hP α β γ, ?_, hBound α β γ⟩
    intro X hX
    obtain ⟨i, hi, hcover⟩ := hCovers α β γ X hX
    exact ⟨i, (hDomIff α β γ i).mp hi, hcover⟩

/-- Auxiliary counting: fewer than `2 ^ β` strings `y` have `K(y | x) < β`. -/
private theorem lemma5_ball_card (D : Map) (hD : isOptimalConditional D) (x : BitString)
    (β : ℕ) (S : Finset BitString) (hS : ∀ y ∈ S, natCondK D y x < β) : S.card < 2 ^ β := by
  rcases Nat.eq_zero_or_pos β with rfl | hβ
  · have : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      exact absurd (hS y hy) (Nat.not_lt_zero _)
    simp [this]
  · have hsub : S ⊆ compressibleWords D x (β - 1) := by
      intro y hy
      rw [mem_compressibleWords_iff]
      have h1 := hS y hy
      have hne : condK D y x ≠ ⊤ := by
        obtain ⟨c, hc⟩ := condK_le_plainK D hD
        obtain ⟨c', hc'⟩ := plainK_le_length D hD
        have hp : plainK D y ≠ ⊤ := ne_top_of_le_natCast_add (hc' y)
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hp
        refine ne_top_of_le_natCast (n := k + c) ((hc y x).trans ?_)
        rw [← hk]
        push_cast
        exact le_rfl
      have h2 := ENat.natCast_toNat hne
      have h3 : natCondK D y x ≤ β - 1 := by omega
      calc condK D y x = (natCondK D y x : ℕ∞) := h2.symm
        _ ≤ ((β - 1 : ℕ) : ℕ∞) := by exact_mod_cast h3
    have := (Finset.card_le_card hsub).trans_lt (card_compressibleWordsLt D x (β - 1))
    rwa [Nat.sub_add_cancel hβ] at this

/-- Every `(α, β, γ)`-bunch covers itself,
`2 ^ (2α) ≤ |X| · 2 ^ (β + 4)`.  Indeed `|X| = 2 ^ α` and `α < β`: `X` is non-empty, and for
`x ∈ X` all of `X` lies in `{y : K(y | x) < β}`, which has fewer than `2 ^ β` elements. -/
private theorem lemma5_self_cover (D : Map) (hD : isOptimalConditional D)
    (α β γ : ℕ) (X : Finset BitString) (hX : IsBunch D α β γ X) :
    2 ^ (2 * α) ≤ X.card * 2 ^ (β + 4) := by
  obtain ⟨hcard, hcond, -⟩ := hX
  have hne : X.Nonempty := by
    rw [← Finset.card_pos, hcard]; exact Nat.pow_pos (by omega)
  obtain ⟨x, hx⟩ := hne
  have hlt := lemma5_ball_card D hD x β X (fun y hy => hcond y hy x hx)
  rw [hcard] at hlt ⊢
  have hαβ : α < β := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  calc 2 ^ (2 * α) = 2 ^ α * 2 ^ α := by rw [two_mul, pow_add]
    _ ≤ 2 ^ α * 2 ^ (β + 4) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

/-- A family `S` of
`(α, β, γ)`-bunches with pairwise intersections `|X ∩ Y| · 2 ^ (β + 4) < 2 ^ (2α)` satisfies
`|S| · 2 ^ (2α) ≤ 2 ^ (β + γ + 4)`.  Proof: fewer than `2 ^ γ` strings `x` have `K(x) < γ`, and
every set of `S` consists of such strings.  For each such `x`, the sets of `S` containing `x`
all lie in `{y : K(y | x) < β}` (fewer than `2 ^ β` elements), have `2 ^ α` elements each and
pairwise intersections `< 2 ^ (2α − β − 4)`; by the Bonferroni inequality
`m · 2 ^ α − m² · 2 ^ (2α − β − 5) ≤ 2 ^ β` there are fewer than `2 ^ (β − α + 3)` of them.
Double counting `Σₓ #{X ∈ S : x ∈ X} = |S| · 2 ^ α` gives the bound. -/
private theorem lemma5_packing_bound_local (D : Map) (hD : isOptimalConditional D)
    (α β γ : ℕ) (x : BitString) (T : Finset (Finset BitString))
    (hT : ∀ X ∈ T, IsBunch D α β γ X) (hx : ∀ X ∈ T, x ∈ X)
    (hSep : ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y →
      (X ∩ Y).card * 2 ^ (β + 4) < 2 ^ (2 * α)) :
    T.card * 2 ^ α ≤ 2 ^ (β + 2) := by
  classical
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · simp [hTe]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 2 ^ α := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 ^ β := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; exact Nat.pow_pos (by omega)
  have h2a : 2 ^ (2 * α) = a * a := by rw [ha, two_mul, pow_add]
  have hq4 : 2 ^ (β + 4) = 16 * q := by rw [hq, pow_add]; ring
  have hq2 : 2 ^ (β + 2) = 4 * q := by rw [hq, pow_add]; ring
  obtain ⟨W, hW⟩ : ∃ W : Finset BitString, W = T.biUnion id := ⟨_, rfl⟩
  have hmemW : ∀ y, y ∈ W ↔ ∃ X ∈ T, y ∈ X := by
    intro y; rw [hW]; simp
  have hWcard : W.card < q := by
    rw [hq]
    refine lemma5_ball_card D hD x β W (fun y hy => ?_)
    obtain ⟨X, hXT, hyX⟩ := (hmemW y).mp hy
    exact (hT X hXT).2.1 y hyX x (hx X hXT)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = (a * a - 1) / (16 * q) := ⟨_, rfl⟩
  have hqpos : 0 < 16 * q := by rw [hq]; positivity
  have ht1 : ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → (X ∩ Y).card ≤ t := by
    intro X hX Y hY hXY
    have h := hSep X hX Y hY hXY
    rw [h2a, hq4] at h
    rw [ht, Nat.le_div_iff_mul_le hqpos]
    omega
  have ht2 : 16 * q * t < a * a := by
    have h1 : t * (16 * q) ≤ a * a - 1 := by
      rw [ht]; exact Nat.div_mul_le_self _ _
    have : 0 < a * a := Nat.mul_pos hapos hapos
    rw [mul_comm]; omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = T.card := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm]; exact Finset.card_pos.mpr hTne
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ∑ X ∈ T, X.card := ⟨_, rfl⟩
  have hLval : L = m * a := by
    rw [hL]
    calc ∑ X ∈ T, X.card = ∑ X ∈ T, a := by
          apply Finset.sum_congr rfl
          intro X hX
          calc X.card = 2 ^ α := (hT X hX).1
            _ = a := ha.symm
      _ = T.card * a := by simp
      _ = m * a := by rw [hm]
  obtain ⟨d, hd⟩ : ∃ d : BitString → ℕ,
      d = fun y => (T.filter fun X => y ∈ X).card := ⟨_, rfl⟩
  have hTX : ∀ X ∈ T, X ⊆ W := by
    intro X hX y hy
    rw [hW]; exact Finset.mem_biUnion.mpr ⟨X, hX, hy⟩
  have hind : ∀ C : Finset BitString, C ⊆ W →
      ∑ y ∈ W, (if y ∈ C then 1 else 0) = C.card := by
    intro C hC
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hC]
    simp
  have hdsum : ∑ y ∈ W, d y = L := by
    rw [hL, hd]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun X hX => hind X (hTX X hX)
  have hdsq : ∑ y ∈ W, d y ^ 2 = ∑ X ∈ T, ∑ Y ∈ T, (X ∩ Y).card := by
    have e1 : ∀ y, d y ^ 2 = ∑ X ∈ T, ∑ Y ∈ T,
        (if y ∈ X ∩ Y then 1 else 0) := by
      intro y
      rw [hd, sq]
      simp only [Finset.card_filter]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun Y _ => ?_
      by_cases h1 : y ∈ X <;> by_cases h2 : y ∈ Y <;> simp [h1, h2]
    simp_rw [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun X hX => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun Y hY =>
      hind (X ∩ Y) ((Finset.inter_subset_left).trans (hTX X hX))
  have hdsq2 : ∑ X ∈ T, ∑ Y ∈ T, (X ∩ Y).card ≤ L + m * m * t := by
    have hrow : ∀ X ∈ T, ∑ Y ∈ T, (X ∩ Y).card ≤ X.card + m * t := by
      intro X hX
      calc ∑ Y ∈ T, (X ∩ Y).card
          ≤ ∑ Y ∈ T, ((if X = Y then X.card else 0) + t) := by
            refine Finset.sum_le_sum fun Y hY => ?_
            by_cases hXY : X = Y
            · subst hXY; simp
            · simpa [hXY] using ht1 X hX Y hY hXY
        _ = X.card + m * t := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
            simp [hm, hX]
    calc ∑ X ∈ T, ∑ Y ∈ T, (X ∩ Y).card
        ≤ ∑ X ∈ T, (X.card + m * t) := Finset.sum_le_sum hrow
      _ = L + m * m * t := by
          rw [hL, Finset.sum_add_distrib]
          simp [hm]
          ring
  have hcs : L * L ≤ W.card * (L + m * m * t) := by
    have h := sq_sum_le_card_mul_sum_sq (s := W) (f := d)
    rw [hdsum, hdsq, sq] at h
    exact h.trans (Nat.mul_le_mul_left _ hdsq2)
  have hmgoal : m * a ≤ 4 * q := by
    by_contra hcon
    push Not at hcon
    have hWle : W.card ≤ q := hWcard.le
    have hcs' : L * L ≤ q * (L + m * m * t) :=
      hcs.trans (Nat.mul_le_mul_right _ hWle)
    have hprod : (16 * q * t) * (m * m) < (a * a) * (m * m) :=
      Nat.mul_lt_mul_of_pos_right ht2 (Nat.mul_pos hmpos hmpos)
    have hP : 16 * (q * (m * m * t)) < L * L := by
      rw [hLval]
      nlinarith [hprod]
    have hQ : L * L ≤ q * L + q * (m * m * t) := by nlinarith [hcs']
    have hineq : 15 * (L * L) < 16 * (q * L) := by omega
    have hLpos : 0 < L := by rw [hLval]; exact Nat.mul_pos hmpos hapos
    nlinarith [Nat.mul_pos hqpos hLpos]
  simpa [hm, ha, hq2] using hmgoal

private theorem lemma5_packing_bound (D : Map) (hD : isOptimalConditional D)
    (α β γ : ℕ) (S : Finset (Finset BitString))
    (hS : ∀ X ∈ S, IsBunch D α β γ X)
    (hSep : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → (X ∩ Y).card * 2 ^ (β + 4) < 2 ^ (2 * α)) :
    S.card * 2 ^ (2 * α) ≤ 2 ^ (β + γ + 4) := by
  classical
  obtain ⟨W, hW⟩ : ∃ W : Finset BitString, W = S.biUnion id := ⟨_, rfl⟩
  have hmemW : ∀ y, y ∈ W ↔ ∃ X ∈ S, y ∈ X := by
    intro y; rw [hW]; simp
  have hWcard : W.card < 2 ^ γ :=
    lemma5_ball_card D hD [] γ W (fun y hy => by
      obtain ⟨X, hXS, hyX⟩ := (hmemW y).mp hy
      exact (hS X hXS).2.2 y hyX)
  have hdouble : ∑ x ∈ W, (S.filter fun X => x ∈ X).card = ∑ X ∈ S, X.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun X hXS => ?_
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,
      fun h => ⟨(hmemW y).mpr ⟨X, hXS, h⟩, h⟩⟩
  have hsumcard : ∑ X ∈ S, X.card = S.card * 2 ^ α := by
    rw [Finset.sum_congr rfl fun X hXS => (hS X hXS).1]
    simp
  have hloc : ∀ x ∈ W, (S.filter fun X => x ∈ X).card * 2 ^ α ≤ 2 ^ (β + 2) := by
    intro x _
    exact lemma5_packing_bound_local D hD α β γ x
      (S.filter fun X => x ∈ X)
      (fun X hX => hS X (Finset.mem_filter.mp hX).1)
      (fun X hX => (Finset.mem_filter.mp hX).2)
      (fun X hX Y hY hXY =>
        hSep X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hXY)
  have hmain : S.card * 2 ^ α * 2 ^ α ≤ W.card * 2 ^ (β + 2) := by
    calc S.card * 2 ^ α * 2 ^ α =
          (∑ x ∈ W, (S.filter fun X => x ∈ X).card) * 2 ^ α := by
          rw [hdouble, hsumcard]
      _ = ∑ x ∈ W, (S.filter fun X => x ∈ X).card * 2 ^ α := Finset.sum_mul _ _ _
      _ ≤ ∑ x ∈ W, 2 ^ (β + 2) := Finset.sum_le_sum hloc
      _ = W.card * 2 ^ (β + 2) := by simp
  calc S.card * 2 ^ (2 * α) = S.card * 2 ^ α * 2 ^ α := by
        rw [two_mul, pow_add, mul_assoc]
    _ ≤ W.card * 2 ^ (β + 2) := hmain
    _ ≤ 2 ^ γ * 2 ^ (β + 2) := Nat.mul_le_mul_right _ hWcard.le
    _ ≤ 2 ^ (β + γ + 4) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)

/-- **Lemma 5** (Romashchenko).  The `(α, β, γ)`-bunches have a standard cover: an algorithm
lists bunches `U₀, …, U_q`, `q < 2 ^ (β + γ − 2α + O(1))`, such that every bunch `U` has
`|U ∩ Uᵢ| ≥ 2 ^ (β − ε)` for some `i`, `ε = 2(β − α) + O(1)`. -/
theorem lemma5 (D : Map) (hD : isOptimalConditional D) : HasStandardCover (IsBunch D) := by
  obtain ⟨E, hE, hSound, hComplete⟩ := lemma5_enumerate_bunches D hD
  exact lemma5_greedy_enumeration (IsBunch D) E hE hSound hComplete 4
    (fun α β γ X hX => lemma5_self_cover D hD α β γ X hX)
    (fun α β γ S hS hSep => lemma5_packing_bound D hD α β γ S hS hSep)

/-- The finite list operations in the stage checker preserve primitive recursiveness. -/
private theorem lemma6_checker_primrec
    (short : (ℕ × BitString × BitString) × ℕ → Bool) (hshort : Primrec short) :
    Primrec (fun r : (((ℕ × ℕ × ℕ) × List BitString) × ℕ) =>
      let X := r.1.2.toFinset
      let L := canonicalFinsetList X
      decide (L.length = 2 ^ r.1.1.1) &&
        L.all (fun x₁ => decide (L.length < 2 *
          L.countP (fun x₂ => short ((r.1.1.2.1, x₁, x₂), r.2)))) &&
        L.all (fun x => short ((r.1.1.2.2, [], x), r.2))) := by
  let R := (((ℕ × ℕ × ℕ) × List BitString) × ℕ)
  have hL : Primrec (fun r : R => canonicalFinsetList r.1.2.toFinset) :=
    canonicalFinsetList_toFinset_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  have hlength : Primrec (fun r : R => (canonicalFinsetList r.1.2.toFinset).length) :=
    Primrec.list_length.comp hL
  have halpha : Primrec (fun r : R => r.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hpow : Primrec (fun r : R => 2 ^ r.1.1.1) := by
    have hpow₂ : Primrec₂ (fun (a b : ℕ) => a ^ b) :=
      Primrec.nat_iff.mpr Nat.Primrec.pow
    exact hpow₂.comp (Primrec.const 2) halpha
  have hsize : Primrec (fun r : R =>
      decide ((canonicalFinsetList r.1.2.toFinset).length = 2 ^ r.1.1.1)) :=
    (PrimrecRel.comp Primrec.eq hlength hpow).decide
  have hL' : Primrec (fun u : R × BitString => canonicalFinsetList u.1.1.2.toFinset) :=
    hL.comp Primrec.fst
  have hBetaR : Primrec (fun r : R => r.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hBeta : Primrec (fun w : (R × BitString) × BitString => w.1.1.1.1.2.1) :=
    hBetaR.comp (Primrec.fst.comp Primrec.fst)
  have hX₁ : Primrec (fun w : (R × BitString) × BitString => w.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hStage : Primrec (fun w : (R × BitString) × BitString => w.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hShortArgs : Primrec (fun w : (R × BitString) × BitString =>
      ((w.1.1.1.1.2.1, w.1.2, w.2), w.1.1.2)) := by
    exact Primrec.pair (Primrec.pair hBeta (Primrec.pair hX₁ Primrec.snd)) hStage
  have hCountPred : Primrec₂ (fun (u : R × BitString) (x₂ : BitString) =>
      short ((u.1.1.1.2.1, u.2, x₂), u.1.2)) :=
    (hshort.comp hShortArgs).to₂
  have hCount : Primrec (fun u : R × BitString =>
      (canonicalFinsetList u.1.1.2.toFinset).countP
        (fun x₂ => short ((u.1.1.1.2.1, u.2, x₂), u.1.2))) :=
    list_countP_primrec hL' hCountPred
  have hLength' : Primrec (fun u : R × BitString =>
      (canonicalFinsetList u.1.1.2.toFinset).length) :=
    hlength.comp Primrec.fst
  have hTwiceCount : Primrec (fun u : R × BitString => 2 *
      (canonicalFinsetList u.1.1.2.toFinset).countP
        (fun x₂ => short ((u.1.1.1.2.1, u.2, x₂), u.1.2))) :=
    Primrec.nat_mul.comp (Primrec.const 2) hCount
  have hMajorPred : Primrec₂ (fun (r : R) (x₁ : BitString) =>
      decide ((canonicalFinsetList r.1.2.toFinset).length <
        2 * (canonicalFinsetList r.1.2.toFinset).countP
          (fun x₂ => short ((r.1.1.2.1, x₁, x₂), r.2)))) := by
    have hMajor : Primrec (fun u : R × BitString =>
        decide ((canonicalFinsetList u.1.1.2.toFinset).length <
          2 * (canonicalFinsetList u.1.1.2.toFinset).countP
            (fun x₂ => short ((u.1.1.1.2.1, u.2, x₂), u.1.2)))) :=
      (PrimrecRel.comp Primrec.nat_lt hLength' hTwiceCount).decide
    exact hMajor.to₂
  have hMajorAll : Primrec (fun r : R =>
      (canonicalFinsetList r.1.2.toFinset).all (fun x₁ =>
        decide ((canonicalFinsetList r.1.2.toFinset).length <
          2 * (canonicalFinsetList r.1.2.toFinset).countP
            (fun x₂ => short ((r.1.1.2.1, x₁, x₂), r.2))))) :=
    list_all_primrec hL hMajorPred
  have hGamma : Primrec (fun r : R => r.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hLastPred : Primrec₂ (fun (r : R) (x : BitString) =>
      short ((r.1.1.2.2, [], x), r.2)) := by
    have hLastArgs : Primrec (fun u : R × BitString =>
        ((u.1.1.1.2.2, ([] : BitString), u.2), u.1.2)) := by
      exact Primrec.pair
        (Primrec.pair (hGamma.comp Primrec.fst)
          (Primrec.pair (Primrec.const []) Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    exact (hshort.comp hLastArgs).to₂
  have hLastAll : Primrec (fun r : R =>
      (canonicalFinsetList r.1.2.toFinset).all
        (fun x => short ((r.1.1.2.2, [], x), r.2))) :=
    list_all_primrec hL hLastPred
  have hresult : Primrec (fun r : R =>
      decide ((canonicalFinsetList r.1.2.toFinset).length = 2 ^ r.1.1.1) &&
        (canonicalFinsetList r.1.2.toFinset).all (fun x₁ =>
          decide ((canonicalFinsetList r.1.2.toFinset).length <
            2 * (canonicalFinsetList r.1.2.toFinset).countP
              (fun x₂ => short ((r.1.1.2.1, x₁, x₂), r.2)))) &&
        (canonicalFinsetList r.1.2.toFinset).all
          (fun x => short ((r.1.1.2.2, [], x), r.2))) :=
    (Primrec.and.comp (Primrec.and.comp hsize hMajorAll) hLastAll)
  exact hresult.of_eq fun _ => rfl

/-- Bounded program
witnesses give a computable finite-stage test for whether a candidate set is a semi-bunch. The
test checks that all its elements have short plain descriptions and that, for each element, enough
conditional descriptions have appeared by the stage. -/
private theorem lemma6_finite_stage_check
    (D : Map) (hD : isOptimalConditional D) :
    ∃ check : ((ℕ × ℕ × ℕ) × List BitString) × ℕ → Bool,
      Computable check ∧
      (∀ p t t', t ≤ t' → check (p, t) = true → check (p, t') = true) ∧
      ∀ p : (ℕ × ℕ × ℕ) × List BitString,
        IsSemiBunch D p.1.1 p.1.2.1 p.1.2.2 p.2.toFinset ↔
          ∃ t, check (p, t) = true := by
  classical
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hD.1
  let short : (ℕ × BitString × BitString) × ℕ → Bool := fun q =>
    decide (0 < q.1.1) &&
      decide (q.1.2.2 ∈ conditionalOutputSnapshot c q.1.2.1 (q.1.1 - 1) q.2)
  have hshortPR : Primrec short := by
    have hbound : Primrec (fun q : (ℕ × BitString × BitString) × ℕ =>
        decide (0 < q.1.1)) :=
      (PrimrecRel.comp Primrec.nat_lt (Primrec.const 0)
        (Primrec.fst.comp Primrec.fst)).decide
    have hsnapshot : Primrec (fun q : (ℕ × BitString × BitString) × ℕ =>
        conditionalOutputSnapshot c q.1.2.1 (q.1.1 - 1) q.2) := by
      have hargs : Primrec (fun q : (ℕ × BitString × BitString) × ℕ =>
          ((q.1.2.1, q.1.1 - 1), q.2)) :=
        Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1)))
          Primrec.snd
      exact (conditionalOutputSnapshot_primrec c).comp hargs
    have hmemPred : Primrec₂ (fun (q : (ℕ × BitString × BitString) × ℕ)
        (y : BitString) => decide (q.1.2.2 = y)) := by
      exact (PrimrecRel.comp Primrec.eq
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd).decide.to₂
    have hmemAny : Primrec (fun q : (ℕ × BitString × BitString) × ℕ =>
        (conditionalOutputSnapshot c q.1.2.1 (q.1.1 - 1) q.2).any
          (fun y => decide (q.1.2.2 = y))) := list_any_primrec hsnapshot hmemPred
    have hmem : Primrec (fun q : (ℕ × BitString × BitString) × ℕ =>
        decide (q.1.2.2 ∈ conditionalOutputSnapshot c q.1.2.1
          (q.1.1 - 1) q.2)) := hmemAny.of_eq fun q => by
      apply Bool.eq_iff_iff.mpr
      rw [List.any_eq_true]
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨y, hy, hEq⟩
        simpa [hEq] using hy
      · intro hy
        exact ⟨q.1.2.2, hy, rfl⟩
    exact (Primrec.and.comp hbound hmem).of_eq fun _ => rfl
  have hshort_mono : ∀ q s t, s ≤ t → short (q, s) = true → short (q, t) = true := by
    intro q s t hst hs
    simp only [short, Bool.and_eq_true, decide_eq_true_eq] at hs ⊢
    refine ⟨hs.1, ?_⟩
    have hmem := hs.2
    unfold conditionalOutputSnapshot at hmem ⊢
    rw [List.mem_filterMap] at hmem ⊢
    obtain ⟨p, hp, hout⟩ := hmem
    exact ⟨p, hp, conditionalRunOut_mono c hst hout⟩
  have hshort_eventually : ∀ b x y,
      (∃ t, short ((b, x, y), t) = true) ↔ natCondK D y x < b := by
    intro b x y
    constructor
    · rintro ⟨t, ht⟩
      simp only [short, Bool.and_eq_true, decide_eq_true_eq] at ht
      obtain ⟨hb, hout⟩ := ht
      unfold conditionalOutputSnapshot at hout
      rw [List.mem_filterMap] at hout
      obtain ⟨p, hp, hrun⟩ := hout
      have hpLen : p.length ≤ b - 1 := (mem_boundedPrograms_iff p (b - 1)).mp hp
      have hprod := conditionalRunOut_sound hc hrun
      have hK := (condK_le_iff D y x p.length).2 ⟨p, le_rfl, hprod⟩
      have hNat : natCondK D y x ≤ p.length := ENat.toNat_le_of_le_natCast hK
      omega
    · intro hlt
      have hfinite : condK D y x ≠ ⊤ := by
        obtain ⟨cCond, hcCond⟩ := condK_le_plainK D hD
        obtain ⟨cPlain, hcPlain⟩ := plainK_le_length D hD
        apply ne_top_of_le_natCast
        calc
          condK D y x ≤ plainK D y + (cCond : ℕ∞) := hcCond y x
          _ ≤ (y.length : ℕ∞) + (cPlain : ℕ∞) + (cCond : ℕ∞) := by
            gcongr
            exact hcPlain y
          _ = ((y.length + cPlain + cCond : ℕ) : ℕ∞) := by simp [Nat.cast_add]
      have hNatCast := ENat.natCast_toNat hfinite
      have hb : 0 < b := by omega
      have hNatLe : natCondK D y x ≤ b - 1 := by omega
      have hK : condK D y x ≤ ((b - 1 : ℕ) : ℕ∞) := by
        rw [← hNatCast]
        exact_mod_cast hNatLe
      obtain ⟨p, hpLen, hprod⟩ := (condK_le_iff D y x (b - 1)).1 hK
      obtain ⟨t, hrun⟩ := conditionalRunOut_complete hc hprod
      refine ⟨t, ?_⟩
      simp only [short, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hb, ?_⟩
      exact mem_conditionalOutputSnapshot_of_run hpLen hrun
  let check : (((ℕ × ℕ × ℕ) × List BitString) × ℕ) → Bool := fun r =>
    let X := r.1.2.toFinset
    let L := canonicalFinsetList X
    decide (L.length = 2 ^ r.1.1.1) &&
      L.all (fun x₁ => decide (L.length < 2 *
        L.countP (fun x₂ => short ((r.1.1.2.1, x₁, x₂), r.2)))) &&
      L.all (fun x => short ((r.1.1.2.2, [], x), r.2))
  have hcheckPR : Primrec check := by
    change Primrec (fun r : (((ℕ × ℕ × ℕ) × List BitString) × ℕ) =>
      let X := r.1.2.toFinset
      let L := canonicalFinsetList X
      decide (L.length = 2 ^ r.1.1.1) &&
        L.all (fun x₁ => decide (L.length < 2 *
          L.countP (fun x₂ => short ((r.1.1.2.1, x₁, x₂), r.2)))) &&
        L.all (fun x => short ((r.1.1.2.2, [], x), r.2)))
    exact lemma6_checker_primrec
      short hshortPR
  have hcheck : Computable check := hcheckPR.to_comp
  refine ⟨check, hcheck, ?_, ?_⟩
  · intro p t t' htt' hpass
    let X := p.2.toFinset
    let L := canonicalFinsetList X
    have hpass' : check (p, t) = true := hpass
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hpass' ⊢
    rcases hpass' with ⟨⟨hsize, hmajor⟩, hplain⟩
    refine ⟨⟨hsize, ?_⟩, ?_⟩
    · intro x₁ hx₁
      have hcount :
          (L.countP fun x₂ => short ((p.1.2.1, x₁, x₂), t)) ≤
            L.countP (fun x₂ => short ((p.1.2.1, x₁, x₂), t')) := by
        exact List.countP_mono_left (fun x₂ _ hx₂ => hshort_mono
          (p.1.2.1, x₁, x₂) t t' htt' hx₂)
      have hmajor' : L.length < 2 *
          L.countP (fun x₂ => short ((p.1.2.1, x₁, x₂), t)) := by
        simpa [L] using hmajor x₁ hx₁
      exact Nat.lt_of_lt_of_le hmajor' (Nat.mul_le_mul_left 2 hcount)
    · intro x hx
      exact hshort_mono (p.1.2.2, [], x) t t' htt' (hplain x hx)
  · intro p
    let X : Finset BitString := p.2.toFinset
    let L : List BitString := canonicalFinsetList X
    have hmemL : ∀ x, x ∈ L ↔ x ∈ X := by simp [L]
    have hlenL : L.length = X.card := by simp [L]
    have hcountK (x₁ : BitString) :
        L.countP (fun x₂ => decide (natCondK D x₂ x₁ < p.1.2.1)) =
          (X.filter fun x₂ => natCondK D x₂ x₁ < p.1.2.1).card := by
      calc
        L.countP (fun x₂ => decide (natCondK D x₂ x₁ < p.1.2.1)) =
            ((L.filter fun x₂ => decide (natCondK D x₂ x₁ < p.1.2.1)).toFinset).card := by
              rw [List.countP_eq_length_filter,
                List.toFinset_card_of_nodup ((canonicalFinsetList_nodup X).filter _)]
        _ = (X.filter fun x₂ => natCondK D x₂ x₁ < p.1.2.1).card := by
              congr 1
              ext x₂
              simp [L, X, List.mem_toFinset,
                decide_eq_true_eq]
    have hstage_le_K (x₁ : BitString) (s : ℕ) :
        L.countP (fun x₂ => short ((p.1.2.1, x₁, x₂), s)) ≤
          (X.filter fun x₂ => natCondK D x₂ x₁ < p.1.2.1).card := by
      calc
        L.countP (fun x₂ => short ((p.1.2.1, x₁, x₂), s)) ≤
            L.countP (fun x₂ => decide (natCondK D x₂ x₁ < p.1.2.1)) :=
          List.countP_mono_left (fun x₂ _ hs =>
            decide_eq_true_eq.mpr
              ((hshort_eventually p.1.2.1 x₁ x₂).mp ⟨s, hs⟩))
        _ = (X.filter fun x₂ => natCondK D x₂ x₁ < p.1.2.1).card := hcountK x₁
    have hK_le_stage (x₁ : BitString) (s : ℕ)
        (hs : ∀ x₂ ∈ L, natCondK D x₂ x₁ < p.1.2.1 →
          short ((p.1.2.1, x₁, x₂), s) = true) :
        (X.filter fun x₂ => natCondK D x₂ x₁ < p.1.2.1).card ≤
          L.countP (fun x₂ => short ((p.1.2.1, x₁, x₂), s)) := by
      rw [← hcountK x₁]
      exact List.countP_mono_left (fun x₂ hx₂ hxK => hs x₂ hx₂
        (decide_eq_true_eq.mp hxK))
    constructor
    · intro hSemi
      have hSize : L.length = 2 ^ p.1.1 := by simpa [L, X] using hSemi.1
      let majority : BitString → ℕ → Bool := fun x₁ s =>
        decide (L.length < 2 * L.countP (fun x₂ => short ((p.1.2.1, x₁, x₂), s)))
      have hmajorMono : ∀ x₁ s s', s ≤ s' → majority x₁ s = true →
          majority x₁ s' = true := by
        intro x₁ s s' hss' hs
        have hcount :
            L.countP (fun x₂ => short ((p.1.2.1, x₁, x₂), s)) ≤
              L.countP (fun x₂ => short ((p.1.2.1, x₁, x₂), s')) :=
          List.countP_mono_left (fun x₂ _ hx₂ => hshort_mono
            (p.1.2.1, x₁, x₂) s s' hss' hx₂)
        simp only [majority, decide_eq_true_eq] at hs ⊢
        omega
      have hmajorExists : ∀ x₁ ∈ L, ∃ s, majority x₁ s = true := by
        intro x₁ hx₁
        have hxX : x₁ ∈ X := (hmemL x₁).mp hx₁
        let KList := L.filter (fun x₂ => decide (natCondK D x₂ x₁ < p.1.2.1))
        obtain ⟨s, hs⟩ := lemma5_common_stage
          (fun x₂ s => short ((p.1.2.1, x₁, x₂), s))
          (fun x₂ s s' hss' hx₂ => hshort_mono (p.1.2.1, x₁, x₂) s s' hss' hx₂)
          KList (fun x₂ hx₂ => by
            have hx₂K := (List.mem_filter.mp hx₂).2
            exact (hshort_eventually p.1.2.1 x₁ x₂).2 (decide_eq_true_eq.mp hx₂K))
        have hsAll : ∀ x₂ ∈ L, natCondK D x₂ x₁ < p.1.2.1 →
            short ((p.1.2.1, x₁, x₂), s) = true := by
          intro x₂ hx₂ hx₂K
          exact hs x₂ (List.mem_filter.mpr ⟨hx₂, decide_eq_true_eq.mpr hx₂K⟩)
        have hcount := hK_le_stage x₁ s hsAll
        have hsemi : L.length < 2 *
            (X.filter fun x₂ => natCondK D x₂ x₁ < p.1.2.1).card := by
          have hsemiX : X.card < 2 *
              (X.filter fun x₂ => natCondK D x₂ x₁ < p.1.2.1).card := by
            simpa [X] using hSemi.2.1 x₁ hxX
          simpa [hlenL] using hsemiX
        have hstage := Nat.mul_le_mul_left 2 hcount
        refine ⟨s, ?_⟩
        simp only [majority, decide_eq_true_eq]
        exact Nat.lt_of_lt_of_le hsemi hstage
      obtain ⟨sCond, hsCond⟩ :=
        lemma5_common_stage majority hmajorMono
          L hmajorExists
      have hplainExists : ∀ x ∈ L, ∃ s, short ((p.1.2.2, [], x), s) = true := by
        intro x hx
        have hxX : x ∈ X := (hmemL x).mp hx
        exact (hshort_eventually p.1.2.2 [] x).2
          (by simpa [natK, plainK, natCondK] using hSemi.2.2 x hxX)
      obtain ⟨sPlain, hsPlain⟩ :=
        lemma5_common_stage
          (fun x s => short ((p.1.2.2, [], x), s))
          (fun x s s' hss' hx => hshort_mono (p.1.2.2, [], x) s s' hss' hx)
          L hplainExists
      let t := max sCond sPlain
      have hmajorAt : ∀ x₁ ∈ L, majority x₁ t = true := by
        intro x₁ hx₁
        exact hmajorMono x₁ sCond t (le_max_left _ _) (hsCond x₁ hx₁)
      have hplainAt : ∀ x ∈ L, short ((p.1.2.2, [], x), t) = true := by
        intro x hx
        exact hshort_mono (p.1.2.2, [], x) sPlain t (le_max_right _ _)
          (hsPlain x hx)
      have hcheckT : check (p, t) = true := by
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        refine ⟨⟨hSize, ?_⟩, hplainAt⟩
        intro x₁ hx₁
        simpa [majority, L] using hmajorAt x₁ hx₁
      exact ⟨t, hcheckT⟩
    · rintro ⟨t, ht⟩
      have hraw : check (p, t) = true := ht
      have hraw' := hraw
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hraw'
      rcases hraw' with ⟨⟨hSize, hMajor⟩, hPlain⟩
      have hcard : X.card = 2 ^ p.1.1 := by
        simpa [L, X] using hSize
      refine ⟨hcard, ?_, ?_⟩
      · intro x₁ hx₁
        have hxL : x₁ ∈ L := (hmemL x₁).mpr hx₁
        have hmajor := hMajor x₁ hxL
        have hcount := hstage_le_K x₁ t
        have hmajorL : L.length < 2 * L.countP
            (fun x₂ => short ((p.1.2.1, x₁, x₂), t)) := by
          simpa [L] using hmajor
        change X.card < 2 * (X.filter fun x₂ => natCondK D x₂ x₁ < p.1.2.1).card
        rw [← hlenL]
        exact Nat.lt_of_lt_of_le hmajorL (Nat.mul_le_mul_left 2 hcount)
      · intro x hx
        have hxL : x ∈ L := (hmemL x).mpr hx
        have h := hPlain x hxL
        simpa [natK, plainK, natCondK] using (hshort_eventually p.1.2.2 [] x).mp ⟨t, h⟩

/-- Semi-bunches can be enumerated uniformly. A partial
recursive `E` outputs only codes `finsetListCode X` of `(α, β, γ)`-semi-bunches `X`, and every
`(α, β, γ)`-semi-bunch has its code output at some index.  (Membership in a semi-bunch is
recursively enumerable, uniformly in `(α, β, γ, X)`: the conditions `K(y | x) < β` and
`K(x) < γ` are witnessed by short programs of the partial recursive `D`, and the majority
condition `|X| < 2 · #{y ∈ X : K(y | x) < β}` is a finite check on the witnessed pairs; dovetail
over all finite sets and all finite stages.) -/
private theorem lemma6_enumerate_semibunches (D : Map) (hD : isOptimalConditional D) :
    ∃ E : ℕ × ℕ × ℕ × ℕ →. BitString, Partrec E ∧
      (∀ α β γ i s, s ∈ E (α, β, γ, i) →
        ∃ X : Finset BitString, s = finsetListCode X ∧ IsSemiBunch D α β γ X) ∧
      (∀ α β γ (X : Finset BitString), IsSemiBunch D α β γ X →
        ∃ i, finsetListCode X ∈ E (α, β, γ, i)) := by
  classical
  obtain ⟨check, hcheck, -, hcheck_iff⟩ :=
    lemma6_finite_stage_check D hD
  have hcheckRE : IsRE (fun q : ((ℕ × ℕ × ℕ) × List BitString) × ℕ =>
      check q = true) :=
    isRE_of_computable_bool _ check (fun _ => Iff.rfl) hcheck
  have hSemiRE : IsRE (fun p : (ℕ × ℕ × ℕ) × List BitString =>
      IsSemiBunch D p.1.1 p.1.2.1 p.1.2.2 p.2.toFinset) :=
    IsRE.of_iff (IsRE.exists_encodable hcheckRE) (fun p => (hcheck_iff p).symm)
  obtain ⟨G, hG, hGdom⟩ :=
    hSemiRE
  let idx : ℕ × ℕ × ℕ × ℕ → ℕ := fun q => q.2.2.2
  let params : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ :=
    fun q => (q.1, q.2.1, q.2.2.1)
  let E : ℕ × ℕ × ℕ × ℕ →. BitString := fun q =>
    (Part.ofOption (Encodable.decode (α := List BitString) (idx q))).bind fun l =>
      (G (params q, l)).map fun _ => finsetListCode l.toFinset
  have hidx : Computable idx :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd))
  have hdecode : Partrec fun q : ℕ × ℕ × ℕ × ℕ =>
      Part.ofOption (Encodable.decode (α := List BitString) (idx q)) :=
    Computable.ofOption (Computable.decode.comp hidx)
  have hparams : Computable params :=
    Computable.pair Computable.fst <| Computable.pair
      (Computable.fst.comp Computable.snd)
      (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have hrel : Partrec fun q : (ℕ × ℕ × ℕ × ℕ) × List BitString =>
      G (params q.1, q.2) := by
    exact hG.comp (Computable.pair (hparams.comp Computable.fst) Computable.snd)
  have hcode : Computable (fun l : List BitString => finsetListCode l.toFinset) := by
    unfold finsetListCode
    exact (listCode_primrec.comp canonicalFinsetList_toFinset_primrec).to_comp
  have hpost : Computable₂ (fun (q : (ℕ × ℕ × ℕ × ℕ) × List BitString)
      (_ : Unit) => finsetListCode q.2.toFinset) := by
    exact hcode.comp (Computable.snd.comp Computable.fst)
  have hE : Partrec E := by
    apply Partrec.of_eq (Partrec.bind hdecode (Partrec.map hrel hpost).to₂)
    intro q
    rfl
  refine ⟨E, hE, ?_, ?_⟩
  · intro α β γ i s hs
    change s ∈ E (α, β, γ, i) at hs
    simp only [E, Part.mem_bind_iff, Part.mem_ofOption, Part.mem_map_iff] at hs
    obtain ⟨X, hXdecode, u, hu, hscode⟩ := hs
    have hX : IsSemiBunch D α β γ X.toFinset := by
      apply (hGdom ((α, β, γ), X)).mp
      exact Part.dom_iff_mem.mpr ⟨u, hu⟩
    exact ⟨X.toFinset, hscode.symm, hX⟩
  · intro α β γ X hX
    refine ⟨Encodable.encode (canonicalFinsetList X), ?_⟩
    simp only [E, idx, params, Encodable.encodek, Part.mem_bind_iff,
      Part.mem_ofOption, Part.mem_map_iff]
    refine ⟨canonicalFinsetList X, rfl, (), ?_, ?_⟩
    · obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp <|
        (hGdom ((α, β, γ), canonicalFinsetList X)).mpr (by simpa using hX)
      cases u
      exact hu
    · exact congrArg finsetListCode (canonicalFinsetList_toFinset X)

open Classical in
/-- Every `(α, β, γ)`-semi-bunch covers itself,
`2 ^ (2α) ≤ |X| · 2 ^ (β + 4)`.  Indeed `|X| = 2 ^ α`, and for `x ∈ X` more than half of `X`
lies in `{y : K(y | x) < β}`, which has fewer than `2 ^ β` elements; so `2 ^ α < 2 ^ (β + 1)`. -/
private theorem lemma6_self_cover (D : Map) (hD : isOptimalConditional D)
    (α β γ : ℕ) (X : Finset BitString) (hX : IsSemiBunch D α β γ X) :
    2 ^ (2 * α) ≤ X.card * 2 ^ (β + 4) := by
  obtain ⟨hcard, hmaj, -⟩ := hX
  have hne : X.Nonempty := by
    rw [← Finset.card_pos, hcard]; exact Nat.pow_pos (by omega)
  obtain ⟨x, hx⟩ := hne
  have hlt := lemma5_ball_card D hD x β (X.filter fun y => natCondK D y x < β)
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h := hmaj x hx
  rw [hcard] at h ⊢
  have h2 : 2 ^ α < 2 ^ (β + 1) := by
    calc 2 ^ α < 2 * _ := h
      _ < 2 * 2 ^ β := by omega
      _ = 2 ^ (β + 1) := by rw [pow_succ]; ring
  have hαβ : α < β + 1 := (Nat.pow_lt_pow_iff_right (by omega)).mp h2
  calc 2 ^ (2 * α) = 2 ^ α * 2 ^ α := by rw [two_mul, pow_add]
    _ ≤ 2 ^ α * 2 ^ (β + 4) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

/-- The local packing bound at a fixed string `x` is as follows:
let `S` be a finite family of `(α, β, γ)`-semi-bunches all containing `x`, with pairwise
intersections `|X ∩ Y| · 2 ^ (β + 4) < 2 ^ (2α)`.  Then `|S| · 2 ^ α ≤ 2 ^ (β + 2)`.
Proof: let `A_X = {y ∈ X : K(y | x) < β}`; `|A_X| > 2 ^ (α - 1)`, all `A_X` lie in a set `B` with
`|B| < 2 ^ β`, and `|A_X ∩ A_Y| ≤ t`, `t · 2 ^ (β + 4) < 2 ^ (2α)`.  Cauchy–Schwarz for the
multiplicity function `d(y) = #{X : y ∈ A_X}` on `B` gives `L² ≤ |B| (L + |S|² t)`,
`L = Σ |A_X| ≥ |S| 2 ^ (α - 1)`, whence `L < 2 |B|`. -/
private theorem lemma6_local_packing (D : Map) (hD : isOptimalConditional D)
    (α β γ : ℕ) (x : BitString) (S : Finset (Finset BitString))
    (hS : ∀ X ∈ S, IsSemiBunch D α β γ X) (hx : ∀ X ∈ S, x ∈ X)
    (hSep : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → (X ∩ Y).card * 2 ^ (β + 4) < 2 ^ (2 * α)) :
    S.card * 2 ^ α ≤ 2 ^ (β + 2) := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 2 ^ α := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 ^ β := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; exact Nat.pow_pos (by omega)
  have h2a : 2 ^ (2 * α) = a * a := by rw [ha, two_mul, pow_add]
  have hq4 : 2 ^ (β + 4) = 16 * q := by rw [hq, pow_add]; ring
  have hq2 : 2 ^ (β + 2) = 4 * q := by rw [hq, pow_add]; ring
  obtain ⟨A, hA⟩ : ∃ A : Finset BitString → Finset BitString,
      A = fun X => X.filter fun y => natCondK D y x < β := ⟨_, rfl⟩
  have hAmem : ∀ X y, y ∈ A X ↔ y ∈ X ∧ natCondK D y x < β := by
    intro X y; rw [hA]; simp
  have hAsub : ∀ X, A X ⊆ X := fun X y hy => ((hAmem X y).mp hy).1
  have hAcard : ∀ X ∈ S, a < 2 * (A X).card := by
    intro X hX
    have h := (hS X hX).2.1 x (hx X hX)
    rw [(hS X hX).1, ← ha] at h
    have : A X = X.filter fun y => natCondK D y x < β := by rw [hA]
    rw [this]; exact h
  obtain ⟨B, hB⟩ : ∃ B : Finset BitString, B = S.biUnion A := ⟨_, rfl⟩
  have hAB : ∀ X ∈ S, A X ⊆ B := by
    intro X hX y hy
    rw [hB]; exact Finset.mem_biUnion.mpr ⟨X, hX, hy⟩
  have hBcard : B.card < q := by
    rw [hq]
    refine lemma5_ball_card D hD x β B (fun y hy => ?_)
    rw [hB] at hy
    obtain ⟨X, -, hyX⟩ := Finset.mem_biUnion.mp hy
    exact ((hAmem X y).mp hyX).2
  -- the threshold `t`
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = (a * a - 1) / (16 * q) := ⟨_, rfl⟩
  have hqpos : 0 < 16 * q := by rw [hq]; positivity
  have ht1 : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → (A X ∩ A Y).card ≤ t := by
    intro X hX Y hY hXY
    have h := hSep X hX Y hY hXY
    rw [h2a, hq4] at h
    have hle : (A X ∩ A Y).card ≤ (X ∩ Y).card :=
      Finset.card_le_card (Finset.inter_subset_inter (hAsub X) (hAsub Y))
    rw [ht, Nat.le_div_iff_mul_le hqpos]
    have := Nat.mul_le_mul_right (16 * q) hle
    omega
  have ht2 : 16 * q * t < a * a := by
    have h1 : t * (16 * q) ≤ a * a - 1 := by
      rw [ht]; exact Nat.div_mul_le_self _ _
    have : 0 < a * a := Nat.mul_pos hapos hapos
    rw [mul_comm]; omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = S.card := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm]; exact Finset.card_pos.mpr hSne
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ∑ X ∈ S, (A X).card := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : BitString → ℕ, d = fun y => (S.filter fun X => y ∈ A X).card :=
    ⟨_, rfl⟩
  have hind : ∀ C : Finset BitString, C ⊆ B →
      ∑ y ∈ B, (if y ∈ C then 1 else 0) = C.card := by
    intro C hC
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hC]
    simp
  have hdsum : ∑ y ∈ B, d y = L := by
    rw [hL, hd]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun X hX => hind _ (hAB X hX)
  have hdsq : ∑ y ∈ B, d y ^ 2 = ∑ X ∈ S, ∑ Y ∈ S, (A X ∩ A Y).card := by
    have e1 : ∀ y, d y ^ 2 = ∑ X ∈ S, ∑ Y ∈ S,
        (if y ∈ A X ∩ A Y then 1 else 0) := by
      intro y
      rw [hd, sq]
      simp only [Finset.card_filter]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun Y _ => ?_
      by_cases h1 : y ∈ A X <;> by_cases h2 : y ∈ A Y <;> simp [h1, h2]
    simp_rw [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun X hX => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun Y hY =>
      hind _ ((Finset.inter_subset_left).trans (hAB X hX))
  have hdsq2 : ∑ X ∈ S, ∑ Y ∈ S, (A X ∩ A Y).card ≤ L + m * m * t := by
    have hrow : ∀ X ∈ S, ∑ Y ∈ S, (A X ∩ A Y).card ≤ (A X).card + m * t := by
      intro X hX
      calc ∑ Y ∈ S, (A X ∩ A Y).card
          ≤ ∑ Y ∈ S, ((if X = Y then (A X).card else 0) + t) := by
            refine Finset.sum_le_sum fun Y hY => ?_
            by_cases hXY : X = Y
            · subst hXY; simp
            · simpa [hXY] using ht1 X hX Y hY hXY
        _ = (A X).card + m * t := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
            simp [hX, hm]
    calc ∑ X ∈ S, ∑ Y ∈ S, (A X ∩ A Y).card
        ≤ ∑ X ∈ S, ((A X).card + m * t) := Finset.sum_le_sum hrow
      _ = L + m * m * t := by
          rw [Finset.sum_add_distrib, ← hL]
          simp [hm]; ring
  have hcs : L * L ≤ B.card * (L + m * m * t) := by
    have h := sq_sum_le_card_mul_sum_sq (s := B) (f := d)
    rw [hdsum, hdsq, sq] at h
    exact h.trans (Nat.mul_le_mul_left _ hdsq2)
  have hmL : m * a ≤ 2 * L := by
    calc m * a = ∑ X ∈ S, a := by simp [hm]
      _ ≤ ∑ X ∈ S, 2 * (A X).card := Finset.sum_le_sum fun X hX => (hAcard X hX).le
      _ = 2 * L := by rw [hL, Finset.mul_sum]
  rw [← ha, ← hm, hq2]
  by_contra hcon
  push Not at hcon
  set N := B.card with hN
  by_cases hLN : L < 2 * N
  · omega
  · push Not at hLN
    have h1 : 2 * N * L ≤ L * L := by nlinarith
    have h5 : L * L ≤ 2 * N * (m * m * t) := by nlinarith
    have h6 : (m * a) * (m * a) ≤ (2 * L) * (2 * L) := Nat.mul_le_mul hmL hmL
    have h7 : N * (m * m * t) ≤ q * (m * m * t) := Nat.mul_le_mul_right _ hBcard.le
    have h9 : (16 * q * t) * (m * m) < (a * a) * (m * m) :=
      Nat.mul_lt_mul_of_pos_right ht2 (Nat.mul_pos hmpos hmpos)
    nlinarith

/-- A family `S` of
`(α, β, γ)`-semi-bunches with pairwise intersections `|X ∩ Y| · 2 ^ (β + 4) < 2 ^ (2α)` satisfies
`|S| · 2 ^ (2α) ≤ 2 ^ (β + γ + 4)`.  Proof: fewer than `2 ^ γ` strings `x` have `K(x) < γ`, and
every set of `S` consists of such strings; double counting `Σₓ #{X ∈ S : x ∈ X} = |S| · 2 ^ α`
and the local bound `#{X ∈ S : x ∈ X} · 2 ^ α ≤ 2 ^ (β + 2)` give
`|S| · 2 ^ (2α) < 2 ^ γ · 2 ^ (β + 2)`. -/
private theorem lemma6_packing_bound (D : Map) (hD : isOptimalConditional D)
    (α β γ : ℕ) (S : Finset (Finset BitString))
    (hS : ∀ X ∈ S, IsSemiBunch D α β γ X)
    (hSep : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → (X ∩ Y).card * 2 ^ (β + 4) < 2 ^ (2 * α)) :
    S.card * 2 ^ (2 * α) ≤ 2 ^ (β + γ + 4) := by
  classical
  obtain ⟨W, hW⟩ : ∃ W : Finset BitString, W = S.biUnion id := ⟨_, rfl⟩
  have hmemW : ∀ y, y ∈ W ↔ ∃ X ∈ S, y ∈ X := by
    intro y; rw [hW]; simp
  have hWcard : W.card < 2 ^ γ :=
    lemma5_ball_card D hD [] γ W (fun y hy => by
      obtain ⟨X, hXS, hyX⟩ := (hmemW y).mp hy
      exact (hS X hXS).2.2 y hyX)
  have hdouble : ∑ x ∈ W, (S.filter fun X => x ∈ X).card = ∑ X ∈ S, X.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun X hXS => ?_
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(hmemW y).mpr ⟨X, hXS, h⟩, h⟩⟩
  have hsumcard : ∑ X ∈ S, X.card = S.card * 2 ^ α := by
    rw [Finset.sum_congr rfl fun X hXS => (hS X hXS).1]; simp
  have hloc : ∀ x ∈ W, (S.filter fun X => x ∈ X).card * 2 ^ α ≤ 2 ^ (β + 2) := by
    intro x _
    exact lemma6_local_packing D hD α β γ x (S.filter fun X => x ∈ X)
      (fun X hX => hS X (Finset.mem_filter.mp hX).1) (fun X hX => (Finset.mem_filter.mp hX).2)
      (fun X hX Y hY hXY => hSep X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hXY)
  have hmain : S.card * 2 ^ α * 2 ^ α ≤ W.card * 2 ^ (β + 2) := by
    calc S.card * 2 ^ α * 2 ^ α = (∑ x ∈ W, (S.filter fun X => x ∈ X).card) * 2 ^ α := by
          rw [hdouble, hsumcard]
      _ = ∑ x ∈ W, (S.filter fun X => x ∈ X).card * 2 ^ α := Finset.sum_mul _ _ _
      _ ≤ ∑ x ∈ W, 2 ^ (β + 2) := Finset.sum_le_sum hloc
      _ = W.card * 2 ^ (β + 2) := by simp
  calc S.card * 2 ^ (2 * α) = S.card * 2 ^ α * 2 ^ α := by rw [two_mul, pow_add, mul_assoc]
    _ ≤ W.card * 2 ^ (β + 2) := hmain
    _ ≤ 2 ^ γ * 2 ^ (β + 2) := Nat.mul_le_mul_right _ hWcard.le
    _ ≤ 2 ^ (β + γ + 4) := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)

/-- **Lemma 6.** The `(α, β, γ)`-semi-bunches have a standard cover: an algorithm lists
semi-bunches `U₀, …, U_q`, `q < 2 ^ (β + γ − 2α + O(1))`, such that every semi-bunch `U` has
`|U ∩ Uᵢ| ≥ 2 ^ (β − ε)` for some `i`, `ε = 2(β − α) + O(1)`.  Proof: Appendix (greedy
selection from an enumeration of all semi-bunches, with `ε = 2(β − α + 2)`). -/
theorem lemma6 (D : Map) (hD : isOptimalConditional D) : HasStandardCover (IsSemiBunch D) := by
  obtain ⟨E, hE, hSound, hComplete⟩ := lemma6_enumerate_semibunches D hD
  exact lemma5_greedy_enumeration (IsSemiBunch D) E hE hSound hComplete 4
    (fun α β γ X hX => lemma6_self_cover D hD α β γ X hX)
    (fun α β γ S hS hSep => lemma6_packing_bound D hD α β γ S hS hSep)

end Kolmogorov.Relativization
