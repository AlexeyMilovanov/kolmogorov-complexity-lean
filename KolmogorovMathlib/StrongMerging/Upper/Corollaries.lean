import KolmogorovMathlib.StrongMerging.Statements
import KolmogorovMathlib.StrongMerging.Upper.Profiles

/-!
# Merging strong sufficient statistics: corollaries of the proved upper bounds

Derivations of the remaining upper statements of `StrongMerging.StatementsExtra` from the proved
headline theorems `exists_sqrt_merger` (`thm:main`) and `setTotalC_le_of_strongRobustMin`
(node Q02) of `StrongMerging.Statements`, and the pointwise transfers behind the derivations of
`StatementsExtra` among the uniform selectors.

* **Q03.** `max_setTotalC_le_of_strongRobustMin'`: two-sided enlarged-window minimality, from
  Q02 applied to `(A, B)` and to the swapped instance `(B, A)` (`isMergingInstance_swap`).
* **Q04.** `headerLog_eventually_le_mul` (`⌈log₂ (m + 2)⌉ = o(m)`),
  `natCeil_eventually_le_mul` (`⌈ε_j⌉ = o(n_j)`), `enlargedWindow_sublinear'` (the window
  `e + c √(n H)` is `o(n)`), `exists_sublinear_merger_seq'` (from `thm:main`) and
  `setTotalC_sublinear_of_strongRobustMin'` (from Q02).  Their sublinearity hypotheses and
  conclusions are written in the unfolded form `∀ η > 0, ∀ᶠ j in atTop, f j ≤ η n_j` of
  `SublinearAbove`, which is defined downstream in `StatementsExtra`.
* **H08, T07.** `sqrtBounds_of_tradeoffBounds` (the rule bounds at the square-root rule
  `sqrtRule` give the square-root bounds), `mutualInfoBounds_of_extractabilityBounds`
  (`Φ ≤ M`), `exists_witnesses_of_isMergingInstance` (a merging instance is a qualifying
  selector instance at the integer budget `⌈ε⌉`) and `pointTotalC_le_length`.
-/

namespace Kolmogorov.StrongMerging.Upper

open Filter

/-! ### Q03: two-sided enlarged-window minimality -/

/-- **Merging instances are symmetric**: swapping the statistics `A` and `B` of a merging
instance gives a merging instance. -/
theorem isMergingInstance_swap {V : Map} {n : ℕ} {ε : ℝ} {x : BitString}
    {A B : Finset BitString} (h : IsMergingInstance V n ε x A B) :
    IsMergingInstance V n ε x B A := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact ⟨a1, a2, a3, a4, a7, a8, a5, a6⟩

/-- **Two-sided enlarged-window minimality** (blueprint target Q03, `UpperTwoSidedMinimality`;
the statement of `max_setTotalC_le_of_strongRobustMin`).  With the constants `c_win, c_out` of
the one-sided `setTotalC_le_of_strongRobustMin` (Q02): Q02 at `(A, B)` with gap `δ_A` bounds
`CT(A | B)`, Q02 at the swapped instance `(B, A)` with gap `δ_B` bounds `CT(B | A)`, and both
gaps are at most `max {δ_A, δ_B}`. -/
theorem max_setTotalC_le_of_strongRobustMin' (V : Map) (hV : isOptimalConditional V) :
    ∃ cwin cout : ℕ, 0 < cwin ∧ 0 < cout ∧
      ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString), IsMergingInstance V n e x A B →
        ∀ δA δB : ℝ, 0 ≤ δA → 0 ≤ δB →
          StrongRobustMin V x A (e + cwin * rootScale n e) δA →
          StrongRobustMin V x B (e + cwin * rootScale n e) δB →
            max (setTotalC A B) (setTotalC B A) ≤ max δA δB + cout * rootScale n e := by
  obtain ⟨cwin, cout, h1, h2, h⟩ := setTotalC_le_of_strongRobustMin V hV
  refine ⟨cwin, cout, h1, h2, fun n e x A B hI δA δB hA hB mA mB => ?_⟩
  have k1 := h n e x A B hI δA hA mA
  have k2 := h n e x B A (isMergingInstance_swap hI) δB hB mB
  exact max_le (by linarith [le_max_left δA δB]) (by linarith [le_max_right δA δB])

/-! ### Q04: the sublinear corollaries -/

/-- **`⌈log₂ (m + 2)⌉ = o(m)`**: for every `κ > 0`, eventually `headerLog m ≤ κ m`.
Proof: `log y ≤ (κ log 2 / 4) y` eventually (`Real.isLittleO_log_id_atTop`) at `y = m + 2`,
so `log₂ (m + 2) ≤ κ (m + 2) / 4`; `headerLog m < log₂ (m + 2) + 1` (`headerLog_eq_ceil_logb`);
and `1 ≤ κ m / 4`, `2 ≤ m` once `m ≥ ⌈4 / κ⌉ + 2`. -/
theorem headerLog_eventually_le_mul (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ m : ℕ in atTop, (headerLog m : ℝ) ≤ κ * m := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 := Real.isLittleO_log_id_atTop.bound (show 0 < κ * Real.log 2 / 4 by positivity)
  have htend : Tendsto (fun m : ℕ => ((m : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually h1, eventually_ge_atTop (⌈4 / κ⌉₊ + 2)] with m hm hm2
  have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hlogle : Real.log ((m : ℝ) + 2) ≤ κ * Real.log 2 / 4 * ((m : ℝ) + 2) := by
    simp only [Real.norm_eq_abs, id] at hm
    rw [abs_of_pos hpos] at hm
    exact (le_abs_self _).trans hm
  have hceil : (headerLog m : ℝ) < Real.logb 2 ((m : ℝ) + 2) + 1 := by
    have h2 := Int.ceil_lt_add_one (Real.logb 2 ((m : ℝ) + 2))
    rw [← headerLog_eq_ceil_logb m] at h2
    exact_mod_cast h2
  have hlogb : Real.logb 2 ((m : ℝ) + 2) ≤ κ / 4 * ((m : ℝ) + 2) := by
    rw [Real.logb, div_le_iff₀ hlog2]
    nlinarith
  have hm2' : (⌈4 / κ⌉₊ : ℝ) + 2 ≤ m := by exact_mod_cast hm2
  have hm4 : 4 / κ ≤ (m : ℝ) := by linarith [Nat.le_ceil (4 / κ)]
  have hk1 : 1 ≤ κ / 4 * m := by
    have := mul_le_mul_of_nonneg_left hm4 (by positivity : (0 : ℝ) ≤ κ / 4)
    rwa [show κ / 4 * (4 / κ) = 1 by field_simp] at this
  have hm2'' : (2 : ℝ) ≤ m := by
    linarith [(Nat.cast_nonneg ⌈4 / κ⌉₊ : (0 : ℝ) ≤ ⌈4 / κ⌉₊)]
  nlinarith

/-- **The enlarged window is sublinear** (blueprint target Q04; the unfolded form of
`enlargedWindow_sublinear`): for every real `c`, if `n_j → ∞` and `e_j = o(n_j)`, then
`e_j + c √(n_j H_j) = o(n_j)` from above, with `H_j = e_j + ⌈log₂ (n_j + 2)⌉`.
Proof: put `c' = max c 0` and `θ = η / (2 (c' + 1))`.  Eventually `e_j ≤ η n_j / 2`,
`e_j ≤ θ² n_j / 2` and `headerLog n_j ≤ θ² n_j / 2`, so `H_j ≤ θ² n_j`, `S_j ≤ θ n_j` and
`c S_j ≤ c' θ n_j ≤ η n_j / 2`. -/
theorem enlargedWindow_sublinear' (c : ℝ) (n e : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (he : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, (e j : ℝ) ≤ η * n j) :
    ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, (e j : ℝ) + c * rootScale (n j) (e j) ≤ η * n j := by
  intro η hη
  set c' := max c 0
  have hc' : 0 ≤ c' := le_max_right _ _
  set θ := η / (2 * (c' + 1)) with hθ
  have hθpos : 0 < θ := by positivity
  have hθsq : 0 < θ ^ 2 / 2 := by positivity
  filter_upwards [he (η / 2) (by linarith), he (θ ^ 2 / 2) hθsq,
    hn.eventually (headerLog_eventually_le_mul (θ ^ 2 / 2) hθsq)] with j h1 h2 h3
  have hn0 : (0 : ℝ) ≤ n j := Nat.cast_nonneg _
  have hH : ((baseBudget (n j) (e j) : ℕ) : ℝ) ≤ θ ^ 2 * n j := by
    unfold baseBudget; push_cast; linarith
  have hS : rootScale (n j) (e j) ≤ θ * n j := by
    unfold rootScale
    rw [Real.sqrt_le_left (by positivity)]
    have := mul_le_mul_of_nonneg_left hH hn0
    nlinarith
  have hS0 : 0 ≤ rootScale (n j) (e j) := Real.sqrt_nonneg _
  have hcS : c * rootScale (n j) (e j) ≤ c' * (θ * n j) :=
    (mul_le_mul_of_nonneg_right (le_max_left c 0) hS0).trans
      (mul_le_mul_of_nonneg_left hS hc')
  have hcθ : c' * θ ≤ η / 2 := by
    rw [hθ, show c' * (η / (2 * (c' + 1))) = η / 2 * (c' / (c' + 1)) by field_simp]
    have : c' / (c' + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  have : c' * (θ * n j) ≤ η / 2 * n j := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcθ hn0
  linarith

/-- **`⌈ε_j⌉ = o(n_j)` when `ε_j = o(n_j)`**, provided eventually `ε_j ≥ 0` and `n_j → ∞`.
Proof: eventually `⌈ε_j⌉ < ε_j + 1`, `ε_j ≤ η n_j / 2` and `n_j ≥ 2 / η`, so
`1 ≤ η n_j / 2` and `⌈ε_j⌉ ≤ η n_j`. -/
theorem natCeil_eventually_le_mul (ε : ℕ → ℝ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h0 : ∀ᶠ j in atTop, 0 ≤ ε j) (hε : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ε j ≤ η * n j) :
    ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ((⌈ε j⌉₊ : ℕ) : ℝ) ≤ η * n j := by
  intro η hη
  have hlarge : ∀ᶠ j in atTop, 2 / η ≤ (n j : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hn).eventually (eventually_ge_atTop (2 / η))
  filter_upwards [h0, hε (η / 2) (by linarith), hlarge] with j h0j hj hlj
  have hc := (Nat.ceil_lt_add_one h0j).le
  have : 1 ≤ η / 2 * n j := by
    have := mul_le_mul_of_nonneg_left hlj (by positivity : (0 : ℝ) ≤ η / 2)
    rwa [show η / 2 * (2 / η) = 1 by field_simp] at this
  linarith

/-- **Sublinear merging along a sequence** (blueprint target Q04, merger part; the unfolded form
of `exists_sublinear_merger_seq`).  With the constant `c` of `exists_sqrt_merger`, take `D_j` to
be its model wherever `(n_j, ε_j, x_j, A_j, B_j)` is a merging instance (and `{x_j}`
elsewhere).  Every error is then eventually at most `c √(n_j H_j)` with `e_j = ⌈ε_j⌉`, which is
`o(n_j)` by `natCeil_eventually_le_mul` and `enlargedWindow_sublinear'`. -/
theorem exists_sublinear_merger_seq' (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n : ℕ → ℕ) (ε : ℕ → ℝ) (x : ℕ → BitString) (A B : ℕ → Finset BitString),
      Tendsto n atTop atTop →
      (∀ᶠ j in atTop, IsMergingInstance V (n j) (ε j) (x j) (A j) (B j)) →
      (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ε j ≤ η * n j) →
        ∃ D : ℕ → Finset BitString,
          (∀ᶠ j in atTop, x j ∈ D j ∧ pointTotalC (D j) (x j) ≤ c * (⌈ε j⌉₊ + 1)) ∧
          (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, modelScore V (D j) (x j) ≤ η * n j) ∧
          (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, setTotalC (D j) (A j) ≤ η * n j) ∧
          (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, setTotalC (D j) (B j) ≤ η * n j) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
            overlapMass (A j) (B j) - Real.logb 2 (D j).card ≤ η * n j := by
  classical
  obtain ⟨c, h⟩ := exists_sqrt_merger V hV
  refine ⟨c, fun n ε x A B hn hI hε => ?_⟩
  let D : ℕ → Finset BitString := fun j =>
    if hj : IsMergingInstance V (n j) (ε j) (x j) (A j) (B j) then
      Classical.choose (h _ _ _ _ _ hj) else {x j}
  have hD : ∀ j, IsMergingInstance V (n j) (ε j) (x j) (A j) (B j) →
      x j ∈ D j ∧ pointTotalC (D j) (x j) ≤ c * (⌈ε j⌉₊ + 1) ∧
        setC V (D j) + Real.logb 2 (D j).card ≤ plainC V (x j) + c * rootScale (n j) ⌈ε j⌉₊ ∧
        setTotalC (D j) (A j) ≤ c * rootScale (n j) ⌈ε j⌉₊ ∧
        setTotalC (D j) (B j) ≤ c * rootScale (n j) ⌈ε j⌉₊ ∧
        Real.logb 2 (A j).card + Real.logb 2 (B j).card - Real.logb 2 (A j ∩ B j).card -
          c * rootScale (n j) ⌈ε j⌉₊ ≤ Real.logb 2 (D j).card := by
    intro j hj
    simpa only [D, hj, ↓reduceDIte] using Classical.choose_spec (h _ _ _ _ _ hj)
  have h0 : ∀ᶠ j in atTop, 0 ≤ ε j := hI.mono fun j hj => hj.2.1
  have hW := enlargedWindow_sublinear' (c : ℝ) n (fun j => ⌈ε j⌉₊) hn
    (natCeil_eventually_le_mul ε n hn h0 hε)
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, (c : ℝ) * rootScale (n j) ⌈ε j⌉₊ ≤ η * n j := by
    intro η hη
    filter_upwards [hW η hη] with j hj
    have : (0 : ℝ) ≤ (⌈ε j⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  refine ⟨D, hI.mono fun j hj => ⟨(hD j hj).1, (hD j hj).2.1⟩, ?_, ?_, ?_, ?_⟩
  · intro η hη
    filter_upwards [hI, key η hη] with j hj hk
    have := (hD j hj).2.2.1
    unfold modelScore
    linarith
  · intro η hη
    filter_upwards [hI, key η hη] with j hj hk
    exact (hD j hj).2.2.2.1.trans hk
  · intro η hη
    filter_upwards [hI, key η hη] with j hj hk
    exact (hD j hj).2.2.2.2.1.trans hk
  · intro η hη
    filter_upwards [hI, key η hη] with j hj hk
    have := (hD j hj).2.2.2.2.2
    unfold overlapMass
    linarith

/-- **Sublinear enlarged-window minimality, one- and two-sided** (blueprint target Q04,
minimality part; the unfolded form of `setTotalC_sublinear_of_strongRobustMin`).  With the
constants `c_win, c_out` of `setTotalC_le_of_strongRobustMin` (Q02): eventually
`CT(A_j | B_j) ≤ δ_j + c_out S_j ≤ η n_j / 2 + η n_j / 2`, by `δ_j = o(n_j)` and
`enlargedWindow_sublinear'` at `c_out` (with `e_j ≥ 0`); the two-sided form applies Q02 also
to the swapped instances (`isMergingInstance_swap`). -/
theorem setTotalC_sublinear_of_strongRobustMin' (V : Map) (hV : isOptimalConditional V) :
    ∃ cwin : ℕ, 0 < cwin ∧
      (∀ (n e : ℕ → ℕ) (x : ℕ → BitString) (A B : ℕ → Finset BitString) (δ : ℕ → ℝ),
        Tendsto n atTop atTop →
        (∀ᶠ j in atTop, IsMergingInstance V (n j) (e j) (x j) (A j) (B j)) →
        (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, (e j : ℝ) ≤ η * n j) →
        (∀ᶠ j in atTop, 0 ≤ δ j) → (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, δ j ≤ η * n j) →
        (∀ᶠ j in atTop,
          StrongRobustMin V (x j) (A j) (e j + cwin * rootScale (n j) (e j)) (δ j)) →
          ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, setTotalC (A j) (B j) ≤ η * n j) ∧
      ∀ (n e : ℕ → ℕ) (x : ℕ → BitString) (A B : ℕ → Finset BitString) (δA δB : ℕ → ℝ),
        Tendsto n atTop atTop →
        (∀ᶠ j in atTop, IsMergingInstance V (n j) (e j) (x j) (A j) (B j)) →
        (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, (e j : ℝ) ≤ η * n j) →
        (∀ᶠ j in atTop, 0 ≤ δA j ∧ 0 ≤ δB j) →
        (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, δA j ≤ η * n j) →
        (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, δB j ≤ η * n j) →
        (∀ᶠ j in atTop,
          StrongRobustMin V (x j) (A j) (e j + cwin * rootScale (n j) (e j)) (δA j) ∧
          StrongRobustMin V (x j) (B j) (e j + cwin * rootScale (n j) (e j)) (δB j)) →
          ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
            max (setTotalC (A j) (B j)) (setTotalC (B j) (A j)) ≤ η * n j := by
  obtain ⟨cwin, cout, h1, -, h⟩ := setTotalC_le_of_strongRobustMin V hV
  refine ⟨cwin, h1, ?_, ?_⟩
  · intro n e x A B δ hn hI he hδ0 hδ hmin η hη
    filter_upwards [hI, hδ0, hmin, hδ (η / 2) (by linarith),
      enlargedWindow_sublinear' (cout : ℝ) n e hn he (η / 2) (by linarith)] with
      j hIj hδj hmj hδj' hSj
    have k := h (n j) (e j) (x j) (A j) (B j) hIj (δ j) hδj hmj
    have he0 : (0 : ℝ) ≤ e j := Nat.cast_nonneg _
    linarith
  · intro n e x A B δA δB hn hI he hδ0 hδA hδB hmin η hη
    filter_upwards [hI, hδ0, hmin, hδA (η / 2) (by linarith), hδB (η / 2) (by linarith),
      enlargedWindow_sublinear' (cout : ℝ) n e hn he (η / 2) (by linarith)] with
      j hIj hδj hmj hAj hBj hSj
    have k1 := h (n j) (e j) (x j) (A j) (B j) hIj (δA j) hδj.1 hmj.1
    have k2 := h (n j) (e j) (x j) (B j) (A j) (isMergingInstance_swap hIj) (δB j) hδj.2 hmj.2
    have he0 : (0 : ℝ) ≤ e j := Nat.cast_nonneg _
    exact max_le (by linarith) (by linarith)

/-! ### H08 and T07: pointwise transfers for the uniform selectors -/

/-- **The square-root bounds from the rule bounds** (blueprint target H08, "in particular … the
square-root bounds for the displayed rule"): for `n ≥ 2` and `e ≤ n`, the tradeoff bounds with
constant `c` at the clipped square-root exponent `R = min n (max 1 (sqrtRule n e))` give the
square-root bounds of `thm:main`, with `S = √(n H)`, for every constant `C ≥ 4 c`.
Proof: `sqrtRule_bounds` gives `R + H ≤ 4 S` and `H + n H / R ≤ 4 S`; multiply by `c ≥ 0`. -/
theorem sqrtBounds_of_tradeoffBounds {V : Map} {n e c C : ℕ} {x : BitString}
    {A B D : Finset BitString} (hn : 2 ≤ n) (he : e ≤ n) (hC : 4 * c ≤ C)
    (h : TradeoffBounds V n e (min n (max 1 (sqrtRule n e))) c x A B D) :
    setC V D + Real.logb 2 D.card ≤ plainC V x + C * rootScale n e ∧
      setTotalC D A ≤ C * rootScale n e ∧ setTotalC D B ≤ C * rootScale n e ∧
      Real.logb 2 A.card + Real.logb 2 B.card - Real.logb 2 (A ∩ B).card -
        C * rootScale n e ≤ Real.logb 2 D.card := by
  obtain ⟨t1, t2, t3, t4⟩ := h
  obtain ⟨hb1, hb2⟩ := sqrtRule_bounds hn he
  have hS : (0 : ℝ) ≤ rootScale n e := Real.sqrt_nonneg _
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have m1 := mul_le_mul_of_nonneg_left hb1 hc0
  have m2 := mul_le_mul_of_nonneg_left hb2 hc0
  have hCS : (4 : ℝ) * c * rootScale n e ≤ C * rootScale n e :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hC) hS
  unfold modelScore at t1
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- **From the extractability envelope to the mutual-information envelope** (blueprint target
T07, the choice `r = 0` in `thm:extractability-envelope`): the score, endpoint and mass bounds by
`c Φ` give the same bounds by `c M`, since `Φ ≤ M`
(`extractabilityEnvelope_le_mutualInfoEnvelope`) and `c ≥ 0`. -/
theorem mutualInfoBounds_of_extractabilityBounds {V : Map} {n e c : ℕ} {x : BitString}
    {A B D : Finset BitString}
    (h : modelScore V D x ≤ c * extractabilityEnvelope V n e A B ∧
      setTotalC D A ≤ c * extractabilityEnvelope V n e A B ∧
      setTotalC D B ≤ c * extractabilityEnvelope V n e A B ∧
      overlapMass A B - Real.logb 2 D.card ≤ c * extractabilityEnvelope V n e A B) :
    modelScore V D x ≤ c * mutualInfoEnvelope V n e A B ∧
      setTotalC D A ≤ c * mutualInfoEnvelope V n e A B ∧
      setTotalC D B ≤ c * mutualInfoEnvelope V n e A B ∧
      overlapMass A B - Real.logb 2 D.card ≤ c * mutualInfoEnvelope V n e A B := by
  obtain ⟨b1, b2, b3, b4⟩ := h
  have m := mul_le_mul_of_nonneg_left (extractabilityEnvelope_le_mutualInfoEnvelope V n e A B)
    (Nat.cast_nonneg (α := ℝ) c)
  exact ⟨b1.trans m, b2.trans m, b3.trans m, b4.trans m⟩

/-- **The point strength of a program's output is at most the program's length**: if the total
program `q` outputs on `z` the canonical code of `F`, then `CT(F | z) ≤ |q|`
(`totalCondK_le_programLength`). -/
theorem pointTotalC_le_length {q z : BitString} {F : Finset BitString}
    (hT : IsTotalProgram universalDecompressor q)
    (hP : produces universalDecompressor q z (canonicalFiniteSetCode F)) :
    pointTotalC F z ≤ q.length := by
  unfold pointTotalC totalC
  have h := totalCondK_le_programLength hT hP
  exact_mod_cast ENat.toNat_le_of_le_natCast h

/-- **A merging instance is a qualifying selector instance at `⌈ε⌉`** (blueprint target T07,
instance form): for a merging instance `(n, ε, x, A, B)` there are total programs `p_A, p_B` of
length at most `⌈ε⌉` that output on `x` the canonical codes of `A` and `B`
(`Lower.exists_totalProgram_of_isStrongModel` and `⌊ε⌋ ≤ ⌈ε⌉`); moreover `⌈ε⌉ ≤ n`, and `A, B`
are `⌈ε⌉`-sufficient since `ε ≤ ⌈ε⌉`.  The conclusion is the unfolded form of
`IsBoundedTotalWitness ⌈ε⌉ p_A`, `IsBoundedTotalWitness ⌈ε⌉ p_B` and
`IsWitnessedInstance V n ⌈ε⌉ p_A p_B x A B` of `StatementsExtra`. -/
theorem exists_witnesses_of_isMergingInstance {V : Map} {n : ℕ} {ε : ℝ} {x : BitString}
    {A B : Finset BitString} (h : IsMergingInstance V n ε x A B) :
    ∃ pA pB : BitString,
      (IsTotalProgram universalDecompressor pA ∧ pA.length ≤ ⌈ε⌉₊) ∧
      (IsTotalProgram universalDecompressor pB ∧ pB.length ≤ ⌈ε⌉₊) ∧
      2 ≤ n ∧ ⌈ε⌉₊ ≤ n ∧ x.length = n ∧
      produces universalDecompressor pA x (canonicalFiniteSetCode A) ∧
      produces universalDecompressor pB x (canonicalFiniteSetCode B) ∧
      IsSufficientModel V x A ⌈ε⌉₊ ∧ IsSufficientModel V x B ⌈ε⌉₊ := by
  obtain ⟨hn, -, hεn, hlen, hsA, hfA, hsB, hfB⟩ := h
  obtain ⟨pA, htA, hlA, hoA⟩ := Lower.exists_totalProgram_of_isStrongModel hsA
  obtain ⟨pB, htB, hlB, hoB⟩ := Lower.exists_totalProgram_of_isStrongModel hsB
  have hfc : ⌊ε⌋₊ ≤ ⌈ε⌉₊ := Nat.floor_le_ceil ε
  have hεe : ε ≤ (⌈ε⌉₊ : ℝ) := Nat.le_ceil ε
  exact ⟨pA, pB, ⟨htA, hlA.trans hfc⟩, ⟨htB, hlB.trans hfc⟩, hn, Nat.ceil_le.mpr hεn, hlen,
    hoA, hoB, ⟨hfA.1, by linarith [hfA.2]⟩, ⟨hfB.1, by linarith [hfB.2]⟩⟩

end Kolmogorov.StrongMerging.Upper
