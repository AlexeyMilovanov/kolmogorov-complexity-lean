import KolmogorovMathlib.StrongMerging.Lower.MovingSphere
import KolmogorovMathlib.StrongMerging.Lower.Calibration

/-!
# The sharp lower bound: the dense-sphere generic edge and its complexity

Blueprint nodes L26 (`denseSphereGenericEdge`) and L27 (`internalEdgeComplexity`) of the
formalization of `sublinear-merging.tex` (paper: "Calibrating an internal edge and its ambient
stars", lines ~1613-1640; blueprint: "Uniform parameter calibration and the incompressible
edge", lines ~4848-4884).

* `SharpReservoir`: the conclusions of the moving-sphere reservoir (L23) at the sharp parameters
  (L05) `R, K, S = 3T, τ = 6T, ℓ = M/8`.
* **L26.**  Some ordered edge `(u, v)` of the distance-`2r` graph inside the dense reservoir `W`
  has `C(v | u), C(u | v) ≥ d - j₀` for any fixed integer `j₀ ≥ 5` (`SharpEdge`): an existential
  counting argument (`exists_generic_edge`), not an effective search.  Removing at most `N/8`
  vertices of the `D_i`-regular distance-`2r` graph on `S_z` keeps `3 N D_i / 4` ordered edges
  (`card_edges_subset_ge`), while fewer than `2 N 2^(d - j₀) ≤ N D_i / 16` ordered pairs have a
  conditional complexity below the integer threshold `d - j₀` (`card_filter_condC_lt_le`).
* **L27.**  For that edge, with the literal concatenation `x = u v` of length `2M`:
  `K + d - j₀ - c m ≤ C(x) ≤ K + d + c m` and `K ≤ C(u), C(v) ≤ K + c m` (`EdgeCalibration`).
  The lower bound is the chain rule through the equal-half bridge to `pairCode`
  (`edge_pair_lower`); the upper bound describes the center, the index of `u` in the full sphere
  and the index of `v` among its internal neighbours (`edge_pair_upper`).  The final reservoir
  `W` is never described.

Constants: `c` and the cutoff `M₀` are fixed with the machine `V`, before `M, E` and `j₀`.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### The sharp reservoir -/

/-- **The reservoir at the sharp parameters**: `ReservoirOutcome` (node L23) at `R`, `K`,
`S = 3T`, `τ = 6T`, `ℓ = M/8` of `sharpParameters M E`, with coding constant `c`. -/
def SharpReservoir (V : Map) (M E c : ℕ) (z : BitString) (W : Finset BitString) : Prop :=
  ReservoirOutcome V M (sharpSphereRadius M E) (sharpThreshold M E) (3 * mergerBudget M E)
    (6 * mergerBudget M E) (M / 8) c z W

/-- **The sharp parameters are polynomially bounded** (header exponent `B = 1`): on the valid
domain, each of `M, R, K, S = 3T, τ = 6T, ℓ = M/8, δ = ⌊r/10⁴⌋, h = M/1024` is at most `M + 2`.

`sharpParameters_valid` gives `2R < M` and `2⁵⁰ r ≤ M`, so `T ≤ r ≤ M` and `δ ≤ r`;
`K ≤ M` is `sharp_threshold_le`.
Reference: paper lines 1522-1528 (encoded fields polynomially bounded); blueprint L22-L23. -/
theorem sharp_params_le_poly {M E : ℕ} (hv : SharpValid M E) :
    ∀ q ∈ [M, sharpSphereRadius M E, sharpThreshold M E, 3 * mergerBudget M E,
      6 * mergerBudget M E, M / 8, sharpRootRadius M E / 10000, M / 1024], q ≤ (M + 2) ^ 1 := by
  obtain ⟨-, hrM, -, -, -, -, -, h2R, -⟩ := sharpParameters_valid hv
  have hr : sharpRootRadius M E ≤ M := le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) hrM
  clear hrM
  have hK := sharp_threshold_le M E
  have hT : mergerBudget M E = sharpRootRadius M E / 1000000 := by
    rw [mergerBudget_eq_sharpRootRadius_div]
    norm_num
  intro q hq
  rw [pow_one]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h <;> subst h <;> omega

/-- **Instantiating the generic reservoir at the sharp parameters**: the generic theorem (L23,
header exponent `1`) and the four sharp game inequalities (L25) give a sharp reservoir. -/
theorem exists_sharpReservoir {V : Map} {c : ℕ}
    (hc : ∀ M R K S τ ℓ δ h : ℕ, 0 < R → 2 * R < M → 1 ≤ h →
      (∀ q ∈ [M, R, K, S, τ, ℓ, δ, h], q ≤ (M + 2) ^ 1) →
      ReservoirInequalities M R K S τ ℓ δ h →
      ∃ (z : BitString) (W : Finset BitString), ReservoirOutcome V M R K S τ ℓ c z W)
    {M E : ℕ} (hv : SharpValid M E)
    (hineq : ReservoirInequalities M (sharpSphereRadius M E) (sharpThreshold M E)
      (3 * mergerBudget M E) (6 * mergerBudget M E) (M / 8) (sharpRootRadius M E / 10000)
      (M / 1024)) :
    ∃ (z : BitString) (W : Finset BitString), SharpReservoir V M E c z W := by
  obtain ⟨-, -, -, -, -, -, hR0, h2R, -, -, -, -, -, -, -, hh0⟩ := sharpParameters_valid hv
  exact hc _ _ _ _ _ _ _ _ hR0 h2R hh0 (sharp_params_le_poly hv) hineq

/-! ### L26: the generic edge -/

/-- **A generic internal edge** (the conclusion of node L26): `z, W` form a sharp reservoir, the
endpoints `u, v` lie in `W` at Hamming distance `2r`, and both conditional complexities are at
least `d - j₀` (real subtraction; `d = ⌊log₂ D_i⌋`). -/
structure SharpEdge (V : Map) (M E j₀ c : ℕ) (z u v : BitString) (W : Finset BitString) :
    Prop where
  /-- `z, W` is the sharp reservoir. -/
  reservoir : SharpReservoir V M E c z W
  /-- The left endpoint lies in the reservoir. -/
  left_mem : u ∈ W
  /-- The right endpoint lies in the reservoir. -/
  right_mem : v ∈ W
  /-- The endpoints are at Hamming distance `2r`. -/
  dist_eq : hammingDist u v = 2 * sharpRootRadius M E
  /-- `C(v | u) ≥ d - j₀`. -/
  cond_right : (sharpLogInternalDegree M E : ℝ) - j₀ ≤ condC V v u
  /-- `C(u | v) ≥ d - j₀`. -/
  cond_left : (sharpLogInternalDegree M E : ℝ) - j₀ ≤ condC V u v

/-- A generic edge stays generic for a larger coding constant. -/
theorem SharpEdge.mono {V : Map} {M E j₀ c c' : ℕ} {z u v : BitString} {W : Finset BitString}
    (h : SharpEdge V M E j₀ c z u v W) (hc : c ≤ c') : SharpEdge V M E j₀ c' z u v W :=
  ⟨ReservoirOutcome.mono h.reservoir hc, h.left_mem, h.right_mem, h.dist_eq, h.cond_right,
    h.cond_left⟩

/-- **Dense subsets keep most ordered edges.**  Let `rel` be a symmetric relation which is
`D`-regular on a finite set `S` (every `u ∈ S` has exactly `D` related points in `S`), and let
`W ⊆ S`.  Then the ordered related pairs inside `W` number at least
`|S| D - 2 (|S| - |W|) D`.

The ordered related pairs of `S × S` number `|S| D`; a pair outside `W × W` has its first point
in `S \ W` (at most `|S \ W| D` pairs) or its second point in `S \ W` (at most `|S \ W| D` pairs,
by symmetry).
Reference: paper lines 1615-1618 ("removing at most `N/8` vertices removes at most `N D_i / 4`
ordered edges"); blueprint L26. -/
theorem card_edges_subset_ge {α : Type*} (S W : Finset α) (rel : α → α → Prop)
    [DecidableRel rel] (D : ℕ) (hreg : ∀ u ∈ S, (S.filter (rel u)).card = D)
    (hsymm : ∀ u v, rel u v → rel v u) (hWS : W ⊆ S) :
    S.card * D ≤ ((W ×ˢ W).filter fun p => rel p.1 p.2).card + 2 * ((S.card - W.card) * D) := by
  classical
  have hrow : ∀ T : Finset α, T ⊆ S →
      ((T ×ˢ S).filter fun p => rel p.1 p.2).card = T.card * D := by
    intro T hT
    rw [Finset.card_filter, Finset.sum_product]
    calc ∑ x ∈ T, ∑ y ∈ S, (if rel (x, y).1 (x, y).2 then 1 else 0)
        = ∑ _x ∈ T, D := Finset.sum_congr rfl fun u hu => by
          rw [← hreg u (hT hu), Finset.card_filter]
      _ = T.card * D := by rw [Finset.sum_const, smul_eq_mul]
  have hcol : ∀ T : Finset α, T ⊆ S →
      ((S ×ˢ T).filter fun p => rel p.1 p.2).card = T.card * D := by
    intro T hT
    rw [Finset.card_filter, Finset.sum_product_right]
    calc ∑ y ∈ T, ∑ x ∈ S, (if rel (x, y).1 (x, y).2 then 1 else 0)
        = ∑ _y ∈ T, D := Finset.sum_congr rfl fun v hv => by
          rw [← hreg v (hT hv), Finset.card_filter]
          refine Finset.sum_congr rfl fun u _ => ?_
          by_cases h : rel u v
          · simp [h, hsymm u v h]
          · simp [h, show ¬ rel v u from fun h' => h (hsymm v u h')]
      _ = T.card * D := by rw [Finset.sum_const, smul_eq_mul]
  have hall := hrow S (subset_refl S)
  have hA := hrow (S \ W) Finset.sdiff_subset
  have hB := hcol (S \ W) Finset.sdiff_subset
  have hsub : ((S ×ˢ S).filter fun p => rel p.1 p.2) ⊆
      ((W ×ˢ W).filter fun p => rel p.1 p.2) ∪
        (((S \ W) ×ˢ S).filter fun p => rel p.1 p.2) ∪
        ((S ×ˢ (S \ W)).filter fun p => rel p.1 p.2) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hr⟩ := hp
    by_cases hw1 : p.1 ∈ W
    · by_cases hw2 : p.2 ∈ W
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hw1, hw2⟩, hr⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨h1, Finset.mem_sdiff.2 ⟨h2, hw2⟩⟩, hr⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨Finset.mem_sdiff.2 ⟨h1, hw1⟩, h2⟩, hr⟩))
  have hcard := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  rw [hall, hA, hB, Finset.card_sdiff_of_subset hWS] at hcard
  generalize S.card * D = X at hcard ⊢
  generalize (S.card - W.card) * D = Y at hcard ⊢
  omega

/-- **Few ordered pairs with a short conditional description, first direction**: at most
`|W| 2^k` ordered pairs `(u, v) ∈ W²` have `C(v | u) < k`.

Counted fiberwise over `u`: each fiber is a set of strings `v` with `C(v | u) < k`, which has
fewer than `2^k` elements (`card_lt_two_pow_of_condC_lt`, node L02).
Reference: paper lines 1619-1621 ("fewer than `2^(d-j₀)` strings `v` have
`C(v | u) < d - j₀`"); blueprint L26. -/
theorem card_filter_condC_lt_le (V : Map) (hV : isOptimalConditional V) (W : Finset BitString)
    (k : ℕ) : ((W ×ˢ W).filter fun p => condC V p.2 p.1 < k).card ≤ W.card * 2 ^ k := by
  rw [Finset.card_filter, Finset.sum_product]
  calc ∑ u ∈ W, ∑ v ∈ W, (if condC V (u, v).2 (u, v).1 < k then 1 else 0)
      ≤ ∑ _u ∈ W, 2 ^ k := Finset.sum_le_sum fun u _ => by
        rw [← Finset.card_filter]
        exact (card_lt_two_pow_of_condC_lt V hV u k _ fun v hv =>
          (Finset.mem_filter.1 hv).2).le
    _ = W.card * 2 ^ k := by rw [Finset.sum_const, smul_eq_mul]

/-- **Few ordered pairs with a short conditional description, second direction**: at most
`|W| 2^k` ordered pairs `(u, v) ∈ W²` have `C(u | v) < k`.

Counted fiberwise over the second coordinate `v`, as `card_filter_condC_lt_le`.
Reference: paper lines 1619-1622 ("the two directions"); blueprint L26. -/
theorem card_filter_condC_lt_le' (V : Map) (hV : isOptimalConditional V) (W : Finset BitString)
    (k : ℕ) : ((W ×ˢ W).filter fun p => condC V p.1 p.2 < k).card ≤ W.card * 2 ^ k := by
  rw [Finset.card_filter, Finset.sum_product_right]
  calc ∑ v ∈ W, ∑ u ∈ W, (if condC V (u, v).1 (u, v).2 < k then 1 else 0)
      ≤ ∑ _v ∈ W, 2 ^ k := Finset.sum_le_sum fun v _ => by
        rw [← Finset.card_filter]
        exact (card_lt_two_pow_of_condC_lt V hV v k _ fun u hu =>
          (Finset.mem_filter.1 hu).2).le
    _ = W.card * 2 ^ k := by rw [Finset.sum_const, smul_eq_mul]

/-- **A generic edge in a dense subset of a sphere** (the counting core of node L26).  Let `W` be
a subset of the sphere `S_z` of radius `R` around an `M`-word `z` with `8 |W| ≥ 7 N`, and let
`D_i = (R choose r)((M - R) choose r)` with `N D_i > 0` and `d = ⌊log₂ D_i⌋`.  For every
`j₀ ≥ 5` some ordered pair `(u, v) ∈ W²` at distance `2r` has `C(v | u), C(u | v) ≥ d - j₀`. -/
theorem exists_generic_edge (V : Map) (hV : isOptimalConditional V) {M R r : ℕ} {z : BitString}
    (hz : z.length = M) {W : Finset BitString} (hW : W ⊆ hammingSphere M z R)
    (hdense : 7 * M.choose R ≤ 8 * W.card)
    (hpos : 0 < M.choose R * (R.choose r * (M - R).choose r)) {j₀ : ℕ} (hj : 5 ≤ j₀) :
    ∃ u ∈ W, ∃ v ∈ W, hammingDist u v = 2 * r ∧
      (Nat.log 2 (R.choose r * (M - R).choose r) : ℝ) - j₀ ≤ condC V v u ∧
      (Nat.log 2 (R.choose r * (M - R).choose r) : ℝ) - j₀ ≤ condC V u v := by
  classical
  set Di := R.choose r * (M - R).choose r with hDi
  set N := M.choose R with hN
  have hS : (hammingSphere M z R).card = N := hammingSphere_card M z R hz
  have hedges : (hammingSphere M z R).card * Di ≤
      ((W ×ˢ W).filter fun p => hammingDist p.1 p.2 = 2 * r).card +
        2 * (((hammingSphere M z R).card - W.card) * Di) :=
    card_edges_subset_ge (hammingSphere M z R) W (fun u v => hammingDist u v = 2 * r) Di
      (fun u hu => sphere_distance_regular M R r z u hz hu)
      (fun u v h => by rw [hammingDist_comm]; exact h) hW
  rw [hS] at hedges
  set Ed := (W ×ˢ W).filter fun p => hammingDist p.1 p.2 = 2 * r with hEd
  have hWN : W.card ≤ N := by
    rw [← hS]
    exact card_le_card hW
  have h8 : 8 * (N - W.card) ≤ N := by omega
  have h8' : 8 * ((N - W.card) * Di) ≤ N * Di := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right Di h8
  have hEdge : 3 * (N * Di) ≤ 4 * Ed.card := by
    generalize (N - W.card) * Di = X at hedges h8'
    generalize N * Di = Y at hedges h8' ⊢
    omega
  by_cases hdj : j₀ ≤ Nat.log 2 Di
  · set k := Nat.log 2 Di - j₀ with hk
    have hpow : 32 * 2 ^ k ≤ Di := by
      have h1 : 2 ^ k * 2 ^ j₀ = 2 ^ Nat.log 2 Di := by
        rw [← pow_add]
        congr 1
        omega
      have h2 : 2 ^ 5 ≤ 2 ^ j₀ := Nat.pow_le_pow_right (by norm_num) hj
      have hDi0 : Di ≠ 0 := by
        rintro h
        rw [h, mul_zero] at hpos
        exact lt_irrefl _ hpos
      have h3 : 2 ^ Nat.log 2 Di ≤ Di := Nat.pow_log_le_self 2 hDi0
      calc 32 * 2 ^ k = 2 ^ k * 2 ^ 5 := by ring
        _ ≤ 2 ^ k * 2 ^ j₀ := Nat.mul_le_mul_left _ h2
        _ = 2 ^ Nat.log 2 Di := h1
        _ ≤ Di := h3
    set B1 := (W ×ˢ W).filter fun p => condC V p.2 p.1 < k with hB1
    set B2 := (W ×ˢ W).filter fun p => condC V p.1 p.2 < k with hB2
    have hc1 : B1.card ≤ W.card * 2 ^ k := card_filter_condC_lt_le V hV W k
    have hc2 : B2.card ≤ W.card * 2 ^ k := card_filter_condC_lt_le' V hV W k
    have hun : (B1 ∪ B2).card ≤ B1.card + B2.card := card_union_le B1 B2
    have hWP : W.card * 2 ^ k ≤ N * 2 ^ k := Nat.mul_le_mul_right _ hWN
    have hNP : 32 * (N * 2 ^ k) ≤ N * Di := by
      calc 32 * (N * 2 ^ k) = N * (32 * 2 ^ k) := by ring
        _ ≤ N * Di := Nat.mul_le_mul_left _ hpow
    have hlt : (B1 ∪ B2).card < Ed.card := by
      generalize N * 2 ^ k = Q at hWP hNP
      generalize N * Di = Y at hNP hEdge hpos
      generalize W.card * 2 ^ k = P at hc1 hc2 hWP
      omega
    obtain ⟨⟨u, v⟩, hpE, hpB⟩ := exists_mem_notMem_of_card_lt_card hlt
    rw [hEd, mem_filter, mem_product] at hpE
    obtain ⟨⟨hu, hv⟩, hdist⟩ := hpE
    have hkR : (Nat.log 2 Di : ℝ) - j₀ = (k : ℝ) := by
      rw [hk, Nat.cast_sub hdj]
    have h1 : (k : ℝ) ≤ condC V v u := by
      by_contra hlt'
      exact hpB (mem_union_left _ (mem_filter.2 ⟨mem_product.2 ⟨hu, hv⟩, not_le.mp hlt'⟩))
    have h2 : (k : ℝ) ≤ condC V u v := by
      by_contra hlt'
      exact hpB (mem_union_right _ (mem_filter.2 ⟨mem_product.2 ⟨hu, hv⟩, not_le.mp hlt'⟩))
    exact ⟨u, hu, v, hv, hdist, by rw [hkR]; exact h1, by rw [hkR]; exact h2⟩
  · have hEpos : 0 < Ed.card := by
      generalize N * Di = Y at hEdge hpos
      omega
    obtain ⟨⟨u, v⟩, hp⟩ := card_pos.mp hEpos
    rw [hEd, mem_filter, mem_product] at hp
    obtain ⟨⟨hu, hv⟩, hdist⟩ := hp
    have hneg : (Nat.log 2 Di : ℝ) - j₀ ≤ 0 := by
      have : (Nat.log 2 Di : ℝ) < j₀ := by exact_mod_cast not_le.mp hdj
      linarith
    exact ⟨u, hu, v, hv, hdist, hneg.trans (condC_nonneg V v u),
      hneg.trans (condC_nonneg V u v)⟩

/-- **Dense-sphere generic edge** (blueprint node L26).  For an optimal plain machine `V` there
are a coding constant `c` and a cutoff `M₀` such that for every valid `M ≥ M₀, E` and every
integer `j₀ ≥ 5` there are a sharp reservoir `z, W` and an ordered edge `(u, v) ∈ W²` at
distance `2r` with `C(v | u), C(u | v) ≥ d - j₀`. -/
theorem denseSphereGenericEdge (V : Map) (hV : isOptimalConditional V) :
    ∃ c M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ E : ℕ, SharpValid M E → ∀ j₀ : ℕ, 5 ≤ j₀ →
      ∃ (z u v : BitString) (W : Finset BitString), SharpEdge V M E j₀ c z u v W := by
  obtain ⟨c, hc⟩ := movingSphereReservoir V hV 1
  obtain ⟨M₀, hM₀⟩ := sharpGameHypotheses
  refine ⟨c, M₀, fun M hM E hv j₀ hj => ?_⟩
  obtain ⟨z, W, hres⟩ := exists_sharpReservoir hc hv (hM₀ M hM E hv)
  obtain ⟨-, -, -, -, -, -, -, -, -, hN0, -, hDi0, -⟩ := sharpParameters_valid hv
  obtain ⟨u, hu, v, hv', hdist, h1, h2⟩ := exists_generic_edge V hV (r := sharpRootRadius M E)
    (ReservoirOutcome.center_length hres) (ReservoirOutcome.subset_sphere hres)
    (ReservoirOutcome.dense hres) (Nat.mul_pos hN0 hDi0) hj
  exact ⟨z, u, v, W, ⟨hres, hu, hv', hdist, h1, h2⟩⟩

/-! ### L27: the complexity of the generic edge -/

/-- **The complexity calibration of an internal edge** (the conclusion of node L27), with
`m = ⌈log₂ (M + 2)⌉`, `K` and `d` of `sharpParameters M E`, for the literal concatenation
`u ++ v`: `K + d - j₀ - c m ≤ C(u v) ≤ K + d + c m` and `K ≤ C(u), C(v) ≤ K + c m`. -/
structure EdgeCalibration (V : Map) (M E j₀ c : ℕ) (u v : BitString) : Prop where
  /-- `C(u v) ≥ K + d - j₀ - c m`. -/
  pair_lower : (sharpThreshold M E : ℝ) + sharpLogInternalDegree M E - j₀ - c * headerLog M ≤
    plainC V (u ++ v)
  /-- `C(u v) ≤ K + d + c m`. -/
  pair_upper : plainC V (u ++ v) ≤
    (sharpThreshold M E : ℝ) + sharpLogInternalDegree M E + c * headerLog M
  /-- `C(u) ≥ K`. -/
  left_lower : (sharpThreshold M E : ℝ) ≤ plainC V u
  /-- `C(u) ≤ K + c m`. -/
  left_upper : plainC V u ≤ sharpThreshold M E + c * headerLog M
  /-- `C(v) ≥ K`. -/
  right_lower : (sharpThreshold M E : ℝ) ≤ plainC V v
  /-- `C(v) ≤ K + c m`. -/
  right_upper : plainC V v ≤ sharpThreshold M E + c * headerLog M

/-- **Chain lower bound for a concatenation of equal halves**:
`C(u v) ≥ C(u) + C(v | u) - c ⌈log₂ (M + 2)⌉` for `M`-words `u, v`.  The equal-half bridge
`pairC_le_plainC_append` (B6) moves to `pairCode`; the lower chain rule `pairC_ge_of_le` (L02)
costs `c log₂ (C(u, v) + 2)`, and `C(u, v) ≤ 2M + O(1)`. -/
theorem edge_pair_lower (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (M : ℕ) (u v : BitString), u.length = M → v.length = M →
      plainC V u + condC V v u - c * headerLog M ≤ plainC V (u ++ v) := by
  obtain ⟨ca, hca⟩ := pairC_le_plainC_append V hV
  obtain ⟨cb, hcb⟩ := pairC_ge_of_le V hV
  obtain ⟨blit, hlit⟩ := plainC_le_length_add V hV
  obtain ⟨ch, hch⟩ := logb_linear_le_headerLog 2 (blit + ca)
  refine ⟨ca + cb * ch, fun M u v hu hv => ?_⟩
  have hN : pairC V u v ≤ plainC V (u ++ v) + ca := hca u v (hu.trans hv.symm)
  have h2 := hcb (plainC V (u ++ v) + ca) u v hN
  have hlen : ((u ++ v).length : ℝ) = 2 * M := by
    rw [List.length_append, hu, hv]
    push_cast
    ring
  have hpos : 0 < plainC V (u ++ v) + ca + 2 := by
    linarith [plainC_nonneg V (u ++ v), Nat.cast_nonneg (α := ℝ) ca]
  have h3 : plainC V (u ++ v) + ca + 2 ≤ ((2 : ℕ) : ℝ) * M + ((blit + ca : ℕ) : ℝ) + 2 := by
    have := hlit (u ++ v)
    rw [hlen] at this
    push_cast
    linarith
  have hlog : Real.logb 2 (plainC V (u ++ v) + ca + 2) ≤ ch * headerLog M :=
    (Real.logb_le_logb_of_le one_lt_two hpos h3).trans (hch M)
  have hm : (1 : ℝ) ≤ headerLog M := by exact_mod_cast one_le_headerLog M
  have hcb2 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) cb)
  have hca1 : (ca : ℝ) ≤ ca * headerLog M := by
    nlinarith [Nat.cast_nonneg (α := ℝ) ca]
  push_cast
  linarith

/-- The ordered internal edges at distance `2r` of the sphere `S_z` of radius `R`, as
concatenations `u ++ v` with `u, v ∈ S_z`, listed in the canonical order of `sphereList`. -/
def internalEdgeList (R r : ℕ) (z : BitString) : List BitString :=
  (sphereList R z).flatMap fun u =>
    ((sphereList R z).filter fun v => hammingDist u v = 2 * r).map (u ++ ·)

/-- **Internal edges are listed**: if `u, v ∈ S_z` and `dist(u, v) = 2r` then
`u ++ v ∈ internalEdgeList R r z`.

Reference: paper lines 1627-1630; blueprint L27. -/
theorem mem_internalEdgeList {M R r : ℕ} {z u v : BitString} (hz : z.length = M)
    (hu : u ∈ hammingSphere M z R) (hv : v ∈ hammingSphere M z R)
    (hd : hammingDist u v = 2 * r) : u ++ v ∈ internalEdgeList R r z := by
  have hu' : u ∈ sphereList R z := (mem_sphereList_iff R z u).2 (by rw [hz]; exact hu)
  have hv' : v ∈ sphereList R z := (mem_sphereList_iff R z v).2 (by rw [hz]; exact hv)
  rw [internalEdgeList, List.mem_flatMap]
  exact ⟨u, hu', List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hv', decide_eq_true hd⟩, rfl⟩⟩

/-- **Number of listed internal edges**: `|internalEdgeList R r z| ≤ N D_i` with
`N = (M choose R)` and `D_i = (R choose r)((M - R) choose r)`.

Each of the `N` points `u` of the sphere list contributes its `D_i` internal neighbours
(`sphere_distance_regular`; the sphere list has no repetitions).
Reference: paper lines 1613-1616 ("regular of degree `D_i`"); blueprint L27. -/
theorem length_internalEdgeList_le {M R r : ℕ} {z : BitString} (hz : z.length = M) :
    (internalEdgeList R r z).length ≤ M.choose R * (R.choose r * (M - R).choose r) := by
  have hnd : (sphereList R z).Nodup := (allStrings_nodup _).filter _
  have hinner : ∀ u ∈ sphereList R z,
      (((sphereList R z).filter fun v => hammingDist u v = 2 * r).map (u ++ ·)).length =
        R.choose r * (M - R).choose r := by
    intro u hu
    have hu' : u ∈ hammingSphere M z R := by
      rw [← hz]
      exact (mem_sphereList_iff R z u).1 hu
    rw [List.length_map, ← List.toFinset_card_of_nodup (hnd.filter _),
      ← sphere_distance_regular M R r z u hz hu']
    congr 1
    ext v
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, mem_sphereList_iff, hz,
      decide_eq_true_eq]
  rw [internalEdgeList, List.length_flatMap]
  refine (List.sum_le_length_nsmul _ (R.choose r * (M - R).choose r) ?_).trans ?_
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    exact (hinner u hu).le
  · rw [List.length_map, length_sphereList, hz, smul_eq_mul]

/-- **The internal-edge family is computable**:
`(ps, y) ↦ internalEdgeList (ps.getD 0 0) (ps.getD 1 0) y`.

It is primitive recursive: `Primrec.list_flatMap` over primitive recursive sphere lists, with the
inner `List.map (u ++ ·)` by `Primrec.list_map` and `Primrec.list_append`.
Reference: blueprint L27 ("uniform headers"). -/
theorem edgeFamily_computable :
    Computable₂ fun (ps : List ℕ) (y : BitString) =>
      internalEdgeList (ps.getD 0 0) (ps.getD 1 0) y := by
  have hsph : Primrec fun q : ℕ × BitString => sphereList q.1 q.2 := by
    have hp : Primrec₂ fun (q : ℕ × BitString) (u : BitString) =>
        decide (hammingDist q.2 u = q.1) :=
      Primrec.eq.decide.comp (hammingDist_primrec.comp (Primrec.snd.comp Primrec.fst)
        Primrec.snd) (Primrec.fst.comp Primrec.fst)
    exact (list_filter_primrec
      (CodedFiniteDistribution.allStrings_primrec.comp (Primrec.list_length.comp Primrec.snd))
      hp).of_eq fun q => rfl
  have hinner : Primrec₂ fun (x : (ℕ × ℕ) × BitString) (u : BitString) =>
      ((sphereList x.1.1 x.2).filter fun v => decide (hammingDist u v = 2 * x.1.2)).map
        (u ++ ·) := by
    have hp : Primrec₂ fun (w : ((ℕ × ℕ) × BitString) × BitString) (v : BitString) =>
        decide (hammingDist w.2 v = 2 * w.1.1.2) :=
      Primrec.eq.decide.comp (hammingDist_primrec.comp (Primrec.snd.comp Primrec.fst)
        Primrec.snd) (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    have hfil : Primrec fun w : ((ℕ × ℕ) × BitString) × BitString =>
        (sphereList w.1.1.1 w.1.2).filter fun v => decide (hammingDist w.2 v = 2 * w.1.1.2) :=
      list_filter_primrec (hsph.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst))) hp
    exact Primrec.list_map hfil (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
      Primrec.snd)
  have hedge : Primrec fun x : (ℕ × ℕ) × BitString => internalEdgeList x.1.1 x.1.2 x.2 :=
    (Primrec.list_flatMap (hsph.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
      hinner).of_eq fun x => rfl
  have hps : Primrec fun p : List ℕ × BitString => ((p.1.getD 0 0, p.1.getD 1 0), p.2) :=
    (((Primrec.list_getD 0).comp Primrec.fst (Primrec.const 0)).pair
      ((Primrec.list_getD 0).comp Primrec.fst (Primrec.const 1))).pair Primrec.snd
  exact (hedge.comp hps).to_comp

/-- **Edge upper code**: for `u, v` in the sphere `S_z` of radius `R ≤ M` around an `M`-word `z`
with `dist(u, v) = 2r`, `r ≤ M`: `C(u v) ≤ C(z) + log₂ N + log₂ D_i + c ⌈log₂ (M + 2)⌉`
(describe the center, the index of `u` in the full sphere and the index of `v` among its `D_i`
internal neighbours, with the numeric fields `R, r`; paper lines 1627-1630). -/
theorem edge_pair_upper (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (M R r : ℕ) (z u v : BitString), z.length = M → R ≤ M → r ≤ M →
      u ∈ hammingSphere M z R → v ∈ hammingSphere M z R → hammingDist u v = 2 * r →
        plainC V (u ++ v) ≤ plainC V z + Real.logb 2 (M.choose R) +
          Real.logb 2 (R.choose r * (M - R).choose r) + c * headerLog M := by
  obtain ⟨c, hc⟩ := plainC_le_of_mem_family V hV
    (fun ps y => internalEdgeList (ps.getD 0 0) (ps.getD 1 0) y) edgeFamily_computable 1 2 2
  refine ⟨c, fun M R r z u v hz hR hr hu hv hd => ?_⟩
  have hmem := mem_internalEdgeList hz hu hv hd
  have hulen : u.length = M := ((mem_hammingSphere_iff_diffSet hz).1 hu).1
  have hvlen : v.length = M := ((mem_hammingSphere_iff_diffSet hz).1 hv).1
  have hlen : (u ++ v).length ≤ 2 * M := by
    rw [List.length_append, hulen, hvlen]
    omega
  have h : plainC V (u ++ v) ≤ plainC V z + Real.logb 2 (internalEdgeList R r z).length +
      c * headerLog M :=
    hc M [R, r] z (u ++ v) (by simp)
      (by
        intro q hq
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl <;> simp only [pow_one] <;> omega)
      hz.le hlen hmem
  have hL := length_internalEdgeList_le (R := R) (r := r) hz
  have hpos : 0 < (internalEdgeList R r z).length := List.length_pos_of_mem hmem
  have hN : 0 < M.choose R := Nat.choose_pos hR
  have hDi : 0 < R.choose r * (M - R).choose r := by
    rcases Nat.eq_zero_or_pos (R.choose r * (M - R).choose r) with h0 | h0
    · rw [h0, mul_zero] at hL
      omega
    · exact h0
  have hlog : Real.logb 2 (internalEdgeList R r z).length ≤
      Real.logb 2 (M.choose R) + Real.logb 2 (R.choose r * (M - R).choose r) := by
    have hNr : (0 : ℝ) < M.choose R := by exact_mod_cast hN
    have hDr : (0 : ℝ) < (R.choose r : ℝ) * ((M - R).choose r : ℝ) := by exact_mod_cast hDi
    rw [← Real.logb_mul hNr.ne' hDr.ne']
    apply Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hpos)
    exact_mod_cast hL
  linarith

/-- **Internal edge complexity** (blueprint node L27).  For an optimal plain machine `V` there are
a coding constant `c` and a cutoff `M₀` such that for every valid `M ≥ M₀, E` and every integer
`j₀ ≥ 5` there are a sharp reservoir `z, W` and a generic internal edge `(u, v)` (node L26)
whose concatenation `x = u v` has `C(x) = K + d + O(m)` (`EdgeCalibration`, the lower bound with
the explicit `- j₀`) and whose endpoints have `K ≤ C(u), C(v) ≤ K + c m`. -/
theorem internalEdgeComplexity (V : Map) (hV : isOptimalConditional V) :
    ∃ c M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ E : ℕ, SharpValid M E → ∀ j₀ : ℕ, 5 ≤ j₀ →
      ∃ (z u v : BitString) (W : Finset BitString),
        SharpEdge V M E j₀ c z u v W ∧ EdgeCalibration V M E j₀ c u v := by
  obtain ⟨c₁, M₀, h26⟩ := denseSphereGenericEdge V hV
  obtain ⟨c₂, hlow⟩ := edge_pair_lower V hV
  obtain ⟨c₃, hup⟩ := edge_pair_upper V hV
  refine ⟨c₁ + c₂ + c₃ + 1, M₀, fun M hM E hv j₀ hj => ?_⟩
  obtain ⟨z, u, v, W, he⟩ := h26 M hM E hv j₀ hj
  have hres : ReservoirOutcome V M (sharpSphereRadius M E) (sharpThreshold M E)
      (3 * mergerBudget M E) (6 * mergerBudget M E) (M / 8) c₁ z W := he.reservoir
  have hz := hres.center_length
  have huS := hres.subset_sphere he.left_mem
  have hvS := hres.subset_sphere he.right_mem
  have hulen : u.length = M := ((mem_hammingSphere_iff_diffSet hz).1 huS).1
  have hvlen : v.length = M := ((mem_hammingSphere_iff_diffSet hz).1 hvS).1
  obtain ⟨-, hrM, -, -, -, -, -, h2R, -, -, -, hDi0, -⟩ := sharpParameters_valid hv
  have hrM' : sharpRootRadius M E ≤ M :=
    le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) hrM
  have hm : (1 : ℝ) ≤ headerLog M := by exact_mod_cast one_le_headerLog M
  have hc1 : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg c₁
  have hc2 : (0 : ℝ) ≤ c₂ := Nat.cast_nonneg c₂
  have hc3 : (0 : ℝ) ≤ c₃ := Nat.cast_nonneg c₃
  have hm0 : (0 : ℝ) ≤ headerLog M := by linarith
  have hlow' := hlow M u v hulen hvlen
  have hup' := hup M (sharpSphereRadius M E) (sharpRootRadius M E) z u v hz (by omega)
    hrM' huS hvS he.dist_eq
  have hcz := hres.center_code
  have hdi : Real.logb 2 (sharpInternalDegree M E : ℝ) <
      (sharpLogInternalDegree M E : ℝ) + 1 := logb_lt_natLog_add_one hDi0.ne'
  have hdi' : Real.logb 2 ((sharpSphereRadius M E).choose (sharpRootRadius M E) *
      (M - sharpSphereRadius M E).choose (sharpRootRadius M E) : ℝ) <
      (sharpLogInternalDegree M E : ℝ) + 1 := by
    have e : ((sharpSphereRadius M E).choose (sharpRootRadius M E) *
        (M - sharpSphereRadius M E).choose (sharpRootRadius M E) : ℝ) =
        (sharpInternalDegree M E : ℝ) := by
      simp only [sharpInternalDegree, Nat.cast_mul]
    rw [e]
    exact hdi
  have hul := hres.endpoint_lower u he.left_mem
  have hvl := hres.endpoint_lower v he.right_mem
  have huu := hres.endpoint_upper u he.left_mem
  have hvu := hres.endpoint_upper v he.right_mem
  have hcr := he.cond_right
  have k1 : (c₁ : ℝ) * headerLog M ≤ ((c₁ + c₂ + c₃ + 1 : ℕ) : ℝ) * headerLog M := by
    apply mul_le_mul_of_nonneg_right _ hm0
    push_cast
    linarith
  have k2 : (c₂ : ℝ) * headerLog M ≤ ((c₁ + c₂ + c₃ + 1 : ℕ) : ℝ) * headerLog M := by
    apply mul_le_mul_of_nonneg_right _ hm0
    push_cast
    linarith
  have k3 : (c₁ : ℝ) * headerLog M + c₃ * headerLog M + 1 ≤
      ((c₁ + c₂ + c₃ + 1 : ℕ) : ℝ) * headerLog M := by
    push_cast
    nlinarith
  refine ⟨z, u, v, W, he.mono (by omega), ⟨?_, ?_, hul, ?_, hvl, ?_⟩⟩
  · linarith
  · linarith
  · linarith
  · linarith

end Kolmogorov.StrongMerging.Lower
