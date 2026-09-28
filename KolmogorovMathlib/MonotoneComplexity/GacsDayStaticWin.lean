import KolmogorovMathlib.MonotoneComplexity.GacsDayWaste

/-!
# A static winning client strategy for `d = 1`

This file proves the `d = 1` instance of the Gacs-Day game (Gate 1 of the
Gacs-Day programme) unconditionally.

For budget parameter `d = 1` the client does not need to react to the server at
all: it plays the *constant* move which asks for `1` at the root and for `3 / 10`
at each of the first three children of the root.  A request of `3 / 10` exceeds
`2 ^ (-2)`, so any allocation serving it must contain a cylinder of measure at
least `2 ^ (-1) = 1/2`.  Three children of the root have pairwise disjoint
allocations, so serving all three costs measure at least `3/2 > 1`, which is
impossible.  Hence one of the three children is never served and the client
wins.

The strategy is a constant function, hence trivially computable, and it is
`RangeSupported` for every branching factor `b ≥ 3`.

For `d ≥ 2` a static strategy cannot win (the rounding loss of a single level is
only a factor `2`), so the general statement genuinely needs an adaptive client;
this file settles the base case.
-/

namespace Kolmogorov

open MeasureTheory ENNReal BigOperators

/-- The constant client move used for `d = 1`: ask `1` at the root and `3 / 10` at
each of the three children `[0]`, `[1]`, `[2]`. -/
def staticWinMove : ClientMove := [([], 1), ([0], 3 / 10), ([1], 3 / 10), ([2], 3 / 10)]

/-- The constant client strategy for `d = 1`. -/
def staticWinStrategy : ClientStrategy := fun _ => staticWinMove

/-- The static winning move requests `1` at the root. -/
@[simp] lemma getReq_staticWinMove_nil : getReq staticWinMove [] = 1 := rfl

/-- The static winning move requests `3 / 10` at the child `0`. -/
@[simp] lemma getReq_staticWinMove_zero : getReq staticWinMove [0] = 3 / 10 := rfl

/-- The static winning move requests `3 / 10` at the child `1`. -/
@[simp] lemma getReq_staticWinMove_one : getReq staticWinMove [1] = 3 / 10 := rfl

/-- The static winning move requests `3 / 10` at the child `2`. -/
@[simp] lemma getReq_staticWinMove_two : getReq staticWinMove [2] = 3 / 10 := rfl

/-- Outside the four listed nodes the constant move requests nothing. -/
lemma getReq_staticWinMove_eq_zero {x : GacsDayNode}
    (h0 : x ≠ []) (h1 : x ≠ [0]) (h2 : x ≠ [1]) (h3 : x ≠ [2]) :
    getReq staticWinMove x = 0 := by
  have e0 : (x == ([] : GacsDayNode)) = false := by simpa using h0
  have e1 : (x == ([0] : GacsDayNode)) = false := by simpa using h1
  have e2 : (x == ([1] : GacsDayNode)) = false := by simpa using h2
  have e3 : (x == ([2] : GacsDayNode)) = false := by simpa using h3
  simp [getReq, staticWinMove, List.lookup, e0, e1, e2, e3]

/-- Every request of the constant move is nonnegative. -/
lemma getReq_staticWinMove_nonneg (x : GacsDayNode) : 0 ≤ getReq staticWinMove x := by
  by_cases h0 : x = []
  · subst h0; norm_num
  by_cases h1 : x = [0]
  · subst h1; norm_num
  by_cases h2 : x = [1]
  · subst h2; norm_num
  by_cases h3 : x = [2]
  · subst h3; norm_num
  rw [getReq_staticWinMove_eq_zero h0 h1 h2 h3]

/-- The requests of the children of a node of positive length all vanish. -/
lemma getReq_staticWinMove_child_of_ne_nil {x : GacsDayNode} (hx : x ≠ []) (c : ℕ) :
    getReq staticWinMove (x ++ [c]) = 0 := by
  have hlen : 2 ≤ (x ++ [c]).length := by
    have : 1 ≤ x.length := List.length_pos_iff.mpr hx
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  refine getReq_staticWinMove_eq_zero ?_ ?_ ?_ ?_ <;>
    · intro h; rw [h] at hlen; simp at hlen

/-- The children of the root receive `3 / 10` for indices `0, 1, 2` and `0` otherwise. -/
lemma getReq_staticWinMove_root_child (c : ℕ) :
    getReq staticWinMove ([] ++ [c]) = if c < 3 then 3 / 10 else 0 := by
  simp only [List.nil_append]
  match c with
  | 0 => norm_num
  | 1 => norm_num
  | 2 => norm_num
  | (n + 3) =>
    have h : ¬ (n + 3 < 3) := by omega
    rw [if_neg h]
    refine getReq_staticWinMove_eq_zero ?_ ?_ ?_ ?_ <;> simp

/-- The total request of the root's children is at most `9 / 10`. -/
lemma sum_getReq_staticWinMove_root (b : ℕ) :
    ∑ c : Fin b, getReq staticWinMove ([] ++ [c.val]) ≤ 9 / 10 := by
  classical
  have hterm : ∀ c : Fin b,
      getReq staticWinMove ([] ++ [c.val]) = if c.val < 3 then (3 / 10 : ℚ) else 0 := by
    intro c; exact getReq_staticWinMove_root_child c.val
  calc ∑ c : Fin b, getReq staticWinMove ([] ++ [c.val])
      = ∑ c : Fin b, (if c.val < 3 then (3 / 10 : ℚ) else 0) := Finset.sum_congr rfl (by
        intro c _; exact hterm c)
    _ = ∑ c ∈ Finset.univ.filter (fun c : Fin b => c.val < 3), (3 / 10 : ℚ) := by
        rw [Finset.sum_filter]
    _ = (Finset.univ.filter (fun c : Fin b => c.val < 3)).card * (3 / 10 : ℚ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * (3 / 10 : ℚ) := by
        have hcard : (Finset.univ.filter (fun c : Fin b => c.val < 3)).card ≤ 3 := by
          have hsub : (Finset.univ.filter (fun c : Fin b => c.val < 3)).card
              ≤ (Finset.range 3).card := by
            refine Finset.card_le_card_of_injOn (fun c => c.val) ?_ ?_
            · intro c hc
              have hc' : c ∈ Finset.univ.filter (fun c : Fin b => c.val < 3) := hc
              exact Finset.mem_range.mpr (Finset.mem_filter.mp hc').2
            · intro c _ c' _ h
              exact Fin.ext h
          simpa using hsub
        have : ((Finset.univ.filter (fun c : Fin b => c.val < 3)).card : ℚ) ≤ 3 := by
          exact_mod_cast hcard
        nlinarith [this]
    _ = 9 / 10 := by norm_num

/-- The constant move is a legal (coherent) request for budget `d = 1`. -/
lemma requestCoherent_staticWinMove (b : ℕ) : requestCoherent b 1 staticWinMove := by
  refine ⟨getReq_staticWinMove_nonneg, by norm_num, ?_⟩
  intro x
  by_cases hx : x = []
  · subst hx
    have := sum_getReq_staticWinMove_root b
    rw [getReq_staticWinMove_nil]
    linarith
  · have hzero : ∀ c : Fin b, getReq staticWinMove (x ++ [c.val]) = 0 := by
      intro c; exact getReq_staticWinMove_child_of_ne_nil hx c.val
    have : ∑ c : Fin b, getReq staticWinMove (x ++ [c.val]) = 0 := by
      rw [Finset.sum_eq_zero]
      intro c _; exact hzero c
    rw [this]
    exact getReq_staticWinMove_nonneg x

/-- The constant strategy plays the constant move at every stage. -/
lemma playClient_staticWinStrategy (sms : ℕ → ServerMove) (t : ℕ) :
    playClient staticWinStrategy sms t = staticWinMove := by
  cases t <;> simp [playClient, staticWinStrategy]

/-- The constant strategy never requests outside the first three branches, hence it is
`RangeSupported` for every branching factor `b ≥ 3`. -/
lemma rangeSupported_staticWinStrategy {b : ℕ} (hb : 3 ≤ b) :
    RangeSupported b staticWinStrategy := by
  intro hist x i hi
  change getReq staticWinMove (x ++ [i]) = 0
  by_cases hx : x = []
  · subst hx
    rw [getReq_staticWinMove_root_child i, if_neg (by omega)]
  · exact getReq_staticWinMove_child_of_ne_nil hx i

/-- Serving three sibling requests of `3 / 10` at the root is impossible: it would need
measure `3/2` inside a probability space. -/
lemma not_all_three_served {b : ℕ} (hb : 3 ≤ b) {sm : ServerMove}
    (h_coh : serverMoveCoherent b sm)
    (h0 : Serves (getAlloc sm [0]) (3 / 10))
    (h1 : Serves (getAlloc sm [1]) (3 / 10))
    (h2 : Serves (getAlloc sm [2]) (3 / 10)) : False := by
  classical
  have hb0 : (0 : ℕ) < b := by omega
  have hb1 : (1 : ℕ) < b := by omega
  have hb2 : (2 : ℕ) < b := by omega
  have hcard : ({⟨0, hb0⟩, ⟨1, hb1⟩, ⟨2, hb2⟩} : Finset (Fin b)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]
  have hmass := sum_children_mass_ge_of_serves h_coh [] 1
    ({⟨0, hb0⟩, ⟨1, hb1⟩, ⟨2, hb2⟩} : Finset (Fin b)) (fun _ => (3 / 10 : ℚ))
    (by
      intro c _
      norm_num)
    (by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · simpa using h0
      · simpa using h1
      · simpa using h2)
  rw [hcard] at hmass
  have hle : allocationMass (getAlloc sm []) ≤ 1 := allocationMass_le_one _
  have h32 : ((3 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞) ^ (-((1 : ℕ) : ℤ)) ≤ 1 := le_trans hmass hle
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hpow : (2 : ℝ≥0∞) ^ (-((1 : ℕ) : ℤ)) = (2 : ℝ≥0∞)⁻¹ := by
    rw [Nat.cast_one]
    exact zpow_neg_one 2
  rw [hpow, Nat.cast_ofNat] at h32
  have h3 : (3 : ℝ≥0∞) ≤ 2 := by
    calc (3 : ℝ≥0∞) = 3 * 2⁻¹ * 2 := by
          rw [mul_assoc, ENNReal.inv_mul_cancel h2ne h2top, mul_one]
      _ ≤ 1 * 2 := mul_le_mul_left h32 2
      _ = 2 := one_mul 2
  exact absurd h3 (by norm_num)

/-- **Gate 1 for `d = 1`.** The constant strategy `staticWinStrategy` is a uniform winning
client strategy for budget `d = 1` on every tree of height at least `1` and branching
factor at least `3`. -/
theorem isUniformWinningStrategy_staticWinStrategy {h b : ℕ} (hh : 1 ≤ h) (hb : 3 ≤ b) :
    IsUniformWinningStrategy h b 1 staticWinStrategy := by
  refine ⟨?_, rangeSupported_staticWinStrategy hb⟩
  intro sms hsms
  constructor
  · refine ⟨fun t => ?_, fun t x => ?_⟩
    · rw [playClient_staticWinStrategy]
      exact requestCoherent_staticWinMove b
    · rw [playClient_staticWinStrategy, playClient_staticWinStrategy]
  · -- some child of the root is never served
    by_contra hcon
    simp only [clientWinsUnserved, not_exists, not_and, not_forall, not_not] at hcon
    have key : ∀ i : ℕ, i < 3 → ∃ t, Serves (getAlloc (sms t) [i]) (3 / 10) := by
      intro i hi
      have hlen : ([i] : GacsDayNode).length ≤ h := by simpa using hh
      have hin : ∀ a ∈ ([i] : GacsDayNode), a < b := by
        intro a ha
        simp only [List.mem_singleton] at ha
        omega
      have := hcon 0 [i] hlen hin
      rcases this with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have hreq : getReq (playClient staticWinStrategy sms 0) [i] = 3 / 10 := by
        rw [playClient_staticWinStrategy]
        interval_cases i
        · exact getReq_staticWinMove_zero
        · exact getReq_staticWinMove_one
        · exact getReq_staticWinMove_two
      rwa [hreq] at ht
    obtain ⟨t0, ht0⟩ := key 0 (by norm_num)
    obtain ⟨t1, ht1⟩ := key 1 (by norm_num)
    obtain ⟨t2, ht2⟩ := key 2 (by norm_num)
    set T := max t0 (max t1 t2) with hT
    have hs0 : Serves (getAlloc (sms T) [0]) (3 / 10) :=
      serves_mono_time hsms (le_max_left _ _) ht0
    have hs1 : Serves (getAlloc (sms T) [1]) (3 / 10) :=
      serves_mono_time hsms (le_trans (le_max_left _ _) (le_max_right t0 _)) ht1
    have hs2 : Serves (getAlloc (sms T) [2]) (3 / 10) :=
      serves_mono_time hsms (le_trans (le_max_right _ _) (le_max_right t0 _)) ht2
    exact not_all_three_served hb (hsms.1 T) hs0 hs1 hs2

/-- The constant strategy, viewed as a uniform family indexed by `d`, is computable. -/
lemma computable₂_staticWinFamily :
    Computable₂ (fun (_ : ℕ) (_ : GameHistory) => staticWinMove) :=
  Computable.const _

/-- **Gate 1, restricted to `d = 1`, in the shape of `GacsDayGameStatement`.**
There is a constant `C` and a computable family of client strategies which wins the
Gacs-Day game with budget `d = 1` on the tree of height `C * 1` and branching factor
`2 ^ ((C * 1) ^ (C * 1))`. -/
theorem gacsDayGameStatement_at_one :
    ∃ C : ℕ, ∃ σ : ℕ → ClientStrategy, Computable₂ σ ∧
      IsUniformWinningStrategy (C * 1) (2 ^ ((C * 1) ^ (C * 1))) 1 (σ 1) := by
  refine ⟨2, fun _ => staticWinStrategy, computable₂_staticWinFamily, ?_⟩
  have h1 : (1 : ℕ) ≤ 2 * 1 := by norm_num
  have h2 : (3 : ℕ) ≤ 2 ^ ((2 * 1) ^ (2 * 1)) := by norm_num
  exact isUniformWinningStrategy_staticWinStrategy h1 h2

/-- The static winning strategy requests only at the root and its children, hence is supported to
any height at least `1`. -/
theorem treeSupported_staticWinStrategy {h b : ℕ} (h_pos : 1
  ≤ h) : TreeSupported h b staticWinStrategy := by
  intro hist x hx
  have hlen : 1 < x.length := lt_of_le_of_lt h_pos hx
  unfold staticWinStrategy staticWinMove getReq
  dsimp [List.lookup]
  have h_not_nil : x ≠ [] := by intro eq; rw [eq] at hlen; contradiction
  have h_not_0 : x ≠ [0] := by intro eq; rw [eq] at hlen; contradiction
  have h_not_1 : x ≠ [1] := by intro eq; rw [eq] at hlen; contradiction
  have h_not_2 : x ≠ [2] := by intro eq; rw [eq] at hlen; contradiction
  have heq1 : (x == []) = false := beq_false_of_ne h_not_nil
  have heq2 : (x == [0]) = false := beq_false_of_ne h_not_0
  have heq3 : (x == [1]) = false := beq_false_of_ne h_not_1
  have heq4 : (x == [2]) = false := beq_false_of_ne h_not_2
  rw [heq1, heq2, heq3, heq4]

end Kolmogorov
