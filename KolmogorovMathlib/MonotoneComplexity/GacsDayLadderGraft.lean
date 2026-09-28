import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderRelocation
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderStep

/-!
# Grafting the recursive calls back into the family game

`GacsDayLadderRelocation` provides the *downward* half of the relocation of
SUV pp. 142-143: a legal family server play on `n` trees restricts to a legal
family server play on a list of grandson slots
(`serverPlayLegal_extractGrandchild`), and a family client move restricts to
the slots (`restrictGrandchildClientMove`).

This file adds the *upward* half, which the bounded loop needs in order to turn
the moves produced by a recursive call into its own move: the two-level graft.
The client of the half-step requests `alpha` at every root, `son i c` at the
son `c` of the root of tree `i`, and, below a grandson that is used as a slot
of the recursive call, exactly what the recursive call requests.

The results are:

* `requestCoherentCap_graftClientMove` -- the cap form of the one-level graft
  (the family game caps the root request by `alpha` rather than by `1 / d`);
* `requestCoherentCap_graftTwoLevel` -- the two-level form, which is what the
  half-step plays;
* `graftGrandchildFamilyMove` and `familyClientMoveAt_graftGrandchildFamilyMove`
  -- the family version, together with
* `restrictGrandchild_graftGrandchild` -- the round trip: restricting the
  grafted family move back to the slots returns the moves of the recursive
  call, so the recursive invariant applies verbatim to the composite play.
-/

namespace Kolmogorov

variable {n b : ℕ}

/-! ### One-level graft, with a direct cap on the root -/

/-- **The cap form of `requestCoherent_graftClientMove`.** The family game caps
the root request directly by `alpha`, so this is the shape the half-step uses. -/
theorem requestCoherentCap_graftClientMove {b : ℕ} {alpha root : ℚ} {f : ℕ → ClientMove}
    (hroot0 : 0 ≤ root) (hcap : root ≤ alpha)
    (hsum : ∑ c : Fin b, getReq (f c.val) [] ≤ root)
    (hpos : ∀ i < b, ∀ x, 0 ≤ getReq (f i) x)
    (hchild : ∀ i < b, ∀ x, getReq (f i) x ≥ ∑ c : Fin b, getReq (f i) (x ++ [c.val])) :
    requestCoherentCap b alpha (graftClientMove root b f) := by
  refine ⟨?_, by simpa using hcap, ?_⟩
  · intro x
    match x with
    | [] => simpa using hroot0
    | i :: y =>
      rcases lt_or_ge i b with hi | hi
      · rw [getReq_graftClientMove_of_lt hi]
        exact hpos i hi y
      · rw [getReq_graftClientMove_of_ge hi]
  · intro x
    match x with
    | [] =>
      refine le_trans (le_of_eq ?_) (le_trans hsum (le_of_eq (by simp)))
      exact Finset.sum_congr rfl fun c _ => by simp
    | i :: y =>
      have hkey : ∀ c : ℕ, (i :: y) ++ [c] = i :: (y ++ [c]) := fun _ => rfl
      rcases lt_or_ge i b with hi | hi
      · rw [getReq_graftClientMove_of_lt hi]
        refine le_trans (le_of_eq ?_) (hchild i hi y)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hkey c.val, getReq_graftClientMove_of_lt hi]
      · rw [getReq_graftClientMove_of_ge hi]
        refine le_of_eq (Finset.sum_eq_zero fun c _ => ?_)
        rw [hkey c.val, getReq_graftClientMove_of_ge hi]

/-! ### Two-level graft -/

/-- The move of the half-step inside one tree: `root` at the root, `son c` at
the son `c`, and the move `g c c'` below the grandson `c'` of the son `c`. -/
def graftTwoLevel (root : ℚ) (b : ℕ) (son : ℕ → ℚ) (g : ℕ → ℕ → ClientMove) : ClientMove :=
  graftClientMove root b (fun c => graftClientMove (son c) b (g c))

/-- A two-level graft requests `root` at the root. -/
@[simp] lemma getReq_graftTwoLevel_root (root : ℚ) (b : ℕ) (son : ℕ → ℚ)
    (g : ℕ → ℕ → ClientMove) : getReq (graftTwoLevel root b son g) [] = root := by
  simp [graftTwoLevel]

/-- A two-level graft requests `son c` at the child `c` below the branching. -/
@[simp] lemma getReq_graftTwoLevel_son {root : ℚ} {b c : ℕ} (hc : c < b) (son : ℕ → ℚ)
    (g : ℕ → ℕ → ClientMove) : getReq (graftTwoLevel root b son g) [c] = son c := by
  simp [graftTwoLevel, getReq_graftClientMove_of_lt hc]

/-- Below a grandchild `(c, c')` a two-level graft reproduces the grafted move `g c c'`. -/
@[simp] lemma getReq_graftTwoLevel_grandson {root : ℚ} {b c c' : ℕ} (hc : c < b) (hc' : c' < b)
    (son : ℕ → ℚ) (g : ℕ → ℕ → ClientMove) (x : GacsDayNode) :
    getReq (graftTwoLevel root b son g) (c :: c' :: x) = getReq (g c c') x := by
  simp [graftTwoLevel, getReq_graftClientMove_of_lt hc, getReq_graftClientMove_of_lt hc']

/-- **The two-level graft is coherent.** Below every used grandson the client
plays the move supplied by the recursive call; the son requests have to carry
the demand of their grandsons, and the root request the demand of its sons. -/
theorem requestCoherentCap_graftTwoLevel {b : ℕ} {alpha root : ℚ} {son : ℕ → ℚ}
    {g : ℕ → ℕ → ClientMove}
    (hroot0 : 0 ≤ root) (hcap : root ≤ alpha)
    (hson0 : ∀ c < b, 0 ≤ son c)
    (hsum : ∑ c : Fin b, son c.val ≤ root)
    (hsonsum : ∀ c < b, ∑ c' : Fin b, getReq (g c c'.val) [] ≤ son c)
    (hpos : ∀ c < b, ∀ c' < b, ∀ x, 0 ≤ getReq (g c c') x)
    (hchild : ∀ c < b, ∀ c' < b, ∀ x,
      getReq (g c c') x ≥ ∑ d : Fin b, getReq (g c c') (x ++ [d.val])) :
    requestCoherentCap b alpha (graftTwoLevel root b son g) := by
  refine requestCoherentCap_graftClientMove hroot0 hcap ?_ ?_ ?_
  · refine le_trans (le_of_eq ?_) hsum
    exact Finset.sum_congr rfl fun c _ => by simp
  · intro c hc x
    match x with
    | [] => simpa using hson0 c hc
    | c' :: y =>
      rcases lt_or_ge c' b with hc' | hc'
      · rw [getReq_graftClientMove_of_lt hc']
        exact hpos c hc c' hc' y
      · rw [getReq_graftClientMove_of_ge hc']
  · intro c hc x
    match x with
    | [] =>
      refine le_trans (le_of_eq ?_) (le_trans (hsonsum c hc) (le_of_eq (by simp)))
      exact Finset.sum_congr rfl fun c' _ => by simp
    | c' :: y =>
      have hkey : ∀ d : ℕ, (c' :: y) ++ [d] = c' :: (y ++ [d]) := fun _ => rfl
      rcases lt_or_ge c' b with hc' | hc'
      · rw [getReq_graftClientMove_of_lt hc']
        refine le_trans (le_of_eq ?_) (hchild c hc c' hc' y)
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hkey d.val, getReq_graftClientMove_of_lt hc']
      · rw [getReq_graftClientMove_of_ge hc']
        refine le_of_eq (Finset.sum_eq_zero fun d _ => ?_)
        rw [hkey d.val, getReq_graftClientMove_of_ge hc']

/-! ### Support of the two-level graft -/

/-- A two-level graft requests nothing outside its branching. -/
@[simp] lemma getReq_graftTwoLevel_of_ge {root : ℚ} {b c : ℕ} (hc : b ≤ c) (son : ℕ → ℚ)
    (g : ℕ → ℕ → ClientMove) (x : GacsDayNode) :
    getReq (graftTwoLevel root b son g) (c :: x) = 0 := by
  simp [graftTwoLevel, getReq_graftClientMove_of_ge hc]

/-- A two-level graft requests nothing below a grandchild outside its branching. -/
@[simp] lemma getReq_graftTwoLevel_of_son_ge {root : ℚ} {b c c' : ℕ} (hc : c < b) (hc' : b ≤ c')
    (son : ℕ → ℚ) (g : ℕ → ℕ → ClientMove) (x : GacsDayNode) :
    getReq (graftTwoLevel root b son g) (c :: c' :: x) = 0 := by
  simp [graftTwoLevel, getReq_graftClientMove_of_lt hc, getReq_graftClientMove_of_ge hc']

/-- **Range support of the graft.** If the moves of the recursive call never
request anything at a son of index `b` or more, neither does the graft; this is
the `range_supported` field of `GrayFamilyGameSpec`. -/
theorem getReq_graftTwoLevel_eq_zero_of_range {root : ℚ} {b : ℕ} {son : ℕ → ℚ}
    {g : ℕ → ℕ → ClientMove}
    (hg : ∀ c < b, ∀ c' < b, ∀ y, ∀ i, b ≤ i → getReq (g c c') (y ++ [i]) = 0)
    (x : GacsDayNode) {i : ℕ} (hi : b ≤ i) :
    getReq (graftTwoLevel root b son g) (x ++ [i]) = 0 := by
  match x with
  | [] => simpa using getReq_graftTwoLevel_of_ge hi son g []
  | c :: y =>
    rcases lt_or_ge c b with hc | hc
    swap
    · simpa using getReq_graftTwoLevel_of_ge hc son g (y ++ [i])
    match y with
    | [] => simpa using getReq_graftTwoLevel_of_son_ge hc hi son g []
    | c' :: z =>
      rcases lt_or_ge c' b with hc' | hc'
      · have hx : (c :: c' :: z) ++ [i] = c :: c' :: (z ++ [i]) := rfl
        rw [hx, getReq_graftTwoLevel_grandson hc hc']
        exact hg c hc c' hc' z i hi
      · simpa using getReq_graftTwoLevel_of_son_ge hc hc' son g (z ++ [i])

/-- **Height support of the graft.** The graft adds two levels to the moves of
the recursive call; this is the `tree_supported` field of
`GrayFamilyGameSpec`. -/
theorem getReq_graftTwoLevel_eq_zero_of_length {root : ℚ} {b h : ℕ} {son : ℕ → ℚ}
    {g : ℕ → ℕ → ClientMove}
    (hg : ∀ c < b, ∀ c' < b, ∀ y, h < y.length → getReq (g c c') y = 0)
    (x : GacsDayNode) (hx : h + 2 < x.length) :
    getReq (graftTwoLevel root b son g) x = 0 := by
  match x with
  | [] => simp at hx
  | c :: y =>
    rcases lt_or_ge c b with hc | hc
    swap
    · exact getReq_graftTwoLevel_of_ge hc son g y
    match y with
    | [] => simp at hx
    | c' :: z =>
      rcases lt_or_ge c' b with hc' | hc'
      · rw [getReq_graftTwoLevel_grandson hc hc']
        refine hg c hc c' hc' z ?_
        simpa using hx
      · exact getReq_graftTwoLevel_of_son_ge hc hc' son g z

/-! ### The son request pattern of the half-step -/

/-- Among the first `b` numbers, exactly `N ≤ b` are below `N`. -/
lemma card_range_filter_lt (b N : ℕ) (h : N ≤ b) :
    ({x ∈ Finset.range b | x < N} : Finset ℕ).card = N := by
  have hset : ({x ∈ Finset.range b | x < N} : Finset ℕ) = Finset.range N := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset, Finset.card_range]

/-- The `2 ^ (e - a)` used sons of a root carry exactly the root request. -/
theorem two_pow_sub_mul_dyadicScale {a e : ℕ} (hae : a ≤ e) :
    ((2 : ℚ) ^ (e - a)) * dyadicScale e = dyadicScale a := by
  obtain ⟨k, rfl⟩ : ∃ k, e = a + k := ⟨e - a, by omega⟩
  have hk : a + k - a = k := by omega
  simp only [dyadicScale, hk, pow_add, div_pow, one_pow]
  field_simp

/-- The son requests of the half-step: the first `2 ^ (e - a)` sons of a root
are raised to `epsilon = 2 ^ (-e)`, the remaining sons stay at `0`
(SUV p. 142, step 1). -/
def sonRequestPattern (a e c : ℕ) : ℚ := if c < 2 ^ (e - a) then dyadicScale e else 0

/-- The son request pattern is nonnegative. -/
lemma sonRequestPattern_nonneg (a e c : ℕ) : 0 ≤ sonRequestPattern a e c := by
  unfold sonRequestPattern dyadicScale
  split <;> positivity

/-- The son request pattern never exceeds `dyadicScale e`. -/
lemma sonRequestPattern_le (a e c : ℕ) : sonRequestPattern a e c ≤ dyadicScale e := by
  unfold sonRequestPattern dyadicScale
  split
  · exact le_rfl
  · positivity

/-- **The son requests exhaust the root request.** With `2 ^ (e - a)` used sons
at `epsilon` the coherence inequality at the root holds with equality, which is
what keeps this particular graft coherent while raising every used son
to `epsilon`. -/
theorem sum_sonRequestPattern {a e b : ℕ} (hae : a ≤ e) (hb : 2 ^ (e - a) ≤ b) :
    ∑ c : Fin b, sonRequestPattern a e c.val = dyadicScale a := by
  have h1 : ∑ c : Fin b, sonRequestPattern a e c.val
      = ((2 ^ (e - a) : ℕ) : ℚ) * dyadicScale e := by
    simp only [sonRequestPattern]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < 2 ^ (e - a) then dyadicScale e else 0) b,
      Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      card_range_filter_lt b _ hb]
  rw [h1]
  push_cast
  exact two_pow_sub_mul_dyadicScale hae

/-- The branching factor of the ladder always has room for the used sons. -/
lemma two_pow_sub_le_ladderBranching (B a e : ℕ) : 2 ^ (e - a) ≤ ladderBranching B a e :=
  le_trans (by
    have h : 1 ≤ 2 ^ (e - a) := Nat.one_le_two_pow
    omega) (le_max_left _ _)

/-! ### The family form -/

/-- The family client move of the half-step: in every tree the root requests
`alpha`, the son `c` requests `son i c`, and below the grandson `c'` of the son
`c` the client plays the move `g i c c'` supplied by the recursive call. -/
def graftGrandchildFamilyMove (n b : ℕ) (alpha : ℚ) (son : ℕ → ℕ → ℚ)
    (g : ℕ → ℕ → ℕ → ClientMove) : FamilyClientMove :=
  List.ofFn (fun i : Fin n => graftTwoLevel alpha b (son i.val) (g i.val))

/-- Each client of a grandchild graft plays the two-level graft of its own son values and grafted
moves. -/
@[simp] lemma familyClientMoveAt_graftGrandchildFamilyMove {n b i : ℕ} (hi : i < n) (alpha : ℚ)
    (son : ℕ → ℕ → ℚ) (g : ℕ → ℕ → ℕ → ClientMove) :
    familyClientMoveAt (graftGrandchildFamilyMove n b alpha son g) i =
      graftTwoLevel alpha b (son i) (g i) := by
  unfold familyClientMoveAt graftGrandchildFamilyMove
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-- Every root request of this grafted family move is exactly alpha; this is
an implementation lemma for the graft, not a global invariant. -/
@[simp] lemma getFamilyReq_graftGrandchildFamilyMove_root {n b i : ℕ} (hi : i < n) (alpha : ℚ)
    (son : ℕ → ℕ → ℚ) (g : ℕ → ℕ → ℕ → ClientMove) :
    getFamilyReq (graftGrandchildFamilyMove n b alpha son g) i [] = alpha := by
  simp [getFamilyReq, familyClientMoveAt_graftGrandchildFamilyMove hi]

/-- Each tree of the grafted family move is a coherent request capped by
`alpha`. -/
theorem requestCoherentCap_graftGrandchildFamilyMove {n b i : ℕ} (hi : i < n) {alpha : ℚ}
    {son : ℕ → ℕ → ℚ} {g : ℕ → ℕ → ℕ → ClientMove}
    (halpha : 0 ≤ alpha)
    (hson0 : ∀ c < b, 0 ≤ son i c)
    (hsum : ∑ c : Fin b, son i c.val ≤ alpha)
    (hsonsum : ∀ c < b, ∑ c' : Fin b, getReq (g i c c'.val) [] ≤ son i c)
    (hpos : ∀ c < b, ∀ c' < b, ∀ x, 0 ≤ getReq (g i c c') x)
    (hchild : ∀ c < b, ∀ c' < b, ∀ x,
      getReq (g i c c') x ≥ ∑ d : Fin b, getReq (g i c c') (x ++ [d.val])) :
    requestCoherentCap b alpha
      (familyClientMoveAt (graftGrandchildFamilyMove n b alpha son g) i) := by
  rw [familyClientMoveAt_graftGrandchildFamilyMove hi]
  exact requestCoherentCap_graftTwoLevel halpha le_rfl hson0 hsum hsonsum hpos hchild

/-- Family range support of the grafted move. -/
theorem getFamilyReq_graftGrandchildFamilyMove_eq_zero_of_range {n b : ℕ} {alpha : ℚ}
    {son : ℕ → ℕ → ℚ} {g : ℕ → ℕ → ℕ → ClientMove}
    (hg : ∀ j < n, ∀ c < b, ∀ c' < b, ∀ y, ∀ i, b ≤ i → getReq (g j c c') (y ++ [i]) = 0)
    (x : GacsDayNode) {i : ℕ} (hi : b ≤ i) {j : ℕ} (hj : j < n) :
    getFamilyReq (graftGrandchildFamilyMove n b alpha son g) j (x ++ [i]) = 0 := by
  rw [getFamilyReq, familyClientMoveAt_graftGrandchildFamilyMove hj]
  exact getReq_graftTwoLevel_eq_zero_of_range (hg j hj) x hi

/-- Family height support of the grafted move: the graft plays two levels above
the recursive call. -/
theorem getFamilyReq_graftGrandchildFamilyMove_eq_zero_of_length {n b h : ℕ} {alpha : ℚ}
    {son : ℕ → ℕ → ℚ} {g : ℕ → ℕ → ℕ → ClientMove}
    (hg : ∀ j < n, ∀ c < b, ∀ c' < b, ∀ y, h < y.length → getReq (g j c c') y = 0)
    (x : GacsDayNode) (hx : h + 2 < x.length) {j : ℕ} (hj : j < n) :
    getFamilyReq (graftGrandchildFamilyMove n b alpha son g) j x = 0 := by
  rw [getFamilyReq, familyClientMoveAt_graftGrandchildFamilyMove hj]
  exact getReq_graftTwoLevel_eq_zero_of_length (hg j hj) x hx

/-- **The round trip.** Restricting the grafted family move back to the
grandson slots returns exactly the moves of the recursive call, so the
invariant obtained from the recursive call transfers verbatim to the composite
play. -/
theorem getFamilyReq_restrictGrandchild_graftGrandchild {n b : ℕ}
    (slots : List (Fin n × Fin b × Fin b)) (alpha : ℚ) (son : ℕ → ℕ → ℚ)
    (g : ℕ → ℕ → ℕ → ClientMove) {j : ℕ} (hj : j < slots.length) (x : GacsDayNode) :
    getFamilyReq (restrictGrandchildClientMove slots
        (graftGrandchildFamilyMove n b alpha son g)) j x =
      getReq (g (slots.get ⟨j, hj⟩).1.val (slots.get ⟨j, hj⟩).2.1.val
        (slots.get ⟨j, hj⟩).2.2.val) x := by
  rw [getFamilyReq_restrictGrandchildClientMove slots _ j hj]
  set s := slots.get ⟨j, hj⟩ with hs
  simp only [getFamilyReq, List.cons_append, List.nil_append,
    familyClientMoveAt_graftGrandchildFamilyMove s.1.isLt]
  exact getReq_graftTwoLevel_grandson s.2.1.isLt s.2.2.isLt _ _ x

end Kolmogorov
