/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Effective.Configs

/-!
# Computable game values

A game of the construction is described by finite data `GD`; `SafeYes` with explicit fuel is
evaluated level by level on a finite box of states (masks × scaled scores), which makes the
evaluation primitive recursive.  The module gives the encoding, its correctness, and the
computability of the game values.

Part of `KolmogorovMathlib.RandomStrings.Effective`.
-/

namespace Kolmogorov.RandomStrings

/-! ## Computable game values

A game of the construction is described by finite data `GD`.  Positions are masks over the
strings in play (without repetitions), scores are scaled by `2^N` (all costs and the budget are
dyadic with denominator `2^N`), and `SafeYes` is evaluated level by level on the finite box of
states `U` (masks × scores `≤ E`), which makes the evaluation primitive recursive. -/

/-- The values `2|z| + 6` modified by a finite table (the first matching entry wins). -/
def tableFn (hT : List (BitString × ℕ)) (z : BitString) : ℕ :=
  hT.foldr (fun p r => if p.1 = z then p.2 else r) (2 * z.length + 6)

/-- A finite description of a game of the construction: the machine code `m`, the time bound `T`
(the value of the clock on the input), the input `x`, the table of the current values, the budget
exponent, the strings in play, the guard `phi` (whether the verdict of the machine is used) and
the default outcome `dflt` (the constant outcome when `phi = false`). -/
structure GD where
  m : ℕ
  T : ℕ
  x : BitString
  hT : List (BitString × ℕ)
  bud : ℕ
  X : List BitString
  phi : Bool
  dflt : Bool

/-- The game described by `g`. -/
noncomputable def GD.game (g : GD) : GameData :=
  gameOfBT (decodeCode g.m) g.T g.x (tableFn g.hT) ((2 : ℝ)⁻¹ ^ g.bud) g.X.toFinset g.phi g.dflt

/-- Removal of repetitions (primitive recursive form). -/
def dedupL (X : List BitString) : List BitString :=
  X.foldr (fun z acc => bif memStr z acc then acc else z :: acc) []

/-- The strings in play, without repetitions. -/
def GD.Xd (g : GD) : List BitString := dedupL g.X

/-- The scale exponent: all costs and the budget are multiples of `2^{-N}`. -/
def GD.N (g : GD) : ℕ := g.bud + g.X.foldr (fun z acc => z.length + tableFn g.hT z + acc) 0

/-- The scaled flip cost `2^N · flipCost`. -/
def GD.cost (g : GD) (z : BitString) : ℕ := 2 ^ (g.N - (z.length - 1)) - 2 ^ (g.N - tableFn g.hT z)

/-- The scaled budget `2^N · 2^{-bud}`. -/
def GD.E (g : GD) : ℕ := 2 ^ (g.N - g.bud)

/-- All sublists of a list (positions are sublists of the strings in play). -/
def allSub (X : List BitString) : List (List BitString) :=
  X.foldr (fun z acc => acc.flatMap fun l => [l, z :: l]) [[]]

/-- `S ⊆ S'` as a test. -/
def subB (S S' : List BitString) : Bool := S.foldr (fun z b => memStr z S' && b) true

/-- `∀ a ∈ l, p a` as a primitive recursive test. -/
def allB {β : Type} (l : List β) (p : β → Bool) : Bool := l.foldr (fun a b => p a && b) true

/-- `∃ a ∈ l, p a` as a primitive recursive test. -/
def anyB {β : Type} (l : List β) (p : β → Bool) : Bool := l.foldr (fun a b => p a || b) false

/-- The scaled cost of the move `S ↦ S'`. -/
def GD.mc (g : GD) (S S' : List BitString) : ℕ :=
  S'.foldr (fun z acc => (bif memStr z S then 0 else g.cost z) + acc) 0

/-- The oracle list of the position `S` restricted to the possible queries. -/
def GD.ans (g : GD) (S : List BitString) : List BitString :=
  (queryListCodeT g.m g.T g.x).flatMap fun z =>
    bif decide (z.length ≤ tableFn g.hT z) && !(memStr z S) then [z] else []

/-- The outcome of the position `S`: the verdict of the clocked machine if `phi`, else `dflt`. -/
def GD.outC (g : GD) (S : List BitString) : Bool :=
  bif g.phi then clockedOutcomeT g.m g.T (g.ans S) g.x else g.dflt

/-- One level of the evaluation of `SafeYes` at `u = (S, sY, sN)` (NO to move), given the values
`f` at the next level: the outcome is `true` and every legal non-passing NO move `S'` has a legal
YES answer `R` (possibly a pass) to a position where `f` holds. -/
def GD.F (g : GD) (u : List BitString × ℕ × ℕ) (f : List BitString × ℕ × ℕ → Bool) : Bool :=
  g.outC u.1 && allB (allSub g.Xd) fun S' =>
    !(subB u.1 S' && decide (u.2.2 + g.mc u.1 S' ≤ g.E)) || subB S' u.1 ||
      anyB (allSub g.Xd) fun R =>
        subB S' R && decide (u.2.1 + g.mc S' R ≤ g.E) &&
          f (R, u.2.1 + g.mc S' R, u.2.2 + g.mc u.1 S')

/-- The finite box of states: positions and scores `≤ E`. -/
def GD.U (g : GD) : List (List BitString × ℕ × ℕ) :=
  (allSub g.Xd).flatMap fun S => (List.range (g.E + 1)).flatMap fun a =>
    (List.range (g.E + 1)).map fun b => (S, a, b)

/-- Lookup in a table of values (`false` if absent). -/
def lookupT (v : List BitString × ℕ × ℕ) (tbl : List ((List BitString × ℕ × ℕ) × Bool)) : Bool :=
  tbl.foldr (fun p r => bif decide (p.1 = v) then p.2 else r) false

/-- The table of values at level `n` on the box `U`. -/
def GD.tab (g : GD) : ℕ → List ((List BitString × ℕ × ℕ) × Bool)
  | 0 => g.U.map fun u => (u, g.F u fun _ => false)
  | n + 1 => g.U.map fun u => (u, g.F u fun v => lookupT v (g.tab n))

/-- The evaluation of `SafeYes` with fuel `n` (looked up in the table). -/
def GD.evS (g : GD) (n : ℕ) (v : List BitString × ℕ × ℕ) : Bool := lookupT v (g.tab n)

/-- The computable game value: YES has a first move `S` (possibly a pass) to a safe position. -/
def valC (g : GD) : Bool :=
  anyB (allSub g.Xd) fun S => decide (g.mc [] S ≤ g.E) && g.evS g.Xd.length (S, g.mc [] S, 0)

/-! ### `SafeYes` with explicit fuel -/

/-- `SafeYes` with explicit fuel (well-founded unfolding of the inductive predicate). -/
def SafeYesF (d : GameData) : ℕ → GState → Prop
  | 0, st => d.outcome st.S = true ∧ ∀ S', LegalMove d st S' → S' = st.S
  | n + 1, st => d.outcome st.S = true ∧ ∀ S', LegalMove d st S' → S' ≠ st.S →
      ∃ R, LegalMove d (applyMove d st S') R ∧ SafeYesF d n (applyMove d (applyMove d st S') R)

/-- The proposition `SafeYes` is equivalent to `SafeYesF` with explicit fuel up to the number
of remaining elements. -/
theorem safeYes_iff_safeYesF (d : GameData) (n : ℕ) : ∀ st : GState, st.S ⊆ d.X →
    (d.X \ st.S).card ≤ n → (SafeYes d st ↔ SafeYesF d n st) := by
  classical
  induction n with
  | zero =>
    intro st hSX hcard
    have hXS : d.X ⊆ st.S := by
      intro z hz
      by_contra hzS
      have hpos := Finset.card_pos.2 ⟨z, Finset.mem_sdiff.2 ⟨hz, hzS⟩⟩
      omega
    have hmove : ∀ S', LegalMove d st S' → S' = st.S := fun S' hL =>
      Finset.Subset.antisymm (hL.2.1.trans hXS) hL.1
    constructor
    · intro h
      exact ⟨h.outcome, hmove⟩
    · rintro ⟨hout, -⟩
      exact SafeYes.intro st id hout (fun S' hL hne => absurd (hmove S' hL) hne)
        (fun S' hL hne => absurd (hmove S' hL) hne)
  | succ n ih =>
    intro st hSX hcard
    have hcard' : ∀ S' R, LegalMove d st S' → S' ≠ st.S →
        LegalMove d (applyMove d st S') R →
        (applyMove d (applyMove d st S') R).S ⊆ d.X ∧
          (d.X \ (applyMove d (applyMove d st S') R).S).card ≤ n := by
      intro S' R hL hne hR
      refine ⟨hR.2.1, ?_⟩
      have h1 := card_sdiff_lt hL.1 hL.2.1 hne
      have h2 : (d.X \ R).card ≤ (d.X \ S').card :=
        Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hR.1)
      change (d.X \ R).card ≤ n
      omega
    constructor
    · intro h
      cases h with
      | intro _ reply hout hlegal hsafe =>
        refine ⟨hout, fun S' hL hne => ⟨reply S', hlegal S' hL hne, ?_⟩⟩
        have hc := hcard' S' (reply S') hL hne (hlegal S' hL hne)
        exact (ih _ hc.1 hc.2).1 (hsafe S' hL hne)
    · rintro ⟨hout, hall⟩
      refine SafeYes.intro st (fun S' => if h : ∃ R, LegalMove d (applyMove d st S') R ∧
          SafeYesF d n (applyMove d (applyMove d st S') R) then Classical.choose h else S')
        hout ?_ ?_
      · intro S' hL hne
        have hh := hall S' hL hne
        rw [dite_eq_left hh]; exact (Classical.choose_spec hh).1
      · intro S' hL hne
        have hh := hall S' hL hne
        rw [dite_eq_left hh]
        have hc := hcard' S' _ hL hne (Classical.choose_spec hh).1
        exact (ih _ hc.1 hc.2).2 (Classical.choose_spec hh).2

/-- The value of the game is `true` if and only if there exists a valid initial move that
results in a state satisfying `SafeYesF`. -/
theorem val_eq_true_iff_safeYesF (d : GameData) :
    val d = true ↔ ∃ S₁, LegalMove d GState.init S₁ ∧
      SafeYesF d d.X.card (applyMove d GState.init S₁) := by
  rw [determined]
  constructor
  · rintro ⟨S₁, hL, hs⟩
    exact ⟨S₁, hL, (safeYes_iff_safeYesF d _ _ hL.2.1
      (Finset.card_le_card Finset.sdiff_subset)).1 hs⟩
  · rintro ⟨S₁, hL, hs⟩
    exact ⟨S₁, hL, (safeYes_iff_safeYesF d _ _ hL.2.1
      (Finset.card_le_card Finset.sdiff_subset)).2 hs⟩

/-! ### The encoding -/

/-- The evaluation unfolds one level (on the box). -/
theorem lookupT_map (L : List (List BitString × ℕ × ℕ)) (f : List BitString × ℕ × ℕ → Bool)
    (v : List BitString × ℕ × ℕ) (hv : v ∈ L) : lookupT v (L.map fun u => (u, f u)) = f v := by
  induction L with
  | nil => simp at hv
  | cons w L ih =>
    have e : lookupT v ((w :: L).map fun u => (u, f u)) =
        bif decide (w = v) then f w else lookupT v (L.map fun u => (u, f u)) := rfl
    rw [e]
    by_cases hw : w = v
    · subst hw; simp
    · simp only [hw, decide_false, Bool.cond_false]
      exact ih ((List.mem_cons.1 hv).resolve_left (Ne.symm hw))

/-- The evaluation function `evS` at step `n + 1` applies the transition function `F` to the
current state and the evaluation at step `n`. -/
theorem evS_succ (g : GD) (n : ℕ) (u : List BitString × ℕ × ℕ) (hu : u ∈ g.U) :
    g.evS (n + 1) u = g.F u (g.evS n) := by
  unfold GD.evS
  rw [GD.tab, lookupT_map _ _ _ hu]

/-- The evaluation function `evS` at step `0` applies the transition function `F` with a
constantly false evaluation function. -/
theorem evS_zero (g : GD) (u : List BitString × ℕ × ℕ) (hu : u ∈ g.U) :
    g.evS 0 u = g.F u fun _ => false := by
  unfold GD.evS
  rw [GD.tab, lookupT_map _ _ _ hu]

/-- The state of the game encoded by `(M, sY, sN)` (NO to move). -/
noncomputable def GD.st (g : GD) (u : List BitString × ℕ × ℕ) : GState :=
  ⟨u.1.toFinset, (u.2.1 : ℝ) / 2 ^ g.N, (u.2.2 : ℝ) / 2 ^ g.N, false⟩

/-! ### Correctness of the encoding -/

/-- The list function `allB` returns `true` if and only if the predicate `p` returns `true`
for all elements of the list. -/
theorem allB_iff {β : Type} (l : List β) (p : β → Bool) :
    allB l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allB]
  | cons a l ih =>
    have e : allB (a :: l) p = (p a && allB l p) := rfl
    rw [e, Bool.and_eq_true, ih, List.forall_mem_cons]

/-- The list function `anyB` returns `true` if and only if the predicate `p` returns `true`
for some element of the list. -/
theorem anyB_iff {β : Type} (l : List β) (p : β → Bool) :
    anyB l p = true ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil => simp [anyB]
  | cons a l ih =>
    have e : anyB (a :: l) p = (p a || anyB l p) := rfl
    rw [e, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨a, List.mem_cons_self, h⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, h⟩
    · rintro ⟨x, hx, h⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, h⟩

/-- The subset test function `subB` returns `true` if and only if all elements of the first
list are contained in the second list. -/
theorem subB_iff (S S' : List BitString) : subB S S' = true ↔ ∀ z ∈ S, z ∈ S' := by
  induction S with
  | nil => simp [subB]
  | cons z S ih =>
    have e : subB (z :: S) S' = (memStr z S' && subB S S') := rfl
    rw [e, Bool.and_eq_true, memStr_iff, ih, List.forall_mem_cons]

/-- The membership test function `memStr` returns `false` if the element is not contained in
the list. -/
theorem memStr_eq_false {z : BitString} {S : List BitString} (h : z ∉ S) : memStr z S = false := by
  cases hm : memStr z S
  · rfl
  · exact absurd ((memStr_iff _ _).1 hm) h

/-- The deduplication function `dedupL` applied to a cons list conditionally includes the head
based on whether it is already in the deduplicated tail. -/
theorem dedupL_cons (z : BitString) (X : List BitString) :
    dedupL (z :: X) = bif memStr z (dedupL X) then dedupL X else z :: dedupL X := rfl

/-- An element is in the result of `dedupL` if and only if it is in the original list. -/
theorem mem_dedupL (X : List BitString) (z : BitString) : z ∈ dedupL X ↔ z ∈ X := by
  induction X generalizing z with
  | nil => simp [dedupL]
  | cons w X ih =>
    rw [dedupL_cons]
    cases h : memStr w (dedupL X)
    · simp only [Bool.cond_false, List.mem_cons, ih]
    · simp only [Bool.cond_true, ih, List.mem_cons]
      have hw : w ∈ X := (ih w).1 ((memStr_iff _ _).1 h)
      constructor
      · intro hz; exact Or.inr hz
      · rintro (rfl | hz)
        · exact hw
        · exact hz

/-- The result of `dedupL` contains no duplicate elements. -/
theorem nodup_dedupL (X : List BitString) : (dedupL X).Nodup := by
  induction X with
  | nil => simp [dedupL]
  | cons w X ih =>
    rw [dedupL_cons]
    cases h : memStr w (dedupL X)
    · simp only [Bool.cond_false]
      refine List.nodup_cons.2 ⟨fun hw => ?_, ih⟩
      have := (memStr_iff _ _).2 hw
      rw [h] at this
      exact absurd this (by decide)
    · simpa using ih

/-- The `allSub` function applied to a cons list maps each sublist of the tail to itself and
itself with the head added. -/
theorem allSub_cons (z : BitString) (X : List BitString) :
    allSub (z :: X) = (allSub X).flatMap fun l => [l, z :: l] := rfl

/-- A list is an element of `allSub X` if and only if it is a sublist of `X`. -/
theorem mem_allSub_iff (X S : List BitString) : S ∈ allSub X ↔ S.Sublist X := by
  induction X generalizing S with
  | nil => simp [allSub]
  | cons z X ih =>
    rw [allSub_cons, List.mem_flatMap]
    constructor
    · rintro ⟨l, hl, hS⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl
      · exact ((ih _).1 hl).cons z
      · exact ((ih _).1 hl).cons_cons z
    · intro h
      cases h with
      | cons _ h => exact ⟨S, (ih S).2 h, by simp⟩
      | cons_cons _ h => exact ⟨_, (ih _).2 h, by simp⟩

/-- There exists a sublist generated by `allSub` that represents any given `Finset` of
elements from the original list. -/
theorem exists_allSub (X : List BitString) (T : Finset BitString) (hT : ∀ z ∈ T, z ∈ X) :
    ∃ S ∈ allSub X, S.toFinset = T := by
  classical
  refine ⟨X.filter fun z => decide (z ∈ T), (mem_allSub_iff _ _).2 List.filter_sublist, ?_⟩
  ext z
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hT z h, h⟩⟩

/-- An element is in `Xd` if and only if it is in `X`. -/
theorem GD.mem_Xd (g : GD) (z : BitString) : z ∈ g.Xd ↔ z ∈ g.X := mem_dedupL _ _

/-- Any sublist in `allSub Xd` contains no duplicate elements. -/
theorem GD.nodup_of_allSub (g : GD) {S : List BitString} (hS : S ∈ allSub g.Xd) : S.Nodup :=
  ((mem_allSub_iff _ _).1 hS).nodup (nodup_dedupL _)

/-- Any element of a sublist in `allSub Xd` is also in `X`. -/
theorem GD.mem_X_of_allSub (g : GD) {S : List BitString} (hS : S ∈ allSub g.Xd) :
    ∀ z ∈ S, z ∈ g.X :=
  fun z hz => (g.mem_Xd z).1 (((mem_allSub_iff _ _).1 hS).subset hz)

/-- The sum of the length and table cost for an element is at most the total folded cost of a
list containing it. -/
theorem le_foldr_N (hT : List (BitString × ℕ)) (X : List BitString) (z : BitString) (hz : z ∈ X) :
    z.length + tableFn hT z ≤ X.foldr (fun z acc => z.length + tableFn hT z + acc) 0 := by
  induction X with
  | nil => simp at hz
  | cons w X ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hz with rfl | hz
    · omega
    · have := ih hz; omega

/-- The length of any string in `X` and its table cost are bounded by `N`. -/
theorem GD.len_le_N (g : GD) (z : BitString) (hz : z ∈ g.X) :
    z.length ≤ g.N ∧ tableFn g.hT z ≤ g.N := by
  have := le_foldr_N g.hT g.X z hz
  unfold GD.N; omega

/-- The budget parameter `bud` is bounded by `N`. -/
theorem GD.bud_le_N (g : GD) : g.bud ≤ g.N := by unfold GD.N; omega

/-- The inverse of `2 ^ a` is equal to `2 ^ (N - a) / 2 ^ N`. -/
theorem inv_two_pow_eq (N a : ℕ) (h : a ≤ N) : (2 : ℝ)⁻¹ ^ a = (2 : ℝ) ^ (N - a) / 2 ^ N := by
  have h2 : (2 : ℝ) ^ N = 2 ^ (N - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [h2, inv_pow, div_mul_eq_div_div, div_self (by positivity), one_div]

/-- The `flipCost` of a string in `X` is equal to its scaled `cost`. -/
theorem GD.flipCost_eq (g : GD) (z : BitString) (hz : z ∈ g.X) :
    flipCost g.game z = (g.cost z : ℝ) / 2 ^ g.N := by
  obtain ⟨h1, h2⟩ := g.len_le_N z hz
  have e1 := inv_two_pow_eq g.N (z.length - 1) (by omega)
  have e2 := inv_two_pow_eq g.N (tableFn g.hT z) h2
  change max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ tableFn g.hT z) = _
  rw [e1, e2]
  unfold GD.cost
  rcases le_total (tableFn g.hT z) (z.length - 1) with hle | hle
  · have hp : 2 ^ (g.N - (z.length - 1)) ≤ 2 ^ (g.N - tableFn g.hT z) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.sub_eq_zero_of_le hp, Nat.cast_zero, zero_div]
    have hr : (2 : ℝ) ^ (g.N - (z.length - 1)) ≤ 2 ^ (g.N - tableFn g.hT z) := by
      exact_mod_cast hp
    exact max_eq_left (sub_nonpos.2 (div_le_div_of_nonneg_right hr (by positivity)))
  · have hp : 2 ^ (g.N - tableFn g.hT z) ≤ 2 ^ (g.N - (z.length - 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, sub_div]
    have hr : (2 : ℝ) ^ (g.N - tableFn g.hT z) ≤ 2 ^ (g.N - (z.length - 1)) := by
      exact_mod_cast hp
    exact max_eq_right (sub_nonneg.2 (div_le_div_of_nonneg_right hr (by positivity)))

/-- The error parameter `ε` is equal to the scaled value of `E`. -/
theorem GD.eps_eq (g : GD) : g.game.ε = (g.E : ℝ) / 2 ^ g.N := by
  change (2 : ℝ)⁻¹ ^ g.bud = _
  rw [inv_two_pow_eq g.N g.bud g.bud_le_N]
  unfold GD.E
  push_cast
  rfl

/-- The `mc` function computes the sum of the costs of elements in `S'` not in `S`. -/
theorem mc_eq_map_sum (g : GD) (S S' : List BitString) :
    g.mc S S' = (S'.map fun z => if z ∈ S then 0 else g.cost z).sum := by
  induction S' with
  | nil => rfl
  | cons z S' ih =>
    have e : g.mc S (z :: S') = (bif memStr z S then 0 else g.cost z) + g.mc S S' := rfl
    rw [e, ih, List.map_cons, List.sum_cons]
    congr 1
    by_cases hz : z ∈ S
    · rw [(memStr_iff _ _).2 hz, ite_eq_left hz]; rfl
    · rw [memStr_eq_false hz, ite_eq_right hz]; rfl

/-- The `moveCost` function computes the scaled sum of the costs of elements in the target
state not in the source state. -/
theorem GD.moveCost_eq (g : GD) (S S' : List BitString) (hS' : S'.Nodup) (hX : ∀ z ∈ S', z ∈ g.X) :
    moveCost g.game S.toFinset S'.toFinset = (g.mc S S' : ℝ) / 2 ^ g.N := by
  classical
  have h1 : (g.mc S S' : ℝ) =
      ∑ z ∈ S'.toFinset, ((if z ∈ S then 0 else g.cost z : ℕ) : ℝ) := by
    rw [mc_eq_map_sum, Nat.cast_list_sum, List.map_map, ← List.sum_toFinset _ hS']
    rfl
  rw [h1, Finset.sum_div, moveCost, Finset.sdiff_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzX : z ∈ g.X := hX z (List.mem_toFinset.1 hz)
  by_cases hzS : z ∈ S
  · simp [hzS]
  · simp [hzS, GD.flipCost_eq g z hzX]

/-- The `outC` function computes the `outcome` evaluation over the provided list. -/
theorem GD.outC_eq (g : GD) (S : List BitString) : g.outC S = g.game.outcome S.toFinset := by
  classical
  have hag : ∀ z ∈ queryListCodeT g.m g.T g.x,
      (z ∈ oracleOf (tableFn g.hT) S.toFinset ↔ z ∈ g.ans S) := by
    intro z hz
    have hc : ∀ w : BitString, (decide (w.length ≤ tableFn g.hT w) && !memStr w S) = true ↔
        (w.length ≤ tableFn g.hT w ∧ w ∉ S) := by
      intro w
      by_cases hw : w ∈ S
      · simp [hw, (memStr_iff _ _).2 hw]
      · simp [hw, memStr_eq_false hw]
    simp only [oracleOf, Set.mem_ofPred_eq, List.mem_toFinset, GD.ans, List.mem_flatMap]
    constructor
    · intro h
      refine ⟨z, hz, ?_⟩
      rw [(hc z).2 h]; simp
    · rintro ⟨w, -, hw⟩
      cases hcw : (decide (w.length ≤ tableFn g.hT w) && !memStr w S)
      · rw [hcw] at hw; simp at hw
      · rw [hcw] at hw
        simp only [Bool.cond_true, List.mem_singleton] at hw
        subst hw
        exact (hc _).1 hcw
  have key : clockedOutcomeT g.m g.T (g.ans S) g.x = true ↔
      ClockedAcceptsT (decodeCode g.m) g.T (oracleOf (tableFn g.hT) S.toFinset) g.x :=
    (clockedAcceptsT_iff_clockedOutcomeT g.m g.T g.x _ (g.ans S) hag).symm
  have hd : g.game.outcome S.toFinset = bif g.phi then
      decide (ClockedAcceptsT (decodeCode g.m) g.T (oracleOf (tableFn g.hT) S.toFinset) g.x)
      else g.dflt := rfl
  rw [hd, GD.outC]
  cases g.phi
  · rfl
  · rw [Bool.cond_true, Bool.cond_true, Bool.eq_iff_iff, key, decide_eq_true_iff]

/-- A state `(S, a, b)` is in `U` if and only if `S` is a sublist in `Xd` and the costs `a`
and `b` are bounded by `E`. -/
theorem GD.mem_U (g : GD) (S : List BitString) (a b : ℕ) :
    (S, a, b) ∈ g.U ↔ S ∈ allSub g.Xd ∧ a ≤ g.E ∧ b ≤ g.E := by
  simp only [GD.U, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨S₀, hS₀, a₀, ha₀, b₀, hb₀, rfl, rfl, rfl⟩
    exact ⟨hS₀, by omega, by omega⟩
  · rintro ⟨hS, ha, hb⟩
    exact ⟨S, hS, a, by omega, b, by omega, rfl, rfl, rfl⟩

/-- The legality of a 'NO' move from a state to `S'` is equivalent to the conditions on `subB`
and the cost bound. -/
theorem GD.legal_no_iff (g : GD) (u : List BitString × ℕ × ℕ) (S' : List BitString)
    (hS' : S' ∈ allSub g.Xd) :
    LegalMove g.game (g.st u) S'.toFinset ↔ subB u.1 S' = true ∧ u.2.2 + g.mc u.1 S' ≤ g.E := by
  have hX := g.mem_X_of_allSub hS'
  have hc := GD.moveCost_eq g u.1 S' (g.nodup_of_allSub hS') hX
  have he := GD.eps_eq g
  have hpos : (0 : ℝ) < 2 ^ g.N := by positivity
  change (u.1.toFinset ⊆ S'.toFinset ∧ S'.toFinset ⊆ g.X.toFinset ∧
    (if false = true then
      (u.2.1 : ℝ) / 2 ^ g.N + moveCost g.game u.1.toFinset S'.toFinset ≤ g.game.ε
      else (u.2.2 : ℝ) / 2 ^ g.N + moveCost g.game u.1.toFinset S'.toFinset ≤ g.game.ε)) ↔ _
  rw [ite_eq_right Bool.false_ne_true, hc, he, subB_iff, ← add_div,
    div_le_div_iff_of_pos_right hpos]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨fun z hz => List.mem_toFinset.1 (h1 (List.mem_toFinset.2 hz)), by exact_mod_cast h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨fun z hz => List.mem_toFinset.2 (h1 z (List.mem_toFinset.1 hz)), fun z hz => ?_,
      by exact_mod_cast h3⟩
    rw [List.mem_toFinset] at hz ⊢
    exact hX z hz

/-- The legality of a 'YES' move from a state to `R` is equivalent to the conditions on `subB`
and the cost bound. -/
theorem GD.legal_yes_iff (g : GD) (S' R : List BitString) (a : ℕ) (b : ℝ) (hR : R ∈ allSub g.Xd) :
    LegalMove g.game ⟨S'.toFinset, (a : ℝ) / 2 ^ g.N, b, true⟩ R.toFinset ↔
      subB S' R = true ∧ a + g.mc S' R ≤ g.E := by
  have hX := g.mem_X_of_allSub hR
  have hc := GD.moveCost_eq g S' R (g.nodup_of_allSub hR) hX
  have he := GD.eps_eq g
  have hpos : (0 : ℝ) < 2 ^ g.N := by positivity
  change (S'.toFinset ⊆ R.toFinset ∧ R.toFinset ⊆ g.X.toFinset ∧
    (if true = true then (a : ℝ) / 2 ^ g.N + moveCost g.game S'.toFinset R.toFinset ≤ g.game.ε
      else b + moveCost g.game S'.toFinset R.toFinset ≤ g.game.ε)) ↔ _
  rw [ite_eq_left rfl, hc, he, subB_iff, ← add_div, div_le_div_iff_of_pos_right hpos]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨fun z hz => List.mem_toFinset.1 (h1 (List.mem_toFinset.2 hz)), by exact_mod_cast h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨fun z hz => List.mem_toFinset.2 (h1 z (List.mem_toFinset.1 hz)), fun z hz => ?_,
      by exact_mod_cast h3⟩
    rw [List.mem_toFinset] at hz ⊢
    exact hX z hz

/-- Applying a 'NO' move to a state yields a new state with updated lists and modified
YES-cost based on `mc`. -/
theorem GD.apply_no (g : GD) (u : List BitString × ℕ × ℕ) (S' : List BitString)
    (hS' : S' ∈ allSub g.Xd) :
    applyMove g.game (g.st u) S'.toFinset =
      ⟨S'.toFinset, (u.2.1 : ℝ) / 2 ^ g.N, ((u.2.2 + g.mc u.1 S' : ℕ) : ℝ) / 2 ^ g.N, true⟩ := by
  have hc := GD.moveCost_eq g u.1 S' (g.nodup_of_allSub hS') (g.mem_X_of_allSub hS')
  change (⟨S'.toFinset, (u.2.1 : ℝ) / 2 ^ g.N,
    (u.2.2 : ℝ) / 2 ^ g.N + moveCost g.game u.1.toFinset S'.toFinset, true⟩ : GState) = _
  rw [hc]
  congr 1
  push_cast
  ring

/-- Applying a 'YES' move to a state yields a new state with updated lists and modified
NO-cost based on `mc`. -/
theorem GD.apply_yes (g : GD) (S' R : List BitString) (a : ℕ) (b : ℝ) (hR : R ∈ allSub g.Xd) :
    applyMove g.game ⟨S'.toFinset, (a : ℝ) / 2 ^ g.N, b, true⟩ R.toFinset =
      ⟨R.toFinset, ((a + g.mc S' R : ℕ) : ℝ) / 2 ^ g.N, b, false⟩ := by
  have hc := GD.moveCost_eq g S' R (g.nodup_of_allSub hR) (g.mem_X_of_allSub hR)
  change (⟨R.toFinset, (a : ℝ) / 2 ^ g.N + moveCost g.game S'.toFinset R.toFinset, b,
    false⟩ : GState) = _
  rw [hc]
  congr 1
  push_cast
  ring

/-- One level of the evaluation is correct, given correct values at the next level. -/
theorem GD.F_iff (g : GD) (u : List BitString × ℕ × ℕ) (hu : u ∈ g.U)
    (f : List BitString × ℕ × ℕ → Bool) (Pn : GState → Prop)
    (hf : ∀ v ∈ g.U, f v = true ↔ Pn (g.st v)) :
    g.F u f = true ↔ (g.game.outcome (g.st u).S = true ∧ ∀ T, LegalMove g.game (g.st u) T →
      T ≠ (g.st u).S → ∃ Rf, LegalMove g.game (applyMove g.game (g.st u) T) Rf ∧
        Pn (applyMove g.game (applyMove g.game (g.st u) T) Rf)) := by
  obtain ⟨S, a, b⟩ := u
  obtain ⟨hS, ha, hb⟩ := (g.mem_U S a b).1 hu
  have hsubX : ∀ T : Finset BitString, T ⊆ g.game.X → ∀ z ∈ T, z ∈ g.Xd := by
    intro T hT z hz
    have := hT hz
    rw [show g.game.X = g.X.toFinset from rfl, List.mem_toFinset] at this
    exact (g.mem_Xd z).2 this
  have hst : (g.st (S, a, b)).S = S.toFinset := rfl
  simp only [GD.F, Bool.and_eq_true, allB_iff]
  rw [GD.outC_eq, hst]
  apply and_congr_right
  intro _
  constructor
  · intro hall T hT hne
    obtain ⟨S', hS', rfl⟩ := exists_allSub g.Xd T (hsubX T hT.2.1)
    have hleg : subB S S' = true ∧ b + g.mc S S' ≤ g.E := (g.legal_no_iff (S, a, b) S' hS').1 hT
    have hP := hall S' hS'
    rw [hleg.1, decide_eq_true hleg.2] at hP
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hP
    rcases hP with h2 | h2
    · exfalso
      apply hne
      apply Finset.Subset.antisymm
      · intro z hz
        rw [List.mem_toFinset] at hz ⊢
        exact (subB_iff _ _).1 h2 z hz
      · intro z hz
        rw [List.mem_toFinset] at hz ⊢
        exact (subB_iff _ _).1 hleg.1 z hz
    · obtain ⟨R, hR, hRt⟩ := (anyB_iff _ _).1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hRt
      obtain ⟨⟨hsub, hle⟩, hfv⟩ := hRt
      refine ⟨R.toFinset, ?_, ?_⟩
      · rw [g.apply_no (S, a, b) S' hS']
        exact (g.legal_yes_iff S' R a _ hR).2 ⟨hsub, hle⟩
      · rw [g.apply_no (S, a, b) S' hS', g.apply_yes S' R a _ hR]
        have hv : (R, a + g.mc S' R, b + g.mc S S') ∈ g.U :=
          (g.mem_U _ _ _).2 ⟨hR, hle, hleg.2⟩
        exact (hf _ hv).1 hfv
  · intro hall S' hS'
    by_cases hg1 : subB S S' = true
    · by_cases hg2 : b + g.mc S S' ≤ g.E
      · rw [hg1, decide_eq_true hg2]
        simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true]
        by_cases hback : subB S' S = true
        · exact Or.inl hback
        · right
          have hT := (g.legal_no_iff (S, a, b) S' hS').2 ⟨hg1, hg2⟩
          have hne : S'.toFinset ≠ S.toFinset := by
            intro heq
            apply hback
            rw [subB_iff]
            intro z hz
            have : z ∈ S'.toFinset := List.mem_toFinset.2 hz
            rw [heq] at this
            exact List.mem_toFinset.1 this
          obtain ⟨Rf, hRf, hPn⟩ := hall _ hT hne
          rw [g.apply_no (S, a, b) S' hS'] at hRf hPn
          obtain ⟨R, hR, rfl⟩ := exists_allSub g.Xd Rf (hsubX Rf hRf.2.1)
          obtain ⟨hsub, hle⟩ := (g.legal_yes_iff S' R a _ hR).1 hRf
          rw [g.apply_yes S' R a _ hR] at hPn
          have hv : (R, a + g.mc S' R, b + g.mc S S') ∈ g.U :=
            (g.mem_U _ _ _).2 ⟨hR, hle, hg2⟩
          rw [anyB_iff]
          refine ⟨R, hR, ?_⟩
          rw [hsub, decide_eq_true hle, (hf _ hv).2 hPn]
          rfl
      · rw [hg1, decide_eq_false hg2]
        rfl
    · have h0 : subB S S' = false := by simpa using hg1
      rw [h0]
      rfl

/-- The evaluation is correct on the box. -/
theorem evS_iff (g : GD) (n : ℕ) (u : List BitString × ℕ × ℕ) (hu : u ∈ g.U) :
    g.evS n u = true ↔ SafeYesF g.game n (g.st u) := by
  induction n generalizing u with
  | zero =>
    rw [evS_zero g u hu, g.F_iff u hu (fun _ => false) (fun _ => False) (fun v _ => by simp)]
    change _ ↔ (g.game.outcome (g.st u).S = true ∧
      ∀ S', LegalMove g.game (g.st u) S' → S' = (g.st u).S)
    apply and_congr_right
    intro _
    constructor
    · intro h S' hL
      by_contra hne
      obtain ⟨_, _, hF⟩ := h S' hL hne
      exact hF
    · intro h S' hL hne
      exact absurd (h S' hL) hne
  | succ n ih =>
    rw [evS_succ g n u hu, g.F_iff u hu (g.evS n) (SafeYesF g.game n) (fun v hv => ih v hv)]
    rfl

/-- **Correctness of the computable game value.** -/
theorem valC_spec (g : GD) : valC g = val g.game := by
  classical
  have hcard : g.game.X.card = g.Xd.length := by
    change g.X.toFinset.card = (dedupL g.X).length
    rw [← List.toFinset_card_of_nodup (nodup_dedupL g.X)]
    congr 1
    ext z
    simp [mem_dedupL]
  have h0 : (∅ : Finset BitString) = ([] : List BitString).toFinset := List.toFinset_nil.symm
  have hinit : ∀ S ∈ allSub g.Xd,
      applyMove g.game GState.init S.toFinset = g.st (S, g.mc [] S, 0) := by
    intro S hS
    have hc := GD.moveCost_eq g [] S (g.nodup_of_allSub hS) (g.mem_X_of_allSub hS)
    change (⟨S.toFinset, 0 + moveCost g.game ∅ S.toFinset, 0, false⟩ : GState) =
      ⟨S.toFinset, ((g.mc [] S : ℕ) : ℝ) / 2 ^ g.N, ((0 : ℕ) : ℝ) / 2 ^ g.N, false⟩
    rw [h0, hc]
    simp
  have hlegal : ∀ S ∈ allSub g.Xd,
      LegalMove g.game GState.init S.toFinset ↔ g.mc [] S ≤ g.E := by
    intro S hS
    have hc := GD.moveCost_eq g [] S (g.nodup_of_allSub hS) (g.mem_X_of_allSub hS)
    have hX := g.mem_X_of_allSub hS
    change (∅ ⊆ S.toFinset ∧ S.toFinset ⊆ g.X.toFinset ∧
      (if true = true then 0 + moveCost g.game ∅ S.toFinset ≤ g.game.ε
        else 0 + moveCost g.game ∅ S.toFinset ≤ g.game.ε)) ↔ _
    rw [ite_eq_left rfl, h0, hc, GD.eps_eq, zero_add, div_le_div_iff_of_pos_right (by positivity)]
    constructor
    · rintro ⟨-, -, h⟩
      exact_mod_cast h
    · intro h
      refine ⟨by simp, fun z hz => ?_, by exact_mod_cast h⟩
      rw [List.mem_toFinset] at hz ⊢
      exact hX z hz
  rw [Bool.eq_iff_iff, val_eq_true_iff_safeYesF, hcard]
  unfold valC
  rw [anyB_iff]
  constructor
  · rintro ⟨S, hS, hb⟩
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hle, hev⟩ := hb
    refine ⟨S.toFinset, (hlegal S hS).2 hle, ?_⟩
    rw [hinit S hS]
    exact (evS_iff g _ _ ((g.mem_U _ _ _).2 ⟨hS, hle, Nat.zero_le _⟩)).1 hev
  · rintro ⟨S₁, hL, hs⟩
    have hsub : ∀ z ∈ S₁, z ∈ g.Xd := by
      intro z hz
      have := hL.2.1 hz
      rw [show g.game.X = g.X.toFinset from rfl, List.mem_toFinset] at this
      exact (g.mem_Xd z).2 this
    obtain ⟨S, hS, rfl⟩ := exists_allSub g.Xd S₁ hsub
    have hle := (hlegal S hS).1 hL
    refine ⟨S, hS, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hle, (evS_iff g _ _ ((g.mem_U _ _ _).2 ⟨hS, hle, Nat.zero_le _⟩)).2 ?_⟩
    rw [← hinit S hS]
    exact hs

/-! ### Computability -/

/-- `GD` as a product type. -/
def GD.equiv :
    GD ≃ ℕ × ℕ × BitString × List (BitString × ℕ) × ℕ × List BitString × Bool × Bool where
  toFun g := (g.m, g.T, g.x, g.hT, g.bud, g.X, g.phi, g.dflt)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable GD := Primcodable.ofEquiv _ GD.equiv

/-- The function projecting `m` from a `GD` object is primitive recursive. -/
theorem GD.primrec_m : Primrec GD.m :=
  (Primrec.fst.comp (Primrec.of_equiv (e := GD.equiv))).of_eq fun _ => rfl
/-- The function projecting `T` from a `GD` object is primitive recursive. -/
theorem GD.primrec_T : Primrec GD.T :=
  ((Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := GD.equiv))).of_eq fun _ => rfl
/-- The function projecting `x` from a `GD` object is primitive recursive. -/
theorem GD.primrec_x : Primrec GD.x :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := GD.equiv))).of_eq fun _ => rfl
/-- The function projecting `hT` from a `GD` object is primitive recursive. -/
theorem GD.primrec_hT : Primrec GD.hT :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    (Primrec.of_equiv (e := GD.equiv))).of_eq fun _ => rfl
/-- The function projecting `bud` from a `GD` object is primitive recursive. -/
theorem GD.primrec_bud : Primrec GD.bud :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    (Primrec.of_equiv (e := GD.equiv))).of_eq fun _ => rfl
/-- The function projecting `X` from a `GD` object is primitive recursive. -/
theorem GD.primrec_X : Primrec GD.X :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    Primrec.snd))))).comp (Primrec.of_equiv (e := GD.equiv))).of_eq fun _ => rfl
/-- The function projecting `phi` from a `GD` object is primitive recursive. -/
theorem GD.primrec_phi : Primrec GD.phi :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd)))))).comp (Primrec.of_equiv (e := GD.equiv))).of_eq fun _ => rfl
/-- The function projecting `dflt` from a `GD` object is primitive recursive. -/
theorem GD.primrec_dflt : Primrec GD.dflt :=
  ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd)))))).comp (Primrec.of_equiv (e := GD.equiv))).of_eq fun _ => rfl

/-- The lookup table function `tableFn` is primitive recursive. -/
theorem tableFn_primrec : Primrec₂ tableFn :=
  (Primrec.list_foldr (f := fun a : List (BitString × ℕ) × BitString => a.1)
    (g := fun a => 2 * a.2.length + 6) (h := fun a pr => if pr.1.1 = a.2 then pr.1.2 else pr.2)
    Primrec.fst (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.list_length.comp Primrec.snd)) (Primrec.const 6))
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- The deduplication function `dedupL` is primitive recursive. -/
theorem dedupL_primrec : Primrec dedupL :=
  (Primrec.list_foldr (f := fun X : List BitString => X) (g := fun _ => ([] : List BitString))
    (h := fun _ p => bif memStr p.1 p.2 then p.2 else p.1 :: p.2) Primrec.id (Primrec.const [])
    (Primrec.cond (memStr_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂).of_eq
    fun _ => rfl

/-- The function computing `Xd` from a `GD` object is primitive recursive. -/
theorem GD.primrec_Xd : Primrec GD.Xd := (dedupL_primrec.comp GD.primrec_X).of_eq fun _ => rfl

/-- The function computing `N` from a `GD` object is primitive recursive. -/
theorem GD.primrec_N : Primrec GD.N :=
  (Primrec.nat_add.comp GD.primrec_bud (Primrec.list_foldr (f := fun g : GD => g.X)
    (g := fun _ => 0) (h := fun g p => p.1.length + tableFn g.hT p.1 + p.2) GD.primrec_X
    (Primrec.const 0) (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (tableFn_primrec.comp (GD.primrec_hT.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun _ => rfl

/-- The power function `fun n => 2 ^ n` is primitive recursive. -/
theorem pow_primrec : Primrec₂ fun a b : ℕ => a ^ b := Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The `cost` function associated with a `GD` object is primitive recursive. -/
theorem GD.primrec_cost : Primrec₂ GD.cost :=
  (Primrec.nat_sub.comp
    (pow_primrec.comp (Primrec.const 2) (Primrec.nat_sub.comp (GD.primrec_N.comp Primrec.fst)
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1))))
    (pow_primrec.comp (Primrec.const 2) (Primrec.nat_sub.comp (GD.primrec_N.comp Primrec.fst)
      (tableFn_primrec.comp (GD.primrec_hT.comp Primrec.fst) Primrec.snd)))).of_eq fun _ => rfl

/-- The function computing `E` from a `GD` object is primitive recursive. -/
theorem GD.primrec_E : Primrec GD.E :=
  (pow_primrec.comp (Primrec.const 2) (Primrec.nat_sub.comp GD.primrec_N GD.primrec_bud)).of_eq
    fun _ => rfl

/-- The function computing all sublists `allSub` is primitive recursive. -/
theorem allSub_primrec : Primrec allSub :=
  (Primrec.list_foldr (f := fun X : List BitString => X)
    (g := fun _ => ([[]] : List (List BitString)))
    (h := fun _ p => p.2.flatMap fun l => [l, p.1 :: l]) Primrec.id (Primrec.const [[]])
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp Primrec.snd (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
        (Primrec.const []))).to₂).to₂).of_eq fun _ => rfl

/-- The subset test function `subB` is primitive recursive. -/
theorem subB_primrec : Primrec₂ subB :=
  (Primrec.list_foldr (f := fun a : List BitString × List BitString => a.1) (g := fun _ => true)
    (h := fun a p => memStr p.1 a.2 && p.2) Primrec.fst (Primrec.const true)
    (Primrec.and.comp (memStr_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

attribute [local irreducible] memStr GD.cost in
/-- The move cost function `mc` is primitive recursive over its arguments. -/
theorem GD.primrec_mc : Primrec fun p : GD × List BitString × List BitString =>
    p.1.mc p.2.1 p.2.2 :=
  (Primrec.list_foldr (f := fun p : GD × List BitString × List BitString => p.2.2) (g := fun _ => 0)
    (h := fun p q => (bif memStr q.1 p.2.1 then 0 else p.1.cost q.1) + q.2)
    (Primrec.snd.comp Primrec.snd) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.cond (memStr_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const 0)
      (GD.primrec_cost.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

attribute [local irreducible] memStr tableFn queryListCodeT in
/-- The function computing `ans` from a `GD` object is primitive recursive. -/
theorem GD.primrec_ans : Primrec fun p : GD × List BitString => p.1.ans p.2 :=
  (Primrec.list_flatMap (queryListCodeT_primrec.comp ((GD.primrec_m.comp Primrec.fst).pair
    ((GD.primrec_T.comp Primrec.fst).pair (GD.primrec_x.comp Primrec.fst))))
    (Primrec.cond (Primrec.and.comp (Primrec.nat_le.decide.comp
        (Primrec.list_length.comp Primrec.snd)
        (tableFn_primrec.comp (GD.primrec_hT.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
      (Primrec.not.comp (memStr_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])) (Primrec.const [])).to₂).of_eq
    fun _ => rfl

attribute [local irreducible] GD.ans clockedOutcomeT in
/-- The function computing `outC` from a `GD` object is primitive recursive. -/
theorem GD.primrec_outC : Primrec fun p : GD × List BitString => p.1.outC p.2 :=
  (Primrec.cond (GD.primrec_phi.comp Primrec.fst)
    (clockedOutcomeT_primrec.comp ((GD.primrec_m.comp Primrec.fst).pair ((GD.primrec_T.comp
      Primrec.fst).pair (GD.primrec_ans.pair (GD.primrec_x.comp Primrec.fst)))))
    (GD.primrec_dflt.comp Primrec.fst)).of_eq fun _ => rfl

/-- The lookup function `lookupT` for the evaluation table is primitive recursive. -/
theorem lookupT_primrec : Primrec₂ lookupT :=
  (Primrec.list_foldr
    (f := fun a : (List BitString × ℕ × ℕ) × List ((List BitString × ℕ × ℕ) × Bool) => a.2)
    (g := fun _ => false) (h := fun a q => bif decide (q.1.1 = a.1) then q.1.2 else q.2)
    Primrec.snd (Primrec.const false)
    (Primrec.cond (Primrec.eq.decide.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- The table type. -/
abbrev Tbl : Type := List ((List BitString × ℕ × ℕ) × Bool)

/-- The inner test of `F`: `R` is a legal YES answer to the NO move `S'` leading to a position
with value `true` in `acc`. -/
def GD.Q (g : GD) (u : List BitString × ℕ × ℕ) (acc : Tbl) (S' R : List BitString) : Bool :=
  subB S' R && decide (u.2.1 + g.mc S' R ≤ g.E) &&
    lookupT (R, u.2.1 + g.mc S' R, u.2.2 + g.mc u.1 S') acc

/-- The outer test of `F` for the NO move `S'`. -/
def GD.P (g : GD) (u : List BitString × ℕ × ℕ) (acc : Tbl) (S' : List BitString) : Bool :=
  !(subB u.1 S' && decide (u.2.2 + g.mc u.1 S' ≤ g.E)) || subB S' u.1 ||
    anyB (allSub g.Xd) (g.Q u acc S')

/-- The `F` transition function can be computed via `lookupT` if the state is in `U`. -/
theorem GD.F_lookup (g : GD) (u : List BitString × ℕ × ℕ) (acc : Tbl) :
    g.F u (fun v => lookupT v acc) = (g.outC u.1 && allB (allSub g.Xd) (g.P u acc)) := rfl

/-- The function applying `mc` within a composition is primitive recursive. -/
theorem GD.primrec_mc_comp {α : Type} [Primcodable α] {g : α → GD} {S S2 : α → List BitString}
    (hg : Primrec g) (hS : Primrec S) (hS2 : Primrec S2) :
    Primrec fun a => (g a).mc (S a) (S2 a) :=
  GD.primrec_mc.comp (hg.pair (hS.pair hS2))

attribute [local irreducible] subB GD.mc GD.E lookupT in
/-- The function computing the combined validity check `Q` is primitive recursive. -/
theorem GD.primrec_Q :
    Primrec fun x : (GD × (List BitString × ℕ × ℕ) × Tbl × List BitString) × List BitString =>
    x.1.1.Q x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2 := by
  have hg :
      Primrec fun x : (GD × (List BitString × ℕ × ℕ) × Tbl × List BitString) × List BitString =>
    x.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hu :
      Primrec fun x : (GD × (List BitString × ℕ × ℕ) × Tbl × List BitString) × List BitString =>
    x.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hacc :
      Primrec fun x : (GD × (List BitString × ℕ × ℕ) × Tbl × List BitString) × List BitString =>
      x.1.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hS' :
      Primrec fun x : (GD × (List BitString × ℕ × ℕ) × Tbl × List BitString) × List BitString =>
      x.1.2.2.2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hR :
      Primrec fun x : (GD × (List BitString × ℕ × ℕ) × Tbl × List BitString) × List BitString =>
    x.2 :=
    Primrec.snd
  have hmc1 := GD.primrec_mc_comp hg hS' hR
  have hmc2 := GD.primrec_mc_comp hg (Primrec.fst.comp hu) hS'
  have hY := Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp hu)) hmc1
  have hN := Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp hu)) hmc2
  exact (Primrec.and.comp (Primrec.and.comp (subB_primrec.comp hS' hR)
    (Primrec.nat_le.decide.comp hY (GD.primrec_E.comp hg)))
    (lookupT_primrec.comp (hR.pair (hY.pair hN)) hacc)).of_eq fun _ => rfl

attribute [local irreducible] subB GD.mc GD.E GD.Q allSub GD.Xd in
/-- The function computing the state update logic `P` is primitive recursive. -/
theorem GD.primrec_P : Primrec fun y : GD × (List BitString × ℕ × ℕ) × Tbl × List BitString =>
    y.1.P y.2.1 y.2.2.1 y.2.2.2 := by
  have hg : Primrec fun y : GD × (List BitString × ℕ × ℕ) × Tbl × List BitString => y.1 :=
    Primrec.fst
  have hu : Primrec fun y : GD × (List BitString × ℕ × ℕ) × Tbl × List BitString => y.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hS' : Primrec fun y : GD × (List BitString × ℕ × ℕ) × Tbl × List BitString => y.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hany : Primrec fun y : GD × (List BitString × ℕ × ℕ) × Tbl × List BitString =>
      anyB (allSub y.1.Xd) (y.1.Q y.2.1 y.2.2.1 y.2.2.2) :=
    (Primrec.list_foldr (f := fun y : GD × (List BitString × ℕ × ℕ) × Tbl × List BitString =>
        allSub y.1.Xd) (g := fun _ => false)
      (h := fun y p => y.1.Q y.2.1 y.2.2.1 y.2.2.2 p.1 || p.2)
      (allSub_primrec.comp (GD.primrec_Xd.comp hg)) (Primrec.const false)
      (Primrec.or.comp (GD.primrec_Q.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  exact (Primrec.or.comp (Primrec.or.comp (Primrec.not.comp (Primrec.and.comp
    (subB_primrec.comp (Primrec.fst.comp hu) hS')
    (Primrec.nat_le.decide.comp (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp hu))
      (GD.primrec_mc.comp (hg.pair ((Primrec.fst.comp hu).pair hS')))) (GD.primrec_E.comp hg))))
    (subB_primrec.comp hS' (Primrec.fst.comp hu))) hany).of_eq fun _ => rfl

attribute [local irreducible] GD.P GD.outC allSub GD.Xd in
/-- The transition function `F` associated with a `GD` object is primitive recursive. -/
theorem GD.primrec_F : Primrec fun p : GD × (List BitString × ℕ × ℕ) × Tbl =>
    p.1.F p.2.1 (fun v => lookupT v p.2.2) := by
  have hall : Primrec fun p : GD × (List BitString × ℕ × ℕ) × Tbl =>
      allB (allSub p.1.Xd) (p.1.P p.2.1 p.2.2) :=
    (Primrec.list_foldr (f := fun p : GD × (List BitString × ℕ × ℕ) × Tbl => allSub p.1.Xd)
      (g := fun _ => true) (h := fun p q => p.1.P p.2.1 p.2.2 q.1 && q.2)
      (allSub_primrec.comp (GD.primrec_Xd.comp Primrec.fst)) (Primrec.const true)
      (Primrec.and.comp (GD.primrec_P.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair ((Primrec.snd.comp
          (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd)))))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  refine (Primrec.and.comp (GD.primrec_outC.comp (Primrec.fst.pair (Primrec.fst.comp
    (Primrec.fst.comp Primrec.snd)))) hall).of_eq fun p => ?_
  exact (GD.F_lookup p.1 p.2.1 p.2.2).symm

attribute [local irreducible] allSub GD.Xd GD.E in
/-- The function computing the valid states space `U` is primitive recursive. -/
theorem GD.primrec_U : Primrec GD.U :=
  (Primrec.list_flatMap (allSub_primrec.comp GD.primrec_Xd)
    (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.nat_add.comp
      (GD.primrec_E.comp Primrec.fst) (Primrec.const 1)))
      (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp
        (GD.primrec_E.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1)))
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂).to₂).of_eq fun _ => rfl

/-- The evaluation table `tab` can be recursively defined based on `F`. -/
theorem GD.tab_eq (g : GD) (n : ℕ) : g.tab n =
    n.rec (g.U.map fun u => (u, g.F u fun v => lookupT v []))
      (fun _ acc => g.U.map fun u => (u, g.F u fun v => lookupT v acc)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [GD.tab, ih]

attribute [local irreducible] GD.U GD.F lookupT in
/-- The evaluation table `tab` associated with a `GD` object is primitive recursive. -/
theorem GD.primrec_tab : Primrec₂ GD.tab := by
  have hstep : Primrec fun p : GD × Tbl => p.1.U.map fun u => (u, p.1.F u fun v => lookupT v p.2) :=
    Primrec.list_map (GD.primrec_U.comp Primrec.fst) (Primrec.snd.pair (GD.primrec_F.comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.pair
        (Primrec.snd.comp Primrec.fst))))).to₂
  have h := Primrec.nat_rec (f := fun g : GD => g.U.map fun u => (u, g.F u fun v => lookupT v []))
    (g := fun g p => g.U.map fun u => (u, g.F u fun v => lookupT v p.2))
    (hstep.comp (Primrec.id.pair (Primrec.const [])))
    (hstep.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun g n => (GD.tab_eq g n).symm

attribute [local irreducible] GD.tab lookupT GD.mc GD.E allSub GD.Xd in
/-- The computable value function `valC` is primitive recursive. -/
theorem valC_primrec : Primrec valC := by
  have hL : Primrec fun g : GD => g.Xd.length := Primrec.list_length.comp GD.primrec_Xd
  have hmc : Primrec fun p : GD × List BitString => p.1.mc [] p.2 :=
    GD.primrec_mc.comp (Primrec.fst.pair ((Primrec.const []).pair Primrec.snd))
  have hev : Primrec fun p : GD × List BitString =>
      p.1.evS p.1.Xd.length (p.2, p.1.mc [] p.2, 0) :=
    (lookupT_primrec.comp (Primrec.snd.pair (hmc.pair (Primrec.const 0)))
      (GD.primrec_tab.comp Primrec.fst (hL.comp Primrec.fst))).of_eq fun _ => rfl
  exact (Primrec.list_foldr (f := fun g : GD => allSub g.Xd) (g := fun _ => false)
    (h := fun g q => (decide (g.mc [] q.1 ≤ g.E) && g.evS g.Xd.length (q.1, g.mc [] q.1, 0)) || q.2)
    (allSub_primrec.comp GD.primrec_Xd) (Primrec.const false)
    (Primrec.or.comp (Primrec.and.comp (Primrec.nat_le.decide.comp
      (hmc.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (GD.primrec_E.comp Primrec.fst)) (hev.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- The computable value function `valC` is effectively computable. -/
theorem valC_computable : Computable valC := valC_primrec.to_comp

end Kolmogorov.RandomStrings
