/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace

/-!
# The path game: keys, the key recursion, and its equivalence with the real game

Game semantics for `P^R_sa ⊆ EXP`.

The run of a position `S` (the strings asked along the run of the clocked machine under the oracle
`O_S`) is abstracted as `PathData.P S`; strict (tree) sub-adaptivity is abstracted by the address
structure `PathData.addr` (`mem_P`, `addr_sub`): every possible query `z` is asked along the run iff
the answers to the strings of its *address* (the answer history leading to `z`) are the recorded
ones.

* `PathData.key S = S ∩ P S`: the flipped strings on the run;
* `KeyMoveRaw`/`PathData.KeyMove`: the path-restricted moves seen on keys;
* `yesKRaw`/`PathData.yesK`, `PathData.noK`, `valKRaw`/`PathData.valK`: the fuel recursion over keys
  with the scores as natural numerators (as `safeYesB`/`gameValB`);
* the structural lemmas (`agree_of_sub`, `P_key`, `mem_P_of_mem_addr`,
  `not_mem_P_of_killed`, `killed_of_leave`, `tight_jmove`, `tight_realize`, `jmove_keyMove`,
  `proj`, `pass_iff`, `nonpass_of_offrun`, the `costN` bookkeeping);
* postponement `yesK_of_safeYes` (a real safe position gives a safe key position), exclusivity of
  the key recursion `yesK_noK_false`, and the centrepiece `PathData.valK_eq_val`.
-/

namespace Kolmogorov.RandomStrings

/-! ### Small facts about the game -/

/-- A legal move on NO's turn means the strings in play increase monotonically, the target
strings are in the allowed domain, and the new total cost does not exceed the budget. -/
theorem legalMove_noTurn_iff (d : GameData) (S S' : Finset BitString) (y n : ℝ) :
    LegalMove d ⟨S, y, n, false⟩ S' ↔ S ⊆ S' ∧ S' ⊆ d.X ∧ n + moveCost d S S' ≤ d.ε := by
  simp [LegalMove]

/-- A legal move on YES's turn means the strings in play increase monotonically, the target
strings are in the allowed domain, and the new total cost does not exceed the budget. -/
theorem legalMove_yesTurn_iff (d : GameData) (S S' : Finset BitString) (y n : ℝ) :
    LegalMove d ⟨S, y, n, true⟩ S' ↔ S ⊆ S' ∧ S' ⊆ d.X ∧ y + moveCost d S S' ≤ d.ε := by
  simp [LegalMove]

/-- Applying a move on NO's turn updates the strings in play, adds the move's cost to NO's
total, and switches the turn. -/
theorem applyMove_noTurn (d : GameData) (S S' : Finset BitString) (y n : ℝ) :
    applyMove d ⟨S, y, n, false⟩ S' = ⟨S', y, n + moveCost d S S', true⟩ := by
  simp [applyMove]

/-- Applying a move on YES's turn updates the strings in play, adds the move's cost to YES's
total, and switches the turn. -/
theorem applyMove_yesTurn (d : GameData) (S S' : Finset BitString) (y n : ℝ) :
    applyMove d ⟨S, y, n, true⟩ S' = ⟨S', y + moveCost d S S', n, false⟩ := by
  simp [applyMove]

/-- The inequality between natural numbers holds if and only if it holds for their quotients
by `2 ^ N` as real numbers. -/
theorem natCast_div_two_pow_le_iff (a b N : ℕ) :
    (a : ℝ) / 2 ^ N ≤ (b : ℝ) / 2 ^ N ↔ a ≤ b := by
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

/-! ### Cost bookkeeping (L11) -/

/-- The cost of transitioning across two nested subsets is the sum of the costs of each
transition. -/
theorem costN_add (c : BitString → ℕ) {S S' S'' : Finset BitString} (h1 : S ⊆ S') (h2 : S' ⊆ S'') :
    costN c S S'' = costN c S S' + costN c S' S'' := by
  unfold costN
  have hdisj : Disjoint (S' \ S) (S'' \ S') := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    exact (Finset.mem_sdiff.1 hz2).2 (Finset.mem_sdiff.1 hz1).1
  have hunion : S'' \ S = (S' \ S) ∪ (S'' \ S') := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hz, hzS⟩
      by_cases hz' : z ∈ S'
      · exact Or.inl ⟨hz', hzS⟩
      · exact Or.inr ⟨hz, hz'⟩
    · rintro (⟨hz, hzS⟩ | ⟨hz, hz'⟩)
      · exact ⟨h2 hz, hzS⟩
      · exact ⟨hz, fun h => hz' (h1 h)⟩
  rw [hunion, Finset.sum_union hdisj]

/-- The cost over a set difference is non-decreasing with respect to inclusion of the set
difference. -/
theorem costN_le_of_subset (c : BitString → ℕ) {S S' R R' : Finset BitString}
    (h : S' \ S ⊆ R' \ R) :
    costN c S S' ≤ costN c R R' :=
  Finset.sum_le_sum_of_subset h

/-- The transition cost from a set to its union with another is the sum of the costs of the
new elements. -/
theorem costN_union (c : BitString → ℕ) (S A : Finset BitString) :
    costN c S (S ∪ A) = ∑ z ∈ A \ S, c z := by
  unfold costN
  rw [Finset.union_sdiff_left]

/-- The transition cost from a set to itself is zero. -/
theorem costN_self (c : BitString → ℕ) (S : Finset BitString) : costN c S S = 0 := by
  simp [costN]

/-- The sum of costs over a subset of a union is bounded by the sum of costs over the
individual sets. -/
theorem sum_le_of_subset_union (c : BitString → ℕ) {s t u : Finset BitString} (h : s ⊆ t ∪ u) :
    ∑ z ∈ s, c z ≤ ∑ z ∈ t, c z + ∑ z ∈ u, c z := by
  have h1 : ∑ z ∈ s, c z ≤ ∑ z ∈ t ∪ u, c z := Finset.sum_le_sum_of_subset h
  have h2 : ∑ z ∈ t ∪ u, c z + ∑ z ∈ t ∩ u, c z = ∑ z ∈ t, c z + ∑ z ∈ u, c z :=
    Finset.sum_union_inter
  omega

/-! ### Raw key moves and the key recursion

These use only the strings in play `X`, the run map `P` and the outcome `out`; the program of the
EXP evaluator computes `valKRaw`. -/

/-- A key move `K ↦ K'`: the new key lies in `X` and on its own run, and every string of the old key
that is on the new run is kept (`K' = K` is a pass). -/
def KeyMoveRaw (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (K K' : Finset BitString) : Prop :=
  K' ⊆ X ∧ K' ⊆ P K' ∧ K ∩ P K' ⊆ K'

instance (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (K K' : Finset BitString) :
    Decidable (KeyMoveRaw X P K K') := by
  unfold KeyMoveRaw; infer_instance

/-- **Key moves without enumerating the possible queries**: when the strings in play
are `U \ Y` and the runs lie in `U`, a key move is decided by the run of the new key, `Y` and list
operations. -/
theorem keyMoveRaw_sdiff_iff {U Y : Finset BitString} {P : Finset BitString → Finset BitString}
    (hP : ∀ S, P S ⊆ U) {K K' : Finset BitString} :
    KeyMoveRaw (U \ Y) P K K' ↔ K' ⊆ P K' ∧ Disjoint K' Y ∧ K ∩ P K' ⊆ K' := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, Finset.disjoint_left.2 fun z hz hzY => (Finset.mem_sdiff.1 (h1 hz)).2 hzY, h3⟩
  · rintro ⟨h2, hY, h3⟩
    exact ⟨fun z hz => Finset.mem_sdiff.2 ⟨hP K' (h2 hz), Finset.disjoint_left.1 hY hz⟩, h2, h3⟩

/-- YES safe at the key `K`, NO to move, scores `y / 2 ^ N` (YES) and `n / 2 ^ N` (NO), fuel `f`:
the outcome is `true`, and every non-passing key move `K'` of NO within its budget has a key reply
`R` of YES (possibly a pass) within its budget after which YES is again safe. -/
def yesKRaw (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool)
    (c : BitString → ℕ) (E : ℕ) : ℕ → Finset BitString → ℕ → ℕ → Bool
  | 0, K, _, _ => out K
  | f + 1, K, y, n => out K && decide (∀ K' ∈ X.powerset, KeyMoveRaw X P K K' → ¬ K' ⊆ K →
      n + costN c K K' ≤ E → ∃ R ∈ X.powerset, KeyMoveRaw X P K' R ∧ y + costN c K' R ≤ E ∧
        yesKRaw X P out c E f R (y + costN c K' R) (n + costN c K K') = true)

/-- The value of the key game: YES has a first key move `K₁` (`K₁ = ∅` is a pass) within its
budget to a key position safe for YES. -/
def valKRaw (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool)
    (c : BitString → ℕ) (E F : ℕ) : Bool :=
  decide (∃ K₁ ∈ X.powerset, KeyMoveRaw X P ∅ K₁ ∧ costN c ∅ K₁ ≤ E ∧
    yesKRaw X P out c E F K₁ (costN c ∅ K₁) 0 = true)

/-! ### The address structure -/

/-- The abstract interface between the machine and the game.  `U`: the possible
queries; `X ⊆ U`: the strings in play; `base w`: the answer to `w` while unflipped; `P S`: the
strings asked along the run of the position `S`; `out S`: the outcome of `S`; `addr z`: the answer
history leading to the query `z`.  `agree`: the run and the outcome depend only on the flips on the
run; `mem_P`: `z` is on the run iff its address is followed; `addr_sub`: addresses are
prefix-closed. -/
structure PathData where
  /-- The possible queries. -/
  U : Finset BitString
  /-- The strings in play. -/
  X : Finset BitString
  /-- The answer to an unflipped string. -/
  base : BitString → Bool
  /-- The strings asked along the run of a position. -/
  P : Finset BitString → Finset BitString
  /-- The outcome of a position. -/
  out : Finset BitString → Bool
  /-- The answer history leading to a query. -/
  addr : BitString → Finset (BitString × Bool)
  X_sub : X ⊆ U
  P_sub : ∀ S, P S ⊆ U
  agree : ∀ S₁ S₂ : Finset BitString, (∀ z ∈ P S₁, (z ∈ S₁ ↔ z ∈ S₂)) →
    P S₂ = P S₁ ∧ out S₂ = out S₁
  mem_P : ∀ z ∈ U, ∀ S : Finset BitString,
    z ∈ P S ↔ ∀ p ∈ addr z, (base p.1 && !decide (p.1 ∈ S)) = p.2
  addr_sub : ∀ z ∈ U, ∀ p ∈ addr z, p.1 ∈ U ∧ addr p.1 ⊆ addr z

namespace PathData

variable (D : PathData)

/-- Negated outcome: NO's view of the same game. -/
def dual : PathData :=
  { D with
    out := fun S => !D.out S
    agree := fun S₁ S₂ h => ⟨(D.agree S₁ S₂ h).1, congrArg (fun b => !b) (D.agree S₁ S₂ h).2⟩ }

/-- The dual game has the same possible queries `U` as `D`. -/
@[simp] theorem dual_U : D.dual.U = D.U := rfl
/-- The dual keeps the strings in play `X`. -/@[simp] theorem dual_X : D.dual.X = D.X := rfl
/-- The dual keeps the answers `base`. -/@[simp] theorem dual_base : D.dual.base = D.base := rfl
/-- The dual keeps the run map `P`. -/@[simp] theorem dual_P : D.dual.P = D.P := rfl
/-- The dual keeps the addresses `addr`. -/@[simp] theorem dual_addr : D.dual.addr = D.addr := rfl
/-- The dual outcome of a position is the negation of its outcome in `D`. -/theorem dual_out
    (S : Finset BitString) : D.dual.out S = !D.out S := rfl

/-- The key of a position: the flipped strings on its run. -/
def key (S : Finset BitString) : Finset BitString := S ∩ D.P S

/-- `z` is dead w.r.t. the key `K`: an ancestor answered "yes" in `z`'s history is permanently
"no" (non-random, or flipped on the run). -/
def Killed (K : Finset BitString) (z : BitString) : Prop :=
  ∃ w, (w, true) ∈ D.addr z ∧ (D.base w = false ∨ w ∈ K)

/-- A position without pending pre-flips: every off-run flipped string is dead. -/
def Tight (S : Finset BitString) : Prop := S ⊆ D.X ∧ ∀ z ∈ S, z ∉ D.P S → D.Killed (D.key S) z

/-- Path-restricted move: every newly flipped string is on the run after the move. -/
def JMove (S S' : Finset BitString) : Prop := S ⊆ S' ∧ S' ⊆ D.X ∧ S' \ S ⊆ D.P S'

/-- The same move seen on keys (`K' = K` is a pass). -/
def KeyMove (K K' : Finset BitString) : Prop := KeyMoveRaw D.X D.P K K'

/-- YES safe at the key `K`, NO to move, scores `y` (YES) and `n` (NO) as numerators, fuel `f`. -/
def yesK (c : BitString → ℕ) (E : ℕ) : ℕ → Finset BitString → ℕ → ℕ → Bool :=
  yesKRaw D.X D.P D.out c E

/-- NO safe at the key `K`, YES to move. -/
def noK (c : BitString → ℕ) (E : ℕ) (f : ℕ) (K : Finset BitString) (y n : ℕ) : Bool :=
  D.dual.yesK c E f K n y

/-- The value of the key game. -/
def valK (c : BitString → ℕ) (E F : ℕ) : Bool := valKRaw D.X D.P D.out c E F

/-- A key move restricts the new key to the strings in play and its own run, and preserves
elements of the old key that lie on the new run. -/
theorem keyMove_iff (K K' : Finset BitString) :
    D.KeyMove K K' ↔ K' ⊆ D.X ∧ K' ⊆ D.P K' ∧ K ∩ D.P K' ⊆ K' := Iff.rfl

/-- A string belongs to the key of a position if and only if it is in the position and on
its run. -/
theorem mem_key {S : Finset BitString} {z : BitString} : z ∈ D.key S ↔ z ∈ S ∧ z ∈ D.P S :=
  Finset.mem_inter

/-- The key of a position is a subset of the position. -/
theorem key_subset (S : Finset BitString) : D.key S ⊆ S := Finset.inter_subset_left

/-- The key of a position is a subset of its run. -/
theorem key_subset_P (S : Finset BitString) : D.key S ⊆ D.P S := Finset.inter_subset_right

/-- The key of the empty position is empty. -/
theorem key_empty : D.key ∅ = ∅ := Finset.empty_inter _

/-- The state of the key game for YES at fuel zero is determined by the outcome of the
key position. -/
theorem yesK_zero (c : BitString → ℕ) (E : ℕ) (K : Finset BitString) (y n : ℕ) :
    D.yesK c E 0 K y n = D.out K := rfl

/-- The state of the key game for YES at positive fuel evaluates to true if and only if the
current outcome is true and every non-passing key move by NO has a valid responding key move
by YES. -/
theorem yesK_succ (c : BitString → ℕ) (E f : ℕ) (K : Finset BitString) (y n : ℕ) :
    D.yesK c E (f + 1) K y n = true ↔ D.out K = true ∧
      ∀ K' ∈ D.X.powerset, D.KeyMove K K' → ¬ K' ⊆ K → n + costN c K K' ≤ E →
        ∃ R ∈ D.X.powerset, D.KeyMove K' R ∧ y + costN c K' R ≤ E ∧
          D.yesK c E f R (y + costN c K' R) (n + costN c K K') = true := by
  change yesKRaw D.X D.P D.out c E (f + 1) K y n = true ↔ _
  simp only [yesKRaw, Bool.and_eq_true, decide_eq_true_eq]
  rfl

/-- If YES is safe in the key game at a position, the outcome at that position must be
true. -/
theorem out_of_yesK {c : BitString → ℕ} {E f : ℕ} {K : Finset BitString} {y n : ℕ}
    (h : D.yesK c E f K y n = true) : D.out K = true := by
  cases f with
  | zero => exact h
  | succ f => exact ((D.yesK_succ c E f K y n).1 h).1

/-- The value of the key game evaluates to true if and only if there is a valid initial key
move for YES that reaches a position safe for YES. -/
theorem valK_iff (c : BitString → ℕ) (E F : ℕ) :
    D.valK c E F = true ↔ ∃ K₁ ∈ D.X.powerset, D.KeyMove ∅ K₁ ∧ costN c ∅ K₁ ≤ E ∧
      D.yesK c E F K₁ (costN c ∅ K₁) 0 = true := by
  change valKRaw D.X D.P D.out c E F = true ↔ _
  simp only [valKRaw, decide_eq_true_eq]
  rfl

/-- `valK` only uses `X`, `P`, `out`. -/
theorem valK_eq_valKRaw (c : BitString → ℕ) (E F : ℕ) :
    D.valK c E F = valKRaw D.X D.P D.out c E F := rfl

/-- The answer to a string under a set of flips is true if and only if its base answer is
true and it is not flipped. -/
theorem ans_eq_true_iff {S : Finset BitString} {w : BitString} :
    (D.base w && !decide (w ∈ S)) = true ↔ D.base w = true ∧ w ∉ S := by
  cases D.base w <;> simp

/-! ### Structural lemmas (L0–L10) -/

/-- **L0.** -/
theorem agree_of_sub {S₁ S₂ : Finset BitString} (h12 : S₁ ⊆ S₂)
    (h : ∀ z ∈ D.P S₁, z ∈ S₂ → z ∈ S₁) : D.P S₂ = D.P S₁ ∧ D.out S₂ = D.out S₁ :=
  D.agree S₁ S₂ fun z hz => ⟨fun h1 => h12 h1, h z hz⟩

/-- **L1.** -/
theorem P_key (S : Finset BitString) : D.P (D.key S) = D.P S ∧ D.out (D.key S) = D.out S :=
  D.agree S (D.key S) fun _ hz =>
    ⟨fun h => Finset.mem_inter.2 ⟨h, hz⟩, fun h => (Finset.mem_inter.1 h).1⟩

/-- **L1** (idempotence). -/
theorem key_key (S : Finset BitString) : D.key (D.key S) = D.key S := by
  change D.key S ∩ D.P (D.key S) = D.key S
  rw [(D.P_key S).1]
  exact Finset.inter_eq_left.2 (D.key_subset_P S)

/-- **L2.** -/
theorem mem_P_of_mem_addr {z : BitString} {T : Finset BitString} {p : BitString × Bool}
    (hz : z ∈ D.U) (hzT : z ∈ D.P T) (hp : p ∈ D.addr z) : p.1 ∈ D.P T := by
  obtain ⟨hpU, hsub⟩ := D.addr_sub z hz p hp
  rw [D.mem_P _ hpU]
  intro q hq
  exact (D.mem_P z hz T).1 hzT q (hsub hq)

/-- **L3.** A string killed by `K` is not on the run of any position keeping the on-run strings
of `K`. -/
theorem not_mem_P_of_killed {K T : Finset BitString} {z : BitString} (hk : D.Killed K z)
    (hz : z ∈ D.U) (hKT : K ∩ D.P T ⊆ T) : z ∉ D.P T := by
  intro hzT
  obtain ⟨w, hw, hw'⟩ := hk
  obtain ⟨hb, hwT⟩ := D.ans_eq_true_iff.1 ((D.mem_P z hz T).1 hzT (w, true) hw)
  rcases hw' with hw' | hw'
  · rw [hb] at hw'; exact Bool.noConfusion hw'
  · exact hwT (hKT (Finset.mem_inter.2 ⟨hw', D.mem_P_of_mem_addr hz hzT hw⟩))

/-- **L4.** A string leaving the run under a monotone move does so because an ancestor with
address answer "yes" was flipped by the move. -/
theorem killed_of_leave {S S' : Finset BitString} {z : BitString} (hSS' : S ⊆ S') (hz : z ∈ D.U)
    (hzS : z ∈ D.P S) (hzS' : z ∉ D.P S') :
    ∃ w, (w, true) ∈ D.addr z ∧ D.base w = true ∧ w ∈ S' \ S := by
  have h1 := (D.mem_P z hz S).1 hzS
  have h2 : ∃ p ∈ D.addr z, (D.base p.1 && !decide (p.1 ∈ S')) ≠ p.2 := by
    by_contra hcon
    push Not at hcon
    exact hzS' ((D.mem_P z hz S').2 hcon)
  obtain ⟨⟨w, b⟩, hp, hne⟩ := h2
  have hb := h1 ⟨w, b⟩ hp
  simp only at hb hne
  by_cases hwS : w ∈ S
  · exfalso; apply hne; rw [← hb]; simp [hwS, hSS' hwS]
  · have hbase : D.base w = true := by
      cases hbw : D.base w
      · exfalso; apply hne; rw [← hb]; simp [hbw]
      · rfl
    have hbt : b = true := by rw [← hb, hbase]; simp [hwS]
    subst hbt
    have hwS' : w ∈ S' := by
      by_contra hwS'
      apply hne; rw [hbase]; simp [hwS']
    exact ⟨w, hp, hbase, Finset.mem_sdiff.2 ⟨hwS', hwS⟩⟩

/-- **L5.** Path-restricted moves keep positions tight. -/
theorem tight_jmove {S S' : Finset BitString} (hT : D.Tight S) (hJ : D.JMove S S') :
    D.Tight S' := by
  obtain ⟨hSX, hk⟩ := hT
  obtain ⟨hSS', hS'X, hnew⟩ := hJ
  refine ⟨hS'X, fun z hz hzP => ?_⟩
  have hzS : z ∈ S := by
    by_contra hzS
    exact hzP (hnew (Finset.mem_sdiff.2 ⟨hz, hzS⟩))
  have hzU : z ∈ D.U := D.X_sub (hSX hzS)
  have leave : ∀ v ∈ D.U, v ∈ D.P S → v ∉ D.P S' →
      ∃ u, (u, true) ∈ D.addr v ∧ u ∈ D.key S' := by
    intro v hvU hvS hvS'
    obtain ⟨u, hu, -, huS⟩ := D.killed_of_leave hSS' hvU hvS hvS'
    exact ⟨u, hu, Finset.mem_inter.2 ⟨(Finset.mem_sdiff.1 huS).1, hnew huS⟩⟩
  by_cases hzPS : z ∈ D.P S
  · obtain ⟨u, hu, huK⟩ := leave z hzU hzPS hzP
    exact ⟨u, hu, Or.inr huK⟩
  · obtain ⟨w, hw, hw'⟩ := hk z hzS hzPS
    rcases hw' with hb | hwK
    · exact ⟨w, hw, Or.inl hb⟩
    · obtain ⟨hwS, hwPS⟩ := Finset.mem_inter.1 hwK
      by_cases hwPS' : w ∈ D.P S'
      · exact ⟨w, hw, Or.inr (Finset.mem_inter.2 ⟨hSS' hwS, hwPS'⟩)⟩
      · have hwU : w ∈ D.U := (D.addr_sub z hzU (w, true) hw).1
        obtain ⟨u, hu, huK⟩ := leave w hwU hwPS hwPS'
        exact ⟨u, (D.addr_sub z hzU (w, true) hw).2 hu, Or.inr huK⟩

/-- **L6.** A key move can be realised from any tight position, whatever its abandoned part. -/
theorem tight_realize {S K' : Finset BitString} (hT : D.Tight S) (hK : D.KeyMove (D.key S) K') :
    D.JMove S (S ∪ K') ∧ D.key (S ∪ K') = K' ∧ D.P (S ∪ K') = D.P K' ∧
      D.out (S ∪ K') = D.out K' ∧ K' \ S = K' \ D.key S := by
  obtain ⟨hSX, hk⟩ := hT
  obtain ⟨hK'X, hK'P, hKK'⟩ := hK
  have h1 : S ∩ D.P K' ⊆ K' := by
    intro z hz
    obtain ⟨hzS, hzP⟩ := Finset.mem_inter.1 hz
    by_cases hzPS : z ∈ D.P S
    · exact hKK' (Finset.mem_inter.2 ⟨Finset.mem_inter.2 ⟨hzS, hzPS⟩, hzP⟩)
    · exact absurd hzP (D.not_mem_P_of_killed (hk z hzS hzPS) (D.X_sub (hSX hzS)) hKK')
  have h2 := D.agree K' (S ∪ K') fun z hz => ⟨fun h => Finset.mem_union_right _ h, fun h => by
    rcases Finset.mem_union.1 h with h | h
    · exact h1 (Finset.mem_inter.2 ⟨h, hz⟩)
    · exact h⟩
  refine ⟨⟨Finset.subset_union_left, Finset.union_subset hSX hK'X, ?_⟩, ?_, h2.1, h2.2, ?_⟩
  · rw [h2.1]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.1 hz
    rcases Finset.mem_union.1 hz1 with h | h
    · exact absurd h hz2
    · exact hK'P h
  · change (S ∪ K') ∩ D.P (S ∪ K') = K'
    rw [h2.1]
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hz⟩
      · exact h1 (Finset.mem_inter.2 ⟨h, hz⟩)
      · exact h
    · intro h; exact ⟨Or.inr h, hK'P h⟩
  · ext z
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨h, hzS⟩; exact ⟨h, fun hk' => hzS (D.key_subset S hk')⟩
    · rintro ⟨h, hzK⟩
      refine ⟨h, fun hzS => ?_⟩
      have hzPS : z ∉ D.P S := fun hp => hzK (Finset.mem_inter.2 ⟨hzS, hp⟩)
      exact D.not_mem_P_of_killed (hk z hzS hzPS) (D.X_sub (hSX hzS)) hKK' (hK'P h)

/-- **L6** (tightness of the realisation). -/
theorem tight_union {S K' : Finset BitString} (hT : D.Tight S) (hK : D.KeyMove (D.key S) K') :
    D.Tight (S ∪ K') :=
  D.tight_jmove hT (D.tight_realize hT hK).1

/-- The empty position is tight. -/
theorem tight_empty : D.Tight ∅ := ⟨Finset.empty_subset _, fun z hz => by simp at hz⟩

/-- A set of strings in play lying on its own run (e.g. a key reached by a key move) is tight. -/
theorem tight_of_subset_P {K : Finset BitString} (hKX : K ⊆ D.X) (hKP : K ⊆ D.P K) : D.Tight K :=
  ⟨hKX, fun _ hz hzP => absurd (hKP hz) hzP⟩

/-- A set lying on its own run is its own key. -/
theorem key_eq_self {K : Finset BitString} (hKP : K ⊆ D.P K) : D.key K = K :=
  Finset.inter_eq_left.2 hKP

/-- A key lies on its own run. -/
theorem key_subset_P_key (S : Finset BitString) : D.key S ⊆ D.P (D.key S) := by
  rw [(D.P_key S).1]; exact D.key_subset_P S

/-- A key pass is exactly `K' = K`: a key move from a set on its own run to a subset of it is the
identity. -/
theorem keyMove_subset_iff_eq {K K' : Finset BitString} (hKP : K ⊆ D.P K) (hK : D.KeyMove K K') :
    K' ⊆ K ↔ K' = K := by
  refine ⟨fun h => ?_, fun h => h ▸ Finset.Subset.refl _⟩
  obtain ⟨-, -, hKK'⟩ := hK
  have hP : D.P K = D.P K' := (D.agree K' K fun z hz =>
    ⟨fun hz' => h hz', fun hzK => hKK' (Finset.mem_inter.2 ⟨hzK, hz⟩)⟩).1
  refine Finset.Subset.antisymm h fun z hz => hKK' (Finset.mem_inter.2 ⟨hz, ?_⟩)
  rw [← hP]; exact hKP hz

/-- **L7.** -/
theorem jmove_keyMove {S S' : Finset BitString} (hJ : D.JMove S S') :
    D.KeyMove (D.key S) (D.key S') ∧ S' = S ∪ D.key S' := by
  obtain ⟨hSS', hS'X, hnew⟩ := hJ
  have hP := (D.P_key S').1
  refine ⟨⟨(D.key_subset S').trans hS'X, ?_, ?_⟩, ?_⟩
  · rw [hP]; exact D.key_subset_P S'
  · rw [hP]
    intro z hz
    obtain ⟨hzK, hzP⟩ := Finset.mem_inter.1 hz
    exact Finset.mem_inter.2 ⟨hSS' (D.key_subset S hzK), hzP⟩
  · ext z
    simp only [Finset.mem_union]
    constructor
    · intro hz
      by_cases hzS : z ∈ S
      · exact Or.inl hzS
      · exact Or.inr (Finset.mem_inter.2 ⟨hz, hnew (Finset.mem_sdiff.2 ⟨hz, hzS⟩)⟩)
    · rintro (h | h)
      · exact hSS' h
      · exact D.key_subset S' h

/-- **L8.** Projection of a move onto the run of its target. -/
theorem proj {S R : Finset BitString} (hSR : S ⊆ R) (hRX : R ⊆ D.X) :
    D.JMove S (S ∪ D.key R) ∧ D.P (S ∪ D.key R) = D.P R ∧ D.out (S ∪ D.key R) = D.out R ∧
      ∀ z ∈ D.P R, z ∈ R → z ∈ S ∪ D.key R := by
  have hJR : S ∪ D.key R ⊆ R := Finset.union_subset hSR (D.key_subset R)
  have hoff : ∀ z ∈ D.P R, z ∈ R → z ∈ S ∪ D.key R := fun z hz hzR =>
    Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hzR, hz⟩)
  have h2 := D.agree R (S ∪ D.key R) fun z hz => ⟨hoff z hz, fun h => hJR h⟩
  refine ⟨⟨Finset.subset_union_left, hJR.trans hRX, ?_⟩, h2.1, h2.2, hoff⟩
  rw [h2.1]
  intro z hz
  obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.1 hz
  rcases Finset.mem_union.1 hz1 with h | h
  · exact absurd h hz2
  · exact D.key_subset_P R h

/-- **L9.** A real pass is a key pass. -/
theorem pass_iff {S K' : Finset BitString} (hT : D.Tight S) (hK : D.KeyMove (D.key S) K') :
    S ∪ K' = S ↔ K' ⊆ D.key S := by
  have h5 := (D.tight_realize hT hK).2.2.2.2
  constructor
  · intro h z hz
    by_contra hzK
    have hz' : z ∈ K' \ D.key S := Finset.mem_sdiff.2 ⟨hz, hzK⟩
    rw [← h5] at hz'
    have hzS : z ∈ S := by rw [← h]; exact Finset.mem_union_right _ hz
    exact (Finset.mem_sdiff.1 hz').2 hzS
  · intro h
    exact Finset.union_eq_left.2 (h.trans (D.key_subset S))

/-- **L10.** A non-passing key move of NO stays non-passing through YES's off-run pre-flips. -/
theorem nonpass_of_offrun {S K' A : Finset BitString} (hT : D.Tight S) (hK : D.KeyMove (D.key S) K')
    (hne : ¬ K' ⊆ D.key S) (hA : ∀ z ∈ D.P S, z ∈ A → z ∈ S) : ¬ K' ⊆ S ∪ A := by
  intro hsub
  have h5 := (D.tight_realize hT hK).2.2.2.2
  obtain ⟨-, hK'P, hKK'⟩ := hK
  have hout : ∀ z, z ∈ K' → z ∉ D.key S → z ∉ S := by
    intro z hz hzK hzS
    have hz' : z ∈ K' \ D.key S := Finset.mem_sdiff.2 ⟨hz, hzK⟩
    rw [← h5] at hz'
    exact (Finset.mem_sdiff.1 hz').2 hzS
  have hA' : ∀ z, z ∈ K' → z ∉ D.key S → z ∈ A := by
    intro z hz hzK
    rcases Finset.mem_union.1 (hsub hz) with h | h
    · exact absurd h (hout z hz hzK)
    · exact h
  have hPK' : D.P (D.key S ∪ K') = D.P K' :=
    (D.agree K' (D.key S ∪ K') fun z hz => ⟨fun h => Finset.mem_union_right _ h, fun h => by
      rcases Finset.mem_union.1 h with h | h
      · exact hKK' (Finset.mem_inter.2 ⟨h, hz⟩)
      · exact h⟩).1
  have hPS : D.P (D.key S ∪ K') = D.P S := by
    have h := (D.agree (D.key S) (D.key S ∪ K') fun z hz =>
      ⟨fun h => Finset.mem_union_left _ h, fun h => by
        rcases Finset.mem_union.1 h with h | h
        · exact h
        · by_contra hzK
          rw [(D.P_key S).1] at hz
          exact hout z h hzK (hA z hz (hA' z h hzK))⟩).1
    rw [h, (D.P_key S).1]
  apply hne
  intro z hz
  by_contra hzK
  have hzP : z ∈ D.P S := by rw [← hPS, hPK']; exact hK'P hz
  exact hout z hz hzK (hA z hzP (hA' z hz hzK))

/-- **L11** (keys and costs): along a path-restricted move from a tight position, the key move
costs the same as the move. -/
theorem costN_key_eq (c : BitString → ℕ) {S S'' : Finset BitString} (hT : D.Tight S)
    (hJ : D.JMove S S'') :
    costN c (D.key S) (D.key S'') = costN c S S'' := by
  obtain ⟨hKM, heq⟩ := D.jmove_keyMove hJ
  have h5 := (D.tight_realize hT hKM).2.2.2.2
  have hsd : S'' \ S = D.key S'' \ D.key S := by
    rw [← h5]
    calc S'' \ S = (S ∪ D.key S'') \ S := by rw [← heq]
      _ = D.key S'' \ S := Finset.union_sdiff_left _ _
  unfold costN
  rw [hsd]

/-! ### The YES/NO symmetry of the real game -/

/-- The flip cost of a string in the dual game is the same as in the original game. -/
theorem flipCost_dual (d : GameData) (z : BitString) : flipCost d.dual z = flipCost d z := rfl

/-- The transition cost between positions in the dual game is the same as in the original
game. -/
theorem moveCost_dual (d : GameData) (S S' : Finset BitString) :
    moveCost d.dual S S' = moveCost d S S' := rfl

/-- NO safe (YES to move) in `d` is YES safe (NO to move) in the dual game with the scores
exchanged. -/
theorem safeNo_iff_dual_swap (d : GameData) (S : Finset BitString) (y n : ℝ) :
    SafeNo d ⟨S, y, n, true⟩ ↔ SafeYes d.dual ⟨S, n, y, false⟩ :=
  (safeNo_iff_safeYes_dual d _).trans (safeYes_swap d.dual S n y false)

/-! ### Postponement: real safety implies key safety -/

/-- **Postponement**, for every fuel. The real position is `S ∪ A`, where `S` is a tight (virtual)
position and `A` holds YES's pending pre-flips: off the run, and really paid for (`yr` includes
them).  NO's real payments are at most its virtual ones.  If YES is safe at the real position,
then the key recursion declares YES safe at the key of `S`, with any fuel (a smaller fuel only
weakens `yesK`). -/
theorem yesK_of_safeYes_anyFuel (d : GameData) (N : ℕ) (c : BitString → ℕ) (E : ℕ)
    (hX : d.X = D.X) (hout : d.outcome = D.out)
    (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N) (hε : d.ε = (E : ℝ) / 2 ^ N) :
    ∀ (f : ℕ) (S A : Finset BitString) (y n : ℕ) (yr nr : ℝ),
      D.Tight S → A ⊆ D.X → (∀ z ∈ D.P S, z ∈ A → z ∈ S) →
      ((y + costN c S (S ∪ A) : ℕ) : ℝ) / 2 ^ N ≤ yr → nr ≤ (n : ℝ) / 2 ^ N →
      SafeYes d ⟨S ∪ A, yr, nr, false⟩ → D.yesK c E f (D.key S) y n = true := by
  have hmc : ∀ {S S' : Finset BitString}, S' ⊆ D.X → moveCost d S S' = (costN c S S' : ℝ) / 2 ^ N :=
    fun hS' => moveCost_eq_costN d N c hc (hX ▸ hS')
  have houtK : ∀ (S A : Finset BitString) (yr nr : ℝ), (∀ z ∈ D.P S, z ∈ A → z ∈ S) →
      SafeYes d ⟨S ∪ A, yr, nr, false⟩ → D.out (D.key S) = true := by
    intro S A yr nr hA hs
    have hag := D.agree_of_sub (S₁ := S) (S₂ := S ∪ A) Finset.subset_union_left
      (fun z hz hzSA => by
        rcases Finset.mem_union.1 hzSA with h | h
        · exact h
        · exact hA z hz h)
    rw [(D.P_key S).2, ← hag.2, ← hout]
    exact hs.outcome
  intro f
  induction f with
  | zero =>
    intro S A y n yr nr _ _ hA _ _ hs
    exact houtK S A yr nr hA hs
  | succ f ih =>
    intro S A y n yr nr hT hAX hA hy hn hs
    rw [D.yesK_succ]
    refine ⟨houtK S A yr nr hA hs, fun K' _ hK hne hcost => ?_⟩
    have hSX : S ⊆ D.X := hT.1
    have hK'X : K' ⊆ D.X := hK.1
    obtain ⟨hJ, hkey', -, -, h5⟩ := D.tight_realize hT hK
    have hT' : D.Tight (S ∪ K') := D.tight_jmove hT hJ
    have hSrX : S ∪ A ⊆ D.X := Finset.union_subset hSX hAX
    have hSr'X : S ∪ A ∪ K' ⊆ D.X := Finset.union_subset hSrX hK'X
    -- NO's real move `S ∪ A ↦ S ∪ A ∪ K'` is not more expensive than the key move
    have hcostNO : costN c (S ∪ A) (S ∪ A ∪ K') ≤ costN c (D.key S) K' := by
      apply costN_le_of_subset
      intro z hz
      rw [← h5]
      obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.1 hz
      refine Finset.mem_sdiff.2 ⟨?_, fun h => hz2 (Finset.mem_union_left _ h)⟩
      rcases Finset.mem_union.1 hz1 with h | h
      · exact absurd h hz2
      · exact h
    have hNOle : nr + moveCost d (S ∪ A) (S ∪ A ∪ K') ≤
        ((n + costN c (D.key S) K' : ℕ) : ℝ) / 2 ^ N := by
      rw [hmc hSr'X, ← natCast_div_two_pow_add]
      have h1 : (costN c (S ∪ A) (S ∪ A ∪ K') : ℝ) / 2 ^ N ≤ (costN c (D.key S) K' : ℝ) / 2 ^ N :=
        (natCast_div_two_pow_le_iff _ _ _).2 hcostNO
      linarith
    have hLno : LegalMove d ⟨S ∪ A, yr, nr, false⟩ (S ∪ A ∪ K') := by
      rw [legalMove_noTurn_iff]
      refine ⟨Finset.subset_union_left, hX ▸ hSr'X, ?_⟩
      rw [hε]
      have h2 : ((n + costN c (D.key S) K' : ℕ) : ℝ) / 2 ^ N ≤ (E : ℝ) / 2 ^ N :=
        (natCast_div_two_pow_le_iff _ _ _).2 hcost
      linarith
    -- the real move is not a pass (L10)
    have hnp : S ∪ A ∪ K' ≠ S ∪ A := by
      intro h
      apply D.nonpass_of_offrun hT hK hne hA
      intro z hz
      rw [← h]; exact Finset.mem_union_right _ hz
    -- YES's real reply
    obtain ⟨-, hrep⟩ := (safeYes_iff_eval d _).1 hs
    obtain ⟨R, hLR, hsR⟩ := hrep _ hLno hnp
    rw [applyMove_noTurn] at hLR hsR
    rw [applyMove_yesTurn] at hsR
    rw [legalMove_yesTurn_iff] at hLR
    obtain ⟨hSr'R, hRX', hRc⟩ := hLR
    have hRX : R ⊆ D.X := hX ▸ hRX'
    have hS'R : S ∪ K' ⊆ R := fun z hz => hSr'R (by
      rcases Finset.mem_union.1 hz with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_right _ h)
    -- its projection onto its own run (L8) and the key reply (L7)
    obtain ⟨hJ2, hP2, -, hoff2⟩ := D.proj hS'R hRX
    have hT'' : D.Tight (S ∪ K' ∪ D.key R) := D.tight_jmove hT' hJ2
    have hKM2 := (D.jmove_keyMove hJ2).1
    rw [hkey'] at hKM2
    have hcostY : costN c K' (D.key (S ∪ K' ∪ D.key R)) =
        costN c (S ∪ K') (S ∪ K' ∪ D.key R) := by
      rw [← D.costN_key_eq c hT' hJ2, hkey']
    have hS''R : S ∪ K' ∪ D.key R ⊆ R := Finset.union_subset hS'R (D.key_subset R)
    have hS''X : S ∪ K' ∪ D.key R ⊆ D.X := hS''R.trans hRX
    have hRu : S ∪ K' ∪ D.key R ∪ (R \ (S ∪ K' ∪ D.key R)) = R :=
      Finset.union_sdiff_of_subset hS''R
    -- scores
    have hnat : y + costN c K' (D.key (S ∪ K' ∪ D.key R)) +
        costN c (S ∪ K' ∪ D.key R) (S ∪ K' ∪ D.key R ∪ (R \ (S ∪ K' ∪ D.key R))) ≤
          (y + costN c S (S ∪ A)) + costN c (S ∪ A ∪ K') R := by
      rw [hcostY, hRu, add_assoc, ← costN_add c Finset.subset_union_left hS''R, costN_union]
      have hsub : R \ (S ∪ K') ⊆ (R \ (S ∪ A ∪ K')) ∪ (A \ S) := by
        intro z hz
        obtain ⟨hzR, hzS⟩ := Finset.mem_sdiff.1 hz
        rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
        by_cases hzA : z ∈ A
        · right; exact ⟨hzA, fun h => hzS (Finset.mem_union_left _ h)⟩
        · left
          refine ⟨hzR, fun h => ?_⟩
          rcases Finset.mem_union.1 h with h | h
          · rcases Finset.mem_union.1 h with h | h
            · exact hzS (Finset.mem_union_left _ h)
            · exact hzA h
          · exact hzS (Finset.mem_union_right _ h)
      have := sum_le_of_subset_union c hsub
      unfold costN
      omega
    have hYreal : ((y + costN c K' (D.key (S ∪ K' ∪ D.key R)) +
        costN c (S ∪ K' ∪ D.key R) (S ∪ K' ∪ D.key R ∪ (R \ (S ∪ K' ∪ D.key R))) : ℕ) : ℝ) /
          2 ^ N ≤ yr + moveCost d (S ∪ A ∪ K') R := by
      rw [hmc hRX]
      have h1 := (natCast_div_two_pow_le_iff _ _ N).2 hnat
      have h2 : (((y + costN c S (S ∪ A)) + costN c (S ∪ A ∪ K') R : ℕ) : ℝ) / 2 ^ N =
          ((y + costN c S (S ∪ A) : ℕ) : ℝ) / 2 ^ N + (costN c (S ∪ A ∪ K') R : ℝ) / 2 ^ N :=
        (natCast_div_two_pow_add _ _ _).symm
      linarith
    have hYle : y + costN c K' (D.key (S ∪ K' ∪ D.key R)) ≤ E := by
      have h1 : ((y + costN c K' (D.key (S ∪ K' ∪ D.key R)) +
          costN c (S ∪ K' ∪ D.key R) (S ∪ K' ∪ D.key R ∪ (R \ (S ∪ K' ∪ D.key R))) : ℕ) : ℝ) /
            2 ^ N ≤ (E : ℝ) / 2 ^ N := by
        rw [← hε]; linarith
      have h2 := (natCast_div_two_pow_le_iff _ _ _).1 h1
      omega
    have hoff : ∀ z ∈ D.P (S ∪ K' ∪ D.key R), z ∈ R \ (S ∪ K' ∪ D.key R) →
        z ∈ S ∪ K' ∪ D.key R := by
      intro z hz hzA
      rw [hP2] at hz
      exact hoff2 z hz (Finset.mem_sdiff.1 hzA).1
    have hsR' : SafeYes d ⟨S ∪ K' ∪ D.key R ∪ (R \ (S ∪ K' ∪ D.key R)),
        yr + moveCost d (S ∪ A ∪ K') R, nr + moveCost d (S ∪ A) (S ∪ A ∪ K'), false⟩ := by
      rw [hRu]; exact hsR
    exact ⟨D.key (S ∪ K' ∪ D.key R), Finset.mem_powerset.2 ((D.key_subset _).trans hS''X), hKM2,
      hYle, ih (S ∪ K' ∪ D.key R) (R \ (S ∪ K' ∪ D.key R)) _ _ _ _ hT''
        (Finset.sdiff_subset.trans hRX) hoff hYreal hNOle hsR'⟩

/-- **Postponement** (the fuel hypothesis is not needed, see
`yesK_of_safeYes_anyFuel`). -/
theorem yesK_of_safeYes (d : GameData) (N : ℕ) (c : BitString → ℕ) (E : ℕ)
    (hX : d.X = D.X) (hout : d.outcome = D.out)
    (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N) (hε : d.ε = (E : ℝ) / 2 ^ N) :
    ∀ (f : ℕ) (S A : Finset BitString) (y n : ℕ) (yr nr : ℝ),
      D.Tight S → A ⊆ D.X → (D.X \ S).card ≤ f → (∀ z ∈ D.P S, z ∈ A → z ∈ S) →
      ((y + costN c S (S ∪ A) : ℕ) : ℝ) / 2 ^ N ≤ yr → nr ≤ (n : ℝ) / 2 ^ N →
      SafeYes d ⟨S ∪ A, yr, nr, false⟩ → D.yesK c E f (D.key S) y n = true :=
  fun f S A y n yr nr hT hA _ =>
    D.yesK_of_safeYes_anyFuel d N c E hX hout hc hε f S A y n yr nr hT hA

/-- **Postponement for NO** (through the dual game and the swap of the scores): the mirror image
of `yesK_of_safeYes_anyFuel`, with NO's pending pre-flips `A` paid for in `nr`. -/
theorem noK_of_safeNo (d : GameData) (N : ℕ) (c : BitString → ℕ) (E : ℕ)
    (hX : d.X = D.X) (hout : d.outcome = D.out)
    (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N) (hε : d.ε = (E : ℝ) / 2 ^ N)
    (f : ℕ) (S A : Finset BitString) (y n : ℕ) (yr nr : ℝ)
    (hT : D.Tight S) (hA : A ⊆ D.X) (hoff : ∀ z ∈ D.P S, z ∈ A → z ∈ S)
    (hn : ((n + costN c S (S ∪ A) : ℕ) : ℝ) / 2 ^ N ≤ nr) (hy : yr ≤ (y : ℝ) / 2 ^ N)
    (hs : SafeNo d ⟨S ∪ A, yr, nr, true⟩) : D.noK c E f (D.key S) y n = true :=
  D.dual.yesK_of_safeYes_anyFuel d.dual N c E hX
    (by funext S; change (!d.outcome S) = !D.out S; rw [hout]) hc hε f S A n y nr yr hT hA
    hoff hn hy ((safeNo_iff_dual_swap d (S ∪ A) yr nr).1 hs)

/-! ### Exclusivity of the key recursion -/

/-- It is impossible for YES to be safe at a tight position while NO is safe after a key move
from it. -/
theorem yesK_noK_false_aux (c : BitString → ℕ) (E : ℕ) (m : ℕ) :
    ∀ (S K₂ : Finset BitString) (f g y n : ℕ), (D.X \ S).card = m → D.Tight S →
      (D.X \ S).card ≤ f → (D.X \ S).card ≤ g →
      D.KeyMove (D.key S) K₂ → n + costN c (D.key S) K₂ ≤ E →
      D.yesK c E f (D.key S) y n = true →
      D.noK c E g K₂ y (n + costN c (D.key S) K₂) = true → False := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro S K₂ f g y n hm hT hf hg hK hcost hY hN
  have hN' : D.dual.yesK c E g K₂ (n + costN c (D.key S) K₂) y = true := hN
  obtain ⟨hJ, hkey2, -, hout2, -⟩ := D.tight_realize hT hK
  have hT2 : D.Tight (S ∪ K₂) := D.tight_jmove hT hJ
  by_cases hpass : K₂ ⊆ D.key S
  · -- NO passes
    have hSeq : S ∪ K₂ = S := (D.pass_iff hT hK).2 hpass
    have ho1 : D.out (D.key S) = true := D.out_of_yesK hY
    have ho2 : D.dual.out K₂ = true := D.dual.out_of_yesK hN'
    have heq : D.out K₂ = D.out (D.key S) := by rw [← hout2, hSeq, (D.P_key S).2]
    rw [dual_out, heq, ho1] at ho2
    exact absurd ho2 (by decide)
  · have hSX : S ⊆ D.X := hT.1
    have hK₂X : K₂ ⊆ D.X := hK.1
    have hSne : S ∪ K₂ ≠ S := fun h => hpass ((D.pass_iff hT hK).1 h)
    have hS2X : S ∪ K₂ ⊆ D.X := Finset.union_subset hSX hK₂X
    have hlt1 := card_sdiff_lt Finset.subset_union_left hS2X hSne
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨-, hYrep⟩ := (D.yesK_succ c E f' _ y n).1 hY
    obtain ⟨R, hRP, hKMR, hRcost, hYR⟩ :=
      hYrep K₂ (Finset.mem_powerset.2 hK₂X) hK hpass hcost
    have hKMR' : D.KeyMove (D.key (S ∪ K₂)) R := by rw [hkey2]; exact hKMR
    obtain ⟨hJ3, hkey3, -, hout3, -⟩ := D.tight_realize hT2 hKMR'
    have hT3 : D.Tight (S ∪ K₂ ∪ R) := D.tight_jmove hT2 hJ3
    by_cases hpass2 : R ⊆ K₂
    · -- YES passes
      have hS3eq : S ∪ K₂ ∪ R = S ∪ K₂ :=
        (D.pass_iff hT2 hKMR').2 (by rw [hkey2]; exact hpass2)
      have ho1 : D.out R = true := D.out_of_yesK hYR
      have ho2 : D.dual.out K₂ = true := D.dual.out_of_yesK hN'
      have heq : D.out R = D.out K₂ := by rw [← hout3, hS3eq, hout2]
      rw [dual_out, ← heq, ho1] at ho2
      exact absurd ho2 (by decide)
    · have hS3ne : S ∪ K₂ ∪ R ≠ S ∪ K₂ := fun h => hpass2 (by
        have h' := (D.pass_iff hT2 hKMR').1 h
        rwa [hkey2] at h')
      have hRX : R ⊆ D.X := hKMR.1
      have hS3X : S ∪ K₂ ∪ R ⊆ D.X := Finset.union_subset hS2X hRX
      have hlt2 := card_sdiff_lt Finset.subset_union_left hS3X hS3ne
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      obtain ⟨-, hNrep⟩ := (D.dual.yesK_succ c E g' K₂ _ y).1 hN'
      obtain ⟨K₄, -, hKM4, hK4cost, hNK4⟩ := hNrep R hRP hKMR hpass2 hRcost
      refine ih (D.X \ (S ∪ K₂ ∪ R)).card (by omega) (S ∪ K₂ ∪ R) K₄ f' g'
        (y + costN c K₂ R) (n + costN c (D.key S) K₂) rfl hT3 (by omega) (by omega)
        (by rw [hkey3]; exact hKM4) (by rw [hkey3]; exact hK4cost) (by rw [hkey3]; exact hYR) ?_
      rw [hkey3]
      exact hNK4

/-- **Exclusivity of the key recursion**: YES safe at the key of a tight position and NO safe
after a key move of NO from it (with adequate fuels) contradict each other. -/
theorem yesK_noK_false (c : BitString → ℕ) (E : ℕ) :
    ∀ (S K₂ : Finset BitString) (f g y n : ℕ), D.Tight S → (D.X \ S).card ≤ f → (D.X \ S).card ≤ g →
      D.KeyMove (D.key S) K₂ → n + costN c (D.key S) K₂ ≤ E →
      D.yesK c E f (D.key S) y n = true →
      D.noK c E g K₂ y (n + costN c (D.key S) K₂) = true → False :=
  fun S K₂ f g y n => D.yesK_noK_false_aux c E _ S K₂ f g y n rfl

/-! ### The centrepiece -/

/-- **The key recursion computes the value of the game**: for a game whose run has an address
structure `D`, with flip costs `c z / 2 ^ N` on the strings in play and budget `E / 2 ^ N`, and
fuel `F ≥ |X|`. -/
theorem valK_eq_val (d : GameData) (N : ℕ) (c : BitString → ℕ) (E F : ℕ)
    (hX : d.X = D.X) (hout : d.outcome = D.out)
    (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N) (hε : d.ε = (E : ℝ) / 2 ^ N)
    (hF : D.X.card ≤ F) :
    D.valK c E F = val d := by
  have hmc : ∀ {S S' : Finset BitString}, S' ⊆ D.X → moveCost d S S' = (costN c S S' : ℝ) / 2 ^ N :=
    fun hS' => moveCost_eq_costN d N c hc (hX ▸ hS')
  have hcardF : ∀ S : Finset BitString, (D.X \ S).card ≤ F := fun S =>
    (Finset.card_le_card Finset.sdiff_subset).trans hF
  rw [Bool.eq_iff_iff, determined, valK_iff]
  constructor
  · -- `valK = true ⇒ val = true`: determinacy, NO postponement, exclusivity
    rintro ⟨K₁, hK₁P, hKM1, hc1, hY1⟩
    by_contra hnot
    have hNo := noWinsInit_of_not_yesWinsInit d hnot
    have hK₁X : K₁ ⊆ D.X := Finset.mem_powerset.1 hK₁P
    have hL1 : LegalMove d GState.init K₁ := by
      change LegalMove d ⟨∅, 0, 0, true⟩ K₁
      rw [legalMove_yesTurn_iff]
      refine ⟨Finset.empty_subset _, hX ▸ hK₁X, ?_⟩
      rw [hmc hK₁X, hε, zero_add]
      exact (natCast_div_two_pow_le_iff _ _ _).2 hc1
    obtain ⟨S₂, hL2, hs2⟩ := hNo K₁ hL1
    have hinit : applyMove d GState.init K₁ = ⟨K₁, 0 + moveCost d ∅ K₁, 0, false⟩ :=
      applyMove_yesTurn d ∅ K₁ 0 0
    rw [hinit] at hL2 hs2
    rw [applyMove_noTurn] at hs2
    rw [legalMove_noTurn_iff] at hL2
    obtain ⟨hK₁S₂, hS₂X', hc2⟩ := hL2
    have hS₂X : S₂ ⊆ D.X := hX ▸ hS₂X'
    obtain ⟨-, hK₁P', -⟩ := hKM1
    have hT1 : D.Tight K₁ := D.tight_of_subset_P hK₁X hK₁P'
    have hkey1 : D.key K₁ = K₁ := D.key_eq_self hK₁P'
    obtain ⟨hJ, hPJ, -, hoffJ⟩ := D.proj hK₁S₂ hS₂X
    have hTJ : D.Tight (K₁ ∪ D.key S₂) := D.tight_jmove hT1 hJ
    have hJS₂ : K₁ ∪ D.key S₂ ⊆ S₂ := Finset.union_subset hK₁S₂ (D.key_subset S₂)
    have hcJ : costN c K₁ (K₁ ∪ D.key S₂) + costN c (K₁ ∪ D.key S₂) S₂ = costN c K₁ S₂ :=
      (costN_add c Finset.subset_union_left hJS₂).symm
    have hoff : ∀ z ∈ D.P (K₁ ∪ D.key S₂), z ∈ S₂ \ (K₁ ∪ D.key S₂) → z ∈ K₁ ∪ D.key S₂ := by
      intro z hz hzA
      rw [hPJ] at hz
      exact hoffJ z hz (Finset.mem_sdiff.1 hzA).1
    have hn : ((costN c K₁ (K₁ ∪ D.key S₂) +
        costN c (K₁ ∪ D.key S₂) (K₁ ∪ D.key S₂ ∪ (S₂ \ (K₁ ∪ D.key S₂))) : ℕ) : ℝ) / 2 ^ N ≤
          0 + moveCost d K₁ S₂ :=
      le_of_eq (by rw [Finset.union_sdiff_of_subset hJS₂, hcJ, hmc hS₂X, zero_add])
    have hy : 0 + moveCost d ∅ K₁ ≤ ((costN c ∅ K₁ : ℕ) : ℝ) / 2 ^ N :=
      le_of_eq (by rw [hmc hK₁X, zero_add])
    have hs2' : SafeNo d ⟨K₁ ∪ D.key S₂ ∪ (S₂ \ (K₁ ∪ D.key S₂)), 0 + moveCost d ∅ K₁,
        0 + moveCost d K₁ S₂, true⟩ := by
      rw [Finset.union_sdiff_of_subset hJS₂]; exact hs2
    have hpost := D.noK_of_safeNo d N c E hX hout hc hε F (K₁ ∪ D.key S₂)
      (S₂ \ (K₁ ∪ D.key S₂)) (costN c ∅ K₁) (costN c K₁ (K₁ ∪ D.key S₂))
      (0 + moveCost d ∅ K₁) (0 + moveCost d K₁ S₂) hTJ (Finset.sdiff_subset.trans hS₂X)
      hoff hn hy hs2'
    obtain ⟨hKM2, -⟩ := D.jmove_keyMove hJ
    have hcK : costN c K₁ (D.key (K₁ ∪ D.key S₂)) = costN c K₁ (K₁ ∪ D.key S₂) := by
      rw [← D.costN_key_eq c hT1 hJ, hkey1]
    have hcle : costN c K₁ (K₁ ∪ D.key S₂) ≤ E := by
      have h1 : costN c K₁ S₂ ≤ E := by
        rw [hmc hS₂X, hε, zero_add, natCast_div_two_pow_le_iff] at hc2
        exact hc2
      omega
    refine D.yesK_noK_false c E K₁ (D.key (K₁ ∪ D.key S₂)) F F (costN c ∅ K₁) 0 hT1 (hcardF _)
      (hcardF _) hKM2 (by rw [hkey1, hcK]; omega) (by rw [hkey1]; exact hY1) ?_
    rw [hkey1, hcK, zero_add]
    exact hpost
  · -- `val = true ⇒ valK = true`: postponement of YES's first move
    rintro ⟨S₁, hL1, hs1⟩
    have hL1' : LegalMove d ⟨∅, 0, 0, true⟩ S₁ := hL1
    rw [legalMove_yesTurn_iff] at hL1'
    obtain ⟨-, hS₁X', hc1⟩ := hL1'
    have hS₁X : S₁ ⊆ D.X := hX ▸ hS₁X'
    have hinit : applyMove d GState.init S₁ = ⟨S₁, 0 + moveCost d ∅ S₁, 0, false⟩ :=
      applyMove_yesTurn d ∅ S₁ 0 0
    rw [hinit] at hs1
    have hc1' : costN c ∅ S₁ ≤ E := by
      rw [hmc hS₁X, hε, zero_add, natCast_div_two_pow_le_iff] at hc1
      exact hc1
    obtain ⟨hJ, hPJ, -, hoffJ⟩ := D.proj (Finset.empty_subset S₁) hS₁X
    rw [Finset.empty_union] at hJ hPJ hoffJ
    have hTJ : D.Tight (D.key S₁) := D.tight_jmove D.tight_empty hJ
    have hJS₁ : D.key S₁ ⊆ S₁ := D.key_subset S₁
    have hoff : ∀ z ∈ D.P (D.key S₁), z ∈ S₁ \ D.key S₁ → z ∈ D.key S₁ := by
      intro z hz hzA
      rw [hPJ] at hz
      exact hoffJ z hz (Finset.mem_sdiff.1 hzA).1
    have hscore : ((costN c ∅ (D.key S₁) + costN c (D.key S₁) (D.key S₁ ∪ (S₁ \ D.key S₁)) :
        ℕ) : ℝ) / 2 ^ N ≤ 0 + moveCost d ∅ S₁ :=
      le_of_eq (by rw [Finset.union_sdiff_of_subset hJS₁,
        ← costN_add c (Finset.empty_subset _) hJS₁, hmc hS₁X, zero_add])
    have hs1' : SafeYes d ⟨D.key S₁ ∪ (S₁ \ D.key S₁), 0 + moveCost d ∅ S₁, 0, false⟩ := by
      rw [Finset.union_sdiff_of_subset hJS₁]; exact hs1
    have hpost := D.yesK_of_safeYes d N c E hX hout hc hε F (D.key S₁) (S₁ \ D.key S₁)
      (costN c ∅ (D.key S₁)) 0 (0 + moveCost d ∅ S₁) 0 hTJ (Finset.sdiff_subset.trans hS₁X)
      (hcardF _) hoff hscore (by simp) hs1'
    rw [D.key_key] at hpost
    obtain ⟨hKM, -⟩ := D.jmove_keyMove hJ
    rw [D.key_empty, D.key_key] at hKM
    have hle : costN c ∅ (D.key S₁) ≤ costN c ∅ S₁ :=
      costN_le_of_subset c (Finset.sdiff_subset_sdiff hJS₁ (Finset.Subset.refl _))
    exact ⟨D.key S₁, Finset.mem_powerset.2 (hJS₁.trans hS₁X), hKM, by omega, hpost⟩

/-- `valK_eq_val` for the raw recursion: whenever `D` has the strings in play `X`, the run map `P`
and the outcome `out`, the raw key recursion over `(X, P, out)` computes the value of the game. -/
theorem valKRaw_eq_val {X : Finset BitString} {P : Finset BitString → Finset BitString}
    {out : Finset BitString → Bool}
    (hX : D.X = X) (hP : ∀ S, D.P S = P S) (hO : ∀ S, D.out S = out S)
    (d : GameData) (N : ℕ) (c : BitString → ℕ) (E F : ℕ) (hdX : d.X = X) (hdout : d.outcome = out)
    (hc : ∀ z ∈ d.X, flipCost d z = (c z : ℝ) / 2 ^ N) (hε : d.ε = (E : ℝ) / 2 ^ N)
    (hF : X.card ≤ F) :
    valKRaw X P out c E F = val d := by
  have hP' : D.P = P := funext hP
  have hO' : D.out = out := funext hO
  subst hX hP' hO'
  exact D.valK_eq_val d N c E F hdX hdout hc hε hF

/-- The centrepiece for the game `G_{e,x}` of a clocked machine (as in `gameValB_gameOf`): cost
numerators `costNum` at the precision `gameN`, budget numerator `2 ^ (gameN - m)`. -/
theorem valK_gameOf (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) (x : BitString)
    (hX : D.X = querySet c.toOTM x (clock e x.length) \ Y)
    (hout : D.out =
      (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)).outcome)
    (F : ℕ) (hF : D.X.card ≤ F) :
    D.valK (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
        (2 ^ (gameN e T m x.length - m)) F =
      val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)) :=
  D.valK_eq_val _ (gameN e T m x.length) _ _ F hX.symm hout.symm
    (fun z hz => gameOf_flipCost_eq c e T m Y x z hz) (gameOf_eps_eq c e T m x _) hF

end PathData

end Kolmogorov.RandomStrings
