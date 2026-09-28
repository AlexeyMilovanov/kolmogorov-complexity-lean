import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import KolmogorovMathlib.AlgorithmicRandomness.Cylinders
import Mathlib.Data.Rat.Denumerable

/-!
# The Gács–Day game

The game between a client requesting mass at the nodes of a finitely branching tree and a server
granting cylinders of Cantor space, whose client win is what separates monotone complexity from a
priori complexity.

### Outline

* the board: `GacsDayNode` and its ancestor relation, `Allocation` with `allocationSubset` and
  `disjointAllocations`, and the moves `ClientMove`, `ServerMove`, `GameHistory`;
* the rules: `Serves` (an allocation meets a request), `requestCoherent` and `clientPlayLegal`
  for the client, `serverMoveCoherent` and `serverPlayLegal` for the server, and `playClient`
  for running a `ClientStrategy` against a server play;
* the winning conditions `clientWins` and its stabilised form `clientWinsUnserved`, with the
  monotonicity lemmas in the height;
* the strategy classes `IsWinningStrategyUnserved`, `IsWinningStrategyReal`,
  `IsWinningStrategyExistential` and the uniform versions `IsUniformWinningStrategy`,
  `IsUniformWinningStrategy'` (`RangeSupported`, `TreeSupported`);
* the rational-parameter variants, with `gacsDayGameStatement_rat_of_nat` deducing them from the
  integer ones.

Source: SUV Theorem 88.
-/

namespace Kolmogorov

/-- A node of the request tree of the Gács–Day game, given by the list of branch labels leading to
it. -/
abbrev GacsDayNode := List ℕ

/-- The node `x` lies on the path to the node `y`. -/
def gacsDayNodePrefix (x y : GacsDayNode) : Prop := ∃ z, y = x ++ z

/-- The ancestor relation on nodes of the request tree is transitive. -/
lemma gacsDayNode_prefix_trans {x y z : GacsDayNode}
    (h1 : gacsDayNodePrefix x y) (h2 : gacsDayNodePrefix y z) :
    gacsDayNodePrefix x z := by
  rcases h1 with ⟨w1, rfl⟩
  rcases h2 with ⟨w2, rfl⟩
  use w1 ++ w2
  rw [List.append_assoc]

/-- A finite set of bit strings, read as the cylinders the server has granted to a node. -/
abbrev Allocation := List BitString

/-- Every cylinder of the first allocation is contained in one of the second. -/
def allocationSubset (a1 a2 : Allocation) : Prop :=
  ∀ x ∈ a1, ∃ y ∈ a2, y <+: x

/-- Every allocation is contained in itself. -/
lemma allocationSubset_refl (a : Allocation) : allocationSubset a a := by
  intro x hx
  use x, hx

/-- Containment of allocations is transitive. -/
lemma allocationSubset_trans {a1 a2 a3 : Allocation}
    (h1 : allocationSubset a1 a2) (h2 : allocationSubset a2 a3) :
    allocationSubset a1 a3 := by
  intro x hx
  rcases h1 x hx with ⟨y, hy, hxy⟩
  rcases h2 y hy with ⟨z, hz, hyz⟩
  use z, hz
  exact hyz.trans hxy

/-- No cylinder of the first allocation is prefix-comparable to a cylinder of the second. -/
def disjointAllocations (a1 a2 : Allocation) : Prop :=
  ∀ x ∈ a1, ∀ y ∈ a2, ¬ (x <+: y ∨ y <+: x)

/-- Disjointness of two allocations (no cylinder of one is prefix-comparable to a
cylinder of the other) is genuine set-level disjointness of the corresponding
Cantor cylinders: for `x ∈ a1` and `y ∈ a2`, the cones `Ω_x` and `Ω_y` are disjoint.
This is the structural fact behind "sibling allocations are disjoint". -/
lemma siblingCylinders_disjoint {a1 a2 : Allocation} (h : disjointAllocations a1 a2)
    {x y : BitString} (hx : x ∈ a1) (hy : y ∈ a2) :
    Disjoint (cantorCylinder x) (cantorCylinder y) := by
  have hxy := h x hx y hy
  rw [not_or] at hxy
  exact cantorCylinder_disjoint_of_incompatible hxy.1 hxy.2

/-- A move of the client: a finite list of nodes with the mass each of them requests. -/
abbrev ClientMove := List (GacsDayNode × ℚ)
/-- A move of the server: a finite list of nodes with the allocation granted to each. -/
abbrev ServerMove := List (GacsDayNode × Allocation)

/-- The record of all client and server moves played so far. -/
abbrev GameHistory := List ClientMove × List ServerMove

/-- The allocation contains a cylinder of measure at least the requested mass. -/
def Serves (alloc : Allocation) (req : ℚ) : Prop :=
  ∃ c ∈ alloc, (req : ℝ) ≤ (1 / 2 : ℝ) ^ c.length

/-- Enlarging an allocation preserves the requests it serves. -/
lemma Serves_mono_of_allocation_subset {a1 a2 : Allocation} {req : ℚ}
    (h : allocationSubset a1 a2) (hServes : Serves a1 req) : Serves a2 req := by
  rcases hServes with ⟨c, hc, hc_len⟩
  rcases h c hc with ⟨c', hc', h_prefix⟩
  use c', hc'
  refine le_trans hc_len ?_
  have hlen : c'.length ≤ c.length := List.IsPrefix.length_le h_prefix
  have hpos : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  exact pow_le_pow_of_le_one hpos hle hlen

/-- The mass requested for a node by a client move, or `0` if the node is not mentioned. -/
def getReq (m : ClientMove) (n : GacsDayNode) : ℚ :=
  match m.lookup n with
  | some q => q
  | none => 0

/-- Adding a zero request at an unmentioned node changes no request value. -/
lemma getReq_extend_unused (req : ClientMove) (n : GacsDayNode) (h_unused : req.lookup n = none) :
    ∀ x, getReq (req ++ [(n, 0)]) x = getReq req x := by
  intro x
  unfold getReq
  rw [List.lookup_append]
  cases hx : req.lookup x
  · by_cases heq : x = n
    · subst heq
      have H : List.lookup x [(x, (0 : ℚ))] = some 0 := by
        simp [List.lookup]
      rw [H]
      rfl
    · have H2 : List.lookup x [(n, (0 : ℚ))] = none := by
        have hne : (x == n) = false := by
          cases h_bool : (x == n)
          · rfl
          · exfalso; apply heq; exact eq_of_beq h_bool
        simp [List.lookup, hne]
      rw [H2]
      rfl
  · rename_i val
    have : (Option.some val).or (List.lookup x [(n, 0)]) = some val := rfl
    rw [this]

/-- A client move is coherent when all requests are nonnegative, the root requests at most `1/d`,
and
the children of any node request together no more than the node itself. -/
def requestCoherent (b : ℕ) (d : ℕ) (req : ClientMove) : Prop :=
  (∀ x : GacsDayNode, 0 ≤ getReq req x) ∧
  (getReq req [] ≤ 1 / (d : ℚ)) ∧
  (∀ x : GacsDayNode, getReq req x ≥ ∑ c : Fin b, getReq req (x ++ [c.val]))

/-- Adding a zero request at an unmentioned node preserves coherence. -/
lemma requestCoherent_of_extend_unused (b d : ℕ) (req : ClientMove) (n : GacsDayNode)
    (h_coh : requestCoherent b d req) (h_unused : req.lookup n = none) :
    requestCoherent b d (req ++ [(n, 0)]) := by
  have H := getReq_extend_unused req n h_unused
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [H x]
    exact h_coh.1 x
  · rw [H []]
    exact h_coh.2.1
  · intro x
    rw [H x]
    have hsum : (∑ c : Fin b, getReq (req ++ [(n, 0)]) (x ++ [c.val]))
        = ∑ c : Fin b, getReq req (x ++ [c.val]) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [H (x ++ [c.val])]
    rw [hsum]
    exact h_coh.2.2 x

/-- A rule producing the client's next move from the history of play. -/
def ClientStrategy := GameHistory → ClientMove

/-- The allocation granted to a node by a server move, empty if the node is not mentioned. -/
def getAlloc (m : ServerMove) (n : GacsDayNode) : Allocation :=
  match m.lookup n with
  | some a => a
  | none => []

/-- A server move is coherent when each child's allocation sits inside its parent's and distinct
siblings receive disjoint allocations. -/
def serverMoveCoherent (b : ℕ) (alloc : ServerMove) : Prop :=
  (∀ x : GacsDayNode, ∀ c : Fin b,
    allocationSubset (getAlloc alloc (x ++ [c.val])) (getAlloc alloc x)) ∧
  (∀ x : GacsDayNode, ∀ c1 c2 : Fin b, c1 ≠ c2 →
    disjointAllocations (getAlloc alloc (x ++ [c1.val])) (getAlloc alloc (x ++ [c2.val])))

/-- A server play is legal when every move is coherent and allocations only grow with time. -/
def serverPlayLegal (b : ℕ) (serverMoves : ℕ → ServerMove) : Prop :=
  (∀ t, serverMoveCoherent b (serverMoves t)) ∧
  (∀ t x, allocationSubset (getAlloc (serverMoves t) x) (getAlloc (serverMoves (t + 1)) x))

/-- A request served at some time stays served at all later times. -/
lemma serves_mono_time {b : ℕ} {sm : ℕ → ServerMove}
    (hlegal : serverPlayLegal b sm) {t t' : ℕ} (hle : t ≤ t')
    {x : GacsDayNode} {q : ℚ}
    (hServes : Serves (getAlloc (sm t) x) q) :
    Serves (getAlloc (sm t') x) q := by
  induction hle with
  | refl => exact hServes
  | step h_le ih =>
    exact Serves_mono_of_allocation_subset (hlegal.2 _ x) ih

/-- A client play is legal when every move is coherent and requests only grow with time. -/
def clientPlayLegal (b d : ℕ) (clientMoves : ℕ → ClientMove) : Prop :=
  (∀ t, requestCoherent b d (clientMoves t)) ∧
  (∀ t x, getReq (clientMoves t) x ≤ getReq (clientMoves (t + 1)) x)

/-- The client wins when some node of the tree is left unserved at every time. -/
def clientWins (h b : ℕ) (clientMoves : ℕ → ClientMove) (serverMoves : ℕ → ServerMove) : Prop :=
  ∃ x : GacsDayNode, x.length ≤ h ∧ (∀ a ∈ x, a < b) ∧
    ∀ t, ¬ Serves (getAlloc (serverMoves t) x) (getReq (clientMoves t) x)

/-- The client wins in the stabilised sense when some node's request at some fixed time is never
served, at any time. -/
def clientWinsUnserved (h b : ℕ) (cm : ℕ → ClientMove) (sm : ℕ → ServerMove) : Prop :=
  ∃ T : ℕ, ∃ x : GacsDayNode, x.length ≤ h ∧ (∀ a ∈ x, a < b) ∧
    ∀ t, ¬ Serves (getAlloc (sm t) x) (getReq (cm T) x)

/-- A win witnessed inside a tree of height `h` is also a win inside any taller tree. -/
lemma clientWinsUnserved_mono_height {h h' b : ℕ} (hh : h ≤ h')
    {cm : ℕ → ClientMove} {sm : ℕ → ServerMove}
    (hwin : clientWinsUnserved h b cm sm) :
    clientWinsUnserved h' b cm sm := by
  rcases hwin with ⟨T, x, hlen, hin, hfail⟩
  use T, x
  exact ⟨le_trans hlen hh, hin, hfail⟩

/-- For a client whose requests stabilise, winning implies winning in the stabilised sense. -/
lemma clientWinsUnserved_of_clientWins {h b : ℕ} {cm : ℕ → ClientMove} {sm : ℕ → ServerMove}
    (hstab : ∃ T, ∀ t ≥ T, ∀ x, getReq (cm t) x = getReq (cm T) x)
    (hlegal : serverPlayLegal b sm) (hwin : clientWins h b cm sm) :
    clientWinsUnserved h b cm sm := by
  rcases hwin with ⟨x, hlen, hin, hfail⟩
  rcases hstab with ⟨T, hT⟩
  use T, x, hlen, hin
  intro t ht
  have hfail_t := hfail (max t T)
  have heq : getReq (cm (max t T)) x = getReq (cm T) x := hT (max t T) (le_max_right t T) x
  rw [heq] at hfail_t
  have hserves_max : Serves (getAlloc (sm (max t T)) x) (getReq (cm T) x) :=
    serves_mono_time hlegal (le_max_left t T) ht
  exact hfail_t hserves_max

/-- The sequence of client moves obtained by running the strategy `σ` against a fixed server play.
-/
def playClient (σ : ClientStrategy) (serverMoves : ℕ → ServerMove) : ℕ → ClientMove
  | 0 => σ ([], [])
  | t + 1 =>
      σ (List.ofFn (fun i : Fin (t+1) => playClient σ serverMoves i.val),
         List.ofFn (fun i : Fin (t+1) => serverMoves i.val))

/-- A strategy that plays legally and wins in the stabilised sense against every legal server play.
-/
def IsWinningStrategyUnserved {h b : ℕ} (d : ℕ) (σ : ClientStrategy) : Prop :=
  ∀ serverMoves : ℕ → ServerMove,
    serverPlayLegal b serverMoves →
    clientPlayLegal b d (playClient σ serverMoves) ∧
    clientWinsUnserved h b (playClient σ serverMoves) serverMoves

/-- A strategy that plays legally and wins against every legal server play. -/
def IsWinningStrategyReal {h b : ℕ} (d : ℕ) (σ : ClientStrategy) : Prop :=
  ∀ serverMoves : ℕ → ServerMove,
    serverPlayLegal b serverMoves →
    clientPlayLegal b d (playClient σ serverMoves) ∧
    clientWins h b (playClient σ serverMoves) serverMoves

/-- The client only ever requests inside the `b`-ary tree. -/
def RangeSupported (b : ℕ) (σ : ClientStrategy) : Prop :=
  ∀ (hist : GameHistory) (x : GacsDayNode) (i : ℕ), b ≤ i → getReq (σ hist) (x ++ [i]) = 0

/-- A winning strategy in the stabilised sense that only ever requests inside the `b`-ary tree. -/
def IsUniformWinningStrategy (h b d : ℕ) (σ : ClientStrategy) : Prop :=
  IsWinningStrategyUnserved (h := h) (b := b) d σ ∧ RangeSupported b σ

/-- The client never requests at a node deeper than `h`. -/
def TreeSupported (h _b : ℕ) (σ : ClientStrategy) : Prop :=
  ∀ hist x, h < x.length → getReq (σ hist) x = 0

/-- A uniform winning strategy that in addition requests nothing below depth `h`. -/
def IsUniformWinningStrategy' (h b d : ℕ) (σ : ClientStrategy) : Prop :=
  IsUniformWinningStrategy h b d σ ∧ TreeSupported h b σ

/-- A depth-bounded uniform winning strategy is in particular a uniform winning strategy. -/
theorem IsUniformWinningStrategy'.toUniform {h b d : ℕ} {σ : ClientStrategy}
    (hw : IsUniformWinningStrategy' h b d σ) : IsUniformWinningStrategy h b d σ :=
  hw.1

/-- A win inside a tree of height `h` is also a win inside any taller tree. -/
lemma clientWins_mono_height {h h' b : ℕ} (hh : h ≤ h') {cm : ℕ → ClientMove} {sm : ℕ → ServerMove}
    (hwin : clientWins h b cm sm) : clientWins h' b cm sm := by
  rcases hwin with ⟨x, hlen, hin, hfail⟩
  use x
  exact ⟨le_trans hlen hh, hin, hfail⟩

/-- A winning strategy for height `h` also wins for any larger height. -/
lemma isWinningStrategyReal_mono_height {h h' b d : ℕ} (hh : h ≤ h') {σ : ClientStrategy}
    (hwin : IsWinningStrategyReal (h := h) (b := b) d σ) :
    IsWinningStrategyReal (h := h') (b := b) d σ := by
  intro sms hsms
  have hw := hwin sms hsms
  exact ⟨hw.1, clientWins_mono_height hh hw.2⟩

/-- This is the older existential form of the winning strategy. It is not usable as the hypothesis
of the binary reduction because the embedding cannot match the branching factor `b0` computably,
and out-of-range requests are not suppressed. -/
lemma isWinningStrategyUnserved_mono_height {h h' b d : ℕ} (hh : h ≤ h') {σ : ClientStrategy}
    (hwin : IsWinningStrategyUnserved (h := h) (b := b) d σ) :
    IsWinningStrategyUnserved (h := h') (b := b) d σ := by
  intro sms hsms
  have hw := hwin sms hsms
  exact ⟨hw.1, clientWinsUnserved_mono_height hh hw.2⟩

/-- A strategy that wins in the stabilised sense for some height and branching factor within the
given bounds. -/
def IsWinningStrategyExistential {h b : ℕ} (d : ℕ) (σ : ClientStrategy) : Prop :=
  ∃ h0 ≤ h, ∃ b0 ≤ b, IsWinningStrategyUnserved (h := h0) (b := b0) d σ

/-- A uniform winning strategy is winning in the existential sense. -/
lemma isWinningStrategy_of_isUniform {h b d : ℕ} {σ : ClientStrategy}
    (hwin : IsUniformWinningStrategy h b d σ) :
    IsWinningStrategyExistential (h := h) (b := b) d σ := by
  use h
  refine ⟨le_refl _, b, le_refl _, hwin.1⟩

/-- Existence of a winning strategy is preserved when height and branching factor are increased. -/
lemma gacsDay_clientWin_mono {h b h' b' d : ℕ} (hh : h ≤ h') (hb : b ≤ b') :
    (∃ σ, IsWinningStrategyExistential (h := h) (b := b) d σ) →
    (∃ σ, IsWinningStrategyExistential (h := h') (b := b') d σ) := by
  intro h_strat
  rcases h_strat with ⟨σ, ⟨h0, h0_le_h, b0, b0_le_b, h_win⟩⟩
  use σ
  exact ⟨h0, le_trans h0_le_h hh, b0, le_trans b0_le_b hb, h_win⟩

/-- The combinatorial statement behind the Gács–Day separation: a computable family of uniform
winning strategies exists at height `C d` and branching factor `2 ^ ((C d) ^ (C d))`. -/
def GacsDayGameStatement : Prop :=
  ∃ C : ℕ, ∃ σ : ℕ → ClientStrategy, Computable₂ σ ∧
    ∀ d ≥ 1, IsUniformWinningStrategy (C * d) (2 ^ ((C * d) ^ (C * d))) d (σ d)

/-- The binary form of the game statement: uniform winning strategies at branching factor `2` and
height `(C d) ^ (C d)`. -/
def BinaryGacsDayStatement : Prop :=
  ∃ C : ℕ, ∃ σ : ℕ → ClientStrategy, Computable₂ σ ∧
    ∀ d ≥ 1, IsUniformWinningStrategy ((C * d) ^ (C * d)) 2 d (σ d)

/-- The binary form of the game statement with the larger height `2 ^ ((C d) ^ (C d))`. -/
def BinaryGacsDayStatement_pow : Prop :=
  ∃ C : ℕ, ∃ σ : ℕ → ClientStrategy, Computable₂ σ ∧
    ∀ d ≥ 1, IsUniformWinningStrategy (2 ^ ((C * d) ^ (C * d))) 2 d (σ d)

/-- Every natural number is at most `2` raised to itself. -/
lemma Nat.le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
    _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left (by apply Nat.one_le_two_pow) (2 ^ n)
    _ = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_two]

/-- The separation the game is used for: monotone complexity relative to `D` is not bounded by a
priori complexity plus a constant, and exceeds it by at least about `log log n` infinitely often. -/
def GacsDaySeparationStatement (D : BitStream → BitStream) : Prop :=
  (¬ ∃ c : ℝ, ∀ x, ((KMOf D x).toNat : ℝ) ≤ KA x + c) ∧
  ∃ c : ℝ, ∀ N : ℕ, ∃ n ≥ N, ∃ x : BitString, x.length = n ∧
     KA x + Real.logb 2 (Real.logb 2 n) - c * Real.logb 2 (Real.logb 2 (Real.logb 2 n))
       ≤ ((KMOf D x).toNat : ℝ)

/-- Coherence of a client move with a rational bound `1/d` on the root request. -/
def requestCoherentRat (b : ℕ) (d : ℚ) (req : ClientMove) : Prop :=
  (∀ x : GacsDayNode, 0 ≤ getReq req x) ∧
  (getReq req [] ≤ 1 / d) ∧
  (∀ x : GacsDayNode, getReq req x ≥ ∑ c : Fin b, getReq req (x ++ [c.val]))

/-- Legality of a client play with a rational bound on the root request. -/
def clientPlayLegalRat (b : ℕ) (d : ℚ) (clientMoves : ℕ → ClientMove) : Prop :=
  (∀ t, requestCoherentRat b d (clientMoves t)) ∧
  (∀ t x, getReq (clientMoves t) x ≤ getReq (clientMoves (t + 1)) x)

/-- A strategy winning in the stabilised sense while playing legally against a rational bound on the
root request. -/
def IsWinningStrategyUnservedRat {h b : ℕ} (d : ℚ) (σ : ClientStrategy) : Prop :=
  ∀ serverMoves : ℕ → ServerMove,
    serverPlayLegal b serverMoves →
    clientPlayLegalRat b d (playClient σ serverMoves) ∧
    clientWinsUnserved h b (playClient σ serverMoves) serverMoves

/-- A rational-parameter winning strategy that only requests inside the `b`-ary tree. -/
def IsUniformWinningStrategyRat (h b : ℕ) (d : ℚ) (σ : ClientStrategy) : Prop :=
  IsWinningStrategyUnservedRat (h := h) (b := b) d σ ∧ RangeSupported b σ

/-- Coherence with an integer bound implies coherence with any smaller rational bound at least `1`.
-/
lemma requestCoherentRat_of_nat {b d_nat : ℕ} {d : ℚ}
    (hd : d ≥ 1) (hle : d ≤ (d_nat : ℚ)) (req : ClientMove)
    (h_coh : requestCoherent b d_nat req) :
    requestCoherentRat b d req := by
  refine ⟨h_coh.1, ?_, h_coh.2.2⟩
  refine le_trans h_coh.2.1 ?_
  have hd_pos : (0 : ℚ) < d := by linarith
  have hd_nat_pos : (0 : ℚ) < d_nat := by linarith
  exact one_div_le_one_div_of_le hd_pos hle

/-- The game statement for integer parameters yields the same statement for rational parameters,
with
the height and branching factor taken at the ceiling of `d`. -/
theorem gacsDayGameStatement_rat_of_nat
    (H : GacsDayGameStatement) :
    ∃ C : ℕ, ∃ σ : ℕ → ClientStrategy, Computable₂ σ ∧
      ∀ d : ℚ, d ≥ 1 →
        IsUniformWinningStrategyRat (C * ⌈d⌉₊)
          (2 ^ ((C * ⌈d⌉₊) ^ (C * ⌈d⌉₊))) d (σ ⌈d⌉₊) := by
  rcases H with ⟨C, σ, hcomp, hwin⟩
  use C, σ, hcomp
  intro d hd
  have hceil_pos : ⌈d⌉₊ ≥ 1 := by
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr (by linarith))
  have hwin_d := hwin ⌈d⌉₊ hceil_pos
  refine ⟨?_, hwin_d.2⟩
  intro sms hsms
  have hwin_real := hwin_d.1 sms hsms
  refine ⟨?_, hwin_real.2⟩
  refine ⟨?_, hwin_real.1.2⟩
  intro t
  have hle : d ≤ (⌈d⌉₊ : ℚ) := Nat.le_ceil d
  exact requestCoherentRat_of_nat hd hle (playClient (σ ⌈d⌉₊) sms t) (hwin_real.1.1 t)

end Kolmogorov
