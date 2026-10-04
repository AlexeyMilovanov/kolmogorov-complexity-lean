/-
Copyright (c) 2024 Someone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: someone
-/
import KolmogorovMathlib.Combinatorics.Bipartite
import Mathlib.Data.List.Range
import Mathlib.Order.OrderIsoNat

/-!
# The combinatorial form of Muchnik's theorem: a game

SUV Section 12.4 states Muchnik's theorem as a game between Mathematician and Adversary with
parameters `a`, `b`, `m` (`m ≤ a`) and `c`.  Mathematician declares, for every `a`-bit string
`A`, at most `c(a+b)^c` strings of length `m` "simple relative to `A`", and for every pair of
a `b`-bit `B` and an `m`-bit `X` at most `c(a+b)^c` strings of length `a` "simple relative to
`B, X`".  Adversary declares, for every `b`-bit `B`, at most `2^m` strings of length `a`
"simple relative to `B`".  Declarations may be made at any moment, seeing the earlier moves of
the opponent, and cannot be retracted; the limit position decides, and Mathematician wins it
when every `A` declared simple relative to some `B` has a witness `X` simple relative to `A`
with `A` simple relative to `B, X`.

Model.  A position of each player is the family of sets declared so far, with the cardinality
restrictions as fields; one position extends another when it declares at least as much.  Time
is discrete: a play (`MuchnikPlay`) lists Adversary's position at every moment `0, 1, 2, …`,
each extending the previous one (a moment without new declarations repeats the position).  A
strategy for Mathematician (`MuchnikStrategy`) gives her position at every moment as a
function of the history of Adversary's positions up to that moment, and it never retracts a
declaration.  Adversary's strategies need no separate type: against a fixed strategy of
Mathematician every Adversary strategy, however adaptive, produces some play, so "winning
against every Adversary strategy" is "winning every play".

The cardinality restrictions bound the number of declarations, so along every play both
players' positions are eventually constant (`MuchnikStrategy.exists_limit`); the positions
from that moment on form the limit position, and `MuchnikStrategy.WinsPlay` asks Mathematician
to win it.

SUV Problem 320, the total-complexity consequence of the "declare all neighbours at once" form
of the strategy, needs non-stochastic strings (Chapter 14) and is archived, with its statement,
in `docs/ARCHIVED_TARGETS.md`.

SUV Section 12.4, pp. 373–375.
-/

namespace Kolmogorov

/-- A position of Adversary in the Muchnik game: for every `b`-bit string `B`, the at most
`2^m` strings of length `a` declared simple relative to `B`.

SUV Section 12.4, p. 373. -/
@[ext]
structure MuchnikAdversaryPosition (a b m : ℕ) where
  /-- The strings declared simple relative to `B`. -/
  simpleGiven : BoolVec b → Finset (BoolVec a)
  /-- Adversary's quantitative restriction. -/
  card_le : ∀ B, (simpleGiven B).card ≤ 2 ^ m

/-- A position of Mathematician in the Muchnik game with parameter `c`: the strings declared
simple relative to a string `A`, and those declared simple relative to a pair `B, X`, both
families obeying the bound `c(a+b)^c`.

SUV Section 12.4, p. 373. -/
@[ext]
structure MuchnikMathematicianPosition (a b m c : ℕ) where
  /-- The `m`-bit strings declared simple relative to `A`. -/
  simpleGivenString : BoolVec a → Finset (BoolVec m)
  /-- The `a`-bit strings declared simple relative to the pair `B, X`. -/
  simpleGivenPair : BoolVec b → BoolVec m → Finset (BoolVec a)
  /-- Mathematician's first quantitative restriction. -/
  card_simpleGivenString_le : ∀ A, (simpleGivenString A).card ≤ c * (a + b) ^ c
  /-- Mathematician's second quantitative restriction. -/
  card_simpleGivenPair_le : ∀ B X, (simpleGivenPair B X).card ≤ c * (a + b) ^ c

/-- One Adversary position extends another: every declaration of the first is a declaration of
the second.

SUV Section 12.4, p. 373 ("the declared strings cannot be taken back"). -/
def MuchnikAdversaryPosition.Extends {a b m : ℕ} (q q' : MuchnikAdversaryPosition a b m) :
    Prop :=
  ∀ B, q.simpleGiven B ⊆ q'.simpleGiven B

/-- One Mathematician position extends another: both families grow.

SUV Section 12.4, p. 373 ("the declared strings cannot be taken back"). -/
def MuchnikMathematicianPosition.Extends {a b m c : ℕ}
    (p p' : MuchnikMathematicianPosition a b m c) : Prop :=
  (∀ A, p.simpleGivenString A ⊆ p'.simpleGivenString A) ∧
    ∀ B X, p.simpleGivenPair B X ⊆ p'.simpleGivenPair B X

/-- Adversary positions are partially ordered by extension.

SUV Section 12.4, p. 373. -/
instance {a b m : ℕ} : PartialOrder (MuchnikAdversaryPosition a b m) where
  le q q' := q.Extends q'
  le_refl _ _ := subset_rfl
  le_trans _ _ _ h₁ h₂ B := (h₁ B).trans (h₂ B)
  le_antisymm _ _ h₁ h₂ := MuchnikAdversaryPosition.ext (funext fun B => (h₁ B).antisymm (h₂ B))

/-- Mathematician positions are partially ordered by extension.

SUV Section 12.4, p. 373. -/
instance {a b m c : ℕ} : PartialOrder (MuchnikMathematicianPosition a b m c) where
  le p p' := p.Extends p'
  le_refl _ := ⟨fun _ => subset_rfl, fun _ _ => subset_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨fun A => (h₁.1 A).trans (h₂.1 A), fun B X => (h₁.2 B X).trans (h₂.2 B X)⟩
  le_antisymm _ _ h₁ h₂ := MuchnikMathematicianPosition.ext
    (funext fun A => (h₁.1 A).antisymm (h₂.1 A))
    (funext fun B => funext fun X => (h₁.2 B X).antisymm (h₂.2 B X))

/-- There are finitely many Adversary positions: the game is "essentially finite".

SUV Section 12.4, p. 373. -/
instance {a b m : ℕ} : Finite (MuchnikAdversaryPosition a b m) :=
  Finite.of_injective (fun q => q.simpleGiven) fun _ _ h => MuchnikAdversaryPosition.ext h

/-- There are finitely many Mathematician positions: the game is "essentially finite".

SUV Section 12.4, p. 373. -/
instance {a b m c : ℕ} : Finite (MuchnikMathematicianPosition a b m c) :=
  Finite.of_injective (fun p => (p.simpleGivenString, p.simpleGivenPair)) fun _ _ h =>
    MuchnikMathematicianPosition.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A sequence in a finite partial order that grows at every step is eventually constant.

SUV Section 12.4, p. 373 ("the game reaches some limit position"). -/
theorem exists_eventually_const_of_le_succ {α : Type*} [PartialOrder α] [Finite α]
    (f : ℕ → α) (hf : ∀ t, f t ≤ f (t + 1)) : ∃ T, ∀ t, T ≤ t → f t = f T := by
  obtain ⟨T, hT⟩ := WellFoundedGT.monotone_chain_condition ⟨f, monotone_nat_of_le_succ hf⟩
  exact ⟨T, fun t ht => (hT t ht).symm⟩

/-- A play of the Muchnik game, seen through Adversary's moves: his position at every moment
`0, 1, 2, …`, each extending the previous one because declarations are irrevocable.

SUV Section 12.4, p. 373. -/
structure MuchnikPlay (a b m : ℕ) where
  /-- Adversary's position at moment `t`. -/
  position : ℕ → MuchnikAdversaryPosition a b m
  /-- Adversary never retracts a declaration. -/
  extends_succ : ∀ t, (position t).Extends (position (t + 1))

/-- The history of a play up to moment `t`: Adversary's positions at the moments `0, …, t`.

SUV Section 12.4, p. 373. -/
def MuchnikPlay.history {a b m : ℕ} (P : MuchnikPlay a b m) (t : ℕ) :
    List (MuchnikAdversaryPosition a b m) :=
  (List.range (t + 1)).map P.position

/-- The history at the next moment is the history now followed by the next position.

SUV Section 12.4, p. 373. -/
theorem MuchnikPlay.history_succ {a b m : ℕ} (P : MuchnikPlay a b m) (t : ℕ) :
    P.history (t + 1) = P.history t ++ [P.position (t + 1)] := by
  simp [MuchnikPlay.history, List.range_succ]

/-- Every history of a play is a chain of positions, each extending the previous one.

SUV Section 12.4, p. 373. -/
theorem MuchnikPlay.isChain_history {a b m : ℕ} (P : MuchnikPlay a b m) (t : ℕ) :
    (P.history t).IsChain MuchnikAdversaryPosition.Extends := by
  rw [MuchnikPlay.history, List.isChain_map, List.isChain_range_succ]
  exact fun s _ => P.extends_succ s

/-- A strategy for Mathematician: her position at every moment as a function of the history of
Adversary's positions so far.  She never retracts a declaration: when a history `h` is followed
by a further Adversary position `q` (the whole list being a chain of extensions), her reply to
`h ++ [q]` extends her reply to `h`.  She may also declare at moments when Adversary does not,
because a moment without Adversary's declarations still lengthens the history.

SUV Section 12.4, p. 373. -/
structure MuchnikStrategy (a b m c : ℕ) where
  /-- Mathematician's position after the given history of Adversary's positions. -/
  reply : List (MuchnikAdversaryPosition a b m) → MuchnikMathematicianPosition a b m c
  /-- Mathematician never retracts a declaration. -/
  reply_extends : ∀ (h : List (MuchnikAdversaryPosition a b m))
    (q : MuchnikAdversaryPosition a b m),
    (h ++ [q]).IsChain MuchnikAdversaryPosition.Extends → (reply h).Extends (reply (h ++ [q]))

/-- Mathematician wins the limit position `(p, q)`: every string `A` that Adversary declared
simple relative to some `B` is served by a string `X` simple relative to `A` such that `A` is
simple relative to `B, X`.

SUV Section 12.4, p. 373. -/
def MathematicianWins {a b m c : ℕ} (p : MuchnikMathematicianPosition a b m c)
    (q : MuchnikAdversaryPosition a b m) : Prop :=
  ∀ (B : BoolVec b) (A : BoolVec a), A ∈ q.simpleGiven B →
    ∃ X ∈ p.simpleGivenString A, A ∈ p.simpleGivenPair B X

/-- The limit position exists: along every play, from some moment `T` on neither Adversary's
position nor Mathematician's reply changes any more.  This is the finiteness of the game — the
cardinality restrictions bound the number of declarations.

SUV Section 12.4, p. 373 ("the game reaches some limit position"). -/
theorem MuchnikStrategy.exists_limit {a b m c : ℕ} (σ : MuchnikStrategy a b m c)
    (P : MuchnikPlay a b m) :
    ∃ T, ∀ t, T ≤ t →
      P.position t = P.position T ∧ σ.reply (P.history t) = σ.reply (P.history T) := by
  obtain ⟨T₁, h₁⟩ := exists_eventually_const_of_le_succ P.position P.extends_succ
  have hσ : ∀ t, σ.reply (P.history t) ≤ σ.reply (P.history (t + 1)) := fun t => by
    have hchain := P.isChain_history (t + 1)
    rw [MuchnikPlay.history_succ] at hchain ⊢
    exact σ.reply_extends _ _ hchain
  obtain ⟨T₂, h₂⟩ := exists_eventually_const_of_le_succ (fun t => σ.reply (P.history t)) hσ
  refine ⟨max T₁ T₂, fun t ht => ⟨?_, ?_⟩⟩
  · rw [h₁ t (le_of_max_le_left ht), h₁ _ (le_max_left _ _)]
  · rw [h₂ t (le_of_max_le_right ht), h₂ _ (le_max_right _ _)]

/-- The strategy `σ` wins the play `P`: at some moment `T` the limit position is reached —
from `T` on neither player declares anything new — and Mathematician wins that limit position.
By `MuchnikStrategy.exists_limit` such a moment always exists, so this is exactly the book's
rule that the limit position decides.

SUV Section 12.4, p. 373. -/
def MuchnikStrategy.WinsPlay {a b m c : ℕ} (σ : MuchnikStrategy a b m c)
    (P : MuchnikPlay a b m) : Prop :=
  ∃ T, (∀ t, T ≤ t →
      P.position t = P.position T ∧ σ.reply (P.history t) = σ.reply (P.history T)) ∧
    MathematicianWins (σ.reply (P.history T)) (P.position T)

/-- Mathematician has a winning strategy in the game with parameters `a, b, m, c`: one of her
strategies wins every play.

SUV Section 12.4, p. 374. -/
def HasMathematicianWinningStrategy (a b m c : ℕ) : Prop :=
  ∃ σ : MuchnikStrategy a b m c, ∀ P : MuchnikPlay a b m, σ.WinsPlay P

section MuchnikStrategyConstruction

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- The load of a right vertex `X` in an assignment `M`: how many left vertices are sent
to `X`. -/
private def assignLoad (M : Finset (L × R)) (X : R) : ℕ :=
  (M.filter fun e => e.2 = X).card

open Classical in
/-- One step of the greedy service at one level (capacity `2`): a newly arrived `A` is sent
to a neighbour of load less than `2`, or, if there is none, forwarded to the next level. -/
private noncomputable def greedyStep (g : Finset (L × R)) (st : Finset (L × R) × List L)
    (A : L) : Finset (L × R) × List L :=
  if h : ∃ X ∈ neighbors g A, assignLoad st.1 X < 2 then (insert (A, h.choose) st.1, st.2)
  else (st.1, st.2 ++ [A])

/-- The greedy service of one level applied to the arrivals `w`, in order: the assignment
made and the list of forwarded strings. -/
private noncomputable def greedyRun (g : Finset (L × R)) (w : List L) :
    Finset (L × R) × List L :=
  w.foldl (greedyStep g) (∅, [])

/-- The multilevel service with `n` levels: each level serves greedily what it can and
forwards the rest to the next level. -/
private noncomputable def served (g : Finset (L × R)) : ℕ → List L → Finset (L × R)
  | 0, _ => ∅
  | n + 1, w => (greedyRun g w).1 ∪ served g n (greedyRun g w).2

/-- The arrivals of a history of declared sets: every string, in order of its first
appearance. -/
private noncomputable def arrivalList (h : List (Finset L)) : List L :=
  h.foldl (fun acc S => acc ++ (S \ acc.toFinset).toList) []

omit [DecidableEq L] in
private lemma assignLoad_mono {M M' : Finset (L × R)} (h : M ⊆ M') (X : R) :
    assignLoad M X ≤ assignLoad M' X :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

private lemma assignLoad_union_le (M M' : Finset (L × R)) (X : R) :
    assignLoad (M ∪ M') X ≤ assignLoad M X + assignLoad M' X := by
  unfold assignLoad
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

/-- The greedy service never takes back an assignment or a forwarding decision. -/
private lemma foldl_greedyStep_mono (g : Finset (L × R)) (v : List L) :
    ∀ st : Finset (L × R) × List L,
      st.1 ⊆ (v.foldl (greedyStep g) st).1 ∧ st.2 <+: (v.foldl (greedyStep g) st).2 := by
  induction v with
  | nil => intro st; exact ⟨subset_rfl, List.prefix_refl _⟩
  | cons A v ih =>
    intro st
    have hstep : st.1 ⊆ (greedyStep g st A).1 ∧ st.2 <+: (greedyStep g st A).2 := by
      unfold greedyStep
      split_ifs
      · exact ⟨Finset.subset_insert _ _, List.prefix_refl _⟩
      · exact ⟨subset_rfl, List.prefix_append _ _⟩
    obtain ⟨h1, h2⟩ := ih (greedyStep g st A)
    exact ⟨hstep.1.trans h1, hstep.2.trans h2⟩

private lemma greedyRun_concat (g : Finset (L × R)) (w : List L) (A : L) :
    greedyRun g (w ++ [A]) = greedyStep g (greedyRun g w) A := by
  simp [greedyRun, List.foldl_append]

/-- The multilevel service is on-line: more arrivals only add assignments. -/
private lemma served_mono (g : Finset (L × R)) (n : ℕ) :
    ∀ w w' : List L, w <+: w' → served g n w ⊆ served g n w' := by
  induction n with
  | zero => intro w w' _; exact subset_rfl
  | succ n ih =>
    intro w w' hw
    obtain ⟨v, rfl⟩ := hw
    have hrun : greedyRun g (w ++ v) = v.foldl (greedyStep g) (greedyRun g w) := by
      simp [greedyRun, List.foldl_append]
    obtain ⟨h1, h2⟩ := foldl_greedyStep_mono g v (greedyRun g w)
    simp only [served]
    rw [hrun]
    exact Finset.union_subset_union h1 (ih _ _ h2)

/-- Each level loads every right vertex at most twice. -/
private lemma assignLoad_greedyRun_le (g : Finset (L × R)) (w : List L) (X : R) :
    assignLoad (greedyRun g w).1 X ≤ 2 := by
  induction w using List.reverseRecOn with
  | nil => simp [greedyRun, assignLoad]
  | append_singleton w A ih =>
    rw [greedyRun_concat]
    unfold greedyStep
    split_ifs with hex
    · have hc := hex.choose_spec.2
      unfold assignLoad at hc ih ⊢
      rw [Finset.filter_insert]
      split_ifs with hX
      · have hX' : hex.choose = X := hX
        subst hX'
        exact (Finset.card_insert_le _ _).trans hc
      · exact ih
    · exact ih

/-- The `n`-level service loads every right vertex at most `2n` times. -/
private lemma assignLoad_served_le (g : Finset (L × R)) (n : ℕ) :
    ∀ (w : List L) (X : R), assignLoad (served g n w) X ≤ 2 * n := by
  induction n with
  | zero => intro w X; simp [served, assignLoad]
  | succ n ih =>
    intro w X
    simp only [served]
    refine (assignLoad_union_le _ _ X).trans ?_
    have := assignLoad_greedyRun_le g w X
    have := ih (greedyRun g w).2 X
    omega

/-- The invariants of one greedy level: it makes at most one assignment per arrival, forwards
a sublist of the arrivals, serves or forwards every arrival, and forwards a string only when
all its neighbours are saturated. -/
private lemma greedyRun_spec (g : Finset (L × R)) (w : List L) :
    (greedyRun g w).1.card ≤ w.length ∧ (greedyRun g w).2.Sublist w ∧
      (∀ A ∈ w, A ∈ (greedyRun g w).2 ∨ ∃ X ∈ neighbors g A, (A, X) ∈ (greedyRun g w).1) ∧
      ∀ A ∈ (greedyRun g w).2, ∀ X ∈ neighbors g A, 2 ≤ assignLoad (greedyRun g w).1 X := by
  induction w using List.reverseRecOn with
  | nil => simp [greedyRun]
  | append_singleton w A ih =>
    rw [greedyRun_concat]
    obtain ⟨hcard, hsub, hcov, hsat⟩ := ih
    generalize greedyRun g w = st at hcard hsub hcov hsat
    obtain ⟨M, F⟩ := st
    unfold greedyStep
    split_ifs with hex
    · refine ⟨?_, hsub.trans (List.sublist_append_left w [A]), ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        exact (Finset.card_insert_le _ _).trans (by simpa using hcard)
      · intro A' hA'
        rcases List.mem_append.1 hA' with hA' | hA'
        · rcases hcov A' hA' with h | ⟨X, hX, hM⟩
          · exact Or.inl h
          · exact Or.inr ⟨X, hX, Finset.mem_insert_of_mem hM⟩
        · rw [List.mem_singleton] at hA'
          subst hA'
          exact Or.inr ⟨_, hex.choose_spec.1, Finset.mem_insert_self _ _⟩
      · intro A' hA' X hX
        exact (hsat A' hA' X hX).trans (assignLoad_mono (Finset.subset_insert _ _) X)
    · refine ⟨?_, hsub.append (List.Sublist.refl _), ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        exact hcard.trans (Nat.le_succ _)
      · intro A' hA'
        rcases List.mem_append.1 hA' with hA' | hA'
        · rcases hcov A' hA' with h | h
          · exact Or.inl (List.mem_append_left _ h)
          · exact Or.inr h
        · exact Or.inl (List.mem_append_right _ hA')
      · intro A' hA' X hX
        rcases List.mem_append.1 hA' with hA' | hA'
        · exact hsat A' hA' X hX
        · rw [List.mem_singleton] at hA'
          subst hA'
          push Not at hex
          exact hex X hX

omit [DecidableEq L] in
/-- Double counting: an assignment with `|M|` edges saturates (load `≥ 2`) at most `|M|/2`
right vertices. -/
private lemma two_mul_card_saturated_le [Fintype R] (M : Finset (L × R)) :
    2 * (Finset.univ.filter fun X => 2 ≤ assignLoad M X).card ≤ M.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  calc 2 * (Finset.univ.filter fun X => 2 ≤ assignLoad M X).card
      = ∑ _X ∈ Finset.univ.filter fun X => 2 ≤ assignLoad M X, 2 := by
        rw [Finset.sum_const_nat fun _ _ => rfl, mul_comm]
    _ ≤ ∑ X ∈ Finset.univ.filter fun X => 2 ≤ assignLoad M X, assignLoad M X :=
        Finset.sum_le_sum fun X hX => (Finset.mem_filter.1 hX).2
    _ ≤ ∑ X, assignLoad M X := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = _ := rfl

/-- The expansion property forces few blocked strings: if all neighbours of every string of
a nonempty `T` lie in a set `U` of at most `k` right vertices, then `|T| < |U|`. -/
private lemma card_lt_of_neighbors_subset {g : Finset (L × R)} {k : ℕ} (hg : IsExpanding g k)
    (hk : 1 ≤ k) {U : Finset R} (hU : U.card ≤ k) {T : Finset L} (hT : T.Nonempty)
    (hTU : ∀ A ∈ T, neighbors g A ⊆ U) : T.card < U.card := by
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hA⟩ := hT
  have h1 := hg {A} (Finset.singleton_nonempty A) (by simpa using hk)
  rw [neighborSet, Finset.singleton_biUnion, Finset.card_singleton] at h1
  have hUpos : 0 < U.card := lt_of_lt_of_le (by omega) (Finset.card_le_card (hTU A hA))
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq hlt
  have hT'ne : T'.Nonempty := Finset.card_pos.1 (by omega)
  have h2 := hg T' hT'ne (by omega)
  have h3 : (neighborSet g T').card ≤ U.card :=
    Finset.card_le_card (Finset.biUnion_subset.2 fun A' hA' => hTU A' (hT'T hA'))
  omega

/-- The multilevel service with `n` levels serves every list of fewer than `2^n` (and at most
`2^m`) distinct arrivals, by an expanding graph: each level forwards less than half of what
it receives. -/
private lemma served_covers [Finite R] {g : Finset (L × R)} {m : ℕ} (hm : 0 < m)
    (hg : IsExpanding g (2 ^ (m - 1))) (n : ℕ) :
    ∀ w : List L, w.Nodup → w.length ≤ 2 ^ m → w.length < 2 ^ n →
      ∀ A ∈ w, ∃ X ∈ neighbors g A, (A, X) ∈ served g n w := by
  induction n with
  | zero =>
    intro w _ _ hlt A hA
    have : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hlt)
    simp [this] at hA
  | succ n ih =>
    intro w hnd hlen hlt A hA
    obtain ⟨hcard, hsub, hcov, hsat⟩ := greedyRun_spec g w
    simp only [served]
    rcases hcov A hA with hF | ⟨X, hX, hM⟩
    · have := Fintype.ofFinite R
      set U := Finset.univ.filter fun X => 2 ≤ assignLoad (greedyRun g w).1 X
      have hcount : 2 * U.card ≤ (greedyRun g w).1.card := two_mul_card_saturated_le _
      have hm2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hFlt : (greedyRun g w).2.toFinset.card < U.card := by
        refine card_lt_of_neighbors_subset hg Nat.one_le_two_pow (by omega)
          ⟨A, List.mem_toFinset.2 hF⟩ ?_
        intro A' hA' X hX
        simpa [U] using hsat A' (List.mem_toFinset.1 hA') X hX
      rw [List.toFinset_card_of_nodup (hsub.nodup hnd)] at hFlt
      have hn2 : 2 ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n
      obtain ⟨X, hX, h⟩ := ih _ (hsub.nodup hnd) (hsub.length_le.trans hlen) (by omega) A hF
      exact ⟨X, hX, Finset.mem_union_right _ h⟩
    · exact ⟨X, hX, Finset.mem_union_left _ hM⟩

private lemma arrivalList_concat (h : List (Finset L)) (S : Finset L) :
    arrivalList (h ++ [S]) = arrivalList h ++ (S \ (arrivalList h).toFinset).toList := by
  simp [arrivalList, List.foldl_append]

private lemma arrivalList_nodup (h : List (Finset L)) : (arrivalList h).Nodup := by
  induction h using List.reverseRecOn with
  | nil => simp [arrivalList]
  | append_singleton h S ih =>
    rw [arrivalList_concat, List.nodup_append]
    refine ⟨ih, Finset.nodup_toList _, ?_⟩
    intro x hx y hy hxy
    subst hxy
    simp [hx] at hy

private lemma toFinset_arrivalList_concat (h : List (Finset L)) (S : Finset L) :
    (arrivalList (h ++ [S])).toFinset = (arrivalList h).toFinset ∪ S := by
  rw [arrivalList_concat, List.toFinset_append, Finset.toList_toFinset,
    Finset.union_sdiff_self_eq_union]

end MuchnikStrategyConstruction

/-- The combinatorial form of Muchnik's theorem: one constant `c` gives Mathematician a
winning strategy for all positive `a, b, m` with `m ≤ a`.

SUV Theorem 230, p. 374. -/
theorem exists_muchnikGame_winningStrategy :
    ∃ c : ℕ, ∀ a b m : ℕ, 0 < a → 0 < b → 0 < m → m ≤ a →
      HasMathematicianWinningStrategy a b m c := by
  classical
  refine ⟨2, fun a b m ha hb hm hma => ?_⟩
  obtain ⟨g, hdeg, hexp⟩ := exists_expanding_bipartiteGraph a m hm hma
  have hsq : a + b ≤ (a + b) ^ 2 := Nat.le_self_pow (by norm_num) (a + b)
  have hK : 2 * (m + 1) ≤ 2 * (a + b) ^ 2 := by omega
  have hK' : a + m + 2 ≤ 2 * (a + b) ^ 2 := by omega
  let arr : List (MuchnikAdversaryPosition a b m) → BoolVec b → List (BoolVec a) :=
    fun h B => arrivalList (h.map fun q => q.simpleGiven B)
  let reply : List (MuchnikAdversaryPosition a b m) → MuchnikMathematicianPosition a b m 2 :=
    fun h =>
    { simpleGivenString := fun A => neighbors g A
      simpleGivenPair := fun B X =>
        ((served g (m + 1) (arr h B)).filter fun e : BoolVec a × BoolVec m => e.2 = X).image
          Prod.fst
      card_simpleGivenString_le := fun A => (hdeg A).trans hK'
      card_simpleGivenPair_le := fun B X =>
        Finset.card_image_le.trans (show assignLoad (served g (m + 1) (arr h B)) X ≤ _ from
          (assignLoad_served_le g _ _ X).trans hK) }
  have harr : ∀ h q B, arr (h ++ [q]) B =
      arr h B ++ (q.simpleGiven B \ (arr h B).toFinset).toList := by
    intro h q B
    simp only [arr, List.map_append, List.map_singleton, arrivalList_concat]
  refine ⟨⟨reply, fun h q _ => ⟨fun A => subset_rfl, fun B X => ?_⟩⟩, fun P => ?_⟩
  · refine Finset.image_subset_image (Finset.filter_subset_filter _ (served_mono g _ _ _ ?_))
    rw [harr]
    exact List.prefix_append _ _
  · obtain ⟨T, hT⟩ := MuchnikStrategy.exists_limit ⟨reply, fun h q _ =>
      ⟨fun A => subset_rfl, fun B X => Finset.image_subset_image
        (Finset.filter_subset_filter _ (served_mono g _ _ _ (by
          rw [harr]; exact List.prefix_append _ _)))⟩⟩ P
    refine ⟨T, hT, ?_⟩
    intro B A hA
    have key : ∀ t, (arr (P.history t) B).toFinset = (P.position t).simpleGiven B := by
      intro t
      induction t with
      | zero => simp [arr, MuchnikPlay.history, arrivalList]
      | succ t ih =>
        rw [MuchnikPlay.history_succ]
        simp only [arr, List.map_append, List.map_singleton, toFinset_arrivalList_concat]
        rw [show (arrivalList ((P.history t).map fun q => q.simpleGiven B)).toFinset =
          (P.position t).simpleGiven B from ih]
        exact Finset.union_eq_right.2 (P.extends_succ t B)
    have hnd := arrivalList_nodup ((P.history T).map fun q => q.simpleGiven B)
    have hlen : (arr (P.history T) B).length ≤ 2 ^ m := by
      rw [← List.toFinset_card_of_nodup hnd]
      rw [show (arr (P.history T) B).toFinset = _ from key T]
      exact (P.position T).card_le B
    have hmem : A ∈ arr (P.history T) B := by
      rw [← List.mem_toFinset, key T]; exact hA
    have hlt : (arr (P.history T) B).length < 2 ^ (m + 1) := by
      have : 0 < 2 ^ m := by positivity
      rw [pow_succ]; omega
    obtain ⟨X, hX, hAX⟩ := served_covers hm hexp (m + 1) _ hnd hlen hlt A hmem
    exact ⟨X, hX, Finset.mem_image.2 ⟨(A, X), Finset.mem_filter.2 ⟨hAX, rfl⟩, rfl⟩⟩

end Kolmogorov
