/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Automaton Defs

Multihead one-way finite automata and the languages `L_m` of strings
`w_1 # … # w_m # w_m # … # w_1` (Shen, Uspensky, Vereshchagin, pp. 236–237).

* `MultiheadAutomaton`, `MultiheadAutomaton.Accepts`, `MultiheadAutomaton.Recognizes`: a `k`-head
  automaton in which each step moves a nonempty set of heads that do not see the end marker, and
  which therefore always terminates (`MultiheadAutomaton.terminated_run`).
* `palindromeBlocks`, `IsRecognizedBy`: the language `L_m` and recognizability by a `k`-head
  automaton with finitely many states.
* `isRecognizedBy_palindromeBlocks`: `L_m` is recognized by a `k`-head automaton whenever
  `m ≤ k(k-1)/2`.
-/

namespace Kolmogorov.Applications

/-- A `k`-head one-way automaton over the alphabet `Sym`, with states `Q`. -/
structure MultiheadAutomaton (k : ℕ) (Sym Q : Type*) where
  /-- The initial state. -/
  init : Q
  /-- The accepting states. -/
  accepting : Set Q
  /-- The transition: the new state and the heads instructed to move, as a function of the state and
  of what the heads observe, where `none` is the end marker. -/
  step : Q → (Fin k → Option Sym) → Q × Finset (Fin k)
  /-- As long as some head does not see the marker, some head that does not see it is moved. -/
  moves_nonempty : ∀ q obs, (∃ i, obs i ≠ none) → ∃ i ∈ (step q obs).2, obs i ≠ none

/-- A configuration of a `k`-head automaton. -/
structure HeadConfig (k : ℕ) (Q : Type*) where
  /-- The current state. -/
  state : Q
  /-- The positions of the heads; position `|w|` is the end marker. -/
  pos : Fin k → ℕ

namespace MultiheadAutomaton

variable {k : ℕ} {Sym Q : Type*}

/-- What the heads see at their positions on the input `w`; `none` is the end marker. -/
def observe (w : List Sym) (pos : Fin k → ℕ) : Fin k → Option Sym := fun i => w[pos i]?

/-- All heads observe the end marker. -/
def Terminated (w : List Sym) (c : HeadConfig k Q) : Prop := ∀ i, observe w c.pos i = none

open Classical in
/-- One step on input `w`: nothing happens once all heads see the marker; otherwise the state
changes, and each instructed head that does not see the marker moves right. -/
noncomputable def next (A : MultiheadAutomaton k Sym Q) (w : List Sym) (c : HeadConfig k Q) :
    HeadConfig k Q :=
  if Terminated w c then c else
    let r := A.step c.state (observe w c.pos)
    { state := r.1
      pos := fun i => if i ∈ r.2 ∧ observe w c.pos i ≠ none then c.pos i + 1 else c.pos i }

/-- The initial configuration: all heads on the leftmost character. -/
def start (A : MultiheadAutomaton k Sym Q) : HeadConfig k Q := ⟨A.init, fun _ => 0⟩

/-- The configuration after `t` steps on input `w`. -/
noncomputable def run (A : MultiheadAutomaton k Sym Q) (w : List Sym) (t : ℕ) : HeadConfig k Q :=
  (A.next w)^[t] A.start

/-- **SUV p. 236.**  `A` accepts `w` if it terminates in an accepting state. -/
def Accepts (A : MultiheadAutomaton k Sym Q) (w : List Sym) : Prop :=
  ∃ t, Terminated w (A.run w t) ∧ (A.run w t).state ∈ A.accepting

/-- **SUV p. 236.**  `A` recognizes `L`: the accepted words are exactly those of `L`. -/
def Recognizes (A : MultiheadAutomaton k Sym Q) (L : Set (List Sym)) : Prop :=
  ∀ w, w ∈ L ↔ A.Accepts w

/-- Heads never leave the input: a head position is at most `|w|`, the position of the marker. -/
lemma pos_le_length (A : MultiheadAutomaton k Sym Q) (w : List Sym) (t : ℕ) (i : Fin k) :
    (A.run w t).pos i ≤ w.length := by
  induction t with
  | zero => simp [run, start]
  | succ t ih =>
    have hrun : A.run w (t + 1) = A.next w (A.run w t) := Function.iterate_succ_apply' _ _ _
    rw [hrun]
    unfold next
    split_ifs with hterm
    · exact ih
    · dsimp only
      split_ifs with hmove
      · have hne := hmove.2
        have hlt : (A.run w t).pos i < w.length := by
          by_contra hge
          exact hne (List.getElem?_eq_none (not_lt.mp hge))
        omega
      · exact ih

/-- Until all heads see the marker, the sum of the head positions is at least the number of steps,
as some head moves at each step. -/
private lemma min_le_sum_pos (A : MultiheadAutomaton k Sym Q) (w : List Sym) (t : ℕ) :
    Terminated w (A.run w t) ∨ t ≤ ∑ i, (A.run w t).pos i := by
  induction t with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ t ih =>
    have hrun : A.run w (t + 1) = A.next w (A.run w t) := Function.iterate_succ_apply' _ _ _
    by_cases hterm : Terminated w (A.run w t)
    · left
      rw [hrun, next, ite_eq_left hterm]
      exact hterm
    · right
      have ih' := ih.resolve_left hterm
      rw [hrun, next, ite_eq_right hterm]
      dsimp only
      have hobs : ∃ i, observe w (A.run w t).pos i ≠ none := by
        by_contra hcon
        push Not at hcon
        exact hterm hcon
      obtain ⟨j, hj, hjne⟩ := A.moves_nonempty (A.run w t).state _ hobs
      have hstep : ∑ i, (A.run w t).pos i + 1 ≤ ∑ i, (if i ∈ (A.step (A.run w t).state
          (observe w (A.run w t).pos)).2 ∧ observe w (A.run w t).pos i ≠ none then
            (A.run w t).pos i + 1 else (A.run w t).pos i) := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j),
          ← Finset.add_sum_erase Finset.univ (fun i => if i ∈ (A.step (A.run w t).state
            (observe w (A.run w t).pos)).2 ∧ observe w (A.run w t).pos i ≠ none then
              (A.run w t).pos i + 1 else (A.run w t).pos i) (Finset.mem_univ j),
          ite_eq_left ⟨hj, hjne⟩]
        have hrest : ∑ i ∈ Finset.univ.erase j, (A.run w t).pos i ≤
            ∑ i ∈ Finset.univ.erase j, (if i ∈ (A.step (A.run w t).state
              (observe w (A.run w t).pos)).2 ∧ observe w (A.run w t).pos i ≠ none then
                (A.run w t).pos i + 1 else (A.run w t).pos i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          split_ifs <;> omega
        omega
      omega

/-- **SUV p. 236.**  The automaton always terminates, since some head moves at each step: after at
most `k · |w| + 1` steps all heads see the marker. -/
theorem terminated_run (A : MultiheadAutomaton k Sym Q) (w : List Sym) :
    Terminated w (A.run w (k * w.length + 1)) := by
  refine (min_le_sum_pos A w (k * w.length + 1)).resolve_right fun hle => ?_
  have hsum : ∑ i, (A.run w (k * w.length + 1)).pos i ≤ k * w.length := by
    calc ∑ i, (A.run w (k * w.length + 1)).pos i
        ≤ ∑ _i : Fin k, w.length := Finset.sum_le_sum fun i _ => pos_le_length A w _ i
      _ = k * w.length := by simp
  omega

end MultiheadAutomaton

/-- The alphabet of the languages `L_m`: the two bits and the separator `#`. -/
inductive BlockSymbol
  | bit (b : Bool)
  | sep
  deriving DecidableEq

/-- The word `w_1 # w_2 # … # w_r` for a list of binary strings. -/
def blockWord (blocks : List (List Bool)) : List BlockSymbol :=
  List.intercalate [BlockSymbol.sep] (blocks.map fun b => b.map BlockSymbol.bit)

/-- **SUV p. 237.**  The language `L_m` of the strings `w_1 # … # w_m # w_m # … # w_1`, with
arbitrary binary strings `w_i`.  For `m = 1` it is the language `x # x` of the example on p. 236. -/
def palindromeBlocks (m : ℕ) : Set (List BlockSymbol) :=
  {s | ∃ w : Fin m → List Bool, s = blockWord (List.ofFn w ++ (List.ofFn w).reverse)}

/-- `L` is recognized by a `k`-head automaton with finitely many states. -/
def IsRecognizedBy (k : ℕ) (L : Set (List BlockSymbol)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (A : MultiheadAutomaton k BlockSymbol Q), A.Recognizes L


/-! ### Head programs (helpers for `isRecognizedBy_palindromeBlocks`)

The automaton of the book proof is described by a *head program*: a list of instructions on heads
numbered by naturals, where `adv h` moves head `h` over one block and `cmp a b last` moves two heads
in lockstep over equal blocks.  `pb_interpreter` turns any such program
into a finite-state automaton; the programs `pb_peelProg` (a traveller
head checks the outer `p` blocks against `p` waiting heads, then the waiting heads are moved to the
start of the inner part) are glued recursively into `pb_prog`, whose
success is characterized in `pb_lang`.  The inner part is run by the
same heads on a suffix of the word, so the waiting heads are reused as in the book. -/

/-- Instructions of a head program: `adv h` moves head `h` over one block (bits and the separator
after them); `cmp a b last` moves heads `a` and `b` in lockstep over equal blocks; the block of `a`
ends with a separator and the block of `b` ends with a separator, or with the end marker when
`last = true`. -/
private def pb_Instr : Type := ℕ ⊕ (ℕ × ℕ × Bool)

@[match_pattern]
private def pb_Instr.adv (h : ℕ) :
    pb_Instr := Sum.inl h

@[match_pattern]
private def pb_Instr.cmp (a b : ℕ) (last : Bool) :
    pb_Instr := Sum.inr (a, b, last)

/-- List-level effect of `adv`: drop one block and its separator. -/
private def pb_execAdv :
    List BlockSymbol → Option (List BlockSymbol)
  | [] => none
  | BlockSymbol.sep :: z => some z
  | BlockSymbol.bit _ :: z => pb_execAdv z

/-- List-level effect of `cmp`. -/
private def pb_execCmp (last : Bool) :
    List BlockSymbol → List BlockSymbol → Option (List BlockSymbol × List BlockSymbol)
  | BlockSymbol.bit x :: za, BlockSymbol.bit x' :: zb =>
      if x = x' then pb_execCmp last za zb else none
  | BlockSymbol.sep :: za, BlockSymbol.sep :: zb => if last then none else some (za, zb)
  | BlockSymbol.sep :: za, [] => if last then some (za, []) else none
  | _, _ => none

/-- The remaining input of every head (head `h` is `r h`) after an instruction, if it succeeds. -/
private def pb_execInstr :
    pb_Instr → (ℕ → List BlockSymbol) →
      Option (ℕ → List BlockSymbol)
  | .adv h, r =>
      (pb_execAdv (r h)).map fun z => Function.update r h z
  | .cmp a b last, r =>
      (pb_execCmp last (r a) (r b)).map fun p =>
        Function.update (Function.update r a p.1) b p.2

/-- The effect of a head program. -/
private def pb_execProg :
    List pb_Instr → (ℕ → List BlockSymbol) →
      Option (ℕ → List BlockSymbol)
  | [], r => some r
  | i :: is, r =>
      (pb_execInstr i r).bind
        (pb_execProg is)

/-- The instruction only mentions heads `< K`, and compares two different heads. -/
private def pb_Instr.Ok (K : ℕ) :
    pb_Instr → Prop
  | .adv h => h < K
  | .cmp a b _ => a < K ∧ b < K ∧ a ≠ b

/-- The program of the peel step: head `o` is the traveller, heads `o+1, …, o+p` wait at the starts
of blocks `0, …, p-1`; the traveller is moved to the start of block `p + N` and compares block `j`
with block `p + N + (p - 1 - j)` for `j = p-1, …, 0` (the last copy ends at the end marker when
`e = true`); finally all heads `o+1, …, o+k` are moved to the start of block `p`. -/
private def pb_peelProg (o k p N : ℕ) (e : Bool) :
    List pb_Instr :=
  List.replicate (p + N) (.adv o) ++
  (List.range p).flatMap (fun j => List.replicate j (.adv (o + 1 + j))) ++
  (List.range p).reverse.map (fun j =>
    pb_Instr.cmp (o + 1 + j) o (e && decide (j = 0))) ++
  (List.range k).flatMap
    (fun j => List.replicate (if j < p then p - 1 - j else p) (.adv (o + 1 + j)))

/-- Block lists `x ++ x.reverse` with `|x| = m`. -/
private def pb_PB (m : ℕ) : Set (List (List Bool)) :=
  {v | ∃ x : List (List Bool), x.length = m ∧ v = x ++ x.reverse}

/-- Words encoding a block list `v ∈ PB m` followed by `g` arbitrary blocks. -/
private def pb_G (m g : ℕ) : Set (List BlockSymbol) :=
  {s | ∃ v y : List (List Bool), v ∈ pb_PB m ∧ y.length = g ∧
    s = blockWord (v ++ y)}

/-- The head program recognizing `pb_G m g` with `K` heads
`o, …, o + K - 1`. -/
private def pb_prog :
    ℕ → ℕ → ℕ → ℕ → List pb_Instr
  | _, 0, _, _ => []
  | o, K + 1, m, g =>
    if m = 0 then List.replicate (g - 1) (.adv o)
    else pb_peelProg o K (min m K) (2 * (m - min m K))
        (decide (g = 0)) ++
      pb_prog (o + 1) K (m - min m K) (min m K + g)

/-- The head that must see no separator at the end of
`pb_prog o K m g`. -/
private def pb_watch : ℕ → ℕ → ℕ → ℕ
  | o, 0, _ => o
  | o, K + 1, m =>
    if m = 0 then o else pb_watch (o + 1) K (m - min m K)


/-! ### `blockWord` injectivity, the base program, heads of the peel program -/

private lemma pb_D_bits_inj {b b' : List Bool}
    (h : b.map BlockSymbol.bit = b'.map BlockSymbol.bit) : b = b' :=
  (List.map_injective_iff.mpr (fun _ _ hxy => BlockSymbol.bit.inj hxy)) h

private lemma pb_D_sep_not_mem_map_bit (b : List Bool) :
    BlockSymbol.sep ∉ b.map BlockSymbol.bit := by
  intro h
  simp at h

private lemma pb_D_split : ∀ (b b' : List Bool)
    (z z' : List BlockSymbol),
    b.map BlockSymbol.bit ++ BlockSymbol.sep :: z =
      b'.map BlockSymbol.bit ++ BlockSymbol.sep :: z' → b = b' ∧ z = z'
  | [], [], z, z', h => by simpa using h
  | [], c :: cs, z, z', h => by simp at h
  | a :: as, [], z, z', h => by simp at h
  | a :: as, c :: cs, z, z', h => by
      simp only [List.map_cons, List.cons_append, List.cons.injEq, BlockSymbol.bit.injEq] at h
      obtain ⟨hac, h2⟩ := h
      obtain ⟨h3, h4⟩ := pb_D_split as cs z z' h2
      exact ⟨by rw [hac, h3], h4⟩

private lemma pb_D_blockWord_single (b : List Bool) :
    blockWord [b] = b.map BlockSymbol.bit := by
  simp [blockWord]

private lemma pb_D_blockWord_cons_cons (b c : List Bool)
    (cs : List (List Bool)) :
    blockWord (b :: c :: cs) =
      b.map BlockSymbol.bit ++ BlockSymbol.sep :: blockWord (c :: cs) := by
  simp [blockWord, List.intercalate]

private lemma pb_D_blockWord_cons (b : List Bool)
    {cs : List (List Bool)} (hcs : cs ≠ []) :
    blockWord (b :: cs) = b.map BlockSymbol.bit ++ BlockSymbol.sep :: blockWord cs := by
  cases cs with
  | nil => exact absurd rfl hcs
  | cons c cs' => exact pb_D_blockWord_cons_cons b c cs'

private lemma pb_D_blockWord_inj : ∀ (A B : List (List Bool)), A ≠ [] →
    B ≠ [] →
    blockWord A = blockWord B → A = B := by
  intro A
  induction A with
  | nil => intro B hA; exact absurd rfl hA
  | cons a A' ih =>
    intro B _ hB h
    cases B with
    | nil => exact absurd rfl hB
    | cons b B' =>
      cases A' with
      | nil =>
        cases B' with
        | nil =>
          rw [pb_D_blockWord_single, pb_D_blockWord_single] at h
          rw [pb_D_bits_inj h]
        | cons b' B'' =>
          rw [pb_D_blockWord_single, pb_D_blockWord_cons_cons] at h
          exfalso
          have : BlockSymbol.sep ∈ a.map BlockSymbol.bit := by rw [h]; simp
          exact pb_D_sep_not_mem_map_bit a this
      | cons a' A'' =>
        cases B' with
        | nil =>
          rw [pb_D_blockWord_single, pb_D_blockWord_cons_cons] at h
          exfalso
          have : BlockSymbol.sep ∈ b.map BlockSymbol.bit := by rw [← h]; simp
          exact pb_D_sep_not_mem_map_bit b this
        | cons b' B'' =>
          rw [pb_D_blockWord_cons_cons, pb_D_blockWord_cons_cons] at h
          obtain ⟨h1, h2⟩ := pb_D_split _ _ _ _ h
          have h3 := ih (b' :: B'') (by simp) (by simp) h2
          rw [h1, h3]

/-- `blockWord` is injective on nonempty block lists. -/
private lemma pb_blockWord_inj {A B : List (List Bool)} (hA : A ≠ [])
    (hB : B ≠ [])
    (h : blockWord A = blockWord B) : A = B :=
  pb_D_blockWord_inj A B hA hB h

/-- `n` successive `adv`'s on one list. -/
private def pb_D_dropB : ℕ → List BlockSymbol →
    Option (List BlockSymbol)
  | 0, z => some z
  | n + 1, z => (pb_execAdv z).bind
                  (pb_D_dropB n)

private lemma pb_D_exec_replicate_adv (o : ℕ) : ∀ (n : ℕ)
    (r : ℕ → List BlockSymbol),
    pb_execProg (List.replicate n
        (pb_Instr.adv o)) r =
      (pb_D_dropB n (r o)).map (fun z => Function.update r o z) := by
  intro n
  induction n with
  | zero => intro r; simp [pb_execProg,
              pb_D_dropB]
  | succ n ih =>
    intro r
    simp only [List.replicate_succ, pb_execProg,
        pb_execInstr, pb_D_dropB]
    cases h : pb_execAdv (r o) with
    | none => simp
    | some z =>
      simp only [Option.map_some, Option.bind_some]
      rw [ih]
      simp

private lemma pb_D_execAdv_of_eq : ∀ (b : List Bool)
    (z : List BlockSymbol),
    pb_execAdv (b.map BlockSymbol.bit ++ BlockSymbol.sep :: z) = some z
  | [], z => by simp [pb_execAdv]
  | x :: b, z => by simp [pb_execAdv,
                      pb_D_execAdv_of_eq b z]

private lemma pb_D_exists_of_execAdv : ∀ (s z : List BlockSymbol),
    pb_execAdv s = some z →
      ∃ b : List Bool, s = b.map BlockSymbol.bit ++ BlockSymbol.sep :: z
  | [], z, h => by simp [pb_execAdv] at h
  | BlockSymbol.sep :: s', z, h => by
      simp only [pb_execAdv, Option.some.injEq] at h
      exact ⟨[], by simp [h]⟩
  | BlockSymbol.bit x :: s', z, h => by
      simp only [pb_execAdv] at h
      obtain ⟨b, hb⟩ := pb_D_exists_of_execAdv s' z h
      exact ⟨x :: b, by simp [hb]⟩

private lemma pb_D_no_sep : ∀ (s : List BlockSymbol), BlockSymbol.sep ∉
    s →
    ∃ b : List Bool, s = b.map BlockSymbol.bit
  | [], _ => ⟨[], rfl⟩
  | BlockSymbol.sep :: s', h => absurd (by simp) h
  | BlockSymbol.bit x :: s', h => by
      obtain ⟨b, hb⟩ := pb_D_no_sep s'
          (fun hh => h (List.mem_cons_of_mem _ hh))
      exact ⟨x :: b, by simp [hb]⟩

private lemma pb_D_dropB_iff : ∀ (n : ℕ) (s : List BlockSymbol),
    (∃ z, pb_D_dropB n s = some z ∧ BlockSymbol.sep ∉ z) ↔
      ∃ y : List (List Bool), y.length = n + 1 ∧ s = blockWord y := by
  intro n
  induction n with
  | zero =>
    intro s
    simp only [pb_D_dropB, Option.some.injEq, exists_eq_left']
    constructor
    · intro h
      obtain ⟨b, hb⟩ := pb_D_no_sep s h
      exact ⟨[b], rfl, by rw [hb, pb_D_blockWord_single]⟩
    · rintro ⟨y, hy, hs⟩
      cases y with
      | nil => simp at hy
      | cons b y' =>
        have : y' = [] := List.length_eq_zero_iff.mp (by simpa using hy)
        subst this
        rw [hs, pb_D_blockWord_single]
        exact pb_D_sep_not_mem_map_bit b
  | succ n ih =>
    intro s
    constructor
    · rintro ⟨z, hz, hsep⟩
      simp only [pb_D_dropB] at hz
      cases h : pb_execAdv s with
      | none => rw [h] at hz; simp at hz
      | some z' =>
        rw [h] at hz
        simp only [Option.bind_some] at hz
        obtain ⟨b, hb⟩ := pb_D_exists_of_execAdv s z' h
        obtain ⟨y', hy', hz'⟩ := (ih z').mp ⟨z, hz, hsep⟩
        refine ⟨b :: y', by simp [hy'], ?_⟩
        have hne : y' ≠ [] := by
          intro h0; rw [h0] at hy'; simp at hy'
        rw [pb_D_blockWord_cons b hne, ← hz', hb]
    · rintro ⟨y, hy, hs⟩
      cases y with
      | nil => simp at hy
      | cons b y' =>
        have hy'' : y'.length = n + 1 := by simpa using hy
        have hne : y' ≠ [] := by
          intro h0; rw [h0] at hy''; simp at hy''
        rw [pb_D_blockWord_cons b hne] at hs
        have h1 : pb_execAdv s = some (blockWord y') := by
          rw [hs]; exact pb_D_execAdv_of_eq b _
        obtain ⟨z, hz, hsep⟩ := (ih (blockWord y')).mpr ⟨y', hy'', rfl⟩
        refine ⟨z, ?_, hsep⟩
        simp only [pb_D_dropB]
        rw [h1]
        simpa using hz

private lemma pb_D_exists_map {α β : Type} (X : Option α) (f : α → β)
    (P : β → Prop) :
    (∃ r', X.map f = some r' ∧ P r') ↔ ∃ z, X = some z ∧ P (f z) := by
  cases X <;> simp

/-- The base program recognizes exactly the words with `g` arbitrary blocks. -/
private lemma pb_base {o g : ℕ} (hg : 1 ≤ g) (r : ℕ → List BlockSymbol)
    (s : List BlockSymbol)
    (hr : r o = s) :
    (∃ r', pb_execProg (List.replicate (g - 1) (.adv o)) r = some r' ∧
      BlockSymbol.sep ∉ r' o) ↔ s ∈ pb_G 0 g := by
  have hPB : ∀ v, v ∈ pb_PB 0 ↔ v = [] := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : x = [] := List.length_eq_zero_iff.mp hx
      simp [this]
    · rintro rfl
      exact ⟨[], rfl, rfl⟩
  have hG : s ∈ pb_G 0 g ↔ ∃ y : List (List Bool), y.length = g ∧ s =
      blockWord y := by
    constructor
    · rintro ⟨v, y, hv, hy, hs⟩
      rw [(hPB v).mp hv] at hs
      exact ⟨y, hy, by simpa using hs⟩
    · rintro ⟨y, hy, hs⟩
      exact ⟨[], y, (hPB []).mpr rfl, hy, by simpa using hs⟩
  rw [hG, pb_D_exec_replicate_adv,
      pb_D_exists_map]
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← hr]
  simpa using pb_D_dropB_iff n (r o)

/-- All instructions of `pb_peelProg` only mention heads `≤ o + k` and
compare distinct heads. -/
private lemma pb_peelProg_ok {o k p N : ℕ} {e : Bool} (hpk : p ≤ k) :
    ∀ i ∈ pb_peelProg o k p N e,
        pb_Instr.Ok (o + k + 1) i := by
  intro i hi
  simp only [pb_peelProg, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_replicate,
    List.mem_range, List.mem_reverse] at hi
  rcases hi with ((⟨_, rfl⟩ | ⟨j, hj, hi⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, hi⟩
  · simp only [pb_Instr.Ok]; omega
  · obtain ⟨_, rfl⟩ := hi
    simp only [pb_Instr.Ok]; omega
  · simp only [pb_Instr.Ok]; omega
  · obtain ⟨_, rfl⟩ := hi
    simp only [pb_Instr.Ok]; omega

/-! ### The interpreter automaton of a head program -/

/-- States: `inl i` = about to execute instruction `i`; `inr true` = flush phase (accepting);
`inr false` = dead. -/
private def pb_A_stage (n j : ℕ) : Fin n ⊕ Bool :=
  if h : j < n then Sum.inl ⟨j, h⟩ else Sum.inr true

private def pb_A_nm {K : ℕ} (obs : Fin K → Option BlockSymbol) :
    Finset (Fin K) :=
  Finset.univ.filter (fun i => obs i ≠ none)

private def pb_A_hd (K watch : ℕ) (hw : watch < K) (h : ℕ) : Fin K :=
  if hh : h < K then ⟨h, hh⟩ else ⟨watch, hw⟩

private def pb_A_step {K : ℕ}
    (prog : List pb_Instr) (watch : ℕ) (hw : watch < K) :
    (Fin prog.length ⊕ Bool) → (Fin K → Option BlockSymbol) → (Fin prog.length ⊕ Bool) ×
        Finset (Fin K)
  | Sum.inr false, obs => (Sum.inr false, pb_A_nm obs)
  | Sum.inr true, obs =>
      (if obs (pb_A_hd K watch hw watch) = some BlockSymbol.sep then
        Sum.inr false
        else Sum.inr true, pb_A_nm obs)
  | Sum.inl i, obs =>
      match prog.get i with
      | .adv h =>
          match obs (pb_A_hd K watch hw h) with
          | some (BlockSymbol.bit _) => (Sum.inl i, {pb_A_hd K watch hw h})
          | some BlockSymbol.sep => (pb_A_stage prog.length (i.val + 1), {pb_A_hd K watch hw h})
          | none => (Sum.inr false, pb_A_nm obs)
      | .cmp a b last =>
          match obs (pb_A_hd K watch hw a),
              obs (pb_A_hd K watch hw b) with
          | some (BlockSymbol.bit x), some (BlockSymbol.bit x') =>
              if x = x' then (Sum.inl i, {pb_A_hd K watch hw a,
                               pb_A_hd K watch hw b})
              else (Sum.inr false, pb_A_nm obs)
          | some BlockSymbol.sep, some BlockSymbol.sep =>
              if last then (Sum.inr false, pb_A_nm obs)
              else (pb_A_stage prog.length (i.val + 1),
                {pb_A_hd K watch hw a,
                    pb_A_hd K watch hw b})
          | some BlockSymbol.sep, none =>
              if last then (pb_A_stage prog.length (i.val + 1),
                {pb_A_hd K watch hw a,
                    pb_A_hd K watch hw b})
              else (Sum.inr false, pb_A_nm obs)
          | _, _ => (Sum.inr false, pb_A_nm obs)

private lemma pb_A_step_moves {K : ℕ} (prog : List pb_Instr) (watch : ℕ) (hw : watch < K)
    (q : (Fin prog.length ⊕ Bool)) (obs : Fin K → Option BlockSymbol) (hobs : ∃ i, obs i ≠ none) :
    ∃ i ∈ (pb_A_step prog watch hw q obs).2, obs i ≠ none := by
  obtain ⟨j, hj⟩ := hobs
  have hnm : ∃ i ∈ pb_A_nm obs, obs i ≠ none := ⟨j, by simp [pb_A_nm, hj], hj⟩
  rcases q with i | b
  · simp only [pb_A_step]
    generalize prog.get i = ins
    rcases ins with h | ⟨a, b, last⟩
    · dsimp only
      generalize pb_A_hd K watch hw h = hh
      split
      · rename_i heq
        exact ⟨hh, by simp, by rw [heq]; simp⟩
      · rename_i heq
        exact ⟨hh, by simp, by rw [heq]; simp⟩
      · exact hnm
    · dsimp only
      generalize pb_A_hd K watch hw a = ha
      generalize pb_A_hd K watch hw b = hb
      split
      · rename_i heq1 heq2
        split
        · exact ⟨ha, by simp, by rw [heq1]; simp⟩
        · exact hnm
      · rename_i heq1 heq2
        split
        · exact hnm
        · exact ⟨ha, by simp, by rw [heq1]; simp⟩
      · rename_i heq1 heq2
        split
        · exact ⟨ha, by simp, by rw [heq1]; simp⟩
        · exact hnm
      · exact hnm
  · cases b
    · exact hnm
    · exact hnm

private def pb_A_machine {K : ℕ}
    (prog : List pb_Instr) (watch : ℕ) (hw : watch < K) :
    MultiheadAutomaton K BlockSymbol (Fin prog.length ⊕ Bool) where
  init := pb_A_stage prog.length 0
  accepting := {Sum.inr true}
  step := pb_A_step prog watch hw
  moves_nonempty := pb_A_step_moves prog watch hw

/-! ### Basic semantics of the interpreter automaton -/

/-- `r j` is the remaining input of head `j`. -/
private def pb_A_Suf {K : ℕ} {Q : Type} (w : List BlockSymbol)
    (c : HeadConfig K Q)
    (r : ℕ → List BlockSymbol) : Prop :=
  ∀ j : Fin K, w.drop (c.pos j) = r j.val

private lemma pb_A_observe {K : ℕ} {Q : Type} {w : List BlockSymbol}
    {c : HeadConfig K Q}
    {r : ℕ → List BlockSymbol} (hs : pb_A_Suf w c r) (j : Fin K) :
    MultiheadAutomaton.observe w c.pos j = (r j.val).head? := by
  rw [← hs j]
  simp [MultiheadAutomaton.observe, List.head?_drop]

private lemma pb_A_terminated_iff {K : ℕ} {Q : Type}
    {w : List BlockSymbol} {c : HeadConfig K Q}
    {r : ℕ → List BlockSymbol} (hs : pb_A_Suf w c r) :
    MultiheadAutomaton.Terminated w c ↔ ∀ j : Fin K, r j.val = [] := by
  unfold MultiheadAutomaton.Terminated
  refine forall_congr' fun j => ?_
  rw [pb_A_observe hs j]
  simp

private lemma pb_A_next_nt {K : ℕ} {Q : Type} (A : MultiheadAutomaton K
    BlockSymbol Q)
    (w : List BlockSymbol) (c : HeadConfig K Q) (hnt : ¬ MultiheadAutomaton.Terminated w c) :
    A.next w c = ⟨(A.step c.state (MultiheadAutomaton.observe w c.pos)).1,
      fun i => if i ∈ (A.step c.state (MultiheadAutomaton.observe w c.pos)).2 ∧
        MultiheadAutomaton.observe w c.pos i ≠ none then c.pos i + 1 else c.pos i⟩ := by
  unfold MultiheadAutomaton.next
  rw [ite_eq_right hnt]

private lemma pb_A_next_term {K : ℕ} {Q : Type} (A : MultiheadAutomaton
    K BlockSymbol Q)
    (w : List BlockSymbol) (c : HeadConfig K Q) (ht : MultiheadAutomaton.Terminated w c) :
    A.next w c = c := by
  unfold MultiheadAutomaton.next
  rw [ite_eq_left ht]

private lemma pb_A_iterate_terminated {K : ℕ} {Q : Type}
    (A : MultiheadAutomaton K BlockSymbol Q)
    {w : List BlockSymbol} {c : HeadConfig K Q} (h : MultiheadAutomaton.Terminated w c) (t : ℕ) :
    (A.next w)^[t] c = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, pb_A_next_term A
                   w c h]

/-- One step of the automaton: the new state and the new remaining inputs. -/
private lemma pb_A_next_suf {K : ℕ} {Q : Type} (A : MultiheadAutomaton
    K BlockSymbol Q)
    {w : List BlockSymbol} {c : HeadConfig K Q} {r : ℕ → List BlockSymbol}
    (hs : pb_A_Suf w c r) (hnt : ¬ MultiheadAutomaton.Terminated w c)
        (r' : ℕ → List BlockSymbol)
    (hr' : ∀ j : Fin K, r' j.val =
      if j ∈ (A.step c.state (MultiheadAutomaton.observe w c.pos)).2 then (r j.val).tail
      else r j.val) :
    (A.next w c).state = (A.step c.state (MultiheadAutomaton.observe w c.pos)).1 ∧
      pb_A_Suf w (A.next w c) r' := by
  rw [pb_A_next_nt A w c hnt]
  refine ⟨rfl, fun j => ?_⟩
  change w.drop (if j ∈ (A.step c.state (MultiheadAutomaton.observe w c.pos)).2 ∧
    MultiheadAutomaton.observe w c.pos j ≠ none then c.pos j + 1 else c.pos j) = r' j.val
  rw [hr' j]
  by_cases hj : j ∈ (A.step c.state (MultiheadAutomaton.observe w c.pos)).2
  · by_cases hobs : MultiheadAutomaton.observe w c.pos j = none
    · have hr : r j.val = [] := by
        rw [pb_A_observe hs j] at hobs
        simpa using hobs
      simp only [hobs, ne_eq, not_true_eq_false, and_false, ite_false, hj, hr]
      rw [← hs j] at hr
      simpa using hr
    · simp only [hj, hobs, ne_eq, not_false_eq_true, and_self, ite_true]
      rw [← hs j, List.tail_drop]
  · simp only [hj, false_and, ite_false]
    exact hs j

section

variable {K : ℕ} (prog : List pb_Instr) (watch : ℕ) (hw : watch < K)
    (w : List BlockSymbol)

/-- From this configuration the automaton is never again in the accepting state (from some time
on). -/
private def pb_A_Never (c : HeadConfig K (Fin prog.length ⊕ Bool)) :
    Prop :=
  ∃ t0, ∀ t, t0 ≤ t →
    (((pb_A_machine prog watch hw).next w)^[t] c).state ≠ Sum.inr true

private lemma pb_A_never_shift
    (c : HeadConfig K (Fin prog.length ⊕ Bool)) (s : ℕ)
    (h : pb_A_Never prog watch hw w
        (((pb_A_machine prog watch hw).next w)^[s] c)) :
    pb_A_Never prog watch hw w c := by
  obtain ⟨t0, ht0⟩ := h
  refine ⟨s + t0, fun t ht => ?_⟩
  have : ((pb_A_machine prog watch hw).next w)^[t] c =
      ((pb_A_machine prog watch hw).next w)^[t - s]
        (((pb_A_machine prog watch hw).next w)^[s] c) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [this]
  exact ht0 _ (by omega)

private lemma pb_A_dead_forever
    (c : HeadConfig K (Fin prog.length ⊕ Bool))
    (h : c.state = Sum.inr false) (t : ℕ) :
    (((pb_A_machine prog watch hw).next w)^[t] c).state = Sum.inr
        false := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases hterm : MultiheadAutomaton.Terminated w
        (((pb_A_machine prog watch hw).next w)^[t] c)
    · rw [pb_A_next_term _ w _ hterm]
      exact ih
    · rw [pb_A_next_nt _ w _ hterm]
      change (pb_A_step prog watch hw _ _).1 = _
      rw [ih]
      simp [pb_A_step]

private lemma pb_A_never_of_dead
    (c : HeadConfig K (Fin prog.length ⊕ Bool))
    (h : c.state = Sum.inr false) : pb_A_Never prog watch hw w c :=
  ⟨0, fun t _ => by rw [pb_A_dead_forever prog watch hw w c h t]; simp⟩

private lemma pb_A_never_of_fail
    (c : HeadConfig K (Fin prog.length ⊕ Bool))
    (hc : c.state ≠ Sum.inr true)
    (hf : ¬ MultiheadAutomaton.Terminated w c →
      (pb_A_step prog watch hw c.state (MultiheadAutomaton.observe w
          c.pos)).1 = Sum.inr false) :
    pb_A_Never prog watch hw w c := by
  by_cases hterm : MultiheadAutomaton.Terminated w c
  · refine ⟨0, fun t _ => ?_⟩
    rw [pb_A_iterate_terminated _ hterm t]
    exact hc
  · apply pb_A_never_shift prog watch hw w c 1
    rw [Function.iterate_one]
    apply pb_A_never_of_dead
    rw [pb_A_next_nt _ w _ hterm]
    exact hf hterm

end

/-! ### The instruction lemmas -/

section

variable {K : ℕ} (prog : List pb_Instr) (watch : ℕ) (hw : watch < K)
    (w : List BlockSymbol)

private lemma pb_A_hd_val {h : ℕ} (hh : h < K) :
    (pb_A_hd K watch hw h).val = h := by
  simp [pb_A_hd, hh]

/-- The instruction `adv h`, by induction on the remaining input of head `h`. -/
private lemma pb_A_adv (i : Fin prog.length) (h : ℕ) (hh : h < K)
    (hi : prog.get i = .adv h) :
    ∀ (z : List BlockSymbol) (c : HeadConfig K (Fin prog.length ⊕ Bool)) (r : ℕ → List BlockSymbol),
      c.state = Sum.inl i → pb_A_Suf w c r → r h = z →
      (∀ z', pb_execAdv z = some z' → ∃ t,
        (((pb_A_machine prog watch hw).next w)^[t] c).state =
            pb_A_stage prog.length (i.val + 1) ∧
        pb_A_Suf w (((pb_A_machine prog watch hw).next w)^[t] c) (Function.update r h z')) ∧
      (pb_execAdv z = none → pb_A_Never prog watch hw w c) := by
  intro z
  induction z with
  | nil =>
    intro c r hst hs hz
    refine ⟨fun z' hz' => by simp [pb_execAdv] at hz', fun _ => ?_⟩
    refine pb_A_never_of_fail prog watch hw w c (by rw [hst]; simp)
        (fun _ => ?_)
    have hobs : MultiheadAutomaton.observe w c.pos (pb_A_hd K watch hw
        h) = none := by
      rw [pb_A_observe hs, pb_A_hd_val
          watch hw hh, hz]; rfl
    change (pb_A_step prog watch hw c.state _).1 = _
    rw [hst]
    simp only [pb_A_step, hi, hobs]
  | cons s z ih =>
    intro c r hst hs hz
    have hobs : MultiheadAutomaton.observe w c.pos (pb_A_hd K watch hw
        h) = some s := by
      rw [pb_A_observe hs, pb_A_hd_val
          watch hw hh, hz]; rfl
    have hnt : ¬ MultiheadAutomaton.Terminated w c := fun ht => by
      have := ht (pb_A_hd K watch hw h)
      rw [hobs] at this
      simp at this
    have hjS : ∀ j : Fin K, j ∈ ({pb_A_hd K watch hw h} :
        Finset (Fin K)) ↔ j.val = h := by
      intro j
      simp [Fin.ext_iff, pb_A_hd_val watch hw hh]
    have hr' : ∀ j : Fin K, Function.update r h z j.val =
        if j ∈ ({pb_A_hd K watch hw h} : Finset (Fin K)) then (r j.val).tail else r j.val := by
      intro j
      by_cases hj : j.val = h
      · rw [ite_eq_left ((hjS j).2 hj), hj, hz]; simp
      · rw [ite_eq_right (fun hm => hj ((hjS j).1 hm))]
        exact Function.update_of_ne hj _ _
    cases s with
    | sep =>
      have hstep : (pb_A_machine prog watch hw).step c.state
          (MultiheadAutomaton.observe w c.pos) =
          (pb_A_stage prog.length (i.val + 1), {pb_A_hd K watch hw h}) := by
        rw [hst]
        change pb_A_step prog watch hw (Sum.inl i) _ = _
        simp only [pb_A_step, hi, hobs]
      obtain ⟨hst', hs'⟩ := pb_A_next_suf (pb_A_machine prog watch hw) hs hnt _
        (by intro j; rw [hstep]; exact hr' j)
      refine ⟨fun z' hz' => ?_, fun hz' => by simp [pb_execAdv] at hz'⟩
      have hz'' : z = z' := by simpa [pb_execAdv] using hz'
      subst hz''
      refine ⟨1, ?_, ?_⟩
      · rw [Function.iterate_one, hst', hstep]
      · rw [Function.iterate_one]; exact hs'
    | bit b =>
      have hstep : (pb_A_machine prog watch hw).step c.state
          (MultiheadAutomaton.observe w c.pos) =
          (Sum.inl i, {pb_A_hd K watch hw h}) := by
        rw [hst]
        change pb_A_step prog watch hw (Sum.inl i) _ = _
        simp only [pb_A_step, hi, hobs]
      obtain ⟨hst', hs'⟩ := pb_A_next_suf
          (pb_A_machine prog watch hw) hs hnt _
        (by intro j; rw [hstep]; exact hr' j)
      have ih' := ih ((pb_A_machine prog watch hw).next w c)
          (Function.update r h z)
        (by rw [hst', hstep]) hs' (by simp)
      refine ⟨fun z' hz' => ?_, fun hz' => ?_⟩
      · obtain ⟨t, ht1, ht2⟩ := ih'.1 z' (by simpa [pb_execAdv] using
                                               hz')
        refine ⟨t + 1, ?_, ?_⟩
        · rw [Function.iterate_succ_apply]; exact ht1
        · rw [Function.iterate_succ_apply]; simpa [Function.update_idem] using ht2
      · have := ih'.2 (by simpa [pb_execAdv] using hz')
        exact pb_A_never_shift prog watch hw w c 1
            (by rw [Function.iterate_one]; exact this)

end

private lemma pb_A_update2_tail {r : ℕ → List BlockSymbol} {a b : ℕ}
    (hab : a ≠ b) (j : ℕ) :
    Function.update (Function.update r a (r a).tail) b (r b).tail j =
      if j = a ∨ j = b then (r j).tail else r j := by
  by_cases hjb : j = b
  · subst hjb
    simp
  · by_cases hja : j = a
    · subst hja
      simp [hjb]
    · simp [hja, hjb]

private lemma pb_A_update2_idem {r : ℕ → List BlockSymbol} {a b : ℕ}
    (hab : a ≠ b)
    (x y x' y' : List BlockSymbol) :
    Function.update (Function.update (Function.update (Function.update r a x) b y) a x') b y' =
      Function.update (Function.update r a x') b y' := by
  funext j
  by_cases hjb : j = b
  · subst hjb
    simp
  · by_cases hja : j = a
    · subst hja
      simp [hjb]
    · simp [hja, hjb]

section

variable {K : ℕ} (prog : List pb_Instr) (watch : ℕ) (hw : watch < K)
    (w : List BlockSymbol)

/-- The instruction `cmp a b last`, by induction on the remaining input of head `a`. -/
private lemma pb_A_cmp (i : Fin prog.length) (a b : ℕ) (last : Bool)
    (ha : a < K) (hb : b < K)
    (hab : a ≠ b) (hi : prog.get i = .cmp a b last) :
    ∀ (za zb : List BlockSymbol) (c : HeadConfig K (Fin prog.length ⊕ Bool))
      (r : ℕ → List BlockSymbol),
      c.state = Sum.inl i → pb_A_Suf w c r → r a = za → r b = zb →
      (∀ p, pb_execCmp last za zb = some p → ∃ t,
        (((pb_A_machine prog watch hw).next w)^[t] c).state =
            pb_A_stage prog.length (i.val + 1) ∧
        pb_A_Suf w (((pb_A_machine prog watch hw).next w)^[t] c)
          (Function.update (Function.update r a p.1) b p.2)) ∧
      (pb_execCmp last za zb = none → pb_A_Never prog watch hw w c) := by
  have hda := pb_A_hd_val watch hw ha
  have hdb := pb_A_hd_val watch hw hb
  have hjS : ∀ j : Fin K,
      j ∈ ({pb_A_hd K watch hw a, pb_A_hd K watch hw b} : Finset (Fin K)) ↔
        (j.val = a ∨ j.val = b) := by
    intro j
    simp [Fin.ext_iff, hda, hdb]
  intro za
  induction za with
  | nil =>
    intro zb c r hst hs hza hzb
    refine ⟨fun p hp => by simp [pb_execCmp] at hp, fun _ => ?_⟩
    refine pb_A_never_of_fail prog watch hw w c (by rw [hst]; simp)
        (fun _ => ?_)
    have hobsa : MultiheadAutomaton.observe w c.pos (pb_A_hd K watch hw
        a) = none := by
      rw [pb_A_observe hs, hda, hza]; rfl
    change (pb_A_step prog watch hw c.state _).1 = _
    rw [hst]
    simp only [pb_A_step, hi, hobsa]
  | cons s za ih =>
    intro zb c r hst hs hza hzb
    have hobsa : MultiheadAutomaton.observe w c.pos (pb_A_hd K watch hw
        a) = some s := by
      rw [pb_A_observe hs, hda, hza]; rfl
    have hobsb : MultiheadAutomaton.observe w c.pos (pb_A_hd K watch hw
        b) = zb.head? := by
      rw [pb_A_observe hs, hdb, hzb]
    have hnt : ¬ MultiheadAutomaton.Terminated w c := fun ht => by
      have := ht (pb_A_hd K watch hw a)
      rw [hobsa] at this
      simp at this
    have hfail : (pb_A_step prog watch hw (Sum.inl i)
        (MultiheadAutomaton.observe w c.pos)).1 = Sum.inr false →
        pb_A_Never prog watch hw w c := fun hf =>
      pb_A_never_of_fail prog watch hw w c (by rw [hst]; simp)
          (fun _ => by
        show (pb_A_step prog watch hw c.state _).1 = _
        rw [hst]; exact hf)
    have hsucc : ∀ q : (Fin prog.length ⊕ Bool),
        pb_A_step prog watch hw (Sum.inl i) (MultiheadAutomaton.observe
            w c.pos) =
          (q, {pb_A_hd K watch hw a,
              pb_A_hd K watch hw b}) →
        ((pb_A_machine prog watch hw).next w c).state = q ∧
        pb_A_Suf w ((pb_A_machine prog
            watch hw).next w c)
          (Function.update (Function.update r a (r a).tail) b (r b).tail) := by
      intro q hq
      have hstep : (pb_A_machine prog watch hw).step c.state
          (MultiheadAutomaton.observe w c.pos) =
          (q, {pb_A_hd K watch hw a,
              pb_A_hd K watch hw b}) := by
        rw [hst]; exact hq
      obtain ⟨h1, h2⟩ := pb_A_next_suf
          (pb_A_machine prog watch hw) hs hnt _ (by
        intro j
        rw [hstep]
        change Function.update (Function.update r a (r a).tail) b (r b).tail j.val =
          if j ∈ ({pb_A_hd K watch hw a,
              pb_A_hd K watch hw b} : Finset (Fin K))
            then (r j.val).tail else r j.val
        rw [pb_A_update2_tail hab]
        by_cases hj : j.val = a ∨ j.val = b
        · rw [ite_eq_left hj, ite_eq_left ((hjS j).2 hj)]
        · rw [ite_eq_right hj, ite_eq_right (fun hm => hj ((hjS j).1 hm))])
      exact ⟨by rw [h1, hstep], h2⟩
    cases s with
    | bit x =>
      cases zb with
      | nil =>
        have hb' : MultiheadAutomaton.observe w c.pos (pb_A_hd K watch hw b) = none := by
          rw [hobsb]; rfl
        refine ⟨fun p hp => by simp [pb_execCmp] at hp,
            fun _ => hfail ?_⟩
        simp only [pb_A_step, hi, hobsa, hb']
      | cons s' zb =>
        cases s' with
        | bit x' =>
          have hb' : MultiheadAutomaton.observe w c.pos (pb_A_hd K
              watch hw b) =
              some (BlockSymbol.bit x') := by
            rw [hobsb]; rfl
          by_cases hxx : x = x'
          · subst hxx
            have hq : pb_A_step prog watch hw (Sum.inl i)
                (MultiheadAutomaton.observe w c.pos) =
                (Sum.inl i, {pb_A_hd K watch hw a, pb_A_hd K watch hw b}) := by
              simp only [pb_A_step, hi, hobsa, hb', ite_true]
            obtain ⟨hst', hs'⟩ := hsucc _ hq
            have ih' := ih zb ((pb_A_machine prog watch hw).next w c)
              (Function.update (Function.update r a (r a).tail) b (r b).tail) hst' hs'
              (by rw [Function.update_of_ne hab, Function.update_self, hza]; rfl)
              (by rw [Function.update_self, hzb]; rfl)
            refine ⟨fun p hp => ?_, fun hp => ?_⟩
            · have hp' : pb_execCmp last za zb = some p := by
                simpa [pb_execCmp] using hp
              obtain ⟨t, ht1, ht2⟩ := ih'.1 p hp'
              refine ⟨t + 1, ?_, ?_⟩
              · rw [Function.iterate_succ_apply]; exact ht1
              · rw [Function.iterate_succ_apply]
                rwa [pb_A_update2_idem hab] at ht2
            · have hp' : pb_execCmp last za zb = none := by
                simpa [pb_execCmp] using hp
              exact pb_A_never_shift prog watch hw w c 1
                (by rw [Function.iterate_one]; exact ih'.2 hp')
          · refine ⟨fun p hp => by simp [pb_execCmp, hxx] at hp, fun _ => hfail ?_⟩
            simp only [pb_A_step, hi, hobsa, hb', hxx, ite_false]
        | sep =>
          have hb' : MultiheadAutomaton.observe w c.pos (pb_A_hd K watch hw b) =
              some BlockSymbol.sep := by
            rw [hobsb]; rfl
          refine ⟨fun p hp => by simp [pb_execCmp] at hp, fun _ => hfail ?_⟩
          simp only [pb_A_step, hi, hobsa, hb']
    | sep =>
      cases zb with
      | nil =>
        have hb' : MultiheadAutomaton.observe w c.pos (pb_A_hd K watch hw b) = none := by
          rw [hobsb]; rfl
        by_cases hl : last = true
        · have hq : pb_A_step prog watch hw (Sum.inl i) (MultiheadAutomaton.observe w c.pos) =
              (pb_A_stage prog.length (i.val + 1),
                {pb_A_hd K watch hw a, pb_A_hd K watch hw b}) := by
            simp only [pb_A_step, hi, hobsa, hb', hl, ite_true]
          obtain ⟨hst', hs'⟩ := hsucc _ hq
          refine ⟨fun p hp => ?_, fun hp => by simp [pb_execCmp, hl] at hp⟩
          obtain rfl : (za, ([] : List BlockSymbol)) = p := by
            simpa [pb_execCmp, hl] using hp
          refine ⟨1, ?_, ?_⟩
          · rw [Function.iterate_one]; exact hst'
          · rw [Function.iterate_one]
            simpa [hza, hzb] using hs'
        · refine ⟨fun p hp => by simp [pb_execCmp, hl] at hp,
            fun _ => hfail ?_⟩
          simp only [pb_A_step, hi, hobsa, hb', hl, Bool.false_eq_true,
              ite_false]
      | cons s' zb =>
        cases s' with
        | bit x' =>
          have hb' : MultiheadAutomaton.observe w c.pos (pb_A_hd K
              watch hw b) =
              some (BlockSymbol.bit x') := by
            rw [hobsb]; rfl
          refine ⟨fun p hp => by simp [pb_execCmp] at hp,
              fun _ => hfail ?_⟩
          simp only [pb_A_step, hi, hobsa, hb']
        | sep =>
          have hb' : MultiheadAutomaton.observe w c.pos (pb_A_hd K
              watch hw b) =
              some BlockSymbol.sep := by
            rw [hobsb]; rfl
          by_cases hl : last = true
          · refine ⟨fun p hp => by simp [pb_execCmp, hl] at hp,
              fun _ => hfail ?_⟩
            simp only [pb_A_step, hi, hobsa, hb', hl, ite_true]
          · have hq : pb_A_step prog watch hw (Sum.inl i)
              (MultiheadAutomaton.observe w c.pos) =
                (pb_A_stage prog.length (i.val + 1),
                  {pb_A_hd K watch hw a,
                      pb_A_hd K watch hw b}) := by
              simp only [pb_A_step, hi, hobsa, hb', hl,
                  Bool.false_eq_true, ite_false]
            obtain ⟨hst', hs'⟩ := hsucc _ hq
            refine ⟨fun p hp => ?_, fun hp => by simp [pb_execCmp, hl]
                                                   at hp⟩
            obtain rfl : (za, zb) = p := by
              simpa [pb_execCmp, hl] using hp
            refine ⟨1, ?_, ?_⟩
            · rw [Function.iterate_one]; exact hst'
            · rw [Function.iterate_one]
              simpa [hza, hzb] using hs'

end

section

variable {K : ℕ} (prog : List pb_Instr) (watch : ℕ) (hw : watch < K)
    (w : List BlockSymbol)

/-- One instruction, success and failure. -/
private lemma pb_A_instr (i : Fin prog.length)
    (hok : pb_Instr.Ok K (prog.get i))
    (c : HeadConfig K (Fin prog.length ⊕ Bool)) (r : ℕ → List BlockSymbol)
    (hst : c.state = Sum.inl i) (hs : pb_A_Suf w c r) :
    (∀ r', pb_execInstr (prog.get i) r = some r' → ∃ t,
      (((pb_A_machine prog watch hw).next w)^[t] c).state =
          pb_A_stage prog.length (i.val + 1) ∧
      pb_A_Suf w (((pb_A_machine prog
          watch hw).next w)^[t] c) r') ∧
    (pb_execInstr (prog.get i) r = none →
        pb_A_Never prog watch hw w c) := by
  rcases hins : prog.get i with h | ⟨a, b, last⟩
  · rw [hins] at hok
    have hh : h < K := hok
    have key := pb_A_adv prog watch hw w i h hh hins (r h) c r hst hs
        rfl
    refine ⟨fun r' hr' => ?_, fun hn => ?_⟩
    · simp only [pb_execInstr, Option.map_eq_some_iff] at hr'
      obtain ⟨z', hz', rfl⟩ := hr'
      exact key.1 z' hz'
    · simp only [pb_execInstr, Option.map_eq_none_iff] at hn
      exact key.2 hn
  · rw [hins] at hok
    obtain ⟨ha, hb, hab⟩ := hok
    have key := pb_A_cmp prog watch hw w i a b last ha hb hab hins
        (r a) (r b) c r hst hs rfl rfl
    refine ⟨fun r' hr' => ?_, fun hn => ?_⟩
    · simp only [pb_execInstr, Option.map_eq_some_iff] at hr'
      obtain ⟨p, hp, rfl⟩ := hr'
      exact key.1 p hp
    · simp only [pb_execInstr, Option.map_eq_none_iff] at hn
      exact key.2 hn

/-- The whole program, by downward induction on the program counter. -/
private lemma pb_A_prog_from (hprog : ∀ ins ∈ prog,
    pb_Instr.Ok K ins) :
    ∀ (d j : ℕ), prog.length - j = d → j ≤ prog.length →
    ∀ (c : HeadConfig K (Fin prog.length ⊕ Bool)) (r : ℕ → List BlockSymbol),
      c.state = pb_A_stage prog.length j →
          pb_A_Suf w c r →
      (∀ r', pb_execProg (prog.drop j) r = some r' → ∃ t,
          (((pb_A_machine prog watch hw).next w)^[t] c).state = Sum.inr
              true ∧
          pb_A_Suf w (((pb_A_machine prog
              watch hw).next w)^[t] c) r') ∧
      (pb_execProg (prog.drop j) r = none →
          pb_A_Never prog watch hw w c) := by
  intro d
  induction d with
  | zero =>
    intro j hd hj c r hst hs
    have hjn : j = prog.length := by omega
    subst hjn
    simp only [List.drop_length, pb_execProg,
        pb_A_stage, lt_irrefl, dite_false] at hst ⊢
    refine ⟨fun r' hr' => ?_, fun hn => by simp at hn⟩
    obtain rfl : r = r' := Option.some.inj hr'
    exact ⟨0, hst, hs⟩
  | succ d ih =>
    intro j hd hj c r hst hs
    have hjl : j < prog.length := by omega
    have hst' : c.state = Sum.inl ⟨j, hjl⟩ := by
      rw [hst]; simp [pb_A_stage, hjl]
    have hdrop : prog.drop j = prog.get ⟨j, hjl⟩ :: prog.drop (j + 1) :=
      List.drop_eq_getElem_cons hjl
    have hok : pb_Instr.Ok K (prog.get ⟨j, hjl⟩) :=
        hprog _ (List.get_mem _ _)
    have hins := pb_A_instr prog watch hw w ⟨j, hjl⟩ hok c r hst' hs
    have hexec : pb_execProg (prog.drop j) r =
        (pb_execInstr (prog.get ⟨j, hjl⟩) r).bind
        (pb_execProg (prog.drop (j + 1))) := by
      rw [hdrop]; rfl
    rw [hexec]
    cases hex : pb_execInstr (prog.get ⟨j, hjl⟩) r with
    | none =>
      refine ⟨fun r' hr' => by simp at hr', fun _ => hins.2 hex⟩
    | some r₁ =>
      obtain ⟨t₁, ht1, hs1⟩ := hins.1 r₁ hex
      have ih' := ih (j + 1) (by omega) (by omega)
        (((pb_A_machine prog watch hw).next w)^[t₁] c) r₁ ht1 hs1
      refine ⟨fun r' hr' => ?_, fun hn => ?_⟩
      · have hr'' : pb_execProg (prog.drop (j + 1)) r₁ = some r' := hr'
        obtain ⟨t₂, ht2, hs2⟩ := ih'.1 r' hr''
        refine ⟨t₂ + t₁, ?_, ?_⟩
        · rw [Function.iterate_add_apply]; exact ht2
        · rw [Function.iterate_add_apply]; exact hs2
      · have hn'' : pb_execProg (prog.drop (j + 1)) r₁ = none := hn
        exact pb_A_never_shift prog watch hw w c t₁ (ih'.2 hn'')

/-- In the flush phase the state stays `fin` as long as the watched head sees no separator. -/
private lemma pb_A_fin_stay (c : HeadConfig K (Fin prog.length ⊕ Bool))
    (hst : c.state = Sum.inr true)
    (hnosep : BlockSymbol.sep ∉ w.drop (c.pos ⟨watch, hw⟩)) (t : ℕ) :
    (((pb_A_machine prog watch hw).next w)^[t] c).state = Sum.inr true
        ∧
    BlockSymbol.sep ∉ w.drop ((((pb_A_machine prog watch hw).next
        w)^[t] c).pos ⟨watch, hw⟩) := by
  induction t with
  | zero => exact ⟨hst, hnosep⟩
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Function.iterate_succ_apply']
    set c' := ((pb_A_machine prog watch hw).next w)^[t] c with hc'
    by_cases hterm : MultiheadAutomaton.Terminated w c'
    · rw [pb_A_next_term _ w _ hterm]
      exact ⟨ih1, ih2⟩
    · rw [pb_A_next_nt _ w _ hterm]
      have hobs : MultiheadAutomaton.observe w c'.pos ⟨watch, hw⟩ =
          (w.drop (c'.pos ⟨watch, hw⟩)).head? := by
        simp [MultiheadAutomaton.observe, List.head?_drop]
      have hne : ¬ MultiheadAutomaton.observe w c'.pos ⟨watch, hw⟩ = some BlockSymbol.sep := by
        rw [hobs]
        intro h
        apply ih2
        cases hl : w.drop (c'.pos ⟨watch, hw⟩) with
        | nil => rw [hl] at h; simp at h
        | cons s l =>
          rw [hl] at h
          have h' : s = BlockSymbol.sep := Option.some.inj h
          rw [h']
          simp
      have hhd : pb_A_hd K watch hw watch = ⟨watch, hw⟩ := by
        simp [pb_A_hd, hw]
      refine ⟨?_, ?_⟩
      · change (pb_A_step prog watch hw c'.state _).1 = _
        rw [ih1]
        simp only [pb_A_step, hhd, hne, ite_false]
      · change BlockSymbol.sep ∉ w.drop (if (⟨watch, hw⟩ : Fin K) ∈
          ((pb_A_machine prog watch hw).step c'.state
              (MultiheadAutomaton.observe w c'.pos)).2 ∧
          MultiheadAutomaton.observe w c'.pos ⟨watch, hw⟩ ≠ none then
            c'.pos ⟨watch, hw⟩ + 1 else c'.pos ⟨watch, hw⟩)
        split_ifs
        · rw [← List.tail_drop]
          exact fun hm => ih2 (List.mem_of_mem_tail hm)
        · exact ih2

/-- If the watched head will see a separator, the flush phase ends in the dead state. -/
private lemma pb_A_fin_dead : ∀ (z : List BlockSymbol), BlockSymbol.sep
    ∈ z →
    ∀ (c : HeadConfig K (Fin prog.length ⊕ Bool)), c.state = Sum.inr true →
      w.drop (c.pos ⟨watch, hw⟩) = z → pb_A_Never prog watch hw w c :=
          by
  intro z
  induction z with
  | nil => intro h; simp at h
  | cons s z ih =>
    intro hz c hst hdrop
    have hobs : MultiheadAutomaton.observe w c.pos ⟨watch, hw⟩ = some s := by
      simp [MultiheadAutomaton.observe, ← List.head?_drop, hdrop]
    have hnt : ¬ MultiheadAutomaton.Terminated w c := fun ht => by
      have := ht ⟨watch, hw⟩
      rw [hobs] at this
      simp at this
    have hhd : pb_A_hd K watch hw watch = ⟨watch, hw⟩ := by
      simp [pb_A_hd, hw]
    have hmem : (⟨watch, hw⟩ : Fin K) ∈ pb_A_nm
        (MultiheadAutomaton.observe w c.pos) := by
      simp [pb_A_nm, hobs]
    have hpos : ((pb_A_machine prog watch hw).next w c).pos ⟨watch, hw⟩
        =
        c.pos ⟨watch, hw⟩ + 1 := by
      rw [pb_A_next_nt _ w _ hnt]
      change (if (⟨watch, hw⟩ : Fin K) ∈
          ((pb_A_machine prog watch hw).step c.state
              (MultiheadAutomaton.observe w c.pos)).2 ∧
          MultiheadAutomaton.observe w c.pos ⟨watch, hw⟩ ≠ none then
            c.pos ⟨watch, hw⟩ + 1 else c.pos ⟨watch, hw⟩) = _
      have : ((pb_A_machine prog watch hw).step c.state
          (MultiheadAutomaton.observe w c.pos)).2 =
            pb_A_nm (MultiheadAutomaton.observe w c.pos) := by
        rw [hst]; rfl
      rw [this, ite_eq_left ⟨hmem, by rw [hobs]; simp⟩]
    cases s with
    | sep =>
      apply pb_A_never_shift prog watch hw w c 1
      rw [Function.iterate_one]
      apply pb_A_never_of_dead
      rw [pb_A_next_nt _ w _ hnt]
      change (pb_A_step prog watch hw c.state _).1 = _
      rw [hst]
      simp only [pb_A_step, hhd, hobs, ite_true]
    | bit b =>
      have hz' : BlockSymbol.sep ∈ z := by
        rcases List.mem_cons.1 hz with h | h
        · cases h
        · exact h
      have hst1 : ((pb_A_machine prog watch hw).next w c).state =
          Sum.inr true := by
        rw [pb_A_next_nt _ w _ hnt]
        change (pb_A_step prog watch hw c.state _).1 = _
        rw [hst]
        simp only [pb_A_step, hhd, hobs]
        simp
      apply pb_A_never_shift prog watch hw w c 1
      rw [Function.iterate_one]
      refine ih hz' _ hst1 ?_
      rw [hpos, ← List.tail_drop, hdrop]
      rfl

/-- `Accepts` means that the state is eventually always `fin`. -/
private lemma pb_A_accepts_iff :
    (pb_A_machine prog watch hw).Accepts w ↔
      ∃ t0, ∀ t, t0 ≤ t → ((pb_A_machine prog watch hw).run w t).state
          = Sum.inr true := by
  constructor
  · rintro ⟨t, hterm, hacc⟩
    refine ⟨t, fun t' ht' => ?_⟩
    have : (pb_A_machine prog watch hw).run w t' =
        (pb_A_machine prog watch hw).run w t := by
      calc (pb_A_machine prog watch hw).run w t'
          = ((pb_A_machine prog watch hw).next w)^[t' - t]
              ((pb_A_machine prog watch hw).run w t) := by
            unfold MultiheadAutomaton.run
            rw [← Function.iterate_add_apply]
            congr 1
            omega
        _ = (pb_A_machine prog watch hw).run w t :=
            pb_A_iterate_terminated _ hterm _
    rw [this]
    exact hacc
  · rintro ⟨t0, ht0⟩
    refine ⟨max t0 (K * w.length + 1), ?_, ?_⟩
    · have h1 := MultiheadAutomaton.terminated_run (pb_A_machine prog
        watch hw) w
      unfold MultiheadAutomaton.run
      have h2 : max t0 (K * w.length + 1) = (max t0 (K * w.length + 1) - (K * w.length + 1)) +
          (K * w.length + 1) := by omega
      rw [h2, Function.iterate_add_apply]
      have h3 : MultiheadAutomaton.Terminated w
          (((pb_A_machine prog watch hw).next w)^[K * w.length + 1]
            (pb_A_machine prog watch hw).start) := h1
      rw [pb_A_iterate_terminated _ h3]
      exact h3
    · exact ht0 _ (le_max_left _ _)

end

/-- A well-formed head program is implemented by a finite-state automaton with the same heads. -/
private lemma pb_interpreter {K : ℕ}
    (prog : List pb_Instr)
    (hprog : ∀ i ∈ prog, pb_Instr.Ok K i) {watch : ℕ} (hw : watch < K)
        :
    ∃ (Q : Type) (_ : Fintype Q) (C : MultiheadAutomaton K BlockSymbol Q), ∀ w,
      C.Accepts w ↔ ∃ r', pb_execProg prog (fun _ => w) = some r' ∧
        BlockSymbol.sep ∉ r' watch := by
  refine ⟨Fin prog.length ⊕ Bool, inferInstance, pb_A_machine prog
      watch hw, fun w => ?_⟩
  rw [pb_A_accepts_iff]
  have hstart : pb_A_Suf w (pb_A_machine
      prog watch hw).start (fun _ => w) := fun j => by
    simp [MultiheadAutomaton.start, pb_A_machine]
  have hstate : (pb_A_machine prog watch hw).start.state =
      pb_A_stage prog.length 0 := rfl
  have key := pb_A_prog_from prog watch hw w hprog (prog.length - 0) 0
      rfl (Nat.zero_le _)
    _ _ hstate hstart
  rw [List.drop_zero] at key
  -- if the start configuration is `Never`, there is no `t0`
  have hnever : pb_A_Never prog watch hw w
      (pb_A_machine prog watch hw).start →
      ¬ ∃ t0, ∀ t, t0 ≤ t → ((pb_A_machine prog watch hw).run w
          t).state = Sum.inr true := by
    rintro ⟨t1, ht1⟩ ⟨t0, ht0⟩
    exact ht1 (max t0 t1) (le_max_right _ _) (ht0 (max t0 t1) (le_max_left _ _))
  cases hex : pb_execProg prog (fun _ => w) with
  | none =>
    refine ⟨fun h => (hnever (key.2 hex) h).elim, fun h => ?_⟩
    obtain ⟨r', h', _⟩ := h
    simp at h'
  | some r' =>
    obtain ⟨t1, hst1, hs1⟩ := key.1 r' hex
    by_cases hsep : BlockSymbol.sep ∈ r' watch
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · exfalso
        have hn1 := pb_A_fin_dead prog watch hw w (r' watch) hsep _
            hst1 (hs1 ⟨watch, hw⟩)
        exact hnever (pb_A_never_shift prog watch hw w _ t1 hn1) h
      · obtain ⟨r'', h', hn⟩ := h
        obtain rfl : r' = r'' := Option.some.inj h'
        exact absurd hsep hn
    · refine ⟨fun _ => ⟨r', rfl, hsep⟩, fun _ => ⟨t1, fun t ht => ?_⟩⟩
      have := (pb_A_fin_stay prog watch hw w _ hst1
        (by rw [hs1 ⟨watch, hw⟩]; exact hsep) (t - t1)).1
      have h1 : ((pb_A_machine prog watch hw).run w t) =
          ((pb_A_machine prog watch hw).next w)^[t - t1]
            (((pb_A_machine prog watch hw).next w)^[t1]
                (pb_A_machine prog watch hw).start) := by
        unfold MultiheadAutomaton.run
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      rw [h1]
      exact this

/-! ### Soundness of the peel program -/

private lemma pb_B_blockWord_cons (b : List Bool)
    (A : List (List Bool)) :
    blockWord (b :: A) =
      b.map BlockSymbol.bit ++ (if A = [] then [] else BlockSymbol.sep :: blockWord A) := by
  cases A with
  | nil => simp [blockWord]
  | cons c A =>
    simp [blockWord, List.intercalate]

private lemma pb_B_exists_blockWord (w : List BlockSymbol) :
    ∃ bs : List (List Bool), bs ≠ [] ∧ w = blockWord bs := by
  induction w with
  | nil => exact ⟨[[]], by simp, by simp [blockWord]⟩
  | cons s w ih =>
    obtain ⟨bs, hbs, hw⟩ := ih
    cases s with
    | bit b =>
      cases bs with
      | nil => exact absurd rfl hbs
      | cons c A =>
        refine ⟨(b :: c) :: A, by simp, ?_⟩
        rw [pb_B_blockWord_cons, hw,
            pb_B_blockWord_cons]
        simp
    | sep =>
      refine ⟨[] :: bs, by simp, ?_⟩
      rw [pb_B_blockWord_cons, hw]
      simp [hbs]

private lemma pb_B_execAdv_append_bits (b : List Bool)
    (z : List BlockSymbol) :
    pb_execAdv (b.map BlockSymbol.bit ++ z) =
        pb_execAdv z := by
  induction b with
  | nil => simp
  | cons x b ih => simpa [pb_execAdv] using ih

private lemma pb_B_execAdv_blockWord (b : List Bool)
    (A : List (List Bool)) :
    pb_execAdv (blockWord (b :: A)) = if A = [] then none else
      some (blockWord A) := by
  rw [pb_B_blockWord_cons, pb_B_execAdv_append_bits]
  by_cases hA : A = []
  · simp [hA, pb_execAdv]
  · simp [hA, pb_execAdv]

/-- `n`-fold block skipping. -/
private def pb_B_dropB : ℕ → List BlockSymbol →
    Option (List BlockSymbol)
  | 0, z => some z
  | n + 1, z => (pb_execAdv z).bind
                  (pb_B_dropB n)

private lemma pb_B_dropB_blockWord (j : ℕ) :
    ∀ (bs : List (List Bool)), bs ≠ [] →
      pb_B_dropB j (blockWord bs) =
        if j < bs.length then some (blockWord (bs.drop j)) else none := by
  induction j with
  | zero =>
    intro bs hbs
    have : 0 < bs.length := List.length_pos_iff.mpr hbs
    simp [pb_B_dropB, this]
  | succ j ih =>
    intro bs hbs
    cases bs with
    | nil => exact absurd rfl hbs
    | cons b A =>
      rw [pb_B_dropB, pb_B_execAdv_blockWord]
      by_cases hA : A = []
      · simp [hA]
      · rw [ite_eq_right hA, Option.bind_some, ih A hA]
        simp

private lemma pb_B_execProg_append
    (A B : List pb_Instr) (r : ℕ → List BlockSymbol) :
    pb_execProg (A ++ B) r = (pb_execProg
        A r).bind (pb_execProg B) := by
  induction A generalizing r with
  | nil => simp [pb_execProg]
  | cons i A ih =>
    simp only [List.cons_append, pb_execProg]
    cases pb_execInstr i r with
    | none => simp
    | some r₁ => simp [ih]

private lemma pb_B_execProg_replicate_adv (n h : ℕ)
    (r : ℕ → List BlockSymbol) :
    pb_execProg (List.replicate n (.adv h)) r =
      (pb_B_dropB n (r h)).map (Function.update r h) := by
  induction n generalizing r with
  | zero => simp [pb_execProg, pb_B_dropB]
  | succ n ih =>
    simp only [List.replicate_succ, pb_execProg,
        pb_execInstr, pb_B_dropB]
    cases hz : pb_execAdv (r h) with
    | none => simp
    | some z =>
      simp only [Option.map_some, Option.bind_some]
      rw [ih]
      have hfun : Function.update (Function.update r h z) h = Function.update r h := by
        funext v
        simp
      simp [hfun]

private lemma pb_B_execCmp_append_bits (last : Bool) (b b' : List Bool)
    (ta tb : List BlockSymbol)
    (hta : ta = [] ∨ ∃ z, ta = BlockSymbol.sep :: z)
    (htb : tb = [] ∨ ∃ z, tb = BlockSymbol.sep :: z) :
    pb_execCmp last (b.map BlockSymbol.bit ++ ta)
        (b'.map BlockSymbol.bit ++ tb) =
      if b = b' then pb_execCmp last ta tb else none := by
  induction b generalizing b' with
  | nil =>
    cases b' with
    | nil => simp
    | cons x b' =>
      rcases hta with rfl | ⟨z, rfl⟩ <;> simp [pb_execCmp]
  | cons x b ih =>
    cases b' with
    | nil =>
      rcases htb with rfl | ⟨z, rfl⟩ <;> simp [pb_execCmp]
    | cons x' b' =>
      by_cases hx : x = x'
      · subst hx
        simp [pb_execCmp, ih]
      · simp [pb_execCmp, hx]

private lemma pb_B_tail_form (A : List (List Bool)) :
    (if A = [] then ([] : List BlockSymbol) else BlockSymbol.sep :: blockWord A) = [] ∨
    ∃ z, (if A = [] then ([] : List BlockSymbol) else BlockSymbol.sep :: blockWord A) =
      BlockSymbol.sep :: z := by
  by_cases hA : A = [] <;> simp [hA]

private lemma pb_B_execCmp_blockWord (last : Bool) (b b' : List Bool)
    (A B : List (List Bool)) :
    pb_execCmp last (blockWord (b :: A)) (blockWord (b' :: B)) =
      if b = b' ∧ A ≠ [] ∧ (B = [] ↔ last = true) then some (blockWord A, blockWord B)
      else none := by
  rw [pb_B_blockWord_cons, pb_B_blockWord_cons,
    pb_B_execCmp_append_bits last b b' _ _
        (pb_B_tail_form A) (pb_B_tail_form
        B)]
  by_cases hb : b = b'
  · subst hb
    by_cases hA : A = []
    · simp [hA, pb_execCmp]
    · by_cases hB : B = []
      · subst hB
        cases last <;> simp [hA, pb_execCmp, blockWord]
      · cases last <;> simp [hA, hB, pb_execCmp]
  · simp [hb]

private lemma pb_B_cmp_step {a c : ℕ} {last : Bool} {r r₁ : ℕ →
    List BlockSymbol}
    {b b' : List Bool} {A B : List (List Bool)}
    (ha : r a = blockWord (b :: A)) (hc : r c = blockWord (b' :: B))
    (h : pb_execInstr (.cmp a c last) r = some r₁) :
    b = b' ∧ A ≠ [] ∧ (B = [] ↔ last = true) ∧
      r₁ = Function.update (Function.update r a (blockWord A)) c (blockWord B) := by
  simp only [pb_execInstr, ha, hc,
      pb_B_execCmp_blockWord] at h
  split_ifs at h with hcond
  · obtain ⟨hb, hA, hB⟩ := hcond
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨hb, hA, hB, h.symm⟩
  · simp at h

private def pb_B_segA (o p N : ℕ) :
    List pb_Instr := List.replicate (p + N) (.adv o)

private def pb_B_segB (o q : ℕ) :
    List pb_Instr :=
  (List.range q).flatMap (fun j => List.replicate j (.adv (o + 1 + j)))

private def pb_B_segC (o q : ℕ) (e : Bool) :
    List pb_Instr :=
  (List.range q).reverse.map (fun j => pb_Instr.cmp (o + 1 + j) o
                                         (e && decide (j = 0)))

private def pb_B_segD (o p q : ℕ) :
    List pb_Instr :=
  (List.range q).flatMap
    (fun j => List.replicate (if j < p then p - 1 - j else p) (.adv (o + 1 + j)))

private lemma pb_B_peelProg_eq (o k p N : ℕ) (e : Bool) :
    pb_peelProg o k p N e =
      pb_B_segA o p N ++ pb_B_segB o p ++
          pb_B_segC o p e ++ pb_B_segD o p
          k := rfl

private lemma pb_B_segB_spec (o : ℕ) (bs : List (List Bool))
    (hbs : bs ≠ []) :
    ∀ (q : ℕ) (r : ℕ → List BlockSymbol), q ≤ bs.length →
      (∀ j, j < q → r (o + 1 + j) = blockWord bs) →
      ∃ r', pb_execProg (pb_B_segB o q) r
          = some r' ∧
        (∀ j, j < q → r' (o + 1 + j) = blockWord (bs.drop j)) ∧
        (∀ h, (h < o + 1 ∨ o + 1 + q ≤ h) → r' h = r h) := by
  intro q
  induction q with
  | zero =>
    intro r _ _
    exact ⟨r, by simp [pb_B_segB,
                   pb_execProg], by simp, by simp⟩
  | succ q ih =>
    intro r hq hr
    obtain ⟨r₁, h₁, hj₁, hf₁⟩ := ih r (by omega) (fun j hj => hr j (by omega))
    have hseg : pb_B_segB o (q + 1) =
        pb_B_segB o q ++ List.replicate q (.adv (o + 1 + q)) := by
      simp [pb_B_segB, List.range_succ]
    have hq' : r₁ (o + 1 + q) = blockWord bs := by
      rw [hf₁ _ (Or.inr (le_refl _))]; exact hr q (by omega)
    rw [hseg, pb_B_execProg_append, h₁, Option.bind_some,
        pb_B_execProg_replicate_adv, hq',
      pb_B_dropB_blockWord q bs hbs, ite_eq_left (by omega)]
    refine ⟨Function.update r₁ (o + 1 + q) (blockWord (bs.drop q)), rfl, ?_, ?_⟩
    · intro j hj
      by_cases hjq : j = q
      · subst hjq; simp
      · rw [Function.update_of_ne (show o + 1 + j ≠ o + 1 + q by omega)]
        exact hj₁ j (by omega)
    · intro h hh
      rw [Function.update_of_ne (show h ≠ o + 1 + q by omega)]
      exact hf₁ h (by omega)

private lemma pb_B_segD_spec (o p : ℕ) (bs : List (List Bool))
    (hp : p < bs.length) :
    ∀ (q : ℕ) (r : ℕ → List BlockSymbol),
      (∀ j, j < q → r (o + 1 + j) = blockWord (bs.drop (if j < p then j + 1 else 0))) →
      ∃ r', pb_execProg (pb_B_segD o p q)
          r = some r' ∧
        (∀ j, j < q → r' (o + 1 + j) = blockWord (bs.drop p)) ∧
        (∀ h, (h < o + 1 ∨ o + 1 + q ≤ h) → r' h = r h) := by
  intro q
  induction q with
  | zero =>
    intro r _
    exact ⟨r, by simp [pb_B_segD,
                   pb_execProg], by simp, by simp⟩
  | succ q ih =>
    intro r hr
    obtain ⟨r₁, h₁, hj₁, hf₁⟩ := ih r (fun j hj => hr j (by omega))
    have hseg : pb_B_segD o p (q + 1) =
        pb_B_segD o p q ++
        List.replicate (if q < p then p - 1 - q else p) (.adv (o + 1 + q)) := by
      simp [pb_B_segD, List.range_succ]
    have hq' : r₁ (o + 1 + q) = blockWord (bs.drop (if q < p then q + 1 else 0)) := by
      rw [hf₁ _ (Or.inr (le_refl _))]; exact hr q (by omega)
    have hne : bs.drop (if q < p then q + 1 else 0) ≠ [] := by
      intro hnil
      rw [List.drop_eq_nil_iff] at hnil
      split_ifs at hnil <;> omega
    have hlen : (if q < p then p - 1 - q else p) <
        (bs.drop (if q < p then q + 1 else 0)).length := by
      rw [List.length_drop]
      split_ifs <;> omega
    have hidx : (if q < p then q + 1 else 0) + (if q < p then p - 1 - q else p) = p := by
      split_ifs <;> omega
    rw [hseg, pb_B_execProg_append, h₁, Option.bind_some,
        pb_B_execProg_replicate_adv, hq',
      pb_B_dropB_blockWord _ _ hne, ite_eq_left hlen, List.drop_drop,
          hidx]
    refine ⟨Function.update r₁ (o + 1 + q) (blockWord (bs.drop p)), rfl, ?_, ?_⟩
    · intro j hj
      by_cases hjq : j = q
      · subst hjq; simp
      · rw [Function.update_of_ne (show o + 1 + j ≠ o + 1 + q by omega)]
        exact hj₁ j (by omega)
    · intro h hh
      rw [Function.update_of_ne (show h ≠ o + 1 + q by omega)]
      exact hf₁ h (by omega)

private lemma pb_B_segC_spec (o p N : ℕ) (e : Bool)
    (bs : List (List Bool)) :
    ∀ (q : ℕ) (r r' : ℕ → List BlockSymbol), 1 ≤ q → q ≤ p →
      p + N + (p - q) < bs.length →
      r o = blockWord (bs.drop (p + N + (p - q))) →
      (∀ j, j < q → r (o + 1 + j) = blockWord (bs.drop j)) →
      pb_execProg (pb_B_segC o q e) r = some r' →
      (∀ j, j < q → bs[j]? = bs[p + N + (p - 1 - j)]?) ∧
      (bs.drop (p + N + p) = [] ↔ e = true) ∧
      r' o = blockWord (bs.drop (p + N + p)) ∧
      (∀ j, j < q → r' (o + 1 + j) = blockWord (bs.drop (j + 1))) ∧
      (∀ h, h ≠ o → (h < o + 1 ∨ o + 1 + q ≤ h) → r' h = r h) := by
  intro q
  induction q with
  | zero => intro r r' h1; omega
  | succ q ih =>
    intro r r' _ hqp hlt hro hrw hrun
    have hqbs : q < bs.length := by omega
    obtain ⟨b, hdq, hbq⟩ : ∃ b, bs.drop q = b :: bs.drop (q + 1) ∧ bs[q]? = some b :=
      ⟨bs[q], List.drop_eq_getElem_cons hqbs, List.getElem?_eq_getElem hqbs⟩
    obtain ⟨b', hdi, hbi⟩ : ∃ b', bs.drop (p + N + (p - (q + 1))) =
        b' :: bs.drop (p + N + (p - (q + 1)) + 1) ∧
        bs[p + N + (p - (q + 1))]? = some b' :=
      ⟨bs[p + N + (p - (q + 1))], List.drop_eq_getElem_cons hlt, List.getElem?_eq_getElem hlt⟩
    have hseg : pb_B_segC o (q + 1) e =
        pb_Instr.cmp (o + 1 + q) o (e && decide (q = 0)) ::
            pb_B_segC o q e := by
      simp [pb_B_segC, List.range_succ]
    rw [hseg, pb_execProg, Option.bind_eq_some_iff] at hrun
    obtain ⟨r₁, hr₁, hrun'⟩ := hrun
    obtain ⟨hbb, hA, hB, hr₁eq⟩ := pb_B_cmp_step (a := o + 1 + q) (c := o)
      (b := b) (b' := b') (A := bs.drop (q + 1))
      (B := bs.drop (p + N + (p - (q + 1)) + 1))
      (by rw [hrw q (by omega), hdq]) (by rw [hro, hdi]) hr₁
    have hr₁o : r₁ o = blockWord (bs.drop (p + N + (p - (q + 1)) + 1)) := by
      rw [hr₁eq]; simp
    have hr₁w : r₁ (o + 1 + q) = blockWord (bs.drop (q + 1)) := by
      rw [hr₁eq, Function.update_of_ne (show o + 1 + q ≠ o by omega)]; simp
    have hr₁f : ∀ h, h ≠ o → h ≠ o + 1 + q → r₁ h = r h := by
      intro h h1 h2
      rw [hr₁eq, Function.update_of_ne h1, Function.update_of_ne h2]
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0
      have hrr : r₁ = r' := by
        have hnil : pb_B_segC o 0 e = [] := by simp [pb_B_segC]
        rw [hnil, pb_execProg] at hrun'
        exact Option.some.inj hrun'
      subst hrr
      have hidx : p + N + (p - (0 + 1)) + 1 = p + N + p := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        obtain rfl : j = 0 := by omega
        rw [hbq, show p + N + (p - 1 - 0) = p + N + (p - (0 + 1)) by omega, hbi, hbb]
      · rw [hidx] at hB
        simpa using hB
      · rw [hr₁o, hidx]
      · intro j hj
        obtain rfl : j = 0 := by omega
        exact hr₁w
      · intro h h1 h2
        exact hr₁f h h1 (by omega)
    · have hflag : (e && decide (q = 0)) = false := by simp [hq0.ne']
      rw [hflag] at hB
      have hBne : bs.drop (p + N + (p - (q + 1)) + 1) ≠ [] := by
        intro h0
        have := hB.mp h0
        simp at this
      have hn : p + N + (p - (q + 1)) + 1 = p + N + (p - q) := by omega
      have hlt' : p + N + (p - q) < bs.length := by
        rw [← hn]
        by_contra hcon
        exact hBne (List.drop_eq_nil_iff.mpr (by omega))
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih r₁ r' hq0 (by omega) hlt' (by rw [hr₁o, hn])
        (fun j hj => by
          rw [hr₁f _ (by omega) (by omega)]
          exact hrw j (by omega)) hrun'
      refine ⟨?_, i2, i3, ?_, ?_⟩
      · intro j hj
        by_cases hjq : j = q
        · subst hjq
          rw [hbq, show p + N + (p - 1 - j) = p + N + (p - (j + 1)) by omega, hbi, hbb]
        · exact i1 j (by omega)
      · intro j hj
        by_cases hjq : j = q
        · subst hjq
          rw [i5 (o + 1 + j) (by omega) (Or.inr (by omega)), hr₁w]
        · exact i4 j (by omega)
      · intro h h1 h2
        rw [i5 h h1 (by omega), hr₁f h h1 (by omega)]

/-- Soundness of the peel program. -/
private lemma pb_peel_sound {o k p N : ℕ} {e : Bool} (hp1 : 1 ≤ p)
    (hpk : p ≤ k)
    {r r' : ℕ → List BlockSymbol} {w : List BlockSymbol}
    (hr : ∀ i, i ≤ k → r (o + i) = w)
    (h : pb_execProg (pb_peelProg o k p N
        e) r = some r') :
    ∃ x u y : List (List Bool), x.length = p ∧ u.length = N ∧ (y = [] ↔ e = true) ∧
      w = blockWord (x ++ u ++ x.reverse ++ y) ∧
      ∀ i, i < k → r' (o + 1 + i) = blockWord (u ++ x.reverse ++ y) := by
  obtain ⟨bs, hbs, hw⟩ := pb_B_exists_blockWord w
  subst hw
  have hro : r o = blockWord bs := by simpa using hr 0 (Nat.zero_le _)
  have hrj : ∀ j, j < k → r (o + 1 + j) = blockWord bs := fun j hj => by
    have := hr (j + 1) (by omega)
    rwa [show o + (j + 1) = o + 1 + j by omega] at this
  rw [pb_B_peelProg_eq, pb_B_execProg_append, pb_B_execProg_append,
    pb_B_execProg_append] at h
  have hA : pb_execProg (pb_B_segA o p N)
      r =
      (pb_B_dropB (p + N) (blockWord bs)).map (Function.update r o) :=
          by
    rw [pb_B_segA, pb_B_execProg_replicate_adv, hro]
  rw [hA, pb_B_dropB_blockWord _ bs hbs] at h
  by_cases hlen : p + N < bs.length
  swap
  · rw [ite_eq_right hlen] at h
    simp at h
  rw [ite_eq_left hlen] at h
  simp only [Option.map_some, Option.bind_some] at h
  -- segment B
  obtain ⟨r₂, hB, hBj, hBf⟩ := pb_B_segB_spec o bs hbs p
    (Function.update r o (blockWord (bs.drop (p + N)))) (by omega)
    (fun j hj => by
      rw [Function.update_of_ne (show o + 1 + j ≠ o by omega)]
      exact hrj j (by omega))
  rw [hB, Option.bind_some] at h
  obtain ⟨r₃, hC, hD⟩ := Option.bind_eq_some_iff.mp h
  have hro₂ : r₂ o = blockWord (bs.drop (p + N + (p - p))) := by
    rw [hBf o (Or.inl (by omega)), Function.update_self]
    simp
  obtain ⟨hC1, hC3, hC4, hC5, hC6⟩ := pb_B_segC_spec o p N e bs p r₂ r₃
      hp1 le_rfl
    (by omega) hro₂ hBj hC
  obtain ⟨r₄, hD', hD1, hD2⟩ := pb_B_segD_spec o p bs (by omega) k r₃
    (fun j hj => by
      by_cases hjp : j < p
      · rw [ite_eq_left hjp]
        exact hC5 j hjp
      · rw [ite_eq_right hjp, List.drop_zero, hC6 (o + 1 + j) (by omega) (Or.inr (by omega)),
          hBf (o + 1 + j) (Or.inr (by omega)),
          Function.update_of_ne (show o + 1 + j ≠ o by omega)]
        exact hrj j hj)
  rw [hD'] at hD
  have hr4 : r₄ = r' := Option.some.inj hD
  subst hr4
  -- reconstruction of the block list
  have hxl : (bs.take p).length = p := by
    simp only [List.length_take]; omega
  have hcopies : (bs.drop (p + N)).take p = (bs.take p).reverse := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < p
    · rw [List.getElem?_take_of_lt hi, List.getElem?_drop,
        List.getElem?_reverse (show i < (bs.take p).length by omega), hxl,
        List.getElem?_take_of_lt (show p - 1 - i < p by omega)]
      have := hC1 (p - 1 - i) (by omega)
      rw [show p + N + (p - 1 - (p - 1 - i)) = p + N + i by omega] at this
      exact this.symm
    · have h1 : ((bs.drop (p + N)).take p)[i]? = none :=
        List.getElem?_eq_none (by simp only [List.length_take]; omega)
      have h2 : (bs.take p).reverse[i]? = none :=
        List.getElem?_eq_none (by simp only [List.length_reverse, hxl]; omega)
      rw [h1, h2]
  have e1 : bs.drop p = (bs.drop p).take N ++ bs.drop (p + N) := by
    have := List.take_append_drop N (bs.drop p)
    rw [List.drop_drop] at this
    exact this.symm
  have e2 : bs.drop (p + N) = (bs.drop (p + N)).take p ++ bs.drop (p + N + p) := by
    have := List.take_append_drop p (bs.drop (p + N))
    rw [List.drop_drop] at this
    exact this.symm
  have hdrop : bs.drop p =
      (bs.drop p).take N ++ (bs.take p).reverse ++ bs.drop (p + N + p) := by
    rw [List.append_assoc, ← hcopies, ← e2, ← e1]
  have hlist : bs = bs.take p ++ (bs.drop p).take N ++ (bs.take p).reverse ++
      bs.drop (p + N + p) := by
    rw [List.append_assoc, List.append_assoc, ← List.append_assoc ((bs.drop p).take N), ← hdrop,
      List.take_append_drop]
  refine ⟨bs.take p, (bs.drop p).take N, bs.drop (p + N + p), hxl, ?_, hC3, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop]; omega
  · rw [← hlist]
  · intro i hi
    rw [hD1 i hi]
    exact congrArg blockWord hdrop

/-! ### Completeness of the peel program -/

private lemma pb_C_bw_single (a : List Bool) : blockWord [a] =
    a.map BlockSymbol.bit := by
  simp [blockWord]

private lemma pb_C_bw_cons_ne (a : List Bool) (z : List (List Bool))
    (hz : z ≠ []) :
    blockWord (a :: z) = a.map BlockSymbol.bit ++ BlockSymbol.sep :: blockWord z := by
  cases z with
  | nil => exact absurd rfl hz
  | cons c cs => simp [blockWord]

private lemma pb_C_execAdv_map (a : List Bool) (w : List BlockSymbol) :
    pb_execAdv (a.map BlockSymbol.bit ++ BlockSymbol.sep :: w) =
        some w := by
  induction a with
  | nil => simp [pb_execAdv]
  | cons b a ih => simpa [pb_execAdv] using ih

private lemma pb_C_execCmp_map_false (a : List Bool)
    (za zb : List BlockSymbol) :
    pb_execCmp false (a.map BlockSymbol.bit ++ BlockSymbol.sep :: za)
      (a.map BlockSymbol.bit ++ BlockSymbol.sep :: zb) = some (za, zb) := by
  induction a with
  | nil => simp [pb_execCmp]
  | cons b a ih => simpa [pb_execCmp] using ih

private lemma pb_C_execCmp_map_true (a : List Bool)
    (za : List BlockSymbol) :
    pb_execCmp true (a.map BlockSymbol.bit ++ BlockSymbol.sep :: za)
      (a.map BlockSymbol.bit) = some (za, []) := by
  induction a with
  | nil => simp [pb_execCmp]
  | cons b a ih => simpa [pb_execCmp] using ih

private lemma pb_C_execAdv_blocks (a : List Bool)
    (z : List (List Bool)) (hz : z ≠ []) :
    pb_execAdv (blockWord (a :: z)) = some (blockWord z) := by
  rw [pb_C_bw_cons_ne a z hz]
  exact pb_C_execAdv_map a _

private lemma pb_C_execCmp_blocks (last : Bool) (a : List Bool)
    (z1 z2 : List (List Bool))
    (h1 : z1 ≠ []) (h2 : (last = true → z2 = []) ∧ (last = false → z2 ≠ [])) :
    pb_execCmp last (blockWord (a :: z1)) (blockWord (a :: z2)) =
      some (blockWord z1, blockWord z2) := by
  cases last with
  | true =>
    have hz2 : z2 = [] := h2.1 rfl
    subst hz2
    rw [pb_C_bw_cons_ne a z1 h1,
        pb_C_bw_single]
    exact pb_C_execCmp_map_true a _
  | false =>
    have hz2 : z2 ≠ [] := h2.2 rfl
    rw [pb_C_bw_cons_ne a z1 h1,
        pb_C_bw_cons_ne a z2 hz2]
    exact pb_C_execCmp_map_false a _ _

private lemma pb_C_execProg_append
    (A B : List pb_Instr) (r : ℕ → List BlockSymbol) :
    pb_execProg (A ++ B) r = (pb_execProg
        A r).bind (pb_execProg B) := by
  induction A generalizing r with
  | nil => simp [pb_execProg]
  | cons i is ih =>
    simp only [List.cons_append, pb_execProg]
    cases pb_execInstr i r <;> simp [ih]

private lemma pb_C_drop_cons (bs : List (List Bool)) (t : ℕ)
    (ht : t < bs.length) :
    ∃ a, bs.drop t = a :: bs.drop (t + 1) :=
  ⟨bs[t], List.drop_eq_getElem_cons ht⟩

private lemma pb_C_drop_ne_nil (bs : List (List Bool)) (t : ℕ)
    (ht : t < bs.length) :
    bs.drop t ≠ [] := by
  simp only [ne_eq, List.drop_eq_nil_iff]
  omega

private lemma pb_C_execAdv_drop (bs : List (List Bool)) (t : ℕ)
    (ht : t + 1 < bs.length) :
    pb_execAdv (blockWord (bs.drop t)) =
        some (blockWord (bs.drop (t + 1))) := by
  obtain ⟨a, ha⟩ := pb_C_drop_cons bs t (by omega)
  rw [ha]
  exact pb_C_execAdv_blocks a _
      (pb_C_drop_ne_nil bs (t + 1) ht)

private lemma pb_C_adv_rep (bs : List (List Bool)) (h : ℕ) :
    ∀ (n t : ℕ) (r : ℕ → List BlockSymbol), r h = blockWord (bs.drop t) →
      (n = 0 ∨ t + n < bs.length) →
      pb_execProg (List.replicate n
          (pb_Instr.adv h)) r =
        some (Function.update r h (blockWord (bs.drop (t + n)))) := by
  intro n
  induction n with
  | zero =>
    intro t r hr _
    simp [pb_execProg, ← hr]
  | succ n ih =>
    intro t r hr hn
    have ht : t + 1 < bs.length := by omega
    rw [List.replicate_succ]
    simp only [pb_execProg, pb_execInstr]
    rw [hr, pb_C_execAdv_drop bs t ht]
    simp only [Option.map_some, Option.bind_some]
    rw [ih (t + 1) _ (by simp) (by omega)]
    simp only [Function.update_idem]
    rw [show t + 1 + n = t + (n + 1) by omega]

private lemma pb_C_cmp_drop (bs : List (List Bool)) (ha hb t1 t2 : ℕ)
    (last : Bool)
    (r : ℕ → List BlockSymbol)
    (h1 : r ha = blockWord (bs.drop t1)) (h2 : r hb = blockWord (bs.drop t2))
    (a : List Bool) (hd1 : bs.drop t1 = a :: bs.drop (t1 + 1))
    (hd2 : bs.drop t2 = a :: bs.drop (t2 + 1))
    (ht1 : t1 + 1 < bs.length)
    (hl : (last = true → t2 + 1 = bs.length) ∧ (last = false → t2 + 1 < bs.length)) :
    pb_execInstr (pb_Instr.cmp ha hb last)
        r =
      some (Function.update (Function.update r ha (blockWord (bs.drop (t1 + 1))))
        hb (blockWord (bs.drop (t2 + 1)))) := by
  simp only [pb_execInstr]
  rw [h1, h2, hd1, hd2, pb_C_execCmp_blocks last a _ _
      (pb_C_drop_ne_nil bs (t1 + 1) ht1)]
  · simp
  · constructor
    · intro hlast
      have := (hl.1 hlast).symm
      simp [List.drop_eq_nil_iff, this]
    · intro hlast
      exact pb_C_drop_ne_nil bs (t2 + 1) (hl.2 hlast)

private lemma pb_C_flatMap_adv (bs : List (List Bool)) (o : ℕ)
    (s c : ℕ → ℕ) :
    ∀ (q : ℕ) (r : ℕ → List BlockSymbol),
      (∀ j, j < q → r (o + 1 + j) = blockWord (bs.drop (s j))) →
      (∀ j, j < q → c j = 0 ∨ s j + c j < bs.length) →
      pb_execProg ((List.range q).flatMap
          (fun j => List.replicate (c j) (pb_Instr.adv (o + 1 + j)))) r
              =
        some (fun h => if o + 1 ≤ h ∧ h < o + 1 + q
          then blockWord (bs.drop (s (h - o - 1) + c (h - o - 1))) else r h) := by
  intro q
  induction q with
  | zero =>
    intro r _ _
    simp only [List.range_zero, List.flatMap_nil, pb_execProg]
    congr 1
    funext h
    have hn : ¬ (o + 1 ≤ h ∧ h < o + 1 + 0) := by omega
    simp only [hn, ↓reduceIte]
  | succ q ih =>
    intro r hr hc
    rw [List.range_succ, List.flatMap_append, pb_C_execProg_append]
    rw [ih r (fun j hj => hr j (by omega)) (fun j hj => hc j (by omega))]
    simp only [Option.bind_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hq : (fun h => if o + 1 ≤ h ∧ h < o + 1 + q
        then blockWord (bs.drop (s (h - o - 1) + c (h - o - 1))) else r h) (o + 1 + q)
          = blockWord (bs.drop (s q)) := by
      have hn : ¬ (o + 1 ≤ o + 1 + q ∧ o + 1 + q < o + 1 + q) := by omega
      simp only [hn, ↓reduceIte]
      exact hr q (by omega)
    rw [pb_C_adv_rep bs (o + 1 + q) (c q) (s q) _ hq (hc q (by omega))]
    congr 1
    funext h
    by_cases h1 : h = o + 1 + q
    · subst h1
      have e1 : o + 1 + q - o - 1 = q := by omega
      have h3 : o + 1 ≤ o + 1 + q ∧ o + 1 + q < o + 1 + (q + 1) := by omega
      simp only [Function.update_apply, ↓reduceIte, h3.1, h3.2, and_self, e1]
    · by_cases h2 : o + 1 ≤ h ∧ h < o + 1 + q
      · have h3 : o + 1 ≤ h ∧ h < o + 1 + (q + 1) := by omega
        simp only [Function.update_apply, h1, h2.1, h2.2, h3.2, and_self, ↓reduceIte]
      · have h3 : ¬ (o + 1 ≤ h ∧ h < o + 1 + (q + 1)) := by omega
        simp only [Function.update_apply, h1, h2, h3, ↓reduceIte]

private lemma pb_C_cmps (bs : List (List Bool)) (o p N : ℕ) (e : Bool)
    (hcopy : ∀ j, j < p → ∃ a, bs.drop j = a :: bs.drop (j + 1) ∧
      bs.drop (p + N + (p - 1 - j)) = a :: bs.drop (p + N + (p - 1 - j) + 1))
    (hT : 2 * p + N ≤ bs.length) (hp1 : 1 ≤ p)
    (hlast0 : (e = true → 2 * p + N = bs.length) ∧ (e = false → 2 * p + N < bs.length)) :
    ∀ (q : ℕ) (r : ℕ → List BlockSymbol), q ≤ p →
      r o = blockWord (bs.drop (p + N + (p - q))) →
      (∀ j, j < q → r (o + 1 + j) = blockWord (bs.drop j)) →
      pb_execProg ((List.range q).reverse.map
          (fun j => pb_Instr.cmp (o + 1 + j) o (e && decide (j = 0))))
              r =
        some (fun h => if h = o then blockWord (bs.drop (p + N + p))
          else if o + 1 ≤ h ∧ h < o + 1 + q then blockWord (bs.drop (h - o - 1 + 1))
          else r h) := by
  intro q
  induction q with
  | zero =>
    intro r _ hro _
    simp only [List.range_zero, List.reverse_nil, List.map_nil,
        pb_execProg]
    congr 1
    funext h
    by_cases h1 : h = o
    · subst h1
      simpa using hro
    · simp [h1]
  | succ q ih =>
    intro r hqp hro hw
    have hqp' : q < p := by omega
    obtain ⟨a, hd1, hd2⟩ := hcopy q hqp'
    have e1 : p + N + (p - 1 - q) = p + N + (p - (q + 1)) := by omega
    rw [e1] at hd2
    have hl : ((e && decide (q = 0)) = true → p + N + (p - (q + 1)) + 1 = bs.length) ∧
        ((e && decide (q = 0)) = false → p + N + (p - (q + 1)) + 1 < bs.length) := by
      by_cases hq0 : q = 0
      · subst hq0
        simp only [decide_true, Bool.and_true]
        constructor
        · intro he
          have := hlast0.1 he
          omega
        · intro he
          have := hlast0.2 he
          omega
      · simp only [hq0, decide_false, Bool.and_false]
        constructor
        · intro h
          exact absurd h (by simp)
        · intro _
          omega
    have hstep := pb_C_cmp_drop bs (o + 1 + q) o q
        (p + N + (p - (q + 1)))
      (e && decide (q = 0)) r (hw q (by omega)) hro a hd1 hd2 (by omega) hl
    have hrange : (List.range (q + 1)).reverse = q :: (List.range q).reverse := by
      simp [List.range_succ]
    rw [hrange, List.map_cons]
    simp only [pb_execProg]
    rw [hstep]
    simp only [Option.bind_some]
    have e2 : p + N + (p - (q + 1)) + 1 = p + N + (p - q) := by omega
    rw [e2]
    rw [ih _ (by omega) (by simp) (by
      intro j hj
      have h1 : o + 1 + j ≠ o := by omega
      have h2 : o + 1 + j ≠ o + 1 + q := by omega
      simp only [Function.update_apply, h1, h2, ↓reduceIte]
      exact hw j (by omega))]
    congr 1
    funext h
    by_cases h0 : h = o
    · simp [h0]
    · by_cases h1 : h = o + 1 + q
      · subst h1
        have e3 : o + 1 + q - o - 1 + 1 = q + 1 := by omega
        have h3 : o + 1 ≤ o + 1 + q ∧ o + 1 + q < o + 1 + (q + 1) := by omega
        simp only [Function.update_apply, h0, ↓reduceIte, h3.1, h3.2, and_self,
          lt_self_iff_false, and_false, e3]
      · by_cases h2 : o + 1 ≤ h ∧ h < o + 1 + q
        · have h3 : o + 1 ≤ h ∧ h < o + 1 + (q + 1) := by omega
          simp only [h0, h2.1, h2.2, h3.2, and_self,
            ↓reduceIte]
        · have h3 : ¬ (o + 1 ≤ h ∧ h < o + 1 + (q + 1)) := by omega
          simp only [Function.update_apply, h0, h1, h2, h3, ↓reduceIte]

private lemma pb_C_drop_of_getElem? (l : List (List Bool)) (t : ℕ)
    (a : List Bool)
    (h : l[t]? = some a) : l.drop t = a :: l.drop (t + 1) := by
  obtain ⟨ht, hta⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons ht, hta]

private lemma pb_C_hcopy (x u y : List (List Bool)) (p N : ℕ)
    (hx : x.length = p)
    (hu : u.length = N) :
    ∀ j, j < p → ∃ a, (x ++ u ++ x.reverse ++ y).drop j =
        a :: (x ++ u ++ x.reverse ++ y).drop (j + 1) ∧
      (x ++ u ++ x.reverse ++ y).drop (p + N + (p - 1 - j)) =
        a :: (x ++ u ++ x.reverse ++ y).drop (p + N + (p - 1 - j) + 1) := by
  intro j hj
  have hjx : j < x.length := by omega
  have hbs : x ++ u ++ x.reverse ++ y = x ++ (u ++ (x.reverse ++ y)) := by
    simp [List.append_assoc]
  refine ⟨x[j], ?_, ?_⟩
  · apply pb_C_drop_of_getElem?
    rw [hbs, List.getElem?_append_left hjx, List.getElem?_eq_getElem hjx]
  · apply pb_C_drop_of_getElem?
    rw [hbs, List.getElem?_append_right (by omega)]
    rw [List.getElem?_append_right (by omega)]
    have e1 : p + N + (p - 1 - j) - x.length - u.length = p - 1 - j := by omega
    rw [e1, List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_reverse (by omega)]
    have e2 : x.length - 1 - (p - 1 - j) = j := by omega
    rw [e2, List.getElem?_eq_getElem hjx]

/-- Completeness of the peel program. -/
private lemma pb_peel_complete {o k p N : ℕ} {e : Bool} (hp1 : 1 ≤ p)
    (hpk : p ≤ k)
    {r : ℕ → List BlockSymbol} {x u y : List (List Bool)}
    (hx : x.length = p) (hu : u.length = N) (hy : y = [] ↔ e = true)
    (hr : ∀ i, i ≤ k → r (o + i) = blockWord (x ++ u ++ x.reverse ++ y)) :
    ∃ r', pb_execProg (pb_peelProg o k p N
        e) r = some r' ∧
      ∀ i, i < k → r' (o + 1 + i) = blockWord (u ++ x.reverse ++ y) := by
  have hcopy := pb_C_hcopy x u y p N hx hu
  have hdrop : (x ++ u ++ x.reverse ++ y).drop p = u ++ x.reverse ++ y := by
    have : x ++ u ++ x.reverse ++ y = x ++ (u ++ x.reverse ++ y) := by
      simp [List.append_assoc]
    rw [this, List.drop_left' hx]
  have hlen : (x ++ u ++ x.reverse ++ y).length = 2 * p + N + y.length := by
    simp [hx, hu]
    omega
  generalize hbs : x ++ u ++ x.reverse ++ y = bs at hr hcopy hdrop hlen
  rw [← hdrop]
  have hlast0 : (e = true → 2 * p + N = bs.length) ∧ (e = false → 2 * p + N < bs.length) := by
    constructor
    · intro he
      have hy0 : y = [] := hy.2 he
      subst hy0
      simp only [List.length_nil] at hlen
      omega
    · intro he
      have hne : y ≠ [] := by
        intro h
        have := hy.1 h
        rw [he] at this
        exact absurd this (by simp)
      have : 0 < y.length := List.length_pos_iff.mpr hne
      omega
  have hT : 2 * p + N ≤ bs.length := by omega
  -- segment 1: the traveller goes to the start of block `p + N`
  have hseg1 := pb_C_adv_rep bs o (p + N) 0 r
      (by simpa using hr 0 (Nat.zero_le _))
    (Or.inr (by omega))
  obtain ⟨r1, h1eq⟩ : ∃ r1, r1 = Function.update r o (blockWord (bs.drop (0 + (p + N)))) :=
    ⟨_, rfl⟩
  rw [← h1eq] at hseg1
  have hr1 : ∀ j, j < k → r1 (o + 1 + j) = blockWord bs := by
    intro j hj
    have hne : o + 1 + j ≠ o := by omega
    rw [h1eq, Function.update_of_ne hne]
    have e1 : o + 1 + j = o + (j + 1) := by omega
    rw [e1]
    exact hr (j + 1) (by omega)
  -- segment 2: the waiting heads go to the starts of blocks `0, …, p-1`
  have hseg2 := pb_C_flatMap_adv bs o (fun _ => 0) (fun j => j) p r1
    (by
      intro j hj
      simpa using hr1 j (by omega))
    (by
      intro j hj
      by_cases hj0 : j = 0
      · exact Or.inl hj0
      · right
        show 0 + j < bs.length
        omega)
  obtain ⟨r2, h2eq⟩ : ∃ r2, r2 = fun h => if o + 1 ≤ h ∧ h < o + 1 + p
      then blockWord (bs.drop ((fun _ => 0) (h - o - 1) + (fun j => j) (h - o - 1)))
      else r1 h := ⟨_, rfl⟩
  rw [← h2eq] at hseg2
  have hro2 : r2 o = blockWord (bs.drop (p + N + (p - p))) := by
    have hn : ¬ (o + 1 ≤ o ∧ o < o + 1 + p) := by omega
    rw [h2eq]
    simp only [hn, ↓reduceIte]
    rw [h1eq]
    simp only [Function.update_self]
    congr 2
    omega
  have hw2 : ∀ j, j < p → r2 (o + 1 + j) = blockWord (bs.drop j) := by
    intro j hj
    have hc : o + 1 ≤ o + 1 + j ∧ o + 1 + j < o + 1 + p := by omega
    have e1 : o + 1 + j - o - 1 = j := by omega
    rw [h2eq]
    simp only [hc.1, hc.2, and_self, ↓reduceIte, e1]
    congr 2
    omega
  -- segment 3: the comparisons
  have hseg3 := pb_C_cmps bs o p N e hcopy hT hp1 hlast0 p r2 le_rfl
      hro2 hw2
  obtain ⟨r3, h3eq⟩ : ∃ r3, r3 = fun h => if h = o then blockWord (bs.drop (p + N + p))
      else if o + 1 ≤ h ∧ h < o + 1 + p then blockWord (bs.drop (h - o - 1 + 1))
      else r2 h := ⟨_, rfl⟩
  rw [← h3eq] at hseg3
  -- segment 4: all the heads `o+1, …, o+k` go to the start of block `p`
  have hseg4 := pb_C_flatMap_adv bs o
      (fun j => if j < p then j + 1 else 0)
    (fun j => if j < p then p - 1 - j else p) k r3
    (by
      intro j hj
      have hne : o + 1 + j ≠ o := by omega
      rw [h3eq]
      simp only [hne, ↓reduceIte]
      by_cases hjp : j < p
      · have hc : o + 1 ≤ o + 1 + j ∧ o + 1 + j < o + 1 + p := by omega
        have e1 : o + 1 + j - o - 1 + 1 = j + 1 := by omega
        simp only [hc.1, hc.2, and_self, ↓reduceIte, e1, hjp]
      · have hc : ¬ (o + 1 ≤ o + 1 + j ∧ o + 1 + j < o + 1 + p) := by omega
        simp only [hc, ↓reduceIte, hjp]
        rw [h2eq]
        simp only [hc, ↓reduceIte]
        rw [hr1 j hj]
        simp)
    (by
      intro j hj
      right
      by_cases hjp : j < p
      · simp only [hjp, ↓reduceIte]
        omega
      · simp only [hjp, ↓reduceIte]
        omega)
  have hrun : pb_execProg (pb_peelProg o k
      p N e) r = some (fun h =>
      if o + 1 ≤ h ∧ h < o + 1 + k
      then blockWord (bs.drop ((if h - o - 1 < p then h - o - 1 + 1 else 0) +
        (if h - o - 1 < p then p - 1 - (h - o - 1) else p))) else r3 h) := by
    unfold pb_peelProg
    rw [pb_C_execProg_append, pb_C_execProg_append, pb_C_execProg_append, hseg1]
    simp only [Option.bind_some]
    rw [hseg2]
    simp only [Option.bind_some]
    rw [hseg3]
    simp only [Option.bind_some]
    exact hseg4
  refine ⟨_, hrun, ?_⟩
  intro i hi
  have hc : o + 1 ≤ o + 1 + i ∧ o + 1 + i < o + 1 + k := by omega
  have e1 : o + 1 + i - o - 1 = i := by omega
  simp only [hc.1, hc.2, and_self, ↓reduceIte, e1]
  congr 2
  by_cases hip : i < p
  · simp only [hip, ↓reduceIte]
    omega
  · simp only [hip, ↓reduceIte]
    omega

private lemma pb_execProg_append
    (A B : List pb_Instr) (r : ℕ → List BlockSymbol) :
    pb_execProg (A ++ B) r = (pb_execProg
        A r).bind (pb_execProg B) := by
  induction A generalizing r with
  | nil => simp [pb_execProg]
  | cons i is ih =>
    simp only [List.cons_append, pb_execProg]
    cases pb_execInstr i r <;> simp [ih]

private lemma pb_choose_succ (K : ℕ) : (K + 1).choose 2 = K.choose 2 +
    K := by
  have h1 : (K + 1).choose 2 = K.choose 1 + K.choose 2 := Nat.choose_succ_succ K 1
  rw [h1, Nat.choose_one_right, add_comm]

private lemma pb_prog_ok : ∀ (K o m g : ℕ), ∀ i ∈
    pb_prog o K m g, pb_Instr.Ok (o + K)
    i := by
  intro K
  induction K with
  | zero => intro o m g i hi; simp [pb_prog] at hi
  | succ K ih =>
    intro o m g i hi
    by_cases hm : m = 0
    · simp only [pb_prog, hm, ite_true] at hi
      rw [List.mem_replicate] at hi
      obtain ⟨_, rfl⟩ := hi
      simp only [pb_Instr.Ok]
      omega
    · simp only [pb_prog, hm, ite_false, List.mem_append] at hi
      rcases hi with hi | hi
      · exact pb_peelProg_ok (min_le_right m K) i hi
      · have := ih (o + 1) (m - min m K) (min m K + g) i hi
        have hoe : o + 1 + K = o + (K + 1) := by omega
        rwa [hoe] at this

private lemma pb_watch_lt : ∀ (K o m : ℕ), 1 ≤ K → m ≤ K.choose 2 →
    o ≤ pb_watch o K m ∧ pb_watch o K m <
        o + K := by
  intro K
  induction K with
  | zero => intro o m h; omega
  | succ K ih =>
    intro o m _ hmK
    by_cases hm : m = 0
    · simp only [pb_watch, hm, ite_true]
      omega
    · simp only [pb_watch, hm, ite_false]
      have hK : 1 ≤ K := by
        rcases Nat.eq_zero_or_pos K with h | h
        · subst h
          simp [Nat.choose] at hmK
          omega
        · exact h
      have hch := pb_choose_succ K
      have hm' : m - min m K ≤ K.choose 2 := by
        rw [hch] at hmK
        omega
      have := ih (o + 1) (m - min m K) hK hm'
      omega

private lemma pb_PB_zero : pb_PB 0 =
    {[]} := by
  ext v
  simp only [pb_PB, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : x = [] := List.length_eq_zero_iff.mp hx
    simp [this]
  · rintro rfl
    exact ⟨[], rfl, rfl⟩

/-- The recursive program checks the palindromic blocks and counts the trailing blocks. -/
private lemma pb_lang : ∀ (K o m g : ℕ), 1 ≤ K → m ≤ K.choose 2 → 1 ≤
    m + g →
    ∀ (r : ℕ → List BlockSymbol) (s : List BlockSymbol), (∀ i, i < K → r (o + i) = s) →
      ((∃ r', pb_execProg (pb_prog o K m
          g) r = some r' ∧
          BlockSymbol.sep ∉ r' (pb_watch o K m)) ↔ s ∈
              pb_G m g) := by
  intro K
  induction K with
  | zero => intro o m g hK; omega
  | succ K ih =>
    intro o m g _ hmK hmg r s hr
    by_cases hm : m = 0
    · subst hm
      have hg : 1 ≤ g := by omega
      simp only [pb_prog, pb_watch,
          ite_true]
      exact pb_base hg r s (by simpa using hr 0 (by omega))
    · have hK : 1 ≤ K := by
        rcases Nat.eq_zero_or_pos K with h | h
        · subst h
          simp [Nat.choose] at hmK
          omega
        · exact h
      have hch := pb_choose_succ K
      set p := min m K with hp
      have hp1 : 1 ≤ p := by omega
      have hpK : p ≤ K := min_le_right m K
      have hpm : p ≤ m := min_le_left m K
      have hm' : m - p ≤ K.choose 2 := by
        rw [hch] at hmK
        omega
      simp only [pb_prog, pb_watch, hm,
          ite_false]
      rw [← hp]
      constructor
      · rintro ⟨r', hr', hsep⟩
        rw [pb_execProg_append] at hr'
        cases hA : pb_execProg
            (pb_peelProg o K p (2 * (m - p)) (decide (g = 0))) r with
        | none => rw [hA] at hr'; simp at hr'
        | some r₁ =>
          rw [hA] at hr'
          simp only [Option.bind_some] at hr'
          obtain ⟨x, u, y, hx, hu, hy, hs, hr₁⟩ :=
            pb_peel_sound (o := o) (k := K) (p := p) (N := 2 * (m - p))
                (e := decide (g = 0))
              hp1 hpK (r := r) (r' := r₁) (w := s)
              (fun i hi => hr i (by omega)) hA
          have hinner := (ih (o + 1) (m - p) (p + g) hK hm' (by omega) r₁
            (blockWord (u ++ x.reverse ++ y)) (fun i hi => by
              have := hr₁ i hi
              rwa [show o + 1 + i = o + 1 + i from rfl] at this)).mp ⟨r', hr', hsep⟩
          obtain ⟨v, z, hv, hz, hvz⟩ := hinner
          obtain ⟨x₂, hx₂, rfl⟩ := hv
          have hne1 : u ++ x.reverse ++ y ≠ [] := by
            intro h
            have := congrArg List.length h
            simp only [List.length_append, List.length_reverse, List.length_nil] at this
            omega
          have hne2 : (x₂ ++ x₂.reverse) ++ z ≠ [] := by
            intro h
            have := congrArg List.length h
            simp only [List.length_append, List.length_reverse, List.length_nil] at this
            omega
          have heq := pb_blockWord_inj hne1 hne2 hvz
          rw [List.append_assoc] at heq
          have hlen : u.length = (x₂ ++ x₂.reverse).length := by
            simp [hu, hx₂]
            omega
          obtain ⟨hux, hzy⟩ := List.append_inj heq hlen
          have hylen : y.length = g := by
            have := congrArg List.length hzy
            simp at this
            omega
          refine ⟨(x ++ x₂) ++ (x ++ x₂).reverse, y, ⟨x ++ x₂, ?_, rfl⟩, hylen, ?_⟩
          · simp [hx, hx₂]
            omega
          · rw [hs, hux]
            simp [List.reverse_append, List.append_assoc]
      · rintro ⟨v, y, hv, hy, hs⟩
        obtain ⟨x₀, hx₀, rfl⟩ := hv
        set x := x₀.take p with hxdef
        set x₂ := x₀.drop p with hx₂def
        have hxlen : x.length = p := by simp [hxdef]; omega
        have hx₂len : x₂.length = m - p := by simp [hx₂def]; omega
        have hx₀eq : x₀ = x ++ x₂ := (List.take_append_drop p x₀).symm
        have hvu : x₀ ++ x₀.reverse = x ++ (x₂ ++ x₂.reverse) ++ x.reverse := by
          rw [hx₀eq]
          simp [List.reverse_append, List.append_assoc]
        have hyiff : y = [] ↔ decide (g = 0) = true := by
          rw [decide_eq_true_iff]
          constructor
          · rintro rfl
            simpa using hy.symm
          · intro h
            rw [h] at hy
            exact List.length_eq_zero_iff.mp hy
        have hwd : s = blockWord (x ++ (x₂ ++ x₂.reverse) ++ x.reverse ++ y) := by
          rw [hs, hvu]
        obtain ⟨r₁, hA, hr₁⟩ :=
          pb_peel_complete (o := o) (k := K) (p := p)
              (N := 2 * (m - p)) (e := decide (g = 0))
            hp1 hpK (r := r) (x := x) (u := x₂ ++ x₂.reverse) (y := y) hxlen
            (by simp [hx₂len]; omega) hyiff
            (fun i hi => by rw [hr i (by omega), hwd])
        have hin : blockWord (x₂ ++ x₂.reverse ++ x.reverse ++ y) ∈
            pb_G (m - p) (p + g) := by
          refine ⟨x₂ ++ x₂.reverse, x.reverse ++ y, ⟨x₂, hx₂len, rfl⟩, ?_, ?_⟩
          · simp [hxlen, hy]
          · simp [List.append_assoc]
        obtain ⟨r', hr', hsep⟩ := (ih (o + 1) (m - p) (p + g) hK hm' (by omega) r₁
          (blockWord (x₂ ++ x₂.reverse ++ x.reverse ++ y)) (fun i hi => hr₁ i hi)).mpr hin
        refine ⟨r', ?_, hsep⟩
        rw [pb_execProg_append, hA]
        exact hr'

/-- **SUV p. 237.**  A `k`-head automaton recognizes `L_m` when `m ≤ k(k-1)/2`, for `m ≥ 1`. -/
theorem isRecognizedBy_palindromeBlocks {k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k.choose 2) :
    IsRecognizedBy k (palindromeBlocks m) := by
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp [Nat.choose] at hmk
      omega
    · exact h
  have hw := pb_watch_lt k 0 m hk hmk
  have hprog := pb_prog_ok k 0 m 0
  obtain ⟨Q, hQ, C, hC⟩ := pb_interpreter (K := k)
    (pb_prog 0 k m 0) (fun i hi => by simpa using hprog i hi)
    (watch := pb_watch 0 k m) (by omega)
  refine ⟨Q, hQ, C, fun w => ?_⟩
  rw [hC w, pb_lang k 0 m 0 hk hmk (by omega) (fun _ => w) w
    (fun _ _ => rfl)]
  -- the language of the head program is `palindromeBlocks m`
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨List.ofFn f ++ (List.ofFn f).reverse, [], ⟨List.ofFn f, by simp, rfl⟩, rfl, ?_⟩
    simpa using hf
  · rintro ⟨v, y, ⟨x, hx, rfl⟩, hy, hs⟩
    have hy' : y = [] := List.length_eq_zero_iff.mp hy
    subst hy'
    have key : ∀ (m : ℕ) (x : List (List Bool)), x.length = m →
        ∃ f : Fin m → List Bool, List.ofFn f = x := by
      intro m x h
      subst h
      exact ⟨x.get, List.ofFn_get x⟩
    obtain ⟨f, rfl⟩ := key m x hx
    exact ⟨f, by simpa using hs⟩

end Kolmogorov.Applications
