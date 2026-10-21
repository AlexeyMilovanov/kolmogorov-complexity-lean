/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Game

/-!
# Stack programs and the setup of their one-tape simulation

An abstract space-bounded programming model: programs over `k` binary stacks (`Instr`, `Prog`,
`PConfig`), their runs, halting and acceptance, and space bounds.  The second half starts the
simulation of a stack program by a one-tape machine (`StackSim`): the instruction functions, runs
with bounded head positions, and tapes holding lists of cells.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-! ### An abstract space-bounded programming model: stack programs -/

/-- Instructions of a stack program with `k` binary stacks; jump targets are instruction
indices. -/
inductive Instr (k : ℕ) where
  /-- Push the bit `b` on stack `r`, go to instruction `next`. -/
  | push (r : Fin k) (b : Bool) (next : ℕ)
  /-- Pop the top bit of stack `r` (no effect on an empty stack), go to `next`. -/
  | pop (r : Fin k) (next : ℕ)
  /-- Branch on the top of stack `r`: empty, `false`, or `true`. -/
  | test (r : Fin k) (ifEmpty ifFalse ifTrue : ℕ)
  /-- Halt and accept. -/
  | accept
  /-- Halt and reject. -/
  | reject

/-- A stack program: `k` stacks of bits and a list of instructions.  The input is loaded on
stack `0` (its first bit on top); execution starts at instruction `0`; a program counter outside
the code halts (rejecting). -/
structure Prog where
  /-- Number of stacks. -/
  k : ℕ
  /-- The instructions. -/
  code : List (Instr k)

/-- A configuration of a stack program: program counter and stack contents. -/
structure PConfig (P : Prog) where
  /-- The program counter. -/
  pc : ℕ
  /-- The stacks. -/
  regs : Fin P.k → BitString

/-- The space used by a configuration: the total length of the stacks. -/
def PConfig.space {P : Prog} (c : PConfig P) : ℕ := ∑ r, (c.regs r).length

/-- The initial configuration on input `x`. -/
def Prog.init (P : Prog) (x : BitString) : PConfig P := ⟨0, fun r => if r.val = 0 then x else []⟩

/-- One step of a stack program (halted configurations are fixed). -/
def Prog.step (P : Prog) (c : PConfig P) : PConfig P :=
  match P.code[c.pc]? with
  | some (.push r b n) => ⟨n, Function.update c.regs r (b :: c.regs r)⟩
  | some (.pop r n) => ⟨n, Function.update c.regs r (c.regs r).tail⟩
  | some (.test r i0 i1 i2) =>
    ⟨match c.regs r with
      | [] => i0
      | false :: _ => i1
      | true :: _ => i2, c.regs⟩
  | _ => c

/-- The configuration after `t` steps on input `x`. -/
def Prog.run (P : Prog) (x : BitString) : ℕ → PConfig P
  | 0 => P.init x
  | t + 1 => P.step (P.run x t)

/-- An accepting configuration. -/
def Prog.Accepting (P : Prog) (c : PConfig P) : Prop := P.code[c.pc]? = some .accept

/-- A halted configuration: at `accept`, at `reject`, or outside the code. -/
def Prog.Halted (P : Prog) (c : PConfig P) : Prop :=
  P.code[c.pc]? = some .accept ∨ P.code[c.pc]? = some .reject ∨ P.code[c.pc]? = none

/-- `P` halts on every input within space `2 ^ p(|x|)`. -/
def Prog.SpaceBounded (P : Prog) (p : Polynomial ℕ) : Prop :=
  ∀ x : BitString, ∃ t : ℕ, P.Halted (P.run x t) ∧ ∀ s ≤ t, (P.run x s).space ≤ 2 ^ p.eval x.length

/-- The set accepted by a stack program. -/
def Prog.Lang (P : Prog) : Set BitString := {x | ∃ t, P.Accepting (P.run x t)}

/-- Halted stack-program configurations are fixed by `step`. -/
theorem Prog.step_of_halted (P : Prog) (c : PConfig P) (h : P.Halted c) : P.step c = c := by
  unfold Prog.step
  rcases h with h | h | h <;> rw [h]

/-- Once halted, a stack program stays in the same configuration. -/
theorem Prog.run_of_halted_le (P : Prog) (x : BitString) {t s : ℕ} (hle : t ≤ s)
    (h : P.Halted (P.run x t)) : P.run x s = P.run x t := by
  induction s with
  | zero =>
    have : t = 0 := Nat.le_zero.mp hle
    subst this; rfl
  | succ s ih =>
    rcases Nat.lt_or_ge s t with hlt | hge
    · have : t = s + 1 := by omega
      subst this; rfl
    · change P.step (P.run x s) = _
      rw [ih hge, Prog.step_of_halted _ _ h]

/-- An accepting configuration is halted. -/
theorem Prog.halted_of_accepting (P : Prog) (c : PConfig P) (h : P.Accepting c) : P.Halted c :=
  Or.inl h

/-- Acceptance is read off any halted configuration. -/
theorem Prog.mem_lang_iff_of_halted (P : Prog) (x : BitString) (t : ℕ) (h : P.Halted (P.run x t)) :
    x ∈ P.Lang ↔ P.Accepting (P.run x t) := by
  constructor
  · rintro ⟨t', ht'⟩
    rcases le_total t' t with hle | hle
    · rw [P.run_of_halted_le x hle (P.halted_of_accepting _ ht')]; exact ht'
    · rw [← P.run_of_halted_le x hle h]; exact ht'
  · intro h'; exact ⟨t, h'⟩

/-! ### Simulating a stack program by a one-tape machine

The `k` stacks are kept on the tape from cell `0` on as consecutive blocks: stack `r`, top first,
as the cells `some b`, each block followed by one blank (`encT`); all other cells are blank.  The
input tape is already the encoding of the initial configuration.  One instruction is simulated by
one rightward sweep from cell `0` (find the block of the active stack by counting blanks, read its
top, and for `push` shift the rest of the encoding one cell to the right), a turn, and one leftward
sweep back to cell `-1` (for a `pop` of a nonempty stack shifting the cells after the top one cell
to the left), followed by one step to cell `0`.  The representation invariant (`repr`) is: the
state is `entry pc`, the tape is `render (encT stacks)`, the head is at `0`, the buffer is empty.
All scanned cells lie in `[-1, space + k + 1]`. -/

namespace StackSim

/-- Encoding of a list of stacks: each stack (top first) followed by one blank. -/
def encT : List BitString → List Sym
  | [] => []
  | s :: rest => s.map some ++ none :: encT rest

/-- The tape holding the list `l` from cell `0` on, blank elsewhere. -/
def render (l : List Sym) (i : ℤ) : Sym := if 0 ≤ i then l.getD i.toNat none else none

/-- Modes of the rightward sweep. -/
inductive RMode where
  /-- Looking for the block of the active stack. -/
  | nav
  /-- The top `o` of the active stack has been read. -/
  | done (o : Sym)
  /-- Pushing: shifting the encoding one cell to the right, carrying the symbol `c`. -/
  | carry (c : Sym)
  deriving DecidableEq, Fintype

/-- States of the simulating machine, for programs with `L` instructions and `K` stacks. -/
inductive SimQ (L K : ℕ) where
  /-- Rightward sweep for instruction `pc`, `cnt` blanks passed. -/
  | R (pc : Fin L) (cnt : Fin (K + 1)) (m : RMode)
  /-- Turning after the rightward sweep; `o` is the top read. -/
  | turn (pc : Fin L) (o : Sym)
  /-- Leftward sweep: `cnt` is the number of blanks among the cells `0, …, head` of the encoding;
  `del = some c`: deleting the top of the active stack, carrying `c`. -/
  | Lf (pc : Fin L) (o : Sym) (cnt : Fin (K + 1)) (del : Option Sym)
  /-- Accepting. -/
  | acc
  /-- Rejecting. -/
  | rej
  deriving DecidableEq, Fintype

section InstrFns
variable {K : ℕ}

/-- The stack an instruction works on. -/
def ireg : Instr K → ℕ
  | .push r _ _ => r.val
  | .pop r _ => r.val
  | .test r _ _ _ => r.val
  | _ => 0

/-- The mode entered at the active stack, whose top cell holds `a`. -/
def switchMode : Instr K → Sym → RMode
  | .push _ b _, _ => .carry (some b)
  | _, a => .done a

/-- Delete during the leftward sweep iff the instruction pops a nonempty stack. -/
def delMode : Instr K → Sym → Option Sym
  | .pop _ _, some _ => some none
  | _, _ => none

/-- The next instruction, given the top `o` of the active stack. -/
def nextPC : Instr K → Sym → ℕ
  | .push _ _ n, _ => n
  | .pop _ n, _ => n
  | .test _ i0 _ _, none => i0
  | .test _ _ i1 _, some false => i1
  | .test _ _ _ i2, some true => i2
  | _, _ => 0

end InstrFns

variable (P : Prog)

/-- The instruction at `pc`. -/
def instrAt (pc : Fin P.code.length) : Instr P.k := P.code[pc.1]

/-- Rightward-sweep state with counter `j` (rejecting when `j > k`). -/
def rS (pc : Fin P.code.length) (j : ℕ) (m : RMode) : SimQ P.code.length P.k :=
  if h : j ≤ P.k then .R pc ⟨j, Nat.lt_succ_of_le h⟩ m else .rej

/-- Leftward-sweep state with counter `j` (rejecting when `j > k`). -/
def lS (pc : Fin P.code.length) (o : Sym) (j : ℕ) (d : Option Sym) : SimQ P.code.length P.k :=
  if h : j ≤ P.k then .Lf pc o ⟨j, Nat.lt_succ_of_le h⟩ d else .rej

/-- The state starting the simulation of instruction `pc`. -/
def entry (pc : ℕ) : SimQ P.code.length P.k :=
  if h : pc < P.code.length then
    match P.code[pc] with
    | .accept => .acc
    | .reject => .rej
    | _ => rS P ⟨pc, h⟩ 0 .nav
  else .rej

/-- The transition function of the simulating machine. -/
def simδ : SimQ P.code.length P.k → Sym → Act (SimQ P.code.length P.k)
  | .R pc cnt .nav, a =>
    if cnt.val = ireg (instrAt P pc) then .step (.R pc cnt (switchMode (instrAt P pc) a)) a .stay
    else if a = none then .step (rS P pc (cnt.val + 1) .nav) a .right
    else .step (.R pc cnt .nav) a .right
  | .R pc cnt (.done o), a =>
    if a = none then
      (if cnt.val + 1 = P.k then .step (.turn pc o) a .right
       else .step (rS P pc (cnt.val + 1) (.done o)) a .right)
    else .step (.R pc cnt (.done o)) a .right
  | .R pc cnt (.carry c), a =>
    if cnt.val = P.k then .step (.turn pc none) c .right
    else if a = none then .step (rS P pc (cnt.val + 1) (.carry none)) c .right
    else .step (.R pc cnt (.carry a)) c .right
  | .turn pc o, a => .step (lS P pc o P.k (delMode (instrAt P pc) o)) a .left
  | .Lf pc o cnt (some c), a =>
    if a = none ∧ cnt.val = ireg (instrAt P pc) then .step (.Lf pc o cnt none) a .stay
    else if a = none then .step (lS P pc o (cnt.val - 1) (some none)) c .left
    else .step (.Lf pc o cnt (some a)) c .left
  | .Lf pc o cnt none, a =>
    if a = none then
      (if cnt.val = 0 then .step (entry P (nextPC (instrAt P pc) o)) a .right
       else .step (lS P pc o (cnt.val - 1) none) a .left)
    else .step (.Lf pc o cnt none) a .left
  | .acc, a => .step .acc a .stay
  | .rej, a => .step .rej a .stay

/-- The simulating machine. -/
def simOTM : OTM where
  Q := SimQ P.code.length P.k
  fin := inferInstance
  start := entry P 0
  accept := .acc
  reject := .rej
  δ := simδ P

/-- The configuration of the simulating machine representing the program configuration `c`. -/
def repr (c : PConfig P) : Config (simOTM P) :=
  ⟨entry P c.pc, render (encT (List.ofFn c.regs)), 0, []⟩

/-! #### Runs with bounded head positions -/

/-- `Reach M H c c'`: the machine `M` (oracle `∅`) goes from `c` to `c'`, every configuration on
the way (both ends included) having its head in `[-1, H]`. -/
inductive Reach (M : OTM) (H : ℤ) : Config M → Config M → Prop
  | refl (c : Config M) : -1 ≤ c.head → c.head ≤ H → Reach M H c c
  | next (c c' : Config M) : -1 ≤ c.head → c.head ≤ H → Reach M H (step M ∅ c) c' →
      Reach M H c c'

/-- `Reach` chains compose. -/
theorem Reach.trans {M : OTM} {H : ℤ} {c₁ c₂ c₃ : Config M} (h₁ : Reach M H c₁ c₂)
    (h₂ : Reach M H c₂ c₃) : Reach M H c₁ c₃ := by
  induction h₁ with
  | refl c _ _ => exact h₂
  | next c c' hl hh _ ih => exact Reach.next _ _ hl hh (ih h₂)

/-- A `Reach` chain is a stretch of the run, all of whose heads lie in `[-1, H]`. -/
theorem Reach.iterate {M : OTM} {H : ℤ} {c c' : Config M} (h : Reach M H c c') :
    ∃ d, (step M ∅)^[d] c = c' ∧
      ∀ e ≤ d, -1 ≤ ((step M ∅)^[e] c).head ∧ ((step M ∅)^[e] c).head ≤ H := by
  induction h with
  | refl c hl hh =>
    refine ⟨0, rfl, fun e he => ?_⟩
    obtain rfl : e = 0 := by omega
    exact ⟨hl, hh⟩
  | next c c' hl hh _ ih =>
    obtain ⟨d, hd, hb⟩ := ih
    refine ⟨d + 1, by rw [Function.iterate_succ_apply]; exact hd, fun e he => ?_⟩
    rcases e with _ | e
    · exact ⟨hl, hh⟩
    · rw [Function.iterate_succ_apply]; exact hb e (by omega)

/-- The run after `T + d` steps is `d` steps from the configuration at time `T`. -/
theorem run_add (M : OTM) (x : BitString) (T d : ℕ) :
    run M ∅ x (T + d) = (step M ∅)^[d] (run M ∅ x T) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- The configuration of an ordinary Turing machine after one step from an unhalted state is formed
by applying the transition function to the current head and tape. -/
theorem step_eq' (M : OTM) (c : Config M) (hc : ¬ Halted M c) {q' : M.Q} {a : Sym} {m : Move}
    (h : M.δ c.q (c.tape c.head) = .step q' a m) :
    step M ∅ c = ⟨q', Function.update c.tape c.head a, moveHead m c.head, c.buf⟩ := by
  unfold step
  rw [ite_eq_right hc, h]

/-- One step of the simulating machine inside a `Reach` chain. -/
theorem reach_step {H : ℤ} {q q' : SimQ P.code.length P.k} {τ : ℤ → Sym} {h : ℤ} {a : Sym}
    {mv : Move} {c' : Config (simOTM P)} (hq : q ≠ .acc ∧ q ≠ .rej)
    (hδ : simδ P q (τ h) = .step q' a mv) (hl : -1 ≤ h) (hh : h ≤ H)
    (hr : Reach (simOTM P) H ⟨q', Function.update τ h a, moveHead mv h, []⟩ c') :
    Reach (simOTM P) H ⟨q, τ, h, []⟩ c' := by
  refine Reach.next _ _ hl hh ?_
  have hc : ¬ Halted (simOTM P) ⟨q, τ, h, []⟩ := by
    rintro (h1 | h1)
    · exact hq.1 h1
    · exact hq.2 h1
  rw [step_eq' (simOTM P) ⟨q, τ, h, []⟩ hc hδ]
  exact hr

/-! #### Tapes holding lists -/

/-- Rendering a list at a natural number index yields the element at that index or `none` if out of
bounds. -/
theorem render_natCast (l : List Sym) (n : ℕ) : render l n = l.getD n none := by
  simp [render]

/-- Rendering a list at the negative index `-1` always yields `none`. -/
theorem render_neg_one (l : List Sym) : render l (-1) = none := by
  simp [render]

/-- Modifying the element of a list immediately following a prefix does not affect the elements
retrieved at any other index. -/
theorem getElem?_mid_ne (pre post : List Sym) (a b : Sym) (n : ℕ) (hn : n ≠ pre.length) :
    (pre ++ a :: post)[n]? = (pre ++ b :: post)[n]? := by
  rcases Nat.lt_or_gt_of_ne hn with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right h.le, List.getElem?_append_right h.le]
    obtain ⟨m, hm⟩ : ∃ m, n - pre.length = m + 1 := ⟨n - pre.length - 1, by omega⟩
    rw [hm]; rfl

/-- Rendering a list constructed by appending a symbol and a suffix to a prefix at the length of
the prefix returns the appended symbol. -/
theorem render_mid (pre post : List Sym) (a : Sym) :
    render (pre ++ a :: post) (pre.length : ℤ) = a := by
  rw [render_natCast, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

/-- Updating the rendered list at the length of a prefix with a new symbol yields the rendered list
with the symbol replaced. -/
theorem update_render_mid (pre post : List Sym) (a b : Sym) :
    Function.update (render (pre ++ a :: post)) (pre.length : ℤ) b = render (pre ++ b :: post) := by
  funext i
  by_cases hi : i = pre.length
  · subst hi; rw [Function.update_self, render_mid]
  · rw [Function.update_of_ne hi]
    unfold render
    split_ifs with h0
    · have hne : i.toNat ≠ pre.length := by
        intro he; apply hi; rw [← he, Int.toNat_of_nonneg h0]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        getElem?_mid_ne pre post a b _ hne]
    · rfl

/-- Rendering a list at an index that corresponds to the end of a prefix returns the symbol
immediately following the prefix. -/
theorem render_at {L pre rest : List Sym} {a : Sym} {h : ℤ} (hL : L = pre ++ a :: rest)
    (hh : h = pre.length) : render L h = a := by
  subst hL hh; exact render_mid pre rest a

/-- Updating a rendered list at an index that corresponds to the end of a prefix returns the
rendered list with the symbol at that position replaced. -/
theorem update_at {L pre rest : List Sym} {a : Sym} (b : Sym) {h : ℤ}
    (hL : L = pre ++ a :: rest) (hh : h = pre.length) :
    Function.update (render L) h b = render (pre ++ b :: rest) := by
  subst hL hh; exact update_render_mid pre rest a b

/-- Updating a rendered list at any position with the symbol already present at that position does
not alter the rendered list. -/
theorem update_read (L : List Sym) (h : ℤ) : Function.update (render L) h (render L h) = render L :=
  Function.update_eq_self _ _

/-- Appending a `none` symbol to a list does not change its rendered representation. -/
theorem render_append_none (l : List Sym) : render (l ++ [none]) = render l := by
  funext i
  unfold render
  split_ifs with h0
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i.toNat l.length with h | h
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_append_right h, List.getElem?_eq_none h]
      rcases Nat.lt_or_ge (i.toNat - l.length) 1 with h' | h'
      · have : i.toNat - l.length = 0 := by omega
        rw [this]; rfl
      · rw [List.getElem?_eq_none (by simpa using h')]
  · rfl

/-- Updating the rendered list at its length with a symbol is equivalent to appending that symbol
to the list. -/
theorem update_render_length (l : List Sym) (a : Sym) :
    Function.update (render l) (l.length : ℤ) a = render (l ++ [a]) := by
  have := update_render_mid l [] none a
  rw [render_append_none] at this
  exact this

end StackSim
end Kolmogorov.RandomStrings
