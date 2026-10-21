/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.StackProg

/-!
# A structured programming layer over stack programs

`Stmt k`, a goto-free language over `k` stacks; its compilation to `Instr`s; the big-step
semantics with a space bound `Exec`; runs of compiled code; whole programs from statements; and
inlining a statement along a renaming of the stacks (`Exec.rename_of_comp`).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-! ### A structured programming layer over stack programs

`Stmt k` is a structured (goto-free) language over `k` stacks: `skip`, `push`, `pop`, sequential
composition, a conditional and a while loop, both testing the top of a stack (`none` when the
stack is empty).  `Stmt.compile s a` lays `s` out as `Instr`s starting at address `a` (jumps are
absolute; an unconditional jump is a `test` with three equal targets).  `Exec s σ σ' S` is the
big-step semantics with a space bound: `s`, started on the stack contents `σ`, terminates with the
contents `σ'`, all intermediate contents (both ends included) having total length `≤ S`.

Main facts:
* `Exec.reaches` (correctness of the compiler): the compiled code, placed at address `a` inside
  any program, runs from `a` to `a + s.size` (the address just after it), transforming `σ` into
  `σ'` through configurations of space `≤ S`; runs concatenate by `Prog.Reaches.trans`;
* `Exec.seq_iff`, `Exec.ite_iff`, `Exec.loop_iff`: a composed statement terminates iff its
  components do, with the intermediate contents threaded through; `Exec.seq_max`: the space of a
  sequential composition is the max of the components' spaces; `Exec.det`: determinism;
  `Exec.space_le`, `Exec.mono`;
* `Exec.rename`, `Exec.rename_of_comp`: inlining a statement written for `k` stacks into a
  program with `k'` stacks along an injective renaming `f` (disjoint state); the other stacks are
  untouched and add their total length to the space bound;
* `Stmt.toProg`, `Stmt.toProg_spec`, `Stmt.exists_prog`: a statement whose output stack decides
  `Φ` within space `2 ^ p(|x|)` yields a stack program of the form required by
  `exists_gameProg`;
* `Exec.frame` (stacks not written are unchanged), `Exec.loop_of_variant` (loop rule with an
  invariant and a variant), `Stmt.exec_of_eq`.

Verified routines (each with an exact `Exec` specification, space linear in the data):
`clear`, `moveBit`, `moveAll` (reversing transfer), `copy`, `pushList` (hardwired constants),
`clearFlag`/`setFlag`, `eqTest` (equality of two stacks), `decodeOne` and the 9-stack procedure
`memTest` (membership of a string in a coded list `Stacks.encList L`), fixed-point arithmetic
`addInto` (`A := A + B`) and `cmpInto` (`F := [A ≤ B]`) with `binVal`/`fixVal` semantics.
The game evaluator is reduced to the finite recursion `safeYesB`/`gameValB`
(`gameValB_eq_val`, proved), and `exists_gameProg` is proved from the remaining program
specifications `exists_simStmt`, `exists_queryEnumStmt`, `exists_evalStmt`. -/

/-- Contents of `k` stacks. -/
abbrev Stacks (k : ℕ) : Type := Fin k → BitString

/-- The total length of the stacks. -/
def Stacks.space {k : ℕ} (σ : Stacks k) : ℕ := ∑ r, (σ r).length

/-- The contents at the start of a run on input `x`: `x` on stack `0`, the other stacks empty. -/
def Stacks.input (k : ℕ) (x : BitString) : Stacks k := fun r => if r.val = 0 then x else []

/-- The space of a configuration is the space of its stacks. -/
theorem PConfig.space_eq {P : Prog} (c : PConfig P) : c.space = Stacks.space c.regs := rfl

/-- Changing one stack changes the space by the difference of the lengths. -/
theorem Stacks.space_update {k : ℕ} (σ : Stacks k) (r : Fin k) (v : BitString) :
    Stacks.space (Function.update σ r v) + (σ r).length = σ.space + v.length := by
  unfold Stacks.space
  have h1 := Finset.add_sum_erase Finset.univ (fun x => (Function.update σ r v x).length)
    (Finset.mem_univ r)
  have h2 := Finset.add_sum_erase Finset.univ (fun x => (σ x).length) (Finset.mem_univ r)
  have h3 : ∑ x ∈ Finset.univ.erase r, (Function.update σ r v x).length =
      ∑ x ∈ Finset.univ.erase r, (σ x).length :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  simp only [Function.update_self] at h1
  omega

/-- Updating stack `r` with a string of at most the same length does not increase the
space of the stacks. -/
theorem Stacks.space_update_le {k : ℕ} (σ : Stacks k) (r : Fin k) (v : BitString)
    (h : v.length ≤ (σ r).length) : Stacks.space (Function.update σ r v) ≤ σ.space := by
  have := σ.space_update r v; omega

/-- Pushing one bit to stack `r` increases the space of the stacks by exactly one. -/
theorem Stacks.space_update_cons {k : ℕ} (σ : Stacks k) (r : Fin k) (b : Bool) :
    Stacks.space (Function.update σ r (b :: σ r)) = σ.space + 1 := by
  have := σ.space_update r (b :: σ r); simp only [List.length_cons] at this; omega

/-- Popping one bit from stack `r` does not increase the space of the stacks. -/
theorem Stacks.space_update_tail_le {k : ℕ} (σ : Stacks k) (r : Fin k) :
    Stacks.space (Function.update σ r (σ r).tail) ≤ σ.space :=
  σ.space_update_le r _ (by rw [List.length_tail]; omega)

/-- Structured statements over `k` stacks. -/
inductive Stmt (k : ℕ) where
  /-- Do nothing. -/
  | skip
  /-- Push the bit `b` on stack `r`. -/
  | push (r : Fin k) (b : Bool)
  /-- Pop stack `r` (no effect on an empty stack). -/
  | pop (r : Fin k)
  /-- Run `s₁`, then `s₂`. -/
  | seq (s₁ s₂ : Stmt k)
  /-- If `cond` holds of the top of stack `r` (`none` if empty), run `s₁`, else `s₂`. -/
  | ite (r : Fin k) (cond : Option Bool → Bool) (s₁ s₂ : Stmt k)
  /-- While `cond` holds of the top of stack `r`, run `body`. -/
  | loop (r : Fin k) (cond : Option Bool → Bool) (body : Stmt k)

namespace Stmt

variable {k : ℕ}

/-- The number of instructions of the compiled statement. -/
def size : Stmt k → ℕ
  | skip => 0
  | push _ _ => 1
  | pop _ => 1
  | seq s₁ s₂ => s₁.size + s₂.size
  | ite _ _ s₁ s₂ => s₁.size + s₂.size + 2
  | loop _ _ b => b.size + 2

/-- A test of the top of `r` jumping to `t` if `cond` holds and to `f` otherwise. -/
def testInstr (r : Fin k) (cond : Option Bool → Bool) (t f : ℕ) : Instr k :=
  .test r (if cond none then t else f) (if cond (some false) then t else f)
    (if cond (some true) then t else f)

/-- An unconditional jump to `n` (a test of `r` with three equal targets). -/
def jumpInstr (r : Fin k) (n : ℕ) : Instr k := .test r n n n

/-- The instructions of `s` laid out from address `a`. -/
def compile : Stmt k → ℕ → List (Instr k)
  | skip, _ => []
  | push r b, a => [.push r b (a + 1)]
  | pop r, a => [.pop r (a + 1)]
  | seq s₁ s₂, a => s₁.compile a ++ s₂.compile (a + s₁.size)
  | ite r c s₁ s₂, a => testInstr r c (a + 1) (a + s₁.size + 2) ::
      (s₁.compile (a + 1) ++
        (jumpInstr r (a + s₁.size + s₂.size + 2) :: s₂.compile (a + s₁.size + 2)))
  | loop r c b, a => testInstr r c (a + 1) (a + b.size + 2) ::
      (b.compile (a + 1) ++ [jumpInstr r a])

/-- The number of instructions in the compiled code of `s` equals its declared `size`. -/
theorem length_compile (s : Stmt k) (a : ℕ) : (s.compile a).length = s.size := by
  induction s generalizing a with
  | skip => rfl
  | push => rfl
  | pop => rfl
  | seq s₁ s₂ ih₁ ih₂ => simp [compile, size, ih₁, ih₂]
  | ite r c s₁ s₂ ih₁ ih₂ => simp [compile, size, ih₁, ih₂]; omega
  | loop r c b ih => simp [compile, size, ih]

end Stmt

/-- Big-step semantics with a space bound: `Exec s σ σ' S` says that `s`, started on the stacks
`σ`, terminates with the stacks `σ'`, all intermediate contents having total length `≤ S`. -/
inductive Exec {k : ℕ} : Stmt k → Stacks k → Stacks k → ℕ → Prop
  | skip {σ : Stacks k} {S : ℕ} : σ.space ≤ S → Exec .skip σ σ S
  | push {r : Fin k} {b : Bool} {σ : Stacks k} {S : ℕ} : σ.space + 1 ≤ S →
      Exec (.push r b) σ (Function.update σ r (b :: σ r)) S
  | pop {r : Fin k} {σ : Stacks k} {S : ℕ} : σ.space ≤ S →
      Exec (.pop r) σ (Function.update σ r (σ r).tail) S
  | seq {s₁ s₂ : Stmt k} {σ σ₁ σ₂ : Stacks k} {S : ℕ} :
      Exec s₁ σ σ₁ S → Exec s₂ σ₁ σ₂ S → Exec (.seq s₁ s₂) σ σ₂ S
  | iteT {r : Fin k} {cond : Option Bool → Bool} {s₁ s₂ : Stmt k} {σ σ' : Stacks k} {S : ℕ} :
      cond (σ r).head? = true → Exec s₁ σ σ' S → Exec (.ite r cond s₁ s₂) σ σ' S
  | iteF {r : Fin k} {cond : Option Bool → Bool} {s₁ s₂ : Stmt k} {σ σ' : Stacks k} {S : ℕ} :
      cond (σ r).head? = false → Exec s₂ σ σ' S → Exec (.ite r cond s₁ s₂) σ σ' S
  | loopT {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k} {σ σ₁ σ₂ : Stacks k}
      {S : ℕ} : cond (σ r).head? = true → Exec body σ σ₁ S → Exec (.loop r cond body) σ₁ σ₂ S →
      Exec (.loop r cond body) σ σ₂ S
  | loopF {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k} {σ : Stacks k} {S : ℕ} :
      cond (σ r).head? = false → σ.space ≤ S → Exec (.loop r cond body) σ σ S

namespace Exec

variable {k : ℕ}

/-- The initial and final contents respect the space bound. -/
theorem space_le {s : Stmt k} {σ σ' : Stacks k} {S : ℕ} (h : Exec s σ σ' S) :
    σ.space ≤ S ∧ σ'.space ≤ S := by
  induction h with
  | skip h => exact ⟨h, h⟩
  | push h => exact ⟨by omega, by rw [Stacks.space_update_cons]; exact h⟩
  | pop h => exact ⟨h, (Stacks.space_update_tail_le _ _).trans h⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopT _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | loopF _ h => exact ⟨h, h⟩

/-- The space bound can be raised. -/
theorem mono {s : Stmt k} {σ σ' : Stacks k} {S S' : ℕ} (h : Exec s σ σ' S) (hS : S ≤ S') :
    Exec s σ σ' S' := by
  induction h with
  | skip h => exact .skip (h.trans hS)
  | push h => exact .push (h.trans hS)
  | pop h => exact .pop (h.trans hS)
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ hS) (ih₂ hS)
  | iteT hc _ ih => exact .iteT hc (ih hS)
  | iteF hc _ ih => exact .iteF hc (ih hS)
  | loopT hc _ _ ih₁ ih₂ => exact .loopT hc (ih₁ hS) (ih₂ hS)
  | loopF hc h => exact .loopF hc (h.trans hS)

/-- Determinism. -/
theorem det {s : Stmt k} {σ σ₁ σ₂ : Stacks k} {S₁ S₂ : ℕ} (h₁ : Exec s σ σ₁ S₁)
    (h₂ : Exec s σ σ₂ S₂) : σ₁ = σ₂ := by
  induction h₁ generalizing σ₂ S₂ with
  | skip _ => cases h₂; rfl
  | push _ => cases h₂; rfl
  | pop _ => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂₁ h₂₂ => obtain rfl := ih₁ h₂₁; exact ih₂ h₂₂
  | iteT hc _ ih =>
    cases h₂ with
    | iteT _ h => exact ih h
    | iteF hc' _ => cases hc.symm.trans hc'
  | iteF hc _ ih =>
    cases h₂ with
    | iteT hc' _ => cases hc.symm.trans hc'
    | iteF _ h => exact ih h
  | loopT hc _ _ ih₁ ih₂ =>
    cases h₂ with
    | loopT _ hb hl => obtain rfl := ih₁ hb; exact ih₂ hl
    | loopF hc' _ => cases hc.symm.trans hc'
  | loopF hc _ =>
    cases h₂ with
    | loopT hc' _ _ => cases hc.symm.trans hc'
    | loopF _ _ => rfl

/-- A sequential composition terminates iff its components do. -/
theorem seq_iff {s₁ s₂ : Stmt k} {σ σ₂ : Stacks k} {S : ℕ} :
    Exec (.seq s₁ s₂) σ σ₂ S ↔ ∃ σ₁, Exec s₁ σ σ₁ S ∧ Exec s₂ σ₁ σ₂ S :=
  ⟨fun h => by cases h with | seq h₁ h₂ => exact ⟨_, h₁, h₂⟩, fun ⟨_, h₁, h₂⟩ => .seq h₁ h₂⟩

/-- The space of a sequential composition is the max of the components' spaces. -/
theorem seq_max {s₁ s₂ : Stmt k} {σ σ₁ σ₂ : Stacks k} {S₁ S₂ : ℕ} (h₁ : Exec s₁ σ σ₁ S₁)
    (h₂ : Exec s₂ σ₁ σ₂ S₂) : Exec (.seq s₁ s₂) σ σ₂ (max S₁ S₂) :=
  .seq (h₁.mono (le_max_left _ _)) (h₂.mono (le_max_right _ _))

/-- A conditional terminates iff the chosen branch does. -/
theorem ite_iff {r : Fin k} {cond : Option Bool → Bool} {s₁ s₂ : Stmt k} {σ σ' : Stacks k}
    {S : ℕ} : Exec (.ite r cond s₁ s₂) σ σ' S ↔
      if cond (σ r).head? then Exec s₁ σ σ' S else Exec s₂ σ σ' S := by
  constructor
  · intro h
    cases h with
    | iteT hc h => rw [ite_eq_left hc]; exact h
    | iteF hc h => rw [ite_eq_right (by simp [hc])]; exact h
  · intro h
    by_cases hc : cond (σ r).head? = true
    · rw [ite_eq_left hc] at h; exact .iteT hc h
    · rw [ite_eq_right hc] at h; exact .iteF (by simpa using hc) h

/-- One unfolding of a loop. -/
theorem loop_iff {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k} {σ σ' : Stacks k}
    {S : ℕ} : Exec (.loop r cond body) σ σ' S ↔
      if cond (σ r).head? then ∃ σ₁, Exec body σ σ₁ S ∧ Exec (.loop r cond body) σ₁ σ' S
      else σ' = σ ∧ σ.space ≤ S := by
  constructor
  · intro h
    cases h with
    | loopT hc hb hl => rw [ite_eq_left hc]; exact ⟨_, hb, hl⟩
    | loopF hc hS => rw [ite_eq_right (by simp [hc])]; exact ⟨rfl, hS⟩
  · intro h
    by_cases hc : cond (σ r).head? = true
    · rw [ite_eq_left hc] at h
      obtain ⟨σ₁, hb, hl⟩ := h
      exact .loopT hc hb hl
    · rw [ite_eq_right hc] at h
      obtain ⟨rfl, hS⟩ := h
      exact .loopF (by simpa using hc) hS

end Exec

/-! #### Runs of compiled code -/

/-- `c` reaches `c'` after finitely many steps of `P`, all configurations on the way (both ends
included) having space `≤ S`. -/
def Prog.Reaches (P : Prog) (c c' : PConfig P) (S : ℕ) : Prop :=
  ∃ n, P.step^[n] c = c' ∧ ∀ m ≤ n, (P.step^[m] c).space ≤ S

/-- A configuration with space at most `S` reaches itself in zero steps within space `S`. -/
theorem Prog.Reaches.refl {P : Prog} {c : PConfig P} {S : ℕ} (h : c.space ≤ S) :
    P.Reaches c c S :=
  ⟨0, rfl, fun m hm => by rw [Nat.le_zero.1 hm]; exact h⟩

/-- A configuration reaches its one-step successor within space `S` if both have
space at most `S`. -/
theorem Prog.Reaches.single {P : Prog} {c c' : PConfig P} {S : ℕ} (hc : P.step c = c')
    (h : c.space ≤ S) (h' : c'.space ≤ S) : P.Reaches c c' S :=
  ⟨1, by simpa using hc, fun m hm => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
    · exact h
    · simpa [hc] using h'⟩

/-- Concatenation of runs. -/
theorem Prog.Reaches.trans {P : Prog} {c₁ c₂ c₃ : PConfig P} {S : ℕ} (h₁ : P.Reaches c₁ c₂ S)
    (h₂ : P.Reaches c₂ c₃ S) : P.Reaches c₁ c₃ S := by
  obtain ⟨n₁, e₁, s₁⟩ := h₁
  obtain ⟨n₂, e₂, s₂⟩ := h₂
  refine ⟨n₂ + n₁, by rw [Function.iterate_add_apply, e₁, e₂], fun m hm => ?_⟩
  rcases Nat.lt_or_ge m n₁ with hlt | hge
  · exact s₁ m hlt.le
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
    rw [Nat.add_comm n₁ j, Function.iterate_add_apply, e₁]
    exact s₂ j (by omega)

/-- The run of a stack program is the iteration of its step function. -/
theorem Prog.run_eq_iterate (P : Prog) (x : BitString) (t : ℕ) :
    P.run x t = P.step^[t] (P.init x) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- The code of `P` contains the instructions `l` from address `a` on. -/
def Prog.CodeAt (P : Prog) (a : ℕ) (l : List (Instr P.k)) : Prop :=
  ∀ i < l.length, P.code[a + i]? = l[i]?

/-- If the program contains the concatenation of `l₁` and `l₂` starting at address `a`,
it contains `l₁` starting at `a`. -/
theorem Prog.CodeAt.append_left {P : Prog} {a : ℕ} {l₁ l₂ : List (Instr P.k)}
    (h : P.CodeAt a (l₁ ++ l₂)) : P.CodeAt a l₁ := fun i hi => by
  have := h i (by rw [List.length_append]; omega)
  rwa [List.getElem?_append_left hi] at this

/-- If the program contains the concatenation of `l₁` and `l₂` starting at address `a`,
it contains `l₂` starting at `a + l₁.length`. -/
theorem Prog.CodeAt.append_right {P : Prog} {a : ℕ} {l₁ l₂ : List (Instr P.k)}
    (h : P.CodeAt a (l₁ ++ l₂)) : P.CodeAt (a + l₁.length) l₂ := fun i hi => by
  have := h (l₁.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, ← Nat.add_assoc] at this
  exact this

/-- If the program contains `x :: l` starting at address `a`, the instruction at `a` is `x`. -/
theorem Prog.CodeAt.head {P : Prog} {a : ℕ} {x : Instr P.k} {l : List (Instr P.k)}
    (h : P.CodeAt a (x :: l)) : P.code[a]? = some x := by
  simpa using h 0 (by simp)

/-- If the program contains `x :: l` starting at address `a`, it contains `l` starting
at `a + 1`. -/
theorem Prog.CodeAt.tail {P : Prog} {a : ℕ} {x : Instr P.k} {l : List (Instr P.k)}
    (h : P.CodeAt a (x :: l)) : P.CodeAt (a + 1) l := fun i hi => by
  have := h (i + 1) (by simp; omega)
  rw [show a + 1 + i = a + (i + 1) by omega]
  simpa using this

/-- Executing a push instruction transitions to its target address and prepends the
given bit to the specified stack. -/
theorem Prog.step_mk_push {P : Prog} {a n : ℕ} {σ : Stacks P.k} {r : Fin P.k} {b : Bool}
    (h : P.code[a]? = some (.push r b n)) :
    P.step ⟨a, σ⟩ = ⟨n, Function.update σ r (b :: σ r)⟩ := by
  unfold Prog.step; rw [h]

/-- Executing a pop instruction transitions to its target address and removes the top bit
of the specified stack. -/
theorem Prog.step_mk_pop {P : Prog} {a n : ℕ} {σ : Stacks P.k} {r : Fin P.k}
    (h : P.code[a]? = some (.pop r n)) :
    P.step ⟨a, σ⟩ = ⟨n, Function.update σ r (σ r).tail⟩ := by
  unfold Prog.step; rw [h]

/-- Executing a test instruction transitions to `t` or `f` according to the evaluated
condition on the top bit, without modifying the stacks. -/
theorem Prog.step_mk_test {P : Prog} {a t f : ℕ} {σ : Stacks P.k} {r : Fin P.k}
    {cond : Option Bool → Bool} (h : P.code[a]? = some (Stmt.testInstr r cond t f)) :
    P.step ⟨a, σ⟩ = ⟨if cond (σ r).head? then t else f, σ⟩ := by
  unfold Prog.step; rw [h]; simp only [Stmt.testInstr]
  cases hr : σ r with
  | nil => rfl
  | cons b l => cases b <;> rfl

/-- Executing a jump instruction transitions to its target address without modifying the
stacks. -/
theorem Prog.step_mk_jump {P : Prog} {a n : ℕ} {σ : Stacks P.k} {r : Fin P.k}
    (h : P.code[a]? = some (Stmt.jumpInstr r n)) : P.step ⟨a, σ⟩ = ⟨n, σ⟩ := by
  unfold Prog.step; rw [h]; simp only [Stmt.jumpInstr]
  cases hr : σ r with
  | nil => rfl
  | cons b l => cases b <;> rfl

/-- **Correctness of the compiler.**  If `s` executes from `σ` to `σ'` within space `S`, then
its compiled code, placed at any address `a` of any program, runs from `⟨a, σ⟩` to
`⟨a + s.size, σ'⟩` through configurations of space `≤ S`. -/
theorem Exec.reaches {P : Prog} {s : Stmt P.k} {σ σ' : Stacks P.k} {S : ℕ}
    (h : Exec s σ σ' S) : ∀ a, P.CodeAt a (s.compile a) → P.Reaches ⟨a, σ⟩ ⟨a + s.size, σ'⟩ S := by
  induction h with
  | skip hS => intro a _; exact Prog.Reaches.refl hS
  | @push r b σ S hS =>
    intro a hc
    simp only [Stmt.compile] at hc
    exact Prog.Reaches.single (Prog.step_mk_push hc.head) (by change σ.space ≤ S; omega)
      (by change Stacks.space (Function.update σ r (b :: σ r)) ≤ S
          rw [Stacks.space_update_cons]; exact hS)
  | @pop r σ S hS =>
    intro a hc
    simp only [Stmt.compile] at hc
    exact Prog.Reaches.single (Prog.step_mk_pop hc.head) hS
      ((Stacks.space_update_tail_le σ r).trans hS)
  | @seq s₁ s₂ σ σ₁ σ₂ S h₁ h₂ ih₁ ih₂ =>
    intro a hc
    simp only [Stmt.compile] at hc
    have r₁ := ih₁ a hc.append_left
    have hc₂ := hc.append_right
    rw [Stmt.length_compile] at hc₂
    have r₂ := ih₂ _ hc₂
    have e : a + (Stmt.seq s₁ s₂).size = a + s₁.size + s₂.size := by
      simp only [Stmt.size]; omega
    rw [e]; exact r₁.trans r₂
  | @iteT r cond s₁ s₂ σ σ' S hcnd h ih =>
    intro a hc
    simp only [Stmt.compile] at hc
    have e0 := Prog.step_mk_test (σ := σ) hc.head
    rw [ite_eq_left hcnd] at e0
    have hsp := h.space_le
    have r₀ : P.Reaches ⟨a, σ⟩ ⟨a + 1, σ⟩ S := Prog.Reaches.single e0 hsp.1 hsp.1
    have hc1 := hc.tail
    have r₁ := ih (a + 1) hc1.append_left
    have hc2 := hc1.append_right
    rw [Stmt.length_compile] at hc2
    have e2 := Prog.step_mk_jump (σ := σ') hc2.head
    have r₂ : P.Reaches ⟨a + 1 + s₁.size, σ'⟩ ⟨a + s₁.size + s₂.size + 2, σ'⟩ S :=
      Prog.Reaches.single e2 hsp.2 hsp.2
    have e : a + (Stmt.ite r cond s₁ s₂).size = a + s₁.size + s₂.size + 2 := by
      simp only [Stmt.size]; omega
    rw [e]; exact r₀.trans (r₁.trans r₂)
  | @iteF r cond s₁ s₂ σ σ' S hcnd h ih =>
    intro a hc
    simp only [Stmt.compile] at hc
    have e0 := Prog.step_mk_test (σ := σ) hc.head
    rw [ite_eq_right (by simp [hcnd])] at e0
    have hsp := h.space_le
    have r₀ : P.Reaches ⟨a, σ⟩ ⟨a + s₁.size + 2, σ⟩ S := Prog.Reaches.single e0 hsp.1 hsp.1
    have hc2 := hc.tail.append_right
    rw [Stmt.length_compile] at hc2
    have hc3 := hc2.tail
    rw [show a + 1 + s₁.size + 1 = a + s₁.size + 2 by omega] at hc3
    have r₁ := ih _ hc3
    have e : a + (Stmt.ite r cond s₁ s₂).size = a + s₁.size + 2 + s₂.size := by
      simp only [Stmt.size]; omega
    rw [e]; exact r₀.trans r₁
  | @loopT r cond body σ σ₁ σ₂ S hcnd hb hl ihb ihl =>
    intro a hc
    have hc' := hc
    simp only [Stmt.compile] at hc
    have e0 := Prog.step_mk_test (σ := σ) hc.head
    rw [ite_eq_left hcnd] at e0
    have hsb := hb.space_le
    have r₀ : P.Reaches ⟨a, σ⟩ ⟨a + 1, σ⟩ S := Prog.Reaches.single e0 hsb.1 hsb.1
    have hc1 := hc.tail
    have r₁ := ihb (a + 1) hc1.append_left
    have hc2 := hc1.append_right
    rw [Stmt.length_compile] at hc2
    have e2 := Prog.step_mk_jump (σ := σ₁) hc2.head
    have r₂ : P.Reaches ⟨a + 1 + body.size, σ₁⟩ ⟨a, σ₁⟩ S := Prog.Reaches.single e2 hsb.2 hsb.2
    exact r₀.trans (r₁.trans (r₂.trans (ihl a hc')))
  | @loopF r cond body σ S hcnd hS =>
    intro a hc
    simp only [Stmt.compile] at hc
    have e0 := Prog.step_mk_test (σ := σ) hc.head
    rw [ite_eq_right (by simp [hcnd])] at e0
    have e : a + (Stmt.loop r cond body).size = a + body.size + 2 := by
      simp only [Stmt.size]; omega
    rw [e]; exact Prog.Reaches.single e0 hS hS

/-! #### Whole programs from statements -/

/-- The code of `Stmt.toProg`: the compiled statement, then a test of the output stack jumping to
`accept` or `reject`. -/
def Stmt.progCode {k : ℕ} (s : Stmt k) (out : Fin k) : List (Instr k) :=
  s.compile 0 ++
    [Stmt.testInstr out (fun o => o == some true) (s.size + 1) (s.size + 2), .accept, .reject]

/-- The program running `s` on the input (loaded on stack `0`), then accepting iff the top of
stack `out` is `true`. -/
def Stmt.toProg {k : ℕ} (s : Stmt k) (out : Fin k) : Prog := ⟨k, s.progCode out⟩

/-- The first `s.size` instructions of `s.progCode out` perfectly match the code compiled
from `s` starting at address `0`. -/
theorem Stmt.progCode_left {k : ℕ} (s : Stmt k) (out : Fin k) (i : ℕ) (hi : i < s.size) :
    (s.progCode out)[i]? = (s.compile 0)[i]? := by
  unfold Stmt.progCode
  rw [List.getElem?_append_left (by rw [Stmt.length_compile]; exact hi)]

/-- The trailing instructions of `s.progCode out` are precisely the test, accept,
and reject instructions. -/
theorem Stmt.progCode_right {k : ℕ} (s : Stmt k) (out : Fin k) (j : ℕ) :
    (s.progCode out)[s.size + j]? =
      [Stmt.testInstr out (fun o => o == some true) (s.size + 1) (s.size + 2), .accept,
        .reject][j]? := by
  unfold Stmt.progCode
  rw [List.getElem?_append_right (by rw [Stmt.length_compile]; omega), Stmt.length_compile,
    Nat.add_sub_cancel_left]

/-- A terminating execution of `s` on the input gives a halting run of `s.toProg out` within the
same space, accepting iff the output stack has `true` on top. -/
theorem Stmt.toProg_spec {k : ℕ} (s : Stmt k) (out : Fin k) (x : BitString) (σ' : Stacks k) (S : ℕ)
    (h : Exec s (Stacks.input k x) σ' S) :
    ∃ t, (s.toProg out).Halted ((s.toProg out).run x t) ∧
      (∀ u ≤ t, ((s.toProg out).run x u).space ≤ S) ∧
      ((s.toProg out).Accepting ((s.toProg out).run x t) ↔ (σ' out).head? = some true) := by
  have hcode : (s.toProg out).CodeAt 0 (s.compile 0) := fun i hi => by
    rw [Nat.zero_add]
    exact s.progCode_left out i (hi.trans_eq (Stmt.length_compile s 0))
  obtain ⟨n, hn, hsp⟩ := Exec.reaches (P := s.toProg out) h 0 hcode
  rw [Nat.zero_add] at hn
  have hσ' : σ'.space ≤ S := h.space_le.2
  have e0 : (s.toProg out).code[s.size]? =
      some (Stmt.testInstr out (fun o => o == some true) (s.size + 1) (s.size + 2)) := by
    have := s.progCode_right out 0
    rw [Nat.add_zero] at this
    exact this
  have hlast := Prog.step_mk_test (P := s.toProg out) (σ := σ') e0
  have hrun : (s.toProg out).run x (n + 1) =
      ⟨if (σ' out).head? == some true then s.size + 1 else s.size + 2, σ'⟩ := by
    rw [Prog.run_eq_iterate, Function.iterate_succ_apply']
    exact (congrArg (s.toProg out).step hn).trans hlast
  have hacc : (s.toProg out).code[s.size + 1]? = some .accept := s.progCode_right out 1
  have hrej : (s.toProg out).code[s.size + 2]? = some .reject := s.progCode_right out 2
  refine ⟨n + 1, ?_, fun u hu => ?_, ?_⟩
  · rw [hrun]
    by_cases ht : (σ' out).head? = some true
    · left; simp [ht, hacc]
    · right; left; simp [ht, hrej]
  · rcases Nat.lt_or_ge u (n + 1) with hlt | hge
    · rw [Prog.run_eq_iterate]; exact hsp u (by omega)
    · rw [show u = n + 1 by omega, hrun]; exact hσ'
  · rw [hrun]
    by_cases ht : (σ' out).head? = some true
    · simp [ht, hacc, Prog.Accepting]
    · simp [ht, hrej, Prog.Accepting]

/-- A statement deciding `Φ` within space `2 ^ p(|x|)` on its output stack gives a stack program
of the form required by `exists_gameProg`. -/
theorem Stmt.exists_prog {k : ℕ} (s : Stmt k) (out : Fin k) (p : Polynomial ℕ)
    (Φ : BitString → Prop) (h : ∀ x : BitString, ∃ σ', Exec s (Stacks.input k x) σ'
      (2 ^ p.eval x.length) ∧ ((σ' out).head? = some true ↔ Φ x)) :
    ∃ (P : Prog) (q : Polynomial ℕ), P.SpaceBounded q ∧ ∀ x : BitString, x ∈ P.Lang ↔ Φ x := by
  refine ⟨s.toProg out, p, fun x => ?_, fun x => ?_⟩
  · obtain ⟨σ', hσ', -⟩ := h x
    obtain ⟨t, ht, hsp, -⟩ := s.toProg_spec out x σ' _ hσ'
    exact ⟨t, ht, hsp⟩
  · obtain ⟨σ', hσ', hΦ⟩ := h x
    obtain ⟨t, ht, -, hacc⟩ := s.toProg_spec out x σ' _ hσ'
    rw [Prog.mem_lang_iff_of_halted _ x t ht, hacc, hΦ]

/-! #### Inlining along a renaming of the stacks -/

/-- Renaming the stacks of a statement along `f`: inlining a subroutine written for `k` stacks
into a program with `k'` stacks (with `f` injective, on a disjoint copy of its own stacks). -/
def Stmt.rename {k k' : ℕ} (f : Fin k → Fin k') : Stmt k → Stmt k'
  | .skip => .skip
  | .push r b => .push (f r) b
  | .pop r => .pop (f r)
  | .seq s₁ s₂ => .seq (s₁.rename f) (s₂.rename f)
  | .ite r c s₁ s₂ => .ite (f r) c (s₁.rename f) (s₂.rename f)
  | .loop r c b => .loop (f r) c (b.rename f)

/-- The total length of the stacks outside the range of `f`. -/
def Stacks.rest {k k' : ℕ} (f : Fin k → Fin k') (τ : Stacks k') : ℕ :=
  ∑ j ∈ (Finset.univ.image f)ᶜ, (τ j).length

/-- The total length of the extended stacks equals the total length of the inner stacks `σ`
plus the length of the unaffected rest of `τ`. -/
theorem Stacks.space_extend {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f)
    (σ : Stacks k) (τ : Stacks k') :
    Stacks.space (Function.extend f σ τ) = σ.space + Stacks.rest f τ := by
  classical
  unfold Stacks.space Stacks.rest
  rw [← Finset.sum_add_sum_compl (Finset.univ.image f), Finset.sum_image (fun x _ y _ h => hf h)]
  congr 1
  · exact Finset.sum_congr rfl fun r _ => by rw [hf.extend_apply]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.extend_apply']
    rintro ⟨r, rfl⟩
    exact (Finset.mem_compl.1 hj) (Finset.mem_image_of_mem f (Finset.mem_univ r))

/-- Updating an extended stack at an index mapped by `f` is equivalent to extending
the updated inner stacks. -/
theorem Stacks.update_extend {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f)
    (σ : Stacks k) (τ : Stacks k') (r : Fin k) (v : BitString) :
    Function.update (Function.extend f σ τ) (f r) v =
      Function.extend f (Function.update σ r v) τ := by
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [hf.extend_apply]
    by_cases hir : i = r
    · subst hir; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (hf.ne hir), Function.update_of_ne hir, hf.extend_apply]
  · rw [Function.update_of_ne (fun h => hj ⟨r, h.symm⟩), Function.extend_apply' _ _ _ hj,
      Function.extend_apply' _ _ _ hj]

/-- Extending from the pullback of `τ` by `f` recovers `τ` exactly. -/
theorem Stacks.extend_comp_self {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f)
    (τ : Stacks k') : Function.extend f (fun r => τ (f r)) τ = τ := by
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj; rw [hf.extend_apply]
  · rw [Function.extend_apply' _ _ _ hj]

/-- **Inlining.**  Running the renamed statement on stacks whose `f`-part is `σ` runs `s` on that
part and leaves the other stacks `τ` untouched; their total length is added to the space. -/
theorem Exec.rename {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f) {s : Stmt k}
    {σ σ' : Stacks k} {S : ℕ} (h : Exec s σ σ' S) (τ : Stacks k') :
    Exec (s.rename f) (Function.extend f σ τ) (Function.extend f σ' τ)
      (S + Stacks.rest f τ) := by
  induction h with
  | skip hS => exact .skip (by rw [Stacks.space_extend hf]; omega)
  | @push r b σ S hS =>
    have := Exec.push (r := f r) (b := b) (σ := Function.extend f σ τ)
      (S := S + Stacks.rest f τ) (by rw [Stacks.space_extend hf]; omega)
    rwa [hf.extend_apply, Stacks.update_extend hf] at this
  | @pop r σ S hS =>
    have := Exec.pop (r := f r) (σ := Function.extend f σ τ)
      (S := S + Stacks.rest f τ) (by rw [Stacks.space_extend hf]; omega)
    rwa [hf.extend_apply, Stacks.update_extend hf] at this
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc _ ih => exact .iteT (by rw [hf.extend_apply]; exact hc) ih
  | iteF hc _ ih => exact .iteF (by rw [hf.extend_apply]; exact hc) ih
  | loopT hc _ _ ih₁ ih₂ => exact .loopT (by rw [hf.extend_apply]; exact hc) ih₁ ih₂
  | loopF hc hS =>
    exact .loopF (by rw [hf.extend_apply]; exact hc) (by rw [Stacks.space_extend hf]; omega)

/-- **Inlining**, user form: started on `τ`, the renamed statement acts on the `f`-part of `τ`
as `s` does and leaves the rest untouched. -/
theorem Exec.rename_of_comp {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f)
    {s : Stmt k} {σ' : Stacks k} {S : ℕ} {τ : Stacks k'} (h : Exec s (fun r => τ (f r)) σ' S) :
    Exec (s.rename f) τ (Function.extend f σ' τ) (S + Stacks.rest f τ) := by
  have := h.rename hf τ
  rwa [Stacks.extend_comp_self hf τ] at this

/-- After inlining, the stacks outside the range of the renaming are unchanged. -/
theorem Stacks.extend_apply_of_not_mem {k k' : ℕ} {f : Fin k → Fin k'} (σ : Stacks k)
    (τ : Stacks k') (j : Fin k') (hj : ∀ r, f r ≠ j) : Function.extend f σ τ j = τ j :=
  Function.extend_apply' _ _ _ fun ⟨r, hr⟩ => hj r hr

end Kolmogorov.RandomStrings
