/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.StmtTime.ExecT

/-!
# Generic step budgets of pop-loop statements

Statements all of whose loops are pop-loops (`Stmt.PopLoops`) run within `s.budget S` steps
(`Exec.execLe_budget`); the step budgets of the routines of `Expspace` and of their helper
statements; polynomial step bounds from the syntax and their invariance under inlining; and local
step budgets in which only the stacks a routine touches count.

Part of `KolmogorovMathlib.RandomStrings.StmtTime`.
-/

namespace Kolmogorov.RandomStrings

/-! #### Generic step budgets: statements built from pop-loops

A *pop-loop* `loop r cond body` exits on an empty test stack (`cond none = false`), and its body
never pushes on `r` and pops `r` on every path; so every iteration makes `r` shorter and the loop
iterates at most `|σ r| ≤ S` times.  All routines of Expspace.lean are built from pop-loops, and
`Exec.execLe_budget` turns each of their `Exec` specifications into a step budget `s.budget S`,
a polynomial in the space bound `S` read off the syntax. -/

/-- A stack is not longer than the total space. -/
theorem Stacks.length_le_space {k : ℕ} (σ : Stacks k) (r : Fin k) : (σ r).length ≤ σ.space :=
  Finset.single_le_sum (f := fun r => (σ r).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ r)

namespace Stmt

variable {k : ℕ}

/-- `s` never pushes on the stack `j`. -/
def NoPush (j : Fin k) : Stmt k → Prop
  | .skip => True
  | .push r _ => r ≠ j
  | .pop _ => True
  | .seq s₁ s₂ => s₁.NoPush j ∧ s₂.NoPush j
  | .ite _ _ s₁ s₂ => s₁.NoPush j ∧ s₂.NoPush j
  | .loop _ _ b => b.NoPush j

/-- Every run of `s` from stacks where `j` is nonempty pops `j`: a `pop j` outside of loops, or a
loop on `j` that runs while `j` is nonempty (so it runs at least once) and whose body pops `j`. -/
def Pops (j : Fin k) : Stmt k → Prop
  | .skip => False
  | .push _ _ => False
  | .pop r => r = j
  | .seq s₁ s₂ => s₁.Pops j ∨ s₂.Pops j
  | .ite _ _ s₁ s₂ => s₁.Pops j ∧ s₂.Pops j
  | .loop r cond b => r = j ∧ (∀ a, cond (some a) = true) ∧ b.Pops j

/-- All loops of `s` are pop-loops: a loop exits on an empty test stack, and its body never pushes
on the test stack and pops it on every path. -/
def PopLoops : Stmt k → Prop
  | .skip => True
  | .push _ _ => True
  | .pop _ => True
  | .seq s₁ s₂ => s₁.PopLoops ∧ s₂.PopLoops
  | .ite _ _ s₁ s₂ => s₁.PopLoops ∧ s₂.PopLoops
  | .loop r cond b => cond none = false ∧ b.NoPush r ∧ b.Pops r ∧ b.PopLoops

/-- The step budget of `s` run within space `S`: the longest path through the code, a pop-loop
counting for at most `S` iterations. -/
def budget (S : ℕ) : Stmt k → ℕ
  | .skip => 0
  | .push _ _ => 1
  | .pop _ => 1
  | .seq s₁ s₂ => s₁.budget S + s₂.budget S
  | .ite _ _ s₁ s₂ => max (s₁.budget S + 2) (s₂.budget S + 1)
  | .loop _ _ b => S * (b.budget S + 2) + 1

end Stmt

/-- A statement that never pushes on `j` does not make `j` longer. -/
theorem Exec.length_le_of_noPush {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ}
    (h : Exec s σ σ' S) {j : Fin k} (hj : s.NoPush j) : (σ' j).length ≤ (σ j).length := by
  induction h with
  | skip _ => exact le_rfl
  | @push r b σ S _ =>
    simp only [Stmt.NoPush] at hj
    rw [Function.update_of_ne hj.symm]
  | @pop r σ S _ =>
    by_cases hr : j = r
    · subst hr; rw [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne hr]
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.NoPush] at hj
    exact (ih₂ hj.2).trans (ih₁ hj.1)
  | iteT _ _ ih =>
    simp only [Stmt.NoPush] at hj
    exact ih hj.1
  | iteF _ _ ih =>
    simp only [Stmt.NoPush] at hj
    exact ih hj.2
  | loopT _ _ _ ih₁ ih₂ =>
    exact (ih₂ hj).trans (ih₁ (by simpa only [Stmt.NoPush] using hj))
  | loopF _ _ => exact le_rfl

/-- A statement that never pushes on `j` and pops it on every path makes a nonempty `j`
shorter. -/
theorem Exec.length_lt_of_pops {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ}
    (h : Exec s σ σ' S) {j : Fin k} (hj : s.NoPush j) (hp : s.Pops j) (hne : σ j ≠ []) :
    (σ' j).length < (σ j).length := by
  induction h with
  | skip _ => simp [Stmt.Pops] at hp
  | push _ => simp [Stmt.Pops] at hp
  | @pop r σ S _ =>
    simp only [Stmt.Pops] at hp
    subst hp
    rw [Function.update_self, List.length_tail]
    have := List.length_pos_iff.2 hne
    omega
  | @seq s₁ s₂ σ σ₁ σ₂ S h₁ h₂ ih₁ ih₂ =>
    simp only [Stmt.NoPush, Stmt.Pops] at hj hp
    rcases hp with hp | hp
    · exact lt_of_le_of_lt (h₂.length_le_of_noPush hj.2) (ih₁ hj.1 hp hne)
    · by_cases h1 : σ₁ j = []
      · have := h₂.length_le_of_noPush hj.2
        rw [h1, List.length_nil] at this
        have := List.length_pos_iff.2 hne
        omega
      · exact lt_of_lt_of_le (ih₂ hj.2 hp h1) (h₁.length_le_of_noPush hj.1)
  | iteT _ _ ih =>
    simp only [Stmt.NoPush, Stmt.Pops] at hj hp
    exact ih hj.1 hp.1 hne
  | iteF _ _ ih =>
    simp only [Stmt.NoPush, Stmt.Pops] at hj hp
    exact ih hj.2 hp.2 hne
  | loopT _ _ hl ihb _ =>
    simp only [Stmt.Pops] at hp
    exact lt_of_le_of_lt (hl.length_le_of_noPush hj) (ihb hj hp.2.2 hne)
  | @loopF r cond body σ S hc _ =>
    simp only [Stmt.Pops] at hp
    obtain ⟨rfl, hall, -⟩ := hp
    obtain ⟨a, l, he⟩ : ∃ a l, σ r = a :: l := by
      cases h' : σ r with
      | nil => exact absurd h' hne
      | cons a l => exact ⟨a, l, rfl⟩
    rw [he, List.head?_cons, hall a] at hc
    cases hc

/-- **Step budget of a pop-loop.**  If the loop exits on an empty test stack `r`, its body never
pushes on `r`, pops `r` on every path and runs within `τ` steps from every state, then the loop
runs within `|σ r| * (τ + 2) + 1` steps. -/
theorem Exec.execLe_popLoop {k : ℕ} {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k}
    {S τ : ℕ} (hc0 : cond none = false) (hn : body.NoPush r) (hp : body.Pops r)
    (hb : ∀ σ₁ σ₂, Exec body σ₁ σ₂ S → ExecLe body σ₁ σ₂ S τ) {σ σ' : Stacks k}
    (h : Exec (.loop r cond body) σ σ' S) :
    ExecLe (.loop r cond body) σ σ' S ((σ r).length * (τ + 2) + 1) :=
  ExecLe.loop_of_exec (fun _ => True) (fun σ => (σ r).length) S τ
    (fun σ₁ σ₂ _ hc hex => ⟨hb σ₁ σ₂ hex, trivial, hex.length_lt_of_pops hn hp (by
      intro he; rw [he] at hc; simp [hc0] at hc)⟩) σ σ' trivial h

/-- **Generic step budget.**  A statement all of whose loops are pop-loops, run within space `S`,
takes at most `s.budget S` steps. -/
theorem Stmt.execLe_budget {k : ℕ} : ∀ (s : Stmt k), s.PopLoops → ∀ {σ σ' : Stacks k} {S : ℕ},
    Exec s σ σ' S → ExecLe s σ σ' S (s.budget S)
  | .skip, _, _, _, _, h => by cases h with | skip hS => exact ExecLe.skip hS
  | .push _ _, _, _, _, _, h => by cases h with | push hS => exact ExecLe.push hS le_rfl
  | .pop _, _, _, _, _, h => by cases h with | pop hS => exact ExecLe.pop hS le_rfl
  | .seq s₁ s₂, hs, _, _, _, h => by
    obtain ⟨σ₁, h₁, h₂⟩ := Exec.seq_iff.1 h
    exact (s₁.execLe_budget hs.1 h₁).seq (s₂.execLe_budget hs.2 h₂)
  | .ite _ _ s₁ s₂, hs, _, _, _, h => by
    cases h with
    | iteT hc h =>
      obtain ⟨T, hT, h⟩ := s₁.execLe_budget hs.1 h
      refine ⟨T + 2, ?_, .iteT hc h⟩
      simp only [Stmt.budget]
      exact (Nat.add_le_add_right hT 2).trans (le_max_left _ _)
    | iteF hc h =>
      obtain ⟨T, hT, h⟩ := s₂.execLe_budget hs.2 h
      refine ⟨T + 1, ?_, .iteF hc h⟩
      simp only [Stmt.budget]
      exact (Nat.add_le_add_right hT 1).trans (le_max_right _ _)
  | .loop r _ b, hs, σ, _, _, h => by
    obtain ⟨hc0, hn, hp, hb⟩ := hs
    have key := Exec.execLe_popLoop hc0 hn hp (fun _ _ hex => b.execLe_budget hb hex) h
    refine key.mono_time ?_
    have h1 : (σ r).length ≤ _ := (Stacks.length_le_space σ r).trans h.space_le.1
    simp only [Stmt.budget]
    exact Nat.add_le_add_right (Nat.mul_le_mul h1 le_rfl) 1

/-- **Generic step budget**, `Exec` form. -/
theorem Exec.execLe_budget {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ} (h : Exec s σ σ' S)
    (hs : s.PopLoops) : ExecLe s σ σ' S (s.budget S) :=
  s.execLe_budget hs h

/-- **Step budget of a top-level pop-loop**: at most `|σ r|` iterations, each within the budget
of the body. -/
theorem Exec.execLe_loop_budget {k : ℕ} {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k}
    {σ σ' : Stacks k} {S : ℕ} (h : Exec (.loop r cond body) σ σ' S)
    (hs : (Stmt.loop r cond body).PopLoops) :
    ExecLe (.loop r cond body) σ σ' S ((σ r).length * (body.budget S + 2) + 1) :=
  Exec.execLe_popLoop hs.1 hs.2.1 hs.2.2.1 (fun _ _ hex => body.execLe_budget hs.2.2.2 hex) h

/-! #### Step budgets of the routines of Expspace.lean

Each lemma has the hypotheses and the conclusion of the corresponding `exec_*` lemma, plus a step
budget: for a single loop, linear in the length of its test stack (`Exec.execLe_loop_budget`);
for a composite routine, a polynomial in the space bound `S` of the `exec_*` lemma
(`Exec.execLe_budget`). -/

namespace Stmt

variable {k : ℕ}

/-- The loops of `clear` are pop-loops. -/
theorem popLoops_clear (r : Fin k) : (clear r).PopLoops := by
  simp [clear, PopLoops, NoPush, Pops]

/-- The step budget of `clear` at space bound `S` is `3 * S + 1`. -/
theorem budget_clear (r : Fin k) (S : ℕ) : (clear r).budget S = 3 * S + 1 := by
  simp [clear, budget]; omega

/-- The loops of `moveAll` are pop-loops. -/
theorem popLoops_moveAll {r r' : Fin k} (hrr : r ≠ r') : (moveAll r r').PopLoops := by
  simp [moveAll, moveBit, caseBit, PopLoops, NoPush, Pops, hrr.symm]

/-- The step budget of `moveAll` at space bound `S` is `6 * S + 1`. -/
theorem budget_moveAll (r r' : Fin k) (S : ℕ) : (moveAll r r').budget S = 6 * S + 1 := by
  simp [moveAll, moveBit, caseBit, budget]; omega

/-- The loops of `copy` are pop-loops. -/
theorem popLoops_copy {r r' t : Fin k} (hrt : r ≠ t) (hr't : r' ≠ t) :
    (copy r r' t).PopLoops := by
  simp [copy, dupStep, seqs, moveAll, moveBit, caseBit, PopLoops, NoPush, Pops, hrt.symm, hrt,
    hr't]

/-- The step budget of `copy` at space bound `S` is `13 * S + 2`. -/
theorem budget_copy (r r' t : Fin k) (S : ℕ) : (copy r r' t).budget S = 13 * S + 2 := by
  simp [copy, dupStep, seqs, moveAll, moveBit, caseBit, budget]; omega

/-- The loops of `addInto` are pop-loops. -/
theorem popLoops_addInto {A B Cy R : Fin k} (hAC : A ≠ Cy) (hAR : A ≠ R) :
    (addInto A B Cy R).PopLoops := by
  simp [addInto, addStep, seqs, clear, moveAll, moveBit, caseBit, PopLoops, NoPush, Pops,
    hAC.symm, hAR.symm, hAR]

/-- The step budget of `addInto` at space bound `S` is `22 * S + 4`. -/
theorem budget_addInto (A B Cy R : Fin k) (S : ℕ) :
    (addInto A B Cy R).budget S = 22 * S + 4 := by
  simp [addInto, addStep, seqs, clear, moveAll, moveBit, caseBit, budget]; omega

/-- The loops of `cmpInto` are pop-loops. -/
theorem popLoops_cmpInto {A B F : Fin k} (hAF : A ≠ F) : (cmpInto A B F).PopLoops := by
  simp [cmpInto, cmpStep, seqs, caseBit, PopLoops, NoPush, Pops, hAF.symm]

/-- The step budget of `cmpInto` at space bound `S` is `12 * S + 2`. -/
theorem budget_cmpInto (A B F : Fin k) (S : ℕ) : (cmpInto A B F).budget S = 12 * S + 2 := by
  simp [cmpInto, cmpStep, seqs, caseBit, budget]; omega

/-- The loops of `incr` are pop-loops. -/
theorem popLoops_incr {A t C : Fin k} (hAt : A ≠ t) : (incr A t C).PopLoops := by
  simp [incr, seqs, moveAll, moveBit, caseBit, PopLoops, NoPush, Pops, isTrue, hAt, hAt.symm]

/-- The step budget of `incr` at space bound `S` is `10 * S + 7`. -/
theorem budget_incr (A t C : Fin k) (S : ℕ) : (incr A t C).budget S = 10 * S + 7 := by
  simp [incr, seqs, moveAll, moveBit, caseBit, budget]; omega

/-- The loops of `eqTest` are pop-loops. -/
theorem popLoops_eqTest {A B tA tB F : Fin k} (h2 : A ≠ tA) (h3 : A ≠ tB) (h4 : A ≠ F)
    (h6 : B ≠ tB) : (eqTest A B tA tB F).PopLoops := by
  simp [eqTest, eqStep, seqs, clearFlag, moveAll, moveBit, caseBit, PopLoops, NoPush, Pops,
    h2, h2.symm, h3.symm, h4.symm, h6, h6.symm]

/-- The step budget of `eqTest` at space bound `S` is `35 * S + 9`. -/
theorem budget_eqTest (A B tA tB F : Fin k) (S : ℕ) :
    (eqTest A B tA tB F).budget S = 35 * S + 9 := by
  simp [eqTest, eqStep, seqs, clearFlag, moveAll, moveBit, caseBit, budget]; omega

/-- The loops of `decodeOne` are pop-loops. -/
theorem popLoops_decodeOne {Lst W Tmp : Fin k} (h1 : Lst ≠ W) (h2 : Lst ≠ Tmp) :
    (decodeOne Lst W Tmp).PopLoops := by
  simp [decodeOne, decodeBody, moveBit, caseBit, PopLoops, NoPush, Pops, isTrue, h1.symm,
    h2.symm]

/-- The step budget of `decodeOne` at space bound `S` is `13 * S + 5`. -/
theorem budget_decodeOne (Lst W Tmp : Fin k) (S : ℕ) :
    (decodeOne Lst W Tmp).budget S = 13 * S + 5 := by
  simp [decodeOne, decodeBody, moveBit, caseBit, budget]; omega

end Stmt

/-- The loops of `memStep` are pop-loops. -/
theorem Stmt.popLoops_memStep : Stmt.memStep.PopLoops := by
  simp [Stmt.memStep, Stmt.decodeOne, Stmt.decodeBody, Stmt.eqTest, Stmt.eqStep, Stmt.seqs,
    Stmt.clearFlag, Stmt.setFlag, Stmt.clear, Stmt.moveAll, Stmt.moveBit, Stmt.caseBit,
    Stmt.PopLoops, Stmt.NoPush, Stmt.Pops, Stmt.isTrue]

/-- The step budget of `memStep` at space bound `S` is `57 * S + 21`. -/
theorem Stmt.budget_memStep (S : ℕ) : Stmt.memStep.budget S = 57 * S + 21 := by
  simp [Stmt.memStep, Stmt.decodeOne, Stmt.decodeBody, Stmt.eqTest, Stmt.eqStep, Stmt.seqs,
    Stmt.clearFlag, Stmt.setFlag, Stmt.clear, Stmt.moveAll, Stmt.moveBit, Stmt.caseBit,
    Stmt.budget]; omega

/-- The loops of `memTest` are pop-loops. -/
theorem Stmt.popLoops_memTest : Stmt.memTest.PopLoops := by
  simp [Stmt.memTest, Stmt.memStep, Stmt.decodeOne, Stmt.decodeBody, Stmt.eqTest, Stmt.eqStep,
    Stmt.seqs, Stmt.clearFlag, Stmt.setFlag, Stmt.clear, Stmt.moveAll, Stmt.moveBit,
    Stmt.caseBit, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops, Stmt.isTrue]

/-- The step budget of `memTest` at space bound `S` is `57 * S * S + 29 * S + 3`. -/
theorem Stmt.budget_memTest (S : ℕ) : Stmt.memTest.budget S = 57 * S * S + 29 * S + 3 := by
  simp [Stmt.memTest, Stmt.memStep, Stmt.decodeOne, Stmt.decodeBody, Stmt.eqTest, Stmt.eqStep,
    Stmt.seqs, Stmt.clearFlag, Stmt.setFlag, Stmt.clear, Stmt.moveAll, Stmt.moveBit,
    Stmt.caseBit, Stmt.budget]; ring

namespace Stmt

variable {k : ℕ}

/-- `clearFlag F` takes exactly `2` steps. -/
theorem execT_clearFlag {F : Fin k} {σ : Stacks k} {f : Bool} (hF : σ F = [f]) :
    ExecT (clearFlag F) σ (Function.update σ F [false]) σ.space 2 := by
  have s1 := space_update_of_cons hF
  have e1 : ExecT (.pop F) σ (Function.update σ F []) σ.space 1 := by
    have := ExecT.pop (r := F) (σ := σ) (S := σ.space) le_rfl
    rwa [hF] at this
  have e2 := ExecT.push (r := F) (b := false) (σ := Function.update σ F []) (S := σ.space)
    (by omega)
  rw [Function.update_self, Function.update_idem] at e2
  exact .seq e1 e2

/-- `setFlag F` takes exactly `2` steps. -/
theorem execT_setFlag {F : Fin k} {σ : Stacks k} {f : Bool} (hF : σ F = [f]) :
    ExecT (setFlag F) σ (Function.update σ F [true]) σ.space 2 := by
  have s1 := space_update_of_cons hF
  have e1 : ExecT (.pop F) σ (Function.update σ F []) σ.space 1 := by
    have := ExecT.pop (r := F) (σ := σ) (S := σ.space) le_rfl
    rwa [hF] at this
  have e2 := ExecT.push (r := F) (b := true) (σ := Function.update σ F []) (S := σ.space)
    (by omega)
  rw [Function.update_self, Function.update_idem] at e2
  exact .seq e1 e2

/-- The adder loop: `|l|` iterations of at most `13` steps. -/
theorem execLe_addLoop {A B Cy R : Fin k} (hAB : A ≠ B) (hAC : A ≠ Cy) (hAR : A ≠ R)
    (hBC : B ≠ Cy) (hBR : B ≠ R) (hCR : Cy ≠ R) (l m : BitString) (c : Bool) (σ : Stacks k)
    (h : l.length = m.length) (hA : σ A = l) (hB : σ B = m) (hC : σ Cy = [c]) :
    ExecLe (.loop A Option.isSome (addStep A B Cy R)) σ
      (Function.update (Function.update (Function.update (Function.update σ A []) B []) Cy
        [addCarry c l m]) R ((addBits c l m).reverse ++ σ R)) σ.space (13 * l.length + 1) := by
  have := (exec_addLoop hAB hAC hAR hBC hBR hCR l m c σ h hA hB hC).execLe_loop_budget
    (by simp [addStep, seqs, caseBit, PopLoops, NoPush, Pops, hAC.symm, hAR.symm])
  have hb : (addStep A B Cy R).budget σ.space = 11 := by
    simp [addStep, seqs, caseBit, budget]
  rw [hA, hb] at this
  exact this.mono_time (by omega)

/-- **Addition**, with a step budget `22 S + 4`, `S = σ.space + 1`. -/
theorem execLe_addInto {A B Cy R : Fin k} (hAB : A ≠ B) (hAC : A ≠ Cy) (hAR : A ≠ R)
    (hBC : B ≠ Cy) (hBR : B ≠ R) (hCR : Cy ≠ R) {σ : Stacks k} {l m : BitString}
    (h : l.length = m.length) (hA : σ A = l) (hB : σ B = m) (hC : σ Cy = []) (hR : σ R = []) :
    ExecLe (addInto A B Cy R) σ (Function.update (Function.update σ A (addBits false l m)) B [])
      (σ.space + 1) (22 * (σ.space + 1) + 4) := by
  have := (exec_addInto hAB hAC hAR hBC hBR hCR h hA hB hC hR).execLe_budget
    (popLoops_addInto hAC hAR)
  rwa [budget_addInto] at this

/-- The comparison loop: `|l|` iterations of at most `12` steps. -/
theorem execLe_cmpLoop {A B F : Fin k} (hAB : A ≠ B) (hAF : A ≠ F) (hBF : B ≠ F)
    (l m : BitString) (f : Bool) (σ : Stacks k) (h : l.length = m.length) (hA : σ A = l)
    (hB : σ B = m) (hF : σ F = [f]) :
    ExecLe (.loop A Option.isSome (cmpStep A B F)) σ
      (Function.update (Function.update (Function.update σ A []) B []) F [cmpBits f l m])
      σ.space (12 * l.length + 1) := by
  have := (exec_cmpLoop hAB hAF hBF l m f σ h hA hB hF).execLe_loop_budget
    (by simp [cmpStep, seqs, caseBit, PopLoops, NoPush, Pops, hAF.symm])
  have hb : (cmpStep A B F).budget σ.space = 10 := by
    simp [cmpStep, seqs, caseBit, budget]
  rw [hA, hb] at this
  exact this.mono_time (by omega)

/-- **Comparison**, with a step budget `12 S + 2`, `S = σ.space + 1`. -/
theorem execLe_cmpInto {A B F : Fin k} (hAB : A ≠ B) (hAF : A ≠ F) (hBF : B ≠ F)
    {σ : Stacks k} {l m : BitString} (h : l.length = m.length) (hA : σ A = l) (hB : σ B = m)
    (hF : σ F = []) :
    ExecLe (cmpInto A B F) σ
      (Function.update (Function.update (Function.update σ A []) B []) F [cmpBits true l m])
      (σ.space + 1) (12 * (σ.space + 1) + 2) := by
  have := (exec_cmpInto hAB hAF hBF h hA hB hF).execLe_budget (popLoops_cmpInto hAF)
  rwa [budget_cmpInto] at this

/-- **Copy**, with a step budget `13 S + 2`, `S = σ.space + |σ r|` (see also `execLe_copy`). -/
theorem execLe_copy_budget {r r' t : Fin k} (hrr : r ≠ r') (hrt : r ≠ t) (hr't : r' ≠ t)
    {σ : Stacks k} (ht : σ t = []) :
    ExecLe (copy r r' t) σ (Function.update σ r' (σ r ++ σ r')) (σ.space + (σ r).length)
      (13 * (σ.space + (σ r).length) + 2) := by
  have := (exec_copy hrr hrt hr't ht).execLe_budget (popLoops_copy hrt hr't)
  rwa [budget_copy] at this

/-- **Binary increment**, with a step budget `10 S + 7`, `S = σ.space + 1`. -/
theorem execLe_incr {A t C : Fin k} (hAt : A ≠ t) (hAC : A ≠ C) (htC : t ≠ C) {σ : Stacks k}
    (ht : σ t = []) (hC : σ C = []) :
    ExecLe (incr A t C) σ
      (Function.update (Function.update σ A (incBits (σ A))) C [incCarry (σ A)])
      (σ.space + 1) (10 * (σ.space + 1) + 7) := by
  have := (exec_incr hAt hAC htC ht hC).execLe_budget (popLoops_incr hAt)
  rwa [budget_incr] at this

/-- The equality loop: `|l|` iterations of at most `15` steps. -/
theorem execLe_eqLoop {A B tA tB F : Fin k} (h1 : A ≠ B) (h2 : A ≠ tA) (h3 : A ≠ tB)
    (h4 : A ≠ F) (h5 : B ≠ tA) (h6 : B ≠ tB) (h7 : B ≠ F) (h8 : tA ≠ tB) (h9 : tA ≠ F)
    (h10 : tB ≠ F) (l m : BitString) (f : Bool) (σ : Stacks k) (hA : σ A = l) (hB : σ B = m)
    (hF : σ F = [f]) :
    ExecLe (.loop A Option.isSome (eqStep A B tA tB F)) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ
        A []) B (m.drop l.length)) tA (l.reverse ++ σ tA))
        tB ((m.take l.length).reverse ++ σ tB)) F [f && decide (m.take l.length = l)])
      σ.space (17 * l.length + 1) := by
  have := (exec_eqLoop h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 l m f σ hA hB hF).execLe_loop_budget
    (by simp [eqStep, clearFlag, moveBit, caseBit, PopLoops, NoPush, Pops, h2.symm, h3.symm,
      h4.symm])
  have hb : (eqStep A B tA tB F).budget σ.space = 15 := by
    simp [eqStep, clearFlag, moveBit, caseBit, budget]
  rw [hA, hb] at this
  exact this.mono_time (by omega)

/-- **Equality test**, with a step budget `35 S + 9`, `S = σ.space + 1`. -/
theorem execLe_eqTest {A B tA tB F : Fin k} (h1 : A ≠ B) (h2 : A ≠ tA) (h3 : A ≠ tB)
    (h4 : A ≠ F) (h5 : B ≠ tA) (h6 : B ≠ tB) (h7 : B ≠ F) (h8 : tA ≠ tB) (h9 : tA ≠ F)
    (h10 : tB ≠ F) {σ : Stacks k} (htA : σ tA = []) (htB : σ tB = []) (hF : σ F = []) :
    ExecLe (eqTest A B tA tB F) σ (Function.update σ F [decide (σ A = σ B)]) (σ.space + 1)
      (35 * (σ.space + 1) + 9) := by
  have := (exec_eqTest h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 htA htB hF).execLe_budget
    (popLoops_eqTest h2 h3 h4 h6)
  rwa [budget_eqTest] at this

/-- **Decoding** one string, with a step budget `13 S + 5`, `S = σ.space + |z|`. -/
theorem execLe_decodeOne {Lst W Tmp : Fin k} (h1 : Lst ≠ W) (h2 : Lst ≠ Tmp) (h3 : W ≠ Tmp)
    {z rest : BitString} {σ : Stacks k} (hσ : σ Lst = Stacks.encStr z ++ rest) :
    ExecLe (decodeOne Lst W Tmp) σ
      (Function.update (Function.update (Function.update σ Lst rest) W (z.reverse ++ σ W)) Tmp
        ((Stacks.encStr z).reverse ++ σ Tmp)) (σ.space + z.length)
      (13 * (σ.space + z.length) + 5) := by
  have := (exec_decodeOne h1 h2 h3 hσ).execLe_budget (popLoops_decodeOne h1 h2)
  rwa [budget_decodeOne] at this

end Stmt

/-- One step of the membership test, with a step budget `57 S + 21`, `S = σ.space + |z| + 1`. -/
theorem Stmt.execLe_memStep {σ : Stacks 9} {z rest : BitString} {f : Bool}
    (h1 : σ 1 = Stacks.encStr z ++ rest) (h2 : σ 2 = [f]) (h3 : σ 3 = []) (h4 : σ 4 = [])
    (h6 : σ 6 = []) (h7 : σ 7 = []) (h8 : σ 8 = []) :
    ExecLe Stmt.memStep σ
      (Function.update (Function.update (Function.update σ 1 rest) 5
        ((Stacks.encStr z).reverse ++ σ 5)) 2 [f || decide (z = σ 0)])
      (σ.space + z.length + 1) (57 * (σ.space + z.length + 1) + 21) := by
  have := (Stmt.exec_memStep h1 h2 h3 h4 h6 h7 h8).execLe_budget Stmt.popLoops_memStep
  rwa [Stmt.budget_memStep] at this

/-- The membership loop: one iteration per element of `L` (at most `|encList L|`), each within
the budget of `memStep`. -/
theorem Stmt.execLe_memLoop (S : ℕ) (L : List BitString) (σ : Stacks 9) (f : Bool)
    (h1 : σ 1 = Stacks.encList L) (h2 : σ 2 = [f]) (h3 : σ 3 = []) (h4 : σ 4 = [])
    (h6 : σ 6 = []) (h7 : σ 7 = []) (h8 : σ 8 = [])
    (hS : σ.space + (Stacks.encList L).length + 1 ≤ S) :
    ExecLe (.loop 1 Option.isSome Stmt.memStep) σ
      (Function.update (Function.update (Function.update σ 1 []) 5
        ((Stacks.encList L).reverse ++ σ 5)) 2 [f || decide (σ 0 ∈ L)]) S
      ((Stacks.encList L).length * (57 * S + 23) + 1) := by
  have := (Stmt.exec_memLoop S L σ f h1 h2 h3 h4 h6 h7 h8 hS).execLe_loop_budget
    ⟨rfl, by
      simp [Stmt.memStep, Stmt.decodeOne, Stmt.decodeBody, Stmt.eqTest, Stmt.eqStep, Stmt.seqs,
        Stmt.clearFlag, Stmt.setFlag, Stmt.clear, Stmt.moveAll, Stmt.moveBit, Stmt.caseBit,
        Stmt.NoPush],
      by simp [Stmt.memStep, Stmt.decodeOne, Stmt.seqs, Stmt.moveBit, Stmt.caseBit, Stmt.Pops],
      Stmt.popLoops_memStep⟩
  rwa [h1, Stmt.budget_memStep] at this

/-- **Membership test**, with a step budget `57 S² + 29 S + 3`, `S = σ.space + |encList L| + 2`. -/
theorem Stmt.execLe_memTest {σ : Stacks 9} {L : List BitString} (h1 : σ 1 = Stacks.encList L)
    (h2 : σ 2 = []) (h3 : σ 3 = []) (h4 : σ 4 = []) (h5 : σ 5 = []) (h6 : σ 6 = [])
    (h7 : σ 7 = []) (h8 : σ 8 = []) :
    ExecLe Stmt.memTest σ (Function.update σ 2 [decide (σ 0 ∈ L)])
      (σ.space + (Stacks.encList L).length + 2)
      (57 * (σ.space + (Stacks.encList L).length + 2) * (σ.space + (Stacks.encList L).length + 2)
        + 29 * (σ.space + (Stacks.encList L).length + 2) + 3) := by
  have := (Stmt.exec_memTest h1 h2 h3 h4 h5 h6 h7 h8).execLe_budget Stmt.popLoops_memTest
  rwa [Stmt.budget_memTest] at this

/-! #### Step budgets of the helper statements of the routines -/

namespace Stmt

variable {k : ℕ}

/-- One step of the adder: at most `11` steps. -/
theorem execLe_addStep {A B Cy R : Fin k} (hAB : A ≠ B) (hAC : A ≠ Cy) (hAR : A ≠ R)
    (hBC : B ≠ Cy) (hBR : B ≠ R) (hCR : Cy ≠ R) {σ : Stacks k} {a b c : Bool} {l m : BitString}
    (hA : σ A = a :: l) (hB : σ B = b :: m) (hC : σ Cy = [c]) :
    ExecLe (addStep A B Cy R) σ
      (Function.update (Function.update (Function.update (Function.update σ A l) B m) Cy
        [carryBit a b c]) R (xor (xor a b) c :: σ R)) σ.space 11 := by
  have := (exec_addStep hAB hAC hAR hBC hBR hCR hA hB hC).execLe_budget
    (by simp [addStep, seqs, caseBit, PopLoops])
  rwa [show (addStep A B Cy R).budget σ.space = 11 by simp [addStep, seqs, caseBit, budget]]
    at this

/-- One step of the comparison: at most `10` steps. -/
theorem execLe_cmpStep {A B F : Fin k} (hAB : A ≠ B) (hAF : A ≠ F) (hBF : B ≠ F)
    {σ : Stacks k} {a b f : Bool} {l m : BitString}
    (hA : σ A = a :: l) (hB : σ B = b :: m) (hF : σ F = [f]) :
    ExecLe (cmpStep A B F) σ
      (Function.update (Function.update (Function.update σ A l) B m) F
        [if a == b then f else b]) σ.space 10 := by
  have := (exec_cmpStep hAB hAF hBF hA hB hF).execLe_budget
    (by simp [cmpStep, seqs, caseBit, PopLoops])
  rwa [show (cmpStep A B F).budget σ.space = 10 by simp [cmpStep, seqs, caseBit, budget]] at this

/-- One step of `copy`: at most `5` steps. -/
theorem execLe_dupStep {t r r' : Fin k} (htr : t ≠ r) (htr' : t ≠ r') (hrr : r ≠ r')
    {σ : Stacks k} {b : Bool} {l : BitString} (ht : σ t = b :: l) :
    ExecLe (dupStep t r r') σ
      (Function.update (Function.update (Function.update σ t l) r (b :: σ r)) r' (b :: σ r'))
      (σ.space + 1) 5 := by
  have := (exec_dupStep htr htr' hrr ht).execLe_budget
    (by simp [dupStep, seqs, caseBit, PopLoops])
  rwa [show (dupStep t r r').budget (σ.space + 1) = 5 by simp [dupStep, seqs, caseBit, budget]]
    at this

/-- The duplication loop of `copy`: `|l|` iterations of at most `5` steps. -/
theorem execLe_dupLoop {t r r' : Fin k} (htr : t ≠ r) (htr' : t ≠ r') (hrr : r ≠ r')
    (l : BitString) (σ : Stacks k) (ht : σ t = l) :
    ExecLe (.loop t Option.isSome (dupStep t r r')) σ
      (Function.update (Function.update (Function.update σ t []) r (l.reverse ++ σ r)) r'
        (l.reverse ++ σ r')) (σ.space + l.length) (7 * l.length + 1) := by
  have := (exec_dupLoop htr htr' hrr l σ ht).execLe_loop_budget
    (by simp [dupStep, seqs, caseBit, PopLoops, NoPush, Pops, htr.symm, htr'.symm])
  have hb : (dupStep t r r').budget (σ.space + l.length) = 5 := by
    simp [dupStep, seqs, caseBit, budget]
  rw [ht, hb] at this
  exact this.mono_time (by omega)

/-- The trailing-ones loop of `incr`: at most `4 |l| + 1` steps. -/
theorem execLe_incLoop {A t : Fin k} (hAt : A ≠ t) (l : BitString) (σ : Stacks k) (hσ : σ A = l) :
    ∃ (n : ℕ) (rest : BitString), l = List.replicate n true ++ rest ∧ rest.head? ≠ some true ∧
      ExecLe (.loop A isTrue (.seq (.pop A) (.push t false))) σ
        (Function.update (Function.update σ A rest) t (List.replicate n false ++ σ t)) σ.space
        (4 * l.length + 1) := by
  obtain ⟨n, rest, hl, hrest, hex⟩ := exec_incLoop hAt l σ hσ
  refine ⟨n, rest, hl, hrest, ?_⟩
  have := hex.execLe_loop_budget (by simp [PopLoops, NoPush, Pops, isTrue, hAt.symm])
  rw [hσ, show (Stmt.seq (.pop A) (.push t false) : Stmt k).budget σ.space = 2 by
    simp [budget]] at this
  exact this.mono_time (by omega)

end Stmt

/-! #### Polynomial step bounds from the syntax; inlining -/

namespace Stmt

variable {k : ℕ}

/-- The loop nesting depth. -/
def loopDepth : Stmt k → ℕ
  | .skip => 0
  | .push _ _ => 0
  | .pop _ => 0
  | .seq s₁ s₂ => max s₁.loopDepth s₂.loopDepth
  | .ite _ _ s₁ s₂ => max s₁.loopDepth s₂.loopDepth
  | .loop _ _ b => b.loopDepth + 1

/-- The budget is at most `size * (S + 1) ^ loopDepth`. -/
theorem budget_le_size_mul_pow (S : ℕ) :
    ∀ s : Stmt k, s.budget S ≤ s.size * (S + 1) ^ s.loopDepth
  | .skip => by simp [budget]
  | .push _ _ => by simp [budget, size, loopDepth]
  | .pop _ => by simp [budget, size, loopDepth]
  | .seq s₁ s₂ => by
    have h₁ := budget_le_size_mul_pow S s₁
    have h₂ := budget_le_size_mul_pow S s₂
    have p₁ : (S + 1) ^ s₁.loopDepth ≤ (S + 1) ^ max s₁.loopDepth s₂.loopDepth :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have p₂ : (S + 1) ^ s₂.loopDepth ≤ (S + 1) ^ max s₁.loopDepth s₂.loopDepth :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    simp only [budget, size, loopDepth]
    have q₁ := Nat.mul_le_mul_left s₁.size p₁
    have q₂ := Nat.mul_le_mul_left s₂.size p₂
    rw [Nat.add_mul]
    omega
  | .ite _ _ s₁ s₂ => by
    have h₁ := budget_le_size_mul_pow S s₁
    have h₂ := budget_le_size_mul_pow S s₂
    have p₁ : (S + 1) ^ s₁.loopDepth ≤ (S + 1) ^ max s₁.loopDepth s₂.loopDepth :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have p₂ : (S + 1) ^ s₂.loopDepth ≤ (S + 1) ^ max s₁.loopDepth s₂.loopDepth :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have p₀ : 1 ≤ (S + 1) ^ max s₁.loopDepth s₂.loopDepth := Nat.one_le_pow _ _ (by omega)
    simp only [budget, size, loopDepth]
    have q₁ := Nat.mul_le_mul_left s₁.size p₁
    have q₂ := Nat.mul_le_mul_left s₂.size p₂
    rw [Nat.add_mul, Nat.add_mul]
    refine max_le ?_ ?_ <;> omega
  | .loop _ _ b => by
    have h := budget_le_size_mul_pow S b
    have p₀ : 1 ≤ (S + 1) ^ b.loopDepth := Nat.one_le_pow _ _ (by omega)
    simp only [budget, size, loopDepth]
    rw [pow_succ]
    set P := (S + 1) ^ b.loopDepth
    have q₁ : S * b.budget S ≤ S * (b.size * P) := Nat.mul_le_mul_left S h
    have q₂ : S * 1 ≤ S * P := Nat.mul_le_mul_left S p₀
    nlinarith

end Stmt

/-- **Polynomial step bound.**  A statement all of whose loops are pop-loops, run within space
`S`, takes at most `s.size * (S + 1) ^ s.loopDepth` steps. -/
theorem Exec.execLe_size_mul_pow {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ}
    (h : Exec s σ σ' S) (hs : s.PopLoops) :
    ExecLe s σ σ' S (s.size * (S + 1) ^ s.loopDepth) :=
  (h.execLe_budget hs).mono_time (s.budget_le_size_mul_pow S)

namespace Stmt

variable {k k' : ℕ}

/-- Renaming the stacks preserves the size of the statement. -/
theorem size_rename (f : Fin k → Fin k') : ∀ s : Stmt k, (s.rename f).size = s.size
  | .skip => rfl
  | .push _ _ => rfl
  | .pop _ => rfl
  | .seq s₁ s₂ => by simp only [rename, size, size_rename f s₁, size_rename f s₂]
  | .ite _ _ s₁ s₂ => by simp only [rename, size, size_rename f s₁, size_rename f s₂]
  | .loop _ _ b => by simp only [rename, size, size_rename f b]

/-- Renaming the stacks preserves the loop depth of the statement. -/
theorem loopDepth_rename (f : Fin k → Fin k') : ∀ s : Stmt k, (s.rename f).loopDepth = s.loopDepth
  | .skip => rfl
  | .push _ _ => rfl
  | .pop _ => rfl
  | .seq s₁ s₂ => by simp only [rename, loopDepth, loopDepth_rename f s₁, loopDepth_rename f s₂]
  | .ite _ _ s₁ s₂ => by
    simp only [rename, loopDepth, loopDepth_rename f s₁, loopDepth_rename f s₂]
  | .loop _ _ b => by simp only [rename, loopDepth, loopDepth_rename f b]

/-- Renaming the stacks preserves the step budget of the statement. -/
theorem budget_rename (f : Fin k → Fin k') (S : ℕ) :
    ∀ s : Stmt k, (s.rename f).budget S = s.budget S
  | .skip => rfl
  | .push _ _ => rfl
  | .pop _ => rfl
  | .seq s₁ s₂ => by simp only [rename, budget, budget_rename f S s₁, budget_rename f S s₂]
  | .ite _ _ s₁ s₂ => by simp only [rename, budget, budget_rename f S s₁, budget_rename f S s₂]
  | .loop _ _ b => by simp only [rename, budget, budget_rename f S b]

/-- If a statement does not push to `j`, then renaming the stacks via an injective function ensures
it does not push to `f j`. -/
theorem noPush_rename {f : Fin k → Fin k'} (hf : Function.Injective f) {j : Fin k} :
    ∀ s : Stmt k, s.NoPush j → (s.rename f).NoPush (f j)
  | .skip, _ => trivial
  | .push _ _, h => fun e => h (hf e)
  | .pop _, _ => trivial
  | .seq s₁ s₂, h => ⟨noPush_rename hf s₁ h.1, noPush_rename hf s₂ h.2⟩
  | .ite _ _ s₁ s₂, h => ⟨noPush_rename hf s₁ h.1, noPush_rename hf s₂ h.2⟩
  | .loop _ _ b, h => noPush_rename hf b h

/-- If a statement pops from `j`, then renaming the stacks ensures it pops from `f j`. -/
theorem pops_rename (f : Fin k → Fin k') {j : Fin k} :
    ∀ s : Stmt k, s.Pops j → (s.rename f).Pops (f j)
  | .skip, h => h.elim
  | .push _ _, h => h.elim
  | .pop _, h => congrArg f h
  | .seq s₁ s₂, h => h.imp (pops_rename f s₁) (pops_rename f s₂)
  | .ite _ _ s₁ s₂, h => ⟨pops_rename f s₁ h.1, pops_rename f s₂ h.2⟩
  | .loop _ _ b, h => ⟨congrArg f h.1, h.2.1, pops_rename f b h.2.2⟩

/-- Inlining keeps the loops pop-loops. -/
theorem popLoops_rename {f : Fin k → Fin k'} (hf : Function.Injective f) :
    ∀ s : Stmt k, s.PopLoops → (s.rename f).PopLoops
  | .skip, _ => trivial
  | .push _ _, _ => trivial
  | .pop _, _ => trivial
  | .seq s₁ s₂, h => ⟨popLoops_rename hf s₁ h.1, popLoops_rename hf s₂ h.2⟩
  | .ite _ _ s₁ s₂, h => ⟨popLoops_rename hf s₁ h.1, popLoops_rename hf s₂ h.2⟩
  | .loop _ _ b, h => ⟨h.1, noPush_rename hf b h.2.1, pops_rename f b h.2.2.1,
      popLoops_rename hf b h.2.2.2⟩

/-- Sequences of pop-loop statements. -/
theorem popLoops_seqs : ∀ l : List (Stmt k'), (∀ s ∈ l, s.PopLoops) → (seqs l).PopLoops
  | [], _ => trivial
  | s :: l, h => ⟨h s (by simp), popLoops_seqs l fun t ht => h t (by simp [ht])⟩

/-- A sequence of statements that do not push to `j` also does not push to `j`. -/
theorem noPush_seqs {j : Fin k'} : ∀ l : List (Stmt k'), (∀ s ∈ l, s.NoPush j) → (seqs l).NoPush j
  | [], _ => trivial
  | s :: l, h => ⟨h s (by simp), noPush_seqs l fun t ht => h t (by simp [ht])⟩

/-- The size of a sequence of statements is the sum of their sizes. -/
theorem size_seqs : ∀ l : List (Stmt k'), (seqs l).size = (l.map size).sum
  | [] => rfl
  | s :: l => by simp [seqs, size, size_seqs l]

end Stmt

namespace Stmt

variable {k : ℕ}

/-- The step budget of a sequence of statements is the sum of their step budgets. -/
theorem budget_seqs (S : ℕ) : ∀ l : List (Stmt k), (seqs l).budget S = (l.map (budget S)).sum
  | [] => rfl
  | s :: l => by simp [seqs, budget, budget_seqs S l]

/-- The step budget of pushing a list is the length of the list. -/
theorem budget_pushList (r : Fin k) (S : ℕ) : ∀ l : BitString, (pushList r l).budget S = l.length
  | [] => rfl
  | _ :: l => by simp [pushList, budget, budget_pushList r S l]

/-- A `caseBit` statement whose branches only have pop-loops also only has pop-loops. -/
theorem popLoops_caseBit (r : Fin k) (s : Bool → Stmt k) (h : ∀ b, (s b).PopLoops) :
    (caseBit r s).PopLoops :=
  ⟨h true, h false⟩

/-- The step budget of a `caseBit` statement is the maximum of the true branch's budget plus two
and the false branch's budget plus one. -/
theorem budget_caseBit (r : Fin k) (s : Bool → Stmt k) (S : ℕ) :
    (caseBit r s).budget S = max ((s true).budget S + 2) ((s false).budget S + 1) := rfl

end Stmt

/-! #### Local step budgets: only the stacks a routine touches count

If `s` writes only the stacks of a set `U`, the stacks outside `U` keep their total length
`Stacks.restOff U σ` along the run, so the pop-loops iterate at most `L` times as soon as
`S ≤ L + restOff U σ`; for the routines below `L` is the total length of their own stacks (plus
the extra space of the `exec_*` lemma), independently of the other stacks of the program. -/

/-- The total length of the stacks outside `U`. -/
def Stacks.restOff {k : ℕ} (U : Finset (Fin k)) (σ : Stacks k) : ℕ := ∑ j ∈ Uᶜ, (σ j).length

/-- The total space used by the stacks is the sum of the lengths of the stacks in `U` plus the
length of the remaining stacks. -/
theorem Stacks.space_eq_sum_add_restOff {k : ℕ} (U : Finset (Fin k)) (σ : Stacks k) :
    σ.space = ∑ j ∈ U, (σ j).length + Stacks.restOff U σ :=
  (Finset.sum_add_sum_compl U _).symm

/-- A statement writing only stacks in `U` keeps the total length of the other stacks. -/
theorem Exec.restOff_eq {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ} (h : Exec s σ σ' S)
    {U : Finset (Fin k)} (hU : ∀ j, s.Writes j → j ∈ U) :
    Stacks.restOff U σ' = Stacks.restOff U σ :=
  Finset.sum_congr rfl fun j hj => by
    rw [h.frame fun hw => (Finset.mem_compl.1 hj) (hU j hw)]

/-- If a statement pops from a stack `j`, then it writes to `j`. -/
theorem Stmt.writes_of_pops {k : ℕ} {j : Fin k} : ∀ s : Stmt k, s.Pops j → s.Writes j
  | .skip, h => h.elim
  | .push _ _, h => h.elim
  | .pop _, h => h
  | .seq s₁ s₂, h => h.imp (writes_of_pops s₁) (writes_of_pops s₂)
  | .ite _ _ s₁ _, h => Or.inl (writes_of_pops s₁ h.1)
  | .loop _ _ b, h => writes_of_pops b h.2.2

/-- **Local step budget.**  A statement all of whose loops are pop-loops and which writes only the
stacks of `U`, run within space `S ≤ L + restOff U σ`, takes at most `s.budget L` steps. -/
theorem Stmt.execLe_budget_on {k : ℕ} (U : Finset (Fin k)) :
    ∀ (s : Stmt k), s.PopLoops → (∀ j, s.Writes j → j ∈ U) → ∀ {σ σ' : Stacks k} {S L : ℕ},
      Exec s σ σ' S → S ≤ L + Stacks.restOff U σ → ExecLe s σ σ' S (s.budget L)
  | .skip, _, _, _, _, _, _, h, _ => by cases h with | skip hS => exact ExecLe.skip hS
  | .push _ _, _, _, _, _, _, _, h, _ => by cases h with | push hS => exact ExecLe.push hS le_rfl
  | .pop _, _, _, _, _, _, _, h, _ => by cases h with | pop hS => exact ExecLe.pop hS le_rfl
  | .seq s₁ s₂, hs, hU, _, _, _, _, h, hL => by
    obtain ⟨σ₁, h₁, h₂⟩ := Exec.seq_iff.1 h
    have hU₁ : ∀ j, s₁.Writes j → j ∈ U := fun j hj => hU j (Or.inl hj)
    have hU₂ : ∀ j, s₂.Writes j → j ∈ U := fun j hj => hU j (Or.inr hj)
    exact (s₁.execLe_budget_on U hs.1 hU₁ h₁ hL).seq
      (s₂.execLe_budget_on U hs.2 hU₂ h₂ (by rw [h₁.restOff_eq hU₁]; exact hL))
  | .ite _ _ s₁ s₂, hs, hU, _, _, _, _, h, hL => by
    cases h with
    | iteT hc h =>
      obtain ⟨T, hT, h⟩ := s₁.execLe_budget_on U hs.1 (fun j hj => hU j (Or.inl hj)) h hL
      refine ⟨T + 2, ?_, .iteT hc h⟩
      simp only [Stmt.budget]
      exact (Nat.add_le_add_right hT 2).trans (le_max_left _ _)
    | iteF hc h =>
      obtain ⟨T, hT, h⟩ := s₂.execLe_budget_on U hs.2 (fun j hj => hU j (Or.inr hj)) h hL
      refine ⟨T + 1, ?_, .iteF hc h⟩
      simp only [Stmt.budget]
      exact (Nat.add_le_add_right hT 1).trans (le_max_right _ _)
  | .loop r cond b, hs, hU, σ, _, S, L, h, hL => by
    obtain ⟨hc0, hn, hp, hb⟩ := hs
    have hUb : ∀ j, b.Writes j → j ∈ U := hU
    have key := ExecLe.loop_of_exec (r := r) (cond := cond) (body := b)
      (fun σ₁ => S ≤ L + Stacks.restOff U σ₁) (fun σ₁ => (σ₁ r).length) S (b.budget L)
      (fun σ₁ σ₂ hI hc hex => ⟨b.execLe_budget_on U hb hUb hex hI,
        by rw [hex.restOff_eq hUb]; exact hI,
        hex.length_lt_of_pops hn hp (by intro he; rw [he] at hc; simp [hc0] at hc)⟩) σ _ hL h
    refine key.mono_time ?_
    have hr : r ∈ U := hU r (b.writes_of_pops hp)
    have h1 : (σ r).length ≤ ∑ j ∈ U, (σ j).length :=
      Finset.single_le_sum (f := fun j => (σ j).length) (fun _ _ => Nat.zero_le _) hr
    have h2 := Stacks.space_eq_sum_add_restOff U σ
    have h3 := h.space_le.1
    have h4 : (σ r).length ≤ L := by omega
    simp only [Stmt.budget]
    exact Nat.add_le_add_right (Nat.mul_le_mul h4 le_rfl) 1

/-- **Local step budget**, `Exec` form. -/
theorem Exec.execLe_budget_on {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S L : ℕ}
    (h : Exec s σ σ' S) (hs : s.PopLoops) (U : Finset (Fin k)) (hU : ∀ j, s.Writes j → j ∈ U)
    (hL : S ≤ L + Stacks.restOff U σ) : ExecLe s σ σ' S (s.budget L) :=
  s.execLe_budget_on U hs hU h hL

namespace Stmt

variable {k : ℕ}

/-- **Addition**, local budget: `22 (|l| + |m| + 1) + 4` steps. -/
theorem execLe_addInto_local {A B Cy R : Fin k} (hAB : A ≠ B) (hAC : A ≠ Cy) (hAR : A ≠ R)
    (hBC : B ≠ Cy) (hBR : B ≠ R) (hCR : Cy ≠ R) {σ : Stacks k} {l m : BitString}
    (h : l.length = m.length) (hA : σ A = l) (hB : σ B = m) (hC : σ Cy = []) (hR : σ R = []) :
    ExecLe (addInto A B Cy R) σ (Function.update (Function.update σ A (addBits false l m)) B [])
      (σ.space + 1) (22 * (l.length + m.length + 1) + 4) := by
  have := (exec_addInto hAB hAC hAR hBC hBR hCR h hA hB hC hR).execLe_budget_on
    (popLoops_addInto hAC hAR) {A, B, Cy, R}
    (fun j hj => by
      simp [addInto, addStep, seqs, clear, moveAll, moveBit, caseBit, Writes] at hj
      aesop)
    (L := l.length + m.length + 1) (by
      have e := Stacks.space_eq_sum_add_restOff {A, B, Cy, R} σ
      simp [Finset.sum_insert, hAB, hAC, hAR, hBC, hBR, hCR, hA, hB, hC, hR] at e
      omega)
  rwa [budget_addInto] at this

/-- **Comparison**, local budget: `12 (|l| + |m| + 1) + 2` steps. -/
theorem execLe_cmpInto_local {A B F : Fin k} (hAB : A ≠ B) (hAF : A ≠ F) (hBF : B ≠ F)
    {σ : Stacks k} {l m : BitString} (h : l.length = m.length) (hA : σ A = l) (hB : σ B = m)
    (hF : σ F = []) :
    ExecLe (cmpInto A B F) σ
      (Function.update (Function.update (Function.update σ A []) B []) F [cmpBits true l m])
      (σ.space + 1) (12 * (l.length + m.length + 1) + 2) := by
  have := (exec_cmpInto hAB hAF hBF h hA hB hF).execLe_budget_on (popLoops_cmpInto hAF)
    {A, B, F}
    (fun j hj => by
      simp [cmpInto, cmpStep, seqs, caseBit, Writes] at hj
      aesop)
    (L := l.length + m.length + 1) (by
      have e := Stacks.space_eq_sum_add_restOff {A, B, F} σ
      simp [Finset.sum_insert, hAB, hAF, hBF, hA, hB, hF] at e
      omega)
  rwa [budget_cmpInto] at this

/-- **Binary increment**, local budget: `10 (|σ A| + 1) + 7` steps. -/
theorem execLe_incr_local {A t C : Fin k} (hAt : A ≠ t) (hAC : A ≠ C) (htC : t ≠ C)
    {σ : Stacks k} (ht : σ t = []) (hC : σ C = []) :
    ExecLe (incr A t C) σ
      (Function.update (Function.update σ A (incBits (σ A))) C [incCarry (σ A)])
      (σ.space + 1) (10 * ((σ A).length + 1) + 7) := by
  have := (exec_incr hAt hAC htC ht hC).execLe_budget_on (popLoops_incr hAt) {A, t, C}
    (fun j hj => by
      simp [incr, seqs, moveAll, moveBit, caseBit, Writes] at hj
      aesop)
    (L := (σ A).length + 1) (by
      have e := Stacks.space_eq_sum_add_restOff {A, t, C} σ
      simp [Finset.sum_insert, hAt, hAC, htC, ht, hC] at e
      omega)
  rwa [budget_incr] at this

/-- **Equality test**, local budget: `35 (|σ A| + |σ B| + 1) + 9` steps. -/
theorem execLe_eqTest_local {A B tA tB F : Fin k} (h1 : A ≠ B) (h2 : A ≠ tA) (h3 : A ≠ tB)
    (h4 : A ≠ F) (h5 : B ≠ tA) (h6 : B ≠ tB) (h7 : B ≠ F) (h8 : tA ≠ tB) (h9 : tA ≠ F)
    (h10 : tB ≠ F) {σ : Stacks k} (htA : σ tA = []) (htB : σ tB = []) (hF : σ F = []) :
    ExecLe (eqTest A B tA tB F) σ (Function.update σ F [decide (σ A = σ B)]) (σ.space + 1)
      (35 * ((σ A).length + (σ B).length + 1) + 9) := by
  have := (exec_eqTest h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 htA htB hF).execLe_budget_on
    (popLoops_eqTest h2 h3 h4 h6) {A, B, tA, tB, F}
    (fun j hj => by
      simp [eqTest, eqStep, seqs, clearFlag, moveAll, moveBit, caseBit, Writes] at hj
      aesop)
    (L := (σ A).length + (σ B).length + 1) (by
      have e := Stacks.space_eq_sum_add_restOff {A, B, tA, tB, F} σ
      simp [Finset.sum_insert, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, htA, htB, hF] at e
      omega)
  rwa [budget_eqTest] at this

/-- **Decoding**, local budget: `13 (|σ Lst| + |σ W| + |σ Tmp| + |z|) + 5` steps. -/
theorem execLe_decodeOne_local {Lst W Tmp : Fin k} (h1 : Lst ≠ W) (h2 : Lst ≠ Tmp)
    (h3 : W ≠ Tmp) {z rest : BitString} {σ : Stacks k} (hσ : σ Lst = Stacks.encStr z ++ rest) :
    ExecLe (decodeOne Lst W Tmp) σ
      (Function.update (Function.update (Function.update σ Lst rest) W (z.reverse ++ σ W)) Tmp
        ((Stacks.encStr z).reverse ++ σ Tmp)) (σ.space + z.length)
      (13 * ((σ Lst).length + (σ W).length + (σ Tmp).length + z.length) + 5) := by
  have := (exec_decodeOne h1 h2 h3 hσ).execLe_budget_on (popLoops_decodeOne h1 h2)
    {Lst, W, Tmp}
    (fun j hj => by
      simp [decodeOne, decodeBody, moveBit, caseBit, Writes] at hj
      aesop)
    (L := (σ Lst).length + (σ W).length + (σ Tmp).length + z.length) (by
      have e := Stacks.space_eq_sum_add_restOff {Lst, W, Tmp} σ
      simp [Finset.sum_insert, h1, h2, h3] at e
      omega)
  rwa [budget_decodeOne] at this

/-- **Copy**, local budget: `13 (2 |σ r| + |σ r'|) + 2` steps. -/
theorem execLe_copy_local {r r' t : Fin k} (hrr : r ≠ r') (hrt : r ≠ t) (hr't : r' ≠ t)
    {σ : Stacks k} (ht : σ t = []) :
    ExecLe (copy r r' t) σ (Function.update σ r' (σ r ++ σ r')) (σ.space + (σ r).length)
      (13 * (2 * (σ r).length + (σ r').length) + 2) := by
  have := (exec_copy hrr hrt hr't ht).execLe_budget_on (popLoops_copy hrt hr't) {r, r', t}
    (fun j hj => by
      simp [copy, dupStep, seqs, moveAll, moveBit, caseBit, Writes] at hj
      aesop)
    (L := 2 * (σ r).length + (σ r').length) (by
      have e := Stacks.space_eq_sum_add_restOff {r, r', t} σ
      simp [Finset.sum_insert, hrr, hrt, hr't, ht] at e
      omega)
  rwa [budget_copy] at this

end Stmt

end Kolmogorov.RandomStrings
