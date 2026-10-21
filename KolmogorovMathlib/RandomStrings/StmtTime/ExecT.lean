/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace

/-!
# Step counts for structured stack programs: the framework

`ExecT`, the big-step semantics with an exact step count, its structural lemmas and the
correctness of the compiler with step counts; inlining keeps the step count; `ExecLe`, executions
within a step budget, with the loop rules; and the step counts of the basic routines and of
existing `Exec` derivations.

Part of `KolmogorovMathlib.RandomStrings.StmtTime`.
-/

namespace Kolmogorov.RandomStrings

/-- Big-step semantics with a space bound `S` and the exact number `T` of steps of the compiled
code. -/
inductive ExecT {k : ℕ} : Stmt k → Stacks k → Stacks k → ℕ → ℕ → Prop
  | skip {σ : Stacks k} {S : ℕ} : σ.space ≤ S → ExecT .skip σ σ S 0
  | push {r : Fin k} {b : Bool} {σ : Stacks k} {S : ℕ} : σ.space + 1 ≤ S →
      ExecT (.push r b) σ (Function.update σ r (b :: σ r)) S 1
  | pop {r : Fin k} {σ : Stacks k} {S : ℕ} : σ.space ≤ S →
      ExecT (.pop r) σ (Function.update σ r (σ r).tail) S 1
  | seq {s₁ s₂ : Stmt k} {σ σ₁ σ₂ : Stacks k} {S T₁ T₂ : ℕ} :
      ExecT s₁ σ σ₁ S T₁ → ExecT s₂ σ₁ σ₂ S T₂ → ExecT (.seq s₁ s₂) σ σ₂ S (T₁ + T₂)
  | iteT {r : Fin k} {cond : Option Bool → Bool} {s₁ s₂ : Stmt k} {σ σ' : Stacks k} {S T : ℕ} :
      cond (σ r).head? = true → ExecT s₁ σ σ' S T → ExecT (.ite r cond s₁ s₂) σ σ' S (T + 2)
  | iteF {r : Fin k} {cond : Option Bool → Bool} {s₁ s₂ : Stmt k} {σ σ' : Stacks k} {S T : ℕ} :
      cond (σ r).head? = false → ExecT s₂ σ σ' S T → ExecT (.ite r cond s₁ s₂) σ σ' S (T + 1)
  | loopT {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k} {σ σ₁ σ₂ : Stacks k}
      {S T₁ T₂ : ℕ} : cond (σ r).head? = true → ExecT body σ σ₁ S T₁ →
      ExecT (.loop r cond body) σ₁ σ₂ S T₂ → ExecT (.loop r cond body) σ σ₂ S (T₁ + T₂ + 2)
  | loopF {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k} {σ : Stacks k} {S : ℕ} :
      cond (σ r).head? = false → σ.space ≤ S → ExecT (.loop r cond body) σ σ S 1

namespace ExecT

variable {k : ℕ}

/-- Forgetting the step count. -/
theorem toExec {s : Stmt k} {σ σ' : Stacks k} {S T : ℕ} (h : ExecT s σ σ' S T) :
    Exec s σ σ' S := by
  induction h with
  | skip h => exact .skip h
  | push h => exact .push h
  | pop h => exact .pop h
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc _ ih => exact .iteT hc ih
  | iteF hc _ ih => exact .iteF hc ih
  | loopT hc _ _ ih₁ ih₂ => exact .loopT hc ih₁ ih₂
  | loopF hc h => exact .loopF hc h

/-- The space bound can be raised. -/
theorem mono {s : Stmt k} {σ σ' : Stacks k} {S S' T : ℕ} (h : ExecT s σ σ' S T) (hS : S ≤ S') :
    ExecT s σ σ' S' T := by
  induction h with
  | skip h => exact .skip (h.trans hS)
  | push h => exact .push (h.trans hS)
  | pop h => exact .pop (h.trans hS)
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ hS) (ih₂ hS)
  | iteT hc _ ih => exact .iteT hc (ih hS)
  | iteF hc _ ih => exact .iteF hc (ih hS)
  | loopT hc _ _ ih₁ ih₂ => exact .loopT hc (ih₁ hS) (ih₂ hS)
  | loopF hc h => exact .loopF hc (h.trans hS)

/-- Rewriting the step count along an equality. -/
theorem cast {s : Stmt k} {σ σ' : Stacks k} {S T T' : ℕ} (h : ExecT s σ σ' S T) (e : T = T') :
    ExecT s σ σ' S T' := e ▸ h

/-- Determinism: the final stacks and the step count are determined. -/
theorem det {s : Stmt k} {σ σ₁ σ₂ : Stacks k} {S₁ S₂ T₁ T₂ : ℕ} (h₁ : ExecT s σ σ₁ S₁ T₁)
    (h₂ : ExecT s σ σ₂ S₂ T₂) : σ₁ = σ₂ ∧ T₁ = T₂ := by
  induction h₁ generalizing σ₂ S₂ T₂ with
  | skip _ => cases h₂; exact ⟨rfl, rfl⟩
  | push _ => cases h₂; exact ⟨rfl, rfl⟩
  | pop _ => cases h₂; exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂₁ h₂₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₂₁
      obtain ⟨rfl, rfl⟩ := ih₂ h₂₂
      exact ⟨rfl, rfl⟩
  | iteT hc _ ih =>
    cases h₂ with
    | iteT _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
    | iteF hc' _ => cases hc.symm.trans hc'
  | iteF hc _ ih =>
    cases h₂ with
    | iteT hc' _ => cases hc.symm.trans hc'
    | iteF _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
  | loopT hc _ _ ih₁ ih₂ =>
    cases h₂ with
    | loopT _ hb hl =>
      obtain ⟨rfl, rfl⟩ := ih₁ hb
      obtain ⟨rfl, rfl⟩ := ih₂ hl
      exact ⟨rfl, rfl⟩
    | loopF hc' _ => cases hc.symm.trans hc'
  | loopF hc _ =>
    cases h₂ with
    | loopT hc' _ _ => cases hc.symm.trans hc'
    | loopF _ _ => exact ⟨rfl, rfl⟩

/-- A sequential composition takes the sum of the components' steps. -/
theorem seq_iff {s₁ s₂ : Stmt k} {σ σ₂ : Stacks k} {S T : ℕ} :
    ExecT (.seq s₁ s₂) σ σ₂ S T ↔
      ∃ σ₁ T₁ T₂, ExecT s₁ σ σ₁ S T₁ ∧ ExecT s₂ σ₁ σ₂ S T₂ ∧ T = T₁ + T₂ := by
  constructor
  · intro h
    cases h with | seq h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩
  · rintro ⟨σ₁, T₁, T₂, h₁, h₂, rfl⟩
    exact .seq h₁ h₂

end ExecT

/-- Every terminating execution has a step count. -/
theorem Exec.exists_execT {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ} (h : Exec s σ σ' S) :
    ∃ T, ExecT s σ σ' S T := by
  induction h with
  | skip h => exact ⟨_, .skip h⟩
  | push h => exact ⟨_, .push h⟩
  | pop h => exact ⟨_, .pop h⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨T₁, h₁⟩ := ih₁
    obtain ⟨T₂, h₂⟩ := ih₂
    exact ⟨_, .seq h₁ h₂⟩
  | iteT hc _ ih => obtain ⟨T, h⟩ := ih; exact ⟨_, .iteT hc h⟩
  | iteF hc _ ih => obtain ⟨T, h⟩ := ih; exact ⟨_, .iteF hc h⟩
  | loopT hc _ _ ih₁ ih₂ =>
    obtain ⟨T₁, h₁⟩ := ih₁
    obtain ⟨T₂, h₂⟩ := ih₂
    exact ⟨_, .loopT hc h₁ h₂⟩
  | loopF hc h => exact ⟨_, .loopF hc h⟩

/-! #### Counted runs of compiled code -/

/-- `c` reaches `c'` in exactly `n` steps of `P`, all configurations on the way (both ends
included) having space `≤ S`. -/
def Prog.ReachesIn (P : Prog) (c c' : PConfig P) (S n : ℕ) : Prop :=
  P.step^[n] c = c' ∧ ∀ m ≤ n, (P.step^[m] c).space ≤ S

/-- A configuration within space `S` reaches itself in zero steps. -/
theorem Prog.ReachesIn.refl {P : Prog} {c : PConfig P} {S : ℕ} (h : c.space ≤ S) :
    P.ReachesIn c c S 0 :=
  ⟨rfl, fun m hm => by rw [Nat.le_zero.1 hm]; exact h⟩

/-- A step from `c` to `c'` gives a one-step run when both configurations fit within `S`. -/
theorem Prog.ReachesIn.single {P : Prog} {c c' : PConfig P} {S : ℕ} (hc : P.step c = c')
    (h : c.space ≤ S) (h' : c'.space ≤ S) : P.ReachesIn c c' S 1 :=
  ⟨by simpa using hc, fun m hm => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
    · exact h
    · simpa [hc] using h'⟩

/-- Concatenation of counted runs. -/
theorem Prog.ReachesIn.trans {P : Prog} {c₁ c₂ c₃ : PConfig P} {S n₁ n₂ : ℕ}
    (h₁ : P.ReachesIn c₁ c₂ S n₁) (h₂ : P.ReachesIn c₂ c₃ S n₂) :
    P.ReachesIn c₁ c₃ S (n₁ + n₂) := by
  obtain ⟨e₁, s₁⟩ := h₁
  obtain ⟨e₂, s₂⟩ := h₂
  refine ⟨by rw [Nat.add_comm, Function.iterate_add_apply, e₁, e₂], fun m hm => ?_⟩
  rcases Nat.lt_or_ge m n₁ with hlt | hge
  · exact s₁ m hlt.le
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
    rw [Nat.add_comm n₁ j, Function.iterate_add_apply, e₁]
    exact s₂ j (by omega)

/-- Equal step counts describe the same run within space `S`. -/
theorem Prog.ReachesIn.cast {P : Prog} {c c' : PConfig P} {S n m : ℕ}
    (h : P.ReachesIn c c' S n) (e : n = m) : P.ReachesIn c c' S m := e ▸ h

/-- **Correctness of the compiler, with step counts.**  If `s` executes from `σ` to `σ'` within
space `S` in `T` steps, then its compiled code, placed at any address `a` of any program, runs from
`⟨a, σ⟩` to `⟨a + s.size, σ'⟩` in exactly `T` steps through configurations of space `≤ S`. -/
theorem ExecT.reachesIn {P : Prog} {s : Stmt P.k} {σ σ' : Stacks P.k} {S T : ℕ}
    (h : ExecT s σ σ' S T) :
    ∀ a, P.CodeAt a (s.compile a) → P.ReachesIn ⟨a, σ⟩ ⟨a + s.size, σ'⟩ S T := by
  induction h with
  | skip hS => intro a _; exact Prog.ReachesIn.refl hS
  | @push r b σ S hS =>
    intro a hc
    simp only [Stmt.compile] at hc
    exact Prog.ReachesIn.single (Prog.step_mk_push hc.head) (by change σ.space ≤ S; omega)
      (by
        change Stacks.space (Function.update σ r (b :: σ r)) ≤ S
        rw [Stacks.space_update_cons]; exact hS)
  | @pop r σ S hS =>
    intro a hc
    simp only [Stmt.compile] at hc
    exact Prog.ReachesIn.single (Prog.step_mk_pop hc.head) hS
      ((Stacks.space_update_tail_le σ r).trans hS)
  | @seq s₁ s₂ σ σ₁ σ₂ S T₁ T₂ h₁ h₂ ih₁ ih₂ =>
    intro a hc
    simp only [Stmt.compile] at hc
    have r₁ := ih₁ a hc.append_left
    have hc₂ := hc.append_right
    rw [Stmt.length_compile] at hc₂
    have r₂ := ih₂ _ hc₂
    have e : a + (Stmt.seq s₁ s₂).size = a + s₁.size + s₂.size := by
      simp only [Stmt.size]; omega
    rw [e]; exact r₁.trans r₂
  | @iteT r cond s₁ s₂ σ σ' S T hcnd h ih =>
    intro a hc
    simp only [Stmt.compile] at hc
    have e0 := Prog.step_mk_test (σ := σ) hc.head
    rw [ite_eq_left hcnd] at e0
    have hsp := h.toExec.space_le
    have r₀ : P.ReachesIn ⟨a, σ⟩ ⟨a + 1, σ⟩ S 1 := Prog.ReachesIn.single e0 hsp.1 hsp.1
    have hc1 := hc.tail
    have r₁ := ih (a + 1) hc1.append_left
    have hc2 := hc1.append_right
    rw [Stmt.length_compile] at hc2
    have e2 := Prog.step_mk_jump (σ := σ') hc2.head
    have r₂ : P.ReachesIn ⟨a + 1 + s₁.size, σ'⟩ ⟨a + s₁.size + s₂.size + 2, σ'⟩ S 1 :=
      Prog.ReachesIn.single e2 hsp.2 hsp.2
    have e : a + (Stmt.ite r cond s₁ s₂).size = a + s₁.size + s₂.size + 2 := by
      simp only [Stmt.size]; omega
    rw [e]; exact (r₀.trans (r₁.trans r₂)).cast (by omega)
  | @iteF r cond s₁ s₂ σ σ' S T hcnd h ih =>
    intro a hc
    simp only [Stmt.compile] at hc
    have e0 := Prog.step_mk_test (σ := σ) hc.head
    rw [ite_eq_right (by simp [hcnd])] at e0
    have hsp := h.toExec.space_le
    have r₀ : P.ReachesIn ⟨a, σ⟩ ⟨a + s₁.size + 2, σ⟩ S 1 := Prog.ReachesIn.single e0 hsp.1 hsp.1
    have hc2 := hc.tail.append_right
    rw [Stmt.length_compile] at hc2
    have hc3 := hc2.tail
    rw [show a + 1 + s₁.size + 1 = a + s₁.size + 2 by omega] at hc3
    have r₁ := ih _ hc3
    have e : a + (Stmt.ite r cond s₁ s₂).size = a + s₁.size + 2 + s₂.size := by
      simp only [Stmt.size]; omega
    rw [e]; exact (r₀.trans r₁).cast (by omega)
  | @loopT r cond body σ σ₁ σ₂ S T₁ T₂ hcnd hb hl ihb ihl =>
    intro a hc
    have hc' := hc
    simp only [Stmt.compile] at hc
    have e0 := Prog.step_mk_test (σ := σ) hc.head
    rw [ite_eq_left hcnd] at e0
    have hsb := hb.toExec.space_le
    have r₀ : P.ReachesIn ⟨a, σ⟩ ⟨a + 1, σ⟩ S 1 := Prog.ReachesIn.single e0 hsb.1 hsb.1
    have hc1 := hc.tail
    have r₁ := ihb (a + 1) hc1.append_left
    have hc2 := hc1.append_right
    rw [Stmt.length_compile] at hc2
    have e2 := Prog.step_mk_jump (σ := σ₁) hc2.head
    have r₂ : P.ReachesIn ⟨a + 1 + body.size, σ₁⟩ ⟨a, σ₁⟩ S 1 :=
      Prog.ReachesIn.single e2 hsb.2 hsb.2
    exact (r₀.trans (r₁.trans (r₂.trans (ihl a hc')))).cast (by omega)
  | @loopF r cond body σ S hcnd hS =>
    intro a hc
    simp only [Stmt.compile] at hc
    have e0 := Prog.step_mk_test (σ := σ) hc.head
    rw [ite_eq_right (by simp [hcnd])] at e0
    have e : a + (Stmt.loop r cond body).size = a + body.size + 2 := by
      simp only [Stmt.size]; omega
    rw [e]; exact Prog.ReachesIn.single e0 hS hS

/-- A terminating execution of `s` on the input in `T` steps gives a run of `s.toProg out`
halting at time `T + 1` within the same space, accepting iff the output stack has `true` on
top. -/
theorem Stmt.toProg_spec_time {k : ℕ} (s : Stmt k) (out : Fin k) (x : BitString) (σ' : Stacks k)
    (S T : ℕ) (h : ExecT s (Stacks.input k x) σ' S T) :
    (s.toProg out).Halted ((s.toProg out).run x (T + 1)) ∧
      (∀ u ≤ T + 1, ((s.toProg out).run x u).space ≤ S) ∧
      ((s.toProg out).Accepting ((s.toProg out).run x (T + 1)) ↔
        (σ' out).head? = some true) := by
  have hcode : (s.toProg out).CodeAt 0 (s.compile 0) := fun i hi => by
    rw [Nat.zero_add]
    exact s.progCode_left out i (hi.trans_eq (Stmt.length_compile s 0))
  obtain ⟨hn, hsp⟩ := ExecT.reachesIn (P := s.toProg out) h 0 hcode
  rw [Nat.zero_add] at hn
  have hσ' : σ'.space ≤ S := h.toExec.space_le.2
  have e0 : (s.toProg out).code[s.size]? =
      some (Stmt.testInstr out (fun o => o == some true) (s.size + 1) (s.size + 2)) := by
    have := s.progCode_right out 0
    rw [Nat.add_zero] at this
    exact this
  have hlast := Prog.step_mk_test (P := s.toProg out) (σ := σ') e0
  have hrun : (s.toProg out).run x (T + 1) =
      ⟨if (σ' out).head? == some true then s.size + 1 else s.size + 2, σ'⟩ := by
    rw [Prog.run_eq_iterate, Function.iterate_succ_apply']
    exact (congrArg (s.toProg out).step hn).trans hlast
  have hacc : (s.toProg out).code[s.size + 1]? = some .accept := s.progCode_right out 1
  have hrej : (s.toProg out).code[s.size + 2]? = some .reject := s.progCode_right out 2
  refine ⟨?_, fun u hu => ?_, ?_⟩
  · rw [hrun]
    by_cases ht : (σ' out).head? = some true
    · left; simp [ht, hacc]
    · right; left; simp [ht, hrej]
  · rcases Nat.lt_or_ge u (T + 1) with hlt | hge
    · rw [Prog.run_eq_iterate]; exact hsp u (by omega)
    · rw [show u = T + 1 by omega, hrun]; exact hσ'
  · rw [hrun]
    by_cases ht : (σ' out).head? = some true
    · simp [ht, hacc, Prog.Accepting]
    · simp [ht, hrej, Prog.Accepting]

/-! #### Inlining keeps the step count -/

/-- **Inlining, with step counts.**  Running the renamed statement takes as many steps as `s`. -/
theorem ExecT.rename {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f) {s : Stmt k}
    {σ σ' : Stacks k} {S T : ℕ} (h : ExecT s σ σ' S T) (τ : Stacks k') :
    ExecT (s.rename f) (Function.extend f σ τ) (Function.extend f σ' τ)
      (S + Stacks.rest f τ) T := by
  induction h with
  | skip hS => exact .skip (by rw [Stacks.space_extend hf]; omega)
  | @push r b σ S hS =>
    have := ExecT.push (r := f r) (b := b) (σ := Function.extend f σ τ)
      (S := S + Stacks.rest f τ) (by rw [Stacks.space_extend hf]; omega)
    rwa [hf.extend_apply, Stacks.update_extend hf] at this
  | @pop r σ S hS =>
    have := ExecT.pop (r := f r) (σ := Function.extend f σ τ)
      (S := S + Stacks.rest f τ) (by rw [Stacks.space_extend hf]; omega)
    rwa [hf.extend_apply, Stacks.update_extend hf] at this
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc _ ih => exact .iteT (by rw [hf.extend_apply]; exact hc) ih
  | iteF hc _ ih => exact .iteF (by rw [hf.extend_apply]; exact hc) ih
  | loopT hc _ _ ih₁ ih₂ => exact .loopT (by rw [hf.extend_apply]; exact hc) ih₁ ih₂
  | loopF hc hS =>
    exact .loopF (by rw [hf.extend_apply]; exact hc) (by rw [Stacks.space_extend hf]; omega)

/-- Renaming `s` along an injective map preserves its step count and leaves the other stacks
unchanged, adding their space to the bound. -/
theorem ExecT.rename_of_comp {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f)
    {s : Stmt k} {σ' : Stacks k} {S T : ℕ} {τ : Stacks k'}
    (h : ExecT s (fun r => τ (f r)) σ' S T) :
    ExecT (s.rename f) τ (Function.extend f σ' τ) (S + Stacks.rest f τ) T := by
  have := h.rename hf τ
  rwa [Stacks.extend_comp_self hf τ] at this

/-! #### Executions within a step budget -/

/-- `s` executes from `σ` to `σ'` within space `S` in at most `T` steps. -/
def ExecLe {k : ℕ} (s : Stmt k) (σ σ' : Stacks k) (S T : ℕ) : Prop :=
  ∃ T' ≤ T, ExecT s σ σ' S T'

namespace ExecLe

variable {k : ℕ}

/-- An execution taking exactly `T` steps satisfies the step budget `T`. -/
theorem of_execT {s : Stmt k} {σ σ' : Stacks k} {S T : ℕ} (h : ExecT s σ σ' S T) :
    ExecLe s σ σ' S T := ⟨T, le_rfl, h⟩

/-- An execution within a step budget is an `Exec` execution with the same space bound. -/
theorem toExec {s : Stmt k} {σ σ' : Stacks k} {S T : ℕ} (h : ExecLe s σ σ' S T) :
    Exec s σ σ' S := by
  obtain ⟨_, _, h⟩ := h; exact h.toExec

/-- A larger step budget is allowed. -/
theorem mono_time {s : Stmt k} {σ σ' : Stacks k} {S T T' : ℕ} (h : ExecLe s σ σ' S T)
    (hT : T ≤ T') : ExecLe s σ σ' S T' := by
  obtain ⟨T₀, h₀, h⟩ := h; exact ⟨T₀, h₀.trans hT, h⟩

/-- A larger space bound is allowed. -/
theorem mono {s : Stmt k} {σ σ' : Stacks k} {S S' T : ℕ} (h : ExecLe s σ σ' S T) (hS : S ≤ S') :
    ExecLe s σ σ' S' T := by
  obtain ⟨T₀, h₀, h⟩ := h; exact ⟨T₀, h₀, h.mono hS⟩

/-- `skip` preserves the stacks within any step budget when they fit within space `S`. -/
theorem skip {σ : Stacks k} {S T : ℕ} (h : σ.space ≤ S) : ExecLe .skip σ σ S T :=
  ⟨0, Nat.zero_le _, .skip h⟩

/-- Pushing `b` onto stack `r` takes one step and requires one extra unit of space. -/
theorem push {r : Fin k} {b : Bool} {σ : Stacks k} {S T : ℕ} (h : σ.space + 1 ≤ S) (hT : 1 ≤ T) :
    ExecLe (.push r b) σ (Function.update σ r (b :: σ r)) S T := ⟨1, hT, .push h⟩

/-- Popping stack `r` takes one step without increasing the space bound. -/
theorem pop {r : Fin k} {σ : Stacks k} {S T : ℕ} (h : σ.space ≤ S) (hT : 1 ≤ T) :
    ExecLe (.pop r) σ (Function.update σ r (σ r).tail) S T := ⟨1, hT, .pop h⟩

/-- Sequential composition adds the step budgets of its two executions within space `S`. -/
theorem seq {s₁ s₂ : Stmt k} {σ σ₁ σ₂ : Stacks k} {S T₁ T₂ : ℕ} (h₁ : ExecLe s₁ σ σ₁ S T₁)
    (h₂ : ExecLe s₂ σ₁ σ₂ S T₂) : ExecLe (.seq s₁ s₂) σ σ₂ S (T₁ + T₂) := by
  obtain ⟨U₁, hU₁, h₁⟩ := h₁
  obtain ⟨U₂, hU₂, h₂⟩ := h₂
  exact ⟨U₁ + U₂, by omega, .seq h₁ h₂⟩

/-- A true conditional executes `s₁` within its step budget plus two control steps. -/
theorem iteT {r : Fin k} {cond : Option Bool → Bool} {s₁ s₂ : Stmt k} {σ σ' : Stacks k}
    {S T : ℕ} (hc : cond (σ r).head? = true) (h : ExecLe s₁ σ σ' S T) :
    ExecLe (.ite r cond s₁ s₂) σ σ' S (T + 2) := by
  obtain ⟨U, hU, h⟩ := h
  exact ⟨U + 2, by omega, .iteT hc h⟩

/-- A false conditional executes `s₂` within the uniform conditional budget `T + 2`. -/
theorem iteF {r : Fin k} {cond : Option Bool → Bool} {s₁ s₂ : Stmt k} {σ σ' : Stacks k}
    {S T : ℕ} (hc : cond (σ r).head? = false) (h : ExecLe s₂ σ σ' S T) :
    ExecLe (.ite r cond s₁ s₂) σ σ' S (T + 2) := by
  obtain ⟨U, hU, h⟩ := h
  exact ⟨U + 1, by omega, .iteF hc h⟩

/-- A loop iteration adds the body and remaining loop budgets, plus two control steps. -/
theorem loopT {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k} {σ σ₁ σ₂ : Stacks k}
    {S T₁ T₂ : ℕ} (hc : cond (σ r).head? = true) (h₁ : ExecLe body σ σ₁ S T₁)
    (h₂ : ExecLe (.loop r cond body) σ₁ σ₂ S T₂) :
    ExecLe (.loop r cond body) σ σ₂ S (T₁ + T₂ + 2) := by
  obtain ⟨U₁, hU₁, h₁⟩ := h₁
  obtain ⟨U₂, hU₂, h₂⟩ := h₂
  exact ⟨U₁ + U₂ + 2, by omega, .loopT hc h₁ h₂⟩

/-- A loop with a false condition exits in one step, preserving stacks within space `S`. -/
theorem loopF {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k} {σ : Stacks k} {S T : ℕ}
    (hc : cond (σ r).head? = false) (h : σ.space ≤ S) (hT : 1 ≤ T) :
    ExecLe (.loop r cond body) σ σ S T := ⟨1, hT, .loopF hc h⟩

/-- Inlining keeps the step budget. -/
theorem rename_of_comp {k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f) {s : Stmt k}
    {σ' : Stacks k} {S T : ℕ} {τ : Stacks k'} (h : ExecLe s (fun r => τ (f r)) σ' S T) :
    ExecLe (s.rename f) τ (Function.extend f σ' τ) (S + Stacks.rest f τ) T := by
  obtain ⟨U, hU, h⟩ := h
  exact ⟨U, hU, h.rename_of_comp hf⟩

/-- **Loop rule with an invariant, a variant and a step budget**: if every iteration started in
an invariant state where the condition holds takes at most `τ` steps (within `S`) and ends in an
invariant state with a smaller variant, then from every invariant state `σ` the loop terminates
within `μ σ * (τ + 2) + 1` steps in an invariant state where the condition fails. -/
theorem loop_of_variant {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k}
    (I : Stacks k → Prop) (μ : Stacks k → ℕ) (S τ : ℕ)
    (hstep : ∀ σ, I σ → cond (σ r).head? = true →
      ∃ σ', ExecLe body σ σ' S τ ∧ I σ' ∧ μ σ' < μ σ)
    (hexit : ∀ σ, I σ → σ.space ≤ S) :
    ∀ σ, I σ → ∃ σ', ExecLe (.loop r cond body) σ σ' S (μ σ * (τ + 2) + 1) ∧ I σ' ∧
      cond (σ' r).head? = false := by
  suffices H : ∀ n σ, μ σ ≤ n → I σ →
      ∃ σ', ExecLe (.loop r cond body) σ σ' S (μ σ * (τ + 2) + 1) ∧ I σ' ∧
        cond (σ' r).head? = false from
    fun σ hσ => H _ σ le_rfl hσ
  intro n
  induction n with
  | zero =>
    intro σ hμ hσ
    cases hc : cond (σ r).head?
    · exact ⟨σ, loopF hc (hexit σ hσ) (by omega), hσ, hc⟩
    · obtain ⟨σ₁, -, -, hlt⟩ := hstep σ hσ hc
      omega
  | succ n ih =>
    intro σ hμ hσ
    cases hc : cond (σ r).head?
    · exact ⟨σ, loopF hc (hexit σ hσ) (by omega), hσ, hc⟩
    · obtain ⟨σ₁, hb, hI, hlt⟩ := hstep σ hσ hc
      obtain ⟨σ₂, hl, hI₂, hc₂⟩ := ih σ₁ (by omega) hI
      refine ⟨σ₂, (loopT hc hb hl).mono_time ?_, hI₂, hc₂⟩
      have h1 : (μ σ₁ + 1) * (τ + 2) ≤ μ σ * (τ + 2) := Nat.mul_le_mul (by omega) le_rfl
      have h2 : (μ σ₁ + 1) * (τ + 2) = μ σ₁ * (τ + 2) + (τ + 2) := by ring
      omega

end ExecLe

/-! #### Step counts of basic routines -/

namespace Stmt

variable {k : ℕ}

/-- `clear r` empties `r` in `3 |l| + 1` steps. -/
theorem execT_clear (r : Fin k) : ∀ (l : BitString) (σ : Stacks k), σ r = l →
    ExecT (clear r) σ (Function.update σ r []) σ.space (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro σ hσ
    have e : Function.update σ r [] = σ := by rw [← hσ, Function.update_eq_self]
    rw [e]
    exact (ExecT.loopF (by simp [hσ]) le_rfl).cast (by simp)
  | cons b l ih =>
    intro σ hσ
    have h1 : ExecT (.pop r) σ (Function.update σ r l) σ.space 1 := by
      have := ExecT.pop (r := r) (σ := σ) (S := σ.space) le_rfl
      rwa [hσ] at this
    have h2 := ih (Function.update σ r l) (by simp)
    rw [Function.update_idem] at h2
    exact (ExecT.loopT (by simp [hσ]) h1
      (h2.mono (by have := space_update_of_cons hσ; omega))).cast
      (by simp only [List.length_cons]; ring)

/-- `moveBit r r'` moves the top bit of `r` onto `r'` in at most `4` steps. -/
theorem execLe_moveBit {r r' : Fin k} (hrr : r ≠ r') {σ : Stacks k} {b : Bool} {l : BitString}
    (hσ : σ r = b :: l) :
    ExecLe (moveBit r r') σ (Function.update (Function.update σ r l) r' (b :: σ r')) σ.space 4 := by
  have hsp := space_update_of_cons hσ
  have hpop : ExecLe (.pop r) σ (Function.update σ r l) σ.space 1 := by
    have := ExecLe.pop (r := r) (σ := σ) (S := σ.space) (T := 1) le_rfl le_rfl
    rwa [hσ] at this
  have hr' : (Function.update σ r l) r' = σ r' := Function.update_of_ne hrr.symm _ _
  have hpush := ExecLe.push (r := r') (b := b) (σ := Function.update σ r l) (S := σ.space)
    (T := 1) (by omega) le_rfl
  rw [hr'] at hpush
  have hb := ExecLe.seq hpop hpush
  unfold moveBit caseBit
  cases b
  · exact ExecLe.iteF (by simp [hσ, isTrue]) hb
  · exact ExecLe.iteT (by simp [hσ, isTrue]) hb

/-- `moveAll r r'` moves the content of `r`, reversed, on top of `r'` in at most `6 |l| + 1`
steps. -/
theorem execLe_moveAll {r r' : Fin k} (hrr : r ≠ r') : ∀ (l : BitString) (σ : Stacks k), σ r = l →
    ExecLe (moveAll r r') σ
      (Function.update (Function.update σ r []) r' (l.reverse ++ σ r')) σ.space
      (6 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro σ hσ
    have e : Function.update (Function.update σ r []) r' ([].reverse ++ σ r') = σ := by
      funext j
      simp only [Function.update_apply, List.reverse_nil, List.nil_append]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    rw [e]
    exact ExecLe.loopF (by simp [hσ]) le_rfl (by simp)
  | cons b l ih =>
    intro σ hσ
    have h1 := execLe_moveBit hrr hσ
    have h2 := ih (Function.update (Function.update σ r l) r' (b :: σ r'))
      (by rw [Function.update_of_ne hrr, Function.update_self])
    have e : Function.update (Function.update (Function.update (Function.update σ r l) r'
        (b :: σ r')) r []) r' (l.reverse ++ (Function.update (Function.update σ r l) r'
          (b :: σ r')) r') =
        Function.update (Function.update σ r []) r' ((b :: l).reverse ++ σ r') := by
      funext j
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> subst_vars <;> simp_all
    rw [e] at h2
    exact (ExecLe.loopT (by simp [hσ]) h1 (h2.mono h1.toExec.space_le.2)).mono_time
      (by simp only [List.length_cons]; omega)

/-- `pushList r l` pushes the hardwired string `l` in `|l|` steps. -/
theorem execT_pushList (r : Fin k) : ∀ (l : BitString) (σ : Stacks k),
    ExecT (pushList r l) σ (Function.update σ r (l ++ σ r)) (σ.space + l.length) l.length
  | [], σ => by
    have := ExecT.skip (σ := σ) (S := σ.space + ([] : BitString).length) (by simp)
    rwa [List.nil_append, Function.update_eq_self]
  | b :: l, σ => by
    have h1 := execT_pushList r l σ
    have s1 : Stacks.space (Function.update σ r (l ++ σ r)) = σ.space + l.length := by
      have := σ.space_update r (l ++ σ r)
      simp only [List.length_append] at this
      omega
    have h2 := ExecT.push (r := r) (b := b) (σ := Function.update σ r (l ++ σ r))
      (S := σ.space + (b :: l).length) (by simp only [List.length_cons]; omega)
    rw [Function.update_self, Function.update_idem] at h2
    exact (ExecT.seq (h1.mono (by simp)) h2).cast (by simp)

end Stmt

/-! #### Time bounds from existing `Exec` derivations -/

/-- Statements without loops. -/
def Stmt.LoopFree {k : ℕ} : Stmt k → Prop
  | .skip => True
  | .push _ _ => True
  | .pop _ => True
  | .seq s₁ s₂ => s₁.LoopFree ∧ s₂.LoopFree
  | .ite _ _ s₁ s₂ => s₁.LoopFree ∧ s₂.LoopFree
  | .loop _ _ _ => False

/-- A loop-free statement takes at most `size` steps (every instruction is run at most once). -/
theorem ExecT.le_size {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S T : ℕ} (h : ExecT s σ σ' S T)
    (hs : s.LoopFree) : T ≤ s.size := by
  induction h with
  | skip _ => simp [Stmt.size]
  | push _ => simp [Stmt.size]
  | pop _ => simp [Stmt.size]
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.LoopFree] at hs
    have := ih₁ hs.1; have := ih₂ hs.2
    simp only [Stmt.size]; omega
  | iteT _ _ ih =>
    simp only [Stmt.LoopFree] at hs
    have := ih hs.1
    simp only [Stmt.size]; omega
  | iteF _ _ ih =>
    simp only [Stmt.LoopFree] at hs
    have := ih hs.2
    simp only [Stmt.size]; omega
  | loopT _ _ _ _ _ => simp [Stmt.LoopFree] at hs
  | loopF _ _ => simp [Stmt.LoopFree] at hs

/-- An execution of a loop-free statement takes at most `size` steps. -/
theorem Exec.execLe_of_loopFree {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ}
    (h : Exec s σ σ' S) (hs : s.LoopFree) : ExecLe s σ σ' S s.size := by
  obtain ⟨T, hT⟩ := h.exists_execT
  exact ⟨T, hT.le_size hs, hT⟩

/-- Decreasing the variant from `m` to `m₁` leaves room for a body budget `τ` and two control
steps within the loop budget `m * (τ + 2) + 1`. -/
theorem loop_budget_le {m₁ m τ : ℕ} (h : m₁ < m) :
    τ + (m₁ * (τ + 2) + 1) + 2 ≤ m * (τ + 2) + 1 := by
  have h1 : (m₁ + 1) * (τ + 2) ≤ m * (τ + 2) := Nat.mul_le_mul (by omega) le_rfl
  have h2 : (m₁ + 1) * (τ + 2) = m₁ * (τ + 2) + (τ + 2) := by ring
  omega

/-- **Step budget of a loop from its `Exec` derivation**: if every execution of the body from an
invariant state where the condition holds takes at most `τ` steps, preserves the invariant and
decreases the variant `μ`, then an execution of the loop from an invariant state `σ` takes at most
`μ σ * (τ + 2) + 1` steps.  (The final stacks come from the existing `Exec` specification.) -/
theorem ExecLe.loop_of_exec {k : ℕ} {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k}
    (I : Stacks k → Prop) (μ : Stacks k → ℕ) (S τ : ℕ)
    (hbody : ∀ σ₁ σ₂, I σ₁ → cond (σ₁ r).head? = true → Exec body σ₁ σ₂ S →
      ExecLe body σ₁ σ₂ S τ ∧ I σ₂ ∧ μ σ₂ < μ σ₁) :
    ∀ σ σ', I σ → Exec (.loop r cond body) σ σ' S →
      ExecLe (.loop r cond body) σ σ' S (μ σ * (τ + 2) + 1) := by
  suffices H : ∀ n σ σ', μ σ ≤ n → I σ → Exec (.loop r cond body) σ σ' S →
      ExecLe (.loop r cond body) σ σ' S (μ σ * (τ + 2) + 1) from
    fun σ σ' hI h => H _ σ σ' le_rfl hI h
  intro n
  induction n with
  | zero =>
    intro σ σ' hμ hI h
    cases h with
    | loopT hc hb _ => obtain ⟨-, -, hlt⟩ := hbody _ _ hI hc hb; omega
    | loopF hc hS => exact ExecLe.loopF hc hS (by omega)
  | succ n ih =>
    intro σ σ' hμ hI h
    cases h with
    | loopT hc hb hl =>
      obtain ⟨hbT, hI₁, hlt⟩ := hbody _ _ hI hc hb
      exact (ExecLe.loopT hc hbT (ih _ _ (by omega) hI₁ hl)).mono_time (loop_budget_le hlt)
    | loopF hc hS => exact ExecLe.loopF hc hS (by omega)

namespace Stmt

variable {k : ℕ}

/-- The bit-duplication step `dupStep t r r'` contains no loops. -/
theorem loopFree_dupStep (t r r' : Fin k) : (dupStep t r r').LoopFree := by
  simp [dupStep, caseBit, seqs, Stmt.LoopFree]

/-- The compiled bit-duplication step `dupStep t r r'` has eight instructions. -/
theorem size_dupStep (t r r' : Fin k) : (dupStep t r r').size = 8 := rfl

/-- `copy r r' t` takes at most `16 |r| + 2` steps. -/
theorem execLe_copy {r r' t : Fin k} (hrr : r ≠ r') (hrt : r ≠ t) (hr't : r' ≠ t)
    {σ : Stacks k} (ht : σ t = []) :
    ExecLe (copy r r' t) σ (Function.update σ r' (σ r ++ σ r')) (σ.space + (σ r).length)
      (16 * (σ r).length + 2) := by
  have hex := exec_copy hrr hrt hr't ht
  unfold copy at hex ⊢
  rw [Exec.seq_iff] at hex
  obtain ⟨σ₁, h₁, h₂⟩ := hex
  have hm := execLe_moveAll hrt (σ r) σ rfl
  have e₁ := Exec.det h₁ hm.toExec
  subst e₁
  have hloop := ExecLe.loop_of_exec (r := t) (cond := Option.isSome) (body := dupStep t r r')
    (fun _ => True) (fun σ => (σ t).length) _ 8
    (fun σ₁ σ₂ _ hc hb => by
      obtain ⟨b, l, hσ₁⟩ : ∃ b l, σ₁ t = b :: l := by
        cases h : σ₁ t with
        | nil => rw [h] at hc; simp at hc
        | cons b l => exact ⟨b, l, rfl⟩
      refine ⟨(hb.execLe_of_loopFree (loopFree_dupStep t r r')).mono_time
        (size_dupStep t r r').le, trivial, ?_⟩
      have e := Exec.det hb (exec_dupStep hrt.symm hr't.symm hrr hσ₁)
      subst e
      simp [hrt.symm, hr't.symm, hσ₁])
    _ _ trivial h₂
  have hlen : ((Function.update (Function.update σ r []) t ((σ r).reverse ++ σ t)) t).length =
      (σ r).length := by simp [ht]
  rw [hlen] at hloop
  exact (ExecLe.seq (hm.mono (Nat.le_add_right _ _)) hloop).mono_time (by omega)

end Stmt

/-! #### More structural lemmas with step counts -/

namespace ExecT

variable {k : ℕ}

/-- A conditional takes the steps of the chosen branch, plus `2` (then: test and jump) or `1`
(else: test). -/
theorem ite_iff {r : Fin k} {cond : Option Bool → Bool} {s₁ s₂ : Stmt k} {σ σ' : Stacks k}
    {S T : ℕ} : ExecT (.ite r cond s₁ s₂) σ σ' S T ↔
      if cond (σ r).head? then ∃ T₁, ExecT s₁ σ σ' S T₁ ∧ T = T₁ + 2
      else ∃ T₂, ExecT s₂ σ σ' S T₂ ∧ T = T₂ + 1 := by
  constructor
  · intro h
    cases h with
    | iteT hc h => rw [ite_eq_left hc]; exact ⟨_, h, rfl⟩
    | iteF hc h => rw [ite_eq_right (by simp [hc])]; exact ⟨_, h, rfl⟩
  · intro h
    by_cases hc : cond (σ r).head? = true
    · rw [ite_eq_left hc] at h
      obtain ⟨T₁, h, rfl⟩ := h
      exact .iteT hc h
    · rw [ite_eq_right hc] at h
      obtain ⟨T₂, h, rfl⟩ := h
      exact .iteF (by simpa using hc) h

/-- One unfolding of a loop, with step counts: an iteration costs the body plus `2` (test and jump
back), the exit `1` (test). -/
theorem loop_iff {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k} {σ σ' : Stacks k}
    {S T : ℕ} : ExecT (.loop r cond body) σ σ' S T ↔
      if cond (σ r).head? then ∃ σ₁ T₁ T₂, ExecT body σ σ₁ S T₁ ∧
          ExecT (.loop r cond body) σ₁ σ' S T₂ ∧ T = T₁ + T₂ + 2
      else σ' = σ ∧ σ.space ≤ S ∧ T = 1 := by
  constructor
  · intro h
    cases h with
    | loopT hc hb hl => rw [ite_eq_left hc]; exact ⟨_, _, _, hb, hl, rfl⟩
    | loopF hc hS => rw [ite_eq_right (by simp [hc])]; exact ⟨rfl, hS, rfl⟩
  · intro h
    by_cases hc : cond (σ r).head? = true
    · rw [ite_eq_left hc] at h
      obtain ⟨σ₁, T₁, T₂, hb, hl, rfl⟩ := h
      exact .loopT hc hb hl
    · rw [ite_eq_right hc] at h
      obtain ⟨rfl, hS, rfl⟩ := h
      exact .loopF (by simpa using hc) hS

/-- The step count does not depend on the space bound: a counted run and a run within another
space bound give a counted run within that bound. -/
theorem of_exec {s : Stmt k} {σ σ' : Stacks k} {S S' T : ℕ} (h : ExecT s σ σ' S T)
    (h' : Exec s σ σ' S') : ExecT s σ σ' S' T := by
  obtain ⟨T', hT'⟩ := h'.exists_execT
  obtain ⟨-, rfl⟩ := hT'.det h
  exact hT'

end ExecT

/-- A step budget can be moved to any other space bound within which the statement runs. -/
theorem ExecLe.of_exec {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S S' T : ℕ}
    (h : ExecLe s σ σ' S T) (h' : Exec s σ σ' S') : ExecLe s σ σ' S' T := by
  obtain ⟨U, hU, h⟩ := h
  exact ⟨U, hU, h.of_exec h'⟩

/-- Rewriting the final stacks of a budgeted run along an equality. -/
theorem ExecLe.of_eq {k : ℕ} {s : Stmt k} {σ σ₁ σ₂ : Stacks k} {S T : ℕ} (h : ExecLe s σ σ₁ S T)
    (e : σ₁ = σ₂) : ExecLe s σ σ₂ S T := e ▸ h

/-- `Prog.ReachesN` is `Prog.ReachesIn`: `c` reaches `c'` in exactly `n` steps, all
configurations on the way having space `≤ S`. -/
abbrev Prog.ReachesN (P : Prog) (c c' : PConfig P) (S n : ℕ) : Prop := P.ReachesIn c c' S n

/-- A counted run is a run. -/
theorem Prog.ReachesIn.reaches {P : Prog} {c c' : PConfig P} {S n : ℕ}
    (h : P.ReachesIn c c' S n) : P.Reaches c c' S := ⟨n, h.1, h.2⟩

/-- **Correctness of the compiler, with step counts** (`ExecT.reachesIn`, stated with
`Prog.ReachesN`). -/
theorem ExecT.reaches {P : Prog} {s : Stmt P.k} {σ σ' : Stacks P.k} {S T : ℕ}
    (h : ExecT s σ σ' S T) (a : ℕ) (hc : P.CodeAt a (s.compile a)) :
    P.ReachesN ⟨a, σ⟩ ⟨a + s.size, σ'⟩ S T := h.reachesIn a hc

/-- `Stmt.toProg_spec_time` in the shape of `Stmt.toProg_spec`: the program halts at some time
`t ≤ T + 1` (in fact at `T + 1`). -/
theorem Stmt.toProg_spec_le_time {k : ℕ} (s : Stmt k) (out : Fin k) (x : BitString) (σ' : Stacks k)
    (S T : ℕ) (h : ExecT s (Stacks.input k x) σ' S T) :
    ∃ t ≤ T + 1, (s.toProg out).Halted ((s.toProg out).run x t) ∧
      (∀ u ≤ t, ((s.toProg out).run x u).space ≤ S) ∧
      ((s.toProg out).Accepting ((s.toProg out).run x t) ↔ (σ' out).head? = some true) := by
  obtain ⟨h1, h2, h3⟩ := s.toProg_spec_time out x σ' S T h
  exact ⟨T + 1, le_rfl, h1, h2, h3⟩

/-- A statement deciding `Φ` within fewer than `2 ^ p(|x|)` steps and space `2 ^ p(|x|)` gives a
stack program halting on every input within `2 ^ p(|x|)` steps and space `2 ^ p(|x|)` and
accepting exactly `Φ`. -/
theorem Stmt.exists_prog_time {k : ℕ} (s : Stmt k) (out : Fin k) (p : Polynomial ℕ)
    (Φ : BitString → Prop)
    (h : ∀ x : BitString, ∃ σ' T, ExecT s (Stacks.input k x) σ' (2 ^ p.eval x.length) T ∧
      T < 2 ^ p.eval x.length ∧ ((σ' out).head? = some true ↔ Φ x)) :
    ∃ P : Prog, (∀ x : BitString, ∃ t ≤ 2 ^ p.eval x.length, P.Halted (P.run x t) ∧
        ∀ u ≤ t, (P.run x u).space ≤ 2 ^ p.eval x.length) ∧ ∀ x : BitString, x ∈ P.Lang ↔ Φ x := by
  refine ⟨s.toProg out, fun x => ?_, fun x => ?_⟩
  · obtain ⟨σ', T, hσ', hT, -⟩ := h x
    obtain ⟨ht, hsp, -⟩ := s.toProg_spec_time out x σ' _ T hσ'
    exact ⟨T + 1, hT, ht, hsp⟩
  · obtain ⟨σ', T, hσ', -, hΦ⟩ := h x
    obtain ⟨ht, -, hacc⟩ := s.toProg_spec_time out x σ' _ T hσ'
    rw [Prog.mem_lang_iff_of_halted _ x _ ht, hacc, hΦ]

/-- A statement deciding `Φ` within a step budget of `2 ^ p(|x|) - 1` and space `2 ^ p(|x|)`
gives a stack program deciding `Φ` within `2 ^ p(|x|)` steps and space `2 ^ p(|x|)`. -/
theorem Stmt.exists_prog_time_of_execLe {k : ℕ} (s : Stmt k) (out : Fin k) (p : Polynomial ℕ)
    (Φ : BitString → Prop)
    (h : ∀ x : BitString, ∃ σ', ExecLe s (Stacks.input k x) σ' (2 ^ p.eval x.length)
      (2 ^ p.eval x.length - 1) ∧ ((σ' out).head? = some true ↔ Φ x)) :
    ∃ P : Prog, (∀ x : BitString, ∃ t ≤ 2 ^ p.eval x.length, P.Halted (P.run x t) ∧
        ∀ u ≤ t, (P.run x u).space ≤ 2 ^ p.eval x.length) ∧ ∀ x : BitString, x ∈ P.Lang ↔ Φ x := by
  refine s.exists_prog_time out p Φ fun x => ?_
  obtain ⟨σ', ⟨T, hT, hσ'⟩, hΦ⟩ := h x
  have := Nat.one_le_two_pow (n := p.eval x.length)
  exact ⟨σ', T, hσ', by omega, hΦ⟩

end Kolmogorov.RandomStrings
