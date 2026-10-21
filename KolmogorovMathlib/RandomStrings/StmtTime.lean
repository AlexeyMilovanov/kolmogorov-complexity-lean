/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.StmtTime.ExecT
import KolmogorovMathlib.RandomStrings.StmtTime.Budgets

/-!
# Step counts for structured stack programs

`ExecT s σ σ' S T` refines the big-step semantics `Exec s σ σ' S` (Expspace.lean) by the exact
number `T` of steps that the compiled code `s.compile a` takes (`ExecT.reachesIn`): `push`/`pop`
take one step, a conditional one test plus (for the `then` branch) one jump, every loop iteration
one test and one jump back, and the exit from a loop one test.  Exact costs per construct:
`skip` 0, `push` 1, `pop` 1, `seq` `T₁ + T₂`, `ite` (taken) `T + 2`, `ite` (not taken) `T + 1`,
loop iteration `T_body + T_rest + 2`, loop exit 1.

Main facts:
* `ExecT.toExec`, `Exec.exists_execT`: `ExecT` is `Exec` with a step count;
* `ExecT.det`: the final stacks and the step count are determined; `ExecT.mono`,
  `Exec.space_le` via `ExecT.toExec`, `ExecT.seq_iff`, `ExecT.ite_iff`, `ExecT.loop_iff`;
* `Prog.ReachesIn` (runs of exactly `n` steps; `Prog.ReachesN` is a synonym) and
  `ExecT.reachesIn` (= `ExecT.reaches`): correctness of the compiler with step counts;
  `Stmt.toProg_spec_time`: `s.toProg out` halts at time `T + 1`;
* `ExecT.rename`: inlining along an injective renaming keeps the step count;
* `ExecLe` (at most `T` steps) and `ExecLe.loop_of_variant`, `ExecLe.loop_of_exec`: a loop whose
  iterations take `≤ τ` steps and decrease a variant `μ` takes `≤ μ σ * (τ + 2) + 1` steps;
* **generic budgets** `Exec.execLe_budget`: every statement all of whose loops are *pop-loops*
  (`Stmt.PopLoops`: the loop exits on an empty test stack, and its body never pushes on that stack
  and pops it on every path) runs within `s.budget S` steps, a polynomial in the space bound `S`
  computed from the syntax (a pop-loop iterates at most `|σ r| ≤ S` times);
  `Exec.execLe_loop_budget` (a top-level pop-loop iterates at most `|σ r|` times);
  `Exec.execLe_budget_on` (only the stacks the statement writes count);
  `Exec.execLe_size_mul_pow` (`budget ≤ size * (S + 1) ^ loopDepth`); invariance under renaming;
* step counts of the routines of Expspace.lean: `clear`, `moveBit`, `moveAll`, `pushList`, `copy`,
  `addInto`, `cmpInto`, `incr`, `clearFlag`, `setFlag`, `eqTest`, `decodeOne`, `memTest`, in the
  lengths of their own stacks;
* the clocked simulation `SimOTM.simStmt`, the recording simulation `SimOTM.recSimStmt` and the
  components `QEnum.zeroStmt`/`selStmt`/`mergeStmt` of the query enumeration are pop-loop
  statements: polynomial step bounds `exists_simStmt_time`, `QEnum.exists_recSimStmt_time`, … .

The development lives in `StmtTime.ExecT` (the step-count framework) and `StmtTime.Budgets`
(generic pop-loop budgets); this module proves that the clocked simulation and the components of
the query enumeration run in polynomial time.
-/

namespace Kolmogorov.RandomStrings

/-! #### The simulation of the clocked machine runs in polynomial time

`SimOTM.simStmt c e` (deciding the clocked acceptance of `c` with the oracle coded on stack `1`)
and the recording simulation `SimOTM.recSimStmt c e` are built from pop-loops (the main loop counts
the clock down on stack `7`), so their `Exec` specifications come with the step bound
`size * (S + 1) ^ loopDepth`, a polynomial in `|x| + clock e |x| + |encList L|` whose coefficient
and degree depend only on `(c, e)`. -/

namespace Stmt

variable {k k' : ℕ}

/-- `pushList r l` is a pop-loop statement: it is a sequence of pushes and has no loop. -/
theorem popLoops_pushList (r : Fin k) : ∀ l : BitString, (pushList r l).PopLoops
  | [] => trivial
  | _ :: l => ⟨popLoops_pushList r l, trivial⟩

/-- `pushList r l` never pushes on a stack `j` different from `r`. -/
theorem noPush_pushList {r j : Fin k} (h : r ≠ j) : ∀ l : BitString, (pushList r l).NoPush j
  | [] => trivial
  | _ :: l => ⟨noPush_pushList h l, h⟩

/-- A renamed statement never pushes on a stack outside the range of the renaming. -/
theorem noPush_rename_of_not_mem {f : Fin k → Fin k'} {j : Fin k'} (hj : ∀ r, f r ≠ j) :
    ∀ s : Stmt k, (s.rename f).NoPush j
  | .skip => trivial
  | .push r _ => hj r
  | .pop _ => trivial
  | .seq s₁ s₂ => ⟨noPush_rename_of_not_mem hj s₁, noPush_rename_of_not_mem hj s₂⟩
  | .ite _ _ s₁ s₂ => ⟨noPush_rename_of_not_mem hj s₁, noPush_rename_of_not_mem hj s₂⟩
  | .loop _ _ b => noPush_rename_of_not_mem hj b

end Stmt

namespace SimOTM

/-- A switch on stack `r` is a pop-loop statement if all its branches are. -/
theorem popLoops_switchU {k : ℕ} (r : Fin k) :
    ∀ l : List (Stmt k), (∀ s ∈ l, s.PopLoops) → (switchU r l).PopLoops
  | [], _ => trivial
  | s :: l, h => ⟨⟨trivial, popLoops_switchU r l fun t ht => h t (by simp [ht])⟩, h s (by simp)⟩

/-- A switch on stack `r` does not push to stack `j` if none of its branches do. -/
theorem noPush_switchU {k : ℕ} (r j : Fin k) :
    ∀ l : List (Stmt k), (∀ s ∈ l, s.NoPush j) → (switchU r l).NoPush j
  | [], _ => trivial
  | s :: l, h => ⟨⟨trivial, noPush_switchU r j l fun t ht => h t (by simp [ht])⟩, h s (by simp)⟩

/-- `readCell r f` is a pop-loop statement if `f a` is one for every cell `a`. -/
theorem popLoops_readCell (r : Fin 21) (f : Sym → Stmt 21) (h : ∀ a, (f a).PopLoops) :
    (readCell r f).PopLoops := by
  simp [readCell, Stmt.caseBit, Stmt.PopLoops, h]

/-- `readCell r f` never pushes on the clock stack `j` if `f a` does not for every cell `a`. -/
theorem noPush_readCell (r j : Fin 21) (f : Sym → Stmt 21) (h : ∀ a, (f a).NoPush j) :
    (readCell r f).NoPush j := by
  simp [readCell, Stmt.caseBit, Stmt.NoPush, h]

/-- The membership test `Stmt.memTest`, renamed onto the stacks of the simulation by `memMap`,
is a pop-loop statement. -/
theorem popLoops_memSim : (Stmt.memTest.rename memMap).PopLoops :=
  Stmt.popLoops_rename memMap_injective _ Stmt.popLoops_memTest

/-- The membership test of the simulation (`memMap`) never pushes on the clock stack `7`. -/
theorem noPush_memSim : (Stmt.memTest.rename memMap).NoPush 7 :=
  Stmt.noPush_rename_of_not_mem (by decide) _

/-- `askStmt c qy qn` (look the buffered query up in the oracle code, push the new state)
is a pop-loop statement and never pushes on the clock stack `7`. -/
theorem popLoops_askStmt (c : OTMCode) (qy qn : Fin c.k) :
    (askStmt c qy qn).PopLoops ∧ (askStmt c qy qn).NoPush 7 := by
  have h1 := popLoops_memSim
  have h2 := noPush_memSim
  constructor <;>
  simp [askStmt, Stmt.seqs, Stmt.moveAll, Stmt.moveBit, Stmt.clear, Stmt.caseBit,
    Stmt.PopLoops, Stmt.NoPush, Stmt.Pops, Stmt.popLoops_pushList, Stmt.noPush_pushList, h1, h2]

/-- `pushCode 8 17 16` (push the code of the string on stack `8` onto the record stack `16`,
through the work stack `17`) is a pop-loop statement and never pushes on the clock stack `7`. -/
theorem popLoops_pushCode : (pushCode 8 17 16).PopLoops ∧ (pushCode 8 17 16).NoPush 7 := by
  constructor <;>
  simp [pushCode, pushCodeBody, Stmt.seqs, Stmt.moveAll, Stmt.moveBit, Stmt.caseBit,
    Stmt.PopLoops, Stmt.NoPush, Stmt.Pops]

/-- `askStmtR c qy qn` (as `askStmt`, and record the query on stack `16`)
is a pop-loop statement and never pushes on the clock stack `7`. -/
theorem popLoops_askStmtR (c : OTMCode) (qy qn : Fin c.k) :
    (askStmtR c qy qn).PopLoops ∧ (askStmtR c qy qn).NoPush 7 := by
  have h1 := popLoops_memSim
  have h2 := noPush_memSim
  have h3 := popLoops_pushCode
  constructor <;>
  simp [askStmtR, Stmt.seqs, Stmt.moveAll, Stmt.moveBit, Stmt.clear, Stmt.caseBit,
    Stmt.PopLoops, Stmt.NoPush, Stmt.Pops, Stmt.popLoops_pushList, Stmt.noPush_pushList, h1, h2,
    h3.1, h3.2]

/-- `actStmt c q a` (the action of state `q` on the scanned cell `a`) is a pop-loop statement and
never pushes on the clock stack `7`. -/
theorem popLoops_actStmt (c : OTMCode) (q : Fin c.k) (a : Sym) :
    (actStmt c q a).PopLoops ∧ (actStmt c q a).NoPush 7 := by
  have h := popLoops_askStmt c
  have hr := popLoops_readCell 4 (pushCell 3) fun a => Stmt.popLoops_pushList _ _
  have hr' := noPush_readCell 4 7 (pushCell 3) fun a => Stmt.noPush_pushList (by decide) _
  unfold actStmt
  split_ifs
  · constructor <;> simp [pushCell, Stmt.PopLoops, Stmt.NoPush, Stmt.popLoops_pushList,
      Stmt.noPush_pushList]
  · split <;> constructor <;> simp [pushCell, Stmt.PopLoops, Stmt.NoPush,
      Stmt.popLoops_pushList, Stmt.noPush_pushList, h, hr, hr']

/-- `actStmtR c q a` (the action of state `q` on the scanned cell `a`, recording the output)
is a pop-loop statement and never pushes on the clock stack `7`. -/
theorem popLoops_actStmtR (c : OTMCode) (q : Fin c.k) (a : Sym) :
    (actStmtR c q a).PopLoops ∧ (actStmtR c q a).NoPush 7 := by
  have h := popLoops_askStmtR c
  have hr := popLoops_readCell 4 (pushCell 3) fun a => Stmt.popLoops_pushList _ _
  have hr' := noPush_readCell 4 7 (pushCell 3) fun a => Stmt.noPush_pushList (by decide) _
  unfold actStmtR
  split_ifs
  · constructor <;> simp [pushCell, Stmt.PopLoops, Stmt.NoPush, Stmt.popLoops_pushList,
      Stmt.noPush_pushList]
  · split <;> constructor <;> simp [pushCell, Stmt.PopLoops, Stmt.NoPush,
      Stmt.popLoops_pushList, Stmt.noPush_pushList, h, hr, hr']

/-- `stepStmt c` (one step of the machine `c`) is a pop-loop statement and never pushes on
the clock stack `7`. -/
theorem popLoops_stepStmt (c : OTMCode) :
    (stepStmt c).PopLoops ∧ (stepStmt c).NoPush 7 := by
  refine ⟨popLoops_switchU 5 _ fun s hs => ?_, noPush_switchU 5 7 _ fun s hs => ?_⟩ <;>
  · simp only [List.mem_ofFn] at hs
    obtain ⟨q, rfl⟩ := hs
    first
    | exact popLoops_readCell 3 _ fun a => (popLoops_actStmt c q a).1
    | exact noPush_readCell 3 7 _ fun a => (popLoops_actStmt c q a).2

/-- `stepStmtR c` (one step of the machine `c`, with recording) is a pop-loop statement and
never pushes on the clock stack `7`. -/
theorem popLoops_stepStmtR (c : OTMCode) :
    (stepStmtR c).PopLoops ∧ (stepStmtR c).NoPush 7 := by
  refine ⟨popLoops_switchU 5 _ fun s hs => ?_, noPush_switchU 5 7 _ fun s hs => ?_⟩ <;>
  · simp only [List.mem_ofFn] at hs
    obtain ⟨q, rfl⟩ := hs
    first
    | exact popLoops_readCell 3 _ fun a => (popLoops_actStmtR c q a).1
    | exact noPush_readCell 3 7 _ fun a => (popLoops_actStmtR c q a).2

/-- `mulStep` (`18 := 18 · 17` in unary) is a pop-loop statement. -/
theorem popLoops_mulStep : mulStep.PopLoops := by
  simp [mulStep, mulLoop, Stmt.copy, Stmt.dupStep, Stmt.seqs, Stmt.moveAll, Stmt.moveBit,
    Stmt.caseBit, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops]

/-- `initStmt e` (load the input, then build the unary clock `|x| ^ e + e` on stack `7`) is a
pop-loop statement. -/
theorem popLoops_initStmt (e : ℕ) : (initStmt e).PopLoops := by
  have hm : (Stmt.seqs (List.replicate e mulStep)).PopLoops :=
    Stmt.popLoops_seqs _ fun s hs => by
      rw [List.eq_of_mem_replicate hs]; exact popLoops_mulStep
  simp [initStmt, loadStmt, loadBody, Stmt.seqs, Stmt.moveAll, Stmt.moveBit, Stmt.clear,
    Stmt.caseBit, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops, Stmt.popLoops_pushList, hm]

/-- `simStmt c e` is a pop-loop statement. -/
theorem popLoops_simStmt (c : OTMCode) (e : ℕ) : (simStmt c e).PopLoops := by
  have h1 := popLoops_initStmt e
  have h2 := popLoops_stepStmt c
  have h3 : (switchU 5 (List.ofFn fun q : Fin c.k => (.push 2 (accB c q) : Stmt 21))).PopLoops :=
    popLoops_switchU 5 _ fun s hs => by
      simp only [List.mem_ofFn] at hs
      obtain ⟨q, rfl⟩ := hs
      trivial
  simp [simStmt, Stmt.seqs, Stmt.clear, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops,
    Stmt.popLoops_pushList, h1, h2.1, h2.2, h3]

/-- `recSimStmt c e` is a pop-loop statement. -/
theorem popLoops_recSimStmt (c : OTMCode) (e : ℕ) : (recSimStmt c e).PopLoops := by
  have h1 := popLoops_initStmt e
  have h2 := popLoops_stepStmtR c
  simp [recSimStmt, Stmt.seqs, Stmt.clear, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops,
    Stmt.popLoops_pushList, h1, h2.1, h2.2]

/-- **The clocked simulation in polynomial time**: `exec_simStmt` with the step bound
`size * (S + 1) ^ loopDepth`. -/
theorem execLe_simStmt (c : OTMCode) (e : ℕ) (x : BitString) (L : List BitString) :
    ExecLe (simStmt c e)
      (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList L))
      (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1
        (Stacks.encList L)) 2
        [accB c (run c.toOTM {z | z ∈ L} x (clock e x.length)).q])
      ((c.k + 10) * (x.length + clock e x.length + (Stacks.encList L).length + 1))
      ((simStmt c e).size *
        ((c.k + 10) * (x.length + clock e x.length + (Stacks.encList L).length + 1) + 1) ^
          (simStmt c e).loopDepth) :=
  (exec_simStmt c e x L).execLe_size_mul_pow (popLoops_simStmt c e)

/-- **The recording simulation in polynomial time**: `exec_recSim` with the step bound
`size * (S + 1) ^ loopDepth`. -/
theorem execLe_recSim (c : OTMCode) (e : ℕ) (x : BitString) (L : List BitString) :
    ExecLe (recSimStmt c e)
      (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList L))
      (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1
        (Stacks.encList L)) 16 (Stacks.encList (recL c.toOTM {z | z ∈ L} x (clock e x.length))))
      ((c.k + 20) * (x.length + clock e x.length + (Stacks.encList L).length + 1) ^ 2)
      ((recSimStmt c e).size *
        ((c.k + 20) * (x.length + clock e x.length + (Stacks.encList L).length + 1) ^ 2 + 1) ^
          (recSimStmt c e).loopDepth) :=
  (exec_recSim c e x L).execLe_size_mul_pow (popLoops_recSimStmt c e)

end SimOTM

/-- `exists_simStmt` with a polynomial step bound: the simulation statement runs within space
`C * N` and within `T * N ^ d` steps, `N = |x| + clock e |x| + |encList L| + 1`, where `C`, `T`,
`d` depend only on `(c, e)`. -/
theorem exists_simStmt_time (c : OTMCode) (e : ℕ) :
    ∃ (k : ℕ) (s : Stmt k) (inp ora out : Fin k) (C T d : ℕ), inp ≠ ora ∧ inp ≠ out ∧
      ora ≠ out ∧ ∀ (x : BitString) (L : List BitString), ∃ b : Bool,
        (b = true ↔ ClockedAccepts c e {z | z ∈ L} x) ∧
        ExecLe s (Function.update (Function.update (fun _ => []) inp x) ora (Stacks.encList L))
          (Function.update (Function.update (Function.update (fun _ => []) inp x) ora
            (Stacks.encList L)) out [b])
          (C * (x.length + clock e x.length + (Stacks.encList L).length + 1))
          (T * (x.length + clock e x.length + (Stacks.encList L).length + 1) ^ d) := by
  refine ⟨21, SimOTM.simStmt c e, 0, 1, 2, c.k + 10,
    (SimOTM.simStmt c e).size * (c.k + 11) ^ (SimOTM.simStmt c e).loopDepth,
    (SimOTM.simStmt c e).loopDepth, by decide, by decide, by decide,
    fun x L => ⟨_, ?_, (SimOTM.execLe_simStmt c e x L).mono_time ?_⟩⟩
  · rw [clockedAccepts_iff_run]
    exact SimOTM.accB_iff c _
  · have hN : 1 ≤ x.length + clock e x.length + (Stacks.encList L).length + 1 := by omega
    generalize x.length + clock e x.length + (Stacks.encList L).length + 1 = N at hN ⊢
    generalize (SimOTM.simStmt c e).loopDepth = d
    generalize (SimOTM.simStmt c e).size = z
    have h1 : (c.k + 10) * N + 1 ≤ (c.k + 11) * N := by nlinarith
    calc z * ((c.k + 10) * N + 1) ^ d ≤ z * ((c.k + 11) * N) ^ d :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
      _ = z * (c.k + 11) ^ d * N ^ d := by rw [mul_pow, Nat.mul_assoc]

/-- `exists_recSimStmt` with a polynomial step bound `T * N ^ d`,
`N = |x| + clock e |x| + |encList L| + 1`. -/
theorem exists_recSimStmt_time (c : OTMCode) (e : ℕ) :
    ∃ (s : Stmt 21) (C T d : ℕ), ∀ (x : BitString) (L : List BitString), ∃ Q : List BitString,
      (∀ z, z ∈ Q ↔ z ∈ queries c.toOTM {z | z ∈ L} x (clock e x.length)) ∧
      ExecLe s (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList L))
        (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1
          (Stacks.encList L)) 16 (Stacks.encList Q))
        (C * (x.length + clock e x.length + (Stacks.encList L).length + 1) ^ 2)
        (T * (x.length + clock e x.length + (Stacks.encList L).length + 1) ^ d) := by
  refine ⟨SimOTM.recSimStmt c e, c.k + 20,
    (SimOTM.recSimStmt c e).size * (c.k + 21) ^ (SimOTM.recSimStmt c e).loopDepth,
    2 * (SimOTM.recSimStmt c e).loopDepth, fun x L =>
    ⟨SimOTM.recL c.toOTM {z | z ∈ L} x (clock e x.length),
      fun z => SimOTM.mem_recL _ _ _ z _, (SimOTM.execLe_recSim c e x L).mono_time ?_⟩⟩
  have hN : 1 ≤ x.length + clock e x.length + (Stacks.encList L).length + 1 := by omega
  generalize x.length + clock e x.length + (Stacks.encList L).length + 1 = N at hN ⊢
  generalize (SimOTM.recSimStmt c e).loopDepth = d
  generalize (SimOTM.recSimStmt c e).size = z
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  have h1 : (c.k + 20) * N ^ 2 + 1 ≤ (c.k + 21) * N ^ 2 := by nlinarith
  calc z * ((c.k + 20) * N ^ 2 + 1) ^ d ≤ z * ((c.k + 21) * N ^ 2) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
    _ = z * (c.k + 21) ^ d * N ^ (2 * d) := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]

/-! #### The components of the query enumeration are pop-loop statements

`QEnum.zeroStmt`, `QEnum.selStmt` and `QEnum.mergeStmt` are built from pop-loops, so every
execution of them (in particular the ones of `exists_zeroStmt`, `exists_selStmt`,
`exists_mergeStmt`) runs within `size * (S + 1) ^ loopDepth` steps (`Exec.execLe_size_mul_pow`).
(The two outer loops of `QEnum.qeStmt`, over the masks and over the rounds, are not pop-loops:
their step counts need the variants of `exec_counterLoop` and `exec_rounds`.) -/

namespace QEnum

/-- `zeroStmt` (the zero mask `replicate |l| false` of the string `l` on stack `0`) is a pop-loop
statement. -/
theorem popLoops_zeroStmt : zeroStmt.PopLoops := by
  simp [zeroStmt, zeroStep, Stmt.seqs, Stmt.moveAll, Stmt.moveBit, Stmt.caseBit, Stmt.PopLoops,
    Stmt.NoPush, Stmt.Pops]

/-- `selStmt` (write the code of `sel v Us`, the strings of `Us` at the `true` positions of the
mask `v`, on stack `2`) is a pop-loop statement. -/
theorem popLoops_selStmt : selStmt.PopLoops := by
  simp [selStmt, selBody, codeDup, Stmt.dupStep, Stmt.seqs, Stmt.clear, Stmt.moveAll,
    Stmt.moveBit, Stmt.caseBit, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops, Stmt.isTrue]

/-- `mergeStmt` (compute `mergeL Lo Q Ln`: merge the strings of the code on stack `0` into the
list on stack `2`, skipping those in `Lo`) is a pop-loop statement. -/
theorem popLoops_mergeStmt : mergeStmt.PopLoops := by
  have hO : (Stmt.memTest.rename memMapO).PopLoops ∧ (Stmt.memTest.rename memMapO).NoPush 0 :=
    ⟨Stmt.popLoops_rename memMapO_injective _ Stmt.popLoops_memTest,
      Stmt.noPush_rename_of_not_mem (by decide) _⟩
  have hN : (Stmt.memTest.rename memMapN).PopLoops ∧ (Stmt.memTest.rename memMapN).NoPush 0 :=
    ⟨Stmt.popLoops_rename memMapN_injective _ Stmt.popLoops_memTest,
      Stmt.noPush_rename_of_not_mem (by decide) _⟩
  have hP : (pushCode (3 : Fin 16) 4 2).PopLoops ∧ (pushCode (3 : Fin 16) 4 2).NoPush 0 := by
    constructor <;> simp [pushCode, pushCodeBody, Stmt.seqs, Stmt.moveAll, Stmt.moveBit,
      Stmt.caseBit, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops]
  simp [mergeStmt, mergeBody, Stmt.decodeOne, Stmt.decodeBody, Stmt.seqs, Stmt.clear,
    Stmt.moveAll, Stmt.moveBit, Stmt.caseBit, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops, Stmt.isTrue,
    hO.1, hO.2, hN.1, hN.2, hP.1, hP.2]

end QEnum

/-- Arithmetic of the polynomial step bounds: `z (K N + 1)^d ≤ z (K + 1)^d N^d` for `N ≥ 1`. -/
theorem mul_add_one_pow_le {z K N d : ℕ} (hN : 1 ≤ N) :
    z * (K * N + 1) ^ d ≤ z * (K + 1) ^ d * N ^ d := by
  have h1 : K * N + 1 ≤ (K + 1) * N := by nlinarith
  calc z * (K * N + 1) ^ d ≤ z * ((K + 1) * N) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
    _ = z * (K + 1) ^ d * N ^ d := by rw [mul_pow, Nat.mul_assoc]

namespace QEnum

/-- The zero mask (the execution of `exists_zeroStmt`, for the named statement). -/
theorem exec_zeroStmt (l : BitString) :
    Exec zeroStmt (Function.update (fun _ => []) 0 l)
      (Function.update (Function.update (fun _ => []) 0 l) 1 (List.replicate l.length false))
      (2 * (l.length + 1)) := by
  have e1 := Stmt.exec_moveAll (by decide : (0 : Fin 3) ≠ 2) l
    (Function.update (fun _ => []) 0 l) (by simp)
  have e2 := exec_zeroLoop (t := (2 : Fin 3)) (r := 0) (r' := 1) l.reverse
    (Function.update (Function.update (Function.update (fun _ => []) 0 l) 0 [])
      2 (l.reverse ++ (Function.update (fun (_ : Fin 3) => ([] : BitString)) 0 l) 2)) (by simp)
  have sp0 : Stacks.space (Function.update (fun (_ : Fin 3) => ([] : BitString)) 0 l) =
      l.length := by
    simp [Stacks.space, Fin.sum_univ_succ, Function.update_apply]
  have sp1 := e1.space_le.2
  rw [sp0] at e1 sp1
  refine Stmt.exec_of_eq (.seq (e1.mono (by nlinarith)) (e2.mono (by
    simp only [List.length_reverse]; nlinarith))) ?_
  funext j
  fin_cases j <;> simp

/-- `exists_zeroStmt` with a polynomial step bound. -/
theorem exists_zeroStmt_time : ∃ (s : Stmt 3) (K T d : ℕ), ∀ l : BitString,
    ExecLe s (Function.update (fun _ => []) 0 l)
      (Function.update (Function.update (fun _ => []) 0 l) 1 (List.replicate l.length false))
      (K * (l.length + 1)) (T * (l.length + 1) ^ d) :=
  ⟨zeroStmt, 2, zeroStmt.size * 3 ^ zeroStmt.loopDepth, zeroStmt.loopDepth, fun l =>
    ((exec_zeroStmt l).execLe_size_mul_pow popLoops_zeroStmt).mono_time
      (mul_add_one_pow_le (by omega))⟩

/-- The selection (the execution of `exists_selStmt`, for the named statement). -/
theorem exec_selStmt (Us : List BitString) (v : BitString) :
    Exec selStmt (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v)
      (Function.update (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v)
        2 (Stacks.encList (sel v Us)))
      (3 * ((Stacks.encList Us).length + v.length + 1)) := by
  set σ0 : Stacks 12 := Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v
    with hσ0
  have sp0 : σ0.space = (Stacks.encList Us).length + v.length := by
    simp [σ0, Stacks.space, Fin.sum_univ_succ, Function.update_apply]
  have e1 := exec_selLoop Us v σ0 (by simp [σ0]) (by simp [σ0]) (by simp [σ0])
  set σ1 : Stacks 12 := Function.update (Function.update (Function.update (Function.update
    (fun _ => []) 1 (v.drop Us.length)) 3 (Stacks.encList Us).reverse) 4
    (v.take Us.length).reverse) 6 (Stacks.encList (sel v Us)).reverse with hσ1
  have e1' := Stmt.exec_of_eq e1 (σ₂ := σ1) (by funext j; fin_cases j <;> simp [σ0, σ1])
  have sp1 := e1'.space_le.2
  have e2 := Stmt.exec_moveAll (r := (3 : Fin 12)) (r' := 0) (by decide) (σ1 3) σ1 rfl
  have sp2 := e2.space_le.2
  have e3 := Stmt.exec_moveAll (r := (4 : Fin 12)) (r' := 1) (by decide) _
    (Function.update (Function.update σ1 3 []) 0 ((σ1 3).reverse ++ σ1 0)) rfl
  have sp3 := e3.space_le.2
  have e4 := Stmt.exec_moveAll (r := (6 : Fin 12)) (r' := 2) (by decide) _
    (Function.update (Function.update (Function.update (Function.update σ1 3 []) 0
      ((σ1 3).reverse ++ σ1 0)) 4 []) 1
      (((Function.update (Function.update σ1 3 []) 0 ((σ1 3).reverse ++ σ1 0)) 4).reverse ++
        (Function.update (Function.update σ1 3 []) 0 ((σ1 3).reverse ++ σ1 0)) 1)) rfl
  have sp4 := e4.space_le.2
  have hb : σ0.space + 2 * (Stacks.encList Us).length ≤
      3 * ((Stacks.encList Us).length + v.length + 1) := by omega
  refine Stmt.exec_of_eq (.seq (e1'.mono hb) (.seq (e2.mono (sp1.trans hb))
    (.seq (e3.mono (sp2.trans (sp1.trans hb))) (.seq (e4.mono (sp3.trans (sp2.trans
      (sp1.trans hb)))) (.skip (sp4.trans (sp3.trans (sp2.trans (sp1.trans hb))))))))) ?_
  clear e1 e1' e2 e3 e4 sp1 sp2 sp3 sp4 hb sp0
  rw [hσ1, hσ0]
  funext j
  fin_cases j <;> simp

/-- `exists_selStmt` with a polynomial step bound. -/
theorem exists_selStmt_time : ∃ (s : Stmt 12) (K T d : ℕ), ∀ (Us : List BitString) (v : BitString),
    ExecLe s (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v)
      (Function.update (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v)
        2 (Stacks.encList (sel v Us)))
      (K * ((Stacks.encList Us).length + v.length + 1))
      (T * ((Stacks.encList Us).length + v.length + 1) ^ d) :=
  ⟨selStmt, 3, selStmt.size * 4 ^ selStmt.loopDepth, selStmt.loopDepth, fun Us v =>
    ((exec_selStmt Us v).execLe_size_mul_pow popLoops_selStmt).mono_time
      (mul_add_one_pow_le (by omega))⟩

/-- `exists_mergeStmt` with a polynomial step bound. -/
theorem exists_mergeStmt_time : ∃ (s : Stmt 16) (K T d : ℕ), ∀ (Q Lo Ln : List BitString),
    ExecLe s (Function.update (Function.update (Function.update (fun _ => [])
        0 (Stacks.encList Q)) 1 (Stacks.encList Lo)) 2 (Stacks.encList Ln))
      (Function.update (Function.update (fun _ => []) 1 (Stacks.encList Lo)) 2
        (Stacks.encList (mergeL Lo Q Ln)))
      (K * ((Stacks.encList Q).length + (Stacks.encList Lo).length +
        (Stacks.encList Ln).length + 1))
      (T * ((Stacks.encList Q).length + (Stacks.encList Lo).length +
        (Stacks.encList Ln).length + 1) ^ d) := by
  refine ⟨mergeStmt, 5, mergeStmt.size * 6 ^ mergeStmt.loopDepth, mergeStmt.loopDepth,
    fun Q Lo Ln => ?_⟩
  have h := exec_mergeLoop Lo Q Ln (S := 5 * ((Stacks.encList Q).length +
    (Stacks.encList Lo).length + (Stacks.encList Ln).length + 1)) (by omega)
  have h' := Stmt.exec_of_eq h (σ₂ := Function.update (Function.update (fun _ => []) 1
    (Stacks.encList Lo)) 2 (Stacks.encList (mergeL Lo Q Ln)))
    (by funext j; fin_cases j <;> rfl)
  have e : mst (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) =
      Function.update (Function.update (Function.update (fun _ => [])
        0 (Stacks.encList Q)) 1 (Stacks.encList Lo)) 2 (Stacks.encList Ln) := rfl
  rw [e] at h'
  exact (h'.execLe_size_mul_pow popLoops_mergeStmt).mono_time (mul_add_one_pow_le (by omega))

end QEnum

end Kolmogorov.RandomStrings
