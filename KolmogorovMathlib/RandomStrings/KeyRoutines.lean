/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.KeyRoutines.Decoder

/-!
# Key-level routines of the EXP evaluator

Statement-level (`Stmt`) routines on keys, each with an `Exec` specification on explicit stacks and
a polynomial step bound (`ExecLe`, through pop-loop budgets); all are meant to be inlined with
`Stmt.rename` / `Exec.rename_of_comp` along injective maps.

The decoder of slot codes (`decodeKey`, which reads a slot code `κ` of `n` slots of `2L + 1` bits
and writes `Stacks.encList (decKList L n κ)`) and the run of the machine at a key (`pushBad`,
`keyVerdictStmt`, `keyQueriesStmt`) live in `KeyRoutines.Decoder`.  This module contains the tests
on a decoded key `Kl`, all on explicit stacks:

1. **Inclusion** (`subsetTest`, 13 stacks, layout `sst`): `decide (∀ z ∈ Kl, z ∈ L)`
   (`exec_subsetTest`, `execLe_subsetTest`); key validity `K ⊆ P K` (`decide_keyValid`).
2. **Conditional inclusion** (`condSubsetTest`, 15 stacks, layout `cst`):
   `decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)` (`exec_condSubsetTest`, `execLe_condSubsetTest`); the move
   condition `K ∩ P K' ⊆ K'` (`decide_keyCond`) and `Disjoint K' Y` (with `Q = Y.toList`, `B = []`);
   `keyMoveRaw_iff_tests`: `KeyMoveRaw` of the game as the conjunction of the three tests.
3. **Duplicate-freeness** (`nodupTest`, 13 stacks, layout `sst`): `decide Kl.Nodup`
   (`exec_nodupTest`, `execLe_nodupTest`).  With the cover of all keys by duplicate-free codes
   (`cover_gameOf_nodup`) and the move cost over such lists (`costN_eq_sum_filter`), the
   evaluator may skip every code whose decoded list repeats a string.
-/

namespace Kolmogorov.RandomStrings

namespace KeyRoutines

open Stmt

/-! ### Inclusion of coded lists (the validity test `K ⊆ P K`)

`subsetTest` (13 stacks): stack `0` holds `Stacks.encList Kl`, stack `1` holds
`Stacks.encList L`; the flag `[decide (∀ z ∈ Kl, z ∈ L)]` is left on `2`, both codes are
restored; stacks `3`–`12` are work stacks (`3` the current string, `4` the membership flag,
`5`–`10` the work stacks of `memTest`, `11`/`12` those of `decodeOne`). -/

/-- The stacks of `subsetTest` between iterations: `A` on `0`, `Q` on `1`, the flag `F` on `2`,
the current string `Z` on `3`, the membership flag `M` on `4`, and the work stacks `W` on `11` and
`Tm` on `12`; all other stacks are empty. -/
def sst (A Q F Z M W Tm : BitString) : Stacks 13 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (fun _ => []) 0 A) 1 Q) 2 F) 3 Z) 4 M) 11 W) 12 Tm

/-- The space of the state `sst A Q F Z M W Tm` is the total length of the seven strings on its
stacks. -/
theorem sst_space (A Q F Z M W Tm : BitString) :
    (sst A Q F Z M W Tm).space = A.length + Q.length + F.length + Z.length + M.length +
      W.length + Tm.length := by
  simp [Stacks.space, sst, Fin.sum_univ_succ, Function.update_apply]
  ring

/-- The stacks of `memTest` inside `subsetTest`: string `3`, list `1`, flag `4`, work `5`–`10`. -/
def memMapS : Fin 9 → Fin 13 := ![3, 1, 4, 5, 6, 7, 8, 9, 10]

/-- The assignment `memMapS` of the nine stacks of `memTest` to stacks of `subsetTest` is
injective. -/
theorem memMapS_injective : Function.Injective memMapS := by decide

/-- **Membership test inside `subsetTest`.**  In the state `sst A (encList L) F Z [] W Tm`, which
has the code of `L` on stack `1` and the string `Z` on `3`, the renamed `memTest` pushes the flag
`decide (Z ∈ L)` on stack `4` and changes nothing else, within the initial space plus
`|encList L| + 2`. -/
theorem exec_memS {A F Z W Tm : BitString} {L : List BitString} :
    Exec (Stmt.memTest.rename memMapS) (sst A (Stacks.encList L) F Z [] W Tm)
      (sst A (Stacks.encList L) F Z [decide (Z ∈ L)] W Tm)
      ((sst A (Stacks.encList L) F Z [] W Tm).space + (Stacks.encList L).length + 2) := by
  generalize hτ : sst A (Stacks.encList L) F Z [] W Tm = τ
  obtain ⟨h1, h4, h5, h6, h7, h8, h9, h10⟩ : τ 1 = Stacks.encList L ∧ τ 4 = [] ∧
      τ 5 = [] ∧ τ 6 = [] ∧ τ 7 = [] ∧ τ 8 = [] ∧ τ 9 = [] ∧ τ 10 = [] := by
    subst hτ
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpost : sst A (Stacks.encList L) F Z [decide (Z ∈ L)] W Tm =
      Function.update τ 4 [decide (τ 3 ∈ L)] := by
    subst hτ
    funext j
    fin_cases j <;> rfl
  rw [hpost]
  have h := Stmt.exec_memTest (σ := fun r => τ (memMapS r)) (L := L) h1 h4 h5 h6 h7 h8 h9 h10
  have h' := Exec.rename_of_comp memMapS_injective h
  have e1 : Function.extend memMapS (Function.update (fun r => τ (memMapS r)) 2
      [decide (τ (memMapS 0) ∈ L)]) τ = Function.update τ 4 [decide (τ 3 ∈ L)] := by
    rw [← Stacks.update_extend memMapS_injective, Stacks.extend_comp_self memMapS_injective]
    rfl
  have e2 : Stacks.space (fun r => τ (memMapS r)) + Stacks.rest memMapS τ = τ.space := by
    rw [← Stacks.space_extend memMapS_injective, Stacks.extend_comp_self memMapS_injective]
  rw [e1] at h'
  exact h'.mono (by omega)

/-- One element: decode it, test its membership, update the flag, clean up. -/
def subsetBody : Stmt 13 :=
  seqs [decodeOne 0 11 12, moveAll 11 3, Stmt.memTest.rename memMapS,
    caseBit 4 (fun g => .seq (.pop 4) (cond g .skip (.seq (.pop 2) (.push 2 false)))), clear 3]

/-- **The inclusion test** `∀ z ∈ Kl, z ∈ L`. -/
def subsetTest : Stmt 13 :=
  seqs [.push 2 true, .loop 0 Option.isSome subsetBody, moveAll 12 0]

/-- **One element of the inclusion test.**  Started with the code of `z` followed by `rest` on
stack `0`, the code of `L` on `1` and the flag `[f]` on `2`, `subsetBody` consumes the code of `z`,
leaves the flag `[f && decide (z ∈ L)]` on `2` and the reversed code of `z` on top of `Tm` on
`12`, within any space `S` that is at least the initial space plus `|z| + |encList L| + 3`. -/
theorem exec_subsetBody (z rest Tm : BitString) (L : List BitString) (f : Bool) {S : ℕ}
    (hS : (sst (Stacks.encStr z ++ rest) (Stacks.encList L) [f] [] [] [] Tm).space + z.length +
      (Stacks.encList L).length + 3 ≤ S) :
    Exec subsetBody (sst (Stacks.encStr z ++ rest) (Stacks.encList L) [f] [] [] [] Tm)
      (sst rest (Stacks.encList L) [f && decide (z ∈ L)] [] [] []
        ((Stacks.encStr z).reverse ++ Tm)) S := by
  have hsp := hS
  rw [sst_space] at hsp
  have e1 := exec_decodeOne (Lst := (0 : Fin 13)) (W := 11) (Tmp := 12) (by decide) (by decide)
    (by decide) (z := z) (rest := rest)
    (σ := sst (Stacks.encStr z ++ rest) (Stacks.encList L) [f] [] [] [] Tm) rfl
  have q1 : Function.update (Function.update (Function.update
      (sst (Stacks.encStr z ++ rest) (Stacks.encList L) [f] [] [] [] Tm) 0 rest) 11
      (z.reverse ++ (sst (Stacks.encStr z ++ rest) (Stacks.encList L) [f] [] [] [] Tm) 11)) 12
      ((Stacks.encStr z).reverse ++
        (sst (Stacks.encStr z ++ rest) (Stacks.encList L) [f] [] [] [] Tm) 12) =
      sst rest (Stacks.encList L) [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm) := by
    funext j; fin_cases j <;> simp [sst]
  rw [q1] at e1
  have e2 := exec_moveAll (r := (11 : Fin 13)) (r' := 3) (by decide) z.reverse
    (sst rest (Stacks.encList L) [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)) rfl
  have q2 : Function.update (Function.update
      (sst rest (Stacks.encList L) [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)) 11 [])
      3 (z.reverse.reverse ++
        (sst rest (Stacks.encList L) [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)) 3) =
      sst rest (Stacks.encList L) [f] z [] [] ((Stacks.encStr z).reverse ++ Tm) := by
    funext j; fin_cases j <;> simp [sst]
  rw [q2] at e2
  have e3 : Exec (Stmt.memTest.rename memMapS)
      (sst rest (Stacks.encList L) [f] z [] [] ((Stacks.encStr z).reverse ++ Tm))
      (sst rest (Stacks.encList L) [f] z [decide (z ∈ L)] [] ((Stacks.encStr z).reverse ++ Tm))
      _ := exec_memS
  have hlen : (Stacks.encStr z).length = 2 * z.length + 1 := Stacks.length_encStr z
  have sp3 := e3.space_le.2
  rw [sst_space] at sp3
  have e4 : Exec (caseBit 4 (fun g => .seq (.pop 4) (cond g .skip (.seq (.pop 2) (.push 2 false)))))
      (sst rest (Stacks.encList L) [f] z [decide (z ∈ L)] [] ((Stacks.encStr z).reverse ++ Tm))
      (sst rest (Stacks.encList L) [f && decide (z ∈ L)] z [] [] ((Stacks.encStr z).reverse ++ Tm))
      S := by
    rw [exec_caseBit (show (sst rest (Stacks.encList L) [f] z [decide (z ∈ L)] []
      ((Stacks.encStr z).reverse ++ Tm)) 4 = decide (z ∈ L) :: [] from rfl)]
    refine Exec.seq (σ₁ := sst rest (Stacks.encList L) [f] z [] []
      ((Stacks.encStr z).reverse ++ Tm))
      (SimOTM.exec_pop_eq (by rw [sst_space]; simp at hsp ⊢; omega)
        (by funext j; fin_cases j <;> rfl)) ?_
    by_cases hz : z ∈ L
    · simp only [hz, decide_true, Bool.cond_true, Bool.and_true]
      exact Exec.skip (by rw [sst_space]; simp at hsp ⊢; omega)
    · simp only [hz, decide_false, Bool.cond_false, Bool.and_false]
      refine Exec.seq (σ₁ := sst rest (Stacks.encList L) [] z [] []
        ((Stacks.encStr z).reverse ++ Tm))
        (SimOTM.exec_pop_eq (by rw [sst_space]; simp at hsp ⊢; omega)
          (by funext j; fin_cases j <;> rfl))
        (SimOTM.exec_push_eq (by rw [sst_space]; simp at hsp ⊢; omega)
          (by funext j; fin_cases j <;> rfl))
  have e5 := exec_clear (3 : Fin 13) z
    (sst rest (Stacks.encList L) [f && decide (z ∈ L)] z [] [] ((Stacks.encStr z).reverse ++ Tm))
    rfl
  have q5 : Function.update (sst rest (Stacks.encList L) [f && decide (z ∈ L)] z [] []
      ((Stacks.encStr z).reverse ++ Tm)) 3 [] =
      sst rest (Stacks.encList L) [f && decide (z ∈ L)] [] [] []
        ((Stacks.encStr z).reverse ++ Tm) := by
    funext j; fin_cases j <;> rfl
  rw [q5] at e5
  have sp1 := e1.space_le.2
  have sp2 := e2.space_le.2
  rw [sst_space] at sp1 sp2
  refine Exec.seq (e1.mono (by rw [sst_space]; simp at hsp ⊢; omega)) (Exec.seq
    (e2.mono (by rw [sst_space]; simp at hsp ⊢; omega)) (Exec.seq
    (e3.mono (by rw [sst_space]; simp at hsp ⊢; omega)) (Exec.seq e4 (Exec.seq
    (e5.mono (by rw [sst_space]; simp at hsp ⊢; omega))
    (Exec.skip (by rw [sst_space]; simp at hsp ⊢; omega))))))

/-- The code of a string followed by anything is nonempty, so the loop condition `Option.isSome`
holds on a stack that starts with it. -/
theorem isSome_head_encStr (z rest : BitString) :
    ((Stacks.encStr z ++ rest).head?).isSome = true := by
  cases z <;> simp [Stacks.encStr]

/-- **The loop of the inclusion test.**  Started with the code of `Kl` on stack `0`, the code of
`L` on `1`, the flag `[f]` on `2` and `Tm` on `12`, the loop over `subsetBody` empties `0`, leaves
the flag `[f && decide (∀ z ∈ Kl, z ∈ L)]` on `2` and the reversed code of `Kl` on top of `Tm`
on `12`, within any space `S` that is at least `2 (|encList Kl| + |encList L| + |Tm|) + 6`. -/
theorem exec_subsetLoop (L : List BitString) :
    ∀ (Kl : List BitString) (Tm : BitString) (f : Bool) {S : ℕ},
    2 * ((Stacks.encList Kl).length + (Stacks.encList L).length + Tm.length) + 6 ≤ S →
    Exec (.loop 0 Option.isSome subsetBody)
      (sst (Stacks.encList Kl) (Stacks.encList L) [f] [] [] [] Tm)
      (sst [] (Stacks.encList L) [f && decide (∀ z ∈ Kl, z ∈ L)] [] [] []
        ((Stacks.encList Kl).reverse ++ Tm)) S
  | [], Tm, f, S, hS => by
    have e : sst [] (Stacks.encList L) [f && decide (∀ z ∈ ([] : List BitString), z ∈ L)] [] [] []
        ((Stacks.encList []).reverse ++ Tm) =
        sst (Stacks.encList []) (Stacks.encList L) [f] [] [] [] Tm := by
      simp [Stacks.encList]
    rw [e]
    exact Exec.loopF (r := 0) (cond := Option.isSome) rfl
      (by rw [sst_space]; simp [Stacks.encList] at hS ⊢; omega)
  | z :: Kl, Tm, f, S, hS => by
    have hc : Stacks.encList (z :: Kl) = Stacks.encStr z ++ Stacks.encList Kl := by
      simp [Stacks.encList]
    have hlen : (Stacks.encStr z).length = 2 * z.length + 1 := Stacks.length_encStr z
    rw [hc] at hS ⊢
    simp only [List.length_append] at hS
    have h1 := exec_subsetBody z (Stacks.encList Kl) Tm L f (S := S)
      (by rw [sst_space]; simp only [List.length_append, List.length_singleton, List.length_nil]
          omega)
    have h2 := exec_subsetLoop L Kl ((Stacks.encStr z).reverse ++ Tm) (f && decide (z ∈ L))
      (S := S) (by simp only [List.length_append, List.length_reverse]; omega)
    have e : sst [] (Stacks.encList L) [(f && decide (z ∈ L)) && decide (∀ w ∈ Kl, w ∈ L)] [] []
        [] ((Stacks.encList Kl).reverse ++ ((Stacks.encStr z).reverse ++ Tm)) =
        sst [] (Stacks.encList L) [f && decide (∀ w ∈ z :: Kl, w ∈ L)] [] [] []
          ((Stacks.encStr z ++ Stacks.encList Kl).reverse ++ Tm) := by
      simp [List.reverse_append, Bool.and_assoc]
    rw [e] at h2
    exact Exec.loopT (r := 0) (cond := Option.isSome) (isSome_head_encStr _ _) h1 h2

/-- **Inclusion test.**  Started with the codes of `Kl` and `L` on `0` and `1` and all other
stacks empty, `subsetTest` leaves `[decide (∀ z ∈ Kl, z ∈ L)]` on `2` and restores everything
else, within space `2 (|encList Kl| + |encList L|) + 6`. -/
theorem exec_subsetTest (Kl L : List BitString) {S : ℕ}
    (hS : 2 * ((Stacks.encList Kl).length + (Stacks.encList L).length) + 6 ≤ S) :
    Exec subsetTest (sst (Stacks.encList Kl) (Stacks.encList L) [] [] [] [] [])
      (sst (Stacks.encList Kl) (Stacks.encList L) [decide (∀ z ∈ Kl, z ∈ L)] [] [] [] []) S := by
  have h0 : Exec (.push 2 true) (sst (Stacks.encList Kl) (Stacks.encList L) [] [] [] [] [])
      (sst (Stacks.encList Kl) (Stacks.encList L) [true] [] [] [] []) S :=
    SimOTM.exec_push_eq (by rw [sst_space]; simp; omega) (by funext j; fin_cases j <;> rfl)
  have h1 := exec_subsetLoop L Kl [] true (S := S) (by simp; omega)
  rw [Bool.true_and] at h1
  have h2 := exec_moveAll (r := (12 : Fin 13)) (r' := 0) (by decide)
    ((Stacks.encList Kl).reverse ++ [])
    (sst [] (Stacks.encList L) [decide (∀ z ∈ Kl, z ∈ L)] [] [] []
      ((Stacks.encList Kl).reverse ++ [])) rfl
  have q2 : Function.update (Function.update (sst [] (Stacks.encList L)
      [decide (∀ z ∈ Kl, z ∈ L)] [] [] [] ((Stacks.encList Kl).reverse ++ [])) 12 []) 0
      (((Stacks.encList Kl).reverse ++ []).reverse ++ (sst [] (Stacks.encList L)
        [decide (∀ z ∈ Kl, z ∈ L)] [] [] [] ((Stacks.encList Kl).reverse ++ [])) 0) =
      sst (Stacks.encList Kl) (Stacks.encList L) [decide (∀ z ∈ Kl, z ∈ L)] [] [] [] [] := by
    funext j; fin_cases j <;> simp [sst]
  rw [q2] at h2
  exact Exec.seq h0 (Exec.seq h1 (Exec.seq (h2.mono h1.space_le.2) (Exec.skip h2.space_le.2 |>.mono
    h1.space_le.2)))

/-- A renamed statement never pushes on a stack outside the range of the renaming. -/
theorem noPush_rename_of_not_mem {k k' : ℕ} {f : Fin k → Fin k'} {j : Fin k'}
    (hj : ∀ r, f r ≠ j) : ∀ s : Stmt k, (s.rename f).NoPush j
  | .skip => trivial
  | .push r _ => hj r
  | .pop _ => trivial
  | .seq s₁ s₂ => ⟨noPush_rename_of_not_mem hj s₁, noPush_rename_of_not_mem hj s₂⟩
  | .ite _ _ s₁ s₂ => ⟨noPush_rename_of_not_mem hj s₁, noPush_rename_of_not_mem hj s₂⟩
  | .loop _ _ b => noPush_rename_of_not_mem hj b

/-- All loops of `subsetTest` are pop-loops: the loop over `subsetBody` pops stack `0` on every
path and never pushes on it. -/
theorem popLoops_subsetTest : subsetTest.PopLoops := by
  have hm : (Stmt.memTest.rename memMapS).PopLoops :=
    popLoops_rename memMapS_injective _ Stmt.popLoops_memTest
  have hn : (Stmt.memTest.rename memMapS).NoPush 0 :=
    noPush_rename_of_not_mem (by decide) _
  refine ⟨trivial, ⟨⟨rfl, ⟨?_, ?_, hn, ?_, ?_, trivial⟩, ?_, ⟨popLoops_decodeOne (by decide)
    (by decide), popLoops_moveAll (by decide), hm, ?_, popLoops_clear 3, trivial⟩⟩,
    popLoops_moveAll (by decide), trivial⟩⟩
  · simp [decodeOne, decodeBody, moveBit, caseBit, NoPush]
  · simp [moveAll, moveBit, caseBit, NoPush]
  · simp [caseBit, NoPush]
  · simp [clear, NoPush]
  · exact Or.inl (Or.inr ⟨Or.inl rfl, Or.inl rfl⟩)
  · simp [caseBit, PopLoops]

/-- **Step bound of the inclusion test**: the run of `exec_subsetTest` takes at most
`subsetTest.budget S` steps. -/
theorem execLe_subsetTest (Kl L : List BitString) {S : ℕ}
    (hS : 2 * ((Stacks.encList Kl).length + (Stacks.encList L).length) + 6 ≤ S) :
    ExecLe subsetTest (sst (Stacks.encList Kl) (Stacks.encList L) [] [] [] [] [])
      (sst (Stacks.encList Kl) (Stacks.encList L) [decide (∀ z ∈ Kl, z ∈ L)] [] [] [] []) S
      (subsetTest.budget S) :=
  (exec_subsetTest Kl L hS).execLe_budget popLoops_subsetTest

/-- **Validity of a key** (`K ⊆ P K`): the inclusion test of the key `Kl` in the recorded queries
`keyQ c e T x Kl` of its run decides `Kl.toFinset ⊆ queries c.toOTM (oracleOf T.fn K) x clock`. -/
theorem decide_keyValid (c : OTMCode) (e : ℕ) (T : Table) (x : BitString) (Kl : List BitString) :
    decide (∀ z ∈ Kl, z ∈ keyQ c e T x Kl) =
      decide (Kl.toFinset ⊆ queries c.toOTM (oracleOf T.fn Kl.toFinset) x (clock e x.length)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h z hz
    exact (mem_keyQ c e T x Kl z).1 (h z (List.mem_toFinset.1 hz))
  · intro h z hz
    exact (mem_keyQ c e T x Kl z).2 (h (List.mem_toFinset.2 hz))

/-! ### The second half of the move test: `K ∩ P K' ⊆ K'`

`condSubsetTest` (15 stacks): the codes of `Kl`, `Q` and `B` on `0`, `1` and `13`; the flag
`[decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)]` is left on `2`, everything else is restored.  With
`Kl` the key `K`, `Q = keyQ … Kl'` the queries `P K'` and `B = Kl'` this is `K ∩ P K' ⊆ K'`
(`decide_keyCond`); with `subsetTest` for `K' ⊆ P K'` it is the move relation `KeyMoveRaw`
of `keyMoveRaw_sdiff_iff` up to the test `Disjoint K' Y` against the fixed finite set `Y`. -/

/-- The stacks of `condSubsetTest` between iterations: `A` on `0`, `Q` on `1`, the flag `F` on `2`,
the current string `Z` on `3`, the membership flag `M` of the test against `Q` on `4`, the work
stacks `W` on `11` and `Tm` on `12`, `B` on `13` and the membership flag `M2` of the test against
`B` on `14`; all other stacks are empty. -/
def cst (A Q F Z M W Tm B M2 : BitString) : Stacks 15 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (fun _ => []) 0 A) 1 Q)
      2 F) 3 Z) 4 M) 11 W) 12 Tm) 13 B) 14 M2

/-- The space of the state `cst A Q F Z M W Tm B M2` is the total length of the nine strings on
its stacks. -/
theorem cst_space (A Q F Z M W Tm B M2 : BitString) :
    (cst A Q F Z M W Tm B M2).space = A.length + Q.length + F.length + Z.length + M.length +
      W.length + Tm.length + B.length + M2.length := by
  simp [Stacks.space, cst, Fin.sum_univ_succ, Function.update_apply]
  ring

/-- The stacks of `memTest` for the test `z ∈ Q` inside `condSubsetTest`: string `3`, list `1`,
flag `4`, work `5`–`10`. -/
def memMapC1 : Fin 9 → Fin 15 := ![3, 1, 4, 5, 6, 7, 8, 9, 10]

/-- The stacks of `memTest` for the test `z ∈ B` inside `condSubsetTest`: string `3`, list `13`,
flag `14`, work `5`–`10`. -/
def memMapC2 : Fin 9 → Fin 15 := ![3, 13, 14, 5, 6, 7, 8, 9, 10]

/-- The assignment `memMapC1` of the nine stacks of `memTest` to stacks of `condSubsetTest` is
injective. -/
theorem memMapC1_injective : Function.Injective memMapC1 := by decide

/-- The assignment `memMapC2` of the nine stacks of `memTest` to stacks of `condSubsetTest` is
injective. -/
theorem memMapC2_injective : Function.Injective memMapC2 := by decide

/-- **First membership test inside `condSubsetTest`.**  In the state
`cst A (encList L) F Z [] W Tm B M2`, which has the code of `L` on stack `1` and the string `Z` on
`3`, the renamed `memTest` pushes the flag `decide (Z ∈ L)` on stack `4` and changes nothing else,
within the initial space plus `|encList L| + 2`. -/
theorem exec_memC1 {A F Z W Tm B M2 : BitString} {L : List BitString} :
    Exec (Stmt.memTest.rename memMapC1) (cst A (Stacks.encList L) F Z [] W Tm B M2)
      (cst A (Stacks.encList L) F Z [decide (Z ∈ L)] W Tm B M2)
      ((cst A (Stacks.encList L) F Z [] W Tm B M2).space + (Stacks.encList L).length + 2) := by
  generalize hτ : cst A (Stacks.encList L) F Z [] W Tm B M2 = τ
  obtain ⟨h1, h4, h5, h6, h7, h8, h9, h10⟩ : τ 1 = Stacks.encList L ∧ τ 4 = [] ∧
      τ 5 = [] ∧ τ 6 = [] ∧ τ 7 = [] ∧ τ 8 = [] ∧ τ 9 = [] ∧ τ 10 = [] := by
    subst hτ
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpost : cst A (Stacks.encList L) F Z [decide (Z ∈ L)] W Tm B M2 =
      Function.update τ 4 [decide (τ 3 ∈ L)] := by
    subst hτ
    funext j
    fin_cases j <;> rfl
  rw [hpost]
  have h := Stmt.exec_memTest (σ := fun r => τ (memMapC1 r)) (L := L) h1 h4 h5 h6 h7 h8 h9 h10
  have h' := Exec.rename_of_comp memMapC1_injective h
  have e1 : Function.extend memMapC1 (Function.update (fun r => τ (memMapC1 r)) 2
      [decide (τ (memMapC1 0) ∈ L)]) τ = Function.update τ 4 [decide (τ 3 ∈ L)] := by
    rw [← Stacks.update_extend memMapC1_injective, Stacks.extend_comp_self memMapC1_injective]
    rfl
  have e2 : Stacks.space (fun r => τ (memMapC1 r)) + Stacks.rest memMapC1 τ = τ.space := by
    rw [← Stacks.space_extend memMapC1_injective, Stacks.extend_comp_self memMapC1_injective]
  rw [e1] at h'
  exact h'.mono (by omega)

/-- **Second membership test inside `condSubsetTest`.**  In the state
`cst A Q F Z M W Tm (encList L) []`, which has the code of `L` on stack `13`, the string `Z` on `3`
and stack `14` empty, the renamed `memTest` pushes the flag `decide (Z ∈ L)` on stack `14` and
changes nothing else, within the initial space plus `|encList L| + 2`. -/
theorem exec_memC2 {A Q F Z M W Tm : BitString} {L : List BitString} :
    Exec (Stmt.memTest.rename memMapC2) (cst A Q F Z M W Tm (Stacks.encList L) [])
      (cst A Q F Z M W Tm (Stacks.encList L) [decide (Z ∈ L)])
      ((cst A Q F Z M W Tm (Stacks.encList L) []).space + (Stacks.encList L).length + 2) := by
  generalize hτ : cst A Q F Z M W Tm (Stacks.encList L) [] = τ
  obtain ⟨h1, h4, h5, h6, h7, h8, h9, h10⟩ : τ 13 = Stacks.encList L ∧ τ 14 = [] ∧
      τ 5 = [] ∧ τ 6 = [] ∧ τ 7 = [] ∧ τ 8 = [] ∧ τ 9 = [] ∧ τ 10 = [] := by
    subst hτ
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpost : cst A Q F Z M W Tm (Stacks.encList L) [decide (Z ∈ L)] =
      Function.update τ 14 [decide (τ 3 ∈ L)] := by
    subst hτ
    funext j
    fin_cases j <;> rfl
  rw [hpost]
  have h := Stmt.exec_memTest (σ := fun r => τ (memMapC2 r)) (L := L) h1 h4 h5 h6 h7 h8 h9 h10
  have h' := Exec.rename_of_comp memMapC2_injective h
  have e1 : Function.extend memMapC2 (Function.update (fun r => τ (memMapC2 r)) 2
      [decide (τ (memMapC2 0) ∈ L)]) τ = Function.update τ 14 [decide (τ 3 ∈ L)] := by
    rw [← Stacks.update_extend memMapC2_injective, Stacks.extend_comp_self memMapC2_injective]
    rfl
  have e2 : Stacks.space (fun r => τ (memMapC2 r)) + Stacks.rest memMapC2 τ = τ.space := by
    rw [← Stacks.space_extend memMapC2_injective, Stacks.extend_comp_self memMapC2_injective]
  rw [e1] at h'
  exact h'.mono (by omega)

/-- One element `z`: the flag is cleared if `z ∈ Q` and `z ∉ B`. -/
def condBody : Stmt 15 :=
  seqs [decodeOne 0 11 12, moveAll 11 3, Stmt.memTest.rename memMapC1,
    Stmt.memTest.rename memMapC2,
    caseBit 4 (fun g₁ => .seq (.pop 4) (caseBit 14 (fun g₂ => .seq (.pop 14)
      (cond (g₁ && !g₂) (.seq (.pop 2) (.push 2 false)) .skip)))), clear 3]

/-- **The conditional inclusion test** `∀ z ∈ Kl, z ∈ Q → z ∈ B`. -/
def condSubsetTest : Stmt 15 :=
  seqs [.push 2 true, .loop 0 Option.isSome condBody, moveAll 12 0]

/-- **One element of the conditional inclusion test.**  Started with the code of `z` followed by
`rest` on stack `0`, the codes of `Q` and `B` on `1` and `13` and the flag `[f]` on `2`,
`condBody` consumes the code of `z`, clears the flag exactly when `z ∈ Q` and `z ∉ B` (it leaves
`[f && !(decide (z ∈ Q) && !decide (z ∈ B))]`) and leaves the reversed code of `z` on top of
`Tm` on `12`, within any space `S` that is at least the initial space plus
`|z| + |encList Q| + |encList B| + 4`. -/
theorem exec_condBody (z rest Tm : BitString) (Q B : List BitString) (f : Bool) {S : ℕ}
    (hS : (cst (Stacks.encStr z ++ rest) (Stacks.encList Q) [f] [] [] [] Tm (Stacks.encList B)
      []).space + z.length + (Stacks.encList Q).length + (Stacks.encList B).length + 4 ≤ S) :
    Exec condBody
      (cst (Stacks.encStr z ++ rest) (Stacks.encList Q) [f] [] [] [] Tm (Stacks.encList B) [])
      (cst rest (Stacks.encList Q) [f && !(decide (z ∈ Q) && !decide (z ∈ B))] [] [] []
        ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) []) S := by
  have hsp := hS
  rw [cst_space] at hsp
  have hlen : (Stacks.encStr z).length = 2 * z.length + 1 := Stacks.length_encStr z
  have e1 := exec_decodeOne (Lst := (0 : Fin 15)) (W := 11) (Tmp := 12) (by decide) (by decide)
    (by decide) (z := z) (rest := rest)
    (σ := cst (Stacks.encStr z ++ rest) (Stacks.encList Q) [f] [] [] [] Tm (Stacks.encList B) [])
    rfl
  have q1 : Function.update (Function.update (Function.update
      (cst (Stacks.encStr z ++ rest) (Stacks.encList Q) [f] [] [] [] Tm (Stacks.encList B) []) 0
        rest) 11
      (z.reverse ++ (cst (Stacks.encStr z ++ rest) (Stacks.encList Q) [f] [] [] [] Tm
        (Stacks.encList B) []) 11)) 12
      ((Stacks.encStr z).reverse ++
        (cst (Stacks.encStr z ++ rest) (Stacks.encList Q) [f] [] [] [] Tm (Stacks.encList B) [])
          12) =
      cst rest (Stacks.encList Q) [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)
        (Stacks.encList B) [] := by
    funext j; fin_cases j <;> simp [cst]
  rw [q1] at e1
  have e2 := exec_moveAll (r := (11 : Fin 15)) (r' := 3) (by decide) z.reverse
    (cst rest (Stacks.encList Q) [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)
      (Stacks.encList B) []) rfl
  have q2 : Function.update (Function.update
      (cst rest (Stacks.encList Q) [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)
        (Stacks.encList B) []) 11 [])
      3 (z.reverse.reverse ++
        (cst rest (Stacks.encList Q) [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)
          (Stacks.encList B) []) 3) =
      cst rest (Stacks.encList Q) [f] z [] [] ((Stacks.encStr z).reverse ++ Tm)
        (Stacks.encList B) [] := by
    funext j; fin_cases j <;> simp [cst]
  rw [q2] at e2
  have e3 : Exec (Stmt.memTest.rename memMapC1)
      (cst rest (Stacks.encList Q) [f] z [] [] ((Stacks.encStr z).reverse ++ Tm)
        (Stacks.encList B) [])
      (cst rest (Stacks.encList Q) [f] z [decide (z ∈ Q)] [] ((Stacks.encStr z).reverse ++ Tm)
        (Stacks.encList B) []) _ := exec_memC1
  have e4 : Exec (Stmt.memTest.rename memMapC2)
      (cst rest (Stacks.encList Q) [f] z [decide (z ∈ Q)] [] ((Stacks.encStr z).reverse ++ Tm)
        (Stacks.encList B) [])
      (cst rest (Stacks.encList Q) [f] z [decide (z ∈ Q)] [] ((Stacks.encStr z).reverse ++ Tm)
        (Stacks.encList B) [decide (z ∈ B)]) _ := exec_memC2
  have sp1 := e1.space_le.2
  have sp2 := e2.space_le.2
  have sp3 := e3.space_le.2
  have sp4 := e4.space_le.2
  rw [cst_space] at sp1 sp2 sp3 sp4
  have e5 : Exec (caseBit 4 (fun g₁ => .seq (.pop 4) (caseBit 14 (fun g₂ => .seq (.pop 14)
      (cond (g₁ && !g₂) (.seq (.pop 2) (.push 2 false)) .skip)))))
      (cst rest (Stacks.encList Q) [f] z [decide (z ∈ Q)] [] ((Stacks.encStr z).reverse ++ Tm)
        (Stacks.encList B) [decide (z ∈ B)])
      (cst rest (Stacks.encList Q) [f && !(decide (z ∈ Q) && !decide (z ∈ B))] z [] []
        ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) []) S := by
    rw [exec_caseBit (show (cst rest (Stacks.encList Q) [f] z [decide (z ∈ Q)] []
      ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) [decide (z ∈ B)]) 4 =
        decide (z ∈ Q) :: [] from rfl)]
    refine Exec.seq (σ₁ := cst rest (Stacks.encList Q) [f] z [] []
      ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) [decide (z ∈ B)])
      (SimOTM.exec_pop_eq (by rw [cst_space]; simp at hsp ⊢; omega)
        (by funext j; fin_cases j <;> rfl)) ?_
    rw [exec_caseBit (show (cst rest (Stacks.encList Q) [f] z [] []
      ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) [decide (z ∈ B)]) 14 =
        decide (z ∈ B) :: [] from rfl)]
    refine Exec.seq (σ₁ := cst rest (Stacks.encList Q) [f] z [] []
      ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) [])
      (SimOTM.exec_pop_eq (by rw [cst_space]; simp at hsp ⊢; omega)
        (by funext j; fin_cases j <;> rfl)) ?_
    by_cases hq : z ∈ Q <;> by_cases hb : z ∈ B
    · simp only [hq, hb, decide_true, Bool.not_true, Bool.and_false, Bool.cond_false,
        Bool.not_false, Bool.and_true]
      exact Exec.skip (by rw [cst_space]; simp at hsp ⊢; omega)
    · simp only [hq, hb, decide_true, decide_false, Bool.not_false, Bool.and_true, Bool.cond_true,
        Bool.not_true, Bool.and_false]
      exact Exec.seq (σ₁ := cst rest (Stacks.encList Q) [] z [] []
        ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) [])
        (SimOTM.exec_pop_eq (by rw [cst_space]; simp at hsp ⊢; omega)
          (by funext j; fin_cases j <;> rfl))
        (SimOTM.exec_push_eq (by rw [cst_space]; simp at hsp ⊢; omega)
          (by funext j; fin_cases j <;> rfl))
    · simp only [hq, hb, decide_true, decide_false, Bool.not_true, Bool.false_and, Bool.cond_false,
        Bool.not_false, Bool.and_true]
      exact Exec.skip (by rw [cst_space]; simp at hsp ⊢; omega)
    · simp only [hq, hb, decide_false, Bool.cond_false, Bool.not_false, Bool.and_true]
      exact Exec.skip (by rw [cst_space]; simp at hsp ⊢; omega)
  have e6 := exec_clear (3 : Fin 15) z
    (cst rest (Stacks.encList Q) [f && !(decide (z ∈ Q) && !decide (z ∈ B))] z [] []
      ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) []) rfl
  have q6 : Function.update (cst rest (Stacks.encList Q)
      [f && !(decide (z ∈ Q) && !decide (z ∈ B))] z [] []
      ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) []) 3 [] =
      cst rest (Stacks.encList Q) [f && !(decide (z ∈ Q) && !decide (z ∈ B))] [] [] []
        ((Stacks.encStr z).reverse ++ Tm) (Stacks.encList B) [] := by
    funext j; fin_cases j <;> rfl
  rw [q6] at e6
  refine Exec.seq (e1.mono (by rw [cst_space]; simp at hsp ⊢; omega)) (Exec.seq
    (e2.mono (by rw [cst_space]; simp at hsp ⊢; omega)) (Exec.seq
    (e3.mono (by rw [cst_space]; simp at hsp ⊢; omega)) (Exec.seq
    (e4.mono (by rw [cst_space]; simp at hsp sp3 ⊢; omega)) (Exec.seq e5 (Exec.seq
    (e6.mono (by rw [cst_space]; simp at hsp ⊢; omega))
    (Exec.skip (by rw [cst_space]; simp at hsp ⊢; omega)))))))

/-- **The loop of the conditional inclusion test.**  Started with the code of `Kl` on stack `0`,
the codes of `Q` and `B` on `1` and `13`, the flag `[f]` on `2` and `Tm` on `12`, the loop over
`condBody` empties `0`, leaves the flag `[f && decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)]` on `2`
and the reversed code of `Kl` on top of `Tm` on `12`, within any space `S` that is at least
`2 (|encList Kl| + |encList Q| + |encList B| + |Tm|) + 6`. -/
theorem exec_condLoop (Q B : List BitString) :
    ∀ (Kl : List BitString) (Tm : BitString) (f : Bool) {S : ℕ},
    2 * ((Stacks.encList Kl).length + (Stacks.encList Q).length + (Stacks.encList B).length +
      Tm.length) + 6 ≤ S →
    Exec (.loop 0 Option.isSome condBody)
      (cst (Stacks.encList Kl) (Stacks.encList Q) [f] [] [] [] Tm (Stacks.encList B) [])
      (cst [] (Stacks.encList Q) [f && decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)] [] [] []
        ((Stacks.encList Kl).reverse ++ Tm) (Stacks.encList B) []) S
  | [], Tm, f, S, hS => by
    have e : cst [] (Stacks.encList Q) [f && decide (∀ z ∈ ([] : List BitString), z ∈ Q → z ∈ B)] []
        [] [] ((Stacks.encList []).reverse ++ Tm) (Stacks.encList B) [] =
        cst (Stacks.encList []) (Stacks.encList Q) [f] [] [] [] Tm (Stacks.encList B) [] := by
      simp [Stacks.encList]
    rw [e]
    exact Exec.loopF (r := 0) (cond := Option.isSome) rfl
      (by rw [cst_space]; simp [Stacks.encList] at hS ⊢; omega)
  | z :: Kl, Tm, f, S, hS => by
    have hc : Stacks.encList (z :: Kl) = Stacks.encStr z ++ Stacks.encList Kl := by
      simp [Stacks.encList]
    have hlen : (Stacks.encStr z).length = 2 * z.length + 1 := Stacks.length_encStr z
    rw [hc] at hS ⊢
    simp only [List.length_append] at hS
    have h1 := exec_condBody z (Stacks.encList Kl) Tm Q B f (S := S)
      (by rw [cst_space]; simp only [List.length_append, List.length_singleton, List.length_nil]
          omega)
    have h2 := exec_condLoop Q B Kl ((Stacks.encStr z).reverse ++ Tm)
      (f && !(decide (z ∈ Q) && !decide (z ∈ B)))
      (S := S) (by simp only [List.length_append, List.length_reverse]; omega)
    have e : cst [] (Stacks.encList Q) [(f && !(decide (z ∈ Q) && !decide (z ∈ B))) &&
        decide (∀ w ∈ Kl, w ∈ Q → w ∈ B)] [] [] []
        ((Stacks.encList Kl).reverse ++ ((Stacks.encStr z).reverse ++ Tm)) (Stacks.encList B) [] =
        cst [] (Stacks.encList Q) [f && decide (∀ w ∈ z :: Kl, w ∈ Q → w ∈ B)] [] [] []
          ((Stacks.encStr z ++ Stacks.encList Kl).reverse ++ Tm) (Stacks.encList B) [] := by
      have hb : (!(decide (z ∈ Q) && !decide (z ∈ B))) = decide (z ∈ Q → z ∈ B) := by
        by_cases hq : z ∈ Q <;> by_cases hb : z ∈ B <;> simp [hq, hb]
      rw [hb]
      simp [List.reverse_append, Bool.and_assoc]
    rw [e] at h2
    exact Exec.loopT (r := 0) (cond := Option.isSome) (isSome_head_encStr _ _) h1 h2

/-- **Conditional inclusion test.**  Started with the codes of `Kl`, `Q`, `B` on `0`, `1`, `13`
and all other stacks empty, `condSubsetTest` leaves `[decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)]` on `2`
and restores everything else, within space `2 (|encList Kl| + |encList Q| + |encList B|) + 6`. -/
theorem exec_condSubsetTest (Kl Q B : List BitString) {S : ℕ}
    (hS : 2 * ((Stacks.encList Kl).length + (Stacks.encList Q).length +
      (Stacks.encList B).length) + 6 ≤ S) :
    Exec condSubsetTest
      (cst (Stacks.encList Kl) (Stacks.encList Q) [] [] [] [] [] (Stacks.encList B) [])
      (cst (Stacks.encList Kl) (Stacks.encList Q) [decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)] [] [] [] []
        (Stacks.encList B) []) S := by
  have h0 : Exec (.push 2 true)
      (cst (Stacks.encList Kl) (Stacks.encList Q) [] [] [] [] [] (Stacks.encList B) [])
      (cst (Stacks.encList Kl) (Stacks.encList Q) [true] [] [] [] [] (Stacks.encList B) []) S :=
    SimOTM.exec_push_eq (by rw [cst_space]; simp; omega) (by funext j; fin_cases j <;> rfl)
  have h1 := exec_condLoop Q B Kl [] true (S := S) (by simp; omega)
  rw [Bool.true_and] at h1
  have h2 := exec_moveAll (r := (12 : Fin 15)) (r' := 0) (by decide)
    ((Stacks.encList Kl).reverse ++ [])
    (cst [] (Stacks.encList Q) [decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)] [] [] []
      ((Stacks.encList Kl).reverse ++ []) (Stacks.encList B) []) rfl
  have q2 : Function.update (Function.update (cst [] (Stacks.encList Q)
      [decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)] [] [] [] ((Stacks.encList Kl).reverse ++ [])
        (Stacks.encList B) []) 12 []) 0
      (((Stacks.encList Kl).reverse ++ []).reverse ++ (cst [] (Stacks.encList Q)
        [decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)] [] [] [] ((Stacks.encList Kl).reverse ++ [])
          (Stacks.encList B) []) 0) =
      cst (Stacks.encList Kl) (Stacks.encList Q) [decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)] [] [] [] []
        (Stacks.encList B) [] := by
    funext j; fin_cases j <;> simp [cst]
  rw [q2] at h2
  exact Exec.seq h0 (Exec.seq h1 (Exec.seq (h2.mono h1.space_le.2) (Exec.skip h2.space_le.2 |>.mono
    h1.space_le.2)))

/-- All loops of `condSubsetTest` are pop-loops: the loop over `condBody` pops stack `0` on every
path and never pushes on it. -/
theorem popLoops_condSubsetTest : condSubsetTest.PopLoops := by
  have hm1 : (Stmt.memTest.rename memMapC1).PopLoops :=
    popLoops_rename memMapC1_injective _ Stmt.popLoops_memTest
  have hm2 : (Stmt.memTest.rename memMapC2).PopLoops :=
    popLoops_rename memMapC2_injective _ Stmt.popLoops_memTest
  have hn1 : (Stmt.memTest.rename memMapC1).NoPush 0 :=
    noPush_rename_of_not_mem (by decide) _
  have hn2 : (Stmt.memTest.rename memMapC2).NoPush 0 :=
    noPush_rename_of_not_mem (by decide) _
  refine ⟨trivial, ⟨⟨rfl, ⟨?_, ?_, hn1, hn2, ?_, ?_, trivial⟩, ?_, ⟨popLoops_decodeOne (by decide)
    (by decide), popLoops_moveAll (by decide), hm1, hm2, ?_, popLoops_clear 3, trivial⟩⟩,
    popLoops_moveAll (by decide), trivial⟩⟩
  · simp [decodeOne, decodeBody, moveBit, caseBit, NoPush]
  · simp [moveAll, moveBit, caseBit, NoPush]
  · simp [caseBit, NoPush]
  · simp [clear, NoPush]
  · exact Or.inl (Or.inr ⟨Or.inl rfl, Or.inl rfl⟩)
  · simp [caseBit, PopLoops]

/-- **Step bound of the conditional inclusion test**: the run of `exec_condSubsetTest` takes at
most `condSubsetTest.budget S` steps. -/
theorem execLe_condSubsetTest (Kl Q B : List BitString) {S : ℕ}
    (hS : 2 * ((Stacks.encList Kl).length + (Stacks.encList Q).length +
      (Stacks.encList B).length) + 6 ≤ S) :
    ExecLe condSubsetTest
      (cst (Stacks.encList Kl) (Stacks.encList Q) [] [] [] [] [] (Stacks.encList B) [])
      (cst (Stacks.encList Kl) (Stacks.encList Q) [decide (∀ z ∈ Kl, z ∈ Q → z ∈ B)] [] [] [] []
        (Stacks.encList B) []) S (condSubsetTest.budget S) :=
  (exec_condSubsetTest Kl Q B hS).execLe_budget popLoops_condSubsetTest

/-- **The second half of the move test**: with `Q` the recorded queries of the key `Kl'`, the
conditional inclusion test decides `K ∩ P K' ⊆ K'`. -/
theorem decide_keyCond (c : OTMCode) (e : ℕ) (T : Table) (x : BitString) (Kl Kl' : List BitString) :
    decide (∀ z ∈ Kl, z ∈ keyQ c e T x Kl' → z ∈ Kl') =
      decide (Kl.toFinset ∩ queries c.toOTM (oracleOf T.fn Kl'.toFinset) x (clock e x.length) ⊆
        Kl'.toFinset) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h z hz
    rw [Finset.mem_inter] at hz
    exact List.mem_toFinset.2 (h z (List.mem_toFinset.1 hz.1) ((mem_keyQ c e T x Kl' z).2 hz.2))
  · intro h z hz hq
    exact List.mem_toFinset.1 (h (Finset.mem_inter.2 ⟨List.mem_toFinset.2 hz,
      (mem_keyQ c e T x Kl' z).1 hq⟩))

/-- **The move relation by three list tests.**  By `keyMoveRaw_sdiff_iff`, for keys given as
lists, `KeyMoveRaw` of the game is the conjunction of `subsetTest` (`K' ⊆ P K'`), `condSubsetTest`
with `Q = Y.toList`, `B = []` (`Disjoint K' Y`), and `condSubsetTest` with `Q = keyQ … Kl'`,
`B = Kl'` (`K ∩ P K' ⊆ K'`). -/
theorem keyMoveRaw_iff_tests (c : OTMCode) (e : ℕ) (T : Table) (x : BitString)
    (Y : Finset BitString) (Kl Kl' : List BitString) :
    KeyMoveRaw (querySet c.toOTM x (clock e x.length) \ Y)
        (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
        Kl.toFinset Kl'.toFinset ↔
      (∀ z ∈ Kl', z ∈ keyQ c e T x Kl') ∧ (∀ z ∈ Kl', z ∈ Y.toList → z ∈ ([] : List BitString)) ∧
        (∀ z ∈ Kl, z ∈ keyQ c e T x Kl' → z ∈ Kl') := by
  rw [keyMoveRaw_sdiff_iff (fun S => queries_subset_querySet _ _ _ _)]
  have h1 := decide_keyValid c e T x Kl'
  have h3 := decide_keyCond c e T x Kl Kl'
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff] at h1 h3
  rw [h1, h3]
  have h2 : Disjoint Kl'.toFinset Y ↔ ∀ z ∈ Kl', z ∈ Y.toList → z ∈ ([] : List BitString) := by
    rw [Finset.disjoint_left]
    simp
  rw [h2]

/-! ### Duplicate-freeness of a decoded key (`nodupTest`, 13 stacks, layout `sst` with `1` unused)

The decoded list of a slot code may repeat a string; a cost sum over the list counts a repeated
string twice.  `nodupTest` decides `Kl.Nodup` (each string is tested against the rest of the list,
which `memTest` reads in place on stack `0`). -/

/-- The stacks of `memTest` inside `nodupTest`: string `3`, list `0`, flag `4`, work `5`–`10`. -/
def memMapN0 : Fin 9 → Fin 13 := ![3, 0, 4, 5, 6, 7, 8, 9, 10]

/-- The assignment `memMapN0` of the nine stacks of `memTest` to stacks of `nodupTest` is
injective. -/
theorem memMapN0_injective : Function.Injective memMapN0 := by decide

/-- **Membership test inside `nodupTest`.**  In the state `sst (encList L) Q F Z [] W Tm`, which
has the code of `L` on stack `0` and the string `Z` on `3`, the renamed `memTest` pushes the flag
`decide (Z ∈ L)` on stack `4` and changes nothing else, within the initial space plus
`|encList L| + 2`. -/
theorem exec_memN0 {Q F Z W Tm : BitString} {L : List BitString} :
    Exec (Stmt.memTest.rename memMapN0) (sst (Stacks.encList L) Q F Z [] W Tm)
      (sst (Stacks.encList L) Q F Z [decide (Z ∈ L)] W Tm)
      ((sst (Stacks.encList L) Q F Z [] W Tm).space + (Stacks.encList L).length + 2) := by
  generalize hτ : sst (Stacks.encList L) Q F Z [] W Tm = τ
  obtain ⟨h1, h4, h5, h6, h7, h8, h9, h10⟩ : τ 0 = Stacks.encList L ∧ τ 4 = [] ∧
      τ 5 = [] ∧ τ 6 = [] ∧ τ 7 = [] ∧ τ 8 = [] ∧ τ 9 = [] ∧ τ 10 = [] := by
    subst hτ
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpost : sst (Stacks.encList L) Q F Z [decide (Z ∈ L)] W Tm =
      Function.update τ 4 [decide (τ 3 ∈ L)] := by
    subst hτ
    funext j
    fin_cases j <;> rfl
  rw [hpost]
  have h := Stmt.exec_memTest (σ := fun r => τ (memMapN0 r)) (L := L) h1 h4 h5 h6 h7 h8 h9 h10
  have h' := Exec.rename_of_comp memMapN0_injective h
  have e1 : Function.extend memMapN0 (Function.update (fun r => τ (memMapN0 r)) 2
      [decide (τ (memMapN0 0) ∈ L)]) τ = Function.update τ 4 [decide (τ 3 ∈ L)] := by
    rw [← Stacks.update_extend memMapN0_injective, Stacks.extend_comp_self memMapN0_injective]
    rfl
  have e2 : Stacks.space (fun r => τ (memMapN0 r)) + Stacks.rest memMapN0 τ = τ.space := by
    rw [← Stacks.space_extend memMapN0_injective, Stacks.extend_comp_self memMapN0_injective]
  rw [e1] at h'
  exact h'.mono (by omega)

/-- One element: decode it, test it against the rest of the list, clear the flag on a repeat. -/
def nodupBody : Stmt 13 :=
  seqs [decodeOne 0 11 12, moveAll 11 3, Stmt.memTest.rename memMapN0,
    caseBit 4 (fun g => .seq (.pop 4) (cond g (.seq (.pop 2) (.push 2 false)) .skip)), clear 3]

/-- **The duplicate test** `Kl.Nodup`. -/
def nodupTest : Stmt 13 :=
  seqs [.push 2 true, .loop 0 Option.isSome nodupBody, moveAll 12 0]

/-- **One element of the duplicate test.**  Started with the code of `z` followed by the code of
`Kl` on stack `0` and the flag `[f]` on `2`, `nodupBody` consumes the code of `z`, leaves the flag
`[f && !decide (z ∈ Kl)]` on `2` and the reversed code of `z` on top of `Tm` on `12`, within any
space `S` that is at least the initial space plus `|z| + |encList Kl| + 3`. -/
theorem exec_nodupBody (z Tm : BitString) (Kl : List BitString) (f : Bool) {S : ℕ}
    (hS : (sst (Stacks.encStr z ++ Stacks.encList Kl) [] [f] [] [] [] Tm).space + z.length +
      (Stacks.encList Kl).length + 3 ≤ S) :
    Exec nodupBody (sst (Stacks.encStr z ++ Stacks.encList Kl) [] [f] [] [] [] Tm)
      (sst (Stacks.encList Kl) [] [f && !decide (z ∈ Kl)] [] [] []
        ((Stacks.encStr z).reverse ++ Tm)) S := by
  have hsp := hS
  rw [sst_space] at hsp
  have e1 := exec_decodeOne (Lst := (0 : Fin 13)) (W := 11) (Tmp := 12) (by decide) (by decide)
    (by decide) (z := z) (rest := Stacks.encList Kl)
    (σ := sst (Stacks.encStr z ++ Stacks.encList Kl) [] [f] [] [] [] Tm) rfl
  have q1 : Function.update (Function.update (Function.update
      (sst (Stacks.encStr z ++ Stacks.encList Kl) [] [f] [] [] [] Tm) 0 (Stacks.encList Kl)) 11
      (z.reverse ++ (sst (Stacks.encStr z ++ Stacks.encList Kl) [] [f] [] [] [] Tm) 11)) 12
      ((Stacks.encStr z).reverse ++
        (sst (Stacks.encStr z ++ Stacks.encList Kl) [] [f] [] [] [] Tm) 12) =
      sst (Stacks.encList Kl) [] [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm) := by
    funext j; fin_cases j <;> simp [sst]
  rw [q1] at e1
  have e2 := exec_moveAll (r := (11 : Fin 13)) (r' := 3) (by decide) z.reverse
    (sst (Stacks.encList Kl) [] [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)) rfl
  have q2 : Function.update (Function.update
      (sst (Stacks.encList Kl) [] [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)) 11 [])
      3 (z.reverse.reverse ++
        (sst (Stacks.encList Kl) [] [f] [] [] z.reverse ((Stacks.encStr z).reverse ++ Tm)) 3) =
      sst (Stacks.encList Kl) [] [f] z [] [] ((Stacks.encStr z).reverse ++ Tm) := by
    funext j; fin_cases j <;> simp [sst]
  rw [q2] at e2
  have e3 : Exec (Stmt.memTest.rename memMapN0)
      (sst (Stacks.encList Kl) [] [f] z [] [] ((Stacks.encStr z).reverse ++ Tm))
      (sst (Stacks.encList Kl) [] [f] z [decide (z ∈ Kl)] [] ((Stacks.encStr z).reverse ++ Tm))
      _ := exec_memN0
  have hlen : (Stacks.encStr z).length = 2 * z.length + 1 := Stacks.length_encStr z
  have e4 : Exec (caseBit 4 (fun g => .seq (.pop 4) (cond g (.seq (.pop 2) (.push 2 false)) .skip)))
      (sst (Stacks.encList Kl) [] [f] z [decide (z ∈ Kl)] [] ((Stacks.encStr z).reverse ++ Tm))
      (sst (Stacks.encList Kl) [] [f && !decide (z ∈ Kl)] z [] [] ((Stacks.encStr z).reverse ++ Tm))
      S := by
    rw [exec_caseBit (show (sst (Stacks.encList Kl) [] [f] z [decide (z ∈ Kl)] []
      ((Stacks.encStr z).reverse ++ Tm)) 4 = decide (z ∈ Kl) :: [] from rfl)]
    refine Exec.seq (σ₁ := sst (Stacks.encList Kl) [] [f] z [] []
      ((Stacks.encStr z).reverse ++ Tm))
      (SimOTM.exec_pop_eq (by rw [sst_space]; simp at hsp ⊢; omega)
        (by funext j; fin_cases j <;> rfl)) ?_
    by_cases hz : z ∈ Kl
    · simp only [hz, decide_true, Bool.cond_true, Bool.not_true, Bool.and_false]
      exact Exec.seq (σ₁ := sst (Stacks.encList Kl) [] [] z [] []
        ((Stacks.encStr z).reverse ++ Tm))
        (SimOTM.exec_pop_eq (by rw [sst_space]; simp at hsp ⊢; omega)
          (by funext j; fin_cases j <;> rfl))
        (SimOTM.exec_push_eq (by rw [sst_space]; simp at hsp ⊢; omega)
          (by funext j; fin_cases j <;> rfl))
    · simp only [hz, decide_false, Bool.cond_false, Bool.not_false, Bool.and_true]
      exact Exec.skip (by rw [sst_space]; simp at hsp ⊢; omega)
  have e5 := exec_clear (3 : Fin 13) z
    (sst (Stacks.encList Kl) [] [f && !decide (z ∈ Kl)] z [] [] ((Stacks.encStr z).reverse ++ Tm))
    rfl
  have q5 : Function.update (sst (Stacks.encList Kl) [] [f && !decide (z ∈ Kl)] z [] []
      ((Stacks.encStr z).reverse ++ Tm)) 3 [] =
      sst (Stacks.encList Kl) [] [f && !decide (z ∈ Kl)] [] [] []
        ((Stacks.encStr z).reverse ++ Tm) := by
    funext j; fin_cases j <;> rfl
  rw [q5] at e5
  refine Exec.seq (e1.mono (by rw [sst_space]; simp at hsp ⊢; omega)) (Exec.seq
    (e2.mono (by rw [sst_space]; simp at hsp ⊢; omega)) (Exec.seq
    (e3.mono (by rw [sst_space]; simp at hsp ⊢; omega)) (Exec.seq e4 (Exec.seq
    (e5.mono (by rw [sst_space]; simp at hsp ⊢; omega))
    (Exec.skip (by rw [sst_space]; simp at hsp ⊢; omega))))))

/-- **The loop of the duplicate test.**  Started with the code of `Kl` on stack `0`, the flag `[f]`
on `2` and `Tm` on `12`, the loop over `nodupBody` empties `0`, leaves the flag
`[f && decide Kl.Nodup]` on `2` and the reversed code of `Kl` on top of `Tm` on `12`, within any
space `S` that is at least `2 (|encList Kl| + |Tm|) + 6`. -/
theorem exec_nodupLoop : ∀ (Kl : List BitString) (Tm : BitString) (f : Bool) {S : ℕ},
    2 * ((Stacks.encList Kl).length + Tm.length) + 6 ≤ S →
    Exec (.loop 0 Option.isSome nodupBody) (sst (Stacks.encList Kl) [] [f] [] [] [] Tm)
      (sst [] [] [f && decide Kl.Nodup] [] [] [] ((Stacks.encList Kl).reverse ++ Tm)) S
  | [], Tm, f, S, hS => by
    have e : sst [] [] [f && decide ([] : List BitString).Nodup] [] [] []
        ((Stacks.encList []).reverse ++ Tm) = sst (Stacks.encList []) [] [f] [] [] [] Tm := by
      simp [Stacks.encList]
    rw [e]
    exact Exec.loopF (r := 0) (cond := Option.isSome) rfl
      (by rw [sst_space]; simp [Stacks.encList] at hS ⊢; omega)
  | z :: Kl, Tm, f, S, hS => by
    have hc : Stacks.encList (z :: Kl) = Stacks.encStr z ++ Stacks.encList Kl := by
      simp [Stacks.encList]
    have hlen : (Stacks.encStr z).length = 2 * z.length + 1 := Stacks.length_encStr z
    rw [hc] at hS ⊢
    simp only [List.length_append] at hS
    have h1 := exec_nodupBody z Tm Kl f (S := S)
      (by rw [sst_space]; simp only [List.length_append, List.length_singleton, List.length_nil]
          omega)
    have h2 := exec_nodupLoop Kl ((Stacks.encStr z).reverse ++ Tm) (f && !decide (z ∈ Kl))
      (S := S) (by simp only [List.length_append, List.length_reverse]; omega)
    have e : sst [] [] [(f && !decide (z ∈ Kl)) && decide Kl.Nodup] [] [] []
        ((Stacks.encList Kl).reverse ++ ((Stacks.encStr z).reverse ++ Tm)) =
        sst [] [] [f && decide (z :: Kl).Nodup] [] [] []
          ((Stacks.encStr z ++ Stacks.encList Kl).reverse ++ Tm) := by
      simp [List.reverse_append, Bool.and_assoc, List.nodup_cons]
    rw [e] at h2
    exact Exec.loopT (r := 0) (cond := Option.isSome) (isSome_head_encStr _ _) h1 h2

/-- **Duplicate test.**  Started with the code of `Kl` on `0` and all other stacks empty,
`nodupTest` leaves `[decide Kl.Nodup]` on `2` and restores the code, within space
`2 |encList Kl| + 6`. -/
theorem exec_nodupTest (Kl : List BitString) {S : ℕ} (hS : 2 * (Stacks.encList Kl).length + 6 ≤ S) :
    Exec nodupTest (sst (Stacks.encList Kl) [] [] [] [] [] [])
      (sst (Stacks.encList Kl) [] [decide Kl.Nodup] [] [] [] []) S := by
  have h0 : Exec (.push 2 true) (sst (Stacks.encList Kl) [] [] [] [] [] [])
      (sst (Stacks.encList Kl) [] [true] [] [] [] []) S :=
    SimOTM.exec_push_eq (by rw [sst_space]; simp; omega) (by funext j; fin_cases j <;> rfl)
  have h1 := exec_nodupLoop Kl [] true (S := S) (by simp; omega)
  rw [Bool.true_and] at h1
  have h2 := exec_moveAll (r := (12 : Fin 13)) (r' := 0) (by decide)
    ((Stacks.encList Kl).reverse ++ [])
    (sst [] [] [decide Kl.Nodup] [] [] [] ((Stacks.encList Kl).reverse ++ [])) rfl
  have q2 : Function.update (Function.update (sst [] [] [decide Kl.Nodup] [] [] []
      ((Stacks.encList Kl).reverse ++ [])) 12 []) 0
      (((Stacks.encList Kl).reverse ++ []).reverse ++ (sst [] [] [decide Kl.Nodup] [] [] []
        ((Stacks.encList Kl).reverse ++ [])) 0) =
      sst (Stacks.encList Kl) [] [decide Kl.Nodup] [] [] [] [] := by
    funext j; fin_cases j <;> simp [sst]
  rw [q2] at h2
  exact Exec.seq h0 (Exec.seq h1 (Exec.seq (h2.mono h1.space_le.2) (Exec.skip h2.space_le.2 |>.mono
    h1.space_le.2)))

/-- All loops inside `nodupBody` are pop-loops.  The loop of `nodupTest` around `nodupBody` is not:
`memTest` pops the rest of the list on stack `0` and pushes it back. -/
theorem popLoops_nodupBody : nodupBody.PopLoops := by
  have hm : (Stmt.memTest.rename memMapN0).PopLoops :=
    popLoops_rename memMapN0_injective _ Stmt.popLoops_memTest
  refine ⟨popLoops_decodeOne (by decide) (by decide), popLoops_moveAll (by decide), hm, ?_,
    popLoops_clear 3, trivial⟩
  simp [caseBit, PopLoops]

/-- The duplicate loop as a loop with a variant (it is not a pop-loop: `memTest` reads the rest of
the list in place and pushes it back): at most `|encList Kl| * (nodupBody.budget S + 2) + 1`
steps. -/
theorem execLe_nodupLoop (Kl : List BitString) (Tm : BitString) (f : Bool) {S : ℕ}
    (hS : 2 * ((Stacks.encList Kl).length + Tm.length) + 6 ≤ S) :
    ExecLe (.loop 0 Option.isSome nodupBody) (sst (Stacks.encList Kl) [] [f] [] [] [] Tm)
      (sst [] [] [f && decide Kl.Nodup] [] [] [] ((Stacks.encList Kl).reverse ++ Tm)) S
      ((Stacks.encList Kl).length * (nodupBody.budget S + 2) + 1) := by
  have key := ExecLe.loop_of_exec (r := (0 : Fin 13)) (cond := Option.isSome) (body := nodupBody)
    (fun σ => ∃ (Kl : List BitString) (Tm : BitString) (f : Bool),
      σ = sst (Stacks.encList Kl) [] [f] [] [] [] Tm ∧
        2 * ((Stacks.encList Kl).length + Tm.length) + 6 ≤ S)
    (fun σ => (σ 0).length) S (nodupBody.budget S) ?_
    (sst (Stacks.encList Kl) [] [f] [] [] [] Tm) _ ⟨Kl, Tm, f, rfl, hS⟩
    (exec_nodupLoop Kl Tm f hS)
  · exact key
  · rintro σ₁ σ₂ ⟨Kl₁, Tm₁, f₁, rfl, hS₁⟩ hc hex
    refine ⟨hex.execLe_budget popLoops_nodupBody, ?_⟩
    cases Kl₁ with
    | nil =>
      exfalso
      have h0 : sst (Stacks.encList []) [] [f₁] [] [] [] Tm₁ 0 = [] := rfl
      rw [h0] at hc
      exact absurd hc (by simp)
    | cons z Kl' =>
      have hc' : Stacks.encList (z :: Kl') = Stacks.encStr z ++ Stacks.encList Kl' := by
        simp [Stacks.encList]
      have hlen : (Stacks.encStr z).length = 2 * z.length + 1 := Stacks.length_encStr z
      rw [hc'] at hS₁ hex
      simp only [List.length_append] at hS₁
      have hspec := exec_nodupBody z Tm₁ Kl' f₁ (S := S)
        (by rw [sst_space]; simp only [List.length_append, List.length_singleton, List.length_nil]
            omega)
      obtain rfl := hex.det hspec
      refine ⟨⟨Kl', (Stacks.encStr z).reverse ++ Tm₁, f₁ && !decide (z ∈ Kl'), rfl, ?_⟩, ?_⟩
      · simp only [List.length_append, List.length_reverse]; omega
      · change (Stacks.encList Kl').length < (Stacks.encList (z :: Kl')).length
        rw [hc', List.length_append]; omega

/-- **Step bound of the duplicate test**: the run of `exec_nodupTest` takes at most
`|encList Kl| * (nodupBody.budget S + 2) + 6 |encList Kl| + 3` steps. -/
theorem execLe_nodupTest (Kl : List BitString) {S : ℕ}
    (hS : 2 * (Stacks.encList Kl).length + 6 ≤ S) :
    ExecLe nodupTest (sst (Stacks.encList Kl) [] [] [] [] [] [])
      (sst (Stacks.encList Kl) [] [decide Kl.Nodup] [] [] [] []) S
      (1 + (((Stacks.encList Kl).length * (nodupBody.budget S + 2) + 1) +
        ((6 * (Stacks.encList Kl).length + 1) + 0))) := by
  have h0 : ExecLe (.push 2 true) (sst (Stacks.encList Kl) [] [] [] [] [] [])
      (sst (Stacks.encList Kl) [] [true] [] [] [] []) S 1 :=
    ExecLe.of_eq (ExecLe.push (by rw [sst_space]; simp; omega) le_rfl)
      (by funext j; fin_cases j <;> rfl)
  have h1 := execLe_nodupLoop Kl [] true (S := S) (by simp; omega)
  rw [Bool.true_and] at h1
  have sp1 := h1.toExec.space_le.2
  have h2 := Stmt.execLe_moveAll (r := (12 : Fin 13)) (r' := 0) (by decide)
    ((Stacks.encList Kl).reverse ++ [])
    (sst [] [] [decide Kl.Nodup] [] [] [] ((Stacks.encList Kl).reverse ++ [])) rfl
  have q2 : Function.update (Function.update (sst [] [] [decide Kl.Nodup] [] [] []
      ((Stacks.encList Kl).reverse ++ [])) 12 []) 0
      (((Stacks.encList Kl).reverse ++ []).reverse ++ (sst [] [] [decide Kl.Nodup] [] [] []
        ((Stacks.encList Kl).reverse ++ [])) 0) =
      sst (Stacks.encList Kl) [] [decide Kl.Nodup] [] [] [] [] := by
    funext j; fin_cases j <;> simp [sst]
  have hl : ((Stacks.encList Kl).reverse ++ []).length = (Stacks.encList Kl).length := by simp
  rw [q2, hl] at h2
  have h2' := h2.mono sp1
  exact ExecLe.seq h0 (ExecLe.seq h1 (ExecLe.seq h2' (ExecLe.skip h2'.toExec.space_le.2)))

/-! ### Codes with duplicate-free decoded lists suffice -/

/-- The canonical code of a small key decodes to `K.toList` (duplicate-free). -/
theorem decKList_encK {L n : ℕ} {K : Finset BitString} (hcard : K.card ≤ n)
    (hlen : ∀ z ∈ K, z.length ≤ L) : decKList L n (encK L n K) = K.toList := by
  have hw : ∀ s ∈ K.toList.map (encSlot L) ++ List.replicate (n - K.card) (emptySlot L),
      s.length = 2 * L + 1 := by
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hs
      exact length_encSlot (hlen z (Finset.mem_toList.1 hz))
    · rw [List.eq_of_mem_replicate hs]; exact length_emptySlot L
  have hlen' :
      (K.toList.map (encSlot L) ++ List.replicate (n - K.card) (emptySlot L)).length = n := by
    simp only [List.length_append, List.length_map, Finset.length_toList, List.length_replicate]
    omega
  unfold decKList encK
  have := slots_flatten (2 * L + 1) _ hw
  rw [hlen'] at this
  rw [this, List.filterMap_append, List.filterMap_replicate_of_none (decSlot_emptySlot L),
    List.append_nil, List.filterMap_map]
  have : (decSlot ∘ encSlot L) = some := funext fun z => decSlot_encSlot L z
  rw [this, List.filterMap_some]

/-- **Cover by duplicate-free codes**: the cover hypothesis of `yesKC_eq` holds for the slot codes
whose decoded list passes `nodupTest`, so the evaluator may skip the other codes. -/
theorem cover_gameOf_nodup (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ)
    (X : Finset BitString) :
    ∀ K : Finset BitString, K ⊆ X → K ⊆ queries c.toOTM (oracleOf h K) x (clock e x.length) →
      ∃ κ ∈ (allBits (clock e x.length * (2 * clock e x.length + 1))).filter
          (fun κ => decide (decKList (clock e x.length) (clock e x.length) κ).Nodup),
        decK (clock e x.length) (clock e x.length) κ = K := by
  intro K _ hKP
  have hcard : K.card ≤ clock e x.length :=
    (Finset.card_le_card hKP).trans (card_queries_le _ _ _ _)
  have hlen : ∀ z ∈ K, z.length ≤ clock e x.length := by
    intro z hz
    obtain ⟨s, hs, hz'⟩ := (mem_queries _ _ x _ z).1 (hKP hz)
    exact (length_le_of_askedAt _ _ x s z hz').trans hs.le
  refine ⟨encK (clock e x.length) (clock e x.length) K, List.mem_filter.2
    ⟨(encK_spec hcard hlen).1, ?_⟩, (encK_spec hcard hlen).2⟩
  rw [decKList_encK hcard hlen]
  simpa using K.nodup_toList

/-- **The move cost over duplicate-free lists**: the cost of the move `Kl → Kl'` is the sum over
the strings of `Kl'` not in `Kl`, in list order (the target of a cost loop over the decoded key). -/
theorem costN_eq_sum_filter (c : BitString → ℕ) (Kl Kl' : List BitString) (hnd : Kl'.Nodup) :
    costN c Kl.toFinset Kl'.toFinset = ((Kl'.filter fun z => decide (z ∉ Kl)).map c).sum := by
  unfold costN
  have h1 : Kl'.toFinset \ Kl.toFinset = (Kl'.filter fun z => decide (z ∉ Kl)).toFinset := by
    ext z
    simp
  rw [h1, List.sum_toFinset _ (hnd.filter _)]

end KeyRoutines

end Kolmogorov.RandomStrings
