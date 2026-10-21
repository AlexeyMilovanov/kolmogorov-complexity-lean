/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.KeyRoutines
import KolmogorovMathlib.RandomStrings.KeyEval

/-!
# Instances of the key-routine interface

The driver of `KeyEval` assumes routines of the forms `KeyBitRoutine`, `PairBitRoutine`,
`PairNumRoutine`: the input `x` on a stack `I`, the key codes on `A` (and `A'`), the result on `F`,
all stacks `j` with `kR ≤ j` empty work stacks, everything else untouched.

This file provides the **plumbing**: a routine is written once as a *core* program in a fixed
number `M` of stacks, run from the canonical state where only the input stack, the argument
stacks and the (empty) output stack are given (`core3`, `core4`), and inlined into the driver's
`k` stacks along an injective renaming `f` that sends the distinguished stacks of the core to
`f i0`, `f a0`, (`f a1`), `f f0` and all other stacks of the core to work stacks `≥ kR`.  Then the
renamed core satisfies the interface (`keyBit_of_core`, `pairBit_of_core`, `pairNum_of_core`),
with the same step bound and the space bound `τ.space + B`.

So each instance reduces to one closed statement about a core program on a canonical state
(no frame reasoning).  Two instances are built here: `outCore`, the verdict of the game at the
decoded key (`sOut_keyBitRoutine`), and `subCore`, the strictness test `dec κ' ⊆ dec κ`
(`sSub_pairBitRoutine`).  Both decode their key codes with `decodeKey`, whose width stack is the
unary clock built by `widthStmt`.
-/

namespace Kolmogorov.RandomStrings
namespace KeyInstances

open KeyEval

/-- The canonical state of a one-key core: input on `i0`, key code on `a0`, output stack `f0`. -/
def core3 {M : ℕ} (i0 a0 f0 : Fin M) (x κ o : BitString) : Stacks M :=
  Function.update (Function.update (Function.update (fun _ => []) i0 x) a0 κ) f0 o

/-- The canonical state of a two-key core: input on `i0`, key codes on `a0`, `a1`, output
stack `f0`. -/
def core4 {M : ℕ} (i0 a0 a1 f0 : Fin M) (x κ κ' o : BitString) : Stacks M :=
  Function.update (Function.update (Function.update (Function.update (fun _ => []) i0 x) a0 κ)
    a1 κ') f0 o

/-- The output stack of `core3` is an update: `core3 … o` is `core3 … []` with `o` written on
`f0`. -/
theorem core3_out {M : ℕ} (i0 a0 f0 : Fin M) (x κ o : BitString) :
    core3 i0 a0 f0 x κ o = Function.update (core3 i0 a0 f0 x κ []) f0 o := by
  unfold core3
  rw [Function.update_idem]

/-- The output stack of `core4` is an update: `core4 … o` is `core4 … []` with `o` written on
`f0`. -/
theorem core4_out {M : ℕ} (i0 a0 a1 f0 : Fin M) (x κ κ' o : BitString) :
    core4 i0 a0 a1 f0 x κ κ' o = Function.update (core4 i0 a0 a1 f0 x κ κ' []) f0 o := by
  unfold core4
  rw [Function.update_idem]

/-- The `f`-part of a driver state is the canonical core state. -/
theorem comp_eq_core3 {M k : ℕ} {f : Fin M → Fin k} {kR : ℕ}
    {I A F : Fin k} {i0 a0 f0 : Fin M} (hI : f i0 = I) (hA : f a0 = A) (hF : f f0 = F)
    (hwork : ∀ j : Fin M, j ≠ i0 → j ≠ a0 → j ≠ f0 → kR ≤ (f j).val) {τ : Stacks k}
    (hτF : τ F = []) (hτw : ∀ j : Fin k, kR ≤ j.val → τ j = []) :
    (fun r => τ (f r)) = core3 i0 a0 f0 (τ I) (τ A) [] := by
  funext r
  unfold core3
  by_cases h2 : r = f0
  · subst h2; rw [Function.update_self, hF, hτF]
  rw [Function.update_of_ne h2]
  by_cases h1 : r = a0
  · subst h1; rw [Function.update_self, hA]
  rw [Function.update_of_ne h1]
  by_cases h0 : r = i0
  · subst h0; rw [Function.update_self, hI]
  rw [Function.update_of_ne h0]
  exact hτw _ (hwork r h0 h1 h2)

/-- The `f`-part of a driver state is the canonical two-key core state (`comp_eq_core3` with a
second key stack). -/
theorem comp_eq_core4 {M k : ℕ} {f : Fin M → Fin k} {kR : ℕ}
    {I A A' F : Fin k} {i0 a0 a1 f0 : Fin M} (hI : f i0 = I) (hA : f a0 = A) (hA' : f a1 = A')
    (hF : f f0 = F)
    (hwork : ∀ j : Fin M, j ≠ i0 → j ≠ a0 → j ≠ a1 → j ≠ f0 → kR ≤ (f j).val) {τ : Stacks k}
    (hτF : τ F = []) (hτw : ∀ j : Fin k, kR ≤ j.val → τ j = []) :
    (fun r => τ (f r)) = core4 i0 a0 a1 f0 (τ I) (τ A) (τ A') [] := by
  funext r
  unfold core4
  by_cases h3 : r = f0
  · subst h3; rw [Function.update_self, hF, hτF]
  rw [Function.update_of_ne h3]
  by_cases h2 : r = a1
  · subst h2; rw [Function.update_self, hA']
  rw [Function.update_of_ne h2]
  by_cases h1 : r = a0
  · subst h1; rw [Function.update_self, hA]
  rw [Function.update_of_ne h1]
  by_cases h0 : r = i0
  · subst h0; rw [Function.update_self, hI]
  rw [Function.update_of_ne h0]
  exact hτw _ (hwork r h0 h1 h2 h3)

/-- Inlining a core whose run only writes the output: the frame and the space. -/
theorem execLe_inline_out {M k : ℕ} {f : Fin M → Fin k} (hf : Function.Injective f)
    {s : Stmt M} {τ : Stacks k} {f0 : Fin M} {F : Fin k} (hF : f f0 = F) {v : BitString} {B : ℕ}
    (h : ExecLe s (fun r => τ (f r)) (Function.update (fun r => τ (f r)) f0 v)
      (Stacks.space (fun r => τ (f r)) + B) B) :
    ExecLe (s.rename f) τ (Function.update τ F v) (τ.space + B) B := by
  have e := ExecLe.rename_of_comp hf h
  have hsp := Stacks.space_extend hf (fun r => τ (f r)) τ
  rw [Stacks.extend_comp_self hf τ] at hsp
  rw [← Stacks.update_extend hf, Stacks.extend_comp_self hf τ, hF] at e
  exact e.mono (by omega)

/-- **One-key instances from a core.** Let `f` rename the `M` stacks of a core `s` injectively into
the driver's `k` stacks, sending its work stacks to stacks `≥ kR`.  If for every key code `κ` of
length `L` the core turns the canonical state `core3 i0 a0 f0 x κ []` into the one with output
`[bit κ]` in at most `B` steps and within the space of that state plus `B`, then `s.rename f` is a
`KeyBitRoutine` with input stack `f i0`, key stack `f a0` and output stack `f f0`. -/
theorem keyBit_of_core {M k : ℕ} {s : Stmt M} {f : Fin M → Fin k} (hf : Function.Injective f)
    {x : BitString} {L kR : ℕ} {i0 a0 f0 : Fin M}
    (hwork : ∀ j : Fin M, j ≠ i0 → j ≠ a0 → j ≠ f0 → kR ≤ (f j).val)
    {B : ℕ} {bit : BitString → Bool}
    (hcore : ∀ κ : BitString, κ.length = L →
      ExecLe s (core3 i0 a0 f0 x κ []) (core3 i0 a0 f0 x κ [bit κ])
        ((core3 i0 a0 f0 x κ []).space + B) B) :
    KeyBitRoutine (s.rename f) x L kR (f i0) (f a0) (f f0) B bit := by
  generalize hI : f i0 = I
  generalize hA : f a0 = A
  generalize hF : f f0 = F
  intro τ hτI hτA hτF hτw
  have hc := comp_eq_core3 hI hA hF hwork hτF hτw
  refine execLe_inline_out hf hF ?_
  rw [hc, ← core3_out, hτI]
  exact hcore (τ A) hτA

/-- **Two-key bit instances from a core.** The two-key analogue of `keyBit_of_core`: if for all key
codes `κ`, `κ'` of length `L` the core turns `core4 i0 a0 a1 f0 x κ κ' []` into the state with
output `[bit κ κ']` in at most `B` steps and within the space of the initial state plus `B`, then
`s.rename f` is a `PairBitRoutine` with input stack `f i0`, key stacks `f a0`, `f a1` and output
stack `f f0`. -/
theorem pairBit_of_core {M k : ℕ} {s : Stmt M} {f : Fin M → Fin k} (hf : Function.Injective f)
    {x : BitString} {L kR : ℕ} {i0 a0 a1 f0 : Fin M}
    (hwork : ∀ j : Fin M, j ≠ i0 → j ≠ a0 → j ≠ a1 → j ≠ f0 → kR ≤ (f j).val)
    {B : ℕ} {bit : BitString → BitString → Bool}
    (hcore : ∀ κ κ' : BitString, κ.length = L → κ'.length = L →
      ExecLe s (core4 i0 a0 a1 f0 x κ κ' []) (core4 i0 a0 a1 f0 x κ κ' [bit κ κ'])
        ((core4 i0 a0 a1 f0 x κ κ' []).space + B) B) :
    PairBitRoutine (s.rename f) x L kR (f i0) (f a0) (f a1) (f f0) B bit := by
  generalize hI : f i0 = I
  generalize hA : f a0 = A
  generalize hA' : f a1 = A'
  generalize hF : f f0 = F
  intro τ hτI hτA hτA' hτF hτw
  have hc := comp_eq_core4 hI hA hA' hF hwork hτF hτw
  refine execLe_inline_out hf hF ?_
  rw [hc, ← core4_out, hτI]
  exact hcore (τ A) (τ A') hτA hτA'

/-- **Two-key number instances from a core.** As `pairBit_of_core`, for a core that writes the
`W` bits `bitsOf W (num κ κ')` of a number: `s.rename f` is then a `PairNumRoutine` on the stacks
`I`, `A`, `A'`, `F` that `f` assigns to the input, key and output stacks of the core. -/
theorem pairNum_of_core {M k : ℕ} {s : Stmt M} {f : Fin M → Fin k} (hf : Function.Injective f)
    {x : BitString} {L W kR : ℕ} {I A A' F : Fin k} {i0 a0 a1 f0 : Fin M}
    (hI : f i0 = I) (hA : f a0 = A) (hA' : f a1 = A') (hF : f f0 = F)
    (hwork : ∀ j : Fin M, j ≠ i0 → j ≠ a0 → j ≠ a1 → j ≠ f0 → kR ≤ (f j).val)
    {B : ℕ} {num : BitString → BitString → ℕ}
    (hcore : ∀ κ κ' : BitString, κ.length = L → κ'.length = L →
      ExecLe s (core4 i0 a0 a1 f0 x κ κ' []) (core4 i0 a0 a1 f0 x κ κ' (bitsOf W (num κ κ')))
        ((core4 i0 a0 a1 f0 x κ κ' []).space + B) B) :
    PairNumRoutine (s.rename f) x L W kR I A A' F B num := by
  intro τ hτI hτA hτA' hτF hτw
  have hc := comp_eq_core4 hI hA hA' hF hwork hτF hτw
  refine execLe_inline_out hf hF ?_
  rw [hc, ← core4_out, hτI]
  exact hcore (τ A) (τ A') hτA hτA'

/-! ### The decoding width: the unary clock

`decodeKey` needs a width stack of length `clock e |x|`.  `widthStmt e` builds it from the input:
the initialisation of the simulation (`SimOTM.initStmt`: the tape on `3`, the unary clock on `7`),
then the tape is cleared. -/

/-- Build `un (clock e |x|)` on stack `7` from `x` on `0` (21 stacks, all others empty). -/
def widthStmt (e : ℕ) : Stmt 21 := .seq (SimOTM.initStmt e) (Stmt.clear 3)

/-- Started on the input `x` (on stack `0`, the oracle stack `1` empty), `widthStmt e` leaves the
unary clock `un (clock e |x|)` on stack `7` and changes no other stack, within space
`8 (|x| + clock e |x| + 1)`. -/
theorem exec_widthStmt (e : ℕ) (x : BitString) :
    Exec (widthStmt e) (Function.update (Function.update (fun _ => []) 0 x) 1 [])
      (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1 []) 7
        (SimOTM.un (clock e x.length)))
      (8 * (x.length + clock e x.length + 1)) := by
  have h1 := SimOTM.exec_init e x []
  have h2 := Stmt.exec_clear (k := 21) 3 _
    (SimOTM.stk x [] (x.map some) [] 0 [] (clock e x.length) []) rfl
  refine Exec.seq (h1.mono (by simp)) (Stmt.exec_of_eq (h2.mono ?_) ?_)
  · have := h1.space_le.2
    simpa using this
  · funext j; fin_cases j <;> rfl

/-- The loops of `widthStmt e` are pop-loops. -/
theorem popLoops_widthStmt (e : ℕ) : (widthStmt e).PopLoops :=
  ⟨SimOTM.popLoops_initStmt e, Stmt.popLoops_clear 3⟩

/-- The run of `exec_widthStmt` takes at most `size * (S + 1) ^ loopDepth` steps, `S` being its
space bound. -/
theorem execLe_widthStmt (e : ℕ) (x : BitString) :
    ExecLe (widthStmt e) (Function.update (Function.update (fun _ => []) 0 x) 1 [])
      (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1 []) 7
        (SimOTM.un (clock e x.length)))
      (8 * (x.length + clock e x.length + 1))
      ((widthStmt e).size * (8 * (x.length + clock e x.length + 1) + 1) ^
        (widthStmt e).loopDepth) :=
  (exec_widthStmt e x).execLe_size_mul_pow (popLoops_widthStmt e)

/-- The inclusion of the 21 stacks of `widthStmt` and of the simulation into the first 21 of the
30 stacks of `outCore`. -/
def up21 : Fin 21 → Fin 30 := Fin.castLE (by omega)

/-- The inclusion `up21` of the simulation stacks into `outCore` is injective. -/
theorem up21_injective : Function.Injective up21 := Fin.castLE_injective _

/-- The renaming of the eight stacks of `decodeKey` into `outCore`: code copy `0 ↦ 23`, width
`1 ↦ 22`, work stacks `2`–`6 ↦ 24`–`28`, decoded list `7 ↦ 1`. -/
def decMap : Fin 8 → Fin 30 := ![23, 22, 24, 25, 26, 27, 28, 1]

/-- The renaming `decMap` of the decoder's stacks into `outCore` is injective. -/
theorem decMap_injective : Function.Injective decMap := by decide

/-- The space of the stacks outside the image of an injective renaming `f`, plus the space of the
`f`-part of `τ`, is the space of `τ`. -/
theorem rest_add_space {M k : ℕ} {f : Fin M → Fin k} (hf : Function.Injective f)
    (τ : Stacks k) : Stacks.rest f τ + Stacks.space (fun r => τ (f r)) = τ.space := by
  have hsp := Stacks.space_extend hf (fun r => τ (f r)) τ
  rw [Stacks.extend_comp_self hf τ] at hsp
  omega

/-- Inlining a program that rewrites one stack: if `s` turns the `f`-part of `τ` into itself with
stack `r` replaced by `v`, then `s.rename f` turns `τ` into itself with stack `f r` replaced by
`v`; the space bound grows by `τ.space`. -/
theorem exec_inline1 {M k : ℕ} {f : Fin M → Fin k} (hf : Function.Injective f) {s : Stmt M}
    {τ : Stacks k} {r : Fin M} {v : BitString} {S : ℕ}
    (h : Exec s (fun j => τ (f j)) (Function.update (fun j => τ (f j)) r v) S) :
    Exec (s.rename f) τ (Function.update τ (f r) v) (S + τ.space) := by
  have e := Exec.rename_of_comp hf h
  rw [← Stacks.update_extend hf, Stacks.extend_comp_self hf τ] at e
  have := rest_add_space hf τ
  exact e.mono (by omega)

/-- As `exec_inline1`, for a program that rewrites two stacks: `s` turns the `f`-part of `τ` into
itself with `r` replaced by `v` and `r'` by `v'`, so `s.rename f` does the same to `τ` at `f r` and
`f r'`, with the space bound grown by `τ.space`. -/
theorem exec_inline2 {M k : ℕ} {f : Fin M → Fin k} (hf : Function.Injective f) {s : Stmt M}
    {τ : Stacks k} {r r' : Fin M} {v v' : BitString} {S : ℕ}
    (h : Exec s (fun j => τ (f j))
      (Function.update (Function.update (fun j => τ (f j)) r v) r' v') S) :
    Exec (s.rename f) τ (Function.update (Function.update τ (f r) v) (f r') v') (S + τ.space) := by
  have e := Exec.rename_of_comp hf h
  rw [← Stacks.update_extend hf, ← Stacks.update_extend hf, Stacks.extend_comp_self hf τ] at e
  have := rest_add_space hf τ
  exact e.mono (by omega)

/-- The one-key verdict core (`sOut`), 30 stacks: input `0`, oracle code `1`, output `2`,
simulation work `3`–`20`, key code `21`, width `22`, code copy `23`, decoder work `24`–`28`,
copy temp `29`. -/
noncomputable def outCore (c : OTMCode) (e : ℕ) (T : Table) : Stmt 30 :=
  .seq ((widthStmt e).rename up21) (.seq (Stmt.moveAll 7 22) (.seq (Stmt.copy 21 23 29)
    (.seq (KeyRoutines.decodeKey.rename decMap) (.seq (Stmt.clear 22)
    (.seq (KeyRoutines.pushBad T 1) (.seq ((KeyRoutines.keyVerdictStmt c e).rename up21)
      (Stmt.clear 1)))))))

/-- The canonical state `core3 0 21 2 x κ o` of the 30-stack core `outCore` has space
`|x| + |κ| + |o|`. -/
theorem core3_space (x κ o : BitString) : (core3 (0 : Fin 30) 21 2 x κ o).space =
    x.length + κ.length + o.length := by
  simp [Stacks.space, core3, Fin.sum_univ_succ, Function.update_apply]
  ring

/-- **Correctness of the verdict core.**  On the canonical state with a key code `κ` of length
`n (2n + 1)`, `n = clock e |x|`, the core `outCore c e T` writes the outcome of the game at the
decoded key `decK n n κ` on its output stack and restores every other stack, within the space
bound displayed. -/
theorem exec_outCore (c : OTMCode) (e : ℕ) (T : Table) (x κ : BitString) (ε : ℝ)
    (X : Finset BitString)
    (hκ : κ.length = clock e x.length * (2 * clock e x.length + 1)) :
    Exec (outCore c e T) (core3 0 21 2 x κ [])
      (core3 0 21 2 x κ [(gameOf c e x T.fn ε X).outcome
        (decK (clock e x.length) (clock e x.length) κ)])
      ((c.swapAsk.k + 10) * (x.length + clock e x.length +
          (Stacks.encList (KeyRoutines.badList T)).length +
          (κ.length + 2 * clock e x.length + 1) + 1) +
        ((8 * (x.length + clock e x.length + 1) + (x.length + κ.length)) + κ.length +
          (κ.length + 2 * clock e x.length + 1) +
          (Stacks.encList (KeyRoutines.badList T)).length)) := by
  have hsp0 := core3_space x κ []
  simp only [List.length_nil, add_zero] at hsp0
  have h1 := exec_widthStmt e x
  have hu : (SimOTM.un (clock e x.length)).length = clock e x.length := List.length_replicate
  have hrev : (SimOTM.un (clock e x.length)).reverse = SimOTM.un (clock e x.length) :=
    List.reverse_replicate
  have h4 := KeyRoutines.exec_decodeKey (L := clock e x.length) (n := clock e x.length) (κ := κ)
    (u := SimOTM.un (clock e x.length)) hκ hu le_rfl
  have h7 := (KeyRoutines.execLe_keyVerdict c e T x
    (KeyRoutines.decKList (clock e x.length) (clock e x.length) κ) ε X).toExec
  have hora := congrArg List.length (KeyRoutines.encList_oraList T
    (KeyRoutines.decKList (clock e x.length) (clock e x.length) κ))
  set n := clock e x.length
  set U := SimOTM.un n
  set D := KeyRoutines.decKList n n κ
  set E := Stacks.encList D
  set σ : Stacks 30 := core3 0 21 2 x κ []
  rw [List.length_append] at hora
  have hlenO : E.length ≤ κ.length + 2 * n + 1 := by
    have hO := h4.space_le.2
    rw [KeyRoutines.dst_space] at hO
    simp only [List.length_nil] at hO
    omega
  -- step 1: the width
  have hp1 : (fun r => σ (up21 r)) =
      Function.update (Function.update (fun _ => []) 0 x) 1 [] := by
    funext r; fin_cases r <;> rfl
  rw [← hp1] at h1
  have e1 := exec_inline1 up21_injective h1
  rw [hsp0] at e1
  have hs1 := e1.space_le.2
  -- step 2: move the width to 22
  have e2 := Stmt.exec_moveAll (k := 30) (r := 7) (r' := 22) (by decide) U
    (Function.update σ (up21 7) U) rfl
  rw [hrev, show Function.update σ (up21 7) U 22 = [] from rfl, List.append_nil] at e2
  set σ₂ : Stacks 30 := Function.update σ 22 U
  have hσ2 : Function.update (Function.update (Function.update σ (up21 7) U) 7 []) 22 U =
      σ₂ := by
    funext j; fin_cases j <;> rfl
  rw [hσ2] at e2
  have hs2 := e2.space_le.2
  -- step 3: copy the code to 23
  have e3 := Stmt.exec_copy (k := 30) (r := 21) (r' := 23) (t := 29) (by decide) (by decide)
    (by decide) (σ := σ₂) rfl
  rw [show σ₂ 21 = κ from rfl, show σ₂ 23 = [] from rfl, List.append_nil] at e3
  have hs3 := e3.space_le.2
  -- step 4: decode the copy onto 1
  set ρ : Stacks 30 := Function.update σ₂ 23 κ
  have hp4 : (fun r => ρ (decMap r)) = KeyRoutines.dst κ U [] [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have hq4 : KeyRoutines.dst [] U [] [] [] [] [] E =
      Function.update (Function.update (fun r => ρ (decMap r)) 0 []) 7 E := by
    funext r; fin_cases r <;> rfl
  rw [← hp4, hq4] at h4
  have e4 := exec_inline2 decMap_injective h4
  set σ₄ : Stacks 30 := Function.update σ₂ 1 E
  have hσ4 : Function.update (Function.update ρ (decMap 0) []) (decMap 7) E = σ₄ := by
    funext j; fin_cases j <;> rfl
  rw [hσ4] at e4
  have hs4 := e4.space_le.2
  -- step 5: clear the width
  have e5 := Stmt.exec_clear (k := 30) 22 U σ₄ rfl
  set σ₅ : Stacks 30 := Function.update σ 1 E
  have hσ5 : Function.update σ₄ 22 [] = σ₅ := by
    funext j; fin_cases j <;> rfl
  rw [hσ5] at e5
  have hs5 := e5.space_le.2
  -- step 6: push the bad strings
  have e6 := (KeyRoutines.execLe_pushBad T (1 : Fin 30) σ₅ D rfl).toExec
  set σ₆ : Stacks 30 := Function.update σ 1 (Stacks.encList (KeyRoutines.oraList T D))
  have hσ6 : Function.update σ₅ 1 (Stacks.encList (KeyRoutines.oraList T D)) = σ₆ := by
    funext j; fin_cases j <;> rfl
  rw [hσ6] at e6
  have hs6 := e6.space_le.2
  -- step 7: the verdict
  have hp7 : (fun r => σ₆ (up21 r)) = Function.update (Function.update (fun _ => []) 0 x) 1
      (Stacks.encList (KeyRoutines.oraList T D)) := by
    funext r; fin_cases r <;> rfl
  rw [← hp7] at h7
  set σ₇ : Stacks 30 :=
    Function.update σ₆ (up21 2) [(gameOf c e x T.fn ε X).outcome D.toFinset]
  have e7 : Exec _ σ₆ σ₇ _ := exec_inline1 up21_injective h7
  have hs7 := e7.space_le.2
  -- step 8: clear the oracle code
  have e8 := Stmt.exec_clear (k := 30) 1 (Stacks.encList (KeyRoutines.oraList T D)) σ₇ rfl
  have hσ8 : Function.update σ₇ 1 [] =
      core3 0 21 2 x κ [(gameOf c e x T.fn ε X).outcome D.toFinset] := by
    funext j; fin_cases j <;> rfl
  rw [hσ8] at e8
  -- the bounds
  have hmul : (c.swapAsk.k + 10) *
        (x.length + n + (Stacks.encList (KeyRoutines.oraList T D)).length + 1) ≤
      (c.swapAsk.k + 10) * (x.length + n + (Stacks.encList (KeyRoutines.badList T)).length +
        (κ.length + 2 * n + 1) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  refine Exec.seq (e1.mono ?_) (Exec.seq (e2.mono ?_) (Exec.seq (e3.mono ?_) (Exec.seq (e4.mono ?_)
    (Exec.seq (e5.mono ?_) (Exec.seq (e6.mono ?_) (Exec.seq (e7.mono ?_) (e8.mono ?_)))))))
  all_goals omega

/-- The loops of `outCore` are pop-loops. -/
theorem popLoops_outCore (c : OTMCode) (e : ℕ) (T : Table) : (outCore c e T).PopLoops :=
  ⟨Stmt.popLoops_rename up21_injective _ (popLoops_widthStmt e), Stmt.popLoops_moveAll (by decide),
    Stmt.popLoops_copy (by decide) (by decide),
    Stmt.popLoops_rename decMap_injective _ KeyRoutines.popLoops_decodeKey, Stmt.popLoops_clear 22,
    Stmt.popLoops_pushList 1 _,
    Stmt.popLoops_rename up21_injective _ (SimOTM.popLoops_simStmt c.swapAsk e),
    Stmt.popLoops_clear 1⟩

/-- The space excess of `outCore` over its input (`n` the clock, `L` the code length). -/
noncomputable def outSpace (c : OTMCode) (T : Table) (xl n L : ℕ) : ℕ :=
  (c.swapAsk.k + 10) * (xl + n + (Stacks.encList (KeyRoutines.badList T)).length +
      (L + 2 * n + 1) + 1) +
    ((8 * (xl + n + 1) + (xl + L)) + L + (L + 2 * n + 1) +
      (Stacks.encList (KeyRoutines.badList T)).length)

/-- The bound `B` of the `sOut` instance. -/
noncomputable def outB (c : OTMCode) (e : ℕ) (T : Table) (xl n L : ℕ) : ℕ :=
  outSpace c T xl n L + (outCore c e T).size * (outSpace c T xl n L + 1) ^ (outCore c e T).loopDepth

/-- The verdict core within the budget `outB`: on a key code of length `n (2n + 1)`,
`n = clock e |x|`, `outCore c e T` writes the outcome of the game at the decoded key in at most
`B = outB c e T |x| n (n (2n + 1))` steps and in space `|σ| + B`, `σ` the initial state. -/
theorem execLe_outCore (c : OTMCode) (e : ℕ) (T : Table) (x κ : BitString) (ε : ℝ)
    (X : Finset BitString)
    (hκ : κ.length = clock e x.length * (2 * clock e x.length + 1)) :
    ExecLe (outCore c e T) (core3 0 21 2 x κ [])
      (core3 0 21 2 x κ [(gameOf c e x T.fn ε X).outcome
        (decK (clock e x.length) (clock e x.length) κ)])
      ((core3 (0 : Fin 30) 21 2 x κ []).space +
        outB c e T x.length (clock e x.length) (clock e x.length * (2 * clock e x.length + 1)))
      (outB c e T x.length (clock e x.length) (clock e x.length * (2 * clock e x.length + 1))) := by
  have h := (exec_outCore c e T x κ ε X hκ).execLe_size_mul_pow (popLoops_outCore c e T)
  have hsp := core3_space x κ []
  rw [← hκ]
  refine (h.mono ?_).mono_time ?_
  · simp only [outB, outSpace, hsp, List.length_nil]; omega
  · simp only [outB, outSpace]; omega

/-- The renaming of a 30-stack core into the driver's stacks: `0 ↦ I`, `21 ↦ A`, `2 ↦ F`, every
other stack `j ↦ kR + j`. -/
def liftMap {k : ℕ} (kR : ℕ) (hk : kR + 30 ≤ k) (I A F : Fin k) (j : Fin 30) : Fin k :=
  if j.val = 0 then I else if j.val = 21 then A else if j.val = 2 then F
  else ⟨kR + j.val, by omega⟩

/-- `liftMap` is injective when `I`, `A`, `F` are distinct stacks below `kR`. -/
theorem liftMap_injective {k : ℕ} {kR : ℕ} (hk : kR + 30 ≤ k) {I A F : Fin k} (hIA : I ≠ A)
    (hIF : I ≠ F) (hAF : A ≠ F) (hI : I.val < kR) (hA : A.val < kR) (hF : F.val < kR) :
    Function.Injective (liftMap kR hk I A F) := by
  intro a b h
  apply Fin.ext
  have hIA' : I.val ≠ A.val := fun e => hIA (Fin.ext e)
  have hIF' : I.val ≠ F.val := fun e => hIF (Fin.ext e)
  have hAF' : A.val ≠ F.val := fun e => hAF (Fin.ext e)
  unfold liftMap at h
  split_ifs at h <;>
    (have hv := congrArg Fin.val h; (try simp only at hv); omega)

/-- `liftMap` sends every stack of the core other than `0`, `21`, `2` to a work stack of the
driver, i.e. one with index at least `kR`. -/
theorem liftMap_work {k : ℕ} {kR : ℕ} (hk : kR + 30 ≤ k) (I A F : Fin k) (j : Fin 30)
    (h0 : j ≠ 0) (h21 : j ≠ 21) (h2 : j ≠ 2) : kR ≤ (liftMap kR hk I A F j).val := by
  have e0 : j.val ≠ 0 := fun e => h0 (Fin.ext e)
  have e21 : j.val ≠ 21 := fun e => h21 (Fin.ext e)
  have e2 : j.val ≠ 2 := fun e => h2 (Fin.ext e)
  unfold liftMap
  rw [ite_eq_right e0, ite_eq_right e21, ite_eq_right e2]
  exact Nat.le_add_right _ _

/-- **The `sOut` instance**: the verdict of the game at the decoded key, in the form the driver
assumes (`KeyBitRoutine`), for any distinct `I`, `A`, `F` below `kR`, `kR + 30 ≤ k`. -/
theorem sOut_keyBitRoutine (c : OTMCode) (e : ℕ) (T : Table) (ε : ℝ) (X : Finset BitString)
    (x : BitString) {k kR : ℕ} (hk : kR + 30 ≤ k) {I A F : Fin k} (hIA : I ≠ A) (hIF : I ≠ F)
    (hAF : A ≠ F) (hI : I.val < kR) (hA : A.val < kR) (hF : F.val < kR) :
    KeyBitRoutine ((outCore c e T).rename (liftMap kR hk I A F)) x
      (clock e x.length * (2 * clock e x.length + 1)) kR I A F
      (outB c e T x.length (clock e x.length) (clock e x.length * (2 * clock e x.length + 1)))
      (fun κ =>
        (gameOf c e x T.fn ε X).outcome (decK (clock e x.length) (clock e x.length) κ)) := by
  refine keyBit_of_core (f := liftMap kR hk I A F) (liftMap_injective hk hIA hIF hAF hI hA hF)
    (i0 := 0) (a0 := 21) (f0 := 2)
    (fun j h0 h21 h2 => liftMap_work hk I A F j h0 h21 h2) ?_
  intro κ hκ
  exact execLe_outCore c e T x κ ε X hκ

/-! ### The `sSub` instance -/

/-- The inclusion of the 21 stacks of `widthStmt` and of the simulation into the first 21 of the
43 stacks of `subCore`. -/
def up21' : Fin 21 → Fin 43 := Fin.castLE (by omega)

/-- The inclusion `up21'` of the simulation stacks into `subCore` is injective. -/
theorem up21'_injective : Function.Injective up21' := Fin.castLE_injective _

/-- The renaming of the eight stacks of `decodeKey` into `subCore` for the decoding of `κ`: code
copy `0 ↦ 23`, width `1 ↦ 22`, work stacks `2`–`6 ↦ 24`–`28`, decoded list `7 ↦ 32`. -/
def decMapA : Fin 8 → Fin 43 := ![23, 22, 24, 25, 26, 27, 28, 32]

/-- The renaming of the eight stacks of `decodeKey` into `subCore` for the decoding of `κ'`: as
`decMapA`, but the decoded list `7` goes to `31`. -/
def decMapB : Fin 8 → Fin 43 := ![23, 22, 24, 25, 26, 27, 28, 31]

/-- The renaming of the 13 stacks of `subsetTest` into `subCore`: tested list `0 ↦ 31`, list
tested against `1 ↦ 32`, flag `2 ↦ 2` (the output), work stacks `3`–`12 ↦ 33`–`42`. -/
def subMap : Fin 13 → Fin 43 := ![31, 32, 2, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42]

/-- The renaming `decMapA` of the decoder's stacks into `subCore` is injective. -/
theorem decMapA_injective : Function.Injective decMapA := by decide

/-- The renaming `decMapB` of the decoder's stacks into `subCore` is injective. -/
theorem decMapB_injective : Function.Injective decMapB := by decide

/-- The renaming `subMap` of the stacks of `subsetTest` into `subCore` is injective. -/
theorem subMap_injective : Function.Injective subMap := by decide

/-- The inclusion core (`sSub`), 43 stacks: input `0`, output `2`, codes `21` (`κ`) and `30`
(`κ'`), width `22`, code copy `23`, decoder work `24`–`28`, copy temp `29`, decoded lists `31`
(`κ'`) and `32` (`κ`), `subsetTest` work `33`–`42`. -/
noncomputable def subCore (e : ℕ) : Stmt 43 :=
  .seq ((widthStmt e).rename up21') (.seq (Stmt.moveAll 7 22)
  (.seq (Stmt.copy 21 23 29) (.seq (KeyRoutines.decodeKey.rename decMapA)
  (.seq (Stmt.copy 30 23 29) (.seq (KeyRoutines.decodeKey.rename decMapB)
  (.seq (Stmt.clear 22) (.seq (KeyRoutines.subsetTest.rename subMap)
  (.seq (Stmt.clear 31) (Stmt.clear 32)))))))))

/-- The canonical state `core4 0 21 30 2 x κ κ' o` of the 43-stack core `subCore` has space
`|x| + |κ| + |κ'| + |o|`. -/
theorem core4_space (x κ κ' o : BitString) : (core4 (0 : Fin 43) 21 30 2 x κ κ' o).space =
    x.length + κ.length + κ'.length + o.length := by
  simp [Stacks.space, core4, Fin.sum_univ_succ, Function.update_apply]
  ring

/-- **Correctness of the inclusion core.**  On the canonical state with key codes `κ`, `κ'` of
length `n (2n + 1)`, `n = clock e |x|`, the core `subCore e` writes on its output stack the truth
value of `∀ z ∈ dec κ', z ∈ dec κ`, the inclusion of the decoded keys, and restores every other
stack, within the space bound displayed. -/
theorem exec_subCore (e : ℕ) (x κ κ' : BitString)
    (hκ : κ.length = clock e x.length * (2 * clock e x.length + 1))
    (hκ' : κ'.length = clock e x.length * (2 * clock e x.length + 1)) :
    Exec (subCore e) (core4 0 21 30 2 x κ κ' [])
      (core4 0 21 30 2 x κ κ' [decide (∀ z ∈ KeyRoutines.decKList (clock e x.length)
        (clock e x.length) κ', z ∈ KeyRoutines.decKList (clock e x.length) (clock e x.length) κ)])
      (2 * ((κ'.length + 2 * clock e x.length + 1) + (κ.length + 2 * clock e x.length + 1)) + 6 +
        ((κ'.length + 2 * clock e x.length + 1) + ((κ.length + 2 * clock e x.length + 1) +
          (8 * (x.length + clock e x.length + 1) + (x.length + κ.length + κ'.length)) +
          κ.length) + κ'.length)) := by
  have hsp0 := core4_space x κ κ' []
  simp only [List.length_nil, add_zero] at hsp0
  have h1 := exec_widthStmt e x
  have hu : (SimOTM.un (clock e x.length)).length = clock e x.length := List.length_replicate
  have hrev : (SimOTM.un (clock e x.length)).reverse = SimOTM.un (clock e x.length) :=
    List.reverse_replicate
  have h4 := KeyRoutines.exec_decodeKey (L := clock e x.length) (n := clock e x.length) (κ := κ)
    (u := SimOTM.un (clock e x.length)) hκ hu le_rfl
  have h6 := KeyRoutines.exec_decodeKey (L := clock e x.length) (n := clock e x.length) (κ := κ')
    (u := SimOTM.un (clock e x.length)) hκ' hu le_rfl
  have h8 := KeyRoutines.exec_subsetTest
    (KeyRoutines.decKList (clock e x.length) (clock e x.length) κ')
    (KeyRoutines.decKList (clock e x.length) (clock e x.length) κ) le_rfl
  set n := clock e x.length
  set U := SimOTM.un n
  set D := KeyRoutines.decKList n n κ
  set D' := KeyRoutines.decKList n n κ'
  set E := Stacks.encList D
  set E' := Stacks.encList D'
  set σ : Stacks 43 := core4 0 21 30 2 x κ κ' []
  set b := decide (∀ z ∈ D', z ∈ D)
  have hlenA : E.length ≤ κ.length + 2 * n + 1 := by
    have hO := h4.space_le.2
    rw [KeyRoutines.dst_space] at hO
    simp only [List.length_nil] at hO
    omega
  have hlenB : E'.length ≤ κ'.length + 2 * n + 1 := by
    have hO := h6.space_le.2
    rw [KeyRoutines.dst_space] at hO
    simp only [List.length_nil] at hO
    omega
  -- step 1: the width
  have hp1 : (fun r => σ (up21' r)) =
      Function.update (Function.update (fun _ => []) 0 x) 1 [] := by
    funext r; fin_cases r <;> rfl
  rw [← hp1] at h1
  have e1 := exec_inline1 up21'_injective h1
  rw [hsp0] at e1
  have hs1 := e1.space_le.2
  -- step 2: move the width to 22
  have e2 := Stmt.exec_moveAll (k := 43) (r := 7) (r' := 22) (by decide) U
    (Function.update σ (up21' 7) U) rfl
  rw [hrev, show Function.update σ (up21' 7) U 22 = [] from rfl, List.append_nil] at e2
  set σ₂ : Stacks 43 := Function.update σ 22 U
  have hσ2 : Function.update (Function.update (Function.update σ (up21' 7) U) 7 []) 22 U =
      σ₂ := by
    funext j; fin_cases j <;> rfl
  rw [hσ2] at e2
  have hs2 := e2.space_le.2
  -- step 3: copy κ to 23
  have e3 := Stmt.exec_copy (k := 43) (r := 21) (r' := 23) (t := 29) (by decide) (by decide)
    (by decide) (σ := σ₂) rfl
  rw [show σ₂ 21 = κ from rfl, show σ₂ 23 = [] from rfl, List.append_nil] at e3
  have hs3 := e3.space_le.2
  -- step 4: decode κ onto 32
  set ρ₃ : Stacks 43 := Function.update σ₂ 23 κ
  have hp4 : (fun r => ρ₃ (decMapA r)) = KeyRoutines.dst κ U [] [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have hq4 : KeyRoutines.dst [] U [] [] [] [] [] E =
      Function.update (Function.update (fun r => ρ₃ (decMapA r)) 0 []) 7 E := by
    funext r; fin_cases r <;> rfl
  rw [← hp4, hq4] at h4
  have e4 := exec_inline2 decMapA_injective h4
  set σ₄ : Stacks 43 := Function.update σ₂ 32 E
  have hσ4 : Function.update (Function.update ρ₃ (decMapA 0) []) (decMapA 7) E = σ₄ := by
    funext j; fin_cases j <;> rfl
  rw [hσ4] at e4
  have hs4 := e4.space_le.2
  -- step 5: copy κ' to 23
  have e5 := Stmt.exec_copy (k := 43) (r := 30) (r' := 23) (t := 29) (by decide) (by decide)
    (by decide) (σ := σ₄) rfl
  rw [show σ₄ 30 = κ' from rfl, show σ₄ 23 = [] from rfl, List.append_nil] at e5
  have hs5 := e5.space_le.2
  -- step 6: decode κ' onto 31
  set ρ₅ : Stacks 43 := Function.update σ₄ 23 κ'
  have hp6 : (fun r => ρ₅ (decMapB r)) = KeyRoutines.dst κ' U [] [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have hq6 : KeyRoutines.dst [] U [] [] [] [] [] E' =
      Function.update (Function.update (fun r => ρ₅ (decMapB r)) 0 []) 7 E' := by
    funext r; fin_cases r <;> rfl
  rw [← hp6, hq6] at h6
  have e6 := exec_inline2 decMapB_injective h6
  set σ₆ : Stacks 43 := Function.update σ₄ 31 E'
  have hσ6 : Function.update (Function.update ρ₅ (decMapB 0) []) (decMapB 7) E' = σ₆ := by
    funext j; fin_cases j <;> rfl
  rw [hσ6] at e6
  have hs6 := e6.space_le.2
  -- step 7: clear the width
  have e7 := Stmt.exec_clear (k := 43) 22 U σ₆ rfl
  set σ₇ : Stacks 43 := Function.update (Function.update σ 32 E) 31 E'
  have hσ7 : Function.update σ₆ 22 [] = σ₇ := by
    funext j; fin_cases j <;> rfl
  rw [hσ7] at e7
  have hs7 := e7.space_le.2
  -- step 8: the inclusion test
  have hp8 : (fun r => σ₇ (subMap r)) = KeyRoutines.sst E' E [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have hσ8 : KeyRoutines.sst E' E [b] [] [] [] [] =
      Function.update (fun j => σ₇ (subMap j)) 2 [b] := by
    funext j; fin_cases j <;> rfl
  rw [← hp8, hσ8] at h8
  set σ₈ : Stacks 43 := Function.update σ₇ 2 [b]
  have e8 : Exec _ σ₇ σ₈ _ := exec_inline1 subMap_injective (r := 2) h8
  have hs8 := e8.space_le.2
  -- steps 9, 10: clear the decoded lists
  have e9 := Stmt.exec_clear (k := 43) 31 E' σ₈ rfl
  set σ₉ : Stacks 43 := Function.update σ₈ 31 []
  have hs9 := e9.space_le.2
  have e10 := Stmt.exec_clear (k := 43) 32 E σ₉ rfl
  have hσ10 : Function.update σ₉ 32 [] = core4 0 21 30 2 x κ κ' [b] := by
    funext j; fin_cases j <;> rfl
  rw [hσ10] at e10
  refine Exec.seq (e1.mono ?_) (Exec.seq (e2.mono ?_) (Exec.seq (e3.mono ?_) (Exec.seq (e4.mono ?_)
    (Exec.seq (e5.mono ?_) (Exec.seq (e6.mono ?_) (Exec.seq (e7.mono ?_) (Exec.seq (e8.mono ?_)
      (Exec.seq (e9.mono ?_) (e10.mono ?_)))))))))
  all_goals omega

/-- The loops of `subCore` are pop-loops. -/
theorem popLoops_subCore (e : ℕ) : (subCore e).PopLoops :=
  ⟨Stmt.popLoops_rename up21'_injective _ (popLoops_widthStmt e), Stmt.popLoops_moveAll (by decide),
    Stmt.popLoops_copy (by decide) (by decide),
    Stmt.popLoops_rename decMapA_injective _ KeyRoutines.popLoops_decodeKey,
    Stmt.popLoops_copy (by decide) (by decide),
    Stmt.popLoops_rename decMapB_injective _ KeyRoutines.popLoops_decodeKey, Stmt.popLoops_clear 22,
    Stmt.popLoops_rename subMap_injective _ KeyRoutines.popLoops_subsetTest,
    Stmt.popLoops_clear 31, Stmt.popLoops_clear 32⟩

/-- The space excess of `subCore` (`n` the clock, `L` the code length). -/
def subSpace (xl n L : ℕ) : ℕ :=
  2 * ((L + 2 * n + 1) + (L + 2 * n + 1)) + 6 +
    ((L + 2 * n + 1) + ((L + 2 * n + 1) + (8 * (xl + n + 1) + (xl + L + L)) + L) + L)

/-- The bound `B` of the `sSub` instance. -/
noncomputable def subB (e : ℕ) (xl n L : ℕ) : ℕ :=
  subSpace xl n L + (subCore e).size * (subSpace xl n L + 1) ^ (subCore e).loopDepth

/-- The test `∀ z ∈ l₁, z ∈ l₂` on lists decides the inclusion `l₁.toFinset ⊆ l₂.toFinset` of the
finsets they enumerate. -/
theorem decide_forall_mem_eq (l₁ l₂ : List BitString) :
    decide (∀ z ∈ l₁, z ∈ l₂) = decide (l₁.toFinset ⊆ l₂.toFinset) :=
  decide_eq_decide.2 (by simp [Finset.subset_iff])

/-- The inclusion core within the budget `subB`: on key codes of length `n (2n + 1)`,
`n = clock e |x|`, `subCore e` writes the bit `dec κ' ⊆ dec κ` in at most
`B = subB e |x| n (n (2n + 1))` steps and in space `|σ| + B`, `σ` the initial state. -/
theorem execLe_subCore (e : ℕ) (x κ κ' : BitString)
    (hκ : κ.length = clock e x.length * (2 * clock e x.length + 1))
    (hκ' : κ'.length = clock e x.length * (2 * clock e x.length + 1)) :
    ExecLe (subCore e) (core4 0 21 30 2 x κ κ' [])
      (core4 0 21 30 2 x κ κ' [decide (decK (clock e x.length) (clock e x.length) κ' ⊆
        decK (clock e x.length) (clock e x.length) κ)])
      ((core4 (0 : Fin 43) 21 30 2 x κ κ' []).space +
        subB e x.length (clock e x.length) (clock e x.length * (2 * clock e x.length + 1)))
      (subB e x.length (clock e x.length) (clock e x.length * (2 * clock e x.length + 1))) := by
  have h := (exec_subCore e x κ κ' hκ hκ').execLe_size_mul_pow (popLoops_subCore e)
  rw [decide_forall_mem_eq, show κ'.length = κ.length by rw [hκ, hκ']] at h
  have hsp := core4_space x κ κ' []
  rw [← hκ]
  refine (h.mono ?_).mono_time ?_
  · simp only [subB, subSpace, hsp, List.length_nil]; omega
  · simp only [subB, subSpace]; omega

/-- The renaming of a 43-stack two-key core into the driver's stacks: `0 ↦ I`, `21 ↦ A`,
`30 ↦ A'`, `2 ↦ F`, every other stack `j ↦ kR + j`. -/
def liftMap4 {k : ℕ} (kR : ℕ) (hk : kR + 43 ≤ k) (I A A' F : Fin k) (j : Fin 43) : Fin k :=
  if j.val = 0 then I else if j.val = 21 then A else if j.val = 30 then A'
  else if j.val = 2 then F else ⟨kR + j.val, by omega⟩

/-- `liftMap4` is injective when `I`, `A`, `A'`, `F` are distinct stacks below `kR`. -/
theorem liftMap4_injective {k : ℕ} {kR : ℕ} (hk : kR + 43 ≤ k) {I A A' F : Fin k}
    (hIA : I ≠ A) (hIA' : I ≠ A') (hIF : I ≠ F) (hAA' : A ≠ A') (hAF : A ≠ F) (hA'F : A' ≠ F)
    (hI : I.val < kR) (hA : A.val < kR) (hA' : A'.val < kR) (hF : F.val < kR) :
    Function.Injective (liftMap4 kR hk I A A' F) := by
  intro a b h
  apply Fin.ext
  have h1 : I.val ≠ A.val := fun e => hIA (Fin.ext e)
  have h2 : I.val ≠ A'.val := fun e => hIA' (Fin.ext e)
  have h3 : I.val ≠ F.val := fun e => hIF (Fin.ext e)
  have h4 : A.val ≠ A'.val := fun e => hAA' (Fin.ext e)
  have h5 : A.val ≠ F.val := fun e => hAF (Fin.ext e)
  have h6 : A'.val ≠ F.val := fun e => hA'F (Fin.ext e)
  unfold liftMap4 at h
  split_ifs at h <;>
    (have hv := congrArg Fin.val h; (try simp only at hv); omega)

/-- `liftMap4` sends every stack of the core other than `0`, `21`, `30`, `2` to a work stack of
the driver, i.e. one with index at least `kR`. -/
theorem liftMap4_work {k : ℕ} {kR : ℕ} (hk : kR + 43 ≤ k) (I A A' F : Fin k) (j : Fin 43)
    (h0 : j ≠ 0) (h21 : j ≠ 21) (h30 : j ≠ 30) (h2 : j ≠ 2) :
    kR ≤ (liftMap4 kR hk I A A' F j).val := by
  have e0 : j.val ≠ 0 := fun e => h0 (Fin.ext e)
  have e21 : j.val ≠ 21 := fun e => h21 (Fin.ext e)
  have e30 : j.val ≠ 30 := fun e => h30 (Fin.ext e)
  have e2 : j.val ≠ 2 := fun e => h2 (Fin.ext e)
  unfold liftMap4
  rw [ite_eq_right e0, ite_eq_right e21, ite_eq_right e30, ite_eq_right e2]
  exact Nat.le_add_right _ _

/-- **The `sSub` instance**: the strictness test `dec κ' ⊆ dec κ` in the form the driver
assumes (`PairBitRoutine`). -/
theorem sSub_pairBitRoutine (e : ℕ) (x : BitString) {k kR : ℕ} (hk : kR + 43 ≤ k) {I A A' F : Fin k}
    (hIA : I ≠ A) (hIA' : I ≠ A') (hIF : I ≠ F) (hAA' : A ≠ A') (hAF : A ≠ F) (hA'F : A' ≠ F)
    (hI : I.val < kR) (hA : A.val < kR) (hA' : A'.val < kR) (hF : F.val < kR) :
    PairBitRoutine ((subCore e).rename (liftMap4 kR hk I A A' F)) x
      (clock e x.length * (2 * clock e x.length + 1)) kR I A A' F
      (subB e x.length (clock e x.length) (clock e x.length * (2 * clock e x.length + 1)))
      (fun κ κ' => decide (decK (clock e x.length) (clock e x.length) κ' ⊆
        decK (clock e x.length) (clock e x.length) κ)) := by
  refine pairBit_of_core (f := liftMap4 kR hk I A A' F)
    (liftMap4_injective hk hIA hIA' hIF hAA' hAF hA'F hI hA hA' hF)
    (i0 := 0) (a0 := 21) (a1 := 30) (f0 := 2)
    (fun j h0 h21 h30 h2 => liftMap4_work hk I A A' F j h0 h21 h30 h2) ?_
  intro κ κ' hκ hκ'
  exact execLe_subCore e x κ κ' hκ hκ'

/-! ### Monotonicity of the interface in the bound `B` -/

/-- A `KeyBitRoutine` stays one when its bound `B` is raised to any `B' ≥ B`. -/
theorem keyBitRoutine_mono {k : ℕ} {s : Stmt k} {x : BitString} {L kR : ℕ} {I A F : Fin k}
    {B B' : ℕ} {bit : BitString → Bool} (h : KeyBitRoutine s x L kR I A F B bit) (hB : B ≤ B') :
    KeyBitRoutine s x L kR I A F B' bit := fun τ h1 h2 h3 h4 =>
  ((h τ h1 h2 h3 h4).mono (by omega)).mono_time hB

/-- A `PairBitRoutine` stays one when its bound `B` is raised to any `B' ≥ B`. -/
theorem pairBitRoutine_mono {k : ℕ} {s : Stmt k} {x : BitString} {L kR : ℕ} {I A A' F : Fin k}
    {B B' : ℕ} {bit : BitString → BitString → Bool} (h : PairBitRoutine s x L kR I A A' F B bit)
    (hB : B ≤ B') : PairBitRoutine s x L kR I A A' F B' bit := fun τ h1 h2 h3 h4 h5 =>
  ((h τ h1 h2 h3 h4 h5).mono (by omega)).mono_time hB

/-- A `PairNumRoutine` stays one when its bound `B` is raised to any `B' ≥ B`. -/
theorem pairNumRoutine_mono {k : ℕ} {s : Stmt k} {x : BitString} {L W kR : ℕ} {I A A' F : Fin k}
    {B B' : ℕ} {num : BitString → BitString → ℕ} (h : PairNumRoutine s x L W kR I A A' F B num)
    (hB : B ≤ B') : PairNumRoutine s x L W kR I A A' F B' num := fun τ h1 h2 h3 h4 h5 =>
  ((h τ h1 h2 h3 h4 h5).mono (by omega)).mono_time hB

/-! ### The bit of `sMove` as three test bits -/

/-- The move bit is the conjunction of the three test bits of `KeyRoutines.keyMoveRaw_iff_tests`
(`subsetTest` on `Kl'` vs `keyQ … Kl'`, `condSubsetTest` on `Kl'` with `Q = Y.toList`, `B = []`,
`condSubsetTest` on `Kl` with `Q = keyQ … Kl'`, `B = Kl'`). -/
theorem decide_keyMoveRaw_eq_tests (c : OTMCode) (e : ℕ) (T : Table) (x : BitString)
    (Y : Finset BitString) (Kl Kl' : List BitString) :
    decide (KeyMoveRaw (querySet c.toOTM x (clock e x.length) \ Y)
        (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
        Kl.toFinset Kl'.toFinset) =
      (decide (∀ z ∈ Kl', z ∈ KeyRoutines.keyQ c e T x Kl') &&
        (decide (∀ z ∈ Kl', z ∈ Y.toList → z ∈ ([] : List BitString)) &&
          decide (∀ z ∈ Kl, z ∈ KeyRoutines.keyQ c e T x Kl' → z ∈ Kl'))) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact KeyRoutines.keyMoveRaw_iff_tests c e T x Y Kl Kl'

end KeyInstances
end Kolmogorov.RandomStrings
