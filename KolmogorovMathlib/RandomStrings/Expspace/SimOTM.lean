/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.CodedLists

/-!
# Simulating the clocked machine with a listed oracle

The 21-stack statement `SimOTM.simStmt` that runs a clocked oracle machine on input `x` with the
oracle given as a coded list: the stack layout, the initialisation of the tape and of the unary
clock, the simulation of one step, and the main contract `exists_simStmt`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace SimOTM

/-- Code of a tape cell: a blank as `[false]`, a bit `b` as `[true, b]`. -/
def encCell : Sym → BitString
  | none => [false]
  | some b => [true, b]

/-- Code of a list of cells. -/
def encCells (cs : List Sym) : BitString := cs.flatMap encCell

/-- Unary code. -/
def un (n : ℕ) : BitString := List.replicate n true

/-- The stacks of the simulation (21 stacks): `0` input, `1` oracle code, `2` output, `3` the
tape from the head on, `4` the tape left of the head (nearest cell on top), `5` the state (unary),
`6` the query buffer (reversed), `7` the clock (unary), `8` a copy of the query, `9` a flag,
`10`–`15` work stacks of `memTest`, `16` the record of the queries, `17`–`20` work stacks. -/
def stk (x eL : BitString) (rs ls : List Sym) (q : ℕ) (rb : BitString) (clk : ℕ)
    (qs : BitString) : Stacks 21 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1 eL) 3 (encCells rs))
      4 (encCells ls)) 5 (un q)) 6 rb) 7 (un clk)) 16 qs

/-- The total space of the stacks `stk x eL rs ls q rb clk qs` is the sum of the lengths of their
contents: the input, the oracle code, the codes of the two halves of the tape, the unary state,
the query buffer, the unary clock and the record of the queries. -/
theorem stk_space (x eL : BitString) (rs ls : List Sym) (q : ℕ) (rb : BitString) (clk : ℕ)
    (qs : BitString) :
    (stk x eL rs ls q rb clk qs).space = x.length + eL.length + (encCells rs).length +
      (encCells ls).length + q + rb.length + clk + qs.length := by
  simp [Stacks.space, stk, Fin.sum_univ_succ, Function.update_apply, un]
  ring

/-! #### Initialisation: loading the tape and the unary clock -/

/-- The stacks during the initialisation: `0` input, `1` oracle code, `3` tape, `7` clock,
`17`–`20` work stacks (`17` the unary length of the input, `18` the clock under construction). -/
def istk (x eL r3 c7 a17 a18 a19 a20 : BitString) : Stacks 21 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1 eL) 3 r3) 7 c7)
      17 a17) 18 a18) 19 a19) 20 a20

/-- The total space of the initialisation stacks `istk x eL r3 c7 a17 a18 a19 a20` is the sum of
the lengths of their contents. -/
theorem istk_space (x eL r3 c7 a17 a18 a19 a20 : BitString) :
    (istk x eL r3 c7 a17 a18 a19 a20).space = x.length + eL.length + r3.length + c7.length +
      a17.length + a18.length + a19.length + a20.length := by
  simp [Stacks.space, istk, Fin.sum_univ_succ, Function.update_apply]
  ring

/-- The start configuration, with the input `x` on stack `0`, the oracle code `eL` on stack `1`
and every other stack empty, is `istk` with all of its work stacks empty. -/
theorem istk_start (x eL : BitString) :
    Function.update (Function.update (fun _ => []) 0 x) 1 eL = istk x eL [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

/-- When the initialisation has finished, with the tape code of `x` on stack `3` and the unary
clock `T` on stack `7`, the stacks are those of the simulation `stk` on the tape `x.map some`,
with empty left part, state `0`, empty query buffer and empty record. -/
theorem istk_end (x eL : BitString) (T : ℕ) :
    istk x eL (encCells (x.map some)) (un T) [] [] [] [] =
      stk x eL (x.map some) [] 0 [] T [] := by
  funext j; fin_cases j <;> rfl

/-- Pushing the bit `b` on stack `r` takes `σ` to `σ'` in space `S`, provided `σ.space + 1 ≤ S`
and `σ'` is `σ` with `b :: σ r` stored at `r`: this is `Exec.push` with the result given by an
equation. -/
theorem exec_push_eq {k : ℕ} {r : Fin k} {b : Bool} {σ σ' : Stacks k} {S : ℕ}
    (h : σ.space + 1 ≤ S) (e : Function.update σ r (b :: σ r) = σ') :
    Exec (.push r b) σ σ' S :=
  e ▸ Exec.push h

/-- Popping stack `r` takes `σ` to `σ'` in space `S`, provided `σ.space ≤ S` and `σ'` is `σ`
with `(σ r).tail` stored at `r`: this is `Exec.pop` with the result given by an equation. -/
theorem exec_pop_eq {k : ℕ} {r : Fin k} {σ σ' : Stacks k} {S : ℕ}
    (h : σ.space ≤ S) (e : Function.update σ r (σ r).tail = σ') : Exec (.pop r) σ σ' S :=
  e ▸ Exec.pop h

/-- The code of the cells `some b`, for the bits `b` of `x`, has length `2 * x.length`. -/
theorem length_encCells_map_some (x : BitString) :
    (encCells (x.map some)).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [encCells, encCell] at ih ⊢; omega

/-- One step of loading the input: move a bit `b` back from `20` to `0`, push its cell code
`true, b` on `3` and a unary digit on `17`. -/
def loadBody : Stmt 21 :=
  Stmt.caseBit 20 fun b => Stmt.seqs [.pop 20, .push 0 b, .push 3 b, .push 3 true, .push 17 true]

/-- Loading the input: the tape code on `3` and the unary length on `17`; the input is restored. -/
def loadStmt : Stmt 21 := .seq (Stmt.moveAll 0 20) (.loop 20 Option.isSome loadBody)

/-- One pass of `loadBody` on the bit `b` on top of stack `20`: it pops `b`, pushes it back on
stack `0`, pushes the cell code `true, b` on stack `3` and a unary digit on stack `17`. -/
theorem exec_loadBody (a0 eL a3 a17 l : BitString) (b : Bool) :
    Exec loadBody (istk a0 eL a3 [] a17 [] [] (b :: l))
      (istk (b :: a0) eL (true :: b :: a3) [] (true :: a17) [] [] l)
      (a0.length + eL.length + a3.length + a17.length + l.length + 4) := by
  rw [loadBody, Stmt.exec_caseBit (b := b) (l := l) rfl]
  have e1 : Exec (.pop 20) (istk a0 eL a3 [] a17 [] [] (b :: l)) (istk a0 eL a3 [] a17 [] [] l)
      (a0.length + eL.length + a3.length + a17.length + l.length + 4) :=
    exec_pop_eq (by simp only [istk_space, List.length_cons, List.length_nil]; omega)
      (by funext j; fin_cases j <;> rfl)
  have e2 : Exec (.push 0 b) (istk a0 eL a3 [] a17 [] [] l) (istk (b :: a0) eL a3 [] a17 [] [] l)
      (a0.length + eL.length + a3.length + a17.length + l.length + 4) :=
    exec_push_eq (by simp only [istk_space, List.length_nil]; omega)
      (by funext j; fin_cases j <;> rfl)
  have e3 : Exec (.push 3 b) (istk (b :: a0) eL a3 [] a17 [] [] l)
      (istk (b :: a0) eL (b :: a3) [] a17 [] [] l)
      (a0.length + eL.length + a3.length + a17.length + l.length + 4) :=
    exec_push_eq (by simp only [istk_space, List.length_cons, List.length_nil]; omega)
      (by funext j; fin_cases j <;> rfl)
  have e4 : Exec (.push 3 true) (istk (b :: a0) eL (b :: a3) [] a17 [] [] l)
      (istk (b :: a0) eL (true :: b :: a3) [] a17 [] [] l)
      (a0.length + eL.length + a3.length + a17.length + l.length + 4) :=
    exec_push_eq (by simp only [istk_space, List.length_cons, List.length_nil]; omega)
      (by funext j; fin_cases j <;> rfl)
  have e5 : Exec (.push 17 true) (istk (b :: a0) eL (true :: b :: a3) [] a17 [] [] l)
      (istk (b :: a0) eL (true :: b :: a3) [] (true :: a17) [] [] l)
      (a0.length + eL.length + a3.length + a17.length + l.length + 4) :=
    exec_push_eq (by simp only [istk_space, List.length_cons, List.length_nil]; omega)
      (by funext j; fin_cases j <;> rfl)
  exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.skip e5.space_le.2)))))

/-- The loop of `loadStmt` consumes the bits `l` on stack `20`: it pushes them back on stack `0`
(in the reverse order), puts their cell codes in front of the tape code on stack `3` and
`l.length` unary digits in front of the contents of stack `17`. -/
theorem exec_loadLoop (eL : BitString) : ∀ (l a0 a3 a17 : BitString),
    Exec (.loop 20 Option.isSome loadBody) (istk a0 eL a3 [] a17 [] [] l)
      (istk (l.reverse ++ a0) eL (encCells (l.reverse.map some) ++ a3) [] (un l.length ++ a17)
        [] [] [])
      (a0.length + eL.length + a3.length + a17.length + 4 * l.length)
  | [], a0, a3, a17 => by
    refine Stmt.exec_of_eq (.loopF rfl ?_) ?_
    · simp [istk_space]
    · simp [encCells, un]
  | b :: l, a0, a3, a17 => by
    have h1 := exec_loadBody a0 eL a3 a17 l b
    have h2 := exec_loadLoop eL l (b :: a0) (true :: b :: a3) (true :: a17)
    refine .loopT rfl (h1.mono ?_) (Stmt.exec_of_eq (h2.mono ?_) ?_)
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · congr 1
      · simp
      · simp [encCells, encCell]
      · simp [un, List.replicate_succ']

/-- Loading the input: `loadStmt` turns the input `x` on stack `0` and the oracle code `eL` on
stack `1` into the tape code `encCells (x.map some)` on stack `3` and the unary length of `x` on
stack `17`, restoring the input on stack `0`. -/
theorem exec_load (x eL : BitString) :
    Exec loadStmt (istk x eL [] [] [] [] [] [])
      (istk x eL (encCells (x.map some)) [] (un x.length) [] [] [])
      (eL.length + 4 * x.length) := by
  have h0 := Stmt.exec_moveAll (k := 21) (r := 0) (r' := 20) (by decide) x
    (istk x eL [] [] [] [] [] []) rfl
  rw [show (istk x eL [] [] [] [] [] []) 20 = [] from rfl, List.append_nil] at h0
  have h0' : Exec (Stmt.moveAll 0 20) (istk x eL [] [] [] [] [] [])
      (istk [] eL [] [] [] [] [] x.reverse) (eL.length + 4 * x.length) := by
    refine Stmt.exec_of_eq (h0.mono ?_) ?_
    · simp only [istk_space, List.length_nil]; omega
    · funext j; fin_cases j <;> rfl
  have h1 := exec_loadLoop eL x.reverse [] [] []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse, List.length_nil,
    Nat.zero_add, Nat.add_zero] at h1
  exact .seq h0' (h1.mono (by omega))

/-- The multiplication loop: for each digit of `18`, append a copy of `17` to `19`. -/
def mulLoop : Stmt 21 := .loop 18 Option.isSome (.seq (.pop 18) (Stmt.copy 17 19 20))

/-- `18 := 18 · 17` in unary (through the work stacks `19`, `20`). -/
def mulStep : Stmt 21 := .seq mulLoop (Stmt.moveAll 19 18)

/-- The unary code of `n` has length `n`. -/
theorem length_un (n : ℕ) : (un n).length = n := by simp [un]

/-- The multiplication loop: if stack `18` holds the unary number `a` and stack `17` the unary
number `n`, then `mulLoop` empties stack `18` and puts `a` copies of the unary code of `n` in front
of the contents `r19` of stack `19`, which then holds `un (a * n) ++ r19`. -/
theorem exec_mulLoop (x eL a3 c7 : BitString) (n B : ℕ) : ∀ (a : ℕ) (r19 : BitString),
    x.length + eL.length + a3.length + c7.length + n + a + r19.length + a * n ≤ B →
    Exec mulLoop (istk x eL a3 c7 (un n) (un a) r19 [])
      (istk x eL a3 c7 (un n) [] (un (a * n) ++ r19) []) B
  | 0, r19, hB => by
    refine Stmt.exec_of_eq (.loopF rfl ?_) ?_
    · simp only [istk_space, length_un, List.length_nil]; omega
    · simp [un]
  | a + 1, r19, hB => by
    have hm : (a + 1) * n = a * n + n := by ring
    have e1 : Exec (.pop 18) (istk x eL a3 c7 (un n) (un (a + 1)) r19 [])
        (istk x eL a3 c7 (un n) (un a) r19 []) B :=
      exec_pop_eq (by simp only [istk_space, length_un, List.length_nil]; omega)
        (by funext j; fin_cases j <;> rfl)
    have e2 := Stmt.exec_copy (k := 21) (r := 17) (r' := 19) (t := 20) (by decide) (by decide)
      (by decide) (σ := istk x eL a3 c7 (un n) (un a) r19 []) rfl
    have e2' : Exec (Stmt.copy 17 19 20) (istk x eL a3 c7 (un n) (un a) r19 [])
        (istk x eL a3 c7 (un n) (un a) (un n ++ r19) []) B := by
      refine Stmt.exec_of_eq (e2.mono ?_) ?_
      · rw [show (istk x eL a3 c7 (un n) (un a) r19 []) 17 = un n from rfl]
        simp only [istk_space, length_un, List.length_nil]
        omega
      · funext j; fin_cases j <;> rfl
    have ih := exec_mulLoop x eL a3 c7 n B a (un n ++ r19)
      (by simp only [List.length_append, length_un]; omega)
    refine .loopT rfl (.seq e1 e2') (Stmt.exec_of_eq ih ?_)
    have hu : un (a * n) ++ (un n ++ r19) = un ((a + 1) * n) ++ r19 := by
      simp only [un, ← List.append_assoc, ← List.replicate_add, hm]
    rw [hu]

/-- The multiplication step: `mulStep` replaces the unary number `a` on stack `18` by `a * n`,
where `n` is the unary number on stack `17`; the space needed is the size of the stacks `0`, `1`,
`3`, `7` and `17` plus `a` and `a * n`. -/
theorem exec_mulStep (x eL a3 c7 : BitString) (n a : ℕ) :
    Exec mulStep (istk x eL a3 c7 (un n) (un a) [] [])
      (istk x eL a3 c7 (un n) (un (a * n)) [] [])
      (x.length + eL.length + a3.length + c7.length + n + a + a * n) := by
  have h1 := exec_mulLoop x eL a3 c7 n
    (x.length + eL.length + a3.length + c7.length + n + a + a * n) a []
    (by simp only [List.length_nil]; omega)
  rw [List.append_nil] at h1
  have h2 := Stmt.exec_moveAll (k := 21) (r := 19) (r' := 18) (by decide) (un (a * n))
    (istk x eL a3 c7 (un n) [] (un (a * n)) []) rfl
  have hr : (un (a * n)).reverse = un (a * n) := List.reverse_replicate
  rw [show (istk x eL a3 c7 (un n) [] (un (a * n)) []) 18 = [] from rfl, List.append_nil,
    hr] at h2
  refine .seq h1 (Stmt.exec_of_eq (h2.mono h1.space_le.2) ?_)
  funext j; fin_cases j <;> rfl

/-- For `i ≤ e` the power `n ^ i` is at most `n ^ e + 1`; the `+ 1` covers `n = 0`, where
`0 ^ 0 = 1`. -/
theorem pow_le_pow_add_one (n : ℕ) {i e : ℕ} (h : i ≤ e) : n ^ i ≤ n ^ e + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases i with _ | i
    · simp
    · simp
  · exact (Nat.pow_le_pow_right hn h).trans (Nat.le_succ _)

/-- Repeated multiplication: if `i + j ≤ e`, then `j` runs of `mulStep` take the unary number
`n ^ i` on stack `18` to `n ^ (i + j)`, while stack `17` keeps the unary number `n`; the space
needed is the size of the other stacks plus `n` and `2 * (n ^ e + 1)`. -/
theorem exec_mulSteps (x eL a3 c7 : BitString) (n e : ℕ) : ∀ (j i : ℕ), i + j ≤ e →
    Exec (Stmt.seqs (List.replicate j mulStep)) (istk x eL a3 c7 (un n) (un (n ^ i)) [] [])
      (istk x eL a3 c7 (un n) (un (n ^ (i + j))) [] [])
      (x.length + eL.length + a3.length + c7.length + n + 2 * (n ^ e + 1))
  | 0, i, h => by
    have := pow_le_pow_add_one n (i := i) (e := e) (by omega)
    refine .skip ?_
    simp only [istk_space, length_un, List.length_nil]
    omega
  | j + 1, i, h => by
    have h1i := pow_le_pow_add_one n (i := i) (e := e) (by omega)
    have h2i := pow_le_pow_add_one n (i := i + 1) (e := e) (by omega)
    have hp : n ^ i * n = n ^ (i + 1) := (pow_succ n i).symm
    have h1 := (exec_mulStep x eL a3 c7 n (n ^ i)).mono
      (S' := x.length + eL.length + a3.length + c7.length + n + 2 * (n ^ e + 1)) (by omega)
    rw [hp] at h1
    have h2 := exec_mulSteps x eL a3 c7 n e j (i + 1) (by omega)
    rw [show i + 1 + j = i + (j + 1) by omega] at h2
    exact .seq h1 h2

/-- The initialisation: load the tape, then build the unary clock `|x| ^ e + e` on `7`. -/
def initStmt (e : ℕ) : Stmt 21 :=
  Stmt.seqs [loadStmt, .push 18 true, Stmt.seqs (List.replicate e mulStep),
    Stmt.pushList 18 (un e), Stmt.moveAll 18 7, Stmt.clear 17]

/-- The initialisation: from the input `x` on stack `0` and the oracle code `eL` on stack `1`,
`initStmt e` reaches the simulation stacks `stk` with the tape `x.map some`, state `0`, empty query
buffer and record, and the unary clock `clock e x.length` on stack `7`. -/
theorem exec_init (e : ℕ) (x eL : BitString) :
    Exec (initStmt e) (Function.update (Function.update (fun _ => []) 0 x) 1 eL)
      (stk x eL (x.map some) [] 0 [] (clock e x.length) [])
      (eL.length + 8 * (x.length + clock e x.length + 1)) := by
  rw [istk_start, ← istk_end]
  have hc : clock e x.length = x.length ^ e + e := rfl
  have hL := length_encCells_map_some x
  have hload := exec_load x eL
  have hpush : Exec (.push 18 true) (istk x eL (encCells (x.map some)) [] (un x.length) [] [] [])
      (istk x eL (encCells (x.map some)) [] (un x.length) (un (x.length ^ 0)) [] [])
      (eL.length + 8 * (x.length + clock e x.length + 1)) :=
    exec_push_eq (by simp only [istk_space, length_un, List.length_nil]; omega)
      (by funext j; fin_cases j <;> rfl)
  have hmul := exec_mulSteps x eL (encCells (x.map some)) [] x.length e e 0 (by omega)
  rw [Nat.zero_add] at hmul
  have hpl := Stmt.exec_pushList (k := 21) 18 (un e)
    (istk x eL (encCells (x.map some)) [] (un x.length) (un (x.length ^ e)) [] [])
  have hu : un e ++ un (x.length ^ e) = un (clock e x.length) := by
    rw [hc, un, un, un, ← List.replicate_add, Nat.add_comm]
  rw [show (istk x eL (encCells (x.map some)) [] (un x.length) (un (x.length ^ e)) [] []) 18 =
    un (x.length ^ e) from rfl, hu] at hpl
  have hpl' : Exec (Stmt.pushList 18 (un e))
      (istk x eL (encCells (x.map some)) [] (un x.length) (un (x.length ^ e)) [] [])
      (istk x eL (encCells (x.map some)) [] (un x.length) (un (clock e x.length)) [] [])
      (eL.length + 8 * (x.length + clock e x.length + 1)) := by
    refine Stmt.exec_of_eq (hpl.mono ?_) ?_
    · simp only [istk_space, length_un, List.length_nil]; omega
    · funext j; fin_cases j <;> rfl
  have hmv := Stmt.exec_moveAll (k := 21) (r := 18) (r' := 7) (by decide) (un (clock e x.length))
    (istk x eL (encCells (x.map some)) [] (un x.length) (un (clock e x.length)) [] []) rfl
  have hr : (un (clock e x.length)).reverse = un (clock e x.length) := List.reverse_replicate
  rw [show (istk x eL (encCells (x.map some)) [] (un x.length) (un (clock e x.length)) [] []) 7 =
    [] from rfl, List.append_nil, hr] at hmv
  have hmv' : Exec (Stmt.moveAll 18 7)
      (istk x eL (encCells (x.map some)) [] (un x.length) (un (clock e x.length)) [] [])
      (istk x eL (encCells (x.map some)) (un (clock e x.length)) (un x.length) [] [] [])
      (eL.length + 8 * (x.length + clock e x.length + 1)) := by
    refine Stmt.exec_of_eq (hmv.mono ?_) ?_
    · simp only [istk_space, length_un, List.length_nil]; omega
    · funext j; fin_cases j <;> rfl
  have hcl := Stmt.exec_clear (k := 21) 17 (un x.length)
    (istk x eL (encCells (x.map some)) (un (clock e x.length)) (un x.length) [] [] []) rfl
  have hcl' : Exec (Stmt.clear 17)
      (istk x eL (encCells (x.map some)) (un (clock e x.length)) (un x.length) [] [] [])
      (istk x eL (encCells (x.map some)) (un (clock e x.length)) [] [] [] [])
      (eL.length + 8 * (x.length + clock e x.length + 1)) := by
    refine Stmt.exec_of_eq (hcl.mono ?_) ?_
    · simp only [istk_space, length_un, List.length_nil]; omega
    · funext j; fin_cases j <;> rfl
  refine .seq (hload.mono (by omega)) (.seq hpush (.seq (hmul.mono ?_) (.seq hpl'
    (.seq hmv' (.seq hcl' (.skip ?_))))))
  · simp only [List.length_nil]; omega
  · simp only [istk_space, length_un, List.length_nil]; omega

/-- The code of the empty list of cells is empty. -/
theorem encCells_nil : encCells [] = [] := rfl

/-- The code of `a :: cs` is the code of the cell `a` followed by the code of `cs`. -/
theorem encCells_cons (a : Sym) (cs : List Sym) :
    encCells (a :: cs) = encCell a ++ encCells cs := by
  simp [encCells]

/-- The code of a single cell has length at most `2`. -/
theorem length_encCell_le (a : Sym) : (encCell a).length ≤ 2 := by
  cases a <;> simp [encCell]

/-- Dropping the first cell of a list of cells does not make its code longer. -/
theorem length_encCells_tail (cs : List Sym) :
    (encCells cs.tail).length ≤ (encCells cs).length := by
  cases cs <;> simp [encCells_cons]

/-- The unary code of `n + 1` is a digit `true` followed by the unary code of `n`. -/
theorem un_succ (n : ℕ) : un (n + 1) = true :: un n := by simp [un, List.replicate_succ]

/-- Push the code of a cell on `r` (it becomes the first cell). -/
def pushCell (r : Fin 21) (a : Sym) : Stmt 21 := Stmt.pushList r (encCell a)

/-- Read and remove the first cell of the code on `r` (an empty stack reads as a blank), then run
`f` on it. -/
def readCell (r : Fin 21) (f : Sym → Stmt 21) : Stmt 21 :=
  .ite r Stmt.isTrue (.seq (.pop r) (Stmt.caseBit r fun b => .seq (.pop r) (f (some b))))
    (.seq (.pop r) (f none))

/-- Dispatch on a unary counter on `r` (consumed): run the `n`-th statement of the list. -/
def switchU {k : ℕ} (r : Fin k) : List (Stmt k) → Stmt k
  | [] => .skip
  | s :: l => .ite r Stmt.isTrue (.seq (.pop r) (switchU r l)) s

/-- Reading a cell: if stack `r` holds the code of the cells `cs`, then `readCell r f` removes the
code of the first cell (a blank if `cs` is empty) and behaves as `f (cs.headD none)` on the stacks
where `r` holds the code of `cs.tail`. -/
theorem exec_readCell {r : Fin 21} {f : Sym → Stmt 21} {σ σ' : Stacks 21} {S : ℕ}
    {cs : List Sym} (hr : σ r = encCells cs) (hS : σ.space ≤ S)
    (h : Exec (f (cs.headD none)) (Function.update σ r (encCells cs.tail)) σ' S) :
    Exec (readCell r f) σ σ' S := by
  unfold readCell
  rcases cs with _ | ⟨a, cs⟩
  · have hr' : σ r = [] := hr
    refine .iteF (by simp [hr', Stmt.isTrue]) (.seq (Exec.pop hS) ?_)
    rw [hr']; exact h
  · rcases a with _ | b
    · have hr' : σ r = false :: encCells cs := by rw [hr, encCells_cons]; rfl
      refine .iteF (by simp [hr', Stmt.isTrue]) (.seq (Exec.pop hS) ?_)
      rw [hr']; exact h
    · have hr' : σ r = true :: b :: encCells cs := by rw [hr, encCells_cons]; rfl
      have e1 := Exec.pop (r := r) (σ := σ) (S := S) hS
      rw [hr'] at e1
      refine .iteT (by simp [hr', Stmt.isTrue]) (.seq e1 ?_)
      rw [Stmt.exec_caseBit (b := b) (l := encCells cs) (by simp)]
      have e2 := Exec.pop (r := r) (σ := Function.update σ r (b :: encCells cs)) (S := S)
        e1.space_le.2
      simp only [Function.update_self, List.tail_cons, Function.update_idem] at e2
      exact .seq e2 h

/-- Dispatch on a unary counter: if stack `r` holds the unary number `n < l.length`, then
`switchU r l` empties `r` and runs the `n`-th statement `l[n]` of the list `l`. -/
theorem exec_switchU {k : ℕ} {r : Fin k} : ∀ (l : List (Stmt k)) (n : ℕ) (hn : n < l.length)
    {σ σ' : Stacks k} {S : ℕ}, σ r = un n → σ.space ≤ S →
    Exec l[n] (Function.update σ r []) σ' S → Exec (switchU r l) σ σ' S
  | [], n, hn, _, _, _, _, _, _ => absurd hn (by simp)
  | s :: l, 0, _, σ, σ', S, hr, hS, h => by
    have hr' : σ r = [] := hr
    refine .iteF (by simp [hr', Stmt.isTrue]) ?_
    have e : Function.update σ r [] = σ := by rw [← hr', Function.update_eq_self]
    rw [e] at h
    exact h
  | s :: l, n + 1, hn, σ, σ', S, hr, hS, h => by
    have hr' : σ r = true :: un n := by rw [hr, un_succ]
    have e1 := Exec.pop (r := r) (σ := σ) (S := S) hS
    rw [hr'] at e1
    refine .iteT (by simp [hr', Stmt.isTrue]) (.seq e1 ?_)
    refine exec_switchU l n (by simpa using hn) (by simp) e1.space_le.2 ?_
    simpa using h

/-- The stacks of `memTest`: query `8`, oracle code `1`, flag `9`, work stacks `10`–`15`. -/
def memMap : Fin 9 → Fin 21 := ![8, 1, 9, 10, 11, 12, 13, 14, 15]

/-- The assignment `memMap` of the stacks of `memTest` to the stacks of the simulation is
injective. -/
theorem memMap_injective : Function.Injective memMap := by decide

/-- The membership test inlined on the stacks of the simulation: with the query `buf` on stack `8`,
the oracle code `Stacks.encList L` on stack `1` and the stacks `9`–`15` empty, the statement
`memTest.rename memMap` puts the verdict `decide (buf ∈ L)` on stack `9`. -/
theorem exec_memSim {x : BitString} {L : List BitString} {rs ls : List Sym} {clk : ℕ}
    {qs : BitString} (buf : BitString) :
    Exec (Stmt.memTest.rename memMap)
      (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk qs) 8 buf)
      (Function.update (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk qs) 8 buf) 9
        [decide (buf ∈ L)])
      (Stacks.space (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk qs) 8 buf) +
        (Stacks.encList L).length + 2) := by
  generalize hτ : Function.update (stk x (Stacks.encList L) rs ls 0 [] clk qs) 8 buf = τ
  obtain ⟨h1, h8, h9, h10, h11, h12, h13, h14, h15⟩ : τ 1 = Stacks.encList L ∧ τ 8 = buf ∧
      τ 9 = [] ∧ τ 10 = [] ∧ τ 11 = [] ∧ τ 12 = [] ∧ τ 13 = [] ∧ τ 14 = [] ∧
      τ 15 = [] := by
    subst hτ; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [← h8]
  have h := Stmt.exec_memTest (σ := fun r => τ (memMap r)) (L := L) h1 h9 h10 h11 h12 h13 h14 h15
  have h' := Exec.rename_of_comp memMap_injective h
  have e1 : Function.extend memMap (Function.update (fun r => τ (memMap r)) 2
      [decide (τ (memMap 0) ∈ L)]) τ = Function.update τ 9 [decide (τ 8 ∈ L)] := by
    rw [← Stacks.update_extend memMap_injective, Stacks.extend_comp_self memMap_injective]
    rfl
  have e2 : Stacks.space (fun r => τ (memMap r)) + Stacks.rest memMap τ = Stacks.space τ := by
    rw [← Stacks.space_extend memMap_injective, Stacks.extend_comp_self memMap_injective]
  rw [e1] at h'
  exact h'.mono (by omega)

/-- Pushing the code of the cell `a` on stack `3` puts `a` in front of the right part `rs` of the
tape, provided `S` exceeds the current space by at least `2`. -/
theorem exec_pushCell3 {x eL : BitString} {rs ls : List Sym} {q : ℕ} {rb : BitString} {clk : ℕ}
    {qs : BitString} (a : Sym) {S : ℕ} (hS : (stk x eL rs ls q rb clk qs).space + 2 ≤ S) :
    Exec (pushCell 3 a) (stk x eL rs ls q rb clk qs) (stk x eL (a :: rs) ls q rb clk qs) S := by
  have h := Stmt.exec_pushList 3 (encCell a) (stk x eL rs ls q rb clk qs)
  refine Stmt.exec_of_eq (h.mono (by have := length_encCell_le a; omega)) ?_
  funext j
  fin_cases j <;> rfl

/-- Pushing the code of the cell `a` on stack `4` puts `a` in front of the left part `ls` of the
tape, provided `S` exceeds the current space by at least `2`. -/
theorem exec_pushCell4 {x eL : BitString} {rs ls : List Sym} {q : ℕ} {rb : BitString} {clk : ℕ}
    {qs : BitString} (a : Sym) {S : ℕ} (hS : (stk x eL rs ls q rb clk qs).space + 2 ≤ S) :
    Exec (pushCell 4 a) (stk x eL rs ls q rb clk qs) (stk x eL rs (a :: ls) q rb clk qs) S := by
  have h := Stmt.exec_pushList 4 (encCell a) (stk x eL rs ls q rb clk qs)
  refine Stmt.exec_of_eq (h.mono (by have := length_encCell_le a; omega)) ?_
  funext j
  fin_cases j <;> rfl

/-- Pushing the unary code of `q` on the empty state stack `5` makes `q` the state of the
simulation stacks, provided `S` exceeds the current space by at least `q`. -/
theorem exec_pushState {x eL : BitString} {rs ls : List Sym} {rb : BitString} {clk : ℕ}
    {qs : BitString} (q : ℕ) {S : ℕ} (hS : (stk x eL rs ls 0 rb clk qs).space + q ≤ S) :
    Exec (Stmt.pushList 5 (un q)) (stk x eL rs ls 0 rb clk qs) (stk x eL rs ls q rb clk qs) S := by
  have h := Stmt.exec_pushList 5 (un q) (stk x eL rs ls 0 rb clk qs)
  refine Stmt.exec_of_eq (h.mono (by simp only [un, List.length_replicate]; omega)) ?_
  funext j
  fin_cases j <;> first | rfl | simp [stk, un]

/-- Pushing the bit `b` on stack `6` puts `b` in front of the reversed query buffer `rb`. -/
theorem exec_pushBuf {x eL : BitString} {rs ls : List Sym} {q : ℕ} {rb : BitString} {clk : ℕ}
    {qs : BitString} (b : Bool) {S : ℕ} (hS : (stk x eL rs ls q rb clk qs).space + 1 ≤ S) :
    Exec (.push 6 b) (stk x eL rs ls q rb clk qs) (stk x eL rs ls q (b :: rb) clk qs) S := by
  refine Stmt.exec_of_eq (Exec.push hS) ?_
  funext j
  fin_cases j <;> rfl

/-- Reading from the right part of the tape: `readCell 3 f` removes the first cell of `rs` (a blank
if `rs` is empty) and continues as `f (rs.headD none)` on the stacks with right part `rs.tail`. -/
theorem exec_readCell3 {x eL : BitString} {rs ls : List Sym} {q : ℕ} {rb : BitString} {clk : ℕ}
    {qs : BitString} {f : Sym → Stmt 21} {σ' : Stacks 21} {S : ℕ}
    (hS : (stk x eL rs ls q rb clk qs).space ≤ S)
    (h : Exec (f (rs.headD none)) (stk x eL rs.tail ls q rb clk qs) σ' S) :
    Exec (readCell 3 f) (stk x eL rs ls q rb clk qs) σ' S := by
  refine exec_readCell (cs := rs) rfl hS ?_
  have e : Function.update (stk x eL rs ls q rb clk qs) 3 (encCells rs.tail) =
      stk x eL rs.tail ls q rb clk qs := by
    funext j; fin_cases j <;> rfl
  rw [e]; exact h

/-- Reading from the left part of the tape: `readCell 4 f` removes the nearest cell of `ls` (a blank
if `ls` is empty) and continues as `f (ls.headD none)` on the stacks with left part `ls.tail`. -/
theorem exec_readCell4 {x eL : BitString} {rs ls : List Sym} {q : ℕ} {rb : BitString} {clk : ℕ}
    {qs : BitString} {f : Sym → Stmt 21} {σ' : Stacks 21} {S : ℕ}
    (hS : (stk x eL rs ls q rb clk qs).space ≤ S)
    (h : Exec (f (ls.headD none)) (stk x eL rs ls.tail q rb clk qs) σ' S) :
    Exec (readCell 4 f) (stk x eL rs ls q rb clk qs) σ' S := by
  refine exec_readCell (cs := ls) rfl hS ?_
  have e : Function.update (stk x eL rs ls q rb clk qs) 4 (encCells ls.tail) =
      stk x eL rs ls.tail q rb clk qs := by
    funext j; fin_cases j <;> rfl
  rw [e]; exact h

/-- Answering a query: the buffer (reversed on `6`) is moved to `8`, looked up in the oracle code
on `1`, and the new state is pushed according to the answer. -/
def askStmt (c : OTMCode) (qy qn : Fin c.k) : Stmt 21 :=
  Stmt.seqs [Stmt.moveAll 6 8, Stmt.memTest.rename memMap, Stmt.clear 8,
    Stmt.caseBit 9 fun g => .seq (.pop 9) (Stmt.pushList 5 (un (if g then qy else qn).val))]

/-- Answering a query: with the query `buf` (stored reversed on stack `6`) and the oracle code
`Stacks.encList L`, `askStmt c qy qn` empties the buffer and makes the state `qy` if `buf ∈ L` and
`qn` otherwise, leaving the other simulation stacks unchanged. -/
theorem exec_ask (c : OTMCode) (qy qn : Fin c.k) {x : BitString} {L : List BitString}
    {rs ls : List Sym} {clk : ℕ} (buf : BitString) {S : ℕ}
    (hS : (stk x (Stacks.encList L) rs ls 0 buf.reverse clk []).space +
      (Stacks.encList L).length + c.k + 2 ≤ S) :
    Exec (askStmt c qy qn) (stk x (Stacks.encList L) rs ls 0 buf.reverse clk [])
      (stk x (Stacks.encList L) rs ls (if buf ∈ L then qy else qn).val [] clk []) S := by
  have e1 := Stmt.exec_moveAll (by decide : (6 : Fin 21) ≠ 8)
    ((stk x (Stacks.encList L) rs ls 0 buf.reverse clk []) 6)
    (stk x (Stacks.encList L) rs ls 0 buf.reverse clk []) rfl
  have hσ1 : Function.update (Function.update (stk x (Stacks.encList L) rs ls 0 buf.reverse clk [])
      6 []) 8 (((stk x (Stacks.encList L) rs ls 0 buf.reverse clk []) 6).reverse ++
        (stk x (Stacks.encList L) rs ls 0 buf.reverse clk []) 8) =
      Function.update (stk x (Stacks.encList L) rs ls 0 [] clk []) 8 buf := by
    funext j; fin_cases j <;> first | rfl | simp [stk]
  rw [hσ1] at e1
  have e2 := exec_memSim (x := x) (L := L) (rs := rs) (ls := ls) (clk := clk) (qs := []) buf
  have e3 := Stmt.exec_clear 8 _ (Function.update (Function.update
    (stk x (Stacks.encList L) rs ls 0 [] clk []) 8 buf) 9 [decide (buf ∈ L)]) rfl
  have hσ3 : Function.update (Function.update (Function.update
      (stk x (Stacks.encList L) rs ls 0 [] clk []) 8 buf) 9 [decide (buf ∈ L)]) 8 [] =
      Function.update (stk x (Stacks.encList L) rs ls 0 [] clk []) 9 [decide (buf ∈ L)] := by
    funext j; fin_cases j <;> rfl
  rw [hσ3] at e3
  have sp0 := stk_space x (Stacks.encList L) rs ls 0 buf.reverse clk []
  have sp1 := stk_space x (Stacks.encList L) rs ls 0 [] clk []
  simp only [List.length_reverse, List.length_nil, add_zero] at sp0 sp1
  have hq := (if buf ∈ L then qy else qn).isLt
  have e4 : Exec (Stmt.caseBit 9 fun g => .seq (.pop 9)
      (Stmt.pushList 5 (un (if g then qy else qn).val)))
      (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk []) 9 [decide (buf ∈ L)])
      (stk x (Stacks.encList L) rs ls (if buf ∈ L then qy else qn).val [] clk []) S := by
    rw [Stmt.exec_caseBit (b := decide (buf ∈ L)) (l := []) rfl]
    have p1 := Exec.pop (r := 9)
      (σ := Function.update (stk x (Stacks.encList L) rs ls 0 [] clk []) 9 [decide (buf ∈ L)])
      (S := S) (e3.space_le.2.trans (e2.space_le.2.trans (by
        have := e1.space_le.2; omega)))
    have hp : Function.update (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk []) 9
        [decide (buf ∈ L)]) 9 ((Function.update (stk x (Stacks.encList L) rs ls 0 [] clk []) 9
          [decide (buf ∈ L)]) 9).tail = stk x (Stacks.encList L) rs ls 0 [] clk [] := by
      funext j; fin_cases j <;> rfl
    rw [hp] at p1
    have p2 := exec_pushState (x := x) (eL := Stacks.encList L) (rs := rs) (ls := ls) (rb := [])
      (clk := clk) (qs := []) (if buf ∈ L then qy else qn).val (S := S)
      (by omega)
    refine .seq p1 ?_
    by_cases hb : buf ∈ L
    · simpa [hb] using p2
    · simpa [hb] using p2
  refine .seq (e1.mono (by omega)) (.seq (e2.mono ?_) (.seq (e3.mono ?_) (.seq e4
    (.skip ?_))))
  · have := e1.space_le.2; omega
  · have := e1.space_le.2; have := e2.space_le.2; omega
  · have := e4.space_le.2; exact this

/-- The tape `τ` with the head at `h` is `rs` from the head on and `ls` (nearest cell first) to
the left of the head. -/
def TapeRep (τ : ℤ → Sym) (h : ℤ) (rs ls : List Sym) : Prop :=
  (∀ i : ℕ, τ (h + i) = rs.getD i none) ∧ ∀ i : ℕ, τ (h - 1 - i) = ls.getD i none

/-- The `i`-th entry (default `none`) of the tail of a list is the `(i + 1)`-th entry of the
list. -/
theorem getD_tail (l : List Sym) (i : ℕ) : l.tail.getD i none = l.getD (i + 1) none := by
  cases l <;> simp

/-- Making the first cell explicit, `l.headD none :: l.tail` (a blank for the empty list), makes
the code of a list of cells longer by at most `1`. -/
theorem length_encCells_headD_tail (l : List Sym) :
    (encCells (l.headD none :: l.tail)).length ≤ (encCells l).length + 1 := by
  cases l <;> simp [encCells_cons, encCell, encCells_nil]

/-- Making the scanned cell explicit, `rs.headD none :: rs.tail`, does not change the tape
represented by the right part `rs`. -/
theorem tapeRep_same {τ : ℤ → Sym} {h : ℤ} {rs ls : List Sym} (hr : TapeRep τ h rs ls) :
    TapeRep τ h (rs.headD none :: rs.tail) ls := by
  refine ⟨fun i => ?_, hr.2⟩
  rw [hr.1 i]
  cases rs <;> cases i <;> simp

/-- Writing `a` and staying: the tape updated at the head `h` with `a` is represented by the right
part `a :: rs.tail` and the same left part `ls`. -/
theorem tapeRep_stay {τ : ℤ → Sym} {h : ℤ} {rs ls : List Sym} (hr : TapeRep τ h rs ls)
    (a : Sym) : TapeRep (Function.update τ h a) h (a :: rs.tail) ls := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · cases i with
    | zero => simp
    | succ j =>
      rw [Function.update_of_ne (by push_cast; omega), hr.1, List.getD_cons_succ, getD_tail]
  · rw [Function.update_of_ne (by omega), hr.2]

/-- Writing `a` and moving right: the tape updated at the head `h` with `a`, with the head at
`h + 1`, is represented by the right part `rs.tail` and the left part `a :: ls`. -/
theorem tapeRep_right {τ : ℤ → Sym} {h : ℤ} {rs ls : List Sym} (hr : TapeRep τ h rs ls)
    (a : Sym) : TapeRep (Function.update τ h a) (h + 1) rs.tail (a :: ls) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [Function.update_of_ne (by omega), getD_tail, ← hr.1]; congr 1; push_cast; ring
  · cases i with
    | zero => simp
    | succ j =>
      rw [Function.update_of_ne (by push_cast; omega), List.getD_cons_succ, ← hr.2]
      congr 1; push_cast; ring

/-- Writing `a` and moving left: the tape updated at the head `h` with `a`, with the head at
`h - 1`, is represented by the right part `ls.headD none :: a :: rs.tail` and the left part
`ls.tail`. -/
theorem tapeRep_left {τ : ℤ → Sym} {h : ℤ} {rs ls : List Sym} (hr : TapeRep τ h rs ls)
    (a : Sym) :
    TapeRep (Function.update τ h a) (h - 1) (ls.headD none :: a :: rs.tail) ls.tail := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · match i with
    | 0 =>
      rw [Function.update_of_ne (by omega)]
      have := hr.2 0
      simp only [Nat.cast_zero, sub_zero, add_zero] at this ⊢
      rw [this]; cases ls <;> rfl
    | 1 => simp
    | j + 2 =>
      rw [Function.update_of_ne (by push_cast; omega), List.getD_cons_succ, List.getD_cons_succ,
        getD_tail, ← hr.1]
      congr 1; push_cast; ring
  · rw [Function.update_of_ne (by omega), getD_tail, ← hr.2]; congr 1; push_cast; ring

/-- The action of the state `q` on the scanned cell `a` (already removed from the right part;
the state stack is empty): perform the step of the machine and push the new state. -/
def actStmt (c : OTMCode) (q : Fin c.k) (a : Sym) : Stmt 21 :=
  if q = c.accept ∨ q = c.reject then .seq (pushCell 3 a) (Stmt.pushList 5 (un q.val))
  else
    match c.δ q a with
    | .step q' a' .stay => .seq (pushCell 3 a') (Stmt.pushList 5 (un q'.val))
    | .step q' a' .right => .seq (pushCell 4 a') (Stmt.pushList 5 (un q'.val))
    | .step q' a' .left =>
      .seq (pushCell 3 a') (.seq (readCell 4 (pushCell 3)) (Stmt.pushList 5 (un q'.val)))
    | .push q' b => .seq (pushCell 3 a) (.seq (.push 6 b) (Stmt.pushList 5 (un q'.val)))
    | .ask qy qn => .seq (pushCell 3 a) (askStmt c qy qn)

/-- One step of the machine `c`: dispatch on the state, read the scanned cell, act. -/
def stepStmt (c : OTMCode) : Stmt 21 :=
  switchU 5 (List.ofFn fun q : Fin c.k => readCell 3 (actStmt c q))

/-- One simulated step: if `rs`, `ls` represent the tape of the configuration `cfg` and the space
bound `S` is large enough, then `stepStmt c` takes the stacks of `cfg` to the stacks of the next
configuration `step c.toOTM {z | z ∈ L} cfg`, for some representation `rs'`, `ls'` of its tape
whose codes together grow by at most `4`. -/
theorem exec_step (c : OTMCode) (L : List BitString) (x : BitString) (clk : ℕ)
    (cfg : Config c.toOTM) (rs ls : List Sym) (hrep : TapeRep cfg.tape cfg.head rs ls) (S : ℕ)
    (hS : x.length + 2 * (Stacks.encList L).length + (encCells rs).length +
      (encCells ls).length + c.k + cfg.buf.length + clk + 8 ≤ S) :
    ∃ rs' ls', TapeRep (step c.toOTM {z | z ∈ L} cfg).tape (step c.toOTM {z | z ∈ L} cfg).head
        rs' ls' ∧
      (encCells rs').length + (encCells ls').length ≤
        (encCells rs).length + (encCells ls).length + 4 ∧
      Exec (stepStmt c)
        (stk x (Stacks.encList L) rs ls (cfg.q : Fin c.k).val cfg.buf.reverse clk [])
        (stk x (Stacks.encList L) rs' ls' ((step c.toOTM {z | z ∈ L} cfg).q : Fin c.k).val
          (step c.toOTM {z | z ∈ L} cfg).buf.reverse clk []) S := by
  have ha : cfg.tape cfg.head = rs.headD none := by
    have := hrep.1 0
    simp only [Nat.cast_zero, add_zero] at this
    rw [this]; cases rs <;> rfl
  have htl := length_encCells_tail rs
  have hht := length_encCells_headD_tail rs
  have hqk := (cfg.q : Fin c.k).isLt
  have key : ∀ σ', Exec (actStmt c cfg.q (rs.headD none))
      (stk x (Stacks.encList L) rs.tail ls 0 cfg.buf.reverse clk []) σ' S →
      Exec (stepStmt c)
        (stk x (Stacks.encList L) rs ls (cfg.q : Fin c.k).val cfg.buf.reverse clk []) σ' S := by
    intro σ' h
    refine exec_switchU _ (cfg.q : Fin c.k).val (by simpa using hqk) rfl
      (by rw [stk_space]; simp only [List.length_reverse, List.length_nil]; omega) ?_
    rw [List.getElem_ofFn]
    have e : Function.update (stk x (Stacks.encList L) rs ls (cfg.q : Fin c.k).val
        cfg.buf.reverse clk []) 5 [] =
        stk x (Stacks.encList L) rs ls 0 cfg.buf.reverse clk [] := by
      funext j; fin_cases j <;> rfl
    rw [e]
    exact exec_readCell3
      (by rw [stk_space]; simp only [List.length_reverse, List.length_nil]; omega) h
  by_cases hH : (cfg.q : Fin c.k) = c.accept ∨ (cfg.q : Fin c.k) = c.reject
  · have hst : step c.toOTM {z | z ∈ L} cfg = cfg := step_of_halted _ _ _ hH
    rw [hst]
    refine ⟨rs.headD none :: rs.tail, ls, tapeRep_same hrep, by omega, key _ ?_⟩
    unfold actStmt
    split_ifs with h'
    swap; · exact (h' hH).elim
    refine .seq (exec_pushCell3 _ ?_) (exec_pushState _ ?_)
    · rw [stk_space]; simp only [List.length_reverse, List.length_nil]; omega
    · rw [stk_space]; simp only [List.length_reverse, List.length_nil]; omega
  · have hH' : ¬ Halted c.toOTM cfg := hH
    have hsp := fun rs' ls' q' rb => stk_space x (Stacks.encList L) rs' ls' q' rb clk []
    cases hδ : c.δ cfg.q (rs.headD none) with
    | step q' a' m =>
      have hq' := q'.isLt
      have ha' := length_encCell_le a'
      unfold step
      rw [ite_eq_right hH', show c.toOTM.δ cfg.q (cfg.tape cfg.head) = Act.step q' a' m by
        rw [ha]; exact hδ]
      dsimp only
      cases m with
      | stay =>
        refine ⟨a' :: rs.tail, ls, tapeRep_stay hrep a', ?_, key _ ?_⟩
        · simp only [encCells_cons, List.length_append]; omega
        · unfold actStmt
          split_ifs with h'
          · exact (hH h').elim
          rw [hδ]
          refine .seq (exec_pushCell3 _ ?_) (exec_pushState _ ?_)
          · rw [hsp]; simp only [List.length_reverse, List.length_nil]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append, List.length_reverse,
              List.length_nil]; omega
      | right =>
        refine ⟨rs.tail, a' :: ls, tapeRep_right hrep a', ?_, key _ ?_⟩
        · simp only [encCells_cons, List.length_append]; omega
        · unfold actStmt
          split_ifs with h'
          · exact (hH h').elim
          rw [hδ]
          refine .seq (exec_pushCell4 _ ?_) (exec_pushState _ ?_)
          · rw [hsp]; simp only [List.length_reverse, List.length_nil]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append, List.length_reverse,
              List.length_nil]; omega
      | left =>
        have hlt := length_encCells_tail ls
        have hlh := length_encCell_le (ls.headD none)
        have hlht := length_encCells_headD_tail ls
        refine ⟨ls.headD none :: a' :: rs.tail, ls.tail, tapeRep_left hrep a', ?_, key _ ?_⟩
        · simp only [encCells_cons, List.length_append] at hlht ⊢; omega
        · unfold actStmt
          split_ifs with h'
          · exact (hH h').elim
          rw [hδ]
          refine .seq (exec_pushCell3 _ ?_) (.seq (exec_readCell4 ?_ (exec_pushCell3 _ ?_))
            (exec_pushState _ ?_))
          · rw [hsp]; simp only [List.length_reverse, List.length_nil]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append, List.length_reverse,
              List.length_nil]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append, List.length_reverse,
              List.length_nil]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append, List.length_reverse,
              List.length_nil] at hlht ⊢; omega
    | push q' b =>
      have hq' := q'.isLt
      unfold step
      rw [ite_eq_right hH', show c.toOTM.δ cfg.q (cfg.tape cfg.head) = Act.push q' b by
        rw [ha]; exact hδ]
      dsimp only
      refine ⟨rs.headD none :: rs.tail, ls, tapeRep_same hrep, by omega, key _ ?_⟩
      unfold actStmt
      split_ifs with h'
      · exact (hH h').elim
      rw [hδ]
      have hrb : (cfg.buf ++ [b]).reverse = b :: cfg.buf.reverse := by simp
      rw [hrb]
      refine .seq (exec_pushCell3 _ ?_) (.seq (exec_pushBuf b ?_) (exec_pushState _ ?_))
      · rw [hsp]; simp only [List.length_reverse, List.length_nil]; omega
      · rw [hsp]; simp only [List.length_reverse, List.length_nil]; omega
      · rw [hsp]; simp only [List.length_reverse, List.length_nil, List.length_cons]; omega
    | ask qy qn =>
      unfold step
      rw [ite_eq_right hH', show c.toOTM.δ cfg.q (cfg.tape cfg.head) = Act.ask qy qn by
        rw [ha]; exact hδ]
      dsimp only
      have hex : ∀ q'' : Fin c.k, q'' = (if cfg.buf ∈ L then qy else qn) →
          Exec (actStmt c cfg.q (rs.headD none))
            (stk x (Stacks.encList L) rs.tail ls 0 cfg.buf.reverse clk [])
            (stk x (Stacks.encList L) (rs.headD none :: rs.tail) ls q''.val [] clk []) S := by
        intro q'' hq''
        unfold actStmt
        split_ifs with h'
        · exact (hH h').elim
        rw [hδ]
        have e := exec_ask c qy qn (x := x) (L := L) (rs := rs.headD none :: rs.tail) (ls := ls)
          (clk := clk) cfg.buf (S := S)
          (by rw [hsp]; simp only [List.length_reverse, List.length_nil]; omega)
        rw [← hq''] at e
        have e0 := exec_pushCell3 (x := x) (eL := Stacks.encList L) (rs := rs.tail) (ls := ls)
          (q := 0) (rb := cfg.buf.reverse) (clk := clk) (qs := []) (rs.headD none) (S := S)
          (by rw [hsp]; simp only [List.length_reverse, List.length_nil]; omega)
        exact .seq e0 e
      refine ⟨rs.headD none :: rs.tail, ls, tapeRep_same hrep, by omega, key _ (hex _ ?_)⟩
      by_cases hb : cfg.buf ∈ L <;> simp [hb]

/-- The initial tape, holding `x` on the cells `0, 1, …` and blanks elsewhere, with the head at
`0`, is represented by the right part `x.map some` and the empty left part. -/
theorem tapeRep_init (x : BitString) :
    TapeRep (fun i : ℤ => if 0 ≤ i then x[i.toNat]? else none) 0 (x.map some) [] := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · simp only [zero_add, Nat.cast_nonneg, ite_true, Int.toNat_natCast]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases x[i]? <;> rfl
  · dsimp only
    rw [ite_eq_right (by omega)]; simp

/-- The main loop: `T` simulated steps, counted down on the clock stack `7`. -/
theorem exec_simLoop (c : OTMCode) (L : List BitString) (x : BitString) (T : ℕ) :
    ∃ rs ls, Exec (.loop 7 Option.isSome (.seq (.pop 7) (stepStmt c)))
      (stk x (Stacks.encList L) (x.map some) [] c.start.val [] T [])
      (stk x (Stacks.encList L) rs ls ((run c.toOTM {z | z ∈ L} x T).q : Fin c.k).val
        (run c.toOTM {z | z ∈ L} x T).buf.reverse 0 [])
      (3 * x.length + 2 * (Stacks.encList L).length + 6 * T + c.k + 9) := by
  set B : Set BitString := {z | z ∈ L} with hB
  set eL := Stacks.encList L with heL
  set S := 3 * x.length + 2 * eL.length + 6 * T + c.k + 9 with hSdef
  let I : Stacks 21 → Prop := fun σ => ∃ t ≤ T, ∃ rs ls,
    TapeRep (run c.toOTM B x t).tape (run c.toOTM B x t).head rs ls ∧
    (encCells rs).length + (encCells ls).length ≤ 2 * x.length + 4 * t ∧
    σ = stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val (run c.toOTM B x t).buf.reverse
      (T - t) []
  have hstep : ∀ σ, I σ → Option.isSome (σ 7).head? = true → ∃ σ',
      Exec (.seq (.pop 7) (stepStmt c)) σ σ' S ∧ I σ' ∧ (σ' 7).length < (σ 7).length := by
    rintro σ ⟨t, ht, rs, ls, hrep, hlen, rfl⟩ hc
    have htT : t < T := by
      by_contra hcon
      have h0 : T - t = 0 := by omega
      have : (stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
          (run c.toOTM B x t).buf.reverse (T - t) []) 7 = [] := by
        change un (T - t) = []; rw [h0]; rfl
      rw [this] at hc; simp at hc
    have hbuf := buf_length_le c.toOTM B x t
    have hqk := ((run c.toOTM B x t).q : Fin c.k).isLt
    have hTt : T - (t + 1) ≤ T := Nat.sub_le _ _
    obtain ⟨rs', ls', hrep', hlen', hex⟩ := exec_step c L x (T - (t + 1)) (run c.toOTM B x t)
      rs ls hrep S (by rw [← heL]; omega)
    have hpop : Exec (.pop 7) (stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
        (run c.toOTM B x t).buf.reverse (T - t) [])
        (stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
        (run c.toOTM B x t).buf.reverse (T - (t + 1)) []) S := by
      have h := Exec.pop (r := 7) (σ := stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
        (run c.toOTM B x t).buf.reverse (T - t) []) (S := S)
        (by rw [stk_space]; simp only [List.length_reverse, List.length_nil]; omega)
      refine Stmt.exec_of_eq h ?_
      have e7 : ((stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
          (run c.toOTM B x t).buf.reverse (T - t) []) 7).tail = un (T - (t + 1)) := by
        change (un (T - t)).tail = un (T - (t + 1))
        simp only [un, List.tail_replicate]; congr 1
      rw [e7]; funext j; fin_cases j <;> rfl
    refine ⟨_, .seq hpop hex, ⟨t + 1, htT, rs', ls', hrep', by omega, rfl⟩, ?_⟩
    change (un (T - (t + 1))).length < (un (T - t)).length
    simp only [length_un]; omega
  have hexit : ∀ σ, I σ → σ.space ≤ S := by
    rintro σ ⟨t, ht, rs, ls, hrep, hlen, rfl⟩
    have hbuf := buf_length_le c.toOTM B x t
    have hqk := ((run c.toOTM B x t).q : Fin c.k).isLt
    rw [stk_space]; simp only [List.length_reverse, List.length_nil]; omega
  have hI0 : I (stk x eL (x.map some) [] c.start.val [] T []) := by
    refine ⟨0, Nat.zero_le _, x.map some, [], tapeRep_init x, ?_, rfl⟩
    rw [length_encCells_map_some]; simp [encCells_nil]
  obtain ⟨σ', hex, ⟨t, ht, rs, ls, hrep, hlen, rfl⟩, hc⟩ :=
    Exec.loop_of_variant I (fun σ => (σ 7).length) S hstep hexit _ hI0
  have htT : t = T := by
    by_contra hcon
    have h0 : un (T - t) = true :: un (T - t - 1) := by
      rw [← un_succ]; congr 1; omega
    have h7 : (stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
        (run c.toOTM B x t).buf.reverse (T - t) []) 7 = un (T - t) := rfl
    rw [h7, h0] at hc; simp at hc
  subst htT
  refine ⟨rs, ls, ?_⟩
  rw [Nat.sub_self] at hex
  exact hex

/-- The verdict bit of a state. -/
def accB (c : OTMCode) (q : Fin c.k) : Bool := decide (q = c.accept)

/-- The verdict bit of a state is `true` exactly when the state is the accepting state. -/
theorem accB_iff (c : OTMCode) (q : Fin c.k) : accB c q = true ↔ q = c.accept := by
  simp [accB]

/-- The simulation statement: initialise, push the start state, run the clocked loop, output the
verdict, and clean up. -/
def simStmt (c : OTMCode) (e : ℕ) : Stmt 21 :=
  Stmt.seqs [initStmt e, Stmt.pushList 5 (un c.start.val),
    .loop 7 Option.isSome (.seq (.pop 7) (stepStmt c)),
    switchU 5 (List.ofFn fun q : Fin c.k => .push 2 (accB c q)),
    Stmt.clear 3, Stmt.clear 4, Stmt.clear 6]

/-- The simulation: from the input `x` on stack `0` and the oracle code `Stacks.encList L` on
stack `1`, `simStmt c e` terminates with the same contents and the verdict bit `accB c q` on
stack `2`, where `q` is the state of `run c.toOTM {z | z ∈ L} x (clock e x.length)`, within space
`(c.k + 10) * (x.length + clock e x.length + (Stacks.encList L).length + 1)`. -/
theorem exec_simStmt (c : OTMCode) (e : ℕ) (x : BitString) (L : List BitString) :
    Exec (simStmt c e) (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList L))
      (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1
        (Stacks.encList L)) 2
        [accB c (run c.toOTM {z | z ∈ L} x (clock e x.length)).q])
      ((c.k + 10) * (x.length + clock e x.length + (Stacks.encList L).length + 1)) := by
  have hCN : c.k + 10 * (x.length + clock e x.length + (Stacks.encList L).length + 1) ≤
      (c.k + 10) * (x.length + clock e x.length + (Stacks.encList L).length + 1) := by
    rw [add_mul]
    have : c.k ≤ c.k * (x.length + clock e x.length + (Stacks.encList L).length + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have e1 := exec_init e x (Stacks.encList L)
  have hst := c.start.isLt
  have e2 := exec_pushState (x := x) (eL := Stacks.encList L) (rs := x.map some) (ls := [])
    (rb := []) (clk := clock e x.length) (qs := []) c.start.val
    (S := (c.k + 10) * (x.length + clock e x.length + (Stacks.encList L).length + 1))
    (by rw [stk_space, length_encCells_map_some]
        simp only [List.length_nil, encCells_nil]; omega)
  obtain ⟨rs, ls, e3⟩ := exec_simLoop c L x (clock e x.length)
  generalize ((run c.toOTM {z | z ∈ L} x (clock e x.length)).q : Fin c.k) = q at e3 ⊢
  generalize (run c.toOTM {z | z ∈ L} x (clock e x.length)).buf.reverse = rb at e3
  generalize Stacks.encList L = eL at e1 e2 e3 hCN ⊢
  generalize clock e x.length = T at e1 e2 e3 hCN ⊢
  have sp3 := e3.space_le.2
  have spq := stk_space x eL rs ls q.val rb 0 []
  have sp0 := stk_space x eL rs ls 0 rb 0 []
  simp only [List.length_nil, add_zero] at spq sp0
  have hq := q.isLt
  have e4 : Exec (switchU 5 (List.ofFn fun q : Fin c.k => .push 2 (accB c q)))
      (stk x eL rs ls q.val rb 0 [])
      (Function.update (stk x eL rs ls 0 rb 0 []) 2 [accB c q])
      ((c.k + 10) * (x.length + T + eL.length + 1)) := by
    refine exec_switchU _ q.val (by simpa using q.isLt) rfl (by omega) ?_
    rw [List.getElem_ofFn]
    have e : Function.update (stk x eL rs ls q.val rb 0 []) 5 [] = stk x eL rs ls 0 rb 0 [] := by
      funext j; fin_cases j <;> rfl
    rw [e]
    refine Stmt.exec_of_eq (Exec.push (by omega)) ?_
    funext j; fin_cases j <;> rfl
  have e5 := Stmt.exec_clear 3 _ (Function.update (stk x eL rs ls 0 rb 0 []) 2
    [accB c q]) rfl
  have e6 := Stmt.exec_clear 4 _ (Function.update (Function.update (stk x eL rs ls 0 rb 0 []) 2
    [accB c q]) 3 []) rfl
  have e7 := Stmt.exec_clear 6 _ (Function.update (Function.update (Function.update
    (stk x eL rs ls 0 rb 0 []) 2 [accB c q]) 3 []) 4 []) rfl
  have hfin : Function.update (Function.update (Function.update (Function.update
      (stk x eL rs ls 0 rb 0 []) 2 [accB c q]) 3 []) 4 []) 6 [] =
      Function.update (Function.update (Function.update (fun _ => []) 0 x) 1 eL) 2
        [accB c q] := by
    funext j; fin_cases j <;> rfl
  rw [hfin] at e7
  have s4 := e4.space_le.2
  have s5 := e5.space_le.2
  have s6 := e6.space_le.2
  exact .seq (e1.mono (by omega)) (.seq e2 (.seq (e3.mono (by omega)) (.seq e4
    (.seq (e5.mono s4) (.seq (e6.mono (s5.trans s4)) (.seq (e7.mono (s6.trans (s5.trans s4)))
      (.skip (e7.space_le.2.trans (s6.trans (s5.trans s4))))))))))

end SimOTM

/-- **Simulation of a clocked machine with a listed oracle.**  For every clocked code
`(c, e)` there are a statement `s` over `k` stacks, three distinct stacks `inp`, `ora`, `out` and
a constant `C` such that, started with `x` on `inp`, the code `Stacks.encList L` of a finite list
`L` on `ora` and all other stacks empty, `s` terminates with the same contents plus a single bit
`[b]` on `out`, where `b = true` iff `(c, e)` accepts `x` with the oracle `{z | z ∈ L}`, within
space `C · (|x| + clock e |x| + |Stacks.encList L| + 1)`.

Construction: the tape of `c.toOTM` on two stacks (cells left of the head reversed, cells from
the head on; the code of a cell is `0` for a blank and `1b` for the bit `b`), the query buffer on
a stack, the current state in unary on a stack (dispatch on it by `switchU`), and a unary step
counter loaded with `|x| ^ e + e` (computed from a unary copy of `|x|` by `e` multiplication
steps); an `ask` compares the buffer with each code of `L` (moving `ora` to a work stack and
back).  Correctness: by induction on the number of simulated steps, the stacks encode
`run c.toOTM {z | z ∈ L} x t`; acceptance within the clock is read off at time `clock e |x|`
(accepting configurations are halted, hence fixed by `step`). -/
theorem exists_simStmt (c : OTMCode) (e : ℕ) :
    ∃ (k : ℕ) (s : Stmt k) (inp ora out : Fin k) (C : ℕ), inp ≠ ora ∧ inp ≠ out ∧
      ora ≠ out ∧ ∀ (x : BitString) (L : List BitString), ∃ b : Bool,
        (b = true ↔ ClockedAccepts c e {z | z ∈ L} x) ∧
        Exec s (Function.update (Function.update (fun _ => []) inp x) ora (Stacks.encList L))
          (Function.update (Function.update (Function.update (fun _ => []) inp x) ora
            (Stacks.encList L)) out [b])
          (C * (x.length + clock e x.length + (Stacks.encList L).length + 1)) := by
  refine ⟨21, SimOTM.simStmt c e, 0, 1, 2, c.k + 10, by decide, by decide, by decide,
    fun x L => ⟨_, ?_, SimOTM.exec_simStmt c e x L⟩⟩
  rw [clockedAccepts_iff_run]
  exact SimOTM.accB_iff c _

end Kolmogorov.RandomStrings
