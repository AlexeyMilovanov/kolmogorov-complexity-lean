/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.SimOTM

/-!
# The recording simulation of the clocked machine

A variant of `SimOTM.simStmt` that additionally records the codes of all queries asked during
the run (`SimOTM.recSimStmt`), together with its correctness (`SimOTM.exec_recSim`) and the
description of the recorded list (`SimOTM.recL`, `SimOTM.mem_recL`).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace SimOTM

/-- The body of `pushCode`: move the top bit `b` of `t` back to `Z` and push `b`, `true` on `D`. -/
def pushCodeBody (Z t D : Fin 21) : Stmt 21 :=
  Stmt.caseBit t fun b => Stmt.seqs [.pop t, .push Z b, .push D b, .push D true]

/-- Push the code `encStr z` of the string `z` on `Z` (first bit on top) onto `D`, restoring `Z`,
through the empty work stack `t`. -/
def pushCode (Z t D : Fin 21) : Stmt 21 :=
  Stmt.seqs [Stmt.moveAll Z t, .push D false, .loop t Option.isSome (pushCodeBody Z t D)]

/-- The cost and effect of the internal loop `pushCodeBody` inside `pushCode`. -/
theorem exec_pushCodeLoop {Z t D : Fin 21} (hZt : Z ≠ t) (hZD : Z ≠ D) (htD : t ≠ D) :
    ∀ (l : BitString) (σ : Stacks 21), σ t = l →
      Exec (.loop t Option.isSome (pushCodeBody Z t D)) σ
        (Function.update (Function.update (Function.update σ t []) Z (l.reverse ++ σ Z)) D
          ((l.reverse.flatMap fun b => [true, b]) ++ σ D)) (σ.space + 2 * l.length)
  | [], σ, h => by
    refine Stmt.exec_of_eq (.loopF (by simp [h]) (by omega)) ?_
    funext j
    simp only [Function.update_apply, List.reverse_nil, List.nil_append, List.flatMap_nil]
    split_ifs <;> subst_vars <;> simp_all
  | b :: l, σ, h => by
    have s1 := Stmt.space_update_of_cons h
    have p1 : Exec (.pop t) σ (Function.update σ t l) (σ.space + 2 * (b :: l).length) :=
      Stmt.exec_pop_cons h (by simp only [List.length_cons]; omega)
    have p2 : Exec (.push Z b) (Function.update σ t l)
        (Function.update (Function.update σ t l) Z (b :: σ Z))
        (σ.space + 2 * (b :: l).length) := by
      have := Exec.push (r := Z) (b := b) (σ := Function.update σ t l)
        (S := σ.space + 2 * (b :: l).length) (by simp only [List.length_cons]; omega)
      rwa [Function.update_of_ne hZt] at this
    have s2 : Stacks.space (Function.update (Function.update σ t l) Z (b :: σ Z)) = σ.space := by
      have := Stacks.space_update_cons (Function.update σ t l) Z b
      rw [Function.update_of_ne hZt] at this; omega
    have p3 : Exec (.push D b) (Function.update (Function.update σ t l) Z (b :: σ Z))
        (Function.update (Function.update (Function.update σ t l) Z (b :: σ Z)) D (b :: σ D))
        (σ.space + 2 * (b :: l).length) := by
      have := Exec.push (r := D) (b := b)
        (σ := Function.update (Function.update σ t l) Z (b :: σ Z))
        (S := σ.space + 2 * (b :: l).length) (by simp only [List.length_cons]; omega)
      rwa [Function.update_of_ne hZD.symm, Function.update_of_ne htD.symm] at this
    have s3 : Stacks.space (Function.update (Function.update (Function.update σ t l) Z
        (b :: σ Z)) D (b :: σ D)) = σ.space + 1 := by
      have := Stacks.space_update_cons (Function.update (Function.update σ t l) Z (b :: σ Z)) D b
      rw [Function.update_of_ne hZD.symm, Function.update_of_ne htD.symm] at this; omega
    have p4 : Exec (.push D true) (Function.update (Function.update (Function.update σ t l) Z
        (b :: σ Z)) D (b :: σ D))
        (Function.update (Function.update (Function.update σ t l) Z (b :: σ Z)) D
          (true :: b :: σ D)) (σ.space + 2 * (b :: l).length) := by
      have := Exec.push (r := D) (b := true)
        (σ := Function.update (Function.update (Function.update σ t l) Z (b :: σ Z)) D
          (b :: σ D)) (S := σ.space + 2 * (b :: l).length)
        (by simp only [List.length_cons]; omega)
      rwa [Function.update_self, Function.update_idem] at this
    have s4 : Stacks.space (Function.update (Function.update (Function.update σ t l) Z
        (b :: σ Z)) D (true :: b :: σ D)) = σ.space + 2 := by
      have := Stacks.space_update (Function.update (Function.update σ t l) Z (b :: σ Z)) D
        (true :: b :: σ D)
      rw [Function.update_of_ne hZD.symm, Function.update_of_ne htD.symm] at this
      simp only [List.length_cons] at this; omega
    have hbody : Exec (pushCodeBody Z t D) σ (Function.update (Function.update
        (Function.update σ t l) Z (b :: σ Z)) D (true :: b :: σ D))
        (σ.space + 2 * (b :: l).length) := by
      unfold pushCodeBody
      rw [Stmt.exec_caseBit h]
      exact .seq p1 (.seq p2 (.seq p3 (.seq p4 (.skip (by
        simp only [List.length_cons]; omega)))))
    have h4t : (Function.update (Function.update (Function.update σ t l) Z (b :: σ Z)) D
        (true :: b :: σ D)) t = l := by
      rw [Function.update_of_ne htD, Function.update_of_ne hZt.symm, Function.update_self]
    have ih := exec_pushCodeLoop hZt hZD htD l _ h4t
    rw [s4] at ih
    refine .loopT (by simp [h]) hbody (Stmt.exec_of_eq (ih.mono ?_) ?_)
    · simp only [List.length_cons]; omega
    · have h4Z : (Function.update (Function.update (Function.update σ t l) Z (b :: σ Z)) D
          (true :: b :: σ D)) Z = b :: σ Z := by
        rw [Function.update_of_ne hZD, Function.update_self]
      have h4D : (Function.update (Function.update (Function.update σ t l) Z (b :: σ Z)) D
          (true :: b :: σ D)) D = true :: b :: σ D := Function.update_self _ _ _
      rw [h4Z, h4D]
      funext j
      rcases eq_or_ne j D with rfl | hjD
      · simp only [Function.update_self, List.reverse_cons, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
          List.cons_append, List.nil_append]
      · rw [Function.update_of_ne hjD, Function.update_of_ne hjD]
        rcases eq_or_ne j Z with rfl | hjZ
        · simp only [Function.update_self, List.reverse_cons, List.append_assoc,
            List.singleton_append]
        · rw [Function.update_of_ne hjZ, Function.update_of_ne hjZ]
          rcases eq_or_ne j t with rfl | hjt
          · simp only [Function.update_self]
          · rw [Function.update_of_ne hjt, Function.update_of_ne hjt, Function.update_of_ne hjD,
              Function.update_of_ne hjZ, Function.update_of_ne hjt]

/-- The cost and effect of `pushCode`. -/
theorem exec_pushCode {Z t D : Fin 21} (hZt : Z ≠ t) (hZD : Z ≠ D) (htD : t ≠ D)
    {σ : Stacks 21} (ht : σ t = []) :
    Exec (pushCode Z t D) σ (Function.update σ D (Stacks.encStr (σ Z) ++ σ D))
      (σ.space + 2 * (σ Z).length + 1) := by
  have e1 := Stmt.exec_moveAll hZt (σ Z) σ rfl
  rw [ht, List.append_nil] at e1
  have sp1 := e1.space_le.2
  have e2 := Exec.push (r := D) (b := false)
    (σ := Function.update (Function.update σ Z []) t (σ Z).reverse)
    (S := σ.space + 2 * (σ Z).length + 1) (by omega)
  rw [Function.update_of_ne htD.symm, Function.update_of_ne hZD.symm] at e2
  have s2 := Stacks.space_update_cons (Function.update (Function.update σ Z []) t (σ Z).reverse)
    D false
  rw [Function.update_of_ne htD.symm, Function.update_of_ne hZD.symm] at s2
  have e3 := exec_pushCodeLoop hZt hZD htD (σ Z).reverse
    (Function.update (Function.update (Function.update σ Z []) t (σ Z).reverse) D
      (false :: σ D)) (by rw [Function.update_of_ne htD, Function.update_self])
  rw [s2, List.length_reverse, List.reverse_reverse] at e3
  have hZ3 : (Function.update (Function.update (Function.update σ Z []) t (σ Z).reverse) D
      (false :: σ D)) Z = [] := by
    rw [Function.update_of_ne hZD, Function.update_of_ne hZt, Function.update_self]
  have hD3 : (Function.update (Function.update (Function.update σ Z []) t (σ Z).reverse) D
      (false :: σ D)) D = false :: σ D := Function.update_self _ _ _
  rw [hZ3, hD3, List.append_nil] at e3
  refine .seq (e1.mono (by omega)) (.seq e2 (.seq (Stmt.exec_of_eq (e3.mono (by omega)) ?_)
    (.skip ?_)))
  · funext j
    rcases eq_or_ne j D with rfl | hjD
    · simp only [Function.update_self, Stacks.encStr, List.append_assoc, List.singleton_append]
    · rw [Function.update_of_ne hjD, Function.update_of_ne hjD]
      rcases eq_or_ne j Z with rfl | hjZ
      · simp only [Function.update_self]
      · rw [Function.update_of_ne hjZ]
        rcases eq_or_ne j t with rfl | hjt
        · rw [Function.update_self, ht]
        · rw [Function.update_of_ne hjt, Function.update_of_ne hjD, Function.update_of_ne hjt,
            Function.update_of_ne hjZ]
  · have := Stacks.space_update σ D (Stacks.encStr (σ Z) ++ σ D)
    simp only [List.length_append, Stacks.length_encStr] at this
    omega

/-- Answering a query and recording it: as `askStmt`, and the code of the query is pushed on the
record stack `16`. -/
def askStmtR (c : OTMCode) (qy qn : Fin c.k) : Stmt 21 :=
  Stmt.seqs [Stmt.moveAll 6 8, Stmt.memTest.rename memMap, pushCode 8 17 16, Stmt.clear 8,
    Stmt.caseBit 9 fun g => .seq (.pop 9) (Stmt.pushList 5 (un (if g then qy else qn).val))]

/-- The cost and effect of `askStmtR` under `stk`. -/
theorem exec_askR (c : OTMCode) (qy qn : Fin c.k) {x : BitString} {L : List BitString}
    {rs ls : List Sym}
    {clk : ℕ} {qs : BitString} (buf : BitString) {S : ℕ}
    (hS : (stk x (Stacks.encList L) rs ls 0 buf.reverse clk qs).space +
      (Stacks.encList L).length + 2 * buf.length + c.k + 3 ≤ S) :
    Exec (askStmtR c qy qn) (stk x (Stacks.encList L) rs ls 0 buf.reverse clk qs)
      (stk x (Stacks.encList L) rs ls (if buf ∈ L then qy else qn).val [] clk
        (Stacks.encStr buf ++ qs)) S := by
  have e1 := Stmt.exec_moveAll (by decide : (6 : Fin 21) ≠ 8)
    ((stk x (Stacks.encList L) rs ls 0 buf.reverse clk qs) 6)
    (stk x (Stacks.encList L) rs ls 0 buf.reverse clk qs) rfl
  have hσ1 : Function.update (Function.update (stk x (Stacks.encList L) rs ls 0 buf.reverse clk qs)
      6 []) 8 (((stk x (Stacks.encList L) rs ls 0 buf.reverse clk qs) 6).reverse ++
        (stk x (Stacks.encList L) rs ls 0 buf.reverse clk qs) 8) =
      Function.update (stk x (Stacks.encList L) rs ls 0 [] clk qs) 8 buf := by
    funext j; fin_cases j <;> first | rfl | simp [stk]
  rw [hσ1] at e1
  have e2 := exec_memSim (x := x) (L := L) (rs := rs) (ls := ls) (clk := clk) (qs := qs) buf
  have eR : Exec (pushCode 8 17 16) (Function.update (Function.update
      (stk x (Stacks.encList L) rs ls 0 [] clk qs) 8 buf) 9 [decide (buf ∈ L)])
      (Function.update (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk
        (Stacks.encStr buf ++ qs)) 8 buf) 9 [decide (buf ∈ L)])
      (Stacks.space (Function.update (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk qs)
        8 buf) 9 [decide (buf ∈ L)]) + 2 * buf.length + 1) := by
    have := exec_pushCode (Z := 8) (t := 17) (D := 16) (by decide) (by decide) (by decide)
      (σ := Function.update (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk qs) 8 buf) 9
        [decide (buf ∈ L)]) rfl
    exact Stmt.exec_of_eq this (by funext j; fin_cases j <;> rfl)
  have e3 := Stmt.exec_clear 8 _ (Function.update (Function.update
    (stk x (Stacks.encList L) rs ls 0 [] clk (Stacks.encStr buf ++ qs)) 8 buf) 9
      [decide (buf ∈ L)]) rfl
  have hσ3 : Function.update (Function.update (Function.update
      (stk x (Stacks.encList L) rs ls 0 [] clk (Stacks.encStr buf ++ qs)) 8 buf) 9
        [decide (buf ∈ L)]) 8 [] =
      Function.update (stk x (Stacks.encList L) rs ls 0 [] clk (Stacks.encStr buf ++ qs)) 9
        [decide (buf ∈ L)] := by
    funext j; fin_cases j <;> rfl
  rw [hσ3] at e3
  have sp0 := stk_space x (Stacks.encList L) rs ls 0 buf.reverse clk qs
  have sp1 := stk_space x (Stacks.encList L) rs ls 0 [] clk (Stacks.encStr buf ++ qs)
  simp only [List.length_reverse, List.length_nil, add_zero, List.length_append,
    Stacks.length_encStr] at sp0 sp1
  have hq := (if buf ∈ L then qy else qn).isLt
  have sA := e1.space_le.2
  have sB := e2.space_le.2
  have sC := eR.space_le.2
  have sD := e3.space_le.2
  have e4 : Exec (Stmt.caseBit 9 fun g => .seq (.pop 9)
      (Stmt.pushList 5 (un (if g then qy else qn).val)))
      (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk (Stacks.encStr buf ++ qs)) 9
        [decide (buf ∈ L)])
      (stk x (Stacks.encList L) rs ls (if buf ∈ L then qy else qn).val [] clk
        (Stacks.encStr buf ++ qs)) S := by
    rw [Stmt.exec_caseBit (b := decide (buf ∈ L)) (l := []) rfl]
    have p1 := Exec.pop (r := 9)
      (σ := Function.update (stk x (Stacks.encList L) rs ls 0 [] clk (Stacks.encStr buf ++ qs)) 9
        [decide (buf ∈ L)]) (S := S) (by omega)
    have hp : Function.update (Function.update (stk x (Stacks.encList L) rs ls 0 [] clk
        (Stacks.encStr buf ++ qs)) 9 [decide (buf ∈ L)]) 9 ((Function.update
          (stk x (Stacks.encList L) rs ls 0 [] clk (Stacks.encStr buf ++ qs)) 9
          [decide (buf ∈ L)]) 9).tail =
        stk x (Stacks.encList L) rs ls 0 [] clk (Stacks.encStr buf ++ qs) := by
      funext j; fin_cases j <;> rfl
    rw [hp] at p1
    have p2 := exec_pushState (x := x) (eL := Stacks.encList L) (rs := rs) (ls := ls) (rb := [])
      (clk := clk) (qs := Stacks.encStr buf ++ qs) (if buf ∈ L then qy else qn).val (S := S)
      (by omega)
    refine .seq p1 ?_
    by_cases hb : buf ∈ L
    · simpa [hb] using p2
    · simpa [hb] using p2
  refine .seq (e1.mono (by omega)) (.seq (e2.mono (by omega)) (.seq (eR.mono (by omega))
    (.seq (e3.mono (by omega)) (.seq e4 (.skip e4.space_le.2)))))

/-- If `M` has halted at `cfg`, `askedAt M cfg` is `none`. -/
theorem askedAt_of_halted {M : OTM} {cfg : Config M} (h : Halted M cfg) :
    askedAt M cfg = none := by
  unfold askedAt; rw [ite_eq_left h]

/-- If the action is a step, `askedAt M cfg` is `none`. -/
theorem askedAt_of_act_step {M : OTM} {cfg : Config M} (h : ¬ Halted M cfg) {q' : M.Q} {a : Sym}
    {m : Move} (hδ : M.δ cfg.q (cfg.tape cfg.head) = .step q' a m) : askedAt M cfg = none := by
  unfold askedAt; rw [ite_eq_right h, hδ]

/-- If the action is a push, `askedAt M cfg` is `none`. -/
theorem askedAt_of_act_push {M : OTM} {cfg : Config M} (h : ¬ Halted M cfg) {q' : M.Q} {b : Bool}
    (hδ : M.δ cfg.q (cfg.tape cfg.head) = .push q' b) : askedAt M cfg = none := by
  unfold askedAt; rw [ite_eq_right h, hδ]

/-- If the action is a query, `askedAt M cfg` is the current buffer string `cfg.buf`. -/
theorem askedAt_of_act_ask {M : OTM} {cfg : Config M} (h : ¬ Halted M cfg) {qy qn : M.Q}
    (hδ : M.δ cfg.q (cfg.tape cfg.head) = .ask qy qn) : askedAt M cfg = some cfg.buf := by
  unfold askedAt; rw [ite_eq_right h, hδ]

/-- The record after one more step: the code of the string asked at `cfg` (if any) is pushed. -/
noncomputable def recNext (M : OTM) (cfg : Config M) (qs : BitString) : BitString :=
  match askedAt M cfg with
  | some z => Stacks.encStr z ++ qs
  | none => qs

/-- When `askedAt` is `none`, `recNext` leaves the history `qs` unchanged. -/
theorem recNext_of_none {M : OTM} {cfg : Config M} {qs : BitString} (h : askedAt M cfg = none) :
    recNext M cfg qs = qs := by
  unfold recNext; rw [h]

/-- When `askedAt` is `some z`, `recNext` prepends the code of `z` to `qs`. -/
theorem recNext_of_some {M : OTM} {cfg : Config M} {qs z : BitString} (h : askedAt M cfg = some z) :
    recNext M cfg qs = Stacks.encStr z ++ qs := by
  unfold recNext; rw [h]

/-- The action of the state `q` on the scanned cell `a` (already removed from the right part;
the state stack is empty): perform the step of the machine and push the new state. -/
def actStmtR (c : OTMCode) (q : Fin c.k) (a : Sym) : Stmt 21 :=
  if q = c.accept ∨ q = c.reject then .seq (pushCell 3 a) (Stmt.pushList 5 (un q.val))
  else
    match c.δ q a with
    | .step q' a' .stay => .seq (pushCell 3 a') (Stmt.pushList 5 (un q'.val))
    | .step q' a' .right => .seq (pushCell 4 a') (Stmt.pushList 5 (un q'.val))
    | .step q' a' .left =>
      .seq (pushCell 3 a') (.seq (readCell 4 (pushCell 3)) (Stmt.pushList 5 (un q'.val)))
    | .push q' b => .seq (pushCell 3 a) (.seq (.push 6 b) (Stmt.pushList 5 (un q'.val)))
    | .ask qy qn => .seq (pushCell 3 a) (askStmtR c qy qn)

/-- One step of the machine `c`: dispatch on the state, read the scanned cell, act. -/
def stepStmtR (c : OTMCode) : Stmt 21 :=
  switchU 5 (List.ofFn fun q : Fin c.k => readCell 3 (actStmtR c q))

/-- The cost and effect of `stepStmtR` under `stk` with the `recNext` update. -/
theorem exec_stepR (c : OTMCode) (L : List BitString) (x : BitString) (clk : ℕ) (qs : BitString)
    (cfg : Config c.toOTM)
    (rs ls : List Sym) (hrep : TapeRep cfg.tape cfg.head rs ls) (S : ℕ)
    (hS : x.length + 2 * (Stacks.encList L).length + (encCells rs).length +
      (encCells ls).length + c.k + 3 * cfg.buf.length + clk + qs.length + 10 ≤ S) :
    ∃ rs' ls', TapeRep (step c.toOTM {z | z ∈ L} cfg).tape (step c.toOTM {z | z ∈ L} cfg).head
        rs' ls' ∧
      (encCells rs').length + (encCells ls').length ≤
        (encCells rs).length + (encCells ls).length + 4 ∧
      Exec (stepStmtR c)
        (stk x (Stacks.encList L) rs ls (cfg.q : Fin c.k).val cfg.buf.reverse clk qs)
        (stk x (Stacks.encList L) rs' ls' ((step c.toOTM {z | z ∈ L} cfg).q : Fin c.k).val
          (step c.toOTM {z | z ∈ L} cfg).buf.reverse clk (recNext c.toOTM cfg qs)) S := by
  have ha : cfg.tape cfg.head = rs.headD none := by
    have := hrep.1 0
    simp only [Nat.cast_zero, add_zero] at this
    rw [this]; cases rs <;> rfl
  have htl := length_encCells_tail rs
  have hht := length_encCells_headD_tail rs
  have hqk := (cfg.q : Fin c.k).isLt
  have key : ∀ σ', Exec (actStmtR c cfg.q (rs.headD none))
      (stk x (Stacks.encList L) rs.tail ls 0 cfg.buf.reverse clk qs) σ' S →
      Exec (stepStmtR c)
        (stk x (Stacks.encList L) rs ls (cfg.q : Fin c.k).val cfg.buf.reverse clk qs) σ' S := by
    intro σ' h
    refine exec_switchU _ (cfg.q : Fin c.k).val (by simpa using hqk) rfl
      (by rw [stk_space]; simp only [List.length_reverse]; omega) ?_
    rw [List.getElem_ofFn]
    have e : Function.update (stk x (Stacks.encList L) rs ls (cfg.q : Fin c.k).val
        cfg.buf.reverse clk qs) 5 [] =
        stk x (Stacks.encList L) rs ls 0 cfg.buf.reverse clk qs := by
      funext j; fin_cases j <;> rfl
    rw [e]
    exact exec_readCell3 (by rw [stk_space]; simp only [List.length_reverse]; omega) h
  by_cases hH : (cfg.q : Fin c.k) = c.accept ∨ (cfg.q : Fin c.k) = c.reject
  · have hst : step c.toOTM {z | z ∈ L} cfg = cfg := step_of_halted _ _ _ hH
    rw [hst, recNext_of_none (askedAt_of_halted (M := c.toOTM) hH)]
    refine ⟨rs.headD none :: rs.tail, ls, tapeRep_same hrep, by omega, key _ ?_⟩
    unfold actStmtR
    split_ifs with h'
    swap; · exact (h' hH).elim
    refine .seq (exec_pushCell3 _ ?_) (exec_pushState _ ?_)
    · rw [stk_space]; simp only [List.length_reverse]; omega
    · rw [stk_space]; simp only [List.length_reverse]; omega
  · have hH' : ¬ Halted c.toOTM cfg := hH
    have hsp := fun rs' ls' q' rb => stk_space x (Stacks.encList L) rs' ls' q' rb clk qs
    cases hδ : c.δ cfg.q (rs.headD none) with
    | step q' a' m =>
      rw [recNext_of_none (askedAt_of_act_step hH' (show c.toOTM.δ cfg.q (cfg.tape cfg.head) =
        Act.step q' a' m by rw [ha]; exact hδ))]
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
        · unfold actStmtR
          split_ifs with h'
          · exact (hH h').elim
          rw [hδ]
          refine .seq (exec_pushCell3 _ ?_) (exec_pushState _ ?_)
          · rw [hsp]; simp only [List.length_reverse]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append, List.length_reverse]; omega
      | right =>
        refine ⟨rs.tail, a' :: ls, tapeRep_right hrep a', ?_, key _ ?_⟩
        · simp only [encCells_cons, List.length_append]; omega
        · unfold actStmtR
          split_ifs with h'
          · exact (hH h').elim
          rw [hδ]
          refine .seq (exec_pushCell4 _ ?_) (exec_pushState _ ?_)
          · rw [hsp]; simp only [List.length_reverse]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append, List.length_reverse]; omega
      | left =>
        have hlt := length_encCells_tail ls
        have hlh := length_encCell_le (ls.headD none)
        have hlht := length_encCells_headD_tail ls
        refine ⟨ls.headD none :: a' :: rs.tail, ls.tail, tapeRep_left hrep a', ?_, key _ ?_⟩
        · simp only [encCells_cons, List.length_append] at hlht ⊢; omega
        · unfold actStmtR
          split_ifs with h'
          · exact (hH h').elim
          rw [hδ]
          refine .seq (exec_pushCell3 _ ?_) (.seq (exec_readCell4 ?_ (exec_pushCell3 _ ?_))
            (exec_pushState _ ?_))
          · rw [hsp]; simp only [List.length_reverse]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append, List.length_reverse]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append, List.length_reverse]; omega
          · rw [hsp]; simp only [encCells_cons, List.length_append,
              List.length_reverse] at hlht ⊢; omega
    | push q' b =>
      rw [recNext_of_none (askedAt_of_act_push hH' (show c.toOTM.δ cfg.q (cfg.tape cfg.head) =
        Act.push q' b by rw [ha]; exact hδ))]
      have hq' := q'.isLt
      unfold step
      rw [ite_eq_right hH', show c.toOTM.δ cfg.q (cfg.tape cfg.head) = Act.push q' b by
        rw [ha]; exact hδ]
      dsimp only
      refine ⟨rs.headD none :: rs.tail, ls, tapeRep_same hrep, by omega, key _ ?_⟩
      unfold actStmtR
      split_ifs with h'
      · exact (hH h').elim
      rw [hδ]
      have hrb : (cfg.buf ++ [b]).reverse = b :: cfg.buf.reverse := by simp
      rw [hrb]
      refine .seq (exec_pushCell3 _ ?_) (.seq (exec_pushBuf b ?_) (exec_pushState _ ?_))
      · rw [hsp]; simp only [List.length_reverse]; omega
      · rw [hsp]; simp only [List.length_reverse]; omega
      · rw [hsp]; simp only [List.length_reverse, List.length_cons]; omega
    | ask qy qn =>
      rw [recNext_of_some (askedAt_of_act_ask hH' (show c.toOTM.δ cfg.q (cfg.tape cfg.head) =
        Act.ask qy qn by rw [ha]; exact hδ))]
      unfold step
      rw [ite_eq_right hH', show c.toOTM.δ cfg.q (cfg.tape cfg.head) = Act.ask qy qn by
        rw [ha]; exact hδ]
      dsimp only
      have hex : ∀ q'' : Fin c.k, q'' = (if cfg.buf ∈ L then qy else qn) →
          Exec (actStmtR c cfg.q (rs.headD none))
            (stk x (Stacks.encList L) rs.tail ls 0 cfg.buf.reverse clk qs)
            (stk x (Stacks.encList L) (rs.headD none :: rs.tail) ls q''.val [] clk
              (Stacks.encStr cfg.buf ++ qs)) S := by
        intro q'' hq''
        unfold actStmtR
        split_ifs with h'
        · exact (hH h').elim
        rw [hδ]
        have e := exec_askR c qy qn (x := x) (L := L) (rs := rs.headD none :: rs.tail) (ls := ls)
          (clk := clk) (qs := qs) cfg.buf (S := S)
          (by rw [hsp]; simp only [List.length_reverse]; omega)
        rw [← hq''] at e
        have e0 := exec_pushCell3 (x := x) (eL := Stacks.encList L) (rs := rs.tail) (ls := ls)
          (q := 0) (rb := cfg.buf.reverse) (clk := clk) (qs := qs) (rs.headD none) (S := S)
          (by rw [hsp]; simp only [List.length_reverse]; omega)
        exact .seq e0 e
      refine ⟨rs.headD none :: rs.tail, ls, tapeRep_same hrep, by omega, key _ (hex _ ?_)⟩
      by_cases hb : cfg.buf ∈ L <;> simp [hb]

/-- The queries asked before time `t`, latest first. -/
noncomputable def recL (M : OTM) (B : Set BitString) (x : BitString) : ℕ → List BitString
  | 0 => []
  | t + 1 => match askedAt M (run M B x t) with
    | some z => z :: recL M B x t
    | none => recL M B x t

/-- `recNext` acting on the encoded list up to `t` gives the encoded list up to `t + 1`. -/
theorem recNext_recL (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) :
    recNext M (run M B x t) (Stacks.encList (recL M B x t)) =
      Stacks.encList (recL M B x (t + 1)) := by
  cases h : askedAt M (run M B x t) with
  | none => rw [recNext_of_none h]; simp only [recL, h]
  | some z => rw [recNext_of_some h]; simp only [recL, h, Stacks.encList, List.flatMap_cons]

/-- The elements of `recL M B x t` are exactly the strings in `queries M B x t`. -/
theorem mem_recL (M : OTM) (B : Set BitString) (x : BitString) (z : BitString) :
    ∀ t, z ∈ recL M B x t ↔ z ∈ queries M B x t
  | 0 => by simp [recL, queries]
  | t + 1 => by
    rw [mem_queries]
    have ih := mem_recL M B x z t
    rw [mem_queries] at ih
    constructor
    · intro h
      simp only [recL] at h
      cases ha : askedAt M (run M B x t) with
      | none =>
        rw [ha] at h
        obtain ⟨s, hs, h'⟩ := ih.1 h
        exact ⟨s, by omega, h'⟩
      | some w =>
        rw [ha] at h
        rcases List.mem_cons.1 h with rfl | h
        · exact ⟨t, by omega, ha⟩
        · obtain ⟨s, hs, h'⟩ := ih.1 h
          exact ⟨s, by omega, h'⟩
    · rintro ⟨s, hs, h'⟩
      simp only [recL]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · have := ih.2 ⟨s, hs, h'⟩
        cases askedAt M (run M B x t) <;> simp [this]
      · rw [h']; simp

/-- The length of the encoded recorded list up to `t` is bounded by `t * (2 * t + 1)`. -/
theorem length_recL (M : OTM) (B : Set BitString) (x : BitString) :
    ∀ t, (Stacks.encList (recL M B x t)).length ≤ t * (2 * t + 1)
  | 0 => by simp [recL, Stacks.encList]
  | t + 1 => by
    have ih := length_recL M B x t
    simp only [recL]
    cases ha : askedAt M (run M B x t) with
    | none => simp only; nlinarith
    | some w =>
      have hw := length_le_of_askedAt M B x t w ha
      simp only [Stacks.encList, List.flatMap_cons, List.length_append, Stacks.length_encStr]
      simp only [Stacks.encList] at ih
      nlinarith

/-- The main loop of the recording simulation. -/
theorem exec_recLoop (c : OTMCode) (L : List BitString) (x : BitString) (T : ℕ) :
    ∃ rs ls, Exec (.loop 7 Option.isSome (.seq (.pop 7) (stepStmtR c)))
      (stk x (Stacks.encList L) (x.map some) [] c.start.val [] T [])
      (stk x (Stacks.encList L) rs ls ((run c.toOTM {z | z ∈ L} x T).q : Fin c.k).val
        (run c.toOTM {z | z ∈ L} x T).buf.reverse 0
        (Stacks.encList (recL c.toOTM {z | z ∈ L} x T)))
      (3 * x.length + 2 * (Stacks.encList L).length + 8 * T + c.k + 10 + T * (2 * T + 1)) := by
  set B : Set BitString := {z | z ∈ L} with hB
  set eL := Stacks.encList L with heL
  set S := 3 * x.length + 2 * eL.length + 8 * T + c.k + 10 + T * (2 * T + 1) with hSdef
  let I : Stacks 21 → Prop := fun σ => ∃ t ≤ T, ∃ rs ls,
    TapeRep (run c.toOTM B x t).tape (run c.toOTM B x t).head rs ls ∧
    (encCells rs).length + (encCells ls).length ≤ 2 * x.length + 4 * t ∧
    σ = stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val (run c.toOTM B x t).buf.reverse
      (T - t) (Stacks.encList (recL c.toOTM B x t))
  have hrecb : ∀ t ≤ T, (Stacks.encList (recL c.toOTM B x t)).length ≤ T * (2 * T + 1) :=
    fun t ht => (length_recL c.toOTM B x t).trans (Nat.mul_le_mul ht (by omega))
  have hstep : ∀ σ, I σ → Option.isSome (σ 7).head? = true →
      ∃ σ', Exec (.seq (.pop 7) (stepStmtR c)) σ σ' S ∧ I σ' ∧ (σ' 7).length < (σ 7).length := by
    rintro σ ⟨t, ht, rs, ls, hrep, hlen, rfl⟩ hc
    have htT : t < T := by
      by_contra hcon
      have h0 : T - t = 0 := by omega
      have : (stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
          (run c.toOTM B x t).buf.reverse (T - t)
          (Stacks.encList (recL c.toOTM B x t))) 7 = [] := by
        change un (T - t) = []; rw [h0]; rfl
      rw [this] at hc; simp at hc
    have hbuf := buf_length_le c.toOTM B x t
    have hqk := ((run c.toOTM B x t).q : Fin c.k).isLt
    have hTt : T - (t + 1) ≤ T := Nat.sub_le _ _
    have hr := hrecb t ht
    obtain ⟨rs', ls', hrep', hlen', hex⟩ := exec_stepR c L x (T - (t + 1))
      (Stacks.encList (recL c.toOTM B x t)) (run c.toOTM B x t) rs ls hrep S
      (by rw [← heL]; omega)
    rw [recNext_recL] at hex
    have hpop : Exec (.pop 7) (stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
        (run c.toOTM B x t).buf.reverse (T - t) (Stacks.encList (recL c.toOTM B x t)))
        (stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
        (run c.toOTM B x t).buf.reverse (T - (t + 1)) (Stacks.encList (recL c.toOTM B x t))) S := by
      have h := Exec.pop (r := 7) (σ := stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
        (run c.toOTM B x t).buf.reverse (T - t) (Stacks.encList (recL c.toOTM B x t))) (S := S)
        (by rw [stk_space]; simp only [List.length_reverse]; omega)
      refine Stmt.exec_of_eq h ?_
      have e7 : ((stk x eL rs ls ((run c.toOTM B x t).q : Fin c.k).val
          (run c.toOTM B x t).buf.reverse (T - t) (Stacks.encList (recL c.toOTM B x t))) 7).tail =
          un (T - (t + 1)) := by
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
    have hr := hrecb t ht
    rw [stk_space]; simp only [List.length_reverse]; omega
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
        (run c.toOTM B x t).buf.reverse (T - t) (Stacks.encList (recL c.toOTM B x t))) 7 =
        un (T - t) := rfl
    rw [h7, h0] at hc; simp at hc
  subst htT
  refine ⟨rs, ls, ?_⟩
  rw [Nat.sub_self] at hex
  exact hex

/-- The recording simulation statement: initialise, push the start state, run the clocked loop
recording the queries on `16`, and clean up. -/
def recSimStmt (c : OTMCode) (e : ℕ) : Stmt 21 :=
  Stmt.seqs [initStmt e, Stmt.pushList 5 (un c.start.val),
    .loop 7 Option.isSome (.seq (.pop 7) (stepStmtR c)),
    Stmt.clear 5, Stmt.clear 3, Stmt.clear 4, Stmt.clear 6]

/-- Correctness of `recSimStmt`: executing `recSimStmt c e` produces the expected output. -/
theorem exec_recSim (c : OTMCode) (e : ℕ) (x : BitString) (L : List BitString) :
    Exec (recSimStmt c e)
      (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList L))
      (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1
        (Stacks.encList L)) 16 (Stacks.encList (recL c.toOTM {z | z ∈ L} x (clock e x.length))))
      ((c.k + 20) * (x.length + clock e x.length + (Stacks.encList L).length + 1) ^ 2) := by
  have e1 := exec_init e x (Stacks.encList L)
  have hst := c.start.isLt
  obtain ⟨rs, ls, e3⟩ := exec_recLoop c L x (clock e x.length)
  generalize ((run c.toOTM {z | z ∈ L} x (clock e x.length)).q : Fin c.k) = q at e3
  generalize (run c.toOTM {z | z ∈ L} x (clock e x.length)).buf.reverse = rb at e3
  generalize Stacks.encList (recL c.toOTM {z | z ∈ L} x (clock e x.length)) = R at e3 ⊢
  generalize Stacks.encList L = eL at e1 e3 ⊢
  generalize clock e x.length = T at e1 e3 ⊢
  set N := x.length + T + eL.length + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hTN : T ≤ N := by omega
  have hT2 : T * (2 * T + 1) ≤ 3 * N ^ 2 := by nlinarith
  have hk : c.k ≤ c.k * N ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hexp : (c.k + 20) * N ^ 2 = c.k * N ^ 2 + 20 * N ^ 2 := by ring
  have e2 := exec_pushState (x := x) (eL := eL) (rs := x.map some) (ls := [])
    (rb := []) (clk := T) (qs := []) c.start.val (S := (c.k + 20) * N ^ 2)
    (by rw [stk_space, length_encCells_map_some]
        simp only [List.length_nil, encCells_nil]; omega)
  have sp3 := e3.space_le.2
  have e4 := Stmt.exec_clear 5 _ (stk x eL rs ls q.val rb 0 R) rfl
  have e5 := Stmt.exec_clear 3 _ (Function.update (stk x eL rs ls q.val rb 0 R) 5 []) rfl
  have e6 := Stmt.exec_clear 4 _ (Function.update (Function.update
    (stk x eL rs ls q.val rb 0 R) 5 []) 3 []) rfl
  have e7 := Stmt.exec_clear 6 _ (Function.update (Function.update (Function.update
    (stk x eL rs ls q.val rb 0 R) 5 []) 3 []) 4 []) rfl
  have hfin : Function.update (Function.update (Function.update (Function.update
      (stk x eL rs ls q.val rb 0 R) 5 []) 3 []) 4 []) 6 [] =
      Function.update (Function.update (Function.update (fun _ => []) 0 x) 1 eL) 16 R := by
    funext j; fin_cases j <;> rfl
  rw [hfin] at e7
  have s4 := e4.space_le.2
  have s5 := e5.space_le.2
  have s6 := e6.space_le.2
  exact .seq (e1.mono (by omega)) (.seq e2 (.seq (e3.mono (by omega)) (.seq (e4.mono (by omega))
    (.seq (e5.mono (by omega)) (.seq (e6.mono (by omega)) (.seq (e7.mono (by omega))
      (.skip (by have := e7.space_le.2; omega))))))))

end SimOTM

end Kolmogorov.RandomStrings
