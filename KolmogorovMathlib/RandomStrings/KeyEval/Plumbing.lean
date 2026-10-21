/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.KeyEval.Table

/-!
# The plumbing of the value-iteration driver

Splitting off a prefix (for the index-string counter), calling a key routine on a key held on
another stack, inlining the 9-stack plumbing routines into the driver's stacks, the bit
combinators of the layer body, and explicit step bounds for the inlined plumbing routines.

Part of `KolmogorovMathlib.RandomStrings.KeyEval`.
-/

namespace Kolmogorov.RandomStrings

namespace KeyEval

/-! ### Splitting off a prefix (for the index-string counter)

`takeLoop U C D` moves the first `n` bits of `C` onto `D` (reversed), consuming a unary counter
`replicate n true` on `U`; with `Stmt.copy` (to keep `C`) and `Stmt.moveAll` (to restore the
order) it splits an index string `κ ++ bitsOf W y ++ bitsOf W n` into its parts. -/

/-- Move `|U|` bits from `C` to `D`, popping the unary counter `U`. -/
def takeLoop {k : ℕ} (U C D : Fin k) : Stmt k :=
  .loop U Option.isSome (.seq (.pop U) (Stmt.moveBit C D))

/-- **Running `takeLoop`.** If `U`, `C`, `D` are pairwise distinct, `U` holds `replicate n true`
and `C` holds `pre ++ rest` with `|pre| = n`, then `takeLoop U C D` empties `U`, leaves `rest`
on `C` and puts `pre.reverse` in front of the content of `D`, within space `σ.space`
and `n * 7 + 1` steps. The three distinctness proofs are optional arguments, found by `decide`
when the stacks are numerals. -/
theorem execLe_takeLoop {k : ℕ} {U C D : Fin k} :
    ∀ (n : ℕ) (σ : Stacks k) (pre rest : BitString), σ U = List.replicate n true →
      σ C = pre ++ rest → pre.length = n →
      (hUC : U ≠ C := by decide) → (hUD : U ≠ D := by decide) →
      (hCD : C ≠ D := by decide) → ExecLe (takeLoop U C D) σ
        (Function.update (Function.update (Function.update σ U []) C rest) D
          (pre.reverse ++ σ D)) σ.space (n * 7 + 1)
  | 0, σ, pre, rest, hU, hC, hpre, _, _, _ => by
    rw [List.length_eq_zero_iff] at hpre
    subst hpre
    have hfin : Function.update (Function.update (Function.update σ U []) C rest) D
        ([].reverse ++ σ D) = σ := by
      simp only [List.replicate_zero] at hU
      simp only [List.nil_append] at hC
      funext r
      by_cases hr : r = D
      · subst hr; simp
      · rw [Function.update_of_ne hr]
        by_cases hr' : r = C
        · subst hr'; rw [Function.update_self, hC]
        · rw [Function.update_of_ne hr']
          by_cases hr'' : r = U
          · subst hr''; rw [Function.update_self, hU]
          · rw [Function.update_of_ne hr'']
    rw [hfin]
    exact ExecLe.loopF (by simp [hU]) le_rfl (by omega)
  | n + 1, σ, pre, rest, hU, hC, hpre, hUC, hUD, hCD => by
    replace hUC : U ≠ C := hUC
    replace hUD : U ≠ D := hUD
    replace hCD : C ≠ D := hCD
    obtain ⟨b, pre', rfl⟩ : ∃ b pre', pre = b :: pre' := by
      cases pre with
      | nil => simp at hpre
      | cons b pre' => exact ⟨b, pre', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hpre
    have hU' : σ U = true :: List.replicate n true := by rw [hU, List.replicate_succ]
    have hsp1 := Stmt.space_update_of_cons hU'
    have e1 : ExecLe (.pop U) σ (Function.update σ U (List.replicate n true)) σ.space 1 := by
      have := ExecLe.pop (r := U) (σ := σ) (S := σ.space) (T := 1) le_rfl le_rfl
      rwa [hU'] at this
    set σ1 := Function.update σ U (List.replicate n true) with hσ1
    have h1C : σ1 C = b :: (pre' ++ rest) := by
      rw [hσ1, Function.update_of_ne hUC.symm, hC, List.cons_append]
    have e2 := (Stmt.execLe_moveBit hCD h1C).mono (show Stacks.space σ1 ≤ σ.space by omega)
    set σ2 := Function.update (Function.update σ1 C (pre' ++ rest)) D (b :: σ1 D) with hσ2
    have hsp2 : Stacks.space σ2 = Stacks.space σ1 := by
      have a1 := Stacks.space_update σ1 C (pre' ++ rest)
      have a2 := Stacks.space_update (Function.update σ1 C (pre' ++ rest)) D (b :: σ1 D)
      rw [Function.update_of_ne hCD.symm] at a2
      rw [h1C] at a1
      simp only [List.length_cons] at a1 a2
      rw [hσ2]; omega
    have h2U : σ2 U = List.replicate n true := by
      rw [hσ2, Function.update_of_ne hUD, Function.update_of_ne hUC, hσ1, Function.update_self]
    have h2C : σ2 C = pre' ++ rest := by
      rw [hσ2, Function.update_of_ne hCD, Function.update_self]
    have e3 := (execLe_takeLoop n σ2 pre' rest h2U h2C hpre hUC hUD hCD).mono
      (show Stacks.space σ2 ≤ σ.space by omega)
    have hfin : Function.update (Function.update (Function.update σ2 U []) C rest) D
        (pre'.reverse ++ σ2 D) =
        Function.update (Function.update (Function.update σ U []) C rest) D
          ((b :: pre').reverse ++ σ D) := by
      have h2D : σ2 D = b :: σ D := by
        rw [hσ2, Function.update_self, hσ1, Function.update_of_ne hUD.symm]
      rw [h2D, List.reverse_cons, List.append_assoc, List.singleton_append]
      funext r
      by_cases hr : r = D
      · subst hr; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hr, Function.update_of_ne hr]
        by_cases hr' : r = C
        · subst hr'; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hr', Function.update_of_ne hr']
          by_cases hr'' : r = U
          · subst hr''; rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hr'', Function.update_of_ne hr'', hσ2,
              Function.update_of_ne hr, Function.update_of_ne hr', hσ1,
              Function.update_of_ne hr'']
    rw [hfin] at e3
    exact (ExecLe.loopT (by simp [hU']) (e1.seq e2) e3).mono_time (by rw [Nat.succ_mul]; omega)

/-- Split an index string (9 stacks, to be inlined with `ExecLe.rename_of_comp`): from
`κ ++ yb ++ nb` on stack `0` (kept) and the unary lengths `replicate |κ| true`,
`replicate |yb| true` on stacks `3`, `4` (consumed), it puts `κ` on `6`, `yb` on `7` and `nb` on
`1`; stacks `2` (copy work stack) and `5` are empty work stacks, `1`, `6`, `7` empty before. -/
def splitStmt : Stmt 9 :=
  .seq (Stmt.copy 0 1 2) (.seq (takeLoop 3 1 5) (.seq (Stmt.moveAll 5 6)
    (.seq (takeLoop 4 1 5) (Stmt.moveAll 5 7))))

/-- Distributing an index string `κ ++ yb ++ nb` to stacks `6` (`κ`), `7` (`yb`), and `1` (`nb`),
while emptying `3` and `4` and keeping stack `0` unchanged. -/
theorem execLe_splitStmt {σ : Stacks 9} {κ yb nb : BitString} (h0 : σ 0 = κ ++ yb ++ nb)
    (h1 : σ 1 = []) (h2 : σ 2 = []) (h3 : σ 3 = List.replicate κ.length true)
    (h4 : σ 4 = List.replicate yb.length true) (h5 : σ 5 = []) (h6 : σ 6 = [])
    (h7 : σ 7 = []) :
    ExecLe splitStmt σ
      (Function.update (Function.update (Function.update (Function.update
        (Function.update σ 3 []) 4 []) 6 κ) 7 yb) 1 nb)
      (σ.space + (σ 0).length)
      (13 * (σ.space + (σ 0).length) + 2 + (κ.length * 7 + 1) + (6 * κ.length + 1) +
        (yb.length * 7 + 1) + (6 * yb.length + 1)) := by
  have e1 := Stmt.execLe_copy_budget (r := (0 : Fin 9)) (r' := 1) (t := 2) (by decide)
    (by decide) (by decide) h2
  rw [h1, List.append_nil] at e1
  set σ1 := Function.update σ 1 (σ 0) with hσ1
  have sp1 := e1.toExec.space_le.2
  have e2 := execLe_takeLoop (U := (3 : Fin 9)) (C := 1) (D := 5) κ.length σ1 κ (yb ++ nb)
    (by rw [hσ1, Function.update_of_ne (by decide), h3])
    (by rw [hσ1, Function.update_self, h0, List.append_assoc]) rfl
  have e2' := e2.mono sp1
  set σ2 := Function.update (Function.update (Function.update σ1 3 []) 1 (yb ++ nb)) 5
    (κ.reverse ++ σ1 5) with hσ2
  have h25 : σ2 5 = κ.reverse := by
    rw [hσ2, Function.update_self, hσ1, Function.update_of_ne (by decide), h5, List.append_nil]
  have e3 := (Stmt.execLe_moveAll (r := (5 : Fin 9)) (r' := 6) (by decide) κ.reverse σ2
    h25).mono (show Stacks.space σ2 ≤ σ.space + (σ 0).length from
      (e2'.toExec.space_le.2))
  set σ3 := Function.update (Function.update σ2 5 []) 6 (κ.reverse.reverse ++ σ2 6) with hσ3
  have h34 : σ3 4 = List.replicate yb.length true := by
    rw [hσ3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hσ2,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hσ1, Function.update_of_ne (by decide), h4]
  have h31 : σ3 1 = yb ++ nb := by
    rw [hσ3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hσ2,
      Function.update_of_ne (by decide), Function.update_self]
  have e4 := (execLe_takeLoop (U := (4 : Fin 9)) (C := 1) (D := 5) yb.length σ3 yb nb h34 h31
    rfl).mono (show Stacks.space σ3 ≤ σ.space + (σ 0).length from e3.toExec.space_le.2)
  set σ4 := Function.update (Function.update (Function.update σ3 4 []) 1 nb) 5
    (yb.reverse ++ σ3 5) with hσ4
  have h45 : σ4 5 = yb.reverse := by
    rw [hσ4, Function.update_self, hσ3, Function.update_of_ne (by decide), Function.update_self,
      List.append_nil]
  have e5 := (Stmt.execLe_moveAll (r := (5 : Fin 9)) (r' := 7) (by decide) yb.reverse σ4
    h45).mono (show Stacks.space σ4 ≤ σ.space + (σ 0).length from e4.toExec.space_le.2)
  have hfin : Function.update (Function.update σ4 5 []) 7 (yb.reverse.reverse ++ σ4 7) =
      Function.update (Function.update (Function.update (Function.update
        (Function.update σ 3 []) 4 []) 6 κ) 7 yb) 1 nb := by
    funext j
    simp only [hσ4, hσ3, hσ2, hσ1, Function.update_apply, List.reverse_reverse]
    fin_cases j <;> simp [h0, h2, h5, h6, h7]
  rw [hfin] at e5
  exact (e1.seq (e2'.seq (e3.seq (e4.seq e5)))).mono_time
    (by simp only [List.length_reverse]; omega)

/-- Join an index string (9 stacks, to be inlined): `ρ` (stack `0`), `yb` (`1`), `nb` (`2`),
all kept, give `ρ ++ yb ++ nb` on the empty stack `3`, through the empty work stack `4`. -/
def joinStmt : Stmt 9 :=
  .seq (Stmt.copy 2 3 4) (.seq (Stmt.copy 1 3 4) (Stmt.copy 0 3 4))

/-- `joinStmt` concatenates `σ 0 ++ σ 1 ++ σ 2` onto stack `3`. -/
theorem execLe_joinStmt {σ : Stacks 9} (h3 : σ 3 = []) (h4 : σ 4 = []) :
    ExecLe joinStmt σ (Function.update σ 3 (σ 0 ++ σ 1 ++ σ 2))
      (σ.space + (σ 0).length + (σ 1).length + (σ 2).length)
      (39 * (σ.space + (σ 0).length + (σ 1).length + (σ 2).length) + 6) := by
  have e1 := Stmt.execLe_copy_budget (r := (2 : Fin 9)) (r' := 3) (t := 4) (by decide)
    (by decide) (by decide) h4
  rw [h3, List.append_nil] at e1
  set σ1 := Function.update σ 3 (σ 2) with hσ1
  have sp1 : Stacks.space σ1 = σ.space + (σ 2).length := by
    have := Stacks.space_update σ 3 (σ 2)
    rw [h3] at this
    simp only [List.length_nil, add_zero] at this
    rw [hσ1]; exact this
  have e2 := Stmt.execLe_copy_budget (r := (1 : Fin 9)) (r' := 3) (t := 4) (σ := σ1) (by decide)
    (by decide) (by decide) (by rw [hσ1, Function.update_of_ne (by decide), h4])
  have h11 : σ1 1 = σ 1 := by rw [hσ1, Function.update_of_ne (by decide)]
  have h13 : σ1 3 = σ 2 := by rw [hσ1, Function.update_self]
  rw [h11, h13] at e2
  set σ2 := Function.update σ1 3 (σ 1 ++ σ 2) with hσ2
  have sp2 : Stacks.space σ2 = σ.space + (σ 1).length + (σ 2).length := by
    have := Stacks.space_update σ1 3 (σ 1 ++ σ 2)
    rw [h13, List.length_append] at this
    rw [hσ2]; omega
  have e3 := Stmt.execLe_copy_budget (r := (0 : Fin 9)) (r' := 3) (t := 4) (σ := σ2) (by decide)
    (by decide) (by decide)
    (by rw [hσ2, Function.update_of_ne (by decide), hσ1, Function.update_of_ne (by decide), h4])
  have h20 : σ2 0 = σ 0 := by
    rw [hσ2, Function.update_of_ne (by decide), hσ1, Function.update_of_ne (by decide)]
  have h23 : σ2 3 = σ 1 ++ σ 2 := by rw [hσ2, Function.update_self]
  rw [h20, h23] at e3
  have hfin : Function.update σ2 3 (σ 0 ++ (σ 1 ++ σ 2)) =
      Function.update σ 3 (σ 0 ++ σ 1 ++ σ 2) := by
    rw [hσ2, hσ1, Function.update_idem, Function.update_idem, List.append_assoc]
  rw [hfin] at e3
  rw [sp1] at e2
  rw [sp2] at e3
  have e1' := (e1.mono (show σ.space + (σ 2).length ≤
      σ.space + (σ 0).length + (σ 1).length + (σ 2).length by omega)).mono_time
    (show 13 * (σ.space + (σ 2).length) + 2 ≤
      13 * (σ.space + (σ 0).length + (σ 1).length + (σ 2).length) + 2 by omega)
  have e2' := (e2.mono (show σ.space + (σ 2).length + (σ 1).length ≤
      σ.space + (σ 0).length + (σ 1).length + (σ 2).length by omega)).mono_time
    (show 13 * (σ.space + (σ 2).length + (σ 1).length) + 2 ≤
      13 * (σ.space + (σ 0).length + (σ 1).length + (σ 2).length) + 2 by omega)
  have e3' := (e3.mono (show σ.space + (σ 1).length + (σ 2).length + (σ 0).length ≤
      σ.space + (σ 0).length + (σ 1).length + (σ 2).length by omega)).mono_time
    (show 13 * (σ.space + (σ 1).length + (σ 2).length + (σ 0).length) + 2 ≤
      13 * (σ.space + (σ 0).length + (σ 1).length + (σ 2).length) + 2 by omega)
  exact (e1'.seq (e2'.seq e3')).mono_time (by omega)

/-- A score step (9 stacks, to be inlined): from the score `yb` (stack `0`, kept), a cost `cb`
(stack `1`, consumed) and the budget `eb` (stack `2`, kept), all of width `W`, it leaves the
new score `addBits false yb cb` (= `y + c`, no overflow) on stack `3` and the flag
`[decide (y + c ≤ E)]` on stack `4`; stacks `5`–`7` are empty work stacks. -/
def scoreStmt : Stmt 9 :=
  .seq (Stmt.copy 0 3 5) (.seq (Stmt.addInto 3 1 6 7) (.seq (Stmt.copy 3 1 5)
    (.seq (Stmt.copy 2 6 5) (Stmt.cmpInto 1 6 4))))

/-- For a score `yb`, cost `cb` and budget `eb` of equal length on stacks `0`, `1`, `2`,
with `binVal yb + binVal cb < 2 ^ yb.length` and stacks `3`–`7` empty, `scoreStmt` reaches,
within space `σ.space + 3 * |yb| + 2` and some number of steps, the state with stack `1` emptied,
`addBits false yb cb` on `3` and `[decide (binVal yb + binVal cb ≤ binVal eb)]` on `4`. -/
theorem execLe_scoreStmt {σ : Stacks 9} {yb cb eb : BitString} (h0 : σ 0 = yb) (h1 : σ 1 = cb)
    (h2 : σ 2 = eb) (h3 : σ 3 = []) (h4 : σ 4 = []) (h5 : σ 5 = []) (h6 : σ 6 = [])
    (h7 : σ 7 = []) (hl1 : cb.length = yb.length) (hl2 : eb.length = yb.length)
    (hov : binVal yb + binVal cb < 2 ^ yb.length) :
    ∃ T, ExecLe scoreStmt σ
      (Function.update (Function.update (Function.update σ 1 []) 3 (addBits false yb cb)) 4
        [decide (binVal yb + binVal cb ≤ binVal eb)])
      (σ.space + 3 * yb.length + 2) T := by
  have hsum : binVal (addBits false yb cb) = binVal yb + binVal cb :=
    binVal_addBits_of_lt yb cb hl1.symm hov
  have hlen : (addBits false yb cb).length = yb.length := length_addBits false yb cb hl1.symm
  -- 1. `3 := yb`
  have e1 := Stmt.execLe_copy_budget (r := (0 : Fin 9)) (r' := 3) (t := 5) (by decide)
    (by decide) (by decide) h5
  rw [h3, List.append_nil, h0] at e1
  set σ1 := Function.update σ 3 yb with hσ1
  have sp1 : Stacks.space σ1 = σ.space + yb.length := by
    have := Stacks.space_update σ 3 yb
    rw [h3] at this
    simp only [List.length_nil, add_zero] at this
    rw [hσ1]; exact this
  -- 2. `3 := yb + cb`, `1 := []`
  have e2 := Stmt.execLe_addInto (A := (3 : Fin 9)) (B := 1) (Cy := 6) (R := 7) (σ := σ1)
    (l := yb) (m := cb) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hl1.symm (by rw [hσ1, Function.update_self])
    (by rw [hσ1, Function.update_of_ne (by decide), h1])
    (by rw [hσ1, Function.update_of_ne (by decide), h6])
    (by rw [hσ1, Function.update_of_ne (by decide), h7])
  set σ2 := Function.update (Function.update σ1 3 (addBits false yb cb)) 1 [] with hσ2
  have sp2 : Stacks.space σ2 + cb.length = Stacks.space σ1 := by
    have a1 := Stacks.space_update σ1 3 (addBits false yb cb)
    have a2 := Stacks.space_update (Function.update σ1 3 (addBits false yb cb)) 1 []
    have h13 : σ1 3 = yb := by rw [hσ1, Function.update_self]
    have h11 : (Function.update σ1 3 (addBits false yb cb)) 1 = cb := by
      rw [Function.update_of_ne (by decide), hσ1, Function.update_of_ne (by decide), h1]
    rw [h13, hlen] at a1
    rw [h11] at a2
    simp only [List.length_nil, add_zero] at a2
    rw [hσ2]; omega
  -- 3. `1 := yb + cb`
  have e3 := Stmt.execLe_copy_budget (r := (3 : Fin 9)) (r' := 1) (t := 5) (σ := σ2) (by decide)
    (by decide) (by decide)
    (by rw [hσ2, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hσ1,
      Function.update_of_ne (by decide), h5])
  have h23 : σ2 3 = addBits false yb cb := by
    rw [hσ2, Function.update_of_ne (by decide), Function.update_self]
  have h21 : σ2 1 = [] := by rw [hσ2, Function.update_self]
  rw [h23, h21, List.append_nil] at e3
  set σ3 := Function.update σ2 1 (addBits false yb cb) with hσ3
  have sp3 : Stacks.space σ3 = Stacks.space σ2 + yb.length := by
    have := Stacks.space_update σ2 1 (addBits false yb cb)
    rw [h21, hlen] at this
    simp only [List.length_nil, add_zero] at this
    rw [hσ3]; exact this
  -- 4. `6 := eb`
  have e4 := Stmt.execLe_copy_budget (r := (2 : Fin 9)) (r' := 6) (t := 5) (σ := σ3) (by decide)
    (by decide) (by decide)
    (by rw [hσ3, Function.update_of_ne (by decide), hσ2, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hσ1, Function.update_of_ne (by decide), h5])
  have h32 : σ3 2 = eb := by
    rw [hσ3, Function.update_of_ne (by decide), hσ2, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hσ1, Function.update_of_ne (by decide), h2]
  have h36 : σ3 6 = [] := by
    rw [hσ3, Function.update_of_ne (by decide), hσ2, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hσ1, Function.update_of_ne (by decide), h6]
  rw [h32, h36, List.append_nil] at e4
  set σ4 := Function.update σ3 6 eb with hσ4
  have sp4 : Stacks.space σ4 = Stacks.space σ3 + yb.length := by
    have := Stacks.space_update σ3 6 eb
    rw [h36, hl2] at this
    simp only [List.length_nil, add_zero] at this
    rw [hσ4]; exact this
  -- 5. `4 := [y + c ≤ E]`, `1 := []`, `6 := []`
  have e5 := Stmt.execLe_cmpInto (A := (1 : Fin 9)) (B := 6) (F := 4) (σ := σ4)
    (l := addBits false yb cb) (m := eb) (by decide) (by decide) (by decide)
    (by rw [hlen, hl2]) (by rw [hσ4, Function.update_of_ne (by decide), hσ3, Function.update_self])
    (by rw [hσ4, Function.update_self])
    (by rw [hσ4, Function.update_of_ne (by decide), hσ3, Function.update_of_ne (by decide), hσ2,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), hσ1,
      Function.update_of_ne (by decide), h4])
  have hcmp : cmpBits true (addBits false yb cb) eb =
      decide (binVal yb + binVal cb ≤ binVal eb) := by
    rw [Bool.eq_iff_iff, cmpBits_true_iff _ _ (by rw [hlen, hl2]), hsum, decide_eq_true_eq]
  rw [hcmp] at e5
  have hfin : Function.update (Function.update (Function.update σ4 1 []) 6 []) 4
      [decide (binVal yb + binVal cb ≤ binVal eb)] =
      Function.update (Function.update (Function.update σ 1 []) 3 (addBits false yb cb)) 4
        [decide (binVal yb + binVal cb ≤ binVal eb)] := by
    funext j
    simp only [hσ4, hσ3, hσ2, hσ1, Function.update_apply]
    fin_cases j <;> simp [h6]
  rw [hfin] at e5
  refine ⟨_, ((e1.mono ?_).seq ((e2.mono ?_).seq ((e3.mono ?_).seq ((e4.mono ?_).seq
    (e5.mono ?_)))))⟩ <;> omega

/-! ### Calling a key routine on a key held on another stack -/

/-- Copy the key on `K` into the routine's argument stack `A` (through `t`), run `s`, clear `A`. -/
def callKey {k : ℕ} (K A t : Fin k) (s : Stmt k) : Stmt k :=
  .seq (Stmt.copy K A t) (.seq s (Stmt.clear A))

/-- If `s` is a `KeyBitRoutine` for `bit` and `|σ K| = L`, then `callKey K A t s`
(copy `σ K` to `A`, run `s`, clear `A`) turns the empty `F` into `[bit (σ K)]` and changes
nothing else, within space `σ.space + L + B`. -/
theorem execLe_callKey {k : ℕ} {K A t I F : Fin k} (hKA : K ≠ A) (hKt : K ≠ t) (hAt : A ≠ t)
    (hIA : I ≠ A) (hFA : F ≠ A) {s : Stmt k} {x : BitString} {L kR B : ℕ} {bit : BitString → Bool}
    (hs : KeyBitRoutine s x L kR I A F B bit) (hAk : A.val < kR) {σ : Stacks k}
    (hI : σ I = x) (hA : σ A = []) (ht : σ t = []) (hF : σ F = []) (hK : (σ K).length = L)
    (hw : ∀ j : Fin k, kR ≤ j.val → σ j = []) :
    ExecLe (callKey K A t s) σ (Function.update σ F [bit (σ K)]) (σ.space + L + B)
      (13 * (σ.space + L) + 2 + B + (3 * L + 1)) := by
  have e1 := Stmt.execLe_copy_budget hKA hKt hAt ht
  rw [hA, List.append_nil, hK] at e1
  set σ1 := Function.update σ A (σ K) with hσ1
  have sp1 : Stacks.space σ1 = σ.space + L := by
    have := Stacks.space_update σ A (σ K)
    rw [hA, hK] at this
    simp only [List.length_nil, add_zero] at this
    rw [hσ1]; exact this
  have e2 := hs σ1 (by rw [hσ1, Function.update_of_ne hIA, hI])
    (by rw [hσ1, Function.update_self, hK]) (by rw [hσ1, Function.update_of_ne hFA, hF])
    (fun j hj => by
      rw [hσ1, Function.update_of_ne (fun h => by subst h; omega), hw j hj])
  rw [sp1] at e2
  have h1A : σ1 A = σ K := by rw [hσ1, Function.update_self]
  set σ2 := Function.update σ1 F [bit (σ1 A)] with hσ2
  have h2A : σ2 A = σ K := by rw [hσ2, Function.update_of_ne hFA.symm, h1A]
  have sp2 := e2.toExec.space_le.2
  have e3 := ExecLe.of_execT (Stmt.execT_clear A (σ K) σ2 h2A)
  rw [hK] at e3
  have hfin : Function.update σ2 A [] = Function.update σ F [bit (σ K)] := by
    rw [hσ2, h1A, hσ1]
    funext j
    by_cases hj : j = A
    · subst hj
      rw [Function.update_self, Function.update_of_ne hFA.symm, hA]
    · rw [Function.update_of_ne hj]
      by_cases hj' : j = F
      · subst hj'; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj', Function.update_of_ne hj', Function.update_of_ne hj]
  rw [hfin] at e3
  exact ((e1.mono (by omega)).seq (e2.seq (e3.mono sp2))).mono_time (by omega)

/-- A routine of two key codes with a string result (`PairBitRoutine` is the case
`g κ κ' = [bit κ κ']`, `PairNumRoutine` the case `g κ κ' = bitsOf W (num κ κ')`, both
definitionally). -/
def PairRoutine {k : ℕ} (s : Stmt k) (x : BitString) (L kR : ℕ) (I A A' F : Fin k) (B : ℕ)
    (g : BitString → BitString → BitString) : Prop :=
  ∀ τ : Stacks k, τ I = x → (τ A).length = L → (τ A').length = L → τ F = [] →
    (∀ j : Fin k, kR ≤ j.val → τ j = []) →
    ExecLe s τ (Function.update τ F (g (τ A) (τ A'))) (τ.space + B) B

/-- Convert a bit-evaluating pair routine to a general pair routine. -/
theorem PairBitRoutine.pair {k : ℕ} {s : Stmt k} {x : BitString} {L kR : ℕ} {I A A' F : Fin k}
    {B : ℕ} {bit : BitString → BitString → Bool} (h : PairBitRoutine s x L kR I A A' F B bit) :
    PairRoutine s x L kR I A A' F B fun κ κ' => [bit κ κ'] := h

/-- Convert a numeric-evaluating pair routine to a general pair routine. -/
theorem PairNumRoutine.pair {k : ℕ} {s : Stmt k} {x : BitString} {L W kR : ℕ} {I A A' F : Fin k}
    {B : ℕ} {num : BitString → BitString → ℕ} (h : PairNumRoutine s x L W kR I A A' F B num) :
    PairRoutine s x L kR I A A' F B fun κ κ' => bitsOf W (num κ κ') := h

/-- Copy the keys on `K`, `K'` into the argument stacks `A`, `A'`, run `s`, clear `A`, `A'`. -/
def callPair {k : ℕ} (K K' A A' t : Fin k) (s : Stmt k) : Stmt k :=
  .seq (Stmt.copy K A t) (.seq (Stmt.copy K' A' t) (.seq s (.seq (Stmt.clear A) (Stmt.clear A'))))

/-- If `s` is a `PairRoutine` for `g`, then `callPair K K' A A' t s` turns the empty `F`
into `g (σ K) (σ K')` and changes nothing else, within space `σ.space + L + L + B`. -/
theorem execLe_callPair {k : ℕ} {K K' A A' t I F : Fin k} (hKA : K ≠ A) (hKt : K ≠ t)
    (hAt : A ≠ t) (hK'A' : K' ≠ A') (hK't : K' ≠ t) (hA't : A' ≠ t) (hK'A : K' ≠ A)
    (hAA' : A ≠ A') (hIA : I ≠ A) (hIA' : I ≠ A') (hFA : F ≠ A) (hFA' : F ≠ A')
    {s : Stmt k} {x : BitString} {L kR B : ℕ} {g : BitString → BitString → BitString}
    (hs : PairRoutine s x L kR I A A' F B g) (hAk : A.val < kR) (hA'k : A'.val < kR)
    {σ : Stacks k} (hI : σ I = x) (hA : σ A = []) (hA' : σ A' = []) (ht : σ t = [])
    (hF : σ F = []) (hK : (σ K).length = L) (hK' : (σ K').length = L)
    (hw : ∀ j : Fin k, kR ≤ j.val → σ j = []) :
    ExecLe (callPair K K' A A' t s) σ (Function.update σ F (g (σ K) (σ K')))
      (σ.space + L + L + B)
      (13 * (σ.space + L) + 2 +
        (13 * (σ.space + L + L) + 2 + (B + (3 * L + 1 + (3 * L + 1))))) := by
  have e1 := Stmt.execLe_copy_budget hKA hKt hAt ht
  rw [hA, List.append_nil, hK] at e1
  set σ1 := Function.update σ A (σ K) with hσ1
  have sp1 : Stacks.space σ1 = σ.space + L := by
    have := Stacks.space_update σ A (σ K)
    rw [hA, hK] at this
    simp only [List.length_nil, add_zero] at this
    rw [hσ1]; exact this
  have e2 := Stmt.execLe_copy_budget (σ := σ1) hK'A' hK't hA't
    (by rw [hσ1, Function.update_of_ne hAt.symm, ht])
  have h1K' : σ1 K' = σ K' := by rw [hσ1, Function.update_of_ne hK'A]
  have h1A' : σ1 A' = [] := by rw [hσ1, Function.update_of_ne hAA'.symm, hA']
  rw [h1K', h1A', List.append_nil, hK'] at e2
  set σ2 := Function.update σ1 A' (σ K') with hσ2
  have sp2 : Stacks.space σ2 = σ.space + L + L := by
    have := Stacks.space_update σ1 A' (σ K')
    rw [h1A', hK'] at this
    simp only [List.length_nil, add_zero] at this
    rw [hσ2]; omega
  have h2A : σ2 A = σ K := by rw [hσ2, Function.update_of_ne hAA', hσ1, Function.update_self]
  have h2A' : σ2 A' = σ K' := by rw [hσ2, Function.update_self]
  have e3 := hs σ2 (by rw [hσ2, Function.update_of_ne hIA', hσ1, Function.update_of_ne hIA, hI])
    (by rw [h2A, hK]) (by rw [h2A', hK'])
    (by rw [hσ2, Function.update_of_ne hFA', hσ1, Function.update_of_ne hFA, hF])
    (fun j hj => by
      rw [hσ2, Function.update_of_ne (fun h => by subst h; omega), hσ1,
        Function.update_of_ne (fun h => by subst h; omega), hw j hj])
  rw [sp2, h2A, h2A'] at e3
  set σ3 := Function.update σ2 F (g (σ K) (σ K')) with hσ3
  have sp3 := e3.toExec.space_le.2
  have h3A : σ3 A = σ K := by rw [hσ3, Function.update_of_ne hFA.symm, h2A]
  have e4 := ExecLe.of_execT (Stmt.execT_clear A (σ K) σ3 h3A)
  set σ4 := Function.update σ3 A [] with hσ4
  have sp4 : Stacks.space σ4 ≤ Stacks.space σ3 := Stacks.space_update_le σ3 A [] (by simp)
  have h4A' : σ4 A' = σ K' := by
    rw [hσ4, Function.update_of_ne hAA'.symm, hσ3, Function.update_of_ne hFA'.symm, h2A']
  have e5 := ExecLe.of_execT (Stmt.execT_clear A' (σ K') σ4 h4A')
  have hfin : Function.update σ4 A' [] = Function.update σ F (g (σ K) (σ K')) := by
    rw [hσ4, hσ3, hσ2, hσ1]
    funext j
    by_cases hj : j = A'
    · subst hj
      rw [Function.update_self, Function.update_of_ne hFA'.symm, hA']
    · rw [Function.update_of_ne hj]
      by_cases hj2 : j = A
      · subst hj2
        rw [Function.update_self, Function.update_of_ne hFA.symm, hA]
      · rw [Function.update_of_ne hj2]
        by_cases hj3 : j = F
        · subst hj3; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hj3, Function.update_of_ne hj3, Function.update_of_ne hj,
            Function.update_of_ne hj2]
  rw [hfin] at e5
  rw [sp1] at e2
  rw [hK] at e4
  rw [hK'] at e5
  exact (e1.mono (by omega)).seq ((e2.mono (by omega)).seq (e3.seq
    ((e4.mono sp3).seq (e5.mono (sp4.trans sp3)))))

/-! ### Inlining the 9-stack plumbing routines into the driver's stacks -/

/-- The total space of `τ` splits into the space on the image of `f` and the space on the rest. -/
theorem space_comp_add_rest {k : ℕ} {f : Fin 9 → Fin k} (hf : Function.Injective f)
    (τ : Stacks k) : Stacks.space (fun r => τ (f r)) + Stacks.rest f τ = τ.space := by
  have := Stacks.space_extend hf (fun r => τ (f r)) τ
  rw [Stacks.extend_comp_self hf τ] at this
  omega

/-- Extending an updated 9-stack state is equivalent to updating the extended state
at the mapped index. -/
theorem extend_update_comp {k : ℕ} {f : Fin 9 → Fin k} (hf : Function.Injective f)
    (σ : Stacks 9) (τ : Stacks k) (r : Fin 9) (v : BitString) :
    Function.extend f (Function.update σ r v) τ = Function.update (Function.extend f σ τ) (f r) v :=
  (Stacks.update_extend hf σ τ r v).symm

/-- `splitStmt` inlined along `f`. -/
theorem execLe_splitK {k : ℕ} {f : Fin 9 → Fin k} (hf : Function.Injective f) {τ : Stacks k}
    {κ yb nb : BitString} (h0 : τ (f 0) = κ ++ yb ++ nb) (h1 : τ (f 1) = []) (h2 : τ (f 2) = [])
    (h3 : τ (f 3) = List.replicate κ.length true) (h4 : τ (f 4) = List.replicate yb.length true)
    (h5 : τ (f 5) = []) (h6 : τ (f 6) = []) (h7 : τ (f 7) = []) :
    ∃ T, ExecLe (splitStmt.rename f) τ
      (Function.update (Function.update (Function.update (Function.update
        (Function.update τ (f 3) []) (f 4) []) (f 6) κ) (f 7) yb) (f 1) nb)
      (τ.space + (τ (f 0)).length) T := by
  have e := execLe_splitStmt (σ := fun r => τ (f r)) h0 h1 h2 h3 h4 h5 h6 h7
  have r := ExecLe.rename_of_comp hf e
  simp only [extend_update_comp hf, Stacks.extend_comp_self hf] at r
  have := space_comp_add_rest hf τ
  exact ⟨_, r.mono (by omega)⟩

/-- `joinStmt` inlined along `f`. -/
theorem execLe_joinK {k : ℕ} {f : Fin 9 → Fin k} (hf : Function.Injective f) {τ : Stacks k}
    (h3 : τ (f 3) = []) (h4 : τ (f 4) = []) :
    ∃ T, ExecLe (joinStmt.rename f) τ
      (Function.update τ (f 3) (τ (f 0) ++ τ (f 1) ++ τ (f 2)))
      (τ.space + (τ (f 0)).length + (τ (f 1)).length + (τ (f 2)).length) T := by
  have e := execLe_joinStmt (σ := fun r => τ (f r)) h3 h4
  have r := ExecLe.rename_of_comp hf e
  simp only [extend_update_comp hf, Stacks.extend_comp_self hf] at r
  have := space_comp_add_rest hf τ
  exact ⟨_, r.mono (by omega)⟩

/-- `scoreStmt` inlined along `f`. -/
theorem execLe_scoreK {k : ℕ} {f : Fin 9 → Fin k} (hf : Function.Injective f) {τ : Stacks k}
    {yb cb eb : BitString} (h0 : τ (f 0) = yb) (h1 : τ (f 1) = cb) (h2 : τ (f 2) = eb)
    (h3 : τ (f 3) = []) (h4 : τ (f 4) = []) (h5 : τ (f 5) = []) (h6 : τ (f 6) = [])
    (h7 : τ (f 7) = []) (hl1 : cb.length = yb.length) (hl2 : eb.length = yb.length)
    (hov : binVal yb + binVal cb < 2 ^ yb.length) :
    ∃ T, ExecLe (scoreStmt.rename f) τ
      (Function.update (Function.update (Function.update τ (f 1) []) (f 3) (addBits false yb cb))
        (f 4) [decide (binVal yb + binVal cb ≤ binVal eb)])
      (τ.space + 3 * yb.length + 2) T := by
  obtain ⟨T, e⟩ := execLe_scoreStmt (σ := fun r => τ (f r)) h0 h1 h2 h3 h4 h5 h6 h7 hl1 hl2 hov
  have r := ExecLe.rename_of_comp hf e
  simp only [extend_update_comp hf, Stacks.extend_comp_self hf] at r
  have := space_comp_add_rest hf τ
  exact ⟨_, r.mono (by omega)⟩

/-- Call a key routine on the key on `K` and move its result bit from `F` to `G`. -/
def callBit {k : ℕ} (K A t F G : Fin k) (s : Stmt k) : Stmt k :=
  .seq (callKey K A t s) (Stmt.moveBit F G)

/-- If `s` is a `KeyBitRoutine` for `bit` and `|σ K| = L`, then `callBit K A t F G s`
evaluates the bit on `F` and moves it to `G`. -/
theorem execLe_callBit {k : ℕ} {K A t I F G : Fin k} (hKA : K ≠ A) (hKt : K ≠ t) (hAt : A ≠ t)
    (hIA : I ≠ A) (hFA : F ≠ A) (hFG : F ≠ G) {s : Stmt k} {x : BitString} {L kR B : ℕ}
    {bit : BitString → Bool} (hs : KeyBitRoutine s x L kR I A F B bit) (hAk : A.val < kR)
    {σ : Stacks k} (hI : σ I = x) (hA : σ A = []) (ht : σ t = []) (hF : σ F = [])
    (hG : σ G = []) (hK : (σ K).length = L) (hw : ∀ j : Fin k, kR ≤ j.val → σ j = []) :
    ExecLe (callBit K A t F G s) σ (Function.update σ G [bit (σ K)]) (σ.space + L + B)
      (13 * (σ.space + L) + 2 + B + (3 * L + 1) + 4) := by
  have e1 := execLe_callKey hKA hKt hAt hIA hFA hs hAk hI hA ht hF hK hw
  have sp1 := e1.toExec.space_le.2
  have e2 := Stmt.execLe_moveBit hFG (σ := Function.update σ F [bit (σ K)]) (b := bit (σ K))
    (l := []) (by rw [Function.update_self])
  rw [Function.update_of_ne hFG.symm, hG] at e2
  have hfin' : Function.update (Function.update (Function.update σ F [bit (σ K)]) F []) G
      [bit (σ K)] = Function.update σ G [bit (σ K)] := by
    funext j
    by_cases hj : j = G
    · subst hj; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_idem]
      by_cases hj' : j = F
      · subst hj'; rw [Function.update_self, hF]
      · rw [Function.update_of_ne hj']
  rw [hfin'] at e2
  exact e1.seq (e2.mono sp1)

/-- **An `any` loop over all keys calling a key routine** (the composition pattern of the
driver, end to end): `forAny` with the body `callBit` leaves `[(allBits L).any bit]` on `Acc`. -/
theorem execLe_forAny_callBit {k : ℕ} {C t Cy G Acc A I F : Fin k} (hCt : C ≠ t)
    (hCCy : C ≠ Cy) (htCy : t ≠ Cy) (hGA : G ≠ Acc) (hAC : Acc ≠ C) (hACy : Acc ≠ Cy)
    (hGC : G ≠ C) (hGCy : G ≠ Cy) (htA : t ≠ Acc) (hCA : C ≠ A) (hAt : A ≠ t) (hIA : I ≠ A)
    (hFA : F ≠ A) (hFG : F ≠ G) (hIC : I ≠ C) (hICy : I ≠ Cy) (hIAcc : I ≠ Acc)
    (hACy' : A ≠ Cy) (hAAcc : A ≠ Acc) (hFC : F ≠ C) (hFCy : F ≠ Cy) (hFAcc : F ≠ Acc)
    {s : Stmt k} {x : BitString} {L kR B : ℕ} {bit : BitString → Bool}
    (hs : KeyBitRoutine s x L kR I A F B bit) (hAk : A.val < kR) (hCk : C.val < kR)
    (hCyk : Cy.val < kR) (hAcck : Acc.val < kR) (σ0 : Stacks k) (hI : σ0 I = x)
    (hA : σ0 A = []) (ht : σ0 t = []) (hF : σ0 F = []) (hG : σ0 G = [])
    (hC : σ0 C = bitsOf L 0) (hCy : σ0 Cy = [false]) (hAcc : σ0 Acc = [false])
    (hw : ∀ j : Fin k, kR ≤ j.val → σ0 j = []) :
    ∃ σ', ExecLe (forAny C t Cy G Acc (callBit C A t F G s)) σ0 σ' (σ0.space + L + B)
      (2 ^ L * (13 * (σ0.space + L) + 2 + B + (3 * L + 1) + 4 + 5 + 10 * (σ0.space + L + B) + 20)
        + 1) ∧
      σ' = Function.update (Function.update σ0 Acc [(allBits L).any bit]) Cy [true] := by
  refine execLe_forAny hCt hCCy htCy hGA hAC hACy hGC hGCy htA L (σ0.space + L + B)
    (13 * (σ0.space + L) + 2 + B + (3 * L + 1) + 4) bit σ0 ?_ hC hCy ht hG hAcc
  intro σ hfr hlC hσCy hlAcc
  have hsp : σ.space = σ0.space := by
    apply space_eq_of_length
    intro r
    by_cases hr1 : r = C
    · subst hr1; rw [hlC, hC, length_bitsOf]
    · by_cases hr2 : r = Cy
      · subst hr2; rw [hσCy, hCy]
      · by_cases hr3 : r = Acc
        · subst hr3; rw [hlAcc, hAcc]; rfl
        · rw [hfr r hr1 hr2 hr3]
  have e := execLe_callBit hCA hCt hAt hIA hFA hFG hs hAk (σ := σ)
    (by rw [hfr I hIC hICy hIAcc, hI]) (by rw [hfr A hCA.symm hACy' hAAcc, hA])
    (by rw [hfr t hCt.symm htCy htA, ht]) (by rw [hfr F hFC hFCy hFAcc, hF])
    (by rw [hfr G hGC hGCy hGA, hG]) hlC
    (fun j hj => by
      rw [hfr j (fun h => by subst h; omega) (fun h => by subst h; omega)
        (fun h => by subst h; omega), hw j hj])
  rw [hsp] at e
  exact e

/-- Call a pair routine with a bit result on the keys on `K`, `K'`, and move the bit from `F`
to `G`. -/
def callPairBit {k : ℕ} (K K' A A' t F G : Fin k) (s : Stmt k) : Stmt k :=
  .seq (callPair K K' A A' t s) (Stmt.moveBit F G)

/-- If `s` is a `PairBitRoutine` for `bit`, then `callPairBit K K' A A' t F G s`
evaluates the pair bit on `F` and moves it to `G`. -/
theorem execLe_callPairBit {k : ℕ} {K K' A A' t I F G : Fin k} (hKA : K ≠ A) (hKt : K ≠ t)
    (hAt : A ≠ t) (hK'A' : K' ≠ A') (hK't : K' ≠ t) (hA't : A' ≠ t) (hK'A : K' ≠ A)
    (hAA' : A ≠ A') (hIA : I ≠ A) (hIA' : I ≠ A') (hFA : F ≠ A) (hFA' : F ≠ A') (hFG : F ≠ G)
    {s : Stmt k} {x : BitString} {L kR B : ℕ} {bit : BitString → BitString → Bool}
    (hs : PairBitRoutine s x L kR I A A' F B bit) (hAk : A.val < kR) (hA'k : A'.val < kR)
    {σ : Stacks k} (hI : σ I = x) (hA : σ A = []) (hA' : σ A' = []) (ht : σ t = [])
    (hF : σ F = []) (hG : σ G = []) (hK : (σ K).length = L) (hK' : (σ K').length = L)
    (hw : ∀ j : Fin k, kR ≤ j.val → σ j = []) :
    ExecLe (callPairBit K K' A A' t F G s) σ (Function.update σ G [bit (σ K) (σ K')])
      (σ.space + L + L + B)
      (13 * (σ.space + L) + 2 + (13 * (σ.space + L + L) + 2 + (B + (3 * L + 1 + (3 * L + 1))))
        + 4) := by
  have e1 := execLe_callPair hKA hKt hAt hK'A' hK't hA't hK'A hAA' hIA hIA' hFA hFA'
    hs.pair hAk hA'k hI hA hA' ht hF hK hK' hw
  have sp1 := e1.toExec.space_le.2
  have e2 := Stmt.execLe_moveBit hFG (σ := Function.update σ F [bit (σ K) (σ K')])
    (b := bit (σ K) (σ K')) (l := []) (by rw [Function.update_self])
  rw [Function.update_of_ne hFG.symm, hG] at e2
  have hfin : Function.update (Function.update (Function.update σ F [bit (σ K) (σ K')]) F []) G
      [bit (σ K) (σ K')] = Function.update σ G [bit (σ K) (σ K')] := by
    funext j
    by_cases hj : j = G
    · subst hj; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_idem]
      by_cases hj' : j = F
      · subst hj'; rw [Function.update_self, hF]
      · rw [Function.update_of_ne hj']
  rw [hfin] at e2
  exact e1.seq (e2.mono sp1)

/-- **A filter loop over all keys calling a key routine**, end to end: `forFilter` with the
body `callBit` prepends to the table on `Tn` a list of exactly the keys `κ` of length `L` with
`bit κ`. -/
theorem execLe_forFilter_callBit {k : ℕ} {C t Cy tw G Tn A I F : Fin k} (hCt : C ≠ t)
    (hCCy : C ≠ Cy) (htCy : t ≠ Cy) (hCtw : C ≠ tw) (hCTn : C ≠ Tn) (htwTn : tw ≠ Tn)
    (hGC : G ≠ C) (hGtw : G ≠ tw) (hGTn : G ≠ Tn) (hGCy : G ≠ Cy) (htwCy : tw ≠ Cy)
    (hTnCy : Tn ≠ Cy) (htTn : t ≠ Tn) (hCA : C ≠ A) (hAt : A ≠ t) (hIA : I ≠ A) (hFA : F ≠ A)
    (hFG : F ≠ G) (hIC : I ≠ C) (hICy : I ≠ Cy) (hITn : I ≠ Tn) (hACy : A ≠ Cy) (hATn : A ≠ Tn)
    (hFC : F ≠ C) (hFCy : F ≠ Cy) (hFTn : F ≠ Tn)
    {s : Stmt k} {x : BitString} {L kR B : ℕ} {bit : BitString → Bool}
    (hs : KeyBitRoutine s x L kR I A F B bit) (hAk : A.val < kR) (hCk : C.val < kR)
    (hCyk : Cy.val < kR) (hTnk : Tn.val < kR) (σ0 : Stacks k) (L0 : List BitString)
    (hI : σ0 I = x) (hA : σ0 A = []) (ht : σ0 t = []) (htw : σ0 tw = []) (hF : σ0 F = [])
    (hG : σ0 G = []) (hC : σ0 C = bitsOf L 0) (hCy : σ0 Cy = [false])
    (hTn : σ0 Tn = Stacks.encList L0) (hw : ∀ j : Fin k, kR ≤ j.val → σ0 j = []) :
    ∃ (σ' : Stacks k) (Lw : List BitString), (∀ s, s ∈ Lw ↔ s.length = L ∧ bit s = true) ∧
      (∀ s ∈ Lw, s.length = L) ∧
      ExecLe (forFilter C t Cy tw G Tn (callBit C A t F G s)) σ0 σ'
        (σ0.space + 2 ^ L * (2 * L + 1) + 2 * L + 2 + B)
        (2 ^ L * (13 * (σ0.space + 2 ^ L * (2 * L + 1) + 2 * L + 2 + B + L) + 2 + B +
          (3 * L + 1) + 4 +
          (tabWrite C tw Tn).budget (σ0.space + 2 ^ L * (2 * L + 1) + 2 * L + 2 + B)
          + 3 + 10 * (σ0.space + 2 ^ L * (2 * L + 1) + 2 * L + 2 + B) + 20) + 1) ∧
      σ' = Function.update (Function.update σ0 Tn (Stacks.encList (Lw ++ L0))) Cy [true] := by
  refine execLe_forFilter hCt hCCy htCy hCtw hCTn htwTn hGC hGtw hGTn hGCy htwCy hTnCy htTn L B
    (13 * (σ0.space + 2 ^ L * (2 * L + 1) + 2 * L + 2 + B + L) + 2 + B + (3 * L + 1) + 4)
    bit σ0 L0 ?_ hC hCy ht htw hG hTn
  intro σ hfr hlC hσCy hsp
  have e := execLe_callBit hCA hCt hAt hIA hFA hFG hs hAk (σ := σ)
    (by rw [hfr I hIC hICy hITn, hI]) (by rw [hfr A hCA.symm hACy hATn, hA])
    (by rw [hfr t hCt.symm htCy htTn, ht]) (by rw [hfr F hFC hFCy hFTn, hF])
    (by rw [hfr G hGC hGCy hGTn, hG]) hlC
    (fun j hj => by
      rw [hfr j (fun h => by subst h; omega) (fun h => by subst h; omega)
        (fun h => by subst h; omega), hw j hj])
  exact (e.mono (by omega)).mono_time (by
    have := Nat.mul_le_mul_left 13 (show σ.space + L ≤
      σ0.space + 2 ^ L * (2 * L + 1) + 2 * L + 2 + B + L by omega)
    omega)

/-- **An `any` loop over all second keys calling a pair routine** (first key fixed on `K`):
`Acc := [(allBits L).any (bit (σ0 K))]`. -/
theorem execLe_forAny_callPairBit {k : ℕ} {C t Cy G Acc K A A' I F : Fin k} (hCt : C ≠ t)
    (hCCy : C ≠ Cy) (htCy : t ≠ Cy) (hGA : G ≠ Acc) (hAC : Acc ≠ C) (hACy : Acc ≠ Cy)
    (hGC : G ≠ C) (hGCy : G ≠ Cy) (htA : t ≠ Acc) (hKA : K ≠ A) (hKt : K ≠ t) (hAt : A ≠ t)
    (hCA' : C ≠ A') (hA't : A' ≠ t) (hCA : C ≠ A) (hAA' : A ≠ A') (hIA : I ≠ A) (hIA' : I ≠ A')
    (hFA : F ≠ A) (hFA' : F ≠ A') (hFG : F ≠ G) (hIC : I ≠ C) (hICy : I ≠ Cy) (hIAcc : I ≠ Acc)
    (hAC' : A ≠ C) (hACy' : A ≠ Cy) (hAAcc : A ≠ Acc) (hA'Cy : A' ≠ Cy) (hA'Acc : A' ≠ Acc)
    (hFC : F ≠ C) (hFCy : F ≠ Cy) (hFAcc : F ≠ Acc) (hKC : K ≠ C) (hKCy : K ≠ Cy)
    (hKAcc : K ≠ Acc)
    {s : Stmt k} {x : BitString} {L kR B : ℕ} {bit : BitString → BitString → Bool}
    (hs : PairBitRoutine s x L kR I A A' F B bit) (hAk : A.val < kR) (hA'k : A'.val < kR)
    (hCk : C.val < kR) (hCyk : Cy.val < kR) (hAcck : Acc.val < kR) (σ0 : Stacks k)
    (hI : σ0 I = x) (hA : σ0 A = []) (hA' : σ0 A' = []) (ht : σ0 t = []) (hF : σ0 F = [])
    (hG : σ0 G = []) (hK : (σ0 K).length = L) (hC : σ0 C = bitsOf L 0)
    (hCy : σ0 Cy = [false]) (hAcc : σ0 Acc = [false])
    (hw : ∀ j : Fin k, kR ≤ j.val → σ0 j = []) :
    ∃ σ', ExecLe (forAny C t Cy G Acc (callPairBit K C A A' t F G s)) σ0 σ'
      (σ0.space + L + L + B)
      (2 ^ L * ((13 * (σ0.space + L) + 2 + (13 * (σ0.space + L + L) + 2 +
        (B + (3 * L + 1 + (3 * L + 1)))) + 4) + 5 + 10 * (σ0.space + L + L + B) + 20) + 1) ∧
      σ' = Function.update (Function.update σ0 Acc [(allBits L).any (bit (σ0 K))]) Cy [true] := by
  refine execLe_forAny hCt hCCy htCy hGA hAC hACy hGC hGCy htA L (σ0.space + L + L + B)
    (13 * (σ0.space + L) + 2 + (13 * (σ0.space + L + L) + 2 + (B + (3 * L + 1 + (3 * L + 1))))
      + 4)
    (bit (σ0 K)) σ0 ?_ hC hCy ht hG hAcc
  intro σ hfr hlC hσCy hlAcc
  have hsp : σ.space = σ0.space := by
    apply space_eq_of_length
    intro r
    by_cases hr1 : r = C
    · subst hr1; rw [hlC, hC, length_bitsOf]
    · by_cases hr2 : r = Cy
      · subst hr2; rw [hσCy, hCy]
      · by_cases hr3 : r = Acc
        · subst hr3; rw [hlAcc, hAcc]; rfl
        · rw [hfr r hr1 hr2 hr3]
  have hσK : σ K = σ0 K := hfr K hKC hKCy hKAcc
  have e := execLe_callPairBit hKA hKt hAt hCA' hCt hA't hCA hAA' hIA hIA' hFA hFA' hFG
    hs hAk hA'k (σ := σ)
    (by rw [hfr I hIC hICy hIAcc, hI]) (by rw [hfr A hAC' hACy' hAAcc, hA])
    (by rw [hfr A' hCA'.symm hA'Cy hA'Acc, hA']) (by rw [hfr t hCt.symm htCy htA, ht])
    (by rw [hfr F hFC hFCy hFAcc, hF]) (by rw [hfr G hGC hGCy hGA, hG])
    (by rw [hσK, hK]) hlC
    (fun j hj => by
      rw [hfr j (fun h => by subst h; omega) (fun h => by subst h; omega)
        (fun h => by subst h; omega), hw j hj])
  rw [hsp, hσK] at e
  exact e

/-! ### Bit combinators for the layer body -/

/-- Short-circuit conjunction of two tests: `s₁` pushes a bit on the empty stack `G`; if it is
`true`, it is popped and `s₂` pushes the result bit. -/
def andBit {k : ℕ} (G : Fin k) (s₁ s₂ : Stmt k) : Stmt k :=
  .seq s₁ (.ite G (fun o => o == some true) (.seq (.pop G) s₂) .skip)

/-- **Short-circuit conjunction**: two self-cleaning tests (each pushes its bit on the empty
stack `G` and changes nothing else; the second one is only run when the first bit is `true`)
give the conjunction of the bits on `G`. -/
theorem execLe_andBit {k : ℕ} {G : Fin k} {s₁ s₂ : Stmt k} {σ : Stacks k} {b₁ b₂ : Bool}
    {S τ₁ τ₂ : ℕ} (hG : σ G = []) (h₁ : ExecLe s₁ σ (Function.update σ G [b₁]) S τ₁)
    (h₂ : b₁ = true → ExecLe s₂ σ (Function.update σ G [b₂]) S τ₂) :
    ExecLe (andBit G s₁ s₂) σ (Function.update σ G [b₁ && b₂]) S (τ₁ + τ₂ + 3) := by
  have sp1 := h₁.toExec.space_le.2
  cases b₁
  · have e2 : ExecLe (.ite G (fun o => o == some true) (.seq (.pop G) s₂) .skip)
        (Function.update σ G [false]) (Function.update σ G [false]) S (τ₂ + 3) :=
      ExecLe.iteF (by rw [Function.update_self]; rfl) (ExecLe.skip (T := τ₂ + 1) sp1)
    rw [Bool.false_and]
    exact (h₁.seq e2).mono_time (by omega)
  · have e3 := h₂ rfl
    have hσ : Function.update σ G [] = σ := by
      rw [← hG, Function.update_eq_self]
    have ep : ExecLe (.pop G) (Function.update σ G [true]) σ S 1 := by
      have := ExecLe.pop (r := G) (σ := Function.update σ G [true]) (S := S) (T := 1) sp1 le_rfl
      rwa [Function.update_self, Function.update_idem, List.tail_cons, hσ] at this
    have e2 := ExecLe.iteT (r := G) (cond := fun o => o == some true) (s₂ := .skip)
      (by rw [Function.update_self]; rfl) (ep.seq e3)
    rw [Bool.true_and]
    exact (h₁.seq e2).mono_time (by omega)

/-- Negate the bit on `G`. -/
def notBit {k : ℕ} (G : Fin k) : Stmt k :=
  .ite G (fun o => o == some true) (Stmt.clearFlag G) (Stmt.setFlag G)

/-- `notBit G` replaces the bit on `G` with its negation. -/
theorem execLe_notBit {k : ℕ} {G : Fin k} {σ : Stacks k} {b : Bool} {S : ℕ} (hG : σ G = [b])
    (hS : σ.space ≤ S) :
    ExecLe (notBit G) σ (Function.update σ G [!b]) S 4 := by
  cases b
  · exact ExecLe.iteF (by rw [hG]; rfl) ((ExecLe.of_execT (Stmt.execT_setFlag hG)).mono hS)
  · exact ExecLe.iteT (by rw [hG]; rfl) ((ExecLe.of_execT (Stmt.execT_clearFlag hG)).mono hS)

/-! ### Explicit step bounds for the inlined plumbing routines

The step bounds of `execLe_splitK`, `execLe_joinK`, `execLe_scoreK` are existential; for the
layer's explicit time bound they are replaced by the budgets of the fixed 9-stack programs
(`Stmt.budget_rename`; `Stmt.budget_le_size_mul_pow` bounds them by a polynomial). -/

/-- Every loop of `scoreStmt` is a pop-loop (`Stmt.PopLoops`): its body pops the test stack
on every path and never pushes on it. -/
theorem popLoops_scoreStmt : scoreStmt.PopLoops :=
  ⟨Stmt.popLoops_copy (by decide) (by decide), Stmt.popLoops_addInto (by decide) (by decide),
    Stmt.popLoops_copy (by decide) (by decide), Stmt.popLoops_copy (by decide) (by decide),
    Stmt.popLoops_cmpInto (by decide)⟩

/-- `scoreStmt` inlined along `f`, with an explicit step bound: the budget of `scoreStmt` at the
space bound (`Stmt.budget_le_size_mul_pow` makes it a polynomial). -/
theorem execLe_scoreK_budget {k : ℕ} {f : Fin 9 → Fin k} (hf : Function.Injective f)
    {τ : Stacks k} {yb cb eb : BitString} (h0 : τ (f 0) = yb) (h1 : τ (f 1) = cb)
    (h2 : τ (f 2) = eb) (h3 : τ (f 3) = []) (h4 : τ (f 4) = []) (h5 : τ (f 5) = [])
    (h6 : τ (f 6) = [])
    (h7 : τ (f 7) = []) (hl1 : cb.length = yb.length) (hl2 : eb.length = yb.length)
    (hov : binVal yb + binVal cb < 2 ^ yb.length) :
    ExecLe (scoreStmt.rename f) τ
      (Function.update (Function.update (Function.update τ (f 1) []) (f 3) (addBits false yb cb))
        (f 4) [decide (binVal yb + binVal cb ≤ binVal eb)])
      (τ.space + 3 * yb.length + 2) (scoreStmt.budget (τ.space + 3 * yb.length + 2)) := by
  obtain ⟨T, e⟩ := execLe_scoreK hf h0 h1 h2 h3 h4 h5 h6 h7 hl1 hl2 hov
  have := Stmt.execLe_budget _ (Stmt.popLoops_rename hf _ popLoops_scoreStmt) e.toExec
  rwa [Stmt.budget_rename] at this

/-- The loop of `takeLoop U C D` is a pop-loop (`Stmt.PopLoops`) when `U` differs from `C` and `D`:
its body pops the test stack `U` on every path and never pushes on it. The two distinctness
proofs are optional arguments, found by `decide` when the stacks are numerals. -/
theorem popLoops_takeLoop {k : ℕ} {U C D : Fin k} (hUC : U ≠ C := by decide)
    (hUD : U ≠ D := by decide) : (takeLoop U C D).PopLoops := by
  replace hUC : U ≠ C := hUC
  replace hUD : U ≠ D := hUD
  simp [takeLoop, Stmt.moveBit, Stmt.caseBit, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops, hUC.symm,
    hUD.symm]

/-- Every loop of `splitStmt` is a pop-loop (`Stmt.PopLoops`): its body pops the test stack
on every path and never pushes on it. -/
theorem popLoops_splitStmt : splitStmt.PopLoops :=
  ⟨Stmt.popLoops_copy (by decide) (by decide), popLoops_takeLoop,
    Stmt.popLoops_moveAll (by decide), popLoops_takeLoop,
    Stmt.popLoops_moveAll (by decide)⟩

/-- Every loop of `joinStmt` is a pop-loop (`Stmt.PopLoops`): its body pops the test stack
on every path and never pushes on it. -/
theorem popLoops_joinStmt : joinStmt.PopLoops :=
  ⟨Stmt.popLoops_copy (by decide) (by decide), Stmt.popLoops_copy (by decide) (by decide),
    Stmt.popLoops_copy (by decide) (by decide)⟩

/-- `splitStmt` inlined along `f`, with an explicit step bound (the budget of `splitStmt`). -/
theorem execLe_splitK_budget {k : ℕ} {f : Fin 9 → Fin k} (hf : Function.Injective f)
    {τ : Stacks k} {κ yb nb : BitString} (h0 : τ (f 0) = κ ++ yb ++ nb) (h1 : τ (f 1) = [])
    (h2 : τ (f 2) = []) (h3 : τ (f 3) = List.replicate κ.length true)
    (h4 : τ (f 4) = List.replicate yb.length true) (h5 : τ (f 5) = []) (h6 : τ (f 6) = [])
    (h7 : τ (f 7) = []) :
    ExecLe (splitStmt.rename f) τ
      (Function.update (Function.update (Function.update (Function.update
        (Function.update τ (f 3) []) (f 4) []) (f 6) κ) (f 7) yb) (f 1) nb)
      (τ.space + (τ (f 0)).length) (splitStmt.budget (τ.space + (τ (f 0)).length)) := by
  obtain ⟨T, e⟩ := execLe_splitK hf h0 h1 h2 h3 h4 h5 h6 h7
  have := Stmt.execLe_budget _ (Stmt.popLoops_rename hf _ popLoops_splitStmt) e.toExec
  rwa [Stmt.budget_rename] at this

/-- `joinStmt` inlined along `f`, with an explicit step bound (the budget of `joinStmt`). -/
theorem execLe_joinK_budget {k : ℕ} {f : Fin 9 → Fin k} (hf : Function.Injective f)
    {τ : Stacks k} (h3 : τ (f 3) = []) (h4 : τ (f 4) = []) :
    ExecLe (joinStmt.rename f) τ
      (Function.update τ (f 3) (τ (f 0) ++ τ (f 1) ++ τ (f 2)))
      (τ.space + (τ (f 0)).length + (τ (f 1)).length + (τ (f 2)).length)
      (joinStmt.budget (τ.space + (τ (f 0)).length + (τ (f 1)).length + (τ (f 2)).length)) := by
  obtain ⟨T, e⟩ := execLe_joinK hf h3 h4
  have := Stmt.execLe_budget _ (Stmt.popLoops_rename hf _ popLoops_joinStmt) e.toExec
  rwa [Stmt.budget_rename] at this

end KeyEval
end Kolmogorov.RandomStrings
