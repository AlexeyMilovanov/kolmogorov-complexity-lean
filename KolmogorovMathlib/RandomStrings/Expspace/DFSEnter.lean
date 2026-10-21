/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSFrames

/-!
# The depth-first search: entering and leaving a frame

The entry routines copy the top frame's position to stack `6` before its mode step
(`DFS.exists_enterPreStmt`), then consume the answer and update the frame stack and mode
(`DFS.exists_enterPostStmt`). Their extra space is bounded by a constant multiple of the
top frame's size and the width of its work strings.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- `enterPreCopyProg` copies the reversed code of the first frame field onto stack `18` while
restoring the encoded frame stack. -/
def enterPreCopyProg : Stmt 38 :=
  Stmt.seqs [QEnum.codeDup 8 17 18, Stmt.moveAll 17 8]

/-- `enterPreDecodeProg` decodes the reversed code on stack `18` into the position on stack `6`
and clears the work stacks used by the decoding phase. -/
def enterPreDecodeProg : Stmt 38 :=
  Stmt.seqs [Stmt.moveAll 18 19, Stmt.decodeOne 19 18 17, Stmt.moveAll 18 6, Stmt.clear 17]

/-- `enterPreProg` copies and decodes the first field of the encoded top frame into stack `6`,
preserving the encoded frame. -/
def enterPreProg : Stmt 38 := .seq enterPreCopyProg enterPreDecodeProg

/-- Encoding the fields of a nonempty frame list starts with the code of its first position. -/
private theorem encList_cons_append (W : ℕ) (F : Frame) (Ks : List Frame) :
    Stacks.encList ((F :: Ks).flatMap (Frame.fields W)) =
      Stacks.encStr F.v ++ Stacks.encList
        ([numBits W F.y, numBits W F.n, List.replicate F.f true, F.v', F.r] ++
          Ks.flatMap (Frame.fields W)) := by
  simp only [Frame.fields, List.flatMap_cons, List.append_assoc, Stacks.encList,
    List.flatMap_append]

/-- `enterPreCopyProg` preserves the encoded frames and leaves the reversed code of `F.v` on
stack `18`, using at most `4 * frameSize W F` extra space. -/
theorem exec_enterPreCopyProg (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    Exec enterPreCopyProg (Function.update (encSt base W m (0, F :: Ks)) 9 [])
      (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 18
        (Stacks.encStr F.v).reverse)
      ((encSt base W m (0, F :: Ks)).space + 4 * frameSize W F) := by
  let σ : Stacks 38 := Function.update (encSt base W m (0, F :: Ks)) 9 []
  let rest := Stacks.encList
    ([numBits W F.y, numBits W F.n, List.replicate F.f true, F.v', F.r] ++
      Ks.flatMap (Frame.fields W))
  let σ₁ : Stacks 38 := Function.update (Function.update (Function.update σ 8 rest) 17
    ((Stacks.encStr F.v).reverse ++ σ 17)) 18 ((Stacks.encStr F.v).reverse ++ σ 18)
  have h8 : σ 8 = Stacks.encStr F.v ++ rest := by
    simpa [σ, encSt, rest] using encList_cons_append W F Ks
  have h17 : σ 17 = [] := by simp [σ, encSt, hb 17 (by decide)]
  have h18 : σ 18 = [] := by simp [σ, encSt, hb 18 (by decide)]
  have eCopy : Exec (QEnum.codeDup 8 17 18) σ σ₁ (σ.space + 2 * F.v.length + 1) :=
    QEnum.exec_codeDup h8
  have eMove := Stmt.exec_moveAll (k := 38) (r := 17) (r' := 8) (by decide)
    (Stacks.encStr F.v).reverse σ₁ (by simp [σ₁, h17])
  have hout : Function.update (Function.update σ₁ 17 []) 8
      ((Stacks.encStr F.v).reverse.reverse ++ σ₁ 8) =
        Function.update σ 18 (Stacks.encStr F.v).reverse := by
    funext j
    by_cases h8j : j = 8
    · subst j
      simpa [σ₁] using h8.symm
    by_cases h17j : j = 17
    · subst j
      simp [σ₁, h17]
    by_cases h18j : j = 18
    · subst j
      simp [σ₁, h18]
    simp [σ₁, h8j, h17j, h18j]
  have eRestore := Stmt.exec_of_eq eMove hout
  have hσ : σ.space ≤ (encSt base W m (0, F :: Ks)).space := by
    apply Stacks.space_update_le
    simp
  have hS : σ.space + 2 * F.v.length + 1 ≤
      (encSt base W m (0, F :: Ks)).space + 4 * frameSize W F := by
    dsimp [frameSize]
    omega
  have hσ₁ := eCopy.space_le.2.trans hS
  exact .seq (eCopy.mono hS)
    (.seq (eRestore.mono hσ₁) (.skip (eRestore.space_le.2.trans hσ₁)))

/-- `enterPreDecodeProg` consumes the reversed code of `F.v` on stack `18` and puts `F.v` on
stack `6`, clearing its work stacks within `8 * frameSize W F` extra space. -/
theorem exec_enterPreDecodeProg (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    Exec enterPreDecodeProg
      (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 18
        (Stacks.encStr F.v).reverse)
      (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v)
      ((encSt base W m (0, F :: Ks)).space + 8 * frameSize W F) := by
  let B := Function.update (encSt base W m (0, F :: Ks)) 9 []
  let C := Stacks.encStr F.v
  let σ0 := Function.update B 18 C.reverse
  let σ1 := Function.update B 19 C
  let σ2 := Function.update (Function.update B 18 F.v.reverse) 17 C.reverse
  let σ3 := Function.update (Function.update B 6 F.v) 17 C.reverse
  let σ4 := Function.update B 6 F.v
  let S := (encSt base W m (0, F :: Ks)).space + 8 * frameSize W F
  have hB : B = encSt base W m (0, F :: Ks) := by
    funext j
    simp only [B, encSt, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have hB6 : B 6 = [] := by rw [hB]; simp [encSt, hb 6 (by decide)]
  have hB17 : B 17 = [] := by rw [hB]; simp [encSt, hb 17 (by decide)]
  have hB18 : B 18 = [] := by rw [hB]; simp [encSt, hb 18 (by decide)]
  have hB19 : B 19 = [] := by rw [hB]; simp [encSt, hb 19 (by decide)]
  have hsp0 : Stacks.space σ0 = Stacks.space B + C.length := by
    have h := Stacks.space_update B (18 : Fin 38) C.reverse
    simpa [σ0, hB18] using h
  have hC : C.length = 2 * F.v.length + 1 := by
    simpa [C] using Stacks.length_encStr F.v
  have hsp0S : Stacks.space σ0 ≤ S := by
    rw [hsp0, hB, hC]
    dsimp [S, frameSize]
    omega
  have hm1raw := Stmt.exec_moveAll (k := 38) (r := 18) (r' := 19) (by decide)
    C.reverse σ0 (by simp [σ0])
  have hm1eq :
      Function.update (Function.update σ0 18 []) 19 (C.reverse.reverse ++ σ0 19) = σ1 := by
    funext j
    by_cases h19 : j = 19 <;> by_cases h18 : j = 18 <;>
      simp [σ0, σ1, h19, h18, hB18, hB19]
  have hm1base : Exec (Stmt.moveAll 18 19) σ0 σ1 (Stacks.space σ0) :=
    Stmt.exec_of_eq hm1raw hm1eq
  have hm1 := hm1base.mono hsp0S
  have hdRaw := Stmt.exec_decodeOne (k := 38) (Lst := 19) (W := 18) (Tmp := 17)
    (by decide) (by decide) (by decide) (z := F.v) (rest := []) (σ := σ1)
      (by simp [σ1, C])
  have hdEq :
      Function.update
          (Function.update (Function.update σ1 19 []) 18 (F.v.reverse ++ σ1 18)) 17
            (C.reverse ++ σ1 17) = σ2 := by
    funext j
    by_cases h17 : j = 17 <;> by_cases h18 : j = 18 <;> by_cases h19 : j = 19 <;>
      simp [σ1, σ2, h17, h18, h19, hB17, hB18, hB19]
  have hdBase : Exec (Stmt.decodeOne 19 18 17) σ1 σ2
      (Stacks.space σ1 + F.v.length) :=
    Stmt.exec_of_eq hdRaw hdEq
  have hsp1 : Stacks.space σ1 ≤ Stacks.space σ0 := hm1base.space_le.2
  have hdS : Stacks.space σ1 + F.v.length ≤ S := by
    rw [hsp0, hB, hC] at hsp1
    dsimp [S, frameSize]
    omega
  have hd := hdBase.mono hdS
  have hm2Raw := Stmt.exec_moveAll (k := 38) (r := 18) (r' := 6) (by decide)
    F.v.reverse σ2 (by simp [σ2])
  have hm2Eq :
      Function.update (Function.update σ2 18 []) 6 (F.v.reverse.reverse ++ σ2 6) = σ3 := by
    funext j
    by_cases h6 : j = 6 <;> by_cases h17 : j = 17 <;> by_cases h18 : j = 18 <;>
      simp [σ2, σ3, h6, h17, h18, hB6, hB18]
  have hm2Base : Exec (Stmt.moveAll 18 6) σ2 σ3 (Stacks.space σ2) :=
    Stmt.exec_of_eq hm2Raw hm2Eq
  have hsp2 : Stacks.space σ2 ≤ Stacks.space σ1 + F.v.length := hdBase.space_le.2
  have hm2 := hm2Base.mono (hsp2.trans hdS)
  have hcRaw := Stmt.exec_clear (k := 38) 17 C.reverse σ3 (by simp [σ3])
  have hcEq : Function.update σ3 17 [] = σ4 := by
    funext j
    by_cases h6 : j = 6 <;> by_cases h17 : j = 17 <;>
      simp [σ3, σ4, h6, h17, hB17]
  have hcBase : Exec (Stmt.clear 17) σ3 σ4 (Stacks.space σ3) :=
    Stmt.exec_of_eq hcRaw hcEq
  have hsp3 : Stacks.space σ3 ≤ Stacks.space σ2 := hm2Base.space_le.2
  have hc := hcBase.mono (hsp3.trans (hsp2.trans hdS))
  have hskip : Exec (Stmt.skip : Stmt 38) σ4 σ4 S := .skip hc.space_le.2
  simpa [enterPreDecodeProg, Stmt.seqs, σ0, σ4, B, C, S] using
    (Exec.seq hm1 (Exec.seq hd (Exec.seq hm2 (Exec.seq hc hskip))))

/-- A stack program copies the top frame's position onto stack `6` while preserving the encoded
frames, using extra space bounded by a constant multiple of `frameSize W F`. -/
theorem exists_enterPreStmt : ∃ (s : Stmt 38) (K : ℕ), ∀ (base : Stacks 38) (W m : ℕ)
    (F : Frame) (Ks : List Frame), (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    Exec s (Function.update (encSt base W m (0, F :: Ks)) 9 [])
      (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v)
      ((encSt base W m (0, F :: Ks)).space + K * frameSize W F) := by
  refine ⟨enterPreProg, 8, ?_⟩
  intro base W m F Ks hb
  have e1 := exec_enterPreCopyProg base W m F Ks hb
  have e2 := exec_enterPreDecodeProg base W m F Ks hb
  exact .seq (e1.mono (by omega)) e2

/-- `clearFrameRegs` empties the six decoded frame registers `11` through `16`. -/
def clearFrameRegs : Stmt 38 :=
  Stmt.seqs [Stmt.clear 11, Stmt.clear 12, Stmt.clear 13, Stmt.clear 14,
    Stmt.clear 15, Stmt.clear 16]

/-- `enterPostTrueFinishProg` resets `v'`, re-encodes the frame and selects mode `1` when fuel is
positive; with zero fuel, it clears the decoded registers and selects mode `6`. -/
def enterPostTrueFinishProg (sPush : Stmt 38) : Stmt 38 :=
  .ite 14 Option.isSome
    (Stmt.seqs [Stmt.clear 15, Stmt.copy 10 15 17, sPush, Stmt.pushList 9 [true]])
    (Stmt.seqs [clearFrameRegs, Stmt.pushList 9 (List.replicate 6 true)])

/-- `enterPostFalseFinishProg` clears the decoded registers and selects return mode `5`. -/
def enterPostFalseFinishProg : Stmt 38 :=
  Stmt.seqs [clearFrameRegs, Stmt.pushList 9 (List.replicate 5 true)]

/-- `enterPostProg` clears the exposed position, consumes the outcome bit, and runs the frame
routines to finish the entry step for that outcome. -/
def enterPostProg (sPop sPush : Stmt 38) : Stmt 38 :=
  .seq (Stmt.clear 6) (Stmt.caseBit 7 fun b => .seq (.pop 7)
    (.seq sPop (if b then enterPostTrueFinishProg sPush else enterPostFalseFinishProg)))

/-- Clearing stack `6` removes the exposed position while leaving the outcome bit on stack `7`,
using at most `2 * (frameSize W F + m + 1)` extra space. -/
theorem exec_enterPost_clear (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (b : Bool) (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    Exec (Stmt.clear 6)
      (Function.update (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        6 F.v) 7 [b])
      (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 7 [b])
      ((encSt base W m (0, F :: Ks)).space + 2 * (frameSize W F + m + 1)) := by
  have e := Stmt.exec_clear 6 F.v (Function.update (Function.update
    (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v) 7 [b]) (by simp)
  have H : Function.update (Function.update (Function.update
      (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v) 7 [b]) 6 [] =
      Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 7 [b] := by
    funext i
    by_cases h : i = 6
    · subst h
      simp [Function.update, encSt, hb 6 (by decide)]
    · simp [h, Function.update, encSt]
  rw [H] at e
  apply Exec.mono e
  have hs1 :
      (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v) 7 = [] := by
    simp [Function.update, encSt, hb 7 (by decide)]
  have hs2 : Stacks.space (Function.update (Function.update
      (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v) 7 [b]) =
      Stacks.space (Function.update
        (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v) + 1 := by
    have this := Stacks.space_update (Function.update
      (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v) 7 [b]
    rw [hs1] at this
    simpa using this
  have hs3 : (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 = [] := by
    simp [Function.update, encSt, hb 6 (by decide)]
  have hs4 : Stacks.space
      (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v) =
      Stacks.space (Function.update (encSt base W m (0, F :: Ks)) 9 []) + F.v.length := by
    have this := Stacks.space_update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v
    rw [hs3] at this
    simpa using this
  have hs5 : Stacks.space (Function.update (encSt base W m (0, F :: Ks)) 9 []) ≤
      Stacks.space (encSt base W m (0, F :: Ks)) := by
    apply Stacks.space_update_le
    simp
  rw [hs2, hs4]
  have Hf : F.v.length ≤ frameSize W F := by
    unfold frameSize
    omega
  omega

/-- Clearing a decoded frame and writing mode `5` uses at most five extra stack cells. -/
private theorem exec_enterPost_false_finish (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    Exec enterPostFalseFinishProg (regSt base W m F Ks)
      (encSt base W m (enterStep m false F Ks))
      ((regSt base W m F Ks).space + 5) := by
  let σ := regSt base W m F Ks
  let σc : Stacks 38 := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update σ 11 []) 12 []) 13 []) 14 []) 15 []) 16 []
  have ec : Exec clearFrameRegs σ σc σ.space := exec_pushFrameClearStmt σ σ.space le_rfl
  have ep := Stmt.exec_pushList 9 (List.replicate 5 true) σc
  have hout : Function.update σc 9 (List.replicate 5 true ++ σc 9) =
      encSt base W m (enterStep m false F Ks) := by
    funext j
    fin_cases j <;> simp [σc, σ, regSt, encSt, enterStep, hb]
  have ep' : Exec (Stmt.pushList 9 (List.replicate 5 true)) σc
      (encSt base W m (enterStep m false F Ks)) (σ.space + 5) := by
    apply (Stmt.exec_of_eq ep hout).mono
    simpa only [List.length_replicate] using Nat.add_le_add_right ec.space_le.2 5
  exact .seq (ec.mono (Nat.le_add_right σ.space 5)) (.seq ep' (.skip ep'.space_le.2))

/-- Popping the top frame and running `enterPostFalseFinishProg` discards the frame and selects
mode `5`, using at most `(KPop + 8) * (frameSize W F + m + 1)` extra space. -/
theorem exec_enterPost_false (sPop : Stmt 38) (KPop : ℕ)
    (hPop : ∀ (base : Stacks 38) (W m i : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPop (Function.update (encSt base W m (i, F :: Ks)) 9 []) (regSt base W m F Ks)
        ((encSt base W m (i, F :: Ks)).space + KPop * frameSize W F))
    (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    Exec (.seq sPop enterPostFalseFinishProg)
      (Function.update (encSt base W m (0, F :: Ks)) 9 [])
      (encSt base W m (enterStep m false F Ks))
      ((encSt base W m (0, F :: Ks)).space + (KPop + 8) * (frameSize W F + m + 1)) := by
  have ePop := hPop base W m 0 F Ks hb
  have H_finish := exec_enterPost_false_finish base W m F Ks hb
  have H_seq := Exec.seq_max ePop H_finish
  have H_le : max ((encSt base W m (0, F :: Ks)).space + KPop * frameSize W F)
      ((regSt base W m F Ks).space + 5) ≤
      ((encSt base W m (0, F :: Ks)).space + (KPop + 8) * (frameSize W F + m + 1)) := by
    have H1 : (encSt base W m (0, F :: Ks)).space + KPop * frameSize W F ≤
        (encSt base W m (0, F :: Ks)).space + (KPop + 8) * (frameSize W F + m + 1) := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul
      · omega
      · omega
    have H2 : (regSt base W m F Ks).space + 5 ≤
        (encSt base W m (0, F :: Ks)).space + (KPop + 8) * (frameSize W F + m + 1) := by
      have H_regSt_le : (regSt base W m F Ks).space ≤
          (encSt base W m (0, F :: Ks)).space + 8 * frameSize W F := by
        have H_push := pushFrameEncode_space base W m F Ks
        omega
      calc (regSt base W m F Ks).space + 5
        ≤ (encSt base W m (0, F :: Ks)).space + 8 * frameSize W F + 5 := by omega
        _ ≤ (encSt base W m (0, F :: Ks)).space + (KPop + 8) * (frameSize W F + m + 1) := by
          have : 8 * frameSize W F + 5 ≤ (KPop + 8) * (frameSize W F + m + 1) := by
            nlinarith [Nat.zero_le KPop, Nat.zero_le m, Nat.zero_le (frameSize W F)]
          omega
    apply max_le H1 H2
  exact H_seq.mono H_le

/-- Installing the unary mode `i` on the empty mode stack of the mode-`0` state gives the
mode-`i` state. -/
private theorem enterPostZero_encSt_mode (base : Stacks 38) (W m i : ℕ) (Fs : List Frame) :
    Function.update (encSt base W m (0, Fs)) 9 (List.replicate i true) =
      encSt base W m (i, Fs) := by
  simp only [encSt]
  rw [Function.update_comm (by decide : (10 : Fin 38) ≠ 9), Function.update_idem]

/-- Clearing the six decoded registers `11`--`16` of `regSt` leaves the mode-`0` state of the
remaining frames, with the mode stack `9` set to empty. -/
private theorem enterPostZero_clear_regSt (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (regSt base W m F Ks) 11 []) 12 []) 13 []) 14 []) 15 []) 16 [] =
      Function.update (encSt base W m (0, Ks)) 9 [] := by
  funext j
  by_cases j16 : j = 16
  · subst j16
    simp [encSt, hb 16 (by decide)]
  by_cases j15 : j = 15
  · subst j15
    simp [encSt, hb 15 (by decide)]
  by_cases j14 : j = 14
  · subst j14
    simp [encSt, hb 14 (by decide)]
  by_cases j13 : j = 13
  · subst j13
    simp [encSt, hb 13 (by decide)]
  by_cases j12 : j = 12
  · subst j12
    simp [encSt, hb 12 (by decide)]
  by_cases j11 : j = 11
  · subst j11
    simp [encSt, hb 11 (by decide)]
  simp [regSt, j16, j15, j14, j13, j12, j11]

/-- With zero fuel, `enterPostTrueFinishProg` clears the decoded frame registers and selects
mode `6`, using at most `9 * (frameSize W F + m + 1)` extra space. -/
private theorem exec_enterPost_true_zero_finish (sPush : Stmt 38)
    (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) (hf : F.f = 0) :
    Exec (enterPostTrueFinishProg sPush) (regSt base W m F Ks)
      (encSt base W m (enterStep m true F Ks))
      ((encSt base W m (0, F :: Ks)).space + 9 * (frameSize W F + m + 1)) := by
  let σ := regSt base W m F Ks
  let σc : Stacks 38 := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update σ 11 []) 12 []) 13 []) 14 []) 15 []) 16 []
  let S := (encSt base W m (0, F :: Ks)).space + 9 * (frameSize W F + m + 1)
  have hreg : σ.space ≤ (encSt base W m (0, F :: Ks)).space + 8 * frameSize W F := by
    have h := pushFrameEncode_space base W m F Ks
    simp only [σ]
    omega
  have ec0 := exec_pushFrameClearStmt σ σ.space le_rfl
  have ec : Exec clearFrameRegs σ σc S := by
    simpa only [clearFrameRegs, σc] using ec0.mono (by simp only [S]; omega)
  have hσc : σc.space ≤ σ.space := ec0.space_le.2
  have ep0 := Stmt.exec_pushList 9 (List.replicate 6 true) σc
  have ep : Exec (Stmt.pushList 9 (List.replicate 6 true)) σc
      (Function.update σc 9 (List.replicate 6 true ++ σc 9)) S := by
    exact ep0.mono (by simp only [List.length_replicate, S]; omega)
  have hclr : σc = Function.update (encSt base W m (0, Ks)) 9 [] := by
    simpa only [σc, σ] using enterPostZero_clear_regSt base W m F Ks hb
  have hE : enterStep m true F Ks = (6, Ks) := by simp [enterStep, hf]
  have hout : Function.update σc 9 (List.replicate 6 true ++ σc 9) =
      encSt base W m (enterStep m true F Ks) := by
    rw [hE, hclr]
    simp only [Function.update_self, List.append_nil, Function.update_idem]
    exact enterPostZero_encSt_mode base W m 6 Ks
  unfold enterPostTrueFinishProg
  have h14 : regSt base W m F Ks 14 = [] := by simp [regSt, hf]
  refine .iteF (by simp [h14]) ?_
  rw [Stmt.exec_seqs_cons]
  refine ⟨σc, ec, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨encSt base W m (enterStep m true F Ks), ?_, ?_⟩
  · rw [← hout]
    exact ep
  · exact .skip (by rw [← hout]; exact ep.space_le.2)

/-- Replacing `F.v'` by an `m`-bit zero vector leaves enough space for re-encoding the frame and
writing its mode bit within `(KPush + 9) * (frameSize W F + m + 1)` extra space. -/
private lemma enterPost_true_push_space (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (KPush : ℕ) :
    (encSt base W m (0, {F with v' := List.replicate m false} :: Ks)).space +
        KPush * frameSize W {F with v' := List.replicate m false} + 1 ≤
      (encSt base W m (0, F :: Ks)).space +
        (KPush + 9) * (frameSize W F + m + 1) := by
  zify
  dsimp [encSt]
  simp only [space_update_int, Function.update]
  simp only [Stacks.length_encList, List.flatMap_cons, List.map_append, List.sum_append]
  dsimp [frameSize, numBits, Frame.fields]
  simp only [List.length_map, List.length_range, List.length_replicate, List.map_cons,
    List.sum_cons, List.sum_nil, List.map_nil]
  push_cast
  nlinarith [Nat.zero_le KPush, Nat.zero_le W, Nat.zero_le m, Nat.zero_le F.v.length,
    Nat.zero_le F.v'.length, Nat.zero_le F.r.length, Nat.zero_le F.f]

/-- Clearing register `15` and copying the zero vector from stack `10` into it replaces `F.v'`
by `List.replicate m false` in the decoded frame state. -/
private lemma exec_enterPost_true_succ_finish_hcopy (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    let F' := { F with v' := List.replicate m false };
    Function.update (Function.update (regSt base W m F Ks) 15 []) 15
      ((Function.update (regSt base W m F Ks) 15 []) 10 ++
        (Function.update (regSt base W m F Ks) 15 []) 15) =
    regSt base W m F' Ks := by
  funext j
  fin_cases j <;> simp [regSt, encSt, hb]

/-- For a frame with positive fuel, writing mode `1` after resetting `F.v'` to the zero vector
gives the encoded state of `enterStep m true F Ks`. -/
private lemma exec_enterPost_true_succ_finish_hout (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (hf : F.f ≠ 0) :
    let F' := { F with v' := List.replicate m false };
    Function.update (Function.update (encSt base W m (0, F' :: Ks)) 9 []) 9
      ([true] ++ Function.update (encSt base W m (0, F' :: Ks)) 9 [] 9) =
    encSt base W m (enterStep m true F Ks) := by
  funext j
  fin_cases j <;> simp [encSt, enterStep, hf]

/-- With positive fuel, `enterPostTrueFinishProg` resets `F.v'` to the zero vector, re-encodes
the frame, and selects mode `1`, using at most
`(KPush + 9) * (frameSize W F + m + 1)` extra space. -/
private theorem exec_enterPost_true_succ_finish (sPush : Stmt 38) (KPush : ℕ)
    (hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPush (regSt base W m F Ks) (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        ((encSt base W m (0, F :: Ks)).space + KPush * frameSize W F))
    (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) (hf : F.f ≠ 0) :
    Exec (enterPostTrueFinishProg sPush) (regSt base W m F Ks)
      (encSt base W m (enterStep m true F Ks))
      ((encSt base W m (0, F :: Ks)).space +
        (KPush + 9) * (frameSize W F + m + 1)) := by
  let F' : Frame := { F with v' := List.replicate m false }
  let σ := regSt base W m F Ks
  let σ1 : Stacks 38 := Function.update σ 15 []
  let σ2 : Stacks 38 := regSt base W m F' Ks
  let τ : Stacks 38 := Function.update (encSt base W m (0, F' :: Ks)) 9 []
  let S := (encSt base W m (0, F :: Ks)).space +
    (KPush + 9) * (frameSize W F + m + 1)
  have hreg : σ.space ≤ (encSt base W m (0, F :: Ks)).space + 8 * frameSize W F := by
    have h := pushFrameEncode_space base W m F Ks
    simp only [σ]
    omega
  have ec0 := Stmt.exec_clear 15 F.v' σ (by simp [σ, regSt])
  have hσ1 : σ1.space ≤ σ.space := by
    simpa only [σ1] using ec0.space_le.2
  have ec : Exec (Stmt.clear 15) σ σ1 S := by
    simpa only [σ1] using ec0.mono (by simp only [S]; nlinarith [Nat.zero_le KPush])
  have h17 : σ1 17 = [] := by
    simp [σ1, σ, regSt, encSt, hb 17 (by decide)]
  have ecopy0 := Stmt.exec_copy (k := 38) (r := 10) (r' := 15) (t := 17)
    (by decide) (by decide) (by decide) h17
  have hcopy : Function.update σ1 15 (σ1 10 ++ σ1 15) = σ2 :=
    exec_enterPost_true_succ_finish_hcopy base W m F Ks hb
  have ecopyBase : Exec (Stmt.copy 10 15 17) σ1 σ2
      (σ1.space + (σ1 10).length) := by
    rw [← hcopy]
    exact ecopy0
  have h10 : (σ1 10).length = m := by simp [σ1, σ, regSt, encSt]
  have ecopy : Exec (Stmt.copy 10 15 17) σ1 σ2 S := by
    exact ecopyBase.mono (by rw [h10]; simp only [S]; nlinarith [Nat.zero_le KPush])
  have epush0 := hPush base W m F' Ks hb
  have hpushSpace0 := enterPost_true_push_space base W m F Ks KPush
  have hpushSpace :
      (encSt base W m (0, F' :: Ks)).space + KPush * frameSize W F' + 1 ≤ S := by
    simpa only [F', S] using hpushSpace0
  have epush : Exec sPush σ2 τ S := by
    apply epush0.mono
    omega
  have hτ : τ.space ≤
      (encSt base W m (0, F' :: Ks)).space + KPush * frameSize W F' := by
    simpa only [τ] using epush0.space_le.2
  have emode0 := Stmt.exec_pushList 9 [true] τ
  have emode : Exec (Stmt.pushList 9 [true]) τ
      (Function.update τ 9 ([true] ++ τ 9)) S := by
    apply emode0.mono
    simp only [List.length_cons, List.length_nil, S]
    omega
  have hout : Function.update τ 9 ([true] ++ τ 9) =
      encSt base W m (enterStep m true F Ks) :=
    exec_enterPost_true_succ_finish_hout base W m F Ks hf
  unfold enterPostTrueFinishProg
  refine .iteT (by simp [regSt, hf]) ?_
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ1, ec, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ2, ecopy, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨τ, epush, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨encSt base W m (enterStep m true F Ks), ?_, ?_⟩
  · rw [← hout]
    exact emode
  · exact .skip (by rw [← hout]; exact emode.space_le.2)

/-- The two frame routines given to the true branch of the entry step: `sPop` pops the top frame
of the coded state into the registers `regSt` within `KPop * frameSize W F` extra space, and
`sPush` re-encodes the registers as the top frame within `KPush * frameSize W F` extra space,
for every base whose stacks `5`–`37` are empty. -/
structure EnterPostTrueRoutines (sPop sPush : Stmt 38) (KPop KPush : ℕ) : Prop where
  /-- `sPop` decodes the top frame `F` into `regSt`, leaving mode stack `9` empty. -/
  hPop : ∀ (base : Stacks 38) (W m i : ℕ) (F : Frame) (Ks : List Frame),
    (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    Exec sPop (Function.update (encSt base W m (i, F :: Ks)) 9 []) (regSt base W m F Ks)
      ((encSt base W m (i, F :: Ks)).space + KPop * frameSize W F)
  /-- `sPush` re-encodes the registers as the top frame `F`, leaving mode stack `9` empty. -/
  hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
    (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    Exec sPush (regSt base W m F Ks) (Function.update (encSt base W m (0, F :: Ks)) 9 [])
      ((encSt base W m (0, F :: Ks)).space + KPush * frameSize W F)

/-- Given the frame routines `R`, the true branch implements `enterStep m true F Ks` within
`(KPop + KPush + 9) * (frameSize W F + m + 1)` extra space. -/
theorem exec_enterPost_true (sPop sPush : Stmt 38) (KPop KPush : ℕ)
    (R : EnterPostTrueRoutines sPop sPush KPop KPush)
    (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    Exec (.seq sPop (enterPostTrueFinishProg sPush))
      (Function.update (encSt base W m (0, F :: Ks)) 9 [])
      (encSt base W m (enterStep m true F Ks))
      ((encSt base W m (0, F :: Ks)).space + (KPop + KPush + 9) *
        (frameSize W F + m + 1)) := by
  obtain ⟨hPop, hPush⟩ := R
  have ePop := hPop base W m 0 F Ks hb
  by_cases hf : F.f = 0
  · have eFinish := exec_enterPost_true_zero_finish sPush base W m F Ks hb hf
    refine (Exec.seq_max ePop eFinish).mono ?_
    apply max_le
    · apply Nat.add_le_add_left
      exact Nat.mul_le_mul (by omega) (by omega)
    · apply Nat.add_le_add_left
      exact Nat.mul_le_mul (by omega) (by omega)
  · have eFinish := exec_enterPost_true_succ_finish sPush KPush hPush base W m F Ks hb hf
    refine (Exec.seq_max ePop eFinish).mono ?_
    apply max_le
    · apply Nat.add_le_add_left
      exact Nat.mul_le_mul (by omega) (by omega)
    · apply Nat.add_le_add_left
      exact Nat.mul_le_mul (by omega) (by omega)

/-- A stack program consumes the position on stack `6` and the outcome bit on stack `7` and
implements `enterStep`, using extra space bounded by a constant multiple of
`frameSize W F + m + 1`. -/
theorem exists_enterPostStmt : ∃ (s : Stmt 38) (K : ℕ), ∀ (base : Stacks 38) (W m : ℕ)
    (F : Frame) (Ks : List Frame) (b : Bool), (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    Exec s (Function.update (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        6 F.v) 7 [b])
      (encSt base W m (enterStep m b F Ks))
      ((encSt base W m (0, F :: Ks)).space + K * (frameSize W F + m + 1)) := by
  obtain ⟨sPop, KPop, hPop⟩ := exists_popFrameStmt
  obtain ⟨sPush, KPush, hPush⟩ := exists_pushFrameStmt
  refine ⟨enterPostProg sPop sPush, KPop + KPush + 10, ?_⟩
  intro base W m F Ks b hb
  let σ := Function.update (encSt base W m (0, F :: Ks)) 9 []
  let τ₀ := Function.update σ 7 [b]
  let S := (encSt base W m (0, F :: Ks)).space +
    (KPop + KPush + 10) * (frameSize W F + m + 1)
  have e0 := (exec_enterPost_clear base W m F Ks b hb).mono (S' := S) (by
    unfold S; simp only [Nat.add_mul]; omega)
  have h7 : τ₀ 7 = b :: [] := by simp [τ₀]
  have ep' := Stmt.exec_pop_cons h7 (S := S) (e0.space_le.2)
  have hp : Function.update τ₀ 7 [] = σ := by
    funext j
    simp only [τ₀, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [σ, encSt, hb 7 (by decide)]
  rw [hp] at ep'
  have ec : Exec (Stmt.caseBit 7 fun b => .seq (.pop 7)
      (.seq sPop (if b then enterPostTrueFinishProg sPush else enterPostFalseFinishProg)))
      τ₀ (encSt base W m (enterStep m b F Ks)) S := by
    rw [Stmt.exec_caseBit h7]
    cases b
    · exact .seq ep' ((exec_enterPost_false sPop KPop hPop base W m F Ks hb).mono (by
        unfold S; simp only [Nat.add_mul]; omega))
    · exact .seq ep' ((exec_enterPost_true sPop sPush KPop KPush ⟨hPop, hPush⟩
        base W m F Ks hb).mono (by unfold S; simp only [Nat.add_mul]; omega))
  exact .seq e0 ec

end DFS
end Kolmogorov.RandomStrings
