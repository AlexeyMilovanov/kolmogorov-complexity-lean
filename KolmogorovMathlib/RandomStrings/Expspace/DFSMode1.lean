/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSFrames
import KolmogorovMathlib.RandomStrings.Expspace.DFSTests

/-!
# The depth-first search: mode 1

The contract `DFS.ModeSpec` of a mode routine, the register helpers (`DFS.putMode`,
`DFS.pushRegFrame`), the frame size bounds, and the mode-1 routine (examine the current NO move:
the inclusion, equality and cost tests, then the commit), `DFS.exists_mode1Stmt`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- **Sub-contract: one step in mode `i ∈ {1, 2, 3, 4}`** (remaining): started after the mode
was consumed (stack `9` empty), the routine performs `mstep`. -/
def ModeSpec (i : ℕ) (s : Stmt 38) (K : ℕ) : Prop :=
  ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ) (F : Frame)
    (Ks : List Frame)
    (out : BitString → Bool), BaseOK base LX cs eb → cs.length = LX.length →
    (∀ c ∈ cs, c.length = W) → eb.length = W → binVal eb + (cs.map binVal).sum < 2 ^ W →
    FrameOK LX.length (binVal eb) F →
    Exec s (Function.update (encSt base W LX.length (i, F :: Ks)) 9 [])
      (encSt base W LX.length (mstep LX.length (costV (cs.map binVal)) (binVal eb) out
        (i, F :: Ks)))
      ((encSt base W LX.length (i, F :: Ks)).space + K * (LX.length + W + 1) ^ 2)

/-- Clear all temporary stacks used by the mode routines. -/
def clearModeScratch : Stmt 38 := Stmt.seqs [Stmt.clear 17, Stmt.clear 18, Stmt.clear 19,
  Stmt.clear 20, Stmt.clear 21, Stmt.clear 22, Stmt.clear 23, Stmt.clear 24, Stmt.clear 25,
  Stmt.clear 26, Stmt.clear 27, Stmt.clear 28, Stmt.clear 29, Stmt.clear 30, Stmt.clear 31,
  Stmt.clear 32, Stmt.clear 33, Stmt.clear 34, Stmt.clear 35, Stmt.clear 36, Stmt.clear 37]

/-- Clear both the six frame registers and all mode scratch stacks. -/
def clearModeRegisters : Stmt 38 := Stmt.seqs [Stmt.clear 11, Stmt.clear 12, Stmt.clear 13,
  Stmt.clear 14, Stmt.clear 15, Stmt.clear 16, clearModeScratch]

/-- Install a unary mode on the (empty) mode stack. -/
def putMode (i : ℕ) : Stmt 38 := Stmt.pushList 9 (List.replicate i true)

/-- Push the frame currently in registers `11`--`16` directly onto the encoded frame stack.
The fields are handled in reverse order because each call prepends one self-delimiting code. -/
def pushRegFrame : Stmt 38 := Stmt.seqs [QEnum.pushCode 16 19 8, QEnum.pushCode 15 19 8,
  QEnum.pushCode 14 19 8, QEnum.pushCode 13 19 8, QEnum.pushCode 12 19 8,
  QEnum.pushCode 11 19 8]

/-- A bounded frame occupies only a linear amount of the quadratic mode allowance.  Unfold
`FrameOK` and `frameSize`, use its four length bounds, and finish by `nlinarith`. -/
theorem frameSize_le_five_square (m E W : ℕ) (F : Frame) (hF : FrameOK m E F) :
    frameSize W F ≤ 5 * (m + W + 1) ^ 2 := by
  rcases hF with ⟨hv, -, -, hf, hv', hr⟩
  unfold frameSize
  nlinarith [sq_nonneg (m + W)]

/-- Multiplying the preceding estimate by a routine constant preserves the form used in a
`ModeSpec` bound.  Apply `Nat.mul_le_mul_left` to `frameSize_le_five_square` and normalize the
products with `ring`. -/
theorem mul_frameSize_le_five_square (K m E W : ℕ) (F : Frame) (hF : FrameOK m E F) :
    K * frameSize W F ≤ (5 * K) * (m + W + 1) ^ 2 := by
  calc
    K * frameSize W F ≤ K * (5 * (m + W + 1) ^ 2) :=
      Nat.mul_le_mul_left K (frameSize_le_five_square m E W F hF)
    _ = (5 * K) * (m + W + 1) ^ 2 := by ring

/-- The concrete test phase for mode `1`: preserve the frame registers, save the equality
and inclusion flags on the empty mode stack `9`, and put the budget flag on `28`.
All cost scratch stacks are empty at the call to `sCost`. -/
def mode1Tests (sCost sSub : Stmt 38) : Stmt 38 := Stmt.seqs [
  Stmt.copy 11 17 20, Stmt.copy 15 18 20, sSub, Stmt.moveAll 19 9,
  .seq (Stmt.eqTest 11 15 20 21 22) (Stmt.moveAll 22 9), sCost, Stmt.copy 13 24 20,
  Stmt.addInto 24 19 25 26, Stmt.copy 3 27 20, Stmt.cmpInto 24 27 28]

/-- Commit the three flags produced by `mode1Tests`.  A legal NO move resets `r` from stack
`10`, pushes the changed frame, and enters mode `3`; every other case restores the frame and
enters mode `2`. -/
def mode1Commit (sPush : Stmt 38) : Stmt 38 :=
  Stmt.caseBit 9 fun heq => .seq (.pop 9) (Stmt.caseBit 9 fun hsub =>
    .seq (.pop 9) (Stmt.caseBit 28 fun hle =>
    if hsub && !heq && hle then
      Stmt.seqs [Stmt.clear 16, Stmt.copy 10 16 20, clearModeScratch, sPush, putMode 3]
    else Stmt.seqs [clearModeScratch, sPush, putMode 2]))

/-- The intermediate stack state asserted for the mode-`1` tests. -/
def mode1TestSt (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (cs : List BitString) : Stacks 38 :=
  Function.update (Function.update (Function.update (Function.update
    (regSt base W m F Ks) 17 F.v) 18 F.v') 9
      [decide (F.v = F.v'), isSub F.v F.v']) 28
      [decide (F.n + costV (cs.map binVal) F.v F.v' ≤ binVal (base 3))]

/-- State after the first `Stmt.copy 11 17 20`: the frame value `F.v` is copied onto `17`. -/
private def m1s1 (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) : Stacks 38 :=
  Function.update (regSt base W m F Ks) 17 F.v

/-- State after `Stmt.copy 15 18 20`: the frame value `F.v'` is copied onto `18`. -/
private def m1s2 (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) : Stacks 38 :=
  Function.update (m1s1 base W m F Ks) 18 F.v'

/-- State after `sSub`: the inclusion bit `isSub F.v F.v'` lands on the accumulator `19`. -/
private def m1s3 (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) : Stacks 38 :=
  Function.update (m1s2 base W m F Ks) 19 [isSub F.v F.v']

/-- State after `Stmt.moveAll 19 9`: the inclusion bit is saved on the empty mode stack. -/
private def m1s4 (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) : Stacks 38 :=
  Function.update (Function.update (m1s3 base W m F Ks) 19 []) 9 [isSub F.v F.v']

/-- State after equality testing and `moveAll 22 9`: the flags are `[eq, sub]` on `9`;
all stacks at or above `19` are empty again. -/
private def m1s5 (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) : Stacks 38 :=
  Function.update (Function.update (m1s4 base W m F Ks) 22 []) 9
    [decide (F.v = F.v'), isSub F.v F.v']

/-- State after `sCost`: the width-`W` cost accumulator `numBits W (costV …)` lands on `19`. -/
private def m1s6 (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (cs : List BitString) : Stacks 38 :=
  Function.update (m1s5 base W m F Ks) 19 (numBits W (costV (cs.map binVal) F.v F.v'))

/-- **Step 1.**  `Stmt.copy 11 17 20` copies `F.v` onto the empty register `17`.
To prove: apply `Stmt.exec_copy` (with `11 ≠ 17`, `11 ≠ 20`, `17 ≠ 20` by `decide`) to
`regSt base W m F Ks`, using `(regSt …) 20 = []` (register `20 ≥ 17` is untouched by `regSt`,
so it equals `base 20 = []`).  The output `Function.update (regSt …) 17 ((regSt …) 11 ++
(regSt …) 17)` simplifies to `m1s1` because `(regSt …) 11 = F.v` and `(regSt …) 17 = []`; then
`.mono hS` (the native cost is `(regSt …).space + (F.v).length`). -/
private theorem m1_exec_c1 (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = [])
    (S : ℕ) (hS : (regSt base W m F Ks).space + (F.v).length ≤ S) :
    Exec (Stmt.copy 11 17 20) (regSt base W m F Ks) (m1s1 base W m F Ks) S := by
  have e := Stmt.exec_copy (r := (11 : Fin 38)) (r' := (17 : Fin 38))
    (t := (20 : Fin 38)) (σ := regSt base W m F Ks)
    (by decide) (by decide) (by decide)
    (by simp [regSt, encSt, hb])
  simpa [regSt, encSt, m1s1, hb] using e.mono (by
    simpa [regSt, encSt] using hS)

/-- **Step 2.**  `Stmt.copy 15 18 20` copies `F.v'` onto the empty register `18`.
To prove: apply `Stmt.exec_copy` to `m1s1 base W m F Ks`, using `(m1s1 …) 15 = F.v'`
(register `15 ≠ 17`, so it still equals `(regSt …) 15 = F.v'`), `(m1s1 …) 18 = []` and
`(m1s1 …) 20 = []`.  The output simplifies to `m1s2`; close with `.mono hS`. -/
private theorem m1_exec_c2 (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = [])
    (S : ℕ) (hS : (m1s1 base W m F Ks).space + (F.v').length ≤ S) :
    Exec (Stmt.copy 15 18 20) (m1s1 base W m F Ks) (m1s2 base W m F Ks) S := by
  have e := Stmt.exec_copy (r := (15 : Fin 38)) (r' := (18 : Fin 38))
    (t := (20 : Fin 38)) (σ := m1s1 base W m F Ks)
    (by decide) (by decide) (by decide)
    (by simp [m1s1, regSt, encSt, hb])
  simpa [m1s1, regSt, encSt, m1s2, hb] using e.mono (by
    simpa [m1s1, regSt, encSt] using hS)

/-- **Step 3.**  `sSub` writes the inclusion bit on `19`.
To prove: apply `hSub` to `m1s2 base W m F Ks`.  Its emptiness premise
`∀ j ≥ 19, (m1s2 …) j = []` holds because `m1s2` only updates registers `17` and `18`
(both `< 19`), so for `j ≥ 19` it agrees with `regSt`, whose registers `≥ 17` are empty.  The
contract output `Function.update (m1s2 …) 19 [isSub ((m1s2 …) 17) ((m1s2 …) 18)]` equals `m1s3`
since `(m1s2 …) 17 = F.v` and `(m1s2 …) 18 = F.v'`; close with `.mono hS`. -/
private theorem m1_exec_sub (sSub : Stmt 38) (KI : ℕ)
    (hSub : ∀ σ : Stacks 38, (∀ j : Fin 38, 19 ≤ j.val → σ j = []) →
      Exec sSub σ (Function.update σ 19 [isSub (σ 17) (σ 18)])
        (σ.space + KI * ((σ 17).length + (σ 18).length + 1)))
    (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = [])
    (S : ℕ) (hS : (m1s2 base W m F Ks).space +
      KI * ((F.v).length + (F.v').length + 1) ≤ S) :
    Exec sSub (m1s2 base W m F Ks) (m1s3 base W m F Ks) S := by
  have he : ∀ j : Fin 38, 19 ≤ j.val → m1s2 base W m F Ks j = [] := by
    intro j hj
    fin_cases j <;> norm_num at hj <;> simp [m1s2, m1s1, regSt, encSt, hb]
  have e := hSub (m1s2 base W m F Ks) he
  simpa [m1s3, m1s2, m1s1] using e.mono (by simpa [m1s2, m1s1] using hS)

/-- **Step 4.** Apply `Stmt.exec_moveAll` with source `19` and destination `9`.
The mode stack is empty in `regSt`; reversing the singleton inclusion flag leaves it unchanged.
Simplify the two updates to `m1s4` and raise the execution with `.mono hS`. -/
private theorem m1_exec_move (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (_hb : ∀ j : Fin 38, 5 ≤ j.val → base j = [])
    (S : ℕ) (hS : (m1s3 base W m F Ks).space ≤ S) :
    Exec (Stmt.moveAll 19 9) (m1s3 base W m F Ks) (m1s4 base W m F Ks) S := by
  have e := Stmt.exec_moveAll (r := (19 : Fin 38)) (r' := (9 : Fin 38))
    (by decide) [isSub F.v F.v'] (m1s3 base W m F Ks) (by simp [m1s3])
  simpa [m1s4, m1s3, m1s2, m1s1, regSt, encSt] using e.mono hS

/-- **Step 5.** Apply `Stmt.exec_eqTest` with empty `20`, `21`, `22` from `hb`,
then `Stmt.exec_moveAll 22 9` to prepend the equality bit to the inclusion bit.
The move reverses only a singleton, so `9 = [eq, sub]`; `22` is empty again.
The first execution bounds the second, and both fit the same `space + 1` allowance. -/
private theorem m1_exec_eq (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = [])
    (S : ℕ) (hS : (m1s4 base W m F Ks).space + 1 ≤ S) :
    Exec (.seq (Stmt.eqTest 11 15 20 21 22) (Stmt.moveAll 22 9)) (m1s4 base W m F Ks)
      (m1s5 base W m F Ks) S := by
  let σ := m1s4 base W m F Ks
  have e := Stmt.exec_eqTest (A := (11 : Fin 38)) (B := (15 : Fin 38))
    (tA := (20 : Fin 38)) (tB := (21 : Fin 38)) (F := (22 : Fin 38)) (σ := σ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [σ, m1s4, m1s3, m1s2, m1s1, regSt, encSt, hb])
    (by simp [σ, m1s4, m1s3, m1s2, m1s1, regSt, encSt, hb])
    (by simp [σ, m1s4, m1s3, m1s2, m1s1, regSt, encSt, hb])
  have em := Stmt.exec_moveAll (r := (22 : Fin 38)) (r' := (9 : Fin 38))
    (by decide) [decide (σ 11 = σ 15)]
    (Function.update σ 22 [decide (σ 11 = σ 15)]) (by simp)
  apply Stmt.exec_of_eq (.seq (e.mono hS) (em.mono (e.space_le.2.trans hS)))
  funext j
  fin_cases j <;> simp [σ, m1s5, m1s4, m1s3, m1s2, m1s1, regSt]

/-- **Step 6 (cost).** Apply `hCost` directly to `m1s5`: the two flags are saved on
stack `9`, so every stack at or above `19` is empty. `BaseOK` supplies the cost list, budget,
and base emptiness; `heb` supplies the width and `hsum` implies the cost-list bound.
Simplify the unchanged masks on `17` and `18`, then raise the execution with `.mono hS`. -/
private theorem m1_exec_cost (sCost : Stmt 38) (KC : ℕ)
    (hCost : ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
      σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
      (cs.map binVal).sum < 2 ^ W → (∀ j : Fin 38, 19 ≤ j.val → σ j = []) →
      Exec sCost σ (Function.update σ 19
        (numBits W (costV (cs.map binVal) (σ 17) (σ 18))))
        (σ.space + KC * ((Stacks.encList cs).length + (σ 17).length +
          (σ 18).length + W + 1)))
    (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) (cs : List BitString)
    (eb : BitString)
    (LX : List BitString) (hbase : BaseOK base LX cs eb) (hcs : ∀ c ∈ cs, c.length = W)
    (heb : eb.length = W) (hsum : binVal eb + (cs.map binVal).sum < 2 ^ W)
    (S : ℕ) (hS : (m1s5 base W m F Ks).space +
      KC * ((Stacks.encList cs).length + (F.v).length + (F.v').length + W + 1) ≤ S) :
    Exec sCost (m1s5 base W m F Ks) (m1s6 base W m F Ks cs) S := by
  have he : ∀ j : Fin 38, 19 ≤ j.val → m1s5 base W m F Ks j = [] := by
    intro j hj
    fin_cases j <;> norm_num at hj <;>
      simp [m1s5, m1s4, m1s3, m1s2, m1s1, regSt, encSt, hbase.2.2.2]
  have h2 : m1s5 base W m F Ks 2 = Stacks.encList cs := by
    simpa [m1s5, m1s4, m1s3, m1s2, m1s1, regSt, encSt] using hbase.2.1
  have h3 : (m1s5 base W m F Ks 3).length = W := by
    simpa [m1s5, m1s4, m1s3, m1s2, m1s1, regSt, encSt, hbase.2.2.1] using heb
  have e := hCost (m1s5 base W m F Ks) cs W h2 hcs h3 (by omega) he
  simpa [m1s6, m1s5, m1s4, m1s3, m1s2, m1s1] using e.mono (by
    simpa [m1s5, m1s4, m1s3, m1s2, m1s1] using hS)

/-- The cost `costV ds v w` never exceeds the total of the cost list `ds`: it only adds up the
entries of `ds` that `w` selects and `v` does not.  Induction on `ds` generalizing the two bit
vectors; each cons step splits on the head bits of `v` and `w` and uses `pv_costV_cons`. -/
theorem costV_le_sum (ds : List ℕ) (v w : BitString) : costV ds v w ≤ ds.sum := by
  induction ds generalizing v w with
  | nil => simp [costV]
  | cons d ds ih =>
    cases v with
    | nil => simp [costV]
    | cons a v =>
      cases w with
      | nil => simp [costV]
      | cons b w =>
        rw [pv_costV_cons, List.sum_cons]
        have hi := ih v w
        split <;> omega

/-- **Steps 7–10 (budget comparison).**  `copy 13 24 20`, `addInto 24 19 25 26`, `copy 3 27 20`,
`cmpInto 24 27 28` compute `F.n + costV …`, compare it with the budget, and write the comparison
bit on `28`.  To prove: peel the four statements with `Stmt.exec_seqs_cons`.  `copy 13 24 20`
puts `numBits W F.n` on `24`; `addInto 24 19 25 26` replaces `24` with `addBits false (numBits W
F.n) (numBits W (costV …))` and empties `19`.  The two summands have equal length `W` (lengths of
`numBits W _`), and `F.n + costV … < 2 ^ W` by `FrameOK` (`F.n ≤ binVal eb`), `hsum`, and
`costV`-monotonicity, so `numBits_add`-style no-overflow gives `24 = numBits W (F.n + costV …)`.
`copy 3 27 20` puts `base 3 = eb` on `27`; `cmpInto 24 27 28` writes `[cmpBits true (numBits W
(F.n + costV …)) eb]` on `28` and empties `24`, `27`.  By `cmpBits_true_iff` with equal widths this
equals `[decide (F.n + costV … ≤ binVal (base 3))]`, so the final state is `mode1TestSt`.  Raise
each sub-step with `.mono`, bounded by `hS`. -/
private theorem m1_exec_rest (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (cs : List BitString) (eb : BitString) (LX : List BitString) (hbase : BaseOK base LX cs eb)
    (_hlen : cs.length = LX.length) (_hcs : ∀ c ∈ cs, c.length = W) (heb : eb.length = W)
    (hsum : binVal eb + (cs.map binVal).sum < 2 ^ W) (hF : FrameOK m (binVal eb) F)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = [])
    (S : ℕ) (hS : (m1s6 base W m F Ks cs).space + 2 * (W + 1) ≤ S) :
    Exec (Stmt.seqs [Stmt.copy 13 24 20, Stmt.addInto 24 19 25 26, Stmt.copy 3 27 20,
      Stmt.cmpInto 24 27 28]) (m1s6 base W m F Ks cs) (mode1TestSt base W m F Ks cs) S := by
  let cv := costV (cs.map binVal) F.v F.v'
  have hcv : cv ≤ (cs.map binVal).sum := costV_le_sum _ _ _
  have hn : F.n ≤ binVal eb := hF.2.2.1
  have hlt : F.n + cv < 2 ^ W := by omega
  have hcvlt : cv < 2 ^ W := by omega
  have hadd : addBits false (numBits W F.n) (numBits W cv) =
      numBits W (F.n + cv) := by
    simpa [binVal_numBits_of_lt W cv hcvlt] using
      addBits_numBits W F.n (numBits W cv) (by simp [numBits]) (by
        rw [binVal_numBits_of_lt W cv hcvlt]
        exact hlt)
  have hcmp : cmpBits true (numBits W (F.n + cv)) eb =
      decide (F.n + cv ≤ binVal eb) := by
    rw [Bool.eq_iff_iff, cmpBits_true_iff, decide_eq_true_eq,
      binVal_numBits_of_lt W (F.n + cv) hlt]
    simp [numBits, heb]
  let σ₀ := m1s6 base W m F Ks cs
  let σ₁ : Stacks 38 := Function.update σ₀ 24 (numBits W F.n)
  let σ₁' : Stacks 38 := Function.update σ₁ 24
    (addBits false (numBits W F.n) (numBits W cv))
  let σ₂ : Stacks 38 := Function.update σ₁' 19 []
  let σ₃ : Stacks 38 := Function.update σ₂ 27 eb
  let σ₄ : Stacks 38 := Function.update (Function.update (Function.update σ₃ 24 []) 27 []) 28
    [cmpBits true (numBits W (F.n + cv)) eb]
  have hnumlen (x : ℕ) : (numBits W x).length = W := by simp [numBits]
  have hS₀ : σ₀.space + 2 * (W + 1) ≤ S := by simpa [σ₀] using hS
  have h₀13 : σ₀ 13 = numBits W F.n := by
    simp [σ₀, m1s6, m1s5, m1s4, m1s3, m1s2, m1s1, regSt]
  have h₀19 : σ₀ 19 = numBits W cv := by simp [σ₀, cv, m1s6]
  have h₀20 : σ₀ 20 = [] := by
    simp [σ₀, m1s6, m1s5, m1s4, m1s3, m1s2, m1s1, regSt, encSt, hb]
  have h₀24 : σ₀ 24 = [] := by
    simp [σ₀, m1s6, m1s5, m1s4, m1s3, m1s2, m1s1, regSt, encSt, hb]
  have e₁₀ := Stmt.exec_copy (k := 38) (r := (13 : Fin 38)) (r' := 24) (t := 20)
    (by decide) (by decide) (by decide) (σ := σ₀) h₀20
  have e₁ : Exec (Stmt.copy 13 24 20) σ₀ σ₁ S := by
    have hbound : σ₀.space + (σ₀ 13).length ≤ S := by
      rw [h₀13, hnumlen]
      exact le_trans (by omega) hS₀
    exact Stmt.exec_of_eq (e₁₀.mono hbound) (by simp [σ₁, h₀13, h₀24])
  have hsp₁ : σ₁.space = σ₀.space + W := by
    have hu := Stacks.space_update σ₀ (24 : Fin 38) (numBits W F.n)
    rw [h₀24, hnumlen] at hu
    simpa [σ₁] using hu
  have h₁24 : σ₁ 24 = numBits W F.n := by simp [σ₁]
  have h₁19 : σ₁ 19 = numBits W cv := by simp [σ₁, h₀19]
  have h₁25 : σ₁ 25 = [] := by
    simp [σ₁, σ₀, m1s6, m1s5, m1s4, m1s3, m1s2, m1s1, regSt, encSt, hb]
  have h₁26 : σ₁ 26 = [] := by
    simp [σ₁, σ₀, m1s6, m1s5, m1s4, m1s3, m1s2, m1s1, regSt, encSt, hb]
  have e₂₀ := Stmt.exec_addInto (k := 38) (A := (24 : Fin 38)) (B := 19)
    (Cy := 25) (R := 26) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (σ := σ₁) (l := numBits W F.n) (m := numBits W cv)
    (by simp [numBits]) h₁24 h₁19 h₁25 h₁26
  have e₂ : Exec (Stmt.addInto 24 19 25 26) σ₁ σ₂ S := by
    have hbound : σ₁.space + 1 ≤ S := by
      calc
        σ₁.space + 1 = σ₀.space + W + 1 := by omega
        _ ≤ σ₀.space + 2 * (W + 1) := by omega
        _ ≤ S := hS₀
    simpa [σ₂, σ₁'] using e₂₀.mono hbound
  have hlenadd : (addBits false (numBits W F.n) (numBits W cv)).length = W := by
    rw [length_addBits false (numBits W F.n) (numBits W cv) (by simp [numBits])]
    simp [numBits]
  have hsp₁' : σ₁'.space = σ₁.space := by
    have hu := Stacks.space_update σ₁ (24 : Fin 38)
      (addBits false (numBits W F.n) (numBits W cv))
    rw [h₁24, hnumlen, hlenadd] at hu
    simpa [σ₁'] using hu
  have h₁'19 : σ₁' 19 = numBits W cv := by simp [σ₁', h₁19]
  have hsp₂ : σ₂.space = σ₀.space := by
    have hu := Stacks.space_update σ₁' (19 : Fin 38) []
    rw [h₁'19, hnumlen] at hu
    simp only [List.length_nil, Nat.add_zero] at hu
    change Stacks.space (Function.update σ₁' 19 []) = σ₀.space
    change Stacks.space (Function.update σ₁' 19 []) + W = σ₁'.space at hu
    omega
  have h₂3 : σ₂ 3 = eb := by
    simpa [σ₂, σ₁', σ₁, σ₀, m1s6, m1s5, m1s4, m1s3, m1s2, m1s1, regSt,
      encSt] using hbase.2.2.1
  have h₂20 : σ₂ 20 = [] := by
    simp [σ₂, σ₁', σ₁, σ₀, m1s6, m1s5, m1s4, m1s3, m1s2, m1s1, regSt,
      encSt, hb]
  have h₂27 : σ₂ 27 = [] := by
    simp [σ₂, σ₁', σ₁, σ₀, m1s6, m1s5, m1s4, m1s3, m1s2, m1s1, regSt,
      encSt, hb]
  have e₃₀ := Stmt.exec_copy (k := 38) (r := (3 : Fin 38)) (r' := 27) (t := 20)
    (by decide) (by decide) (by decide) (σ := σ₂) h₂20
  have e₃ : Exec (Stmt.copy 3 27 20) σ₂ σ₃ S := by
    have hbound : σ₂.space + (σ₂ 3).length ≤ S := by
      rw [h₂3, heb]
      calc
        σ₂.space + W = σ₀.space + W := by omega
        _ ≤ σ₀.space + 2 * (W + 1) := by omega
        _ ≤ S := hS₀
    exact Stmt.exec_of_eq (e₃₀.mono hbound) (by simp [σ₃, h₂3, h₂27])
  have hsp₃ : σ₃.space = σ₀.space + W := by
    have hu := Stacks.space_update σ₂ (27 : Fin 38) eb
    rw [h₂27, heb] at hu
    have hsp₃₂ : σ₃.space = σ₂.space + W := by simpa [σ₃] using hu
    omega
  have h₃24 : σ₃ 24 = numBits W (F.n + cv) := by
    simp [σ₃, σ₂, σ₁', hadd]
  have h₃27 : σ₃ 27 = eb := by simp [σ₃]
  have h₃28 : σ₃ 28 = [] := by
    simp [σ₃, σ₂, σ₁', σ₁, σ₀, m1s6, m1s5, m1s4, m1s3, m1s2, m1s1, regSt,
      encSt, hb]
  have e₄₀ := Stmt.exec_cmpInto (k := 38) (A := (24 : Fin 38)) (B := 27) (F := 28)
    (by decide) (by decide) (by decide) (σ := σ₃) (l := numBits W (F.n + cv)) (m := eb)
    (by simp [numBits, heb]) h₃24 h₃27 h₃28
  have e₄ : Exec (Stmt.cmpInto 24 27 28) σ₃ σ₄ S := by
    have hbound : σ₃.space + 1 ≤ S := by
      calc
        σ₃.space + 1 = σ₀.space + W + 1 := by omega
        _ ≤ σ₀.space + 2 * (W + 1) := by omega
        _ ≤ S := hS₀
    simpa [σ₄] using e₄₀.mono hbound
  have hfinal : σ₄ = mode1TestSt base W m F Ks cs := by
    funext j
    fin_cases j <;>
      simp [σ₄, σ₃, σ₂, σ₁', σ₁, σ₀, cv, hcmp, mode1TestSt, m1s6, m1s5, m1s4,
        m1s3, m1s2, m1s1, regSt, encSt, hbase.2.2.1, hb]
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ₁, e₁, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ₂, e₂, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ₃, e₃, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨mode1TestSt base W m F Ks cs, Stmt.exec_of_eq e₄ hfinal, ?_⟩
  exact .skip (Stmt.exec_of_eq e₄ hfinal).space_le.2


/-- Writing a word to one stack raises the total space by at most the length of that word. -/
private theorem space_update_le_add {k : ℕ} (σ : Stacks k) (r : Fin k) (v : BitString) :
    Stacks.space (Function.update σ r v) ≤ σ.space + v.length := by
  have := σ.space_update r v
  omega

/-- The frame registers of `regSt`, the copies of `F.v` and `F.v'`, a width-`W` word and four
spare bits fit in the space of the encoded stack `encSt … (1, F :: Ks)`. -/
private theorem m1_regSt_space_le (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) :
    (regSt base W m F Ks).space + (F.v.length + F.v'.length + W + 4) ≤
      (encSt base W m (1, F :: Ks)).space := by
  zify
  dsimp [regSt, encSt]
  simp only [space_update_int, Function.update]
  simp only [Stacks.length_encList, List.flatMap_cons, List.map_append, List.sum_append]
  dsimp [Frame.fields, numBits]
  simp only [List.length_map, List.length_range, List.length_replicate, List.map_cons,
    List.sum_cons, List.sum_nil, List.map_nil]
  omega

/-- **Space budget.** All seven phase costs fit inside a single quadratic budget
`(encSt base W m (1, F :: Ks)).space + K * (m + W + 1) ^ 2`.  To prove: each intermediate state's
`space` differs from `(encSt …).space` by at most the total register content, which is bounded by a
constant times `(m + W + 1)` (every field length is `≤ m` by `FrameOK`, `(Stacks.encList cs).length`
is `m * (2 * W + 1)`, and each `numBits W _` has length `W`). The encoded cost list
and the cost-call allowance are quadratic in `m + W + 1`; the other native deltas
(`(F.v).length`, `KI * (…)`, `2 * (W + 1)`, …) are linear, so each sum is
`≤ (encSt …).space + C * (m + W + 1) ^ 2` for a constant `C` depending only on `KC`, `KI`; take
`K := C`.  Discharge the seven conjuncts with the length bounds and `nlinarith`/`Nat` arithmetic. -/
private theorem m1_space_bound (KC KI : ℕ) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) (cs : List BitString)
      (eb : BitString), (∀ c ∈ cs, c.length = W) → eb.length = W →
      binVal eb + (cs.map binVal).sum < 2 ^ W → FrameOK m (binVal eb) F → cs.length = m →
      ((regSt base W m F Ks).space + (F.v).length ≤
          (encSt base W m (1, F :: Ks)).space + K * (m + W + 1) ^ 2) ∧
      ((m1s1 base W m F Ks).space + (F.v').length ≤
          (encSt base W m (1, F :: Ks)).space + K * (m + W + 1) ^ 2) ∧
      ((m1s2 base W m F Ks).space + KI * ((F.v).length + (F.v').length + 1) ≤
          (encSt base W m (1, F :: Ks)).space + K * (m + W + 1) ^ 2) ∧
      ((m1s3 base W m F Ks).space ≤
          (encSt base W m (1, F :: Ks)).space + K * (m + W + 1) ^ 2) ∧
      ((m1s4 base W m F Ks).space + 1 ≤
          (encSt base W m (1, F :: Ks)).space + K * (m + W + 1) ^ 2) ∧
      ((m1s5 base W m F Ks).space +
            KC * ((Stacks.encList cs).length + (F.v).length + (F.v').length + W + 1) ≤
          (encSt base W m (1, F :: Ks)).space + K * (m + W + 1) ^ 2) ∧
      ((m1s6 base W m F Ks cs).space + 2 * (W + 1) ≤
          (encSt base W m (1, F :: Ks)).space + K * (m + W + 1) ^ 2) := by
  refine ⟨2 * KI + 5 * KC + 2, ?_⟩
  intro base W m F Ks cs eb hcs _heb _hsum hF hlen
  rcases hF with ⟨hv, _hy, _hn, _hf, hv', _hr⟩
  have henc : (Stacks.encList cs).length ≤ m * (2 * W + 1) := by
    rw [← hlen]
    exact QEnum.length_encList_le W cs fun c hc => by simp [hcs c hc]
  have hkey := m1_regSt_space_le base W m F Ks
  have hs0 : (regSt base W m F Ks).space ≤ (encSt base W m (1, F :: Ks)).space := by omega
  have h1 : (m1s1 base W m F Ks).space ≤ (regSt base W m F Ks).space + F.v.length :=
    space_update_le_add _ _ _
  have hs1 : (m1s1 base W m F Ks).space ≤ (encSt base W m (1, F :: Ks)).space := by omega
  have h2 : (m1s2 base W m F Ks).space ≤ (m1s1 base W m F Ks).space + F.v'.length :=
    space_update_le_add _ _ _
  have hs2 : (m1s2 base W m F Ks).space ≤ (encSt base W m (1, F :: Ks)).space := by omega
  have h3 : (m1s3 base W m F Ks).space ≤ (m1s2 base W m F Ks).space + 1 :=
    space_update_le_add _ _ _
  have hs3 : (m1s3 base W m F Ks).space ≤ (encSt base W m (1, F :: Ks)).space := by omega
  have h4 : (m1s4 base W m F Ks).space ≤ (m1s3 base W m F Ks).space + 1 :=
    (space_update_le_add _ _ _).trans
      (Nat.add_le_add_right (Stacks.space_update_le _ 19 [] (by simp)) _)
  have hs4 : (m1s4 base W m F Ks).space ≤ (encSt base W m (1, F :: Ks)).space := by omega
  have h5 : (m1s5 base W m F Ks).space ≤ (m1s4 base W m F Ks).space + 2 :=
    (space_update_le_add _ _ _).trans
      (Nat.add_le_add_right (Stacks.space_update_le _ 22 [] (by simp)) _)
  have hs5 : (m1s5 base W m F Ks).space ≤ (encSt base W m (1, F :: Ks)).space := by omega
  have h6 : (m1s6 base W m F Ks cs).space ≤ (m1s5 base W m F Ks).space + W :=
    (space_update_le_add _ _ _).trans (by simp [numBits])
  have hs6 : (m1s6 base W m F Ks cs).space ≤ (encSt base W m (1, F :: Ks)).space := by omega
  have hA : m + W + 1 ≤ (m + W + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hunit : (m + W + 1) ^ 2 ≤
      (2 * KI + 5 * KC + 2) * (m + W + 1) ^ 2 := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hvK : F.v.length ≤ (2 * KI + 5 * KC + 2) * (m + W + 1) ^ 2 := by
    calc
      F.v.length = m := hv
      _ ≤ m + W + 1 := by omega
      _ ≤ (m + W + 1) ^ 2 := hA
      _ ≤ _ := hunit
  have hvK' : F.v'.length ≤ (2 * KI + 5 * KC + 2) * (m + W + 1) ^ 2 := by
    calc
      F.v'.length ≤ m := hv'
      _ ≤ m + W + 1 := by omega
      _ ≤ (m + W + 1) ^ 2 := hA
      _ ≤ _ := hunit
  have hKI : KI * (F.v.length + F.v'.length + 1) ≤
      (2 * KI + 5 * KC + 2) * (m + W + 1) ^ 2 := by
    calc
      KI * (F.v.length + F.v'.length + 1) ≤ KI * (2 * (m + W + 1)) :=
        Nat.mul_le_mul_left KI (by omega)
      _ = (2 * KI) * (m + W + 1) := by ring
      _ ≤ (2 * KI) * (m + W + 1) ^ 2 := Nat.mul_le_mul_left _ hA
      _ ≤ (2 * KI + 5 * KC + 2) * (m + W + 1) ^ 2 :=
        Nat.mul_le_mul_right _ (by omega)
  have hprod : m * (2 * W + 1) ≤ 2 * (m + W + 1) ^ 2 := by
    calc
      m * (2 * W + 1) ≤ (m + W + 1) * (2 * (m + W + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (m + W + 1) ^ 2 := by ring
  have hdata : (Stacks.encList cs).length + F.v.length + F.v'.length + W + 1 ≤
      5 * (m + W + 1) ^ 2 := by
    calc
      (Stacks.encList cs).length + F.v.length + F.v'.length + W + 1 ≤
          2 * (m + W + 1) ^ 2 + 3 * (m + W + 1) := by omega
      _ ≤ 2 * (m + W + 1) ^ 2 + 3 * (m + W + 1) ^ 2 := by omega
      _ = 5 * (m + W + 1) ^ 2 := by ring
  have hKC : KC * ((Stacks.encList cs).length + F.v.length + F.v'.length + W + 1) ≤
      (2 * KI + 5 * KC + 2) * (m + W + 1) ^ 2 := by
    calc
      KC * ((Stacks.encList cs).length + F.v.length + F.v'.length + W + 1) ≤
          KC * (5 * (m + W + 1) ^ 2) := Nat.mul_le_mul_left KC hdata
      _ = (5 * KC) * (m + W + 1) ^ 2 := by ring
      _ ≤ (2 * KI + 5 * KC + 2) * (m + W + 1) ^ 2 :=
        Nat.mul_le_mul_right _ (by omega)
  have htwo : 2 * (W + 1) ≤
      (2 * KI + 5 * KC + 2) * (m + W + 1) ^ 2 := by
    calc
      2 * (W + 1) ≤ 2 * (m + W + 1) := Nat.mul_le_mul_left 2 (by omega)
      _ ≤ 2 * (m + W + 1) ^ 2 := Nat.mul_le_mul_left 2 hA
      _ ≤ (2 * KI + 5 * KC + 2) * (m + W + 1) ^ 2 :=
        Nat.mul_le_mul_right _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Prove the test phase by two `Stmt.exec_copy` calls, `exists_isSubStmt`, `exec_eqTest`, and
`exists_costVStmt`, followed by `exec_addInto` and `exec_cmpInto`.  The width hypotheses turn
the binary arithmetic results into `numBits`, and the linear temporary space fits this bound. -/
theorem exec_mode1Tests (sCost sSub : Stmt 38) (KC KI : ℕ)
    (hCost : ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
      σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
      (cs.map binVal).sum < 2 ^ W → (∀ j : Fin 38, 19 ≤ j.val → σ j = []) →
      Exec sCost σ (Function.update σ 19
        (numBits W (costV (cs.map binVal) (σ 17) (σ 18))))
        (σ.space + KC * ((Stacks.encList cs).length + (σ 17).length +
          (σ 18).length + W + 1)))
    (hSub : ∀ σ : Stacks 38, (∀ j : Fin 38, 19 ≤ j.val → σ j = []) →
      Exec sSub σ (Function.update σ 19 [isSub (σ 17) (σ 18)])
        (σ.space + KI * ((σ 17).length + (σ 18).length + 1))) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
      (F : Frame) (Ks : List Frame), BaseOK base LX cs eb → cs.length = LX.length →
      (∀ c ∈ cs, c.length = W) → eb.length = W →
      binVal eb + (cs.map binVal).sum < 2 ^ W → FrameOK LX.length (binVal eb) F →
      Exec (mode1Tests sCost sSub) (regSt base W LX.length F Ks)
        (mode1TestSt base W LX.length F Ks cs)
        ((encSt base W LX.length (1, F :: Ks)).space + K * (LX.length + W + 1) ^ 2) := by
  obtain ⟨K, hbound⟩ := m1_space_bound KC KI
  refine ⟨K, fun base LX cs eb W F Ks hbase hlen hcs heb hsum hF => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ :=
    hbound base W LX.length F Ks cs eb hcs heb hsum hF hlen
  unfold mode1Tests
  rw [Stmt.exec_seqs_cons]
  refine ⟨m1s1 base W LX.length F Ks, m1_exec_c1 base W LX.length F Ks hbase.2.2.2 _ b1, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨m1s2 base W LX.length F Ks, m1_exec_c2 base W LX.length F Ks hbase.2.2.2 _ b2, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨m1s3 base W LX.length F Ks, m1_exec_sub sSub KI hSub base W LX.length F Ks
      hbase.2.2.2 _ b3, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨m1s4 base W LX.length F Ks, m1_exec_move base W LX.length F Ks hbase.2.2.2 _ b4, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨m1s5 base W LX.length F Ks, m1_exec_eq base W LX.length F Ks hbase.2.2.2 _ b5, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨m1s6 base W LX.length F Ks cs,
    m1_exec_cost sCost KC hCost base W LX.length F Ks cs eb LX hbase hcs heb hsum _ b6, ?_⟩
  exact m1_exec_rest base W LX.length F Ks cs eb LX hbase hlen hcs heb hsum hF hbase.2.2.2 _ b7

/-- Clearing the registers of a list one after the other costs no space beyond the start state:
it turns `σ` into any state `ρ` that is empty on the list and agrees with `σ` off the list. -/
private theorem m1c_exec_clearList (l : List (Fin 38)) (σ ρ : Stacks 38)
    (hσρ : ∀ j, j ∉ l → σ j = ρ j) (hρ : ∀ j ∈ l, ρ j = []) :
    Exec (Stmt.seqs (l.map Stmt.clear)) σ ρ σ.space := by
  induction l generalizing σ with
  | nil =>
    obtain rfl : σ = ρ := funext fun j => hσρ j (by simp)
    exact .skip le_rfl
  | cons r l ih =>
    refine .seq (Stmt.exec_clear r (σ r) σ rfl) ((ih (Function.update σ r []) ?_
      fun j hj => hρ j (List.mem_cons_of_mem r hj)).mono
        (Stacks.space_update_le σ r [] (by simp)))
    intro j hj
    by_cases hjr : j = r
    · subst hjr
      simp [hρ j (by simp)]
    · rw [Function.update_of_ne hjr]
      exact hσρ j (by simp [hjr, hj])

/-- Clearing the scratch registers `17`–`37` costs no space: it turns `τ` into any state `ρ`
that agrees with `τ` below `17` and is empty from `17` on. -/
private theorem m1c_exec_clearScratch (τ ρ : Stacks 38)
    (hlow : ∀ j : Fin 38, j.val < 17 → τ j = ρ j)
    (hhigh : ∀ j : Fin 38, 17 ≤ j.val → ρ j = []) :
    Exec clearModeScratch τ ρ τ.space := by
  let l : List (Fin 38) := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33,
    34, 35, 36, 37]
  have hmem : ∀ j : Fin 38, j ∈ l ↔ 17 ≤ j.val := by
    intro j
    have hj := j.isLt
    simp only [l, List.mem_cons, Fin.ext_iff]
    simp
    omega
  exact m1c_exec_clearList l τ ρ (fun j hj => hlow j (not_le.1 fun h => hj ((hmem j).2 h)))
    fun j hj => hhigh j ((hmem j).1 hj)

/-- The registers `17`–`37` of `regSt` are empty when `base` is empty from register `5` on. -/
private theorem m1c_regSt_high (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) (j : Fin 38) (hj : 17 ≤ j.val) :
    regSt base W m F Ks j = [] := by
  have hne : ∀ k : Fin 38, k.val < 17 → j ≠ k := fun k hk h => by rw [h] at hj; omega
  unfold regSt encSt
  rw [Function.update_of_ne (hne 16 (by decide)), Function.update_of_ne (hne 15 (by decide)),
    Function.update_of_ne (hne 14 (by decide)), Function.update_of_ne (hne 13 (by decide)),
    Function.update_of_ne (hne 12 (by decide)), Function.update_of_ne (hne 11 (by decide)),
    Function.update_of_ne (hne 9 (by decide)), Function.update_of_ne (hne 10 (by decide)),
    Function.update_of_ne (hne 9 (by decide)), Function.update_of_ne (hne 8 (by decide))]
  exact hb j (by omega)

/-- Replacing the field `r` of the popped frame changes only register `16` of `regSt`. -/
private theorem m1c_regSt_setR (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (r : BitString) :
    regSt base W m { F with r := r } Ks = Function.update (regSt base W m F Ks) 16 r := by
  simp only [regSt, Function.update_idem]

/-- Installing the unary mode `i` on the empty mode stack of the mode-`0` state gives the
mode-`i` state. -/
private theorem m1c_encSt_mode (base : Stacks 38) (W m i : ℕ) (Fs : List Frame) :
    Function.update (encSt base W m (0, Fs)) 9 (List.replicate i true) =
      encSt base W m (i, Fs) := by
  simp only [encSt]
  rw [Function.update_comm (by decide : (10 : Fin 38) ≠ 9), Function.update_idem]

/-- The mode stack contributes exactly its unary length to the space of an encoded state. -/
private theorem m1c_encSt_space (base : Stacks 38) (W m i : ℕ) (Fs : List Frame) :
    (encSt base W m (i, Fs)).space = (encSt base W m (0, Fs)).space + i := by
  have h9 : encSt base W m (0, Fs) 9 = [] := by simp [encSt]
  have h := Stacks.space_update (encSt base W m (0, Fs)) 9 (List.replicate i true)
  rw [m1c_encSt_mode, h9] at h
  simpa using h

/-- Replacing the YES answer `r` of the top frame changes the space of the encoded mode-`0`
state by twice the change of the length of `r`. -/
private theorem m1c_encSt_space_setR (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (r : BitString) :
    (encSt base W m (0, { F with r := r } :: Ks)).space + 2 * F.r.length =
      (encSt base W m (0, F :: Ks)).space + 2 * r.length := by
  zify
  dsimp [encSt]
  simp only [space_update_int, Function.update]
  simp only [Stacks.length_encList, List.flatMap_cons, List.map_append, List.sum_append]
  dsimp [Frame.fields, numBits]
  simp only [List.length_map, List.length_range, List.length_replicate, List.map_cons,
    List.sum_cons, List.sum_nil, List.map_nil]
  omega

/-- The four registers written by the mode-`1` tests (`17`, `18`, the mode stack `9` and the
budget flag `28`) add at most their contents to the space of the frame registers `regSt`. -/
private theorem m1c_testSt_space_le (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (cs : List BitString) :
    (mode1TestSt base W m F Ks cs).space ≤
      (regSt base W m F Ks).space + F.v.length + F.v'.length + 3 := by
  unfold mode1TestSt
  generalize regSt base W m F Ks = R
  have h1 := Stacks.space_update R 17 F.v
  have h2 := Stacks.space_update (Function.update R 17 F.v) 18 F.v'
  have h3 := Stacks.space_update (Function.update (Function.update R 17 F.v) 18 F.v') 9
    [decide (F.v = F.v'), isSub F.v F.v']
  have h4 := Stacks.space_update (Function.update (Function.update (Function.update R 17 F.v) 18
    F.v') 9 [decide (F.v = F.v'), isSub F.v F.v']) 28
    [decide (F.n + costV (cs.map binVal) F.v F.v' ≤ binVal (base 3))]
  simp only [List.length_cons, List.length_nil] at h3 h4
  omega

/-- The tail shared by both commit branches: from a state `τ` that agrees with the frame registers
of `G` below `17`, clear the scratch registers, push `G` back with the supplied run of `sPush`, and
install the unary mode `i`. -/
private theorem m1c_exec_clearPushPut (sPush : Stmt 38) (base : Stacks 38) (W m : ℕ) (G : Frame)
    (Ks : List Frame) (i : ℕ) (τ : Stacks 38) (S : ℕ)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = [])
    (hτ : ∀ j : Fin 38, j.val < 17 → τ j = regSt base W m G Ks j) (hτS : τ.space ≤ S)
    (ep : Exec sPush (regSt base W m G Ks)
      (Function.update (encSt base W m (0, G :: Ks)) 9 []) S)
    (hS : (encSt base W m (i, G :: Ks)).space ≤ S) :
    Exec (Stmt.seqs [clearModeScratch, sPush, putMode i]) τ
      (encSt base W m (i, G :: Ks)) S := by
  have es : Exec clearModeScratch τ (regSt base W m G Ks) S :=
    (m1c_exec_clearScratch τ _ hτ (m1c_regSt_high base W m G Ks hb)).mono hτS
  let υ : Stacks 38 := Function.update (encSt base W m (0, G :: Ks)) 9 []
  have hυ : υ.space ≤ (encSt base W m (0, G :: Ks)).space :=
    Stacks.space_update_le _ _ _ (by simp)
  have em₀ := Stmt.exec_pushList (k := 38) 9 (List.replicate i true) υ
  have hemS : υ.space + (List.replicate i true).length ≤ S := by
    have := m1c_encSt_space base W m i (G :: Ks)
    rw [List.length_replicate]
    omega
  have em : Exec (putMode i) υ (encSt base W m (i, G :: Ks)) S := by
    unfold putMode
    refine Stmt.exec_of_eq (em₀.mono hemS) ?_
    rw [← m1c_encSt_mode base W m i (G :: Ks)]
    simp [υ]
  exact .seq es (.seq ep (.seq em (.skip em.space_le.2)))

/-- Prove the commit phase by splitting the three one-bit flags with `exec_caseBit`.  In the
true branch clear `16`, copy the zero vector, apply the supplied push-frame contract, and set
mode `3`; in all other branches clear scratch, push the unchanged frame, and set mode `2`. -/
theorem exec_mode1Commit (sPush : Stmt 38) (KP : ℕ)
    (hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPush (regSt base W m F Ks)
        (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        ((encSt base W m (0, F :: Ks)).space + KP * frameSize W F)) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
      (F : Frame) (Ks : List Frame) (out : BitString → Bool), BaseOK base LX cs eb →
      FrameOK LX.length (binVal eb) F →
      Exec (mode1Commit sPush) (mode1TestSt base W LX.length F Ks cs)
        (encSt base W LX.length (mstep LX.length (costV (cs.map binVal)) (binVal eb) out
          (1, F :: Ks)))
        ((encSt base W LX.length (1, F :: Ks)).space + K * (LX.length + W + 1) ^ 2) := by
  refine ⟨5 * KP + 50, ?_⟩
  intro base LX cs eb W F Ks out hbase hF
  rcases hbase with ⟨hb1, hb2, hb3, hbrest⟩
  let σ := mode1TestSt base W LX.length F Ks cs
  let σ₁ := Function.update σ 9 [isSub F.v F.v']
  let τ := Function.update σ₁ 9 []
  let F' : Frame := { F with r := List.replicate LX.length false }
  let S := (encSt base W LX.length (1, F :: Ks)).space +
    (5 * KP + 50) * (LX.length + W + 1) ^ 2
  have hF' : FrameOK LX.length (binVal eb) F' := by
    rcases hF with ⟨hv, hy, hn, hf, hv', hr⟩
    exact ⟨hv, hy, hn, hf, hv', by simp [F']⟩
  have hframe := mul_frameSize_le_five_square 8 LX.length (binVal eb) W F hF
  have hpframe := mul_frameSize_le_five_square KP LX.length (binVal eb) W F hF
  have hpframe' := mul_frameSize_le_five_square KP LX.length (binVal eb) W F' hF'
  obtain ⟨hv, -, -, -, hv', hr⟩ := hF
  have hq : 1 ≤ (LX.length + W + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
  have hm : LX.length + W + 1 ≤ (LX.length + W + 1) ^ 2 := Nat.le_pow (by omega)
  have henc1 := m1c_encSt_space base W LX.length 1 (F :: Ks)
  have henc2 := m1c_encSt_space base W LX.length 2 (F :: Ks)
  have henc3 : (encSt base W LX.length (3, F' :: Ks)).space =
      (encSt base W LX.length (0, F' :: Ks)).space + 3 :=
    m1c_encSt_space base W LX.length 3 (F' :: Ks)
  have hsetR : (encSt base W LX.length (0, F' :: Ks)).space + 2 * F.r.length =
      (encSt base W LX.length (0, F :: Ks)).space + 2 * LX.length := by
    have := m1c_encSt_space_setR base W LX.length F Ks (List.replicate LX.length false)
    rwa [List.length_replicate] at this
  have hreg := pushFrameEncode_space base W LX.length F Ks
  have hσsp : Stacks.space σ ≤
      (regSt base W LX.length F Ks).space + F.v.length + F.v'.length + 3 :=
    m1c_testSt_space_le base W LX.length F Ks cs
  have hσS : Stacks.space σ + LX.length ≤ S := by
    dsimp only [S]
    rw [Nat.add_mul]
    omega
  have hτσ : Stacks.space τ ≤ Stacks.space σ := by
    have h₁ : Stacks.space σ₁ ≤ Stacks.space σ := by
      apply Stacks.space_update_le
      simp [σ, mode1TestSt]
    have h₂ : Stacks.space τ ≤ Stacks.space σ₁ := by
      apply Stacks.space_update_le
      simp
    exact h₂.trans h₁
  have hτS : Stacks.space τ ≤ S := hτσ.trans (by omega)
  have hτ : ∀ j : Fin 38, j.val < 17 → τ j = regSt base W LX.length F Ks j := by
    intro j hj
    by_cases h9 : j = 9
    · subst h9
      simp [τ, regSt]
    · have hne : ∀ k : Fin 38, 17 ≤ k.val → j ≠ k := fun k hk h => by rw [h] at hj; omega
      simp only [τ, σ₁, σ, mode1TestSt, Function.update_of_ne h9,
        Function.update_of_ne (hne 28 (by decide)), Function.update_of_ne (hne 18 (by decide)),
        Function.update_of_ne (hne 17 (by decide))]
  have hfalse : Exec (Stmt.seqs [clearModeScratch, sPush, putMode 2]) τ
      (encSt base W LX.length (2, F :: Ks)) S := by
    refine m1c_exec_clearPushPut sPush base W LX.length F Ks 2 τ S hbrest hτ hτS
      ((hPush base W LX.length F Ks hbrest).mono ?_) ?_
    · dsimp only [S]
      rw [Nat.add_mul]
      omega
    · dsimp only [S]
      rw [Nat.add_mul]
      omega
  have htrue : Exec (Stmt.seqs [Stmt.clear 16, Stmt.copy 10 16 20, clearModeScratch, sPush,
      putMode 3]) τ (encSt base W LX.length (3, F' :: Ks)) S := by
    let ρ := Function.update τ 16 []
    let κ := Function.update τ 16 (List.replicate LX.length false)
    have h20 : ρ 20 = [] := by
      simpa [ρ, τ, σ₁, σ, mode1TestSt] using
        m1c_regSt_high base W LX.length F Ks hbrest 20 (by decide)
    have h10 : ρ 10 = List.replicate LX.length false := by
      simp only [ρ, Function.update_of_ne (show (10 : Fin 38) ≠ 16 by decide)]
      rw [hτ 10 (by decide)]
      simp [regSt, encSt]
    have ec : Exec (Stmt.clear 16) τ ρ S := (Stmt.exec_clear 16 (τ 16) τ rfl).mono hτS
    have hcopyS : Stacks.space ρ + (ρ 10).length ≤ S := by
      have hρτ : Stacks.space ρ ≤ Stacks.space τ := Stacks.space_update_le _ _ _ (by simp)
      rw [h10, List.length_replicate]
      omega
    have ecopy := (Stmt.exec_copy (r := (10 : Fin 38)) (r' := (16 : Fin 38))
      (t := (20 : Fin 38)) (by decide) (by decide) (by decide) h20).mono hcopyS
    have eκ : Exec (Stmt.copy 10 16 20) ρ κ S := by
      refine Stmt.exec_of_eq ecopy ?_
      rw [h10, show ρ 16 = [] by simp [ρ], List.append_nil]
      exact Function.update_idem _ _ _
    have hκ : ∀ j : Fin 38, j.val < 17 → κ j = regSt base W LX.length F' Ks j := by
      intro j hj
      change κ j = regSt base W LX.length { F with r := List.replicate LX.length false } Ks j
      rw [m1c_regSt_setR]
      by_cases h16 : j = 16
      · subst h16
        simp [κ]
      · simp only [κ, Function.update_of_ne h16]
        exact hτ j hj
    refine .seq ec (.seq eκ (m1c_exec_clearPushPut sPush base W LX.length F' Ks 3 κ S hbrest hκ
      eκ.space_le.2 ((hPush base W LX.length F' Ks hbrest).mono ?_) ?_))
    · dsimp only [S]
      rw [Nat.add_mul]
      omega
    · dsimp only [S]
      rw [Nat.add_mul]
      omega
  have h9 : σ 9 = [decide (F.v = F.v'), isSub F.v F.v'] := by
    simp [σ, mode1TestSt]
  rw [mode1Commit, Stmt.exec_caseBit h9]
  have epop₁ := Stmt.exec_pop_cons h9 (S := S) (by omega)
  refine .seq (by simpa [σ₁] using epop₁) ?_
  have h9₁ : σ₁ 9 = [isSub F.v F.v'] := by simp [σ₁]
  rw [Stmt.exec_caseBit h9₁]
  have epop₂ := Stmt.exec_pop_cons h9₁ (S := S) (by
    have := epop₁.space_le.2
    simpa [σ₁] using this)
  refine .seq (by simpa [τ] using epop₂) ?_
  have h28 : τ 28 =
      [decide (F.n + costV (cs.map binVal) F.v F.v' ≤ binVal (base 3))] := by
    simp [τ, σ₁, σ, mode1TestSt]
  rw [Stmt.exec_caseBit h28]
  by_cases hc : (isSub F.v F.v' = true ∧ ¬F.v = F.v') ∧
      F.n + costV (cs.map binVal) F.v F.v' ≤ binVal eb
  · simpa [hc, mstep, F', hb3] using htrue
  · simpa [hc, mstep, hb3] using hfalse

/-- **Sub-contract: mode `1`, check the NO move** (remaining). -/
theorem exists_mode1Stmt : ∃ (s : Stmt 38) (K : ℕ), ModeSpec 1 s K := by
  obtain ⟨sPop, KPop, hPop⟩ := exists_popFrameStmt
  obtain ⟨sPush, KPush, hPush⟩ := exists_pushFrameStmt
  obtain ⟨sCost, KCost, hCost⟩ := exists_costVStmt
  obtain ⟨sSub, KSub, hSub⟩ := exists_isSubStmt
  obtain ⟨KT, hTests⟩ := exec_mode1Tests sCost sSub KCost KSub hCost hSub
  obtain ⟨KC, hCommit⟩ := exec_mode1Commit sPush KPush hPush
  refine ⟨.seq sPop (.seq (mode1Tests sCost sSub) (mode1Commit sPush)),
    5 * KPop + KT + KC, ?_⟩
  intro base LX cs eb W F Ks out hbase hlen hcs heb hsum hF
  rcases hbase with ⟨hb1, hb2, hb3, hbrest⟩
  have ep := hPop base W LX.length 1 F Ks hbrest
  have et := hTests base LX cs eb W F Ks ⟨hb1, hb2, hb3, hbrest⟩ hlen hcs heb hsum hF
  have ec := hCommit base LX cs eb W F Ks out ⟨hb1, hb2, hb3, hbrest⟩ hF
  have hp := mul_frameSize_le_five_square KPop LX.length (binVal eb) W F hF
  have hp' := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2)
    (show 5 * KPop ≤ 5 * KPop + KT + KC by omega)
  have ht := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2)
    (show KT ≤ 5 * KPop + KT + KC by omega)
  have hc := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2)
    (show KC ≤ 5 * KPop + KT + KC by omega)
  exact .seq (ep.mono (by omega)) (.seq (et.mono (by omega)) (ec.mono (by omega)))

end DFS
end Kolmogorov.RandomStrings
