/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode1

/-!
# The depth-first search: mode 4

The mode-4 routine of the search (advance the YES answer counter: increment, carry and
no-carry branches), `DFS.exists_mode4Stmt`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- The first phase of mode `4` increments the answer register and records its carry on stack
`18`.  Apply `Stmt.exec_incr`; the remaining work is the space comparison between the popped
register representation and the encoded mode-`4` state, using the six field encodings. -/
private theorem exec_mode4_increment : ∃ K : ℕ, ∀ (base : Stacks 38) (W m E : ℕ)
    (F : Frame) (Ks : List Frame), (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    FrameOK m E F →
    Exec (Stmt.incr 16 17 18) (regSt base W m F Ks)
      (Function.update (Function.update (regSt base W m F Ks) 16 (incBits F.r)) 18
        [incCarry F.r])
      ((encSt base W m (4, F :: Ks)).space + K * (m + W + 1) ^ 2) := by
  obtain ⟨sPop, KPop, hPop⟩ := exists_popFrameStmt
  refine ⟨5 * KPop + 1, ?_⟩
  intro base W m E F Ks hbase hF
  let σ := regSt base W m F Ks
  have h17 : σ 17 = [] := by simp [σ, regSt, encSt, hbase 17 (by omega)]
  have h18 : σ 18 = [] := by simp [σ, regSt, encSt, hbase 18 (by omega)]
  have ei := Stmt.exec_incr (A := (16 : Fin 38)) (t := (17 : Fin 38))
    (C := (18 : Fin 38)) (by decide) (by decide) (by decide) h17 h18
  have ep := hPop base W m 4 F Ks hbase
  have hs := ep.space_le.2
  have hf := mul_frameSize_le_five_square KPop m E W F hF
  have hq : 1 ≤ (m + W + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
  have hbudget : σ.space + 1 ≤
      (encSt base W m (4, F :: Ks)).space + (5 * KPop + 1) * (m + W + 1) ^ 2 := by
    dsimp [σ] at hs ⊢
    rw [Nat.add_mul, one_mul]
    omega
  simpa [σ, regSt] using ei.mono hbudget

/-- Execute a list of stack clears without increasing space.  This is the induction used for the
scratch portion of `clearModeRegisters`. -/
private theorem exec_mode4_clearList {k : ℕ} (rs : List (Fin k)) (σ : Stacks k) :
    Exec (Stmt.seqs (rs.map Stmt.clear)) σ
      (rs.foldl (fun τ r => Function.update τ r []) σ) σ.space := by
  induction rs generalizing σ with
  | nil => simpa [Stmt.seqs] using (Exec.skip (σ := σ) (S := σ.space) le_rfl)
  | cons r rs ih =>
      have e₁ := Stmt.exec_clear r (σ r) σ rfl
      have e₂ := ih (Function.update σ r [])
      simpa [Stmt.seqs] using Exec.seq e₁ (e₂.mono e₁.space_le.2)

/-- `clearModeRegisters` empties registers `11`--`16` and scratch stacks `17`--`37` without
increasing space.  Execute its six leading clears explicitly and its scratch suffix by
`exec_mode4_clearList`. -/
private theorem exec_mode4_clearRegisters (σ : Stacks 38) :
    let rs : List (Fin 38) := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
    Exec clearModeRegisters σ (rs.foldl (fun τ r => Function.update τ r []) σ) σ.space := by
  dsimp only
  let σ₁₁ := Function.update σ 11 []
  let σ₁₂ := Function.update σ₁₁ 12 []
  let σ₁₃ := Function.update σ₁₂ 13 []
  let σ₁₄ := Function.update σ₁₃ 14 []
  let σ₁₅ := Function.update σ₁₄ 15 []
  let σ₁₆ := Function.update σ₁₅ 16 []
  have e₁₁ : Exec (Stmt.clear 11) σ σ₁₁ σ.space := by
    simpa [σ₁₁] using Stmt.exec_clear 11 (σ 11) σ rfl
  have e₁₂ : Exec (Stmt.clear 12) σ₁₁ σ₁₂ σ.space := by
    simpa [σ₁₂] using (Stmt.exec_clear 12 (σ₁₁ 12) σ₁₁ rfl).mono e₁₁.space_le.2
  have e₁₃ : Exec (Stmt.clear 13) σ₁₂ σ₁₃ σ.space := by
    simpa [σ₁₃] using (Stmt.exec_clear 13 (σ₁₂ 13) σ₁₂ rfl).mono e₁₂.space_le.2
  have e₁₄ : Exec (Stmt.clear 14) σ₁₃ σ₁₄ σ.space := by
    simpa [σ₁₄] using (Stmt.exec_clear 14 (σ₁₃ 14) σ₁₃ rfl).mono e₁₃.space_le.2
  have e₁₅ : Exec (Stmt.clear 15) σ₁₄ σ₁₅ σ.space := by
    simpa [σ₁₅] using (Stmt.exec_clear 15 (σ₁₄ 15) σ₁₄ rfl).mono e₁₄.space_le.2
  have e₁₆ : Exec (Stmt.clear 16) σ₁₅ σ₁₆ σ.space := by
    simpa [σ₁₆] using (Stmt.exec_clear 16 (σ₁₅ 16) σ₁₅ rfl).mono e₁₅.space_le.2
  let scratch : List (Fin 38) := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31, 32, 33, 34, 35, 36, 37]
  have es₀ := exec_mode4_clearList scratch σ₁₆
  have es : Exec clearModeScratch σ₁₆
      (scratch.foldl (fun τ r => Function.update τ r []) σ₁₆) σ.space := by
    simpa [scratch, clearModeScratch] using es₀.mono e₁₆.space_le.2
  unfold clearModeRegisters
  simpa [Stmt.seqs, scratch, σ₁₆, σ₁₅, σ₁₄, σ₁₃, σ₁₂, σ₁₁] using
    Exec.seq e₁₁ (Exec.seq e₁₂ (Exec.seq e₁₃ (Exec.seq e₁₄
      (Exec.seq e₁₅ (Exec.seq e₁₆ (Exec.seq es (.skip es.space_le.2)))))))

/-- The carry branch of mode `4`: discard the carry bit and all popped-frame registers, then
install mode `5`.  Prove it by repeated `Stmt.exec_clear`, followed by `Stmt.exec_pushList`, and
normalize the updates against `regSt`/`encSt`; `FrameOK` bounds the space overhead. -/
private theorem exec_mode4_carry : ∃ K : ℕ, ∀ (base : Stacks 38) (W m E : ℕ)
    (F : Frame) (Ks : List Frame),
    (∀ j : Fin 38, 5 ≤ j.val → base j = []) → FrameOK m E F → incCarry F.r = true →
    Exec (.seq (Stmt.clear 18) (.seq clearModeRegisters (putMode 5)))
      (Function.update (Function.update (regSt base W m F Ks) 16 (incBits F.r)) 18 [true])
      (encSt base W m (5, Ks))
      ((encSt base W m (4, F :: Ks)).space + K * (m + W + 1) ^ 2) := by
  obtain ⟨KI, hIncr⟩ := exec_mode4_increment
  refine ⟨KI + 5, ?_⟩
  intro base W m E F Ks hbase hF hc
  let τ := Function.update (Function.update (regSt base W m F Ks) 16 (incBits F.r)) 18 [true]
  let ρ := Function.update τ 18 []
  let rs : List (Fin 38) := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
  let ζ := rs.foldl (fun τ r => Function.update τ r []) ρ
  let S := (encSt base W m (4, F :: Ks)).space + (KI + 5) * (m + W + 1) ^ 2
  have hi := hIncr base W m E F Ks hbase hF
  have hτbase : Stacks.space τ ≤
      (encSt base W m (4, F :: Ks)).space + KI * (m + W + 1) ^ 2 := by
    have hout := hi.space_le.2
    simpa only [τ, hc] using hout
  have hτS : Stacks.space τ ≤ S :=
    hτbase.trans (by
      dsimp [S]
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (show KI ≤ KI + 5 by omega)) _)
  have eclear₀ := Stmt.exec_clear 18 [true] τ (by simp [τ])
  have eclear : Exec (Stmt.clear 18) τ ρ S := by
    simpa [ρ] using eclear₀.mono hτS
  have eregs₀ := exec_mode4_clearRegisters ρ
  have eregs : Exec clearModeRegisters ρ ζ S := by
    simpa [ζ, rs] using eregs₀.mono eclear.space_le.2
  have hζτ : Stacks.space ζ ≤ Stacks.space τ := by
    have h₁ : Stacks.space ζ ≤ Stacks.space ρ := by
      simpa [ζ, rs] using eregs₀.space_le.2
    have h₂ : Stacks.space ρ ≤ Stacks.space τ := by
      simpa [ρ] using eclear₀.space_le.2
    exact h₁.trans h₂
  have hζ : ζ = encSt base W m (0, Ks) := by
    funext j
    fin_cases j <;> simp [ζ, rs, ρ, τ, regSt, encSt, hbase]
  have emode₀ := Stmt.exec_pushList (k := 38) 9 (List.replicate 5 true) ζ
  have hmodeS : Stacks.space ζ + (List.replicate 5 true).length ≤ S := by
    have hζbase := hζτ.trans hτbase
    have hq : 1 ≤ (m + W + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    dsimp [S]
    rw [Nat.add_mul]
    omega
  have emode : Exec (putMode 5) ζ (encSt base W m (5, Ks)) S := by
    unfold putMode
    apply Stmt.exec_of_eq (emode₀.mono hmodeS)
    funext j
    fin_cases j <;> simp [hζ, encSt]
  simpa [τ, S] using Exec.seq eclear (Exec.seq eregs emode)

/-- The no-carry branch of mode `4`: discard the carry bit, push the frame whose answer field is
`incBits F.r`, and install mode `3`.  Rewrite the post-clear state as `regSt` for the updated
frame, apply `hPush`, then use `Stmt.exec_pushList`; the frame bounds control the common budget. -/
private theorem exec_mode4_noCarry (sPush : Stmt 38) (KP : ℕ)
    (hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPush (regSt base W m F Ks)
        (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        ((encSt base W m (0, F :: Ks)).space + KP * frameSize W F)) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (W m E : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) → FrameOK m E F →
      incCarry F.r = false →
      Exec (.seq (Stmt.clear 18) (.seq sPush (putMode 3)))
        (Function.update (Function.update (regSt base W m F Ks) 16 (incBits F.r)) 18 [false])
        (encSt base W m (3, { F with r := incBits F.r } :: Ks))
        ((encSt base W m (4, F :: Ks)).space + K * (m + W + 1) ^ 2) := by
  obtain ⟨KI, hIncr⟩ := exec_mode4_increment
  refine ⟨KI + 5 * KP + 3, ?_⟩
  intro base W m E F Ks hbase hF hc
  let F' : Frame := { F with r := incBits F.r }
  let τ := Function.update (Function.update (regSt base W m F Ks) 16 (incBits F.r)) 18
    [false]
  let τ₀ := Function.update τ 18 []
  let τ₁ := Function.update (encSt base W m (0, F' :: Ks)) 9 []
  let S := (encSt base W m (4, F :: Ks)).space +
    (KI + 5 * KP + 3) * (m + W + 1) ^ 2
  have hF' : FrameOK m E F' := by
    rcases hF with ⟨hv, hy, hn, hf, hv', hr⟩
    exact ⟨hv, hy, hn, hf, hv', by simpa [F', length_incBits] using hr⟩
  have hτ₀ : τ₀ = regSt base W m F' Ks := by
    funext j
    fin_cases j <;> first | rfl | exact (hbase _ (by decide)).symm
  have henc : (encSt base W m (0, F' :: Ks)).space ≤
      (encSt base W m (4, F :: Ks)).space := by
    unfold Stacks.space
    apply Finset.sum_le_sum
    intro j hj
    fin_cases j <;>
      simp [encSt, F', Frame.fields, Stacks.length_encList, length_incBits]
  have hi := hIncr base W m E F Ks hbase hF
  have hτS : Stacks.space τ ≤ S := by
    have hout := hi.space_le.2
    have hout' : Stacks.space τ ≤
        (encSt base W m (4, F :: Ks)).space + KI * (m + W + 1) ^ 2 := by
      simpa only [τ, hc] using hout
    exact hout'.trans (by
      dsimp [S]
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (show KI ≤ KI + 5 * KP + 3 by omega)) _)
  have eclear₀ := Stmt.exec_clear 18 [false] τ (by simp [τ])
  have eclear : Exec (Stmt.clear 18) τ (regSt base W m F' Ks) S :=
    Stmt.exec_of_eq (eclear₀.mono hτS) hτ₀
  have epush₀ := hPush base W m F' Ks hbase
  have hframe := mul_frameSize_le_five_square KP m E W F' hF'
  have hpushS : (encSt base W m (0, F' :: Ks)).space + KP * frameSize W F' ≤ S := by
    dsimp [S]
    have hmul := Nat.mul_le_mul_right ((m + W + 1) ^ 2)
      (show 5 * KP ≤ KI + 5 * KP + 3 by omega)
    omega
  have epush : Exec sPush (regSt base W m F' Ks) τ₁ S := by
    exact Exec.mono epush₀ hpushS
  have hτ₁eq : τ₁ = encSt base W m (0, F' :: Ks) := by
    funext j
    fin_cases j <;> rfl
  have emode₀ := Stmt.exec_pushList (k := 38) 9 (List.replicate 3 true) τ₁
  have hmodeS : Stacks.space τ₁ + (List.replicate 3 true).length ≤ S := by
    have hτ₁ : Stacks.space τ₁ ≤ (encSt base W m (0, F' :: Ks)).space := by
      rw [hτ₁eq]
    have hq : 1 ≤ (m + W + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    dsimp [S]
    rw [Nat.add_mul]
    omega
  have emode : Exec (putMode 3) τ₁ (encSt base W m (3, F' :: Ks)) S := by
    unfold putMode
    apply Stmt.exec_of_eq (emode₀.mono hmodeS)
    funext j
    fin_cases j <;> simp [hτ₁eq, encSt]
  simpa [τ, F', S] using Exec.seq eclear (Exec.seq epush emode)

/-- Increment `r` after a popped mode-`4` frame.  Use `Stmt.exec_incr` and split on its carry:
carry clears the frame and enters mode `5`, while no carry pushes the updated frame and enters
mode `3`; simplifying `mstep` identifies both final encodings. -/
theorem exec_mode4AfterPop (sPush : Stmt 38) (KP : ℕ)
    (hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPush (regSt base W m F Ks)
        (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        ((encSt base W m (0, F :: Ks)).space + KP * frameSize W F)) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
      (F : Frame) (Ks : List Frame) (out : BitString → Bool), BaseOK base LX cs eb →
      FrameOK LX.length (binVal eb) F →
      Exec (.seq (Stmt.incr 16 17 18) (Stmt.caseBit 18 fun carry =>
          .seq (Stmt.clear 18) (if carry then .seq clearModeRegisters (putMode 5)
            else .seq sPush (putMode 3))))
        (regSt base W LX.length F Ks)
        (encSt base W LX.length (mstep LX.length (costV (cs.map binVal)) (binVal eb) out
          (4, F :: Ks)))
        ((encSt base W LX.length (4, F :: Ks)).space + K * (LX.length + W + 1) ^ 2) := by
  obtain ⟨KI, hIncr⟩ := exec_mode4_increment
  obtain ⟨KT, hCarry⟩ := exec_mode4_carry
  obtain ⟨KF, hNoCarry⟩ := exec_mode4_noCarry sPush KP hPush
  refine ⟨KI + KT + KF, ?_⟩
  intro base LX cs eb W F Ks out hbase hF
  rcases hbase with ⟨hb1, hb2, hb3, hbrest⟩
  let τ := Function.update (Function.update (regSt base W LX.length F Ks) 16
    (incBits F.r)) 18 [incCarry F.r]
  let S := (encSt base W LX.length (4, F :: Ks)).space +
    (KI + KT + KF) * (LX.length + W + 1) ^ 2
  have hSI : (encSt base W LX.length (4, F :: Ks)).space +
      KI * (LX.length + W + 1) ^ 2 ≤ S := by
    dsimp [S]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hST : (encSt base W LX.length (4, F :: Ks)).space +
      KT * (LX.length + W + 1) ^ 2 ≤ S := by
    dsimp [S]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hSF : (encSt base W LX.length (4, F :: Ks)).space +
      KF * (LX.length + W + 1) ^ 2 ≤ S := by
    dsimp [S]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have ei := hIncr base W LX.length (binVal eb) F Ks hbrest hF
  have h18 : τ 18 = [incCarry F.r] := by simp [τ]
  cases hc : incCarry F.r with
  | false =>
      have eb := hNoCarry base W LX.length (binVal eb) F Ks hbrest hF hc
      have ec : Exec (Stmt.caseBit 18 fun carry =>
          .seq (Stmt.clear 18) (if carry then .seq clearModeRegisters (putMode 5)
            else .seq sPush (putMode 3))) τ
          (encSt base W LX.length (3, { F with r := incBits F.r } :: Ks)) S := by
        rw [Stmt.exec_caseBit h18]
        simpa [hc, S, τ] using eb.mono hSF
      exact .seq (by simpa [τ, S] using ei.mono hSI)
        (by simpa [mstep, hc, S, τ] using ec)
  | true =>
      have eb := hCarry base W LX.length (binVal eb) F Ks hbrest hF hc
      have ec : Exec (Stmt.caseBit 18 fun carry =>
          .seq (Stmt.clear 18) (if carry then .seq clearModeRegisters (putMode 5)
            else .seq sPush (putMode 3))) τ (encSt base W LX.length (5, Ks)) S := by
        rw [Stmt.exec_caseBit h18]
        simpa [hc, S, τ] using eb.mono hST
      exact .seq (by simpa [τ, S] using ei.mono hSI)
        (by simpa [mstep, hc, S, τ] using ec)

/-- **Sub-contract: mode `4`, next YES answer** (remaining). -/
theorem exists_mode4Stmt : ∃ (s : Stmt 38) (K : ℕ), ModeSpec 4 s K := by
  obtain ⟨sPop, KPop, hPop⟩ := exists_popFrameStmt
  obtain ⟨sPush, KPush, hPush⟩ := exists_pushFrameStmt
  obtain ⟨KC, hCore⟩ := exec_mode4AfterPop sPush KPush hPush
  let core : Stmt 38 := .seq (Stmt.incr 16 17 18) (Stmt.caseBit 18 fun carry =>
    .seq (Stmt.clear 18) (if carry then .seq clearModeRegisters (putMode 5)
      else .seq sPush (putMode 3)))
  refine ⟨.seq sPop core, 5 * KPop + KC, ?_⟩
  intro base LX cs eb W F Ks out hbase hlen hcs heb hsum hF
  rcases hbase with ⟨hb1, hb2, hb3, hbrest⟩
  have ep := hPop base W LX.length 4 F Ks hbrest
  have ec := hCore base LX cs eb W F Ks out ⟨hb1, hb2, hb3, hbrest⟩ hF
  have hp := mul_frameSize_le_five_square KPop LX.length (binVal eb) W F hF
  have hp' := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2)
    (show 5 * KPop ≤ 5 * KPop + KC by omega)
  have hc := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2)
    (show KC ≤ 5 * KPop + KC by omega)
  exact .seq (ep.mono (by omega)) (by simpa [core] using ec.mono (by omega))

end DFS
end Kolmogorov.RandomStrings
