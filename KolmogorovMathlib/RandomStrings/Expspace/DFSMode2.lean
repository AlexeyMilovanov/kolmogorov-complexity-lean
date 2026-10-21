/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode1

/-!
# The depth-first search: mode 2

The mode-2 routine of the search (advance the NO move counter: increment, carry and no-carry
branches), `DFS.exists_mode2Stmt`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- The first phase of mode `2` increments the NO-move register and records its carry on stack
`18`.  The popped-frame contract supplies the comparison between the register and encoded
representations needed for the common quadratic space bound. -/
private theorem exec_mode2_increment : ∃ K : ℕ, ∀ (base : Stacks 38) (W m E : ℕ)
    (F : Frame) (Ks : List Frame), (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    FrameOK m E F →
    Exec (Stmt.incr 15 17 18) (regSt base W m F Ks)
      (Function.update (Function.update (regSt base W m F Ks) 15 (incBits F.v')) 18
        [incCarry F.v'])
      ((encSt base W m (2, F :: Ks)).space + K * (m + W + 1) ^ 2) := by
  obtain ⟨sPop, KPop, hPop⟩ := exists_popFrameStmt
  refine ⟨5 * KPop + 1, ?_⟩
  intro base W m E F Ks hbase hF
  let σ := regSt base W m F Ks
  have h17 : σ 17 = [] := by simp [σ, regSt, encSt, hbase 17 (by omega)]
  have h18 : σ 18 = [] := by simp [σ, regSt, encSt, hbase 18 (by omega)]
  have ei := Stmt.exec_incr (A := (15 : Fin 38)) (t := (17 : Fin 38))
    (C := (18 : Fin 38)) (by decide) (by decide) (by decide) h17 h18
  have ep := hPop base W m 2 F Ks hbase
  have hs := ep.space_le.2
  have hf := mul_frameSize_le_five_square KPop m E W F hF
  have hq : 1 ≤ (m + W + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
  have hbudget : σ.space + 1 ≤
      (encSt base W m (2, F :: Ks)).space + (5 * KPop + 1) * (m + W + 1) ^ 2 := by
    dsimp [σ] at hs ⊢
    rw [Nat.add_mul, one_mul]
    omega
  simpa [σ, regSt] using ei.mono hbudget

/-- Execute the register/scratch clear list used by the carry branch of mode `2`. -/
private theorem exec_mode2_clearList {k : ℕ} (rs : List (Fin k)) (σ : Stacks k) :
    Exec (Stmt.seqs (rs.map Stmt.clear)) σ
      (rs.foldl (fun τ r => Function.update τ r []) σ) σ.space := by
  induction rs generalizing σ with
  | nil => simpa [Stmt.seqs] using (Exec.skip (σ := σ) (S := σ.space) le_rfl)
  | cons r rs ih =>
      have e₁ := Stmt.exec_clear r (σ r) σ rfl
      have e₂ := ih (Function.update σ r [])
      simpa [Stmt.seqs] using Exec.seq e₁ (e₂.mono e₁.space_le.2)

/-- Clear registers `11`--`16` and scratch stacks `17`--`37` without increasing space. -/
private theorem exec_mode2_clearRegisters (σ : Stacks 38) :
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
  have es₀ := exec_mode2_clearList scratch σ₁₆
  have es : Exec clearModeScratch σ₁₆
      (scratch.foldl (fun τ r => Function.update τ r []) σ₁₆) σ.space := by
    simpa [scratch, clearModeScratch] using es₀.mono e₁₆.space_le.2
  unfold clearModeRegisters
  simpa [Stmt.seqs, scratch, σ₁₆, σ₁₅, σ₁₄, σ₁₃, σ₁₂, σ₁₁] using
    Exec.seq e₁₁ (Exec.seq e₁₂ (Exec.seq e₁₃ (Exec.seq e₁₄
      (Exec.seq e₁₅ (Exec.seq e₁₆ (Exec.seq es (.skip es.space_le.2)))))))

/-- The carry branch of mode `2` discards the popped frame and enters mode `6`. -/
private theorem exec_mode2_carry : ∃ K : ℕ, ∀ (base : Stacks 38) (W m E : ℕ)
    (F : Frame) (Ks : List Frame),
    (∀ j : Fin 38, 5 ≤ j.val → base j = []) → FrameOK m E F → incCarry F.v' = true →
    Exec (.seq (Stmt.clear 18) (.seq clearModeRegisters (putMode 6)))
      (Function.update (Function.update (regSt base W m F Ks) 15 (incBits F.v')) 18 [true])
      (encSt base W m (6, Ks))
      ((encSt base W m (2, F :: Ks)).space + K * (m + W + 1) ^ 2) := by
  obtain ⟨KI, hIncr⟩ := exec_mode2_increment
  refine ⟨KI + 6, ?_⟩
  intro base W m E F Ks hbase hF hc
  let τ := Function.update (Function.update (regSt base W m F Ks) 15 (incBits F.v')) 18 [true]
  let ρ := Function.update τ 18 []
  let rs : List (Fin 38) := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
  let ζ := rs.foldl (fun τ r => Function.update τ r []) ρ
  let S := (encSt base W m (2, F :: Ks)).space + (KI + 6) * (m + W + 1) ^ 2
  have hi := hIncr base W m E F Ks hbase hF
  have hτbase : Stacks.space τ ≤
      (encSt base W m (2, F :: Ks)).space + KI * (m + W + 1) ^ 2 := by
    have hout := hi.space_le.2
    simpa only [τ, hc] using hout
  have hτS : Stacks.space τ ≤ S :=
    hτbase.trans (by
      dsimp [S]
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (show KI ≤ KI + 6 by omega)) _)
  have eclear₀ := Stmt.exec_clear 18 [true] τ (by simp [τ])
  have eclear : Exec (Stmt.clear 18) τ ρ S := by
    simpa [ρ] using eclear₀.mono hτS
  have eregs₀ := exec_mode2_clearRegisters ρ
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
  have emode₀ := Stmt.exec_pushList (k := 38) 9 (List.replicate 6 true) ζ
  have hmodeS : Stacks.space ζ + (List.replicate 6 true).length ≤ S := by
    have hζbase := hζτ.trans hτbase
    have hq : 1 ≤ (m + W + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    dsimp [S]
    rw [Nat.add_mul]
    omega
  have emode : Exec (putMode 6) ζ (encSt base W m (6, Ks)) S := by
    unfold putMode
    apply Stmt.exec_of_eq (emode₀.mono hmodeS)
    funext j
    fin_cases j <;> simp [hζ, encSt]
  simpa [τ, S] using Exec.seq eclear (Exec.seq eregs emode)

/-- The no-carry branch of mode `2` pushes the frame with incremented `v'` and enters mode `1`. -/
private theorem exec_mode2_noCarry (sPush : Stmt 38) (KP : ℕ)
    (hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPush (regSt base W m F Ks)
        (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        ((encSt base W m (0, F :: Ks)).space + KP * frameSize W F)) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (W m E : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) → FrameOK m E F →
      incCarry F.v' = false →
      Exec (.seq (Stmt.clear 18) (.seq sPush (putMode 1)))
        (Function.update (Function.update (regSt base W m F Ks) 15 (incBits F.v')) 18 [false])
        (encSt base W m (1, { F with v' := incBits F.v' } :: Ks))
        ((encSt base W m (2, F :: Ks)).space + K * (m + W + 1) ^ 2) := by
  obtain ⟨KI, hIncr⟩ := exec_mode2_increment
  refine ⟨KI + 5 * KP + 1, ?_⟩
  intro base W m E F Ks hbase hF hc
  let F' : Frame := { F with v' := incBits F.v' }
  let τ := Function.update (Function.update (regSt base W m F Ks) 15 (incBits F.v')) 18
    [false]
  let τ₀ := Function.update τ 18 []
  let τ₁ := Function.update (encSt base W m (0, F' :: Ks)) 9 []
  let S := (encSt base W m (2, F :: Ks)).space +
    (KI + 5 * KP + 1) * (m + W + 1) ^ 2
  have hF' : FrameOK m E F' := by
    rcases hF with ⟨hv, hy, hn, hf, hv', hr⟩
    exact ⟨hv, hy, hn, hf, by simpa [F', length_incBits] using hv', hr⟩
  have hτ₀ : τ₀ = regSt base W m F' Ks := by
    funext j
    fin_cases j <;> first | rfl | exact (hbase _ (by decide)).symm
  have henc : (encSt base W m (0, F' :: Ks)).space ≤
      (encSt base W m (2, F :: Ks)).space := by
    unfold Stacks.space
    apply Finset.sum_le_sum
    intro j hj
    fin_cases j <;>
      simp [encSt, F', Frame.fields, Stacks.length_encList, length_incBits]
  have hi := hIncr base W m E F Ks hbase hF
  have hτS : Stacks.space τ ≤ S := by
    have hout := hi.space_le.2
    have hout' : Stacks.space τ ≤
        (encSt base W m (2, F :: Ks)).space + KI * (m + W + 1) ^ 2 := by
      simpa only [τ, hc] using hout
    exact hout'.trans (by
      dsimp [S]
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (show KI ≤ KI + 5 * KP + 1 by omega)) _)
  have eclear₀ := Stmt.exec_clear 18 [false] τ (by simp [τ])
  have eclear : Exec (Stmt.clear 18) τ (regSt base W m F' Ks) S :=
    Stmt.exec_of_eq (eclear₀.mono hτS) hτ₀
  have epush₀ := hPush base W m F' Ks hbase
  have hframe := mul_frameSize_le_five_square KP m E W F' hF'
  have hpushS : (encSt base W m (0, F' :: Ks)).space + KP * frameSize W F' ≤ S := by
    dsimp [S]
    have hmul := Nat.mul_le_mul_right ((m + W + 1) ^ 2)
      (show 5 * KP ≤ KI + 5 * KP + 1 by omega)
    omega
  have epush : Exec sPush (regSt base W m F' Ks) τ₁ S := by
    exact Exec.mono epush₀ hpushS
  have hτ₁eq : τ₁ = encSt base W m (0, F' :: Ks) := by
    funext j
    fin_cases j <;> rfl
  have emode₀ := Stmt.exec_pushList (k := 38) 9 (List.replicate 1 true) τ₁
  have hmodeS : Stacks.space τ₁ + (List.replicate 1 true).length ≤ S := by
    have hτ₁ : Stacks.space τ₁ ≤ (encSt base W m (0, F' :: Ks)).space := by
      rw [hτ₁eq]
    have hq : 1 ≤ (m + W + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    dsimp [S]
    rw [Nat.add_mul]
    omega
  have emode : Exec (putMode 1) τ₁ (encSt base W m (1, F' :: Ks)) S := by
    unfold putMode
    apply Stmt.exec_of_eq (emode₀.mono hmodeS)
    funext j
    fin_cases j <;> simp [hτ₁eq, encSt]
  simpa [τ, F', S] using Exec.seq eclear (Exec.seq epush emode)

/-- Increment `v'` after a popped mode-`2` frame.  Prove this with `Stmt.exec_incr`, split on
the carry bit, then either clear the registers and put mode `6`, or use the supplied push-frame
contract and put mode `1`; the two branches are exactly the two clauses of `mstep`. -/
theorem exec_mode2AfterPop (sPush : Stmt 38) (KP : ℕ)
    (hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPush (regSt base W m F Ks)
        (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        ((encSt base W m (0, F :: Ks)).space + KP * frameSize W F)) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
      (F : Frame) (Ks : List Frame) (out : BitString → Bool), BaseOK base LX cs eb →
      FrameOK LX.length (binVal eb) F →
      Exec (.seq (Stmt.incr 15 17 18) (Stmt.caseBit 18 fun carry =>
          .seq (Stmt.clear 18) (if carry then .seq clearModeRegisters (putMode 6)
            else .seq sPush (putMode 1))))
        (regSt base W LX.length F Ks)
        (encSt base W LX.length (mstep LX.length (costV (cs.map binVal)) (binVal eb) out
          (2, F :: Ks)))
        ((encSt base W LX.length (2, F :: Ks)).space + K * (LX.length + W + 1) ^ 2) := by
  obtain ⟨KI, hIncr⟩ := exec_mode2_increment
  obtain ⟨KT, hCarry⟩ := exec_mode2_carry
  obtain ⟨KF, hNoCarry⟩ := exec_mode2_noCarry sPush KP hPush
  refine ⟨KI + KT + KF, ?_⟩
  intro base LX cs eb W F Ks out hbase hF
  rcases hbase with ⟨hb1, hb2, hb3, hbrest⟩
  let τ := Function.update (Function.update (regSt base W LX.length F Ks) 15
    (incBits F.v')) 18 [incCarry F.v']
  let S := (encSt base W LX.length (2, F :: Ks)).space +
    (KI + KT + KF) * (LX.length + W + 1) ^ 2
  have hSI : (encSt base W LX.length (2, F :: Ks)).space +
      KI * (LX.length + W + 1) ^ 2 ≤ S := by
    dsimp [S]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hST : (encSt base W LX.length (2, F :: Ks)).space +
      KT * (LX.length + W + 1) ^ 2 ≤ S := by
    dsimp [S]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hSF : (encSt base W LX.length (2, F :: Ks)).space +
      KF * (LX.length + W + 1) ^ 2 ≤ S := by
    dsimp [S]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have ei := hIncr base W LX.length (binVal eb) F Ks hbrest hF
  have h18 : τ 18 = [incCarry F.v'] := by simp [τ]
  cases hc : incCarry F.v' with
  | false =>
      have eb := hNoCarry base W LX.length (binVal eb) F Ks hbrest hF hc
      have ec : Exec (Stmt.caseBit 18 fun carry =>
          .seq (Stmt.clear 18) (if carry then .seq clearModeRegisters (putMode 6)
            else .seq sPush (putMode 1))) τ
          (encSt base W LX.length (1, { F with v' := incBits F.v' } :: Ks)) S := by
        rw [Stmt.exec_caseBit h18]
        simpa [hc, S, τ] using eb.mono hSF
      exact .seq (by simpa [τ, S] using ei.mono hSI)
        (by simpa [mstep, hc, S, τ] using ec)
  | true =>
      have eb := hCarry base W LX.length (binVal eb) F Ks hbrest hF hc
      have ec : Exec (Stmt.caseBit 18 fun carry =>
          .seq (Stmt.clear 18) (if carry then .seq clearModeRegisters (putMode 6)
            else .seq sPush (putMode 1))) τ (encSt base W LX.length (6, Ks)) S := by
        rw [Stmt.exec_caseBit h18]
        simpa [hc, S, τ] using eb.mono hST
      exact .seq (by simpa [τ, S] using ei.mono hSI)
        (by simpa [mstep, hc, S, τ] using ec)

/-- **Sub-contract: mode `2`, next NO move** (remaining). -/
theorem exists_mode2Stmt : ∃ (s : Stmt 38) (K : ℕ), ModeSpec 2 s K := by
  obtain ⟨sPop, KPop, hPop⟩ := exists_popFrameStmt
  obtain ⟨sPush, KPush, hPush⟩ := exists_pushFrameStmt
  obtain ⟨KC, hCore⟩ := exec_mode2AfterPop sPush KPush hPush
  let core : Stmt 38 := .seq (Stmt.incr 15 17 18) (Stmt.caseBit 18 fun carry =>
    .seq (Stmt.clear 18) (if carry then .seq clearModeRegisters (putMode 6)
      else .seq sPush (putMode 1)))
  refine ⟨.seq sPop core, 5 * KPop + KC, ?_⟩
  intro base LX cs eb W F Ks out hbase hlen hcs heb hsum hF
  rcases hbase with ⟨hb1, hb2, hb3, hbrest⟩
  have ep := hPop base W LX.length 2 F Ks hbrest
  have ec := hCore base LX cs eb W F Ks out ⟨hb1, hb2, hb3, hbrest⟩ hF
  have hp := mul_frameSize_le_five_square KPop LX.length (binVal eb) W F hF
  have hp' := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2)
    (show 5 * KPop ≤ 5 * KPop + KC by omega)
  have hc := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2)
    (show KC ≤ 5 * KPop + KC by omega)
  exact .seq (ep.mono (by omega)) (by simpa [core] using ec.mono (by omega))

end DFS
end Kolmogorov.RandomStrings
