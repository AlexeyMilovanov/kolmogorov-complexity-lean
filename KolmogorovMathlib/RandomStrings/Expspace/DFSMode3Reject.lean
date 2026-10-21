/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode3Tests

/-!
# The depth-first search: the rejecting leaves of mode 3

The two commit leaves of mode 3 that reject the current YES answer: the answer is not a superset
of the NO move (`DFS.exec_mode3Commit_notSub`) or it exceeds the budget
(`DFS.exec_mode3Commit_overBudget`).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-! The commit phase naturally splits into the three leaves of its two tests.  Keeping these
leaves separate prevents the successful branch's long register calculation from being elaborated
in the same context as the two restore-parent branches. -/

/-- If the proposed answer is not a superset of the NO move, the commit phase clears its test
scratch, restores the unchanged parent with `hPush`, and changes the mode to `4`.  To prove this,
rewrite both `caseBit`s with `Stmt.exec_caseBit`, execute `clearModeScratch`, apply `hPush`, and
execute `putMode 4`; the `FrameOK` bounds dominate the intermediate stack spaces. -/
theorem exec_mode3Commit_notSub (sPush sCost : Stmt 38) (KP : ℕ)
    (hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPush (regSt base W m F Ks)
        (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        ((encSt base W m (0, F :: Ks)).space + KP * frameSize W F)) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
      (F : Frame) (Ks : List Frame), BaseOK base LX cs eb →
      FrameOK LX.length (binVal eb) F → isSub F.v' F.r = false →
      Exec (mode3Commit sPush sCost) (mode3TestSt base W LX.length F Ks cs)
        (encSt base W LX.length (4, F :: Ks))
        ((encSt base W LX.length (3, F :: Ks)).space +
          K * (LX.length + W + 1) ^ 2) := by
  let scratch : List (Fin 38) := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31, 32, 33, 34, 35, 36, 37]
  have clearList : ∀ (σ : Stacks 38),
      Exec (Stmt.seqs (scratch.map Stmt.clear)) σ
        (scratch.foldl (fun τ r => Function.update τ r []) σ) σ.space := by
    intro σ
    induction scratch generalizing σ with
    | nil => simpa [Stmt.seqs] using (Exec.skip (σ := σ) (S := σ.space) le_rfl)
    | cons r rs ih =>
        have e₁ := Stmt.exec_clear r (σ r) σ rfl
        have e₂ := ih (Function.update σ r [])
        simpa [Stmt.seqs] using Exec.seq e₁ (e₂.mono e₁.space_le.2)
  refine ⟨5 * KP + 50, ?_⟩
  intro base LX cs eb W F Ks hbase hF hsub
  rcases hbase with ⟨hb1, hb2, hb3, hbrest⟩
  let m := LX.length
  let Q := (m + W + 1) ^ 2
  let E := (encSt base W m (3, F :: Ks)).space
  let S := E + (5 * KP + 50) * Q
  let σ := mode3TestSt base W m F Ks cs
  let ζ := scratch.foldl (fun τ r => Function.update τ r []) σ
  let υ := Function.update (encSt base W m (0, F :: Ks)) 9 []
  have hQ : 1 ≤ Q := by
    exact Nat.one_le_pow 2 _ (by omega)
  have henc : (encSt base W m (0, F :: Ks)).space ≤ E := by
    let ξ := encSt base W m (0, F :: Ks)
    have hu := Stacks.space_update ξ (9 : Fin 38) (List.replicate 3 true)
    have he : Function.update ξ 9 (List.replicate 3 true) =
        encSt base W m (3, F :: Ks) := by
      funext j
      fin_cases j <;> simp [ξ, encSt]
    rw [he] at hu
    have h9 : ξ 9 = [] := by simp [ξ, encSt]
    rw [h9] at hu
    simp only [List.length_replicate, List.length_nil] at hu
    dsimp [ξ] at hu
    dsimp [E]
    omega
  have hframe := mul_frameSize_le_five_square 8 m (binVal eb) W F hF
  have hreg₀ := pushFrameEncode_space base W m F Ks
  have hreg : (regSt base W m F Ks).space ≤ E + 40 * Q := by
    dsimp [Q] at hframe
    omega
  have hup : ∀ (ρ : Stacks 38) (r : Fin 38) (v : BitString),
      Stacks.space (Function.update ρ r v) ≤ ρ.space + v.length := by
    intro ρ r v
    have hu := Stacks.space_update ρ r v
    omega
  have hσreg : σ.space ≤ (regSt base W m F Ks).space +
      F.v'.length + F.r.length + 1 + W + 1 := by
    dsimp [σ, mode3TestSt]
    have h1 := hup (regSt base W m F Ks) 17 F.v'
    have h2 := hup (Function.update (regSt base W m F Ks) 17 F.v') 18 F.r
    have h3 := hup (Function.update (Function.update (regSt base W m F Ks) 17 F.v') 18 F.r)
      23 [isSub F.v' F.r]
    have h4 := hup (Function.update (Function.update (Function.update
      (regSt base W m F Ks) 17 F.v') 18 F.r) 23 [isSub F.v' F.r]) 29
      (numBits W (F.y + costV (cs.map binVal) F.v' F.r))
    have h5 := hup (Function.update (Function.update (Function.update (Function.update
      (regSt base W m F Ks) 17 F.v') 18 F.r) 23 [isSub F.v' F.r]) 29
      (numBits W (F.y + costV (cs.map binVal) F.v' F.r))) 28
      [decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal (base 3))]
    simp only [List.length_cons, List.length_nil, numBits, List.length_map,
      List.length_range] at h3 h4 h5 ⊢
    omega
  have hσS : σ.space ≤ S := by
    have hv : F.v'.length ≤ m := by simpa [m] using hF.2.2.2.2.1
    have hr : F.r.length ≤ m := by simpa [m] using hF.2.2.2.2.2
    have hmQ : m ≤ Q := by
      calc
        m ≤ m + W + 1 := by omega
        _ ≤ Q := by dsimp [Q]; exact Nat.le_pow (by omega)
    have hWQ : W ≤ Q := by
      calc
        W ≤ m + W + 1 := by omega
        _ ≤ Q := by dsimp [Q]; exact Nat.le_pow (by omega)
    have hsmall : 2 * m + W + 2 ≤ 10 * Q := by
      omega
    have hσ50 : σ.space ≤ E + 50 * Q := by omega
    have hcoef : 50 * Q ≤ (5 * KP + 50) * Q :=
      Nat.mul_le_mul_right Q (by omega)
    dsimp [S]
    omega
  have hregScratch : ∀ j : Fin 38, 17 ≤ j.val → regSt base W m F Ks j = [] := by
    intro j hj
    fin_cases j <;> norm_num at hj <;> simp [regSt, encSt, hbrest]
  have hζ : ζ = regSt base W m F Ks := by
    funext j
    fin_cases j <;>
      simp [ζ, scratch, σ, mode3TestSt, hregScratch]
  have es₀ := clearList σ
  have es : Exec clearModeScratch σ ζ S := by
    have es' : Exec clearModeScratch σ
        (scratch.foldl (fun τ r => Function.update τ r []) σ) S := by
      simpa [clearModeScratch, scratch] using es₀.mono hσS
    simpa only [ζ] using es'
  have ep₀ := hPush base W m F Ks hbrest
  have hpframe := mul_frameSize_le_five_square KP m (binVal eb) W F hF
  have hpS : (encSt base W m (0, F :: Ks)).space + KP * frameSize W F ≤ S := by
    have hcoef : (5 * KP) * Q ≤ (5 * KP + 50) * Q :=
      Nat.mul_le_mul_right Q (by omega)
    have hpframe' : KP * frameSize W F ≤ (5 * KP) * Q := by
      simpa [Q] using hpframe
    dsimp [S]
    omega
  have ep : Exec sPush ζ υ S := by
    simpa [hζ, υ] using ep₀.mono hpS
  have em₀ := Stmt.exec_pushList (k := 38) 9 (List.replicate 4 true) υ
  have hemS : Stacks.space υ + (List.replicate 4 true).length ≤ S := by
    have hυ : Stacks.space υ ≤ (encSt base W m (0, F :: Ks)).space := by
      apply Stacks.space_update_le
      simp
    have hcoef : 50 * Q ≤ (5 * KP + 50) * Q :=
      Nat.mul_le_mul_right Q (by omega)
    have hfour : 4 ≤ 50 * Q := by omega
    simp only [List.length_replicate]
    dsimp [S]
    omega
  have em : Exec (putMode 4) υ (encSt base W m (4, F :: Ks)) S := by
    unfold putMode
    apply Stmt.exec_of_eq (em₀.mono hemS)
    funext j
    fin_cases j <;> simp [υ, encSt]
  have ebody : Exec (Stmt.seqs [clearModeScratch, sPush, putMode 4]) σ
      (encSt base W m (4, F :: Ks)) S := by
    simpa [Stmt.seqs, υ] using
      Exec.seq es (Exec.seq ep (Exec.seq em (.skip em.space_le.2)))
  have h23 : σ 23 = false :: [] := by simp [σ, mode3TestSt, hsub]
  have h28 : σ 28 =
      decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal (base 3)) :: [] := by
    simp [σ, mode3TestSt]
  rw [mode3Commit, Stmt.exec_caseBit h23, Stmt.exec_caseBit h28]
  simpa [m, E, Q, S] using ebody


/-- Setting stack 9 of the mode-0 encoding to three trues gives the mode-3 encoding. -/
private lemma m3ob_he (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) :
  Function.update (encSt base W m (0, F :: Ks)) 9 (List.replicate 3 true) =
    encSt base W m (3, F :: Ks) := by
  funext j
  fin_cases j <;> simp [encSt]

/-- Test scratch registers 17 through 37 are clear in the base state. -/
private lemma m3ob_hregScratch (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame)
    (hbrest : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    ∀ j : Fin 38, 17 ≤ j.val → regSt base W m F Ks j = [] := by
  intro j hj
  fin_cases j <;> norm_num at hj <;> simp [regSt, encSt, hbrest]

/-- Clearing the test scratch list from mode3TestSt yields regSt. -/
private lemma m3ob_hζ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (cs : List BitString)
    (hregScratch : ∀ j : Fin 38, 17 ≤ j.val → regSt base W m F Ks j = []) :
    let scratch : List (Fin 38) := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30, 31, 32, 33, 34, 35, 36, 37]
    let σ := mode3TestSt base W m F Ks cs
    scratch.foldl (fun τ r => Function.update τ r []) σ = regSt base W m F Ks := by
  intro scratch σ
  funext j
  fin_cases j <;> simp [scratch, σ, mode3TestSt, hregScratch]

/-- Pushing 4 true values to stack 9 updates mode 0 to mode 4. -/
private lemma m3ob_em (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) :
    let υ := Function.update (encSt base W m (0, F :: Ks)) 9 []
    Function.update υ 9 (List.replicate 4 true) = encSt base W m (4, F :: Ks) := by
  intro υ
  funext j
  fin_cases j <;> simp [υ, encSt]

/-- If inclusion succeeds but the accumulated YES cost exceeds the budget, the commit phase takes
the same restore-parent leaf and enters mode `4`.  Prove it by selecting the `true`/`false`
`caseBit` leaves, clearing the test scratch, applying `hPush`, and normalizing `putMode 4`; use the
global width and `FrameOK` hypotheses for the common quadratic space bound. -/
theorem exec_mode3Commit_overBudget (sPush sCost : Stmt 38) (KP : ℕ)
    (hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPush (regSt base W m F Ks)
        (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        ((encSt base W m (0, F :: Ks)).space + KP * frameSize W F)) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
      (F : Frame) (Ks : List Frame), BaseOK base LX cs eb →
      FrameOK LX.length (binVal eb) F → isSub F.v' F.r = true →
      decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal eb) = false →
      Exec (mode3Commit sPush sCost) (mode3TestSt base W LX.length F Ks cs)
        (encSt base W LX.length (4, F :: Ks))
        ((encSt base W LX.length (3, F :: Ks)).space +
          K * (LX.length + W + 1) ^ 2) := by
  let scratch : List (Fin 38) := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31, 32, 33, 34, 35, 36, 37]
  have clearList : ∀ (σ : Stacks 38),
      Exec (Stmt.seqs (scratch.map Stmt.clear)) σ
        (scratch.foldl (fun τ r => Function.update τ r []) σ) σ.space := by
    intro σ
    induction scratch generalizing σ with
    | nil => simpa [Stmt.seqs] using (Exec.skip (σ := σ) (S := σ.space) le_rfl)
    | cons r rs ih =>
        have e₁ := Stmt.exec_clear r (σ r) σ rfl
        have e₂ := ih (Function.update σ r [])
        simpa [Stmt.seqs] using Exec.seq e₁ (e₂.mono e₁.space_le.2)
  refine ⟨5 * KP + 50, ?_⟩
  intro base LX cs eb W F Ks hbase hF hsub hle
  rcases hbase with ⟨hb1, hb2, hb3, hbrest⟩
  let m := LX.length
  let Q := (m + W + 1) ^ 2
  let E := (encSt base W m (3, F :: Ks)).space
  let S := E + (5 * KP + 50) * Q
  let σ := mode3TestSt base W m F Ks cs
  let ζ := scratch.foldl (fun τ r => Function.update τ r []) σ
  let υ := Function.update (encSt base W m (0, F :: Ks)) 9 []
  have hQ : 1 ≤ Q := by
    exact Nat.one_le_pow 2 _ (by omega)
  have henc : (encSt base W m (0, F :: Ks)).space ≤ E := by
    let ξ := encSt base W m (0, F :: Ks)
    have hu := Stacks.space_update ξ (9 : Fin 38) (List.replicate 3 true)
    have he : Function.update ξ 9 (List.replicate 3 true) =
        encSt base W m (3, F :: Ks) :=
      m3ob_he base W m F Ks
    rw [he] at hu
    have h9 : ξ 9 = [] := by simp [ξ, encSt]
    rw [h9] at hu
    simp only [List.length_replicate, List.length_nil] at hu
    dsimp [ξ] at hu
    dsimp [E]
    omega
  have hframe := mul_frameSize_le_five_square 8 m (binVal eb) W F hF
  have hreg₀ := pushFrameEncode_space base W m F Ks
  have hreg : (regSt base W m F Ks).space ≤ E + 40 * Q := by
    dsimp [Q] at hframe
    omega
  have hup : ∀ (ρ : Stacks 38) (r : Fin 38) (v : BitString),
      Stacks.space (Function.update ρ r v) ≤ ρ.space + v.length := by
    intro ρ r v
    have hu := Stacks.space_update ρ r v
    omega
  have hσreg : σ.space ≤ (regSt base W m F Ks).space +
      F.v'.length + F.r.length + 1 + W + 1 := by
    dsimp [σ, mode3TestSt]
    have h1 := hup (regSt base W m F Ks) 17 F.v'
    have h2 := hup (Function.update (regSt base W m F Ks) 17 F.v') 18 F.r
    have h3 := hup (Function.update (Function.update (regSt base W m F Ks) 17 F.v') 18 F.r)
      23 [isSub F.v' F.r]
    have h4 := hup (Function.update (Function.update (Function.update
      (regSt base W m F Ks) 17 F.v') 18 F.r) 23 [isSub F.v' F.r]) 29
      (numBits W (F.y + costV (cs.map binVal) F.v' F.r))
    have h5 := hup (Function.update (Function.update (Function.update (Function.update
      (regSt base W m F Ks) 17 F.v') 18 F.r) 23 [isSub F.v' F.r]) 29
      (numBits W (F.y + costV (cs.map binVal) F.v' F.r))) 28
      [decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal (base 3))]
    simp only [List.length_cons, List.length_nil, numBits, List.length_map,
      List.length_range] at h3 h4 h5 ⊢
    omega
  have hσS : σ.space ≤ S := by
    have hv : F.v'.length ≤ m := by simpa [m] using hF.2.2.2.2.1
    have hr : F.r.length ≤ m := by simpa [m] using hF.2.2.2.2.2
    have hmQ : m ≤ Q := by
      calc
        m ≤ m + W + 1 := by omega
        _ ≤ Q := by dsimp [Q]; exact Nat.le_pow (by omega)
    have hWQ : W ≤ Q := by
      calc
        W ≤ m + W + 1 := by omega
        _ ≤ Q := by dsimp [Q]; exact Nat.le_pow (by omega)
    have hsmall : 2 * m + W + 2 ≤ 10 * Q := by
      omega
    have hσ50 : σ.space ≤ E + 50 * Q := by omega
    have hcoef : 50 * Q ≤ (5 * KP + 50) * Q :=
      Nat.mul_le_mul_right Q (by omega)
    dsimp [S]
    omega
  have hregScratch : ∀ j : Fin 38, 17 ≤ j.val → regSt base W m F Ks j = [] :=
    m3ob_hregScratch base W m F Ks hbrest
  have hζ : ζ = regSt base W m F Ks :=
    m3ob_hζ base W m F Ks cs hregScratch
  have es₀ := clearList σ
  have es : Exec clearModeScratch σ ζ S := by
    have es' : Exec clearModeScratch σ
        (scratch.foldl (fun τ r => Function.update τ r []) σ) S := by
      simpa [clearModeScratch, scratch] using es₀.mono hσS
    simpa only [ζ] using es'
  have ep₀ := hPush base W m F Ks hbrest
  have hpframe := mul_frameSize_le_five_square KP m (binVal eb) W F hF
  have hpS : (encSt base W m (0, F :: Ks)).space + KP * frameSize W F ≤ S := by
    have hcoef : (5 * KP) * Q ≤ (5 * KP + 50) * Q :=
      Nat.mul_le_mul_right Q (by omega)
    have hpframe' : KP * frameSize W F ≤ (5 * KP) * Q := by
      simpa [Q] using hpframe
    dsimp [S]
    omega
  have ep : Exec sPush ζ υ S := by
    simpa [hζ, υ] using ep₀.mono hpS
  have em₀ := Stmt.exec_pushList (k := 38) 9 (List.replicate 4 true) υ
  have hemS : Stacks.space υ + (List.replicate 4 true).length ≤ S := by
    have hυ : Stacks.space υ ≤ (encSt base W m (0, F :: Ks)).space := by
      apply Stacks.space_update_le
      simp
    have hcoef : 50 * Q ≤ (5 * KP + 50) * Q :=
      Nat.mul_le_mul_right Q (by omega)
    have hfour : 4 ≤ 50 * Q := by omega
    simp only [List.length_replicate]
    dsimp [S]
    omega
  have em : Exec (putMode 4) υ (encSt base W m (4, F :: Ks)) S := by
    unfold putMode
    apply Stmt.exec_of_eq (em₀.mono hemS)
    exact m3ob_em base W m F Ks
  have ebody : Exec (Stmt.seqs [clearModeScratch, sPush, putMode 4]) σ
      (encSt base W m (4, F :: Ks)) S := by
    simpa [Stmt.seqs, υ] using
      Exec.seq es (Exec.seq ep (Exec.seq em (.skip em.space_le.2)))
  have h23 : σ 23 = true :: [] := by simp [σ, mode3TestSt, hsub]
  have h28 : σ 28 = false :: [] := by
    simp only [σ, mode3TestSt, Function.update_self, hb3, hle]
  rw [mode3Commit, Stmt.exec_caseBit h23, Stmt.exec_caseBit h28]
  simpa [m, E, Q, S] using ebody

end DFS
end Kolmogorov.RandomStrings
