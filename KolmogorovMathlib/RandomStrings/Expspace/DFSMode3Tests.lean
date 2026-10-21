/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode1

/-!
# The depth-first search: the tests of mode 3

Mode 3 examines the current YES answer.  This module provides the stack-avoidance transport
(`exec_update_avoided`), the cost routines that preserve stacks `29` and `23`, the definitions
`DFS.mode3Tests`, `DFS.mode3TestSt` and `DFS.mode3Commit`, and the contract of the tests
`DFS.exec_mode3Tests`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- A statement avoids a stack when it neither tests, pushes, nor pops that stack. -/
private def avoidsStack {k : ℕ} (j : Fin k) : Stmt k → Prop
  | .skip => True
  | .push r _ => r ≠ j
  | .pop r => r ≠ j
  | .seq a b => avoidsStack j a ∧ avoidsStack j b
  | .ite r _ a b => r ≠ j ∧ avoidsStack j a ∧ avoidsStack j b
  | .loop r _ b => r ≠ j ∧ avoidsStack j b

/-- Changing an unobserved stack transports an execution, paying only for its new content. -/
private theorem exec_update_avoided {k : ℕ} {s : Stmt k} {σ τ : Stacks k} {S : ℕ}
    (e : Exec s σ τ S) (j : Fin k) (v : BitString) (hj : avoidsStack j s) :
    Exec s (Function.update σ j v) (Function.update τ j v) (S + v.length) := by
  induction e with
  | @skip σ S hS =>
      apply Exec.skip
      have hu := Stacks.space_update σ j v
      omega
  | @push r b σ S hS =>
      have hn : r ≠ j := hj
      have hu := Stacks.space_update σ j v
      have e := Exec.push (r := r) (b := b) (σ := Function.update σ j v)
        (S := S + v.length) (by omega)
      apply Stmt.exec_of_eq e
      funext i
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | @pop r σ S hS =>
      have hn : r ≠ j := hj
      have hu := Stacks.space_update σ j v
      have e := Exec.pop (r := r) (σ := Function.update σ j v)
        (S := S + v.length) (by omega)
      apply Stmt.exec_of_eq e
      funext i
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ hj.1) (ih₂ hj.2)
  | iteT hc _ ih =>
      exact .iteT (by simpa only [Function.update_of_ne hj.1] using hc) (ih hj.2.1)
  | iteF hc _ ih =>
      exact .iteF (by simpa only [Function.update_of_ne hj.1] using hc) (ih hj.2.2)
  | loopT hc _ _ ih₁ ih₂ =>
      exact .loopT (by simpa only [Function.update_of_ne hj.1] using hc)
        (ih₁ hj.2) (ih₂ hj)
  | @loopF r cond body σ S hc hS =>
      apply Exec.loopF (by simpa only [Function.update_of_ne hj.1] using hc)
      have hu := Stacks.space_update σ j v
      omega

/-- The concrete cost routine never observes stack `29`. Clear that stack for its strict
contract, transport the execution with `exec_update_avoided`, and restore its saved content.
The added content length cancels the space removed by the initial clear. -/
theorem exists_costVStmt_except29 : ∃ (s : Stmt 38) (K : ℕ),
    ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
      σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
      (cs.map binVal).sum < 2 ^ W →
      (∀ j : Fin 38, 19 ≤ j.val → j.val ≠ 29 → σ j = []) →
      Exec s σ (Function.update σ 19
        (numBits W (costV (cs.map binVal) (σ 17) (σ 18))))
        (σ.space + K * ((Stacks.encList cs).length + (σ 17).length +
          (σ 18).length + W + 1)) := by
  refine ⟨costVStmt, 64, ?_⟩
  intro σ cs W h2 hcs h3 hsum he
  let ρ : Stacks 38 := Function.update σ 29 []
  have hρ : ∀ j : Fin 38, 19 ≤ j.val → ρ j = [] := by
    intro j hj
    by_cases h : j = 29
    · subst j; simp [ρ]
    · simp only [ρ, Function.update_of_ne h]
      exact he j hj (by intro hval; exact h (Fin.ext hval))
  have hi := exec_costVInitStmt ρ W (by simpa [ρ] using h3) hρ
    (ρ.space + 64 * ((Stacks.encList cs).length + (σ 17).length +
      (σ 18).length + W + 1)) (by simp only [ρ,
      Function.update_of_ne (by decide : (2 : Fin 38) ≠ 29),
      Function.update_of_ne (by decide : (17 : Fin 38) ≠ 29),
      Function.update_of_ne (by decide : (18 : Fin 38) ≠ 29), h2]; omega)
  have hl := exec_costVLoopStmt ρ cs W (by simpa [ρ] using h2) hcs hsum hρ
    (ρ.space + 64 * ((Stacks.encList cs).length + (σ 17).length +
      (σ 18).length + W + 1)) (by simp [ρ])
  have ha : avoidsStack (29 : Fin 38) costVStmt := by
    simp [avoidsStack, costVStmt, costVInitStmt, costVZeroStmt, costVLoopStmt,
      costVBodyStmt, Stmt.seqs, Stmt.copy, Stmt.dupStep,
      Stmt.moveAll, Stmt.moveBit, Stmt.caseBit, QEnum.zeroStep, Stmt.decodeOne,
      Stmt.decodeBody, Stmt.clear, Stmt.addInto, Stmt.addStep]
  have e := exec_update_avoided (.seq hi hl) 29 (σ 29) ha
  have hρspace := Stacks.space_update σ (29 : Fin 38) []
  have hb : ρ.space + 64 * ((Stacks.encList cs).length + (σ 17).length +
      (σ 18).length + W + 1) + (σ 29).length =
      σ.space + 64 * ((Stacks.encList cs).length + (σ 17).length +
        (σ 18).length + W + 1) := by
    simp only [List.length_nil, Nat.add_zero] at hρspace
    dsimp [ρ]
    omega
  rw [hb] at e
  change Exec costVStmt _ _ _ at e
  convert e using 1 <;> (funext j; fin_cases j <;> simp [ρ])

/-- Inlining along a permutation `f`: a run of `s` on `σ ∘ f` that writes `v` on stack `r`,
within space `Stacks.space (σ ∘ f) + B`, gives a run of `s.rename f` on `σ` that writes `v`
on stack `f r`, within space `σ.space + B`. -/
private theorem exec_rename_perm {k : ℕ} (f : Equiv.Perm (Fin k)) {s : Stmt k} {σ : Stacks k}
    {r : Fin k} {v : BitString} {B : ℕ}
    (h : Exec s (fun j => σ (f j)) (Function.update (fun j => σ (f j)) r v)
      (Stacks.space (fun j => σ (f j)) + B)) :
    Exec (s.rename f) σ (Function.update σ (f r) v) (σ.space + B) := by
  have e := Exec.rename_of_comp (τ := σ) f.injective h
  have h0 : Stacks.rest f σ = 0 := by simp [Stacks.rest]
  have h1 : Stacks.space (fun j => σ (f j)) = σ.space := by
    unfold Stacks.space
    exact Equiv.sum_comp f fun j => (σ j).length
  rw [← Stacks.update_extend f.injective, Stacks.extend_comp_self f.injective σ, h0, h1,
    Nat.add_zero] at e
  exact e

/-- Move the concrete cost routine's reversal scratch from `23` to unused stack `29`.
The permutation transports the preceding framed contract, so the inclusion flag on `23`
is preserved without changing the strict contract of `exists_costVStmt`. -/
theorem exists_costVStmt_except23 : ∃ (s : Stmt 38) (K : ℕ),
    ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
      σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
      (cs.map binVal).sum < 2 ^ W →
      (∀ j : Fin 38, 19 ≤ j.val → j ≠ 23 → σ j = []) →
      Exec s σ (Function.update σ 19
        (numBits W (costV (cs.map binVal) (σ 17) (σ 18))))
        (σ.space + K * ((Stacks.encList cs).length + (σ 17).length +
          (σ 18).length + W + 1)) := by
  obtain ⟨s, K, h⟩ := exists_costVStmt_except29
  obtain ⟨f, f23, hf⟩ : ∃ f : Equiv.Perm (Fin 38),
      f 23 = 29 ∧ ∀ j : Fin 38, j ≠ 23 → j ≠ 29 → f j = j :=
    ⟨Equiv.swap 23 29, Equiv.swap_apply_left 23 29,
      fun _ h23 h29 => Equiv.swap_apply_of_ne_of_ne h23 h29⟩
  refine ⟨s.rename f, K, ?_⟩
  intro σ cs W h2 hcs h3 hsum he
  have f2 : f 2 = 2 := hf 2 (by decide) (by decide)
  have f3 : f 3 = 3 := hf 3 (by decide) (by decide)
  have f17 : f 17 = 17 := hf 17 (by decide) (by decide)
  have f18 : f 18 = 18 := hf 18 (by decide) (by decide)
  have f19 : f 19 = 19 := hf 19 (by decide) (by decide)
  have hρ : ∀ j : Fin 38, 19 ≤ j.val → j.val ≠ 29 → σ (f j) = [] := by
    intro j hj hj29
    by_cases hj23 : j = 23
    · rw [hj23, f23]
      exact he 29 (by decide) (by decide)
    · rw [hf j hj23 (fun hh => hj29 (congrArg Fin.val hh))]
      exact he j hj hj23
  have e := h (fun j => σ (f j)) cs W ((congrArg σ f2).trans h2) hcs
    ((congrArg List.length (congrArg σ f3)).trans h3) hsum hρ
  have e' := exec_rename_perm (σ := σ) f e
  simp only [f17, f18, f19] at e'
  exact e'

/-- The concrete predicate-and-budget phase for mode `3`. -/
def mode3Tests (sCost sSub : Stmt 38) : Stmt 38 := Stmt.seqs [
  Stmt.copy 15 17 20, Stmt.copy 16 18 20, sSub, Stmt.moveAll 19 23, sCost,
  Stmt.copy 12 24 20, Stmt.addInto 24 19 25 26, Stmt.copy 24 29 20,
  Stmt.copy 3 27 20, Stmt.cmpInto 24 27 28]

/-- The intermediate stack state asserted for the mode-`3` tests. -/
def mode3TestSt (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (cs : List BitString) : Stacks 38 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (regSt base W m F Ks) 17 F.v') 18 F.r) 23 [isSub F.v' F.r]) 29
      (numBits W (F.y + costV (cs.map binVal) F.v' F.r))) 28
      [decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal (base 3))]

/-- In the successful mode-`3` branch this program computes the child's NO score, prepends the
parent with `pushRegFrame`, rewrites the registers to the child, and prepends it too.  The false
branches merely clear scratch, restore the parent with `sPush`, and enter mode `4`. -/
def mode3Commit (sPush sCost : Stmt 38) : Stmt 38 :=
  Stmt.caseBit 23 fun hsub => Stmt.caseBit 28 fun hle =>
    if hsub && hle then Stmt.seqs [
      Stmt.clear 23, Stmt.clear 28, Stmt.clear 17, Stmt.clear 18, Stmt.clear 19, Stmt.copy 11 17 20,
      Stmt.copy 15 18 20, sCost, Stmt.copy 13 30 20, Stmt.addInto 30 19 31 32,
      Stmt.clear 17, Stmt.clear 18, pushRegFrame, Stmt.clear 11, Stmt.copy 16 11 20,
      Stmt.clear 12, Stmt.copy 29 12 20, Stmt.clear 13, Stmt.copy 30 13 20,
      .pop 14, Stmt.clear 15, Stmt.clear 16, clearModeScratch, pushRegFrame,
      clearModeRegisters, putMode 0]
    else Stmt.seqs [clearModeScratch, sPush, putMode 4]

/-- Overwriting one stack grows the space by at most the length of the new contents. -/
private theorem m3t_space_upd (σ : Stacks 38) (r : Fin 38) (v : BitString) :
    Stacks.space (Function.update σ r v) ≤ σ.space + v.length := by
  have := Stacks.space_update σ r v
  omega

/-- Copying a string onto an empty stack `r'` through an empty work stack `t`. -/
private theorem m3t_exec_copy {σ : Stacks 38} {r r' t : Fin 38} {z : BitString} {S : ℕ}
    (hrr : r ≠ r') (hrt : r ≠ t) (hr't : r' ≠ t) (hz : σ r = z) (hr' : σ r' = [])
    (ht : σ t = []) (hS : σ.space + z.length ≤ S) :
    Exec (Stmt.copy r r' t) σ (Function.update σ r' z) S := by
  have e := Stmt.exec_copy hrr hrt hr't ht
  rw [hz, hr', List.append_nil] at e
  exact e.mono hS

/-- Writing a stack and clearing it again changes nothing when the stack started empty. -/
private theorem m3t_update_clear (σ : Stacks 38) (r : Fin 38) (v : BitString)
    (h : σ r = []) : Function.update (Function.update σ r v) r [] = σ := by
  funext j
  by_cases hj : j = r
  · subst hj
    simp [h]
  · simp [hj]

/-- Executing two statement lists one after the other executes their concatenation. -/
private theorem m3t_seqs_append : ∀ (l₁ l₂ : List (Stmt 38)) {σ μ τ : Stacks 38} {S : ℕ},
    Exec (Stmt.seqs l₁) σ μ S → Exec (Stmt.seqs l₂) μ τ S →
      Exec (Stmt.seqs (l₁ ++ l₂)) σ τ S
  | [], _, _, _, _, _, h₁, h₂ => by
      simp only [Stmt.seqs] at h₁
      cases h₁
      simpa using h₂
  | _ :: l₁, l₂, _, _, _, _, h₁, h₂ => by
      rw [Stmt.exec_seqs_cons] at h₁
      obtain ⟨ν, hs, hr⟩ := h₁
      rw [List.cons_append, Stmt.exec_seqs_cons]
      exact ⟨ν, hs, m3t_seqs_append l₁ _ hr h₂⟩

/-- The registers `17`--`37` of `regSt` are empty when `base` is empty from register `5` on. -/
private theorem m3t_regSt_high (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
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

/-- `costV` charges at most the sum of the cost vector. -/
private theorem m3t_costV_le_sum (ds : List ℕ) :
    ∀ v w : BitString, costV ds v w ≤ ds.sum := by
  induction ds with
  | nil =>
      intro v w
      simp [costV]
  | cons d ds ih =>
      intro v w
      cases v with
      | nil => simp [costV]
      | cons a v =>
          cases w with
          | nil => simp [costV]
          | cons b w =>
              rw [pv_costV_cons, List.sum_cons]
              have hi := ih v w
              split <;> omega

/-- The quadratic allowance of the mode-`3` tests covers the register space, the words `v`, `r`
of at most `m` bits, the width-`W` words and both routine costs.  Here `Q = (m + W + 1) ^ 2`, the
register space is at most `E + 5 * KP * Q`, and the coded cost list has at most `2 * Q` bits. -/
private theorem m3t_allowance (KP KC KI m W e v r R E : ℕ)
    (hR : R ≤ E + 5 * KP * (m + W + 1) ^ 2) (hv : v ≤ m) (hr : r ≤ m)
    (he : e ≤ 2 * (m + W + 1) ^ 2) :
    R + v + r + 2 + 4 * W + KI * (v + r + 1) + KC * (e + v + r + W + 1) ≤
      E + (5 * KP + 10 + 6 * KC + 3 * KI) * (m + W + 1) ^ 2 := by
  have hQ : m + W + 1 ≤ (m + W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1 : KI * (v + r + 1) ≤ KI * (3 * (m + W + 1) ^ 2) :=
    Nat.mul_le_mul_left KI (by omega)
  have h2 : KC * (e + v + r + W + 1) ≤ KC * (6 * (m + W + 1) ^ 2) :=
    Nat.mul_le_mul_left KC (by omega)
  have h3 : (5 * KP + 10 + 6 * KC + 3 * KI) * (m + W + 1) ^ 2 =
      5 * KP * (m + W + 1) ^ 2 + 10 * (m + W + 1) ^ 2 + KC * (6 * (m + W + 1) ^ 2) +
        KI * (3 * (m + W + 1) ^ 2) := by ring
  omega

/-- The state after the budget comparison: the stacks `19`, `24` and `27` are cleared again, the
sum is kept on `29` and the verdict `b` sits on `28`.  Here `σ` is the state after the addition,
which agrees with `B` off the stacks `19` and `24`. -/
private theorem m3t_budget_state (B σ : Stacks 38) (T eb : BitString) (b : Bool)
    (hB19 : B 19 = []) (hB24 : B 24 = []) (hB27 : B 27 = []) (hσ19 : σ 19 = [])
    (hσ : ∀ j : Fin 38, j ≠ 19 → j ≠ 24 → σ j = B j) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update σ 29 T) 27 eb) 24 []) 27 []) 28 [b] =
      Function.update (Function.update B 29 T) 28 [b] := by
  funext j
  by_cases h28 : j = 28
  · subst h28
    simp
  by_cases h27 : j = 27
  · subst h27
    simp [hB27]
  by_cases h24 : j = 24
  · subst h24
    simp [hB24]
  by_cases h29 : j = 29
  · subst h29
    simp
  by_cases h19 : j = 19
  · subst h19
    simp [hB19, hσ19]
  simp [h28, h27, h24, h29, hσ j h19 h24]

/-- The first phase of the mode-`3` tests: copy `v` and `r` from the registers `15` and `16` onto
the empty stacks `17` and `18`, let `sSub` write their inclusion bit on `19`, and move that bit to
stack `23`. -/
private theorem m3t_exec_prep (sSub : Stmt 38) (KI : ℕ)
    (hSub : ∀ σ : Stacks 38, (∀ j : Fin 38, 19 ≤ j.val → σ j = []) →
      Exec sSub σ (Function.update σ 19 [isSub (σ 17) (σ 18)])
        (σ.space + KI * ((σ 17).length + (σ 18).length + 1)))
    (R : Stacks 38) (v r : BitString) (h15 : R 15 = v) (h16 : R 16 = r)
    (hR : ∀ j : Fin 38, 17 ≤ j.val → R j = []) (S : ℕ)
    (hS : R.space + v.length + r.length + 1 + KI * (v.length + r.length + 1) ≤ S) :
    Exec (Stmt.seqs [Stmt.copy 15 17 20, Stmt.copy 16 18 20, sSub, Stmt.moveAll 19 23]) R
      (Function.update (Function.update (Function.update R 17 v) 18 r) 23 [isSub v r]) S := by
  have s1 := m3t_space_upd R 17 v
  have s2 := m3t_space_upd (Function.update R 17 v) 18 r
  have s3 := m3t_space_upd (Function.update (Function.update R 17 v) 18 r) 19 [isSub v r]
  simp only [List.length_cons, List.length_nil] at s3
  have e₁ : Exec (Stmt.copy 15 17 20) R (Function.update R 17 v) S :=
    m3t_exec_copy (by decide) (by decide) (by decide) h15 (hR 17 (by decide))
      (hR 20 (by decide)) (by omega)
  have e₂ : Exec (Stmt.copy 16 18 20) (Function.update R 17 v)
      (Function.update (Function.update R 17 v) 18 r) S :=
    m3t_exec_copy (by decide) (by decide) (by decide) (by simp [h16])
      (by simp [hR 18 (by decide)]) (by simp [hR 20 (by decide)]) (by omega)
  have h2 : ∀ j : Fin 38, 19 ≤ j.val →
      Function.update (Function.update R 17 v) 18 r j = [] := by
    intro j hj
    have hne : ∀ k : Fin 38, k.val < 19 → j ≠ k := fun k hk h => by rw [h] at hj; omega
    rw [Function.update_of_ne (hne 18 (by decide)), Function.update_of_ne (hne 17 (by decide))]
    exact hR j (by omega)
  have e₃ := hSub (Function.update (Function.update R 17 v) 18 r) h2
  have h217 : Function.update (Function.update R 17 v) 18 r 17 = v := by simp
  have h218 : Function.update (Function.update R 17 v) 18 r 18 = r := by simp
  rw [h217, h218] at e₃
  have e₃' : Exec sSub (Function.update (Function.update R 17 v) 18 r)
      (Function.update (Function.update (Function.update R 17 v) 18 r) 19 [isSub v r]) S :=
    e₃.mono (by omega)
  have h19 : Function.update (Function.update R 17 v) 18 r 19 = [] := h2 19 (by decide)
  have h23 : Function.update (Function.update (Function.update R 17 v) 18 r) 19 [isSub v r] 23 =
      [] := by simp [hR 23 (by decide)]
  have e₄ := Stmt.exec_moveAll (k := 38) (r := (19 : Fin 38)) (r' := 23) (by decide) [isSub v r]
    (Function.update (Function.update (Function.update R 17 v) 18 r) 19 [isSub v r]) (by simp)
  rw [m3t_update_clear _ _ _ h19, h23] at e₄
  have e₄' : Exec (Stmt.moveAll 19 23)
      (Function.update (Function.update (Function.update R 17 v) 18 r) 19 [isSub v r])
      (Function.update (Function.update (Function.update R 17 v) 18 r) 23 [isSub v r]) S :=
    e₄.mono (by omega)
  exact .seq e₁ (.seq e₂ (.seq e₃' (.seq e₄' (.skip e₄'.space_le.2))))

/-- The budget comparison of the mode-`3` tests, run after the cost routine has written
`numBits W c` on `19`: it adds `numBits W y` and `numBits W c`, keeps the sum on `29`, and leaves
the verdict `y + c ≤ binVal eb` on `28`, with all other scratch stacks cleared again. -/
private theorem m3t_exec_budget (y c W : ℕ) (eb : BitString) (B : Stacks 38) (S : ℕ)
    (hlt : y + c < 2 ^ W) (heb : eb.length = W) (h3 : B 3 = eb) (h12 : B 12 = numBits W y)
    (hB : ∀ j : Fin 38, 19 ≤ j.val → j ≠ 23 → B j = []) (hS : B.space + 4 * W + 1 ≤ S) :
    Exec (Stmt.seqs [Stmt.copy 12 24 20, Stmt.addInto 24 19 25 26, Stmt.copy 24 29 20,
      Stmt.copy 3 27 20, Stmt.cmpInto 24 27 28]) (Function.update B 19 (numBits W c))
      (Function.update (Function.update B 29 (numBits W (y + c))) 28
        [decide (y + c ≤ binVal eb)]) S := by
  have hnl : ∀ x : ℕ, (numBits W x).length = W := fun x => by simp [numBits]
  have hc : c < 2 ^ W := by omega
  have hadd : addBits false (numBits W y) (numBits W c) = numBits W (y + c) := by
    rw [addBits_numBits W y (numBits W c) (hnl c)
      (by rw [binVal_numBits_of_lt W c hc]; exact hlt), binVal_numBits_of_lt W c hc]
  have hcmp : cmpBits true (numBits W (y + c)) eb = decide (y + c ≤ binVal eb) := by
    rw [Bool.eq_iff_iff, cmpBits_true_iff _ _ (by rw [hnl, heb]), decide_eq_true_iff,
      binVal_numBits_of_lt W (y + c) hlt]
  obtain ⟨A, hA⟩ : ∃ A : Stacks 38, A = Function.update B 19 (numBits W c) := ⟨_, rfl⟩
  rw [← hA]
  have hAB : ∀ j : Fin 38, j ≠ 19 → A j = B j := fun j hj => by
    rw [hA, Function.update_of_ne hj]
  have hA19 : A 19 = numBits W c := by rw [hA, Function.update_self]
  have hAs : A.space ≤ B.space + W := by
    have h := m3t_space_upd B 19 (numBits W c)
    rw [hnl, ← hA] at h
    exact h
  have hE : ∀ j : Fin 38, 20 ≤ j.val → j ≠ 23 → A j = [] := by
    intro j hj hj23
    have hj19 : j ≠ 19 := fun h => by rw [h] at hj; exact absurd hj (by decide)
    rw [hAB j hj19]
    exact hB j (by omega) hj23
  have e₆ : Exec (Stmt.copy 12 24 20) A (Function.update A 24 (numBits W y)) S :=
    m3t_exec_copy (by decide) (by decide) (by decide) ((hAB 12 (by decide)).trans h12)
      (hE 24 (by decide) (by decide)) (hE 20 (by decide) (by decide)) (by rw [hnl]; omega)
  have s6 := m3t_space_upd A 24 (numBits W y)
  rw [hnl] at s6
  have e₇ := Stmt.exec_addInto (k := 38) (A := (24 : Fin 38)) (B := 19) (Cy := 25) (R := 26)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (σ := Function.update A 24 (numBits W y)) (l := numBits W y) (m := numBits W c)
    (by rw [hnl, hnl]) (by simp) (by simpa using hA19) (by simp [hE 25 (by decide) (by decide)])
    (by simp [hE 26 (by decide) (by decide)])
  rw [hadd, Function.update_idem] at e₇
  generalize hσ₇ : Function.update (Function.update A 24 (numBits W (y + c))) 19 [] = σ₇
    at e₇
  have hσ₇B : ∀ j : Fin 38, j ≠ 19 → j ≠ 24 → σ₇ j = B j := fun j h19 h24 => by
    rw [← hσ₇, Function.update_of_ne h19, Function.update_of_ne h24, hAB j h19]
  have hσ₇19 : σ₇ 19 = [] := by rw [← hσ₇, Function.update_self]
  have hσ₇24 : σ₇ 24 = numBits W (y + c) := by
    rw [← hσ₇, Function.update_of_ne (by decide), Function.update_self]
  have hs7 : Stacks.space σ₇ ≤ A.space + W := by
    have h1 := m3t_space_upd A 24 (numBits W (y + c))
    have h2 := Stacks.space_update_le (Function.update A 24 (numBits W (y + c))) 19 [] (by simp)
    rw [hnl] at h1
    rw [← hσ₇]
    omega
  have e₈ : Exec (Stmt.copy 24 29 20) σ₇ (Function.update σ₇ 29 (numBits W (y + c))) S :=
    m3t_exec_copy (by decide) (by decide) (by decide) hσ₇24
      ((hσ₇B 29 (by decide) (by decide)).trans (hB 29 (by decide) (by decide)))
      ((hσ₇B 20 (by decide) (by decide)).trans (hB 20 (by decide) (by decide)))
      (by rw [hnl]; omega)
  have hs8 := m3t_space_upd σ₇ 29 (numBits W (y + c))
  rw [hnl] at hs8
  have e₉ : Exec (Stmt.copy 3 27 20) (Function.update σ₇ 29 (numBits W (y + c)))
      (Function.update (Function.update σ₇ 29 (numBits W (y + c))) 27 eb) S :=
    m3t_exec_copy (by decide) (by decide) (by decide)
      (by simp [hσ₇B 3 (by decide) (by decide), h3])
      (by simp [hσ₇B 27 (by decide) (by decide), hB 27 (by decide) (by decide)])
      (by simp [hσ₇B 20 (by decide) (by decide), hB 20 (by decide) (by decide)])
      (by rw [heb]; omega)
  have hs9 := m3t_space_upd (Function.update σ₇ 29 (numBits W (y + c))) 27 eb
  rw [heb] at hs9
  have e₁₀ := Stmt.exec_cmpInto (k := 38) (A := (24 : Fin 38)) (B := 27) (F := 28)
    (by decide) (by decide) (by decide)
    (σ := Function.update (Function.update σ₇ 29 (numBits W (y + c))) 27 eb)
    (l := numBits W (y + c)) (m := eb) (by rw [hnl, heb]) (by simp [hσ₇24]) (by simp)
    (by simp [hσ₇B 28 (by decide) (by decide), hB 28 (by decide) (by decide)])
  rw [hcmp] at e₁₀
  have e₁₀' := Stmt.exec_of_eq (e₁₀.mono (S' := S) (by omega))
    (m3t_budget_state B σ₇ (numBits W (y + c)) eb (decide (y + c ≤ binVal eb))
      (hB 19 (by decide) (by decide)) (hB 24 (by decide) (by decide))
      (hB 27 (by decide) (by decide)) hσ₇19 hσ₇B)
  exact .seq e₆ (.seq (e₇.mono (by omega)) (.seq e₈ (.seq e₉
    (.seq e₁₀' (.skip e₁₀'.space_le.2)))))

/-- Prove this phase exactly as `exec_mode1Tests`, omitting equality and retaining a copy of the
YES sum on stack `29` before comparison.  The cost and inclusion sub-contracts supply the only
non-primitive executions, while `FrameOK` and the global width inequality discharge overflow. -/
theorem exec_mode3Tests (sCost sSub : Stmt 38) (KC KI : ℕ)
    (hCost : ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
      σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
      (cs.map binVal).sum < 2 ^ W → (∀ j : Fin 38, 19 ≤ j.val → j ≠ 23 → σ j = []) →
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
      Exec (mode3Tests sCost sSub) (regSt base W LX.length F Ks)
        (mode3TestSt base W LX.length F Ks cs)
        ((encSt base W LX.length (3, F :: Ks)).space + K * (LX.length + W + 1) ^ 2) := by
  obtain ⟨sPop, KP, hPop⟩ := exists_popFrameStmt
  refine ⟨5 * KP + 10 + 6 * KC + 3 * KI, ?_⟩
  intro base LX cs eb W F Ks hbase hlen hcs heb hsum hF
  have hhigh := m3t_regSt_high base W LX.length F Ks hbase.2.2.2
  have h2 : regSt base W LX.length F Ks 2 = Stacks.encList cs := by
    simpa [regSt, encSt] using hbase.2.1
  have h3 : regSt base W LX.length F Ks 3 = eb := by
    simpa [regSt, encSt] using hbase.2.2.1
  have h12 : regSt base W LX.length F Ks 12 = numBits W F.y := by simp [regSt]
  have h15 : regSt base W LX.length F Ks 15 = F.v' := by simp [regSt]
  have h16 : regSt base W LX.length F Ks 16 = F.r := by simp [regSt]
  have hsp := (hPop base W LX.length 3 F Ks hbase.2.2.2).space_le.2.trans
    (Nat.add_le_add_left (mul_frameSize_le_five_square KP LX.length (binVal eb) W F hF) _)
  have henc : (Stacks.encList cs).length ≤ 2 * (LX.length + W + 1) ^ 2 := by
    calc (Stacks.encList cs).length ≤ cs.length * (2 * W + 1) :=
          QEnum.length_encList_le W cs fun z hz => by simp [hcs z hz]
      _ = LX.length * (2 * W + 1) := by rw [hlen]
      _ ≤ (LX.length + W + 1) * (2 * (LX.length + W + 1)) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (LX.length + W + 1) ^ 2 := by ring
  have hZ := m3t_allowance KP KC KI LX.length W (Stacks.encList cs).length F.v'.length
    F.r.length _ _ hsp hF.2.2.2.2.1 hF.2.2.2.2.2 henc
  have hlt : F.y + costV (cs.map binVal) F.v' F.r < 2 ^ W := by
    have hc := m3t_costV_le_sum (cs.map binVal) F.v' F.r
    have hy := hF.2.1
    omega
  have hsum' : (cs.map binVal).sum < 2 ^ W := by omega
  have hb3 : base 3 = eb := hbase.2.2.1
  unfold mode3TestSt
  rw [hb3]
  generalize regSt base W LX.length F Ks = R at h2 h3 h12 h15 h16 hhigh hZ ⊢
  generalize hS : (encSt base W LX.length (3, F :: Ks)).space +
    (5 * KP + 10 + 6 * KC + 3 * KI) * (LX.length + W + 1) ^ 2 = S at hZ ⊢
  have hS1 : R.space + F.v'.length + F.r.length + 1 +
      KI * (F.v'.length + F.r.length + 1) ≤ S := by omega
  have ePrep := m3t_exec_prep sSub KI hSub R F.v' F.r h15 h16 hhigh S hS1
  generalize hσ₄ : Function.update (Function.update (Function.update R 17 F.v') 18 F.r) 23
    [isSub F.v' F.r] = σ₄ at ePrep ⊢
  have h42 : σ₄ 2 = Stacks.encList cs := by
    rw [← hσ₄]
    simpa using h2
  have h43 : σ₄ 3 = eb := by
    rw [← hσ₄]
    simpa using h3
  have h412 : σ₄ 12 = numBits W F.y := by
    rw [← hσ₄]
    simpa using h12
  have h417 : σ₄ 17 = F.v' := by
    rw [← hσ₄]
    simp
  have h418 : σ₄ 18 = F.r := by
    rw [← hσ₄]
    simp
  have hσ4high : ∀ j : Fin 38, 19 ≤ j.val → j ≠ 23 → σ₄ j = [] := by
    intro j hj hj23
    have hne : ∀ k : Fin 38, k.val < 19 → j ≠ k := fun k hk h => by rw [h] at hj; omega
    rw [← hσ₄, Function.update_of_ne hj23, Function.update_of_ne (hne 18 (by decide)),
      Function.update_of_ne (hne 17 (by decide))]
    exact hhigh j (by omega)
  have hσ4sp : Stacks.space σ₄ ≤ R.space + F.v'.length + F.r.length + 1 := by
    have s1 := m3t_space_upd R 17 F.v'
    have s2 := m3t_space_upd (Function.update R 17 F.v') 18 F.r
    have s3 := m3t_space_upd (Function.update (Function.update R 17 F.v') 18 F.r) 23
      [isSub F.v' F.r]
    simp only [List.length_cons, List.length_nil] at s3
    rw [← hσ₄]
    omega
  have hS2 : Stacks.space σ₄ +
      KC * ((Stacks.encList cs).length + F.v'.length + F.r.length + W + 1) ≤ S := by omega
  have hS3 : Stacks.space σ₄ + 4 * W + 1 ≤ S := by omega
  have eCost := hCost σ₄ cs W h42 hcs (by rw [h43]; exact heb) hsum' hσ4high
  rw [h417, h418] at eCost
  have eBudget := m3t_exec_budget F.y (costV (cs.map binVal) F.v' F.r) W eb σ₄ S hlt heb h43
    h412 hσ4high hS3
  unfold mode3Tests
  exact m3t_seqs_append _ _ ePrep (Stmt.exec_seqs_cons.2 ⟨_, eCost.mono hS2, eBudget⟩)

end DFS
end Kolmogorov.RandomStrings
