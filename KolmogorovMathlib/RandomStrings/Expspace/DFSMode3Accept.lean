/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode3Reject

/-!
# The depth-first search: the accepting leaf of mode 3

The commit leaf of mode 3 that accepts the current YES answer and pushes the child frame, split
at the point where the unchanged parent has been encoded (`m3a_prefix`, `m3a_suffix`), and the
assembly of the whole commit phase `DFS.exec_mode3Commit` and of `DFS.exists_mode3Stmt`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-! The successful leaf is split at the point where the unchanged parent has been encoded.
The first list computes the child's NO score and pushes the parent; the second list installs and
pushes the child. -/

private def mode3AcceptPrefix (sCost : Stmt 38) : List (Stmt 38) :=
  [Stmt.clear 23, Stmt.clear 28, Stmt.clear 17, Stmt.clear 18, Stmt.clear 19,
    Stmt.copy 11 17 20, Stmt.copy 15 18 20, sCost, Stmt.copy 13 30 20,
    Stmt.addInto 30 19 31 32, Stmt.clear 17, Stmt.clear 18, pushRegFrame]

private def mode3AcceptSuffix : List (Stmt 38) :=
  [Stmt.clear 11, Stmt.copy 16 11 20, Stmt.clear 12, Stmt.copy 29 12 20,
    Stmt.clear 13, Stmt.copy 30 13 20, .pop 14, Stmt.clear 15, Stmt.clear 16,
    clearModeScratch, pushRegFrame, clearModeRegisters, putMode 0]

/-- State at the successful branch's natural midpoint: the parent has been prepended to stack
`8`, its six registers are unchanged, stack `29` retains the YES score, and stack `30` contains
the newly computed NO score. -/
private def mode3ParentPushedSt (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (cs : List BitString) : Stacks 38 :=
  Function.update (Function.update (regSt base W m F (F :: Ks)) 29
    (numBits W (F.y + costV (cs.map binVal) F.v' F.r))) 30
    (numBits W (F.n + costV (cs.map binVal) F.v F.v'))

/-- `costV` charges at most the sum of the cost vector.  Thus the global width inequality and
the `FrameOK` bound on `F.n` ensure that the child's NO score fits in `W` bits. -/
private theorem mode3_accept_noScore_lt (cs : List BitString) (eb : BitString) (W m : ℕ)
    (F : Frame) (hsum : binVal eb + (cs.map binVal).sum < 2 ^ W)
    (hF : FrameOK m (binVal eb) F) :
    F.n + costV (cs.map binVal) F.v F.v' < 2 ^ W := by
  have hcost : ∀ (ds : List ℕ) (v w : BitString), costV ds v w ≤ ds.sum := by
    intro ds
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
  have hn := hF.2.2.1
  have hc := hcost (cs.map binVal) F.v F.v'
  omega

/-- Executing two statement lists one after the other executes their concatenation. -/
private theorem m3a_seqs_append : ∀ (l₁ l₂ : List (Stmt 38)) {σ μ τ : Stacks 38} {S : ℕ},
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
      exact ⟨ν, hs, m3a_seqs_append l₁ _ hr h₂⟩

/-- A one-element statement list executes as its element. -/
private theorem m3a_seqs_single {s : Stmt 38} {σ τ : Stacks 38} {S : ℕ}
    (e : Exec s σ τ S) : Exec (Stmt.seqs [s]) σ τ S :=
  Exec.seq e (.skip e.space_le.2)

/-- Clearing a list of stacks one by one, within the initial space. -/
private theorem m3a_clearList : ∀ (rs : List (Fin 38)) (σ : Stacks 38),
    Exec (Stmt.seqs (rs.map Stmt.clear)) σ (rs.foldl (fun τ r => Function.update τ r []) σ)
      σ.space
  | [], σ => by simpa [Stmt.seqs] using (Exec.skip (σ := σ) (S := σ.space) le_rfl)
  | r :: rs, σ => by
      have e₁ := Stmt.exec_clear r (σ r) σ rfl
      have e₂ := m3a_clearList rs (Function.update σ r [])
      simpa [Stmt.seqs] using Exec.seq e₁ (e₂.mono e₁.space_le.2)

private theorem m3a_space_upd (σ : Stacks 38) (r : Fin 38) (v : BitString) :
    Stacks.space (Function.update σ r v) ≤ σ.space + v.length := by
  have := Stacks.space_update σ r v
  omega

private theorem m3a_space_clr (σ : Stacks 38) (r : Fin 38) :
    Stacks.space (Function.update σ r []) ≤ σ.space :=
  Stacks.space_update_le σ r [] (by simp)

private theorem m3a_space_push8 (σ : Stacks 38) (p : BitString) :
    Stacks.space (Function.update σ 8 (p ++ σ 8)) = σ.space + p.length := by
  have := Stacks.space_update σ 8 (p ++ σ 8)
  simp only [List.length_append] at this
  omega

/-- `pushRegFrame` prepends the codes of registers `11`–`16` to stack `8`, using the empty
work stack `19`. -/
private theorem m3a_exec_pushRegFrame (σ : Stacks 38) (z₁ z₂ z₃ z₄ z₅ z₆ : BitString)
    (S : ℕ) (h11 : σ 11 = z₁) (h12 : σ 12 = z₂) (h13 : σ 13 = z₃) (h14 : σ 14 = z₄)
    (h15 : σ 15 = z₅) (h16 : σ 16 = z₆) (h19 : σ 19 = [])
    (hS : σ.space + 2 * (z₁.length + z₂.length + z₃.length + z₄.length + z₅.length +
      z₆.length) + 6 ≤ S) :
    Exec pushRegFrame σ
      (Function.update σ 8 (Stacks.encList [z₁, z₂, z₃, z₄, z₅, z₆] ++ σ 8)) S := by
  have hstep : ∀ (Z : Fin 38) (ρ : Stacks 38) (z : BitString), Z ≠ 19 → Z ≠ 8 →
      ρ Z = z → ρ 19 = [] → ρ.space + 2 * z.length + 1 ≤ S →
      Exec (QEnum.pushCode Z 19 8) ρ (Function.update ρ 8 (Stacks.encStr z ++ ρ 8)) S := by
    intro Z ρ z hZ19 hZ8 hz hρ19 hρ
    have e := QEnum.exec_pushCode hZ19 hZ8 (by decide : (19 : Fin 38) ≠ 8) hρ19
    rw [hz] at e
    exact e.mono hρ
  have hsp : ∀ (ρ : Stacks 38) (z : BitString),
      Stacks.space (Function.update ρ 8 (Stacks.encStr z ++ ρ 8)) =
        ρ.space + 2 * z.length + 1 := by
    intro ρ z
    rw [m3a_space_push8, Stacks.length_encStr]
    omega
  obtain ⟨σ1, h1⟩ : ∃ τ : Stacks 38,
      τ = Function.update σ 8 (Stacks.encStr z₆ ++ σ 8) := ⟨_, rfl⟩
  obtain ⟨σ2, h2⟩ : ∃ τ : Stacks 38,
      τ = Function.update σ1 8 (Stacks.encStr z₅ ++ σ1 8) := ⟨_, rfl⟩
  obtain ⟨σ3, h3⟩ : ∃ τ : Stacks 38,
      τ = Function.update σ2 8 (Stacks.encStr z₄ ++ σ2 8) := ⟨_, rfl⟩
  obtain ⟨σ4, h4⟩ : ∃ τ : Stacks 38,
      τ = Function.update σ3 8 (Stacks.encStr z₃ ++ σ3 8) := ⟨_, rfl⟩
  obtain ⟨σ5, h5⟩ : ∃ τ : Stacks 38,
      τ = Function.update σ4 8 (Stacks.encStr z₂ ++ σ4 8) := ⟨_, rfl⟩
  obtain ⟨σ6, h6⟩ : ∃ τ : Stacks 38,
      τ = Function.update σ5 8 (Stacks.encStr z₁ ++ σ5 8) := ⟨_, rfl⟩
  have s1 : σ1.space = σ.space + 2 * z₆.length + 1 := by rw [h1, hsp]
  have s2 : σ2.space = σ1.space + 2 * z₅.length + 1 := by rw [h2, hsp]
  have s3 : σ3.space = σ2.space + 2 * z₄.length + 1 := by rw [h3, hsp]
  have s4 : σ4.space = σ3.space + 2 * z₃.length + 1 := by rw [h4, hsp]
  have s5 : σ5.space = σ4.space + 2 * z₂.length + 1 := by rw [h5, hsp]
  have e1 := hstep 16 σ z₆ (by decide) (by decide) h16 h19 (by omega)
  have e2 := hstep 15 σ1 z₅ (by decide) (by decide) (by simp [h1, h15])
    (by simp [h1, h19]) (by omega)
  have e3 := hstep 14 σ2 z₄ (by decide) (by decide) (by simp [h2, h1, h14])
    (by simp [h2, h1, h19]) (by omega)
  have e4 := hstep 13 σ3 z₃ (by decide) (by decide) (by simp [h3, h2, h1, h13])
    (by simp [h3, h2, h1, h19]) (by omega)
  have e5 := hstep 12 σ4 z₂ (by decide) (by decide) (by simp [h4, h3, h2, h1, h12])
    (by simp [h4, h3, h2, h1, h19]) (by omega)
  have e6 := hstep 11 σ5 z₁ (by decide) (by decide) (by simp [h5, h4, h3, h2, h1, h11])
    (by simp [h5, h4, h3, h2, h1, h19]) (by omega)
  rw [← h1] at e1
  rw [← h2] at e2
  rw [← h3] at e3
  rw [← h4] at e4
  rw [← h5] at e5
  rw [← h6] at e6
  have heq : σ6 =
      Function.update σ 8 (Stacks.encList [z₁, z₂, z₃, z₄, z₅, z₆] ++ σ 8) := by
    funext i
    by_cases h : i = 8
    · subst h
      simp [h6, h5, h4, h3, h2, h1, Stacks.encList]
    · simp [h6, h5, h4, h3, h2, h1, h]
  rw [← heq]
  unfold pushRegFrame
  rw [Stmt.exec_seqs_cons]; refine ⟨σ1, e1, ?_⟩
  rw [Stmt.exec_seqs_cons]; refine ⟨σ2, e2, ?_⟩
  rw [Stmt.exec_seqs_cons]; refine ⟨σ3, e3, ?_⟩
  rw [Stmt.exec_seqs_cons]; refine ⟨σ4, e4, ?_⟩
  rw [Stmt.exec_seqs_cons]; refine ⟨σ5, e5, ?_⟩
  rw [Stmt.exec_seqs_cons]; refine ⟨σ6, e6, ?_⟩
  exact Exec.skip e6.space_le.2

private theorem m3a_numBits_length (W x : ℕ) : (numBits W x).length = W := by
  simp [numBits]

/-- Every stack of `regSt` from `17` on is empty when the base has nothing above stack `4`. -/
private theorem m3a_prefix_regSt_high (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (hbrest : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    ∀ j : Fin 38, 17 ≤ j.val → regSt base W m F Ks j = [] := by
  intro j hj
  fin_cases j <;> norm_num at hj <;> simp [regSt, encSt, hbrest]

/-- Pushing the parent frame puts its code on stack `8` of the register state and changes no
other stack. -/
private theorem m3a_prefix_regSt_cons (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) :
    regSt base W m F (F :: Ks) = Function.update (regSt base W m F Ks) 8
      (Stacks.encList (Frame.fields W F) ++ regSt base W m F Ks 8) := by
  funext j
  by_cases h8 : j = 8
  · subst h8
    simp [regSt, encSt, Stacks.encList, Frame.fields]
  · simp [regSt, encSt, Function.update_apply, h8]

/-- Prepending the parent's code to stack `8` of the register state that carries the two scores
gives the state `mode3ParentPushedSt`. -/
private theorem m3a_prefix_push_state (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (cs : List BitString) (P : Stacks 38)
    (hP : P = Function.update (Function.update (regSt base W m F Ks) 29
      (numBits W (F.y + costV (cs.map binVal) F.v' F.r))) 30
      (numBits W (F.n + costV (cs.map binVal) F.v F.v'))) :
    Function.update P 8 (Stacks.encList (Frame.fields W F) ++ P 8) =
      mode3ParentPushedSt base W m F Ks cs := by
  have h8 : P 8 = regSt base W m F Ks 8 := by simp [hP]
  rw [h8, hP, mode3ParentPushedSt, m3a_prefix_regSt_cons,
    Function.update_comm (by decide : (30 : Fin 38) ≠ 8),
    Function.update_comm (by decide : (29 : Fin 38) ≠ 8)]

/-- The mode-`3` test state exceeds the register state only by the two work strings, the two
flags and the YES score. -/
private theorem m3a_prefix_space_testSt (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (cs : List BitString) :
    (mode3TestSt base W m F Ks cs).space ≤
      (regSt base W m F Ks).space + F.v'.length + F.r.length + W + 2 := by
  have h1 := m3a_space_upd (regSt base W m F Ks) 17 F.v'
  have h2 := m3a_space_upd (Function.update (regSt base W m F Ks) 17 F.v') 18 F.r
  have h3 := m3a_space_upd (Function.update (Function.update (regSt base W m F Ks) 17 F.v')
    18 F.r) 23 [isSub F.v' F.r]
  have h4 := m3a_space_upd (Function.update (Function.update (Function.update
    (regSt base W m F Ks) 17 F.v') 18 F.r) 23 [isSub F.v' F.r]) 29
    (numBits W (F.y + costV (cs.map binVal) F.v' F.r))
  have h5 := m3a_space_upd (Function.update (Function.update (Function.update (Function.update
    (regSt base W m F Ks) 17 F.v') 18 F.r) 23 [isSub F.v' F.r]) 29
    (numBits W (F.y + costV (cs.map binVal) F.v' F.r))) 28
    [decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal (base 3))]
  simp only [List.length_cons, List.length_nil, m3a_numBits_length] at h3 h4 h5
  unfold mode3TestSt
  omega

/-- Overwriting one stack grows the space by at most the length of the new contents. -/
private theorem m3a_prefix_space_of_upd {σ τ : Stacks 38} {r : Fin 38} {v : BitString}
    (h : τ = Function.update σ r v) : τ.space ≤ σ.space + v.length := by
  rw [h]
  exact m3a_space_upd σ r v

/-- Copying a string onto an empty stack `r'` through an empty work stack `t`. -/
private theorem m3a_prefix_exec_copy {σ : Stacks 38} {r r' t : Fin 38} {z : BitString}
    {S : ℕ} (hrr : r ≠ r') (hrt : r ≠ t) (hr't : r' ≠ t) (hz : σ r = z) (hr' : σ r' = [])
    (ht : σ t = []) (hS : σ.space + z.length ≤ S) :
    Exec (Stmt.copy r r' t) σ (Function.update σ r' z) S := by
  have e := Stmt.exec_copy hrr hrt hr't ht
  rw [hz, hr', List.append_nil] at e
  exact e.mono hS

/-- Clearing the flag stacks `23`, `28`, `17`, `18`, `19` of the mode-`3` test state leaves the
register state with the YES score on stack `29`. -/
private theorem m3a_prefix_clear_flags (base : Stacks 38) (W m : ℕ) (F : Frame)
    (Ks : List Frame) (cs : List BitString)
    (hbrest : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    List.foldl (fun τ r => Function.update τ r []) (mode3TestSt base W m F Ks cs)
      ([23, 28, 17, 18, 19] : List (Fin 38)) =
      Function.update (regSt base W m F Ks) 29
        (numBits W (F.y + costV (cs.map binVal) F.v' F.r)) := by
  have hR := m3a_prefix_regSt_high base W m F Ks hbrest
  unfold mode3TestSt
  generalize regSt base W m F Ks = R at hR ⊢
  funext j
  fin_cases j <;> simp [hR]

/-- Starting from empty work stacks `17`, `18`, `19`, the scoring phase writes on `17`, `18`, `19`
and `30`; clearing `17` and `18` then leaves only the sum on stack `30`. -/
private theorem m3a_prefix_clear_work (A : Stacks 38) (h17 : A 17 = []) (h18 : A 18 = [])
    (h19 : A 19 = []) (x y X N₀ N₁ : BitString) :
    List.foldl (fun τ r => Function.update τ r [])
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update A 17 x) 18 y) 19 X) 30 N₀) 30 N₁) 19 []) ([17, 18] : List (Fin 38)) =
      Function.update A 30 N₁ := by
  funext j
  fin_cases j <;> simp [h17, h18, h19]

/-- The first half of the successful mode-`3` body: clear the flags, compute the child's NO score
on `30`, and push the unchanged parent frame.  The space used is at most that of the register
state plus the two `W`-bit scores, the code of the parent frame and the allowance of the cost
routine `sCost`, which is `KC` times the size of its input. -/
private theorem m3a_prefix (sCost : Stmt 38) (KC : ℕ)
    (hCost : ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
      σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
      (cs.map binVal).sum < 2 ^ W →
      (∀ j : Fin 38, 19 ≤ j.val → j.val ≠ 29 → σ j = []) →
      Exec sCost σ (Function.update σ 19
        (numBits W (costV (cs.map binVal) (σ 17) (σ 18))))
        (σ.space + KC * ((Stacks.encList cs).length + (σ 17).length +
          (σ 18).length + W + 1)))
    (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) (cs : List BitString)
    (hb2 : base 2 = Stacks.encList cs) (hb3 : (base 3).length = W)
    (hbrest : ∀ j : Fin 38, 5 ≤ j.val → base j = [])
    (hcs : ∀ c ∈ cs, c.length = W) (hsum : (cs.map binVal).sum < 2 ^ W)
    (hno : F.n + costV (cs.map binVal) F.v F.v' < 2 ^ W) :
    Exec (Stmt.seqs (mode3AcceptPrefix sCost)) (mode3TestSt base W m F Ks cs)
      (mode3ParentPushedSt base W m F Ks cs)
      ((regSt base W m F Ks).space + 2 * W +
        2 * (F.v.length + W + W + F.f + F.v'.length + F.r.length) + 6 +
        KC * ((Stacks.encList cs).length + F.v.length + F.v'.length + W + 1)) := by
  generalize hSdef : (regSt base W m F Ks).space + 2 * W +
    2 * (F.v.length + W + W + F.f + F.v'.length + F.r.length) + 6 +
    KC * ((Stacks.encList cs).length + F.v.length + F.v'.length + W + 1) = S
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = costV (cs.map binVal) F.v' F.r := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = costV (cs.map binVal) F.v F.v' := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ τ : Stacks 38, τ = regSt base W m F Ks := ⟨_, rfl⟩
  obtain ⟨σ₀, hσ₀⟩ : ∃ τ : Stacks 38, τ = mode3TestSt base W m F Ks cs := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ τ : Stacks 38, τ = Function.update R 29 (numBits W (F.y + c₁)) :=
    ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ τ : Stacks 38, τ = Function.update A 17 F.v := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ τ : Stacks 38, τ = Function.update A₁ 18 F.v' := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ τ : Stacks 38, τ = Function.update B 19 (numBits W c₂) :=
    ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ τ : Stacks 38, τ = Function.update B₁ 30 (numBits W F.n) :=
    ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ τ : Stacks 38, τ = Function.update B₂ 30 (numBits W (F.n + c₂)) :=
    ⟨_, rfl⟩
  obtain ⟨B₃, hB₃⟩ : ∃ τ : Stacks 38, τ = Function.update C 19 [] := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ τ : Stacks 38, τ = Function.update A 30 (numBits W (F.n + c₂)) :=
    ⟨_, rfl⟩
  have hRh : ∀ j : Fin 38, 17 ≤ j.val → R j = [] := by
    rw [hR]
    exact m3a_prefix_regSt_high base W m F Ks hbrest
  have hRs : R.space = (regSt base W m F Ks).space := by rw [hR]
  -- spaces
  have sσ₀ := m3a_prefix_space_testSt base W m F Ks cs
  rw [← hσ₀] at sσ₀
  have sA := m3a_prefix_space_of_upd hA
  have sA₁ := m3a_prefix_space_of_upd hA₁
  have sB := m3a_prefix_space_of_upd hB
  have sB₁ := m3a_prefix_space_of_upd hB₁
  have sB₂ := m3a_prefix_space_of_upd hB₂
  have sC := m3a_prefix_space_of_upd hC
  have sP := m3a_prefix_space_of_upd hP
  have sB₃ : B₃.space ≤ C.space := by
    rw [hB₃]
    exact m3a_space_clr C 19
  simp only [m3a_numBits_length] at sA sB₁ sB₂ sC sP
  -- step 1: five clears
  have eC1 :
      Exec (Stmt.seqs (([23, 28, 17, 18, 19] : List (Fin 38)).map Stmt.clear)) σ₀ A S := by
    refine Stmt.exec_of_eq ((m3a_clearList [23, 28, 17, 18, 19] σ₀).mono
      (sσ₀.trans (by omega))) ?_
    rw [hσ₀, hA, hR, hc₁]
    exact m3a_prefix_clear_flags base W m F Ks cs hbrest
  -- step 2: copy 11 → 17
  have eA₁ : Exec (Stmt.copy 11 17 20) A A₁ S := by
    rw [hA₁]
    exact m3a_prefix_exec_copy (by decide) (by decide) (by decide) (by simp [hA, hR, regSt])
      (by simp [hA, hRh 17 (by decide)]) (by simp [hA, hRh 20 (by decide)]) (by omega)
  -- step 3: copy 15 → 18
  have eB : Exec (Stmt.copy 15 18 20) A₁ B S := by
    rw [hB]
    exact m3a_prefix_exec_copy (by decide) (by decide) (by decide)
      (by simp [hA₁, hA, hR, regSt]) (by simp [hA₁, hA, hRh 18 (by decide)])
      (by simp [hA₁, hA, hRh 20 (by decide)]) (by omega)
  -- step 4: the cost routine
  have eCost : Exec sCost B B₁ S := by
    have hB17 : B 17 = F.v := by simp [hB, hA₁]
    have hB18 : B 18 = F.v' := by simp [hB]
    have hB2 : B 2 = Stacks.encList cs := by simp [hB, hA₁, hA, hR, regSt, encSt, hb2]
    have hB3 : (B 3).length = W := by simpa [hB, hA₁, hA, hR, regSt, encSt] using hb3
    have hBhigh : ∀ j : Fin 38, 19 ≤ j.val → j.val ≠ 29 → B j = [] := by
      intro j hj hj29
      have hne : ∀ k : Fin 38, k.val < 19 → j ≠ k := fun k hk h => by
        rw [h] at hj
        omega
      have h29 : j ≠ 29 := fun h => hj29 (by simp [h])
      rw [hB, hA₁, hA, Function.update_of_ne (hne 18 (by decide)),
        Function.update_of_ne (hne 17 (by decide)), Function.update_of_ne h29]
      exact hRh j (by omega)
    have e := hCost B cs W hB2 hcs hB3 hsum hBhigh
    rw [hB17, hB18, ← hc₂, ← hB₁] at e
    exact e.mono (by omega)
  -- step 5: copy 13 → 30
  have eB₂ : Exec (Stmt.copy 13 30 20) B₁ B₂ S := by
    rw [hB₂]
    exact m3a_prefix_exec_copy (by decide) (by decide) (by decide)
      (by simp [hB₁, hB, hA₁, hA, hR, regSt])
      (by simp [hB₁, hB, hA₁, hA, hRh 30 (by decide)])
      (by simp [hB₁, hB, hA₁, hA, hRh 20 (by decide)]) (by rw [m3a_numBits_length]; omega)
  -- step 6: addition
  have hc₂lt : c₂ < 2 ^ W := by rw [hc₂]; omega
  have hadd : addBits false (numBits W F.n) (numBits W c₂) = numBits W (F.n + c₂) := by
    rw [addBits_numBits W F.n (numBits W c₂) (m3a_numBits_length W c₂)
      (by rw [binVal_numBits_of_lt W c₂ hc₂lt, hc₂]; exact hno),
      binVal_numBits_of_lt W c₂ hc₂lt]
  have eAdd : Exec (Stmt.addInto 30 19 31 32) B₂ B₃ S := by
    have e := Stmt.exec_addInto (k := 38) (A := (30 : Fin 38)) (B := 19) (Cy := 31) (R := 32)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (σ := B₂)
      (l := numBits W F.n) (m := numBits W c₂)
      (by simp [m3a_numBits_length]) (by simp [hB₂]) (by simp [hB₂, hB₁])
      (by simp [hB₂, hB₁, hB, hA₁, hA, hRh 31 (by decide)])
      (by simp [hB₂, hB₁, hB, hA₁, hA, hRh 32 (by decide)])
    rw [hadd, ← hC, ← hB₃] at e
    exact e.mono (by omega)
  -- step 7: clear 17 and 18
  have eC2 : Exec (Stmt.seqs (([17, 18] : List (Fin 38)).map Stmt.clear)) B₃ P S := by
    refine Stmt.exec_of_eq ((m3a_clearList [17, 18] B₃).mono (by omega)) ?_
    rw [hB₃, hC, hB₂, hB₁, hB, hA₁, hP]
    exact m3a_prefix_clear_work A (by simp [hA, hRh 17 (by decide)])
      (by simp [hA, hRh 18 (by decide)]) (by simp [hA, hRh 19 (by decide)]) _ _ _ _ _
  -- step 8: push the parent
  have ePush : Exec pushRegFrame P (mode3ParentPushedSt base W m F Ks cs) S := by
    have e := m3a_exec_pushRegFrame P F.v (numBits W F.y) (numBits W F.n)
      (List.replicate F.f true) F.v' F.r S
      (by simp [hP, hA, hR, regSt]) (by simp [hP, hA, hR, regSt]) (by simp [hP, hA, hR, regSt])
      (by simp [hP, hA, hR, regSt]) (by simp [hP, hA, hR, regSt]) (by simp [hP, hA, hR, regSt])
      (by simp [hP, hA, hRh 19 (by decide)])
      (by simp only [m3a_numBits_length, List.length_replicate]; omega)
    refine Stmt.exec_of_eq e ?_
    exact m3a_prefix_push_state base W m F Ks cs P (by rw [hP, hA, hR, hc₁, hc₂])
  have hsplit : mode3AcceptPrefix sCost =
      (([23, 28, 17, 18, 19] : List (Fin 38)).map Stmt.clear) ++
        ([Stmt.copy 11 17 20, Stmt.copy 15 18 20, sCost, Stmt.copy 13 30 20,
          Stmt.addInto 30 19 31 32] ++
          ((([17, 18] : List (Fin 38)).map Stmt.clear) ++ [pushRegFrame])) := rfl
  have eMid : Exec (Stmt.seqs [Stmt.copy 11 17 20, Stmt.copy 15 18 20, sCost,
      Stmt.copy 13 30 20, Stmt.addInto 30 19 31 32]) A B₃ S :=
    Stmt.exec_seqs_cons.2 ⟨A₁, eA₁, Stmt.exec_seqs_cons.2 ⟨B, eB, Stmt.exec_seqs_cons.2
      ⟨B₁, eCost, Stmt.exec_seqs_cons.2 ⟨B₂, eB₂, m3a_seqs_single eAdd⟩⟩⟩⟩
  rw [hsplit, ← hσ₀]
  exact m3a_seqs_append _ _ eC1 (m3a_seqs_append _ _ eMid
    (m3a_seqs_append _ _ eC2 (m3a_seqs_single ePush)))

/-- Helper for `m3a_suffix` bounding values in `M`. -/
private lemma m3a_suffix_hMhigh (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (y' n' : ℕ)
    (hbrest : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    ∀ j : Fin 38, 17 ≤ j.val → j ≠ 29 → j ≠ 30 →
      Function.update (Function.update (regSt base W m F (F :: Ks)) 29
      (numBits W y')) 30 (numBits W n') j = [] := by
  intro j hj h29 h30
  fin_cases j <;> (try (norm_num at hj; done)) <;> (try (exact absurd rfl h29)) <;>
    (try (exact absurd rfl h30)) <;> simp [regSt, encSt, hbrest]

/-- Helper for `m3a_suffix` showing equivalence of the cleared registers and `Rc`. -/
private lemma m3a_suffix_hRcEq (base : Stacks 38) (W m : ℕ) (F C : Frame) (Ks : List Frame)
    (y' n' : ℕ)
    (hbrest : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    C = ⟨F.r, y', n', F.f - 1, [], []⟩ →
    List.foldl (fun τ r => Function.update τ r [])
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (regSt base W m F (F :: Ks)) 29
      (numBits W y')) 30 (numBits W n')) 11 []) 11 F.r) 12 []) 12 (numBits W y')) 13 []) 13
      (numBits W n')) 14 (List.replicate (F.f - 1) true)) 15 []) 16 [])
      ([17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] :
        List (Fin 38)) = regSt base W m C (F :: Ks) := by
  intro hC
  subst hC
  funext j
  fin_cases j <;>
    simp [regSt, encSt, hbrest, Frame.fields, Stacks.encList]

/-- Helper for `m3a_suffix` showing equivalence of cleared registers to `encSt`. -/
private lemma m3a_suffix_hFin (base : Stacks 38) (W m : ℕ) (F C : Frame) (Ks : List Frame)
    (y' n' : ℕ)
    (hbrest : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    C = ⟨F.r, y', n', F.f - 1, [], []⟩ →
    List.foldl (fun τ r => Function.update τ r [])
      (List.foldl (fun τ r => Function.update τ r [])
        (Function.update (regSt base W m C (F :: Ks)) 8
          (Stacks.encList [F.r, numBits W y', numBits W n', List.replicate (F.f - 1) true, [], []]
          ++
            regSt base W m C (F :: Ks) 8))
        ([11, 12, 13, 14, 15, 16] : List (Fin 38)))
      ([17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] :
        List (Fin 38)) =
      encSt base W m (0, C :: F :: Ks) := by
  intro hC
  subst hC
  funext j
  fin_cases j <;>
    simp [regSt, encSt, hbrest, Frame.fields, Stacks.encList]

/-- The second half of the successful mode-`3` body: install the child's fields in the
registers, clear the scratch, push the child frame and enter mode `0`.  The space used is at
most that of the midpoint state plus the child's fields and the code of the child frame. -/
private theorem m3a_suffix (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (cs : List BitString) (hbrest : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    Exec (Stmt.seqs mode3AcceptSuffix) (mode3ParentPushedSt base W m F Ks cs)
      (encSt base W m (0, ⟨F.r, F.y + costV (cs.map binVal) F.v' F.r,
        F.n + costV (cs.map binVal) F.v F.v', F.f - 1, [], []⟩ :: F :: Ks))
      ((mode3ParentPushedSt base W m F Ks cs).space + F.r.length + 2 * W +
        2 * (F.r.length + W + W + F.f) + 6) := by
  generalize hSdef : (mode3ParentPushedSt base W m F Ks cs).space + F.r.length + 2 * W +
    2 * (F.r.length + W + W + F.f) + 6 = S
  obtain ⟨y', hy'⟩ : ∃ c, c = F.y + costV (cs.map binVal) F.v' F.r := ⟨_, rfl⟩
  obtain ⟨n', hn'⟩ : ∃ c, c = F.n + costV (cs.map binVal) F.v F.v' := ⟨_, rfl⟩
  rw [← hy', ← hn']
  obtain ⟨M, hM⟩ : ∃ τ : Stacks 38, τ = mode3ParentPushedSt base W m F Ks cs := ⟨_, rfl⟩
  rw [← hM] at hSdef ⊢
  have hMv : M = Function.update (Function.update (regSt base W m F (F :: Ks)) 29
      (numBits W y')) 30 (numBits W n') := by
    rw [hM, hy', hn']; rfl
  have hMhigh : ∀ j : Fin 38, 17 ≤ j.val → j ≠ 29 → j ≠ 30 → M j = [] := by
    intro j hj h29 h30
    rw [hMv]
    exact m3a_suffix_hMhigh base W m F Ks y' n' hbrest j hj h29 h30
  obtain ⟨u₁, hu₁⟩ : ∃ τ : Stacks 38, τ = Function.update M 11 [] := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ τ : Stacks 38, τ = Function.update u₁ 11 F.r := ⟨_, rfl⟩
  obtain ⟨u₃, hu₃⟩ : ∃ τ : Stacks 38, τ = Function.update u₂ 12 [] := ⟨_, rfl⟩
  obtain ⟨u₄, hu₄⟩ : ∃ τ : Stacks 38, τ = Function.update u₃ 12 (numBits W y') :=
    ⟨_, rfl⟩
  obtain ⟨u₅, hu₅⟩ : ∃ τ : Stacks 38, τ = Function.update u₄ 13 [] := ⟨_, rfl⟩
  obtain ⟨u₆, hu₆⟩ : ∃ τ : Stacks 38, τ = Function.update u₅ 13 (numBits W n') :=
    ⟨_, rfl⟩
  obtain ⟨u₇, hu₇⟩ : ∃ τ : Stacks 38,
      τ = Function.update u₆ 14 (List.replicate (F.f - 1) true) := ⟨_, rfl⟩
  obtain ⟨u₈, hu₈⟩ : ∃ τ : Stacks 38, τ = Function.update u₇ 15 [] := ⟨_, rfl⟩
  obtain ⟨u₉, hu₉⟩ : ∃ τ : Stacks 38, τ = Function.update u₈ 16 [] := ⟨_, rfl⟩
  let C : Frame := ⟨F.r, y', n', F.f - 1, [], []⟩
  obtain ⟨Rc, hRc⟩ : ∃ τ : Stacks 38, τ = regSt base W m C (F :: Ks) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ τ : Stacks 38, τ = Function.update Rc 8
      (Stacks.encList [F.r, numBits W y', numBits W n', List.replicate (F.f - 1) true, [], []] ++
      Rc 8) := ⟨_, rfl⟩
  -- spaces
  have s₁ : u₁.space ≤ M.space := by rw [hu₁]; exact m3a_space_clr M 11
  have s₂ : u₂.space ≤ u₁.space + F.r.length := by
    rw [hu₂]; exact m3a_space_upd u₁ 11 F.r
  have s₃ : u₃.space ≤ u₂.space := by rw [hu₃]; exact m3a_space_clr u₂ 12
  have s₄ : u₄.space ≤ u₃.space + W := by
    have h := m3a_space_upd u₃ 12 (numBits W y')
    rwa [m3a_numBits_length, ← hu₄] at h
  have s₅ : u₅.space ≤ u₄.space := by rw [hu₅]; exact m3a_space_clr u₄ 13
  have s₆ : u₆.space ≤ u₅.space + W := by
    have h := m3a_space_upd u₅ 13 (numBits W n')
    rwa [m3a_numBits_length, ← hu₆] at h
  have h₆14 : u₆ 14 = List.replicate F.f true := by
    simp [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁, hMv, regSt]
  have s₇ : u₇.space ≤ u₆.space := by
    rw [hu₇]
    exact Stacks.space_update_le u₆ 14 _ (by rw [h₆14]; simp)
  have s₈ : u₈.space ≤ u₇.space := by rw [hu₈]; exact m3a_space_clr u₇ 15
  have s₉ : u₉.space ≤ u₈.space := by rw [hu₉]; exact m3a_space_clr u₈ 16
  -- the steps
  have e₁ : Exec (Stmt.clear 11) M u₁ S := by
    rw [hu₁]; exact (Stmt.exec_clear 11 (M 11) M rfl).mono (by omega)
  have e₂ : Exec (Stmt.copy 16 11 20) u₁ u₂ S := by
    have e := Stmt.exec_copy (k := 38) (r := (16 : Fin 38)) (r' := 11) (t := 20)
      (by decide) (by decide) (by decide) (σ := u₁)
      (by simp [hu₁, hMhigh 20 (by decide) (by decide) (by decide)])
    have h16 : u₁ 16 = F.r := by simp [hu₁, hMv, regSt]
    have h11 : u₁ 11 = [] := by simp [hu₁]
    rw [h16, h11, List.append_nil, ← hu₂] at e
    exact e.mono (by omega)
  have e₃ : Exec (Stmt.clear 12) u₂ u₃ S := by
    rw [hu₃]; exact (Stmt.exec_clear 12 (u₂ 12) u₂ rfl).mono (by omega)
  have e₄ : Exec (Stmt.copy 29 12 20) u₃ u₄ S := by
    have e := Stmt.exec_copy (k := 38) (r := (29 : Fin 38)) (r' := 12) (t := 20)
      (by decide) (by decide) (by decide) (σ := u₃)
      (by simp [hu₃, hu₂, hu₁, hMhigh 20 (by decide) (by decide) (by decide)])
    have h29 : u₃ 29 = numBits W y' := by simp [hu₃, hu₂, hu₁, hMv]
    have h12 : u₃ 12 = [] := by simp [hu₃]
    rw [h29, h12, List.append_nil, ← hu₄, m3a_numBits_length] at e
    exact e.mono (by omega)
  have e₅ : Exec (Stmt.clear 13) u₄ u₅ S := by
    rw [hu₅]; exact (Stmt.exec_clear 13 (u₄ 13) u₄ rfl).mono (by omega)
  have e₆ : Exec (Stmt.copy 30 13 20) u₅ u₆ S := by
    have e := Stmt.exec_copy (k := 38) (r := (30 : Fin 38)) (r' := 13) (t := 20)
      (by decide) (by decide) (by decide) (σ := u₅)
      (by simp [hu₅, hu₄, hu₃, hu₂, hu₁, hMhigh 20 (by decide) (by decide) (by decide)])
    have h30 : u₅ 30 = numBits W n' := by simp [hu₅, hu₄, hu₃, hu₂, hu₁, hMv]
    have h13 : u₅ 13 = [] := by simp [hu₅]
    rw [h30, h13, List.append_nil, ← hu₆, m3a_numBits_length] at e
    exact e.mono (by omega)
  have e₇ : Exec (.pop 14) u₆ u₇ S := by
    have e := Exec.pop (r := (14 : Fin 38)) (σ := u₆) (S := S) (by omega)
    rw [h₆14, List.tail_replicate, ← hu₇] at e
    exact e
  have e₈ : Exec (Stmt.clear 15) u₇ u₈ S := by
    rw [hu₈]; exact (Stmt.exec_clear 15 (u₇ 15) u₇ rfl).mono (by omega)
  have e₉ : Exec (Stmt.clear 16) u₈ u₉ S := by
    rw [hu₉]; exact (Stmt.exec_clear 16 (u₈ 16) u₈ rfl).mono (by omega)
  -- clear the mode scratch
  have hcms : clearModeScratch = Stmt.seqs (([17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30, 31, 32, 33, 34, 35, 36, 37] : List (Fin 38)).map Stmt.clear) := rfl
  have eScr₀ := m3a_clearList [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30, 31, 32, 33, 34, 35, 36, 37] u₉
  have hRcEq : List.foldl (fun τ r => Function.update τ r []) u₉ ([17, 18, 19, 20, 21, 22, 23,
      24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] : List (Fin 38)) = Rc := by
    have hRc' : Rc = regSt base W m C (F :: Ks) := by simp [hRc]
    rw [hRc']
    rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁, hMv]
    exact m3a_suffix_hRcEq base W m F C Ks y' n' hbrest rfl
  rw [hRcEq] at eScr₀
  have sRc : Rc.space ≤ u₉.space := eScr₀.space_le.2
  have eScr : Exec clearModeScratch u₉ Rc S := by
    rw [hcms]; exact eScr₀.mono (by omega)
  -- push the child
  have ePush : Exec pushRegFrame Rc V S := by
    have e := m3a_exec_pushRegFrame Rc F.r (numBits W y') (numBits W n')
      (List.replicate (F.f - 1) true) [] [] S
      (by simp [hRc, C, regSt]) (by simp [hRc, C, regSt]) (by simp [hRc, C, regSt])
      (by simp [hRc, C, regSt]) (by simp [hRc, C, regSt]) (by simp [hRc, C, regSt])
      (by simp [hRc, regSt, encSt, hbrest])
      (by simp only [m3a_numBits_length, List.length_replicate, List.length_nil]; omega)
    rwa [← hV] at e
  -- clear the registers and the scratch, enter mode `0`
  have hcmr : clearModeRegisters = Stmt.seqs ((([11, 12, 13, 14, 15, 16] : List (Fin 38)).map
      Stmt.clear) ++ [clearModeScratch]) := rfl
  have eR₁ := m3a_clearList [11, 12, 13, 14, 15, 16] V
  obtain ⟨V₁, hV₁⟩ : ∃ τ : Stacks 38,
      τ = List.foldl (fun τ r => Function.update τ r []) V
        ([11, 12, 13, 14, 15, 16] : List (Fin 38)) := ⟨_, rfl⟩
  rw [← hV₁] at eR₁
  have eR₂ := m3a_clearList [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30, 31, 32, 33, 34, 35, 36, 37] V₁
  have hFin : List.foldl (fun τ r => Function.update τ r []) V₁ ([17, 18, 19, 20, 21, 22, 23,
      24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] : List (Fin 38)) =
      encSt base W m (0, C :: F :: Ks) := by
    rw [hV₁, hV, hRc]
    exact m3a_suffix_hFin base W m F C Ks y' n' hbrest rfl
  rw [hFin] at eR₂
  have sV : V.space ≤ S := ePush.space_le.2
  have eRegs : Exec clearModeRegisters V (encSt base W m (0, C :: F :: Ks)) S := by
    rw [hcmr, hcms]
    exact m3a_seqs_append _ _ (eR₁.mono sV)
      (m3a_seqs_single (eR₂.mono (eR₁.space_le.2.trans sV)))
  have eMode : Exec (putMode 0) (encSt base W m (0, C :: F :: Ks))
      (encSt base W m (0, C :: F :: Ks)) S := by
    unfold putMode
    simp only [List.replicate_zero, Stmt.pushList]
    exact Exec.skip eRegs.space_le.2
  have hsplit : mode3AcceptSuffix = [Stmt.clear 11, Stmt.copy 16 11 20, Stmt.clear 12,
      Stmt.copy 29 12 20, Stmt.clear 13, Stmt.copy 30 13 20, .pop 14, Stmt.clear 15,
      Stmt.clear 16] ++ [clearModeScratch, pushRegFrame, clearModeRegisters, putMode 0] := rfl
  rw [hsplit]
  refine m3a_seqs_append _ _ ?_ ?_ (μ := u₉)
  · rw [Stmt.exec_seqs_cons]; refine ⟨u₁, e₁, ?_⟩
    rw [Stmt.exec_seqs_cons]; refine ⟨u₂, e₂, ?_⟩
    rw [Stmt.exec_seqs_cons]; refine ⟨u₃, e₃, ?_⟩
    rw [Stmt.exec_seqs_cons]; refine ⟨u₄, e₄, ?_⟩
    rw [Stmt.exec_seqs_cons]; refine ⟨u₅, e₅, ?_⟩
    rw [Stmt.exec_seqs_cons]; refine ⟨u₆, e₆, ?_⟩
    rw [Stmt.exec_seqs_cons]; refine ⟨u₇, e₇, ?_⟩
    rw [Stmt.exec_seqs_cons]; refine ⟨u₈, e₈, ?_⟩
    exact m3a_seqs_single e₉
  · rw [Stmt.exec_seqs_cons]; refine ⟨Rc, eScr, ?_⟩
    rw [Stmt.exec_seqs_cons]; refine ⟨V, ePush, ?_⟩
    rw [Stmt.exec_seqs_cons]; refine ⟨_, eRegs, ?_⟩
    exact m3a_seqs_single eMode

/-- Installing the unary mode `i` on the empty mode stack of the mode-`0` state gives the
mode-`i` state. -/
private theorem m3a_body_encSt_mode (base : Stacks 38) (W m i : ℕ) (Fs : List Frame) :
    Function.update (encSt base W m (0, Fs)) 9 (List.replicate i true) =
      encSt base W m (i, Fs) := by
  simp only [encSt]
  rw [Function.update_comm (by decide : (10 : Fin 38) ≠ 9), Function.update_idem]

/-- The mode-`0` state is no larger than the mode-`3` state: the mode stack is empty in the
first and holds three bits in the second. -/
private theorem m3a_body_encSt_space (base : Stacks 38) (W m : ℕ) (Fs : List Frame) :
    (encSt base W m (0, Fs)).space ≤ (encSt base W m (3, Fs)).space := by
  have h9 : encSt base W m (0, Fs) 9 = [] := by simp [encSt]
  have h := Stacks.space_update (encSt base W m (0, Fs)) 9 (List.replicate 3 true)
  rw [m3a_body_encSt_mode, h9] at h
  simp only [List.length_replicate, List.length_nil] at h
  omega

/-- The midpoint of the successful branch takes at most the space of the register state plus the
length of the parent frame's code prepended to stack `8` and the two scores on stacks `29` and
`30`. -/
private theorem m3a_body_space_mid (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (cs : List BitString) :
    (mode3ParentPushedSt base W m F Ks cs).space ≤
      (regSt base W m F Ks).space + 2 * (F.v.length + W + W + F.f + F.v'.length +
        F.r.length) + 6 + 2 * W := by
  have h8 := m3a_space_push8 (regSt base W m F Ks) (Stacks.encList (Frame.fields W F))
  rw [← m3a_prefix_regSt_cons base W m F Ks] at h8
  have hlf : (Stacks.encList (Frame.fields W F)).length =
      2 * (F.v.length + W + W + F.f + F.v'.length + F.r.length) + 6 := by
    simp only [Stacks.length_encList, Frame.fields, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, m3a_numBits_length, List.length_replicate]
    omega
  have h1 := m3a_space_upd (regSt base W m F (F :: Ks)) 29
    (numBits W (F.y + costV (cs.map binVal) F.v' F.r))
  have h2 := m3a_space_upd (Function.update (regSt base W m F (F :: Ks)) 29
    (numBits W (F.y + costV (cs.map binVal) F.v' F.r))) 30
    (numBits W (F.n + costV (cs.map binVal) F.v F.v'))
  rw [m3a_numBits_length] at h1 h2
  have he : mode3ParentPushedSt base W m F Ks cs = Function.update (Function.update
      (regSt base W m F (F :: Ks)) 29 (numBits W (F.y + costV (cs.map binVal) F.v' F.r))) 30
      (numBits W (F.n + costV (cs.map binVal) F.v F.v')) := rfl
  rw [he]
  omega

/-- Execute the successful body in its two semantic phases.  For `mode3AcceptPrefix`, clear the
flags, compute the cost of `F.v → F.v'`, add it to `F.n`, and use six
`QEnum.exec_pushCode` applications to reach `mode3ParentPushedSt`.  For `mode3AcceptSuffix`,
install the child fields, decrement the fuel, clear scratch, and use six further push-code
executions before clearing the registers and installing mode `0`.  The copy/clear/pop contracts,
`Stmt.exec_addInto`, `hNoOverflow`, and `frameSize_le_five_square` give the displayed common
quadratic allowance. -/
private theorem exec_mode3AcceptBody (sCost : Stmt 38) (KC : ℕ)
    (hCost : ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
      σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
      (cs.map binVal).sum < 2 ^ W →
      (∀ j : Fin 38, 19 ≤ j.val → j.val ≠ 29 → σ j = []) →
      Exec sCost σ (Function.update σ 19
        (numBits W (costV (cs.map binVal) (σ 17) (σ 18))))
        (σ.space + KC * ((Stacks.encList cs).length + (σ 17).length +
          (σ 18).length + W + 1))) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
      (F : Frame) (Ks : List Frame), BaseOK base LX cs eb → cs.length = LX.length →
      (∀ c ∈ cs, c.length = W) → eb.length = W →
      binVal eb + (cs.map binVal).sum < 2 ^ W →
      FrameOK LX.length (binVal eb) F →
      F.n + costV (cs.map binVal) F.v F.v' < 2 ^ W →
      isSub F.v' F.r = true →
      decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal eb) = true →
      Exec (Stmt.seqs (mode3AcceptPrefix sCost ++ mode3AcceptSuffix))
        (mode3TestSt base W LX.length F Ks cs)
        (encSt base W LX.length
          (0, ⟨F.r, F.y + costV (cs.map binVal) F.v' F.r,
            F.n + costV (cs.map binVal) F.v F.v', F.f - 1, [], []⟩ :: F :: Ks))
        ((encSt base W LX.length (3, F :: Ks)).space +
          K * (LX.length + W + 1) ^ 2) := by
  refine ⟨5 * KC + 100, ?_⟩
  intro base LX cs eb W F Ks hbase hlen hcs heb hsum hF hno _hsub _hle
  rcases hbase with ⟨_hb1, hb2, hb3, hbrest⟩
  obtain ⟨m, hm⟩ : ∃ n, n = LX.length := ⟨_, rfl⟩
  rw [← hm] at hF ⊢
  obtain ⟨Q, hQ⟩ : ∃ n, n = (m + W + 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ n, n = (encSt base W m (3, F :: Ks)).space := ⟨_, rfl⟩
  obtain ⟨KQ, hKQ⟩ : ∃ n, n = KC * Q := ⟨_, rfl⟩
  have hS : (encSt base W m (3, F :: Ks)).space + (5 * KC + 100) * (m + W + 1) ^ 2 =
      E + 5 * KQ + 100 * Q := by
    rw [hE, hKQ, hQ]; ring
  rw [hS]
  obtain ⟨hv, hy, hn, hf, hv', hr⟩ := hF
  have hmQ : m + W + 1 ≤ Q := by
    rw [hQ]
    exact Nat.le_self_pow (by norm_num) _
  have hlenc : (Stacks.encList cs).length ≤ 2 * Q := by
    have h₀ : (Stacks.encList cs).length ≤ cs.length * (2 * W + 1) :=
      QEnum.length_encList_le W cs (fun z hz => by simp [hcs z hz])
    rw [hlen, ← hm] at h₀
    refine h₀.trans ?_
    rw [hQ]
    calc m * (2 * W + 1) ≤ (m + W + 1) * (2 * (m + W + 1)) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (m + W + 1) ^ 2 := by ring
  have hcost : KC * ((Stacks.encList cs).length + F.v.length + F.v'.length + W + 1) ≤
      5 * KQ := by
    have h : (Stacks.encList cs).length + F.v.length + F.v'.length + W + 1 ≤ 5 * Q := by
      omega
    calc _ ≤ KC * (5 * Q) := Nat.mul_le_mul_left KC h
      _ = 5 * KQ := by rw [hKQ]; ring
  -- the register state and the encoded state
  have hE0 : (encSt base W m (0, F :: Ks)).space ≤ E := by
    rw [hE]
    exact m3a_body_encSt_space base W m (F :: Ks)
  have hfs := pushFrameEncode_space base W m F Ks
  simp only [m3a_numBits_length, List.length_replicate] at hfs
  have hframe : frameSize W F ≤ 5 * Q := by
    have h := frameSize_le_five_square m (binVal eb) W F ⟨hv, hy, hn, hf, hv', hr⟩
    rwa [← hQ] at h
  have hR : (regSt base W m F Ks).space + 2 * (F.v.length + W + W + F.f + F.v'.length +
      F.r.length) + 6 ≤ E + 40 * Q := by
    calc _ ≤ (encSt base W m (0, F :: Ks)).space + 8 * frameSize W F := hfs
      _ ≤ E + 8 * (5 * Q) := Nat.add_le_add hE0 (Nat.mul_le_mul_left 8 hframe)
      _ = E + 40 * Q := by ring
  -- the prefix
  have hb3' : (base 3).length = W := by rw [hb3, heb]
  have hsum' : (cs.map binVal).sum < 2 ^ W := by omega
  have ePre := (m3a_prefix sCost KC hCost base W m F Ks cs hb2 hb3' hbrest hcs hsum' hno).mono
    (S' := E + 5 * KQ + 100 * Q) (by omega)
  -- the space of the midpoint
  have hMid := m3a_body_space_mid base W m F Ks cs
  have eSuf := (m3a_suffix base W m F Ks cs hbrest).mono
    (S' := E + 5 * KQ + 100 * Q) (by omega)
  exact m3a_seqs_append _ _ ePre eSuf

/-- Select the true/true leaf of `mode3Commit`.  Both `caseBit`s only inspect their singleton
flag stacks, so the selected program is the concatenation of the two successful phases. -/
private theorem exec_mode3Commit_selectAccept (sPush sCost : Stmt 38)
    (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) (cs : List BitString)
    (hsub : isSub F.v' F.r = true)
    (hle : decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal (base 3)) = true)
    (τ : Stacks 38) (S : ℕ)
    (e : Exec (Stmt.seqs (mode3AcceptPrefix sCost ++ mode3AcceptSuffix))
      (mode3TestSt base W m F Ks cs) τ S) :
    Exec (mode3Commit sPush sCost) (mode3TestSt base W m F Ks cs) τ S := by
  have h23 : mode3TestSt base W m F Ks cs 23 = true :: [] := by
    simp [mode3TestSt, hsub]
  have h28 : mode3TestSt base W m F Ks cs 28 = true :: [] := by
    simp [mode3TestSt, hle]
  rw [mode3Commit, Stmt.exec_caseBit h23, Stmt.exec_caseBit h28]
  simpa [mode3AcceptPrefix, mode3AcceptSuffix] using e

/-- If both tests succeed, compute the child's NO score, encode the parent frame, replace the six
registers by the child fields, and encode the child frame.  A proof follows the displayed
`mode3Commit` sequence: use `hCost`, `Stmt.exec_addInto`, the copy/clear/pop contracts, and six
`QEnum.exec_pushCode` applications for each call of `pushRegFrame`, then identify the result with
the successful mode-`3` clause of `mstep`. -/
private theorem exec_mode3Commit_accept (sPush sCost : Stmt 38) (KC : ℕ)
    (hCost : ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
      σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
      (cs.map binVal).sum < 2 ^ W →
      (∀ j : Fin 38, 19 ≤ j.val → j.val ≠ 29 → σ j = []) →
      Exec sCost σ (Function.update σ 19
        (numBits W (costV (cs.map binVal) (σ 17) (σ 18))))
        (σ.space + KC * ((Stacks.encList cs).length + (σ 17).length +
          (σ 18).length + W + 1))) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
      (F : Frame) (Ks : List Frame), BaseOK base LX cs eb →
      cs.length = LX.length → (∀ c ∈ cs, c.length = W) → eb.length = W →
      binVal eb + (cs.map binVal).sum < 2 ^ W →
      FrameOK LX.length (binVal eb) F → isSub F.v' F.r = true →
      decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal eb) = true →
      Exec (mode3Commit sPush sCost) (mode3TestSt base W LX.length F Ks cs)
        (encSt base W LX.length
          (0, ⟨F.r, F.y + costV (cs.map binVal) F.v' F.r,
            F.n + costV (cs.map binVal) F.v F.v', F.f - 1, [], []⟩ :: F :: Ks))
        ((encSt base W LX.length (3, F :: Ks)).space +
          K * (LX.length + W + 1) ^ 2) := by
  obtain ⟨K, hbody⟩ := exec_mode3AcceptBody sCost KC hCost
  refine ⟨K, ?_⟩
  intro base LX cs eb W F Ks hbase hlen hcs heb hsum hF hsub hle
  have hno := mode3_accept_noScore_lt cs eb W LX.length F hsum hF
  have ebod := hbody base LX cs eb W F Ks hbase hlen hcs heb hsum hF hno hsub hle
  exact exec_mode3Commit_selectAccept sPush sCost base W LX.length F Ks cs hsub
    (by simpa [hbase.2.2.1] using hle) _ _ ebod

/-- Split the two test flags, then clear `23` and `28` explicitly (`caseBit` only reads).
The false cases use the push-frame contract; the true case uses
`exists_costVStmt`, arithmetic primitives, and six applications of `QEnum.exec_pushCode` per
frame to realize the child/parent stack prescribed by `mstep`. -/
theorem exec_mode3Commit (sPush sCost : Stmt 38) (KP KC : ℕ)
    (hPush : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPush (regSt base W m F Ks)
        (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        ((encSt base W m (0, F :: Ks)).space + KP * frameSize W F))
    (hCost : ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
      σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
      (cs.map binVal).sum < 2 ^ W →
      (∀ j : Fin 38, 19 ≤ j.val → j.val ≠ 29 → σ j = []) →
      Exec sCost σ (Function.update σ 19
        (numBits W (costV (cs.map binVal) (σ 17) (σ 18))))
        (σ.space + KC * ((Stacks.encList cs).length + (σ 17).length +
          (σ 18).length + W + 1))) :
    ∃ K : ℕ, ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
      (F : Frame) (Ks : List Frame) (out : BitString → Bool), BaseOK base LX cs eb →
      cs.length = LX.length → (∀ c ∈ cs, c.length = W) → eb.length = W →
      binVal eb + (cs.map binVal).sum < 2 ^ W → FrameOK LX.length (binVal eb) F →
      Exec (mode3Commit sPush sCost) (mode3TestSt base W LX.length F Ks cs)
        (encSt base W LX.length (mstep LX.length (costV (cs.map binVal)) (binVal eb) out
          (3, F :: Ks)))
        ((encSt base W LX.length (3, F :: Ks)).space + K * (LX.length + W + 1) ^ 2) := by
  obtain ⟨KnotSub, hnotSub⟩ := exec_mode3Commit_notSub sPush sCost KP hPush
  obtain ⟨Kover, hover⟩ := exec_mode3Commit_overBudget sPush sCost KP hPush
  obtain ⟨Kaccept, haccept⟩ := exec_mode3Commit_accept sPush sCost KC hCost
  refine ⟨KnotSub + Kover + Kaccept, ?_⟩
  intro base LX cs eb W F Ks out hbase hlen hcs heb hsum hF
  cases hsub : isSub F.v' F.r with
  | false =>
      have e := hnotSub base LX cs eb W F Ks hbase hF hsub
      have hK : KnotSub ≤ KnotSub + Kover + Kaccept := by omega
      have hmul := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2) hK
      have e' := e.mono (Nat.add_le_add_left hmul _)
      simpa [mstep, hsub] using e'
  | true =>
      cases hle : decide (F.y + costV (cs.map binVal) F.v' F.r ≤ binVal eb) with
      | false =>
          have e := hover base LX cs eb W F Ks hbase hF hsub hle
          have hK : Kover ≤ KnotSub + Kover + Kaccept := by omega
          have hmul := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2) hK
          have e' := e.mono (Nat.add_le_add_left hmul _)
          simpa [mstep, hsub, hle] using e'
      | true =>
          have e := haccept base LX cs eb W F Ks hbase hlen hcs heb hsum hF hsub hle
          have hK : Kaccept ≤ KnotSub + Kover + Kaccept := by omega
          have hmul := Nat.mul_le_mul_right ((LX.length + W + 1) ^ 2) hK
          have e' := e.mono (Nat.add_le_add_left hmul _)
          simpa [mstep, hsub, hle] using e'

/-- **Sub-contract: mode `3`, check the YES answer** (remaining). -/
theorem exists_mode3Stmt : ∃ (s : Stmt 38) (K : ℕ), ModeSpec 3 s K := by
  obtain ⟨sPop, KPop, hPop⟩ := exists_popFrameStmt
  obtain ⟨sPush, KPush, hPush⟩ := exists_pushFrameStmt
  obtain ⟨sCostT, KCostT, hCostT⟩ := exists_costVStmt_except23
  obtain ⟨sCostC, KCostC, hCostC⟩ := exists_costVStmt_except29
  obtain ⟨sSub, KSub, hSub⟩ := exists_isSubStmt
  obtain ⟨KT, hTests⟩ := exec_mode3Tests sCostT sSub KCostT KSub hCostT hSub
  obtain ⟨KC, hCommit⟩ := exec_mode3Commit sPush sCostC KPush KCostC hPush hCostC
  refine ⟨.seq sPop (.seq (mode3Tests sCostT sSub) (mode3Commit sPush sCostC)),
    5 * KPop + KT + KC, ?_⟩
  intro base LX cs eb W F Ks out hbase hlen hcs heb hsum hF
  rcases hbase with ⟨hb1, hb2, hb3, hbrest⟩
  have ep := hPop base W LX.length 3 F Ks hbrest
  have et := hTests base LX cs eb W F Ks ⟨hb1, hb2, hb3, hbrest⟩ hlen hcs heb hsum hF
  have ec := hCommit base LX cs eb W F Ks out ⟨hb1, hb2, hb3, hbrest⟩ hlen hcs heb hsum hF
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
