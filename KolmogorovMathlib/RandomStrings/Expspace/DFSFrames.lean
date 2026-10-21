/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSMachine

/-!
# The depth-first search: coding frames on stacks

The coding of the search state on the 38-stack layout (`DFS.encSt`, `DFS.regSt`,
`DFS.frameSize`) and the routines that pop a frame into the registers and push the registers back
as a frame (`DFS.exists_popFrameStmt`, `DFS.exists_pushFrameStmt`).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- `encSt base W m st` is the coding of the search state `st = (mode, frames)` on the `38`
stacks: the frames, field by field with width `W`, on `8`, the mode in unary on `9`, the zero
vector of width `m` on `10`, and everything else as in `base` (`1` board, `2` costs, `3` budget,
`0` and `4` private, `5`–`7` and `11`–`37` empty). -/
def encSt (base : Stacks 38) (W m : ℕ) (st : ℕ × List Frame) : Stacks 38 :=
  Function.update (Function.update (Function.update base 8
    (Stacks.encList (st.2.flatMap (Frame.fields W)))) 9 (List.replicate st.1 true)) 10
    (List.replicate m false)

/-- The base contents: stack `1` holds the coded board `LX`, stack `2` the coded costs `cs`,
stack `3` the budget `eb`, and the stacks `5`–`37` are empty. -/
def BaseOK (base : Stacks 38) (LX cs : List BitString) (eb : BitString) : Prop :=
  base 1 = Stacks.encList LX ∧ base 2 = Stacks.encList cs ∧ base 3 = eb ∧
    ∀ j : Fin 38, 5 ≤ j.val → base j = []

/-- The register state after popping the top frame `F`: its fields are in the registers
`11`–`16` (`F.v`, the `W`-bit codes of `F.y` and `F.n`, `F.f` in unary, `F.v'` and `F.r`), the
remaining frames `K` are coded on `8` as in `encSt base W m (0, K)`, and the mode stack `9` is
empty. -/
def regSt (base : Stacks 38) (W m : ℕ) (F : Frame) (K : List Frame) : Stacks 38 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (encSt base W m (0, K)) 9 []) 11 F.v) 12
      (numBits W F.y)) 13 (numBits W F.n)) 14 (List.replicate F.f true)) 15 F.v') 16 F.r

/-- The size of the frame `F` for the width `W`: the lengths of its work strings `F.v`, `F.v'` and
`F.r`, its fuel `F.f`, the width `W`, and one. -/
def frameSize (W : ℕ) (F : Frame) : ℕ := F.v.length + F.v'.length + F.r.length + F.f + W + 1

/-- Decode the six fields at the head of stack `8`, reversing each decoded work string onto its
register.  Stack `18` retains the reversed self-delimiting codes until the cleanup phase. -/
def popFrameDecodeStmt : Stmt 38 :=
  Stmt.seqs [Stmt.decodeOne 8 17 18, Stmt.moveAll 17 11,
    Stmt.decodeOne 8 17 18, Stmt.moveAll 17 12,
    Stmt.decodeOne 8 17 18, Stmt.moveAll 17 13,
    Stmt.decodeOne 8 17 18, Stmt.moveAll 17 14,
    Stmt.decodeOne 8 17 18, Stmt.moveAll 17 15,
    Stmt.decodeOne 8 17 18, Stmt.moveAll 17 16]

/-- The concrete pop-frame routine decodes all fields and then discards the saved encodings. -/
def popFrameStmt : Stmt 38 := .seq popFrameDecodeStmt (Stmt.clear 18)

/-- The stack state after the six decoding phases of `popFrameDecodeStmt` run from `σ`: stack `8`
holds `rest`, the registers `11`–`16` hold `z₁, …, z₆`, stack `17` is empty and stack `18`
holds the reversed code `(Stacks.encList [z₁, …, z₆]).reverse` of the six strings. -/
def popFrameMid (σ : Stacks 38) (rest z₁ z₂ z₃ z₄ z₅ z₆ : BitString) : Stacks 38 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update σ 8 rest) 11 z₁) 12 z₂)
      13 z₃) 14 z₄) 15 z₅) 16 z₆) 17 []) 18
      (Stacks.encList [z₁, z₂, z₃, z₄, z₅, z₆]).reverse

/-- One decode-and-move phase.  If stack `8` starts with the code of `z` followed by `rest`, the
routines `Stmt.decodeOne 8 17 18` and `Stmt.moveAll 17 D` run one after the other within
`σ.space + z.length` and leave `rest` on stack `8`, `z` in the register `D`, stack `17` empty, and
the reversed code of `z` prepended to stack `18`. -/
private theorem exec_popFrameDecodeMove (σ : Stacks 38) (z rest : BitString) (D : Fin 38)
    (hD8 : D ≠ 8) (hD17 : D ≠ 17) (hD18 : D ≠ 18)
    (h8 : σ 8 = Stacks.encStr z ++ rest) (h17 : σ 17 = []) (hD : σ D = []) :
    ∃ τ, Exec (Stmt.decodeOne 8 17 18) σ τ (σ.space + z.length) ∧
      Exec (Stmt.moveAll 17 D) τ
        (Function.update (Function.update (Function.update (Function.update σ 8 rest) D z)
          17 []) 18 ((Stacks.encStr z).reverse ++ σ 18)) (σ.space + z.length) := by
  have e1 := Stmt.exec_decodeOne (by decide : (8 : Fin 38) ≠ 17)
    (by decide : (8 : Fin 38) ≠ 18) (by decide : (17 : Fin 38) ≠ 18) h8
  let τ := Function.update (Function.update (Function.update σ 8 rest) 17
    (z.reverse ++ σ 17)) 18 ((Stacks.encStr z).reverse ++ σ 18)
  have hτ17 : τ 17 = z.reverse := by simp [τ, h17]
  have e2 := Stmt.exec_moveAll hD17.symm z.reverse τ hτ17
  refine ⟨τ, e1, Stmt.exec_of_eq (e2.mono e1.space_le.2) ?_⟩
  funext j
  simp only [τ, Function.update_apply, List.reverse_reverse]
  split_ifs <;> subst_vars <;> simp_all

/-- **The decoding phase of the pop-frame routine.**  If stack `8` of `σ` starts with the codes of
six strings `z₁, …, z₆` followed by `rest`, the stacks `11` and above are empty, and the bound
`S` covers the space of `σ` plus four times one more than the total length of the strings, then
`popFrameDecodeStmt` runs from `σ` to `popFrameMid σ rest z₁ … z₆` within space `S`. -/
theorem exec_popFrameDecodeStmt (σ : Stacks 38) (rest z₁ z₂ z₃ z₄ z₅ z₆ : BitString) (S : ℕ)
    (h8 : σ 8 = Stacks.encList [z₁, z₂, z₃, z₄, z₅, z₆] ++ rest)
    (hempty : ∀ j : Fin 38, 11 ≤ j.val → σ j = [])
    (hS : σ.space + 4 * (z₁.length + z₂.length + z₃.length + z₄.length + z₅.length +
      z₆.length + 1) ≤ S) :
    Exec popFrameDecodeStmt σ (popFrameMid σ rest z₁ z₂ z₃ z₄ z₅ z₆) S := by
  let s₁ : Stacks 38 := Function.update (Function.update (Function.update (Function.update σ 8
    (Stacks.encList [z₂, z₃, z₄, z₅, z₆] ++ rest)) 11 z₁) 17 []) 18
      ((Stacks.encStr z₁).reverse ++ σ 18)
  let s₂ : Stacks 38 := Function.update (Function.update (Function.update (Function.update s₁ 8
    (Stacks.encList [z₃, z₄, z₅, z₆] ++ rest)) 12 z₂) 17 []) 18
      ((Stacks.encStr z₂).reverse ++ s₁ 18)
  let s₃ : Stacks 38 := Function.update (Function.update (Function.update (Function.update s₂ 8
    (Stacks.encList [z₄, z₅, z₆] ++ rest)) 13 z₃) 17 []) 18
      ((Stacks.encStr z₃).reverse ++ s₂ 18)
  let s₄ : Stacks 38 := Function.update (Function.update (Function.update (Function.update s₃ 8
    (Stacks.encList [z₅, z₆] ++ rest)) 14 z₄) 17 []) 18
      ((Stacks.encStr z₄).reverse ++ s₃ 18)
  let s₅ : Stacks 38 := Function.update (Function.update (Function.update (Function.update s₄ 8
    (Stacks.encList [z₆] ++ rest)) 15 z₅) 17 []) 18
      ((Stacks.encStr z₅).reverse ++ s₄ 18)
  let s₆ : Stacks 38 := Function.update (Function.update (Function.update (Function.update s₅ 8
    rest) 16 z₆) 17 []) 18 ((Stacks.encStr z₆).reverse ++ s₅ 18)
  have h8₁ : σ 8 = Stacks.encStr z₁ ++ (Stacks.encList [z₂, z₃, z₄, z₅, z₆] ++ rest) := by
    simpa [Stacks.encList, List.append_assoc] using h8
  obtain ⟨d₁, e₁, e₂⟩ := exec_popFrameDecodeMove σ z₁
    (Stacks.encList [z₂, z₃, z₄, z₅, z₆] ++ rest) 11 (by decide) (by decide) (by decide)
    h8₁ (hempty 17 (by omega)) (hempty 11 (by omega))
  change Exec (Stmt.moveAll 17 11) d₁ s₁ (σ.space + z₁.length) at e₂
  have h8₂ : s₁ 8 = Stacks.encStr z₂ ++ (Stacks.encList [z₃, z₄, z₅, z₆] ++ rest) := by
    simp [s₁, Stacks.encList, List.append_assoc]
  obtain ⟨d₂, e₃, e₄⟩ := exec_popFrameDecodeMove s₁ z₂
    (Stacks.encList [z₃, z₄, z₅, z₆] ++ rest) 12 (by decide) (by decide) (by decide)
    h8₂ (by simp [s₁]) (by simp [s₁, hempty 12 (by omega)])
  change Exec (Stmt.moveAll 17 12) d₂ s₂ (s₁.space + z₂.length) at e₄
  have h8₃ : s₂ 8 = Stacks.encStr z₃ ++ (Stacks.encList [z₄, z₅, z₆] ++ rest) := by
    simp [s₂, Stacks.encList, List.append_assoc]
  obtain ⟨d₃, e₅, e₆⟩ := exec_popFrameDecodeMove s₂ z₃
    (Stacks.encList [z₄, z₅, z₆] ++ rest) 13 (by decide) (by decide) (by decide)
    h8₃ (by simp [s₂]) (by simp [s₂, s₁, hempty 13 (by omega)])
  change Exec (Stmt.moveAll 17 13) d₃ s₃ (s₂.space + z₃.length) at e₆
  have h8₄ : s₃ 8 = Stacks.encStr z₄ ++ (Stacks.encList [z₅, z₆] ++ rest) := by
    simp [s₃, Stacks.encList, List.append_assoc]
  obtain ⟨d₄, e₇, e₈⟩ := exec_popFrameDecodeMove s₃ z₄
    (Stacks.encList [z₅, z₆] ++ rest) 14 (by decide) (by decide) (by decide)
    h8₄ (by simp [s₃]) (by simp [s₃, s₂, s₁, hempty 14 (by omega)])
  change Exec (Stmt.moveAll 17 14) d₄ s₄ (s₃.space + z₄.length) at e₈
  have h8₅ : s₄ 8 = Stacks.encStr z₅ ++ (Stacks.encList [z₆] ++ rest) := by
    simp [s₄, Stacks.encList, List.append_assoc]
  obtain ⟨d₅, e₉, e₁₀⟩ := exec_popFrameDecodeMove s₄ z₅
    (Stacks.encList [z₆] ++ rest) 15 (by decide) (by decide) (by decide)
    h8₅ (by simp [s₄]) (by simp [s₄, s₃, s₂, s₁, hempty 15 (by omega)])
  change Exec (Stmt.moveAll 17 15) d₅ s₅ (s₄.space + z₅.length) at e₁₀
  have h8₆ : s₅ 8 = Stacks.encStr z₆ ++ rest := by
    simp [s₅, Stacks.encList]
  obtain ⟨d₆, e₁₁, e₁₂⟩ := exec_popFrameDecodeMove s₅ z₆ rest 16
    (by decide) (by decide) (by decide) h8₆ (by simp [s₅])
    (by simp [s₅, s₄, s₃, s₂, s₁, hempty 16 (by omega)])
  change Exec (Stmt.moveAll 17 16) d₆ s₆ (s₅.space + z₆.length) at e₁₂
  have hs₁ := e₂.space_le.2
  have hs₂ := e₄.space_le.2
  have hs₃ := e₆.space_le.2
  have hs₄ := e₈.space_le.2
  have hs₅ := e₁₀.space_le.2
  have hs₆ := e₁₂.space_le.2
  have hend : s₆ = popFrameMid σ rest z₁ z₂ z₃ z₄ z₅ z₆ := by
    funext j
    fin_cases j <;>
      simp [s₆, s₅, s₄, s₃, s₂, s₁, popFrameMid, Stacks.encList, hempty,
        List.reverse_append, List.append_assoc]
  rw [popFrameDecodeStmt]
  exact .seq (e₁.mono (by omega)) (.seq (e₂.mono (by omega))
    (.seq (e₃.mono (by omega)) (.seq (e₄.mono (by omega))
    (.seq (e₅.mono (by omega)) (.seq (e₆.mono (by omega))
    (.seq (e₇.mono (by omega)) (.seq (e₈.mono (by omega))
    (.seq (e₉.mono (by omega)) (.seq (e₁₀.mono (by omega))
    (.seq (e₁₁.mono (by omega)) (.seq (Stmt.exec_of_eq (e₁₂.mono (by omega)) hend)
      (.skip (by rw [← hend]; omega)))))))))))))

/-- The space of the coded state with its mode stack `9` cleared, increased by four times one more
than the total length of the six fields of the top frame `F`, is at most the space of
`encSt base W m (i, F :: Ks)` plus `8 * frameSize W F`.  This is the bound that pays for the
decoding phase of the pop-frame routine. -/
theorem popFrameDecode_space (base : Stacks 38) (W m i : ℕ) (F : Frame) (Ks : List Frame) :
    Stacks.space (Function.update (encSt base W m (i, F :: Ks)) 9 []) +
        4 * (F.v.length + (numBits W F.y).length + (numBits W F.n).length +
          (List.replicate F.f true).length + F.v'.length + F.r.length + 1) ≤
      (encSt base W m (i, F :: Ks)).space + 8 * frameSize W F := by
  have h := Stacks.space_update (encSt base W m (i, F :: Ks)) 9 []
  dsimp [encSt, frameSize, numBits] at *
  simp at *
  omega

/-- Clearing stack `18` of the state reached after decoding the six fields of the top frame `F`
of the coded search state (with its mode stack cleared) gives the register state
`regSt base W m F Ks`. -/
theorem popFrameMid_clear_eq (base : Stacks 38) (W m i : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    Function.update
        (popFrameMid (Function.update (encSt base W m (i, F :: Ks)) 9 [])
          (Stacks.encList (Ks.flatMap (Frame.fields W))) F.v (numBits W F.y) (numBits W F.n)
          (List.replicate F.f true) F.v' F.r) 18 [] =
      regSt base W m F Ks := by
  funext j
  fin_cases j <;> simp [popFrameMid, regSt, encSt, Frame.fields, Stacks.encList, hb]

/-- **Popping the top frame into the registers.**  There are a statement `s` and a constant `K`
such that, for every base with the stacks `5`–`37` empty, `s` turns the coded search state with
top frame `F` and cleared mode stack `9` into the register state `regSt base W m F Ks`, within the
space of the coded state plus `K * frameSize W F`. -/
theorem exists_popFrameStmt : ∃ (s : Stmt 38) (K : ℕ), ∀ (base : Stacks 38) (W m i : ℕ)
    (F : Frame) (Ks : List Frame), (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    Exec s (Function.update (encSt base W m (i, F :: Ks)) 9 []) (regSt base W m F Ks)
      ((encSt base W m (i, F :: Ks)).space + K * frameSize W F) := by
  refine ⟨popFrameStmt, 8, fun base W m i F Ks hbase => ?_⟩
  let σ := Function.update (encSt base W m (i, F :: Ks)) 9 []
  let rest := Stacks.encList (Ks.flatMap (Frame.fields W))
  have h8 : σ 8 = Stacks.encList
      [F.v, numBits W F.y, numBits W F.n, List.replicate F.f true, F.v', F.r] ++ rest := by
    change encSt base W m (i, F :: Ks) 8 = _
    unfold encSt
    change Function.update (Function.update (Function.update base 8 _) 9 _) 10 _ 8 = _
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    change (if (8 : Fin 38) = 8 then _ else base 8) = _
    rw [ite_eq_left_iff.mpr (fun h => (h rfl).elim)]
    dsimp [Stacks.encList, Frame.fields, rest, List.flatMap]
    simp only [List.map_cons, List.flatten_cons, List.map_nil, List.flatten_nil,
      List.append_nil, List.append_assoc]
  have he : ∀ j : Fin 38, 11 ≤ j.val → σ j = [] := by
    intro j hj
    have hj9 : j ≠ (9 : Fin 38) := by
      intro h
      subst j
      norm_num at hj
    change Function.update (encSt base W m (i, F :: Ks)) 9 [] j = []
    rw [Function.update_of_ne hj9]
    unfold encSt
    change Function.update (Function.update (Function.update base 8 _) 9 _) 10 _ j = []
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hbase j (by omega)
  have hd := exec_popFrameDecodeStmt σ rest F.v (numBits W F.y) (numBits W F.n)
    (List.replicate F.f true) F.v' F.r
    ((encSt base W m (i, F :: Ks)).space + 8 * frameSize W F) h8 he
    (popFrameDecode_space base W m i F Ks)
  have hc := Stmt.exec_clear 18
    ((popFrameMid σ rest F.v (numBits W F.y) (numBits W F.n)
      (List.replicate F.f true) F.v' F.r) 18)
    (popFrameMid σ rest F.v (numBits W F.y) (numBits W F.n)
      (List.replicate F.f true) F.v' F.r) rfl
  refine Stmt.exec_of_eq (.seq hd (hc.mono hd.space_le.2)) ?_
  exact popFrameMid_clear_eq base W m i F Ks hbase

/-- Push the six register strings in reverse field order, so their self-delimiting codes appear
on stack `8` in forward frame order.  Stack `17` is the shared empty work stack. -/
def pushFrameEncodeStmt : Stmt 38 :=
  Stmt.seqs [QEnum.pushCode 16 17 8, QEnum.pushCode 15 17 8, QEnum.pushCode 14 17 8,
    QEnum.pushCode 13 17 8, QEnum.pushCode 12 17 8, QEnum.pushCode 11 17 8]

/-- The concrete push-frame routine encodes the registers and then clears their six copies. -/
def pushFrameStmt : Stmt 38 := .seq pushFrameEncodeStmt
  (Stmt.seqs [Stmt.clear 11, Stmt.clear 12, Stmt.clear 13, Stmt.clear 14, Stmt.clear 15,
    Stmt.clear 16])

/-- Prepending the code of `z` to stack `8` adds `2 * z.length + 1` to the space. -/
private lemma push_step_space (σ : Stacks 38) (z : BitString) :
    Stacks.space (Function.update σ 8 (Stacks.encStr z ++ σ 8)) =
    σ.space + 2 * z.length + 1 := by
  have h := Stacks.space_update σ 8 (Stacks.encStr z ++ σ 8)
  have hl : (Stacks.encStr z ++ σ 8).length = 2 * z.length + 1 + (σ 8).length := by
    rw [List.length_append, Stacks.length_encStr]
  omega

/-- `QEnum.pushCode Z 17 8` prepends the code of register `Z` to stack `8`, using the empty
stack `17` as work space, within any bound `S` that covers the added space. -/
private theorem push_step (Z : Fin 38) (σ : Stacks 38) (z pre : BitString) (S : ℕ)
    (hZ17 : Z ≠ 17) (hZ8 : Z ≠ 8) (hz : σ Z = z) (h17 : σ 17 = []) (h8 : σ 8 = pre)
    (hS : σ.space + 2 * z.length + 1 ≤ S) :
    Exec (QEnum.pushCode Z 17 8) σ (Function.update σ 8 (Stacks.encStr z ++ pre)) S := by
  have htD : (17 : Fin 38) ≠ 8 := by decide
  have e := QEnum.exec_pushCode hZ17 hZ8 htD h17
  rw [hz, h8] at e
  exact e.mono hS

/-- Six statements executed one after the other, each from the final state of the previous one
within the same bound `S`, execute as the sequence `Stmt.seqs [s₁, …, s₆]`. -/
private theorem exec_seqs_cons_6 {k : ℕ} {s₁ s₂ s₃ s₄ s₅ s₆ : Stmt k}
    {σ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ : Stacks k} {S : ℕ}
    (e1 : Exec s₁ σ σ₁ S)
    (e2 : Exec s₂ σ₁ σ₂ S)
    (e3 : Exec s₃ σ₂ σ₃ S)
    (e4 : Exec s₄ σ₃ σ₄ S)
    (e5 : Exec s₅ σ₄ σ₅ S)
    (e6 : Exec s₆ σ₅ σ₆ S) :
    Exec (Stmt.seqs [s₁, s₂, s₃, s₄, s₅, s₆]) σ σ₆ S := by
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ₁, e1, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ₂, e2, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ₃, e3, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ₄, e4, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ₅, e5, ?_⟩
  rw [Stmt.exec_seqs_cons]
  exact ⟨σ₆, e6, Exec.skip (Exec.space_le e6).2⟩

/-- **The encoding phase of the push-frame routine.**  If the registers `11`–`16` of `σ` hold
`z₁, …, z₆`, stack `17` is empty, and the bound `S` covers the space of `σ` plus twice the
total length of the strings plus six, then `pushFrameEncodeStmt` prepends
`Stacks.encList [z₁, …, z₆]` to stack `8` and changes no other stack, within space `S`. -/
theorem exec_pushFrameEncodeStmt (σ : Stacks 38) (z₁ z₂ z₃ z₄ z₅ z₆ : BitString) (S : ℕ)
    (h11 : σ 11 = z₁) (h12 : σ 12 = z₂) (h13 : σ 13 = z₃) (h14 : σ 14 = z₄)
    (h15 : σ 15 = z₅) (h16 : σ 16 = z₆) (h17 : σ 17 = [])
    (hS : σ.space + 2 * (z₁.length + z₂.length + z₃.length + z₄.length + z₅.length +
      z₆.length) + 6 ≤ S) :
    Exec pushFrameEncodeStmt σ
      (Function.update σ 8 (Stacks.encList [z₁, z₂, z₃, z₄, z₅, z₆] ++ σ 8)) S := by
  let σ1 : Stacks 38 := Function.update σ 8 (Stacks.encStr z₆ ++ σ 8)
  let σ2 : Stacks 38 := Function.update σ1 8 (Stacks.encStr z₅ ++ σ1 8)
  let σ3 : Stacks 38 := Function.update σ2 8 (Stacks.encStr z₄ ++ σ2 8)
  let σ4 : Stacks 38 := Function.update σ3 8 (Stacks.encStr z₃ ++ σ3 8)
  let σ5 : Stacks 38 := Function.update σ4 8 (Stacks.encStr z₂ ++ σ4 8)
  let σ6 : Stacks 38 := Function.update σ5 8 (Stacks.encStr z₁ ++ σ5 8)
  have h1 : σ1.space = σ.space + 2 * z₆.length + 1 := push_step_space σ z₆
  have h2 : σ2.space = σ1.space + 2 * z₅.length + 1 := push_step_space σ1 z₅
  have h3 : σ3.space = σ2.space + 2 * z₄.length + 1 := push_step_space σ2 z₄
  have h4 : σ4.space = σ3.space + 2 * z₃.length + 1 := push_step_space σ3 z₃
  have h5 : σ5.space = σ4.space + 2 * z₂.length + 1 := push_step_space σ4 z₂
  have hs1 : σ.space + 2 * z₆.length + 1 ≤ S := by omega
  have hs2 : σ1.space + 2 * z₅.length + 1 ≤ S := by omega
  have hs3 : σ2.space + 2 * z₄.length + 1 ≤ S := by omega
  have hs4 : σ3.space + 2 * z₃.length + 1 ≤ S := by omega
  have hs5 : σ4.space + 2 * z₂.length + 1 ≤ S := by omega
  have hs6 : σ5.space + 2 * z₁.length + 1 ≤ S := by omega
  have h15' : σ1 15 = z₅ := by simp [σ1, h15]
  have h14' : σ2 14 = z₄ := by simp [σ2, σ1, h14]
  have h13' : σ3 13 = z₃ := by simp [σ3, σ2, σ1, h13]
  have h12' : σ4 12 = z₂ := by simp [σ4, σ3, σ2, σ1, h12]
  have h11' : σ5 11 = z₁ := by simp [σ5, σ4, σ3, σ2, σ1, h11]
  have h17₂ : σ1 17 = [] := by simp [σ1, h17]
  have h17₃ : σ2 17 = [] := by simp [σ2, σ1, h17]
  have h17₄ : σ3 17 = [] := by simp [σ3, σ2, σ1, h17]
  have h17₅ : σ4 17 = [] := by simp [σ4, σ3, σ2, σ1, h17]
  have h17₆ : σ5 17 = [] := by simp [σ5, σ4, σ3, σ2, σ1, h17]
  have heq : σ6 = Function.update σ 8 (Stacks.encList [z₁, z₂, z₃, z₄, z₅, z₆] ++ σ 8) := by
    simp only [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_idem, Function.update_self,
      Stacks.encList, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  unfold pushFrameEncodeStmt
  rw [← heq]
  have e6 := push_step 16 σ z₆ (σ 8) S (by decide) (by decide) h16 h17 rfl hs1
  have e5 := push_step 15 σ1 z₅ (σ1 8) S (by decide) (by decide) h15' h17₂ rfl hs2
  have e4 := push_step 14 σ2 z₄ (σ2 8) S (by decide) (by decide) h14' h17₃ rfl hs3
  have e3 := push_step 13 σ3 z₃ (σ3 8) S (by decide) (by decide) h13' h17₄ rfl hs4
  have e2 := push_step 12 σ4 z₂ (σ4 8) S (by decide) (by decide) h12' h17₅ rfl hs5
  have e1 := push_step 11 σ5 z₁ (σ5 8) S (by decide) (by decide) h11' h17₆ rfl hs6
  exact exec_seqs_cons_6 e6 e5 e4 e3 e2 e1

/-- Clearing the registers `11` through `16` one after the other empties exactly these six
stacks, within any space bound `S` that covers the space of `σ`. -/
theorem exec_pushFrameClearStmt (σ : Stacks 38) (S : ℕ) (hS : σ.space ≤ S) :
    Exec (Stmt.seqs [Stmt.clear 11, Stmt.clear 12, Stmt.clear 13, Stmt.clear 14,
      Stmt.clear 15, Stmt.clear 16]) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update σ 11 []) 12 []) 13 []) 14 []) 15 []) 16 []) S := by
  have hc1 := (Stmt.exec_clear 11 (σ 11) σ rfl).mono hS
  have hc2 := (Stmt.exec_clear 12 _ _ rfl).mono hc1.space_le.2
  have hc3 := (Stmt.exec_clear 13 _ _ rfl).mono hc2.space_le.2
  have hc4 := (Stmt.exec_clear 14 _ _ rfl).mono hc3.space_le.2
  have hc5 := (Stmt.exec_clear 15 _ _ rfl).mono hc4.space_le.2
  have hc6 := (Stmt.exec_clear 16 _ _ rfl).mono hc5.space_le.2
  exact exec_seqs_cons_6 hc1 hc2 hc3 hc4 hc5 hc6

/-- Integer form of the space of a stack update: the old space plus the new content length
minus the old content length. -/
theorem space_update_int {k : ℕ} (σ : Stacks k) (r : Fin k) (v : BitString) :
    (Stacks.space (Function.update σ r v) : ℤ) = (σ.space : ℤ) + v.length - (σ r).length := by
  have := Stacks.space_update σ r v; omega

/-- The space of the register state `regSt base W m F Ks`, increased by twice the total length of
the six registers and by six, is at most the space of `encSt base W m (0, F :: Ks)` plus
`8 * frameSize W F`.  This is the bound that pays for coding all six registers back onto stack `8`
before they are cleared. -/
theorem pushFrameEncode_space (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) :
    (regSt base W m F Ks).space +
        2 * (F.v.length + (numBits W F.y).length + (numBits W F.n).length +
          (List.replicate F.f true).length + F.v'.length + F.r.length) + 6 ≤
      (encSt base W m (0, F :: Ks)).space + 8 * frameSize W F := by
  zify
  dsimp [regSt, encSt]
  simp only [space_update_int, Function.update]
  simp only [Stacks.length_encList, List.flatMap_cons, List.map_append, List.sum_append]
  dsimp [frameSize, numBits, Frame.fields]
  simp only [List.length_map, List.length_range, List.length_replicate, List.map_cons,
    List.sum_cons, List.sum_nil, List.map_nil]
  omega

/-- Prefixing the code of the six fields of `F` to stack `8` of the register state
`regSt base W m F Ks` and then clearing the registers `11`–`16` gives the coded state
`encSt base W m (0, F :: Ks)` with its mode stack `9` cleared. -/
theorem pushFrameClear_eq (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame)
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    let σ := Function.update (regSt base W m F Ks) 8
      (Stacks.encList [F.v, numBits W F.y, numBits W F.n, List.replicate F.f true, F.v', F.r] ++
        regSt base W m F Ks 8)
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update σ 11 []) 12 []) 13 []) 14 []) 15 []) 16 [] =
      Function.update (encSt base W m (0, F :: Ks)) 9 [] := by
  funext j
  fin_cases j <;> simp [regSt, encSt, Frame.fields, Stacks.encList, hb]

/-- **Pushing the registers back as the top frame.**  There are a statement `s` and a constant `K`
such that, for every base with the stacks `5`–`37` empty, `s` turns the register state
`regSt base W m F Ks` into the coded search state with top frame `F` and cleared mode stack `9`,
within the space of that coded state plus `K * frameSize W F`. -/
theorem exists_pushFrameStmt : ∃ (s : Stmt 38) (K : ℕ), ∀ (base : Stacks 38) (W m : ℕ)
    (F : Frame) (Ks : List Frame), (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    Exec s (regSt base W m F Ks) (Function.update (encSt base W m (0, F :: Ks)) 9 [])
      ((encSt base W m (0, F :: Ks)).space + K * frameSize W F) := by
  refine ⟨pushFrameStmt, 8, fun base W m F Ks hbase => ?_⟩
  let σ := regSt base W m F Ks
  have h11 : σ 11 = F.v := by simp [σ, regSt]
  have h12 : σ 12 = numBits W F.y := by simp [σ, regSt]
  have h13 : σ 13 = numBits W F.n := by simp [σ, regSt]
  have h14 : σ 14 = List.replicate F.f true := by simp [σ, regSt]
  have h15 : σ 15 = F.v' := by simp [σ, regSt]
  have h16 : σ 16 = F.r := by simp [σ, regSt]
  have h17 : σ 17 = [] := by
    simp [σ, regSt, encSt, hbase (17 : Fin 38) (by omega)]
  have he := exec_pushFrameEncodeStmt σ F.v (numBits W F.y) (numBits W F.n)
    (List.replicate F.f true) F.v' F.r
    ((encSt base W m (0, F :: Ks)).space + 8 * frameSize W F)
    h11 h12 h13 h14 h15 h16 h17 (pushFrameEncode_space base W m F Ks)
  have hc := exec_pushFrameClearStmt
    (Function.update σ 8 (Stacks.encList [F.v, numBits W F.y, numBits W F.n,
      List.replicate F.f true, F.v', F.r] ++ σ 8))
    ((encSt base W m (0, F :: Ks)).space + 8 * frameSize W F) he.space_le.2
  refine Stmt.exec_of_eq (.seq he hc) ?_
  exact pushFrameClear_eq base W m F Ks hbase

end DFS
end Kolmogorov.RandomStrings
