/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSFrames

/-!
# The depth-first search: initialisation

The initialisation routine of the search: counting the board, writing the zero vector and the
unary fuel, and encoding the root frame (`DFS.exists_initStmt`).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- One scan step moves either a delimiter or a marker/data pair from the board code to stack
`11`; delimiters additionally increment the unary counter on `12`.  The encoding invariant says
that a `true` marker always has a following data bit. -/
def initCountBody : Stmt 38 :=
  Stmt.caseBit 1 fun marker =>
    if marker then Stmt.seqs [Stmt.moveBit 1 11, Stmt.moveBit 1 11]
    else Stmt.seqs [Stmt.moveBit 1 11, .push 12 true]

/-- Scan the board code without decoding its (possibly long) strings, then restore it from the
reversal stack. -/
def initCountProg : Stmt 38 :=
  Stmt.seqs [.loop 1 Option.isSome initCountBody, Stmt.moveAll 11 1]

/-- `initZero src tmp dst` restores `src` through an empty temporary stack `tmp` and prepends
one zero to `dst` for each bit of `src`, provided the three stacks are distinct. -/
def initZero (src tmp dst : Fin 38) : Stmt 38 :=
  .seq (Stmt.moveAll src tmp) (.loop tmp Option.isSome (QEnum.zeroStep tmp src dst))

/-- Construct the persistent zero vector, a width-`W` zero vector, and unary fuel `m+1` from
the unary board-cardinality counter. -/
def initVectorProg : Stmt 38 :=
  Stmt.seqs [initZero 12 17 10, initZero 3 17 13, Stmt.copy 12 14 17, .push 14 true]

/-- Encode the six root fields onto stack `8` in reverse field order, clear temporary vectors,
and write mode `3` on stack `9`. -/
def initEncodeProg : Stmt 38 :=
  Stmt.seqs [QEnum.pushCode 10 17 8, QEnum.pushCode 10 17 8, QEnum.pushCode 14 17 8,
    QEnum.pushCode 13 17 8, QEnum.pushCode 13 17 8, QEnum.pushCode 12 17 8,
    Stmt.clear 12, Stmt.clear 13, Stmt.clear 14,
    Stmt.pushList 9 (List.replicate 3 true)]

/-- The complete initializer counts the board strings, constructs the zero vectors and unary
fuel, and encodes the root frame in mode `3`. -/
def initProg : Stmt 38 := .seq initCountProg (.seq initVectorProg initEncodeProg)

/-- Consuming one encoded string transfers its reversed code from stack `1` to `11` and pushes
one unary counter bit on `12`, after which the scan continues on the remaining input. -/
private theorem exec_initCountString (z rest : BitString) (σ out : Stacks 38) (S : ℕ)
    (h1 : σ 1 = Stacks.encStr z ++ rest)
    (hcont : Exec (.loop 1 Option.isSome initCountBody)
      (Function.update (Function.update (Function.update σ 1 rest) 11
        ((Stacks.encStr z).reverse ++ σ 11)) 12 (true :: σ 12)) out S) :
    Exec (.loop 1 Option.isSome initCountBody) σ out S := by
  have hS : σ.space + 1 ≤ S := by
    have e1 := Stacks.space_update σ (1 : Fin 38) rest
    have e2 := Stacks.space_update (Function.update σ 1 rest) (11 : Fin 38)
      ((Stacks.encStr z).reverse ++ σ 11)
    have e3 := Stacks.space_update (Function.update (Function.update σ 1 rest) 11
      ((Stacks.encStr z).reverse ++ σ 11)) (12 : Fin 38) (true :: σ 12)
    rw [h1] at e1
    rw [Function.update_of_ne (by decide : (11 : Fin 38) ≠ 1)] at e2
    rw [Function.update_of_ne (by decide : (12 : Fin 38) ≠ 11),
      Function.update_of_ne (by decide : (12 : Fin 38) ≠ 1)] at e3
    simp only [List.length_append, List.length_reverse, List.length_cons] at e1 e2 e3
    have := hcont.space_le.1
    omega
  induction z generalizing σ with
  | nil =>
    have h1' : σ 1 = false :: rest := by simpa [Stacks.encStr] using h1
    let τ := Function.update (Function.update σ 1 rest) 11 (false :: σ 11)
    have em := Stmt.exec_moveBit (by decide : (1 : Fin 38) ≠ 11) h1'
    have em' : Exec (Stmt.moveBit 1 11) σ τ σ.space := by simpa [τ] using em
    have ep : Exec (.push 12 true) τ (Function.update τ 12 (true :: τ 12)) S :=
      .push (by have := em'.space_le.2; omega)
    have esk : Exec (.skip : Stmt 38) (Function.update τ 12 (true :: τ 12))
        (Function.update τ 12 (true :: τ 12)) S := .skip ep.space_le.2
    have eb : Exec initCountBody σ (Function.update τ 12 (true :: τ 12)) S := by
      rw [initCountBody, Stmt.exec_caseBit h1']
      simp only [Bool.false_eq_true, ite_false]
      exact .seq (em'.mono (by omega)) (.seq ep esk)
    have ht : Function.update τ 12 (true :: τ 12) =
        Function.update (Function.update (Function.update σ 1 rest) 11
          ((Stacks.encStr []).reverse ++ σ 11)) 12 (true :: σ 12) := by
      funext j
      simp [τ, Stacks.encStr]
    rw [ht] at eb
    exact .loopT (by simp [h1']) eb hcont
  | cons b z ih =>
    have h1' : σ 1 = true :: b :: (Stacks.encStr z ++ rest) := by
      simpa [Stacks.encStr] using h1
    let σ₁ := Function.update (Function.update σ 1 (b :: Stacks.encStr z ++ rest)) 11
      (true :: σ 11)
    let τ := Function.update (Function.update σ₁ 1 (Stacks.encStr z ++ rest)) 11
      (b :: σ₁ 11)
    have em1 := Stmt.exec_moveBit (by decide : (1 : Fin 38) ≠ 11) h1'
    have em1' : Exec (Stmt.moveBit 1 11) σ σ₁ σ.space := by simpa [σ₁] using em1
    have hsecond : σ₁ 1 = b :: (Stacks.encStr z ++ rest) := by simp [σ₁]
    have em2 := Stmt.exec_moveBit (by decide : (1 : Fin 38) ≠ 11) hsecond
    have em2' : Exec (Stmt.moveBit 1 11) σ₁ τ (Stacks.space σ₁) := by
      simpa [τ] using em2
    have eb : Exec initCountBody σ τ S := by
      rw [initCountBody, Stmt.exec_caseBit h1']
      simp only [ite_true]
      exact .seq (em1'.mono (by omega))
        (.seq (em2'.mono (by have := em1'.space_le.2; omega))
          (.skip (by
            have hle₁ := em1'.space_le.2
            have hle₂ := em2'.space_le.2
            omega)))
    have hτ1 : τ 1 = Stacks.encStr z ++ rest := by simp [τ]
    have hτS : Stacks.space τ + 1 ≤ S := by
      have hle₁ := em1'.space_le.2
      have hle₂ := em2'.space_le.2
      omega
    have heq : Function.update (Function.update (Function.update τ 1 rest) 11
        ((Stacks.encStr z).reverse ++ τ 11)) 12 (true :: τ 12) =
        Function.update (Function.update (Function.update σ 1 rest) 11
          ((Stacks.encStr (b :: z)).reverse ++ σ 11)) 12 (true :: σ 12) := by
      funext j
      simp only [τ, σ₁, Function.update_apply, Stacks.encStr, List.flatMap_cons,
        List.reverse_append, List.append_assoc]
      split_ifs <;> subst_vars <;> simp_all
    rw [← heq] at hcont
    have erest := ih τ hτ1 hcont hτS
    exact .loopT (by simp [h1']) eb erest

/-- One scan step moves the code of `z` from stack `1` to `11` and adds one unary bit on `12`, so
the total length grows by exactly one. -/
private theorem initCountStep_space (z : BitString) (L : List BitString) (σ : Stacks 38)
    (h1 : σ 1 = Stacks.encStr z ++ Stacks.encList L) :
    Stacks.space (Function.update (Function.update (Function.update σ 1 (Stacks.encList L)) 11
      ((Stacks.encStr z).reverse ++ σ 11)) 12 (true :: σ 12)) = σ.space + 1 := by
  have e1 := Stacks.space_update σ (1 : Fin 38) (Stacks.encList L)
  have e2 := Stacks.space_update (Function.update σ 1 (Stacks.encList L)) (11 : Fin 38)
    ((Stacks.encStr z).reverse ++ σ 11)
  have e3 := Stacks.space_update (Function.update (Function.update σ 1 (Stacks.encList L)) 11
    ((Stacks.encStr z).reverse ++ σ 11)) (12 : Fin 38) (true :: σ 12)
  rw [h1] at e1
  rw [Function.update_of_ne (by decide : (11 : Fin 38) ≠ 1)] at e2
  rw [Function.update_of_ne (by decide : (12 : Fin 38) ≠ 11),
    Function.update_of_ne (by decide : (12 : Fin 38) ≠ 1)] at e3
  simp only [List.length_append, List.length_reverse, List.length_cons] at e1 e2 e3
  omega

/-- Scanning `L` empties stack `1`, prepends its reversed encoding to `11`, and adds one unary
bit to `12` per string, preserving every other stack within space `σ.space + L.length`. -/
theorem exec_initCountLoopAux (L : List BitString) (σ : Stacks 38) (S : ℕ)
    (h1 : σ 1 = Stacks.encList L) (hS : σ.space + L.length ≤ S) :
    ∃ out, Exec (.loop 1 Option.isSome initCountBody) σ out S ∧ out 1 = [] ∧
      out 11 = (Stacks.encList L).reverse ++ σ 11 ∧
      out 12 = List.replicate L.length true ++ σ 12 ∧
      ∀ j : Fin 38, j ≠ 1 → j ≠ 11 → j ≠ 12 → out j = σ j := by
  revert σ
  induction L with
  | nil =>
    intro σ h1 hS
    have h1' : σ 1 = [] := h1.trans QEnum.encList_nil
    refine ⟨σ, .loopF (by rw [h1']; rfl) (by simpa using hS), h1', ?_, ?_, ?_⟩
    · rfl
    · rfl
    · intros; rfl
  | cons z L ih =>
    intro σ h1 hS
    have h1' : σ 1 = Stacks.encStr z ++ Stacks.encList L := h1.trans (QEnum.encList_cons z L)
    let τ : Stacks 38 := Function.update (Function.update (Function.update σ 1
      (Stacks.encList L)) 11 ((Stacks.encStr z).reverse ++ σ 11)) 12 (true :: σ 12)
    have hτsp : Stacks.space τ = σ.space + 1 := initCountStep_space z L σ h1'
    have hτ1 : τ 1 = Stacks.encList L := by
      simp only [τ, Function.update_of_ne (by decide : (1 : Fin 38) ≠ 12),
        Function.update_of_ne (by decide : (1 : Fin 38) ≠ 11), Function.update_self]
    have hτ11 : τ 11 = (Stacks.encStr z).reverse ++ σ 11 := by
      simp only [τ, Function.update_of_ne (by decide : (11 : Fin 38) ≠ 12),
        Function.update_self]
    have hτ12 : τ 12 = true :: σ 12 := by simp only [τ, Function.update_self]
    have hτS : Stacks.space τ + L.length ≤ S := by
      rw [List.length_cons] at hS; omega
    obtain ⟨out, ec, ho1, ho11, ho12, ho⟩ := ih τ hτ1 hτS
    refine ⟨out, exec_initCountString z (Stacks.encList L) σ out S h1' ec, ho1,
      ?_, ?_, fun j hj1 hj11 hj12 => ?_⟩
    · rw [ho11, hτ11, QEnum.encList_cons, List.reverse_append, List.append_assoc]
    · rw [ho12, hτ12, List.length_cons, List.replicate_succ', List.append_assoc,
        List.singleton_append]
    · rw [ho j hj1 hj11 hj12]
      simp only [τ, Function.update_of_ne hj12, Function.update_of_ne hj11,
        Function.update_of_ne hj1]
/-- The complete scan loop transfers the reversed encoded list to stack `11` and adds one unary
bit on stack `12` per encoded string. -/
private theorem exec_initCountLoop (L : List BitString) (σ : Stacks 38) (S : ℕ)
    (h1 : σ 1 = Stacks.encList L) (hS : σ.space + L.length ≤ S) :
    Exec (.loop 1 Option.isSome initCountBody) σ
      (Function.update (Function.update (Function.update σ 1 []) 11
        ((Stacks.encList L).reverse ++ σ 11)) 12
        (List.replicate L.length true ++ σ 12)) S := by
  obtain ⟨out, e, ho1, ho11, ho12, ho⟩ := exec_initCountLoopAux L σ S h1 hS
  apply Stmt.exec_of_eq e
  funext j
  simp only [Function.update_apply]
  split_ifs with h12 h11 h1
  · simpa [h12] using ho12
  · simpa [h11] using ho11
  · simpa [h1] using ho1
  · exact ho j h1 h11 h12

/-- The in-place scan restores `Stacks.encList LX` and leaves exactly `LX.length` unary bits
on stack `12`, using at most `base.space + 2 * (LX.length + 1) ^ 2` space. -/
theorem exec_initCountProg (base : Stacks 38) (LX cs : List BitString) (eb : BitString)
    (hbase : BaseOK base LX cs eb) :
    Exec initCountProg base (Function.update base 12 (List.replicate LX.length true))
      (base.space + 2 * (LX.length + 1) ^ 2) := by
  let S := base.space + 2 * (LX.length + 1) ^ 2
  have h1 : base 1 = Stacks.encList LX := hbase.1
  have h11 : base 11 = [] := hbase.2.2.2 11 (by decide)
  have h12 : base 12 = [] := hbase.2.2.2 12 (by decide)
  have eloop := exec_initCountLoop LX base S h1 (by unfold S; nlinarith)
  let τ := Function.update (Function.update (Function.update base 1 []) 11
    (Stacks.encList LX).reverse) 12 (List.replicate LX.length true ++ base 12)
  have hτ11 : τ 11 = (Stacks.encList LX).reverse := by simp [τ]
  have emove := Stmt.exec_moveAll (by decide : (11 : Fin 38) ≠ 1)
    (Stacks.encList LX).reverse τ hτ11
  have hout : Function.update (Function.update τ 11 []) 1
      ((Stacks.encList LX).reverse.reverse ++ τ 1) =
      Function.update base 12 (List.replicate LX.length true) := by
    funext j
    simp only [τ, Function.update_apply, List.reverse_reverse]
    split_ifs <;> subst_vars <;> simp_all
  have eloop' : Exec (.loop 1 Option.isSome initCountBody) base τ S := by
    simpa [τ, h11] using eloop
  change Exec initCountProg base (Function.update base 12 (List.replicate LX.length true)) S
  rw [initCountProg]
  have emove' := Stmt.exec_of_eq (emove.mono (by exact eloop'.space_le.2)) hout
  exact .seq eloop' (.seq emove' (.skip emove'.space_le.2))

/-- From the unary count, the vector phase builds `0^m` on stack `10`, `0^W` on `13`, and
`1^(m+1)` on `14`, preserving the count on `12` within
`base.space + 10 * (LX.length + W + 1) ^ 2` space. -/
theorem exec_initVectorProg (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
    (hbase : BaseOK base LX cs eb) (heb : eb.length = W) :
    Exec initVectorProg (Function.update base 12 (List.replicate LX.length true))
      (Function.update (Function.update (Function.update
        (Function.update base 12 (List.replicate LX.length true)) 10
          (List.replicate LX.length false)) 13 (List.replicate W false)) 14
          (List.replicate (LX.length + 1) true))
      (base.space + 10 * (LX.length + W + 1) ^ 2) := by
  obtain ⟨-, -, h3, hb⟩ := hbase
  let σ₀ : Stacks 38 := Function.update base 12 (List.replicate LX.length true)
  let σ₁ : Stacks 38 := Function.update σ₀ 10 (List.replicate LX.length false)
  let σ₂ : Stacks 38 := Function.update σ₁ 13 (List.replicate W false)
  let S := base.space + 10 * (LX.length + W + 1) ^ 2
  have hb12 : base (12 : Fin 38) = [] := hb 12 (by decide)
  have hb10 : base (10 : Fin 38) = [] := hb 10 (by decide)
  have hb13 : base (13 : Fin 38) = [] := hb 13 (by decide)
  have hb14 : base (14 : Fin 38) = [] := hb 14 (by decide)
  have hb17 : base (17 : Fin 38) = [] := hb 17 (by decide)
  have hσ₀space : σ₀.space = base.space + LX.length := by
    have hu := Stacks.space_update base (12 : Fin 38) (List.replicate LX.length true)
    rw [hb12] at hu
    simp only [List.length_nil, List.length_replicate, Nat.add_zero] at hu
    simpa [σ₀] using hu
  have hσ₀twelve : σ₀ (12 : Fin 38) = List.replicate LX.length true := by simp [σ₀]
  have hlarge : 3 * LX.length + W + 1 ≤ 10 * (LX.length + W + 1) ^ 2 := by
    have hquad : LX.length + W + 1 ≤ (LX.length + W + 1) ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ (by omega)
    calc
      3 * LX.length + W + 1 ≤ 10 * (LX.length + W + 1) := by omega
      _ ≤ 10 * (LX.length + W + 1) ^ 2 := Nat.mul_le_mul_left 10 hquad
  have e₀' : Exec (initZero 12 17 10) σ₀ σ₁ S := by
    let τ : Stacks 38 := Function.update (Function.update σ₀ 12 []) 17 (σ₀ 12).reverse
    have ht : σ₀ 17 = [] := by simp [σ₀, hb17]
    have em : Exec (Stmt.moveAll 12 17) σ₀ τ σ₀.space := by
      simpa only [τ, ht, List.append_nil] using
        (Stmt.exec_moveAll (by decide : (12 : Fin 38) ≠ 17) (σ₀ 12) σ₀ rfl)
    have ez := QEnum.exec_zeroLoop (t := 17) (r := 12) (r' := 10)
      (σ₀ 12).reverse τ (by simp [τ])
    have hτ := em.space_le.2
    rw [initZero]
    refine Stmt.exec_of_eq (.seq (em.mono (by unfold S; omega)) (ez.mono ?_)) ?_
    · rw [List.length_reverse, hσ₀twelve, List.length_replicate]
      unfold S
      omega
    · funext j
      by_cases h10 : j = 10
      · subst j; simp [τ, σ₁, σ₀, hb10]
      by_cases h12 : j = 12
      · subst j; simp [τ, σ₁]
      by_cases h17 : j = 17
      · subst j; simp [τ, σ₁, σ₀, hb17]
      simp [τ, σ₁, h10, h12, h17]
  have hσ₁space : σ₁.space = base.space + 2 * LX.length := by
    have hu := Stacks.space_update σ₀ (10 : Fin 38) (List.replicate LX.length false)
    have h10 : σ₀ (10 : Fin 38) = [] := by simp [σ₀, hb10]
    rw [h10, hσ₀space] at hu
    simp only [List.length_nil, List.length_replicate, Nat.add_zero] at hu
    change σ₁.space = base.space + LX.length + LX.length at hu
    omega
  have hσ₁three : σ₁ (3 : Fin 38) = eb := by simp [σ₁, σ₀, h3]
  have e₁' : Exec (initZero 3 17 13) σ₁ σ₂ S := by
    let τ : Stacks 38 := Function.update (Function.update σ₁ 3 []) 17 (σ₁ 3).reverse
    have ht : σ₁ 17 = [] := by simp [σ₁, σ₀, hb17]
    have em : Exec (Stmt.moveAll 3 17) σ₁ τ σ₁.space := by
      simpa only [τ, ht, List.append_nil] using
        (Stmt.exec_moveAll (by decide : (3 : Fin 38) ≠ 17) (σ₁ 3) σ₁ rfl)
    have ez := QEnum.exec_zeroLoop (t := 17) (r := 3) (r' := 13)
      (σ₁ 3).reverse τ (by simp [τ])
    have hτ := em.space_le.2
    rw [initZero]
    refine Stmt.exec_of_eq (.seq (em.mono (by unfold S; omega)) (ez.mono ?_)) ?_
    · rw [List.length_reverse, hσ₁three, heb]
      unfold S
      omega
    · funext j
      by_cases h13 : j = 13
      · subst j; simp [τ, σ₂, σ₁, σ₀, h3, heb, hb13]
      by_cases h3 : j = 3
      · subst j; simp [τ, σ₂]
      by_cases h17 : j = 17
      · subst j; simp [τ, σ₂, σ₁, σ₀, hb17]
      simp [τ, σ₂, h13, h3, h17]
  have hσ₂space : σ₂.space = base.space + 2 * LX.length + W := by
    have hu := Stacks.space_update σ₁ (13 : Fin 38) (List.replicate W false)
    have h13 : σ₁ (13 : Fin 38) = [] := by simp [σ₁, σ₀, hb13]
    rw [h13, hσ₁space] at hu
    simp only [List.length_nil, List.length_replicate, Nat.add_zero] at hu
    change σ₂.space = base.space + 2 * LX.length + W at hu
    exact hu
  have e₂' : Exec (Stmt.seqs [Stmt.copy 12 14 17, .push 14 true]) σ₂
      (Function.update σ₂ 14 (List.replicate (LX.length + 1) true)) S := by
    have ht : σ₂ 17 = [] := by simp [σ₂, σ₁, σ₀, hb17]
    have h12 : σ₂ 12 = List.replicate LX.length true := by simp [σ₂, σ₁, σ₀]
    have h14 : σ₂ 14 = [] := by simp [σ₂, σ₁, σ₀, hb14]
    let τ : Stacks 38 := Function.update σ₂ 14 (List.replicate LX.length true)
    have ec := Stmt.exec_copy (r := 12) (r' := 14) (t := 17)
      (by decide) (by decide) (by decide) ht
    rw [h12, h14, List.append_nil, List.length_replicate] at ec
    have hτspace : τ.space = σ₂.space + LX.length := by
      have hu := Stacks.space_update σ₂ 14 (List.replicate LX.length true)
      rw [h14] at hu
      simpa only [List.length_nil, List.length_replicate, Nat.add_zero] using hu
    have ep : Exec (.push 14 true) τ (Function.update τ 14 (true :: τ 14)) S :=
      .push (by rw [hτspace, hσ₂space]; unfold S; omega)
    refine Stmt.exec_of_eq
      (.seq (ec.mono (by rw [hσ₂space]; unfold S; omega)) (.seq ep (.skip ep.space_le.2))) ?_
    simp [τ, List.replicate_succ, Function.update_idem]
  simpa only [initVectorProg, Stmt.seqs, σ₀, σ₁, σ₂, S] using
    Exec.seq e₀' (Exec.seq e₁' e₂')

/-- Writing `1^m` on stack `12`, `0^m` on `10`, `0^W` on `13` and `1^(m+1)` on `14` of a base
that is empty from stack `5` on adds `3 * m + W + 1` to the total space. -/
private theorem exec_initEncodeProg_space {base : Stacks 38} {m W : ℕ}
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    let σ0 : Stacks 38 := Function.update (Function.update (Function.update
      (Function.update base 12 (List.replicate m true)) 10
        (List.replicate m false)) 13 (List.replicate W false)) 14
        (List.replicate (m + 1) true)
    σ0.space = base.space + (3 * m + W + 1) := by
  intro σ0
  have h1 := Stacks.space_update base 12 (List.replicate m true)
  have h2 := Stacks.space_update (Function.update base 12 (List.replicate m true)) 10
    (List.replicate m false)
  have h3 := Stacks.space_update (Function.update (Function.update base 12
    (List.replicate m true)) 10 (List.replicate m false)) 13 (List.replicate W false)
  have h4 := Stacks.space_update (Function.update (Function.update (Function.update base 12
    (List.replicate m true)) 10 (List.replicate m false)) 13 (List.replicate W false)) 14
    (List.replicate (m + 1) true)
  have e1 : base 12 = [] := hb 12 (by decide)
  have e2 : (Function.update base 12 (List.replicate m true)) 10 = [] := by
    rw [Function.update_of_ne (by decide)]; exact hb 10 (by decide)
  have e3 : (Function.update (Function.update base 12 (List.replicate m true)) 10
    (List.replicate m false)) 13 = [] := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact hb 13 (by decide)
  have e4 : (Function.update (Function.update (Function.update base 12 (List.replicate m true)) 10
    (List.replicate m false)) 13 (List.replicate W false)) 14 = [] := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    exact hb 14 (by decide)
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  simp only [List.length_nil, List.length_replicate, Nat.add_zero] at h1 h2 h3 h4
  change σ0.space = _
  rw [h4, h3, h2, h1]
  omega

/-- With the six root fields encoded on stack `8` and stacks `12`-`14` cleared, pushing the mode
code `1^3` onto stack `9` gives exactly the encoded root state `encSt base W m (3, [root m])`. -/
private theorem exec_initEncodeProg_finaleq {base : Stacks 38} {m W : ℕ}
    (hb : ∀ j : Fin 38, 5 ≤ j.val → base j = []) :
    let σ0 : Stacks 38 := Function.update (Function.update (Function.update
      (Function.update base 12 (List.replicate m true)) 10
        (List.replicate m false)) 13 (List.replicate W false)) 14
        (List.replicate (m + 1) true)
    let V6 : BitString := Stacks.encStr (List.replicate m true) ++
      (Stacks.encStr (List.replicate W false) ++ (Stacks.encStr (List.replicate W false) ++
        (Stacks.encStr (List.replicate (m + 1) true) ++ (Stacks.encStr (List.replicate m false) ++
          (Stacks.encStr (List.replicate m false) ++ [])))))
    let τ9 : Stacks 38 := Function.update (Function.update (Function.update
      (Function.update σ0 8 V6) 12 []) 13 []) 14 []
    Function.update τ9 9 (List.replicate 3 true ++ τ9 9) = encSt base W m (3, [root m]) := by
  intro σ0 V6 τ9
  have hb9 := hb 9 (by decide)
  have hb12 := hb 12 (by decide)
  have hb13 := hb 13 (by decide)
  have hb14 := hb 14 (by decide)
  have hnb : numBits W 0 = List.replicate W false := by
    simp only [numBits, Nat.zero_testBit, List.map_const', List.length_range]
  have hstack8 : V6 = Stacks.encList ([root m].flatMap (Frame.fields W)) := by
    dsimp only [V6]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Frame.fields, root,
      Stacks.encList, hnb]
  funext j
  by_cases h8 : j = 8
  · subst h8
    simp [τ9, σ0, encSt, hstack8]
  by_cases h9 : j = 9
  · subst h9
    simp [τ9, σ0, encSt, hb9]
  by_cases h10 : j = 10
  · subst h10
    simp [τ9, σ0, encSt]
  by_cases h12 : j = 12
  · subst h12
    simp [τ9, σ0, encSt, hb12]
  by_cases h13 : j = 13
  · subst h13
    simp [τ9, σ0, encSt, hb13]
  by_cases h14 : j = 14
  · subst h14
    simp [τ9, σ0, encSt, hb14]
  simp [τ9, σ0, encSt, *]

/-- The encoding phase puts the six root fields on stack `8`, clears the temporary vectors,
and sets mode `3`, using at most `base.space + 30 * (LX.length + W + 1) ^ 2` space. -/
theorem exec_initEncodeProg (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ)
    (hbase : BaseOK base LX cs eb) :
    Exec initEncodeProg
      (Function.update (Function.update (Function.update
        (Function.update base 12 (List.replicate LX.length true)) 10
          (List.replicate LX.length false)) 13 (List.replicate W false)) 14
          (List.replicate (LX.length + 1) true))
      (encSt base W LX.length (3, [root LX.length]))
      (base.space + 30 * (LX.length + W + 1) ^ 2) := by
  obtain ⟨-, -, -, hb⟩ := hbase
  set m := LX.length with hm
  set S := base.space + 30 * (m + W + 1) ^ 2 with hS
  set σ0 : Stacks 38 := Function.update (Function.update (Function.update
    (Function.update base 12 (List.replicate m true)) 10
      (List.replicate m false)) 13 (List.replicate W false)) 14
      (List.replicate (m + 1) true) with hσ0def
  -- contents of σ0 at the relevant stacks
  have e8 : σ0 8 = [] := by
    rw [hσ0def, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact hb 8 (by decide)
  have e10 : σ0 10 = List.replicate m false := by
    rw [hσ0def, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have e12 : σ0 12 = List.replicate m true := by
    rw [hσ0def, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  have e13 : σ0 13 = List.replicate W false := by
    rw [hσ0def, Function.update_of_ne (by decide), Function.update_self]
  have e14 : σ0 14 = List.replicate (m + 1) true := by
    rw [hσ0def, Function.update_self]
  have e17 : σ0 17 = [] := by
    rw [hσ0def, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact hb 17 (by decide)
  -- the space of σ0
  have hspace0 : σ0.space = base.space + (3 * m + W + 1) := exec_initEncodeProg_space hb
  -- space of a single stack-8 update
  have hsp8 : ∀ pre : BitString,
      Stacks.space (Function.update σ0 8 pre) = σ0.space + pre.length := by
    intro pre
    have := Stacks.space_update σ0 8 pre
    rw [e8] at this
    simpa using this
  -- the needed space budget
  have hSbig : base.space + (11 * m + 5 * W + 12) ≤ S := by
    have hp : 11 * m + 5 * W + 12 ≤ 30 * (m + W + 1) ^ 2 := by
      have hpow : m + W + 1 ≤ (m + W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
    rw [hS]; omega
  -- the single-push contract in clean form
  have push8 : ∀ (Z : Fin 38) (w pre : BitString),
      Z ≠ (8 : Fin 38) → Z ≠ (17 : Fin 38) → σ0 Z = w →
      (σ0.space + pre.length + 2 * w.length + 1 ≤ S) →
      Exec (QEnum.pushCode Z 17 8) (Function.update σ0 8 pre)
        (Function.update σ0 8 (Stacks.encStr w ++ pre)) S := by
    intro Z w pre hZ8 hZ17 hw hbnd
    have ht : (Function.update σ0 8 pre) (17 : Fin 38) = [] := by
      rw [Function.update_of_ne (by decide : (17 : Fin 38) ≠ 8)]; exact e17
    have e := QEnum.exec_pushCode hZ17 hZ8 (by decide : (17 : Fin 38) ≠ (8 : Fin 38)) ht
    refine Stmt.exec_of_eq (e.mono ?_) ?_
    · rw [Function.update_of_ne hZ8, hw, hsp8 pre]; omega
    · simp only [Function.update_of_ne hZ8, Function.update_self, hw, Function.update_idem]
  -- rewrite the start state as a stack-8 update
  have hσ0' : Function.update σ0 8 [] = σ0 := by
    rw [← e8]; exact Function.update_eq_self 8 σ0
  rw [← hσ0']
  -- the six pushes
  refine .seq (push8 10 (List.replicate m false) [] (by decide) (by decide) e10 (by
      rw [hspace0]; simp only [List.length_nil, List.length_replicate]; omega))
    (.seq (push8 10 (List.replicate m false)
        (Stacks.encStr (List.replicate m false) ++ []) (by decide) (by decide) e10 (by
      rw [hspace0]; simp only [List.length_append, List.length_nil, Stacks.length_encStr,
        List.length_replicate]; omega))
    (.seq (push8 14 (List.replicate (m + 1) true)
        (Stacks.encStr (List.replicate m false) ++ (Stacks.encStr (List.replicate m false) ++ []))
        (by decide) (by decide) e14 (by
      rw [hspace0]; simp only [List.length_append, List.length_nil, Stacks.length_encStr,
        List.length_replicate]; omega))
    (.seq (push8 13 (List.replicate W false)
        (Stacks.encStr (List.replicate (m + 1) true) ++ (Stacks.encStr (List.replicate m false) ++
          (Stacks.encStr (List.replicate m false) ++ []))) (by decide) (by decide) e13 (by
      rw [hspace0]; simp only [List.length_append, List.length_nil, Stacks.length_encStr,
        List.length_replicate]; omega))
    (.seq (push8 13 (List.replicate W false)
        (Stacks.encStr (List.replicate W false) ++ (Stacks.encStr (List.replicate (m + 1) true) ++
          (Stacks.encStr (List.replicate m false) ++ (Stacks.encStr (List.replicate m false) ++
            [])))) (by decide) (by decide) e13 (by
      rw [hspace0]; simp only [List.length_append, List.length_nil, Stacks.length_encStr,
        List.length_replicate]; omega))
    (.seq (push8 12 (List.replicate m true)
        (Stacks.encStr (List.replicate W false) ++ (Stacks.encStr (List.replicate W false) ++
          (Stacks.encStr (List.replicate (m + 1) true) ++ (Stacks.encStr (List.replicate m false) ++
            (Stacks.encStr (List.replicate m false) ++ []))))) (by decide) (by decide) e12 (by
      rw [hspace0]; simp only [List.length_append, List.length_nil, Stacks.length_encStr,
        List.length_replicate]; omega))
      ?_)))))
  -- the final state after the six pushes
  set V6 : BitString := Stacks.encStr (List.replicate m true) ++
    (Stacks.encStr (List.replicate W false) ++ (Stacks.encStr (List.replicate W false) ++
      (Stacks.encStr (List.replicate (m + 1) true) ++ (Stacks.encStr (List.replicate m false) ++
        (Stacks.encStr (List.replicate m false) ++ []))))) with hV6def
  have hV6len : V6.length = 8 * m + 4 * W + 8 := by
    rw [hV6def]
    simp only [List.length_append, List.length_nil, Stacks.length_encStr, List.length_replicate]
    omega
  have hmax : Stacks.space (Function.update σ0 8 V6) ≤ S := by
    rw [hsp8 V6, hspace0, hV6len]; omega
  set τ9 : Stacks 38 := Function.update (Function.update (Function.update
    (Function.update σ0 8 V6) 12 []) 13 []) 14 [] with hτ9def
  -- the state after the clears has space below the budget
  have hτ9max : τ9.space ≤ Stacks.space (Function.update σ0 8 V6) := by
    rw [hτ9def]
    exact (Stacks.space_update_le _ 14 [] (by simp)).trans
      ((Stacks.space_update_le _ 13 [] (by simp)).trans
        (Stacks.space_update_le _ 12 [] (by simp)))
  have hple : τ9.space + 3 ≤ S := by
    rw [hsp8 V6, hspace0, hV6len] at hτ9max
    omega
  -- the pushList output equals the encoded root state
  have hfinaleq : Function.update τ9 9 (List.replicate 3 true ++ τ9 9)
      = encSt base W m (3, [root m]) := exec_initEncodeProg_finaleq hb
  have epl : Exec (Stmt.pushList 9 (List.replicate 3 true)) τ9
      (encSt base W m (3, [root m])) S :=
    Stmt.exec_of_eq ((Stmt.exec_pushList 9 (List.replicate 3 true) τ9).mono hple) hfinaleq
  -- clears and pushList
  exact .seq ((Stmt.exec_clear 12 _ _ rfl).mono hmax)
    (.seq ((Stmt.exec_clear 13 _ _ rfl).mono
        ((Stacks.space_update_le _ 12 [] (by simp)).trans hmax))
    (.seq ((Stmt.exec_clear 14 _ _ rfl).mono
        ((Stacks.space_update_le _ 13 [] (by simp)).trans
          ((Stacks.space_update_le _ 12 [] (by simp)).trans hmax)))
    (.seq epl (.skip epl.space_le.2))))

/-- An initializer sets up the root frame in mode `3` from the base contents, with space
overhead bounded by a constant times `(LX.length + W + 1) ^ 2`. -/
theorem exists_initStmt : ∃ (s : Stmt 38) (K : ℕ), ∀ (base : Stacks 38) (LX cs : List BitString)
    (eb : BitString) (W : ℕ), BaseOK base LX cs eb → eb.length = W →
    Exec s base (encSt base W LX.length (3, [root LX.length]))
      (base.space + K * (LX.length + W + 1) ^ 2) := by
  refine ⟨initProg, 30, ?_⟩
  intro base LX cs eb W hbase heb
  have e1 := exec_initCountProg base LX cs eb hbase
  have e2 := exec_initVectorProg base LX cs eb W hbase heb
  have e3 := exec_initEncodeProg base LX cs eb W hbase
  refine .seq (e1.mono (S' := base.space + 30 * (LX.length + W + 1) ^ 2) ?_)
    (.seq (e2.mono (S' := base.space + 30 * (LX.length + W + 1) ^ 2) (by omega)) e3)
  have hs : (LX.length + 1) ^ 2 ≤ (LX.length + W + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  omega

end DFS

end Kolmogorov.RandomStrings
