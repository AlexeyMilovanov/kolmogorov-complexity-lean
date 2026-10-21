/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSGame

/-!
# The depth-first search: the cost and inclusion tests

The two vector routines of the search: `DFS.costVStmt`, which sums the costs at the positions
selected by one bit vector and not by another (`DFS.exists_costVStmt`), and `DFS.isSubStmt`, the
inclusion test of two bit vectors (`DFS.exists_isSubStmt`).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- Produce a width-`W` zero accumulator on `19`, restoring stack `3` through work stack `23`. -/
def costVZeroStmt : Stmt 38 := .seq (Stmt.moveAll 3 23)
  (.loop 23 Option.isSome (QEnum.zeroStep 23 3 19))

/-- Copy the coded costs and the two masks to work stacks after initializing the accumulator. -/
def costVInitStmt : Stmt 38 := Stmt.seqs [costVZeroStmt, Stmt.copy 2 20 23,
  Stmt.copy 17 21 23, Stmt.copy 18 22 23]

/-- State at the start of the destructive cost fold. -/
def costVWorkSt (σ : Stacks 38) (W : ℕ) : Stacks 38 :=
  Function.update (Function.update (Function.update (Function.update σ 19
    (List.replicate W false)) 20 (σ 2)) 21 (σ 17)) 22 (σ 18)

/-- Decode one cost, advance the two masks when both have a bit, and add exactly when the move
sets a previously unset bit.  The adder uses stacks `27` and `28` for carry and reversal. -/
def costVBodyStmt : Stmt 38 := Stmt.seqs [Stmt.decodeOne 20 24 25, Stmt.moveAll 24 26,
  .ite 21 Option.isSome
    (Stmt.caseBit 21 fun a => .ite 22 Option.isSome
      (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
        if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
      (Stmt.clear 21))
    (Stmt.clear 26)]

/-- Fold all coded costs, then erase the consumed-list and decoding work stacks. -/
def costVLoopStmt : Stmt 38 := .seq (.loop 20 Option.isSome costVBodyStmt)
  (Stmt.seqs [Stmt.clear 20, Stmt.clear 21, Stmt.clear 22, Stmt.clear 23, Stmt.clear 24,
    Stmt.clear 25, Stmt.clear 26, Stmt.clear 27, Stmt.clear 28])

/-- The concrete cost routine consists of an initialization/copy phase and a destructive fold. -/
def costVStmt : Stmt 38 := .seq costVInitStmt costVLoopStmt

/-- The first initialization phase restores stack `3` after using `23` as a reversal stack and
puts the width-`W` zero accumulator on `19`.  Apply `Stmt.exec_moveAll`, followed by
`QEnum.exec_zeroLoop`; use emptiness of `19` and `23`, `h3`, and pointwise simplification of the
nested updates. -/
private theorem exec_costVZeroStmt_phase (σ : Stacks 38) (W : ℕ)
    (h3 : (σ 3).length = W) (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) (S : ℕ)
    (hS : σ.space + 16 * ((σ 2).length + (σ 17).length + (σ 18).length + W + 1) ≤ S) :
    Exec costVZeroStmt σ (Function.update σ 19 (List.replicate W false)) S := by
  have h19 := hempty (19 : Fin 38) (by omega)
  have h23 := hempty (23 : Fin 38) (by omega)
  let τ : Stacks 38 := Function.update (Function.update σ 3 []) 23 (σ 3).reverse
  have e1 : Exec (Stmt.moveAll 3 23) σ τ σ.space := by
    simpa [τ, h23] using
      (Stmt.exec_moveAll (k := 38) (r := 3) (r' := 23) (by decide) (σ 3) σ rfl)
  have ht : τ 23 = (σ 3).reverse := by simp [τ]
  have e2 := QEnum.exec_zeroLoop (k := 38) (t := 23) (r := 3) (r' := 19) (σ 3).reverse τ ht
  have hτ := e1.space_le.2
  refine Stmt.exec_of_eq (.seq (e1.mono (by omega)) (e2.mono ?_)) ?_
  · simp only [List.length_reverse]
    omega
  · funext j
    simp only [τ, Function.update_apply, List.reverse_reverse, List.length_reverse]
    split_ifs <;> subst_vars <;> simp_all

/-- The second initialization phase copies the coded costs from `2` to the empty work stack `20`,
using empty stack `23` as scratch.  Apply `Stmt.exec_copy`; compute the space of the preceding
update at `19` with `Stacks.space_update`, and simplify the distinct updates pointwise. -/
private theorem exec_costVCopyCosts_phase (σ : Stacks 38) (W : ℕ)
    (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) (S : ℕ)
    (hS : σ.space + 16 * ((σ 2).length + (σ 17).length + (σ 18).length + W + 1) ≤ S) :
    Exec (Stmt.copy 2 20 23) (Function.update σ 19 (List.replicate W false))
      (Function.update (Function.update σ 19 (List.replicate W false)) 20 (σ 2)) S := by
  let τ : Stacks 38 := Function.update σ 19 (List.replicate W false)
  have ht : τ 23 = [] := by simp [τ, hempty (23 : Fin 38) (by omega)]
  have h2 : τ 2 = σ 2 := by simp [τ]
  have h20 : τ 20 = [] := by simp [τ, hempty (20 : Fin 38) (by omega)]
  have hτ : τ.space = σ.space + W := by
    have hu := Stacks.space_update σ (19 : Fin 38) (List.replicate W false)
    rw [hempty (19 : Fin 38) (by omega)] at hu
    simp only [List.length_nil, List.length_replicate, Nat.add_zero] at hu
    omega
  have e := Stmt.exec_copy (k := 38) (r := 2) (r' := 20) (t := 23)
    (by decide) (by decide) (by decide) ht
  rw [h2, h20, List.append_nil] at e
  exact e.mono (by rw [hτ]; omega)

/-- The third initialization phase copies the first mask from `17` to the empty work stack `21`,
again using `23` as scratch.  Apply `Stmt.exec_copy`; two uses of `Stacks.space_update` give the
current space, and simplification shows that earlier updates do not change stacks `17`, `21`, or
`23`. -/
private theorem exec_costVCopyLeftMask_phase (σ : Stacks 38) (W : ℕ)
    (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) (S : ℕ)
    (hS : σ.space + 16 * ((σ 2).length + (σ 17).length + (σ 18).length + W + 1) ≤ S) :
    Exec (Stmt.copy 17 21 23)
      (Function.update (Function.update σ 19 (List.replicate W false)) 20 (σ 2))
      (Function.update (Function.update (Function.update σ 19 (List.replicate W false)) 20
        (σ 2)) 21 (σ 17)) S := by
  let τ₀ : Stacks 38 := Function.update σ 19 (List.replicate W false)
  let τ₁ : Stacks 38 := Function.update τ₀ 20 (σ 2)
  have h17 : τ₁ 17 = σ 17 := by simp [τ₁, τ₀]
  have h21 : τ₁ 21 = [] := by
    simp [τ₁, τ₀, hempty (21 : Fin 38) (by omega)]
  have ht : τ₁ 23 = [] := by
    simp [τ₁, τ₀, hempty (23 : Fin 38) (by omega)]
  have hτ₀ : τ₀.space = σ.space + W := by
    have hu := Stacks.space_update σ (19 : Fin 38) (List.replicate W false)
    rw [hempty (19 : Fin 38) (by omega)] at hu
    simp only [List.length_nil, List.length_replicate, Nat.add_zero] at hu
    omega
  have hτ₀20 : τ₀ 20 = [] := by
    simp [τ₀, hempty (20 : Fin 38) (by omega)]
  have hτ₁ : τ₁.space = τ₀.space + (σ 2).length := by
    have hu := Stacks.space_update τ₀ (20 : Fin 38) (σ 2)
    rw [hτ₀20] at hu
    simp only [List.length_nil, Nat.add_zero] at hu
    omega
  have e := Stmt.exec_copy (k := 38) (r := 17) (r' := 21) (t := 23)
    (by decide) (by decide) (by decide) ht
  rw [h17, h21, List.append_nil] at e
  exact e.mono (by rw [hτ₁, hτ₀]; omega)

/-- The last initialization phase copies the second mask from `18` to the empty work stack `22`,
using `23` as scratch.  Apply `Stmt.exec_copy`; compute the space after the three earlier updates
and simplify the distinct updates to identify the result with `costVWorkSt`. -/
private theorem exec_costVCopyRightMask_phase (σ : Stacks 38) (W : ℕ)
    (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) (S : ℕ)
    (hS : σ.space + 16 * ((σ 2).length + (σ 17).length + (σ 18).length + W + 1) ≤ S) :
    Exec (Stmt.copy 18 22 23)
      (Function.update (Function.update (Function.update σ 19 (List.replicate W false)) 20
        (σ 2)) 21 (σ 17)) (costVWorkSt σ W) S := by
  let τ₀ : Stacks 38 := Function.update σ 19 (List.replicate W false)
  let τ₁ : Stacks 38 := Function.update τ₀ 20 (σ 2)
  let τ₂ : Stacks 38 := Function.update τ₁ 21 (σ 17)
  have h18 : τ₂ 18 = σ 18 := by simp [τ₂, τ₁, τ₀]
  have h22 : τ₂ 22 = [] := by
    simp [τ₂, τ₁, τ₀, hempty (22 : Fin 38) (by omega)]
  have ht : τ₂ 23 = [] := by
    simp [τ₂, τ₁, τ₀, hempty (23 : Fin 38) (by omega)]
  have hτ₀ : τ₀.space = σ.space + W := by
    have hu := Stacks.space_update σ (19 : Fin 38) (List.replicate W false)
    rw [hempty (19 : Fin 38) (by omega)] at hu
    simp only [List.length_nil, List.length_replicate, Nat.add_zero] at hu
    omega
  have hτ₀20 : τ₀ 20 = [] := by
    simp [τ₀, hempty (20 : Fin 38) (by omega)]
  have hτ₁ : τ₁.space = τ₀.space + (σ 2).length := by
    have hu := Stacks.space_update τ₀ (20 : Fin 38) (σ 2)
    rw [hτ₀20] at hu
    simp only [List.length_nil, Nat.add_zero] at hu
    omega
  have hτ₁21 : τ₁ 21 = [] := by
    simp [τ₁, τ₀, hempty (21 : Fin 38) (by omega)]
  have hτ₂ : τ₂.space = τ₁.space + (σ 17).length := by
    have hu := Stacks.space_update τ₁ (21 : Fin 38) (σ 17)
    rw [hτ₁21] at hu
    simp only [List.length_nil, Nat.add_zero] at hu
    omega
  have e := Stmt.exec_copy (k := 38) (r := 18) (r' := 22) (t := 23)
    (by decide) (by decide) (by decide) ht
  rw [h18, h22, List.append_nil] at e
  exact e.mono (by rw [hτ₂, hτ₁, hτ₀]; omega)

/-- Use `Stmt.exec_moveAll` and `QEnum.exec_zeroLoop` for the first phase, then three applications
of `Stmt.exec_copy`.  Simplifying the updates gives `costVWorkSt`; the stated generous common
bound follows from the four individual space bounds. -/
theorem exec_costVInitStmt (σ : Stacks 38) (W : ℕ)
    (h3 : (σ 3).length = W) (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) (S : ℕ)
    (hS : σ.space + 16 * ((σ 2).length + (σ 17).length + (σ 18).length + W + 1) ≤ S) :
    Exec costVInitStmt σ (costVWorkSt σ W) S := by
  have e0 := exec_costVZeroStmt_phase σ W h3 hempty S hS
  have e1 := exec_costVCopyCosts_phase σ W hempty S hS
  have e2 := exec_costVCopyLeftMask_phase σ W hempty S hS
  have e3 := exec_costVCopyRightMask_phase σ W hempty S hS
  exact .seq e0 (.seq e1 (.seq e2 (.seq e3 (.skip e3.space_le.2))))

/-- The contribution of the current cost to the accumulator.  If either mask has ended, the
zipped definition of `costV` contributes zero. -/
private def costVStepCost (c : ℕ) : BitString → BitString → ℕ
  | a :: _, b :: _ => if b && !a then c else 0
  | _, _ => 0

/-- The unconsumed suffix of the left mask after one iteration of `costVBodyStmt`. -/
private def costVNextLeft : BitString → BitString → BitString
  | _ :: as, _ :: _ => as
  | _, _ => []

/-- The unconsumed suffix of the right mask after one iteration of `costVBodyStmt`. -/
private def costVNextRight : BitString → BitString → BitString
  | [], bs => bs
  | _ :: _, [] => []
  | _ :: _, _ :: bs => bs

/-- Decoder output left on stack `26`: only the branch where the right mask has ended leaves the
decoded cost pending; every other branch clears it or consumes it in the adder. -/
private def costVNextTmp (c : BitString) : BitString → BitString → BitString → BitString
  | [], _, _ => []
  | _ :: _, [], tmp => c ++ tmp
  | _ :: _, _ :: _, _ => []

/-- A pending decoder word can occur only after at least one mask has ended. -/
private def costVTmpOK (as bs tmp : BitString) : Prop := as ≠ [] → bs ≠ [] → tmp = []

/-- Peeling one cost and the available mask heads agrees with the three operational branches of
`costVBodyStmt`. -/
private theorem costV_cons_step (c : ℕ) (cs : List ℕ) (as bs : BitString) :
    costV (c :: cs) as bs = costVStepCost c as bs +
      costV cs (costVNextLeft as bs) (costVNextRight as bs) := by
  cases as with
  | nil => simp [costV, costVStepCost, costVNextLeft, costVNextRight]
  | cons a as =>
    cases bs with
    | nil => simp [costV, costVStepCost, costVNextLeft, costVNextRight]
    | cons b bs =>
      exact pv_costV_cons c cs a b as bs

/-- A generalized state for the destructive fold: `x` is the numeric accumulator, `cs` are the
costs not yet decoded, and `as`, `bs` are the unconsumed mask suffixes. -/
private def costVLoopState (σ : Stacks 38) (W x : ℕ) (cs : List BitString)
    (as bs hist tmp : BitString) :
    Stacks 38 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update σ 19 (numBits W x)) 20 (Stacks.encList cs)) 21 as) 22 bs) 25 hist) 26 tmp

/-- The generalized fold state replaces four initially empty work stacks, so its space is the
base space plus exactly the lengths of the accumulator, encoded suffix, and mask suffixes. -/
private theorem costVLoopState_space (σ : Stacks 38) (W x : ℕ) (cs : List BitString)
    (as bs hist tmp : BitString)
    (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) :
    (costVLoopState σ W x cs as bs hist tmp).space =
      σ.space + W + (Stacks.encList cs).length + as.length + bs.length + hist.length +
        tmp.length := by
  let τ₀ : Stacks 38 := Function.update σ 19 (numBits W x)
  let τ₁ : Stacks 38 := Function.update τ₀ 20 (Stacks.encList cs)
  let τ₂ : Stacks 38 := Function.update τ₁ 21 as
  let τ₃ : Stacks 38 := Function.update τ₂ 22 bs
  let τ₄ : Stacks 38 := Function.update τ₃ 25 hist
  let τ₅ : Stacks 38 := Function.update τ₄ 26 tmp
  have h₀ := Stacks.space_update σ (19 : Fin 38) (numBits W x)
  have h₁ := Stacks.space_update τ₀ (20 : Fin 38) (Stacks.encList cs)
  have h₂ := Stacks.space_update τ₁ (21 : Fin 38) as
  have h₃ := Stacks.space_update τ₂ (22 : Fin 38) bs
  have h₄ := Stacks.space_update τ₃ (25 : Fin 38) hist
  have h₅ := Stacks.space_update τ₄ (26 : Fin 38) tmp
  have e₀ : τ₀.space = σ.space + W := by
    simpa [τ₀, hempty (19 : Fin 38) (by omega), numBits] using h₀
  have e₁ : τ₁.space = τ₀.space + (Stacks.encList cs).length := by
    have ht : τ₀ 20 = [] := by simp [τ₀, hempty (20 : Fin 38) (by omega)]
    simpa [τ₁, ht] using h₁
  have e₂ : τ₂.space = τ₁.space + as.length := by
    have ht : τ₁ 21 = [] := by
      simp [τ₁, τ₀, hempty (21 : Fin 38) (by omega)]
    simpa [τ₂, ht] using h₂
  have e₃ : τ₃.space = τ₂.space + bs.length := by
    have ht : τ₂ 22 = [] := by
      simp [τ₂, τ₁, τ₀, hempty (22 : Fin 38) (by omega)]
    simpa [τ₃, ht] using h₃
  have e₄ : τ₄.space = τ₃.space + hist.length := by
    have ht : τ₃ 25 = [] := by
      simp [τ₃, τ₂, τ₁, τ₀, hempty (25 : Fin 38) (by omega)]
    simpa [τ₄, ht] using h₄
  have e₅ : τ₅.space = τ₄.space + tmp.length := by
    have ht : τ₄ 26 = [] := by
      simp [τ₄, τ₃, τ₂, τ₁, τ₀, hempty (26 : Fin 38) (by omega)]
    simpa [τ₅, ht] using h₅
  change τ₅.space = _
  omega

/-- Exposing the low bit of a fixed-width binary word leaves the remaining bits as the word for
the quotient by two. -/
private theorem numBits_succ (W n : ℕ) :
    numBits (W + 1) n = n.testBit 0 :: numBits W (n / 2) := by
  simp [numBits, List.range_succ_eq_map, List.map_map, Function.comp_def,
    Nat.testBit_add_one]

/-- A number below the width bound is recovered from its little-endian `numBits` word. -/
theorem binVal_numBits_of_lt : ∀ (W n : ℕ), n < 2 ^ W → binVal (numBits W n) = n
  | 0, n, h => by
    have hn : n = 0 := by simpa using h
    subst n
    rfl
  | W + 1, n, h => by
    rw [numBits_succ, binVal, binVal_numBits_of_lt W (n / 2)]
    · have hm := Nat.mod_add_div n 2
      have hr := Nat.mod_lt n (by omega : 0 < 2)
      rw [Nat.testBit_zero]
      have hz : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hz with hz | hz <;> simp [hz] <;> omega
    · apply (Nat.div_lt_iff_lt_mul (by omega)).2
      rw [pow_succ] at h
      omega

/-- Equal-length little-endian bit strings with the same numeric value are equal. -/
private theorem binVal_eq_of_length_eq : ∀ (l m : BitString), l.length = m.length →
    binVal l = binVal m → l = m
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: m, hlen, hval => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    cases a <;> cases b <;>
      simp only [binVal, Bool.toNat_false, zero_add, mul_eq_mul_left_iff,
        OfNat.ofNat_ne_zero, or_false, List.cons.injEq, true_and, Bool.toNat_true,
        Bool.false_eq_true, false_and, Bool.true_eq_false, Nat.add_left_cancel_iff] at hval ⊢
    · exact binVal_eq_of_length_eq l m hlen (by omega)
    · omega
    · omega
    · exact binVal_eq_of_length_eq l m hlen (by omega)

/-- Adding a width-`W` word to a `numBits` accumulator without overflow produces the canonical
`numBits` word for the numeric sum. -/
theorem addBits_numBits (W x : ℕ) (c : BitString) (hc : c.length = W)
    (hlt : x + binVal c < 2 ^ W) :
    addBits false (numBits W x) c = numBits W (x + binVal c) := by
  have hx : x < 2 ^ W := by omega
  have hlen : (numBits W x).length = c.length := by simp [numBits, hc]
  have hsum := binVal_addBits_of_lt (numBits W x) c hlen
    (by rw [binVal_numBits_of_lt W x hx]; simpa [numBits] using hlt)
  apply binVal_eq_of_length_eq
  · rw [length_addBits false (numBits W x) c hlen]
    simp [numBits]
  · rw [hsum, binVal_numBits_of_lt W x hx,
      binVal_numBits_of_lt W (x + binVal c) hlt]

/-- Execute one genuine iteration of the cost fold.  To prove this helper, apply
`Stmt.exec_decodeOne` to expose `c`, then `Stmt.exec_moveAll` to put it on stack `26`.  Split on
`as` and `bs`; the empty-mask branches use `Stmt.exec_clear`, while the two-head branch pops both
heads and either clears `26` or applies `Stmt.exec_addInto`.  In the selected branch,
`binVal_addBits_of_lt` and fixed-width injectivity identify the new accumulator with
`numBits W (x + c)`.  Simplify the distinct updates and use `costVLoopState_space` for the common
space bound. -/
private theorem exec_costVBody_step (σ : Stacks 38) (c : BitString) (cs : List BitString) (W x : ℕ)
    (as bs hist tmp : BitString) (hc : c.length = W) (htmp : costVTmpOK as bs tmp)
    (hlt : x + (binVal c + (cs.map binVal).sum) < 2 ^ W)
    (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) (S : ℕ)
    (hS : σ.space + 64 * ((Stacks.encList (c :: cs)).length + as.length + bs.length + W + 1) +
      hist.length + tmp.length ≤ S) :
    Exec costVBodyStmt (costVLoopState σ W x (c :: cs) as bs hist tmp)
      (costVLoopState σ W (x + costVStepCost (binVal c) as bs) cs
        (costVNextLeft as bs) (costVNextRight as bs) ((Stacks.encStr c).reverse ++ hist)
        (costVNextTmp c as bs tmp)) S := by
  let ρ₀ := costVLoopState σ W x (c :: cs) as bs hist tmp
  let ρ₁ := Function.update (Function.update (Function.update ρ₀ 20 (Stacks.encList cs)) 24
    c.reverse) 25 ((Stacks.encStr c).reverse ++ hist)
  let ρ₂ := Function.update (Function.update ρ₁ 24 []) 26 (c ++ tmp)
  let B := ρ₀.space + c.length
  have hB : B + 1 ≤ S := by
    dsimp only [B, ρ₀]
    rw [costVLoopState_space σ W x (c :: cs) as bs hist tmp hempty]
    omega
  have hBS : B ≤ S := by omega
  have h20 : ρ₀ 20 = Stacks.encStr c ++ Stacks.encList cs := by
    simp [ρ₀, costVLoopState, Stacks.encList]
  have ed₀ := Stmt.exec_decodeOne (k := 38) (Lst := 20) (W := 24) (Tmp := 25)
    (by decide) (by decide) (by decide) h20
  have ed : Exec (Stmt.decodeOne 20 24 25) ρ₀ ρ₁ B := by
    refine Stmt.exec_of_eq ed₀ ?_
    funext j
    fin_cases j <;> simp [ρ₁, ρ₀, costVLoopState, hempty]
  have h24 : ρ₁ 24 = c.reverse := by simp [ρ₁]
  have em₀ := Stmt.exec_moveAll (k := 38) (r := 24) (r' := 26) (by decide)
    c.reverse ρ₁ h24
  have em : Exec (Stmt.moveAll 24 26) ρ₁ ρ₂ B := by
    refine Stmt.exec_of_eq (em₀.mono ed.space_le.2) ?_
    funext j
    fin_cases j <;> simp [ρ₂, ρ₁, ρ₀, costVLoopState, hempty]
  have edS := ed.mono hBS
  have emS := em.mono hBS
  unfold costVBodyStmt
  cases as with
  | nil =>
    have h21 : ρ₂ 21 = [] := by simp [ρ₂, ρ₁, ρ₀, costVLoopState]
    have h26 : ρ₂ 26 = c ++ tmp := by simp [ρ₂]
    have ec := (Stmt.exec_clear (26 : Fin 38) (c ++ tmp) ρ₂ h26).mono emS.space_le.2
    have eb : Exec (.ite 21 Option.isSome
        (Stmt.caseBit 21 fun a => .ite 22 Option.isSome
          (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
            if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
          (Stmt.clear 21))
        (Stmt.clear 26)) ρ₂ (Function.update ρ₂ 26 []) S :=
      .iteF (by simp [h21]) ec
    refine Stmt.exec_of_eq (.seq edS (.seq emS (.seq eb (.skip eb.space_le.2)))) ?_
    funext j
    fin_cases j <;> simp [ρ₂, ρ₁, ρ₀, costVLoopState, costVStepCost,
      costVNextLeft, costVNextRight, costVNextTmp, hempty]
  | cons a as =>
    cases bs with
    | nil =>
      have h21 : ρ₂ 21 = a :: as := by simp [ρ₂, ρ₁, ρ₀, costVLoopState]
      have h22 : ρ₂ 22 = [] := by simp [ρ₂, ρ₁, ρ₀, costVLoopState]
      have ec := (Stmt.exec_clear (21 : Fin 38) (a :: as) ρ₂ h21).mono emS.space_le.2
      have ei : Exec (.ite 22 Option.isSome
          (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
            if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
          (Stmt.clear 21)) ρ₂ (Function.update ρ₂ 21 []) S :=
        .iteF (by simp [h22]) ec
      have ecase : Exec (Stmt.caseBit 21 fun a => .ite 22 Option.isSome
          (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
            if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
          (Stmt.clear 21)) ρ₂ (Function.update ρ₂ 21 []) S :=
        (Stmt.exec_caseBit h21).2 ei
      have eb : Exec (.ite 21 Option.isSome
          (Stmt.caseBit 21 fun a => .ite 22 Option.isSome
            (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
              if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
            (Stmt.clear 21))
          (Stmt.clear 26)) ρ₂ (Function.update ρ₂ 21 []) S :=
        .iteT (by simp [h21]) ecase
      refine Stmt.exec_of_eq (.seq edS (.seq emS (.seq eb (.skip eb.space_le.2)))) ?_
      funext j
      fin_cases j <;> simp [ρ₂, ρ₁, ρ₀, costVLoopState, costVStepCost,
        costVNextLeft, costVNextRight, costVNextTmp, hempty]
    | cons b bs =>
      have h21 : ρ₂ 21 = a :: as := by simp [ρ₂, ρ₁, ρ₀, costVLoopState]
      have h22 : ρ₂ 22 = b :: bs := by simp [ρ₂, ρ₁, ρ₀, costVLoopState]
      let ρ₃ := Function.update ρ₂ 21 as
      let ρ₄ := Function.update ρ₃ 22 bs
      have htmp0 : tmp = [] := htmp (by simp) (by simp)
      have ep₁ : Exec (.pop 21) ρ₂ ρ₃ B := by
        exact (Stmt.exec_pop_cons h21 (S := B) em.space_le.2)
      have h22' : ρ₃ 22 = b :: bs := by simp [ρ₃, h22]
      have ep₂ : Exec (.pop 22) ρ₃ ρ₄ B := by
        exact Stmt.exec_pop_cons h22' (S := B) ep₁.space_le.2
      have h19 : ρ₄ 19 = numBits W x := by
        simp [ρ₄, ρ₃, ρ₂, ρ₁, ρ₀, costVLoopState]
      have h26 : ρ₄ 26 = c := by simp [ρ₄, ρ₃, ρ₂, htmp0]
      have h27 : ρ₄ 27 = [] := by
        simp [ρ₄, ρ₃, ρ₂, ρ₁, ρ₀, costVLoopState, hempty (27 : Fin 38) (by omega)]
      have h28 : ρ₄ 28 = [] := by
        simp [ρ₄, ρ₃, ρ₂, ρ₁, ρ₀, costVLoopState, hempty (28 : Fin 38) (by omega)]
      by_cases hab : b && !a = true
      · have ha : a = false := by
          cases a <;> cases b <;> simp_all
        have hb : b = true := by
          cases a <;> cases b <;> simp_all
        have hadd₀ := Stmt.exec_addInto (k := 38) (A := 19) (B := 26) (Cy := 27) (R := 28)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by simp [numBits, hc]) h19 h26 h27 h28
        have hadd : Exec (Stmt.addInto 19 26 27 28) ρ₄
            (Function.update (Function.update ρ₄ 19 (numBits W (x + binVal c))) 26 []) S := by
          refine Stmt.exec_of_eq (hadd₀.mono ?_) ?_
          · have := ep₂.space_le.2
            omega
          · rw [addBits_numBits W x c hc (by omega)]
        have eops : Exec (Stmt.seqs [.pop 21, .pop 22, Stmt.addInto 19 26 27 28]) ρ₂
            (Function.update (Function.update ρ₄ 19 (numBits W (x + binVal c))) 26 []) S :=
          .seq (ep₁.mono (by omega)) (.seq (ep₂.mono (by omega))
            (.seq hadd (.skip hadd.space_le.2)))
        have ecase22 : Exec (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
            if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26]) ρ₂
            (Function.update (Function.update ρ₄ 19 (numBits W (x + binVal c))) 26 []) S := by
          rw [Stmt.exec_caseBit h22]
          simpa [ha, hb] using eops
        have ei : Exec (.ite 22 Option.isSome
            (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
              if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
            (Stmt.clear 21)) ρ₂
            (Function.update (Function.update ρ₄ 19 (numBits W (x + binVal c))) 26 []) S :=
          .iteT (by simp [h22]) ecase22
        have ecase21 : Exec (Stmt.caseBit 21 fun a => .ite 22 Option.isSome
            (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
              if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
            (Stmt.clear 21)) ρ₂
            (Function.update (Function.update ρ₄ 19 (numBits W (x + binVal c))) 26 []) S :=
          (Stmt.exec_caseBit h21).2 ei
        have eb : Exec (.ite 21 Option.isSome
            (Stmt.caseBit 21 fun a => .ite 22 Option.isSome
              (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
                if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
              (Stmt.clear 21))
            (Stmt.clear 26)) ρ₂
            (Function.update (Function.update ρ₄ 19 (numBits W (x + binVal c))) 26 []) S :=
          .iteT (by simp [h21]) ecase21
        refine Stmt.exec_of_eq (.seq edS (.seq emS (.seq eb (.skip eb.space_le.2)))) ?_
        funext j
        fin_cases j <;> simp [ρ₄, ρ₃, ρ₂, ρ₁, ρ₀, costVLoopState, costVStepCost,
          costVNextLeft, costVNextRight, costVNextTmp, ha, hb, htmp0, hempty]
      · have hab' : ¬(b = true ∧ a = false) := by
          rintro ⟨rfl, rfl⟩
          simp at hab
        have ecB := Stmt.exec_clear (26 : Fin 38) c ρ₄ h26
        have ec : Exec (Stmt.clear 26) ρ₄ (Function.update ρ₄ 26 []) S := ecB.mono (by
          have := ep₂.space_le.2
          omega)
        have eops : Exec (Stmt.seqs [.pop 21, .pop 22, Stmt.clear 26]) ρ₂
            (Function.update ρ₄ 26 []) S :=
          .seq (ep₁.mono (by omega)) (.seq (ep₂.mono (by omega))
            (.seq ec (.skip ec.space_le.2)))
        have ecase22 : Exec (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
            if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26]) ρ₂
            (Function.update ρ₄ 26 []) S := by
          rw [Stmt.exec_caseBit h22]
          simpa [hab'] using eops
        have ei : Exec (.ite 22 Option.isSome
            (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
              if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
            (Stmt.clear 21)) ρ₂ (Function.update ρ₄ 26 []) S :=
          .iteT (by simp [h22]) ecase22
        have ecase21 : Exec (Stmt.caseBit 21 fun a => .ite 22 Option.isSome
            (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
              if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
            (Stmt.clear 21)) ρ₂ (Function.update ρ₄ 26 []) S :=
          (Stmt.exec_caseBit h21).2 ei
        have eb : Exec (.ite 21 Option.isSome
            (Stmt.caseBit 21 fun a => .ite 22 Option.isSome
              (Stmt.caseBit 22 fun b => Stmt.seqs [.pop 21, .pop 22,
                if b && !a then Stmt.addInto 19 26 27 28 else Stmt.clear 26])
              (Stmt.clear 21))
            (Stmt.clear 26)) ρ₂ (Function.update ρ₄ 26 []) S :=
          .iteT (by simp [h21]) ecase21
        refine Stmt.exec_of_eq (.seq edS (.seq emS (.seq eb (.skip eb.space_le.2)))) ?_
        funext j
        fin_cases j <;> simp [ρ₄, ρ₃, ρ₂, ρ₁, ρ₀, costVLoopState, costVStepCost,
          costVNextLeft, costVNextRight, costVNextTmp, hab', htmp0, hempty]

/-- Induct over the still-coded cost suffix.  The one-step helper maintains the numeric
accumulator and advances exactly the mask suffixes consumed by that iteration; the existential
suffixes are all that the subsequent cleanup phase needs. -/
private theorem exec_costVFold_phase (σ : Stacks 38) (cs : List BitString) (W x : ℕ)
    (as bs hist tmp : BitString) (htmp : costVTmpOK as bs tmp)
    (hcs : ∀ c ∈ cs, c.length = W) (hlt : x + (cs.map binVal).sum < 2 ^ W)
    (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) (S : ℕ)
    (hS : σ.space + 64 * ((Stacks.encList cs).length + as.length + bs.length + W + 1) +
      hist.length + tmp.length ≤ S) :
    ∃ as' bs' hist' tmp', Exec (.loop 20 Option.isSome costVBodyStmt)
      (costVLoopState σ W x cs as bs hist tmp)
      (costVLoopState σ W (x + costV (cs.map binVal) as bs) [] as' bs' hist' tmp') S := by
  induction cs generalizing x as bs hist tmp with
  | nil =>
    refine ⟨as, bs, hist, tmp, Stmt.exec_of_eq (.loopF ?_ ?_) ?_⟩
    · rfl
    · rw [costVLoopState_space σ W x [] as bs hist tmp hempty]
      simp only [Stacks.encList, List.flatMap_nil, List.length_nil]
      omega
    · simp [costV, costVLoopState]
  | cons c cs ih =>
    have hc : c.length = W := hcs c (by simp)
    have hcs' : ∀ d ∈ cs, d.length = W := by
      intro d hd
      exact hcs d (by simp [hd])
    let d := costVStepCost (binVal c) as bs
    let as₁ := costVNextLeft as bs
    let bs₁ := costVNextRight as bs
    let hist₁ := (Stacks.encStr c).reverse ++ hist
    let tmp₁ := costVNextTmp c as bs tmp
    have hd : d ≤ binVal c := by
      dsimp [d]
      cases as with
      | nil => simp [costVStepCost]
      | cons a as =>
        cases bs with
        | nil => simp [costVStepCost]
        | cons b bs =>
          simp only [costVStepCost]
          split <;> omega
    have hlt' : (x + d) + (cs.map binVal).sum < 2 ^ W := by
      simp only [List.map_cons, List.sum_cons] at hlt
      omega
    have hS' : σ.space +
        64 * ((Stacks.encList cs).length + as₁.length + bs₁.length + W + 1) +
          hist₁.length + tmp₁.length ≤ S := by
      have henc : (Stacks.encList (c :: cs)).length =
          2 * W + 1 + (Stacks.encList cs).length := by
        simp [Stacks.encList, Stacks.length_encStr, hc]
      cases as <;> cases bs <;>
        simp [as₁, bs₁, hist₁, tmp₁, costVNextLeft, costVNextRight, costVNextTmp,
          Stacks.length_encStr] at * <;> omega
    have htmp' : costVTmpOK as₁ bs₁ tmp₁ := by
      cases as <;> cases bs <;>
        simp [costVTmpOK, as₁, bs₁, tmp₁, costVNextLeft, costVNextRight, costVNextTmp]
    have e₁ := exec_costVBody_step σ c cs W x as bs hist tmp hc htmp hlt hempty S hS
    obtain ⟨as', bs', hist', tmp', e₂⟩ :=
      ih (x + d) as₁ bs₁ hist₁ tmp₁ htmp' hcs' hlt' hS'
    refine ⟨as', bs', hist', tmp', Stmt.exec_of_eq (.loopT ?_ e₁ e₂) ?_⟩
    · simp [costVLoopState, Stacks.encList, Stacks.encStr]
    · have hcost : costV ((c :: cs).map binVal) as bs =
          d + costV (cs.map binVal) as₁ bs₁ := by
        simpa [d, as₁, bs₁] using costV_cons_step (binVal c) (cs.map binVal) as bs
      have hnum : x + d + costV (cs.map binVal) as₁ bs₁ =
          x + costV ((c :: cs).map binVal) as bs := by omega
      rw [hnum]

/-- Clear the nine fold work stacks at a common ambient space bound. -/
private theorem exec_costVCleanup_phase (τ : Stacks 38) (S : ℕ) (hS : τ.space ≤ S) :
    Exec (Stmt.seqs [Stmt.clear 20, Stmt.clear 21, Stmt.clear 22, Stmt.clear 23,
      Stmt.clear 24, Stmt.clear 25, Stmt.clear 26, Stmt.clear 27, Stmt.clear 28]) τ
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update τ 20 []) 21 []) 22 [])
          23 []) 24 []) 25 []) 26 []) 27 []) 28 []) S := by
  let τ₂₀ := Function.update τ 20 []
  let τ₂₁ := Function.update τ₂₀ 21 []
  let τ₂₂ := Function.update τ₂₁ 22 []
  let τ₂₃ := Function.update τ₂₂ 23 []
  let τ₂₄ := Function.update τ₂₃ 24 []
  let τ₂₅ := Function.update τ₂₄ 25 []
  let τ₂₆ := Function.update τ₂₅ 26 []
  let τ₂₇ := Function.update τ₂₆ 27 []
  let τ₂₈ := Function.update τ₂₇ 28 []
  have e₂₀ := (Stmt.exec_clear (20 : Fin 38) (τ 20) τ rfl).mono hS
  have e₂₁ := (Stmt.exec_clear (21 : Fin 38) (τ₂₀ 21) τ₂₀ rfl).mono e₂₀.space_le.2
  have e₂₂ := (Stmt.exec_clear (22 : Fin 38) (τ₂₁ 22) τ₂₁ rfl).mono e₂₁.space_le.2
  have e₂₃ := (Stmt.exec_clear (23 : Fin 38) (τ₂₂ 23) τ₂₂ rfl).mono e₂₂.space_le.2
  have e₂₄ := (Stmt.exec_clear (24 : Fin 38) (τ₂₃ 24) τ₂₃ rfl).mono e₂₃.space_le.2
  have e₂₅ := (Stmt.exec_clear (25 : Fin 38) (τ₂₄ 25) τ₂₄ rfl).mono e₂₄.space_le.2
  have e₂₆ := (Stmt.exec_clear (26 : Fin 38) (τ₂₅ 26) τ₂₅ rfl).mono e₂₅.space_le.2
  have e₂₇ := (Stmt.exec_clear (27 : Fin 38) (τ₂₆ 27) τ₂₆ rfl).mono e₂₆.space_le.2
  have e₂₈ := (Stmt.exec_clear (28 : Fin 38) (τ₂₇ 28) τ₂₇ rfl).mono e₂₇.space_le.2
  exact .seq e₂₀ (.seq e₂₁ (.seq e₂₂ (.seq e₂₃ (.seq e₂₄ (.seq e₂₅
    (.seq e₂₆ (.seq e₂₇ (.seq e₂₈ (.skip e₂₈.space_le.2)))))))))

/-- Prove this by induction on `cs`, maintaining the accumulator value and the unconsumed suffixes
of both masks.  One `Stmt.exec_decodeOne` exposes the next width-`W` cost; split on the mask heads,
and in the selected case use `Stmt.exec_addInto` plus `binVal_addBits_of_lt`. -/
theorem exec_costVLoopStmt (σ : Stacks 38) (cs : List BitString) (W : ℕ)
    (h2 : σ 2 = Stacks.encList cs) (hcs : ∀ c ∈ cs, c.length = W)
    (hsum : (cs.map binVal).sum < 2 ^ W)
    (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) (S : ℕ)
    (hS : σ.space + 64 * ((Stacks.encList cs).length + (σ 17).length +
      (σ 18).length + W + 1) ≤ S) :
    Exec costVLoopStmt (costVWorkSt σ W)
      (Function.update σ 19 (numBits W (costV (cs.map binVal) (σ 17) (σ 18)))) S := by
  obtain ⟨as', bs', hist', tmp', e₁⟩ := exec_costVFold_phase σ cs W 0 (σ 17) (σ 18)
    [] [] (by simp [costVTmpOK]) hcs (by simpa using hsum) hempty S (by simpa using hS)
  let τ := costVLoopState σ W (costV (cs.map binVal) (σ 17) (σ 18)) [] as' bs' hist' tmp'
  have hstart : costVLoopState σ W 0 cs (σ 17) (σ 18) [] [] = costVWorkSt σ W := by
    funext j
    fin_cases j <;> simp [costVLoopState, costVWorkSt, numBits, h2, hempty]
  have e₁' : Exec (.loop 20 Option.isSome costVBodyStmt) (costVWorkSt σ W) τ S := by
    simpa [τ, hstart] using e₁
  have e₂ := exec_costVCleanup_phase τ S e₁'.space_le.2
  unfold costVLoopStmt
  refine Stmt.exec_of_eq (.seq e₁' e₂) ?_
  funext j
  fin_cases j <;> simp [τ, costVLoopState, hempty]

/-- **Sub-contract: the cost of a move** (remaining): with the costs `encList cs` (width `W`) on
`2`, a string of width `W` on `3` (the budget, giving the width when `cs = []`), `a` on `17`, `b`
on `18` and stacks `19`–`37` empty, push `numBits W (costV … a b)` on `19`. -/
theorem exists_costVStmt : ∃ (s : Stmt 38) (K : ℕ), ∀ (σ : Stacks 38) (cs : List BitString) (W : ℕ),
    σ 2 = Stacks.encList cs → (∀ c ∈ cs, c.length = W) → (σ 3).length = W →
    (cs.map binVal).sum < 2 ^ W → (∀ j : Fin 38, 19 ≤ j.val → σ j = []) →
    Exec s σ (Function.update σ 19 (numBits W (costV (cs.map binVal) (σ 17) (σ 18))))
      (σ.space + K * ((Stacks.encList cs).length + (σ 17).length + (σ 18).length + W + 1)) := by
  refine ⟨costVStmt, 64, fun σ cs W h2 hcs h3 hsum he => ?_⟩
  let S := σ.space + 64 * ((Stacks.encList cs).length + (σ 17).length +
    (σ 18).length + W + 1)
  have hi := exec_costVInitStmt σ W h3 he S (by rw [h2]; omega)
  have hl := exec_costVLoopStmt σ cs W h2 hcs hsum he S le_rfl
  exact .seq hi hl

/-- Copy the two compared strings to `20` and `21`, leaving a true accumulator flag on `19`. -/
def isSubInitStmt : Stmt 38 := Stmt.seqs [Stmt.copy 17 20 22, Stmt.copy 18 21 22,
  .push 19 true]

/-- Consume aligned bits from the two work copies.  If the right copy ends first, the remaining
left bits are irrelevant because `List.zip` stops at the shorter input. -/
def isSubWorkStmt : Stmt 38 := .seq
  (.loop 20 Option.isSome (Stmt.caseBit 20 fun a => .ite 21 Option.isSome
    (Stmt.caseBit 21 fun b => Stmt.seqs [.pop 20, .pop 21,
      if !a || b then .skip else Stmt.clearFlag 19])
    (Stmt.clear 20)))
  (Stmt.clear 21)

/-- The concrete inclusion routine copies its inputs and folds the pointwise implication. -/
def isSubStmt : Stmt 38 := .seq isSubInitStmt isSubWorkStmt

/-- Apply `Stmt.exec_copy` twice and one `Exec.push`; both copy work stacks are empty by the global
precondition.  Simplify their updates to obtain the displayed work state, and raise each phase to
the common linear bound. -/
theorem exec_isSubInitStmt (σ : Stacks 38)
    (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = []) (S : ℕ)
    (hS : σ.space + 8 * ((σ 17).length + (σ 18).length + 1) ≤ S) :
    Exec isSubInitStmt σ
      (Function.update (Function.update (Function.update σ 19 [true]) 20 (σ 17)) 21 (σ 18)) S := by
  change Exec (Stmt.seqs [Stmt.copy 17 20 22, Stmt.copy 18 21 22, Stmt.push 19 true]) _ _ _
  rw [Stmt.exec_seqs_cons]
  have e1 : Exec (Stmt.copy 17 20 22) σ (Function.update σ 20 (σ 17 ++ σ 20))
      (σ.space + (σ 17).length) := by
    apply Stmt.exec_copy
    · decide
    · decide
    · decide
    · apply hempty; decide
  have hz20 : σ 20 = [] := hempty 20 (by decide)
  rw [hz20, List.append_nil] at e1
  refine ⟨Function.update σ 20 (σ 17), e1.mono ?_, ?_⟩
  · omega
  rw [Stmt.exec_seqs_cons]
  have e2 : Exec (Stmt.copy 18 21 22) (Function.update σ 20 (σ 17))
      (Function.update (Function.update σ 20 (σ 17)) 21
        ((Function.update σ 20 (σ 17)) 18 ++ (Function.update σ 20 (σ 17)) 21))
      (Stacks.space (Function.update σ 20 (σ 17)) + ((Function.update σ 20 (σ 17)) 18).length) := by
    apply Stmt.exec_copy
    · decide
    · decide
    · decide
    · have h : 19 ≤ (22 : Fin 38).val := by decide
      have h2 := hempty 22 h
      simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, h2]
  have hz21 : (Function.update σ 20 (σ 17)) 21 = [] := by
    rw [Function.update]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceDIte]
    apply hempty; decide
  rw [hz21, List.append_nil] at e2
  have h_18 : (Function.update σ 20 (σ 17)) 18 = σ 18 := by
    rw [Function.update]
    simp
  rw [h_18] at e2
  refine ⟨Function.update (Function.update σ 20 (σ 17)) 21 (σ 18), e2.mono ?_, ?_⟩
  · have hspace : Stacks.space (Function.update σ 20 (σ 17)) + (σ 18).length =
        σ.space + (σ 17).length - (σ 20).length + (σ 18).length := by
      have hs1 : Stacks.space (Function.update σ 20 (σ 17)) + (σ 20).length =
          σ.space + (σ 17).length := Stacks.space_update σ 20 (σ 17)
      rw [hz20] at hs1
      simp only [Fin.isValue, List.length_nil, add_zero] at hs1
      rw [hs1]
      rw [hz20]
      simp
    rw [hspace]
    omega
  have e3 : Exec (Stmt.push 19 true) (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18))
      (Function.update (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) 19
        (true :: (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) 19)) S := by
    apply Exec.push
    have hspace2 : Stacks.space (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) =
        σ.space + (σ 17).length + (σ 18).length := by
      have hs2 : Stacks.space (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) +
          ((Function.update σ 20 (σ 17)) 21).length =
          Stacks.space (Function.update σ 20 (σ 17)) + (σ 18).length :=
        Stacks.space_update (Function.update σ 20 (σ 17)) 21 (σ 18)
      rw [hz21] at hs2
      simp only [Fin.isValue, List.length_nil, add_zero] at hs2
      have hs1 : Stacks.space (Function.update σ 20 (σ 17)) + (σ 20).length =
          σ.space + (σ 17).length := Stacks.space_update σ 20 (σ 17)
      rw [hz20] at hs1
      simp only [Fin.isValue, List.length_nil, add_zero] at hs1
      rw [hs1] at hs2
      exact hs2
    rw [hspace2]
    omega
  have hz19 : (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) 19 = [] := by
    rw [Function.update, Function.update]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceDIte]
    apply hempty; decide
  rw [hz19] at e3
  have e4 : Exec Stmt.skip
      (Function.update (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) 19 [true])
      (Function.update (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) 19 [true]) S := by
    apply Exec.skip
    have hspace3 : Stacks.space (Function.update (Function.update (Function.update σ 20 (σ 17))
        21 (σ 18)) 19 [true]) = σ.space + (σ 17).length + (σ 18).length + 1 := by
      have hs3 : Stacks.space (Function.update (Function.update (Function.update σ 20 (σ 17)) 21
          (σ 18)) 19 [true]) + ((Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) 19).length
          = Stacks.space (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) + 1 :=
        Stacks.space_update (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) 19 [true]
      rw [hz19] at hs3
      simp only [Fin.isValue, List.length_nil, add_zero] at hs3
      have hs2 : Stacks.space (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) +
          ((Function.update σ 20 (σ 17)) 21).length =
          Stacks.space (Function.update σ 20 (σ 17)) + (σ 18).length :=
        Stacks.space_update (Function.update σ 20 (σ 17)) 21 (σ 18)
      rw [hz21] at hs2
      simp only [Fin.isValue, List.length_nil, add_zero] at hs2
      have hs1 : Stacks.space (Function.update σ 20 (σ 17)) + (σ 20).length =
          σ.space + (σ 17).length := Stacks.space_update σ 20 (σ 17)
      rw [hz20] at hs1
      simp only [Fin.isValue, List.length_nil, add_zero] at hs1
      rw [hs1] at hs2
      rw [hs2] at hs3
      exact hs3
    rw [hspace3]
    omega
  have h_eq : Function.update (Function.update (Function.update σ 19 [true]) 20 (σ 17)) 21 (σ 18) =
      Function.update (Function.update (Function.update σ 20 (σ 17)) 21 (σ 18)) 19 [true] := by
    funext j
    by_cases h19 : j = 19
    · subst h19
      simp [Function.update]
    by_cases h20 : j = 20
    · subst h20
      simp [Function.update]
    by_cases h21 : j = 21
    · subst h21
      simp [Function.update]
    · simp [Function.update, h19, h20, h21]
  rw [h_eq]
  rw [Stmt.exec_seqs_cons]
  refine ⟨_, e3, ?_⟩
  exact e4

/-- The destructive loop underlying `isSubWorkStmt`.  Induct on `l` and split on `m`.  When both
strings are nonempty, use `Stmt.exec_caseBit` twice, pop both heads, update the flag by
`f && (!a || b)`, and invoke the induction hypothesis.  When only `l` is nonempty, execute the
`Stmt.clear 20` branch; this is exactly the stopping behavior of `List.zip`. -/
private theorem exec_isSubWorkLoop :
    ∀ (l m : BitString) (f : Bool) (σ : Stacks 38), σ 20 = l → σ 21 = m → σ 19 = [f] →
      Exec (.loop 20 Option.isSome (Stmt.caseBit 20 fun a => .ite 21 Option.isSome
        (Stmt.caseBit 21 fun b => Stmt.seqs [.pop 20, .pop 21,
          if !a || b then .skip else Stmt.clearFlag 19])
        (Stmt.clear 20))) σ
        (Function.update (Function.update (Function.update σ 20 []) 21 (m.drop l.length)) 19
          [f && isSub l m]) σ.space
  | [], m, f, σ, h20, h21, h19 => by
    refine Stmt.exec_of_eq (.loopF (by simp [h20]) le_rfl) ?_
    funext j
    simp only [Function.update_apply, List.length_nil, List.drop_zero]
    split_ifs <;> subst_vars <;> simp_all [isSub]
  | a :: l, [], f, σ, h20, h21, h19 => by
    have ec := Stmt.exec_clear 20 (a :: l) σ h20
    have hl : Exec (.loop 20 Option.isSome (Stmt.caseBit 20 fun a => .ite 21 Option.isSome
        (Stmt.caseBit 21 fun b => Stmt.seqs [.pop 20, .pop 21,
          if !a || b then .skip else Stmt.clearFlag 19])
        (Stmt.clear 20))) (Function.update σ 20 []) (Function.update σ 20 []) σ.space :=
      .loopF (by simp) ec.space_le.2
    refine Stmt.exec_of_eq (.loopT (by simp [h20]) ?_ hl) ?_
    · rw [Stmt.exec_caseBit h20]
      exact .iteF (by simp [h21]) ec
    · funext j
      simp only [Function.update_apply, List.length_cons, List.drop_nil]
      split_ifs <;> subst_vars <;> simp_all [isSub]
  | a :: l, b :: m, f, σ, h20, h21, h19 => by
    have e20 := Stmt.exec_pop_cons h20 (S := σ.space) le_rfl
    have h21' : (Function.update σ 20 l) 21 = b :: m := by simpa using h21
    have e21 := Stmt.exec_pop_cons h21' e20.space_le.2
    let τ := Function.update (Function.update σ 20 l) 21 m
    have h19' : τ 19 = [f] := by simp [τ, h19]
    have hτ : Stacks.space τ ≤ σ.space := e21.space_le.2
    have ef : Exec (if !a || b then .skip else Stmt.clearFlag 19) τ
        (Function.update τ 19 [f && (!a || b)]) σ.space := by
      cases a <;> cases b
      · simpa [← h19', Function.update_eq_self] using Exec.skip hτ
      · simpa [← h19', Function.update_eq_self] using Exec.skip hτ
      · simpa using (Stmt.exec_clearFlag h19').mono hτ
      · simpa [← h19', Function.update_eq_self] using Exec.skip hτ
    have hbody : Exec (Stmt.caseBit 20 fun a => .ite 21 Option.isSome
        (Stmt.caseBit 21 fun b => Stmt.seqs [.pop 20, .pop 21,
          if !a || b then .skip else Stmt.clearFlag 19])
        (Stmt.clear 20)) σ (Function.update τ 19 [f && (!a || b)]) σ.space := by
      rw [Stmt.exec_caseBit h20]
      refine .iteT (by simp [h21]) ?_
      rw [Stmt.exec_caseBit h21]
      exact .seq e20 (.seq e21 (.seq ef (.skip ef.space_le.2)))
    have ih := exec_isSubWorkLoop l m (f && (!a || b))
      (Function.update τ 19 [f && (!a || b)])
      (by simp [τ]) (by simp [τ]) (by simp)
    refine .loopT (by simp [h20]) hbody (Stmt.exec_of_eq (ih.mono hbody.space_le.2) ?_)
    funext j
    simp only [τ, Function.update_apply, List.length_cons, List.drop_succ_cons]
    split_ifs <;> subst_vars <;> simp_all [isSub, Bool.and_assoc]

/-- Induct on the copied left string and case-split on the copied right string.  The nonempty case
uses `Stmt.exec_caseBit` twice and updates the flag by conjunction with `!a || b`; the empty case
clears the unused left suffix, matching the stopping behavior of `List.zip`. -/
theorem exec_isSubWorkStmt (σ : Stacks 38) (S : ℕ)
    (hempty : ∀ j : Fin 38, 19 ≤ j.val → σ j = [])
    (hS : σ.space + 8 * ((σ 17).length + (σ 18).length + 1) ≤ S) :
    Exec isSubWorkStmt
      (Function.update (Function.update (Function.update σ 19 [true]) 20 (σ 17)) 21 (σ 18))
      (Function.update σ 19 [isSub (σ 17) (σ 18)]) S := by
  unfold isSubWorkStmt
  let τ := Function.update (Function.update (Function.update σ 19 [true]) 20 (σ 17)) 21
    (σ 18)
  have h20 : τ 20 = σ 17 := by simp [τ]
  have h21 : τ 21 = σ 18 := by simp [τ]
  have h19 : τ 19 = [true] := by simp [τ]
  have eloop := exec_isSubWorkLoop (σ 17) (σ 18) true τ h20 h21 h19
  have hτS : Stacks.space τ ≤ S := by
    have hi := (exec_isSubInitStmt σ hempty S hS).space_le.2
    simpa [τ] using hi
  let τ' := Function.update (Function.update (Function.update τ 20 []) 21
    ((σ 18).drop (σ 17).length)) 19 [isSub (σ 17) (σ 18)]
  have hloop' : Exec (.loop 20 Option.isSome (Stmt.caseBit 20 fun a => .ite 21 Option.isSome
      (Stmt.caseBit 21 fun b => Stmt.seqs [.pop 20, .pop 21,
        if !a || b then .skip else Stmt.clearFlag 19])
      (Stmt.clear 20))) τ τ' S := by
    simpa [τ'] using eloop.mono hτS
  have ec := Stmt.exec_clear 21 (τ' 21) τ' rfl
  refine .seq hloop' (Stmt.exec_of_eq (ec.mono hloop'.space_le.2) ?_)
  funext j
  simp only [τ', τ, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- **Sub-contract: the inclusion test** (remaining): with `a` on `17`, `b` on `18` and stacks
`19`–`37` empty, push `[isSub a b]` on `19`. -/
theorem exists_isSubStmt : ∃ (s : Stmt 38) (K : ℕ), ∀ σ : Stacks 38,
    (∀ j : Fin 38, 19 ≤ j.val → σ j = []) →
    Exec s σ (Function.update σ 19 [isSub (σ 17) (σ 18)])
      (σ.space + K * ((σ 17).length + (σ 18).length + 1)) := by
  refine ⟨isSubStmt, 8, fun σ he => ?_⟩
  let S := σ.space + 8 * ((σ 17).length + (σ 18).length + 1)
  exact .seq (exec_isSubInitStmt σ he S le_rfl) (exec_isSubWorkStmt σ S he le_rfl)

end DFS
end Kolmogorov.RandomStrings
