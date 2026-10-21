/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.Stmt

/-!
# Basic stack routines

Generic statements over stacks and their contracts: moving and copying stacks, fixed-point dyadic
arithmetic (`binVal`, `addInto`, `cmpInto`), frames and a loop rule with a variant, the equality
test of two stacks, and binary increment (`Stmt.incr`, used to enumerate subsets and answer
vectors as counters).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-! #### Basic stack routines -/

namespace Stmt

variable {k : ℕ}

/-- The condition "the top of the stack is `true`". -/
def isTrue (o : Option Bool) : Bool := o == some true

/-- Sequential composition of a list of statements. -/
def seqs : List (Stmt k) → Stmt k
  | [] => .skip
  | s :: l => .seq s (seqs l)

/-- Branch on the top bit of `r` (an empty stack counts as `false`). -/
def caseBit (r : Fin k) (s : Bool → Stmt k) : Stmt k := .ite r isTrue (s true) (s false)

/-- Empty the stack `r`. -/
def clear (r : Fin k) : Stmt k := .loop r Option.isSome (.pop r)

/-- Move the top bit of `r` onto `r'`. -/
def moveBit (r r' : Fin k) : Stmt k := caseBit r fun b => .seq (.pop r) (.push r' b)

/-- Move the whole content of `r` onto `r'`, bit by bit (so it arrives reversed). -/
def moveAll (r r' : Fin k) : Stmt k := .loop r Option.isSome (moveBit r r')

/-- Executing a sequence of statements `s :: l` is equivalent to executing `s` then `seqs l`. -/
theorem exec_seqs_cons {s : Stmt k} {l : List (Stmt k)} {σ σ' : Stacks k} {S : ℕ} :
    Exec (seqs (s :: l)) σ σ' S ↔ ∃ σ₁, Exec s σ σ₁ S ∧ Exec (seqs l) σ₁ σ' S :=
  Exec.seq_iff

/-- Executing `caseBit r s` with `r` starting with `b` is equivalent to executing `s b`. -/
theorem exec_caseBit {r : Fin k} {s : Bool → Stmt k} {σ σ' : Stacks k} {S : ℕ} {b : Bool}
    {l : BitString} (hσ : σ r = b :: l) : Exec (caseBit r s) σ σ' S ↔ Exec (s b) σ σ' S := by
  unfold caseBit
  rw [Exec.ite_iff]
  cases b <;> simp [hσ, isTrue]

/-- Popping from a stack updates it to its tail. -/
theorem exec_pop_cons {r : Fin k} {σ : Stacks k} {b : Bool} {l : BitString} (hσ : σ r = b :: l)
    {S : ℕ} (hS : σ.space ≤ S) : Exec (.pop r) σ (Function.update σ r l) S := by
  have := Exec.pop (r := r) (σ := σ) (S := S) hS
  rwa [hσ] at this

/-- Updating a stack with a one-element smaller list reduces the space sum by 1. -/
theorem space_update_of_cons {σ : Stacks k} {r : Fin k} {b : Bool} {l : BitString}
    (hσ : σ r = b :: l) : Stacks.space (Function.update σ r l) + 1 = σ.space := by
  have := σ.space_update r l
  rw [hσ, List.length_cons] at this
  omega

/-- `clear r` empties `r` within the initial space. -/
theorem exec_clear (r : Fin k) : ∀ (l : BitString) (σ : Stacks k), σ r = l →
    Exec (clear r) σ (Function.update σ r []) σ.space := by
  intro l
  induction l with
  | nil =>
    intro σ hσ
    have e : Function.update σ r [] = σ := by rw [← hσ, Function.update_eq_self]
    rw [e]
    exact .loopF (by simp [hσ]) le_rfl
  | cons b l ih =>
    intro σ hσ
    have h1 := exec_pop_cons hσ (S := σ.space) le_rfl
    have h2 := ih (Function.update σ r l) (by simp)
    rw [Function.update_idem] at h2
    exact .loopT (by simp [hσ]) h1 (h2.mono (by have := space_update_of_cons hσ; omega))

/-- `moveBit r r'` moves the top bit of `r` onto `r'`, within the initial space. -/
theorem exec_moveBit {r r' : Fin k} (hrr : r ≠ r') {σ : Stacks k} {b : Bool} {l : BitString}
    (hσ : σ r = b :: l) :
    Exec (moveBit r r') σ (Function.update (Function.update σ r l) r' (b :: σ r')) σ.space := by
  rw [moveBit, exec_caseBit hσ]
  have hsp := space_update_of_cons hσ
  have hpop := exec_pop_cons hσ (S := σ.space) le_rfl
  have hr' : (Function.update σ r l) r' = σ r' := Function.update_of_ne hrr.symm _ _
  have hpush := Exec.push (r := r') (b := b) (σ := Function.update σ r l) (S := σ.space)
    (by omega)
  rw [hr'] at hpush
  exact .seq hpop hpush

/-- `moveAll r r'` moves the content of `r`, reversed, on top of `r'`, within the initial
space. -/
theorem exec_moveAll {r r' : Fin k} (hrr : r ≠ r') : ∀ (l : BitString) (σ : Stacks k), σ r = l →
    Exec (moveAll r r') σ
      (Function.update (Function.update σ r []) r' (l.reverse ++ σ r')) σ.space := by
  intro l
  induction l with
  | nil =>
    intro σ hσ
    have e : Function.update (Function.update σ r []) r' ([].reverse ++ σ r') = σ := by
      funext j
      simp only [Function.update_apply, List.reverse_nil, List.nil_append]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    rw [e]
    exact .loopF (by simp [hσ]) le_rfl
  | cons b l ih =>
    intro σ hσ
    have h1 := exec_moveBit hrr hσ
    have h2 := ih (Function.update (Function.update σ r l) r' (b :: σ r'))
      (by rw [Function.update_of_ne hrr, Function.update_self])
    have e : Function.update (Function.update (Function.update (Function.update σ r l) r'
        (b :: σ r')) r []) r' (l.reverse ++ (Function.update (Function.update σ r l) r'
          (b :: σ r')) r') =
        Function.update (Function.update σ r []) r' ((b :: l).reverse ++ σ r') := by
      funext j
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> subst_vars <;> simp_all
    rw [e] at h2
    exact .loopT (by simp [hσ]) h1 (h2.mono h1.space_le.2)

end Stmt

/-! #### Fixed-point dyadic arithmetic on stacks

A dyadic number `a / 2 ^ N` (`a : ℕ`; precision `N`) is stored as a bit string `l` with
`binVal l = a`, least significant bit on top of the stack; all the numbers of one computation use
a common width `W` (for the game: `N ≥ 2 · clock + 6` and `N ≥` the budget exponent `m` and the
table values, so every flip cost `2⁻¹ ^ (|z| - 1) - 2⁻¹ ^ h z` with `|z| ≤ clock` is a multiple of
`2⁻¹ ^ N`; `W = N + clock + 3` leaves room for the sums of at most `2 ^ (clock + 1)` costs, each
`≤ 1`).  `fixVal N l = binVal l / 2 ^ N` is the represented real; `powBits W j` represents
`2 ^ j / 2 ^ N`, in particular `fixVal N (powBits W (N - b)) = 2⁻¹ ^ b` for `b ≤ N`.
`addInto` (`A := A + B`) and `cmpInto` (`O := [A ≤ B]`) work in space linear in `W`. -/

/-- The number denoted by a bit string, least significant bit first. -/
def binVal : BitString → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * binVal l

/-- The real number `binVal l / 2 ^ N` represented by `l` at precision `N`. -/
noncomputable def fixVal (N : ℕ) (l : BitString) : ℝ := (binVal l : ℝ) / 2 ^ N

/-- The binary value of `l ++ m` is the binary value of `l` plus `2 ^ l.length` times the
binary value of `m`. -/
theorem binVal_append (l m : BitString) : binVal (l ++ m) = binVal l + 2 ^ l.length * binVal m := by
  induction l with
  | nil => simp [binVal]
  | cons b l ih => simp only [List.cons_append, binVal, ih, List.length_cons, pow_succ]; ring

/-- The binary value of a list of `false`s is 0. -/
theorem binVal_replicate_false (n : ℕ) : binVal (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, binVal, ih]

/-- The binary value of a bitstring `l` is less than `2 ^ l.length`. -/
theorem binVal_lt (l : BitString) : binVal l < 2 ^ l.length := by
  induction l with
  | nil => simp [binVal]
  | cons b l ih =>
    simp only [binVal, List.length_cons, pow_succ]
    have := b.toNat_lt
    omega

/-- The width-`w` representation of `2 ^ j`: a single `true` at position `j`. -/
def powBits (w j : ℕ) : BitString :=
  List.replicate j false ++ true :: List.replicate (w - j - 1) false

/-- The binary value of `powBits w j` is `2 ^ j`. -/
theorem binVal_powBits (w j : ℕ) : binVal (powBits w j) = 2 ^ j := by
  simp [powBits, binVal_append, binVal, binVal_replicate_false]

/-- The length of `powBits w j` is `w` if `j < w`. -/
theorem length_powBits (w j : ℕ) (h : j < w) : (powBits w j).length = w := by
  simp [powBits]; omega

/-- The fixed-point value of `powBits w (N - b)` is `2⁻¹ ^ b`. -/
theorem fixVal_powBits (N w b : ℕ) (hb : b ≤ N) :
    fixVal N (powBits w (N - b)) = (2 : ℝ)⁻¹ ^ b := by
  rw [fixVal, binVal_powBits]
  have h2 : (2 : ℝ) ^ N = 2 ^ (N - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hb]
  rw [h2, inv_pow]
  push_cast
  field_simp

/-- The carry of a full adder. -/
def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Ripple-carry addition with input carry `c` (as long as both operands last). -/
def addBits : Bool → BitString → BitString → BitString
  | c, a :: l, b :: m => xor (xor a b) c :: addBits (carryBit a b c) l m
  | _, _, _ => []

/-- The carry out of `addBits`. -/
def addCarry : Bool → BitString → BitString → Bool
  | c, a :: l, b :: m => addCarry (carryBit a b c) l m
  | c, _, _ => c

/-- A full adder computes the sum of three bits. -/
theorem full_adder_toNat (a b c : Bool) :
    a.toNat + b.toNat + c.toNat = (xor (xor a b) c).toNat + 2 * (carryBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The length of `addBits c l m` is the length of `l` if `l` and `m` have the same length. -/
theorem length_addBits : ∀ (c : Bool) (l m : BitString), l.length = m.length →
    (addBits c l m).length = l.length
  | _, [], [], _ => rfl
  | c, a :: l, b :: m, h => by
    simp only [addBits, List.length_cons, length_addBits (carryBit a b c) l m (by simpa using h)]
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-- Correctness of the ripple-carry adder. -/
theorem binVal_addBits : ∀ (c : Bool) (l m : BitString), l.length = m.length →
    binVal (addBits c l m) + 2 ^ l.length * (addCarry c l m).toNat =
      binVal l + binVal m + c.toNat
  | c, [], [], _ => by simp [addBits, addCarry, binVal]
  | c, a :: l, b :: m, h => by
    have ih := binVal_addBits (carryBit a b c) l m (by simpa using h)
    have fa := full_adder_toNat a b c
    simp only [addBits, addCarry, binVal, List.length_cons, pow_succ]
    linarith
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-- Without overflow, `addBits false` adds. -/
theorem binVal_addBits_of_lt (l m : BitString) (h : l.length = m.length)
    (hlt : binVal l + binVal m < 2 ^ l.length) :
    binVal (addBits false l m) = binVal l + binVal m := by
  have e := binVal_addBits false l m h
  cases hc : addCarry false l m
  · simpa [hc] using e
  · rw [hc] at e; simp at e; omega

/-- Without overflow, fixed-point addition adds the represented reals. -/
theorem fixVal_addBits (N : ℕ) (l m : BitString) (h : l.length = m.length)
    (hlt : binVal l + binVal m < 2 ^ l.length) :
    fixVal N (addBits false l m) = fixVal N l + fixVal N m := by
  rw [fixVal, fixVal, fixVal, binVal_addBits_of_lt l m h hlt]
  push_cast
  ring

/-- Comparison scanning from the least significant bit: the flag holds the comparison of the bits
read so far (`true` iff "first operand ≤ second" when started with `true`). -/
def cmpBits : Bool → BitString → BitString → Bool
  | f, a :: l, b :: m => cmpBits (if a == b then f else b) l m
  | f, _, _ => f

/-- The result of `cmpBits f l m` is true if and only if the binary value of `l` is less than the
binary value of `m`, or they are equal and `f` is true. -/
theorem cmpBits_iff : ∀ (f : Bool) (l m : BitString), l.length = m.length →
    (cmpBits f l m = true ↔ binVal l < binVal m ∨ (binVal l = binVal m ∧ f = true))
  | f, [], [], _ => by simp [cmpBits, binVal]
  | f, a :: l, b :: m, h => by
    have ih := cmpBits_iff (if a == b then f else b) l m (by simpa using h)
    simp only [cmpBits, binVal]
    rw [ih]
    cases a <;> cases b <;> cases f <;> simp <;> omega
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-- `cmpBits true` decides `≤`. -/
theorem cmpBits_true_iff (l m : BitString) (h : l.length = m.length) :
    cmpBits true l m = true ↔ binVal l ≤ binVal m := by
  rw [cmpBits_iff true l m h, Nat.le_iff_lt_or_eq]; simp

/-- `cmpBits true` decides `≤` of the represented reals. -/
theorem cmpBits_true_iff_fixVal (N : ℕ) (l m : BitString) (h : l.length = m.length) :
    cmpBits true l m = true ↔ fixVal N l ≤ fixVal N m := by
  rw [cmpBits_true_iff l m h, fixVal, fixVal, div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

namespace Stmt

variable {k : ℕ}

/-- If a statement executes to `σ₁` and `σ₁ = σ₂`, then it executes to `σ₂`. -/
theorem exec_of_eq {s : Stmt k} {σ σ₁ σ₂ : Stacks k} {S : ℕ} (h : Exec s σ σ₁ S) (e : σ₁ = σ₂) :
    Exec s σ σ₂ S := e ▸ h

/-- One step of the ripple-carry adder: pop the low bits `a`, `b` of `A`, `B` and the carry `c`
of `Cy`; push the new carry on `Cy` and the sum bit on `R`. -/
def addStep (A B Cy R : Fin k) : Stmt k :=
  caseBit A fun a => caseBit B fun b => caseBit Cy fun c =>
    seqs [.pop A, .pop B, .pop Cy, .push Cy (carryBit a b c), .push R (xor (xor a b) c)]

/-- `A := A + B` (operands of equal width, carry out discarded) and `B := []`, using the empty
work stacks `Cy` (carry) and `R` (result, built reversed). -/
def addInto (A B Cy R : Fin k) : Stmt k :=
  seqs [.push Cy false, .loop A Option.isSome (addStep A B Cy R), clear Cy, moveAll R A]

/-- Executing `addStep A B Cy R` pops bits from `A` and `B`, adds them with the carry `Cy`,
and pushes the result to `R`. -/
theorem exec_addStep {A B Cy R : Fin k} (hAB : A ≠ B) (hAC : A ≠ Cy) (hAR : A ≠ R)
    (hBC : B ≠ Cy) (hBR : B ≠ R) (hCR : Cy ≠ R) {σ : Stacks k} {a b c : Bool} {l m : BitString}
    (hA : σ A = a :: l) (hB : σ B = b :: m) (hC : σ Cy = [c]) :
    Exec (addStep A B Cy R) σ
      (Function.update (Function.update (Function.update (Function.update σ A l) B m) Cy
        [carryBit a b c]) R (xor (xor a b) c :: σ R)) σ.space := by
  rw [addStep, exec_caseBit hA, exec_caseBit hB, exec_caseBit hC]
  have hB1 : (Function.update σ A l) B = b :: m := by rw [Function.update_of_ne hAB.symm]; exact hB
  have hC1 : (Function.update σ A l) Cy = [c] := by
    rw [Function.update_of_ne hAC.symm]; exact hC
  have hC2 : (Function.update (Function.update σ A l) B m) Cy = [c] := by
    rw [Function.update_of_ne hBC.symm]; exact hC1
  have s1 := space_update_of_cons hA
  have s2 := space_update_of_cons hB1
  have s3 := space_update_of_cons hC2
  have e1 := exec_pop_cons hA (S := σ.space) le_rfl
  have e2 := exec_pop_cons hB1 (S := σ.space) (by omega)
  have e3 := exec_pop_cons hC2 (S := σ.space) (by omega)
  have e4 := Exec.push (r := Cy) (b := carryBit a b c)
    (σ := Function.update (Function.update (Function.update σ A l) B m) Cy []) (S := σ.space)
    (by omega)
  rw [Function.update_self, Function.update_idem] at e4
  have s4 := Stacks.space_update_cons
    (Function.update (Function.update (Function.update σ A l) B m) Cy []) Cy (carryBit a b c)
  rw [Function.update_self, Function.update_idem] at s4
  have e5 := Exec.push (r := R) (b := xor (xor a b) c)
    (σ := Function.update (Function.update (Function.update σ A l) B m) Cy [carryBit a b c])
    (S := σ.space) (by omega)
  have hR : (Function.update (Function.update (Function.update σ A l) B m) Cy [carryBit a b c]) R =
      σ R := by
    rw [Function.update_of_ne hCR.symm, Function.update_of_ne hBR.symm,
      Function.update_of_ne hAR.symm]
  rw [hR] at e5
  exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.skip e5.space_le.2)))))

/-- Executing the loop of `addInto A B R` computes the sum of `A` and `B` into `R` bit by bit. -/
theorem exec_addLoop {A B Cy R : Fin k} (hAB : A ≠ B) (hAC : A ≠ Cy) (hAR : A ≠ R)
    (hBC : B ≠ Cy) (hBR : B ≠ R) (hCR : Cy ≠ R) :
    ∀ (l m : BitString) (c : Bool) (σ : Stacks k), l.length = m.length → σ A = l → σ B = m →
      σ Cy = [c] →
      Exec (.loop A Option.isSome (addStep A B Cy R)) σ
        (Function.update (Function.update (Function.update (Function.update σ A []) B []) Cy
          [addCarry c l m]) R ((addBits c l m).reverse ++ σ R)) σ.space
  | [], [], c, σ, _, hA, hB, hC => by
    refine exec_of_eq (.loopF (by simp [hA]) le_rfl) ?_
    funext j
    simp only [Function.update_apply, addCarry, addBits, List.reverse_nil, List.nil_append]
    split_ifs <;> subst_vars <;> simp_all
  | a :: l, b :: m, c, σ, h, hA, hB, hC => by
    have h1 := exec_addStep hAB hAC hAR hBC hBR hCR hA hB hC
    have h2 := exec_addLoop hAB hAC hAR hBC hBR hCR l m (carryBit a b c)
      (Function.update (Function.update (Function.update (Function.update σ A l) B m) Cy
        [carryBit a b c]) R (xor (xor a b) c :: σ R)) (by simpa using h)
      (by simp [hAB, hAC, hAR]) (by simp [hBC, hBR]) (by simp [hCR])
    refine .loopT (by simp [hA]) h1 (exec_of_eq (h2.mono h1.space_le.2) ?_)
    funext j
    simp only [Function.update_apply, addCarry, addBits, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    split_ifs <;> subst_vars <;> simp_all
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h

/-- **Addition.**  With `A, B, Cy, R` distinct, `|A| = |B|` and `Cy`, `R` empty, `addInto` sets
`A := addBits false A B` (= `A + B` without overflow, `binVal_addBits_of_lt`) and empties `B`,
within the initial space `+ 1`. -/
theorem exec_addInto {A B Cy R : Fin k} (hAB : A ≠ B) (hAC : A ≠ Cy) (hAR : A ≠ R)
    (hBC : B ≠ Cy) (hBR : B ≠ R) (hCR : Cy ≠ R) {σ : Stacks k} {l m : BitString}
    (h : l.length = m.length) (hA : σ A = l) (hB : σ B = m) (hC : σ Cy = []) (hR : σ R = []) :
    Exec (addInto A B Cy R) σ (Function.update (Function.update σ A (addBits false l m)) B [])
      (σ.space + 1) := by
  have e0 := Exec.push (r := Cy) (b := false) (σ := σ) (S := σ.space + 1) le_rfl
  rw [hC] at e0
  have s0 := Stacks.space_update_cons σ Cy false
  rw [hC] at s0
  have e1 := exec_addLoop hAB hAC hAR hBC hBR hCR l m false (Function.update σ Cy [false]) h
    (by rw [Function.update_of_ne hAC]; exact hA) (by rw [Function.update_of_ne hBC]; exact hB)
    (Function.update_self _ _ _)
  rw [s0] at e1
  have e2 := exec_clear Cy _ (Function.update (Function.update (Function.update
    (Function.update (Function.update σ Cy [false]) A []) B []) Cy [addCarry false l m]) R
      ((addBits false l m).reverse ++ (Function.update σ Cy [false]) R)) rfl
  have e3 := exec_moveAll hAR.symm _ (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update σ Cy [false]) A []) B [])
      Cy [addCarry false l m]) R ((addBits false l m).reverse ++
        (Function.update σ Cy [false]) R)) Cy []) rfl
  have sp1 := e1.space_le.2
  have sp2 := e2.space_le.2
  refine .seq e0 (.seq e1 (.seq (e2.mono sp1) (.seq (e3.mono (sp2.trans sp1))
    (.skip ((e3.space_le.2.trans sp2).trans sp1)))) |> fun h => exec_of_eq h ?_)
  funext j
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- One step of the comparison: pop the low bits `a`, `b` of `A`, `B` and the flag `f` of `F`;
push the new flag (`f` if `a = b`, else `b`). -/
def cmpStep (A B F : Fin k) : Stmt k :=
  caseBit A fun a => caseBit B fun b => caseBit F fun f =>
    seqs [.pop A, .pop B, .pop F, .push F (if a == b then f else b)]

/-- `F := [cmpBits true A B]` (that is, `[decide (binVal A ≤ binVal B)]` for equal widths,
`cmpBits_true_iff`), emptying `A` and `B`; `F` must be empty. -/
def cmpInto (A B F : Fin k) : Stmt k :=
  seqs [.push F true, .loop A Option.isSome (cmpStep A B F)]

/-- Executing `cmpStep A B F` pops bits from `A` and `B`, compares them using `F` as the current
comparison flag, and updates `F`. -/
theorem exec_cmpStep {A B F : Fin k} (hAB : A ≠ B) (hAF : A ≠ F) (hBF : B ≠ F)
    {σ : Stacks k} {a b f : Bool} {l m : BitString}
    (hA : σ A = a :: l) (hB : σ B = b :: m) (hF : σ F = [f]) :
    Exec (cmpStep A B F) σ
      (Function.update (Function.update (Function.update σ A l) B m) F
        [if a == b then f else b]) σ.space := by
  rw [cmpStep, exec_caseBit hA, exec_caseBit hB, exec_caseBit hF]
  have hB1 : (Function.update σ A l) B = b :: m := by rw [Function.update_of_ne hAB.symm]; exact hB
  have hF1 : (Function.update σ A l) F = [f] := by
    rw [Function.update_of_ne hAF.symm]; exact hF
  have hF2 : (Function.update (Function.update σ A l) B m) F = [f] := by
    rw [Function.update_of_ne hBF.symm]; exact hF1
  have s1 := space_update_of_cons hA
  have s2 := space_update_of_cons hB1
  have s3 := space_update_of_cons hF2
  have e1 := exec_pop_cons hA (S := σ.space) le_rfl
  have e2 := exec_pop_cons hB1 (S := σ.space) (by omega)
  have e3 := exec_pop_cons hF2 (S := σ.space) (by omega)
  have e4 := Exec.push (r := F) (b := if a == b then f else b)
    (σ := Function.update (Function.update (Function.update σ A l) B m) F []) (S := σ.space)
    (by omega)
  rw [Function.update_self, Function.update_idem] at e4
  exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.skip e4.space_le.2))))

/-- Executing the loop of `cmpInto A B F` compares `A` and `B` into `F` bit by bit. -/
theorem exec_cmpLoop {A B F : Fin k} (hAB : A ≠ B) (hAF : A ≠ F) (hBF : B ≠ F) :
    ∀ (l m : BitString) (f : Bool) (σ : Stacks k), l.length = m.length → σ A = l → σ B = m →
      σ F = [f] →
      Exec (.loop A Option.isSome (cmpStep A B F)) σ
        (Function.update (Function.update (Function.update σ A []) B []) F [cmpBits f l m])
        σ.space
  | [], [], f, σ, _, hA, hB, hF => by
    refine exec_of_eq (.loopF (by simp [hA]) le_rfl) ?_
    funext j
    simp only [Function.update_apply, cmpBits]
    split_ifs <;> subst_vars <;> simp_all
  | a :: l, b :: m, f, σ, h, hA, hB, hF => by
    have h1 := exec_cmpStep hAB hAF hBF hA hB hF
    have h2 := exec_cmpLoop hAB hAF hBF l m (if a == b then f else b)
      (Function.update (Function.update (Function.update σ A l) B m) F
        [if a == b then f else b]) (by simpa using h)
      (by simp [hAB, hAF]) (by simp [hBF]) (by simp)
    refine .loopT (by simp [hA]) h1 (exec_of_eq (h2.mono h1.space_le.2) ?_)
    funext j
    simp only [Function.update_apply, cmpBits]
    split_ifs <;> subst_vars <;> simp_all
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h

/-- **Comparison.**  With `A, B, F` distinct, `|A| = |B|` and `F` empty, `cmpInto` leaves
`[cmpBits true A B]` on `F` and empties `A`, `B`, within the initial space `+ 1`. -/
theorem exec_cmpInto {A B F : Fin k} (hAB : A ≠ B) (hAF : A ≠ F) (hBF : B ≠ F)
    {σ : Stacks k} {l m : BitString} (h : l.length = m.length) (hA : σ A = l) (hB : σ B = m)
    (hF : σ F = []) :
    Exec (cmpInto A B F) σ
      (Function.update (Function.update (Function.update σ A []) B []) F [cmpBits true l m])
      (σ.space + 1) := by
  have e0 := Exec.push (r := F) (b := true) (σ := σ) (S := σ.space + 1) le_rfl
  rw [hF] at e0
  have s0 := Stacks.space_update_cons σ F true
  rw [hF] at s0
  have e1 := exec_cmpLoop hAB hAF hBF l m true (Function.update σ F [true]) h
    (by rw [Function.update_of_ne hAF]; exact hA) (by rw [Function.update_of_ne hBF]; exact hB)
    (Function.update_self _ _ _)
  rw [s0] at e1
  refine exec_of_eq (.seq e0 (.seq e1 (.skip e1.space_le.2))) ?_
  funext j
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- One step of `copy`: move the top bit of `t` onto both `r` and `r'`. -/
def dupStep (t r r' : Fin k) : Stmt k :=
  caseBit t fun b => seqs [.pop t, .push r b, .push r' b]

/-- `copy r r' t`: put a copy of `r` on top of `r'` (`r` is restored), through the empty work
stack `t`. -/
def copy (r r' t : Fin k) : Stmt k :=
  .seq (moveAll r t) (.loop t Option.isSome (dupStep t r r'))

/-- Executing `dupStep t r r'` pops a bit from `t` and pushes it to both `r` and `r'`. -/
theorem exec_dupStep {t r r' : Fin k} (htr : t ≠ r) (htr' : t ≠ r') (hrr : r ≠ r')
    {σ : Stacks k} {b : Bool} {l : BitString} (ht : σ t = b :: l) :
    Exec (dupStep t r r') σ
      (Function.update (Function.update (Function.update σ t l) r (b :: σ r)) r' (b :: σ r'))
      (σ.space + 1) := by
  rw [dupStep, exec_caseBit ht]
  have s1 := space_update_of_cons ht
  have e1 := exec_pop_cons ht (S := σ.space + 1) (by omega)
  have e2 := Exec.push (r := r) (b := b) (σ := Function.update σ t l) (S := σ.space + 1)
    (by omega)
  rw [Function.update_of_ne htr.symm] at e2
  have s2 := Stacks.space_update_cons (Function.update σ t l) r b
  rw [Function.update_of_ne htr.symm] at s2
  have e3 := Exec.push (r := r') (b := b)
    (σ := Function.update (Function.update σ t l) r (b :: σ r)) (S := σ.space + 1) (by omega)
  rw [Function.update_of_ne hrr.symm, Function.update_of_ne htr'.symm] at e3
  exact .seq e1 (.seq e2 (.seq e3 (.skip e3.space_le.2)))

/-- Executing the loop of `dup t r r'` duplicates `t` into `r` and `r'`. -/
theorem exec_dupLoop {t r r' : Fin k} (htr : t ≠ r) (htr' : t ≠ r') (hrr : r ≠ r') :
    ∀ (l : BitString) (σ : Stacks k), σ t = l →
      Exec (.loop t Option.isSome (dupStep t r r')) σ
        (Function.update (Function.update (Function.update σ t []) r (l.reverse ++ σ r)) r'
          (l.reverse ++ σ r')) (σ.space + l.length)
  | [], σ, ht => by
    refine exec_of_eq (.loopF (by simp [ht]) (by simp)) ?_
    funext j
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs <;> subst_vars <;> simp_all
  | b :: l, σ, ht => by
    have h1 := exec_dupStep htr htr' hrr ht
    have h2 := exec_dupLoop htr htr' hrr l
      (Function.update (Function.update (Function.update σ t l) r (b :: σ r)) r' (b :: σ r'))
      (by simp [htr, htr'])
    have sp : Stacks.space (Function.update (Function.update (Function.update σ t l) r
        (b :: σ r)) r' (b :: σ r')) = σ.space + 1 := by
      have s1 := space_update_of_cons ht
      have s2 := Stacks.space_update_cons (Function.update σ t l) r b
      rw [Function.update_of_ne htr.symm] at s2
      have s3 := Stacks.space_update_cons (Function.update (Function.update σ t l) r (b :: σ r))
        r' b
      rw [Function.update_of_ne hrr.symm, Function.update_of_ne htr'.symm] at s3
      omega
    rw [sp] at h2
    refine .loopT (by simp [ht]) (h1.mono (by simp only [List.length_cons]; omega))
      (exec_of_eq (h2.mono (by simp only [List.length_cons]; omega)) ?_)
    funext j
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    split_ifs <;> subst_vars <;> simp_all

/-- **Copy.**  With `r, r', t` distinct and `t` empty, `copy r r' t` puts a copy of `r` on top
of `r'`, within the initial space plus `|r|`. -/
theorem exec_copy {r r' t : Fin k} (hrr : r ≠ r') (hrt : r ≠ t) (hr't : r' ≠ t)
    {σ : Stacks k} (ht : σ t = []) :
    Exec (copy r r' t) σ (Function.update σ r' (σ r ++ σ r')) (σ.space + (σ r).length) := by
  have e1 := exec_moveAll hrt (σ r) σ rfl
  rw [ht, List.append_nil] at e1
  have h2 := exec_dupLoop hrt.symm hr't.symm hrr (σ r).reverse
    (Function.update (Function.update σ r []) t (σ r).reverse) (Function.update_self _ _ _)
  have sp := e1.space_le.2
  rw [List.length_reverse] at h2
  refine .seq (e1.mono (by omega)) (exec_of_eq (h2.mono (by omega)) ?_)
  funext j
  simp only [Function.update_apply, List.reverse_reverse]
  split_ifs <;> subst_vars <;> simp_all

end Stmt

/-! #### Further generic tools: frames, a loop rule with a variant, constants -/

/-- The stack `j` is written (pushed or popped) somewhere in `s`. -/
def Stmt.Writes {k : ℕ} (j : Fin k) : Stmt k → Prop
  | .skip => False
  | .push r _ => r = j
  | .pop r => r = j
  | .seq s₁ s₂ => s₁.Writes j ∨ s₂.Writes j
  | .ite _ _ s₁ s₂ => s₁.Writes j ∨ s₂.Writes j
  | .loop _ _ b => b.Writes j

/-- **Frame.**  A stack that `s` never writes is unchanged by an execution of `s`. -/
theorem Exec.frame {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ} (h : Exec s σ σ' S)
    {j : Fin k} (hj : ¬ s.Writes j) : σ' j = σ j := by
  induction h with
  | skip _ => rfl
  | @push r b σ S _ => exact Function.update_of_ne (fun h => hj h.symm) _ _
  | @pop r σ S _ => exact Function.update_of_ne (fun h => hj h.symm) _ _
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.Writes, not_or] at hj
    rw [ih₂ hj.2, ih₁ hj.1]
  | iteT _ _ ih =>
    simp only [Stmt.Writes, not_or] at hj
    exact ih hj.1
  | iteF _ _ ih =>
    simp only [Stmt.Writes, not_or] at hj
    exact ih hj.2
  | loopT _ _ _ ih₁ ih₂ => rw [ih₂ hj, ih₁ hj]
  | loopF _ _ => rfl

/-- **Loop rule with an invariant and a variant**: if every iteration started in an invariant
state where the condition holds terminates (within `S`) in an invariant state with a smaller
variant, and invariant states respect the space bound, then from every invariant state the loop
terminates in an invariant state where the condition fails. -/
theorem Exec.loop_of_variant {k : ℕ} {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k}
    (I : Stacks k → Prop) (μ : Stacks k → ℕ) (S : ℕ)
    (hstep : ∀ σ, I σ → cond (σ r).head? = true →
      ∃ σ', Exec body σ σ' S ∧ I σ' ∧ μ σ' < μ σ)
    (hexit : ∀ σ, I σ → σ.space ≤ S) :
    ∀ σ, I σ → ∃ σ', Exec (.loop r cond body) σ σ' S ∧ I σ' ∧ cond (σ' r).head? = false := by
  suffices H : ∀ n σ, μ σ ≤ n → I σ →
      ∃ σ', Exec (.loop r cond body) σ σ' S ∧ I σ' ∧ cond (σ' r).head? = false from
    fun σ hσ => H _ σ le_rfl hσ
  intro n
  induction n with
  | zero =>
    intro σ hμ hσ
    cases hc : cond (σ r).head?
    · exact ⟨σ, .loopF hc (hexit σ hσ), hσ, hc⟩
    · obtain ⟨σ₁, -, -, hlt⟩ := hstep σ hσ hc
      omega
  | succ n ih =>
    intro σ hμ hσ
    cases hc : cond (σ r).head?
    · exact ⟨σ, .loopF hc (hexit σ hσ), hσ, hc⟩
    · obtain ⟨σ₁, hb, hI, hlt⟩ := hstep σ hσ hc
      obtain ⟨σ₂, hl, hI₂, hc₂⟩ := ih σ₁ (by omega) hI
      exact ⟨σ₂, .loopT hc hb hl, hI₂, hc₂⟩

/-- Push the bits of a hardwired string `l` on `r` (so that `l` is on top, first bit first). -/
def Stmt.pushList {k : ℕ} (r : Fin k) : BitString → Stmt k
  | [] => .skip
  | b :: l => .seq (pushList r l) (.push r b)

/-- Executing `pushList r l` pushes the elements of `l` onto `r`. -/
theorem Stmt.exec_pushList {k : ℕ} (r : Fin k) : ∀ (l : BitString) (σ : Stacks k),
    Exec (pushList r l) σ (Function.update σ r (l ++ σ r)) (σ.space + l.length)
  | [], σ => Stmt.exec_of_eq (Exec.skip (by simp))
      (by rw [List.nil_append, Function.update_eq_self])
  | b :: l, σ => by
    have h1 := exec_pushList r l σ
    have s1 : Stacks.space (Function.update σ r (l ++ σ r)) = σ.space + l.length := by
      have := σ.space_update r (l ++ σ r)
      simp only [List.length_append] at this
      omega
    have h2 := Exec.push (r := r) (b := b) (σ := Function.update σ r (l ++ σ r))
      (S := σ.space + (b :: l).length) (by simp only [List.length_cons]; omega)
    rw [Function.update_self, Function.update_idem] at h2
    exact .seq (h1.mono (by simp)) h2

/-! #### Equality test of two stacks -/

namespace Stmt

variable {k : ℕ}

/-- Set the one-bit flag on `F` to `false`. -/
def clearFlag (F : Fin k) : Stmt k := .seq (.pop F) (.push F false)

/-- Executing `clearFlag F` sets the top bit of `F` to `false`. -/
theorem exec_clearFlag {F : Fin k} {σ : Stacks k} {f : Bool} (hF : σ F = [f]) :
    Exec (clearFlag F) σ (Function.update σ F [false]) σ.space := by
  have s1 := space_update_of_cons hF
  have e1 := exec_pop_cons hF (S := σ.space) le_rfl
  have e2 := Exec.push (r := F) (b := false) (σ := Function.update σ F []) (S := σ.space)
    (by omega)
  rw [Function.update_self, Function.update_idem] at e2
  exact .seq e1 e2

/-- One step of the equality test: move the top bit `a` of `A` to `tA` and the top bit `b` of
`B` (if any) to `tB`; clear the flag `F` if `B` is empty or `a ≠ b`. -/
def eqStep (A B tA tB F : Fin k) : Stmt k :=
  caseBit A fun a =>
    .seq (.ite B Option.isSome
        (caseBit B fun b => .seq (if a == b then .skip else clearFlag F) (moveBit B tB))
        (clearFlag F))
      (moveBit A tA)

/-- `F := [decide (A = B)]`, restoring `A` and `B`, through the empty stacks `tA`, `tB`, `F`. -/
def eqTest (A B tA tB F : Fin k) : Stmt k :=
  seqs [.push F true, .loop A Option.isSome (eqStep A B tA tB F),
    .ite B Option.isSome (clearFlag F) .skip, moveAll B tB, moveAll tA A, moveAll tB B]

/-- Executing the loop of `eqInto A B F` checks if `A` and `B` are equal into `F`. -/
theorem exec_eqLoop {A B tA tB F : Fin k} (h1 : A ≠ B) (h2 : A ≠ tA) (h3 : A ≠ tB) (h4 : A ≠ F)
    (h5 : B ≠ tA) (h6 : B ≠ tB) (h7 : B ≠ F) (h8 : tA ≠ tB) (h9 : tA ≠ F) (h10 : tB ≠ F) :
    ∀ (l m : BitString) (f : Bool) (σ : Stacks k), σ A = l → σ B = m → σ F = [f] →
      Exec (.loop A Option.isSome (eqStep A B tA tB F)) σ
        (Function.update (Function.update (Function.update (Function.update (Function.update σ
          A []) B (m.drop l.length)) tA (l.reverse ++ σ tA))
          tB ((m.take l.length).reverse ++ σ tB)) F [f && decide (m.take l.length = l)])
        σ.space
  | [], m, f, σ, hA, hB, hF => by
    refine exec_of_eq (.loopF (by simp [hA]) le_rfl) ?_
    funext j
    simp only [Function.update_apply, List.length_nil, List.drop_zero, List.take_zero,
      List.reverse_nil, List.nil_append, decide_true, Bool.and_true]
    split_ifs <;> subst_vars <;> simp_all
  | a :: l, [], f, σ, hA, hB, hF => by
    have e1 := exec_clearFlag hF
    have hA1 : (Function.update σ F [false]) A = a :: l := by
      rw [Function.update_of_ne h4]; exact hA
    have e2 := exec_moveBit h2 hA1
    have hstep : Exec (eqStep A B tA tB F) σ
        (Function.update (Function.update (Function.update σ F [false]) A l) tA
          (a :: (Function.update σ F [false]) tA)) σ.space := by
      rw [eqStep, exec_caseBit hA]
      have e1' : Exec (.ite B Option.isSome
          (caseBit B fun b => .seq (if a == b then .skip else clearFlag F) (moveBit B tB))
          (clearFlag F)) σ (Function.update σ F [false]) σ.space :=
        .iteF (by simp [hB]) e1
      have hsp : Stacks.space (Function.update σ F [false]) = σ.space := by
        have := σ.space_update F [false]; rw [hF] at this; simp at this; omega
      exact .seq e1' (by rw [← hsp]; exact e2)
    have ih := exec_eqLoop h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 l [] false
      (Function.update (Function.update (Function.update σ F [false]) A l) tA
          (a :: (Function.update σ F [false]) tA))
      (by rw [Function.update_of_ne h2, Function.update_self])
      (by rw [Function.update_of_ne h5, Function.update_of_ne h1.symm,
        Function.update_of_ne h7]; exact hB)
      (by rw [Function.update_of_ne h9.symm, Function.update_of_ne h4.symm,
        Function.update_self])
    refine .loopT (by simp [hA]) hstep (exec_of_eq (ih.mono hstep.space_le.2) ?_)
    funext j
    simp only [Function.update_apply, List.drop_nil, List.take_nil, List.reverse_nil,
      List.nil_append, List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    split_ifs <;> subst_vars <;> simp_all
  | a :: l, b :: m, f, σ, hA, hB, hF => by
    have hsp : ∀ g : Bool, Stacks.space (Function.update σ F [g]) = σ.space := fun g => by
      have := σ.space_update F [g]; rw [hF] at this; simp at this; omega
    -- the flag after comparing `a` and `b`
    have e1 : Exec (if a == b then .skip else clearFlag F) σ
        (Function.update σ F [f && (a == b)]) σ.space := by
      by_cases hab : a = b
      · subst hab
        simp only [beq_self_eq_true, ite_true, Bool.and_true]
        rw [← hF, Function.update_eq_self]
        exact .skip le_rfl
      · have : (a == b) = false := by simpa using hab
        rw [this, Bool.and_false]
        simpa [this] using exec_clearFlag hF
    have hB1 : (Function.update σ F [f && (a == b)]) B = b :: m := by
      rw [Function.update_of_ne h7]; exact hB
    have e2 := exec_moveBit h6 hB1
    have hA2 : (Function.update (Function.update (Function.update σ F [f && (a == b)]) B m) tB
        (b :: (Function.update σ F [f && (a == b)]) tB)) A = a :: l := by
      rw [Function.update_of_ne h3, Function.update_of_ne h1, Function.update_of_ne h4]; exact hA
    have e3 := exec_moveBit h2 hA2
    have hstep : Exec (eqStep A B tA tB F) σ
        (Function.update (Function.update (Function.update (Function.update
          (Function.update σ F [f && (a == b)]) B m) tB
            (b :: (Function.update σ F [f && (a == b)]) tB)) A l) tA
          (a :: (Function.update (Function.update (Function.update σ F [f && (a == b)]) B m) tB
            (b :: (Function.update σ F [f && (a == b)]) tB)) tA)) σ.space := by
      have hite : Exec (.ite B Option.isSome
            (caseBit B fun b' => .seq (if a == b' then .skip else clearFlag F) (moveBit B tB))
            (clearFlag F)) σ
          (Function.update (Function.update (Function.update σ F [f && (a == b)]) B m) tB
            (b :: (Function.update σ F [f && (a == b)]) tB)) σ.space := by
        refine .iteT (by simp [hB]) ?_
        rw [exec_caseBit hB]
        exact .seq e1 (e2.mono (hsp _).le)
      rw [eqStep, exec_caseBit hA]
      exact .seq hite (e3.mono (e2.space_le.2.trans (hsp _).le))
    have ih := exec_eqLoop h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 l m (f && (a == b))
      (Function.update (Function.update (Function.update (Function.update
          (Function.update σ F [f && (a == b)]) B m) tB
            (b :: (Function.update σ F [f && (a == b)]) tB)) A l) tA
          (a :: (Function.update (Function.update (Function.update σ F [f && (a == b)]) B m) tB
            (b :: (Function.update σ F [f && (a == b)]) tB)) tA))
      (by rw [Function.update_of_ne h2, Function.update_self])
      (by rw [Function.update_of_ne h5, Function.update_of_ne h1.symm, Function.update_of_ne h6,
        Function.update_self])
      (by rw [Function.update_of_ne h9.symm, Function.update_of_ne h4.symm,
        Function.update_of_ne h10.symm, Function.update_of_ne h7.symm, Function.update_self])
    refine .loopT (by simp [hA]) hstep (exec_of_eq (ih.mono hstep.space_le.2) ?_)
    funext j
    simp only [Function.update_apply, List.length_cons, List.drop_succ_cons, List.take_succ_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append, List.cons.injEq]
    split_ifs <;> subst_vars <;> simp_all [Bool.and_assoc]
    cases a <;> cases b <;> simp_all

/-- **Equality test.**  With `A, B, tA, tB, F` distinct and `tA`, `tB`, `F` empty, `eqTest`
leaves `[decide (σ A = σ B)]` on `F` and restores every other stack, within the initial
space `+ 1`. -/
theorem exec_eqTest {A B tA tB F : Fin k} (h1 : A ≠ B) (h2 : A ≠ tA) (h3 : A ≠ tB) (h4 : A ≠ F)
    (h5 : B ≠ tA) (h6 : B ≠ tB) (h7 : B ≠ F) (h8 : tA ≠ tB) (h9 : tA ≠ F) (h10 : tB ≠ F)
    {σ : Stacks k} (htA : σ tA = []) (htB : σ tB = []) (hF : σ F = []) :
    Exec (eqTest A B tA tB F) σ (Function.update σ F [decide (σ A = σ B)]) (σ.space + 1) := by
  have e0 := Exec.push (r := F) (b := true) (σ := σ) (S := σ.space + 1) le_rfl
  rw [hF] at e0
  have s0 := Stacks.space_update_cons σ F true
  rw [hF] at s0
  have e1 := exec_eqLoop h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (σ A) (σ B) true
    (Function.update σ F [true]) (by rw [Function.update_of_ne h4])
    (by rw [Function.update_of_ne h7])
    (Function.update_self _ _ _)
  rw [s0] at e1
  have htA' : Function.update σ F [true] tA = σ tA := Function.update_of_ne h9 _ _
  have htB' : Function.update σ F [true] tB = σ tB := Function.update_of_ne h10 _ _
  rw [htA', htB', htA, htB, List.append_nil, List.append_nil, Bool.true_and] at e1
  obtain ⟨σ1, e1, hσ1⟩ : ∃ σ1, Exec (.loop A Option.isSome (eqStep A B tA tB F))
      (Function.update σ F [true]) σ1 (σ.space + 1) ∧ σ1 = Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update σ F [true]) A [])
          B ((σ B).drop (σ A).length)) tA (σ A).reverse) tB ((σ B).take (σ A).length).reverse)
        F [decide ((σ B).take (σ A).length = σ A)] := ⟨_, e1, rfl⟩
  have hσ1B : σ1 B = (σ B).drop (σ A).length := by
    rw [hσ1, Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5,
      Function.update_self]
  have hσ1F : σ1 F = [decide ((σ B).take (σ A).length = σ A)] := by
    rw [hσ1, Function.update_self]
  have sp1 := e1.space_le.2
  -- the final check: the flag is cleared if `B` is longer than `A`
  obtain ⟨σ2, e2, hσ2⟩ : ∃ σ2, Exec (.ite B Option.isSome (clearFlag F) .skip) σ1 σ2
      (Stacks.space σ1) ∧ σ2 = Function.update σ1 F [decide (σ A = σ B)] := by
    cases hd : (σ B).drop (σ A).length with
    | nil =>
      refine ⟨σ1, .iteF (by simp [hσ1B, hd]) (.skip le_rfl), ?_⟩
      have hm : (σ B).take (σ A).length = σ B := by
        rw [← List.take_append_drop (σ A).length (σ B), hd, List.append_nil, List.take_take,
          min_self]
      rw [hm] at hσ1F
      funext j
      by_cases hj : j = F
      · subst hj
        rw [Function.update_self, hσ1F]
        congr 1
        exact decide_eq_decide.2 ⟨Eq.symm, Eq.symm⟩
      · rw [Function.update_of_ne hj]
    | cons b r =>
      refine ⟨_, .iteT (by simp [hσ1B, hd]) (exec_clearFlag hσ1F), ?_⟩
      have hne : σ A ≠ σ B := by
        intro h; rw [← h, List.drop_length] at hd; cases hd
      simp [hne]
  have sp2 := e2.space_le.2
  have e3 := exec_moveAll h6 (σ2 B) σ2 rfl
  have sp3 := e3.space_le.2
  have e4 := exec_moveAll h2.symm _ (Function.update (Function.update σ2 B []) tB
    ((σ2 B).reverse ++ σ2 tB)) rfl
  have sp4 := e4.space_le.2
  have e5 := exec_moveAll h6.symm _ (Function.update (Function.update (Function.update
    (Function.update σ2 B []) tB ((σ2 B).reverse ++ σ2 tB)) tA []) A
      ((Function.update (Function.update σ2 B []) tB ((σ2 B).reverse ++ σ2 tB) tA).reverse ++
        (Function.update (Function.update σ2 B []) tB ((σ2 B).reverse ++ σ2 tB)) A)) rfl
  have sp5 := e5.space_le.2
  refine exec_of_eq (.seq e0 (.seq e1 (.seq (e2.mono sp1) (.seq (e3.mono (sp2.trans sp1))
    (.seq (e4.mono (sp3.trans (sp2.trans sp1))) (.seq (e5.mono (sp4.trans (sp3.trans
      (sp2.trans sp1)))) (.skip (sp5.trans (sp4.trans (sp3.trans (sp2.trans sp1))))))))))) ?_
  subst hσ2 hσ1
  funext j
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;>
    simp_all [List.reverse_append, List.take_append_drop]

end Stmt

/-! #### Binary increment (for enumerating subsets and answer vectors as counters) -/

/-- Binary increment, least significant bit first (wrapping around). -/
def incBits : BitString → BitString
  | [] => []
  | true :: l => false :: incBits l
  | false :: l => true :: l

/-- The carry out of `incBits` (all bits were `true`). -/
def incCarry : BitString → Bool
  | [] => true
  | true :: l => incCarry l
  | false :: _ => false

/-- The length of `incBits l` is the length of `l`. -/
theorem length_incBits : ∀ l : BitString, (incBits l).length = l.length
  | [] => rfl
  | true :: l => by simp [incBits, length_incBits l]
  | false :: l => rfl

/-- The binary value of `incBits l` plus the carry times `2 ^ l.length` is the binary value
of `l` plus 1. -/
theorem binVal_incBits : ∀ l : BitString,
    binVal (incBits l) + 2 ^ l.length * (incCarry l).toNat = binVal l + 1
  | [] => by simp [incBits, incCarry, binVal]
  | true :: l => by
    have ih := binVal_incBits l
    simp only [incBits, incCarry, binVal, List.length_cons, pow_succ, Bool.toNat_true,
      Bool.toNat_false]
    linarith
  | false :: l => by simp [incBits, incCarry, binVal]; omega

/-- Incrementing a bitstring that starts with `n` `true`s flips them to `false`s and increments
the rest. -/
theorem incBits_replicate_append (n : ℕ) (rest : BitString) :
    incBits (List.replicate n true ++ rest) = List.replicate n false ++ incBits rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, incBits, ih]

/-- The increment carry of a bitstring starting with `n` `true`s is the increment carry of
the rest. -/
theorem incCarry_replicate_append (n : ℕ) (rest : BitString) :
    incCarry (List.replicate n true ++ rest) = incCarry rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, incCarry, ih]

/-- Appending `a :: l` to `List.replicate n a` is the same as prepending `a` to
`List.replicate n a ++ l`. -/
theorem replicate_append_cons_same {α : Type} (a : α) (n : ℕ) (l : List α) :
    List.replicate n a ++ a :: l = a :: (List.replicate n a ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

namespace Stmt

variable {k : ℕ}

/-- `A := incBits A`, `C := [incCarry A]`, through the empty work stack `t` (`C` empty). -/
def incr (A t C : Fin k) : Stmt k :=
  seqs [.loop A isTrue (.seq (.pop A) (.push t false)),
    .ite A Option.isSome (seqs [.pop A, .push A true, .push C false]) (.push C true),
    moveAll t A]

/-- The trailing-ones loop: `true` bits of `A` are replaced, on `t`, by `false` bits. -/
theorem exec_incLoop {A t : Fin k} (hAt : A ≠ t) : ∀ (l : BitString) (σ : Stacks k), σ A = l →
    ∃ (n : ℕ) (rest : BitString), l = List.replicate n true ++ rest ∧ rest.head? ≠ some true ∧
      Exec (.loop A isTrue (.seq (.pop A) (.push t false))) σ
        (Function.update (Function.update σ A rest) t (List.replicate n false ++ σ t)) σ.space
  | [], σ, hσ => ⟨0, [], by simp, by simp, exec_of_eq (.loopF (by simp [hσ, isTrue]) le_rfl)
      (by funext j; simp only [Function.update_apply, List.replicate_zero, List.nil_append];
          split_ifs <;> subst_vars <;> simp_all)⟩
  | false :: l, σ, hσ => ⟨0, false :: l, by simp, by simp,
      exec_of_eq (.loopF (by simp [hσ, isTrue]) le_rfl)
        (by funext j; simp only [Function.update_apply, List.replicate_zero, List.nil_append];
            split_ifs <;> subst_vars <;> simp_all)⟩
  | true :: l, σ, hσ => by
    have s1 := space_update_of_cons hσ
    have e1 := exec_pop_cons hσ (S := σ.space) le_rfl
    have e2 := Exec.push (r := t) (b := false) (σ := Function.update σ A l) (S := σ.space)
      (by omega)
    rw [Function.update_of_ne hAt.symm] at e2
    have hA2 : (Function.update (Function.update σ A l) t (false :: σ t)) A = l := by
      rw [Function.update_of_ne hAt, Function.update_self]
    obtain ⟨n, rest, hl, hrest, e3⟩ := exec_incLoop hAt l _ hA2
    have s2 := Stacks.space_update_cons (Function.update σ A l) t false
    rw [Function.update_of_ne hAt.symm] at s2
    refine ⟨n + 1, rest, by rw [hl]; simp [List.replicate_succ], hrest, ?_⟩
    refine .loopT (by simp [hσ, isTrue]) (.seq e1 e2) (exec_of_eq (e3.mono (by omega)) ?_)
    funext j
    simp only [Function.update_apply, List.replicate_succ, List.cons_append]
    split_ifs <;> subst_vars <;> simp_all [replicate_append_cons_same]

/-- **Binary increment.**  With `A, t, C` distinct and `t`, `C` empty, `incr A t C` replaces
`A` by `incBits A` (that is, `binVal A + 1` modulo `2 ^ |A|`, `binVal_incBits`) and leaves the
carry `[incCarry A]` on `C`, within the initial space `+ 1`. -/
theorem exec_incr {A t C : Fin k} (hAt : A ≠ t) (hAC : A ≠ C) (htC : t ≠ C) {σ : Stacks k}
    (ht : σ t = []) (hC : σ C = []) :
    Exec (incr A t C) σ
      (Function.update (Function.update σ A (incBits (σ A))) C [incCarry (σ A)])
      (σ.space + 1) := by
  obtain ⟨n, rest, hl, hrest, e1⟩ := exec_incLoop hAt (σ A) σ rfl
  rw [ht, List.append_nil] at e1
  have sp1 := e1.space_le.2
  have hA1 : (Function.update (Function.update σ A rest) t (List.replicate n false)) A = rest := by
    rw [Function.update_of_ne hAt, Function.update_self]
  have hC1 : (Function.update (Function.update σ A rest) t (List.replicate n false)) C = [] := by
    rw [Function.update_of_ne htC.symm, Function.update_of_ne hAC.symm, hC]
  obtain ⟨σ2, e2, hσ2⟩ : ∃ σ2, Exec (.ite A Option.isSome
        (seqs [.pop A, .push A true, .push C false]) (.push C true))
      (Function.update (Function.update σ A rest) t (List.replicate n false)) σ2 (σ.space + 1) ∧
      σ2 = Function.update (Function.update (Function.update (Function.update σ A rest) t
        (List.replicate n false)) A (incBits rest)) C [incCarry rest] := by
    cases rest with
    | nil =>
      have e := Exec.push (r := C) (b := true)
        (σ := Function.update (Function.update σ A []) t (List.replicate n false))
        (S := σ.space + 1) (by omega)
      rw [hC1] at e
      refine ⟨_, .iteF (by simp [hA1]) e, ?_⟩
      funext j
      simp only [Function.update_apply, incBits, incCarry]
      split_ifs <;> subst_vars <;> simp_all
    | cons b r =>
      have hb : b = false := by cases b <;> simp_all
      subst hb
      have s1 := space_update_of_cons hA1
      have p1 := exec_pop_cons hA1 (S := σ.space + 1) (by omega)
      have p2 := Exec.push (r := A) (b := true) (σ := Function.update (Function.update
        (Function.update σ A (false :: r)) t (List.replicate n false)) A r)
        (S := σ.space + 1) (by omega)
      rw [Function.update_self, Function.update_idem] at p2
      have s2 := Stacks.space_update (Function.update (Function.update σ A (false :: r)) t
        (List.replicate n false)) A (true :: r)
      rw [hA1] at s2
      simp only [List.length_cons] at s2
      have hC2 : (Function.update (Function.update (Function.update σ A (false :: r)) t
          (List.replicate n false)) A (true :: r)) C = [] := by
        rw [Function.update_of_ne hAC.symm]; exact hC1
      have p3 := Exec.push (r := C) (b := false) (σ := Function.update (Function.update
        (Function.update σ A (false :: r)) t (List.replicate n false)) A (true :: r))
        (S := σ.space + 1) (by omega)
      rw [hC2] at p3
      refine ⟨_, .iteT (by simp [hA1]) (.seq p1 (.seq p2 (.seq p3 (.skip p3.space_le.2)))), ?_⟩
      rfl
  subst hσ2
  have sp2 := e2.space_le.2
  have e3 := exec_moveAll hAt.symm _ (Function.update (Function.update (Function.update
    (Function.update σ A rest) t (List.replicate n false)) A (incBits rest)) C [incCarry rest]) rfl
  refine exec_of_eq (.seq (e1.mono (by omega)) (.seq e2 (.seq (e3.mono sp2)
    (.skip (e3.space_le.2.trans sp2))))) ?_
  funext j
  rw [hl, incBits_replicate_append, incCarry_replicate_append]
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

end Stmt

end Kolmogorov.RandomStrings
