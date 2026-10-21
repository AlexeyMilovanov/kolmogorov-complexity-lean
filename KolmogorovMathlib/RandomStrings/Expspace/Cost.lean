/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.GameStmt

/-!
# Cost and budget bit strings

The routines that write cost and budget bit strings (`Stmt.subLoop`, `Stmt.fillLoop`,
`Stmt.emitLoop`) and the cost procedure: from the coded query list and a hardwired table it
computes the fixed-point flip costs and the budget (`exists_costStmt`).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-! ### Cost and budget bit strings: routines -/
namespace Stmt

variable {k : ℕ}

/-- Pop `A` and `B` as long as `A` is nonempty: `B` loses `|A|` bits and `A` is emptied. -/
def subLoop (A B : Fin k) : Stmt k := .loop A Option.isSome (.seq (.pop A) (.pop B))

/-- Space-bounded execution theorem for `subLoop`. -/
theorem exec_subLoop {A B : Fin k} (hAB : A ≠ B) : ∀ (l : BitString) (σ : Stacks k), σ A = l →
    Exec (subLoop A B) σ (Function.update (Function.update σ A []) B ((σ B).drop l.length))
      σ.space
  | [], σ, hσ => by
    refine exec_of_eq (.loopF (by simp [hσ]) le_rfl) ?_
    funext j
    simp only [Function.update_apply, List.length_nil, List.drop_zero]
    split_ifs <;> subst_vars <;> simp_all
  | x :: l, σ, hσ => by
    have s1 := space_update_of_cons hσ
    have e1 := exec_pop_cons hσ (S := σ.space) le_rfl
    have e2 := Exec.pop (r := B) (σ := Function.update σ A l) (S := σ.space) (by omega)
    have s2 := Stacks.space_update_tail_le (Function.update σ A l) B
    rw [Function.update_of_ne hAB.symm] at e2 s2
    have ih := exec_subLoop hAB l (Function.update (Function.update σ A l) B (σ B).tail)
      (by rw [Function.update_of_ne hAB, Function.update_self])
    refine .loopT (by simp [hσ]) (.seq e1 e2) (exec_of_eq (ih.mono (by omega)) ?_)
    funext j
    simp only [Function.update_apply, List.length_cons]
    split_ifs <;> subst_vars <;> simp_all [List.drop_tail]

/-- Pop `K` and push `b` on `R`, as long as `K` is nonempty. -/
def fillLoop (K R : Fin k) (b : Bool) : Stmt k := .loop K Option.isSome (.seq (.pop K) (.push R b))

/-- Space-bounded execution theorem for `fillLoop`. -/
theorem exec_fillLoop {K R : Fin k} (hKR : K ≠ R) (b : Bool) : ∀ (l : BitString) (σ : Stacks k),
    σ K = l → Exec (fillLoop K R b) σ
      (Function.update (Function.update σ K []) R (List.replicate l.length b ++ σ R)) σ.space
  | [], σ, hσ => by
    refine exec_of_eq (.loopF (by simp [hσ]) le_rfl) ?_
    funext j
    simp only [Function.update_apply, List.length_nil, List.replicate_zero, List.nil_append]
    split_ifs <;> subst_vars <;> simp_all
  | x :: l, σ, hσ => by
    have s1 := space_update_of_cons hσ
    have e1 := exec_pop_cons hσ (S := σ.space) le_rfl
    have e2 := Exec.push (r := R) (b := b) (σ := Function.update σ K l) (S := σ.space) (by omega)
    have s2 := Stacks.space_update_cons (Function.update σ K l) R b
    rw [Function.update_of_ne hKR.symm] at e2 s2
    have ih := exec_fillLoop hKR b l (Function.update (Function.update σ K l) R (b :: σ R))
      (by rw [Function.update_of_ne hKR, Function.update_self])
    refine .loopT (by simp [hσ]) (.seq e1 e2) (exec_of_eq (ih.mono (by omega)) ?_)
    funext j
    simp only [Function.update_apply, List.length_cons]
    split_ifs <;> subst_vars <;> simp_all [List.replicate_succ, replicate_append_cons_same]

/-- `j` pairs `b, true`: the reversed code of `j` copies of the bit `b`. -/
def emitStr (j : ℕ) (b : Bool) : BitString := (List.replicate j [b, true]).flatten

/-- Emit a bit block appended with `[b, true]`. -/
theorem emitStr_succ (j : ℕ) (b : Bool) : emitStr (j + 1) b = emitStr j b ++ [b, true] := by
  simp [emitStr, List.replicate_succ']

/-- Emit a bit block consed with `b :: true ::`. -/
theorem emitStr_succ' (j : ℕ) (b : Bool) : emitStr (j + 1) b = b :: true :: emitStr j b := by
  simp [emitStr, List.replicate_succ]

/-- The length of a bit block emitted by `emitStr`. -/
theorem length_emitStr (j : ℕ) (b : Bool) : (emitStr j b).length = 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [emitStr_succ', List.length_cons, List.length_cons, ih]; ring

/-- For each bit of `K`: pop `K` and `B`, and push `true, b` on `R`. -/
def emitLoop (K B R : Fin k) (b : Bool) : Stmt k :=
  .loop K Option.isSome (seqs [.pop K, .pop B, .push R true, .push R b])

/-- Space-bounded execution theorem for `emitLoop`. -/
theorem exec_emitLoop {K B R : Fin k} (hKB : K ≠ B) (hKR : K ≠ R) (hBR : B ≠ R) (b : Bool) :
    ∀ (l : BitString) (σ : Stacks k), σ K = l →
      Exec (emitLoop K B R b) σ (Function.update (Function.update (Function.update σ K [])
        B ((σ B).drop l.length)) R (emitStr l.length b ++ σ R)) (σ.space + l.length)
  | [], σ, hσ => by
    refine exec_of_eq (.loopF (by simp [hσ]) (by simp)) ?_
    funext j
    simp only [Function.update_apply, List.length_nil, List.drop_zero, emitStr,
      List.replicate_zero, List.flatten_nil, List.nil_append]
    split_ifs <;> subst_vars <;> simp_all
  | x :: l, σ, hσ => by
    have s1 := space_update_of_cons hσ
    have e1 := exec_pop_cons hσ (S := σ.space + (x :: l).length) (by simp)
    have e2 := Exec.pop (r := B) (σ := Function.update σ K l) (S := σ.space + (x :: l).length)
      (by simp only [List.length_cons]; omega)
    have s2 := Stacks.space_update_tail_le (Function.update σ K l) B
    rw [Function.update_of_ne hKB.symm] at e2 s2
    set σ2 := Function.update (Function.update σ K l) B (σ B).tail with hσ2
    have e3 := Exec.push (r := R) (b := true) (σ := σ2) (S := σ.space + (x :: l).length)
      (by simp only [List.length_cons]; omega)
    have s3 := Stacks.space_update_cons σ2 R true
    set σ3 := Function.update σ2 R (true :: σ2 R) with hσ3
    have e4 := Exec.push (r := R) (b := b) (σ := σ3) (S := σ.space + (x :: l).length)
      (by simp only [List.length_cons]; omega)
    have s4 := Stacks.space_update_cons σ3 R b
    have hK : (Function.update σ3 R (b :: σ3 R)) K = l := by
      simp [hσ3, hσ2, hKR, hKB]
    have ih := exec_emitLoop hKB hKR hBR b l _ hK
    refine .loopT (by simp [hσ]) (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.skip e4.space_le.2)))))
      (exec_of_eq (ih.mono (by simp only [List.length_cons]; omega)) ?_)
    funext j
    simp only [hσ3, hσ2, Function.update_apply, List.length_cons, emitStr_succ]
    split_ifs <;> subst_vars <;> simp_all [List.drop_tail]

end Stmt

/-! #### The cost procedure (`exists_costStmt`) -/

/-- The stacks of the cost procedure (14 stacks): `0` the input `encList LX`, `1`, `2` the
outputs, `3` the strings still to be processed, `4` the costs computed so far (reversed code),
`5` the current string (reversed), `6` its value (unary), `7`–`9` unary counters; the work stacks
`10`–`13` are empty. -/
def costSt (x0 o1 o2 L R Z Hs K1 K2 KW : BitString) : Stacks 14 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _ => []) 0 x0) 1 o1) 2 o2) 3 L) 4 R) 5 Z) 6 Hs) 7 K1) 8 K2) 9 KW

/-- Space size of the cost procedure stacks. -/
theorem costSt_space (x0 o1 o2 L R Z Hs K1 K2 KW : BitString) :
    (costSt x0 o1 o2 L R Z Hs K1 K2 KW).space = x0.length + o1.length + o2.length + L.length +
      R.length + Z.length + Hs.length + K1.length + K2.length + KW.length := by
  simp [Stacks.space, costSt, Fin.sum_univ_succ, Function.update_apply]
  ring

/-- `T.fn z` through a list `tl` of table entries (the first equal entry gives the value). -/
def tabVal (T : Table) : List BitString → BitString → ℕ
  | [], z => 2 * z.length + 6
  | t :: tl, z => if z = t then T.value t else tabVal T tl z

/-- The numerical table value evaluated via the cost procedure. -/
theorem tabVal_eq (T : Table) (z : BitString) : ∀ tl : List BitString,
    tabVal T tl z = if z ∈ tl then T.value z else 2 * z.length + 6
  | [] => by simp [tabVal]
  | t :: tl => by
    rw [tabVal, tabVal_eq T z tl]
    by_cases h : z = t
    · subst h; simp
    · simp [h]

/-- Tabulation of the numerical table value via the cost procedure. -/
theorem tabVal_toList (T : Table) (z : BitString) : tabVal T T.dom.toList z = T.fn z := by
  rw [tabVal_eq, Table.fn]
  simp only [Finset.mem_toList]

/-- The total size of the table entries `tl`. -/
def tabSize (T : Table) (tl : List BitString) : ℕ := (tl.map fun t => t.length + T.value t).sum

/-- Push `tabVal T tl z` unary digits on stack `6`, the string `z` being on stack `5`, reversed
(work stacks `10`–`13`): compare `z` with the entries of `tl` (`Stmt.eqTest`), the default
`2 |z| + 6` by two copies of `z` and six more digits. -/
def costTab (T : Table) : List BitString → Stmt 14
  | [] => Stmt.seqs [Stmt.copy 5 6 11, Stmt.copy 5 6 11, Stmt.pushList 6 (List.replicate 6 true)]
  | t :: tl => Stmt.seqs [Stmt.pushList 10 t.reverse, Stmt.eqTest 5 10 11 12 13, Stmt.clear 10,
      .ite 13 Stmt.isTrue (.seq (.pop 13) (Stmt.pushList 6 (List.replicate (T.value t) true)))
        (.seq (.pop 13) (costTab T tl))]

/-- Space-bounded execution theorem for `costTab`. -/
theorem exec_costTab (T : Table) (x0 o1 o2 L R Z K1 K2 KW : BitString) : ∀ tl : List BitString,
    ∃ hs : BitString, hs.length = tabVal T tl Z.reverse ∧
      Exec (costTab T tl) (costSt x0 o1 o2 L R Z [] K1 K2 KW) (costSt x0 o1 o2 L R Z hs K1 K2 KW)
        ((costSt x0 o1 o2 L R Z [] K1 K2 KW).space + 2 * Z.length + tabSize T tl + 7)
  | [] => by
    have hsp := costSt_space x0 o1 o2 L R Z [] K1 K2 KW
    have e1 : Exec (Stmt.copy 5 6 11) (costSt x0 o1 o2 L R Z [] K1 K2 KW)
        (costSt x0 o1 o2 L R Z (Z ++ []) K1 K2 KW)
        ((costSt x0 o1 o2 L R Z [] K1 K2 KW).space + Z.length) :=
      Stmt.exec_of_eq (Stmt.exec_copy (r := 5) (r' := 6) (t := 11) (by decide) (by decide)
        (by decide) rfl) (by funext j; fin_cases j <;> rfl)
    have e2 : Exec (Stmt.copy 5 6 11) (costSt x0 o1 o2 L R Z (Z ++ []) K1 K2 KW)
        (costSt x0 o1 o2 L R Z (Z ++ (Z ++ [])) K1 K2 KW)
        ((costSt x0 o1 o2 L R Z (Z ++ []) K1 K2 KW).space + Z.length) :=
      Stmt.exec_of_eq (Stmt.exec_copy (r := 5) (r' := 6) (t := 11) (by decide) (by decide)
        (by decide) rfl) (by funext j; fin_cases j <;> rfl)
    have e3 : Exec (Stmt.pushList 6 (List.replicate 6 true))
        (costSt x0 o1 o2 L R Z (Z ++ (Z ++ [])) K1 K2 KW)
        (costSt x0 o1 o2 L R Z (List.replicate 6 true ++ (Z ++ (Z ++ []))) K1 K2 KW)
        ((costSt x0 o1 o2 L R Z (Z ++ (Z ++ [])) K1 K2 KW).space +
          (List.replicate 6 true).length) :=
      Stmt.exec_of_eq (Stmt.exec_pushList 6 _ _) (by funext j; fin_cases j <;> rfl)
    have h1 := costSt_space x0 o1 o2 L R Z (Z ++ []) K1 K2 KW
    have h2 := costSt_space x0 o1 o2 L R Z (Z ++ (Z ++ [])) K1 K2 KW
    simp only [List.length_append, List.length_nil, List.length_replicate] at hsp h1 h2 e3
    refine ⟨List.replicate 6 true ++ (Z ++ (Z ++ [])), by simp [tabVal]; ring, ?_⟩
    refine .seq (e1.mono (by omega)) (.seq (e2.mono (by omega)) (.seq (e3.mono (by omega))
      (.skip ?_)))
    have := e3.space_le.2
    omega
  | t :: tl => by
    set σ0 := costSt x0 o1 o2 L R Z [] K1 K2 KW with hσ0
    have e1 : Exec (Stmt.pushList 10 t.reverse) σ0 (Function.update σ0 10 t.reverse)
        (σ0.space + t.reverse.length) :=
      Stmt.exec_of_eq (Stmt.exec_pushList 10 t.reverse σ0)
        (by rw [show σ0 10 = [] from rfl, List.append_nil])
    have s1 := Stacks.space_update_nil σ0 10 t.reverse rfl
    set σ1 : Stacks 14 := Function.update σ0 10 t.reverse with hσ1
    have e2 : Exec (Stmt.eqTest 5 10 11 12 13) σ1
        (Function.update σ1 13 [decide (Z = t.reverse)]) (σ1.space + 1) :=
      Stmt.exec_eqTest (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
    have s2 := Stacks.space_update_nil σ1 13 [decide (Z = t.reverse)] rfl
    have e3 : Exec (Stmt.clear 10) (Function.update σ1 13 [decide (Z = t.reverse)])
        (Function.update σ0 13 [decide (Z = t.reverse)])
        (Stacks.space (Function.update σ1 13 [decide (Z = t.reverse)])) :=
      Stmt.exec_of_eq (Stmt.exec_clear 10 _ _ rfl) (by funext j; fin_cases j <;> rfl)
    have s3 := Stacks.space_update_nil σ0 13 [decide (Z = t.reverse)] rfl
    have hts : tabSize T (t :: tl) = t.length + T.value t + tabSize T tl := by
      simp only [tabSize, List.map_cons, List.sum_cons]
    obtain ⟨hs, hhs, ih⟩ := exec_costTab T x0 o1 o2 L R Z K1 K2 KW tl
    rw [← hσ0] at ih
    simp only [List.length_reverse, List.length_cons, List.length_nil] at s1 s2 s3 e1
    by_cases hzt : Z = t.reverse
    · -- the entry matches
      have hd : decide (Z = t.reverse) = true := decide_eq_true hzt
      rw [hd] at e2 e3 s2 s3
      have e4 : Exec (.pop 13) (Function.update σ0 13 [true]) σ0
          (Stacks.space (Function.update σ0 13 [true])) :=
        Stmt.exec_of_eq (Exec.pop le_rfl) (by funext j; fin_cases j <;> rfl)
      have e5 : Exec (Stmt.pushList 6 (List.replicate (T.value t) true)) σ0
          (costSt x0 o1 o2 L R Z (List.replicate (T.value t) true ++ []) K1 K2 KW)
          (σ0.space + (List.replicate (T.value t) true).length) :=
        Stmt.exec_of_eq (Stmt.exec_pushList 6 _ _) (by funext j; fin_cases j <;> rfl)
      simp only [List.length_replicate] at e5
      refine ⟨List.replicate (T.value t) true ++ [], ?_, ?_⟩
      · simp [tabVal, hzt]
      · refine .seq (e1.mono (by omega)) (.seq (e2.mono (by omega)) (.seq (e3.mono (by omega))
          (.seq (.iteT (by rfl) (.seq (e4.mono (by omega)) (e5.mono (by omega)))) (.skip ?_))))
        have := e5.space_le.2
        omega
    · -- the entry does not match: continue with the rest of the table
      have hd : decide (Z = t.reverse) = false := decide_eq_false hzt
      rw [hd] at e2 e3 s2 s3
      have e4 : Exec (.pop 13) (Function.update σ0 13 [false]) σ0
          (Stacks.space (Function.update σ0 13 [false])) :=
        Stmt.exec_of_eq (Exec.pop le_rfl) (by funext j; fin_cases j <;> rfl)
      refine ⟨hs, ?_, ?_⟩
      · rw [hhs, tabVal, ite_eq_right (fun h => hzt (by rw [← h, List.reverse_reverse]))]
      · refine .seq (e1.mono (by omega)) (.seq (e2.mono (by omega)) (.seq (e3.mono (by omega))
          (.seq (.iteF (by rfl) (.seq (e4.mono (by omega)) (ih.mono (by omega)))) (.skip ?_))))
        have := ih.space_le.2
        omega

/-- The cost bit string at precision `N` and width `W` of a string of value `h` with `a = |z| - 1`:
ones exactly at the positions `N - h, …, N - a - 1`. -/
def costBits (N W h a : ℕ) : BitString :=
  List.replicate (N - h) false ++ List.replicate (h - a) true ++
    List.replicate (W - (N - h) - (h - a)) false

/-- Expanding reversed logic strings over list replications. -/
theorem rev_flatMap_replicate (j : ℕ) (b : Bool) :
    ((List.replicate j b).flatMap fun x => [true, x]).reverse = Stmt.emitStr j b := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ', List.flatMap_append, List.reverse_append, ih, Stmt.emitStr_succ']
    simp

/-- Encoding cost bits in reverse logic form. -/
theorem encStr_costBits_rev (N W h a : ℕ) (r : BitString) :
    (Stacks.encStr (costBits N W h a)).reverse ++ r =
      false :: (Stmt.emitStr (W - (N - h) - (h - a)) false ++ (Stmt.emitStr (h - a) true ++
        (Stmt.emitStr (N - h) false ++ r))) := by
  simp only [Stacks.encStr, costBits, List.flatMap_append, List.reverse_append,
    rev_flatMap_replicate]
  simp

/-- The body of the cost loop: decode the next string `z` (stack `3`, reversed onto `5`), compute
its value `h` (stack `6`), the counters `N - h` (stack `7`), `h - (|z| - 1)` (stack `8`) and the
width `W` (stack `9`) in unary, and push the reversed code of `costBits N W h (|z| - 1)` on
stack `4` (`N = |x0| + c`, `W = 2 |x0| + c + 1`, `x0` the input on stack `0`). -/
def costBody (T : Table) (tl : List BitString) (c : ℕ) : Stmt 14 :=
  Stmt.seqs [Stmt.decodeOne 3 5 9, Stmt.clear 9, costTab T tl, .pop 5, Stmt.copy 6 8 11,
    Stmt.subLoop 5 8, Stmt.copy 0 7 11, Stmt.pushList 7 (List.replicate c true),
    Stmt.subLoop 6 7, Stmt.copy 0 9 11, Stmt.copy 0 9 11,
    Stmt.pushList 9 (List.replicate (c + 1) true), Stmt.emitLoop 7 9 4 false,
    Stmt.emitLoop 8 9 4 true, Stmt.emitLoop 9 5 4 false, .push 4 false]

/-- Executing two statement lists one after the other executes their concatenation. -/
private theorem costBody_seqs_append :
    ∀ (l₁ l₂ : List (Stmt 14)) {σ μ τ : Stacks 14} {S : ℕ},
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
      exact ⟨ν, hs, costBody_seqs_append l₁ _ hr h₂⟩

/-- `copy r r' t` onto an empty stack `r'` makes `r'` a copy of `r`, within the initial space
plus `|r|`. -/
private theorem exec_copy_nil {k : ℕ} {r r' t : Fin k} (hrr : r ≠ r') (hrt : r ≠ t)
    (hr't : r' ≠ t) {σ : Stacks k} {v : BitString} (ht : σ t = []) (hr : σ r = v)
    (hr' : σ r' = []) :
    Exec (Stmt.copy r r' t) σ (Function.update σ r' v) (σ.space + v.length) := by
  have h := Stmt.exec_copy hrr hrt hr't ht
  rwa [hr, hr', List.append_nil] at h

/-- The counters of `costBody`: given the value `hs` of the current string (stack `6`) and the rest
`Zt` of its reversed form (stack `5`), these statements empty the stacks `5`, `6` and leave on the
stacks `7`, `8`, `9` unary counters `K1`, `K2`, `KW` of lengths `|x0| + c - |hs|`, `|hs| - |Zt|`
and `2 |x0| + c + 1`. -/
private theorem exec_costCounters (x0 rest r Zt hs : BitString) (c S : ℕ)
    (hh : hs.length ≤ x0.length + c)
    (hS : 4 * x0.length + 3 * c + rest.length + r.length + Zt.length + 1 ≤ S) :
    ∃ K1 K2 KW : BitString, K1.length = x0.length + c - hs.length ∧
      K2.length = hs.length - Zt.length ∧ KW.length = 2 * x0.length + c + 1 ∧
      Exec (Stmt.seqs [Stmt.copy 6 8 11, Stmt.subLoop 5 8, Stmt.copy 0 7 11,
        Stmt.pushList 7 (List.replicate c true), Stmt.subLoop 6 7, Stmt.copy 0 9 11,
        Stmt.copy 0 9 11, Stmt.pushList 9 (List.replicate (c + 1) true)])
        (costSt x0 [] [] rest r Zt hs [] [] []) (costSt x0 [] [] rest r [] [] K1 K2 KW) S := by
  set P : BitString := List.replicate c true ++ x0 with hPd
  set Q : BitString := hs.drop Zt.length with hQd
  set K1 : BitString := P.drop hs.length with hK1d
  set V : BitString := List.replicate (c + 1) true ++ (x0 ++ x0) with hVd
  have hP : P.length = x0.length + c := by
    rw [hPd, List.length_append, List.length_replicate]; omega
  have hQ : Q.length = hs.length - Zt.length := by rw [hQd, List.length_drop]
  have hK : K1.length = x0.length + c - hs.length := by rw [hK1d, List.length_drop, hP]
  have hV : V.length = 2 * x0.length + c + 1 := by
    rw [hVd, List.length_append, List.length_append, List.length_replicate]; omega
  have e1 : Exec (Stmt.copy 6 8 11) (costSt x0 [] [] rest r Zt hs [] [] [])
      (costSt x0 [] [] rest r Zt hs [] hs []) S :=
    Exec.mono (Stmt.exec_of_eq
      (exec_copy_nil (v := hs) (by decide) (by decide) (by decide) rfl rfl rfl)
      (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil]; omega)
  have e2 : Exec (Stmt.subLoop 5 8) (costSt x0 [] [] rest r Zt hs [] hs [])
      (costSt x0 [] [] rest r [] hs [] Q []) S :=
    Exec.mono (Stmt.exec_of_eq (Stmt.exec_subLoop (A := 5) (B := 8) (by decide) _ _ rfl)
      (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil]; omega)
  have e3 : Exec (Stmt.copy 0 7 11) (costSt x0 [] [] rest r [] hs [] Q [])
      (costSt x0 [] [] rest r [] hs x0 Q []) S :=
    Exec.mono (Stmt.exec_of_eq
      (exec_copy_nil (v := x0) (by decide) (by decide) (by decide) rfl rfl rfl)
      (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil]; omega)
  have e4 : Exec (Stmt.pushList 7 (List.replicate c true))
      (costSt x0 [] [] rest r [] hs x0 Q []) (costSt x0 [] [] rest r [] hs P Q []) S :=
    Exec.mono (Stmt.exec_of_eq (Stmt.exec_pushList 7 _ _) (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil, List.length_replicate]; omega)
  have e5 : Exec (Stmt.subLoop 6 7) (costSt x0 [] [] rest r [] hs P Q [])
      (costSt x0 [] [] rest r [] [] K1 Q []) S :=
    Exec.mono (Stmt.exec_of_eq (Stmt.exec_subLoop (A := 6) (B := 7) (by decide) _ _ rfl)
      (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil]; omega)
  have e6 : Exec (Stmt.copy 0 9 11) (costSt x0 [] [] rest r [] [] K1 Q [])
      (costSt x0 [] [] rest r [] [] K1 Q x0) S :=
    Exec.mono (Stmt.exec_of_eq
      (exec_copy_nil (v := x0) (by decide) (by decide) (by decide) rfl rfl rfl)
      (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil]; omega)
  have e7 : Exec (Stmt.copy 0 9 11) (costSt x0 [] [] rest r [] [] K1 Q x0)
      (costSt x0 [] [] rest r [] [] K1 Q (x0 ++ x0)) S :=
    Exec.mono (Stmt.exec_of_eq
      (Stmt.exec_copy (r := 0) (r' := 9) (t := 11) (by decide) (by decide) (by decide) rfl)
      (by funext j; fin_cases j <;> rfl))
      (by change (costSt x0 [] [] rest r [] [] K1 Q x0).space + x0.length ≤ S
          simp only [costSt_space, List.length_nil]; omega)
  have e8 : Exec (Stmt.pushList 9 (List.replicate (c + 1) true))
      (costSt x0 [] [] rest r [] [] K1 Q (x0 ++ x0)) (costSt x0 [] [] rest r [] [] K1 Q V) S :=
    Exec.mono (Stmt.exec_of_eq (Stmt.exec_pushList 9 _ _) (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil, List.length_replicate, List.length_append]
          omega)
  exact ⟨K1, Q, V, hK, hQ, hV, .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7
    (.seq e8 (.skip e8.space_le.2))))))))⟩

/-- The emit phase of `costBody`: `emitLoop` on the counters `K1`, `K2` and on what is left of `KW`
writes `2 |K1|`, `2 |K2|` and `2 (|KW| - |K1| - |K2|)` bits on stack `4`, and a final `false` is
pushed there. -/
private theorem exec_costEmit (x0 rest r K1 K2 KW : BitString) (S : ℕ)
    (hK : K1.length + K2.length ≤ KW.length)
    (hS : x0.length + rest.length + r.length + 3 * KW.length + 1 ≤ S) :
    Exec (Stmt.seqs [Stmt.emitLoop 7 9 4 false, Stmt.emitLoop 8 9 4 true,
        Stmt.emitLoop 9 5 4 false, .push 4 false])
      (costSt x0 [] [] rest r [] [] K1 K2 KW)
      (costSt x0 [] [] rest (false :: (Stmt.emitStr (KW.length - K1.length - K2.length) false ++
        (Stmt.emitStr K2.length true ++ (Stmt.emitStr K1.length false ++ r)))) [] [] [] [] [])
      S := by
  set W : BitString := (KW.drop K1.length).drop K2.length with hWd
  have hW : W.length = KW.length - K1.length - K2.length := by
    rw [hWd, List.length_drop, List.length_drop]
  have e1 : Exec (Stmt.emitLoop 7 9 4 false) (costSt x0 [] [] rest r [] [] K1 K2 KW)
      (costSt x0 [] [] rest (Stmt.emitStr K1.length false ++ r) [] [] [] K2 (KW.drop K1.length))
      S :=
    Exec.mono (Stmt.exec_of_eq
      (Stmt.exec_emitLoop (by decide) (by decide) (by decide) false K1 _ rfl)
      (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil]; omega)
  have e2 : Exec (Stmt.emitLoop 8 9 4 true)
      (costSt x0 [] [] rest (Stmt.emitStr K1.length false ++ r) [] [] [] K2 (KW.drop K1.length))
      (costSt x0 [] [] rest (Stmt.emitStr K2.length true ++ (Stmt.emitStr K1.length false ++ r))
        [] [] [] [] W) S :=
    Exec.mono (Stmt.exec_of_eq
      (Stmt.exec_emitLoop (by decide) (by decide) (by decide) true K2 _ rfl)
      (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil, List.length_append, Stmt.length_emitStr,
            List.length_drop]
          omega)
  have e3 : Exec (Stmt.emitLoop 9 5 4 false)
      (costSt x0 [] [] rest (Stmt.emitStr K2.length true ++ (Stmt.emitStr K1.length false ++ r))
        [] [] [] [] W)
      (costSt x0 [] [] rest (Stmt.emitStr W.length false ++
        (Stmt.emitStr K2.length true ++ (Stmt.emitStr K1.length false ++ r))) [] [] [] [] [])
      S :=
    Exec.mono (Stmt.exec_of_eq
      (Stmt.exec_emitLoop (by decide) (by decide) (by decide) false W _ rfl)
      (by funext j; fin_cases j <;> first | rfl | simp [costSt]))
      (by simp only [costSt_space, List.length_nil, List.length_append, Stmt.length_emitStr]
          omega)
  have e4 : Exec (.push 4 false)
      (costSt x0 [] [] rest (Stmt.emitStr W.length false ++
        (Stmt.emitStr K2.length true ++ (Stmt.emitStr K1.length false ++ r))) [] [] [] [] [])
      (costSt x0 [] [] rest (false :: (Stmt.emitStr W.length false ++
        (Stmt.emitStr K2.length true ++ (Stmt.emitStr K1.length false ++ r)))) [] [] [] [] [])
      S :=
    Stmt.exec_of_eq (Exec.push (by
      simp only [costSt_space, List.length_nil, List.length_append, Stmt.length_emitStr]
      omega)) (by funext j; fin_cases j <;> rfl)
  rw [hW] at e3 e4
  exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.skip e4.space_le.2))))

/-- One iteration of the cost loop: `costBody` run on the coded list `encStr z ++ rest` consumes
`z` and pushes the reversed code of `costBits (|x0| + c) (2 |x0| + c + 1) (tabVal T tl z) (|z| - 1)`
on stack `4`, within the space `S`. -/
theorem exec_costBody (T : Table) (tl : List BitString) (c : ℕ) (x0 z rest r : BitString)
    (hz : 2 * z.length + 1 ≤ x0.length) (hh : tabVal T tl z ≤ x0.length + c) :
    Exec (costBody T tl c) (costSt x0 [] [] (Stacks.encStr z ++ rest) r [] [] [] [] [])
      (costSt x0 [] [] rest ((Stacks.encStr (costBits (x0.length + c) (2 * x0.length + c + 1)
        (tabVal T tl z) (z.length - 1))).reverse ++ r) [] [] [] [] [])
      (x0.length + (Stacks.encStr z).length + rest.length + r.length + 8 * x0.length +
        4 * c + tabSize T tl + 12) := by
  generalize hSdef : x0.length + (Stacks.encStr z).length + rest.length + r.length +
    8 * x0.length + 4 * c + tabSize T tl + 12 = S
  have e1 : Exec (Stmt.decodeOne 3 5 9)
      (costSt x0 [] [] (Stacks.encStr z ++ rest) r [] [] [] [] [])
      (costSt x0 [] [] rest r z.reverse [] [] [] (Stacks.encStr z).reverse) S :=
    Exec.mono (Stmt.exec_of_eq
      (Stmt.exec_decodeOne (Lst := 3) (W := 5) (Tmp := 9) (by decide) (by decide) (by decide) rfl)
      (by funext j; fin_cases j <;> first | rfl | simp [costSt]))
      (by simp only [costSt_space, List.length_nil, List.length_append]; omega)
  have e2 : Exec (Stmt.clear 9)
      (costSt x0 [] [] rest r z.reverse [] [] [] (Stacks.encStr z).reverse)
      (costSt x0 [] [] rest r z.reverse [] [] [] []) S :=
    Exec.mono (Stmt.exec_of_eq (Stmt.exec_clear 9 _ _ rfl) (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil, List.length_reverse]; omega)
  obtain ⟨hs, hhs, e3⟩ := exec_costTab T x0 [] [] rest r z.reverse [] [] [] tl
  rw [List.reverse_reverse] at hhs
  have e3' : Exec (costTab T tl) (costSt x0 [] [] rest r z.reverse [] [] [] [])
      (costSt x0 [] [] rest r z.reverse hs [] [] []) S :=
    Exec.mono e3 (by simp only [costSt_space, List.length_nil, List.length_reverse]; omega)
  have e4 : Exec (.pop 5) (costSt x0 [] [] rest r z.reverse hs [] [] [])
      (costSt x0 [] [] rest r z.reverse.tail hs [] [] []) S :=
    Exec.mono (Stmt.exec_of_eq (Exec.pop le_rfl) (by funext j; fin_cases j <;> rfl))
      (by simp only [costSt_space, List.length_nil, List.length_reverse]; omega)
  have hzt : z.reverse.tail.length = z.length - 1 := by simp
  have hSB : 4 * x0.length + 3 * c + rest.length + r.length + z.reverse.tail.length + 1 ≤ S := by
    omega
  obtain ⟨K1, K2, KW, hK1, hK2, hKW, e5⟩ :=
    exec_costCounters x0 rest r z.reverse.tail hs c S (hhs.le.trans hh) hSB
  have hKle : K1.length + K2.length ≤ KW.length := by omega
  have hSC : x0.length + rest.length + r.length + 3 * KW.length + 1 ≤ S := by omega
  have e6 := exec_costEmit x0 rest r K1 K2 KW S hKle hSC
  rw [hKW, hK1, hK2, hzt, hhs] at e6
  rw [encStr_costBits_rev]
  exact .seq e1 (.seq e2 (.seq e3' (.seq e4 (costBody_seqs_append _ _ e5 e6))))

/-- The exact length of the bit string emitted by `costBits`. -/
theorem length_costBits (N W h a : ℕ) (h1 : h ≤ N) (h2 : N ≤ W) :
    (costBits N W h a).length = W := by
  simp only [costBits, List.length_append, List.length_replicate]
  omega

/-- The cost loop: the body `costBody` for each string of the list on stack `3`. -/
theorem exec_costLoop (T : Table) (tl : List BitString) (c : ℕ) (x0 : BitString) :
    ∀ (LX : List BitString) (r : BitString) (S : ℕ),
      (∀ z ∈ LX, 2 * z.length + 1 ≤ x0.length ∧ tabVal T tl z ≤ x0.length + c) →
      x0.length + (Stacks.encList LX).length + r.length +
        LX.length * (4 * x0.length + 2 * c + 3) + 8 * x0.length + 4 * c + tabSize T tl + 12 ≤ S →
      Exec (.loop 3 Option.isSome (costBody T tl c))
        (costSt x0 [] [] (Stacks.encList LX) r [] [] [] [] [])
        (costSt x0 [] [] [] ((Stacks.encList (LX.map fun z => costBits (x0.length + c)
          (2 * x0.length + c + 1) (tabVal T tl z) (z.length - 1))).reverse ++ r) [] [] [] [] []) S
  | [], r, S, _, hS => by
    have hsp := costSt_space x0 [] [] (Stacks.encList []) r [] [] [] [] []
    refine Stmt.exec_of_eq (.loopF rfl ?_) rfl
    simp only [List.length_nil] at hsp hS
    omega
  | z :: LX, r, S, hLX, hS => by
    obtain ⟨hz, hh⟩ := hLX z List.mem_cons_self
    have hlen : (Stacks.encList (z :: LX)).length =
        (Stacks.encStr z).length + (Stacks.encList LX).length := by
      rw [QEnum.encList_cons, List.length_append]
    have hcb := length_costBits (x0.length + c) (2 * x0.length + c + 1) (tabVal T tl z)
      (z.length - 1) hh (by omega)
    have hm : (LX.length + 1) * (4 * x0.length + 2 * c + 3) =
        LX.length * (4 * x0.length + 2 * c + 3) + (4 * x0.length + 2 * c + 3) := by ring
    have hez := Stacks.length_encStr (costBits (x0.length + c) (2 * x0.length + c + 1)
      (tabVal T tl z) (z.length - 1))
    rw [List.length_cons, hm, hlen] at hS
    have e := (exec_costBody T tl c x0 z (Stacks.encList LX) r hz hh).mono (S' := S) (by omega)
    have ih := exec_costLoop T tl c x0 LX ((Stacks.encStr (costBits (x0.length + c)
      (2 * x0.length + c + 1) (tabVal T tl z) (z.length - 1))).reverse ++ r) S
      (fun z' hz' => hLX z' (List.mem_cons_of_mem _ hz'))
      (by simp only [List.length_append, List.length_reverse]; omega)
    rw [QEnum.encList_cons]
    refine .loopT ?_ e (Stmt.exec_of_eq ih ?_)
    · cases z <;> rfl
    · simp [QEnum.encList_cons, List.reverse_append, List.append_assoc]

/-- The cost procedure: copy the input to stack `3`, run the cost loop, move the costs to stack
`1`, and write the budget `powBits W (N - m)` on stack `2` (in unary: `|x0| + m` zeros, a one,
`|x0| + c - m` zeros, pushed in this order). -/
def costProg (T : Table) (tl : List BitString) (m c : ℕ) : Stmt 14 :=
  Stmt.seqs [Stmt.copy 0 3 11, .loop 3 Option.isSome (costBody T tl c), Stmt.moveAll 4 1,
    Stmt.copy 0 7 11, Stmt.pushList 7 (List.replicate m true), Stmt.fillLoop 7 2 false,
    .push 2 true, Stmt.copy 0 7 11, Stmt.pushList 7 (List.replicate (c - m) true),
    Stmt.fillLoop 7 2 false]

/-- The numerical value of the bit block emitted by `costBody` is the intended cost numerator.
Expand `costBits`, use `binVal_append` and `binVal_replicate_false`, and split on `a ≤ h`;
in the positive branch the finite geometric sum represented by the middle block telescopes.
The hypotheses ensure that none of the three block lengths truncate unexpectedly. -/
private lemma binVal_replicate_true (n : ℕ) : binVal (List.replicate n true) = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, binVal, ih]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

/-- The numerical binary value of `costBits`. -/
theorem binVal_costBits (N W h a : ℕ) (hh : h ≤ N) (hNW : N < W) :
    binVal (costBits N W h a) = if a ≤ h then 2 ^ (N - a) - 2 ^ (N - h) else 0 := by
  have _ := hNW
  unfold costBits
  rw [binVal_append, binVal_append, binVal_replicate_false,
    binVal_replicate_false, binVal_replicate_true]
  rw [List.length_append, List.length_replicate, List.length_replicate,
    zero_add, mul_zero, add_zero]
  split_ifs with h1
  · have h2 : N - a = N - h + (h - a) := by omega
    rw [h2, pow_add]
    have h5 : 2 ^ (N - h) * (2 ^ (h - a) - 1) = 2 ^ (N - h) * 2 ^ (h - a) - 2 ^ (N - h) := by
      calc
        2 ^ (N - h) * (2 ^ (h - a) - 1) = 2 ^ (N - h) * 2 ^ (h - a) - 2 ^ (N - h) * 1 :=
          Nat.mul_sub_left_distrib (2 ^ (N - h)) (2 ^ (h - a)) 1
        _ = 2 ^ (N - h) * 2 ^ (h - a) - 2 ^ (N - h) := by rw [mul_one]
    rw [h5]
  · have : h - a = 0 := by omega
    simp [this]

/-- The fixed choice of `c` makes the encoded input long enough for every per-string loop and
bounds both possible definitions of `T.fn`.  Prove the encoding bound from
`Stacks.length_encList`, isolate the summand belonging to `z`, and unfold `Table.fn`; for a table
entry use `Finset.le_sup`, while the default case follows from the encoding bound. -/
theorem cost_input_bounds (T : Table) (m : ℕ) (LX : List BitString) :
    let x := (Stacks.encList LX).length
    let c := 6 + m + T.dom.sup T.value
    (∀ z ∈ LX, 2 * z.length + 1 ≤ x ∧ tabVal T T.dom.toList z ≤ x + c) ∧
    (∀ z ∈ LX, z.length - 1 ≤ x + c ∧ T.fn z ≤ x + c) ∧ m ≤ x + c := by
  intro x c
  have hm : m ≤ x + c := by
    dsimp [x, c]
    omega
  refine ⟨?_, ?_, hm⟩
  · intro z hz
    have hz2 : 2 * z.length + 1 ≤ x := by
      dsimp [x]
      rw [Stacks.length_encList]
      apply List.single_le_sum (fun _ _ => Nat.zero_le _)
      exact List.mem_map_of_mem (f := fun w : BitString => 2 * w.length + 1) hz
    have htab : tabVal T T.dom.toList z ≤ x + c := by
      dsimp [x, c]
      rw [tabVal_toList, Table.fn]
      split_ifs with h1
      · have : T.value z ≤ T.dom.sup T.value := Finset.le_sup h1
        omega
      · omega
    exact ⟨hz2, htab⟩
  · intro z hz
    have hz1 : z.length - 1 ≤ x + c := by
      dsimp [x, c]
      have : 2 * z.length + 1 ≤ (Stacks.encList LX).length := by
        rw [Stacks.length_encList]
        apply List.single_le_sum (fun _ _ => Nat.zero_le _)
        exact List.mem_map_of_mem (f := fun w : BitString => 2 * w.length + 1) hz
      omega
    have hfn : T.fn z ≤ x + c := by
      dsimp [x, c, Table.fn]
      split_ifs with h1
      · have : T.value z ≤ T.dom.sup T.value := Finset.le_sup h1
        omega
      · have : 2 * z.length + 1 ≤ (Stacks.encList LX).length := by
          rw [Stacks.length_encList]
          apply List.single_le_sum (fun _ _ => Nat.zero_le _)
          exact List.mem_map_of_mem (f := fun w : BitString => 2 * w.length + 1) hz
        omega
    exact ⟨hz1, hfn⟩

/-- Once the cost loop has produced the reversed encoded list on stack `4`, this is the complete
postlude: `moveAll` restores its order, and the two `fillLoop`s surround a single one by the
required numbers of zeroes.  Apply `Stmt.exec_moveAll`, `Stmt.exec_copy`, and
`Stmt.exec_fillLoop` in sequence, simplifying `costSt` and `powBits` after each phase. -/
theorem exec_costProg_postlude (x0 : BitString) (cs : List BitString) (m c S : ℕ) (hm : m ≤ c)
    (hS : x0.length + (Stacks.encList cs).length + (2 * x0.length + c + 1) ≤ S) :
    Exec (Stmt.seqs [Stmt.moveAll 4 1, Stmt.copy 0 7 11,
        Stmt.pushList 7 (List.replicate m true), Stmt.fillLoop 7 2 false, .push 2 true,
        Stmt.copy 0 7 11, Stmt.pushList 7 (List.replicate (c - m) true),
        Stmt.fillLoop 7 2 false])
      (costSt x0 [] [] [] (Stacks.encList cs).reverse [] [] [] [] [])
      (Stacks.layout 14 [x0, Stacks.encList cs,
        powBits (2 * x0.length + c + 1) (x0.length + c - m)]) S := by
  let σ0 := costSt x0 [] [] [] (Stacks.encList cs).reverse [] [] [] [] []
  let σ1 := costSt x0 (Stacks.encList cs) [] [] [] [] [] [] [] []
  let σ2 := costSt x0 (Stacks.encList cs) [] [] [] [] [] x0 [] []
  let σ3 := costSt x0 (Stacks.encList cs) [] [] [] [] []
    (List.replicate m true ++ x0) [] []
  let σ4 := costSt x0 (Stacks.encList cs) (List.replicate (x0.length + m) false) [] []
    [] [] [] [] []
  let σ5 := costSt x0 (Stacks.encList cs)
    (true :: List.replicate (x0.length + m) false) [] [] [] [] [] [] []
  let σ6 := costSt x0 (Stacks.encList cs)
    (true :: List.replicate (x0.length + m) false) [] [] [] [] x0 [] []
  let σ7 := costSt x0 (Stacks.encList cs)
    (true :: List.replicate (x0.length + m) false) [] [] [] []
    (List.replicate (c - m) true ++ x0) [] []
  have e1 : Exec (Stmt.moveAll 4 1) σ0 σ1 S := by
    have e := Stmt.exec_moveAll (k := 14) (r := 4) (r' := 1) (by decide)
      (Stacks.encList cs).reverse σ0 (by simp [σ0, costSt])
    apply (Stmt.exec_of_eq e ?_).mono
    · dsimp [σ0]
      rw [costSt_space]
      simp only [List.length_nil, List.length_reverse, add_zero]
      omega
    · funext j
      fin_cases j <;> simp [σ0, σ1, costSt]
  have e2 : Exec (Stmt.copy 0 7 11) σ1 σ2 S := by
    have e := Stmt.exec_copy (k := 14) (r := 0) (r' := 7) (t := 11)
      (by decide) (by decide) (by decide) (σ := σ1) (by simp [σ1, costSt])
    apply (Stmt.exec_of_eq e ?_).mono
    · dsimp [σ1]
      rw [costSt_space]
      simp only [List.length_nil, add_zero]
      simp [costSt]
      omega
    · funext j
      fin_cases j <;> simp [σ1, σ2, costSt]
  have e3 : Exec (Stmt.pushList 7 (List.replicate m true)) σ2 σ3 S := by
    have e := Stmt.exec_pushList (k := 14) 7 (List.replicate m true) σ2
    apply (Stmt.exec_of_eq e ?_).mono
    · dsimp [σ2]
      rw [costSt_space]
      simp only [List.length_nil, List.length_replicate, add_zero]
      omega
    · funext j
      fin_cases j <;> simp [σ2, σ3, costSt]
  have e4 : Exec (Stmt.fillLoop 7 2 false) σ3 σ4 S := by
    have e := Stmt.exec_fillLoop (k := 14) (K := 7) (R := 2) (by decide) false
      (List.replicate m true ++ x0) σ3 (by simp [σ3, costSt])
    apply (Stmt.exec_of_eq e ?_).mono
    · dsimp [σ3]
      rw [costSt_space]
      simp only [List.length_nil, List.length_append, List.length_replicate, add_zero]
      omega
    · funext j
      fin_cases j <;> simp [σ3, σ4, costSt, Nat.add_comm]
  have e5 : Exec (.push 2 true) σ4 σ5 S := by
    apply Stmt.exec_of_eq (Exec.push (r := (2 : Fin 14)) (b := true) (σ := σ4) (S := S) ?_) ?_
    · dsimp [σ4]
      rw [costSt_space]
      simp only [List.length_nil, List.length_replicate, add_zero]
      omega
    · funext j
      fin_cases j <;> simp [σ4, σ5, costSt]
  have e6 : Exec (Stmt.copy 0 7 11) σ5 σ6 S := by
    have e := Stmt.exec_copy (k := 14) (r := 0) (r' := 7) (t := 11)
      (by decide) (by decide) (by decide) (σ := σ5) (by simp [σ5, costSt])
    apply (Stmt.exec_of_eq e ?_).mono
    · dsimp [σ5]
      rw [costSt_space]
      simp only [List.length_nil, List.length_cons, List.length_replicate, add_zero]
      simp [costSt]
      omega
    · funext j
      fin_cases j <;> simp [σ5, σ6, costSt]
  have e7 : Exec (Stmt.pushList 7 (List.replicate (c - m) true)) σ6 σ7 S := by
    have e := Stmt.exec_pushList (k := 14) 7 (List.replicate (c - m) true) σ6
    apply (Stmt.exec_of_eq e ?_).mono
    · dsimp [σ6]
      rw [costSt_space]
      simp only [List.length_nil, List.length_cons, List.length_replicate, add_zero]
      omega
    · funext j
      fin_cases j <;> simp [σ6, σ7, costSt]
  have hzero : c - m + x0.length = x0.length + c - m := by omega
  have htail : 2 * x0.length + c + 1 - (x0.length + c - m) - 1 = x0.length + m := by
    omega
  have e8 : Exec (Stmt.fillLoop 7 2 false) σ7
      (Stacks.layout 14 [x0, Stacks.encList cs,
        powBits (2 * x0.length + c + 1) (x0.length + c - m)]) S := by
    have e := Stmt.exec_fillLoop (k := 14) (K := 7) (R := 2) (by decide) false
      (List.replicate (c - m) true ++ x0) σ7 (by simp [σ7, costSt])
    apply (Stmt.exec_of_eq e ?_).mono
    · dsimp [σ7]
      rw [costSt_space]
      simp only [List.length_nil, List.length_cons, List.length_append, List.length_replicate,
        add_zero]
      omega
    · funext j
      fin_cases j <;> simp [σ7, costSt, Stacks.layout, powBits, hzero, htail]
  change Exec (Stmt.seqs [Stmt.moveAll 4 1, Stmt.copy 0 7 11,
    Stmt.pushList 7 (List.replicate m true), Stmt.fillLoop 7 2 false, .push 2 true,
    Stmt.copy 0 7 11, Stmt.pushList 7 (List.replicate (c - m) true),
    Stmt.fillLoop 7 2 false]) σ0 _ S
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ1, e1, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ2, e2, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ3, e3, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ4, e4, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ5, e5, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ6, e6, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ7, e7, ?_⟩
  rw [Stmt.exec_seqs_cons]
  refine ⟨_, e8, ?_⟩
  exact .skip e8.space_le.2

/-- This packages the already verified copy and cost loop with `exec_costProg_postlude`, at an
arbitrary space limit satisfying the loop's explicit bound.  Use `Stmt.exec_copy`, then
`exec_costLoop`; `length_costBits` identifies the encoded-list size needed to discharge the
postlude bound, and the three executions compose according to the definition of `costProg`. -/
theorem exec_costProg (T : Table) (tl : List BitString) (m c : ℕ) (LX : List BitString) (S : ℕ)
    (hm : m ≤ c)
    (hLX : ∀ z ∈ LX, 2 * z.length + 1 ≤ (Stacks.encList LX).length ∧
      tabVal T tl z ≤ (Stacks.encList LX).length + c)
    (hS : 2 * (Stacks.encList LX).length +
      LX.length * (4 * (Stacks.encList LX).length + 2 * c + 3) +
      8 * (Stacks.encList LX).length + 4 * c + tabSize T tl + 12 ≤ S) :
    let cs := LX.map fun z => costBits ((Stacks.encList LX).length + c)
      (2 * (Stacks.encList LX).length + c + 1) (tabVal T tl z) (z.length - 1)
    Exec (costProg T tl m c) (Stacks.layout 14 [Stacks.encList LX])
      (Stacks.layout 14 [Stacks.encList LX, Stacks.encList cs,
        powBits (2 * (Stacks.encList LX).length + c + 1)
          ((Stacks.encList LX).length + c - m)]) S := by
  let x0 := Stacks.encList LX
  let cs := LX.map fun z => costBits (x0.length + c)
    (2 * x0.length + c + 1) (tabVal T tl z) (z.length - 1)
  let σ0 := Stacks.layout 14 [x0]
  let σ1 := costSt x0 [] [] x0 [] [] [] [] [] []
  let σ2 := costSt x0 [] [] [] (Stacks.encList cs).reverse [] [] [] [] []
  have e1 : Exec (Stmt.copy 0 3 11) σ0 σ1 S := by
    have e := Stmt.exec_copy (k := 14) (r := 0) (r' := 3) (t := 11)
      (by decide) (by decide) (by decide) (σ := σ0) (by simp [σ0, Stacks.layout])
    apply (Stmt.exec_of_eq e ?_).mono
    · have hsp : σ0.space = x0.length := by
        dsimp [σ0]
        rw [Stacks.space_layout _ (by simp)]
        simp
      have hval : σ0 0 = x0 := by simp [σ0, Stacks.layout]
      rw [hsp, hval]
      dsimp [x0] at hS ⊢
      omega
    · funext j
      fin_cases j <;> simp [σ0, σ1, x0, costSt, Stacks.layout]
  have e2 : Exec (.loop 3 Option.isSome (costBody T tl c)) σ1 σ2 S := by
    have e := exec_costLoop T tl c x0 LX [] S
      (by simpa [x0] using hLX) (by dsimp [x0]; omega)
    exact Stmt.exec_of_eq e (by simp [σ2, cs])
  have hcs : (Stacks.encList cs).length =
      LX.length * (4 * x0.length + 2 * c + 3) := by
    rw [Stacks.length_encList]
    rw [show cs.map (fun z => 2 * z.length + 1) =
        LX.map (fun _ => 4 * x0.length + 2 * c + 3) by
      dsimp [cs]
      rw [List.map_map]
      apply List.map_congr_left
      intro z hz
      dsimp
      rw [length_costBits (x0.length + c) (2 * x0.length + c + 1)
        (tabVal T tl z) (z.length - 1) (by simpa [x0] using (hLX z hz).2) (by omega)]
      omega]
    simp
  have e3 := exec_costProg_postlude x0 cs m c S hm (by
    rw [hcs]
    dsimp [x0] at hS ⊢
    omega)
  change Exec (Stmt.seqs [Stmt.copy 0 3 11, .loop 3 Option.isSome (costBody T tl c),
    Stmt.moveAll 4 1, Stmt.copy 0 7 11, Stmt.pushList 7 (List.replicate m true),
    Stmt.fillLoop 7 2 false, .push 2 true, Stmt.copy 0 7 11,
    Stmt.pushList 7 (List.replicate (c - m) true), Stmt.fillLoop 7 2 false]) σ0 _ S
  rw [Stmt.exec_seqs_cons]
  refine ⟨σ1, e1, ?_⟩
  rw [Stmt.exec_seqs_cons]
  exact ⟨σ2, e2, e3⟩

/-- The explicit space bound required by `exec_costProg` is uniformly quadratic in the encoded
input length.  Bound `LX.length` by `Stacks.length_le_length_encList LX`, put
`q = |encList LX| + 1`, and distribute; every constant, linear, and quadratic term is absorbed
by `(6*c + tabSize T tl + 29) * q^2`. -/
theorem cost_space_bound (T : Table) (tl : List BitString) (c : ℕ) (LX : List BitString) :
    2 * (Stacks.encList LX).length +
        LX.length * (4 * (Stacks.encList LX).length + 2 * c + 3) +
        8 * (Stacks.encList LX).length + 4 * c + tabSize T tl + 12 ≤
      (6 * c + tabSize T tl + 29) * ((Stacks.encList LX).length + 1) ^ 2 := by
  have h1 : LX.length ≤ (Stacks.encList LX).length := Stacks.length_le_length_encList LX
  calc
    2 * (Stacks.encList LX).length +
        LX.length * (4 * (Stacks.encList LX).length + 2 * c + 3) +
        8 * (Stacks.encList LX).length + 4 * c + tabSize T tl + 12
      ≤ 2 * (Stacks.encList LX).length +
        (Stacks.encList LX).length * (4 * (Stacks.encList LX).length + 2 * c + 3) +
        8 * (Stacks.encList LX).length + 4 * c + tabSize T tl + 12 := by gcongr
    _ = 4 * (Stacks.encList LX).length^2 + 2 * c * (Stacks.encList LX).length +
        13 * (Stacks.encList LX).length + 4 * c + tabSize T tl + 12 := by ring
    _ ≤ 6 * c * (Stacks.encList LX).length^2 + 12 * c * (Stacks.encList LX).length + 6 * c +
        tabSize T tl * (Stacks.encList LX).length^2 + 2 * tabSize T tl *
        (Stacks.encList LX).length + tabSize T tl + 29 * (Stacks.encList LX).length^2 +
        58 * (Stacks.encList LX).length + 29 := by nlinarith
    _ = (6 * c + tabSize T tl + 29) * ((Stacks.encList LX).length + 1) ^ 2 := by ring

/-- A budget bit together with all cost blocks fits strictly below the common width chosen by
`costProg`.  First bound each `costNum` by `2^N` and the list length by the encoded input length;
then factor `2^W = 2^N * 2^(|encList LX|+1)` and use
`|LX| + 1 < 2^(|encList LX|+1)`. -/
theorem cost_overflow (T : Table) (m c : ℕ) (LX : List BitString) (hm : m ≤ c) :
    let x := (Stacks.encList LX).length
    let N := x + c
    let W := 2 * x + c + 1
    2 ^ (N - m) + (LX.map fun z => costNum N (T.fn z) z.length).sum < 2 ^ W := by
  intro x N W
  have h1 : (LX.map fun z => costNum N (T.fn z) z.length).sum ≤ LX.length * 2 ^ N := by
    calc
      _ ≤ (LX.map fun _ => 2 ^ N).sum := by
        apply List.sum_le_sum
        intro z _
        unfold costNum
        split_ifs
        · exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
        · exact Nat.zero_le _
      _ = LX.length * 2 ^ N := by
        simp
  have h2 : 2 ^ (N - m) + LX.length * 2 ^ N ≤ 2 ^ (N - m) + x * 2 ^ N := by
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    apply Stacks.length_le_length_encList
  have h3 : 2 ^ (N - m) + x * 2 ^ N < 2 ^ W := by
    calc
      2 ^ (N - m) + x * 2 ^ N ≤ 2 ^ N + x * 2 ^ N := by
        apply Nat.add_le_add_right
        apply Nat.pow_le_pow_right (by decide) (by omega)
      _ = (x + 1) * 2 ^ N := by ring
      _ < 2 ^ (x + 1) * 2 ^ N := by
        apply Nat.mul_lt_mul_of_pos_right
        · exact Nat.lt_two_pow_self
        · exact Nat.pos_of_ne_zero
            (by intro h; have : 2 = 0 := (Nat.pow_eq_zero.mp h).1; contradiction)
      _ = 2 ^ (x + 1 + N) := by rw [← pow_add]
      _ = 2 ^ W := by
        apply congrArg
        dsimp [x, N, W]
        omega
  calc
    2 ^ (N - m) + (LX.map fun z => costNum N (T.fn z) z.length).sum ≤
        2 ^ (N - m) + LX.length * 2 ^ N := Nat.add_le_add_left h1 _
    _ ≤ 2 ^ (N - m) + x * 2 ^ N := h2
    _ < 2 ^ W := h3

/-- **Costs and budget (remaining).**  For a hardwired table `T` and budget exponent `m` there is
a statement which, started on `[encList LX]` (stack `0`, all other stacks empty), adds on stacks
`1` and `2` the cost numerators `costNum N (T.fn z) |z|` of the strings of `LX` (same order, as
bit strings of a common width `W`) and the budget numerator `2 ^ (N - m)` (width `W`), for a
precision `N` bounding `|z| - 1`, `T.fn z` (`z ∈ LX`) and `m`, without overflow in width `W`,
within space `C · (|encList LX| + 1) ^ 2`.
Construction: `N = 2 |encList LX| + 6 + m + max T.value` and `W = N + |LX| + 1` in unary; `T.fn z`
by comparing `z` with the hardwired table (`Stmt.eqTest`) or as `2 |z| + 6`; the cost of `z` is
the bit string with ones exactly at the positions `N - T.fn z, …, N - |z|` (if `|z| - 1 ≤ T.fn z`),
the budget has a single one at position `N - m` (cf. `powBits`). -/
theorem exists_costStmt (T : Table) (m : ℕ) :
    ∃ (k : ℕ) (s : Stmt k) (C : ℕ), 4 ≤ k ∧ ∀ LX : List BitString,
      ∃ (cs : List BitString) (eb : BitString) (N W : ℕ),
        (∀ z ∈ LX, z.length - 1 ≤ N ∧ T.fn z ≤ N) ∧ m ≤ N ∧
        cs.length = LX.length ∧ (∀ b ∈ cs, b.length = W) ∧ eb.length = W ∧
        (∀ i < LX.length, binVal (cs.getD i []) =
          costNum N (T.fn (LX.getD i [])) (LX.getD i []).length) ∧
        binVal eb = 2 ^ (N - m) ∧
        binVal eb + (LX.map fun z => costNum N (T.fn z) z.length).sum < 2 ^ W ∧
        Exec s (Stacks.layout k [Stacks.encList LX])
          (Stacks.layout k [Stacks.encList LX, Stacks.encList cs, eb])
          (C * ((Stacks.encList LX).length + 1) ^ 2) := by
  let tl := T.dom.toList
  let c := 6 + m + T.dom.sup T.value
  let C := 6 * c + tabSize T tl + 29
  refine ⟨14, costProg T tl m c, C, by omega, ?_⟩
  intro LX
  let x := (Stacks.encList LX).length
  let N := x + c
  let W := 2 * x + c + 1
  let cs := LX.map fun z => costBits N W (T.fn z) (z.length - 1)
  let eb := powBits W (N - m)
  have hb := cost_input_bounds T m LX
  dsimp only at hb
  have htab : ∀ z, tabVal T tl z = T.fn z := by
    intro z
    exact tabVal_toList T z
  have hm : m ≤ c := by dsimp [c]; omega
  have hNW : N < W := by simp [N, W]; omega
  refine ⟨cs, eb, N, W, hb.2.1, hb.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [cs]
  · intro b hbcs
    simp only [cs, List.mem_map] at hbcs
    obtain ⟨z, hz, rfl⟩ := hbcs
    exact length_costBits N W (T.fn z) (z.length - 1) (hb.2.1 z hz).2 (by omega)
  · exact length_powBits W (N - m) (by omega)
  · intro i hi
    simp only [cs]
    rw [List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
    rw [binVal_costBits N W (T.fn LX[i]) (LX[i].length - 1)
      ((hb.2.1 LX[i] (List.getElem_mem _)).2) hNW]
    rfl
  · exact binVal_powBits W (N - m)
  · simpa [eb, binVal_powBits] using cost_overflow T m c LX hm
  · have he := exec_costProg T tl m c LX
      (C * ((Stacks.encList LX).length + 1) ^ 2) hm
      (fun z hz => by simpa [tl, htab z] using hb.1 z hz)
      (cost_space_bound T tl c LX)
    simpa [cs, eb, N, W, x, htab] using he

end Kolmogorov.RandomStrings
