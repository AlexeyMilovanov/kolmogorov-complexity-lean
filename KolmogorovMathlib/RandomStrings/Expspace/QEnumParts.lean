/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.RecSim

/-!
# The sub-contracts of the query enumeration

The building blocks of the enumeration of the query set (`QEnum`): the selection `sel` of a
sublist by a mask, the zero mask, copying the code of the first string of a coded list,
selection, pushing the code of a string, the merge `mergeL`, and the recording simulation
contract `QEnum.exists_recSimStmt`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace QEnum

/-- The strings of `Us` at the positions of the `true` bits of the mask `v`. -/
def sel : BitString → List BitString → List BitString
  | b :: v, z :: Us => if b then z :: sel v Us else sel v Us
  | _, _ => []

/-- Merge the strings of `Q` (in order) into `Ln` (each new string on top), skipping those in `Lo`
or already in the accumulated list. -/
def mergeL (Lo : List BitString) : List BitString → List BitString → List BitString
  | [], Ln => Ln
  | z :: Q, Ln => mergeL Lo Q (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)

/-- The empty mask selects nothing: `sel [] Us` is the empty list for every list `Us`. -/
theorem sel_nil_left (Us : List BitString) : sel [] Us = [] := by
  cases Us <;> rfl

/-- Nothing can be selected from the empty list, whatever the mask `v`. -/
theorem sel_nil_right (v : BitString) : sel v [] = [] := by
  cases v <;> rfl

/-- The code of the list `z :: L` is the code `Stacks.encStr z` of its first string followed by
the code of the rest `L`. -/
theorem encList_cons (z : BitString) (L : List BitString) :
    Stacks.encList (z :: L) = Stacks.encStr z ++ Stacks.encList L := by
  simp [Stacks.encList]

/-- The code of the empty list of strings is the empty bit string. -/
theorem encList_nil : Stacks.encList [] = [] := rfl

/-! #### The zero mask -/

/-- Move the top bit `b` of `t` onto `r` and push `false` on `r'`. -/
def zeroStep {k : ℕ} (t r r' : Fin k) : Stmt k :=
  Stmt.caseBit t fun b => Stmt.seqs [.pop t, .push r b, .push r' false]

/-- One step of the zero mask: for pairwise distinct stacks `t`, `r`, `r'` with `b :: l` on `t`,
`zeroStep t r r'` pops `b` from `t`, pushes it on `r` and pushes `false` on `r'`, within the
initial space plus one. -/
theorem exec_zeroStep {k : ℕ} {t r r' : Fin k} (htr : t ≠ r) (htr' : t ≠ r') (hrr : r ≠ r')
    {σ : Stacks k} {b : Bool} {l : BitString} (ht : σ t = b :: l) :
    Exec (zeroStep t r r') σ
      (Function.update (Function.update (Function.update σ t l) r (b :: σ r)) r'
        (false :: σ r')) (σ.space + 1) := by
  rw [zeroStep, Stmt.exec_caseBit ht]
  have s1 := Stmt.space_update_of_cons ht
  have e1 := Stmt.exec_pop_cons ht (S := σ.space + 1) (by omega)
  have e2 := Exec.push (r := r) (b := b) (σ := Function.update σ t l) (S := σ.space + 1)
    (by omega)
  rw [Function.update_of_ne htr.symm] at e2
  have s2 := Stacks.space_update_cons (Function.update σ t l) r b
  rw [Function.update_of_ne htr.symm] at s2
  have e3 := Exec.push (r := r') (b := false)
    (σ := Function.update (Function.update σ t l) r (b :: σ r)) (S := σ.space + 1) (by omega)
  rw [Function.update_of_ne hrr.symm, Function.update_of_ne htr'.symm] at e3
  exact .seq e1 (.seq e2 (.seq e3 (.skip e3.space_le.2)))

/-- The loop of the zero mask: for pairwise distinct stacks `t`, `r`, `r'` with `l` on `t`,
running `zeroStep t r r'` while `t` is nonempty empties `t`, pushes `l` reversed on `r` and
`|l|` copies of `false` on `r'`, within the initial space plus `|l|`.  The distinctness
hypotheses default to a proof by `decide`, which settles them for numeric stack indices. -/
theorem exec_zeroLoop {k : ℕ} {t r r' : Fin k} (l : BitString) (σ : Stacks k) (ht : σ t = l)
    (htr : t ≠ r := by decide) (htr' : t ≠ r' := by decide) (hrr : r ≠ r' := by decide) :
    Exec (.loop t Option.isSome (zeroStep t r r')) σ
      (Function.update (Function.update (Function.update σ t []) r (l.reverse ++ σ r)) r'
        (List.replicate l.length false ++ σ r')) (σ.space + l.length) := by
  replace htr : t ≠ r := htr
  replace htr' : t ≠ r' := htr'
  replace hrr : r ≠ r' := hrr
  induction l generalizing σ with
  | nil =>
    refine Stmt.exec_of_eq (.loopF (by simp [ht]) (by simp)) ?_
    funext j
    simp only [Function.update_apply, List.reverse_nil, List.nil_append, List.length_nil,
      List.replicate_zero]
    split_ifs <;> subst_vars <;> simp_all
  | cons b l ih =>
    have h1 := exec_zeroStep htr htr' hrr ht
    have h2 := ih
      (Function.update (Function.update (Function.update σ t l) r (b :: σ r)) r' (false :: σ r'))
      (by simp [htr, htr'])
    have sp := h1.space_le.2
    refine .loopT (by simp [ht]) (h1.mono (by simp only [List.length_cons]; omega))
      (Stmt.exec_of_eq (h2.mono (by simp only [List.length_cons]; omega)) ?_)
    funext j
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons, List.replicate_succ']
    split_ifs <;> subst_vars <;> simp_all

/-- The zero mask: `1 := replicate |l| false` from `0 = l` (restored), through `2`. -/
def zeroStmt : Stmt 3 := .seq (Stmt.moveAll 0 2) (.loop 2 Option.isSome (zeroStep 2 0 1))

/-- **The zero mask.**  There are a statement `s` on three stacks and a constant `K` such that,
from `l` on stack `0` and the other stacks empty, `s` leaves `l` on stack `0` and puts
`replicate |l| false` on stack `1`, within space `K * (|l| + 1)`. -/
theorem exists_zeroStmt : ∃ (s : Stmt 3) (K : ℕ), ∀ l : BitString,
    Exec s (Function.update (fun _ => []) 0 l)
      (Function.update (Function.update (fun _ => []) 0 l) 1 (List.replicate l.length false))
      (K * (l.length + 1)) := by
  refine ⟨zeroStmt, 2, fun l => ?_⟩
  have e1 := Stmt.exec_moveAll (by decide : (0 : Fin 3) ≠ 2) l
    (Function.update (fun _ => []) 0 l) (by simp)
  have e2 := exec_zeroLoop (t := (2 : Fin 3)) (r := 0) (r' := 1) l.reverse
    (Function.update (Function.update (Function.update (fun _ => []) 0 l) 0 [])
      2 (l.reverse ++ (Function.update (fun (_ : Fin 3) => ([] : BitString)) 0 l) 2)) (by simp)
  have sp0 : Stacks.space (Function.update (fun (_ : Fin 3) => ([] : BitString)) 0 l) =
      l.length := by
    simp [Stacks.space, Fin.sum_univ_succ, Function.update_apply]
  have sp1 := e1.space_le.2
  rw [sp0] at e1 sp1
  refine Stmt.exec_of_eq (.seq (e1.mono (by nlinarith)) (e2.mono (by
    simp only [List.length_reverse]; nlinarith))) ?_
  funext j
  fin_cases j <;> simp

/-! #### Copying the code of the first string of a coded list -/

/-- Move the code of the first string on `t` onto both `r` and `r'` (reversed), bit by bit. -/
def codeDup {k : ℕ} (t r r' : Fin k) : Stmt k :=
  .seq (.loop t Stmt.isTrue (.seq (Stmt.dupStep t r r') (Stmt.dupStep t r r')))
    (Stmt.dupStep t r r')

/-- The loop of `codeDup`: for pairwise distinct stacks `t`, `r`, `r'` with the bit pairs
`true, b` of `z` followed by `false :: rest` on `t`, running two `dupStep`s while `t` starts with
`true` moves these bit pairs off `t`, reversed, onto both `r` and `r'` and leaves `false :: rest`
on `t`, within the initial space plus `2 |z|`. -/
theorem exec_codeDupLoop {k : ℕ} {t r r' : Fin k} (htr : t ≠ r) (htr' : t ≠ r') (hrr : r ≠ r') :
    ∀ (z rest : BitString) (σ : Stacks k), σ t = z.flatMap (fun b => [true, b]) ++ false :: rest →
      Exec (.loop t Stmt.isTrue (.seq (Stmt.dupStep t r r') (Stmt.dupStep t r r'))) σ
        (Function.update (Function.update (Function.update σ t (false :: rest)) r
          ((z.flatMap (fun b => [true, b])).reverse ++ σ r)) r'
          ((z.flatMap (fun b => [true, b])).reverse ++ σ r'))
        (σ.space + 2 * z.length)
  | [], rest, σ, hσ => by
    simp only [List.flatMap_nil, List.nil_append] at hσ
    refine Stmt.exec_of_eq (.loopF (by simp [hσ, Stmt.isTrue]) (by omega)) ?_
    funext j
    simp only [Function.update_apply, List.flatMap_nil, List.reverse_nil, List.nil_append]
    split_ifs <;> subst_vars <;> simp_all
  | b :: z, rest, σ, hσ => by
    have hσ' : σ t = true :: b :: (z.flatMap (fun b => [true, b]) ++ false :: rest) := by
      rw [hσ]; simp
    have e1 := Stmt.exec_dupStep htr htr' hrr hσ'
    have h1t : (Function.update (Function.update (Function.update σ t
        (b :: (z.flatMap (fun b => [true, b]) ++ false :: rest))) r (true :: σ r)) r'
        (true :: σ r')) t = b :: (z.flatMap (fun b => [true, b]) ++ false :: rest) := by
      rw [Function.update_of_ne htr', Function.update_of_ne htr, Function.update_self]
    have e2 := Stmt.exec_dupStep htr htr' hrr h1t
    have h2t : (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update σ t
        (b :: (z.flatMap (fun b => [true, b]) ++ false :: rest))) r (true :: σ r)) r'
        (true :: σ r')) t (z.flatMap (fun b => [true, b]) ++ false :: rest)) r
        (b :: (Function.update (Function.update (Function.update σ t
        (b :: (z.flatMap (fun b => [true, b]) ++ false :: rest))) r (true :: σ r)) r'
        (true :: σ r')) r)) r'
        (b :: (Function.update (Function.update (Function.update σ t
        (b :: (z.flatMap (fun b => [true, b]) ++ false :: rest))) r (true :: σ r)) r'
        (true :: σ r')) r')) t = z.flatMap (fun b => [true, b]) ++ false :: rest := by
      rw [Function.update_of_ne htr', Function.update_of_ne htr, Function.update_self]
    have ih := exec_codeDupLoop htr htr' hrr z rest _ h2t
    have sp1 := e1.space_le.2
    have sp2 := e2.space_le.2
    have b1 : σ.space + 1 ≤ σ.space + 2 * (b :: z).length := by
      simp only [List.length_cons]; omega
    have hb := e1.mono b1
    have he2 := e2.mono (S' := σ.space + 2 * (b :: z).length)
      (by simp only [List.length_cons]; omega)
    have hih := ih.mono (S' := σ.space + 2 * (b :: z).length)
      (by simp only [List.length_cons]; omega)
    refine .loopT (by simp [hσ', Stmt.isTrue]) (.seq hb he2) (Stmt.exec_of_eq hih ?_)
    funext j
    simp only [Function.update_apply, List.reverse_cons, List.flatMap_cons,
      List.reverse_append, List.append_assoc, List.singleton_append]
    split_ifs <;> subst_vars <;> simp_all

/-- **Duplicating a code.**  For pairwise distinct stacks `t`, `r`, `r'` with `encStr z ++ rest`
on `t`, `codeDup t r r'` leaves `rest` on `t` and pushes the reversed code `(encStr z).reverse`
on both `r` and `r'`, within the initial space plus `2 |z| + 1`.  The distinctness hypotheses
default to a proof by `decide`, which settles them for numeric stack indices. -/
theorem exec_codeDup {k : ℕ} {t r r' : Fin k} {z rest : BitString} {σ : Stacks k}
    (hσ : σ t = Stacks.encStr z ++ rest) (htr : t ≠ r := by decide)
    (htr' : t ≠ r' := by decide) (hrr : r ≠ r' := by decide) :
    Exec (codeDup t r r') σ
      (Function.update (Function.update (Function.update σ t rest) r
        ((Stacks.encStr z).reverse ++ σ r)) r' ((Stacks.encStr z).reverse ++ σ r'))
      (σ.space + 2 * z.length + 1) := by
  replace htr : t ≠ r := htr
  replace htr' : t ≠ r' := htr'
  replace hrr : r ≠ r' := hrr
  have hσ' : σ t = z.flatMap (fun b => [true, b]) ++ false :: rest := by
    rw [hσ, Stacks.encStr]; simp
  have e1 := exec_codeDupLoop htr htr' hrr z rest σ hσ'
  have hL : (Function.update (Function.update (Function.update σ t (false :: rest)) r
      ((z.flatMap (fun b => [true, b])).reverse ++ σ r)) r'
      ((z.flatMap (fun b => [true, b])).reverse ++ σ r')) t = false :: rest := by
    rw [Function.update_of_ne htr', Function.update_of_ne htr, Function.update_self]
  have e2 := Stmt.exec_dupStep htr htr' hrr hL
  have sp1 := e1.space_le.2
  refine Stmt.exec_of_eq (.seq (e1.mono (by omega)) (e2.mono (by omega))) ?_
  funext j
  simp only [Function.update_apply, Stacks.encStr, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append]
  split_ifs <;> subst_vars <;> simp_all

/-! #### Selection -/

/-- One step of the selection: if the mask on `1` is not exhausted, move its next bit `b` to `4`
and copy the code of the first string of `0` onto `3` and onto the accumulator `6` (if `b`) or
onto the trash `7` (cleared); if the mask is exhausted, move the rest of `0` onto `3`. -/
def selBody : Stmt 12 :=
  .ite 1 Option.isSome
    (Stmt.caseBit 1 fun b => .seq (Stmt.moveBit 1 4)
      (if b then codeDup 0 3 6 else .seq (codeDup 0 3 7) (Stmt.clear 7)))
    (Stmt.moveAll 0 3)

/-- The code of `z :: Us` has length `2 |z| + 1` plus the length of the code of `Us`. -/
theorem length_encList_cons (z : BitString) (Us : List BitString) :
    (Stacks.encList (z :: Us)).length = 2 * z.length + 1 + (Stacks.encList Us).length := by
  rw [encList_cons, List.length_append, Stacks.length_encStr]

/-- The selection loop: with the code of `Us` on stack `0`, the mask `v` on stack `1` and stack
`7` empty, running `selBody` while `0` is nonempty empties `0` onto `3`, moves the first `|Us|`
mask bits from `1` onto `4` and pushes the reversed code of `sel v Us` on `6`, within the
initial space plus twice the length of the code of `Us`. -/
theorem exec_selLoop : ∀ (Us : List BitString) (v : BitString) (σ : Stacks 12),
    σ 0 = Stacks.encList Us → σ 1 = v → σ 7 = [] →
    Exec (.loop 0 Option.isSome selBody) σ
      (Function.update (Function.update (Function.update (Function.update
        (Function.update σ 0 []) 3 ((Stacks.encList Us).reverse ++ σ 3)) 1 (v.drop Us.length)) 4
        ((v.take Us.length).reverse ++ σ 4)) 6 ((Stacks.encList (sel v Us)).reverse ++ σ 6))
      (σ.space + 2 * (Stacks.encList Us).length)
  | [], v, σ, h0, h1, h7 => by
    refine Stmt.exec_of_eq (.loopF (by simp [h0, encList_nil]) (by omega)) ?_
    funext j
    simp only [Function.update_apply, encList_nil, List.reverse_nil, List.nil_append,
      List.length_nil, List.drop_zero, List.take_zero, sel_nil_right]
    split_ifs <;> subst_vars <;> simp_all [encList_nil]
  | z :: Us, [], σ, h0, h1, h7 => by
    have hz : σ 0 = Stacks.encStr z ++ Stacks.encList Us := by rw [h0, encList_cons]
    have hne : Option.isSome (σ 0).head? = true := by
      rw [hz]; simp [Stacks.encStr]
    have e1 := Stmt.exec_moveAll (by decide : (0 : Fin 12) ≠ 3) (σ 0) σ rfl
    have e2 : Exec (.loop 0 Option.isSome selBody)
        (Function.update (Function.update σ 0 []) 3 ((σ 0).reverse ++ σ 3))
        (Function.update (Function.update σ 0 []) 3 ((σ 0).reverse ++ σ 3)) σ.space :=
      .loopF (by simp) e1.space_le.2
    refine .loopT hne (.iteF (by simp [h1]) (e1.mono (by omega)))
      (Stmt.exec_of_eq (e2.mono (by omega)) ?_)
    funext j
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [sel_nil_left, encList_cons, encList_nil]
  | z :: Us, b :: v, σ, h0, h1, h7 => by
    have hz : σ 0 = Stacks.encStr z ++ Stacks.encList Us := by rw [h0, encList_cons]
    have hne : Option.isSome (σ 0).head? = true := by
      rw [hz]; simp [Stacks.encStr]
    have hlen := length_encList_cons z Us
    have e1 := Stmt.exec_moveBit (by decide : (1 : Fin 12) ≠ 4) h1
    have sp1 := e1.space_le.2
    have ha0 : (Function.update (Function.update σ 1 v) 4 (b :: σ 4)) 0 =
        Stacks.encStr z ++ Stacks.encList Us := by simp [hz]
    cases b with
    | false =>
      have e2 := exec_codeDup (t := 0) (r := 3) (r' := 7) ha0
      have sp2 := e2.space_le.2
      have e3 := Stmt.exec_clear 7 _ (Function.update (Function.update
        (Function.update (Function.update (Function.update σ 1 v) 4 (false :: σ 4)) 0
          (Stacks.encList Us)) 3 ((Stacks.encStr z).reverse ++
            (Function.update (Function.update σ 1 v) 4 (false :: σ 4)) 3)) 7
        ((Stacks.encStr z).reverse ++ (Function.update (Function.update σ 1 v) 4
          (false :: σ 4)) 7)) rfl
      have sp3 := e3.space_le.2
      have ih := exec_selLoop Us v (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update σ 1 v) 4 (false :: σ 4)) 0
            (Stacks.encList Us)) 3 ((Stacks.encStr z).reverse ++
              (Function.update (Function.update σ 1 v) 4 (false :: σ 4)) 3)) 7
          ((Stacks.encStr z).reverse ++ (Function.update (Function.update σ 1 v) 4
            (false :: σ 4)) 7)) 7 []) (by simp) (by simp) (by simp)
      have spi := ih.space_le.2
      have hbody : Exec selBody σ (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update σ 1 v) 4 (false :: σ 4)) 0
            (Stacks.encList Us)) 3 ((Stacks.encStr z).reverse ++
              (Function.update (Function.update σ 1 v) 4 (false :: σ 4)) 3)) 7
          ((Stacks.encStr z).reverse ++ (Function.update (Function.update σ 1 v) 4
            (false :: σ 4)) 7)) 7 [])
          (σ.space + 2 * (Stacks.encList (z :: Us)).length) := by
        refine .iteT (by simp [h1]) ?_
        rw [Stmt.exec_caseBit h1]
        exact .seq (e1.mono (by omega)) (.seq (e2.mono (by omega)) (e3.mono (by omega)))
      refine .loopT hne hbody (Stmt.exec_of_eq (ih.mono (by omega)) ?_)
      clear e1 e2 e3 ih hbody sp1 sp2 sp3 spi hne ha0 hlen h0 h1 hz
      funext j
      fin_cases j <;> simp [sel, encList_cons, h7]
    | true =>
      have e2 := exec_codeDup (t := 0) (r := 3) (r' := 6) ha0
      have sp2 := e2.space_le.2
      have ih := exec_selLoop Us v (Function.update (Function.update (Function.update
          (Function.update (Function.update σ 1 v) 4 (true :: σ 4)) 0
            (Stacks.encList Us)) 3 ((Stacks.encStr z).reverse ++
              (Function.update (Function.update σ 1 v) 4 (true :: σ 4)) 3)) 6
          ((Stacks.encStr z).reverse ++ (Function.update (Function.update σ 1 v) 4
            (true :: σ 4)) 6)) (by simp) (by simp) (by simp [h7])
      have spi := ih.space_le.2
      have hbody : Exec selBody σ (Function.update (Function.update (Function.update
          (Function.update (Function.update σ 1 v) 4 (true :: σ 4)) 0
            (Stacks.encList Us)) 3 ((Stacks.encStr z).reverse ++
              (Function.update (Function.update σ 1 v) 4 (true :: σ 4)) 3)) 6
          ((Stacks.encStr z).reverse ++ (Function.update (Function.update σ 1 v) 4
            (true :: σ 4)) 6))
          (σ.space + 2 * (Stacks.encList (z :: Us)).length) := by
        refine .iteT (by simp [h1]) ?_
        rw [Stmt.exec_caseBit h1]
        exact .seq (e1.mono (by omega)) (e2.mono (by omega))
      refine .loopT hne hbody (Stmt.exec_of_eq (ih.mono (by omega)) ?_)
      clear e1 e2 ih hbody sp1 sp2 spi hne ha0 hlen h0 h1 hz h7
      funext j
      fin_cases j <;> simp [sel, encList_cons]

/-- Selection: `2 := encList (sel v Us)` from `0 = encList Us` and `1 = v` (both restored), through
the work stacks `3`, `4`, `6`, `7`. -/
def selStmt : Stmt 12 :=
  Stmt.seqs [.loop 0 Option.isSome selBody, Stmt.moveAll 3 0, Stmt.moveAll 4 1, Stmt.moveAll 6 2]

/-- **Selection.**  There are a statement `s` on twelve stacks and a constant `K` such that, from
the code of `Us` on stack `0`, the mask `v` on stack `1` and the other stacks empty, `s` leaves
the code of `sel v Us` on stack `2` and restores stacks `0` and `1`, within space
`K * (|encList Us| + |v| + 1)`. -/
theorem exists_selStmt : ∃ (s : Stmt 12) (K : ℕ), ∀ (Us : List BitString) (v : BitString),
    Exec s (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v)
      (Function.update (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v)
        2 (Stacks.encList (sel v Us)))
      (K * ((Stacks.encList Us).length + v.length + 1)) := by
  refine ⟨selStmt, 3, fun Us v => ?_⟩
  set σ0 : Stacks 12 := Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v
    with hσ0
  have sp0 : σ0.space = (Stacks.encList Us).length + v.length := by
    simp [σ0, Stacks.space, Fin.sum_univ_succ, Function.update_apply]
  have e1 := exec_selLoop Us v σ0 (by simp [σ0]) (by simp [σ0]) (by simp [σ0])
  set σ1 : Stacks 12 := Function.update (Function.update (Function.update (Function.update
    (fun _ => []) 1 (v.drop Us.length)) 3 (Stacks.encList Us).reverse) 4
    (v.take Us.length).reverse) 6 (Stacks.encList (sel v Us)).reverse with hσ1
  have e1' := Stmt.exec_of_eq e1 (σ₂ := σ1) (by funext j; fin_cases j <;> simp [σ0, σ1])
  have sp1 := e1'.space_le.2
  have e2 := Stmt.exec_moveAll (r := (3 : Fin 12)) (r' := 0) (by decide) (σ1 3) σ1 rfl
  have sp2 := e2.space_le.2
  have e3 := Stmt.exec_moveAll (r := (4 : Fin 12)) (r' := 1) (by decide) _
    (Function.update (Function.update σ1 3 []) 0 ((σ1 3).reverse ++ σ1 0)) rfl
  have sp3 := e3.space_le.2
  have e4 := Stmt.exec_moveAll (r := (6 : Fin 12)) (r' := 2) (by decide) _
    (Function.update (Function.update (Function.update (Function.update σ1 3 []) 0
      ((σ1 3).reverse ++ σ1 0)) 4 []) 1
      (((Function.update (Function.update σ1 3 []) 0 ((σ1 3).reverse ++ σ1 0)) 4).reverse ++
        (Function.update (Function.update σ1 3 []) 0 ((σ1 3).reverse ++ σ1 0)) 1)) rfl
  have sp4 := e4.space_le.2
  have hb : σ0.space + 2 * (Stacks.encList Us).length ≤
      3 * ((Stacks.encList Us).length + v.length + 1) := by omega
  refine Stmt.exec_of_eq (.seq (e1'.mono hb) (.seq (e2.mono (sp1.trans hb))
    (.seq (e3.mono (sp2.trans (sp1.trans hb))) (.seq (e4.mono (sp3.trans (sp2.trans
      (sp1.trans hb)))) (.skip (sp4.trans (sp3.trans (sp2.trans (sp1.trans hb))))))))) ?_
  clear e1 e1' e2 e3 e4 sp1 sp2 sp3 sp4 hb sp0
  rw [hσ1, hσ0]
  funext j
  fin_cases j <;> simp

/-! #### Pushing the code of a string -/

section PushCode

variable {k : ℕ}

/-- One step of `pushCode`: pop the top bit `b` of `t`, push it back on `Z`, and push `b` then
`true` on `D`. -/
def pushCodeBody (Z t D : Fin k) : Stmt k :=
  Stmt.caseBit t fun b => Stmt.seqs [.pop t, .push Z b, .push D b, .push D true]

/-- Push the code `encStr z` of the string `z` held on `Z` (first bit on top) on top of `D`,
restoring `Z`, through the empty work stack `t`. -/
def pushCode (Z t D : Fin k) : Stmt k :=
  Stmt.seqs [Stmt.moveAll Z t, .push D false, .loop t Option.isSome (pushCodeBody Z t D)]

/-- One step of `pushCode`: for pairwise distinct stacks `Z`, `t`, `D` with `b :: l` on `t`,
`pushCodeBody Z t D` pops `b` from `t`, pushes it back on `Z`, and pushes `b` and then `true` on
`D`, within the initial space plus two. -/
theorem exec_pushCodeBody {Z t D : Fin k} (hZt : Z ≠ t) (hZD : Z ≠ D) (htD : t ≠ D)
    {σ : Stacks k} {b : Bool} {l : BitString} (ht : σ t = b :: l) :
    Exec (pushCodeBody Z t D) σ
      (Function.update (Function.update (Function.update σ t l) Z (b :: σ Z)) D
        (true :: b :: σ D)) (σ.space + 2) := by
  rw [pushCodeBody, Stmt.exec_caseBit ht]
  have s1 := Stmt.space_update_of_cons ht
  have e1 := Stmt.exec_pop_cons ht (S := σ.space + 2) (by omega)
  have e2 := Exec.push (r := Z) (b := b) (σ := Function.update σ t l) (S := σ.space + 2)
    (by omega)
  rw [Function.update_of_ne hZt] at e2
  have s2 := Stacks.space_update_cons (Function.update σ t l) Z b
  rw [Function.update_of_ne hZt] at s2
  have e3 := Exec.push (r := D) (b := b)
    (σ := Function.update (Function.update σ t l) Z (b :: σ Z)) (S := σ.space + 2) (by omega)
  rw [Function.update_of_ne hZD.symm, Function.update_of_ne htD.symm] at e3
  have s3 := Stacks.space_update_cons (Function.update (Function.update σ t l) Z (b :: σ Z)) D b
  rw [Function.update_of_ne hZD.symm, Function.update_of_ne htD.symm] at s3
  have e4 := Exec.push (r := D) (b := true)
    (σ := Function.update (Function.update (Function.update σ t l) Z (b :: σ Z)) D (b :: σ D))
    (S := σ.space + 2) (by omega)
  rw [Function.update_self, Function.update_idem] at e4
  exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.skip e4.space_le.2))))

/-- The loop of `pushCode`: for pairwise distinct stacks `Z`, `t`, `D` with `l` on `t`, running
`pushCodeBody Z t D` while `t` is nonempty empties `t`, pushes `l` reversed on `Z` and
`l.reverse.flatMap (fun b => [true, b])` on `D`, within the initial space plus `2 |l|`. -/
theorem exec_pushCodeLoop {Z t D : Fin k} (hZt : Z ≠ t) (hZD : Z ≠ D) (htD : t ≠ D) :
    ∀ (l : BitString) (σ : Stacks k), σ t = l →
      Exec (.loop t Option.isSome (pushCodeBody Z t D)) σ
        (Function.update (Function.update (Function.update σ t []) Z (l.reverse ++ σ Z)) D
          (l.reverse.flatMap (fun b => [true, b]) ++ σ D)) (σ.space + 2 * l.length)
  | [], σ, ht => by
    refine Stmt.exec_of_eq (.loopF (by simp [ht]) (by omega)) ?_
    funext j
    simp only [Function.update_apply, List.reverse_nil, List.nil_append, List.flatMap_nil]
    split_ifs <;> subst_vars <;> simp_all
  | b :: l, σ, ht => by
    have h1 := exec_pushCodeBody hZt hZD htD ht
    have h2 := exec_pushCodeLoop hZt hZD htD l
      (Function.update (Function.update (Function.update σ t l) Z (b :: σ Z)) D
        (true :: b :: σ D))
      (by rw [Function.update_of_ne htD, Function.update_of_ne hZt.symm, Function.update_self])
    have sp : Stacks.space (Function.update (Function.update (Function.update σ t l) Z
        (b :: σ Z)) D (true :: b :: σ D)) = σ.space + 2 := by
      have s1 := Stmt.space_update_of_cons ht
      have s2 := Stacks.space_update_cons (Function.update σ t l) Z b
      rw [Function.update_of_ne hZt] at s2
      have s3 := Stacks.space_update (Function.update (Function.update σ t l) Z (b :: σ Z)) D
        (true :: b :: σ D)
      rw [Function.update_of_ne hZD.symm, Function.update_of_ne htD.symm] at s3
      simp only [List.length_cons] at s3
      omega
    rw [sp] at h2
    refine .loopT (by simp [ht]) (h1.mono (by simp only [List.length_cons]; omega))
      (Stmt.exec_of_eq (h2.mono (by simp only [List.length_cons]; omega)) ?_)
    funext j
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
    split_ifs <;> subst_vars <;> simp_all

/-- **Pushing a code.**  With `Z, t, D` distinct and `t` empty, `pushCode Z t D` pushes the code
`encStr (σ Z)` on top of `D` and restores `Z`, within the initial space `+ 2 |σ Z| + 1`. -/
theorem exec_pushCode {Z t D : Fin k} (hZt : Z ≠ t) (hZD : Z ≠ D) (htD : t ≠ D)
    {σ : Stacks k} (ht : σ t = []) :
    Exec (pushCode Z t D) σ (Function.update σ D (Stacks.encStr (σ Z) ++ σ D))
      (σ.space + 2 * (σ Z).length + 1) := by
  have e1 := Stmt.exec_moveAll hZt (σ Z) σ rfl
  rw [ht, List.append_nil] at e1
  have s1a := Stacks.space_update σ Z []
  have s1b := Stacks.space_update (Function.update σ Z []) t (σ Z).reverse
  rw [Function.update_of_ne hZt.symm, ht] at s1b
  simp only [List.length_nil, List.length_reverse] at s1a s1b
  have hD1 : (Function.update (Function.update σ Z []) t (σ Z).reverse) D = σ D := by
    rw [Function.update_of_ne htD.symm, Function.update_of_ne hZD.symm]
  have e2 := Exec.push (r := D) (b := false)
    (σ := Function.update (Function.update σ Z []) t (σ Z).reverse)
    (S := σ.space + 2 * (σ Z).length + 1) (by omega)
  rw [hD1] at e2
  have s2 := Stacks.space_update_cons (Function.update (Function.update σ Z []) t (σ Z).reverse)
    D false
  rw [hD1] at s2
  have ht2 : (Function.update (Function.update (Function.update σ Z []) t (σ Z).reverse) D
      (false :: σ D)) t = (σ Z).reverse := by
    rw [Function.update_of_ne htD, Function.update_self]
  have e3 := exec_pushCodeLoop hZt hZD htD _ _ ht2
  rw [s2, List.length_reverse] at e3
  have hfin : Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update σ Z []) t (σ Z).reverse) D (false :: σ D)) t []) Z
        ((σ Z).reverse.reverse ++ (Function.update (Function.update (Function.update σ Z []) t
          (σ Z).reverse) D (false :: σ D)) Z)) D
        ((σ Z).reverse.reverse.flatMap (fun b => [true, b]) ++ (Function.update
          (Function.update (Function.update σ Z []) t (σ Z).reverse) D (false :: σ D)) D) =
      Function.update σ D (Stacks.encStr (σ Z) ++ σ D) := by
    funext j
    by_cases hjD : j = D
    · subst hjD
      simp only [Function.update_self, List.reverse_reverse, Stacks.encStr, List.append_assoc,
        List.singleton_append]
    · rw [Function.update_of_ne hjD, Function.update_of_ne hjD]
      by_cases hjZ : j = Z
      · subst hjZ
        rw [Function.update_self, List.reverse_reverse, Function.update_of_ne hZD,
          Function.update_of_ne hZt, Function.update_self, List.append_nil]
      · rw [Function.update_of_ne hjZ]
        by_cases hjt : j = t
        · subst hjt; rw [Function.update_self, ht]
        · rw [Function.update_of_ne hjt, Function.update_of_ne hjD, Function.update_of_ne hjt,
            Function.update_of_ne hjZ]
  have e3' := Stmt.exec_of_eq (e3.mono (S' := σ.space + 2 * (σ Z).length + 1) (by omega)) hfin
  exact .seq (e1.mono (by omega)) (.seq e2 (.seq e3' (.skip e3'.space_le.2)))

end PushCode

/-! #### The merge -/

/-- The state of the merge: codes on `0`, `1`, `2`, all other stacks empty. -/
def mst (q lo ln : BitString) : Stacks 16 :=
  Function.update (Function.update (Function.update (fun _ => []) 0 q) 1 lo) 2 ln

/-- The state inside a step of the merge: `z` on `3`, flags `f₁`, `f₂` on `6`, `7`. -/
def mst2 (q lo ln z f₁ f₂ : BitString) : Stacks 16 :=
  Function.update (Function.update (Function.update (mst q lo ln) 3 z) 6 f₁) 7 f₂

/-- The stacks of `memTest` for a membership test in the code on `1`: string `3`, list `1`,
flag `6`, work stacks `8`–`13`. -/
def memMapO : Fin 9 → Fin 16 := ![3, 1, 6, 8, 9, 10, 11, 12, 13]

/-- The stacks of `memTest` for a membership test in the code on `2`: string `3`, list `2`,
flag `7`, work stacks `8`–`13`. -/
def memMapN : Fin 9 → Fin 16 := ![3, 2, 7, 8, 9, 10, 11, 12, 13]

/-- The assignment `memMapO` of the nine stacks of `memTest` to stacks of the merge is
injective. -/
theorem memMapO_injective : Function.Injective memMapO := by decide

/-- The assignment `memMapN` of the nine stacks of `memTest` to stacks of the merge is
injective. -/
theorem memMapN_injective : Function.Injective memMapN := by decide

/-- **Membership in the old list.**  In the merge state `mst2 q (encList L) ln z [] f₂`, which
has the code of `L` on stack `1`, the string `z` on `3` and stack `6` empty, the renamed `memTest`
pushes the flag `decide (z ∈ L)` on `6` and changes nothing else, within the initial space plus
`|encList L| + 2`. -/
theorem exec_memO {q ln z f₂ : BitString} {L : List BitString} :
    Exec (Stmt.memTest.rename memMapO) (mst2 q (Stacks.encList L) ln z [] f₂)
      (mst2 q (Stacks.encList L) ln z [decide (z ∈ L)] f₂)
      ((mst2 q (Stacks.encList L) ln z [] f₂).space + (Stacks.encList L).length + 2) := by
  generalize hτ : mst2 q (Stacks.encList L) ln z [] f₂ = τ
  obtain ⟨h1, h6, h8, h9, h10, h11, h12, h13⟩ : τ 1 = Stacks.encList L ∧ τ 6 = [] ∧
      τ 8 = [] ∧ τ 9 = [] ∧ τ 10 = [] ∧ τ 11 = [] ∧ τ 12 = [] ∧ τ 13 = [] := by
    subst hτ
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpost : mst2 q (Stacks.encList L) ln z [decide (z ∈ L)] f₂ =
      Function.update τ 6 [decide (τ 3 ∈ L)] := by
    subst hτ
    funext j
    fin_cases j <;> rfl
  rw [hpost]
  have h := Stmt.exec_memTest (σ := fun r => τ (memMapO r)) (L := L) h1 h6 h8 h9 h10 h11 h12 h13
  have h' := Exec.rename_of_comp memMapO_injective h
  have e1 : Function.extend memMapO (Function.update (fun r => τ (memMapO r)) 2
      [decide (τ (memMapO 0) ∈ L)]) τ = Function.update τ 6 [decide (τ 3 ∈ L)] := by
    rw [← Stacks.update_extend memMapO_injective, Stacks.extend_comp_self memMapO_injective]
    rfl
  have e2 : Stacks.space (fun r => τ (memMapO r)) + Stacks.rest memMapO τ = τ.space := by
    rw [← Stacks.space_extend memMapO_injective, Stacks.extend_comp_self memMapO_injective]
  rw [e1] at h'
  exact h'.mono (by omega)

/-- **Membership in the new list.**  In the merge state `mst2 q lo (encList L) z f₁ []`, which
has the code of `L` on stack `2`, the string `z` on `3` and stack `7` empty, the renamed `memTest`
pushes the flag `decide (z ∈ L)` on `7` and changes nothing else, within the initial space plus
`|encList L| + 2`. -/
theorem exec_memN {q lo z f₁ : BitString} {L : List BitString} :
    Exec (Stmt.memTest.rename memMapN) (mst2 q lo (Stacks.encList L) z f₁ [])
      (mst2 q lo (Stacks.encList L) z f₁ [decide (z ∈ L)])
      ((mst2 q lo (Stacks.encList L) z f₁ []).space + (Stacks.encList L).length + 2) := by
  generalize hτ : mst2 q lo (Stacks.encList L) z f₁ [] = τ
  obtain ⟨h1, h7, h8, h9, h10, h11, h12, h13⟩ : τ 2 = Stacks.encList L ∧ τ 7 = [] ∧
      τ 8 = [] ∧ τ 9 = [] ∧ τ 10 = [] ∧ τ 11 = [] ∧ τ 12 = [] ∧ τ 13 = [] := by
    subst hτ
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpost : mst2 q lo (Stacks.encList L) z f₁ [decide (z ∈ L)] =
      Function.update τ 7 [decide (τ 3 ∈ L)] := by
    subst hτ
    funext j
    fin_cases j <;> rfl
  rw [hpost]
  have h := Stmt.exec_memTest (σ := fun r => τ (memMapN r)) (L := L) h1 h7 h8 h9 h10 h11 h12 h13
  have h' := Exec.rename_of_comp memMapN_injective h
  have e1 : Function.extend memMapN (Function.update (fun r => τ (memMapN r)) 2
      [decide (τ (memMapN 0) ∈ L)]) τ = Function.update τ 7 [decide (τ 3 ∈ L)] := by
    rw [← Stacks.update_extend memMapN_injective, Stacks.extend_comp_self memMapN_injective]
    rfl
  have e2 : Stacks.space (fun r => τ (memMapN r)) + Stacks.rest memMapN τ = τ.space := by
    rw [← Stacks.space_extend memMapN_injective, Stacks.extend_comp_self memMapN_injective]
  rw [e1] at h'
  exact h'.mono (by omega)

/-- One step of the merge: decode the first string `z` of the code on `0` (onto `3`), test
`z ∈ Lo` (code on `1`, flag `6`) and `z ∈ Ln` (code on `2`, flag `7`), push the code of `z` on
`2` if both tests fail, and clean up. -/
def mergeBody : Stmt 16 :=
  Stmt.seqs [Stmt.decodeOne 0 5 4, Stmt.clear 4, Stmt.moveAll 5 3,
    Stmt.memTest.rename memMapO, Stmt.memTest.rename memMapN,
    Stmt.caseBit 6 (fun g₁ => Stmt.caseBit 7 (fun g₂ =>
      if g₁ || g₂ then .skip else pushCode 3 4 2)),
    .pop 6, .pop 7, Stmt.clear 3]

/-- The merge: run `mergeBody` while the code on `0` is nonempty. -/
def mergeStmt : Stmt 16 := .loop 0 Option.isSome mergeBody

/-- The space of the merge state `mst q lo ln` is the total length `|q| + |lo| + |ln|` of the
three codes. -/
theorem mst_space (q lo ln : BitString) :
    (mst q lo ln).space = q.length + lo.length + ln.length := by
  simp [Stacks.space, mst, Fin.sum_univ_succ, Function.update_apply]
  ring

/-- The space of the inner merge state `mst2 q lo ln z f₁ f₂` is the total length of the six
strings on its stacks. -/
theorem mst2_space (q lo ln z f₁ f₂ : BitString) :
    (mst2 q lo ln z f₁ f₂).space =
      q.length + lo.length + ln.length + z.length + f₁.length + f₂.length := by
  simp [Stacks.space, mst2, mst, Fin.sum_univ_succ, Function.update_apply]
  ring

/-- One step of the merge: with the code of `z :: Q` on stack `0` and the codes of `Lo` and `Ln`
on `1` and `2`, `mergeBody` consumes the code of `z` from `0` and pushes it on the code of `Ln`
unless `z ∈ Lo` or `z ∈ Ln`, restoring `1` and leaving all other stacks empty, within any space
`S` that is at least `|encList (z :: Q)| + 2 |encList Lo| + 2 |encList Ln| + 3 |z| + 5`. -/
theorem exec_mergeBody (z : BitString) (Q Lo Ln : List BitString) {S : ℕ}
    (hS : (Stacks.encList (z :: Q)).length + 2 * (Stacks.encList Lo).length +
      2 * (Stacks.encList Ln).length + 3 * z.length + 5 ≤ S) :
    Exec mergeBody (mst (Stacks.encList (z :: Q)) (Stacks.encList Lo) (Stacks.encList Ln))
      (mst (Stacks.encList Q) (Stacks.encList Lo)
        (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln))) S := by
  have hlen := length_encList_cons z Q
  have sA := mst_space (Stacks.encList (z :: Q)) (Stacks.encList Lo) (Stacks.encList Ln)
  -- 1. decode `z`
  have hz : (mst (Stacks.encList (z :: Q)) (Stacks.encList Lo) (Stacks.encList Ln)) 0 =
      Stacks.encStr z ++ Stacks.encList Q := encList_cons z Q
  have e1 : Exec (Stmt.decodeOne 0 5 4)
      (mst (Stacks.encList (z :: Q)) (Stacks.encList Lo) (Stacks.encList Ln))
      (Function.update (Function.update (mst (Stacks.encList Q) (Stacks.encList Lo)
        (Stacks.encList Ln)) 5 z.reverse) 4 (Stacks.encStr z).reverse)
      ((mst (Stacks.encList (z :: Q)) (Stacks.encList Lo) (Stacks.encList Ln)).space +
        z.length) :=
    Stmt.exec_of_eq (Stmt.exec_decodeOne (by decide : (0 : Fin 16) ≠ 5)
      (by decide : (0 : Fin 16) ≠ 4) (by decide : (5 : Fin 16) ≠ 4) hz)
      (by funext j; fin_cases j <;> simp [mst])
  -- 2. clear the code copy
  have e2 : Exec (Stmt.clear 4) (Function.update (Function.update (mst (Stacks.encList Q)
      (Stacks.encList Lo) (Stacks.encList Ln)) 5 z.reverse) 4 (Stacks.encStr z).reverse)
      (Function.update (mst (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln)) 5
        z.reverse) _ :=
    Stmt.exec_of_eq (Stmt.exec_clear 4 _ _ rfl) (by funext j; fin_cases j <;> rfl)
  -- 3. put `z` in order on `3`
  have e3 : Exec (Stmt.moveAll 5 3) (Function.update (mst (Stacks.encList Q)
      (Stacks.encList Lo) (Stacks.encList Ln)) 5 z.reverse)
      (mst2 (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) z [] []) _ :=
    Stmt.exec_of_eq (Stmt.exec_moveAll (by decide : (5 : Fin 16) ≠ 3) _ _ rfl)
      (by funext j; fin_cases j <;> simp [mst2, mst])
  -- 4., 5. the membership tests
  have e4 : Exec (Stmt.memTest.rename memMapO)
      (mst2 (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) z [] [])
      (mst2 (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) z [decide (z ∈ Lo)] [])
      _ := exec_memO
  have e5 : Exec (Stmt.memTest.rename memMapN)
      (mst2 (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) z [decide (z ∈ Lo)] [])
      (mst2 (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) z [decide (z ∈ Lo)]
        [decide (z ∈ Ln)]) _ := exec_memN
  -- spaces
  have s3 := mst2_space (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) z [] []
  have s4 := mst2_space (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) z
    [decide (z ∈ Lo)] []
  have s5 := mst2_space (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) z
    [decide (z ∈ Lo)] [decide (z ∈ Ln)]
  simp only [List.length_nil, List.length_singleton] at s3 s4 s5
  -- 6. push the code of `z` if it is new
  have hLn' : (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)).length ≤
      (Stacks.encList Ln).length + 2 * z.length + 1 := by
    split_ifs
    · omega
    · rw [length_encList_cons]; omega
  have e6 : Exec (Stmt.caseBit 6 (fun g₁ => Stmt.caseBit 7 (fun g₂ =>
      if g₁ || g₂ then .skip else pushCode 3 4 2)))
      (mst2 (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln) z [decide (z ∈ Lo)]
        [decide (z ∈ Ln)])
      (mst2 (Stacks.encList Q) (Stacks.encList Lo)
        (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [decide (z ∈ Lo)]
        [decide (z ∈ Ln)]) S := by
    rw [Stmt.exec_caseBit (b := decide (z ∈ Lo)) (l := []) rfl,
      Stmt.exec_caseBit (b := decide (z ∈ Ln)) (l := []) rfl]
    by_cases h : z ∈ Lo ∨ z ∈ Ln
    · have hg : (decide (z ∈ Lo) || decide (z ∈ Ln)) = true := by simpa using h
      rw [ite_eq_left hg, ite_eq_left h]
      exact .skip (by omega)
    · have hg : (decide (z ∈ Lo) || decide (z ∈ Ln)) = false := by simpa using h
      rw [ite_eq_right (by rw [hg]; decide), ite_eq_right h]
      have e := exec_pushCode (by decide : (3 : Fin 16) ≠ 4) (by decide : (3 : Fin 16) ≠ 2)
        (by decide : (4 : Fin 16) ≠ 2) (σ := mst2 (Stacks.encList Q) (Stacks.encList Lo)
          (Stacks.encList Ln) z [decide (z ∈ Lo)] [decide (z ∈ Ln)]) rfl
      refine Stmt.exec_of_eq (e.mono ?_) ?_
      · change _ + 2 * z.length + 1 ≤ S
        omega
      · rw [encList_cons]
        funext j; fin_cases j <;> rfl
  -- 7.–9. clean up
  have s6 := mst2_space (Stacks.encList Q) (Stacks.encList Lo)
    (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [decide (z ∈ Lo)]
    [decide (z ∈ Ln)]
  simp only [List.length_singleton] at s6
  have e7 := Exec.pop (r := 6) (σ := mst2 (Stacks.encList Q) (Stacks.encList Lo)
    (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [decide (z ∈ Lo)]
    [decide (z ∈ Ln)]) (S := S) (by omega)
  have h7 : Function.update (mst2 (Stacks.encList Q) (Stacks.encList Lo)
      (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [decide (z ∈ Lo)]
      [decide (z ∈ Ln)]) 6 ((mst2 (Stacks.encList Q) (Stacks.encList Lo)
      (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [decide (z ∈ Lo)]
      [decide (z ∈ Ln)]) 6).tail = mst2 (Stacks.encList Q) (Stacks.encList Lo)
      (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [] [decide (z ∈ Ln)] := by
    funext j; fin_cases j <;> rfl
  rw [h7] at e7
  have e8 := Exec.pop (r := 7) (σ := mst2 (Stacks.encList Q) (Stacks.encList Lo)
    (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [] [decide (z ∈ Ln)]) (S := S)
    e7.space_le.2
  have h8 : Function.update (mst2 (Stacks.encList Q) (Stacks.encList Lo)
      (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [] [decide (z ∈ Ln)]) 7
      ((mst2 (Stacks.encList Q) (Stacks.encList Lo)
      (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [] [decide (z ∈ Ln)]) 7).tail =
      mst2 (Stacks.encList Q) (Stacks.encList Lo)
      (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [] [] := by
    funext j; fin_cases j <;> rfl
  rw [h8] at e8
  have e9 := Stmt.exec_clear 3 _ (mst2 (Stacks.encList Q) (Stacks.encList Lo)
      (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [] []) rfl
  have h9 : Function.update (mst2 (Stacks.encList Q) (Stacks.encList Lo)
      (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) z [] []) 3 [] =
      mst (Stacks.encList Q) (Stacks.encList Lo)
        (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)) := by
    funext j; fin_cases j <;> rfl
  rw [h9] at e9
  have sp1 := e1.space_le.2
  have sp2 := e2.space_le.2
  have sp9 := e9.space_le.2
  have sp8 := e8.space_le.2
  exact .seq (e1.mono (by omega)) (.seq (e2.mono (by omega)) (.seq (e3.mono (by omega))
    (.seq (e4.mono (by omega)) (.seq (e5.mono (by omega)) (.seq e6 (.seq e7 (.seq e8
      (.seq (e9.mono (sp8.trans le_rfl)) (.skip (sp9.trans sp8))))))))))

/-- The merge loop: for any space bound `S` of at least `4 |encList Q| + 2 |encList Lo| +
2 |encList Ln| + 5`, `mergeStmt` turns the state with the codes of `Q`, `Lo`, `Ln` on stacks `0`,
`1`, `2` into the state with `0` empty and the code of `mergeL Lo Q Ln` on `2`, restoring `1`,
within space `S`. -/
theorem exec_mergeLoop (Lo : List BitString) : ∀ (Q Ln : List BitString) {S : ℕ},
    4 * (Stacks.encList Q).length + 2 * (Stacks.encList Lo).length +
      2 * (Stacks.encList Ln).length + 5 ≤ S →
    Exec mergeStmt (mst (Stacks.encList Q) (Stacks.encList Lo) (Stacks.encList Ln))
      (mst [] (Stacks.encList Lo) (Stacks.encList (mergeL Lo Q Ln))) S
  | [], Ln, S, hS => by
    have e : Stacks.encList ([] : List BitString) = [] := rfl
    rw [e]
    refine .loopF rfl ?_
    rw [mst_space]; simp only [List.length_nil]; omega
  | z :: Q, Ln, S, hS => by
    have hlen := length_encList_cons z Q
    have hLn' : (Stacks.encList (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln)).length ≤
        (Stacks.encList Ln).length + 2 * z.length + 1 := by
      split_ifs
      · omega
      · rw [length_encList_cons]; omega
    have e1 := exec_mergeBody z Q Lo Ln (S := S) (by omega)
    have e2 := exec_mergeLoop Lo Q (if z ∈ Lo ∨ z ∈ Ln then Ln else z :: Ln) (S := S) (by omega)
    have hc : Option.isSome ((mst (Stacks.encList (z :: Q)) (Stacks.encList Lo)
        (Stacks.encList Ln)) 0).head? = true := by
      change Option.isSome (Stacks.encList (z :: Q)).head? = true
      rw [encList_cons]
      cases z <;> simp [Stacks.encStr]
    exact .loopT hc e1 e2

/-- **Merge** (16 stacks): with the codes of `Q` on `0`, `Lo` on `1`, `Ln` on `2`, consume `0`
and leave the code of `mergeL Lo Q Ln` on `2`, restoring `1`; all other stacks empty before and
after. -/
theorem exists_mergeStmt : ∃ (s : Stmt 16) (K : ℕ), ∀ (Q Lo Ln : List BitString),
    Exec s (Function.update (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Q))
        1 (Stacks.encList Lo)) 2 (Stacks.encList Ln))
      (Function.update (Function.update (fun _ => []) 1 (Stacks.encList Lo)) 2
        (Stacks.encList (mergeL Lo Q Ln)))
      (K * ((Stacks.encList Q).length + (Stacks.encList Lo).length +
        (Stacks.encList Ln).length + 1)) := by
  refine ⟨mergeStmt, 5, fun Q Lo Ln => ?_⟩
  have h := exec_mergeLoop Lo Q Ln (S := 5 * ((Stacks.encList Q).length +
    (Stacks.encList Lo).length + (Stacks.encList Ln).length + 1)) (by omega)
  refine Stmt.exec_of_eq h ?_
  funext j; fin_cases j <;> rfl

/-- **Recording simulation** (21 stacks): with `x` on `0` and the code of `L` on `1`, simulate the
clocked machine `(c, e)` with the oracle `{z | z ∈ L}` and leave on `16` the code of a list `Q` of
exactly the queries made within the clock, restoring `0`, `1`; all other stacks empty before and
after. -/
theorem exists_recSimStmt (c : OTMCode) (e : ℕ) :
    ∃ (s : Stmt 21) (C : ℕ), ∀ (x : BitString) (L : List BitString), ∃ Q : List BitString,
      (∀ z, z ∈ Q ↔ z ∈ queries c.toOTM {z | z ∈ L} x (clock e x.length)) ∧
      Exec s (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList L))
        (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1
          (Stacks.encList L)) 16 (Stacks.encList Q))
        (C * (x.length + clock e x.length + (Stacks.encList L).length + 1) ^ 2) :=
  ⟨SimOTM.recSimStmt c e, c.k + 20, fun x L =>
    ⟨SimOTM.recL c.toOTM {z | z ∈ L} x (clock e x.length),
      fun z => SimOTM.mem_recL _ _ _ z _, SimOTM.exec_recSim c e x L⟩⟩

end QEnum

end Kolmogorov.RandomStrings
