/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSAssembly

/-!
# The game statement: selection, filtering and output

Selecting the strings of a position (`selectBy`), filtering out the members of a coded list
(`exists_filterNotMemStmt`), the outcome statement of a position (`exists_outStmt`), and the
evaluation statement of the game `exists_gameStmt`, with the placement helpers `place3`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-! #### Selection of the strings of a position -/

/-- Select the strings of `L` whose aligned bit is set. -/
def selectBy : List BitString → List Bool → List BitString
  | z :: L, b :: bs => if b then z :: selectBy L bs else selectBy L bs
  | _, _ => []

/-- Selecting elements of `LX` corresponding to the boolean list `Stacks.posBits LX S` returns
exactly the elements of `LX` that are present in `S`. -/
theorem selectBy_posBits (LX : List BitString) (S : Finset BitString) :
    selectBy LX (Stacks.posBits LX S) = LX.filter fun z => decide (z ∈ S) := by
  induction LX with
  | nil => rfl
  | cons z L ih =>
    simp only [Stacks.posBits, List.map_cons] at ih ⊢
    unfold selectBy
    rw [ih, List.filter_cons]

namespace Stmt

/-- The body of the re-encoding loop on 9 stacks: pop a bit `b` of stack `7` and push `true, b`
on stack `6`. -/
def encBody : Stmt 9 := caseBit 7 fun b => seqs [.pop 7, .push 6 true, .push 6 b]

/-- Execution of `encBody` repeatedly until stack 7 is empty: re-encodes the string `z` from stack
7 into a sequence of pairs `true, b` onto stack 6, with space overhead bounded by the length of
`z`. -/
theorem exec_encLoop : ∀ (z : BitString) (σ : Stacks 9), σ 7 = z →
    Exec (.loop 7 Option.isSome encBody) σ
      (Function.update (Function.update σ 7 []) 6
        ((z.flatMap fun b => [true, b]).reverse ++ σ 6)) (σ.space + z.length)
  | [], σ, h7 => exec_of_eq (.loopF (by simp [h7]) (by omega))
      (by funext j; simp only [Function.update_apply]; split_ifs <;> subst_vars <;> simp_all)
  | b :: z, σ, h7 => by
    have s1 := space_update_of_cons h7
    have e1 := exec_pop_cons h7 (S := σ.space + (b :: z).length) (by omega)
    have e2 := Exec.push (r := 6) (b := true) (σ := Function.update σ 7 z)
      (S := σ.space + (b :: z).length) (by simp; omega)
    have s2 := Stacks.space_update_cons (Function.update σ 7 z) 6 true
    have e3 := Exec.push (r := 6) (b := b)
      (σ := Function.update (Function.update σ 7 z) 6 (true :: (Function.update σ 7 z) 6))
      (S := σ.space + (b :: z).length) (by simp only [List.length_cons] at *; omega)
    rw [Function.update_self, Function.update_idem] at e3
    have hbody : Exec encBody σ (Function.update (Function.update σ 7 z) 6
        (b :: true :: (Function.update σ 7 z) 6)) (σ.space + (b :: z).length) := by
      rw [encBody, exec_caseBit h7]
      exact .seq e1 (.seq e2 (.seq e3 (.skip e3.space_le.2)))
    have ih := exec_encLoop z _ (show (Function.update (Function.update σ 7 z) 6
      (b :: true :: (Function.update σ 7 z) 6)) 7 = z by simp)
    have sp : Stacks.space (Function.update (Function.update σ 7 z) 6
        (b :: true :: (Function.update σ 7 z) 6)) + z.length ≤ σ.space + (b :: z).length := by
      have := hbody.space_le.2
      have s3 := Stacks.space_update (Function.update σ 7 z) 6
          (b :: true :: (Function.update σ 7 z) 6)
      simp only [List.length_cons] at s3 ⊢
      omega
    refine .loopT (by simp [h7]) hbody (exec_of_eq (ih.mono sp) ?_)
    funext j
    simp only [Function.update_apply, List.flatMap_cons, List.reverse_cons,
      List.nil_append, List.append_assoc, List.cons_append]
    split_ifs <;> subst_vars <;> simp_all

/-- One step of the selection on 9 stacks (`0` the coded list, `1` the bits, `4`, `5` the consumed
codes and bits, `6` the selected codes, reversed; `3`, `7` work stacks). -/
def selStep : Stmt 9 :=
  seqs [decodeOne 0 3 4, caseBit 1 fun bit => .seq (moveBit 1 5)
    (if bit then seqs [moveAll 3 7, .loop 7 Option.isSome encBody, .push 6 false] else clear 3)]

/-- One loop step of the selection statement `selStep`: pops the next coded string from stack 0,
then if the corresponding bit on stack 1 is set, re-encodes it reversed onto the output stack 6,
within space overhead bounded by the length of the coded string. -/
theorem exec_selStep {σ : Stacks 9} {z rest bs : BitString} {bit : Bool}
    (h0 : σ 0 = Stacks.encStr z ++ rest) (h1 : σ 1 = bit :: bs) (h3 : σ 3 = []) (h7 : σ 7 = []) :
    Exec selStep σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ 0 rest)
        4 ((Stacks.encStr z).reverse ++ σ 4)) 1 bs) 5 (bit :: σ 5)) 6
        ((if bit then (Stacks.encStr z).reverse else []) ++ σ 6))
      (σ.space + (Stacks.encStr z).length) := by
  have hz := Stacks.length_encStr z
  have e1 := exec_decodeOne (Lst := 0) (W := 3) (Tmp := 4) (by decide) (by decide) (by decide) h0
  rw [h3, List.append_nil] at e1
  set σ1 := Function.update (Function.update (Function.update σ 0 rest) 3 z.reverse) 4
    ((Stacks.encStr z).reverse ++ σ 4) with hσ1
  have h11 : σ1 1 = bit :: bs := by simp [hσ1, h1]
  have e2 := exec_moveBit (r := 1) (r' := 5) (by decide) h11
  set σ2 := Function.update (Function.update σ1 1 bs) 5 (bit :: σ1 5) with hσ2
  have sp1 := e1.space_le.2
  have sp2 := e2.space_le.2
  rw [selStep]
  cases bit
  · -- not selected: drop the decoded string
    have e3 := exec_clear (3 : Fin 9) _ σ2 rfl
    have sp3 := e3.space_le.2
    have hmid : Exec (caseBit 1 fun bit => .seq (moveBit 1 5)
        (if bit then seqs [moveAll 3 7, .loop 7 Option.isSome encBody, .push 6 false]
          else clear 3)) σ1 (Function.update σ2 3 []) (σ.space + (Stacks.encStr z).length) := by
      rw [exec_caseBit h11]
      exact .seq (e2.mono (by omega)) (e3.mono (by omega))
    refine exec_of_eq (.seq (e1.mono (by omega)) (.seq hmid (.skip (by omega)))) ?_
    funext j
    simp only [hσ2, hσ1, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · -- selected: re-encode the decoded string onto stack 6
    have h23 : σ2 3 = z.reverse := by simp [hσ2, hσ1]
    have e3 := exec_moveAll (r := 3) (r' := 7) (by decide) z.reverse σ2 h23
    rw [List.reverse_reverse] at e3
    set σ3 := Function.update (Function.update σ2 3 []) 7 (z ++ σ2 7) with hσ3
    have h37 : σ3 7 = z := by simp [hσ3, hσ2, hσ1, h7]
    have e4 := exec_encLoop z σ3 h37
    set σ4 := Function.update (Function.update σ3 7 []) 6
      ((z.flatMap fun b => [true, b]).reverse ++ σ3 6) with hσ4
    have sp3 := e3.space_le.2
    have sp4 := e4.space_le.2
    have e5 := Exec.push (r := 6) (b := false) (σ := σ4) (S := σ.space + (Stacks.encStr z).length)
      (by omega)
    have hmid : Exec (caseBit 1 fun bit => .seq (moveBit 1 5)
        (if bit then seqs [moveAll 3 7, .loop 7 Option.isSome encBody, .push 6 false]
          else clear 3)) σ1 (Function.update σ4 6 (false :: σ4 6))
          (σ.space + (Stacks.encStr z).length) := by
      rw [exec_caseBit h11]
      exact .seq (e2.mono (by omega)) (.seq (e3.mono (by omega)) (.seq (e4.mono (by omega))
        (.seq e5 (.skip e5.space_le.2))))
    refine exec_of_eq (.seq (e1.mono (by omega)) (.seq hmid (.skip hmid.space_le.2))) ?_
    funext j
    obtain ⟨n, hn⟩ := j
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    all_goals first
      | omega
      | simp [hσ4, hσ3, hσ2, hσ1, Stacks.encStr, h3, h7]

/-- Looping `selStep` over all members of `R` reads the codes from stack 0 and matching bits from
stack 1, transferring them to the consumed stacks 4 and 5, and producing on stack 6 the reversed
codes of elements whose bit is `true`. -/
theorem exec_selLoop : ∀ (R : List BitString) (bs : List Bool) (σ : Stacks 9) (S : ℕ),
    bs.length = R.length → σ 0 = Stacks.encList R → σ 1 = bs → σ 3 = [] → σ 7 = [] →
    σ.space + (Stacks.encList R).length + 1 ≤ S →
    Exec (.loop 0 Option.isSome selStep) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ 0 [])
        4 ((Stacks.encList R).reverse ++ σ 4)) 1 []) 5 (bs.reverse ++ σ 5)) 6
        ((Stacks.encList (selectBy R bs)).reverse ++ σ 6)) S
  | [], [], σ, S, _, h0, h1, h3, h7, hS => by
    simp only [Stacks.encList, List.flatMap_nil] at h0
    refine exec_of_eq (.loopF (by simp [h0]) (by omega)) ?_
    funext j
    obtain ⟨n, hn⟩ := j
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    all_goals first
      | omega
      | simp [Stacks.encList, selectBy, h0, h1]
  | z :: R, bit :: bs, σ, S, hlen, h0, h1, h3, h7, hS => by
    have hz := Stacks.length_encStr z
    have hlenR : (Stacks.encList (z :: R)).length =
        (Stacks.encStr z).length + (Stacks.encList R).length := by
      simp [Stacks.encList]
    have h0' : σ 0 = Stacks.encStr z ++ Stacks.encList R := by rw [h0]; simp [Stacks.encList]
    have e := exec_selStep h0' h1 h3 h7
    have spe := e.space_le.2
    have ih := exec_selLoop R bs
      (Function.update (Function.update (Function.update (Function.update (Function.update σ 0
        (Stacks.encList R)) 4 ((Stacks.encStr z).reverse ++ σ 4)) 1 bs) 5 (bit :: σ 5)) 6
        ((if bit then (Stacks.encStr z).reverse else []) ++ σ 6)) S (by simpa using hlen)
      (by simp) (by simp) (by simp [h3]) (by simp [h7]) (by omega)
    refine .loopT (by rw [h0']; cases z <;> simp [Stacks.encStr]) (e.mono (by omega))
      (exec_of_eq ih ?_)
    funext j
    obtain ⟨n, hn⟩ := j
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    all_goals first
      | omega
      | (cases bit <;> simp [Stacks.encList, selectBy, List.reverse_append])

end Stmt

/-- **Selecting a position.**  A statement which, started on
`[encList LX, posBits LX S]` (stacks `0`, `1`; all other stacks empty), adds on stack `2` the
code of `LX.filter (· ∈ S)`, within space
`C · (|encList LX| + |LX| + 1)`.  Proof: one loop (`Stmt.selStep`, `Stmt.exec_selLoop`) over `LX`
with `Stmt.decodeOne`, re-encoding the current string onto a reversed output when the current
bit is `true` (`Stmt.exec_encLoop`), then restoring the inputs (`selectBy_posBits`). -/
theorem exists_selectStmt :
    ∃ (k : ℕ) (s : Stmt k) (C : ℕ), 3 ≤ k ∧ ∀ (LX : List BitString) (S : Finset BitString),
      Exec s (Stacks.layout k [Stacks.encList LX, Stacks.posBits LX S])
        (Stacks.layout k [Stacks.encList LX, Stacks.posBits LX S,
          Stacks.encList (LX.filter fun z => decide (z ∈ S))])
        (C * ((Stacks.encList LX).length + LX.length + 1)) := by
  refine ⟨9, Stmt.seqs [.loop 0 Option.isSome Stmt.selStep, Stmt.moveAll 4 0, Stmt.moveAll 5 1,
    Stmt.moveAll 6 2], 2, by norm_num, fun LX S => ?_⟩
  have hsp : Stacks.space (Stacks.layout 9 [Stacks.encList LX, Stacks.posBits LX S]) =
      (Stacks.encList LX).length + LX.length := by
    rw [Stacks.space_layout _ (by simp)]
    simp [Stacks.posBits]
  have e1 := Stmt.exec_selLoop LX (Stacks.posBits LX S)
    (Stacks.layout 9 [Stacks.encList LX, Stacks.posBits LX S])
    (2 * ((Stacks.encList LX).length + LX.length + 1)) (by simp [Stacks.posBits]) rfl rfl rfl rfl
    (by omega)
  set σL := Function.update (Function.update (Function.update (Function.update (Function.update
      (Stacks.layout 9 [Stacks.encList LX, Stacks.posBits LX S]) 0 []) 4
      ((Stacks.encList LX).reverse ++ (Stacks.layout 9 [Stacks.encList LX,
        Stacks.posBits LX S]) 4)) 1 []) 5 ((Stacks.posBits LX S).reverse ++
          (Stacks.layout 9 [Stacks.encList LX, Stacks.posBits LX S]) 5)) 6
      ((Stacks.encList (selectBy LX (Stacks.posBits LX S))).reverse ++
        (Stacks.layout 9 [Stacks.encList LX, Stacks.posBits LX S]) 6) with hσL
  have e2 := Stmt.exec_moveAll (r := 4) (r' := 0) (by decide) _ σL rfl
  set σ2 := Function.update (Function.update σL 4 []) 0 ((σL 4).reverse ++ σL 0) with hσ2
  have e3 := Stmt.exec_moveAll (r := 5) (r' := 1) (by decide) _ σ2 rfl
  set σ3 := Function.update (Function.update σ2 5 []) 1 ((σ2 5).reverse ++ σ2 1) with hσ3
  have e4 := Stmt.exec_moveAll (r := 6) (r' := 2) (by decide) _ σ3 rfl
  have s1 := e1.space_le.2
  have s2 := e2.space_le.2
  have s3 := e3.space_le.2
  have s4 := e4.space_le.2
  refine Stmt.exec_of_eq (.seq e1 (.seq (e2.mono s1) (.seq (e3.mono (s2.trans s1))
    (.seq (e4.mono ((s3.trans s2).trans s1)) (.skip (((s4.trans s3).trans s2).trans s1)))))) ?_
  rw [← selectBy_posBits]
  funext j
  obtain ⟨n, hn⟩ := j
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  all_goals first
    | omega
    | simp [hσ3, hσ2, hσL, Stacks.layout]

/-- Replacing an empty string with `v` on stack `r` increases the overall space of `σ` by the
length of `v`. -/
theorem Stacks.space_update_nil {k : ℕ} (σ : Stacks k) (r : Fin k) (v : BitString) (h : σ r = []) :
    Stacks.space (Function.update σ r v) = σ.space + v.length := by
  have := σ.space_update r v; rw [h] at this; simpa using this

/-- **Procedure call with two results.** -/
theorem Exec.call2 {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f) {s : Stmt k}
    {τ : Stacks k'} {d₁ d₂ : Fin k} {v₁ v₂ : BitString} {S : ℕ}
    (h : Exec s (fun r => τ (f r))
      (Function.update (Function.update (fun r => τ (f r)) d₁ v₁) d₂ v₂) S) :
    Exec (s.rename f) τ (Function.update (Function.update τ (f d₁) v₁) (f d₂) v₂)
      (S + τ.space) := by
  have r := Exec.rename_of_comp hf h
  rw [← Stacks.update_extend hf, ← Stacks.update_extend hf, Stacks.extend_comp_self hf] at r
  exact r.mono (Nat.add_le_add_left (Stacks.rest_le_space f τ) _)

/-! #### Filtering a coded list -/

/-- Placement of the membership test inside the filtering procedure: `Z ↦ 7`, list `↦ 1`,
flag `↦ 8`, work stacks `3..8 ↦ 9..14`. -/
def memPlace (n : ℕ) : ℕ := if n = 0 then 7 else if n = 1 then 1 else if n = 2 then 8 else n + 6

/-- The stack placement function `memPlace` for the membership test is injective. -/
theorem memPlace_injective : Function.Injective memPlace := by
  intro a b h; unfold memPlace at h; split_ifs at h <;> omega

/-- Relocating stacks using an injective function does not increase the sum of their lengths. -/
theorem Stacks.space_comp_le {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f)
    (τ : Stacks k') : Stacks.space (fun r => τ (f r)) ≤ τ.space := by
  classical
  unfold Stacks.space
  rw [← Finset.sum_image (f := fun j => (τ j).length) (fun x _ y _ h => hf h)]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

namespace Stmt

/-- One step of the filtering on 15 stacks (`0` the coded list `LR`, `1` the coded list `LS`,
`4` the consumed codes, `6` the kept codes reversed, `3`, `7`, `8`, `9..14` work stacks). -/
def filtStep : Stmt 15 :=
  seqs [decodeOne 0 3 4, moveAll 3 7,
    memTest.rename fun i => ⟨memPlace i.val, by unfold memPlace; split_ifs <;> omega⟩,
    caseBit 8 fun g => .seq (.pop 8) (if g then clear 7 else
      .seq ((Stmt.loop 7 Option.isSome encBody).rename (Fin.castLE (by norm_num)))
        (.push 6 false))]

/-- One loop step of the filtering statement `filtStep`: pops the next coded string from stack 0,
checks if it is a member of the list on stack 1, and if not, re-encodes it reversed onto the output
stack 6. -/
theorem exec_filtStep {σ : Stacks 15} {z rest : BitString} {LS : List BitString}
    (h0 : σ 0 = Stacks.encStr z ++ rest) (h1 : σ 1 = Stacks.encList LS) (h3 : σ 3 = [])
    (h7 : σ 7 = []) (h8 : σ 8 = []) (hw : ∀ j : Fin 15, 9 ≤ j.val → σ j = []) :
    Exec filtStep σ
      (Function.update (Function.update (Function.update σ 0 rest) 4
        ((Stacks.encStr z).reverse ++ σ 4)) 6
        ((if z ∈ LS then [] else (Stacks.encStr z).reverse) ++ σ 6))
      (2 * σ.space + 3 * z.length + (Stacks.encList LS).length + 4) := by
  classical
  have hz := Stacks.length_encStr z
  have e1 := exec_decodeOne (Lst := 0) (W := 3) (Tmp := 4) (by decide) (by decide) (by decide) h0
  rw [h3, List.append_nil] at e1
  set σ1 := Function.update (Function.update (Function.update σ 0 rest) 3 z.reverse) 4
    ((Stacks.encStr z).reverse ++ σ 4) with hσ1
  have e2 := exec_moveAll (r := 3) (r' := 7) (by decide) z.reverse σ1 (by simp [hσ1])
  rw [List.reverse_reverse] at e2
  set σ2 := Function.update (Function.update σ1 3 []) 7 (z ++ σ1 7) with hσ2
  have h27 : σ2 7 = z := by simp [hσ2, hσ1, h7]
  -- the membership test
  have hmp : Function.Injective (fun i : Fin 9 =>
      (⟨memPlace i.val, by unfold memPlace; split_ifs <;> omega⟩ : Fin 15)) :=
    fun a b h => Fin.ext (memPlace_injective (congrArg Fin.val h))
  have hm := exec_memTest (σ := fun r : Fin 9 => σ2 ⟨memPlace r.val, by
      unfold memPlace; split_ifs <;> omega⟩) (L := LS)
    (by simp [memPlace, hσ2, hσ1, h1]) (by simp [memPlace, hσ2, hσ1, h8])
    (by simp [memPlace, hσ2, hσ1, hw 9 (by decide)])
    (by simp [memPlace, hσ2, hσ1, hw 10 (by decide)])
    (by simp [memPlace, hσ2, hσ1, hw 11 (by decide)])
    (by simp [memPlace, hσ2, hσ1, hw 12 (by decide)])
    (by simp [memPlace, hσ2, hσ1, hw 13 (by decide)])
    (by simp [memPlace, hσ2, hσ1, hw 14 (by decide)])
  have e3 := Exec.call hmp hm
  have hflag : decide (σ2 ⟨memPlace ((0 : Fin 9) : ℕ),
          by unfold memPlace; split_ifs <;> omega⟩ ∈ LS) =
      decide (z ∈ LS) := by simp [memPlace, h27]
  rw [hflag] at e3
  set σ3 := Function.update σ2 ⟨memPlace ((2 : Fin 9) : ℕ), by unfold memPlace; split_ifs <;> omega⟩
    [decide (z ∈ LS)] with hσ3
  have sp1 := e1.space_le.2
  have sp2 := e2.space_le.2
  have spc := Stacks.space_comp_le hmp σ2
  have h28 : σ2 ⟨memPlace ((2 : Fin 9) : ℕ), by unfold memPlace; split_ifs <;> omega⟩ = [] := by
    simp [memPlace, hσ2, hσ1, h8]
  have sp3 : Stacks.space σ3 = Stacks.space σ2 + 1 := by
    rw [hσ3, Stacks.space_update_nil _ _ _ h28]; rfl
  have h38 : σ3 8 = [decide (z ∈ LS)] := by simp [hσ3, memPlace]
  have sp4 := space_update_of_cons h38
  set B := 2 * σ.space + 3 * z.length + (Stacks.encList LS).length + 4 with hB
  have e4 := exec_pop_cons h38 (S := B) (by omega)
  set σ4 := Function.update σ3 8 [] with hσ4
  have h47 : σ4 7 = z := by simp [hσ4, hσ3, memPlace, h27]
  by_cases hzL : z ∈ LS
  · have e5 := exec_clear (7 : Fin 15) _ σ4 rfl
    have hmid : Exec (caseBit 8 fun g => .seq (.pop 8) (if g then clear 7 else
        .seq ((Stmt.loop 7 Option.isSome encBody).rename (Fin.castLE (by norm_num)))
          (.push 6 false))) σ3 (Function.update σ4 7 []) B := by
      rw [exec_caseBit h38]
      simp only [hzL, decide_true, ↓reduceIte]
      exact .seq e4 (e5.mono (by have := e4.space_le.2; omega))
    refine exec_of_eq (.seq (e1.mono (by omega)) (.seq (e2.mono (by omega))
      (.seq (e3.mono (by omega)) (.seq hmid (.skip hmid.space_le.2))))) ?_
    funext j
    obtain ⟨n, hn⟩ := j
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    all_goals first
      | omega
      | simp [hσ4, hσ3, hσ2, hσ1, memPlace, hzL, h3, h7, h8]
  · have hres : (fun r : Fin 9 => σ4 (Fin.castLE (by norm_num : 9 ≤ 15) r)) 7 = z := h47
    have he := exec_encLoop z (fun r : Fin 9 => σ4 (Fin.castLE (by norm_num : 9 ≤ 15) r)) hres
    have e5 := Exec.call2 (Fin.castLE_injective (by norm_num : 9 ≤ 15)) he
    have spr := Stacks.space_comp_le (Fin.castLE_injective (by norm_num : 9 ≤ 15)) σ4
    obtain ⟨σ5, e5, hσ5⟩ := (⟨_, e5, rfl⟩ : ∃ σ5, Exec _ σ4 σ5 _ ∧ σ5 = _)
    have sp5 := e5.space_le.2
    have e6 := Exec.push (r := 6) (b := false) (σ := σ5) (S := B) (by omega)
    have hmid : Exec (caseBit 8 fun g => .seq (.pop 8) (if g then clear 7 else
        .seq ((Stmt.loop 7 Option.isSome encBody).rename (Fin.castLE (by norm_num)))
          (.push 6 false))) σ3 (Function.update σ5 6 (false :: σ5 6)) B := by
      rw [exec_caseBit h38]
      simp only [hzL, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact .seq e4 (.seq (e5.mono (by omega)) e6)
    refine exec_of_eq (.seq (e1.mono (by omega)) (.seq (e2.mono (by omega))
      (.seq (e3.mono (by omega)) (.seq hmid (.skip hmid.space_le.2))))) ?_
    subst hσ5
    funext j
    obtain ⟨n, hn⟩ := j
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    all_goals first
      | omega
      | simp [hσ4, hσ3, hσ2, hσ1, memPlace, hzL, h3, h7, h8, Stacks.encStr]


/-- Looping `filtStep` over all members of `R` reads the codes from stack 0, checking them against
the list `LS` on stack 1, and produces on stack 6 the reversed codes of elements that are not in
`LS`. -/
theorem exec_filtLoop (LS : List BitString) : ∀ (R : List BitString) (σ : Stacks 15) (S : ℕ),
    σ 0 = Stacks.encList R → σ 1 = Stacks.encList LS → σ 3 = [] → σ 7 = [] → σ 8 = [] →
    (∀ j : Fin 15, 9 ≤ j.val → σ j = []) →
    2 * σ.space + 2 * (Stacks.encList R).length + (Stacks.encList LS).length + 4 ≤ S →
    Exec (.loop 0 Option.isSome filtStep) σ
      (Function.update (Function.update (Function.update σ 0 []) 4
        ((Stacks.encList R).reverse ++ σ 4)) 6
        ((Stacks.encList (R.filter fun z => decide (z ∉ LS))).reverse ++ σ 6)) S
  | [], σ, S, h0, h1, h3, h7, h8, hw, hS => by
    simp only [Stacks.encList, List.flatMap_nil] at h0
    refine exec_of_eq (.loopF (by simp [h0]) (by omega)) ?_
    funext j
    by_cases h6 : j = 6
    · subst h6; simp [Stacks.encList]
    by_cases h4 : j = 4
    · subst h4; simp [Stacks.encList]
    by_cases h0_ : j = 0
    · subst h0_; simp [Stacks.encList, h0]
    have hj6 : j ≠ 6 := h6
    have hj4 : j ≠ 4 := h4
    have hj0 : j ≠ 0 := h0_
    simp [Function.update_of_ne hj6, Function.update_of_ne hj4, Function.update_of_ne hj0]
  | z :: R, σ, S, h0, h1, h3, h7, h8, hw, hS => by
    classical
    have hz := Stacks.length_encStr z
    have hlen : (Stacks.encList (z :: R)).length =
        (Stacks.encStr z).length + (Stacks.encList R).length := by
      simp [Stacks.encList]
    have h0' : σ 0 = Stacks.encStr z ++ Stacks.encList R := by rw [h0]; simp [Stacks.encList]
    have e := exec_filtStep h0' h1 h3 h7 h8 hw
    set σ' := Function.update (Function.update (Function.update σ 0 (Stacks.encList R)) 4
      ((Stacks.encStr z).reverse ++ σ 4)) 6
      ((if z ∈ LS then [] else (Stacks.encStr z).reverse) ++ σ 6) with hσ'
    have hsp : Stacks.space σ' ≤ σ.space + (Stacks.encStr z).length := by
      have s1 := σ.space_update 0 (Stacks.encList R)
      have s2 := Stacks.space_update (Function.update σ 0 (Stacks.encList R)) 4
        ((Stacks.encStr z).reverse ++ σ 4)
      have s3 := Stacks.space_update (Function.update (Function.update σ 0 (Stacks.encList R)) 4
        ((Stacks.encStr z).reverse ++ σ 4)) 6
        ((if z ∈ LS then [] else (Stacks.encStr z).reverse) ++ σ 6)
      have a1 : (Function.update σ 0 (Stacks.encList R)) 4 = σ 4 := by simp
      have a2 : (Function.update (Function.update σ 0 (Stacks.encList R)) 4
        ((Stacks.encStr z).reverse ++ σ 4)) 6 = σ 6 := by simp
      rw [a1] at s2
      rw [a2] at s3
      rw [h0', List.length_append] at s1
      have a3 : ((if z ∈ LS then [] else (Stacks.encStr z).reverse) ++ σ 6).length ≤
          (Stacks.encStr z).length + (σ 6).length := by
        split_ifs <;> simp
      simp only [List.length_append, List.length_reverse] at s2
      rw [hσ']
      omega
    have ih := exec_filtLoop LS R σ' S (by simp [hσ']) (by simp [hσ', h1]) (by simp [hσ', h3])
      (by simp [hσ', h7]) (by simp [hσ', h8])
      (fun j hj => by
        have h6 : j ≠ 6 := by rintro rfl; simp at hj
        have h4 : j ≠ 4 := by rintro rfl; simp at hj
        have h0 : j ≠ 0 := by rintro rfl; simp at hj
        rw [hσ', Function.update_of_ne h6, Function.update_of_ne h4, Function.update_of_ne h0]
        exact hw j hj)
      (by omega)
    refine .loopT (by rw [h0']; cases z <;> simp [Stacks.encStr]) (e.mono (by omega))
      (exec_of_eq ih ?_)
    funext j
    by_cases h6 : j = 6
    · subst h6
      by_cases hzL : z ∈ LS <;> simp [hσ', hzL, Stacks.encList, List.reverse_append]
    by_cases h4 : j = 4
    · subst h4
      by_cases hzL : z ∈ LS <;> simp [hσ', hzL, Stacks.encList, List.reverse_append]
    by_cases h0_ : j = 0
    · subst h0_
      by_cases hzL : z ∈ LS <;> simp [hσ', hzL, Stacks.encList, List.reverse_append]
    have hj6 : j ≠ 6 := h6
    have hj4 : j ≠ 4 := h4
    have hj0 : j ≠ 0 := h0_
    simp [Function.update_of_ne hj6, Function.update_of_ne hj4, Function.update_of_ne hj0, hσ']
end Stmt

/-- **Filtering out the members of a list.**  A statement which, started on
`[encList LR, encList LS]` (stacks `0`, `1`; all other stacks empty), adds on stack `2` the code of
`LR.filter (· ∉ LS)`, within space `C · (|encList LR| + |encList LS| + 1)`.  Proof: one loop
(`Stmt.filtStep`, `Stmt.exec_filtLoop`) over `LR` with `Stmt.decodeOne`, the 9-stack `Stmt.memTest`
inlined along
`memPlace` (`Exec.call`), and a re-encoding of the current string onto a reversed output when the
test fails (`Stmt.exec_encLoop` inlined along `Fin.castLE`), then restoring the inputs. -/
theorem exists_filterNotMemStmt :
    ∃ (k : ℕ) (s : Stmt k) (C : ℕ), 3 ≤ k ∧ ∀ (LR LS : List BitString),
      Exec s (Stacks.layout k [Stacks.encList LR, Stacks.encList LS])
        (Stacks.layout k [Stacks.encList LR, Stacks.encList LS,
          Stacks.encList (LR.filter fun z => decide (z ∉ LS))])
        (C * ((Stacks.encList LR).length + (Stacks.encList LS).length + 1)) := by
  refine ⟨15, Stmt.seqs [.loop 0 Option.isSome Stmt.filtStep, Stmt.moveAll 4 0,
    Stmt.moveAll 6 2], 5, by norm_num, fun LR LS => ?_⟩
  have hsp : Stacks.space (Stacks.layout 15 [Stacks.encList LR, Stacks.encList LS]) =
      (Stacks.encList LR).length + (Stacks.encList LS).length := by
    rw [Stacks.space_layout _ (by simp)]
    simp
  have e1 := Stmt.exec_filtLoop LS LR (Stacks.layout 15 [Stacks.encList LR, Stacks.encList LS])
    (5 * ((Stacks.encList LR).length + (Stacks.encList LS).length + 1)) rfl rfl rfl rfl rfl
    (fun j hj => by
      simp only [Stacks.layout]
      exact Stacks.getD_nil_of_le (by simp only [List.length_cons, List.length_nil]; omega))
    (by omega)
  set σL := Function.update (Function.update (Function.update
    (Stacks.layout 15 [Stacks.encList LR, Stacks.encList LS]) 0 []) 4
    ((Stacks.encList LR).reverse ++ (Stacks.layout 15 [Stacks.encList LR, Stacks.encList LS]) 4))
    6 ((Stacks.encList (LR.filter fun z => decide (z ∉ LS))).reverse ++
      (Stacks.layout 15 [Stacks.encList LR, Stacks.encList LS]) 6) with hσL
  have e2 := Stmt.exec_moveAll (r := 4) (r' := 0) (by decide) _ σL rfl
  set σ2 := Function.update (Function.update σL 4 []) 0 ((σL 4).reverse ++ σL 0) with hσ2
  have e3 := Stmt.exec_moveAll (r := 6) (r' := 2) (by decide) _ σ2 rfl
  have s1 := e1.space_le.2
  have s2 := e2.space_le.2
  have s3 := e3.space_le.2
  refine Stmt.exec_of_eq (.seq e1 (.seq (e2.mono s1) (.seq (e3.mono (s2.trans s1))
    (.skip ((s3.trans s2).trans s1))))) ?_
  funext j
  obtain ⟨n, hn⟩ := j
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  all_goals first
    | omega
    | simp [hσ2, hσL, Stacks.layout]

/-- Filtering a list of strings and coding the result yields a boolean list no longer than the code
of the original list. -/
theorem Stacks.length_encList_filter_le (L : List BitString) (p : BitString → Bool) :
    (Stacks.encList (L.filter p)).length ≤ (Stacks.encList L).length := by
  induction L with
  | nil => simp
  | cons z L ih =>
    rw [List.filter_cons]
    split_ifs
    · simp only [Stacks.encList, List.flatMap_cons, List.length_append] at ih ⊢; omega
    · simp only [Stacks.encList, List.flatMap_cons, List.length_append] at ih ⊢; omega

/-- Placement of the stacks of the selection procedure: `0 ↦ 1`, `1 ↦ 3`, `2 ↦ 5`, work stacks
from `7` on. -/
def outMap1 (n : ℕ) : ℕ := if n = 0 then 1 else if n = 1 then 3 else if n = 2 then 5 else 7 + n

/-- Placement of the stacks of the filtering procedure: `0 ↦ 2`, `1 ↦ 5`, `2 ↦ 6`, work stacks
from `7 + k₁` on. -/
def outMap2 (k₁ n : ℕ) : ℕ :=
    if n = 0 then 2 else if n = 1 then 5 else if n = 2 then 6 else 7 + k₁ + n

/-- The stack placement function `outMap1` for the selection procedure is injective. -/
theorem outMap1_injective : Function.Injective outMap1 := by
  intro a b h; unfold outMap1 at h; split_ifs at h <;> omega

/-- The stack placement function `outMap2` for the filtering procedure is injective. -/
theorem outMap2_injective (k₁ : ℕ) : Function.Injective (outMap2 k₁) := by
  intro a b h; unfold outMap2 at h; split_ifs at h <;> omega

/-- **Calling a procedure with a layout contract.**  A procedure `s` on `k` stacks which turns the
layout of `l` into the layout of `l ++ [v]`, inlined along an injective `f` into a configuration
`τ` whose stacks `f r` hold the entries of `l`, writes `v` onto the stack `f l.length` and changes
nothing else; the space grows by at most the current space. -/
theorem Exec.call_layout {k K : ℕ} {f : Fin k → Fin K} (hf : Function.Injective f) {s : Stmt k}
    {l : List BitString} {v : BitString} {S : ℕ}
    (h : Exec s (Stacks.layout k l) (Stacks.layout k (l ++ [v])) S) (hl : l.length < k)
    {τ : Stacks K} (hτ : ∀ r, τ (f r) = l.getD r.val []) :
    Exec (s.rename f) τ (Function.update τ (f ⟨l.length, hl⟩) v) (S + τ.space) := by
  rw [Stacks.layout_append l v hl, ← show (fun r => τ (f r)) = Stacks.layout k l from funext hτ]
    at h
  exact Exec.call hf h

/-- Seen through the placement `outMap1`, the entries `[x, a, b, c]` are `a` and `c` followed by
empty strings: the input stacks of the selection procedure. -/
theorem getD_outMap1 (x a b c : BitString) (n : ℕ) :
    [x, a, b, c].getD (outMap1 n) [] = [a, c].getD n [] := by
  unfold outMap1
  split_ifs with h0 h1 h2
  · subst h0; rfl
  · subst h1; rfl
  · subst h2; rfl
  · rw [Stacks.getD_nil_of_le, Stacks.getD_nil_of_le] <;>
      simp only [List.length_cons, List.length_nil] <;> omega

/-- Seen through the placement `outMap2 k₁`, the layout of `[x, a, b, c]` over `K` stacks with `u`
written on stack `5` holds `b` and `u` followed by empty strings: the input stacks of the
filtering procedure. -/
theorem update_layout_outMap2 {K : ℕ} (hK : 7 ≤ K) (k₁ n : ℕ) (x a b c u : BitString)
    (hn : outMap2 k₁ n < K) :
    Function.update (Stacks.layout K [x, a, b, c]) ⟨5, by omega⟩ u ⟨outMap2 k₁ n, hn⟩ =
      [b, u].getD n [] := by
  rcases n with _ | _ | _ | n
  · simp [outMap2, Stacks.layout]
  · simp [outMap2]
  · simp [outMap2, Stacks.layout]
  · have hv : outMap2 k₁ (n + 1 + 1 + 1) = 7 + k₁ + (n + 1 + 1 + 1) := by simp [outMap2]
    simp only [hv, Function.update_apply, Fin.mk.injEq, Stacks.layout]
    rw [ite_eq_right (show ¬ (7 + k₁ + (n + 1 + 1 + 1) = 5) by omega),
      Stacks.getD_nil_of_le, Stacks.getD_nil_of_le] <;>
      simp only [List.length_cons, List.length_nil] <;> omega

/-- Writing `u`, `v` on the stacks `5`, `6` of the layout of `[a, b, c, d]`, then `w` on stack `4`,
and clearing `5` and `6` again leaves the layout of `[a, b, c, d, w]`. -/
theorem Stacks.layout_update_clear {K : ℕ} (hK : 7 ≤ K) (a b c d u v w : BitString) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Stacks.layout K [a, b, c, d]) ⟨5, by omega⟩ u) ⟨6, by omega⟩ v) ⟨4, by omega⟩ w)
      ⟨5, by omega⟩ []) ⟨6, by omega⟩ [] = Stacks.layout K [a, b, c, d, w] := by
  funext ⟨n, hn⟩
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · simp [Stacks.layout]
  · simp [Stacks.layout]
  · simp [Stacks.layout]
  · simp [Stacks.layout]
  · simp [Stacks.layout]
  · simp [Stacks.layout]
  · simp [Stacks.layout]
  · simp only [Function.update_apply, Fin.mk.injEq, Stacks.layout]
    rw [ite_eq_right (show ¬ (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 6) by omega),
      ite_eq_right (show ¬ (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 5) by omega),
      ite_eq_right (show ¬ (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 4) by omega),
      ite_eq_right (show ¬ (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 6) by omega),
      ite_eq_right (show ¬ (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 5) by omega),
      Stacks.getD_nil_of_le, Stacks.getD_nil_of_le] <;>
      simp only [List.length_cons, List.length_nil] <;> omega

/-- The oracle of a position: removing from `LR` the strings of `LX` selected by `S ⊆ LX` leaves
exactly the strings of `LR` outside `S`. -/
theorem filter_notMem_select_eq {LX LR : List BitString} {S : Finset BitString}
    (hS : S ⊆ LX.toFinset) :
    {z | z ∈ LR.filter fun z => decide (z ∉ LX.filter fun z => decide (z ∈ S))} =
      {z | z ∈ LR ∧ z ∉ S} := by
  ext z
  simp only [Set.mem_ofPred_eq, List.mem_filter, decide_eq_true_eq, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hzS => h2 (List.mem_toFinset.1 (hS hzS)) hzS⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun _ hzS => h2 hzS⟩

/-- **The outcome of a position.**  For the clocked machine `(c, e)` there is a
statement which, started on `[x, encList LX, encList LR, posBits LX S]` (stacks `0`–`3`, all other
stacks empty; `LX` duplicate-free, `S ⊆ LX`), adds on stack `4` the bit
`[(c, e) accepts x with the oracle {z ∈ LR | z ∉ S}]`, everything else unchanged, within space
`C · (|x| + clock e |x| + |encList LX| + |encList LR| + 1) ^ 2`.
Proof: select `LS = LX.filter (· ∈ S)` (`exists_selectStmt`), filter `L = LR.filter (· ∉ LS)`
(`exists_filterNotMemStmt`), run the machine with the oracle `L` (`exists_simStmt`), each
inlined by `Exec.call` (`Exec.call_layout`) along injective placements (`outMap1`, `outMap2`, and a
placement of the three designated stacks of the simulation), then clear `LS` and `L`;
`{z | z ∈ L}` is `{z ∈ LR | z ∉ S}` because `S ⊆ LX` (`filter_notMem_select_eq`). -/
theorem exists_outStmt (c : OTMCode) (e : ℕ) :
    ∃ (k : ℕ) (s : Stmt k) (C : ℕ), 5 ≤ k ∧
        ∀ (x : BitString) (LX LR : List BitString) (S : Finset BitString),
      LX.Nodup → S ⊆ LX.toFinset →
      Exec s (Stacks.layout k [x, Stacks.encList LX, Stacks.encList LR, Stacks.posBits LX S])
        (Stacks.layout k [x, Stacks.encList LX, Stacks.encList LR, Stacks.posBits LX S,
          [by classical exact decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x)]])
        (C * (x.length + clock e x.length + (Stacks.encList LX).length +
          (Stacks.encList LR).length + 1) ^ 2) := by
  classical
  obtain ⟨k₁, s₁, C₁, hk₁, hsel⟩ := exists_selectStmt
  obtain ⟨k₂, s₂, C₂, hk₂, hfil⟩ := exists_filterNotMemStmt
  obtain ⟨k₃, s₃, inp, ora, out, C₃, hio, hiu, hou, hsim⟩ := exists_simStmt c e
  -- the placements
  let K := 7 + k₁ + k₂ + k₃
  let f₁ : Fin k₁ → Fin K := fun i => ⟨outMap1 i.val, by unfold outMap1; split_ifs <;> omega⟩
  let f₂ : Fin k₂ → Fin K := fun i => ⟨outMap2 k₁ i.val, by unfold outMap2; split_ifs <;> omega⟩
  let f₃ : Fin k₃ → Fin K := fun i => if i = inp then ⟨0, by omega⟩ else if i = ora then
    ⟨6, by omega⟩ else if i = out then ⟨4, by omega⟩ else ⟨7 + k₁ + k₂ + i.val, by omega⟩
  have hf₁ : Function.Injective f₁ := fun a b h =>
    Fin.ext (outMap1_injective (congrArg Fin.val h))
  have hf₂ : Function.Injective f₂ := fun a b h =>
    Fin.ext (outMap2_injective k₁ (congrArg Fin.val h))
  have hf₃ : Function.Injective f₃ := by
    intro a b h
    simp only [f₃] at h
    split_ifs at h <;> simp_all [Fin.ext_iff] <;> omega
  refine ⟨K, Stmt.seqs [s₁.rename f₁, s₂.rename f₂, s₃.rename f₃, Stmt.clear ⟨5, by omega⟩,
    Stmt.clear ⟨6, by omega⟩], 2 * C₁ + 2 * C₂ + C₃ + 5, by omega, ?_⟩
  intro x LX LR S hnd hS
  have hK7 : 7 ≤ K := by omega
  set LS := LX.filter fun z => decide (z ∈ S)
  set L := LR.filter fun z => decide (z ∉ LS)
  set τ₀ := Stacks.layout K [x, Stacks.encList LX, Stacks.encList LR, Stacks.posBits LX S]
    with hτ₀
  -- step 1: select the position
  have e₁ : Exec (s₁.rename f₁) τ₀ (Function.update τ₀ ⟨5, by omega⟩ (Stacks.encList LS))
      (C₁ * ((Stacks.encList LX).length + LX.length + 1) + τ₀.space) :=
    Exec.call_layout hf₁ (hsel LX S) hk₁ (fun r => getD_outMap1 x _ _ _ r.val)
  set τ₁ := Function.update τ₀ ⟨5, by omega⟩ (Stacks.encList LS) with hτ₁
  -- step 2: filter the random queries
  have e₂ : Exec (s₂.rename f₂) τ₁ (Function.update τ₁ ⟨6, by omega⟩ (Stacks.encList L))
      (C₂ * ((Stacks.encList LR).length + (Stacks.encList LS).length + 1) +
        Stacks.space τ₁) :=
    Exec.call_layout hf₂ (hfil LR LS) hk₂
      (fun r => update_layout_outMap2 hK7 k₁ r.val x _ _ _ _ _)
  set τ₂ := Function.update τ₁ ⟨6, by omega⟩ (Stacks.encList L) with hτ₂
  -- step 3: run the machine with the oracle `L`
  obtain ⟨b, hb, hsimx⟩ := hsim x L
  have e₃ : Exec (s₃.rename f₃) τ₂ (Function.update τ₂ ⟨4, by omega⟩ [b])
      (C₃ * (x.length + clock e x.length + (Stacks.encList L).length + 1) + Stacks.space τ₂) := by
    have hc : (fun r => τ₂ (f₃ r)) =
        Function.update (Function.update (fun _ => []) inp x) ora (Stacks.encList L) := by
      funext r
      by_cases h1 : r = inp
      · subst h1
        simp [f₃, hτ₂, hτ₁, hτ₀, Stacks.layout, hio]
      · by_cases h2 : r = ora
        · subst h2
          simp [f₃, hτ₂, h1]
        · by_cases h3 : r = out
          · subst h3
            simp [f₃, hτ₂, hτ₁, hτ₀, h1, h2, Stacks.layout]
          · simp only [f₃, h1, h2, h3, ite_false, hτ₂, hτ₁, hτ₀, Function.update_apply,
              Fin.mk.injEq, Stacks.layout]
            rw [ite_eq_right (show ¬ (7 + k₁ + k₂ + r.val = 6) by omega),
              ite_eq_right (show ¬ (7 + k₁ + k₂ + r.val = 5) by omega),
              Stacks.getD_nil_of_le]
            simp only [List.length_cons, List.length_nil]
            omega
    rw [← hc] at hsimx
    have r₃ := Exec.call hf₃ hsimx
    have hf₃out : f₃ out = ⟨4, by omega⟩ := by simp [f₃, hiu.symm, hou.symm]
    rwa [hf₃out] at r₃
  set τ₃ := Function.update τ₂ ⟨4, by omega⟩ [b] with hτ₃
  -- steps 4, 5: clean up
  have e₄ := Stmt.exec_clear (⟨5, by omega⟩ : Fin K) _ τ₃ rfl
  set τ₄ := Function.update τ₃ ⟨5, by omega⟩ [] with hτ₄
  have e₅ := Stmt.exec_clear (⟨6, by omega⟩ : Fin K) _ τ₄ rfl
  -- space bookkeeping
  have hLXe := Stacks.length_le_length_encList LX
  have hLSe : (Stacks.encList LS).length ≤ (Stacks.encList LX).length :=
    Stacks.length_encList_filter_le LX _
  have hLe : (Stacks.encList L).length ≤ (Stacks.encList LR).length :=
    Stacks.length_encList_filter_le LR _
  have hsp0 : Stacks.space τ₀ = x.length + (Stacks.encList LX).length +
      (Stacks.encList LR).length + LX.length := by
    rw [hτ₀, Stacks.space_layout _ (by simp only [List.length_cons, List.length_nil]; omega)]
    simp [Stacks.posBits]
    ring
  have hsp1 : Stacks.space τ₁ = Stacks.space τ₀ + (Stacks.encList LS).length :=
    Stacks.space_update_nil _ _ _ (by rw [hτ₀]; rfl)
  have hsp2 : Stacks.space τ₂ = Stacks.space τ₁ + (Stacks.encList L).length :=
    Stacks.space_update_nil _ _ _ (by rw [hτ₁, Function.update_of_ne (by simp), hτ₀]; rfl)
  have hsp3 : Stacks.space τ₃ = Stacks.space τ₂ + 1 :=
    Stacks.space_update_nil _ _ _ (by
      rw [hτ₂, Function.update_of_ne (by simp), hτ₁, Function.update_of_ne (by simp), hτ₀]; rfl)
  have hsp4 := e₄.space_le.2
  have hsp5 := e₅.space_le.2
  set A := x.length + clock e x.length + (Stacks.encList LX).length +
    (Stacks.encList LR).length + 1 with hA
  have hA1 : 1 ≤ A := by omega
  have hfin : ∀ t, t ≤ (2 * C₁ + 2 * C₂ + C₃ + 5) * A →
      t ≤ (2 * C₁ + 2 * C₂ + C₃ + 5) * A ^ 2 := fun t ht =>
    ht.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _))
  have b₁ : C₁ * ((Stacks.encList LX).length + LX.length + 1) + Stacks.space τ₀ ≤
      (2 * C₁ + 2 * C₂ + C₃ + 5) * A := by
    have := Nat.mul_le_mul_left C₁
        (show (Stacks.encList LX).length + LX.length + 1 ≤ 2 * A by omega)
    nlinarith
  have b₂ : C₂ * ((Stacks.encList LR).length + (Stacks.encList LS).length + 1) +
      Stacks.space τ₁ ≤ (2 * C₁ + 2 * C₂ + C₃ + 5) * A := by
    have := Nat.mul_le_mul_left C₂
      (show (Stacks.encList LR).length + (Stacks.encList LS).length + 1 ≤ 2 * A by omega)
    nlinarith
  have b₃ : C₃ * (x.length + clock e x.length + (Stacks.encList L).length + 1) +
      Stacks.space τ₂ ≤ (2 * C₁ + 2 * C₂ + C₃ + 5) * A := by
    have := Nat.mul_le_mul_left C₃
      (show x.length + clock e x.length + (Stacks.encList L).length + 1 ≤ A by omega)
    nlinarith
  have b₄ : Stacks.space τ₃ ≤ (2 * C₁ + 2 * C₂ + C₃ + 5) * A := by nlinarith
  -- the outcome bit
  have hset : {z | z ∈ L} = {z | z ∈ LR ∧ z ∉ S} := filter_notMem_select_eq hS
  have hbd : b = decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x) := by
    rw [Bool.eq_iff_iff, hb, decide_eq_true_iff, hset]
  refine Stmt.exec_of_eq (.seq (e₁.mono (hfin _ b₁)) (.seq (e₂.mono (hfin _ b₂))
    (.seq (e₃.mono (hfin _ b₃)) (.seq (e₄.mono (hfin _ b₄)) (.seq (e₅.mono (hfin _ (hsp4.trans b₄)))
      (.skip (hfin _ ((hsp5.trans hsp4).trans b₄)))))))) ?_
  rw [hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, hbd]
  exact Stacks.layout_update_clear hK7 _ _ _ _ _ _ _

/-- Where the stacks of the outcome procedure are placed inside the evaluation program:
`0 ↦ 0` (`x`), `1 ↦ 1` (board), `2 ↦ 4` (`LR`), `3 ↦ 6` (position), `4 ↦ 7` (outcome bit), and the
work stacks after the `8 + kD` stacks of the search. -/
def outMap (kD n : ℕ) : ℕ :=
  if n = 0 then 0 else if n = 1 then 1 else if n = 2 then 4 else if n = 3 then 6
  else if n = 4 then 7 else 8 + kD + (n - 5)

/-- The stack placement function `outMap` maps indices strictly below its source arity `ko` to
indices strictly below its target arity `8 + kD + ko`. -/
theorem outMap_lt (kD ko n : ℕ) (hn : n < ko) (hko : 5 ≤ ko) : outMap kD n < 8 + kD + ko := by
  unfold outMap; split_ifs <;> omega

/-- The stack placement function `outMap` for the outcome procedure is injective. -/
theorem outMap_injective (kD : ℕ) : Function.Injective (outMap kD) := by
  intro a b h; unfold outMap at h; split_ifs at h <;> omega

/-- **Evaluation of the game on prepared data.**  For the clocked machine `(c, e)`
there is a statement which, started on the stacks
`[x, encList LX, encList cs, eb, encList LR]` (stacks `0`–`4`, all other stacks empty), where
`LX` is duplicate-free, `cs` lists the costs `cost z` of the strings `z` of `LX` (same order) as bit
strings of width `W`, `eb` is a width-`W` budget, and nothing overflows `W` bits, adds on stack `5`
the bit `gameValB LX.toFinset cost (binVal eb) out` for the outcomes
`out S = [ (c, e) accepts x with the oracle {z ∈ LR | z ∉ S} ]`, everything else unchanged,
within space `C · (size of the data + clock e |x| + 1) ^ 2`.
Proof: the search `exists_dfsStmt` with the outcome procedure `exists_outStmt` inlined along
`outMap` (its stacks `x`, board, `LR`, position, outcome go to `0, 1, 4, 6, 7`, its work stacks
after those of the search); the contract of the outcome procedure is checked from
`Exec.rename_of_comp`. -/
theorem exists_gameStmt (c : OTMCode) (e : ℕ) :
    ∃ (k : ℕ) (s : Stmt k) (C : ℕ), 6 ≤ k ∧
        ∀ (x : BitString) (LX LR cs : List BitString) (eb : BitString) (W : ℕ)
      (cost : BitString → ℕ), LX.Nodup → cs.length = LX.length → (∀ b ∈ cs, b.length = W) →
      eb.length = W → (∀ i < LX.length, binVal (cs.getD i []) = cost (LX.getD i [])) →
      binVal eb + (LX.map cost).sum < 2 ^ W →
      Exec s (Stacks.layout k [x, Stacks.encList LX, Stacks.encList cs, eb, Stacks.encList LR])
        (Stacks.layout k [x, Stacks.encList LX, Stacks.encList cs, eb, Stacks.encList LR,
          [gameValB LX.toFinset cost (binVal eb)
            (fun S => by classical exact decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x))]])
        (C * (x.length + clock e x.length + (Stacks.encList LX).length +
          (Stacks.encList cs).length + eb.length + (Stacks.encList LR).length + 1) ^ 2) := by
  classical
  obtain ⟨kD, dfs, Cd, hdfs⟩ := exists_dfsStmt
  obtain ⟨ko, so, Co, hko, hout⟩ := exists_outStmt c e
  have hf : Function.Injective (fun i : Fin ko =>
      (⟨outMap kD i.val, outMap_lt kD ko i.val i.isLt hko⟩ : Fin (8 + kD + ko))) :=
    fun a b h => Fin.ext (outMap_injective kD (congrArg Fin.val h))
  refine ⟨8 + kD + ko, dfs (8 + kD + ko) (so.rename fun i =>
    ⟨outMap kD i.val, outMap_lt kD ko i.val i.isLt hko⟩), 1 + Cd + Co, by omega, ?_⟩
  intro x LX LR cs eb W cost hnd hcs hW heb hcost hov
  set σ := Stacks.layout (8 + kD + ko)
    [x, Stacks.encList LX, Stacks.encList cs, eb, Stacks.encList LR] with hσ
  set B := Co * (x.length + clock e x.length + (Stacks.encList LX).length +
    (Stacks.encList LR).length + 1) ^ 2 with hB
  have hcontract : ∀ (τ : Stacks (8 + kD + ko)) (S : Finset BitString), S ⊆ LX.toFinset →
      τ ⟨1, by omega⟩ = Stacks.encList LX → τ ⟨6, by omega⟩ = Stacks.posBits LX S →
      τ ⟨7, by omega⟩ = [] → τ ⟨0, by omega⟩ = σ ⟨0, by omega⟩ →
      τ ⟨4, by omega⟩ = σ ⟨4, by omega⟩ → (∀ j : Fin (8 + kD + ko), 8 + kD ≤ j.val → τ j = σ j) →
      Exec (so.rename fun i => ⟨outMap kD i.val, outMap_lt kD ko i.val i.isLt hko⟩) τ
        (Function.update τ ⟨7, by omega⟩
          [decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x)]) (τ.space + B) := by
    intro τ S hS h1 h6 h7 h0 h4 hpriv
    have ho := hout x LX LR S hnd hS
    have hcomp : (fun r : Fin ko => τ ⟨outMap kD r.val, outMap_lt kD ko r.val r.isLt hko⟩) =
        Stacks.layout ko [x, Stacks.encList LX, Stacks.encList LR, Stacks.posBits LX S] := by
      funext r
      obtain ⟨n, hn⟩ := r
      rcases n with _ | _ | _ | _ | _ | n
      · simpa [outMap, Stacks.layout, hσ] using h0
      · simpa [outMap, Stacks.layout] using h1
      · simpa [outMap, Stacks.layout, hσ] using h4
      · simpa [outMap, Stacks.layout] using h6
      · simpa [outMap, Stacks.layout] using h7
      · have := hpriv ⟨8 + kD + n, by omega⟩ (by simp)
        simp only [outMap, Stacks.layout] at this ⊢
        simp only [show n + 1 + 1 + 1 + 1 + 1 ≠ 0 by omega, show n + 1 + 1 + 1 + 1 + 1 ≠ 1 by omega,
          show n + 1 + 1 + 1 + 1 + 1 ≠ 2 by omega, show n + 1 + 1 + 1 + 1 + 1 ≠ 3 by omega,
          show n + 1 + 1 + 1 + 1 + 1 ≠ 4 by omega, ite_false,
          show n + 1 + 1 + 1 + 1 + 1 - 5 = n by omega]
        rw [this, hσ]
        simp only [Stacks.layout]
        rw [Stacks.getD_nil_of_le (by simp only [List.length_cons, List.length_nil]; omega),
          Stacks.getD_nil_of_le (by simp only [List.length_cons, List.length_nil]; omega)]
    rw [← hcomp] at ho
    have r := Exec.rename_of_comp hf ho
    have hext : Function.extend (fun i : Fin ko =>
        (⟨outMap kD i.val, outMap_lt kD ko i.val i.isLt hko⟩ : Fin (8 + kD + ko)))
        (Stacks.layout ko [x, Stacks.encList LX, Stacks.encList LR, Stacks.posBits LX S,
          [decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x)]]) τ =
        Function.update τ ⟨7, by omega⟩ [decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x)] := by
      funext j
      by_cases hj : ∃ i : Fin ko, (⟨outMap kD i.val, outMap_lt kD ko i.val i.isLt hko⟩ :
          Fin (8 + kD + ko)) = j
      · obtain ⟨i, rfl⟩ := hj
        rw [hf.extend_apply]
        have hc := congrFun hcomp i
        by_cases hi4 : i.val = 4
        · have e7 : (⟨outMap kD i.val, outMap_lt kD ko i.val i.isLt hko⟩ : Fin (8 + kD + ko)) =
              ⟨7, by omega⟩ := Fin.ext (by simp [outMap, hi4])
          rw [e7, Function.update_self]
          simp [Stacks.layout, hi4]
        · have ne7 : (⟨outMap kD i.val, outMap_lt kD ko i.val i.isLt hko⟩ : Fin (8 + kD + ko)) ≠
              ⟨7, by omega⟩ := by
            intro h
            have h' := congrArg Fin.val h
            simp only at h'
            exact hi4 (outMap_injective kD (h'.trans (by simp [outMap])))
          rw [Function.update_of_ne ne7, hc]
          simp only [Stacks.layout]
          obtain ⟨n, hn⟩ := i
          simp only at hi4
          rcases n with _ | _ | _ | _ | _ | n
          · rfl
          · rfl
          · rfl
          · rfl
          · exact absurd rfl hi4
          · rw [Stacks.getD_nil_of_le (by simp), Stacks.getD_nil_of_le (by simp)]
      · rw [Function.extend_apply' _ _ _ hj]
        have ne7 : j ≠ ⟨7, by omega⟩ := by
          rintro rfl
          exact hj ⟨⟨4, by omega⟩, Fin.ext (by simp [outMap])⟩
        rw [Function.update_of_ne ne7]
    rw [hext] at r
    exact r.mono (by have := Stacks.rest_le_space (fun i : Fin ko =>
      (⟨outMap kD i.val, outMap_lt kD ko i.val i.isLt hko⟩ : Fin (8 + kD + ko))) τ; omega)
  have hscr : ∀ j : Fin (8 + kD + ko), 8 ≤ j.val → j.val < 8 + kD → σ j = [] := by
    intro j hj1 _
    rw [hσ]
    simp only [Stacks.layout]
    exact Stacks.getD_nil_of_le (by simp only [List.length_cons, List.length_nil]; omega)
  have hd := hdfs (8 + kD + ko) (by omega)
    (so.rename fun i => ⟨outMap kD i.val, outMap_lt kD ko i.val i.isLt hko⟩) B
    (fun S => decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x)) LX cs eb W cost σ hnd hcs hW
    heb hcost hov hcontract σ (by rw [hσ]; rfl) (by rw [hσ]; rfl) (by rw [hσ]; rfl)
    (by rw [hσ]; rfl) (by rw [hσ]; rfl) (by rw [hσ]; rfl) hscr rfl rfl (fun _ _ => rfl)
  have hsp : σ.space = x.length + (Stacks.encList LX).length + (Stacks.encList cs).length +
      eb.length + (Stacks.encList LR).length := by
    rw [hσ, Stacks.space_layout _ (by simp only [List.length_cons, List.length_nil]; omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  have hLXle := Stacks.length_le_length_encList LX
  have hA : σ.space ≤ (x.length + clock e x.length + (Stacks.encList LX).length +
      (Stacks.encList cs).length + eb.length + (Stacks.encList LR).length + 1) ^ 2 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
  have hBd : Cd * (LX.length + W + 1) ^ 2 ≤ Cd * (x.length + clock e x.length +
      (Stacks.encList LX).length + (Stacks.encList cs).length + eb.length +
      (Stacks.encList LR).length + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hBo : B ≤ Co * (x.length + clock e x.length + (Stacks.encList LX).length +
      (Stacks.encList cs).length + eb.length + (Stacks.encList LR).length + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  refine Stmt.exec_of_eq (hd.mono (le_trans (Nat.add_le_add (Nat.add_le_add hA hBd) hBo)
    (le_of_eq (by ring)))) ?_
  funext j
  obtain ⟨n, hn⟩ := j
  rw [hσ]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [show (⟨0 + 1 + 1 + 1 + 1 + 1, hn⟩ : Fin (8 + kD + ko)) = ⟨5, by omega⟩ from rfl,
      Function.update_self]
    rfl
  · rw [Function.update_of_ne (by simp)]
    simp only [Stacks.layout]
    rw [Stacks.getD_nil_of_le (by simp only [List.length_cons, List.length_nil]; omega),
      Stacks.getD_nil_of_le (by simp only [List.length_cons, List.length_nil]; omega)]

/-- An exponential bound on the composed time cost of exponential space computations. -/
theorem pow_mul_sq_le (C₁ C₂ a : ℕ) (ha : 1 ≤ a) :
    C₂ * (2 ^ (C₁ * a)) ^ 2 ≤ 2 ^ ((C₂ + 2 * C₁ + 1) * a) := by
  have h1 : C₂ < 2 ^ C₂ := Nat.lt_two_pow_self
  have h2 : 2 ^ C₂ ≤ 2 ^ (C₂ * a) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h3 : (2 ^ (C₁ * a)) ^ 2 = 2 ^ (2 * C₁ * a) := by rw [← pow_mul]; ring_nf
  have h4 : 2 ^ ((C₂ + 2 * C₁ + 1) * a) = 2 ^ (C₂ * a) * 2 ^ (2 * C₁ * a) * 2 ^ a := by
    rw [← pow_add, ← pow_add]; ring_nf
  rw [h3, h4]
  have h5 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  calc C₂ * 2 ^ (2 * C₁ * a) ≤ 2 ^ (C₂ * a) * 2 ^ (2 * C₁ * a) :=
        Nat.mul_le_mul_right _ (h1.le.trans h2)
    _ ≤ 2 ^ (C₂ * a) * 2 ^ (2 * C₁ * a) * 2 ^ a := Nat.le_mul_of_pos_right _ h5

/-- Placement of a procedure whose designated stacks are `0, 1, 2`: they go to `a, b, c`, the
work stacks `n ≥ 3` to `base + n`. -/
def place3 (a b c base n : ℕ) : ℕ :=
  if n = 0 then a else if n = 1 then b else if n = 2 then c else base + n

/-- The stack placement function `place3` maps indices strictly below its source arity `k` to
indices strictly below its target arity `K`, provided all components are properly bounded. -/
theorem place3_lt {a b c base k K n : ℕ} (ha : a < K) (hb : b < K) (hc : c < K)
    (hK : base + k ≤ K) (hn : n < k) : place3 a b c base n < K := by
  unfold place3; split_ifs <;> omega

/-- The stack placement function `place3` is injective if the designated stacks are distinct and
placed before the work stacks block. -/
theorem place3_injective {a b c base : ℕ} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) (ha : a < base)
    (hb : b < base) (hc : c < base) : Function.Injective (place3 a b c base) := by
  intro x y h; unfold place3 at h; split_ifs at h <;> omega

/-- The stack placement function `place3` maps an index `n ≥ 3` to `base + n`. -/
theorem place3_ge (a b c base n : ℕ) :
    place3 a b c base (n + 1 + 1 + 1) = base + (n + 1 + 1 + 1) := by
  simp [place3]

/-- Decomposing the configuration of three strings on the first stacks. -/
theorem Stacks.layout_three' {k : ℕ} (a b v : BitString) (h1 : 1 < k) (h2 : 2 < k) :
    Stacks.layout k [a, b, v] =
      Function.update (Function.update (Stacks.layout k [a]) ⟨1, h1⟩ b) ⟨2, h2⟩ v := by
  rw [Stacks.layout_three a b v h2, show [a, b] = [a] ++ [b] from rfl,
    Stacks.layout_append [a] b h1]
  rfl

end Kolmogorov.RandomStrings
