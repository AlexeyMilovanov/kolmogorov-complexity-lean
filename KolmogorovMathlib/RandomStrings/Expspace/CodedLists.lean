/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.Routines

/-!
# Coded strings and lists on stacks

Self-delimiting codes of strings and lists of strings (`Stacks.encStr`, `Stacks.encList`), the
decoding of coded lists, and the 9-stack membership test of a string in a coded list
(`Stmt.memTest`), stated as procedure contracts to be inlined with `Exec.rename_of_comp`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-! #### Simulating the clocked machine and enumerating its query set (specifications)

Strings and lists of strings are stored on a stack through self-delimiting codes (`Stacks.encStr`,
`Stacks.encList`).  The two statements below are the machine-simulation components of the game
evaluator; they are stated as procedure contracts (inputs on designated stacks, all other stacks
empty before and after, the result on a designated stack), so that they can be inlined into the
evaluator with `Exec.rename_of_comp`. -/

/-- Self-delimiting code of a string: each bit `b` as `true, b`, then the end marker `false`. -/
def Stacks.encStr (z : BitString) : BitString := z.flatMap (fun b => [true, b]) ++ [false]

/-- Code of a list of strings: the concatenation of the codes of its elements. -/
def Stacks.encList (L : List BitString) : BitString := L.flatMap Stacks.encStr

/-- The length of the encoded string `Stacks.encStr z` is `2 * |z| + 1`. -/
theorem Stacks.length_encStr (z : BitString) : (Stacks.encStr z).length = 2 * z.length + 1 := by
  induction z with
  | nil => rfl
  | cons b z ih =>
    have e : Stacks.encStr (b :: z) = true :: b :: Stacks.encStr z := by simp [Stacks.encStr]
    rw [e, List.length_cons, List.length_cons, ih, List.length_cons]; ring

/-- The length of the encoded list `Stacks.encList L` is the sum of `2 * |z| + 1` for each
string `z` in `L`. -/
theorem Stacks.length_encList (L : List BitString) :
    (Stacks.encList L).length = (L.map fun z => 2 * z.length + 1).sum := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    simp only [Stacks.encList, List.flatMap_cons, List.length_append, Stacks.length_encStr,
      List.map_cons, List.sum_cons] at ih ⊢
    omega

/-! #### Decoding coded lists -/

namespace Stmt

variable {k : ℕ}

/-- The body of the decoding loop: move the marker `true` and the following bit `b` of `Lst` to
`Tmp`, and push `b` on `W`. -/
def decodeBody (Lst W Tmp : Fin k) : Stmt k :=
  .seq (moveBit Lst Tmp) (caseBit Lst fun b => .seq (moveBit Lst Tmp) (.push W b))

/-- Decode the first string of a coded list: `Lst = encStr z ++ rest` becomes `rest`, `z` is pushed
bit by bit on `W` (so `W := z.reverse ++ W`), and the code is moved, reversed, onto `Tmp`. -/
def decodeOne (Lst W Tmp : Fin k) : Stmt k :=
  .seq (.loop Lst isTrue (decodeBody Lst W Tmp)) (moveBit Lst Tmp)

/-- The execution of the decoding loop: moving bits from `Lst` onto `W` and the encoded markers onto
`Tmp` until reaching the end marker, using a maximum space bound of `σ.space + |z|`. -/
theorem exec_decodeLoop {Lst W Tmp : Fin k} (h1 : Lst ≠ W) (h2 : Lst ≠ Tmp) (h3 : W ≠ Tmp) :
    ∀ (z rest : BitString) (σ : Stacks k), σ Lst = z.flatMap (fun b => [true, b]) ++ false :: rest →
      Exec (.loop Lst isTrue (decodeBody Lst W Tmp)) σ
        (Function.update (Function.update (Function.update σ Lst (false :: rest)) W
          (z.reverse ++ σ W)) Tmp ((z.flatMap (fun b => [true, b])).reverse ++ σ Tmp))
        (σ.space + z.length)
  | [], rest, σ, hσ => by
    simp only [List.flatMap_nil, List.nil_append] at hσ
    refine exec_of_eq (.loopF (by simp [hσ, isTrue]) (by omega)) ?_
    funext j
    simp only [Function.update_apply, List.flatMap_nil, List.reverse_nil, List.nil_append]
    split_ifs <;> subst_vars <;> simp_all
  | b :: z, rest, σ, hσ => by
    have hσ' : σ Lst = true :: b :: (z.flatMap (fun b => [true, b]) ++ false :: rest) := by
      rw [hσ]; simp
    have e1 := exec_moveBit h2 hσ'
    have hL1 : (Function.update (Function.update σ Lst (b :: (z.flatMap (fun b => [true, b]) ++
        false :: rest))) Tmp (true :: σ Tmp)) Lst =
        b :: (z.flatMap (fun b => [true, b]) ++ false :: rest) := by
      rw [Function.update_of_ne h2, Function.update_self]
    have e2 := exec_moveBit h2 hL1
    rw [Function.update_self] at e2
    set σ2 := Function.update (Function.update (Function.update (Function.update σ Lst
      (b :: (z.flatMap (fun b => [true, b]) ++ false :: rest))) Tmp (true :: σ Tmp)) Lst
      (z.flatMap (fun b => [true, b]) ++ false :: rest)) Tmp (b :: true :: σ Tmp) with hσ2
    have hW2 : σ2 W = σ W := by
      rw [hσ2, Function.update_of_ne h3, Function.update_of_ne h1.symm, Function.update_of_ne h3,
        Function.update_of_ne h1.symm]
    have e3 := Exec.push (r := W) (b := b) (σ := σ2) (S := σ.space + (b :: z).length)
      (by have := e1.space_le.2; have := e2.space_le.2; simp only [List.length_cons]; omega)
    rw [hW2] at e3
    have hbody : Exec (decodeBody Lst W Tmp) σ (Function.update σ2 W (b :: σ W))
        (σ.space + (b :: z).length) := by
      unfold decodeBody
      refine .seq (e1.mono (by simp)) ?_
      rw [exec_caseBit hL1]
      exact .seq (e2.mono (e1.space_le.2.trans (by simp))) e3
    have hσ3 : (Function.update σ2 W (b :: σ W)) Lst = z.flatMap (fun b => [true, b]) ++
        false :: rest := by
      rw [Function.update_of_ne h1, hσ2, Function.update_of_ne h2, Function.update_self]
    have ih := exec_decodeLoop h1 h2 h3 z rest _ hσ3
    have sp3 : Stacks.space (Function.update σ2 W (b :: σ W)) ≤ σ.space + 1 := by
      have := Stacks.space_update_cons σ2 W b
      rw [hW2] at this
      have := e1.space_le.2; have := e2.space_le.2
      omega
    refine .loopT (by simp [hσ', isTrue]) hbody
      (exec_of_eq (ih.mono (by simp only [List.length_cons]; omega)) ?_)
    funext j
    simp only [hσ2, Function.update_apply, List.reverse_cons, List.flatMap_cons,
      List.reverse_append, List.append_assoc, List.singleton_append]
    split_ifs <;> subst_vars <;> simp_all

/-- Decoding a single string from a coded list: moving it from `Lst` onto `W` in reverse, and moving
its encoded form onto `Tmp` in reverse, while remaining within a space bound of `σ.space + |z|`. -/
theorem exec_decodeOne {Lst W Tmp : Fin k} (h1 : Lst ≠ W) (h2 : Lst ≠ Tmp) (h3 : W ≠ Tmp)
    {z rest : BitString} {σ : Stacks k} (hσ : σ Lst = Stacks.encStr z ++ rest) :
    Exec (decodeOne Lst W Tmp) σ
      (Function.update (Function.update (Function.update σ Lst rest) W (z.reverse ++ σ W)) Tmp
        ((Stacks.encStr z).reverse ++ σ Tmp)) (σ.space + z.length) := by
  have hσ' : σ Lst = z.flatMap (fun b => [true, b]) ++ false :: rest := by
    rw [hσ, Stacks.encStr]; simp
  have e1 := exec_decodeLoop h1 h2 h3 z rest σ hσ'
  have hL : (Function.update (Function.update (Function.update σ Lst (false :: rest)) W
      (z.reverse ++ σ W)) Tmp ((z.flatMap (fun b => [true, b])).reverse ++ σ Tmp)) Lst =
      false :: rest := by
    rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
  have e2 := exec_moveBit h2 hL
  refine exec_of_eq (.seq e1 (e2.mono e1.space_le.2)) ?_
  funext j
  simp only [Function.update_apply, Stacks.encStr, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append]
  split_ifs <;> subst_vars <;> simp_all

/-- Set the one-bit flag on `F` to `true`. -/
def setFlag (F : Fin k) : Stmt k := .seq (.pop F) (.push F true)

/-- Execution of `setFlag`: pops a bit from stack `F` and pushes `true`, preserving initial
space. -/
theorem exec_setFlag {F : Fin k} {σ : Stacks k} {f : Bool} (hF : σ F = [f]) :
    Exec (setFlag F) σ (Function.update σ F [true]) σ.space := by
  have s1 := space_update_of_cons hF
  have e1 := exec_pop_cons hF (S := σ.space) le_rfl
  have e2 := Exec.push (r := F) (b := true) (σ := Function.update σ F []) (S := σ.space)
    (by omega)
  rw [Function.update_self, Function.update_idem] at e2
  exact .seq e1 e2

end Stmt

/-! #### Membership of a string in a coded list (a 9-stack procedure, to be inlined with
`Exec.rename_of_comp`): stack `0` holds the string `Z`, stack `1` the code `encList L`, the flag
`[decide (Z ∈ L)]` is left on stack `2`; stacks `3`–`8` are work stacks. -/

/-- One step: decode the first string `z` of the list (onto `3`, its code onto `5`), copy it in
order to `4`, compare it with `Z` (result on `8`), update the flag, and clean up. -/
def Stmt.memStep : Stmt 9 :=
  Stmt.seqs [Stmt.decodeOne 1 3 5, Stmt.moveAll 3 4, Stmt.eqTest 4 0 6 7 8,
    Stmt.caseBit 8 (fun g => if g then Stmt.setFlag 2 else .skip), .pop 8, Stmt.clear 4]

/-- The membership test. -/
def Stmt.memTest : Stmt 9 :=
  Stmt.seqs [.push 2 false, .loop 1 Option.isSome Stmt.memStep, Stmt.moveAll 5 1]

/-- Execution of `memStep`: pops an encoded string from stack `1`, tests if it is equal to
the query string on stack `0`, updates the boolean flag on stack `2` with the disjunction,
and stores the reversed encoded string on stack `5`. -/
theorem Stmt.exec_memStep {σ : Stacks 9} {z rest : BitString} {f : Bool}
    (h1 : σ 1 = Stacks.encStr z ++ rest) (h2 : σ 2 = [f]) (h3 : σ 3 = []) (h4 : σ 4 = [])
    (h6 : σ 6 = []) (h7 : σ 7 = []) (h8 : σ 8 = []) :
    Exec Stmt.memStep σ
      (Function.update (Function.update (Function.update σ 1 rest) 5
        ((Stacks.encStr z).reverse ++ σ 5)) 2 [f || decide (z = σ 0)])
      (σ.space + z.length + 1) := by
  have e1 := Stmt.exec_decodeOne (Lst := 1) (W := 3) (Tmp := 5) (by decide) (by decide)
    (by decide) h1
  rw [h3, List.append_nil] at e1
  have sp1 := e1.space_le.2
  have e2 := Stmt.exec_moveAll (by decide : (3 : Fin 9) ≠ 4) z.reverse
    (Function.update (Function.update (Function.update σ 1 rest) 3 z.reverse) 5
      ((Stacks.encStr z).reverse ++ σ 5)) (by simp)
  have sp2 := e2.space_le.2
  have e2' : Exec (Stmt.moveAll 3 4) (Function.update (Function.update (Function.update σ 1 rest)
      3 z.reverse) 5 ((Stacks.encStr z).reverse ++ σ 5))
      (Function.update (Function.update (Function.update σ 1 rest) 5
        ((Stacks.encStr z).reverse ++ σ 5)) 4 z)
      (Stacks.space (Function.update (Function.update (Function.update σ 1 rest)
        3 z.reverse) 5 ((Stacks.encStr z).reverse ++ σ 5))) := by
    refine exec_of_eq e2 ?_
    funext j
    simp only [Function.update_apply, List.reverse_reverse]
    split_ifs <;> subst_vars <;> simp_all
  set σ2 := Function.update (Function.update (Function.update σ 1 rest) 5
        ((Stacks.encStr z).reverse ++ σ 5)) 4 z with hσ2
  have sp2' := e2'.space_le.2
  have e3 := Stmt.exec_eqTest (A := 4) (B := 0) (tA := 6) (tB := 7) (F := 8) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (σ := σ2) (by simp [hσ2, h6]) (by simp [hσ2, h7]) (by simp [hσ2, h8])
  have h40 : decide (σ2 4 = σ2 0) = decide (z = σ 0) := by simp [hσ2]
  rw [h40] at e3
  have sp3 := e3.space_le.2
  have h83 : (Function.update σ2 8 [decide (z = σ 0)]) 8 = [decide (z = σ 0)] :=
    Function.update_self _ _ _
  have h23 : (Function.update σ2 8 [decide (z = σ 0)]) 2 = [f] := by simp [hσ2, h2]
  have e4 : Exec (Stmt.caseBit 8 (fun g => if g then Stmt.setFlag 2 else .skip))
      (Function.update σ2 8 [decide (z = σ 0)])
      (Function.update (Function.update σ2 8 [decide (z = σ 0)]) 2 [f || decide (z = σ 0)])
      (Stacks.space (Function.update σ2 8 [decide (z = σ 0)])) := by
    rw [Stmt.exec_caseBit h83]
    cases hg : decide (z = σ 0)
    · simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      rw [hg] at h23
      rw [← h23, Function.update_eq_self]
      exact .skip le_rfl
    · simp only [Bool.or_true, ↓reduceIte]
      rw [hg] at h23
      exact Stmt.exec_setFlag h23
  have sp4 := e4.space_le.2
  have h84 : (Function.update (Function.update σ2 8 [decide (z = σ 0)]) 2
      [f || decide (z = σ 0)]) 8 = [decide (z = σ 0)] := by simp
  have e5 := Stmt.exec_pop_cons h84 (S := σ.space + z.length + 1) (by omega)
  have sp5 := e5.space_le.2
  have e6 := Stmt.exec_clear 4 _ (Function.update (Function.update (Function.update σ2 8
    [decide (z = σ 0)]) 2 [f || decide (z = σ 0)]) 8 []) rfl
  have sp6 := e6.space_le.2
  refine exec_of_eq (.seq (e1.mono (by omega))
    (.seq (e2'.mono (by omega))
      (.seq (e3.mono (by omega))
        (.seq (e4.mono (by omega))
          (.seq e5
            (.seq (e6.mono (by omega)) (.skip (by omega)))))))) ?_
  funext j
  simp only [hσ2, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- Execution of `memLoop`: iterates `memStep` over the coded list on stack `1`,
accumulating on stack `2` a boolean flag indicating if any tested string matched stack `0`,
and moves the parsed strings to stack `5`. -/
theorem Stmt.exec_memLoop (S : ℕ) : ∀ (L : List BitString) (σ : Stacks 9) (f : Bool),
    σ 1 = Stacks.encList L → σ 2 = [f] → σ 3 = [] → σ 4 = [] → σ 6 = [] → σ 7 = [] →
    σ 8 = [] → σ.space + (Stacks.encList L).length + 1 ≤ S →
    Exec (.loop 1 Option.isSome Stmt.memStep) σ
      (Function.update (Function.update (Function.update σ 1 []) 5
        ((Stacks.encList L).reverse ++ σ 5)) 2 [f || decide (σ 0 ∈ L)]) S
  | [], σ, f, h1, h2, h3, h4, h6, h7, h8, hS => by
    simp only [Stacks.encList, List.flatMap_nil] at h1
    refine exec_of_eq (.loopF (by simp [h1]) (by omega)) ?_
    funext j
    simp only [Function.update_apply, Stacks.encList, List.flatMap_nil, List.reverse_nil,
      List.nil_append, List.not_mem_nil, decide_false, Bool.or_false]
    split_ifs <;> subst_vars <;> simp_all
  | z :: L, σ, f, h1, h2, h3, h4, h6, h7, h8, hS => by
    have h1' : σ 1 = Stacks.encStr z ++ Stacks.encList L := by rw [h1]; simp [Stacks.encList]
    have hlen : (Stacks.encList (z :: L)).length =
        (Stacks.encStr z).length + (Stacks.encList L).length := by
      simp [Stacks.encList]
    have hz := Stacks.length_encStr z
    have e1 := Stmt.exec_memStep h1' h2 h3 h4 h6 h7 h8
    set σ' := Function.update (Function.update (Function.update σ 1 (Stacks.encList L)) 5
        ((Stacks.encStr z).reverse ++ σ 5)) 2 [f || decide (z = σ 0)] with hσ'
    have hsp : Stacks.space σ' ≤ σ.space := by
      have s1 := σ.space_update 1 (Stacks.encList L)
      have s2 := Stacks.space_update (Function.update σ 1 (Stacks.encList L)) 5
        ((Stacks.encStr z).reverse ++ σ 5)
      have s3 := Stacks.space_update (Function.update (Function.update σ 1 (Stacks.encList L)) 5
        ((Stacks.encStr z).reverse ++ σ 5)) 2 [f || decide (z = σ 0)]
      have a1 : (Function.update σ 1 (Stacks.encList L)) 5 = σ 5 := by simp
      have a2 : (Function.update (Function.update σ 1 (Stacks.encList L)) 5
          ((Stacks.encStr z).reverse ++ σ 5)) 2 = [f] := by simp [h2]
      rw [a1] at s2
      rw [a2] at s3
      rw [h1', List.length_append] at s1
      simp only [List.length_append, List.length_reverse, List.length_cons,
        List.length_nil] at s2 s3
      rw [hσ']
      omega
    have ih := exec_memLoop S L σ' (f || decide (z = σ 0)) (by simp [hσ']) (by simp [hσ'])
      (by simp [hσ', h3]) (by simp [hσ', h4]) (by simp [hσ', h6]) (by simp [hσ', h7])
      (by simp [hσ', h8]) (by omega)
    have hflag : ((f || decide (z = σ 0)) || decide (σ' 0 ∈ L)) =
        (f || decide (σ 0 ∈ z :: L)) := by
      have h0 : σ' 0 = σ 0 := by simp [hσ']
      rw [h0, Bool.or_assoc]
      congr 1
      by_cases hz : σ 0 = z
      · subst hz; simp
      · have : z ≠ σ 0 := fun h => hz h.symm
        simp [hz, this]
    rw [hflag] at ih
    refine .loopT (by rw [h1']; cases z <;> simp [Stacks.encStr]) (e1.mono (by omega))
      (exec_of_eq ih ?_)
    funext j
    simp only [hσ', Function.update_apply, Stacks.encList, List.flatMap_cons, List.reverse_append,
      List.append_assoc]
    split_ifs <;> subst_vars <;> simp_all [Stacks.encList]

/-- **Membership test.**  On 9 stacks, with the string `Z` on stack `0`, the code
`encList L` on stack `1` and stacks `2`–`8` empty, `memTest` leaves `[decide (Z ∈ L)]` on
stack `2` and restores everything else, within the initial space plus `|encList L| + 2`. -/
theorem Stmt.exec_memTest {σ : Stacks 9} {L : List BitString} (h1 : σ 1 = Stacks.encList L)
    (h2 : σ 2 = []) (h3 : σ 3 = []) (h4 : σ 4 = []) (h5 : σ 5 = []) (h6 : σ 6 = [])
    (h7 : σ 7 = []) (h8 : σ 8 = []) :
    Exec Stmt.memTest σ (Function.update σ 2 [decide (σ 0 ∈ L)])
      (σ.space + (Stacks.encList L).length + 2) := by
  have e0 := Exec.push (r := 2) (b := false) (σ := σ)
    (S := σ.space + (Stacks.encList L).length + 2) (by omega)
  rw [h2] at e0
  have s0 := Stacks.space_update_cons σ 2 false
  rw [h2] at s0
  have e1 := Stmt.exec_memLoop (σ.space + (Stacks.encList L).length + 2) L
    (Function.update σ 2 [false]) false (by simp [h1]) (by simp) (by simp [h3]) (by simp [h4])
    (by simp [h6]) (by simp [h7]) (by simp [h8]) (by rw [s0]; omega)
  have e2 := Stmt.exec_moveAll (by decide : (5 : Fin 9) ≠ 1) _
    (Function.update (Function.update (Function.update (Function.update σ 2 [false]) 1 []) 5
      ((Stacks.encList L).reverse ++ (Function.update σ 2 [false]) 5)) 2
      [false || decide ((Function.update σ 2 [false]) 0 ∈ L)]) rfl
  refine exec_of_eq (.seq e0 (.seq e1 (.seq (e2.mono e1.space_le.2)
    (.skip (e2.space_le.2.trans e1.space_le.2))))) ?_
  funext j
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- Membership in the finite query set. -/
theorem mem_querySet_iff_queryAll (M : OTM) (x : BitString) (T : ℕ) (z : BitString) :
    z ∈ querySet M x T ↔ z ∈ queryAll M x T := by
  rw [querySet, Set.Finite.mem_toFinset]

/-- The outcome of the game at the position `S` only needs the oracle as a finite list of the
"yes" strings among the possible queries: any list `L` that agrees with `oracleOf h S` on the
query set gives the same clocked verdict. -/
theorem clockedAccepts_oracleOf_iff_list (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ)
    (S : Finset BitString) (L : List BitString)
    (hL : ∀ z ∈ querySet c.toOTM x (clock e x.length), z ∈ L ↔ z ∈ oracleOf h S) :
    ClockedAccepts c e (oracleOf h S) x ↔ ClockedAccepts c e {z | z ∈ L} x :=
  clockedAccepts_iff_of_agree c e _ _ x fun z hz => (hL z hz).symm

/-- Acceptance within the clock is acceptance at the clock (accepting configurations are halted,
hence fixed by `step`): the simulation may run exactly `clock e |x|` steps and read the state. -/
theorem clockedAccepts_iff_run (c : OTMCode) (e : ℕ) (B : Set BitString) (x : BitString) :
    ClockedAccepts c e B x ↔ (run c.toOTM B x (clock e x.length)).q = c.toOTM.accept := by
  constructor
  · rintro ⟨t, ht, hacc⟩
    rw [run_of_halted_le c.toOTM B x ht (Or.inl hacc)]
    exact hacc
  · intro h
    exact ⟨_, le_rfl, h⟩

end Kolmogorov.RandomStrings
