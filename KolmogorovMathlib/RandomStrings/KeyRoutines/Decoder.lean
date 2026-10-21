/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.KeySlots
import KolmogorovMathlib.RandomStrings.StmtTime
import KolmogorovMathlib.RandomStrings.SwapAsk

/-!
# The decoder of slot codes and the run at a key

The functional model of the decoder, cutting a code into slots, the statement `decodeKey` with
its `Exec` and `ExecLe` specifications, and the run of the machine at a key (`pushBad`,
`keyVerdictStmt`, `keyQueriesStmt`).

Part of `KolmogorovMathlib.RandomStrings.KeyRoutines`.
-/

namespace Kolmogorov.RandomStrings

namespace KeyRoutines

open Stmt

/-! ### The functional model of the decoder -/

/-- The bits `f₁ b₁ f₂ b₂ …` of a list of (flag, bit) pairs. -/
def pairBits : List (Bool × Bool) → BitString
  | [] => []
  | (f, b) :: ps => f :: b :: pairBits ps

/-- The bits of a slot: the presence bit, then the pairs. -/
def slotBits (s : Bool × List (Bool × Bool)) : BitString := s.1 :: pairBits s.2

/-- The run of the pair loop: the "active" bit and the reversed output. -/
def pairOut : Bool → List (Bool × Bool) → BitString → Bool × BitString
  | a, [], T => (a, T)
  | a, (f, b) :: ps, T => pairOut (f && a) ps (if (f && a) = true then b :: true :: T else T)

/-- The decoded list of a slot code: the strings of the present slots, in slot order. -/
def decKList (L n : ℕ) (κ : BitString) : List BitString :=
  (slots (2 * L + 1) n κ).filterMap decSlot

/-- The key `decK L n κ` is the set of strings of the decoded list `decKList L n κ`. -/
theorem decK_eq_toFinset (L n : ℕ) (κ : BitString) :
    decK L n κ = (decKList L n κ).toFinset := rfl

/-- The list `pairBits ps` has two bits per pair of `ps`. -/
theorem length_pairBits (ps : List (Bool × Bool)) : (pairBits ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => obtain ⟨f, b⟩ := p; simp [pairBits, ih]; omega

/-- Started with the active bit cleared, the pair loop keeps it cleared and leaves the reversed
output `T` unchanged. -/
theorem pairOut_false :
    ∀ (ps : List (Bool × Bool)) (T : BitString), pairOut false ps T = (false, T)
  | [], _ => rfl
  | (f, b) :: ps, T => by simp [pairOut, pairOut_false ps T]

/-- Started with the active bit set, the pair loop puts on top of `T` the reversed flagged code
`flagBits` of the string `unflagBits (pairBits ps)`, which consists of the bits of the pairs before
the first cleared flag. -/
theorem pairOut_true : ∀ (ps : List (Bool × Bool)) (T : BitString),
    (pairOut true ps T).2 = (flagBits (unflagBits (pairBits ps))).reverse ++ T
  | [], _ => rfl
  | (f, b) :: ps, T => by
    cases f
    · simp [pairOut, pairOut_false, pairBits, unflagBits, flagBits]
    · simp only [pairOut, Bool.and_self, ite_true, pairBits, unflagBits]
      rw [pairOut_true ps]
      simp [flagBits]

/-- The pair loop adds at most two bits per pair to the reversed output. -/
theorem length_pairOut_le : ∀ (ps : List (Bool × Bool)) (a : Bool) (T : BitString),
    (pairOut a ps T).2.length ≤ 2 * ps.length + T.length
  | [], _, _ => by simp [pairOut]
  | (f, b) :: ps, a, T => by
    have := length_pairOut_le ps (f && a) (if (f && a) = true then b :: true :: T else T)
    simp only [pairOut, List.length_cons]
    split_ifs at this ⊢ <;> simp at this ⊢ <;> omega

/-- The reversed output of one slot. -/
def slotRev (s : BitString) (T : BitString) : BitString :=
  match decSlot s with
  | some z => (Stacks.encStr z).reverse ++ T
  | none => T

/-- The reversed output of a list of slots. -/
def revOut : List (Bool × List (Bool × Bool)) → BitString → BitString
  | [], T => T
  | s :: sl, T => revOut sl (slotRev (slotBits s) T)

/-- The reversed output of the slot `(p, ps)`: if the presence bit `p` is set, the output of the
pair loop started with the active bit set, topped by the end marker `false`; otherwise `T`
unchanged. -/
theorem slotRev_slotBits (p : Bool) (ps : List (Bool × Bool)) (T : BitString) :
    slotRev (slotBits (p, ps)) T = if p = true then false :: (pairOut true ps T).2 else T := by
  cases p
  · rfl
  · simp only [slotRev, slotBits, decSlot, ite_true, pairOut_true, Stacks.encStr]
    simp [flagBits]

/-- The reversed output of a list of slots is the reversed code `Stacks.encList` of the strings of
its present slots, in slot order, on top of `T`. -/
theorem revOut_eq : ∀ (sl : List (Bool × List (Bool × Bool))) (T : BitString),
    revOut sl T = (Stacks.encList (sl.filterMap fun s => decSlot (slotBits s))).reverse ++ T
  | [], T => rfl
  | s :: sl, T => by
    rw [revOut, revOut_eq sl]
    unfold slotRev
    cases h : decSlot (slotBits s) with
    | none => simp [h]
    | some z =>
      simp [h, Stacks.encList, List.flatMap_cons, List.reverse_append]

/-- Decoding a slot adds at most the length of the slot to the reversed output. -/
theorem length_slotRev_le (p : Bool) (ps : List (Bool × Bool)) (T : BitString) :
    (slotRev (slotBits (p, ps)) T).length ≤ (slotBits (p, ps)).length + T.length := by
  rw [slotRev_slotBits]
  have := length_pairOut_le ps true T
  simp only [slotBits, List.length_cons, length_pairBits]
  split_ifs
  · simp; omega
  · simp

/-! ### Cutting a code into slots -/

/-- Every string of length `2 * L` is the bits `pairBits ps` of a list `ps` of `L` pairs. -/
theorem exists_pairBits : ∀ (L : ℕ) (s : BitString), s.length = 2 * L →
    ∃ ps : List (Bool × Bool), ps.length = L ∧ s = pairBits ps
  | 0, s, h => ⟨[], rfl, List.eq_nil_of_length_eq_zero (by simpa using h)⟩
  | L + 1, f :: b :: s, h => by
    obtain ⟨ps, h1, h2⟩ := exists_pairBits L s (by simp at h; omega)
    exact ⟨(f, b) :: ps, by simp [h1], by simp [pairBits, h2]⟩
  | L + 1, [], h => by simp at h
  | L + 1, [_], h => by simp at h; omega

/-- A code `κ` of `n` slots of `2 * L + 1` bits is the concatenation of the bits of a list `sl` of
slots with `L` pairs each, and its decoded list `decKList L n κ` consists of the decoded present
slots of `sl`, in order. -/
theorem exists_slots (L : ℕ) : ∀ (n : ℕ) (κ : BitString), κ.length = n * (2 * L + 1) →
    ∃ sl : List (Bool × List (Bool × Bool)), (∀ s ∈ sl, s.2.length = L) ∧
      κ = sl.flatMap slotBits ∧ decKList L n κ = sl.filterMap fun s => decSlot (slotBits s)
  | 0, κ, h => ⟨[], by simp, List.eq_nil_of_length_eq_zero (by simpa using h), by
      simp [decKList, slots]⟩
  | n + 1, κ, h => by
    have h1 : (κ.take (2 * L + 1)).length = 2 * L + 1 := by
      rw [List.length_take]; rw [h]; apply min_eq_left; nlinarith
    have h2 : (κ.drop (2 * L + 1)).length = n * (2 * L + 1) := by
      rw [List.length_drop, h]; ring_nf; omega
    obtain ⟨sl, hsl, he, hd⟩ := exists_slots L n _ h2
    obtain ⟨p, rest, hpr⟩ : ∃ p rest, κ.take (2 * L + 1) = p :: rest := by
      cases hk : κ.take (2 * L + 1) with
      | nil => rw [hk] at h1; simp at h1
      | cons p rest => exact ⟨p, rest, rfl⟩
    have hrest : rest.length = 2 * L := by rw [hpr] at h1; simpa using h1
    obtain ⟨ps, hps, hpb⟩ := exists_pairBits L rest hrest
    refine ⟨(p, ps) :: sl, ?_, ?_, ?_⟩
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact hps
      · exact hsl s hs
    · rw [List.flatMap_cons, ← he]
      have : slotBits (p, ps) = κ.take (2 * L + 1) := by rw [hpr, hpb]; rfl
      rw [this, List.take_append_drop]
    · simp only [decKList, slots, List.filterMap_cons]
      have : κ.take (2 * L + 1) = slotBits (p, ps) := by rw [hpr, hpb]; rfl
      rw [this]
      have hd' : (slots (2 * L + 1) n (κ.drop (2 * L + 1))).filterMap decSlot =
          sl.filterMap fun s => decSlot (slotBits s) := hd
      rw [hd']

/-! ### The decoder -/

/-- The stacks of the decoder. -/
def dst (κ u C t A P T O : BitString) : Stacks 8 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (fun _ => []) 0 κ) 1 u) 2 C) 3 t) 4 A)
      5 P) 6 T) 7 O

/-- The lemmas `dst_0` to `dst_7` read the eight stacks off `dst κ u C t A P T O`: stack `0` is
the code `κ` still to be read; stack `1` is the width `u`, with one symbol per pair of a slot;
stack `2` is the counter `C` of the pairs left in the current slot; stack `3` is the work stack
`t` through which `copy` loads the counter; stack `4` is the active bit `A`, which the first
pair with a cleared flag switches off; stack `5` is the presence bit `P` of the slot being
decoded; stack `6` is the output `T` produced so far, in reverse order; and stack `7` is the
stack `O` that receives the final output. -/
@[simp] theorem dst_0 (κ u C t A P T O : BitString) : dst κ u C t A P T O 0 = κ := rfl
@[simp] theorem dst_1 (κ u C t A P T O : BitString) : dst κ u C t A P T O 1 = u := rfl
@[simp] theorem dst_2 (κ u C t A P T O : BitString) : dst κ u C t A P T O 2 = C := rfl
@[simp] theorem dst_3 (κ u C t A P T O : BitString) : dst κ u C t A P T O 3 = t := rfl
@[simp] theorem dst_4 (κ u C t A P T O : BitString) : dst κ u C t A P T O 4 = A := rfl
@[simp] theorem dst_5 (κ u C t A P T O : BitString) : dst κ u C t A P T O 5 = P := rfl
@[simp] theorem dst_6 (κ u C t A P T O : BitString) : dst κ u C t A P T O 6 = T := rfl
@[simp] theorem dst_7 (κ u C t A P T O : BitString) : dst κ u C t A P T O 7 = O := rfl

/-- Stack `1` of `dst κ u C t A P T O` is the width `u`, with one symbol per pair of a slot. -/
add_decl_doc dst_1

/-- Stack `2` of `dst κ u C t A P T O` is the counter `C` of the pairs left in the current slot. -/
add_decl_doc dst_2

/-- Stack `3` of `dst κ u C t A P T O` is the work stack `t` through which `copy` loads the
counter. -/
add_decl_doc dst_3

/-- Stack `4` of `dst κ u C t A P T O` is the active bit `A`, which the first pair with a cleared
flag switches off. -/
add_decl_doc dst_4

/-- Stack `5` of `dst κ u C t A P T O` is the presence bit `P` of the slot being decoded. -/
add_decl_doc dst_5

/-- Stack `6` of `dst κ u C t A P T O` is the output `T` produced so far, in reverse order. -/
add_decl_doc dst_6

/-- Stack `7` of `dst κ u C t A P T O` is the stack `O` that receives the final output. -/
add_decl_doc dst_7

/-- The space of the decoder's stacks `dst κ u C t A P T O` is the total length of the eight
strings. -/
theorem dst_space (κ u C t A P T O : BitString) :
    (dst κ u C t A P T O).space = κ.length + u.length + C.length + t.length + A.length +
      P.length + T.length + O.length := by
  simp [Stacks.space, dst, Fin.sum_univ_succ, Function.update_apply]
  ring

/-- Length arithmetic of the decoder's states. -/
macro "key_routines_dlen" : tactic => `(tactic|
  (simp only [dst_space, slotBits, pairBits, List.cons_append, List.length_cons,
    List.length_append, length_pairBits, List.length_nil, List.length_singleton, dst_0, dst_1,
    dst_2, dst_3, dst_4, dst_5, dst_6, dst_7] at *;
   omega))

/-- One pair `(f, b)` of a slot: pop it; if `f` and the active bit hold, emit `true, b` on the
reversed output, else clear the active bit. -/
def pairStep : Stmt 8 :=
  caseBit 0 fun f => .seq (.pop 0) (caseBit 0 fun b => .seq (.pop 0) (caseBit 4 fun a =>
    cond (f && a) (.seq (.push 6 true) (.push 6 b)) (.seq (.pop 4) (.push 4 false))))

/-- The pairs of a slot, one per symbol of the counter `2`. -/
def pairLoop : Stmt 8 := .loop 2 Option.isSome (.seq (.pop 2) pairStep)

/-- One slot: load the counter, read the presence bit, run the pairs, emit the terminator. -/
def slotBody : Stmt 8 :=
  seqs [copy 1 2 3, caseBit 0 (fun p => seqs [.pop 0, .push 4 p, .push 5 p]), pairLoop, .pop 4,
    caseBit 5 (fun p => .seq (.pop 5) (cond p (.push 6 false) .skip))]

/-- **The decoder**: all slots, then the reversed output is moved (reversed) onto `7`. -/
def decodeKey : Stmt 8 := .seq (.loop 0 Option.isSome slotBody) (moveAll 6 7)

/-- One pair step: on the code `f :: b :: rest` with active bit `a`, `pairStep` pops `f` and `b`,
replaces the active bit by `f && a`, and pushes `true` and then `b` on the reversed output `T`
when `f && a` holds. -/
theorem exec_pairStep (f b a : Bool) (rest u C t P T O : BitString) {S : ℕ}
    (hS : (dst (f :: b :: rest) u C t [a] P T O).space ≤ S) :
    Exec pairStep (dst (f :: b :: rest) u C t [a] P T O)
      (dst rest u C t [f && a] P (if (f && a) = true then b :: true :: T else T) O) S := by
  have hsp := hS
  rw [dst_space] at hsp
  simp only [List.length_cons] at hsp
  unfold pairStep
  rw [exec_caseBit (show (dst (f :: b :: rest) u C t [a] P T O) 0 = f :: (b :: rest) from rfl)]
  refine Exec.seq (σ₁ := dst (b :: rest) u C t [a] P T O)
    (SimOTM.exec_pop_eq hS (by funext j; fin_cases j <;> rfl)) ?_
  rw [exec_caseBit (show (dst (b :: rest) u C t [a] P T O) 0 = b :: rest from rfl)]
  refine Exec.seq (σ₁ := dst rest u C t [a] P T O)
    (SimOTM.exec_pop_eq (by rw [dst_space]; simp; omega) (by funext j; fin_cases j <;> rfl)) ?_
  rw [exec_caseBit (show (dst rest u C t [a] P T O) 4 = a :: [] from rfl)]
  cases f <;> cases a <;> simp only [Bool.and_true, Bool.and_false, Bool.cond_true,
    Bool.cond_false] <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact Exec.seq (σ₁ := dst rest u C t [] P T O)
      (SimOTM.exec_pop_eq (by rw [dst_space]; simp; omega) (by funext j; fin_cases j <;> rfl))
      (SimOTM.exec_push_eq (by rw [dst_space]; simp; omega) (by funext j; fin_cases j <;> rfl))
  · exact Exec.seq (σ₁ := dst rest u C t [] P T O)
      (SimOTM.exec_pop_eq (by rw [dst_space]; simp; omega) (by funext j; fin_cases j <;> rfl))
      (SimOTM.exec_push_eq (by rw [dst_space]; simp; omega) (by funext j; fin_cases j <;> rfl))
  · exact Exec.seq (σ₁ := dst rest u C t [] P T O)
      (SimOTM.exec_pop_eq (by rw [dst_space]; simp; omega) (by funext j; fin_cases j <;> rfl))
      (SimOTM.exec_push_eq (by rw [dst_space]; simp; omega) (by funext j; fin_cases j <;> rfl))
  · exact Exec.seq (σ₁ := dst rest u C t [true] P (true :: T) O)
      (SimOTM.exec_push_eq (by rw [dst_space]; simp; omega) (by funext j; fin_cases j <;> rfl))
      (SimOTM.exec_push_eq (by rw [dst_space]; simp; omega) (by funext j; fin_cases j <;> rfl))

/-- The pair loop: with a counter `C` of length `ps.length` on `2`, `pairLoop` consumes the bits
`pairBits ps` of the code, empties the counter, and leaves the active bit and the reversed output
given by `pairOut a ps T`. -/
theorem exec_pairLoop (u t P O : BitString) :
    ∀ (ps : List (Bool × Bool)) (C rest T : BitString) (a : Bool) {S : ℕ},
    C.length = ps.length → (dst (pairBits ps ++ rest) u C t [a] P T O).space ≤ S →
    Exec pairLoop (dst (pairBits ps ++ rest) u C t [a] P T O)
      (dst rest u [] t [(pairOut a ps T).1] P (pairOut a ps T).2 O) S
  | [], C, rest, T, a, S, hC, hS => by
    have hC' : C = [] := List.eq_nil_of_length_eq_zero (by simpa using hC)
    subst hC'
    exact Exec.loopF (r := 2) (cond := Option.isSome) rfl hS
  | (f, b) :: ps, C, rest, T, a, S, hC, hS => by
    obtain ⟨c, C', rfl⟩ : ∃ c C', C = c :: C' := by
      cases C with
      | nil => simp at hC
      | cons c C' => exact ⟨c, C', rfl⟩
    have hsp := hS
    simp only [dst_space, pairBits, List.cons_append, List.length_cons, List.length_append,
      length_pairBits] at hsp
    have h1 : Exec (.pop 2) (dst (pairBits ((f, b) :: ps) ++ rest) u (c :: C') t [a] P T O)
        (dst (f :: b :: (pairBits ps ++ rest)) u C' t [a] P T O) S :=
      SimOTM.exec_pop_eq hS (by funext j; fin_cases j <;> rfl)
    have h2 := exec_pairStep f b a (pairBits ps ++ rest) u C' t P T O (S := S)
      (by simp only [dst_space, List.length_cons, List.length_append, length_pairBits]; omega)
    have h3 := exec_pairLoop u t P O ps C' rest
      (if (f && a) = true then b :: true :: T else T) (f && a) (S := S)
      (by simpa using hC) (by
        simp only [dst_space, List.length_cons, List.length_append, length_pairBits]
        split_ifs <;> (try simp only [List.length_cons]) <;> omega)
    exact Exec.loopT (r := 2) (cond := Option.isSome) rfl (Exec.seq h1 h2) h3

/-- One slot: on a code that starts with the bits of the slot `(p, ps)`, where `ps` has `|u|`
pairs and the work stacks are empty, `slotBody` consumes the slot and replaces the reversed output
`T` by `slotRev (slotBits (p, ps)) T`, within any space that exceeds the initial one by at least
`|u| + 1`. -/
theorem exec_slotBody (p : Bool) (ps : List (Bool × Bool)) (rest u T O : BitString) {S : ℕ}
    (hlen : ps.length = u.length)
    (hS : (dst (slotBits (p, ps) ++ rest) u [] [] [] [] T O).space + u.length + 1 ≤ S) :
    Exec slotBody (dst (slotBits (p, ps) ++ rest) u [] [] [] [] T O)
      (dst rest u [] [] [] [] (slotRev (slotBits (p, ps)) T) O) S := by
  have hsp := hS
  rw [dst_space] at hsp
  simp only [slotBits, List.cons_append, List.length_cons, List.length_nil] at hsp
  -- 1. the counter
  have e1 := exec_copy (r := (1 : Fin 8)) (r' := 2) (t := 3) (by decide) (by decide) (by decide)
    (σ := dst (p :: (pairBits ps ++ rest)) u [] [] [] [] T O) rfl
  have h1 : Exec (copy 1 2 3) (dst (p :: (pairBits ps ++ rest)) u [] [] [] [] T O)
      (dst (p :: (pairBits ps ++ rest)) u u [] [] [] T O) S := by
    refine exec_of_eq (e1.mono ?_) ?_
    · key_routines_dlen
    · funext j; fin_cases j <;> simp [dst]
  -- 2. the presence bit
  have h2 : Exec (caseBit 0 (fun p => seqs [.pop 0, .push 4 p, .push 5 p]))
      (dst (p :: (pairBits ps ++ rest)) u u [] [] [] T O)
      (dst (pairBits ps ++ rest) u u [] [p] [p] T O) S := by
    rw [exec_caseBit (show (dst (p :: (pairBits ps ++ rest)) u u [] [] [] T O) 0 =
      p :: (pairBits ps ++ rest) from rfl)]
    refine Exec.seq (σ₁ := dst (pairBits ps ++ rest) u u [] [] [] T O)
      (SimOTM.exec_pop_eq (by key_routines_dlen) (by funext j; fin_cases j <;> rfl)) ?_
    refine Exec.seq (σ₁ := dst (pairBits ps ++ rest) u u [] [p] [] T O)
      (SimOTM.exec_push_eq (by key_routines_dlen) (by funext j; fin_cases j <;> rfl)) ?_
    refine Exec.seq (σ₁ := dst (pairBits ps ++ rest) u u [] [p] [p] T O)
      (SimOTM.exec_push_eq (by key_routines_dlen) (by funext j; fin_cases j <;> rfl)) ?_
    exact Exec.skip (by key_routines_dlen)
  -- 3. the pairs
  have h3 := exec_pairLoop u [] [p] O ps u rest T p (S := S) hlen.symm
    (by key_routines_dlen)
  -- 4. clear the active bit
  have h4 : Exec (.pop 4) (dst rest u [] [] [(pairOut p ps T).1] [p] (pairOut p ps T).2 O)
      (dst rest u [] [] [] [p] (pairOut p ps T).2 O) S :=
    SimOTM.exec_pop_eq (h3.space_le.2) (by funext j; fin_cases j <;> rfl)
  -- 5. the terminator
  have h5 : Exec (caseBit 5 (fun p => .seq (.pop 5) (cond p (.push 6 false) .skip)))
      (dst rest u [] [] [] [p] (pairOut p ps T).2 O)
      (dst rest u [] [] [] [] (slotRev (slotBits (p, ps)) T) O) S := by
    have hs4 := h4.space_le.2
    rw [exec_caseBit (show (dst rest u [] [] [] [p] (pairOut p ps T).2 O) 5 = p :: [] from rfl),
      slotRev_slotBits]
    refine Exec.seq (σ₁ := dst rest u [] [] [] [] (pairOut p ps T).2 O)
      (SimOTM.exec_pop_eq hs4 (by funext j; fin_cases j <;> rfl)) ?_
    cases p
    · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
      rw [pairOut_false]
      exact Exec.skip (by key_routines_dlen)
    · simp only [Bool.cond_true, ite_true]
      exact SimOTM.exec_push_eq (by key_routines_dlen)
        (by funext j; fin_cases j <;> rfl)
  exact Exec.seq h1 (Exec.seq h2 (Exec.seq h3 (Exec.seq h4 (Exec.seq h5
    (Exec.skip h5.space_le.2)))))

/-- The slot loop: on the code `sl.flatMap slotBits` of slots with `|u|` pairs each, the loop of
`slotBody` consumes the whole code and leaves the reversed output `revOut sl T` on `6`. -/
theorem exec_slotLoop (u O : BitString) :
    ∀ (sl : List (Bool × List (Bool × Bool))) (T : BitString) {S : ℕ},
    (∀ s ∈ sl, s.2.length = u.length) →
    (dst (sl.flatMap slotBits) u [] [] [] [] T O).space + u.length + 1 ≤ S →
    Exec (.loop 0 Option.isSome slotBody) (dst (sl.flatMap slotBits) u [] [] [] [] T O)
      (dst [] u [] [] [] [] (revOut sl T) O) S
  | [], T, S, _, hS => Exec.loopF (by rfl) (by omega)
  | (p, ps) :: sl, T, S, hsl, hS => by
    have h1 := exec_slotBody p ps (sl.flatMap slotBits) u T O (S := S)
      (hsl _ List.mem_cons_self) (by simpa using hS)
    have hl := length_slotRev_le p ps T
    have h2 := exec_slotLoop u O sl (slotRev (slotBits (p, ps)) T) (S := S)
      (fun s hs => hsl s (List.mem_cons_of_mem _ hs)) (by
        rw [dst_space] at hS ⊢
        simp only [List.flatMap_cons, List.length_append, List.length_nil] at hS ⊢
        omega)
    exact Exec.loopT (by rfl) (by simpa using h1) h2

/-- **The decoder.**  On a code `κ` of `n` slots of `2L + 1` bits, with a width stack of length
`L`, `decodeKey` leaves `Stacks.encList (decKList L n κ)` on `7`, empties `0`, keeps the width,
within space `|κ| + 2L + 1`. -/
theorem exec_decodeKey {L n : ℕ} {κ u : BitString} (hκ : κ.length = n * (2 * L + 1))
    (hu : u.length = L) {S : ℕ} (hS : κ.length + 2 * L + 1 ≤ S) :
    Exec decodeKey (dst κ u [] [] [] [] [] [])
      (dst [] u [] [] [] [] [] (Stacks.encList (decKList L n κ))) S := by
  obtain ⟨sl, hsl, rfl, hd⟩ := exists_slots L n κ hκ
  have h1 := exec_slotLoop u [] sl [] (S := S) (fun s hs => (hsl s hs).trans hu.symm)
    (by rw [dst_space]; simp only [List.length_nil, add_zero]; omega)
  have hs1 := h1.space_le.2
  have h2 := exec_moveAll (r := (6 : Fin 8)) (r' := 7) (by decide) (revOut sl [])
    (dst [] u [] [] [] [] (revOut sl []) []) rfl
  refine Exec.seq h1 (exec_of_eq (h2.mono hs1) ?_)
  rw [hd, revOut_eq]
  funext j; fin_cases j <;> simp [dst]

/-- All loops of the decoder are pop-loops: each exits on an empty test stack, and its body pops
that stack on every path and never pushes on it. -/
theorem popLoops_decodeKey : decodeKey.PopLoops := by
  simp [decodeKey, slotBody, pairLoop, pairStep, seqs, copy, dupStep, moveAll, moveBit, caseBit,
    PopLoops, NoPush, Pops]

/-- The loops of the decoder are nested two deep: the loops of `copy` and the pair loop run inside
the slot loop. -/
theorem loopDepth_decodeKey : decodeKey.loopDepth = 2 := rfl

/-- **Step bound of the decoder**: at most `decodeKey.size * (S + 1) ^ 2` steps within space
`S ≥ |κ| + 2L + 1`. -/
theorem execLe_decodeKey {L n : ℕ} {κ u : BitString} (hκ : κ.length = n * (2 * L + 1))
    (hu : u.length = L) {S : ℕ} (hS : κ.length + 2 * L + 1 ≤ S) :
    ExecLe decodeKey (dst κ u [] [] [] [] [] [])
      (dst [] u [] [] [] [] [] (Stacks.encList (decKList L n κ))) S
      (decodeKey.size * (S + 1) ^ 2) := by
  have := (exec_decodeKey hκ hu hS).execLe_size_mul_pow popLoops_decodeKey
  rwa [loopDepth_decodeKey] at this

/-! ### The run of the machine at a key

The oracle of the position `K` is `oracleOf T.fn K = {z | z ∈ K ∪ T.bad}ᶜ` (`oracleOf_table`);
the run of `c` under it is the run of `c.swapAsk` under the listed oracle `K ∪ T.bad`.  With the
key given as a list `Kl` (e.g. the output of `decodeKey`), the listed oracle is
`oraList T Kl = badList T ++ Kl`: its code is obtained by pushing the fixed code of the bad
strings on top of `Stacks.encList Kl` (`pushBad`).  The verdict and the queries are then the
clocked simulation `SimOTM.simStmt` and the recording simulation `SimOTM.recSimStmt` of
`c.swapAsk`, with their step bounds. -/

/-- The bad strings of the table (a fixed finite list). -/
noncomputable def badList (T : Table) : List BitString := T.bad.toList

/-- The listed oracle of the position `Kl.toFinset`: the bad strings, then the key. -/
noncomputable def oraList (T : Table) (Kl : List BitString) : List BitString := badList T ++ Kl

/-- The members of the listed oracle `oraList T Kl` are the strings of the key `Kl` and the bad
strings of the table `T`. -/
theorem setOf_mem_oraList (T : Table) (Kl : List BitString) :
    {z | z ∈ oraList T Kl} = {z | z ∈ Kl.toFinset ∪ T.bad} := by
  ext z
  simp [oraList, badList, or_comm]

/-- The code of the listed oracle `oraList T Kl` is the code of the bad strings followed by the
code of the key `Kl`. -/
theorem encList_oraList (T : Table) (Kl : List BitString) :
    Stacks.encList (oraList T Kl) = Stacks.encList (badList T) ++ Stacks.encList Kl := by
  simp [oraList, Stacks.encList, List.flatMap_append]

/-- Push the code of the bad strings on top of the stack `r`. -/
noncomputable def pushBad {k : ℕ} (T : Table) (r : Fin k) : Stmt k :=
  pushList r (Stacks.encList (badList T))

/-- `pushBad` turns the code of the key `Kl` into the code of the listed oracle, in
`|encList (badList T)|` steps (a constant for a fixed table). -/
theorem execLe_pushBad {k : ℕ} (T : Table) (r : Fin k) (σ : Stacks k) (Kl : List BitString)
    (h : σ r = Stacks.encList Kl) :
    ExecLe (pushBad T r) σ (Function.update σ r (Stacks.encList (oraList T Kl)))
      (σ.space + (Stacks.encList (badList T)).length) (Stacks.encList (badList T)).length := by
  have := ExecLe.of_execT (Stmt.execT_pushList r (Stacks.encList (badList T)) σ)
  rw [h] at this
  rw [encList_oraList]
  exact this

/-- The verdict bit of the run of `c` at a position. -/
theorem accB_swapAsk_eq_outcome (c : OTMCode) (e : ℕ) (T : Table) (x : BitString)
    (Kl : List BitString) (ε : ℝ) (X : Finset BitString) :
    SimOTM.accB c.swapAsk (run c.swapAsk.toOTM {z | z ∈ oraList T Kl} x (clock e x.length)).q =
      (gameOf c e x T.fn ε X).outcome Kl.toFinset := by
  classical
  unfold gameOf
  dsimp only
  rw [Bool.eq_iff_iff, decide_eq_true_iff, OTMCode.clockedAccepts_oracleOf_table,
    clockedAccepts_iff_run, ← setOf_mem_oraList]
  exact SimOTM.accB_iff c.swapAsk _

/-- **The verdict at a key**: the clocked simulation of `c.swapAsk`. -/
def keyVerdictStmt (c : OTMCode) (e : ℕ) : Stmt 21 := SimOTM.simStmt c.swapAsk e

/-- Started with `x` on `0` and the code of `oraList T Kl` on `1`, `keyVerdictStmt c e` leaves the
outcome of the position `Kl.toFinset` of `G_{e,x}` on `2` (all else as before), within space
`(k + 10) N` and time `size ((k + 10) N + 1) ^ depth`, `N = |x| + clock e |x| + |code| + 1`,
`k = c.swapAsk.k`. -/
theorem execLe_keyVerdict (c : OTMCode) (e : ℕ) (T : Table) (x : BitString)
    (Kl : List BitString) (ε : ℝ) (X : Finset BitString) :
    ExecLe (keyVerdictStmt c e)
      (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList (oraList T Kl)))
      (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1
        (Stacks.encList (oraList T Kl))) 2 [(gameOf c e x T.fn ε X).outcome Kl.toFinset])
      ((c.swapAsk.k + 10) *
        (x.length + clock e x.length + (Stacks.encList (oraList T Kl)).length + 1))
      ((keyVerdictStmt c e).size * ((c.swapAsk.k + 10) *
        (x.length + clock e x.length + (Stacks.encList (oraList T Kl)).length + 1) + 1) ^
          (keyVerdictStmt c e).loopDepth) := by
  rw [← accB_swapAsk_eq_outcome c e T x Kl ε X]
  exact SimOTM.execLe_simStmt c.swapAsk e x (oraList T Kl)

/-- **The queries at a key**: the recording simulation of `c.swapAsk`. -/
def keyQueriesStmt (c : OTMCode) (e : ℕ) : Stmt 21 := SimOTM.recSimStmt c.swapAsk e

/-- The recorded queries of the run at the position `Kl.toFinset` (with repetitions). -/
noncomputable def keyQ (c : OTMCode) (e : ℕ) (T : Table) (x : BitString) (Kl : List BitString) :
    List BitString :=
  SimOTM.recL c.swapAsk.toOTM {z | z ∈ oraList T Kl} x (clock e x.length)

/-- The recorded queries `keyQ c e T x Kl` are exactly the queries that `c` asks on `x` within
`clock e |x|` steps under the oracle `oracleOf T.fn Kl.toFinset` of the position `Kl.toFinset`. -/
theorem mem_keyQ (c : OTMCode) (e : ℕ) (T : Table) (x : BitString) (Kl : List BitString)
    (z : BitString) :
    z ∈ keyQ c e T x Kl ↔
      z ∈ queries c.toOTM (oracleOf T.fn Kl.toFinset) x (clock e x.length) := by
  rw [keyQ, SimOTM.mem_recL, OTMCode.queries_oracleOf_table, setOf_mem_oraList]

/-- The code of the recorded queries `keyQ c e T x Kl` has length at most `N * (2 * N + 1)`, where
`N = clock e |x|` bounds the number of steps of the run. -/
theorem length_keyQ (c : OTMCode) (e : ℕ) (T : Table) (x : BitString) (Kl : List BitString) :
    (Stacks.encList (keyQ c e T x Kl)).length ≤ clock e x.length * (2 * clock e x.length + 1) :=
  SimOTM.length_recL _ _ _ _

/-- Started with `x` on `0` and the code of `oraList T Kl` on `1`, `keyQueriesStmt c e` leaves
the code of `keyQ c e T x Kl` (whose members are the queries `P K` of the run at the position
`K = Kl.toFinset`, `mem_keyQ`) on `16`, all else as before. -/
theorem execLe_keyQueries
    (c : OTMCode) (e : ℕ) (T : Table) (x : BitString) (Kl : List BitString) :
    ExecLe (keyQueriesStmt c e)
      (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList (oraList T Kl)))
      (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1
        (Stacks.encList (oraList T Kl))) 16 (Stacks.encList (keyQ c e T x Kl)))
      ((c.swapAsk.k + 20) *
        (x.length + clock e x.length + (Stacks.encList (oraList T Kl)).length + 1) ^ 2)
      ((keyQueriesStmt c e).size * ((c.swapAsk.k + 20) *
        (x.length + clock e x.length + (Stacks.encList (oraList T Kl)).length + 1) ^ 2 + 1) ^
          (keyQueriesStmt c e).loopDepth) :=
  SimOTM.execLe_recSim c.swapAsk e x (oraList T Kl)

end KeyRoutines
end Kolmogorov.RandomStrings
