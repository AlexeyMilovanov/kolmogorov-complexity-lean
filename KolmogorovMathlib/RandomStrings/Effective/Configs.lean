/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Effective.Codes

/-!
# Codes of configurations and their runs

Finite codes of configurations (`CC`) and the representation relation `Rep`; the primitive
recursive step and run functions (`stepC`, `runC`, `stepCode`, `runCode`) simulating `step` and
`run` with a finite oracle; the clocked verdicts (`clockedOutcomeT`, `clockedOutcome`); the
possible queries (`queryListCodeT`, `queryListCode`); and their primitive recursiveness.

Part of `KolmogorovMathlib.RandomStrings.Effective`.
-/

namespace Kolmogorov.RandomStrings

/-! ### Codes of configurations -/

/-- A configuration code: state index `q`, the cells left of the head (nearest first) `L`, the
scanned cell `a`, the cells right of the head (nearest first) `R`, the head position `hp - hn`,
and the query buffer `buf`. -/
structure CC where
  q : ℕ
  L : List Sym
  a : Sym
  R : List Sym
  hp : ℕ
  hn : ℕ
  buf : BitString

/-- `CC` as a product type. -/
def CC.equiv : CC ≃ ℕ × List Sym × Sym × List Sym × ℕ × ℕ × BitString where
  toFun c := (c.q, c.L, c.a, c.R, c.hp, c.hn, c.buf)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable CC := Primcodable.ofEquiv _ CC.equiv

instance : Inhabited CC := ⟨⟨0, [], none, [], 0, 0, []⟩⟩

/-- `cc` describes the tape `tape` around the head position `head`. -/
def TapeRep (cc : CC) (tape : ℤ → Sym) (head : ℤ) : Prop :=
  head = (cc.hp : ℤ) - cc.hn ∧ tape head = cc.a ∧
    (∀ i : ℕ, tape (head - 1 - i) = cc.L.getD i none) ∧
    (∀ i : ℕ, tape (head + 1 + i) = cc.R.getD i none)

/-- The code `cc` represents the configuration `c` of the machine coded by `m` (this determines
`c` completely). -/
def Rep {m : ℕ} (cc : CC) (c : Config (decodeCode m).toOTM) : Prop :=
  cc.q = (c.q : Fin (codeK m)).val ∧ TapeRep cc c.tape c.head ∧ c.buf = cc.buf

/-- Writing the scanned cell. -/
def CC.write (cc : CC) (s : Sym) : CC := { cc with a := s }
/-- Moving the head left. -/
def CC.left (cc : CC) : CC :=
  { cc with L := cc.L.tail, a := cc.L.headD none, R := cc.a :: cc.R, hn := cc.hn + 1 }
/-- Moving the head right. -/
def CC.right (cc : CC) : CC :=
  { cc with L := cc.a :: cc.L, a := cc.R.headD none, R := cc.R.tail, hp := cc.hp + 1 }
/-- The move of index `n mod 3`. -/
def CC.move (n : ℕ) (cc : CC) : CC :=
  if n % 3 = 0 then cc.left else if n % 3 = 1 then cc else cc.right

/-- Updating a configuration with a written symbol maintains the tape representation. -/
theorem tapeRep_write {cc : CC} {tape : ℤ → Sym} {head : ℤ} (h : TapeRep cc tape head)
    (s : Sym) : TapeRep (cc.write s) (Function.update tape head s) head := by
  obtain ⟨h0, -, h2, h3⟩ := h
  refine ⟨h0, by simp [CC.write], fun i => ?_, fun i => ?_⟩
  · rw [Function.update_of_ne (by omega)]; exact h2 i
  · rw [Function.update_of_ne (by omega)]; exact h3 i

/-- Moving the head of a configuration to the left maintains the tape representation. -/
theorem tapeRep_left {cc : CC} {tape : ℤ → Sym} {head : ℤ} (h : TapeRep cc tape head) :
    TapeRep cc.left tape (head - 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun i => ?_, fun i => ?_⟩
  · simp only [CC.left]; push_cast; omega
  · have := h2 0
    simp only [Nat.cast_zero, sub_zero] at this
    rw [this]; simp only [CC.left]; cases cc.L <;> rfl
  · have := h2 (i + 1)
    rw [show head - 1 - 1 - (i : ℤ) = head - 1 - ((i + 1 : ℕ) : ℤ) by push_cast; ring, this]
    simp only [CC.left]; cases cc.L <;> simp
  · rcases i with _ | i
    · simp only [CC.left, Nat.cast_zero, add_zero, sub_add_cancel]; simpa using h1
    · rw [show head - 1 + 1 + ((i + 1 : ℕ) : ℤ) = head + 1 + (i : ℤ) by push_cast; ring, h3 i]
      simp [CC.left]

/-- Moving the head of a configuration to the right maintains the tape representation. -/
theorem tapeRep_right {cc : CC} {tape : ℤ → Sym} {head : ℤ} (h : TapeRep cc tape head) :
    TapeRep cc.right tape (head + 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun i => ?_, fun i => ?_⟩
  · simp only [CC.right]; push_cast; omega
  · have := h3 0
    simp only [Nat.cast_zero, add_zero] at this
    rw [this]; simp only [CC.right]; cases cc.R <;> rfl
  · rcases i with _ | i
    · simp only [CC.right, Nat.cast_zero, sub_zero, add_sub_cancel_right]; simpa using h1
    · rw [show head + 1 - 1 - ((i + 1 : ℕ) : ℤ) = head - 1 - (i : ℤ) by push_cast; ring, h2 i]
      simp [CC.right]
  · have := h3 (i + 1)
    rw [show head + 1 + 1 + (i : ℤ) = head + 1 + ((i + 1 : ℕ) : ℤ) by push_cast; ring, this]
    simp only [CC.right]; cases cc.R <;> simp

/-- Moving the head of a configuration by `n` steps maintains the tape representation. -/
theorem tapeRep_move {cc : CC} {tape : ℤ → Sym} {head : ℤ} (h : TapeRep cc tape head)
    (n : ℕ) : TapeRep (cc.move n) tape (moveHead (moveOf n) head) := by
  unfold CC.move moveOf
  split_ifs
  · exact tapeRep_left h
  · exact h
  · exact tapeRep_right h

/-- The buffer is preserved when moving the head of a configuration. -/
theorem CC.move_buf (cc : CC) (n : ℕ) : (cc.move n).buf = cc.buf := by
  unfold CC.move; split_ifs <;> rfl

/-! ### One step on codes -/

/-- Halting test on codes. -/
def haltedB (m : ℕ) (cc : CC) : Bool := decide (cc.q = codeAcc m) || decide (cc.q = codeRej m)

/-- The action at a code, with the oracle answer `b` used by an `ask`. -/
def CC.act (m : ℕ) (b : Bool) (cc : CC) : CC :=
  if actCode m cc.q cc.a % 3 = 0 then
    { CC.move ((actCode m cc.q cc.a / 3).unpair.2 / 3)
        (cc.write (symOf (actCode m cc.q cc.a / 3).unpair.2)) with
      q := (actCode m cc.q cc.a / 3).unpair.1 % codeK m }
  else if actCode m cc.q cc.a % 3 = 1 then
    { cc with q := (actCode m cc.q cc.a / 3).unpair.1 % codeK m,
              buf := cc.buf ++ [decide ((actCode m cc.q cc.a / 3).unpair.2 % 2 = 1)] }
  else
    { cc with q := (bif b then (actCode m cc.q cc.a / 3).unpair.1 else
                    (actCode m cc.q cc.a / 3).unpair.2) % codeK m,
              buf := [] }

/-- Membership in a finite oracle, as a primitive recursive test. -/
def memStr (z : BitString) (ans : List BitString) : Bool :=
  ans.foldr (fun w b => decide (w = z) || b) false

/-- The string membership test evaluates to true if and only if the string is in the answer list. -/
theorem memStr_iff (z : BitString) (ans : List BitString) : memStr z ans = true ↔ z ∈ ans := by
  induction ans with
  | nil => simp [memStr]
  | cons w ans ih =>
    have h : memStr z (w :: ans) = (decide (w = z) || memStr z ans) := rfl
    rw [h, Bool.or_eq_true, ih, decide_eq_true_eq, List.mem_cons, eq_comm]

/-- `step` on a `step` action. -/
theorem step_eq_step (M : OTM) (B : Set BitString) (c : Config M) (hc : ¬ Halted M c) {q' : M.Q}
    {a : Sym} {mv : Move} (h : M.δ c.q (c.tape c.head) = .step q' a mv) :
    step M B c = ⟨q', Function.update c.tape c.head a, moveHead mv c.head, c.buf⟩ := by
  unfold step; rw [ite_eq_right hc, h]

/-- `step` on a `push` action. -/
theorem step_eq_push (M : OTM) (B : Set BitString) (c : Config M) (hc : ¬ Halted M c) {q' : M.Q}
    {b : Bool} (h : M.δ c.q (c.tape c.head) = .push q' b) :
    step M B c = ⟨q', c.tape, c.head, c.buf ++ [b]⟩ := by
  unfold step; rw [ite_eq_right hc, h]

open Classical in
/-- `step` on an `ask` action. -/
theorem step_eq_ask (M : OTM) (B : Set BitString) (c : Config M) (hc : ¬ Halted M c) {q₁ q₂ : M.Q}
    (h : M.δ c.q (c.tape c.head) = .ask q₁ q₂) :
    step M B c = ⟨if c.buf ∈ B then q₁ else q₂, c.tape, c.head, []⟩ := by
  unfold step; rw [ite_eq_right hc, h]

/-- One step of the machine coded by `m` with the finite oracle `{z | z ∈ ans}`, on codes. -/
def stepC (m : ℕ) (ans : List BitString) (cc : CC) : CC :=
  if haltedB m cc = true then cc else cc.act m (memStr cc.buf ans)

/-- The general step lemma: if the code represents a non-halted configuration and `b` is the
answer of the oracle `B` to the current buffer, the action represents the next configuration. -/
theorem act_represents (m : ℕ) (B : Set BitString) (b : Bool) (cc : CC)
    (c : Config (decodeCode m).toOTM) (h : Rep cc c) (hnh : ¬ Halted (decodeCode m).toOTM c)
    (hb : c.buf ∈ B ↔ b = true) : Rep (cc.act m b) (step (decodeCode m).toOTM B c) := by
  classical
  obtain ⟨hq, ht, hbuf⟩ := h
  set A := actCode m cc.q cc.a with hA
  have hδ : (decodeCode m).toOTM.δ c.q (c.tape c.head) = decodeAct m.unpair.1 A := by
    rw [ht.2.1, hA, hq]; rfl
  by_cases h0 : A % 3 = 0
  · have hδ' := hδ
    rw [decodeAct, ite_eq_left h0] at hδ'
    rw [step_eq_step _ _ _ hnh hδ']
    have hact : cc.act m b = { CC.move ((A / 3).unpair.2 / 3)
        (cc.write (symOf (A / 3).unpair.2)) with q := (A / 3).unpair.1 % codeK m } := by
      simp only [CC.act, ← hA, h0, ite_true]
    rw [hact]
    exact ⟨rfl, tapeRep_move (tapeRep_write ht (symOf (A / 3).unpair.2)) ((A / 3).unpair.2 / 3),
      by rw [CC.move_buf]; exact hbuf⟩
  · by_cases h1 : A % 3 = 1
    · have hδ' := hδ
      rw [decodeAct, ite_eq_right h0, ite_eq_left h1] at hδ'
      rw [step_eq_push _ _ _ hnh hδ']
      have hact : cc.act m b = ⟨(A / 3).unpair.1 % codeK m, cc.L, cc.a, cc.R, cc.hp, cc.hn,
          cc.buf ++ [decide ((A / 3).unpair.2 % 2 = 1)]⟩ := by
        simp only [CC.act, ← hA]
        rw [ite_eq_right h0, ite_eq_left h1]
      rw [hact]
      exact ⟨rfl, ht, by rw [hbuf]⟩
    · have hδ' := hδ
      rw [decodeAct, ite_eq_right h0, ite_eq_right h1] at hδ'
      rw [step_eq_ask _ _ _ hnh hδ']
      have hact : cc.act m b = ⟨(bif b then (A / 3).unpair.1 else (A / 3).unpair.2) % codeK m,
          cc.L, cc.a, cc.R, cc.hp, cc.hn, []⟩ := by
        simp only [CC.act, ← hA]
        rw [ite_eq_right h0, ite_eq_right h1]
      rw [hact]
      refine ⟨?_, ht, rfl⟩
      by_cases hB : c.buf ∈ B
      · have hbt : b = true := hb.1 hB
        subst hbt
        simp only [hB, Bool.cond_true]
        try rfl
      · have hbf : b = false := by
          cases b
          · rfl
          · exact absurd (hb.2 rfl) hB
        subst hbf
        simp only [hB, Bool.cond_false]
        try rfl

/-- A configuration is halted if and only if the encoded machine is halted. -/
theorem haltedB_iff (m : ℕ) (cc : CC) (c : Config (decodeCode m).toOTM) (h : Rep cc c) :
    haltedB m cc = true ↔ Halted (decodeCode m).toOTM c := by
  obtain ⟨hq, -, -⟩ := h
  constructor
  · intro hh
    simp only [haltedB, Bool.or_eq_true, decide_eq_true_eq] at hh
    rcases hh with hh | hh
    · left; exact Fin.ext (hq.symm.trans hh)
    · right; exact Fin.ext (hq.symm.trans hh)
  · rintro (hh | hh)
    · simp only [haltedB, Bool.or_eq_true, decide_eq_true_eq]; left; rw [hq, hh]; rfl
    · simp only [haltedB, Bool.or_eq_true, decide_eq_true_eq]; right; rw [hq, hh]; rfl

/-- Taking a step on a configuration code correctly represents taking a step on the machine. -/
theorem stepC_represents (m : ℕ) (ans : List BitString) (cc : CC) (c : Config (decodeCode m).toOTM)
    (h : Rep cc c) : Rep (stepC m ans cc) (step (decodeCode m).toOTM {z | z ∈ ans} c) := by
  by_cases hh : Halted (decodeCode m).toOTM c
  · rw [step_of_halted _ _ _ hh]
    simp only [stepC, (haltedB_iff m cc c h).2 hh, ite_true]
    exact h
  · have hf : ¬ haltedB m cc = true := fun h' => hh ((haltedB_iff m cc c h).1 h')
    simp only [stepC, hf]
    refine act_represents m _ _ cc c h hh ?_
    rw [memStr_iff, ← h.2.2]
    rfl

/-! ### Runs on codes -/

/-- The code of the initial configuration on input `x`. -/
def initC (m : ℕ) (x : BitString) : CC := ⟨codeStart m, [], x[0]?, x.tail.map some, 0, 0, []⟩

/-- Looking up an index in an optionally mapped list is equivalent to an optional get
on the list. -/
theorem getD_map_some (l : List Bool) (i : ℕ) : (l.map some).getD i none = l[i]? := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-- The initial configuration code correctly represents the initial state of the encoded machine. -/
theorem initC_represents (m : ℕ) (x : BitString) :
    Rep (initC m x) (init (decodeCode m).toOTM x) := by
  refine ⟨rfl, ⟨by simp [init, initC], by simp [init, initC], fun i => ?_, fun i => ?_⟩, rfl⟩
  · simp only [init, initC]
    rw [ite_eq_right (by omega)]; simp
  · simp only [init, initC]
    rw [ite_eq_left (by omega), show (0 + 1 + (i : ℤ)).toNat = i + 1 by omega, getD_map_some]
    cases x <;> simp

/-- The code of the configuration after `t` steps with the finite oracle `{z | z ∈ ans}`. -/
def runC (m : ℕ) (ans : List BitString) (x : BitString) : ℕ → CC
  | 0 => initC m x
  | t + 1 => stepC m ans (runC m ans x t)

/-- Running a configuration code correctly represents running the machine. -/
theorem runC_represents (m : ℕ) (ans : List BitString) (x : BitString) (t : ℕ) :
    Rep (runC m ans x t) (run (decodeCode m).toOTM {z | z ∈ ans} x t) := by
  induction t with
  | zero => exact initC_represents m x
  | succ t ih => exact stepC_represents m ans _ _ ih

/-! ### `ℕ`-codes of configurations -/

/-- Decoding a configuration code (total). -/
def decodeCC (n : ℕ) : CC := (Encodable.decode n).getD default

/-- Decoding the encoding of a configuration code returns the original code. -/
theorem decodeCC_encode (cc : CC) : decodeCC (Encodable.encode cc) = cc := by
  simp [decodeCC, Encodable.encodek]

/-- The `ℕ`-code `n` represents the configuration `c` of the machine coded by `m`. -/
def Represents (m : ℕ) (n : ℕ) (c : Config (decodeCode m).toOTM) : Prop := Rep (decodeCC n) c

/-- One step on `ℕ`-codes. -/
def stepCode (m : ℕ) (ans : List BitString) (n : ℕ) : ℕ :=
  Encodable.encode (stepC m ans (decodeCC n))

/-- The run on `ℕ`-codes. -/
def runCode (m : ℕ) (ans : List BitString) (x : BitString) (t : ℕ) : ℕ :=
  Encodable.encode (runC m ans x t)

/-- Taking a step on a numeric configuration code correctly represents taking a step on
the machine. -/
theorem stepCode_represents (m : ℕ) (ans : List BitString) (n : ℕ) (c : Config (decodeCode m).toOTM)
    (h : Represents m n c) :
    Represents m (stepCode m ans n) (step (decodeCode m).toOTM {z | z ∈ ans} c) := by
  unfold Represents stepCode
  rw [decodeCC_encode]
  exact stepC_represents m ans _ c h

/-- Running a numeric configuration code correctly represents running the machine. -/
theorem runCode_represents (m : ℕ) (ans : List BitString) (x : BitString) (t : ℕ) :
    Represents m (runCode m ans x t) (run (decodeCode m).toOTM {z | z ∈ ans} x t) := by
  unfold Represents runCode
  rw [decodeCC_encode]
  exact runC_represents m ans x t

/-! ### Clocked verdicts -/

/-- The verdict within `T` steps of the coded machine `decodeCode m` with the finite oracle. -/
def clockedOutcomeT (m T : ℕ) (ans : List BitString) (x : BitString) : Bool :=
  (List.range (T + 1)).foldr
    (fun t b => decide ((runC m ans x t).q = codeAcc m) || b) false

/-- The verdict of the clocked coded machine `(decodeCode m, e)` with the finite oracle. -/
def clockedOutcome (m e : ℕ) (ans : List BitString) (x : BitString) : Bool :=
  (List.range (clock e x.length + 1)).foldr
    (fun t b => decide ((runC m ans x t).q = codeAcc m) || b) false

/-- The clocked outcome is equal to the outcome bounded by the clock for the given size. -/
theorem clockedOutcome_eq_T (m e : ℕ) (ans : List BitString) (x : BitString) :
    clockedOutcome m e ans x = clockedOutcomeT m (clock e x.length) ans x := rfl

/-- A right fold with boolean or over a list evaluates to true if and only if the predicate holds
for some element. -/
theorem foldr_or_iff (l : List ℕ) (p : ℕ → Bool) :
    l.foldr (fun t b => p t || b) false = true ↔ ∃ t ∈ l, p t = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.foldr_cons, ih]

/-- The clocked outcome up to bound `T` evaluates to true if and only if the machine accepts
within `T` steps. -/
theorem clockedOutcomeT_iff (m T : ℕ) (ans : List BitString) (x : BitString) :
    clockedOutcomeT m T ans x = true ↔ ClockedAcceptsT (decodeCode m) T {z | z ∈ ans} x := by
  unfold clockedOutcomeT ClockedAcceptsT
  rw [foldr_or_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨t, Nat.lt_succ_iff.1 (List.mem_range.1 ht), ?_⟩
    have hr := (runC_represents m ans x t).1
    simp only [decide_eq_true_eq] at h
    exact Fin.ext (hr.symm.trans h)
  · rintro ⟨t, ht, h⟩
    refine ⟨t, List.mem_range.2 (Nat.lt_succ_of_le ht), ?_⟩
    have hr := (runC_represents m ans x t).1
    simp only [decide_eq_true_eq]
    rw [hr, h]; rfl

/-- The clocked outcome evaluates to true if and only if the machine accepts within its
clocked time. -/
theorem clockedOutcome_iff (m e : ℕ) (ans : List BitString) (x : BitString) :
    clockedOutcome m e ans x = true ↔ ClockedAccepts (decodeCode m) e {z | z ∈ ans} x :=
  clockedOutcomeT_iff m (clock e x.length) ans x

/-! ### The possible queries -/

/-- Lookup of a recorded oracle answer. -/
def lookupB (z : BitString) (rec : List (BitString × Bool)) : Option Bool :=
  rec.foldr (fun r o => if r.1 = z then some r.2 else o) none

/-- The code is about to ask its buffer. -/
def askB (m : ℕ) (cc : CC) : Bool := !haltedB m cc && decide (actCode m cc.q cc.a % 3 = 2)

/-- Successors in the exploration of all consistent oracle answers: a recorded answer is reused,
an unrecorded query branches into both answers (and records them). -/
def succs (m : ℕ) (p : CC × List (BitString × Bool)) : List (CC × List (BitString × Bool)) :=
  if askB m p.1 = true then
    match lookupB p.1.buf p.2 with
    | some b => [(p.1.act m b, p.2)]
    | none => [(p.1.act m true, p.2 ++ [(p.1.buf, true)]),
               (p.1.act m false, p.2 ++ [(p.1.buf, false)])]
  else [(stepC m [] p.1, p.2)]

/-- The explored configurations (with their recorded answers) at depth `s`. -/
def explore (m : ℕ) (x : BitString) : ℕ → List (CC × List (BitString × Bool))
  | 0 => [(initC m x, [])]
  | s + 1 => (explore m x s).flatMap (succs m)

/-- All strings that the coded machine `decodeCode m` can query on `x` within `T` steps. -/
def queryListCodeT (m T : ℕ) (x : BitString) : List BitString :=
  (List.range T).flatMap fun s =>
    (explore m x s).flatMap fun p => bif askB m p.1 then [p.1.buf] else []

/-- All strings that the clocked coded machine `(decodeCode m, e)` can query on `x`. -/
def queryListCode (m e : ℕ) (x : BitString) : List BitString :=
  (List.range (clock e x.length)).flatMap fun s =>
    (explore m x s).flatMap fun p => bif askB m p.1 then [p.1.buf] else []

/-- Looking up a recorded boolean answer returns `some b` only if the pair `(z, b)` is
in the list. -/
theorem lookupB_eq_some {z : BitString} {rec : List (BitString × Bool)} {b : Bool}
    (h : lookupB z rec = some b) : (z, b) ∈ rec := by
  induction rec with
  | nil => simp [lookupB] at h
  | cons r rec ih =>
    have e : lookupB z (r :: rec) = if r.1 = z then some r.2 else lookupB z rec := rfl
    rw [e] at h
    by_cases hr : r.1 = z
    · rw [ite_eq_left hr, Option.some.injEq] at h
      exact List.mem_cons.2 (Or.inl (Prod.ext hr.symm h.symm))
    · rw [ite_eq_right hr] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Looking up a recorded boolean answer returns `none` if and only if the string was not asked. -/
theorem lookupB_eq_none {z : BitString} {rec : List (BitString × Bool)} (h : lookupB z rec = none) :
    ∀ r ∈ rec, r.1 ≠ z := by
  induction rec with
  | nil => simp
  | cons r rec ih =>
    have e : lookupB z (r :: rec) = if r.1 = z then some r.2 else lookupB z rec := rfl
    rw [e] at h
    by_cases hr : r.1 = z
    · rw [ite_eq_left hr] at h; simp at h
    · rw [ite_eq_right hr] at h
      intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact hr
      · exact ih h r' hr'

/-- The string asked at a represented configuration. -/
theorem askedAt_eq_of_rep (m : ℕ) (cc : CC) (c : Config (decodeCode m).toOTM) (h : Rep cc c) :
    askedAt (decodeCode m).toOTM c = bif askB m cc then some cc.buf else none := by
  have hδ : (decodeCode m).toOTM.δ c.q (c.tape c.head) =
      decodeAct m.unpair.1 (actCode m cc.q cc.a) := by
    rw [h.2.1.2.1, h.1]; rfl
  unfold askedAt askB
  by_cases hh : Halted (decodeCode m).toOTM c
  · have hb : haltedB m cc = true := (haltedB_iff m cc c h).2 hh
    rw [ite_eq_left hh, hb]; rfl
  · have hb : haltedB m cc = false := by
      cases hb' : haltedB m cc
      · rfl
      · exact absurd ((haltedB_iff m cc c h).1 hb') hh
    rw [ite_eq_right hh, hb, hδ, ← h.2.2]
    unfold decodeAct
    by_cases h0 : actCode m cc.q cc.a % 3 = 0
    · rw [ite_eq_left h0]; simp [h0]
    · by_cases h1 : actCode m cc.q cc.a % 3 = 1
      · rw [ite_eq_right h0, ite_eq_left h1]; simp [h1]
      · rw [ite_eq_right h0, ite_eq_right h1]
        have h2 : actCode m cc.q cc.a % 3 = 2 := by omega
        simp [h2]

/-- A step that does not ask does not depend on the oracle. -/
theorem rep_step_noask (m : ℕ) (B : Set BitString) (cc : CC) (c : Config (decodeCode m).toOTM)
    (h : Rep cc c) (ha : askB m cc = false) :
    Rep (stepC m [] cc) (step (decodeCode m).toOTM B c) := by
  have hstep : step (decodeCode m).toOTM B c =
      step (decodeCode m).toOTM {z | z ∈ ([] : List BitString)} c := by
    apply step_eq_of_agree
    intro z hz
    rw [askedAt_eq_of_rep m cc c h, ha] at hz
    simp at hz
  rw [hstep]
  exact stepC_represents m [] cc c h

/-- Recorded answers agree with an oracle. -/
def Agrees (B : Set BitString) (rec : List (BitString × Bool)) : Prop :=
  ∀ r ∈ rec, (r.1 ∈ B ↔ r.2 = true)

/-- Each string is recorded with at most one answer. -/
def Functional (rec : List (BitString × Bool)) : Prop :=
  ∀ r ∈ rec, ∀ r' ∈ rec, r.1 = r'.1 → r.2 = r'.2

/-- Appending a new consistent pair to a functional list maintains its functionality. -/
theorem functional_append (rec : List (BitString × Bool)) (z : BitString) (b : Bool)
    (hf : Functional rec)
    (hz : ∀ r ∈ rec, r.1 ≠ z) : Functional (rec ++ [(z, b)]) := by
  intro r hr r' hr' he
  rcases List.mem_append.1 hr with hr | hr <;> rcases List.mem_append.1 hr' with hr' | hr'
  · exact hf r hr r' hr' he
  · rw [List.mem_singleton] at hr'; subst hr'; exact absurd he (hz r hr)
  · rw [List.mem_singleton] at hr; subst hr; exact absurd he.symm (hz r' hr')
  · rw [List.mem_singleton] at hr hr'; subst hr; subst hr'; rfl

/-- A configuration that issues a query is not in a halted state. -/
theorem not_halted_of_askB (m : ℕ) (cc : CC) (c : Config (decodeCode m).toOTM) (h : Rep cc c)
    (ha : askB m cc = true) : ¬ Halted (decodeCode m).toOTM c := by
  intro hH
  have := (haltedB_iff m cc c h).2 hH
  simp [askB, this] at ha

/-- Soundness of the exploration: the recorded answers are consistent, and every oracle agreeing
with them follows the explored branch. -/
theorem explore_sound (m : ℕ) (x : BitString) (s : ℕ) :
    ∀ p ∈ explore m x s, Functional p.2 ∧
      ∀ B : Set BitString, Agrees B p.2 → Rep p.1 (run (decodeCode m).toOTM B x s) := by
  induction s with
  | zero =>
    intro p hp
    simp only [explore, List.mem_singleton] at hp
    subst hp
    exact ⟨by simp [Functional], fun B _ => initC_represents m x⟩
  | succ s ih =>
    intro p' hp'
    simp only [explore, List.mem_flatMap] at hp'
    obtain ⟨p, hp, hp'⟩ := hp'
    obtain ⟨hfun, hrep⟩ := ih p hp
    unfold succs at hp'
    by_cases ha : askB m p.1 = true
    · rw [ite_eq_left ha] at hp'
      rcases hl : lookupB p.1.buf p.2 with _ | b
      · rw [hl] at hp'
        have hnone := lookupB_eq_none hl
        have hcase : ∀ b : Bool, p' = (p.1.act m b, p.2 ++ [(p.1.buf, b)]) →
            Functional p'.2 ∧ ∀ B : Set BitString, Agrees B p'.2 →
              Rep p'.1 (run (decodeCode m).toOTM B x (s + 1)) := by
          intro b hb
          subst hb
          refine ⟨functional_append _ _ _ hfun hnone, fun B hB => ?_⟩
          have hB' : Agrees B p.2 := fun r hr => hB r (List.mem_append_left _ hr)
          have hans := hB (p.1.buf, b) (List.mem_append_right _ (List.mem_singleton_self _))
          exact act_represents m B b p.1 _ (hrep B hB') (not_halted_of_askB m p.1 _ (hrep B hB') ha)
            (by rw [(hrep B hB').2.2]; exact hans)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with h | h
        · exact hcase true h
        · exact hcase false h
      · rw [hl] at hp'
        simp only [List.mem_singleton] at hp'
        subst hp'
        refine ⟨hfun, fun B hB => ?_⟩
        exact act_represents m B b p.1 _ (hrep B hB) (not_halted_of_askB m p.1 _ (hrep B hB) ha)
          (by rw [(hrep B hB).2.2]; exact hB _ (lookupB_eq_some hl))
    · rw [ite_eq_right ha] at hp'
      simp only [List.mem_singleton] at hp'
      subst hp'
      exact ⟨hfun, fun B hB => rep_step_noask m B p.1 _ (hrep B hB) (by simpa using ha)⟩

/-- Completeness of the exploration: every oracle is followed by an explored branch. -/
theorem explore_complete (m : ℕ) (x : BitString) (B : Set BitString) (s : ℕ) :
    ∃ p ∈ explore m x s, Agrees B p.2 ∧ Rep p.1 (run (decodeCode m).toOTM B x s) := by
  classical
  induction s with
  | zero => exact ⟨(initC m x, []), by simp [explore], by simp [Agrees], initC_represents m x⟩
  | succ s ih =>
    obtain ⟨p, hp, hag, hrep⟩ := ih
    have hsucc : ∀ p', p' ∈ succs m p → p' ∈ explore m x (s + 1) := fun p' h' => by
      simp only [explore, List.mem_flatMap]; exact ⟨p, hp, h'⟩
    by_cases ha : askB m p.1 = true
    · have hnh := not_halted_of_askB m p.1 _ hrep ha
      rcases hl : lookupB p.1.buf p.2 with _ | b
      · refine ⟨(p.1.act m (decide (p.1.buf ∈ B)), p.2 ++ [(p.1.buf, decide (p.1.buf ∈ B))]),
          hsucc _ ?_, ?_, ?_⟩
        · unfold succs; rw [ite_eq_left ha, hl]
          cases decide (p.1.buf ∈ B) <;> simp
        · intro r hr
          rcases List.mem_append.1 hr with hr | hr
          · exact hag r hr
          · rw [List.mem_singleton] at hr; subst hr; simp
        · exact act_represents m B _ p.1 _ hrep hnh (by rw [hrep.2.2]; simp)
      · refine ⟨(p.1.act m b, p.2), hsucc _ ?_, hag, ?_⟩
        · unfold succs; rw [ite_eq_left ha, hl]; simp
        · exact act_represents m B b p.1 _ hrep hnh
            (by rw [hrep.2.2]; exact hag _ (lookupB_eq_some hl))
    · refine ⟨(stepC m [] p.1, p.2), hsucc _ ?_, hag, ?_⟩
      · unfold succs; rw [ite_eq_right ha]; simp
      · exact rep_step_noask m B p.1 _ hrep (by simpa using ha)

/-- The computed query list coincides with the query list computed up to the proper clock limit. -/
theorem queryListCode_eq_T (m e : ℕ) (x : BitString) :
    queryListCode m e x = queryListCodeT m (clock e x.length) x := rfl

/-- A string belongs to the computed query list if and only if the machine queries it within its
clocked time. -/
theorem mem_queryListCodeT (m T : ℕ) (x : BitString) (z : BitString) :
    z ∈ queryListCodeT m T x ↔ z ∈ queryAll (decodeCode m).toOTM x T := by
  classical
  have key : z ∈ queryListCodeT m T x ↔ ∃ s < T, ∃ p ∈ explore m x s,
      askB m p.1 = true ∧ p.1.buf = z := by
    simp only [queryListCodeT, List.mem_flatMap, List.mem_range]
    constructor
    · rintro ⟨s, hs, p, hp, hz⟩
      cases ha : askB m p.1
      · rw [ha] at hz; simp at hz
      · rw [ha] at hz
        simp only [Bool.cond_true, List.mem_singleton] at hz
        exact ⟨s, hs, p, hp, ha, hz.symm⟩
    · rintro ⟨s, hs, p, hp, ha, rfl⟩
      exact ⟨s, hs, p, hp, by rw [ha]; simp⟩
  rw [key]
  constructor
  · rintro ⟨s, hs, p, hp, ha, rfl⟩
    obtain ⟨hfun, hrep⟩ := explore_sound m x s p hp
    have hB : Agrees {w | (w, true) ∈ p.2} p.2 := by
      intro r hr
      constructor
      · intro hw
        exact (hfun _ hw r hr rfl).symm
      · intro h2
        change (r.1, true) ∈ p.2
        rw [← h2]
        exact hr
    have hask := askedAt_eq_of_rep m p.1 _ (hrep _ hB)
    rw [ha] at hask
    exact ⟨{w | (w, true) ∈ p.2}, (mem_queries _ _ _ _ _).2 ⟨s, hs, by rw [hask]; rfl⟩⟩
  · rintro ⟨B, hB⟩
    obtain ⟨s, hs, hz⟩ := (mem_queries _ _ _ _ _).1 hB
    obtain ⟨p, hp, -, hrep⟩ := explore_complete m x B s
    have hask := askedAt_eq_of_rep m p.1 _ hrep
    rw [hz] at hask
    cases ha : askB m p.1
    · rw [ha] at hask; simp at hask
    · rw [ha] at hask
      simp only [Bool.cond_true, Option.some.injEq] at hask
      exact ⟨s, hs, p, hp, ha, hask.symm⟩

/-- A string belongs to the computed query list if and only if the machine queries it within its
clocked time. -/
theorem mem_queryListCode (m e : ℕ) (x : BitString) (z : BitString) :
    z ∈ queryListCode m e x ↔ z ∈ queryAll (decodeCode m).toOTM x (clock e x.length) :=
  mem_queryListCodeT m (clock e x.length) x z

/-- The query set within `T` steps of a coded machine is the finset of the computed query list. -/
theorem querySet_eq_toFinsetT (m T : ℕ) (x : BitString) :
    querySet (decodeCode m).toOTM x T = (queryListCodeT m T x).toFinset := by
  ext z
  rw [querySet, Set.Finite.mem_toFinset, List.mem_toFinset, mem_queryListCodeT]

/-- The query set of a coded clocked machine is the finset of the computed query list. -/
theorem querySet_eq_toFinset (m e : ℕ) (x : BitString) :
    querySet (decodeCode m).toOTM x (clock e x.length) = (queryListCode m e x).toFinset :=
  querySet_eq_toFinsetT m (clock e x.length) x

/-- The verdict within `T` steps with an arbitrary oracle `B` is computed by `clockedOutcomeT`
from any list `ans` agreeing with `B` on the computed query list. -/
theorem clockedAcceptsT_iff_clockedOutcomeT (m T : ℕ) (x : BitString) (B : Set BitString)
    (ans : List BitString)
    (h : ∀ z ∈ queryListCodeT m T x, (z ∈ B ↔ z ∈ ans)) :
    ClockedAcceptsT (decodeCode m) T B x ↔ clockedOutcomeT m T ans x = true := by
  rw [clockedOutcomeT_iff]
  apply clockedAcceptsT_iff_of_agree
  intro z hz
  rw [querySet_eq_toFinsetT, List.mem_toFinset] at hz
  exact h z hz

/-- The clocked verdict with an arbitrary oracle `B` is computed by `clockedOutcome` from any list
`ans` agreeing with `B` on the computed query list. -/
theorem clockedAccepts_iff_clockedOutcome (m e : ℕ) (x : BitString) (B : Set BitString)
    (ans : List BitString)
    (h : ∀ z ∈ queryListCode m e x, (z ∈ B ↔ z ∈ ans)) :
    ClockedAccepts (decodeCode m) e B x ↔ clockedOutcome m e ans x = true :=
  clockedAcceptsT_iff_clockedOutcomeT m (clock e x.length) x B ans h

/-! ### Primitive recursiveness -/

/-- The projection of the state from a configuration code is primitive recursive. -/
theorem CC.primrec_q : Primrec CC.q :=
  (Primrec.fst.comp (Primrec.of_equiv (e := CC.equiv))).of_eq fun _ => rfl
/-- The projection of the left tape symbols from a configuration code is primitive recursive. -/
theorem CC.primrec_L : Primrec CC.L :=
  ((Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := CC.equiv))).of_eq fun _ => rfl
/-- The projection of the current tape symbol from a configuration code is primitive recursive. -/
theorem CC.primrec_a : Primrec CC.a :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := CC.equiv))).of_eq fun _ => rfl
/-- The projection of the right tape symbols from a configuration code is primitive recursive. -/
theorem CC.primrec_R : Primrec CC.R :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    (Primrec.of_equiv (e := CC.equiv))).of_eq fun _ => rfl
/-- The projection of the positive head position from a configuration code is primitive
recursive. -/
theorem CC.primrec_hp : Primrec CC.hp :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    (Primrec.of_equiv (e := CC.equiv))).of_eq fun _ => rfl
/-- The projection of the negative head position from a configuration code is primitive
recursive. -/
theorem CC.primrec_hn : Primrec CC.hn :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))))).comp (Primrec.of_equiv (e := CC.equiv))).of_eq
    fun _ => rfl
/-- The projection of the query buffer from a configuration code is primitive recursive. -/
theorem CC.primrec_buf : Primrec CC.buf :=
  ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))))).comp (Primrec.of_equiv (e := CC.equiv))).of_eq
    fun _ => rfl

/-- Constructing a configuration code from its components is primitive recursive. -/
theorem CC.primrec_mk {α : Type*} [Primcodable α] {f₁ : α → ℕ} {f₂ : α → List Sym}
    {f₃ : α → Sym} {f₄ : α → List Sym} {f₅ f₆ : α → ℕ} {f₇ : α → BitString} (h₁ : Primrec f₁)
    (h₂ : Primrec f₂) (h₃ : Primrec f₃) (h₄ : Primrec f₄) (h₅ : Primrec f₅) (h₆ : Primrec f₆)
    (h₇ : Primrec f₇) :
    Primrec fun x => CC.mk (f₁ x) (f₂ x) (f₃ x) (f₄ x) (f₅ x) (f₆ x) (f₇ x) :=
  ((Primrec.of_equiv_symm (e := CC.equiv)).comp (h₁.pair (h₂.pair (h₃.pair (h₄.pair
    (h₅.pair (h₆.pair h₇))))))).of_eq fun _ => rfl

/-- Moving the head of a configuration code left is primitive recursive. -/
theorem CC.left_primrec : Primrec CC.left :=
  (CC.primrec_mk CC.primrec_q (Primrec.list_tail.comp CC.primrec_L)
    (Primrec.option_getD.comp (Primrec.list_head?.comp CC.primrec_L) (Primrec.const none))
    (Primrec.list_cons.comp CC.primrec_a CC.primrec_R) CC.primrec_hp
    (Primrec.nat_add.comp CC.primrec_hn (Primrec.const 1)) CC.primrec_buf).of_eq fun cc => by
    rcases cc with ⟨q, _ | ⟨y, L⟩, a, R, hp, hn, buf⟩ <;> rfl

/-- Moving the head of a configuration code right is primitive recursive. -/
theorem CC.right_primrec : Primrec CC.right :=
  (CC.primrec_mk CC.primrec_q (Primrec.list_cons.comp CC.primrec_a CC.primrec_L)
    (Primrec.option_getD.comp (Primrec.list_head?.comp CC.primrec_R) (Primrec.const none))
    (Primrec.list_tail.comp CC.primrec_R)
    (Primrec.nat_add.comp CC.primrec_hp (Primrec.const 1)) CC.primrec_hn CC.primrec_buf).of_eq
    fun cc => by rcases cc with ⟨q, L, a, _ | ⟨y, R⟩, hp, hn, buf⟩ <;> rfl

/-- Writing a symbol onto the tape of a configuration code is primitive recursive. -/
theorem CC.write_primrec : Primrec₂ CC.write :=
  (CC.primrec_mk (CC.primrec_q.comp Primrec.fst) (CC.primrec_L.comp Primrec.fst) Primrec.snd
    (CC.primrec_R.comp Primrec.fst) (CC.primrec_hp.comp Primrec.fst)
    (CC.primrec_hn.comp Primrec.fst) (CC.primrec_buf.comp Primrec.fst)).of_eq fun _ => rfl

/-- Moving the head of a configuration code by a variable displacement is primitive recursive. -/
theorem CC.move_primrec : Primrec₂ fun (n : ℕ) (cc : CC) => cc.move n :=
  (Primrec.ite ((mod3_primrecPred 0).comp Primrec.fst) (CC.left_primrec.comp Primrec.snd)
    (Primrec.ite ((mod3_primrecPred 1).comp Primrec.fst) Primrec.snd
      (CC.right_primrec.comp Primrec.snd))).of_eq fun _ => rfl

/-- Testing whether a configuration code represents a halted state is primitive recursive. -/
theorem haltedB_primrec : Primrec₂ haltedB :=
  (Primrec.or.comp (Primrec.eq.decide.comp (CC.primrec_q.comp Primrec.snd)
      (codeAcc_primrec.comp Primrec.fst))
    (Primrec.eq.decide.comp (CC.primrec_q.comp Primrec.snd)
      (codeRej_primrec.comp Primrec.fst))).of_eq fun _ => rfl

attribute [local irreducible] actCode codeK CC.move CC.write in
/-- Performing a machine action on a configuration code is primitive recursive. -/
theorem CC.act_primrec : Primrec fun p : ℕ × Bool × CC => p.2.2.act p.1 p.2.1 := by
  have hc : Primrec fun p : ℕ × Bool × CC => p.2.2 := Primrec.snd.comp Primrec.snd
  have hA : Primrec fun p : ℕ × Bool × CC => actCode p.1 p.2.2.q p.2.2.a :=
    actCode_primrec.comp (Primrec.fst.pair ((CC.primrec_q.comp hc).pair (CC.primrec_a.comp hc)))
  have hd : Primrec fun p : ℕ × Bool × CC => (actCode p.1 p.2.2.q p.2.2.a / 3).unpair :=
    Primrec.unpair.comp (Primrec.nat_div.comp hA (Primrec.const 3))
  have hu1 := Primrec.fst.comp hd
  have hu2 := Primrec.snd.comp hd
  have hK : Primrec fun p : ℕ × Bool × CC => codeK p.1 := codeK_primrec.comp Primrec.fst
  have hX : Primrec fun p : ℕ × Bool × CC =>
      CC.move ((actCode p.1 p.2.2.q p.2.2.a / 3).unpair.2 / 3)
        (p.2.2.write (symOf (actCode p.1 p.2.2.q p.2.2.a / 3).unpair.2)) :=
    CC.move_primrec.comp (Primrec.nat_div.comp hu2 (Primrec.const 3))
      (CC.write_primrec.comp hc (symOf_primrec.comp hu2))
  have b0 := CC.primrec_mk (Primrec.nat_mod.comp hu1 hK) (CC.primrec_L.comp hX)
    (CC.primrec_a.comp hX) (CC.primrec_R.comp hX) (CC.primrec_hp.comp hX)
    (CC.primrec_hn.comp hX) (CC.primrec_buf.comp hX)
  have b1 := CC.primrec_mk (Primrec.nat_mod.comp hu1 hK) (CC.primrec_L.comp hc)
    (CC.primrec_a.comp hc) (CC.primrec_R.comp hc) (CC.primrec_hp.comp hc)
    (CC.primrec_hn.comp hc) (Primrec.list_concat.comp (CC.primrec_buf.comp hc)
      (Primrec.eq.decide.comp (Primrec.nat_mod.comp hu2 (Primrec.const 2)) (Primrec.const 1)))
  have b2 := CC.primrec_mk (Primrec.nat_mod.comp (Primrec.cond (Primrec.fst.comp Primrec.snd)
      hu1 hu2) hK) (CC.primrec_L.comp hc)
    (CC.primrec_a.comp hc) (CC.primrec_R.comp hc) (CC.primrec_hp.comp hc)
    (CC.primrec_hn.comp hc) (Primrec.const [])
  have c0 : PrimrecPred fun p : ℕ × Bool × CC => actCode p.1 p.2.2.q p.2.2.a % 3 = 0 :=
    (mod3_primrecPred 0).comp hA
  have c1 : PrimrecPred fun p : ℕ × Bool × CC => actCode p.1 p.2.2.q p.2.2.a % 3 = 1 :=
    (mod3_primrecPred 1).comp hA
  refine (Primrec.ite c0 b0 (Primrec.ite c1 b1 b2)).of_eq fun p => ?_
  unfold CC.act
  rfl

/-- Checking if a string belongs to a list of answers is primitive recursive. -/
theorem memStr_primrec : Primrec₂ memStr :=
  (Primrec.list_foldr (f := fun a : BitString × List BitString => a.2) (g := fun _ => false)
    (h := fun a wb => decide (wb.1 = a.1) || wb.2) Primrec.snd (Primrec.const false)
    (Primrec.or.comp (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

attribute [local irreducible] CC.act haltedB memStr in
/-- Executing a single step on a configuration code is primitive recursive. -/
theorem stepC_primrec : Primrec fun p : ℕ × List BitString × CC => stepC p.1 p.2.1 p.2.2 := by
  have hc : Primrec fun p : ℕ × List BitString × CC => p.2.2 := Primrec.snd.comp Primrec.snd
  have hh : PrimrecPred fun p : ℕ × List BitString × CC => haltedB p.1 p.2.2 = true :=
    Primrec.eq.comp (haltedB_primrec.comp Primrec.fst hc) (Primrec.const true)
  have hact : Primrec fun p : ℕ × List BitString × CC => p.2.2.act p.1 (memStr p.2.2.buf p.2.1) :=
    CC.act_primrec.comp (Primrec.fst.pair ((memStr_primrec.comp (CC.primrec_buf.comp hc)
      (Primrec.fst.comp Primrec.snd)).pair hc))
  refine (Primrec.ite hh hc hact).of_eq fun p => ?_
  unfold stepC
  rfl

/-- Constructing the initial configuration code for a given input is primitive recursive. -/
theorem initC_primrec : Primrec₂ initC :=
  (CC.primrec_mk (codeStart_primrec.comp Primrec.fst) (Primrec.const [])
    (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0))
    (Primrec.list_map (Primrec.list_tail.comp Primrec.snd) (Primrec.option_some.comp
      Primrec.snd).to₂) (Primrec.const 0) (Primrec.const 0) (Primrec.const [])).of_eq
    fun _ => rfl

/-- Running a configuration code for a specific number of steps is primitive recursive. -/
theorem runC_primrec :
    Primrec fun p : ℕ × List BitString × BitString × ℕ => runC p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have h := Primrec.nat_rec' (f := fun p : ℕ × List BitString × BitString × ℕ => p.2.2.2)
    (g := fun p => initC p.1 p.2.2.1)
    (h := fun p (q : ℕ × CC) => stepC p.1 p.2.1 q.2)
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (initC_primrec.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (stepC_primrec.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp
      (Primrec.snd.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.snd)))).to₂
  refine h.of_eq fun p => ?_
  obtain ⟨m, ans, x, t⟩ := p
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg (stepC m ans) ih

/-- Decoding a numeric representation into a configuration code is primitive recursive. -/
theorem decodeCC_primrec : Primrec decodeCC :=
  (Primrec.option_getD.comp Primrec.decode (Primrec.const default)).of_eq fun _ => rfl

/-- Computing the next numeric state of a configuration code is primitive recursive. -/
theorem stepCode_primrec : Primrec fun p : ℕ × List BitString × ℕ => stepCode p.1 p.2.1 p.2.2 :=
  (Primrec.encode.comp (stepC_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp
    Primrec.snd).pair (decodeCC_primrec.comp (Primrec.snd.comp Primrec.snd)))))).of_eq
    fun _ => rfl

/-- Running a numeric configuration code for a number of steps is primitive recursive. -/
theorem runCode_primrec :
    Primrec fun p : ℕ × List BitString × BitString × ℕ => runCode p.1 p.2.1 p.2.2.1 p.2.2.2 :=
  (Primrec.encode.comp runC_primrec).of_eq fun _ => rfl

/-- The clock bounds function is primitive recursive. -/
theorem clock_primrec : Primrec₂ clock :=
  (Primrec.nat_add.comp ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp Primrec.snd Primrec.fst)
    Primrec.fst).of_eq fun _ => rfl

/-- The clock bounds function is computable. -/
theorem clock_computable : Computable₂ clock := clock_primrec.to_comp

/-- The exponential bound calculation based on the clock is primitive recursive. -/
theorem clkE_primrec : Primrec₂ clkE :=
  ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
    (clock_primrec : Primrec fun p : ℕ × ℕ => clock p.1 p.2)).of_eq fun _ => rfl

/-- The exponential bound calculation based on the clock is computable. -/
theorem clkE_computable : Computable₂ clkE := clkE_primrec.to_comp

/-- The evaluation of the clocked outcome up to bounded time `T` is primitive recursive. -/
theorem clockedOutcomeT_primrec :
    Primrec fun p : ℕ × ℕ × List BitString × BitString =>
      clockedOutcomeT p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hT : Primrec fun p : ℕ × ℕ × List BitString × BitString => p.2.1 + 1 :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have hrun : Primrec fun q : (ℕ × ℕ × List BitString × BitString) × ℕ =>
      runC q.1.1 q.1.2.2.1 q.1.2.2.2 q.2 :=
    runC_primrec.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))).pair ((Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)))
  exact (Primrec.list_foldr (Primrec.list_range.comp hT) (Primrec.const false)
    (Primrec.or.comp (Primrec.eq.decide.comp (CC.primrec_q.comp (hrun.comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))))
      (codeAcc_primrec.comp (Primrec.fst.comp Primrec.fst))) (Primrec.snd.comp
        Primrec.snd)).to₂).of_eq fun _ => rfl

/-- The evaluation of the clocked outcome is primitive recursive. -/
theorem clockedOutcome_primrec :
    Primrec fun p : ℕ × ℕ × List BitString × BitString =>
      clockedOutcome p.1 p.2.1 p.2.2.1 p.2.2.2 :=
  (clockedOutcomeT_primrec.comp (Primrec.fst.pair ((clock_primrec.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.list_length.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).pair
        (Primrec.snd.comp Primrec.snd)))).of_eq fun _ => rfl

/-- The lookup of recorded boolean answers from an oracle trace is primitive recursive. -/
theorem lookupB_primrec : Primrec₂ lookupB :=
  (Primrec.list_foldr (f := fun a : BitString × List (BitString × Bool) => a.2) (g := fun _ => none)
    (h := fun a ro => if ro.1.1 = a.1 then some ro.1.2 else ro.2) Primrec.snd
    (Primrec.const none)
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp Primrec.fst))
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- Testing whether a configuration queries the oracle is primitive recursive. -/
theorem askB_primrec : Primrec₂ askB :=
  (Primrec.and.comp (Primrec.not.comp haltedB_primrec)
    ((mod3_primrecPred 2).decide.comp (actCode_primrec.comp (Primrec.fst.pair
      ((CC.primrec_q.comp Primrec.snd).pair (CC.primrec_a.comp Primrec.snd)))))).of_eq
    fun _ => rfl

attribute [local irreducible] CC.act stepC askB lookupB in
/-- Computing the successor exploration configurations from a given state is primitive recursive. -/
theorem succs_primrec : Primrec₂ succs := by
  have hcc : Primrec fun a : ℕ × (CC × List (BitString × Bool)) => a.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hrec : Primrec fun a : ℕ × (CC × List (BitString × Bool)) => a.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hact : ∀ b : Bool, Primrec fun a : ℕ × (CC × List (BitString × Bool)) => a.2.1.act a.1 b :=
    fun b => CC.act_primrec.comp (Primrec.fst.pair ((Primrec.const b).pair hcc))
  have hbuf : Primrec fun a : ℕ × (CC × List (BitString × Bool)) => a.2.1.buf :=
    CC.primrec_buf.comp hcc
  have hsome : Primrec₂ fun (a : ℕ × (CC × List (BitString × Bool))) (b : Bool) =>
      [(a.2.1.act a.1 b, a.2.2)] :=
    (Primrec.list_cons.comp ((CC.act_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.pair (hcc.comp Primrec.fst)))).pair (hrec.comp Primrec.fst))
      (Primrec.const [])).to₂
  have hnone : Primrec fun a : ℕ × (CC × List (BitString × Bool)) =>
      [(a.2.1.act a.1 true, a.2.2 ++ [(a.2.1.buf, true)]),
        (a.2.1.act a.1 false, a.2.2 ++ [(a.2.1.buf, false)])] :=
    Primrec.list_cons.comp ((hact true).pair (Primrec.list_concat.comp hrec
      (hbuf.pair (Primrec.const true)))) (Primrec.list_cons.comp ((hact false).pair
        (Primrec.list_concat.comp hrec (hbuf.pair (Primrec.const false)))) (Primrec.const []))
  have hask : PrimrecPred fun a : ℕ × (CC × List (BitString × Bool)) => askB a.1 a.2.1 = true :=
    Primrec.eq.comp (askB_primrec.comp Primrec.fst hcc) (Primrec.const true)
  have hstep : Primrec fun a : ℕ × (CC × List (BitString × Bool)) =>
      [(stepC a.1 [] a.2.1, a.2.2)] :=
    Primrec.list_cons.comp ((stepC_primrec.comp (Primrec.fst.pair ((Primrec.const []).pair
      hcc))).pair hrec) (Primrec.const [])
  refine (Primrec.ite hask (Primrec.option_casesOn (lookupB_primrec.comp hbuf hrec) hnone hsome)
    hstep).of_eq fun a => ?_
  unfold succs
  by_cases h : askB a.1 a.2.1 = true
  · rw [ite_eq_left h, ite_eq_left h]
    rcases lookupB a.2.1.buf a.2.2 with _ | b <;> rfl
  · rw [ite_eq_right h, ite_eq_right h]

/-- Computing the complete list of possible execution traces for `s` steps is primitive
recursive. -/
theorem explore_primrec : Primrec fun p : ℕ × BitString × ℕ => explore p.1 p.2.1 p.2.2 := by
  have h := Primrec.nat_rec' (f := fun p : ℕ × BitString × ℕ => p.2.2)
    (g := fun p => [(initC p.1 p.2.1, ([] : List (BitString × Bool)))])
    (h := fun p (q : ℕ × List (CC × List (BitString × Bool))) => q.2.flatMap (succs p.1))
    (Primrec.snd.comp Primrec.snd)
    (Primrec.list_cons.comp ((initC_primrec.comp Primrec.fst (Primrec.fst.comp
      Primrec.snd)).pair (Primrec.const [])) (Primrec.const []))
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (succs_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂).to₂
  refine h.of_eq fun p => ?_
  obtain ⟨m, x, s⟩ := p
  induction s with
  | zero => rfl
  | succ s ih => exact congrArg (fun L => L.flatMap (succs m)) ih

/-- Computing the list of queries issued within `T` steps over all traces is primitive recursive. -/
theorem queryListCodeT_primrec :
    Primrec fun p : ℕ × ℕ × BitString => queryListCodeT p.1 p.2.1 p.2.2 := by
  have hT : Primrec fun p : ℕ × ℕ × BitString => p.2.1 := Primrec.fst.comp Primrec.snd
  have hex : Primrec fun q : (ℕ × ℕ × BitString) × ℕ => explore q.1.1 q.1.2.2 q.2 :=
    explore_primrec.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  have hinner : Primrec₂ fun (q : (ℕ × ℕ × BitString) × ℕ) (pr : CC × List (BitString × Bool)) =>
      bif askB q.1.1 pr.1 then [pr.1.buf] else [] :=
    (Primrec.cond (askB_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)) (Primrec.list_cons.comp (CC.primrec_buf.comp
        (Primrec.fst.comp Primrec.snd)) (Primrec.const [])) (Primrec.const [])).to₂
  exact (Primrec.list_flatMap (Primrec.list_range.comp hT)
    (Primrec.list_flatMap hex hinner).to₂).of_eq fun _ => rfl

/-- Computing the list of queries issued within the machine's clocked time is primitive
recursive. -/
theorem queryListCode_primrec :
    Primrec fun p : ℕ × ℕ × BitString => queryListCode p.1 p.2.1 p.2.2 :=
  (queryListCodeT_primrec.comp (Primrec.fst.pair ((clock_primrec.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.list_length.comp
      (Primrec.snd.comp Primrec.snd))).pair (Primrec.snd.comp Primrec.snd)))).of_eq fun _ => rfl

end Kolmogorov.RandomStrings
