/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Machines
import KolmogorovMathlib.RandomStrings.Game
import KolmogorovMathlib.RandomStrings.Clocks

/-!
# Codes of oracle machines

Symbols, moves and actions as natural numbers; the codes of machines (`encodeCode`,
`decodeCode`, the computable surjection `γ₀ : ℕ → OTMCode × ℕ`); primitive recursiveness of the
code components; and the code of a machine given by an effective table.

Part of `KolmogorovMathlib.RandomStrings.Effective`.
-/

namespace Kolmogorov.RandomStrings

/-! ### Symbols, moves, actions -/

/-- Index of a tape symbol. -/
def symIdx : Sym → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- The symbol of index `n mod 3`. -/
def symOf (n : ℕ) : Sym := if n % 3 = 0 then none else if n % 3 = 1 then some false else some true

/-- The move of index `n mod 3` (`left, stay, right`, as in `Move.toNat`). -/
def moveOf (n : ℕ) : Move := if n % 3 = 0 then .left else if n % 3 = 1 then .stay else .right

/-- The index of a tape symbol is strictly less than `3`. -/
theorem symIdx_lt (s : Sym) : symIdx s < 3 := by
  rcases s with _ | _ | _ <;> decide

/-- A tape symbol is retrieved from its index. -/
theorem symOf_symIdx (s : Sym) : symOf (symIdx s) = s := by
  rcases s with _ | _ | _ <;> rfl

/-- The symbol of index `n` is the same as the symbol of index `n mod 3`. -/
theorem symOf_mod (n : ℕ) : symOf n = symOf (n % 3) := by
  simp only [symOf, Nat.mod_mod]

/-- The index of a move is strictly less than `3`. -/
theorem Move.toNat_lt (mv : Move) : mv.toNat < 3 := by
  cases mv <;> decide

/-- A move is retrieved from its index. -/
theorem moveOf_toNat (mv : Move) : moveOf mv.toNat = mv := by
  cases mv <;> rfl

/-- Code of an action. -/
def encodeAct {k : ℕ} : Act (Fin k) → ℕ
  | .step q s mv => 3 * Nat.pair q (symIdx s + 3 * mv.toNat)
  | .push q b => 3 * Nat.pair q (if b then 1 else 0) + 1
  | .ask q₁ q₂ => 3 * Nat.pair q₁ q₂ + 2

/-- Decoding of an action for `k + 1` states (components reduced modulo their ranges). -/
def decodeAct (k : ℕ) (a : ℕ) : Act (Fin (k + 1)) :=
  if a % 3 = 0 then
    .step ⟨(a / 3).unpair.1 % (k + 1), Nat.mod_lt _ k.succ_pos⟩ (symOf (a / 3).unpair.2)
      (moveOf ((a / 3).unpair.2 / 3))
  else if a % 3 = 1 then
    .push ⟨(a / 3).unpair.1 % (k + 1), Nat.mod_lt _ k.succ_pos⟩
      (decide ((a / 3).unpair.2 % 2 = 1))
  else
    .ask ⟨(a / 3).unpair.1 % (k + 1), Nat.mod_lt _ k.succ_pos⟩
      ⟨(a / 3).unpair.2 % (k + 1), Nat.mod_lt _ k.succ_pos⟩

/-- Encoding and decoding are inverse on actions for `k + 1` states. -/
theorem decodeAct_encodeAct (k : ℕ) (a : Act (Fin (k + 1))) :
    decodeAct k (encodeAct a) = a := by
  have hfin : ∀ q : Fin (k + 1),
      (⟨q.val % (k + 1), Nat.mod_lt _ k.succ_pos⟩ : Fin (k + 1)) = q :=
    fun q => Fin.ext (Nat.mod_eq_of_lt q.isLt)
  cases a with
  | step q s mv =>
    have h3 : symOf (symIdx s + 3 * mv.toNat) = s := by
      rw [symOf_mod]
      have : (symIdx s + 3 * mv.toNat) % 3 = symIdx s := by
        have := symIdx_lt s; omega
      rw [this, symOf_symIdx]
    have h4 : moveOf ((symIdx s + 3 * mv.toNat) / 3) = mv := by
      have : (symIdx s + 3 * mv.toNat) / 3 = mv.toNat := by
        have := symIdx_lt s; omega
      rw [this, moveOf_toNat]
    change decodeAct k (3 * Nat.pair q (symIdx s + 3 * mv.toNat)) = _
    have e1 : 3 * Nat.pair (↑q) (symIdx s + 3 * mv.toNat) / 3 =
        Nat.pair (↑q) (symIdx s + 3 * mv.toNat) := by omega
    rw [decodeAct, ite_eq_left (by omega)]
    simp only [e1, Nat.unpair_pair, h3, h4, hfin]
  | push q b =>
    change decodeAct k (3 * Nat.pair q (if b then 1 else 0) + 1) = _
    have e1 : (3 * Nat.pair (↑q) (if b then 1 else 0) + 1) / 3 =
        Nat.pair (↑q) (if b then 1 else 0) := by omega
    rw [decodeAct, ite_eq_right (by omega), ite_eq_left (by omega)]
    simp only [e1, Nat.unpair_pair, hfin]
    cases b <;> rfl
  | ask q₁ q₂ =>
    change decodeAct k (3 * Nat.pair q₁ q₂ + 2) = _
    have e1 : (3 * Nat.pair (↑q₁) (↑q₂) + 2) / 3 = Nat.pair (↑q₁) (↑q₂) := by omega
    rw [decodeAct, ite_eq_right (by omega), ite_eq_right (by omega)]
    simp only [e1, Nat.unpair_pair, hfin]

/-! ### Codes of machines -/

/-- Number of states of the machine coded by `m`. -/
def codeK (m : ℕ) : ℕ := m.unpair.1 + 1
/-- Index of the initial state. -/
def codeStart (m : ℕ) : ℕ := m.unpair.2.unpair.1 % codeK m
/-- Index of the accepting state. -/
def codeAcc (m : ℕ) : ℕ := m.unpair.2.unpair.2.unpair.1 % codeK m
/-- Index of the rejecting state. -/
def codeRej (m : ℕ) : ℕ := m.unpair.2.unpair.2.unpair.2.unpair.1 % codeK m
/-- The transition table: entry `3 q + symIdx s` codes `δ q s`. -/
def codeTable (m : ℕ) : List ℕ :=
  Denumerable.ofNat (List ℕ) m.unpair.2.unpair.2.unpair.2.unpair.2
/-- The code of the action `δ q s` (state given by its index). -/
def actCode (m q : ℕ) (s : Sym) : ℕ := (codeTable m).getD (3 * q + symIdx s) 0

/-- The machine coded by `m` (total decoding). -/
def decodeCode (m : ℕ) : OTMCode where
  k := codeK m
  start := ⟨codeStart m, Nat.mod_lt _ (Nat.succ_pos _)⟩
  accept := ⟨codeAcc m, Nat.mod_lt _ (Nat.succ_pos _)⟩
  reject := ⟨codeRej m, Nat.mod_lt _ (Nat.succ_pos _)⟩
  δ := fun i s => decodeAct m.unpair.1 (actCode m i.val s)

/-- The transition table of a machine as a list (entry `3 q + symIdx s` codes `δ q s`). -/
def encodeTable (c : OTMCode) : List ℕ :=
  List.ofFn fun j : Fin (3 * c.k) =>
    encodeAct (c.δ ⟨j / 3, by have := j.isLt; omega⟩ (symOf (j % 3)))

/-- The code of a machine. -/
def encodeCode (c : OTMCode) : ℕ :=
  Nat.pair (c.k - 1) (Nat.pair c.start (Nat.pair c.accept (Nat.pair c.reject
    (Encodable.encode (encodeTable c)))))

/-- Encoding and decoding are inverse on actions with state cast. -/
theorem decodeAct_encodeAct' (k n : ℕ) (h : n = k + 1) (a : Act (Fin n)) :
    decodeAct k (encodeAct a) = a.map (Fin.cast h) := by
  subst h
  rw [decodeAct_encodeAct]
  cases a <;> rfl

/-- The element of index `j` with `j < n` in a list constructed by `List.ofFn` is `f ⟨j, hj⟩`. -/
theorem getD_ofFn {n : ℕ} (f : Fin n → ℕ) (j : ℕ) (hj : j < n) :
    (List.ofFn f).getD j 0 = f ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]

/-- Extensionality for codes, up to the identification of the state sets. -/
theorem OTMCode.ext' {c d : OTMCode} (hk : c.k = d.k) (hs : (c.start : ℕ) = d.start)
    (ha : (c.accept : ℕ) = d.accept) (hr : (c.reject : ℕ) = d.reject)
    (hδ : ∀ (i : Fin c.k) s, c.δ i s = (d.δ (Fin.cast hk i) s).map (Fin.cast hk.symm)) :
    c = d := by
  obtain ⟨k, s1, a1, r1, d1⟩ := c
  obtain ⟨k', s2, a2, r2, d2⟩ := d
  dsimp only at hk
  subst hk
  have e4 : d1 = d2 := by
    funext i s
    have h2 : ∀ a : Act (Fin k), a.map (Fin.cast rfl) = a := fun a => by cases a <;> rfl
    exact (hδ i s).trans (h2 _)
  have e1 : s1 = s2 := Fin.ext hs
  have e2 : a1 = a2 := Fin.ext ha
  have e3 : r1 = r2 := Fin.ext hr
  subst e1 e2 e3 e4
  rfl

/-- Encoding and decoding are inverse on codes of machines. -/
theorem decodeCode_encodeCode (c : OTMCode) : decodeCode (encodeCode c) = c := by
  have hk0 : 0 < c.k := Nat.lt_of_le_of_lt (Nat.zero_le _) c.start.isLt
  have hu : (encodeCode c).unpair = (c.k - 1, Nat.pair c.start (Nat.pair c.accept
      (Nat.pair c.reject (Encodable.encode (encodeTable c))))) := Nat.unpair_pair _ _
  have hK : codeK (encodeCode c) = c.k := by unfold codeK; rw [hu]; omega
  refine OTMCode.ext' hK ?_ ?_ ?_ ?_
  · change codeStart (encodeCode c) = c.start
    unfold codeStart; rw [hK, hu]; simp only [Nat.unpair_pair]
    exact Nat.mod_eq_of_lt c.start.isLt
  · change codeAcc (encodeCode c) = c.accept
    unfold codeAcc; rw [hK, hu]; simp only [Nat.unpair_pair]
    exact Nat.mod_eq_of_lt c.accept.isLt
  · change codeRej (encodeCode c) = c.reject
    unfold codeRej; rw [hK, hu]; simp only [Nat.unpair_pair]
    exact Nat.mod_eq_of_lt c.reject.isLt
  · intro i s
    have hT : codeTable (encodeCode c) = encodeTable c := by
      unfold codeTable; rw [hu]; simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
    have hi : i.val < c.k := hK ▸ i.isLt
    have hs3 := symIdx_lt s
    have hA : actCode (encodeCode c) i.val s = encodeAct (c.δ (Fin.cast hK i) s) := by
      unfold actCode
      rw [hT, encodeTable, getD_ofFn _ _ (by omega)]
      have e1 : (3 * i.val + symIdx s) % 3 = symIdx s := by omega
      have e2 : (3 * i.val + symIdx s) / 3 = i.val := by omega
      simp only [e1, e2, symOf_symIdx]
      rfl
    change decodeAct (encodeCode c).unpair.1 (actCode (encodeCode c) i.val s) = _
    rw [hA, decodeAct_encodeAct' _ c.k (by simp only [hu]; omega)]
    rfl

/-- The decoding function from natural numbers to machine codes is surjective. -/
theorem decodeCode_surjective : Function.Surjective decodeCode :=
  fun c => ⟨encodeCode c, decodeCode_encodeCode c⟩

/-- A computable enumeration of all clocked machines. -/
def γ₀ (n : ℕ) : OTMCode × ℕ := (decodeCode n.unpair.1, n.unpair.2)

/-- The effective enumeration `γ₀` of clocked machines is surjective. -/
theorem γ₀_surjective : Function.Surjective γ₀ := by
  rintro ⟨c, e⟩
  refine ⟨Nat.pair (encodeCode c) e, ?_⟩
  simp [γ₀, Nat.unpair_pair, decodeCode_encodeCode]

/-! ### Primitive recursiveness of the code components -/

/-- The number of states is primitive recursive in the code. -/
theorem codeK_primrec : Primrec codeK :=
  (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).of_eq fun _ => rfl

/-- The index of the initial state is primitive recursive in the code. -/
theorem codeStart_primrec : Primrec codeStart :=
  (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    codeK_primrec).of_eq fun _ => rfl

/-- The index of the accepting state is primitive recursive in the code. -/
theorem codeAcc_primrec : Primrec codeAcc :=
  (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))) codeK_primrec).of_eq fun _ => rfl

/-- The index of the rejecting state is primitive recursive in the code. -/
theorem codeRej_primrec : Primrec codeRej :=
  (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      Primrec.unpair))))))) codeK_primrec).of_eq fun _ => rfl

/-- The transition table is primitive recursive in the code. -/
theorem codeTable_primrec : Primrec codeTable :=
  ((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      Primrec.unpair)))))))).of_eq fun _ => rfl

/-- The index of a tape symbol is primitive recursive. -/
theorem symIdx_primrec : Primrec symIdx := Primrec.dom_finite _

/-- Equality to `j` modulo `3` is a primitive recursive predicate. -/
theorem mod3_primrecPred (j : ℕ) : PrimrecPred fun n : ℕ => n % 3 = j :=
  Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 3)) (Primrec.const j)

/-- The symbol of an index is primitive recursive. -/
theorem symOf_primrec : Primrec symOf :=
  (Primrec.ite (mod3_primrecPred 0) (Primrec.const none) (Primrec.ite (mod3_primrecPred 1)
    (Primrec.const (some false)) (Primrec.const (some true)))).of_eq fun _ => rfl

/-- The code of an action is primitive recursive in the machine code, state, and symbol. -/
theorem actCode_primrec : Primrec fun p : ℕ × ℕ × Sym => actCode p.1 p.2.1 p.2.2 :=
  ((Primrec.list_getD 0).comp (codeTable_primrec.comp Primrec.fst)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) (Primrec.fst.comp Primrec.snd))
      (symIdx_primrec.comp (Primrec.snd.comp Primrec.snd)))).of_eq fun _ => rfl

/-- A numbering of actions with natural states (the same as `Act.code` of the construction). -/
def actNum {k : ℕ} : Act (Fin k) → ℕ
  | .step q a m => Nat.pair 0 (Nat.pair (q : ℕ) (Nat.pair (Encodable.encode a) m.toNat))
  | .push q b => Nat.pair 1 (Nat.pair (q : ℕ) (Encodable.encode b))
  | .ask q₁ q₂ => Nat.pair 2 (Nat.pair (q₁ : ℕ) (q₂ : ℕ))

/-- `actNum (decodeAct k A)` computed arithmetically. -/
def actNumDecode (k A : ℕ) : ℕ :=
  if A % 3 = 0 then
    Nat.pair 0 (Nat.pair ((A / 3).unpair.1 % (k + 1))
      (Nat.pair (Encodable.encode (symOf (A / 3).unpair.2)) ((A / 3).unpair.2 / 3 % 3)))
  else if A % 3 = 1 then
    Nat.pair 1 (Nat.pair ((A / 3).unpair.1 % (k + 1))
      (Encodable.encode (decide ((A / 3).unpair.2 % 2 = 1))))
  else Nat.pair 2 (Nat.pair ((A / 3).unpair.1 % (k + 1)) ((A / 3).unpair.2 % (k + 1)))

/-- The index of the move of index `n` is `n mod 3`. -/
theorem moveOf_toNat_eq (n : ℕ) : (moveOf n).toNat = n % 3 := by
  unfold moveOf
  split_ifs with h0 h1
  · simp [Move.toNat, h0]
  · simp [Move.toNat, h1]
  · simp only [Move.toNat]; omega

/-- Action decoding matches arithmetic decoding. -/
theorem actNum_decodeAct (k A : ℕ) : actNum (decodeAct k A) = actNumDecode k A := by
  unfold decodeAct actNumDecode
  split_ifs <;> simp only [actNum, moveOf_toNat_eq]

/-- The transition table of the decoded machine, as a function of naturals. -/
def tableNum (m i : ℕ) (a : Sym) : ℕ :=
  if i < codeK m then actNumDecode m.unpair.1 (actCode m i a) else 0

/-- The numerical transition table matches the decoded machine's table. -/
theorem tableNum_spec (m i : ℕ) (a : Sym) :
    (if h : i < (decodeCode m).k then actNum ((decodeCode m).δ ⟨i, h⟩ a) else 0) =
      tableNum m i a := by
  unfold tableNum
  by_cases h : i < codeK m
  · have h' : i < (decodeCode m).k := h
    rw [dite_eq_left h', ite_eq_left h]
    exact actNum_decodeAct _ _
  · have h' : ¬ i < (decodeCode m).k := h
    rw [dite_eq_right h', ite_eq_right h]

/-- The arithmetic decoding of an action is primitive recursive. -/
theorem actNumDecode_primrec : Primrec₂ actNumDecode := by
  have hd : Primrec fun p : ℕ × ℕ => (p.2 / 3).unpair :=
    Primrec.unpair.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 3))
  have hu1 : Primrec fun p : ℕ × ℕ => (p.2 / 3).unpair.1 := Primrec.fst.comp hd
  have hu2 : Primrec fun p : ℕ × ℕ => (p.2 / 3).unpair.2 := Primrec.snd.comp hd
  have hk1 : Primrec fun p : ℕ × ℕ => p.1 + 1 := Primrec.nat_add.comp Primrec.fst (Primrec.const 1)
  have hq1 : Primrec fun p : ℕ × ℕ => (p.2 / 3).unpair.1 % (p.1 + 1) := Primrec.nat_mod.comp hu1 hk1
  have hq2 : Primrec fun p : ℕ × ℕ => (p.2 / 3).unpair.2 % (p.1 + 1) := Primrec.nat_mod.comp hu2 hk1
  have c0 : PrimrecPred fun p : ℕ × ℕ => p.2 % 3 = 0 := (mod3_primrecPred 0).comp Primrec.snd
  have c1 : PrimrecPred fun p : ℕ × ℕ => p.2 % 3 = 1 := (mod3_primrecPred 1).comp Primrec.snd
  have b0 : Primrec fun p : ℕ × ℕ => Nat.pair 0 (Nat.pair ((p.2 / 3).unpair.1 % (p.1 + 1))
      (Nat.pair (Encodable.encode (symOf (p.2 / 3).unpair.2))
        ((p.2 / 3).unpair.2 / 3 % 3))) :=
    Primrec₂.natPair.comp (Primrec.const 0) (Primrec₂.natPair.comp hq1 (Primrec₂.natPair.comp
      (Primrec.encode.comp (symOf_primrec.comp hu2))
      (Primrec.nat_mod.comp (Primrec.nat_div.comp hu2 (Primrec.const 3)) (Primrec.const 3))))
  have b1 : Primrec fun p : ℕ × ℕ => Nat.pair 1 (Nat.pair ((p.2 / 3).unpair.1 % (p.1 + 1))
      (Encodable.encode (decide ((p.2 / 3).unpair.2 % 2 = 1)))) :=
    Primrec₂.natPair.comp (Primrec.const 1) (Primrec₂.natPair.comp hq1 (Primrec.encode.comp
      (Primrec.eq.decide.comp (Primrec.nat_mod.comp hu2 (Primrec.const 2)) (Primrec.const 1))))
  have b2 : Primrec fun p : ℕ × ℕ => Nat.pair 2 (Nat.pair ((p.2 / 3).unpair.1 % (p.1 + 1))
      ((p.2 / 3).unpair.2 % (p.1 + 1))) :=
    Primrec₂.natPair.comp (Primrec.const 2) (Primrec₂.natPair.comp hq1 hq2)
  exact (Primrec.ite c0 b0 (Primrec.ite c1 b1 b2)).of_eq fun _ => rfl

/-- The numerical transition table is primitive recursive. -/
theorem tableNum_primrec : Primrec fun p : ℕ × ℕ × Sym => tableNum p.1 p.2.1 p.2.2 :=
  (Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (codeK_primrec.comp Primrec.fst))
    (actNumDecode_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)) actCode_primrec)
    (Primrec.const 0)).of_eq fun _ => rfl

/-! ### From an effective table to a code -/

/-- Conversion from the `actNum` numbering of actions to the `encodeAct` numbering. -/
def convAct (n : ℕ) : ℕ :=
  if n.unpair.1 = 0 then
    3 * Nat.pair n.unpair.2.unpair.1
      (n.unpair.2.unpair.2.unpair.1 + 3 * n.unpair.2.unpair.2.unpair.2)
  else if n.unpair.1 = 1 then
    3 * Nat.pair n.unpair.2.unpair.1 n.unpair.2.unpair.2 + 1
  else
    3 * Nat.pair n.unpair.2.unpair.1 n.unpair.2.unpair.2 + 2

/-- The encoding of a symbol is its index. -/
theorem encode_sym (s : Sym) : Encodable.encode s = symIdx s := by
  rcases s with _ | _ | _ <;> rfl

/-- The encoding of a boolean is `1` for `true` and `0` for `false`. -/
theorem encode_bool (b : Bool) : Encodable.encode b = if b then 1 else 0 := by
  cases b <;> rfl

/-- The conversion function bridges `actNum` and `encodeAct`. -/
theorem convAct_actNum {k : ℕ} (a : Act (Fin k)) : convAct (actNum a) = encodeAct a := by
  cases a with
  | step q s mv => simp [convAct, actNum, encodeAct, Nat.unpair_pair, encode_sym]
  | push q b => simp [convAct, actNum, encodeAct, Nat.unpair_pair, encode_bool]
  | ask q₁ q₂ => simp [convAct, actNum, encodeAct, Nat.unpair_pair]

/-- The conversion function `convAct` is primitive recursive. -/
theorem convAct_primrec : Primrec convAct := by
  have hu : Primrec fun n : ℕ => n.unpair := Primrec.unpair
  have h1 : Primrec fun n : ℕ => n.unpair.1 := Primrec.fst.comp hu
  have h2 : Primrec fun n : ℕ => n.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp hu)
  have h21 : Primrec fun n : ℕ => n.unpair.2.unpair.1 := Primrec.fst.comp h2
  have h22 : Primrec fun n : ℕ => n.unpair.2.unpair.2 := Primrec.snd.comp h2
  have h221 : Primrec fun n : ℕ => n.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp h22)
  have h222 : Primrec fun n : ℕ => n.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp h22)
  have c0 : PrimrecPred fun n : ℕ => n.unpair.1 = 0 := Primrec.eq.comp h1 (Primrec.const 0)
  have c1 : PrimrecPred fun n : ℕ => n.unpair.1 = 1 := Primrec.eq.comp h1 (Primrec.const 1)
  have b0 : Primrec fun n : ℕ => 3 * Nat.pair n.unpair.2.unpair.1
      (n.unpair.2.unpair.2.unpair.1 + 3 * n.unpair.2.unpair.2.unpair.2) :=
    Primrec.nat_mul.comp (Primrec.const 3) (Primrec₂.natPair.comp h21
      (Primrec.nat_add.comp h221 (Primrec.nat_mul.comp (Primrec.const 3) h222)))
  have b1 : Primrec fun n : ℕ =>
      3 * Nat.pair n.unpair.2.unpair.1 n.unpair.2.unpair.2 + 1 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) (Primrec₂.natPair.comp h21 h22))
      (Primrec.const 1)
  have b2 : Primrec fun n : ℕ => 3 * Nat.pair n.unpair.2.unpair.1 n.unpair.2.unpair.2 + 2 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) (Primrec₂.natPair.comp h21 h22))
      (Primrec.const 2)
  exact (Primrec.ite c0 b0 (Primrec.ite c1 b1 b2)).of_eq fun _ => rfl

/-- The table of a machine in the `actNum` numbering (`0` outside the state range); this is
`OTMCode.table` of the construction. -/
def actTable (c : OTMCode) (i : ℕ) (a : Sym) : ℕ :=
  if h : i < c.k then actNum (c.δ ⟨i, h⟩ a) else 0

/-- The table list `[convAct (T (j / 3) (symOf (j % 3))) | j < n]`. -/
def tableList (T : ℕ → Sym → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map fun j => convAct (T (j / 3) (symOf (j % 3)))

/-- Expanding the table list to `n + 1` appends the conversion of the action for index `n`. -/
theorem tableList_succ (T : ℕ → Sym → ℕ) (n : ℕ) :
    tableList T (n + 1) = tableList T n ++ [convAct (T (n / 3) (symOf (n % 3)))] := by
  simp [tableList, List.range_succ]

/-- The table list of `actTable` matches the encoded transition table. -/
theorem tableList_actTable (c : OTMCode) : tableList (actTable c) (3 * c.k) = encodeTable c := by
  unfold tableList encodeTable
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hj : j / 3 < c.k := by simp at h1; omega
    simp only [actTable, dite_eq_left hj, convAct_actNum]

/-- The code of a machine computed from its data and its `actNum` table. -/
def codeOfTable (k s a r : ℕ) (T : ℕ → Sym → ℕ) : ℕ :=
  Nat.pair (k - 1) (Nat.pair s (Nat.pair a (Nat.pair r (Encodable.encode (tableList T (3 * k))))))

/-- The code of a table from machine parameters equals its encoded code. -/
theorem codeOfTable_eq (c : OTMCode) :
    codeOfTable c.k c.start c.accept c.reject (actTable c) = encodeCode c := by
  unfold codeOfTable encodeCode
  rw [tableList_actTable]

/-- **Bridge to effective enumerations.**  If the number of states, the distinguished states and
the `actNum` table of `γ e` are computable in `e`, then a code of `γ e` is computable in `e`. -/
theorem exists_code_computable (γ : ℕ → OTMCode)
    (hk : Computable fun e => (γ e).k) (hs : Computable fun e => ((γ e).start : ℕ))
    (ha : Computable fun e => ((γ e).accept : ℕ)) (hr : Computable fun e => ((γ e).reject : ℕ))
    (ht : Computable fun p : ℕ × ℕ × Sym => actTable (γ p.1) p.2.1 p.2.2) :
    ∃ code : ℕ → ℕ, Computable code ∧ ∀ e, decodeCode (code e) = γ e := by
  refine ⟨fun e => codeOfTable (γ e).k (γ e).start (γ e).accept (γ e).reject (actTable (γ e)),
    ?_, fun e => ?_⟩
  · have hL : Computable fun e => tableList (actTable (γ e)) (3 * (γ e).k) := by
      have h := Computable.nat_rec (f := fun e => 3 * (γ e).k) (g := fun _ => ([] : List ℕ))
        (h := fun e (p : ℕ × List ℕ) =>
          p.2 ++ [convAct (actTable (γ e) (p.1 / 3) (symOf (p.1 % 3)))])
        ((Primrec.nat_mul.to_comp).comp (Computable.const 3) hk) (Computable.const [])
        ((Primrec.list_concat.to_comp).comp (Computable.snd.comp Computable.snd)
          ((convAct_primrec.to_comp).comp (ht.comp (Computable.fst.pair
            (((Primrec.nat_div.to_comp).comp (Computable.fst.comp Computable.snd)
              (Computable.const 3)).pair ((symOf_primrec.to_comp).comp
                ((Primrec.nat_mod.to_comp).comp (Computable.fst.comp Computable.snd)
                  (Computable.const 3))))))))
      refine h.of_eq fun e => ?_
      generalize 3 * (γ e).k = n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [tableList_succ]
        exact congrArg (fun L => L ++ [convAct (actTable (γ e) (n / 3) (symOf (n % 3)))]) ih
    exact ((Primrec₂.natPair.to_comp).comp ((Primrec.nat_sub.to_comp).comp hk (Computable.const 1))
      ((Primrec₂.natPair.to_comp).comp hs ((Primrec₂.natPair.to_comp).comp ha
        ((Primrec₂.natPair.to_comp).comp hr (Computable.encode.comp hL))))).of_eq fun _ => rfl
  · change decodeCode (codeOfTable (γ e).k (γ e).start (γ e).accept (γ e).reject
      (actTable (γ e))) = γ e
    rw [codeOfTable_eq, decodeCode_encodeCode]

end Kolmogorov.RandomStrings
