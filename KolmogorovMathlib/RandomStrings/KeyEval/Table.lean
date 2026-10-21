/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.SAExp
import KolmogorovMathlib.RandomStrings.StmtTime
import KolmogorovMathlib.RandomStrings.StepBudget

/-!
# The table of the value-iteration driver and its loops

The table representation of the driver (`KeyEval.idxStr`, `KeyEval.tabRead`, `KeyEval.tabNext`,
`KeyEval.tabIter`), the layers restricted to the codes of the list, the table as the list of its
`true` entries, the interface of the key routines, the table routines, and the loops over all bit
strings of a given length: accumulating a flag (`any`) and writing the strings of a predicate
(`filter`).

Part of `KolmogorovMathlib.RandomStrings.KeyEval`.
-/

namespace Kolmogorov.RandomStrings

namespace KeyEval

/-! ### Bits of a number -/

/-- The `w` low bits of `a`, least significant first (the inverse of `binVal`). -/
def bitsOf : ℕ → ℕ → BitString
  | 0, _ => []
  | w + 1, a => decide (a % 2 = 1) :: bitsOf w (a / 2)

/-- `bitsOf w a` consists of exactly `w` bits. -/
theorem length_bitsOf : ∀ (w a : ℕ), (bitsOf w a).length = w
  | 0, _ => rfl
  | w + 1, a => by simp [bitsOf, length_bitsOf w]

/-- `bitsOf` inverts `binVal`: the `s.length` low bits of the value of `s` are `s` itself. -/
theorem bitsOf_binVal : ∀ s : BitString, bitsOf s.length (binVal s) = s
  | [] => rfl
  | b :: s => by
    have h1 : (b.toNat + 2 * binVal s) / 2 = binVal s := by
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have h2 : decide ((b.toNat + 2 * binVal s) % 2 = 1) = b := by cases b <;> simp
    simp only [List.length_cons, bitsOf, binVal, h1, h2, bitsOf_binVal s]

/-- `binVal` inverts `bitsOf` on the numbers that fit in `w` bits: the `w` low bits of `a < 2 ^ w`
have the value `a`. -/
theorem binVal_bitsOf_of_lt {w a : ℕ} (h : a < 2 ^ w) : binVal (bitsOf w a) = a := by
  induction w generalizing a with
  | zero => rw [pow_zero, Nat.lt_one_iff] at h; subst h; rfl
  | succ w ih =>
    have h' : a / 2 < 2 ^ w := by rw [pow_succ] at h; omega
    simp only [bitsOf, binVal, ih h']
    rcases Nat.mod_two_eq_zero_or_one a with h2 | h2 <;> simp [h2] <;> omega

/-! ### The table -/

variable (L W : ℕ)

/-- The index string of the triple `(κ, y, n)`: the key code, then the two scores in `W` bits. -/
def idxStr (κ : BitString) (y n : ℕ) : BitString := κ ++ bitsOf W y ++ bitsOf W n

/-- The entry of the triple `(κ, y, n)` in the table `tab`. -/
def tabRead (tab : List Bool) (κ : BitString) (y n : ℕ) : Bool :=
  tab.getD (binVal (idxStr W κ y n)) false

/-- The key code of the index `i`. -/
def idxKey (i : ℕ) : BitString := (bitsOf (L + W + W) i).take L

/-- The yes-score of the index `i`. -/
def idxY (i : ℕ) : ℕ := binVal (((bitsOf (L + W + W) i).drop L).take W)

/-- The no-score of the index `i`. -/
def idxN (i : ℕ) : ℕ := binVal ((bitsOf (L + W + W) i).drop (L + W))

variable {L W}

/-- The index string of a triple whose key code has length `L` has length `L + W + W`. -/
theorem length_idxStr {κ : BitString} (hκ : κ.length = L) (y n : ℕ) :
    (idxStr W κ y n).length = L + W + W := by
  simp only [idxStr, List.length_append, length_bitsOf, hκ]

/-- The position `binVal (idxStr W κ y n)` of the index string of a triple with a key code `κ`
of length `L` lies in the table of `2 ^ (L + W + W)` entries. -/
theorem binVal_idxStr_lt {κ : BitString} (hκ : κ.length = L) (y n : ℕ) :
    binVal (idxStr W κ y n) < 2 ^ (L + W + W) := by
  have := binVal_lt (idxStr W κ y n)
  rwa [length_idxStr hκ] at this

/-- **Decoding a table position.** If the key code `κ` has length `L` and the scores `y`, `n` are
below `2 ^ W`, then the position of the index string of `(κ, y, n)` decodes (`idxKey`, `idxY`,
`idxN`) back to `κ`, `y` and `n`. -/
theorem idx_decode {κ : BitString} (hκ : κ.length = L) {y n : ℕ} (hy : y < 2 ^ W)
    (hn : n < 2 ^ W) :
    idxKey L W (binVal (idxStr W κ y n)) = κ ∧ idxY L W (binVal (idxStr W κ y n)) = y ∧
      idxN L W (binVal (idxStr W κ y n)) = n := by
  have hb : bitsOf (L + W + W) (binVal (idxStr W κ y n)) = idxStr W κ y n := by
    rw [← length_idxStr hκ y n (W := W), bitsOf_binVal]
  have hlY : (bitsOf W y).length = W := length_bitsOf W y
  have hlN : (bitsOf W n).length = W := length_bitsOf W n
  unfold idxKey idxY idxN
  rw [hb]
  unfold idxStr
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_left' hκ]
  · rw [List.append_assoc, List.drop_left' hκ, List.take_left' hlY, binVal_bitsOf_of_lt hy]
  · rw [List.drop_left' (by simp [hκ, hlY]), binVal_bitsOf_of_lt hn]

/-- The first layer: the outcome of the key at every triple. -/
def tabInit (L W : ℕ) (o : BitString → Bool) : List Bool :=
  List.ofFn fun i : Fin (2 ^ (L + W + W)) => o (idxKey L W i)

/-- One layer step: entry `i` of the new table is the step function, reading the old table, at
the decoded triple of `i`. -/
def tabNext (L W : ℕ)
    (step : (BitString → ℕ → ℕ → Bool) → BitString → ℕ → ℕ → Bool)
    (tab : List Bool) : List Bool :=
  List.ofFn fun i : Fin (2 ^ (L + W + W)) =>
    step (tabRead W tab) (idxKey L W i) (idxY L W i) (idxN L W i)

/-- The tables of the value iteration. -/
def tabIter (L W : ℕ)
    (step : (BitString → ℕ → ℕ → Bool) → BitString → ℕ → ℕ → Bool)
    (o : BitString → Bool) : ℕ → List Bool
  | 0 => tabInit L W o
  | f + 1 => tabNext L W step (tabIter L W step o f)

/-- The first layer `tabInit L W o` has one entry for every position, `2 ^ (L + W + W)` in all. -/
theorem length_tabInit (o : BitString → Bool) : (tabInit L W o).length = 2 ^ (L + W + W) := by
  simp [tabInit]

/-- The table `tabNext L W step tab` produced by a layer step has `2 ^ (L + W + W)` entries. -/
theorem length_tabNext
    (step : (BitString → ℕ → ℕ → Bool) → BitString → ℕ → ℕ → Bool)
    (tab : List Bool) : (tabNext L W step tab).length = 2 ^ (L + W + W) := by
  simp [tabNext]

/-- Every layer of the value iteration has `2 ^ (L + W + W)` entries. -/
theorem length_tabIter
    (step : (BitString → ℕ → ℕ → Bool) → BitString → ℕ → ℕ → Bool)
    (o : BitString → Bool) : ∀ f, (tabIter L W step o f).length = 2 ^ (L + W + W)
  | 0 => length_tabInit o
  | _ + 1 => length_tabNext step _

/-- **Read-back of the first layer.** At a triple whose key code `κ` has length `L` and whose
scores are below `2 ^ W`, the table `tabInit L W o` holds the outcome `o κ`. -/
theorem tabRead_tabInit (o : BitString → Bool) {κ : BitString} (hκ : κ.length = L) {y n : ℕ}
    (hy : y < 2 ^ W) (hn : n < 2 ^ W) : tabRead W (tabInit L W o) κ y n = o κ := by
  unfold tabRead tabInit
  rw [List.getD_eq_getElem _ _ (by simpa using binVal_idxStr_lt hκ y n (W := W)),
    List.getElem_ofFn]
  exact congrArg o (idx_decode hκ hy hn).1

/-- **Read-back of a layer step.** At a triple whose key code `κ` has length `L` and whose scores
are below `2 ^ W`, the table `tabNext L W step tab` holds the step function, applied to the read
function of `tab`, at that triple. -/
theorem tabRead_tabNext
    (step : (BitString → ℕ → ℕ → Bool) → BitString → ℕ → ℕ → Bool)
    (tab : List Bool) {κ : BitString} (hκ : κ.length = L) {y n : ℕ} (hy : y < 2 ^ W)
    (hn : n < 2 ^ W) :
    tabRead W (tabNext L W step tab) κ y n = step (tabRead W tab) κ y n := by
  unfold tabRead tabNext
  rw [List.getD_eq_getElem _ _ (by simpa using binVal_idxStr_lt hκ y n (W := W)),
    List.getElem_ofFn]
  obtain ⟨h1, h2, h3⟩ := idx_decode hκ hy hn (W := W)
  simp only [h1, h2, h3]
  rfl

end KeyEval

/-! ### Layers restricted to the codes of the list -/

section LayersMem

variable {α : Type} (codes : List α) (dec : α → Finset BitString) (X : Finset BitString)
  (P : Finset BitString → Finset BitString) (out : Finset BitString → Bool)
  (c : BitString → ℕ) (E : ℕ)

/-- `stepKC` only reads the previous layer at codes of the list and scores `≤ E`. -/
theorem stepKC_congr_mem {g₁ g₂ : α → ℕ → ℕ → Bool}
    (h : ∀ ρ ∈ codes, ∀ y' n', y' ≤ E → n' ≤ E → g₁ ρ y' n' = g₂ ρ y' n')
    (κ : α) (y n : ℕ) :
    stepKC codes dec X P out c E g₁ κ y n = stepKC codes dec X P out c E g₂ κ y n := by
  unfold stepKC
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun κ' _ => ?_
  by_cases h2 : n + costN c (dec κ) (dec κ') ≤ E
  · simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    refine or_congr_right (exists_congr fun ρ => and_congr_right fun hρ => ?_)
    by_cases h1 : y + costN c (dec κ') (dec ρ) ≤ E
    · rw [h ρ hρ _ _ h1 h2]
    · simp [h1]
  · simp [h2]

/-- The layer invariant on the codes of the list. -/
theorem layer_eq_yesKC_mem (tab : ℕ → α → ℕ → ℕ → Bool)
    (h0 : ∀ κ ∈ codes, ∀ y n, y ≤ E → n ≤ E → tab 0 κ y n = out (dec κ))
    (hs : ∀ f, ∀ κ ∈ codes, ∀ y n, y ≤ E → n ≤ E →
      tab (f + 1) κ y n = stepKC codes dec X P out c E (tab f) κ y n) :
    ∀ f, ∀ κ ∈ codes, ∀ y n, y ≤ E → n ≤ E →
      tab f κ y n = yesKC codes dec X P out c E f κ y n := by
  intro f
  induction f with
  | zero => intro κ hκ y n hy hn; exact h0 κ hκ y n hy hn
  | succ f ih =>
    intro κ hκ y n hy hn
    rw [hs f κ hκ y n hy hn, yesKC_succ]
    exact stepKC_congr_mem codes dec X P out c E
      (fun ρ hρ y' n' hy' hn' => ih ρ hρ y' n' hy' hn') κ y n

/-- The answer read off the last layer, on the codes of the list. -/
theorem valKC_eq_of_layer_mem (F : ℕ) (tabF : α → ℕ → ℕ → Bool)
    (h : ∀ κ ∈ codes, ∀ y n, y ≤ E → n ≤ E →
      tabF κ y n = yesKC codes dec X P out c E F κ y n) :
    valKC codes dec X P out c E F = codes.any fun κ =>
      decide (KeyMoveRaw X P ∅ (dec κ)) && decide (costN c ∅ (dec κ) ≤ E) &&
        tabF κ (costN c ∅ (dec κ)) 0 := by
  unfold valKC
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  refine exists_congr fun κ => and_congr_right fun hκ => ?_
  by_cases hc : costN c ∅ (dec κ) ≤ E
  · rw [h κ hκ _ 0 hc (Nat.zero_le _)]
  · simp [hc]

end LayersMem

/-- **One layer preserves the layer invariant** (the form used by the program's main loop: the
current table is only known through its read function `g`). -/
theorem layer_inv_succ {α : Type} (codes : List α) (dec : α → Finset BitString)
    (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool) (c : BitString → ℕ) (E f : ℕ)
    (g g' : α → ℕ → ℕ → Bool)
    (hg : ∀ κ ∈ codes, ∀ y n, y ≤ E → n ≤ E →
      g κ y n = yesKC codes dec X P out c E f κ y n)
    (hg' : ∀ κ ∈ codes, ∀ y n, y ≤ E → n ≤ E →
      g' κ y n = stepKC codes dec X P out c E g κ y n) :
    ∀ κ ∈ codes, ∀ y n, y ≤ E → n ≤ E →
      g' κ y n = yesKC codes dec X P out c E (f + 1) κ y n := by
  intro κ hκ y n hy hn
  rw [hg' κ hκ y n hy hn, yesKC_succ]
  exact stepKC_congr_mem codes dec X P out c E (fun ρ hρ y' n' hy' hn' => hg ρ hρ y' n' hy' hn')
    κ y n

/-- The first layer satisfies the layer invariant. -/
theorem layer_inv_zero {α : Type} (codes : List α) (dec : α → Finset BitString)
    (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool) (c : BitString → ℕ) (E : ℕ)
    (g : α → ℕ → ℕ → Bool)
    (hg : ∀ κ ∈ codes, ∀ y n, y ≤ E → n ≤ E → g κ y n = out (dec κ)) :
    ∀ κ ∈ codes, ∀ y n, y ≤ E → n ≤ E →
      g κ y n = yesKC codes dec X P out c E 0 κ y n :=
  hg

namespace KeyEval

/-! ### The table as the list of its `true` entries

The program keeps a layer on a stack as `Stacks.encList Ls`, `Ls` the list of the index strings
`idxStr W κ y n` of the triples with entry `true` (in any order, possibly with repetitions): a
lookup is the verified membership test `Stmt.memTest`, a write of a `true` entry pushes
`Stacks.encStr` of the index string.  `readL W Ls` is the read function of such a table. -/

/-- The read function of a table given by the list of its `true` index strings. -/
def readL (W : ℕ) (Ls : List BitString) (κ : BitString) (y n : ℕ) : Bool :=
  decide (idxStr W κ y n ∈ Ls)

/-- The key code of an index string. -/
def strKey (L : ℕ) (s : BitString) : BitString := s.take L

/-- The yes-score of an index string. -/
def strY (L W : ℕ) (s : BitString) : ℕ := binVal ((s.drop L).take W)

/-- The no-score of an index string. -/
def strN (L W : ℕ) (s : BitString) : ℕ := binVal (s.drop (L + W))

/-- **Decoding an index string.** If the key code `κ` has length `L` and the scores `y`, `n` are
below `2 ^ W`, then `strKey`, `strY` and `strN` of the index string of `(κ, y, n)` give back `κ`,
`y` and `n`. -/
theorem str_decode {L W : ℕ} {κ : BitString} (hκ : κ.length = L) {y n : ℕ} (hy : y < 2 ^ W)
    (hn : n < 2 ^ W) :
    strKey L (idxStr W κ y n) = κ ∧ strY L W (idxStr W κ y n) = y ∧
      strN L W (idxStr W κ y n) = n := by
  have h := idx_decode hκ hy hn (W := W)
  have hb : bitsOf (L + W + W) (binVal (idxStr W κ y n)) = idxStr W κ y n := by
    rw [← length_idxStr hκ y n (W := W), bitsOf_binVal]
  unfold idxKey idxY idxN at h
  rw [hb] at h
  exact h

/-- Every string of length `L + W + W` is the index string of its decoded triple. -/
theorem idxStr_decode {L W : ℕ} {s : BitString} (hs : s.length = L + W + W) :
    idxStr W (strKey L s) (strY L W s) (strN L W s) = s := by
  have h2 : ((s.drop L).take W).length = W := by
    simp only [List.length_take, List.length_drop, hs]; omega
  have h3 : (s.drop (L + W)).length = W := by simp only [List.length_drop, hs]; omega
  have ha : bitsOf W (binVal ((s.drop L).take W)) = (s.drop L).take W := by
    have := bitsOf_binVal ((s.drop L).take W); rwa [h2] at this
  have hb : bitsOf W (binVal (s.drop (L + W))) = s.drop (L + W) := by
    have := bitsOf_binVal (s.drop (L + W)); rwa [h3] at this
  unfold idxStr strY strN strKey
  rw [ha, hb, ← List.take_add, List.take_append_drop]

/-- **The layer step on lists**: a list containing, among the strings of length `L + W + W`,
exactly those whose decoded triple has step value `true` reads back as the step of the old table. -/
theorem readL_step {L W : ℕ}
    (step : (BitString → ℕ → ℕ → Bool) → BitString → ℕ → ℕ → Bool)
    (Lold Lnew : List BitString)
    (hnew : ∀ s : BitString, s.length = L + W + W →
      (s ∈ Lnew ↔ step (readL W Lold) (strKey L s) (strY L W s) (strN L W s) = true))
    {κ : BitString} (hκ : κ.length = L) {y n : ℕ} (hy : y < 2 ^ W) (hn : n < 2 ^ W) :
    readL W Lnew κ y n = step (readL W Lold) κ y n := by
  obtain ⟨h1, h2, h3⟩ := str_decode hκ hy hn (W := W)
  have := hnew (idxStr W κ y n) (length_idxStr hκ y n)
  rw [h1, h2, h3] at this
  unfold readL
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  exact this

/-- **The first layer on lists**: a list containing, among the strings of length `L + W + W`,
exactly those whose key code has outcome `true` reads back as `o κ`. -/
theorem readL_init {L W : ℕ} (o : BitString → Bool) (Ls : List BitString)
    (h0 : ∀ s : BitString, s.length = L + W + W → (s ∈ Ls ↔ o (strKey L s) = true))
    {κ : BitString} (hκ : κ.length = L) {y n : ℕ} (hy : y < 2 ^ W) (hn : n < 2 ^ W) :
    readL W Ls κ y n = o κ := by
  obtain ⟨h1, -, -⟩ := str_decode hκ hy hn (W := W)
  have := h0 (idxStr W κ y n) (length_idxStr hκ y n)
  rw [h1] at this
  unfold readL
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  exact this

/-! ### The interface of the key routines

Each routine runs in `k` stacks, reads the input `x` on stack `I` (unchanged), its key-code
arguments (bit strings of length `L`) on the argument stacks (unchanged), writes its result on
the output stack `F` (empty before), uses the stacks `j` with `kR ≤ j` as its own work stacks
(empty before and after) and changes nothing else; it runs within the space `τ.space + B` and at
most `B` steps. -/

/-- A routine computing a bit of one key code (`sOut`: `bit κ = out (dec κ)`; `sValid`). -/
def KeyBitRoutine {k : ℕ} (s : Stmt k) (x : BitString) (L kR : ℕ) (I A F : Fin k) (B : ℕ)
    (bit : BitString → Bool) : Prop :=
  ∀ τ : Stacks k, τ I = x → (τ A).length = L → τ F = [] →
    (∀ j : Fin k, kR ≤ j.val → τ j = []) →
    ExecLe s τ (Function.update τ F [bit (τ A)]) (τ.space + B) B

/-- A routine computing a bit of two key codes (`sMove`: `KeyMoveRaw X P (dec κ) (dec κ')`;
the strictness test `dec κ' ⊆ dec κ`). -/
def PairBitRoutine {k : ℕ} (s : Stmt k) (x : BitString) (L kR : ℕ) (I A A' F : Fin k) (B : ℕ)
    (bit : BitString → BitString → Bool) : Prop :=
  ∀ τ : Stacks k, τ I = x → (τ A).length = L → (τ A').length = L → τ F = [] →
    (∀ j : Fin k, kR ≤ j.val → τ j = []) →
    ExecLe s τ (Function.update τ F [bit (τ A) (τ A')]) (τ.space + B) B

/-- A routine computing a `W`-bit number of two key codes, least significant bit on top
(`sMove`'s cost: `min (costN c (dec κ) (dec κ')) (E + 1)`). -/
def PairNumRoutine {k : ℕ} (s : Stmt k) (x : BitString) (L W kR : ℕ) (I A A' F : Fin k)
    (B : ℕ) (num : BitString → BitString → ℕ) : Prop :=
  ∀ τ : Stacks k, τ I = x → (τ A).length = L → (τ A').length = L → τ F = [] →
    (∀ j : Fin k, kR ≤ j.val → τ j = []) →
    ExecLe s τ (Function.update τ F (bitsOf W (num (τ A) (τ A')))) (τ.space + B) B

/-! ### The table routines

A layer is kept on a stack as `Stacks.encList Ls` (`readL`).  A lookup is the verified
membership test `Stmt.memTest` inlined along an injective renaming `f : Fin 9 → Fin k`: the index
string on stack `f 0`, the table on stack `f 1`, the bit on stack `f 2` (empty before), the stacks
`f 3, …, f 8` empty work stacks (`exec_tabLookup`).  A write of a `true` entry is
`QEnum.pushCode`: it pushes `Stacks.encStr` of the index string on the new table
(`execLe_tabWrite`), i.e. it prepends the index string to the list. -/

/-- Table lookup: `Stmt.memTest` inlined along `f`. -/
def tabLookup {k : ℕ} (f : Fin 9 → Fin k) : Stmt k := Stmt.memTest.rename f

/-- **Table lookup.** If the stack `f 1` holds the table `Stacks.encList Ls` and the stacks
`f 2, …, f 8` are empty, then `tabLookup f` leaves the bit `decide (τ (f 0) ∈ Ls)` on `f 2`,
which says whether the index string on `f 0` is in the table, and changes nothing else.  It stays
within the space `m = τ.space + |encList Ls| + 2` and takes at most `57 m² + 29 m + 3` steps. -/
theorem exec_tabLookup {k : ℕ} {f : Fin 9 → Fin k} (hf : Function.Injective f) {τ : Stacks k}
    {Ls : List BitString} (h1 : τ (f 1) = Stacks.encList Ls) (h2 : τ (f 2) = [])
    (h3 : τ (f 3) = []) (h4 : τ (f 4) = []) (h5 : τ (f 5) = []) (h6 : τ (f 6) = [])
    (h7 : τ (f 7) = []) (h8 : τ (f 8) = []) :
    ExecLe (tabLookup f) τ (Function.update τ (f 2) [decide (τ (f 0) ∈ Ls)])
      (τ.space + (Stacks.encList Ls).length + 2)
      (57 * (τ.space + (Stacks.encList Ls).length + 2) *
        (τ.space + (Stacks.encList Ls).length + 2) +
        29 * (τ.space + (Stacks.encList Ls).length + 2) + 3) := by
  have e := Stmt.execLe_memTest (σ := fun r => τ (f r)) (L := Ls) h1 h2 h3 h4 h5 h6 h7 h8
  have r := ExecLe.rename_of_comp hf e
  have hsp := Stacks.space_extend hf (fun r => τ (f r)) τ
  rw [Stacks.extend_comp_self hf τ] at hsp
  have hfin : Function.extend f (Function.update (fun r => τ (f r)) 2
      [decide ((fun r => τ (f r)) 0 ∈ Ls)]) τ =
      Function.update τ (f 2) [decide (τ (f 0) ∈ Ls)] := by
    rw [← Stacks.update_extend hf, Stacks.extend_comp_self hf τ]
  rw [hfin] at r
  refine (r.mono (by omega)).mono_time ?_
  have hle : Stacks.space (fun r => τ (f r)) ≤ τ.space := by omega
  have := Nat.mul_le_mul
    (Nat.mul_le_mul_left 57 (Nat.add_le_add_right (Nat.add_le_add_right hle
      (Stacks.encList Ls).length) 2))
    (Nat.add_le_add_right (Nat.add_le_add_right hle (Stacks.encList Ls).length) 2)
  omega

/-- Table write: push the code of the index string on stack `Z` onto the table on stack `D`,
through the empty work stack `t`. -/
def tabWrite {k : ℕ} (Z t D : Fin k) : Stmt k := QEnum.pushCode Z t D

/-- The table write `tabWrite Z t D` is built from pop-loops only (`Stmt.PopLoops`), so its running
time is bounded by its step budget. -/
theorem popLoops_tabWrite {k : ℕ} {Z t D : Fin k} (hZt : Z ≠ t) (htD : t ≠ D) :
    (tabWrite Z t D).PopLoops := by
  simp [tabWrite, QEnum.pushCode, QEnum.pushCodeBody, Stmt.seqs, Stmt.moveAll, Stmt.moveBit,
    Stmt.caseBit, Stmt.PopLoops, Stmt.NoPush, Stmt.Pops, hZt, hZt.symm, htD.symm]

/-- **Table write.** If the work stack `t` is empty, `tabWrite Z t D` prepends the code
`Stacks.encStr (σ Z)` of the string on `Z` to the table on `D` and changes nothing else, within
the space `σ.space + 2 |σ Z| + 1` and the step budget of `tabWrite` for that space. -/
theorem execLe_tabWrite {k : ℕ} {Z t D : Fin k} (hZt : Z ≠ t) (hZD : Z ≠ D) (htD : t ≠ D)
    {σ : Stacks k} (ht : σ t = []) :
    ExecLe (tabWrite Z t D) σ (Function.update σ D (Stacks.encStr (σ Z) ++ σ D))
      (σ.space + 2 * (σ Z).length + 1)
      ((tabWrite Z t D).budget (σ.space + 2 * (σ Z).length + 1)) :=
  (QEnum.exec_pushCode hZt hZD htD ht).execLe_budget (popLoops_tabWrite hZt htD)

/-- A write prepends the index string to the list of `true` entries. -/
theorem encStr_append_encList (z : BitString) (Ls : List BitString) :
    Stacks.encStr z ++ Stacks.encList Ls = Stacks.encList (z :: Ls) := by
  simp [Stacks.encList]

/-! ### A loop over all bit strings of a given length

`forBits C t Cy body` runs `body` once for every bit string of length `M`, held on the counter
`C` in the order of `incBits` from `bitsOf M 0` (all `false`) — the `j`-th string is
`bitsOf M j` — with the carry flag on `Cy` (`[false]` while running, `[true]` at the end) and
the empty work stack `t`; the counter is back to `bitsOf M 0` at the end, so the loop can be
nested.  Its specification `execLe_forBits` carries an invariant indexed by the number of
iterations done; the invariant may not look at `C` and `Cy` (hypothesis `hfr`). -/

/-- **The binary increment on counters.** For `j < 2 ^ M`, `incBits` takes `bitsOf M j` to
`bitsOf M (j + 1)` with carry `false` when `j + 1 < 2 ^ M`, and wraps around to `bitsOf M 0` with
carry `true` when `j + 1 = 2 ^ M`. -/
theorem incBits_bitsOf {M j : ℕ} (hj : j < 2 ^ M) :
    (j + 1 < 2 ^ M →
      incBits (bitsOf M j) = bitsOf M (j + 1) ∧ incCarry (bitsOf M j) = false) ∧
    (j + 1 = 2 ^ M → incBits (bitsOf M j) = bitsOf M 0 ∧ incCarry (bitsOf M j) = true) := by
  have h := binVal_incBits (bitsOf M j)
  have hl : (incBits (bitsOf M j)).length = M := by rw [length_incBits, length_bitsOf]
  have hlt := binVal_lt (incBits (bitsOf M j))
  rw [hl] at hlt
  rw [binVal_bitsOf_of_lt hj, length_bitsOf] at h
  have hb := bitsOf_binVal (incBits (bitsOf M j))
  rw [hl] at hb
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · cases hc : incCarry (bitsOf M j)
    · rw [hc] at h
      simp only [Bool.toNat_false, mul_zero, add_zero] at h
      rw [← h, hb]
      exact ⟨rfl, rfl⟩
    · rw [hc] at h
      simp only [Bool.toNat_true, mul_one] at h
      omega
  · cases hc : incCarry (bitsOf M j)
    · rw [hc] at h
      simp only [Bool.toNat_false, mul_zero, add_zero] at h
      omega
    · rw [hc] at h
      simp only [Bool.toNat_true, mul_one] at h
      have h0 : binVal (incBits (bitsOf M j)) = 0 := by omega
      rw [← h0, hb]
      exact ⟨rfl, rfl⟩

/-- The loop over all bit strings of length `M` on the counter `C`. -/
def forBits {k : ℕ} (C t Cy : Fin k) (body : Stmt k) : Stmt k :=
  .loop Cy (fun o => o == some false) (.seq body (.seq (.pop Cy) (Stmt.incr C t Cy)))

/-- **The loop over all bit strings of length `M`.** Let `Inv j` be an invariant of the states after
`j` iterations that does not look at `C` and `Cy` (`hfr`) and keeps the space within `S` (`hsp`).
Suppose that for every `j < 2 ^ M`, `body` run within space `S` and `τ` steps from a state with
`Inv j`, the counter `bitsOf M j`, the carry `[false]` and `t` empty ends in a state with
`Inv (j + 1)` and the same counter, carry and empty `t`.  Then from a state with `Inv 0`, the
counter `bitsOf M 0`, the carry `[false]` and `t` empty, `forBits C t Cy body` runs within space
`S` and `2 ^ M * (τ + 10 * S + 20) + 1` steps to a state with `Inv (2 ^ M)`, the counter back at
`bitsOf M 0`, the carry `[true]` and `t` empty. -/
theorem execLe_forBits {k : ℕ} {C t Cy : Fin k} (hCt : C ≠ t) (hCCy : C ≠ Cy)
    (htCy : t ≠ Cy) {body : Stmt k} (M S τ : ℕ) (Inv : ℕ → Stacks k → Prop)
    (hfr : ∀ j σ σ', Inv j σ → (∀ r, r ≠ C → r ≠ Cy → σ' r = σ r) → Inv j σ')
    (hsp : ∀ j σ, Inv j σ → (σ C).length = M → (σ Cy).length = 1 → σ.space ≤ S)
    (hbody : ∀ j < 2 ^ M, ∀ σ, Inv j σ → σ C = bitsOf M j → σ Cy = [false] →
      σ t = [] →
      ∃ σ', ExecLe body σ σ' S τ ∧ Inv (j + 1) σ' ∧ σ' C = bitsOf M j ∧
        σ' Cy = [false] ∧ σ' t = [])
    (σ : Stacks k) (h0 : Inv 0 σ) (hC : σ C = bitsOf M 0) (hCy : σ Cy = [false])
    (ht : σ t = []) :
    ∃ σ', ExecLe (forBits C t Cy body) σ σ' S (2 ^ M * (τ + 10 * S + 20) + 1) ∧
      Inv (2 ^ M) σ' ∧ σ' C = bitsOf M 0 ∧ σ' Cy = [true] ∧ σ' t = [] := by
  let I : Stacks k → Prop := fun σ => ∃ j ≤ 2 ^ M, Inv j σ ∧ σ t = [] ∧
    ((j < 2 ^ M ∧ σ C = bitsOf M j ∧ σ Cy = [false]) ∨
      (j = 2 ^ M ∧ σ C = bitsOf M 0 ∧ σ Cy = [true]))
  let μ : Stacks k → ℕ := fun σ => if σ Cy = [true] then 0 else 2 ^ M - binVal (σ C)
  have hstep : ∀ σ, I σ → (fun o => o == some false) (σ Cy).head? = true →
      ∃ σ', ExecLe (.seq body (.seq (.pop Cy) (Stmt.incr C t Cy))) σ σ' S
        (τ + 10 * S + 18) ∧ I σ' ∧ μ σ' < μ σ := by
    rintro σ ⟨j, hjle, hInv, hσt, ⟨hj, hσC, hσCy⟩ | ⟨rfl, hσC, hσCy⟩⟩ hcond
    · obtain ⟨σ1, e1, hInv1, h1C, h1Cy, h1t⟩ := hbody j hj σ hInv hσC hσCy hσt
      have sp1 := e1.toExec.space_le.2
      have hs2 : Stacks.space (Function.update σ1 Cy (σ1 Cy).tail) + 1 = Stacks.space σ1 := by
        have := Stacks.space_update σ1 Cy (σ1 Cy).tail
        rw [h1Cy] at this ⊢
        simpa using this
      set σ2 := Function.update σ1 Cy (σ1 Cy).tail with hσ2
      have e2 : ExecLe (.pop Cy) σ1 σ2 S 1 := ExecLe.pop sp1 le_rfl
      have h2t : σ2 t = [] := by rw [hσ2, Function.update_of_ne htCy, h1t]
      have h2Cy : σ2 Cy = [] := by rw [hσ2, Function.update_self, h1Cy]; rfl
      have h2C : σ2 C = bitsOf M j := by rw [hσ2, Function.update_of_ne hCCy, h1C]
      have e3 := Stmt.execLe_incr hCt hCCy htCy h2t h2Cy
      rw [h2C] at e3
      have e3' := (e3.mono (show Stacks.space σ2 + 1 ≤ S by omega)).mono_time
        (show 10 * (Stacks.space σ2 + 1) + 7 ≤ 10 * S + 17 by omega)
      set σ3 := Function.update (Function.update σ2 C (incBits (bitsOf M j))) Cy
        [incCarry (bitsOf M j)] with hσ3
      have hfr3 : ∀ r, r ≠ C → r ≠ Cy → σ3 r = σ1 r := by
        intro r hrC hrCy
        rw [hσ3, Function.update_of_ne hrCy, Function.update_of_ne hrC, hσ2,
          Function.update_of_ne hrCy]
      have hInv3 : Inv (j + 1) σ3 := hfr _ _ _ hInv1 hfr3
      have h3t : σ3 t = [] := by rw [hfr3 t hCt.symm htCy, h1t]
      have h3Cy : σ3 Cy = [incCarry (bitsOf M j)] := by rw [hσ3, Function.update_self]
      have h3C : σ3 C = incBits (bitsOf M j) := by
        rw [hσ3, Function.update_of_ne hCCy, Function.update_self]
      have hμ : μ σ = 2 ^ M - j := by
        change (if σ Cy = [true] then 0 else 2 ^ M - binVal (σ C)) = 2 ^ M - j
        rw [hσCy, hσC, ite_eq_right (by simp), binVal_bitsOf_of_lt hj]
      refine ⟨σ3, ((e1.seq (e2.seq e3')).mono_time (by omega)), ?_, ?_⟩
      · obtain ⟨hA, hB⟩ := incBits_bitsOf hj (M := M)
        rcases Nat.lt_or_ge (j + 1) (2 ^ M) with hj1 | hj1
        · obtain ⟨hi, hc⟩ := hA hj1
          exact ⟨j + 1, hj1.le, hInv3, h3t, Or.inl ⟨hj1, by rw [h3C, hi], by rw [h3Cy, hc]⟩⟩
        · obtain ⟨hi, hc⟩ := hB (by omega)
          exact ⟨j + 1, by omega, hInv3, h3t,
            Or.inr ⟨by omega, by rw [h3C, hi], by rw [h3Cy, hc]⟩⟩
      · rw [hμ]
        change (if σ3 Cy = [true] then 0 else 2 ^ M - binVal (σ3 C)) < 2 ^ M - j
        obtain ⟨hA, hB⟩ := incBits_bitsOf hj (M := M)
        rcases Nat.lt_or_ge (j + 1) (2 ^ M) with hj1 | hj1
        · obtain ⟨hi, hc⟩ := hA hj1
          rw [h3Cy, hc, ite_eq_right (by simp), h3C, hi, binVal_bitsOf_of_lt hj1]
          omega
        · obtain ⟨hi, hc⟩ := hB (by omega)
          rw [h3Cy, hc, ite_eq_left rfl]
          omega
    · rw [hσCy] at hcond
      simp at hcond
  have hexit : ∀ σ, I σ → σ.space ≤ S := by
    rintro σ ⟨j, -, hInv, -, ⟨-, hC', hCy'⟩ | ⟨-, hC', hCy'⟩⟩
    · exact hsp j σ hInv (by rw [hC', length_bitsOf]) (by rw [hCy']; rfl)
    · exact hsp j σ hInv (by rw [hC', length_bitsOf]) (by rw [hCy']; rfl)
  obtain ⟨σ', e, hI', hc'⟩ :=
    ExecLe.loop_of_variant (r := Cy) (cond := fun o => o == some false)
    (body := .seq body (.seq (.pop Cy) (Stmt.incr C t Cy))) I μ S (τ + 10 * S + 18) hstep hexit σ
    ⟨0, Nat.zero_le _, h0, ht, Or.inl ⟨Nat.two_pow_pos M, hC, hCy⟩⟩
  have hμ0 : μ σ = 2 ^ M := by
    change (if σ Cy = [true] then 0 else 2 ^ M - binVal (σ C)) = 2 ^ M
    rw [hCy, hC, ite_eq_right (by simp), binVal_bitsOf_of_lt (Nat.two_pow_pos M)]
    rfl
  rw [hμ0] at e
  obtain ⟨j, -, hInv', ht', ⟨-, -, hCy'⟩ | ⟨rfl, hC', hCy'⟩⟩ := hI'
  · rw [hCy'] at hc'
    simp at hc'
  · exact ⟨σ', e.mono_time (le_of_eq (by ring)), hInv', hC', hCy', ht'⟩

/-! ### Accumulating a flag over all bit strings (`any`) -/

/-- Two states whose stacks have the same lengths have the same space. -/
theorem space_eq_of_length {k : ℕ} {σ σ' : Stacks k}
    (h : ∀ r, (σ r).length = (σ' r).length) : σ.space = σ'.space := by
  unfold Stacks.space
  exact Finset.sum_congr rfl fun r _ => h r

/-- One step of an `any` loop: `sb` pushes a bit on the empty stack `G`; it is or-ed into the
flag `Acc`, and `G` is popped. -/
def anyBody {k : ℕ} (G Acc : Fin k) (sb : Stmt k) : Stmt k :=
  .seq sb (.seq (.ite G (fun o => o == some true) (Stmt.setFlag Acc) .skip) (.pop G))

/-- **One step of an `any` loop.** If `sb` pushes the bit `b` on the empty stack `G` within `S`
and `τ` steps, then `anyBody G Acc sb` replaces the flag `[a]` on `Acc` by `[a || b]`, leaves `G`
empty and changes nothing else, within `S` and `τ + 5` steps. -/
theorem execLe_anyBody {k : ℕ} {G Acc : Fin k} (hGA : G ≠ Acc) {sb : Stmt k} {σ : Stacks k}
    {b a : Bool} {S τ : ℕ} (hG : σ G = []) (hAcc : σ Acc = [a])
    (hb : ExecLe sb σ (Function.update σ G [b]) S τ) :
    ExecLe (anyBody G Acc sb) σ (Function.update σ Acc [a || b]) S (τ + 5) := by
  have sp1 := hb.toExec.space_le.2
  set σ1 := Function.update σ G [b] with hσ1
  have h1G : σ1 G = [b] := by rw [hσ1, Function.update_self]
  have h1A : σ1 Acc = [a] := by rw [hσ1, Function.update_of_ne hGA.symm, hAcc]
  cases b
  · have e2 : ExecLe (.ite G (fun o => o == some true) (Stmt.setFlag Acc) .skip) σ1 σ1 S 2 :=
      ExecLe.iteF (by rw [h1G]; rfl) (ExecLe.skip sp1)
    have e3 : ExecLe (.pop G) σ1 (Function.update σ1 G (σ1 G).tail) S 1 := ExecLe.pop sp1 le_rfl
    have hfin : Function.update σ1 G (σ1 G).tail = Function.update σ Acc [a || false] := by
      rw [h1G, hσ1, Function.update_idem, Bool.or_false]
      funext r
      by_cases hr : r = G
      · subst hr; rw [Function.update_self, Function.update_of_ne hGA, hG]; rfl
      · by_cases hr' : r = Acc
        · subst hr'; rw [Function.update_of_ne hr, Function.update_self, hAcc]
        · rw [Function.update_of_ne hr, Function.update_of_ne hr']
    rw [hfin] at e3
    exact (hb.seq (e2.seq e3)).mono_time (by omega)
  · have e2' := Stmt.execT_setFlag (F := Acc) h1A
    have e2 : ExecLe (.ite G (fun o => o == some true) (Stmt.setFlag Acc) .skip) σ1
        (Function.update σ1 Acc [true]) S 4 :=
      ExecLe.iteT (by rw [h1G]; rfl) ((ExecLe.of_execT e2').mono sp1)
    have sp2 := e2.toExec.space_le.2
    have e3 := ExecLe.pop (r := G) sp2 (le_refl 1)
    have hfin : Function.update (Function.update σ1 Acc [true]) G
        ((Function.update σ1 Acc [true]) G).tail = Function.update σ Acc [a || true] := by
      rw [Function.update_of_ne hGA, h1G, hσ1, Bool.or_true]
      funext r
      by_cases hr : r = G
      · subst hr
        rw [Function.update_self, Function.update_of_ne hGA, hG]; rfl
      · rw [Function.update_of_ne hr]
        by_cases hr' : r = Acc
        · subst hr'; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hr', Function.update_of_ne hr', Function.update_of_ne hr]
    rw [hfin] at e3
    exact (hb.seq (e2.seq e3)).mono_time (by omega)

/-- The `any` loop over all bit strings of length `M` on the counter `C`. -/
def forAny {k : ℕ} (C t Cy G Acc : Fin k) (sb : Stmt k) : Stmt k :=
  forBits C t Cy (anyBody G Acc sb)

/-- Quantifying over the numbers `i < 2 ^ M` through `bitsOf M i` is the same as quantifying over
the bit strings of length `M`. -/
theorem exists_bitsOf_iff (M : ℕ) (b : BitString → Bool) :
    (∃ i < 2 ^ M, b (bitsOf M i) = true) ↔ ∃ s : BitString, s.length = M ∧ b s = true := by
  constructor
  · rintro ⟨i, -, h⟩
    exact ⟨bitsOf M i, length_bitsOf M i, h⟩
  · rintro ⟨s, hs, h⟩
    refine ⟨binVal s, hs ▸ binVal_lt s, ?_⟩
    rw [← hs, bitsOf_binVal]
    exact h

/-- **The `any` loop**: if `sb`, on any stacks that agree with `σ0` off `C`, `Cy`, `Acc`, pushes
`[b (counter)]` on `G`, then `forAny` sets `Acc` to `[(allBits M).any b]` (`∃ s, |s| = M ∧ b s`)
and the carry to `[true]`, and changes nothing else. -/
theorem execLe_forAny {k : ℕ} {C t Cy G Acc : Fin k} (hCt : C ≠ t) (hCCy : C ≠ Cy)
    (htCy : t ≠ Cy) (hGA : G ≠ Acc) (hAC : Acc ≠ C) (hACy : Acc ≠ Cy) (hGC : G ≠ C)
    (hGCy : G ≠ Cy) (htA : t ≠ Acc) {sb : Stmt k} (M S τ : ℕ) (b : BitString → Bool)
    (σ0 : Stacks k)
    (hsb : ∀ σ : Stacks k, (∀ r, r ≠ C → r ≠ Cy → r ≠ Acc → σ r = σ0 r) →
      (σ C).length = M → σ Cy = [false] → (σ Acc).length = 1 →
      ExecLe sb σ (Function.update σ G [b (σ C)]) S τ)
    (hC : σ0 C = bitsOf M 0) (hCy : σ0 Cy = [false]) (ht : σ0 t = [])
    (hG : σ0 G = []) (hAcc : σ0 Acc = [false]) :
    ∃ σ', ExecLe (forAny C t Cy G Acc sb) σ0 σ' S (2 ^ M * (τ + 5 + 10 * S + 20) + 1) ∧
      σ' = Function.update (Function.update σ0 Acc [(allBits M).any b]) Cy [true] := by
  have hS : σ0.space ≤ S :=
    (hsb σ0 (fun _ _ _ _ => rfl) (by rw [hC, length_bitsOf]) hCy (by simp [hAcc])).toExec.space_le.1
  let Inv : ℕ → Stacks k → Prop := fun j σ =>
    (∀ r, r ≠ C → r ≠ Cy → r ≠ Acc → σ r = σ0 r) ∧
      σ Acc = [decide (∃ i < j, b (bitsOf M i) = true)]
  have hfr : ∀ j σ σ', Inv j σ →
      (∀ r, r ≠ C → r ≠ Cy → σ' r = σ r) → Inv j σ' := by
    rintro j σ σ' ⟨h1, h2⟩ h
    exact ⟨fun r hr1 hr2 hr3 => (h r hr1 hr2).trans (h1 r hr1 hr2 hr3),
      (h Acc hAC hACy).trans h2⟩
  have hsp : ∀ j σ, Inv j σ → (σ C).length = M → (σ Cy).length = 1 →
      σ.space ≤ S := by
    rintro j σ ⟨h1, h2⟩ hlC hlCy
    rw [space_eq_of_length (σ' := σ0) fun r => ?_]
    · exact hS
    · by_cases hr1 : r = C
      · subst hr1; rw [hlC, hC, length_bitsOf]
      · by_cases hr2 : r = Cy
        · subst hr2; rw [hlCy, hCy]; rfl
        · by_cases hr3 : r = Acc
          · subst hr3; rw [h2, hAcc]; rfl
          · rw [h1 r hr1 hr2 hr3]
  have hbody : ∀ j < 2 ^ M, ∀ σ, Inv j σ → σ C = bitsOf M j → σ Cy = [false] →
      σ t = [] → ∃ σ', ExecLe (anyBody G Acc sb) σ σ' S (τ + 5) ∧ Inv (j + 1) σ' ∧
        σ' C = bitsOf M j ∧ σ' Cy = [false] ∧ σ' t = [] := by
    rintro j - σ ⟨h1, h2⟩ hσC hσCy hσt
    have hσG : σ G = [] := by rw [h1 G hGC hGCy hGA, hG]
    have hb := hsb σ h1 (by rw [hσC, length_bitsOf]) hσCy (by rw [h2]; rfl)
    rw [hσC] at hb
    refine ⟨_, execLe_anyBody hGA hσG h2 hb, ⟨fun r hr1 hr2 hr3 => ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne hr3, h1 r hr1 hr2 hr3]
    · rw [Function.update_self]
      congr 1
    · rw [Function.update_of_ne hAC.symm, hσC]
    · rw [Function.update_of_ne hACy.symm, hσCy]
    · rw [Function.update_of_ne htA, hσt]
  have h0 : Inv 0 σ0 := ⟨fun _ _ _ _ => rfl, by rw [hAcc]; simp⟩
  obtain ⟨σ', e, ⟨h1, h2⟩, hC', hCy', -⟩ :=
    execLe_forBits hCt hCCy htCy M S (τ + 5) Inv hfr hsp hbody σ0 h0 hC hCy ht
  refine ⟨σ', e, ?_⟩
  funext r
  by_cases hr2 : r = Cy
  · subst hr2; rw [Function.update_self, hCy']
  · rw [Function.update_of_ne hr2]
    by_cases hr3 : r = Acc
    · subst hr3
      rw [Function.update_self, h2]
      congr 1
      rw [Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true, exists_bitsOf_iff]
      simp only [mem_allBits]
    · rw [Function.update_of_ne hr3]
      by_cases hr1 : r = C
      · subst hr1; rw [hC', hC]
      · exact h1 r hr1 hr2 hr3

/-! ### Small facts for the driver -/

/-- The `w` low bits of `0` are `w` copies of `false`. -/
theorem bitsOf_zero : ∀ w : ℕ, bitsOf w 0 = List.replicate w false
  | 0 => rfl
  | w + 1 => by
    change decide (0 % 2 = 1) :: bitsOf w (0 / 2) = false :: List.replicate w false
    rw [Nat.zero_div, bitsOf_zero w]
    rfl

/-- Cutting `n * w` copies of `false` into `n` slots of `w` bits gives `n` slots of `w` copies of
`false`. -/
theorem slots_replicate_false (w : ℕ) :
    ∀ n : ℕ,
      slots w n (List.replicate (n * w) false) = List.replicate n (List.replicate w false)
  | 0 => rfl
  | n + 1 => by
    change (List.replicate ((n + 1) * w) false).take w ::
        slots w n ((List.replicate ((n + 1) * w) false).drop w) = _
    rw [List.take_replicate, List.drop_replicate, show min w ((n + 1) * w) = w by
      rw [Nat.succ_mul]; omega, show (n + 1) * w - w = n * w by rw [Nat.succ_mul]; omega,
      slots_replicate_false w n, List.replicate_succ]

/-- The all-`false` code (the first value of the counter) is the code of the empty key: the
root move of `valKC` is `sMove` on the counter's start value. -/
theorem decK_bitsOf_zero (L n : ℕ) : decK L n (bitsOf (n * (2 * L + 1)) 0) = ∅ := by
  unfold decK
  rw [bitsOf_zero, slots_replicate_false,
    show List.replicate (2 * L + 1) false = emptySlot L from rfl,
    List.filterMap_replicate_of_none (decSlot_emptySlot L)]
  rfl

/-- The length of a table of index strings of length `M`. -/
theorem length_encList_of_forall {M : ℕ} :
    ∀ Ls : List BitString, (∀ s ∈ Ls, s.length = M) →
      (Stacks.encList Ls).length = Ls.length * (2 * M + 1)
  | [], _ => by simp [Stacks.encList]
  | s :: Ls, h => by
    have ih := length_encList_of_forall Ls fun t ht => h t (List.mem_cons_of_mem _ ht)
    have hs := h s List.mem_cons_self
    rw [← encStr_append_encList, List.length_append, Stacks.length_encStr, ih, hs,
      List.length_cons, Nat.succ_mul]
    ring

/-! ### Writing the strings of a predicate (`filter`) -/

/-- The step budget of a statement grows with the space bound. -/
theorem budget_mono {k : ℕ} :
    ∀ (s : Stmt k) {S S' : ℕ}, S ≤ S' → s.budget S ≤ s.budget S'
  | .skip, _, _, _ => le_rfl
  | .push _ _, _, _, _ => le_rfl
  | .pop _, _, _, _ => le_rfl
  | .seq s₁ s₂, _, _, h => Nat.add_le_add (budget_mono s₁ h) (budget_mono s₂ h)
  | .ite _ _ s₁ s₂, _, _, h => max_le_max (Nat.add_le_add_right (budget_mono s₁ h) 2)
      (Nat.add_le_add_right (budget_mono s₂ h) 1)
  | .loop _ _ b, _, _, h => Nat.add_le_add_right
      (Nat.mul_le_mul h (Nat.add_le_add_right (budget_mono b h) 2)) 1

/-- One step of a filter loop: `sb` pushes a bit on the empty stack `G`; if it is `true`, the
code of the counter `C` is pushed on the table `Tn` (`tabWrite`, work stack `tw`); `G` is
popped. -/
def filterBody {k : ℕ} (C tw G Tn : Fin k) (sb : Stmt k) : Stmt k :=
  .seq sb (.seq (.ite G (fun o => o == some true) (tabWrite C tw Tn) .skip) (.pop G))

/-- **One step of a filter loop.** Let `sb` push the bit `v` on the empty stack `G` within `S` and
`τ` steps, let `tw` be empty, and let `S` leave room for one more table entry
(`σ.space + 1 + 2 |σ C| + 1 ≤ S`).  Then `filterBody C tw G Tn sb` leaves `G` empty and, if `v`
is `true`, prepends the code of the counter `σ C` to the table on `Tn`; otherwise it changes
nothing.  It runs within `S` and `τ + (tabWrite C tw Tn).budget S + 3` steps. -/
theorem execLe_filterBody {k : ℕ} {C tw G Tn : Fin k} (hCtw : C ≠ tw) (hCTn : C ≠ Tn)
    (htwTn : tw ≠ Tn) (hGC : G ≠ C) (hGtw : G ≠ tw) (hGTn : G ≠ Tn) {sb : Stmt k}
    {σ : Stacks k} {v : Bool} {S τ : ℕ} (hG : σ G = []) (htw : σ tw = [])
    (hb : ExecLe sb σ (Function.update σ G [v]) S τ)
    (hS : σ.space + 1 + 2 * (σ C).length + 1 ≤ S) :
    ExecLe (filterBody C tw G Tn sb) σ
      (if v then Function.update σ Tn (Stacks.encStr (σ C) ++ σ Tn) else σ) S
      (τ + (tabWrite C tw Tn).budget S + 3) := by
  have sp1 := hb.toExec.space_le.2
  set σ1 := Function.update σ G [v] with hσ1
  have h1G : σ1 G = [v] := by rw [hσ1, Function.update_self]
  have hs1 : Stacks.space σ1 = σ.space + 1 := by
    have := Stacks.space_update σ G [v]
    rw [hG] at this
    simp only [List.length_nil, List.length_cons, add_zero] at this
    rw [hσ1]; omega
  cases v
  · have e2 : ExecLe (.ite G (fun o => o == some true) (tabWrite C tw Tn) .skip) σ1 σ1 S 2 :=
      ExecLe.iteF (by rw [h1G]; rfl) (ExecLe.skip sp1)
    have e3 : ExecLe (.pop G) σ1 (Function.update σ1 G (σ1 G).tail) S 1 := ExecLe.pop sp1 le_rfl
    have hfin : Function.update σ1 G (σ1 G).tail = σ := by
      rw [h1G, hσ1, Function.update_idem]
      funext r
      by_cases hr : r = G
      · subst hr; rw [Function.update_self, hG]; rfl
      · rw [Function.update_of_ne hr]
    rw [hfin] at e3
    refine (hb.seq (e2.seq e3)).mono_time (by omega)
  · have h1tw : σ1 tw = [] := by rw [hσ1, Function.update_of_ne hGtw.symm, htw]
    have h1C : σ1 C = σ C := by rw [hσ1, Function.update_of_ne hGC.symm]
    have e2' := execLe_tabWrite hCtw hCTn htwTn h1tw
    rw [h1C] at e2'
    have e2'' := (e2'.mono (show Stacks.space σ1 + 2 * (σ C).length + 1 ≤ S by omega)).mono_time
      (budget_mono (tabWrite C tw Tn)
        (show Stacks.space σ1 + 2 * (σ C).length + 1 ≤ S by omega))
    have e2 := ExecLe.iteT (s₂ := .skip) (r := G) (cond := fun o => o == some true)
      (by rw [h1G]; rfl) e2''
    have sp2 := e2.toExec.space_le.2
    have e3 := ExecLe.pop (r := G) sp2 (le_refl 1)
    have hfin : Function.update (Function.update σ1 Tn (Stacks.encStr (σ C) ++ σ1 Tn)) G
        ((Function.update σ1 Tn (Stacks.encStr (σ C) ++ σ1 Tn)) G).tail =
        Function.update σ Tn (Stacks.encStr (σ C) ++ σ Tn) := by
      rw [Function.update_of_ne hGTn, h1G, hσ1, Function.update_of_ne hGTn.symm]
      funext r
      by_cases hr : r = G
      · subst hr
        rw [Function.update_self, Function.update_of_ne hGTn, hG]; rfl
      · rw [Function.update_of_ne hr]
        by_cases hr' : r = Tn
        · subst hr'; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hr', Function.update_of_ne hr', Function.update_of_ne hr]
    rw [hfin] at e3
    exact (hb.seq (e2.seq e3)).mono_time (by omega)

/-- The filter loop over all bit strings of length `M` on the counter `C`. -/
def forFilter {k : ℕ} (C t Cy tw G Tn : Fin k) (sb : Stmt k) : Stmt k :=
  forBits C t Cy (filterBody C tw G Tn sb)

/-- **The filter loop**: if `sb`, on any stacks that agree with `σ0` off `C`, `Cy`, `Tn` (and
are not larger than `σ0` plus a full table), pushes `[v (counter)]` on `G`, then `forFilter`
prepends to the table `encList L0` on `Tn` a list `Lw` of exactly the strings `s` of length `M`
with `v s`, sets the carry to `[true]` and changes nothing else.  The space bound is that of `σ0`
plus a full table of `2 ^ M` strings of length `M`, the room for writing one more entry, and the
extra space `B` that `sb` needs. -/
theorem execLe_forFilter {k : ℕ} {C t Cy tw G Tn : Fin k} (hCt : C ≠ t) (hCCy : C ≠ Cy)
    (htCy : t ≠ Cy) (hCtw : C ≠ tw) (hCTn : C ≠ Tn) (htwTn : tw ≠ Tn) (hGC : G ≠ C)
    (hGtw : G ≠ tw) (hGTn : G ≠ Tn) (hGCy : G ≠ Cy) (htwCy : tw ≠ Cy) (hTnCy : Tn ≠ Cy)
    (htTn : t ≠ Tn) {sb : Stmt k} (M B τ : ℕ) (v : BitString → Bool) (σ0 : Stacks k)
    (L0 : List BitString)
    (hsb : ∀ σ : Stacks k, (∀ r, r ≠ C → r ≠ Cy → r ≠ Tn → σ r = σ0 r) →
      (σ C).length = M → σ Cy = [false] → σ.space ≤ σ0.space + 2 ^ M * (2 * M + 1) →
      ExecLe sb σ (Function.update σ G [v (σ C)])
        (σ0.space + 2 ^ M * (2 * M + 1) + 2 * M + 2 + B) τ)
    (hC : σ0 C = bitsOf M 0) (hCy : σ0 Cy = [false]) (ht : σ0 t = []) (htw : σ0 tw = [])
    (hG : σ0 G = []) (hTn : σ0 Tn = Stacks.encList L0) :
    ∃ (σ' : Stacks k) (Lw : List BitString),
      (∀ s, s ∈ Lw ↔ s.length = M ∧ v s = true) ∧ (∀ s ∈ Lw, s.length = M) ∧
      ExecLe (forFilter C t Cy tw G Tn sb) σ0 σ' (σ0.space + 2 ^ M * (2 * M + 1) + 2 * M + 2 + B)
        (2 ^ M * (τ + (tabWrite C tw Tn).budget (σ0.space + 2 ^ M * (2 * M + 1) + 2 * M + 2 + B) +
          3 + 10 * (σ0.space + 2 ^ M * (2 * M + 1) + 2 * M + 2 + B) + 20) + 1) ∧
      σ' = Function.update (Function.update σ0 Tn (Stacks.encList (Lw ++ L0))) Cy [true] := by
  generalize hSdef : σ0.space + 2 ^ M * (2 * M + 1) + 2 * M + 2 + B = S at hsb ⊢
  have hS : σ0.space + 2 ^ M * (2 * M + 1) + 2 * M + 2 ≤ S := by omega
  let Inv : ℕ → Stacks k → Prop := fun j σ =>
    (∀ r, r ≠ C → r ≠ Cy → r ≠ Tn → σ r = σ0 r) ∧ j ≤ 2 ^ M ∧
      ∃ Lw : List BitString,
        (∀ s, s ∈ Lw ↔ ∃ i < j, s = bitsOf M i ∧ v (bitsOf M i) = true) ∧
        (∀ s ∈ Lw, s.length = M) ∧ Lw.length ≤ j ∧ σ Tn = Stacks.encList (Lw ++ L0)
  -- the space of a state of the loop
  have hspace : ∀ σ : Stacks k, (∀ r, r ≠ C → r ≠ Cy → r ≠ Tn → σ r = σ0 r) →
      (σ C).length = M → (σ Cy).length = 1 →
      σ.space + (σ0 Tn).length = σ0.space + (σ Tn).length := by
    intro σ h1 hlC hlCy
    have e1 := Stacks.space_update σ0 Tn (σ Tn)
    have e2 : σ.space = Stacks.space (Function.update σ0 Tn (σ Tn)) := by
      apply space_eq_of_length
      intro r
      by_cases hr : r = Tn
      · subst hr; rw [Function.update_self]
      · rw [Function.update_of_ne hr]
        by_cases hr1 : r = C
        · subst hr1; rw [hlC, hC, length_bitsOf]
        · by_cases hr2 : r = Cy
          · subst hr2; rw [hlCy, hCy]; rfl
          · rw [h1 r hr1 hr2 hr]
    omega
  have hfr : ∀ j σ σ', Inv j σ →
      (∀ r, r ≠ C → r ≠ Cy → σ' r = σ r) → Inv j σ' := by
    rintro j σ σ' ⟨h1, hj, Lw, h2, h3, h4, h5⟩ h
    exact ⟨fun r hr1 hr2 hr3 => (h r hr1 hr2).trans (h1 r hr1 hr2 hr3), hj, Lw, h2, h3, h4,
      (h Tn hCTn.symm hTnCy).trans h5⟩
  have hTnlen : ∀ Lw : List BitString, (∀ s ∈ Lw, s.length = M) →
      (Stacks.encList (Lw ++ L0)).length = Lw.length * (2 * M + 1) + (σ0 Tn).length := by
    intro Lw hLw
    rw [hTn, Stacks.encList, List.flatMap_append, List.length_append,
      ← Stacks.encList, ← Stacks.encList, length_encList_of_forall Lw hLw]
  have hsp : ∀ j σ, Inv j σ → (σ C).length = M → (σ Cy).length = 1 →
      σ.space ≤ S := by
    rintro j σ ⟨h1, hj, Lw, -, h3, h4, h5⟩ hlC hlCy
    have := hspace σ h1 hlC hlCy
    rw [h5, hTnlen Lw h3] at this
    have hm := Nat.mul_le_mul_right (2 * M + 1) (h4.trans hj)
    omega
  have hbody : ∀ j < 2 ^ M, ∀ σ, Inv j σ → σ C = bitsOf M j → σ Cy = [false] →
      σ t = [] → ∃ σ', ExecLe (filterBody C tw G Tn sb) σ σ' S
        (τ + (tabWrite C tw Tn).budget S + 3) ∧ Inv (j + 1) σ' ∧ σ' C = bitsOf M j ∧
        σ' Cy = [false] ∧ σ' t = [] := by
    rintro j hj σ ⟨h1, -, Lw, h2, h3, h4, h5⟩ hσC hσCy hσt
    have hσG : σ G = [] := by rw [h1 G hGC hGCy hGTn, hG]
    have hσtw : σ tw = [] := by rw [h1 tw hCtw.symm htwCy htwTn, htw]
    have hlC : (σ C).length = M := by rw [hσC, length_bitsOf]
    have hsz := hspace σ h1 hlC (by rw [hσCy]; rfl)
    rw [h5, hTnlen Lw h3] at hsz
    have hm := Nat.mul_le_mul_right (2 * M + 1) (show Lw.length + 1 ≤ 2 ^ M by omega)
    rw [Nat.succ_mul] at hm
    have hb := hsb σ h1 hlC hσCy (by omega)
    rw [hσC] at hb
    have e := execLe_filterBody hCtw hCTn htwTn hGC hGtw hGTn hσG hσtw hb
      (by rw [hlC]; omega)
    refine ⟨_, e, ?_, ?_, ?_, ?_⟩
    · cases hv : v (bitsOf M j)
      · rw [ite_eq_right (by decide)]
        refine ⟨h1, by omega, Lw, fun s => ?_, h3, by omega, h5⟩
        rw [h2 s]
        constructor
        · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h⟩
        · rintro ⟨i, hi, hs, h⟩
          refine ⟨i, ?_, hs, h⟩
          rcases Nat.lt_or_ge i j with h' | h'
          · exact h'
          · have : i = j := by omega
            subst this; rw [hv] at h; exact absurd h (by simp)
      · rw [ite_eq_left rfl]
        refine ⟨fun r hr1 hr2 hr3 => ?_, by omega, bitsOf M j :: Lw, fun s => ?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne hr3, h1 r hr1 hr2 hr3]
        · rw [List.mem_cons, h2 s]
          constructor
          · rintro (rfl | ⟨i, hi, h⟩)
            · exact ⟨j, by omega, rfl, hv⟩
            · exact ⟨i, by omega, h⟩
          · rintro ⟨i, hi, hs, h⟩
            rcases Nat.lt_or_ge i j with h' | h'
            · exact Or.inr ⟨i, h', hs, h⟩
            · have : i = j := by omega
              subst this; exact Or.inl hs
        · intro s hs
          rcases List.mem_cons.1 hs with rfl | hs
          · exact length_bitsOf M j
          · exact h3 s hs
        · simp only [List.length_cons]; omega
        · rw [Function.update_self, hσC, h5, encStr_append_encList, List.cons_append]
    · cases v (bitsOf M j)
      · exact hσC
      · rw [ite_eq_left rfl, Function.update_of_ne hCTn, hσC]
    · cases v (bitsOf M j)
      · exact hσCy
      · rw [ite_eq_left rfl, Function.update_of_ne hTnCy.symm, hσCy]
    · cases v (bitsOf M j)
      · exact hσt
      · rw [ite_eq_left rfl, Function.update_of_ne htTn, hσt]
  have h0 : Inv 0 σ0 := ⟨fun _ _ _ _ => rfl, Nat.zero_le _, [], fun s => by simp, by simp,
    le_rfl, by rw [hTn]; rfl⟩
  obtain ⟨σ', e, ⟨h1, -, Lw, h2, h3, -, h5⟩, hC', hCy', -⟩ :=
    execLe_forBits hCt hCCy htCy M S (τ + (tabWrite C tw Tn).budget S + 3) Inv hfr hsp hbody
      σ0 h0 hC hCy ht
  refine ⟨σ', Lw, fun s => ?_, h3, e, ?_⟩
  · rw [h2 s]
    constructor
    · rintro ⟨i, -, rfl, h⟩; exact ⟨length_bitsOf M i, h⟩
    · rintro ⟨hs, h⟩
      refine ⟨binVal s, hs ▸ binVal_lt s, ?_, ?_⟩
      · rw [← hs, bitsOf_binVal]
      · rw [← hs, bitsOf_binVal]; exact h
  · funext r
    by_cases hr2 : r = Cy
    · subst hr2; rw [Function.update_self, hCy']
    · rw [Function.update_of_ne hr2]
      by_cases hr3 : r = Tn
      · subst hr3; rw [Function.update_self, h5]
      · rw [Function.update_of_ne hr3]
        by_cases hr1 : r = C
        · subst hr1; rw [hC', hC]
        · exact h1 r hr1 hr2 hr3

end KeyEval
end Kolmogorov.RandomStrings
