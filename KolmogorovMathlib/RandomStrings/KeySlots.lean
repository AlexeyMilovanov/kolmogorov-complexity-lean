/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.KeyCodes
import KolmogorovMathlib.RandomStrings.PathDataSA

/-!
# A slot encoding of keys

A key of `G_{e,x}` has at most `clock e |x|` strings of length `≤ clock e |x|`
(`keyMoveRaw_gameOf_small`).  It is coded by `n` slots of `2L + 1` bits (`n = L = clock e |x|`):
a slot is a presence bit followed by the bits of the string, each preceded by a "continue" flag,
and padding (`encSlot`); the empty slot is all `false` (`emptySlot`).  `decK L n κ` decodes the
slots of a bit string; `encK_spec` is code completeness (every small set has a code among all
bit strings of length `n (2L + 1)`, `allBits`).  With `yesKC_eq`/`valKC_eq` this gives
`valKC_slots_gameOf`: for a sub-adaptive machine, the key recursion over all bit strings of
`clock (2 clock + 1)` bits computes the value of `G_{e,x}` — the exact target of the EXP evaluator
loop over codes.
-/

namespace Kolmogorov.RandomStrings

/-- The bits of a string with a "continue" flag before each bit. -/
def flagBits (z : BitString) : List Bool := z.flatMap fun b => [true, b]

/-- Decoding of `flagBits`, ignoring a padding of `false`s. -/
def unflagBits : List Bool → BitString
  | true :: b :: rest => b :: unflagBits rest
  | _ => []

/-- The slot of a string of length `≤ L`: a presence bit, the flagged bits, padding; `2L + 1`
bits in all. -/
def encSlot (L : ℕ) (z : BitString) : List Bool :=
  true :: (flagBits z ++ List.replicate (2 * (L - z.length)) false)

/-- The empty slot. -/
def emptySlot (L : ℕ) : List Bool := List.replicate (2 * L + 1) false

/-- Decoding of a slot, dropping the presence bit. -/
def decSlot : List Bool → Option BitString
  | true :: rest => some (unflagBits rest)
  | _ => none

/-- The length of a bit string with "continue" flags is twice the length of the string. -/
theorem length_flagBits (z : BitString) : (flagBits z).length = 2 * z.length := by
  induction z with
  | nil => rfl
  | cons b z ih => simp [flagBits] at ih ⊢; omega

/-- Decoding a flagged bit string padded with `false`s returns the original string. -/
theorem unflagBits_flagBits_append (z : BitString) (k : ℕ) :
    unflagBits (flagBits z ++ List.replicate k false) = z := by
  induction z with
  | nil =>
    cases k with
    | zero => rfl
    | succ k => rfl
  | cons b z ih =>
    change unflagBits (true :: b :: (flagBits z ++ List.replicate k false)) = b :: z
    rw [unflagBits, ih]

/-- Decoding an encoded slot recovers the original string. -/
theorem decSlot_encSlot (L : ℕ) (z : BitString) : decSlot (encSlot L z) = some z := by
  simp only [encSlot, decSlot, unflagBits_flagBits_append]

/-- Decoding the empty slot yields `none`. -/
theorem decSlot_emptySlot (L : ℕ) : decSlot (emptySlot L) = none := rfl

/-- The length of a slot coding a string of length `≤ L` is `2L + 1`. -/
theorem length_encSlot {L : ℕ} {z : BitString} (hz : z.length ≤ L) :
    (encSlot L z).length = 2 * L + 1 := by
  simp only [encSlot, List.length_cons, List.length_append, length_flagBits,
    List.length_replicate]
  omega

/-- The length of the empty slot is `2L + 1`. -/
theorem length_emptySlot (L : ℕ) : (emptySlot L).length = 2 * L + 1 := by
  simp [emptySlot]

/-- Cutting a bit string into `k` slots of `w` bits. -/
def slots (w : ℕ) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | k + 1, κ => κ.take w :: slots w k (κ.drop w)

/-- A list of elements of equal length is decomposed to itself by `slots`. -/
theorem slots_flatten (w : ℕ) :
    ∀ ss : List (List Bool), (∀ s ∈ ss, s.length = w) → slots w ss.length ss.flatten = ss := by
  intro ss
  induction ss with
  | nil => intro _; rfl
  | cons s ss ih =>
    intro h
    have hs : s.length = w := h s List.mem_cons_self
    change (s ++ ss.flatten).take w :: slots w ss.length ((s ++ ss.flatten).drop w) = s :: ss
    rw [List.take_left' hs, List.drop_left' hs, ih fun t ht => h t (List.mem_cons_of_mem _ ht)]

/-- The length of a flattened list of elements of equal length `w` is the number of elements
times `w`. -/
theorem length_flatten_of_forall (w : ℕ) :
    ∀ ss : List (List Bool), (∀ s ∈ ss, s.length = w) → ss.flatten.length = ss.length * w := by
  intro ss
  induction ss with
  | nil => intro _; simp
  | cons s ss ih =>
    intro h
    rw [List.flatten_cons, List.length_append, h s List.mem_cons_self,
      ih fun t ht => h t (List.mem_cons_of_mem _ ht), List.length_cons, Nat.succ_mul]
    ring

/-- All bit strings of length `k`. -/
def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBits k).flatMap fun l => [false :: l, true :: l]

/-- A string is in `allBits k` if and only if it has length `k`. -/
theorem mem_allBits : ∀ (k : ℕ) (l : List Bool), l ∈ allBits k ↔ l.length = k := by
  intro k
  induction k with
  | zero => intro l; cases l <;> simp [allBits]
  | succ k ih =>
    intro l
    cases l with
    | nil => simp [allBits]
    | cons b l =>
      simp only [allBits, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false,
        List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨l', hl', h | h⟩ <;> (simp only [List.cons.injEq] at h; rw [← (ih l').1 hl', h.2])
      · intro hl
        refine ⟨l, (ih l).2 hl, ?_⟩
        cases b <;> simp

/-- The key coded by `κ`: the strings in its `n` slots of `2L + 1` bits. -/
def decK (L n : ℕ) (κ : List Bool) : Finset BitString :=
  ((slots (2 * L + 1) n κ).filterMap decSlot).toFinset

/-- The code of a key with at most `n` strings of length `≤ L`. -/
noncomputable def encK (L n : ℕ) (K : Finset BitString) : List Bool :=
  (K.toList.map (encSlot L) ++ List.replicate (n - K.card) (emptySlot L)).flatten

/-- **Code completeness**: every set of at most `n` strings of length `≤ L` has a code of
`n (2L + 1)` bits. -/
theorem encK_spec {L n : ℕ} {K : Finset BitString} (hcard : K.card ≤ n)
    (hlen : ∀ z ∈ K, z.length ≤ L) :
    encK L n K ∈ allBits (n * (2 * L + 1)) ∧ decK L n (encK L n K) = K := by
  have hw : ∀ s ∈ K.toList.map (encSlot L) ++ List.replicate (n - K.card) (emptySlot L),
      s.length = 2 * L + 1 := by
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hs
      exact length_encSlot (hlen z (Finset.mem_toList.1 hz))
    · rw [List.eq_of_mem_replicate hs]; exact length_emptySlot L
  have hlen' :
      (K.toList.map (encSlot L) ++ List.replicate (n - K.card) (emptySlot L)).length = n := by
    simp only [List.length_append, List.length_map, Finset.length_toList, List.length_replicate]
    omega
  refine ⟨(mem_allBits _ _).2 ?_, ?_⟩
  · unfold encK
    rw [length_flatten_of_forall _ _ hw, hlen']
  · unfold decK encK
    have := slots_flatten (2 * L + 1) _ hw
    rw [hlen'] at this
    rw [this, List.filterMap_append, List.filterMap_replicate_of_none (decSlot_emptySlot L),
      List.append_nil, List.filterMap_map]
    have hsome : (List.filterMap (decSlot ∘ encSlot L) K.toList) = K.toList := by
      have : (decSlot ∘ encSlot L) = some := funext fun z => decSlot_encSlot L z
      rw [this, List.filterMap_some]
    rw [hsome, Finset.toList_toFinset]

/-- The cover hypothesis of `yesKC_eq` for the game of a clocked machine and the slot codes with
`clock e |x|` slots of strings of length `≤ clock e |x|`. -/
theorem cover_gameOf (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ)
    (X : Finset BitString) :
    ∀ K : Finset BitString, K ⊆ X → K ⊆ queries c.toOTM (oracleOf h K) x (clock e x.length) →
      ∃ κ ∈ allBits (clock e x.length * (2 * clock e x.length + 1)),
        decK (clock e x.length) (clock e x.length) κ = K := by
  intro K _ hKP
  have hcard : K.card ≤ clock e x.length :=
    (Finset.card_le_card hKP).trans (card_queries_le _ _ _ _)
  have hlen : ∀ z ∈ K, z.length ≤ clock e x.length := by
    intro z hz
    obtain ⟨s, hs, hz'⟩ := (mem_queries _ _ x _ z).1 (hKP hz)
    exact (length_le_of_askedAt _ _ x s z hz').trans hs.le
  exact ⟨_, (encK_spec hcard hlen).1, (encK_spec hcard hlen).2⟩

/-- **The game value by the recursion over slot codes**: for a sub-adaptive machine, the key
recursion over all bit strings of `clock (2 clock + 1)` bits, decoded slotwise, computes the value
of `G_{e,x}`. -/
theorem valKC_slots_gameOf (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString)
    (x : BitString) (hsa : SubAdaptiveOn c e x) :
    valKC (allBits (clock e x.length * (2 * clock e x.length + 1)))
        (decK (clock e x.length) (clock e x.length))
        (querySet c.toOTM x (clock e x.length) \ Y)
        (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
        (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)).outcome
        (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
        (2 ^ (gameN e T m x.length - m)) (2 ^ (clock e x.length + 1)) =
      val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)) := by
  rw [valKC_eq _ _ _ (cover_gameOf c e x T.fn _)]
  exact valKRaw_gameOf_of_subAdaptive_clock c e T m Y x hsa

end Kolmogorov.RandomStrings
