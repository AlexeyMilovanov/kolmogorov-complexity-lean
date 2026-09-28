import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import KolmogorovMathlib.AlgorithmicRandomness.Cylinders
import KolmogorovMathlib.Prefix.Encoding
import KolmogorovMathlib.Prefix.Basic
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# Binary words, prefix order, cylinders and fixed-length codes

Foundations of the stopping-complexity development (blueprint part 01, section F1). Words are
the repository's `BitString = List Bool` with Mathlib's prefix relation `<+:`. This module
adds the comparability predicates `IsComparable` and `IsIncomparable` (F1-DEF), the elementary
prefix facts F1.1–F1.4, the missing converses of the cylinder lemmas of `Cylinders.lean`
(F1.6a, F1.6b), finite additivity of the uniform measure over a prefix-free list (F1.6c), and
the fixed-length big-endian code `bitsOfNatBE` / `natOfBits` with the zero padding `padZeros`
(F1-CODE) used by the finite cell/cylinder correspondence and by the word game.

Item F1.5 (the cylinder of `p` has uniform measure `2^{-|p|}`) is the repository lemma
`cantorMass_uniformMeasure`, stated about `cantorMass uniformMeasure p`, which unfolds to
`uniformMeasure (cantorCylinder p)`; it is reused verbatim and not restated here.

Blueprint 01 F1 (items 1–6, last paragraph) and F1-CODE.
-/

open scoped ENNReal

namespace Kolmogorov

/-! ### Comparability -/

/-- Two words are *comparable* when one is a prefix of the other (`u ≤p v ∨ v ≤p u`).
Blueprint 01 F1-DEF. -/
def IsComparable (u v : BitString) : Prop := u <+: v ∨ v <+: u

/-- Two words are *incomparable* (`u ‖ v`) when neither is a prefix of the other.
Blueprint 01 F1-DEF. -/
def IsIncomparable (u v : BitString) : Prop := ¬ u <+: v ∧ ¬ v <+: u

/-- Comparability of two words is decidable (the prefix relation on lists is decidable).
Blueprint 01 F1-DEF. -/
instance instDecidableIsComparable (u v : BitString) : Decidable (IsComparable u v) := by
  unfold IsComparable; infer_instance

/-- Incomparability of two words is decidable. Blueprint 01 F1-DEF. -/
instance instDecidableIsIncomparable (u v : BitString) : Decidable (IsIncomparable u v) := by
  unfold IsIncomparable; infer_instance

/-- Incomparability is symmetric. Blueprint 01 F1-DEF. -/
theorem isIncomparable_comm (u v : BitString) : IsIncomparable u v ↔ IsIncomparable v u := by
  unfold IsIncomparable
  exact and_comm

/-- Two words are not incomparable exactly when they are comparable. Blueprint 01 F1-DEF. -/
theorem not_isIncomparable_iff_isComparable (u v : BitString) :
    ¬ IsIncomparable u v ↔ IsComparable u v := by
  unfold IsIncomparable IsComparable
  rw [not_and_or, not_not, not_not]

/-- Incomparable words are distinct. Blueprint 01 F1-DEF. -/
theorem IsIncomparable.ne {u v : BitString} (h : IsIncomparable u v) : u ≠ v := by
  rintro rfl
  exact h.1 List.prefix_rfl

/-- Extending an incomparable word keeps it incomparable with the other word: if `u ‖ v` and
`u ≤p u'` then `u' ‖ v`. Blueprint 01 F1 (item 1, chains of prefixes). -/
theorem IsIncomparable.of_prefix_left {u v u' : BitString} (h : IsIncomparable u v)
    (hu : u <+: u') : IsIncomparable u' v := by
  refine ⟨fun h' => h.1 (hu.trans h'), fun h' => ?_⟩
  rcases List.prefix_or_prefix_of_prefix hu h' with h'' | h''
  · exact h.1 h''
  · exact h.2 h''

/-- The prefixes of one word form a chain: two prefixes of `w` are comparable.
Blueprint 01 F1.1. -/
theorem isComparable_of_prefix_of_prefix {u v w : BitString} (hu : u <+: w) (hv : v <+: w) :
    IsComparable u v := by
  exact List.prefix_or_prefix_of_prefix hu hv

/-- Appending a fixed prefix `u` preserves and reflects incomparability:
`u ++ v ‖ u ++ w ↔ v ‖ w` (the prefix half is Mathlib's `List.prefix_append_right_inj`).
Blueprint 01 F1.2. -/
theorem isIncomparable_append_left_iff (u v w : BitString) :
    IsIncomparable (u ++ v) (u ++ w) ↔ IsIncomparable v w := by
  simp only [IsIncomparable, List.prefix_append_right_inj]

/-- The subtrees below `u0` and `u1` are disjoint in the prefix order: a word extending
`u ++ [false]` is incomparable with a word extending `u ++ [true]`. Blueprint 01 F1.3. -/
theorem isIncomparable_of_zero_one_subtrees {u v w : BitString}
    (hv : u ++ [false] <+: v) (hw : u ++ [true] <+: w) : IsIncomparable v w := by
  have hroot : IsIncomparable (u ++ [false]) (u ++ [true]) :=
    (isIncomparable_append_left_iff u [false] [true]).2 (by decide)
  have hv' := (isIncomparable_comm _ _).1 (hroot.of_prefix_left hv)
  exact (isIncomparable_comm _ _).1 (hv'.of_prefix_left hw)

/-! ### Cylinders -/

/-- Every finite word has an infinite extension (witness: `prependCantor u (fun _ => false)`).
Blueprint 01 F1.4. -/
theorem exists_isCantorPrefix (u : BitString) : ∃ w : CantorSeq, IsCantorPrefix u w := by
  exact ⟨prependCantor u fun _ => false, isCantorPrefix_prepend u _⟩

/-- Disjoint cylinders have incomparable words: the converse of
`cantorCylinder_disjoint_of_incompatible`. Blueprint 01 F1.6 (item 6a). -/
theorem isIncomparable_of_disjoint_cantorCylinder {u v : BitString}
    (h : Disjoint (cantorCylinder u) (cantorCylinder v)) : IsIncomparable u v := by
  constructor
  · intro huv
    obtain ⟨w, hw⟩ := exists_isCantorPrefix v
    exact Set.disjoint_left.1 h (cantorCylinder_subset_of_prefix huv hw) hw
  · intro hvu
    obtain ⟨w, hw⟩ := exists_isCantorPrefix u
    exact Set.disjoint_left.1 h hw (cantorCylinder_subset_of_prefix hvu hw)

/-- Two cylinders are disjoint exactly when their words are incomparable.
Blueprint 01 F1.6 (item 6a). -/
theorem disjoint_cantorCylinder_iff (u v : BitString) :
    Disjoint (cantorCylinder u) (cantorCylinder v) ↔ IsIncomparable u v := by
  exact ⟨isIncomparable_of_disjoint_cantorCylinder,
    fun h => cantorCylinder_disjoint_of_incompatible h.1 h.2⟩

/-- Cylinder containment forces the prefix relation: the converse of
`cantorCylinder_subset_of_prefix`. Blueprint 01 F1.6 (item 6b). -/
theorem prefix_of_cantorCylinder_subset {u v : BitString}
    (h : cantorCylinder v ⊆ cantorCylinder u) : u <+: v := by
  -- the stream that follows `v` and then disagrees with `u` at position `|v|`
  have hvw := isCantorPrefix_prepend v fun i => !(u.getD (v.length + i) false)
  have huw : IsCantorPrefix u _ := h hvw
  have hlen : u.length ≤ v.length := by
    by_contra hlt
    push_neg at hlt
    have h1 := huw v.length hlt
    simp [prependCantor, List.getElem?_eq_getElem hlt] at h1
  have hmono := cantorPrefix_mono (prependCantor v fun i => !(u.getD (v.length + i) false)) hlen
  rwa [(isCantorPrefix_iff_cantorPrefix_eq _ _).1 huw,
    (isCantorPrefix_iff_cantorPrefix_eq _ _).1 hvw] at hmono

/-- The cylinder of `v` lies inside the cylinder of `u` exactly when `u` is a prefix of `v`.
Blueprint 01 F1.6 (item 6b). -/
theorem cantorCylinder_subset_iff (u v : BitString) :
    cantorCylinder v ⊆ cantorCylinder u ↔ u <+: v := by
  exact ⟨prefix_of_cantorCylinder_subset, cantorCylinder_subset_of_prefix⟩

/-- Finite additivity over a prefix-free list: for pairwise incomparable words the uniform
measure of the union of their cylinders is the sum of the weights `2^{-|p|}`.
Blueprint 01 F1.6 (item 6c, last sentence of the proof of item 6). -/
theorem uniformMeasure_biUnion_cantorCylinder {L : List BitString}
    (hL : L.Pairwise IsIncomparable) :
    uniformMeasure (⋃ p ∈ L, cantorCylinder p) =
      (L.map fun p => (2 : ℝ≥0∞)⁻¹ ^ p.length).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.pairwise_cons] at hL
    have hmeas : MeasurableSet (⋃ q ∈ L, cantorCylinder q) :=
      MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => measurableSet_cantorCylinder q
    have hdisj : Disjoint (cantorCylinder p) (⋃ q ∈ L, cantorCylinder q) :=
      Set.disjoint_iUnion_right.2 fun q => Set.disjoint_iUnion_right.2 fun hq =>
        cantorCylinder_disjoint_of_incompatible (hL.1 q hq).1 (hL.1 q hq).2
    simp only [List.mem_cons, Set.iUnion_iUnion_eq_or_left, List.map_cons, List.sum_cons]
    rw [MeasureTheory.measure_union hdisj hmeas, ih hL.2]
    congr 1
    exact cantorMass_uniformMeasure p

/-! ### Fixed-length binary codes and zero padding -/

/-- Big-endian binary code of `n` in exactly `len` bits (`n` is taken modulo `2 ^ len`).
Blueprint 01 F1-CODE. -/
def bitsOfNatBE (len n : ℕ) : BitString :=
  (List.range len).map fun i => decide (n / 2 ^ (len - 1 - i) % 2 = 1)

/-- The value of a big-endian bit string. Blueprint 01 F1-CODE. -/
def natOfBits : BitString → ℕ
  | [] => 0
  | b :: t => (if b then 1 else 0) * 2 ^ t.length + natOfBits t

/-- The code of `n` in `len` bits has length `len`. Blueprint 01 F1-CODE. -/
@[simp] theorem length_bitsOfNatBE (len n : ℕ) : (bitsOfNatBE len n).length = len := by
  simp [bitsOfNatBE]

/-- The value of a word of length `k` is below `2 ^ k`. Blueprint 01 F1-CODE. -/
theorem natOfBits_lt (w : BitString) : natOfBits w < 2 ^ w.length := by
  induction w with
  | nil => simp [natOfBits]
  | cons b t ih =>
    rw [natOfBits, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- The code in `len + 1` bits is the bit of weight `2 ^ len` followed by the code in `len`
bits. -/
private theorem bitsOfNatBE_succ (len n : ℕ) :
    bitsOfNatBE (len + 1) n = decide (n / 2 ^ len % 2 = 1) :: bitsOfNatBE len n := by
  simp only [bitsOfNatBE, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ _ (by simp) (List.map_congr_left fun i hi => ?_)
  rw [List.mem_range] at hi
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show len + 1 - 1 - (i + 1) = len - 1 - i by omega]

/-- The `len`-bit code sees `n` only modulo `2 ^ len`: its bits are the binary digits of `n`
of weight below `2 ^ len`. -/
private theorem bitsOfNatBE_mod (len n : ℕ) :
    bitsOfNatBE len (n % 2 ^ len) = bitsOfNatBE len n := by
  unfold bitsOfNatBE
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [← Nat.testBit_eq_decide_div_mod_eq, ← Nat.testBit_eq_decide_div_mod_eq,
    Nat.testBit_mod_two_pow]
  simp [show len - 1 - i < len by omega]

/-- Decoding the `len`-bit code of `n` returns `n` modulo `2 ^ len`. -/
private theorem natOfBits_bitsOfNatBE_eq_mod (len n : ℕ) :
    natOfBits (bitsOfNatBE len n) = n % 2 ^ len := by
  induction len with
  | zero => simp [bitsOfNatBE, natOfBits, Nat.mod_one]
  | succ len ih =>
    rw [bitsOfNatBE_succ, natOfBits, ih, length_bitsOfNatBE, pow_succ, Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ len) with h | h
    · simp [h]
    · simp [h]
      ring

/-- Decoding the `len`-bit code of `n < 2 ^ len` returns `n`. Blueprint 01 F1-CODE. -/
theorem natOfBits_bitsOfNatBE {len n : ℕ} (h : n < 2 ^ len) :
    natOfBits (bitsOfNatBE len n) = n := by
  rw [natOfBits_bitsOfNatBE_eq_mod, Nat.mod_eq_of_lt h]

/-- Encoding the value of a word in its own length returns the word.
Blueprint 01 F1-CODE. -/
theorem bitsOfNatBE_natOfBits (w : BitString) : bitsOfNatBE w.length (natOfBits w) = w := by
  induction w with
  | nil => rfl
  | cons b t ih =>
    have hlt := natOfBits_lt t
    have hN : natOfBits (b :: t) = natOfBits t + (if b then 1 else 0) * 2 ^ t.length := by
      rw [natOfBits, add_comm]
    rw [List.length_cons, bitsOfNatBE_succ, ← bitsOfNatBE_mod t.length, hN,
      Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right,
      Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, ih]
    cases b <;> rfl

/-- Horner's rule for the big-endian value: folding `acc ↦ 2 * acc + b` over `w` from the
accumulator `a` gives `a * 2 ^ |w| + natOfBits w`. -/
private theorem foldl_horner_eq (w : BitString) (a : ℕ) :
    w.foldl (fun acc b => 2 * acc + if b then 1 else 0) a = a * 2 ^ w.length + natOfBits w := by
  induction w generalizing a with
  | nil => simp [natOfBits]
  | cons b t ih =>
    rw [List.foldl_cons, ih, natOfBits, List.length_cons, pow_succ]
    ring

/-- The fixed-length code is primitive recursive in `(len, n)`. Blueprint 01 F1-CODE. -/
theorem primrec_bitsOfNatBE : Primrec₂ bitsOfNatBE := by
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec.nat_iff.mpr Nat.Primrec.pow
  -- the bit of weight `2 ^ (len - 1 - i)` of `n`, as a function of `((len, n), i)`
  have hbit : Primrec₂ fun (p : ℕ × ℕ) (i : ℕ) => decide (p.2 / 2 ^ (p.1 - 1 - i) % 2 = 1) :=
    (Primrec.eq.decide.comp
      (Primrec.nat_mod.comp
        (Primrec.nat_div.comp (Primrec.snd.comp Primrec.fst)
          (hpow.comp (Primrec.const 2)
            (Primrec.nat_sub.comp
              (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1))
              Primrec.snd)))
        (Primrec.const 2))
      (Primrec.const 1)).to₂
  exact Primrec₂.mk
    ((Primrec.list_map (Primrec.list_range.comp Primrec.fst) hbit).of_eq fun p => rfl)

/-- The value of a bit string is primitive recursive. Blueprint 01 F1-CODE. -/
theorem primrec_natOfBits : Primrec natOfBits := by
  have h := Primrec.list_foldl (f := fun w : BitString => w) (g := fun _ => 0)
    (h := fun (_ : BitString) (p : ℕ × Bool) => 2 * p.1 + if p.2 then 1 else 0)
    Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd))
      ((Primrec.dom_bool fun b => if b then 1 else 0).comp (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun w => by simpa using foldl_horner_eq w 0

/-- Pad a word with trailing zeros to length `len` (a no-op when `len ≤ |p|`).
Blueprint 01 F1-CODE. -/
def padZeros (len : ℕ) (p : BitString) : BitString :=
  p ++ List.replicate (len - p.length) false

/-- A word is a prefix of its zero padding. Blueprint 01 F1-CODE. -/
theorem prefix_padZeros (len : ℕ) (p : BitString) : p <+: padZeros len p := by
  exact List.prefix_append p _

/-- Padding a word of length `≤ len` produces a word of length exactly `len`.
Blueprint 01 F1-CODE. -/
theorem length_padZeros {len : ℕ} {p : BitString} (h : p.length ≤ len) :
    (padZeros len p).length = len := by
  simp only [padZeros, List.length_append, List.length_replicate]
  omega

/-- Padding preserves incomparability, for two possibly *different* target lengths: the
disagreeing position of `p ‖ q` lies inside both original words. Two target lengths are
needed because the answers at two comparable vertices are padded to `depthOf n + cap` and
`depthOf n' + cap`, which differ when the exponents differ. Blueprint 01 F1-CODE
(LEM-SHADOW core). -/
theorem isIncomparable_padZeros {p q : BitString} (h : IsIncomparable p q) (len₁ len₂ : ℕ) :
    IsIncomparable (padZeros len₁ p) (padZeros len₂ q) := by
  have h₁ := (isIncomparable_comm _ _).1 (h.of_prefix_left (prefix_padZeros len₁ p))
  exact (isIncomparable_comm _ _).1 (h₁.of_prefix_left (prefix_padZeros len₂ q))

end Kolmogorov
