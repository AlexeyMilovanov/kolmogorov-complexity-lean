/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.Counting

/-!
# Dilution sets: subsets of `Ω` of prescribed effective Hausdorff dimension

SUV Problem 173 (§5.8, p. 175) constructs sets of every classical Hausdorff
dimension by "the set of all sequences that have zeros at specified places"; the
same sets serve the *effective* theory, and the proof of SUV Theorem 118 (the
converse half, p. 174) needs exactly such a witness: for every rational
`γ = p/q ∈ (0,1)` a set that is an effective `α`-null set for every `α > γ` and
is *not* an `α`-null set (not even classically) for any `α ≤ γ`.

This module supplies that witness and the two facts about it.  It is stated in
the raw form `uniformMeasure (cantorCylinder x) ^ α` (and not with
`intervalAlphaMass` / `IsEffectiveAlphaNull`, which are introduced in
`Dimension/Basic.lean`) so that `Dimension/Basic.lean` can import it, exactly
like `Dimension/Counting.lean`.

## Contents

* `dilCount p q n = ⌈p·n/q⌉` — the number of "free" places below `n`, and
  `dilSel p q i` — the Boolean marking the free places themselves.
* `dilate p q w` — the sequence that carries the bits of `w` on the free places
  and `false` elsewhere; `dilSet p q` is its range.
* `dilCover p q n` — the computable cover of `dilSet p q` by the `2^{⌈p n/q⌉}`
  intervals of length `n` that meet it, and `tsum_dilCover_rpow` its exact
  `α`-weight `2^{⌈p n/q⌉}·(2^{-n})^α`.
* `one_le_tsum_dilPull` — the mass-distribution bound: *any* countable family of
  intervals covering `dilSet p q` satisfies `∑ 2^{-⌈p·l(x_k)/q⌉} ≥ 1`.  The
  proof is a pull-back along `dilate`: the preimage of an interval `Ω_x` is
  contained in one interval of length `⌈p·l(x)/q⌉`, so the pulled-back family
  covers the whole Cantor space and the uniform measure is a probability
  measure.  No mass distribution and no compactness argument is needed.
-/

namespace Kolmogorov

open MeasureTheory Encodable
open scoped ENNReal

/-! ## The counting function `⌈p n / q⌉` and the free places -/

/-- `dilCount p q n = ⌈p·n/q⌉`: the number of free places among `0, …, n-1`. -/
def dilCount (p q n : ℕ) : ℕ := (p * n + (q - 1)) / q

/-- `dilSel p q i` marks the free places: the places at which `dilCount` grows. -/
def dilSel (p q i : ℕ) : Bool := decide (dilCount p q (i + 1) = dilCount p q i + 1)

/-- No position is selected before position `0`, so the dilution counter starts at `0`. -/
@[simp] lemma dilCount_zero (p q : ℕ) : dilCount p q 0 = 0 := by
  unfold dilCount
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · simp only [Nat.mul_zero, Nat.zero_add]
    exact Nat.div_eq_of_lt (by omega)

/-- Among the first `n` positions at least a `p/q` fraction is selected: `p * n ≤ q * dilCount p q
n`. -/
lemma le_dilCount (p q n : ℕ) (hq : 0 < q) : p * n ≤ q * dilCount p q n := by
  have h1 := Nat.div_add_mod (p * n + (q - 1)) q
  have h2 : (p * n + (q - 1)) % q < q := Nat.mod_lt _ hq
  change p * n ≤ q * ((p * n + (q - 1)) / q)
  generalize hX : q * ((p * n + (q - 1)) / q) = X at h1 ⊢
  generalize hR : (p * n + (q - 1)) % q = R at h1 h2
  omega

/-- The dilution counter overshoots the `p/q` fraction by less than one selected position:
`q * dilCount p q n ≤ p * n + q`. -/
lemma dilCount_mul_le (p q n : ℕ) : q * dilCount p q n ≤ p * n + q := by
  have h : (p * n + (q - 1)) / q * q ≤ p * n + (q - 1) := Nat.div_mul_le_self _ _
  have hcomm : q * ((p * n + (q - 1)) / q) = (p * n + (q - 1)) / q * q := Nat.mul_comm _ _
  change q * ((p * n + (q - 1)) / q) ≤ p * n + q
  rw [hcomm]
  omega

/-- The number of selected positions below `n` is nondecreasing in `n`. -/
lemma dilCount_mono (p q : ℕ) : Monotone (dilCount p q) := by
  intro a b hab
  exact Nat.div_le_div_right (by
    have : p * a ≤ p * b := Nat.mul_le_mul_left p hab
    omega)

/-- When `p ≤ q` one further position can add at most one selection, so the counter grows by at
most one at each step. -/
lemma dilCount_succ_le (p q n : ℕ) (hq : 0 < q) (hpq : p ≤ q) :
    dilCount p q (n + 1) ≤ dilCount p q n + 1 := by
  have hstep : p * (n + 1) + (q - 1) ≤ (p * n + (q - 1)) + q := by
    rw [Nat.mul_succ]; omega
  calc dilCount p q (n + 1) ≤ ((p * n + (q - 1)) + q) / q := Nat.div_le_div_right hstep
    _ = (p * n + (q - 1)) / q + 1 := Nat.add_div_right _ hq
    _ = dilCount p q n + 1 := rfl

/-- For `p ≤ q` the counter either stays put or increases by exactly one when `n` is incremented. -/
lemma dilCount_succ_cases (p q n : ℕ) (hq : 0 < q) (hpq : p ≤ q) :
    dilCount p q (n + 1) = dilCount p q n ∨ dilCount p q (n + 1) = dilCount p q n + 1 := by
  have h1 : dilCount p q n ≤ dilCount p q (n + 1) := dilCount_mono p q (by omega)
  have h2 := dilCount_succ_le p q n hq hpq
  omega

/-- A selected position `i < n` is counted, so it makes the counter at `i` strictly smaller than
the counter at `n`. -/
lemma dilCount_lt_of_dilSel {p q i n : ℕ} (hq : 0 < q) (hi : i < n)
    (hsel : dilSel p q i = true) : dilCount p q i < dilCount p q n := by
  have _ := hq
  have hstep : dilCount p q (i + 1) = dilCount p q i + 1 := of_decide_eq_true hsel
  have hmono : dilCount p q (i + 1) ≤ dilCount p q n := dilCount_mono p q hi
  omega

/-- Every index below `dilCount p q n` is `dilCount p q i` for a unique free
place `i < n`.  This is the combinatorial heart of the whole module. -/
lemma exists_dilSel_dilCount_eq (p q : ℕ) (hq : 0 < q) (hpq : p ≤ q) :
    ∀ n j : ℕ, j < dilCount p q n → ∃ i, i < n ∧ dilSel p q i = true ∧ dilCount p q i = j := by
  intro n
  induction n with
  | zero => intro j hj; simp at hj
  | succ n ih =>
      intro j hj
      rcases dilCount_succ_cases p q n hq hpq with heq | heq
      · obtain ⟨i, hi, hsel, hval⟩ := ih j (by omega)
        exact ⟨i, by omega, hsel, hval⟩
      · have hseln : dilSel p q n = true := decide_eq_true heq
        by_cases hjlt : j < dilCount p q n
        · obtain ⟨i, hi, hsel, hval⟩ := ih j hjlt
          exact ⟨i, by omega, hsel, hval⟩
        · have : j = dilCount p q n := by omega
          exact ⟨n, Nat.lt_succ_self n, hseln, this.symm⟩

/-! ## The dilution map and the dilution set -/

/-- The sequence carrying the bits of `w` on the free places, `false` elsewhere. -/
def dilate (p q : ℕ) (w : CantorSeq) : CantorSeq :=
  fun i => if dilSel p q i then w (dilCount p q i) else false

/-- The finite version of `dilate`: expand a payload `y` into a string of
length `n`. -/
def dilExpand (p q n : ℕ) (y : BitString) : BitString :=
  (List.range n).map (fun i => if dilSel p q i then y.getD (dilCount p q i) false else false)

/-- **SUV Problem 173 (§5.8, p. 175)**, effective form: the set of sequences
carrying zeros outside the free places of density `p/q`. -/
def dilSet (p q : ℕ) : Set CantorSeq := Set.range (dilate p q)

/-- Expanding a source block to the first `n` positions produces a string of length exactly `n`. -/
@[simp] lemma dilExpand_length (p q n : ℕ) (y : BitString) :
    (dilExpand p q n y).length = n := by
  simp [dilExpand]

/-- Reading position `j < m` of the length-`m` prefix of `w` returns the bit `w j`. -/
lemma getD_cantorPrefix {w : CantorSeq} {m j : ℕ} (hj : j < m) :
    (cantorPrefix w m).getD j false = w j := by
  have hlen : j < (cantorPrefix w m).length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hlen]
  simp [cantorPrefix]

/-- The length-`n` prefix of the dilution of `w` is obtained by expanding the prefix of `w` of
length `dilCount p q n`: the diluted sequence carries no information beyond that many source bits.
-/
lemma cantorPrefix_dilate (p q : ℕ) (hq : 0 < q) (w : CantorSeq) (n : ℕ) :
    cantorPrefix (dilate p q w) n = dilExpand p q n (cantorPrefix w (dilCount p q n)) := by
  refine List.ext_getElem (by simp [dilExpand]) (fun i h1 h2 => ?_)
  have hin : i < n := by simpa using h1
  have hL : (cantorPrefix (dilate p q w) n)[i]'h1 = dilate p q w i := by
    simp [cantorPrefix]
  have hR : (dilExpand p q n (cantorPrefix w (dilCount p q n)))[i]'h2 =
      (if dilSel p q i then
        (cantorPrefix w (dilCount p q n)).getD (dilCount p q i) false else false) := by
    simp [dilExpand]
  rw [hL, hR, dilate]
  by_cases hsel : dilSel p q i = true
  · rw [if_pos hsel, if_pos hsel,
      getD_cantorPrefix (dilCount_lt_of_dilSel hq hin hsel)]
  · simp only [Bool.not_eq_true] at hsel
    rw [if_neg (by simp [hsel]), if_neg (by simp [hsel])]

/-! ## The computable cover of the dilution set -/

/-- The cover of `dilSet p q` at length `n`: all the `2^{⌈p n/q⌉}` strings of
length `n` that meet the set, obtained by expanding the payloads. -/
def dilCover (p q n k : ℕ) : Option BitString :=
  (levelEnum (dilCount p q n) k).map (dilExpand p q n)

/-- The dilution counter is primitive recursive. -/
lemma primrec_dilCount (p q : ℕ) : Primrec (dilCount p q) :=
  Primrec.nat_div.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const p) Primrec.id) (Primrec.const (q - 1)))
    (Primrec.const q)

/-- The dilution counter is computable. -/
lemma computable_dilCount (p q : ℕ) : Computable (dilCount p q) :=
  (primrec_dilCount p q).to_comp

/-- `dilCount` is computable jointly in all three arguments. -/
lemma computable_dilCount₃ : Computable (fun t : (ℕ × ℕ) × ℕ => dilCount t.1.1 t.1.2 t.2) :=
  (Primrec.nat_div.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)))
    (Primrec.snd.comp Primrec.fst)).to_comp

/-- The predicate deciding whether a position carries a source bit is primitive recursive. -/
lemma primrec_dilSel (p q : ℕ) : Primrec (dilSel p q) := by
  have h1 : Primrec (fun i : ℕ => dilCount p q (i + 1)) :=
    (primrec_dilCount p q).comp (Primrec.succ)
  have h2 : Primrec (fun i : ℕ => dilCount p q i + 1) :=
    Primrec.succ.comp (primrec_dilCount p q)
  exact (PrimrecRel.comp Primrec.eq h1 h2).decide

/-- Expanding a source string into the first `n` positions is computable in the pair
`(n, source string)`. -/
lemma computable₂_dilExpand (p q : ℕ) :
    Computable₂ (fun n (y : BitString) => dilExpand p q n y) := by
  have hrange : Primrec (fun a : ℕ × BitString => List.range a.1) :=
    Primrec.list_range.comp Primrec.fst
  have hsel : Primrec (fun r : (ℕ × BitString) × ℕ => dilSel p q r.2) :=
    (primrec_dilSel p q).comp Primrec.snd
  have hget : Primrec (fun r : (ℕ × BitString) × ℕ =>
      r.1.2.getD (dilCount p q r.2) false) :=
    (Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst)
      ((primrec_dilCount p q).comp Primrec.snd)
  have hbody : Primrec₂ (fun (a : ℕ × BitString) (i : ℕ) =>
      if dilSel p q i then a.2.getD (dilCount p q i) false else false) := by
    refine (Primrec.cond hsel hget (Primrec.const false)).of_eq (fun r => ?_)
    by_cases h : dilSel p q r.2 = true <;> simp [h]
  exact ((Primrec.list_map hrange hbody).to_comp).to₂

/-- The enumeration of the covering strings at level `n` is computable in the level and the index.
-/
lemma computable₂_dilCover (p q : ℕ) : Computable₂ (dilCover p q) := by
  have hlev : Computable (fun a : ℕ × ℕ => levelEnum (dilCount p q a.1) a.2) :=
    computable₂_levelEnum.comp ((computable_dilCount p q).comp Computable.fst) Computable.snd
  have hmap : Computable₂ (fun (a : ℕ × ℕ) (y : BitString) => dilExpand p q a.1 y) :=
    (computable₂_dilExpand p q).comp (Computable.fst.comp Computable.fst)
      Computable.snd |>.to₂
  exact (Computable.option_map hlev hmap).to₂

/-- At every level `n` the cylinders enumerated by `dilCover p q n` cover the set of `p/q`-diluted
sequences. -/
lemma subset_iUnion_dilCover (p q : ℕ) (hq : 0 < q) (n : ℕ) :
    dilSet p q ⊆ ⋃ k, (dilCover p q n k).elim ∅ cantorCylinder := by
  rintro _ ⟨w, rfl⟩
  refine Set.mem_iUnion.2 ⟨encode (cantorPrefix w (dilCount p q n)), ?_⟩
  rw [dilCover, levelEnum_encode (cantorPrefix_length w (dilCount p q n))]
  simp only [Option.map_some, Option.elim_some]
  rw [← cantorPrefix_dilate p q hq w n]
  exact mem_cantorCylinder_cantorPrefix _ n

/-- The codes of the strings of length `L`, as in `Dimension/Counting.lean`. -/
private def dilCodes (L : ℕ) : Finset ℕ := (levelFinset L).image encode

private lemma card_dilCodes (L : ℕ) : (dilCodes L).card = 2 ^ L := by
  rw [dilCodes, Finset.card_image_of_injective _ encode_injective, card_levelFinset]

private lemma mem_dilCodes_of_levelEnum {L k : ℕ} {x : BitString}
    (h : levelEnum L k = some x) : k ∈ dilCodes L := by
  obtain ⟨hlen, hcode⟩ := levelEnum_eq_some_iff.1 h
  exact Finset.mem_image.2 ⟨x, mem_levelFinset.2 hlen, hcode⟩

/-- The exact `α`-weight of the cover at length `n`: `2^{⌈p n/q⌉}·(2^{-n})^α`. -/
theorem tsum_dilCover_rpow (p q : ℕ) (α : ℝ) (n : ℕ) :
    (∑' k, (dilCover p q n k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α))
      = (2 : ℝ≥0∞) ^ (dilCount p q n) * ((2 : ℝ≥0∞)⁻¹ ^ n) ^ α := by
  have hzero : ∀ k ∉ dilCodes (dilCount p q n),
      (dilCover p q n k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α) = 0 := by
    intro k hk
    cases h : levelEnum (dilCount p q n) k with
    | none => rw [dilCover, h]; rfl
    | some x => exact absurd (mem_dilCodes_of_levelEnum h) hk
  have hval : ∀ k ∈ dilCodes (dilCount p q n),
      (dilCover p q n k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α)
        = ((2 : ℝ≥0∞)⁻¹ ^ n) ^ α := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    have hlen : x.length = dilCount p q n := mem_levelFinset.1 hx
    rw [dilCover, levelEnum_encode hlen]
    simp only [Option.map_some, Option.elim_some]
    rw [uniformMeasure_cantorCylinder, dilExpand_length]
  rw [tsum_eq_sum hzero, Finset.sum_congr rfl hval, Finset.sum_const, card_dilCodes,
    nsmul_eq_mul]
  norm_cast

/-! ## The pull-back bound: every cover of the dilution set is heavy -/

open Classical in
/-- A witness prefix for the preimage of `Ω_x` under `dilate p q`. -/
private noncomputable def dilWitness (p q : ℕ) (x : BitString) : BitString :=
  if h : ∃ v : CantorSeq, IsCantorPrefix x (dilate p q v) then
    cantorPrefix h.choose (dilCount p q x.length)
  else List.replicate (dilCount p q x.length) false

private lemma dilWitness_length (p q : ℕ) (x : BitString) :
    (dilWitness p q x).length = dilCount p q x.length := by
  classical
  unfold dilWitness
  by_cases h : ∃ v : CantorSeq, IsCantorPrefix x (dilate p q v)
  · rw [dif_pos h]; simp
  · rw [dif_neg h]; simp

private lemma mem_cantorCylinder_dilWitness (p q : ℕ) (hq : 0 < q) (hpq : p ≤ q)
    {x : BitString} {v : CantorSeq} (hv : IsCantorPrefix x (dilate p q v)) :
    v ∈ cantorCylinder (dilWitness p q x) := by
  classical
  have hex : ∃ u : CantorSeq, IsCantorPrefix x (dilate p q u) := ⟨v, hv⟩
  have hw := hex.choose_spec
  unfold dilWitness
  rw [dif_pos hex]
  intro j hj
  have hjlt : j < dilCount p q x.length := by simpa using hj
  obtain ⟨i, hi, hsel, hval⟩ := exists_dilSel_dilCount_eq p q hq hpq x.length j hjlt
  have h1 : dilate p q v i = x[i]'hi := hv i hi
  have h2 : dilate p q hex.choose i = x[i]'hi := hw i hi
  have h3 : v (dilCount p q i) = hex.choose (dilCount p q i) := by
    have e1 : dilate p q v i = v (dilCount p q i) := by simp [dilate, hsel]
    have e2 : dilate p q hex.choose i = hex.choose (dilCount p q i) := by simp [dilate, hsel]
    rw [← e1, ← e2, h1, h2]
  rw [hval] at h3
  rw [h3]
  simp [cantorPrefix]

/-- **The mass-distribution bound for the dilution set.**  Any countable family
of intervals covering `dilSet p q` has `∑ 2^{-⌈p·l(x_k)/q⌉} ≥ 1`.

The proof pulls the family back along `dilate p q`: the preimage of `Ω_x` sits
inside a single interval of length `⌈p·l(x)/q⌉`, so the pulled-back family
covers the whole Cantor space, whose uniform measure is `1`. -/
theorem one_le_tsum_dilPull (p q : ℕ) (hq : 0 < q) (hpq : p ≤ q)
    (I : ℕ → Option BitString) (hI : dilSet p q ⊆ ⋃ k, (I k).elim ∅ cantorCylinder) :
    (1 : ℝ≥0∞) ≤ ∑' k, (I k).elim 0 (fun x => (2 : ℝ≥0∞)⁻¹ ^ (dilCount p q x.length)) := by
  set J : ℕ → Set CantorSeq :=
    fun k => (I k).elim ∅ (fun x => cantorCylinder (dilWitness p q x)) with hJ
  have hcover : (Set.univ : Set CantorSeq) ⊆ ⋃ k, J k := by
    intro v _
    have hmem : dilate p q v ∈ dilSet p q := ⟨v, rfl⟩
    obtain ⟨k, hS⟩ := Set.mem_iUnion.1 (hI hmem)
    cases hIk : I k with
    | none => rw [hIk] at hS; simp at hS
    | some x =>
        rw [hIk] at hS
        simp only [Option.elim_some] at hS
        exact Set.mem_iUnion.2 ⟨k, by
          simp only [hJ, hIk, Option.elim_some]
          exact mem_cantorCylinder_dilWitness p q hq hpq hS⟩
  have h1 : (1 : ℝ≥0∞) = uniformMeasure (Set.univ : Set CantorSeq) := by
    rw [measure_univ]
  have h2 : uniformMeasure (Set.univ : Set CantorSeq) ≤ uniformMeasure (⋃ k, J k) :=
    measure_mono hcover
  have h3 : uniformMeasure (⋃ k, J k) ≤ ∑' k, uniformMeasure (J k) := measure_iUnion_le J
  have h4 : ∀ k, uniformMeasure (J k)
      = (I k).elim 0 (fun x => (2 : ℝ≥0∞)⁻¹ ^ (dilCount p q x.length)) := by
    intro k
    cases hIk : I k with
    | none => simp [hJ, hIk]
    | some x =>
        simp only [hJ, hIk, Option.elim_some]
        rw [uniformMeasure_cantorCylinder, dilWitness_length]
  calc (1 : ℝ≥0∞) = uniformMeasure (Set.univ : Set CantorSeq) := h1
    _ ≤ uniformMeasure (⋃ k, J k) := h2
    _ ≤ ∑' k, uniformMeasure (J k) := h3
    _ = ∑' k, (I k).elim 0 (fun x => (2 : ℝ≥0∞)⁻¹ ^ (dilCount p q x.length)) := by
        exact tsum_congr h4

end Kolmogorov
