/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Converse
import KolmogorovMathlib.MonotoneComplexity.BinaryInterval

/-!
# SUV Problem 143: randomness from a decidable set of lengths

> Let `A` be a decidable infinite set of natural numbers (lengths), and let `ω` be some
> sequence.  If `K(x) ⩾ −log μ(Ω_x) − c` for some `c` and for every prefix `x` of `ω` with
> length in `A`, then `ω` is random.
>
> (Hint: In the proofs of Theorems 90 and 92, we can split the intervals into parts to get
> the desired length.)  — SUV p. 149

This module carries out the hint.  Everything in `LevinSchnorr/Converse.lean` is reused
verbatim; the only change is that the enumeration of the universal Martin-Löf test's cover is
replaced by the enumeration of *all extensions of its intervals to the next length in `A`*.
That leaves the union of the cover unchanged (`union_extensions`) and therefore leaves the
Kraft–Chaitin request weights unchanged, while forcing every requested string to have its
length in `A`.

## Main results

* `nextLen` — the least element of `A` strictly above `k`, and its computability;
* `extendEnum` — the extension transform on enumerations of cylinders;
* `exists_prefix_mem_two_pow_mul_cantorMass_lt_complexityWeight_KPPlain` — the `A`-refined
  form of the converse half of Theorem 92;
* `isMartinLofRandom_of_boundedPrefixDeficiency_mem` — Problem 143.
-/

namespace Kolmogorov

open MeasureTheory Set

open scoped ENNReal

/-! ### The next length in `A` -/

section NextLen

variable {A : Set ℕ}

/-- An infinite set of naturals has elements above every bound. -/
lemma exists_gt_mem (hAinf : A.Infinite) (k : ℕ) : ∃ n, k < n ∧ n ∈ A := by
  obtain ⟨n, hn, hlt⟩ := hAinf.exists_gt k
  exact ⟨n, hlt, hn⟩

open Classical in
/-- The least element of `A` strictly above `k`. -/
noncomputable def nextLen (hAinf : A.Infinite) (k : ℕ) : ℕ :=
  Nat.find (exists_gt_mem hAinf k)

open Classical in
/-- The next admissible length after `k` is strictly above `k`. -/
lemma lt_nextLen (hAinf : A.Infinite) (k : ℕ) : k < nextLen hAinf k :=
  (Nat.find_spec (exists_gt_mem hAinf k)).1

open Classical in
/-- The next admissible length is admissible. -/
lemma nextLen_mem (hAinf : A.Infinite) (k : ℕ) : nextLen hAinf k ∈ A :=
  (Nat.find_spec (exists_gt_mem hAinf k)).2

open Classical in
/-- Nothing admissible lies strictly between `k` and the next admissible length. -/
lemma not_lt_and_mem_of_lt_nextLen (hAinf : A.Infinite) {k m : ℕ}
    (hm : m < nextLen hAinf k) : ¬ (k < m ∧ m ∈ A) :=
  Nat.find_min _ hm

/-- The search function used to compute `nextLen` by an unbounded search. -/
def nextLenSearch (dec : ℕ → Bool) (k m : ℕ) : Option ℕ :=
  bif decide (k < m) && dec m then some m else none

/-- The bounded search for the next admissible length is computable. -/
lemma computable₂_nextLenSearch {dec : ℕ → Bool} (hdec : Computable dec) :
    Computable₂ (nextLenSearch dec) := by
  have hlt : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) :=
    primrec_decide_nat_lt.to_comp
  have hd : Computable (fun p : ℕ × ℕ => dec p.2) := hdec.comp Computable.snd
  have hand : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2) && dec p.2) :=
    Primrec.and.to_comp.comp hlt hd
  exact Computable.cond hand (Computable.option_some.comp Computable.snd)
    (Computable.const none)

/-- For a decidable set of admissible lengths, the next admissible length is computable. -/
lemma computable_nextLen {dec : ℕ → Bool} (hdec : Computable dec)
    (hspec : ∀ n, dec n = true ↔ n ∈ A) (hAinf : A.Infinite) :
    Computable (nextLen hAinf) := by
  refine Partrec.of_eq_tot (Partrec.rfindOpt (computable₂_nextLenSearch hdec)) fun k => ?_
  have hsome : nextLenSearch dec k (nextLen hAinf k) = some (nextLen hAinf k) := by
    have h1 : decide (k < nextLen hAinf k) = true := by simp [lt_nextLen hAinf k]
    have h2 : dec (nextLen hAinf k) = true := (hspec _).mpr (nextLen_mem hAinf k)
    simp [nextLenSearch, h1, h2]
  rw [Nat.rfindOpt]
  refine Part.mem_bind_iff.mpr ⟨nextLen hAinf k, ?_, ?_⟩
  · rw [Nat.mem_rfind]
    have hnone : ∀ m : ℕ, m < nextLen hAinf k → nextLenSearch dec k m = none := by
      intro m hm
      have hnot := not_lt_and_mem_of_lt_nextLen hAinf hm
      by_cases h1 : k < m
      · have h2 : dec m = false := by
          by_contra hcon
          exact hnot ⟨h1, (hspec m).mp (by simpa using hcon)⟩
        simp [nextLenSearch, h2]
      · simp [nextLenSearch, h1]
    refine ⟨by simp [hsome], fun {m} hm => ?_⟩
    simp [hnone m hm]
  · simp [hsome]

end NextLen

/-! ### Extending an enumeration of cylinders to `A`-lengths -/

/-- The `j`-th extension of `x` to the length `nx |x|`. -/
def extendPad (nx : ℕ → ℕ) (j : ℕ) (x : BitString) : Option BitString :=
  if j < 2 ^ (nx x.length - x.length) then
    some (x ++ (bitStringsOfLength (nx x.length - x.length)).getD j [])
  else none

/-- Replace the interval `Ω_x` enumerated by `f` at index `i` with the intervals `Ω_{x ++ t}`
for all strings `t` of the length that pads `|x|` up to `nx |x|`.  The index of the new
enumeration codes the pair `(i, j)`. -/
def extendEnum (nx : ℕ → ℕ) (f : ℕ → Option BitString) (k : ℕ) : Option BitString :=
  (f (Nat.unpair k).1).bind (extendPad nx (Nat.unpair k).2)

/-- The `j`-th string of length `m` has length `m`. -/
lemma getD_bitStringsOfLength_length {m j : ℕ} (hj : j < 2 ^ m) :
    ((bitStringsOfLength m).getD j []).length = m := by
  have hlen : j < (bitStringsOfLength m).length := by
    rw [length_bitStringsOfLength]
    exact hj
  rw [List.getD_eq_getElem _ _ hlen]
  exact length_of_mem_bitStringsOfLength (List.getElem_mem hlen)

/-- A padded extension is the `j`-th extension of `x` to the next admissible length, and exists
only for `j` below the number of such extensions. -/
lemma extendPad_eq_some {nx : ℕ → ℕ} {j : ℕ} {x u : BitString}
    (h : extendPad nx j x = some u) :
    j < 2 ^ (nx x.length - x.length) ∧
      u = x ++ (bitStringsOfLength (nx x.length - x.length)).getD j [] := by
  rw [extendPad] at h
  by_cases hc : j < 2 ^ (nx x.length - x.length)
  · rw [if_pos hc] at h
    exact ⟨hc, (Option.some_inj.mp h).symm⟩
  · rw [if_neg hc] at h
    simp at h

/-- An entry of the padded enumeration comes from an entry of the original one, extended to the
next admissible length. -/
lemma extendEnum_eq_some {nx : ℕ → ℕ} {f : ℕ → Option BitString} {k : ℕ} {u : BitString}
    (h : extendEnum nx f k = some u) :
    ∃ x : BitString, f (Nat.unpair k).1 = some x ∧
      (Nat.unpair k).2 < 2 ^ (nx x.length - x.length) ∧
      u = x ++ (bitStringsOfLength (nx x.length - x.length)).getD (Nat.unpair k).2 [] := by
  rw [extendEnum, Option.bind_eq_some_iff] at h
  obtain ⟨x, hf, hx⟩ := h
  obtain ⟨hc, hu⟩ := extendPad_eq_some hx
  exact ⟨x, hf, hc, hu⟩

/-- Every entry of the padded enumeration has an admissible length. -/
lemma length_extendEnum {nx : ℕ → ℕ} (hnx : ∀ j, j ≤ nx j) {f : ℕ → Option BitString}
    {k : ℕ} {u : BitString} (h : extendEnum nx f k = some u) :
    ∃ x : BitString, f (Nat.unpair k).1 = some x ∧ u.length = nx x.length := by
  obtain ⟨x, hf, hc, rfl⟩ := extendEnum_eq_some h
  refine ⟨x, hf, ?_⟩
  have hle := hnx x.length
  rw [List.length_append, getD_bitStringsOfLength_length hc]
  omega

/-- Every entry of the padded enumeration extends an entry of the original one. -/
lemma extendEnum_prefix {nx : ℕ → ℕ} {f : ℕ → Option BitString} {k : ℕ} {u : BitString}
    (h : extendEnum nx f k = some u) :
    ∃ x : BitString, f (Nat.unpair k).1 = some x ∧ x <+: u := by
  obtain ⟨x, hf, -, rfl⟩ := extendEnum_eq_some h
  exact ⟨x, hf, ⟨_, rfl⟩⟩

/-- Padding the enumeration does not change the set it covers. -/
lemma coverSet_extendEnum_iUnion (nx : ℕ → ℕ) (f : ℕ → Option BitString) :
    (⋃ k, coverSet (extendEnum nx f) k) = ⋃ i, coverSet f i := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun k => ?_) (Set.iUnion_subset fun i => ?_)
  · intro w hw
    cases hu : extendEnum nx f k with
    | none => rw [coverSet, hu] at hw; simp at hw
    | some u =>
      rw [coverSet, hu] at hw
      obtain ⟨x, hf, hpre⟩ := extendEnum_prefix hu
      refine Set.mem_iUnion.2 ⟨(Nat.unpair k).1, ?_⟩
      rw [coverSet, hf]
      exact cantorCylinder_subset_of_prefix hpre hw
  · intro w hw
    cases hf : f i with
    | none => rw [coverSet, hf] at hw; simp at hw
    | some x =>
      rw [coverSet, hf] at hw
      have hmem : w ∈ ⋃ (y : BitString), ⋃ (_ : y.length = nx x.length - x.length),
          cantorCylinder (x ++ y) := by
        rw [union_extensions x (nx x.length - x.length)]
        exact hw
      obtain ⟨y, hy⟩ := Set.mem_iUnion.1 hmem
      obtain ⟨hylen, hwy⟩ := Set.mem_iUnion.1 hy
      have hyin : y ∈ bitStringsOfLength (nx x.length - x.length) :=
        mem_bitStringsOfLength_iff.mpr hylen
      obtain ⟨j, hjlt, hjy⟩ := List.getElem_of_mem hyin
      have hjlt' : j < 2 ^ (nx x.length - x.length) := by
        rwa [length_bitStringsOfLength] at hjlt
      refine Set.mem_iUnion.2 ⟨Nat.pair i j, ?_⟩
      have h1 : extendEnum nx f (Nat.pair i j) = extendPad nx j x := by
        simp only [extendEnum, Nat.unpair_pair, hf, Option.bind_some]
      have hval : extendEnum nx f (Nat.pair i j) = some (x ++ y) := by
        rw [h1, extendPad, if_pos hjlt', List.getD_eq_getElem _ _ hjlt, hjy]
      rw [coverSet, hval]
      exact hwy

/-- The padded extension is computable. -/
lemma computable₂_extendPad {nx : ℕ → ℕ} (hnx : Computable nx) :
    Computable₂ fun (j : ℕ) (x : BitString) => extendPad nx j x := by
  have hsub : Computable₂ (fun u v : ℕ => u - v) := Primrec.nat_sub.to_comp
  have hlt : Computable₂ (fun u v : ℕ => decide (u < v)) := primrec_decide_nat_lt.to_comp
  have hlen : Computable (fun q : ℕ × BitString => q.2.length) :=
    Computable.list_length.comp Computable.snd
  have hm : Computable (fun q : ℕ × BitString => nx q.2.length - q.2.length) :=
    hsub.comp (hnx.comp hlen) hlen
  have hcond : Computable (fun q : ℕ × BitString =>
      decide (q.1 < 2 ^ (nx q.2.length - q.2.length))) :=
    hlt.comp Computable.fst (primrec_two_pow_aux.to_comp.comp hm)
  have hlist : Computable (fun q : ℕ × BitString =>
      bitStringsOfLength (nx q.2.length - q.2.length)) :=
    computable_bitStringsOfLength.comp hm
  have hstr : Computable (fun q : ℕ × BitString =>
      q.2 ++ (bitStringsOfLength (nx q.2.length - q.2.length)).getD q.1 []) :=
    Primrec.list_append.to_comp.comp Computable.snd
      ((Primrec.list_getD ([] : BitString)).to_comp.comp hlist Computable.fst)
  refine (Computable.cond hcond (Computable.option_some.comp hstr)
    (Computable.const none)).of_eq fun q => ?_
  by_cases h : q.1 < 2 ^ (nx q.2.length - q.2.length) <;> simp [extendPad, h]

/-- The padded enumeration of a computable enumeration is computable. -/
lemma computable₂_extendEnum {nx : ℕ → ℕ} (hnx : Computable nx)
    {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g) :
    Computable₂ fun n k => extendEnum nx (g n) k := by
  have hidx : Computable (fun p : ℕ × ℕ => (Nat.unpair p.2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hj : Computable (fun p : ℕ × ℕ => (Nat.unpair p.2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hf : Computable (fun p : ℕ × ℕ => g p.1 (Nat.unpair p.2).1) :=
    hg.comp Computable.fst hidx
  have hinner : Computable₂ (fun (p : ℕ × ℕ) (x : BitString) =>
      extendPad nx (Nat.unpair p.2).2 x) :=
    (computable₂_extendPad hnx).comp (hj.comp Computable.fst) Computable.snd
  exact Computable.option_bind hf hinner

/-! ### The maximal length of an extended enumeration lies in `A` -/

/-- A running maximum over an initial segment is either zero or attained. -/
lemma natMaxBelow_eq_zero_or_exists (len : ℕ → ℕ) (k : ℕ) :
    natMaxBelow len k = 0 ∨ ∃ j, j < k ∧ len j = natMaxBelow len k := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    have hstep : natMaxBelow len (k + 1) = max (natMaxBelow len k) (len k) := rfl
    rcases le_total (len k) (natMaxBelow len k) with h | h
    · rw [hstep, max_eq_left h]
      rcases ih with h0 | ⟨j, hj, hjv⟩
      · exact Or.inl h0
      · exact Or.inr ⟨j, by omega, hjv⟩
    · rw [hstep, max_eq_right h]
      exact Or.inr ⟨k, by omega, rfl⟩

/-- A positive recorded length comes from an actual entry of that length. -/
lemma lenOf_pos_eq {h : ℕ → Option BitString} {j : ℕ} (hpos : 0 < lenOf h j) :
    ∃ u : BitString, h j = some u ∧ u.length = lenOf h j := by
  cases hj : h j with
  | none => rw [lenOf, hj] at hpos; simp at hpos
  | some u => exact ⟨u, rfl, by rw [lenOf, hj]; rfl⟩

/-- A positive maximal length of an enumeration with admissible lengths is admissible. -/
lemma maxLen_mem {A : Set ℕ} {h : ℕ → Option BitString}
    (hlen : ∀ j u, h j = some u → u.length ∈ A) (k : ℕ) (hpos : 0 < maxLen h k) :
    maxLen h k ∈ A := by
  rcases natMaxBelow_eq_zero_or_exists (lenOf h) k with h0 | ⟨j, -, hjv⟩
  · rw [maxLen] at hpos
    omega
  · have hjpos : 0 < lenOf h j := by rw [hjv]; exact hpos
    obtain ⟨u, hu, hulen⟩ := lenOf_pos_eq hjpos
    have : u.length = maxLen h k := by rw [hulen, hjv]; rfl
    rw [← this]
    exact hlen j u hu

/-! ### The `A`-refined converse of Theorem 92 -/

/-- SUV Problem 143 (Section 5.6, p. 149), the key step: if `w` is *not* Martin-Löf random,
then for every `C` there is a prefix of `w` **whose length lies in `A`** with prefix-complexity
deficiency more than `C`.  This is
`exists_prefix_two_pow_mul_cantorMass_lt_complexityWeight_KPPlain` with the cover of the
universal test replaced by the enumeration of all its extensions to the next length in `A`. -/
theorem exists_prefix_mem_two_pow_mul_cantorMass_lt_complexityWeight_KPPlain
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) {A : Set ℕ} {dec : ℕ → Bool} (hdec : Computable dec)
    (hspec : ∀ n, dec n = true ↔ n ∈ A) (hAinf : A.Infinite) {w : CantorSeq}
    (hw : ¬ IsMartinLofRandom μ w) (C : ℕ) :
    ∃ n : ℕ, n ∈ A ∧ (2 : ℝ≥0∞) ^ C * cantorMass μ (cantorPrefix w n)
      < complexityWeight (KPPlain U (cantorPrefix w n)) := by
  classical
  obtain ⟨V, hV⟩ := exists_universal_martinLof_test hμ
  have hmem : w ∈ ⋂ n, V n := (not_isMartinLofRandom_iff_mem_universal_test hV w).1 hw
  obtain ⟨g₀, hg₀, hg₀V⟩ := hV.1.1
  set nx : ℕ → ℕ := nextLen hAinf with hnxdef
  have hnxle : ∀ j, j ≤ nx j := fun j => (lt_nextLen hAinf j).le
  have hnxpos : ∀ j, 0 < nx j := fun j => lt_of_le_of_lt (Nat.zero_le j) (lt_nextLen hAinf j)
  have hnxmem : ∀ j, nx j ∈ A := fun j => nextLen_mem hAinf j
  set g : ℕ → ℕ → Option BitString := fun n => extendEnum nx (g₀ n) with hgdef
  have hg : Computable₂ g := computable₂_extendEnum (computable_nextLen hdec hspec hAinf) hg₀
  have hgunion : ∀ n, (⋃ i, coverSet (g n) i) = ⋃ i, coverSet (g₀ n) i :=
    fun n => coverSet_extendEnum_iUnion nx (g₀ n)
  have hglen : ∀ n j u, g n j = some u → u.length ∈ A := by
    intro n j u hu
    obtain ⟨x, -, hlen⟩ := length_extendEnum hnxle hu
    rw [hlen]
    exact hnxmem _
  have hglenpos : ∀ n j u, g n j = some u → 0 < u.length := by
    intro n j u hu
    obtain ⟨x, -, hlen⟩ := length_extendEnum hnxle hu
    rw [hlen]
    exact hnxpos _
  have hsmall : ∀ n, μ (⋃ i, coverSet (g n) i) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    have hb := hV.1.2 n
    rw [dyadicValue_one_eq_inv_two_pow'] at hb
    rw [hgunion n, show (⋃ i, coverSet (g₀ n) i) = V n from (hg₀V n).symm]
    exact hb
  obtain ⟨c₀, hc₀⟩ := exists_const_two_pow_mul_cantorMass_le_complexityWeight_KPPlain
    hμ hU hg hsmall
  obtain ⟨cK, hcK⟩ := KPPlain_le_two_mul_length U hU
  set c : ℕ := C + c₀ + 1 with hc
  have hwV : w ∈ V (2 * c + 2) := Set.mem_iInter.1 hmem _
  have hveq : V (2 * c + 2) = ⋃ j, coverSet (g₀ (2 * c + 2)) j := hg₀V (2 * c + 2)
  have hcover : w ∈ ⋃ i, coverSet (disjEnum (g (2 * c + 2))) i := by
    rw [coverSet_disjEnum_iUnion, hgunion, ← hveq]
    exact hwV
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hcover
  rcases hx : disjEnum (g (2 * c + 2)) i with _ | x
  · rw [coverSet, hx] at hi
    exact absurd hi (Set.notMem_empty w)
  · rw [coverSet, hx] at hi
    have hpref : cantorPrefix w x.length = x :=
      (isCantorPrefix_iff_cantorPrefix_eq x w).1 hi
    obtain ⟨-, hbit⟩ := disjEnum_eq_some hx
    obtain ⟨hxlen, hcb, -⟩ := disjBit_spec hbit
    obtain ⟨t, hht, htu⟩ :=
      (coverBit_eq_true_iff (g (2 * c + 2)) x (Nat.unpair i).1).mp hcb
    have hposx : 0 < x.length := by
      have h1 : lenOf (g (2 * c + 2)) (Nat.unpair i).1 ≤ maxLen (g (2 * c + 2))
          ((Nat.unpair i).1 + 1) := lenOf_le_maxLen _ (Nat.lt_succ_self _)
      have h2 : lenOf (g (2 * c + 2)) (Nat.unpair i).1 = t.length := by
        rw [lenOf, hht]
        rfl
      have h3 := hglenpos (2 * c + 2) (Nat.unpair i).1 t hht
      omega
    have hxA : x.length ∈ A := by
      rw [hxlen]
      exact maxLen_mem (hglen (2 * c + 2)) _ (by omega)
    refine ⟨x.length, hxA, ?_⟩
    rw [hpref]
    have hlow := hc₀ c i x hx
    rcases eq_or_ne (cantorMass μ x) 0 with hzero | hpos
    · rw [hzero, mul_zero]
      refine (complexityWeight_pos_iff _).2 ?_
      exact ne_top_of_le_ne_top (ENat.coe_ne_top _) (hcK x)
    · have hmasstop : cantorMass μ x ≠ ⊤ := measure_ne_top μ _
      by_contra hcon
      push_neg at hcon
      have hkey : (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞) ^ c * cantorMass μ x
          ≤ (2 : ℝ≥0∞) ^ C * cantorMass μ x := by
        rw [mul_assoc]
        exact le_trans hlow hcon
      have hcancel : (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞) ^ c ≤ (2 : ℝ≥0∞) ^ C :=
        (ENNReal.mul_le_mul_iff_left hpos hmasstop).1 hkey
      have heval : (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞) ^ c = (2 : ℝ≥0∞) ^ (C + 1) := by
        rw [hc, show C + c₀ + 1 = c₀ + (C + 1) by omega, pow_add, ← mul_assoc,
          ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, one_mul]
      rw [heval] at hcancel
      have hscale : (2 : ℝ≥0∞) ^ (C + 1) * (2 : ℝ≥0∞)⁻¹ ^ C
          ≤ (2 : ℝ≥0∞) ^ C * (2 : ℝ≥0∞)⁻¹ ^ C := by gcongr
      have hL : (2 : ℝ≥0∞) ^ (C + 1) * (2 : ℝ≥0∞)⁻¹ ^ C = 2 := by
        rw [pow_succ, mul_comm ((2 : ℝ≥0∞) ^ C) 2, mul_assoc, ← mul_pow,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, mul_one]
      have hR : (2 : ℝ≥0∞) ^ C * (2 : ℝ≥0∞)⁻¹ ^ C = 1 := by
        rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
      rw [hL, hR] at hscale
      exact absurd hscale (by norm_num)

/-- **SUV Problem 143** (Section 5.6, p. 149). -/
theorem isMartinLofRandom_of_boundedPrefixDeficiency_mem {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) {A : Set ℕ} (hA : ComputablePred fun n => n ∈ A)
    (hAinf : A.Infinite) {w : CantorSeq}
    (hw : ∃ c : ℕ, ∀ n ∈ A, complexityWeight (KPPlain U (cantorPrefix w n))
      ≤ (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n)) :
    IsMartinLofRandom μ w := by
  obtain ⟨inst, hcomp⟩ := hA
  obtain ⟨c, hc⟩ := hw
  by_contra hnr
  obtain ⟨n, hn, hlt⟩ := exists_prefix_mem_two_pow_mul_cantorMass_lt_complexityWeight_KPPlain
    hμ hU hcomp (fun n => decide_eq_true_iff) hAinf hnr c
  exact absurd (hc n hn) (not_le.mpr hlt)


end Kolmogorov
