import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveOpenNormalForm
import KolmogorovMathlib.AlgorithmicRandomness.StrongLaw
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveLaws
import KolmogorovMathlib.Foundation.BigOperators

/-!
# Block map from uniform to Bernoulli randomness (SUV Chapter 3, Problems 83, 84)

If `x` is uniformly Martin-Löf random, replacing its two-bit blocks by a single
bit (mapping `00 ↦ 0` and `01, 10, 11 ↦ 1`) yields a sequence that is Martin-Löf
random with respect to the Bernoulli(3/4) measure. Conversely, every such
sequence can be obtained in this way from a uniform ML-random sequence.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal NNReal

/-- The 2-to-1 block map that sends 00 to 0 and the rest to 1. -/
def blockMap (x : CantorSeq) : CantorSeq := fun n => x (2 * n) || x (2 * n + 1)

/-- The bias `3/4` used for the block construction is at most one, so it is a legitimate
Bernoulli parameter. -/
lemma p34_le_one : (3 / 4 : ℝ≥0) ≤ 1 := by exact_mod_cast (by norm_num : (3 / 4 : ℝ) ≤ 1)

/-- The Bernoulli measure with parameter 3/4. -/
noncomputable def bernoulli34 : Measure CantorSeq :=
  bernoulliMeasure (3 / 4 : ℝ≥0) p34_le_one

/-- Cylinder mass under a Bernoulli measure as a product of per-bit weights
(`p` for `true`, `1 - p` for `false`), in list form.  This repackages the
existing `cantorMass_bernoulliMeasure` (a `Finset.Iio` product) as a
`List.prod`, convenient for the counting argument below. -/
lemma cantorMass_bernoulliMeasure_prod (p : NNReal) (hp : p ≤ 1) (s : BitString) :
    cantorMass (bernoulliMeasure p hp) s
      = (s.map (fun b => if b then (p : ℝ≥0∞) else 1 - p)).prod := by
  have h_range : Finset.Iio s.length = Finset.range s.length := by ext; simp
  rw [cantorMass_bernoulliMeasure]
  have hmap : s.map (fun b => if b then (p : ℝ≥0∞) else 1 - p)
      = List.ofFn (fun i : Fin s.length => if s[i] then (p : ℝ≥0∞) else 1 - p) := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2; simp
  rw [hmap, List.prod_ofFn, h_range, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  have hi : (i : ℕ) < s.length := i.isLt
  simp only [hi, dif_pos, Fin.getElem_fin]

/-- The product of a two-valued weight over a boolean list, grouped by the count
of `true` and `false` entries. -/
lemma prod_map_ite_bool (s : List Bool) (a c : ℝ≥0∞) :
    (s.map (fun b => if b then a else c)).prod = a ^ (s.count true) * c ^ (s.count false) := by
  induction s with
  | nil => simp
  | cons b s ih =>
    rw [List.map_cons, List.prod_cons, ih, List.count_cons, List.count_cons]
    cases b <;> simp <;> ring

/-- Every boolean list splits into its `true` and `false` counts. -/
lemma count_true_add_count_false (s : List Bool) :
    s.count true + s.count false = s.length := by
  induction s with
  | nil => simp
  | cons b s ih => cases b <;> simp <;> omega

/-- Closed form for the Bernoulli(3/4) cylinder mass:
`μ(Ω_s) = 3^{#true} / 2^{2|s|}`. -/
lemma cantorMass_bernoulli34_eq (s : BitString) :
    cantorMass bernoulli34 s = (3 : ℝ≥0∞) ^ s.count true / 2 ^ (2 * s.length) := by
  have hcoe : ((3 / 4 : NNReal) : ℝ≥0∞) = 3 / 4 := by
    rw [ENNReal.coe_div (by norm_num)]; norm_num
  have hsub : (1 : ℝ≥0∞) - 3 / 4 = 1 / 4 := by
    refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
    rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 3 = 4 from by norm_num,
        ENNReal.div_self (by norm_num) (by norm_num)]
  rw [bernoulli34, cantorMass_bernoulliMeasure_prod, prod_map_ite_bool, hcoe, hsub]
  have hlen : s.count true + s.count false = s.length := count_true_add_count_false s
  set ct := s.count true
  set cf := s.count false
  set n := s.length
  have h34 : (3 / 4 : ℝ≥0∞) = 3 * 4⁻¹ := by rw [div_eq_mul_inv]
  have h14 : (1 / 4 : ℝ≥0∞) = 4⁻¹ := by rw [div_eq_mul_inv, one_mul]
  rw [h34, h14, mul_pow, ← ENNReal.inv_pow, ← ENNReal.inv_pow,
      mul_assoc, ← ENNReal.mul_inv (by simp) (by simp), ← pow_add, hlen,
      ENNReal.div_eq_inv_mul, mul_comm]
  congr 1
  rw [show (2 : ℝ≥0∞) ^ (2 * n) = 4 ^ n by rw [pow_mul]; norm_num]

/-- The cast of a natural-number quotient is at most the real quotient. -/
lemma cast_div_le_ennreal (m n : ℕ) : ((m / n : ℕ) : ℝ≥0∞) ≤ (m : ℝ≥0∞) / n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hn.ne')) (Or.inl (by simp)),
        ← Nat.cast_mul]
    exact_mod_cast Nat.div_mul_le_self m n

/-- The real quotient is within one unit of the natural-number quotient. -/
lemma div_le_cast_div_add_one_ennreal (m n : ℕ) (hn : 0 < n) :
    (m : ℝ≥0∞) / n ≤ ((m / n : ℕ) : ℝ≥0∞) + 1 := by
  rw [ENNReal.div_le_iff (by exact_mod_cast hn.ne') (by simp), add_mul, one_mul, ← Nat.cast_mul]
  have hnat : m ≤ (m / n) * n + n := by
    have h1 : n * (m / n) + m % n = m := Nat.div_add_mod m n
    have h2 : m % n < n := Nat.mod_lt m hn
    have h3 : n * (m / n) = (m / n) * n := Nat.mul_comm _ _
    omega
  calc (m : ℝ≥0∞) ≤ ((m / n * n + n : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
    _ = ↑(m / n * n) + ↑n := by push_cast; ring

/-- The floor dyadic approximant `⌊P·2^s / Q⌋ / 2^s` brackets the dyadic rational
`P / Q` from below within one grid step `2^{-s}`. -/
lemma floor_dyadic_bounds (P Q s : ℕ) (hQ : 0 < Q) :
    dyadicValue ((P * 2 ^ s) / Q) s ≤ (P : ℝ≥0∞) / Q ∧
    (P : ℝ≥0∞) / Q ≤ dyadicValue ((P * 2 ^ s) / Q) s + dyadicValue 1 s := by
  have h2s0 : (2 : ℝ≥0∞) ^ s ≠ 0 := by positivity
  have h2st : (2 : ℝ≥0∞) ^ s ≠ ∞ := by finiteness
  have hPcast : ((P * 2 ^ s : ℕ) : ℝ≥0∞) = ↑P * 2 ^ s := by push_cast; ring
  have hcancel : ((P * 2 ^ s : ℕ) : ℝ≥0∞) / (↑Q * 2 ^ s) = ↑P / ↑Q := by
    rw [hPcast, ENNReal.mul_div_mul_right _ _ h2s0 h2st]
  have hassoc : ∀ A : ℝ≥0∞, A / ↑Q / 2 ^ s = A / (↑Q * 2 ^ s) := fun A => by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
        ENNReal.mul_inv (Or.inl (by exact_mod_cast hQ.ne')) (Or.inl (by simp))]
  refine ⟨?_, ?_⟩
  · unfold dyadicValue
    calc ((((P * 2 ^ s) / Q : ℕ)) : ℝ≥0∞) / 2 ^ s
        ≤ (((P * 2 ^ s : ℕ) : ℝ≥0∞) / ↑Q) / 2 ^ s := by gcongr; exact cast_div_le_ennreal _ _
      _ = ((P * 2 ^ s : ℕ) : ℝ≥0∞) / (↑Q * 2 ^ s) := hassoc _
      _ = ↑P / ↑Q := hcancel
  · unfold dyadicValue
    have hd : ((P * 2 ^ s : ℕ) : ℝ≥0∞) / ↑Q ≤ (((P * 2 ^ s) / Q : ℕ) : ℝ≥0∞) + 1 :=
      div_le_cast_div_add_one_ennreal _ _ hQ
    calc (↑P : ℝ≥0∞) / ↑Q
        = ((P * 2 ^ s : ℕ) : ℝ≥0∞) / (↑Q * 2 ^ s) := hcancel.symm
      _ = (((P * 2 ^ s : ℕ) : ℝ≥0∞) / ↑Q) / 2 ^ s := (hassoc _).symm
      _ ≤ ((((P * 2 ^ s) / Q : ℕ) : ℝ≥0∞) + 1) / 2 ^ s := by gcongr
      _ = (((P * 2 ^ s) / Q : ℕ) : ℝ≥0∞) / 2 ^ s + (1 : ℕ) / 2 ^ s := by
            rw [ENNReal.add_div]; norm_num

/-- Counting the `true` bits of a bitstring is primitive recursive. -/
lemma primrec_count_true : Primrec (fun s : BitString => s.count true) := by
  have hstep : Primrec₂ (fun (_ : BitString) (bn : Bool × ℕ) =>
      bif bn.1 then bn.2 + 1 else bn.2) :=
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have heq : (fun s : BitString => s.count true)
      = fun s => s.foldr (fun b n => bif b then n + 1 else n) 0 := by
    funext s; induction s with
    | nil => rfl
    | cons b s ih => cases b <;> simp [ih]
  rw [heq]
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep

/-- Raising a fixed base to a variable exponent is primitive recursive. -/
lemma primrec_const_pow (b : ℕ) : Primrec (fun k : ℕ => b ^ k) := by
  have heq : (fun k : ℕ => b ^ k) = fun k => Nat.rec 1 (fun _ ih => ih * b) k := by
    funext k; induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, ih]
  rw [heq]
  exact Primrec.nat_rec' Primrec.id (Primrec.const 1)
    ((Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) (Primrec.const b)).to₂)

/-- The Bernoulli(3/4) measure is computable: the floor approximant
`⌊3^{#true}·2^s / 2^{2|s|}⌋` is a uniform computable dyadic approximation of the
cylinder mass `3^{#true}/2^{2|s|}`. -/
lemma isComputableMeasure_bernoulli34 : IsComputableMeasure bernoulli34 := by
  refine isComputableMeasure_of_dyadicFloorApprox
    (a := fun x s => (3 ^ x.count true * 2 ^ s) / 2 ^ (2 * x.length)) ?_ ?_
  · have h3 : Computable (fun p : BitString × ℕ => (3 : ℕ) ^ p.1.count true) :=
      ((primrec_const_pow 3).to_comp).comp (primrec_count_true.to_comp.comp Computable.fst)
    have h2 : Computable (fun p : BitString × ℕ => (2 : ℕ) ^ p.2) :=
      ((primrec_const_pow 2).to_comp).comp Computable.snd
    have hnum : Computable (fun p : BitString × ℕ => 3 ^ p.1.count true * 2 ^ p.2) :=
      Primrec.nat_mul.to_comp.comp h3 h2
    have hden : Computable (fun p : BitString × ℕ => 2 ^ (2 * p.1.length)) :=
      ((primrec_const_pow 2).comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.list_length.comp Primrec.fst))).to_comp
    exact Primrec.nat_div.to_comp.comp hnum hden
  · intro x s
    rw [cantorMass_bernoulli34_eq]
    set ct := x.count true with hct
    set L := x.length with hL
    have hP : ((3 ^ ct : ℕ) : ℝ≥0∞) = (3 : ℝ≥0∞) ^ ct := by push_cast; ring
    have hQ : ((2 ^ (2 * L) : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (2 * L) := by push_cast; ring
    rw [← hP, ← hQ]
    exact floor_dyadic_bounds (3 ^ ct) (2 ^ (2 * L)) s (by positivity)

/-- A string's full preimage under the block map at the bitstring level. -/
def blockPreimage : BitString → List BitString
  | [] => [[]]
  | false :: s => (blockPreimage s).map (fun t => false :: false :: t)
  | true :: s =>
      (blockPreimage s).flatMap
        (fun t => [false :: true :: t, true :: false :: t, true :: true :: t])

/-- The value of `blockMap` at `0` is the disjunction of the first two bits. -/
@[simp] lemma blockMap_zero (x : CantorSeq) : blockMap x 0 = (x 0 || x 1) := by
  simp [blockMap]

/-- `blockMap` on a shifted sequence: consuming one output bit corresponds to
dropping two input bits. -/
lemma blockMap_succ (x : CantorSeq) (n : ℕ) :
    blockMap x (n + 1) = blockMap (fun j => x (j + 2)) n := by
  change (x (2 * (n + 1)) || x (2 * (n + 1) + 1)) = (x (2 * n + 2) || x (2 * n + 1 + 2))
  rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 from by omega,
      show 2 * (n + 1) = 2 * n + 2 from by omega]

/-- Peel the first coordinate off a cylinder membership. -/
lemma mem_cantorCylinder_cons (a : Bool) (rest : BitString) (x : CantorSeq) :
    x ∈ cantorCylinder (a :: rest) ↔
      x 0 = a ∧ (fun j => x (j + 1)) ∈ cantorCylinder rest := by
  simp only [cantorCylinder, Set.mem_ofPred_eq, IsCantorPrefix, List.length_cons]
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · have := h 0 (by omega); simpa using this
    · have := h (i + 1) (by omega); simpa using this
  · rintro ⟨h0, hr⟩ i hi
    match i, hi with
    | 0, _ => simpa using h0
    | i + 1, hi => have := hr i (by omega); simpa using this

/-- Peel the first two coordinates off a cylinder membership. -/
lemma mem_cantorCylinder_cons₂ (c d : Bool) (rest : BitString) (x : CantorSeq) :
    x ∈ cantorCylinder (c :: d :: rest) ↔
      x 0 = c ∧ x 1 = d ∧ (fun j => x (j + 2)) ∈ cantorCylinder rest := by
  simp only [cantorCylinder, Set.mem_ofPred_eq, IsCantorPrefix, List.length_cons]
  constructor
  · intro h
    refine ⟨?_, ?_, fun i hi => ?_⟩
    · have := h 0 (by omega); simpa using this
    · have := h 1 (by omega); simpa using this
    · have := h (i + 2) (by omega); simpa using this
  · rintro ⟨h0, h1, hr⟩ i hi
    match i, hi with
    | 0, _ => simpa using h0
    | 1, _ => simpa using h1
    | i + 2, hi => have := hr i (by omega); simpa using this

/-- Characterisation of membership in `blockPreimage (b :: s')`: it consists of
strings `c :: d :: t'` where `c || d = b` and `t'` lies in `blockPreimage s'`. -/
lemma mem_blockPreimage_cons (b : Bool) (s' : BitString) (t : BitString) :
    t ∈ blockPreimage (b :: s') ↔
      ∃ c d t', (c || d) = b ∧ t' ∈ blockPreimage s' ∧ t = c :: d :: t' := by
  cases b with
  | false =>
    simp only [blockPreimage, List.mem_map]
    constructor
    · rintro ⟨t', ht', rfl⟩
      exact ⟨false, false, t', rfl, ht', rfl⟩
    · rintro ⟨c, d, t', hcd, ht', rfl⟩
      refine ⟨t', ht', ?_⟩
      cases c <;> cases d <;> simp_all
  | true =>
    simp only [blockPreimage, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨t', ht', (rfl | rfl | rfl)⟩
      · exact ⟨false, true, t', rfl, ht', rfl⟩
      · exact ⟨true, false, t', rfl, ht', rfl⟩
      · exact ⟨true, true, t', rfl, ht', rfl⟩
    · rintro ⟨c, d, t', hcd, ht', rfl⟩
      refine ⟨t', ht', ?_⟩
      cases c <;> cases d <;> simp_all

/-- The fundamental correspondence of cylinders under `blockMap`. -/
lemma mem_cantorCylinder_blockMap (s : BitString) (x : CantorSeq) :
    blockMap x ∈ cantorCylinder s ↔ ∃ t ∈ blockPreimage s, x ∈ cantorCylinder t := by
  induction s generalizing x with
  | nil =>
    have hnil : ∀ y : CantorSeq, y ∈ cantorCylinder ([] : BitString) := by
      intro y i hi; simp at hi
    refine iff_of_true (hnil _) ⟨[], ?_, hnil _⟩
    simp [blockPreimage]
  | cons b s' ih =>
    rw [mem_cantorCylinder_cons]
    have hfun : (fun j => blockMap x (j + 1)) = blockMap (fun j => x (j + 2)) := by
      funext j; exact blockMap_succ x j
    rw [hfun, blockMap_zero, ih (fun j => x (j + 2))]
    constructor
    · rintro ⟨hb, t', ht', hmem⟩
      refine ⟨x 0 :: x 1 :: t', ?_, ?_⟩
      · rw [mem_blockPreimage_cons]
        exact ⟨x 0, x 1, t', hb, ht', rfl⟩
      · rw [mem_cantorCylinder_cons₂]
        exact ⟨rfl, rfl, hmem⟩
    · rintro ⟨t, ht, hmem⟩
      rw [mem_blockPreimage_cons] at ht
      obtain ⟨c, d, t', hcd, ht', rfl⟩ := ht
      rw [mem_cantorCylinder_cons₂] at hmem
      obtain ⟨hx0, hx1, hmem'⟩ := hmem
      refine ⟨?_, t', ht', hmem'⟩
      rw [hx0, hx1]; exact hcd

/-- Every string in `blockPreimage s` has length `2 * |s|`. -/
lemma blockPreimage_length_bits (s : BitString) :
    ∀ t ∈ blockPreimage s, t.length = 2 * s.length := by
  induction s with
  | nil =>
      intro t ht
      simp only [blockPreimage, List.mem_cons, List.not_mem_nil, or_false] at ht
      subst ht; simp
  | cons b s' ih =>
    intro t ht
    rw [mem_blockPreimage_cons] at ht
    obtain ⟨c, d, t', _, ht', rfl⟩ := ht
    have := ih t' ht'
    simp only [List.length_cons]; omega

/-- `blockPreimage s` has exactly `3^{#true(s)}` strings. -/
lemma blockPreimage_card (s : BitString) :
    (blockPreimage s).length = 3 ^ s.count true := by
  induction s with
  | nil => simp [blockPreimage]
  | cons b s' ih =>
    cases b with
    | false => simp [blockPreimage, List.length_map, ih]
    | true =>
      have hflat : (blockPreimage (true :: s')).length = 3 * (blockPreimage s').length := by
        simp only [blockPreimage]
        induction (blockPreimage s') with
        | nil => simp
        | cons a l ihl =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
            ihl]
          ring
      rw [hflat, ih, List.count_cons]
      simp only [beq_iff_eq, if_true]
      ring

/-- The uniform mass of the preimage equals the Bernoulli(3/4) mass.  Stated as a
list sum (each `t ∈ blockPreimage s` counted once, which matches the total mass
since the strings are distinct); this is the form consumed by the Solovay-test
pullback, mirroring `tsum_selectPullOne` for Problem 82. -/
lemma sum_cantorMass_blockPreimage (s : BitString) :
    ((blockPreimage s).map (cantorMass uniformMeasure)).sum = cantorMass bernoulli34 s := by
  have hsum : ∀ (l : List BitString) (c : ℝ≥0∞),
      (l.map (fun _ => c)).sum = (l.length : ℝ≥0∞) * c := by
    intro l c
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring
  have hconst : (blockPreimage s).map (cantorMass uniformMeasure)
      = (blockPreimage s).map (fun _ => (2⁻¹ : ℝ≥0∞) ^ (2 * s.length)) := by
    apply List.map_congr_left
    intro t ht
    rw [cantorMass_uniformMeasure, blockPreimage_length_bits s t ht]
  rw [hconst, hsum, blockPreimage_card, cantorMass_bernoulli34_eq, ← ENNReal.inv_pow,
      div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]

/-- The preimage list `blockPreimage s` has no repetitions. -/
lemma blockPreimage_nodup (s : BitString) : (blockPreimage s).Nodup := by
  induction s with
  | nil => simp [blockPreimage]
  | cons b s' ih =>
    cases b with
    | false => exact List.Nodup.map (fun a b h => by simpa using h) ih
    | true =>
      refine List.nodup_flatMap.mpr ⟨fun t _ => by simp, ?_⟩
      refine ih.imp ?_
      intro a b hab
      simp only [Function.onFun, List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> simp_all

instance : IsProbabilityMeasure bernoulli34 := by
  dsimp [bernoulli34]; infer_instance

/-- The block map is measurable. -/
lemma measurable_blockMap : Measurable blockMap := by
  apply measurable_pi_lambda
  intro n
  have hset : MeasurableSet ((fun f : CantorSeq => f (2 * n)) ⁻¹' {true}) :=
    (measurable_pi_apply (2 * n)) (measurableSet_singleton true)
  have h : (fun x : CantorSeq => blockMap x n)
      = fun x => if x (2 * n) = true then true else x (2 * n + 1) := by
    funext x; simp only [blockMap]; cases hx : x (2 * n) <;> simp
  rw [h]
  exact Measurable.ite hset measurable_const (measurable_pi_apply (2 * n + 1))

/-- The `blockMap`-preimage of a cylinder is the finite union of the cylinders
enumerated by `blockPreimage`. -/
lemma blockMap_preimage_cantorCylinder (s : BitString) :
    blockMap ⁻¹' cantorCylinder s = ⋃ t ∈ (blockPreimage s).toFinset, cantorCylinder t := by
  ext x
  simp only [Set.mem_preimage, Set.mem_iUnion, List.mem_toFinset, exists_prop]
  exact mem_cantorCylinder_blockMap s x

/-- Distinct preimage strings have the same length, hence disjoint cylinders. -/
lemma pairwiseDisjoint_blockPreimage_cylinders (s : BitString) :
    ((blockPreimage s).toFinset : Set BitString).PairwiseDisjoint cantorCylinder := by
  intro t ht u hu htu
  simp only [Finset.mem_coe, List.mem_toFinset] at ht hu
  have hlt := blockPreimage_length_bits s t ht
  have hlu := blockPreimage_length_bits s u hu
  have hlen : t.length = u.length := by omega
  refine cantorCylinder_disjoint_of_incompatible ?_ ?_
  · intro hp; exact htu (hp.eq_of_length hlen)
  · intro hp; exact htu (hp.eq_of_length hlen.symm).symm

/-- The uniform measure of the `blockMap`-preimage of a cylinder is its
Bernoulli(3/4) mass. -/
lemma uniformMeasure_blockMap_preimage (s : BitString) :
    uniformMeasure (blockMap ⁻¹' cantorCylinder s) = cantorMass bernoulli34 s := by
  rw [blockMap_preimage_cantorCylinder,
    measure_biUnion_finset (pairwiseDisjoint_blockPreimage_cylinders s)
      (fun t _ => measurableSet_cantorCylinder t),
    show (∑ t ∈ (blockPreimage s).toFinset, uniformMeasure (cantorCylinder t))
      = ∑ t ∈ (blockPreimage s).toFinset, cantorMass uniformMeasure t from rfl,
    List.sum_toFinset _ (blockPreimage_nodup s), sum_cantorMass_blockPreimage]

/-- The block map preserves measure from uniform to Bernoulli(3/4). -/
lemma blockMap_measurePreserving :
    MeasurePreserving blockMap uniformMeasure bernoulli34 := by
  refine ⟨measurable_blockMap, ?_⟩
  have : IsProbabilityMeasure (Measure.map blockMap uniformMeasure) :=
    Measure.isProbabilityMeasure_map measurable_blockMap.aemeasurable
  refine cantorMeasure_unique _ _ (fun s => ?_)
  rw [cantorMass, Measure.map_apply measurable_blockMap (measurableSet_cantorCylinder s)]
  exact uniformMeasure_blockMap_preimage s

/-- Computable pullback of a Solovay test along the block map. -/
def blockPullTest (f : ℕ → Option BitString) (n : ℕ) : Option BitString :=
  (f n.unpair.1).bind (fun s => (blockPreimage s)[n.unpair.2]?)

/-- `blockPreimage` as a right fold, exposing its primitive-recursive shape. -/
lemma blockPreimage_eq_foldr (s : BitString) :
    blockPreimage s = s.foldr (fun b ih =>
      bif b then ih.flatMap (fun t => [false::true::t, true::false::t, true::true::t])
             else ih.map (fun t => false::false::t)) [[]] := by
  induction s with
  | nil => rfl
  | cons b s ih => cases b <;> simp [blockPreimage, ih]

/-- `blockPreimage` is primitive recursive. -/
lemma primrec_blockPreimage : Primrec blockPreimage := by
  have cons2 : ∀ (a b : Bool),
      Primrec₂ (fun (_ : BitString × (Bool × List BitString)) (t : BitString) => a :: b :: t) := by
    intro a b
    exact (Primrec.list_cons.comp (Primrec.const a)
      (Primrec.list_cons.comp (Primrec.const b) Primrec.snd)).to₂
  have hmap : Primrec (fun p : BitString × (Bool × List BitString) =>
      p.2.2.map (fun t => false :: false :: t)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) (cons2 false false)
  have hflat : Primrec (fun p : BitString × (Bool × List BitString) =>
      p.2.2.flatMap (fun t => [false::true::t, true::false::t, true::true::t])) := by
    have hg : Primrec₂ (fun (_ : BitString × (Bool × List BitString)) (t : BitString) =>
        [false::true::t, true::false::t, true::true::t]) :=
      (Primrec.list_cons.comp (cons2 false true)
        (Primrec.list_cons.comp (cons2 true false)
          (Primrec.list_cons.comp (cons2 true true) (Primrec.const [])))).to₂
    exact Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) hg
  have hstep : Primrec₂ (fun (_ : BitString) (bs : Bool × List BitString) =>
      bif bs.1 then bs.2.flatMap (fun t => [false::true::t, true::false::t, true::true::t])
               else bs.2.map (fun t => false::false::t)) :=
    (Primrec.cond (Primrec.fst.comp Primrec.snd) hflat hmap).to₂
  refine (Primrec.list_foldr Primrec.id (Primrec.const [[]]) hstep).of_eq
    (fun s => (blockPreimage_eq_foldr s).symm)

/-- The pullback of a computable enumeration of basic sets along the block map is again a
computable enumeration. -/
lemma computable_blockPullTest {f : ℕ → Option BitString} (hf : Computable f) :
    Computable (blockPullTest f) := by
  have hbody : Computable₂ (fun (n : ℕ) (s : BitString) => (blockPreimage s)[n.unpair.2]?) := by
    have hbp : Computable (fun a : ℕ × BitString => blockPreimage a.2) :=
      primrec_blockPreimage.to_comp.comp Computable.snd
    have hidx : Computable (fun a : ℕ × BitString => a.1.unpair.2) :=
      (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst
    exact (Primrec.list_getElem?.to_comp.comp hbp hidx).to₂
  have hfa : Computable (fun n : ℕ => f n.unpair.1) :=
    hf.comp ((Primrec.fst.comp Primrec.unpair).to_comp)
  exact Computable.option_bind hfa hbody

/-- The uniform mass carried by the `blockMap`-pullback of a single cylinder `s`
equals its Bernoulli(3/4) mass. -/
lemma tsum_blockPullOne (s : BitString) :
    (∑' m : ℕ, ((blockPreimage s)[m]?).elim (0 : ℝ≥0∞) (cantorMass uniformMeasure))
      = cantorMass bernoulli34 s := by
  rw [tsum_list_getElem?_elim, sum_cantorMass_blockPreimage]

/-- The `blockMap`-pullback of a Solovay test preserves total uniform mass:
`∑ uniform(pullback) = ∑ bernoulli34(original)`. -/
lemma tsum_blockPullTest (g : ℕ → Option BitString) :
    (∑' n : ℕ, (blockPullTest g n).elim (0 : ℝ≥0∞) (cantorMass uniformMeasure))
      = ∑' i : ℕ, (g i).elim (0 : ℝ≥0∞) (cantorMass bernoulli34) := by
  rw [← (Nat.pairEquiv).tsum_eq
    (fun n => (blockPullTest g n).elim (0 : ℝ≥0∞) (cantorMass uniformMeasure))]
  have hstep : (∑' c : ℕ × ℕ,
        (blockPullTest g (Nat.pairEquiv c)).elim (0 : ℝ≥0∞) (cantorMass uniformMeasure))
      = ∑' c : ℕ × ℕ,
        (g c.1).elim (0 : ℝ≥0∞)
          (fun s => ((blockPreimage s)[c.2]?).elim (0 : ℝ≥0∞) (cantorMass uniformMeasure)) := by
    refine tsum_congr fun c => ?_
    obtain ⟨i, m⟩ := c
    simp only [blockPullTest, Nat.pairEquiv_apply, Function.uncurry_apply_pair, Nat.unpair_pair]
    cases g i with
    | none => simp
    | some s => simp
  rw [hstep]
  refine Eq.trans (ENNReal.tsum_prod
    (f := fun i m => (g i).elim (0 : ℝ≥0∞)
      (fun s => ((blockPreimage s)[m]?).elim (0 : ℝ≥0∞) (cantorMass uniformMeasure)))) ?_
  refine tsum_congr fun i => ?_
  cases g i with
  | none => simp
  | some s => simpa using tsum_blockPullOne s

/-- If `blockMap x` lands in `cantorCylinder s`, then `x` lands in one of the
preimage cylinders enumerated by `blockPreimage s`. -/
lemma exists_mem_blockPullOne {s : BitString} {x : CantorSeq}
    (h : blockMap x ∈ cantorCylinder s) :
    ∃ m : ℕ, x ∈ ((blockPreimage s)[m]?).elim (∅ : Set CantorSeq) cantorCylinder := by
  rw [mem_cantorCylinder_blockMap] at h
  obtain ⟨t, ht, hx⟩ := h
  obtain ⟨m, hm, hget⟩ := List.getElem_of_mem ht
  refine ⟨m, ?_⟩
  rw [List.getElem?_eq_getElem hm, hget]
  exact hx

/-- **SUV Chapter 3, Problem 83.** The block map transforms uniform ML-randomness
into Bernoulli(3/4) ML-randomness. -/
theorem isMartinLofRandom_bernoulli34_blockMap {x : CantorSeq}
    (hx : IsMartinLofRandom uniformMeasure x) :
    IsMartinLofRandom bernoulli34 (blockMap x) := by
  by_contra hnot
  rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_bernoulli34] at hnot
  obtain ⟨g, hgc, hgsum, hginf⟩ := hnot
  have hxnot : ¬ IsMartinLofRandom uniformMeasure x := by
    rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_uniform]
    refine ⟨blockPullTest g, computable_blockPullTest hgc, ?_, ?_⟩
    · rw [tsum_blockPullTest g]; exact hgsum
    · have hchoice : ∀ i ∈ {i | blockMap x ∈ (g i).elim ∅ cantorCylinder},
          ∃ m, x ∈ (blockPullTest g (Nat.pair i m)).elim ∅ cantorCylinder := by
        intro i hi
        simp only [Set.mem_ofPred_eq] at hi
        cases hgi : g i with
        | none => rw [hgi] at hi; simp at hi
        | some s =>
            rw [hgi] at hi
            simp only [Option.elim_some] at hi
            obtain ⟨m, hm⟩ := exists_mem_blockPullOne hi
            refine ⟨m, ?_⟩
            simpa [blockPullTest, hgi, Nat.unpair_pair] using hm
      choose! pick hpick using hchoice
      refine Set.Infinite.mono (s := (fun i => Nat.pair i (pick i)) ''
        {i | blockMap x ∈ (g i).elim ∅ cantorCylinder}) ?_ ?_
      · rintro n ⟨i, hi, rfl⟩
        exact hpick i hi
      · refine Set.Infinite.image ?_ hginf
        intro a _ b _ hab
        exact (Nat.pair_eq_pair.1 hab).1
  exact hxnot hx

/-! ## Lifting Bernoulli(3/4)-randomness back through the block map (Problem 84)

The lift is obtained by contraposition.  If no preimage of `y` were uniformly
ML-random, the whole (compact) fibre of `y` would be swallowed by every level of
the universal uniform test `U`.  The set of `y'` whose fibre is covered by a
level of `U` is itself effectively open (compactness makes the covering
condition depend only on a finite prefix of `y'`), and by measure preservation
its Bernoulli(3/4)-mass is bounded by the uniform mass of that level.  So it is
a Bernoulli(3/4) Martin-Löf test containing `y`, contradicting `hy`. -/

/-- The lift of `y` that starts with the preimage string `t` and then copies each
bit of `y` twice. -/
def blockLift (y : CantorSeq) (t : BitString) : CantorSeq :=
  fun m => if h : m < t.length then t[m] else y (m / 2)

/-- The lift of `y` along the string `t` lies in the cylinder determined by `t`. -/
lemma blockLift_mem_cantorCylinder (y : CantorSeq) (t : BitString) :
    blockLift y t ∈ cantorCylinder t := by
  intro i hi
  simp [blockLift, hi]

/-- If `t` is a preimage of the length-`k` prefix of `y`, the lift `blockLift y t`
is a genuine preimage of `y` extending `t`. -/
lemma blockMap_blockLift {y : CantorSeq} {k : ℕ} {t : BitString}
    (ht : t ∈ blockPreimage (cantorPrefix y k)) :
    blockMap (blockLift y t) = y := by
  have hlen : t.length = 2 * k := by
    have := blockPreimage_length_bits _ t ht
    simpa using this
  have hcyl : blockMap (blockLift y t) ∈ cantorCylinder (cantorPrefix y k) :=
    (mem_cantorCylinder_blockMap _ _).2 ⟨t, ht, blockLift_mem_cantorCylinder y t⟩
  funext n
  by_cases hn : n < k
  · have := hcyl n (by simpa using hn)
    simpa using this
  · have h1 : ¬ (2 * n < t.length) := by omega
    have h2 : ¬ (2 * n + 1 < t.length) := by omega
    change (blockLift y t (2 * n) || blockLift y t (2 * n + 1)) = y n
    simp only [blockLift, h1, h2]
    rw [show 2 * n / 2 = n from by omega, show (2 * n + 1) / 2 = n from by omega]
    simp

/-- The block map is continuous. -/
lemma continuous_blockMap : Continuous blockMap := by
  refine continuous_pi fun n => ?_
  have h : Continuous (fun x : CantorSeq => (x (2 * n), x (2 * n + 1))) :=
    (continuous_apply _).prodMk (continuous_apply _)
  exact (continuous_of_discreteTopology (f := fun p : Bool × Bool => p.1 || p.2)).comp h

/-- Fibres of the block map are compact. -/
lemma isCompact_blockMap_fibre (y : CantorSeq) : IsCompact (blockMap ⁻¹' {y}) :=
  (isClosed_singleton.preimage continuous_blockMap).isCompact

/-- Auxiliary counter for `blockCovered`: all of the first `j` block-preimages of
`s` are covered by the enumeration `f`. -/
def blockCoveredUpto (f : ℕ → Option BitString) (s : BitString) : ℕ → Bool
  | 0 => true
  | j + 1 => blockCoveredUpto f s j && (((blockPreimage s)[j]?).map (decidableCover f)).getD true

/-- The strings all of whose block-preimages are already covered by the
enumeration `f` (in the bounded-stage sense of `decidableCover`). -/
def blockCovered (f : ℕ → Option BitString) (s : BitString) : Bool :=
  blockCoveredUpto f s (blockPreimage s).length

/-- The bounded covering test succeeds exactly when each of the first `m` block preimages of `s`
is covered by the enumeration. -/
lemma blockCoveredUpto_spec (f : ℕ → Option BitString) (s : BitString) (m : ℕ) :
    blockCoveredUpto f s m = true ↔
      ∀ j < m, (((blockPreimage s)[j]?).map (decidableCover f)).getD true = true := by
  induction m with
  | zero => simp [blockCoveredUpto]
  | succ m ih =>
    rw [blockCoveredUpto, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · exact h1 j h
      · exact h2
    · intro h
      exact ⟨fun j hj => h j (by omega), h m (by omega)⟩

/-- The covering test on `s` succeeds exactly when every block preimage of `s` is covered by the
enumeration. -/
lemma blockCovered_iff (f : ℕ → Option BitString) (s : BitString) :
    blockCovered f s = true ↔ ∀ t ∈ blockPreimage s, decidableCover f t = true := by
  rw [blockCovered, blockCoveredUpto_spec]
  constructor
  · intro h t ht
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem ht
    have hj' := h j hj
    rw [List.getElem?_eq_getElem hj, hget] at hj'
    simpa using hj'
  · intro h j hj
    rw [List.getElem?_eq_getElem hj]
    simpa using h _ (List.getElem_mem hj)

/-- The effectively open set of sequences whose fibre is covered by `f`. -/
def blockCoveredSet (f : ℕ → Option BitString) : Set CantorSeq :=
  ⋃ s, if blockCovered f s then cantorCylinder s else (∅ : Set CantorSeq)

/-- The set of sequences all of whose blocks are covered by the enumeration is measurable. -/
lemma measurableSet_blockCoveredSet (f : ℕ → Option BitString) :
    MeasurableSet (blockCoveredSet f) := by
  refine MeasurableSet.iUnion fun s => ?_
  by_cases h : blockCovered f s <;> simp [h, measurableSet_cantorCylinder]

/-- Everything in the `blockMap`-preimage of `blockCoveredSet f` is covered by `f`. -/
lemma blockMap_preimage_blockCoveredSet_subset (f : ℕ → Option BitString) :
    blockMap ⁻¹' blockCoveredSet f ⊆ ⋃ i, (f i).elim ∅ cantorCylinder := by
  intro x hx
  simp only [Set.mem_preimage, blockCoveredSet, Set.mem_iUnion] at hx
  obtain ⟨s, hs⟩ := hx
  by_cases hc : blockCovered f s = true
  · rw [if_pos hc] at hs
    obtain ⟨t, ht, hxt⟩ := (mem_cantorCylinder_blockMap s x).1 hs
    have hdt : decidableCover f t = true := (blockCovered_iff f s).1 hc t ht
    have hmem : x ∈ ⋃ x',
        if decidableCover f x' then cantorCylinder x' else (∅ : Set CantorSeq) :=
      Set.mem_iUnion.2 ⟨t, by simp [hdt, hxt]⟩
    rwa [decidableCover_iUnion] at hmem
  · rw [if_neg hc] at hs
    exact absurd hs (Set.notMem_empty x)

/-- Compactness: if the whole fibre of `y` is covered by `f`, then already a
finite prefix of `y` witnesses this, i.e. `y ∈ blockCoveredSet f`. -/
lemma mem_blockCoveredSet_of_fibre_subset (f : ℕ → Option BitString) (y : CantorSeq)
    (hsub : blockMap ⁻¹' {y} ⊆ ⋃ i, (f i).elim ∅ cantorCylinder) :
    y ∈ blockCoveredSet f := by
  obtain ⟨I, hI⟩ := (isCompact_blockMap_fibre y).elim_finite_subcover
    (fun i => (f i).elim ∅ cantorCylinder)
    (fun i => by
      cases hfi : f i with
      | none => exact isOpen_empty
      | some u => exact isOpen_cantorCylinder u) hsub
  set N := I.sup id with hN
  set L := I.sup (fun i => (f i).elim 0 List.length) with hL
  have hcov : blockCovered f (cantorPrefix y (N + L + 1)) = true := by
    rw [blockCovered_iff]
    intro t ht
    have hlen : t.length = 2 * (N + L + 1) := by
      simpa using blockPreimage_length_bits _ t ht
    have hx : blockLift y t ∈ blockMap ⁻¹' {y} := blockMap_blockLift ht
    obtain ⟨i, hiI, hxi⟩ := Set.mem_iUnion₂.1 (hI hx)
    cases hfi : f i with
    | none => rw [hfi] at hxi; simp at hxi
    | some u =>
        rw [hfi] at hxi
        have hu : IsCantorPrefix u (blockLift y t) := hxi
        have huL : u.length ≤ L := by
          have hle := Finset.le_sup (f := fun i => (f i).elim 0 List.length) hiI
          simpa [hfi] using hle
        have hut : u <+: t :=
          prefix_of_isCantorPrefix hu (blockLift_mem_cantorCylinder y t) (by omega)
        have hiN : i ≤ N := Finset.le_sup (f := id) hiI
        exact (prefixSeen_spec f t (t.length + 1)).2 ⟨i, by omega, u, hfi, hut⟩
  refine Set.mem_iUnion.2 ⟨cantorPrefix y (N + L + 1), ?_⟩
  rw [if_pos hcov]
  exact mem_cantorCylinder_cantorPrefix y (N + L + 1)

/-- The covering test is computable uniformly in the index of a computable family of
enumerations. -/
lemma computable_blockCovered {f : ℕ → ℕ → Option BitString} (hf : Computable₂ f) :
    Computable₂ (fun n s => blockCovered (f n) s) := by
  have hdc : Computable₂ (fun n x => decidableCover (f n) x) := computable_decidableCover hf
  have hlen : Computable (fun a : ℕ × BitString => (blockPreimage a.2).length) :=
    (Primrec.list_length.comp (primrec_blockPreimage.comp Primrec.snd)).to_comp
  have hstep : Computable₂ (fun (a : ℕ × BitString) (q : ℕ × Bool) =>
      q.2 && (((blockPreimage a.2)[q.1]?).map (decidableCover (f a.1))).getD true) := by
    have hopt : Computable (fun r : (ℕ × BitString) × (ℕ × Bool) =>
        (blockPreimage r.1.2)[r.2.1]?) :=
      Primrec.list_getElem?.to_comp.comp
        ((primrec_blockPreimage.comp (Primrec.snd.comp Primrec.fst)).to_comp)
        (Computable.fst.comp Computable.snd)
    have hmap : Computable (fun r : (ℕ × BitString) × (ℕ × Bool) =>
        ((blockPreimage r.1.2)[r.2.1]?).map (decidableCover (f r.1.1))) :=
      Computable.option_map hopt
        (hdc.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd)
    exact (Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.option_getD hmap (Computable.const true))).to₂
  have hrec := Computable.nat_rec hlen (Computable.const true) hstep
  have hfin : Computable (fun a : ℕ × BitString => blockCovered (f a.1) a.2) := by
    refine hrec.of_eq ?_
    rintro ⟨n, s⟩
    simp only [blockCovered]
    induction (blockPreimage s).length with
    | zero => rfl
    | succ m ih => simp only [blockCoveredUpto]; rw [← ih]
  exact hfin.to₂

/-- The covered sets of a computable family of enumerations form a uniformly effectively open
family. -/
lemma isUniformlyEffectiveOpen_blockCoveredSet {f : ℕ → ℕ → Option BitString}
    (hf : Computable₂ f) : IsUniformlyEffectiveOpen (fun n => blockCoveredSet (f n)) := by
  refine ⟨fun n i => decidableFamilyEnum (blockCovered (f n)) i,
    computable_decidableFamilyEnum (computable_blockCovered hf), fun n => ?_⟩
  rw [decidableFamilyEnum_iUnion]
  rfl

/-- **SUV Chapter 3, Problem 84.** Every Bernoulli(3/4) ML-random sequence can be
obtained via `blockMap` from a uniformly ML-random sequence. -/
theorem exists_isMartinLofRandom_uniform_of_isMartinLofRandom_bernoulli34
    {y : CantorSeq} (hy : IsMartinLofRandom bernoulli34 y) :
    ∃ x : CantorSeq, IsMartinLofRandom uniformMeasure x ∧ blockMap x = y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨U, hU⟩ := exists_universal_martinLof_test isComputableMeasure_uniform
  obtain ⟨f, hf, hUeq⟩ := hU.1.1
  refine hy (fun n => blockCoveredSet (f n))
    ⟨isUniformlyEffectiveOpen_blockCoveredSet hf, fun n => ?_⟩ (Set.mem_iInter.2 fun n => ?_)
  · have h1 : uniformMeasure (blockMap ⁻¹' blockCoveredSet (f n))
        = bernoulli34 (blockCoveredSet (f n)) :=
      blockMap_measurePreserving.measure_preimage
        (measurableSet_blockCoveredSet (f n)).nullMeasurableSet
    rw [← h1]
    refine le_trans (measure_mono ?_) (hU.1.2 n)
    rw [hUeq n]
    exact blockMap_preimage_blockCoveredSet_subset (f n)
  · refine mem_blockCoveredSet_of_fibre_subset (f n) y ?_
    intro x hx
    have hnr : ¬ IsMartinLofRandom uniformMeasure x := fun hr => hcon x hr hx
    have hmem := Set.mem_iInter.1
      ((not_isMartinLofRandom_iff_mem_universal_test hU x).1 hnr) n
    rwa [hUeq n] at hmem

end Kolmogorov
