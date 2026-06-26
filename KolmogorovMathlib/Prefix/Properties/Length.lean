/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.Prefix.CountableKraft
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Prefix.CountingBound
import KolmogorovMathlib.Prefix.Properties.Pair

/-!
# Properties of Prefix Complexity

This module establishes the first layer of easy theorems about prefix complexity
and its relationship to ordinary/plain Kolmogorov complexity, mirroring SUV Chapter 4.
-/

namespace Kolmogorov
open scoped ENNReal


/-- Optional implementation of a simple length decompressor. -/
def simpleLenDecompressorOpt (p : List Bool) : Option (List Bool) :=
  bif (p.length == (p.takeWhile id).length + (p.takeWhile id).length + 1) then some (p.drop ((p.takeWhile id).length + 1)) else none

/-- A simple length decompressor. -/
def simpleLenDecompressor : Map := fun pr => Part.ofOption (simpleLenDecompressorOpt pr.1)

lemma simpleLenDecompressor_computable : isDecompressor simpleLenDecompressor := by
  have h_opt : Computable simpleLenDecompressorOpt := by
    have h_n : Computable (fun p : List Bool => (p.takeWhile id).length) :=
      ((Primrec.list_findIdx Primrec.id (Primrec.not.comp Primrec.snd).to₂).of_eq
        (fun z => (takeWhile_id_length_eq_findIdx z).symm)).to_comp
    have h_n_plus_1 : Computable (fun p : List Bool => (p.takeWhile id).length + 1) :=
      Computable.succ.comp h_n
    have h_q : Computable (fun p : List Bool => p.drop ((p.takeWhile id).length + 1)) :=
      primrec_list_drop.to_comp.comp Computable.id h_n_plus_1
    have h_len : Computable (fun p : List Bool => p.length) :=
      Computable.list_length
    have h_add : Computable₂ (fun (x y : Nat) => x + y) := Primrec.nat_add.to_comp
    have h_2n : Computable (fun p : List Bool => (p.takeWhile id).length + (p.takeWhile id).length) :=
      h_add.comp h_n h_n
    have h_2n1 : Computable (fun p : List Bool => (p.takeWhile id).length + (p.takeWhile id).length + 1) :=
      Computable.succ.comp h_2n
    have h_beq : Computable (fun p : List Bool => (p.length == (p.takeWhile id).length + (p.takeWhile id).length + 1)) := by
      have h1 := (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp (h_len.pair h_2n1)
      exact h1.of_eq (fun p => rfl)
    have h_none : Computable (fun (p : List Bool) => (none : Option (List Bool))) :=
      Computable.const (α := List Bool) (σ := Option (List Bool)) none
    have h_cond := Computable.cond h_beq (Computable.option_some.comp h_q) h_none
    exact h_cond.of_eq (fun p => by
      unfold simpleLenDecompressorOpt
      cases h : (p.length == (p.takeWhile id).length + (p.takeWhile id).length + 1)
      · rfl
      · rfl)
  have h_fst : Computable (fun (pr : List Bool × List Bool) => pr.1) := Computable.fst
  have h_pr := Computable.ofOption (h_opt.comp h_fst)
  exact h_pr

lemma takeWhile_length_eq_of_prefix {p q : List Bool} (hpre : p <+: q)
    (h_bounds : (p.takeWhile id).length < p.length) :
    (p.takeWhile id).length = (q.takeWhile id).length := by
  induction p generalizing q
  · exact absurd h_bounds (by simp)
  · rename_i a p ih
    rcases hpre with ⟨t, rfl⟩
    cases h_a : a
    · -- a = false
      rfl
    · -- a = true
      subst h_a
      have h1 : (List.takeWhile id (true :: p)).length = (List.takeWhile id p).length + 1 := rfl
      have h2 : (List.takeWhile id (true :: p ++ t)).length = (List.takeWhile id (p ++ t)).length + 1 := rfl
      have h_bounds_p : (List.takeWhile id p).length < p.length := by
        rw [h1] at h_bounds
        have h3 : (true :: p).length = p.length + 1 := rfl
        omega
      have h_ih := ih (List.prefix_append p t) h_bounds_p
      rw [h1, h_ih, h2]

lemma simpleLenDecompressor_isPrefixMachine : IsPrefixMachine simpleLenDecompressor := by
  intro y p hp q hq hpre
  unfold simpleLenDecompressor at hp hq
  have hp' : simpleLenDecompressorOpt p ≠ none := by
    intro h
    change (Part.ofOption (simpleLenDecompressorOpt p)).Dom at hp
    rw [h] at hp
    exact hp
  have hq' : simpleLenDecompressorOpt q ≠ none := by
    intro h
    change (Part.ofOption (simpleLenDecompressorOpt q)).Dom at hq
    rw [h] at hq
    exact hq
  unfold simpleLenDecompressorOpt at hp' hq'
  cases h1 : (p.length == (p.takeWhile id).length + (p.takeWhile id).length + 1) <;> rw [h1] at hp'
  · contradiction
  cases h2 : (q.length == (q.takeWhile id).length + (q.takeWhile id).length + 1) <;> rw [h2] at hq'
  · contradiction
  have h1_eq := beq_iff_eq.mp h1
  have h2_eq := beq_iff_eq.mp h2
  have h_bounds : (p.takeWhile id).length < p.length := by omega
  have h_n_eq : (p.takeWhile id).length = (q.takeWhile id).length :=
    takeWhile_length_eq_of_prefix hpre h_bounds
  have h_len_eq : p.length = q.length := by
    rw [h1_eq, h2_eq, h_n_eq]
  rcases hpre with ⟨t, rfl⟩
  have ht : t = [] := by
    have h_len2 : p.length = (p ++ t).length := h_len_eq
    simp only [List.length_append] at h_len2
    cases t
    · rfl
    · simp at h_len2
  subst ht
  exact (List.append_nil p).symm

lemma simpleLenDecompressor_produces (p y : List Bool) (h : p.length = (p.takeWhile id).length + (p.takeWhile id).length + 1) :
    produces simpleLenDecompressor p y (p.drop ((p.takeWhile id).length + 1)) := by
  unfold produces simpleLenDecompressor
  have heq : simpleLenDecompressorOpt p = some (p.drop ((p.takeWhile id).length + 1)) := by
    unfold simpleLenDecompressorOpt
    rw [beq_iff_eq.mpr h]
    rfl
  change _ ∈ Part.ofOption (simpleLenDecompressorOpt p)
  rw [heq]
  exact ⟨trivial, rfl⟩

/-- Kraft sum for prefix complexity. -/
theorem KPPlain_kraft_sum_le_one (U : Map) (hU : IsPrefixDecompressor U) :
    (∑' x : BitString, complexityWeight (KPPlain U x)) ≤ 1 := by
  have h := tsum_aprioriMeasure_le_one U [] hU.isPrefixMachine
  have h_le : ∀ x, complexityWeight (KPPlain U x) ≤ aprioriMeasure U x [] := fun x =>
    complexityWeight_KP_le_aprioriMeasure U x []
  exact le_trans (ENNReal.tsum_le_tsum h_le) h

lemma drop_replicate_append (n : Nat) (x : List Bool) :
  List.drop (n + 1) (List.replicate n true ++ false :: x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Simple length bound: `KPPlain U x ≤ 2 * x.length + O(1)`. -/
theorem KPPlain_le_two_mul_length (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, KPPlain U x ≤ 2 * x.length + (c : ENat) := by
  have hM : IsPrefixDecompressor simpleLenDecompressor := ⟨simpleLenDecompressor_computable, simpleLenDecompressor_isPrefixMachine⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  use c + 1
  intro x
  let p : List Bool := List.replicate x.length true ++ (false :: x)
  have h_p_take : (p.takeWhile id).length = x.length := by
    simp [p]
  have h_p_len : p.length = 2 * x.length + 1 := by
    simp [p]
    omega
  have h_p_eq : p.length = (p.takeWhile id).length + (p.takeWhile id).length + 1 := by
    rw [h_p_take, h_p_len]
    omega
  have h_prod := simpleLenDecompressor_produces p [] h_p_eq
  have h_drop : p.drop ((p.takeWhile id).length + 1) = x := by
    rw [h_p_take]
    exact drop_replicate_append x.length x
  rw [h_drop] at h_prod
  have h_KP := KP_le_programLength_of_produces h_prod
  calc
    KPPlain U x = KP U x [] := rfl
    _           ≤ KP simpleLenDecompressor x [] + c := hc x []
    _           ≤ p.length + c := by gcongr
    _           = ((2 * x.length + 1 : ℕ) : ENat) + c := by rw [h_p_len]
    _           = (2 * x.length + (c + 1) : ℕ) := by norm_cast; omega

/-- Conditional decompressor that accepts exactly programs whose length is the
length encoded in the context and returns the program literally. For each fixed
context, all halting programs have the same length, hence form a prefix-free
domain. -/
def exactLengthContextDecompressorOpt (pr : BitString × BitString) : Option BitString :=
  bif (pr.1.length == decodeBits pr.2) then some pr.1 else none

/-- Decompressor for `exactLengthContextDecompressorOpt`. -/
def exactLengthContextDecompressor : Map := fun pr =>
  Part.ofOption (exactLengthContextDecompressorOpt pr)

lemma exactLengthContextDecompressor_computable :
    isDecompressor exactLengthContextDecompressor := by
  have h_opt : Computable exactLengthContextDecompressorOpt := by
    have h_len : Computable (fun pr : BitString × BitString => pr.1.length) :=
      Computable.list_length.comp Computable.fst
    have h_dec : Computable (fun pr : BitString × BitString => decodeBits pr.2) :=
      decodeBitsComputable.comp Computable.snd
    have h_beq : Computable (fun pr : BitString × BitString =>
        (pr.1.length == decodeBits pr.2)) := by
      exact (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp (h_len.pair h_dec)
    have h_none : Computable (fun (_ : BitString × BitString) => (none : Option BitString)) :=
      Computable.const (α := BitString × BitString) (σ := Option BitString) none
    exact (Computable.cond h_beq (Computable.option_some.comp Computable.fst) h_none).of_eq
      (fun pr => by
        unfold exactLengthContextDecompressorOpt
        cases h : (pr.1.length == decodeBits pr.2) <;> rfl)
  exact Computable.ofOption h_opt

lemma exactLengthContextDecompressor_isPrefixMachine :
    IsPrefixMachine exactLengthContextDecompressor := by
  intro y p hp q hq hpre
  unfold exactLengthContextDecompressor at hp hq
  have hp' : exactLengthContextDecompressorOpt (p, y) ≠ none := by
    intro h
    change (Part.ofOption (exactLengthContextDecompressorOpt (p, y))).Dom at hp
    rw [h] at hp
    exact hp
  have hq' : exactLengthContextDecompressorOpt (q, y) ≠ none := by
    intro h
    change (Part.ofOption (exactLengthContextDecompressorOpt (q, y))).Dom at hq
    rw [h] at hq
    exact hq
  unfold exactLengthContextDecompressorOpt at hp' hq'
  cases hp_eq : (p.length == decodeBits y) <;> rw [hp_eq] at hp'
  · contradiction
  cases hq_eq : (q.length == decodeBits y) <;> rw [hq_eq] at hq'
  · contradiction
  have hplen : p.length = decodeBits y := beq_iff_eq.mp hp_eq
  have hqlen : q.length = decodeBits y := beq_iff_eq.mp hq_eq
  exact hpre.eq_of_length (by rw [hplen, hqlen])

lemma exactLengthContextDecompressor_produces
    (x y : BitString) (h : x.length = decodeBits y) :
    produces exactLengthContextDecompressor x y x := by
  unfold produces exactLengthContextDecompressor exactLengthContextDecompressorOpt
  rw [beq_iff_eq.mpr h]
  exact ⟨trivial, rfl⟩

/-- Given a binary encoding of `x.length` as condition, a prefix program can be
the literal string `x` up to the universal-machine overhead. -/
theorem KP_le_length_given_natBits_length (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, KP U x (Nat.bits x.length) ≤ x.length + (c : ENat) := by
  have hM : IsPrefixDecompressor exactLengthContextDecompressor :=
    ⟨exactLengthContextDecompressor_computable, exactLengthContextDecompressor_isPrefixMachine⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, ?_⟩
  intro x
  have hprod : produces exactLengthContextDecompressor x (Nat.bits x.length) x :=
    exactLengthContextDecompressor_produces x (Nat.bits x.length) (by simp [decodeBits_natBits])
  calc
    KP U x (Nat.bits x.length)
        ≤ KP exactLengthContextDecompressor x (Nat.bits x.length) + (c : ENat) := hc x (Nat.bits x.length)
    _ ≤ (x.length : ENat) + (c : ENat) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (KP_le_programLength_of_produces hprod) (c : ENat)

/-- Sharper self-delimiting length bound: `KPPlain U x ≤ x.length + 2 * log x.length + O(1)`. -/
theorem KPPlain_le_length_add_log (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, KPPlain U x ≤ x.length + 2 * (Nat.bits x.length).length + (c : ENat) := by
  obtain ⟨c_sub, h_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_cond, h_cond⟩ := KP_le_length_given_natBits_length U hU
  obtain ⟨c_nat, h_nat⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c_cond + c_nat + c_sub, ?_⟩
  intro x
  calc
    KPPlain U x
        ≤ KPPlain U (Nat.bits x.length) + KP U x (Nat.bits x.length)
            + (c_sub : ENat) := h_sub x (Nat.bits x.length)
    _ ≤ (2 * (Nat.bits x.length).length + (c_nat : ENat))
          + (x.length + (c_cond : ENat)) + (c_sub : ENat) := by
        gcongr
        · exact h_nat (Nat.bits x.length)
        · exact h_cond x
    _ = x.length + 2 * (Nat.bits x.length).length
          + ((c_cond + c_nat + c_sub : ℕ) : ENat) := by
        rw [Nat.cast_add, Nat.cast_add]
        simp [add_comm, add_left_comm, add_assoc]


/-- Natural-number prefix complexity bound: `KPPlain U (natCode n) ≤ 2 * log n + O(1)`. -/
theorem KPPlain_natCode_le_log (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, KPPlain U (natCode n) ≤ 2 * (Nat.bits n).length + (c : ENat) := by
  let bitsToNatCode : BitString → BitString := fun bs => natCode (decodeBits bs)
  have h_bitsToNatCode : Computable bitsToNatCode :=
    natCode_computable.comp decodeBitsComputable
  obtain ⟨c_map, h_map⟩ := KPPlain_map_le U hU bitsToNatCode h_bitsToNatCode
  obtain ⟨c_len, h_len⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c_len + c_map, ?_⟩
  intro n
  calc
    KPPlain U (natCode n)
        = KPPlain U (bitsToNatCode (Nat.bits n)) := by
            simp [bitsToNatCode, decodeBits_natBits]
    _ ≤ KPPlain U (Nat.bits n) + (c_map : ENat) := h_map (Nat.bits n)
    _ ≤ (2 * (Nat.bits n).length + (c_len : ENat)) + (c_map : ENat) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (h_len (Nat.bits n)) (c_map : ENat)
    _ = 2 * (Nat.bits n).length + ((c_len + c_map : ℕ) : ENat) := by
        rw [Nat.cast_add]
        ac_rfl

/-- SUV Theorem 61: `K(x, K(x)) = K(x) + O(1)`. -/
theorem KPPair_self_complexity_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x kx, HasPrefixComplexityValue U x kx → KPPair U x (natCode kx) ≤ kx + (c : ENat) := by
  obtain ⟨c_chain, h_chain⟩ := KPPair_chain_upper U hU
  obtain ⟨c_cond, h_cond⟩ := KP_map_self_le U hU decodeSecond decodeSecond_computable
  refine ⟨c_cond + c_chain, ?_⟩
  intro x kx hkx
  have hdec : decodeSecond (prefixComplexityContext x kx) = natCode kx := by
    exact decodeSecond_pairCode x (natCode kx)
  have h_cond' : KP U (natCode kx) (prefixComplexityContext x kx) ≤ (c_cond : ENat) := by
    simpa [prefixComplexityContext, decodeSecond_pairCode] using
      h_cond (prefixComplexityContext x kx)
  calc
    KPPair U x (natCode kx)
        ≤ KPPlain U x + KP U (natCode kx) (prefixComplexityContext x kx)
            + (c_chain : ENat) := h_chain x (natCode kx) kx hkx
    _ ≤ (kx : ENat) + (c_cond : ENat) + (c_chain : ENat) := by
        rw [← hkx]
        gcongr
    _ = (kx : ENat) + ((c_cond + c_chain : ℕ) : ENat) := by
        rw [Nat.cast_add]
        simp [add_assoc, add_comm]

theorem KPPlain_le_KPPair_self_complexity (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x kx, HasPrefixComplexityValue U x kx → (kx : ENat) ≤ KPPair U x (natCode kx) + (c : ENat) := by
  obtain ⟨c, h_left⟩ := KPPlain_left_le_KPPair U hU
  refine ⟨c, ?_⟩
  intro x kx hkx
  rw [hkx]
  exact h_left x (natCode kx)

/-- SUV Theorem 63(a): `K(x) ≤ |x| + K(|x|) + O(1)`. -/
theorem KPPlain_le_length_add_KPPlain_length (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, KPPlain U x ≤ x.length + KPPlain U (Nat.bits x.length) + (c : ENat) := by
  obtain ⟨c_sub, h_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_cond, h_cond⟩ := KP_le_length_given_natBits_length U hU
  refine ⟨c_cond + c_sub, ?_⟩
  intro x
  calc
    KPPlain U x
        ≤ KPPlain U (Nat.bits x.length) + KP U x (Nat.bits x.length)
            + (c_sub : ENat) := h_sub x (Nat.bits x.length)
    _ ≤ KPPlain U (Nat.bits x.length) + (x.length + (c_cond : ENat))
            + (c_sub : ENat) := by
        gcongr
        exact h_cond x
    _ = x.length + KPPlain U (Nat.bits x.length) + ((c_cond + c_sub : ℕ) : ENat) := by
        rw [Nat.cast_add]
        simp [add_comm, add_left_comm, add_assoc]

/-- Run a plain decompressor only on programs whose length is encoded in the
condition. The fixed-length guard is what makes the domain prefix-free in every
condition. -/
def plainProgramLengthContextDecompressor (V : Map) : Map := fun pr =>
  bif (pr.1.length == decodeBits pr.2) then V (pr.1, []) else Part.none

lemma plainProgramLengthContextDecompressor_computable (V : Map) (hV : isDecompressor V) :
    isDecompressor (plainProgramLengthContextDecompressor V) := by
  have h_len : Computable (fun pr : BitString × BitString => pr.1.length) :=
    Computable.list_length.comp Computable.fst
  have h_dec : Computable (fun pr : BitString × BitString => decodeBits pr.2) :=
    decodeBitsComputable.comp Computable.snd
  have h_guard : Computable (fun pr : BitString × BitString =>
      (pr.1.length == decodeBits pr.2)) :=
    (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp (h_len.pair h_dec)
  have h_call : Partrec (fun pr : BitString × BitString => V (pr.1, [])) :=
    Partrec.comp hV (Computable.fst.pair (Computable.const []))
  exact (Partrec.cond h_guard h_call Partrec.none).of_eq (fun pr => by
    unfold plainProgramLengthContextDecompressor
    cases h : (pr.1.length == decodeBits pr.2) <;> rfl)

lemma plainProgramLengthContextDecompressor_isPrefixMachine (V : Map) :
    IsPrefixMachine (plainProgramLengthContextDecompressor V) := by
  intro y p hp q hq hpre
  change (plainProgramLengthContextDecompressor V (p, y)).Dom at hp
  change (plainProgramLengthContextDecompressor V (q, y)).Dom at hq
  unfold plainProgramLengthContextDecompressor at hp hq
  cases hp_eq : (p.length == decodeBits y) <;> rw [hp_eq] at hp
  · exact False.elim hp
  cases hq_eq : (q.length == decodeBits y) <;> rw [hq_eq] at hq
  · exact False.elim hq
  have hplen : p.length = decodeBits y := beq_iff_eq.mp hp_eq
  have hqlen : q.length = decodeBits y := beq_iff_eq.mp hq_eq
  exact hpre.eq_of_length (by rw [hplen, hqlen])

lemma plainProgramLengthContextDecompressor_produces
    {V : Map} {p x y : BitString} (hprod : produces V p [] x)
    (hlen : p.length = decodeBits y) :
    produces (plainProgramLengthContextDecompressor V) p y x := by
  unfold produces plainProgramLengthContextDecompressor
  rw [beq_iff_eq.mpr hlen]
  exact hprod

/-- If `kC` is the exact plain complexity of `x`, then `x` has conditional prefix
complexity at most `kC + O(1)` given the binary code of `kC`. -/
theorem KP_le_plainK_value_given_value_code (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (kC : ℕ), plainK V x = (kC : ENat) →
      KP U x (Nat.bits kC) ≤ (kC : ENat) + (c : ENat) := by
  have hM : IsPrefixDecompressor (plainProgramLengthContextDecompressor V) :=
    ⟨plainProgramLengthContextDecompressor_computable V hV.1,
      plainProgramLengthContextDecompressor_isPrefixMachine V⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, ?_⟩
  intro x kC hfin
  have hK_ne_top : KP V x [] ≠ ⊤ := by
    change plainK V x ≠ ⊤
    rw [hfin]
    exact ENat.coe_ne_top kC
  obtain ⟨p, hp, hplen⟩ := exists_program_of_KP_ne_top (M := V) (x := x) (y := []) hK_ne_top
  have hp_len_nat : p.length = kC := by
    have : (p.length : ENat) = (kC : ENat) := by
      rw [hplen]
      exact hfin
    exact_mod_cast this
  have hprod : produces (plainProgramLengthContextDecompressor V) p (Nat.bits kC) x :=
    plainProgramLengthContextDecompressor_produces hp (by simp [hp_len_nat, decodeBits_natBits])
  calc
    KP U x (Nat.bits kC)
        ≤ KP (plainProgramLengthContextDecompressor V) x (Nat.bits kC) + (c : ENat) :=
          hc x (Nat.bits kC)
    _ ≤ (kC : ENat) + (c : ENat) := by
        have hp_bound := KP_le_programLength_of_produces hprod
        simpa [programLength, hp_len_nat, add_comm, add_left_comm, add_assoc] using
          add_le_add_right hp_bound (c : ENat)

/-- SUV Theorem 63(b): counting bound. Among the strings of length `n`, the number
whose prefix complexity is below `n + K(n) - c - d` is at most `2^{n-d}`.

The proof is a Kraft/coding argument: each string in the bad set carries
complexity weight at least `2^{-(n+K(n)-c-d)}`, while the total weight of all
length-`n` strings is at most `2^{c}·2^{-K(n)}` by the length-marginal coding
bound `sum_complexityWeight_stringsOfLength_le`. -/
theorem card_KPPlain_lt_length_add_KPPlain_sub_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n d kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn →
    (Finset.filter (fun x : BitString =>
        KPPlain U x + (d : ENat) < (n : ENat) + (kn : ENat) - (c : ENat))
      (stringsOfLength n)).card ≤ (2 : ℕ) ^ (n - d) := by
  obtain ⟨c, hc⟩ := sum_complexityWeight_stringsOfLength_le U hU
  refine ⟨c, fun n d kn hkn => ?_⟩
  set A := Finset.filter
    (fun x : BitString => KPPlain U x + (d : ENat) < (n : ENat) + (kn : ENat) - (c : ENat))
    (stringsOfLength n) with hA
  -- The total weight of length-`n` strings, from the crux lemma.
  have htot : (∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x))
        ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn := hc n kn hkn
  -- The threshold, as a (truncated) natural exponent.
  set T : ℕ := (n + kn) - c with hT
  -- `(n:ENat)+(kn:ENat)-(c:ENat) = (T : ENat)`
  have hTcast : (n : ENat) + (kn : ENat) - (c : ENat) = (T : ENat) := by
    rw [hT]; push_cast; rfl
  by_cases hcase : n + kn ≤ c
  · -- The threshold is `0`, so the bad set is empty.
    have hT0 : T = 0 := by rw [hT]; omega
    have hempty : A = ∅ := by
      rw [hA]
      apply Finset.filter_eq_empty_iff.mpr
      intro x _
      rw [hTcast, hT0, Nat.cast_zero]
      exact not_lt_bot
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · -- The interesting case: `c < n + kn`.
    have hcle : c ≤ n + kn := (not_le.mp hcase).le
    -- Key pointwise lower bound: each `x ∈ A` has weight `≥ 2^{-T}·2^{d}`.
    have hpt : ∀ x ∈ A, (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d
        ≤ complexityWeight (KPPlain U x) := by
      intro x hx
      rw [hA, Finset.mem_filter] at hx
      have hlt := hx.2
      rw [hTcast] at hlt
      have hle : KPPlain U x + (d : ENat) ≤ (T : ENat) := le_of_lt hlt
      have hmono := complexityWeight_le_of_le hle
      rw [complexityWeight_add_nat, complexityWeight_coe] at hmono
      -- hmono : (2⁻¹)^T ≤ complexityWeight (KPPlain U x) * (2⁻¹)^d
      have hdd : (2 : ℝ≥0∞)⁻¹ ^ d * (2 : ℝ≥0∞) ^ d = 1 := by
        rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
      calc
        (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d
            ≤ (complexityWeight (KPPlain U x) * (2 : ℝ≥0∞)⁻¹ ^ d) * (2 : ℝ≥0∞) ^ d := by
              gcongr
        _ = complexityWeight (KPPlain U x) * ((2 : ℝ≥0∞)⁻¹ ^ d * (2 : ℝ≥0∞) ^ d) := by ring
        _ = complexityWeight (KPPlain U x) := by rw [hdd, mul_one]
    -- The cardinality times the per-element weight bounds the total weight.
    have hcard : (A.card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d)
        ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn := by
      have hsub : A ⊆ stringsOfLength n := Finset.filter_subset _ _
      calc
        (A.card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d)
            = ∑ _x ∈ A, ((2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ A, complexityWeight (KPPlain U x) := Finset.sum_le_sum hpt
        _ ≤ ∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x) :=
              Finset.sum_le_sum_of_subset hsub
        _ ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn := htot
    -- Cancel the per-element weight to get `card ≤ 2^n · 2^{-d}`.
    have hfin : (A.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ d := by
      have hstep := mul_le_mul_left hcard ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d)
      have hcancel : (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d *
          ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d) = 1 := by
        have e1 : (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ T = 1 := by
          rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
        have e2 : (2 : ℝ≥0∞) ^ d * (2 : ℝ≥0∞)⁻¹ ^ d = 1 := by
          rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
        calc
          (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d * ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d)
              = ((2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ T) * ((2 : ℝ≥0∞) ^ d * (2 : ℝ≥0∞)⁻¹ ^ d) := by ring
          _ = 1 := by rw [e1, e2, one_mul]
      have hRHS : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn * ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d)
          = (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ d := by
        have hcT : c + T = n + kn := by rw [hT]; omega
        have e3 : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞) ^ T = (2 : ℝ≥0∞) ^ (n + kn) := by
          rw [← pow_add, hcT]
        have e4 : (2 : ℝ≥0∞) ^ (n + kn) * (2 : ℝ≥0∞)⁻¹ ^ kn = (2 : ℝ≥0∞) ^ n := by
          rw [pow_add, mul_assoc,
            show (2 : ℝ≥0∞) ^ kn * (2 : ℝ≥0∞)⁻¹ ^ kn = 1 from by
              rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow],
            mul_one]
        calc
          (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn * ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d)
              = ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞) ^ T) * (2 : ℝ≥0∞)⁻¹ ^ kn * (2 : ℝ≥0∞)⁻¹ ^ d := by ring
          _ = (2 : ℝ≥0∞) ^ (n + kn) * (2 : ℝ≥0∞)⁻¹ ^ kn * (2 : ℝ≥0∞)⁻¹ ^ d := by rw [e3]
          _ = (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ d := by rw [e4]
      rw [mul_assoc, hcancel, mul_one, hRHS] at hstep
      exact hstep
    -- Convert the `ℝ≥0∞` bound to the `ℕ` cardinality bound.
    have hcast : (A.card : ℝ≥0∞) ≤ ((2 ^ (n - d) : ℕ) : ℝ≥0∞) :=
      le_trans hfin (two_pow_mul_inv_pow_le_cast_pow_sub n d)
    exact_mod_cast hcast

/-- SUV Theorem 65: `K(x) ≤ C(x) + K(C(x)) + O(1)`. -/
theorem KPPlain_le_plainK_add_KPPlain_plainK (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (kC : ℕ), plainK V x = (kC : ENat) →
      KPPlain U x ≤ (kC : ENat) + KPPlain U (Nat.bits kC) + (c : ENat) := by
  obtain ⟨c_sub, h_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_cond, h_cond⟩ := KP_le_plainK_value_given_value_code U V hU hV
  refine ⟨c_cond + c_sub, ?_⟩
  intro x kC hfin
  calc
    KPPlain U x
        ≤ KPPlain U (Nat.bits kC) + KP U x (Nat.bits kC) + (c_sub : ENat) :=
          h_sub x (Nat.bits kC)
    _ ≤ KPPlain U (Nat.bits kC) + ((kC : ENat) + (c_cond : ENat)) + (c_sub : ENat) := by
        gcongr
        exact h_cond x kC hfin
    _ = (kC : ENat) + KPPlain U (Nat.bits kC) + ((c_cond + c_sub : ℕ) : ENat) := by
        rw [Nat.cast_add]
        simp [add_comm, add_left_comm, add_assoc]

end Kolmogorov
