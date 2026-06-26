/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.TotalCountingBound.Basic

namespace Kolmogorov

open scoped ENNReal

/-! ### The counting lower-semicomputable function (SUV Theorem 64 upper bound)

The genuinely hard half of Theorem 64 needs a prefix machine that assigns the
output `Nat.bits n` a weight of at least (a constant multiple of) `N_n · 2^{-n}`,
where `N_n = #{x : K(x) ≤ n}`.  We obtain it from the abstract Kraft–Chaitin
realization engine `kraftChaitin_realization_bound` applied to the lower-
semicomputable *counting function*

  `countingF c (Nat.bits n) [] = m_n · 2^{-n}`,

where `m_n` is the number of programs of length `≤ n` that halt under `U`.  Two
elementary facts make this work:

* `N_n ≤ m_n` (distinct outputs have distinct programs), so the count of any set
  `A` of low-complexity strings is bounded by `m_n` — this gives the *lower* bound
  `|A| · 2^{-n} ≤ countingF c (Nat.bits n) []` (`countingF_ge_card`);
* `∑_n m_n · 2^{-n} = 2 · ∑_{p halting} 2^{-|p|} ≤ 2` by the Kraft inequality on
  `U`'s prefix-free domain (`countingF_tsum_le`), so the engine applies at
  subnormalization level `d = 1`.

Counting programs *with multiplicity* (rather than distinct outputs) is what keeps
the staged approximation trivially computable, mirroring `aprioriApprox`. -/

section CountingLSC

/-- Stage-`s` count of programs of length `≤ n` whose run under code `c` (on empty
context) halts within fuel `s`.  Written as a `map`-`sum` (one `1` per halting
program) so the computability proof mirrors `aprioriApprox_computable`. -/
def countingApprox (c : Nat.Partrec.Code) (s n : ℕ) : ℕ :=
  ((boundedPrograms n).map
    (fun p => if (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))).isSome
      then 1 else 0)).sum

/-- The staged dyadic numerator for the counting function: on a canonical output
`Nat.bits n` with empty context it is `countingApprox c s n · 2^{s-n}` (whose
dyadic value `·/2^s` is `countingApprox c s n · 2^{-n}`), and `0` otherwise. -/
def countingNum (c : Nat.Partrec.Code) (s : ℕ) (out ctx : BitString) : ℕ :=
  if ctx = [] ∧ Nat.bits (decodeBits out) = out ∧ decodeBits out ≤ s then
    countingApprox c s (decodeBits out) * 2 ^ (s - decodeBits out)
  else 0

/-- The counting lower-semicomputable function, defined directly as the supremum
of its staged dyadic approximation. -/
noncomputable def countingF (c : Nat.Partrec.Code) (out ctx : BitString) : ℝ≥0∞ :=
  ⨆ s, dyadicValue (countingNum c s out ctx) s

/-
`countingApprox` is monotone in the fuel `s`: more fuel only makes more
programs halt.
-/
lemma countingApprox_mono (c : Nat.Partrec.Code) (s n : ℕ) :
    countingApprox c s n ≤ countingApprox c (s + 1) n := by
  apply List.sum_le_sum
  intro p _
  by_cases h₁ :
      (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))).isSome = true
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h₁
    have h_eval := Nat.Partrec.Code.evaln_mono (Nat.le_succ s) hx
    have h₂ :
        (Nat.Partrec.Code.evaln (s + 1) c
          (Encodable.encode (p, ([] : BitString)))).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨x, h_eval⟩
    have h₁' :
        (Nat.Partrec.Code.evaln s c (Nat.pair (Encodable.encode p) 0)).isSome = true := by
      simpa using h₁
    have h₂' :
        (Nat.Partrec.Code.evaln (s + 1) c (Nat.pair (Encodable.encode p) 0)).isSome = true := by
      simpa using h₂
    simp [h₁', h₂']
  · have h₁' :
        ¬ (Nat.Partrec.Code.evaln s c (Nat.pair (Encodable.encode p) 0)).isSome = true := by
      simpa using h₁
    simp [h₁']

/-
Closed form for the dyadic value of the staged numerator.
-/
lemma dyadicValue_countingNum (c : Nat.Partrec.Code) (s : ℕ) (out ctx : BitString) :
    dyadicValue (countingNum c s out ctx) s
      = if ctx = [] ∧ Nat.bits (decodeBits out) = out ∧ decodeBits out ≤ s
        then (countingApprox c s (decodeBits out) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (decodeBits out)
        else 0 := by
  unfold dyadicValue countingNum
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := h
    simp_all only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_assoc]
    have h_pow : (2 : ℝ≥0∞) ^ s = (2 : ℝ≥0∞) ^ (s - decodeBits out) * (2 : ℝ≥0∞) ^ decodeBits out := by rw [← pow_add, Nat.sub_add_cancel h3]
    rw [h_pow]
    norm_num [ENNReal.mul_inv, ENNReal.inv_pow]
    simp only [← mul_assoc, ← mul_pow]
    rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
    norm_num
  · simp [div_eq_mul_inv]

/-- The dyadic value of the staged numerator at a canonical output `Nat.bits n`
(with enough fuel `n ≤ s`). -/
lemma dyadicValue_countingNum_bits (c : Nat.Partrec.Code) {s n : ℕ} (hs : n ≤ s) :
    dyadicValue (countingNum c s (Nat.bits n) []) s
      = (countingApprox c s n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [dyadicValue_countingNum,
    if_pos ⟨rfl, by rw [decodeBits_natBits], by rw [decodeBits_natBits]; exact hs⟩,
    decodeBits_natBits]

/-- The dyadic value of the staged numerator is monotone in the stage. -/
lemma countingNum_dyadic_mono (c : Nat.Partrec.Code) (s : ℕ) (out ctx : BitString) :
    dyadicValue (countingNum c s out ctx) s
      ≤ dyadicValue (countingNum c (s + 1) out ctx) (s + 1) := by
  rw [dyadicValue_countingNum, dyadicValue_countingNum]
  by_cases h : ctx = [] ∧ Nat.bits (decodeBits out) = out ∧ decodeBits out ≤ s
  · obtain ⟨h1, h2, h3⟩ := h
    rw [if_pos ⟨h1, h2, h3⟩, if_pos ⟨h1, h2, Nat.le_succ_of_le h3⟩]
    gcongr
    exact_mod_cast countingApprox_mono c s (decodeBits out)
  · rw [if_neg h]
    exact zero_le

/-
`countingApprox` is computable in `(s, n)`.  Mirrors `aprioriApprox_computable`.
-/
lemma countingApprox_computable (c : Nat.Partrec.Code) :
    Computable (fun q : ℕ × ℕ => countingApprox c q.1 q.2) := by
  convert Primrec.to_comp _;
  unfold countingApprox;
  have h_countingApprox_primrec : Primrec (fun (q : ℕ × ℕ) => List.map (fun p => if (Nat.Partrec.Code.evaln q.1 c (Encodable.encode (p, ([] : BitString)))).isSome then 1 else 0) (boundedPrograms q.2)) := by
    refine Primrec.list_map ?_ ?_;
    · exact Primrec.comp ( primrec_boundedPrograms ) ( Primrec.snd );
    · have h_evaln_computable : Primrec (fun q : ℕ × BitString => (Nat.Partrec.Code.evaln q.1 c (Encodable.encode (q.2, ([] : BitString)))).isSome) := by
        have h_evaln_computable : Primrec (fun q : ℕ × BitString => Nat.Partrec.Code.evaln q.1 c (Encodable.encode (q.2, ([] : BitString)))) := by
          have := Nat.Partrec.Code.primrec_evaln;
          convert this.comp ( Primrec.pair ( Primrec.fst ) ( Primrec.const c ) |> Primrec.pair <| Primrec.comp ( show Primrec ( fun q : BitString => Encodable.encode ( q, [] ) ) from ?_ ) Primrec.snd ) using 1;
          exact Primrec.encode.comp ( Primrec.pair ( Primrec.id ) ( Primrec.const [] ) );
        exact Primrec.option_isSome.comp h_evaln_computable;
      have h_if_computable : Primrec (fun q : Bool => if q then 1 else 0) := by
        convert Primrec.cond _ _ _;
        rotate_left;
        exact fun x => x;
        · exact Primrec.id;
        · exact Primrec.const 1;
        · exact Primrec.const 0;
        · cases ‹_› <;> rfl;
      exact h_if_computable.comp ( h_evaln_computable.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) );
  convert Primrec.comp ( show Primrec ( fun l : List ℕ => List.sum l ) from ?_ ) h_countingApprox_primrec using 1;
  convert Primrec.list_foldr _ _ _ using 1;
  rotate_left;
  exact ℕ;
  exact inferInstance;
  exact fun l => l;
  exact fun _ => 0;
  exact fun l p => p.1 + p.2;
  · exact Primrec.id;
  · exact Primrec.const 0;
  · exact Primrec.nat_add.comp ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.snd.comp ( Primrec.snd ) );
  · exact funext fun l => by induction l <;> simp +decide [ * ] ;

/-
The guard predicate of `countingNum` is a computable predicate.
-/
lemma countingNum_guard_computable :
    Computable (fun q : ℕ × BitString × BitString =>
      decide (q.2.2 = [] ∧ Nat.bits (decodeBits q.2.1) = q.2.1 ∧ decodeBits q.2.1 ≤ q.1)) := by
  have h_computable : Computable (fun q : ℕ × BitString × BitString => decide (q.1 ≥ decodeBits q.2.1)) ∧ Computable (fun q : ℕ × BitString × BitString => decide (q.2.1 = Nat.bits (decodeBits q.2.1))) ∧ Computable (fun q : ℕ × BitString × BitString => decide (q.2.2 = [])) := by
    constructor;
    · have h_computable : Computable (fun q : ℕ × BitString => decide (q.1 ≥ decodeBits q.2)) := by
        have h_decode : Computable (fun q : BitString => decodeBits q) := by
          convert decodeBitsComputable using 1
        have h_computable : Computable (fun q : ℕ × ℕ => decide (q.1 ≥ q.2)) := by
          have h_computable : Computable (fun q : ℕ × ℕ => decide (q.1 ≤ q.2)) := by
            have h_computable : Primrec (fun q : ℕ × ℕ => decide (q.1 ≤ q.2)) := by
              convert Primrec.nat_le using 1;
              constructor <;> intro h <;> simp_all +decide [ PrimrecRel ];
              · convert h using 1;
                constructor <;> intro h <;> rw [ PrimrecPred ] at * <;> aesop;
              · grind +suggestions
            exact h_computable.to_comp;
          convert h_computable.comp ( Computable.snd.pair Computable.fst ) using 1;
        convert h_computable.comp ( Computable.pair ( Computable.fst ) ( h_decode.comp ( Computable.snd ) ) ) using 1;
      convert h_computable.comp ( Computable.fst.pair ( Computable.fst.comp Computable.snd ) ) using 1;
    · constructor;
      · have h_eq : Computable (fun q : BitString × BitString => decide (q.1 = q.2)) := by
          have h_eq_pred : PrimrecPred (fun q : BitString × BitString => q.1 = q.2) :=
            Primrec.eq
          obtain ⟨_, h_eq⟩ := h_eq_pred
          exact Computable.of_eq h_eq.to_comp (fun q => by
            by_cases h : q.1 = q.2 <;> simp [h])
        convert h_eq.comp ( Computable.pair ( Computable.fst.comp ( Computable.snd ) ) ( natBitsComputable.comp ( decodeBitsComputable.comp ( Computable.fst.comp ( Computable.snd ) ) ) ) ) using 1;
      · have h_decide_empty : Computable (fun q : BitString => decide (q = [])) := by
          convert Computable.of_eq _ _;
          exact fun n => n.isEmpty;
          · convert Computable.nat_casesOn _ _ _ using 1;
            rotate_left;
            exact fun n => n.length;
            exact fun _ => Bool.true;
            exact fun _ _ => Bool.false;
            · exact Computable.list_length;
            · exact Computable.const Bool.true;
            · exact Computable.const Bool.false;
            · ext ( _ | _ ) <;> simp +decide;
          · grind;
        exact h_decide_empty.comp ( Computable.snd.comp Computable.snd );
  convert Computable.cond ( h_computable.1 ) ( Computable.cond ( h_computable.2.2 ) ( h_computable.2.1 ) ( Computable.const Bool.false ) ) ( Computable.const Bool.false ) using 1;
  grind +revert

/-
The staged numerator is computable in `(s, out, ctx)`.
-/
lemma countingNum_computable (c : Nat.Partrec.Code) :
    Computable (fun q : ℕ × BitString × BitString => countingNum c q.1 q.2.1 q.2.2) := by
  unfold countingNum;
  convert Computable.cond _ _ _;
  rotate_left;
  exact fun q => q.2.2 = [] ∧ Nat.bits ( decodeBits q.2.1 ) = q.2.1 ∧ decodeBits q.2.1 ≤ q.1;
  · convert countingNum_guard_computable using 1;
  · convert Computable.comp ( show Computable ( fun q : ℕ × ℕ => countingApprox c q.1 q.2 * 2 ^ ( q.1 - q.2 ) ) from ?_ ) ( show Computable ( fun q : ℕ × BitString × BitString => ( q.1, decodeBits q.2.1 ) ) from ?_ ) using 1;
    · have h_computable : Computable (fun q : ℕ × ℕ => countingApprox c q.1 q.2) ∧ Computable (fun q : ℕ × ℕ => 2 ^ (q.1 - q.2)) := by
        constructor;
        · exact countingApprox_computable c;
        · convert Computable.comp ( show Computable ( fun n => 2 ^ n ) from ?_ ) ( show Computable ( fun q : ℕ × ℕ => q.1 - q.2 ) from ?_ ) using 1;
          · exact Computable.of_eq ( Primrec.to_comp ( Kolmogorov.Computability.primrec_two_pow ) ) fun n => rfl;
          · convert Primrec.to_comp ( show Primrec ( fun q : ℕ × ℕ => q.1 - q.2 ) from ?_ ) using 1;
            exact Primrec.nat_sub.comp ( Primrec.fst ) ( Primrec.snd );
      convert Computable.comp ( show Computable ( fun q : ℕ × ℕ => q.1 * q.2 ) from ?_ ) ( h_computable.1.pair h_computable.2 ) using 1;
      convert Primrec.to_comp ( show Primrec ( fun q : ℕ × ℕ => q.1 * q.2 ) from ?_ ) using 1;
      exact Primrec.nat_mul.comp ( Primrec.fst ) ( Primrec.snd );
    · exact Computable.pair ( Computable.fst ) ( decodeBitsComputable.comp ( Computable.fst.comp ( Computable.snd ) ) );
  · exact Computable.const 0;
  · grind

/-- The counting function is lower-semicomputable. -/
lemma countingF_isLSC (c : Nat.Partrec.Code) : IsLSC (countingF c) :=
  ⟨countingNum c, countingNum_dyadic_mono c, fun _ _ => rfl, countingNum_computable c⟩

/-
**Counting injection.**  For a finite set `A` of strings all of complexity
`≤ n`, a large enough fuel `s ≥ n` makes `countingApprox c s n` at least `|A|`:
each `x ∈ A` has a distinct halting program of length `≤ n`, and all of them halt
within a common fuel bound.
-/
lemma countingApprox_ge_card (U : Map) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
    (n : ℕ) (A : Finset BitString) (hA : ∀ x ∈ A, KPPlain U x ≤ (n : ENat)) :
    ∃ s, n ≤ s ∧ A.card ≤ countingApprox c s n := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, n ≤ s ∧ ∀ x ∈ A, ∃ p : BitString, p.length ≤ n ∧ produces U p [] x ∧ (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString))) = some (Encodable.encode x)) := by
    have h_exists_p : ∀ x ∈ A, ∃ p : BitString, p.length ≤ n ∧ produces U p [] x := by
      exact fun x hx => (condKLeIff U x [] n).mp (hA x hx);
    choose! p hp₁ hp₂ using h_exists_p;
    obtain ⟨s, hs⟩ : ∃ s : ℕ, ∀ x ∈ A, ∃ k : ℕ, k ≤ s ∧ (Nat.Partrec.Code.evaln k c (Encodable.encode (p x, ([] : BitString))) = some (Encodable.encode x)) := by
      have h_exists_k : ∀ x ∈ A, ∃ k : ℕ, (Nat.Partrec.Code.evaln k c (Encodable.encode (p x, ([] : BitString))) = some (Encodable.encode x)) := by
        intro x hx; specialize hp₂ x hx; rw [ produces_iff_evaln c hc ] at hp₂; aesop;
      choose! k hk using h_exists_k;
      exact ⟨ Finset.sup A k, fun x hx => ⟨ k x, Finset.le_sup ( f := k ) hx, hk x hx ⟩ ⟩;
    exact ⟨ s + n, by linarith, fun x hx => by obtain ⟨ k, hk₁, hk₂ ⟩ := hs x hx; exact ⟨ p x, hp₁ x hx, hp₂ x hx, by simpa [ hk₂ ] using Nat.Partrec.Code.evaln_mono ( by linarith : k ≤ s + n ) hk₂ ⟩ ⟩;
  obtain ⟨pOf, hpOf⟩ : ∃ pOf : BitString → BitString, (∀ x ∈ A, pOf x ∈ boundedPrograms n ∧ produces U (pOf x) [] x ∧ (Nat.Partrec.Code.evaln s c (Encodable.encode (pOf x, ([] : BitString))) = some (Encodable.encode x))) ∧ (∀ x y : BitString, x ∈ A → y ∈ A → pOf x = pOf y → x = y) := by
    choose! p hp using hs.2;
    refine ⟨ p, ?_, ?_ ⟩ <;> simp_all +decide [ mem_boundedPrograms_iff ];
    intro x y hx hy hxy; have := hp x hx; have := hp y hy; simp_all +decide [ produces ] ;
  refine ⟨ s, hs.1, ?_ ⟩;
  have h_card : (Finset.image pOf A).card ≤ ((boundedPrograms n).filter (fun p => (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))).isSome)).length := by
    have h_card : (Finset.image pOf A).card ≤ (List.toFinset (List.filter (fun p => (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))).isSome) (boundedPrograms n))).card := by
      refine Finset.card_le_card ?_;
      simp_all +decide [ Finset.subset_iff ];
    exact h_card.trans ( List.toFinset_card_le _ );
  convert h_card using 1;
  · rw [ Finset.card_image_of_injOn fun x hx y hy hxy => hpOf.2 x y hx hy hxy ];
  · unfold countingApprox; simp +decide;
    induction ( boundedPrograms n ) <;> simp +decide [ * ];
    grind

/-- **Lower bound for the counting function.**  For any finite set `A` of strings
all of complexity `≤ n`, the counting function at `Nat.bits n` dominates
`|A| · 2^{-n}`. -/
lemma countingF_ge_card (U : Map) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
    (n : ℕ) (A : Finset BitString) (hA : ∀ x ∈ A, KPPlain U x ≤ (n : ENat)) :
    (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n ≤ countingF c (Nat.bits n) [] := by
  obtain ⟨s, hns, hcard⟩ := countingApprox_ge_card U c hc n A hA
  calc
    (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n
        ≤ (countingApprox c s n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n := by
          gcongr
    _ = dyadicValue (countingNum c s (Nat.bits n) []) s := (dyadicValue_countingNum_bits c hns).symm
    _ ≤ countingF c (Nat.bits n) [] := by
          unfold countingF
          exact le_iSup (fun s => dyadicValue (countingNum c s (Nat.bits n) []) s) s

/-- Total `2^{-(decodeBits out)}`-mass of programs of length `≤ decodeBits out` that
halt under `U`, attached to a canonical output `out = Nat.bits (decodeBits out)`. -/
noncomputable def haltMass (U : Map) (out : BitString) : ℝ≥0∞ := by
  classical
  exact if Nat.bits (decodeBits out) = out then
    ∑' p : BitString,
      if p.length ≤ decodeBits out ∧ (U (p, ([] : BitString))).Dom
        then (2 : ℝ≥0∞)⁻¹ ^ (decodeBits out) else 0
  else 0

/-
The counting function is pointwise dominated by `haltMass` (in the empty
context): at each stage at most the halting programs of length `≤ n` are counted.
-/
lemma countingF_le_haltMass (U : Map) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
    (out : BitString) :
    countingF c out [] ≤ haltMass U out := by
  classical
  refine iSup_le fun s => ?_;
  by_cases hcanon : Nat.bits (decodeBits out) = out <;> by_cases hle : decodeBits out ≤ s <;> simp +decide [ dyadicValue_countingNum, hcanon, hle, haltMass ];
  have h_card : (countingApprox c s (decodeBits out) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (decodeBits out) = ∑ p ∈ (boundedPrograms (decodeBits out)).toFinset.filter (fun p => (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))).isSome), (2 : ℝ≥0∞)⁻¹ ^ (decodeBits out) := by
    simp +decide [countingApprox];
    rw [ Finset.card_filter ];
    rw [ List.sum_toFinset ] ; aesop;
    exact boundedPrograms_nodup _;
  refine h_card ▸ le_trans ?_
    ( ENNReal.sum_le_tsum
        (f := fun p => if p.length ≤ decodeBits out ∧ (U (p, ([] : BitString))).Dom
          then (2 : ℝ≥0∞)⁻¹ ^ (decodeBits out) else 0)
        ((boundedPrograms (decodeBits out)).toFinset.filter
          (fun p => (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))).isSome)) );
  refine Finset.sum_le_sum ?_;
  intro p hp; split_ifs <;> simp_all +decide [ Part.dom_iff_mem ] ;
  obtain ⟨ x, hx ⟩ := Option.isSome_iff_exists.mp hp.2;
  have := Nat.Partrec.Code.evaln_sound hx; simp_all +decide;
  obtain ⟨ a, ha₁, ha₂ ⟩ := this; specialize ‹p.length ≤ decodeBits out → ∀ x : BitString, x ∉ U ( p, [] ) › ( by simpa using mem_boundedPrograms_iff p ( decodeBits out ) |>.1 hp ) a; aesop;

open Classical in
/-- **Kraft inequality on the halting domain.**  For a prefix decompressor, the
sum of program weights over the halting domain (empty context) is `≤ 1`. -/
lemma tsum_domain_progWeight_le_one (U : Map) (hU : IsPrefixDecompressor U) :
    (∑' p : BitString, if (U (p, ([] : BitString))).Dom then progWeight p else 0) ≤ 1 := by
  have h_sum : (∑' x, aprioriMeasure U x []) ≤ 1 := by
    convert tsum_aprioriMeasure_le_one U [] hU.isPrefixMachine using 1;
  convert h_sum using 1
  have h_sum_eq : (∑' x, aprioriMeasure U x []) = (∑' p, ∑' x, if produces U p [] x then progWeight p else 0) := by
    simp only [aprioriMeasure]
    rw [ENNReal.tsum_comm]
  generalize_proofs at *;
  convert h_sum_eq.symm using 3;
  split_ifs <;> simp_all +decide [ produces ];
  · rename_i p hp;
    rw [ tsum_eq_single ( U ( p, [] ) |> Part.get <| hp ) ] <;> simp +contextual;
    · exact fun h => False.elim <| h <| Part.get_mem _;
    · exact fun x hx₁ hx₂ => False.elim <| hx₁ <| Part.mem_unique hx₂ <| Part.get_mem _;
  · convert tsum_zero.symm;
    exact if_neg fun h => ‹¬ ( U ( _, _ ) ).Dom› <| Part.dom_iff_mem.mpr <| by tauto;

open Classical in
/-- The value of `haltMass` at a canonical output `Nat.bits n`. -/
lemma haltMass_natBits (U : Map) (n : ℕ) :
    haltMass U (Nat.bits n)
      = ∑' p : BitString, if p.length ≤ n ∧ (U (p, ([] : BitString))).Dom
          then (2 : ℝ≥0∞)⁻¹ ^ n else 0 := by
  -- By definition of `haltMass`, we know that `haltMass U (Nat.bits n)` is equal to the sum of the weights of all programs that produce `n`.
  unfold haltMass
  simp [decodeBits_natBits]

/-
The total `haltMass` is supported on canonical outputs, so it reindexes along
`Nat.bits`.
-/
lemma tsum_haltMass_eq_tsum_nat (U : Map) :
    (∑' out : BitString, haltMass U out) = ∑' n : ℕ, haltMass U (Nat.bits n) := by
  convert ( Function.Injective.tsum_eq ( show Function.Injective Nat.bits from ?_ ) ?_ ) |> Eq.symm using 1;
  · exact Function.LeftInverse.injective ( show Function.LeftInverse decodeBits Nat.bits from fun n => decodeBits_natBits n );
  · intro x hx; contrapose! hx; unfold haltMass; aesop;

/-
Geometric tail sum: `∑_{n ≥ m} 2^{-n} = 2 · 2^{-m}`.
-/
lemma tsum_ge_pow (m : ℕ) :
    (∑' n : ℕ, if m ≤ n then (2 : ℝ≥0∞)⁻¹ ^ n else 0) = 2 * (2 : ℝ≥0∞)⁻¹ ^ m := by
  -- We can factor out $2^{-m}$ from the sum.
  have h_factor : (∑' n, if m ≤ n then (2 : ℝ≥0∞)⁻¹ ^ n else 0) = (∑' n, (2 : ℝ≥0∞)⁻¹ ^ (n + m)) := by
    rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
    use fun x => x.val - m;
    · intro a₁ a₂ h; rw [ tsub_left_inj ] at h <;> aesop;
    · intro x hx; use ⟨ x + m, by aesop ⟩ ; aesop;
    · aesop;
  simp_all +decide [ pow_add, ENNReal.tsum_mul_right ]

/-- **Total-mass bound for `haltMass`.**  `∑_out haltMass U out = 2 · ∑_{p halting}
2^{-|p|} ≤ 2`. -/
lemma tsum_haltMass_le (U : Map) (hU : IsPrefixDecompressor U) :
    (∑' out : BitString, haltMass U out) ≤ 2 := by
  classical
  rw [tsum_haltMass_eq_tsum_nat U]
  simp_rw [haltMass_natBits U]
  rw [ENNReal.tsum_comm]
  have hinner : ∀ p : BitString,
      (∑' n : ℕ, if p.length ≤ n ∧ (U (p, ([] : BitString))).Dom then (2 : ℝ≥0∞)⁻¹ ^ n else 0)
        = 2 * (if (U (p, ([] : BitString))).Dom then progWeight p else 0) := by
    intro p
    by_cases hdom : (U (p, ([] : BitString))).Dom
    · simp only [hdom, and_true, if_true]
      rw [tsum_ge_pow p.length, progWeight]
    · simp [hdom]
  simp_rw [hinner]
  rw [ENNReal.tsum_mul_left]
  calc
    2 * (∑' p : BitString, if (U (p, ([] : BitString))).Dom then progWeight p else 0)
        ≤ 2 * 1 := by gcongr; exact tsum_domain_progWeight_le_one U hU
    _ = 2 := by ring

/-- **Total-mass bound for the counting function.**  Summed over all outputs, the
counting function has mass `≤ 2` in every context: in a nonempty context it
vanishes, and in the empty context the mass is dominated by `tsum_haltMass_le`. -/
lemma countingF_tsum_le (U : Map) (hU : IsPrefixDecompressor U) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
    (ctx : BitString) :
    (∑' out : BitString, countingF c out ctx) ≤ 2 := by
  by_cases hctx : ctx = []
  · subst hctx
    calc
      (∑' out : BitString, countingF c out [])
          ≤ ∑' out : BitString, haltMass U out :=
            ENNReal.tsum_le_tsum (fun out => countingF_le_haltMass U c hc out)
      _ ≤ 2 := tsum_haltMass_le U hU
  · have hzero : ∀ out : BitString, countingF c out ctx = 0 := by
      intro out
      have hs : ∀ s, dyadicValue (countingNum c s out ctx) s = 0 := by
        intro s
        rw [dyadicValue_countingNum, if_neg]
        rintro ⟨h1, _⟩; exact hctx h1
      unfold countingF
      simp only [hs, iSup_const]
    simp only [hzero, tsum_zero]
    exact zero_le

end CountingLSC

end Kolmogorov
