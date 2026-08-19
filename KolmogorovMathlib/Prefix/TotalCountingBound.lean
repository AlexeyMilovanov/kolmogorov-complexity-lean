/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding
import KolmogorovMathlib.Prefix.Properties

/-!
# Total Counting Bound for Prefix Complexity (SUV Theorem 64)

This module isolates the counting bounds for the total number of strings with
prefix complexity at most `n`.

SUV Theorem 64 states that `#{x | K(x) ≤ n} = 2^{n - K(n) \pm O(1)}`.
We split this into explicit upper and lower bounds on finite sets.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Finite low-complexity sets -/

/-- Any finite family of strings with `KPPlain ≤ n` injects into the concrete
finite list of programs of length at most `n`.

This is the elementary counting part of Theorem 64: choose, for each output in
`A`, one producing program of length at most `n`. Determinism of `Part` makes the
chosen-program map injective on `A`. The sharper SUV estimate below needs the
additional argument that recovers the `K(n)` factor. -/
theorem card_KPPlain_le_boundedPrograms_length (U : Map) (n : ℕ)
    (A : Finset BitString) (hA : ∀ x ∈ A, KPPlain U x ≤ (n : ENat)) :
    A.card ≤ (boundedPrograms n).length := by
  classical
  have h_exists : ∀ x ∈ A, ∃ p, p.length ≤ n ∧ produces U p [] x := by
    intro x hx
    have hxK : condK U x [] ≤ (n : ENat) := by
      simpa [KPPlain, KP, KP_eq_condK] using hA x hx
    exact (condKLeIff U x [] n).mp hxK
  let pOf : BitString → BitString := fun x ↦
    if hx : x ∈ A then Classical.choose (h_exists x hx) else []
  have hpOf_mem :
      Set.MapsTo pOf (A : Set BitString) ((boundedPrograms n).toFinset : Set BitString) := by
    intro x hx
    have hxf : x ∈ A := by simpa using hx
    have hspec := Classical.choose_spec (h_exists x hxf)
    change pOf x ∈ (boundedPrograms n).toFinset
    rw [show pOf x = Classical.choose (h_exists x hxf) by simp [pOf, hxf]]
    rw [List.mem_toFinset]
    exact (mem_boundedPrograms_iff (Classical.choose (h_exists x hxf)) n).mpr hspec.1
  have hpOf_inj : (A : Set BitString).InjOn pOf := by
    intro x hx y hy hxy
    have hxf : x ∈ A := by simpa using hx
    have hyf : y ∈ A := by simpa using hy
    have hxspec := Classical.choose_spec (h_exists x hxf)
    have hyspec := Classical.choose_spec (h_exists y hyf)
    have hxprod : produces U (pOf x) [] x := by
      rw [show pOf x = Classical.choose (h_exists x hxf) by simp [pOf, hxf]]
      exact hxspec.2
    have hyprod : produces U (pOf x) [] y := by
      rw [hxy]
      rw [show pOf y = Classical.choose (h_exists y hyf) by simp [pOf, hyf]]
      exact hyspec.2
    exact (Part.mem_unique hxprod hyprod)
  calc
    A.card ≤ ((boundedPrograms n).toFinset).card :=
      Finset.card_le_card_of_injOn pOf hpOf_mem hpOf_inj
    _ = (boundedPrograms n).length := by
      rw [List.toFinset_card_of_nodup (boundedPrograms_nodup n)]

/-! ### The crux of the lower bound: short codes for `n - K(n)` -/

/-
**Crux of the Theorem 64 lower bound.**  The number `n - K(n)` has prefix
complexity at most `K(n) + O(1)`.

A single fixed computable function `f` reads the pair
`(Nat.bits n, natCode kn) = prefixComplexityContext (Nat.bits n) kn` and outputs
`Nat.bits (n - kn)`: it recovers `n = decodeBits (decodeFirst ·)` and
`kn = (decodeSecond ·).length - 1` (since `natCode kn` has length `kn + 1`), then
emits the binary code of their truncated difference.  Computable maps do not raise
prefix complexity (`KPPlain_map_le`), and the pair itself has complexity
`kn + O(1)` by SUV Theorem 61 (`KPPair_self_complexity_le`).  Composing the two
bounds yields the claim.
-/
theorem KPPlain_natBits_sub_self_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn →
      KPPlain U (Nat.bits (n - kn)) ≤ (kn : ENat) + (c : ENat) := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℕ, ∀ n kn : ℕ, HasPrefixComplexityValue U (Nat.bits n) kn →
      KPPlain U (Nat.bits (n - kn)) ≤ KPPlain U (prefixComplexityContext (Nat.bits n) kn) + c1 := by
    obtain ⟨c1, hc1⟩ : ∃ c1 : ℕ, ∀ w : BitString,
        KPPlain U (Nat.bits ((decodeBits (decodeFirst w)) - ((decodeSecond w).length - 1)))
          ≤ KPPlain U w + c1 := by
      have hf_computable : Computable (fun w : BitString ↦
          Nat.bits ((decodeBits (decodeFirst w)) - ((decodeSecond w).length - 1))) := by
        refine Computable.comp natBitsComputable ?_
        apply Computable.comp Primrec.nat_sub.to_comp
          (Computable.pair (decodeBitsComputable.comp decodeFirst_computable)
            (Computable.comp Primrec.nat_sub.to_comp
              (Computable.pair (Computable.list_length.comp decodeSecond_computable)
                (Computable.const 1))))
      convert KPPlain_map_le U hU _ hf_computable using 1
    use c1; intros n kn hkn; specialize hc1 (prefixComplexityContext n.bits kn)
    simp only [prefixComplexityContext_eq_pairCode, decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits, length_natCode, add_tsub_cancel_right] at hc1 ⊢
    exact hc1
  obtain ⟨c61, hc61⟩ : ∃ c61 : ℕ, ∀ n kn : ℕ, HasPrefixComplexityValue U (Nat.bits n) kn →
      KPPlain U (prefixComplexityContext (Nat.bits n) kn) ≤ kn + c61 := by
    obtain ⟨c61, hc61⟩ := KPPair_self_complexity_le U hU
    exact ⟨c61, fun n kn h ↦ hc61 _ _ h⟩
  exact ⟨c1 + c61, fun n kn h ↦ le_trans (hc1 n kn h) (by
    rw [add_comm]
    refine le_trans (add_le_add_right (hc61 n kn h) _) ?_
    norm_cast
    omega)⟩

/-- **SUV Theorem 64 (Lower Bound), faithful form.**  In the meaningful regime
`K(n) ≤ n`, there are at least `2^{n - K(n)}` strings whose prefix complexity is
at most `n + O(1)`.

The witnesses are *all* `2^{n-kn}` strings of length `n - kn`.  Each such string
`x` satisfies, by SUV Theorem 63(a) (`KPPlain_le_length_add_KPPlain_length`),
`K(x) ≤ (n - kn) + K(Nat.bits (n - kn)) + O(1)`, and the crux
`KPPlain_natBits_sub_self_le` bounds `K(Nat.bits (n - kn)) ≤ kn + O(1)`, giving
`K(x) ≤ (n - kn) + kn + O(1) = n + O(1)` because `kn ≤ n`.  The cardinality
`2^{n-kn}` equals `2^n · 2^{-kn}` in `ℝ≥0∞` since `kn ≤ n`.

The additive `O(1)` slack on the complexity side is genuine: the original
`card_KPPlain_le_lower_bound` below, which asks for complexity `≤ n` exactly, is
not a theorem for every optimal machine — for a machine all of whose halting
programs have positive length (e.g. the tagged-union universal machine), no
string has complexity `≤ 0`, so the `n = 0` instance forces an empty witness set
while the right-hand side `2^0 · 2^{-(kn+c)}` is positive.
-/
theorem card_KPPlain_le_lower_bound_faithful (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn → kn ≤ n →
    ∃ A : Finset BitString, (∀ x ∈ A, KPPlain U x ≤ (n : ENat) + (c : ENat)) ∧
    (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ kn ≤ (A.card : ℝ≥0∞) := by
  obtain ⟨c63a, hc63a⟩ := KPPlain_le_length_add_KPPlain_length U hU
  obtain ⟨ccrux, hccrux⟩ := KPPlain_natBits_sub_self_le U hU
  use ccrux + c63a
  intro n kn hkn hle
  use stringsOfLength (n - kn)
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxlen : x.length = n - kn := (memStringsOfLength (n - kn) x).mp hx
    refine le_trans (hc63a x) ?_
    rw [hxlen]
    refine le_trans (add_le_add_three le_rfl (hccrux n kn hkn) le_rfl) ?_
    norm_cast
    omega
  · rw [cardStringsOfLength]
    exact two_pow_mul_inv_pow_le_cast_pow_sub n kn

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
    (fun p ↦ if (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))).isSome
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
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_assoc]
    have h_pow : (2 : ℝ≥0∞) ^ s
        = (2 : ℝ≥0∞) ^ (s - decodeBits out) * (2 : ℝ≥0∞) ^ decodeBits out := by
      rw [← pow_add, Nat.sub_add_cancel h3]
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
    Computable (fun q : ℕ × ℕ ↦ countingApprox c q.1 q.2) := by
  convert Primrec.to_comp _;
  unfold countingApprox;
  have h_countingApprox_primrec : Primrec (fun (q : ℕ × ℕ) ↦
      List.map (fun p ↦ if (Nat.Partrec.Code.evaln q.1 c
          (Encodable.encode (p, ([] : BitString)))).isSome then 1 else 0)
        (boundedPrograms q.2)) := by
    refine Primrec.list_map ?_ ?_
    · exact Primrec.comp primrec_boundedPrograms Primrec.snd
    · have h_evaln_computable : Primrec (fun q : ℕ × BitString ↦
          (Nat.Partrec.Code.evaln q.1 c (Encodable.encode (q.2, ([] : BitString)))).isSome) := by
        have h_evaln_computable : Primrec (fun q : ℕ × BitString ↦
            Nat.Partrec.Code.evaln q.1 c (Encodable.encode (q.2, ([] : BitString)))) := by
          have := Nat.Partrec.Code.primrec_evaln
          convert this.comp (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c))
            (Primrec.comp
              (show Primrec (fun q : BitString ↦ Encodable.encode (q, [])) from ?_)
              Primrec.snd)) using 1
          exact Primrec.encode.comp (Primrec.pair Primrec.id (Primrec.const []))
        exact Primrec.option_isSome.comp h_evaln_computable;
      have h_if_computable : Primrec (fun q : Bool ↦ if q then 1 else 0) := by
        have := Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)
        convert this using 1
        ext q
        cases q <;> rfl
      exact h_if_computable.comp
        (h_evaln_computable.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
  have h_sum : Primrec (fun l : List ℕ ↦ List.sum l) := by
    convert Primrec.list_foldr _ _ _ using 1
    rotate_left
    · exact ℕ
    · exact inferInstance
    · exact fun l ↦ l
    · exact fun _ ↦ 0
    · exact fun l p ↦ p.1 + p.2
    · exact Primrec.id
    · exact Primrec.const 0
    · exact Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    · exact funext fun l ↦ by induction l <;> simp +decide [*]
  convert Primrec.comp h_sum h_countingApprox_primrec using 1

/-
The guard predicate of `countingNum` is a computable predicate.
-/
lemma countingNum_guard_computable :
    Computable (fun q : ℕ × BitString × BitString ↦
      decide (q.2.2 = [] ∧ Nat.bits (decodeBits q.2.1) = q.2.1 ∧ decodeBits q.2.1 ≤ q.1)) := by
  have h_computable :
      Computable (fun q : ℕ × BitString × BitString ↦ decide (q.1 ≥ decodeBits q.2.1))
        ∧ Computable (fun q : ℕ × BitString × BitString ↦
            decide (q.2.1 = Nat.bits (decodeBits q.2.1)))
        ∧ Computable (fun q : ℕ × BitString × BitString ↦ decide (q.2.2 = [])) := by
    constructor
    · have h_computable : Computable (fun q : ℕ × BitString ↦ decide (q.1 ≥ decodeBits q.2)) := by
        have h_decode : Computable (fun q : BitString ↦ decodeBits q) := by
          convert decodeBitsComputable using 1
        have h_computable : Computable (fun q : ℕ × ℕ ↦ decide (q.1 ≥ q.2)) := by
          have h_computable : Computable (fun q : ℕ × ℕ ↦ decide (q.1 ≤ q.2)) := by
            have h_computable : Primrec (fun q : ℕ × ℕ ↦ decide (q.1 ≤ q.2)) := by
              exact PrimrecPred.decide Primrec.nat_le
            exact h_computable.to_comp;
          convert h_computable.comp ( Computable.snd.pair Computable.fst ) using 1;
        convert h_computable.comp
          (Computable.pair Computable.fst (h_decode.comp Computable.snd)) using 1
      convert h_computable.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)) using 1
    · constructor;
      · have h_eq : Computable (fun q : BitString × BitString ↦ decide (q.1 = q.2)) := by
          have h_eq : Primrec (fun q : BitString × BitString ↦ decide (q.1 = q.2)) := by
            obtain ⟨_, h_eq⟩ := @Primrec.eq BitString _
            convert h_eq
          convert h_eq.to_comp using 1;
        convert h_eq.comp (Computable.pair (Computable.fst.comp Computable.snd)
          (natBitsComputable.comp (decodeBitsComputable.comp (Computable.fst.comp Computable.snd))))
          using 1
      · have h_decide_empty : Computable (fun q : BitString ↦ decide (q = [])) := by
          convert Computable.of_eq _ _
          · exact fun n ↦ n.isEmpty
          · convert Computable.nat_casesOn _ _ _ using 1
            rotate_left
            · exact fun n ↦ n.length
            · exact fun _ ↦ Bool.true
            · exact fun _ _ ↦ Bool.false
            · exact Computable.list_length
            · exact Computable.const Bool.true
            · exact Computable.const Bool.false
            · ext (_ | _) <;> rfl
          · rintro (_ | _) <;> rfl
        exact h_decide_empty.comp ( Computable.snd.comp Computable.snd );
  convert Computable.cond h_computable.1
    (Computable.cond h_computable.2.2 h_computable.2.1 (Computable.const Bool.false))
    (Computable.const Bool.false) using 1
  ext ⟨q1, q21, q22⟩
  dsimp only
  have h_symm : q21 = Nat.bits (decodeBits q21) ↔ Nat.bits (decodeBits q21) = q21 :=
    ⟨Eq.symm, Eq.symm⟩
  simp only [h_symm, Bool.cond_decide, ge_iff_le]
  by_cases h1 : q22 = [] <;> by_cases h2 : Nat.bits (decodeBits q21) = q21 <;>
    by_cases h3 : decodeBits q21 ≤ q1 <;> simp [h1, h2, h3]

/-
The staged numerator is computable in `(s, out, ctx)`.
-/
lemma countingNum_computable (c : Nat.Partrec.Code) :
    Computable (fun q : ℕ × BitString × BitString ↦ countingNum c q.1 q.2.1 q.2.2) := by
  unfold countingNum
  have h_guard := countingNum_guard_computable
  have h_true : Computable (fun q : ℕ × BitString × BitString ↦
      countingApprox c q.1 (decodeBits q.2.1) * 2 ^ (q.1 - decodeBits q.2.1)) := by
    convert Computable.comp
      (show Computable (fun q : ℕ × ℕ ↦ countingApprox c q.1 q.2 * 2 ^ (q.1 - q.2)) from ?_)
      (show Computable (fun q : ℕ × BitString × BitString ↦ (q.1, decodeBits q.2.1)) from ?_)
      using 1
    · have h_computable : Computable (fun q : ℕ × ℕ ↦ countingApprox c q.1 q.2)
          ∧ Computable (fun q : ℕ × ℕ ↦ 2 ^ (q.1 - q.2)) := by
        constructor
        · exact countingApprox_computable c
        · convert Computable.comp (show Computable (fun n ↦ 2 ^ n) from ?_)
            (show Computable (fun q : ℕ × ℕ ↦ q.1 - q.2) from ?_) using 1
          · exact Computable.of_eq (Primrec.to_comp Kolmogorov.primrec_two_pow) fun n ↦ rfl
          · convert Primrec.to_comp (show Primrec (fun q : ℕ × ℕ ↦ q.1 - q.2) from ?_) using 1
            exact Primrec.nat_sub.comp Primrec.fst Primrec.snd
      convert Computable.comp (show Computable (fun q : ℕ × ℕ ↦ q.1 * q.2) from ?_)
        (h_computable.1.pair h_computable.2) using 1
      convert Primrec.to_comp (show Primrec (fun q : ℕ × ℕ ↦ q.1 * q.2) from ?_) using 1
      exact Primrec.nat_mul.comp Primrec.fst Primrec.snd
    · exact Computable.pair Computable.fst
        (decodeBitsComputable.comp (Computable.fst.comp Computable.snd))
  have h_false : Computable (fun q : ℕ × BitString × BitString ↦ 0) := Computable.const 0
  have h_cond := Computable.cond h_guard h_true h_false
  convert h_cond using 1
  ext q
  by_cases h : q.2.2 = [] ∧ Nat.bits (decodeBits q.2.1) = q.2.1 ∧ decodeBits q.2.1 ≤ q.1 <;>
    simp [h]

/-- The counting function is lower-semicomputable. -/
lemma countingF_isLSC (c : Nat.Partrec.Code) : IsLSC (countingF c) :=
  ⟨countingNum c, countingNum_dyadic_mono c, fun _ _ ↦ rfl, countingNum_computable c⟩

/-
**Counting injection.**  For a finite set `A` of strings all of complexity
`≤ n`, a large enough fuel `s ≥ n` makes `countingApprox c s n` at least `|A|`:
each `x ∈ A` has a distinct halting program of length `≤ n`, and all of them halt
within a common fuel bound.
-/
lemma countingApprox_ge_card (U : Map) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (n : ℕ) (A : Finset BitString) (hA : ∀ x ∈ A, KPPlain U x ≤ (n : ENat)) :
    ∃ s, n ≤ s ∧ A.card ≤ countingApprox c s n := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, n ≤ s ∧ ∀ x ∈ A, ∃ p : BitString, p.length ≤ n ∧ produces U p [] x
      ∧ (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))
        = some (Encodable.encode x)) := by
    have h_exists_p : ∀ x ∈ A, ∃ p : BitString, p.length ≤ n ∧ produces U p [] x := by
      exact fun x hx ↦ (condKLeIff U x [] n).mp (hA x hx)
    choose! p hp₁ hp₂ using h_exists_p
    obtain ⟨s, hs⟩ : ∃ s : ℕ, ∀ x ∈ A, ∃ k : ℕ, k ≤ s
        ∧ (Nat.Partrec.Code.evaln k c (Encodable.encode (p x, ([] : BitString)))
          = some (Encodable.encode x)) := by
      have h_exists_k : ∀ x ∈ A, ∃ k : ℕ,
          (Nat.Partrec.Code.evaln k c (Encodable.encode (p x, ([] : BitString)))
            = some (Encodable.encode x)) := by
        intro x hx
        exact (produces_iff_evaln c hc (p x) x []).mp (hp₂ x hx)
      choose! k hk using h_exists_k;
      exact ⟨ Finset.sup A k, fun x hx ↦ ⟨ k x, Finset.le_sup ( f := k ) hx, hk x hx ⟩ ⟩;
    exact ⟨s + n, by linarith, fun x hx ↦ by
      obtain ⟨k, hk₁, hk₂⟩ := hs x hx
      exact ⟨p x, hp₁ x hx, hp₂ x hx,
        by simpa [hk₂] using Nat.Partrec.Code.evaln_mono (by linarith : k ≤ s + n) hk₂⟩⟩
  obtain ⟨pOf, hpOf⟩ : ∃ pOf : BitString → BitString,
      (∀ x ∈ A, pOf x ∈ boundedPrograms n ∧ produces U (pOf x) [] x
        ∧ (Nat.Partrec.Code.evaln s c (Encodable.encode (pOf x, ([] : BitString)))
          = some (Encodable.encode x)))
        ∧ (∀ x y : BitString, x ∈ A → y ∈ A → pOf x = pOf y → x = y) := by
    choose! p hp using hs.2
    refine ⟨p, ?_, ?_⟩
    · intro x hx
      exact ⟨(mem_boundedPrograms_iff (p x) n).mpr (hp x hx).1,
        (hp x hx).2.1, (hp x hx).2.2⟩
    · intro x y hx hy hxy
      have hx_prod := (hp x hx).2.1
      have hy_prod := (hp y hy).2.1
      rw [hxy] at hx_prod
      exact Part.mem_unique hx_prod hy_prod
  refine ⟨ s, hs.1, ?_ ⟩;
  have h_card : (Finset.image pOf A).card
      ≤ ((boundedPrograms n).filter (fun p ↦ (Nat.Partrec.Code.evaln s c
          (Encodable.encode (p, ([] : BitString)))).isSome)).length := by
    have h_card : (Finset.image pOf A).card
        ≤ (List.toFinset (List.filter (fun p ↦
            (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))).isSome)
          (boundedPrograms n))).card := by
      refine Finset.card_le_card ?_
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      rw [List.mem_toFinset, List.mem_filter]
      have hpx := hpOf.1 x hx
      exact ⟨hpx.1, Option.isSome_iff_exists.mpr ⟨Encodable.encode x, hpx.2.2⟩⟩
    exact h_card.trans (List.toFinset_card_le _)
  convert h_card using 1;
  · rw [ Finset.card_image_of_injOn fun x hx y hy hxy ↦ hpOf.2 x y hx hy hxy ];
  · unfold countingApprox
    induction boundedPrograms n with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.filter_cons, List.map_cons]
      split_ifs
      · simp only [List.sum_cons, List.length_cons]
        omega
      · simp only [List.sum_cons]
        omega

/-- **Lower bound for the counting function.**  For any finite set `A` of strings
all of complexity `≤ n`, the counting function at `Nat.bits n` dominates
`|A| · 2^{-n}`. -/
lemma countingF_ge_card (U : Map) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
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
          exact le_iSup (fun s ↦ dyadicValue (countingNum c s (Nat.bits n) []) s) s

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
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (out : BitString) :
    countingF c out [] ≤ haltMass U out := by
  classical
  refine iSup_le fun s ↦ ?_;
  by_cases hcanon : Nat.bits (decodeBits out) = out <;> by_cases hle : decodeBits out ≤ s <;>
    simp +decide only [dyadicValue_countingNum, hcanon, hle, and_self, and_false, and_true,
      ↓reduceIte, haltMass, zero_le, Std.le_refl]
  have h_card : (countingApprox c s (decodeBits out) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (decodeBits out)
      = ∑ p ∈ (boundedPrograms (decodeBits out)).toFinset.filter (fun p ↦
          (Nat.Partrec.Code.evaln s c (Encodable.encode (p, ([] : BitString)))).isSome),
        (2 : ℝ≥0∞)⁻¹ ^ (decodeBits out) := by
    simp +decide only [countingApprox, Encodable.encode_prod_val, Encodable.encode_list_nil,
      Nat.cast_list_sum, List.map_map, Finset.sum_const, nsmul_eq_mul]
    rw [ Finset.card_filter ];
    rw [List.sum_toFinset]
    · simp only [Nat.cast_list_sum, List.map_map]
      rfl
    · exact boundedPrograms_nodup _
  refine h_card ▸ le_trans ?_
    ( ENNReal.sum_le_tsum
        (f := fun p ↦ if p.length ≤ decodeBits out ∧ (U (p, ([] : BitString))).Dom
          then (2 : ℝ≥0∞)⁻¹ ^ (decodeBits out) else 0)
        ((boundedPrograms (decodeBits out)).toFinset.filter
          (fun p ↦ (Nat.Partrec.Code.evaln s c
            (Encodable.encode (p, ([] : BitString)))).isSome)) );
  refine Finset.sum_le_sum ?_
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hp_len : p.length ≤ decodeBits out := by
    exact (mem_boundedPrograms_iff p (decodeBits out)).mp (by simpa using hp'.1)
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp'.2
  have h_eval := Nat.Partrec.Code.evaln_sound hx
  rw [hc] at h_eval
  obtain ⟨a, ha_decode, ha_map⟩ := Part.mem_bind_iff.mp h_eval
  have ha_eq : a = (p, ([] : BitString)) := by
    exact Part.mem_unique ha_decode (by simp)
  subst a
  obtain ⟨y, hy, _⟩ := (Part.mem_map_iff Encodable.encode).mp ha_map
  have h_dom : (U (p, [])).Dom := Part.dom_iff_mem.mpr ⟨y, hy⟩
  simp [hp_len, h_dom]

open Classical in
/-- **Kraft inequality on the halting domain.**  For a prefix decompressor, the
sum of program weights over the halting domain (empty context) is `≤ 1`. -/
lemma tsum_domain_progWeight_le_one (U : Map) (hU : IsPrefixDecompressor U) :
    (∑' p : BitString, if (U (p, ([] : BitString))).Dom then progWeight p else 0) ≤ 1 := by
  have h_sum : (∑' x, aprioriMeasure U x []) ≤ 1 := by
    exact tsum_aprioriMeasure_le_one U [] hU.isPrefixMachine
  have h_sum_eq : (∑' x, aprioriMeasure U x [])
      = (∑' p, ∑' x, if produces U p [] x then progWeight p else 0) := by
    exact ENNReal.tsum_comm
  rw [h_sum_eq] at h_sum
  refine le_trans (le_of_eq ?_) h_sum
  refine tsum_congr (fun p ↦ ?_)
  by_cases hp : (U (p, [])).Dom
  · rw [if_pos hp]
    have ⟨x, hx⟩ := Part.dom_iff_mem.mp hp
    have h_prod : produces U p [] x := hx
    have h_eq : (∑' x', if produces U p [] x' then progWeight p else 0) = progWeight p := by
      rw [tsum_eq_single x]
      · rw [if_pos h_prod]
      · intro x' hneq
        rw [if_neg]
        intro h_prod'
        exact hneq (Part.mem_unique h_prod' h_prod)
    exact h_eq.symm
  · rw [if_neg hp]
    have h_eq : (∑' x', if produces U p [] x' then progWeight p else 0) = 0 := by
      have h_zero : (fun x' ↦ if produces U p [] x' then (progWeight p : ENNReal) else 0)
          = fun _ ↦ 0 := by
        ext x'
        rw [if_neg]
        intro h_prod
        exact hp (Part.dom_iff_mem.mpr ⟨x', h_prod⟩)
      rw [h_zero, tsum_zero]
    exact h_eq.symm

open Classical in
/-- The value of `haltMass` at a canonical output `Nat.bits n`. -/
lemma haltMass_natBits (U : Map) (n : ℕ) :
    haltMass U (Nat.bits n)
      = ∑' p : BitString, if p.length ≤ n ∧ (U (p, ([] : BitString))).Dom
          then (2 : ℝ≥0∞)⁻¹ ^ n else 0 := by
  -- By definition, `haltMass U (Nat.bits n)` sums the weights of programs producing `n`.
  unfold haltMass
  simp [decodeBits_natBits]

/-
The total `haltMass` is supported on canonical outputs, so it reindexes along
`Nat.bits`.
-/
lemma tsum_haltMass_eq_tsum_nat (U : Map) :
    (∑' out : BitString, haltMass U out) = ∑' n : ℕ, haltMass U (Nat.bits n) := by
  convert (Function.Injective.tsum_eq (show Function.Injective Nat.bits from ?_) ?_).symm using 1
  · exact Function.LeftInverse.injective
      (show Function.LeftInverse decodeBits Nat.bits from fun n ↦ decodeBits_natBits n)
  · intro x hx
    unfold haltMass at hx
    rw [Function.mem_support] at hx
    by_cases h : Nat.bits (decodeBits x) = x
    · exact ⟨decodeBits x, h⟩
    · rw [if_neg h] at hx
      contradiction

/-
Geometric tail sum: `∑_{n ≥ m} 2^{-n} = 2 · 2^{-m}`.
-/
lemma tsum_ge_pow (m : ℕ) :
    (∑' n : ℕ, if m ≤ n then (2 : ℝ≥0∞)⁻¹ ^ n else 0) = 2 * (2 : ℝ≥0∞)⁻¹ ^ m := by
  -- Reindex the tail sum `∑_{n ≥ m}` along `k ↦ k + m`, then factor out `2^{-m}`.
  have hinj : Function.Injective (fun k : ℕ ↦ k + m) := fun _ _ h ↦ Nat.add_right_cancel h
  have hsupp : Function.support (fun n ↦ if m ≤ n then (2 : ℝ≥0∞)⁻¹ ^ n else 0)
      ⊆ Set.range (fun k : ℕ ↦ k + m) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_cases hmx : m ≤ x
    · exact ⟨x - m, Nat.sub_add_cancel hmx⟩
    · rw [if_neg hmx] at hx
      exact absurd rfl hx
  have h_factor : (∑' n, if m ≤ n then (2 : ℝ≥0∞)⁻¹ ^ n else 0)
      = (∑' n, (2 : ℝ≥0∞)⁻¹ ^ (n + m)) := by
    rw [← hinj.tsum_eq hsupp]
    exact tsum_congr fun n ↦ if_pos (Nat.le_add_left m n)
  rw [h_factor]
  simp [pow_add, ENNReal.tsum_mul_right]

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
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (ctx : BitString) :
    (∑' out : BitString, countingF c out ctx) ≤ 2 := by
  by_cases hctx : ctx = []
  · subst hctx
    calc
      (∑' out : BitString, countingF c out [])
          ≤ ∑' out : BitString, haltMass U out :=
            ENNReal.tsum_le_tsum (fun out ↦ countingF_le_haltMass U c hc out)
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

/-- **Counting prefix machine for SUV Theorem 64 (upper bound).**  There is a
prefix decompressor `M` and a coding constant `c₀` such that, for every `n` and
every finite set `A` of strings of prefix complexity `≤ n`,

  `2^{-c₀} · (|A| · 2^{-n}) ≤ 2^{-KP_M(Nat.bits n)}`.

This is the genuinely hard enumeration-and-coding step of Theorem 64: it is the
Kraft–Chaitin realization (`kraftChaitin_realization_bound`) of the counting
lower-semicomputable function `countingF`, whose pointwise lower bound is
`countingF_ge_card` and whose total mass `≤ 2 = 2^1` is `countingF_tsum_le`.

The coding constant `c₀` is genuine.  A constant-free version is **false**: a
prefix machine `M` has total Kraft mass `∑_x 2^{-KP_M(x)} ≤ 1`, whereas the
required counting mass `∑_n N_n 2^{-n} = 2 ∑_x 2^{-K(x)}` can exceed `1`.  The
constant is harmlessly absorbed by the optimal-machine invariance in
`card_KPPlain_le_complexityWeight_bound`, so the downstream Theorem 64 upper bound
is unaffected. -/
theorem exists_counting_prefix_machine (U : Map) (hU : IsPrefixDecompressor U) :
    ∃ M : Map, IsPrefixDecompressor M ∧ ∃ c₀ : ℕ,
    ∀ (n : ℕ) (A : Finset BitString),
      (∀ x ∈ A, KPPlain U x ≤ (n : ENat)) →
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * ((A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n)
        ≤ complexityWeight (KP M (Nat.bits n) []) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  have hlsc : IsLSC (countingF c) := countingF_isLSC c
  have hsum : ∀ ctx : BitString, (∑' out : BitString, countingF c out ctx) ≤ (2 : ℝ≥0∞) ^ 1 := by
    intro ctx
    rw [pow_one]
    exact countingF_tsum_le U hU c hc ctx
  obtain ⟨M, hM, c₀, hreal⟩ := kraftChaitin_realization_bound hlsc 1 hsum
  refine ⟨M, hM, c₀, fun n A hA ↦ ?_⟩
  calc
    (2 : ℝ≥0∞)⁻¹ ^ c₀ * ((A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n)
        ≤ (2 : ℝ≥0∞)⁻¹ ^ c₀ * countingF c (Nat.bits n) [] := by
          gcongr
          exact countingF_ge_card U c hc n A hA
    _ ≤ complexityWeight (KP M (Nat.bits n) []) := hreal (Nat.bits n) []

/-- The counting weight of `n` is bounded by the complexity weight of `n` in an optimal machine. -/
theorem card_KPPlain_le_complexityWeight_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n : ℕ) (A : Finset BitString),
    (∀ x ∈ A, KPPlain U x ≤ (n : ENat)) →
    (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n
      ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (Nat.bits n)) := by
  obtain ⟨M, hM, c₀, hM_bound⟩ := exists_counting_prefix_machine U hU.isPrefixDecompressor
  obtain ⟨c, hc⟩ := optimalPrefix_complexityWeight_bound hU hM
  refine ⟨c + c₀, fun n A hA ↦ ?_⟩
  have key := hM_bound n A hA
  have hopt := hc (Nat.bits n) []
  have h1 : (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n
      ≤ (2 : ℝ≥0∞) ^ c₀ * complexityWeight (KP M (Nat.bits n) []) := by
    calc
      (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n
          = (2 : ℝ≥0∞) ^ c₀ * ((2 : ℝ≥0∞)⁻¹ ^ c₀ * ((A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n)) := by
            rw [← mul_assoc, ← mul_pow,
              ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
      _ ≤ (2 : ℝ≥0∞) ^ c₀ * complexityWeight (KP M (Nat.bits n) []) := by gcongr
  have h2 : complexityWeight (KP M (Nat.bits n) [])
      ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (Nat.bits n)) := by
    calc
      complexityWeight (KP M (Nat.bits n) [])
          = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c * complexityWeight (KP M (Nat.bits n) [])) := by
            rw [← mul_assoc, ← mul_pow,
              ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
      _ ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (Nat.bits n)) := by
            gcongr
            simpa [KPPlain] using hopt
  calc
    (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n
        ≤ (2 : ℝ≥0∞) ^ c₀ * complexityWeight (KP M (Nat.bits n) []) := h1
    _ ≤ (2 : ℝ≥0∞) ^ c₀ * ((2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (Nat.bits n))) := by
          gcongr
    _ = (2 : ℝ≥0∞) ^ (c + c₀) * complexityWeight (KPPlain U (Nat.bits n)) := by
          rw [pow_add]; ring

theorem card_KPPlain_le_upper_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn →
    ∀ A : Finset BitString, (∀ x ∈ A, KPPlain U x ≤ (n : ENat)) →
    (A.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (n + c) * (2 : ℝ≥0∞)⁻¹ ^ kn := by
  obtain ⟨c, hc⟩ := card_KPPlain_le_complexityWeight_bound U hU
  use c
  intro n kn hkn A hA
  specialize hc n A hA
  have h_weight : complexityWeight (KPPlain U (Nat.bits n)) = (2 : ℝ≥0∞)⁻¹ ^ kn := by
    dsimp [HasPrefixComplexityValue, KPPlain] at hkn ⊢
    rw [← hkn, complexityWeight_coe]
  rw [h_weight] at hc
  have e : (A.card : ℝ≥0∞) = (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n := by
    rw [mul_assoc]
    have h_inv : (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    rw [h_inv, mul_one]
  calc
    (A.card : ℝ≥0∞) = (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n := e
    _ ≤ ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn) * (2 : ℝ≥0∞) ^ n := by
        gcongr
    _ = (2 : ℝ≥0∞) ^ (n + c) * (2 : ℝ≥0∞)⁻¹ ^ kn := by
        rw [pow_add]
        ring

/- SUV Theorem 64 (Lower Bound), historical exact statement.

There are at least `2^{n - K(n) - O(1)}` strings
with prefix complexity at most `n`.
Formulated as the existence of a finite set `A` of such strings.

This exact form (complexity `≤ n`, no additive slack) is **not** provable for
every optimal prefix machine: at `n = 0` it would require a string of complexity
`≤ 0`, which need not exist (e.g. for machines whose halting programs are all
nonempty).  The faithful, provable statement is
`card_KPPlain_le_lower_bound_faithful`, which asks for complexity `≤ n + O(1)` in
the regime `K(n) ≤ n`.

This declaration is therefore commented out: it is genuinely false for some
optimal prefix decompressors (so it cannot be proved without an additional
normalization hypothesis on `U` supplying a zero-length program), and it is not
referenced anywhere in the project.  The faithful, fully proved replacement
`card_KPPlain_le_lower_bound_faithful` above supersedes it.
-/

/-
theorem card_KPPlain_le_lower_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn →
    ∃ A : Finset BitString, (∀ x ∈ A, KPPlain U x ≤ (n : ENat)) ∧
    (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ (kn + c) ≤ (A.card : ℝ≥0∞) :=
  -- False without additional hypotheses on U
  -- e.g. at n=0 requires complexity ≤ 0, impossible if all halting programs are nonempty
  -- Use `card_KPPlain_le_lower_bound_faithful` instead.
-/

end Kolmogorov
