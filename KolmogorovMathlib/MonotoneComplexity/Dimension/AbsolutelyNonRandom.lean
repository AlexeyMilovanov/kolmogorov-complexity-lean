/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.APrioriBranching
import KolmogorovMathlib.MonotoneComplexity.Dimension.DeficiencySemimeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.ImageMeasure
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.SimpleTreeApproximation
import KolmogorovMathlib.MonotoneComplexity.SubSemimeasureDomination

/-!
# Absolutely non-random sequences (SUV Theorem 122, §5.9.2, p. 177)

There is a sequence that is ML-random with respect to no computable measure.
The source's proof is a diagonal construction:

> "To get a 'non-proper' sequence `ω`, we need to ensure that for every
> computable measure `P` there is a prefix of `ω` that has large randomness
> deficiency with respect to `P`.  So we get a countable family of requirements:
> for each measure `P` and for each `c` the corresponding requirement says that
> some prefix has deficiency at least `c` with respect to `P`.  Using a diagonal
> construction, we fulfill these requirements one by one." (p. 177)

This file carries out the diagonal construction and proves it in full.  The
three ingredients are the source's effective descent
(`exists_isRE_chain_cantorMass_le`: for a computable measure, above every string
there is an *enumerable chain* of strings whose measures tend to zero), the
passage from such a chain to a deficiency bound, and the diagonal construction
itself, including the passage from that chain to a
deficiency bound (`exists_pos_le_universalContinuousSemimeasure_of_isRE_chain`:
the indicator of an enumerable chain is a lower semicomputable continuous
semimeasure, so the universal one is bounded below along the chain), the
countability of the family of requirements
(`exists_enumeration_computable₂_nat`: a computable measure enters the
construction only through an approximation algorithm for its interval masses,
and the computable approximation algorithms are indexed by their programs), the
chain of strings, its limit, and the contradiction with the Levin-Schnorr
criterion.

## The `approxMass` device

The diagonal construction cannot quantify over measures: to index the
requirements by natural numbers one needs the *algorithms*, not the measures.
`approxMass a x = ⨅ₛ (a x s / 2^s + 1 / 2^s)` reads the mass of `Ω_x` off an
approximation algorithm `a`, and `approxMass_eq_cantorMass` says that it is the
true mass whenever `a` is an approximation algorithm for a measure.  So the
requirement indexed by `(i, c)` can be stated with `approxMass (E i)` alone.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## The two leaves -/

/-- The computable functions `BitString → ℕ → ℕ` can be enumerated: there is a
family `E : ℕ → BitString → ℕ → ℕ` -- not itself computable, only a list -- that
contains every computable function.

This is what makes the family of requirements of SUV Theorem 122 countable: a
computable measure enters the diagonal construction only through an
approximation algorithm for its interval masses.  Every computable
`a : BitString → ℕ → ℕ` is `Nat.Partrec.Code.eval c` read through the encodings
for one code `c`, and `c` determines `a`, so `a ↦ c` is an injection into `ℕ`. -/
theorem exists_enumeration_computable₂_nat :
    ∃ E : ℕ → BitString → ℕ → ℕ, ∀ a : BitString → ℕ → ℕ, Computable₂ a → ∃ i : ℕ, E i = a := by
  classical
  have key : ∀ a : BitString → ℕ → ℕ, Computable₂ a → ∃ c : Nat.Partrec.Code, ∀ x s,
      Nat.Partrec.Code.eval c (Encodable.encode (x, s)) = Part.some (Encodable.encode (a x s)) := by
    intro a ha
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp ha
    refine ⟨c, fun x s => ?_⟩
    have h := congrFun hc (Encodable.encode ((x, s) : BitString × ℕ))
    rw [h]
    simp [Encodable.encodek]
  have hcount : {a : BitString → ℕ → ℕ | Computable₂ a}.Countable := by
    rw [Set.countable_iff_exists_injOn]
    refine ⟨fun a => if h : Computable₂ a then Encodable.encode (key a h).choose else 0, ?_⟩
    intro a ha b hb hab
    simp only [Set.mem_setOf_eq] at ha hb
    simp only [dif_pos ha, dif_pos hb] at hab
    have hcodes : (key a ha).choose = (key b hb).choose := Encodable.encode_injective hab
    funext x s
    have h1 := (key a ha).choose_spec x s
    have h2 := (key b hb).choose_spec x s
    rw [hcodes] at h1
    have h3 : Part.some (Encodable.encode (a x s)) = Part.some (Encodable.encode (b x s)) :=
      h1.symm.trans h2
    exact Encodable.encode_injective (Part.some_inj.mp h3)
  obtain ⟨E, hE⟩ := hcount.exists_eq_range
    ⟨fun _ _ => 0, (Computable.const 0 : Computable₂ (fun (_ : BitString) (_ : ℕ) => (0 : ℕ)))⟩
  refine ⟨E, fun a ha => ?_⟩
  have hmem : a ∈ Set.range E := by rw [← hE]; exact ha
  obtain ⟨i, hi⟩ := hmem
  exact ⟨i, hi⟩

/-! ## The effective descent (SUV Theorem 122, p. 177)

> "we may extend `x` by adding a bit in such a way that the `P`-measure decreases
> at least by a factor of `1.5`, then do this again, etc.  This can be done
> effectively, so the complexity of the prefixes increases slowly, while the
> measure decreases fast, so we get an arbitrary large deficiency." (p. 177)

Of the two children of a string one has at most half of its mass
(`exists_bool_child_mass_le_half`), so when the mass of the parent is positive
the approximations of `IsComputableMeasure` *certify*, at a fine enough
precision, a child of mass at most two thirds of the parent: the certificate at
precision `s` for the `b`-child of `z` is the inequality of natural numbers
`3 · (a (z ++ [b]) s + 1) ≤ 2 · (a z s - 1)` (`descCertB`).

The path defined below is therefore search-free -- at stage `k` it uses the
precision `k` and takes the `false` child if the stage-`k` certificate accepts
it, the `true` child otherwise -- so it is plainly computable, and its set of
strings is enumerable.  At a stage whose certificate is uninformative the mass
need not drop; but that can only happen when the mass is already below
`20 · 2^{-k}` (`descend_step`), and the mass never increases, so in both cases
the mass along the path tends to zero (`exists_descend_cantorMass_le`).
-/

/-- The stage-`s` certificate that the `b`-child of `z` carries at most two
thirds of the mass of `z`. -/
def descCertB (a : BitString → ℕ → ℕ) (z : BitString) (b : Bool) (s : ℕ) : Bool :=
  decide (3 * (a (z ++ [b]) s + 1) ≤ 2 * (a z s - 1))

/-- Scaling the dyadic rational `n / 2 ^ s` back by `2 ^ s` recovers `n`. -/
lemma dyadicValue_mul_two_pow_self (n s : ℕ) : dyadicValue n s * 2 ^ s = (n : ℝ≥0∞) := by
  rw [dyadicValue, ENNReal.div_mul_cancel (by positivity) (ENNReal.pow_ne_top (by norm_num))]

/-- At a fixed denominator the dyadic value is order-reflecting in the numerator. -/
lemma le_of_dyadicValue_le {n m s : ℕ} (h : dyadicValue n s ≤ dyadicValue m s) : n ≤ m := by
  have h2 : (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
    rw [← dyadicValue_mul_two_pow_self n s, ← dyadicValue_mul_two_pow_self m s]
    exact mul_le_mul' h le_rfl
  exact_mod_cast h2

section Arithmetic

variable {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
  (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
    cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)

include ha

/-- The lower approximation of the mass. -/
lemma dyadicValue_pred_le (z : BitString) (s : ℕ) :
    dyadicValue (a z s - 1) s ≤ cantorMass μ z := by
  rcases Nat.eq_zero_or_pos (a z s) with h0 | hpos
  · rw [h0]
    simp [dyadicValue_zero]
  · have hsplit : a z s - 1 + 1 = a z s := by omega
    have h := (ha z s).1
    rw [← hsplit, dyadicValue_add] at h
    exact (ENNReal.add_le_add_iff_right (dyadicValue_one_ne_top s)).1 h

/-- Soundness of the certificate. -/
lemma descCertB_sound {z : BitString} {b : Bool} {s : ℕ} (h : descCertB a z b s = true) :
    3 * cantorMass μ (z ++ [b]) ≤ 2 * cantorMass μ z := by
  have hnat : 3 * (a (z ++ [b]) s + 1) ≤ 2 * (a z s - 1) := by
    simpa [descCertB] using h
  calc 3 * cantorMass μ (z ++ [b])
      ≤ 3 * (dyadicValue (a (z ++ [b]) s) s + dyadicValue 1 s) :=
        mul_le_mul' le_rfl (ha (z ++ [b]) s).2
    _ = dyadicValue (3 * (a (z ++ [b]) s + 1)) s := by
        rw [dyadicValue_nat_mul, dyadicValue_add]
        norm_num
    _ ≤ dyadicValue (2 * (a z s - 1)) s := dyadicValue_le _ _ _ hnat
    _ = 2 * dyadicValue (a z s - 1) s := by rw [dyadicValue_nat_mul]; norm_num
    _ ≤ 2 * cantorMass μ z := mul_le_mul' le_rfl (dyadicValue_pred_le ha z s)

/-- Completeness of the certificate: a child of at most half the mass is
certified as soon as the precision is finer than a twentieth of the mass. -/
lemma descCertB_of_small {z : BitString} {b : Bool} {s : ℕ}
    (hhalf : 2 * cantorMass μ (z ++ [b]) ≤ cantorMass μ z)
    (hfine : 20 * dyadicValue 1 s ≤ cantorMass μ z) : descCertB a z b s = true := by
  set d : ℝ≥0∞ := dyadicValue 1 s with hd
  set m : ℝ≥0∞ := cantorMass μ z with hm
  set mc : ℝ≥0∞ := cantorMass μ (z ++ [b]) with hmc
  set L : ℝ≥0∞ := dyadicValue (a z s - 1) s with hL
  have hdtop : d ≠ ⊤ := dyadicValue_one_ne_top s
  have hiii : m ≤ L + 2 * d := by
    have h1 : dyadicValue (a z s) s ≤ L + d := by
      rw [hL, ← dyadicValue_add]
      exact dyadicValue_le _ _ _ (by omega)
    calc m ≤ dyadicValue (a z s) s + d := (ha z s).2
      _ ≤ (L + d) + d := add_le_add h1 le_rfl
      _ = L + 2 * d := by ring
  have hU : dyadicValue (3 * (a (z ++ [b]) s + 1)) s ≤ 3 * mc + 6 * d := by
    calc dyadicValue (3 * (a (z ++ [b]) s + 1)) s
        = 3 * (dyadicValue (a (z ++ [b]) s) s + d) := by
          rw [dyadicValue_nat_mul, dyadicValue_add, hd]
          norm_num
      _ ≤ 3 * ((mc + d) + d) := mul_le_mul' le_rfl (add_le_add (ha (z ++ [b]) s).1 le_rfl)
      _ = 3 * mc + 6 * d := by ring
  have hstep : 3 * mc + 6 * d ≤ 2 * L := by
    have h4 : (3 * m + 12 * d) + 8 * d ≤ (4 * L) + 8 * d := by
      calc (3 * m + 12 * d) + 8 * d = 3 * m + 20 * d := by ring
        _ ≤ 3 * m + m := add_le_add le_rfl hfine
        _ = 4 * m := by ring
        _ ≤ 4 * (L + 2 * d) := mul_le_mul' le_rfl hiii
        _ = 4 * L + 8 * d := by ring
    have h5 : 3 * m + 12 * d ≤ 4 * L :=
      (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by norm_num) hdtop)).1 h4
    have h6 : 2 * (3 * mc + 6 * d) ≤ 2 * (2 * L) := by
      calc 2 * (3 * mc + 6 * d) = 3 * (2 * mc) + 12 * d := by ring
        _ ≤ 3 * m + 12 * d := add_le_add (mul_le_mul' le_rfl hhalf) le_rfl
        _ ≤ 4 * L := h5
        _ = 2 * (2 * L) := by ring
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h6
  have hkey : dyadicValue (3 * (a (z ++ [b]) s + 1)) s ≤ dyadicValue (2 * (a z s - 1)) s := by
    calc dyadicValue (3 * (a (z ++ [b]) s + 1)) s ≤ 3 * mc + 6 * d := hU
      _ ≤ 2 * L := hstep
      _ = dyadicValue (2 * (a z s - 1)) s := by rw [hL, dyadicValue_nat_mul]; norm_num
  simp only [descCertB, decide_eq_true_eq]
  exact le_of_dyadicValue_le hkey

end Arithmetic

/-! ### The descent path -/

/-- The descent path from `x`: at stage `k` take the `false` child if the
stage-`k` certificate accepts it, and the `true` child otherwise. -/
def descend (a : BitString → ℕ → ℕ) (x : BitString) : ℕ → BitString
  | 0 => x
  | k + 1 => descend a x k ++ [!descCertB a (descend a x k) false k]

/-- One descent step appends the bit that is *not* certified at the current string, so the chain
always moves into the branch of small mass. -/
lemma descend_succ (a : BitString → ℕ → ℕ) (x : BitString) (k : ℕ) :
    descend a x (k + 1) = descend a x k ++ [!descCertB a (descend a x k) false k] := rfl

/-- Each stage of the descent chain is a prefix of the next. -/
lemma descend_prefix_succ (a : BitString → ℕ → ℕ) (x : BitString) (k : ℕ) :
    descend a x k <+: descend a x (k + 1) := by
  rw [descend_succ]
  exact List.prefix_append _ _

/-- Earlier stages of the descent chain are prefixes of later ones. -/
lemma descend_prefix_mono (a : BitString → ℕ → ℕ) (x : BitString) {k k' : ℕ} (h : k ≤ k') :
    descend a x k <+: descend a x k' := by
  induction k' with
  | zero => simp [Nat.le_zero.1 h]
  | succ k' ih =>
      rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
      · exact (ih (by omega)).trans (descend_prefix_succ a x k')
      · have : k = k' + 1 := by omega
        subst this
        exact List.prefix_refl _

/-- The descent chain starts at `x`, so `x` is a prefix of every stage. -/
lemma prefix_descend (a : BitString → ℕ → ℕ) (x : BitString) (k : ℕ) :
    x <+: descend a x k :=
  descend_prefix_mono a x (Nat.zero_le k)

/-- The dyadic value `n / 2 ^ s` decreases as the stage `s` grows. -/
lemma dyadicValue_le_of_stage_ge {n s t : ℕ} (h : t ≤ s) :
    dyadicValue n s ≤ dyadicValue n t := by
  rw [dyadicValue, dyadicValue]
  gcongr
  exact one_le_two

section Descent

variable {μ : Measure CantorSeq} [IsProbabilityMeasure μ] {a : BitString → ℕ → ℕ}
  (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
    cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)

include ha

/-- One step of the descent: either the mass drops by a factor `3/2`, or it is
already below `20 · 2^{-k}`. -/
lemma descend_step (x : BitString) (k : ℕ) :
    3 * cantorMass μ (descend a x (k + 1)) ≤ 2 * cantorMass μ (descend a x k)
      ∨ cantorMass μ (descend a x k) < 20 * dyadicValue 1 k := by
  classical
  by_cases h20 : 20 * dyadicValue 1 k ≤ cantorMass μ (descend a x k)
  · left
    have hcts : IsContinuousTreeSemimeasure (cantorMass μ) :=
      ⟨cantorMass_nil μ, fun z => le_of_eq (cantorMass_add μ z).symm⟩
    obtain ⟨b, hb⟩ := exists_bool_child_mass_le_half hcts (descend a x k)
    have hhalf : 2 * cantorMass μ (descend a x k ++ [b]) ≤ cantorMass μ (descend a x k) := by
      have h2 : 2 * cantorMass μ (descend a x k ++ [b])
          ≤ 2 * (cantorMass μ (descend a x k) / 2) := mul_le_mul' le_rfl hb
      rwa [ENNReal.mul_div_cancel' (by norm_num) (by norm_num)] at h2
    have hcert : descCertB a (descend a x k) b k = true := descCertB_of_small ha hhalf h20
    by_cases hf : descCertB a (descend a x k) false k = true
    · have hstep : descend a x (k + 1) = descend a x k ++ [false] := by
        rw [descend_succ, hf]
        rfl
      rw [hstep]
      exact descCertB_sound ha hf
    · have hffalse : descCertB a (descend a x k) false k = false := by
        simpa using hf
      have hbtrue : b = true := by
        cases b with
        | false => exact absurd hcert (by rw [hffalse]; simp)
        | true => rfl
      have hstep : descend a x (k + 1) = descend a x k ++ [true] := by
        rw [descend_succ, hffalse]
        rfl
      rw [hstep]
      rw [hbtrue] at hcert
      exact descCertB_sound ha hcert
  · exact Or.inr (not_le.1 h20)

/-- The mass along the descent path tends to zero. -/
lemma exists_descend_cantorMass_le (x : BitString) (n : ℕ) :
    ∃ k : ℕ, cantorMass μ (descend a x k) ≤ dyadicValue 1 n := by
  classical
  have h5 : (32 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 5 = 1 := by
    rw [← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ 5 = 32 by norm_num]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have h32 : dyadicValue 32 (n + 5) = dyadicValue 1 n := by
    calc dyadicValue 32 (n + 5) = 32 * ((2 : ℝ≥0∞)⁻¹) ^ (n + 5) := by
          rw [show (32 : ℕ) = 32 * 1 by norm_num, dyadicValue_nat_mul,
            dyadicValue_one_eq_inv_two_pow']
          norm_num
      _ = (32 * ((2 : ℝ≥0∞)⁻¹) ^ 5) * ((2 : ℝ≥0∞)⁻¹) ^ n := by rw [pow_add]; ring
      _ = ((2 : ℝ≥0∞)⁻¹) ^ n := by rw [h5, one_mul]
      _ = dyadicValue 1 n := (dyadicValue_one_eq_inv_two_pow' n).symm
  by_cases hex : ∃ j, j ≤ 2 * n ∧
      cantorMass μ (descend a x (n + 5 + j)) < 20 * dyadicValue 1 (n + 5 + j)
  · obtain ⟨j, -, hlt⟩ := hex
    refine ⟨n + 5 + j, le_of_lt (lt_of_lt_of_le hlt ?_)⟩
    calc 20 * dyadicValue 1 (n + 5 + j) = dyadicValue (20 * 1) (n + 5 + j) := by
          rw [dyadicValue_nat_mul]
          norm_num
      _ = dyadicValue 20 (n + 5 + j) := by norm_num
      _ ≤ dyadicValue 20 (n + 5) := dyadicValue_le_of_stage_ge (by omega)
      _ ≤ dyadicValue 32 (n + 5) := dyadicValue_le _ _ _ (by norm_num)
      _ = dyadicValue 1 n := h32
  · push_neg at hex
    have hcert : ∀ j, j ≤ 2 * n →
        3 * cantorMass μ (descend a x (n + 5 + j + 1))
          ≤ 2 * cantorMass μ (descend a x (n + 5 + j)) := by
      intro j hj
      rcases descend_step ha x (n + 5 + j) with h | h
      · exact h
      · exact absurd h (not_lt.2 (hex j hj))
    have hgeom : ∀ j, j ≤ 2 * n →
        (3 : ℝ≥0∞) ^ j * cantorMass μ (descend a x (n + 5 + j))
          ≤ 2 ^ j * cantorMass μ (descend a x (n + 5)) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
          intro hj
          have hstep := hcert j (by omega)
          calc (3 : ℝ≥0∞) ^ (j + 1) * cantorMass μ (descend a x (n + 5 + (j + 1)))
              = 3 ^ j * (3 * cantorMass μ (descend a x (n + 5 + j + 1))) := by
                rw [show n + 5 + (j + 1) = n + 5 + j + 1 by omega]
                ring
            _ ≤ 3 ^ j * (2 * cantorMass μ (descend a x (n + 5 + j))) := mul_le_mul' le_rfl hstep
            _ = 2 * (3 ^ j * cantorMass μ (descend a x (n + 5 + j))) := by ring
            _ ≤ 2 * (2 ^ j * cantorMass μ (descend a x (n + 5))) :=
                mul_le_mul' le_rfl (ih (by omega))
            _ = 2 ^ (j + 1) * cantorMass μ (descend a x (n + 5)) := by ring
    refine ⟨n + 5 + 2 * n, ?_⟩
    have hmain := hgeom (2 * n) le_rfl
    have hone : cantorMass μ (descend a x (n + 5)) ≤ 1 := prob_le_one
    have h9 : (9 : ℝ≥0∞) ^ n * cantorMass μ (descend a x (n + 5 + 2 * n)) ≤ 4 ^ n := by
      calc (9 : ℝ≥0∞) ^ n * cantorMass μ (descend a x (n + 5 + 2 * n))
          = 3 ^ (2 * n) * cantorMass μ (descend a x (n + 5 + 2 * n)) := by
            rw [pow_mul]
            norm_num
        _ ≤ 2 ^ (2 * n) * cantorMass μ (descend a x (n + 5)) := hmain
        _ ≤ 2 ^ (2 * n) * 1 := mul_le_mul' le_rfl hone
        _ = 4 ^ n := by rw [mul_one, pow_mul]; norm_num
    have h8 : (4 : ℝ≥0∞) ^ n * ((2 : ℝ≥0∞) ^ n * cantorMass μ (descend a x (n + 5 + 2 * n)))
        ≤ 4 ^ n * 1 := by
      calc (4 : ℝ≥0∞) ^ n * ((2 : ℝ≥0∞) ^ n * cantorMass μ (descend a x (n + 5 + 2 * n)))
          = 8 ^ n * cantorMass μ (descend a x (n + 5 + 2 * n)) := by
            rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num, mul_pow]
            ring
        _ ≤ 9 ^ n * cantorMass μ (descend a x (n + 5 + 2 * n)) := by
            gcongr
            norm_num
        _ ≤ 4 ^ n := h9
        _ = 4 ^ n * 1 := (mul_one _).symm
    have h2n : (2 : ℝ≥0∞) ^ n * cantorMass μ (descend a x (n + 5 + 2 * n)) ≤ 1 :=
      (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ (by norm_num))
        (ENNReal.pow_ne_top (by norm_num))).1 h8
    have hinv : ((2 : ℝ≥0∞)⁻¹) ^ n * (2 : ℝ≥0∞) ^ n = 1 := by
      rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel (by positivity)
        (ENNReal.pow_ne_top (by norm_num))]
    calc cantorMass μ (descend a x (n + 5 + 2 * n))
        = ((2 : ℝ≥0∞)⁻¹) ^ n * ((2 : ℝ≥0∞) ^ n * cantorMass μ (descend a x (n + 5 + 2 * n))) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ n * 1 := mul_le_mul' le_rfl h2n
      _ = dyadicValue 1 n := by rw [mul_one, dyadicValue_one_eq_inv_two_pow']

end Descent

/-! ### The chain is enumerable -/

/-- The descent chain agrees with the primitive recursion that appends one bit per stage, the form
used to establish its computability. -/
lemma descend_eq_natRec (a : BitString → ℕ → ℕ) (x : BitString) (k : ℕ) :
    descend a x k = Nat.rec x (fun k' ih => ih ++ [!descCertB a ih false k']) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [descend_succ, ih]

/-- If the dyadic approximation `a` is computable then so is the bit chosen at each descent step. -/
lemma computable_descCertB_false {a : BitString → ℕ → ℕ} (hacomp : Computable₂ a) :
    Computable fun q : ℕ × BitString => descCertB a q.2 false q.1 := by
  have hchild : Computable fun q : ℕ × BitString => a (q.2 ++ [false]) q.1 :=
    hacomp.comp (Primrec.list_append.to_comp.comp Computable.snd (Computable.const [false]))
      Computable.fst
  have hself : Computable fun q : ℕ × BitString => a q.2 q.1 :=
    hacomp.comp Computable.snd Computable.fst
  have hlhs : Computable fun q : ℕ × BitString => 3 * (a (q.2 ++ [false]) q.1 + 1) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 3)
      (Primrec.nat_add.to_comp.comp hchild (Computable.const 1))
  have hrhs : Computable fun q : ℕ × BitString => 2 * (a q.2 q.1 - 1) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2)
      (Primrec.nat_sub.to_comp.comp hself (Computable.const 1))
  have hle : Primrec fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by
    have ⟨_, H⟩ : PrimrecRel (fun m n : ℕ => m ≤ n) := Primrec.nat_le
    convert H
  exact (hle.to_comp.comp (Computable.pair hlhs hrhs)).of_eq fun q => rfl

/-- For a computable dyadic approximation the descent chain started at `x` is computable in the
stage index. -/
lemma computable_descend {a : BitString → ℕ → ℕ} (hacomp : Computable₂ a) (x : BitString) :
    Computable (descend a x) := by
  have hbit : Computable fun r : ℕ × (ℕ × BitString) =>
      !descCertB a r.2.2 false r.2.1 :=
    Primrec.not.to_comp.comp ((computable_descCertB_false hacomp).comp Computable.snd)
  have hstep : Computable₂ fun (_ : ℕ) (q : ℕ × BitString) =>
      q.2 ++ [!descCertB a q.2 false q.1] :=
    Primrec.list_append.to_comp.comp (Computable.snd.comp Computable.snd)
      (Primrec.list_cons.to_comp.comp hbit (Computable.const []))
  refine (Computable.nat_rec Computable.id (Computable.const x) hstep).of_eq fun k => ?_
  rw [descend_eq_natRec]
  rfl

/-- The set of strings occurring in the descent chain from `x` is recursively enumerable. -/
lemma isRE_mem_descend {a : BitString → ℕ → ℕ} (hacomp : Computable₂ a) (x : BitString) :
    IsRE fun z : BitString => ∃ k : ℕ, descend a x k = z := by
  refine IsRE.exists_encodable ?_
  refine isRE_of_computable_bool _ (fun p : BitString × ℕ => decide (descend a x p.2 = p.1))
    (fun p => by simp) ?_
  have heqp : Primrec fun p : BitString × BitString => decide (p.1 = p.2) := by
    have ⟨_, H⟩ : PrimrecRel (@Eq BitString) := Primrec.eq
    convert H
  have heq : Computable₂ fun u v : BitString => decide (u = v) := heqp.to_comp
  exact heq.comp ((computable_descend hacomp x).comp Computable.snd) Computable.fst

/-! ### The leaf -/

/-- For a computable probability measure and any string `x` there is a recursively enumerable,
prefix-closed and non-branching set of extensions of `x` whose members have `μ`-mass below
`2 ^ (-n)` for every `n`. -/
theorem exists_isRE_chain_cantorMass_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) (x : BitString) :
    ∃ P : BitString → Prop, IsRE P ∧
      (∀ z : BitString, ¬ (P (z ++ [false]) ∧ P (z ++ [true]))) ∧
      (∀ (z : BitString) (b : Bool), P (z ++ [b]) → P z) ∧
      ∀ n : ℕ, ∃ z : BitString, P z ∧ x <+: z ∧ cantorMass μ z ≤ dyadicValue 1 n := by
  classical
  obtain ⟨a, hacomp, ha⟩ := hμ
  refine ⟨fun z => (∃ k : ℕ, descend a x k = z) ∨ z <+: x, ?_, ?_, ?_, ?_⟩
  · refine IsRE.or (isRE_mem_descend hacomp x) ?_
    refine isRE_of_computable_bool _ (fun z => decide (x.take z.length = z)) (fun z => ?_) ?_
    · simp only [decide_eq_true_eq]
      constructor
      · intro h
        exact h ▸ List.take_prefix _ _
      · intro h
        exact (List.prefix_iff_eq_take.1 h).symm
    · have heqp : Primrec fun p : BitString × BitString => decide (p.1 = p.2) := by
        have ⟨_, H⟩ : PrimrecRel (@Eq BitString) := Primrec.eq
        convert H
      have htake : Primrec fun z : BitString => x.take z.length :=
        Primrec.list_take.comp (Primrec.const x) Primrec.list_length
      exact (heqp.comp (Primrec.pair htake Primrec.id)).to_comp
  · rintro z ⟨h0, h1⟩
    have hcomp : ∀ u v : BitString, ((∃ k, descend a x k = u) ∨ u <+: x) →
        ((∃ k, descend a x k = v) ∨ v <+: x) → u <+: v ∨ v <+: u := by
      rintro u v (⟨k, rfl⟩ | hu) (⟨k', rfl⟩ | hv)
      · rcases le_total k k' with h | h
        · exact Or.inl (descend_prefix_mono a x h)
        · exact Or.inr (descend_prefix_mono a x h)
      · exact Or.inr (hv.trans (prefix_descend a x k))
      · exact Or.inl (hu.trans (prefix_descend a x k'))
      · exact List.prefix_or_prefix_of_prefix hu hv
    rcases hcomp _ _ h0 h1 with h | h
    · have heq : z ++ [false] = z ++ [true] := h.eq_of_length (by simp)
      simp at heq
    · have heq : z ++ [true] = z ++ [false] := h.eq_of_length (by simp)
      simp at heq
  · rintro z b (⟨k, hk⟩ | hpre)
    · cases k with
      | zero =>
          refine Or.inr ?_
          change z <+: descend a x 0
          rw [hk]
          exact List.prefix_append z [b]
      | succ j =>
          refine Or.inl ⟨j, ?_⟩
          have hj : descend a x j ++ [!descCertB a (descend a x j) false j] = z ++ [b] := by
            rw [← descend_succ]
            exact hk
          have hlen : (descend a x j).length = z.length := by
            have hl := congrArg List.length hj
            simp only [List.length_append, List.length_singleton] at hl
            omega
          exact (List.append_inj hj hlen).1
    · exact Or.inr ((List.prefix_append z [b]).trans hpre)
  · intro n
    obtain ⟨k, hk⟩ := exists_descend_cantorMass_le ha x n
    exact ⟨descend a x k, Or.inl ⟨k, rfl⟩, prefix_descend a x k, hk⟩

/-! ## The a priori semimeasure along an enumerable chain -/

/-- **The a priori semimeasure is bounded below along an enumerable chain.** -/
theorem exists_pos_le_universalContinuousSemimeasure_of_isRE_chain
    {P : BitString → Prop} (hRE : IsRE P)
    (hchain : ∀ z : BitString, ¬ (P (z ++ [false]) ∧ P (z ++ [true])))
    (hpar : ∀ (z : BitString) (b : Bool), P (z ++ [b]) → P z) :
    ∃ ε : ℝ≥0∞, ε ≠ 0 ∧ ∀ z, P z → ε ≤ universalContinuousSemimeasure z := by
  classical
  obtain ⟨chk, hchkc, hmono, hspec⟩ := hRE.exists_stageApprox
  set f : BitString → ℝ≥0∞ := fun z => if P z then 1 else 0 with hfdef
  have hcoh : ∀ x, f (x ++ [false]) + f (x ++ [true]) ≤ f x := by
    intro x
    by_cases hx : P x
    · by_cases h0 : P (x ++ [false])
      · have h1 : ¬ P (x ++ [true]) := fun h => hchain x ⟨h0, h⟩
        simp [hfdef, if_pos h0, if_neg h1, if_pos hx]
      · by_cases h1 : P (x ++ [true])
        · simp [hfdef, if_neg h0, if_pos h1, if_pos hx]
        · simp [hfdef, if_neg h0, if_neg h1, if_pos hx]
    · have h0 : ¬ P (x ++ [false]) := fun h => hx (hpar x false h)
      have h1 : ¬ P (x ++ [true]) := fun h => hx (hpar x true h)
      simp [hfdef, if_neg h0, if_neg h1, if_neg hx]
  have hroot : f [] ≤ 1 := by
    simp only [hfdef]
    split_ifs <;> simp
  have hlsc : IsLSC fun x (_ : BitString) => f x := by
    refine ⟨fun s out _ => bif chk out s then 2 ^ s else 0, ?_, ?_, ?_⟩
    · intro s out ctx
      cases h : chk out s
      · simp [h, dyadicValue]
      · have h' : chk out (s + 1) = true := hmono out s (s + 1) (by omega) h
        simp [h, h', dyadicValue_two_pow_self]
    · intro out ctx
      by_cases hP : P out
      · obtain ⟨s₀, hs₀⟩ := (hspec out).1 hP
        refine le_antisymm (iSup_le fun s => ?_) ?_
        · cases h : chk out s
          · simp [h, dyadicValue, hfdef, if_pos hP]
          · simp [h, dyadicValue_two_pow_self, hfdef, if_pos hP]
        · refine le_iSup_of_le s₀ ?_
          simp [hs₀, dyadicValue_two_pow_self, hfdef, if_pos hP]
      · have hall : ∀ s, chk out s = false := by
          intro s
          cases h : chk out s
          · rfl
          · exact absurd ((hspec out).2 ⟨s, h⟩) hP
        simp [hall, dyadicValue, hfdef, if_neg hP]
    · have hcond : Computable (fun p : ℕ × BitString × BitString => chk p.2.1 p.1) :=
        hchkc.comp (Computable.fst.comp Computable.snd) Computable.fst
      have hpow : Computable (fun p : ℕ × BitString × BitString => 2 ^ p.1) :=
        (primrec_two_pow_aux.comp Primrec.fst).to_comp
      exact (Computable.cond hcond hpow (Computable.const 0)).of_eq fun p => rfl
  obtain ⟨c, hctop, hc⟩ := exists_const_mul_universalContinuousSemimeasure_ge hcoh hroot hlsc
  by_cases hex : ∃ z, P z
  · obtain ⟨z₀, hz₀⟩ := hex
    have hone : ∀ z, P z → (1 : ℝ≥0∞) ≤ c * universalContinuousSemimeasure z := by
      intro z hz
      have h := hc z
      simp only [hfdef, if_pos hz] at h
      exact h
    have hc0 : c ≠ 0 := by
      intro h
      have := hone z₀ hz₀
      rw [h, zero_mul] at this
      exact absurd this (by norm_num)
    refine ⟨c⁻¹, ENNReal.inv_ne_zero.2 hctop, fun z hz => ?_⟩
    calc c⁻¹ = c⁻¹ * 1 := (mul_one _).symm
      _ ≤ c⁻¹ * (c * universalContinuousSemimeasure z) := by
          exact mul_le_mul' le_rfl (hone z hz)
      _ = (c⁻¹ * c) * universalContinuousSemimeasure z := (mul_assoc _ _ _).symm
      _ = universalContinuousSemimeasure z := by
          rw [ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  · exact ⟨1, one_ne_zero, fun z hz => absurd ⟨z, hz⟩ hex⟩

/-- **SUV Theorem 122, the descent step** (p. 177): above every string there is
an extension whose a priori randomness deficiency exceeds any prescribed
constant.  The enumerable chain of `exists_isRE_chain_cantorMass_le` carries a
lower semicomputable continuous semimeasure of value `1` on it, so the universal
one is bounded below along the chain, while the measure of its strings tends to
zero. -/
theorem exists_prefix_two_pow_mul_cantorMass_lt (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (x : BitString) (c : ℕ) :
    ∃ y : BitString, x <+: y ∧
      (2 : ℝ≥0∞) ^ c * cantorMass μ y < universalContinuousSemimeasure y := by
  obtain ⟨P, hRE, hchain, hpar, hsmall⟩ := exists_isRE_chain_cantorMass_le μ hμ x
  obtain ⟨ε, hε0, hε⟩ :=
    exists_pos_le_universalContinuousSemimeasure_of_isRE_chain hRE hchain hpar
  have h2c0 : ((2 : ℝ≥0∞) ^ c) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2ctop : ((2 : ℝ≥0∞) ^ c) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hdiv : ε / (2 : ℝ≥0∞) ^ c ≠ 0 := by
    simp only [ne_eq, ENNReal.div_eq_zero_iff]
    push_neg
    exact ⟨hε0, h2ctop⟩
  obtain ⟨u, hu⟩ := exists_inv_two_pow_lt hdiv
  obtain ⟨z, hzP, hxz, hzmass⟩ := hsmall u
  refine ⟨z, hxz, ?_⟩
  have hstep : (2 : ℝ≥0∞) ^ c * cantorMass μ z ≤ (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹) ^ u := by
    refine mul_le_mul' le_rfl ?_
    rw [← dyadicValue_one_eq_inv_two_pow']
    exact hzmass
  have hlt : (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹) ^ u < ε := by
    calc (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹) ^ u < (2 : ℝ≥0∞) ^ c * (ε / (2 : ℝ≥0∞) ^ c) :=
          ENNReal.mul_lt_mul_right h2c0 h2ctop hu
      _ = ε := by
          rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.mul_inv_cancel h2c0 h2ctop,
            one_mul]
  exact lt_of_le_of_lt hstep (lt_of_lt_of_le hlt (hε z hzP))

/-! ## The mass read off an approximation algorithm -/

/-- The interval mass that an approximation algorithm `a` describes: the
infimum of the upper bounds `a x s / 2^s + 1 / 2^s` it provides. -/
noncomputable def approxMass (a : BitString → ℕ → ℕ) (x : BitString) : ℝ≥0∞ :=
  ⨅ s : ℕ, (dyadicValue (a x s) s + dyadicValue 1 s)

/-- An approximation algorithm of a measure describes the true interval masses. -/
lemma approxMass_eq_cantorMass {μ : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s) (x : BitString) :
    approxMass a x = cantorMass μ x := by
  refine le_antisymm ?_ (le_iInf fun s => (ha x s).2)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨s, hs⟩ : ∃ s : ℕ, dyadicValue 1 s + dyadicValue 1 s < (ε : ℝ≥0∞) := by
    have hhalf : ((ε : ℝ≥0∞) / 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.div_eq_zero_iff]
      push_neg
      exact ⟨by exact_mod_cast hε.ne', by norm_num⟩
    obtain ⟨s, hs⟩ := exists_inv_two_pow_lt hhalf
    refine ⟨s, ?_⟩
    rw [dyadicValue_one_eq_inv_two_pow']
    calc ((2 : ℝ≥0∞)⁻¹) ^ s + ((2 : ℝ≥0∞)⁻¹) ^ s < (ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2 :=
          ENNReal.add_lt_add hs hs
      _ = (ε : ℝ≥0∞) := ENNReal.add_halves _
  calc approxMass a x ≤ dyadicValue (a x s) s + dyadicValue 1 s := iInf_le _ s
    _ ≤ (cantorMass μ x + dyadicValue 1 s) + dyadicValue 1 s := by
        exact add_le_add (ha x s).1 le_rfl
    _ = cantorMass μ x + (dyadicValue 1 s + dyadicValue 1 s) := by rw [add_assoc]
    _ ≤ cantorMass μ x + (ε : ℝ≥0∞) := add_le_add le_rfl hs.le

/-! ## The limit of a chain of strings -/

/-- The infinite sequence read off an increasing chain of strings. -/
def limitOfChain (x : ℕ → BitString) : CantorSeq := fun n => (x (n + 1)).getD n false

/-- A sequence of strings in which each term is a prefix of its successor is prefix-monotone. -/
lemma chain_prefix_of_le {x : ℕ → BitString} (h : ∀ j, x j <+: x (j + 1)) {i j : ℕ}
    (hij : i ≤ j) : x i <+: x j := by
  induction j with
  | zero => simp [Nat.le_zero.1 hij]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact (ih (by omega)).trans (h j)
      · have : i = j + 1 := by omega
        subst this
        exact List.prefix_refl _

/-- Every string of the chain is a prefix of the limit. -/
lemma cantorPrefix_limitOfChain {x : ℕ → BitString} (hpre : ∀ j, x j <+: x (j + 1))
    (hlen : ∀ j, j ≤ (x j).length) (j : ℕ) :
    cantorPrefix (limitOfChain x) (x j).length = x j := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hij : i < (x j).length := by simpa using h2
  have hi1 : i < (x (i + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self i) (hlen (i + 1))
  set m := max (i + 1) j with hm
  have hpi : x (i + 1) <+: x m := chain_prefix_of_le hpre (le_max_left _ _)
  have hpj : x j <+: x m := chain_prefix_of_le hpre (le_max_right _ _)
  have e1 : (x (i + 1))[i]'hi1 = (x m)[i]'(lt_of_lt_of_le hi1 hpi.length_le) := hpi.getElem hi1
  have e2 : (x j)[i]'hij = (x m)[i]'(lt_of_lt_of_le hij hpj.length_le) := hpj.getElem hij
  have hlimit : limitOfChain x i = (x (i + 1))[i]'hi1 := by
    simp [limitOfChain, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
  simp only [cantorPrefix_getElem]
  rw [hlimit, e1, ← e2]

/-! ## The diagonal construction -/

open Classical in
/-- One step of the diagonal construction: meet the `j`-th requirement if it can
be met above the current string, then add a bit so that the chain grows. -/
noncomputable def nonProperStep (E : ℕ → BitString → ℕ → ℕ) (j : ℕ) (x : BitString) :
    BitString :=
  (if h : ∃ y : BitString, x <+: y ∧
      (2 : ℝ≥0∞) ^ (Nat.unpair j).2 * approxMass (E (Nat.unpair j).1) y
        < universalContinuousSemimeasure y then h.choose else x) ++ [false]

/-- The chain of strings of the diagonal construction. -/
noncomputable def nonProperChain (E : ℕ → BitString → ℕ → ℕ) : ℕ → BitString
  | 0 => []
  | j + 1 => nonProperStep E j (nonProperChain E j)

/-- Each stage of the chain built from the family `E` is a prefix of the next. -/
lemma nonProperChain_prefix (E : ℕ → BitString → ℕ → ℕ) (j : ℕ) :
    nonProperChain E j <+: nonProperChain E (j + 1) := by
  change nonProperChain E j <+: nonProperStep E j (nonProperChain E j)
  unfold nonProperStep
  split_ifs with h
  · exact h.choose_spec.1.trans (List.prefix_append _ _)
  · exact List.prefix_append _ _

/-- The chain built from `E` grows by at least one bit per stage, so stage `j` has length at least
`j`. -/
lemma nonProperChain_length (E : ℕ → BitString → ℕ → ℕ) (j : ℕ) :
    j ≤ (nonProperChain E j).length := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hgrow : (nonProperChain E j).length < (nonProperChain E (j + 1)).length := by
        change (nonProperChain E j).length < (nonProperStep E j (nonProperChain E j)).length
        unfold nonProperStep
        split_ifs with h
        · have := h.choose_spec.1.length_le
          simp only [List.length_append, List.length_singleton]
          omega
        · simp
      omega

/-- If the `j`-th requirement can be met above the `j`-th string of the chain,
then it is met by a prefix of the `(j+1)`-st. -/
lemma nonProperChain_meets (E : ℕ → BitString → ℕ → ℕ) (j : ℕ)
    (h : ∃ y : BitString, nonProperChain E j <+: y ∧
      (2 : ℝ≥0∞) ^ (Nat.unpair j).2 * approxMass (E (Nat.unpair j).1) y
        < universalContinuousSemimeasure y) :
    ∃ y : BitString, y <+: nonProperChain E (j + 1) ∧
      (2 : ℝ≥0∞) ^ (Nat.unpair j).2 * approxMass (E (Nat.unpair j).1) y
        < universalContinuousSemimeasure y := by
  refine ⟨h.choose, ?_, h.choose_spec.2⟩
  change h.choose <+: nonProperStep E j (nonProperChain E j)
  unfold nonProperStep
  rw [dif_pos h]
  exact List.prefix_append _ _

/-- **SUV Theorem 122 (§5.9.2, p. 177).**  There is a sequence that is ML-random
with respect to no computable measure. -/
theorem exists_not_isMartinLofRandom_forall_isComputableMeasure_diag :
    ∃ w : CantorSeq, ∀ μ : Measure CantorSeq, IsProbabilityMeasure μ →
      IsComputableMeasure μ → ¬ IsMartinLofRandom μ w := by
  obtain ⟨E, hE⟩ := exists_enumeration_computable₂_nat
  refine ⟨limitOfChain (nonProperChain E), fun μ hprob hμ hrand => ?_⟩
  haveI := hprob
  obtain ⟨a, hacomp, ha⟩ := hμ
  obtain ⟨i, hi⟩ := hE a hacomp
  obtain ⟨c, hc⟩ := (isMartinLofRandom_iff_boundedAPrioriDeficiency ⟨a, hacomp, ha⟩ _).1 hrand
  have hmass : ∀ z : BitString, approxMass (E i) z = cantorMass μ z := by
    intro z
    rw [hi]
    exact approxMass_eq_cantorMass ha z
  have h1 : (Nat.unpair (Nat.pair i c)).1 = i := by simp
  have h2 : (Nat.unpair (Nat.pair i c)).2 = c := by simp
  have hex : ∃ y : BitString, nonProperChain E (Nat.pair i c) <+: y ∧
      (2 : ℝ≥0∞) ^ (Nat.unpair (Nat.pair i c)).2 *
          approxMass (E (Nat.unpair (Nat.pair i c)).1) y
        < universalContinuousSemimeasure y := by
    obtain ⟨y, hy1, hy2⟩ := exists_prefix_two_pow_mul_cantorMass_lt μ ⟨a, hacomp, ha⟩
      (nonProperChain E (Nat.pair i c)) c
    refine ⟨y, hy1, ?_⟩
    rw [h1, h2, hmass y]
    exact hy2
  obtain ⟨y, hy1, hy2⟩ := nonProperChain_meets E (Nat.pair i c) hex
  rw [h1, h2, hmass y] at hy2
  -- `y` is a prefix of the chain, hence of the limit
  have hlim : cantorPrefix (limitOfChain (nonProperChain E))
      (nonProperChain E (Nat.pair i c + 1)).length
        = nonProperChain E (Nat.pair i c + 1) :=
    cantorPrefix_limitOfChain (nonProperChain_prefix E) (nonProperChain_length E) _
  have hzpre : IsCantorPrefix (nonProperChain E (Nat.pair i c + 1))
      (limitOfChain (nonProperChain E)) :=
    (isCantorPrefix_iff_cantorPrefix_eq _ _).2 hlim
  have hypre : IsCantorPrefix y (limitOfChain (nonProperChain E)) := by
    intro k hk
    have hk1 : k < (nonProperChain E (Nat.pair i c + 1)).length :=
      lt_of_lt_of_le hk hy1.length_le
    rw [hzpre k hk1]
    exact (hy1.getElem hk).symm
  have hyprefix : cantorPrefix (limitOfChain (nonProperChain E)) y.length = y :=
    (isCantorPrefix_iff_cantorPrefix_eq _ _).1 hypre
  have hcy := hc y.length
  rw [hyprefix] at hcy
  exact absurd hcy (not_le.2 hy2)

end Kolmogorov
