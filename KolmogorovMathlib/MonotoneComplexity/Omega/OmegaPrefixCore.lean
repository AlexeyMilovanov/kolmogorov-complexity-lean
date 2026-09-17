/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.LscBasic
import KolmogorovMathlib.AlgorithmicRandomness.Cantor
import Mathlib.Order.BourbakiWitt
import KolmogorovMathlib.MonotoneComplexity.Omega.PrefixTransfer

/-!
# The binary value of a prefix (SUV Theorem 100, p. 157)

The quantitative core of SUV Theorem 100 reads the first `n` bits of `Ω` as the rational
`0.x₀x₁…x_{n-1}` and uses that this rational is within `2⁻ⁿ` of `Ω` from below.  This
module supplies that rational and the two-sided estimate.

`bitsValue x = bitsNum x / 2^{|x|}`, where `bitsNum` is Horner's scheme on the bits (most
significant first).  Both are computable, and on a prefix of `w` the value is the partial
sum of the series defining the real of `w`:

* `bitsValue_cantorPrefix` — `bitsValue (cantorPrefix w n) = ∑_{k<n} [w k] · 2^{-(k+1)}`;
* `bitsValue_cantorPrefix_le` and `le_bitsValue_cantorPrefix_add` — the sandwich
  `value ≤ Ω ≤ value + 2⁻ⁿ`.

This module is *upstream* of `Omega/Basic.lean` (which is where the leaf that consumes it
lives), so it may not use anything defined there.  It renders no statement of the source.
-/

namespace Kolmogorov

open ENNReal

/-! ### Horner's scheme on a bit string -/

/-- The binary numeral of a bit string, most significant bit first. -/
def bitsNum (x : BitString) : ℕ := x.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0

/-- Reading a bit string as a binary numeral is primitive recursive. -/
theorem primrec_bitsNum : Primrec bitsNum := by
  have hstep : Primrec₂
      (fun (_ : BitString) (q : ℕ × Bool) => 2 * q.1 + (if q.2 then 1 else 0)) := by
    have h1 : Primrec (fun q : BitString × (ℕ × Bool) => 2 * q.2.1) :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd)
    have h2 : Primrec (fun q : BitString × (ℕ × Bool) => if q.2.2 then 1 else 0) :=
      (Primrec.cond (Primrec.snd.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0)).of_eq
        (fun q => by cases q.2.2 <;> simp)
    exact Primrec₂.mk (Primrec.nat_add.comp h1 h2)
  exact Primrec.list_foldl Primrec.id (Primrec.const 0) hstep

/-- Appending a bit doubles the numeral and adds the new bit. -/
theorem bitsNum_append_singleton (x : BitString) (b : Bool) :
    bitsNum (x ++ [b]) = 2 * bitsNum x + (if b then 1 else 0) := by
  rw [bitsNum, bitsNum, List.foldl_append]
  simp

/-- The value of the bit string `x` read as the binary fraction `0.x₀x₁…`. -/
def bitsValue (x : BitString) : ℚ := (bitsNum x : ℚ) / 2 ^ x.length

/-- Reading a bit string as the binary fraction `0.x` is computable. -/
theorem computable_bitsValue : Computable bitsValue := by
  have hden : Computable (fun x : BitString => (1 : ℚ) / 2 ^ x.length) := by
    have hnat : Primrec (fun x : BitString => 2 ^ x.length) :=
      (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.list_length
    refine computable_of_num_den (N := fun _ : BitString => (1 : ℤ))
      (D := fun x : BitString => 2 ^ x.length) (Computable.const 1)
      hnat.to_comp (fun _ => by positivity) (fun x => ?_)
    push_cast
    ring
  have hnum : Computable (fun x : BitString => ((bitsNum x : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp primrec_bitsNum.to_comp
  refine (Computable₂.comp computable₂_ratMul hnum hden).of_eq (fun x => ?_)
  rw [bitsValue]
  ring

/-- The binary fraction of a bit string is nonnegative. -/
theorem bitsValue_nonneg (x : BitString) : 0 ≤ bitsValue x := by
  rw [bitsValue]
  positivity

/-! ### The value of a prefix of a binary sequence -/

/-- The binary fraction of the first `n` bits of a Cantor sequence is the corresponding partial
sum of its expansion series. -/
theorem bitsValue_cantorPrefix (w : CantorSeq) (n : ℕ) :
    bitsValue (cantorPrefix w n)
      = ∑ k ∈ Finset.range n, (if w k then (1 : ℚ) / 2 ^ (k + 1) else 0) := by
  induction n with
  | zero => simp [bitsValue, bitsNum, cantorPrefix]
  | succ n ih =>
      have hpref : cantorPrefix w (n + 1) = cantorPrefix w n ++ [w n] := cantorPrefix_succ w n
      have hlen : (cantorPrefix w n).length = n := cantorPrefix_length w n
      rw [Finset.sum_range_succ, ← ih, bitsValue, bitsValue, hpref, bitsNum_append_singleton,
        List.length_append, hlen, List.length_singleton]
      have h2 : ((2 : ℚ) ^ (n + 1)) ≠ 0 := by positivity
      have h2' : ((2 : ℚ) ^ n) ≠ 0 := by positivity
      by_cases hb : w n
      · rw [if_pos hb, if_pos hb]
        push_cast
        field_simp
        ring
      · rw [if_neg hb, if_neg hb]
        push_cast
        field_simp
        ring

/-! ### The sandwich -/

/-- The binary expansion series of a Cantor sequence is summable. -/
theorem summable_cantorTerm (w : CantorSeq) :
    Summable (fun k : ℕ => (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0)) := by
  have hnn : ∀ k : ℕ, 0 ≤ (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) := by
    intro k; by_cases h : w k <;> simp [h]
  have hdom : ∀ k : ℕ,
      (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) ≤ ((1 : ℝ) / 2) ^ (k + 1) := by
    intro k
    have hpow : ((1 : ℝ) / 2) ^ (k + 1) = (1 : ℝ) / 2 ^ (k + 1) := by rw [div_pow, one_pow]
    rw [hpow]
    by_cases h : w k
    · simp [h]
    · simp only [h]
      positivity
  have hgeom : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hshift : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 1)) := by
    simpa [pow_succ] using hgeom.mul_right ((1 : ℝ) / 2)
  exact Summable.of_nonneg_of_le hnn hdom hshift

/-- The value of the `n`-bit prefix is below the real of the sequence. -/
theorem bitsValue_cantorPrefix_le (w : CantorSeq) (n : ℕ) :
    ((bitsValue (cantorPrefix w n) : ℚ) : ℝ)
      ≤ ∑' k : ℕ, (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) := by
  have hS := summable_cantorTerm w
  have hnn : ∀ k : ℕ, 0 ≤ (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) := by
    intro k; by_cases h : w k <;> simp [h]
  have hcast : ((bitsValue (cantorPrefix w n) : ℚ) : ℝ)
      = ∑ k ∈ Finset.range n, (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) := by
    rw [bitsValue_cantorPrefix]
    push_cast
    exact Finset.sum_congr rfl (fun k _ => by by_cases h : w k <;> simp [h])
  rw [hcast]
  exact hS.sum_le_tsum (Finset.range n) (fun k _ => hnn k)

/-- The real of the sequence is within `2⁻ⁿ` above the value of its `n`-bit prefix. -/
theorem le_bitsValue_cantorPrefix_add (w : CantorSeq) (n : ℕ) :
    (∑' k : ℕ, (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0))
      ≤ ((bitsValue (cantorPrefix w n) : ℚ) : ℝ) + (1 : ℝ) / 2 ^ n := by
  have hS := summable_cantorTerm w
  have hcast : ((bitsValue (cantorPrefix w n) : ℚ) : ℝ)
      = ∑ k ∈ Finset.range n, (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) := by
    rw [bitsValue_cantorPrefix]
    push_cast
    exact Finset.sum_congr rfl (fun k _ => by by_cases h : w k <;> simp [h])
  have hsplit := hS.sum_add_tsum_nat_add n
  have htail : (∑' k : ℕ, (if w (k + n) then (1 : ℝ) / 2 ^ (k + n + 1) else 0))
      ≤ (1 : ℝ) / 2 ^ n := by
    have hgeom : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + n + 1)) := by
      have h0 : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      simpa [pow_add, mul_assoc] using (h0.mul_right (((1 : ℝ) / 2) ^ (n + 1)))
    have hdom : ∀ k : ℕ, (if w (k + n) then (1 : ℝ) / 2 ^ (k + n + 1) else 0)
        ≤ ((1 : ℝ) / 2) ^ (k + n + 1) := by
      intro k
      have hpow : ((1 : ℝ) / 2) ^ (k + n + 1) = (1 : ℝ) / 2 ^ (k + n + 1) := by
        rw [div_pow, one_pow]
      rw [hpow]
      by_cases h : w (k + n)
      · simp [h]
      · simp only [h]
        positivity
    have hsum : (∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + n + 1)) = (1 : ℝ) / 2 ^ n := by
      have h0 : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      have hc : ∀ k : ℕ, ((1 : ℝ) / 2) ^ (k + n + 1)
          = ((1 : ℝ) / 2) ^ k * ((1 : ℝ) / 2) ^ (n + 1) := by
        intro k
        rw [← pow_add]
        ring_nf
      rw [tsum_congr hc, h0.tsum_mul_right,
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      have h2 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
      rw [h2, pow_succ]
      field_simp
      rw [← mul_pow]
      norm_num
    calc (∑' k : ℕ, (if w (k + n) then (1 : ℝ) / 2 ^ (k + n + 1) else 0))
        ≤ ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + n + 1) :=
          Summable.tsum_le_tsum hdom ((summable_nat_add_iff n).2 hS) hgeom
      _ = (1 : ℝ) / 2 ^ n := hsum
  rw [hcast, ← hsplit]
  have hshift : (∑' k : ℕ, (if w (k + n) then (1 : ℝ) / 2 ^ (k + n + 1) else 0))
      = ∑' k : ℕ, (if w (k + n) then (1 : ℝ) / 2 ^ ((k + n) + 1) else 0) := rfl
  rw [← hshift] at htail
  linarith [htail]

/-! ### A bounded search -/

/-- The least `i ≤ k` at which the test fires, and `k` if it never does (in the shape
`Computable.nat_rec` accepts, with `p` as the recursion parameter). -/
def leastUpTo {σ : Type} (P : σ → ℕ → Bool) (p : σ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cond (P p (leastUpTo P p k)) (leastUpTo P p k) (k + 1)

variable {σ : Type}

/-- The bounded least-index search never returns more than its bound. -/
theorem leastUpTo_le (P : σ → ℕ → Bool) (p : σ) : ∀ k, leastUpTo P p k ≤ k := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rcases h : P p (leastUpTo P p k) with _ | _
      · rw [leastUpTo, h]
        exact le_rfl
      · rw [leastUpTo, h]
        exact le_trans ih (Nat.le_succ k)


/-- Either the search found a witness, or the test is false throughout `[0, k]`. -/
theorem leastUpTo_spec (P : σ → ℕ → Bool) (p : σ) :
    ∀ k, P p (leastUpTo P p k) = true ∨ ∀ i, i ≤ k → P p i = false := by
  intro k
  induction k with
  | zero =>
      rcases h : P p 0 with _ | _
      · exact Or.inr (fun i hi => by rw [Nat.le_zero.1 hi]; exact h)
      · exact Or.inl h
  | succ k ih =>
      rcases ih with hl | hr
      · refine Or.inl ?_
        rw [leastUpTo, hl]
        exact hl
      · have h0 : P p (leastUpTo P p k) = false := hr _ (leastUpTo_le P p k)
        have heq : leastUpTo P p (k + 1) = k + 1 := by rw [leastUpTo, h0]; rfl
        rcases h : P p (k + 1) with _ | _
        · refine Or.inr (fun i hi => ?_)
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with h' | h'
          · exact hr i (Nat.lt_succ_iff.1 h')
          · rw [h']; exact h
        · exact Or.inl (by rw [heq]; exact h)

/-- The bounded least-index search of a computable test is computable. -/
theorem computable_leastUpTo [Primcodable σ] {P : σ → ℕ → Bool} (hP : Computable₂ P) :
    Computable (fun q : σ × ℕ => leastUpTo P q.1 q.2) := by
  have hIH : Computable (fun s : (σ × ℕ) × ℕ × ℕ => s.2.2) := Computable.snd.comp Computable.snd
  have hy : Computable (fun s : (σ × ℕ) × ℕ × ℕ => s.2.1 + 1) :=
    Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)
  have hP' : Computable (fun s : (σ × ℕ) × ℕ × ℕ => P s.1.1 s.2.2) :=
    hP.comp (Computable.fst.comp Computable.fst) hIH
  have hstep : Computable₂ (fun (q : σ × ℕ) (r : ℕ × ℕ) => cond (P q.1 r.2) r.2 (r.1 + 1)) :=
    Computable.cond hP' hIH hy
  have hrec := Computable.nat_rec (σ := ℕ) Computable.snd (Computable.const 0) hstep
  refine hrec.of_eq (fun q => ?_)
  obtain ⟨p, n⟩ := q
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℕ) 0
      (fun y IH => cond (P p IH) IH (y + 1)) m) = leastUpTo P p m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [leastUpTo]; rw [ih]
  exact key n

/-! ### Rational dyadics and the diagonal stage sum -/

/-- The rational number `n / 2 ^ s`. -/
def ratOfDyadic (n s : ℕ) : ℚ := (n : ℚ) / 2 ^ s

/-- The dyadic rational `n / 2 ^ s` is nonnegative. -/
theorem ratOfDyadic_nonneg (n s : ℕ) : 0 ≤ ratOfDyadic n s := by
  rw [ratOfDyadic]
  positivity

/-- A dyadic rational with numerator zero is zero. -/
@[simp] theorem ratOfDyadic_zero (s : ℕ) : ratOfDyadic 0 s = 0 := by
  rw [ratOfDyadic]
  simp

/-- The extended-nonnegative value of the dyadic rational `n / 2 ^ s` is `dyadicValue n s`. -/
theorem ofReal_ratOfDyadic (n s : ℕ) :
    ENNReal.ofReal ((ratOfDyadic n s : ℚ) : ℝ) = dyadicValue n s := by
  rw [← ofReal_toReal_dyadicValue n s]
  congr 1
  rw [ratOfDyadic]
  push_cast
  ring

/-- The sequence `s ↦ 2 ^ -s` of rationals is computable. -/
theorem computable_invPow2 : Computable (fun s : ℕ => (1 : ℚ) / 2 ^ s) := by
  have hnat : Primrec (fun s : ℕ => 2 ^ s) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun s : ℕ => 2 ^ s)
    (Computable.const 1) hnat.to_comp (fun _ => by positivity) (fun s => ?_)
  push_cast
  ring

/-- The dyadic rational `n / 2 ^ s` is computable in both arguments. -/
theorem computable₂_ratOfDyadic : Computable₂ ratOfDyadic := by
  have hnum : Computable (fun p : ℕ × ℕ => ((p.1 : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp Computable.fst
  have hden : Computable (fun p : ℕ × ℕ => (1 : ℚ) / 2 ^ p.2) :=
    computable_invPow2.comp Computable.snd
  refine (Computable₂.comp computable₂_ratMul hnum hden).of_eq (fun p => ?_)
  rw [ratOfDyadic]
  ring

/-- `∑_{k < n} A s k / 2 ^ s`, in the shape `Computable.nat_rec` accepts. -/
def diagSum (A : ℕ → ℕ → ℕ) (s : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => diagSum A s k + ratOfDyadic (A s k) s

/-- The recursively defined stage sum agrees with the sum of the dyadic masses over
`Finset.range`. -/
theorem diagSum_eq (A : ℕ → ℕ → ℕ) (s n : ℕ) :
    diagSum A s n = ∑ k ∈ Finset.range n, ratOfDyadic (A s k) s := by
  induction n with
  | zero => simp [diagSum]
  | succ n ih => rw [diagSum, ih, Finset.sum_range_succ]

/-- The diagonal stage sum of a computable mass matrix is computable. -/
theorem computable_diagSum_diag {A : ℕ → ℕ → ℕ}
    (hA : Computable (fun p : ℕ × ℕ => A p.1 p.2)) :
    Computable (fun s : ℕ => diagSum A s s) := by
  have hAstep : Computable (fun z : ℕ × ℕ × ℚ => A z.1 z.2.1) :=
    hA.comp (Computable.fst.pair (Computable.fst.comp Computable.snd))
  have hval : Computable (fun z : ℕ × ℕ × ℚ => ratOfDyadic (A z.1 z.2.1) z.1) :=
    Computable₂.comp computable₂_ratOfDyadic hAstep Computable.fst
  have hIH : Computable (fun z : ℕ × ℕ × ℚ => z.2.2) := Computable.snd.comp Computable.snd
  have hstep : Computable₂ (fun (s : ℕ) (r : ℕ × ℚ) => r.2 + ratOfDyadic (A s r.1) s) :=
    Computable₂.comp computable₂_ratAdd hIH hval
  have hrec := Computable.nat_rec (σ := ℚ) Computable.id (Computable.const 0) hstep
  refine hrec.of_eq (fun s => ?_)
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) 0
      (fun y IH => IH + ratOfDyadic (A s y) s) m) = diagSum A s m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [diagSum]; rw [ih]
  exact key s

/-! ### The partial computable map of SUV p. 157 -/

/-- The least index `i ≤ 2 ^ s` that has received no mass by stage `s`. -/
def omegaZero (A : ℕ → ℕ → ℕ) (s : ℕ) : ℕ :=
  leastUpTo (fun s i => decide (A s i = 0)) s (2 ^ (s + 1))

/-- The probe of stage `s`: fire as soon as the stage-`s` mass exceeds
`bitsValue x − 2^{-|x|}`, and then answer with an index that has received no mass. -/
def omegaProbe (A : ℕ → ℕ → ℕ) (x : BitString) (s : ℕ) : Option ℕ :=
  cond (ratLtPair (bitsValue x - 1 / 2 ^ x.length, diagSum A s s)) (some (omegaZero A s)) none

/-- "From the first `n` bits of `Ω`, compute an integer of large prefix complexity": the
map is *partial*, because on strings that are not prefixes of `Ω` the search may run
forever. -/
def omegaSearch (A : ℕ → ℕ → ℕ) (x : BitString) : Part ℕ := Nat.rfindOpt (omegaProbe A x)

/-- The least index without mass at stage `s` is computable. -/
theorem computable_omegaZero {A : ℕ → ℕ → ℕ}
    (hA : Computable (fun p : ℕ × ℕ => A p.1 p.2)) : Computable (omegaZero A) := by
  have heq : Computable₂ (fun (s : ℕ) (i : ℕ) => decide (A s i = 0)) := by
    have h1 : Computable (fun q : ℕ × ℕ => A q.1 q.2) := hA
    have h2 : Computable₂ (fun x y : ℕ => decide (x = y)) :=
      (PrimrecRel.decide (Primrec.eq (α := ℕ))).to_comp
    exact Computable₂.comp h2 h1 (Computable.const 0)
  have hpow : Computable (fun s : ℕ => 2 ^ (s + 1)) :=
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.succ).to_comp
  have h := (computable_leastUpTo heq).comp (Computable.id.pair hpow)
  exact h.of_eq (fun s => rfl)

/-- The stage probe is computable in the prefix and the stage. -/
theorem computable₂_omegaProbe {A : ℕ → ℕ → ℕ}
    (hA : Computable (fun p : ℕ × ℕ => A p.1 p.2)) : Computable₂ (omegaProbe A) := by
  have hv : Computable (fun q : BitString × ℕ => bitsValue q.1) :=
    computable_bitsValue.comp Computable.fst
  have hlen : Computable (fun q : BitString × ℕ => (1 : ℚ) / 2 ^ q.1.length) :=
    computable_invPow2.comp (Primrec.list_length.to_comp.comp Computable.fst)
  have hleft := Computable₂.comp computable₂_ratSub hv hlen
  have hright : Computable (fun q : BitString × ℕ => diagSum A q.2 q.2) :=
    (computable_diagSum_diag hA).comp Computable.snd
  have htest := computable_ratLtPair.comp (Computable.pair hleft hright)
  have hz : Computable (fun q : BitString × ℕ => some (omegaZero A q.2)) :=
    Computable.option_some.comp ((computable_omegaZero hA).comp Computable.snd)
  have h := Computable.cond htest hz
    (Computable.const (none : Option ℕ) : Computable (fun _ : BitString × ℕ => (none : Option ℕ)))
  exact h.of_eq (fun q => rfl)

/-- The search that reads an integer of large prefix complexity out of a prefix of `Ω` is partial
recursive. -/
theorem partrec_omegaSearch {A : ℕ → ℕ → ℕ}
    (hA : Computable (fun p : ℕ × ℕ => A p.1 p.2)) : Partrec (omegaSearch A) :=
  Partrec.rfindOpt (computable₂_omegaProbe hA)

/-- What a value of the search means: some stage fired, and the answer is an index that
had received no mass at that stage. -/
theorem omegaSearch_spec {A : ℕ → ℕ → ℕ} {x : BitString} {i : ℕ} (h : i ∈ omegaSearch A x) :
    ∃ s : ℕ, bitsValue x - 1 / 2 ^ x.length < diagSum A s s ∧ i = omegaZero A s := by
  obtain ⟨s, hs⟩ := Nat.rfindOpt_spec h
  refine ⟨s, ?_, ?_⟩
  · rcases ht : ratLtPair (bitsValue x - 1 / 2 ^ x.length, diagSum A s s) with _ | _
    · rw [omegaProbe, ht] at hs
      exact absurd hs (by simp)
    · rw [ratLtPair] at ht
      exact of_decide_eq_true ht
  · rcases ht : ratLtPair (bitsValue x - 1 / 2 ^ x.length, diagSum A s s) with _ | _
    · rw [omegaProbe, ht] at hs
      exact absurd hs (by simp)
    · rw [omegaProbe, ht] at hs
      exact (Option.some_inj.1 hs).symm

/-- The search terminates as soon as some stage fires. -/
theorem omegaSearch_dom {A : ℕ → ℕ → ℕ} {x : BitString} {s : ℕ}
    (h : bitsValue x - 1 / 2 ^ x.length < diagSum A s s) : ∃ i, i ∈ omegaSearch A x := by
  have hprobe : omegaProbe A x s = some (omegaZero A s) := by
    have ht : ratLtPair (bitsValue x - 1 / 2 ^ x.length, diagSum A s s) = true := by
      rw [ratLtPair]
      exact decide_eq_true h
    rw [omegaProbe, ht]
    rfl
  have hdom : (omegaSearch A x).Dom := Nat.rfindOpt_dom.2 ⟨s, omegaZero A s, by rw [hprobe]; rfl⟩
  exact ⟨(omegaSearch A x).get hdom, Part.get_mem hdom⟩

/-! ### The estimate of SUV p. 157 -/

/-- Doubling the numerator doubles the dyadic value. -/
theorem dyadicValue_mul_two_num (n s : ℕ) : dyadicValue (2 * n) s = 2 * dyadicValue n s := by
  rw [dyadicValue, dyadicValue]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

/-- Some index `≤ 2^{s+1}` has received no mass by stage `s`: otherwise the stage-`s` mass
would be at least `2`. -/
theorem omegaZero_spec {A : ℕ → ℕ → ℕ} {m : ℕ → ℝ≥0∞}
    (hle : ∀ s i, dyadicValue (A s i) s ≤ m i) (hmass : (∑' k, m k) ≤ 1) (s : ℕ) :
    A s (omegaZero A s) = 0 := by
  rcases leastUpTo_spec (fun s i => decide (A s i = 0)) s (2 ^ (s + 1)) with h | h
  · exact of_decide_eq_true h
  · exfalso
    have hone : ∀ i ∈ Finset.range (2 ^ (s + 1)), 1 ≤ A s i := by
      intro i hi
      have := h i (le_of_lt (Finset.mem_range.1 hi))
      have hne : ¬ (A s i = 0) := of_decide_eq_false this
      omega
    have hsum : 2 ^ (s + 1) ≤ ∑ i ∈ Finset.range (2 ^ (s + 1)), A s i := by
      calc 2 ^ (s + 1) = ∑ _i ∈ Finset.range (2 ^ (s + 1)), 1 := by simp
        _ ≤ ∑ i ∈ Finset.range (2 ^ (s + 1)), A s i := Finset.sum_le_sum hone
    have hdy : (2 : ℝ≥0∞) ≤ ∑ i ∈ Finset.range (2 ^ (s + 1)), dyadicValue (A s i) s := by
      rw [← dyadicValue_sum]
      have h2 : dyadicValue (2 ^ (s + 1)) s = 2 := by
        have hpow : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by ring
        rw [hpow, dyadicValue_mul_two_num, dyadicValue_two_pow_self, mul_one]
      rw [← h2]
      exact dyadicValue_le_of_le hsum
    have hle' : ∑ i ∈ Finset.range (2 ^ (s + 1)), dyadicValue (A s i) s ≤ ∑' k, m k :=
      le_trans (Finset.sum_le_sum (fun i _ => hle s i))
        (ENNReal.sum_le_tsum (Finset.range (2 ^ (s + 1))))
    have : (2 : ℝ≥0∞) ≤ 1 := le_trans hdy (le_trans hle' hmass)
    exact absurd this (by norm_num)

/-- The extended-nonnegative value of a stage sum is the sum of the dyadic masses. -/
theorem ofReal_diagSum {A : ℕ → ℕ → ℕ} (s n : ℕ) :
    ENNReal.ofReal ((diagSum A s n : ℚ) : ℝ)
      = ∑ k ∈ Finset.range n, dyadicValue (A s k) s := by
  rw [diagSum_eq]
  have hnn : ∀ k ∈ Finset.range n, (0 : ℝ) ≤ ((ratOfDyadic (A s k) s : ℚ) : ℝ) :=
    fun k _ => by exact_mod_cast ratOfDyadic_nonneg _ _
  have hcast : (((∑ k ∈ Finset.range n, ratOfDyadic (A s k) s : ℚ)) : ℝ)
      = ∑ k ∈ Finset.range n, ((ratOfDyadic (A s k) s : ℚ) : ℝ) := by push_cast; ring
  rw [hcast, ENNReal.ofReal_sum_of_nonneg hnn]
  exact Finset.sum_congr rfl (fun k _ => ofReal_ratOfDyadic _ _)

/-- The mass already accounted for at stage `s`, plus the mass of an index that has
received nothing, is at most the total mass. -/
theorem diagSum_add_mass_le {A : ℕ → ℕ → ℕ} {m : ℕ → ℝ≥0∞} {s : ℕ}
    (hle : ∀ s i, dyadicValue (A s i) s ≤ m i) (hz : A s (omegaZero A s) = 0) :
    ENNReal.ofReal ((diagSum A s s : ℚ) : ℝ) + m (omegaZero A s) ≤ ∑' k, m k := by
  classical
  set i := omegaZero A s with hi
  set f : ℕ → ℝ≥0∞ := fun k => (if k < s then dyadicValue (A s k) s else 0) with hf
  set g : ℕ → ℝ≥0∞ := fun k => (if k = i then m k else 0) with hg
  have hfval : ∀ k, f k = if k < s then dyadicValue (A s k) s else 0 := fun _ => rfl
  have hgval : ∀ k, g k = if k = i then m k else 0 := fun _ => rfl
  have hfg : ∀ k, f k + g k ≤ m k := by
    intro k
    rw [hfval k, hgval k]
    by_cases hk : k = i
    · rw [if_pos hk]
      have hz0 : (if k < s then dyadicValue (A s k) s else 0) = 0 := by
        by_cases hks : k < s
        · rw [if_pos hks, hk, hz, dyadicValue_zero]
        · rw [if_neg hks]
      rw [hz0, zero_add]
    · rw [if_neg hk, add_zero]
      by_cases hks : k < s
      · rw [if_pos hks]
        exact hle s k
      · rw [if_neg hks]
        exact zero_le
  have hsum : (∑' k, f k) + (∑' k, g k) ≤ ∑' k, m k := by
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum hfg
  have hfsum : (∑' k, f k) = ∑ k ∈ Finset.range s, dyadicValue (A s k) s := by
    rw [tsum_eq_sum (s := Finset.range s)
      (fun k hk => by rw [hfval k, if_neg (by simpa using hk)])]
    exact Finset.sum_congr rfl (fun k hk => by rw [hfval k, if_pos (Finset.mem_range.1 hk)])
  have hgsum : (∑' k, g k) = m i := by
    have := tsum_ite_eq i m
    rw [hg]
    exact this
  rw [ofReal_diagSum, ← hfsum, ← hgsum]
  exact hsum

/-- **The estimate of SUV p. 157.**  If the string `x` sandwiches the total mass between
`bitsValue x` and `bitsValue x + 2^{-|x|}`, then any value of the search at `x` is an
index of mass at most `2 · 2^{-|x|}`. -/
theorem omegaSearch_mass_le {A : ℕ → ℕ → ℕ} {m : ℕ → ℝ≥0∞} {x : BitString} {i : ℕ}
    (hle : ∀ s i, dyadicValue (A s i) s ≤ m i) (hmass : (∑' k, m k) ≤ 1)
    (hhigh : (∑' k, m k)
      ≤ ENNReal.ofReal (((bitsValue x : ℚ) : ℝ) + (1 : ℝ) / 2 ^ x.length))
    (hi : i ∈ omegaSearch A x) :
    m i ≤ ENNReal.ofReal (2 * ((1 : ℝ) / 2 ^ x.length)) := by
  obtain ⟨s, hfire, rfl⟩ := omegaSearch_spec hi
  have hz := omegaZero_spec hle hmass s
  have hkey := diagSum_add_mass_le hle hz
  set v : ℝ := ((bitsValue x : ℚ) : ℝ) with hv
  set p : ℝ := (1 : ℝ) / 2 ^ x.length with hp
  have hppos : (0 : ℝ) < p := by rw [hp]; positivity
  have hfireR : v - p < ((diagSum A s s : ℚ) : ℝ) := by
    rw [hv, hp]
    have : ((bitsValue x - 1 / 2 ^ x.length : ℚ) : ℝ) < ((diagSum A s s : ℚ) : ℝ) := by
      exact_mod_cast hfire
    push_cast at this
    linarith
  have hchain : ENNReal.ofReal (v - p) + m (omegaZero A s) ≤ ENNReal.ofReal (v + p) := by
    refine le_trans (add_le_add (ENNReal.ofReal_le_ofReal hfireR.le) le_rfl) ?_
    exact le_trans hkey hhigh
  rcases lt_or_ge p v with hvp | hvp
  · have hnn : (0 : ℝ) ≤ v - p := by linarith
    have hsplit : ENNReal.ofReal (v + p) = ENNReal.ofReal (v - p) + ENNReal.ofReal (2 * p) := by
      rw [← ENNReal.ofReal_add hnn (by positivity)]
      congr 1
      ring
    rw [hsplit] at hchain
    have hfin : ENNReal.ofReal (v - p) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [add_comm (ENNReal.ofReal (v - p)) (m (omegaZero A s)),
      add_comm (ENNReal.ofReal (v - p)) (ENNReal.ofReal (2 * p))] at hchain
    exact (ENNReal.add_le_add_iff_right hfin).1 hchain
  · refine le_trans (le_trans le_add_self hchain) (ENNReal.ofReal_le_ofReal ?_)
    linarith

/-! ### Termination of the search -/

/-- Stage sums are nonnegative. -/
theorem diagSum_nonneg (A : ℕ → ℕ → ℕ) (s n : ℕ) : 0 ≤ diagSum A s n := by
  rw [diagSum_eq]
  exact Finset.sum_nonneg (fun k _ => ratOfDyadic_nonneg _ _)

/-- A mass matrix that never loses mass from one stage to the next has monotone dyadic masses at
each index. -/
theorem dyadicValue_mono_stage {A : ℕ → ℕ → ℕ}
    (hmono : ∀ s i, dyadicValue (A s i) s ≤ dyadicValue (A (s + 1) i) (s + 1)) (i : ℕ) :
    Monotone (fun s => dyadicValue (A s i) s) :=
  monotone_nat_of_le_succ (fun s => hmono s i)

/-- The diagonal stage sums converge to the total mass, so the search of `omegaProbe`
fires at some stage whenever its threshold is below the total mass. -/
theorem exists_lt_diagSum {A : ℕ → ℕ → ℕ} {m : ℕ → ℝ≥0∞}
    (hmono : ∀ s i, dyadicValue (A s i) s ≤ dyadicValue (A (s + 1) i) (s + 1))
    (hsup : ∀ i, ⨆ s, dyadicValue (A s i) s = m i)
    {t : ℝ} (ht : ENNReal.ofReal t < ∑' k, m k) :
    ∃ s : ℕ, t < ((diagSum A s s : ℚ) : ℝ) := by
  rw [ENNReal.tsum_eq_iSup_nat] at ht
  obtain ⟨N, hN⟩ := lt_iSup_iff.1 ht
  have hswap : (∑ k ∈ Finset.range N, m k)
      = ⨆ s, ∑ k ∈ Finset.range N, dyadicValue (A s k) s := by
    rw [← ENNReal.finsetSum_iSup_of_monotone (fun k => dyadicValue_mono_stage hmono k)]
    exact Finset.sum_congr rfl (fun k _ => (hsup k).symm)
  rw [hswap] at hN
  obtain ⟨s, hs⟩ := lt_iSup_iff.1 hN
  refine ⟨max N s, ?_⟩
  have hmono2 : ∀ k, dyadicValue (A s k) s ≤ dyadicValue (A (max N s) k) (max N s) :=
    fun k => dyadicValue_mono_stage hmono k (le_max_right N s)
  have hsubset : Finset.range N ⊆ Finset.range (max N s) := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) (le_max_left N s))
  have hstep : ∑ k ∈ Finset.range N, dyadicValue (A s k) s
      ≤ ∑ k ∈ Finset.range (max N s), dyadicValue (A (max N s) k) (max N s) :=
    le_trans (Finset.sum_le_sum (fun k _ => hmono2 k))
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => zero_le))
  have hlt : ENNReal.ofReal t
      < ENNReal.ofReal ((diagSum A (max N s) (max N s) : ℚ) : ℝ) := by
    rw [ofReal_diagSum]
    exact lt_of_lt_of_le hs hstep
  rcases lt_or_ge t 0 with h0 | h0
  · have hnn : (0 : ℝ) ≤ ((diagSum A (max N s) (max N s) : ℚ) : ℝ) := by
      exact_mod_cast diagSum_nonneg A (max N s) (max N s)
    linarith
  · exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).1 hlt

/-! ### The counting step -/

/-- The extended-nonnegative value of `2 * 2 ^ -n` is `2 * 2 ^ -n`. -/
theorem ofReal_two_mul_inv_pow (n : ℕ) :
    ENNReal.ofReal (2 * ((1 : ℝ) / 2 ^ n)) = 2 * (2 : ℝ≥0∞)⁻¹ ^ n := by
  have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  have hpow : ENNReal.ofReal ((1 : ℝ) / 2 ^ n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
    rw [show ((1 : ℝ) / 2 ^ n) = ((1 : ℝ) / 2) ^ n by rw [div_pow, one_pow],
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1 / 2), hhalf]
  rw [ENNReal.ofReal_mul (by norm_num), hpow]
  congr 1
  norm_num

/-- The counting step of SUV p. 157: if the semimeasure of an index is at most
`2 · 2^{-n}` while the coding theorem bounds it below by `c · 2^{-K(i)}`, then
`n ≤ K(i) + O(1)`, with the constant depending only on `c`. -/
theorem exists_const_le_of_weight {cc : ℝ≥0∞} (hcc : 0 < cc) :
    ∃ c₀ : ℕ, ∀ (k : ENat) (n : ℕ),
      cc * complexityWeight k ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ n → (n : ENat) ≤ k + (c₀ : ENat) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (2 : ℝ≥0∞)⁻¹ ^ N < cc := ENNReal.exists_inv_two_pow_lt hcc.ne'
  refine ⟨N + 1, fun k n hk => ?_⟩
  by_contra hcon
  push Not at hcon
  -- `k` must be finite, and `k + N + 2 ≤ n`
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ENat) := by
    cases k with
    | top => exact absurd hcon (by simp)
    | coe j => exact ⟨j, rfl⟩
  have hjn : j + (N + 1) < n := by exact_mod_cast hcon
  have hpow : (2 : ℝ≥0∞)⁻¹ ^ n ≤ (2 : ℝ≥0∞)⁻¹ ^ j * (2 : ℝ≥0∞)⁻¹ ^ (N + 1) := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one (zero_le) (ENNReal.inv_le_one.2 (by norm_num))
      (le_of_lt hjn)
  rw [complexityWeight_coe] at hk
  have hchain : cc * (2 : ℝ≥0∞)⁻¹ ^ j
      ≤ (2 * (2 : ℝ≥0∞)⁻¹ ^ (N + 1)) * (2 : ℝ≥0∞)⁻¹ ^ j := by
    refine le_trans hk ?_
    calc 2 * (2 : ℝ≥0∞)⁻¹ ^ n
        ≤ 2 * ((2 : ℝ≥0∞)⁻¹ ^ j * (2 : ℝ≥0∞)⁻¹ ^ (N + 1)) := by
          exact mul_le_mul_right hpow 2
      _ = (2 * (2 : ℝ≥0∞)⁻¹ ^ (N + 1)) * (2 : ℝ≥0∞)⁻¹ ^ j := by ring
  have hne0 : ((2 : ℝ≥0∞)⁻¹ ^ j) ≠ 0 := by
    refine pow_ne_zero j ?_
    simp
  have hnetop : ((2 : ℝ≥0∞)⁻¹ ^ j) ≠ ⊤ := by
    refine ENNReal.pow_ne_top ?_
    simp
  have hcc' : cc ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ (N + 1) :=
    (ENNReal.mul_le_mul_iff_left hne0 hnetop).1 hchain
  have h2inv : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hval : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (N + 1) = (2 : ℝ≥0∞)⁻¹ ^ N := by
    rw [pow_succ]
    calc (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ N * (2 : ℝ≥0∞)⁻¹)
        = ((2 : ℝ≥0∞)⁻¹ ^ N) * ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) := by ring
      _ = (2 : ℝ≥0∞)⁻¹ ^ N := by rw [h2inv, mul_one]
  rw [hval] at hcc'
  exact absurd hN (not_lt.2 hcc')

end Kolmogorov
