/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Infra
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.MaximalSumTest
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaPrefixCore

/-!
# Maximality of `sup_{x ⊑ ω} m(x)/p(x)` (SUV Problem 147, p. 150)

The source's hint, verbatim:

> A lower semicomputable function that is equal to `a` inside some effectively open set and is
> equal to zero outside it can be represented by means of weights that are equal to `a` and are
> placed in incompatible vertices.  Every lower semicomputable function can be represented up to
> a `Θ(1)`-factor as the sum `t(ω) = ∑_k t_k(ω)`, where `t_k(ω) = 2^k` if `t(ω) > 2^k` and
> `t_k(ω) = 0` otherwise.  If all `t_k` are represented as explained above, all the summands in
> the formula for the deficiency are powers of two.  Then the sum equals the supremum up to a
> `Θ(1)`-factor.

Problem 146's maximality (`maximal_prefixSumRatio`) does **not** give this, because
`prefixSupRatio ≤ prefixSumRatio` goes the wrong way.

The argument is carried out here with the *antichain of first crossings* made explicit, which
removes every enumeration subtlety.  SUV Theorem 40 writes an expectation-bounded test `v` as
`v ω = ∑_s u((ω)_s)` with `u x = vertexWeight term x` an **exactly computable** dyadic rational
at the known scale `|x|`.  Hence the running partial sum

`w(x) = ∑_{y ⊑ x} u(y) = prefixNum term x / 2^{|x|}` (`supPartial`)

is again exactly computable, with numerator `prefixNum term x : ℕ`, and `v ω = sup_n w((ω)_n)`.
Rounding `w` down to the nearest power of two,

`d(x) = pow2Floor (prefixNum term x) / 2^{|x|}` (`supFloor`),

gives `d ≤ w ≤ 2·d` and a *doubling staircase* along every branch: `d` increases along the tree
and every strict increase at least doubles it.  Its increments

`u*(x) = d(x) − d(x⁻)` (`supVertex`, numerator `supVertexNum`)

are exactly the source's weights "equal to `a`, placed in incompatible vertices": along a branch
they telescope to `d`, so `∑_x u*(x)·p(x) = sup_N ∫ d((ω)_N) dμ ≤ ∫ v dμ ≤ 1`, i.e.
`x ↦ u*(x)·p(x)` is a lower semicomputable semimeasure and `m` dominates it.  Because the
staircase doubles, its *last* step already carries half of its total
(`exists_le_two_mul_of_jump`), so

`v ω = sup_n w((ω)_n) ≤ 2·sup_n d((ω)_n) ≤ 4·sup_j u*((ω)_j) ≤ 2^{k+2}·sup_j m((ω)_j)/p((ω)_j)`.

## Main results

* `pow2Floor` and its arithmetic (`pow2Floor_le`, `le_two_mul_pow2Floor`,
  `two_mul_pow2Floor_le`, `pow2Floor_jump`);
* `computable_nat_size` — `Nat.size` is computable;
* `prefixNum` — the exactly computable numerator of the running partial sum, and
  `dyadicValue_prefixNum_cantorPrefix`;
* `exists_le_two_mul_of_jump` — the sum of a doubling staircase is at most twice its last step;
* `tsum_supVertex_mul_cantorMass_le` — the telescoping mass bound;
* `maximal_prefixSupRatio` and `problem_147_maximal_prefixSupRatio'` — Problem 147's maximality.
-/

namespace Kolmogorov

open MeasureTheory

open scoped ENNReal NNReal

/-! ### Dyadic bookkeeping -/

/-! ### `Nat.size` is computable -/

/-- One halving step of the binary-length computation: halve the running value and increment
the counter, unless the value has already reached `0`. -/
def sizeHalveStep (p : ℕ × ℕ) : ℕ × ℕ := if p.1 = 0 then p else (p.1 / 2, p.2 + 1)

/-- Iterating the halving step enough times computes `Nat.size`. -/
lemma sizeHalveStep_iterate (k : ℕ) : ∀ x acc : ℕ, x < 2 ^ k →
    sizeHalveStep^[k] (x, acc) = (0, acc + Nat.size x) := by
  induction k with
  | zero =>
    intro x acc hx
    simp only [pow_zero, Nat.lt_one_iff] at hx
    subst hx
    simp
  | succ k ih =>
    intro x acc hx
    rw [Function.iterate_succ_apply]
    by_cases h : x = 0
    · subst h
      have h0 : sizeHalveStep ((0 : ℕ), acc) = (0, acc) := by simp [sizeHalveStep]
      rw [h0, ih 0 acc (by positivity)]
    · have h1 : sizeHalveStep (x, acc) = (x / 2, acc + 1) := by simp [sizeHalveStep, h]
      have h2 : x / 2 < 2 ^ k := Nat.div_lt_of_lt_mul (by rw [pow_succ] at hx; omega)
      rw [h1, ih (x / 2) (acc + 1) h2, nat_size_div_two x h]
      congr 1
      omega

/-- The halving step is primitive recursive. -/
lemma primrec_sizeHalveStep : Primrec sizeHalveStep := by
  unfold sizeHalveStep
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) Primrec.id
    (Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))

/-! ### The largest power of two below a natural number -/

/-- `pow2Floor n` is the largest power of two that is at most `n`, and `0` for `n = 0`.  This is
the rounding that turns the running partial sum into a doubling staircase. -/
def pow2Floor (n : ℕ) : ℕ := if n = 0 then 0 else 2 ^ (Nat.size n - 1)

/-- Every value of `pow2Floor` is `0` or a power of two. -/
lemma pow2Floor_eq_zero_or_pow (n : ℕ) :
    pow2Floor n = 0 ∨ ∃ j : ℕ, pow2Floor n = 2 ^ j := by
  rw [pow2Floor]
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr ⟨Nat.size n - 1, rfl⟩

/-- `pow2Floor n ≤ n`. -/
lemma pow2Floor_le (n : ℕ) : pow2Floor n ≤ n := by
  rw [pow2Floor]
  split_ifs with h
  · exact Nat.zero_le _
  · have hpos : 0 < Nat.size n := Nat.size_pos.mpr (Nat.pos_of_ne_zero h)
    exact Nat.lt_size.mp (by omega)

/-- `n ≤ 2 · pow2Floor n`: the rounding loses at most a factor of two. -/
lemma le_two_mul_pow2Floor (n : ℕ) : n ≤ 2 * pow2Floor n := by
  rw [pow2Floor]
  split_ifs with h
  · omega
  · have hpos : 0 < Nat.size n := Nat.size_pos.mpr (Nat.pos_of_ne_zero h)
    have hlt : n < 2 ^ Nat.size n := Nat.lt_size_self n
    have he : (2 : ℕ) ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

/-- `pow2Floor` transports the doubling of the numerator along a tree edge. -/
lemma two_mul_pow2Floor_le {a b : ℕ} (h : 2 * a ≤ b) : 2 * pow2Floor a ≤ pow2Floor b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · simp [pow2Floor, ha]
  · have hb : b ≠ 0 := by omega
    have ha' : a ≠ 0 := by omega
    have hsa : 0 < Nat.size a := Nat.size_pos.mpr ha
    have h1 : 2 ^ (Nat.size a - 1) ≤ a := Nat.lt_size.mp (by omega)
    have h2 : (2 : ℕ) ^ Nat.size a = 2 * 2 ^ (Nat.size a - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : 2 ^ Nat.size a ≤ b := by omega
    have h4 : Nat.size a < Nat.size b := Nat.lt_size.mpr h3
    have h5 : (2 : ℕ) ^ Nat.size a ≤ 2 ^ (Nat.size b - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow2Floor, pow2Floor, ite_eq_right ha', ite_eq_right hb]
    omega

/-- A strict increase of `pow2Floor` past a doubling is itself at least a doubling: the values
are powers of two. -/
lemma pow2Floor_jump {a b : ℕ} (h : 2 * pow2Floor a < pow2Floor b) :
    2 * (2 * pow2Floor a) ≤ pow2Floor b := by
  rcases pow2Floor_eq_zero_or_pow a with ha | ⟨i, hi⟩
  · rw [ha]
    omega
  · rcases pow2Floor_eq_zero_or_pow b with hb | ⟨j, hj⟩
    · rw [hb] at h
      omega
    · rw [hi, hj] at h ⊢
      have hij : i + 1 < j := by
        by_contra hcon
        have hle : j ≤ i + 1 := by omega
        have hpow : (2 : ℕ) ^ j ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) hle
        rw [pow_succ] at hpow
        omega
      have hstep : (2 : ℕ) ^ (i + 2) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hval : (2 : ℕ) ^ (i + 2) = 2 * (2 * 2 ^ i) := by
        rw [pow_add]
        ring
      omega

/-- `Computable pow2Floor`. -/
lemma computable_pow2Floor : Computable pow2Floor := by
  have hsub : Computable₂ (fun u v : ℕ => u - v) := Primrec.nat_sub.to_comp
  have hpow : Computable (fun n : ℕ => 2 ^ (Nat.size n - 1)) :=
    primrec_two_pow_aux.to_comp.comp (hsub.comp computable_nat_size (Computable.const 1))
  have hlt : Computable₂ (fun u v : ℕ => decide (u < v)) := primrec_decide_nat_lt.to_comp
  have hcond : Computable (fun n : ℕ => decide (n < 1)) :=
    hlt.comp Computable.id (Computable.const 1)
  refine (Computable.cond hcond (Computable.const 0) hpow).of_eq fun n => ?_
  by_cases h : n = 0 <;> simp [pow2Floor, h]

/-! ### The running partial sum of the vertex weights -/

/-- `prefixNumAux term x n` is the numerator, at scale `n`, of the partial sum
`∑_{i ≤ n} u(x↾i)` of the vertex weights along the prefixes of `x`.  Each vertex weight is an
exactly known dyadic rational at a known scale, so the partial sum is again exact: no stage
approximation is involved. -/
def prefixNumAux (term : ℕ → BitString → ℕ) (x : BitString) : ℕ → ℕ
  | 0 => term 0 []
  | (i + 1) => 2 * prefixNumAux term x i + term (i + 1) (x.take (i + 1))

/-- The numerator of the running partial sum at the full length of `x`. -/
def prefixNum (term : ℕ → BitString → ℕ) (x : BitString) : ℕ :=
  prefixNumAux term x x.length

/-- Base equation of `prefixNumAux`. -/
lemma prefixNumAux_zero (term : ℕ → BitString → ℕ) (x : BitString) :
    prefixNumAux term x 0 = term 0 [] := rfl

/-- Step equation of `prefixNumAux`. -/
lemma prefixNumAux_succ (term : ℕ → BitString → ℕ) (x : BitString) (i : ℕ) :
    prefixNumAux term x (i + 1)
      = 2 * prefixNumAux term x i + term (i + 1) (x.take (i + 1)) := rfl

/-- `prefixNumAux term x n` depends on `x` only through `x.take n`. -/
lemma prefixNumAux_congr (term : ℕ → BitString → ℕ) (x y : BitString) :
    ∀ n : ℕ, x.take n = y.take n → prefixNumAux term x n = prefixNumAux term y n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      have hmin : min n (n + 1) = n := by omega
      have h' := congrArg (fun l : BitString => l.take n) h
      simp only [List.take_take, hmin] at h'
      rw [prefixNumAux_succ, prefixNumAux_succ, ih h', h]

/-- `prefixNumAux` written as the `Nat.rec` term the computability API produces. -/
lemma prefixNumAux_eq_rec (term : ℕ → BitString → ℕ) (x : BitString) (n : ℕ) :
    prefixNumAux term x n
      = Nat.rec (motive := fun _ => ℕ) (term 0 ([] : BitString))
          (fun i ih => 2 * ih + term (i + 1) (x.take (i + 1))) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prefixNumAux_succ, ih]

/-- `prefixNum term` is computable whenever `term` is. -/
lemma computable_prefixNum {term : ℕ → BitString → ℕ}
    (hterm : Computable fun p : ℕ × BitString => term p.1 p.2) :
    Computable (prefixNum term) := by
  have hlen : Computable (fun x : BitString => x.length) := Computable.list_length
  have hadd : Computable₂ (fun u v : ℕ => u + v) := Primrec.nat_add.to_comp
  have hmul : Computable₂ (fun u v : ℕ => u * v) := Primrec.nat_mul.to_comp
  have hidx : Computable (fun q : BitString × ℕ × ℕ => q.2.1 + 1) :=
    hadd.comp (Computable.fst.comp Computable.snd) (Computable.const 1)
  have htake : Computable (fun q : BitString × ℕ × ℕ => q.1.take (q.2.1 + 1)) :=
    (Primrec.list_take (α := Bool)).to_comp.comp hidx Computable.fst
  have hstep : Computable₂ (fun (x : BitString) (p : ℕ × ℕ) =>
      2 * p.2 + term (p.1 + 1) (x.take (p.1 + 1))) :=
    hadd.comp (hmul.comp (Computable.const 2) (Computable.snd.comp Computable.snd))
      (hterm.comp (Computable.pair hidx htake))
  have hrec := Computable.nat_rec (σ := ℕ) hlen
    (Computable.const (term 0 ([] : BitString))) hstep
  refine hrec.of_eq fun x => ?_
  exact (prefixNumAux_eq_rec term x x.length).symm

/-- `cantorPrefix w 0` is the empty string. -/
lemma cantorPrefix_zero_eq_nil (w : CantorSeq) : cantorPrefix w 0 = [] := by
  simp [cantorPrefix]

/-- The tree recursion of `prefixNum` along a branch: extending a prefix by one bit doubles the
numerator and adds the new vertex weight. -/
lemma prefixNum_cantorPrefix_succ (term : ℕ → BitString → ℕ) (w : CantorSeq) (n : ℕ) :
    prefixNum term (cantorPrefix w (n + 1))
      = 2 * prefixNum term (cantorPrefix w n) + term (n + 1) (cantorPrefix w (n + 1)) := by
  have hcong : prefixNumAux term (cantorPrefix w (n + 1)) n
      = prefixNumAux term (cantorPrefix w n) n := by
    refine prefixNumAux_congr term _ _ n ?_
    rw [cantorPrefix_take w n (n + 1) (Nat.le_succ n), cantorPrefix_take w n n le_rfl]
  simp only [prefixNum, cantorPrefix_length]
  rw [prefixNumAux_succ, hcong, cantorPrefix_take w (n + 1) (n + 1) le_rfl]

/-- Along a branch the numerator at least doubles at every step. -/
lemma two_mul_prefixNum_le (term : ℕ → BitString → ℕ) (w : CantorSeq) (n : ℕ) :
    2 * prefixNum term (cantorPrefix w n) ≤ prefixNum term (cantorPrefix w (n + 1)) := by
  rw [prefixNum_cantorPrefix_succ]
  omega

/-- The running partial sum really is the partial sum of the vertex weights. -/
lemma dyadicValue_prefixNum_cantorPrefix (term : ℕ → BitString → ℕ) (w : CantorSeq) (n : ℕ) :
    dyadicValue (prefixNum term (cantorPrefix w n)) n
      = ∑ i ∈ Finset.range (n + 1), vertexWeight term (cantorPrefix w i) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_one]
      simp only [prefixNum, cantorPrefix_length]
      rw [prefixNumAux_zero, vertexWeight, cantorPrefix_length, cantorPrefix_zero_eq_nil]
  | succ n ih =>
      rw [prefixNum_cantorPrefix_succ, dyadicValue_add, dyadicValue_two_mul_succ,
        Finset.sum_range_succ, ← ih]
      congr 1
      rw [vertexWeight, cantorPrefix_length]

/-! ### The doubling staircase and its increments -/

/-- The running partial sum `w(x) = ∑_{y ⊑ x} u(y)` of the vertex weights. -/
noncomputable def supPartial (term : ℕ → BitString → ℕ) (x : BitString) : ℝ≥0∞ :=
  dyadicValue (prefixNum term x) x.length

/-- The running partial sum rounded down to the nearest power of two — the source's
`t_k = 2^k` levels, collected into a single staircase. -/
noncomputable def supFloor (term : ℕ → BitString → ℕ) (x : BitString) : ℝ≥0∞ :=
  dyadicValue (pow2Floor (prefixNum term x)) x.length

/-- Twice the staircase numerator at the parent of `x` (and `0` at the root). -/
def supParentNum (term : ℕ → BitString → ℕ) (x : BitString) : ℕ :=
  if x.length = 0 then 0 else 2 * pow2Floor (prefixNum term (x.take (x.length - 1)))

/-- The numerator of the staircase increment `d(x) − d(x⁻)`.  These are the source's weights
"equal to `a`, placed in incompatible vertices": the increment is nonzero exactly at the
vertices where a new power of two is crossed for the first time. -/
def supVertexNum (term : ℕ → BitString → ℕ) (x : BitString) : ℕ :=
  pow2Floor (prefixNum term x) - supParentNum term x

/-- The staircase increment `d(x) − d(x⁻)` as an element of `ℝ≥0∞`. -/
noncomputable def supVertex (term : ℕ → BitString → ℕ) (x : BitString) : ℝ≥0∞ :=
  dyadicValue (supVertexNum term x) x.length

/-- The staircase is below the partial sum. -/
lemma supFloor_le_supPartial (term : ℕ → BitString → ℕ) (x : BitString) :
    supFloor term x ≤ supPartial term x :=
  dyadicValue_mono_nat (pow2Floor_le _) x.length

/-- The staircase is finite. -/
lemma supFloor_ne_top (term : ℕ → BitString → ℕ) (x : BitString) : supFloor term x ≠ ⊤ :=
  dyadicValue_ne_top _ _

/-- The staircase loses at most a factor of two. -/
lemma supPartial_le_two_mul_supFloor (term : ℕ → BitString → ℕ) (x : BitString) :
    supPartial term x ≤ 2 * supFloor term x := by
  rw [supPartial, supFloor, ← dyadicValue_mul_two_num]
  exact dyadicValue_mono_nat (le_two_mul_pow2Floor _) x.length

/-- The increment numerators telescope along a branch. -/
lemma supVertexNum_add (term : ℕ → BitString → ℕ) (w : CantorSeq) (n : ℕ) :
    supVertexNum term (cantorPrefix w (n + 1))
        + 2 * pow2Floor (prefixNum term (cantorPrefix w n))
      = pow2Floor (prefixNum term (cantorPrefix w (n + 1))) := by
  have hpar : supParentNum term (cantorPrefix w (n + 1))
      = 2 * pow2Floor (prefixNum term (cantorPrefix w n)) := by
    rw [supParentNum, ite_eq_right (by simp), cantorPrefix_length, Nat.add_sub_cancel,
      cantorPrefix_take w n (n + 1) (Nat.le_succ n)]
  rw [supVertexNum, hpar]
  exact Nat.sub_add_cancel (two_mul_pow2Floor_le (two_mul_prefixNum_le term w n))

/-- At the root the increment is the whole staircase. -/
lemma supVertex_cantorPrefix_zero (term : ℕ → BitString → ℕ) (w : CantorSeq) :
    supVertex term (cantorPrefix w 0) = supFloor term (cantorPrefix w 0) := by
  rw [supVertex, supFloor, supVertexNum, supParentNum, ite_eq_left (by simp), Nat.sub_zero]

/-- The telescoping identity `d((ω)_{n+1}) = u*((ω)_{n+1}) + d((ω)_n)`. -/
lemma supFloor_cantorPrefix_succ (term : ℕ → BitString → ℕ) (w : CantorSeq) (n : ℕ) :
    supFloor term (cantorPrefix w (n + 1))
      = supVertex term (cantorPrefix w (n + 1)) + supFloor term (cantorPrefix w n) := by
  simp only [supFloor, supVertex, cantorPrefix_length]
  rw [← supVertexNum_add term w n, dyadicValue_add, dyadicValue_two_mul_succ]

/-- Every strict increase of the staircase is at least a doubling. -/
lemma supFloor_jump (term : ℕ → BitString → ℕ) (w : CantorSeq) (n : ℕ)
    (h : supFloor term (cantorPrefix w n) < supFloor term (cantorPrefix w (n + 1))) :
    2 * supFloor term (cantorPrefix w n) ≤ supFloor term (cantorPrefix w (n + 1)) := by
  have hgn : supFloor term (cantorPrefix w n)
      = dyadicValue (2 * pow2Floor (prefixNum term (cantorPrefix w n))) (n + 1) := by
    rw [dyadicValue_two_mul_succ, supFloor, cantorPrefix_length]
  have hgn1 : supFloor term (cantorPrefix w (n + 1))
      = dyadicValue (pow2Floor (prefixNum term (cantorPrefix w (n + 1)))) (n + 1) := by
    rw [supFloor, cantorPrefix_length]
  have hlt : 2 * pow2Floor (prefixNum term (cantorPrefix w n))
      < pow2Floor (prefixNum term (cantorPrefix w (n + 1))) := by
    by_contra hcon
    have hcon : pow2Floor (prefixNum term (cantorPrefix w (n + 1))) ≤ 
        2 * pow2Floor (prefixNum term (cantorPrefix w n)) := not_lt.mp hcon
    rw [hgn, hgn1] at h
    exact absurd (dyadicValue_mono_nat hcon (n + 1)) (not_le.mpr h)
  rw [hgn, hgn1, ← dyadicValue_mul_two_num]
  exact dyadicValue_mono_nat (pow2Floor_jump hlt) (n + 1)

/-- `supVertexNum term` is computable whenever `term` is. -/
lemma computable_supVertexNum {term : ℕ → BitString → ℕ}
    (hterm : Computable fun p : ℕ × BitString => term p.1 p.2) :
    Computable (supVertexNum term) := by
  have hmul : Computable₂ (fun u v : ℕ => u * v) := Primrec.nat_mul.to_comp
  have hsub : Computable₂ (fun u v : ℕ => u - v) := Primrec.nat_sub.to_comp
  have hlt : Computable₂ (fun u v : ℕ => decide (u < v)) := primrec_decide_nat_lt.to_comp
  have hlen : Computable (fun x : BitString => x.length) := Computable.list_length
  have hpn : Computable (prefixNum term) := computable_prefixNum hterm
  have hpf : Computable (fun x : BitString => pow2Floor (prefixNum term x)) :=
    computable_pow2Floor.comp hpn
  have htake : Computable (fun x : BitString => x.take (x.length - 1)) :=
    (Primrec.list_take (α := Bool)).to_comp.comp (hsub.comp hlen (Computable.const 1))
      Computable.id
  have hval : Computable (fun x : BitString =>
      2 * pow2Floor (prefixNum term (x.take (x.length - 1)))) :=
    hmul.comp (Computable.const 2) (computable_pow2Floor.comp (hpn.comp htake))
  have hcond : Computable (fun x : BitString => decide (x.length < 1)) :=
    hlt.comp hlen (Computable.const 1)
  have hpar : Computable (supParentNum term) := by
    refine (Computable.cond hcond (Computable.const 0) hval).of_eq fun x => ?_
    by_cases h : x.length = 0 <;> simp [supParentNum, h]
  exact hsub.comp hpf hpar

/-! ### The sum of a doubling staircase is at most twice its last step -/

/-- The combinatorial core of the source's hint.  If `g` is the running total of the
increments `u` and every strict increase of `g` at least doubles it, then the *last* increment
before `n` already accounts for half of `g n`; equivalently, "the sum equals the supremum up to
a `Θ(1)`-factor". -/
lemma exists_le_two_mul_of_jump {g u : ℕ → ℝ≥0∞} (hzero : g 0 = u 0)
    (hstep : ∀ n : ℕ, g (n + 1) = u (n + 1) + g n)
    (hjump : ∀ n : ℕ, g n < g (n + 1) → 2 * g n ≤ g (n + 1))
    (hfin : ∀ n : ℕ, g n ≠ ⊤) (n : ℕ) : ∃ j ≤ n, g n ≤ 2 * u j := by
  induction n with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      rw [hzero]
      calc u 0 = 1 * u 0 := (one_mul _).symm
        _ ≤ 2 * u 0 := by gcongr; norm_num
  | succ n ih =>
      have hmono : g n ≤ g (n + 1) := by
        rw [hstep n]
        exact le_add_self
      rcases eq_or_lt_of_le hmono with he | hlt
      · obtain ⟨j, hjn, hj⟩ := ih
        exact ⟨j, by omega, by rw [← he]; exact hj⟩
      · refine ⟨n + 1, le_rfl, ?_⟩
        have h2 := hjump n hlt
        rw [hstep n] at h2 ⊢
        rw [two_mul] at h2
        have hle : g n ≤ u (n + 1) := (ENNReal.add_le_add_iff_right (hfin n)).mp h2
        calc u (n + 1) + g n ≤ u (n + 1) + u (n + 1) := by gcongr
          _ = 2 * u (n + 1) := (two_mul _).symm

/-! ### The mass bound -/

/-- A supremum over `∑_{i ≤ n}` is the `tsum`. -/
lemma iSup_sum_range_succ_eq_tsum (f : ℕ → ℝ≥0∞) :
    ⨆ n : ℕ, ∑ i ∈ Finset.range (n + 1), f i = ∑' i : ℕ, f i := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine le_antisymm (iSup_le fun n => le_iSup (fun N => ∑ i ∈ Finset.range N, f i) (n + 1))
    (iSup_le fun N => ?_)
  refine le_iSup_of_le N ?_
  exact Finset.sum_le_sum_of_subset
    (by intro i hi; simp only [Finset.mem_range] at hi ⊢; omega)

/-- **The telescoping mass bound.**  The increments of the staircase, weighted by the cylinder
masses, sum to at most `∫ v dμ ≤ 1`: the partial sums over the first `N + 1` levels are exactly
`∫ d((ω)_N) dμ`, and `d ≤ w ≤ v`. -/
lemma tsum_supVertex_mul_cantorMass_le {μ : Measure CantorSeq} [IsFiniteMeasure μ]
    (term : ℕ → BitString → ℕ) {v : CantorSeq → ℝ≥0∞}
    (hvsup : ∀ w : CantorSeq, v w = ⨆ n : ℕ, supPartial term (cantorPrefix w n))
    (hint : ∫⁻ w, v w ∂μ ≤ 1) :
    (∑' x : BitString, supVertex term x * cantorMass μ x) ≤ 1 := by
  have hIle : ∀ N : ℕ, (∫⁻ w, supFloor term (cantorPrefix w N) ∂μ) ≤ 1 := by
    intro N
    refine le_trans (lintegral_mono fun w => ?_) hint
    rw [hvsup w]
    exact le_trans (supFloor_le_supPartial term _)
      (le_iSup (fun i : ℕ => supPartial term (cantorPrefix w i)) N)
  have hmeasV : ∀ n : ℕ, Measurable fun w : CantorSeq => supVertex term (cantorPrefix w n) :=
    fun n => measurable_comp_cantorPrefix n (supVertex term)
  have hrec : ∀ n : ℕ,
      (∫⁻ w, supVertex term (cantorPrefix w (n + 1)) ∂μ)
          + ∫⁻ w, supFloor term (cantorPrefix w n) ∂μ
        = ∫⁻ w, supFloor term (cantorPrefix w (n + 1)) ∂μ := by
    intro n
    rw [← lintegral_add_left (hmeasV (n + 1))]
    exact lintegral_congr fun w => (supFloor_cantorPrefix_succ term w n).symm
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1),
      (∫⁻ w, supVertex term (cantorPrefix w n) ∂μ)
        = ∫⁻ w, supFloor term (cantorPrefix w N) ∂μ := by
    intro N
    induction N with
    | zero =>
        rw [Finset.sum_range_one]
        exact lintegral_congr fun w => supVertex_cantorPrefix_zero term w
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, add_comm]
        exact hrec N
  have hfin : (∑' n : ℕ, ∫⁻ w, supVertex term (cantorPrefix w n) ∂μ) ≤ 1 := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    refine le_trans ?_ (hIle N)
    rw [← hsum N]
    exact Finset.sum_le_sum_of_subset
      (by intro i hi; simp only [Finset.mem_range] at hi ⊢; omega)
  calc (∑' x : BitString, supVertex term x * cantorMass μ x)
      = ∑' n : ℕ, ∑ y ∈ levelFinset n, supVertex term y * cantorMass μ y :=
        tsum_eq_tsum_sum_levelFinset _
    _ = ∑' n : ℕ, ∫⁻ w, supVertex term (cantorPrefix w n) ∂μ :=
        tsum_congr fun n => (lintegral_comp_cantorPrefix μ n (supVertex term)).symm
    _ ≤ 1 := hfin

/-! ### Maximality -/

/-- **SUV Problem 147 (Section 5.6, p. 150)**: `ω ↦ sup_{x ⊑ ω} m(x)/p(x)` dominates every
expectation-bounded randomness test for `μ` up to a constant factor. -/
theorem maximal_prefixSupRatio {μ : Measure CantorSeq} [IsFiniteMeasure μ]
    (hμ : IsComputableMeasure μ) {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m)
    (v : CantorSeq → ℝ≥0∞) (hv : IsExpectationBoundedRandomnessTest μ v) :
    ∃ c : NNReal, ∀ w : CantorSeq, v w ≤ c * prefixSupRatio m μ w := by
  obtain ⟨term, hterm, hvterm⟩ := ((lowerSemicomputableFun_characterizations v).2.2).mp hv.1
  have hvw : ∀ w : CantorSeq, v w = ∑' s : ℕ, vertexWeight term (cantorPrefix w s) := by
    intro w
    rw [hvterm w]
    exact tsum_congr fun s => (vertexWeight_cantorPrefix term w s).symm
  have hvsup : ∀ w : CantorSeq, v w = ⨆ n : ℕ, supPartial term (cantorPrefix w n) := by
    intro w
    rw [hvw w, ← iSup_sum_range_succ_eq_tsum]
    refine iSup_congr fun n => ?_
    rw [supPartial, cantorPrefix_length, dyadicValue_prefixNum_cantorPrefix]
  have hmass := tsum_supVertex_mul_cantorMass_le term hvsup hv.2
  have hlsc : IsLSC fun (x : BitString) (_ : BitString) => supVertex term x * cantorMass μ x := by
    have hnum : Computable fun p : ℕ × BitString => supVertexNum term p.2 :=
      (computable_supVertexNum hterm).comp Computable.snd
    have hfun : (fun (x : BitString) (_ : BitString) => supVertex term x * cantorMass μ x)
        = fun (x : BitString) (_ : BitString) =>
            vertexWeight (fun (_ : ℕ) (y : BitString) => supVertexNum term y) x
              * cantorMass μ x := by
      funext x _
      rw [supVertex, vertexWeight]
    rw [hfun]
    exact isLSC_vertexWeight_mul_cantorMass hμ hnum
  obtain ⟨c, hc, hdom⟩ := hm.2 (fun x => supVertex term x * cantorMass μ x) ⟨hmass, hlsc⟩
  obtain ⟨k, hk⟩ := exists_inv_two_pow_lt hc.ne'
  have hbound : ∀ y : BitString,
      supVertex term y ≤ (2 : ℝ≥0∞) ^ k * (m y / cantorMass μ y) := by
    intro y
    have hkey : (2 : ℝ≥0∞)⁻¹ ^ k * (supVertex term y * cantorMass μ y) ≤ m y := by
      refine le_trans ?_ (hdom y)
      gcongr
    rcases eq_or_ne (cantorMass μ y) 0 with h0 | h0
    · have hmy : m y ≠ 0 := (universalSemimeasure_pos hm y).ne'
      rw [h0, ENNReal.div_zero hmy, ENNReal.mul_top (by positivity)]
      exact le_top
    · have hdivle : (2 : ℝ≥0∞)⁻¹ ^ k * supVertex term y ≤ m y / cantorMass μ y := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (measure_ne_top μ _)), mul_assoc]
        exact hkey
      calc supVertex term y
          = (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞)⁻¹ ^ k * supVertex term y) := by
            rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
              one_pow, one_mul]
        _ ≤ (2 : ℝ≥0∞) ^ k * (m y / cantorMass μ y) := by gcongr
  refine ⟨(2 : NNReal) ^ (k + 2), fun w => ?_⟩
  have hcast : (((2 : NNReal) ^ (k + 2) : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (k + 2) := by
    push_cast
    ring
  rw [hcast, hvsup w]
  refine iSup_le fun n => ?_
  obtain ⟨j, -, hj⟩ := exists_le_two_mul_of_jump
    (g := fun i => supFloor term (cantorPrefix w i))
    (u := fun i => supVertex term (cantorPrefix w i))
    (supVertex_cantorPrefix_zero term w).symm
    (fun i => supFloor_cantorPrefix_succ term w i)
    (fun i => supFloor_jump term w i)
    (fun i => supFloor_ne_top term (cantorPrefix w i)) n
  have hbj : supVertex term (cantorPrefix w j)
      ≤ (2 : ℝ≥0∞) ^ k * (m (cantorPrefix w j) / cantorMass μ (cantorPrefix w j)) :=
    hbound (cantorPrefix w j)
  have hsupj : m (cantorPrefix w j) / cantorMass μ (cantorPrefix w j)
      ≤ prefixSupRatio m μ w :=
    le_iSup (fun i : ℕ => m (cantorPrefix w i) / cantorMass μ (cantorPrefix w i)) j
  calc supPartial term (cantorPrefix w n)
      ≤ 2 * supFloor term (cantorPrefix w n) := supPartial_le_two_mul_supFloor term _
    _ ≤ 2 * (2 * supVertex term (cantorPrefix w j)) := by gcongr
    _ ≤ 2 * (2 * ((2 : ℝ≥0∞) ^ k
          * (m (cantorPrefix w j) / cantorMass μ (cantorPrefix w j)))) := by
        gcongr
    _ = (2 : ℝ≥0∞) ^ (k + 2) * (m (cantorPrefix w j) / cantorMass μ (cantorPrefix w j)) := by
        ring
    _ ≤ (2 : ℝ≥0∞) ^ (k + 2) * prefixSupRatio m μ w := by gcongr

/-- SUV Problem 147 (Section 5.6, p. 150): the sum in Problem 146 may be replaced by the
supremum -- `sup_{x ⊑ w} m(x)/p(x)` is still a universal expectation-bounded randomness test.

Source hint: represent a lower semicomputable `t` as `∑_k t_k` with `t_k = 2^k` on
`{t > 2^k}` and `0` elsewhere; each `t_k` is realised by equal weights placed at incompatible
vertices, so every summand is a power of two and the sum equals the supremum up to a `Θ(1)`
factor. -/
theorem problem_147_maximal_prefixSupRatio' {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m) :
    ∀ v : CantorSeq → ℝ≥0∞, IsExpectationBoundedRandomnessTest μ v →
      ∃ c : NNReal, ∀ w : CantorSeq, v w ≤ c * prefixSupRatio m μ w :=
  fun v hv => maximal_prefixSupRatio hμ hm v hv

end Kolmogorov
