import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerBallModels
import KolmogorovMathlib.Prefix.Properties
import Mathlib.Tactic.Ring

open Kolmogorov CodedFiniteDistribution

/-- **Aristotle Leaf L8:** Prefix complexity of `q * 2^t`.
By combining `KPPlain_map_le` (on a pair-decoding map) and
`KPPair_le_KPPlain_add_KPPlain`, we bound the complexity of the rounded length
`q * 2^t` by the sum of the complexities of `q` and `t`.
-/
theorem KPPlain_natCode_mul_pow_two_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ q t : ℕ,
      KPPlain U (natCode (q * 2 ^ t)) ≤
        KPPlain U (natCode q) + KPPlain U (natCode t) + (c : ENat) := by
  classical
  -- The decoder: read a pair of unary codes `(natCode q, natCode t)` and output
  -- the unary code of `q * 2 ^ t`.
  set f : BitString → BitString := fun w =>
    natCode (decodeNatCode (decodeFirst w) * 2 ^ decodeNatCode (decodeSecond w)) with hf_def
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  have hf_comp : Computable f := by
    have h1 : Primrec (fun w : BitString => decodeNatCode (decodeFirst w)) :=
      decodeNatCode_primrec.comp decodeFirst_primrec
    have h2 : Primrec (fun w : BitString => decodeNatCode (decodeSecond w)) :=
      decodeNatCode_primrec.comp decodeSecond_primrec
    have h3 : Primrec (fun w : BitString =>
        decodeNatCode (decodeFirst w) * 2 ^ decodeNatCode (decodeSecond w)) :=
      Primrec.nat_mul.comp h1 (hpow.comp (Primrec.const 2) h2)
    exact natCode_computable.comp h3.to_comp
  obtain ⟨c_map, hmap⟩ := KPPlain_map_le U hU f hf_comp
  obtain ⟨c_pair, hpair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  refine ⟨c_map + c_pair, fun q t => ?_⟩
  have hfval : f (pairCode (natCode q) (natCode t)) = natCode (q * 2 ^ t) := by
    simp [hf_def, decodeFirst_pairCode, decodeSecond_pairCode]
  have h1 := hmap (pairCode (natCode q) (natCode t))
  rw [hfval] at h1
  have h2 : KPPlain U (pairCode (natCode q) (natCode t)) = KPPair U (natCode q) (natCode t) := rfl
  rw [h2] at h1
  calc KPPlain U (natCode (q * 2 ^ t))
      ≤ KPPair U (natCode q) (natCode t) + (c_map : ENat) := h1
    _ ≤ (KPPlain U (natCode q) + KPPlain U (natCode t) + (c_pair : ENat)) + (c_map : ENat) := by
        gcongr
        exact hpair _ _
    _ = KPPlain U (natCode q) + KPPlain U (natCode t) + ((c_map + c_pair : ℕ) : ENat) := by
        push_cast
        ring

/-- `logSlack` is monotone in its constant. -/
theorem logSlack_mono_const {c c' n : ℕ} (h : c ≤ c') : logSlack c n ≤ logSlack c' n := by
  unfold logSlack
  exact Nat.add_le_add (Nat.mul_le_mul_right _ h) h

/-- **The rounded-length corner at an explicit rounded radius.**  If the length of
`x` is at most the multiple `q * 2 ^ t` of a power of two, and `m` bounds the
combined prefix complexity of the quotient `q` and the exponent `t` (plus the
fixed pair-coding overhead `c`), then the ball at radius `q * 2 ^ t` realizes the
budget-scale plain corner, provided `m` fits the model budget (`m ≤ alpha`) and
the size coordinate `q * 2 ^ t + 1` together with `m` fits the two-part budget.

This is the assembly of `KPPlain_natCode_mul_pow_two_le` with
`budgeted_plain_corner_of_ball_length`: it converts the address complexity of the
rounded radius into the two separately controlled complexities of `q` and `t`.
The second budget hypothesis `q * 2 ^ t + 1 + m ≤ kx + beta` is what pins the
rounded radius inside the two-part budget; it is not implied by the `alpha`
condition alone. -/
theorem budgeted_plain_corner_of_rounded_multiple
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta q t m : ℕ),
      x.length ≤ q * 2 ^ t →
      KPPlain U (natCode q) + KPPlain U (natCode t) + (c : ENat) ≤ (m : ENat) →
      m ≤ alpha →
      q * 2 ^ t + 1 + m ≤ kx + beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨c8, h8⟩ := KPPlain_natCode_mul_pow_two_le U hU
  obtain ⟨cBall, hBall⟩ := budgeted_plain_corner_of_ball_length V U hV hU
  refine ⟨c8 + cBall, fun x kx baseBudget alpha beta q t m hlen hm hma hsum => ?_⟩
  have hn : KPPlain U (natCode (q * 2 ^ t)) ≤ (m : ENat) := by
    refine (h8 q t).trans (le_trans ?_ hm)
    gcongr
    exact_mod_cast Nat.le_add_right c8 cBall
  obtain ⟨i, j, hprof, hi, hij⟩ :=
    hBall x kx baseBudget alpha beta (q * 2 ^ t) m hlen hn hma hsum
  have hmono : logSlack cBall baseBudget ≤ logSlack (c8 + cBall) baseBudget :=
    logSlack_mono_const (Nat.le_add_left _ _)
  exact ⟨i, j, hprof, by omega, by omega⟩

/-- The ceiling multiple `⌈l / 2^t⌉ · 2^t` is at least `l`.  This is the exact
membership fact placing `x` inside the rounded ball of radius
`⌈l(x)/2^t⌉·2^t`; it is the witness-explicit specialisation of the first clause
of `exists_rounded_multiple`. -/
theorem length_le_roundedMultiple (l t : ℕ) :
    l ≤ ((l + 2 ^ t - 1) / 2 ^ t) * 2 ^ t := by
  have hbpos : 0 < 2 ^ t := pow_pos (by norm_num) t
  rw [Nat.mul_comm]
  have hdm := Nat.div_add_mod (l + 2 ^ t - 1) (2 ^ t)
  have hmod : (l + 2 ^ t - 1) % 2 ^ t < 2 ^ t := Nat.mod_lt _ hbpos
  omega

/-- **The rounded-length corner (honest budget-fit form).**  Fix an exponent `t`
and round `l(x)` up to the ceiling multiple `n = ⌈l(x)/2^t⌉·2^t` of `2^t`.  If the
combined address complexity of the quotient `q = ⌈l(x)/2^t⌉` and the exponent `t`
(plus the fixed pair-coding overhead `c`) is bounded by `m`, and both the model
budget (`m ≤ alpha`) and the two-part budget (`n + 1 + m ≤ kx + beta`) are met,
then the exact budget-scale plain corner holds with slack `logSlack c baseBudget`.

**Why the two-part budget hypothesis `n + 1 + m ≤ kx + beta` is genuinely
required (retirement of `rounded_length_radius_fits_budget`).**  An earlier draft
of this file tried to *derive* the existence of a good `(n, m)` from an
`alpha`-only side condition (the retired, unproved-leaf
`rounded_length_radius_fits_budget`).  That statement is mathematically FALSE:
when the two-part slack `S = kx + beta - l(x)` is small (e.g. `S = 2`, forcing the
strategy's `t = Nat.log2 (S/2) = 0`, hence `n = l(x)`) while `l(x)` is large, no
`m ≥ K(natCode n)` can satisfy `n + 1 + m ≤ kx + beta`, no matter how large
`alpha` is.  The corner genuinely fails in that regime.  The honest content is
therefore a *sufficient condition*: the caller must exhibit a `t` for which the
rounded radius fits the two-part slack, which is possible exactly when `S` is
large enough to absorb the address cost `2^t + K(q) + K(t) + O(1)`.  This is the
ceiling specialisation of `budgeted_plain_corner_of_rounded_multiple`. -/
theorem budgeted_plain_corner_of_rounded_length
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta t m : ℕ),
      KPPlain U (natCode ((x.length + 2 ^ t - 1) / 2 ^ t))
          + KPPlain U (natCode t) + (c : ENat) ≤ (m : ENat) →
      m ≤ alpha →
      ((x.length + 2 ^ t - 1) / 2 ^ t) * 2 ^ t + 1 + m ≤ kx + beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨c, hc⟩ := budgeted_plain_corner_of_rounded_multiple V U hV hU
  refine ⟨c, fun x kx baseBudget alpha beta t m hm hma hsum => ?_⟩
  exact hc x kx baseBudget alpha beta ((x.length + 2 ^ t - 1) / 2 ^ t) t m
    (length_le_roundedMultiple x.length t) hm hma hsum

/-- **Log-explicit rounded-length corner.**  Discharges the abstract address
bound of `budgeted_plain_corner_of_rounded_length` using the universal estimate
`K(natCode n) ≤ 2·|bits n| + O(1)` (`KPPlain_natCode_le_log`), so the two side
conditions are stated purely in terms of the explicit logarithmic address cost
`m₀ = 2·|bits ⌈l(x)/2^t⌉| + 2·|bits t| + c` of the rounded radius `n = ⌈l(x)/2^t⌉·2^t`.

This is the form a hard-regime corner assembler consumes: it does not manipulate
`K(natCode ·)` directly, it only has to exhibit an exponent `t` whose *explicit*
rounded radius simultaneously fits the model budget `alpha` and the two-part slack
`kx + beta`.  Such a `t` exists exactly when the slack `S = kx + beta - l(x)` is
large enough to absorb `2^t + 2·|bits ⌈l(x)/2^t⌉| + 2·|bits t| + O(1)`; when `S` is
small no `t` works, which is precisely the residual sub-regime where the
rounded-length lane does not apply (see the retirement note above). -/
theorem budgeted_plain_corner_of_rounded_length_log
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta t : ℕ),
      2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
          + 2 * (Nat.bits t).length + c ≤ alpha →
      ((x.length + 2 ^ t - 1) / 2 ^ t) * 2 ^ t + 1
          + (2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
            + 2 * (Nat.bits t).length + c) ≤ kx + beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨cR, hR⟩ := budgeted_plain_corner_of_rounded_length V U hV hU
  obtain ⟨cLog, hLog⟩ := KPPlain_natCode_le_log U hU
  refine ⟨cR + 2 * cLog, fun x kx baseBudget alpha beta t hma hsum => ?_⟩
  obtain ⟨i, j, hprof, hi, hij⟩ := hR x kx baseBudget alpha beta t
    (2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length + 2 * (Nat.bits t).length
      + (cR + 2 * cLog))
    (by
      calc KPPlain U (natCode ((x.length + 2 ^ t - 1) / 2 ^ t))
              + KPPlain U (natCode t) + (cR : ENat)
          ≤ (2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length + (cLog : ENat))
              + (2 * (Nat.bits t).length + (cLog : ENat)) + (cR : ENat) :=
            add_le_add (add_le_add (hLog _) (hLog t)) le_rfl
        _ = ((2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
              + 2 * (Nat.bits t).length + (cR + 2 * cLog) : ℕ) : ENat) := by push_cast; ring)
    hma hsum
  have hmono : logSlack cR baseBudget ≤ logSlack (cR + 2 * cLog) baseBudget :=
    logSlack_mono_const (Nat.le_add_right _ _)
  exact ⟨i, j, hprof, by omega, by omega⟩
