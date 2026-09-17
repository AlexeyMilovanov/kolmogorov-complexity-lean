import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Schedule
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedSpendArithmetic

/-!
# V2 block multiplicities and the aggregate recovery

Blueprint v11, Stage C1 (proof doc v14 §9.0 item 2; audit U3(a)/(b)).

The Day-literal controller replaces the flattened single-root spend/advantage
calls by *blocks* of many fine-scale roots.  The blocks are chosen so that
their aggregate request is exactly the flattened one — so H4 and the
committed per-round request bound are recovered verbatim — while every root
now lives at its block's own anchor scale, which is what the disjointness
chase needs (PD §9.0).

* **Spend pass `i`** (`0 ≤ i < 8`): `2^{(7−i)·L}` roots per deficient outer
  root, each requesting at the pass-anchor scale `2^{−(a+3+(7−i)L)}`.
  Aggregate `2^{−(a+3)}` per deficient root per pass — the committed
  `dyadicScale a / 8`, so the eight passes recover the committed
  `[α/16, α/8]` per-pass increment (H4).
* **Advantage round `r`**: `2^{ε_r − grayCallDepth}` roots per selected
  source son / fresh slot, each at the round-anchor scale `2^{−ε_r}`.
  Aggregate `2^{−grayCallDepth}` per slot — the committed per-round request.
-/

namespace Kolmogorov

/-- `2^m` roots each of dyadic mass `2^{−(base+m)}` aggregate to the base
mass `2^{−base}`. -/
lemma two_pow_mul_dyadicScale_add (base m : Nat) :
    ((2 : Rat) ^ m) * dyadicScale (base + m) = dyadicScale base := by
  unfold dyadicScale
  rw [pow_add, ← mul_assoc]
  rw [show ((2 : Rat) ^ m) * ((1 / 2 : Rat) ^ base) =
      ((1 / 2 : Rat) ^ base) * (2 : Rat) ^ m by ring, mul_assoc,
    ← mul_pow]
  norm_num

/-- The number of fine-scale spend roots run per deficient outer root in
pass `i` of the stage-`j` rung (per-round budget `L`): `2^{(7−i)·L}`. -/
def graySpendMult (L i : Nat) : Nat := 2 ^ ((7 - i) * L)

/-- The request scale (α-depth) of a spend root in pass `i`: the pass
anchor `a + 3 + (7−i)·L`. -/
def graySpendAnchor (a L i : Nat) : Nat := a + 3 + (7 - i) * L

/-- **Spend aggregate recovery (H4)** (audit U3(a)): the `2^{(7−i)L}`
roots of pass `i`, each at scale `2^{−(a+3+(7−i)L)}`, sum to exactly
`dyadicScale a / 8` — the committed single-root value at depth `a+3`. -/
theorem graySpendMult_mass (a L i : Nat) :
    (graySpendMult L i : Rat) * dyadicScale (graySpendAnchor a L i) =
      dyadicScale a / 8 := by
  unfold graySpendMult graySpendAnchor
  push_cast
  rw [show a + 3 + (7 - i) * L = (a + 3) + ((7 - i) * L) by ring,
    two_pow_mul_dyadicScale_add]
  unfold dyadicScale
  rw [pow_add]
  ring

/-- The advantage block multiplicity: `2^{ε_r − grayCallDepth}` roots per
selected source son / fresh slot. -/
def grayAdvMult (callDepth epsR : Nat) : Nat := 2 ^ (epsR - callDepth)

/-- **Advantage aggregate recovery** (audit U3(b)): the `2^{ε_r − d}` roots
of round `r`, each at scale `2^{−ε_r}`, sum to `2^{−d}` per slot — the
committed per-round request at the call depth `d = grayCallDepth`. -/
theorem grayAdvMult_mass {callDepth epsR : Nat} (h : callDepth ≤ epsR) :
    (grayAdvMult callDepth epsR : Rat) * dyadicScale epsR =
      dyadicScale callDepth := by
  unfold grayAdvMult
  push_cast
  rw [show dyadicScale epsR = dyadicScale (callDepth + (epsR - callDepth)) by
    congr 1; omega, two_pow_mul_dyadicScale_add]

/-- The eight spend passes, summed, recover the full root scale
`dyadicScale a` — i.e. one deficient root can be lifted by exactly `α`
across the eight passes (the H4 ceiling). -/
theorem graySpendMult_total_mass (a L : Nat) :
    (∑ i ∈ Finset.range 8,
        (graySpendMult L i : Rat) * dyadicScale (graySpendAnchor a L i)) =
      dyadicScale a := by
  have hterm : ∀ i ∈ Finset.range 8,
      (graySpendMult L i : Rat) * dyadicScale (graySpendAnchor a L i) =
        dyadicScale a / 8 := fun i _ => graySpendMult_mass a L i
  rw [Finset.sum_congr rfl hterm]
  simp [Finset.sum_const, Finset.card_range]
  ring

end Kolmogorov
