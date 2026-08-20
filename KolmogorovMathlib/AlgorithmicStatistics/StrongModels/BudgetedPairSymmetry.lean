import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.Prefix.Properties

/-!
# Budget-scale pair estimates for a conditionally random tail

The add-noise transport needed by `prop:upward` measures every logarithmic
overhead against a *complexity budget* for the head string `x`, never against
its length `l(x)`: the head is a model code, whose length can be exponentially
larger than its complexity.

This module supplies the two pair estimates of `NormalPair` and
`PlainPairSymmetry` in that budget-scale form.  Both are consumer forms of the
already proved budgeted chain

* `KP_le_condK_of_logSlack_budget` — `K(x) ≤ C(x) + O(log N)` whenever
  `C(x) ≤ N`, and
* `plainK_add_condK_le_plainK_pair` — `C(x) + C(y | x) ≤ C(x, y) + O(log N)`
  whenever `C(x), C(x, y) ≤ N`,

both of which are *already* stated at the complexity scale.  Only their
existing consumer instantiations happen to substitute `N := l(x) + l(y)`.

* `plainK_pair_le_plainK_add_length_budget`:
  `C(x, y) ≤ C(x) + l(y) + O(log N)` for any budget `N ≥ C(x), l(y)`.
* `plainK_pair_ge_plainK_add_length_of_random_budget`:
  `C(x) + l(y) ≤ C(x, y) + eps + O(log N)` for a conditionally random tail `y`
  and any budget `N ≥ C(x), l(y)`.

Neither statement mentions `l(x)`.
-/

namespace Kolmogorov

/-- **Budget-scale upper pair bound.**  Encoding the pair costs at most the
plain complexity of the head, the length of the tail, and a logarithmic
overhead measured against any budget `N` dominating both.  This is
`plainK_pair_le_plainK_add_length` with the length-scale slack
`logSlack c (l(x) + l(y))` replaced by the budget-scale `logSlack c N`. -/
theorem plainK_pair_le_plainK_add_length_budget
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (kx N : Nat),
      plainK V x = (kx : ENat) →
      kx ≤ N →
      y.length ≤ N →
      plainK V (pairCode x y) ≤ ((kx + y.length + logSlack c N : Nat) : ENat) := by
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_KPPlain_add_KPPlain V U hV hU
  obtain ⟨cB, hB⟩ := KP_le_condK_of_logSlack_budget V U hV hU
  obtain ⟨cL, hL⟩ := KPPlain_le_length_add_log U hU
  refine ⟨cB + (2 + cL + cPair), ?_⟩
  intro x y kx N hkx hkxN hyN
  set c := cB + (2 + cL + cPair) with hc
  have hKx : KPPlain U x ≤ ((kx + logSlack cB N : Nat) : ENat) :=
    hB x [] kx N hkx hkxN
  have hKy : KPPlain U y ≤
      ((y.length + 2 * (Nat.bits y.length).length + cL : Nat) : ENat) := by
    refine (hL y).trans ?_
    push_cast
    exact le_rfl
  have harith :
      kx + logSlack cB N + (y.length + 2 * (Nat.bits y.length).length + cL)
          + cPair
        ≤ kx + y.length + logSlack c N := by
    have hmono : (Nat.bits y.length).length ≤ (Nat.bits N).length :=
      length_natBits_mono hyN
    have hsum : logSlack cB N + logSlack (2 + cL + cPair) N = logSlack c N :=
      logSlack_add_const _ _ _
    have hsecond :
        2 * (Nat.bits y.length).length + cL + cPair
          ≤ logSlack (2 + cL + cPair) N := by
      have hls : logSlack (2 + cL + cPair) N
          = (2 + cL + cPair) * (Nat.bits N).length + (2 + cL + cPair) := rfl
      nlinarith [hmono]
    omega
  calc plainK V (pairCode x y) ≤ KPPlain U x + KPPlain U y + (cPair : ENat) :=
        hPair x y
    _ ≤ ((kx + logSlack cB N : Nat) : ENat)
          + ((y.length + 2 * (Nat.bits y.length).length + cL : Nat) : ENat)
          + (cPair : ENat) := by gcongr
    _ = ((kx + logSlack cB N + (y.length + 2 * (Nat.bits y.length).length + cL)
          + cPair : Nat) : ENat) := by push_cast; ring
    _ ≤ ((kx + y.length + logSlack c N : Nat) : ENat) := by exact_mod_cast harith

/-- **Budget-scale lower pair bound for a conditionally random tail.**  If `y`
is conditionally random given `x` up to loss `epsilon`, then

`C(x) + l(y) ≤ C(x, y) + epsilon + O(log N)`

for any budget `N` dominating `C(x)` and `l(y)`.  This is
`plainK_pair_ge_plainK_add_length_of_random` with the length-scale slack
`logSlack c (l(x) + l(y))` replaced by the budget-scale `logSlack c N`; the
complexity of the pair is itself brought inside the budget by
`plainK_pair_le_plainK_add_length_budget`. -/
theorem plainK_pair_ge_plainK_add_length_of_random_budget
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon kx kxy N : Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      kx ≤ N →
      y.length ≤ N →
      kx + y.length ≤ kxy + epsilon + logSlack c N := by
  obtain ⟨cSOI, hSOI⟩ := plainK_add_condK_le_plainK_pair V U hV hU
  obtain ⟨cUp, hUp⟩ := plainK_pair_le_plainK_add_length_budget V U hV hU
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cSOI (2 + cUp) cUp
  refine ⟨cFold, ?_⟩
  intro x y epsilon kx kxy N hkx hkxy hrandom hkxN hyN
  -- A budget dominating both `C(x)` and `C(x, y)`.
  set M := (2 + cUp) * N + cUp with hM
  have hupper : kxy ≤ kx + y.length + logSlack cUp N := by
    have h := hUp x y kx N hkx hkxN hyN
    rw [hkxy] at h
    exact_mod_cast h
  have hslackLinear : logSlack cUp N ≤ cUp * N + cUp := by
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left cUp (length_natBits_le_self N)) cUp
  have hkxyM : kxy ≤ M := by
    simp only [hM]
    nlinarith [hupper, hslackLinear, hkxN, hyN]
  have hxM : plainK V x ≤ (M : ENat) := by
    rw [hkx]
    have : kx ≤ M := by simp only [hM]; nlinarith [hkxN]
    exact_mod_cast this
  have hxyM : plainK V (pairCode x y) ≤ (M : ENat) := by
    rw [hkxy]
    exact_mod_cast hkxyM
  obtain ⟨s, hs⟩ : ∃ k : Nat, condK V y x = (k : ENat) :=
    ⟨(condK V y x).toNat, (ENat.coe_toNat (condK_ne_top_of_optimal V hV y x)).symm⟩
  have hys : y.length ≤ s + epsilon := by
    rw [hs] at hrandom
    exact_mod_cast hrandom
  have hsoi := hSOI x y M hxM hxyM
  rw [hkx, hkxy, hs] at hsoi
  have hsoiNat : kx + s ≤ kxy + logSlack cSOI M := by exact_mod_cast hsoi
  have hslack : logSlack cSOI M ≤ logSlack cFold N := hFold N
  omega

/-- **Two-sided budget-scale pair estimate for a conditionally random tail.**
The plain complexity of the canonical pair equals `C(x) + l(y)` up to `epsilon`
and a logarithmic term in any budget `N` dominating `C(x)` and `l(y)`.  This is
the budget-scale analogue of `pair_complexity_close_of_random_tail`, whose slack
is measured at the length scale `l(x) + l(y)`. -/
theorem plainK_pair_close_of_random_tail_budget
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon kx kxy N : Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      kx ≤ N →
      y.length ≤ N →
      kxy ≤ kx + y.length + logSlack c N ∧
        kx + y.length ≤ kxy + epsilon + logSlack c N := by
  obtain ⟨cUp, hUp⟩ := plainK_pair_le_plainK_add_length_budget V U hV hU
  obtain ⟨cLow, hLow⟩ := plainK_pair_ge_plainK_add_length_of_random_budget V U hV hU
  refine ⟨cUp + cLow, ?_⟩
  intro x y epsilon kx kxy N hkx hkxy hrandom hkxN hyN
  have hupper : kxy ≤ kx + y.length + logSlack cUp N := by
    have h := hUp x y kx N hkx hkxN hyN
    rw [hkxy] at h
    exact_mod_cast h
  have hlower : kx + y.length ≤ kxy + epsilon + logSlack cLow N :=
    hLow x y epsilon kx kxy N hkx hkxy hrandom hkxN hyN
  have hUpFold : logSlack cUp N ≤ logSlack (cUp + cLow) N :=
    logSlack_mono_left (by omega) N
  have hLowFold : logSlack cLow N ≤ logSlack (cUp + cLow) N :=
    logSlack_mono_left (by omega) N
  exact ⟨by omega, by omega⟩

end Kolmogorov
