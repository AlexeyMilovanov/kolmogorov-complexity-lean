import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.OrdinalPlainRandomness
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.NonStochasticRevisited
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

/-!
# Symmetry of information for ordinary plain complexity

SUV §2.3 (Kolmogorov–Levin) in the budgeted form used throughout VS40 §7:

`C(y) + C(x | y) ≤ C(x) + C(y | x) + O(log N)`

whenever all three complexities on the right are bounded by `N`.

The proof is a bridge from the already formalized *prefix* statement
`KP_mutual_symm_le_of_complexity_budget`:

* `C(z) ≤ K(z) + O(1)` and `C(z | w) ≤ K(z | w) + O(1)`
  (`plainK_le_KPPlain`, `condK_le_KP`) give the left-hand side;
* conversely `K(z | w) ≤ C(z | w) + O(log N)` once the *exact* value of
  `C(z | w)` is available to the prefix machine as a self-delimiting length
  field (`KP_le_condK_of_logSlack_budget` below, a corollary of the exact-budget
  decompressor `conditionalPlainLengthDecompressor`); this is where the
  logarithmic term is paid.

The consumer form used by VS40 §7 is `condK_reverse_of_plain_complexity_gap`:
if `x` is at most `delta` more complex than `y` and `C(y | x) ≤ s`, then
`C(x | y) ≤ delta + s + O(log N)`.

Note on placement: the exact-budget decompressor is currently duplicated in
`Prefix/ExactBudget.lean` (an orphan module that no other file imports and whose
`conditionalPlainLengthDecompressor` clashes with the copy in
`StrongModels/AddNoise.lean`).  This file builds on the `AddNoise.lean` copy so
that the result is available inside the §7 import graph; once the duplication is
resolved it should move next to the prefix symmetry-of-information development.
-/

namespace Kolmogorov

/-- Prefix conditional complexity is bounded by ordinary conditional complexity
plus a logarithmic term, provided the *exact* value `k` of the ordinary
complexity is known to be at most the budget `N`.  The length field `k` is
supplied to the exact-budget decompressor and then removed at cost
`K(k) = O(log N)`. -/
theorem KP_le_condK_of_logSlack_budget
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : Nat, ∀ x y (k N : Nat),
      condK V x y = (k : ENat) →
      k ≤ N →
      KP U x y ≤ ((k + logSlack C N : Nat) : ENat) := by
  obtain ⟨c_exact, h_exact⟩ := KP_le_condK_given_plain_program_length V U hV hU
  obtain ⟨c_rem, h_rem⟩ := KP_cond_remove_short_info U hU
  obtain ⟨c_len, h_len⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c_len + c_exact + c_rem + 2, fun x y k N hk hN => ?_⟩
  set C := c_len + c_exact + c_rem + 2 with hC
  have h2 : KP U x y ≤
      KP U x (pairCode y (Nat.bits k)) + KPPlain U (Nat.bits k) + (c_rem : ENat) :=
    h_rem x y (Nat.bits k)
  have h3 : KPPlain U (Nat.bits k) ≤ ((2 * (Nat.bits k).length + c_len : ℕ) : ENat) := by
    calc KPPlain U (Nat.bits k)
        ≤ 2 * ((Nat.bits k).length : ENat) + (c_len : ENat) := h_len (Nat.bits k)
      _ = ((2 * (Nat.bits k).length + c_len : ℕ) : ENat) := by push_cast; ring
  have h_bound :
      k + c_exact + (2 * (Nat.bits k).length + c_len) + c_rem ≤ k + logSlack C N := by
    have hk_len : (Nat.bits k).length ≤ (Nat.bits N).length := length_natBits_mono hN
    unfold logSlack
    have hmul : 2 * (Nat.bits k).length ≤ C * (Nat.bits N).length := by
      calc 2 * (Nat.bits k).length ≤ 2 * (Nat.bits N).length := by omega
        _ ≤ C * (Nat.bits N).length := Nat.mul_le_mul_right _ (by omega)
    omega
  calc
    KP U x y ≤ KP U x (pairCode y (Nat.bits k)) + KPPlain U (Nat.bits k) + (c_rem : ENat) := h2
    _ ≤ ((k + c_exact : Nat) : ENat) + ((2 * (Nat.bits k).length + c_len : ℕ) : ENat)
          + (c_rem : ENat) := by
          gcongr
          exact_mod_cast h_exact x y k hk
    _ = ((k + c_exact + (2 * (Nat.bits k).length + c_len) + c_rem : Nat) : ENat) := by
          push_cast; abel
    _ ≤ ((k + logSlack C N : Nat) : ENat) := by exact_mod_cast h_bound

/-- Symmetry of information for ordinary plain complexity, in budgeted form:
`C(y) + C(x | y) ≤ C(x) + C(y | x) + O(log N)` whenever `C(x)`, `C(y)` and
`C(y | x)` are at most `N`. -/
theorem plainK_add_condK_symmetry
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : Nat, ∀ (x y : BitString) (N : Nat),
      plainK V x ≤ (N : ENat) →
      plainK V y ≤ (N : ENat) →
      condK V y x ≤ (N : ENat) →
      plainK V y + condK V x y ≤
        plainK V x + condK V y x + (logSlack C N : ENat) := by
  obtain ⟨cB, hB⟩ := KP_le_condK_of_logSlack_budget V U hV hU
  obtain ⟨c1, h1⟩ := condK_le_KP V U hV hU.isPrefixDecompressor
  obtain ⟨cS, hS⟩ := KP_mutual_symm_le_of_complexity_budget U hU
  obtain ⟨cLin, hLin⟩ := logSlack_linear_bound cS (cB + 1) cB
  refine ⟨cLin + 2 * cB + 2 * c1, fun x y N hx hy hyx => ?_⟩
  obtain ⟨kx, hkx⟩ : ∃ k : Nat, plainK V x = (k : ENat) :=
    ⟨(plainK V x).toNat, (ENat.natCast_toNat (condK_ne_top_of_optimal V hV x [])).symm⟩
  obtain ⟨ky, hky⟩ : ∃ k : Nat, plainK V y = (k : ENat) :=
    ⟨(plainK V y).toNat, (ENat.natCast_toNat (condK_ne_top_of_optimal V hV y [])).symm⟩
  obtain ⟨s, hs⟩ : ∃ k : Nat, condK V y x = (k : ENat) :=
    ⟨(condK V y x).toNat, (ENat.natCast_toNat (condK_ne_top_of_optimal V hV y x)).symm⟩
  have hkxN : kx ≤ N := by rw [hkx] at hx; exact_mod_cast hx
  have hkyN : ky ≤ N := by rw [hky] at hy; exact_mod_cast hy
  have hsN : s ≤ N := by rw [hs] at hyx; exact_mod_cast hyx
  set M := N + logSlack cB N with hM
  have hKPx : KPPlain U x ≤ ((kx + logSlack cB N : Nat) : ENat) := hB x [] kx N hkx hkxN
  have hKPy : KPPlain U y ≤ ((ky + logSlack cB N : Nat) : ENat) := hB y [] ky N hky hkyN
  have hKPyx : KP U y x ≤ ((s + logSlack cB N : Nat) : ENat) := hB y x s N hs hsN
  have hKPyM : KPPlain U y ≤ (M : ENat) := by
    refine hKPy.trans ?_
    exact_mod_cast Nat.add_le_add_right hkyN _
  have hsym := hS x y M hKPyM
  have hMle : M ≤ (cB + 1) * N + cB := by
    have hlen := length_natBits_le_self N
    have hmul : cB * (Nat.bits N).length ≤ cB * N := Nat.mul_le_mul_left _ hlen
    calc M = N + (cB * (Nat.bits N).length + cB) := by rw [hM, logSlack]
      _ ≤ N + (cB * N + cB) := by omega
      _ = (cB + 1) * N + cB := by ring
  have hslack : logSlack cS M ≤ logSlack cLin N :=
    (logSlack_mono_right cS hMle).trans (hLin N)
  calc plainK V y + condK V x y
      ≤ (KPPlain U y + (c1 : ENat)) + (KP U x y + (c1 : ENat)) := by
        gcongr
        · exact h1 y []
        · exact h1 x y
    _ = (KPPlain U y + KP U x y) + ((2 * c1 : Nat) : ENat) := by push_cast; ring
    _ ≤ (KPPlain U x + KP U y x + (logSlack cS M : ENat)) + ((2 * c1 : Nat) : ENat) := by
        gcongr
    _ ≤ (((kx + logSlack cB N : Nat) : ENat) + ((s + logSlack cB N : Nat) : ENat)
          + (logSlack cLin N : ENat)) + ((2 * c1 : Nat) : ENat) := by
        gcongr
    _ = plainK V x + condK V y x
          + ((2 * logSlack cB N + logSlack cLin N + 2 * c1 : Nat) : ENat) := by
        rw [hkx, hs]; push_cast; ring
    _ ≤ plainK V x + condK V y x + (logSlack (cLin + 2 * cB + 2 * c1) N : ENat) := by
        have hfin : 2 * logSlack cB N + logSlack cLin N + 2 * c1
            ≤ logSlack (cLin + 2 * cB + 2 * c1) N := by
          simp only [logSlack]; ring_nf; omega
        gcongr

/-- Consumer form of symmetry of information: if `x` is at most `delta` more
complex than `y`, and `y` is described by `s` bits given `x`, then `x` is
described by `delta + s + O(log N)` bits given `y`. -/
theorem condK_reverse_of_plain_complexity_gap
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : Nat, ∀ (x y : BitString) (N delta s : Nat),
      plainK V x ≤ (N : ENat) →
      plainK V y ≤ (N : ENat) →
      condK V y x ≤ (s : ENat) →
      s ≤ N →
      plainK V x ≤ plainK V y + (delta : ENat) →
      condK V x y ≤ ((delta + s : Nat) : ENat) + (logSlack C N : ENat) := by
  obtain ⟨C, hC⟩ := plainK_add_condK_symmetry V U hV hU
  refine ⟨C, fun x y N delta s hx hy hyx hsN hgap => ?_⟩
  have hyxN : condK V y x ≤ (N : ENat) :=
    hyx.trans (by exact_mod_cast hsN)
  have hsym := hC x y N hx hy hyxN
  obtain ⟨ky, hky⟩ : ∃ k : Nat, plainK V y = (k : ENat) :=
    ⟨(plainK V y).toNat, (ENat.natCast_toNat (condK_ne_top_of_optimal V hV y [])).symm⟩
  have hchain :
      (ky : ENat) + condK V x y ≤
        (ky : ENat) + (((delta + s : Nat) : ENat) + (logSlack C N : ENat)) := by
    calc (ky : ENat) + condK V x y
        = plainK V y + condK V x y := by rw [hky]
      _ ≤ plainK V x + condK V y x + (logSlack C N : ENat) := hsym
      _ ≤ (plainK V y + (delta : ENat)) + (s : ENat) + (logSlack C N : ENat) := by
          gcongr
      _ = (ky : ENat) + (((delta + s : Nat) : ENat) + (logSlack C N : ENat)) := by
          rw [hky]; push_cast; ring
  exact (WithTop.add_le_add_iff_left (ENat.natCast_ne_top ky)).mp hchain

end Kolmogorov
