import KolmogorovMathlib.InformationInequalities.Typization

/-!
# Size bounds for typization sets

Estimates shared by the two combinatorial interpretations of Sections 10.8 and 10.9: a finite
set is no larger than the product of its one-dimensional projections, a singleton subtuple
costs only a constant more than its coordinate, and the logarithmic slack `(2 + log₂ |A|)^d`
of a typization set built from strings of complexity at most `N` costs `O(log N)` bits.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}
/-- A set is no larger than the product of its one-dimensional projections. -/
theorem card_le_prod_projCard_singleton {Y : Fin n → Type} [∀ i, Finite (Y i)]
    [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i)) :
    A.card ≤ ∏ k : Fin n, projCard A {k} := by
  have : ∀ i, Fintype (Y i) := fun i => Fintype.ofFinite (Y i)
  refine (card_le_chainBound A (Equiv.refl _)).trans ?_
  unfold chainBound
  refine Finset.prod_le_prod fun k _ => ?_
  exact Finset.sup_le fun p _ =>
    Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

/-- Singleton projection bounds control the cardinality of a set. -/
theorem logb_card_le_of_projCard_singleton {Y : Fin n → Type} [∀ i, Finite (Y i)]
    [∀ i, DecidableEq (Y i)] {A : Finset (∀ i, Y i)} (hA : A.Nonempty) {r : ℝ}
    (h : ∀ k, Real.logb 2 (projCard A {k}) ≤ r) : Real.logb 2 A.card ≤ n * r := by
  have hpos : ∀ k, (0 : ℝ) < projCard A {k} := fun k => by
    exact_mod_cast Finset.card_pos.2 (hA.image _)
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.2 hA
  calc
    Real.logb 2 A.card ≤ Real.logb 2 (∏ k : Fin n, (projCard A {k} : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) hApos
        (by exact_mod_cast card_le_prod_projCard_singleton A)
    _ = ∑ k : Fin n, Real.logb 2 (projCard A {k}) :=
      Real.logb_prod _ _ fun k _ => (hpos k).ne'
    _ ≤ ∑ _k : Fin n, r := Finset.sum_le_sum fun k _ => h k
    _ = n * r := by simp

/-- A singleton subtuple has complexity at most that of its coordinate plus a constant. -/
theorem exists_tuplePlainK_singleton_le (D : Map) (hD : isOptimalConditional D) :
    ∃ c0 : ℕ, ∀ (x : Fin n → BitString) (k : Fin n),
      tuplePlainK D x {k} ≤ plainK D (x k) + c0 := by
  obtain ⟨c0, hc⟩ := plainK_map_le D hD (fun s => listCode [s])
    (listCode_computable.comp (Computable.list_cons.comp Computable.id (Computable.const [])))
  refine ⟨c0, fun x k => ?_⟩
  have h : subtupleCode x {k} = listCode [x k] := by simp [subtupleCode]
  rw [tuplePlainK, h]
  exact hc (x k)


/-- Replacing `N` by `max N 2` triples a `logSlack` constant. -/
theorem logSlack_max_two_le_three_mul (c N : ℕ) :
    logSlack c (max N 2) ≤ logSlack (3 * c) N := by
  match N with
  | 0 =>
    have h2 : (Nat.bits 2).length = 2 := rfl
    have h0 : (Nat.bits 0).length = 0 := rfl
    simp only [logSlack, show max 0 2 = 2 from rfl, h2, h0]
    omega
  | 1 =>
    have h2 : (Nat.bits 2).length = 2 := rfl
    have h1 : (Nat.bits 1).length = 1 := rfl
    simp only [logSlack, show max 1 2 = 2 from rfl, h2, h1]
    omega
  | N + 2 =>
    rw [show max (N + 2) 2 = N + 2 by omega]
    simp only [logSlack]
    nlinarith [Nat.zero_le (c * (Nat.bits (N + 2)).length)]

/-- The binary logarithm of `N` is at most the binary length of `N`. -/
theorem logb_le_length_bits (N : ℕ) : Real.logb 2 N ≤ (Nat.bits N).length := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hpow : (N : ℝ) ≤ (2 : ℝ) ^ ((Nat.bits N).length : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (show N < 2 ^ (Nat.bits N).length by
      simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self N).le
  exact (Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hN)).2 hpow

/-- **The logarithmic slack of a typization set.**  If every one-coordinate projection of a
non-empty `A` has log-size at most `N + c₀ + logSlack dt N`, then
`log₂ (2 + log₂ |A|) ≤ ⌈log₂ K⌉ + |bits N|` with `K = 2 + n (1 + c₀ + 3 dt)`: a slack factor
`(2 + log₂ |A|)^d` costs `O(log N)` bits. -/
theorem logb_two_add_logb_card_le {Y : Fin n → Type} [∀ i, Finite (Y i)]
    [∀ i, DecidableEq (Y i)] {A : Finset (∀ i, Y i)} (hA : A.Nonempty) {N c0 dt : ℕ}
    (hN : 1 ≤ N) (h : ∀ k, Real.logb 2 (projCard A {k}) ≤ N + c0 + logSlack dt N) :
    Real.logb 2 (2 + Real.logb 2 A.card) ≤
      ⌈Real.logb 2 ((2 + n * (1 + c0 + 3 * dt) : ℕ) : ℝ)⌉₊ + (Nat.bits N).length := by
  set b : ℕ := (Nat.bits N).length with hb
  set K : ℕ := 2 + n * (1 + c0 + 3 * dt) with hK
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hslack : (logSlack dt N : ℝ) = dt * b + dt := by
    simp only [logSlack, hb]
    push_cast
    ring
  have hbN : (b : ℝ) ≤ N := by
    have : b ≤ N := by
      rw [hb, Nat.size_eq_bits_len]
      exact Nat.size_le.2 Nat.lt_two_pow_self
    exact_mod_cast this
  have hlogN : Real.logb 2 N ≤ b := logb_le_length_bits N
  have hlogA : Real.logb 2 A.card ≤ n * (N + c0 + (dt * b + dt)) :=
    logb_card_le_of_projCard_singleton hA fun k => by
      rw [← hslack]
      exact h k
  set L := Real.logb 2 A.card
  have hApos : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.card_pos.2 hA
  have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two hApos
  have h2L : 2 + L ≤ K * N := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hdt0 : (0 : ℝ) ≤ dt := Nat.cast_nonneg dt
    have hc00 : (0 : ℝ) ≤ c0 := Nat.cast_nonneg c0
    have hbd : (dt : ℝ) * b ≤ dt * N := mul_le_mul_of_nonneg_left hbN hdt0
    have hK' : (K : ℝ) * N = 2 * N + n * (N + c0 * N + 3 * dt * N) := by
      rw [hK]
      push_cast
      ring
    have h1 : (n : ℝ) * (N + c0 + (dt * b + dt)) ≤
        n * (N + c0 * N + 3 * dt * N) := by
      apply mul_le_mul_of_nonneg_left _ hn
      nlinarith
    linarith
  have hKpos : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  calc
    Real.logb 2 (2 + L) ≤ Real.logb 2 (K * N) :=
      Real.logb_le_logb_of_le one_lt_two (by linarith) h2L
    _ = Real.logb 2 K + Real.logb 2 N := Real.logb_mul (by linarith) (by linarith)
    _ ≤ ⌈Real.logb 2 K⌉₊ + b := add_le_add (Nat.le_ceil _) hlogN

end Kolmogorov
