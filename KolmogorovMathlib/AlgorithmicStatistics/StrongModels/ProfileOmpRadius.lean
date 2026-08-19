import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileEndpointBound

/-!
# The neighborhood radius in the `m_P_eps` corner of Lemma `omp`

A member `x` of the `epsilon`-neighborhood of a profile `P` carries a standard
block `(i, j)` whose two-part budget satisfies `i + j ≤ C(x) + O(log C(x))`, and
the endpoint estimate bounds `C(x)` by `k_P + 2 * epsilon + O(log (k_P + 2 eps))`.
Transporting such a block into the shifted diagonal that defines `m_P_eps`
costs `epsilon` on each coordinate, so the total budget available at radius
`epsilon` is `k_P + O(log)`, whereas the block only supplies
`k_P + 2 * epsilon + O(log)`.

This file settles that quantitative corner:

* `m_P_eps_le_of_profileNeighborhood_point_widened` and
  `m_P_eps_three_radius_le_standardBlock_complexity` show that the transfer *is*
  available once the radius used inside `m_P_eps` is enlarged from `epsilon` to
  `3 * epsilon`; the enlargement absorbs exactly the missing `2 * epsilon`.
* `not_m_P_eps_le_neighborhood_point_add_logSlack` shows that at the original
  radius `epsilon` the corresponding profile-geometric conclusion is false:
  for every constant `c` there is an admissible profile `P` and a transferred
  neighborhood point `(i, j)` obeying every numerical budget used by that
  geometry argument, with
  `m_P_eps P k_P epsilon c > i + logSlack c n_P`.

So the missing `2 * epsilon` cannot be removed by any argument that uses only
the profile geometry (upper closure, the step condition, and the endpoint
values); it is a genuine feature of the plane, not a gap in the bookkeeping.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Arithmetic folding step: a two-part budget measured on the scale `B = M + c₀ log M`
with an extra `O(log B)` term is measured on the scale `M` with a doubled constant. -/
theorem two_part_budget_fold_of_slack
    (s M Lb L' c₀ C₁ X : Nat)
    (h1 : s ≤ M + (c₀ * Lb + c₀) + X)
    (h2 : X ≤ C₁ * Lb + C₁)
    (h3 : 1 ≤ Lb) (h4 : Lb ≤ L') :
    s ≤ M + 2 * (c₀ + C₁) * L' := by
  nlinarith

/-- Neighborhood transfer of a single profile point: a point of the plain
description profile of a member of the `epsilon`-neighborhood of `P` becomes a
point of `P` after shifting both coordinates by `epsilon`. -/
theorem profileNeighborhood_shift_mem
    (V : Map) (P : Set (Nat × Nat)) (epsilon i j : Nat) (x : BitString)
    (hUp : IsUpperSet P)
    (hx : x ∈ profileNeighborhood V P epsilon)
    (hij : (i, j) ∈ plainDescriptionProfileSet V x) :
    (i + epsilon, j + epsilon) ∈ P := by
  have hnear : ProfileSetsWithinNeighborhood
      (plainDescriptionProfileSet V x) P epsilon := hx
  obtain ⟨q, hq, hdist⟩ := hnear.1 (i, j) hij
  unfold natPairLInfDistance at hdist
  have h1 := (Nat.le_max_left ((i - q.1) + (q.1 - i))
    ((j - q.2) + (q.2 - j))).trans hdist
  have h2 := (Nat.le_max_right ((i - q.1) + (q.1 - i))
    ((j - q.2) + (q.2 - j))).trans hdist
  exact hUp (show q ≤ (i + epsilon, j + epsilon) from ⟨by omega, by omega⟩) hq

/-- Widened-radius transfer into the shifted diagonal defining `m_P_eps`: a
two-part description of a member of the `epsilon`-neighborhood of `P` whose
budget `i + j` exceeds the visible scale `k_P` by at most `delta` plus
logarithmic slack certifies `m_P_eps ≤ i` at radius `epsilon + delta`.

For `delta = 0` this is `m_P_eps_le_of_profileNeighborhood_point`; the point of
the statement is that every unit of excess budget can be paid by one unit of
extra neighborhood radius. -/
theorem m_P_eps_le_of_profileNeighborhood_point_widened
    (V : Map) (P : Set (Nat × Nat)) (kp epsilon delta c i j : Nat) (x : BitString)
    (hUp : IsUpperSet P)
    (hkP : k_P P = (kp : ENat))
    (hx : x ∈ profileNeighborhood V P epsilon)
    (hij : (i, j) ∈ plainDescriptionProfileSet V x)
    (hbudget :
      i + j ≤ kp + delta + c * (kp + 2 * (epsilon + delta)).bits.length) :
    m_P_eps P kp (epsilon + delta) c ≤ (i : ENat) := by
  rcases Nat.lt_or_ge i kp with hik | hik
  · have hshift : (i + epsilon, j + epsilon) ∈ P :=
      profileNeighborhood_shift_mem V P epsilon i j x hUp hx hij
    refine m_P_eps_le_of_mem P kp (epsilon + delta) c i ?_
    refine hUp (a := (i + epsilon, j + epsilon)) ?_ hshift
    exact ⟨by simp only; omega, by simp only; omega⟩
  · exact (m_P_eps_le_k_P_of_eq P kp (epsilon + delta) c hUp hkP).trans
      (by exact_mod_cast hik)

/-- **Standard-block corner at radius `3 * epsilon`.**  For a member `x` of the
`epsilon`-neighborhood of `P`, any standard block of `x` at its own plain
complexity level whose two-part budget is within logarithmic slack of `C(x)`
witnesses `m_P_eps P k_P (3 * epsilon) C ≤ i`, where `i` is the plain complexity
of the block's canonical uniform code.

The radius `3 * epsilon` is exactly `epsilon` (paid by the neighborhood
transfer) plus `2 * epsilon` (paid by the endpoint estimate for `C(x)`).  By
`not_m_P_eps_le_neighborhood_point_add_logSlack`, the corresponding generic
profile-point conclusion at radius `epsilon` is false; that result is not an
actual-string counterexample to the full frozen lemma. -/
theorem m_P_eps_three_radius_le_standardBlock_complexity
    (V : Map) (hV : isOptimalConditional V) (c_in : Nat) :
    ∃ C : Nat, ∀ (P : Set (Nat × Nat)) (q : Nat.Partrec.Code)
        (kp epsilon m j i : Nat) (x : BitString),
      IsUpperSet P →
      k_P P = (kp : ENat) →
      x ∈ profileNeighborhood V P epsilon →
      plainK V x = (m : ENat) →
      (hx : x ∈ standardBlock q m j x) →
      plainK V (codedUniformOn (standardBlock q m j x) ⟨x, hx⟩).code = (i : ENat) →
      i + j ≤ m + logSlack c_in m →
      m_P_eps P kp (3 * epsilon) C ≤ (i : ENat) := by
  obtain ⟨c₀, hsharp⟩ := plainK_upper_of_profileNeighborhood_endpoint_sharp V hV
  obtain ⟨C₁, hC₁⟩ := logSlack_linear_bound c_in (1 + c₀) c₀
  refine ⟨2 * (c₀ + C₁), ?_⟩
  intro P q kp epsilon m j i x hUp hkP hxP hm hx hi hij
  set C : Nat := 2 * (c₀ + C₁) with hC
  have h3 : (3 : Nat) * epsilon = epsilon + 2 * epsilon := by ring
  rw [h3]
  rcases Nat.lt_or_ge i kp with hik | hik
  · -- The block is a genuine profile point of `x`.
    have hcard : (standardBlock q m j x).card ≤ 2 ^ j :=
      le_of_eq (card_standardBlock_of_mem q m j x hx)
    have hpoint : (i, j) ∈ plainDescriptionProfileSet V x :=
      ⟨standardBlock q m j x, ⟨x, hx⟩, hx, le_of_eq hi, hcard⟩
    -- The endpoint estimate bounds `C(x)` on the visible scale `kp + 2 * eps`.
    set M : Nat := kp + 2 * epsilon with hM
    set B : Nat := M + logSlack c₀ M with hB
    have hmB : m ≤ B := by
      have := hsharp P kp epsilon x hkP hxP
      rw [hm] at this
      exact_mod_cast this
    -- Fold the block budget onto the visible scale.
    have hLb : 1 ≤ (Nat.bits M).length := by
      have h1 : 1 ≤ M := by omega
      have := length_natBits_mono h1
      simpa using this
    have hBlin : B ≤ (1 + c₀) * M + c₀ := by
      have hle : (Nat.bits M).length ≤ M := length_natBits_le_self M
      rw [hB]
      unfold logSlack
      nlinarith
    have hslack : logSlack c_in B ≤ logSlack C₁ M :=
      (logSlack_mono_right c_in hBlin).trans (hC₁ M)
    have hLM : (Nat.bits M).length ≤
        (Nat.bits (kp + 2 * (epsilon + 2 * epsilon))).length :=
      length_natBits_mono (by omega)
    have hbudget : i + j ≤ kp + 2 * epsilon +
        C * (kp + 2 * (epsilon + 2 * epsilon)).bits.length := by
      have hstep : i + j ≤ B + logSlack c_in B :=
        hij.trans (Nat.add_le_add hmB (logSlack_mono_right c_in hmB))
      have hBval : B = M + (c₀ * (Nat.bits M).length + c₀) := rfl
      unfold logSlack at hstep hslack
      have hfold := two_part_budget_fold_of_slack (i + j) M (Nat.bits M).length
        (Nat.bits (kp + 2 * (epsilon + 2 * epsilon))).length c₀ C₁
        (c_in * (Nat.bits B).length + c_in) (by omega) hslack hLb hLM
      simpa [hM, hC] using hfold
    exact m_P_eps_le_of_profileNeighborhood_point_widened V P kp epsilon
      (2 * epsilon) C i j x hUp hkP hxP hpoint hbudget
  · exact (m_P_eps_le_k_P_of_eq P kp (epsilon + 2 * epsilon) C hUp hkP).trans
      (by exact_mod_cast hik)

/-! ### Unit-drop profile sets

The counterexample below uses a profile set whose boundary *jumps*: its height
drops from `3 * E` to `0` in a single step of the complexity coordinate.
`IsAdmissibleProfileSet` permits such jumps, because its shift condition only
moves log-cardinality into complexity, never back.  Profile boundaries that
descend by at most one unit of log-cardinality per unit of complexity satisfy
the reverse implication as well, and for those the exact-`epsilon` corner is
available outright: the shifted diagonal defining `m_P_eps` is reached already
at complexity `0`. -/

/-- Unit-drop (slope) condition on a profile set: lowering the complexity
coordinate by one can be paid for by raising the log-cardinality coordinate by
one.  Equivalently, the boundary height of `P` drops by at most one per unit of
complexity. -/
def IsUnitDropProfileSet (P : Set (Nat × Nat)) : Prop :=
  ∀ a b : Nat, (a + 1, b) ∈ P → (a, b + 1) ∈ P

/-- Iterated form of the unit-drop condition: complexity can be traded back into
log-cardinality at rate one, in arbitrarily large steps. -/
theorem mem_of_isUnitDropProfileSet
    (P : Set (Nat × Nat)) (hdrop : IsUnitDropProfileSet P) :
    ∀ (d a b : Nat), (a + d, b) ∈ P → (a, b + d) ∈ P := by
  intro d
  induction d with
  | zero => intro a b h; simpa using h
  | succ d ih =>
    intro a b h
    have h' : ((a + 1) + d, b) ∈ P := by
      have hidx : a + (d + 1) = (a + 1) + d := by omega
      rwa [hidx] at h
    have h'' : (a + 1, b + d) ∈ P := ih (a + 1) b h'
    have hstep := hdrop a (b + d) h''
    have heq : b + d + 1 = b + (d + 1) := by omega
    rwa [heq] at hstep

/-- **The exact-`epsilon` corner is free for unit-drop profile sets.**  If `P`
has no boundary jumps and `epsilon ≤ k_P`, then the shifted diagonal defining
`m_P_eps` already meets `P` at complexity `0`, so `m_P_eps P k_P epsilon c = 0`.

This is the exact radius `epsilon`, not the widened radius `3 * epsilon`, and it
needs no information about any string. -/
theorem m_P_eps_eq_zero_of_isUnitDropProfileSet
    (P : Set (Nat × Nat)) (kp epsilon c : Nat)
    (hUp : IsUpperSet P)
    (hdrop : IsUnitDropProfileSet P)
    (hkP : k_P P = (kp : ENat))
    (heps : epsilon ≤ kp) :
    m_P_eps P kp epsilon c = 0 := by
  have hk : (kp, 0) ∈ P := k_P_mem_of_eq P kp hkP
  have hk' : (epsilon + (kp - epsilon), 0) ∈ P := by
    have hsum : epsilon + (kp - epsilon) = kp := by omega
    rwa [hsum]
  have hdown : (epsilon, 0 + (kp - epsilon)) ∈ P :=
    mem_of_isUnitDropProfileSet P hdrop (kp - epsilon) epsilon 0 hk'
  have hmem : (0 + epsilon,
      kp - 0 + c * (kp + 2 * epsilon).bits.length + epsilon) ∈ P := by
    refine hUp (a := (epsilon, 0 + (kp - epsilon))) ?_ hdown
    exact Prod.mk_le_mk.mpr ⟨by omega, by omega⟩
  have hle : m_P_eps P kp epsilon c ≤ ((0 : Nat) : ENat) :=
    m_P_eps_le_of_mem P kp epsilon c 0 hmem
  simpa using le_antisymm hle (by simp)

/-- A second, orthogonal sufficient condition for the exact-`epsilon` corner:
if the height endpoint `n_P` is already within the diagonal budget, then the
shifted diagonal is met at complexity `0` by the height endpoint itself. -/
theorem m_P_eps_eq_zero_of_n_P_le
    (P : Set (Nat × Nat)) (kp np epsilon c : Nat)
    (hUp : IsUpperSet P)
    (hnP : n_P P = (np : ENat))
    (hle : np ≤ kp + c * (kp + 2 * epsilon).bits.length + epsilon) :
    m_P_eps P kp epsilon c = 0 := by
  have hn : (0, np) ∈ P := n_P_mem_of_eq P np hnP
  have hmem : (0 + epsilon,
      kp - 0 + c * (kp + 2 * epsilon).bits.length + epsilon) ∈ P := by
    refine hUp (a := (0, np)) ?_ hn
    exact Prod.mk_le_mk.mpr ⟨by omega, by omega⟩
  have hzero : m_P_eps P kp epsilon c ≤ ((0 : Nat) : ENat) :=
    m_P_eps_le_of_mem P kp epsilon c 0 hmem
  simpa using le_antisymm hzero (by simp)

/-- **The height endpoint bounds `m_P_eps` with two `epsilon`'s of room.**

For an admissible profile set `P` the step rule moves the height endpoint
`(0, n_P)` to `(epsilon, n_P - epsilon)`; closing upwards from there reaches the
`t = 0` point of the shifted diagonal as soon as
`n_P ≤ k_P + 2 * epsilon + c * log(k_P + 2 * epsilon)`.

This strengthens `m_P_eps_eq_zero_of_n_P_le`, which needs the same bound with a
single `epsilon`, by using admissibility instead of upward closure alone. -/
theorem m_P_eps_eq_zero_of_n_P_le_add_two_mul
    (P : Set (Nat × Nat)) (kp np epsilon c : Nat)
    (hadm : IsAdmissibleProfileSet P)
    (hnP : n_P P = (np : ENat))
    (hle : np ≤ kp + 2 * epsilon + c * (kp + 2 * epsilon).bits.length) :
    m_P_eps P kp epsilon c = 0 := by
  have hn : (0, np) ∈ P := n_P_mem_of_eq P np hnP
  set d : Nat := min epsilon np with hd
  have hdle : d ≤ epsilon ∧ d ≤ np ∧ (d = epsilon ∨ d = np) := by
    rw [hd]; omega
  have hsplit : (0, d + (np - d)) ∈ P := by
    have h : d + (np - d) = np := by omega
    rwa [h]
  have hshift : (0 + d, np - d) ∈ P := hadm.step 0 d (np - d) hsplit
  have hmem : (0 + epsilon,
      kp - 0 + c * (kp + 2 * epsilon).bits.length + epsilon) ∈ P := by
    refine hadm.isUpperSet (a := (0 + d, np - d)) ?_ hshift
    exact Prod.mk_le_mk.mpr ⟨by omega, by omega⟩
  have hzero : m_P_eps P kp epsilon c ≤ ((0 : Nat) : ENat) :=
    m_P_eps_le_of_mem P kp epsilon c 0 hmem
  simpa using le_antisymm hzero (by simp)

/-- The unconditional upper bound `m_P_eps P k_P epsilon c ≤ k_P - epsilon`:
the shifted diagonal always meets `P` no later than the complexity endpoint. -/
theorem m_P_eps_le_k_P_sub_of_isUpperSet
    (P : Set (Nat × Nat)) (kp epsilon c : Nat)
    (hUp : IsUpperSet P)
    (hkP : k_P P = (kp : ENat)) :
    m_P_eps P kp epsilon c ≤ ((kp - epsilon : Nat) : ENat) := by
  have hk : (kp, 0) ∈ P := k_P_mem_of_eq P kp hkP
  refine m_P_eps_le_of_mem P kp epsilon c (kp - epsilon) ?_
  refine hUp (a := (kp, 0)) ?_ hk
  exact Prod.mk_le_mk.mpr ⟨by omega, by omega⟩

/-! ### The unit-drop class is not vacuous

The diagonal half-plane `{(i, j) | n ≤ i + j}` — the shape of the plain
description profile of an incompressible string of length `n` — is admissible,
jump-free, and has both endpoints equal to `n`. -/

/-- The diagonal half-plane profile set with endpoints `n`. -/
def diagonalProfileSet (n : Nat) : Set (Nat × Nat) := {p | n ≤ p.1 + p.2}

theorem isAdmissibleProfileSet_diagonalProfileSet (n : Nat) :
    IsAdmissibleProfileSet (diagonalProfileSet n) := by
  refine ⟨⟨(n, 0), by simp [diagonalProfileSet]⟩, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨ha, hb⟩ h
    simp only [diagonalProfileSet, Set.mem_ofPred_eq] at h ⊢
    simp only at ha hb
    omega
  · rintro a b d h
    simp only [diagonalProfileSet, Set.mem_ofPred_eq] at h ⊢
    omega

theorem isUnitDropProfileSet_diagonalProfileSet (n : Nat) :
    IsUnitDropProfileSet (diagonalProfileSet n) := by
  intro a b h
  simp only [diagonalProfileSet, Set.mem_ofPred_eq] at h ⊢
  omega

theorem k_P_diagonalProfileSet (n : Nat) :
    k_P (diagonalProfileSet n) = (n : ENat) := by
  refine le_antisymm (sInf_le ⟨n, rfl, by simp [diagonalProfileSet]⟩) (le_sInf ?_)
  rintro _ ⟨t, rfl, ht⟩
  simp only [diagonalProfileSet, Set.mem_ofPred_eq] at ht
  exact_mod_cast (by omega : n ≤ t)

theorem n_P_diagonalProfileSet (n : Nat) :
    n_P (diagonalProfileSet n) = (n : ENat) := by
  refine le_antisymm (sInf_le ⟨n, rfl, by simp [diagonalProfileSet]⟩) (le_sInf ?_)
  rintro _ ⟨t, rfl, ht⟩
  simp only [diagonalProfileSet, Set.mem_ofPred_eq] at ht
  exact_mod_cast (by omega : n ≤ t)

/-! ### The radius cannot be kept at `epsilon`

The counterexample below is purely two-dimensional: it exhibits an admissible
profile set together with a transferred neighborhood point that satisfies every
numerical constraint the standard-block construction can supply, and for which
the conclusion `m_P_eps P kp epsilon c ≤ i + logSlack c np` fails. -/

/-- An exponential dominates a linear function of its exponent, in the explicit
form needed to pick the scale of the counterexample. -/
theorem exists_two_pow_gt_linear (c : Nat) : ∃ K : Nat, c * (K + 5) < 2 ^ K := by
  refine ⟨3 * c + 10, ?_⟩
  have h1 : c < 2 ^ c := Nat.lt_two_pow_self
  have hpow : c + 5 < 2 ^ (c + 5) := Nat.lt_two_pow_self
  have h2 : 3 * c + 10 + 5 < 2 ^ (2 * c + 10) := by
    have hsplit : 2 ^ (2 * c + 10) = 2 ^ (c + 5) * 2 ^ (c + 5) := by
      rw [← pow_add]; ring_nf
    rw [hsplit]
    nlinarith
  have hmul : c * (3 * c + 10 + 5) < 2 ^ c * 2 ^ (2 * c + 10) :=
    Nat.mul_lt_mul_of_lt_of_lt h1 h2
  calc c * (3 * c + 10 + 5) < 2 ^ c * 2 ^ (2 * c + 10) := hmul
    _ = 2 ^ (3 * c + 10) := by rw [← pow_add]; ring_nf

/-- **The `epsilon`-radius corner of Lemma `omp` is false at the profile level.**

For every constant `c` there are an admissible profile set `P` with finite
endpoints `k_P = kp`, `n_P = np`, a radius `epsilon ≤ kp`, and a point `(i, j)`
whose `epsilon`-shift lies in `P` (this is exactly what neighborhood transfer
supplies for a two-part description of a neighborhood member) with two-part
budget `i + j ≤ kp + 2 * epsilon` (this is exactly what the endpoint estimate
supplies for a standard block of a neighborhood member), such that

`m_P_eps P kp epsilon c > i + logSlack c np`.

Hence no argument based only on the profile geometry can bound `m_P_eps` at
radius `epsilon` by the standard-block complexity plus logarithmic slack; the
radius has to be widened, as in
`m_P_eps_three_radius_le_standardBlock_complexity`. -/
theorem not_m_P_eps_le_neighborhood_point_add_logSlack (c : Nat) :
    ∃ (P : Set (Nat × Nat)) (kp np epsilon i j : Nat),
      IsAdmissibleProfileSet P ∧
      epsilon ≤ kp ∧
      k_P P = (kp : ENat) ∧
      n_P P = (np : ENat) ∧
      (i + epsilon, j + epsilon) ∈ P ∧
      i + j ≤ kp + 2 * epsilon ∧
      ¬ m_P_eps P kp epsilon c ≤ (i : ENat) + (logSlack c np : ENat) := by
  obtain ⟨K, hK⟩ := exists_two_pow_gt_linear c
  set E : Nat := 2 ^ K with hE
  have hE1 : 1 ≤ E := Nat.one_le_two_pow
  have hkey : c * (K + 3) + c < E := by
    have hle : c * (K + 3) + c ≤ c * (K + 5) := by nlinarith
    exact lt_of_le_of_lt hle hK
  -- Binary lengths on the scale of the counterexample.
  have hbits : ∀ n : Nat, n < 8 * E → (Nat.bits n).length ≤ K + 3 := by
    intro n hn
    rw [Nat.size_eq_bits_len]
    refine Nat.size_le.mpr ?_
    have h8 : (8 : Nat) * E = 2 ^ (K + 3) := by
      rw [hE, pow_add]; ring
    omega
  set P : Set (Nat × Nat) := {p | 2 * E ≤ p.1 ∨ 5 * E ≤ p.1 + p.2} with hP
  refine ⟨P, 2 * E, 5 * E, E, 0, 3 * E, ?_, by omega, ?_, ?_, ?_, by omega, ?_⟩
  · -- admissibility
    refine ⟨⟨(2 * E, 0), Or.inl le_rfl⟩, ?_, ?_⟩
    · rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨ha, hb⟩ h
      rcases h with h | h
      · exact Or.inl (by simp only at ha ⊢; omega)
      · exact Or.inr (by simp only at ha hb ⊢; omega)
    · rintro a b d h
      rcases h with h | h
      · exact Or.inl (by simp only at h ⊢; omega)
      · exact Or.inr (by simp only at h ⊢; omega)
  · -- k_P
    refine le_antisymm ?_ ?_
    · exact sInf_le ⟨2 * E, rfl, Or.inl le_rfl⟩
    · refine le_sInf ?_
      rintro _ ⟨n, rfl, hn⟩
      have : 2 * E ≤ n := by
        rcases hn with h | h <;> simp only at h <;> omega
      exact_mod_cast this
  · -- n_P
    refine le_antisymm ?_ ?_
    · exact sInf_le ⟨5 * E, rfl, Or.inr (by simp only; omega)⟩
    · refine le_sInf ?_
      rintro _ ⟨n, rfl, hn⟩
      have : 5 * E ≤ n := by
        rcases hn with h | h <;> simp only at h <;> omega
      exact_mod_cast this
  · -- the transferred neighborhood point
    exact Or.inr (by simp only; omega)
  · -- the failure of the conclusion
    intro hle
    have hlow : (E : ENat) ≤ m_P_eps P (2 * E) E c := by
      refine le_sInf ?_
      rintro _ ⟨n, rfl, hn⟩
      have hL : c * (Nat.bits (2 * E + 2 * E)).length ≤ c * (K + 3) :=
        Nat.mul_le_mul_left _ (hbits _ (by omega))
      have : E ≤ n := by
        rcases hn with h | h <;> simp only at h <;> omega
      exact_mod_cast this
    have hup : (E : ENat) ≤ ((0 : Nat) : ENat) + (logSlack c (5 * E) : ENat) :=
      hlow.trans hle
    have hnat : E ≤ logSlack c (5 * E) := by
      have : (E : ENat) ≤ (logSlack c (5 * E) : ENat) := by simpa using hup
      exact_mod_cast this
    have hLb : (Nat.bits (5 * E)).length ≤ K + 3 := hbits _ (by omega)
    have : c * (Nat.bits (5 * E)).length ≤ c * (K + 3) :=
      Nat.mul_le_mul_left _ hLb
    unfold logSlack at hnat
    omega

end Kolmogorov
