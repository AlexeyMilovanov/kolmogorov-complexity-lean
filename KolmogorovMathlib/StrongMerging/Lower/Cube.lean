import KolmogorovMathlib.StrongMerging.Basic
import KolmogorovMathlib.Restricted.Examples.HammingBalls.Part01

/-!
# The sharp lower bound: parameters and exact Hamming-sphere incidence

Blueprint nodes L05 (`sharpParameters`) and L06 (`sphereIncidence`) of the formalization of
`sublinear-merging.tex` (appendix "Finite geometry and analytical obligations", tex lines
4444-4475; main text "Near-equator parameters and uniform entropy estimates", lines 1506-1530).

* **L05.**  The integer parameters `m, r, w, R, N, b, K, D_a, D_i, d, T, S, τ, ℓ, h, δ` of the
  sharp lower bound are explicit natural-number functions of `M` and `E` (`sharpParameters`),
  computed with `Nat.sqrt`, natural division and `Nat.log 2`.  The truncated subtraction in
  `R = M / 2 - w` is guarded by `sharpParameters_valid`, which proves `w < M / 2`,
  `R + w = M / 2` and the positivity and divisibility facts on the valid domain
  `SharpValid M E` (`2048 ∣ M`, `1 ≤ E ≤ 2⁻¹⁰⁰ M`).
* **L06.**  Hamming spheres `S_z = hammingSphere M z R` of the library: their size, the symmetry
  `u ∈ S_z ↔ z ∈ S_u`, the exact distance-`2k` regularity inside a sphere (the internal degree
  `D_i` for `k = r`), and the ambient star size `D_a = (M choose 2r)`.  Positions are compared
  through `diffSet M u v`, the set of coordinates where `u` and `v` differ.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### L05: the sharp parameters -/

/-- The root radius `r = ⌊√(M E)⌋` of the sharp lower bound. -/
def sharpRootRadius (M E : ℕ) : ℕ :=
  Nat.sqrt (M * E)

/-- The equator shift `w = ⌊√(M r)⌋`. -/
def sharpShift (M E : ℕ) : ℕ :=
  Nat.sqrt (M * sharpRootRadius M E)

/-- The sphere radius `R = M / 2 - w`.  This is a natural subtraction; on the valid domain
`w < M / 2` (`sharpParameters_valid`), so it is the integer difference. -/
def sharpSphereRadius (M E : ℕ) : ℕ :=
  M / 2 - sharpShift M E

/-- The sphere size `N = (M choose R)`. -/
def sharpSphereCard (M E : ℕ) : ℕ :=
  M.choose (sharpSphereRadius M E)

/-- `b = ⌊log₂ N⌋`, computed by `Nat.log 2`. -/
def sharpLogSphereCard (M E : ℕ) : ℕ :=
  Nat.log 2 (sharpSphereCard M E)

/-- The game threshold `K = (M + b) div 2`. -/
def sharpThreshold (M E : ℕ) : ℕ :=
  (M + sharpLogSphereCard M E) / 2

/-- The ambient star size `D_a = (M choose 2r)`. -/
def sharpAmbientDegree (M E : ℕ) : ℕ :=
  M.choose (2 * sharpRootRadius M E)

/-- The internal degree `D_i = (R choose r) ((M - R) choose r)`. -/
def sharpInternalDegree (M E : ℕ) : ℕ :=
  (sharpSphereRadius M E).choose (sharpRootRadius M E) *
    (M - sharpSphereRadius M E).choose (sharpRootRadius M E)

/-- `d = ⌊log₂ D_i⌋`, computed by `Nat.log 2`. -/
def sharpLogInternalDegree (M E : ℕ) : ℕ :=
  Nat.log 2 (sharpInternalDegree M E)

/-- The exact integer parameters of the sharp lower bound (manuscript equations
`eq:ham-parameters-first`, `eq:ham-parameters-degree`, `eq:ham-parameters-game`). -/
structure SharpParams where
  /-- `m = ⌈log₂ (M + 2)⌉`. -/
  m : ℕ
  /-- `r = ⌊√(M E)⌋`. -/
  r : ℕ
  /-- `w = ⌊√(M r)⌋`. -/
  w : ℕ
  /-- `R = M / 2 - w`. -/
  R : ℕ
  /-- `N = (M choose R)`. -/
  N : ℕ
  /-- `b = ⌊log₂ N⌋`. -/
  b : ℕ
  /-- `K = (M + b) div 2`. -/
  K : ℕ
  /-- `D_a = (M choose 2r)`. -/
  Da : ℕ
  /-- `D_i = (R choose r) ((M - R) choose r)`. -/
  Di : ℕ
  /-- `d = ⌊log₂ D_i⌋`. -/
  d : ℕ
  /-- `T = r div 10⁶`. -/
  T : ℕ
  /-- `S = 3 T`. -/
  S : ℕ
  /-- `τ = 6 T`. -/
  tau : ℕ
  /-- `ℓ = M / 8`. -/
  ell : ℕ
  /-- `h = M / 1024`. -/
  h : ℕ
  /-- `δ = r div 10000`. -/
  delta : ℕ

/-- **The sharp parameters** (blueprint node L05): every parameter of the sharp lower bound
by exact integer arithmetic.  `T` is the shared `mergerBudget M E = ⌊√(M E)⌋ / 10⁶`. -/
def sharpParameters (M E : ℕ) : SharpParams where
  m := headerLog M
  r := sharpRootRadius M E
  w := sharpShift M E
  R := sharpSphereRadius M E
  N := sharpSphereCard M E
  b := sharpLogSphereCard M E
  K := sharpThreshold M E
  Da := sharpAmbientDegree M E
  Di := sharpInternalDegree M E
  d := sharpLogInternalDegree M E
  T := mergerBudget M E
  S := 3 * mergerBudget M E
  tau := 6 * mergerBudget M E
  ell := M / 8
  h := M / 1024
  delta := sharpRootRadius M E / 10000

/-- The merger budget is `T = r div 10⁶` for the root radius `r` of `sharpParameters`. -/
theorem mergerBudget_eq_sharpRootRadius_div (M E : ℕ) :
    mergerBudget M E = sharpRootRadius M E / 10 ^ 6 :=
  rfl

/-- The valid domain of the sharp parameters: `2048 ∣ M`, `1 ≤ E` and `E ≤ 2⁻¹⁰⁰ M`.  This is
the range `λ m ≤ E ≤ η M` of the sharp theorem (`η = 2⁻¹⁰⁰`), since `λ m ≥ 1`. -/
def SharpValid (M E : ℕ) : Prop :=
  2048 ∣ M ∧ 1 ≤ E ∧ 2 ^ 100 * E ≤ M

/-- **Square-root scaling.**  If `2^(2k) E ≤ M` then `2^k ⌊√(M E)⌋ ≤ M`.

Proof sketch: put `s = ⌊√(M E)⌋`, so `s² ≤ M E` (`Nat.sqrt_le'`).  Then
`(2^k s)² = 2^(2k) s² ≤ 2^(2k) M E ≤ M²`, hence `2^k s ≤ M` (`Nat.pow_le_pow_left` /
`Nat.mul_self_le_mul_self_iff`).  The case `M = 0` forces `E = 0`.
Reference: tex 1550-1556 (`r/M ≤ 2⁻⁵⁰`, `α ≤ 2⁻²⁵`); node L05.  [leaf: easy] -/
theorem two_pow_mul_sqrt_le {M E k : ℕ} (h : 2 ^ (2 * k) * E ≤ M) :
    2 ^ k * Nat.sqrt (M * E) ≤ M := by
  have hs : Nat.sqrt (M * E) * Nat.sqrt (M * E) ≤ M * E := Nat.sqrt_le (M * E)
  have key : (2 ^ k * Nat.sqrt (M * E)) * (2 ^ k * Nat.sqrt (M * E)) ≤ M * M := by
    calc (2 ^ k * Nat.sqrt (M * E)) * (2 ^ k * Nat.sqrt (M * E))
        = 2 ^ (2 * k) * (Nat.sqrt (M * E) * Nat.sqrt (M * E)) := by rw [pow_mul']; ring
      _ ≤ 2 ^ (2 * k) * (M * E) := Nat.mul_le_mul_left _ hs
      _ = M * (2 ^ (2 * k) * E) := by ring
      _ ≤ M * M := Nat.mul_le_mul_left _ h
  exact Nat.mul_self_le_mul_self_iff.mp key

/-- **Valid-domain facts of the sharp parameters** (blueprint node L05).  On `SharpValid M E`:
`0 < r`, `2⁵⁰ r ≤ M`, `0 < w`, `2²⁵ w ≤ M`, `w < M / 2` (so the subtraction in `R` is exact:
`R + w = M / 2`), `0 < R`, `2 R < M`, `2 r ≤ R`, the positivity of `N, D_a, D_i, h`, and the
divisibilities `M = 2 (M / 2) = 8 ℓ = 1024 h`. -/
theorem sharpParameters_valid {M E : ℕ} (hv : SharpValid M E) :
    0 < sharpRootRadius M E ∧ 2 ^ 50 * sharpRootRadius M E ≤ M ∧
      0 < sharpShift M E ∧ 2 ^ 25 * sharpShift M E ≤ M ∧ sharpShift M E < M / 2 ∧
      sharpSphereRadius M E + sharpShift M E = M / 2 ∧ 0 < sharpSphereRadius M E ∧
      2 * sharpSphereRadius M E < M ∧ 2 * sharpRootRadius M E ≤ sharpSphereRadius M E ∧
      0 < sharpSphereCard M E ∧ 0 < sharpAmbientDegree M E ∧ 0 < sharpInternalDegree M E ∧
      M = 2 * (M / 2) ∧ M = 8 * (M / 8) ∧ M = 1024 * (M / 1024) ∧ 0 < M / 1024 := by
  obtain ⟨hdiv, hE, hEM⟩ := hv
  have hM : 2 ^ 100 ≤ M := le_trans (Nat.le_mul_of_pos_right _ hE) hEM
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hr : 2 ^ 50 * sharpRootRadius M E ≤ M :=
    two_pow_mul_sqrt_le (k := 50) (by rw [show 2 * 50 = 100 from rfl]; exact hEM)
  have hr0 : 0 < sharpRootRadius M E := Nat.sqrt_pos.mpr (Nat.mul_pos hMpos hE)
  have hw : 2 ^ 25 * sharpShift M E ≤ M :=
    two_pow_mul_sqrt_le (k := 25) (by rw [show 2 * 25 = 50 from rfl]; exact hr)
  have hw0 : 0 < sharpShift M E := Nat.sqrt_pos.mpr (Nat.mul_pos hMpos hr0)
  have hRdef : sharpSphereRadius M E = M / 2 - sharpShift M E := rfl
  norm_num at hM hr hw
  have hwlt : sharpShift M E < M / 2 := by omega
  have hRpos : 0 < sharpSphereRadius M E := by omega
  have hrR : 2 * sharpRootRadius M E ≤ sharpSphereRadius M E := by omega
  have hRM : sharpSphereRadius M E ≤ M := by omega
  refine ⟨hr0, by norm_num; exact hr, hw0, by norm_num; exact hw, hwlt, by omega, hRpos,
    by omega, hrR, Nat.choose_pos hRM, Nat.choose_pos (by omega), ?_, by omega, by omega,
    by omega, by omega⟩
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

/-! ### L06: Hamming-sphere incidence -/

/-- The positions `i < M` at which the strings `u` and `v` differ. -/
def diffSet (M : ℕ) (u v : BitString) : Finset ℕ :=
  (range M).filter (fun i => u[i]! ≠ v[i]!)

/-- For strings of length `M`, the Hamming distance is the size of `diffSet`. -/
theorem hammingDist_eq_card_diffSet {M : ℕ} {u v : BitString} (hu : u.length = M)
    (hv : v.length = M) : hammingDist u v = (diffSet M u v).card :=
  hammingDist_eq_filter_card M u v hu hv

/-- Membership in a Hamming sphere through `diffSet`. -/
theorem mem_hammingSphere_iff_diffSet {M s : ℕ} {u v : BitString} (hu : u.length = M) :
    v ∈ hammingSphere M u s ↔ v.length = M ∧ (diffSet M u v).card = s := by
  rw [hammingSphere, mem_filter, mem_stringsOfLength]
  constructor
  · rintro ⟨hv, hd⟩
    exact ⟨hv, (hammingDist_eq_card_diffSet hu hv).symm.trans hd⟩
  · rintro ⟨hv, hd⟩
    exact ⟨hv, (hammingDist_eq_card_diffSet hu hv).trans hd⟩

/-- **Difference sets compose by symmetric difference**: `v` and `w` differ exactly where one,
but not both, of them differs from `u`.

Proof sketch: `ext i`; unfold `diffSet`, `mem_filter`, `mem_symmDiff`; for `i < M` do a case
split on the three Boolean values `u[i]!`, `v[i]!`, `w[i]!` (`cases … <;> simp`).
Reference: tex 1287-1293 (proof of `lem:ham-collision`); node L06.  [leaf: easy] -/
theorem diffSet_symmDiff (M : ℕ) (u v w : BitString) :
    diffSet M v w = symmDiff (diffSet M u v) (diffSet M u w) := by
  ext i
  simp only [diffSet, mem_filter, mem_range, mem_symmDiff]
  generalize u[i]! = a
  generalize v[i]! = b
  generalize w[i]! = c
  cases a <;> cases b <;> cases c <;> simp

/-- Reading the flip of `u` along `D` at a position `n < M`. -/
private theorem card_filter_diffSet_aux_get (M : ℕ) (u : BitString) (D : Finset ℕ) {n : ℕ}
    (hn : n < M) :
    (List.ofFn (fun i : Fin M => if (i : ℕ) ∈ D then !u[(i : ℕ)]! else u[(i : ℕ)]!))[n]! =
      if n ∈ D then !u[n]! else u[n]! := by
  rw [getElem!_pos _ n (by simpa using hn), List.getElem_ofFn]

/-- The flip-set bijection count; the length of `u` plays no role. -/
private theorem card_filter_diffSet_aux (M : ℕ) (u : BitString) (P : Finset ℕ → Prop)
    [DecidablePred P] :
    ((stringsOfLength M).filter (fun v => P (diffSet M u v))).card =
      ((range M).powerset.filter P).card := by
  have hinv : ∀ D ⊆ range M, diffSet M u (List.ofFn (fun i : Fin M =>
      if (i : ℕ) ∈ D then !u[(i : ℕ)]! else u[(i : ℕ)]!)) = D := by
    intro D hD
    ext n
    rw [diffSet, mem_filter, mem_range]
    by_cases hn : n < M
    · rw [card_filter_diffSet_aux_get M u D hn]
      by_cases hnD : n ∈ D <;> simp [hn, hnD]
    · exact iff_of_false (fun h => hn h.1) (fun h => hn (mem_range.1 (hD h)))
  refine card_bij' (fun v _ => diffSet M u v) (fun D _ => List.ofFn (fun i : Fin M =>
      if (i : ℕ) ∈ D then !u[(i : ℕ)]! else u[(i : ℕ)]!)) ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_filter] at hv ⊢
    exact ⟨mem_powerset.2 (filter_subset _ _), hv.2⟩
  · intro D hD
    rw [mem_filter, mem_powerset] at hD
    rw [mem_filter, mem_stringsOfLength, hinv D hD.1]
    exact ⟨by simp, hD.2⟩
  · intro v hv
    rw [mem_filter, mem_stringsOfLength] at hv
    apply List.ext_getElem (by simp [hv.1])
    intro n h1 h2
    have hnM : n < M := by simpa using h1
    rw [List.getElem_ofFn, ← getElem!_pos v n h2]
    simp only [diffSet, mem_filter, mem_range]
    generalize u[n]! = a
    generalize v[n]! = b
    cases a <;> cases b <;> simp [hnM]
  · intro D hD
    rw [mem_filter, mem_powerset] at hD
    exact hinv D hD.1

/-- **Flip-set bijection.**  For `u` of length `M`, `v ↦ diffSet M u v` is a bijection from the
strings of length `M` onto the subsets of `range M`; so counting strings by a property of their
flip set is counting subsets.

Proof sketch: `Finset.card_bij'` (or `card_nbij'`) with the inverse
`D ↦ List.ofFn (fun i : Fin M => if (i : ℕ) ∈ D then !u[i]! else u[i]!)`; both round trips are
pointwise Boolean identities (`List.ext_getElem`, `Bool.not_not`).
Reference: tex 4471-4472 ("explicit bijection choosing flipped coordinates"); node L06.
[leaf: medium] -/
theorem card_filter_diffSet (M : ℕ) (u : BitString) (hu : u.length = M)
    (P : Finset ℕ → Prop) [DecidablePred P] :
    ((stringsOfLength M).filter (fun v => P (diffSet M u v))).card =
      ((range M).powerset.filter P).card := by
  subst hu
  exact card_filter_diffSet_aux _ u P

/-- **Sphere symmetry**: `u ∈ S_z ↔ z ∈ S_u` for strings of length `M`. -/
theorem mem_hammingSphere_comm {M R : ℕ} {u z : BitString} (hu : u.length = M)
    (hz : z.length = M) : u ∈ hammingSphere M z R ↔ z ∈ hammingSphere M u R := by
  rw [hammingSphere, hammingSphere, mem_filter, mem_filter, mem_stringsOfLength,
    mem_stringsOfLength, hammingDist_comm]
  exact ⟨fun h => ⟨hz, h.2⟩, fun h => ⟨hu, h.2⟩⟩

/-- A union of a subset of `A` and a subset of `X \ A` splits back along `A`. -/
private theorem card_powerset_filter_inter_sdiff_aux {X A D₁ D₂ : Finset ℕ} (h1 : D₁ ⊆ A)
    (h2 : D₂ ⊆ X \ A) : (D₁ ∪ D₂) ∩ A = D₁ ∧ (D₁ ∪ D₂) \ A = D₂ := by
  constructor
  · ext x
    have hx1 := @h1 x
    have hx2 := @h2 x
    simp only [mem_inter, mem_union, mem_sdiff] at hx1 hx2 ⊢
    tauto
  · ext x
    have hx1 := @h1 x
    have hx2 := @h2 x
    simp only [mem_union, mem_sdiff] at hx1 hx2 ⊢
    tauto

/-- **Counting by the two halves.**  For `A ⊆ X`, the subsets `D ⊆ X` with `|D ∩ A| = k` and
`|D \ A| = l` number `(|A| choose k) ((|X| - |A|) choose l)`.

Proof sketch: `D ↦ (D ∩ A, D \ A)` is a bijection onto
`A.powersetCard k ×ˢ (X \ A).powersetCard l` (inverse `(D₁, D₂) ↦ D₁ ∪ D₂`); use
`card_product`, `card_powersetCard` and `card_sdiff` (`|X \ A| = |X| - |A|`).
Reference: tex 4471-4472; node L06.  [leaf: medium] -/
theorem card_powerset_filter_inter_sdiff (X A : Finset ℕ) (hA : A ⊆ X) (k l : ℕ) :
    (X.powerset.filter (fun D => (D ∩ A).card = k ∧ (D \ A).card = l)).card =
      A.card.choose k * (X.card - A.card).choose l := by
  rw [← card_sdiff_of_subset hA, ← card_powersetCard, ← card_powersetCard, ← card_product]
  refine card_bij' (fun D _ => (D ∩ A, D \ A)) (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · intro D hD
    rw [mem_filter, mem_powerset] at hD
    rw [mem_product, mem_powersetCard, mem_powersetCard]
    exact ⟨⟨inter_subset_right, hD.2.1⟩, ⟨sdiff_subset_sdiff hD.1 subset_rfl, hD.2.2⟩⟩
  · rintro ⟨D₁, D₂⟩ hp
    rw [mem_product, mem_powersetCard, mem_powersetCard] at hp
    obtain ⟨⟨h1, hk⟩, ⟨h2, hl⟩⟩ := hp
    obtain ⟨hi, hs⟩ := card_powerset_filter_inter_sdiff_aux h1 h2
    rw [mem_filter, mem_powerset, hi, hs]
    exact ⟨union_subset (h1.trans hA) (h2.trans sdiff_subset), hk, hl⟩
  · intro D _
    rw [union_comm]
    exact sdiff_union_inter D A
  · rintro ⟨D₁, D₂⟩ hp
    rw [mem_product, mem_powersetCard, mem_powersetCard] at hp
    obtain ⟨hi, hs⟩ := card_powerset_filter_inter_sdiff_aux hp.1.1 hp.2.1
    rw [hi, hs]

/-- **Distance-`2k` neighbours inside a sphere, as a filter on flip sets.**  Let `u ∈ S_z` and
`A = diffSet M u z` (so `|A| = R`).  A string `v ∈ S_z` is at distance `2k` from `u` exactly
when its flip set `D = diffSet M u v` flips `k` coordinates inside `A` and `k` outside.

Proof sketch: `ext v`; unfold `hammingSphere`, `mem_filter`, `mem_stringsOfLength`.  For `v` of
length `M`, by `diffSet_symmDiff` (base `u`), `diffSet M z v = A Δ D`, and
`|A Δ D| + 2 |A ∩ D| = |A| + |D|` (`card_symmDiff_add_card_inter`-type counting:
`card_sdiff_add_card_inter`); with `hammingDist_eq_card_diffSet` the condition
`|A Δ D| = R ∧ |D| = 2k` is equivalent to `|D ∩ A| = k ∧ |D \ A| = k`
(`card_sdiff_add_card_inter`, `inter_comm`, `omega`).
Reference: tex 4469-4472 (exact internal degree `D_i`); node L06.  [leaf: medium] -/
theorem sphere_filter_dist_eq_filter_diffSet (M R k : ℕ) (z u : BitString) (hz : z.length = M)
    (hu : u ∈ hammingSphere M z R) :
    (hammingSphere M z R).filter (fun v => hammingDist u v = 2 * k) =
      (stringsOfLength M).filter (fun v =>
        (diffSet M u v ∩ diffSet M u z).card = k ∧ (diffSet M u v \ diffSet M u z).card = k) := by
  obtain ⟨hu1, hu2⟩ := (mem_hammingSphere_iff_diffSet hz).1 hu
  have hA : (diffSet M u z).card = R := by
    rw [← hammingDist_eq_card_diffSet hu1 hz, hammingDist_comm,
      hammingDist_eq_card_diffSet hz hu1, hu2]
  have key : ∀ v : BitString, v.length = M →
      ((diffSet M z v).card = R ∧ hammingDist u v = 2 * k ↔
        (diffSet M u v ∩ diffSet M u z).card = k ∧
          (diffSet M u v \ diffSet M u z).card = k) := by
    intro v hv
    rw [hammingDist_eq_card_diffSet hu1 hv, diffSet_symmDiff M u z v, Finset.symmDiff_def,
      card_union_of_disjoint disjoint_sdiff_sdiff]
    have h1 := card_sdiff_add_card_inter (diffSet M u z) (diffSet M u v)
    have h2 := card_sdiff_add_card_inter (diffSet M u v) (diffSet M u z)
    rw [inter_comm] at h1
    omega
  ext v
  rw [mem_filter, mem_filter, mem_hammingSphere_iff_diffSet hz, mem_stringsOfLength, and_assoc]
  exact and_congr_right (key v)

/-- **Distance-`2k` neighbours inside a sphere, counted by flip sets**: with
`A = diffSet M u z`, they correspond to the subsets `D ⊆ range M` with
`|D ∩ A| = k = |D \ A|` (`sphere_filter_dist_eq_filter_diffSet` and the flip-set bijection
`card_filter_diffSet`). -/
theorem card_sphere_filter_dist_eq (M R k : ℕ) (z u : BitString) (hz : z.length = M)
    (hu : u ∈ hammingSphere M z R) :
    ((hammingSphere M z R).filter (fun v => hammingDist u v = 2 * k)).card =
      ((range M).powerset.filter
        (fun D => (D ∩ diffSet M u z).card = k ∧ (D \ diffSet M u z).card = k)).card := by
  rw [sphere_filter_dist_eq_filter_diffSet M R k z u hz hu]
  exact card_filter_diffSet M u ((mem_hammingSphere_iff_diffSet hz).1 hu).1
    (fun D => (D ∩ diffSet M u z).card = k ∧ (D \ diffSet M u z).card = k)

/-- **Exact distance-`2k` regularity of a sphere**: every point of `S_z` has exactly
`(R choose k) ((M - R) choose k)` neighbours at distance `2k` inside `S_z` (for `k = r` this is
the internal degree `D_i`). -/
theorem sphere_distance_regular (M R k : ℕ) (z u : BitString) (hz : z.length = M)
    (hu : u ∈ hammingSphere M z R) :
    ((hammingSphere M z R).filter (fun v => hammingDist u v = 2 * k)).card =
      R.choose k * (M - R).choose k := by
  have hu' := (mem_hammingSphere_iff_diffSet hz).1 hu
  have hA : (diffSet M u z).card = R := by
    rw [← hammingDist_eq_card_diffSet hu'.1 hz, hammingDist_comm,
      hammingDist_eq_card_diffSet hz hu'.1, hu'.2]
  rw [card_sphere_filter_dist_eq M R k z u hz hu,
    card_powerset_filter_inter_sdiff (range M) (diffSet M u z) (filter_subset _ _) k k, hA,
    card_range]

/-- **Sphere incidence** (blueprint node L06).  For a center `z` of length `M`:
the cube has `2^M` points; `|S_z| = (M choose R)`, positive for `R ≤ M`; `u ∈ S_z ↔ z ∈ S_u`;
every point of `S_z` has exactly `(R choose k) ((M - R) choose k)` neighbours at distance `2k`
in `S_z` (the internal degree `D_i` at `k = r`); and the ambient star of radius `j` (`D_a` at
`j = 2r`) has `(M choose j)` points. -/
theorem sphereIncidence (M R : ℕ) (z : BitString) (hz : z.length = M) :
    (stringsOfLength M).card = 2 ^ M ∧
      (hammingSphere M z R).card = M.choose R ∧
      (R ≤ M → 0 < (hammingSphere M z R).card) ∧
      (∀ u : BitString, u.length = M →
        (u ∈ hammingSphere M z R ↔ z ∈ hammingSphere M u R)) ∧
      (∀ u ∈ hammingSphere M z R, ∀ k : ℕ,
        ((hammingSphere M z R).filter (fun v => hammingDist u v = 2 * k)).card =
          R.choose k * (M - R).choose k) ∧
      (∀ j : ℕ, (hammingSphere M z j).card = M.choose j) := by
  refine ⟨card_stringsOfLength M, hammingSphere_card M z R hz, fun h => ?_,
    fun u hu => mem_hammingSphere_comm hu hz,
    fun u hu k => sphere_distance_regular M R k z u hz hu, fun j => hammingSphere_card M z j hz⟩
  rw [hammingSphere_card M z R hz]
  exact Nat.choose_pos h

end Kolmogorov.StrongMerging.Lower
