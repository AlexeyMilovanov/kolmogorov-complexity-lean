import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame

/-!
# Gray-area witnesses at two dyadic scales

The base case of the parallel family induction only needs the gray area at a
single scale (`epsDepth = deltaDepth`) and only for allocated cells that are
coarser than the request scale, which is what
`card_newGrayCells_ge_of_disjoint_witnesses` provides. Every later stage of the
induction of SUV pp. 143-144 runs at two genuinely different scales: server
allocations are rounded up to the coarse scale `epsDepth`, while the gray cells
are counted at the fine scale `deltaDepth`, and the cells that witness the gray
area are the *deep* allocations made below a served root request, not the root
allocation itself.

The main lemma here is `card_newGrayCells_ge_of_incomparable_witnesses`: any
family of pairwise incompatible cells that (i) sit below the allocated set and
(ii) avoid the unavailable set contributes its full mass to the gray area, at
whatever depths those cells happen to live. Since the `Serves` relation of
`GacsDayGame` asks for a *single* cylinder of at least the requested mass, a
request of `q` forces a cell of mass at least `2 ^ (-⌊log₂ (1/q)⌋) ≥ q`: this
lemma is what converts that rounding-up into gray mass.

Also recorded here is the structural monotonicity of `GrayFamilyGameSpec` in the
height, which the half-step of the induction needs when it raises the height
from `2 * k` to `2 * (k + 1)`. Nothing in this file changes a frozen statement.
-/

namespace Kolmogorov

/-- All extensions of a cell `c` to length `deltaDepth`. -/
private def extensionsAt (deltaDepth : ℕ) (c : BitString) : Finset BitString :=
  (stringsOfLength (deltaDepth - c.length)).image (fun w => c ++ w)

private lemma card_extensionsAt (deltaDepth : ℕ) (c : BitString) :
    (extensionsAt deltaDepth c).card = 2 ^ (deltaDepth - c.length) := by
  classical
  rw [extensionsAt, Finset.card_image_of_injective _ (fun w v h => by
    simpa using List.append_cancel_left h), card_stringsOfLength]

private lemma mem_extensionsAt {deltaDepth : ℕ} {c p : BitString}
    (hp : p ∈ extensionsAt deltaDepth c) :
    c <+: p ∧ (c.length ≤ deltaDepth → p.length = deltaDepth) := by
  classical
  rw [extensionsAt, Finset.mem_image] at hp
  obtain ⟨w, hw, rfl⟩ := hp
  refine ⟨List.prefix_append _ _, fun hle => ?_⟩
  have : w.length = deltaDepth - c.length := (mem_stringsOfLength _ _).mp hw
  simp [this]
  omega

/-- **Gray witnesses.** Pairwise incompatible cells that lie below the allocated
set and avoid the unavailable set contribute all of their extensions to the gray
area at depth `deltaDepth`.

This is the engine of the granularity waste of SUV pp. 143-144: the server may
serve a request with a cell of far greater mass than the request, and every such
cell is counted here at its own size, no matter at which depth it lives and no
matter how coarse the intermediate scale `epsDepth` is. -/
lemma card_newGrayCells_ge_of_incomparable_witnesses
    (epsDepth deltaDepth : ℕ) (hed : epsDepth ≤ deltaDepth)
    (S U : Finset BitString) {ι : Type*} [Fintype ι] (c : ι → BitString)
    (hc_len : ∀ i, (c i).length ≤ deltaDepth)
    (hc_anc : ∀ i, ∃ y ∈ S, y <+: c i)
    (hc_disj : ∀ i j, i ≠ j → ¬ ((c i) <+: (c j) ∨ (c j) <+: (c i)))
    (hc_avoid : ∀ i, ∀ u ∈ U, ¬ ((c i) <+: u ∨ u <+: (c i))) :
    ∑ i : ι, 2 ^ (deltaDepth - (c i).length)
      ≤ (newGrayCells epsDepth deltaDepth S U).card := by
  classical
  set G : Finset BitString :=
    (Finset.univ : Finset ι).biUnion (fun i => extensionsAt deltaDepth (c i)) with hG
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i => extensionsAt deltaDepth (c i)) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    have h1 := (mem_extensionsAt hpi).1
    have h2 := (mem_extensionsAt hpj).1
    exact hc_disj i j hij (List.prefix_or_prefix_of_prefix h1 h2)
  have hcard : G.card = ∑ i : ι, 2 ^ (deltaDepth - (c i).length) := by
    rw [hG, Finset.card_biUnion hdisj]
    exact Finset.sum_congr rfl (fun i _ => card_extensionsAt _ _)
  rw [← hcard]
  refine Finset.card_le_card ?_
  intro p hp
  rw [hG, Finset.mem_biUnion] at hp
  obtain ⟨i, -, hpi⟩ := hp
  have hpref : c i <+: p := (mem_extensionsAt hpi).1
  have hlen : p.length = deltaDepth := (mem_extensionsAt hpi).2 (hc_len i)
  refine mem_newGrayCells_iff.mpr ⟨hlen, ?_, ?_⟩
  · obtain ⟨y, hy, hyc⟩ := hc_anc i
    have hyp : y <+: p := hyc.trans hpref
    have htake : p.take epsDepth <+: p := List.take_prefix _ _
    have hlen' : (p.take epsDepth).length = epsDepth := by
      simp [hlen]
      omega
    exact mem_neighborhoodCells_iff_prefixComparable.mpr
      ⟨hlen', y, hy, List.prefix_or_prefix_of_prefix htake hyp⟩
  · intro hmem
    obtain ⟨-, u, hu, hcomp⟩ := mem_neighborhoodCells_iff_prefixComparable.mp hmem
    refine hc_avoid i u hu ?_
    rcases hcomp with hcomp | hcomp
    · exact Or.inl (hpref.trans hcomp)
    · exact List.prefix_or_prefix_of_prefix hpref hcomp

/-- The dyadic bookkeeping behind the mass form of the witness bounds. -/
lemma two_pow_sub_mul_half_pow {a d : ℕ} (h : a ≤ d) :
    ((2 : ℚ) ^ (d - a)) * (1 / 2 : ℚ) ^ d = (1 / 2 : ℚ) ^ a := by
  obtain ⟨k, rfl⟩ : ∃ k, d = a + k := ⟨d - a, by omega⟩
  have hk : a + k - a = k := by omega
  rw [hk, pow_add, div_pow, div_pow, one_pow, one_pow]
  field_simp

/-- Mass form of the witness bound: the gray area weighs at least the total mass
of the witnessing cells. -/
lemma grayMass_ge_of_incomparable_witnesses
    (epsDepth deltaDepth : ℕ) (hed : epsDepth ≤ deltaDepth)
    (S U : Finset BitString) {ι : Type*} [Fintype ι] (c : ι → BitString)
    (hc_len : ∀ i, (c i).length ≤ deltaDepth)
    (hc_anc : ∀ i, ∃ y ∈ S, y <+: c i)
    (hc_disj : ∀ i j, i ≠ j → ¬ ((c i) <+: (c j) ∨ (c j) <+: (c i)))
    (hc_avoid : ∀ i, ∀ u ∈ U, ¬ ((c i) <+: u ∨ u <+: (c i))) :
    ∑ i : ι, (1 / 2 : ℚ) ^ (c i).length ≤
      ((newGrayCells epsDepth deltaDepth S U).card : ℚ) * (1 / 2 : ℚ) ^ deltaDepth := by
  have hcard := card_newGrayCells_ge_of_incomparable_witnesses epsDepth deltaDepth hed
    S U c hc_len hc_anc hc_disj hc_avoid
  have hcQ : ((∑ i : ι, 2 ^ (deltaDepth - (c i).length) : ℕ) : ℚ) ≤
      ((newGrayCells epsDepth deltaDepth S U).card : ℚ) := by exact_mod_cast hcard
  have hstep : ∑ i : ι, (1 / 2 : ℚ) ^ (c i).length
      = ((∑ i : ι, 2 ^ (deltaDepth - (c i).length) : ℕ) : ℚ) * (1 / 2 : ℚ) ^ deltaDepth := by
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => (two_pow_sub_mul_half_pow (hc_len i)).symm)
  rw [hstep]
  gcongr

/-- Two-scale form of the base-case witness bound.

If `n` pairwise incompatible allocated cylinders of length at most `a` avoid the
unavailable set, then at the fine scale `deltaDepth` they contribute at least
`n * 2 ^ (deltaDepth - a)` new gray cells, for any intermediate coarse scale
`a ≤ epsDepth ≤ deltaDepth`. This generalises
`card_newGrayCells_ge_of_disjoint_witnesses`, which is the case
`a ≤ epsDepth = deltaDepth`. -/
lemma card_newGrayCells_ge_of_disjoint_witnesses_scales
    (a epsDepth deltaDepth : ℕ) (hae : a ≤ epsDepth) (hed : epsDepth ≤ deltaDepth)
    (S U : Finset BitString) (n : ℕ) (c : Fin n → BitString)
    (hc_len : ∀ i, (c i).length ≤ a)
    (hc_mem : ∀ i, c i ∈ S)
    (hc_disj : ∀ i j, i ≠ j → ¬ ((c i) <+: (c j) ∨ (c j) <+: (c i)))
    (hc_avoid : ∀ i, ∀ u ∈ U, ¬ ((c i) <+: u ∨ u <+: (c i))) :
    n * 2 ^ (deltaDepth - a) ≤ (newGrayCells epsDepth deltaDepth S U).card := by
  have had : a ≤ deltaDepth := le_trans hae hed
  refine le_trans ?_ (card_newGrayCells_ge_of_incomparable_witnesses epsDepth deltaDepth hed
    S U c (fun i => le_trans (hc_len i) had) (fun i => ⟨c i, hc_mem i, List.prefix_rfl⟩)
    hc_disj hc_avoid)
  have hterm : ∀ i : Fin n, 2 ^ (deltaDepth - a) ≤ 2 ^ (deltaDepth - (c i).length) := by
    intro i
    exact Nat.pow_le_pow_right (by norm_num) (by have := hc_len i; omega)
  calc n * 2 ^ (deltaDepth - a)
      = ∑ _i : Fin n, 2 ^ (deltaDepth - a) := by simp
    _ ≤ ∑ i : Fin n, 2 ^ (deltaDepth - (c i).length) :=
        Finset.sum_le_sum (fun i _ => hterm i)

/-- Mass form of the two-scale witness bound: `n` pairwise incompatible allocated
cells of length at most `a` carry gray mass at least `n * 2 ^ (-a)`. -/
lemma grayMass_ge_of_disjoint_witnesses_scales
    (a epsDepth deltaDepth : ℕ) (hae : a ≤ epsDepth) (hed : epsDepth ≤ deltaDepth)
    (S U : Finset BitString) (n : ℕ) (c : Fin n → BitString)
    (hc_len : ∀ i, (c i).length ≤ a)
    (hc_mem : ∀ i, c i ∈ S)
    (hc_disj : ∀ i j, i ≠ j → ¬ ((c i) <+: (c j) ∨ (c j) <+: (c i)))
    (hc_avoid : ∀ i, ∀ u ∈ U, ¬ ((c i) <+: u ∨ u <+: (c i))) :
    (n : ℚ) * (1 / 2 : ℚ) ^ a ≤
      ((newGrayCells epsDepth deltaDepth S U).card : ℚ) * (1 / 2 : ℚ) ^ deltaDepth := by
  have hcard := card_newGrayCells_ge_of_disjoint_witnesses_scales a epsDepth deltaDepth hae hed
    S U n c hc_len hc_mem hc_disj hc_avoid
  have hcQ : ((n * 2 ^ (deltaDepth - a) : ℕ) : ℚ) ≤
      ((newGrayCells epsDepth deltaDepth S U).card : ℚ) := by exact_mod_cast hcard
  have hstep : (n : ℚ) * (1 / 2 : ℚ) ^ a
      = ((n * 2 ^ (deltaDepth - a) : ℕ) : ℚ) * (1 / 2 : ℚ) ^ deltaDepth := by
    push_cast
    rw [mul_assoc, two_pow_sub_mul_half_pow (le_trans hae hed)]
  rw [hstep]
  gcongr

/-- Granularity waste at the coarse scale.

Every cell `p` of length `epsDepth` that meets the allocated set and misses the
unavailable set contributes *all* of its `2 ^ (deltaDepth - epsDepth)`
extensions to the gray area, however little mass the server actually allocated
inside `p`. Unlike the witness bounds above, the allocated cell here may be an
arbitrary extension of `p`: allocations finer than the coarse scale are rounded
up to whole `epsDepth`-cells. -/
lemma card_newGrayCells_ge_of_coarse_cells
    (epsDepth deltaDepth : ℕ) (hed : epsDepth ≤ deltaDepth)
    (S U P : Finset BitString)
    (hP_len : ∀ p ∈ P, p.length = epsDepth)
    (hP_nb : ∀ p ∈ P, ∃ s ∈ S, p <+: s ∨ s <+: p)
    (hP_avoid : ∀ p ∈ P, ∀ u ∈ U, ¬ (p <+: u ∨ u <+: p)) :
    P.card * 2 ^ (deltaDepth - epsDepth) ≤ (newGrayCells epsDepth deltaDepth S U).card := by
  classical
  have hcard : (P ×ˢ (stringsOfLength (deltaDepth - epsDepth))).card
      = P.card * 2 ^ (deltaDepth - epsDepth) := by
    rw [Finset.card_product, card_stringsOfLength]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun q => q.1 ++ q.2) ?_ ?_
  · rintro ⟨p, w⟩ hq
    obtain ⟨hp, hw⟩ := Finset.mem_product.mp hq
    have hplen := hP_len p hp
    have hwlen : w.length = deltaDepth - epsDepth := (mem_stringsOfLength _ _).mp hw
    have hlen : (p ++ w).length = deltaDepth := by
      simp [hplen, hwlen]
      omega
    have htake : (p ++ w).take epsDepth = p := by
      rw [← hplen, List.take_left]
    refine mem_newGrayCells_iff.mpr ⟨hlen, ?_, ?_⟩
    · rw [htake]
      obtain ⟨s, hs, hcomp⟩ := hP_nb p hp
      exact mem_neighborhoodCells_iff_prefixComparable.mpr ⟨hplen, s, hs, hcomp⟩
    · intro hmem
      obtain ⟨-, u, hu, hcomp⟩ := mem_neighborhoodCells_iff_prefixComparable.mp hmem
      have hpw : p <+: p ++ w := List.prefix_append _ _
      refine hP_avoid p hp u hu ?_
      rcases hcomp with hcomp | hcomp
      · exact Or.inl (hpw.trans hcomp)
      · exact List.prefix_or_prefix_of_prefix hpw hcomp
  · rintro ⟨p, w⟩ hq ⟨p', w'⟩ hq' hEq
    obtain ⟨hp, -⟩ := Finset.mem_product.mp hq
    obtain ⟨hp', -⟩ := Finset.mem_product.mp hq'
    have hlen : p.length = p'.length := by rw [hP_len p hp, hP_len p' hp']
    obtain ⟨h1, h2⟩ := List.append_inj hEq hlen
    exact Prod.ext h1 h2

/-- Mass form of the granularity waste: every coarse cell touched by the server
carries a full `2 ^ (-epsDepth)` of gray mass. -/
lemma grayMass_ge_of_coarse_cells
    (epsDepth deltaDepth : ℕ) (hed : epsDepth ≤ deltaDepth)
    (S U P : Finset BitString)
    (hP_len : ∀ p ∈ P, p.length = epsDepth)
    (hP_nb : ∀ p ∈ P, ∃ s ∈ S, p <+: s ∨ s <+: p)
    (hP_avoid : ∀ p ∈ P, ∀ u ∈ U, ¬ (p <+: u ∨ u <+: p)) :
    (P.card : ℚ) * (1 / 2 : ℚ) ^ epsDepth ≤
      ((newGrayCells epsDepth deltaDepth S U).card : ℚ) * (1 / 2 : ℚ) ^ deltaDepth := by
  have hcard := card_newGrayCells_ge_of_coarse_cells epsDepth deltaDepth hed S U P
    hP_len hP_nb hP_avoid
  have hcQ : ((P.card * 2 ^ (deltaDepth - epsDepth) : ℕ) : ℚ) ≤
      ((newGrayCells epsDepth deltaDepth S U).card : ℚ) := by exact_mod_cast hcard
  have hstep : (P.card : ℚ) * (1 / 2 : ℚ) ^ epsDepth
      = ((P.card * 2 ^ (deltaDepth - epsDepth) : ℕ) : ℚ) * (1 / 2 : ℚ) ^ deltaDepth := by
    push_cast
    rw [mul_assoc, two_pow_sub_mul_half_pow hed]
  rw [hstep]
  gcongr

/-- Gray mass of a family play, bounded below by the total mass of pairwise
incompatible cells sitting below the root allocations and avoiding the
unavailable set. -/
lemma familyGrayMass_ge_of_incomparable_witnesses
    {epsDepth deltaDepth n T : ℕ} (hed : epsDepth ≤ deltaDepth)
    {A : Allocation} {sm : ℕ → FamilyServerMove} {ι : Type*} [Fintype ι] (c : ι → BitString)
    (hc_len : ∀ i, (c i).length ≤ deltaDepth)
    (hc_anc : ∀ i, ∃ y ∈ familyAllocated n T sm, y <+: c i)
    (hc_disj : ∀ i j, i ≠ j → ¬ ((c i) <+: (c j) ∨ (c j) <+: (c i)))
    (hc_avoid : ∀ i, ∀ u ∈ A, ¬ ((c i) <+: u ∨ u <+: (c i))) :
    ∑ i : ι, (1 / 2 : ℚ) ^ (c i).length ≤
      familyGrayMass epsDepth deltaDepth n T A sm :=
  grayMass_ge_of_incomparable_witnesses epsDepth deltaDepth hed _ _ c hc_len hc_anc hc_disj
    (fun i u hu => hc_avoid i u (List.mem_toFinset.mp hu))

/-- Gray mass of a family play, bounded below by the coarse cells it touches. -/
lemma familyGrayMass_ge_of_coarse_cells
    {epsDepth deltaDepth n T : ℕ} (hed : epsDepth ≤ deltaDepth)
    {A : Allocation} {sm : ℕ → FamilyServerMove} (P : Finset BitString)
    (hP_len : ∀ p ∈ P, p.length = epsDepth)
    (hP_nb : ∀ p ∈ P, ∃ s ∈ familyAllocated n T sm, p <+: s ∨ s <+: p)
    (hP_avoid : ∀ p ∈ P, ∀ u ∈ A, ¬ (p <+: u ∨ u <+: p)) :
    (P.card : ℚ) * (1 / 2 : ℚ) ^ epsDepth ≤
      familyGrayMass epsDepth deltaDepth n T A sm :=
  grayMass_ge_of_coarse_cells epsDepth deltaDepth hed _ _ P hP_len hP_nb
    (fun p hp u hu => hP_avoid p hp u (List.mem_toFinset.mp hu))

/-!
## Structural monotonicity of the family specification in the height

The induction of SUV pp. 143-144 raises the height from `2 * k` to `2 * k + 2`
at every half-step, so the two height-dependent fields of `GrayFamilyGameSpec`
have to be transported upwards.
-/

/-- A strategy supported on the first `h` levels is supported on the first `h'`
levels for any `h ≤ h'`. -/
theorem familyTreeSupported_mono_height {n h h' : ℕ} (hh : h ≤ h')
    {A : Allocation} {σ : ClientFamilyStrategy}
    (H : FamilyTreeSupported n h A σ) : FamilyTreeSupported n h' A σ := by
  intro hist x hx j hj
  exact H hist x (lt_of_le_of_lt hh hx) j hj

/-- An unserved family win at height `h` is an unserved family win at any larger
height. -/
theorem familyClientWinsUnserved_mono_height {n h h' b : ℕ} (hh : h ≤ h')
    {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (H : familyClientWinsUnserved n h b cm sm) :
    familyClientWinsUnserved n h' b cm sm := by
  obtain ⟨i, hi, hwin⟩ := H
  exact ⟨i, hi, clientWinsUnserved_mono_height hh hwin⟩

/-- Winning with positive unserved mass at height `h` still wins at any larger height. -/
theorem familyClientWinsUnservedPositive_mono_height {n h h' b : ℕ} (hh : h ≤ h')
    {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (H : familyClientWinsUnservedPositive n h b cm sm) :
    familyClientWinsUnservedPositive n h' b cm sm := by
  obtain ⟨i, hi, T, x, hlen, hdig, hfail, hpos⟩ := H
  exact ⟨i, hi, T, x, le_trans hlen hh, hdig, hfail, hpos⟩

/-- The family game specification is monotone in the height. -/
theorem grayFamilyGameSpec_mono_height {kappa alpha beta : ℚ}
    {epsDepth deltaDepth h h' b n : ℕ} (hh : h ≤ h')
    {A : Allocation} {σ : ClientFamilyStrategy}
    (H : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A σ) :
    GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h' b n A σ where
  nonempty := H.nonempty
  kappa_ge_one := H.kappa_ge_one
  alpha_pos := H.alpha_pos
  beta_nonneg := H.beta_nonneg
  scales := H.scales
  legal := H.legal
  minimum_request := H.minimum_request
  wins := fun sm hsm => (H.wins sm hsm).imp
    (fun hw => familyClientWinsUnserved_mono_height hh hw) id
  wins_positively := fun sm hsm => (H.wins_positively sm hsm).imp
    (fun hw => familyClientWinsUnservedPositive_mono_height hh hw) id
  range_supported := H.range_supported
  tree_supported := familyTreeSupported_mono_height hh H.tree_supported

end Kolmogorov
