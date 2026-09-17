import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayWitness

/-!
# Refining the fine scale of the gray area

The gray mass `familyGrayMass epsDepth deltaDepth n T A sm` counts the cells of
length `deltaDepth` that sit under the allocated set and avoid the unavailable
set, each weighted by `2 ^ (-deltaDepth)`. Moving the fine scale `deltaDepth`
*down* (i.e. making the cells smaller) can only increase that mass: every gray
cell at depth `d` splits into its `2 ^ (d' - d)` extensions at depth `d'`, and
each of them is again gray, because a cell comparable with the unavailable set
has a prefix comparable with it.

That is the content of `card_newGrayCells_mono_deltaDepth` and its mass forms.
It is the third structural monotonicity of `GrayFamilyGameSpec`, next to the
monotonicity in the height (`grayFamilyGameSpec_mono_height`) and in the
branching factor (`grayFamilyGameSpec_mono_branching`): a strategy that wins at
fine scale `deltaDepth` still wins at any finer scale, which is what lets a
construction with a good depth loss be weakened to the loss the ladder
recurrence of SUV p. 143 prescribes.
-/

namespace Kolmogorov

/-- All extensions of a cell `p` to length `d`. -/
private def refineCells (d : ℕ) (p : BitString) : Finset BitString :=
  (stringsOfLength (d - p.length)).image (fun w => p ++ w)

private lemma card_refineCells (d : ℕ) (p : BitString) :
    (refineCells d p).card = 2 ^ (d - p.length) := by
  classical
  rw [refineCells, Finset.card_image_of_injective _ (fun w v h => by
    simpa using List.append_cancel_left h), card_stringsOfLength]

private lemma mem_refineCells {d : ℕ} {p q : BitString} (hq : q ∈ refineCells d p) :
    p <+: q ∧ (p.length ≤ d → q.length = d) := by
  classical
  rw [refineCells, Finset.mem_image] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  refine ⟨List.prefix_append _ _, fun hle => ?_⟩
  have hwlen : w.length = d - p.length := (mem_stringsOfLength _ _).mp hw
  simp [hwlen]
  omega

/-- **Refining the fine scale multiplies the gray cell count.** Each gray cell
at depth `deltaDepth` has all of its `2 ^ (deltaDepth' - deltaDepth)` extensions
gray at depth `deltaDepth'`. -/
theorem card_newGrayCells_mono_deltaDepth {eps d d' : ℕ} (hed : eps ≤ d) (hdd : d ≤ d')
    (S U : Finset BitString) :
    (newGrayCells eps d S U).card * 2 ^ (d' - d) ≤ (newGrayCells eps d' S U).card := by
  classical
  set N := newGrayCells eps d S U with hN
  set G : Finset BitString := N.biUnion (fun p => refineCells d' p) with hG
  have hlen : ∀ p ∈ N, p.length = d := fun p hp => (mem_newGrayCells_iff.mp hp).1
  have hdisj : (N : Set BitString).PairwiseDisjoint (fun p => refineCells d' p) := by
    intro p hp p' hp' hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro q hq hq'
    have h1 := (mem_refineCells hq).1
    have h2 := (mem_refineCells hq').1
    have hlenp : p.length = p'.length := by
      rw [hlen p (Finset.mem_coe.mp hp), hlen p' (Finset.mem_coe.mp hp')]
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hne (h.eq_of_length hlenp)
    · exact hne (h.eq_of_length hlenp.symm).symm
  have hcard : G.card = N.card * 2 ^ (d' - d) := by
    rw [hG, Finset.card_biUnion hdisj]
    have : ∀ p ∈ N, (refineCells d' p).card = 2 ^ (d' - d) := by
      intro p hp
      rw [card_refineCells, hlen p hp]
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  rw [← hcard]
  refine Finset.card_le_card ?_
  intro q hq
  rw [hG, Finset.mem_biUnion] at hq
  obtain ⟨p, hp, hqp⟩ := hq
  obtain ⟨hplen, hptake, hpU⟩ := mem_newGrayCells_iff.mp hp
  have hpq : p <+: q := (mem_refineCells hqp).1
  have hqlen : q.length = d' := (mem_refineCells hqp).2 (by omega)
  refine mem_newGrayCells_iff.mpr ⟨hqlen, ?_, ?_⟩
  · have htake : q.take eps = p.take eps := by
      obtain ⟨w, rfl⟩ := hpq
      rw [List.take_append_of_le_length (by omega)]
    rw [htake]
    exact hptake
  · intro hmem
    obtain ⟨-, u, hu, hcomp⟩ := mem_neighborhoodCells_iff_prefixComparable.mp hmem
    refine hpU (mem_neighborhoodCells_iff_prefixComparable.mpr ⟨hplen, u, hu, ?_⟩)
    rcases hcomp with hcomp | hcomp
    · exact Or.inl (hpq.trans hcomp)
    · exact (List.prefix_or_prefix_of_prefix hcomp hpq).symm

/-- Mass form of the refinement bound: the gray mass does not decrease when the
fine scale gets finer. -/
theorem grayMass_mono_deltaDepth {eps d d' : ℕ} (hed : eps ≤ d) (hdd : d ≤ d')
    (S U : Finset BitString) :
    ((newGrayCells eps d S U).card : ℚ) * (1 / 2 : ℚ) ^ d
      ≤ ((newGrayCells eps d' S U).card : ℚ) * (1 / 2 : ℚ) ^ d' := by
  have hcard := card_newGrayCells_mono_deltaDepth hed hdd S U
  have hQ : (((newGrayCells eps d S U).card * 2 ^ (d' - d) : ℕ) : ℚ)
      ≤ ((newGrayCells eps d' S U).card : ℚ) := by exact_mod_cast hcard
  have hpow : ((2 : ℚ) ^ (d' - d)) * (1 / 2 : ℚ) ^ d' = (1 / 2 : ℚ) ^ d :=
    two_pow_sub_mul_half_pow hdd
  calc ((newGrayCells eps d S U).card : ℚ) * (1 / 2 : ℚ) ^ d
      = ((newGrayCells eps d S U).card : ℚ) * ((2 : ℚ) ^ (d' - d)) * (1 / 2 : ℚ) ^ d' := by
        rw [mul_assoc, hpow]
    _ ≤ ((newGrayCells eps d' S U).card : ℚ) * (1 / 2 : ℚ) ^ d' := by
        have hnn : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ d' := by positivity
        refine mul_le_mul_of_nonneg_right ?_ hnn
        have := hQ
        push_cast at this
        linarith

/-- The gray mass of a family play is monotone in the fine scale. -/
theorem familyGrayMass_mono_deltaDepth {eps d d' n T : ℕ} (hed : eps ≤ d) (hdd : d ≤ d')
    (A : Allocation) (sm : ℕ → FamilyServerMove) :
    familyGrayMass eps d n T A sm ≤ familyGrayMass eps d' n T A sm :=
  grayMass_mono_deltaDepth hed hdd _ _

/-- The winning condition of the family game is monotone in the fine scale. -/
theorem familyGrayGoal_mono_deltaDepth {kappa beta : ℚ} {eps d d' n : ℕ}
    (hed : eps ≤ d) (hdd : d ≤ d') {A : Allocation}
    {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (H : familyGrayGoal kappa beta eps d n A cm sm) :
    familyGrayGoal kappa beta eps d' n A cm sm := by
  obtain ⟨T, hbeta, hkappa, hprogress⟩ := H
  have hmass := familyGrayMass_mono_deltaDepth (n := n) (T := T) hed hdd A sm
  exact ⟨T, le_trans hbeta hmass, le_trans hkappa hmass, hprogress⟩

/-- **The family game specification is monotone in the fine scale.** A strategy
that wins with fine scale `deltaDepth` wins with any finer scale: its requests
still avoid the smaller granularity, and its gray mass only grows. -/
theorem grayFamilyGameSpec_mono_deltaDepth {kappa alpha beta : ℚ}
    {epsDepth deltaDepth deltaDepth' h b n : ℕ} (hdd : deltaDepth ≤ deltaDepth')
    {A : Allocation} {σ : ClientFamilyStrategy}
    (H : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A σ) :
    GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth' h b n A σ where
  nonempty := H.nonempty
  kappa_ge_one := H.kappa_ge_one
  alpha_pos := H.alpha_pos
  beta_nonneg := H.beta_nonneg
  scales := le_trans H.scales hdd
  legal := H.legal
  minimum_request := by
    intro sm hsm t i hi x
    have hsmall : (1 / 2 : ℚ) ^ deltaDepth' ≤ (1 / 2 : ℚ) ^ deltaDepth :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hdd
    rcases H.minimum_request sm hsm t i hi x with h0 | hge
    · exact Or.inl h0
    · exact Or.inr (le_trans hsmall hge)
  wins := fun sm hsm => (H.wins sm hsm).imp id
    (fun hgoal => familyGrayGoal_mono_deltaDepth H.scales hdd hgoal)
  wins_positively := fun sm hsm => (H.wins_positively sm hsm).imp id
    (fun hgoal => familyGrayGoal_mono_deltaDepth H.scales hdd hgoal)
  range_supported := H.range_supported
  tree_supported := H.tree_supported

end Kolmogorov
