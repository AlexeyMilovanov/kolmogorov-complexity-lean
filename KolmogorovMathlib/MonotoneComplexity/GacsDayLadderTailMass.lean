import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailTerminal

/-!
# Reserve mass at different stopping times

A reserve need not remain a reserve: later allocations may enter another
subcone of the same coarse cylinder.  What is persistent is the gray cell it
creates.  This file packages the correct temporal argument.  Reserves chosen
at different times are distinct by orienting each pair toward the later time
and using the later reserve's exclusion clause against the earlier anchor.
-/

namespace Kolmogorov

/-- Two strings with a common extension are prefix-comparable: if `R` is comparable with `v`
and `w` is a prefix of `v`, then `R` and `w` are comparable. -/
lemma prefixComparable_of_common_extension
    {R v w : BitString} (hRv : R <+: v ∨ v <+: R) (hwv : w <+: v) :
    R <+: w ∨ w <+: R := by
  rcases hRv with hRv | hvR
  · exact List.prefix_or_prefix_of_prefix hRv hwv
  · exact Or.inr (hwv.trans hvR)

/-- Source-faithful reserves acquired at son-dependent times contribute their
full coarse mass at every common later time.  No persistence assumption on the
reserve predicate is made. -/
theorem familyGrayMass_ge_of_tailFamilyReserves_at_times
    {epsDepth deltaDepth n T b : Nat} (hed : epsDepth <= deltaDepth)
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hleg : familyServerPlayLegal n b A sm)
    {ι : Type*} [Fintype ι]
    (time : ι -> Nat) (tree : ι -> Nat)
    (x : ι -> GacsDayNode) (R : ι -> BitString)
    (htime : forall j, time j <= T)
    (htree : forall j, tree j < n)
    (hnodes : forall j d, d ∈ x j -> d < b)
    (hdistinct : forall j l, j ≠ l ->
      tree j ≠ tree l ∨ ¬ (x j <+: x l ∨ x l <+: x j))
    (hres : forall j, IsTailFamilyReserve epsDepth b A n (tree j)
      (sm (time j)) (x j) (R j)) :
    (Fintype.card ι : Rat) * (1 / 2 : Rat) ^ epsDepth <=
      familyGrayMass epsDepth deltaDepth n T A sm := by
  classical
  have hpair : forall (j l : ι), j ≠ l -> time j <= time l ->
      R j ≠ R l := by
    intro j l hjl hjlTime hEq
    obtain ⟨v, hv, hRv⟩ := (hres j).1.2.1
    have hmono := allocationSubset_mono_time
      (hleg.1 (tree j) (htree j)) hjlTime (x j)
    obtain ⟨w, hw, hwv⟩ := hmono v hv
    have hRw : R j <+: w ∨ w <+: R j :=
      prefixComparable_of_common_extension hRv hwv
    by_cases htreeEq : tree j = tree l
    · have hinc : ¬ (x j <+: x l ∨ x l <+: x j) := by
        rcases hdistinct j l hjl with hne | hinc
        · exact (hne htreeEq).elim
        · exact hinc
      have houtside := (hres l).1.2.2.1 (x j) (hnodes j)
        (fun h => hinc h.symm)
      have hw' : w ∈ getAlloc
          (familyServerMoveAt (sm (time l)) (tree l)) (x j) := by
        simpa [htreeEq] using hw
      have hcomp : R l <+: w ∨ w <+: R l := by
        simpa [hEq] using hRw
      exact houtside w hw' hcomp
    · have hcoh := (hleg.1 (tree j) (htree j)).1 (time l)
      obtain ⟨u, hu, huw⟩ :=
        allocationSubset_getAlloc_root hcoh (x j) (hnodes j) w hw
      have hRu : R j <+: u ∨ u <+: R j :=
        prefixComparable_of_common_extension hRw huw
      have hcomp : R l <+: u ∨ u <+: R l := by
        simpa [hEq] using hRu
      exact (hres l).2 (tree j) (htree j) htreeEq u hu hcomp
  have hinj : Function.Injective R := by
    intro j l hEq
    by_contra hjl
    rcases le_total (time j) (time l) with hjlTime | hljTime
    · exact hpair j l hjl hjlTime hEq
    · exact hpair l j (Ne.symm hjl) hljTime hEq.symm
  set P : Finset BitString := Finset.image R Finset.univ with hP
  have hcard : P.card = Fintype.card ι := by
    rw [hP, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hlen : forall p, p ∈ P -> p.length = epsDepth := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hres j).1.1
  have hcovered : forall p, p ∈ P ->
      exists s, s ∈ familyAllocated n T sm ∧ (p <+: s ∨ s <+: p) := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v, hv, hRv⟩ := (hres j).1.2.1
    obtain ⟨s, hs, hsv⟩ := exists_root_prefix_of_family_alloc
      hleg (htree j) (htime j) (hnodes j) hv
    refine ⟨s, ?_, prefixComparable_of_common_extension hRv hsv⟩
    simp only [familyAllocated, Finset.mem_biUnion, Finset.mem_univ,
      List.mem_toFinset, true_and]
    exact ⟨⟨tree j, htree j⟩, hs⟩
  have havoid : forall p, p ∈ P -> forall u, u ∈ A ->
      ¬ (p <+: u ∨ u <+: p) := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hres j).1.2.2.2
  have hmass := familyGrayMass_ge_of_coarse_cells
    (n := n) (T := T) (A := A) (sm := sm)
    hed P hlen hcovered havoid
  rwa [hcard] at hmass

end Kolmogorov
