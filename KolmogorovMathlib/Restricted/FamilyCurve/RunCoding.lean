import KolmogorovMathlib.Restricted.FamilyCurve.CoupledRun

namespace Kolmogorov

/-- Concrete charging bridge for one sampled scale.  Large rebuilds are
charged to distinct restricted descriptions and small rebuilds to fresh
deleted volume; the already-proved description-count bounds then reduce the
version estimate to one explicit arithmetic budget. -/
lemma restrictedSampledRun_rebuild_count_le
    (𝒜 : DescriptionFamily) (U : Map)
    (n c i j t_s threshold rebuilds_large rebuilds_small : ℕ)
    (hthreshold : 0 < threshold)
    (h_large :
      rebuilds_large ≤ (restrictedBadDescriptions 𝒜 U i j).card)
    (h_small :
      rebuilds_small * threshold ≤
        ((restrictedBadDescriptions 𝒜 U i j).biUnion id).card)
    (h_budget :
      2 ^ (i + 1) + (2 ^ (i + 1) * 2 ^ j) / threshold + 1 ≤
        2 ^ (t_s + sqrtSlack c n)) :
    rebuilds_large + rebuilds_small + 1 ≤
      2 ^ (t_s + sqrtSlack c n) := by
  apply restrictedSampledRun_versions_le n c t_s
    (restrictedBadDescriptions 𝒜 U i j).card
    ((restrictedBadDescriptions 𝒜 U i j).biUnion id).card
    threshold rebuilds_large rebuilds_small hthreshold h_large h_small
  calc
    (restrictedBadDescriptions 𝒜 U i j).card +
          ((restrictedBadDescriptions 𝒜 U i j).biUnion id).card / threshold + 1
        ≤ 2 ^ (i + 1) +
            (2 ^ (i + 1) * 2 ^ j) / threshold + 1 := by
          gcongr
          · exact restricted_large_bad_appearances_le 𝒜 U i j
          · exact restricted_small_bad_deleted_volume_le 𝒜 U i j
    _ ≤ 2 ^ (t_s + sqrtSlack c n) := h_budget

/-- A version number that fits in `s + Δ` bits has a literal binary code of
prefix complexity `s + Δ + O(log (s + Δ))`.  This is the fixed-length coding
fact needed before composing a version decoder with the encoded grid. -/
lemma restrictedSampledRun_version_code_complexity
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (version s Δ : ℕ),
      version < 2 ^ (s + Δ) →
      KPPlain U (Nat.bits version) ≤
        (s + Δ : ENat) + 2 * (Nat.bits (s + Δ)).length + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_le_length_add_log U hU
  refine ⟨c, ?_⟩
  intro version s Δ hversion
  have hlength : (Nat.bits version).length ≤ s + Δ := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hversion
  calc
    KPPlain U (Nat.bits version)
        ≤ ((Nat.bits version).length : ENat) +
            2 * (Nat.bits (Nat.bits version).length).length + (c : ENat) :=
          hc (Nat.bits version)
    _ ≤ (s + Δ : ENat) + 2 * (Nat.bits (s + Δ)).length + (c : ENat) := by
          gcongr
          · exact_mod_cast hlength
          · exact length_natBits_mono hlength

/-- The root survivor pool of the chronological sampled run is antitone in
time.  Deeper live sets are deliberately not claimed antitone: suffix rebuilds
may replace them. -/
lemma restrictedSampledRun_root_antitone
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (initialState : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (badStream : ℕ → List (Finset BitString))
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i) :
    Antitone (fun time =>
      (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
        badStream hover ht_strict time).live 0) := by
  intro time₁ time₂ htime
  induction htime with
  | refl => exact Finset.Subset.rfl
  | @step time₂ htime ih =>
      have hstep := restrictedSampledRunProcess_live_subset_root 𝒜 N
        ambientLength overheadBound t hover ht_strict
        (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
          badStream hover ht_strict time₂)
        (badStream time₂) 0 (Nat.zero_le N)
      exact hstep.trans ih

/-- The finite root survivor pool eventually stabilizes.  This is the honest
stabilization consequence currently available from the extensional run; it
does not assert computability of the chosen suffix rebuilds or stability of
their individual versions. -/
lemma restrictedSampledRun_stabilizes
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (initialState : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (badStream : ℕ → List (Finset BitString))
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i) :
    ∃ T : ℕ, ∀ time ≥ T,
      (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
        badStream hover ht_strict time).live 0 =
      (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
        badStream hover ht_strict T).live 0 := by
  classical
  let root : ℕ → Finset BitString := fun time =>
    (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
      badStream hover ht_strict time).live 0
  have hexists : ∃ card : ℕ, ∃ time : ℕ, (root time).card = card :=
    ⟨(root 0).card, 0, rfl⟩
  obtain ⟨T, hT⟩ := Nat.find_spec hexists
  refine ⟨T, ?_⟩
  intro time htime
  have hsub : root time ⊆ root T :=
    restrictedSampledRun_root_antitone 𝒜 N ambientLength overheadBound t
      initialState badStream hover ht_strict htime
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hT]
  by_contra hnot
  have hlt : (root time).card < Nat.find hexists := Nat.lt_of_not_ge hnot
  exact (Nat.find_min hexists hlt) ⟨time, rfl⟩

/-- Once a bad event has been processed, every live set at every later time is
disjoint from it. -/
lemma restrictedSampledRun_processed_bad_disjoint
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (initialState : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (badStream : ℕ → List (Finset BitString))
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i)
    (eventTime currentTime : ℕ) (hTime : eventTime < currentTime)
    (bad : Finset BitString) (hbad : bad ∈ badStream eventTime) :
    ∀ s ≤ N,
      Disjoint
        ((restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
          badStream hover ht_strict currentTime).live s) bad := by
  intro s hs
  let current := restrictedSampledRun 𝒜 N ambientLength overheadBound t
    initialState badStream hover ht_strict currentTime
  have hlive_root : current.live s ⊆ current.live 0 :=
    current.live_subset_root hs
  have hroot_time : current.live 0 ⊆
      (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
        badStream hover ht_strict (eventTime + 1)).live 0 :=
    restrictedSampledRun_root_antitone 𝒜 N ambientLength overheadBound t
      initialState badStream hover ht_strict (by omega)
  have himmediate := restrictedSampledRun_deleted_fresh 𝒜 N ambientLength
    overheadBound t initialState badStream hover ht_strict eventTime bad hbad
      0 (Nat.zero_le N)
  apply Finset.disjoint_left.mpr
  intro x hx hxbad
  exact (Finset.disjoint_left.mp himmediate)
    (hroot_time (hlive_root hx)) hxbad

/-- If the root survivor pool never becomes empty, root stabilization selects
a survivor that remains live forever after some finite time. -/
lemma restrictedSampledRun_exists_persistent_survivor
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (initialState : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (badStream : ℕ → List (Finset BitString))
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i)
    (hroot_nonempty : ∀ time,
      ((restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
        badStream hover ht_strict time).live 0).Nonempty) :
    ∃ (T : ℕ) (survivor : BitString), ∀ time ≥ T,
      survivor ∈
        (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
          badStream hover ht_strict time).live 0 := by
  obtain ⟨T, hstable⟩ := restrictedSampledRun_stabilizes 𝒜 N ambientLength
    overheadBound t initialState badStream hover ht_strict
  obtain ⟨survivor, hsurvivor⟩ := hroot_nonempty T
  refine ⟨T, survivor, ?_⟩
  intro time htime
  rw [hstable time htime]
  exact hsurvivor

/-
A persistent root survivor avoids every bad event in the chronological
stream, including events that occur before its stabilization stage.
-/
lemma restrictedSampledRun_exists_survivor_avoiding_stream
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (initialState : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (badStream : ℕ → List (Finset BitString))
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i)
    (hroot_nonempty : ∀ time,
      ((restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
        badStream hover ht_strict time).live 0).Nonempty) :
    ∃ (T : ℕ) (survivor : BitString),
      (∀ time ≥ T,
        survivor ∈
          (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
            badStream hover ht_strict time).live 0) ∧
      (∀ eventTime (bad : Finset BitString), bad ∈ badStream eventTime →
        survivor ∉ bad) := by
  obtain ⟨T, survivor, hsurvivor⟩ :=
    restrictedSampledRun_exists_persistent_survivor 𝒜 N ambientLength
      overheadBound t initialState badStream hover ht_strict hroot_nonempty
  refine ⟨T, survivor, hsurvivor, ?_⟩
  intro eventTime bad hbad hmem
  let currentTime := max T (eventTime + 1)
  have htime : eventTime < currentTime := by
    simp [currentTime]
  have hlive := hsurvivor currentTime (by simp [currentTime])
  have hdisjoint := restrictedSampledRun_processed_bad_disjoint 𝒜 N
    ambientLength overheadBound t initialState badStream hover ht_strict
    eventTime currentTime htime bad hbad 0 (Nat.zero_le N)
  exact (Finset.disjoint_left.mp hdisjoint) hlive hmem

end Kolmogorov
