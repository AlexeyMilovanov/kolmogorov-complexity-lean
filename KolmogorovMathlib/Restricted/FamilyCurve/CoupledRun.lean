import KolmogorovMathlib.Restricted.FamilyCurve.Basic.FiniteBadDescriptionCounting
import KolmogorovMathlib.Restricted.FamilyCurve.Basic
import KolmogorovMathlib.Restricted.FamilyCurve.BadStream

/-!
# Chronological sampled coupled run

This file packages the state and finite-stage recursion used by the M7 coupled
construction.  A rebuild is allowed to replace the good sets *after* the least
failed sampled scale, so deeper live intersections are not falsely required to
be subsets of their previous versions.  What is monotone in chronological time
is the root survivor pool.

The transition below is currently specified extensionally using the proved
suffix-rebuild theorem.  Its later coding refinement must identify this choice
with the partial-recursive maximum-intersection selector from `Selector.lean`;
no computability claim is made here.
-/

namespace Kolmogorov

/-- Good family members and their live prefix intersections at one instant of
the sampled construction. -/
structure RestrictedSampledRunState (𝒜 : DescriptionFamily)
    (N ambientLength overheadBound : ℕ) (t : ℕ → ℕ) where
  B : ℕ → Finset BitString
  live : ℕ → Finset BitString
  mem_family : ∀ s ≤ N, 𝒜.mem (B s)
  size_bound : ∀ s ≤ N, (B s).card ≤ 2 ^ t s
  live_subset : ∀ s ≤ N, live s ⊆ B s
  live_ambient : ∀ s ≤ N, ∀ x ∈ live s, x.length = ambientLength
  live_monotonic : ∀ s < N, live (s + 1) ⊆ live s
  density : ∀ s < N,
    (2 ^ t (s + 1)) * (live s).card ≤
      (overheadBound * 2 ^ t s) * (live (s + 1)).card

/-- Every live pool of a sampled run state is contained in the root pool. -/
lemma RestrictedSampledRunState.live_subset_root
    {𝒜 : DescriptionFamily} {N ambientLength overheadBound : ℕ}
    {t : ℕ → ℕ}
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    {s : ℕ} (hs : s ≤ N) : state.live s ⊆ state.live 0 := by
  intro x hx
  induction s with
  | zero => exact hx
  | succ s ih =>
      apply ih (by omega)
      exact state.live_monotonic s (by omega) hx

/-- After deleting `bad`, the density edge from `s` to `s+1` fails precisely
when its required lower bound is no longer met. -/
def restrictedSampledDensityFails
    {𝒜 : DescriptionFamily} {N ambientLength overheadBound : ℕ}
    {t : ℕ → ℕ}
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (bad : Finset BitString) (s : ℕ) : Prop :=
  (overheadBound * 2 ^ t s) * (state.live (s + 1) \ bad).card <
    (2 ^ t (s + 1)) * (state.live s \ bad).card

/-- Exact locality contract of one chronological update.

If no deleted density edge fails, `q = N` and all good sets are retained.  If
an edge fails, `q` is the least failed edge: levels through `q` are retained
and only the strict suffix is rebuilt.  Every rebuilt live set stays inside
the deleted live pool at `q`.  The final clause is the doubled density margin
restored on the rebuilt suffix. -/
def RestrictedSampledRunStepSpec
    {𝒜 : DescriptionFamily} {N ambientLength overheadBound : ℕ}
    {t : ℕ → ℕ}
    (state next : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (bad : Finset BitString) (q : ℕ) : Prop :=
  q ≤ N ∧
  ((q = N ∧ ∀ s < N, ¬ restrictedSampledDensityFails state bad s) ∨
    (q < N ∧ restrictedSampledDensityFails state bad q ∧
      ∀ s < q, ¬ restrictedSampledDensityFails state bad s)) ∧
  (∀ s ≤ q, next.B s = state.B s ∧
    next.live s = state.live s \ bad) ∧
  (∀ s, q ≤ s → s ≤ N → next.live s ⊆ state.live q \ bad) ∧
  (∀ s, q ≤ s → s < N →
    2 * ((2 ^ t (s + 1)) * (next.live s).card) ≤
      (overheadBound * 2 ^ t s) * (next.live (s + 1)).card)

/-- Suffix rebuilt live sets remain subsets of the rebuilt base set `Cnew q`. -/
private lemma restricted_rebuild_cnew_subset_root
    {Bnew Cnew : ℕ → Finset BitString} {q N : ℕ}
    (hinter : ∀ i, q ≤ i → i < N → Cnew (i + 1) = Cnew i ∩ Bnew (i + 1))
    (i : ℕ) (hqi : q ≤ i) (hiN : i ≤ N) : Cnew i ⊆ Cnew q := by
  induction hqi with
  | refl => exact Finset.Subset.rfl
  | @step i hqi ih =>
      rw [hinter i hqi (by omega)]
      exact Finset.inter_subset_left.trans (ih (by omega))

/-- Doubled density bound holds after rebuilding the suffix given the rebuilt density bound. -/
private lemma restricted_rebuild_density_doubled
    {𝒜 : DescriptionFamily} {ambientLength overheadBound : ℕ} {t : ℕ → ℕ}
    {Cnew : ℕ → Finset BitString} {s : ℕ}
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (hd : (2 ^ t (s + 1)) * (Cnew s).card ≤
      (𝒜.overhead ambientLength * 2 ^ t s) * (Cnew (s + 1)).card) :
    2 * ((2 ^ t (s + 1)) * (Cnew s).card) ≤
      (overheadBound * 2 ^ t s) * (Cnew (s + 1)).card := by
  calc
    2 * ((2 ^ t (s + 1)) * (Cnew s).card)
        ≤ 2 * ((𝒜.overhead ambientLength * 2 ^ t s) *
            (Cnew (s + 1)).card) := Nat.mul_le_mul_left 2 hd
    _ = ((2 * 𝒜.overhead ambientLength) * 2 ^ t s) *
          (Cnew (s + 1)).card := by ring
    _ ≤ (overheadBound * 2 ^ t s) * (Cnew (s + 1)).card :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hover)

/-- Constructs the updated state when a scale density condition fails and rebuilding occurs. -/
private noncomputable def restrictedSampledRunState_rebuild
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (bad : Finset BitString)
    (q : ℕ) (hq_le : q ≤ N) (hq_lt : q < N)
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (hprefix : ∀ s < q, ¬ restrictedSampledDensityFails state bad s)
    (Bnew Cnew : ℕ → Finset BitString)
    (hBq : Bnew q = state.B q)
    (hCq : Cnew q = state.live q \ bad)
    (hmem : ∀ i, q < i → i ≤ N → 𝒜.mem (Bnew i))
    (hsize : ∀ i, q < i → i ≤ N → (Bnew i).card ≤ 2 ^ t i)
    (hinter : ∀ i, q ≤ i → i < N → Cnew (i + 1) = Cnew i ∩ Bnew (i + 1))
    (hdensity : ∀ i, q ≤ i → i < N →
      (2 ^ t (i + 1)) * (Cnew i).card ≤
        (𝒜.overhead ambientLength * 2 ^ t i) * (Cnew (i + 1)).card) :
    RestrictedSampledRunState 𝒜 N ambientLength overheadBound t where
  B := fun s => if s ≤ q then state.B s else Bnew s
  live := fun s => if s ≤ q then state.live s \ bad else Cnew s
  mem_family := by
    intro s hs
    by_cases hsq : s ≤ q
    · simp only [ite_eq_left hsq]
      exact state.mem_family s hs
    · simp only [ite_eq_right hsq]
      exact hmem s (Nat.lt_of_not_ge hsq) hs
  size_bound := by
    intro s hs
    by_cases hsq : s ≤ q
    · simp only [ite_eq_left hsq]
      exact state.size_bound s hs
    · simp only [ite_eq_right hsq]
      exact hsize s (Nat.lt_of_not_ge hsq) hs
  live_subset := by
    intro s hs
    by_cases hsq : s ≤ q
    · simp only [ite_eq_left hsq]
      exact Finset.sdiff_subset.trans (state.live_subset s hs)
    · simp only [ite_eq_right hsq]
      have hqi : q ≤ s := Nat.le_of_lt (Nat.lt_of_not_ge hsq)
      induction hqi with
      | refl =>
          rw [hBq, hCq]
          exact Finset.sdiff_subset.trans (state.live_subset q hq_le)
      | @step i hqi ih =>
          rw [hinter i hqi (by omega)]
          exact Finset.inter_subset_right
  live_ambient := by
    intro s hs x hx
    by_cases hsq : s ≤ q
    · simp only [ite_eq_left hsq] at hx
      exact state.live_ambient s hs x (Finset.mem_sdiff.mp hx).1
    · simp only [ite_eq_right hsq] at hx
      have hxq : x ∈ Cnew q :=
        restricted_rebuild_cnew_subset_root hinter s (Nat.le_of_lt (Nat.lt_of_not_ge hsq)) hs hx
      rw [hCq] at hxq
      exact state.live_ambient q hq_le x (Finset.mem_sdiff.mp hxq).1
  live_monotonic := by
    intro s hsN
    by_cases hsuccq : s + 1 ≤ q
    · have hsq : s ≤ q := by omega
      simp only [ite_eq_left hsq, ite_eq_left hsuccq]
      intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨state.live_monotonic s hsN (Finset.mem_sdiff.mp hx).1,
          (Finset.mem_sdiff.mp hx).2⟩
    · have hqs : q ≤ s := by omega
      by_cases hsq : s ≤ q
      · have hsqeq : s = q := by omega
        subst s
        simp only [ite_eq_left le_rfl, ite_eq_right (by omega : ¬q + 1 ≤ q)]
        rw [hinter q le_rfl hq_lt, hCq]
        exact Finset.inter_subset_left
      · simp only [ite_eq_right hsq, ite_eq_right hsuccq]
        rw [hinter s hqs hsN]
        exact Finset.inter_subset_left
  density := by
    intro s hsN
    by_cases hsq : s < q
    · have hsuccq : s + 1 ≤ q := by omega
      have hsle : s ≤ q := Nat.le_of_lt hsq
      simp only [ite_eq_left hsle, ite_eq_left hsuccq]
      exact Nat.le_of_not_gt (hprefix s hsq)
    · have hqs : q ≤ s := Nat.le_of_not_gt hsq
      have hsucc_not : ¬s + 1 ≤ q := by omega
      have hover_one : 𝒜.overhead ambientLength ≤ overheadBound := by omega
      have hd := hdensity s hqs hsN
      by_cases hseq : s ≤ q
      · have hsqeq : s = q := by omega
        subst s
        simp only [ite_eq_left le_rfl, ite_eq_right (by omega : ¬q + 1 ≤ q)]
        rw [← hCq]
        exact hd.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hover_one))
      · simp only [ite_eq_right hseq, ite_eq_right hsucc_not]
        exact hd.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hover_one))

/-- Constructs the updated state when no scale density condition fails. -/
private def restrictedSampledRunState_noFail
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (bad : Finset BitString)
    (hfail : ¬ ∃ s, s < N ∧ restrictedSampledDensityFails state bad s) :
    RestrictedSampledRunState 𝒜 N ambientLength overheadBound t where
  B := state.B
  live := fun s => state.live s \ bad
  mem_family := state.mem_family
  size_bound := state.size_bound
  live_subset := by
    intro s hs
    exact Finset.sdiff_subset.trans (state.live_subset s hs)
  live_ambient := by
    intro s hs x hx
    exact state.live_ambient s hs x (Finset.mem_sdiff.mp hx).1
  live_monotonic := by
    intro s hs x hx
    exact Finset.mem_sdiff.mpr
      ⟨state.live_monotonic s hs (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
  density := by
    intro s hs
    exact Nat.le_of_not_gt (fun hlt => hfail ⟨s, hs, hlt⟩)

/-- One sound least-failed-scale update.  The factor-two overhead hypothesis is
what provides the post-rebuild doubled density margin; the weaker
`𝒜.overhead ambientLength ≤ overheadBound` assumption is insufficient for that
claim. -/
lemma restrictedSampledRun_step_preserves
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (bad : Finset BitString)
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i) :
    ∃ (next : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
      (q : ℕ), RestrictedSampledRunStepSpec state next bad q := by
  classical
  by_cases hfail : ∃ s, s < N ∧ restrictedSampledDensityFails state bad s
  · let q := Nat.find hfail
    have hq_spec : q < N ∧ restrictedSampledDensityFails state bad q :=
      Nat.find_spec hfail
    have hq_le : q ≤ N := Nat.le_of_lt hq_spec.1
    have hprefix : ∀ s < q, ¬ restrictedSampledDensityFails state bad s := by
      intro s hs hsFail
      exact Nat.find_min hfail hs ⟨hs.trans hq_spec.1, hsFail⟩
    obtain ⟨Bnew, Cnew, hBq, hCq, hmem, hsize, hinter, hdensity⟩ :=
      restricted_rebuild_suffix_pointwise_core 𝒜 ambientLength q N t
        (state.B q) (state.mem_family q hq_le)
        (state.live q) bad (state.live_subset q hq_le)
        (state.live_ambient q hq_le) (state.size_bound q hq_le)
        (fun i _hqi hiN => ht_strict i hiN)
    let next := restrictedSampledRunState_rebuild 𝒜 N ambientLength overheadBound t state bad
      q hq_le hq_spec.1 hover hprefix Bnew Cnew hBq hCq hmem hsize hinter hdensity
    refine ⟨next, q, hq_le, Or.inr ⟨hq_spec.1, hq_spec.2, hprefix⟩, ?_, ?_, ?_⟩
    · intro s hsq
      have hlive : next.live s = state.live s \ bad := by
        change (if s ≤ q then state.live s \ bad else Cnew s) = state.live s \ bad
        rw [ite_eq_left hsq]
      have hB : next.B s = state.B s := by
        change (if s ≤ q then state.B s else Bnew s) = state.B s
        rw [ite_eq_left hsq]
      exact ⟨hB, hlive⟩
    · intro s hqs hsN
      have hs_as_Cnew : next.live s = Cnew s := by
        by_cases hsq : s ≤ q
        · have hsqeq : s = q := by omega
          subst s
          change (if q ≤ q then state.live q \ bad else Cnew q) = Cnew q
          rw [ite_eq_left le_rfl, hCq]
        · change (if s ≤ q then state.live s \ bad else Cnew s) = Cnew s
          rw [ite_eq_right hsq]
      rw [hs_as_Cnew, ← hCq]
      exact restricted_rebuild_cnew_subset_root hinter s hqs hsN
    · intro s hqs hsN
      have hsucc_not : ¬s + 1 ≤ q := by omega
      have hs_as_Cnew : next.live s = Cnew s := by
        by_cases hsq : s ≤ q
        · have hsqeq : s = q := by omega
          subst s
          change (if q ≤ q then state.live q \ bad else Cnew q) = Cnew q
          rw [ite_eq_left le_rfl, hCq]
        · change (if s ≤ q then state.live s \ bad else Cnew s) = Cnew s
          rw [ite_eq_right hsq]
      have hsucc_as_Cnew : next.live (s + 1) = Cnew (s + 1) := by
        change (if s + 1 ≤ q then state.live (s + 1) \ bad else Cnew (s + 1)) = Cnew (s + 1)
        rw [ite_eq_right hsucc_not]
      rw [hs_as_Cnew, hsucc_as_Cnew]
      exact restricted_rebuild_density_doubled hover (hdensity s hqs hsN)
  · let next := restrictedSampledRunState_noFail 𝒜 N ambientLength overheadBound t state bad hfail
    refine ⟨next, N, le_rfl, Or.inl ⟨rfl, ?_⟩, ?_, ?_, ?_⟩
    · intro s hs hbad
      exact hfail ⟨s, hs, hbad⟩
    · intro s _hs
      exact ⟨rfl, rfl⟩
    · intro s hNs hsN
      have hs_eq : s = N := by omega
      subst s
      exact Finset.Subset.rfl
    · intro s hNs hsN
      omega

/-- One step of the sampled run: delete the bad set from the root pool and rebuild the live pools
at all scales. -/
noncomputable def restrictedSampledRunStep
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (bad : Finset BitString)
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i) :
    RestrictedSampledRunState 𝒜 N ambientLength overheadBound t :=
  Classical.choose
    (restrictedSampledRun_step_preserves 𝒜 N ambientLength overheadBound t
      state bad hover ht_strict)

/-- The state produced by one sampled run step satisfies the step specification. -/
lemma restrictedSampledRunStep_spec
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (bad : Finset BitString)
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i) :
    ∃ q, RestrictedSampledRunStepSpec state
      (restrictedSampledRunStep 𝒜 N ambientLength overheadBound t state bad
        hover ht_strict) bad q :=
  Classical.choose_spec
    (restrictedSampledRun_step_preserves 𝒜 N ambientLength overheadBound t
      state bad hover ht_strict)

/-- After a step the root pool is the previous root pool with the bad set removed. -/
lemma RestrictedSampledRunStepSpec.root_eq
    {𝒜 : DescriptionFamily} {N ambientLength overheadBound : ℕ}
    {t : ℕ → ℕ}
    {state next : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t}
    {bad : Finset BitString} {q : ℕ}
    (h : RestrictedSampledRunStepSpec state next bad q) :
    next.live 0 = state.live 0 \ bad := by
  exact (h.2.2.1 0 (Nat.zero_le q)).2

/-- After a step every live pool is contained in the previous root pool minus the bad set. -/
lemma RestrictedSampledRunStepSpec.live_subset_old_root
    {𝒜 : DescriptionFamily} {N ambientLength overheadBound : ℕ}
    {t : ℕ → ℕ}
    {state next : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t}
    {bad : Finset BitString} {q s : ℕ}
    (h : RestrictedSampledRunStepSpec state next bad q) (hs : s ≤ N) :
    next.live s ⊆ state.live 0 \ bad := by
  rcases le_total s q with hsq | hqs
  · rw [(h.2.2.1 s hsq).2]
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨state.live_subset_root hs (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
  · exact (h.2.2.2.1 s hqs hs).trans (by
      intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨state.live_subset_root h.1 (Finset.mem_sdiff.mp hx).1,
          (Finset.mem_sdiff.mp hx).2⟩)

/-- The step removes exactly the bad set from the root pool. -/
lemma restrictedSampledRunStep_root_eq
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (bad : Finset BitString)
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i) :
    (restrictedSampledRunStep 𝒜 N ambientLength overheadBound t state bad
      hover ht_strict).live 0 = state.live 0 \ bad := by
  obtain ⟨q, hq⟩ := restrictedSampledRunStep_spec 𝒜 N ambientLength
    overheadBound t state bad hover ht_strict
  exact hq.root_eq

/-- After the step every live pool avoids the bad set and stays inside the old root pool. -/
lemma restrictedSampledRunStep_live_subset_root
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (bad : Finset BitString)
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i)
    (s : ℕ) (hs : s ≤ N) :
    (restrictedSampledRunStep 𝒜 N ambientLength overheadBound t state bad
      hover ht_strict).live s ⊆ state.live 0 \ bad := by
  obtain ⟨q, hq⟩ := restrictedSampledRunStep_spec 𝒜 N ambientLength
    overheadBound t state bad hover ht_strict
  exact hq.live_subset_old_root hs

/-- Process one finite batch of newly arrived bad sets. -/
noncomputable def restrictedSampledRunProcess
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (events : List (Finset BitString)) :
    RestrictedSampledRunState 𝒜 N ambientLength overheadBound t :=
  events.foldl (fun current bad =>
    restrictedSampledRunStep 𝒜 N ambientLength overheadBound t current bad
      hover ht_strict) state

/-- Processing a list of bad sets keeps every live pool inside the root pool it started from. -/
lemma restrictedSampledRunProcess_live_subset_root
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (events : List (Finset BitString)) (s : ℕ) (hs : s ≤ N) :
    (restrictedSampledRunProcess 𝒜 N ambientLength overheadBound t hover
      ht_strict state events).live s ⊆ state.live 0 := by
  induction events generalizing state with
  | nil =>
      exact state.live_subset_root hs
  | cons bad events ih =>
      let next := restrictedSampledRunStep 𝒜 N ambientLength overheadBound t
        state bad hover ht_strict
      have htail :
          (restrictedSampledRunProcess 𝒜 N ambientLength overheadBound t hover
            ht_strict next events).live s ⊆ next.live 0 :=
        ih next
      have hroot : next.live 0 = state.live 0 \ bad := by
        exact restrictedSampledRunStep_root_eq 𝒜 N ambientLength overheadBound
          t state bad hover ht_strict
      change
        (restrictedSampledRunProcess 𝒜 N ambientLength overheadBound t hover
          ht_strict next events).live s ⊆ state.live 0
      exact htail.trans (by rw [hroot]; exact Finset.sdiff_subset)

/-- A bad set processed in a run is disjoint from every live pool afterwards. -/
lemma restrictedSampledRunProcess_deleted_fresh
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (events : List (Finset BitString)) (bad : Finset BitString)
    (hbad : bad ∈ events) (s : ℕ) (hs : s ≤ N) :
    Disjoint
      ((restrictedSampledRunProcess 𝒜 N ambientLength overheadBound t hover
        ht_strict state events).live s) bad := by
  induction events generalizing state with
  | nil => simp at hbad
  | cons head events ih =>
      let next := restrictedSampledRunStep 𝒜 N ambientLength overheadBound t
        state head hover ht_strict
      simp only [List.mem_cons] at hbad
      rcases hbad with rfl | htail
      · apply Finset.disjoint_left.mpr
        intro x hx hxbad
        have hxroot : x ∈ next.live 0 :=
          restrictedSampledRunProcess_live_subset_root 𝒜 N ambientLength
            overheadBound t hover ht_strict next events s hs hx
        have hroot : next.live 0 = state.live 0 \ bad := by
          exact restrictedSampledRunStep_root_eq 𝒜 N ambientLength
            overheadBound t state bad hover ht_strict
        exact (Finset.mem_sdiff.mp (hroot ▸ hxroot)).2 hxbad
      · exact ih next htail

/-- The chronological run treats `badStream time` as the finite batch of new
bad sets arriving between times `time` and `time + 1`. -/
noncomputable def restrictedSampledRun
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (initialState : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (badStream : ℕ → List (Finset BitString))
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i) :
    ℕ → RestrictedSampledRunState 𝒜 N ambientLength overheadBound t
  | 0 => initialState
  | time + 1 =>
      restrictedSampledRunProcess 𝒜 N ambientLength overheadBound t hover
        ht_strict
        (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
          badStream hover ht_strict time)
        (badStream time)

/-- A bad set deleted at some time stays deleted: it is disjoint from all live pools at all
later times. -/
lemma restrictedSampledRun_deleted_fresh
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (initialState : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (badStream : ℕ → List (Finset BitString))
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i)
    (time : ℕ) (bad : Finset BitString) (hbad : bad ∈ badStream time) :
    ∀ s ≤ N,
      Disjoint
        ((restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
          badStream hover ht_strict (time + 1)).live s) bad := by
  intro s hs
  change Disjoint
    ((restrictedSampledRunProcess 𝒜 N ambientLength overheadBound t hover
      ht_strict
      (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
        badStream hover ht_strict time)
      (badStream time)).live s) bad
  exact restrictedSampledRunProcess_deleted_fresh 𝒜 N ambientLength
    overheadBound t hover ht_strict _ (badStream time) bad hbad s hs

/-- All live sets at every later time remain inside the initial root survivor
pool.  This is the sound chronological monotonicity invariant; pointwise
monotonicity of deeper levels is false across suffix rebuilds. -/
lemma restrictedSampledRun_invariants
    (𝒜 : DescriptionFamily) (N ambientLength overheadBound : ℕ)
    (t : ℕ → ℕ)
    (initialState : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    (badStream : ℕ → List (Finset BitString))
    (hover : 2 * 𝒜.overhead ambientLength ≤ overheadBound)
    (ht_strict : ∀ i < N, t (i + 1) < t i)
    (time : ℕ) :
    ∀ s ≤ N,
      (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
        badStream hover ht_strict time).live s ⊆ initialState.live 0 := by
  intro s hs
  induction time generalizing s with
  | zero => exact initialState.live_subset_root hs
  | succ time ih =>
      have hstep := restrictedSampledRunProcess_live_subset_root 𝒜 N
        ambientLength overheadBound t hover ht_strict
        (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
          badStream hover ht_strict time)
        (badStream time) s hs
      change
        (restrictedSampledRunProcess 𝒜 N ambientLength overheadBound t hover
          ht_strict
          (restrictedSampledRun 𝒜 N ambientLength overheadBound t initialState
            badStream hover ht_strict time)
          (badStream time)).live s ⊆ initialState.live 0
      exact hstep.trans (ih 0 (Nat.zero_le N))

end Kolmogorov
