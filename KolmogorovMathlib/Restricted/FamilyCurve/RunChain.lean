import KolmogorovMathlib.Restricted.FamilyCurve.CoupledRun

/-!
# M7: event-indexed run chains and the version-count bound

This module proves the survey's bound on the number of model rebuilds
(VS40 §6, proof of `thm:family-curve`) at the level of an abstract chain of
sampled run states connected by `RestrictedSampledRunStepSpec` steps.  The
effective anchored run instantiates such a chain (one step per processed
stream event); no computability enters here.

The main theorem `RestrictedRunChain.rebuildSteps_card_mul_le` charges every step
whose least failed edge is `≤ s` either to an `L`-event (an abstract
classification, instantiated by "the event is visible at snapshot complexity
at most `grid.i s`", of which there are at most `CL` many) or to
`2^(t (q+1))` worth of freshly deleted volume drawn from the `S`-events
(instantiated by the small bad sets, whose total volume `VS` the boundary
slope controls).  Everything is stated multiplicatively over `ℕ`.
-/

namespace Kolmogorov

/-- An event-indexed chain of sampled run states: `M` steps, each satisfying
the frozen one-step contract at its least failed edge. -/
structure RestrictedRunChain (𝒜 : DescriptionFamily)
    (N ambientLength overheadBound : ℕ) (t : ℕ → ℕ) (M : ℕ) where
  states : ℕ → RestrictedSampledRunState 𝒜 N ambientLength overheadBound t
  bads : ℕ → Finset BitString
  edges : ℕ → ℕ
  spec : ∀ m < M, RestrictedSampledRunStepSpec (states m) (states (m + 1))
    (bads m) (edges m)

namespace RestrictedRunChain

variable {𝒜 : DescriptionFamily} {N ambientLength overheadBound : ℕ}
  {t : ℕ → ℕ} {M : ℕ}
  (chain : RestrictedRunChain 𝒜 N ambientLength overheadBound t M)

/-- Levels at or below the failed edge are retained modulo deletion. -/
lemma live_step_eq {m : ℕ} (hm : m < M) {r : ℕ} (hr : r ≤ chain.edges m) :
    (chain.states (m + 1)).live r = (chain.states m).live r \ chain.bads m :=
  ((chain.spec m hm).2.2.1 r hr).2

/-- The root pool evolves by exact deletion at every step. -/
lemma live_zero_step {m : ℕ} (hm : m < M) :
    (chain.states (m + 1)).live 0 = (chain.states m).live 0 \ chain.bads m :=
  chain.live_step_eq hm (Nat.zero_le _)

/-- The root pool is antitone along the chain. -/
lemma live_zero_antitone {m m' : ℕ} (h : m ≤ m') (hM : m' ≤ M) :
    (chain.states m').live 0 ⊆ (chain.states m).live 0 := by
  induction h with
  | refl => exact fun x hx => hx
  | @step m'' h ih =>
      intro x hx
      refine ih (by omega) ?_
      rw [chain.live_zero_step (by omega : m'' < M)] at hx
      exact (Finset.mem_sdiff.mp hx).1

/-- An element deleted at step `m` never returns to the root pool. -/
lemma deleted_not_in_root {m m' : ℕ} (hm : m < m') (hM : m' ≤ M)
    {x : BitString} (hx : x ∈ chain.bads m) :
    x ∉ (chain.states m').live 0 := by
  intro hmem
  have hsub := chain.live_zero_antitone (show m + 1 ≤ m' by omega) hM hmem
  rw [chain.live_zero_step (by omega : m < M)] at hsub
  exact (Finset.mem_sdiff.mp hsub).2 hx

/-- Over an interval whose steps all fail at or above `r`, the level-`r`
pool evolves by pure deletion of the interval's events. -/
lemma window_live_eq {a b r : ℕ} (hab : a ≤ b) (hbM : b ≤ M)
    (hr : ∀ m, a ≤ m → m < b → r ≤ chain.edges m) :
    (chain.states b).live r = (chain.states a).live r \
      (Finset.Ico a b).biUnion chain.bads := by
  induction hab with
  | refl => simp
  | @step b' hab ih =>
      have hb'M : b' ≤ M := by omega
      rw [chain.live_step_eq (by omega : b' < M) (hr b' hab (by omega)),
        ih hb'M (fun m hm hm' => hr m hm (by omega))]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hx, hno⟩, hxb⟩
        refine ⟨hx, ?_⟩
        rintro ⟨a', ⟨ha1, ha2⟩, hxa⟩
        by_cases h : a' = b'
        · exact hxb (h ▸ hxa)
        · exact hno ⟨a', ⟨ha1, by omega⟩, hxa⟩
      · rintro ⟨hx, hno⟩
        refine ⟨⟨hx, ?_⟩, ?_⟩
        · rintro ⟨a', ⟨ha1, ha2⟩, hxa⟩
          exact hno ⟨a', ⟨ha1, by omega⟩, hxa⟩
        · intro hxb
          exact hno ⟨b', ⟨hab, by omega⟩, hxb⟩

/-- Multiplicative density floor inside one state: the level-`r` pool holds at
least an `overheadBound^r`-fraction of the root pool at the exponent scale. -/
lemma live_card_floor
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t)
    {r : ℕ} (hr : r ≤ N) :
    2 ^ t r * (state.live 0).card ≤
      overheadBound ^ r * 2 ^ t 0 * (state.live r).card := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrN : r ≤ N := by omega
      have hdens := state.density r (by omega)
      have hih := ih hrN
      have hstep :
          2 ^ t r * (2 ^ t (r + 1) * (state.live 0).card) ≤
            2 ^ t r *
              (overheadBound ^ (r + 1) * 2 ^ t 0 *
                (state.live (r + 1)).card) := by
        calc
          2 ^ t r * (2 ^ t (r + 1) * (state.live 0).card)
              = 2 ^ t (r + 1) * (2 ^ t r * (state.live 0).card) := by ring
          _ ≤ 2 ^ t (r + 1) *
                (overheadBound ^ r * 2 ^ t 0 * (state.live r).card) :=
              Nat.mul_le_mul_left _ hih
          _ = overheadBound ^ r * 2 ^ t 0 *
                (2 ^ t (r + 1) * (state.live r).card) := by ring
          _ ≤ overheadBound ^ r * 2 ^ t 0 *
                (overheadBound * 2 ^ t r * (state.live (r + 1)).card) :=
              Nat.mul_le_mul_left _ hdens
          _ = 2 ^ t r *
                (overheadBound ^ (r + 1) * 2 ^ t 0 *
                  (state.live (r + 1)).card) := by ring
      exact Nat.le_of_mul_le_mul_left hstep (pow_pos (by omega) _)

/-- Root-floor transported to any level of any chain state: the level-`q` pool
is nonvanishing at the multiplicative scale `2 ^ t q / (2·OB^q)`. -/
lemma live_floor_of_root
    (hroot : ∀ m ≤ M, 2 ^ t 0 ≤ 2 * ((chain.states m).live 0).card)
    {m q : ℕ} (hm : m ≤ M) (hq : q ≤ N) :
    2 ^ t q ≤ 2 * overheadBound ^ q * ((chain.states m).live q).card := by
  have hfloor := live_card_floor (chain.states m) hq
  have hcombined :
      2 ^ t 0 * 2 ^ t q ≤
        2 ^ t 0 * (2 * overheadBound ^ q * ((chain.states m).live q).card) := by
    calc
      2 ^ t 0 * 2 ^ t q
          ≤ (2 * ((chain.states m).live 0).card) * 2 ^ t q :=
            Nat.mul_le_mul_right _ (hroot m hm)
      _ = 2 * (2 ^ t q * ((chain.states m).live 0).card) := by ring
      _ ≤ 2 * (overheadBound ^ q * 2 ^ t 0 *
            ((chain.states m).live q).card) :=
          Nat.mul_le_mul_left _ hfloor
      _ = 2 ^ t 0 *
            (2 * overheadBound ^ q * ((chain.states m).live q).card) := by ring
  exact Nat.le_of_mul_le_mul_left hcombined (pow_pos (by omega) _)

section Counting

variable (s : ℕ) (isL : ℕ → Bool)

/-- The steps that rebuild the levels above `s`. -/
def rebuildSteps : Finset ℕ :=
  (Finset.range M).filter fun m => chain.edges m ≤ s

/-- The steps whose least failed edge is exactly `q`. -/
def edgeSteps (q : ℕ) : Finset ℕ :=
  (Finset.range M).filter fun m => chain.edges m = q

/-- Rebuild steps split by their exact least failed edge. -/
lemma rebuildSteps_card_le_sum :
    (chain.rebuildSteps s).card ≤
      ∑ q ∈ Finset.range (s + 1), (chain.edgeSteps q).card := by
  have hsub : chain.rebuildSteps s ⊆
      (Finset.range (s + 1)).biUnion chain.edgeSteps := by
    intro m hm
    rw [rebuildSteps, Finset.mem_filter] at hm
    rw [Finset.mem_biUnion]
    exact ⟨chain.edges m, Finset.mem_range.mpr (by omega),
      Finset.mem_filter.mpr ⟨hm.1, rfl⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- The window start before step `m` at edge budget `q`: the greatest earlier
step whose edge is `≤ q`. -/
noncomputable def windowStart (q m : ℕ) : ℕ :=
  Nat.findGreatest (fun a => chain.edges a ≤ q ∧ a < m) m

variable {chain} in
/-- Specification of the window start when a witness exists. -/
lemma windowStart_spec {q m a₀ : ℕ} (ha₀ : chain.edges a₀ ≤ q ∧ a₀ < m) :
    (chain.edges (chain.windowStart q m) ≤ q ∧ chain.windowStart q m < m) ∧
      ∀ a, chain.windowStart q m < a → a < m → ¬ chain.edges a ≤ q := by
  unfold windowStart
  constructor
  · exact Nat.findGreatest_spec
      (P := fun a => chain.edges a ≤ q ∧ a < m) (Nat.le_of_lt ha₀.2) ha₀
  · intro a ha ham hle
    have hle' := Nat.le_findGreatest
      (P := fun a => chain.edges a ≤ q ∧ a < m) (Nat.le_of_lt ham) ⟨hle, ham⟩
    omega

/-- No step inside the window fails at an edge `≤ q`; consequently every level
`r ≤ q + 1` evolves by pure deletion across the window. -/
lemma window_deletion_only {q m a₀ : ℕ} (hmM : m ≤ M)
    (ha₀ : chain.edges a₀ ≤ q ∧ a₀ < m) {r : ℕ} (hr : r ≤ q + 1) :
    (chain.states m).live r =
      (chain.states (chain.windowStart q m + 1)).live r \
        (Finset.Ico (chain.windowStart q m + 1) m).biUnion chain.bads := by
  obtain ⟨⟨_hEdge, hlt⟩, hmax⟩ := windowStart_spec (chain := chain) ha₀
  exact chain.window_live_eq (by omega) hmM
    (fun m' hm' hm'' => by
      have := hmax m' (by omega) (by omega)
      omega)

end Counting

section EdgeCount

/-- The drained set of the window ending at step `m` (edge budget `q`): the
elements removed from the level-`q+1` pool between the window start and the
completion of step `m`'s deletion. -/
noncomputable def windowDrain (q m : ℕ) : Finset BitString :=
  (chain.states (chain.windowStart q m + 1)).live (q + 1) \
    ((chain.states m).live (q + 1) \ chain.bads m)

/-- One S-charged window drains a definite fresh volume: the set
`E = A.live (q+1) \ (B.live (q+1) \ bad)` of elements removed from the level
`q+1` pool across the window satisfies `2·OB^(q+1)·|E| ≥ 2^(t (q+1))`. -/
lemma window_drain_card
    (hroot : ∀ m' ≤ M, 2 ^ t 0 ≤ 2 * ((chain.states m').live 0).card)
    {q m : ℕ} (hqN : q < N) (hmM : m < M) (hedge : chain.edges m = q)
    {a₀ : ℕ} (ha₀ : chain.edges a₀ ≤ q ∧ a₀ < m) :
    2 ^ t (q + 1) ≤
      2 * overheadBound ^ (q + 1) *
        ((chain.states (chain.windowStart q m + 1)).live (q + 1) \
          ((chain.states m).live (q + 1) \ chain.bads m)).card := by
  classical
  set a := chain.windowStart q m with ha_def
  obtain ⟨⟨haEdge, haLt⟩, _hmax⟩ := windowStart_spec (chain := chain) ha₀
  set A := chain.states (a + 1) with hA_def
  set Bst := chain.states m with hB_def
  set E := A.live (q + 1) \ (Bst.live (q + 1) \ chain.bads m) with hE_def
  -- doubled margin at the window start
  have hdoubled : 2 * (2 ^ t (q + 1) * (A.live q).card) ≤
      overheadBound * 2 ^ t q * (A.live (q + 1)).card := by
    have h := (chain.spec a (by omega)).2.2.2.2 q haEdge hqN
    calc 2 * (2 ^ t (q + 1) * (A.live q).card) ≤
        (overheadBound * 2 ^ t q) * (A.live (q + 1)).card := h
      _ = overheadBound * 2 ^ t q * (A.live (q + 1)).card := rfl
  -- failure of the density edge `q` at step `m`
  have hfails : overheadBound * 2 ^ t q *
      (Bst.live (q + 1) \ chain.bads m).card <
        2 ^ t (q + 1) * (Bst.live q \ chain.bads m).card := by
    have hspec := (chain.spec m hmM).2.1
    rcases hspec with ⟨hqEq, _⟩ | ⟨_, hfail, _⟩
    · omega
    · rw [hedge] at hfail
      exact hfail
  -- window monotonicity at level `q`
  have hmono_q : (Bst.live q \ chain.bads m).card ≤ (A.live q).card := by
    apply Finset.card_le_card
    intro x hx
    have hx' := (Finset.mem_sdiff.mp hx).1
    rw [hB_def, chain.window_deletion_only (by omega) ha₀ (by omega : q ≤ q + 1)]
      at hx'
    exact (Finset.mem_sdiff.mp hx').1
  -- covering `A.live (q+1)` by the surviving pool and the drained set
  have hcover : (A.live (q + 1)).card ≤
      (Bst.live (q + 1) \ chain.bads m).card + E.card := by
    calc (A.live (q + 1)).card
        ≤ ((Bst.live (q + 1) \ chain.bads m) ∪ E).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_union]
          by_cases hxB : x ∈ Bst.live (q + 1) \ chain.bads m
          · exact Or.inl hxB
          · exact Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
      _ ≤ (Bst.live (q + 1) \ chain.bads m).card + E.card :=
          Finset.card_union_le _ _
  -- eliminate: OB·2^(t q)·|E| ≥ 2^(t (q+1))·|A.live q|
  have hkey : 2 ^ t (q + 1) * (A.live q).card ≤
      overheadBound * 2 ^ t q * E.card := by
    have h1 : overheadBound * 2 ^ t q * (A.live (q + 1)).card ≤
        overheadBound * 2 ^ t q *
          ((Bst.live (q + 1) \ chain.bads m).card + E.card) :=
      Nat.mul_le_mul_left _ hcover
    rw [Nat.mul_add] at h1
    have h2 : 2 ^ t (q + 1) * (Bst.live q \ chain.bads m).card ≤
        2 ^ t (q + 1) * (A.live q).card :=
      Nat.mul_le_mul_left _ hmono_q
    omega
  -- combine with the level-`q` floor at the window-start state
  have hfloor : 2 ^ t q ≤ 2 * overheadBound ^ q * (A.live q).card :=
    chain.live_floor_of_root hroot (by omega) (by omega)
  have hfinal : 2 ^ t q * 2 ^ t (q + 1) ≤
      2 ^ t q * (2 * overheadBound ^ (q + 1) * E.card) := by
    calc
      2 ^ t q * 2 ^ t (q + 1)
          ≤ (2 * overheadBound ^ q * (A.live q).card) * 2 ^ t (q + 1) :=
            Nat.mul_le_mul_right _ hfloor
      _ = 2 * overheadBound ^ q * (2 ^ t (q + 1) * (A.live q).card) := by ring
      _ ≤ 2 * overheadBound ^ q * (overheadBound * 2 ^ t q * E.card) :=
          Nat.mul_le_mul_left _ hkey
      _ = 2 ^ t q * (2 * overheadBound ^ (q + 1) * E.card) := by ring
  exact Nat.le_of_mul_le_mul_left hfinal (pow_pos (by omega) _)

/-- Every element of the window drain was deleted by an event strictly inside
the window `(windowStart, m]`. -/
lemma windowDrain_source
    {q m : ℕ} (hmM : m < M)
    {a₀ : ℕ} (ha₀ : chain.edges a₀ ≤ q ∧ a₀ < m)
    {x : BitString} (hx : x ∈ chain.windowDrain q m) :
    ∃ a, (chain.windowStart q m < a ∧ a ≤ m) ∧ x ∈ chain.bads a := by
  obtain ⟨⟨_hEdge, hlt⟩, _hmax⟩ := windowStart_spec (chain := chain) ha₀
  rw [windowDrain, Finset.mem_sdiff] at hx
  obtain ⟨hxA, hxB⟩ := hx
  by_cases hxm : x ∈ chain.bads m
  · exact ⟨m, ⟨hlt, le_rfl⟩, hxm⟩
  · have hxBlive : x ∉ (chain.states m).live (q + 1) := by
      intro hmem
      exact hxB (Finset.mem_sdiff.mpr ⟨hmem, hxm⟩)
    have hwindow := chain.window_deletion_only (q := q) (m := m)
      (by omega : m ≤ M) ha₀ (le_rfl : q + 1 ≤ q + 1)
    rw [hwindow] at hxBlive
    have : ¬ (x ∈ (chain.states (chain.windowStart q m + 1)).live (q + 1) ∧
        x ∉ (Finset.Ico (chain.windowStart q m + 1) m).biUnion chain.bads) := by
      intro h
      exact hxBlive (Finset.mem_sdiff.mpr ⟨h.1, h.2⟩)
    push Not at this
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp (this hxA)
    rw [Finset.mem_Ico] at ha
    exact ⟨a, ⟨by omega, by omega⟩, hxa⟩

/-- Every element of the window drain is gone from the root pool right after
step `m`. -/
lemma windowDrain_dead
    {q m : ℕ} (hmM : m < M)
    {a₀ : ℕ} (ha₀ : chain.edges a₀ ≤ q ∧ a₀ < m)
    {x : BitString} (hx : x ∈ chain.windowDrain q m)
    {m' : ℕ} (hm' : m < m') (hm'M : m' ≤ M) :
    x ∉ (chain.states m').live 0 := by
  obtain ⟨a, ⟨_ha1, ha2⟩, hxa⟩ := chain.windowDrain_source hmM ha₀ hx
  exact chain.deleted_not_in_root (by omega) hm'M hxa

/-- Per-edge counting: the steps failing exactly at edge `q` split into at
most `CL + 1` L-charged steps and an S-charged remainder whose count is
controlled by the total S-volume. -/
theorem edgeSteps_card_le_of_charges
    (hroot : ∀ m' ≤ M, 2 ^ t 0 ≤ 2 * ((chain.states m').live 0).card)
    {q : ℕ} (hqN : q < N) (isL : ℕ → Bool) {CL VS : ℕ}
    (hL : ((Finset.range M).filter fun a => isL a = true).card ≤ CL)
    (hS : ∑ a ∈ (Finset.range M).filter (fun a => isL a = false),
        (chain.bads a).card ≤ VS) :
    ∃ SC : ℕ, (chain.edgeSteps q).card ≤ CL + 1 + SC ∧
      SC * 2 ^ t (q + 1) ≤ 2 * overheadBound ^ (q + 1) * VS := by
  classical
  set T := chain.edgeSteps q with hT
  have hTmem : ∀ m ∈ T, m < M ∧ chain.edges m = q := by
    intro m hm
    rw [hT, edgeSteps, Finset.mem_filter, Finset.mem_range] at hm
    exact hm
  set hasStart : ℕ → Prop := fun m => ∃ a, chain.edges a ≤ q ∧ a < m
    with hhasStart
  set hasL : ℕ → Prop := fun m =>
    ∃ a, chain.windowStart q m < a ∧ a ≤ m ∧ isL a = true with hhasL
  set T0 := T.filter (fun m => ¬ hasStart m) with hT0
  set TL := T.filter (fun m => hasStart m ∧ hasL m) with hTLdef
  set TS := T.filter (fun m => hasStart m ∧ ¬ hasL m) with hTSdef
  -- the split covers everything
  have hsplit : T.card ≤ T0.card + TL.card + TS.card := by
    have hsub : T ⊆ T0 ∪ TL ∪ TS := by
      intro m hm
      by_cases h1 : hasStart m
      · by_cases h2 : hasL m
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hm, h1, h2⟩))
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hm, h1, h2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hm, h1⟩))
    calc T.card ≤ (T0 ∪ TL ∪ TS).card := Finset.card_le_card hsub
      _ ≤ (T0 ∪ TL).card + TS.card := Finset.card_union_le _ _
      _ ≤ T0.card + TL.card + TS.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
  -- at most one step lacks a window start
  have hT0card : T0.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro m hm m' hm'
    rw [hT0, Finset.mem_filter] at hm hm'
    by_contra hne
    rcases Nat.lt_or_ge m m' with h | h
    · exact hm'.2 ⟨m, (hTmem m hm.1).2.le, h⟩
    · exact hm.2 ⟨m', (hTmem m' hm'.1).2.le, by omega⟩
  -- L-charged steps inject into the L-events through their chosen witness
  have hTLcard : TL.card ≤ CL := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun m => if h : hasL m then h.choose else 0) ?_ ?_) hL
    · intro m hm
      have hm₁ : m ∈ TL := hm
      rw [hTLdef, Finset.mem_filter] at hm₁
      obtain ⟨hmT, _hstart, hL'⟩ := hm₁
      simp only [dif_pos hL']
      obtain ⟨_h1, h2, h3⟩ := hL'.choose_spec
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by
          have := (hTmem m hmT).1
          omega), h3⟩
    · intro m hm m' hm' heq
      have hm₁ : m ∈ TL := hm
      have hm₂ : m' ∈ TL := hm'
      rw [hTLdef, Finset.mem_filter] at hm₁ hm₂
      obtain ⟨hmT, hstart, hLm⟩ := hm₁
      obtain ⟨hmT', hstart', hLm'⟩ := hm₂
      have heq' : (if h : hasL m then h.choose else 0) =
          (if h : hasL m' then h.choose else 0) := heq
      rw [dif_pos hLm, dif_pos hLm'] at heq'
      by_contra hne
      obtain ⟨hc1, hc2, _⟩ := hLm.choose_spec
      obtain ⟨hc1', hc2', _⟩ := hLm'.choose_spec
      rcases Nat.lt_or_ge m m' with h | h
      · have hws : m ≤ chain.windowStart q m' :=
          Nat.le_findGreatest
            (P := fun a => chain.edges a ≤ q ∧ a < m') (by omega)
            ⟨(hTmem m hmT).2.le, h⟩
        omega
      · have h' : m' < m := by omega
        have hws : m' ≤ chain.windowStart q m :=
          Nat.le_findGreatest
            (P := fun a => chain.edges a ≤ q ∧ a < m) (by omega)
            ⟨(hTmem m' hmT').2.le, h'⟩
        omega
  -- S-charged steps drain disjoint fresh volume from the S-events
  have hTSvol : TS.card * 2 ^ t (q + 1) ≤ 2 * overheadBound ^ (q + 1) * VS := by
    set SBad := ((Finset.range M).filter (fun a => isL a = false)).biUnion
      chain.bads with hSBad
    have hstart' : ∀ m ∈ TS, ∃ a, chain.edges a ≤ q ∧ a < m := by
      intro m hm
      exact (Finset.mem_filter.mp hm).2.1
    have hnoL : ∀ m ∈ TS, ¬ hasL m := by
      intro m hm
      exact (Finset.mem_filter.mp hm).2.2
    have hTS_T : ∀ m ∈ TS, m < M ∧ chain.edges m = q := by
      intro m hm
      exact hTmem m (Finset.mem_filter.mp hm).1
    -- each drain sits inside the S-events
    have hdrainS : ∀ m ∈ TS, chain.windowDrain q m ⊆ SBad := by
      intro m hm x hx
      obtain ⟨a, ⟨ha1, ha2⟩, hxa⟩ := chain.windowDrain_source
        (hTS_T m hm).1 (hstart' m hm).choose_spec hx
      have haS : isL a = false := by
        by_contra hL'
        exact hnoL m hm ⟨a, ha1, ha2, by
          cases h : isL a
          · exact absurd h hL'
          · rfl⟩
      exact Finset.mem_biUnion.mpr
        ⟨a, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by have := (hTS_T m hm).1; omega), haS⟩, hxa⟩
    -- drains of distinct S-charged steps are disjoint
    have hdisj : ∀ m ∈ TS, ∀ m' ∈ TS, m ≠ m' →
        Disjoint (chain.windowDrain q m) (chain.windowDrain q m') := by
      have key : ∀ m ∈ TS, ∀ m' ∈ TS, m < m' →
          Disjoint (chain.windowDrain q m) (chain.windowDrain q m') := by
        intro m hm m' hm' hlt
        rw [Finset.disjoint_left]
        intro x hxm hxm'
        have hwsm' : m ≤ chain.windowStart q m' :=
          Nat.le_findGreatest
            (P := fun a => chain.edges a ≤ q ∧ a < m') (by omega)
            ⟨(hTS_T m hm).2.le, hlt⟩
        have hM' : chain.windowStart q m' + 1 ≤ M := by
          obtain ⟨⟨_, hlt'⟩, _⟩ := windowStart_spec (chain := chain)
            (hstart' m' hm').choose_spec
          have := (hTS_T m' hm').1
          omega
        have hdead : x ∉ (chain.states (chain.windowStart q m' + 1)).live 0 :=
          chain.windowDrain_dead (hTS_T m hm).1
            (hstart' m hm).choose_spec hxm (by omega) hM'
        have hlive : x ∈ (chain.states (chain.windowStart q m' + 1)).live 0 := by
          have hxA : x ∈ (chain.states
              (chain.windowStart q m' + 1)).live (q + 1) := by
            rw [windowDrain, Finset.mem_sdiff] at hxm'
            exact hxm'.1
          exact (chain.states (chain.windowStart q m' + 1)).live_subset_root
            (by omega : q + 1 ≤ N) hxA
        exact hdead hlive
      intro m hm m' hm' hne
      rcases Nat.lt_or_ge m m' with h | h
      · exact key m hm m' hm' h
      · exact (key m' hm' m hm (by omega)).symm
    -- assemble the volume bound
    have hlower : ∀ m ∈ TS,
        2 ^ t (q + 1) ≤
          2 * overheadBound ^ (q + 1) * (chain.windowDrain q m).card := by
      intro m hm
      exact chain.window_drain_card hroot hqN (hTS_T m hm).1
        (hTS_T m hm).2 (hstart' m hm).choose_spec
    calc TS.card * 2 ^ t (q + 1)
        = TS.card • 2 ^ t (q + 1) := (smul_eq_mul _ _).symm
      _ ≤ ∑ m ∈ TS, 2 * overheadBound ^ (q + 1) *
            (chain.windowDrain q m).card :=
          Finset.card_nsmul_le_sum _ _ _ hlower
      _ = 2 * overheadBound ^ (q + 1) *
            ∑ m ∈ TS, (chain.windowDrain q m).card := by
          rw [Finset.mul_sum]
      _ = 2 * overheadBound ^ (q + 1) *
            (TS.biUnion (chain.windowDrain q)).card := by
          rw [Finset.card_biUnion
            (fun m hm m' hm' hne => hdisj m hm m' hm' hne)]
      _ ≤ 2 * overheadBound ^ (q + 1) * SBad.card := by
          apply Nat.mul_le_mul_left
          apply Finset.card_le_card
          exact Finset.biUnion_subset.mpr hdrainS
      _ ≤ 2 * overheadBound ^ (q + 1) * VS := by
          apply Nat.mul_le_mul_left
          exact Finset.card_biUnion_le.trans hS
  exact ⟨TS.card, by omega, hTSvol⟩

/-- Antitone transport for the target exponents. -/
lemma target_antitone (hmono : ∀ r < N, t (r + 1) ≤ t r)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N) : t b ≤ t a := by
  induction hab with
  | refl => exact le_rfl
  | @step b' hab ih =>
      exact le_trans (hmono b' (by omega)) (ih (by omega))

/-- The version-count bound: the number of steps rebuilding the levels above
`s` is at most `(s+1)·(CL + 1)` plus an S-charged remainder controlled by the
total small-event volume, all at the multiplicative scale `2^(t (s+1))`. -/
theorem rebuildSteps_card_mul_le
    (hroot : ∀ m' ≤ M, 2 ^ t 0 ≤ 2 * ((chain.states m').live 0).card)
    (hmono : ∀ r < N, t (r + 1) ≤ t r) (hOB : 1 ≤ overheadBound)
    {s : ℕ} (hs : s < N) (isL : ℕ → Bool) {CL VS : ℕ}
    (hL : ((Finset.range M).filter fun a => isL a = true).card ≤ CL)
    (hS : ∑ a ∈ (Finset.range M).filter (fun a => isL a = false),
        (chain.bads a).card ≤ VS) :
    (chain.rebuildSteps s).card * 2 ^ t (s + 1) ≤
      (s + 1) * ((CL + 1) * 2 ^ t (s + 1) +
        2 * overheadBound ^ (s + 1) * VS) := by
  classical
  have h : ∀ q : ℕ, ∃ SC : ℕ,
      (q < s + 1 → (chain.edgeSteps q).card ≤ CL + 1 + SC) ∧
      (q < s + 1 → SC * 2 ^ t (q + 1) ≤
        2 * overheadBound ^ (q + 1) * VS) := by
    intro q
    by_cases hq : q < s + 1
    · obtain ⟨SC, h1, h2⟩ := chain.edgeSteps_card_le_of_charges hroot
        (show q < N by omega) isL hL hS
      exact ⟨SC, fun _ => h1, fun _ => h2⟩
    · exact ⟨0, fun h' => absurd h' hq, fun h' => absurd h' hq⟩
  choose SC hSC1 hSC2 using h
  calc (chain.rebuildSteps s).card * 2 ^ t (s + 1)
      ≤ (∑ q ∈ Finset.range (s + 1), (chain.edgeSteps q).card) *
          2 ^ t (s + 1) :=
        Nat.mul_le_mul_right _ (chain.rebuildSteps_card_le_sum s)
    _ ≤ (∑ q ∈ Finset.range (s + 1), (CL + 1 + SC q)) * 2 ^ t (s + 1) := by
        apply Nat.mul_le_mul_right
        apply Finset.sum_le_sum
        intro q hq
        exact hSC1 q (Finset.mem_range.mp hq)
    _ = ∑ q ∈ Finset.range (s + 1),
          ((CL + 1) * 2 ^ t (s + 1) + SC q * 2 ^ t (s + 1)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q _
        ring
    _ ≤ ∑ q ∈ Finset.range (s + 1),
          ((CL + 1) * 2 ^ t (s + 1) +
            2 * overheadBound ^ (s + 1) * VS) := by
        apply Finset.sum_le_sum
        intro q hq
        have hq' := Finset.mem_range.mp hq
        have hts : t (s + 1) ≤ t (q + 1) :=
          target_antitone hmono
            (by omega : q + 1 ≤ s + 1) (by omega : s + 1 ≤ N)
        have h1 : SC q * 2 ^ t (s + 1) ≤ SC q * 2 ^ t (q + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hts)
        have h2 := hSC2 q hq'
        have h3 : 2 * overheadBound ^ (q + 1) * VS ≤
            2 * overheadBound ^ (s + 1) * VS := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right hOB (by omega)
        omega
    _ = (s + 1) * ((CL + 1) * 2 ^ t (s + 1) +
          2 * overheadBound ^ (s + 1) * VS) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end EdgeCount

end RestrictedRunChain

end Kolmogorov
