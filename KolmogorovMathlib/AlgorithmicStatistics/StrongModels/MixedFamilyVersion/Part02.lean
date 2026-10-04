import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MixedFamilyRun
import KolmogorovMathlib.Restricted.FamilyCurve
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MixedFamilyVersion.Part01
import KolmogorovMathlib.Restricted.FamilyCurve.RunChain
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredVocabulary
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredRun
import KolmogorovMathlib.Restricted.FamilyCurve.RunBounds

/-!
# Counting the events of a mixed run

The estimates that keep the mixed run of `Part01` within its budget.

`anchoredChangeTraceAgainst_eq_count` identifies the change trace with the change count and
model list, `anchoredListChangeCount_le_filter_card` bounds the changes up to a step by the
number of light edges, and `anchoredModelListAt_eq_of_mstar_le` shows the model list
stabilises, so `anchoredVersionDecoderAgainst_terminal` returns the terminal `𝒢` model at a
bounded version ordinal.

`mixedLargeEventCount_le` and `mixedSmallEventDecodedVolume_le` are the two halves of the
event budget for the sampled bad-code stream, and
`restrictedAnchoredEventChain_bads_subset` and
`restrictedAnchoredEventChain_root_live_card_ge` keep the live set large.  The conclusion is
`exists_restrictedAnchoredEventChain_with_count_against`: for a curve grid on `n` with
`N = ⌊√(n / (log₂ n + 1))⌋ + 1` samples the mixed event chain exists with the required count.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

/-- The change trace of the anchored decoder matches the change count and model list. -/
private lemma anchoredChangeTraceAgainst_eq_count
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (T : ℕ) (codes : ℕ → BitString)
    (hfold : ∀ m, restrictedAnchoredEventRun 𝒢 grid
      (restrictedAnchoredBadStream c ℬ grid T) m = Part.some (codes m))
    (s m : ℕ)
    (hm : m ≤ (restrictedAnchoredBadStream c ℬ grid T).length) :
    anchoredChangeTraceAgainst 𝒢 ℬ c
        (restrictedCurveGridCode grid)
        (𝒢.overhead (restrictedAnchoredAmbient n)) s m =
      Part.some (anchoredListChangeCount s codes m,
        anchoredModelListAt s (codes m)) := by
  induction m with
  | zero =>
      rw [anchoredChangeTraceAgainst,
        anchoredDecoderTraceAgainst_replay
          𝒢 ℬ c grid hN T 0 (codes 0)
          (by omega) (hfold 0),
        Part.map_some]
      rfl
  | succ m ih =>
      rw [anchoredChangeTraceAgainst, ih (by omega),
        Part.bind_some,
        anchoredDecoderTraceAgainst_replay
          𝒢 ℬ c grid hN T (m + 1) (codes (m + 1))
          (by omega) (hfold (m + 1)),
        Part.map_some]
      by_cases hEq :
          anchoredModelListAt s (codes (m + 1)) =
            anchoredModelListAt s (codes m)
      · rw [ite_eq_left hEq]
        rw [show anchoredListChangeCount s codes (m + 1) =
            anchoredListChangeCount s codes m by
              rw [anchoredListChangeCount, ite_eq_left hEq],
          hEq]
      · rw [ite_eq_right hEq]
        rw [show anchoredListChangeCount s codes (m + 1) =
            anchoredListChangeCount s codes m + 1 by
              rw [anchoredListChangeCount, ite_eq_right hEq]]

/-- The change count up to step `m` is bounded by the number of edges with weight `≤ s`. -/
private lemma anchoredListChangeCount_le_filter_card
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (T : ℕ)
    (chain : RestrictedAnchoredChain 𝒢 grid
      (restrictedAnchoredBadStream c ℬ grid T).length)
    (codes : ℕ → BitString)
    (hdec : ∀ m, DecodesToRestrictedSampledRunState
      (codes m) (chain.states m))
    (s : ℕ) (hs : s ≤ N) (m : ℕ)
    (hm : m ≤ (restrictedAnchoredBadStream c ℬ grid T).length) :
    anchoredListChangeCount s codes m ≤
      ((Finset.range m).filter
        (fun a => chain.edges a ≤ s)).card := by
  induction m with
  | zero => simp [anchoredListChangeCount]
  | succ m ih =>
      have hstep := ih (by omega)
      have hsub :
          (Finset.range m).filter
              (fun a => chain.edges a ≤ s) ⊆
            (Finset.range (m + 1)).filter
              (fun a => chain.edges a ≤ s) :=
        Finset.filter_subset_filter _
          (fun x hx => Finset.mem_range.mpr
            (Nat.lt_succ_of_lt (Finset.mem_range.mp hx)))
      by_cases hEq :
          anchoredModelListAt s (codes (m + 1)) =
            anchoredModelListAt s (codes m)
      · rw [anchoredListChangeCount, ite_eq_left hEq]
        exact hstep.trans (Finset.card_le_card hsub)
      · rw [anchoredListChangeCount, ite_eq_right hEq]
        have hedge : chain.edges m ≤ s := by
          by_contra hgt
          have hpres :=
            ((chain.spec m (by omega)).2.2.1
              (s + 1) (by omega)).1
          have h1 :=
            anchoredModelListAt_eq (hdec m) s hs
          have h2 :=
            anchoredModelListAt_eq (hdec (m + 1)) s hs
          rw [h1, h2, hpres] at hEq
          exact hEq rfl
        have hmem : m ∈
            (Finset.range (m + 1)).filter
              (fun a => chain.edges a ≤ s) :=
          Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by omega), hedge⟩
        have hnot : m ∉
            (Finset.range m).filter
              (fun a => chain.edges a ≤ s) := by
          intro hmm
          exact absurd
            (Finset.mem_range.mp (Finset.mem_filter.mp hmm).1)
            (by omega)
        have hins :
            insert m ((Finset.range m).filter
              (fun a => chain.edges a ≤ s)) ⊆
            (Finset.range (m + 1)).filter
              (fun a => chain.edges a ≤ s) := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hmem
          · exact hsub hx'
        calc
          anchoredListChangeCount s codes m + 1
              ≤ ((Finset.range m).filter
                  (fun a => chain.edges a ≤ s)).card + 1 := by
                omega
          _ = (insert m ((Finset.range m).filter
                  (fun a => chain.edges a ≤ s))).card :=
                (Finset.card_insert_of_notMem hnot).symm
          _ ≤ ((Finset.range (m + 1)).filter
                  (fun a => chain.edges a ≤ s)).card :=
                Finset.card_le_card hins

/-- The model list at level `s` remains constant for all steps after `mstar`. -/
private lemma anchoredModelListAt_eq_of_mstar_le
    (s : ℕ) (codes : ℕ → BitString) (v mstar M : ℕ)
    (hcntstar : anchoredListChangeCount s codes mstar = v)
    (hmax : ∀ m, m ≤ M → anchoredListChangeCount s codes m ≤ v)
    (m : ℕ) (hm : mstar ≤ m) (hmM : m ≤ M) :
    anchoredModelListAt s (codes m) =
      anchoredModelListAt s (codes mstar) := by
  induction hm with
  | refl => rfl
  | @step m' hm' ih =>
      have hm'M : m' ≤ M := by omega
      have hcm' :
          anchoredListChangeCount s codes m' = v := by
        have h1 : v ≤
            anchoredListChangeCount s codes m' := by
          rw [← hcntstar]
          exact anchoredListChangeCount_mono s codes hm'
        have h2 :
            anchoredListChangeCount s codes m' ≤ v :=
          hmax m' hm'M
        omega
      have hcm'1 :
          anchoredListChangeCount s codes (m' + 1) = v := by
        have h1 : v ≤
            anchoredListChangeCount s codes (m' + 1) := by
          rw [← hcm']
          exact anchoredListChangeCount_succ_le s codes m'
        have h2 :
            anchoredListChangeCount s codes (m' + 1) ≤ v :=
          hmax (m' + 1) hmM
        omega
      have hEq :=
        (anchoredListChangeCount_succ_eq_iff s codes m').mp
          (by omega)
      exact hEq.trans (ih hm'M)

/-- The mixed decoder returns the terminal `𝒢` model at a version ordinal
bounded by the rebuild count of the `𝒢` chain driven by `ℬ` events. -/
lemma anchoredVersionDecoderAgainst_terminal
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (T : ℕ)
    (chain : RestrictedRunChain 𝒢 (N + 1)
      (n + logSlack 8 n)
      (2 * 𝒢.overhead (n + logSlack 8 n))
      (restrictedAnchoredTarget (n + logSlack 8 n)
        (sqrtSlack 8 n) grid)
      (restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) ℬ.toPre N
        (sqrtSlack 8 n) T).length)
    (codes : ℕ → BitString)
    (hfold : ∀ m,
      (restrictedEffectiveAnchoredInitialState 𝒢
          (n + logSlack 8 n) (sqrtSlack 8 n) grid).bind
        (fun st0 => restrictedEventPrefixRun 𝒢
          (𝒢.overhead (n + logSlack 8 n))
          (restrictedEffectiveAnchoredSizes
            (n + logSlack 8 n) (sqrtSlack 8 n) grid) st0
          (restrictedSampledBadCodeStream c
            (restrictedCurveGridCode grid) ℬ.toPre N
            (sqrtSlack 8 n) T) m) = Part.some (codes m) ∧
      DecodesToRestrictedSampledRunState
        (codes m) (chain.states m))
    (s : ℕ) (hs : s ≤ N)
    (hS : ((chain.states
      (restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) ℬ.toPre N
        (sqrtSlack 8 n) T).length).B (s + 1)).Nonempty) :
    ∃ v, v ≤ (chain.rebuildSteps s).card ∧
      anchoredVersionDecoderAgainst 𝒢 ℬ c
        (listCode [restrictedCurveGridCode grid,
          Nat.bits (𝒢.overhead (n + logSlack 8 n)),
          Nat.bits s, Nat.bits v]) =
        Part.some ((codedUniformOn ((chain.states
          (restrictedSampledBadCodeStream c
            (restrictedCurveGridCode grid) ℬ.toPre N
            (sqrtSlack 8 n) T).length).B (s + 1)) hS).code) := by
  classical
  have htrace : ∀ m,
      m ≤ (restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) ℬ.toPre N
        (sqrtSlack 8 n) T).length →
      anchoredChangeTraceAgainst 𝒢 ℬ c
          (restrictedCurveGridCode grid)
          (𝒢.overhead (n + logSlack 8 n)) s m =
        Part.some (anchoredListChangeCount s codes m,
          anchoredModelListAt s (codes m)) :=
    fun m hm => anchoredChangeTraceAgainst_eq_count
      𝒢 ℬ c grid hN T codes (fun m' => (hfold m').1) s m hm
  have hcount_le : ∀ m,
      m ≤ (restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) ℬ.toPre N
        (sqrtSlack 8 n) T).length →
      anchoredListChangeCount s codes m ≤
        ((Finset.range m).filter
          (fun a => chain.edges a ≤ s)).card :=
    fun m hm => anchoredListChangeCount_le_filter_card
      𝒢 ℬ c grid T chain codes (fun m' => (hfold m').2) s hs m hm
  set M := (restrictedSampledBadCodeStream c
    (restrictedCurveGridCode grid) ℬ.toPre N
    (sqrtSlack 8 n) T).length
  set v := anchoredListChangeCount s codes M with hv
  have hvexists :
      ∃ m, v ≤ anchoredListChangeCount s codes m :=
    ⟨M, le_rfl⟩
  set mstar := Nat.find hvexists with hmstar
  have hmstarM : mstar ≤ M :=
    Nat.find_min' hvexists le_rfl
  have hcntstar :
      anchoredListChangeCount s codes mstar = v := by
    have h1 : v ≤ anchoredListChangeCount s codes mstar :=
      Nat.find_spec hvexists
    have h2 : anchoredListChangeCount s codes mstar ≤ v :=
      anchoredListChangeCount_mono s codes hmstarM
    omega
  have hbelow : ∀ m' < mstar,
      anchoredListChangeCount s codes m' < v := by
    intro m' hm'
    have h := Nat.find_min hvexists hm'
    omega
  have hconst : ∀ m, mstar ≤ m → m ≤ M →
      anchoredModelListAt s (codes m) =
        anchoredModelListAt s (codes mstar) :=
    anchoredModelListAt_eq_of_mstar_le s codes v mstar M
      hcntstar (fun m' hm' => anchoredListChangeCount_mono s codes hm')
  have hrfind : Nat.rfind (fun m =>
      (anchoredChangeTraceAgainst 𝒢 ℬ c
        (restrictedCurveGridCode grid)
        (𝒢.overhead (n + logSlack 8 n)) s m).map
          (fun p => decide (v ≤ p.1))) =
      Part.some mstar := by
    let p : ℕ →. Bool := fun m =>
      (anchoredChangeTraceAgainst 𝒢 ℬ c
        (restrictedCurveGridCode grid)
        (𝒢.overhead (n + logSlack 8 n)) s m).map
          (fun p => decide (v ≤ p.1))
    change Nat.rfind p = Part.some mstar
    refine Part.eq_some_iff.mpr (Nat.mem_rfind.mpr ⟨?_, ?_⟩)
    · dsimp [p]
      rw [htrace mstar hmstarM, Part.map_some]
      have h_dec : decide (v ≤ (anchoredListChangeCount s codes mstar, 
          anchoredModelListAt s (codes mstar)).1) = true := by
        simp only
        rw [hcntstar]
        exact decide_eq_true le_rfl
      exact Part.mem_some_iff.mpr h_dec.symm
    · intro q hq
      dsimp [p]
      rw [htrace q (by omega), Part.map_some]
      have h := hbelow q hq
      have h_dec : decide (v ≤ (anchoredListChangeCount s codes q, 
          anchoredModelListAt s (codes q)).1) = false := by
        simp only
        exact decide_eq_false (by omega)
      exact Part.mem_some_iff.mpr h_dec.symm
  refine ⟨v, ?_, ?_⟩
  · exact (hcount_le _ le_rfl).trans (le_of_eq rfl)
  · rw [anchoredVersionDecoderAgainst_eval,
      bitsToNat_bits, bitsToNat_bits, bitsToNat_bits,
      hrfind, Part.bind_some, htrace mstar hmstarM,
      Part.map_some]
    congr 1
    have hlist : anchoredModelListAt s (codes M) =
        anchoredModelListAt s (codes mstar) :=
      hconst M hmstarM le_rfl
    rw [← hlist]
    exact uniformCodeOfList_anchoredModelListAt_eq
      (hfold M).2 s hs hS

/-- Bound on the number of large events in the sampled bad code stream up to sample index `s`. -/
lemma mixedLargeEventCount_le
    (ℬ : DescriptionFamily) (c : Nat.Partrec.Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (Δ T s : ℕ) (_hs : s ≤ N) :
  let events := restrictedSampledBadCodeStream c
    (restrictedCurveGridCode grid) ℬ.toPre N Δ T
  let isL := fun m => decide (∃ l, l < N ∧
    grid.i (l + 1) ≤ grid.i s ∧
    events.getD m [] ∈ familyStageModelCodesList c
      (grid.i (l + 1)) ℬ.toPre (grid.j l - (Δ + 1)) T)
  ((Finset.range events.length).filter
    fun a => isL a = true).card ≤ N * 2 ^ (grid.i s + 1) := by
  intro events isL
  set M := events.length
  have hgetD_inj : ∀ {a a' : ℕ}, a < M → a' < M →
      events.getD a [] = events.getD a' [] → a = a' := by
    intro a a' ha ha' hEq
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ ha'] at hEq
    have hnodup := restrictedSampledBadCodeStream_nodup c
      (restrictedCurveGridCode grid) ℬ.toPre N Δ T
    have hinj := List.nodup_iff_injective_get.mp hnodup
    have h2 := hinj (show events.get ⟨a, ha⟩ = events.get ⟨a', ha'⟩ by simpa using hEq)
    simpa using h2
  have hmapsTo : ∀ a ∈ (Finset.range M).filter (fun a => isL a = true),
      events.getD a [] ∈ (((List.range N).filter (fun l =>
        grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
          (familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
            (grid.j l - (Δ + 1)) T).toFinset)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    have hprop : ∃ l, l < N ∧ grid.i (l + 1) ≤ grid.i s ∧
        events.getD a [] ∈ familyStageModelCodesList c (grid.i (l + 1))
          ℬ.toPre (grid.j l - (Δ + 1)) T := of_decide_eq_true ha.2
    obtain ⟨l, hlN, hle, hmem⟩ := hprop
    refine Finset.mem_biUnion.mpr ⟨l, ?_, List.mem_toFinset.mpr hmem⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_range.mpr hlN, by simpa using hle⟩
  have hinj : Set.InjOn (fun a => events.getD a [])
      ↑((Finset.range M).filter fun a => isL a = true) := by
    intro a ha a' ha' hEq
    have ha1 : a ∈ (Finset.range M).filter fun a => isL a = true := ha
    have ha2 : a' ∈ (Finset.range M).filter fun a => isL a = true := ha'
    rw [Finset.mem_filter, Finset.mem_range] at ha1 ha2
    exact hgetD_inj ha1.1 ha2.1 hEq
  calc ((Finset.range M).filter fun a => isL a = true).card
      ≤ (((List.range N).filter (fun l =>
          grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
            (familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
              (grid.j l - (Δ + 1)) T).toFinset)).card :=
        Finset.card_le_card_of_injOn _ hmapsTo hinj
    _ ≤ ∑ l ∈ ((List.range N).filter (fun l =>
          grid.i (l + 1) ≤ grid.i s)).toFinset,
          (familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
            (grid.j l - (Δ + 1)) T).toFinset.card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ ((List.range N).filter (fun l =>
          grid.i (l + 1) ≤ grid.i s)).toFinset, 2 ^ (grid.i s + 1) := by
        apply Finset.sum_le_sum
        intro l hl
        rw [List.mem_toFinset, List.mem_filter] at hl
        have hle : grid.i (l + 1) ≤ grid.i s := by
          have := hl.2
          simpa using this
        calc (familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
              (grid.j l - (Δ + 1)) T).toFinset.card
            ≤ (familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
                (grid.j l - (Δ + 1)) T).length := List.toFinset_card_le _
          _ ≤ 2 ^ (grid.i (l + 1) + 1) :=
              familyStageModelCodesList_length_le c _ ℬ.toPre _ T
          _ ≤ 2 ^ (grid.i s + 1) :=
              Nat.pow_le_pow_right (by omega) (by omega)
    _ = (((List.range N).filter (fun l =>
          grid.i (l + 1) ≤ grid.i s)).toFinset).card *
          2 ^ (grid.i s + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ N * 2 ^ (grid.i s + 1) := by
        apply Nat.mul_le_mul_right
        calc (((List.range N).filter (fun l =>
              grid.i (l + 1) ≤ grid.i s)).toFinset).card
            ≤ ((List.range N).filter (fun l =>
                grid.i (l + 1) ≤ grid.i s)).length :=
              List.toFinset_card_le _
          _ ≤ (List.range N).length := List.length_filter_le _ _
          _ = N := List.length_range

/-- Bound on the decoded volume contributed by the small events of the sampled bad code stream
up to sample index `s`, for a strictly decreasing target curve. -/
lemma mixedSmallEventDecodedVolume_le
    (ℬ : DescriptionFamily) (c : Nat.Partrec.Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hstrict : ∀ i < k, target (i + 1) < target i)
    (Δ T s : ℕ) (hs : s ≤ N) :
  let events := restrictedSampledBadCodeStream c
    (restrictedCurveGridCode grid) ℬ.toPre N Δ T
  let isL := fun m => decide (∃ l, l < N ∧
    grid.i (l + 1) ≤ grid.i s ∧
    events.getD m [] ∈ familyStageModelCodesList c
      (grid.i (l + 1)) ℬ.toPre (grid.j l - (Δ + 1)) T)
  ∑ a ∈ (Finset.range events.length).filter
      (fun a => isL a = false),
      (decodeCoverCodeList (events.getD a [])).toFinset.card ≤
    N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) +
      Δ + (n / N + 1) + 4) := by
  intro events isL
  set M := events.length
  have hgetD_inj : ∀ {a a' : ℕ}, a < M → a' < M →
      events.getD a [] = events.getD a' [] → a = a' := by
    intro a a' ha ha' hEq
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ ha'] at hEq
    have hnodup := restrictedSampledBadCodeStream_nodup c
      (restrictedCurveGridCode grid) ℬ.toPre N Δ T
    have hinj := List.nodup_iff_injective_get.mp hnodup
    have h2 := hinj (show events.get ⟨a, ha⟩ = events.get ⟨a', ha'⟩ by simpa using hEq)
    simpa using h2
  have hinj2 : Set.InjOn (fun a => events.getD a [])
      ↑((Finset.range M).filter (fun a => isL a = false)) := by
    intro a ha a' ha' hEq
    have ha1 : a ∈ (Finset.range M).filter (fun a => isL a = false) := ha
    have ha2 : a' ∈ (Finset.range M).filter (fun a => isL a = false) := ha'
    rw [Finset.mem_filter, Finset.mem_range] at ha1 ha2
    exact hgetD_inj ha1.1 ha2.1 hEq
  have hstep1 : ∑ a ∈ (Finset.range M).filter (fun a => isL a = false),
      (decodeCoverCodeList (events.getD a [])).toFinset.card =
      ∑ w ∈ ((Finset.range M).filter (fun a => isL a = false)).image
        (fun a => events.getD a []),
        (decodeCoverCodeList w).toFinset.card := by
    rw [Finset.sum_image hinj2]
  rw [hstep1]
  have himg : ((Finset.range M).filter (fun a => isL a = false)).image
      (fun a => events.getD a []) ⊆
      (((List.range N).filter (fun l =>
        ¬ grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
          (familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
            (grid.j l - (Δ + 1)) T).toFinset)) := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    rw [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨haM, hnotL⟩ := ha
    have hmem : events.getD a [] ∈ events := by
      rw [List.getD_eq_getElem _ _ haM]
      exact List.getElem_mem haM
    have hraw := restrictedSampledBadCodeStream_mem_raw c (restrictedCurveGridCode grid)
      ℬ.toPre N Δ T hmem
    rw [restrictedSampledBadCodesRaw, List.mem_flatMap] at hraw
    obtain ⟨l, hlrange, hlmem⟩ := hraw
    have hlN : l < N := List.mem_range.mp hlrange
    rw [decode_restrictedCurveGridCode_sample_eq grid
        (show l + 1 ≤ N by omega),
      decode_restrictedCurveGridCode_sample_eq grid
        (show l ≤ N by omega)] at hlmem
    have hgt : ¬ grid.i (l + 1) ≤ grid.i s := by
      intro hle
      have htrue : isL a = true :=
        decide_eq_true ⟨l, hlN, hle, hlmem⟩
      rw [hnotL] at htrue
      exact absurd htrue (by decide)
    refine Finset.mem_biUnion.mpr ⟨l, ?_, List.mem_toFinset.mpr hlmem⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_range.mpr hlN, by simpa using hgt⟩
  calc ∑ w ∈ ((Finset.range M).filter
        (fun a => isL a = false)).image (fun a => events.getD a []),
        (decodeCoverCodeList w).toFinset.card
      ≤ ∑ w ∈ (((List.range N).filter (fun l =>
          ¬ grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
            (familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
              (grid.j l - (Δ + 1)) T).toFinset)),
          (decodeCoverCodeList w).toFinset.card :=
        Finset.sum_le_sum_of_subset himg
    _ ≤ ∑ l ∈ ((List.range N).filter (fun l =>
          ¬ grid.i (l + 1) ≤ grid.i s)).toFinset,
          ∑ w ∈ (familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
            (grid.j l - (Δ + 1)) T).toFinset,
            (decodeCoverCodeList w).toFinset.card :=
        sum_biUnion_le' _ _ _
    _ ≤ ∑ _l ∈ ((List.range N).filter (fun l =>
          ¬ grid.i (l + 1) ≤ grid.i s)).toFinset,
          2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
        apply Finset.sum_le_sum
        intro l hl
        rw [List.mem_toFinset, List.mem_filter] at hl
        have hlN : l < N := List.mem_range.mp hl.1
        have hgt : grid.i s < grid.i (l + 1) := by
          have := hl.2
          simp at this
          omega
        calc ∑ w ∈ (familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
              (grid.j l - (Δ + 1)) T).toFinset,
              (decodeCoverCodeList w).toFinset.card
            ≤ ((familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
                (grid.j l - (Δ + 1)) T).map fun w =>
                  (decodeCoverCodeList w).toFinset.card).sum :=
              sum_toFinset_le_list_sum _ _
          _ ≤ 2 ^ (grid.i (l + 1) + 1) * 2 ^ (grid.j l - (Δ + 1)) :=
              familyStageModelCodesList_decoded_volume_le c _ ℬ.toPre _ T
          _ = 2 ^ (grid.i (l + 1) + 1 + (grid.j l - (Δ + 1))) :=
              (pow_add 2 _ _).symm
          _ ≤ 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ +
                (n / N + 1) + 4) :=
              Nat.pow_le_pow_right (by omega)
                (restrictedCurveGrid_sStage_exponent_le grid hstrict hs hlN hgt)
    _ = (((List.range N).filter (fun l =>
          ¬ grid.i (l + 1) ≤ grid.i s)).toFinset).card *
          2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ +
          (n / N + 1) + 4) := by
        apply Nat.mul_le_mul_right
        calc (((List.range N).filter (fun l =>
              ¬ grid.i (l + 1) ≤ grid.i s)).toFinset).card
            ≤ ((List.range N).filter (fun l =>
                ¬ grid.i (l + 1) ≤ grid.i s)).length :=
              List.toFinset_card_le _
          _ ≤ (List.range N).length := List.length_filter_le _ _
          _ = N := List.length_range

/-- The bad set of step `m` is contained in the union of all processed bad sets up to time `T+1`. -/
private lemma restrictedAnchoredEventChain_bads_subset
    (𝒢 ℬ : DescriptionFamily) (c : Nat.Partrec.Code)
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (T : ℕ)
    (chain : RestrictedAnchoredChain 𝒢 grid
      (restrictedAnchoredBadStream c ℬ grid T).length)
    (hbads : RestrictedAnchoredChainBads 𝒢 ℬ c grid T chain)
    (m : ℕ) (hm : m < (restrictedAnchoredBadStream c ℬ grid T).length) :
    chain.bads m ⊆
      restrictedAnchoredProcessedBadUnion c ℬ (restrictedAnchoredSlack n) grid (T + 1) := by
  intro x hx
  rw [hbads m, List.mem_toFinset] at hx
  rw [restrictedAnchoredProcessedBadUnion_eq_codes,
    restrictedAnchoredProcessedBadCodes_succ]
  refine (mem_restrictedDecodedBadCodesUnion_iff _ x).mpr
    ⟨(restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        ℬ.toPre N (sqrtSlack 8 n) T).getD m [], ?_, List.mem_toFinset.mpr hx⟩
  rw [List.getD_eq_getElem _ _ hm]
  exact List.getElem_mem hm

/-- Lower bound on the live set cardinality at level 0 across all steps `m`. -/
private lemma restrictedAnchoredEventChain_root_live_card_ge
    (𝒢 ℬ : DescriptionFamily) (c : Nat.Partrec.Code)
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n) (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) (T : ℕ)
    (chain : RestrictedAnchoredChain 𝒢 grid
      (restrictedAnchoredBadStream c ℬ grid T).length)
    (hbadsub : RestrictedAnchoredChainBadsProcessed 𝒢 ℬ c grid T chain)
    (hlive0 : (chain.states 0).live 0 = stringsOfLength (restrictedAnchoredAmbient n))
    (m : ℕ) (hm : m ≤ (restrictedAnchoredBadStream c ℬ grid T).length) :
    2 ^ restrictedAnchoredTarget (restrictedAnchoredAmbient n)
        (restrictedAnchoredSlack n) grid 0 ≤
      2 * ((chain.states m).live 0).card := by
  have hwin := chain.window_live_eq (Nat.zero_le m) hm
    (fun m' _ _ => Nat.zero_le _)
  rw [hwin, hlive0]
  simp only [restrictedAnchoredAmbient, restrictedAnchoredSlack]
  have hsub : (Finset.Ico 0 m).biUnion chain.bads ⊆
      restrictedAnchoredProcessedBadUnion c ℬ (sqrtSlack 8 n) grid (T + 1) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
    rw [Finset.mem_Ico] at ha
    exact hbadsub a (by omega) hxa
  have hcardsub := Finset.card_le_card hsub
  have hcube : (stringsOfLength (n + logSlack 8 n)).card =
      2 ^ (n + logSlack 8 n) := card_stringsOfLength _
  have hsdiff := Finset.card_le_card_sdiff_add_card
    (s := stringsOfLength (n + logSlack 8 n))
    (t := (Finset.Ico 0 m).biUnion chain.bads)
  have hUcard : 2 * (restrictedAnchoredProcessedBadUnion c ℬ (sqrtSlack 8 n) grid
      (T + 1)).card < 2 ^ (n + logSlack 8 n) := by
    calc 2 * (restrictedAnchoredProcessedBadUnion c ℬ (sqrtSlack 8 n) grid (T + 1)).card
        ≤ 2 * ((List.range N).map fun s' =>
            2 ^ (grid.i (s' + 1) + 1) *
              2 ^ (grid.j s' - ((sqrtSlack 8 n) + 1))).sum :=
          Nat.mul_le_mul_left 2
            (restrictedAnchoredProcessedBadUnion_card_le c ℬ (sqrtSlack 8 n) grid T)
      _ < 2 ^ (n + logSlack 8 n) :=
          restrictedCurveGrid_bad_volume_padding_half grid hN hkn htarget
            hstrict
  rw [restrictedAnchoredTarget_zero]
  omega

/-- For a curve grid on `n` with `N = ⌊√(n / (log₂ n + 1))⌋ + 1` sample points there is a
restricted run chain, together with codes for its states, that realises the anchored run
against the sampled bad code stream and whose bad sets are exactly the decoded cover lists. -/
theorem exists_restrictedAnchoredEventChain_with_count_against
    (𝒢 ℬ : DescriptionFamily) (c : Nat.Partrec.Code)
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n) (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) (T : ℕ) :
    ∃ (chain : RestrictedRunChain 𝒢 (N + 1) (n + logSlack 8 n)
        (2 * 𝒢.overhead (n + logSlack 8 n))
        (restrictedAnchoredTarget (n + logSlack 8 n) (sqrtSlack 8 n) grid)
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          ℬ.toPre N (sqrtSlack 8 n) T).length)
      (codes : ℕ → BitString),
      (∀ m,
        (restrictedEffectiveAnchoredInitialState 𝒢 (n + logSlack 8 n)
            (sqrtSlack 8 n) grid).bind
          (fun st0 => restrictedEventPrefixRun 𝒢
            (𝒢.overhead (n + logSlack 8 n))
            (restrictedEffectiveAnchoredSizes (n + logSlack 8 n)
              (sqrtSlack 8 n) grid) st0
            (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
              ℬ.toPre N (sqrtSlack 8 n) T) m) = Part.some (codes m) ∧
        DecodesToRestrictedSampledRunState (codes m) (chain.states m)) ∧
      (∀ m, chain.bads m = (decodeCoverCodeList
        ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          ℬ.toPre N (sqrtSlack 8 n) T).getD m [])).toFinset) ∧
      (chain.states 0).B 0 = stringsOfLength (n + logSlack 8 n) ∧
      (chain.states 0).live 0 = stringsOfLength (n + logSlack 8 n) ∧
      ∀ s ≤ N, (chain.rebuildSteps s).card ≤
        2 ^ (grid.i s + anchoredVersionExp 𝒢 n N) := by
  classical
  set Δ := sqrtSlack 8 n with hΔdef
  set gridCode := restrictedCurveGridCode grid with hgridCodeDef
  set events := restrictedSampledBadCodeStream c gridCode ℬ.toPre N Δ T
    with heventsDef
  set M := events.length with hMdef
  set OB := 2 * 𝒢.overhead (n + logSlack 8 n) with hOBdef
  have hnamb : n ≤ n + logSlack 8 n := Nat.le_add_right _ _
  obtain ⟨chain, codes, hfold, hbads, hB0, hlive0⟩ :=
    exists_restrictedAnchoredEventChain_against 𝒢 ℬ c (n + logSlack 8 n) Δ grid
      hnamb T
  refine ⟨chain, codes, hfold, hbads, hB0, hlive0, ?_⟩
  intro s hsN
  have hbadsub : ∀ m : ℕ, m < M → chain.bads m ⊆
      restrictedAnchoredProcessedBadUnion c ℬ Δ grid (T + 1) :=
    restrictedAnchoredEventChain_bads_subset 𝒢 ℬ c grid T chain hbads
  have hroot : ∀ m ≤ M, 2 ^ (restrictedAnchoredTarget (n + logSlack 8 n) Δ
      grid) 0 ≤ 2 * ((chain.states m).live 0).card :=
    restrictedAnchoredEventChain_root_live_card_ge 𝒢 ℬ c grid hN hkn htarget hstrict T
      chain hbadsub hlive0
  have hmono : ∀ r < N + 1,
      restrictedAnchoredTarget (n + logSlack 8 n) Δ grid (r + 1) ≤
        restrictedAnchoredTarget (n + logSlack 8 n) Δ grid r :=
    restrictedAnchoredTarget_mono _ _ grid hnamb
  have hOB1 : 1 ≤ OB := by
    have := 𝒢.overhead_pos (n + logSlack 8 n)
    omega
  set isL : ℕ → Bool := fun m => decide (∃ l, l < N ∧
    grid.i (l + 1) ≤ grid.i s ∧ events.getD m [] ∈
      familyStageModelCodesList c (grid.i (l + 1)) ℬ.toPre
        (grid.j l - (Δ + 1)) T) with hisL
  have hLcard : ((Finset.range M).filter fun a => isL a = true).card ≤
      N * 2 ^ (grid.i s + 1) :=
    mixedLargeEventCount_le ℬ c grid Δ T s hsN
  have hSsum : ∑ a ∈ (Finset.range M).filter (fun a => isL a = false),
      (chain.bads a).card ≤
      N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
    have hsumeq : ∑ a ∈ (Finset.range M).filter (fun a => isL a = false),
        (chain.bads a).card =
        ∑ a ∈ (Finset.range M).filter (fun a => isL a = false),
        (decodeCoverCodeList (events.getD a [])).toFinset.card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hbads x]
    rw [hsumeq]
    exact mixedSmallEventDecodedVolume_le ℬ c grid hstrict Δ T s hsN
  have hmain := chain.rebuildSteps_card_mul_le hroot hmono hOB1
    (show s < N + 1 by omega) isL hLcard hSsum
  rw [restrictedAnchoredTarget_succ] at hmain
  have hVSsplit : N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ +
      (n / N + 1) + 4) =
      N * 2 ^ (grid.i s + Δ + (n / N + 1) + 4) *
        2 ^ (grid.j s - (Δ + 1)) := by
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hVSsplit] at hmain
  have hfact : (s + 1) * ((N * 2 ^ (grid.i s + 1) + 1) *
      2 ^ (grid.j s - (Δ + 1)) +
      2 * OB ^ (s + 1) *
        (N * 2 ^ (grid.i s + Δ + (n / N + 1) + 4) *
          2 ^ (grid.j s - (Δ + 1)))) =
      ((s + 1) * (N * 2 ^ (grid.i s + 1) + 1 +
        2 * OB ^ (s + 1) *
          (N * 2 ^ (grid.i s + Δ + (n / N + 1) + 4)))) *
        2 ^ (grid.j s - (Δ + 1)) := by
    ring
  rw [hfact] at hmain
  have hcount := Nat.le_of_mul_le_mul_right hmain (pow_pos (by omega) _)
  have hNN : N + 1 ≤ 2 ^ (Nat.bits (N + 1)).length := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.lt_size_self (N + 1)).le
  have hOBsize : OB ≤ 2 ^ (Nat.bits OB).length := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.lt_size_self OB).le
  have harith := version_count_arith (I := grid.i s) (Δm := Δ)
    (mesh := n / N + 1) (LN := (Nat.bits (N + 1)).length)
    (Lob := (Nat.bits OB).length) (NN := N) (OB := OB) (s := s)
    hNN hOBsize hsN
  refine hcount.trans (harith.trans (Nat.pow_le_pow_right (by omega) ?_))
  have hexp : anchoredVersionExp 𝒢 n N =
      (N + 2) * (Nat.bits OB).length +
        2 * (Nat.bits (N + 1)).length + Δ + (n / N + 1) + 9 := rfl
  rw [hexp]
  have hmul : (N + 1) * (Nat.bits OB).length ≤
      (N + 2) * (Nat.bits OB).length :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end Kolmogorov
