import KolmogorovMathlib.Restricted.FamilyCurve.VersionPartrec2
import KolmogorovMathlib.Restricted.FamilyCurve.BundleCost
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain
import KolmogorovMathlib.Encoding.TuplesComplexity
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# Terminal evaluation of the version decoder

Given the event chain of the anchored run, the version decoder — fed the
encoded grid, the covering overhead, the scale, and the number of changes of
the decoded scale-`s` model list up to the terminal event — outputs exactly
the canonical uniform code of the terminal sampled model, and that ordinal is
bounded by the chain's rebuild count.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- The number of changes of the decoded scale-`s` model list along a code
trace. -/
def anchoredListChangeCount (s : ℕ) (codes : ℕ → BitString) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
      if anchoredModelListAt s (codes (m + 1)) =
          anchoredModelListAt s (codes m) then
        anchoredListChangeCount s codes m
      else
        anchoredListChangeCount s codes m + 1

/-- One step changes the count by at most one. -/
lemma anchoredListChangeCount_succ_le (s : ℕ) (codes : ℕ → BitString)
    (m : ℕ) :
    anchoredListChangeCount s codes m ≤
      anchoredListChangeCount s codes (m + 1) := by
  rw [anchoredListChangeCount]
  split <;> omega

/-- The change count is monotone in the event index. -/
lemma anchoredListChangeCount_mono (s : ℕ) (codes : ℕ → BitString)
    {m m' : ℕ} (h : m ≤ m') :
    anchoredListChangeCount s codes m ≤ anchoredListChangeCount s codes m' := by
  induction h with
  | refl => exact le_rfl
  | @step m'' _ ih =>
      exact ih.trans (anchoredListChangeCount_succ_le s codes m'')

/-- A stalled count step means the decoded list did not change. -/
lemma anchoredListChangeCount_succ_eq_iff (s : ℕ) (codes : ℕ → BitString)
    (m : ℕ) :
    anchoredListChangeCount s codes (m + 1) =
        anchoredListChangeCount s codes m ↔
      anchoredModelListAt s (codes (m + 1)) =
        anchoredModelListAt s (codes m) := by
  rw [anchoredListChangeCount]
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun hEq => absurd hEq (by omega), fun hEq => absurd hEq h⟩

/-- Evaluation of the decoder on an explicit four-component bundle. -/
lemma anchoredVersionDecoder_eval (𝒜 : DescriptionFamily) (c : Code)
    (g q0b sb vb : BitString) :
    anchoredVersionDecoder 𝒜 c (listCode [g, q0b, sb, vb]) =
      (Nat.rfind (fun m =>
        (anchoredChangeTrace 𝒜 c g (bitsToNat q0b) (bitsToNat sb) m).map
          (fun p => decide (bitsToNat vb ≤ p.1)))).bind
        (fun m =>
          (anchoredChangeTrace 𝒜 c g (bitsToNat q0b) (bitsToNat sb) m).map
            (fun p => uniformCodeOfList p.2)) := by
  unfold anchoredVersionDecoder
  rw [decodeListCode_listCode]
  rfl

/-- Every change of the decoded scale-`s` list happens at a rebuild edge at or below `s`, so
the change count up to event `m` is at most the number of such edges before `m`. -/
lemma anchoredListChangeCount_le_card_filter {s M : ℕ} (codes : ℕ → BitString) (edges : ℕ → ℕ)
    (hedge : ∀ a < M, anchoredModelListAt s (codes (a + 1)) ≠ anchoredModelListAt s (codes a) →
      edges a ≤ s) :
    ∀ m ≤ M, anchoredListChangeCount s codes m ≤
      ((Finset.range m).filter (fun a => edges a ≤ s)).card := by
  intro m
  induction m with
  | zero => intro _; simp [anchoredListChangeCount]
  | succ m ih =>
      intro hm
      have hstep := ih (by omega)
      have hsub : (Finset.range m).filter (fun a => edges a ≤ s) ⊆
          (Finset.range (m + 1)).filter (fun a => edges a ≤ s) :=
        Finset.filter_subset_filter _
          (fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hx)))
      by_cases hEq : anchoredModelListAt s (codes (m + 1)) = anchoredModelListAt s (codes m)
      · rw [anchoredListChangeCount, ite_eq_left hEq]
        exact hstep.trans (Finset.card_le_card hsub)
      · rw [anchoredListChangeCount, ite_eq_right hEq]
        have hmem : m ∈ (Finset.range (m + 1)).filter (fun a => edges a ≤ s) :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hedge m (by omega) hEq⟩
        have hnot : m ∉ (Finset.range m).filter (fun a => edges a ≤ s) := by
          intro hmm
          exact absurd (Finset.mem_range.mp (Finset.mem_filter.mp hmm).1) (by omega)
        have hins : insert m ((Finset.range m).filter (fun a => edges a ≤ s)) ⊆
            (Finset.range (m + 1)).filter (fun a => edges a ≤ s) := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hmem
          · exact hsub hx'
        calc anchoredListChangeCount s codes m + 1
            ≤ ((Finset.range m).filter (fun a => edges a ≤ s)).card + 1 := by omega
          _ = (insert m ((Finset.range m).filter (fun a => edges a ≤ s))).card :=
              (Finset.card_insert_of_notMem hnot).symm
          _ ≤ ((Finset.range (m + 1)).filter (fun a => edges a ≤ s)).card :=
              Finset.card_le_card hins

/-- Between two event indices whose change counts agree the decoded scale-`s` list is
constant. -/
lemma anchoredModelListAt_eq_of_count_le (s : ℕ) (codes : ℕ → BitString) {a b : ℕ}
    (hab : a ≤ b)
    (hcount : anchoredListChangeCount s codes b ≤ anchoredListChangeCount s codes a) :
    anchoredModelListAt s (codes b) = anchoredModelListAt s (codes a) := by
  revert hcount
  induction hab with
  | refl => intro _; rfl
  | @step b' hb' ih =>
      intro hcount
      have h1 := anchoredListChangeCount_mono s codes hb'
      have h2 := anchoredListChangeCount_succ_le s codes b'
      have h3 : anchoredListChangeCount s codes (b' + 1) ≤
          anchoredListChangeCount s codes a := hcount
      have hEq := (anchoredListChangeCount_succ_eq_iff s codes b').mp (by omega)
      exact hEq.trans (ih (by omega))

/-- The decoded change trace of the replayed anchored run agrees, at every event index inside
the sampled stream, with the change count and the scale-`s` model list of the folded state
codes. -/
lemma anchoredChangeTrace_eq_of_fold (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1) (T s : ℕ) (codes : ℕ → BitString)
    (hfold : ∀ m, (restrictedEffectiveAnchoredInitialState 𝒜 (n + logSlack 8 n)
          (sqrtSlack 8 n) grid).bind
        (fun st0 => restrictedEventPrefixRun 𝒜 (𝒜.overhead (n + logSlack 8 n))
          (restrictedEffectiveAnchoredSizes (n + logSlack 8 n) (sqrtSlack 8 n) grid) st0
          (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
            𝒜.toPre N (sqrtSlack 8 n) T) m) = Part.some (codes m)) :
    ∀ m ≤ (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T).length,
      anchoredChangeTrace 𝒜 c (restrictedCurveGridCode grid)
          (𝒜.overhead (n + logSlack 8 n)) s m =
        Part.some (anchoredListChangeCount s codes m, anchoredModelListAt s (codes m)) := by
  intro m
  induction m with
  | zero =>
      intro _
      rw [anchoredChangeTrace,
        anchoredDecoderTrace_replay 𝒜 c grid hN T 0 (codes 0) (by omega) (hfold 0),
        Part.map_some]
      rfl
  | succ m ih =>
      intro hm
      rw [anchoredChangeTrace, ih (by omega), Part.bind_some,
        anchoredDecoderTrace_replay 𝒜 c grid hN T (m + 1) (codes (m + 1))
          (by omega) (hfold (m + 1)),
        Part.map_some]
      by_cases hEq : anchoredModelListAt s (codes (m + 1)) = anchoredModelListAt s (codes m)
      · rw [ite_eq_left hEq]
        rw [show anchoredListChangeCount s codes (m + 1) =
            anchoredListChangeCount s codes m by
          rw [anchoredListChangeCount, ite_eq_left hEq], hEq]
      · rw [ite_eq_right hEq]
        rw [show anchoredListChangeCount s codes (m + 1) =
            anchoredListChangeCount s codes m + 1 by
          rw [anchoredListChangeCount, ite_eq_right hEq]]

/-- Terminal decoder evaluation over the anchored event chain: the change
count of the decoded scale-`s` list is bounded by the chain's rebuild count,
and the decoder at that ordinal returns the terminal model's canonical
uniform code. -/
lemma anchoredVersionDecoder_terminal
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (T : ℕ)
    (chain : RestrictedRunChain 𝒜 (N + 1) (n + logSlack 8 n)
        (2 * 𝒜.overhead (n + logSlack 8 n))
        (restrictedAnchoredTarget (n + logSlack 8 n) (sqrtSlack 8 n) grid)
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length)
    (codes : ℕ → BitString)
    (hfold : ∀ m,
      (restrictedEffectiveAnchoredInitialState 𝒜 (n + logSlack 8 n)
          (sqrtSlack 8 n) grid).bind
        (fun st0 => restrictedEventPrefixRun 𝒜
          (𝒜.overhead (n + logSlack 8 n))
          (restrictedEffectiveAnchoredSizes (n + logSlack 8 n)
            (sqrtSlack 8 n) grid) st0
          (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
            𝒜.toPre N (sqrtSlack 8 n) T) m) = Part.some (codes m) ∧
      DecodesToRestrictedSampledRunState (codes m) (chain.states m))
    (s : ℕ) (hs : s ≤ N)
    (hS : ((chain.states (restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
          T).length).B (s + 1)).Nonempty) :
    ∃ v, v ≤ (chain.rebuildSteps s).card ∧
      anchoredVersionDecoder 𝒜 c
        (listCode [restrictedCurveGridCode grid,
          Nat.bits (𝒜.overhead (n + logSlack 8 n)),
          Nat.bits s, Nat.bits v]) =
      Part.some ((codedUniformOn ((chain.states
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length).B (s + 1)) hS).code) := by
  classical
  have htrace := anchoredChangeTrace_eq_of_fold 𝒜 c grid hN T s codes (fun m => (hfold m).1)
  -- a change of the decoded list forces a rebuild at an edge at or below `s`
  have hedge : ∀ a < (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T).length,
      anchoredModelListAt s (codes (a + 1)) ≠ anchoredModelListAt s (codes a) →
      chain.edges a ≤ s := by
    intro a ha hne
    by_contra hgt
    have hpres := ((chain.spec a ha).2.2.1 (s + 1) (by omega)).1
    have h1 := anchoredModelListAt_eq (hfold a).2 s hs
    have h2 := anchoredModelListAt_eq (hfold (a + 1)).2 s hs
    rw [h1, h2, hpres] at hne
    exact hne rfl
  have hcount_le := anchoredListChangeCount_le_card_filter codes chain.edges hedge
  -- the terminal ordinal and its first attainment
  set v := anchoredListChangeCount s codes
    (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
      𝒜.toPre N (sqrtSlack 8 n) T).length with hv
  have hvexists : ∃ m, v ≤ anchoredListChangeCount s codes m :=
    ⟨(restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
      𝒜.toPre N (sqrtSlack 8 n) T).length, le_rfl⟩
  set mstar := Nat.find hvexists with hmstar
  have hmstarM : mstar ≤ (restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n) T).length :=
    Nat.find_min' hvexists le_rfl
  have hcntstar : anchoredListChangeCount s codes mstar = v := by
    have h1 : v ≤ anchoredListChangeCount s codes mstar := Nat.find_spec hvexists
    have h2 : anchoredListChangeCount s codes mstar ≤ v :=
      anchoredListChangeCount_mono s codes hmstarM
    omega
  have hbelow : ∀ m' < mstar, anchoredListChangeCount s codes m' < v := by
    intro m' hm'
    have := Nat.find_min hvexists hm'
    omega
  -- the μ-search stops exactly at the first attainment
  have hrfind : Nat.rfind (fun m =>
      (anchoredChangeTrace 𝒜 c (restrictedCurveGridCode grid)
        (𝒜.overhead (n + logSlack 8 n)) s m).map
        (fun p => decide (v ≤ p.1))) = Part.some mstar := by
    rw [Part.eq_some_iff]
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · rw [htrace mstar hmstarM, Part.map_some]
      refine Part.mem_some_iff.mpr (decide_eq_true ?_).symm
      omega
    · intro k hk
      rw [htrace k (by omega), Part.map_some]
      refine Part.mem_some_iff.mpr (decide_eq_false ?_).symm
      have := hbelow k hk
      omega
  refine ⟨v, ?_, ?_⟩
  · exact (hcount_le _ le_rfl).trans (le_of_eq rfl)
  · rw [anchoredVersionDecoder_eval, bitsToNat_bits, bitsToNat_bits,
      bitsToNat_bits, hrfind, Part.bind_some, htrace mstar hmstarM,
      Part.map_some]
    congr 1
    have hlist : anchoredModelListAt s (codes
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length) =
        anchoredModelListAt s (codes mstar) :=
      anchoredModelListAt_eq_of_count_le s codes hmstarM (le_of_eq (by omega))
    rw [← hlist]
    exact uniformCodeOfList_anchoredModelListAt_eq (hfold _).2 s hs hS

section FinalAssembly

/-- The version-coding theorem for a fixed decompressor code: every terminal
sampled model of the anchored run is describable by the encoded grid, the
covering overhead, the scale index, and a bounded version ordinal, so its set
complexity is the grid coordinate plus square-root slack plus the grid code's
complexity. -/
theorem restrictedAnchoredState_model_complexity
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead)
    (c : Code) (_hc : IsCodeFor c U) :
    ∃ c_ver : ℕ, ∀ {n k N : ℕ} {t : ℕ → ℕ}
      (grid : RestrictedCurveGrid n k N t)
      (_hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
      (_hkn : k ≤ n) (_ht0 : t 0 ≤ n)
      (_hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i)
      (T : ℕ) (output : BitString)
      (state : RestrictedSampledRunState 𝒜 (N + 1)
          (n + logSlack 8 n) (2 * 𝒜.overhead (n + logSlack 8 n))
          (restrictedAnchoredTarget (n + logSlack 8 n)
            (sqrtSlack 8 n) grid)),
      restrictedEffectiveAnchoredSampledRun 𝒜 c
          (n + logSlack 8 n) (sqrtSlack 8 n) grid (T + 1) =
            Part.some output →
      DecodesToRestrictedSampledRunState output state →
      ∀ s (_hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty),
        setComplexity U (state.B (s + 1)) hS ≤
          (grid.i s + sqrtSlack c_ver n +
            KPPlain U (restrictedCurveGridCode grid) : ENat) := by
  classical
  obtain ⟨c_F, hF⟩ := KPPlain_partrec_map_le U hU
    (anchoredVersionDecoder 𝒜 c) (anchoredVersionDecoder_partrec 𝒜 c)
  obtain ⟨c_L, hLc⟩ := KPPlain_listCode_le U hU
  obtain ⟨c_lg, hlg⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_P, hPex⟩ := anchoredVersionExp_le_sqrtSlack 𝒜 hPoly
  obtain ⟨c_over, hover⟩ := 𝒜.overhead_bits_le_logSlack hPoly
  refine ⟨c_P + 15 * c_over + 3 * c_lg + 5 * c_L + c_F +
    2 * Nat.size (c_P + 1) + 40, ?_⟩
  intro n k N t grid hN hkn ht0 hstrict T output state hrun hdec s hs hS
  obtain ⟨chain, codes, hfold, hbads, hB0, hlive0, hcount⟩ :=
    exists_restrictedAnchoredEventChain_with_count 𝒜 c grid hN hkn ht0
      hstrict T
  have hboundary := restrictedEffectiveAnchoredSampledRun_eq_eventPrefix
    𝒜 c (n + logSlack 8 n) (sqrtSlack 8 n) grid (le_refl T)
  have hout : output = codes ((restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
        T).length) := by
    rw [hboundary] at hrun
    exact Part.some_injective (hrun.symm.trans (hfold _).1)
  have hdec' : DecodesToRestrictedSampledRunState
      (codes ((restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
          T).length)) state := hout ▸ hdec
  have hBeq := decodesTo_eq_B_live hdec'
    ((hfold ((restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
        T).length)).2) (s := s + 1) (by omega)
  have hS' : ((chain.states ((restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
        T).length)).B (s + 1)).Nonempty := by
    rw [← hBeq.1]
    exact hS
  obtain ⟨v, hvle, heval⟩ := anchoredVersionDecoder_terminal 𝒜 c grid hN T
    chain codes hfold s hs hS'
  have hv2 : v ≤ 2 ^ (grid.i s + anchoredVersionExp 𝒜 n N) :=
    hvle.trans (hcount s hs)
  have hmem : (codedUniformOn ((chain.states
      ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T).length)).B (s + 1)) hS').code ∈
      anchoredVersionDecoder 𝒜 c
        (listCode [restrictedCurveGridCode grid,
          Nat.bits (𝒜.overhead (n + logSlack 8 n)),
          Nat.bits s, Nat.bits v]) := by
    rw [heval]
    exact Part.mem_some_iff.mpr rfl
  have hKP1 := hF _ _ hmem
  have hKP2 := hLc [restrictedCurveGridCode grid,
    Nat.bits (𝒜.overhead (n + logSlack 8 n)), Nat.bits s, Nat.bits v]
  have hq0c := KPPlain_le_selfDelimitedCost hlg (Nat.bits (𝒜.overhead (n + logSlack 8 n)))
  have hsc := KPPlain_le_selfDelimitedCost hlg (Nat.bits s)
  have hvc := KPPlain_le_selfDelimitedCost hlg (Nat.bits v)
  have hNat := decoderBundleFieldCost_le 𝒜 grid hN hkn hover (hPex n N hN)
    hs hv2 c_lg c_L c_F
  rw [setComplexity_eq_KPPlain_codedUniformOn U hS hS' hBeq.1]
  have hbound_calc := KPPlain_le_grid_add_bundleCost
    U (restrictedCurveGridCode grid) (Nat.bits (𝒜.overhead (n + logSlack 8 n)))
    (Nat.bits s) (Nat.bits v)
    ((codedUniformOn ((chain.states
      ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T).length)).B (s + 1)) hS').code)
    c_lg c_L c_F
    (grid.i s + sqrtSlack (c_P + 15 * c_over + 3 * c_lg + 5 * c_L + c_F +
      2 * Nat.size (c_P + 1) + 40) n)
    hKP1 (by simpa using hKP2) hq0c hsc hvc (by simpa [selfDelimitedCost] using hNat)
  refine hbound_calc.trans (le_of_eq ?_)
  push_cast
  ring

end FinalAssembly

end Kolmogorov
