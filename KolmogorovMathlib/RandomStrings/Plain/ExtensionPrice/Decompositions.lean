/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice.PastFuture

/-!
# Two volume decompositions

For blueprint node `key:decompositions`, the total extension volume is comparable to the
sum of its past count and an enriched future volume, at both the upper and lower scales.
The proofs combine marker replay and partial computable decoding with the information gaps
and extension-density estimates. The common loss constant feeds the structural volume
bounds in `SquareRoot`.
-/

namespace Kolmogorov.Milovanov

/-- Every output of an event emitted through tick `t` by a program of length at most `k` lies in
`stageOutputs B k t`. -/
private theorem event_output_mem_stageOutputs (B : Base) {t i k : ℕ} {p y : BitString}
    (hev : eventAt B t = some (t, i, p, y)) (hk : p.length ≤ k) : y ∈ stageOutputs B k t := by
  obtain ⟨_, _, hget⟩ := canonical_enumeration_spec_position B hev
  unfold stageOutputs stageOutputList
  rw [List.mem_toFinset, List.mem_eraseDups, List.mem_filterMap]
  exact ⟨(t, i, p, y), List.mem_of_getElem? hget, by simp [hk]⟩

/-- A short program for an output absent at the marker is emitted after the marker tick.
Blueprint node `key:decompositions`. -/
private lemma emission_tick_gt_marker_of_not_mem_stageOutputs
    (B : Base) (n k : ℕ) (p z : BitString) (hplen : p.length ≤ k)
    (hprod : produces B.V p [] z) (hnot : z ∉ stageOutputs B k (markerTick B n)) :
    ∀ t i y, eventAt B t = some (t, i, p, y) → markerTick B n < t := by
  intro t i y hev
  by_contra hle
  have hle : t ≤ markerTick B n := not_lt.mp hle
  apply hnot
  have hsound := canonical_enumeration_spec_sound B hev
  have hyz : z = y := Part.mem_unique hprod hsound.2
  have hmem := event_output_mem_stageOutputs B hev hplen
  rw [← hyz] at hmem
  exact (canonical_enumeration_spec_mono B k hle).1 hmem

/-- The logarithmic length bound for integer codes is at most the integer plus six. -/
private theorem integer_code_log_bound (h : ℕ) : 2 * Nat.clog 2 (h + 2) + 1 ≤ h + 6 := by
  have h1 : Nat.clog 2 (h + 2) ≤ (h + 5) / 2 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    have := Nat.mul_le_pow (by decide : 2 ≠ 1) ((h + 5) / 2)
    omega
  omega

/-- Encoding the padding amount before a program costs at most six extra bits.
Blueprint node `key:decompositions`. -/
lemma length_pairCode_bits_le (h : ℕ) (p : BitString) :
    (pairCode (bits h) p).length ≤ h + p.length + 6 := by
  have h1 := length_integerCode_le h
  have h2 := integer_code_log_bound h
  have h3 : (pairCode (bits h) p).length = (integerCode h).length + p.length := by
    simp only [integerCode, length_sd, literal_and_tuple_code_interface_pair]
  omega

/-- A fixed partial computable decoder costs a constant in plain complexity. -/
private theorem exists_plain_complexity_bound_of_partrec
    (B : Base) (g : BitString →. BitString) (hg : Partrec g) :
    ∃ c : ℕ, ∀ p z : BitString, z ∈ g p → plainK B.V z ≤ (p.length : ENat) + c := by
  let Dm : Map := fun pc ↦ g pc.1
  have hDm : isDecompressor Dm := hg.comp Computable.fst
  obtain ⟨c, hc⟩ := B.optimalV.2 Dm hDm
  refine ⟨c, fun p z hz ↦ ?_⟩
  have h1 : condK Dm z [] ≤ (p.length : ENat) := sInf_le ⟨p, hz, rfl⟩
  calc plainK B.V z = condK B.V z [] := rfl
    _ ≤ condK Dm z [] + c := hc z []
    _ ≤ (p.length : ENat) + c := by gcongr

/-- Every upper-scale extension outside the past has a short enriched description.
Blueprint node `key:decompositions`. -/
private lemma upper_future_extension_simple (B : Base) :
  ∃ cEx n₀ : ℕ, 32 ≤ n₀ ∧
    ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q →
      ∀ (s : BitString),
        Simple B.V (pairCode x s) (extensionScale q) →
        pairCode x s ∉ stageOutputs B (extensionScale q) candidate.2 →
        Simple B.V (pairCode (upperFutureBase B n candidate x q) s) (extensionScale q + cEx) := by
  obtain ⟨rep, hrepc, n₁, hn₁, hrep⟩ := exists_computable_marker_replay B
  obtain ⟨dec, hdec, hspec⟩ :=
    exists_upper_future_decoder B rep n₁ hrepc hn₁ hrep
  obtain ⟨c, hc⟩ := exists_plain_complexity_bound_of_partrec B dec hdec
  refine ⟨c + 6, n₁, hn₁, ?_⟩
  intro n candidate x q hK s hsimple hnot
  obtain ⟨hn, htow, hcand, hrange, -⟩ := hK
  subst hcand
  obtain ⟨p, hplen, hprod⟩ := (simple_iff_exists_program B.V _ _).mp hsimple
  have hlate :=
    emission_tick_gt_marker_of_not_mem_stageOutputs
      B n (extensionScale q) p _ hplen hprod hnot
  have hmem := hspec n hn htow q hrange x s p hprod hplen hlate
  have h := hc _ _ hmem
  have hlen : (pairCode (bits (extensionScale q - p.length)) p).length ≤ extensionScale q + 6 := by
    have := length_pairCode_bits_le (extensionScale q - p.length) p
    omega
  change plainK B.V _ ≤ ((extensionScale q + (c + 6) : ℕ) : ENat)
  calc plainK B.V _ ≤ ((pairCode (bits (extensionScale q - p.length)) p).length : ENat) + c := h
    _ ≤ ((extensionScale q + (c + 6) : ℕ) : ENat) := by
      have : (pairCode (bits (extensionScale q - p.length)) p).length + c ≤
          extensionScale q + (c + 6) := by omega
      exact_mod_cast this

/-- If every future extension has a relaxed description over `y`, the total count is
bounded by the past count plus the relaxed extension count of `y`. -/
private lemma strict_count_le_past_add_of_future_simple
    (B : Base) {n q δ : ℕ} {candidate : Candidate} {x y : BitString}
    (hvalid : validCandidate B n candidate = true)
    (hfuture : ∀ s, Simple B.V (pairCode x s) (extensionScale q) →
      pairCode x s ∉ stageOutputs B (extensionScale q) candidate.2 →
      Simple B.V (pairCode y s) (extensionScale q + δ)) :
    strictExtensionCount B q x ≤ pastExtensionCount B n candidate q x +
      extensionCount B q δ y := by
  have hsub : extensionSet B q 0 x ⊆
      (pastExtensionIndices B n candidate q x : Set BitString) ∪ extensionSet B q δ y := by
    intro s hs
    by_cases hpast : pairCode x s ∈ stageOutputs B (extensionScale q) candidate.2
    · exact Or.inl ((mem_past_extension_indices B n candidate q x s hvalid).mpr hpast)
    · exact Or.inr (hfuture s
        (by simpa only [extensionSet, add_zero, Set.mem_ofPred_eq] using hs) hpast)
  calc
    strictExtensionCount B q x ≤
        ((pastExtensionIndices B n candidate q x : Set BitString) ∪ extensionSet B q δ y).ncard :=
      Set.ncard_le_ncard hsub ((Finset.finite_toSet _).union (extension_set_finite B q δ y))
    _ ≤ (pastExtensionIndices B n candidate q x : Set BitString).ncard +
        (extensionSet B q δ y).ncard := Set.ncard_union_le _ _
    _ = pastExtensionCount B n candidate q x + extensionCount B q δ y := by
      rw [Set.ncard_coe_finset]
      rfl

/-- The upper total count is bounded by its past count and a fixed relaxation of the future.
Blueprint node `key:decompositions`. -/
private theorem upper_count_le_past_add_relaxed_future (B : Base) :
  ∃ cEx n₂ : ℕ, 32 ≤ n₂ ∧
    ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₂ n candidate x q →
      strictExtensionCount B q x ≤ pastExtensionCount B n candidate q x +
        extensionCount B q cEx (upperFutureBase B n candidate x q) := by
  obtain ⟨cEx, n₀, hn₀, hcore⟩ := upper_future_extension_simple B
  obtain ⟨n₃, _, hstab⟩ := last_program_stabilizes_short_descriptions B
  refine ⟨cEx, max n₀ n₃, le_trans hn₀ (le_max_left _ _), ?_⟩
  intro n candidate x q hK
  have hK₀ := KeyParameters.of_threshold_le B (le_max_left n₀ n₃) candidate x q hK
  have hn₃ : n₃ ≤ n := le_trans (le_max_right n₀ n₃) hK.1
  have hvalid : validCandidate B n candidate = true := by
    rw [hK.2.2.1]
    exact (hstab n hn₃).1
  exact strict_count_le_past_add_of_future_simple B hvalid (hcore n candidate x q hK₀)

/-- The past count never exceeds the total extension count, even for invalid candidates. -/
lemma past_extension_count_le_strict
    (B : Base) (n : ℕ) (candidate : Candidate) (h : ℕ) (y : BitString) :
    pastExtensionCount B n candidate h y ≤ strictExtensionCount B h y := by
  by_cases hc : validCandidate B n candidate = true
  · have h1 := past_extension_count_eq B n candidate h y hc
    rw [h1]
    have h2 : {s | pairCode y s ∈ stageOutputs B (extensionScale h) candidate.2} ⊆
        extensionSet B h 0 y := by
      intro s hs
      exact (canonical_enumeration_spec_union B (extensionScale h) (pairCode y s)).mpr
        ⟨candidate.2, hs⟩
    exact Set.ncard_le_ncard h2 (extension_set_finite B h 0 y)
  · simp [pastExtensionCount, pastExtensionIndices, hc]

/-- Projection bounds the upper future count by a fixed multiple of the total count.
Blueprint node `key:decompositions`. -/
private theorem upper_future_count_le_mul (B : Base) :
  ∃ cF n₁ : ℕ, 32 ≤ n₁ ∧
    ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₁ n candidate x q →
      strictExtensionCount B q (upperFutureBase B n candidate x q) ≤
        2 ^ cF * strictExtensionCount B q x := by
  obtain ⟨c0, cDen, cRel0, hd⟩ := extension_density_common B
  obtain ⟨cF, hcF⟩ := extension_volume_of_computable_projection B hd
    (fun z ↦ Part.some (decodeFirst (decodeFirst z)))
    (Computable.partrec (decodeFirst_computable.comp decodeFirst_computable))
  obtain ⟨n1, hn1, hgap⟩ := key_lemma_information_gaps B c0
  use cF, n1, hn1
  intro n candidate x q hK
  have hg := hgap n candidate x q hK
  have hF := hcF q (upperFutureBase B n candidate x q) x
    (by simp [upperFutureBase, proxyBase, decodeFirst_pairCode]) hg.plain
  exact_mod_cast hF

/-- Relaxing the upper future description length increases its count by a dyadic factor.
Blueprint node `key:decompositions`. -/
private theorem upper_relaxed_count_le_mul (B : Base) :
  ∃ cRel n₁ : ℕ, 32 ≤ n₁ ∧
    ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₁ n candidate x q →
      ∀ (δ : ℕ), extensionCount B q δ (upperFutureBase B n candidate x q) ≤
        2 ^ (cRel * (δ + 1)) * strictExtensionCount B q (upperFutureBase B n candidate x q) := by
  obtain ⟨c0r, cRel, hrel⟩ := extension_density_relaxed B
  obtain ⟨n1, hn1, hgap⟩ := key_lemma_information_gaps B c0r
  use cRel, n1
  constructor
  · exact hn1
  · intro n candidate x q hp δ
    have hg := (hgap n candidate x q hp).upper
    have hG := hrel q (upperFutureBase B n candidate x q) hg δ
    have h3 : ((2 : ℚ) ^ ((cRel : ℤ) * (δ + 1))) = ((2 ^ (cRel * (δ + 1)) : ℕ) : ℚ) := by
      push_cast
      rfl
    rw [h3] at hG
    exact_mod_cast hG

/-- Bounds for the past, future, and relaxed future combine into a dyadic comparison. -/
private lemma dyadic_bounds_of_past_future_bounds
    (cF e : ℕ) (p a f g : ℚ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hf : 0 ≤ f)
    (h1 : p ≤ a)
    (h2 : f ≤ (2 : ℚ) ^ cF * a)
    (h3 : a ≤ p + g)
    (h4 : g ≤ (2 : ℚ) ^ e * f) :
    (2 : ℚ) ^ (-(cF + 1 + e : ℤ)) * (p + f) ≤ a ∧ a ≤ (2 : ℚ) ^ (cF + 1 + e : ℤ) * (p + f) := by
  have h2e : (1 : ℚ) ≤ 2 ^ e := by apply one_le_pow₀ (by norm_num)
  have h2F : (1 : ℚ) ≤ 2 ^ cF := by apply one_le_pow₀ (by norm_num)
  have hT : (2 : ℚ) ^ (cF + 1 + e : ℤ) = 2 ^ cF * 2 * 2 ^ e := by
    rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    simp [zpow_natCast, mul_assoc]
  have hTpos : 0 < (2 : ℚ) ^ (cF + 1 + e : ℤ) := by positivity
  constructor
  · rw [zpow_neg, inv_mul_le_iff₀ hTpos, hT]
    have hsum : p + f ≤ (1 + 2 ^ cF) * a := by linarith
    have hdouble : (1 + 2 ^ cF) * a ≤ 2 ^ cF * 2 * a := by nlinarith
    have hscale : 2 ^ cF * 2 * a ≤ 2 ^ cF * 2 * 2 ^ e * a := by nlinarith
    linarith
  · rw [hT]
    have hsum : a ≤ p + 2 ^ e * f := by linarith
    have hrelax : p + 2 ^ e * f ≤ 2 ^ e * (p + f) := by nlinarith
    have hscale : 2 ^ e * (p + f) ≤ 2 ^ cF * 2 * 2 ^ e * (p + f) := by nlinarith
    linarith

/-- Four bounds on counts yield a two-sided dyadic comparison with the past-plus-future sum.
Blueprint node `key:decompositions`. -/
private lemma exists_dyadic_bounds_of_counts (cF cRel cEx : ℕ) :
  ∃ cDec : ℕ,
    ∀ (p a f g : ℕ),
      p ≤ a →
      f ≤ 2 ^ cF * a →
      a ≤ p + g →
      g ≤ 2 ^ (cRel * (cEx + 1)) * f →
      (2 : ℚ) ^ (-(cDec : ℤ)) * ((p : ℚ) + (f : ℚ)) ≤ a ∧
        (a : ℚ) ≤ (2 : ℚ) ^ (cDec : ℤ) * ((p : ℚ) + (f : ℚ)) := by
  use cF + 1 + cRel * (cEx + 1)
  intro p a f g hp hf ha hg
  have hp_cast : (p : ℚ) ≤ (a : ℚ) := by exact_mod_cast hp
  have hf_cast : (f : ℚ) ≤ (2 : ℚ) ^ cF * (a : ℚ) := by exact_mod_cast hf
  have ha_cast : (a : ℚ) ≤ (p : ℚ) + (g : ℚ) := by exact_mod_cast ha
  have hg_cast : (g : ℚ) ≤ (2 : ℚ) ^ (cRel * (cEx + 1)) * (f : ℚ) := by exact_mod_cast hg
  exact dyadic_bounds_of_past_future_bounds
    cF (cRel * (cEx + 1)) p a f g
    (by positivity) (by positivity) (by positivity)
    hp_cast hf_cast ha_cast hg_cast

/-- The upper total volume is comparable to its past count plus the enriched future volume.
Blueprint node `key:decompositions`. -/
theorem key_lemma_past_future_decompositions (B : Base) :
    ∃ cDec n₀ : ℕ, 32 ≤ n₀ ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → UpperVolumeDecomposition B cDec n candidate x q := by
  obtain ⟨cEx, nCore, hnCore, hcore⟩ := upper_count_le_past_add_relaxed_future B
  obtain ⟨cF, nFuture, _, hfuture⟩ := upper_future_count_le_mul B
  obtain ⟨cRel, nRelaxed, _, hrelaxed⟩ := upper_relaxed_count_le_mul B
  obtain ⟨cDec, harith⟩ := exists_dyadic_bounds_of_counts cF cRel cEx
  refine ⟨cDec, max nCore (max nFuture nRelaxed), hnCore.trans (le_max_left _ _), ?_⟩
  intro n candidate x q hp
  have hpCore := KeyParameters.of_threshold_le B (le_max_left _ _) candidate x q hp
  have hpFuture := KeyParameters.of_threshold_le B
    ((le_max_left _ _).trans (le_max_right _ _)) candidate x q hp
  have hpRelaxed := KeyParameters.of_threshold_le B
    ((le_max_right _ _).trans (le_max_right _ _)) candidate x q hp
  exact harith (pastExtensionCount B n candidate q x) (strictExtensionCount B q x)
    (strictExtensionCount B q (upperFutureBase B n candidate x q))
    (extensionCount B q cEx (upperFutureBase B n candidate x q))
    (past_extension_count_le_strict B n candidate q x)
    (hfuture n candidate x q hpFuture) (hcore n candidate x q hpCore)
    (hrelaxed n candidate x q hpRelaxed cEx)

private def markerTripleScale (z : BitString) : ℕ :=
  (Milovanov.decodeNat (decodeFirst (decodeSecond z))).getD 0

private def markerTripleProxyArgs (z : BitString) (t : ℕ) :
    ℕ × (Candidate × ℕ) :=
  let q' := markerTripleScale z
  (towerFloor q', ((decodeSecond (decodeSecond z), t), q'))

private def markerTripleProxyOutput (B : Base) (z : BitString) (t : ℕ) : BitString :=
  let q' := markerTripleScale z
  pairCode (computeStructuralProxy B (towerFloor q') (decodeSecond (decodeSecond z), t) q')
    (decodeFirst z)

private def markerTripleProxy (B : Base) (z : BitString) : Part BitString :=
  (findEmission B (decodeSecond (decodeSecond z))).map
    (markerTripleProxyOutput B z)

private lemma markerTripleScale_computable : Computable markerTripleScale := by
  have hq0 : Computable (fun z : BitString ↦ decodeFirst (decodeSecond z)) :=
    decodeFirst_computable.comp decodeSecond_computable
  exact Computable.option_getD (bits_computable.2.comp hq0) (Computable.const 0)

private lemma markerTripleProxyArgs_computable :
  Computable (fun p : BitString × ℕ ↦
    markerTripleProxyArgs p.1 p.2) := by
  have hq : Computable markerTripleScale := markerTripleScale_computable
  have hfloor : Computable (fun z : BitString ↦
      towerFloor (markerTripleScale z)) :=
    tower_floor_computable.comp hq
  have hw : Computable (fun z : BitString ↦ decodeSecond (decodeSecond z)) :=
    decodeSecond_computable.comp (decodeSecond_computable.comp Computable.id)
  have ht : Computable (fun p : BitString × ℕ ↦ p.2) := Computable.snd
  have hCand := (hw.comp Computable.fst).pair ht
  have hCandQ := hCand.pair (hq.comp Computable.fst)
  exact (hfloor.comp Computable.fst).pair hCandQ

private lemma markerTripleProxyOutput_computable
    (B : Base) : Computable (fun p : BitString × ℕ ↦ markerTripleProxyOutput B p.1 p.2) := by
  have hproxy : Computable (fun p : BitString × ℕ ↦
      computeStructuralProxy B (markerTripleProxyArgs p.1 p.2).1
        (markerTripleProxyArgs p.1 p.2).2.1 (markerTripleProxyArgs p.1 p.2).2.2) :=
    (compute_structural_proxy B).1.comp markerTripleProxyArgs_computable
  have hfirst : Computable (fun p : BitString × ℕ ↦ decodeFirst p.1) :=
    decodeFirst_computable.comp Computable.fst
  exact (pairCode_computable.comp (hproxy.pair hfirst)).of_eq (fun _ ↦ rfl)

private lemma markerTripleProxy_partrec (B : Base) :
  Partrec (markerTripleProxy B) := by
  have hout : Computable₂ (markerTripleProxyOutput B) :=
    markerTripleProxyOutput_computable B
  have hsearch : Partrec (fun (z : BitString) ↦ findEmission B (decodeSecond (decodeSecond z))) :=
    (canonical_enumeration_spec_search B).comp
      (decodeSecond_computable.comp decodeSecond_computable)
  exact Partrec.map hsearch hout

/-- A partial computable projection reconstructs the lower proxy base from the marker triple.
Blueprint node `key:decompositions`. -/
private lemma exists_marker_triple_projection (B : Base) :
  ∃ f : BitString →. BitString, Partrec f ∧
    ∃ n₄ : ℕ, 32 ≤ n₄ ∧ ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₄ n candidate x q →
      lowerProxyBase B n candidate x q ∈ f (triple x q candidate.1) := by
  use markerTripleProxy B
  constructor
  · exact markerTripleProxy_partrec B
  · obtain ⟨n1, hn1, h1⟩ := last_program_stabilizes_short_descriptions B
    use n1
    refine ⟨hn1, fun n candidate x q hK ↦ ?_⟩
    obtain ⟨hn0, htower, hcand, hrange, -⟩ := hK
    subst hcand
    have hvalid : validCandidate B n (markerCandidate B n) = true := (h1 n hn0).1
    have hsearch_eq : markerTick B n ∈ findEmission B (lastProgram B n) := by
      have hevent := (canonical_enumeration_spec_candidate B n (markerCandidate B n)).mp hvalid
      exact (canonical_enumeration_spec_search_eq B _ _).mpr hevent.2
    have htow : towerFloor q = n := tower_floor_eq n q (le_trans hn1 hn0) htower hrange
    simp only [markerTripleProxy, Part.mem_map_iff]
    use markerTick B n
    constructor
    · simpa [triple, decodeSecond_pairCode, markerCandidate] using hsearch_eq
    · dsimp [markerTripleProxyOutput]
      have hq' : markerTripleScale (triple x q (markerCandidate B n).1) = q := by
        simp [markerTripleScale, triple, decodeFirst_pairCode, decodeSecond_pairCode,
          decodeNat_bits]
      rw [hq']
      rw [htow]
      simp [triple, decodeFirst_pairCode, decodeSecond_pairCode, lowerProxyBase, markerCandidate]

private def lowerDecoderOutput
    (B : Base) : TimedEvent → BitString
  | (t, _, (_, z)) =>
    let qCode := decodeFirst (decodeFirst (decodeFirst z))
    let q' := (decodeNat qCode).getD 0
    let x := decodeSecond (decodeFirst z)
    let s := decodeSecond z
    pairCode (triple x q' (replayMarker B (towerFloor q') t).1) s

private def lowerDecoder (B : Base) (p : BitString) : Part BitString :=
  (programEmission B p).map (lowerDecoderOutput B)

/-- The lower future decoder is partial computable.
Blueprint node `key:decompositions`. -/
private lemma lowerDecoder_partrec (B : Base) : Partrec (lowerDecoder B) := by
  have hf := programEmission_partrec B
  have hz : Computable (fun (e : TimedEvent) ↦ e.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ht : Computable (fun (e : TimedEvent) ↦ e.1) :=
    Computable.fst
  have hx := decodeSecond_computable.comp (decodeFirst_computable.comp hz)
  have hs := decodeSecond_computable.comp hz
  have hfirst : Computable (fun z : BitString ↦ decodeFirst (decodeFirst (decodeFirst z))) :=
    decodeFirst_computable.comp (decodeFirst_computable.comp decodeFirst_computable)
  have h_q_prime : Computable (fun z : BitString ↦
      (decodeNat (decodeFirst (decodeFirst (decodeFirst z)))).getD 0) :=
    Computable.option_getD (bits_computable.2.comp hfirst) (Computable.const 0)
  have hq := h_q_prime.comp hz
  have hr := replayMarker_computable B
  have hw := Computable.fst.comp (hr.comp ((tower_floor_computable.comp hq).pair ht))
  have htr := triple_computable.1.comp (hx.pair (hq.pair hw))
  have hg : Computable (lowerDecoderOutput B) := by
    apply Computable.of_eq (pairCode_computable.comp (htr.pair hs))
    intro ⟨t, i, p, z⟩
    rfl
  have hg2 : Computable₂ (fun _ : BitString ↦ lowerDecoderOutput B) :=
    hg.comp Computable.snd
  exact Partrec.map hf hg2

/-- A late description of a lower proxy extension decodes to the corresponding marker extension.
Blueprint node `key:decompositions`. -/
private lemma lowerDecoder_mem_of_late_emission
    (B : Base) : ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q → ∀ (s p : BitString),
      pairCode (lowerProxyBase B n candidate x q) s ∈ B.V (p, []) →
      (∀ t i o, eventAt B t = some (t, i, p, o) → t > markerTick B n) →
      pairCode (triple x q candidate.1) s ∈
        lowerDecoder B p := by
  obtain ⟨n₁, hn₁, hrep⟩ := replayMarker_eq_markerCandidate B
  obtain ⟨n₂, -, hstab⟩ := last_program_stabilizes_short_descriptions B
  use max n₁ n₂
  constructor
  · exact le_trans hn₁ (le_max_left _ _)
  · intro n candidate x q hkp s p hp hlate
    obtain ⟨hn_ge, hIsTower, hCand, hTowerRange, -⟩ := hkp
    have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hn_ge
    have hn2 : n₂ ≤ n := le_trans (le_max_right _ _) hn_ge
    have hvalid : validCandidate B n candidate = true := by
      rw [hCand]
      exact (hstab n hn2).1
    obtain ⟨t, i, hev⟩ := (canonical_enumeration_spec_complete B p _).mp hp
    have hsearch : t ∈ findEmission B p :=
      (canonical_enumeration_spec_search_eq B p t).mpr ⟨i, _, hev⟩
    have hfind : findEmission B p = Part.some t := Part.eq_some_iff.mpr hsearch
    have hmt : markerTick B n < t := hlate t i _ hev
    have hemit : programEmission B p =
        Part.some (t, i, p, pairCode (lowerProxyBase B n candidate x q) s) := by
      simp [programEmission, hfind, hev]
    have hz : lowerDecoderOutput B (t, i, p, pairCode (lowerProxyBase B n candidate x q) s) =
        pairCode (triple x q candidate.1) s := by
      unfold lowerDecoderOutput
      dsimp
      have hz1 := decodeFirst_pairCode (lowerProxyBase B n candidate x q) s
      have hz2 := decodeSecond_pairCode (lowerProxyBase B n candidate x q) s
      have hq1 : decodeFirst (lowerProxyBase B n candidate x q) =
          computeStructuralProxy B n candidate q := by
        unfold lowerProxyBase
        rw [decodeFirst_pairCode]
      have hq2 : decodeNat (decodeFirst (computeStructuralProxy B n candidate q)) = some q :=
        compute_structural_proxy_first B n candidate q hvalid
      have hx1 : decodeSecond (lowerProxyBase B n candidate x q) = x := by
        unfold lowerProxyBase
        rw [decodeSecond_pairCode]
      rw [hz1, hz2, hq1, hq2, Option.getD_some, hx1]
      have hfl : towerFloor q = n := tower_floor_eq n q (le_trans hn₁ hn1) hIsTower hTowerRange
      rw [hfl, hrep n hn1 t (le_of_lt hmt), ← hCand]
    rw [lowerDecoder, hemit, Part.map_some, hz]
    exact Part.mem_some _

/-- Every lower-scale extension outside the past has a short marker-triple description.
Blueprint node `key:decompositions`. -/
private lemma lower_future_extension_simple (B : Base) :
  ∃ cEx n₂ : ℕ, 32 ≤ n₂ ∧ ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
    KeyParameters B n₂ n candidate x q → ∀ (s : BitString),
    Simple B.V (pairCode (lowerProxyBase B n candidate x q) s) (extensionScale n) →
    pairCode (lowerProxyBase B n candidate x q) s ∉ stageOutputs B (extensionScale n) candidate.2 →
    Simple B.V (pairCode (triple x q candidate.1) s) (extensionScale n + cEx) := by
  have hg : Partrec (lowerDecoder B) := lowerDecoder_partrec B
  obtain ⟨c, hc⟩ := exists_plain_complexity_bound_of_partrec B _ hg
  obtain ⟨n₀, hn₀, hn_prop⟩ := lowerDecoder_mem_of_late_emission B
  refine ⟨c, n₀, hn₀, fun n candidate x q h_kp s h_simple h_not_past ↦ ?_⟩
  obtain ⟨p, hp_len, hp_mem⟩ := (simple_iff_exists_program B.V _ _).mp h_simple
  have hkp_cand : candidate = markerCandidate B n := h_kp.2.2.1
  have htick : candidate.2 = markerTick B n := congrArg Prod.snd hkp_cand
  have h_not_past' : pairCode (lowerProxyBase B n candidate x q) s ∉
      stageOutputs B (extensionScale n) (markerTick B n) := by
    rw [← htick]
    exact h_not_past
  have h_late : ∀ t i x_1, eventAt B t = some (t, i, p, x_1) → t > markerTick B n :=
    emission_tick_gt_marker_of_not_mem_stageOutputs B n (extensionScale n) p
      (pairCode (lowerProxyBase B n candidate x q) s) hp_len hp_mem h_not_past'
  have h_correct : pairCode (triple x q candidate.1) s ∈ lowerDecoder B p :=
    hn_prop n candidate x q h_kp s p hp_mem h_late
  change plainK B.V (pairCode (triple x q candidate.1) s) ≤ ((extensionScale n + c : ℕ) : ENat)
  calc
    _ ≤ (p.length : ENat) + (c : ENat) :=
      hc p (pairCode (triple x q candidate.1) s) h_correct
    _ ≤ ((extensionScale n + c : ℕ) : ENat) := by
      exact_mod_cast (Nat.add_le_add_right hp_len c)

/-- The lower proxy volume is comparable to its past count plus the marker-triple volume.
Blueprint node `key:decompositions`. -/
theorem key_lemma_past_future_decompositions_lower (B : Base) :
    ∃ cDec n₀ : ℕ, 32 ≤ n₀ ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q → LowerVolumeDecomposition B cDec n candidate x q := by
  obtain ⟨f, hf, n4, hn4, hmap⟩ := exists_marker_triple_projection B
  obtain ⟨c0, cDen, cRel0, hd⟩ := extension_density_common B
  obtain ⟨c0r, cRel, hrel⟩ := extension_density_relaxed B
  obtain ⟨cF, hcF⟩ := extension_volume_of_computable_projection B hd f hf
  obtain ⟨cEx, n2, -, hcore⟩ := lower_future_extension_simple B
  obtain ⟨n1, -, hgap⟩ := key_lemma_information_gaps B (max c0 c0r)
  obtain ⟨n3, -, hstab⟩ := last_program_stabilizes_short_descriptions B
  let n₀ := max (max (max n1 n2) n3) n4
  let cDec := cF + 1 + cRel * (cEx + 1)
  use cDec, n₀
  constructor
  · apply le_trans hn4 (le_max_right _ _)
  · intro n candidate x q hp
    have hp_n1 := KeyParameters.of_threshold_le B
      ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))) candidate x q hp
    have hp_n2 := KeyParameters.of_threshold_le B
      ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))) candidate x q hp
    have hp_n4 := KeyParameters.of_threshold_le B (le_max_right _ _) candidate x q hp
    have hGaps := hgap n candidate x q hp_n1
    have h_lower_gap : KP B.D (lowerProxyBase B n candidate x q) (bits n) + c0 ≤
        (extensionScale n : ENat) := by
      have h1 : (c0 : ENat) ≤ (max c0 c0r : ENat) :=
        WithTop.coe_le_coe.mpr (le_max_left _ _)
      have h := hGaps.lower
      exact le_trans (add_le_add le_rfl h1) h
    have h_marker_gap : KP B.D (triple x q candidate.1) (bits n) + c0r ≤
        (extensionScale n : ENat) := by
      have h1 : (c0r : ENat) ≤ (max c0 c0r : ENat) :=
        WithTop.coe_le_coe.mpr (le_max_right _ _)
      have h := hGaps.marker
      exact le_trans (add_le_add le_rfl h1) h
    have h_valid : validCandidate B n candidate = true := by
      have h_n3 : n3 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hp.1)
      have h_cand := hp.2.2.1
      rw [h_cand]
      exact (hstab n h_n3).1
    have h_F := hcF n (triple x q candidate.1) (lowerProxyBase B n candidate x q)
      (hmap n candidate x q hp_n4) h_lower_gap
    have h_G := hrel n (triple x q candidate.1) h_marker_gap cEx
    have h3 : ((2 : ℚ) ^ ((cRel : ℤ) * (cEx + 1))) = ((2 ^ (cRel * (cEx + 1)) : ℕ) : ℚ) := by
      push_cast
      rfl
    rw [h3] at h_G
    let a := strictExtensionCount B n (lowerProxyBase B n candidate x q)
    let p := pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q)
    let f_val := strictExtensionCount B n (triple x q candidate.1)
    let g_val := extensionCount B n cEx (triple x q candidate.1)
    have ha : p ≤ a := past_extension_count_le_strict B n candidate n
      (lowerProxyBase B n candidate x q)
    have hg_count : a ≤ p + g_val :=
      strict_count_le_past_add_of_future_simple B h_valid (hcore n candidate x q hp_n2)
    dsimp [LowerVolumeDecomposition]
    have harith := dyadic_bounds_of_past_future_bounds cF (cRel * (cEx + 1)) p a f_val g_val
      (by positivity) (by positivity) (by positivity)
      (by exact_mod_cast ha) (by exact_mod_cast h_F)
      (by exact_mod_cast hg_count) (by exact_mod_cast h_G)
    have h_cDec : (cDec : ℤ) = (cF + 1 + (cRel * (cEx + 1)) : ℤ) := by rfl
    have h_p_f : (p : ℚ) + (f_val : ℚ) = ((p + f_val : ℕ) : ℚ) := by push_cast; rfl
    rw [h_cDec]
    rw [h_p_f] at harith
    exact harith

/-- Upper and lower decompositions share one loss constant and one scale threshold.
Blueprint node `key:decompositions`. Reconstruction uses the program's event, not its output. -/
theorem key_lemma_past_future_decompositions_common (B : Base) :
    ∃ cDec n₀ : ℕ, 32 ≤ n₀ ∧
      ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
        KeyParameters B n₀ n candidate x q →
        UpperVolumeDecomposition B cDec n candidate x q ∧
        LowerVolumeDecomposition B cDec n candidate x q := by
  obtain ⟨cDec1, n01, hn01, h1⟩ := key_lemma_past_future_decompositions B
  obtain ⟨cDec2, n02, hn02, h2⟩ := key_lemma_past_future_decompositions_lower B
  use max cDec1 cDec2, max n01 n02
  constructor
  · apply le_trans hn01 (le_max_left _ _)
  · intro n candidate x q hp
    constructor
    · apply UpperVolumeDecomposition.mono B (le_max_left _ _)
      apply h1
      exact KeyParameters.of_threshold_le B (le_max_left _ _) _ _ _ hp
    · apply LowerVolumeDecomposition.mono B (le_max_right _ _)
      apply h2
      exact KeyParameters.of_threshold_le B (le_max_right _ _) _ _ _ hp

end Kolmogorov.Milovanov
