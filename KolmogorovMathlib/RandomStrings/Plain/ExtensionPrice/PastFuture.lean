/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Encoding
import KolmogorovMathlib.RandomStrings.Plain.Enumeration
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity
import KolmogorovMathlib.RandomStrings.Plain.Markers
import KolmogorovMathlib.RandomStrings.Plain.PrefixInterface
import KolmogorovMathlib.RandomStrings.Plain.StructuralProxy
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Floor
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.FinsetComputable
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.Foundation.ListUtil
import KolmogorovMathlib.StoppingComplexity.RatComputableExtras

/-!
# Past extension counts and future decoding

This module prepares the two volume decompositions of blueprint node `key:decompositions`.
It defines the computable count of extensions emitted before a candidate marker, the two
future bases, and the upper and lower volume decomposition predicates. For blueprint node
`key:gaps`, it verifies the prefix-complexity gaps required by the density estimates.

Replaying the canonical enumeration recovers the true marker after its emission. A partial
computable decoder uses this replay to turn a late short description into an extension of
the upper future base. `Decompositions` combines this decoder with density and projection
bounds; `SquareRoot` uses the information gaps to obtain structural volume estimates.
-/

namespace Kolmogorov.Milovanov

/-- The finite extension indices emitted by a candidate's numeric timestamp.
Blueprint node `key:decompositions`. Re-encoding rejects malformed pairs; invalid candidates
give the empty set. `n` verifies the candidate length, independently of the volume scale `h`. -/
def pastExtensionIndices (B : Base) (n : ℕ) (candidate : Candidate) (h : ℕ)
    (y : BitString) : Finset BitString :=
  if validCandidate B n candidate then
    ((stageOutputs B (extensionScale h) candidate.2).filter
      (fun output ↦ pairCode y (decodeSecond output) = output)).image decodeSecond
  else ∅

/-- The computable past count `P_h^w(y)`, defaulting to zero on malformed records.
Blueprint node `key:decompositions`. Outputs and extension indices are each deduplicated. -/
def pastExtensionCount (B : Base) (n : ℕ) (candidate : Candidate) (h : ℕ)
    (y : BitString) : ℕ := (pastExtensionIndices B n candidate h y).card

private theorem extension_indices_eq_filter_map
    (l : List BitString) (y : BitString) :
    (l.toFinset.filter
      (fun output ↦ pairCode y (decodeSecond output) = output)).image
        decodeSecond =
    ((l.filter (fun output ↦
      decide (pairCode y (decodeSecond output) = output))).map
        decodeSecond).toFinset := by
  ext s
  simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset,
    List.mem_map, List.mem_filter, decide_eq_true_eq]

private theorem past_candidate_valid_computable
    (B : Base) : Computable (fun p : ℕ × Candidate × ℕ × BitString ↦ validCandidate B p.1 p.2.1) :=
  Computable₂.comp (canonical_enumeration_spec_prefix_computable B).1
    Computable.fst (Computable.fst.comp Computable.snd)

private theorem past_output_list_computable
    (B : Base) : Computable (fun p : ℕ × Candidate × ℕ × BitString ↦
      stageOutputList B (extensionScale p.2.2.1) p.2.1.2) := by
  have h_scale : Computable (fun p : ℕ × Candidate × ℕ × BitString ↦ extensionScale p.2.2.1) :=
    Kolmogorov.primrec_two_pow_aux.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have h_t : Computable (fun p : ℕ × Candidate × ℕ × BitString ↦ p.2.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  exact Computable₂.comp (canonical_enumeration_spec_outputs B).1 h_scale h_t

private theorem past_pair_list_computable
    (B : Base) : Computable (fun p : ℕ × Candidate × ℕ × BitString ↦
      (stageOutputList B (extensionScale p.2.2.1) p.2.1.2).filter
        (fun output ↦ pairCode p.2.2.2 (decodeSecond output) = output)) := by
  have h_E_list := past_output_list_computable B
  have h_p : Computable (fun p : (ℕ × Candidate × ℕ × BitString) × BitString ↦ p.1) :=
    Computable.fst
  have h_y : Computable (fun (p : (ℕ × Candidate × ℕ × BitString) × BitString) ↦ p.1.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp h_p))
  have h_output : Computable (fun p : (ℕ × Candidate × ℕ × BitString) × BitString ↦ p.2) :=
    Computable.snd
  have h_eq : Computable (fun p : (ℕ × Candidate × ℕ × BitString) × BitString ↦
      decide (pairCode p.1.2.2.2 (decodeSecond p.2) = p.2)) :=
    (Kolmogorov.primrec_decideEq.to_comp.comp
      (Computable₂.comp pairCode_computable h_y (decodeSecond_computable.comp h_output)) h_output)
  exact computable_list_filter h_E_list h_eq

private theorem past_index_list_computable
    (B : Base) : Computable (fun p : ℕ × Candidate × ℕ × BitString ↦
      ((stageOutputList B (extensionScale p.2.2.1) p.2.1.2).filter
        (fun output ↦ pairCode p.2.2.2 (decodeSecond output) = output)).map decodeSecond) := by
  exact Computable.list_map (past_pair_list_computable B)
    (decodeSecond_computable.comp Computable.snd)

private theorem past_index_list_card_computable
    (B : Base) : Computable (fun p : ℕ × Candidate × ℕ × BitString ↦
      (((stageOutputList B (extensionScale p.2.2.1) p.2.1.2).filter
        (fun output ↦ pairCode p.2.2.2 (decodeSecond output) = output)).map
          decodeSecond).eraseDups.length) := by
  exact Computable.list_length.comp
    (CodedFiniteDistribution.eraseDups_bitstring_primrec.to_comp.comp
      (past_index_list_computable B))

/-- The past counter is computable uniformly in the candidate, scale, and base object.
Blueprint node `key:decompositions`. Only finite emitted snapshots are inspected. -/
theorem past_extension_count_computable (B : Base) :
    Computable (fun p : ℕ × Candidate × ℕ × BitString =>
      pastExtensionCount B p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ht_valid := past_candidate_valid_computable B
  have h_list_length := past_index_list_card_computable B
  have h_empty : Computable (fun p : ℕ × Candidate × ℕ × BitString ↦ (∅ : Finset BitString).card) :=
    Computable.const 0
  exact Computable.of_eq (Computable.cond ht_valid h_list_length h_empty) (fun p ↦ by
    dsimp [pastExtensionCount, pastExtensionIndices, stageOutputs]
    by_cases h : validCandidate B p.1 p.2.1 = true
    · simp only [h, Bool.cond_true, ite_true]
      rw [extension_indices_eq_filter_map]
      rw [card_toFinset_eq_length_eraseDups]
    · have hF : validCandidate B p.1 p.2.1 = false := by
        cases h' : validCandidate B p.1 p.2.1 <;> simp_all
      simp only [hF, Bool.cond_false]
      rfl)

/-- On valid records, membership is exactly membership of the pair in the frozen emitted table.
Blueprint node `key:decompositions`. Pending events do not enter this set. -/
theorem mem_past_extension_indices (B : Base) (n : ℕ) (candidate : Candidate)
    (h : ℕ) (y s : BitString) (hc : validCandidate B n candidate = true) :
    s ∈ pastExtensionIndices B n candidate h y ↔
      pairCode y s ∈ stageOutputs B (extensionScale h) candidate.2 := by
  simp only [pastExtensionIndices, hc, ite_true, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨output, ⟨hmem, hpair⟩, rfl⟩
    rwa [hpair]
  · intro hmem
    exact ⟨pairCode y s, ⟨hmem, by simp [decodeSecond_pairCode]⟩,
      decodeSecond_pairCode y s⟩

/-- The finite counter agrees with the chapter's mathematical set of past extension indices.
Blueprint node `key:decompositions`. -/
theorem past_extension_count_eq (B : Base) (n : ℕ) (candidate : Candidate)
    (h : ℕ) (y : BitString) (hc : validCandidate B n candidate = true) :
    pastExtensionCount B n candidate h y =
      {s | pairCode y s ∈ stageOutputs B (extensionScale h) candidate.2}.ncard := by
  have he : (pastExtensionIndices B n candidate h y : Set BitString) =
      {s | pairCode y s ∈ stageOutputs B (extensionScale h) candidate.2} := by
    ext s
    exact mem_past_extension_indices B n candidate h y s hc
  rw [← he, Set.ncard_coe_finset]
  rfl

/-- The four-field extension set uses exactly the frozen `extensionCode` strings.
Blueprint node `key:decompositions`. No description-length shift occurs at this boundary. -/
theorem extension_set_triple (B : Base) (h δ q : ℕ) (x w : BitString) :
    extensionSet B h δ (triple x q w) =
      {s | Simple B.V (extensionCode x q w s) (extensionScale h + δ)} := rfl

/-- The upper-scale future base uses the computed proxy and its bounded alpha.
Blueprint node `key:decompositions`. The extension index is attached only after this base. -/
def upperFutureBase (B : Base) (n : ℕ) (candidate : Candidate) (x : BitString)
    (q : ℕ) : BitString :=
  proxyBase x (computeStructuralProxy B n candidate q) (structuralProxyAlpha B n candidate q)

/-- The lower-scale proxy base is the frozen pair `(q̃,x)`.
Blueprint node `key:decompositions`. -/
def lowerProxyBase (B : Base) (n : ℕ) (candidate : Candidate) (x : BitString)
    (q : ℕ) : BitString := pairCode (computeStructuralProxy B n candidate q) x

/-- Exactly the true-marker, large-tower, target-range, and string-length hypotheses.
Blueprint node `key:gaps`. There is no hypothesis involving the later padding parameter. -/
def KeyParameters (B : Base) (n₀ n : ℕ) (candidate : Candidate) (x : BitString)
    (q : ℕ) : Prop :=
  n₀ ≤ n ∧ IsTower n ∧ candidate = markerCandidate B n ∧
    TowerRange n q ∧ x.length ≤ towerRangeBound n

/-- Parameters above a threshold also satisfy every smaller threshold. -/
lemma KeyParameters.of_threshold_le (B : Base) {n0_1 n0_2 n : ℕ} (h : n0_1 ≤ n0_2)
    (candidate : Candidate) (x : BitString) (q : ℕ)
    (hK : KeyParameters B n0_2 n candidate x q) :
    KeyParameters B n0_1 n candidate x q := by
  exact ⟨h.trans hK.1, hK.2⟩

/-- The four density gaps, with one gap constant and the indicated binary scale conditions.
Blueprint node `key:gaps`. The marker base uses `candidate.1`, equal to `lastProgram` in scope. -/
structure KeyInformationGaps (B : Base) (c₀ n : ℕ) (candidate : Candidate)
    (x : BitString) (q : ℕ) : Prop where
  /-- The original object has the density gap at the upper scale. -/
  plain : KP B.D x (bits q) + c₀ ≤ (extensionScale q : ENat)
  /-- The upper future base has the density gap at the upper scale. -/
  upper : KP B.D (upperFutureBase B n candidate x q) (bits q) + c₀ ≤
    (extensionScale q : ENat)
  /-- The proxy pair has the density gap at the lower scale. -/
  lower : KP B.D (lowerProxyBase B n candidate x q) (bits n) + c₀ ≤
    (extensionScale n : ENat)
  /-- The marker triple has the density gap at the lower scale. -/
  marker : KP B.D (triple x q candidate.1) (bits n) + c₀ ≤ (extensionScale n : ENat)

private lemma eventually_literal_bound_le_extension_scale (A A' c : ℕ) :
    ∃ N₀ : ℕ, 32 ≤ N₀ ∧ ∀ (n : ℕ), N₀ ≤ n → IsTower n →
      A * towerRangeBound n + A' + 2 * Nat.clog 2 (A * towerRangeBound n + A' + 2) + c ≤
        extensionScale n := by
  let M := 3 * A + 3 * A' + 4 + c
  let N₀ := 2 ^ (M + 8)
  use max 32 N₀
  constructor
  · exact le_max_left _ _
  · intro n h_n_bound h_tower
    have hN₀ : N₀ ≤ n := le_trans (le_max_right _ _) h_n_bound
    have h32 : 32 ≤ n := le_trans (le_max_left _ _) h_n_bound
    let R := towerRangeBound n
    have hn_pos : 0 < n := by omega
    have h1 : 1 ≤ R := by
      dsimp [R, towerRangeBound]
      apply Nat.one_le_pow _ _ hn_pos
    have h2 : Nat.clog 2 (A * R + A' + 2) ≤ A * R + A' + 2 := by
      apply (Nat.clog_le_iff_le_pow (by decide)).mpr
      apply le_of_lt
      apply Nat.lt_two_pow_self
    have h3 : A * R + A' + 2 * Nat.clog 2 (A * R + A' + 2) + c ≤ M * R := by
      calc
        A * R + A' + 2 * Nat.clog 2 (A * R + A' + 2) + c
            ≤ A * R + A' + 2 * (A * R + A' + 2) + c := by gcongr
        _ = 3 * (A * R) + 3 * A' + 4 + c := by ring
        _ ≤ 3 * (A * R) + 3 * (A' * R) + 4 * R + c * R := by
          have hA' : A' * 1 ≤ A' * R := Nat.mul_le_mul_left _ h1
          have hc : c * 1 ≤ c * R := Nat.mul_le_mul_left _ h1
          have h4 : 4 * 1 ≤ 4 * R := Nat.mul_le_mul_left _ h1
          nlinarith
        _ = (3 * A + 3 * A' + 4 + c) * R := by ring
    have h4 : M * R ≤ extensionScale n := by
      rcases h_tower with ⟨i, hi⟩
      cases i with
      | zero =>
        dsimp [tower] at hi
        omega
      | succ i' =>
        let t := tower i'
        have ht : n = 2 ^ t := by
          rw [← hi]
          rfl
        have h_M_bound : M + 8 ≤ t := by
          have : 2 ^ (M + 8) ≤ 2 ^ t := by omega
          exact (Nat.pow_le_pow_iff_right (by decide)).mp this
        have h_R_eq : R = 2 ^ (t * t) := by
          dsimp [R, towerRangeBound]
          rw [ht, Nat.log2_two_pow, ← Nat.pow_mul]
        have h_M_le_2_M : M ≤ 2 ^ M := le_of_lt Nat.lt_two_pow_self
        have h_MR : M * R ≤ 2 ^ (M + t * t) := by
          rw [h_R_eq, Nat.pow_add]
          apply Nat.mul_le_mul h_M_le_2_M (le_refl _)
        have h_exp : t * t + M ≤ 2 ^ t := by
          obtain ⟨u, hu⟩ : ∃ u, t = u + 1 := by
            use t - 1
            omega
          have hu5 : 5 ≤ u := by omega
          have h_u_sq : u * u < 2 ^ u := by
            have : ∀ x, 5 ≤ x → x * x < 2 ^ x := by
              intro x hx
              induction x, hx using Nat.le_induction with
              | base => decide
              | succ k hk ih =>
                have h_k_sq : 2 * k + 1 ≤ k * k := by nlinarith
                have h_2_k : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
                linarith
            apply this _ hu5
          have h_2_u_1 : 2 ^ (u + 1) = 2 ^ u + 2 ^ u := by ring
          have h_M7_u : (M + 7) * u ≤ u * u := by
            apply Nat.mul_le_mul_right
            omega
          have h_M : M * 1 ≤ M * u := Nat.mul_le_mul_left _ (by omega)
          have ht_sq : t * t = (u + 1) * (u + 1) := by rw [hu]
          have h_exp1 : (u + 1) * (u + 1) + M ≤ 2 ^ (u + 1) := by
            nlinarith
          rw [hu]
          exact h_exp1
        have h_pow : 2 ^ (M + t * t) ≤ 2 ^ n := by
          rw [Nat.add_comm]
          apply Nat.pow_le_pow_right (by decide)
          rw [ht]
          exact h_exp
        exact le_trans h_MR h_pow
    exact le_trans h3 h4

private lemma prefix_complexity_gap_of_length_le (B : Base) (s b : BitString) (ℓ c₀ N : ℕ)
    (h_len : s.length ≤ ℓ) (h_bound : ℓ + 2 * Nat.clog 2 (ℓ + 2) + B.cD + c₀ ≤ N) :
    KP B.D s b + c₀ ≤ (N : ENat) := by
  have h1 := B.literal_bound s b
  have h2 : s.length + 2 * Nat.clog 2 (s.length + 2) + B.cD ≤
      ℓ + 2 * Nat.clog 2 (ℓ + 2) + B.cD := by
    have h_clog : Nat.clog 2 (s.length + 2) ≤ Nat.clog 2 (ℓ + 2) := Nat.clog_mono_right 2 (by omega)
    omega
  calc
    KP B.D s b + c₀ ≤ (s.length + 2 * Nat.clog 2 (s.length + 2) + B.cD : ℕ) + c₀ := by gcongr
    _ = ((s.length + 2 * Nat.clog 2 (s.length + 2) + B.cD + c₀ : ℕ) : ENat) := by push_cast; rfl
    _ ≤ (N : ENat) := by exact_mod_cast (by omega)

/-- The original object's upper-scale density gap. Blueprint node `key:gaps`. -/
theorem key_lemma_information_gaps_plain (B : Base) (c₀ : ℕ) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q →
      KP B.D x (bits q) + c₀ ≤ (extensionScale q : ENat) := by
  obtain ⟨N₀, hn₀, h_gap⟩ := eventually_literal_bound_le_extension_scale 1 0 (B.cD + c₀)
  use N₀
  constructor
  · exact hn₀
  · intro n cand x q hp
    rcases hp with ⟨h_n₀_le_n, h_tower, h_cand, ⟨h_n_le_q, h_q_lt_R⟩, h_len⟩
    have h_scale : extensionScale n ≤ extensionScale q := Nat.pow_le_pow_right (by decide) h_n_le_q
    have h_gap' := h_gap n h_n₀_le_n h_tower
    apply prefix_complexity_gap_of_length_le B x (bits q) (towerRangeBound n)
      c₀ (extensionScale q) h_len
    simpa only [one_mul, Nat.add_zero, Nat.add_assoc] using h_gap'.trans h_scale

/-- The future base's upper-scale density gap. Blueprint node `key:gaps`. -/
theorem key_lemma_information_gaps_upper (B : Base) (c₀ : ℕ) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q →
      KP B.D (upperFutureBase B n candidate x q) (bits q) + c₀ ≤
        (extensionScale q : ENat) := by
  obtain ⟨cLen, n₁, hn1, hproxy⟩ := compute_structural_proxy_length B
  obtain ⟨N₀, hN₀, hgap⟩ := eventually_literal_bound_le_extension_scale (4 + 5 * cLen)
    (10 * cLen + 8 + B.cD) (B.cD + c₀)
  refine ⟨max n₁ N₀, le_trans hn1 (le_max_left _ _), ?_⟩
  rintro n candidate x q ⟨hn, ht, hc, hq, hx⟩
  have hlen := hproxy n (le_trans (le_max_left _ _) hn) ht candidate q hc hq
  have hq1 : q + 1 ≤ towerRangeBound n := hq.2
  have hlog : Nat.log2 (q + 2) ≤ q + 2 := Nat.log2_le_self _
  have hpl : (computeStructuralProxy B n candidate q).length ≤
      cLen * towerRangeBound n + 2 * cLen := by
    calc (computeStructuralProxy B n candidate q).length
        ≤ cLen * Nat.log2 (q + 2) + cLen := hlen
      _ ≤ cLen * (q + 2) + cLen := Nat.add_le_add_right (Nat.mul_le_mul_left cLen hlog) cLen
      _ ≤ cLen * (towerRangeBound n + 1) + cLen := by
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_left
          omega
      _ = cLen * towerRangeBound n + 2 * cLen := by ring
  have h_alpha : structuralProxyAlpha B n candidate q ≤
      literalBound B (computeStructuralProxy B n candidate q) := by
    unfold structuralProxyAlpha candidatePrefixComplexity
    split_ifs
    · exact (canonical_enumeration_spec_prefix_min B _ _ _ _).mpr (Or.inl le_rfl)
    · exact le_rfl
  have h_base_len : (upperFutureBase B n candidate x q).length ≤
      (4 + 5 * cLen) * towerRangeBound n + 10 * cLen + 8 + B.cD := by
    have hbits := length_bits_le (structuralProxyAlpha B n candidate q)
    have hclog : Nat.clog 2 ((computeStructuralProxy B n candidate q).length + 2) ≤
        (computeStructuralProxy B n candidate q).length + 2 := by
      apply (Nat.clog_le_iff_le_pow (by decide)).2
      exact Nat.lt_two_pow_self.le
    dsimp [literalBound] at h_alpha
    dsimp [upperFutureBase, proxyBase]
    rw [length_pairCode, length_pairCode]
    nlinarith
  apply prefix_complexity_gap_of_length_le B _ (bits q)
    ((4 + 5 * cLen) * towerRangeBound n + 10 * cLen + 8 + B.cD) c₀ (extensionScale q)
  · exact h_base_len
  · have h1 := hgap n (le_trans (le_max_right _ _) hn) ht
    have h2 : extensionScale n ≤ extensionScale q := Nat.pow_le_pow_right (by decide) hq.1
    simpa only [Nat.add_assoc] using h1.trans h2

/-- The proxy pair's lower-scale density gap. Blueprint node `key:gaps`. -/
theorem key_lemma_information_gaps_lower (B : Base) (c₀ : ℕ) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q →
      KP B.D (lowerProxyBase B n candidate x q) (bits n) + c₀ ≤
        (extensionScale n : ENat) := by
  obtain ⟨cLen, n1, _, h1⟩ := compute_structural_proxy_length B
  obtain ⟨N₀, hn0, h2⟩ :=
    eventually_literal_bound_le_extension_scale (2 * cLen + 1) (4 * cLen + 1) (B.cD + c₀)
  refine ⟨max n1 N₀, le_trans hn0 (le_max_right _ _), ?_⟩
  intro n candidate x q hp
  rcases hp with ⟨h_n0, ht, hc, hr, hx⟩
  have hn1 : n1 ≤ n := le_trans (le_max_left _ _) h_n0
  have hN₀ : N₀ ≤ n := le_trans (le_max_right _ _) h_n0
  have hlen1 := h1 n hn1 ht candidate q hc hr
  have hlog : (q + 2).log2 ≤ q + 2 := Nat.log2_le_self _
  have hq : q < towerRangeBound n := hr.2
  have hlen0 : (computeStructuralProxy B n candidate q).length ≤
      cLen * towerRangeBound n + 2 * cLen := by
    calc (computeStructuralProxy B n candidate q).length
        ≤ cLen * (q + 2).log2 + cLen := hlen1
      _ ≤ cLen * (q + 2) + cLen := by gcongr
      _ ≤ cLen * (towerRangeBound n + 1) + cLen :=
        Nat.add_le_add_right (Nat.mul_le_mul_left cLen (by omega)) cLen
      _ = cLen * towerRangeBound n + 2 * cLen := by ring
  have hlen2 : (lowerProxyBase B n candidate x q).length ≤
      (2 * cLen + 1) * towerRangeBound n + (4 * cLen + 1) := by
    unfold lowerProxyBase
    rw [length_pairCode]
    linarith
  have hN_bound := h2 n hN₀ ht
  apply prefix_complexity_gap_of_length_le B (lowerProxyBase B n candidate x q) (bits n)
    ((2 * cLen + 1) * towerRangeBound n + (4 * cLen + 1)) c₀ (extensionScale n)
  · exact hlen2
  · change _ ≤ 2 ^ n
    have heq : (2 * cLen + 1) * towerRangeBound n + (4 * cLen + 1) +
        2 * Nat.clog 2 ((2 * cLen + 1) * towerRangeBound n + (4 * cLen + 1) + 2) + B.cD + c₀ =
      (2 * cLen + 1) * towerRangeBound n + (4 * cLen + 1) +
        2 * Nat.clog 2 ((2 * cLen + 1) * towerRangeBound n + (4 * cLen + 1) + 2) +
          (B.cD + c₀) := by omega
    rw [heq]
    exact hN_bound

/-- The marker triple's lower-scale density gap. Blueprint node `key:gaps`. -/
theorem key_lemma_information_gaps_marker (B : Base) (c₀ : ℕ) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q →
      KP B.D (triple x q candidate.1) (bits n) + c₀ ≤ (extensionScale n : ENat) := by
  obtain ⟨n₁, hn₁, hstab⟩ := last_program_stabilizes_short_descriptions B
  obtain ⟨N₀, hN₀32, hgap⟩ := eventually_literal_bound_le_extension_scale 5 2 (B.cD + c₀)
  refine ⟨max n₁ N₀, le_trans hN₀32 (le_max_right _ _), ?_⟩
  intro n candidate x q hp
  rcases hp with ⟨h_n0, ht, hc, ⟨hnq, hqR⟩, hx⟩
  have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) h_n0
  have hN : N₀ ≤ n := le_trans (le_max_right _ _) h_n0
  have hv : validCandidate B n (markerCandidate B n) = true := (hstab n hn1).1
  subst hc
  have hw : (markerCandidate B n).1.length ≤ n := by
    unfold validCandidate at hv
    rw [Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1
  have hlen : (triple x q (markerCandidate B n).1).length ≤ 5 * towerRangeBound n + 2 := by
    rw [literal_and_tuple_code_interface_triple]
    have := length_bits_le q
    omega
  have hS := hgap n hN ht
  apply prefix_complexity_gap_of_length_le B (triple x q (markerCandidate B n).1) (bits n)
    (5 * towerRangeBound n + 2) c₀ (extensionScale n) hlen
  change _ ≤ 2 ^ n
  have hS' : 5 * towerRangeBound n + 2 +
      2 * Nat.clog 2 (5 * towerRangeBound n + 2 + 2) + (B.cD + c₀) ≤ 2 ^ n := hS
  omega

/-- All four bases satisfy the same density gap after enlarging a fixed threshold.
Blueprint node `key:gaps`. The supplied `c₀` is fixed before choosing that threshold. -/
theorem key_lemma_information_gaps (B : Base) (c₀ : ℕ) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ (n : ℕ) (candidate : Candidate) (x : BitString) (q : ℕ),
      KeyParameters B n₀ n candidate x q → KeyInformationGaps B c₀ n candidate x q := by
  obtain ⟨nPlain, hnPlain, hplain⟩ := key_lemma_information_gaps_plain B c₀
  obtain ⟨nUpper, _, hupper⟩ := key_lemma_information_gaps_upper B c₀
  obtain ⟨nLower, _, hlower⟩ := key_lemma_information_gaps_lower B c₀
  obtain ⟨nMarker, _, hmarker⟩ := key_lemma_information_gaps_marker B c₀
  refine ⟨max nPlain (max nUpper (max nLower nMarker)),
    hnPlain.trans (le_max_left _ _), ?_⟩
  intro n candidate x q hp
  have hpPlain := KeyParameters.of_threshold_le B (le_max_left _ _) candidate x q hp
  have hpUpper := KeyParameters.of_threshold_le B
    ((le_max_left _ _).trans (le_max_right _ _)) candidate x q hp
  have hpLower := KeyParameters.of_threshold_le B
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) candidate x q hp
  have hpMarker := KeyParameters.of_threshold_le B
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) candidate x q hp
  exact ⟨hplain n candidate x q hpPlain, hupper n candidate x q hpUpper,
    hlower n candidate x q hpLower, hmarker n candidate x q hpMarker⟩

/-- The upper-scale past/future decomposition with explicit two-sided loss.
Blueprint node `key:decompositions`. -/
def UpperVolumeDecomposition (B : Base) (cDec n : ℕ) (candidate : Candidate)
    (x : BitString) (q : ℕ) : Prop :=
  let P := pastExtensionCount B n candidate q x
  let F := strictExtensionCount B q (upperFutureBase B n candidate x q)
  (2 : ℚ) ^ (-(cDec : ℤ)) * (P + F) ≤ strictExtensionCount B q x ∧
  (strictExtensionCount B q x : ℚ) ≤ (2 : ℚ) ^ (cDec : ℤ) * (P + F)

/-- The lower-scale past/future decomposition with explicit two-sided loss.
Blueprint node `key:decompositions`. The future summand is the marker-triple volume. -/
def LowerVolumeDecomposition (B : Base) (cDec n : ℕ) (candidate : Candidate)
    (x : BitString) (q : ℕ) : Prop :=
  let base := lowerProxyBase B n candidate x q
  let R := pastExtensionCount B n candidate n base +
    strictExtensionCount B n (triple x q candidate.1)
  (2 : ℚ) ^ (-(cDec : ℤ)) * R ≤ strictExtensionCount B n base ∧
  (strictExtensionCount B n base : ℚ) ≤ (2 : ℚ) ^ (cDec : ℤ) * R

/-- Increasing the loss exponent preserves the upper volume decomposition. -/
lemma UpperVolumeDecomposition.mono (B : Base) {c1 c2 n : ℕ} (h : c1 ≤ c2)
    (candidate : Candidate) (x : BitString) (q : ℕ)
    (hU : UpperVolumeDecomposition B c1 n candidate x q) :
    UpperVolumeDecomposition B c2 n candidate x q := by
  dsimp [UpperVolumeDecomposition] at *
  obtain ⟨h1, h2⟩ := hU
  have hp : 0 ≤ (pastExtensionCount B n candidate q x : ℚ) +
    (strictExtensionCount B q (upperFutureBase B n candidate x q) : ℚ) := by positivity
  constructor
  · apply le_trans _ h1
    have hm : (2 : ℚ) ^ (-(c2 : ℤ)) ≤ (2 : ℚ) ^ (-(c1 : ℤ)) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    nlinarith
  · apply le_trans h2
    have hm : (2 : ℚ) ^ ((c1 : ℤ)) ≤ (2 : ℚ) ^ ((c2 : ℤ)) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    nlinarith

/-- Increasing the loss exponent preserves the lower volume decomposition. -/
lemma LowerVolumeDecomposition.mono (B : Base) {c1 c2 n : ℕ} (h : c1 ≤ c2)
    (candidate : Candidate) (x : BitString) (q : ℕ)
    (hL : LowerVolumeDecomposition B c1 n candidate x q) :
    LowerVolumeDecomposition B c2 n candidate x q := by
  dsimp [LowerVolumeDecomposition] at *
  obtain ⟨h1, h2⟩ := hL
  have hp : 0 ≤ ((pastExtensionCount B n candidate n (lowerProxyBase B n candidate x q) +
    strictExtensionCount B n (triple x q candidate.1) : ℕ) : ℚ) := by positivity
  constructor
  · apply le_trans _ h1
    have hm : (2 : ℚ) ^ (-(c2 : ℤ)) ≤ (2 : ℚ) ^ (-(c1 : ℤ)) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    nlinarith
  · apply le_trans h2
    have hm : (2 : ℚ) ^ ((c1 : ℤ)) ≤ (2 : ℚ) ^ ((c2 : ℤ)) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    nlinarith

/-- Is there an event of a program of length at most `n` at tick `u`? -/
def hasShortEvent (B : Base) (n u : ℕ) : Bool :=
  (eventAt B u).any (fun e ↦ decide (e.2.2.1.length ≤ n))

/-- The last tick `u ≤ t` that carries an event of a program of length at most `n` (default 0). -/
def replayTick (B : Base) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => if hasShortEvent B n (t + 1) then t + 1 else replayTick B n t

/-- The program of the event at a tick (default `[]`). -/
def eventProgram (B : Base) (u : ℕ) : BitString :=
  ((eventAt B u).map (fun e ↦ e.2.2.1)).getD []

/-- The candidate recovered by replaying the enumeration up to tick `t`. -/
def replayMarker (B : Base) (n t : ℕ) : Candidate :=
  (eventProgram B (replayTick B n t), replayTick B n t)

/-- For sufficiently large cutoffs, replay at or after the marker tick returns the true marker.
Blueprint node `key:decompositions`. -/
theorem replayMarker_eq_markerCandidate (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ t ≥ markerTick B n,
      replayMarker B n t = markerCandidate B n := by
  obtain ⟨n₁, hn₁, hstab⟩ := last_program_stabilizes_short_descriptions B
  obtain ⟨n₂, hn₂, hlater⟩ := last_program_stabilizes_short_descriptions_no_later B
  refine ⟨max n₁ n₂, le_trans hn₁ (le_max_left _ _), ?_⟩
  intro n hn t ht
  have hvalid := (hstab n (le_trans (le_max_left _ _) hn)).1
  obtain ⟨hlen, i, x, hev⟩ :=
    (canonical_enumeration_spec_candidate B n (markerCandidate B n)).mp hvalid
  have hev' : eventAt B (markerTick B n) = some (markerTick B n, i, lastProgram B n, x) := hev
  have hlen' : (lastProgram B n).length ≤ n := hlen
  have hshort : hasShortEvent B n (markerTick B n) = true := by
    simp [hasShortEvent, hev', hlen']
  have hbase : replayTick B n (markerTick B n) = markerTick B n := by
    cases hm : markerTick B n with
    | zero => rfl
    | succ m =>
      rw [hm] at hshort
      simp [replayTick, hshort]
  have hstep : ∀ u ≥ markerTick B n, replayTick B n u = markerTick B n := by
    intro u hu
    induction u, hu using Nat.le_induction with
    | base => exact hbase
    | succ u hu ih =>
      have hnot : hasShortEvent B n (u + 1) = false := by
        cases he : eventAt B (u + 1) with
        | none => simp [hasShortEvent, he]
        | some e =>
          obtain ⟨e1, e2, e3, e4⟩ := e
          have hsound := canonical_enumeration_spec_sound B he
          obtain rfl : e1 = u + 1 := hsound.1
          have hlt := hlater n (le_trans (le_max_right _ _) hn) (u + 1) (by omega) e2 e3 e4 he
          simpa [hasShortEvent, he] using Nat.not_le_of_lt hlt
      simp [replayTick, hnot, ih]
  have h1 := hstep t ht
  have h2 : eventProgram B (markerTick B n) = lastProgram B n := by
    simp [eventProgram, hev']
  simp [replayMarker, h1, h2, markerCandidate]

private theorem hasShortEvent_computable (B : Base) :
    Computable (fun p : ℕ × ℕ ↦ hasShortEvent B p.1 p.2) := by
  have hev : Computable (fun p : ℕ × ℕ ↦ eventAt B p.2) :=
    (canonical_enumeration_spec_tables B).2.2.comp Computable.snd
  have hprim : Primrec (fun q : (ℕ × ℕ) × TimedEvent ↦ decide (q.2.2.2.1.length ≤ q.1.1)) :=
    (Primrec.nat_le.comp (Primrec.list_length.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.fst.comp Primrec.fst)).decide
  have h : Computable (fun p : ℕ × ℕ ↦ @Option.casesOn TimedEvent (fun _ ↦ Bool)
      (eventAt B p.2) false (fun e ↦ decide (e.2.2.1.length ≤ p.1))) :=
    Computable.option_casesOn hev (Computable.const false) hprim.to_comp
  exact h.of_eq (fun p ↦ by
    cases hp : eventAt B p.2 <;> simp [hasShortEvent, hp])

private theorem replayTick_computable (B : Base) :
    Computable (fun p : ℕ × ℕ ↦ replayTick B p.1 p.2) := by
  have hs := hasShortEvent_computable B
  have hadd : Computable₂ (fun a b : ℕ ↦ a + b) := Primrec.nat_add.to_comp
  have hA : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦ q.1.1) :=
    Computable.fst.comp Computable.fst
  have hR1 : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦ q.2.1) :=
    Computable.fst.comp Computable.snd
  have hR2 : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦ q.2.2) :=
    Computable.snd.comp Computable.snd
  have hsucc : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦ q.2.1 + 1) :=
    hadd.comp hR1 (Computable.const 1)
  have hargs : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦ (q.1.1, q.2.1 + 1)) := hA.pair hsucc
  have h1 : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦ hasShortEvent B q.1.1 (q.2.1 + 1)) := by
    exact (hs.comp hargs).of_eq (fun _ ↦ rfl)
  have hstep : Computable₂ (fun (a : ℕ × ℕ) (r : ℕ × ℕ) ↦
      cond (hasShortEvent B a.1 (r.1 + 1)) (r.1 + 1) r.2) :=
    Computable.cond h1 hsucc hR2
  have hrec := Computable.nat_rec (f := fun p : ℕ × ℕ ↦ p.2) (g := fun _ ↦ (0 : ℕ))
    (h := fun (a : ℕ × ℕ) (r : ℕ × ℕ) ↦ cond (hasShortEvent B a.1 (r.1 + 1)) (r.1 + 1) r.2)
    Computable.snd (Computable.const 0) hstep
  have heq : ∀ n t : ℕ, (Nat.rec (motive := fun _ ↦ ℕ) 0
      (fun y IH ↦ cond (hasShortEvent B n (y + 1)) (y + 1) IH) t) = replayTick B n t := by
    intro n t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [replayTick, ← ih]
      cases hshort : hasShortEvent B n (t + 1) <;> simp [hshort]
  refine hrec.of_eq (fun p ↦ ?_)
  exact heq p.1 p.2

private theorem eventProgram_computable (B : Base) : Computable (eventProgram B) := by
  have hev : Computable (eventAt B) := (canonical_enumeration_spec_tables B).2.2
  have hprog : Computable₂ (fun (_ : ℕ) (e : TimedEvent) ↦ e.2.2.1) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp
  have hmap : Computable (fun u : ℕ ↦ Option.map (fun e : TimedEvent ↦ e.2.2.1) (eventAt B u)) :=
    Computable.option_map hev hprog
  exact Computable.option_getD hmap (Computable.const ([] : BitString))

/-- The candidate obtained by finite enumeration replay is computable in the cutoff and tick. -/
theorem replayMarker_computable (B : Base) :
    Computable (fun p : ℕ × ℕ ↦ replayMarker B p.1 p.2) := by
  have ht := replayTick_computable B
  have hp := eventProgram_computable B
  have h1 : Computable (fun p : ℕ × ℕ ↦ eventProgram B (replayTick B p.1 p.2)) := by
    exact (hp.comp ht).of_eq (fun _ ↦ rfl)
  exact h1.pair ht

/-- There is a computable replay that recovers the true marker at every later tick.
Blueprint node `key:decompositions`. -/
lemma exists_computable_marker_replay (B : Base) :
    ∃ rep : ℕ → ℕ → Candidate, Computable (fun p : ℕ × ℕ ↦ rep p.1 p.2) ∧
      ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ t ≥ markerTick B n, rep n t = markerCandidate B n := by
  obtain ⟨n₀, hn₀, h⟩ := replayMarker_eq_markerCandidate B
  exact ⟨replayMarker B, replayMarker_computable B, n₀, hn₀, h⟩

/-- The emission event of a program: its tick, position, and recorded output. -/
def programEmission (B : Base) (p : BitString) : Part TimedEvent :=
  (findEmission B p).bind (fun t ↦ Part.ofOption (eventAt B t))

/-- Searching for a program's emission event is partial computable. -/
theorem programEmission_partrec (B : Base) : Partrec (programEmission B) := by
  have h1 : Partrec (findEmission B) := canonical_enumeration_spec_search B
  have hev : Computable (fun pt : BitString × ℕ ↦ eventAt B pt.2) :=
    (canonical_enumeration_spec_tables B).2.2.comp Computable.snd
  have h2 : Partrec₂ (fun (_ : BitString) (t : ℕ) ↦ Part.ofOption (eventAt B t)) :=
    Computable.ofOption hev
  exact h1.bind h2

/-- The tower parameter read from the total scale `Q = 2^q`. -/
private def scaleTower (Q : ℕ) : ℕ := towerFloor (Nat.clog 2 Q)

/-- The upper-scale decoder applied to an emission event, for a scale `Q = 2^q`. -/
private def upperDecoderOutput (B : Base) (rep : ℕ → ℕ → Candidate) (Q : ℕ)
    (e : TimedEvent) : BitString :=
  pairCode (proxyBase (decodeFirst e.2.2.2)
    (computeStructuralProxy B (scaleTower Q) (rep (scaleTower Q) e.1) (Nat.clog 2 Q))
    (structuralProxyAlpha B (scaleTower Q) (rep (scaleTower Q) e.1) (Nat.clog 2 Q)))
    (decodeSecond e.2.2.2)

private theorem upperDecoderOutput_computable (B : Base) (rep : ℕ → ℕ → Candidate)
    (hrepc : Computable (fun p : ℕ × ℕ ↦ rep p.1 p.2)) :
    Computable (fun r : ℕ × TimedEvent ↦ upperDecoderOutput B rep r.1 r.2) := by
  have hz : Computable (fun r : ℕ × TimedEvent ↦ r.2.2.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp
  have ht : Computable (fun r : ℕ × TimedEvent ↦ r.2.1) :=
    Computable.fst.comp Computable.snd
  have hQ : Computable (fun r : ℕ × TimedEvent ↦ r.1) := Computable.fst
  have hq : Computable (fun r : ℕ × TimedEvent ↦ Nat.clog 2 r.1) :=
    Kolmogorov.clogTwo_computable.comp hQ
  have hn : Computable (fun r : ℕ × TimedEvent ↦ scaleTower r.1) := tower_floor_computable.comp hq
  have hnt : Computable (fun r : ℕ × TimedEvent ↦ (scaleTower r.1, r.2.1)) := hn.pair ht
  have hcand : Computable (fun r : ℕ × TimedEvent ↦ rep (scaleTower r.1) r.2.1) := by
    exact (hrepc.comp hnt).of_eq (fun _ ↦ rfl)
  have hcq : Computable (fun r : ℕ × TimedEvent ↦
      (rep (scaleTower r.1) r.2.1, Nat.clog 2 r.1)) := hcand.pair hq
  have hargs : Computable (fun r : ℕ × TimedEvent ↦
      (scaleTower r.1, (rep (scaleTower r.1) r.2.1, Nat.clog 2 r.1))) := hn.pair hcq
  have hproxy : Computable (fun r : ℕ × TimedEvent ↦
      computeStructuralProxy B (scaleTower r.1) (rep (scaleTower r.1) r.2.1)
        (Nat.clog 2 r.1)) := by
    exact ((compute_structural_proxy B).1.comp hargs).of_eq (fun _ ↦ rfl)
  have halpha : Computable (fun r : ℕ × TimedEvent ↦
      structuralProxyAlpha B (scaleTower r.1) (rep (scaleTower r.1) r.2.1)
        (Nat.clog 2 r.1)) := by
    exact ((compute_structural_proxy B).2.1.comp hargs).of_eq (fun _ ↦ rfl)
  have hx : Computable (fun r : ℕ × TimedEvent ↦ decodeFirst r.2.2.2.2) :=
    decodeFirst_computable.comp hz
  have hs : Computable (fun r : ℕ × TimedEvent ↦ decodeSecond r.2.2.2.2) :=
    decodeSecond_computable.comp hz
  have hxp : Computable (fun r : ℕ × TimedEvent ↦ (decodeFirst r.2.2.2.2,
      computeStructuralProxy B (scaleTower r.1) (rep (scaleTower r.1) r.2.1)
        (Nat.clog 2 r.1))) := hx.pair hproxy
  have hxpP : Computable (fun r : ℕ × TimedEvent ↦ pairCode (decodeFirst r.2.2.2.2)
      (computeStructuralProxy B (scaleTower r.1) (rep (scaleTower r.1) r.2.1)
        (Nat.clog 2 r.1))) := by
    exact (pairCode_computable.comp hxp).of_eq (fun _ ↦ rfl)
  have hbitsα : Computable (fun r : ℕ × TimedEvent ↦ bits (structuralProxyAlpha B (scaleTower r.1)
      (rep (scaleTower r.1) r.2.1) (Nat.clog 2 r.1))) := bits_computable.1.comp halpha
  have hbase : Computable (fun r : ℕ × TimedEvent ↦ proxyBase (decodeFirst r.2.2.2.2)
      (computeStructuralProxy B (scaleTower r.1) (rep (scaleTower r.1) r.2.1)
        (Nat.clog 2 r.1))
      (structuralProxyAlpha B (scaleTower r.1) (rep (scaleTower r.1) r.2.1)
        (Nat.clog 2 r.1))) := by
    exact (pairCode_computable.comp (hxpP.pair hbitsα)).of_eq (fun _ ↦ rfl)
  exact (pairCode_computable.comp (hbase.pair hs)).of_eq (fun _ ↦ rfl)

/-- The scale `Q = h + |p|` read from the code `pairCode (bits h) p`. -/
private def paddedProgramScale (c : BitString) : ℕ :=
  (decodeNat (decodeFirst c)).getD 0 + (decodeSecond c).length

private theorem paddedProgramScale_computable : Computable paddedProgramScale := by
  have h1 : Computable (fun c : BitString ↦ (decodeNat (decodeFirst c)).getD 0) :=
    Computable.option_getD (bits_computable.2.comp decodeFirst_computable) (Computable.const 0)
  have h2 : Computable (fun c : BitString ↦ (decodeSecond c).length) :=
    Computable.list_length.comp decodeSecond_computable
  have hadd : Computable₂ (fun a b : ℕ ↦ a + b) := Primrec.nat_add.to_comp
  exact hadd.comp h1 h2

/-- The upper-scale decoder: read `h` and the program `p`, replay the emission of `p`. -/
private def upperDecoder (B : Base) (rep : ℕ → ℕ → Candidate) (c : BitString) : Part BitString :=
  (programEmission B (decodeSecond c)).map (upperDecoderOutput B rep (paddedProgramScale c))

private theorem upperDecoder_partrec (B : Base) (rep : ℕ → ℕ → Candidate)
    (hrepc : Computable (fun p : ℕ × ℕ ↦ rep p.1 p.2)) : Partrec (upperDecoder B rep) := by
  have hf : Partrec (fun c : BitString ↦ programEmission B (decodeSecond c)) :=
    (programEmission_partrec B).comp decodeSecond_computable
  have hg : Computable₂ (fun (c : BitString) (e : TimedEvent) ↦
      upperDecoderOutput B rep (paddedProgramScale c) e) := by
    have h := (upperDecoderOutput_computable B rep hrepc).comp
      ((paddedProgramScale_computable.comp Computable.fst).pair Computable.snd)
    exact h
  exact hf.map hg

private theorem upperDecoder_eq_of_late_emission (B : Base) (rep : ℕ → ℕ → Candidate)
    (n₀ : ℕ) (hn₀ : 32 ≤ n₀)
    (hrep : ∀ n ≥ n₀, ∀ t ≥ markerTick B n, rep n t = markerCandidate B n) :
    ∀ n : ℕ, n₀ ≤ n → IsTower n → ∀ q : ℕ, TowerRange n q →
      ∀ x s p : BitString, produces B.V p [] (pairCode x s) → p.length ≤ extensionScale q →
      (∀ t i y, eventAt B t = some (t, i, p, y) → markerTick B n < t) →
      upperDecoder B rep (pairCode (bits (extensionScale q - p.length)) p) =
        Part.some (pairCode (upperFutureBase B n (markerCandidate B n) x q) s) := by
  intro n hn htower q hq x s p hprod hplen hlate
  obtain ⟨t, i, hev⟩ := (canonical_enumeration_spec_complete B p _).mp hprod
  have hsearch : t ∈ findEmission B p :=
    (canonical_enumeration_spec_search_eq B p t).mpr ⟨i, _, hev⟩
  have hfind : findEmission B p = Part.some t := Part.eq_some_iff.mpr hsearch
  have hmt : markerTick B n < t := hlate t i _ hev
  have hemit : programEmission B p = Part.some (t, i, p, pairCode x s) := by
    simp [programEmission, hfind, hev]
  have hQ : paddedProgramScale (pairCode (bits (extensionScale q - p.length)) p) = 2 ^ q := by
    have : extensionScale q = 2 ^ q := rfl
    simp only [paddedProgramScale, decodeFirst_pairCode, decodeSecond_pairCode, decodeNat_bits,
      Option.getD_some]
    omega
  have hfl : towerFloor q = n := tower_floor_eq n q (le_trans hn₀ hn) htower hq
  have hrm := hrep n hn t (le_of_lt hmt)
  have hout : upperDecoderOutput B rep (2 ^ q) (t, i, p, pairCode x s) =
      pairCode (upperFutureBase B n (markerCandidate B n) x q) s := by
    simp only [upperDecoderOutput, scaleTower, Nat.clog_pow 2 q (by norm_num), hfl, hrm,
      decodeFirst_pairCode, decodeSecond_pairCode, upperFutureBase]
  simp only [upperDecoder, decodeSecond_pairCode, hemit, hQ, Part.map_some, hout]

/-- Given a computable marker replay, a fixed partial computable decoder sends the
code `pairCode (bits (2^q - |p|)) p` of a late short program `p` for `pairCode x s` to
`pairCode (upperFutureBase ..) s`. Blueprint node `key:decompositions`. -/
lemma exists_upper_future_decoder
    (B : Base) (rep : ℕ → ℕ → Candidate) (n₀ : ℕ)
    (hrepc : Computable (fun p : ℕ × ℕ ↦ rep p.1 p.2)) (hn₀ : 32 ≤ n₀)
    (hrep : ∀ n ≥ n₀, ∀ t ≥ markerTick B n, rep n t = markerCandidate B n) :
    ∃ dec : BitString →. BitString, Partrec dec ∧
      ∀ n : ℕ, n₀ ≤ n → IsTower n → ∀ q : ℕ, TowerRange n q →
        ∀ x s p : BitString, produces B.V p [] (pairCode x s) → p.length ≤ extensionScale q →
        (∀ t i y, eventAt B t = some (t, i, p, y) → markerTick B n < t) →
        pairCode (upperFutureBase B n (markerCandidate B n) x q) s ∈
          dec (pairCode (bits (extensionScale q - p.length)) p) := by
  refine ⟨upperDecoder B rep, upperDecoder_partrec B rep hrepc, ?_⟩
  intro n hn htower q hq x s p hprod hplen hlate
  rw [upperDecoder_eq_of_late_emission B rep n₀ hn₀ hrep n hn htower q hq x s p hprod hplen hlate]
  exact Part.mem_some _

end Kolmogorov.Milovanov
