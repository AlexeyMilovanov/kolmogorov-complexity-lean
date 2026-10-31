/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.StructuralProxy.Towers

/-!
# Structural Proxy Properties and Symmetry

This module proves the main structural properties of the proxy algorithm (`key:proxy`).
It establishes the computability and totality of the proxy generation, its length bound,
exactness at the true marker, and the carrier identity. It then leverages these to prove
the constant-error symmetry transfer theorem (`key:symmetry`), bounding the difference
between conditional complexities involving the true target and the proxy. These results
are used by downstream modules to maintain complexity invariants across crossing phases.
-/

namespace Kolmogorov.Milovanov

/-- The finite crossing supremum agrees with a bounded natural recursion. -/
private lemma proxyCrossingIndex_eq_sup (β : ℕ → ℕ) (k : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0
      (fun j m => if j ≤ β j then max j m else m) k =
        ((Finset.range k).filter (fun j => j ≤ β j)).sup id := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Finset.range_add_one, Finset.filter_insert]
    by_cases hk : k ≤ β k
    · simp [hk, Finset.sup_insert, ih]
    · simp [hk, ih]

/-- A bounded crossing search is computable uniformly in a computable family of tables. -/
private lemma proxyCrossingIndex_computable
    {σ : Type} [Primcodable σ] {β : σ → ℕ → ℕ} {q : σ → ℕ}
    (hβ : Computable₂ β) (hq : Computable q) :
    Computable (fun p => proxyCrossingIndex (q p) (β p)) := by
  have hstep : Computable₂ (fun (p : σ) (u : ℕ × ℕ) =>
      bif decide (u.1 ≤ β p u.1) then max u.1 u.2 else u.2) := by
    have hj : Computable (fun p : σ × (ℕ × ℕ) => p.2.1) :=
      Computable.fst.comp Computable.snd
    have hv : Computable (fun p : σ × (ℕ × ℕ) => β p.1 p.2.1) :=
      hβ.comp Computable.fst hj
    exact Computable.cond (Primrec.nat_le.decide.to_comp.comp hj hv)
      (Primrec.nat_max.to_comp.comp hj (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  have hrec := Computable.nat_rec (Computable.succ.comp hq) (Computable.const 0) hstep
  exact hrec.of_eq (fun p => by
    simp only [Bool.cond_decide]
    exact proxyCrossingIndex_eq_sup (β p) (q p + 1))

/-- Compose the finite candidate prefix-minimum interface with computable arguments. -/
private lemma candidatePrefixComplexity_computable (B : Base)
    {σ : Type} [Primcodable σ] {n : σ → ℕ} {candidate : σ → Candidate}
    {a b : σ → BitString} (hn : Computable n) (hc : Computable candidate)
    (ha : Computable a) (hb : Computable b) :
    Computable (fun p => candidatePrefixComplexity B (n p) (candidate p) (a p) (b p)) := by
  exact (canonical_enumeration_spec_prefix_computable B).2.2.comp
    (hn.pair (hc.pair (ha.pair hb)))

/-- The binary numeric pair is computable in both coordinates. -/
private lemma proxyPairCode_computable : Computable₂ proxyPair := by
  change Computable (fun p : ℕ × ℕ => pairCode (bits p.1) (bits p.2))
  exact Computable₂.comp pairCode_computable (bits_computable.1.comp Computable.fst)
    (bits_computable.1.comp Computable.snd)

/-- All bounded alpha entries are computable uniformly, including for false candidates. -/
private lemma boundedProxyAlpha_computable (B : Base) :
    Computable (fun p : (ℕ × Candidate × ℕ) × ℕ =>
      boundedProxyAlpha B p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hn : Computable (fun p : (ℕ × Candidate × ℕ) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hc : Computable (fun p : (ℕ × Candidate × ℕ) × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hq : Computable (fun p : (ℕ × Candidate × ℕ) × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  exact candidatePrefixComplexity_computable B hn hc
    (proxyPairCode_computable.comp hq Computable.snd)
    (bits_computable.1.comp hn)

/-- All bounded beta entries are computable from the bounded alpha table. -/
private lemma boundedProxyBeta_computable (B : Base) :
    Computable (fun p : (ℕ × Candidate × ℕ) × ℕ =>
      boundedProxyBeta B p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hn : Computable (fun p : (ℕ × Candidate × ℕ) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hc : Computable (fun p : (ℕ × Candidate × ℕ) × ℕ => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hq : Computable (fun p : (ℕ × Candidate × ℕ) × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  exact candidatePrefixComplexity_computable B hn hc
    (Computable₂.comp pairCode_computable
      (proxyPairCode_computable.comp hq Computable.snd)
      (bits_computable.1.comp (boundedProxyAlpha_computable B)))
    (bits_computable.1.comp hq)

/-- The finite proxy algorithm and both selected complexity bounds are computable.
Blueprint node `key:proxy`. Totality does not assume that the candidate is true. -/
theorem compute_structural_proxy (B : Base) :
    Computable (fun p : ℕ × Candidate × ℕ => computeStructuralProxy B p.1 p.2.1 p.2.2) ∧
    Computable (fun p : ℕ × Candidate × ℕ => structuralProxyAlpha B p.1 p.2.1 p.2.2) ∧
    Computable (fun p : ℕ × Candidate × ℕ => structuralProxyBeta B p.1 p.2.1 p.2.2) ∧
    Computable (fun p : ℕ × Candidate × ℕ => structuralProxyDelta B p.1 p.2.1 p.2.2) := by
  have hn : Computable (fun p : ℕ × Candidate × ℕ => p.1) := Computable.fst
  have hc : Computable (fun p : ℕ × Candidate × ℕ => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hq : Computable (fun p : ℕ × Candidate × ℕ => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hindex : Computable (fun p : ℕ × Candidate × ℕ =>
      structuralProxyIndex B p.1 p.2.1 p.2.2) :=
    proxyCrossingIndex_computable
      (boundedProxyBeta_computable B).to₂ hq
  have hvalid : Computable (fun p : ℕ × Candidate × ℕ =>
      validCandidate B p.1 p.2.1) :=
    (canonical_enumeration_spec_prefix_computable B).1.comp hn hc
  have hproxy : Computable (fun p : ℕ × Candidate × ℕ =>
      computeStructuralProxy B p.1 p.2.1 p.2.2) := by
    exact (Computable.cond hvalid
      (proxyPairCode_computable.comp hq hindex) (Computable.const [])).of_eq
        (fun p => by simp only [computeStructuralProxy, Bool.cond_eq_ite])
  have halpha : Computable (fun p : ℕ × Candidate × ℕ =>
      structuralProxyAlpha B p.1 p.2.1 p.2.2) :=
    candidatePrefixComplexity_computable B hn hc hproxy (bits_computable.1.comp hn)
  have hbeta : Computable (fun p : ℕ × Candidate × ℕ =>
      structuralProxyBeta B p.1 p.2.1 p.2.2) :=
    candidatePrefixComplexity_computable B hn hc
      (Computable₂.comp pairCode_computable hproxy (bits_computable.1.comp halpha))
      (bits_computable.1.comp hq)
  exact ⟨hproxy, halpha, hbeta, ComputableReals.primrec_natSubInt.to_comp.comp hbeta halpha⟩

/-- A valid proxy record explicitly carries its target as the first binary component.
Blueprint node `key:proxy`. This projection also works for valid false candidates. -/
theorem compute_structural_proxy_first (B : Base) (n : ℕ) (candidate : Candidate) (q : ℕ)
    (hc : validCandidate B n candidate = true) :
    decodeNat (decodeFirst (computeStructuralProxy B n candidate q)) = some q := by
  simp [computeStructuralProxy, hc, proxyPair, decodeFirst_pairCode, decodeNat_bits]

private theorem proxyPair_eq (q j : ℕ) :
    proxyPair q j = pairCode (bits q) (bits j) := rfl

private theorem length_proxyPair (q j : ℕ) :
    (proxyPair q j).length = (bits q).length * 2 + 1 + (bits j).length := by
  rw [proxyPair_eq, length_pairCode]
  omega

private theorem length_bits_le_log2 (n : ℕ) :
    (bits n).length ≤ Nat.log2 (n + 1) + 1 := by
  have : n + 1 < 2 ^ (Nat.log2 (n + 1) + 1) := by
    rw [← Nat.log2_lt (by omega)]
    apply Nat.lt_succ_self
  have : n < 2 ^ (Nat.log2 (n + 1) + 1) := by omega
  apply length_bits_le_of_lt this

private theorem proxyCrossingIndex_le (q : ℕ) (β : ℕ → ℕ) :
    proxyCrossingIndex q β ≤ q := by
  unfold proxyCrossingIndex
  apply Finset.sup_le
  intro b hb
  simp only [proxyCrossingIndices, Finset.mem_filter, Finset.mem_range] at hb
  have h_id : id b = b := rfl
  omega

private theorem nat_log2_mono {a b : ℕ} (h : a ≤ b) :
    a.log2 ≤ b.log2 := by
  by_cases ha : a = 0
  · subst ha; exact Nat.zero_le _
  · apply (Nat.le_log2 (by omega)).mpr
    have : 2 ^ a.log2 ≤ a := (Nat.le_log2 ha).mp (le_refl _)
    omega

/-- The true-marker proxy has logarithmic length with a fixed explicit coefficient.
Blueprint node `key:proxy`. -/
theorem compute_structural_proxy_length (B : Base) :
    ∃ cLen n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, IsTower n → ∀ (candidate : Candidate) (q : ℕ),
      candidate = markerCandidate B n → TowerRange n q →
      (computeStructuralProxy B n candidate q).length ≤ cLen * Nat.log2 (q + 2) + cLen := by
  use 4, 32
  refine ⟨by omega, ?_⟩
  intro n hn hn_tower candidate q hc hq
  rw [computeStructuralProxy]
  split_ifs with h_val
  · rw [length_proxyPair]
    have h1 : (bits q).length ≤ Nat.log2 (q + 1) + 1 :=
      length_bits_le_log2 q
    have h2 : (bits (structuralProxyIndex B n candidate q)).length ≤
        Nat.log2 (structuralProxyIndex B n candidate q + 1) + 1 :=
      length_bits_le_log2 _
    have h3 : structuralProxyIndex B n candidate q ≤ q :=
      proxyCrossingIndex_le _ _
    have h_log_mono : Nat.log2 (structuralProxyIndex B n candidate q + 1) ≤
        Nat.log2 (q + 1) := by
      apply nat_log2_mono (by omega)
    have h_log_le : Nat.log2 (q + 1) ≤ Nat.log2 (q + 2) := by
      apply nat_log2_mono (by omega)
    omega
  · simp

private lemma lt_two_pow_of_exponential_gap (L : ℕ) (hL : 64 ≤ L) :
    40 * (L * L) < 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    nlinarith

/-- All arguments of the bounded table fit the marker cutoff once `n` is large enough,
uniformly in the index and in every alpha below the literal budget. -/
private lemma length_proxy_args_le (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ q, TowerRange n q → ∀ j ≤ q,
      ∀ α, α ≤ literalBound B (proxyPair q j) →
        2 * ((proxyPair q j).length + (bits n).length) < n ∧
        2 * ((pairCode (proxyPair q j) (bits α)).length + (bits q).length) < n := by
  refine ⟨2 ^ (64 + B.cD), ?_, ?_⟩
  · calc
      32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (64 + B.cD) := Nat.pow_le_pow_right (by decide) (by omega)
  · intro n hn q hq j hj α hα
    let L := Nat.log2 n
    let X := L * L
    have hnpos : n ≠ 0 := by
      have := Nat.two_pow_pos (64 + B.cD)
      omega
    have hL : 64 + B.cD ≤ L := (Nat.le_log2 hnpos).2 hn
    have hLn : 2 ^ L ≤ n := Nat.log2_self_le hnpos
    have hnL : n < 2 ^ (L + 1) := Nat.lt_log2_self
    have hqpow : q < 2 ^ (X + L) := by
      calc
        q < n ^ L := hq.2
        _ < (2 ^ (L + 1)) ^ L := Nat.pow_lt_pow_left hnL (by omega)
        _ = 2 ^ (X + L) := by rw [← pow_mul]; congr 1; dsimp [X]; ring
    have hqpow' : q < 2 ^ (X + L + 1) :=
      lt_trans hqpow (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
    have hbq : (bits q).length ≤ X + L + 1 := length_bits_le_of_lt hqpow'
    have hbj : (bits j).length ≤ X + L + 1 :=
      length_bits_le_of_lt (lt_of_le_of_lt hj hqpow')
    have hbn : (bits n).length ≤ L + 1 := length_bits_le_of_lt hnL
    have hY : (proxyPair q j).length ≤ 3 * X + 3 * L + 4 := by
      rw [proxyPair, literal_and_tuple_code_interface_pair]
      omega
    have hclog : Nat.clog 2 ((proxyPair q j).length + 2) ≤
        (proxyPair q j).length + 2 :=
      Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    have hα' : α ≤ 3 * (proxyPair q j).length + 4 + B.cD := by
      dsimp [literalBound] at hα
      omega
    have hba : (bits α).length ≤ α + 1 := length_bits_le α
    have hpair := literal_and_tuple_code_interface_pair (proxyPair q j) (bits α)
    have hX : 64 * L ≤ X := by dsimp [X]; nlinarith
    have hsmall : 40 * X < n :=
      lt_of_lt_of_le (lt_two_pow_of_exponential_gap L (by omega)) hLn
    constructor <;> omega

private lemma candidate_prefix_le_of_args_bound (B : Base) (n : ℕ)
    (candidate : Candidate) (a b : BitString) :
    candidatePrefixComplexity B n candidate a b ≤ literalBound B a := by
  unfold candidatePrefixComplexity
  split_ifs
  · exact (canonical_enumeration_spec_prefix_bound B _ a b).2
  · exact le_rfl

/-- Every bounded table entry and the chosen alpha and beta are exact at the true marker.
Blueprint node `key:proxy`. No conversion from an infinite complexity is used. -/
theorem compute_structural_proxy_exact (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, IsTower n → ∀ (candidate : Candidate) (q : ℕ),
      candidate = markerCandidate B n → TowerRange n q →
      ExactProxyTable B n q (boundedProxyAlpha B n candidate q)
        (boundedProxyBeta B n candidate q) ∧
      KP B.D (computeStructuralProxy B n candidate q) (bits n) =
        (structuralProxyAlpha B n candidate q : ENat) ∧
      KP B.D (pairCode (computeStructuralProxy B n candidate q)
        (bits (structuralProxyAlpha B n candidate q))) (bits q) =
          (structuralProxyBeta B n candidate q : ENat) := by
  obtain ⟨nL, hnL, hL⟩ := length_proxy_args_le B
  obtain ⟨nM, hnM, hM⟩ := marker_stage_prefix_complexity_exact_candidate B
  obtain ⟨nV, hnV, hV⟩ := last_program_stabilizes_short_descriptions B
  refine ⟨max nL (max nM nV), le_trans hnL (le_max_left _ _), ?_⟩
  intro n hn _ candidate q hc hq
  subst candidate
  have hnL' : nL ≤ n := by omega
  have hnM' : nM ≤ n := by omega
  have hnV' : nV ≤ n := by omega
  have hvalid := (hV n hnV').1
  have htab : ExactProxyTable B n q (boundedProxyAlpha B n (markerCandidate B n) q)
      (boundedProxyBeta B n (markerCandidate B n) q) := by
    intro j hj
    have hα : boundedProxyAlpha B n (markerCandidate B n) q j ≤
        literalBound B (proxyPair q j) :=
      candidate_prefix_le_of_args_bound B n (markerCandidate B n) _ _
    obtain ⟨hshortα, hshortβ⟩ := hL n hnL' q hq j hj _ hα
    exact ⟨(hM n hnM' (markerCandidate B n) hvalid rfl _ _ hshortα).symm,
      (hM n hnM' (markerCandidate B n) hvalid rfl _ _ hshortβ).symm⟩
  have hj : structuralProxyIndex B n (markerCandidate B n) q ≤ q :=
    proxyCrossingIndex_le q _
  refine ⟨htab, ?_, ?_⟩
  · simpa only [structuralProxyAlpha, computeStructuralProxy, hvalid, ite_true,
      boundedProxyAlpha] using (htab _ hj).1
  · simpa only [structuralProxyBeta, structuralProxyAlpha, computeStructuralProxy,
      hvalid, ite_true, boundedProxyBeta, boundedProxyAlpha] using (htab _ hj).2

/-- Re-pairs the proxy record with its alpha value and the beta bound shifted by delta. -/
private def offsetMap (delta : ℕ) (w : BitString) : BitString :=
  pairCode (decodeFirst w) (pairCode (decodeSecond w)
    (bits (decodeSecondNat (decodeFirst w) + delta)))

private theorem offsetMap_computable (delta : ℕ) : Computable (offsetMap delta) := by
  have h1 : Computable (fun w : BitString ↦ decodeFirst w) := decodeFirst_computable
  have h2 : Computable (fun w : BitString ↦ decodeSecond w) := decodeSecond_computable
  have h3 : Computable (fun w : BitString ↦ decodeSecondNat (decodeFirst w)) :=
    decodeSecondNat_computable.comp h1
  have h4 : Computable (fun w : BitString ↦ delta) := Computable.const delta
  have h5 : Computable (fun w : BitString ↦ (decodeSecondNat (decodeFirst w), delta)) :=
    Computable.pair h3 h4
  have h6 : Computable (fun w : BitString ↦ decodeSecondNat (decodeFirst w) + delta) :=
    Computable.of_eq (Computable.comp Primrec.nat_add.to_comp h5) (by intro w; rfl)
  have h7 : Computable (fun w : BitString ↦ bits (decodeSecondNat (decodeFirst w) + delta)) :=
    bits_computable.1.comp h6
  have h8 : Computable (fun w : BitString ↦
      (decodeSecond w, bits (decodeSecondNat (decodeFirst w) + delta))) :=
    Computable.pair h2 h7
  have h9 : Computable (fun w : BitString ↦ pairCode (decodeSecond w)
      (bits (decodeSecondNat (decodeFirst w) + delta))) :=
    Computable.of_eq (pairCode_computable.comp h8) (by intro w; rfl)
  have h10 : Computable (fun w : BitString ↦ (decodeFirst w, pairCode (decodeSecond w)
      (bits (decodeSecondNat (decodeFirst w) + delta)))) :=
    Computable.pair h1 h9
  exact Computable.of_eq (pairCode_computable.comp h10) (by intro w; rfl)

private theorem offsetMap_apply (q j α δ : ℕ) (w : BitString)
    (h_w : w = pairCode (proxyPair q j) (bits α)) :
    offsetMap δ w = triple (proxyPair q j) α (bits (j + δ)) := by
  subst w
  simp only [offsetMap, decodeSecondNat, proxyPair, triple, decodeFirst_pairCode,
    decodeSecond_pairCode, decodeNat_bits, Option.getD_some]


/-- Adjoining both selected complexity values changes conditional complexity by a constant.
Blueprint node `key:proxy`. The carrier complexity is explicitly bound to a natural value. -/
theorem compute_structural_proxy_carrier (B : Base) :
    ∃ cCar n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, IsTower n → ∀ (candidate : Candidate) (q : ℕ),
      candidate = markerCandidate B n → TowerRange n q →
      let proxy := computeStructuralProxy B n candidate q
      let α := structuralProxyAlpha B n candidate q
      let β := structuralProxyBeta B n candidate q
      ∀ k : ℕ, KP B.D (proxyCarrier proxy α β) (bits n) = (k : ENat) →
        |(k : ℤ) - α| ≤ (cCar : ℤ) := by
  obtain ⟨cBeta, n1, q0, hn1, h1_cross⟩ := structural_proxy_crossing_finite B
  obtain ⟨n2, hn2, h2_exact⟩ := compute_structural_proxy_exact B
  obtain ⟨n3, hn3, h3_stab⟩ := last_program_stabilizes_short_descriptions B
  obtain ⟨cSS, hcSS⟩ := prefix_self_sufficiency_interface B
  obtain ⟨cPr, hcPr⟩ := KP_map_le B.D B.optimalD decodeFirst decodeFirst_computable
  have hoff : ∀ δ, ∃ c : ℕ, ∀ x y, KP B.D (offsetMap δ x) y ≤ KP B.D x y + c :=
    fun δ => KP_map_le B.D B.optimalD _ (offsetMap_computable δ)
  choose cO hcO using hoff
  let cOmax := (Finset.range (cBeta + 1)).sup cO
  let n₀ := max (max n1 n2) (max n3 q0)
  use max (cSS + cOmax) cPr, n₀
  refine ⟨by omega, ?_⟩
  intro n hn hT candidate q hc hq
  dsimp only
  intro k hk
  have hn1' : n1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn2' : n2 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn3' : n3 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hq0' : q0 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hq_ge : q0 ≤ q := le_trans hq0' hq.1
  have hv : validCandidate B n (markerCandidate B n) = true := (h3_stab n hn3').1
  subst hc
  have hproxy : computeStructuralProxy B n (markerCandidate B n) q =
      proxyPair q (structuralProxyIndex B n (markerCandidate B n) q) := by
    simp [computeStructuralProxy, hv]
  set j := structuralProxyIndex B n (markerCandidate B n) q
  have h_exact := (h2_exact n hn2' hT (markerCandidate B n) q rfl hq).1
  have h_cross := h1_cross n hn1' hT q hq_ge hq (boundedProxyAlpha B n (markerCandidate B n) q)
      (boundedProxyBeta B n (markerCandidate B n) q) h_exact
  have hj_le : j ≤ boundedProxyBeta B n (markerCandidate B n) q
      (structuralProxyIndex B n (markerCandidate B n) q) := h_cross.2.2.1
  have h_beta_lt : boundedProxyBeta B n (markerCandidate B n) q
      (structuralProxyIndex B n (markerCandidate B n) q) < j + 1 + cBeta := h_cross.2.2.2
  have h_alpha_eq : structuralProxyAlpha B n (markerCandidate B n) q =
      boundedProxyAlpha B n (markerCandidate B n) q j := by
    unfold structuralProxyAlpha boundedProxyAlpha
    rw [hproxy]
  have h_beta_eq : structuralProxyBeta B n (markerCandidate B n) q =
      boundedProxyBeta B n (markerCandidate B n) q j := by
    unfold structuralProxyBeta boundedProxyBeta
    rw [hproxy, h_alpha_eq]
  set α := structuralProxyAlpha B n (markerCandidate B n) q
  set β := structuralProxyBeta B n (markerCandidate B n) q
  have hj_le_beta : j ≤ β := by rw [h_beta_eq]; exact hj_le
  have h_beta_lt_j : β < j + 1 + cBeta := by rw [h_beta_eq]; exact h_beta_lt
  set δ := β - j
  have h_delta_le : δ ≤ cBeta := by omega
  have h_beta_delta : β = j + δ := by omega
  have h_carrier : proxyCarrier (computeStructuralProxy B n (markerCandidate B n) q) α β =
      offsetMap δ (pairCode (computeStructuralProxy B n (markerCandidate B n) q) (bits α)) := by
    simpa only [proxyCarrier, hproxy, h_beta_delta] using
      (offsetMap_apply q j α δ
        (pairCode (proxyPair q j) (bits α)) rfl).symm
  have h_upper1 : (k : ENat) ≤ KP B.D (pairCode (computeStructuralProxy B n (markerCandidate B n) q)
      (bits α)) (bits n) + cO δ := by
    rw [← hk, h_carrier]
    exact hcO δ (pairCode (computeStructuralProxy B n (markerCandidate B n) q) (bits α)) (bits n)
  have h_upper2 : KP B.D (pairCode (computeStructuralProxy B n (markerCandidate B n) q) (bits α))
      (bits n) ≤ (α : ENat) + cSS := by
    have h_alpha_KP : KP B.D (computeStructuralProxy B n (markerCandidate B n) q) (bits n) =
        (α : ENat) := (h2_exact n hn2' hT (markerCandidate B n) q rfl hq).2.1
    simpa only [h_alpha_KP] using
      (hcSS (computeStructuralProxy B n (markerCandidate B n) q)
        (bits n) α h_alpha_KP)
  have h_upper3 : (k : ENat) ≤ (α : ENat) + cSS + cO δ := by
    calc
      (k : ENat) ≤ KP B.D (pairCode (computeStructuralProxy B n (markerCandidate B n) q) (bits α))
        (bits n) + cO δ := h_upper1
      _ ≤ (α : ENat) + cSS + cO δ := by gcongr
  have h_cO_le : cO δ ≤ cOmax := by
    apply Finset.le_sup
    rw [Finset.mem_range]
    omega
  have h_upper4 : (k : ENat) ≤ (α : ENat) + (cSS + cOmax) := by
    calc
      (k : ENat) ≤ (α : ENat) + cSS + cO δ := h_upper3
      _ ≤ (α : ENat) + cSS + cOmax := by gcongr
      _ = (α : ENat) + (cSS + cOmax) := by
        simp only [add_assoc]
  have h_lower1 : (α : ENat) = KP B.D (computeStructuralProxy B n (markerCandidate B n) q) (bits n)
      := ((h2_exact n hn2' hT (markerCandidate B n) q rfl hq).2.1).symm
  have h_first : decodeFirst (proxyCarrier (computeStructuralProxy B n (markerCandidate B n) q) α β)
      = computeStructuralProxy B n (markerCandidate B n) q := by
    dsimp [proxyCarrier, triple]
    rw [decodeFirst_pairCode]
  have h_lower2 : KP B.D (computeStructuralProxy B n (markerCandidate B n) q) (bits n) ≤
      (k : ENat) + cPr := by
    rw [← h_first, ← hk]
    exact hcPr (proxyCarrier (computeStructuralProxy B n (markerCandidate B n) q) α β) (bits n)
  have h_lower3 : (α : ENat) ≤ (k : ENat) + cPr := by
    calc
      (α : ENat) = KP B.D (computeStructuralProxy B n (markerCandidate B n) q) (bits n) := h_lower1
      _ ≤ (k : ENat) + cPr := h_lower2
  have h_upper5 : k ≤ α + (cSS + cOmax) := by exact_mod_cast h_upper4
  have h_lower4 : α ≤ k + cPr := by exact_mod_cast h_lower3
  have h_max1 : cSS + cOmax ≤ max (cSS + cOmax) cPr := le_max_left _ _
  have h_max2 : cPr ≤ max (cSS + cOmax) cPr := le_max_right _ _
  have h_max1_Z : ((cSS + cOmax : ℕ) : ℤ) ≤ ((max (cSS + cOmax) cPr : ℕ) : ℤ) := by
    exact_mod_cast h_max1
  have h_max2_Z : (cPr : ℤ) ≤ ((max (cSS + cOmax) cPr : ℕ) : ℤ) := by exact_mod_cast h_max2
  apply abs_le.mpr
  constructor
  · have h_Z : (α : ℤ) ≤ (k : ℤ) + (cPr : ℤ) := by exact_mod_cast h_lower4
    linarith
  · have h_Z : (k : ℤ) ≤ (α : ℤ) + ((cSS + cOmax : ℕ) : ℤ) := by exact_mod_cast h_upper5
    linarith

/-- A single threshold gives all proxy properties with common length and carrier constants.
Blueprint node `key:proxy`. All constants precede the tower, candidate, and target. -/
theorem compute_structural_proxy_common (B : Base) :
    ∃ cLen cCar n₀ : ℕ, 32 ≤ n₀ ∧
      ∀ n ≥ n₀, IsTower n → ∀ (candidate : Candidate) (q : ℕ),
        candidate = markerCandidate B n → TowerRange n q →
        StructuralProxySpec B cLen cCar n candidate q := by
  obtain ⟨cLen, n1, hn1, h1⟩ := compute_structural_proxy_length B
  obtain ⟨n2, hn2, h2⟩ := compute_structural_proxy_exact B
  obtain ⟨cCar, n3, hn3, h3⟩ := compute_structural_proxy_carrier B
  obtain ⟨n4, hn4, h4⟩ := last_program_stabilizes_short_descriptions B
  let n₀ := max (max n1 n2) (max n3 n4)
  use cLen, cCar, n₀
  refine ⟨?_, ?_⟩
  · exact le_trans hn1 (le_max_of_le_left (le_max_left _ _))
  · intro n hn hnTower candidate q hc hq
    have hn1' : n ≥ n1 := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
    have hn2' : n ≥ n2 := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
    have hn3' : n ≥ n3 := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
    have hn4' : n ≥ n4 := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
    dsimp [StructuralProxySpec]
    refine ⟨h1 n hn1' hnTower candidate q hc hq, ?_, ?_, ?_, ?_,
      h3 n hn3' hnTower candidate q hc hq⟩
    · have hvalid : validCandidate B n (markerCandidate B n) = true := (h4 n hn4').1
      rw [hc]
      exact compute_structural_proxy_first B n (markerCandidate B n) q hvalid
    · exact (h2 n hn2' hnTower candidate q hc hq).1
    · exact (h2 n hn2' hnTower candidate q hc hq).2.1
    · exact (h2 n hn2' hnTower candidate q hc hq).2.2

private def proxyContextFromEncodedData : BitString → BitString := fun C1 =>
  let a := decodeFirst C1
  let a1 := decodeFirst a
  let a2 := decodeSecond a
  let q := decodeSecond (decodeSecond C1)
  let n := towerFloor (decodeNat q |>.getD 0)
  pairCode a1 (pairCode a2 (bits n))

private def proxyBaseFromEncodedData : BitString → BitString := fun P =>
  let proxy_alpha := decodeFirst P
  let proxy := decodeFirst proxy_alpha
  let alpha := decodeSecond proxy_alpha
  let x := decodeSecond P
  proxyBase x proxy (decodeNat alpha |>.getD 0)

private lemma proxy_context_from_encoded_data_computable :
    Computable proxyContextFromEncodedData := by
  have hP : Computable₂ pairCode := pairCode_computable
  apply hP.comp
  · exact decodeFirst_computable.comp (decodeFirst_computable.comp Computable.id)
  · apply hP.comp
    · exact decodeSecond_computable.comp (decodeFirst_computable.comp Computable.id)
    · apply bits_computable.1.comp
      apply tower_floor_computable.comp
      apply Computable.option_getD
      · exact bits_computable.2.comp (decodeSecond_computable.comp
          (decodeSecond_computable.comp Computable.id))
      · exact Computable.const 0

private lemma proxy_base_from_encoded_data_computable :
    Computable proxyBaseFromEncodedData := by
  have hP : Computable₂ pairCode := pairCode_computable
  unfold proxyBaseFromEncodedData proxyBase
  apply hP.comp
  · apply hP.comp
    · exact decodeSecond_computable.comp Computable.id
    · exact decodeFirst_computable.comp (decodeFirst_computable.comp Computable.id)
  · apply bits_computable.1.comp
    apply Computable.option_getD
    · exact bits_computable.2.comp (decodeSecond_computable.comp
        (decodeFirst_computable.comp Computable.id))
    · exact Computable.const 0

/-- Bounds the proxy symmetry difference from above given exact complexity values. -/
private theorem proxy_symmetry_diff_le_of_complexity_eqs (B : Base) :
    ∃ c1 c2 c3 c4 : ℕ, ∀ (q n α β k l : ℕ) (proxy x : BitString),
      towerFloor q = n →
      KP B.D proxy (bits n) = (α : ENat) →
      KP B.D (pairCode proxy (bits α)) (bits q) = (β : ENat) →
      KP B.D (proxyBase x proxy α) (bits q) = (k : ENat) →
      KP B.D (pairCode proxy x) (bits n) = (l : ENat) →
      ((k : ℤ) - β) - ((l : ℤ) - α) ≤ ((c1 + c2 + c3 + c4 : ℕ) : ℤ) := by
  obtain ⟨c1, hc1⟩ := KP_map_le B.D B.optimalD proxyBaseFromEncodedData
    proxy_base_from_encoded_data_computable
  obtain ⟨c2, hc2⟩ := conditional_prefix_chain_interface B
  obtain ⟨c3, hc3⟩ := KP_cond_map_le B.D B.optimalD proxyContextFromEncodedData
    proxy_context_from_encoded_data_computable
  obtain ⟨c4, hc4⟩ := conditional_prefix_chain_interface_lower B
  use c1, c2, c3, c4
  intro q n α β k l proxy x hn h_alpha h_beta h_k h_l
  have step1 : (k : ENat) ≤ KP B.D (pairCode (pairCode proxy (bits α)) x) (bits q) + c1 := by
    have H1 := hc1 (pairCode (pairCode proxy (bits α)) x) (bits q)
    have h_eq : proxyBaseFromEncodedData (pairCode (pairCode proxy (bits α)) x)
        = proxyBase x proxy α := by
      unfold proxyBaseFromEncodedData proxyBase
      dsimp
      simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeNat_bits, Option.getD_some]
    rw [h_eq, h_k] at H1
    exact H1
  have step2 : (k : ENat) ≤ (β : ENat) + KP B.D x (triple (pairCode proxy (bits α)) β (bits q))
      + c2 + c1 := by
    have H1 := hc2 (pairCode proxy (bits α)) x (bits q) β h_beta
    rw [h_beta] at H1
    calc (k : ENat) ≤ KP B.D (pairCode (pairCode proxy (bits α)) x) (bits q) + c1 := step1
      _ ≤ (β : ENat) + KP B.D x (triple (pairCode proxy (bits α)) β (bits q)) + c2 + c1 := by
        gcongr
  have step3 : (k : ENat) ≤ (β : ENat) + KP B.D x (triple proxy α (bits n)) + c3 + c2 + c1 := by
    have H1 := hc3 x (triple (pairCode proxy (bits α)) β (bits q))
    have h_eq : proxyContextFromEncodedData
        (triple (pairCode proxy (bits α)) β (bits q)) = triple proxy α (bits n) := by
      unfold proxyContextFromEncodedData triple
      dsimp
      simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeNat_bits, Option.getD_some, hn]
    rw [h_eq] at H1
    calc (k : ENat) ≤ (β : ENat) + KP B.D x (triple (pairCode proxy (bits α)) β (bits q))
        + c2 + c1 := step2
      _ ≤ (β : ENat) + (KP B.D x (triple proxy α (bits n)) + c3) + c2 + c1 := by gcongr
      _ = (β : ENat) + KP B.D x (triple proxy α (bits n)) + c3 + c2 + c1 := by ring
  have step4 : (k : ENat) + α ≤ (β : ENat) + (l : ENat) + c4 + c3 + c2 + c1 := by
    have H1 := hc4 proxy x (bits n) α h_alpha
    calc
      (k : ENat) + α ≤ (β : ENat) + KP B.D x (triple proxy α (bits n)) + c3 + c2 + c1 + α := by
        gcongr
      _ = (β : ENat) + (KP B.D x (triple proxy α (bits n)) + α) + c3 + c2 + c1 := by ring
      _ = (β : ENat) + ((α : ENat) + KP B.D x (triple proxy α (bits n))) + c3 + c2 + c1 := by
        ring
      _ ≤ (β : ENat) + (KP B.D (pairCode proxy x) (bits n) + c4) + c3 + c2 + c1 := by
        have step4_sub : (α : ENat) + KP B.D x (triple proxy α (bits n)) ≤
            KP B.D (pairCode proxy x) (bits n) + c4 := by
          rw [h_alpha] at H1
          exact H1
        gcongr
      _ = (β : ENat) + (l : ENat) + c4 + c3 + c2 + c1 := by rw [h_l]; ring
  have H' : (k + α : ENat) ≤ (β + l + c4 + c3 + c2 + c1 : ℕ) := by
    have h_reorder : (β : ENat) + (l : ENat) + c4 + c3 + c2 + c1 =
        ((β + l + c4 + c3 + c2 + c1 : ℕ) : ENat) := by
      exact_mod_cast rfl
    calc (k + α : ENat) = (k : ENat) + α := by exact_mod_cast rfl
      _ ≤ β + (l : ENat) + c4 + c3 + c2 + c1 := step4
      _ = (β + l + c4 + c3 + c2 + c1 : ℕ) := h_reorder
  have H'' : k + α ≤ β + l + (c1 + c2 + c3 + c4) := by
    have H3 : k + α ≤ β + l + c4 + c3 + c2 + c1 := by exact_mod_cast H'
    linarith
  have H_Z : (k : ℤ) + α ≤ β + l + (c1 + c2 + c3 + c4 : ℕ) := by
    exact_mod_cast H''
  linarith

/-- Upper bound without absolute value. -/
private theorem proxy_symmetry_upper_bound (B : Base) :
    ∃ cSym n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, IsTower n → ∀ (candidate : Candidate) (q : ℕ),
      candidate = markerCandidate B n → TowerRange n q →
      let proxy := computeStructuralProxy B n candidate q
      let α := structuralProxyAlpha B n candidate q
      let β := structuralProxyBeta B n candidate q
      ∀ (x : BitString) (k l : ℕ),
        KP B.D (proxyBase x proxy α) (bits q) = (k : ENat) →
        KP B.D (pairCode proxy x) (bits n) = (l : ENat) →
        ((k : ℤ) - β) - ((l : ℤ) - α) ≤ (cSym : ℤ) := by
  obtain ⟨c1, c2, c3, c4, H_core⟩ := proxy_symmetry_diff_le_of_complexity_eqs B
  obtain ⟨cLen, cCar, n0, hn0, H_proxy⟩ := compute_structural_proxy_common B
  use c1 + c2 + c3 + c4, max 32 n0
  have hn_ge_32 : 32 ≤ max 32 n0 := le_max_left 32 n0
  refine ⟨hn_ge_32, fun n hn htower candidate q hcand hrange x k l hk hl => ?_⟩
  have hn' : n ≥ n0 := le_trans (le_max_right 32 n0) hn
  have hn32 : 32 ≤ n := le_trans (le_max_left 32 n0) hn
  have H_spec := H_proxy n hn' htower candidate q hcand hrange
  have h_alpha : KP B.D (computeStructuralProxy B n candidate q) (bits n) =
      (structuralProxyAlpha B n candidate q : ENat) := H_spec.2.2.2.1
  have h_beta : KP B.D (pairCode (computeStructuralProxy B n candidate q)
      (bits (structuralProxyAlpha B n candidate q))) (bits q) =
      (structuralProxyBeta B n candidate q : ENat) := H_spec.2.2.2.2.1
  have h_floor : towerFloor q = n := by
    exact tower_floor_eq n q hn32 htower hrange
  exact H_core q n (structuralProxyAlpha B n candidate q) (structuralProxyBeta B n candidate q) k l
    (computeStructuralProxy B n candidate q) x h_floor h_alpha h_beta hk hl

/-- The carrier identity and recovery of the target from the proxy suffice for the lower
symmetry bound. All transformations, and hence their complexity costs, are fixed. -/
private theorem proxy_symmetry_diff_ge_of_complexity_eqs (B : Base) :
    ∃ c : ℕ, ∀ (q n α β cCar k l : ℕ) (proxy x : BitString),
      decodeFirst proxy = bits q →
      KP B.D (pairCode proxy (bits α)) (bits q) = (β : ENat) →
      (∀ kZ : ℕ, KP B.D (proxyCarrier proxy α β) (bits n) = (kZ : ENat) →
        |(kZ : ℤ) - α| ≤ (cCar : ℤ)) →
      KP B.D (proxyBase x proxy α) (bits q) = (k : ENat) →
      KP B.D (pairCode proxy x) (bits n) = (l : ENat) →
      ((l : ℤ) - α) - ((k : ℤ) - β) ≤ ((cCar + c : ℕ) : ℤ) := by
  let project : BitString → BitString := fun w =>
    pairCode (decodeFirst (decodeFirst w)) (decodeSecond w)
  let context : BitString → BitString := fun w =>
    pairCode (pairCode (decodeFirst w) (decodeFirst (decodeSecond w)))
      (pairCode (decodeSecond (decodeSecond w)) (decodeFirst (decodeFirst w)))
  let rearrange : BitString → BitString := fun w =>
    pairCode (pairCode (decodeSecond (decodeFirst w)) (decodeSecond w))
      (decodeFirst (decodeFirst w))
  have hP : Computable₂ pairCode := pairCode_computable
  have hproject : Computable project :=
    hP.comp (decodeFirst_computable.comp decodeFirst_computable) decodeSecond_computable
  have hcontext : Computable context :=
    hP.comp (hP.comp decodeFirst_computable
      (decodeFirst_computable.comp decodeSecond_computable))
      (hP.comp (decodeSecond_computable.comp decodeSecond_computable)
        (decodeFirst_computable.comp decodeFirst_computable))
  have hrearrange : Computable rearrange :=
    hP.comp (hP.comp (decodeSecond_computable.comp decodeFirst_computable)
      decodeSecond_computable) (decodeFirst_computable.comp decodeFirst_computable)
  obtain ⟨c1, hc1⟩ := KP_map_le B.D B.optimalD project hproject
  obtain ⟨c2, hc2⟩ := conditional_prefix_chain_interface B
  obtain ⟨c3, hc3⟩ := KP_cond_drop_right_le B.D B.optimalD
  obtain ⟨c4, hc4⟩ := KP_cond_map_le B.D B.optimalD context hcontext
  obtain ⟨c5, hc5⟩ := conditional_prefix_chain_interface_lower B
  obtain ⟨c6, hc6⟩ := KP_map_le B.D B.optimalD rearrange hrearrange
  refine ⟨c1 + c2 + c3 + c4 + c5 + c6, ?_⟩
  intro q n α β cCar k l proxy x hfirst hβ hcar hk hl
  let Z := proxyCarrier proxy α β
  let a := pairCode proxy (bits α)
  let C1 := triple a β (bits q)
  obtain ⟨kZ, hkZ⟩ := prefix_complexity_finite_value B Z (bits n)
  have hproject_eq : project (pairCode Z x) = pairCode proxy x := by
    simp only [project, Z, proxyCarrier, triple, decodeFirst_pairCode,
      decodeSecond_pairCode]
  have hcontext_eq : context Z = C1 := by
    simp only [context, Z, C1, a, proxyCarrier, triple, decodeFirst_pairCode,
      decodeSecond_pairCode, hfirst]
  have hrearrange_eq : rearrange (proxyBase x proxy α) = pairCode a x := by
    simp only [rearrange, proxyBase, a, decodeFirst_pairCode, decodeSecond_pairCode]
  have h1 : (l : ENat) ≤ KP B.D (pairCode Z x) (bits n) + c1 := by
    have h := hc1 (pairCode Z x) (bits n)
    rwa [hproject_eq, hl] at h
  have h2 := hc2 Z x (bits n) kZ hkZ
  rw [hkZ] at h2
  have h3 : KP B.D x (triple Z kZ (bits n)) ≤ KP B.D x Z + c3 :=
    hc3 x Z (pairCode (bits kZ) (bits n))
  have h4 : KP B.D x Z ≤ KP B.D x C1 + c4 := by
    have h := hc4 x Z
    rwa [hcontext_eq] at h
  have h5 : (β : ENat) + KP B.D x C1 ≤ KP B.D (pairCode a x) (bits q) + c5 := by
    have h := hc5 a x (bits q) β hβ
    rwa [hβ] at h
  have h6 : KP B.D (pairCode a x) (bits q) ≤ (k : ENat) + c6 := by
    have h := hc6 (proxyBase x proxy α) (bits q)
    rwa [hrearrange_eq, hk] at h
  have hupper : (l : ENat) ≤ (kZ : ENat) + KP B.D x C1 + c4 + c3 + c2 + c1 := by
    calc
      (l : ENat) ≤ KP B.D (pairCode Z x) (bits n) + c1 := h1
      _ ≤ (kZ : ENat) + KP B.D x (triple Z kZ (bits n)) + c2 + c1 := by gcongr
      _ ≤ (kZ : ENat) + (KP B.D x Z + c3) + c2 + c1 := by gcongr
      _ ≤ (kZ : ENat) + (KP B.D x C1 + c4 + c3) + c2 + c1 := by gcongr
      _ = (kZ : ENat) + KP B.D x C1 + c4 + c3 + c2 + c1 := by ring
  have htotal : (l : ENat) + β ≤ (kZ : ENat) + k + c6 + c5 + c4 + c3 + c2 + c1 := by
    calc
      (l : ENat) + β ≤ ((kZ : ENat) + KP B.D x C1 + c4 + c3 + c2 + c1) + β := by
        gcongr
      _ = (kZ : ENat) + ((β : ENat) + KP B.D x C1) + c4 + c3 + c2 + c1 := by ring
      _ ≤ (kZ : ENat) + (KP B.D (pairCode a x) (bits q) + c5) + c4 + c3 + c2 + c1 := by
        gcongr
      _ ≤ (kZ : ENat) + ((k : ENat) + c6 + c5) + c4 + c3 + c2 + c1 := by gcongr
      _ = (kZ : ENat) + k + c6 + c5 + c4 + c3 + c2 + c1 := by ring
  have hnat : l + β ≤ kZ + k + c6 + c5 + c4 + c3 + c2 + c1 := by
    exact_mod_cast htotal
  have hcarrier := (abs_le.mp (hcar kZ hkZ)).2
  push_cast
  omega

/-- Lower bound without absolute value. -/
private theorem proxy_symmetry_lower_bound (B : Base) :
    ∃ cSym n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, IsTower n → ∀ (candidate : Candidate) (q : ℕ),
      candidate = markerCandidate B n → TowerRange n q →
      let proxy := computeStructuralProxy B n candidate q
      let α := structuralProxyAlpha B n candidate q
      let β := structuralProxyBeta B n candidate q
      ∀ (x : BitString) (k l : ℕ),
        KP B.D (proxyBase x proxy α) (bits q) = (k : ENat) →
        KP B.D (pairCode proxy x) (bits n) = (l : ENat) →
        ((l : ℤ) - α) - ((k : ℤ) - β) ≤ (cSym : ℤ) := by
  obtain ⟨c, hcore⟩ := proxy_symmetry_diff_ge_of_complexity_eqs B
  obtain ⟨cLen, cCar, n₀, hn₀, hproxy⟩ := compute_structural_proxy_common B
  refine ⟨cCar + c, n₀, hn₀, ?_⟩
  intro n hn htower candidate q hcand hrange
  dsimp only
  intro x k l hk hl
  have hs := hproxy n hn htower candidate q hcand hrange
  simp only [StructuralProxySpec] at hs
  have hfirst : decodeFirst (computeStructuralProxy B n candidate q) = bits q := by
    have hdecode := hs.2.1
    unfold decodeNat at hdecode
    dsimp only at hdecode
    split_ifs at hdecode with hcanon
    have hval := Option.some.inj hdecode
    exact hcanon.symm.trans (congrArg bits hval)
  exact hcore q n (structuralProxyAlpha B n candidate q)
    (structuralProxyBeta B n candidate q) cCar k l (computeStructuralProxy B n candidate q) x
    hfirst hs.2.2.2.2.1 hs.2.2.2.2.2 hk hl

/-- The proxy transfers conditional symmetry with constant, rather than logarithmic, error.
Blueprint node `key:symmetry`. The string `x` is unrestricted; both differences are integers. -/
theorem structural_proxy_symmetry_transfer (B : Base) :
    ∃ cSym n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, IsTower n → ∀ (candidate : Candidate) (q : ℕ),
      candidate = markerCandidate B n → TowerRange n q →
      let proxy := computeStructuralProxy B n candidate q
      let α := structuralProxyAlpha B n candidate q
      let β := structuralProxyBeta B n candidate q
      ∀ (x : BitString) (k l : ℕ),
        KP B.D (proxyBase x proxy α) (bits q) = (k : ENat) →
        KP B.D (pairCode proxy x) (bits n) = (l : ENat) →
        |((k : ℤ) - β) - ((l : ℤ) - α)| ≤ (cSym : ℤ) := by
  obtain ⟨c1, n1, hn1, h1⟩ := proxy_symmetry_upper_bound B
  obtain ⟨c2, n2, hn2, h2⟩ := proxy_symmetry_lower_bound B
  use max c1 c2, max n1 n2
  refine ⟨le_trans hn1 (le_max_left n1 n2),
    fun n hn htower candidate q hcand hrange x' k' l' hk' hl' ↦ ?_⟩
  have h1_eval :=
    h1 n (le_trans (le_max_left n1 n2) hn) htower candidate q hcand hrange x' k' l' hk' hl'
  have h2_eval :=
    h2 n (le_trans (le_max_right n1 n2) hn) htower candidate q hcand hrange x' k' l' hk' hl'
  rw [abs_le]
  constructor
  · have h2_rearranged : - (c2 : ℤ) ≤ ((k' : ℤ) - (structuralProxyBeta B n candidate q : ℤ)) -
        ((l' : ℤ) - (structuralProxyAlpha B n candidate q : ℤ)) := by
      calc
        - (c2 : ℤ) ≤ - (((l' : ℤ) - (structuralProxyAlpha B n candidate q : ℤ)) -
          ((k' : ℤ) - (structuralProxyBeta B n candidate q : ℤ))) := by exact neg_le_neg h2_eval
        _ = ((k' : ℤ) - (structuralProxyBeta B n candidate q : ℤ)) -
          ((l' : ℤ) - (structuralProxyAlpha B n candidate q : ℤ)) := by ring
    have hc2 : - ((max c1 c2 : ℕ) : ℤ) ≤ - (c2 : ℤ) := by
      have : (c2 : ℤ) ≤ ((max c1 c2 : ℕ) : ℤ) := by exact_mod_cast le_max_right c1 c2
      exact neg_le_neg this
    exact le_trans hc2 h2_rearranged
  · have hc1 : (c1 : ℤ) ≤ ((max c1 c2 : ℕ) : ℤ) := by exact_mod_cast le_max_left c1 c2
    exact le_trans h1_eval hc1

end Kolmogorov.Milovanov
