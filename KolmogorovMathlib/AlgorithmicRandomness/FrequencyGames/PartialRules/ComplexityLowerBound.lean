/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.PartialRules.MisesChurchDaley

/-!
# Complexity Lower Bound

No Mises–Church–Daley random sequence has prefixes of logarithmic plain complexity: the main
declaration `not_exists_isMisesChurchDaleyRandom_plainK_log` states that there is no
Mises–Church–Daley random sequence `w` with `C(w_0 … w_{n-1}) ≤ c log n + c` for all `n`.  The proof
follows Merkle's argument: from the short descriptions of the prefixes it enumerates candidate
prefixes, and by induction on the exponent of a polynomial bound on their number it builds a
partial computable predictor that guesses more than half of the bits of `w` correctly infinitely
often.

The module contains the counting lemmas for chains of selected positions, the construction of the
winning predictor from an enumeration of candidate prefixes, and the final induction.  It
formalizes Theorem 188 of the book by Shen, Uspensky and Vereshchagin.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

open Classical in
/-- Auxiliary for the Merkle proof of `not_exists_isMisesChurchDaleyRandom_plainK_log`: the number
of
correct predictions of the partial predictor `P` among the first `n` bits of `w`, i.e. the number of
positions `i < n` with `w i ∈ P (w_0 … w_{i-1})` (a position on which `P` hangs counts as an
error). -/
private noncomputable def plk_correct
    (P : BitString →. Bool) (w : CantorSeq) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => w i ∈ P (cantorPrefix w i)).card

/-- Auxiliary for the Merkle proof of `not_exists_isMisesChurchDaleyRandom_plainK_log`: `P` is a
*winning partial predictor* for `w`.  It is partial computable, defined on all prefixes of `w`, and
for some `d > 0` it guesses at least `(1/2 + d) n` of the first `n` bits of `w` correctly, for
infinitely many `n`. -/
private def plk_PredictorWins
    (P : BitString →. Bool) (w : CantorSeq) : Prop :=
  Partrec P ∧ (∀ n, (P (cantorPrefix w n)).Dom) ∧
    ∃ d : ℝ, 0 < d ∧ ∃ᶠ n : ℕ in atTop,
      (1 / 2 + d) * (n : ℝ) ≤ (plk_correct P w n : ℝ)

/-- On a sequence on all of whose prefixes `r` is defined, a prefix lies in the set of the partial
rule `r` exactly when `r` takes the value `true` on it. -/
private lemma plk_mem_ruleSet
    (r : BitString →. Bool) (w : CantorSeq) (hdom : ∀ n, (r (cantorPrefix w n)).Dom) (t : ℕ) :
    cantorPrefix w t ∈ partialRuleSet r ↔ true ∈ r (cantorPrefix w t) := by
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨fun y hy => ?_, h⟩
    have hlen : y.length ≤ t := by simpa using hy.length_le
    have hy' : y = cantorPrefix w y.length := by
      rw [List.prefix_iff_eq_take] at hy
      rw [hy, cantorPrefix_take w y.length t hlen, cantorPrefix_length]
    rw [hy']
    exact hdom _

open Classical in
/-- One more step of the chain of selected prefixes. -/
private lemma plk_chain_succ (R : Set BitString)
    (w : CantorSeq) (t : ℕ) :
    selectChain R w (t + 1)
      = selectChain R w t ++ (if cantorPrefix w t ∈ R then [w t] else []) := by
  unfold selectChain
  rw [cantorPrefix_succ, selectedBits_append_singleton]

/-- The chain of selected prefixes starts with the empty string. -/
private lemma plk_chain_zero (R : Set BitString)
    (w : CantorSeq) : selectChain R w 0 = [] := by
  simp [selectChain, selectedBits, selectedAux, cantorPrefix]

open Classical in
/-- One more position: the number of correct predictions increases by one iff the prediction at
that position is correct. -/
private lemma plk_correct_succ
    (P : BitString →. Bool) (w : CantorSeq) (t : ℕ) :
    plk_correct P w (t + 1) =
      plk_correct P w t +
        (if w t ∈ P (cantorPrefix w t) then 1 else 0) := by
  unfold plk_correct
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : w t ∈ P (cantorPrefix w t)
  · have hnot : t ∉ (Finset.range t).filter (fun i => w i ∈ P (cantorPrefix w i)) := by simp
    simp [h, Finset.card_insert_of_notMem hnot]
  · simp [h]

open Classical in
/-- The two rules "select where `P` predicts `true`" and "select where `P` predicts `false`" split
the positions into two parts, and the correct predictions are the `true`s of the first selected
prefix together with the `false`s of the second. -/
private lemma plk_identities
    (P : BitString →. Bool) (w : CantorSeq) (hdom : ∀ n, (P (cantorPrefix w n)).Dom) (t : ℕ) :
    (selectChain (partialRuleSet P) w t).length +
        (selectChain (partialRuleSet (fun x => (P x).map not)) w t).length = t ∧
      plk_correct P w t +
          (selectChain (partialRuleSet (fun x => (P x).map not)) w t).count true =
        (selectChain (partialRuleSet P) w t).count true +
          (selectChain (partialRuleSet (fun x => (P x).map not)) w t).length := by
  have hdom' : ∀ n, ((fun x => (P x).map not) (cantorPrefix w n)).Dom := by
    intro n
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 (hdom n)
    exact Part.dom_iff_mem.2 ⟨not y, Part.mem_map _ hy⟩
  induction t with
  | zero =>
    simp [plk_chain_zero,
      plk_correct]
  | succ t ih =>
    rw [plk_chain_succ,
      plk_chain_succ,
      plk_correct_succ,
      plk_mem_ruleSet P w hdom t,
      plk_mem_ruleSet
        (fun x => (P x).map not) w hdom' t]
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 (hdom t)
    have hmem : ∀ c, c ∈ P (cantorPrefix w t) ↔ c = b := fun c =>
      ⟨fun h => Part.mem_unique h hb, fun h => h ▸ hb⟩
    have h1 : (true ∈ P (cantorPrefix w t)) ↔ true = b := hmem true
    have h2 : (true ∈ (fun x => (P x).map not) (cantorPrefix w t)) ↔ false = b := by
      change true ∈ Part.map not (P (cantorPrefix w t)) ↔ _
      rw [Part.mem_map_iff]
      constructor
      · rintro ⟨a, ha, hna⟩
        have := (hmem a).1 ha
        subst this
        cases a <;> simp_all
      · intro hb'
        exact ⟨b, hb, by simp [← hb']⟩
    have h3 : (w t ∈ P (cantorPrefix w t)) ↔ w t = b := hmem (w t)
    obtain ⟨ih1, ih2⟩ := ih
    simp only [h1, h2, h3]
    cases b <;> cases hwt : w t <;> simp <;> omega

/-- A stream prefix set of unbounded length determines an infinite sequence of which every member
is an initial segment. -/
private lemma plk_ofPrefixSet_infinite
    {T : Set BitString} (hT : IsStreamPrefixSet T) (h_unbdd : ¬ ∃ M, ∀ x ∈ T, x.length ≤ M) :
    ∃ u : CantorSeq, BitStream.ofPrefixSet T hT = .infinite u ∧ ∀ x ∈ T, IsCantorPrefix x u := by
  classical
  refine ⟨fun i => (Classical.choose (exists_mem_length_gt h_unbdd i)).get
      ⟨i, (Classical.choose_spec (exists_mem_length_gt h_unbdd i)).2⟩, ?_,
    isCantorPrefix_of_mem hT h_unbdd⟩
  unfold BitStream.ofPrefixSet
  rw [dite_eq_right h_unbdd]

/-- If the selected stream is finite or has limit frequency `1/2`, then for long selected prefixes
the number of ones is within `ε` of half the length (the converse of the criterion used for
Theorem 173). -/
private lemma plk_chain_balanced
    (R : Set BitString) (w : CantorSeq) (h : FiniteOrFreq (1 / 2) (selectStream R w))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ t : ℕ, L ≤ (selectChain R w t).length →
      |((selectChain R w t).count true : ℝ) - ((selectChain R w t).length : ℝ) / 2|
        ≤ ε * ((selectChain R w t).length : ℝ) := by
  classical
  have hT : IsStreamPrefixSet (chainPrefixSet (selectChain R w)) :=
    isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)
  have hsel : selectStream R w
      = BitStream.ofPrefixSet (chainPrefixSet (selectChain R w)) hT := rfl
  by_cases hb : ∃ M, ∀ x ∈ chainPrefixSet (selectChain R w), x.length ≤ M
  · obtain ⟨M, hM⟩ := hb
    refine ⟨M + 1, fun t ht => ?_⟩
    exfalso
    have := hM (selectChain R w t) ⟨t, List.prefix_rfl⟩
    omega
  · obtain ⟨u, hu, hpre⟩ :=
      plk_ofPrefixSet_infinite hT hb
    rw [hsel, hu] at h
    have h' : Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 (1 / 2)) := h
    rw [Metric.tendsto_atTop] at h'
    obtain ⟨N, hN⟩ := h' ε hε
    refine ⟨max N 1, fun t ht => ?_⟩
    have hcp : cantorPrefix u (selectChain R w t).length = selectChain R w t := by
      have hmem : selectChain R w t ∈ chainPrefixSet (selectChain R w) := ⟨t, List.prefix_rfl⟩
      exact (isCantorPrefix_iff_cantorPrefix_eq _ _).1 (hpre _ hmem)
    have hn1 : (1 : ℝ) ≤ ((selectChain R w t).length : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) ht
    have hnpos : (0 : ℝ) < ((selectChain R w t).length : ℝ) := by linarith
    have hd := hN (selectChain R w t).length (le_trans (le_max_left _ _) ht)
    have hfreq : (freqOne u (selectChain R w t).length : ℝ)
        = ((selectChain R w t).count true : ℝ) / ((selectChain R w t).length : ℝ) := by
      unfold freqOne
      rw [hcp]
      push_cast
      rfl
    rw [Real.dist_eq, hfreq] at hd
    have halg : ((selectChain R w t).count true : ℝ) / ((selectChain R w t).length : ℝ) - 1 / 2
        = (((selectChain R w t).count true : ℝ) - ((selectChain R w t).length : ℝ) / 2) /
          ((selectChain R w t).length : ℝ) := by
      field_simp
    rw [halg, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos] at hd
    exact hd.le

/-- Short selected prefixes are harmless: the bound on the number of ones holds with an additive
constant for all `t`. -/
private lemma plk_abs_bound
    (R : Set BitString) (w : CantorSeq) (ε : ℝ) (hε : 0 ≤ ε) (L : ℕ)
    (h : ∀ t : ℕ, L ≤ (selectChain R w t).length →
      |((selectChain R w t).count true : ℝ) - ((selectChain R w t).length : ℝ) / 2|
        ≤ ε * ((selectChain R w t).length : ℝ))
    (t : ℕ) :
    |((selectChain R w t).count true : ℝ) - ((selectChain R w t).length : ℝ) / 2|
      ≤ ε * ((selectChain R w t).length : ℝ) + L := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  by_cases hL : L ≤ (selectChain R w t).length
  · have := h t hL
    linarith
  · replace hL := not_le.1 hL
    have hc : ((selectChain R w t).count true : ℝ) ≤ ((selectChain R w t).length : ℝ) := by
      exact_mod_cast List.count_le_length
    have hc0 : (0 : ℝ) ≤ ((selectChain R w t).count true : ℝ) := Nat.cast_nonneg _
    have hl : ((selectChain R w t).length : ℝ) < L := by exact_mod_cast hL
    have hl0 : (0 : ℝ) ≤ ((selectChain R w t).length : ℝ) := Nat.cast_nonneg _
    have hel := mul_nonneg hε hl0
    rw [abs_le]
    constructor <;> linarith

/-- The real-number arithmetic of step 1. -/
private lemma plk_arith
    (d : ℝ) (hd : 0 < d) (L1 L0 T t : ℕ) (hT : 8 * ((L1 : ℝ) + L0) / d < T) (htT : T ≤ t)
    (c k1 l1 k0 l0 : ℝ) (hl : l1 + l0 = t) (hc : c + k0 = k1 + l0)
    (b1 : |k1 - l1 / 2| ≤ d / 4 * l1 + L1) (b0 : |k0 - l0 / 2| ≤ d / 4 * l0 + L0)
    (ht : (1 / 2 + d) * t ≤ c) : False := by
  rw [abs_le] at b1 b0
  have hdt : 8 * ((L1 : ℝ) + L0) < d * T := by
    have := (div_lt_iff₀ hd).1 hT
    linarith
  have hdt' : d * (T : ℝ) ≤ d * t := mul_le_mul_of_nonneg_left (by exact_mod_cast htT) hd.le
  have hsplit : d * l1 + d * l0 = d * t := by rw [← mul_add, hl]
  have hL1 : (0 : ℝ) ≤ L1 := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L0 := Nat.cast_nonneg _
  have hexp : (1 / 2 + d) * (t : ℝ) = t / 2 + d * t := by ring
  have hb1 : k1 - l1 / 2 ≤ d / 4 * l1 + L1 := b1.2
  have hb0 : -(d / 4 * l0 + L0) ≤ k0 - l0 / 2 := b0.1
  have hd1 : d / 4 * l1 = d * l1 / 4 := by ring
  have hd0 : d / 4 * l0 = d * l0 / 4 := by ring
  rw [hd1] at hb1
  rw [hd0] at hb0
  rw [hexp] at ht
  linarith

/-- Step 1 of the proof of `not_exists_isMisesChurchDaleyRandom_plainK_log`: the partial
analogue of Theorem 169.  If a partial computable predictor is defined on all prefixes of `w` and
guesses at least a fraction `1/2 + d` of the first `n` bits correctly for infinitely many `n`, then
`w` is not Mises-Church-Daley random: one of the two Church-Daley admissible rules "select the terms
where `P` predicts `b`" (`b ∈ {0, 1}`) selects an unbalanced sequence.  (Both selected streams
balanced or finite would give `correct(n) / n → 1/2`.) -/
private lemma plk_predictor
    {P : BitString →. Bool} {w : CantorSeq}
    (h : plk_PredictorWins P w) :
    ¬ IsMisesChurchDaleyRandom w := by
  obtain ⟨hP, hdom, d, hd, hfreq⟩ := h
  intro hw
  have hnot : Computable₂ (fun (_ : BitString) (b : Bool) => !b) :=
    (Primrec.not.comp Primrec.snd).to_comp
  have hP' : Partrec (fun x => (P x).map not) := hP.map hnot
  have h1 := hw P hP
  have h2 := hw (fun x => (P x).map not) hP'
  obtain ⟨L1, hL1⟩ := plk_chain_balanced _ w h1
    (d / 4) (by positivity)
  obtain ⟨L0, hL0⟩ := plk_chain_balanced _ w h2
    (d / 4) (by positivity)
  obtain ⟨T, hT⟩ := exists_nat_gt (8 * ((L1 : ℝ) + L0) / d)
  obtain ⟨t, htT, ht⟩ := Filter.frequently_atTop.1 hfreq T
  obtain ⟨hlen, hcor⟩ :=
    plk_identities P w hdom t
  have hlen' : (((selectChain (partialRuleSet P) w t).length : ℕ) : ℝ) +
      (((selectChain (partialRuleSet (fun x => (P x).map not)) w t).length : ℕ) : ℝ) = t := by
    exact_mod_cast hlen
  have hcor' : ((plk_correct P w t : ℕ) : ℝ) +
      (((selectChain (partialRuleSet (fun x => (P x).map not)) w t).count true : ℕ) : ℝ) =
      (((selectChain (partialRuleSet P) w t).count true : ℕ) : ℝ) +
      (((selectChain (partialRuleSet (fun x => (P x).map not)) w t).length : ℕ) : ℝ) := by
    exact_mod_cast hcor
  exact plk_arith d hd L1 L0 T t hT htT _ _ _ _ _
    hlen' hcor'
    (plk_abs_bound _ w (d / 4) (by positivity) L1
      hL1 t)
    (plk_abs_bound _ w (d / 4) (by positivity) L0
      hL0 t)
    ht

/-- Auxiliary for step 2: the test "the `k`-th string enumerated by `en j` extends `y`". -/
private def plk_aux_test
    (en : ℕ → ℕ → Option BitString) (j : ℕ) (y : BitString) (k : ℕ) : Bool :=
  ((en j k).map fun x => decide (y = x.take y.length)).getD false

/-- Auxiliary for step 2: bit number `|y|` of the `k`-th string enumerated by `en j`. -/
private def plk_aux_out
    (en : ℕ → ℕ → Option BitString) (j : ℕ) (y : BitString) (k : ℕ) : Bool :=
  ((en j k).map fun x => x.getD y.length false).getD false

/-- Auxiliary for step 2: the candidate predictor.  On `y`, find the stage `j` (the least `j` with
`|y| < n j`), then the first enumerated string of `E_j` extending `y`, and predict its bit `|y|`. -/
private noncomputable def plk_aux_pred
    (n : ℕ → ℕ) (en : ℕ → ℕ → Option BitString) (y : BitString) : Part Bool :=
  (Nat.rfind fun j => Part.some (decide (y.length < n j))).bind fun j =>
    (Nat.rfind fun k => Part.some
        (plk_aux_test en j y k)).map
      fun k => plk_aux_out en j y k

private lemma plk_aux_test_iff
    (en : ℕ → ℕ → Option BitString) (j : ℕ) (y : BitString) (k : ℕ) :
    plk_aux_test en j y k = true ↔
      ∃ x, en j k = some x ∧ y <+: x := by
  unfold plk_aux_test
  rcases h : en j k with _ | x
  · simp
  · simp [List.prefix_iff_eq_take]

private lemma plk_aux_out_eq
    (en : ℕ → ℕ → Option BitString) (j : ℕ) (y : BitString) (k : ℕ) (x : BitString)
    (h : en j k = some x) :
    plk_aux_out en j y k = x.getD y.length false :=
        by
  simp [plk_aux_out, h]

private lemma plk_aux_stage_mem
    (n : ℕ → ℕ) (i j : ℕ) (hj : i < n j) (hmin : ∀ m < j, n m ≤ i) :
    j ∈ Nat.rfind (fun j => Part.some (decide (i < n j))) := by
  refine Nat.mem_rfind.2 ⟨by simp [hj], fun {m} hm => ?_⟩
  have := hmin m hm
  simp [Nat.not_lt.2 this]

private lemma plk_aux_pred_mem
    (n : ℕ → ℕ) (en : ℕ → ℕ → Option BitString) (y : BitString) (j k : ℕ)
    (hj : j ∈ Nat.rfind (fun j => Part.some (decide (y.length < n j))))
    (hk : k ∈ Nat.rfind (fun k => Part.some
      (plk_aux_test en j y k))) :
    plk_aux_out en j y k ∈
      plk_aux_pred n en y := by
  unfold plk_aux_pred
  exact Part.mem_bind_iff.2 ⟨j, hj, Part.mem_map _ hk⟩

private lemma plk_aux_pred_spec
    (n : ℕ → ℕ) (en : ℕ → ℕ → Option BitString) (y : BitString) (j : ℕ)
    (hj : y.length < n j) (hmin : ∀ m < j, n m ≤ y.length)
    (hk : ∃ k, plk_aux_test en j y k = true) :
    ∃ x, (∃ k, en j k = some x) ∧ y <+: x ∧
      plk_aux_pred n en y =
        Part.some (x.getD y.length false) := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨k0, hk0, -⟩ := Nat.rfind_min'
    (p := fun k => plk_aux_test en j y k) hk
  have hk0' : k0 ∈ Nat.rfind (fun k => Part.some
      (plk_aux_test en j y k)) := hk0
  have hspec : true ∈ Part.some
      (plk_aux_test en j y k0) :=
    Nat.rfind_spec hk0'
  have htest : plk_aux_test en j y k0 = true :=
    (Part.mem_some_iff.1 hspec).symm
  obtain ⟨x, hx, hpre⟩ :=
    (plk_aux_test_iff en j y k0).1 htest
  refine ⟨x, ⟨k0, hx⟩, hpre, ?_⟩
  rw [Part.eq_some_iff]
  have hout := plk_aux_out_eq en j y k0 x hx
  rw [← hout]
  exact plk_aux_pred_mem n en y j k0
    (plk_aux_stage_mem n y.length j hj hmin) hk0'

private lemma plk_aux_partrec
    (n : ℕ → ℕ) (hn : Computable n) (en : ℕ → ℕ → Option BitString) (hen : Computable₂ en) :
    Partrec (plk_aux_pred n en) := by
  have heq : Computable₂ fun a b : BitString => decide (a = b) :=
    (PrimrecPred.decide (Primrec.eq (α := BitString))).to_comp.to₂
  have htake : Computable₂ fun (l : BitString) (n : ℕ) => l.take n :=
    (Primrec.list_take.comp Primrec.snd Primrec.fst).to_comp
  have hlen : Computable fun l : BitString => l.length :=
    (Primrec.list_length (α := Bool)).to_comp
  have hgetD : Computable₂ fun (l : BitString) (m : ℕ) => l.getD m false :=
    (Primrec.list_getD false).to_comp
  -- the stage search
  have hlt : Computable₂ fun (y : BitString) (j : ℕ) => decide (y.length < n j) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp (hlen.comp Computable.fst)
      (hn.comp Computable.snd)
  have hS : Partrec fun y : BitString => Nat.rfind fun j => Part.some (decide (y.length < n j)) :=
    Partrec.rfind (Computable₂.partrec₂ hlt)
  -- the candidate search
  have hgw : Computable fun r : (BitString × ℕ) × ℕ => en r.1.2 r.2 :=
    hen.comp (Computable.snd.comp Computable.fst) Computable.snd
  have hy : Computable fun p : ((BitString × ℕ) × ℕ) × BitString => p.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have htest : Computable₂ fun (q : BitString × ℕ) (k : ℕ) =>
      plk_aux_test en q.2 q.1 k := by
    have hinner : Computable₂ fun (r : (BitString × ℕ) × ℕ) (x : BitString) =>
        decide (r.1.1 = x.take r.1.1.length) :=
      heq.comp hy (htake.comp Computable.snd (hlen.comp hy))
    exact Computable.option_getD (Computable.option_map hgw hinner) (Computable.const false)
  have hC : Partrec fun q : BitString × ℕ => Nat.rfind fun k => Part.some
      (plk_aux_test en q.2 q.1 k) :=
    Partrec.rfind (Computable₂.partrec₂ htest)
  have hout : Computable₂ fun (q : BitString × ℕ) (k : ℕ) =>
      plk_aux_out en q.2 q.1 k := by
    have hinner : Computable₂ fun (r : (BitString × ℕ) × ℕ) (x : BitString) =>
        x.getD r.1.1.length false :=
      hgetD.comp Computable.snd (hlen.comp hy)
    exact Computable.option_getD (Computable.option_map hgw hinner) (Computable.const false)
  have hbody : Partrec₂ fun (y : BitString) (j : ℕ) =>
      (Nat.rfind fun k => Part.some
        (plk_aux_test en j y k)).map
        fun k => plk_aux_out en j y k :=
    Partrec.map hC hout
  exact Partrec.bind hS hbody

private lemma plk_aux_window_spec
    (n : ℕ → ℕ) (en : ℕ → ℕ → Option BitString) (w : CantorSeq)
    (hgrow : ∀ j, 8 * n j ≤ n (j + 1))
    (hw : ∀ j, ∃ k, en j k = some (cantorPrefix w (n j)))
    (j i : ℕ) (h1 : n j / 4 ≤ i) (h2 : i < n j) :
    ∃ x, (∃ k, en j k = some x) ∧ cantorPrefix w i <+: x ∧
      plk_aux_pred n en (cantorPrefix w i) =
        Part.some (x.getD i false) := by
  have hmono : Monotone n := monotone_nat_of_le_succ fun j => by have := hgrow j; omega
  have hmin : ∀ m < j, n m ≤ i := by
    intro m hm
    have h8 : 8 * n m ≤ n j :=
      calc 8 * n m ≤ n (m + 1) := hgrow m
        _ ≤ n j := hmono (by omega)
    omega
  have hk : ∃ k, plk_aux_test en j
      (cantorPrefix w i) k = true := by
    obtain ⟨k, hk⟩ := hw j
    exact ⟨k, (plk_aux_test_iff en j _ k).2
      ⟨_, hk, cantorPrefix_mono w h2.le⟩⟩
  obtain ⟨x, hx1, hx2, hx3⟩ :=
    plk_aux_pred_spec n en (cantorPrefix w i) j
      (by simpa using h2) (by simpa using hmin) hk
  refine ⟨x, hx1, hx2, ?_⟩
  simpa using hx3

private lemma plk_aux_dom
    (n : ℕ → ℕ) (en : ℕ → ℕ → Option BitString) (w : CantorSeq)
    (hlt : ∀ j, j < n j) (hw : ∀ j, ∃ k, en j k = some (cantorPrefix w (n j))) (i : ℕ) :
    (plk_aux_pred n en (cantorPrefix w i)).Dom :=
        by
  classical
  have hex : ∃ j, i < n j := ⟨i, hlt i⟩
  have hj : i < n (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, n m ≤ i := fun m hm => not_lt.1 (Nat.find_min hex hm)
  have hk : ∃ k, plk_aux_test en (Nat.find hex)
      (cantorPrefix w i) k = true := by
    obtain ⟨k, hk⟩ := hw (Nat.find hex)
    exact ⟨k, (plk_aux_test_iff en _ _ k).2
      ⟨_, hk, cantorPrefix_mono w hj.le⟩⟩
  obtain ⟨x, -, -, hx⟩ :=
    plk_aux_pred_spec n en (cantorPrefix w i)
      (Nat.find hex) (by simpa using hj) (by simpa using hmin) hk
  rw [hx]
  exact Part.some_dom _

open Classical in
private lemma plk_aux_window_errors
    (n : ℕ → ℕ) (en : ℕ → ℕ → Option BitString) (w : CantorSeq)
    (hgrow : ∀ j, 8 * n j ≤ n (j + 1))
    (hw : ∀ j, ∃ k, en j k = some (cantorPrefix w (n j)))
    (j : ℕ) (F : Finset BitString)
    (hF : ∀ x, (∃ k, en j k = some x) → cantorPrefix w (n j / 4) <+: x → x ∈ F) :
    ((Finset.Ico (n j / 4) (n j)).filter fun i =>
      w i ∉ plk_aux_pred n en
        (cantorPrefix w i)).card ≤ F.card := by
  have hW : ∀ i : ℕ, ∃ x : BitString, (n j / 4 ≤ i ∧ i < n j) →
      ((∃ k, en j k = some x) ∧ cantorPrefix w i <+: x ∧
        plk_aux_pred n en (cantorPrefix w i) =
          Part.some (x.getD i false)) := by
    intro i
    by_cases hi : n j / 4 ≤ i ∧ i < n j
    · obtain ⟨x, hx1, hx2, hx3⟩ :=
        plk_aux_window_spec n en w hgrow hw j i
          hi.1 hi.2
      exact ⟨x, fun _ => ⟨hx1, hx2, hx3⟩⟩
    · exact ⟨[], fun h => absurd h hi⟩
  choose xs hxs using hW
  -- two distinct errors have distinct candidates
  have key : ∀ i i', (n j / 4 ≤ i ∧ i < n j) → (n j / 4 ≤ i' ∧ i' < n j) →
      w i ∉ plk_aux_pred n en
        (cantorPrefix w i) → i < i' → xs i ≠ xs i' := by
    intro i i' hi hi' herr hlt heq
    obtain ⟨-, -, hpred⟩ := hxs i hi
    obtain ⟨-, hpre, -⟩ := hxs i' hi'
    have hlen : i < (cantorPrefix w i').length := by simpa using hlt
    have h1 : i < (xs i').length := lt_of_lt_of_le hlen hpre.length_le
    have hbit : (xs i').getD i false = w i := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
      have := hpre.getElem hlen
      rw [← this]
      simp
    apply herr
    rw [hpred, Part.mem_some_iff, heq]
    exact hbit.symm
  refine Finset.card_le_card_of_injOn xs ?_ ?_
  · intro i hi
    have hi' := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
    have hIco := Finset.mem_Ico.1 hi'.1
    obtain ⟨hx1, hx2, -⟩ := hxs i hIco
    exact Finset.mem_coe.2 (hF (xs i) hx1 ((cantorPrefix_mono w hIco.1).trans hx2))
  · intro i hi i' hi' heq
    have hi1 := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
    have hi2 := Finset.mem_filter.1 (Finset.mem_coe.1 hi')
    have hI := Finset.mem_Ico.1 hi1.1
    have hI' := Finset.mem_Ico.1 hi2.1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact key i i' hI hI' hi1.2 hlt heq
    · exact key i' i hI' hI hi2.2 hlt heq.symm

open Classical in
private lemma plk_aux_correct_ge
    (P : BitString →. Bool) (w : CantorSeq) (a N : ℕ) :
    N - a ≤ plk_correct P w N +
      ((Finset.Ico a N).filter fun i => w i ∉ P (cantorPrefix w i)).card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.Ico a N)
    (fun i => w i ∈ P (cantorPrefix w i))
  have h2 : ((Finset.Ico a N).filter fun i => w i ∈ P (cantorPrefix w i)).card ≤
      plk_correct P w N := by
    unfold plk_correct
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hi ⊢
    exact ⟨hi.1.2, hi.2⟩
  rw [Nat.card_Ico] at h1
  omega

/-- Step 2 of the proof of `not_exists_isMisesChurchDaleyRandom_plainK_log`: the
candidate-enumeration predictor of the book (p. 300), applied to the *window* `[n_j/4, n_j)` of the
stage `j`. Let `en j` enumerate (uniformly computably in `j`) a set `E_j` of strings of length
`n_j`,
where `n_{j+1} ≥ 8 n_j`, and let `w↾n_j ∈ E_j` for all `j`. Suppose that for infinitely many `j` the
strings of `E_j` extending `w↾⌊n_j/4⌋` lie in a finite set `F` with `10 |F| < n_j - ⌊n_j/4⌋`.
Then some partial computable predictor, defined on all prefixes of `w`, wins on `w`.

(Proof idea: at a position `i` with `n_{j-1} ≤ i < n_j` predict `false` if `i < n_j/4`, and
otherwise
the bit `i` of the first-enumerated element of `E_j` extending `w↾i`.  The latter never hangs on `w`
since `w↾n_j ∈ E_j`; it changes the candidate only after an error and never returns to a refuted
candidate, so on the window it errs at most `|F|` times; hence at least `0.9 (n_j - n_j/4) ≥ 0.6
n_j`
of the first `n_j` guesses are correct, for the infinitely many good `j`.) -/
private lemma plk_window
    (n : ℕ → ℕ) (hn : Computable n) (hgrow : ∀ j, 8 * n j ≤ n (j + 1)) (hpos : ∀ j, 1 ≤ n j)
    (en : ℕ → ℕ → Option BitString) (hen : Computable₂ en)
    (w : CantorSeq) (hw : ∀ j, ∃ k, en j k = some (cantorPrefix w (n j)))
    (hfew : ∃ᶠ j : ℕ in atTop, ∃ F : Finset BitString,
      10 * F.card < n j - n j / 4 ∧
      ∀ x, (∃ k, en j k = some x) → cantorPrefix w (n j / 4) <+: x → x ∈ F) :
    ∃ P : BitString →. Bool,
      plk_PredictorWins P w := by
  have hlt : ∀ j, j < n j := by
    intro j
    induction j with
    | zero => have := hpos 0; omega
    | succ j ih => have := hgrow j; omega
  refine ⟨plk_aux_pred n en, ?_⟩
  unfold plk_PredictorWins
  refine ⟨plk_aux_partrec n hn en hen,
    fun i => plk_aux_dom n en w hlt hw i,
    1 / 10, by norm_num, ?_⟩
  rw [Filter.frequently_atTop] at hfew ⊢
  intro M
  obtain ⟨j, hjM, F, hF1, hF2⟩ := hfew M
  refine ⟨n j, by have := hlt j; omega, ?_⟩
  have hErr := plk_aux_window_errors n en w
    hgrow hw j F hF2
  have hcor := plk_aux_correct_ge
    (plk_aux_pred n en) w (n j / 4) (n j)
  have hnat : 6 * n j ≤ 10 * plk_correct
      (plk_aux_pred n en) w (n j) := by
    omega
  have hreal : (6 : ℝ) * (n j : ℝ) ≤ 10 * (plk_correct
      (plk_aux_pred n en) w (n j) : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- One step of the deduplicating accumulation of the enumeration `en j`. -/
private def plk_aux_step (en : ℕ → ℕ →
    Option BitString) (j i : ℕ) (acc : List BitString) :
    List BitString :=
  match en j i with
  | none => acc
  | some y => if y ∈ acc then acc else y :: acc

/-- The distinct strings among `en j 0, …, en j (k-1)`. -/
private def plk_aux_items (en : ℕ → ℕ →
    Option BitString) (j : ℕ) : ℕ → List BitString
  | 0 => []
  | k + 1 => plk_aux_step en j k
               (plk_aux_items en j k)

private lemma plk_aux_mem_step (en : ℕ → ℕ →
    Option BitString) (j i : ℕ) (acc : List BitString)
    (y : BitString) : y ∈ plk_aux_step en j i acc ↔
        y ∈ acc ∨ en j i = some y := by
  cases h : en j i with
  | none => simp [plk_aux_step, h]
  | some z =>
    simp only [plk_aux_step, h]
    by_cases hz : z ∈ acc
    · rw [ite_eq_left hz]
      constructor
      · exact Or.inl
      · rintro (h1 | h1)
        · exact h1
        · rw [Option.some.injEq] at h1
          rw [← h1]
          exact hz
    · rw [ite_eq_right hz, List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact Or.inr (by rw [h1])
        · exact Or.inl h1
      · rintro (h1 | h1)
        · exact Or.inr h1
        · left
          rw [Option.some.injEq] at h1
          exact h1.symm

private lemma plk_aux_mem_items (en : ℕ → ℕ →
    Option BitString) (j k : ℕ) (y : BitString) :
    y ∈ plk_aux_items en j k ↔ ∃ i < k, en j i =
        some y := by
  induction k with
  | zero => simp [plk_aux_items]
  | succ k ih =>
    rw [plk_aux_items, plk_aux_mem_step, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
      · exact ⟨k, Nat.lt_succ_self k, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · exact Or.inl ⟨i, hi', h⟩
      · exact Or.inr h

private lemma plk_aux_nodup_items (en : ℕ → ℕ →
    Option BitString) (j k : ℕ) :
    (plk_aux_items en j k).Nodup := by
  induction k with
  | zero => simp [plk_aux_items]
  | succ k ih =>
    rw [plk_aux_items]
    cases h : en j k with
    | none => simpa [plk_aux_step, h] using ih
    | some z =>
      simp only [plk_aux_step, h]
      by_cases hz : z ∈ plk_aux_items en j k
      · rw [ite_eq_left hz]
        exact ih
      · rw [ite_eq_right hz]
        exact List.nodup_cons.mpr ⟨hz, ih⟩

/-- Membership `a ∈ l` is a primitive-recursive relation (decidable, any primcodable type). -/
private lemma plk_aux_mem_decide_primrec :
    Primrec₂ (fun (a : BitString) (l : List BitString) => decide (a ∈ l)) := by
  have key : ∀ (a : BitString) (l : List BitString),
      decide (a ∈ l) = l.foldr (fun x acc => if x = a then true else acc) false := by
    intro a l
    induction l with
    | nil => simp
    | cons x t ih =>
      simp only [List.mem_cons, List.foldr_cons, ← ih]
      by_cases h : x = a
      · simp only [h, true_or, decide_true, ↓reduceIte]
      · simp only [Bool.decide_or, h, ↓reduceIte, eq_comm, Bool.eq_or_self,
          true_eq_decide_iff]
        exact fun heq => absurd heq.symm h
  have hcond : PrimrecPred (fun a : (BitString × List BitString) × (BitString × Bool) =>
      a.2.1 = a.1.1) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)
  have hstep : Primrec₂ (fun (p : BitString × List BitString) (q : BitString × Bool) =>
      if q.1 = p.1 then true else q.2) :=
    Primrec.ite hcond (Primrec.const true) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.snd (Primrec.const false) hstep).of_eq
    (fun p => (key p.1 p.2).symm)

private lemma plk_aux_items_computable
    (en : ℕ → ℕ → Option BitString) (hen : Computable₂ en) :
    Computable (fun p : ℕ × ℕ => plk_aux_items en
                                   p.1 p.2) := by
  have hstep : Computable₂ (fun (p : ℕ × ℕ) (q : ℕ × List BitString) =>
      plk_aux_step en p.1 q.1 q.2) := by
    have h1 : Computable (fun v : (ℕ × ℕ) × (ℕ × List BitString) => en v.1.1 v.2.1) :=
      hen.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
    have hg : Computable₂ (fun (v : (ℕ × ℕ) × (ℕ × List BitString)) (y : BitString) =>
        if y ∈ v.2.2 then v.2.2 else y :: v.2.2) := by
      have hc : Computable (fun w : ((ℕ × ℕ) × (ℕ × List BitString)) × BitString =>
          decide (w.2 ∈ w.1.2.2)) :=
        plk_aux_mem_decide_primrec.to_comp.comp Computable.snd
          (Computable.snd.comp (Computable.snd.comp Computable.fst))
      have hcons : Computable (fun w : ((ℕ × ℕ) × (ℕ × List BitString)) × BitString =>
          w.2 :: w.1.2.2) :=
        Computable.list_cons.comp Computable.snd
          (Computable.snd.comp (Computable.snd.comp Computable.fst))
      refine (Computable.cond hc
        (Computable.snd.comp (Computable.snd.comp Computable.fst)) hcons).of_eq (fun w => ?_)
      simp
    have h2 := Computable.option_casesOn (σ := List BitString) h1
      (Computable.snd.comp Computable.snd) hg
    refine h2.of_eq (fun v => ?_)
    change _ = plk_aux_step en v.1.1 v.2.1 v.2.2
    unfold plk_aux_step
    cases en v.1.1 v.2.1 <;> rfl
  have hrec := Computable.nat_rec (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ => ([] : List BitString))
    (h := fun (p : ℕ × ℕ) (q : ℕ × List BitString) =>
      plk_aux_step en p.1 q.1 q.2)
    Computable.snd (Computable.const []) hstep
  refine hrec.of_eq (fun p => ?_)
  obtain ⟨j, k⟩ := p
  induction k with
  | zero => rfl
  | succ k ih =>
    change plk_aux_step en j k
        (Nat.rec (motive := fun _ => List BitString) []
      (fun y IH => plk_aux_step en j y IH) k) =
          plk_aux_step en j k
          (plk_aux_items en j k)
    rw [ih]

/-- The number of strings in `L` extending `u`. -/
private def plk_aux_cnt (L : List BitString)
    (u : BitString) : ℕ :=
  (L.filter (fun y => decide (u = y.take u.length))).length

/-- The test of the heavy-prefix enumeration: `x` is turned into its prefix `u` of length
`|x| / 4` if at least `(|x| - |x| / 4) / 10` strings of `L` extend `u`. -/
private def plk_step3_aux_test (L : List BitString)
    (x : BitString) : Option BitString :=
  if x.length - x.length / 4 ≤ 10 * plk_aux_cnt L
      (x.take (x.length / 4))
  then some (x.take (x.length / 4)) else none

/-- The enumeration of the heavy prefixes. -/
private def plk_aux_enH (en : ℕ → ℕ →
    Option BitString) (j k : ℕ) : Option BitString :=
  (en j k).bind (fun x => plk_step3_aux_test
                            (plk_aux_items en j
                            (k + 1)) x)

private lemma plk_aux_test_computable : Computable₂
    plk_step3_aux_test := by
  have hlen_x : Computable (fun q : List BitString × BitString => q.2.length) :=
    Primrec.list_length.to_comp.comp Computable.snd
  have ha : Computable (fun q : List BitString × BitString => q.2.length / 4) :=
    Primrec.nat_div.to_comp.comp hlen_x (Computable.const 4)
  have hu : Computable (fun q : List BitString × BitString => q.2.take (q.2.length / 4)) :=
    Primrec.list_take.to_comp.comp ha Computable.snd
  have hpred : Computable₂ (fun (q : List BitString × BitString) (y : BitString) =>
      decide (q.2.take (q.2.length / 4) = y.take (q.2.take (q.2.length / 4)).length)) := by
    have hu' : Computable (fun r : (List BitString × BitString) × BitString =>
        r.1.2.take (r.1.2.length / 4)) := hu.comp Computable.fst
    have hlen : Computable (fun r : (List BitString × BitString) × BitString =>
        (r.1.2.take (r.1.2.length / 4)).length) := Primrec.list_length.to_comp.comp hu'
    have htake : Computable (fun r : (List BitString × BitString) × BitString =>
        r.2.take (r.1.2.take (r.1.2.length / 4)).length) :=
      Primrec.list_take.to_comp.comp hlen Computable.snd
    exact primrec_decideEq.to_comp.comp hu' htake
  have hfilt : Computable (fun q : List BitString × BitString =>
      q.1.filter (fun y => decide (q.2.take (q.2.length / 4) =
        y.take (q.2.take (q.2.length / 4)).length))) :=
    computable_list_filter Computable.fst hpred
  have hcnt : Computable (fun q : List BitString × BitString =>
      10 * plk_aux_cnt q.1
          (q.2.take (q.2.length / 4))) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 10) (Primrec.list_length.to_comp.comp hfilt)
  have hT : Computable (fun q : List BitString × BitString => q.2.length - q.2.length / 4) :=
    Primrec.nat_sub.to_comp.comp hlen_x ha
  have hle : Primrec₂ (fun a b : ℕ => decide (a ≤ b)) := Primrec.nat_le.decide
  have hcond : Computable (fun q : List BitString × BitString =>
      decide (q.2.length - q.2.length / 4 ≤ 10 *
          plk_aux_cnt q.1 (q.2.take (q.2.length /
          4)))) :=
    hle.to_comp.comp hT hcnt
  refine (Computable.cond hcond (Computable.option_some.comp hu)
    (Computable.const (none : Option BitString))).of_eq (fun q => ?_)
  simp only [plk_step3_aux_test, Bool.cond_decide]

private lemma plk_aux_enH_computable (en : ℕ → ℕ →
    Option BitString) (hen : Computable₂ en) :
    Computable₂ (plk_aux_enH en) := by
  have hitems : Computable (fun p : ℕ × ℕ =>
    plk_aux_items en p.1 (p.2 + 1)) :=
    (plk_aux_items_computable en hen).comp
      (Computable.pair Computable.fst (Computable.succ.comp Computable.snd))
  have hg : Computable₂ (fun (p : ℕ × ℕ) (x : BitString) =>
      plk_step3_aux_test (plk_aux_items en p.1 (p.2 + 1)) x) :=
    plk_aux_test_computable.comp (hitems.comp Computable.fst) Computable.snd
  exact Computable.option_bind hen hg

private lemma plk_aux_enH_eq_some_iff (en : ℕ → ℕ →
    Option BitString) (j k : ℕ) (u : BitString) :
    plk_aux_enH en j k = some u ↔ ∃ x, en j k =
        some x ∧ u = x.take (x.length / 4) ∧
      x.length - x.length / 4 ≤ 10 * plk_aux_cnt
          (plk_aux_items en j (k + 1)) u := by
  unfold plk_aux_enH
  cases h : en j k with
  | none => simp
  | some x =>
    simp only [Option.bind_some, plk_step3_aux_test]
    constructor
    · intro h1
      by_cases hc : x.length - x.length / 4 ≤ 10 * plk_aux_cnt (plk_aux_items en j (k + 1))
          (x.take (x.length / 4))
      · rw [ite_eq_left hc, Option.some.injEq] at h1
        subst h1
        exact ⟨x, rfl, rfl, hc⟩
      · rw [ite_eq_right hc] at h1
        exact absurd h1 (by simp)
    · rintro ⟨x', hx', hu, hc⟩
      rw [Option.some.injEq] at hx'
      subst hx'
      subst hu
      rw [ite_eq_left hc]

private lemma plk_aux_cnt_eq (L : List BitString)
    (hL : L.Nodup) (u : BitString) :
    plk_aux_cnt L u =
        (L.toFinset.filter (fun y => u <+: y)).card := by
  classical
  unfold plk_aux_cnt
  rw [← List.toFinset_card_of_nodup (hL.filter _)]
  congr 1
  ext y
  simp [List.prefix_iff_eq_take]

private lemma plk_aux_length (n : ℕ → ℕ)
    (en : ℕ → ℕ → Option BitString)
    (hlen : ∀ j k x, en j k = some x → x.length = n j) (j k : ℕ) (u : BitString)
    (h : plk_aux_enH en j k = some u) : u.length =
        n j / 4 := by
  rw [plk_aux_enH_eq_some_iff] at h
  obtain ⟨x, hx, hu, -⟩ := h
  have hxlen := hlen j k x hx
  rw [hu, List.length_take, hxlen]
  exact Nat.min_eq_left (Nat.div_le_self _ _)

private lemma plk_aux_cover (n : ℕ → ℕ)
    (en : ℕ → ℕ → Option BitString)
    (hlen : ∀ j k x, en j k = some x → x.length = n j) (j : ℕ) (G : Finset BitString)
    (hG : ∀ x, (∃ k, en j k = some x) → x ∈ G) :
    ∃ G' : Finset BitString, (∀ u, (∃ k, plk_aux_enH en j k = some u) → u ∈ G') ∧
      G'.card * (n j - n j / 4) ≤ 10 * G.card := by
  classical
  refine ⟨(G.image (fun x => x.take (n j / 4))).filter (fun u => u.length = n j / 4 ∧
    n j - n j / 4 ≤ 10 * (G.filter (fun x => u <+: x)).card), ?_, ?_⟩
  · rintro u ⟨k, hk⟩
    have hulen := plk_aux_length n en hlen j k u hk
    rw [plk_aux_enH_eq_some_iff] at hk
    obtain ⟨x, hx, hu, hc⟩ := hk
    have hxlen := hlen j k x hx
    have hxG : x ∈ G := hG x ⟨k, hx⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hxG, ?_⟩, hulen, ?_⟩
    · rw [hu, hxlen]
    · have hcnt : plk_aux_cnt
        (plk_aux_items en j (k + 1)) u ≤
        (G.filter (fun x => u <+: x)).card := by
        rw [plk_aux_cnt_eq _
            (plk_aux_nodup_items en j (k + 1))]
        apply Finset.card_le_card
        intro y hy
        rw [Finset.mem_filter, List.mem_toFinset,
            plk_aux_mem_items] at hy
        obtain ⟨⟨i, -, hi⟩, hpy⟩ := hy
        exact Finset.mem_filter.mpr ⟨hG y ⟨i, hi⟩, hpy⟩
      rw [hxlen] at hc
      calc n j - n j / 4 ≤ 10 * plk_aux_cnt (plk_aux_items en j (k + 1)) u := hc
        _ ≤ 10 * (G.filter (fun x => u <+: x)).card := Nat.mul_le_mul_left 10 hcnt
  · set G' := (G.image (fun x => x.take (n j / 4))).filter (fun u => u.length = n j / 4 ∧
      n j - n j / 4 ≤ 10 * (G.filter (fun x => u <+: x)).card) with hG'
    have hdisj : ∀ u ∈ G', ∀ u' ∈ G', u ≠ u' →
        Disjoint (G.filter (fun x => u <+: x)) (G.filter (fun x => u' <+: x)) := by
      intro u hu u' hu' hne
      rw [Finset.disjoint_filter]
      intro x _ h1 h2
      apply hne
      have hl1 := (Finset.mem_filter.mp hu).2.1
      have hl2 := (Finset.mem_filter.mp hu').2.1
      rw [List.prefix_iff_eq_take] at h1 h2
      rw [h1, h2, hl1, hl2]
    have hsum : ∑ u ∈ G', (G.filter (fun x => u <+: x)).card ≤ G.card := by
      rw [← Finset.card_biUnion hdisj]
      exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun u _ => Finset.filter_subset _ _))
    calc G'.card * (n j - n j / 4) = ∑ _u ∈ G', (n j - n j / 4) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ u ∈ G', 10 * (G.filter (fun x => u <+: x)).card :=
          Finset.sum_le_sum (fun u hu => (Finset.mem_filter.mp hu).2.2)
      _ = 10 * ∑ u ∈ G', (G.filter (fun x => u <+: x)).card := by rw [Finset.mul_sum]
      _ ≤ 10 * G.card := Nat.mul_le_mul_left 10 hsum

private lemma plk_aux_light (n : ℕ → ℕ)
    (hpos : ∀ j, 1 ≤ n j) (en : ℕ → ℕ → Option BitString)
    (hlen : ∀ j k x, en j k = some x → x.length = n j) (j : ℕ) (u : BitString)
    (hu : u.length = n j / 4) (hnot : ¬ ∃ k,
        plk_aux_enH en j k = some u) :
    ∃ F : Finset BitString, 10 * F.card < n j - n j / 4 ∧
      ∀ x, (∃ k, en j k = some x) → u <+: x → x ∈ F := by
  classical
  obtain ⟨S, hSmem, hcard⟩ : ∃ S : ℕ → Finset BitString,
      (∀ k y, y ∈ S k ↔ (∃ i < k, en j i = some y) ∧ u <+: y) ∧
      ∀ k, plk_aux_cnt
          (plk_aux_items en j k) u = (S k).card :=
          by
    refine ⟨fun k => (plk_aux_items en j
                       k).toFinset.filter (fun y => u <+: y), ?_, ?_⟩
    · intro k y
      simp [plk_aux_mem_items]
    · intro k
      exact plk_aux_cnt_eq _
          (plk_aux_nodup_items en j k) u
  have hSmono : ∀ k k', k ≤ k' → S k ⊆ S k' := by
    intro k k' hkk' y hy
    obtain ⟨⟨i, hi, hiy⟩, hpy⟩ := (hSmem k y).mp hy
    exact (hSmem k' y).mpr ⟨⟨i, lt_of_lt_of_le hi hkk', hiy⟩, hpy⟩
  have hT : 1 ≤ n j - n j / 4 := by
    have := hpos j
    omega
  have hA : ∀ k, 10 * (S k).card < n j - n j / 4 := by
    intro k
    by_contra hge
    push Not at hge
    have hne : (S k).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [h] at hge
      simp only [Finset.card_empty, mul_zero] at hge
      omega
    obtain ⟨y, hy⟩ := hne
    obtain ⟨⟨i, hi, hiy⟩, hpy⟩ := (hSmem k y).mp hy
    let I : Finset ℕ := (Finset.range k).filter (fun i => ∃ y', en j i = some y' ∧ u <+: y')
    have hIne : I.Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, y, hiy, hpy⟩⟩
    have hi0mem := Finset.max'_mem I hIne
    obtain ⟨hi0k, y0, hy0, hupy0⟩ := Finset.mem_filter.mp hi0mem
    have hi0lt : I.max' hIne < k := Finset.mem_range.mp hi0k
    have hsub1 : S k ⊆ S (I.max' hIne + 1) := by
      intro z hz
      obtain ⟨⟨i', hi', hiz⟩, hpz⟩ := (hSmem k z).mp hz
      have hiI : i' ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi', z, hiz, hpz⟩
      have hle : i' ≤ I.max' hIne := Finset.le_max' I i' hiI
      exact (hSmem _ z).mpr ⟨⟨i', Nat.lt_succ_of_le hle, hiz⟩, hpz⟩
    have hsub2 : S (I.max' hIne + 1) ⊆ S k := hSmono _ _ (Nat.succ_le_of_lt hi0lt)
    have hcardEq : (S (I.max' hIne + 1)).card = (S k).card :=
      le_antisymm (Finset.card_le_card hsub2) (Finset.card_le_card hsub1)
    apply hnot
    refine ⟨I.max' hIne, (plk_aux_enH_eq_some_iff
        en j _ u).mpr ⟨y0, hy0, ?_, ?_⟩⟩
    · have hy0len := hlen j _ y0 hy0
      have hu' := hupy0
      rw [List.prefix_iff_eq_take] at hu'
      rw [hu', hu, hy0len]
    · rw [hcard, hcardEq, hlen j _ y0 hy0]
      exact hge
  obtain ⟨K, hK⟩ : ∃ K, ∀ k, (S k).card ≤ (S K).card := by
    have hbdd : BddAbove (Set.range fun k => (S k).card) :=
      ⟨n j, by
        rintro _ ⟨k, rfl⟩
        have := hA k
        change (S k).card ≤ n j
        omega⟩
    have hne : (Set.range fun k => (S k).card).Nonempty := ⟨_, 0, rfl⟩
    obtain ⟨K, hK⟩ := Nat.sSup_mem hne hbdd
    have hK' : (S K).card = sSup (Set.range fun k => (S k).card) := hK
    exact ⟨K, fun k => by rw [hK']; exact le_csSup hbdd ⟨k, rfl⟩⟩
  have hSK : ∀ k, S k ⊆ S K := by
    intro k
    rcases le_total k K with h | h
    · exact hSmono _ _ h
    · have hsub := hSmono _ _ h
      have heq := Finset.eq_of_subset_of_card_le hsub (hK k)
      rw [heq]
  refine ⟨S K, hA K, ?_⟩
  rintro x ⟨k, hk⟩ hux
  exact hSK (k + 1) ((hSmem (k + 1) x).mpr ⟨⟨k, Nat.lt_succ_self k, hk⟩, hux⟩)

/-- Step 3 of the proof of `not_exists_isMisesChurchDaleyRandom_plainK_log`: the *heavy
prefixes* of the book (p. 301: "the values of `u` such that there are at least `n^{0.8}` different
`v` with `uv ∈ C_n`").  Let `en j` enumerate, uniformly computably in `j`, a set `E_j` of strings of
length `n_j ≥ 1`.  Then the set `H_j` of the strings `u` of length `⌊n_j/4⌋` that are prefixes of at
least `(n_j - ⌊n_j/4⌋)/10` distinct elements of `E_j` is again uniformly enumerable, by some
`enH` (a string is enumerated once the stage-`k` approximation of `E_j` has that many elements
extending it), and
* `H_j` is covered by a finite set of at most `10 |G| / (n_j - ⌊n_j/4⌋)` strings, for every finite
  `G ⊇ E_j`;
* a string `u` of length `⌊n_j/4⌋` outside `H_j` has fewer than `(n_j - ⌊n_j/4⌋)/10` extensions in
  `E_j`
  (they lie in a finite set `F` with `10 |F| < n_j - ⌊n_j/4⌋`). -/
private lemma plk_heavy
    (n : ℕ → ℕ) (hpos : ∀ j, 1 ≤ n j)
    (en : ℕ → ℕ → Option BitString) (hen : Computable₂ en)
    (hlen : ∀ j k x, en j k = some x → x.length = n j) :
    ∃ enH : ℕ → ℕ → Option BitString, Computable₂ enH ∧
      (∀ j k u, enH j k = some u → u.length = n j / 4) ∧
      (∀ j, ∀ G : Finset BitString, (∀ x, (∃ k, en j k = some x) → x ∈ G) →
        ∃ G' : Finset BitString, (∀ u, (∃ k, enH j k = some u) → u ∈ G') ∧
          G'.card * (n j - n j / 4) ≤ 10 * G.card) ∧
      (∀ j, ∀ u : BitString, u.length = n j / 4 → (¬ ∃ k, enH j k = some u) →
        ∃ F : Finset BitString, 10 * F.card < n j - n j / 4 ∧
          ∀ x, (∃ k, en j k = some x) → u <+: x → x ∈ F) := by
  refine ⟨plk_aux_enH en,
    plk_aux_enH_computable en hen, ?_, ?_, ?_⟩
  · intro j k u h
    exact plk_aux_length n en hlen j k u h
  · intro j G hG
    exact plk_aux_cover n en hlen j G hG
  · intro j u hu hnot
    exact plk_aux_light n hpos en hlen j u hu hnot

/-- Auxiliary for step 4 (case 1 of the induction step): if the stage-`j` string `w↾⌊n_j/4⌋` is not
a
heavy prefix for infinitely many `j`, then step 2 gives a winning predictor. -/
private lemma plk_case1
    (n : ℕ → ℕ) (hn : Computable n) (hgrow : ∀ j, 8 * n j ≤ n (j + 1)) (hpos : ∀ j, 1 ≤ n j)
    (en : ℕ → ℕ → Option BitString) (hen : Computable₂ en)
    (w : CantorSeq) (hw : ∀ j, ∃ k, en j k = some (cantorPrefix w (n j)))
    (enH : ℕ → ℕ → Option BitString)
    (hlight : ∀ j, ∀ u : BitString, u.length = n j / 4 → (¬ ∃ k, enH j k = some u) →
      ∃ F : Finset BitString, 10 * F.card < n j - n j / 4 ∧
        ∀ x, (∃ k, en j k = some x) → u <+: x → x ∈ F)
    (hJ : ∃ᶠ j : ℕ in atTop, ¬ ∃ k, enH j k = some (cantorPrefix w (n j / 4))) :
    ∃ P : BitString →. Bool,
      plk_PredictorWins P w := by
  refine plk_window n hn hgrow hpos en hen w hw ?_
  refine hJ.mono ?_
  intro j hj
  exact hlight j _ (cantorPrefix_length w (n j / 4)) hj

/-- Auxiliary for step 4 (exponent `0`): the heavy case is impossible, since a single heavy prefix
`w↾⌊n_j/4⌋` would force `n_j - ⌊n_j/4⌋ ≤ 10 A`, which fails for large `j`. -/
private lemma plk_zero_absurd
    (A : ℕ) (n : ℕ → ℕ) (hgrow : ∀ j, 8 * n j ≤ n (j + 1)) (hpos : ∀ j, 1 ≤ n j)
    (en : ℕ → ℕ → Option BitString)
    (hG : ∀ j, ∃ G : Finset BitString, G.card ≤ A * n j ^ 0 ∧
        ∀ x, (∃ k, en j k = some x) → x ∈ G)
    (w : CantorSeq) (enH : ℕ → ℕ → Option BitString)
    (hcov : ∀ j, ∀ G : Finset BitString, (∀ x, (∃ k, en j k = some x) → x ∈ G) →
        ∃ G' : Finset BitString, (∀ u, (∃ k, enH j k = some u) → u ∈ G') ∧
          G'.card * (n j - n j / 4) ≤ 10 * G.card)
    (hJ : ¬ ∃ᶠ j : ℕ in atTop, ¬ ∃ k, enH j k = some (cantorPrefix w (n j / 4))) :
    False := by
  have hev : ∀ᶠ j : ℕ in atTop, ∃ k, enH j k = some (cantorPrefix w (n j / 4)) := by
    have := Filter.not_frequently.mp hJ
    simpa using this
  obtain ⟨j0, hj0⟩ := Filter.eventually_atTop.mp hev
  have hnj : ∀ j, j + 1 ≤ n j := by
    intro j
    induction j with
    | zero => simpa using hpos 0
    | succ j ih => have := hgrow j; omega
  obtain ⟨j, hjdef⟩ : ∃ j, j = j0 + 14 * A + 14 := ⟨_, rfl⟩
  obtain ⟨G, hGcard, hGmem⟩ := hG j
  obtain ⟨G', hG'mem, hG'card⟩ := hcov j G hGmem
  obtain ⟨k, hk⟩ := hj0 j (by omega)
  have hmem : cantorPrefix w (n j / 4) ∈ G' := hG'mem _ ⟨k, hk⟩
  have hpos' : 0 < G'.card := Finset.card_pos.mpr ⟨_, hmem⟩
  have h1 : n j - n j / 4 ≤ G'.card * (n j - n j / 4) := Nat.le_mul_of_pos_left _ hpos'
  have hGcard' : G.card ≤ A := by simpa using hGcard
  have hnj' := hnj j
  omega

/-- Arithmetic for step 4 (exponent `g + 1`): a cover of the heavy prefixes with
`c * (m - m/4) ≤ 10 A m^(g+1)` elements has `c ≤ 14 · 7^g · A · (m/4)^g`. -/
private lemma plk_card_bound
    (g A m c : ℕ) (hm : 4 ≤ m) (hc : c * (m - m / 4) ≤ 10 * (A * m ^ (g + 1))) :
    c ≤ 14 * 7 ^ g * A * (m / 4) ^ g := by
  have h1 : 3 * m ≤ 4 * (m - m / 4) := by omega
  have h2 : c * (3 * m) ≤ c * (4 * (m - m / 4)) := Nat.mul_le_mul_left c h1
  have h3 : 3 * c * m ≤ 40 * (A * m ^ g) * m := by
    calc 3 * c * m = c * (3 * m) := by ring
      _ ≤ c * (4 * (m - m / 4)) := h2
      _ = 4 * (c * (m - m / 4)) := by ring
      _ ≤ 4 * (10 * (A * m ^ (g + 1))) := Nat.mul_le_mul_left 4 hc
      _ = 40 * (A * m ^ g) * m := by ring
  have h4 : 3 * c ≤ 40 * (A * m ^ g) := Nat.le_of_mul_le_mul_right h3 (by omega)
  have h5 : c ≤ 14 * (A * m ^ g) := by omega
  have h6 : m ^ g ≤ 7 ^ g * (m / 4) ^ g := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) g
  calc c ≤ 14 * (A * m ^ g) := h5
    _ ≤ 14 * (A * (7 ^ g * (m / 4) ^ g)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6)
    _ = 14 * 7 ^ g * A * (m / 4) ^ g := by ring

/-- Step 4 of the proof of `not_exists_isMisesChurchDaleyRandom_plainK_log`: the induction
on the exponent `g` (the book's "split the string into `k > c` pieces and repeat the argument",
p. 301). Let `n_{j+1} ≥ 8 n_j`, `n_0 ≥ 1`, let `en j` enumerate (uniformly computably) a set `E_j`
of
strings of length `n_j` contained in a finite set of at most `A n_j^g` strings, and let
`w↾n_j ∈ E_j` for all `j`.  Then some partial computable predictor, defined on all prefixes of `w`,
wins on `w`.

(Proof: induction on `g`, for all `A, n, en` simultaneously.  Take `enH` from step 3.  If
`w↾⌊n_j/4⌋ ∉ H_j` for infinitely many `j`, step 2 applies.  Otherwise `w↾⌊n_j/4⌋ ∈ H_j` for all
`j ≥ j_0`, and the induction hypothesis applies to the stage lengths `⌊n_{j_0+j}/4⌋` (the growth
ratio `8` is preserved by `⌊·/4⌋`) and to the sets `H_{j_0+j}`, which have at most
`14 · 7^{g-1} A ⌊n_{j_0+j}/4⌋^{g-1}` elements (by step 3: `|H_j| ≤ 10 A n_j^g / (3 n_j / 4)`);
for `g = 0` this case is impossible, since `|H_j| ≥ 1` would force `3 n_j / 4 ≤ 10 A`.) -/
private lemma plk_claim (g : ℕ) :
    ∀ (A : ℕ) (n : ℕ → ℕ) (en : ℕ → ℕ → Option BitString) (w : CantorSeq),
      Computable n → Computable₂ en → (∀ j, 8 * n j ≤ n (j + 1)) → (∀ j, 1 ≤ n j) →
      (∀ j k x, en j k = some x → x.length = n j) →
      (∀ j, ∃ G : Finset BitString, G.card ≤ A * n j ^ g ∧
        ∀ x, (∃ k, en j k = some x) → x ∈ G) →
      (∀ j, ∃ k, en j k = some (cantorPrefix w (n j))) →
      ∃ P : BitString →. Bool,
        plk_PredictorWins P w := by
  induction g with
  | zero =>
    intro A n en w hn hen hgrow hpos hlen hG hw
    obtain ⟨enH, henH, hlenH, hcov, hlight⟩ :=
      plk_heavy n hpos en hen hlen
    by_cases hJ : ∃ᶠ j : ℕ in atTop, ¬ ∃ k, enH j k = some (cantorPrefix w (n j / 4))
    · exact plk_case1 n hn hgrow hpos en hen w hw enH hlight hJ
    · exact (plk_zero_absurd A n hgrow hpos en
        hG w enH hcov hJ).elim
  | succ g ih =>
    intro A n en w hn hen hgrow hpos hlen hG hw
    obtain ⟨enH, henH, hlenH, hcov, hlight⟩ :=
      plk_heavy n hpos en hen hlen
    by_cases hJ : ∃ᶠ j : ℕ in atTop, ¬ ∃ k, enH j k = some (cantorPrefix w (n j / 4))
    · exact plk_case1 n hn hgrow hpos en hen w hw enH hlight hJ
    · have hev : ∀ᶠ j : ℕ in atTop, ∃ k, enH j k = some (cantorPrefix w (n j / 4)) := by
        have := Filter.not_frequently.mp hJ
        simpa using this
      obtain ⟨j0, hj0⟩ := Filter.eventually_atTop.mp hev
      have hn8 : ∀ j, 8 ≤ n (j + 1) := fun j => by
        have := hgrow j
        have := hpos j
        omega
      have hshift : Computable (fun j : ℕ => j0 + 1 + j) :=
        (Primrec.nat_add.comp (Primrec.const (j0 + 1)) Primrec.id).to_comp
      refine ih (14 * 7 ^ g * A) (fun j => n (j0 + 1 + j) / 4) (fun j k => enH (j0 + 1 + j) k) w
        ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact Computable₂.comp (Primrec.nat_div.to_comp) (hn.comp hshift) (Computable.const 4)
      · exact Computable₂.comp henH (g := fun p : ℕ × ℕ => j0 + 1 + p.1) (h := fun p : ℕ × ℕ => p.2)
          (Primrec.nat_add.comp (Primrec.const (j0 + 1)) Primrec.fst).to_comp Computable.snd
      · intro j
        have h := hgrow (j0 + 1 + j)
        change 8 * (n (j0 + 1 + j) / 4) ≤ n (j0 + 1 + (j + 1)) / 4
        have e : j0 + 1 + (j + 1) = j0 + 1 + j + 1 := by omega
        rw [e]
        omega
      · intro j
        show 1 ≤ n (j0 + 1 + j) / 4
        have e : j0 + 1 + j = (j0 + j) + 1 := by omega
        rw [e]
        have := hn8 (j0 + j)
        omega
      · intro j k x hx
        exact hlenH (j0 + 1 + j) k x hx
      · intro j
        obtain ⟨G, hGcard, hGmem⟩ := hG (j0 + 1 + j)
        obtain ⟨G', hG'mem, hG'card⟩ := hcov (j0 + 1 + j) G hGmem
        refine ⟨G', ?_, fun x hx => hG'mem x hx⟩
        have hm : 4 ≤ n (j0 + 1 + j) := by
          have e : j0 + 1 + j = (j0 + j) + 1 := by omega
          rw [e]
          have := hn8 (j0 + j)
          omega
        have hc : G'.card * (n (j0 + 1 + j) - n (j0 + 1 + j) / 4)
            ≤ 10 * (A * n (j0 + 1 + j) ^ (g + 1)) :=
          hG'card.trans (Nat.mul_le_mul_left 10 hGcard)
        exact plk_card_bound g A _ _ hm hc
      · intro j
        exact hj0 (j0 + 1 + j) (by omega)

/-- Auxiliary for step 5 of the proof of `not_exists_isMisesChurchDaleyRandom_plainK_log`: the
dovetailed enumeration of the strings of length `2^(3(j+1))` accepted by the stage test `chk` at the
complexity threshold `c * (3 (j+1)) + c + 1`. The index `k = ⟨code of x, stage⟩` yields `x` when the
stage test `chk (threshold, x) stage` succeeds. -/
private def plk_en
    (chk : ℕ × BitString → ℕ → Bool) (c j k : ℕ) : Option BitString :=
  (levelEnum (2 ^ (3 * (j + 1))) (Nat.unpair k).1).bind fun x =>
    bif chk (c * (3 * (j + 1)) + c + 1, x) (Nat.unpair k).2 then some x else none

/-- Auxiliary for step 5: the dovetailed enumeration is computable. -/
private lemma plk_computable_en
    {chk : ℕ × BitString → ℕ → Bool} (hchk : Computable₂ chk) (c : ℕ) :
    Computable₂ (plk_en chk c) := by
  have hexp : Computable (fun j : ℕ => 3 * (j + 1)) :=
    (Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))).to_comp
  have hlen : Computable (fun j : ℕ => 2 ^ (3 * (j + 1))) :=
    primrec_two_pow_aux.to_comp.comp hexp
  have hK : Computable (fun j : ℕ => c * (3 * (j + 1)) + c + 1) :=
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const c)
          (Primrec.nat_mul.comp (Primrec.const 3)
            (Primrec.nat_add.comp Primrec.id (Primrec.const 1))))
        (Primrec.const c))
      (Primrec.const 1)).to_comp
  have hidx1 : Computable (fun p : ℕ × ℕ => (Nat.unpair p.2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hidx2 : Computable (fun p : ℕ × ℕ => (Nat.unpair p.2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hbase : Computable (fun p : ℕ × ℕ =>
      levelEnum (2 ^ (3 * (p.1 + 1))) (Nat.unpair p.2).1) :=
    computable₂_levelEnum.comp (hlen.comp Computable.fst) hidx1
  have hbranch : Computable₂ (fun (p : ℕ × ℕ) (x : BitString) =>
      bif chk (c * (3 * (p.1 + 1)) + c + 1, x) (Nat.unpair p.2).2 then some x else none) := by
    have htest : Computable (fun q : (ℕ × ℕ) × BitString =>
        chk (c * (3 * (q.1.1 + 1)) + c + 1, q.2) (Nat.unpair q.1.2).2) :=
      hchk.comp (Computable.pair (hK.comp (Computable.fst.comp Computable.fst)) Computable.snd)
        (hidx2.comp Computable.fst)
    exact (Computable.cond htest (Computable.option_some.comp Computable.snd)
      (Computable.const none)).to₂
  exact (Computable.option_bind hbase hbranch).to₂

/-- Auxiliary for step 5: what the dovetailed enumeration outputs. -/
private lemma plk_en_eq_some
    (chk : ℕ × BitString → ℕ → Bool) (c j k : ℕ) (x : BitString) :
    plk_en chk c j k = some x ↔
      x.length = 2 ^ (3 * (j + 1)) ∧ Encodable.encode x = (Nat.unpair k).1 ∧
        chk (c * (3 * (j + 1)) + c + 1, x) (Nat.unpair k).2 = true := by
  unfold plk_en
  constructor
  · intro h
    cases hl : levelEnum (2 ^ (3 * (j + 1))) (Nat.unpair k).1 with
    | none => rw [hl] at h; simp at h
    | some y =>
      rw [hl] at h
      simp only [Option.bind_some] at h
      cases hc : chk (c * (3 * (j + 1)) + c + 1, y) (Nat.unpair k).2 with
      | false => rw [hc] at h; simp at h
      | true =>
        rw [hc] at h
        simp only [Bool.cond_true, Option.some_inj] at h
        subst h
        obtain ⟨hlen, hcode⟩ := levelEnum_eq_some_iff.1 hl
        exact ⟨hlen, hcode, hc⟩
  · rintro ⟨hlen, hcode, hc⟩
    rw [levelEnum_eq_some_iff.2 ⟨hlen, hcode⟩]
    simp only [Option.bind_some, hc, Bool.cond_true]

/-- Step 5 of the proof of `not_exists_isMisesChurchDaleyRandom_plainK_log`: the candidate
sets of the book (p. 299: "the set of all strings of complexity less than `c log n` is an
enumerable set of at most `n^c` elements").  For `n_j = 8^{j+1}` the sets
`E_j = {x : |x| = n_j, C(x) < c ⌊log n_j⌋ + c + 1}` are uniformly enumerable (`isRE_plainK_lt`,
dovetailed into a computable `en`), contained in a finite set of at most `2^{c+1} n_j^c` strings
(`card_lowPlainK_level_le`), and contain `w↾n_j` for every `w` with
`C(w↾m) ≤ c ⌊log m⌋ + c` for all `m`. -/
private lemma plk_candidates
    (V : Map) (hV : isOptimalConditional V) (c : ℕ) :
    ∃ (A : ℕ) (n : ℕ → ℕ) (en : ℕ → ℕ → Option BitString),
      Computable n ∧ Computable₂ en ∧ (∀ j, 8 * n j ≤ n (j + 1)) ∧ (∀ j, 1 ≤ n j) ∧
      (∀ j k x, en j k = some x → x.length = n j) ∧
      (∀ j, ∃ G : Finset BitString, G.card ≤ A * n j ^ c ∧
        ∀ x, (∃ k, en j k = some x) → x ∈ G) ∧
      ∀ w : CantorSeq, (∀ m : ℕ, plainK V (cantorPrefix w m) ≤ ((c * Nat.log 2 m + c : ℕ) : ℕ∞)) →
        ∀ j, ∃ k, en j k = some (cantorPrefix w (n j)) := by
  obtain ⟨chk, hchk, hmono, hspec⟩ := exists_computable₂_plainKStage V hV.1
  refine ⟨2 ^ (c + 1), fun j => 2 ^ (3 * (j + 1)),
    plk_en chk c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (primrec_two_pow_aux.comp (Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))).to_comp
  · exact plk_computable_en hchk c
  · intro j
    change 8 * 2 ^ (3 * (j + 1)) ≤ 2 ^ (3 * (j + 1 + 1))
    rw [show 3 * (j + 1 + 1) = 3 * (j + 1) + 3 by ring, pow_add]
    omega
  · intro j
    exact Nat.one_le_two_pow
  · intro j k x h
    exact ((plk_en_eq_some chk c j k x).1 h).1
  · intro j
    refine ⟨lowPlainKLevel V (c * (3 * (j + 1)) + c + 1) (2 ^ (3 * (j + 1))), ?_, ?_⟩
    · refine (card_lowPlainK_level_le V _ _).trans (le_of_eq ?_)
      change 2 ^ (c * (3 * (j + 1)) + c + 1) = 2 ^ (c + 1) * (2 ^ (3 * (j + 1))) ^ c
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    · rintro x ⟨k, hk⟩
      obtain ⟨hlen, -, hc'⟩ :=
        (plk_en_eq_some chk c j k x).1 hk
      exact mem_lowPlainKLevel.2 ⟨hlen, (hspec (c * (3 * (j + 1)) + c + 1, x)).2 ⟨_, hc'⟩⟩
  · intro w hw j
    have hlog : Nat.log 2 (2 ^ (3 * (j + 1))) = 3 * (j + 1) := Nat.log_pow (by norm_num) _
    have h1 := hw (2 ^ (3 * (j + 1)))
    rw [hlog] at h1
    have h2 : plainK V (cantorPrefix w (2 ^ (3 * (j + 1)))) <
        ((c * (3 * (j + 1)) + c + 1 : ℕ) : ℕ∞) :=
      lt_of_le_of_lt h1 (by exact_mod_cast Nat.lt_succ_self _)
    obtain ⟨s, hs⟩ := (hspec (c * (3 * (j + 1)) + c + 1,
      cantorPrefix w (2 ^ (3 * (j + 1))))).1 h2
    refine ⟨Nat.pair (Encodable.encode (cantorPrefix w (2 ^ (3 * (j + 1))))) s, ?_⟩
    rw [plk_en_eq_some]
    refine ⟨cantorPrefix_length _ _, ?_, ?_⟩
    · simp [Nat.unpair_pair]
    · simpa [Nat.unpair_pair] using hs

/-- **SUV Theorem 188, p. 287 (Merkle).**  There is no Mises-Church-Daley random sequence with
`C(ω_0 … ω_{n-1}) = O(log n)`. -/
theorem not_exists_isMisesChurchDaleyRandom_plainK_log (V : Map) (hV : isOptimalConditional V) :
    ¬ ∃ w, IsMisesChurchDaleyRandom w ∧ ∃ c : ℕ, ∀ n : ℕ,
      plainK V (cantorPrefix w n) ≤ ((c * Nat.log 2 n + c : ℕ) : ℕ∞) := by
  rintro ⟨w, hw, c, hc⟩
  obtain ⟨A, n, en, hn, hen, hgrow, hpos, hlen, hG, hmem⟩ :=
    plk_candidates V hV c
  obtain ⟨P, hP⟩ := plk_claim c A n en w hn hen
    hgrow hpos hlen hG (hmem w hc)
  exact plk_predictor hP hw

end Kolmogorov.FrequencyGames
