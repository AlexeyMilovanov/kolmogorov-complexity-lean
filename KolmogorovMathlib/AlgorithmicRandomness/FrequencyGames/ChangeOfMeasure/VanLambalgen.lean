/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.FrequencyDeviation

/-!
# Van Lambalgen's theorem on Mises-Church-Daley randomness

A sequence that is Martin-Löf random with respect to the independent-trials measure with
probabilities `p_i → q` (computably) is Mises-Church-Daley random with frequency `q`.  The proof
bounds the measure of the sets of sequences whose frequency along a selection rule deviates from
`q`, and shows these sets are effectively open and null.

The main declaration is `isMisesChurchDaleyRandomAt_of_isMartinLofRandom`
(SUV Theorem 201, p. 305, van Lambalgen), in the part of the book on frequency stability and
randomness tests.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

private def isMisesChurchDaleyRandomAt_of_isMartinLofRandom_E (R : Set BitString) (a b : ℚ) (n : ℕ)
    : Set CantorSeq :=
  {w | ∃ T, (selectedPositions R w T).card = n ∧ ((a:ℝ)*n < selectedOnes R w T ∨ selectedOnes R w T
      < (b:ℝ)*n)}

open Classical in
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_chain_succ
    (R : Set BitString) (w : CantorSeq) (t : ℕ) :
    selectChain R w (t + 1)
      = selectChain R w t ++ (if cantorPrefix w t ∈ R then [w t] else []) := by
  unfold selectChain
  rw [cantorPrefix_succ, selectedBits_append_singleton]

private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_chain_zero
    (R : Set BitString) (w : CantorSeq) : selectChain R w 0 = [] := by
  simp [selectChain, selectedBits, selectedAux, cantorPrefix]

open Classical in
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_bookkeeping
    (R : Set BitString) (w : CantorSeq) (T : ℕ) :
    (selectChain R w T).length = (selectedPositions R w T).card ∧
      ((selectChain R w T).count true : ℝ) = selectedOnes R w T := by
  induction T with
  | zero =>
    simp [isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_chain_zero,
      selectedPositions, selectedOnes]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpos : selectedPositions R w (t + 1) =
        if cantorPrefix w t ∈ R then insert t (selectedPositions R w t)
        else selectedPositions R w t := by
      unfold selectedPositions
      rw [Finset.range_add_one, Finset.filter_insert]
    have hnot : t ∉ selectedPositions R w t := by simp [selectedPositions]
    rw [isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_chain_succ]
    by_cases h : cantorPrefix w t ∈ R
    · have hp : selectedPositions R w (t + 1) = insert t (selectedPositions R w t) := by
        rw [hpos, ite_eq_left h]
      simp only [h, ite_true]
      refine ⟨by simp [hp, ih1, Finset.card_insert_of_notMem hnot], ?_⟩
      unfold selectedOnes
      rw [hp, Finset.sum_insert hnot, ← selectedOnes, ← ih2, List.count_append]
      cases w t with
      | false => simp [bitVal]
      | true => simp [bitVal]; ring
    · have hp : selectedPositions R w (t + 1) = selectedPositions R w t := by
        rw [hpos, ite_eq_right h]
      have ho : selectedOnes R w (t + 1) = selectedOnes R w t := by
        unfold selectedOnes; rw [hp]
      simp only [h, ite_false]
      rw [ho]
      exact ⟨by simpa [hp] using ih1, by simpa using ih2⟩

private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_ofPrefixSet
    {T : Set BitString} (hT : IsStreamPrefixSet T) (h_unbdd : ¬ ∃ M, ∀ x ∈ T, x.length ≤ M) :
    ∃ u : CantorSeq, BitStream.ofPrefixSet T hT = .infinite u ∧ ∀ x ∈ T, IsCantorPrefix x u := by
  classical
  refine ⟨fun i => (Classical.choose (exists_mem_length_gt h_unbdd i)).get
      ⟨i, (Classical.choose_spec (exists_mem_length_gt h_unbdd i)).2⟩, ?_,
    isCantorPrefix_of_mem hT h_unbdd⟩
  unfold BitStream.ofPrefixSet
  rw [dite_eq_right h_unbdd]

private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_infinite
    (R : Set BitString) (w : CantorSeq) {q : ℝ} (h : ¬ FiniteOrFreq q (selectStream R w)) :
    ∃ u : CantorSeq, ¬ HasLimitFreq q u ∧ ∀ n : ℕ, ∃ T : ℕ,
      (selectedPositions R w T).card = n ∧
        selectedOnes R w T = ((cantorPrefix u n).count true : ℝ) := by
  classical
  have hT : IsStreamPrefixSet (chainPrefixSet (selectChain R w)) :=
    isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)
  have hsel : selectStream R w
      = BitStream.ofPrefixSet (chainPrefixSet (selectChain R w)) hT := rfl
  by_cases hb : ∃ M, ∀ x ∈ chainPrefixSet (selectChain R w), x.length ≤ M
  · exfalso
    apply h
    rw [hsel]
    unfold BitStream.ofPrefixSet
    rw [dite_eq_left hb]
    trivial
  · obtain ⟨u, hu, hpre⟩ :=
      isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_ofPrefixSet hT hb
    rw [hsel, hu] at h
    refine ⟨u, h, fun n => ?_⟩
    have hbk := isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_bookkeeping R w
    have hlen : ∀ m, ∃ t, m < (selectChain R w t).length := by
      intro m
      obtain ⟨x, hx, hxm⟩ := exists_mem_length_gt hb m
      obtain ⟨t, ht⟩ := hx
      exact ⟨t, lt_of_lt_of_le hxm ht.length_le⟩
    have hstep : ∀ t, (selectChain R w (t + 1)).length ≤ (selectChain R w t).length + 1 := by
      intro t
      rw [isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_chain_succ]
      simp only [List.length_append]
      split_ifs <;> simp
    have hex : ∃ T, (selectChain R w T).length = n := by
      rcases n with _ | n
      · exact ⟨0, by simp
                       [isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_chain_zero]⟩
      · have hne : ∃ t, n < (selectChain R w t).length := hlen n
        have hs : n < (selectChain R w (Nat.find hne)).length := Nat.find_spec hne
        have ht0pos : Nat.find hne ≠ 0 := by
          intro h0
          rw [h0, isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_chain_zero] at hs
          simp at hs
        obtain ⟨s, hs'⟩ := Nat.exists_eq_succ_of_ne_zero ht0pos
        have hmin : ¬ n < (selectChain R w s).length := Nat.find_min hne (by omega)
        have : (selectChain R w (Nat.find hne)).length ≤ (selectChain R w s).length + 1 := by
          rw [hs']; exact hstep s
        exact ⟨Nat.find hne, by omega⟩
    obtain ⟨T, hT'⟩ := hex
    refine ⟨T, ?_, ?_⟩
    · rw [← (hbk T).1, hT']
    · rw [← (hbk T).2]
      have hmem : selectChain R w T ∈ chainPrefixSet (selectChain R w) := ⟨T, List.prefix_rfl⟩
      have hcp := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 (hpre _ hmem)
      rw [hT'] at hcp
      rw [hcp]

/-- Step 1 of the proof of `isMisesChurchDaleyRandomAt_of_isMartinLofRandom`:
deterministic relation. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic
    (R : Set BitString) {w : CantorSeq} {q : ℝ}
    (h_not : ¬ FiniteOrFreq q (selectStream R w)) :
    ∃ a b : ℚ, (b:ℝ) < q ∧ q < (a:ℝ) ∧ ∃ᶠ n in atTop, w ∈
        isMisesChurchDaleyRandomAt_of_isMartinLofRandom_E R a b n := by
  obtain ⟨u, hu, hT⟩ :=
    isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic_infinite R w h_not
  unfold HasLimitFreq at hu
  rw [Metric.tendsto_atTop] at hu
  push Not at hu
  obtain ⟨ε, hε, hfreq⟩ := hu
  have hfreq' : ∃ᶠ n in atTop, ε ≤ |(freqOne u n : ℝ) - q| := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hd⟩ := hfreq N
    exact ⟨n, hn, by rwa [Real.dist_eq] at hd⟩
  have hfreq2 : ∃ᶠ n in atTop, q + ε ≤ (freqOne u n : ℝ) ∨ (freqOne u n : ℝ) ≤ q - ε := by
    refine hfreq'.mono fun n hn => ?_
    rcases le_abs'.1 hn with h | h
    · right; linarith
    · left; linarith
  have hf : ∀ n : ℕ, 1 ≤ n → ((cantorPrefix u n).count true : ℝ) = (n : ℝ) * (freqOne u n : ℝ) := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    unfold freqOne
    push_cast
    field_simp
  rw [Filter.frequently_or_distrib] at hfreq2
  rcases hfreq2 with h1 | h2
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show q < q + ε by linarith)
    obtain ⟨b, hb⟩ := exists_rat_lt q
    refine ⟨a, b, hb, ha1, ?_⟩
    refine (h1.and_eventually (Filter.eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_
    obtain ⟨T, hT1, hT2⟩ := hT n
    refine ⟨T, hT1, Or.inl ?_⟩
    rw [hT2, hf n hn1]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    nlinarith
  · obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show q - ε < q by linarith)
    obtain ⟨a, ha⟩ := exists_rat_gt q
    refine ⟨a, b, hb2, ha, ?_⟩
    refine (h2.and_eventually (Filter.eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_
    obtain ⟨T, hT1, hT2⟩ := hT n
    refine ⟨T, hT1, Or.inr ?_⟩
    rw [hT2, hf n hn1]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    nlinarith

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`: the `k`-th stage of
the
partial computation of the bits selected by the partial rule `r` from `x`. -/
private def isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK
    (r : BitString →. Bool) (x : BitString) (k : ℕ) : Part BitString :=
  Nat.rec (Part.some []) (fun n ih => ih >>= fun s => do
      let b ← r (x.take n)
      if b then Part.some (s ++ [x.getD n false]) else Part.some s) k

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK_mem_ruleSet
    (r : BitString →. Bool) (x : BitString) (k : ℕ)
    (hdom : ∀ n < k, (r (x.take n)).Dom) (b : Bool) (hb : b ∈ r (x.take k)) :
    x.take k ∈ partialRuleSet r ↔ b = true := by
  constructor
  · intro h
    exact (Part.mem_unique h.2 hb).symm
  · rintro rfl
    refine ⟨fun y hy => ?_, hb⟩
    have hyx : y <+: x := hy.trans (List.take_prefix k x)
    have hle : y.length ≤ k := le_trans hy.length_le (List.length_take_le k x)
    have hy_eq : y = x.take y.length := List.prefix_iff_eq_take.mp hyx
    rw [hy_eq]
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hdom _ hlt
    · rw [heq]
      exact Part.dom_iff_mem.mpr ⟨_, hb⟩

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK_mem_iff
    (r : BitString →. Bool) (x : BitString) :
    ∀ k, k ≤ x.length → ∀ s, s ∈ isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK r x
        k ↔
      (∀ n < k, (r (x.take n)).Dom) ∧ s = selectedBits (partialRuleSet r) (x.take k) := by
  intro k
  induction k with
  | zero =>
    intro _ s
    change s ∈ Part.some [] ↔ _
    have h_sel : selectedBits (partialRuleSet r) [] = [] := rfl
    simp only [Part.mem_some_iff, List.take_zero, h_sel]
    constructor
    · rintro rfl
      exact ⟨fun n hn => absurd hn (Nat.not_lt_zero n), rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  | succ k ih =>
    intro hk s
    have hk' : k < x.length := hk
    have ihk := ih hk'.le
    have htake : x.take (k+1) = x.take k ++ [x[k]] := List.take_succ_eq_append_getElem hk'
    have hget : x.getD k false = x[k] := List.getD_eq_getElem x false hk'
    have hunf : isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK r x (k+1) =
        (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK r x k).bind
          fun s' => (r (x.take k)).bind fun b =>
            if b then Part.some (s' ++ [x.getD k false]) else Part.some s' := rfl
    rw [hunf]
    simp only [Part.mem_bind_iff, ihk]
    constructor
    · rintro ⟨s', ⟨hd, rfl⟩, b, hb, hs⟩
      have hR := isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK_mem_ruleSet
        r x k hd b hb
      refine ⟨fun n hn => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | rfl
        · exact hd n h
        · exact Part.dom_iff_mem.mpr ⟨b, hb⟩
      · rw [htake, selectedBits_append_singleton]
        cases b with
        | true =>
          simp only [ite_true, Part.mem_some_iff] at hs
          rw [ite_eq_left (hR.mpr rfl), ← hget]
          exact hs
        | false =>
          simp only [Bool.false_eq_true, ite_false, Part.mem_some_iff] at hs
          rw [ite_eq_right (fun h => by simpa using hR.mp h)]
          simpa using hs
    · rintro ⟨hd, hs⟩
      have hbk : (r (x.take k)).Dom := hd k (Nat.lt_succ_self k)
      have hd' : ∀ n < k, (r (x.take n)).Dom := fun n hn => hd n (Nat.lt_succ_of_lt hn)
      have hR := isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK_mem_ruleSet
        r x k hd' _ (Part.get_mem hbk)
      refine ⟨selectedBits (partialRuleSet r) (x.take k), ⟨hd', rfl⟩, (r (x.take k)).get hbk,
        Part.get_mem hbk, ?_⟩
      rw [htake, selectedBits_append_singleton] at hs
      cases hbb : (r (x.take k)).get hbk with
      | true =>
        rw [hbb] at hR
        simp only [ite_true, Part.mem_some_iff]
        rw [ite_eq_left (hR.mpr rfl)] at hs
        rw [hget]
        exact hs
      | false =>
        rw [hbb] at hR
        simp only [Bool.false_eq_true, ite_false, Part.mem_some_iff]
        rw [ite_eq_right (fun h => by simpa using hR.mp h)] at hs
        simpa using hs

open Classical in
/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_pos_succ
    (R : Set BitString) (w : CantorSeq) (T : ℕ) :
    selectedPositions R w (T+1) =
      if cantorPrefix w T ∈ R then insert T (selectedPositions R w T) else
        selectedPositions R w T := by
  unfold selectedPositions
  rw [Finset.range_add_one, Finset.filter_insert]

open Classical in
/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`: the selected bits of
a prefix have the length and the number of ones of the selected positions. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_sel_chain
    (R : Set BitString) (w : CantorSeq) (T : ℕ) :
    (selectedBits R (cantorPrefix w T)).length = (selectedPositions R w T).card ∧
    (((selectedBits R (cantorPrefix w T)).count true : ℕ) : ℝ) = selectedOnes R w T := by
  induction T with
  | zero =>
    have h0 : cantorPrefix w 0 = [] := by simp [cantorPrefix]
    simp [h0, selectedBits, selectedAux, selectedPositions, selectedOnes]
  | succ T ih =>
    have hpos := isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_pos_succ R w T
    have hnot : T ∉ selectedPositions R w T := by simp [selectedPositions]
    have hones : selectedOnes R w (T+1) =
        if cantorPrefix w T ∈ R then bitVal (w T) + selectedOnes R w T else selectedOnes R w T := by
      unfold selectedOnes
      rw [hpos]
      by_cases h : cantorPrefix w T ∈ R
      · simp only [h, ite_true]
        rw [Finset.sum_insert hnot]
      · simp only [h, ite_false]
    rw [cantorPrefix_succ, selectedBits_append_singleton, hpos, hones]
    by_cases h : cantorPrefix w T ∈ R
    · simp only [h, ite_true]
      rw [Finset.card_insert_of_notMem hnot]
      refine ⟨by simp [ih.1], ?_⟩
      simp only [List.count_append, List.count_singleton, Nat.cast_add]
      rw [ih.2, add_comm]
      cases w T <;> simp [bitVal]
    · simp only [h, ite_false, List.append_nil]
      exact ih

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`: the selected-bits
function is partial computable. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK_partrec
    (r : BitString →. Bool) (hr : Partrec r) :
    Partrec (fun x : BitString =>
      isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK r x x.length) := by
  have h1 : Partrec (fun (xn : BitString × ℕ) =>
      isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK r xn.1 xn.2) := by
    apply Partrec.nat_rec (f := Prod.snd) (g := fun _ => Part.some [])
        (h := fun (xn : BitString × ℕ) (ns : ℕ × BitString) => do
      let b ← r (xn.1.take ns.1)
      if b then Part.some (ns.2 ++ [xn.1.getD ns.1 false]) else Part.some ns.2)
    · exact Computable.snd
    · exact (Computable.partrec (Computable.const []))
    · have h_take : Computable (fun (p : (BitString × ℕ) × (ℕ × BitString)) => p.1.1.take p.2.1) :=
        by
        have h_pair : Computable (fun (p : (BitString × ℕ) × (ℕ × BitString)) => (p.2.1, p.1.1)) :=
          Computable.pair (Computable.fst.comp Computable.snd) (Computable.fst.comp Computable.fst)
        exact Computable.of_eq (Computable.comp Primrec.list_take.to_comp h_pair) fun _ => rfl
      have h_b : Partrec (fun (p : (BitString × ℕ) × (ℕ × BitString)) => r (p.1.1.take p.2.1)) :=
          hr.comp h_take
      have h_getD : Computable (fun (p : (BitString × ℕ) × (ℕ × BitString)) =>
        p.1.1.getD p.2.1 false) := by
        have h_pair : Computable (fun (p : (BitString × ℕ) × (ℕ × BitString)) => (p.1.1, p.2.1)) :=
          Computable.pair (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
        exact Computable.of_eq (Computable.comp (Primrec.list_getD false).to_comp h_pair) fun _ =>
          rfl
      have h_cons : Computable (fun (p : (BitString × ℕ) × (ℕ × BitString)) =>
        [p.1.1.getD p.2.1 false]) := by
        have h_pair : Computable (fun (p : (BitString × ℕ) × (ℕ × BitString)) =>
          (p.1.1.getD p.2.1 false, ([] : List Bool))) :=
          Computable.pair h_getD (Computable.const [])
        exact Computable.of_eq (Computable.comp Primrec.list_cons.to_comp h_pair) fun _ => rfl
      have h_append : Computable (fun (p : (BitString × ℕ) × (ℕ × BitString)) =>
        p.2.2 ++ [p.1.1.getD p.2.1 false]) := by
        have h_pair : Computable (fun (p : (BitString × ℕ) × (ℕ × BitString)) =>
          (p.2.2, [p.1.1.getD p.2.1 false])) :=
          Computable.pair (Computable.snd.comp Computable.snd) h_cons
        exact Computable.of_eq (Computable.comp Primrec.list_append.to_comp h_pair) fun _ => rfl
      have hc : Partrec (fun (p : (BitString × ℕ) × (ℕ × BitString)) => do
        let b ← r (p.1.1.take p.2.1)
        if b then Part.some (p.2.2 ++ [p.1.1.getD p.2.1 false]) else Part.some p.2.2) := by
        apply Partrec.bind h_b
        have h_cond : Partrec (fun (p : ((BitString × ℕ) × (ℕ × BitString)) × Bool) =>
          bif p.2 then (Part.some (p.1.2.2 ++ [p.1.1.1.getD p.1.2.1 false]) : Part BitString) else
            (Part.some p.1.2.2 : Part BitString)) := by
          have h1 : Partrec (fun (p : ((BitString × ℕ) × (ℕ × BitString)) × Bool) =>
            Part.some (p.1.2.2 ++ [p.1.1.1.getD p.1.2.1 false])) :=
            (Computable.partrec h_append).comp Computable.fst
          have h2 : Partrec (fun (p : ((BitString × ℕ) × (ℕ × BitString)) × Bool) =>
            Part.some p.1.2.2) :=
            (Computable.partrec (Computable.snd.comp Computable.snd)).comp Computable.fst
          exact Partrec.cond Computable.snd h1 h2
        apply Partrec.of_eq h_cond
        intro p
        cases p.2
        · rfl
        · rfl
      exact hc
  have h_len : Computable (fun (x : BitString) => x.length) := Primrec.list_length.to_comp
  have h_pair : Computable (fun (x : BitString) => (x, x.length)) := Computable.pair Computable.id
      h_len
  exact h1.comp h_pair

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`: the test
"`v` has length `n` and violates the rational bounds `a`, `b`", in natural-number arithmetic. -/
private def isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB
    (a b : ℚ) (n : ℕ) (v : BitString) : Bool :=
  decide (v.length = n) &&
    (decide (a.num.toNat * n < v.count true * a.den + (-a.num).toNat * n) ||
      decide (v.count true * b.den + (-b.num).toNat * n < b.num.toNat * n))

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_rat_lt_iff
    (a : ℚ) (n c : ℕ) :
    ((a : ℝ) * n < c) ↔ a.num.toNat * n < c * a.den + (-a.num).toNat * n := by
  have hd : (0:ℝ) < a.den := by exact_mod_cast a.den_pos
  have hnum : (a.num : ℝ) = (a.num.toNat : ℝ) - ((-a.num).toNat : ℝ) := by
    have h : a.num = (a.num.toNat : ℤ) - ((-a.num).toNat : ℤ) := by omega
    exact_mod_cast h
  rw [Rat.cast_def, div_mul_eq_mul_div, div_lt_iff₀ hd, hnum]
  constructor
  · intro h
    have : ((a.num.toNat * n : ℕ) : ℝ) < ((c * a.den + (-a.num).toNat * n : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  · intro h
    have := (Nat.cast_lt (α := ℝ)).mpr h
    push_cast at this
    nlinarith

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_rat_gt_iff
    (b : ℚ) (n c : ℕ) :
    ((c : ℝ) < (b : ℝ) * n) ↔ c * b.den + (-b.num).toNat * n < b.num.toNat * n := by
  have hd : (0:ℝ) < b.den := by exact_mod_cast b.den_pos
  have hnum : (b.num : ℝ) = (b.num.toNat : ℝ) - ((-b.num).toNat : ℝ) := by
    have h : b.num = (b.num.toNat : ℤ) - ((-b.num).toNat : ℤ) := by omega
    exact_mod_cast h
  rw [Rat.cast_def, div_mul_eq_mul_div, lt_div_iff₀ hd, hnum]
  constructor
  · intro h
    have : ((c * b.den + (-b.num).toNat * n : ℕ) : ℝ) < ((b.num.toNat * n : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  · intro h
    have := (Nat.cast_lt (α := ℝ)).mpr h
    push_cast at this
    nlinarith

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB_iff
    (a b : ℚ) (n : ℕ) (v : BitString) :
    isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB a b n v = true ↔
      v.length = n ∧
      ((a : ℝ) * n < ((v.count true : ℕ) : ℝ) ∨ ((v.count true : ℕ) : ℝ) < (b : ℝ) * n) := by
  simp only [isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq,
    isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_rat_lt_iff,
    isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_rat_gt_iff]

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_count_true_primrec :
    Primrec (fun l : BitString => l.count true) := by
  have heq : (fun l : BitString => l.count true)
      = fun l => l.foldr (fun b n => bif b then n+1 else n) 0 := by
    funext l
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp [ih]
  rw [heq]
  exact Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB_computable
    (a b : ℚ) :
    Computable (fun p : (ℕ × BitString) × BitString =>
      isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB a b p.1.1 p.2) := by
  have hn : Primrec (fun p : (ℕ × BitString) × BitString => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hv : Primrec (fun p : (ℕ × BitString) × BitString => p.2) := Primrec.snd
  have hc : Primrec (fun p : (ℕ × BitString) × BitString => p.2.count true) :=
    isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_count_true_primrec.comp hv
  have e0 : PrimrecPred (fun p : (ℕ × BitString) × BitString => p.2.length = p.1.1) :=
    Primrec.eq.comp (Primrec.list_length.comp hv) hn
  have e1 : PrimrecPred (fun p : (ℕ × BitString) × BitString =>
      a.num.toNat * p.1.1 < p.2.count true * a.den + (-a.num).toNat * p.1.1) :=
    Primrec.nat_lt.comp (Primrec.nat_mul.comp (Primrec.const a.num.toNat) hn)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hc (Primrec.const a.den))
        (Primrec.nat_mul.comp (Primrec.const (-a.num).toNat) hn))
  have e2 : PrimrecPred (fun p : (ℕ × BitString) × BitString =>
      p.2.count true * b.den + (-b.num).toNat * p.1.1 < b.num.toNat * p.1.1) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hc (Primrec.const b.den))
        (Primrec.nat_mul.comp (Primrec.const (-b.num).toNat) hn))
      (Primrec.nat_mul.comp (Primrec.const b.num.toNat) hn)
  have h : Primrec (fun p : (ℕ × BitString) × BitString =>
      decide (p.2.length = p.1.1 ∧
        (a.num.toNat * p.1.1 < p.2.count true * a.den + (-a.num).toNat * p.1.1 ∨
          p.2.count true * b.den + (-b.num).toNat * p.1.1 < b.num.toNat * p.1.1))) :=
    (PrimrecPred.and e0 (PrimrecPred.or e1 e2)).decide
  refine Computable.of_eq (Primrec.to_comp h) (fun p => ?_)
  simp only [isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB]
  rw [Bool.decide_and, Bool.decide_or]

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`: the r.e. set of
strings `x` such that the selected bits of `x` have length `n` and violate the bounds. -/
private def isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selSet
    (r : BitString →. Bool) (a b : ℚ) (n : ℕ) : Set BitString :=
  {x | ∃ v ∈ isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK r x x.length,
    isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB a b n v = true}

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selSet_isRE
    (r : BitString →. Bool) (hr : Partrec r) (a b : ℚ) :
    IsRE (fun q : ℕ × BitString =>
      q.2 ∈ isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selSet r a b q.1) := by
  refine ⟨fun q => (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK r q.2
      q.2.length).bind fun v =>
    bif isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB a b q.1 v
      then Part.some () else Part.none, ?_, ?_⟩
  · refine Partrec.bind
      ((isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK_partrec r hr).comp
        Computable.snd) ?_
    exact Partrec.cond
      (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB_computable a b)
      (Computable.partrec (Computable.const ())) Partrec.none
  · intro q
    rw [Part.dom_iff_mem]
    constructor
    · rintro ⟨u, hu⟩
      rw [Part.mem_bind_iff] at hu
      obtain ⟨v, hv, hu⟩ := hu
      refine ⟨v, hv, ?_⟩
      cases h : isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB a b q.1 v
      · rw [h] at hu
        exact absurd hu (by simp)
      · rfl
    · rintro ⟨v, hv, hc⟩
      refine ⟨(), ?_⟩
      rw [Part.mem_bind_iff]
      exact ⟨v, hv, by rw [hc]; exact Part.mem_some ()⟩

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open`: `E_n` is the set of
sequences with a prefix in the r.e. set `selSet`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_E_eq
    (r : BitString →. Bool) (a b : ℚ) (n : ℕ) :
    {w : CantorSeq | ∃ T, (selectedPositions (partialRuleSet r) w T).card = n ∧
      ((a:ℝ) * n < selectedOnes (partialRuleSet r) w T ∨
        selectedOnes (partialRuleSet r) w T < (b:ℝ) * n)} =
      prefixHitSet (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selSet r a b n) := by
  ext w
  constructor
  · rintro ⟨T, hcard, hcond⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      have hemp : selectedPositions (partialRuleSet r) w T = ∅ := Finset.card_eq_zero.mp hcard
      have h0 : selectedOnes (partialRuleSet r) w T = 0 := by simp [selectedOnes, hemp]
      rw [h0] at hcond
      simp at hcond
    · have hex : ∃ T', (selectedPositions (partialRuleSet r) w T').card = n := ⟨T, hcard⟩
      classical
      obtain ⟨T', hT'spec, hT'le, hmin⟩ : ∃ T', (selectedPositions (partialRuleSet r) w T').card =
          n ∧
          T' ≤ T ∧ ∀ t < T', (selectedPositions (partialRuleSet r) w t).card ≠ n :=
        ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex hcard, fun t ht => Nat.find_min hex ht⟩
      have hsub : selectedPositions (partialRuleSet r) w T' ⊆ selectedPositions (partialRuleSet r) w
          T := by
        intro i hi
        simp only [selectedPositions, Finset.mem_filter, Finset.mem_range] at hi ⊢
        exact ⟨by omega, hi.2⟩
      have heqpos : selectedPositions (partialRuleSet r) w T' = selectedPositions (partialRuleSet r)
          w T :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hT'spec, hcard])
      have hones : selectedOnes (partialRuleSet r) w T' = selectedOnes (partialRuleSet r) w T := by
        unfold selectedOnes
        rw [heqpos]
      cases T' with
      | zero =>
        exfalso
        have : selectedPositions (partialRuleSet r) w 0 = ∅ := by simp [selectedPositions]
        rw [this] at hT'spec
        simp at hT'spec
        omega
      | succ t =>
        have hRt : cantorPrefix w t ∈ partialRuleSet r := by
          by_contra hnot
          rw [isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_pos_succ,
            ite_eq_right hnot] at hT'spec
          exact hmin t (Nat.lt_succ_self t) hT'spec
        have hdom : ∀ j < t + 1, (r ((cantorPrefix w (t + 1)).take j)).Dom := by
          intro j hj
          rw [cantorPrefix_take w j (t + 1) hj.le]
          exact hRt.1 _ (cantorPrefix_mono w (by omega))
        have hmem : selectedBits (partialRuleSet r) (cantorPrefix w (t + 1)) ∈
            isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK r (cantorPrefix w
                (t + 1))
              (cantorPrefix w (t + 1)).length := by
          rw [cantorPrefix_length]
          refine (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK_mem_iff r _
              (t + 1)
            (by simp) _).mpr ⟨hdom, ?_⟩
          rw [cantorPrefix_take w (t + 1) (t + 1) le_rfl]
        refine ⟨t + 1, selectedBits (partialRuleSet r) (cantorPrefix w (t + 1)), hmem, ?_⟩
        obtain ⟨hl, hcnt⟩ :=
          isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_sel_chain (partialRuleSet r) w
              (t + 1)
        rw [isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB_iff]
        refine ⟨hl.trans hT'spec, ?_⟩
        rw [hcnt, hones]
        exact hcond
  · rintro ⟨k, v, hv, hc⟩
    rw [cantorPrefix_length] at hv
    have hs := (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selK_mem_iff r
      (cantorPrefix w k) k (by simp) v).mp hv
    have hv' : v = selectedBits (partialRuleSet r) (cantorPrefix w k) := by
      rw [hs.2, cantorPrefix_take w k k le_rfl]
    obtain ⟨hl, hcnt⟩ :=
      isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_sel_chain (partialRuleSet r) w k
    rw [← hv'] at hl hcnt
    obtain ⟨hlen, hcond⟩ :=
      (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_condB_iff a b n v).mp hc
    refine ⟨k, hl.symm.trans hlen, ?_⟩
    rw [← hcnt]
    exact hcond

/-- Step 2 of the proof of `isMisesChurchDaleyRandomAt_of_isMartinLofRandom`: uniform
effective openness. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open (r : BitString →. Bool)
    (hr : Partrec r) (a b : ℚ) :
    IsUniformlyEffectiveOpen (fun n => isMisesChurchDaleyRandomAt_of_isMartinLofRandom_E
                                         (partialRuleSet r) a b n) := by
  have h := isUniformlyEffectiveOpen_prefixHitSet_of_isRE
    (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selSet_isRE r hr a b)
  have heq : (fun n => isMisesChurchDaleyRandomAt_of_isMartinLofRandom_E (partialRuleSet r) a b n) =
      fun n => prefixHitSet (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_selSet r a b
                 n) :=
    funext fun n => isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open_E_eq r a b n
  rw [heq]
  exact h

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound`: almost surely no
prefix of the sequence has mass zero, since the cylinders of mass zero are countably many null
sets. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound_null
    (μ : Measure CantorSeq) :
    μ {w | ∃ i, cantorMass μ (cantorPrefix w i) = 0} = 0 := by
  apply measure_mono_null (t := ⋃ x ∈ {x : BitString | cantorMass μ x = 0}, cantorCylinder x)
  · rintro w ⟨i, hi⟩
    exact Set.mem_biUnion (x := cantorPrefix w i) hi
      (fun j h => (cantorPrefix_getElem w i j h).symm)
  · exact (measure_biUnion_null_iff (Set.to_countable _)).mpr (fun x hx => hx)

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound`: off the null set
of sequences with a prefix of mass zero, the sum of the conditional probabilities at the selected
positions is the sum of the `p i`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound_condSum (p : ℕ → NNReal)
    (hp : ∀ i, p i ≤ 1)
    (R : Set BitString) (w : CantorSeq)
    (hw : ∀ i, cantorMass (independentTrials p hp) (cantorPrefix w i) ≠ 0) (T : ℕ) :
    selectedCondSum (independentTrials p hp) R w T = ∑ i ∈ selectedPositions R w T, (p i : ℝ) := by
  unfold selectedCondSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [condOne_independentTrials p hp (hw i), cantorPrefix_length]

/-- Auxiliary for `isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound`: if
`|p i - q| < ε` for `i ≥ N`, then over any finite set `s` of positions the sum of the `p i`
differs from `|s| q` by at most `∑_{i < N} |p i - q| + |s| ε`. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound_sum_le (p : ℕ → NNReal)
    (q ε : ℝ)
    (N : ℕ) (hN : ∀ i, N ≤ i → |(p i : ℝ) - q| < ε) (s : Finset ℕ) :
    |∑ i ∈ s, (p i : ℝ) - s.card * q| ≤
      ∑ i ∈ Finset.range N, |(p i : ℝ) - q| + s.card * ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hN N le_rfl).le
  have h1 : ∑ i ∈ s, (p i : ℝ) - s.card * q = ∑ i ∈ s, ((p i : ℝ) - q) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => i < N)]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_filter] at hi
      simpa using hi.2
    · intro i _ _
      exact abs_nonneg _
  · calc ∑ i ∈ s.filter (fun i => ¬ i < N), |(p i : ℝ) - q|
          ≤ ∑ i ∈ s.filter (fun i => ¬ i < N), ε := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [Finset.mem_filter, not_lt] at hi
            exact (hN i hi.2).le
        _ = (s.filter (fun i => ¬ i < N)).card * ε := by simp
        _ ≤ s.card * ε := by
            apply mul_le_mul_of_nonneg_right _ hε
            exact_mod_cast Finset.card_filter_le _ _

/-- Step 3 of the proof of `isMisesChurchDaleyRandomAt_of_isMartinLofRandom`: measure
bound. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound {p : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1)
    {q : ℝ} (hconv : ConvergesComputably p q) (a b : ℚ) (ha : q < (a : ℝ)) (hb : (b : ℝ) < q) :
    ∃ (n0 : ℕ) (c : ℝ), 0 < c ∧ ∀ R n, 1 ≤ n → n0 ≤ n →
      independentTrials p hp (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_E R a b n) ≤
          ENNReal.ofReal (4 * Real.exp (-(c*(n:ℝ)))) := by
  obtain ⟨ε0, hε0pos, ha', hb'⟩ : ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ (a:ℝ) - q ∧ ε0 ≤ q - (b:ℝ) :=
    ⟨min ((a:ℝ) - q) (q - b), lt_min (by linarith) (by linarith), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨Nf, -, hNf⟩ := hconv.rate
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (show (0:ℝ) < ε0 / 4 by linarith)
  have hNbound : ∀ i, Nf δ ≤ i → |(p i : ℝ) - q| < ε0 / 4 :=
    fun i hi => (hNf δ (by exact_mod_cast hδ0) i hi).trans hδ
  refine ⟨⌈(∑ i ∈ Finset.range (Nf δ), |(p i : ℝ) - q|) / (ε0 / 4)⌉₊, ε0 ^ 2 / 16,
    div_pos (pow_pos hε0pos 2) (by norm_num), ?_⟩
  intro R n hn hn0
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hM0n : ∑ i ∈ Finset.range (Nf δ), |(p i : ℝ) - q| ≤ n * (ε0 / 4) := by
    have h1 : (∑ i ∈ Finset.range (Nf δ), |(p i : ℝ) - q|) / (ε0 / 4) ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn0)
    rwa [div_le_iff₀ (by linarith)] at h1
  -- Off the null set of sequences with a prefix of mass zero, a violation of the bounds `b < q < a`
  -- by `n` selected terms is a deviation of more than `n ε0 / 2` from the conditional sum.
  have hsub : isMisesChurchDaleyRandomAt_of_isMartinLofRandom_E R a b n ⊆
      {w | ∃ i, cantorMass (independentTrials p hp) (cantorPrefix w i) = 0} ∪
      {w | ∃ T, (selectedPositions R w T).card = n ∧
        (n:ℝ) * ε0 / 2 < |selectedOnes R w T - selectedCondSum (independentTrials p hp) R w T|} :=
            by
    rintro w ⟨T, hT, hcases⟩
    by_cases hwZ : ∃ i, cantorMass (independentTrials p hp) (cantorPrefix w i) = 0
    · exact Or.inl hwZ
    · right
      have hw : ∀ i, cantorMass (independentTrials p hp) (cantorPrefix w i) ≠ 0 :=
        fun i hi => hwZ ⟨i, hi⟩
      refine ⟨T, hT, ?_⟩
      rw [isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound_condSum p hp R w hw T]
      have hS := isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound_sum_le p q (ε0 / 4)
        (Nf δ) hNbound (selectedPositions R w T)
      rw [hT] at hS
      have hS' := abs_le.mp (hS.trans (show _ ≤ (n:ℝ) * ε0 / 2 by linarith))
      have hna : (n:ℝ) * ε0 ≤ n * ((a:ℝ) - q) := mul_le_mul_of_nonneg_left ha' hnpos.le
      have hnb : (n:ℝ) * ε0 ≤ n * (q - (b:ℝ)) := mul_le_mul_of_nonneg_left hb' hnpos.le
      rcases hcases with h | h
      · exact lt_abs.mpr (Or.inl (by linarith))
      · exact lt_abs.mpr (Or.inr (by linarith))
  calc independentTrials p hp (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_E R a b n)
      ≤ independentTrials p hp ({w | ∃ i, cantorMass (independentTrials p hp) (cantorPrefix w i) =
          0} ∪
        {w | ∃ T, (selectedPositions R w T).card = n ∧
          (n:ℝ) * ε0 / 2 < |selectedOnes R w T - selectedCondSum (independentTrials p hp) R w
              T|}) :=
        measure_mono hsub
    _ ≤ independentTrials p hp {w | ∃ i, cantorMass (independentTrials p hp) (cantorPrefix w i) = 0}
        +
        independentTrials p hp {w | ∃ T, (selectedPositions R w T).card = n ∧
          (n:ℝ) * ε0 / 2 < |selectedOnes R w T - selectedCondSum (independentTrials p hp) R w T|} :=
        measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal (2 * Real.exp (-((n:ℝ) * ε0 / 2) ^ 2 / (4 * n))) :=
        add_le_add (isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound_null _).le
          (measure_selected_abs_sub_gt_le _ R (by omega)
            (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hε0pos.le) (by norm_num)))
    _ ≤ ENNReal.ofReal (4 * Real.exp (-(ε0 ^ 2 / 16 * (n:ℝ)))) := by
        rw [zero_add]
        apply ENNReal.ofReal_le_ofReal
        have h4n : (4:ℝ) * n ≠ 0 := (mul_pos (by norm_num) hnpos).ne'
        have : -((n:ℝ) * ε0 / 2) ^ 2 / (4 * n) = -(ε0 ^ 2 / 16 * n) := by
          rw [div_eq_iff h4n]; ring
        rw [this]
        linarith [Real.exp_pos (-(ε0 ^ 2 / 16 * (n:ℝ)))]

private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_generic_aux_consts (n0 : ℕ)
    (c : ℝ) (hc : 0 < c) (K : ℝ) :
    ∃ A B : ℕ, n0 ≤ B ∧ 1 ≤ B ∧
      Real.exp (-c) ^ A ≤ 2⁻¹ ∧ max K 0 * Real.exp (-c) ^ B / (1 - Real.exp (-c)) ≤ 1 := by
  have hρ0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hρ1 : Real.exp (-c) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  obtain ⟨A, hA⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 2⁻¹ by norm_num) hρ1
  have hK : 0 ≤ max K 0 := le_max_right _ _
  have hpos : 0 < (1 - Real.exp (-c)) / (max K 0 + 1) := by
    apply div_pos <;> linarith
  obtain ⟨B1, hB1⟩ := exists_pow_lt_of_lt_one hpos hρ1
  refine ⟨A, max B1 (max n0 1), le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_right _ _), hA.le, ?_⟩
  have hle : Real.exp (-c) ^ (max B1 (max n0 1)) ≤ Real.exp (-c) ^ B1 :=
    pow_le_pow_of_le_one hρ0.le hρ1.le (le_max_left _ _)
  have h1 : 0 < 1 - Real.exp (-c) := by linarith
  rw [div_le_one h1]
  have h2 : Real.exp (-c) ^ B1 * (max K 0 + 1) < 1 - Real.exp (-c) := by
    rwa [lt_div_iff₀ (by linarith)] at hB1
  nlinarith [pow_nonneg hρ0.le (max B1 (max n0 1))]

private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_generic_aux_measure
    (μ : Measure CantorSeq)
    (U : ℕ → Set CantorSeq) (n0 : ℕ) (c : ℝ) (hc : 0 < c) (K : ℝ)
    (hbound : ∀ n, 1 ≤ n → n0 ≤ n → μ (U n) ≤ ENNReal.ofReal (K * Real.exp (-(c * (n : ℝ)))))
    (A B : ℕ) (hB0 : n0 ≤ B) (hB1 : 1 ≤ B)
    (hA : Real.exp (-c) ^ A ≤ 2⁻¹)
    (hBB : max K 0 * Real.exp (-c) ^ B / (1 - Real.exp (-c)) ≤ 1) (k : ℕ) :
    μ (⋃ j, U (A * k + B + j)) ≤ dyadicValue 1 k := by
  set ρ := Real.exp (-c) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    rw [hρdef, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have h1 : 0 < 1 - ρ := by linarith
  set K' := max K 0 with hK'
  have hK : 0 ≤ K' := le_max_right _ _
  set m := A * k + B with hm
  have hmB : B ≤ m := by rw [hm]; omega
  have hterm : ∀ j, μ (U (m + j)) ≤ ENNReal.ofReal (K' * ρ ^ m * ρ ^ j) := by
    intro j
    refine le_trans (hbound (m + j) (by omega) (by omega)) (ENNReal.ofReal_le_ofReal ?_)
    have : Real.exp (-(c * ((m + j : ℕ) : ℝ))) = ρ ^ (m + j) := by
      rw [hρdef, ← Real.exp_nat_mul]; congr 1; ring
    rw [this, pow_add]
    have : 0 ≤ ρ ^ m * ρ ^ j := by positivity
    nlinarith [le_max_left K 0, this]
  have hsum : Summable (fun j : ℕ => K' * ρ ^ m * ρ ^ j) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _
  calc μ (⋃ j, U (m + j)) ≤ ∑' j, μ (U (m + j)) := measure_iUnion_le _
    _ ≤ ∑' j, ENNReal.ofReal (K' * ρ ^ m * ρ ^ j) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j, K' * ρ ^ m * ρ ^ j) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum).symm
    _ = ENNReal.ofReal (K' * ρ ^ m / (1 - ρ)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal (2⁻¹ ^ k) := by
        apply ENNReal.ofReal_le_ofReal
        have hpk : ρ ^ m = (ρ ^ A) ^ k * ρ ^ B := by
          rw [hm, pow_add, pow_mul]
        have hAk : (ρ ^ A) ^ k ≤ 2⁻¹ ^ k := pow_le_pow_left₀ (by positivity) hA k
        have : K' * ρ ^ m / (1 - ρ) = (ρ ^ A) ^ k * (K' * ρ ^ B / (1 - ρ)) := by
          rw [hpk]; ring
        rw [this]
        calc (ρ ^ A) ^ k * (K' * ρ ^ B / (1 - ρ)) ≤ (ρ ^ A) ^ k * 1 :=
              mul_le_mul_of_nonneg_left hBB (by positivity)
          _ ≤ 2⁻¹ ^ k := by rw [mul_one]; exact hAk
    _ = dyadicValue 1 k := by
        have h3 : ENNReal.ofReal (2⁻¹ ^ k) = (2 : ℝ≥0∞)⁻¹ ^ k := by
          rw [ENNReal.ofReal_pow (by norm_num)]
          congr 1
          rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
        rw [h3]
        unfold dyadicValue
        have : ((1 : ℕ) : ℝ≥0∞) = 1 := by norm_num
        rw [this, div_eq_mul_inv, one_mul]
        exact ENNReal.inv_pow.symm

/-- Step 4 of the proof of `isMisesChurchDaleyRandomAt_of_isMartinLofRandom`: generic
effectively null. -/
private lemma isMisesChurchDaleyRandomAt_of_isMartinLofRandom_generic (μ : Measure CantorSeq)
    (U : ℕ → Set CantorSeq) (hU : IsUniformlyEffectiveOpen U) (n0 : ℕ) (c : ℝ) (hc : 0 < c) (K : ℝ)
    (hbound : ∀ n, 1 ≤ n → n0 ≤ n → μ (U n) ≤ ENNReal.ofReal (K * Real.exp (-(c * (n : ℝ))))) :
    IsEffectivelyNull μ {w | ∃ᶠ n in atTop, w ∈ U n} := by
  obtain ⟨A, B, hB0, hB1, hA, hBB⟩ :=
    isMisesChurchDaleyRandomAt_of_isMartinLofRandom_generic_aux_consts n0 c hc K
  obtain ⟨f, hf, hUf⟩ := hU
  refine ⟨fun k => ⋃ j, U (A * k + B + j), ?_, ?_, fun k =>
    isMisesChurchDaleyRandomAt_of_isMartinLofRandom_generic_aux_measure μ U n0 c hc K hbound
      A B hB0 hB1 hA hBB k⟩
  · refine ⟨fun k j => f (A * k + B + (Nat.unpair j).1) (Nat.unpair j).2, ?_, ?_⟩
    · have hu2 : Computable (fun p : ℕ × ℕ => (Nat.unpair p.2).2) :=
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
      have hm : Computable (fun p : ℕ × ℕ => A * p.1 + B + (Nat.unpair p.2).1) :=
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const A) Primrec.fst)
            (Primrec.const B)) (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).to_comp
      exact hf.comp₂ hm hu2
    · intro k
      ext x
      simp only [Set.mem_iUnion, hUf]
      constructor
      · rintro ⟨j, i, hi⟩
        exact ⟨Nat.pair j i, by simpa using hi⟩
      · rintro ⟨j, hj⟩
        exact ⟨(Nat.unpair j).1, (Nat.unpair j).2, hj⟩
  · intro w hw
    simp only [Set.mem_iInter, Set.mem_iUnion]
    intro k
    obtain ⟨n, hn, hwn⟩ := (Filter.frequently_atTop.mp hw) (A * k + B)
    exact ⟨n - (A * k + B), by rwa [Nat.add_sub_cancel' hn]⟩

/-- **SUV Theorem 201, p. 305 (van Lambalgen).**  Every Martin-Löf random sequence with respect to
`μ`, independent trials with probabilities `p_i → q` computably, is Mises-Church-Daley random with
frequency `q`. -/
theorem isMisesChurchDaleyRandomAt_of_isMartinLofRandom {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1)
    {q : ℝ} (_hq0 : 0 < q) (_hq1 : q < 1) (hconv : ConvergesComputably p q) {w : CantorSeq}
    (hw : IsMartinLofRandom (independentTrials p hp) w) : IsMisesChurchDaleyRandomAt q w := by
  intro r hr
  by_contra h_not
  rcases isMisesChurchDaleyRandomAt_of_isMartinLofRandom_deterministic (partialRuleSet r)
      h_not with ⟨a, b, hb, ha, hfreq⟩
  have hU_open := isMisesChurchDaleyRandomAt_of_isMartinLofRandom_open r hr a b
  rcases isMisesChurchDaleyRandomAt_of_isMartinLofRandom_bound hp hconv a b ha hb with ⟨n0, c,
      hc, hbound⟩
  have h_null := isMisesChurchDaleyRandomAt_of_isMartinLofRandom_generic (independentTrials p
      hp) _ hU_open n0 c hc 4 (fun n hn hn0 => hbound _ n hn hn0)
  rw [isEffectivelyNull_iff_forall_not_random] at h_null
  · exact h_null w hfreq hw
  · exact isComputableMeasure_independentTrials hp hconv.computable

end Kolmogorov.FrequencyGames
