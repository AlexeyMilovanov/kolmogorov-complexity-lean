/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure
import KolmogorovMathlib.AlgorithmicRandomness.StrongLaw

/-!
# The relations between notions of randomness (SUV Figure 3, p. 310)

The diagram closing Chapter 9, for the uniform measure.  The left column contains the game
definitions, the right one the selection definitions; each notion in a column implies the next one
down:

* left: Martin-Löf; Kolmogorov-Loveland; partial-computably random; computably random; Schnorr;
  Kurtz;
* right: Martin-Löf; Mises-Kolmogorov-Loveland; Mises-Church-Daley; Mises-Church; balanced.

Across: Kolmogorov-Loveland implies Mises-Kolmogorov-Loveland; partial-computably random implies
Mises-Church-Daley; computably random implies Mises-Church; Schnorr implies balanced.  All arrows
but the top one are irreversible.  Whether the top one is reversible is the open question
`KLRandomnessEqualsMartinLofQuestion`, and nothing here settles it.

Implications already stated elsewhere are not stated again: Theorems 182(a), 182(c), 190(a), 192,
`isComputablyRandom_of_isPartialComputablyRandom`, `isSchnorrRandom_of_isComputablyRandom`,
`isKurtzRandom_of_isSchnorrRandom`, `isBalanced_of_isSchnorrRandom`.
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory

private def isPartialComputablyRandom_of_isKLRandom_klBetting (m : BitString →. ℚ)
    (hm : IsPartialMartingale m) : KLBetting where
  next := fun x => Part.some x.length
  capital := m
  noRepeat := by
    intro x y hxy hneq a ha b hb
    rw [Part.mem_some_iff] at ha hb
    subst ha hb
    have h2 : x.length ≠ y.length := by
      intro h
      have h3 : x = y := by
        rcases hxy with ⟨c, hc⟩
        have hlen : y.length = x.length + c.length := by
          rw [← hc, List.length_append]
        rw [← h] at hlen
        have hc_len : c.length = 0 := by omega
        have hc_nil : c = [] := List.length_eq_zero_iff.mp hc_len
        rw [hc_nil, List.append_nil] at hc
        exact hc
      exact hneq h3
    exact h2
  nonneg := hm.nonneg
  fair := hm.fair

private lemma isPartialComputablyRandom_of_isKLRandom_next (m : BitString →. ℚ)
    (hm : IsPartialMartingale m) : Partrec (isPartialComputablyRandom_of_isKLRandom_klBetting m
        hm).next := by
  have h1 : (isPartialComputablyRandom_of_isKLRandom_klBetting m hm).next = fun x =>
    Part.some x.length := rfl
  rw [h1]
  apply Computable.partrec
  exact Computable.list_length

private lemma isPartialComputablyRandom_of_isKLRandom_capital (m : BitString →. ℚ)
    (hm : IsPartialMartingale m) (hcomp : Partrec m) :
    Partrec (isPartialComputablyRandom_of_isKLRandom_klBetting m hm).capital := by
  exact hcomp

private lemma isPartialComputablyRandom_of_isKLRandom_wins_aux {w : CantorSeq} (m : BitString →. ℚ)
    (hm : IsPartialMartingale m) :
    ∀ t, (isPartialComputablyRandom_of_isKLRandom_klBetting m hm).toRule.revealed w t = cantorPrefix
        w t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ht =>
    have hstep : (isPartialComputablyRandom_of_isKLRandom_klBetting m hm).toRule.revealed w (t + 1)
        =
        (isPartialComputablyRandom_of_isKLRandom_klBetting m hm).toRule.revealed w t ++
            [w ((isPartialComputablyRandom_of_isKLRandom_klBetting m hm).toRule.revealed w
            t).length] := by
      rw [KLRule.revealed]
      dsimp [isPartialComputablyRandom_of_isKLRandom_klBetting, KLBetting.toRule]
      simp
    rw [hstep, ht]
    have hlen : (cantorPrefix w t).length = t := by
      exact cantorPrefix_length w t
    rw [hlen]
    exact (cantorPrefix_succ w t).symm

private lemma isPartialComputablyRandom_of_isKLRandom_wins {w : CantorSeq} (m : BitString →. ℚ)
    (hm : IsPartialMartingale m) (hwins : PartialWins m w) :
    (isPartialComputablyRandom_of_isKLRandom_klBetting m hm).Wins w := by
  rcases hwins with ⟨hdom, hunbdd⟩
  constructor
  · intro t
    have ht : (cantorPrefix w t).length = t := by
      exact cantorPrefix_length w t
    have hrw1 := isPartialComputablyRandom_of_isKLRandom_wins_aux (w := w) m hm t
    rw [hrw1]
    rw [ht]
  constructor
  · intro t
    have hrw1 := isPartialComputablyRandom_of_isKLRandom_wins_aux (w := w) m hm t
    rw [hrw1]
    exact hdom t
  · intro h
    apply hunbdd
    have hset : {r | ∃ t, ∃ q ∈ (isPartialComputablyRandom_of_isKLRandom_klBetting m hm).capital
        ((isPartialComputablyRandom_of_isKLRandom_klBetting m hm).toRule.revealed w t), (q : ℝ) =
        r} = {r | ∃ n, ∃ q ∈ m (cantorPrefix w n), (q : ℝ) = r} := by
      ext r
      constructor
      · intro hr
        rcases hr with ⟨t, q, hq, hqr⟩
        use t
        have hrw1 := isPartialComputablyRandom_of_isKLRandom_wins_aux (w := w) m hm t
        rw [hrw1] at hq
        use q
        exact ⟨hq, hqr⟩
      · intro hr
        rcases hr with ⟨n, q, hq, hqr⟩
        use n
        have hrw1 := isPartialComputablyRandom_of_isKLRandom_wins_aux (w := w) m hm n
        rw [hrw1]
        use q
        exact ⟨hq, hqr⟩
    rw [← hset]
    exact h

/-- **SUV Figure 3, p. 310.**  Kolmogorov-Loveland random sequences are partial-computably random: a
partial martingale is a non-monotonic betting strategy revealing the bits in order. -/
theorem isPartialComputablyRandom_of_isKLRandom {w : CantorSeq} (hw : IsKLRandom w) :
    IsPartialComputablyRandom w := by
  intro m hm hpm hwins
  have hnext := isPartialComputablyRandom_of_isKLRandom_next m hpm
  have hcap := isPartialComputablyRandom_of_isKLRandom_capital m hpm hm
  have hβwins := isPartialComputablyRandom_of_isKLRandom_wins m hpm hwins
  exact hw _ hnext hcap hβwins


/-- Step 1 of the proof of `isMisesKLRandom_of_isKLRandom_run_facts`: next. -/
private lemma isMisesKLRandom_of_isKLRandom_next
    {ρ : KLRule} {w u : CantorSeq} (hout : ρ.output w = .infinite u) :
    ∀ t, (ρ.next (ρ.revealed w t)).Dom := by
  intro t
  by_contra h_not_dom
  have h_rev : ∀ j, ρ.revealed w (t + j) = ρ.revealed w t := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have : t + (j + 1) = t + j + 1 := by omega
      rw [this, KLRule.revealed, ih]
      simp [h_not_dom]
  have h_out : ∀ j, ρ.outputChain w (t + j) = ρ.outputChain w t := by
    intro j
    unfold KLRule.outputChain
    rw [h_rev j]
  have h_bdd : BddAbove (Set.range (fun j => (ρ.outputChain w j).length)) := by
    use (Finset.range t).sup (fun j => (ρ.outputChain w j).length) ⊔ (ρ.outputChain w t).length
    rintro _ ⟨j, rfl⟩
    by_cases hj : j < t
    · change (ρ.outputChain w j).length ≤ _
      exact le_sup_of_le_left (Finset.le_sup (f := fun j => (ρ.outputChain w j).length)
          (Finset.mem_range.mpr hj))
    · push Not at hj
      have hj_eq : j = t + (j - t) := by omega
      have : (ρ.outputChain w j).length = (ρ.outputChain w t).length := by
        nth_rw 1 [hj_eq]
        rw [h_out]
      change (ρ.outputChain w j).length ≤ _
      rw [this]
      exact le_sup_right
  have h_bdd_prefixSet : ∃ M, ∀ x ∈ chainPrefixSet (ρ.outputChain w), List.length x ≤ M := by
    obtain ⟨M, hM⟩ := h_bdd
    use M
    rintro y ⟨n, hn⟩
    have h_len : y.length ≤ (ρ.outputChain w n).length := List.IsPrefix.length_le hn
    exact le_trans h_len (hM ⟨n, rfl⟩)
  have h_fin : BitStream.ofPrefixSet (chainPrefixSet (ρ.outputChain w))
      (isStreamPrefixSet_chainPrefixSet (KLRule.outputChain_prefix ρ w)) = BitStream.finite
      (Classical.choose (exists_greatest_of_bddAbove_length (isStreamPrefixSet_chainPrefixSet
      (KLRule.outputChain_prefix ρ w)) h_bdd_prefixSet)) := by
    rw [BitStream.ofPrefixSet]
    split_ifs
    · rfl
  have h_fin' : ρ.output w = BitStream.finite (Classical.choose (exists_greatest_of_bddAbove_length
      (isStreamPrefixSet_chainPrefixSet (KLRule.outputChain_prefix ρ w)) h_bdd_prefixSet)) := by
    unfold KLRule.output streamOfChain
    exact h_fin
  rw [h_fin'] at hout
  contradiction

/-- Step 2 of the proof of `isMisesKLRandom_of_isKLRandom_run_facts`: sel. -/
private lemma isMisesKLRandom_of_isKLRandom_sel
    {ρ : KLRule} {w u : CantorSeq} (hout : ρ.output w = .infinite u) :
    ∀ t i, i ≤ (ρ.revealed w t).length →
      (ρ.sel ((ρ.revealed w t).take i)).Dom := by
  intro t i hi
  by_contra hndom
  let R := partialRuleSet ρ.sel
  have h_not_in_R : ∀ (z : BitString), ((ρ.revealed w t).take i) <+: z → z ∉ R := by
    intro z hz hz_in
    have h_dom := hz_in.1 ((ρ.revealed w t).take i) hz
    exact hndom h_dom
  have h_sel_z : ∀ (z : BitString), ((ρ.revealed w t).take i) <+: z → selectedBits R z =
      selectedBits R ((ρ.revealed w t).take i) := by
    intro z hz
    unfold selectedBits
    obtain ⟨y, rfl⟩ := hz
    rw [selectedAux_append]
    have h_empty : ∀ (y' : BitString),
        selectedAux R ([] ++ (ρ.revealed w t).take i ++ y') y = [] := by
      induction y with
      | nil => simp [selectedAux]
      | cons b y ih =>
        intro y'
        simp only [selectedAux]
        have h_in : [] ++ (ρ.revealed w t).take i ++ y' ∉ R := by
          rw [List.nil_append]
          apply h_not_in_R
          exact List.prefix_append _ _
        open Classical in
        rw [ite_eq_right_iff.mpr (fun h => (h_in h).elim)]
        rw [List.nil_append, List.append_assoc]
        exact ih (y' ++ [b])
    have hh : selectedAux R ([] ++ (ρ.revealed w t).take i) y = [] := by
      have hh' := h_empty []
      rw [List.append_nil] at hh'
      exact hh'
    rw [hh, List.append_nil]
  have h_bound : ∀ s, t ≤ s → ρ.outputChain w s = selectedBits R ((ρ.revealed w t).take i) := by
    intro s hts
    unfold KLRule.outputChain
    have h_pref : ((ρ.revealed w t).take i) <+: (ρ.revealed w s) := by
      apply List.IsPrefix.trans (List.take_prefix i _)
      induction hts with
      | refl => exact List.prefix_rfl
      | @step s' _ ih => apply List.IsPrefix.trans ih (KLRule.revealed_prefix ρ w s')
    apply h_sel_z _ h_pref
  have h_len_bound : ∀ s, t ≤ s → (ρ.outputChain w s).length =
      (selectedBits R ((ρ.revealed w t).take i)).length := by
    intro s hts
    rw [h_bound s hts]
  have h_fin : BitStream.ofPrefixSet (chainPrefixSet (ρ.outputChain w))
      (isStreamPrefixSet_chainPrefixSet (KLRule.outputChain_prefix ρ w)) = .finite
      (Classical.choose (exists_greatest_of_bddAbove_length (isStreamPrefixSet_chainPrefixSet
      (KLRule.outputChain_prefix ρ w)) ⟨max ((Finset.range t).sup
      (fun s => (ρ.outputChain w s).length)) (selectedBits R ((ρ.revealed w t).take i)).length, by
    rintro s ⟨s_len, hh⟩
    by_cases hts : t ≤ s_len
    · have h_len := hh.length_le
      rw [h_len_bound s_len hts] at h_len
      exact h_len.trans (le_max_right _ _)
    · push Not at hts
      have h_len := hh.length_le
      have : (ρ.outputChain w s_len).length ≤ (Finset.range t).sup
          (fun s => (ρ.outputChain w s).length) := by
        apply Finset.le_sup (f := fun s => (ρ.outputChain w s).length)
        rw [Finset.mem_range]
        exact hts
      exact h_len.trans (this.trans (le_max_left _ _))
  ⟩)) := by
    unfold BitStream.ofPrefixSet
    split_ifs with h_bdd
    · rfl
    · exfalso
      exact h_bdd ⟨max ((Finset.range t).sup (fun s => (ρ.outputChain w s).length))
          (selectedBits R ((ρ.revealed w t).take i)).length, by
        rintro s ⟨s_len, hh⟩
        by_cases hts : t ≤ s_len
        · have h_len := hh.length_le
          rw [h_len_bound s_len hts] at h_len
          exact h_len.trans (le_max_right _ _)
        · push Not at hts
          have h_len := hh.length_le
          have : (ρ.outputChain w s_len).length ≤ (Finset.range t).sup
              (fun s => (ρ.outputChain w s).length) := by
            apply Finset.le_sup (f := fun s => (ρ.outputChain w s).length)
            rw [Finset.mem_range]
            exact hts
          exact h_len.trans (this.trans (le_max_left _ _))
      ⟩
  unfold KLRule.output at hout
  unfold streamOfChain at hout
  rw [h_fin] at hout
  contradiction

/-- Step 3 of the proof of `isMisesKLRandom_of_isKLRandom_run_facts`: outputChain
prefix. -/
private lemma isMisesKLRandom_of_isKLRandom_outputChain_prefix
    {ρ : KLRule} {w u : CantorSeq} (hout : ρ.output w = .infinite u) :
    ∀ t, ∃ k, ρ.outputChain w t = cantorPrefix u k := by
  intro t
  have h1 : ρ.outputChain w t ∈ chainPrefixSet (ρ.outputChain w) := by
    exact ⟨t, List.prefix_rfl⟩
  have h2 : BitStream.finite (ρ.outputChain w t) ≤
      BitStream.ofPrefixSet (chainPrefixSet (ρ.outputChain w))
        (isStreamPrefixSet_chainPrefixSet (KLRule.outputChain_prefix ρ w)) :=
    (BitStream.finite_le_ofPrefixSet_iff
      (isStreamPrefixSet_chainPrefixSet (KLRule.outputChain_prefix ρ w))
      (ρ.outputChain w t)).mpr h1
  have h3 : BitStream.ofPrefixSet (chainPrefixSet (ρ.outputChain w))
      (isStreamPrefixSet_chainPrefixSet (KLRule.outputChain_prefix ρ w)) = .infinite u := by
    simpa [KLRule.output, streamOfChain] using hout
  rw [h3] at h2
  have hp : IsCantorPrefix (ρ.outputChain w t) u :=
    BitStream.finite_le_infinite_iff.mp h2
  exact ⟨(ρ.outputChain w t).length,
    ((isCantorPrefix_iff_cantorPrefix_eq (ρ.outputChain w t) u).mp hp).symm⟩

/-- Step 4 of the proof of `isMisesKLRandom_of_isKLRandom_run_facts`: outputChain
length. -/
private lemma isMisesKLRandom_of_isKLRandom_outputChain_length
    {ρ : KLRule} {w u : CantorSeq} (hout : ρ.output w = .infinite u) :
    ∀ k, ∃ t, (ρ.outputChain w t).length = k := by
  intro k
  have h_step : ∀ t, (ρ.outputChain w (t + 1)).length ≤ (ρ.outputChain w t).length + 1 := by
    intro t
    unfold KLRule.outputChain
    have h_rev_pre := KLRule.revealed_prefix ρ w t
    rcases h_rev_pre with ⟨z, hz⟩
    rw [← hz]
    have h_aux : selectedBits (partialRuleSet ρ.sel) (ρ.revealed w t ++ z) = selectedBits
        (partialRuleSet ρ.sel) (ρ.revealed w t) ++ selectedAux (partialRuleSet ρ.sel)
        (ρ.revealed w t) z := by
      exact selectedAux_append (partialRuleSet ρ.sel) [] (ρ.revealed w t) z
    rw [h_aux]
    have hz_len : z.length ≤ 1 := by
      have h_len : (ρ.revealed w (t + 1)).length ≤ (ρ.revealed w t).length + 1 := by
        have h_eq : ρ.revealed w (t + 1) = @dite (List Bool) ((ρ.next (ρ.revealed w t)).Dom)
            (Classical.propDecidable _) (fun h => (ρ.revealed w t) ++
                                                    [w ((ρ.next (ρ.revealed w t)).get h)])
                                                    (fun _ => (ρ.revealed w t)) := rfl
        rw [h_eq]
        split_ifs with h_if
        · rw [List.length_append, List.length_singleton]
        · linarith
      have h_len_app : (ρ.revealed w t ++ z).length = (ρ.revealed w t).length + z.length := by
        rw [List.length_append]
      rw [hz] at h_len_app
      linarith
    have h_sel_len : ∀ pre z_, (selectedAux (partialRuleSet ρ.sel) pre z_).length ≤ z_.length := by
      intro pre z_
      induction z_ generalizing pre with
      | nil => rfl
      | cons b z_ ih =>
        rw [selectedAux]
        split_ifs
        · rw [List.length_append, List.length_singleton]
          have h_ih := ih (pre ++ [b])
          have h_len_b : (b :: z_).length = z_.length + 1 := rfl
          linarith
        · rw [List.nil_append]
          have h_ih := ih (pre ++ [b])
          have h_len_b : (b :: z_).length = z_.length + 1 := rfl
          linarith
    have h_z := h_sel_len (ρ.revealed w t) z
    rw [List.length_append]
    linarith
  have h_unbdd : ∀ M, ∃ x ∈ chainPrefixSet (ρ.outputChain w), M < x.length := by
    intro M
    by_contra h_bdd
    push Not at h_bdd
    have h_fin : BitStream.ofPrefixSet (chainPrefixSet (ρ.outputChain w))
        (isStreamPrefixSet_chainPrefixSet (KLRule.outputChain_prefix ρ w)) = .finite
        (Classical.choose (exists_greatest_of_bddAbove_length (isStreamPrefixSet_chainPrefixSet
        (KLRule.outputChain_prefix ρ w)) ⟨M, h_bdd⟩)) := by
      unfold BitStream.ofPrefixSet
      split_ifs with h_if
      · rfl
      · exfalso
        exact h_if ⟨M, h_bdd⟩
    unfold KLRule.output at hout
    unfold streamOfChain at hout
    rw [h_fin] at hout
    contradiction
  have h_t : ∃ t, k ≤ (ρ.outputChain w t).length := by
    obtain ⟨x, ⟨t, ht⟩, hx⟩ := h_unbdd k
    exact ⟨t, (le_of_lt hx).trans ht.length_le⟩
  obtain ⟨t, ht⟩ := h_t
  induction t with
  | zero =>
    have h0 : (ρ.outputChain w 0).length = 0 := rfl
    have h_k_eq_0 : k = 0 := by linarith
    rw [h_k_eq_0]
    exact ⟨0, rfl⟩
  | succ t ih =>
    by_cases h_k_t : k ≤ (ρ.outputChain w t).length
    · exact ih h_k_t
    · have h_k_t' : (ρ.outputChain w t).length < k := by linarith
      have h_step_t := h_step t
      have h_eq : (ρ.outputChain w (t + 1)).length = k := by linarith
      exact ⟨t + 1, h_eq⟩

/-- Step 1 of the proof of `isMisesKLRandom_of_isKLRandom`: run facts. -/
private lemma isMisesKLRandom_of_isKLRandom_run_facts
    {ρ : KLRule} {w u : CantorSeq} (hout : ρ.output w = .infinite u) :
    (∀ t, (ρ.next (ρ.revealed w t)).Dom) ∧
    (∀ t i, i ≤ (ρ.revealed w t).length → (ρ.sel ((ρ.revealed w t).take i)).Dom) ∧
    (∀ t, ∃ k, ρ.outputChain w t = cantorPrefix u k) ∧
    (∀ k, ∃ t, (ρ.outputChain w t).length = k) := by
  exact ⟨isMisesKLRandom_of_isKLRandom_next hout,
         isMisesKLRandom_of_isKLRandom_sel hout,
         isMisesKLRandom_of_isKLRandom_outputChain_prefix hout,
         isMisesKLRandom_of_isKLRandom_outputChain_length hout⟩

private def isMisesKLRandom_of_isKLRandom_construction_loop
    (r : BitString →. Bool) (x : BitString) : ℕ → Part BitString
  | 0 => Part.some []
  | k + 1 => (isMisesKLRandom_of_isKLRandom_construction_loop r x k).bind fun s =>
      (r (x.take k)).map fun b => s ++ cond b [x.getD k false] []

private def isMisesKLRandom_of_isKLRandom_construction_m
    (r : BitString →. Bool) (M : BitString → ℚ) (x : BitString) : Part ℚ :=
  (r x).bind fun _ => (isMisesKLRandom_of_isKLRandom_construction_loop r x x.length).map M

private lemma isMisesKLRandom_of_isKLRandom_partrec
    {r : BitString →. Bool} (hr : Partrec r)
    {M : BitString → ℚ} (hM_comp : Computable M) :
    Partrec (isMisesKLRandom_of_isKLRandom_construction_m r M) := by
  have h_step : Partrec₂ (fun (x : BitString) (p : ℕ × BitString) =>
      (r (x.take p.1)).map fun b => p.2 ++ cond b [x.getD p.1 false] []) := by
    apply Partrec.map
    · exact hr.comp (Primrec.list_take.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).to_comp
    · have h1 : Primrec₂ fun (p : (BitString × ℕ × BitString)) (b : Bool) =>
        p.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
      have h2 : Primrec₂ fun (p : (BitString × ℕ × BitString)) (b : Bool) =>
        cond b [p.1.getD p.2.1 false] [] :=
        Primrec.cond (Primrec.snd)
          (Primrec.list_cons.comp (Primrec.list_getD false |>.comp (Primrec.fst.comp Primrec.fst)
              (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const []))
          (Primrec.const [])
      exact (Primrec.list_append.comp h1 h2).to_comp
  have h_init : Partrec (fun _x : BitString => (Part.some [] : Part BitString)) :=
    Computable.ofOption (Computable.const (some []))
  have h_loop : Partrec (fun x : BitString => isMisesKLRandom_of_isKLRandom_construction_loop
                                                r x x.length) := by
    have H := @Partrec.nat_rec BitString BitString _ _ (fun x => x.length) _ _
        Computable.list_length h_init h_step
    exact H.of_eq <| fun x => by
      have h_ind : ∀ k, (Nat.rec (motive := fun _ => Part BitString) (Part.some [])
          (fun y IH => IH.bind fun a => Part.map
            (fun b => a ++ bif b then [List.getD x y false] else []) (r (List.take y x)))
          k) = isMisesKLRandom_of_isKLRandom_construction_loop r x k := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          dsimp only [isMisesKLRandom_of_isKLRandom_construction_loop, Nat.rec]
          rw [ih]
      exact h_ind x.length
  have h_loop_map : Partrec (fun x : BitString =>
    (isMisesKLRandom_of_isKLRandom_construction_loop r x x.length).map M) :=
    Partrec.map h_loop (hM_comp.comp Computable.snd)
  exact (Partrec.bind hr (h_loop_map.comp Computable.fst).to₂).of_eq <| fun x => by rfl

private lemma isMisesKLRandom_of_isKLRandom_loop_dom
    (r : BitString →. Bool) (x : BitString) (k : ℕ) :
    (isMisesKLRandom_of_isKLRandom_construction_loop r x k).Dom ↔ ∀ j < k,
        (r (x.take j)).Dom := by
  induction k with
  | zero => simp [isMisesKLRandom_of_isKLRandom_construction_loop]
  | succ k ih =>
    change ((isMisesKLRandom_of_isKLRandom_construction_loop r x k).bind fun s =>
      (r (x.take k)).map fun b => s ++ cond b [x.getD k false] []).Dom ↔ ∀ j < k + 1,
                                    (r (x.take j)).Dom
    simp only [Part.bind_dom, Part.map, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact h1 j hj'
      · exact h2
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self k)⟩

private lemma isMisesKLRandom_of_isKLRandom_dom
    (r : BitString →. Bool) (M : BitString → ℚ) (x : BitString) :
    (isMisesKLRandom_of_isKLRandom_construction_m r M x).Dom ↔ ∀ y, y <+: x → (r y).Dom := by
  dsimp [isMisesKLRandom_of_isKLRandom_construction_m]
  rw [Part.bind_dom]
  have h_map_dom (f : BitString → ℚ) (p : Part BitString) : (p.map f).Dom ↔ p.Dom := Iff.rfl
  simp only [h_map_dom, isMisesKLRandom_of_isKLRandom_loop_dom]
  constructor
  · rintro ⟨hx, hloop⟩ y hy
    have hy2 : y = x.take y.length := List.prefix_iff_eq_take.mp hy
    rw [hy2]
    rcases lt_trichotomy y.length x.length with h | h | h
    · exact hloop y.length h
    · rw [h, List.take_length]
      exact hx
    · rw [List.take_of_length_le (le_of_lt h)]
      exact hx
  · intro h
    refine ⟨?_, ?_⟩
    · exact h x List.prefix_rfl
    · intro j hj
      exact h (x.take j) (List.take_prefix j x)

private lemma isMisesKLRandom_of_isKLRandom_loop_val
    (r : BitString →. Bool) (x : BitString) (k : ℕ) (hk : k ≤ x.length) (hr_dom : ∀ j < k,
        (r (x.take j)).Dom) :
    ∀ s ∈ isMisesKLRandom_of_isKLRandom_construction_loop r x k, s = selectedBits
        (partialRuleSet r) (x.take k) := by
  induction k with
  | zero =>
    intro s hs
    have h : s = [] := Part.mem_unique hs (Part.mem_some _)
    rw [h, List.take_zero]
    rfl
  | succ k ih =>
    intro s hs
    change s ∈ (isMisesKLRandom_of_isKLRandom_construction_loop r x k).bind fun s =>
      (r (x.take k)).map fun b => s ++ cond b [x.getD k false] [] at hs
    rcases Part.mem_bind_iff.mp hs with ⟨s', hs', hmap⟩
    rcases (Part.mem_map_iff _).mp hmap with ⟨b, hb, rfl⟩
    have hr_dom_k : ∀ j < k, (r (x.take j)).Dom := fun j hj => hr_dom j (Nat.lt_succ_of_lt hj)
    have hs'_val := ih (le_trans (Nat.le_succ _) hk) hr_dom_k s' hs'
    rw [hs'_val]
    open Classical in
    have h_sel : selectedBits (partialRuleSet r) (x.take (k + 1)) = selectedBits (partialRuleSet r)
        (x.take k) ++ (if x.take k ∈ partialRuleSet r then [x.getD k false] else []) := by
      have h_take : x.take (k + 1) = x.take k ++ [x.getD k false] := by
        have hk_lt : k < x.length := by omega
        have h_get : x[k]? = some (x.getD k false) := by
          rw [List.getElem?_eq_getElem hk_lt]
          have h_getD : x.getD k false = x[k] := by
            apply List.getD_eq_getElem x false hk_lt
          rw [h_getD]
        rw [List.take_add_one, h_get, Option.toList_some]
      nth_rw 1 [h_take]
      exact selectedBits_append_singleton (partialRuleSet r) (x.take k) (x.getD k false)
    rw [h_sel]
    have hr : (r (x.take k)).Dom := hr_dom k (Nat.lt_succ_self k)
    have h_mem : x.take k ∈ partialRuleSet r ↔ b = true := by
      simp only [partialRuleSet, Set.mem_ofPred_eq]
      refine ⟨fun h => (Part.mem_unique (a := true) h.2 hb).symm, fun h => ⟨fun y hy => ?_, ?_⟩⟩
      · have hy_eq : y = (x.take k).take y.length := List.prefix_iff_eq_take.mp hy
        have hlen := hy.length_le
        have h_len_take : (x.take k).length ≤ k := List.length_take_le k x
        rw [hy_eq, List.take_take]
        have hmin : min y.length k = y.length := Nat.min_eq_left (by omega)
        rw [hmin]
        exact hr_dom y.length (by omega)
      · rw [h] at hb
        exact hb
    open Classical in
    by_cases hx : b = true
    · have h_mem_true : x.take k ∈ partialRuleSet r := h_mem.mpr hx
      rw [hx]
      rw [ite_eq_left h_mem_true]
      rfl
    · have h_not_mem : x.take k ∉ partialRuleSet r := fun h => hx (h_mem.mp h)
      have hb_false : b = false := by cases b <;> simp_all
      rw [hb_false]
      rw [ite_eq_right h_not_mem]
      rfl

private lemma isMisesKLRandom_of_isKLRandom_val
    (r : BitString →. Bool) (M : BitString → ℚ) (x : BitString) :
    ∀ q ∈ isMisesKLRandom_of_isKLRandom_construction_m r M x,
      (isMisesKLRandom_of_isKLRandom_construction_m r M x).Dom ∧ q =
          M (selectedBits (partialRuleSet r) x) := by
  intro q hq
  constructor
  · exact Part.dom_iff_mem.mpr ⟨q, hq⟩
  · dsimp [isMisesKLRandom_of_isKLRandom_construction_m] at hq
    rcases Part.mem_bind_iff.mp hq with ⟨b, hrx, hmap⟩
    rcases (Part.mem_map_iff _).mp hmap with ⟨s, hs, rfl⟩
    have hr_dom : ∀ j < x.length, (r (x.take j)).Dom := by
      intro j hj
      have h_dom := (isMisesKLRandom_of_isKLRandom_dom r M x).mp
          (Part.dom_iff_mem.mpr ⟨_, hq⟩)
      exact h_dom (x.take j) (List.take_prefix j x)
    have h_loop := isMisesKLRandom_of_isKLRandom_loop_val r x x.length
        le_rfl hr_dom s hs
    rw [h_loop, List.take_length]

private def isMisesKLRandom_of_isKLRandom_construction_M (c : ℚ) (l : BitString) : ℚ :=
  (1 + c) ^ l.count true * (1 - c) ^ l.count false

private lemma isMisesKLRandom_of_isKLRandom_construction_M_nonneg {c : ℚ} (hc : |c| ≤ 1) :
    ∀ x, 0 ≤ isMisesKLRandom_of_isKLRandom_construction_M c x := by
  intro x
  dsimp [isMisesKLRandom_of_isKLRandom_construction_M]
  have hc_le : c ≤ 1 := by exact (abs_le.mp hc).2
  have hc_ge : -1 ≤ c := by exact (abs_le.mp hc).1
  have h1 : 0 ≤ 1 + c := by linarith
  have h2 : 0 ≤ 1 - c := by linarith
  apply mul_nonneg
  · exact pow_nonneg h1 _
  · exact pow_nonneg h2 _

private lemma isMisesKLRandom_of_isKLRandom_construction_M_fair {c : ℚ} :
    ∀ x, isMisesKLRandom_of_isKLRandom_construction_M c x =
      (isMisesKLRandom_of_isKLRandom_construction_M c (x ++ [false]) +
       isMisesKLRandom_of_isKLRandom_construction_M c (x ++ [true])) / 2 := by
  intro x
  dsimp [isMisesKLRandom_of_isKLRandom_construction_M]
  have h_count_true_false : (x ++ [false]).count true = x.count true := by
    simp [List.count_append]
  have h_count_false_false : (x ++ [false]).count false = x.count false + 1 := by
    simp [List.count_append]
  have h_count_true_true : (x ++ [true]).count true = x.count true + 1 := by
    simp [List.count_append]
  have h_count_false_true : (x ++ [true]).count false = x.count false := by
    simp [List.count_append]
  rw [h_count_true_false, h_count_false_false, h_count_true_true, h_count_false_true]
  have h_pow_true : (1 + c) ^ (x.count true + 1) = (1 + c) ^ x.count true * (1 + c) := by ring
  have h_pow_false : (1 - c) ^ (x.count false + 1) = (1 - c) ^ x.count false * (1 - c) := by ring
  rw [h_pow_true, h_pow_false]
  ring

private lemma computable_rat_pow (q : ℚ) :
    Computable (fun n : ℕ => q ^ n) := by
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × ℚ) => p.2 * q) :=
    Kolmogorov.computable₂_ratMul.comp
      (Computable.snd.comp Computable.snd) (Computable.const q)
  have h := Computable.nat_rec
    (f := fun n : ℕ => n)
    (g := fun _ : ℕ => (1 : ℚ))
    (h := fun (_ : ℕ) (p : ℕ × ℚ) => p.2 * q)
    Computable.id (Computable.const (1 : ℚ)) hstep
  exact h.of_eq fun n => by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, ih]

private lemma isMisesKLRandom_of_isKLRandom_construction_M_comp {c : ℚ} :
    Computable (isMisesKLRandom_of_isKLRandom_construction_M c) := by
  have h_count_true : Computable (fun l : BitString => l.count true) := by
    have h := list_countP_primrec
        (f := fun l : BitString => l)
        (p := fun l z => decide (z = true))
        Primrec.id
        (Primrec.eq.decide.comp Primrec.snd (Primrec.const true))
    exact h.to_comp.of_eq (fun y => by simp [List.count_eq_countP, beq_eq_decide])
  have h_count_false : Computable (fun l : BitString => l.count false) := by
    have h := list_countP_primrec
        (f := fun l : BitString => l)
        (p := fun l z => decide (z = false))
        Primrec.id
        (Primrec.eq.decide.comp Primrec.snd (Primrec.const false))
    exact h.to_comp.of_eq (fun y => by simp [List.count_eq_countP, beq_eq_decide])
  have h_pow_true : Computable (fun l : BitString => (1 + c) ^ l.count true) :=
    (computable_rat_pow (1 + c)).comp h_count_true
  have h_pow_false : Computable (fun l : BitString => (1 - c) ^ l.count false) :=
    (computable_rat_pow (1 - c)).comp h_count_false
  exact (Computable₂.comp (f := fun a b : ℚ => a * b) computable₂_ratMul h_pow_true
      h_pow_false).of_eq (fun _ => rfl)

/-- Step 2 of the proof of `isMisesKLRandom_of_isKLRandom`: construction. -/
private lemma isMisesKLRandom_of_isKLRandom_construction
    {ρ : KLRule} (hρ : ρ.IsAdmissible) (c : ℚ) (hc : |c| ≤ 1) :
    ∃ β : KLBetting,
      β.next = ρ.next ∧
      Partrec β.capital ∧
      ∀ x, (∀ i, i ≤ x.length → (ρ.sel (x.take i)).Dom) →
        ∃ q ∈ β.capital x, (q : ℝ) =
          (1 + (c : ℝ)) ^ (selectedBits (partialRuleSet ρ.sel) x).count true *
          (1 - (c : ℝ)) ^ (selectedBits (partialRuleSet ρ.sel) x).count false := by
  let M := isMisesKLRandom_of_isKLRandom_construction_M c
  let β : KLBetting := {
    next := ρ.next
    capital := isMisesKLRandom_of_isKLRandom_construction_m ρ.sel M
    noRepeat := ρ.noRepeat
    nonneg := by
      intro x q hq
      have hval := isMisesKLRandom_of_isKLRandom_val ρ.sel M x q hq
      rw [hval.2]
      exact isMisesKLRandom_of_isKLRandom_construction_M_nonneg hc _
    fair := by
      intro x q q0 q1 hq hq0 hq1
      have hval_q := isMisesKLRandom_of_isKLRandom_val ρ.sel M x q hq
      have hval_q0 := isMisesKLRandom_of_isKLRandom_val ρ.sel M
          (x ++ [false]) q0 hq0
      have hval_q1 := isMisesKLRandom_of_isKLRandom_val ρ.sel M
          (x ++ [true]) q1 hq1
      rw [hval_q.2, hval_q0.2, hval_q1.2]
      open Classical in
      by_cases hx : x ∈ partialRuleSet ρ.sel
      · rw [selectedBits_append_singleton (partialRuleSet ρ.sel) x false,
          selectedBits_append_singleton (partialRuleSet ρ.sel) x true]
        rw [ite_eq_left hx, ite_eq_left hx]
        exact isMisesKLRandom_of_isKLRandom_construction_M_fair (c := c)
            (selectedBits (partialRuleSet ρ.sel) x)
      · rw [selectedBits_append_singleton (partialRuleSet ρ.sel) x false,
          selectedBits_append_singleton (partialRuleSet ρ.sel) x true]
        rw [ite_eq_right hx, ite_eq_right hx]
        simp only [List.append_nil]
        ring
  }
  use β
  refine ⟨rfl, ?_, ?_⟩
  · exact isMisesKLRandom_of_isKLRandom_partrec hρ.2
      (isMisesKLRandom_of_isKLRandom_construction_M_comp (c := c))
  · intro x hx
    have hdom : (β.capital x).Dom := by
      apply (isMisesKLRandom_of_isKLRandom_dom ρ.sel M x).mpr
      intro y hy
      have hy_eq := List.prefix_iff_eq_take.mp hy
      rw [hy_eq]
      have hlen := hy.length_le
      exact hx y.length (by omega)
    have ⟨q, hq⟩ := Part.dom_iff_mem.mp hdom
    use q, hq
    have hval := isMisesKLRandom_of_isKLRandom_val ρ.sel M x q hq
    rw [hval.2]
    dsimp [M, isMisesKLRandom_of_isKLRandom_construction_M]
    push_cast
    rfl


/-- Step 3 of the proof of `isMisesKLRandom_of_isKLRandom`: analysis. -/
private lemma isMisesKLRandom_of_isKLRandom_analysis
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℚ, 0 < c ∧ c < 1 ∧ ∃ γ : ℝ, 1 < γ ∧
      ∀ a b : ℕ, (1 / 2 + δ) * (a + b : ℝ) < (a : ℝ) →
        γ ^ (a + b) ≤ (1 + (c : ℝ)) ^ a * (1 - (c : ℝ)) ^ b := by
  by_cases hδ' : δ < 1/2
  · -- δ < 1/2
    have h_min : 0 < min (2 * δ) 1 := by
      apply lt_min
      · linarith
      · norm_num
    obtain ⟨c, hc_pos, hc_lt⟩ := exists_rat_btwn h_min
    have hc_lt_2δ : (c : ℝ) < 2 * δ := by
      exact hc_lt.trans_le (min_le_left _ _)
    have hc_lt_1 : (c : ℝ) < 1 := by
      exact hc_lt.trans_le (min_le_right _ _)
    have hc_pos' : 0 < (c : ℝ) := hc_pos
    let A := Real.log (1 + c)
    let B := Real.log (1 - c)
    let L := (1 / 2 + δ) * A + (1 / 2 - δ) * B
    let γ := Real.exp L
    use c
    have hc_pos_q : (0 : ℚ) < c := by exact_mod_cast hc_pos
    have hc_lt_1_q : (c : ℚ) < 1 := by exact_mod_cast hc_lt_1
    refine ⟨hc_pos_q, hc_lt_1_q, γ, ?_, ?_⟩
    · -- show 1 < γ
      have hA : 1 - (1 + (c : ℝ))⁻¹ ≤ A := by
        apply Real.one_sub_inv_le_log_of_pos
        linarith
      have hB : 1 - (1 - (c : ℝ))⁻¹ ≤ B := by
        apply Real.one_sub_inv_le_log_of_pos
        linarith
      have hL1 : (1 / 2 + δ) * (1 - (1 + (c : ℝ))⁻¹) + (1 / 2 - δ) * (1 - (1 - (c : ℝ))⁻¹) ≤ L := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left hA
          linarith
        · apply mul_le_mul_of_nonneg_left hB
          linarith
      have hL2 : (1 / 2 + δ) * (1 - (1 + (c : ℝ))⁻¹) + (1 / 2 - δ) * (1 - (1 - (c : ℝ))⁻¹) = (c : ℝ)
          * (2 * δ - (c : ℝ)) / ((1 + (c : ℝ)) * (1 - (c : ℝ))) := by
        have hd1 : (1 + (c : ℝ)) ≠ 0 := by linarith
        have hd2 : (1 - (c : ℝ)) ≠ 0 := by linarith
        calc
          (1 / 2 + δ) * (1 - (1 + (c : ℝ))⁻¹) + (1 / 2 - δ) * (1 - (1 - (c : ℝ))⁻¹)
          _ = (1 / 2 + δ) * (1 - 1 / (1 + (c : ℝ))) + (1 / 2 - δ) * (1 - 1 / (1 - (c : ℝ))) := by
            rw [inv_eq_one_div, inv_eq_one_div]
          _ = (1 / 2 + δ) * (c / (1 + c)) + (1 / 2 - δ) * (-c / (1 - c)) := by
            congr 1
            · congr 1
              have h1 : 1 - 1 / (1 + (c : ℝ)) = ((1 + c) - 1) / (1 + c) := by
                rw [sub_div, div_self hd1]
              rw [h1]
              ring_nf
            · congr 1
              have h2 : 1 - 1 / (1 - (c : ℝ)) = ((1 - c) - 1) / (1 - c) := by
                rw [sub_div, div_self hd2]
              rw [h2]
              ring_nf
          _ = (1 / 2 + δ) * (c * (1 - c) / ((1 + c) * (1 - c))) + (1 / 2 - δ) *
              (-c * (1 + c) / ((1 - c) * (1 + c))) := by
            congr 1
            · congr 1
              rw [div_eq_div_iff]
              · ring
              · exact hd1
              · apply mul_ne_zero hd1 hd2
            · congr 1
              rw [div_eq_div_iff]
              · ring
              · exact hd2
              · apply mul_ne_zero hd2 hd1
          _ = ((1 / 2 + δ) * c * (1 - c) + (1 / 2 - δ) * -c * (1 + c)) / ((1 + c) * (1 - c)) := by
            have h_denom : (1 - (c:ℝ)) * (1 + (c:ℝ)) = (1 + (c:ℝ)) * (1 - (c:ℝ)) := by ring
            rw [h_denom]
            ring
          _ = (c : ℝ) * (2 * δ - (c : ℝ)) / ((1 + (c : ℝ)) * (1 - (c : ℝ))) := by
            congr 1
            ring
      have hL3 : 0 < (c : ℝ) * (2 * δ - (c : ℝ)) / ((1 + (c : ℝ)) * (1 - (c : ℝ))) := by
        apply div_pos
        · apply mul_pos hc_pos'
          linarith
        · apply mul_pos
          · linarith
          · linarith
      have hL : 0 < L := by linarith
      exact Real.one_lt_exp_iff.mpr hL
    · -- show the main inequality
      intro a b hab
      have hab_A_B : (a : ℝ) * A + (b : ℝ) * B - (a + b : ℝ) * L = ((a : ℝ) - (1 / 2 + δ) *
          (a + b : ℝ)) * (A - B) := by
        dsimp [L]
        ring
      have hAB_diff : 0 < A - B := by
        dsimp [A, B]
        rw [sub_pos]
        apply Real.log_lt_log
        · linarith
        · linarith
      have hab_diff : 0 ≤ (a : ℝ) - (1 / 2 + δ) * (a + b : ℝ) := by linarith
      have hmul_nonneg : 0 ≤ ((a : ℝ) - (1 / 2 + δ) * (a + b : ℝ)) * (A - B) := by
        apply mul_nonneg hab_diff
        linarith
      rw [← hab_A_B] at hmul_nonneg
      have h_L_le : (a + b : ℝ) * L ≤ (a : ℝ) * A + (b : ℝ) * B := by linarith
      have h_exp_L : γ ^ (a + b) = Real.exp ((a + b : ℝ) * L) := by
        dsimp [γ]
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have h_exp_ab : Real.exp ((a : ℝ) * A + (b : ℝ) * B) = (1 + (c : ℝ)) ^ a * (1 - (c : ℝ)) ^
          b := by
        rw [Real.exp_add]
        dsimp [A, B]
        congr 1
        · have h1 : (a : ℝ) * Real.log (1 + ↑c) = ↑a * Real.log (1 + ↑c) := by ring
          rw [h1]
          rw [Real.exp_nat_mul]
          rw [Real.exp_log]
          linarith
        · have h1 : (b : ℝ) * Real.log (1 - ↑c) = ↑b * Real.log (1 - ↑c) := by ring
          rw [h1]
          rw [Real.exp_nat_mul]
          rw [Real.exp_log]
          linarith
      rw [h_exp_L]
      rw [← h_exp_ab]
      apply Real.exp_le_exp.mpr
      exact h_L_le
  · -- δ >= 1/2
    use 1/2
    refine ⟨by norm_num, by norm_num, 2, by norm_num, ?_⟩
    intro a b hab
    exfalso
    push Not at hδ'
    have h1 : (a + b : ℝ) ≤ (1 / 2 + δ) * (a + b : ℝ) := by
      calc
        (a + b : ℝ) = 1 * (a + b : ℝ) := by ring
        _ ≤ (1 / 2 + δ) * (a + b : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · positivity
    linarith

/-- Step 4 of the proof of `isMisesKLRandom_of_isKLRandom`: assembly. -/
private lemma isMisesKLRandom_of_isKLRandom_assembly
    {ρ : KLRule} (hρ : ρ.IsAdmissible) {w u : CantorSeq}
    (hout : ρ.output w = .infinite u) (c : ℚ) (hc : |c| ≤ 1) (γ : ℝ) (hγ : 1 < γ)
    (hinf : ∃ᶠ k : ℕ in Filter.atTop,
      γ ^ k ≤ (1 + (c : ℝ)) ^ (cantorPrefix u k).count true *
              (1 - (c : ℝ)) ^ (cantorPrefix u k).count false) :
    ∃ β : KLBetting, Partrec β.next ∧ Partrec β.capital ∧ β.Wins w := by
  classical
  obtain ⟨β, hnext, hcap, hval⟩ :=
    isMisesKLRandom_of_isKLRandom_construction hρ c hc
  obtain ⟨h1, h2, h3, h4⟩ :=
    isMisesKLRandom_of_isKLRandom_run_facts hout
  have hn : β.toRule.next = ρ.next := hnext
  have hr : ∀ t, β.toRule.revealed w t = ρ.revealed w t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [KLRule.revealed, KLRule.revealed, ih, hn]
  have hlen : ∀ t, (ρ.revealed w t).length = t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [KLRule.revealed, dite_eq_left (h1 t)]
      simp only [List.length_append, List.length_singleton, ih]
  refine ⟨β, ?_, hcap, ?_⟩
  · rw [hnext]
    exact hρ.1
  change (∀ t, t ≤ (β.toRule.revealed w t).length) ∧
    (∀ t, (β.capital (β.toRule.revealed w t)).Dom) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rw [hr t, hlen t]
  · intro t
    rw [hr t]
    obtain ⟨q, hq, _⟩ := hval (ρ.revealed w t) (h2 t)
    exact Part.dom_iff_mem.mpr ⟨q, hq⟩
  · rintro ⟨B, hB⟩
    have hev : ∀ᶠ k : ℕ in Filter.atTop, B < γ ^ k :=
      (tendsto_pow_atTop_atTop_of_one_lt hγ)
        (Filter.eventually_gt_atTop B)
    obtain ⟨k, hk, hBk⟩ := (hinf.and_eventually hev).exists
    obtain ⟨t, ht⟩ := h4 k
    obtain ⟨j, htj⟩ := h3 t
    have hjk : j = k := by
      simpa only [htj, cantorPrefix_length] using ht
    have houtk : ρ.outputChain w t = cantorPrefix u k := by
      simpa only [hjk] using htj
    obtain ⟨q, hq, hqval⟩ := hval (ρ.revealed w t) (h2 t)
    rw [← KLRule.outputChain, houtk] at hqval
    have hqβ : q ∈ β.capital (β.toRule.revealed w t) := by
      rw [hr t]
      exact hq
    have hqB : (q : ℝ) ≤ B := hB ⟨t, q, hqβ, rfl⟩
    linarith

private lemma isMisesKLRandom_of_isKLRandom_high_count_true_add_count_false (l : List Bool) :
    l.count true + l.count false = l.length := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases hd
    · simp
      omega
    · simp
      omega

/-- Step 5 of the proof of `isMisesKLRandom_of_isKLRandom`: a non-monotone rule outputting
a sequence where ones are too frequent can be used to construct a betting strategy that wins. -/
private lemma isMisesKLRandom_of_isKLRandom_high
    {ρ : KLRule} (hρ : ρ.IsAdmissible) {w u : CantorSeq}
    (hout : ρ.output w = .infinite u) {δ : ℝ} (hδ : 0 < δ)
    (hfreq : ∃ᶠ n : ℕ in Filter.atTop,
      1 / 2 + δ < (Kolmogorov.freqOne u n : ℝ)) :
    ∃ β : KLBetting, Partrec β.next ∧ Partrec β.capital ∧ β.Wins w := by
  obtain ⟨c, hc_pos, hc_lt, γ, hγ, h_ineq⟩ := isMisesKLRandom_of_isKLRandom_analysis hδ
  have hc_le_one : |(c : ℚ)| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  refine isMisesKLRandom_of_isKLRandom_assembly hρ hout c hc_le_one γ hγ ?_
  apply Filter.Frequently.mono hfreq
  intro n hn
  have ha : (cantorPrefix u n).length = n := by simp only [cantorPrefix_length]
  have h_count : (cantorPrefix u n).count true + (cantorPrefix u n).count false =
      (cantorPrefix u n).length :=
      isMisesKLRandom_of_isKLRandom_high_count_true_add_count_false (cantorPrefix u n)
  have hn_pos : 0 < n := by
    by_contra h0
    push Not at h0
    have : n = 0 := by omega
    subst this
    simp [freqOne] at hn
    linarith
  unfold freqOne at hn
  -- hn : 1 / 2 + δ < (cantorPrefix u n).count true / n
  have h_cast : ((↑(List.count true (cantorPrefix u n)) / ↑n : ℚ) : ℝ) =
      (List.count true (cantorPrefix u n) : ℝ) / (n : ℝ) := by push_cast; rfl
  rw [h_cast] at hn
  have hn' : (1 / 2 + δ) * (n : ℝ) < ((cantorPrefix u n).count true : ℝ) := by
    exact (lt_div_iff₀ (Nat.cast_pos.mpr hn_pos)).mp hn
  have hn'' : (1 / 2 + δ) * ((cantorPrefix u n).count true + (cantorPrefix u n).count false : ℝ) <
      ((cantorPrefix u n).count true : ℝ) := by
    have h1 : ((cantorPrefix u n).count true + (cantorPrefix u n).count false : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_add]
      rw [h_count, ha]
    rw [h1]
    exact hn'
  have h_final := h_ineq ((cantorPrefix u n).count true) ((cantorPrefix u n).count false) hn''
  have H : (cantorPrefix u n).count true + (cantorPrefix u n).count false = n := by omega
  rw [H] at h_final
  exact h_final

/-- Step 6 of the proof of `isMisesKLRandom_of_isKLRandom`: a non-monotone rule outputting
a sequence where ones are too rare can be used to construct a betting strategy that wins. -/
private lemma isMisesKLRandom_of_isKLRandom_low
    {ρ : KLRule} (hρ : ρ.IsAdmissible) {w u : CantorSeq}
    (hout : ρ.output w = .infinite u) {δ : ℝ} (hδ : 0 < δ)
    (hfreq : ∃ᶠ n : ℕ in Filter.atTop,
      (Kolmogorov.freqOne u n : ℝ) < 1 / 2 - δ) :
    ∃ β : KLBetting, Partrec β.next ∧ Partrec β.capital ∧ β.Wins w := by
  obtain ⟨c, hc_pos, hc_lt, γ, hγ, hgrowth⟩ :=
    isMisesKLRandom_of_isKLRandom_analysis hδ
  have hc : |(-c : ℚ)| ≤ 1 := by
    rw [abs_neg, abs_of_pos hc_pos]
    exact hc_lt.le
  refine isMisesKLRandom_of_isKLRandom_assembly hρ hout (-c) hc γ hγ ?_
  refine hfreq.mono fun n hn => ?_
  by_cases hn_zero : n = 0
  · subst n
    simp [cantorPrefix]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn_zero)
  have hcount : (cantorPrefix u n).count false + (cantorPrefix u n).count true = n := by
    simpa only [cantorPrefix_length] using List.count_false_add_count_true (cantorPrefix u n)
  have hcount_real : ((cantorPrefix u n).count false : ℝ) +
      ((cantorPrefix u n).count true : ℝ) = (n : ℝ) := by
    exact_mod_cast hcount
  have hfreq_real : ((cantorPrefix u n).count true : ℝ) / (n : ℝ) < 1 / 2 - δ := by
    simpa only [freqOne, Rat.cast_div, Rat.cast_natCast] using hn
  have hones : ((cantorPrefix u n).count true : ℝ) < (1 / 2 - δ) * (n : ℝ) :=
    (div_lt_iff₀ hn_pos).mp hfreq_real
  have hzeros : (1 / 2 + δ) *
      ((cantorPrefix u n).count false + (cantorPrefix u n).count true : ℝ) <
      ((cantorPrefix u n).count false : ℝ) := by
    rw [hcount_real]
    nlinarith
  have hbound := hgrowth ((cantorPrefix u n).count false) ((cantorPrefix u n).count true) hzeros
  rw [hcount] at hbound
  simpa only [Rat.cast_neg, sub_eq_add_neg, neg_neg, mul_comm] using hbound

/-- Step 7 of the proof of `isMisesKLRandom_of_isKLRandom`: if a sequence lacks a limit
frequency of 1/2, it deviates from 1/2 infinitely often by some positive delta in at least one
direction. -/
private lemma isMisesKLRandom_of_isKLRandom_frequency_split
    {u : CantorSeq} (h : ¬ HasLimitFreq (1 / 2) u) :
    (∃ δ : ℝ, 0 < δ ∧ ∃ᶠ n : ℕ in Filter.atTop,
      1 / 2 + δ < (Kolmogorov.freqOne u n : ℝ)) ∨
    (∃ δ : ℝ, 0 < δ ∧ ∃ᶠ n : ℕ in Filter.atTop,
      (Kolmogorov.freqOne u n : ℝ) < 1 / 2 - δ) := by
  unfold HasLimitFreq at h
  rw [Metric.tendsto_atTop] at h
  simp only [not_forall, not_exists] at h
  rcases h with ⟨ε, hε, hfreq⟩
  have hfreq' : ∃ᶠ (n : ℕ) in Filter.atTop, ε ≤ dist (Kolmogorov.freqOne u n : ℝ) (1 / 2) := by
    rw [Filter.frequently_atTop]
    intro a
    rcases hfreq a with ⟨n, hn, hn'⟩
    exact ⟨n, hn, not_lt.mp hn'⟩
  have h_or : ∃ᶠ n : ℕ in Filter.atTop, 1 / 2 + ε / 2 < (Kolmogorov.freqOne u n : ℝ) ∨
      (Kolmogorov.freqOne u n : ℝ) < 1 / 2 - ε / 2 := by
    refine hfreq'.mono (fun n hn => ?_)
    have h_abs : ε ≤ |(Kolmogorov.freqOne u n : ℝ) - 1 / 2| := by
      have hd : dist (Kolmogorov.freqOne u n : ℝ) (1 / 2) = |(Kolmogorov.freqOne u n : ℝ) - 1 /
          2| := Real.dist_eq _ _
      rwa [hd] at hn
    by_cases hneg : (Kolmogorov.freqOne u n : ℝ) - 1 / 2 ≤ 0
    · right
      rw [abs_of_nonpos hneg] at h_abs
      linarith
    · left
      simp only [not_le] at hneg
      have hpos : 0 ≤ (Kolmogorov.freqOne u n : ℝ) - 1 / 2 := le_of_lt hneg
      have habs : |(Kolmogorov.freqOne u n : ℝ) - 1 / 2| = (Kolmogorov.freqOne u n : ℝ) - 1 / 2 :=
          abs_of_pos hneg
      rw [habs] at h_abs
      linarith
  rw [Filter.frequently_or_distrib] at h_or
  cases h_or with
  | inl hleft =>
    left
    use ε / 2
    exact ⟨by linarith, hleft⟩
  | inr hright =>
    right
    use ε / 2
    exact ⟨by linarith, hright⟩

/-- **SUV Figure 3, p. 310.**  Kolmogorov-Loveland random sequences are
Mises-Kolmogorov-Loveland random. -/
theorem isMisesKLRandom_of_isKLRandom {w : CantorSeq} (hw : IsKLRandom w) : IsMisesKLRandom w := by
  intro ρ hρ
  unfold FiniteOrFreq
  cases hout : ρ.output w with
  | finite l => exact trivial
  | infinite u =>
    by_contra h_not_limit
    rcases isMisesKLRandom_of_isKLRandom_frequency_split h_not_limit with ⟨δ, hδ, hfreq⟩ |
        ⟨δ, hδ, hfreq⟩
    · obtain ⟨β, hβnext, hβcap, hβwins⟩ := isMisesKLRandom_of_isKLRandom_high hρ hout hδ hfreq
      exact hw β hβnext hβcap hβwins
    · obtain ⟨β, hβnext, hβcap, hβwins⟩ := isMisesKLRandom_of_isKLRandom_low hρ hout hδ hfreq
      exact hw β hβnext hβcap hβwins

private lemma exists_isBalanced_not_isKurtzRandom_selectedBits_univ_cantorPrefix (w : CantorSeq)
    (t : ℕ) :
    selectedBits Set.univ (cantorPrefix w t) = cantorPrefix w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [cantorPrefix_succ, selectedBits_append_singleton, ih]
    have h : cantorPrefix w t ∈ (Set.univ : Set BitString) := Set.mem_univ _
    simp [h]

private theorem exists_isBalanced_not_isKurtzRandom_isBalanced_of_isMisesKLRandom {w : CantorSeq}
    (hw : IsMisesKLRandom w) : IsBalanced w := by
  have hmcr := hw.isMisesChurchRandomAt
  have hdec : IsDecidableSet (Set.univ : Set BitString) := 
    ⟨fun _ => true, Computable.const true, by simp⟩
  have hsel := hmcr Set.univ hdec
  have h1 : selectStream Set.univ w = .infinite w := by
    apply BitStream.eq_of_forall_finite_le_iff
    intro t
    have h_stream : selectStream Set.univ w = streamOfChain (selectChain Set.univ w)
        (selectChain_prefix _ _) := rfl
    rw [h_stream]
    have hd : streamOfChain (selectChain Set.univ w) (selectChain_prefix _ _) = 
      BitStream.ofPrefixSet (chainPrefixSet (selectChain Set.univ w))
          (isStreamPrefixSet_chainPrefixSet (selectChain_prefix Set.univ w)) := rfl
    rw [hd, BitStream.finite_le_ofPrefixSet_iff]
    change _ ↔ IsCantorPrefix t w
    simp only [chainPrefixSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      have hn' : t <+: selectChain Set.univ w n := hn
      rw [selectChain, exists_isBalanced_not_isKurtzRandom_selectedBits_univ_cantorPrefix] at hn'
      exact isCantorPrefix_of_prefix hn' ((isCantorPrefix_iff_cantorPrefix_eq _ _).mpr
          (by rw [cantorPrefix_length]))
    · intro h
      have h' := (isCantorPrefix_iff_cantorPrefix_eq _ _).mp h
      exact ⟨t.length, by rw [selectChain,
                            exists_isBalanced_not_isKurtzRandom_selectedBits_univ_cantorPrefix, h']⟩
  rw [h1] at hsel
  exact hsel

/-- A balanced sequence need not be Kurtz random, since Mises-Kolmogorov-Loveland random sequences
are balanced and Problem 280 applies: no arrow goes from the right column to the left one. -/
theorem exists_isBalanced_not_isKurtzRandom :
    ∃ w, IsBalanced w ∧ ¬ IsKurtzRandom uniformMeasure w := by
  obtain ⟨w, hw, hnk⟩ := exists_isMisesKLRandom_not_isKurtzRandom
  exact ⟨w, exists_isBalanced_not_isKurtzRandom_isBalanced_of_isMisesKLRandom hw, hnk⟩

/-- **SUV p. 310.**  Computable randomness does not imply Mises-Church-Daley randomness: by
Theorem 182(b) a computably random sequence can have prefixes of logarithmic complexity, which is
impossible for a Mises-Church-Daley random sequence by Theorem 188. -/
theorem exists_isComputablyRandom_not_isMisesChurchDaleyRandom :
    ∃ w, IsComputablyRandom uniformMeasure w ∧ ¬ IsMisesChurchDaleyRandom w := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  have hpos : ∀ x, 0 < cantorMass uniformMeasure x := by
    intro x
    rw [cantorMass_uniformMeasure]
    exact ENNReal.pow_pos (by norm_num) _
  obtain ⟨w, hw1, hw2⟩ := exists_isComputablyRandom_plainK_log isComputableMeasure_uniform hpos V hV
  use w
  exact ⟨hw1, fun hmcd => not_exists_isMisesChurchDaleyRandom_plainK_log V hV ⟨w, hmcd, hw2⟩⟩

/-- Step 1 of the proof of `exists_isPartialComputablyRandom_not_isMisesKLRandom`: The
growth condition of sublinear complexity. -/
private lemma exists_isPartialComputablyRandom_not_isMisesKLRandom_limit (c : ℝ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, (Nat.size n : ℝ) * Real.logb 2 (n : ℝ) + c < 1/2 * (n : ℝ) := by
  have a : Asymptotics.IsLittleO Filter.atTop (fun x : ℝ => (Real.log x)^2) (fun x => x) :=
    Real.isLittleO_pow_log_id_atTop (n := 2)
  have b : Asymptotics.IsLittleO Filter.atTop (fun x : ℝ => Real.log x) (fun x => x) :=
    Real.isLittleO_log_id_atTop
  have hc : Asymptotics.IsLittleO Filter.atTop (fun _ : ℝ => c) (fun x => x) :=
    Asymptotics.isLittleO_const_id_atTop c
  have h1 : Asymptotics.IsLittleO Filter.atTop
      (fun x : ℝ => (Real.logb 2 x)^2 + Real.logb 2 x + c) (fun x => x) := by
    have a' := a.const_mul_left (1 / Real.log 2 ^ 2)
    have b' := b.const_mul_left (1 / Real.log 2)
    refine ((a'.add b').add hc).congr_left ?_
    intro x
    simp only [Real.logb]
    field_simp
  have h2 := h1.def (c := 1/4) (by norm_num)
  have h3 : ∀ᶠ n : ℕ in Filter.atTop,
      ‖(Real.logb 2 (n:ℝ))^2 + Real.logb 2 (n:ℝ) + c‖ ≤ 1/4 * ‖(n:ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually h2
  filter_upwards [h3, Filter.eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hL : 0 ≤ Real.logb 2 (n:ℝ) := Real.logb_nonneg (by norm_num) hn1'
  have hs : (Nat.size n : ℝ) ≤ Real.logb 2 (n:ℝ) + 1 := by
    have hpos : 0 < Nat.size n := Nat.size_pos.mpr (by omega)
    have h : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
    have h' : (2:ℝ) ^ ((Nat.size n - 1 : ℕ) : ℝ) ≤ n := by
      rw [Real.rpow_natCast]; exact_mod_cast h
    have := (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).mpr h'
    have e : ((Nat.size n - 1 : ℕ) : ℝ) = (Nat.size n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    linarith
  rw [Real.norm_of_nonneg (Nat.cast_nonneg n)] at hn
  have := le_trans (le_abs_self _) (Real.norm_eq_abs _ ▸ hn)
  nlinarith [mul_le_mul_of_nonneg_right hs hL]

/-- **SUV p. 310.**  Partial-computable randomness does not imply Mises-Kolmogorov-Loveland
randomness: by Theorem 190(b) its prefixes can have sublinear complexity, which is impossible for a
Mises-Kolmogorov-Loveland random sequence by Theorem 193. -/
theorem exists_isPartialComputablyRandom_not_isMisesKLRandom :
    ∃ w, IsPartialComputablyRandom w ∧ ¬ IsMisesKLRandom w := by
  have ⟨V, hV⟩ := Kolmogorov.exists_isOptimalConditional
  let f : ℕ → ℕ := fun n => Nat.size n
  have hf : Computable f := Kolmogorov.computable_nat_size
  have hmono : Monotone f := fun _ _ h => Nat.size_le_size h
  have hunb : ∀ B, ∃ n, B ≤ f n := fun B => ⟨2^B, by
    have : Nat.size (2^B) = B + 1 := Nat.size_pow
    linarith⟩
  rcases exists_isPartialComputablyRandom_plainK_le hf hmono hunb V hV with ⟨w, hw, c, hc⟩
  use w, hw
  apply not_isMisesKLRandom_of_plainK_lt V hV (α := 1/2) (by norm_num)
  have := exists_isPartialComputablyRandom_not_isMisesKLRandom_limit c
  have H : ∀ᶠ (n : ℕ) in Filter.atTop, ((plainK V (cantorPrefix w n)).toNat : ℝ) < 1/2 * (n : ℝ) :=
      by
    apply Filter.Eventually.mono this
    intro n hn
    calc ((plainK V (cantorPrefix w n)).toNat : ℝ)
      _ ≤ (f n : ℝ) * Real.logb 2 (n : ℝ) + c := hc n
      _ < 1/2 * (n : ℝ) := hn
  exact H




end FrequencyGames

end Kolmogorov
