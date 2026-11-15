/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.PartialRules
import KolmogorovMathlib.Complexity.Applications.LipschitzBesicovitch
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.Oracle.PrefixComplexity.MonotonicityThreshold
import Mathlib.Data.Bool.Count
import KolmogorovMathlib.MonotoneComplexity.GacsDayPartrecFold

/-!
# Kolmogorov–Loveland selection rules

A Kolmogorov–Loveland (non-monotone) selection rule chooses, from the bits revealed so far, which
position to reveal next and whether to select it.  We define such rules and the sequence they
output on an infinite binary word, together with the notions of admissible (computable) and total
rules, and of Mises–Kolmogorov–Loveland randomness of a given frequency `p`.

The main declarations are `KLRule`, `KLRule.output`, `IsMisesKLRandomAt`, and the theorem
`isMisesKLRandomAt_iff_total`, which shows that restricting to total computable rules does not
change the notion of randomness.  Monotone rules embed into KL rules (`KLRule.ofMonotone`).
This formalizes the part of the book by Shen, Uspensky and Vereshchagin on non-monotone
selection rules (p. 291).
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology

/-- **SUV p. 291.**  A non-monotonic selection rule: `next` is the book's `F`, `sel` is its `G`. -/
structure KLRule where
  /-- Which bit to reveal, given the bits revealed so far. -/
  next : BitString →. ℕ
  /-- Whether the bit about to be revealed is selected, given the bits revealed before it. -/
  sel : BitString →. Bool
  /-- `F` differs on compatible strings, so the same bit is never revealed twice. -/
  noRepeat : ∀ x y, x <+: y → x ≠ y → ∀ a ∈ next x, ∀ b ∈ next y, a ≠ b

open Classical in
/-- The bits of `ω` revealed in `t` steps, `ω_{n_0} ω_{n_1} …`, where `n_i` is `F` applied to the
bits already revealed.  The run stops when the next value of `F` is undefined. -/
noncomputable def KLRule.revealed (ρ : KLRule) (w : CantorSeq) : ℕ → BitString
  | 0 => []
  | t + 1 =>
    let x := ρ.revealed w t
    if h : (ρ.next x).Dom then x ++ [w ((ρ.next x).get h)] else x

/-- The revealed bits form a chain. -/
lemma KLRule.revealed_prefix (ρ : KLRule) (w : CantorSeq) (t : ℕ) :
    ρ.revealed w t <+: ρ.revealed w (t + 1) := by
  rw [KLRule.revealed]
  split_ifs
  · exact List.prefix_append _ _
  · exact List.prefix_rfl

/-- The sequence `ω_F` of all revealed bits, selected or not (proof of Theorem 202, p. 305). -/
noncomputable def KLRule.revealedStream (ρ : KLRule) (w : CantorSeq) : BitStream :=
  streamOfChain (ρ.revealed w) (ρ.revealed_prefix w)

/-- The bits selected in `t` steps: `ω_{n_i}` for which `G` is defined on all prefixes of
`ω_{n_0} … ω_{n_{i-1}}` and equal to `1` on this string.  SUV p. 291. -/
noncomputable def KLRule.outputChain (ρ : KLRule) (w : CantorSeq) (t : ℕ) : BitString :=
  selectedBits (partialRuleSet ρ.sel) (ρ.revealed w t)

/-- The selected bits form a chain. -/
lemma KLRule.outputChain_prefix (ρ : KLRule) (w : CantorSeq) (t : ℕ) :
    ρ.outputChain w t <+: ρ.outputChain w (t + 1) :=
  selectedBits_prefix _ (ρ.revealed_prefix w t)

/-- **SUV p. 291.**  The output `S_{F,G}(ω)` of a non-monotonic rule. -/
noncomputable def KLRule.output (ρ : KLRule) (w : CantorSeq) : BitStream :=
  streamOfChain (ρ.outputChain w) (ρ.outputChain_prefix w)

/-- **SUV p. 291.**  A *Kolmogorov-Loveland admissible* rule: `F` and `G` are partial computable. -/
def KLRule.IsAdmissible (ρ : KLRule) : Prop := Partrec ρ.next ∧ Partrec ρ.sel

/-- A rule with `F` and `G` total. -/
def KLRule.IsTotal (ρ : KLRule) : Prop := (∀ x, (ρ.next x).Dom) ∧ ∀ x, (ρ.sel x).Dom

/-- **SUV p. 291**, with the frequency as a parameter: every Kolmogorov-Loveland admissible rule
selects a finite sequence or one with limit frequency `p`.  The notion of p. 292 for `B_p`. -/
def IsMisesKLRandomAt (p : ℝ) (w : CantorSeq) : Prop :=
  ∀ ρ : KLRule, ρ.IsAdmissible → FiniteOrFreq p (ρ.output w)

/-- **SUV p. 291.**  *Mises-Kolmogorov-Loveland random* sequences (Kolmogorov-Loveland
stochastic). -/
abbrev IsMisesKLRandom (w : CantorSeq) : Prop := IsMisesKLRandomAt (1 / 2) w

/-! ### Monotone rules as a special case -/

/-- A monotone partial rule `r` as a non-monotonic rule: reveal the bits in order. -/
def KLRule.ofMonotone (r : BitString →. Bool) : KLRule where
  next x := Part.some x.length
  sel := r
  noRepeat := by
    intro x y hxy hne a ha b hb hab
    rw [Part.mem_some_iff] at ha hb
    subst ha hb
    exact hne (hxy.eq_of_length hab)

/-- Under a monotone rule the revealed bits are the prefixes of `ω`. -/
lemma KLRule.revealed_ofMonotone (r : BitString →. Bool) (w : CantorSeq) (t : ℕ) :
    (KLRule.ofMonotone r).revealed w t = cantorPrefix w t := by
  induction t with
  | zero => simp [KLRule.revealed, cantorPrefix]
  | succ t ih =>
    have hstep : (KLRule.ofMonotone r).revealed w (t + 1) =
        (KLRule.ofMonotone r).revealed w t ++ [w ((KLRule.ofMonotone r).revealed w t).length] := by
      rw [KLRule.revealed]
      exact dite_eq_left trivial
    rw [hstep, ih, cantorPrefix_length, cantorPrefix_succ]

/-- The output of the rule `KLRule.ofMonotone r` is `S_r`. -/
theorem KLRule.output_ofMonotone (r : BitString →. Bool) (w : CantorSeq) :
    (KLRule.ofMonotone r).output w = selectStream (partialRuleSet r) w := by
  have hchain : (KLRule.ofMonotone r).outputChain w = selectChain (partialRuleSet r) w := by
    funext t
    change selectedBits (partialRuleSet r) ((KLRule.ofMonotone r).revealed w t) = _
    rw [KLRule.revealed_ofMonotone]
    rfl
  simp only [KLRule.output, selectStream, hchain]

/-- **SUV Theorem 192(a), p. 292.**  For every `p`, a Mises-Kolmogorov-Loveland random sequence is
Mises-Church-Daley random. -/
theorem IsMisesKLRandomAt.isMisesChurchDaleyRandomAt {p : ℝ} {w : CantorSeq}
    (hw : IsMisesKLRandomAt p w) : IsMisesChurchDaleyRandomAt p w := by
  intro r hr
  rw [← KLRule.output_ofMonotone]
  exact hw _ ⟨Primrec.list_length.to_comp.partrec, hr⟩

/-- **SUV Theorem 192(a), p. 292**, the parenthetical: and therefore Mises-Church random. -/
theorem IsMisesKLRandomAt.isMisesChurchRandomAt {p : ℝ} {w : CantorSeq}
    (hw : IsMisesKLRandomAt p w) : IsMisesChurchRandomAt p w :=
  hw.isMisesChurchDaleyRandomAt.isMisesChurchRandomAt

/-! ### Total rules -/


/-- The stream of a chain that is finite or has limit frequency `p`: either the lengths of the
chain are bounded, or they tend to infinity and the frequencies of ones in the chain tend to `p`. -/
private lemma isMisesKLRandomAt_iff_total_analysis_chain (p : ℝ) (c : ℕ → BitString)
    (hc : ∀ t, c t <+: c (t + 1)) (h : FiniteOrFreq p (streamOfChain c hc)) :
    (∃ M, ∀ t, (c t).length ≤ M) ∨
      (Tendsto (fun t => (c t).length) atTop atTop ∧
        Tendsto (fun t => ((c t).count true : ℝ) / ((c t).length : ℝ)) atTop (𝓝 p)) := by
  have hmem (x : BitString) :
      BitStream.finite x ≤ streamOfChain c hc ↔ x ∈ chainPrefixSet c :=
    BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet hc) x
  rcases hs : streamOfChain c hc with x | v
  · left
    refine ⟨x.length, fun t => ?_⟩
    have h1 : BitStream.finite (c t) ≤ BitStream.finite x := by
      rw [← hs]
      exact (hmem _).mpr ⟨t, List.prefix_rfl⟩
    exact List.IsPrefix.length_le h1
  · right
    rw [hs] at h
    have hpre (t : ℕ) : cantorPrefix v (c t).length = c t := by
      have h1 : BitStream.finite (c t) ≤ BitStream.infinite v := by
        rw [← hs]
        exact (hmem _).mpr ⟨t, List.prefix_rfl⟩
      exact (isCantorPrefix_iff_cantorPrefix_eq _ _).mp h1
    have hlen : Tendsto (fun t => (c t).length) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro k
      have h1 : BitStream.finite (cantorPrefix v k) ≤ BitStream.infinite v := by
        change IsCantorPrefix (cantorPrefix v k) v
        rw [isCantorPrefix_iff_cantorPrefix_eq, cantorPrefix_length]
      rw [← hs, hmem] at h1
      obtain ⟨t, ht⟩ := h1
      refine ⟨t, fun s hst => ?_⟩
      have h2 := (chain_prefix_of_le hc hst).length_le
      have h3 := ht.length_le
      rw [cantorPrefix_length] at h3
      omega
    refine ⟨hlen, ?_⟩
    have hv : HasLimitFreq p v := h
    refine (hv.comp hlen).congr (fun t => ?_)
    simp only [Function.comp, freqOne, hpre t]
    push_cast
    rfl

/-- Each bit of `u` is selected by exactly one of `R` and its complement: the lengths and the
numbers of ones of the two selected chains add up. -/
private lemma isMisesKLRandomAt_iff_total_analysis_count (R : Set BitString)
    (u : CantorSeq) (t : ℕ) :
    (selectChain R u t).length + (selectChain Rᶜ u t).length = t ∧
      (selectChain R u t).count true + (selectChain Rᶜ u t).count true =
        (cantorPrefix u t).count true := by
  induction t with
  | zero => simp [selectChain, selectedBits, selectedAux, cantorPrefix]
  | succ t ih =>
    simp only [selectChain, cantorPrefix_succ, selectedBits_append_singleton] at ih ⊢
    by_cases h : cantorPrefix u t ∈ R
    · have h' : cantorPrefix u t ∉ Rᶜ := fun h2 => h2 h
      simp only [h, h', ↓reduceIte, List.length_append, List.count_append, List.length_cons,
        List.length_nil, List.append_nil]
      omega
    · have h' : cantorPrefix u t ∈ Rᶜ := h
      simp only [h, h', ↓reduceIte, List.length_append, List.count_append, List.length_cons,
        List.length_nil, List.append_nil]
      omega

/-- The real-analysis step: if `a n ≤ e n ≤ n` and either `e` is bounded or `e → ∞` with
`a / e → p`, then `(a n - p e n) / n → 0`. -/
private lemma isMisesKLRandomAt_iff_total_analysis_real (p : ℝ) (a e : ℕ → ℕ)
    (ha : ∀ n, a n ≤ e n) (he : ∀ n, e n ≤ n)
    (h : (∃ M, ∀ n, e n ≤ M) ∨
      (Tendsto e atTop atTop ∧ Tendsto (fun n => (a n : ℝ) / (e n : ℝ)) atTop (𝓝 p))) :
    Tendsto (fun n => ((a n : ℝ) - p * e n) / n) atTop (𝓝 0) := by
  rcases h with ⟨M, hM⟩ | ⟨he_top, hfreq⟩
  · apply squeeze_zero_norm (a := fun n : ℕ => ((M : ℝ) + |p| * M) / n)
    · intro n
      rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      have h1 : (a n : ℝ) ≤ M := by exact_mod_cast (ha n).trans (hM n)
      have h2 : (e n : ℝ) ≤ M := by exact_mod_cast hM n
      have h3 : (0 : ℝ) ≤ a n := Nat.cast_nonneg _
      have h4 : (0 : ℝ) ≤ e n := Nat.cast_nonneg _
      calc |(a n : ℝ) - p * e n| ≤ |(a n : ℝ)| + |p * e n| := abs_sub _ _
        _ = a n + |p| * e n := by rw [abs_of_nonneg h3, abs_mul, abs_of_nonneg h4]
        _ ≤ M + |p| * M := by gcongr
    · exact tendsto_const_div_atTop_nhds_zero_nat _
  · have hev : ∀ᶠ n in atTop, ‖((a n : ℝ) - p * e n) / n‖ ≤ |(a n : ℝ) / e n - p| := by
      filter_upwards [he_top.eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ e n := by exact_mod_cast hn
      have hen : (e n : ℝ) ≤ n := by exact_mod_cast he n
      have hnpos : (0 : ℝ) < n := by linarith
      have hepos : (0 : ℝ) < e n := by linarith
      rw [Real.norm_eq_abs]
      have heq : ((a n : ℝ) - p * e n) / n = ((a n : ℝ) / e n - p) * (e n / n) := by
        field_simp
      rw [heq, abs_mul]
      have h1 : |(e n : ℝ) / n| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        exact (div_le_one hnpos).mpr hen
      calc |(a n : ℝ) / e n - p| * |(e n : ℝ) / n| ≤ |(a n : ℝ) / e n - p| * 1 := by gcongr
        _ = _ := mul_one _
    apply squeeze_zero_norm' hev
    have h2 := (hfreq.sub_const p).abs
    rw [sub_self, abs_zero] at h2
    exact h2

/-- The analysis step for an arbitrary set of strings `R` and its complement: if both selected
streams are finite or have limit frequency `p`, then `u` has limit frequency `p`. -/
private lemma isMisesKLRandomAt_iff_total_analysis_compl (p : ℝ) (R : Set BitString)
    (u : CantorSeq) (h1 : FiniteOrFreq p (selectStream R u))
    (h2 : FiniteOrFreq p (selectStream Rᶜ u)) : HasLimitFreq p u := by
  have d1 := isMisesKLRandomAt_iff_total_analysis_chain p _ (selectChain_prefix R u) h1
  have d2 := isMisesKLRandomAt_iff_total_analysis_chain p _ (selectChain_prefix Rᶜ u) h2
  have hcount := isMisesKLRandomAt_iff_total_analysis_count R u
  have t1 := isMisesKLRandomAt_iff_total_analysis_real p
    (fun n => (selectChain R u n).count true) (fun n => (selectChain R u n).length)
    (fun n => List.count_le_length) (fun n => by have := (hcount n).1; omega) d1
  have t2 := isMisesKLRandomAt_iff_total_analysis_real p
    (fun n => (selectChain Rᶜ u n).count true) (fun n => (selectChain Rᶜ u n).length)
    (fun n => List.count_le_length) (fun n => by have := (hcount n).1; omega) d2
  have hsum := (t1.add t2).const_add p
  rw [add_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  obtain ⟨hl, hc⟩ := hcount n
  have hc' : ((cantorPrefix u n).count true : ℝ) =
      ((selectChain R u n).count true : ℝ) + ((selectChain Rᶜ u n).count true : ℝ) := by
    exact_mod_cast hc.symm
  have hl' : (n : ℝ) =
      ((selectChain R u n).length : ℝ) + ((selectChain Rᶜ u n).length : ℝ) := by
    exact_mod_cast hl.symm
  have hp : p =
      p * (((selectChain R u n).length : ℝ) + ((selectChain Rᶜ u n).length : ℝ)) / n := by
    rw [← hl', mul_div_assoc, div_self hn', mul_one]
  simp only [freqOne]
  push_cast
  rw [hc']
  linear_combination hp

/-- Step 1 of the proof of `isMisesKLRandomAt_iff_total`: the analysis step combining
finite or limit frequencies. -/
private lemma isMisesKLRandomAt_iff_total_analysis (p : ℝ) (E : Set ℕ) (u : CantorSeq) :
    FiniteOrFreq p (selectStream {x | x.length ∈ E} u) →
    FiniteOrFreq p (selectStream {x | x.length ∉ E} u) →
    HasLimitFreq p u :=
  fun h1 h2 => isMisesKLRandomAt_iff_total_analysis_compl p {x | x.length ∈ E} u h1 h2

/-- A helper rule that only queries the sequence at positions of a specific parity and simulates
returning `false` for others. -/
private def isMisesKLRandomAt_iff_total_onParity (ρ : KLRule) (b : Bool) : KLRule where
  next := ρ.next
  sel x := (ρ.next x).bind (fun n => if (n % 2 == 1) = b then ρ.sel x else Part.some false)
  noRepeat := ρ.noRepeat

/-- Step 2 of the proof of `isMisesKLRandomAt_iff_total`: admissibility of the parity
rule. -/
private lemma isMisesKLRandomAt_iff_total_onParity_admissible (ρ : KLRule) (b : Bool)
    (hρ : ρ.IsAdmissible) : (isMisesKLRandomAt_iff_total_onParity ρ b).IsAdmissible := by
  constructor
  · exact hρ.1
  · have h_bind : Partrec (fun x => (ρ.next x).bind
                                      (fun n => if (n % 2 == 1) = b then ρ.sel x else
                                                  Part.some false)) := by
      have htest : Computable (fun (xn : BitString × ℕ) => ((xn.2 % 2 == 1) : Bool) == b) := by
        have hmod := Primrec.nat_mod.comp Primrec.snd (Primrec.const (α := BitString × ℕ) 2)
        have hbeq := Primrec.beq.comp hmod (Primrec.const (α := BitString × ℕ) 1)
        cases b
        · exact (Primrec.not.comp hbeq).to_comp.of_eq (by
            intro q
            generalize h : (q.2 % 2 == 1) = c
            cases c <;> rfl
          )
        · exact hbeq.to_comp.of_eq (by
            intro q
            generalize h : (q.2 % 2 == 1) = c
            cases c <;> rfl
          )
      have hcond := Partrec.cond htest (hρ.2.comp Computable.fst) (Computable.const false).partrec
      exact Partrec.bind hρ.1 (hcond.of_eq (by
        intro q
        by_cases h : (((q.snd % 2 == 1) : Bool) == b)
        · have heq : (q.2 % 2 == 1) = b := eq_of_beq h
          simp [heq]
        · have heq : ¬((q.2 % 2 == 1) = b) := ne_of_beq_false (Bool.eq_false_of_ne_true h)
          simp [heq]
      ))
    exact h_bind

/-- Step 3 of the proof of `isMisesKLRandomAt_iff_total`: the selection property of the
parity rule. -/
private lemma isMisesKLRandomAt_iff_total_onParity_sel (ρ : KLRule) (b : Bool) (x : BitString)
    (n : ℕ)
    (hn : n ∈ (isMisesKLRandomAt_iff_total_onParity ρ b).next x) (hneq : (n % 2 == 1) ≠ b) :
    (isMisesKLRandomAt_iff_total_onParity ρ b).sel x = Part.some false := by
  have hn' : n ∈ ρ.next x := hn
  have hdef : (isMisesKLRandomAt_iff_total_onParity ρ b).sel x = (ρ.next x).bind
      (fun m => if (m % 2 == 1) = b then ρ.sel x else Part.some false) := rfl
  rw [hdef]
  rw [Part.bind_of_mem hn']
  rw [ite_eq_right hneq]

/-- Revealing bits depends only on the querying function. -/
private lemma isMisesKLRandomAt_iff_total_onParity_output_revealed
    (ρ ρ' : KLRule) (hnext : ρ'.next = ρ.next) (w : CantorSeq) (t : ℕ) :
    ρ'.revealed w t = ρ.revealed w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [KLRule.revealed, KLRule.revealed, ih, hnext]

/-- An infinite chain output determines all its finite prefixes and has unbounded lengths. -/
private lemma isMisesKLRandomAt_iff_total_onParity_output_chain_facts
    (ρ : KLRule) (w u : CantorSeq) (hout : ρ.output w = .infinite u) :
    (∀ t, ρ.outputChain w t = cantorPrefix u (ρ.outputChain w t).length) ∧
    (∀ k, ∃ t, k ≤ (ρ.outputChain w t).length) := by
  have hmem (x : BitString) :
      BitStream.finite x ≤ BitStream.infinite u ↔ x ∈ chainPrefixSet (ρ.outputChain w) := by
    rw [← hout]
    exact BitStream.finite_le_ofPrefixSet_iff
      (isStreamPrefixSet_chainPrefixSet (ρ.outputChain_prefix w)) x
  constructor
  · intro t
    have hp := (hmem _).mpr ⟨t, List.prefix_rfl⟩
    exact ((isCantorPrefix_iff_cantorPrefix_eq _ _).mp hp).symm
  · intro k
    have hp : BitStream.finite (cantorPrefix u k) ≤ BitStream.infinite u := by
      apply BitStream.finite_le_infinite_iff.mpr
      rw [isCantorPrefix_iff_cantorPrefix_eq, cantorPrefix_length]
    obtain ⟨t, ht⟩ := (hmem _).mp hp
    exact ⟨t, by simpa only [cantorPrefix_length] using ht.length_le⟩

/-- Infinite output prevents either partial function from hanging on the revealed run. -/
private lemma isMisesKLRandomAt_iff_total_onParity_output_run
    (ρ : KLRule) (w u : CantorSeq) (hout : ρ.output w = .infinite u) :
    (∀ t, (ρ.next (ρ.revealed w t)).Dom) ∧
    (∀ t y, y <+: ρ.revealed w t → (ρ.next y).Dom ∧ (ρ.sel y).Dom) := by
  classical
  obtain ⟨_, hlong⟩ :=
    isMisesKLRandomAt_iff_total_onParity_output_chain_facts ρ w u hout
  have hgrowth (t : ℕ) : ∃ s ≥ t, (ρ.outputChain w t).length < (ρ.outputChain w s).length := by
    obtain ⟨s, hs⟩ := hlong ((ρ.outputChain w t).length + 1)
    refine ⟨max t s, le_max_left _ _, ?_⟩
    have := (chain_prefix_of_le (ρ.outputChain_prefix w) (le_max_right t s)).length_le
    omega
  have hnext : ∀ t, (ρ.next (ρ.revealed w t)).Dom := by
    intro t
    by_contra hd
    have hstop : ∀ k, ρ.revealed w (t + k) = ρ.revealed w t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show t + (k + 1) = t + k + 1 by omega, KLRule.revealed, ih,
          dite_eq_right hd]
    obtain ⟨s, hts, hs⟩ := hgrowth t
    have heq : ρ.outputChain w s = ρ.outputChain w t := by
      change selectedBits _ (ρ.revealed w s) = selectedBits _ (ρ.revealed w t)
      have := hstop (s - t)
      rw [Nat.add_sub_of_le hts] at this
      rw [this]
    rw [heq] at hs
    exact (lt_irrefl _ hs)
  have hsucc (t : ℕ) : ρ.revealed w (t + 1) =
      ρ.revealed w t ++ [w ((ρ.next (ρ.revealed w t)).get (hnext t))] := by
    rw [KLRule.revealed, dite_eq_left (hnext t)]
  have hlen (t : ℕ) : (ρ.revealed w t).length = t := by
    induction t with
    | zero => rfl
    | succ t ih => simp only [hsucc, List.length_append, List.length_singleton, ih]
  have hevent (t : ℕ) : ∃ s ≥ t, ρ.revealed w s ∈ partialRuleSet ρ.sel := by
    by_contra h
    push Not at h
    have hstop : ∀ k, ρ.outputChain w (t + k) = ρ.outputChain w t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        change selectedBits _ (ρ.revealed w (t + (k + 1))) = _
        rw [Nat.add_succ, hsucc, selectedBits_append_singleton,
          ite_eq_right (h _ (by omega)), List.append_nil]
        exact ih
    obtain ⟨s, hts, hs⟩ := hgrowth t
    have heq := hstop (s - t)
    rw [Nat.add_sub_of_le hts] at heq
    rw [heq] at hs
    exact (lt_irrefl _ hs)
  refine ⟨hnext, ?_⟩
  intro t y hy
  have hi : y.length ≤ t := by simpa only [hlen] using hy.length_le
  have hpre := chain_prefix_of_le (ρ.revealed_prefix w) hi
  have heq : y = ρ.revealed w y.length := by
    rcases List.prefix_or_prefix_of_prefix hy hpre with h | h
    · exact h.eq_of_length (hlen _).symm
    · exact (h.eq_of_length (hlen _)).symm
  refine ⟨by rw [heq]; exact hnext _, ?_⟩
  obtain ⟨s, hts, hs⟩ := hevent t
  exact hs.1 y (hy.trans (chain_prefix_of_le (ρ.revealed_prefix w) hts))

open Classical in
/-- Counting selected reveal times gives the length of the output chain. -/
private lemma isMisesKLRandomAt_iff_total_onParity_output_length
    (ρ : KLRule) (w : CantorSeq)
    (hnext : ∀ t, (ρ.next (ρ.revealed w t)).Dom) (t : ℕ) :
    (ρ.outputChain w t).length =
      Nat.count (fun j => ρ.revealed w j ∈ partialRuleSet ρ.sel) t := by
  classical
  induction t with
  | zero => simp [KLRule.outputChain, KLRule.revealed, selectedBits, selectedAux]
  | succ t ih =>
    have hr : ρ.revealed w (t + 1) =
        ρ.revealed w t ++ [w ((ρ.next (ρ.revealed w t)).get (hnext t))] := by
      rw [KLRule.revealed, dite_eq_left (hnext t)]
    change (selectedBits _ (ρ.revealed w (t + 1))).length = _
    rw [hr, selectedBits_append_singleton, List.length_append, Nat.count_succ]
    change (ρ.outputChain w t).length + _ = _
    rw [ih]
    split_ifs <;> rfl

/-- Where both functions are defined on every prefix, parity filtering just conjoins parity. -/
private lemma isMisesKLRandomAt_iff_total_onParity_output_parity_mem
    (ρ : KLRule) (b : Bool) (x : BitString)
    (hnext : ∀ y, y <+: x → (ρ.next y).Dom)
    (hsel : ∀ y, y <+: x → (ρ.sel y).Dom) :
    x ∈ partialRuleSet (isMisesKLRandomAt_iff_total_onParity ρ b).sel ↔
      x ∈ partialRuleSet ρ.sel ∧
        ((ρ.next x).get (hnext x List.prefix_rfl) % 2 == 1) = b := by
  classical
  have heval (y : BitString) (hy : y <+: x) :
      (isMisesKLRandomAt_iff_total_onParity ρ b).sel y =
        if ((ρ.next y).get (hnext y hy) % 2 == 1) = b then ρ.sel y else Part.some false := by
    change (ρ.next y).bind (fun n => if (n % 2 == 1) = b then ρ.sel y else Part.some false) = _
    rw [Part.bind_of_mem (Part.get_mem (hnext y hy))]
  have hdom (y : BitString) (hy : y <+: x) :
      ((isMisesKLRandomAt_iff_total_onParity ρ b).sel y).Dom := by
    rw [heval y hy]
    split_ifs
    · exact hsel y hy
    · trivial
  change ((∀ y, y <+: x → _) ∧ true ∈ _) ↔ _
  rw [and_iff_right (hdom), heval x List.prefix_rfl]
  change (true ∈ (if _ then ρ.sel x else Part.some false)) ↔
    ((∀ y, y <+: x → (ρ.sel y).Dom) ∧ true ∈ ρ.sel x) ∧ _
  rw [and_iff_right hsel]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Filtering selection decisions composes selection on each finite output chain. -/
private lemma isMisesKLRandomAt_iff_total_onParity_output_thinning
    (ρ ρ' : KLRule) (w : CantorSeq) (R : Set BitString)
    (hnext : ρ'.next = ρ.next)
    (hdom : ∀ t, (ρ.next (ρ.revealed w t)).Dom)
    (hselect : ∀ t, ρ.revealed w t ∈ partialRuleSet ρ'.sel ↔
      ρ.revealed w t ∈ partialRuleSet ρ.sel ∧ ρ.outputChain w t ∈ R) :
    ∀ t, ρ'.outputChain w t = selectedBits R (ρ.outputChain w t) := by
  classical
  have heq (t : ℕ) : ρ'.outputChain w t =
      selectedBits (partialRuleSet ρ'.sel) (ρ.revealed w t) := by
    unfold KLRule.outputChain
    rw [isMisesKLRandomAt_iff_total_onParity_output_revealed ρ ρ' hnext]
  have hstep (t : ℕ) : ρ.revealed w (t + 1) =
      ρ.revealed w t ++ [w ((ρ.next (ρ.revealed w t)).get (hdom t))] := by
    rw [KLRule.revealed, dite_eq_left (hdom t)]
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [heq, hstep, selectedBits_append_singleton, ← heq t, ih]
    have ho : ρ.outputChain w (t + 1) = ρ.outputChain w t ++
        (if ρ.revealed w t ∈ partialRuleSet ρ.sel then
          [w ((ρ.next (ρ.revealed w t)).get (hdom t))] else []) := by
      change selectedBits _ (ρ.revealed w (t + 1)) = _
      rw [hstep, selectedBits_append_singleton]
      rfl
    rw [ho]
    by_cases hp : ρ.revealed w t ∈ partialRuleSet ρ.sel
    · rw [ite_eq_left hp, selectedBits_append_singleton]
      by_cases hR : ρ.outputChain w t ∈ R
      · rw [ite_eq_left ((hselect t).mpr ⟨hp, hR⟩), ite_eq_left hR]
      · rw [ite_eq_right (fun h => hR ((hselect t).mp h).2), ite_eq_right hR]
    · rw [ite_eq_right hp, List.append_nil,
        ite_eq_right (fun h => hp ((hselect t).mp h).1), List.append_nil]

/-- Selecting from an unbounded output chain agrees with selecting from its infinite limit. -/
private lemma isMisesKLRandomAt_iff_total_onParity_output_transport
    (ρ : KLRule) (w u : CantorSeq) (hout : ρ.output w = .infinite u) (R : Set BitString) :
    streamOfChain (fun t => selectedBits R (ρ.outputChain w t))
      (fun t => selectedBits_prefix R (ρ.outputChain_prefix w t)) = selectStream R u := by
  obtain ⟨hpref, hlong⟩ :=
    isMisesKLRandomAt_iff_total_onParity_output_chain_facts ρ w u hout
  have hsets : chainPrefixSet (fun t => selectedBits R (ρ.outputChain w t)) =
      chainPrefixSet (selectChain R u) := by
    ext y
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨(ρ.outputChain w t).length, ?_⟩
      change y <+: selectedBits R (cantorPrefix u _)
      change y <+: selectedBits R (ρ.outputChain w t) at ht
      rwa [hpref t] at ht
    · rintro ⟨s, hs⟩
      obtain ⟨t, ht⟩ := hlong s
      refine ⟨t, ?_⟩
      change y <+: selectedBits R (ρ.outputChain w t)
      rw [hpref t]
      exact hs.trans (selectedBits_prefix R (cantorPrefix_mono u ht))
  simp only [selectStream, streamOfChain]
  congr 1

/-- Step 4 of the proof of `isMisesKLRandomAt_iff_total`: output decomposition along the
parity rules. -/
private lemma isMisesKLRandomAt_iff_total_onParity_output (ρ : KLRule) (w : CantorSeq)
    (u : CantorSeq)
    (hout : ρ.output w = .infinite u) :
    ∃ E : Set ℕ,
      (isMisesKLRandomAt_iff_total_onParity ρ false).output w = selectStream {x | x.length ∈ E} u ∧
      (isMisesKLRandomAt_iff_total_onParity ρ true).output w = selectStream {x | x.length ∉ E} u :=
          by
  classical
  obtain ⟨hnext, hdefs⟩ :=
    isMisesKLRandomAt_iff_total_onParity_output_run ρ w u hout
  let P (t : ℕ) := ρ.revealed w t ∈ partialRuleSet ρ.sel
  let n (t : ℕ) := (ρ.next (ρ.revealed w t)).get (hnext t)
  let E : Set ℕ := {i | (n (Nat.nth P i) % 2 == 1) = false}
  let R (b : Bool) : Set BitString := {x | (n (Nat.nth P x.length) % 2 == 1) = b}
  have hselect (b : Bool) (t : ℕ) :
      ρ.revealed w t ∈ partialRuleSet (isMisesKLRandomAt_iff_total_onParity ρ b).sel ↔
        ρ.revealed w t ∈ partialRuleSet ρ.sel ∧ ρ.outputChain w t ∈ R b := by
    rw [isMisesKLRandomAt_iff_total_onParity_output_parity_mem ρ b _
      (fun y hy => (hdefs t y hy).1) (fun y hy => (hdefs t y hy).2)]
    change P t ∧ (n t % 2 == 1) = b ↔
      P t ∧ (n (Nat.nth P (ρ.outputChain w t).length) % 2 == 1) = b
    apply and_congr_right
    intro hp
    have hlen := isMisesKLRandomAt_iff_total_onParity_output_length ρ w hnext t
    change (ρ.outputChain w t).length = Nat.count P t at hlen
    rw [hlen, Nat.nth_count hp]
  have hparity (b : Bool) :
      (isMisesKLRandomAt_iff_total_onParity ρ b).output w = selectStream (R b) u := by
    have hchain : (isMisesKLRandomAt_iff_total_onParity ρ b).outputChain w =
        fun t => selectedBits (R b) (ρ.outputChain w t) := by
      funext t
      exact isMisesKLRandomAt_iff_total_onParity_output_thinning
        ρ (isMisesKLRandomAt_iff_total_onParity ρ b) w (R b) rfl hnext (hselect b) t
    simpa only [KLRule.output, hchain] using
      isMisesKLRandomAt_iff_total_onParity_output_transport ρ w u hout (R b)
  refine ⟨E, hparity false, ?_⟩
  have hR : R true = {x | x.length ∉ E} := by
    ext x
    change (n (Nat.nth P x.length) % 2 == 1) = true ↔
      ¬ (n (Nat.nth P x.length) % 2 == 1) = false
    cases (n (Nat.nth P x.length) % 2 == 1) <;> decide
  rw [← hR]
  exact hparity true

/-- Step 1 of the proof of `isMisesKLRandomAt_iff_total_totalize`: sound, complete
and monotone primitive recursive fuel approximations. -/
lemma isMisesKLRandomAt_iff_total_fuel
    {β : Type} [Primcodable β] {F : BitString →. β} (hF : Partrec F) :
    ∃ Fs : ℕ → BitString → Option β,
      Primrec₂ Fs ∧
      (∀ s x n, Fs s x = some n → n ∈ F x) ∧
      (∀ x n, n ∈ F x → ∃ s, Fs s x = some n) ∧
      (∀ s x n, Fs s x = some n → ∀ t ≥ s, Fs t x = some n) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hF
  let Fs := fun s (x : BitString) =>
    (c.evaln s (Encodable.encode x)).bind (Encodable.decode (α := β))
  have heval : ∀ x, c.eval (Encodable.encode x) = (F x).map Encodable.encode := by
    intro x
    rw [hc]
    simp
  refine ⟨Fs, ?_, ?_, ?_, ?_⟩
  · exact Primrec.option_bind
      (Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.fst.pair (Primrec.const c)).pair
          (Primrec.encode.comp Primrec.snd)))
      (Primrec.decode.comp Primrec.snd)
  · intro s x n hn
    obtain ⟨k, hk, hn⟩ := Option.mem_bind_iff.mp hn
    have hk' := Nat.Partrec.Code.evaln_sound hk
    rw [heval x] at hk'
    have hex : ∃ v, v ∈ F x ∧ Encodable.encode v = k := by
      simpa only [Part.mem_map_iff] using hk'
    obtain ⟨v, hv, rfl⟩ := hex
    have hnv : v = n := by simpa using hn
    simpa [← hnv] using hv
  · intro x n hn
    have hn' : Encodable.encode n ∈ c.eval (Encodable.encode x) := by
      rw [heval]
      exact Part.mem_map Encodable.encode hn
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hn'
    refine ⟨s, ?_⟩
    simp only [Fs, Option.mem_def] at hs ⊢
    simp [hs]
  · intro s x n hn t hst
    obtain ⟨k, hk, hn⟩ := Option.mem_bind_iff.mp hn
    have hk' := Nat.Partrec.Code.evaln_mono hst hk
    exact Option.mem_bind_iff.mpr ⟨k, hk', hn⟩

/-- The finite simulator stores its virtual input and every physical card already read. -/
private abbrev isMisesKLRandomAt_iff_total_totalize_State :=
  BitString × List (ℕ × Bool)

/-- An instruction gives the physical card, selection flag, virtual input, and whether to append
this physical card's bit to the virtual input. -/
private abbrev isMisesKLRandomAt_iff_total_totalize_Action :=
  ℕ × Bool × BitString × Bool

/-- A filler of the unused parity above all positions recorded so far. -/
def isMisesKLRandomAt_iff_total_totalize_filler
    (b : Bool) (K : List (ℕ × Bool)) : ℕ :=
  2 * ((K.map Prod.fst).sum + 1) + cond b 0 1

/-- Step 2 of the proof of `isMisesKLRandomAt_iff_total_totalize`: fillers have
the unused parity and have not been read, even for an arbitrary finite record. -/
lemma isMisesKLRandomAt_iff_total_filler
    (b : Bool) (K : List (ℕ × Bool)) :
    isMisesKLRandomAt_iff_total_totalize_filler b K ∉ K.map Prod.fst ∧
    (isMisesKLRandomAt_iff_total_totalize_filler b K % 2 == 1) ≠ b := by
  constructor
  · intro h
    have hle := List.single_le_sum (fun (n : ℕ) _ => Nat.zero_le n) _ h
    dsimp [isMisesKLRandomAt_iff_total_totalize_filler] at hle
    cases b <;> simp only [Bool.cond_false, Bool.cond_true] at hle <;> omega
  · cases b <;>
      simp [isMisesKLRandomAt_iff_total_totalize_filler, Nat.add_mod]

/-- One instruction of the dovetailing machine. Already read cards of the selected parity are
rejected defensively; for sound approximations of a no-repeat rule this branch is unreachable. -/
private def isMisesKLRandomAt_iff_total_totalize_plan
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (st : isMisesKLRandomAt_iff_total_totalize_State) :
    isMisesKLRandomAt_iff_total_totalize_Action :=
  let idle := (isMisesKLRandomAt_iff_total_totalize_filler b st.2,
    false, st.1, false)
  match Fs st.2.length st.1 with
  | none => idle
  | some n =>
    match st.2.lookup n with
    | some c =>
      if (n % 2 == 1) == b then idle
      else (idle.1, false, st.1 ++ [c], false)
    | none =>
      if (n % 2 == 1) == b then
        match Gs st.2.length st.1 with
        | none => idle
        | some g => (n, g, st.1, true)
      else (n, false, st.1, true)

/-- Execute an instruction and remember the new card and its value. -/
private def isMisesKLRandomAt_iff_total_totalize_step
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (st : isMisesKLRandomAt_iff_total_totalize_State) (c : Bool) :
    isMisesKLRandomAt_iff_total_totalize_State :=
  let a := isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b st
  (if a.2.2.2 then a.2.2.1 ++ [c] else a.2.2.1, st.2 ++ [(a.1, c)])

/-- Replay a finite physical history to recover the virtual input and read-card record. -/
private def isMisesKLRandomAt_iff_total_totalize_replay
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (y : BitString) : isMisesKLRandomAt_iff_total_totalize_State :=
  y.foldl (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b) ([], [])

/-- The two total functions extracted from the next instruction after replay. -/
private def isMisesKLRandomAt_iff_total_totalize_F1G1
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (y : BitString) : ℕ × Bool :=
  let a := isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b
    (isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b y)
  (a.1, a.2.1)

/-- Absence from the association list is exactly absence from its list of positions. -/
lemma isMisesKLRandomAt_iff_total_totalize_lookup_none
    (K : List (ℕ × Bool)) (n : ℕ) :
    K.lookup n = none ↔ n ∉ K.map Prod.fst := by
  induction K with
  | nil => simp [List.lookup]
  | cons p K ih =>
    rcases p with ⟨m, c⟩
    by_cases h : n = m
    · simp [List.lookup, h]
    · have he : (n == m) = false := beq_eq_false_iff_ne.mpr h
      simpa only [List.lookup, he, List.map_cons, List.mem_cons, not_or, h, false_or,
        not_false_eq_true, true_and] using ih

/-- Every instruction requests a card absent from the complete physical record. -/
private lemma isMisesKLRandomAt_iff_total_totalize_plan_fresh
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (st : isMisesKLRandomAt_iff_total_totalize_State) :
    (isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b st).1 ∉ st.2.map Prod.fst := by
  have hf := (isMisesKLRandomAt_iff_total_filler b st.2).1
  unfold isMisesKLRandomAt_iff_total_totalize_plan
  split
  · exact hf
  · rename_i n hn
    split
    · rename_i c hc
      split <;> exact hf
    · rename_i hnK
      have hmem := (isMisesKLRandomAt_iff_total_totalize_lookup_none st.2 n).mp hnK
      split
      · split
        · exact hf
        · exact hmem
      · exact hmem

/-- Executing any finite history only extends the read-card record. -/
private lemma isMisesKLRandomAt_iff_total_totalize_record_prefix
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (z : BitString) (st : isMisesKLRandomAt_iff_total_totalize_State) :
    st.2 <+: (z.foldl (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b) st).2 := by
  induction z generalizing st with
  | nil => exact List.prefix_rfl
  | cons c z ih =>
    exact (List.prefix_append _ _).trans
      (ih (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b st c))

/-- Step 4 of the proof of `isMisesKLRandomAt_iff_total_totalize`: no card is
requested twice on compatible histories, for arbitrary fuel functions. -/
private lemma isMisesKLRandomAt_iff_total_noRepeat
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (x y : BitString) (hxy : x <+: y) (hne : x ≠ y) :
    (isMisesKLRandomAt_iff_total_totalize_F1G1 Fs Gs b x).1 ≠
      (isMisesKLRandomAt_iff_total_totalize_F1G1 Fs Gs b y).1 := by
  obtain ⟨z, rfl⟩ := hxy
  cases z with
  | nil => simp at hne
  | cons c z =>
    let st := isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b x
    have hp := isMisesKLRandomAt_iff_total_totalize_record_prefix Fs Gs b z
      (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b st c)
    have hmem : ((isMisesKLRandomAt_iff_total_totalize_F1G1 Fs Gs b x).1, c) ∈
        (isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (x ++ c :: z)).2 := by
      rw [isMisesKLRandomAt_iff_total_totalize_replay, List.foldl_append,
        List.foldl_cons]
      change _ ∈ (z.foldl (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b)
        (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b st c)).2
      exact hp.subset (by simp [isMisesKLRandomAt_iff_total_totalize_step,
        isMisesKLRandomAt_iff_total_totalize_F1G1, st])
    intro heq
    have hf := isMisesKLRandomAt_iff_total_totalize_plan_fresh Fs Gs b
      (isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (x ++ c :: z))
    apply hf
    exact List.mem_map.mpr ⟨_, hmem, heq⟩

/-- The explicit total rule defined by the replay machine. -/
private def isMisesKLRandomAt_iff_total_totalize_rule
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool) : KLRule where
  next y := Part.some (isMisesKLRandomAt_iff_total_totalize_F1G1 Fs Gs b y).1
  sel y := Part.some (isMisesKLRandomAt_iff_total_totalize_F1G1 Fs Gs b y).2
  noRepeat x y hxy hne a ha d hd := by
    have hf := isMisesKLRandomAt_iff_total_noRepeat Fs Gs b x y hxy hne
    simp only [Part.mem_some_iff] at ha hd
    subst a d
    exact hf

/-- The filler can be computed by a finite sum and arithmetic. -/
lemma isMisesKLRandomAt_iff_total_filler_primrec (b : Bool) :
    Primrec (isMisesKLRandomAt_iff_total_totalize_filler b) := by
  have hsum : Primrec (fun l : List ℕ => l.sum) := by
    refine (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq ?_
    intro l
    change l.foldr (fun n s => n + s) 0 = l.sum
    induction l with
    | nil => rfl
    | cons n l ih => simp only [List.foldr_cons, List.sum_cons, ih]
  have hmap : Primrec (fun K : List (ℕ × Bool) => K.map Prod.fst) :=
    Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp (hsum.comp hmap)))
    (Primrec.const (cond b 0 1))

/-- A bounded instruction uses only primitive recursive operations. -/
private lemma isMisesKLRandomAt_iff_total_plan_primrec
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs : Primrec₂ Fs) (hGs : Primrec₂ Gs) :
    Primrec (isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b) := by
  let S := isMisesKLRandomAt_iff_total_totalize_State
  let A := isMisesKLRandomAt_iff_total_totalize_Action
  have hf : Primrec (fun st : S =>
      isMisesKLRandomAt_iff_total_totalize_filler b st.2) :=
    (isMisesKLRandomAt_iff_total_filler_primrec b).comp Primrec.snd
  have hi : Primrec (fun st : S =>
      (isMisesKLRandomAt_iff_total_totalize_filler b st.2, false, st.1, false) : S → A) :=
    hf.pair ((Primrec.const false).pair (Primrec.fst.pair (Primrec.const false)))
  have hp : Primrec (fun p : S × ℕ => (p.2 % 2 == 1) == b) :=
    Primrec.beq.comp
      (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
        (Primrec.const 1)) (Primrec.const b)
  have hq : Primrec (fun p : (S × ℕ) × Bool => (p.1.2, p.2, p.1.1.1, true) :
      ((S × ℕ) × Bool) → A) :=
    (Primrec.snd.comp Primrec.fst).pair
      (Primrec.snd.pair ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.const true)))
  have hg : Primrec (fun p : S × ℕ =>
      match Gs p.1.2.length p.1.1 with
      | none => (isMisesKLRandomAt_iff_total_totalize_filler b p.1.2,
          false, p.1.1, false)
      | some g => (p.2, g, p.1.1, true)) := by
    refine (Primrec.option_casesOn
      (hGs.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.fst)) (hi.comp Primrec.fst) hq.to₂).of_eq ?_
    intro p
    cases Gs p.1.2.length p.1.1 <;> rfl
  have hu : Primrec (fun p : S × ℕ =>
      if (p.2 % 2 == 1) == b then
        match Gs p.1.2.length p.1.1 with
        | none => (isMisesKLRandomAt_iff_total_totalize_filler b p.1.2,
            false, p.1.1, false)
        | some g => (p.2, g, p.1.1, true)
      else (p.2, false, p.1.1, true)) := by
    simpa only [Bool.cond_eq_ite] using Primrec.cond hp hg
      (Primrec.snd.pair ((Primrec.const false).pair
        ((Primrec.fst.comp Primrec.fst).pair (Primrec.const true))))
  have hc : Primrec (fun p : (S × ℕ) × Bool =>
      if (p.1.2 % 2 == 1) == b then
        (isMisesKLRandomAt_iff_total_totalize_filler b p.1.1.2,
          false, p.1.1.1, false)
      else (isMisesKLRandomAt_iff_total_totalize_filler b p.1.1.2,
        false, p.1.1.1 ++ [p.2], false)) := by
    simpa only [Bool.cond_eq_ite] using Primrec.cond (hp.comp Primrec.fst)
      (hi.comp (Primrec.fst.comp Primrec.fst))
      ((hf.comp (Primrec.fst.comp Primrec.fst)).pair ((Primrec.const false).pair
        ((Primrec.list_concat.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd).pair (Primrec.const false))))
  have hn := Primrec.option_casesOn
    (Primrec.listLookup.comp Primrec.snd (Primrec.snd.comp Primrec.fst)) hu hc.to₂
  refine (Primrec.option_casesOn
    (hFs.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst) hi hn.to₂).of_eq ?_
  intro st
  unfold isMisesKLRandomAt_iff_total_totalize_plan
  cases Fs st.2.length st.1 with
  | none => rfl
  | some n =>
    dsimp only
    cases st.2.lookup n <;> rfl

/-- Step 3 of the proof of `isMisesKLRandomAt_iff_total_totalize`: both total
functions are primitive recursive, by folding the finite instruction evaluator. -/
private lemma isMisesKLRandomAt_iff_total_primrec
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs : Primrec₂ Fs) (hGs : Primrec₂ Gs) :
    Primrec (isMisesKLRandomAt_iff_total_totalize_F1G1 Fs Gs b) := by
  let S := isMisesKLRandomAt_iff_total_totalize_State
  have hp := isMisesKLRandomAt_iff_total_plan_primrec Fs Gs b hFs hGs
  have ha := hp.comp (Primrec.fst : Primrec (Prod.fst : S × Bool → S))
  have hx := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hb := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hs : Primrec (fun p : S × Bool =>
      isMisesKLRandomAt_iff_total_totalize_step Fs Gs b p.1 p.2) := by
    simpa only [isMisesKLRandomAt_iff_total_totalize_step, Bool.cond_eq_ite] using
      (Primrec.cond hb (Primrec.list_concat.comp hx Primrec.snd) hx).pair
        (Primrec.list_concat.comp (Primrec.snd.comp Primrec.fst)
          ((Primrec.fst.comp ha).pair Primrec.snd))
  have hr : Primrec (isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b) :=
    Primrec.list_foldl Primrec.id (Primrec.const ([], [])) (hs.comp Primrec.snd).to₂
  exact (Primrec.fst.comp (hp.comp hr)).pair
    (Primrec.fst.comp (Primrec.snd.comp (hp.comp hr)))

/-- A successful lookup gives a recorded physical card. -/
lemma isMisesKLRandomAt_iff_total_totalize_lookup_mem
    (K : List (ℕ × Bool)) (n : ℕ) (c : Bool) (h : K.lookup n = some c) :
    (n, c) ∈ K := by
  induction K with
  | nil => simp [List.lookup] at h
  | cons p K ih =>
    rcases p with ⟨m, d⟩
    by_cases he : n = m
    · subst m
      simp [List.lookup] at h
      subst c
      simp
    · have hb : (n == m) = false := beq_eq_false_iff_ne.mpr he
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A defined selection decision extends the selected string by precisely its chosen bit. -/
private lemma isMisesKLRandomAt_iff_total_totalize_selected_append
    (r : BitString →. Bool) (x : BitString) (c g : Bool)
    (hpre : ∀ z, z <+: x → z ≠ x → (r z).Dom) (hg : g ∈ r x) :
    selectedBits (partialRuleSet r) (x ++ [c]) =
      selectedBits (partialRuleSet r) x ++ (if g then [c] else []) := by
  classical
  have hall : ∀ z, z <+: x → (r z).Dom := by
    intro z hz
    by_cases he : z = x
    · simpa [he] using hg.1
    · exact hpre z hz he
  have hm : x ∈ partialRuleSet r ↔ g = true := by
    constructor
    · intro h
      exact Part.mem_unique hg h.2
    · intro h
      exact ⟨hall, h ▸ hg⟩
  rw [selectedBits_append_singleton, hm]
  cases g <;> simp

/-- The local semantic alternatives: either an unselected filler leaves the virtual input
unchanged, or one defined original step is performed. A cached original card is unselected. -/
private lemma isMisesKLRandomAt_iff_total_totalize_classify
    (ρ : KLRule)
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs : ∀ s x n, Fs s x = some n → n ∈ ρ.next x)
    (hGs : ∀ s x g, Gs s x = some g → g ∈ ρ.sel x)
    (hsel : ∀ x n, n ∈ ρ.next x → (n % 2 == 1) ≠ b → ρ.sel x = Part.some false)
    (w : CantorSeq) (st : isMisesKLRandomAt_iff_total_totalize_State)
    (hK : ∀ n c, (n, c) ∈ st.2 → c = w n) :
    let a := isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b st
    let st' := isMisesKLRandomAt_iff_total_totalize_step Fs Gs b st (w a.1)
    (a.2.1 = false ∧ st'.1 = st.1 ∧ (a.1 % 2 == 1) ≠ b) ∨
      ∃ n g, n ∈ ρ.next st.1 ∧ g ∈ ρ.sel st.1 ∧
        st'.1 = st.1 ++ [w n] ∧ a.2.1 = g ∧
        (a.1 = n ∨ ((a.1 % 2 == 1) ≠ b ∧ g = false)) := by
  have hf := (isMisesKLRandomAt_iff_total_filler b st.2).2
  dsimp only
  cases hF : Fs st.2.length st.1 with
  | none =>
    left
    simp [isMisesKLRandomAt_iff_total_totalize_step,
      isMisesKLRandomAt_iff_total_totalize_plan, hF, hf]
  | some n =>
    have hn := hFs _ _ _ hF
    cases hL : st.2.lookup n with
    | some c =>
      by_cases hp : (n % 2 == 1) = b
      · have hb : ((n % 2 == 1) == b) = true := beq_iff_eq.mpr hp
        left
        simp [isMisesKLRandomAt_iff_total_totalize_step,
          isMisesKLRandomAt_iff_total_totalize_plan, hF, hL, hb, hf]
      · have hb : ((n % 2 == 1) == b) = false := beq_eq_false_iff_ne.mpr hp
        have hc := hK n c (isMisesKLRandomAt_iff_total_totalize_lookup_mem _ _ _ hL)
        have hg : false ∈ ρ.sel st.1 := by rw [hsel _ _ hn hp]; simp
        right
        refine ⟨n, false, hn, hg, ?_⟩
        simp [isMisesKLRandomAt_iff_total_totalize_step,
          isMisesKLRandomAt_iff_total_totalize_plan, hF, hL, hb, hc, hf]
    | none =>
      by_cases hp : (n % 2 == 1) = b
      · have hb : ((n % 2 == 1) == b) = true := beq_iff_eq.mpr hp
        cases hG : Gs st.2.length st.1 with
        | none =>
          left
          simp [isMisesKLRandomAt_iff_total_totalize_step,
            isMisesKLRandomAt_iff_total_totalize_plan, hF, hL, hG, hb, hf]
        | some g =>
          right
          refine ⟨n, g, hn, hGs _ _ _ hG, ?_⟩
          simp [isMisesKLRandomAt_iff_total_totalize_step,
            isMisesKLRandomAt_iff_total_totalize_plan, hF, hL, hG, hb]
      · have hb : ((n % 2 == 1) == b) = false := beq_eq_false_iff_ne.mpr hp
        have hg : false ∈ ρ.sel st.1 := by rw [hsel _ _ hn hp]; simp
        right
        refine ⟨n, false, hn, hg, ?_⟩
        simp [isMisesKLRandomAt_iff_total_totalize_step,
          isMisesKLRandomAt_iff_total_totalize_plan, hF, hL, hb]

/-- The semantic part of the replay invariant, independent of elapsed time and output length. -/
private def isMisesKLRandomAt_iff_total_totalize_Good
    (ρ : KLRule) (b : Bool) (w : CantorSeq)
    (st : isMisesKLRandomAt_iff_total_totalize_State) : Prop :=
  ρ.revealed w st.1.length = st.1 ∧
    (∀ z, z <+: st.1 → z ≠ st.1 → (ρ.sel z).Dom) ∧
    (∀ n c, (n, c) ∈ st.2 → c = w n) ∧
    (∀ n c, (n, c) ∈ st.2 → (n % 2 == 1) = b →
      ∃ j < st.1.length, n ∈ ρ.next (st.1.take j))

/-- Executing one physical instruction preserves the virtual-run invariant and its selection. -/
private lemma isMisesKLRandomAt_iff_total_preserves
    (ρ : KLRule)
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs : ∀ s x n, Fs s x = some n → n ∈ ρ.next x)
    (hGs : ∀ s x g, Gs s x = some g → g ∈ ρ.sel x)
    (hsel : ∀ x n, n ∈ ρ.next x → (n % 2 == 1) ≠ b → ρ.sel x = Part.some false)
    (w : CantorSeq) (st : isMisesKLRandomAt_iff_total_totalize_State)
    (hgood : isMisesKLRandomAt_iff_total_totalize_Good ρ b w st) :
    let a := isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b st
    let st' := isMisesKLRandomAt_iff_total_totalize_step Fs Gs b st (w a.1)
    isMisesKLRandomAt_iff_total_totalize_Good ρ b w st' ∧
      st.1 <+: st'.1 ∧
      selectedBits (partialRuleSet ρ.sel) st'.1 =
        selectedBits (partialRuleSet ρ.sel) st.1 ++ (if a.2.1 then [w a.1] else []) := by
  classical
  let a := isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b st
  let st' := isMisesKLRandomAt_iff_total_totalize_step Fs Gs b st (w a.1)
  change isMisesKLRandomAt_iff_total_totalize_Good ρ b w st' ∧
    st.1 <+: st'.1 ∧ selectedBits (partialRuleSet ρ.sel) st'.1 =
      selectedBits (partialRuleSet ρ.sel) st.1 ++ (if a.2.1 then [w a.1] else [])
  have hk : ∀ n c, (n, c) ∈ st'.2 → c = w n := by
    intro n c hc
    change (n, c) ∈ st.2 ++ [(a.1, w a.1)] at hc
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hc
    rcases hc with hc | ⟨rfl, rfl⟩
    · exact hgood.2.2.1 n c hc
    · rfl
  have hclass := isMisesKLRandomAt_iff_total_totalize_classify
    ρ Fs Gs b hFs hGs hsel w st hgood.2.2.1
  change (a.2.1 = false ∧ st'.1 = st.1 ∧ (a.1 % 2 == 1) ≠ b) ∨
    (∃ n g, n ∈ ρ.next st.1 ∧ g ∈ ρ.sel st.1 ∧ st'.1 = st.1 ++ [w n] ∧
      a.2.1 = g ∧ (a.1 = n ∨ ((a.1 % 2 == 1) ≠ b ∧ g = false))) at hclass
  rcases hclass with ⟨hag, hx, hpar⟩ | ⟨n, g, hn, hg, hx, hag, hphys⟩
  · refine ⟨⟨?_, ?_, hk, ?_⟩, ?_, ?_⟩
    · simpa [hx] using hgood.1
    · simpa [hx] using hgood.2.1
    · intro n c hc hnp
      change (n, c) ∈ st.2 ++ [(a.1, w a.1)] at hc
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hc
      rcases hc with hc | ⟨rfl, rfl⟩
      · simpa [hx] using hgood.2.2.2 n c hc hnp
      · exact (hpar hnp).elim
    · rw [hx]
    · simp [hx, hag]
  · have hrev : ρ.revealed w (st.1 ++ [w n]).length = st.1 ++ [w n] := by
      simp only [List.length_append, List.length_singleton]
      rw [KLRule.revealed, hgood.1, dite_eq_left hn.1, Part.get_eq_of_mem hn hn.1]
    have hpre : ∀ z, z <+: st.1 ++ [w n] → z ≠ st.1 ++ [w n] → (ρ.sel z).Dom := by
      intro z hz hne
      rcases List.prefix_concat_iff.mp hz with he | hz
      · exact (hne he).elim
      · by_cases he : z = st.1
        · simpa [he] using hg.1
        · exact hgood.2.1 z hz he
    refine ⟨⟨?_, ?_, hk, ?_⟩, ?_, ?_⟩
    · simpa [hx] using hrev
    · simpa [hx] using hpre
    · intro m c hc hmp
      change (m, c) ∈ st.2 ++ [(a.1, w a.1)] at hc
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hc
      rw [hx]
      rcases hc with hc | ⟨rfl, rfl⟩
      · obtain ⟨j, hj, hnext⟩ := hgood.2.2.2 m c hc hmp
        refine ⟨j, by simpa using Nat.lt_succ_of_lt hj, ?_⟩
        simpa only [List.take_append_of_le_length hj.le] using hnext
      · rcases hphys with he | ⟨hpar, _⟩
        · refine ⟨st.1.length, by simp, ?_⟩
          simpa [he] using hn
        · exact (hpar hmp).elim
    · rw [hx]
      exact List.prefix_append _ _
    · rw [hx, isMisesKLRandomAt_iff_total_totalize_selected_append
        ρ.sel st.1 (w n) g hgood.2.1 hg, hag]
      rcases hphys with he | ⟨_, hgfalse⟩
      · rw [he]
      · simp [hgfalse]

/-- A total replay rule reveals its requested card at every physical step. -/
private lemma isMisesKLRandomAt_iff_total_totalize_revealed_succ
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (w : CantorSeq) (t : ℕ) :
    let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
    σ.revealed w (t + 1) = σ.revealed w t ++
      [w (isMisesKLRandomAt_iff_total_totalize_F1G1 Fs Gs b (σ.revealed w t)).1] := by
  dsimp only
  rw [KLRule.revealed]
  exact dite_eq_left trivial

/-- Replaying one further physical card executes exactly one instruction. -/
private lemma isMisesKLRandomAt_iff_total_totalize_replay_append
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (y : BitString) (c : Bool) :
    isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (y ++ [c]) =
      isMisesKLRandomAt_iff_total_totalize_step Fs Gs b
        (isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b y) c := by
  simp [isMisesKLRandomAt_iff_total_totalize_replay, List.foldl_append]
/-- Step 5 of the proof of `isMisesKLRandomAt_iff_total_totalize`: the replay
invariant. The virtual string is an actual original-run prefix; selection has halted on none of
its strict prefixes; the complete physical record contains the true bits; every recorded card
of the selected parity has already been consumed virtually; and the selected strings agree.
Only soundness of the fuel approximations is needed for this invariant. -/
private lemma isMisesKLRandomAt_iff_total_invariant
    (ρ : KLRule)
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs : ∀ s x n, Fs s x = some n → n ∈ ρ.next x)
    (hGs : ∀ s x g, Gs s x = some g → g ∈ ρ.sel x)
    (hsel : ∀ x n, n ∈ ρ.next x → (n % 2 == 1) ≠ b → ρ.sel x = Part.some false)
    (w : CantorSeq) (t : ℕ) :
    let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
    let st := isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w t)
    st.2.length = t ∧
      ρ.revealed w st.1.length = st.1 ∧
      (∀ z, z <+: st.1 → z ≠ st.1 → (ρ.sel z).Dom) ∧
      (∀ n c, (n, c) ∈ st.2 → c = w n) ∧
      (∀ n c, (n, c) ∈ st.2 → (n % 2 == 1) = b →
        ∃ j < st.1.length, n ∈ ρ.next (st.1.take j)) ∧
      σ.outputChain w t = selectedBits (partialRuleSet ρ.sel) st.1 := by
  classical
  let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
  let st := fun t => isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w t)
  have hi : ∀ t, isMisesKLRandomAt_iff_total_totalize_Good ρ b w (st t) ∧
      (st t).2.length = t ∧ σ.outputChain w t = selectedBits (partialRuleSet ρ.sel) (st t).1 := by
    intro t
    induction t with
    | zero =>
      simp [isMisesKLRandomAt_iff_total_totalize_Good, st,
        isMisesKLRandomAt_iff_total_totalize_replay, KLRule.revealed,
        KLRule.outputChain, selectedBits, selectedAux]
    | succ t ih =>
      let a := isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b (st t)
      have hs : st (t + 1) =
          isMisesKLRandomAt_iff_total_totalize_step Fs Gs b (st t) (w a.1) := by
        dsimp only [st]
        rw [isMisesKLRandomAt_iff_total_totalize_revealed_succ,
          isMisesKLRandomAt_iff_total_totalize_replay_append]
        rfl
      have hp := isMisesKLRandomAt_iff_total_preserves
        ρ Fs Gs b hFs hGs hsel w (st t) ih.1
      change isMisesKLRandomAt_iff_total_totalize_Good ρ b w
        (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b (st t) (w a.1)) ∧ _ at hp
      refine ⟨?_, ?_, ?_⟩
      · rw [hs]
        exact hp.1
      · rw [hs]
        change ((st t).2 ++ [(a.1, w a.1)]).length = t + 1
        simp [ih.2.1]
      · have hm : σ.revealed w t ∈ partialRuleSet σ.sel ↔ a.2.1 = true := by
          simp only [partialRuleSet, Set.mem_ofPred_eq, σ,
            isMisesKLRandomAt_iff_total_totalize_rule, Part.some_dom,
            implies_true, true_and, Part.mem_some_iff]
          change true = a.2.1 ↔ a.2.1 = true
          exact eq_comm
        change selectedBits (partialRuleSet σ.sel) (σ.revealed w (t + 1)) = _
        rw [isMisesKLRandomAt_iff_total_totalize_revealed_succ,
          selectedBits_append_singleton, hm]
        change σ.outputChain w t ++ _ = _
        have hcard : (isMisesKLRandomAt_iff_total_totalize_F1G1 Fs Gs b
            (σ.revealed w t)).1 = a.1 := rfl
        rw [hcard, ih.2.2, hs]
        have ho : selectedBits (partialRuleSet ρ.sel)
            (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b (st t) (w a.1)).1 =
            selectedBits (partialRuleSet ρ.sel) (st t).1 ++ (if a.2.1 then [w a.1] else []) :=
          hp.2.2
        cases hflag : a.2.1 <;> simpa [hflag] using ho.symm
  have h := hi t
  exact ⟨h.2.1, h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2.2⟩

/-- The original revealed string gains at most one bit per step. -/
private lemma isMisesKLRandomAt_iff_total_totalize_source_length
    (ρ : KLRule) (w : CantorSeq) (t : ℕ) : (ρ.revealed w t).length ≤ t := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    rw [KLRule.revealed]
    split_ifs
    · simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right ih 1
    · exact ih.trans (Nat.le_succ _)

/-- A defined original next card extends a correctly simulated virtual prefix. -/
private lemma isMisesKLRandomAt_iff_total_totalize_source_extend
    (ρ : KLRule) (w : CantorSeq) (x : BitString) (n : ℕ)
    (hx : ρ.revealed w x.length = x) (hn : n ∈ ρ.next x) :
    ρ.revealed w (x ++ [w n]).length = x ++ [w n] := by
  simp only [List.length_append, List.length_singleton]
  rw [KLRule.revealed, hx, dite_eq_left hn.1, Part.get_eq_of_mem hn hn.1]

/-- Inverting a nonempty original-run prefix recovers its previous prefix and last query. -/
private lemma isMisesKLRandomAt_iff_total_totalize_source_snoc
    (ρ : KLRule) (w : CantorSeq) (x : BitString) (c : Bool)
    (hx : ρ.revealed w (x ++ [c]).length = x ++ [c]) :
    ρ.revealed w x.length = x ∧ ∃ n ∈ ρ.next x, w n = c := by
  have hlen := isMisesKLRandomAt_iff_total_totalize_source_length ρ w x.length
  simp only [List.length_append, List.length_singleton] at hx
  rw [KLRule.revealed] at hx
  split_ifs at hx with hd
  · obtain ⟨hprev, hbit⟩ := List.append_inj' hx rfl
    obtain ⟨n, hn, hbit⟩ : ∃ n, n ∈ ρ.next (ρ.revealed w x.length) ∧ w n = c :=
      ⟨_, Part.get_mem hd, by simpa using hbit⟩
    rw [hprev] at hn
    exact ⟨hprev, n, hn, hbit⟩
  · rw [hx] at hlen
    simp at hlen

/-- Every prefix of a valid virtual history is itself a valid original history. -/
private lemma isMisesKLRandomAt_iff_total_totalize_source_prefix
    (ρ : KLRule) (w : CantorSeq) (x z : BitString)
    (hx : ρ.revealed w x.length = x) (hz : z <+: x) :
    ρ.revealed w z.length = z := by
  induction x using List.reverseRecOn with
  | nil =>
    have he : z = [] := by simpa using hz
    subst z
    rfl
  | append_singleton x c ih =>
    rcases List.prefix_concat_iff.mp hz with he | hz
    · simpa [he] using hx
    · exact ih (isMisesKLRandomAt_iff_total_totalize_source_snoc ρ w x c hx).1 hz

/-- A revealed history is already complete at the time given by its own length. -/
private lemma isMisesKLRandomAt_iff_total_totalize_source_fix
    (ρ : KLRule) (w : CantorSeq) (t : ℕ) :
    ρ.revealed w (ρ.revealed w t).length = ρ.revealed w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [KLRule.revealed]
    split_ifs with hd
    · exact isMisesKLRandomAt_iff_total_totalize_source_extend
        ρ w (ρ.revealed w t) _ ih (Part.get_mem hd)
    · exact ih

/-- Once selection is undefined on a prefix, extending that prefix selects nothing further. -/
private lemma isMisesKLRandomAt_iff_total_totalize_selected_stop
    (r : BitString →. Bool) (x y : BitString) (hx : ¬ (r x).Dom) (hxy : x <+: y) :
    selectedBits (partialRuleSet r) y = selectedBits (partialRuleSet r) x := by
  classical
  obtain ⟨z, rfl⟩ := hxy
  induction z using List.reverseRecOn with
  | nil => simp
  | append_singleton z c ih =>
    rw [← List.append_assoc, selectedBits_append_singleton, ih]
    have hnot : x ++ z ∉ partialRuleSet r := by
      intro h
      exact hx (h.1 x (List.prefix_append _ _))
    simp [hnot]

/-- A finite selected string is already obtained before the first undefined selection decision.
The witness contract also records that any proper cut is a point of divergence. -/
private lemma isMisesKLRandomAt_iff_total_totalize_selection_cut
    (r : BitString →. Bool) (x : BitString) :
    ∃ z, z <+: x ∧ (∀ y, y <+: z → y ≠ z → (r y).Dom) ∧
      (z = x ∨ ¬ (r z).Dom) ∧
      selectedBits (partialRuleSet r) z = selectedBits (partialRuleSet r) x := by
  classical
  induction x using List.reverseRecOn with
  | nil => refine ⟨[], List.prefix_rfl, ?_, Or.inl rfl, rfl⟩; simp
  | append_singleton x c ih =>
    obtain ⟨z, hzx, hpre, hstop, heq⟩ := ih
    by_cases he : z = x
    · subst z
      by_cases hd : (r x).Dom
      · refine ⟨x ++ [c], List.prefix_rfl, ?_, Or.inl rfl, rfl⟩
        intro y hy hne
        rcases List.prefix_concat_iff.mp hy with he | hy
        · exact (hne he).elim
        · by_cases he : y = x
          · simpa [he] using hd
          · exact hpre y hy he
      · exact ⟨x, List.prefix_append _ _, hpre, Or.inr hd,
          (isMisesKLRandomAt_iff_total_totalize_selected_stop r x _ hd
            (List.prefix_append _ _)).symm⟩
    · have hd := hstop.resolve_left he
      exact ⟨z, hzx.trans (List.prefix_append _ _), hpre, Or.inr hd,
        (isMisesKLRandomAt_iff_total_totalize_selected_stop r z _ hd
          (hzx.trans (List.prefix_append _ _))).symm⟩

/-- The virtual input never retreats during the total rule's run. -/
private lemma isMisesKLRandomAt_iff_total_virtual_prefix
    (ρ : KLRule)
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs : ∀ s x n, Fs s x = some n → n ∈ ρ.next x)
    (hGs : ∀ s x g, Gs s x = some g → g ∈ ρ.sel x)
    (hsel : ∀ x n, n ∈ ρ.next x → (n % 2 == 1) ≠ b → ρ.sel x = Part.some false)
    (w : CantorSeq) (t : ℕ) :
    let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
    (isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w t)).1 <+:
      (isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w (t + 1))).1 := by
  dsimp only
  have hi := isMisesKLRandomAt_iff_total_invariant
    ρ Fs Gs b hFs hGs hsel w t
  have hp := isMisesKLRandomAt_iff_total_preserves
    ρ Fs Gs b hFs hGs hsel w _
    ⟨hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1⟩
  rw [isMisesKLRandomAt_iff_total_totalize_revealed_succ,
    isMisesKLRandomAt_iff_total_totalize_replay_append]
  exact hp.2.1

/-- Step 6 of the proof of `isMisesKLRandomAt_iff_total_totalize`: a virtual
step with defined next position and selection decision is eventually simulated. Growing fuel
handles waiting, and the original no-repeat condition excludes a cached card of selected parity. -/
private lemma isMisesKLRandomAt_iff_total_advance
    (ρ : KLRule)
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs_sound : ∀ s x n, Fs s x = some n → n ∈ ρ.next x)
    (hFs_complete : ∀ x n, n ∈ ρ.next x → ∃ s, Fs s x = some n)
    (hFs_mono : ∀ s x n, Fs s x = some n → ∀ t ≥ s, Fs t x = some n)
    (hGs_sound : ∀ s x g, Gs s x = some g → g ∈ ρ.sel x)
    (hGs_complete : ∀ x g, g ∈ ρ.sel x → ∃ s, Gs s x = some g)
    (hGs_mono : ∀ s x g, Gs s x = some g → ∀ t ≥ s, Gs t x = some g)
    (hsel : ∀ x n, n ∈ ρ.next x → (n % 2 == 1) ≠ b → ρ.sel x = Part.some false)
    (w : CantorSeq) :
    let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
    let st := fun t => isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w t)
    ∀ t n g, n ∈ ρ.next (st t).1 → g ∈ ρ.sel (st t).1 →
      ∃ s, (st t).1 ++ [w n] <+: (st s).1 := by
  let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
  let st := fun t => isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w t)
  change ∀ t n g, n ∈ ρ.next (st t).1 → g ∈ ρ.sel (st t).1 →
    ∃ s, (st t).1 ++ [w n] <+: (st s).1
  intro t n g hn hg
  obtain ⟨sF, hF⟩ := hFs_complete _ _ hn
  obtain ⟨sG, hG⟩ := hGs_complete _ _ hg
  let k := t + sF + sG
  have hI := isMisesKLRandomAt_iff_total_invariant
    ρ Fs Gs b hFs_sound hGs_sound hsel w k
  have hlen : (st k).2.length = k := hI.1
  have hprefix : (st t).1 <+: (st k).1 :=
    chain_prefix_of_le (isMisesKLRandomAt_iff_total_virtual_prefix
      ρ Fs Gs b hFs_sound hGs_sound hsel w) (by dsimp [k]; omega)
  by_cases he : (st k).1 = (st t).1
  · have hFk : Fs (st k).2.length (st k).1 = some n := by
      rw [hlen, he]
      exact hFs_mono _ _ _ hF k (by dsimp [k]; omega)
    have hGk : Gs (st k).2.length (st k).1 = some g := by
      rw [hlen, he]
      exact hGs_mono _ _ _ hG k (by dsimp [k]; omega)
    have hnK : n ∈ ρ.next (st k).1 := by simpa only [he] using hn
    have hstep : (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b (st k)
        (w (isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b (st k)).1)).1 =
        (st k).1 ++ [w n] := by
      cases hL : (st k).2.lookup n with
      | none =>
        by_cases hp : (n % 2 == 1) = b
        · have hb : ((n % 2 == 1) == b) = true := beq_iff_eq.mpr hp
          simp [isMisesKLRandomAt_iff_total_totalize_step,
            isMisesKLRandomAt_iff_total_totalize_plan, hFk, hGk, hL, hb]
        · have hb : ((n % 2 == 1) == b) = false := beq_eq_false_iff_ne.mpr hp
          simp [isMisesKLRandomAt_iff_total_totalize_step,
            isMisesKLRandomAt_iff_total_totalize_plan, hFk, hL, hb]
      | some c =>
        have hmem := isMisesKLRandomAt_iff_total_totalize_lookup_mem _ _ _ hL
        have hp : (n % 2 == 1) ≠ b := by
          intro hp
          obtain ⟨j, hj, hjn⟩ := hI.2.2.2.2.1 n c hmem hp
          change j < (st k).1.length at hj
          change n ∈ ρ.next ((st k).1.take j) at hjn
          have hne : (st k).1.take j ≠ (st k).1 := by
            intro heq
            have hlength := congrArg List.length heq
            simp only [List.length_take, Nat.min_eq_left hj.le] at hlength
            omega
          exact (ρ.noRepeat _ _ (List.take_prefix _ _) hne n hjn n hnK) rfl
        have hb : ((n % 2 == 1) == b) = false := beq_eq_false_iff_ne.mpr hp
        have hc : c = w n := hI.2.2.2.1 n c hmem
        simp [isMisesKLRandomAt_iff_total_totalize_step,
          isMisesKLRandomAt_iff_total_totalize_plan, hFk, hL, hb, hc]
    refine ⟨k + 1, ?_⟩
    change (st t).1 ++ [w n] <+:
      (isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w (k + 1))).1
    rw [isMisesKLRandomAt_iff_total_totalize_revealed_succ,
      isMisesKLRandomAt_iff_total_totalize_replay_append]
    change (st t).1 ++ [w n] <+:
      (isMisesKLRandomAt_iff_total_totalize_step Fs Gs b (st k)
        (w (isMisesKLRandomAt_iff_total_totalize_plan Fs Gs b (st k)).1)).1
    rw [hstep, he]
  · have hlt : (st t).1.length < (st k).1.length := by
      have hle := hprefix.length_le
      by_contra h
      exact he (hprefix.eq_of_length (by omega)).symm
    have hT := isMisesKLRandomAt_iff_total_invariant
      ρ Fs Gs b hFs_sound hGs_sound hsel w t
    have hrev := isMisesKLRandomAt_iff_total_totalize_source_extend
      ρ w (st t).1 n hT.2.1 hn
    have hp := chain_prefix_of_le (ρ.revealed_prefix w)
      (show ((st t).1 ++ [w n]).length ≤ (st k).1.length by simp; omega)
    rw [hrev, hI.2.1] at hp
    exact ⟨k, hp⟩

/-- Every original history whose earlier selection decisions are defined is eventually covered
by the simulated history. The proof follows the finite original path one card at a time. -/
private lemma isMisesKLRandomAt_iff_total_reach
    (ρ : KLRule)
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs_sound : ∀ s x n, Fs s x = some n → n ∈ ρ.next x)
    (hFs_complete : ∀ x n, n ∈ ρ.next x → ∃ s, Fs s x = some n)
    (hFs_mono : ∀ s x n, Fs s x = some n → ∀ t ≥ s, Fs t x = some n)
    (hGs_sound : ∀ s x g, Gs s x = some g → g ∈ ρ.sel x)
    (hGs_complete : ∀ x g, g ∈ ρ.sel x → ∃ s, Gs s x = some g)
    (hGs_mono : ∀ s x g, Gs s x = some g → ∀ t ≥ s, Gs t x = some g)
    (hsel : ∀ x n, n ∈ ρ.next x → (n % 2 == 1) ≠ b → ρ.sel x = Part.some false)
    (w : CantorSeq) (x : BitString) (hx : ρ.revealed w x.length = x)
    (hpre : ∀ z, z <+: x → z ≠ x → (ρ.sel z).Dom) :
    let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
    ∃ t, x <+: (isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w t)).1 := by
  let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
  let st := fun t => isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w t)
  change ∃ t, x <+: (st t).1
  induction x using List.reverseRecOn with
  | nil => exact ⟨0, List.nil_prefix⟩
  | append_singleton x c ih =>
    have hpath := isMisesKLRandomAt_iff_total_totalize_source_snoc ρ w x c hx
    have hall : ∀ z, z <+: x → (ρ.sel z).Dom := by
      intro z hz
      refine hpre z (hz.trans (List.prefix_append _ _)) ?_
      intro he
      have hlength := hz.length_le
      rw [he] at hlength
      simp at hlength
    obtain ⟨t, ht⟩ := ih hpath.1 (fun z hz _ => hall z hz)
    by_cases he : (st t).1 = x
    · obtain ⟨n, hn, hnc⟩ := hpath.2
      obtain ⟨g, hg⟩ := Part.dom_iff_mem.mp (hall x List.prefix_rfl)
      have hn' : n ∈ ρ.next (st t).1 := by simpa only [he] using hn
      have hg' : g ∈ ρ.sel (st t).1 := by simpa only [he] using hg
      obtain ⟨s, hs⟩ := isMisesKLRandomAt_iff_total_advance
        ρ Fs Gs b hFs_sound hFs_complete hFs_mono hGs_sound hGs_complete hGs_mono hsel w t n g hn'
            hg'
      change (st t).1 ++ [w n] <+: (st s).1 at hs
      rw [he, hnc] at hs
      exact ⟨s, hs⟩
    · have hlt : x.length < (st t).1.length := by
        have hle := ht.length_le
        by_contra h
        exact he (ht.eq_of_length (by omega)).symm
      have hi := isMisesKLRandomAt_iff_total_invariant
        ρ Fs Gs b hFs_sound hGs_sound hsel w t
      have hp := chain_prefix_of_le (ρ.revealed_prefix w)
        (show (x ++ [c]).length ≤ (st t).1.length by simp; omega)
      rw [hx, hi.2.1] at hp
      exact ⟨t, hp⟩
/-- Step 6 of the proof of `isMisesKLRandomAt_iff_total_totalize`: cofinality
of selected prefixes. Sound, complete, monotone fuel approximations ensure that each finite
original selected prefix occurs as a prefix of some selected string of the explicit replay rule.
If the original next function or selection function diverges, only unselected fillers continue. -/
private lemma isMisesKLRandomAt_iff_total_cofinal
    (ρ : KLRule)
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs_sound : ∀ s x n, Fs s x = some n → n ∈ ρ.next x)
    (hFs_complete : ∀ x n, n ∈ ρ.next x → ∃ s, Fs s x = some n)
    (hFs_mono : ∀ s x n, Fs s x = some n → ∀ t ≥ s, Fs t x = some n)
    (hGs_sound : ∀ s x g, Gs s x = some g → g ∈ ρ.sel x)
    (hGs_complete : ∀ x g, g ∈ ρ.sel x → ∃ s, Gs s x = some g)
    (hGs_mono : ∀ s x g, Gs s x = some g → ∀ t ≥ s, Gs t x = some g)
    (hsel : ∀ x n, n ∈ ρ.next x → (n % 2 == 1) ≠ b → ρ.sel x = Part.some false)
    (w : CantorSeq) (j : ℕ) :
    ∃ t, ρ.outputChain w j <+:
      (isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b).outputChain w t := by
  let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
  obtain ⟨z, hz, hpre, _, hout⟩ :=
    isMisesKLRandomAt_iff_total_totalize_selection_cut ρ.sel (ρ.revealed w j)
  have hrun := isMisesKLRandomAt_iff_total_totalize_source_prefix
    ρ w (ρ.revealed w j) z
    (isMisesKLRandomAt_iff_total_totalize_source_fix ρ w j) hz
  obtain ⟨t, ht⟩ := isMisesKLRandomAt_iff_total_reach
    ρ Fs Gs b hFs_sound hFs_complete hFs_mono hGs_sound hGs_complete hGs_mono hsel w z hrun hpre
  have hi := isMisesKLRandomAt_iff_total_invariant
    ρ Fs Gs b hFs_sound hGs_sound hsel w t
  refine ⟨t, ?_⟩
  change selectedBits (partialRuleSet ρ.sel) (ρ.revealed w j) <+: σ.outputChain w t
  rw [← hout, hi.2.2.2.2.2]
  exact selectedBits_prefix _ ht

/-- Step 7 of the proof of `isMisesKLRandomAt_iff_total_totalize`: two inclusions
of chain prefix sets identify the finite or infinite output streams. -/
private lemma isMisesKLRandomAt_iff_total_output
    (ρ : KLRule)
    (Fs : ℕ → BitString → Option ℕ) (Gs : ℕ → BitString → Option Bool) (b : Bool)
    (hFs_sound : ∀ s x n, Fs s x = some n → n ∈ ρ.next x)
    (hFs_complete : ∀ x n, n ∈ ρ.next x → ∃ s, Fs s x = some n)
    (hFs_mono : ∀ s x n, Fs s x = some n → ∀ t ≥ s, Fs t x = some n)
    (hGs_sound : ∀ s x g, Gs s x = some g → g ∈ ρ.sel x)
    (hGs_complete : ∀ x g, g ∈ ρ.sel x → ∃ s, Gs s x = some g)
    (hGs_mono : ∀ s x g, Gs s x = some g → ∀ t ≥ s, Gs t x = some g)
    (hsel : ∀ x n, n ∈ ρ.next x → (n % 2 == 1) ≠ b → ρ.sel x = Part.some false)
    (w : CantorSeq) :
    (isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b).output w = ρ.output w := by
  let σ := isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b
  have heq : chainPrefixSet (σ.outputChain w) = chainPrefixSet (ρ.outputChain w) := by
    ext v
    constructor
    · rintro ⟨t, ht⟩
      have hi := isMisesKLRandomAt_iff_total_invariant
        ρ Fs Gs b hFs_sound hGs_sound hsel w t
      let st := isMisesKLRandomAt_iff_total_totalize_replay Fs Gs b (σ.revealed w t)
      change st.2.length = t ∧ _ at hi
      refine ⟨st.1.length, ?_⟩
      change v <+: selectedBits (partialRuleSet ρ.sel) (ρ.revealed w st.1.length)
      rw [hi.2.1, ← hi.2.2.2.2.2]
      exact ht
    · rintro ⟨j, hj⟩
      obtain ⟨t, ht⟩ := isMisesKLRandomAt_iff_total_cofinal
        ρ Fs Gs b hFs_sound hFs_complete hFs_mono hGs_sound hGs_complete hGs_mono hsel w j
      exact ⟨t, hj.trans ht⟩
  change streamOfChain (σ.outputChain w) (σ.outputChain_prefix w) =
    streamOfChain (ρ.outputChain w) (ρ.outputChain_prefix w)
  unfold streamOfChain
  congr 1

/-- Step 5 of the proof of `isMisesKLRandomAt_iff_total`: totalizing the rule. -/
private lemma isMisesKLRandomAt_iff_total_totalize (ρ : KLRule)
    (hρ : ρ.IsAdmissible)
    (b : Bool)
    (hsel : ∀ x n, n ∈ ρ.next x → (n % 2 == 1) ≠ b → ρ.sel x = Part.some false) :
    ∃ ρ1 : KLRule, ρ1.IsAdmissible ∧ ρ1.IsTotal ∧ ∀ w, ρ1.output w = ρ.output w := by
  obtain ⟨Fs, hFs, hFs_sound, hFs_complete, hFs_mono⟩ :=
    isMisesKLRandomAt_iff_total_fuel hρ.1
  obtain ⟨Gs, hGs, hGs_sound, hGs_complete, hGs_mono⟩ :=
    isMisesKLRandomAt_iff_total_fuel hρ.2
  have hc := isMisesKLRandomAt_iff_total_primrec Fs Gs b hFs hGs
  refine ⟨isMisesKLRandomAt_iff_total_totalize_rule Fs Gs b,
    ⟨(Primrec.fst.comp hc).to_comp.partrec, (Primrec.snd.comp hc).to_comp.partrec⟩,
    ⟨fun _ => trivial, fun _ => trivial⟩, ?_⟩
  exact isMisesKLRandomAt_iff_total_output
    ρ Fs Gs b hFs_sound hFs_complete hFs_mono hGs_sound hGs_complete hGs_mono hsel

/-- **SUV Theorem 191, p. 291 (Merkle).**  Restricting to total `F` and `G` gives the same class.
The printed statement is for frequency `1/2`.  Here it is generalized to any real frequency `p`:
the totalization argument splits the output into two subsequences and preserves any common limit.
For `p` outside `[0, 1]`, both sides are false by the identity rule. -/
theorem isMisesKLRandomAt_iff_total (p : ℝ) (w : CantorSeq) :
    IsMisesKLRandomAt p w ↔
      ∀ ρ : KLRule, ρ.IsAdmissible → ρ.IsTotal → FiniteOrFreq p (ρ.output w) := by
  refine ⟨fun h ρ hρ _ => h ρ hρ, fun h => ?_⟩
  intro ρ hρ
  rcases h_out : ρ.output w with _ | u
  · exact trivial
  · have ⟨ρ_false, h_false_adm, h_false_tot, h_false_eq⟩ :=
      isMisesKLRandomAt_iff_total_totalize (isMisesKLRandomAt_iff_total_onParity ρ false)
      (isMisesKLRandomAt_iff_total_onParity_admissible ρ false hρ) false
      (isMisesKLRandomAt_iff_total_onParity_sel ρ false)
    have ⟨ρ_true, h_true_adm, h_true_tot, h_true_eq⟩ := isMisesKLRandomAt_iff_total_totalize
        (isMisesKLRandomAt_iff_total_onParity ρ true)
        (isMisesKLRandomAt_iff_total_onParity_admissible ρ true hρ) true
        (isMisesKLRandomAt_iff_total_onParity_sel ρ true)
    have h_false_freq := h ρ_false h_false_adm h_false_tot
    have h_true_freq := h ρ_true h_true_adm h_true_tot
    rw [h_false_eq] at h_false_freq
    rw [h_true_eq] at h_true_freq
    have ⟨E, hE_false, hE_true⟩ := isMisesKLRandomAt_iff_total_onParity_output ρ w u h_out
    rw [hE_false] at h_false_freq
    rw [hE_true] at h_true_freq
    exact isMisesKLRandomAt_iff_total_analysis p E u h_false_freq h_true_freq

end Kolmogorov.FrequencyGames
