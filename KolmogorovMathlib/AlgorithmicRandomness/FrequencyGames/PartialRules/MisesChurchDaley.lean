/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.VilleExample
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.MonotoneComplexity.Dimension.LowComplexityCover

/-!
# Mises Church Daley

Mises-Church-Daley randomness: a sequence is random in this sense if every partially computable
admissible rule (in the sense of Church and Daley) selects from it either a finite sequence or an
infinite one with limit frequency `1/2`.

Main declarations:

* `IsMisesChurchDaleyRandomAt`, `IsMisesChurchDaleyRandom`: the definition, with the frequency as
  a parameter and for the frequency `1/2`;
* `IsMisesChurchDaleyRandomAt.isMisesChurchRandomAt`: Mises-Church-Daley randomness implies
  Mises-Church randomness;
* `isMisesChurchDaleyRandom_of_selectStream`: closure under composition of selections, i.e. a
  sequence selected from a Mises-Church-Daley random sequence by an admissible rule is again
  Mises-Church-Daley random.

This formalizes the discussion of Mises-Church-Daley randomness on p. 287 of the book by Shen,
Uspensky and Vereshchagin, "Kolmogorov complexity and algorithmic randomness".
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology

/-- **SUV p. 287**, with the frequency as a parameter: every Church-Daley admissible rule selects a
finite sequence or one with limit frequency `p`. -/
def IsMisesChurchDaleyRandomAt (p : ℝ) (w : CantorSeq) : Prop :=
  ∀ r : BitString →. Bool, Partrec r → FiniteOrFreq p (selectStream (partialRuleSet r) w)

/-- **SUV p. 287.**  *Mises-Church-Daley random* sequences. -/
abbrev IsMisesChurchDaleyRandom (w : CantorSeq) : Prop := IsMisesChurchDaleyRandomAt (1 / 2) w

/-- A decidable set is the set of a total, hence partial, computable rule. -/
lemma exists_partrec_partialRuleSet_eq {R : Set BitString} (hR : IsDecidableSet R) :
    ∃ r : BitString →. Bool, Partrec r ∧ partialRuleSet r = R := by
  obtain ⟨f, hf, hfR⟩ := hR
  refine ⟨fun x => Part.some (f x), hf.partrec, ?_⟩
  ext x
  simp only [partialRuleSet, Set.mem_ofPred_eq, Part.some_dom, implies_true, true_and,
    Part.mem_some_iff]
  rw [← hfR x]
  exact eq_comm

/-- **SUV p. 287.**  Church-admissible rules are Church-Daley admissible, so Mises-Church-Daley
random sequences are Mises-Church random. -/
theorem IsMisesChurchDaleyRandomAt.isMisesChurchRandomAt {p : ℝ} {w : CantorSeq}
    (hw : IsMisesChurchDaleyRandomAt p w) : IsMisesChurchRandomAt p w := by
  intro R hR
  obtain ⟨r, hr, rfl⟩ := exists_partrec_partialRuleSet_eq hR
  exact hw r hr

/-- Step 1 of the proof of `isMisesChurchDaleyRandom_of_selectStream`: Define a partial
recursive function to compute selected bits without hanging if the condition fails on a prefix. -/
def isMisesChurchDaleyRandom_of_selectStream_selPart
    (r : BitString →. Bool) (x : BitString) : Part BitString :=
  Nat.recOn x.length (Part.some []) fun n ih => do
    let s ← ih
    let b ← r (x.take n)
    if b then Part.some (s ++ [x.getD n false]) else Part.some s

/-- Step 2 of the proof of `isMisesChurchDaleyRandom_of_selectStream`: Define the composed
partial rule. -/
private def isMisesChurchDaleyRandom_of_selectStream_compose
    (r r' : BitString →. Bool) : BitString →. Bool :=
  fun x => do
    let s ← isMisesChurchDaleyRandom_of_selectStream_selPart r x
    let c ← r x
    if c then r' s else pure false


/-- Step 3 of the proof of `isMisesChurchDaleyRandom_of_selectStream`: Define a partial
recursive function to compute selected bits without hanging if the condition fails on a prefix. -/
lemma isMisesChurchDaleyRandom_of_selectStream_selPart_partrec
    (r : BitString →. Bool) (hr : Partrec r) :
    Partrec (isMisesChurchDaleyRandom_of_selectStream_selPart r) := by
  have h1 : Partrec (fun (xn : BitString × ℕ) => 
    (Nat.rec (Part.some []) (fun n ih => ih >>= fun s => do
      let b ← r (xn.1.take n)
      if b then Part.some (s ++ [xn.1.getD n false]) else Part.some s) xn.2 : Part BitString)) := by
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

/-- Step 3 of the proof of `isMisesChurchDaleyRandom_of_selectStream`: The composed
partial rule is partial recursive. -/
private lemma isMisesChurchDaleyRandom_of_selectStream_compose_partrec
    (r r' : BitString →. Bool) (hr : Partrec r) (hr' : Partrec r') :
    Partrec (isMisesChurchDaleyRandom_of_selectStream_compose r r') := by
  have h1 : Partrec (isMisesChurchDaleyRandom_of_selectStream_selPart r) :=
    isMisesChurchDaleyRandom_of_selectStream_selPart_partrec r hr
  have hc : Partrec (fun (x : BitString) => do
    let s ← isMisesChurchDaleyRandom_of_selectStream_selPart r x
    let c ← r x
    if c then r' s else Part.some false) := by
    have h_s : Partrec (fun (x : BitString) =>
      isMisesChurchDaleyRandom_of_selectStream_selPart r x) := h1
    have h_c : Partrec (fun (x : BitString × BitString) => r x.1) := hr.comp Computable.fst
    apply Partrec.bind h_s
    apply Partrec.bind h_c
    have h_r_prime : Partrec (fun (p : (BitString × BitString) × Bool) => r' p.1.2) :=
      hr'.comp (Computable.snd.comp Computable.fst)
    have h_false : Partrec (fun (p : (BitString × BitString) × Bool) => Part.some false) :=
      Computable.partrec (Computable.const false)
    have h_cond : Partrec (fun (p : (BitString × BitString) × Bool) =>
      bif p.2 then r' p.1.2 else Part.some false) :=
      Partrec.cond Computable.snd h_r_prime h_false
    apply Partrec.of_eq h_cond
    intro p
    cases p.2
    · rfl
    · rfl
  exact hc

/-- Step 1 of the proof of `isMisesChurchDaleyRandom_of_selectStream_compose_eq`:
Characterize each selection stage. -/
lemma isMisesChurchDaleyRandom_of_selectStream_stage
    (r : BitString →. Bool) (x : BitString) (k : ℕ) (hk : k ≤ x.length) :
    ∀ s, s ∈ Nat.recOn (motive := fun _ => Part BitString) k (Part.some []) (fun n ih => do
      let s' ← ih
      let b ← r (x.take n)
      if b then Part.some (s' ++ [x.getD n false]) else Part.some s') ↔
    (∀ n < k, (r (x.take n)).Dom) ∧ s = selectedBits (partialRuleSet r) (x.take k) := by
  revert hk
  induction k
  · intro _ s
    change s ∈ Part.some [] ↔ _
    have h_sel : selectedBits (partialRuleSet r) [] = [] := by rfl
    simp only [Part.mem_some_iff, List.take_zero, h_sel]
    constructor
    · rintro rfl
      exact ⟨fun n hn => False.elim (Nat.not_lt_zero n hn), rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  · rename_i k ih
    intro hk s
    have hk_lt : k < x.length := hk
    have heq : (Nat.recOn (motive := fun _ => Part BitString) (k + 1) (Part.some []) (fun n ih => do
      let s' ← ih
      let b ← r (x.take n)
      if b then Part.some (s' ++ [x.getD n false]) else Part.some s')) = 
      (Nat.recOn (motive := fun _ => Part BitString) k (Part.some []) (fun n ih => do
        let s' ← ih
        let b ← r (x.take n)
        if b then Part.some (s' ++ [x.getD n false]) else Part.some s')).bind
      (fun s' => (r (x.take k)).bind (fun b => if b = true then
                                                 Part.some (s' ++ [x.getD k false]) else
                                                   Part.some s')) := rfl
    rw [heq]
    rw [Part.mem_bind_iff]
    simp only [Part.mem_bind_iff, ih (le_trans (Nat.le_succ _) hk)]
    constructor
    · rintro ⟨s', ⟨hs'dom, rfl⟩, b, hbdom, hs⟩
      have h_take_succ : x.take (k + 1) = x.take k ++ [x[k]'(hk_lt)] :=
          List.take_succ_eq_append_getElem hk_lt
      have h_getD : x.getD k false = x[k]'(hk_lt) := List.getD_eq_getElem x false hk_lt
      have hprefix : ∀ y, y <+: x.take k → (r y).Dom := by
        intro y hy
        have hle : y.length ≤ k := le_trans (List.IsPrefix.length_le hy) (List.length_take_le k x)
        have hyx : y <+: x := hy.trans (List.take_prefix k x)
        have hy_eq : y = x.take y.length := List.prefix_iff_eq_take.mp hyx
        rw [hy_eq]
        rcases lt_or_eq_of_le hle with hlt | heq2
        · exact hs'dom y.length hlt
        · rw [heq2]
          exact Part.dom_iff_mem.mpr ⟨b, hbdom⟩
      have hR : x.take k ∈ partialRuleSet r ↔ b = true := by
        change ((∀ y, y <+: x.take k → (r y).Dom) ∧ true ∈ r (x.take k)) ↔ b = true
        constructor
        · intro h
          exact Part.mem_unique hbdom h.2
        · intro heq2
          subst heq2
          exact ⟨hprefix, hbdom⟩
      constructor
      · intro n hn
        by_cases h : n = k
        · rw [h]; exact Part.dom_iff_mem.mpr ⟨b, hbdom⟩
        · exact hs'dom n (lt_of_le_of_ne (Nat.lt_succ_iff.mp hn) h)
      · rw [h_take_succ, selectedBits_append_singleton]
        by_cases hb : b = true
        · simp only [hb, ite_true] at hs
          rw [h_getD] at hs
          have hs_eq : s = selectedBits (partialRuleSet r) (x.take k) ++ [x[k]'(hk_lt)] :=
              Part.mem_some_iff.mp hs
          rw [ite_eq_left (hR.mpr hb)]
          exact hs_eq
        · simp only [hb] at hs
          have hs_eq : s = selectedBits (partialRuleSet r) (x.take k) := Part.mem_some_iff.mp hs
          have hnR : x.take k ∉ partialRuleSet r := by
            intro hR_true
            have hb_true : b = true := hR.mp hR_true
            exact hb hb_true
          rw [ite_eq_right hnR, List.append_nil]
          exact hs_eq
    · rintro ⟨hdom, hs⟩
      have h_take_succ : x.take (k + 1) = x.take k ++ [x[k]'(hk_lt)] :=
          List.take_succ_eq_append_getElem hk_lt
      have h_getD : x.getD k false = x[k]'(hk_lt) := List.getD_eq_getElem x false hk_lt
      use selectedBits (partialRuleSet r) (x.take k)
      constructor
      · constructor
        · intro n hn
          exact hdom n (lt_trans hn (Nat.lt_succ_self k))
        · rfl
      · have hbk : (r (x.take k)).Dom := hdom k (Nat.lt_succ_self k)
        use (r (x.take k)).get hbk
        constructor
        · exact Part.get_mem hbk
        · rw [h_take_succ, selectedBits_append_singleton] at hs
          have hs'dom : ∀ (n : ℕ), n < k → (r (List.take n x)).Dom :=
              fun n hn => hdom n (lt_trans hn (Nat.lt_succ_self k))
          have hbdom : (r (x.take k)).get hbk ∈ r (x.take k) := Part.get_mem hbk
          have hprefix : ∀ y, y <+: x.take k → (r y).Dom := by
            intro y hy
            have hle : y.length ≤ k := le_trans (List.IsPrefix.length_le hy) (List.length_take_le k
                x)
            have hyx : y <+: x := hy.trans (List.take_prefix k x)
            have hy_eq : y = x.take y.length := List.prefix_iff_eq_take.mp hyx
            rw [hy_eq]
            rcases lt_or_eq_of_le hle with hlt | heq2
            · exact hs'dom y.length hlt
            · rw [heq2]
              exact Part.dom_iff_mem.mpr ⟨_, hbdom⟩
          have hR : x.take k ∈ partialRuleSet r ↔ (r (x.take k)).get hbk = true := by
            change ((∀ y, y <+: x.take k → (r y).Dom) ∧ true ∈ r (x.take k)) ↔ (r (x.take k)).get
                hbk = true
            constructor
            · intro h
              exact Part.mem_unique hbdom h.2
            · intro heq2
              rw [heq2] at hbdom
              exact ⟨hprefix, hbdom⟩
          by_cases hR_true : x.take k ∈ partialRuleSet r
          · have hb_true : (r (x.take k)).get hbk = true := hR.mp hR_true
            simp only [hb_true, ite_true, ite_eq_left hR_true] at hs ⊢
            rw [h_getD]
            exact Part.mem_some_iff.mpr hs
          · have hb_false : ¬(r (x.take k)).get hbk = true := mt hR.mpr hR_true
            have hb_false2 : (r (x.take k)).get hbk = false := Bool.eq_false_of_ne_true hb_false
            simp only [hb_false2, ite_eq_right hR_true, List.append_nil] at hs ⊢
            exact Part.mem_some_iff.mpr hs

/-- Step 2 of the proof of `isMisesChurchDaleyRandom_of_selectStream_compose_eq`:
Characterize when composition returns true. -/
private lemma isMisesChurchDaleyRandom_of_selectStream_eval
    (r r' : BitString →. Bool) (y : BitString) :
    true ∈ isMisesChurchDaleyRandom_of_selectStream_compose r r' y ↔
    (∀ n < y.length, (r (y.take n)).Dom) ∧ true ∈ r y ∧ true ∈ r' (selectedBits (partialRuleSet r)
        y) := by
  have hvalue :
      selectedBits (partialRuleSet r) (y.take y.length) =
        selectedBits (partialRuleSet r) y :=
    congrArg (selectedBits (partialRuleSet r))
      (List.take_length (l := y))
  have hstage : ∀ s : BitString,
      s ∈ isMisesChurchDaleyRandom_of_selectStream_selPart r y ↔
      (∀ n < y.length, (r (y.take n)).Dom) ∧
        s = selectedBits (partialRuleSet r) (y.take y.length) := by
    intro s
    exact
      isMisesChurchDaleyRandom_of_selectStream_stage
        r y y.length (Nat.le_refl _) s
  unfold isMisesChurchDaleyRandom_of_selectStream_compose
  simp only [Part.mem_bind_iff, Part.bind_eq_bind]
  constructor
  · rintro ⟨s, hs, c, hc, ht⟩
    obtain ⟨hd, he⟩ := (hstage s).mp hs
    cases c with
    | false =>
        change true ∈ Part.some false at ht
        have hbad : true = false := Part.mem_some_iff.mp ht
        cases hbad
    | true =>
        change true ∈ r' s at ht
        have he' : s = selectedBits (partialRuleSet r) y :=
          he.trans hvalue
        have hp : (true ∈ r' s) =
            (true ∈ r' (selectedBits (partialRuleSet r) y)) :=
          congrArg (fun t : BitString => true ∈ r' t) he'
        exact ⟨hd, hc, Eq.mp hp ht⟩
  · rintro ⟨hd, hc, ht⟩
    refine ⟨selectedBits (partialRuleSet r) y,
      (hstage _).mpr ⟨hd, hvalue.symm⟩, true, hc, ?_⟩
    exact ht

/-- Step 3 of the proof of `isMisesChurchDaleyRandom_of_selectStream_compose_eq`:
Characterize the domain of composition. -/
private lemma isMisesChurchDaleyRandom_of_selectStream_dom
    (r r' : BitString →. Bool) (y : BitString) :
    (isMisesChurchDaleyRandom_of_selectStream_compose r r' y).Dom ↔
    (∀ n < y.length, (r (y.take n)).Dom) ∧ (r y).Dom ∧
    (true ∈ r y → (r' (selectedBits (partialRuleSet r) y)).Dom) := by
  unfold isMisesChurchDaleyRandom_of_selectStream_compose
  dsimp
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨b, hb⟩
    simp only [Part.mem_bind_iff] at hb
    rcases hb with ⟨s, hs, c, hc, hb2⟩
    have hs' : s ∈ isMisesChurchDaleyRandom_of_selectStream_selPart r y := hs
    have h_step1 : s ∈ isMisesChurchDaleyRandom_of_selectStream_selPart r y ↔ (∀ n < y.length,
        (r (y.take n)).Dom) ∧ s = selectedBits (partialRuleSet r) (y.take y.length) := by
      exact isMisesChurchDaleyRandom_of_selectStream_stage r y y.length
          (le_refl _) s
    rw [List.take_length] at h_step1
    rw [h_step1] at hs'
    rcases hs' with ⟨h_dom, rfl⟩
    refine ⟨h_dom, Part.dom_iff_mem.mpr ⟨c, hc⟩, ?_⟩
    intro hc_true
    have hc_eq_true : c = true := Part.mem_unique hc hc_true
    subst hc_eq_true
    exact Part.dom_iff_mem.mpr ⟨b, hb2⟩
  · rintro ⟨h_dom, h_c_dom, h_true⟩
    rcases Part.dom_iff_mem.mp h_c_dom with ⟨c, hc⟩
    have h_step1 : (selectedBits (partialRuleSet r) y) ∈
        isMisesChurchDaleyRandom_of_selectStream_selPart r y ↔ (∀ n < y.length,
        (r (y.take n)).Dom) ∧ (selectedBits (partialRuleSet r) y) = selectedBits (partialRuleSet r)
        (y.take y.length) := by
      exact isMisesChurchDaleyRandom_of_selectStream_stage r y y.length
          (le_refl _) (selectedBits (partialRuleSet r) y)
    rw [List.take_length] at h_step1
    have hs : (selectedBits (partialRuleSet r) y) ∈
        isMisesChurchDaleyRandom_of_selectStream_selPart r y := by
      rw [h_step1]
      exact ⟨h_dom, rfl⟩
    by_cases hc_eq : c = true
    · subst hc_eq
      have h_r'_dom := h_true hc
      rcases Part.dom_iff_mem.mp h_r'_dom with ⟨b, hb⟩
      use b
      simp only [Part.mem_bind_iff]
      use (selectedBits (partialRuleSet r) y), hs, true, hc
      exact hb
    · have hc_eq_false : c = false := Bool.eq_false_iff.mpr hc_eq
      subst hc_eq_false
      use false
      simp only [Part.mem_bind_iff]
      use (selectedBits (partialRuleSet r) y), hs, false, hc
      exact Part.mem_some_iff.mpr rfl




private lemma prefix_of_prefix_append_singleton {α : Type*} {x y : List α} {b : α}
    (h : x <+: y ++ [b]) (hlen : x.length ≤ y.length) : x <+: y := by
  rcases h with ⟨c, hc⟩
  have h1 : (x ++ c).take x.length = (y ++ [b]).take x.length := by rw [hc]
  rw [List.take_left] at h1
  have h2 : (y ++ [b]).take x.length = y.take x.length := by
    apply List.take_append_of_le_length hlen
  rw [h2] at h1
  have h3 : x = y.take x.length := h1
  exact List.prefix_iff_eq_take.mpr h3

open Classical in
/-- Step 4 of the proof of `isMisesChurchDaleyRandom_of_selectStream_compose_eq`:
Represent prefixes of the selected string. -/
private lemma isMisesChurchDaleyRandom_of_selectStream_prefix
    (r : BitString →. Bool) (x : BitString) (z : BitString) (hz : z <+: selectedBits
        (partialRuleSet r) x) :
    z = selectedBits (partialRuleSet r) x ∨ ∃ y, y <+: x ∧ y ∈ partialRuleSet r ∧ z = selectedBits
        (partialRuleSet r) y := by
  let R := partialRuleSet r
  change z = selectedBits R x ∨ ∃ y, y <+: x ∧ y ∈ R ∧ z = selectedBits R y
  change z <+: selectedBits R x at hz
  induction x using List.reverseRecOn generalizing z with
  | nil =>
    have h1 : selectedBits R [] = [] := rfl
    rw [h1] at hz ⊢
    left
    exact List.eq_nil_of_prefix_nil hz
  | append_singleton a b ih =>
    rw [selectedBits_append_singleton R a b] at hz ⊢
    by_cases ha : a ∈ R
    · have h_pos : (if a ∈ R then [b] else []) = [b] := ite_eq_left ha
      rw [h_pos] at hz ⊢
      have h_len : z.length ≤ (selectedBits R a ++ [b]).length := List.IsPrefix.length_le hz
      rw [List.length_append, List.length_singleton] at h_len
      rcases eq_or_lt_of_le h_len with h_eq | h_lt
      · left
        rcases hz with ⟨c, hc⟩
        have hzlen : z.length = (selectedBits R a).length + 1 := h_eq
        have hlen2 : (z ++ c).length = ((selectedBits R a) ++ [b]).length := by rw [hc]
        rw [List.length_append, hzlen, List.length_append, List.length_singleton] at hlen2
        have hc0 : c.length = 0 := by omega
        have cnil : c = [] := List.length_eq_zero_iff.mp hc0
        rw [cnil, List.append_nil] at hc
        exact hc
      · right
        have hz' : z <+: selectedBits R a := by
          have h1 : z.length ≤ (selectedBits R a).length := by omega
          exact prefix_of_prefix_append_singleton hz h1
        rcases ih z hz' with h1 | ⟨y, hy1, hy2, hy3⟩
        · use a
          refine ⟨List.prefix_append _ _, ha, h1⟩
        · use y
          refine ⟨List.IsPrefix.trans hy1 (List.prefix_append _ _), hy2, hy3⟩
    · have h_neg : (if a ∈ R then [b] else []) = [] := ite_eq_right ha
      rw [h_neg] at hz ⊢
      simp only [List.append_nil] at hz ⊢
      rcases ih z hz with h1 | ⟨y, hy1, hy2, hy3⟩
      · left
        exact h1
      · right
        use y
        refine ⟨List.IsPrefix.trans hy1 (List.prefix_append _ _), hy2, hy3⟩

/-- Step 5 of the proof of `isMisesChurchDaleyRandom_of_selectStream_compose_eq`:
Represent list prefixes by take. -/
private lemma isMisesChurchDaleyRandom_of_selectStream_compose_eq_prefix_iff_take
    (y x : BitString) : y <+: x ↔ ∃ n ≤ x.length, y = x.take n := by
  constructor
  · intro h
    exact ⟨y.length, List.IsPrefix.length_le h, List.prefix_iff_eq_take.mp h⟩
  · rintro ⟨n, _, rfl⟩
    exact List.take_prefix n x

/-- Step 6 of the proof of `isMisesChurchDaleyRandom_of_selectStream_compose_eq`:
Simplify nested takes. -/
private lemma isMisesChurchDaleyRandom_of_selectStream_compose_eq_take_take_eq (x : BitString)
    (m n : ℕ) (hm : m < n) (_hn : n ≤ x.length) :
    (x.take n).take m = x.take m := by
  rw [List.take_take]
  have hm_le : m ≤ n := le_of_lt hm
  rw [min_eq_left hm_le]

/-- Step 7 of the proof of `isMisesChurchDaleyRandom_of_selectStream_compose_eq`:
Compute the length of a bounded take. -/
private lemma isMisesChurchDaleyRandom_of_selectStream_compose_eq_take_length_le
    (x : BitString) (n : ℕ) (hn : n ≤ x.length) : (x.take n).length = n := by
  rw [List.length_take]
  exact min_eq_left hn

/-- Step 4 of the proof of `isMisesChurchDaleyRandom_of_selectStream`: The `compose` acts
as expected where it is defined. -/
private lemma isMisesChurchDaleyRandom_of_selectStream_compose_eq
    (r r' : BitString →. Bool) :
    partialRuleSet (isMisesChurchDaleyRandom_of_selectStream_compose r r') = 
      {x | x ∈ partialRuleSet r ∧ selectedBits (partialRuleSet r) x ∈ partialRuleSet r'} := by
  ext x
  simp only [partialRuleSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h_dom, h_true⟩
    have h2' : true ∈ isMisesChurchDaleyRandom_of_selectStream_compose r r' x := h_true
    rw [isMisesChurchDaleyRandom_of_selectStream_eval] at h2'
    rcases h2' with ⟨h2_1, h2_2, h2_3⟩
    constructor
    · constructor
      · intro y hy
        rcases (isMisesChurchDaleyRandom_of_selectStream_compose_eq_prefix_iff_take y x).mp hy
            with ⟨n, hn_le, rfl⟩
        by_cases hn : n = x.length
        · rw [hn, List.take_length]
          have h_x_dom : (isMisesChurchDaleyRandom_of_selectStream_compose r r' x).Dom :=
              Part.dom_iff_mem.mpr ⟨true, h_true⟩
          rw [isMisesChurchDaleyRandom_of_selectStream_dom] at h_x_dom
          exact h_x_dom.2.1
        · have hn_lt : n < x.length := lt_of_le_of_ne hn_le hn
          exact h2_1 n hn_lt
      · exact h2_2
    · constructor
      · intro z hz
        have h_z := isMisesChurchDaleyRandom_of_selectStream_prefix r x z hz
        rcases h_z with rfl | ⟨y, hy1, hy2, rfl⟩
        · have h_x_dom : (isMisesChurchDaleyRandom_of_selectStream_compose r r' x).Dom :=
            Part.dom_iff_mem.mpr ⟨true, h_true⟩
          rw [isMisesChurchDaleyRandom_of_selectStream_dom] at h_x_dom
          exact h_x_dom.2.2 h2_2
        · have hy_dom := h_dom y hy1
          rw [isMisesChurchDaleyRandom_of_selectStream_dom] at hy_dom
          exact hy_dom.2.2 hy2.2
      · exact h2_3
  · rintro ⟨⟨h1_dom, h1_true⟩, ⟨h2_dom, h2_true⟩⟩
    constructor
    · intro y hy
      rw [isMisesChurchDaleyRandom_of_selectStream_dom]
      rcases (isMisesChurchDaleyRandom_of_selectStream_compose_eq_prefix_iff_take y x).mp hy
          with ⟨n, hn_le, rfl⟩
      constructor
      · intro m hm
        rw [isMisesChurchDaleyRandom_of_selectStream_compose_eq_take_length_le x n hn_le] at hm
        rw [isMisesChurchDaleyRandom_of_selectStream_compose_eq_take_take_eq x m n hm hn_le]
        exact h1_dom (x.take m) (List.take_prefix m x)
      · constructor
        · exact h1_dom (x.take n) (List.take_prefix n x)
        · intro _hy_true
          have h_sel_pre : selectedBits (partialRuleSet r) (x.take n) <+: selectedBits
              (partialRuleSet r) x := by
            exact selectedBits_prefix (partialRuleSet r) (List.take_prefix n x)
          exact h2_dom (selectedBits (partialRuleSet r) (x.take n)) h_sel_pre
    · rw [isMisesChurchDaleyRandom_of_selectStream_eval]
      constructor
      · intro n hn
        exact h1_dom (x.take n) (List.take_prefix n x)
      · exact ⟨h1_true, h2_true⟩

private lemma bitstream_eq {T T' : Set BitString} (hT : IsStreamPrefixSet T)
    (hT' : IsStreamPrefixSet T') (h : T = T') : BitStream.ofPrefixSet T hT = BitStream.ofPrefixSet
    T' hT' := by
  subst h
  rfl

/-- Step 5 of the proof of `isMisesChurchDaleyRandom_of_selectStream`: The composition
selects the same sequence. -/
private lemma isMisesChurchDaleyRandom_of_selectStream_selectStream_compose
    (w : CantorSeq) (u : CantorSeq) (R R' : Set BitString)
    (hu : selectStream R w = .infinite u) :
    selectStream {x | x ∈ R ∧ selectedBits R x ∈ R'} w = selectStream R' u := by
  classical
  let R'' := {x | x ∈ R ∧ selectedBits R x ∈ R'}
  have h_sel_eq : ∀ x, selectedBits R'' x = selectedBits R' (selectedBits R x) := by
    intro x
    induction x using List.reverseRecOn
    · rfl
    · rename_i x b ih
      rw [selectedBits_append_singleton R'' x b]
      rw [selectedBits_append_singleton R x b]
      rw [ih]
      by_cases h : x ∈ R''
      · have hR : x ∈ R := h.1
        have hR' : selectedBits R x ∈ R' := h.2
        simp [h, hR, hR', selectedBits_append_singleton R' (selectedBits R x) b]
      · by_cases hR : x ∈ R
        · have hR' : selectedBits R x ∉ R' := fun h' => h ⟨hR, h'⟩
          simp [h, hR, hR', selectedBits_append_singleton R' (selectedBits R x) b]
        · simp [h, hR]
  
  have h_T_eq : chainPrefixSet (fun t => selectedBits R'' (cantorPrefix w t)) = 
                chainPrefixSet (fun s => selectedBits R' (cantorPrefix u s)) := by
    ext y
    simp only [chainPrefixSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      have hu_chain := selectChain_prefix R w
      have hT : IsStreamPrefixSet (chainPrefixSet (fun t => selectChain R w t)) := 
        isStreamPrefixSet_chainPrefixSet hu_chain
      have hc : ∀ s, selectChain R w s = cantorPrefix u (selectChain R w s).length := by
        intro s
        have hs_in : selectChain R w s ∈ chainPrefixSet (fun t => selectChain R w t) := by
          simp only [chainPrefixSet, Set.mem_ofPred_eq]
          use s
        have h_le : BitStream.finite (selectChain R w s) ≤ BitStream.ofPrefixSet _ hT := 
          (BitStream.finite_le_ofPrefixSet_iff hT _).mpr hs_in
        have h_eq : BitStream.ofPrefixSet _ hT = selectStream R w := rfl
        rw [h_eq, hu] at h_le
        exact (isCantorPrefix_iff_cantorPrefix_eq _ u |>.mp h_le).symm
      
      have hs : selectChain R w t = cantorPrefix u (selectChain R w t).length := hc t
      use (selectChain R w t).length
      have h_sel_w : selectedBits R'' (cantorPrefix w t) = selectedBits R' (selectChain R w t) := by
        change selectedBits R'' (cantorPrefix w t) = selectedBits R'
            (selectedBits R (cantorPrefix w t))
        rw [h_sel_eq]
      rw [h_sel_w] at ht
      rw [hs] at ht
      exact ht
    · rintro ⟨s, hs⟩
      let T := chainPrefixSet (selectChain R w)
      have hT : IsStreamPrefixSet T :=
        isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)
      have hsel : selectStream R w = BitStream.ofPrefixSet T hT := rfl
      have h_unbdd : ¬ ∃ M, ∀ x ∈ T, x.length ≤ M := by
        intro hb
        have hfinite : selectStream R w =
            .finite (Classical.choose (exists_greatest_of_bddAbove_length hT hb)) := by
          calc
            selectStream R w = BitStream.ofPrefixSet T hT := hsel
            _ = .finite (Classical.choose (exists_greatest_of_bddAbove_length hT hb)) := by
              simp only [BitStream.ofPrefixSet, dite_eq_left hb]
        rw [hu] at hfinite
        cases hfinite
      have h_ex : ∃ t, s ≤ (selectChain R w t).length := by
        obtain ⟨x, hx, h_len⟩ := exists_mem_length_gt h_unbdd s
        change x ∈ chainPrefixSet (selectChain R w) at hx
        simp only [chainPrefixSet, Set.mem_ofPred_eq] at hx
        obtain ⟨t, ht_prefix⟩ := hx
        use t
        have h1 := List.IsPrefix.length_le ht_prefix
        omega
      obtain ⟨t, ht_len⟩ := h_ex
      use t
      have h_sel_w : selectedBits R'' (cantorPrefix w t) = selectedBits R' (selectChain R w t) := by
        change selectedBits R'' (cantorPrefix w t) = selectedBits R'
            (selectedBits R (cantorPrefix w t))
        rw [h_sel_eq]
      rw [h_sel_w]
      have hc : ∀ s, selectChain R w s = cantorPrefix u (selectChain R w s).length := by
        intro s'
        have hs_in : selectChain R w s' ∈ T := by
          change selectChain R w s' ∈ chainPrefixSet (selectChain R w)
          simp only [chainPrefixSet, Set.mem_ofPred_eq]
          use s'
        have h_le : BitStream.finite (selectChain R w s') ≤ BitStream.ofPrefixSet T hT := 
          (BitStream.finite_le_ofPrefixSet_iff hT _).mpr hs_in
        rw [← hsel, hu] at h_le
        have h_pref2 : IsCantorPrefix (selectChain R w s') u := BitStream.finite_le_infinite_iff.mp
            h_le
        exact (isCantorPrefix_iff_cantorPrefix_eq _ u).mp h_pref2 |>.symm
      have hs' : selectChain R w t = cantorPrefix u (selectChain R w t).length := hc t
      rw [hs']
      
      have h_pref : cantorPrefix u s <+: cantorPrefix u (selectChain R w t).length := 
        cantorPrefix_mono u ht_len
      have h_sel_pref := selectedBits_prefix R' h_pref
      exact List.IsPrefix.trans hs h_sel_pref
      
  have hT2_chain := selectChain_prefix R' u
  have hT2 : IsStreamPrefixSet (chainPrefixSet (fun s => selectChain R' u s)) := 
    isStreamPrefixSet_chainPrefixSet hT2_chain
    
  have hT1_chain := selectChain_prefix R'' w
  have hT1 : IsStreamPrefixSet (chainPrefixSet (fun t => selectChain R'' w t)) := 
    isStreamPrefixSet_chainPrefixSet hT1_chain
    
  have h_streams : BitStream.ofPrefixSet _ hT1 = BitStream.ofPrefixSet _ hT2 := by
    apply bitstream_eq
    exact h_T_eq
  
  have h_left : selectStream R'' w = BitStream.ofPrefixSet _ hT1 := rfl
  have h_right : selectStream R' u = BitStream.ofPrefixSet _ hT2 := rfl
  rw [h_left, h_right]
  exact h_streams


/-- **SUV Problem 273, p. 287.**  A Church-Daley admissible rule applied to a Mises-Church-Daley
random sequence gives a finite or a Mises-Church-Daley random sequence. -/
theorem isMisesChurchDaleyRandom_of_selectStream {w : CantorSeq}
    (hw : IsMisesChurchDaleyRandom w) {r : BitString →. Bool} (hr : Partrec r) {u : CantorSeq}
    (hu : selectStream (partialRuleSet r) w = .infinite u) : IsMisesChurchDaleyRandom u := by
  intro r' hr'
  have h_comp_partrec := isMisesChurchDaleyRandom_of_selectStream_compose_partrec r r' hr hr'
  have h_eq := isMisesChurchDaleyRandom_of_selectStream_selectStream_compose w u
      (partialRuleSet r) (partialRuleSet r') hu
  have h_w := hw (isMisesChurchDaleyRandom_of_selectStream_compose r r') h_comp_partrec
  have h_eq2 := isMisesChurchDaleyRandom_of_selectStream_compose_eq r r'
  rw [h_eq2] at h_w
  rwa [← h_eq]

end Kolmogorov.FrequencyGames
