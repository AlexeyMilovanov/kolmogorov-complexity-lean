/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.Mirror

/-!
# The reply test on finite data

Comparison of formal sums `∑ ±2^{-k}`, the invariance of `ourReply` under changes of the values
and outcomes of a game away from the strings in play, floors of remaining budgets, and the reply
test evaluated on finite data.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-! #### Comparison of formal sums and the remaining bookkeeping -/

/-- The largest exponent of a formal sum. -/
def FSum.maxExp (l : FSum) : ℕ := l.foldr (fun p acc => max p.2 acc) 0

/-- `2^B` times the positive part of a formal sum. -/
def FSum.posScaled (B : ℕ) (l : FSum) : ℕ :=
  l.foldr (fun p acc => if p.1 = true then 2 ^ (B - p.2) + acc else acc) 0

/-- `2^B` times the negative part of a formal sum. -/
def FSum.negScaled (B : ℕ) (l : FSum) : ℕ :=
  l.foldr (fun p acc => if p.1 = true then acc else 2 ^ (B - p.2) + acc) 0

/-- The comparison `val l₁ < val l₂` of formal sums, computed in `ℕ` after scaling. -/
def fsLt (l₁ l₂ : FSum) : Bool :=
  decide (FSum.posScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₁ +
      FSum.negScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₂ <
    FSum.posScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₂ +
      FSum.negScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₁)

section

omit [Family]

/-- Every exponent occurring in the formal sum `l` is at most `FSum.maxExp l`. -/
theorem FSum.le_maxExp (l : FSum) : ∀ p ∈ l, p.2 ≤ FSum.maxExp l := by
  induction l with
  | nil => intro p hp; simp at hp
  | cons q l ih =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact le_max_left _ _
    · exact (ih p hp).trans (le_max_right _ _)

/-- If every exponent of the formal sum `l` is at most `B`, then `2 ^ B` times its value is the
difference of the natural numbers `FSum.posScaled B l` and `FSum.negScaled B l`. -/
theorem FSum.val_scaled (B : ℕ) (l : FSum) (hB : ∀ p ∈ l, p.2 ≤ B) :
    FSum.val l * 2 ^ B = (FSum.posScaled B l : ℝ) - FSum.negScaled B l := by
  induction l with
  | nil => simp [FSum.val, FSum.posScaled, FSum.negScaled]
  | cons p l ih =>
    obtain ⟨b, k⟩ := p
    have hk : k ≤ B := hB (b, k) (List.mem_cons_self ..)
    have ih' := ih (fun q hq => hB q (List.mem_cons_of_mem _ hq))
    have hpow : (2 : ℝ)⁻¹ ^ k * 2 ^ B = 2 ^ (B - k) := by
      rw [show (2 : ℝ) ^ B = 2 ^ (B - k) * 2 ^ k by rw [← pow_add, Nat.sub_add_cancel hk]]
      rw [← mul_assoc, mul_comm ((2 : ℝ)⁻¹ ^ k), mul_assoc, ← mul_pow,
        inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]
    have hv : FSum.val ((b, k) :: l) =
        (if b then (2 : ℝ)⁻¹ ^ k else -((2 : ℝ)⁻¹ ^ k)) + FSum.val l := by
      simp [FSum.val]
    have hP : FSum.posScaled B ((b, k) :: l) =
        if b = true then 2 ^ (B - k) + FSum.posScaled B l else FSum.posScaled B l := rfl
    have hN : FSum.negScaled B ((b, k) :: l) =
        if b = true then FSum.negScaled B l else 2 ^ (B - k) + FSum.negScaled B l := rfl
    rw [hv, add_mul, ih', hP, hN]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      push_cast
      rw [neg_mul, hpow]; ring
    · simp only [ite_true]
      push_cast
      rw [hpow]; ring

/-- The test `fsLt l₁ l₂` decides whether the value of the formal sum `l₁` is less than the
value of `l₂`. -/
theorem fsLt_spec (l₁ l₂ : FSum) : fsLt l₁ l₂ = decide (FSum.val l₁ < FSum.val l₂) := by
  have h1 := FSum.val_scaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₁
    (fun p hp => (FSum.le_maxExp l₁ p hp).trans (le_max_left _ _))
  have h2 := FSum.val_scaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₂
    (fun p hp => (FSum.le_maxExp l₂ p hp).trans (le_max_right _ _))
  have hB : (0 : ℝ) < 2 ^ (max (FSum.maxExp l₁) (FSum.maxExp l₂)) := by positivity
  unfold fsLt
  rw [decide_eq_decide]
  constructor
  · intro h
    have h' : ((FSum.posScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₁ +
        FSum.negScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₂ : ℕ) : ℝ) <
        ((FSum.posScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₂ +
        FSum.negScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₁ : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    refine lt_of_mul_lt_mul_right ?_ hB.le
    rw [h1, h2]; linarith
  · intro h
    have h' := mul_lt_mul_of_pos_right h hB
    rw [h1, h2] at h'
    have h'' : ((FSum.posScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₁ +
        FSum.negScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₂ : ℕ) : ℝ) <
        ((FSum.posScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₂ +
        FSum.negScaled (max (FSum.maxExp l₁) (FSum.maxExp l₂)) l₁ : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h''

/-- The largest exponent of a formal sum is a primitive recursive function of the sum. -/
theorem FSum.maxExp_primrec : Primrec FSum.maxExp := by
  have h := Primrec.list_foldr (σ := ℕ) (Primrec.id : Primrec fun l : FSum => l)
    (Primrec.const 0)
    ((Primrec.nat_max.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq fun l => rfl

/-- The scaled positive part `FSum.posScaled B l` is primitive recursive in the scale `B` and the
formal sum `l`. -/
theorem FSum.posScaled_primrec : Primrec₂ FSum.posScaled := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have h := Primrec.list_foldr (σ := ℕ) (Primrec.snd : Primrec fun a : ℕ × FSum => a.2)
    (Primrec.const 0)
    ((Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const true))
      (Primrec.nat_add.comp (hpow.comp (Primrec.const 2) (Primrec.nat_sub.comp
          (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq fun a => rfl

/-- The scaled negative part `FSum.negScaled B l` is primitive recursive in the scale `B` and the
formal sum `l`. -/
theorem FSum.negScaled_primrec : Primrec₂ FSum.negScaled := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have h := Primrec.list_foldr (σ := ℕ) (Primrec.snd : Primrec fun a : ℕ × FSum => a.2)
    (Primrec.const 0)
    ((Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const true))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.nat_add.comp (hpow.comp (Primrec.const 2) (Primrec.nat_sub.comp
          (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
        (Primrec.snd.comp Primrec.snd))).to₂)
  exact h.of_eq fun a => rfl

/-- The comparison `fsLt` of two formal sums is primitive recursive. -/
theorem fsLt_primrec : Primrec₂ fsLt := by
  have hB : Primrec fun p : FSum × FSum => max (FSum.maxExp p.1) (FSum.maxExp p.2) :=
    Primrec.nat_max.comp (FSum.maxExp_primrec.comp Primrec.fst)
      (FSum.maxExp_primrec.comp Primrec.snd)
  have h := Primrec.nat_lt.decide.comp
    (Primrec.nat_add.comp (FSum.posScaled_primrec.comp hB Primrec.fst)
      (FSum.negScaled_primrec.comp hB Primrec.snd))
    (Primrec.nat_add.comp (FSum.posScaled_primrec.comp hB Primrec.snd)
      (FSum.negScaled_primrec.comp hB Primrec.fst))
  exact h.of_eq fun p => rfl

/-! #### Congruence of `ourReply` -/

/-- Two games with the same strings in play and the same budget, whose flip costs agree on those
strings, have the same legal moves. -/
theorem legal_congr (d d' : GameData) (hX : d'.X = d.X) (hε : d'.ε = d.ε)
    (hf : ∀ z ∈ d.X, flipCost d' z = flipCost d z) (st : GState) (S' : Finset BitString) :
    LegalMove d' st S' ↔ LegalMove d st S' := by
  have hm : S' ⊆ d.X → moveCost d' st.S S' = moveCost d st.S S' := fun hS' =>
    Finset.sum_congr rfl fun z hz => hf z (hS' (Finset.sdiff_subset hz))
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hX] at h2
    refine ⟨h1, h2, ?_⟩
    rw [hm h2, hε] at h3
    exact h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, hX ▸ h2, ?_⟩
    rw [hm h2, hε]
    exact h3

/-- Two games whose flip costs agree on the strings in play lead to the same state after a move to
a set `S'` of strings in play. -/
theorem applyMove_congr (d d' : GameData) (hf : ∀ z ∈ d.X, flipCost d' z = flipCost d z)
    (st : GState) (S' : Finset BitString) (hS' : S' ⊆ d.X) :
    applyMove d' st S' = applyMove d st S' := by
  have hm : moveCost d' st.S S' = moveCost d st.S S' :=
    Finset.sum_congr rfl fun z hz => hf z (hS' (Finset.sdiff_subset hz))
  unfold applyMove
  rw [hm]

/-- `SafeYes` transfers between two games with the same strings in play and the same budget whose
flip costs agree on those strings and whose outcomes agree on the positions inside them: if
`SafeYes d st` holds at a position `st.S` inside the strings in play, then so does
`SafeYes d' st`. -/
theorem safeYes_congr (d d' : GameData) (hX : d'.X = d.X) (hε : d'.ε = d.ε)
    (hf : ∀ z ∈ d.X, flipCost d' z = flipCost d z)
    (hout : ∀ S, S ⊆ d.X → d'.outcome S = d.outcome S) (st : GState) (h : SafeYes d st) :
    st.S ⊆ d.X → SafeYes d' st := by
  induction h with
  | intro st reply hout' hlegal hsafe ih =>
    intro hSX
    refine SafeYes.intro st reply (by rw [hout _ hSX]; exact hout') (fun S' hL hne => ?_)
      (fun S' hL hne => ?_)
    · have hL' := (legal_congr d d' hX hε hf st S').1 hL
      have h2 := hlegal S' hL' hne
      rw [applyMove_congr d d' hf st S' hL'.2.1]
      exact (legal_congr d d' hX hε hf _ _).2 h2
    · have hL' := (legal_congr d d' hX hε hf st S').1 hL
      have h2 := hlegal S' hL' hne
      rw [applyMove_congr d d' hf st S' hL'.2.1, applyMove_congr d d' hf _ _ h2.2.1]
      exact ih S' hL' hne h2.2.1

/-- `SafeNo` transfers between two games with the same strings in play and the same budget whose
flip costs agree on those strings and whose outcomes agree on the positions inside them: if
`SafeNo d st` holds at a position `st.S` inside the strings in play, then so does
`SafeNo d' st`. -/
theorem safeNo_congr (d d' : GameData) (hX : d'.X = d.X) (hε : d'.ε = d.ε)
    (hf : ∀ z ∈ d.X, flipCost d' z = flipCost d z)
    (hout : ∀ S, S ⊆ d.X → d'.outcome S = d.outcome S) (st : GState) (h : SafeNo d st) :
    st.S ⊆ d.X → SafeNo d' st := by
  induction h with
  | intro st reply hout' hlegal hsafe ih =>
    intro hSX
    refine SafeNo.intro st reply (by rw [hout _ hSX]; exact hout') (fun S' hL hne => ?_)
      (fun S' hL hne => ?_)
    · have hL' := (legal_congr d d' hX hε hf st S').1 hL
      have h2 := hlegal S' hL' hne
      rw [applyMove_congr d d' hf st S' hL'.2.1]
      exact (legal_congr d d' hX hε hf _ _).2 h2
    · have hL' := (legal_congr d d' hX hε hf st S').1 hL
      have h2 := hlegal S' hL' hne
      rw [applyMove_congr d d' hf st S' hL'.2.1, applyMove_congr d d' hf _ _ h2.2.1]
      exact ih S' hL' hne h2.2.1

/-- Replacing the values `h₀` and the verdicts `outcome` of a game by functions that agree with
them on the strings in play, respectively on the positions inside them, does not change
`ourReply`. -/
theorem ourReply_congr (d : GameData) (h₀' : BitString → ℕ)
    (outcome' : Finset BitString → Bool) (hh : ∀ z ∈ d.X, h₀' z = d.h₀ z)
    (hout : ∀ S, S ⊆ d.X → outcome' S = d.outcome S) (we : Bool) (st : GState) :
    ourReply { d with h₀ := h₀', outcome := outcome' } we st = ourReply d we st := by
  classical
  generalize hd' : ({ d with h₀ := h₀', outcome := outcome' } : GameData) = d'
  obtain ⟨hX, hε, hh, hout⟩ :
      d'.X = d.X ∧ d'.ε = d.ε ∧ (∀ z ∈ d.X, d'.h₀ z = d.h₀ z) ∧
        ∀ S, S ⊆ d.X → d'.outcome S = d.outcome S := by
    subst hd'
    exact ⟨rfl, rfl, hh, hout⟩
  have hf : ∀ z ∈ d.X, flipCost d' z = flipCost d z := fun z hz => by
    unfold flipCost; rw [hh z hz]
  have hf' : ∀ z ∈ d'.X, flipCost d z = flipCost d' z := fun z hz => (hf z (hX ▸ hz)).symm
  have hout' : ∀ S, S ⊆ d'.X → d.outcome S = d'.outcome S := fun S hS =>
    (hout S (hX ▸ hS)).symm
  have hsafe : ∀ R, LegalMove d st R →
      (SafeFor d' we (applyMove d' st R) ↔ SafeFor d we (applyMove d st R)) := by
    intro R hR
    rw [applyMove_congr d d' hf st R hR.2.1]
    have hSX : (applyMove d st R).S ⊆ d.X := hR.2.1
    have hSX' : (applyMove d st R).S ⊆ d'.X := hX ▸ hSX
    unfold SafeFor
    cases we
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨fun h => safeNo_congr d' d hX.symm hε.symm hf' hout' _ h hSX',
        fun h => safeNo_congr d d' hX hε hf hout _ h hSX⟩
    · simp only [ite_true]
      exact ⟨fun h => safeYes_congr d' d hX.symm hε.symm hf' hout' _ h hSX',
        fun h => safeYes_congr d d' hX hε hf hout _ h hSX⟩
  have hP : ∀ R, (LegalMove d' st R ∧ SafeFor d' we (applyMove d' st R)) ↔
      (LegalMove d st R ∧ SafeFor d we (applyMove d st R)) := by
    intro R
    rw [legal_congr d d' hX hε hf st R]
    exact and_congr_right fun hL => hsafe R hL
  unfold ourReply
  by_cases h : ∃ k : ℕ, LegalMove d st
      (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S) ∧
      SafeFor d we (applyMove d st
        (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S))
  · have h' : ∃ k : ℕ, LegalMove d' st
        (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S) ∧
        SafeFor d' we (applyMove d' st
          (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S)) := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, (hP _).2 hk⟩
    rw [dite_eq_left h', dite_eq_left h]
    have hfind : Nat.find h' = Nat.find h := by
      rw [Nat.find_eq_iff]
      exact ⟨(hP _).2 (Nat.find_spec h), fun n hn hn' => Nat.find_min h hn ((hP _).1 hn')⟩
    rw [hfind]
  · have h' : ¬ ∃ k : ℕ, LegalMove d' st
        (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S) ∧
        SafeFor d' we (applyMove d' st
          (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.S)) := by
      rintro ⟨k, hk⟩
      exact h ⟨k, (hP _).1 hk⟩
    rw [dite_eq_right h', dite_eq_right h]

end

/-! #### Floors of remaining budgets -/

/-- `k` fits into the optional budget `o`. -/
def fitsO (o : Option ℕ) (k : ℕ) : Bool :=
  match o with
  | none => false
  | some E => decide (k ≤ E)

/-- The optional budget `o` diminished by `k`. -/
def subOC (o : Option ℕ) (k : ℕ) : Option ℕ :=
  match o with
  | none => none
  | some E => if k ≤ E then some (E - k) else none

omit [Family] in
/-- If the optional budget `o` is the floor of the real number `r`, then `k` fits into `o` exactly
when `(k : ℝ) ≤ r`. -/
theorem fitsO_iff {r : ℝ} {o : Option ℕ} (ho : IsFloorO r o) (k : ℕ) :
    fitsO o k = true ↔ (k : ℝ) ≤ r := by
  rw [ho k]
  cases o with
  | none => simp [fitsO]
  | some E => simp [fitsO]

omit [Family] in
/-- If the optional budget `o` is the floor of `r`, then `subOC o k` is the floor of `r - k`. -/
theorem isFloorO_subOC {r : ℝ} {o : Option ℕ} (ho : IsFloorO r o) (k : ℕ) :
    IsFloorO (r - k) (subOC o k) := by
  intro j
  have h1 := ho (j + k)
  push_cast at h1
  have h2 : ((j : ℝ) ≤ r - k) ↔ ((j : ℝ) + k ≤ r) := by
    constructor <;> intro h <;> linarith
  rw [h2, h1]
  cases o with
  | none =>
    constructor
    · rintro ⟨E', hE', -⟩; cases hE'
    · rintro ⟨E', hE', -⟩; cases hE'
  | some E =>
    constructor
    · rintro ⟨E', hE', hle⟩
      cases hE'
      refine ⟨E - k, ?_, by omega⟩
      change (if k ≤ E then some (E - k) else none) = some (E - k)
      rw [ite_eq_left (by omega)]
    · rintro ⟨E', hE', hle⟩
      change (if k ≤ E then some (E - k) else none) = some E' at hE'
      split_ifs at hE' with hk
      cases hE'
      exact ⟨E, rfl, by omega⟩

/-- The floor of `(2^{-m} - val a) * 2^N` as an optional natural. -/
def floorO (m N : ℕ) (a : FSum) : Option ℕ :=
  if FSum.posScaled (max (max N m) (FSum.maxExp a)) a ≤
      2 ^ (max (max N m) (FSum.maxExp a) - m) + FSum.negScaled (max (max N m) (FSum.maxExp a)) a
  then some ((2 ^ (max (max N m) (FSum.maxExp a) - m) +
      FSum.negScaled (max (max N m) (FSum.maxExp a)) a -
      FSum.posScaled (max (max N m) (FSum.maxExp a)) a) / 2 ^ (max (max N m) (FSum.maxExp a) - N))
  else none

omit [Family] in
/-- `floorO m N a` is the floor of `(2^{-m} - val a) * 2^N` in the sense of `IsFloorO`. -/
theorem floorO_spec (m N : ℕ) (a : FSum) :
    IsFloorO (((2 : ℝ)⁻¹ ^ m - FSum.val a) * 2 ^ N) (floorO m N a) := by
  set B := max (max N m) (FSum.maxExp a) with hBdef
  have hNB : N ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hmB : m ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hval := FSum.val_scaled B a (fun p hp => (FSum.le_maxExp a p hp).trans (le_max_right _ _))
  have hpm : (2 : ℝ)⁻¹ ^ m * 2 ^ B = 2 ^ (B - m) := by
    rw [show (2 : ℝ) ^ B = 2 ^ (B - m) * 2 ^ m by rw [← pow_add, Nat.sub_add_cancel hmB]]
    rw [← mul_assoc, mul_comm ((2 : ℝ)⁻¹ ^ m), mul_assoc, ← mul_pow,
      inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]
  have hNs : (2 : ℝ) ^ N * 2 ^ (B - N) = 2 ^ B := by
    rw [← pow_add, Nat.add_sub_cancel' hNB]
  have hpos : (0 : ℝ) < 2 ^ (B - N) := by positivity
  have hkey : ((2 : ℝ)⁻¹ ^ m - FSum.val a) * 2 ^ N * 2 ^ (B - N) =
      (2 : ℝ) ^ (B - m) + FSum.negScaled B a - FSum.posScaled B a := by
    rw [mul_assoc, hNs, sub_mul, hpm, hval]; ring
  intro k
  have hk : ((k : ℝ) ≤ ((2 : ℝ)⁻¹ ^ m - FSum.val a) * 2 ^ N) ↔
      ((k : ℝ) * 2 ^ (B - N) ≤
        (2 : ℝ) ^ (B - m) + FSum.negScaled B a - FSum.posScaled B a) := by
    rw [← hkey]
    exact (mul_le_mul_iff_of_pos_right hpos).symm
  rw [hk]
  unfold floorO
  rw [← hBdef]
  split_ifs with hle
  · have hcast : ((2 : ℝ) ^ (B - m) + FSum.negScaled B a - FSum.posScaled B a) =
        ((2 ^ (B - m) + FSum.negScaled B a - FSum.posScaled B a : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [hcast]
    constructor
    · intro h
      refine ⟨_, rfl, ?_⟩
      rw [Nat.le_div_iff_mul_le (by positivity)]
      exact_mod_cast h
    · rintro ⟨E, hE, hkE⟩
      cases hE
      rw [Nat.le_div_iff_mul_le (by positivity)] at hkE
      exact_mod_cast hkE
  · constructor
    · intro h
      exfalso
      have h0 : (0 : ℝ) ≤ (k : ℝ) * 2 ^ (B - N) := by positivity
      have hlt : (2 : ℝ) ^ (B - m) + FSum.negScaled B a < FSum.posScaled B a := by
        exact_mod_cast (not_le.1 hle)
      linarith
    · rintro ⟨E, hE, -⟩
      cases hE

omit [Family] in
/-- The floor `floorO m N a` is a primitive recursive function of `m`, `N` and the formal sum
`a`. -/
theorem floorO_primrec : Primrec fun p : ℕ × ℕ × FSum => floorO p.1 p.2.1 p.2.2 := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hB : Primrec fun p : ℕ × ℕ × FSum => max (max p.2.1 p.1) (FSum.maxExp p.2.2) :=
    Primrec.nat_max.comp (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (FSum.maxExp_primrec.comp (Primrec.snd.comp Primrec.snd))
  have hP : Primrec fun p : ℕ × ℕ × FSum =>
      FSum.posScaled (max (max p.2.1 p.1) (FSum.maxExp p.2.2)) p.2.2 :=
    FSum.posScaled_primrec.comp hB (Primrec.snd.comp Primrec.snd)
  have hQ : Primrec fun p : ℕ × ℕ × FSum =>
      FSum.negScaled (max (max p.2.1 p.1) (FSum.maxExp p.2.2)) p.2.2 :=
    FSum.negScaled_primrec.comp hB (Primrec.snd.comp Primrec.snd)
  have hT : Primrec fun p : ℕ × ℕ × FSum =>
      2 ^ (max (max p.2.1 p.1) (FSum.maxExp p.2.2) - p.1) +
        FSum.negScaled (max (max p.2.1 p.1) (FSum.maxExp p.2.2)) p.2.2 :=
    Primrec.nat_add.comp (hpow.comp (Primrec.const 2) (Primrec.nat_sub.comp hB Primrec.fst)) hQ
  have hD : Primrec fun p : ℕ × ℕ × FSum =>
      2 ^ (max (max p.2.1 p.1) (FSum.maxExp p.2.2) - p.2.1) :=
    hpow.comp (Primrec.const 2) (Primrec.nat_sub.comp hB (Primrec.fst.comp Primrec.snd))
  have h := Primrec.ite (Primrec.nat_le.comp hP hT)
    (Primrec.option_some.comp (Primrec.nat_div.comp (Primrec.nat_sub.comp hT hP) hD))
    (Primrec.const none)
  exact h.of_eq fun p => rfl

/-! #### The reply test on finite data -/

/-- The floor of the remaining YES budget. -/
def EYC (G : GD) (st : GStC) : Option ℕ := floorO G.bud G.N st.2.1

/-- The floor of the remaining NO budget. -/
def ENC (G : GD) (st : GStC) : Option ℕ := floorO G.bud G.N st.2.2.1

/-- The scaled cost of the move to `L`. -/
def mcC (G : GD) (st : GStC) (L : List BitString) : ℕ := G.mc st.1 (dedupL L)

/-- The finite state after the move to `L`. -/
def afterC (G : GD) (st : GStC) (L : List BitString) : GSt :=
  (dedupL L, if st.2.2.2 = true then subOC (EYC G st) (mcC G st L) else EYC G st,
    if st.2.2.2 = true then ENC G st else subOC (ENC G st) (mcC G st L), !st.2.2.2)

/-- The legality test of the move to `L`. -/
def legalTest (G : GD) (st : GStC) (L : List BitString) : Bool :=
  subB st.1 L && subB L G.X &&
    fitsO (if st.2.2.2 = true then EYC G st else ENC G st) (mcC G st L)

/-- The safety test after the move to `L`. -/
def safeTest (G : GD) (we : Bool) (st : GStC) (L : List BitString) : Bool :=
  if we = true then safeYesC G (afterC G st L) else safeNoC G (afterC G st L)

section

omit [Family]

/-- If `o` is the floor of the scaled remaining budget `(2^{-bud} - α) * 2^N` of the game `G`, then
`k` fits into `o` exactly when spending a further `k / 2^N` keeps the score `α` within the budget
`G.game.ε`. -/
theorem fit_iff (G : GD) (α : ℝ) (o : Option ℕ)
    (ho : IsFloorO (((2 : ℝ)⁻¹ ^ G.bud - α) * 2 ^ G.N) o) (k : ℕ) :
    fitsO o k = true ↔ α + (k : ℝ) / 2 ^ G.N ≤ G.game.ε := by
  rw [fitsO_iff ho, show G.game.ε = (2 : ℝ)⁻¹ ^ G.bud from rfl, ← le_sub_iff_add_le',
    div_le_iff₀ (by positivity)]

/-- For a list `L` of strings in play, the cost of the move from the position `st.1` to `L` in the
game `G.game` is the scaled cost `mcC G st L` divided by `2^N`. -/
theorem mcC_cost (G : GD) (st : GStC) (L : List BitString) (hLX : ∀ z ∈ L, z ∈ G.X) :
    moveCost G.game st.1.toFinset L.toFinset = (mcC G st L : ℝ) / 2 ^ G.N := by
  have hdL : (dedupL L).toFinset = L.toFinset := by ext z; simp [mem_dedupL]
  rw [← hdL]
  exact G.moveCost_eq st.1 (dedupL L) (nodup_dedupL L)
    (fun z hz => hLX z ((mem_dedupL L z).1 hz))

/-- The finite test `legalTest G st L` holds iff the move to `L` is legal in the game `G.game` at
the state `st.toG`. -/
theorem legalTest_iff (G : GD) (st : GStC) (L : List BitString) :
    legalTest G st L = true ↔ LegalMove G.game st.toG L.toFinset := by
  obtain ⟨S, a, b, t⟩ := st
  have hS : S.toFinset ⊆ L.toFinset ↔ ∀ z ∈ S, z ∈ L := by simp [Finset.subset_iff]
  have hX : L.toFinset ⊆ G.game.X ↔ ∀ z ∈ L, z ∈ G.X := by
    change L.toFinset ⊆ G.X.toFinset ↔ _
    simp [Finset.subset_iff]
  unfold legalTest
  simp only [Bool.and_eq_true, subB_iff]
  change _ ↔ (S.toFinset ⊆ L.toFinset ∧ L.toFinset ⊆ G.game.X ∧
    (if t = true then FSum.val a + moveCost G.game S.toFinset L.toFinset ≤ G.game.ε
      else FSum.val b + moveCost G.game S.toFinset L.toFinset ≤ G.game.ε))
  rw [hS, hX]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [mcC_cost G (S, a, b, t) L h2]
    cases t
    · simp only [Bool.false_eq_true, ite_false] at h3 ⊢
      exact (fit_iff G _ _ (floorO_spec _ _ _) _).1 h3
    · simp only [ite_true] at h3 ⊢
      exact (fit_iff G _ _ (floorO_spec _ _ _) _).1 h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    rw [mcC_cost G (S, a, b, t) L h2] at h3
    cases t
    · simp only [Bool.false_eq_true, ite_false] at h3 ⊢
      exact (fit_iff G _ _ (floorO_spec _ _ _) _).2 h3
    · simp only [ite_true] at h3 ⊢
      exact (fit_iff G _ _ (floorO_spec _ _ _) _).2 h3

/-- For a list `L` of strings in play, the finite test `safeTest G we st L` holds iff the position
reached by the move to `L` is safe for the side `we` in the game `G.game`. -/
theorem safeTest_iff (G : GD) (we : Bool) (st : GStC) (L : List BitString)
    (hLX : ∀ z ∈ L, z ∈ G.X) :
    safeTest G we st L = true ↔ SafeFor G.game we (applyMove G.game st.toG L.toFinset) := by
  obtain ⟨S, a, b, t⟩ := st
  have hdL : (dedupL L).toFinset = L.toFinset := by ext z; simp [mem_dedupL]
  have hdX : ∀ z ∈ dedupL L, z ∈ G.X := fun z hz => hLX z ((mem_dedupL L z).1 hz)
  have hmc := mcC_cost G (S, a, b, t) L hLX
  have hsub : ∀ (α : ℝ) (o : Option ℕ),
      IsFloorO (((2 : ℝ)⁻¹ ^ G.bud - α) * 2 ^ G.N) o →
      IsFloorO ((G.game.ε - (α + (mcC G (S, a, b, t) L : ℝ) / 2 ^ G.N)) * 2 ^ G.N)
        (subOC o (mcC G (S, a, b, t) L)) := by
    intro α o ho
    have h := isFloorO_subOC ho (mcC G (S, a, b, t) L)
    have he : (G.game.ε - (α + (mcC G (S, a, b, t) L : ℝ) / 2 ^ G.N)) * 2 ^ G.N =
        ((2 : ℝ)⁻¹ ^ G.bud - α) * 2 ^ G.N - (mcC G (S, a, b, t) L : ℝ) := by
      change ((2 : ℝ)⁻¹ ^ G.bud - (α + (mcC G (S, a, b, t) L : ℝ) / 2 ^ G.N)) * 2 ^ G.N = _
      field_simp
      ring
    rw [he]
    exact h
  have happ : applyMove G.game (GStC.toG (S, a, b, t)) L.toFinset =
      ⟨(dedupL L).toFinset,
        if t = true then FSum.val a + (mcC G (S, a, b, t) L : ℝ) / 2 ^ G.N else FSum.val a,
        if t = true then FSum.val b else FSum.val b + (mcC G (S, a, b, t) L : ℝ) / 2 ^ G.N,
        !t⟩ := by
    rw [hdL, ← hmc]
    rfl
  rw [happ]
  unfold safeTest afterC SafeFor
  cases t <;> cases we
  · simp only [Bool.false_eq_true, ite_false, Bool.not_false]
    exact safeNoC_spec G (dedupL L) _ _ true _ _ hdX (floorO_spec _ _ _)
      (hsub _ _ (floorO_spec _ _ _))
  · simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false]
    exact safeYesC_spec G (dedupL L) _ _ true _ _ hdX (floorO_spec _ _ _)
      (hsub _ _ (floorO_spec _ _ _))
  · simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_true]
    exact safeNoC_spec G (dedupL L) _ _ false _ _ hdX (hsub _ _ (floorO_spec _ _ _))
      (floorO_spec _ _ _)
  · simp only [ite_true, Bool.not_true]
    exact safeYesC_spec G (dedupL L) _ _ false _ _ hdX (hsub _ _ (floorO_spec _ _ _))
      (floorO_spec _ _ _)

end

/-- The combined test of the move to `L`. -/
def replyTest (G : GD) (we : Bool) (st : GStC) (L : List BitString) : Bool :=
  legalTest G st L && safeTest G we st L

omit [Family] in
/-- The combined test `replyTest G we st L` holds iff the move to `L` is legal in the game
`G.game` at the state `st.toG` and the position it leads to is safe for the side `we`. -/
theorem replyTest_iff (G : GD) (we : Bool) (st : GStC) (L : List BitString) :
    replyTest G we st L = true ↔
      LegalMove G.game st.toG L.toFinset ∧
        SafeFor G.game we (applyMove G.game st.toG L.toFinset) := by
  unfold replyTest
  rw [Bool.and_eq_true, legalTest_iff]
  have hX : LegalMove G.game st.toG L.toFinset → ∀ z ∈ L, z ∈ G.X := fun hL z hz =>
    List.mem_toFinset.1 (hL.2.1 (List.mem_toFinset.2 hz))
  constructor
  · rintro ⟨hL, hs⟩
    exact ⟨hL, (safeTest_iff G we st L (hX hL)).1 hs⟩
  · rintro ⟨hL, hs⟩
    exact ⟨hL, (safeTest_iff G we st L (hX hL)).2 hs⟩

/-- The candidate move of code `k`: the decoded list, or the position `S`. -/
def candC (S : List BitString) (k : ℕ) : List BitString :=
  (Encodable.decode k : Option (List BitString)).getD S

omit [Family] in
/-- The candidate `candC S k`, read as a finite set, is the set decoded from `k`, or the set of
the strings of `S` if `k` is not the code of a list. -/
theorem candC_toFinset (S : List BitString) (k : ℕ) :
    (candC S k).toFinset =
      ((Encodable.decode k : Option (List BitString)).map List.toFinset).getD S.toFinset := by
  unfold candC
  cases (Encodable.decode k : Option (List BitString)) <;> rfl

/-- The search bound: the largest code of a candidate sub-list of the strings in play. -/
def replyBound (G : GD) : ℕ := (allSub G.Xd).foldr (fun R acc => max (Encodable.encode R) acc) 0

omit [Family] in
/-- The code of a member `R` of a list of lists is at most the largest code of its members. -/
theorem encode_le_foldr_max (l : List (List BitString)) (R : List BitString) (hR : R ∈ l) :
    Encodable.encode R ≤ l.foldr (fun R acc => max (Encodable.encode R) acc) 0 := by
  induction l with
  | nil => simp at hR
  | cons a l ih =>
    rcases List.mem_cons.1 hR with rfl | hR
    · exact le_max_left _ _
    · exact (ih hR).trans (le_max_right _ _)

/-- The least `k < n` with `p k`, starting the search from the value `init`. -/
def leastAux (p : ℕ → Bool) (n init : ℕ) : ℕ :=
  (List.range n).foldr (fun k acc => if p k = true then k else acc) init

omit [Family] in
/-- `leastAux p n init` is the least `j < n` with `p j = true` if there is one, and `init`
otherwise. -/
theorem leastAux_eq (p : ℕ → Bool) (n init : ℕ) :
    leastAux p n init = if h : ∃ j, j < n ∧ p j = true then Nat.find h else init := by
  induction n generalizing init with
  | zero =>
    have h : ¬ ∃ j, j < 0 ∧ p j = true := by rintro ⟨j, hj, -⟩; omega
    rw [dite_eq_right h]; rfl
  | succ n ih =>
    have hstep : leastAux p (n + 1) init = leastAux p n (if p n = true then n else init) := by
      unfold leastAux
      rw [List.range_succ, List.foldr_append]
      rfl
    rw [hstep, ih]
    by_cases h : ∃ j, j < n ∧ p j = true
    · have h' : ∃ j, j < n + 1 ∧ p j = true := by
        obtain ⟨j, hj, hp⟩ := h; exact ⟨j, by omega, hp⟩
      rw [dite_eq_left h, dite_eq_left h']
      apply le_antisymm
      · exact Nat.find_min' h ⟨by
          have := Nat.find_min' h' ⟨(Nat.find_spec h).1.trans (by omega), (Nat.find_spec h).2⟩
          have h2 := (Nat.find_spec h).1
          by_contra hc
          have h3 : Nat.find h' = n := by
            have := (Nat.find_spec h').1; omega
          have h4 := (Nat.find_spec h').2
          rw [h3] at h4
          omega, (Nat.find_spec h').2⟩
      · exact Nat.find_min' h' ⟨(Nat.find_spec h).1.trans (by omega), (Nat.find_spec h).2⟩
    · rw [dite_eq_right h]
      by_cases hn : p n = true
      · have h' : ∃ j, j < n + 1 ∧ p j = true := ⟨n, by omega, hn⟩
        rw [ite_eq_left hn, dite_eq_left h']
        apply le_antisymm
        · by_contra hc
          push Not at hc
          exact h ⟨Nat.find h', hc, (Nat.find_spec h').2⟩
        · exact Nat.find_min' h' ⟨by omega, hn⟩
      · have h' : ¬ ∃ j, j < n + 1 ∧ p j = true := by
          rintro ⟨j, hj, hp⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact h ⟨j, hj, hp⟩
          · exact hn hp
        rw [ite_eq_right hn, dite_eq_right h']

/-- The least code `≤ replyBound` passing the test (or `replyBound + 1`). -/
def replyK (G : GD) (we : Bool) (st : GStC) : ℕ :=
  leastAux (fun k => replyTest G we st (candC st.1 k)) (replyBound G + 1) (replyBound G + 1)

/-- Our reply on finite data. -/
def replyFn (G : GD) (we : Bool) (st : GStC) : List BitString :=
  if replyK G we st < replyBound G + 1 then sortStr (candC st.1 (replyK G we st)).toFinset
  else sortStr st.1.toFinset

section

omit [Family]

/-- The finite computation `replyFn G we st` returns `ourReply` of the game `G.game` at the state
`st.toG`, as the canonical list `sortStr`. -/
theorem replyFn_spec (G : GD) (we : Bool) (st : GStC) :
    replyFn G we st = sortStr (ourReply G.game we st.toG) := by
  classical
  have hP : ∀ k, replyTest G we st (candC st.1 k) = true ↔
      (LegalMove G.game st.toG
        (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.toG.S) ∧
      SafeFor G.game we (applyMove G.game st.toG
        (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.toG.S))) := by
    intro k
    rw [replyTest_iff, candC_toFinset]
    rfl
  unfold replyFn replyK
  rw [leastAux_eq]
  unfold ourReply
  by_cases h : ∃ k : ℕ, LegalMove G.game st.toG
      (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.toG.S) ∧
      SafeFor G.game we (applyMove G.game st.toG
        (((Encodable.decode k : Option (List BitString)).map List.toFinset).getD st.toG.S))
  · have hX : ∀ z ∈ ((Encodable.decode (Nat.find h) : Option (List BitString)).map
        List.toFinset).getD st.toG.S, z ∈ G.Xd := fun z hz =>
      (G.mem_Xd z).2 (List.mem_toFinset.1 ((Nat.find_spec h).1.2.1 hz))
    obtain ⟨R', hR', hR'eq⟩ := exists_allSub G.Xd _ hX
    have hb : Nat.find h ≤ replyBound G := by
      refine (Nat.find_min' h ?_).trans (encode_le_foldr_max _ R' hR')
      simp only [Encodable.encodek, Option.map_some, Option.getD_some, hR'eq]
      exact Nat.find_spec h
    have hex : ∃ j, j < replyBound G + 1 ∧ replyTest G we st (candC st.1 j) = true :=
      ⟨Nat.find h, by omega, (hP _).2 (Nat.find_spec h)⟩
    rw [dite_eq_left hex, dite_eq_left h]
    have hfind : Nat.find hex = Nat.find h := by
      apply le_antisymm
      · exact Nat.find_min' hex ⟨by omega, (hP _).2 (Nat.find_spec h)⟩
      · exact Nat.find_min' h ((hP _).1 (Nat.find_spec hex).2)
    rw [ite_eq_left (Nat.find_spec hex).1, hfind, candC_toFinset]
    rfl
  · have hex : ¬ ∃ j, j < replyBound G + 1 ∧ replyTest G we st (candC st.1 j) = true := by
      rintro ⟨j, -, hj⟩
      exact h ⟨j, (hP j).1 hj⟩
    rw [dite_eq_right hex, dite_eq_right h, ite_eq_right (lt_irrefl _)]
    rfl

end
end Kolmogorov.RandomStrings
