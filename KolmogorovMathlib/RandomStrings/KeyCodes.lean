/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.PathGame

/-!
# The key recursion over codes

The EXP evaluator iterates over a list `codes` of codes of keys, decoded by `dec`, instead of the
subsets of the strings in play.  `yesKC`/`valKC` are `yesKRaw`/`valKRaw` with every quantifier over
`X.powerset` replaced by one over `codes` (as `List.all`/`List.any`); they agree with the key
recursion as soon as every target of a key move has a code (`yesKC_eq`, `valKC_eq`).  Duplicates
and junk codes are harmless: junk is only looked at behind a `KeyMoveRaw` test, which implies
`⊆ X`.  For the game of a clocked machine the targets of key moves are small
(`keyMoveRaw_gameOf_small`: at most `clock` strings of length `≤ clock`), which gives the cover
hypothesis for a slot encoding with an empty-slot code.

* Layered value iteration: one layer is `stepKC` of the previous one, which is read
  only at scores `≤ E` (`stepKC_congr`); a table built this way is `yesKC` on the scores `≤ E`
  (`layer_eq_yesKC`), and the answer is read off the last layer (`valKC_eq_of_layer`).
* Saturated costs: costs `min (c z) (E + 1)` give the same recursion (`yesKRaw_sat`,
  `valKRaw_sat`), so costs may be computed in bounded width.
-/

namespace Kolmogorov.RandomStrings

section Codes

variable {α : Type} (codes : List α) (dec : α → Finset BitString) (X : Finset BitString)
  (P : Finset BitString → Finset BitString) (out : Finset BitString → Bool)
  (c : BitString → ℕ) (E : ℕ)

/-- The key recursion over codes. -/
def yesKC : ℕ → α → ℕ → ℕ → Bool
  | 0, κ, _, _ => out (dec κ)
  | f + 1, κ, y, n => out (dec κ) && codes.all fun κ' =>
      !(decide (KeyMoveRaw X P (dec κ) (dec κ')) && !decide (dec κ' ⊆ dec κ) &&
          decide (n + costN c (dec κ) (dec κ') ≤ E)) ||
        codes.any fun ρ => decide (KeyMoveRaw X P (dec κ') (dec ρ)) &&
          decide (y + costN c (dec κ') (dec ρ) ≤ E) &&
          yesKC f ρ (y + costN c (dec κ') (dec ρ)) (n + costN c (dec κ) (dec κ'))

/-- The value of the key game over codes. -/
def valKC (F : ℕ) : Bool :=
  codes.any fun κ => decide (KeyMoveRaw X P ∅ (dec κ)) && decide (costN c ∅ (dec κ) ≤ E) &&
    yesKC codes dec X P out c E F κ (costN c ∅ (dec κ)) 0

variable {codes dec X P}

/-- **The recursion over codes is the key recursion** when every target of a key move (a subset
of `X` on its own run) has a code. -/
theorem yesKC_eq (hcover : ∀ K : Finset BitString, K ⊆ X → K ⊆ P K → ∃ κ ∈ codes, dec κ = K) :
    ∀ (f : ℕ) (κ : α) (y n : ℕ),
      yesKC codes dec X P out c E f κ y n = yesKRaw X P out c E f (dec κ) y n := by
  intro f
  induction f with
  | zero => intro κ y n; rfl
  | succ f ih =>
    intro κ y n
    simp only [yesKC, yesKRaw]
    congr 1
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro H K' hK'P hKM hne hcost
      obtain ⟨κ', hκ', rfl⟩ := hcover K' hKM.1 hKM.2.1
      have h1 := H κ' hκ'
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
        List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
      rcases h1 with ((h1 | h1) | h1) | ⟨ρ, hρ, ⟨hKMρ, hcostρ⟩, hyes⟩
      · exact absurd hKM h1
      · exact absurd (by simpa using h1) hne
      · exact absurd hcost h1
      · refine ⟨dec ρ, Finset.mem_powerset.2 hKMρ.1, hKMρ, hcostρ, ?_⟩
        rw [← ih]; exact hyes
    · intro H κ' hκ'
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
        List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hKM : KeyMoveRaw X P (dec κ) (dec κ')
      · by_cases hne : dec κ' ⊆ dec κ
        · left; left; right; simpa using hne
        · by_cases hcost : n + costN c (dec κ) (dec κ') ≤ E
          · obtain ⟨R, -, hKMR, hcostR, hyes⟩ :=
              H (dec κ') (Finset.mem_powerset.2 hKM.1) hKM hne hcost
            obtain ⟨ρ, hρ, rfl⟩ := hcover R hKMR.1 hKMR.2.1
            right
            exact ⟨ρ, hρ, ⟨hKMR, hcostR⟩, by rw [ih]; exact hyes⟩
          · left; right; exact hcost
      · left; left; left; exact hKM

/-- The value of the key game over codes equals the raw value of the key game, provided every target
of a key move has a code. -/
theorem valKC_eq (hcover : ∀ K : Finset BitString, K ⊆ X → K ⊆ P K → ∃ κ ∈ codes, dec κ = K)
    (F : ℕ) : valKC codes dec X P out c E F = valKRaw X P out c E F := by
  unfold valKC valKRaw
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨κ, -, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hKM, hcost⟩, hyes⟩ := h
    exact ⟨dec κ, Finset.mem_powerset.2 hKM.1, hKM, hcost,
      by rw [← yesKC_eq out c E hcover]; exact hyes⟩
  · rintro ⟨K₁, -, hKM, hcost, hyes⟩
    obtain ⟨κ, hκ, rfl⟩ := hcover K₁ hKM.1 hKM.2.1
    refine ⟨κ, hκ, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hKM, hcost⟩, by rw [yesKC_eq out c E hcover]; exact hyes⟩

end Codes

/-! ### Layered value iteration

One layer of the evaluator computes `stepKC (previous layer)`; it only consults the previous layer
at scores `≤ E` (both scores are guarded by `≤ E`).  So any table that starts with the outcomes
and is updated by `stepKC` agrees with `yesKC` on the scores `≤ E` (`layer_eq_yesKC`), and the
answer read off the last layer is `valKC` (`valKC_eq_of_layer`). -/

section Layers

variable {α : Type} (codes : List α) (dec : α → Finset BitString) (X : Finset BitString)
  (P : Finset BitString → Finset BitString) (out : Finset BitString → Bool)
  (c : BitString → ℕ) (E : ℕ)

/-- One layer of value iteration over codes, reading the previous layer `g`. -/
def stepKC (g : α → ℕ → ℕ → Bool) (κ : α) (y n : ℕ) : Bool :=
  out (dec κ) && codes.all fun κ' =>
    !(decide (KeyMoveRaw X P (dec κ) (dec κ')) && !decide (dec κ' ⊆ dec κ) &&
        decide (n + costN c (dec κ) (dec κ') ≤ E)) ||
      codes.any fun ρ => decide (KeyMoveRaw X P (dec κ') (dec ρ)) &&
        decide (y + costN c (dec κ') (dec ρ) ≤ E) &&
        g ρ (y + costN c (dec κ') (dec ρ)) (n + costN c (dec κ) (dec κ'))

/-- Evaluating `yesKC` for one more layer is equal to applying `stepKC` to the previous layer. -/
theorem yesKC_succ (f : ℕ) (κ : α) (y n : ℕ) :
    yesKC codes dec X P out c E (f + 1) κ y n =
      stepKC codes dec X P out c E (yesKC codes dec X P out c E f) κ y n := rfl

/-- A layer only reads the previous one at scores `≤ E`. -/
theorem stepKC_congr {g₁ g₂ : α → ℕ → ℕ → Bool}
    (h : ∀ ρ y' n', y' ≤ E → n' ≤ E → g₁ ρ y' n' = g₂ ρ y' n') (κ : α) (y n : ℕ) :
    stepKC codes dec X P out c E g₁ κ y n = stepKC codes dec X P out c E g₂ κ y n := by
  unfold stepKC
  congr 1
  congr 1
  funext κ'
  by_cases h2 : n + costN c (dec κ) (dec κ') ≤ E
  · congr 1
    congr 1
    funext ρ
    by_cases h1 : y + costN c (dec κ') (dec ρ) ≤ E
    · rw [h ρ _ _ h1 h2]
    · simp [h1]
  · simp [h2]

/-- **The layer invariant**: a table that starts with the outcomes and is updated by `stepKC`
agrees with `yesKC` at all scores `≤ E`. -/
theorem layer_eq_yesKC (tab : ℕ → α → ℕ → ℕ → Bool)
    (h0 : ∀ κ y n, y ≤ E → n ≤ E → tab 0 κ y n = out (dec κ))
    (hs : ∀ f κ y n, y ≤ E → n ≤ E →
      tab (f + 1) κ y n = stepKC codes dec X P out c E (tab f) κ y n) :
    ∀ f κ y n, y ≤ E → n ≤ E → tab f κ y n = yesKC codes dec X P out c E f κ y n := by
  intro f
  induction f with
  | zero => intro κ y n hy hn; exact h0 κ y n hy hn
  | succ f ih =>
    intro κ y n hy hn
    rw [hs f κ y n hy hn, yesKC_succ]
    exact stepKC_congr codes dec X P out c E (fun ρ y' n' hy' hn' => ih ρ y' n' hy' hn') κ y n

/-- The answer read off the last layer. -/
theorem valKC_eq_of_layer (F : ℕ) (tabF : α → ℕ → ℕ → Bool)
    (h : ∀ κ y n, y ≤ E → n ≤ E → tabF κ y n = yesKC codes dec X P out c E F κ y n) :
    valKC codes dec X P out c E F = codes.any fun κ =>
      decide (KeyMoveRaw X P ∅ (dec κ)) && decide (costN c ∅ (dec κ) ≤ E) &&
        tabF κ (costN c ∅ (dec κ)) 0 := by
  unfold valKC
  congr 1
  funext κ
  by_cases hc : costN c ∅ (dec κ) ≤ E
  · rw [h κ _ 0 hc (Nat.zero_le _)]
  · simp [hc]

end Layers

/-! ### Saturated costs

The key recursion only compares sums of costs with the budget `E`; costs saturated at `E + 1`
give the same recursion, so an evaluator may compute costs in bounded width. -/

section Saturation

/-- The saturated cost of a move is at most the true cost of the move. -/
theorem costN_sat_le (c : BitString → ℕ) (E : ℕ) (S S' : Finset BitString) :
    costN (fun z => min (c z) (E + 1)) S S' ≤ costN c S S' :=
  Finset.sum_le_sum fun _ _ => min_le_left _ _

/-- Within the budget, saturated costs are the costs. -/
theorem costN_sat_eq_of_le {c : BitString → ℕ} {E n : ℕ} {S S' : Finset BitString}
    (h : n + costN (fun z => min (c z) (E + 1)) S S' ≤ E) :
    costN (fun z => min (c z) (E + 1)) S S' = costN c S S' := by
  refine Finset.sum_congr rfl fun z hz => min_eq_left ?_
  have h1 : min (c z) (E + 1) ≤ costN (fun z => min (c z) (E + 1)) S S' :=
    Finset.single_le_sum (f := fun z => min (c z) (E + 1)) (fun _ _ => Nat.zero_le _) hz
  rcases min_le_iff.1 (show min (c z) (E + 1) ≤ E by omega) with h2 | h2 <;> omega

/-- The saturated cost of a move is within the budget if and only if the true cost is within the
budget. -/
theorem costN_sat_le_iff (c : BitString → ℕ) (E n : ℕ) (S S' : Finset BitString) :
    n + costN (fun z => min (c z) (E + 1)) S S' ≤ E ↔ n + costN c S S' ≤ E := by
  constructor
  · intro h
    rw [← costN_sat_eq_of_le h]; exact h
  · intro h
    have := costN_sat_le c E S S'
    omega

/-- **Saturation does not change the key recursion.** -/
theorem yesKRaw_sat (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool) (c : BitString → ℕ) (E : ℕ) :
    ∀ (f : ℕ) (K : Finset BitString) (y n : ℕ),
      yesKRaw X P out (fun z => min (c z) (E + 1)) E f K y n = yesKRaw X P out c E f K y n := by
  intro f
  induction f with
  | zero => intro K y n; rfl
  | succ f ih =>
    intro K y n
    simp only [yesKRaw]
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    refine forall₂_congr fun K' _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
    constructor
    · intro H hc
      have hc' := (costN_sat_le_iff c E n K K').2 hc
      obtain ⟨R, hR, hKM, hcR, hy⟩ := H hc'
      refine ⟨R, hR, hKM, (costN_sat_le_iff c E y K' R).1 hcR, ?_⟩
      rw [costN_sat_eq_of_le hcR, costN_sat_eq_of_le hc', ih] at hy
      exact hy
    · intro H hc
      have hc' := (costN_sat_le_iff c E n K K').1 hc
      obtain ⟨R, hR, hKM, hcR, hy⟩ := H hc'
      have hcR' := (costN_sat_le_iff c E y K' R).2 hcR
      refine ⟨R, hR, hKM, hcR', ?_⟩
      rw [costN_sat_eq_of_le hcR', costN_sat_eq_of_le hc, ih]
      exact hy

/-- **Saturation does not change the value of the key game.** The value of the key game with
saturated costs is equal to the value with true costs. -/
theorem valKRaw_sat (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool) (c : BitString → ℕ) (E F : ℕ) :
    valKRaw X P out (fun z => min (c z) (E + 1)) E F = valKRaw X P out c E F := by
  unfold valKRaw
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  refine exists_congr fun K₁ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hc, hy⟩
    rw [yesKRaw_sat, costN_sat_eq_of_le (n := 0) (by simpa using hc)] at hy
    exact ⟨(by simpa using (costN_sat_le_iff c E 0 ∅ K₁).1 (by simpa using hc)), hy⟩
  · rintro ⟨hc, hy⟩
    have hc' : 0 + costN (fun z => min (c z) (E + 1)) ∅ K₁ ≤ E :=
      (costN_sat_le_iff c E 0 ∅ K₁).2 (by simpa using hc)
    refine ⟨by simpa using hc', ?_⟩
    rw [yesKRaw_sat, costN_sat_eq_of_le hc']
    exact hy

end Saturation

end Kolmogorov.RandomStrings
