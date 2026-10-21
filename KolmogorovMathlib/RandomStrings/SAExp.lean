/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.PathDataSA
import KolmogorovMathlib.RandomStrings.KeySlots
import KolmogorovMathlib.RandomStrings.Instances
import KolmogorovMathlib.RandomStrings.StackTime

/-!
# `P^R_sa ⊆ EXP` modulo the evaluator

The semantic half of the EXP theorem for sub-adaptive reductions is complete: the value of the
game `G_{e,x}` of a sub-adaptive clocked machine is the raw key recursion
(`valKRaw_gameOf_of_subAdaptive_clock`).  What remains is the evaluator: the language
`valKLang c e T m Y` of the key recursion is in `EXP`.  Given that, this file derives
`hgame` for `EXP` and the family `Family.sa` (`gameValue_mem_EXP_of_subAdaptive`), and the
final theorem (`dec_inter_polyTimeSA_RA_subset_EXP_of_eval`, and its strict corollary).
`valKCLang` is the same language written with the loops over slot codes (`valKCLang_eq`),
with the corresponding final theorem `dec_inter_polyTimeSA_RA_subset_EXP_of_evalC`.
-/

namespace Kolmogorov.RandomStrings

/-- The language of the key recursion: the target of the EXP evaluator (with the outcome of the
game `(gameOf …).outcome = fun S => decide (ClockedAccepts c e (oracleOf T.fn S) x)` and the
fuel `2 ^ (clock e |x| + 1)`). -/
def valKLang (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) : Set BitString :=
  {x | valKRaw (querySet c.toOTM x (clock e x.length) \ Y)
      (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
      (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)).outcome
      (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
      (2 ^ (gameN e T m x.length - m)) (2 ^ (clock e x.length + 1)) = true}

/-- **`hgame` for `EXP` and sub-adaptive machines, given the evaluator**: off a finite set of
inputs on which the machine may fail to be sub-adaptive, the game language agrees with the
language of the key recursion. -/
theorem gameValue_mem_EXP_of_subAdaptive
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLang c e T m Y ∈ EXP)
    (c : OTMCode) (e : ℕ) (Z : Finset BitString) (hΦ : ∀ x, x ∉ Z → SubAdaptiveOn c e x)
    (T : Table) (m : ℕ) (Y : Finset BitString) :
    {x : BitString | val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
      (querySet c.toOTM x (clock e x.length) \ Y)) = true} ∈ EXP :=
  EXP_of_eventually_eq _ _ (hprog c e T m Y) Z fun x hx => by
    change _ = true ↔ _ = true
    rw [valKRaw_gameOf_of_subAdaptive_clock c e T m Y x (hΦ x hx)]

/-- **`P^R_sa ⊆ EXP`, given the evaluator** (Theorem `th_super` of the paper, for the
two-stage history-based notion `PolyTimeSA`): a decidable set that is polynomial-time
sub-adaptively reducible to `R_K` for every universal a priori complexity `K` lies in `EXP`. -/
theorem dec_inter_polyTimeSA_RA_subset_EXP_of_eval
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLang c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeSA (RA K)) :
    A ∈ EXP := by
  let _ := Family.sa
  exact general_clock (fun _ _ => rfl) EXP EXP_of_eventually_eq'
    (fun c e Z hZ T m Y => gameValue_mem_EXP_of_subAdaptive hprog c e Z hZ T m Y) A hA
    fun K hKU => exists_clocked_sa _ _ (hK K hKU)

/-- The strict version: `P^R_ssa ⊆ EXP`, given the evaluator. -/
theorem dec_inter_polyTimeStrictSA_RA_subset_EXP_of_eval
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLang c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeStrictSA (RA K)) :
    A ∈ EXP :=
  dec_inter_polyTimeSA_RA_subset_EXP_of_eval hprog A hA fun K hKU =>
    polyTimeStrictSA_subset_polyTimeSA _ (hK K hKU)

/-- The language of the key recursion over slot codes (`KeySlots.lean`): the same as `valKLang`
(`valKCLang_eq`), in the form of the evaluator's loops over all bit strings of
`clock (2 clock + 1)` bits. -/
def valKCLang (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) : Set BitString :=
  {x | valKC (allBits (clock e x.length * (2 * clock e x.length + 1)))
      (decK (clock e x.length) (clock e x.length))
      (querySet c.toOTM x (clock e x.length) \ Y)
      (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
      (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)).outcome
      (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
      (2 ^ (gameN e T m x.length - m)) (2 ^ (clock e x.length + 1)) = true}

/-- The two forms of the evaluator's target coincide (for every machine). -/
theorem valKCLang_eq (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    valKCLang c e T m Y = valKLang c e T m Y := by
  ext x
  change _ = true ↔ _ = true
  rw [valKC_eq _ _ _ (cover_gameOf c e x T.fn _)]

/-- `P^R_sa ⊆ EXP`, given the evaluator in the form of the loops over slot codes. -/
theorem dec_inter_polyTimeSA_RA_subset_EXP_of_evalC
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKCLang c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeSA (RA K)) :
    A ∈ EXP :=
  dec_inter_polyTimeSA_RA_subset_EXP_of_eval
    (fun c e T m Y => valKCLang_eq c e T m Y ▸ hprog c e T m Y) A hA hK

end Kolmogorov.RandomStrings
