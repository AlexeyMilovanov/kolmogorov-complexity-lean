/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.PathDataSA
import KolmogorovMathlib.RandomStrings.SAExp
import KolmogorovMathlib.RandomStrings.Instances

/-!
# The address structure of a boundary-free sub-adaptive machine, and `P^R_saTree ⊆ EXP`

For a clocked machine `(c, e)` that is sub-adaptive on `x` in the boundary-free sense
(`SubAdaptiveTreeOn`), the game `G_{e,x}` has an address structure (`exists_pathData_tree`): this
is `exists_pathData_of_stages` with the stage-1 set `Q₁ := alwaysAsked c.toOTM x (clock e |x|)`,
the strings asked under every oracle within the clock.  The subset condition is
`alwaysAsked_subset_queries`, and `subAdaptiveTree_iff_alwaysAsked` implies that a string outside
the always-asked set is asked at a single node of the reduction tree.  No stage boundary is needed.

With `PathData.valKRaw_eq_val`, the key recursion computes the value of the game
(`valKRaw_gameOf_of_subAdaptiveTree_clock`), which gives `hgame` for `EXP` and the family
`Family.saTree` given the evaluator (`gameValue_mem_EXP_of_subAdaptiveTree`) and the final theorem
`dec_inter_polyTimeSATree_RA_subset_EXP_of_eval` (and `…_of_evalC`, with the evaluator over slot
codes).  The boundary-free class contains the two-stage, strictly sub-adaptive and truth-table
classes (`polyTimeSA_subset_polyTimeSATree`, `polyTimeStrictSA_subset_polyTimeSATree`,
`polyTimeTT_subset_polyTimeSATree`), so the tree version subsumes the corresponding statements
for these classes (the corollaries at the end).
-/

namespace Kolmogorov.RandomStrings

/-- **The address structure of a boundary-free sub-adaptive clocked machine**:
`exists_pathData_of_stages` with the always-asked set as the stage-1 set. -/
theorem exists_pathData_tree (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (hX : X ⊆ querySet c.toOTM x (clock e x.length))
    (hsa : SubAdaptiveTreeOn c e x) :
    ∃ D : PathData, D.X = X ∧ D.U = querySet c.toOTM x (clock e x.length) ∧
      D.out = (gameOf c e x h ε X).outcome ∧
      ∀ S, D.P S = queries c.toOTM (oracleOf h S) x (clock e x.length) :=
  exists_pathData_of_stages c e x h ε X hX (alwaysAsked c.toOTM x (clock e x.length))
    (alwaysAsked_subset_queries c.toOTM x (clock e x.length))
    fun B B' t t' z ht ht' hz hz' hQ =>
      (subAdaptiveTree_iff_alwaysAsked (M := c.toOTM) (x := x) (T := clock e x.length)).1 hsa
        B B' t t' z ht ht' hz hz' hQ

/-- **The key recursion computes the value of `G_{e,x}` for a boundary-free sub-adaptive
machine** (mirror of `valKRaw_gameOf_of_subAdaptive`), with any fuel `F ≥ |X|`. -/
theorem valKRaw_gameOf_of_subAdaptiveTree (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ)
    (Y : Finset BitString) (x : BitString) (hsa : SubAdaptiveTreeOn c e x) (F : ℕ)
    (hF : (querySet c.toOTM x (clock e x.length) \ Y).card ≤ F) :
    valKRaw (querySet c.toOTM x (clock e x.length) \ Y)
        (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
        (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)).outcome
        (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
        (2 ^ (gameN e T m x.length - m)) F =
      val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)) := by
  obtain ⟨D, hDX, -, hDout, hDP⟩ := exists_pathData_tree c e x T.fn ((2 : ℝ)⁻¹ ^ m)
    (querySet c.toOTM x (clock e x.length) \ Y) Finset.sdiff_subset hsa
  exact D.valKRaw_eq_val hDX hDP (fun S => by rw [hDout]) _ (gameN e T m x.length) _ _ F rfl rfl
    (fun z hz => gameOf_flipCost_eq c e T m Y x z hz) (gameOf_eps_eq c e T m x _) hF

/-- `valKRaw_gameOf_of_subAdaptiveTree` with the fuel `2 ^ (clock e |x| + 1)` of the evaluator
(mirror of `valKRaw_gameOf_of_subAdaptive_clock`). -/
theorem valKRaw_gameOf_of_subAdaptiveTree_clock (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ)
    (Y : Finset BitString) (x : BitString) (hsa : SubAdaptiveTreeOn c e x) :
    valKRaw (querySet c.toOTM x (clock e x.length) \ Y)
        (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
        (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)).outcome
        (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
        (2 ^ (gameN e T m x.length - m)) (2 ^ (clock e x.length + 1)) =
      val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)) :=
  valKRaw_gameOf_of_subAdaptiveTree c e T m Y x hsa _
    ((Finset.card_le_card Finset.sdiff_subset).trans (card_querySet_lt _ _ _).le)

/-- **`hgame` for `EXP` and boundary-free sub-adaptive machines, given the evaluator**: off a
finite set of inputs on which the machine may fail to be sub-adaptive, the game language agrees
with the language `valKLang` of the key recursion. -/
theorem gameValue_mem_EXP_of_subAdaptiveTree
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLang c e T m Y ∈ EXP)
    (c : OTMCode) (e : ℕ) (Z : Finset BitString) (hΦ : ∀ x, x ∉ Z → SubAdaptiveTreeOn c e x)
    (T : Table) (m : ℕ) (Y : Finset BitString) :
    {x : BitString | val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
      (querySet c.toOTM x (clock e x.length) \ Y)) = true} ∈ EXP :=
  EXP_of_eventually_eq _ _ (hprog c e T m Y) Z fun x hx => by
    change _ = true ↔ _ = true
    rw [valKRaw_gameOf_of_subAdaptiveTree_clock c e T m Y x (hΦ x hx)]

/-- **`P^R_saTree ⊆ EXP`, given the evaluator** (Theorem `th_super` of the paper, for the
boundary-free two-stage notion `PolyTimeSATree`): a decidable set that is polynomial-time
sub-adaptively reducible (boundary-free) to `R_K` for every universal a priori complexity `K` lies
in `EXP`. -/
theorem dec_inter_polyTimeSATree_RA_subset_EXP_of_eval
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLang c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeSATree (RA K)) :
    A ∈ EXP := by
  let _ := Family.saTree
  exact general_clock (fun _ _ => rfl) EXP EXP_of_eventually_eq'
    (fun c e Z hZ T m Y => gameValue_mem_EXP_of_subAdaptiveTree hprog c e Z hZ T m Y) A hA
    fun K hKU => exists_clocked_saTree _ _ (hK K hKU)

/-- `P^R_saTree ⊆ EXP`, given the evaluator in the form of the loops over slot codes
(`valKCLang`, `valKCLang_eq`; mirror of `dec_inter_polyTimeSA_RA_subset_EXP_of_evalC`). -/
theorem dec_inter_polyTimeSATree_RA_subset_EXP_of_evalC
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKCLang c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeSATree (RA K)) :
    A ∈ EXP :=
  dec_inter_polyTimeSATree_RA_subset_EXP_of_eval
    (fun c e T m Y => valKCLang_eq c e T m Y ▸ hprog c e T m Y) A hA hK

/-! ### The tree version subsumes the other notions -/

/-- `P^R_sa ⊆ EXP`, given the evaluator, as a corollary of the tree version
(`polyTimeSA_subset_polyTimeSATree`). -/
theorem dec_inter_polyTimeSA_RA_subset_EXP_of_eval'
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLang c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeSA (RA K)) :
    A ∈ EXP :=
  dec_inter_polyTimeSATree_RA_subset_EXP_of_eval hprog A hA fun K hKU =>
    polyTimeSA_subset_polyTimeSATree _ (hK K hKU)

/-- `P^R_ssa ⊆ EXP`, given the evaluator, as a corollary of the tree version
(`polyTimeStrictSA_subset_polyTimeSATree`). -/
theorem dec_inter_polyTimeStrictSA_RA_subset_EXP_of_eval'
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLang c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeStrictSA (RA K)) :
    A ∈ EXP :=
  dec_inter_polyTimeSATree_RA_subset_EXP_of_eval hprog A hA fun K hKU =>
    polyTimeStrictSA_subset_polyTimeSATree _ (hK K hKU)

/-- `P^R_tt ⊆ EXP`, given the evaluator, as a corollary of the tree version
(`polyTimeTT_subset_polyTimeSATree`; the unconditional `PSPACE` bound is
`dec_inter_polyTimeTT_RA_subset_PSPACE`). -/
theorem dec_inter_polyTimeTT_RA_subset_EXP_of_eval
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLang c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ PolyTimeTT (RA K)) :
    A ∈ EXP :=
  dec_inter_polyTimeSATree_RA_subset_EXP_of_eval hprog A hA fun K hKU =>
    polyTimeTT_subset_polyTimeSATree _ (hK K hKU)

end Kolmogorov.RandomStrings
