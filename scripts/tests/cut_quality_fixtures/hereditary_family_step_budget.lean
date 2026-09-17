-- Calibration fixture for scripts/cut_quality.py: hereditary_family_step_budget.
-- Lines 814-857 of KolmogorovMathlib/AlgorithmicStatistics/StrongModels/Hereditary/Part02/Budget.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- The ordinary-complexity overhead of the partition, family and transport steps — the
transport charge, the family charge, the two-stage transfer of the model to its partition
class, the sufficiency gap and the two extra bits of the partition — lies inside the
hereditary slack of `b ^ 27`. -/
lemma hereditary_family_step_budget {b n eps delta cardA1 mComp pF1 pPlain gapCost c : Nat}
    (hb : 3 ≤ b) (hsqrt : 1 ≤ Nat.sqrt n) (hc : c ≤ b) (hcardA1 : cardA1 ≤ 2 * n + b)
    (hmComp : mComp ≤ 2 * n + b + hereditaryUnit delta eps n)
    (hpF1 : pF1 ≤ b ^ 3 * hereditaryUnit delta eps n)
    (hpPlain : pPlain ≤ b ^ 4 * hereditaryUnit delta eps n)
    (hgap : gapCost ≤ b ^ 20 * hereditaryUnit delta eps n) :
    2 * pF1 + c + (c * pF1 + logSlack c cardA1) +
        (pPlain + 2 * (Nat.bits mComp).length + c) + gapCost + 2 ≤
      hereditarySlack (b ^ 27) delta eps n := by
  set U := hereditaryUnit delta eps n with hU
  have hb2 : 2 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hU1 : 1 ≤ U := one_le_hereditaryUnit delta eps n
  have hLbU : (Nat.bits n).length ≤ U := bitsLength_le_hereditaryUnit delta eps hsqrt
  have hc1 : 2 * pF1 + c ≤ b ^ 5 * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) (budget_mul_pow (by omega : 2 ≤ b) hpF1))
      (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hc))
  have hc2 : c * pF1 + logSlack c cardA1 ≤ b ^ 5 * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) (budget_mul_pow hc hpF1))
      (budget_logSlack_pow hb2 hU1 hc (budget_bits_of_le_two_mul hb hU1 hLbU hcardA1))
  have hbitsM : (Nat.bits mComp).length ≤ b ^ 3 * U := by
    refine budget_bits_mix hb hU1 hLbU ?_
    simpa using hmComp
  have hc3 : pPlain + 2 * (Nat.bits mComp).length + c ≤ b ^ 6 * U := by
    refine budget_add_pow hb2 (budget_add_pow hb2 (budget_mono_pow hb1 (by omega) hpPlain)
      (budget_mono_pow hb1 (by omega) (budget_mul_pow (by omega : 2 ≤ b) hbitsM))) ?_
    exact budget_mono_pow hb1 (by omega) (budget_const_pow hU1 hc)
  have t1 : 2 * pF1 + c + (c * pF1 + logSlack c cardA1) ≤ b ^ 6 * U :=
    budget_add_pow hb2 hc1 hc2
  have t2 : 2 * pF1 + c + (c * pF1 + logSlack c cardA1) +
      (pPlain + 2 * (Nat.bits mComp).length + c) ≤ b ^ 7 * U :=
    budget_add_pow hb2 t1 hc3
  have t3 : 2 * pF1 + c + (c * pF1 + logSlack c cardA1) +
      (pPlain + 2 * (Nat.bits mComp).length + c) + gapCost ≤ b ^ 21 * U :=
    budget_add_pow hb2 (budget_mono_pow hb1 (by omega) t2)
      (budget_mono_pow hb1 (by omega) hgap)
  have t4 := budget_add_pow (a2 := 2) hb2 t3
    (budget_mono_pow hb1 (by omega) (budget_const_pow hU1 (by omega : 2 ≤ b)))
  rw [hereditarySlack_eq_mul_unit, ← hU]
  exact budget_mono_pow hb1 (by omega) t4

end Kolmogorov
