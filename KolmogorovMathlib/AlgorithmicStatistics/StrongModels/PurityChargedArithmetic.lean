import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting

/-!
# Absorbing the purity-charged overhead into a single slack constant

The purity-charged route through the uniform-extension stochasticity argument
accumulates an overhead of the shape

```
cExt * (eps + rho + logSlack cBound m + logSlack cBound k_a + logSlack cNat m
        + cNat + cCond) + logSlack cExt m + cExt
```

where `k_a` is a *program-length* witness for the model code, so it is bounded by
`a_len + 2 * (Nat.bits a_len).length + O(1)`, and both `a_len` and `m` are bounded
by the visible parameter budget `B`.

This file shows that all of that folds into the standard charged shape
`C * eps + C * rho + logSlack C B` for a single constant `C` depending only on
the fixed machine constants.  It is pure `Nat`/`logSlack` bookkeeping.
-/

namespace Kolmogorov

/-- The binary length of a program-length witness `k_a` bounded by
`a_len + 2 * L a_len + c₀`, with `a_len ≤ B`, is at most `3 * L B + L c₀ + 3`. -/
theorem length_natBits_programWitness_le (c0 B a_len k_a : ℕ)
    (hka : k_a ≤ a_len + 2 * (Nat.bits a_len).length + c0) (ha : a_len ≤ B) :
    (Nat.bits k_a).length ≤ 3 * (Nat.bits B).length + ((Nat.bits c0).length + 3) := by
  set LB := (Nat.bits B).length with hLB
  have halen : (Nat.bits a_len).length ≤ LB := length_natBits_mono ha
  have h1 : k_a ≤ B + (2 * LB + c0) := by omega
  have h2 : (Nat.bits (2 * LB + c0)).length
      ≤ (Nat.bits (2 * LB)).length + (Nat.bits c0).length + 1 :=
    length_natBits_add_le _ _
  have h3 : (Nat.bits (2 * LB)).length ≤ 2 * LB + 1 := by
    have hsplit : 2 * LB = LB + LB := by ring
    have h := length_natBits_add_le LB LB
    have hself : (Nat.bits LB).length ≤ LB := length_natBits_le_self LB
    rw [hsplit]
    omega
  calc (Nat.bits k_a).length
      ≤ (Nat.bits (B + (2 * LB + c0))).length := length_natBits_mono h1
    _ ≤ LB + (Nat.bits (2 * LB + c0)).length + 1 := length_natBits_add_le _ _
    _ ≤ 3 * LB + ((Nat.bits c0).length + 3) := by omega

/-- **Purity-charged overhead absorption.**  All the machine constants and the
program-length witness `k_a` of the model code fold into a single charged shape
`C * eps + C * rho + logSlack C B`. -/
theorem purity_charged_arithmetic_absorb (cExt cBound cNat cCond cPlain cLen : ℕ) :
    ∃ C : ℕ, ∀ k_a m eps rho B a_len : ℕ,
      k_a ≤ a_len + 2 * (Nat.bits a_len).length + cPlain + cLen →
      a_len ≤ B → m ≤ B →
      cExt * (eps + rho + logSlack cBound m + logSlack cBound k_a + logSlack cNat m
            + cNat + cCond) + logSlack cExt m + cExt
        ≤ C * eps + C * rho + logSlack C B := by
  set D := (Nat.bits (cPlain + cLen)).length + 3 with hDdef
  set P := cExt * (4 * cBound + cNat + 1) with hPdef
  set Q := cExt * (2 * cBound + cBound * D + 2 * cNat + cCond + 2) with hQdef
  refine ⟨cExt + P + Q, ?_⟩
  intro k_a m eps rho B a_len hka ha hm
  set LB := (Nat.bits B).length with hLB
  have hmB : (Nat.bits m).length ≤ LB := length_natBits_mono hm
  have hkB : (Nat.bits k_a).length ≤ 3 * LB + D :=
    length_natBits_programWitness_le (cPlain + cLen) B a_len k_a (by omega) ha
  have step1 :
      cExt * (eps + rho + logSlack cBound m + logSlack cBound k_a + logSlack cNat m
            + cNat + cCond) + logSlack cExt m + cExt
        ≤ cExt * (eps + rho + (cBound * LB + cBound) + (cBound * (3 * LB + D) + cBound)
              + (cNat * LB + cNat) + cNat + cCond) + (cExt * LB + cExt) + cExt := by
    unfold logSlack
    gcongr
  have step2 :
      cExt * (eps + rho + (cBound * LB + cBound) + (cBound * (3 * LB + D) + cBound)
            + (cNat * LB + cNat) + cNat + cCond) + (cExt * LB + cExt) + cExt
        = cExt * eps + cExt * rho + P * LB + Q := by
    rw [hPdef, hQdef]; ring
  have step3 : cExt * eps + cExt * rho + P * LB + Q
      ≤ (cExt + P + Q) * eps + (cExt + P + Q) * rho + logSlack (cExt + P + Q) B := by
    have hC : cExt ≤ cExt + P + Q := by omega
    have h1 : cExt * eps ≤ (cExt + P + Q) * eps := Nat.mul_le_mul_right _ hC
    have h2 : cExt * rho ≤ (cExt + P + Q) * rho := Nat.mul_le_mul_right _ hC
    have h3 : P * LB ≤ (cExt + P + Q) * LB := Nat.mul_le_mul_right _ (by omega)
    have h4 : logSlack (cExt + P + Q) B = (cExt + P + Q) * LB + (cExt + P + Q) := by
      rw [hLB]; rfl
    omega
  omega

end Kolmogorov
