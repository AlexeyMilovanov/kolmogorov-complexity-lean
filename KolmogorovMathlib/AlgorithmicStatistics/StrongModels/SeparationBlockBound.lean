import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4

/-!
# S7 support: the complexity bound `m` of a standard block is `O(C(B) + j)`

The frozen four-way statement of the separation theorem quantifies over an
*unbounded* complexity bound `m`, so the `O(log (max |y| m))` error term supplied
by VS40 Lemma 4 cannot be absorbed for free.  This file supplies the missing
structural input: for a genuine standard block `B = standardBlock q m j x` with
`x ∈ B`, the bound `m` itself is controlled,

`m ≤ C(B) + j + O(C(q)) + O(log m)`,

because the block together with the enumerator and the outstanding-output
counter reconstructs `Ω_m`, whose plain complexity is at least `m - O(C(q) + log m)`.
Combined with the elementary fact that a logarithmic slack is eventually
dominated by its own argument, this yields `m = O(C(B) + j + C(q))`, which is the
form used by the separation capstone.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- A logarithmic slack is eventually strictly below its own argument. -/
theorem logSlack_lt_self_of_large (C : Nat) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → logSlack C k < k := by
  refine ⟨(3 * C + 3) * (3 * C + 3), fun k hk => ?_⟩
  have hbits : (Nat.bits k).length ≤ Nat.sqrt k + 2 := bits_length_le_sqrt_add_two k
  have h1 : Nat.sqrt k * Nat.sqrt k ≤ k := Nat.sqrt_le k
  have h2 : 3 * C + 3 ≤ Nat.sqrt k := by
    have h := Nat.sqrt_le_sqrt hk
    rwa [Nat.sqrt_eq] at h
  have hle : logSlack C k ≤ C * (Nat.sqrt k + 2) + C := by
    unfold logSlack
    exact Nat.add_le_add_right (Nat.mul_le_mul_left C hbits) C
  nlinarith [Nat.zero_le (Nat.sqrt k)]

/-- If a quantity is bounded by `A` plus its own logarithmic slack, it is bounded
by `2 * A` plus a constant depending only on the slack constant. -/
theorem le_two_mul_of_le_add_logSlack (c : Nat) :
    ∃ b : Nat, ∀ m A : Nat, m ≤ A + logSlack c m → m ≤ 2 * A + b := by
  obtain ⟨m0, hm0⟩ := logSlack_lt_self_of_large (2 * c)
  refine ⟨m0, fun m A h => ?_⟩
  rcases le_or_gt m0 m with hm | hm
  · have hlt := hm0 m hm
    have heq : 2 * logSlack c m = logSlack (2 * c) m := by
      unfold logSlack; ring
    omega
  · omega

/-- **Standard blocks control their own complexity bound.**  If `x` lies in the
genuine standard block `B = standardBlock q m j x`, then the enumeration bound
`m` is bounded by the plain complexity of `B`, its log-cardinality `j`, the
complexity of the enumerator, and a logarithmic slack.

The proof reconstructs `Ω_m` from `B` (a block of `2 ^ j` outputs occurring at a
known dyadic position, so the outstanding-output counter fits in `j + 1` bits)
and compares with the uniform lower bound `m ≤ C(Ω_m) + O(C(q) + log m)`. -/
theorem enumerationBound_le_standardBlock_complexity
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (q : Code), IsCodeFor q V → ∀ (m j : Nat) (x : BitString)
      (hx : x ∈ standardBlock q m j x),
      m ≤ (plainSetComplexity V (standardBlock q m j x) ⟨x, hx⟩).toNat + j +
        c * (plainK V (standardEnumeratorCode q)).toNat + logSlack c m := by
  classical
  obtain ⟨c₄, hRecon⟩ := plainKNat_omegaCount_le_of_stage_cover_width V hV
  obtain ⟨c₅, hLower⟩ := plainKNat_omegaCount_lower_uniform V hV
  refine ⟨c₄ + c₅ + 10, ?_⟩
  set c := c₄ + c₅ + 10 with hcdef
  intro q hq m j x hx
  set B := standardBlock q m j x with hBdef
  have hB : B.Nonempty := ⟨x, hx⟩
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  have hQfin : plainK V (standardEnumeratorCode q) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.natCast_ne_top ((standardEnumeratorCode q).length + cLen)))
      (hLen (standardEnumeratorCode q))
  obtain ⟨Qv, hQv⟩ := ENat.ne_top_iff_exists.mp hQfin
  have hQtoNat : (plainK V (standardEnumeratorCode q)).toNat = Qv := by
    rw [← hQv]; simp
  have hBfin : plainSetComplexity V B hB ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.natCast_ne_top ((codedUniformOn B hB).code.length + cLen)))
      (hLen (codedUniformOn B hB).code)
  obtain ⟨Bv, hBv⟩ := ENat.ne_top_iff_exists.mp hBfin
  have hBtoNat : (plainSetComplexity V B hB).toNat = Bv := by
    rw [← hBv]; simp
  have hsub : ∀ z ∈ B, z ∈ completedBoundedOutput q m := fun z hz =>
    List.mem_toFinset.mp (standardBlock_subset_completed q m j x hz)
  obtain ⟨t, hcover, hmint⟩ := exists_minimal_boundedOutputStage_cover q m B hsub
  have hx0 : x ∈ standardBlock q m j [] := hx
  have hrem : omegaCount q m - (boundedOutputStage q m t).length < 2 ^ (j + 1) :=
    boundedOutputStage_remainder_lt_two_pow_succ_of_mem_standardBlock
      q m j t x hx0 (hcover x hx)
  have hjm : j ≤ m := standardBlock_exponent_le q m j x hx
  have hbitsj : (Nat.bits (j + 1)).length ≤ (Nat.bits m).length + 1 :=
    le_trans (length_natBits_mono (Nat.succ_le_succ hjm)) (length_natBits_succ_le m)
  have hstep : plainKNat V (omegaCount q m) ≤
      ((Bv + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
        2 * (Nat.bits (j + 1)).length + c₄ : Nat) : ENat) := by
    refine (hRecon q m B hB t (j + 1) hcover hmint hrem).trans (le_of_eq ?_)
    rw [← hQv, ← hBv]
    push_cast
    ring
  have hm : (m : ENat) ≤
      ((Bv + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
        2 * (Nat.bits (j + 1)).length + c₄ + c₅ * Qv + logSlack c₅ m : Nat) : ENat) := by
    refine (hLower q hq m).trans ?_
    rw [← hQv]
    calc
      plainKNat V (omegaCount q m) + (c₅ : ENat) * (Qv : ENat) +
            ((logSlack c₅ m : Nat) : ENat)
          ≤ ((Bv + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
              2 * (Nat.bits (j + 1)).length + c₄ : Nat) : ENat) +
              (c₅ : ENat) * (Qv : ENat) + ((logSlack c₅ m : Nat) : ENat) := by
            gcongr
      _ = ((Bv + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
              2 * (Nat.bits (j + 1)).length + c₄ + c₅ * Qv + logSlack c₅ m : Nat) : ENat) := by
            push_cast
            ring
  have hmnat : m ≤ Bv + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
      2 * (Nat.bits (j + 1)).length + c₄ + c₅ * Qv + logSlack c₅ m := by
    exact_mod_cast hm
  rw [hBtoNat, hQtoNat]
  set L := (Nat.bits m).length with hLdef
  have hQmul : (2 + c₅) * Qv ≤ c * Qv :=
    Nat.mul_le_mul_right _ (by omega)
  have hLmul : (4 + c₅) * L ≤ c * L :=
    Nat.mul_le_mul_right _ (by omega)
  have hslack : logSlack c₅ m = c₅ * L + c₅ := by
    unfold logSlack; rw [hLdef]
  have hgoal : logSlack c m = c * L + c := by
    unfold logSlack; rw [hLdef]
  rw [hgoal]
  have hexp1 : (2 + c₅) * Qv = 2 * Qv + c₅ * Qv := by ring
  have hexp2 : (4 + c₅) * L = 2 * L + 2 * L + c₅ * L := by ring
  omega

end Kolmogorov
