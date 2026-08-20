import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileCardinality
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.StandardDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainSymmetry

/-!
# Counting leaves for the exact-radius Lemma `omp`

This module collects the elementary counting facts that the remaining
exact-radius branch of Lemma `omp` (`LemmaOmp.lean`) needs about *genuine*
standard blocks, i.e. about the additional structure that pure profile geometry
does not see.

* `exists_high_testBit_of_pow_le` — a natural number `n` with `2 ^ a ≤ n` has a
  set bit at some position `≥ a`.  Applied to `omegaCount`, this produces a
  standard block whose exponent is at least the given scale.
* `exists_condK_ge_of_finset_card_pow` — incompressibility for finite sets: a
  finset of at least `2 ^ r` bit strings contains a member of conditional
  complexity at least `r` (relative to any condition `z` and any map `V`).
* `exists_standardBlock_member_condK_ge` — the specialisation to a standard
  block of exponent `r`, whose cardinality is exactly `2 ^ r`.
-/

namespace Kolmogorov

/-- If `2 ^ a ≤ n` then `n` has a set binary digit at some position `≥ a`. -/
theorem exists_high_testBit_of_pow_le {a n : Nat} (h : 2 ^ a ≤ n) :
    ∃ r, a ≤ r ∧ n.testBit r = true := by
  have hn : n ≠ 0 := by
    have : 0 < 2 ^ a := Nat.two_pow_pos a
    omega
  obtain ⟨i, hi, hi'⟩ := Nat.exists_most_significant_bit hn
  refine ⟨i, ?_, hi⟩
  by_contra hlt
  push_neg at hlt
  have hlt2 : n < 2 ^ (i + 1) := by
    refine Nat.lt_of_testBit (i + 1) (hi' _ (by omega)) (by simp) ?_
    intro j hj
    rw [hi' j (by omega), Nat.testBit_two_pow]
    simp
    omega
  have : (2 : Nat) ^ (i + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Incompressibility for finite sets.**  A finset of at least `2 ^ r` bit
strings contains a member whose conditional complexity given `z` is at least
`r`: there are fewer than `2 ^ r` programs of length `< r`. -/
theorem exists_condK_ge_of_finset_card_pow
    (V : Map) (A : Finset BitString) (z : BitString) (r : Nat)
    (hcard : 2 ^ r ≤ A.card) :
    ∃ x ∈ A, (r : ENat) ≤ condK V x z := by
  classical
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have : A.Nonempty := Finset.card_pos.mp (by simpa using hcard)
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx, by simp⟩
  · by_contra hcon
    push_neg at hcon
    have hbudget : ∀ x ∈ A, condK V x z ≤ ((r - 1 : Nat) : ENat) := by
      intro x hx
      have hlt : condK V x z < (r : ENat) := hcon x hx
      have hlt' : sInf (candidateLengths V x z) < (r : ENat) := hlt
      obtain ⟨len, hmem, hvlt⟩ := sInf_lt_iff.mp hlt'
      obtain ⟨p, hp, rfl⟩ := hmem
      have hplt : programLength p < r := by exact_mod_cast hvlt
      have hple : programLength p ≤ r - 1 := by omega
      calc condK V x z ≤ (programLength p : ENat) :=
            sInf_le ⟨p, hp, rfl⟩
        _ ≤ ((r - 1 : Nat) : ENat) := by exact_mod_cast hple
    have hle := card_condK_le_boundedPrograms_length V z (r - 1) A hbudget
    have hlt := length_boundedPrograms_lt (r - 1)
    have hpow : (2 : Nat) ^ (r - 1 + 1) = 2 ^ r := by
      congr 1
      omega
    omega

/-- Every genuine standard block of exponent `r` contains a member of
conditional complexity at least `r` given any fixed condition `z`: the block has
exactly `2 ^ r` elements. -/
theorem exists_standardBlock_member_condK_ge
    (V : Map) (c : Nat.Partrec.Code) (m r : Nat)
    (x z : BitString) (hx : x ∈ standardBlock c m r x) :
    ∃ w ∈ standardBlock c m r x, (r : ENat) ≤ condK V w z :=
  exists_condK_ge_of_finset_card_pow V (standardBlock c m r x) z r
    (le_of_eq (card_standardBlock_of_mem c m r x hx).symm)
/-- Cardinality of a standard block from a set bit alone (no membership witness
needed): if bit `j` of `omegaCount c m` is set, the block has exactly `2 ^ j`
elements.  This is the `testBit`-keyed companion of `card_standardBlock_of_mem`,
used to extract an incompressible block member before any member is known. -/
theorem card_standardBlock_of_testBit
    (c : Nat.Partrec.Code) (m j : ℕ) (x : BitString)
    (hbit : (omegaCount c m).testBit j = true) :
    (standardBlock c m j x).card = 2 ^ j := by
  unfold standardBlock
  rw [if_pos hbit, List.toFinset_card_of_nodup]
  · simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    have hfit :=
      standardBlock_start_add_size_le
        (n := omegaCount c m) hbit
    change
      2 ^ j ≤
        (completedBoundedOutput c m).length -
          omegaCount c m / 2 ^ (j + 1) * 2 ^ (j + 1)
    change
      2 ^ j ≤
        omegaCount c m -
          omegaCount c m / 2 ^ (j + 1) * 2 ^ (j + 1)
    omega
  · exact ((boundedOutputStage_nodup c m
      (maxHaltingStage c m)).drop.take)

/-- **Genuine standard-block member, Omega-independent lower bound.**  There is a
uniform constant `C` such that for every bound `m ≥ C` and every `t ≤ m`, the
completed bound-`m` enumeration has a standard block of exponent `r ≥ m - C`
containing an actual string `x` for which
`t + r ≤ C(x) + C(Ω_t | x) + O(log m)`.

The proof combines: (1) the lower bound `2^(m-C) ≤ omegaCount c m`, which via
`exists_high_testBit_of_pow_le` produces a set bit at exponent `r ≥ m - C`; (2)
incompressibility for finite sets (`exists_condK_ge_of_finset_card_pow`) applied
to that `2^r`-element block conditioned on `Ω_t`, giving a member `x` with
`C(x | Ω_t) ≥ r`; (3) plain symmetry of information
(`plainK_add_condK_symmetry`), `C(Ω_t) + C(x | Ω_t) ≤ C(x) + C(Ω_t | x) + O(log)`;
and (4) the complexity pin `C(Ω_t) ≥ t - O(1)`.  Membership certifies
`C(x) ≤ m` directly.  All slack is at the length scale of `m`. -/
theorem exists_large_standardBlock_member_omega_independent
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∃ C, ∀ m t, C ≤ m → t ≤ m →
      ∃ r x,
        m - C ≤ r ∧
        x ∈ standardBlock c m r x ∧
        plainK V x ≤ (m : ENat) ∧
        ((t + r : Nat) : ENat) ≤
          plainK V x +
            condK V (omegaFixedCode c t) x +
            (logSlack C m : ENat) := by
  obtain ⟨C₁, hC₁⟩ := omegaCount_lower_of_plainK_length V hV c hc
  obtain ⟨C₂, hC₂⟩ := plainK_omegaFixedCode_lower V hV c hc
  obtain ⟨C₃, hC₃⟩ := plainK_omegaFixedCode_upper V hV c
  obtain ⟨C₅, hC₅⟩ := condKLePlainK V hV
  obtain ⟨C₄, hSOI⟩ := plainK_add_condK_symmetry V U hV hU
  obtain ⟨C', hC'⟩ := logSlack_linear_bound C₄ 1 (C₃ + C₅)
  refine ⟨C₁ + C₂ + C' + 1, fun m t hCm htm => ?_⟩
  set C := C₁ + C₂ + C' + 1 with hCdef
  -- Step 1: a set bit of `omegaCount c m` at exponent `r ≥ m - C₁`.
  have hC₁m : C₁ ≤ m := by omega
  have hpow : 2 ^ (m - C₁) ≤ omegaCount c m := hC₁ m hC₁m
  obtain ⟨r, hr_ge, hbit⟩ := exists_high_testBit_of_pow_le hpow
  -- Step 2: an incompressible member `x` of the `2^r`-element block.
  have hcard : 2 ^ r ≤ (standardBlock c m r []).card :=
    le_of_eq (card_standardBlock_of_testBit c m r [] hbit).symm
  obtain ⟨x, hx_mem, hxcond⟩ :=
    exists_condK_ge_of_finset_card_pow V (standardBlock c m r [])
      (omegaFixedCode c t) r hcard
  have hx_mem' : x ∈ standardBlock c m r x := hx_mem
  -- Step 3: membership pins `C(x) ≤ m`.
  have hx_completed : x ∈ completedBoundedOutput c m :=
    mem_completedBoundedOutput_of_mem_standardBlock c m r x hx_mem'
  have hplainx : plainK V x ≤ (m : ENat) :=
    (mem_completedBoundedOutput_iff_plainK_le hc m x).mp hx_completed
  refine ⟨r, x, by omega, hx_mem', hplainx, ?_⟩
  -- Step 4: symmetry of information, at length scale `N = m + C₃ + C₅`.
  set Ω := omegaFixedCode c t with hΩ
  set N := m + C₃ + C₅ with hN
  have hxN : plainK V x ≤ (N : ENat) :=
    hplainx.trans (by exact_mod_cast (by omega : m ≤ N))
  have hΩupper : plainK V Ω ≤ ((t + C₃ : ℕ) : ENat) := hC₃ t
  have hΩN : plainK V Ω ≤ (N : ENat) :=
    hΩupper.trans (by exact_mod_cast (by omega : t + C₃ ≤ N))
  have hcondΩxN : condK V Ω x ≤ (N : ENat) := by
    refine (hC₅ Ω x).trans ?_
    refine (add_le_add hΩupper (le_refl (C₅ : ENat))).trans ?_
    have hcast : ((t + C₃ : ℕ) : ENat) + (C₅ : ENat) = ((t + C₃ + C₅ : ℕ) : ENat) := by
      push_cast; ring
    rw [hcast]
    exact_mod_cast (by omega : t + C₃ + C₅ ≤ N)
  have hsym := hSOI x Ω N hxN hΩN hcondΩxN
  -- Lower bound on the symmetric left-hand side.
  have hlow : (t : ENat) + (r : ENat) ≤ plainK V Ω + condK V x Ω + (C₂ : ENat) := by
    calc (t : ENat) + (r : ENat)
        ≤ (plainK V Ω + (C₂ : ENat)) + condK V x Ω := add_le_add (hC₂ t) hxcond
      _ = plainK V Ω + condK V x Ω + (C₂ : ENat) := by rw [add_right_comm]
  -- Fold the slack.
  have hslacknat : logSlack C₄ N + C₂ ≤ logSlack C m := by
    have hNeq : N = 1 * m + (C₃ + C₅) := by rw [hN]; omega
    have hlin : logSlack C₄ N ≤ logSlack C' m := by rw [hNeq]; exact hC' m
    have hC₂slack : C₂ ≤ logSlack C₂ m := by unfold logSlack; exact Nat.le_add_left _ _
    calc logSlack C₄ N + C₂
        ≤ logSlack C' m + logSlack C₂ m := by omega
      _ = logSlack (C' + C₂) m := logSlack_add_const C' C₂ m
      _ ≤ logSlack C m := logSlack_mono_left (by omega) m
  calc ((t + r : Nat) : ENat)
      = (t : ENat) + (r : ENat) := by rw [Nat.cast_add]
    _ ≤ plainK V Ω + condK V x Ω + (C₂ : ENat) := hlow
    _ ≤ (plainK V x + condK V Ω x + (logSlack C₄ N : ENat)) + (C₂ : ENat) :=
        add_le_add hsym (le_refl (C₂ : ENat))
    _ = plainK V x + condK V Ω x + ((logSlack C₄ N + C₂ : ℕ) : ENat) := by
        rw [add_assoc, ← Nat.cast_add]
    _ ≤ plainK V x + condK V Ω x + (logSlack C m : ENat) :=
        add_le_add (le_refl _) (by exact_mod_cast hslacknat)

end Kolmogorov
