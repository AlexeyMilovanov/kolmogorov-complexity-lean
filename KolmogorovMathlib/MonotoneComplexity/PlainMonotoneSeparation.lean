import KolmogorovMathlib.MonotoneComplexity.PlainPrefixDips
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.MonotoneAPriori
import KolmogorovMathlib.MonotoneComplexity.APrioriBranching
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# Plain complexity dips below monotone and a priori complexity infinitely often

The lower half of the comparison between plain complexity and the monotone-type complexities.
`exists_incompressible_marked_nat` supplies, in each dyadic block, a length whose binary digits
are incompressible, and the constant bounds `KA_replicate_false_bounded`,
`KMOf_replicate_false_bounded` handle the all-zero sequence. Together they give
`exists_KA_sub_plainK_ge_logb_infinitely_often` and
`exists_KMOf_sub_plainK_ge_logb_infinitely_often`: some sequence has infinitely many prefixes on
which the a priori, respectively monotone, complexity exceeds the plain complexity by at least
`log₂` of the length. Combined with the reverse dips this yields the two-sided statements
`plainK_KA_log_gap_both_signs` and `plainK_KMOf_log_gap_both_signs`.

Source: SUV Theorem 86 and Problem 129.
-/

namespace Kolmogorov

/-- The prefixes of the constantly zero sequence are the all-zero strings. -/
lemma cantorPrefix_const_false (n : ℕ) :
    cantorPrefix (fun _ => false) n = List.replicate n false := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [cantorPrefix_getElem]

/-- The a priori complexity of the all-zero strings is bounded by a constant independent of the
length. -/
lemma KA_replicate_false_bounded : ∃ c : ℝ, ∀ n, KA (List.replicate n false) ≤ c := by
  have H : Computable (fun _ : ℕ => false) := Primrec.to_comp (Primrec.const false)
  obtain ⟨c, hc⟩ := (computable_iff_KA_prefixes_bounded (fun _ => false)).mp H
  use c
  intro n
  have := hc n
  rw [cantorPrefix_const_false] at this
  exact this

/-- The monotone complexity of the all-zero strings is bounded by a constant independent of the
length. -/
lemma KMOf_replicate_false_bounded {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℕ, ∀ n, KMOf D (List.replicate n false) ≤ c := by
  have H : Computable (fun _ : ℕ => false) := Primrec.to_comp (Primrec.const false)
  obtain ⟨c, hc⟩ := hD.2 _ (constStreamMap_isComputable _ H)
  use c
  intro n
  have h1 := hc (cantorPrefix (fun _ => false) n)
  have h2 : KMOf (constStreamMap (fun _ => false)) (cantorPrefix (fun _ => false) n) = 0 := by
    exact KMOf_constStreamMap_zero (fun _ => false) n
  rw [h2] at h1
  rw [cantorPrefix_const_false] at h1
  exact le_trans h1 (by simp)

/-- The binary digits of the length of a string are no harder to describe, up to a constant, than
the
string itself. -/
lemma plainK_natBits_length_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString, (plainK V (Nat.bits x.length)).toNat ≤ (plainK V x).toNat + c := by
  have H_comp : Computable (fun x : BitString => Nat.bits x.length) :=
    Primrec.to_comp (Primrec.comp Kolmogorov.primrec_natBits Primrec.list_length)
  obtain ⟨c, hc⟩ := plainK_map_le V hV _ H_comp
  use c
  intro x
  have h1 := hc x
  have hfin : plainK V x ≠ ⊤ := plainK_ne_top_of_isOptimalConditional hV x
  have hrhs_fin : plainK V x + (c : ENat) ≠ ⊤ :=
    WithTop.add_ne_top.mpr ⟨hfin, ENat.natCast_ne_top _⟩
  have H3 := ENat.toNat_le_toNat h1 hrhs_fin
  rw [ENat.toNat_add hfin (ENat.natCast_ne_top _), ENat.toNat_natCast] at H3
  exact H3

/-- Deleting the last bit of a string is computable. -/
lemma computable_dropLast : Computable (fun u : BitString => u.dropLast) := by
  have H : (fun u : BitString => u.dropLast) = (fun u => u.reverse.tail.reverse) := by
    funext u
    simp [List.dropLast_eq_take]
  rw [H]
  apply Primrec.to_comp
  refine Primrec.list_reverse.comp ?_
  refine Primrec.list_tail.comp ?_
  exact Primrec.list_reverse

/-- In every dyadic block `[2 ^ k, 2 ^ (k + 1))` there is a number whose binary digits have plain
complexity at least `k - c`. -/
lemma exists_incompressible_marked_nat (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℝ, ∀ k : ℕ, ∃ N : ℕ,
      2^k ≤ N ∧ N < 2^(k+1) ∧ (k : ℝ) - c ≤ ((plainK V (Nat.bits N)).toNat : ℝ) := by
  obtain ⟨c, hc⟩ := plainK_map_le V hV _ computable_dropLast
  use c
  intro k
  obtain ⟨u, hu_len, hu_K⟩ := exists_incompressible_string V [] k
  set N := decodeBits (u ++ [true])
  use N
  have h_len : u.length = k := hu_len
  have hpow1 : 2^k ≤ N := by rw [← h_len]; exact pow_length_le_decodeBits_append_true u
  have hpow2 : N < 2^(k+1) := by rw [← h_len]; exact decodeBits_append_true_lt u
  refine ⟨hpow1, hpow2, ?_⟩
  have h_drop : (Nat.bits N).dropLast = u := by
    dsimp [N]
    rw [dropLast_natBits_decodeBits_append_true]
  have H := hc (Nat.bits N)
  rw [h_drop] at H
  have H2 : (k : ENat) ≤ plainK V (Nat.bits N) + (c : ENat) := le_trans hu_K H
  have hfin : plainK V (Nat.bits N) ≠ ⊤ := plainK_ne_top_of_isOptimalConditional hV _
  have hrhs_fin : plainK V (Nat.bits N) + (c : ENat) ≠ ⊤ :=
    WithTop.add_ne_top.mpr ⟨hfin, ENat.natCast_ne_top _⟩
  have H3 := ENat.toNat_le_toNat H2 hrhs_fin
  rw [ENat.toNat_add hfin (ENat.natCast_ne_top _), ENat.toNat_natCast] at H3
  have H4 : k ≤ (plainK V (Nat.bits N)).toNat + c := H3
  have H5 : (k : ℝ) ≤ ((plainK V (Nat.bits N)).toNat : ℝ) + (c : ℝ) := by exact_mod_cast H4
  linarith

/-- A number below `2 ^ (k + 1)` has binary logarithm at most `k + 1`. -/
lemma logb_lt_of_pow_bounds {k N : ℕ} (h2 : N < 2 ^ (k + 1)) : Real.logb 2 N ≤ k + 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp only [CharP.cast_eq_zero, Real.logb_zero]
    positivity
  · have h2_le : N ≤ 2^(k+1) := Nat.le_of_lt h2
    have h_real : (N : ℝ) ≤ (2^(k+1) : ℕ) := by exact_mod_cast h2_le
    have H3 : ((2^(k+1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1 : ℕ) := by norm_cast
    have H4 : (2 : ℝ) ^ (k + 1 : ℕ) = (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
      exact Real.rpow_natCast 2 (k + 1) |>.symm
    have H5 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have h_log : Real.logb 2 (N : ℝ) ≤ Real.logb 2 ((2^(k + 1) : ℕ) : ℝ) :=
      (Real.logb_le_logb (by norm_num) (by exact_mod_cast hpos) (by positivity)).mpr h_real
    rw [H3, H4, H5] at h_log
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at h_log
    linarith

/-- Plain complexity exceeds a priori complexity by at least `log₂ n - c` for arbitrarily long
all-zero strings, so the two measures differ unboundedly. -/
theorem exists_plainK_sub_KA_ge_logb_of_length (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℝ, ∀ m : ℕ, ∃ n : ℕ, m < n ∧
      Real.logb 2 n - c ≤ ((plainK V (List.replicate n false)).toNat : ℝ)
                            - KA (List.replicate n false) := by
  obtain ⟨c1, hc1⟩ := exists_incompressible_marked_nat V hV
  obtain ⟨c2, hc2⟩ := KA_replicate_false_bounded
  obtain ⟨c3, hc3⟩ := plainK_natBits_length_le V hV
  use c1 + c2 + c3 + 1
  intro m
  obtain ⟨N, hN1, hN2, hN3⟩ := hc1 (m + 1)
  use N
  refine ⟨?_, ?_⟩
  · calc m < m + 1 := Nat.lt_succ_self _
      _ ≤ 2^(m+1) := Nat.lt_two_pow_self.le
      _ ≤ N := hN1
  · have h_K_N := hc3 (List.replicate N false)
    have h_len : (List.replicate N false).length = N := by simp
    rw [h_len] at h_K_N
    have h_K_N_real : ((plainK V (Nat.bits N)).toNat : ℝ) ≤
        ((plainK V (List.replicate N false)).toNat : ℝ) + (c3 : ℝ) := by exact_mod_cast h_K_N
    have h_KA := hc2 N
    have hlog := logb_lt_of_pow_bounds hN2
    linarith

/-- Plain complexity exceeds monotone complexity by at least `log₂ n - c` for arbitrarily long
all-zero strings. -/
theorem exists_plainK_sub_KMOf_ge_logb_of_length (V : Map) (hV : isOptimalConditional V)
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℝ, ∀ m : ℕ, ∃ n : ℕ, m < n ∧
      Real.logb 2 n - c ≤ ((plainK V (List.replicate n false)).toNat : ℝ)
                            - ((KMOf D (List.replicate n false)).toNat : ℝ) := by
  obtain ⟨c1, hc1⟩ := exists_incompressible_marked_nat V hV
  obtain ⟨c2, hc2⟩ := KMOf_replicate_false_bounded hD
  obtain ⟨c3, hc3⟩ := plainK_natBits_length_le V hV
  use c1 + c2 + c3 + 1
  intro m
  obtain ⟨N, hN1, hN2, hN3⟩ := hc1 (m + 1)
  use N
  refine ⟨?_, ?_⟩
  · calc m < m + 1 := Nat.lt_succ_self _
      _ ≤ 2^(m+1) := Nat.lt_two_pow_self.le
      _ ≤ N := hN1
  · have h_K_N := hc3 (List.replicate N false)
    have h_len : (List.replicate N false).length = N := by simp
    rw [h_len] at h_K_N
    have h_K_N_real : ((plainK V (Nat.bits N)).toNat : ℝ) ≤
        ((plainK V (List.replicate N false)).toNat : ℝ) + (c3 : ℝ) := by exact_mod_cast h_K_N
    have h_KM := hc2 N
    have h_KM_real : ((KMOf D (List.replicate N false)).toNat : ℝ) ≤ (c2 : ℝ) := by
      have hfin : KMOf D (List.replicate N false) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENat.natCast_ne_top _) h_KM
      have H3 := ENat.toNat_le_toNat h_KM (ENat.natCast_ne_top _)
      rw [ENat.toNat_natCast] at H3
      exact_mod_cast H3
    have hlog := logb_lt_of_pow_bounds hN2
    linarith

/-- Some sequence has infinitely many prefixes whose a priori complexity exceeds their plain
complexity by at least `log₂ n - c`; together with the previous separation neither measure
dominates the other. -/
theorem exists_KA_sub_plainK_ge_logb_infinitely_often (V : Map) (hV : isOptimalConditional V) :
    ∃ (w : CantorSeq) (c : ℝ),
      {n : ℕ | Real.logb 2 n - c ≤ KA (cantorPrefix w n)
                                 - ((plainK V (cantorPrefix w n)).toNat : ℝ)}.Infinite := by
  obtain ⟨w, hw⟩ := exists_cantorSeq_KA_prefix_ge_length
  obtain ⟨c, hc⟩ := plainK_prefix_le_length_sub_logb_infinitely_often V hV
  use w, c
  have h_inf := hc w
  apply Set.Infinite.mono _ h_inf
  intro n hn
  dsimp at hn ⊢
  have h1 : ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ (n : ℝ) - Real.logb 2 n + c := hn
  have h2 : (n : ℝ) ≤ KA (cantorPrefix w n) := hw n
  linarith

/-- Some sequence has infinitely many prefixes whose monotone complexity exceeds their plain
complexity by at least `log₂ n - c`. -/
theorem exists_KMOf_sub_plainK_ge_logb_infinitely_often (V : Map) (hV : isOptimalConditional V)
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D) :
    ∃ (w : CantorSeq) (c : ℝ),
      {n : ℕ | Real.logb 2 n - c ≤ ((KMOf D (cantorPrefix w n)).toNat : ℝ)
                                 - ((plainK V (cantorPrefix w n)).toNat : ℝ)}.Infinite := by
  obtain ⟨w, hw⟩ := exists_cantorSeq_KA_prefix_ge_length
  obtain ⟨c, hc⟩ := plainK_prefix_le_length_sub_logb_infinitely_often V hV
  obtain ⟨c2, hc2⟩ := exists_const_KA_le_KMOf hD
  use w, c + c2
  have h_inf := hc w
  apply Set.Infinite.mono _ h_inf
  intro n hn
  dsimp at hn ⊢
  have h1 : ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ (n : ℝ) - Real.logb 2 n + c := hn
  have h2 : (n : ℝ) ≤ KA (cantorPrefix w n) := hw n
  have h3 : KA (cantorPrefix w n) ≤ ((KMOf D (cantorPrefix w n)).toNat : ℝ) + c2 := hc2 _
  linarith

/-- Problem 129 -/
theorem plainK_KA_log_gap_both_signs (V : Map) (hV : isOptimalConditional V) :
    (∃ c : ℝ, ∀ m : ℕ, ∃ n : ℕ, m < n ∧
      Real.logb 2 n - c ≤ ((plainK V (List.replicate n false)).toNat : ℝ)
                            - KA (List.replicate n false)) ∧
    (∃ (w : CantorSeq) (c : ℝ),
      {n : ℕ | Real.logb 2 n - c ≤ KA (cantorPrefix w n)
                                 - ((plainK V (cantorPrefix w n)).toNat : ℝ)}.Infinite) :=
  ⟨exists_plainK_sub_KA_ge_logb_of_length V hV, exists_KA_sub_plainK_ge_logb_infinitely_often V hV⟩

/-- Theorem 86, sharp form (upper bound reused, not re-proved) -/
theorem plainK_KMOf_log_gap_both_signs (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    (∃ c : ℝ, ∀ x : BitString,
      |((plainK V x).toNat : ℝ) - ((KMOf D x).toNat : ℝ)| ≤
        2 * Real.logb 2 ((x.length : ℝ) + 1) + c) ∧
    (∃ c : ℝ, ∀ m : ℕ, ∃ n : ℕ, m < n ∧
      Real.logb 2 n - c ≤ ((plainK V (List.replicate n false)).toNat : ℝ)
                            - ((KMOf D (List.replicate n false)).toNat : ℝ)) ∧
    (∃ (w : CantorSeq) (c : ℝ),
      {n : ℕ | Real.logb 2 n - c ≤ ((KMOf D (cantorPrefix w n)).toNat : ℝ)
                                 - ((plainK V (cantorPrefix w n)).toNat : ℝ)}.Infinite) :=
  ⟨exists_const_abs_plainK_sub_KMOf_le_log V U hV hU hD,
   exists_plainK_sub_KMOf_ge_logb_of_length V hV hD,
   exists_KMOf_sub_plainK_ge_logb_infinitely_often V hV hD⟩

end Kolmogorov
