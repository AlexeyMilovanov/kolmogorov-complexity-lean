import KolmogorovMathlib.Restricted.Improving
import KolmogorovMathlib.Restricted.GapCountingIn
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Deficiencies
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems
import KolmogorovMathlib.Restricted.DeficiencyEquiv.ProgrammedFamilies
import KolmogorovMathlib.Restricted.DeficiencyEquiv.MarkedCodeSelectors

/-!
# Deficiency and optimality gap inside a restricted family

The equivalence, for models drawn from a fixed enumerable family, between having a large
optimality gap and admitting many descriptions. `ManyIJDescriptionsMem` counts the descriptions
of a string by sets of the family of complexity at most `i` and size at most `2 ^ j`; it is
monotone in the size bound and downwards in the multiplicity, and
`manyIJDescriptionsMem_k_le_i_add_one` caps the multiplicity by the number of available
descriptions. `uniform_manyIJDescriptionsMem_of_realizedSetOptimalityGap` turns an optimality gap
into that multiplicity, and the conclusions are `restricted_deficiencies_theorem_tight`,
`restricted_stochasticity_to_optimal_set_thm` and
`restricted_improving_descriptions_conditional`.

Source: VS40, the restricted form of the deficiency and improving-descriptions theorems.
-/

namespace Kolmogorov

open CodedFiniteDistribution
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Sound form of `uniform_familyComplexityRefinedSet`: the constant is chosen
after the enumerator. -/
theorem uniform_familyComplexityRefinedSet_ofEnum
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (p : BitString) (mem : Finset BitString → Prop) (enum : BitString → ℕ → List BitString)
    (henum : Computable (fun p_t : BitString × ℕ => enum p_t.1 p_t.2))
    (hmono : ∀ t, enum p t <+: enum p (t + 1))
    (hsound : ∀ t, ∀ w ∈ enum p t, ∃ (S : Finset BitString) (hS : S.Nonempty),
      mem S ∧ w = (codedUniformOn S hS).code)
    (hcomplete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S →
      ∃ t, (codedUniformOn S hS).code ∈ enum p t) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsMem mem U x i j k →
      k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), mem S ∧ x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) : ENat) ∧
        S.card ≤ 2 ^ (j + logSlack c (n + i + j)) := by
  obtain ⟨c, hc⟩ := exists_familyComplexityRefinedSet U hU
    (uniformPreFamily p mem enum henum hmono hsound hcomplete)
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hmemS, hxS, hcomp, hcard⟩ := hc x n i j k hn
    ((manyIJDescriptionsMem_iff_in p mem enum henum hmono hsound hcomplete
      U x i j k).mp hmany) hk
  exact ⟨S, hS, hmemS.1, hxS, hcomp, hcard⟩

/-- A single set of the family containing `x`, of complexity at most `i` and size at most `2 ^ j`,
already witnesses multiplicity `2 ^ 0`. -/
theorem manyIJDescriptionsMem_zero_of_mem {mem : Finset BitString → Prop} {U : Map} {x :
    BitString} {A : Finset BitString} {i j : ℕ}
    (hA : A.Nonempty) (hx : x ∈ A) (hmem : mem A) (hi : setComplexity U A hA ≤ (i : ENat))
    (hj : A.card ≤ 2 ^ j) :
    ManyIJDescriptionsMem mem U x i j 0 := by
  classical
  unfold ManyIJDescriptionsMem
  rw [pow_zero]
  refine Finset.card_pos.mpr ?_
  refine ⟨A, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hx⟩
  unfold descriptionsWithComplexityLeAndSizeLeMem
  rw [Finset.mem_filter]
  refine ⟨?_, hmem⟩
  unfold descriptionsWithComplexityLeAndSizeLe
  rw [Finset.mem_filter]
  exact ⟨mem_descriptionsWithComplexityLe_of_complexity hA hi, hj⟩

/-- Description multiplicity for a predicate family is monotone in the size bound `j`. -/
theorem ManyIJDescriptionsMem.mono_j {mem : Finset BitString → Prop} {U : Map} {x : BitString}
    {i j j' k : ℕ}
    (h : ManyIJDescriptionsMem mem U x i j k)
        (hj : j ≤ j') : ManyIJDescriptionsMem mem U x i j' k := by
  classical
  unfold ManyIJDescriptionsMem at *
  refine h.trans (Finset.card_le_card ?_)
  refine Finset.filter_subset_filter _ ?_
  intro S hS
  unfold descriptionsWithComplexityLeAndSizeLeMem at hS ⊢
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨descriptionsWithComplexityLeAndSizeLe_subset_of_le_right U i hj hS.1, hS.2⟩

/-- Description multiplicity for a predicate family is monotone downwards in `k`. -/
theorem ManyIJDescriptionsMem.mono_k {mem : Finset BitString → Prop} {U : Map} {x : BitString}
    {i j k k' : ℕ}
    (h : ManyIJDescriptionsMem mem U x i j k)
        (hk : k' ≤ k) : ManyIJDescriptionsMem mem U x i j k' := by
  unfold ManyIJDescriptionsMem at *
  exact le_trans (Nat.pow_le_pow_right (by norm_num) hk) h

/-- A set with optimality gap `delta` and deficiency `d` for `x` forces `x` to have
`2 ^ (delta - d - slack)` descriptions in the family, with `slack` logarithmic in the
parameters plus the complexity of the program defining the family. -/
theorem uniform_manyIJDescriptionsMem_of_realizedSetOptimalityGap (U : Map)
    (hU : IsOptimalPrefixConditional U) :
  ∃ c : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop),
    IsProgramForFamily p mem →
    ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n delta d i j kx c_soi : ℕ),
    x.length = n →
    mem A →
    RealizedSetOptimalityGap U A hA x delta i j kx →
    CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
    d ≤ delta + c_soi →
    ∃ slack : ℕ, slack ≤ logSlack c (n + delta + d) + (KPPlain U p).toNat ∧
      ManyIJDescriptionsMem mem U x i j (delta - d - slack) := by
  rcases gap_lowerBound_conditional_setComplexity_tight U hU with ⟨c1, hc1⟩
  rcases uniform_description_count_of_conditional_complexity_gap U hU with ⟨c2, hc2⟩
  rcases gapCounting_slack_arithmetic U hU c1 c2 with ⟨c3, hc3⟩
  refine ⟨c3, fun p mem hp
      A hA x n delta d i j kx c_soi hn hmem h_realized hdef_cond hd => ?_⟩
  have hxA := h_realized.1
  have hi := h_realized.2.1
  have hj := h_realized.2.2.1
  have hj_lower := h_realized.2.2.2.1
  have hkx := h_realized.2.2.2.2.1
  have hdelta_eq := h_realized.2.2.2.2.2
  have hi_bound : (i : ENat) ≤ KPPlain U x + (delta : ENat) := by
    have hkx_eq : KPPlain U x = (kx : ENat) := hkx.symm
    rw [hkx_eq]
    norm_cast
    omega
  rcases card_le_of_deficiency hxA hdef_cond with ⟨j_opt, hj_opt, hj_bound⟩
  have h_gap := hc1 A hA x n delta d i j kx c_soi hn
    ⟨hxA, hi, hj, hj_lower, hkx, hdelta_eq⟩ hdef_cond hd
  have hj_min : A.card ≤ 2 ^ min j j_opt := by
    by_cases hle : j ≤ j_opt
    · rw [Nat.min_eq_left hle]
      exact hj
    · rw [Nat.min_eq_right (le_of_not_ge hle)]
      exact hj_opt
  clear hdelta_eq
  set kp := (KPPlain U p).toNat
  have hkp_eq : (kp : ENat) = KPPlain U p := ENat.natCast_toNat (KPPlain_ne_top_of_optimal U hU p)
  set slack := logSlack c3 (n + delta + d) + kp
  use slack
  refine ⟨le_rfl, ?_⟩
  by_cases h_zero : delta - d ≤ slack
  · rw [Nat.sub_eq_zero_of_le h_zero]
    exact manyIJDescriptionsMem_zero_of_mem hA hxA hmem (le_of_eq hi) hj
  · by_contra hnot_goal
    have hnot_min :
        ¬ ManyIJDescriptionsMem mem U x i (min j j_opt) (delta - d - slack) := by
      intro hmany
      exact hnot_goal (ManyIJDescriptionsMem.mono_j hmany (min_le_left _ _))
    have h_count := hc2 p mem hp
      A hA x n i (min j j_opt) (delta - d - slack) kx
      hn hmem hxA (le_of_eq hi) hj_min hkx hnot_min
    have h_count' :
        KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤
          (delta - d - slack + logSlack c2 (n + i + min j j_opt) + kp : ENat) := by
      rw [← hkp_eq] at h_count
      simpa using h_count
    have h_arith := hc3 n delta d i (min j j_opt) x (codedUniformOn A hA).code
      hn hi_bound (le_trans (mod_cast min_le_right _ _) hj_bound)
    have hsum_lt :
        logSlack c2 (n + i + min j j_opt) + logSlack c1 (n + delta + d) <
          logSlack c3 (n + delta + d) := by
      simpa using h_arith
    have hslack_lt : slack < delta - d := Nat.lt_of_not_ge h_zero
    have hnat_lt :
        delta - d - slack + logSlack c2 (n + i + min j j_opt) + kp +
            logSlack c1 (n + delta + d) < delta - d := by
      omega
    have hcontra : (delta - d : ENat) < (delta - d : ENat) := by
      calc
        (delta - d : ENat)
            ≤ KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) +
                (logSlack c1 (n + delta + d) : ENat) := h_gap
        _ ≤ (delta - d - slack + logSlack c2 (n + i + min j j_opt) + kp : ENat) +
                (logSlack c1 (n + delta + d) : ENat) := by
              exact add_le_add h_count' le_rfl
        _ = (delta - d - slack + logSlack c2 (n + i + min j j_opt) + kp +
                logSlack c1 (n + delta + d) : ENat) := by
              ring
        _ < (delta - d : ENat) := by
              exact_mod_cast hnat_lt
    exact not_lt_of_ge le_rfl hcontra

/-- There are at most `2 ^ (i + 1)` descriptions of complexity at most `i`, so the multiplicity
exponent satisfies `k ≤ i + 1`. -/
theorem manyIJDescriptionsMem_k_le_i_add_one {mem : Finset BitString → Prop} {U : Map}
    {x : BitString} {i j k : ℕ} (h : ManyIJDescriptionsMem mem U x i j k) : k ≤ i + 1 := by
  contrapose! h
  simp only [ManyIJDescriptionsMem, not_le]
  apply lt_of_le_of_lt (Finset.card_le_card ?_) ?_
  · exact descriptionsWithComplexityLeAndSizeLe U i j
  · simp +contextual [Finset.subset_iff, descriptionsWithComplexityLeAndSizeLeMem]
  · exact lt_of_le_of_lt (card_descriptionsWithComplexityLeAndSizeLe U i j)
      (pow_lt_pow_right₀ (by decide) h)

/-- From a set with optimality gap `delta` and deficiency `d` one obtains a set of the family
containing `x` whose complexity is smaller by `delta - d` and whose optimality deficiency
exceeds `d` by a logarithmic term plus twice the complexity of the family's program. -/
theorem uniform_deficiencies_theorem_tight (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop),
      IsProgramForFamily p mem →
      ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j kx c_soi : ℕ),
      x.length = n →
      mem A →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), mem B ∧ x ∈ B ∧
        setComplexity U B hB + (delta - d : ℕ) ≤
          setComplexity U A hA + (logSlack c (n + delta + d) + 2 * KPPlain U p : ENat) ∧
        SetOptimalityDeficiencyLe U B hB x (d + logSlack c (n + delta + d) + 2 * (KPPlain U
            p).toNat) := by
  obtain ⟨c1, hc1⟩ := uniform_manyIJDescriptionsMem_of_realizedSetOptimalityGap U hU
  obtain ⟨c2, hc2⟩ := uniform_familyComplexityRefinedSet U hU
  obtain ⟨bb, hbb⟩ := visible_param_linear_bound U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c2 4 bb
  refine ⟨c1 + 2 * C0 + 2, ?_⟩
  intro p mem hp A hA x n delta d i j kx c_soi
    hn hmem h_realized h_def hd
  obtain ⟨slack1, hslack1, h_many⟩ :=
    hc1 p mem hp
      A hA x n delta d i j kx c_soi hn hmem h_realized h_def hd
  set k := min (delta - d - slack1) i with hk_def
  have hk_le_i : k ≤ i := Nat.min_le_right _ _
  have h_many' : ManyIJDescriptionsMem mem U x i j k :=
    ManyIJDescriptionsMem.mono_k h_many (Nat.min_le_left _ _)
  have hkc : delta - d - slack1 ≤ i + 1 :=
    manyIJDescriptionsMem_k_le_i_add_one h_many
  obtain ⟨B, hB, hmemB, hxB, hcompB, hsizeB⟩ :=
    hc2 p mem hp x n i j k hn h_many' hk_le_i
  set kp := (KPPlain U p).toNat with hkp_def
  have hkp_eq : (kp : ENat) = KPPlain U p := by
    rw [hkp_def]
    exact ENat.natCast_toNat (KPPlain_ne_top_of_optimal U hU p)
  rw [← hkp_eq] at hcompB
  have hj_bound : (j : ENat) + i ≤ KPPlain U x + delta := by
    have hdelta := h_realized.2.2.2.2.2
    have hkx := h_realized.2.2.2.2.1
    rw [show KPPlain U x = kx from hkx.symm]
    norm_cast
    omega
  have hvis : n + i + j ≤ 4 * (n + delta + d) + bb := by
    have h := hbb x n i j delta d hn hj_bound
    omega
  have hslackvis : logSlack c2 (n + i + j) ≤ logSlack C0 (n + delta + d) :=
    le_trans (logSlack_mono_right c2 hvis) (hC0 (n + delta + d))
  have hdk : (delta - d) - k ≤ slack1 + 1 := by omega
  have hdeltak : delta - k ≤ d + slack1 + 1 := by omega
  have hcomb : logSlack c1 (n + delta + d) + 2 * logSlack C0 (n + delta + d) + 1 ≤
      logSlack (c1 + 2 * C0 + 2) (n + delta + d) := by
    have e : logSlack (c1 + 2 * C0 + 2) (n + delta + d)
        = logSlack c1 (n + delta + d) + 2 * logSlack C0 (n + delta + d)
          + (2 * (Nat.bits (n + delta + d)).length + 2) := by
      unfold logSlack; ring
    omega
  refine ⟨B, hB, hmemB, hxB, ?_, ?_⟩
  · refine le_trans (add_le_add hcompB (le_refl ((delta - d : ℕ) : ENat))) ?_
    rw [show setComplexity U A hA = (i : ENat) from h_realized.2.1, ← hkp_eq]
    norm_cast
    omega
  · apply setOptimalityDeficiencyLe_of_profile hxB hcompB hsizeB
    rw [show KPPlain U x = kx from h_realized.2.2.2.2.1.symm]
    norm_cast
    change (i - k + logSlack c2 (n + i + j) + kp) + (j + logSlack c2 (n + i + j)) ≤
      kx + (d + logSlack (c1 + 2 * C0 + 2) (n + delta + d) + 2 * kp)
    have hdelta_eq := h_realized.2.2.2.2.2
    omega

/-- The uniform proposition for arbitrary enumerable 𝒜, with slack
`O(K(p) + log K(A) + log n + log log #A)`. The condition includes the enumeration
program `p`. -/
theorem restricted_stochasticity_to_optimal_set_uniform (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop),
      IsProgramForFamily p mem →
      ∀ (x : BitString) (n alpha beta : ℕ),
      x.length = n →
      (∃ (A : Finset BitString) (hA : A.Nonempty),
          mem A ∧ setComplexity U A hA ≤ (alpha : ENat) ∧
            CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x beta) →
      (∃ (A : Finset BitString) (hA : A.Nonempty),
          mem A ∧ setComplexity U A hA ≤
            (alpha + logSlack c (n + alpha + beta) + 2 * KPPlain U p : ENat) ∧
          SetOptimalityDeficiencyLe U A hA x
            (beta + logSlack c (n + alpha + beta) + 2 * (KPPlain U p).toNat)) := by
  obtain ⟨c_def, hc_def⟩ := uniform_deficiencies_theorem_tight U hU
  obtain ⟨c_br, hc_br⟩ := restricted_exists_realizedGap_of_member U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c_def 4 c_br
  refine ⟨max (c_br + C0) (c_def + c_br + 1) + 1, ?_⟩
  intro p mem hp x n alpha beta hn hyp
  obtain ⟨A, hA, hmemA, hcompA, hdefA⟩ := hyp
  obtain ⟨delta, i, j, kx, d, hgap, hdef, hdd, hi, hd, hlin⟩ :=
    hc_br A hA x n alpha beta hn hcompA hdefA
  obtain ⟨B, hB, hmemB, hxB, hcompB, hoptB⟩ :=
    hc_def p mem hp A hA x n delta d i j kx c_br hn hmemA hgap hdef hdd
  have hlogSlack : logSlack c_def (n + delta + d) ≤ logSlack C0 (n + alpha + beta) :=
    le_trans (logSlack_mono_right _ hlin) (hC0 _)
  have hcompA_i : setComplexity U A hA = (i : ENat) := hgap.2.1
  have hslack : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
      ≤ logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) := by
    have h1 : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
        ≤ logSlack (c_br + C0 + 1) (n + alpha + beta) := by
      unfold logSlack; ring_nf; linarith
    exact le_trans h1 (logSlack_mono_left (Nat.succ_le_succ (le_max_left _ _)) _)
  refine ⟨B, hB, hmemB, ?_, ?_⟩
  · have h_le1 : setComplexity U B hB ≤ (i : ENat) + (logSlack c_def (n + delta + d) : ENat) +
      2 * KPPlain U p := by
      rw [hcompA_i] at hcompB
      have h_rhs : (logSlack c_def (n + delta + d) + 2 * KPPlain U p : ENat) = (logSlack c_def
          (n + delta + d) : ENat) + 2 * KPPlain U p := by rfl
      rw [h_rhs] at hcompB
      have h_assoc : (i : ENat) + ((logSlack c_def (n + delta + d) : ENat) + 2 * KPPlain U p)
          = (i : ENat) + (logSlack c_def (n + delta + d) : ENat) +
            2 * KPPlain U p := by
        exact (add_assoc _ _ _).symm
      rw [h_assoc] at hcompB
      have h_self : setComplexity U B hB ≤ setComplexity U B hB + (delta - d : ℕ) :=
          le_add_right le_rfl
      exact le_trans h_self hcompB
    have h_le2 : (i : ENat) + (logSlack c_def (n + delta + d) : ENat) + 2 * KPPlain U p ≤
        (alpha : ENat) + (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1)
          (n + alpha + beta) : ENat) + 2 * KPPlain U p := by
      have hnat : i + logSlack c_def (n + delta + d) ≤ alpha + logSlack (max (c_br + C0)
          (c_def + c_br + 1) + 1) (n + alpha + beta) := by omega
      have hcast : (i : ENat) + (logSlack c_def (n + delta + d) : ENat) ≤ (alpha : ENat) +
          (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) : ENat) := by
        exact_mod_cast hnat
      exact add_le_add hcast le_rfl
    have h_le3 : (alpha : ENat) + (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1)
        (n + alpha + beta) : ENat) + 2 * KPPlain U p =
        (alpha + logSlack (max (c_br + C0) (c_def + c_br + 1) + 1)
          (n + alpha + beta) + 2 * KPPlain U p : ENat) := by rfl
    rw [← h_le3]
    exact le_trans h_le1 h_le2
  · refine hoptB.mono_beta ?_
    omega

/-- For a fixed family, a set with optimality gap `delta` and deficiency `d` for `x` forces
`2 ^ (delta - d - slack)` descriptions of `x` in the family, with logarithmic `slack`. -/
theorem restricted_manyIJDescriptionsIn_of_realizedSetOptimalityGap (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : PreDescriptionFamily) :
  ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n delta d i j kx c_soi : ℕ),
    x.length = n →
    𝒜.mem A →
    RealizedSetOptimalityGap U A hA x delta i j kx →
    CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
    d ≤ delta + c_soi →
    ∃ slack : ℕ, slack ≤ logSlack c (n + delta + d) ∧
      ManyIJDescriptionsIn 𝒜 U x i j (delta - d - slack) := by
  rcases gap_lowerBound_conditional_setComplexity_tight U hU with ⟨c1, hc1⟩
  rcases restricted_description_count_of_conditional_complexity_gap_aux U hU 𝒜 with ⟨c2, hc2⟩
  rcases gapCounting_slack_arithmetic U hU c1 c2 with ⟨c3, hc3⟩
  refine ⟨c3, fun A hA x n delta d i j kx c_soi hn hmem h_realized hdef_cond hd => ?_⟩
  have hxA := h_realized.1
  have hi := h_realized.2.1
  have hj := h_realized.2.2.1
  have hj_lower := h_realized.2.2.2.1
  have hkx := h_realized.2.2.2.2.1
  have hdelta := h_realized.2.2.2.2.2
  have hi_bound : (i : ENat) ≤ KPPlain U x + (delta : ENat) := by
    have hkx_eq : KPPlain U x = (kx : ENat) := hkx.symm
    rw [hkx_eq]
    norm_cast
    omega
  rcases card_le_of_deficiency hxA hdef_cond with ⟨j_opt, hj_opt, hj_bound⟩
  have h_gap := hc1 A hA x n delta d i j kx c_soi hn
    ⟨hxA, hi, hj, hj_lower, hkx, h_realized.2.2.2.2.2⟩ hdef_cond hd
  have hj_min : A.card ≤ 2 ^ min j j_opt := by
    by_cases hle : j ≤ j_opt
    · rw [Nat.min_eq_left hle]; exact hj
    · rw [Nat.min_eq_right (le_of_not_ge hle)]; exact hj_opt
  set slack := logSlack c3 (n + delta + d)
  use slack
  refine ⟨le_rfl, ?_⟩
  by_cases h_zero : delta - d ≤ slack
  · rw [Nat.sub_eq_zero_of_le h_zero]
    exact manyIJDescriptionsIn_zero_of_mem hA hxA hmem (le_of_eq hi) hj
  · by_contra hnot_goal
    have hnot_min : ¬ ManyIJDescriptionsIn 𝒜 U x i (min j j_opt) (delta - d - slack) := by
      intro hmany
      exact hnot_goal (ManyIJDescriptionsIn.mono_j hmany (min_le_left _ _))
    have h_count := hc2 A hA x n i (min j j_opt) (delta - d - slack) kx
      hn hmem hxA (le_of_eq hi) hj_min hkx hnot_min
    have h_arith := hc3 n delta d i (min j j_opt) x (codedUniformOn A hA).code
      hn hi_bound (le_trans (mod_cast min_le_right _ _) hj_bound)
    have hsum_lt : logSlack c2 (n + i + min j j_opt) + logSlack c1 (n + delta + d) <
          logSlack c3 (n + delta + d) := by simpa using h_arith
    have hnat_lt : delta - d - slack + logSlack c2 (n + i + min j j_opt) +
            logSlack c1 (n + delta + d) < delta - d := by omega
    have hcontra : (delta - d : ENat) < (delta - d : ENat) := by
      calc (delta - d : ENat)
            ≤ KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) +
                (logSlack c1 (n + delta + d) : ENat) := h_gap
        _ ≤ (delta - d - slack + logSlack c2 (n + i + min j j_opt) : ENat) +
                (logSlack c1 (n + delta + d) : ENat) :=
                    add_le_add (by exact_mod_cast h_count) le_rfl
        _ = (delta - d - slack + logSlack c2 (n + i + min j j_opt) +
                logSlack c1 (n + delta + d) : ENat) := by ring
        _ < (delta - d : ENat) := by exact_mod_cast hnat_lt
    exact not_lt_of_ge le_rfl hcontra

/-- The multiplicity exponent of restricted descriptions satisfies `k ≤ i + 1`. -/
theorem manyIJDescriptionsIn_k_le_i_add_one {𝒜 : PreDescriptionFamily} {U : Map}
    {x : BitString} {i j k : ℕ} (h : ManyIJDescriptionsIn 𝒜 U x i j k) : k ≤ i + 1 := by
  contrapose! h
  simp only [ManyIJDescriptionsIn, not_le]
  apply lt_of_le_of_lt (Finset.card_le_card ?_) ?_
  · exact descriptionsWithComplexityLeAndSizeLe U i j
  · simp +contextual [Finset.subset_iff, descriptionsWithComplexityLeAndSizeLeIn]
  · exact lt_of_le_of_lt (card_descriptionsWithComplexityLeAndSizeLe U i j)
      (pow_lt_pow_right₀ (by decide) h)

/-- For a fixed family, a set with optimality gap `delta` and deficiency `d` yields a family
member containing `x` with complexity smaller by `delta - d` and optimality deficiency larger
by only a logarithmic term. -/
theorem restricted_deficiencies_theorem_tight
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒜 : PreDescriptionFamily) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
      (n delta d i j kx c_soi : ℕ),
      x.length = n →
      𝒜.mem A →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), 𝒜.mem B ∧ x ∈ B ∧
        setComplexity U B hB + (delta - d : ℕ) ≤
          setComplexity U A hA + (logSlack c (n + delta + d) : ENat) ∧
        SetOptimalityDeficiencyLe U B hB x (d + logSlack c (n + delta + d)) := by
  obtain ⟨c1, hc1⟩ := restricted_manyIJDescriptionsIn_of_realizedSetOptimalityGap U hU 𝒜
  obtain ⟨c2, hc2⟩ := exists_familyComplexityRefinedSet U hU 𝒜
  obtain ⟨bb, hbb⟩ := visible_param_linear_bound U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c2 4 bb
  refine ⟨c1 + 2 * C0 + 2, ?_⟩
  intro A hA x n delta d i j kx c_soi hn hmem h_realized h_def hd
  obtain ⟨slack1, hslack1, h_many⟩ :=
    hc1 A hA x n delta d i j kx c_soi hn hmem h_realized h_def hd
  set k := min (delta - d - slack1) i with hk_def
  have hk_le_i : k ≤ i := Nat.min_le_right _ _
  have h_many' : ManyIJDescriptionsIn 𝒜 U x i j k :=
    ManyIJDescriptionsIn.mono_k h_many (Nat.min_le_left _ _)
  have hkc : delta - d - slack1 ≤ i + 1 :=
    manyIJDescriptionsIn_k_le_i_add_one h_many
  obtain ⟨B, hB, hmemB, hxB, hcompB, hsizeB⟩ :=
    hc2 x n i j k hn h_many' hk_le_i
  have hj_bound : (j : ENat) + i ≤ KPPlain U x + delta := by
    have hdelta := h_realized.2.2.2.2.2
    have hkx := h_realized.2.2.2.2.1
    rw [show KPPlain U x = kx from hkx.symm]
    norm_cast
    omega
  have hvis : n + i + j ≤ 4 * (n + delta + d) + bb := by
    have h := hbb x n i j delta d hn hj_bound
    omega
  have hslackvis : logSlack c2 (n + i + j) ≤ logSlack C0 (n + delta + d) :=
    le_trans (logSlack_mono_right c2 hvis) (hC0 (n + delta + d))
  have hdk : (delta - d) - k ≤ slack1 + 1 := by omega
  have hdeltak : delta - k ≤ d + slack1 + 1 := by omega
  have hcomb : logSlack c1 (n + delta + d) + 2 * logSlack C0 (n + delta + d) + 1 ≤
      logSlack (c1 + 2 * C0 + 2) (n + delta + d) := by
    have e : logSlack (c1 + 2 * C0 + 2) (n + delta + d)
        = logSlack c1 (n + delta + d) + 2 * logSlack C0 (n + delta + d)
          + (2 * (Nat.bits (n + delta + d)).length + 2) := by
      unfold logSlack; ring
    omega
  refine ⟨B, hB, hmemB, hxB, ?_, ?_⟩
  · refine le_trans (add_le_add hcompB (le_refl ((delta - d : ℕ) : ENat))) ?_
    rw [show setComplexity U A hA = (i : ENat) from h_realized.2.1]
    norm_cast
    omega
  · apply setOptimalityDeficiencyLe_of_profile hxB hcompB hsizeB
    rw [show KPPlain U x = kx from h_realized.2.2.2.2.1.symm]
    norm_cast
    change (i - k + logSlack c2 (n + i + j)) + (j + logSlack c2 (n + i + j)) ≤
      kx + (d + logSlack (c1 + 2 * C0 + 2) (n + delta + d))
    have hdelta_eq := h_realized.2.2.2.2.2
    omega

/-- A string with an `(alpha, beta)` description in the family has one whose deficiency is an
optimality deficiency, at a logarithmic cost in both parameters. -/
theorem restricted_stochasticity_to_optimal_set_thm (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : PreDescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n alpha beta : ℕ),
      x.length = n →
      (∃ (A : Finset BitString) (hA : A.Nonempty),
          𝒜.mem A ∧ setComplexity U A hA ≤ (alpha : ENat) ∧
            CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x beta) →
      (∃ (A : Finset BitString) (hA : A.Nonempty),
          𝒜.mem A ∧ setComplexity U A hA ≤
            (alpha + logSlack c (n + alpha + beta) : ENat) ∧
          SetOptimalityDeficiencyLe U A hA x (beta + logSlack c (n + alpha + beta))) := by
  obtain ⟨c_def, hc_def⟩ := restricted_deficiencies_theorem_tight U hU 𝒜
  obtain ⟨c_br, hc_br⟩ := restricted_exists_realizedGap_of_member U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c_def 4 c_br
  refine ⟨max (c_br + C0) (c_def + c_br + 1) + 1, ?_⟩
  intro x n alpha beta hn hyp
  obtain ⟨A, hA, hmemA, hcompA, hdefA⟩ := hyp
  obtain ⟨delta, i, j, kx, d, hgap, hdef, hdd, hi, hd, hlin⟩ :=
    hc_br A hA x n alpha beta hn hcompA hdefA
  obtain ⟨B, hB, hmemB, hxB, hcompB, hoptB⟩ :=
    hc_def A hA x n delta d i j kx c_br hn hmemA hgap hdef hdd
  have hlogSlack : logSlack c_def (n + delta + d) ≤ logSlack C0 (n + alpha + beta) :=
    le_trans (logSlack_mono_right _ hlin) (hC0 _)
  have hcompA_i : setComplexity U A hA = (i : ENat) := hgap.2.1
  have hslack : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
      ≤ logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) := by
    have h1 : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
        ≤ logSlack (c_br + C0 + 1) (n + alpha + beta) := by
      unfold logSlack; ring_nf; linarith
    exact le_trans h1 (logSlack_mono_left (Nat.succ_le_succ (le_max_left _ _)) _)
  refine ⟨B, hB, hmemB, ?_, ?_⟩
  · have h_le1 : setComplexity U B hB ≤ (i : ENat) + (logSlack c_def (n + delta + d) : ENat) := by
      rw [hcompA_i] at hcompB
      have h_self : setComplexity U B hB ≤ setComplexity U B hB + (delta - d : ℕ) :=
          le_add_right le_rfl
      exact le_trans h_self hcompB
    have h_le2 : (i : ENat) + (logSlack c_def (n + delta + d) : ENat) ≤ (alpha : ENat) +
        (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) : ENat) := by
      have hnat : i + logSlack c_def (n + delta + d) ≤ alpha + logSlack (max (c_br + C0)
          (c_def + c_br + 1) + 1) (n + alpha + beta) := by omega
      have hcast : (i : ENat) + (logSlack c_def (n + delta + d) : ENat) ≤ (alpha : ENat) +
          (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) : ENat) := by
        exact_mod_cast hnat
      exact hcast
    exact le_trans h_le1 h_le2
  · refine hoptB.mono_beta ?_
    omega

/-- `2 ^ k` descriptions of complexity at most `i` and size at most `2 ^ j` yield one description
of complexity about `i - k` and size about `2 ^ j`, up to logarithmic terms. -/
theorem restricted_improving_descriptions_conditional (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : DescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsIn 𝒜.toPre U x i j k →
      k ≤ i →
      InDescriptionProfileIn 𝒜 U x (i - k + logSlack c (n + i + j))
          (j + logSlack c (n + i + j)) := by
  obtain ⟨c, hc⟩ := exists_familyComplexityRefinedSet U hU 𝒜
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hmemS, hxS, hcomp, hcard⟩ := hc x n i j k hn hmany hk
  refine ⟨S, hS, hmemS, hxS, hcomp, hcard⟩

end Kolmogorov
