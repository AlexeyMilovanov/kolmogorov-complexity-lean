import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileCardinality
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Support

/-!
# Plain-complexity endpoint bound on a profile neighborhood

For a shift-closed profile `P` with finite endpoints `k_P = kp` and `n_P = np`,
every string whose plain description profile is `epsilon`-close to `P` has plain
complexity at most `kp + 2 * epsilon` up to logarithmic slack in `np`.

The argument is the two-part code: closeness to the attained endpoint `(kp, 0)`
gives an `(kp + epsilon, epsilon)`-description of `x`, and a member of a finite
set costs the set's complexity plus its log-cardinality, up to a logarithmic
correction which is absorbed by `logSlack` because `kp ≤ np`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Doubling a natural number costs at most one extra binary digit. -/
theorem length_natBits_two_mul_le (n : Nat) :
    (Nat.bits (2 * n)).length ≤ (Nat.bits n).length + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  refine Nat.size_le.mpr ?_
  have h : n < 2 ^ Nat.size n := Nat.lt_size_self n
  calc 2 * n < 2 * 2 ^ Nat.size n := by omega
    _ = 2 ^ (Nat.size n + 1) := by rw [pow_succ]; ring

/-- Plain complexity is bounded by the profile endpoint `k_P` plus twice the
neighborhood radius, up to logarithmic slack in the height endpoint `n_P`. -/
theorem plainK_upper_of_profileNeighborhood_endpoint
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (P : Set (Nat × Nat)) (kp np epsilon : Nat) (x : BitString),
      (∀ a b d, (a, b + d) ∈ P → (a + b, d) ∈ P) →
      epsilon ≤ kp →
      k_P P = (kp : ENat) →
      n_P P = (np : ENat) →
      x ∈ profileNeighborhood V P epsilon →
      plainK V x ≤
        ((kp + 2 * epsilon + logSlack c np : Nat) : ENat) := by
  obtain ⟨c₀, hc₀⟩ := plainK_mem_le_of_plainSetComplexity_le V hV
  refine ⟨c₀ + 2, ?_⟩
  intro P kp np epsilon x hshift heps hkP hnP hx
  -- The attained endpoint `(kp, 0)` of `P` gives a two-part description of `x`.
  have hend : (kp + epsilon, epsilon) ∈ plainDescriptionProfileSet V x :=
    plainProfile_endpoint_of_profileNeighborhood V P epsilon kp x hkP hx
  obtain ⟨S, hS, hxS, hcompl, hcard⟩ := hend
  have hlog : finiteSetLogCard S ≤ epsilon :=
    (finiteSetLogCard_le_iff S epsilon).mpr hcard
  have hmain := hc₀ S hS x (kp + epsilon) hxS hcompl
  refine hmain.trans ?_
  have hkpnp : kp ≤ np := by
    have h : (kp : ENat) ≤ (np : ENat) := by
      rw [← hkP, ← hnP]; exact k_P_le_n_P P hshift
    exact_mod_cast h
  have hbits : (Nat.bits (kp + epsilon)).length ≤ (Nat.bits np).length + 1 :=
    (length_natBits_mono (show kp + epsilon ≤ 2 * np by omega)).trans
      (length_natBits_two_mul_le np)
  have hmul : 2 * (Nat.bits np).length ≤ (c₀ + 2) * (Nat.bits np).length :=
    Nat.mul_le_mul_right _ (by omega)
  refine Nat.cast_le.mpr ?_
  unfold logSlack
  omega

/-- Sharpened endpoint bound: the logarithmic slack is measured on the visible
scale `k_P + 2 * epsilon` itself, so neither the height endpoint `n_P` nor
shift-closedness of `P` is needed. -/
theorem plainK_upper_of_profileNeighborhood_endpoint_sharp
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (P : Set (Nat × Nat)) (kp epsilon : Nat) (x : BitString),
      k_P P = (kp : ENat) →
      x ∈ profileNeighborhood V P epsilon →
      plainK V x ≤
        ((kp + 2 * epsilon + logSlack c (kp + 2 * epsilon) : Nat) : ENat) := by
  obtain ⟨c₀, hc₀⟩ := plainK_mem_le_of_plainSetComplexity_le V hV
  refine ⟨c₀ + 2, ?_⟩
  intro P kp epsilon x hkP hx
  have hend : (kp + epsilon, epsilon) ∈ plainDescriptionProfileSet V x :=
    plainProfile_endpoint_of_profileNeighborhood V P epsilon kp x hkP hx
  obtain ⟨S, hS, hxS, hcompl, hcard⟩ := hend
  have hlog : finiteSetLogCard S ≤ epsilon :=
    (finiteSetLogCard_le_iff S epsilon).mpr hcard
  refine (hc₀ S hS x (kp + epsilon) hxS hcompl).trans ?_
  have hbits : (Nat.bits (kp + epsilon)).length ≤
      (Nat.bits (kp + 2 * epsilon)).length :=
    length_natBits_mono (by omega)
  refine Nat.cast_le.mpr ?_
  unfold logSlack
  have hmul : 2 * (Nat.bits (kp + 2 * epsilon)).length ≤
      (c₀ + 2) * (Nat.bits (kp + 2 * epsilon)).length :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- Unconditional counting bound on a profile neighborhood: any finite family of
strings whose plain description profiles are `epsilon`-close to `P` has
log-cardinality at most `k_P + 2 * epsilon` up to logarithmic slack on the same
visible scale.  This is the `m_P_eps`-free part of Theorem `uppest`. -/
theorem finiteSetLogCard_le_of_subset_profileNeighborhood
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (P : Set (Nat × Nat)) (kp epsilon : Nat) (S : Finset BitString),
      k_P P = (kp : ENat) →
      (S : Set BitString) ⊆ profileNeighborhood V P epsilon →
      finiteSetLogCard S ≤ kp + 2 * epsilon + logSlack c (kp + 2 * epsilon) := by
  obtain ⟨c₀, hc₀⟩ := plainK_upper_of_profileNeighborhood_endpoint_sharp V hV
  refine ⟨c₀ + 1, ?_⟩
  intro P kp epsilon S hkP hS
  set B : Nat := kp + 2 * epsilon + logSlack c₀ (kp + 2 * epsilon) with hB
  have hbound : ∀ x ∈ S, condK V x [] ≤ (B : ENat) := by
    intro x hx
    exact hc₀ P kp epsilon x hkP (hS (by simpa using hx))
  have hcard : finiteSetLogCard S ≤ B + 1 :=
    finiteSetLogCard_le_condK_budget V [] B S hbound
  have hslack : logSlack c₀ (kp + 2 * epsilon) + 1 ≤
      logSlack (c₀ + 1) (kp + 2 * epsilon) := by
    unfold logSlack
    have : c₀ * (Nat.bits (kp + 2 * epsilon)).length ≤
        (c₀ + 1) * (Nat.bits (kp + 2 * epsilon)).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  omega

/-- A standard block containing `x` places `m_P_eps` below the block's own plain
complexity, provided the two-part budget `i + j` of the block stays within the
visible scale `k_P` plus logarithmic slack.  Here `i` bounds the complexity of
the block's canonical uniform code and `2 ^ j` is its cardinality. -/
theorem m_P_eps_le_standardBlock_plainComplexity_of_budget
    (V : Map) (P : Set (Nat × Nat)) (qc : Nat.Partrec.Code)
    (kp epsilon c kx i j : Nat) (x : BitString)
    (hx : x ∈ standardBlock qc kx j x)
    (hUp : IsUpperSet P)
    (hkP : k_P P = (kp : ENat))
    (hxP : x ∈ profileNeighborhood V P epsilon)
    (hi : plainK V (codedUniformOn (standardBlock qc kx j x) ⟨x, hx⟩).code ≤ (i : ENat))
    (hbudget : i + j ≤ kp + c * (kp + 2 * epsilon).bits.length) :
    m_P_eps P kp epsilon c ≤ (i : ENat) := by
  have hcard : (standardBlock qc kx j x).card ≤ 2 ^ j :=
    le_of_eq (card_standardBlock_of_mem qc kx j x hx)
  have hij : (i, j) ∈ plainDescriptionProfileSet V x :=
    ⟨standardBlock qc kx j x, ⟨x, hx⟩, hx, hi, hcard⟩
  exact m_P_eps_le_of_profileNeighborhood_point V P kp epsilon c i j x hUp hkP hxP hij
    hbudget

/-- Assembly step towards Lemma `omp`: given a standard block of `x` at level
`j` in the bound-`m` enumeration whose canonical code has exact plain complexity
`i`, every target index `t ≤ i` inside the linear bridge window is cheap given
`x`: the fixed-width finite Omega code `omegaFixedCode q t` costs only
logarithmic advice given `x`. -/
theorem condK_omegaFixedCode_le_of_standardBlock
    (V : Map) (hV : isOptimalConditional V)
    (q : Nat.Partrec.Code) (hq : IsCodeFor q V) :
    ∃ C : Nat, ∀ (m j i t : Nat) (x : BitString)
        (hx : x ∈ standardBlock q m j x),
      let hA : (standardBlock q m j x).Nonempty := ⟨x, hx⟩
      plainK V (codedUniformOn (standardBlock q m j x) hA).code = (i : ENat) →
      t ≤ i →
      i ≤ m + logSlack 1 m →
      condK V (omegaFixedCode q t) x ≤ (logSlack C m : ENat) := by
  obtain ⟨C₁, hstd⟩ := standard_description_simple_given_x V hV q hq
  obtain ⟨C₂, homega⟩ := prop_std_omega V hV q hq
  obtain ⟨C₃, hbridge⟩ := omegaFixedCode_bridge_linear V hV q hq 1
  obtain ⟨Ct, htrans⟩ := condK_trans_nat V hV
  refine ⟨4 * C₁ + 2 * C₂ + C₃ + 3 * Ct, ?_⟩
  intro m j i t x hx hA hplain hti him
  have h₁ : condK V (codedUniformOn (standardBlock q m j x) hA).code x ≤
      (logSlack C₁ m : ENat) := hstd m j x hx
  have h₂ : condK V (omegaFixedCode q i)
      (codedUniformOn (standardBlock q m j x) hA).code ≤ (logSlack C₂ m : ENat) :=
    (homega m j i x hx hplain).2
  have h₃ : condK V (omegaFixedCode q i) x ≤
      ((2 * logSlack C₁ m + logSlack C₂ m + Ct : Nat) : ENat) :=
    htrans x (codedUniformOn (standardBlock q m j x) hA).code (omegaFixedCode q i)
      (logSlack C₁ m) (logSlack C₂ m) h₁ h₂
  have htm : t ≤ m + logSlack 1 m := le_trans hti him
  have h₄ : condK V (omegaFixedCode q t) (omegaFixedCode q i) ≤
      ((t - i) + logSlack C₃ m : ENat) := hbridge m t i htm him
  have h₄' : condK V (omegaFixedCode q t) (omegaFixedCode q i) ≤
      ((logSlack C₃ m : Nat) : ENat) := by
    have hti0 : (t : ENat) - (i : ENat) = 0 :=
      tsub_eq_zero_of_le (by exact_mod_cast hti)
    simpa [hti0] using h₄
  have h₅ := htrans x (omegaFixedCode q i) (omegaFixedCode q t)
    (2 * logSlack C₁ m + logSlack C₂ m + Ct) (logSlack C₃ m) h₃ h₄'
  refine h₅.trans ?_
  refine Nat.cast_le.mpr ?_
  unfold logSlack
  nlinarith [Nat.zero_le (Ct * (Nat.bits m).length)]

/-- Slackened Omega target for a standard block.  The target index may exceed
the block-code complexity by `logSlack c_in m`; the linear Omega bridge pays
exactly that excess and the final cost remains logarithmic in `m`. -/
theorem condK_omegaFixedCode_le_of_standardBlock_slack
    (V : Map) (hV : isOptimalConditional V)
    (q : Nat.Partrec.Code) (hq : IsCodeFor q V) (c_in : Nat) :
    ∃ C : Nat, ∀ (m j i t : Nat) (x : BitString)
        (hx : x ∈ standardBlock q m j x),
      let hA : (standardBlock q m j x).Nonempty := ⟨x, hx⟩
      plainK V (codedUniformOn (standardBlock q m j x) hA).code = (i : ENat) →
      t ≤ i + logSlack c_in m →
      i ≤ m + logSlack 1 m →
      condK V (omegaFixedCode q t) x ≤ (logSlack C m : ENat) := by
  obtain ⟨C₁, hstd⟩ := standard_description_simple_given_x V hV q hq
  obtain ⟨C₂, homega⟩ := prop_std_omega V hV q hq
  obtain ⟨C₃, hbridge⟩ := omegaFixedCode_bridge_linear V hV q hq (1 + c_in)
  obtain ⟨Ct, htrans⟩ := condK_trans_nat V hV
  refine ⟨4 * C₁ + 2 * C₂ + C₃ + 3 * Ct + c_in, ?_⟩
  intro m j i t x hx hA hplain hti him
  have h₁ : condK V (codedUniformOn (standardBlock q m j x) hA).code x ≤
      (logSlack C₁ m : ENat) := hstd m j x hx
  have h₂ : condK V (omegaFixedCode q i)
      (codedUniformOn (standardBlock q m j x) hA).code ≤ (logSlack C₂ m : ENat) :=
    (homega m j i x hx hplain).2
  have h₃ : condK V (omegaFixedCode q i) x ≤
      ((2 * logSlack C₁ m + logSlack C₂ m + Ct : Nat) : ENat) :=
    htrans x (codedUniformOn (standardBlock q m j x) hA).code (omegaFixedCode q i)
      (logSlack C₁ m) (logSlack C₂ m) h₁ h₂
  have hiWindow : i ≤ m + logSlack (1 + c_in) m := by
    calc
      i ≤ m + logSlack 1 m := him
      _ ≤ (m + logSlack 1 m) + logSlack c_in m := Nat.le_add_right _ _
      _ = m + logSlack (1 + c_in) m := by
        rw [Nat.add_assoc, logSlack_add_const]
  have htWindow : t ≤ m + logSlack (1 + c_in) m := by
    calc
      t ≤ i + logSlack c_in m := hti
      _ ≤ (m + logSlack 1 m) + logSlack c_in m := Nat.add_le_add_right him _
      _ = m + logSlack (1 + c_in) m := by
        rw [Nat.add_assoc, logSlack_add_const]
  have h₄ : condK V (omegaFixedCode q t) (omegaFixedCode q i) ≤
      ((t - i) + logSlack C₃ m : ENat) := hbridge m t i htWindow hiWindow
  have htiGap : t - i ≤ logSlack c_in m :=
    Nat.sub_le_of_le_add (by simpa [Nat.add_comm] using hti)
  have h₄' : condK V (omegaFixedCode q t) (omegaFixedCode q i) ≤
      (logSlack (c_in + C₃) m : ENat) := by
    apply le_trans h₄
    apply Nat.cast_le.mpr
    rw [← logSlack_add_const]
    exact Nat.add_le_add_right htiGap _
  have h₅ := htrans x (omegaFixedCode q i) (omegaFixedCode q t)
    (2 * logSlack C₁ m + logSlack C₂ m + Ct) (logSlack (c_in + C₃) m) h₃ h₄'
  refine h₅.trans ?_
  apply Nat.cast_le.mpr
  unfold logSlack
  nlinarith [Nat.zero_le (Ct * (Nat.bits m).length)]

/-- Slack transfer to the visible base `np`: if `m` is at most `3 * np` up to
logarithmic slack in `np`, then any logarithmic slack measured on the joint
scale `m + np` is dominated by a logarithmic slack measured on `np` alone. -/
theorem logSlack_add_le_logSlack_of_le_three_mul_add_slack (c_in cc : Nat) :
    ∃ CC : Nat, ∀ m np : Nat,
      m ≤ 3 * np + logSlack c_in np → logSlack cc (m + np) ≤ logSlack CC np := by
  obtain ⟨CC, hCC⟩ := logSlack_linear_bound cc (4 + c_in) c_in
  refine ⟨CC, ?_⟩
  intro m np hm
  have hb : (Nat.bits np).length ≤ np := length_natBits_le_self np
  have hle : m + np ≤ (4 + c_in) * np + c_in := by
    unfold logSlack at hm
    nlinarith
  exact (logSlack_mono_right cc hle).trans (hCC np)

/-- Visible-endpoint Omega bridge.  Same conclusion as
`condK_omegaFixedCode_le_of_standardBlock_slack`, but every logarithmic term is
measured on the *visible* scale `np`, given that the block level `m` is at most
`3 * np` up to logarithmic slack. -/
theorem condK_omegaFixedCode_le_of_standardBlock_slack_np
    (V : Map) (hV : isOptimalConditional V)
    (q : Nat.Partrec.Code) (hq : IsCodeFor q V) (c_in : Nat) :
    ∃ C : Nat, ∀ (m j i t np : Nat) (x : BitString)
        (hx : x ∈ standardBlock q m j x),
      let hA : (standardBlock q m j x).Nonempty := ⟨x, hx⟩
      plainK V (codedUniformOn (standardBlock q m j x) hA).code = (i : ENat) →
      t ≤ i + logSlack c_in np →
      i ≤ m + logSlack c_in m →
      m ≤ 3 * np + logSlack c_in np →
      condK V (omegaFixedCode q t) x ≤ (logSlack C np : ENat) := by
  obtain ⟨C₁, hstd⟩ := standard_description_simple_given_x V hV q hq
  obtain ⟨C₂, homega⟩ := prop_std_omega V hV q hq
  obtain ⟨C₃, hbridge⟩ := omegaFixedCode_bridge_linear V hV q hq (2 * c_in)
  obtain ⟨Ct, htrans⟩ := condK_trans_nat V hV
  obtain ⟨CC, hCC⟩ :=
    logSlack_add_le_logSlack_of_le_three_mul_add_slack c_in
      (C₁ + C₂ + C₃ + c_in)
  refine ⟨8 * CC + 3 * Ct, ?_⟩
  intro m j i t np x hx hA hplain hti him hmnp
  -- All the logarithmic budgets appearing below live on the visible scale `np`.
  have hbase : ∀ cc : Nat, cc ≤ C₁ + C₂ + C₃ + c_in →
      ∀ r : Nat, r ≤ m + np → logSlack cc r ≤ logSlack CC np := by
    intro cc hcc r hr
    calc logSlack cc r ≤ logSlack (C₁ + C₂ + C₃ + c_in) (m + np) :=
          (logSlack_mono_right cc hr).trans (logSlack_mono_left hcc _)
      _ ≤ logSlack CC np := hCC m np hmnp
  have hm_le : m ≤ m + np := Nat.le_add_right _ _
  have hnp_le : np ≤ m + np := Nat.le_add_left _ _
  -- Step 1: the block code is cheap given `x`.
  have h₁ : condK V (codedUniformOn (standardBlock q m j x) hA).code x ≤
      (logSlack C₁ m : ENat) := hstd m j x hx
  -- Step 2: the Omega prefix at the block's own complexity is cheap given the block code.
  have h₂ : condK V (omegaFixedCode q i)
      (codedUniformOn (standardBlock q m j x) hA).code ≤ (logSlack C₂ m : ENat) :=
    (homega m j i x hx hplain).2
  have h₃ : condK V (omegaFixedCode q i) x ≤
      ((2 * logSlack C₁ m + logSlack C₂ m + Ct : Nat) : ENat) :=
    htrans x (codedUniformOn (standardBlock q m j x) hA).code (omegaFixedCode q i)
      (logSlack C₁ m) (logSlack C₂ m) h₁ h₂
  -- Step 3: the linear Omega bridge on the joint window `m + np`.
  have hiWindow : i ≤ (m + np) + logSlack (2 * c_in) (m + np) := by
    calc i ≤ m + logSlack c_in m := him
      _ ≤ (m + np) + logSlack (2 * c_in) (m + np) :=
        Nat.add_le_add hm_le
          ((logSlack_mono_right c_in hm_le).trans
            (logSlack_mono_left (by omega) _))
  have htWindow : t ≤ (m + np) + logSlack (2 * c_in) (m + np) := by
    have h1 : logSlack c_in m ≤ logSlack c_in (m + np) :=
      logSlack_mono_right c_in hm_le
    have h2 : logSlack c_in np ≤ logSlack c_in (m + np) :=
      logSlack_mono_right c_in hnp_le
    have h3 : logSlack c_in (m + np) + logSlack c_in (m + np) =
        logSlack (2 * c_in) (m + np) := by
      rw [logSlack_add_const]; ring_nf
    calc t ≤ i + logSlack c_in np := hti
      _ ≤ (m + logSlack c_in m) + logSlack c_in np := Nat.add_le_add_right him _
      _ ≤ (m + np) + logSlack (2 * c_in) (m + np) := by omega
  have h₄ : condK V (omegaFixedCode q t) (omegaFixedCode q i) ≤
      ((t - i) + logSlack C₃ (m + np) : ENat) :=
    hbridge (m + np) t i htWindow hiWindow
  have htiGap : t - i ≤ logSlack c_in np :=
    Nat.sub_le_of_le_add (by simpa [Nat.add_comm] using hti)
  have h₄' : condK V (omegaFixedCode q t) (omegaFixedCode q i) ≤
      ((logSlack c_in np + logSlack C₃ (m + np) : Nat) : ENat) := by
    refine le_trans h₄ ?_
    exact_mod_cast Nat.add_le_add_right htiGap _
  have h₅ := htrans x (omegaFixedCode q i) (omegaFixedCode q t)
    (2 * logSlack C₁ m + logSlack C₂ m + Ct)
    (logSlack c_in np + logSlack C₃ (m + np)) h₃ h₄'
  refine h₅.trans ?_
  refine Nat.cast_le.mpr ?_
  -- Step 4: fold every budget onto the visible scale `np`.
  have b₁ : logSlack C₁ m ≤ logSlack CC np := hbase C₁ (by omega) m hm_le
  have b₂ : logSlack C₂ m ≤ logSlack CC np := hbase C₂ (by omega) m hm_le
  have b₃ : logSlack C₃ (m + np) ≤ logSlack CC np := hbase C₃ (by omega) _ le_rfl
  have b₄ : logSlack c_in np ≤ logSlack CC np := hbase c_in (by omega) np hnp_le
  have hfinal : 8 * logSlack CC np + 3 * Ct ≤ logSlack (8 * CC + 3 * Ct) np := by
    unfold logSlack
    nlinarith [Nat.zero_le (Ct * (Nat.bits np).length)]
  omega

end Kolmogorov
