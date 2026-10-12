import KolmogorovMathlib.StrongMerging.Coding.Chain

/-!
# Strong merging, coding foundation IV: typicality, common information, mass (U04–U06)

`sublinear-merging.tex`, appendix "Coding lemmas and constants before asymptotic notation",
items 4–6.

* **U04, `UpperTypicality`.**  Input sufficiency gives `C(x | A) ≥ a - b_typ H` for the floor
  size bucket `a = ⌊log₂ |A|⌋` and `H = e + ⌈log₂ (n + 2)⌉`, and `a ≤ 2 n + b_size`
  (`upperTypicality`); the models and the tuple `((A, B), x)` have complexity `O(n + 1)`
  (`upperJointBound`), obtained from the crude joint bound before any chain rule.
* **U05, `UpperCommonInformation`.**  `C(D) ≤ I(A : B) + C(D | A) + C(D | B) + c log₂ (N + 2)`
  when the four joint complexities are at most `N` (`upperCommonInformation`), and its form with
  total endpoint costs `CT(D | A), CT(D | B) ≤ T` (`upperCommonInformation_total`).  Mutual
  information is signed (`mutualInfo`).
* **U06, `UpperMassTransfer`.**  `I(A : B) ≤ C(x) - t + 2 e + c log₂ (N + 2)` with
  `t = log₂ |A| + log₂ |B| - log₂ |A ∩ B|` (`upperMassTransfer_info`), and
  `t - log₂ |D| ≤ 2 T + 2 e + c log₂ (N + 2)` for every `D ∋ x` with endpoint costs `≤ T`
  (`upperMassTransfer`).  Only the upper inequality for `I` is used.

With `N = O(n + 1)` (`upperJointBound` and the crude joint bound `pairC_le_crude`) the errors
`2 e + c log₂ (N + 2)` are `O(H)` (`logb_linear_le_headerLog`).
-/

namespace Kolmogorov.StrongMerging

/-! ### Model-level notation -/

/-- `C(A, B)`: the joint complexity of two finite models, on their canonical codes. -/
noncomputable def setPairC (V : Map) (A B : Finset BitString) : ℝ :=
  pairC V (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)

/-- `I(A : B) = C(A) + C(B) - C(A, B)`: the signed mutual information of two finite models. -/
noncomputable def setMutualInfo (V : Map) (A B : Finset BitString) : ℝ :=
  mutualInfo V (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)

/-- `t = log₂ |A| + log₂ |B| - log₂ |A ∩ B|`: the overlap mass of two finite models, with the
real binary logarithm. -/
noncomputable def overlapMass (A B : Finset BitString) : ℝ :=
  Real.logb 2 A.card + Real.logb 2 B.card - Real.logb 2 (A ∩ B).card

/-- Mutual information of models in terms of `setC` and `setPairC`. -/
theorem setMutualInfo_eq (V : Map) (A B : Finset BitString) :
    setMutualInfo V A B = setC V A + setC V B - setPairC V A B :=
  rfl

/-! ### Arithmetic leaves -/

/-- The floor binary logarithm is at most the real binary logarithm (both are `0` at `0`). -/
theorem natLog_le_logb (N : ℕ) : (Nat.log 2 N : ℝ) ≤ Real.logb 2 N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hN), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'

/-- `log₂ (a n + b + 2) ≤ c ⌈log₂ (n + 2)⌉` with `c` depending only on `a, b`. -/
theorem logb_linear_le_headerLog (a b : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ, Real.logb 2 ((a : ℝ) * n + b + 2) ≤ c * headerLog n := by
  refine ⟨⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ + 1, fun n => ?_⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have h1 : (a : ℝ) * n + b + 2 ≤ ((a : ℝ) + b + 2) * ((n : ℝ) + 2) := by nlinarith
  have h2 : Real.logb 2 ((a : ℝ) * n + b + 2) ≤
      Real.logb 2 ((a : ℝ) + b + 2) + Real.logb 2 ((n : ℝ) + 2) := by
    rw [← Real.logb_mul (by positivity) (by positivity)]
    exact Real.logb_le_logb_of_le one_lt_two (by positivity) h1
  have h3 : Real.logb 2 ((n : ℝ) + 2) ≤ headerLog n := by
    have hh := headerLog_eq_ceil_logb n
    have h4 := Int.le_ceil (Real.logb 2 ((n : ℝ) + 2))
    rw [← hh] at h4
    exact_mod_cast h4
  have h5 : Real.logb 2 ((a : ℝ) + b + 2) ≤ ⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ := Nat.le_ceil _
  have hl1 : (1 : ℝ) ≤ headerLog n := by exact_mod_cast one_le_headerLog n
  have hC0 : (0 : ℝ) ≤ ⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ := Nat.cast_nonneg _
  have h6 : (⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ : ℝ) ≤
      ⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ * (headerLog n : ℝ) := le_mul_of_one_le_right hC0 hl1
  push_cast
  linarith

/-- A sufficient model of `x` contains `x`, so its real binary log-cardinality is nonnegative. -/
theorem logb_card_nonneg_of_mem {x : BitString} {A : Finset BitString} (hx : x ∈ A) :
    0 ≤ Real.logb 2 A.card :=
  Real.logb_nonneg one_lt_two (Nat.one_le_cast.2 (Finset.card_pos.2 ⟨x, hx⟩))

/-- An `e`-sufficient model of `x` has `C(A) ≤ C(x) + e`. -/
theorem setC_le_of_sufficient {V : Map} {x : BitString} {A : Finset BitString} {e : ℝ}
    (hA : IsSufficientModel V x A e) : setC V A ≤ plainC V x + e := by
  have h := hA.2
  have h0 := logb_card_nonneg_of_mem hA.1
  linarith

/-! ### U04: typicality and the joint bound -/

/-- **Node U04, `UpperTypicality`.**  For an optimal plain machine there are constants `b_typ`,
`b_size` such that every `e`-sufficient model `A` of an `n`-bit string `x`, `e ≤ n`, has
`C(x | A) ≥ a - b_typ (e + ⌈log₂ (n + 2)⌉)` and `a ≤ 2 n + b_size`, for the floor size bucket
`a = ⌊log₂ |A|⌋`. -/
theorem upperTypicality (V : Map) (hV : isOptimalConditional V) :
    ∃ btyp bsize : ℕ, ∀ (n e : ℕ) (x : BitString) (A : Finset BitString),
      x.length = n → e ≤ n → IsSufficientModel V x A e →
        (Nat.log 2 A.card : ℝ) - btyp * baseBudget n e ≤ condC V x (canonicalFiniteSetCode A) ∧
          Nat.log 2 A.card ≤ 2 * n + bsize := by
  obtain ⟨blit, hlit⟩ := plainC_le_length_add V hV
  obtain ⟨cp, hp⟩ := plainC_le_pairC_right V hV
  obtain ⟨cu, hu⟩ := upperComplexityChain_upper V hV
  obtain ⟨ccr, hcr⟩ := pairC_le_crude V hV
  obtain ⟨ch, hh⟩ := logb_linear_le_headerLog 7 (4 * blit + ccr)
  refine ⟨cu * ch + cp + 1, blit, fun n e x A hx hen hA => ?_⟩
  have hx' := hlit x
  rw [hx] at hx'
  have hen' : (e : ℝ) ≤ n := by exact_mod_cast hen
  have hsuf : plainC V (canonicalFiniteSetCode A) + Real.logb 2 A.card ≤ plainC V x + e := hA.2
  have hlog0 := logb_card_nonneg_of_mem hA.1
  have hnat := natLog_le_logb A.card
  have hCA0 := plainC_nonneg V (canonicalFiniteSetCode A)
  refine ⟨?_, ?_⟩
  · set a := canonicalFiniteSetCode A with ha
    have hK0 := pairC_nonneg V a x
    have hKle : pairC V a x ≤ ((7 : ℕ) : ℝ) * n + ((4 * blit + ccr : ℕ) : ℝ) := by
      have := hcr a x
      push_cast
      linarith
    have hL := (logb_add_two_mono hK0 hKle).trans (hh n)
    have hcu0 : (0 : ℝ) ≤ cu := Nat.cast_nonneg cu
    have hcuL := mul_le_mul_of_nonneg_left hL hcu0
    have hl1 : (1 : ℝ) ≤ headerLog n := by exact_mod_cast one_le_headerLog n
    have hcp : (cp : ℝ) ≤ cp * headerLog n := le_mul_of_one_le_right (Nat.cast_nonneg _) hl1
    have hpos1 : (0 : ℝ) ≤ (cu : ℝ) * ch * e := by positivity
    have hpos2 : (0 : ℝ) ≤ (cp : ℝ) * e := by positivity
    have h1 := hp a x
    have h2 := hu a x
    rw [baseBudget]
    push_cast
    linarith
  · have hreal : ((Nat.log 2 A.card : ℕ) : ℝ) ≤ ((2 * n + blit : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hreal

/-- **Joint complexity bound** (node U04): for `e`-sufficient models `A, B` of an `n`-bit string
`x`, `e ≤ n`, the complexities `C(A)`, `C(A, B)` and `C((A, B), x)` are at most
`b_joint (n + 1)`, with `b_joint` depending only on `V`. -/
theorem upperJointBound (V : Map) (hV : isOptimalConditional V) :
    ∃ bjoint : ℕ, ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString),
      x.length = n → e ≤ n → IsSufficientModel V x A e → IsSufficientModel V x B e →
        setC V A ≤ bjoint * (n + 1) ∧ setPairC V A B ≤ bjoint * (n + 1) ∧
          pairC V (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) x ≤
            bjoint * (n + 1) := by
  obtain ⟨blit, hlit⟩ := plainC_le_length_add V hV
  obtain ⟨ccr, hcr⟩ := pairC_le_crude V hV
  refine ⟨25 + 13 * blit + 4 * ccr, fun n e x A B hx hen hA hB => ?_⟩
  have hx' := hlit x
  rw [hx] at hx'
  have hen' : (e : ℝ) ≤ n := by exact_mod_cast hen
  have hA' : plainC V (canonicalFiniteSetCode A) ≤ plainC V x + e := setC_le_of_sufficient hA
  have hB' : plainC V (canonicalFiniteSetCode B) ≤ plainC V x + e := setC_le_of_sufficient hB
  have hAB := hcr (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)
  have hABx := hcr (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) x
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp1 : (0 : ℝ) ≤ (blit : ℝ) * n := by positivity
  have hp2 : (0 : ℝ) ≤ (ccr : ℝ) * n := by positivity
  have hb0 : (0 : ℝ) ≤ blit := Nat.cast_nonneg blit
  have hc0 : (0 : ℝ) ≤ ccr := Nat.cast_nonneg ccr
  have hAB' : setPairC V A B = plainC V
      (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) := rfl
  have hA'' : setC V A = plainC V (canonicalFiniteSetCode A) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hA'']
    push_cast
    nlinarith
  · rw [hAB']
    change plainC V (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) ≤
      3 * plainC V (canonicalFiniteSetCode A) + plainC V (canonicalFiniteSetCode B) + ccr at hAB
    push_cast
    nlinarith
  · change pairC V (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) x ≤
      3 * plainC V (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) +
        plainC V x + ccr at hABx
    change plainC V (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) ≤
      3 * plainC V (canonicalFiniteSetCode A) + plainC V (canonicalFiniteSetCode B) + ccr at hAB
    push_cast
    nlinarith

/-! ### U05: common information -/

/-- **Node U05, `UpperCommonInformation`.**  For an optimal plain machine there is a constant `c`
such that, whenever `C(d), C(a, b), C(a, d), C(b, d) ≤ N`,
`C(d) ≤ I(a : b) + C(d | a) + C(d | b) + c log₂ (N + 2)`, with signed mutual information. -/
theorem upperCommonInformation (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (N : ℝ) (a b d : BitString), plainC V d ≤ N → pairC V a b ≤ N →
      pairC V a d ≤ N → pairC V b d ≤ N →
        plainC V d ≤ mutualInfo V a b + condC V d a + condC V d b + c * Real.logb 2 (N + 2) := by
  obtain ⟨cs, hs⟩ := upperSubmodularity V hV
  obtain ⟨cu, hu⟩ := upperComplexityChain_upper V hV
  refine ⟨cs + 2 * cu, fun N a b d hd hab had hbd => ?_⟩
  have h1 := hs N a b d hd hab had hbd
  have h2 := hu a d
  have h3 := hu b d
  have hcu : (0 : ℝ) ≤ cu := Nat.cast_nonneg cu
  have h2' := mul_le_mul_of_nonneg_left (logb_add_two_mono (pairC_nonneg V a d) had) hcu
  have h3' := mul_le_mul_of_nonneg_left (logb_add_two_mono (pairC_nonneg V b d) hbd) hcu
  rw [mutualInfo]
  push_cast
  linarith

/-- **Node U05, total-endpoint form**: if `C(D), C(A, B), C(A, D), C(B, D) ≤ N` and
`CT(D | A), CT(D | B) ≤ T`, then `C(D) ≤ I(A : B) + 2 T + c log₂ (N + 2)`; the constant includes
the total-to-plain interpreter overhead. -/
theorem upperCommonInformation_total (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (N T : ℝ) (A B D : Finset BitString), setC V D ≤ N → setPairC V A B ≤ N →
      setPairC V A D ≤ N → setPairC V B D ≤ N → setTotalC D A ≤ T → setTotalC D B ≤ T →
        setC V D ≤ setMutualInfo V A B + 2 * T + c * Real.logb 2 (N + 2) := by
  obtain ⟨c₁, h₁⟩ := upperCommonInformation V hV
  obtain ⟨ct, ht⟩ := condC_le_totalC_add V hV
  refine ⟨c₁ + 2 * ct, fun N T A B D hD hAB hAD hBD hTA hTB => ?_⟩
  have h := h₁ N _ _ _ hD hAB hAD hBD
  have hA := ht (canonicalFiniteSetCode D) (canonicalFiniteSetCode A)
  have hB := ht (canonicalFiniteSetCode D) (canonicalFiniteSetCode B)
  have hTA' : totalC (canonicalFiniteSetCode D) (canonicalFiniteSetCode A) ≤ T := hTA
  have hTB' : totalC (canonicalFiniteSetCode D) (canonicalFiniteSetCode B) ≤ T := hTB
  have hN : 0 ≤ N := (plainC_nonneg V _).trans hD
  have hL := one_le_logb_add_two hN
  have hctL : (ct : ℝ) ≤ ct * Real.logb 2 (N + 2) := le_mul_of_one_le_right (Nat.cast_nonneg _) hL
  change plainC V (canonicalFiniteSetCode D) ≤
    mutualInfo V (canonicalFiniteSetCode A) (canonicalFiniteSetCode B) + 2 * T + _
  push_cast
  linarith

/-! ### U06: mass transfer -/

/-- **Node U06, `UpperMassTransfer`, information bound**: for `e`-sufficient models `A, B` of
`x`, if `C((A, B), x) ≤ N` then `I(A : B) ≤ C(x) - t + 2 e + c log₂ (N + 2)`, where
`t = log₂ |A| + log₂ |B| - log₂ |A ∩ B|` (`overlapMass`).  Only this upper inequality holds in
general. -/
theorem upperMassTransfer_info (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (N e : ℝ) (x : BitString) (A B : Finset BitString),
      IsSufficientModel V x A e → IsSufficientModel V x B e →
      pairC V (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) x ≤ N →
        setMutualInfo V A B ≤ plainC V x - overlapMass A B + 2 * e + c * Real.logb 2 (N + 2) := by
  obtain ⟨cp, hp⟩ := plainC_le_pairC_right V hV
  obtain ⟨cu, hu⟩ := upperComplexityChain_upper V hV
  obtain ⟨ci, hi⟩ := condC_le_logb_card_inter V hV
  refine ⟨cp + cu + ci, fun N e x A B hA hB hN => ?_⟩
  have hxAB : x ∈ A ∩ B := Finset.mem_inter.2 ⟨hA.1, hB.1⟩
  have h1 := hp (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) x
  have h2 := hu (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) x
  have h3 := hi A B x hxAB
  have hN0 : 0 ≤ N := (pairC_nonneg V _ x).trans hN
  have hL := one_le_logb_add_two hN0
  have hcu : (0 : ℝ) ≤ cu := Nat.cast_nonneg cu
  have h2' := mul_le_mul_of_nonneg_left (logb_add_two_mono (pairC_nonneg V _ x) hN) hcu
  have hcpL : (cp : ℝ) ≤ cp * Real.logb 2 (N + 2) := le_mul_of_one_le_right (Nat.cast_nonneg _) hL
  have hciL : (ci : ℝ) ≤ ci * Real.logb 2 (N + 2) := le_mul_of_one_le_right (Nat.cast_nonneg _) hL
  have sA : plainC V (canonicalFiniteSetCode A) + Real.logb 2 A.card ≤ plainC V x + e := hA.2
  have sB : plainC V (canonicalFiniteSetCode B) + Real.logb 2 B.card ≤ plainC V x + e := hB.2
  change plainC V (canonicalFiniteSetCode A) + plainC V (canonicalFiniteSetCode B) -
      plainC V (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) ≤
    plainC V x - (Real.logb 2 A.card + Real.logb 2 B.card - Real.logb 2 (A ∩ B).card) +
      2 * e + _
  push_cast
  linarith

/-- **Node U06, `UpperMassTransfer`.**  For `e`-sufficient models `A, B` of `x` and a model
`D ∋ x` with `CT(D | A), CT(D | B) ≤ T`, if the joint complexities `C((A, B), x)`, `C(D, x)`,
`C(D)`, `C(A, B)`, `C(A, D)`, `C(B, D)` are at most `N`, then
`t - log₂ |D| ≤ 2 T + 2 e + c log₂ (N + 2)` with `t = log₂ |A| + log₂ |B| - log₂ |A ∩ B|`. -/
theorem upperMassTransfer (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (N e T : ℝ) (x : BitString) (A B D : Finset BitString),
      IsSufficientModel V x A e → IsSufficientModel V x B e → x ∈ D →
      pairC V (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) x ≤ N →
      pairC V (canonicalFiniteSetCode D) x ≤ N → setC V D ≤ N → setPairC V A B ≤ N →
      setPairC V A D ≤ N → setPairC V B D ≤ N → setTotalC D A ≤ T → setTotalC D B ≤ T →
        overlapMass A B - Real.logb 2 D.card ≤ 2 * T + 2 * e + c * Real.logb 2 (N + 2) := by
  obtain ⟨cmi, hmi⟩ := upperMassTransfer_info V hV
  obtain ⟨cci, hci⟩ := upperCommonInformation_total V hV
  obtain ⟨cp, hp⟩ := plainC_le_pairC_right V hV
  obtain ⟨cu, hu⟩ := upperComplexityChain_upper V hV
  obtain ⟨cf, hf⟩ := condC_le_logb_card V hV
  refine ⟨cmi + cci + cp + cu + cf, fun N e T x A B D hA hB hxD hN hDx hD hAB hAD hBD hTA hTB =>
    ?_⟩
  have h1 := hmi N e x A B hA hB hN
  have h2 := hci N T A B D hD hAB hAD hBD hTA hTB
  have h3 := hp (canonicalFiniteSetCode D) x
  have h4 := hu (canonicalFiniteSetCode D) x
  have h5 := hf D x hxD
  have hN0 : 0 ≤ N := (pairC_nonneg V _ x).trans hN
  have hL := one_le_logb_add_two hN0
  have hcu : (0 : ℝ) ≤ cu := Nat.cast_nonneg cu
  have h4' := mul_le_mul_of_nonneg_left (logb_add_two_mono (pairC_nonneg V _ x) hDx) hcu
  have hcpL : (cp : ℝ) ≤ cp * Real.logb 2 (N + 2) := le_mul_of_one_le_right (Nat.cast_nonneg _) hL
  have hcfL : (cf : ℝ) ≤ cf * Real.logb 2 (N + 2) := le_mul_of_one_le_right (Nat.cast_nonneg _) hL
  change plainC V (canonicalFiniteSetCode D) ≤ setMutualInfo V A B + 2 * T + _ at h2
  push_cast
  linarith

end Kolmogorov.StrongMerging
