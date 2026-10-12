import KolmogorovMathlib.StrongMerging.Upper.CoreCaps
import KolmogorovMathlib.StrongMerging.Upper.Portfolio

/-!
# The extractability envelope (blueprint T06, `UpperExtractabilityEnvelope`)

`sublinear-merging.tex`, Theorem `thm:extractability-envelope` (tex ~635–657) and its proof
(tex ~834–978); blueprint section `bp-upper-portfolio` (tex ~4040–4058).

The selector is the exact partition filter (T05) of the universal portfolio (T04).  At a
qualifying instance the portfolio picks a trial `r*` of least observable cost, so
`T_{r*} ≤ T_r ≤ b_trial (H + r + √((H + r) max {0, I - 𝓔_p(r)}))` for every `r ≤ n` (T02), hence
`T_{r*} ≤ b_trial Φ` (`le_mul_extractabilityEnvelope`); the candidate has score and endpoint
costs at most `b_cand T_{r*}` (T03).  Filtering costs `O(e + 1)` in the endpoint costs
(`filter_endpoint_le`) and in the score (`filter_score_le`, with `C(q₀(x)) = O(n)` from the point
bound, `logb_setC_le_of_point`), and the mass loss is reproved after filtering by the mass
transfer U06 (`mass_le_of_point`).  As `H ≤ Φ` and `H ≥ 1`, all additive terms are `O(Φ)`.

* `exists_extractabilityEnvelope_selector_of_cores`: the frozen statement of T06, assuming the
  three minimum-core nodes M04, M07, M08 as the named hypotheses `CoverageStmt`,
  `InitialProfileCapStmt`, `AdjacentCapStmt` of `Upper.Trial` (cluster M_CORES,
  `Upper.CoreCaps`).

Constants are fixed in the order: the node constants (after `V`), then the trial step constant
`c_* = c_min^{T02} + c_min^{T03} + 1`, then the program constants of T04/T05, then `c, c_pt`.
The program `q` depends on `V` only through `c_*` and is chosen after `V`, before every instance
(auditor note K13).
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### Elementary steps -/

/-- **A bound by every term bounds by the envelope**: if `T ≤ b (H + r + √((H + r) Δ_r))` for
every `r ≤ n`, then `T ≤ b Φ` (the minimum is attained, `Finset.exists_mem_eq_inf'`). -/
theorem le_mul_extractabilityEnvelope {V : Map} {n e : ℕ} {A B : Finset BitString} {T bt : ℝ}
    (h : ∀ r ≤ n, T ≤ bt * (((baseBudget n e + r : ℕ) : ℝ) +
      Real.sqrt (((baseBudget n e + r : ℕ) : ℝ) *
        max 0 (setMutualInfo V A B - ordinaryCommonProfile V A B r)))) :
    T ≤ bt * extractabilityEnvelope V n e A B := by
  obtain ⟨r, hr, hreq⟩ := Finset.exists_mem_eq_inf' (Finset.nonempty_range_add_one (n := n))
    (fun r => ((baseBudget n e + r : ℕ) : ℝ) + Real.sqrt (((baseBudget n e + r : ℕ) : ℝ) *
      max 0 (setMutualInfo V A B - ordinaryCommonProfile V A B r)))
  unfold extractabilityEnvelope
  rw [hreq]
  exact h r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))

/-- **Endpoint costs after filtering** (tex ~956): `CT(Q z | A) ≤ 5 CT(Q₀ z | A) + |q₀| + c`, by
composing the endpoint description of `Q₀ z` with the set-level filter (`Lower.totalC_trans`,
`totalC_filterModel_le`) and `log₂ (t + 2) ≤ 2 t + 2`. -/
theorem filter_endpoint_le :
    ∃ c : ℕ, ∀ q0 : BitString, IsTotalProgram universalDecompressor q0 →
      ∀ (z : BitString) (A : Finset BitString),
        setTotalC (filterModel q0 z) A ≤ 5 * setTotalC (progModel q0 z) A + q0.length + c := by
  obtain ⟨ctr, htr⟩ := Lower.totalC_trans
  obtain ⟨cf, hcf⟩ := totalC_filterModel_le
  refine ⟨ctr + cf + 4, fun q0 hq0 z A => ?_⟩
  have h1 := htr (canonicalFiniteSetCode A) (canonicalFiniteSetCode (progModel q0 z))
    (canonicalFiniteSetCode (filterModel q0 z))
  have h2 := hcf q0 hq0 z
  have ht0 := totalC_nonneg (canonicalFiniteSetCode (progModel q0 z)) (canonicalFiniteSetCode A)
  have h3 := logb_add_two_le ht0
  unfold setTotalC
  push_cast
  linarith

/-- **Score after filtering** (tex ~956): for `x ∈ Q z`,
`Score(Q z, x) ≤ Score(Q₀ z, x) + c (|q₀| + 1) + c log₂ (C(Q₀ z) + 2)`, from
`setC_filterModel_le` and `|Q z| ≤ |Q₀ z|`. -/
theorem filter_score_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ q0 : BitString, IsTotalProgram universalDecompressor q0 →
      ∀ z x : BitString, x ∈ filterModel q0 z →
        modelScore V (filterModel q0 z) x ≤ modelScore V (progModel q0 z) x +
          c * ((q0.length : ℝ) + 1) + c * Real.logb 2 (setC V (progModel q0 z) + 2) := by
  obtain ⟨c, hc⟩ := setC_filterModel_le V hV
  refine ⟨c, fun q0 hq0 z x hx => ?_⟩
  have h1 := hc q0 hq0 z
  have hpos : (0 : ℝ) < (filterModel q0 z).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
  have hle : ((filterModel q0 z).card : ℝ) ≤ (progModel q0 z).card := by
    exact_mod_cast Finset.card_le_card (filterModel_subset q0 z)
  have h2 := Real.logb_le_logb_of_le one_lt_two hpos hle
  unfold modelScore
  linarith

/-- **A short point description bounds the model's complexity logarithmically**: for every
`a, b` there is `k` with `log₂ (C(D) + 2) ≤ k H` whenever `|x| = n` and
`CT(D | x) ≤ a (e + 1) + b`.

Proof sketch: `C(D) ≤ C(x) + C(D | x) + c log₂ (C(x) + C(D | x) + 2)`
(`upperComplexityChain_trans`, empty condition), `C(x) ≤ n + b_lit` (`plainC_le_length_add`),
`C(D | x) ≤ CT(D | x) + c'` (`condC_le_totalC_add`); with `log₂ (t + 2) ≤ 2 t + 2`
(`logb_add_two_le`) this gives `C(D) + 2 ≤ β (e + 2) (n + 2)` for a `β` depending on `a, b, V`.
Then `log₂ (β (e + 2) (n + 2)) = log₂ β + log₂ (e + 2) + log₂ (n + 2)`, with
`log₂ (n + 2) ≤ ⌈log₂ (n + 2)⌉` (`headerLog_eq_ceil_logb`), `log₂ (e + 2) ≤ 2 e + 2`
(`logb_add_two_le`) and `H ≥ 1`.  No relation between `e` and `n` is needed. -/
theorem logb_setC_le_of_point (V : Map) (hV : isOptimalConditional V) :
    ∀ a b : ℕ, ∃ k : ℕ, ∀ (n e : ℕ) (x : BitString) (D : Finset BitString), x.length = n →
      pointTotalC D x ≤ ((a * (e + 1) + b : ℕ) : ℝ) →
        Real.logb 2 (setC V D + 2) ≤ k * baseBudget n e := by
  intro a b
  obtain ⟨c₃, h₃⟩ := upperComplexityChain_trans V hV
  obtain ⟨ct, hct⟩ := condC_le_totalC_add V hV
  obtain ⟨blit, hblit⟩ := plainC_le_length_add V hV
  obtain ⟨β, hβ⟩ : ∃ β : ℕ, β = (1 + 2 * c₃) * (1 + blit + a + b + ct) + 2 * c₃ + 2 :=
    ⟨_, rfl⟩
  refine ⟨⌈Real.logb 2 β⌉₊ + 5, fun n e x D hx hpt => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hc₃ : (0 : ℝ) ≤ c₃ := Nat.cast_nonneg c₃
  have hct0 : (0 : ℝ) ≤ ct := Nat.cast_nonneg ct
  have hbl : (0 : ℝ) ≤ blit := Nat.cast_nonneg blit
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  -- the basic bounds `C(x) ≤ n + b_lit`, `C(D | x) ≤ a (e + 1) + b + c'`
  have hCx : plainC V x ≤ n + blit := by
    have := hblit x
    rw [hx] at this
    exact this
  have hCDx : condC V (canonicalFiniteSetCode D) x ≤ a * ((e : ℝ) + 1) + b + ct := by
    have h1 := hct (canonicalFiniteSetCode D) x
    have h2 : totalC (canonicalFiniteSetCode D) x ≤ ((a * (e + 1) + b : ℕ) : ℝ) := hpt
    push_cast at h2
    linarith
  have hx0 := plainC_nonneg V x
  have hdx0 := condC_nonneg V (canonicalFiniteSetCode D) x
  have hD : plainC V (canonicalFiniteSetCode D) ≤ plainC V x +
      condC V (canonicalFiniteSetCode D) x + c₃ * Real.logb 2
        (plainC V x + condC V (canonicalFiniteSetCode D) x + 2) :=
    h₃ (canonicalFiniteSetCode D) x []
  have hlg := logb_add_two_le (add_nonneg hx0 hdx0)
  have hlg' := mul_le_mul_of_nonneg_left hlg hc₃
  -- `C(D) + 2 ≤ β M` with `M = (e + 2) (n + 2)`
  have hM0 : (0 : ℝ) ≤ (e : ℝ) * n := mul_nonneg he0 hn0
  have hM1 : (1 : ℝ) ≤ ((e : ℝ) + 2) * ((n : ℝ) + 2) := by nlinarith
  have hMn : (n : ℝ) ≤ ((e : ℝ) + 2) * ((n : ℝ) + 2) := by nlinarith
  have hMe : (e : ℝ) + 1 ≤ ((e : ℝ) + 2) * ((n : ℝ) + 2) := by nlinarith
  generalize hM : ((e : ℝ) + 2) * ((n : ℝ) + 2) = M at hM1 hMn hMe
  have hs : plainC V x + condC V (canonicalFiniteSetCode D) x ≤
      (1 + (blit : ℝ) + a + b + ct) * M := by
    have h1 : (blit : ℝ) ≤ blit * M := le_mul_of_one_le_right hbl hM1
    have h2 : (a : ℝ) * ((e : ℝ) + 1) ≤ a * M := mul_le_mul_of_nonneg_left hMe ha0
    have h3 : (b : ℝ) ≤ b * M := le_mul_of_one_le_right hb0 hM1
    have h4 : (ct : ℝ) ≤ ct * M := le_mul_of_one_le_right hct0 hM1
    have h5 : (1 + (blit : ℝ) + a + b + ct) * M = M + blit * M + a * M + b * M + ct * M := by
      ring
    rw [h5]
    linarith
  have hs' := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 1 + 2 * c₃)
  have hc2M : 2 * (c₃ : ℝ) + 2 ≤ (2 * c₃ + 2) * M :=
    le_mul_of_one_le_right (by positivity) hM1
  have hβr : (β : ℝ) = (1 + 2 * (c₃ : ℝ)) * (1 + blit + a + b + ct) + 2 * c₃ + 2 := by
    rw [hβ]
    push_cast
    ring
  have hβM : setC V D + 2 ≤ (β : ℝ) * M := by
    have h1 : (β : ℝ) * M = (1 + 2 * (c₃ : ℝ)) * ((1 + (blit : ℝ) + a + b + ct) * M) +
        (2 * c₃ + 2) * M := by
      rw [hβr]
      ring
    rw [h1]
    change plainC V (canonicalFiniteSetCode D) + 2 ≤ _
    linarith
  -- `log₂ (β M) = log₂ β + log₂ (e + 2) + log₂ (n + 2)`
  have hβ2 : (2 : ℝ) ≤ β := by
    have : 2 ≤ β := by omega
    exact_mod_cast this
  have hlogM : Real.logb 2 (setC V D + 2) ≤
      Real.logb 2 β + (Real.logb 2 ((e : ℝ) + 2) + Real.logb 2 ((n : ℝ) + 2)) := by
    have hpos : (0 : ℝ) < setC V D + 2 := by
      have := plainC_nonneg V (canonicalFiniteSetCode D)
      change (0 : ℝ) < plainC V (canonicalFiniteSetCode D) + 2
      linarith
    have he2 : (e : ℝ) + 2 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
    have hβ0 : (β : ℝ) ≠ 0 := by
      intro h
      linarith
    rw [← Real.logb_mul he2 hn2, ← Real.logb_mul hβ0 (mul_ne_zero he2 hn2), hM]
    exact Real.logb_le_logb_of_le one_lt_two hpos hβM
  -- the three logarithms
  have hl1 : Real.logb 2 β ≤ ⌈Real.logb 2 β⌉₊ := Nat.le_ceil _
  have hl2 := logb_add_two_le he0
  have hl3 : Real.logb 2 ((n : ℝ) + 2) ≤ headerLog n := by
    have hh := headerLog_eq_ceil_logb n
    have h4 := Int.le_ceil (Real.logb 2 ((n : ℝ) + 2))
    rw [← hh] at h4
    exact_mod_cast h4
  have hL1 : (1 : ℝ) ≤ headerLog n := by exact_mod_cast one_le_headerLog n
  have hH : (baseBudget n e : ℝ) = e + headerLog n := Nat.cast_add e (headerLog n)
  have hH1 : (1 : ℝ) ≤ baseBudget n e := by
    rw [hH]
    linarith
  have hK0 : (⌈Real.logb 2 β⌉₊ : ℝ) ≤ ⌈Real.logb 2 β⌉₊ * (baseBudget n e : ℝ) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hH1
  have hK : ((⌈Real.logb 2 β⌉₊ + 5 : ℕ) : ℝ) * baseBudget n e =
      ⌈Real.logb 2 β⌉₊ * (baseBudget n e : ℝ) + 5 * baseBudget n e := by
    push_cast
    ring
  rw [hK]
  rw [hH] at hK0 ⊢
  linarith

/-- **Mass after any short-point model** (U06 with joint bounds): for every `a, b` there is `k`
such that for `e`-sufficient `A, B` of an `n`-bit `x`, `e ≤ n`, and every `D ∋ x` with
`CT(D | x) ≤ a (e + 1) + b` and `CT(D | A), CT(D | B) ≤ T`,
`t - log₂ |D| ≤ 2 T + k H`.

Proof sketch: `upperMassTransfer` with `N = (b_j + c_j) (1 + a + b) (n + 1)`: the joint
complexities of `((A, B), x)` and `(A, B)` by `upperJointBound`, those of `D` by
`jointBounds_of_point` with `T₀ = a (e + 1) + b ≤ (a + b) (n + 1)`; then `2 e ≤ 2 H` and
`log₂ (N + 2) ≤ k_l H` (`logb_le_baseBudget`).  As in `tradeoffBounds_of_raw`. -/
theorem mass_le_of_point (V : Map) (hV : isOptimalConditional V) :
    ∀ a b : ℕ, ∃ k : ℕ, ∀ (n e : ℕ) (x : BitString) (A B D : Finset BitString) (T : ℝ),
      x.length = n → e ≤ n → IsSufficientModel V x A e → IsSufficientModel V x B e → x ∈ D →
      pointTotalC D x ≤ ((a * (e + 1) + b : ℕ) : ℝ) → setTotalC D A ≤ T → setTotalC D B ≤ T →
        overlapMass A B - Real.logb 2 D.card ≤ 2 * T + k * baseBudget n e := by
  intro a b
  obtain ⟨cm, hcm⟩ := upperMassTransfer V hV
  obtain ⟨bj, hbj⟩ := upperJointBound V hV
  obtain ⟨cj, hcj⟩ := jointBounds_of_point V hV
  obtain ⟨kl, hkl⟩ := logb_le_baseBudget ((bj + cj) * (1 + a + b))
  refine ⟨2 + cm * kl, fun n e x A B D T hx he hA hB hxD hpt hTA hTB => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hcj0 : (0 : ℝ) ≤ cj := Nat.cast_nonneg cj
  have hbj0 : (0 : ℝ) ≤ bj := Nat.cast_nonneg bj
  have he' : (e : ℝ) ≤ n := by exact_mod_cast he
  have hT0 : (0 : ℝ) ≤ ((a * (e + 1) + b : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨j1, j2, j3, j4⟩ := hcj n e _ x A B D hx he hA hB hT0 hpt
  obtain ⟨-, b2, b3⟩ := hbj n e x A B hx he hA hB
  -- `T₀ = a (e + 1) + b ≤ (a + b) (n + 1)`
  have hT₀ : ((a * (e + 1) + b : ℕ) : ℝ) ≤ ((a : ℝ) + b) * (n + 1) := by
    have h1 : (a : ℝ) * ((e : ℝ) + 1) ≤ a * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) ha0
    have h2 : (b : ℝ) ≤ b * ((n : ℝ) + 1) := le_mul_of_one_le_right hb0 (by linarith)
    have h3 : ((a : ℝ) + b) * (n + 1) = a * ((n : ℝ) + 1) + b * ((n : ℝ) + 1) := by ring
    rw [h3]
    push_cast
    linarith
  -- the joint budget `N = ((b_j + c_j) (1 + a + b)) (n + 1)`
  have hP0 : (0 : ℝ) ≤ (1 + (a : ℝ) + b) * (n + 1) := by positivity
  have hP : (1 + (a : ℝ) + b) * (n + 1) = (n + 1) + ((a : ℝ) + b) * (n + 1) := by ring
  have hcast : (((bj + cj) * (1 + a + b) : ℕ) : ℝ) * (n + 1) =
      (bj : ℝ) * ((1 + (a : ℝ) + b) * (n + 1)) + cj * ((1 + (a : ℝ) + b) * (n + 1)) := by
    push_cast
    ring
  have hN1 : (cj : ℝ) * (n + 1 + ((a * (e + 1) + b : ℕ) : ℝ)) ≤
      (((bj + cj) * (1 + a + b) : ℕ) : ℝ) * (n + 1) := by
    rw [hcast]
    have h1 : (n : ℝ) + 1 + ((a * (e + 1) + b : ℕ) : ℝ) ≤ (1 + (a : ℝ) + b) * (n + 1) := by
      rw [hP]
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hcj0
    have h3 := mul_nonneg hbj0 hP0
    linarith
  have hN2 : (bj : ℝ) * (n + 1) ≤ (((bj + cj) * (1 + a + b) : ℕ) : ℝ) * (n + 1) := by
    rw [hcast]
    have h1 : (n : ℝ) + 1 ≤ (1 + (a : ℝ) + b) * (n + 1) := by
      rw [hP]
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hbj0
    have h3 := mul_nonneg hcj0 hP0
    linarith
  have hmass := hcm _ _ _ x A B D hA hB hxD (b3.trans hN2) (j2.trans hN1)
    (j1.trans hN1) (b2.trans hN2) (j3.trans hN1) (j4.trans hN1) hTA hTB
  have hlog := hkl n e
  have hcmlog := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) cm)
  have heH : (e : ℝ) ≤ baseBudget n e := by
    exact_mod_cast (show e ≤ baseBudget n e by unfold baseBudget; omega)
  have hK : ((2 + cm * kl : ℕ) : ℝ) * baseBudget n e =
      2 * (baseBudget n e : ℝ) + cm * (kl * baseBudget n e) := by
    push_cast
    ring
  rw [hK]
  linarith

/-! ### T06 from the minimum-core nodes -/

/-- **T06 from the minimum-core nodes.**  The frozen statement of
`exists_extractabilityEnvelope_selector` (`StatementsExtra`), assuming M04, M07 and M08 as the
named hypotheses `CoverageStmt V`, `InitialProfileCapStmt V`, `AdjacentCapStmt V`. -/
theorem exists_extractabilityEnvelope_selector_of_cores (V : Map) (hV : isOptimalConditional V)
    (hM04 : CoverageStmt V) (hM07 : InitialProfileCapStmt V) (hM08 : AdjacentCapStmt V) :
    ∃ c cpt : ℕ, ∀ (e : ℕ) (pA pB : BitString), IsBoundedTotalWitness e pA →
      IsBoundedTotalWitness e pB →
        ∃ (q : BitString) (Q : BitString → Finset BitString), IsExactPartitionSelector q Q ∧
          q.length ≤ cpt * (e + 1) ∧
          ∀ (n : ℕ) (x : BitString) (A B : Finset BitString),
            IsWitnessedInstance V n e pA pB x A B →
              modelScore V (Q x) x ≤ c * extractabilityEnvelope V n e A B ∧
              setTotalC (Q x) A ≤ c * extractabilityEnvelope V n e A B ∧
              setTotalC (Q x) B ≤ c * extractabilityEnvelope V n e A B ∧
              overlapMass A B - Real.logb 2 (Q x).card ≤
                c * extractabilityEnvelope V n e A B := by
  -- node constants (after `V`), then `c_*`, then program constants
  obtain ⟨cminQ, bq, hQ⟩ := upperTrialQuadratic V hV hM07
  obtain ⟨cminC, bcand, hC⟩ := upperCandidateBounds V hV hM04 hM08
  obtain ⟨cs, hcs⟩ : ∃ cs : ℕ, cs = cminQ + cminC + 1 := ⟨_, rfl⟩
  obtain ⟨c₀, hport⟩ := upperPortfolio cs
  obtain ⟨cf, hfilt⟩ := upperPartitionFilter
  obtain ⟨ce, hce⟩ := filter_endpoint_le
  obtain ⟨csc, hsc⟩ := filter_score_le V hV
  obtain ⟨kL, hkL⟩ := logb_setC_le_of_point V hV 7 c₀
  obtain ⟨km, hkm⟩ := mass_le_of_point V hV 7 (c₀ + cf)
  obtain ⟨bt, hbt⟩ : ∃ bt : ℕ, bt = (bq + 7) * cs := ⟨_, rfl⟩
  obtain ⟨S0, hS0⟩ : ∃ S0 : ℕ, S0 = bcand * bt := ⟨_, rfl⟩
  obtain ⟨cT, hcT⟩ : ∃ cT : ℕ, cT = 5 * S0 + 14 + c₀ + ce := ⟨_, rfl⟩
  obtain ⟨cS, hcS⟩ : ∃ cS : ℕ, cS = S0 + csc * (15 + c₀) + csc * kL := ⟨_, rfl⟩
  refine ⟨cS + 3 * cT + km, 7 + c₀ + cf, fun e pA pB hA hB => ?_⟩
  obtain ⟨q0, hq0tot, hq0len, hq0prod⟩ := hport e pA pB hA hB
  have hQ0 : ∀ z : BitString, progModel q0 z = portfolioModel cs e pA pB z :=
    progModel_eq_of_produces hq0prod
  have hcont : ∀ z : BitString, z ∈ progModel q0 z := fun z => by
    rw [hQ0]
    exact mem_portfolioModel_self cs e pA pB z
  obtain ⟨q, hqlen, hqsel⟩ := hfilt q0 hq0tot hcont
  refine ⟨q, filterModel q0, hqsel, ?_, ?_⟩
  · rw [hqlen]
    linarith [Nat.zero_le (c₀ * e), Nat.zero_le (cf * e)]
  intro n x A B hI
  obtain ⟨hn, hen, hx, hpa, hpb, hsA, hsB⟩ := hI
  have h : IsCoreInstance V n e pA pB x A B :=
    ⟨hA.1, hA.2, hB.1, hB.2, hen, hx, hpa, hpb, hsA, hsB⟩
  have hH1 : (1 : ℝ) ≤ baseBudget n e := by exact_mod_cast one_le_baseBudget n e
  have heH : (e : ℝ) ≤ baseBudget n e := by
    have : e ≤ baseBudget n e := Nat.le_add_right e (headerLog n)
    exact_mod_cast this
  -- the unfiltered selection: a trial of least observable cost
  obtain ⟨r₀, hr₀, hsel, hmin⟩ := portfolioModel_spec h hn cs
  obtain ⟨-, hs0, hA0, hB0⟩ := hC cs (by omega) n e r₀ pA pB x A B h hr₀
  have hT : ((((instTrial cs n e r₀ pA pB x A B).2 + 1) * trialStep cs n e r₀ : ℕ) : ℝ) ≤
      (bt : ℝ) * extractabilityEnvelope V n e A B := by
    apply le_mul_extractabilityEnvelope
    intro r hr
    have h1 := hQ cs (by omega) n e r pA pB x A B h hr
    rw [← hbt] at h1
    have h2 : ((((instTrial cs n e r₀ pA pB x A B).2 + 1) * trialStep cs n e r₀ : ℕ) : ℝ) ≤
        ((((instTrial cs n e r pA pB x A B).2 + 1) * trialStep cs n e r : ℕ) : ℝ) := by
      exact_mod_cast hmin r hr
    exact h2.trans h1
  have hHΦ : (baseBudget n e : ℝ) ≤ extractabilityEnvelope V n e A B :=
    baseBudget_le_extractabilityEnvelope V n e A B
  generalize extractabilityEnvelope V n e A B = Φ at hT hHΦ ⊢
  generalize ((((instTrial cs n e r₀ pA pB x A B).2 + 1) * trialStep cs n e r₀ : ℕ) : ℝ) = T₀
    at hT hs0 hA0 hB0
  have hΦ1 : (1 : ℝ) ≤ Φ := hH1.trans hHΦ
  have hΦ0 : (0 : ℝ) ≤ Φ := by linarith
  have hbc0 : (0 : ℝ) ≤ bcand := Nat.cast_nonneg _
  have hS0r : (S0 : ℝ) = (bcand : ℝ) * bt := by
    rw [hS0]
    push_cast
    ring
  have hbT := mul_le_mul_of_nonneg_left hT hbc0
  have hpm : progModel q0 x = (instTrial cs n e r₀ pA pB x A B).1 := by rw [hQ0, hsel]
  -- bounds on the unfiltered model `Q₀ x`
  have hs0' : modelScore V (progModel q0 x) x ≤ (S0 : ℝ) * Φ := by
    rw [hpm, hS0r]
    linarith
  have hA0' : setTotalC (progModel q0 x) A ≤ (S0 : ℝ) * Φ := by
    rw [hpm, hS0r]
    linarith
  have hB0' : setTotalC (progModel q0 x) B ≤ (S0 : ℝ) * Φ := by
    rw [hpm, hS0r]
    linarith
  -- lengths and point bounds of the two programs
  have hq0r : (q0.length : ℝ) ≤ 7 * ((e : ℝ) + 1) + c₀ := by exact_mod_cast hq0len
  have hpt0 : pointTotalC (progModel q0 x) x ≤ ((7 * (e + 1) + c₀ : ℕ) : ℝ) := by
    have hp := hq0prod x
    rw [← hQ0] at hp
    exact (Lower.totalC_le_length_of_totalProgram hq0tot hp).trans (by exact_mod_cast hq0len)
  have hxQ : x ∈ filterModel q0 x := mem_filterModel_self hcont x
  have hptQ : pointTotalC (filterModel q0 x) x ≤ ((7 * (e + 1) + (c₀ + cf) : ℕ) : ℝ) := by
    refine (Lower.totalC_le_length_of_totalProgram hqsel.1 (hqsel.2.1 x)).trans ?_
    rw [hqlen]
    exact_mod_cast (by omega : q0.length + cf ≤ 7 * (e + 1) + (c₀ + cf))
  -- the filtered model `Q x`
  have h7 : 7 * ((e : ℝ) + 1) ≤ 14 * Φ := by linarith
  have hc₀Φ : (c₀ : ℝ) ≤ c₀ * Φ := le_mul_of_one_le_right (Nat.cast_nonneg _) hΦ1
  have hceΦ : (ce : ℝ) ≤ ce * Φ := le_mul_of_one_le_right (Nat.cast_nonneg _) hΦ1
  have hcTr : (cT : ℝ) = 5 * (S0 : ℝ) + 14 + c₀ + ce := by
    rw [hcT]
    push_cast
    ring
  have hTA : setTotalC (filterModel q0 x) A ≤ (cT : ℝ) * Φ := by
    have h1 := hce q0 hq0tot x A
    rw [hcTr]
    linarith
  have hTB : setTotalC (filterModel q0 x) B ≤ (cT : ℝ) * Φ := by
    have h1 := hce q0 hq0tot x B
    rw [hcTr]
    linarith
  have hscore : modelScore V (filterModel q0 x) x ≤ (cS : ℝ) * Φ := by
    have h1 := hsc q0 hq0tot x x hxQ
    have h2 := hkL n e x (progModel q0 x) hx hpt0
    have hcsc : (0 : ℝ) ≤ csc := Nat.cast_nonneg _
    have h3 : (q0.length : ℝ) + 1 ≤ (15 + (c₀ : ℝ)) * Φ := by
      have : (c₀ : ℝ) + 1 ≤ ((c₀ : ℝ) + 1) * Φ := le_mul_of_one_le_right (by positivity) hΦ1
      linarith
    have h3' := mul_le_mul_of_nonneg_left h3 hcsc
    have h4 : (kL : ℝ) * baseBudget n e ≤ kL * Φ :=
      mul_le_mul_of_nonneg_left hHΦ (Nat.cast_nonneg _)
    have h4' := mul_le_mul_of_nonneg_left (h2.trans h4) hcsc
    have hcSr : (cS : ℝ) = (S0 : ℝ) + csc * (15 + (c₀ : ℝ)) + csc * kL := by
      rw [hcS]
      push_cast
      ring
    rw [hcSr]
    linarith
  have hmass : overlapMass A B - Real.logb 2 (filterModel q0 x).card ≤
      2 * ((cT : ℝ) * Φ) + km * Φ := by
    have h1 := hkm n e x A B (filterModel q0 x) ((cT : ℝ) * Φ) hx hen hsA hsB hxQ hptQ hTA hTB
    have h2 : (km : ℝ) * baseBudget n e ≤ km * Φ :=
      mul_le_mul_of_nonneg_left hHΦ (Nat.cast_nonneg _)
    linarith
  have hp1 : 0 ≤ (cT : ℝ) * Φ := mul_nonneg (Nat.cast_nonneg _) hΦ0
  have hp2 : 0 ≤ (cS : ℝ) * Φ := mul_nonneg (Nat.cast_nonneg _) hΦ0
  have hp3 : 0 ≤ (km : ℝ) * Φ := mul_nonneg (Nat.cast_nonneg _) hΦ0
  have hfin : ((cS + 3 * cT + km : ℕ) : ℝ) * Φ =
      (cS : ℝ) * Φ + 3 * ((cT : ℝ) * Φ) + (km : ℝ) * Φ := by
    push_cast
    ring
  rw [hfin]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### T06: the extractability envelope -/

/-- **T06: an envelope over ordinary common factors (blueprint `UpperExtractabilityEnvelope`).**
For an optimal plain machine `V` there are constants `c, c_pt` such that for every integer
`e ≥ 0` and all total witnesses `p_A, p_B` of length at most `e` there is one total program `q`,
depending only on the witnesses and `e`, of length at most `c_pt (e + 1)`, which is an exact
partition selector, such that at every qualifying instance the model `D = q(x)` satisfies
`C(D) + log₂ |D| - k ≤ c Φ`, `CT(D | A), CT(D | B) ≤ c Φ` and `t - log₂ |D| ≤ c Φ`, where
`Φ = extractabilityEnvelope n e A B`.  The statement is verbatim that of
`exists_extractabilityEnvelope_selector` in `StatementsExtra`; the minimum-core nodes are
`upperMinCoreCoverage`, `upperInitialProfileCap` and `upperAdjacentCap` (`Upper.CoreCaps`).

`sublinear-merging.tex`, Theorem `thm:extractability-envelope`. -/
theorem exists_extractabilityEnvelope_selector' (V : Map) (hV : isOptimalConditional V) :
    ∃ c cpt : ℕ, ∀ (e : ℕ) (pA pB : BitString), IsBoundedTotalWitness e pA →
      IsBoundedTotalWitness e pB →
        ∃ (q : BitString) (Q : BitString → Finset BitString), IsExactPartitionSelector q Q ∧
          q.length ≤ cpt * (e + 1) ∧
          ∀ (n : ℕ) (x : BitString) (A B : Finset BitString),
            IsWitnessedInstance V n e pA pB x A B →
              modelScore V (Q x) x ≤ c * extractabilityEnvelope V n e A B ∧
              setTotalC (Q x) A ≤ c * extractabilityEnvelope V n e A B ∧
              setTotalC (Q x) B ≤ c * extractabilityEnvelope V n e A B ∧
              overlapMass A B - Real.logb 2 (Q x).card ≤
                c * extractabilityEnvelope V n e A B :=
  exists_extractabilityEnvelope_selector_of_cores V hV (upperMinCoreCoverage V hV)
    (upperInitialProfileCap V hV) (upperAdjacentCap V hV)

end Kolmogorov.StrongMerging.Upper
