import KolmogorovMathlib.StrongMerging.Lower.Projection
import KolmogorovMathlib.StrongMerging.Lower.GenericEdge

/-!
# The sharp lower bound: no common model at the budget, assembly, full tolerance range

Blueprint nodes L36 (`noCommonModelAtBudget`), L37 (`sharpLowerBound`, the target L00) and L38
(`sharpLowerRealTolerance`) of the formalization of `sublinear-merging.tex` (main text: Theorem
`thm:hamming-obstruction`, Corollary `cor:ham-sharp-range` and their proofs, tex lines 1209-1275
and 1759-1820; appendix paragraphs "L35--L36" and "L37--L38", lines 5013-5050).

* **L36.**  Given the sharp generic edge and its calibration (cluster F: `SharpEdge`,
  `EdgeCalibration`), a peeling exponent `q = d - 2T - C₁ m` with `C₁ > c_p + j₀`, the distance
  gap of L33 and the explicit premises `c_t m ≤ T` (admission of the partition program to the
  game budget `S = 3T`) and `(c + C₁ + c_q) m ≤ T` (absorption of the score slack), no finite
  `D ∋ x` has score and both total reduction costs at most `T`.  No strength or mass condition on
  `D` is used.
* **L37.**  `exists_strong_pair_without_common_model'`, verbatim the frozen statement
  `exists_strong_pair_without_common_model`: the constants are chosen in the ledger order
  (L43): machines, then the coding constants `c_p, c_t, c_q` (L31, L34, L35), `c_pt, c_s` (L28)
  and `c` (L27), then `j₀ = 5` and `C₁ = c_p + j₀ + 1`, then `λ = 2c + c_s + 8`, then one cutoff
  `M₀` from the uniform growth of `T / m` (`sharp_growth`).
* **L38.**  `exists_strong_pair_without_common_model_real'`, verbatim the frozen real-tolerance
  corollary, with `E = min ⌊ε/32⌋ ⌊M/2¹⁰⁰⌋` chosen in the proof (no real oracle in any game).
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### Arithmetic leaves -/

/-- **Thin projections lose `q` bits of log-cardinality**: if `2^q |Q| ≤ |D|` and `Q` is
nonempty then `log₂ |Q| + q ≤ log₂ |D|`.

Proof sketch: cast to reals, take `Real.logb 2` of both sides (`Real.logb_le_logb_of_le`, both
sides positive), and expand `logb 2 (2^q |Q|) = q + logb 2 |Q|` (`Real.logb_mul`,
`Real.logb_pow`, `Real.logb_self_eq_one`).
Reference: tex 1806-1812 (first line of the score chain). -/
theorem logb_card_add_le {Q D : Finset BitString} {q : ℕ} (hQ : 0 < Q.card)
    (h : 2 ^ q * Q.card ≤ D.card) : Real.logb 2 Q.card + q ≤ Real.logb 2 D.card := by
  have hQ' : (0 : ℝ) < Q.card := by exact_mod_cast hQ
  have h' : (2 : ℝ) ^ q * Q.card ≤ D.card := by exact_mod_cast h
  have hpos : (0 : ℝ) < 2 ^ q * Q.card := by positivity
  have hlog := Real.logb_le_logb_of_le one_lt_two hpos h'
  rw [Real.logb_mul (by positivity) hQ'.ne', Real.logb_pow,
    Real.logb_self_eq_one one_lt_two] at hlog
  linarith

/-- **The header bounds the logarithm**: `log₂ (M + 1) ≤ ⌈log₂ (M + 2)⌉ = headerLog M`.

Proof sketch: `Real.logb_le_logb_of_le` gives `log₂ (M + 1) ≤ log₂ (M + 2)`, and
`log₂ (M + 2) ≤ Nat.clog 2 (M + 2)` since `M + 2 ≤ 2 ^ clog` (`Nat.le_pow_clog`,
`Real.logb_le_iff_le_rpow`).
Reference: tex 1730-1736 (`log(M+1) ≤ m`). -/
theorem logb_succ_le_headerLog (M : ℕ) : Real.logb 2 ((M : ℝ) + 1) ≤ headerLog M := by
  have h1 : Real.logb 2 ((M : ℝ) + 1) ≤ Real.logb 2 ((M : ℝ) + 2) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  have h2 : ((M + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (headerLog M : ℕ) := by
    have := Nat.le_pow_clog one_lt_two (M + 2)
    unfold headerLog
    exact_mod_cast this
  have h3 : Real.logb 2 ((M : ℝ) + 2) ≤ headerLog M := by
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity), Real.rpow_natCast]
    push_cast at h2
    exact h2
  linarith

/-- **The peeling threshold beats the distance count** (`eq:ham-threshold-gap`, SSE form).  With
`a = log₂ (M choose 2r)`, `a - d < 20E + 2m + 1` (L24), `2⁵⁰ E ≤ r`, `10⁶ T ≤ r`,
`log₂ (M + 1) ≤ m`, `1 ≤ m`, `q + 2T + C₁ m = d` and `(C₁ + 5) m ≤ T`:
`2 (M + 1) (M choose 2r) 2^(-3r/2) < 2^q`.

Proof sketch: take `log₂`; the left side is `1 + log₂ (M + 1) + a - 3r/2 < d + 20E + 3m + 2 -
3r/2` and the right side is `q = d - 2T - C₁ m`; it remains `20E + 2T + (C₁ + 3) m + 2 ≤ 3r/2`,
which follows from `(C₁ + 3) m + 2 ≤ (C₁ + 5) m ≤ T`, `20E ≤ 20 r / 2⁵⁰` and `3T ≤ 3r / 10⁶`
(`Real.rpow_natCast`, `Real.rpow_add`, `Real.logb_lt_iff_lt_rpow`).
Reference: tex 1730-1757 (`log θ - F ≥ r`), blueprint L33 (lines 4955-4964). -/
theorem peel_gap_of_bounds {M r T m d q C₁ E : ℕ} (hDa : 0 < M.choose (2 * r))
    (hgap : Real.logb 2 (M.choose (2 * r)) - d < 20 * E + 2 * m + 1) (hE : 2 ^ 50 * E ≤ r)
    (hT : 10 ^ 6 * T ≤ r) (hm : Real.logb 2 ((M : ℝ) + 1) ≤ m) (hm1 : 1 ≤ m)
    (hq : q + 2 * T + C₁ * m = d) (hgrow : (C₁ + 5) * m ≤ T) :
    2 * ((M : ℝ) + 1) * M.choose (2 * r) * (2 : ℝ) ^ (-(3 * (r : ℝ) / 2)) < 2 ^ q := by
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hDa' : (0 : ℝ) < (M.choose (2 * r) : ℝ) := by exact_mod_cast hDa
  have hlhs : (2 : ℝ) ^ (1 + Real.logb 2 ((M : ℝ) + 1) + Real.logb 2 (M.choose (2 * r)) -
      3 * (r : ℝ) / 2) =
      2 * ((M : ℝ) + 1) * M.choose (2 * r) * (2 : ℝ) ^ (-(3 * (r : ℝ) / 2)) := by
    rw [sub_eq_add_neg, Real.rpow_add two_pos, Real.rpow_add two_pos, Real.rpow_add two_pos,
      Real.rpow_one, Real.rpow_logb two_pos (by norm_num) hM1,
      Real.rpow_logb two_pos (by norm_num) hDa']
  rw [← hlhs, ← Real.rpow_natCast]
  apply Real.rpow_lt_rpow_of_exponent_lt one_lt_two
  have hq' : (q : ℝ) + 2 * T + C₁ * m = d := by exact_mod_cast hq
  have hg' : ((C₁ : ℝ) + 5) * m ≤ T := by exact_mod_cast hgrow
  have hg'' : (C₁ : ℝ) * m + 5 * m ≤ T := by
    linarith [hg', show ((C₁ : ℝ) + 5) * m = C₁ * m + 5 * m by ring]
  have hE' : (2 : ℝ) ^ 50 * E ≤ r := by exact_mod_cast hE
  have hT' : (10 : ℝ) ^ 6 * T ≤ r := by exact_mod_cast hT
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg E
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  norm_num at hE' hT'
  linarith

/-! ### L36: no common model at the budget -/

/-- **Node L36, `noCommonModelAtBudget`.**  For an optimal plain machine `V` there are coding
constants `c_p` (L31/L32), `c_t` (L34) and `c_q` (L35) such that the following holds.  Let
`M, E` be valid, let `z, u, v, W` be a sharp generic edge with calibration (cluster F,
`SharpEdge` and `EdgeCalibration` with constant `c` and gap `j₀`), and let `q` satisfy
`q + 2T + C₁ m = d` for some `C₁ > c_p + j₀`.  Assume the distance gap of L33 at threshold `2^q`
and the premises `c_t m ≤ T`, `(c + C₁ + c_q) m ≤ T`.  Then no finite `D ∋ u v` satisfies all
three of `C(D) + log₂ |D| ≤ C(u v) + T`, `CT(D | A_u) ≤ T`, `CT(D | B_v) ≤ T`. -/
theorem noCommonModelAtBudget (V : Map) (hV : isOptimalConditional V) :
    ∃ cp ct cq : ℕ, ∀ (M E j₀ c C₁ q : ℕ) (z u v : BitString) (W : Finset BitString),
      SharpValid M E → SharpEdge V M E j₀ c z u v W → EdgeCalibration V M E j₀ c u v →
      q + 2 * mergerBudget M E + C₁ * headerLog M = sharpLogInternalDegree M E →
      cp + j₀ < C₁ →
      2 * ((M : ℝ) + 1) * M.choose (2 * sharpRootRadius M E) *
        (2 : ℝ) ^ (-(3 * (sharpRootRadius M E : ℝ) / 2)) < 2 ^ q →
      ct * headerLog M ≤ mergerBudget M E →
      (c + C₁ + cq) * headerLog M ≤ mergerBudget M E →
      ∀ D : Finset BitString, u ++ v ∈ D →
        ¬ (setC V D + Real.logb 2 D.card ≤ plainC V (u ++ v) + mergerBudget M E ∧
          setTotalC D (rowStar (2 * sharpRootRadius M E) u) ≤ mergerBudget M E ∧
          setTotalC D (colStar (2 * sharpRootRadius M E) v) ≤ mergerBudget M E) := by
  obtain ⟨cp, hcp⟩ := actualEdgeSurvives V hV
  obtain ⟨ct, hct⟩ := labelProjectionPartition
  obtain ⟨cq, hcq⟩ := projectionScoreCode V hV
  refine ⟨cp, ct, cq, fun M E j₀ c C₁ q z u v W hv hedge hcal hq hC₁ hgap hctT hscT D hxD
    hbud => ?_⟩
  obtain ⟨hscore, hTA, hTB⟩ := hbud
  obtain ⟨hr0, hr50, -, -, -, -, -, -, -, -, -, -, -, h8, -, -⟩ := sharpParameters_valid hv
  set r := sharpRootRadius M E with hr
  set T := mergerBudget M E with hT
  set m := headerLog M with hm
  set d := sharpLogInternalDegree M E with hd
  have hm1 : 1 ≤ m := one_le_headerLog M
  have hlen : ∀ y ∈ W, y.length = M := fun y hy =>
    (mem_stringsOfLength M y).1 (mem_filter.1 (hedge.reservoir.subset_sphere hy)).1
  have hu : u.length = M := hlen u hedge.left_mem
  have hv' : v.length = M := hlen v hedge.right_mem
  have hTr : T ≤ r := Nat.div_le_self _ _
  have hdM : d ≤ M := sharp_logDegree_le_M hv
  have hqM : q ≤ M := by omega
  have hjM : 2 * r ≤ M := by omega
  have hTM : T ≤ M := by omega
  -- the total witnesses of the two reductions
  obtain ⟨pA, hpA, hpAlen, hpAprod⟩ := exists_totalProgram_of_totalC_le (t := T) hTA
  obtain ⟨pB, hpB, hpBlen, hpBprod⟩ := exists_totalProgram_of_totalC_le (t := T) hTB
  have hpAM : pA.length ≤ M := hpAlen.trans hTM
  have hpBM : pB.length ≤ M := hpBlen.trans hTM
  have hzA := progOut_eq_of_produces hpA hpAprod
  have hzB := progOut_eq_of_produces hpB hpBprod
  set G := labelGraph (progOut pA) (progOut pB) M (2 * r) (canonicalFiniteSetCode D) with hG
  have hedge' : (u, v) ∈ G := mem_labelGraph_actual hu hv' hxD hedge.dist_eq hzA hzB
  -- L32: the actual edge survives
  have hbudget : (pA.length + pB.length + q + cp * m : ℝ) < (d : ℝ) - j₀ := by
    have h1 : (pA.length : ℝ) ≤ T := by exact_mod_cast hpAlen
    have h2 : (pB.length : ℝ) ≤ T := by exact_mod_cast hpBlen
    have h3 : ((q + 2 * T + C₁ * m : ℕ) : ℝ) = d := by exact_mod_cast hq
    have h4 : ((cp + j₀ + 1 : ℕ) : ℝ) ≤ C₁ := by exact_mod_cast hC₁
    have h5 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    push_cast at h3 h4
    have k1 : ((cp : ℝ) + j₀ + 1) * m ≤ C₁ * m := mul_le_mul_of_nonneg_right h4 (by positivity)
    have k2 : (j₀ : ℝ) ≤ j₀ * m := by nlinarith [(Nat.cast_nonneg j₀ : (0 : ℝ) ≤ j₀)]
    have k3 : ((cp : ℝ) + j₀ + 1) * m = cp * m + j₀ * m + m := by ring
    linarith
  have hsurv := hcp M (2 * r) q pA pB u v D ((d : ℝ) - j₀) hpA hpB hpAM hpBM hjM hqM hzA hzB
    hedge' hedge.cond_right hedge.cond_left hbudget
  -- L33: a large projection
  have hE : ∀ e ∈ G, e.1.length = M ∧ e.2.length = M ∧ hammingDist e.1 e.2 = 2 * r :=
    fun e he => by
      obtain ⟨h1, h2, -, h4, -, -⟩ := mem_labelGraph.1 he
      exact ⟨h1, h2, h4⟩
  have hgap' : 2 * ((M : ℝ) + 1) * M.choose (2 * r) * (2 : ℝ) ^ (-(3 * (r : ℝ) / 2)) <
      ((2 ^ q : ℕ) : ℝ) := by
    push_cast
    exact hgap
  have hlarge := coreHasLargeProjection hE hr0 (by omega) h8 (by omega) ⟨_, hsurv⟩ hgap'
  -- the score of a projection of the core, common to both sides
  have hscoreQ : ∀ (side : Bool) (Q : Finset BitString),
      Q = coreProj (progOut pA) (progOut pB) M (2 * r) (2 ^ q) side (canonicalFiniteSetCode D) →
      0 < Q.card → setC V Q + Real.logb 2 Q.card ≤ (sharpThreshold M E : ℝ) + (6 * T : ℕ) := by
    intro side Q hQdef hQ
    subst hQdef
    obtain ⟨hQcard, hQC⟩ := hcq M (2 * r) q side pA pB D hpA hpB hpAM hpBM hjM hqM
    have hlog := logb_card_add_le hQ hQcard
    have h1 : (pA.length : ℝ) ≤ T := by exact_mod_cast hpAlen
    have h2 : (pB.length : ℝ) ≤ T := by exact_mod_cast hpBlen
    have h3 : ((q + 2 * T + C₁ * m : ℕ) : ℝ) = d := by exact_mod_cast hq
    have h4 : (((c + C₁ + cq) * m : ℕ) : ℝ) ≤ T := by exact_mod_cast hscT
    have h5 := hcal.pair_upper
    push_cast at h3 h4 ⊢
    have k1 : ((c : ℝ) + C₁ + cq) * m = c * m + C₁ * m + cq * m := by ring
    linarith
  rcases hlarge with hL | hR
  · -- the left projection is large; it is the cell of `u`
    set Q := coreProj (progOut pA) (progOut pB) M (2 * r) (2 ^ q) false
      (canonicalFiniteSetCode D) with hQ
    have hQimg : (peelCore (2 ^ q) G).image Prod.fst = Q := by
      simp only [hQ, coreProj, Bool.false_eq_true, ↓reduceIte, hG]
    have huQ : u ∈ Q := hQimg ▸ mem_image.2 ⟨(u, v), hsurv, rfl⟩
    have hlab : sideLabel (progOut pA) (progOut pB) (2 * r) false u =
        canonicalFiniteSetCode D := by
      simp only [sideLabel, Bool.false_eq_true, ↓reduceIte, hzA]
    have hcell : projCell (progOut pA) (progOut pB) M (2 * r) (2 ^ q) false u = Q := by
      rw [projCell, hlab, ite_eq_left (show u.length = M ∧ u ∈ Q from ⟨hu, huQ⟩)]
    obtain ⟨p, hplen, -, hpart, hpprod⟩ := hct M (2 * r) q false pA pB hpA hpB hpAM hpBM hjM hqM
    have hplen' : p.length ≤ pA.length + pB.length + ct * m := hplen
    have hpS : p.length ≤ 3 * T := by omega
    have hprodu := hpprod u
    rw [hcell] at hprodu
    exact hedge.reservoir.avoid p hpS hpart u hedge.left_mem Q hprodu (hQimg ▸ hL)
      (by have := hscoreQ false Q hQ (card_pos.2 ⟨u, huQ⟩); push_cast at this ⊢; linarith)
  · -- the right projection is large; it is the cell of `v`
    set Q := coreProj (progOut pA) (progOut pB) M (2 * r) (2 ^ q) true
      (canonicalFiniteSetCode D) with hQ
    have hQimg : (peelCore (2 ^ q) G).image Prod.snd = Q := by
      simp only [hQ, coreProj, ↓reduceIte, hG]
    have hvQ : v ∈ Q := hQimg ▸ mem_image.2 ⟨(u, v), hsurv, rfl⟩
    have hlab : sideLabel (progOut pA) (progOut pB) (2 * r) true v =
        canonicalFiniteSetCode D := by
      simp only [sideLabel, ↓reduceIte, hzB]
    have hcell : projCell (progOut pA) (progOut pB) M (2 * r) (2 ^ q) true v = Q := by
      rw [projCell, hlab, ite_eq_left (show v.length = M ∧ v ∈ Q from ⟨hv', hvQ⟩)]
    obtain ⟨p, hplen, -, hpart, hpprod⟩ := hct M (2 * r) q true pA pB hpA hpB hpAM hpBM hjM hqM
    have hplen' : p.length ≤ pA.length + pB.length + ct * m := hplen
    have hpS : p.length ≤ 3 * T := by omega
    have hprodv := hpprod v
    rw [hcell] at hprodv
    exact hedge.reservoir.avoid p hpS hpart v hedge.right_mem Q hprodv (hQimg ▸ hR)
      (by have := hscoreQ true Q hQ (card_pos.2 ⟨v, hvQ⟩); push_cast at this ⊢; linarith)

/-! ### L37: the sharp lower bound (target L00) -/

/-- **Node L37, `sharpLowerBound`** (target L00): verbatim the frozen statement
`exists_strong_pair_without_common_model` of `StrongMerging.Statements`. -/
theorem exists_strong_pair_without_common_model' (V : Map) (hV : isOptimalConditional V) :
    ∃ lam cpt M₀ : ℕ, 1 ≤ lam ∧
      ∀ M : ℕ, M₀ ≤ M → 2048 ∣ M → ∀ E : ℕ, lam * headerLog M ≤ E → 2 ^ 100 * E ≤ M →
        ∃ (x : BitString) (A B : Finset BitString), x.length = 2 * M ∧
          pointTotalC A x ≤ cpt ∧ pointTotalC B x ≤ cpt ∧
          IsSufficientModel V x A (32 * E) ∧ IsSufficientModel V x B (32 * E) ∧ A ∩ B = {x} ∧
          ∀ D : Finset BitString, x ∈ D →
            ¬ (setC V D + Real.logb 2 D.card ≤ plainC V x + mergerBudget M E ∧
              setTotalC D A ≤ mergerBudget M E ∧ setTotalC D B ≤ mergerBudget M E) := by
  obtain ⟨cp, ct, cq, hL36⟩ := noCommonModelAtBudget V hV
  obtain ⟨cpt, cs, hstar⟩ := ambientStarModels V hV
  obtain ⟨c, MF, hF⟩ := internalEdgeComplexity V hV
  obtain ⟨M1, hM1⟩ := sharp_growth ct
  obtain ⟨M2, hM2⟩ := sharp_growth (c + (cp + 5 + 1) + cq)
  obtain ⟨M3, hM3⟩ := sharp_growth (cp + 5 + 1 + 5)
  refine ⟨2 * c + cs + 8, cpt, max MF (max M1 (max M2 M3)), by omega,
    fun M hM hdiv E hlam hE100 => ?_⟩
  have hMF : MF ≤ M := le_of_max_le_left hM
  have hM1' : M1 ≤ M := le_trans (le_max_left _ _) (le_of_max_le_right hM)
  have hM2' : M2 ≤ M :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_max_le_right hM)
  have hM3' : M3 ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_max_le_right hM)
  set m := headerLog M with hm
  have hm1 : 1 ≤ m := one_le_headerLog M
  have hE1 : 1 ≤ E := by
    have := Nat.mul_le_mul (show 1 ≤ 2 * c + cs + 8 by omega) hm1
    omega
  have hv : SharpValid M E := ⟨hdiv, hE1, hE100⟩
  obtain ⟨z, u, v, W, hedge, hcal⟩ := hF M hMF E hv 5 le_rfl
  obtain ⟨hr0, hr50, -, -, -, -, -, -, -, -, hDa, -, -, h8, -, -⟩ := sharpParameters_valid hv
  set r := sharpRootRadius M E with hr
  set T := mergerBudget M E with hT
  set d := sharpLogInternalDegree M E with hd
  have hlen : ∀ y ∈ W, y.length = M := fun y hy =>
    (mem_stringsOfLength M y).1 (mem_filter.1 (hedge.reservoir.subset_sphere hy)).1
  have hu : u.length = M := hlen u hedge.left_mem
  have hv' : v.length = M := hlen v hedge.right_mem
  have hTct : ct * m ≤ T := hM1 M hM1' E hE1
  have hTsc : (c + (cp + 5 + 1) + cq) * m ≤ T := hM2 M hM2' E hE1
  have hTgr : (cp + 5 + 1 + 5) * m ≤ T := hM3 M hM3' E hE1
  have hTr : 10 ^ 6 * T ≤ r := by
    rw [hT, mergerBudget_eq_sharpRootRadius_div]
    exact Nat.mul_div_le _ _
  have hd97 : 97 * r ≤ d := sharp_logDegree_lower hv
  have hmono : (cp + 5 + 1) * m ≤ (cp + 5 + 1 + 5) * m := Nat.mul_le_mul_right _ (by omega)
  have hq : (d - 2 * T - (cp + 5 + 1) * m) + 2 * T + (cp + 5 + 1) * m = d := by omega
  have hgap := peel_gap_of_bounds (M := M) (r := r) (E := E) hDa (sharp_gap_lt hv)
    (sharp_tolerance_le hv) hTr (logb_succ_le_headerLog M) hm1 hq hTgr
  obtain ⟨hxA, hxB, hinter, hcardA, hcardB, hptA, hptB, hsA, hsB⟩ :=
    hstar M (2 * r) u v hu hv' hedge.dist_eq
  -- the input sufficiency of the stars
  have hgapE := sharp_gap_lt hv
  have hlamE : (((2 * c + cs + 8) * m : ℕ) : ℝ) ≤ E := by exact_mod_cast hlam
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hsuff : ∀ (A : Finset BitString) (y : BitString), u ++ v ∈ A →
      A.card = M.choose (2 * r) → setC V A ≤ plainC V y + cs * m →
      plainC V y ≤ sharpThreshold M E + c * m → IsSufficientModel V (u ++ v) A (32 * E) := by
    intro A y hxA hcard hsA hy
    refine ⟨hxA, ?_⟩
    have hlog : Real.logb 2 A.card = sharpLogAmbient M E := by
      rw [hcard]
      rfl
    have hpl := hcal.pair_lower
    rw [hlog]
    push_cast at hlamE hpl ⊢
    have k1 : (2 * (c : ℝ) + cs + 8) * m = 2 * (c * m) + cs * m + 8 * m := by ring
    have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg E
    linarith
  refine ⟨u ++ v, rowStar (2 * r) u, colStar (2 * r) v, length_append_of_length hu hv', hptA,
    hptB, hsuff _ u hxA hcardA hsA hcal.left_upper, hsuff _ v hxB hcardB hsB hcal.right_upper,
    hinter, fun D hD => ?_⟩
  exact hL36 M E 5 c (cp + 5 + 1) (d - 2 * T - (cp + 5 + 1) * m) z u v W hv hedge hcal hq
    (by omega) hgap hTct hTsc D hD

/-! ### L38: the full tolerance range -/

/-- `2¹⁰⁰ k² + 1 ≤ 2^(k-1)` for `k ≥ 200`. -/
theorem two_pow_pred_ge_sq (k : ℕ) (hk : 200 ≤ k) : 2 ^ 100 * k ^ 2 + 1 ≤ 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : 2 ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
      ring
    rw [h1]
    have hk2 : 2 * k + 1 ≤ k ^ 2 := by nlinarith
    nlinarith

/-- **Eventual size of the header** (used by L38 and L42): for fixed `λ, c_pt`, eventually
`λ m ≤ m²`, `2¹⁰⁰ m² ≤ M` and `c_pt ≤ 32 m²`, with `m = ⌈log₂ (M + 2)⌉`; the cutoff is
`2^(λ + c_pt + 200)`, beyond which `m ≥ λ + c_pt + 200` and `2^(m-1) < M + 2`. -/
theorem headerLog_eventually (lam cpt : ℕ) :
    ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M → lam * headerLog M ≤ headerLog M ^ 2 ∧
      2 ^ 100 * headerLog M ^ 2 ≤ M ∧ cpt ≤ 32 * headerLog M ^ 2 := by
  refine ⟨2 ^ (lam + cpt + 200), fun M hM => ?_⟩
  have hA : lam + cpt + 200 ≤ headerLog M := by
    have h1 : Nat.clog 2 (2 ^ (lam + cpt + 200)) ≤ Nat.clog 2 (M + 2) :=
      Nat.clog_mono_right 2 (by omega)
    rw [Nat.clog_pow 2 _ one_lt_two] at h1
    exact h1
  have hpred : 2 ^ (headerLog M - 1) < M + 2 := by
    have := Nat.pow_pred_clog_lt_self one_lt_two (show 1 < M + 2 by omega)
    exact this
  have hkey := two_pow_pred_ge_sq (headerLog M) (by omega)
  refine ⟨?_, by omega, ?_⟩
  · rw [sq]
    exact Nat.mul_le_mul_right _ (by omega)
  · have : headerLog M ≤ headerLog M ^ 2 := by
      rw [sq]
      exact Nat.le_mul_self _
    omega

/-- **Admissibility of the rounded tolerance** (L38).  For fixed `λ ≥ 1` and `c_pt` there is a
cutoff `M₁` such that for `M ≥ M₁` with `2048 ∣ M` and every real `ε` with
`(64 λ + 64 + c_pt) log₂ (2M + 2) ≤ ε ≤ 2M`, the integer `E = min ⌊ε/32⌋ ⌊M/2¹⁰⁰⌋` satisfies
`λ m ≤ E`, `2¹⁰⁰ E ≤ M`, `32 E ≤ ε`, `c_pt ≤ ε` and `64 ≤ ε`.

Proof sketch: `m = ⌈log₂ (M + 2)⌉ ≤ log₂ (2M + 2) + 1` (`clog_le_logb_add_one`) and
`log₂ (2M + 2) ≥ 1`, so `ε ≥ 64 λ m + 64 - 64 λ ≥ 32 λ m + 32` gives `⌊ε/32⌋ ≥ λ m`
(`Nat.le_floor`); `⌊M/2¹⁰⁰⌋ ≥ λ m` for `M ≥ M₁` since `log₂ (M + 2) = o(M)`
(`Real.isLittleO_log_id_atTop`-type bound or an explicit `2^k ≥ k²` estimate); `2¹⁰⁰ ⌊M/2¹⁰⁰⌋ ≤ M`
(`Nat.div_mul_le_self`); `32 ⌊ε/32⌋ ≤ ε` (`Nat.floor_le`); `c_pt, 64 ≤ ε` from
`log₂ (2M + 2) ≥ 1`.
Reference: proof of `cor:ham-sharp-range` (tex 1260-1266), blueprint L38. -/
theorem tolerance_admissible (lam cpt : ℕ) (hlam : 1 ≤ lam) :
    ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M → ∀ ε : ℝ,
      ((64 * lam + 64 + cpt : ℕ) : ℝ) * Real.logb 2 (2 * M + 2) ≤ ε → ε ≤ 2 * M →
        lam * headerLog M ≤ min ⌊ε / 32⌋₊ (M / 2 ^ 100) ∧
          2 ^ 100 * min ⌊ε / 32⌋₊ (M / 2 ^ 100) ≤ M ∧
          (32 * (min ⌊ε / 32⌋₊ (M / 2 ^ 100) : ℕ) : ℝ) ≤ ε ∧ (cpt : ℝ) ≤ ε ∧ 64 ≤ ε := by
  obtain ⟨M₁, hM₁⟩ := headerLog_eventually lam cpt
  refine ⟨M₁, fun M hM ε hεlo hεhi => ?_⟩
  obtain ⟨h1, h2, -⟩ := hM₁ M hM
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hL1 : 1 ≤ Real.logb 2 (2 * (M : ℝ) + 2) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_one]
    linarith
  have hmL : (headerLog M : ℝ) ≤ Real.logb 2 (2 * (M : ℝ) + 2) + 1 := by
    have h3 := clog_le_logb_add_one (M + 2)
    have h4 : Real.logb 2 ((M + 2 : ℕ) : ℝ) ≤ Real.logb 2 (2 * (M : ℝ) + 2) :=
      Real.logb_le_logb_of_le one_lt_two (by positivity) (by push_cast; linarith)
    have h5 : (headerLog M : ℝ) = (Nat.clog 2 (M + 2) : ℝ) := rfl
    linarith
  set L := Real.logb 2 (2 * (M : ℝ) + 2) with hL
  have hε : ((64 * lam + 64 + cpt : ℕ) : ℝ) * L ≤ ε := hεlo
  push_cast at hε
  have hlamR : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hcpt0 : (0 : ℝ) ≤ cpt := Nat.cast_nonneg _
  have hfloor : lam * headerLog M ≤ ⌊ε / 32⌋₊ := by
    apply Nat.le_floor
    push_cast
    have : (lam : ℝ) * headerLog M ≤ lam * (L + 1) :=
      mul_le_mul_of_nonneg_left hmL (by positivity)
    nlinarith
  have hdiv : lam * headerLog M ≤ M / 2 ^ 100 := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc lam * headerLog M * 2 ^ 100 ≤ headerLog M ^ 2 * 2 ^ 100 := Nat.mul_le_mul_right _ h1
      _ = 2 ^ 100 * headerLog M ^ 2 := by ring
      _ ≤ M := h2
  refine ⟨le_min hfloor hdiv, ?_, ?_, ?_, ?_⟩
  · calc 2 ^ 100 * min ⌊ε / 32⌋₊ (M / 2 ^ 100) ≤ 2 ^ 100 * (M / 2 ^ 100) :=
          Nat.mul_le_mul_left _ (min_le_right _ _)
      _ ≤ M := Nat.mul_div_le M (2 ^ 100)
  · have h32 : 32 * min ⌊ε / 32⌋₊ (M / 2 ^ 100) ≤ 32 * ⌊ε / 32⌋₊ :=
      Nat.mul_le_mul_left _ (min_le_left _ _)
    have h32' : ((32 * min ⌊ε / 32⌋₊ (M / 2 ^ 100) : ℕ) : ℝ) ≤ ((32 * ⌊ε / 32⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h32
    have hfl : (⌊ε / 32⌋₊ : ℝ) ≤ ε / 32 := Nat.floor_le (by nlinarith)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h32' ⊢
    linarith
  · nlinarith
  · nlinarith

/-- **The merger budget is of order `√(n ε)`** (L38).  There is a cutoff `M₂` such that for
`M ≥ M₂`, `1 ≤ E`, `0 ≤ ε ≤ 2M`, if either `ε ≤ 64 E` (unsaturated case) or `M ≤ 2¹⁰¹ E`
(saturated case), then `√(2 M ε) / 2⁸⁰ ≤ T = ⌊⌊√(M E)⌋ / 10⁶⌋`.

Proof sketch: `r = ⌊√(M E)⌋ ≥ √(M E) / 2` and `T ≥ r / (2 · 10⁶)` once `√(M E) ≥ √M ≥ 4 · 10⁶`
(`Nat.sqrt` floor bounds, `mergerBudget_eq_floor`); unsaturated: `√(2Mε) ≤ √(128 M E)`;
saturated: `√(2Mε) ≤ 2M ≤ 2^51.5 √(M E)`; both are at most `2⁸⁰ √(M E) / (4 · 10⁶)`.
Reference: proof of `cor:ham-sharp-range` (tex 1262-1269), blueprint L38 (floor bounds
`r ≥ √(ME)/2`, `T ≥ r/(2·10⁶)`). -/
theorem mergerBudget_ge_sqrt :
    ∃ M₂ : ℕ, ∀ M : ℕ, M₂ ≤ M → ∀ (E : ℕ) (ε : ℝ), 1 ≤ E → 0 ≤ ε → ε ≤ 2 * M →
      (ε ≤ 64 * E ∨ (M : ℝ) ≤ 2 ^ 101 * E) →
        Real.sqrt (2 * M * ε) / 2 ^ 80 ≤ mergerBudget M E := by
  refine ⟨(4 * 10 ^ 6) ^ 2, fun M hM E ε hE hε0 hεM hcase => ?_⟩
  set s : ℝ := Real.sqrt ((M : ℝ) * E) with hs
  have hMr : ((4 * 10 ^ 6 : ℕ) : ℝ) ^ 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hE1 : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- `s ≥ √M ≥ 4·10⁶`
  have hs_ge : (4 * 10 ^ 6 : ℝ) ≤ s := by
    rw [hs]
    calc (4 * 10 ^ 6 : ℝ) = Real.sqrt (((4 * 10 ^ 6 : ℕ) : ℝ) ^ 2) := by
          rw [Real.sqrt_sq (by positivity)]
          norm_num
      _ ≤ Real.sqrt ((M : ℝ) * E) :=
          Real.sqrt_le_sqrt (by nlinarith)
  -- `T ≥ s / (2·10⁶)`
  have hr : s < (Nat.sqrt (M * E) : ℝ) + 1 := by
    have := Real.real_sqrt_lt_nat_sqrt_succ (a := M * E)
    push_cast at this
    exact this
  have hT : (Nat.sqrt (M * E) : ℝ) < 10 ^ 6 * ((mergerBudget M E : ℝ) + 1) := by
    have h := Nat.lt_mul_div_succ (Nat.sqrt (M * E)) (show 0 < 10 ^ 6 by positivity)
    have h' : (Nat.sqrt (M * E) : ℝ) < ((10 ^ 6 * (Nat.sqrt (M * E) / 10 ^ 6 + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [mergerBudget]
    push_cast at h' ⊢
    linarith
  have hTs : s / (2 * 10 ^ 6) ≤ mergerBudget M E := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  -- the two cases
  have hsq : Real.sqrt (2 * M * ε) / 2 ^ 80 ≤ s / (2 * 10 ^ 6) := by
    rcases hcase with h | h
    · have h1 : Real.sqrt (2 * M * ε) ≤ Real.sqrt (128 * ((M : ℝ) * E)) :=
        Real.sqrt_le_sqrt (by nlinarith)
      have h2 : Real.sqrt (128 * ((M : ℝ) * E)) = Real.sqrt 128 * s := by
        rw [hs, Real.sqrt_mul (by norm_num)]
      have h3 : Real.sqrt 128 ≤ 12 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · have h1 : Real.sqrt (2 * M * ε) ≤ 2 * M := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
      have h2 : (M : ℝ) / 2 ^ 51 ≤ s := by
        rw [hs, Real.le_sqrt (by positivity) (by positivity)]
        have : (M : ℝ) * M ≤ 2 ^ 101 * (M * E) := by nlinarith
        nlinarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  linarith

/-- **The two cases of the rounded tolerance** (L38): for `ε ≥ 64` and `M ≥ 2¹⁰⁰`, the integer
`E = min ⌊ε/32⌋ ⌊M/2¹⁰⁰⌋` satisfies `ε ≤ 64 E` (if the first term is the minimum) or
`M ≤ 2¹⁰¹ E` (otherwise).

Proof sketch: `min_choice`; in the first case `⌊ε/32⌋ ≥ ε/32 - 1 ≥ ε/64` for `ε ≥ 64`
(`Nat.lt_floor_add_one`); in the second `⌊M/2¹⁰⁰⌋ ≥ (M - 2¹⁰⁰ + 1)/2¹⁰⁰ ≥ M/2¹⁰¹` for
`M ≥ 2¹⁰⁰` (`Nat.lt_div_mul_add`).
Reference: proof of `cor:ham-sharp-range` (tex 1260-1268). -/
theorem tolerance_cases {M : ℕ} {ε : ℝ} (hε : 64 ≤ ε) (hM : 2 ^ 100 ≤ M) :
    ε ≤ 64 * (min ⌊ε / 32⌋₊ (M / 2 ^ 100) : ℕ) ∨
      (M : ℝ) ≤ 2 ^ 101 * (min ⌊ε / 32⌋₊ (M / 2 ^ 100) : ℕ) := by
  rcases min_choice ⌊ε / 32⌋₊ (M / 2 ^ 100) with h | h <;> rw [h]
  · left
    have h1 := Nat.lt_floor_add_one (ε / 32)
    have h2 : (2 : ℝ) ≤ ⌊ε / 32⌋₊ := by
      have : 2 ≤ ⌊ε / 32⌋₊ := Nat.le_floor (by norm_num; linarith)
      exact_mod_cast this
    linarith
  · right
    have h1 := Nat.div_add_mod M (2 ^ 100)
    have h2 := Nat.mod_lt M (show 0 < 2 ^ 100 by positivity)
    have h3 : 1 ≤ M / 2 ^ 100 := (Nat.one_le_div_iff (by positivity)).2 hM
    have h4 : M ≤ 2 ^ 101 * (M / 2 ^ 100) := by
      have h5 : 2 ^ 101 = 2 * 2 ^ 100 := by norm_num
      rw [h5]
      nlinarith
    exact_mod_cast h4

/-- **Node L38, `sharpLowerRealTolerance`**: verbatim the frozen statement
`exists_strong_pair_without_common_model_real` of `StrongMerging.Statements`. -/
theorem exists_strong_pair_without_common_model_real' (V : Map) (hV : isOptimalConditional V) :
    ∃ (C c : ℝ) (cpt M₀ : ℕ), 0 < C ∧ 0 < c ∧
      ∀ M : ℕ, M₀ ≤ M → 2048 ∣ M → ∀ ε : ℝ, C * Real.logb 2 (2 * M + 2) ≤ ε → ε ≤ 2 * M →
        ∃ (x : BitString) (A B : Finset BitString), x.length = 2 * M ∧
          IsStrongModel x A ε ∧ IsSufficientModel V x A ε ∧
          IsStrongModel x B ε ∧ IsSufficientModel V x B ε ∧ A ∩ B = {x} ∧
          pointTotalC A x ≤ cpt ∧ pointTotalC B x ≤ cpt ∧
          ∀ D : Finset BitString, x ∈ D →
            c * Real.sqrt (2 * M * ε) <
              max (modelScore V D x) (max (setTotalC D A) (setTotalC D B)) := by
  obtain ⟨lam, cpt, M₀, hlam, h37⟩ := exists_strong_pair_without_common_model' V hV
  obtain ⟨M₁, hM₁⟩ := tolerance_admissible lam cpt hlam
  obtain ⟨M₂, hM₂⟩ := mergerBudget_ge_sqrt
  refine ⟨((64 * lam + 64 + cpt : ℕ) : ℝ), 1 / 2 ^ 80, cpt, max M₀ (max M₁ (max M₂ (2 ^ 100))),
    by positivity, by positivity, fun M hM hdiv ε hεlo hεhi => ?_⟩
  have hM0 : M₀ ≤ M := le_of_max_le_left hM
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) (le_of_max_le_right hM)
  have hM2 : M₂ ≤ M :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_max_le_right hM)
  have hM100 : 2 ^ 100 ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_max_le_right hM)
  obtain ⟨hadm1, hadm2, h32, hcpt, h64⟩ := hM₁ M hM1 ε hεlo hεhi
  set E := min ⌊ε / 32⌋₊ (M / 2 ^ 100) with hE
  obtain ⟨x, A, B, hx, hptA, hptB, hsA, hsB, hAB, hno⟩ := h37 M hM0 hdiv E hadm1 hadm2
  have hE1 : 1 ≤ E := by
    have := Nat.mul_le_mul hlam (one_le_headerLog M)
    omega
  have hT := hM₂ M hM2 E ε hE1 (by linarith) hεhi (tolerance_cases h64 hM100)
  have h32' : (32 : ℝ) * E ≤ ε := by exact_mod_cast h32
  refine ⟨x, A, B, hx, le_trans hptA hcpt, ⟨hsA.1, by linarith [hsA.2]⟩, le_trans hptB hcpt,
    ⟨hsB.1, by linarith [hsB.2]⟩, hAB, hptA, hptB, fun D hD => ?_⟩
  by_contra hle
  have hmax := not_lt.mp hle
  apply hno D hD
  have h1 : modelScore V D x ≤ mergerBudget M E := by
    have := le_trans (le_max_left _ _) hmax
    rw [one_div, ← div_eq_inv_mul] at this
    linarith
  have h2 : setTotalC D A ≤ mergerBudget M E := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmax
    rw [one_div, ← div_eq_inv_mul] at this
    linarith
  have h3 : setTotalC D B ≤ mergerBudget M E := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hmax
    rw [one_div, ← div_eq_inv_mul] at this
    linarith
  refine ⟨?_, h2, h3⟩
  unfold modelScore at h1
  linarith

end Kolmogorov.StrongMerging.Lower
