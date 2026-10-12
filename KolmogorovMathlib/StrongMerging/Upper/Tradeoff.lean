import KolmogorovMathlib.StrongMerging.Upper.Tradeoff.Leaves

/-!
# The merging tradeoff and the square-root merger (blueprint H06, H07)

`sublinear-merging.tex`, Proposition `prop:tradeoff` and Theorem `thm:main` (tex ~112–160), the
sections "Residual compression and stopping" (tex ~382) and "The mass bound and parameter choice"
(tex ~491); blueprint `bp-upper-hierarchy`, paragraphs "Point selector and score" and "Balancing".

The proof is assembled in the order the paper prescribes:
1. `exists_calInstance`: a real-tolerance instance gives an integer calibrated instance
   (`CalInstance`) at `e = ⌈ε⌉` with two total witnesses of length `≤ e`.
2. The model `D = selectModelAt c₂ R p_A p_B e x` (H05's semantic selector).  Its *raw* bounds
   (`RawBounds`: score `≤ R + k H`, endpoint costs `≤ JL + k H`) are proved separately in the
   small-degree branch (`rawBounds_small`) and in the hierarchy branch (`rawBounds_big`, from the
   residual bound H04, the local decoder H03 and the score chain rule).
3. `tradeoffBounds_of_raw`: the joint-complexity bounds come from the point bound
   `CT(D | x) ≤ c_pt H` (established first, by the selector), then the mass transfer U06 and the
   elementary inequality `JL ≤ c₂ (H + n H / R)` give `TradeoffBounds`.
4. `tradeoff_core` fixes the constants in the noncircular order (U04/H04 constant `u`, then `c₂`
   with `u + u ⌈log₂ (c₂ + 2)⌉ < c₂`, then the selector constants, then `c`), and
   `exists_merger_tradeoff'` (H06) and `exists_sqrt_merger'` (H07) are the frozen statements of
   `Statements.lean`.

The first part of the development is in `KolmogorovMathlib.StrongMerging.Upper.Tradeoff.Leaves`,
imported here.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### Raw bounds of the construction -/

/-- The raw bounds of a model `D` before the conversion to `TradeoffBounds`: `x ∈ D`,
`Score(D, x) ≤ R + k H` and `CT(D | A), CT(D | B) ≤ JL + k H`, with `L = c₂ H`,
`J = ⌊n / R⌋ + 1`. -/
def RawBounds (V : Map) (n e R c₂ k : ℕ) (x : BitString) (A B D : Finset BitString) : Prop :=
  x ∈ D ∧ modelScore V D x ≤ (R : ℝ) + (k : ℝ) * (baseBudget n e : ℝ) ∧
    setTotalC D A ≤ (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) +
      (k : ℝ) * (baseBudget n e : ℝ) ∧
    setTotalC D B ≤ (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) +
      (k : ℝ) * (baseBudget n e : ℝ)

/-- Raw bounds are monotone in the constant `k`. -/
theorem RawBounds.mono {V : Map} {n e R c₂ k k' : ℕ} {x : BitString} {A B D : Finset BitString}
    (h : RawBounds V n e R c₂ k x A B D) (hk : k ≤ k') : RawBounds V n e R c₂ k' x A B D := by
  have hk' : (k : ℝ) ≤ k' := by exact_mod_cast hk
  have hH : (0 : ℝ) ≤ baseBudget n e := Nat.cast_nonneg _
  have hmul : (k : ℝ) * baseBudget n e ≤ k' * baseBudget n e := mul_le_mul_of_nonneg_right hk' hH
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, by linarith, by linarith, by linarith⟩

/-- The tradeoff bounds are monotone in the constant. -/
theorem TradeoffBounds.mono {V : Map} {n e R c c' : ℕ} {x : BitString} {A B D : Finset BitString}
    (h : TradeoffBounds V n e R c x A B D) (hc : c ≤ c') : TradeoffBounds V n e R c' x A B D := by
  have hc' : (c : ℝ) ≤ c' := by exact_mod_cast hc
  have hX : (0 : ℝ) ≤ (R : ℝ) + baseBudget n e := by positivity
  have hY : (0 : ℝ) ≤ (baseBudget n e : ℝ) + n * baseBudget n e / R := by positivity
  have m1 := mul_le_mul_of_nonneg_right hc' hX
  have m2 := mul_le_mul_of_nonneg_right hc' hY
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The small-degree branch** (tex ~316–331).  If `min a b ≤ JL`, the selected model is the
original model of the larger bucket (ties to `B`); it is `e`-sufficient, and its endpoint costs are
at most the smaller bucket (`≤ JL`) plus `O(H)`, and a constant on its own side. -/
theorem rawBounds_small (V : Map) (hV : isOptimalConditional V) :
    ∀ c₂ : ℕ, ∃ k : ℕ, ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString) (pA pB : BitString)
      (R : ℕ), CalInstance V n e x A B pA pB → 1 ≤ R → R ≤ n →
        min (Nat.log 2 A.card) (Nat.log 2 B.card) ≤ (n / R + 1) * (c₂ * baseBudget n e) →
        RawBounds V n e R c₂ k x A B (selectModelAt c₂ R pA pB e x) := by
  intro c₂
  obtain ⟨cfb, hfb⟩ := totalC_fallback_le
  obtain ⟨cid, hid⟩ := totalC_self_le
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  obtain ⟨kl, hkl⟩ := logb_le_baseBudget (bsize + 3)
  refine ⟨2 + 2 * kl + cfb + cid, fun n e x A B pA pB R I hR1 hRn hsmall => ?_⟩
  have hn := I.two_le
  have hxlen := I.len
  have hoA : progOut pA x = canonicalFiniteSetCode A := progOut_eq_of_mem I.outA
  have hoB : progOut pB x = canonicalFiniteSetCode B := progOut_eq_of_mem I.outB
  have hxA : x ∈ A := I.suffA.1
  have hxB : x ∈ B := I.suffB.1
  have hHb := baseBudget_bounds hn I.e_le
  have hsel := selectModelAt_of_le (c₂ := c₂) (R := R) (e := e) (by omega) hoA hoB hxA hxB
    (by rw [hxlen]; exact hsmall)
  rw [hsel]
  have hH1 : (1 : ℝ) ≤ (baseBudget n e : ℝ) := by exact_mod_cast (by omega : 1 ≤ baseBudget n e)
  have heH : (e : ℝ) ≤ (baseBudget n e : ℝ) := by
    exact_mod_cast (show e ≤ baseBudget n e by unfold baseBudget; omega)
  have hJL0 : (0 : ℝ) ≤ (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hkl0 : (0 : ℝ) ≤ kl := Nat.cast_nonneg kl
  have hcfb0 : (0 : ℝ) ≤ cfb := Nat.cast_nonneg cfb
  have hcid0 : (0 : ℝ) ≤ cid := Nat.cast_nonneg cid
  have hfall : ∀ (X Y : Finset BitString) (p : BitString), x ∈ X →
      IsTotalProgram universalDecompressor p → p.length ≤ e →
      canonicalFiniteSetCode Y ∈ universalDecompressor (p, x) → IsSufficientModel V x X e →
      Nat.log 2 X.card ≤ (n / R + 1) * (c₂ * baseBudget n e) →
      setTotalC Y X ≤ (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) +
        (2 + 2 * (kl : ℝ) + cfb + cid) * (baseBudget n e : ℝ) := by
    intro X Y p hxX hp hpl hpY hsX hXJ
    have h1 := hfb x X p _ hxX hp hpY
    have h2 := logb_card_lt_log_add_one (⟨x, hxX⟩ : X.Nonempty)
    have hXb := (htyp n e x X hxlen I.e_le hsX).2
    have h3 : Real.logb 2 (Real.logb 2 X.card + 2) ≤ kl * baseBudget n e := by
      refine le_trans ?_ (hkl n e)
      apply logb_add_two_mono (logb_card_nonneg_of_mem hxX)
      have hb : (Nat.log 2 X.card : ℝ) ≤ 2 * n + bsize := by exact_mod_cast hXb
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hbs0 : (0 : ℝ) ≤ bsize := Nat.cast_nonneg bsize
      push_cast
      nlinarith
    have hXJ' : (Nat.log 2 X.card : ℝ) ≤ (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) := by
      exact_mod_cast hXJ
    have hpl' : (p.length : ℝ) ≤ e := by exact_mod_cast hpl
    exact arith_fallback h1 h2 h3 hXJ' hpl' heH hH1 hcfb0 (by linarith)
  have hself : ∀ Y : Finset BitString, setTotalC Y Y ≤
      (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) +
        (2 + 2 * (kl : ℝ) + cfb + cid) * (baseBudget n e : ℝ) := by
    intro Y
    exact arith_const (hid _) hJL0 hH1 hcid0 (by linarith)
  have hscore : ∀ Y : Finset BitString, IsSufficientModel V x Y e →
      modelScore V Y x ≤ (R : ℝ) + (2 + 2 * (kl : ℝ) + cfb + cid) * (baseBudget n e : ℝ) := by
    intro Y hY
    exact arith_score_small ((isSufficientModel_iff_modelScore_le V x Y e).1 hY).2 heH
      (Nat.cast_nonneg _) (by linarith) (by linarith)
  have hK : ((2 + 2 * kl + cfb + cid : ℕ) : ℝ) = 2 + 2 * (kl : ℝ) + cfb + cid := by
    push_cast
    ring
  unfold RawBounds
  rw [hK]
  split_ifs with hab
  · refine ⟨hxB, hscore B I.suffB, ?_, hself B⟩
    exact hfall A B pB hxA I.totB I.lenB I.outB I.suffA (by rwa [min_eq_left hab] at hsmall)
  · refine ⟨hxA, hscore A I.suffA, hself A, ?_⟩
    exact hfall B A pA hxB I.totA I.lenA I.outA I.suffB
      (by rwa [min_eq_right (by omega)] at hsmall)

/-- **The hierarchy branch** (tex ~436–480).  If `JL < min a b` and `CT(D | x) ≤ c_pt H` for the
selected parent `D = F` of the first residual along `x`, then `Score(F, x) ≤ R + k H` (residual
bound H04 and the score chain rule) and `CT(F | A), CT(F | B) ≤ JL + k H` (one global local rank,
H03). -/
theorem rawBounds_big (V : Map) (hV : isOptimalConditional V) :
    ∃ u : ℕ, ∀ c₂ : ℕ, u + u * headerLog c₂ < c₂ → ∀ cpt : ℕ, ∃ k : ℕ,
      ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString) (pA pB : BitString) (R : ℕ),
        CalInstance V n e x A B pA pB → 1 ≤ R → R ≤ n →
        (n / R + 1) * (c₂ * baseBudget n e) < min (Nat.log 2 A.card) (Nat.log 2 B.card) →
        pointTotalC (selectModelAt c₂ R pA pB e x) x ≤ cpt * baseBudget n e →
        RawBounds V n e R c₂ k x A B (selectModelAt c₂ R pA pB e x) := by
  obtain ⟨u, hres⟩ := upperResidualBound V hV
  refine ⟨u, fun c₂ hc₂ cpt => ?_⟩
  obtain ⟨cloc, hloc⟩ := upperLocalBlockDecoder
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  obtain ⟨kh, hkh⟩ := hdrCost_le bsize
  obtain ⟨cs, hcs⟩ := modelScore_le_of_deficiency V hV
  obtain ⟨ct, hct⟩ := condC_le_totalC_add V hV
  obtain ⟨blit, hblit⟩ := plainC_le_length_add V hV
  obtain ⟨kl, hkl⟩ := logb_le_baseBudget (blit + ct + 2 * cpt + 2)
  refine ⟨3 + cpt + ct + cs * kl + 2 + cloc * (kh + headerLog c₂ + 1),
    fun n e x A B pA pB R I hR1 hRn hbig hpt => ?_⟩
  have hn := I.two_le
  have hxlen := I.len
  have hoA : progOut pA x = canonicalFiniteSetCode A := progOut_eq_of_mem I.outA
  have hoB : progOut pB x = canonicalFiniteSetCode B := progOut_eq_of_mem I.outB
  have hxA : x ∈ A := I.suffA.1
  have hxB : x ∈ B := I.suffB.1
  have hHb := baseBudget_bounds hn I.e_le
  have hH1 : (1 : ℝ) ≤ (baseBudget n e : ℝ) := by exact_mod_cast (by omega : 1 ≤ baseBudget n e)
  have heH : (e : ℝ) ≤ (baseBudget n e : ℝ) := by
    exact_mod_cast (show e ≤ baseBudget n e by unfold baseBudget; omega)
  have hHn : (baseBudget n e : ℝ) ≤ 2 * n := by exact_mod_cast hHb.2
  have hbigA : (n / R + 1) * (c₂ * baseBudget n e) < Nat.log 2 A.card :=
    lt_of_lt_of_le hbig (min_le_left _ _)
  have hbigB : (n / R + 1) * (c₂ * baseBudget n e) < Nat.log 2 B.card :=
    lt_of_lt_of_le hbig (min_le_right _ _)
  -- the actual edge and the first residual along its path
  have hxG : x ∈ shapeEdges (instShape pA pB n (Nat.log 2 A.card) (Nat.log 2 B.card)) :=
    mem_shapeEdges_of _ hxlen hoA hoB hxA hxB rfl rfl
  obtain ⟨j, F, hsel, hjJ, hF, hxF, hxres⟩ :=
    firstResidualBlock_spec (instShape pA pB n (Nat.log 2 A.card) (Nat.log 2 B.card)) R
      (c₂ * baseBudget n e) (n / R + 1) (lt_div_add_one_mul hR1) hxG
  have hD : selectModelAt c₂ R pA pB e x = F := by
    subst hxlen
    exact selectModelAt_of_lt (by omega) hoA hoB hxA hxB hbig hsel
  rw [hD] at hpt ⊢
  have hcpt0 : (0 : ℝ) ≤ cpt := Nat.cast_nonneg cpt
  have hct0 : (0 : ℝ) ≤ ct := Nat.cast_nonneg ct
  have hcs0 : (0 : ℝ) ≤ cs := Nat.cast_nonneg cs
  have hkl0 : (0 : ℝ) ≤ kl := Nat.cast_nonneg kl
  have hcloc0 : (0 : ℝ) ≤ cloc := Nat.cast_nonneg cloc
  have hkh0 : (0 : ℝ) ≤ kh := Nat.cast_nonneg kh
  have hh₂0 : (0 : ℝ) ≤ headerLog c₂ := Nat.cast_nonneg _
  have hcskl : (0 : ℝ) ≤ cs * kl := mul_nonneg hcs0 hkl0
  have hcl : (0 : ℝ) ≤ cloc * (kh + headerLog c₂ + 1) := by positivity
  -- score: residual bound H04 and the chain rule
  have hres' := hres c₂ hc₂ n e x A B pA pB R j F hn hxlen I.e_le I.suffA I.suffB I.totA I.totB
    I.lenA I.lenB I.outA I.outB hR1 hRn hbigA hbigB hjJ hF hxres
  have hCFx : condC V (canonicalFiniteSetCode F) x ≤ cpt * baseBudget n e + ct := by
    have h1 := hct (canonicalFiniteSetCode F) x
    have h2 : totalC (canonicalFiniteSetCode F) x ≤ cpt * baseBudget n e := hpt
    linarith
  have hCx : plainC V x ≤ n + blit := by
    have := hblit x
    rw [hxlen] at this
    exact this
  have hN := arith_N hCx hCFx hHn (Nat.cast_nonneg n) (Nat.cast_nonneg blit) hct0 hcpt0
  have hsc := hcs _ x F hN
  have hlog : Real.logb 2 (((blit : ℝ) + ct + 2 * cpt + 2) * (n + 1) + 2) ≤
      kl * baseBudget n e := by
    have := hkl n e
    push_cast at this
    exact this
  have hcslog : (cs : ℝ) * Real.logb 2 (((blit : ℝ) + ct + 2 * cpt + 2) * (n + 1) + 2) ≤
      cs * kl * baseBudget n e := by
    have := mul_le_mul_of_nonneg_left hlog hcs0
    rw [← mul_assoc] at this
    exact this
  -- endpoints: the local block decoder H03
  have hjn : j ≤ n := by
    have : n / R ≤ n := Nat.div_le_self n R
    omega
  have hjJL : j * (c₂ * baseBudget n e) ≤ (n / R + 1) * (c₂ * baseBudget n e) :=
    Nat.mul_le_mul_right _ hjJ.le
  have hjLa : j * (c₂ * baseBudget n e) ≤ Nat.log 2 A.card := by omega
  have hjLb : j * (c₂ * baseBudget n e) ≤ Nat.log 2 B.card := by omega
  have hab := (htyp n e x A hxlen I.e_le I.suffA).2
  have hbb := (htyp n e x B hxlen I.e_le I.suffB).2
  have hlA : (pA.length : ℝ) ≤ e := by exact_mod_cast I.lenA
  have hlB : (pB.length : ℝ) ≤ e := by exact_mod_cast I.lenB
  have hjJL' : (j : ℝ) * ((c₂ * baseBudget n e : ℕ) : ℝ) ≤
      (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) := by
    exact_mod_cast hjJL
  have hend : ∀ side : Bool,
      totalC (canonicalFiniteSetCode F)
        (sideOut (instShape pA pB n (Nat.log 2 A.card) (Nat.log 2 B.card)) side x) ≤
        (((n / R + 1) * (c₂ * baseBudget n e) : ℕ) : ℝ) +
          (3 + (cpt : ℝ) + ct + cs * kl + 2 + cloc * (kh + headerLog c₂ + 1)) *
            (baseBudget n e : ℝ) := by
    intro side
    have h1 := hloc pA pB n _ _ R _ j side F x I.totA I.totB hjLa hjLb hF hxF
    have hhdr := hkh c₂ n e _ _ R j pA pB hn I.e_le hab hbb hRn hjn I.lenA I.lenB
    generalize hdrCost [n, Nat.log 2 A.card, Nat.log 2 B.card, R, c₂ * baseBudget n e, j,
      pA.length, pB.length] = hc at h1 hhdr
    have hhdr' : (hc : ℝ) ≤ kh * baseBudget n e + headerLog c₂ := by exact_mod_cast hhdr
    exact arith_endpoint_big h1 hjJL' hlA hlB heH hhdr' hH1 hcloc0 hh₂0 (by linarith)
  have hsA : sideOut (instShape pA pB n (Nat.log 2 A.card) (Nat.log 2 B.card)) false x =
      canonicalFiniteSetCode A := by
    simp [sideOut, instShape, hoA]
  have hsB : sideOut (instShape pA pB n (Nat.log 2 A.card) (Nat.log 2 B.card)) true x =
      canonicalFiniteSetCode B := by
    simp [sideOut, instShape, hoB]
  have hK : ((3 + cpt + ct + cs * kl + 2 + cloc * (kh + headerLog c₂ + 1) : ℕ) : ℝ) =
      3 + (cpt : ℝ) + ct + cs * kl + 2 + cloc * (kh + headerLog c₂ + 1) := by
    push_cast
    ring
  unfold RawBounds
  rw [hK]
  refine ⟨hxF, ?_, ?_, ?_⟩
  · exact arith_score_big hsc hres' hCFx hcslog hH1 hct0 (by linarith)
  · have h := hend false
    rw [hsA] at h
    exact h
  · have h := hend true
    rw [hsB] at h
    exact h

/-- **From raw bounds to the tradeoff bounds** (tex ~491–520).  Given the raw bounds and the point
bound `CT(D | x) ≤ c_pt H`, the joint complexities are `O(n)` (`jointBounds_of_point`,
`upperJointBound`), the mass transfer U06 bounds the mass loss by `2 T + 2 e + O(H)`, and
`JL ≤ c₂ (H + n H / R)` (`depthLoss_le`) converts everything to `TradeoffBounds`. -/
theorem tradeoffBounds_of_raw (V : Map) (hV : isOptimalConditional V) :
    ∀ c₂ k cpt : ℕ, ∃ c : ℕ, ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString)
      (pA pB : BitString) (R : ℕ) (D : Finset BitString),
      CalInstance V n e x A B pA pB → 1 ≤ R → R ≤ n →
      RawBounds V n e R c₂ k x A B D → pointTotalC D x ≤ cpt * baseBudget n e →
        TradeoffBounds V n e R c x A B D := by
  intro c₂ k cpt
  obtain ⟨cm, hcm⟩ := upperMassTransfer V hV
  obtain ⟨bj, hbj⟩ := upperJointBound V hV
  obtain ⟨cj, hcj⟩ := jointBounds_of_point V hV
  obtain ⟨kl, hkl⟩ := logb_le_baseBudget ((bj + cj) * (1 + 2 * cpt))
  refine ⟨2 * c₂ + 2 * k + 2 + cm * kl + 1, fun n e x A B pA pB R D I hR1 hRn hraw hpt => ?_⟩
  obtain ⟨hxD, hsc, hTA, hTB⟩ := hraw
  have hn := I.two_le
  have hHb := baseBudget_bounds hn I.e_le
  have hH1 : (1 : ℝ) ≤ (baseBudget n e : ℝ) := by exact_mod_cast (by omega : 1 ≤ baseBudget n e)
  have heH : (e : ℝ) ≤ (baseBudget n e : ℝ) := by
    exact_mod_cast (show e ≤ baseBudget n e by unfold baseBudget; omega)
  have hHn : (baseBudget n e : ℝ) ≤ 2 * n := by exact_mod_cast hHb.2
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR1
  have hQ0 : (0 : ℝ) ≤ (n : ℝ) * baseBudget n e / R := by positivity
  have hJL := depthLoss_le c₂ (baseBudget n e) n R hR1
  have hTA' : setTotalC D A ≤ c₂ * ((baseBudget n e : ℝ) + n * baseBudget n e / R) +
      k * baseBudget n e := by linarith
  have hTB' : setTotalC D B ≤ c₂ * ((baseBudget n e : ℝ) + n * baseBudget n e / R) +
      k * baseBudget n e := by linarith
  have hcpt0 : (0 : ℝ) ≤ cpt * baseBudget n e := by positivity
  obtain ⟨j1, j2, j3, j4⟩ :=
    hcj n e (cpt * baseBudget n e) x A B D I.len I.e_le I.suffA I.suffB hcpt0 hpt
  obtain ⟨-, b2, b3⟩ := hbj n e x A B I.len I.e_le I.suffA I.suffB
  obtain ⟨hjN, hbN⟩ := arith_joint (bj := bj) (cj := cj) (cpt := cpt) hHn (Nat.cast_nonneg n)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmass := hcm _ _ _ x A B D I.suffA I.suffB hxD (b3.trans hbN) (j2.trans hjN)
    (j1.trans hjN) (b2.trans hbN) (j3.trans hjN) (j4.trans hjN) hTA' hTB'
  have hlog : Real.logb 2 (((bj : ℝ) + cj) * (1 + 2 * cpt) * (n + 1) + 2) ≤
      kl * baseBudget n e := by
    have := hkl n e
    push_cast at this
    exact this
  have hcmlog := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) cm)
  have hfin := arith_tradeoff (m := overlapMass A B - Real.logb 2 D.card)
    (Nat.cast_nonneg R) hH1 hQ0 heH (Nat.cast_nonneg c₂)
    (Nat.cast_nonneg k) (Nat.cast_nonneg cm) (Nat.cast_nonneg kl) hsc hTA' hTB'
    (by linarith [hmass, hcmlog])
  have hC : ((2 * c₂ + 2 * k + 2 + cm * kl + 1 : ℕ) : ℝ) =
      2 * (c₂ : ℝ) + 2 * k + 2 + cm * kl + 1 := by
    push_cast
    ring
  unfold TradeoffBounds
  rw [hC]
  refine ⟨hfin.1, hfin.2.1, hfin.2.2.1, ?_⟩
  have h4 := hfin.2.2.2
  unfold overlapMass at h4
  linarith

/-! ### H06 -/

/-- **The tradeoff at hardwired `R`, with the point bound as hypothesis** (the core of H06).  The
constants are chosen in the noncircular order: the residual constant `u` (H04), then `c₂` with
`u + u ⌈log₂ (c₂ + 2)⌉ < c₂` (`exists_const_gt_header`), then for every point constant `c_pt` the
tradeoff constant `c`. -/
theorem tradeoff_core (V : Map) (hV : isOptimalConditional V) :
    ∃ c₂ : ℕ, ∀ cpt : ℕ, ∃ c : ℕ, ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString)
      (pA pB : BitString) (R : ℕ), CalInstance V n e x A B pA pB → 1 ≤ R → R ≤ n →
      pointTotalC (selectModelAt c₂ R pA pB e x) x ≤ cpt * baseBudget n e →
        x ∈ selectModelAt c₂ R pA pB e x ∧
          TradeoffBounds V n e R c x A B (selectModelAt c₂ R pA pB e x) := by
  obtain ⟨u, hbig⟩ := rawBounds_big V hV
  obtain ⟨c₂, hc₂⟩ := exists_const_gt_header u u
  refine ⟨c₂, fun cpt => ?_⟩
  obtain ⟨k₁, hk₁⟩ := rawBounds_small V hV c₂
  obtain ⟨k₂, hk₂⟩ := hbig c₂ hc₂ cpt
  obtain ⟨c, hc⟩ := tradeoffBounds_of_raw V hV c₂ (k₁ + k₂) cpt
  refine ⟨c, fun n e x A B pA pB R I hR1 hRn hpt => ?_⟩
  have hraw : RawBounds V n e R c₂ (k₁ + k₂) x A B (selectModelAt c₂ R pA pB e x) := by
    by_cases hs : min (Nat.log 2 A.card) (Nat.log 2 B.card) ≤ (n / R + 1) * (c₂ * baseBudget n e)
    · exact (hk₁ n e x A B pA pB R I hR1 hRn hs).mono (by omega)
    · exact (hk₂ n e x A B pA pB R I hR1 hRn (not_le.mp hs) hpt).mono (by omega)
  exact ⟨hraw.1, hc n e x A B pA pB R _ I hR1 hRn hraw hpt⟩

/-- The hardwired rule selects at the hardwired exponent. -/
theorem selectModel_const {c₂ R e : ℕ} {pA pB x : BitString} (h1 : 1 ≤ R) (h2 : R ≤ x.length) :
    selectModel c₂ (fun _ _ => R) pA pB e x = selectModelAt c₂ R pA pB e x := by
  unfold selectModel
  rw [clipR_of_le h1 h2]

/-- **Selector cost as an `O(H)` point bound**:
`7 (e + 1) + 4 ⌈log₂ (R + 2)⌉ + c ≤ (18 + c) H` for `R ≤ n`, `n ≥ 2`. -/
theorem point_le_cpt {n e R c : ℕ} (hn : 2 ≤ n) (hRn : R ≤ n) :
    7 * ((e : ℝ) + 1) + 4 * (headerLog R : ℝ) + c ≤ ((18 + c : ℕ) : ℝ) * baseBudget n e := by
  have hR : headerLog R ≤ headerLog n := Nat.clog_mono_right 2 (by omega)
  have h2 := two_le_headerLog hn
  have hH : headerLog n ≤ baseBudget n e := by unfold baseBudget; omega
  have he : e ≤ baseBudget n e := by unfold baseBudget; omega
  have hR' : (headerLog R : ℝ) ≤ baseBudget n e := by exact_mod_cast hR.trans hH
  have he' : (e : ℝ) ≤ baseBudget n e := by exact_mod_cast he
  have hH1 : (1 : ℝ) ≤ baseBudget n e := by exact_mod_cast (show 1 ≤ baseBudget n e by omega)
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hcH := mul_le_mul_of_nonneg_left hH1 hc0
  push_cast
  nlinarith

/-- **Selector cost against the logarithmic point budget** (tex ~2408, "an arbitrary hardwired
`R` costs a further `O(log n)`"):
`7 (e + 1) + 4 ⌈log₂ (R + 2)⌉ + c ≤ (c + 11) (e + log₂ (n + 2))` for `R ≤ n`, `n ≥ 2`. -/
theorem point_le_log {n e R c : ℕ} (hn : 2 ≤ n) (hRn : R ≤ n) :
    7 * ((e : ℝ) + 1) + 4 * (headerLog R : ℝ) + c ≤ (c + 11 : ℝ) * (e + Real.logb 2 (n + 2)) := by
  have hR : headerLog R ≤ headerLog n := Nat.clog_mono_right 2 (by omega)
  have h1 : (headerLog n : ℝ) ≤ Real.logb 2 (n + 2) + 1 := by
    have := clog_le_logb_add_one (n + 2)
    push_cast at this
    exact this
  have h2 : (2 : ℝ) ≤ Real.logb 2 (n + 2) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_two]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hR' : (headerLog R : ℝ) ≤ headerLog n := by exact_mod_cast hR
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  nlinarith [mul_nonneg hc he, mul_nonneg hc (by linarith : (0 : ℝ) ≤ Real.logb 2 (n + 2) - 2)]

/-- **Selector cost with a fixed rule**: `7 (e + 1) + 4 ⌈log₂ 2⌉ + c ≤ (c + 11) (e + 1)`. -/
theorem point_le_one {e c : ℕ} :
    7 * ((e : ℝ) + 1) + 4 * (headerLog 0 : ℝ) + c ≤ (c + 11 : ℝ) * (e + 1) := by
  have h0 : headerLog 0 = 1 := by
    unfold headerLog
    rw [show (0 + 2 : ℕ) = 2 ^ 1 by norm_num, Nat.clog_pow 2 1 one_lt_two]
  rw [h0]
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  push_cast
  nlinarith

/-- **Quantitative merging tradeoff (blueprint H06, `UpperTradeoff`; `prop:tradeoff`).**  The
frozen statement `exists_merger_tradeoff` of `Statements.lean`, verbatim. -/
theorem exists_merger_tradeoff' (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ,
      (∀ (n : ℕ) (ε : ℝ) (x : BitString) (A B : Finset BitString),
        IsMergingInstance V n ε x A B → ∀ R : ℕ, 1 ≤ R → R ≤ n →
          ∃ D : Finset BitString, x ∈ D ∧ TradeoffBounds V n ⌈ε⌉₊ R c x A B D ∧
            pointTotalC D x ≤ c * (⌈ε⌉₊ + Real.logb 2 (n + 2))) ∧
      ∀ ρ : ℕ → ℕ → ℕ, Computable₂ ρ → ∃ cρ : ℕ,
        ∀ (n : ℕ) (ε : ℝ) (x : BitString) (A B : Finset BitString),
          IsMergingInstance V n ε x A B → ∃ D : Finset BitString, x ∈ D ∧
            TradeoffBounds V n ⌈ε⌉₊ (min n (max 1 (ρ n ⌈ε⌉₊))) c x A B D ∧
            pointTotalC D x ≤ cρ * (⌈ε⌉₊ + 1) := by
  obtain ⟨c₂, hcore⟩ := tradeoff_core V hV
  obtain ⟨cH, hsel⟩ := upperHierarchySelector c₂ (fun _ _ h => h)
    (Computable.snd.comp Computable.snd)
  obtain ⟨c, hc⟩ := hcore (18 + cH)
  refine ⟨c + cH + 11, fun n ε x A B hI R hR1 hRn => ?_, fun ρ hρ => ?_⟩
  · obtain ⟨pA, pB, I⟩ := exists_calInstance hI
    have hpt : pointTotalC (selectModelAt c₂ R pA pB ⌈ε⌉₊ x) x ≤
        7 * ((⌈ε⌉₊ : ℕ) + 1) + 4 * headerLog R + cH := by
      have h := hsel pA pB ⌈ε⌉₊ R x I.totA I.totB I.lenA I.lenB
      rw [selectModel_const hR1 (I.len ▸ hRn)] at h
      exact h
    obtain ⟨hxD, hTB⟩ := hc n _ x A B pA pB R I hR1 hRn
      (hpt.trans (point_le_cpt I.two_le hRn))
    refine ⟨_, hxD, TradeoffBounds.mono hTB (by omega), ?_⟩
    have h1 := hpt.trans (point_le_log (c := cH) (e := ⌈ε⌉₊) I.two_le hRn)
    have h2 : (0 : ℝ) ≤ (⌈ε⌉₊ : ℝ) + Real.logb 2 (n + 2) := by
      have := Real.logb_nonneg (b := 2) one_lt_two (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith : (1 : ℝ) ≤ (n : ℝ) + 2)
      positivity
    have h3 : ((cH : ℝ) + 11) ≤ ((c + cH + 11 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) c]
    exact h1.trans (mul_le_mul_of_nonneg_right h3 h2)
  · obtain ⟨cρ, hselρ⟩ := upperHierarchySelector c₂ (fun n e _ => ρ n e)
      (hρ.comp Computable.fst (Computable.fst.comp Computable.snd))
    refine ⟨cρ + 11, fun n ε x A B hI => ?_⟩
    obtain ⟨pA, pB, I⟩ := exists_calInstance hI
    have hR := one_le_clipR (r := ρ n ⌈ε⌉₊) (by have := I.two_le; omega : 1 ≤ n)
    have hpt : pointTotalC (selectModelAt c₂ (clipR n (ρ n ⌈ε⌉₊)) pA pB ⌈ε⌉₊ x) x ≤
        7 * ((⌈ε⌉₊ : ℕ) + 1) + 4 * headerLog (clipR n (ρ n ⌈ε⌉₊)) + cH := by
      have h := hsel pA pB ⌈ε⌉₊ (clipR n (ρ n ⌈ε⌉₊)) x I.totA I.totB I.lenA I.lenB
      rw [selectModel_const hR.1 (I.len ▸ hR.2)] at h
      exact h
    obtain ⟨hxD, hTB⟩ := hc n _ x A B pA pB _ I hR.1 hR.2
      (hpt.trans (point_le_cpt I.two_le hR.2))
    have hptρ : pointTotalC (selectModelAt c₂ (clipR n (ρ n ⌈ε⌉₊)) pA pB ⌈ε⌉₊ x) x ≤
        7 * ((⌈ε⌉₊ : ℕ) + 1) + 4 * headerLog 0 + cρ := by
      have h := hselρ pA pB ⌈ε⌉₊ 0 x I.totA I.totB I.lenA I.lenB
      have he : selectModel c₂ (fun n e => ρ n e) pA pB ⌈ε⌉₊ x =
          selectModelAt c₂ (clipR n (ρ n ⌈ε⌉₊)) pA pB ⌈ε⌉₊ x := by
        unfold selectModel
        rw [I.len]
      rw [he] at h
      exact h
    refine ⟨_, hxD, TradeoffBounds.mono hTB (by omega), ?_⟩
    have h1 := hptρ.trans (point_le_one (c := cρ) (e := ⌈ε⌉₊))
    have h3 : ((cρ : ℝ) + 11) = ((cρ + 11 : ℕ) : ℝ) := by push_cast; ring
    rw [h3] at h1
    exact h1

/-! ### H07 -/

/-- The square-root rule `R = ⌊√(n H)⌋ + 1` before clipping, with `H = e + ⌈log₂ (n + 2)⌉`;
computed by the integer square root. -/
def sqrtRule (n e : ℕ) : ℕ :=
  Nat.sqrt (n * baseBudget n e) + 1

/-- **The square-root rule is computable** (`Primrec.nat_sqrt` and `baseBudget_primrec`). -/
theorem sqrtRule_computable : Computable₂ sqrtRule := by
  have h : Primrec₂ sqrtRule :=
    (Primrec.nat_add.comp (Primrec.nat_sqrt.comp (Primrec.nat_mul.comp Primrec.fst
      baseBudget_primrec)) (Primrec.const 1)).of_eq fun _ => rfl
  exact h.to_comp

/-- **Balancing** (tex ~522–545, node H07 obligation "unclipped/clipped inequalities").  With
`R = min n (max 1 (⌊√(n H)⌋ + 1))`, `S = √(n H)`, for `n ≥ 2` and `e ≤ n`:
`R + H ≤ 4 S` and `H + n H / R ≤ 4 S`.  Here `2 ≤ H ≤ 2n` gives `S ≥ 2` and `H ≤ 3S/2`;
unclipped, `S < R ≤ S + 1` and `n H / R ≤ S`; clipped (`R = n ≤ ⌊S⌋`), `n ≤ S`. -/
theorem sqrtRule_bounds {n e : ℕ} (hn : 2 ≤ n) (he : e ≤ n) :
    ((min n (max 1 (sqrtRule n e)) : ℕ) : ℝ) + baseBudget n e ≤ 4 * rootScale n e ∧
      (baseBudget n e : ℝ) + n * baseBudget n e / ((min n (max 1 (sqrtRule n e)) : ℕ) : ℝ) ≤
        4 * rootScale n e := by
  obtain ⟨hH2, hHn⟩ := baseBudget_bounds hn he
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hH2' : (2 : ℝ) ≤ baseBudget n e := by exact_mod_cast hH2
  have hHn' : (baseBudget n e : ℝ) ≤ 2 * n := by exact_mod_cast hHn
  have hm : ((n * baseBudget n e : ℕ) : ℝ) = (n : ℝ) * baseBudget n e := by push_cast; ring
  have hS : rootScale n e = Real.sqrt ((n * baseBudget n e : ℕ) : ℝ) := by
    unfold rootScale
    rw [hm]
  have hnH : (4 : ℝ) ≤ n * baseBudget n e := by nlinarith
  have hSsq : rootScale n e ^ 2 = (n : ℝ) * baseBudget n e := by
    unfold rootScale
    rw [Real.sq_sqrt (by positivity)]
  have hS0 : 0 ≤ rootScale n e := Real.sqrt_nonneg _
  have hlo : (Nat.sqrt (n * baseBudget n e) : ℝ) ≤ rootScale n e := by
    rw [hS]
    exact Real.nat_sqrt_le_real_sqrt
  have hhi : rootScale n e < Nat.sqrt (n * baseBudget n e) + 1 := by
    rw [hS]
    exact Real.real_sqrt_lt_nat_sqrt_succ
  have hS2 : 2 ≤ rootScale n e := by nlinarith
  have hHS : (baseBudget n e : ℝ) ≤ 3 / 2 * rootScale n e := by
    nlinarith [mul_le_mul_of_nonneg_right hHn' (by positivity : (0 : ℝ) ≤ baseBudget n e)]
  have hsr : sqrtRule n e = Nat.sqrt (n * baseBudget n e) + 1 := rfl
  have hmax : max 1 (Nat.sqrt (n * baseBudget n e) + 1) = Nat.sqrt (n * baseBudget n e) + 1 :=
    max_eq_right (by omega)
  rw [hsr, hmax]
  by_cases hc : Nat.sqrt (n * baseBudget n e) + 1 ≤ n
  · rw [min_eq_right hc]
    push_cast
    have hRpos : (0 : ℝ) < (Nat.sqrt (n * baseBudget n e) : ℝ) + 1 := by positivity
    refine ⟨by linarith, ?_⟩
    have hdiv : (n : ℝ) * baseBudget n e / ((Nat.sqrt (n * baseBudget n e) : ℝ) + 1) ≤
        rootScale n e := by
      rw [div_le_iff₀ hRpos]
      nlinarith
    linarith
  · have hc' : n ≤ Nat.sqrt (n * baseBudget n e) + 1 := by omega
    rw [min_eq_left hc']
    have hnS : (n : ℝ) ≤ rootScale n e := by
      have h1 : n ≤ Nat.sqrt (n * baseBudget n e) := by omega
      have h2 : (n : ℝ) ≤ Nat.sqrt (n * baseBudget n e) := by exact_mod_cast h1
      linarith
    have hnpos : (0 : ℝ) < n := by linarith
    refine ⟨by linarith, ?_⟩
    have hdiv : (n : ℝ) * baseBudget n e / n = baseBudget n e := by field_simp
    rw [hdiv]
    linarith

/-- **Square-root merger (blueprint H07, `UpperSqrtMerging`; `thm:main`).**  The frozen
statement `exists_sqrt_merger` of `Statements.lean`, verbatim. -/
theorem exists_sqrt_merger' (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n : ℕ) (ε : ℝ) (x : BitString) (A B : Finset BitString),
      IsMergingInstance V n ε x A B → ∃ D : Finset BitString, x ∈ D ∧
        pointTotalC D x ≤ c * (⌈ε⌉₊ + 1) ∧
        setC V D + Real.logb 2 D.card ≤ plainC V x + c * rootScale n ⌈ε⌉₊ ∧
        setTotalC D A ≤ c * rootScale n ⌈ε⌉₊ ∧ setTotalC D B ≤ c * rootScale n ⌈ε⌉₊ ∧
        Real.logb 2 A.card + Real.logb 2 B.card - Real.logb 2 (A ∩ B).card -
          c * rootScale n ⌈ε⌉₊ ≤ Real.logb 2 D.card := by
  obtain ⟨c, -, hrule⟩ := exists_merger_tradeoff' V hV
  obtain ⟨cρ, hρ⟩ := hrule sqrtRule sqrtRule_computable
  refine ⟨4 * c + cρ, fun n ε x A B hI => ?_⟩
  obtain ⟨D, hxD, ⟨h1, h2, h3, h4⟩, hpt⟩ := hρ n ε x A B hI
  have hn : 2 ≤ n := hI.1
  have he : ⌈ε⌉₊ ≤ n := Nat.ceil_le.mpr hI.2.2.1
  obtain ⟨hb1, hb2⟩ := sqrtRule_bounds hn he
  have hS : (0 : ℝ) ≤ rootScale n ⌈ε⌉₊ := Real.sqrt_nonneg _
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hcρ0 : (0 : ℝ) ≤ cρ := Nat.cast_nonneg cρ
  have m1 := mul_le_mul_of_nonneg_left hb1 hc0
  have m2 := mul_le_mul_of_nonneg_left hb2 hc0
  have hCS : (4 : ℝ) * c * rootScale n ⌈ε⌉₊ ≤ ((4 * c + cρ : ℕ) : ℝ) * rootScale n ⌈ε⌉₊ := by
    push_cast
    nlinarith
  have hE : (0 : ℝ) ≤ (⌈ε⌉₊ : ℝ) + 1 := by positivity
  have hCE : (cρ : ℝ) * ((⌈ε⌉₊ : ℝ) + 1) ≤ ((4 * c + cρ : ℕ) : ℝ) * ((⌈ε⌉₊ : ℝ) + 1) := by
    apply mul_le_mul_of_nonneg_right _ hE
    push_cast
    linarith
  refine ⟨D, hxD, hpt.trans hCE, ?_, ?_, ?_, ?_⟩
  · unfold modelScore at h1
    nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

end Kolmogorov.StrongMerging.Upper
