import KolmogorovMathlib.Foundation.ListUtil
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.BusyBeavers
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverInfra
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealCantor
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealKraft
import KolmogorovMathlib.MonotoneComplexity.Omega.AntitoneSplit
import KolmogorovMathlib.MonotoneComplexity.Omega.ModulusRandom
import KolmogorovMathlib.MonotoneComplexity.Omega.CappedScaling
import KolmogorovMathlib.MonotoneComplexity.Omega.IntervalCover
import KolmogorovMathlib.MonotoneComplexity.Omega.NeighbourhoodCover
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverSearch
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaBitsFromApprox
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.Prefix.UpperSemicomputableBound

/-!
# `Ω` and the busy beaver determine each other

The two-way translation between prefixes of `Ω` and the busy-beaver function.
`omegaPrefix_of_busyBeaver` computes `Ωₙ` from `B(n + O(log n))`, and
`busyBeaver_of_omegaPrefix` recovers `B(n)` from `Ω_{n + O(log n)}` by a partial computable
decoder, the enumeration bound `exists_const_completionTime_le_BP` and the approximation
`exists_computable_ratApprox_le_BPlain` supplying the `O(log n)` overhead. The total forms of
both statements are refuted: no total computable function can beat or reproduce the busy beaver
(`not_exists_computable_gt_BP`, `not_exists_computable_eq_BPlain`, and their versions in the
shape of the source's statement), which is why the corrected partial statements are the ones
proved.

Source: SUV §5.7.7, Theorem 116.
-/

namespace Kolmogorov
open MeasureTheory ENNReal

/-- **The approximation side of Theorem 116 reverse.** A *computable*
monotone sequence `q` of rational lower approximations of `Ω` whose accuracy at the argument
`BPlain V (M + C)` is `2^{-M}`.

This is the only place where the busy beaver enters the reverse direction, and it is the
p.-157 search of `Omega/OmegaPrefixCore.lean` read from the other side.  Take `A` to be the
stage approximation of the universal semimeasure (`hm.1.2`, exactly as in
`exists_computable_gt_BP_of_omegaPrefix`) and `q b := diagSum A b b`; `Computable q` is
`computable_diagSum_diag`, non-negativity is `diagSum_nonneg`, monotonicity in the stage is
`dyadicValue_mono_stage` through `ofReal_diagSum`, and `q b ≤ Ω` is the same computation.  For
the accuracy: `stageSearch A 0` (`Omega/BusyBeaverSearch.lean`) applied to `Ω↾(M+1)` is
`Partrec` and converges (`exists_lt_diagSum` with the sandwich `bitsValue_cantorPrefix_le` /
`le_bitsValue_cantorPrefix_add`) to a stage `s` with `diagSum A s s > Ω − 2^{-M}`; composing
that partial map with `Nat.bits` and applying `plainK_partrec_map_le` together with
`plainK_le_length` bounds `plainKNat V s` by `M + 1 + O(1)`, so `le_BPlain_of_plainKNat_le`
gives `s ≤ BPlain V (M + C)` and monotonicity of `q` finishes.  Note that no halting-time
machinery (`boundedOutputCompletionTime`, `prop_busy_beavers`) is needed: the whole argument
stays on the semimeasure side, which is why `m` and `V` may be decoupled. -/
theorem exists_computable_ratApprox_le_BPlain {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {V : Map} (hV : isOptimalConditional V) :
    ∃ (q : ℕ → ℚ) (C : ℕ), Computable q ∧ (∀ b : ℕ, 0 ≤ q b) ∧ Monotone q ∧
      (∀ b : ℕ, ((q b : ℚ) : ℝ) ≤ omegaReal m) ∧
      ∀ M : ℕ, omegaReal m < ((q (BPlain V (M + C)) : ℚ) : ℝ) + 1 / 2 ^ M := by
  classical
  -- the `ℕ`-indexed dyadic approximation of `m`, exactly as in the forward direction
  obtain ⟨approx, hstepB, hsupB, hcompB⟩ := hm.1.2
  set A : ℕ → ℕ → ℕ := fun s i => approx s (natToBitString i) [] with hAdef
  have hAstep : ∀ s i, dyadicValue (A s i) s ≤ dyadicValue (A (s + 1) i) (s + 1) :=
    fun s i => hstepB s (natToBitString i) []
  have hAsup : ∀ i, ⨆ s, dyadicValue (A s i) s = m i := by
    intro i
    have h := hsupB (natToBitString i) []
    simpa [hAdef, bitStringToNat_natToBitString] using h
  have hAle : ∀ s i, dyadicValue (A s i) s ≤ m i := by
    intro s i
    rw [← hAsup i]
    exact le_iSup (fun t => dyadicValue (A t i) t) s
  have hAcomp : Computable (fun p : ℕ × ℕ => A p.1 p.2) := by
    have h1 : Computable (fun p : ℕ × ℕ => (p.1, natToBitString p.2, ([] : BitString))) :=
      Computable.fst.pair ((computable_natToBitString.comp Computable.snd).pair
        (Computable.const []))
    exact (hcompB.comp h1).of_eq (fun p => rfl)
  have hne : omegaSum m ≠ ⊤ := omegaSum_ne_top hm
  have hoR : ENNReal.ofReal (omegaReal m) = omegaSum m := ENNReal.ofReal_toReal hne
  have hOpos : (0 : ℝ) < omegaReal m := omegaReal_pos hm
  -- the approximation and its three easy properties
  have hqmono : Monotone (fun s : ℕ => diagSum A s s) := diagSum_diag_mono hAstep
  have hqle : ∀ b : ℕ, ((diagSum A b b : ℚ) : ℝ) ≤ omegaReal m := by
    intro b
    have hE : ENNReal.ofReal ((diagSum A b b : ℚ) : ℝ) ≤ ENNReal.ofReal (omegaReal m) := by
      rw [hoR, ofReal_diagSum]
      exact le_trans (Finset.sum_le_sum fun k _ => hAle b k)
        (ENNReal.sum_le_tsum (Finset.range b))
    exact (ENNReal.ofReal_le_ofReal_iff hOpos.le).1 hE
  -- a binary expansion of `Ω`, used only to name the strings the search is run on
  obtain ⟨w, hw, -⟩ := exists_cantorReal_eq hOpos (omegaReal_le_one hm)
  -- the two constants: the length bound and the cost of the partial search
  obtain ⟨c₁, hc₁⟩ := plainK_le_length V hV
  have hpf : Partrec
      (fun y : BitString => (stageSearch A 0 y).map (fun t : ℕ => Nat.bits t)) := by
    have hg : Computable₂ (fun (_ : BitString) (t : ℕ) => Nat.bits t) :=
      natBits_computable.comp Computable.snd
    exact (partrec_stageSearch 0 hAcomp).map hg
  obtain ⟨c₂, hc₂⟩ := plainK_partrec_map_le V hV _ hpf
  refine ⟨fun b => diagSum A b b, 1 + c₁ + c₂, computable_diagSum_diag hAcomp,
    fun b => diagSum_nonneg A b b, hqmono, hqle, fun M => ?_⟩
  dsimp only
  -- the length-`M+1` prefix of the expansion of `Ω` sandwiches `Ω`
  have hxlen : (cantorPrefix w (M + 1)).length = M + 1 := cantorPrefix_length w (M + 1)
  have hOm : cantorReal w = ∑' k : ℕ, (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) := rfl
  have hlow : ((bitsValue (cantorPrefix w (M + 1)) : ℚ) : ℝ) ≤ omegaReal m := by
    rw [← hw, hOm]
    exact bitsValue_cantorPrefix_le w (M + 1)
  have hhigh : omegaReal m
      ≤ ((bitsValue (cantorPrefix w (M + 1)) : ℚ) : ℝ) + (1 : ℝ) / 2 ^ (M + 1) := by
    rw [← hw, hOm]
    exact le_bitsValue_cantorPrefix_add w (M + 1)
  have hppos : (0 : ℝ) < (1 : ℝ) / 2 ^ (cantorPrefix w (M + 1)).length := by positivity
  -- the search fires
  have hfire : ∃ s : ℕ,
      ((bitsValue (cantorPrefix w (M + 1)) : ℚ) : ℝ)
          - (1 : ℝ) / 2 ^ (cantorPrefix w (M + 1)).length
        < ((diagSum A s s : ℚ) : ℝ) := by
    refine exists_lt_diagSum hAstep hAsup ?_
    rw [show (∑' k, m k) = omegaSum m from rfl, ← hoR]
    exact (ENNReal.ofReal_lt_ofReal_iff hOpos).2 (by linarith)
  obtain ⟨s, hs⟩ := hfire
  have hsQ : bitsValue (cantorPrefix w (M + 1))
      - 1 / 2 ^ (cantorPrefix w (M + 1)).length < diagSum A s s := by
    have hcast : ((bitsValue (cantorPrefix w (M + 1))
          - 1 / 2 ^ (cantorPrefix w (M + 1)).length : ℚ) : ℝ)
        < ((diagSum A s s : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  obtain ⟨t, ht⟩ := stageSearch_dom (A := A) (K := 0) hsQ
  obtain ⟨s', hs', hts⟩ := stageSearch_spec ht
  have htEq : t = s' := by omega
  subst htEq
  -- at the firing stage the approximation is already within `2^{-M}` of `Ω`
  have hacc : omegaReal m < ((diagSum A t t : ℚ) : ℝ) + 1 / 2 ^ M := by
    have hR : ((bitsValue (cantorPrefix w (M + 1)) : ℚ) : ℝ)
        - (1 : ℝ) / 2 ^ (cantorPrefix w (M + 1)).length < ((diagSum A t t : ℚ) : ℝ) := by
      have hcast : ((bitsValue (cantorPrefix w (M + 1))
            - 1 / 2 ^ (cantorPrefix w (M + 1)).length : ℚ) : ℝ)
          < ((diagSum A t t : ℚ) : ℝ) := by exact_mod_cast hs'
      push_cast at hcast
      linarith
    rw [hxlen] at hR
    have h2 : (1 : ℝ) / 2 ^ (M + 1) + (1 : ℝ) / 2 ^ (M + 1) = (1 : ℝ) / 2 ^ M := by
      rw [pow_succ]; ring
    linarith
  -- the firing stage is small: it is the output of a partial map on a string of length `M+1`
  have hmem : Nat.bits t ∈
      (fun y : BitString => (stageSearch A 0 y).map (fun t : ℕ => Nat.bits t))
        (cantorPrefix w (M + 1)) := Part.mem_map _ ht
  have hlen2 : plainK V (cantorPrefix w (M + 1)) ≤ ((M + 1 : ℕ) : ENat) + (c₁ : ENat) := by
    have h2 := hc₁ (cantorPrefix w (M + 1))
    simpa [programLength, cantorPrefix_length] using h2
  have hK : plainKNat V t ≤ ((M + (1 + c₁ + c₂) : ℕ) : ENat) := by
    calc plainKNat V t = plainK V (Nat.bits t) := rfl
      _ ≤ plainK V (cantorPrefix w (M + 1)) + (c₂ : ENat) := hc₂ _ _ hmem
      _ ≤ ((M + 1 : ℕ) : ENat) + (c₁ : ENat) + (c₂ : ENat) := by gcongr
      _ = ((M + (1 + c₁ + c₂) : ℕ) : ENat) := by push_cast; ring
  have hle : t ≤ BPlain V (M + (1 + c₁ + c₂)) := le_BPlain_of_plainKNat_le hK
  have hstep2 : ((diagSum A t t : ℚ) : ℝ)
      ≤ ((diagSum A (BPlain V (M + (1 + c₁ + c₂))) (BPlain V (M + (1 + c₁ + c₂))) : ℚ) : ℝ) := by
    exact_mod_cast hqmono hle
  linarith

/-- `Ωₙ`, the length-`n` prefix of the binary expansion of `Ω`, is computed from
`B(n + O(log n))`: there are a computable `g` and a constant `c` with
`g n (B(n + c·log₂(n+2) + c)) = Ωₙ` for every `n`.  SUV Theorem 116 (Section 5.7, p. 171),
reverse direction. -/
theorem omegaPrefix_of_busyBeaver {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {V : Map} (hV : isOptimalConditional V)
    {w : CantorSeq} (hw : cantorReal w = omegaReal m) :
    ∃ (g : ℕ → ℕ → BitString) (c : ℕ), Computable₂ g ∧
      ∀ n, g n (BPlain V (n + c * Nat.log 2 (n + 2) + c)) = cantorPrefix w n := by
  obtain ⟨D, hD, hDspec⟩ := exists_computable_cantorPrefix_of_ratApprox
  obtain ⟨q, C, hqc, hq0, hqmono, hqle, hqacc⟩ := exists_computable_ratApprox_le_BPlain hm hV
  have hrand : IsMartinLofRandomReal (cantorReal w) := by
    rw [hw]; exact isMartinLofRandomReal_omegaReal hm
  obtain ⟨c₁, hrun⟩ := exists_const_window_true_of_isMartinLofRandomReal hrand
  refine ⟨fun n b => D n (q b), c₁ + C, hD.comp Computable.fst (hqc.comp Computable.snd), ?_⟩
  intro n
  have hstep : BPlain V (n + c₁ * Nat.log 2 (n + 2) + c₁ + C)
      ≤ BPlain V (n + (c₁ + C) * Nat.log 2 (n + 2) + (c₁ + C)) := by
    refine BPlain_mono V ?_
    have hmul : (c₁ + C) * Nat.log 2 (n + 2)
        = c₁ * Nat.log 2 (n + 2) + C * Nat.log 2 (n + 2) := Nat.add_mul _ _ _
    omega
  refine hDspec w (q (BPlain V (n + (c₁ + C) * Nat.log 2 (n + 2) + (c₁ + C)))) n
    (n + c₁ * Nat.log 2 (n + 2) + c₁) (hq0 _)
    (ne_ratCast_of_isMartinLofRandomReal hrand) (by rw [hw]; exact hqle _) ?_ (hrun n)
  have h1 := hqacc (n + c₁ * Nat.log 2 (n + 2) + c₁)
  have h2 : ((q (BPlain V (n + c₁ * Nat.log 2 (n + 2) + c₁ + C)) : ℚ) : ℝ)
      ≤ ((q (BPlain V (n + (c₁ + C) * Nat.log 2 (n + 2) + (c₁ + C))) : ℚ) : ℝ) := by
    exact_mod_cast hqmono hstep
  rw [hw]
  linarith

/-! ### Theorem 116: the refutation of the total form, and the corrected leaves -/

/-- **The total form is refutable.**  No *total* computable `f` can beat the busy-beaver
function `BP` along a family of strings whose `n`-th member has length `n` — whatever that
family is.  Since `(cantorPrefix w n).length = n`, this refutes the total reading of
`exists_computable_gt_BP_of_omegaPrefix`, which is therefore stated in its `Partrec`
form, for every `m`, `U` and `w`, and it does so without using anything about `Ω`: the
obstruction is the *totality* built into `Computable₂`. -/
theorem not_exists_computable_gt_BP {U : Map} (hU : IsOptimalPrefixConditional U)
    {x : ℕ → BitString} (hx : ∀ n, (x n).length = n) :
    ¬ ∃ f : ℕ → BitString → ℕ, Computable₂ f ∧ ∀ n : ℕ, BP U n < f n (x n) := by
  classical
  rintro ⟨f, hf, hlt⟩
  have hle_foldr : ∀ (l : List ℕ) (v : ℕ), v ∈ l → v ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro v hv; simp at hv
    | cons a l ih =>
        intro v hv
        rcases List.mem_cons.1 hv with rfl | h'
        · exact le_max_left _ _
        · exact le_trans (ih v h') (le_max_right _ _)
  set F : ℕ → ℕ := fun n => ((boundedPrograms n).map (f n)).foldr max 0 with hFdef
  have hFcomp : Computable F := by
    have hmax : Computable₂ (fun a b : ℕ => max a b) := by
      have h : Primrec₂ (fun a b : ℕ => a + (b - a)) :=
        Primrec₂.comp Primrec.nat_add Primrec.fst
          (Primrec₂.comp Primrec.nat_sub Primrec.snd Primrec.fst)
      exact (h.of_eq (fun a b => by omega)).to_comp
    have hmap : Computable (fun n : ℕ => (boundedPrograms n).map (f n)) :=
      Computable.list_map primrec_boundedPrograms.to_comp hf
    rw [hFdef]
    exact Computable.list_foldr hmap (Computable.const 0)
      ((hmax.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)).to₂)
  have hdom : ∀ n : ℕ, f n (x n) ≤ F n := by
    intro n
    rw [hFdef]
    refine hle_foldr _ _ (List.mem_map.2 ⟨x n, ?_, rfl⟩)
    exact (mem_boundedPrograms_iff (x n) n).2 (le_of_eq (hx n))
  obtain ⟨c₀, hc₀⟩ := exists_const_KPPlain_le_KPNat U hU
    (e := fun n : ℕ => natToBitString (F n)) (computable_natToBitString.comp hFcomp)
  obtain ⟨c₁, hc₁⟩ := exists_const_KPPlain_le_KPNat U hU
    (e := fun j : ℕ => natToBitString (2 ^ j))
    (computable_natToBitString.comp primrec_two_pow_aux.to_comp)
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_two_mul_length U hU
  set C : ℕ := c₂ + c₁ + c₀ with hCdef
  set j : ℕ := C + 4 with hjdef
  -- `|natToBitString j| ≤ j`
  have hlen : (natToBitString j).length ≤ j := by
    have h1 : (natToBitString j).length = (Nat.bits (j + 1)).length - 1 := by
      simp [natToBitString]
    have h2 : (Nat.bits (j + 1)).length = Nat.size (j + 1) := Nat.size_eq_bits_len _
    have h3 : Nat.size (j + 1) ≤ j + 1 := Nat.size_le.2 Nat.lt_two_pow_self
    omega
  -- `K(j) ≤ 2j + c₂`
  have hKj : KPNat U j ≤ ((2 * j + c₂ : ℕ) : ENat) := by
    refine le_trans (hc₂ (natToBitString j)) ?_
    have hcast : ((natToBitString j).length : ENat) ≤ (j : ENat) := by exact_mod_cast hlen
    calc (2 : ENat) * ((natToBitString j).length : ENat) + (c₂ : ENat)
        ≤ 2 * (j : ENat) + (c₂ : ENat) := by gcongr
      _ = ((2 * j + c₂ : ℕ) : ENat) := by push_cast; ring
  -- `K(2^j) ≤ 2j + c₂ + c₁`
  have hK2 : KPNat U (2 ^ j) ≤ ((2 * j + c₂ + c₁ : ℕ) : ENat) := by
    have h := hc₁ j
    rw [← KPNat_def] at h
    refine le_trans h ?_
    calc KPNat U j + (c₁ : ENat) ≤ ((2 * j + c₂ : ℕ) : ENat) + (c₁ : ENat) := by gcongr
      _ = ((2 * j + c₂ + c₁ : ℕ) : ENat) := by push_cast; ring
  -- `K(F (2^j)) ≤ 2j + C`
  have hKF : KPNat U (F (2 ^ j)) ≤ ((2 * j + C : ℕ) : ENat) := by
    have h := hc₀ (2 ^ j)
    rw [← KPNat_def] at h
    refine le_trans h ?_
    calc KPNat U (2 ^ j) + (c₀ : ENat)
        ≤ ((2 * j + c₂ + c₁ : ℕ) : ENat) + (c₀ : ENat) := by gcongr
      _ = ((2 * j + C : ℕ) : ENat) := by rw [hCdef]; push_cast; ring
  have hbound : F (2 ^ j) ≤ BP U (2 * j + C) := le_BP_of_KPNat_le hKF
  have hlt2 : BP U (2 ^ j) < F (2 ^ j) := lt_of_lt_of_le (hlt (2 ^ j)) (hdom (2 ^ j))
  have hsmall : 2 ^ j < 2 * j + C := by
    by_contra hle
    simp only [not_lt] at hle
    exact absurd (le_trans hbound (BP_mono U hle)) (not_le.2 hlt2)
  -- the arithmetic contradiction at `j = C + 4`
  have hCpow : C + 1 ≤ 2 ^ C := Nat.lt_two_pow_self
  have h16 : (2 : ℕ) ^ j = 16 * 2 ^ C := by rw [hjdef, pow_add]; ring
  omega

/-- **The refutation, in the shape of the source's statement.**  The total form of
`exists_computable_gt_BP_of_omegaPrefix` is false for every optimal prefix machine `U`
and every sequence `w`; in particular no hypothesis on `m` or on `hw` can rescue it. -/
theorem not_exists_computable_gt_BP_of_omegaPrefix {U : Map}
    (hU : IsOptimalPrefixConditional U) (w : CantorSeq) :
    ¬ ∃ f : ℕ → BitString → ℕ, Computable₂ f ∧ ∀ n, BP U n < f n (cantorPrefix w n) :=
  not_exists_computable_gt_BP hU (fun n => cantorPrefix_length w n)

/-- **The total form of `busyBeaver_of_omegaPrefix` is refutable.**
No *total* computable decoder can return the busy-beaver value `B(n)` on a family of
strings whose `n`-th member has length `n`, whatever that family is. -/
theorem not_exists_computable_eq_BPlain {V : Map} (hV : isOptimalConditional V)
    {x : ℕ → BitString} (hx : ∀ n, (x n).length = n) :
    ¬ ∃ (f : ℕ → BitString → ℕ) (c : ℕ), Computable₂ f ∧
        ∀ n : ℕ, f n (x (n + c * Nat.log 2 (n + 2) + c)) = BPlain V n := by
  classical
  rintro ⟨f, c, hf, heq⟩
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  have hle_foldr : ∀ (l : List ℕ) (v : ℕ), v ∈ l → v ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro v hv; simp at hv
    | cons a l ih =>
        intro v hv
        rcases List.mem_cons.1 hv with rfl | h'
        · exact le_max_left _ _
        · exact le_trans (ih v h') (le_max_right _ _)
  have hlog : ∀ n : ℕ, Nat.log 2 (n + 2) ≤ n + 1 := by
    intro n
    have h : Nat.log 2 (n + 2) < n + 2 :=
      Nat.log_lt_of_lt_pow (by omega) Nat.lt_two_pow_self
    omega
  set B : ℕ → ℕ := fun n => (c + 1) * n + 2 * c with hBdef
  have hMB : ∀ n : ℕ, n + c * Nat.log 2 (n + 2) + c ≤ B n := by
    intro n
    rw [hBdef]
    calc n + c * Nat.log 2 (n + 2) + c ≤ n + c * (n + 1) + c := by
          gcongr
          exact hlog n
      _ = (c + 1) * n + 2 * c := by ring
  set F : ℕ → ℕ := fun n => ((boundedPrograms (B n)).map (f n)).foldr max 0 + 1 with hFdef
  have hFcomp : Computable F := by
    have hBc : Computable B := by
      rw [hBdef]
      exact (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const (c + 1)) Primrec.id)
        (Primrec.const (2 * c))).to_comp
    have hmax : Computable₂ (fun a b : ℕ => max a b) := by
      have h : Primrec₂ (fun a b : ℕ => a + (b - a)) :=
        Primrec₂.comp Primrec.nat_add Primrec.fst
          (Primrec₂.comp Primrec.nat_sub Primrec.snd Primrec.fst)
      exact (h.of_eq (fun a b => by omega)).to_comp
    have hmap : Computable (fun n : ℕ => (boundedPrograms (B n)).map (f n)) :=
      Computable.list_map (primrec_boundedPrograms.to_comp.comp hBc) hf
    have hfold : Computable (fun n : ℕ => ((boundedPrograms (B n)).map (f n)).foldr max 0) :=
      Computable.list_foldr hmap (Computable.const 0)
        ((hmax.comp (Computable.fst.comp Computable.snd)
          (Computable.snd.comp Computable.snd)).to₂)
    rw [hFdef]
    exact Primrec.succ.to_comp.comp hfold
  have hdom : ∀ n : ℕ, BPlain V n < F n := by
    intro n
    rw [hFdef]
    refine Nat.lt_succ_of_le (hle_foldr _ _ (List.mem_map.2
      ⟨x (n + c * Nat.log 2 (n + 2) + c), ?_, heq n⟩))
    refine (mem_boundedPrograms_iff _ _).2 ?_
    rw [hx]
    exact hMB n
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨c₅, hc₅⟩ := plain_le_prefix V U hV hU.isPrefixDecompressor
  obtain ⟨c₃, hc₃⟩ := plainK_map_le V hV (fun y : BitString => Nat.bits (F (decodeBits y)))
    (natBits_computable.comp (hFcomp.comp decodeBits_computable))
  have hstep : ∀ n : ℕ, plainKNat V (F n) ≤ plainKNat V n + (c₃ : ENat) := by
    intro n
    have h := hc₃ (Nat.bits n)
    rw [decodeBits_natBits] at h
    exact h
  have hsize : ∀ k : ℕ,
      plainKNat V k ≤ 2 * ((Nat.bits k).length : ENat) + ((c₅ + c₂ : ℕ) : ENat) := by
    intro k
    calc plainKNat V k = plainK V (Nat.bits k) := rfl
      _ ≤ KPPlain U (Nat.bits k) + (c₅ : ENat) := hc₅ _
      _ ≤ (2 * ((Nat.bits k).length : ENat) + (c₂ : ENat)) + (c₅ : ENat) :=
          add_le_add (hc₂ _) le_rfl
      _ = 2 * ((Nat.bits k).length : ENat) + ((c₅ + c₂ : ℕ) : ENat) := by push_cast; ring
  set C : ℕ := 2 + (c₅ + c₂) + c₃ with hCdef
  set j : ℕ := C + 4 with hjdef
  have hsz : (Nat.bits (2 ^ j)).length ≤ j + 1 := by
    rw [Nat.size_eq_bits_len]
    refine Nat.size_le.2 ?_
    have hp : 0 < (2 : ℕ) ^ j := by positivity
    have hps : (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    omega
  have hKF : plainKNat V (F (2 ^ j)) ≤ ((2 * j + C : ℕ) : ENat) := by
    refine le_trans (hstep (2 ^ j)) ?_
    have hc : (((Nat.bits (2 ^ j)).length : ℕ) : ENat) ≤ ((j + 1 : ℕ) : ENat) := by
      exact_mod_cast hsz
    have h1 : plainKNat V (2 ^ j) ≤ ((2 * (j + 1) + (c₅ + c₂) : ℕ) : ENat) := by
      refine le_trans (hsize (2 ^ j)) ?_
      calc 2 * ((Nat.bits (2 ^ j)).length : ENat) + ((c₅ + c₂ : ℕ) : ENat)
          ≤ 2 * ((j + 1 : ℕ) : ENat) + ((c₅ + c₂ : ℕ) : ENat) := by gcongr
        _ = ((2 * (j + 1) + (c₅ + c₂) : ℕ) : ENat) := by push_cast; ring
    calc plainKNat V (2 ^ j) + (c₃ : ENat)
        ≤ ((2 * (j + 1) + (c₅ + c₂) : ℕ) : ENat) + (c₃ : ENat) := by gcongr
      _ = ((2 * j + C : ℕ) : ENat) := by rw [hCdef]; push_cast; ring
  have hbound : F (2 ^ j) ≤ BPlain V (2 * j + C) := le_BPlain_of_plainKNat_le hKF
  have hsmall : 2 ^ j < 2 * j + C := by
    by_contra hle
    simp only [not_lt] at hle
    exact absurd (le_trans hbound (BPlain_mono V hle)) (not_le.2 (hdom (2 ^ j)))
  have hCpow : C + 1 ≤ 2 ^ C := Nat.lt_two_pow_self
  have h16 : (2 : ℕ) ^ j = 16 * 2 ^ C := by rw [hjdef, pow_add]; ring
  omega

/-- **The refutation, in the shape of the source's statement.**  The total form of
`busyBeaver_of_omegaPrefix` is false for every optimal `V` and every `w`. -/
theorem not_exists_computable_eq_BPlain_of_omegaPrefix {V : Map}
    (hV : isOptimalConditional V) (w : CantorSeq) :
    ¬ ∃ (f : ℕ → BitString → ℕ) (c : ℕ), Computable₂ f ∧
        ∀ n, f n (cantorPrefix w (n + c * Nat.log 2 (n + 2) + c)) = BPlain V n :=
  not_exists_computable_eq_BPlain hV (fun n => cantorPrefix_length w n)

/-! ### Theorem 116: the corrected statements -/

/-- **SUV p. 171, first half of the proof of Theorem 116.**  From `Ωₙ` a *partial*
computable map produces an integer beyond the busy-beaver value `BP(n − d)`.

The source's form asks for a *total* `Computable₂ f` with
`BP U n < f n (cantorPrefix w n)`; that is refutable, see
`not_exists_computable_gt_BP_of_omegaPrefix` below, so the statement is given in its
`Partrec` form.  The alias `exists_partrec_gt_BP_of_omegaPrefix` is kept below.

Two corrections to the source's statement, both forced:

* the map is `Partrec`, not `Computable₂` — the source's construction is the unbounded
  search "enumerate `m` until the accumulated mass exceeds `Ωₙ − 2^{-n}`, then report the
  stage", which diverges off the prefixes of `Ω`, and the frozen total form is refutable;
* the conclusion carries a constant shift `n − d`, because the frozen signature decouples
  the semimeasure `m` from the machine `U`: the coding theorem only gives
  `m(k) ≥ c₂·2^{-K(k)}`, so a residual mass `< 2^{-n}` dominates the objects of prefix
  complexity `≤ n − d` for `2^{-d} ≤ c₂`, not those of complexity `≤ n`.

Both are harmless downstream: Theorem 116 states its precision as `n + O(log n)`.

*What a proof has to do.*  Take the `IsLSC` witness `A` of `m` and the diagonal stage sums
`diagSum A s s` of `Omega/OmegaPrefixCore.lean`; the search
`Nat.rfind (fun s => bitsValue x - 2^{-|x|} < diagSum A s s)` converges on `x = Ωₙ`
(`exists_lt_diagSum` together with the sandwich `bitsValue_cantorPrefix_le` /
`le_bitsValue_cantorPrefix_add`), and at the stage it returns the residual mass is
`< 2^{-n}`, so every `k` with `K(k) ≤ n - d` has already been enumerated; the halting-time
bookkeeping of `problem_165_BP_le_maxHaltTime_le_BP` then converts the stage into an
integer above `BP U (n - d)`. -/
theorem exists_computable_gt_BP_of_omegaPrefix {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {U : Map} (hU : IsOptimalPrefixConditional U)
    {w : CantorSeq} (hw : cantorReal w = omegaReal m) :
    ∃ (f : BitString →. ℕ) (d : ℕ), Partrec f ∧
      ∀ n : ℕ, ∃ t, t ∈ f (cantorPrefix w n) ∧ BP U (n - d) < t := by
  classical
  -- the `ℕ`-indexed dyadic approximation of `m`, exactly as in the proof of Theorem 100
  obtain ⟨approx, hstepB, hsupB, hcompB⟩ := hm.1.2
  set A : ℕ → ℕ → ℕ := fun s i => approx s (natToBitString i) [] with hAdef
  have hAstep : ∀ s i, dyadicValue (A s i) s ≤ dyadicValue (A (s + 1) i) (s + 1) :=
    fun s i => hstepB s (natToBitString i) []
  have hAsup : ∀ i, ⨆ s, dyadicValue (A s i) s = m i := by
    intro i
    have h := hsupB (natToBitString i) []
    simpa [hAdef, bitStringToNat_natToBitString] using h
  have hAle : ∀ s i, dyadicValue (A s i) s ≤ m i := by
    intro s i
    rw [← hAsup i]
    exact le_iSup (fun t => dyadicValue (A t i) t) s
  have hAcomp : Computable (fun p : ℕ × ℕ => A p.1 p.2) := by
    have h1 : Computable (fun p : ℕ × ℕ => (p.1, natToBitString p.2, ([] : BitString))) :=
      Computable.fst.pair ((computable_natToBitString.comp Computable.snd).pair
        (Computable.const []))
    have h2 := hcompB.comp h1
    exact h2.of_eq (fun p => rfl)
  have hne : omegaSum m ≠ ⊤ := omegaSum_ne_top hm
  have hoR : ENNReal.ofReal (omegaReal m) = omegaSum m := ENNReal.ofReal_toReal hne
  obtain ⟨_cc1, cc2, _hcc1, hcc2, _hfwd, hbwd⟩ := exists_const_KPNat_aprioriNat_equiv hm hU
  obtain ⟨c₀, hc₀⟩ := exists_const_le_of_weight hcc2
  refine ⟨stageSearch A 1, c₀ + 1, partrec_stageSearch _ hAcomp, fun n => ?_⟩
  -- the sandwich `bitsValue x ≤ Ω ≤ bitsValue x + 2^{-n}` for `x = Ω↾n`
  have hxlen : (cantorPrefix w n).length = n := cantorPrefix_length w n
  have hΩ : cantorReal w = ∑' k : ℕ, (if w k then (1 : ℝ) / 2 ^ (k + 1) else 0) := rfl
  have hlow : ((bitsValue (cantorPrefix w n) : ℚ) : ℝ) ≤ omegaReal m := by
    rw [← hw, hΩ]
    exact bitsValue_cantorPrefix_le w n
  have hhigh : omegaReal m
      ≤ ((bitsValue (cantorPrefix w n) : ℚ) : ℝ)
        + (1 : ℝ) / 2 ^ (cantorPrefix w n).length := by
    rw [← hw, hΩ, hxlen]
    exact le_bitsValue_cantorPrefix_add w n
  have hhighE : (∑' k, m k)
      ≤ ENNReal.ofReal (((bitsValue (cantorPrefix w n) : ℚ) : ℝ)
        + (1 : ℝ) / 2 ^ (cantorPrefix w n).length) := by
    rw [show (∑' k, m k) = omegaSum m from rfl, ← hoR]
    exact ENNReal.ofReal_le_ofReal hhigh
  -- the search terminates on this prefix
  have hppos : (0 : ℝ) < (1 : ℝ) / 2 ^ (cantorPrefix w n).length := by positivity
  have hfire : ∃ s : ℕ,
      ((bitsValue (cantorPrefix w n) : ℚ) : ℝ) - (1 : ℝ) / 2 ^ (cantorPrefix w n).length
        < ((diagSum A s s : ℚ) : ℝ) := by
    refine exists_lt_diagSum hAstep hAsup ?_
    rw [show (∑' k, m k) = omegaSum m from rfl, ← hoR]
    exact (ENNReal.ofReal_lt_ofReal_iff (omegaReal_pos hm)).2 (by linarith)
  obtain ⟨s, hs⟩ := hfire
  have hsQ : bitsValue (cantorPrefix w n) - 1 / 2 ^ (cantorPrefix w n).length
      < diagSum A s s := by
    have hcast : ((bitsValue (cantorPrefix w n)
          - 1 / 2 ^ (cantorPrefix w n).length : ℚ) : ℝ)
        < ((diagSum A s s : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  obtain ⟨t, ht⟩ := stageSearch_dom (A := A) (K := 1) hsQ
  refine ⟨t, ht, ?_⟩
  obtain ⟨s', hs', rfl⟩ := stageSearch_spec ht
  -- every index the firing stage has not yet inspected is still unaccounted for, so its
  -- mass is below `2·2^{-n}` and its prefix complexity is therefore at least `n − c₀`
  have hbig : ∀ i : ℕ, s' ≤ i → (n : ENat) ≤ KPNat U i + (c₀ : ENat) := by
    intro i hi
    have hkey := diagSum_add_mass_le_of_stage_le hAle hi
    have hmi := mass_le_two_pow_of_diagSum hkey hhighE hs'
    have hmi' : m i ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [← ofReal_two_mul_inv_pow n, ← hxlen]
      exact hmi
    exact hc₀ (KPNat U i) n (le_trans (hbwd i) hmi')
  rcases Nat.lt_or_ge n (c₀ + 1) with hn | hn
  · -- below the additive constant the claim is the trivial `BP U 0 = 0 < t`
    rw [show n - (c₀ + 1) = 0 by omega, BP_zero hU]
    omega
  · -- above it, no integer of prefix complexity `≤ n − (c₀+1)` can have escaped the search
    have hle : BP U (n - (c₀ + 1)) ≤ s' := by
      refine BP_le_of_forall fun k hk => ?_
      by_contra hgt
      simp only [not_le] at hgt
      have hn' : (n : ENat) ≤ ((n - (c₀ + 1) + c₀ : ℕ) : ENat) := by
        refine le_trans (hbig k hgt.le) ?_
        rw [Nat.cast_add]
        exact add_le_add hk le_rfl
      have hn'' : n ≤ n - (c₀ + 1) + c₀ := by exact_mod_cast hn'
      omega
    omega

/-- Alternative name for `exists_computable_gt_BP_of_omegaPrefix`, which is stated in
its `Partrec` form. -/
alias exists_partrec_gt_BP_of_omegaPrefix := exists_computable_gt_BP_of_omegaPrefix

/-! #### Reading `B(n)` off a completed enumeration stage

`AlgorithmicStatistics/BoundedLists/` already enumerates, for each length bound
`m` and each time budget `t`, the outputs of the programs of length `≤ m` that have halted
(`boundedOutputStage`), and knows that beyond the *completion time*
`boundedOutputCompletionTime` the list no longer changes
(`boundedOutputStage_eq_completed_of_completion_le`), at which point it consists exactly of
the strings of plain complexity `≤ m` (`mem_completedBoundedOutput_iff_plainK_le`).  Since
`plainKNat V k = plainK V (Nat.bits k)`, the busy-beaver value `BPlain V m` is the largest
`k` whose canonical bit code occurs in that list — which the following primitive recursive
read-off computes from any `t` past the completion time. -/

/-- The natural number a string codes, when the string is the canonical `Nat.bits` code of
a natural, and `0` otherwise. -/
def bbCode (v : BitString) : ℕ := if Nat.bits (bitsToNat v) = v then bitsToNat v else 0

/-- Reading a string as the natural number it canonically codes is computable. -/
theorem computable_bbCode : Computable bbCode := by
  have hnum : Computable (fun v : BitString => bitsToNat v) := bitsToNat_primrec.to_comp
  have heqb : Computable₂ (fun x y : BitString => decide (x = y)) :=
    (PrimrecRel.decide (Primrec.eq (α := BitString))).to_comp
  have htest : Computable (fun v : BitString => decide (Nat.bits (bitsToNat v) = v)) :=
    Computable₂.comp heqb (natBits_computable.comp hnum) Computable.id
  refine (Computable.cond htest hnum (Computable.const 0)).of_eq (fun v => ?_)
  by_cases h : Nat.bits (bitsToNat v) = v <;> simp [bbCode, h]

/-- The largest natural number whose canonical bit code occurs among the outputs
enumerated by stage `t` of the programs of length `≤ m`; `0` if there is none. -/
def bbFromStage (c : Nat.Partrec.Code) (m t : ℕ) : ℕ :=
  ((boundedOutputStage c m t).map bbCode).foldr max 0

/-- A common bound on the entries of a list bounds the maximum of the list. -/
theorem foldr_max_le_nat {b : ℕ} : ∀ l : List ℕ, (∀ x ∈ l, x ≤ b) → l.foldr max 0 ≤ b :=
  fun _ h => foldr_max_le_of_forall_le h

/-- Every entry of a list of naturals is at most the maximum of the list. -/
theorem le_foldr_max_nat_mem {a : ℕ} : ∀ l : List ℕ, a ∈ l → a ≤ l.foldr max 0 :=
  fun _ h => le_foldr_max_of_mem h

/-- The largest output enumerated by a given stage from programs of bounded length is computable
in the length bound and the stage. -/
theorem computable_bbFromStage (c : Nat.Partrec.Code) :
    Computable (fun p : ℕ × ℕ => bbFromStage c p.1 p.2) := by
  have hmap : Computable (fun p : ℕ × ℕ => (boundedOutputStage c p.1 p.2).map bbCode) :=
    Computable.list_map (boundedOutputStage_computable c)
      (computable_bbCode.comp Computable.snd).to₂
  have hmax : Computable₂ (fun a b : ℕ => max a b) := by
    have h : Primrec₂ (fun a b : ℕ => a + (b - a)) :=
      Primrec₂.comp Primrec.nat_add Primrec.fst
        (Primrec₂.comp Primrec.nat_sub Primrec.snd Primrec.fst)
    exact (h.of_eq (fun a b => by omega)).to_comp
  exact Computable.list_foldr hmap (Computable.const 0)
    ((hmax.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)).to₂)

/-- **Past the completion time the read-off is exact.**  For `t` beyond
`boundedOutputCompletionTime c m` the enumerated stage is the complete list of outputs of
plain complexity `≤ m`, so `bbFromStage c m t` is the busy-beaver value `BPlain V m`. -/
theorem bbFromStage_eq_BPlain {V : Map} {c : Nat.Partrec.Code} (hc : IsCodeFor c V) {m t : ℕ}
    (ht : boundedOutputCompletionTime c m ≤ t) : bbFromStage c m t = BPlain V m := by
  have hstage : boundedOutputStage c m t = completedBoundedOutput c m :=
    boundedOutputStage_eq_completed_of_completion_le c m t ht
  refine le_antisymm ?_ ?_
  · rw [bbFromStage, hstage]
    refine foldr_max_le_nat _ (fun x hx => ?_)
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    by_cases hcanon : Nat.bits (bitsToNat v) = v
    · simp only [bbCode, if_pos hcanon]
      have hmem : bitsToNat v ∈ boundedNatOutputs c m := by
        rw [mem_boundedNatOutputs_iff_mem_completed, hcanon]
        exact hv
      exact le_BPlain_of_plainKNat_le ((mem_boundedNatOutputs_iff_plainKNat_le hc m _).1 hmem)
    · simp only [bbCode, if_neg hcanon]
      exact Nat.zero_le _
  · rcases Set.eq_empty_or_nonempty (plainKNatSublevel V m) with hE | hN
    · have hzero : BPlain V m = 0 := by rw [BPlain, hE]; simp
      rw [hzero]
      exact Nat.zero_le _
    · have hmem := (BPlain_mem_and_le hN).1
      have hbits : Nat.bits (BPlain V m) ∈ completedBoundedOutput c m := by
        rw [← mem_boundedNatOutputs_iff_mem_completed]
        exact (mem_boundedNatOutputs_iff_plainKNat_le hc m _).2 hmem
      have hb : bbCode (Nat.bits (BPlain V m)) = BPlain V m := by
        simp only [bbCode, bitsToNat_bits, if_pos]
      rw [bbFromStage, hstage]
      exact le_foldr_max_nat_mem _ (List.mem_map.2 ⟨Nat.bits (BPlain V m), hbits, hb⟩)

/-- `log₂` absorbs an additive constant into an additive constant. -/
theorem log_two_add_const_le (m C : ℕ) :
    Nat.log 2 (m + C + 2) ≤ Nat.log 2 (m + 2) + C := by
  set L := Nat.log 2 (m + 2) with hL
  have h1 : m + 2 < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : C + 1 ≤ 2 ^ C := Nat.lt_two_pow_self
  have h3 : m + 3 ≤ 2 ^ (L + 1) := by omega
  have h4 : (m + 3) * (C + 1) ≤ 2 ^ (L + 1) * 2 ^ C := Nat.mul_le_mul h3 h2
  have h5 : 2 ^ (L + 1) * 2 ^ C = 2 ^ (L + C + 1) := by
    rw [← pow_add]
    ring_nf
  have h6 : m + 3 * C + 3 ≤ (m + 3) * (C + 1) := by
    calc m + 3 * C + 3 ≤ m * C + (m + 3 * C + 3) := Nat.le_add_left _ _
      _ = (m + 3) * (C + 1) := by ring
  have h7 : m + C + 2 < 2 ^ (L + C + 1) := by
    have hchain : m + 3 * C + 3 ≤ 2 ^ (L + C + 1) := by
      rw [← h5]
      exact le_trans h6 h4
    omega
  have h8 := Nat.log_lt_of_lt_pow (by omega : m + C + 2 ≠ 0) h7
  omega

/-- **The `O(log n)` bound on the enumeration completion time.**  `B'(m)`, the stage at
which the enumeration of the outputs of plain complexity `≤ m` stabilises, has plain
complexity `≤ m + O(1)` (`plainKNat_completionTime_le`), hence is dominated by the plain
busy beaver at `m + O(1)`, hence by the *prefix* busy beaver at `m + O(log m)`
(`exists_const_BPlain_le_BP`).  This is the only place where the `O(log n)` of Theorem 116
is produced. -/
theorem exists_const_completionTime_le_BP {V : Map} (hV : isOptimalConditional V)
    {U : Map} (hU : IsOptimalPrefixConditional U) (c : Nat.Partrec.Code) :
    ∃ k : ℕ, ∀ m : ℕ,
      boundedOutputCompletionTime c m ≤ BP U (m + k * Nat.log 2 (m + 2) + k) := by
  obtain ⟨C, hC⟩ := plainKNat_completionTime_le V hV c
  obtain ⟨c', hc'⟩ := exists_const_BPlain_le_BP hU hV
  refine ⟨c' + C + c' * C + c', fun m => ?_⟩
  refine le_trans (le_BPlain_of_plainKNat_le (hC m))
    (le_trans (hc' (m + C)) (BP_mono U ?_))
  have hlog : c' * Nat.log 2 (m + C + 2) ≤ c' * (Nat.log 2 (m + 2) + C) :=
    Nat.mul_le_mul_left _ (log_two_add_const_le m C)
  have hmul : c' * Nat.log 2 (m + 2)
      ≤ (c' + C + c' * C + c') * Nat.log 2 (m + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have hexp : c' * (Nat.log 2 (m + 2) + C) = c' * Nat.log 2 (m + 2) + c' * C := by ring
  omega

/-- `B(n)` is produced from `Ω_{n+O(log n)}` by a *partial* computable decoder: there are a
partial computable `f` and a constant `c` with `B(n) ∈ f n (Ω_{n + c·log₂(n+2) + c})` for
every `n`.  The decoder is partial by necessity — no *total* computable `f` with
`f n (Ω_{n + c·log₂(n+2) + c}) = B(n)` exists, see
`not_exists_computable_eq_BPlain_of_omegaPrefix` below.  SUV Theorem 116 (Section 5.7,
p. 171), forward direction. -/
theorem busyBeaver_of_omegaPrefix {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {V : Map} (hV : isOptimalConditional V)
    {w : CantorSeq} (hw : cantorReal w = omegaReal m) :
    ∃ (f : ℕ → BitString →. ℕ) (c : ℕ), Partrec₂ f ∧
      ∀ n : ℕ,
        BPlain V n ∈ f n (cantorPrefix w (n + c * Nat.log 2 (n + 2) + c)) := by
  classical
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cd, hcd⟩ : ∃ cd : Nat.Partrec.Code, IsCodeFor cd V :=
    Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨g, d, hgp, hg⟩ := exists_computable_gt_BP_of_omegaPrefix hm hU hw
  obtain ⟨k, hk⟩ := exists_const_completionTime_le_BP hV hU cd
  refine ⟨fun n x => (g x).map (fun t => bbFromStage cd n t), d + k, ?_, fun n => ?_⟩
  · have hpart : Partrec (fun p : ℕ × BitString => g p.2) := hgp.comp Computable.snd
    have hcomp : Computable₂ (fun (p : ℕ × BitString) (t : ℕ) => bbFromStage cd p.1 t) :=
      ((computable_bbFromStage cd).comp
        ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
    exact hpart.map hcomp
  · obtain ⟨t, ht, htlt⟩ := hg (n + (d + k) * Nat.log 2 (n + 2) + (d + k))
    have harg : n + k * Nat.log 2 (n + 2) + k
        ≤ (n + (d + k) * Nat.log 2 (n + 2) + (d + k)) - d := by
      have h1 : k * Nat.log 2 (n + 2) ≤ (d + k) * Nat.log 2 (n + 2) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hcompl : boundedOutputCompletionTime cd n ≤ t :=
      le_of_lt (lt_of_le_of_lt (le_trans (hk n) (BP_mono U harg)) htlt)
    have hval : bbFromStage cd n t = BPlain V n := bbFromStage_eq_BPlain hcd hcompl
    rw [← hval]
    exact Part.mem_map _ ht

/-- Alternative name for `busyBeaver_of_omegaPrefix`, which is stated in its `Partrec`
form. -/
alias theorem_116_busyBeaver_of_omegaPrefix_partrec := busyBeaver_of_omegaPrefix

end Kolmogorov
