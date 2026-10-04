/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.GapCover
import KolmogorovMathlib.MonotoneComplexity.Omega.CappedScaling
import KolmogorovMathlib.MonotoneComplexity.Omega.GridCells
import KolmogorovMathlib.MonotoneComplexity.Omega.IntervalCover
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaComplete

/-!
# The a priori neighbourhood estimate of SUV p. 170

SUV p. 170, inside the proof of Theorem 115: *for a random `α` the total a priori
probability of the rationals in the `2^{-k}`-neighbourhood of `α` is `O(2^{-k})`.*

The source's argument is a **Martin-Löf test**, one level for each constant `c = 2^{j+2}`:

> the union of the intervals `I` with `ν(I) > (c/2)·|I|` has Lebesgue measure at most
> `4/c` (a finite non-redundant subfamily has multiplicity two, and each of the two
> disjoint halves is controlled by `∑_q m(q) ≤ 1`); a real that fails the estimate at
> every level lies in every one of these open sets, hence in an effectively null set.

The measure core is `mul_volume_biUnion_le` (`Omega/IntervalCover.lean`).
This module carries out the **assembly**: it turns that estimate plus three clean
ingredients into `exists_const_apriori_ratCode_neighbourhood_le`, which
`Omega/SolovayFunctions.lean` re-exports as the frozen leaf
`exists_const_apriori_neighbourhood_le`.

## The three ingredients (two of them proved)

* `exists_computable_heavyInterval_enum` — **proved**: the `Σ₁` enumeration of the "heavy"
  rational intervals at level `j`.  Heaviness, `2^{j+2}·|I| < 2·ν(I)`, is a `Σ₁` condition
  because `ν(I) = ∑_{q ∈ I} m(ratCode q)` is a supremum of finite sums of stage
  approximations of the lower semicomputable `m` (the `IsLSC` witness is turned into
  rationals by `lscRatApprox` of `Omega/CappedScaling.lean`), and `q ∈ ratInterval I` is
  decidable.  The enumeration is `heavyEnum`: the `i`-th entry inspects the interval coded
  by `i.unpair.1`, at stage `i`, summing over the first `i` rational codes; `heavyFlag`
  keeps only the valid codes of rationals inside the interval, which is what makes the
  partial sums both a lower bound (`ofReal_heavyMass_le`) and a supremum
  (`le_iSup_ofReal_heavyMass`) for the true mass.
* `isEffectivelyNullReal_iInter_iUnion_of_volume_le` — **the one remaining leaf**: the
  bridge from a *uniformly
  effectively open* family whose **unions** have small Lebesgue measure to
  `IsEffectivelyNullReal`, whose frozen definition instead bounds the **sum of the
  lengths** of the enumerated intervals.  The two differ, and the enumeration cannot be
  pruned on the fly (an interval emitted early may only later become redundant).  The
  conversion re-covers the open set by *pairwise disjoint* dyadic cells — good at the
  first stage at which they sit inside an enumerated interval and are still disjoint from
  all the earlier ones — for which the sum of the lengths **is** the measure of the union;
  see that leaf's docstring for the full recipe.  Pulling back to Cantor space is not
  needed.
* `exists_ratInterval_lt_tsum` — **proved**: shrinking the ball `B(x, ε)`, whose endpoints are
  irrational for a random centre, to a *rational* interval that still contains `x` and
  still carries more than the given mass.  Monotone convergence on the countable index
  set `ℚ` supplies a finite witnessing set, and density of `ℚ` supplies endpoints that
  separate that finite set from the ends of the ball.

Everything else on p. 170 is proved here.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ### The enumeration machinery for the heavy intervals -/

/-- The `c`-th rational interval, through the repository's computable coding `ratOfCode` of
the rationals.  Every rational interval occurs (`ratIntervalOfCode_apply`). -/
def ratIntervalOfCode (c : ℕ) : ℚ × ℚ := (ratOfCode c.unpair.1, ratOfCode c.unpair.2)

/-- Decoding a natural number as a rational interval is computable. -/
theorem computable_ratIntervalOfCode : Computable ratIntervalOfCode :=
  Computable.pair (computable_ratOfCode.comp (Primrec.fst.comp Primrec.unpair).to_comp)
    (computable_ratOfCode.comp (Primrec.snd.comp Primrec.unpair).to_comp)

/-- Decoding the code of an interval returns that interval. -/
@[simp] theorem ratIntervalOfCode_apply (J : ℚ × ℚ) :
    ratIntervalOfCode (Nat.pair (ratCode J.1) (ratCode J.2)) = J := by
  simp [ratIntervalOfCode, Nat.unpair_pair, ratOfCode_ratCode]

/-- The test "the natural `t` is a valid code of a rational lying inside the interval coded by
`u.unpair.1`".  Both conjuncts are decidable comparisons of computable rationals, so the test
is computable; `ratCode (ratOfCode t) = t` is the repository's `IsRatCode t`. -/
def heavyFlag (u t : ℕ) : Bool :=
  decide (ratCode (ratOfCode t) = t) &&
    (decide ((ratIntervalOfCode u.unpair.1).1 < ratOfCode t) &&
      decide (ratOfCode t < (ratIntervalOfCode u.unpair.1).2))

/-- The test that a code is that of a rational inside the given interval is computable. -/
theorem computable₂_heavyFlag : Computable₂ heavyFlag := by
  have ht : Computable (fun p : ℕ × ℕ => ratOfCode p.2) :=
    computable_ratOfCode.comp Computable.snd
  have hJ : Computable (fun p : ℕ × ℕ => ratIntervalOfCode p.1.unpair.1) :=
    computable_ratIntervalOfCode.comp ((Primrec.fst.comp Primrec.unpair).to_comp.comp
      Computable.fst)
  have hcode : Computable (fun p : ℕ × ℕ => decide (ratCode (ratOfCode p.2) = p.2)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp (computable_ratCode.comp ht) Computable.snd
  have hlo : Computable (fun p : ℕ × ℕ =>
      decide ((ratIntervalOfCode p.1.unpair.1).1 < ratOfCode p.2)) :=
    computable₂_ratLt.comp (Computable.fst.comp hJ) ht
  have hhi : Computable (fun p : ℕ × ℕ =>
      decide (ratOfCode p.2 < (ratIntervalOfCode p.1.unpair.1).2)) :=
    computable₂_ratLt.comp ht (Computable.snd.comp hJ)
  have hand : Computable₂ (fun a b : Bool => a && b) := (Primrec.dom_bool₂ _).to_comp
  exact hand.comp hcode (hand.comp hlo hhi)

/-- The stage-`u` contribution of the rational coded by `t` to the a priori mass of the
interval coded by `u.unpair.1`, taken through a computable family of rational lower
approximations `a` of the semimeasure. -/
noncomputable def heavyTerm (a : ℕ → ℕ → ℚ) (u t : ℕ) : ℚ :=
  cond (heavyFlag u t) (a u t) 0

/-- The stagewise contributions to the a priori mass of an interval are computable. -/
theorem computable₂_heavyTerm {a : ℕ → ℕ → ℚ} (ha : Computable₂ a) :
    Computable₂ (heavyTerm a) :=
  Computable.cond computable₂_heavyFlag ha (Computable.const 0)

/-- The stage-`u` approximation of the a priori mass of the rationals inside the interval
coded by `u.unpair.1`: the first `u` codes are inspected, at approximation stage `u`. -/
noncomputable def heavyMass (a : ℕ → ℕ → ℚ) (u : ℕ) : ℚ :=
  ratStageSum (heavyTerm a) u u

/-- The stage approximation of the a priori mass of an interval is computable. -/
theorem computable_heavyMass {a : ℕ → ℕ → ℚ} (ha : Computable₂ a) :
    Computable (heavyMass a) :=
  computable_ratStageSum_diag (computable₂_heavyTerm ha)

/-- The stage-`u` mass of an interval is the sum of its stagewise contributions. -/
theorem heavyMass_eq (a : ℕ → ℕ → ℚ) (u : ℕ) :
    heavyMass a u = ∑ t ∈ Finset.range u, heavyTerm a u t :=
  ratStageSum_eq _ _ _

/-- The enumeration of the heavy intervals of level `j`: the `i`-th entry inspects the
interval coded by `i.unpair.1` at stage `i`, and emits it as soon as the stage-`i`
approximation of its mass already witnesses heaviness. -/
noncomputable def heavyEnum (a : ℕ → ℕ → ℚ) (j i : ℕ) : Option (ℚ × ℚ) :=
  cond (decide ((2 : ℚ) ^ (j + 2) *
      ((ratIntervalOfCode i.unpair.1).2 - (ratIntervalOfCode i.unpair.1).1)
        < 2 * heavyMass a i))
    (some (ratIntervalOfCode i.unpair.1)) none

/-- The enumeration of heavy intervals is computable in the level and the index. -/
theorem computable₂_heavyEnum {a : ℕ → ℕ → ℚ} (ha : Computable₂ a) :
    Computable₂ (heavyEnum a) := by
  have hJ : Computable (fun p : ℕ × ℕ => ratIntervalOfCode p.2.unpair.1) :=
    computable_ratIntervalOfCode.comp ((Primrec.fst.comp Primrec.unpair).to_comp.comp
      Computable.snd)
  have hlen : Computable (fun p : ℕ × ℕ =>
      (ratIntervalOfCode p.2.unpair.1).2 - (ratIntervalOfCode p.2.unpair.1).1) :=
    computable₂_ratSub.comp (Computable.snd.comp hJ) (Computable.fst.comp hJ)
  have hpow : Computable (fun p : ℕ × ℕ => (2 : ℚ) ^ (p.1 + 2)) :=
    computable_two_pow_rat.comp
      (Primrec.nat_add.to_comp.comp Computable.fst (Computable.const 2))
  have hlhs : Computable (fun p : ℕ × ℕ => (2 : ℚ) ^ (p.1 + 2) *
      ((ratIntervalOfCode p.2.unpair.1).2 - (ratIntervalOfCode p.2.unpair.1).1)) :=
    computable₂_ratMul.comp hpow hlen
  have hrhs : Computable (fun p : ℕ × ℕ => 2 * heavyMass a p.2) :=
    computable₂_ratMul.comp (Computable.const 2) ((computable_heavyMass ha).comp Computable.snd)
  exact Computable.cond (computable₂_ratLt.comp hlhs hrhs)
    (Computable.option_some.comp hJ) (Computable.const none)

/-- The stage approximation as a sum in `ℝ≥0∞`. -/
theorem ofReal_heavyMass_eq {a : ℕ → ℕ → ℚ} (ha0 : ∀ s t, 0 ≤ a s t) (u : ℕ) :
    ENNReal.ofReal ((heavyMass a u : ℚ) : ℝ)
      = ∑ t ∈ Finset.range u, ENNReal.ofReal ((heavyTerm a u t : ℚ) : ℝ) := by
  have hcast : ((heavyMass a u : ℚ) : ℝ)
      = ∑ t ∈ Finset.range u, ((heavyTerm a u t : ℚ) : ℝ) := by
    rw [heavyMass_eq]; push_cast; ring
  rw [hcast]
  refine ENNReal.ofReal_sum_of_nonneg fun t _ => ?_
  have h : (0 : ℚ) ≤ heavyTerm a u t := by
    cases hf : heavyFlag u t <;> simp [heavyTerm, hf, ha0]
  exact_mod_cast h

open scoped Classical in
/-- **Soundness of the stage approximation.**  The stage-`u` approximation of the mass of the
interval coded by `u.unpair.1` never exceeds the true a priori mass of that interval: the
`heavyFlag` picks out the *valid* codes of *distinct* rationals inside the interval, and each
term is a lower approximation of the semimeasure at that code. -/
theorem ofReal_heavyMass_le {m : ℕ → ℝ≥0∞} {a : ℕ → ℕ → ℚ}
    (ha0 : ∀ s t, 0 ≤ a s t) (hale : ∀ s t, ENNReal.ofReal ((a s t : ℚ) : ℝ) ≤ m t) (u : ℕ) :
    ENNReal.ofReal ((heavyMass a u : ℚ) : ℝ)
      ≤ ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval (ratIntervalOfCode u.unpair.1)
          then m (ratCode q) else 0) := by
  classical
  set S : Finset ℕ := (Finset.range u).filter (fun t => heavyFlag u t = true) with hSdef
  have hsum : ENNReal.ofReal ((heavyMass a u : ℚ) : ℝ)
      = ∑ t ∈ S, ENNReal.ofReal ((a u t : ℚ) : ℝ) := by
    rw [ofReal_heavyMass_eq ha0, hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    cases h : heavyFlag u t <;> simp [heavyTerm, h]
  have hcode : ∀ t ∈ S, ratCode (ratOfCode t) = t := by
    intro t ht
    have h := (Finset.mem_filter.1 ht).2
    simp only [heavyFlag, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hin : ∀ t ∈ S, ((ratOfCode t : ℚ) : ℝ) ∈ ratInterval (ratIntervalOfCode u.unpair.1) := by
    intro t ht
    have h := (Finset.mem_filter.1 ht).2
    simp only [heavyFlag, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Set.mem_Ioo.2 ⟨by exact_mod_cast h.2.1, by exact_mod_cast h.2.2⟩
  have hinj : Set.InjOn ratOfCode (S : Set ℕ) := by
    intro t ht t' ht' h
    rw [← hcode t (Finset.mem_coe.1 ht), ← hcode t' (Finset.mem_coe.1 ht'), h]
  rw [hsum]
  calc ∑ t ∈ S, ENNReal.ofReal ((a u t : ℚ) : ℝ)
      ≤ ∑ t ∈ S, m t := Finset.sum_le_sum fun t _ => hale u t
    _ = ∑ q ∈ S.image ratOfCode, m (ratCode q) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl fun t ht => by rw [hcode t ht]
    _ = ∑ q ∈ S.image ratOfCode,
          (if ((q : ℚ) : ℝ) ∈ ratInterval (ratIntervalOfCode u.unpair.1)
            then m (ratCode q) else 0) := by
        refine (Finset.sum_congr rfl fun q hq => ?_).symm
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
        rw [ite_eq_left (hin t ht)]
    _ ≤ _ := ENNReal.sum_le_tsum _

open scoped Classical in
/-- **Completeness of the stage approximation.**  Along the codes `Nat.pair c r`, `r : ℕ`, the
stage approximations of the mass of the interval coded by `c` converge to the true a priori
mass of that interval: every finite set of rationals inside the interval is inspected from
some stage on, and at that stage the approximations are already arbitrarily close. -/
theorem le_iSup_ofReal_heavyMass {m : ℕ → ℝ≥0∞} {a : ℕ → ℕ → ℚ}
    (ha0 : ∀ s t, 0 ≤ a s t) (hamono : ∀ s t, a s t ≤ a (s + 1) t)
    (hasup : ∀ t, ⨆ s, ENNReal.ofReal ((a s t : ℚ) : ℝ) = m t) (c : ℕ) :
    (∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval (ratIntervalOfCode c) then m (ratCode q) else 0))
      ≤ ⨆ r : ℕ, ENNReal.ofReal ((heavyMass a (Nat.pair c r) : ℚ) : ℝ) := by
  classical
  have hstage : ∀ t : ℕ, Monotone fun s => ENNReal.ofReal ((a s t : ℚ) : ℝ) := by
    intro t
    refine monotone_nat_of_le_succ fun s => ?_
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hamono s t)
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun T => ?_
  set T' : Finset ℚ :=
    T.filter (fun q => ((q : ℚ) : ℝ) ∈ ratInterval (ratIntervalOfCode c)) with hT'def
  have hTT' : ∑ q ∈ T,
      (if ((q : ℚ) : ℝ) ∈ ratInterval (ratIntervalOfCode c) then m (ratCode q) else 0)
        = ∑ q ∈ T', m (ratCode q) := by
    rw [hT'def, Finset.sum_filter]
  rw [hTT']
  have hfin : ∑ q ∈ T', m (ratCode q)
      = ⨆ s : ℕ, ∑ q ∈ T', ENNReal.ofReal ((a s (ratCode q) : ℚ) : ℝ) := by
    rw [← ENNReal.finsetSum_iSup_of_monotone (fun q => hstage (ratCode q))]
    exact Finset.sum_congr rfl fun q _ => (hasup (ratCode q)).symm
  rw [hfin]
  refine iSup_le fun s => ?_
  set N : ℕ := (T'.image ratCode).sup id + 1 with hNdef
  set r : ℕ := max s N with hrdef
  have hri : r ≤ Nat.pair c r := Nat.right_le_pair c r
  have hsr : s ≤ Nat.pair c r := le_trans (le_max_left s N) hri
  have hcodes : ∀ q ∈ T', ratCode q < Nat.pair c r := by
    intro q hq
    have h1 : ratCode q ≤ (T'.image ratCode).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hq)
    have h2 : N ≤ Nat.pair c r := le_trans (le_max_right s N) hri
    omega
  have hflag : ∀ q ∈ T', heavyFlag (Nat.pair c r) (ratCode q) = true := by
    intro q hq
    have hqJ : ((q : ℚ) : ℝ) ∈ ratInterval (ratIntervalOfCode c) :=
      (Finset.mem_filter.1 hq).2
    obtain ⟨hlo, hhi⟩ := Set.mem_Ioo.1 hqJ
    simp only [heavyFlag, Nat.unpair_pair, ratOfCode_ratCode, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨trivial, by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hinjc : Set.InjOn ratCode (T' : Set ℚ) := fun q _ q' _ h => ratCode_injective h
  calc ∑ q ∈ T', ENNReal.ofReal ((a s (ratCode q) : ℚ) : ℝ)
      ≤ ∑ q ∈ T', ENNReal.ofReal ((a (Nat.pair c r) (ratCode q) : ℚ) : ℝ) :=
        Finset.sum_le_sum fun q _ => hstage (ratCode q) hsr
    _ = ∑ t ∈ T'.image ratCode, ENNReal.ofReal ((a (Nat.pair c r) t : ℚ) : ℝ) := by
        rw [Finset.sum_image hinjc]
    _ = ∑ t ∈ T'.image ratCode,
          ENNReal.ofReal ((heavyTerm a (Nat.pair c r) t : ℚ) : ℝ) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        rw [heavyTerm, hflag q hq]
        rfl
    _ ≤ ∑ t ∈ Finset.range (Nat.pair c r),
          ENNReal.ofReal ((heavyTerm a (Nat.pair c r) t : ℚ) : ℝ) := by
        refine Finset.sum_le_sum_of_subset ?_
        intro t ht
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        exact Finset.mem_range.2 (hcodes q hq)
    _ = ENNReal.ofReal ((heavyMass a (Nat.pair c r) : ℚ) : ℝ) :=
        (ofReal_heavyMass_eq ha0 _).symm
    _ ≤ ⨆ r' : ℕ, ENNReal.ofReal ((heavyMass a (Nat.pair c r') : ℚ) : ℝ) :=
        le_iSup (fun r' : ℕ => ENNReal.ofReal ((heavyMass a (Nat.pair c r') : ℚ) : ℝ)) r

/-! ### The `Σ₁` enumeration of the heavy intervals -/

open scoped Classical in
/-- **SUV p. 170, the enumeration step.**  For a universal (hence lower
semicomputable) semimeasure `m` on `ℕ`, the family of rational intervals whose a priori
mass exceeds `2^{j+1}` times their length is computably enumerable, uniformly in `j`.

*What a proof has to do.*  `m` is lower semicomputable (`hm.1.2 : IsLSC`), so
`lscRatApprox` (`Omega/CappedScaling.lean`) extracts a computable family of rationals
`mₛ(i) ↑ m(i)`.  At stage `s` compare `2^{j+2}·|I|` with
`2·∑ {mₛ(ratCode q) | ratCode q < s, q ∈ I}` — a finite computable rational sum, the
membership test `q ∈ ratInterval I` being decidable.  Enumerate the pairs `(I, s)` at
which the comparison succeeds, using `ratOfCode` to run over the rationals.  Soundness is
monotonicity of the stage approximations; completeness is that the finite partial sums of
`ν(I)` over the enumerated stages converge to `ν(I)`. -/
theorem exists_computable_heavyInterval_enum {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) :
    ∃ I : ℕ → ℕ → Option (ℚ × ℚ), Computable₂ I ∧
      (∀ (j i : ℕ) (J : ℚ × ℚ), I j i = some J →
        (2 : ℝ≥0∞) ^ (j + 2) * ratIntervalLength J
          ≤ 2 * ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval J then m (ratCode q) else 0)) ∧
      (∀ (j : ℕ) (J : ℚ × ℚ),
        (2 : ℝ≥0∞) ^ (j + 2) * ratIntervalLength J
            < 2 * ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval J then m (ratCode q) else 0) →
        ∃ i : ℕ, I j i = some J) := by
  classical
  obtain ⟨A, hAmono, hAsup, hAcomp⟩ := hm.1.2
  set a : ℕ → ℕ → ℚ := lscRatApprox A with hadef
  have ha : Computable₂ a := computable_lscRatApprox hAcomp
  have ha0 : ∀ s t, 0 ≤ a s t := fun s t => lscRatApprox_nonneg A s t
  have haof : ∀ s t, ENNReal.ofReal ((a s t : ℚ) : ℝ)
      = dyadicValue (A s (natToBitString t) []) s := fun s t => ofReal_lscRatApprox A s t
  have hasup : ∀ t, ⨆ s, ENNReal.ofReal ((a s t : ℚ) : ℝ) = m t := by
    intro t
    have h1 : (⨆ s, ENNReal.ofReal ((a s t : ℚ) : ℝ))
        = ⨆ s, dyadicValue (A s (natToBitString t) []) s := iSup_congr fun s => haof s t
    rw [h1, hAsup (natToBitString t) []]
    simp
  have hale : ∀ s t, ENNReal.ofReal ((a s t : ℚ) : ℝ) ≤ m t := by
    intro s t
    rw [← hasup t]
    exact le_iSup (fun s => ENNReal.ofReal ((a s t : ℚ) : ℝ)) s
  have hamono : ∀ s t, a s t ≤ a (s + 1) t := by
    intro s t
    have h := hAmono s (natToBitString t) []
    rw [← haof s t, ← haof (s + 1) t] at h
    have hR : ((a s t : ℚ) : ℝ) ≤ ((a (s + 1) t : ℚ) : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by exact_mod_cast ha0 (s + 1) t)).1 h
    exact_mod_cast hR
  -- the two sides of the heaviness test, transported to `ℝ≥0∞`
  have hLeq : ∀ (j : ℕ) (J : ℚ × ℚ), (2 : ℝ≥0∞) ^ (j + 2) * ratIntervalLength J
      = ENNReal.ofReal ((2 : ℝ) ^ (j + 2) * (((J.2 : ℚ) : ℝ) - ((J.1 : ℚ) : ℝ))) := by
    intro j J
    have h2 : ENNReal.ofReal ((2 : ℝ) ^ (j + 2)) = (2 : ℝ≥0∞) ^ (j + 2) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num
    rw [ENNReal.ofReal_mul (by positivity), h2]
    simp only [ratIntervalLength]
  have hReq : ∀ u : ℕ, ENNReal.ofReal (2 * ((heavyMass a u : ℚ) : ℝ))
      = 2 * ENNReal.ofReal ((heavyMass a u : ℚ) : ℝ) := by
    intro u
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine ⟨heavyEnum a, computable₂_heavyEnum ha, ?_, ?_⟩
  · -- soundness
    intro j i J hJ
    rw [heavyEnum] at hJ
    cases hcond : decide ((2 : ℚ) ^ (j + 2) *
        ((ratIntervalOfCode i.unpair.1).2 - (ratIntervalOfCode i.unpair.1).1)
          < 2 * heavyMass a i) with
    | false => rw [hcond] at hJ; simp at hJ
    | true =>
        rw [hcond] at hJ
        simp only [Bool.cond_true, Option.some.injEq] at hJ
        subst hJ
        have hq : (2 : ℚ) ^ (j + 2) *
            ((ratIntervalOfCode i.unpair.1).2 - (ratIntervalOfCode i.unpair.1).1)
              < 2 * heavyMass a i := of_decide_eq_true hcond
        have hr : (2 : ℝ) ^ (j + 2) *
            ((((ratIntervalOfCode i.unpair.1).2 : ℚ) : ℝ)
              - (((ratIntervalOfCode i.unpair.1).1 : ℚ) : ℝ))
              ≤ 2 * ((heavyMass a i : ℚ) : ℝ) := by exact_mod_cast hq.le
        calc (2 : ℝ≥0∞) ^ (j + 2) * ratIntervalLength (ratIntervalOfCode i.unpair.1)
            = ENNReal.ofReal ((2 : ℝ) ^ (j + 2) *
                ((((ratIntervalOfCode i.unpair.1).2 : ℚ) : ℝ)
                  - (((ratIntervalOfCode i.unpair.1).1 : ℚ) : ℝ))) := hLeq _ _
          _ ≤ ENNReal.ofReal (2 * ((heavyMass a i : ℚ) : ℝ)) := ENNReal.ofReal_le_ofReal hr
          _ = 2 * ENNReal.ofReal ((heavyMass a i : ℚ) : ℝ) := hReq i
          _ ≤ 2 * _ := by gcongr; exact ofReal_heavyMass_le ha0 hale i
  · -- completeness
    intro j J hlt
    set c : ℕ := Nat.pair (ratCode J.1) (ratCode J.2) with hcdef
    have hJc : ratIntervalOfCode c = J := by rw [hcdef, ratIntervalOfCode_apply]
    have hsup := le_iSup_ofReal_heavyMass ha0 hamono hasup c
    rw [hJc] at hsup
    have hlt2 : (2 : ℝ≥0∞) ^ (j + 2) * ratIntervalLength J
        < ⨆ r : ℕ, 2 * ENNReal.ofReal ((heavyMass a (Nat.pair c r) : ℚ) : ℝ) := by
      refine lt_of_lt_of_le hlt ?_
      rw [← ENNReal.mul_iSup]
      exact mul_le_mul' le_rfl hsup
    obtain ⟨r, hr⟩ := lt_iSup_iff.1 hlt2
    refine ⟨Nat.pair c r, ?_⟩
    have hu : (Nat.pair c r).unpair.1 = c := by rw [Nat.unpair_pair]
    -- transport the strict inequality back to `ℚ`
    rw [hLeq, ← hReq] at hr
    have hpos : (0 : ℝ) < 2 * ((heavyMass a (Nat.pair c r) : ℚ) : ℝ) := by
      by_contra hle
      push Not at hle
      rw [ENNReal.ofReal_eq_zero.2 hle] at hr
      exact absurd hr (by simp)
    have hR := (ENNReal.ofReal_lt_ofReal_iff hpos).1 hr
    have hQ : (2 : ℚ) ^ (j + 2) *
        ((ratIntervalOfCode (Nat.pair c r).unpair.1).2
          - (ratIntervalOfCode (Nat.pair c r).unpair.1).1)
          < 2 * heavyMass a (Nat.pair c r) := by
      rw [hu, hJc]
      exact_mod_cast hR
    rw [heavyEnum, decide_eq_true hQ, Bool.cond_true, hu, hJc]

/-! ### Two proved steps of that route -/

/-- **Disjoint covers.**  When the intervals enumerated at a given level are pairwise
disjoint, the sum of their lengths *is* the Lebesgue measure of their union, so the budget
condition of `IsEffectivelyNullReal` follows from a bound on the measure of the union alone.

This is the last step of `isEffectivelyNullReal_iInter_iUnion_of_volume_le`: it reduces that
leaf to producing a **disjoint** re-covering of `⋃ᵢ Iᵢ`, which is the combinatorial content
described in its docstring. -/
theorem isEffectivelyNullReal_of_disjoint_pow_cover {X : Set ℝ}
    (cover : ℕ → ℕ → Option (ℚ × ℚ)) (hcov : Computable₂ cover)
    (hsub : ∀ n : ℕ, X ⊆ ⋃ i, (cover n i).elim ∅ ratInterval)
    (hdisj : ∀ (n i i' : ℕ), i ≠ i' →
      Disjoint ((cover n i).elim ∅ ratInterval) ((cover n i').elim ∅ ratInterval))
    (hvol : ∀ n : ℕ, volume (⋃ i, (cover n i).elim ∅ ratInterval) ≤ (2 : ℝ≥0∞)⁻¹ ^ n) :
    IsEffectivelyNullReal X := by
  refine isEffectivelyNullReal_of_pow_cover cover hcov hsub fun n => ?_
  have hmeas : ∀ i : ℕ, MeasurableSet ((cover n i).elim ∅ ratInterval) := by
    intro i
    cases h : cover n i with
    | none => simp
    | some J => simp [ratInterval]
  have hlen : ∀ i : ℕ,
      (cover n i).elim 0 ratIntervalLength = volume ((cover n i).elim ∅ ratInterval) := by
    intro i
    cases h : cover n i with
    | none => simp
    | some J => simpa using (volume_ratInterval J).symm
  calc (∑' i, (cover n i).elim 0 ratIntervalLength)
      = ∑' i, volume ((cover n i).elim ∅ ratInterval) := tsum_congr hlen
    _ = volume (⋃ i, (cover n i).elim ∅ ratInterval) :=
        (measure_iUnion (fun i i' h => hdisj n i i' h) hmeas).symm
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n := hvol n

/-- **The rationals form an effectively null set of reals.**  The other step that
`isEffectivelyNullReal_iInter_iUnion_of_volume_le` needs: a re-covering by intervals disjoint
from all the earlier ones misses exactly the points lying on the boundaries of those earlier
intervals, and those are rational, so they can be swept up separately and merged with
`IsEffectivelyNullReal.union`.

The cover puts the interval of radius `2^{-(k+1)}` around the `n`-th rational (through the
repository's computable coding `ratOfCode`) at budget level `k`, which has total length
exactly `2^{-k}`. -/
theorem isEffectivelyNullReal_range_ratCast :
    IsEffectivelyNullReal (Set.range ((↑) : ℚ → ℝ)) := by
  classical
  have hrange : Set.range ((↑) : ℚ → ℝ) = ⋃ n : ℕ, ({((ratOfCode n : ℚ) : ℝ)} : Set ℝ) := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact Set.mem_iUnion.2 ⟨ratCode q, by rw [ratOfCode_ratCode]; rfl⟩
    · intro hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
      exact ⟨ratOfCode n, by simpa using hn.symm⟩
  rw [hrange]
  refine isEffectivelyNullReal_iUnion
    (fun n k i => if i = 0 then some (centreInterval (ratOfCode n) (k + 1)) else none)
    ?_ ?_ ?_
  · have hc : Computable (fun p : (ℕ × ℕ) × ℕ => decide (p.2 = 0)) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp Computable.snd (Computable.const 0)
    have hsome : Computable (fun p : (ℕ × ℕ) × ℕ =>
        (some (centreInterval (ratOfCode p.1.1) (p.1.2 + 1)) : Option (ℚ × ℚ))) :=
      Computable.option_some.comp (computable₂_centreInterval.comp
        (computable_ratOfCode.comp (Computable.fst.comp Computable.fst))
        (Primrec.succ.to_comp.comp (Computable.snd.comp Computable.fst)))
    refine (Computable.cond hc hsome (Computable.const none)).of_eq fun p => ?_
    by_cases h : p.2 = 0 <;> simp [h]
  · intro n k
    refine Set.singleton_subset_iff.2 (Set.mem_iUnion.2 ⟨0, ?_⟩)
    simp only [Option.elim]
    refine mem_centreInterval ?_
    simp
  · intro n k
    have hval : ∀ i : ℕ,
        ((if i = 0 then some (centreInterval (ratOfCode n) (k + 1)) else none :
            Option (ℚ × ℚ))).elim 0 ratIntervalLength
          = if i = 0 then ratIntervalLength (centreInterval (ratOfCode n) (k + 1)) else 0 := by
      intro i
      by_cases h : i = 0 <;> simp [h]
    have hsingle : (∑' i : ℕ,
        if i = 0 then ratIntervalLength (centreInterval (ratOfCode n) (k + 1)) else 0)
          = ratIntervalLength (centreInterval (ratOfCode n) (k + 1)) := by
      rw [tsum_eq_single 0 (fun i hi => by simp [hi])]
      simp
    have hcalc : 2 * (2 : ℝ≥0∞)⁻¹ ^ (k + 1) = (2 : ℝ≥0∞)⁻¹ ^ k := by
      rw [pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞) ((2 : ℝ≥0∞)⁻¹ ^ k), mul_assoc,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
    rw [tsum_congr hval, hsingle, ratIntervalLength_centreInterval, hcalc]

/-! ### From small unions to an effectively null set -/

/-- **The union/sum bridge for `IsEffectivelyNullReal` (SUV p. 170).**  A computable
family of rational intervals whose *unions* have Lebesgue measure at most `2^{-j}` defines
an effectively null intersection.

This is exactly the gap between the frozen `IsEffectivelyNullReal`, which bounds the sum
`∑ᵢ |Iᵢ|` of the enumerated lengths, and the measure `Leb(⋃ᵢ Iᵢ)` of the union: an
enumeration cannot be pruned on the fly, because an interval emitted early may only later
become redundant.

*The route.*  `Omega/GridCells.lean` re-covers `U := ⋃ᵢ Iᵢ` by the **elementary
cells of the endpoint grid**: at stage `N` the grid is the set of endpoints of
`I 0, …, I N`, and a cell is a maximal interval between two grid points containing no grid
point inside.  Every `I i` with `i ≤ N` has both endpoints in that grid, so a cell is
either contained in `I i` or disjoint from it, and its **midpoint decides which** — which
is what makes the selection computable.  `gridCover` emits the cells that are new at their
stage (inside `U_{N+1}`, outside `U_N`), with canonical endpoint indices; these are pairwise
disjoint (`gridCover_disjoint`), lie inside `U` (`iUnion_gridCover_subset`), and cover every
**irrational** point of `U` (`sdiff_range_ratCast_subset_iUnion_gridCover`).  For a disjoint
family the sum of the lengths *is* the measure of the union, which is
`isEffectivelyNullReal_of_disjoint_pow_cover`; the rationals that the cells miss — they are
exactly the grid points — are swept up by `isEffectivelyNullReal_range_ratCast` and merged
with `IsEffectivelyNullReal.union`.

No dyadic cells, no pull-back to Cantor space and no tiling of `ℝ` by unit intervals are
needed: `ratInterval` is an *open* interval, so the cells are genuine rational intervals. -/
theorem isEffectivelyNullReal_iInter_iUnion_of_volume_le
    {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I)
    (hvol : ∀ j : ℕ, volume (⋃ i : ℕ, (I j i).elim ∅ ratInterval) ≤ (2 : ℝ≥0∞)⁻¹ ^ j) :
    IsEffectivelyNullReal (⋂ j : ℕ, ⋃ i : ℕ, (I j i).elim ∅ ratInterval) := by
  classical
  have hmain : IsEffectivelyNullReal
      ((⋂ j : ℕ, ⋃ i : ℕ, (I j i).elim ∅ ratInterval) \ Set.range ((↑) : ℚ → ℝ)) := by
    refine isEffectivelyNullReal_of_disjoint_pow_cover (gridCover I) (computable₂_gridCover hI)
      (fun n => ?_) (fun n k k' hkk => gridCover_disjoint I n k k' hkk) (fun n => ?_)
    · refine subset_trans ?_ (sdiff_range_ratCast_subset_iUnion_gridCover I n)
      exact Set.sdiff_subset_sdiff_left (Set.iInter_subset _ n)
    · exact le_trans (measure_mono (iUnion_gridCover_subset I n)) (hvol n)
  refine (hmain.union isEffectivelyNullReal_range_ratCast).mono fun x hx => ?_
  by_cases h : x ∈ Set.range ((↑) : ℚ → ℝ)
  · exact Or.inr h
  · exact Or.inl ⟨hx, h⟩

/-! ### Shrinking a ball to a rational interval -/

open scoped Classical in
/-- **SUV p. 170, the rationalisation step.**  If the mass that a
weight `w` on `ℚ` puts on the `ε`-ball around `x` exceeds `t`, then some *rational*
interval containing `x`, of length at most `2ε`, already carries more than `t`.

*What a proof has to do.*  `∑' q, …` over `ℚ` is the supremum of its finite partial sums,
so a finite set `S` of rationals inside the ball already carries more than `t`; density of
`ℚ` gives rational endpoints `l, r` with `x - ε ≤ l < min (S ∪ {x})` and
`max (S ∪ {x}) < r ≤ x + ε`. -/
theorem exists_ratInterval_lt_tsum {w : ℚ → ℝ≥0∞} {x ε : ℝ} (hε : 0 < ε) {t : ℝ≥0∞}
    (ht : t < ∑' q : ℚ, (if |x - (q : ℝ)| < ε then w q else 0)) :
    ∃ J : ℚ × ℚ, x ∈ ratInterval J ∧ ratIntervalLength J ≤ ENNReal.ofReal (2 * ε) ∧
      t < ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval J then w q else 0) := by
  classical
  -- a finite set of rationals inside the ball already carries more than `t`
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at ht
  obtain ⟨S, hS⟩ := ht
  have hsum : ∑ q ∈ S.filter (fun q : ℚ => |x - (q : ℝ)| < ε), w q
      = ∑ q ∈ S, (if |x - (q : ℝ)| < ε then w q else 0) := Finset.sum_filter _ _
  rw [← hsum] at hS
  have hmem : ∀ q ∈ S.filter (fun q : ℚ => |x - (q : ℝ)| < ε), |x - (q : ℝ)| < ε := by
    intro q hq
    exact (Finset.mem_filter.1 hq).2
  have hSne : (S.filter (fun q : ℚ => |x - (q : ℝ)| < ε)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (S.filter (fun q : ℚ => |x - (q : ℝ)| < ε)) with hE | hN
    · rw [hE] at hS; simp at hS
    · exact hN
  -- the extreme members of that finite set
  obtain ⟨q₀, hq₀, hq₀min⟩ :=
    (S.filter (fun q : ℚ => |x - (q : ℝ)| < ε)).exists_min_image (fun q : ℚ => (q : ℝ)) hSne
  obtain ⟨q₁, hq₁, hq₁max⟩ :=
    (S.filter (fun q : ℚ => |x - (q : ℝ)| < ε)).exists_max_image (fun q : ℚ => (q : ℝ)) hSne
  have h0 := hmem q₀ hq₀
  have h1 := hmem q₁ hq₁
  rw [abs_sub_lt_iff] at h0 h1
  -- rational endpoints separating the finite set (and `x`) from the ends of the ball
  obtain ⟨l, hl1, hl2⟩ :=
    exists_rat_btwn (lt_min (by linarith [h0.1] : x - ε < (q₀ : ℝ)) (by linarith : x - ε < x))
  obtain ⟨r, hr1, hr2⟩ :=
    exists_rat_btwn (max_lt (by linarith [h1.2] : (q₁ : ℝ) < x + ε) (by linarith : x < x + ε))
  have hlq : ((l : ℚ) : ℝ) < (q₀ : ℝ) := lt_of_lt_of_le hl2 (min_le_left _ _)
  have hlx : ((l : ℚ) : ℝ) < x := lt_of_lt_of_le hl2 (min_le_right _ _)
  have hqr : ((q₁ : ℚ) : ℝ) < (r : ℝ) := lt_of_le_of_lt (le_max_left _ _) hr1
  have hxr : x < ((r : ℚ) : ℝ) := lt_of_le_of_lt (le_max_right _ _) hr1
  refine ⟨(l, r), Set.mem_Ioo.2 ⟨hlx, hxr⟩, ?_, ?_⟩
  · refine ENNReal.ofReal_le_ofReal ?_
    have : ((r : ℚ) : ℝ) - ((l : ℚ) : ℝ) ≤ 2 * ε := by linarith
    exact this
  · refine lt_of_lt_of_le hS ?_
    have hsub : ∀ q ∈ S.filter (fun q : ℚ => |x - (q : ℝ)| < ε),
        w q = (if ((q : ℚ) : ℝ) ∈ ratInterval (l, r) then w q else 0) := by
      intro q hq
      rw [ite_eq_left]
      exact Set.mem_Ioo.2 ⟨lt_of_lt_of_le hlq (hq₀min q hq), lt_of_le_of_lt (hq₁max q hq) hqr⟩
    calc ∑ q ∈ S.filter (fun q : ℚ => |x - (q : ℝ)| < ε), w q
        = ∑ q ∈ S.filter (fun q : ℚ => |x - (q : ℝ)| < ε),
            (if ((q : ℚ) : ℝ) ∈ ratInterval (l, r) then w q else 0) :=
          Finset.sum_congr rfl hsub
      _ ≤ ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval (l, r) then w q else 0) :=
          ENNReal.sum_le_tsum _

/-! ### The estimate -/

open scoped Classical in
/-- **SUV p. 170, the measure estimate behind Theorem 115.**  For a random `α` the total a
priori probability of the rationals in the `2^{-k}`-neighbourhood of `α` is `O(2^{-k})`. -/
theorem exists_const_apriori_ratCode_neighbourhood_le {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {α : ℝ} (h : IsMartinLofRandomReal α) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ k : ℕ,
      (∑' q : ℚ, if |α - (q : ℝ)| < (2 : ℝ)⁻¹ ^ k then m (ratCode q) else 0)
        ≤ c * (2 : ℝ≥0∞)⁻¹ ^ k := by
  classical
  obtain ⟨I, hIc, hIsound, hIcomplete⟩ := exists_computable_heavyInterval_enum hm
  -- the total a priori mass of the rationals is at most `1`
  have hmass : (∑' q : ℚ, m (ratCode q)) ≤ 1 :=
    le_trans (ENNReal.tsum_comp_le_tsum_of_injective ratCode_injective m) hm.tsum_le_one
  have hpow2 : ∀ j : ℕ, (2 : ℝ≥0∞) ^ (j + 2) ≠ 0 := fun _ => pow_ne_zero _ two_ne_zero
  have hpow2t : ∀ j : ℕ, (2 : ℝ≥0∞) ^ (j + 2) ≠ ⊤ := fun _ =>
    ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  -- each level of the test has small Lebesgue measure
  have hvol : ∀ j : ℕ, volume (⋃ i : ℕ, (I j i).elim ∅ ratInterval) ≤ (2 : ℝ≥0∞)⁻¹ ^ j := by
    intro j
    have hSJ : ∀ i : ℕ, (I j i).elim ∅ ratInterval = ratInterval ((I j i).getD (0, 0)) := by
      intro i
      cases hIi : I j i with
      | none => simp [ratInterval]
      | some J => simp
    set T : ℕ → Set ℝ := fun N =>
      ⋃ J ∈ (Finset.range N).image (fun i => (I j i).getD (0, 0)), ratInterval J with hTdef
    have hTmono : Monotone T := by
      intro a b hab
      refine Set.iUnion₂_subset fun J hJ => ?_
      simp only [Finset.mem_image, Finset.mem_range] at hJ
      obtain ⟨i, hi, rfl⟩ := hJ
      refine Set.subset_biUnion_of_mem (u := fun J => ratInterval J) ?_
      exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (lt_of_lt_of_le hi hab))
    have hTunion : (⋃ N : ℕ, T N) = ⋃ i : ℕ, (I j i).elim ∅ ratInterval := by
      refine Set.Subset.antisymm (Set.iUnion_subset fun N => ?_) (Set.iUnion_subset fun i => ?_)
      · refine Set.iUnion₂_subset fun J hJ => ?_
        simp only [Finset.mem_image, Finset.mem_range] at hJ
        obtain ⟨i, _, rfl⟩ := hJ
        rw [← hSJ i]
        exact Set.subset_iUnion (fun i => (I j i).elim ∅ ratInterval) i
      · refine Set.subset_iUnion_of_subset (i + 1) ?_
        rw [hSJ i, hTdef]
        refine Set.subset_biUnion_of_mem (u := fun J => ratInterval J) ?_
        exact Finset.mem_image_of_mem _ (Finset.self_mem_range_succ i)
    rw [← hTunion, hTmono.measure_iUnion]
    refine iSup_le fun N => ?_
    have hF : ∀ J ∈ (Finset.range N).image (fun i => (I j i).getD (0, 0)),
        (2 : ℝ≥0∞) ^ (j + 2) * ratIntervalLength J
          ≤ 2 * ∑' q : ℚ,
              (if ((q : ℚ) : ℝ) ∈ ratInterval J then m (ratCode q) else 0) := by
      intro J hJ
      simp only [Finset.mem_image, Finset.mem_range] at hJ
      obtain ⟨i, _, rfl⟩ := hJ
      cases hIi : I j i with
      | none =>
          have hzero : ratIntervalLength ((0 : ℚ), (0 : ℚ)) = 0 := by simp [ratIntervalLength]
          simp only [Option.getD_none, hzero, mul_zero]
          exact zero_le
      | some J' =>
          simp only [Option.getD_some]
          exact hIsound j i J' hIi
    have hbound := mul_volume_biUnion_le (ν := fun q => m (ratCode q)) hmass
      (c := (2 : ℝ≥0∞) ^ (j + 2)) _ hF
    have hfour : (2 : ℝ≥0∞) ^ (j + 2) * (2 : ℝ≥0∞)⁻¹ ^ j = 4 := by
      rw [pow_add, mul_comm ((2 : ℝ≥0∞) ^ j) ((2 : ℝ≥0∞) ^ 2), mul_assoc, ← mul_pow,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]
      norm_num
    rw [← hfour] at hbound
    exact (ENNReal.mul_le_mul_iff_right (hpow2 j) (hpow2t j)).1 hbound
  -- the random `α` escapes some level of the test
  have hnull := isEffectivelyNullReal_iInter_iUnion_of_volume_le hIc hvol
  have hnot : α ∉ ⋂ j : ℕ, ⋃ i : ℕ, (I j i).elim ∅ ratInterval := h _ hnull
  rw [Set.mem_iInter] at hnot
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  refine ⟨(2 : ℝ≥0∞) ^ (j + 3), ENNReal.pow_ne_top ENNReal.ofNat_ne_top, fun k => ?_⟩
  by_contra hcon
  push Not at hcon
  -- shrink the ball to a rational interval that is still heavy
  obtain ⟨J, hJmem, hJlen, hJmass⟩ :=
    exists_ratInterval_lt_tsum (w := fun q => m (ratCode q)) (x := α)
      (ε := (2 : ℝ)⁻¹ ^ k) (by positivity) hcon
  have hlen2 : ENNReal.ofReal (2 * ((2 : ℝ)⁻¹ ^ k)) = 2 * (2 : ℝ≥0∞)⁻¹ ^ k := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_inv_two_pow]
    norm_num
  have hheavy : (2 : ℝ≥0∞) ^ (j + 2) * ratIntervalLength J
      < 2 * ∑' q : ℚ, (if ((q : ℚ) : ℝ) ∈ ratInterval J then m (ratCode q) else 0) := by
    have hstep : (2 : ℝ≥0∞) ^ (j + 2) * ratIntervalLength J
        ≤ (2 : ℝ≥0∞) ^ (j + 3) * (2 : ℝ≥0∞)⁻¹ ^ k := by
      calc (2 : ℝ≥0∞) ^ (j + 2) * ratIntervalLength J
          ≤ (2 : ℝ≥0∞) ^ (j + 2) * (2 * (2 : ℝ≥0∞)⁻¹ ^ k) := by
            gcongr
            rw [← hlen2]
            exact hJlen
        _ = (2 : ℝ≥0∞) ^ (j + 3) * (2 : ℝ≥0∞)⁻¹ ^ k := by rw [← mul_assoc, ← pow_succ]
    refine lt_of_le_of_lt hstep (lt_of_lt_of_le hJmass ?_)
    exact le_mul_of_one_le_left (zero_le) one_le_two
  obtain ⟨i, hi⟩ := hIcomplete j J hheavy
  exact hj (Set.mem_iUnion.2 ⟨i, by rw [hi]; exact hJmem⟩)

end Kolmogorov
