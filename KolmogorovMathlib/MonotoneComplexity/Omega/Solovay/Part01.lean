



/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic
import KolmogorovMathlib.MonotoneComplexity.Omega.LscEnum
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaComplete
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaFromComplete
import KolmogorovMathlib.MonotoneComplexity.Omega.ShiftedProcess
import KolmogorovMathlib.MonotoneComplexity.Omega.LeftmostRandom

/-!
# SUV Section 5.7.1–5.7.4: Solovay reducibility and completeness

This module states the Solovay-reducibility layer of SUV Section 5.7
(pp. 158–165):

* `SolovayDominates` — the book's fine-grained relation `α ≼₁ β` (p. 158);
* `ConvergesBetter` — the same relation in terms of approximating sequences
  (p. 158) and the equivalence of the two renderings;
* **Theorem 101** (p. 159): `α ≼₁ β` iff `β - α` is lower semicomputable;
* `SolovayReducible` — Solovay reducibility `α ≼ β`, i.e. `α ≼₁ cβ` for some
  positive integer `c` (p. 160), and the completeness deficiency;
* **Theorem 102** (p. 160): a biggest lower semicomputable real exists;
* **Theorem 103** (p. 160): complete lower semicomputable reals in `(0,1)` are
  exactly the sums of maximal semimeasures on `ℕ`;
* Section 5.7.2 (pp. 160–161): randomness is upward closed for `≼`;
* **Theorem 110** (p. 165): a lower semicomputable real is Solovay complete iff it
  is ML-random.

## Definitional choices frozen here

* The **primary** rendering of `α ≼₁ β` is the sequence-free reduction-function
  form of p. 158: a partial computable `p : ℚ →. ℚ`, total on every rational
  `r < β`, with `p(r) < α` and `α - p(r) < β - r`. Both inequalities are strict, as
  in the source. The sequence definition (`ConvergesBetter`, with `α - a_{h i} ≤
  β - b_i`) is stated separately and tied to it by
  `solovayDominates_iff_convergesBetter`; the source's own remark that the choice
  of approximating sequences is irrelevant is exactly that leaf.
* `SolovayReducible` uses a positive **integer** `c`, as in the book's definition;
  the "convenient notation" with a positive rational `c` is `SolovayReducibleWith`,
  and `solovayReducible_iff_exists_rat` records that the two agree.
-/

namespace Kolmogorov


open ComputableReals
open MeasureTheory ENNReal

/-! ### The relation `α ≼₁ β` (SUV p. 158) -/

/-- **SUV Section 5.7.1 (p. 158).** `SolovayDominates α β` is the book's `α ≼₁ β`:
there exists a partial computable function `p` defined on all rational numbers
`r < β` such that `p(r) < α` and `α - p(r) < β - r` for all of them. The function
`p` is the source's *reduction function*. -/
def SolovayDominates (α β : ℝ) : Prop :=
  ∃ p : ℚ →. ℚ, Partrec p ∧ ∀ r : ℚ, (r : ℝ) < β →
    ∃ q ∈ p r, (q : ℝ) < α ∧ α - (q : ℝ) < β - (r : ℝ)

/-- **SUV Section 5.7.1 (p. 158), the original definition.** The approximation
`a → α` *converges better (not worse) than* `b → β` if there exists a total
computable function `h` with `α - a_{h(i)} ≤ β - b_i` for every `i`. -/
def ConvergesBetter {α β : ℝ} (a : LowerApprox α) (b : LowerApprox β) : Prop :=
  ∃ h : ℕ → ℕ, Computable h ∧ ∀ i, α - (a.seq (h i) : ℝ) ≤ β - (b.seq i : ℝ)

/-! ### The `≼₁` criterion of SUV p. 158

The reduction function of the source is a search: on input `r` wait until the
approximation `b` of `β` passes `r`, then answer with the corresponding term of the
approximation `a` of `α`.  `Omega/LscBasic.lean` supplies the partial computable
object (`ratSearchPair`); the criterion below packages its correctness. -/

/-- **SUV p. 158.** If `a`, `b` are computable rational sequences with `a n < α`,
`α - a n ≤ β - b n` for all `n`, and `b` eventually passes every rational strictly
below `β`, then `α ≼₁ β`. -/
theorem solovayDominates_of_approxPair {α β : ℝ} {a b : ℕ → ℚ}
    (ha : Computable a) (hb : Computable b)
    (hlt : ∀ n, ((a n : ℚ) : ℝ) < α)
    (hgap : ∀ n, α - ((a n : ℚ) : ℝ) ≤ β - ((b n : ℚ) : ℝ))
    (hcof : ∀ r : ℚ, (r : ℝ) < β → ∃ n, r < b n) :
    SolovayDominates α β := by
  refine ⟨ratSearchPair a b, partrec_ratSearchPair ha hb, ?_⟩
  intro r hr
  obtain ⟨q, hq⟩ := Part.dom_iff_mem.1 (ratSearchPair_dom (hcof r hr))
  obtain ⟨n, hn, hqn⟩ := mem_ratSearchPair hq
  subst hqn
  have hrn : (r : ℝ) < ((b n : ℚ) : ℝ) := by exact_mod_cast hn
  have hg := hgap n
  exact ⟨a n, hq, hlt n, by linarith⟩

/-- **SUV p. 160.** `≼₁` is invariant under scaling both sides by one positive
rational: this is what makes the "convenient notation" `α ≼_c β` a preorder-friendly
device. -/
theorem SolovayDominates.rat_mul {c : ℚ} (hc : 0 < c) {α β : ℝ}
    (h : SolovayDominates α β) : SolovayDominates ((c : ℝ) * α) ((c : ℝ) * β) := by
  obtain ⟨p, hp, hspec⟩ := h
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hdiv : Computable (fun r : ℚ => r / c) := computable_ratDivConst hc
  have hmul : Computable₂ (fun (_ : ℚ) (q : ℚ) => c * q) :=
    Computable₂.comp computable₂_ratMul (Computable.const c) Computable.snd
  refine ⟨fun r => (p (r / c)).map (fun q => c * q), Partrec.map (hp.comp hdiv) hmul, ?_⟩
  intro r hr
  have hrc : ((r / c : ℚ) : ℝ) < β := by
    push_cast
    rw [div_lt_iff₀ hcR]
    linarith
  obtain ⟨q, hq, hqlt, hqgap⟩ := hspec (r / c) hrc
  refine ⟨c * q, Part.mem_map _ hq, ?_, ?_⟩
  · push_cast
    exact mul_lt_mul_of_pos_left hqlt hcR
  · have hq2 : α - (q : ℝ) < β - (r : ℝ) / (c : ℝ) := by push_cast at hqgap; exact hqgap
    have h2 := mul_lt_mul_of_pos_left hq2 hcR
    have h3 : (c : ℝ) * ((r : ℝ) / (c : ℝ)) = (r : ℝ) := by field_simp
    rw [mul_sub, mul_sub, h3] at h2
    push_cast
    linarith

/-- **SUV p. 158.** "The choice of specific sequences that approximate `α` and `β`
is irrelevant: any two increasing computable sequences of rational numbers that
have the same limit are equivalent with respect to this quasi-ordering", and the
resulting relation is exactly the reduction-function reformulation. -/
theorem convergesBetter_of_solovayDominates {α β : ℝ}
    (a : LowerApprox α) (b : LowerApprox β) (h : SolovayDominates α β) :
    ConvergesBetter a b := by
  obtain ⟨p, hp, hspec⟩ := h
  have hHp : Partrec (fun i : ℕ => (p (b.seq i)).bind (ratSearchIndex a.seq)) :=
    Partrec.bind (hp.comp b.isComputable)
      ((partrec_ratSearchIndex a.isComputable).comp Computable.snd)
  have hmem : ∀ i : ℕ, ∃ n, n ∈ (p (b.seq i)).bind (ratSearchIndex a.seq) := by
    intro i
    obtain ⟨q, hq, hqlt, -⟩ := hspec (b.seq i) (b.seq_lt i)
    obtain ⟨n, hn⟩ := Part.dom_iff_mem.1 (ratSearchIndex_dom (a.exists_lt hqlt))
    exact ⟨n, Part.mem_bind_iff.2 ⟨q, hq, hn⟩⟩
  have hdom : ∀ i : ℕ, ((p (b.seq i)).bind (ratSearchIndex a.seq)).Dom :=
    fun i => Part.dom_iff_mem.2 (hmem i)
  refine ⟨fun i => ((p (b.seq i)).bind (ratSearchIndex a.seq)).get (hdom i),
    computable_of_partrec_total hHp hdom, ?_⟩
  intro i
  obtain ⟨q, hq, hn⟩ := Part.mem_bind_iff.1 (Part.get_mem (hdom i))
  obtain ⟨q', hq', hq'lt, hq'gap⟩ := hspec (b.seq i) (b.seq_lt i)
  have hqq : q = q' := Part.mem_unique hq hq'
  subst hqq
  have hlt := mem_ratSearchIndex hn
  have hltR : ((q : ℚ) : ℝ) <
      ((a.seq (((p (b.seq i)).bind (ratSearchIndex a.seq)).get (hdom i)) : ℚ) : ℝ) := by
    exact_mod_cast hlt
  linarith

/-- Solovay domination of `α` over `β` is equivalent to the approximation of `α` converging
better than that of `β`. SUV p. 165. -/
theorem solovayDominates_iff_convergesBetter {α β : ℝ}
    (a : LowerApprox α) (b : LowerApprox β) :
    SolovayDominates α β ↔ ConvergesBetter a b := by
  refine ⟨convergesBetter_of_solovayDominates a b, ?_⟩
  rintro ⟨f, hf, hspec⟩
  exact solovayDominates_of_approxPair (a.isComputable.comp hf) b.isComputable
    (fun n => a.seq_lt (f n)) hspec (fun r hr => b.exists_lt hr)

/-- **SUV p. 158.** The relation `≼₁` is reflexive. -/
theorem solovayDominates_refl {α : ℝ} (hα : IsLowerSemicomputableReal α) :
    SolovayDominates α α := by
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hα
  exact solovayDominates_of_approxPair a.isComputable a.isComputable a.seq_lt
    (fun _ => le_rfl) (fun _ hr => a.exists_lt hr)

/-- **SUV p. 158.** The relation `≼₁` is transitive ("take the composition of two
reducing functions"). -/
theorem SolovayDominates.trans {α β γ : ℝ}
    (hαβ : SolovayDominates α β) (hβγ : SolovayDominates β γ) :
    SolovayDominates α γ := by
  obtain ⟨p, hp, hpspec⟩ := hαβ
  obtain ⟨p', hp', hp'spec⟩ := hβγ
  refine ⟨fun r => (p' r).bind p, Partrec.bind hp' (hp.comp Computable.snd), ?_⟩
  intro r hr
  obtain ⟨q', hq', hq'lt, hq'gap⟩ := hp'spec r hr
  obtain ⟨q, hq, hqlt, hqgap⟩ := hpspec q' hq'lt
  exact ⟨q, Part.mem_bind_iff.2 ⟨q', hq', hq⟩, hqlt, by linarith⟩

/-! ### Theorem 101 -/

/-- For every two lower semicomputable reals `α` and `ρ` we have `α ≼₁ α + ρ`; equivalently, if
`β - α` is lower semicomputable then `α ≼₁ β`.  SUV Theorem 101 (Section 5.7, p. 159), first
direction. -/
theorem solovayDominates_of_isLowerSemicomputableReal_sub {α β : ℝ}
    (hα : IsLowerSemicomputableReal α) (hβα : IsLowerSemicomputableReal (β - α)) :
    SolovayDominates α β := by
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hα
  obtain ⟨c, hc, hmc, hlc⟩ := hβα
  have hcle : ∀ n, ((c n : ℚ) : ℝ) ≤ β - α := rat_le_of_monotone_tendsto hmc hlc
  have hblim : Filter.Tendsto (fun n => ((a.seq n + c n : ℚ) : ℝ)) Filter.atTop (nhds β) := by
    have hcast : (fun n => ((a.seq n + c n : ℚ) : ℝ))
        = fun n => ((a.seq n : ℚ) : ℝ) + ((c n : ℚ) : ℝ) := by
      funext n; push_cast; ring
    rw [hcast]
    have hsum := a.tendsto.add hlc
    have hβeq : α + (β - α) = β := by ring
    rwa [hβeq] at hsum
  refine solovayDominates_of_approxPair a.isComputable
    (Computable₂.comp computable₂_ratAdd a.isComputable hc) a.seq_lt (fun n => ?_)
    (fun r hr => exists_rat_lt_of_tendsto hblim hr)
  have h1 := hcle n
  push_cast
  linarith

/-- If `α ≼₁ β` then `ρ = β - α` is lower semicomputable.  SUV Theorem 101 (Section 5.7, p.
159), reverse direction. -/
theorem isLowerSemicomputableReal_sub_of_solovayDominates {α β : ℝ}
    (hα : IsLowerSemicomputableReal α) (hβ : IsLowerSemicomputableReal β)
    (h : SolovayDominates α β) : IsLowerSemicomputableReal (β - α) := by
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hα
  obtain ⟨b⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hβ
  obtain ⟨f, hf, hspec⟩ := convergesBetter_of_solovayDominates a b h
  have hdc : Computable (fun i => b.seq i - a.seq (f i)) :=
    Computable₂.comp computable₂_ratSub b.isComputable (a.isComputable.comp hf)
  have hdle : ∀ i, (((b.seq i - a.seq (f i) : ℚ)) : ℝ) ≤ β - α := by
    intro i
    have h1 := hspec i
    push_cast
    linarith
  have h0 : Filter.Tendsto (fun i => α - ((a.seq (f i) : ℚ) : ℝ)) Filter.atTop (nhds 0) := by
    have hlow : ∀ i, (0 : ℝ) ≤ α - ((a.seq (f i) : ℚ) : ℝ) := by
      intro i; have := a.seq_lt (f i); linarith
    have hb0 : Filter.Tendsto (fun i => β - ((b.seq i : ℚ) : ℝ)) Filter.atTop (nhds 0) := by
      have hbb := b.tendsto.const_sub β
      simpa using hbb
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb0 hlow hspec
  have ha : Filter.Tendsto (fun i => ((a.seq (f i) : ℚ) : ℝ)) Filter.atTop (nhds α) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => α) Filter.atTop (nhds α) := tendsto_const_nhds
    have h1 := hconst.sub h0
    have h2 : (fun i : ℕ => α - (α - ((a.seq (f i) : ℚ) : ℝ)))
        = fun i => ((a.seq (f i) : ℚ) : ℝ) := by funext i; ring
    rw [h2] at h1
    simpa using h1
  have hlim : Filter.Tendsto (fun i => (((b.seq i - a.seq (f i) : ℚ)) : ℝ))
      Filter.atTop (nhds (β - α)) := by
    have hcast : (fun i => (((b.seq i - a.seq (f i) : ℚ)) : ℝ))
        = fun i => ((b.seq i : ℚ) : ℝ) - ((a.seq (f i) : ℚ) : ℝ) := by
      funext i; push_cast; ring
    rw [hcast]
    exact b.tendsto.sub ha
  exact ⟨ratRunMax (fun i => b.seq i - a.seq (f i)), computable_ratRunMax hdc,
    monotone_ratRunMax _, tendsto_ratRunMax hlim hdle⟩

/-- `α ≼₁ β` if and only if `β - α` is lower semicomputable (equivalently, `β = α + ρ` for some
lower semicomputable real `ρ`).  SUV Theorem 101 (Section 5.7, p. 159). -/
theorem solovayDominates_iff_isLowerSemicomputableReal_sub {α β : ℝ}
    (hα : IsLowerSemicomputableReal α) (hβ : IsLowerSemicomputableReal β) :
    SolovayDominates α β ↔ IsLowerSemicomputableReal (β - α) :=
  ⟨isLowerSemicomputableReal_sub_of_solovayDominates hα hβ,
    solovayDominates_of_isLowerSemicomputableReal_sub hα⟩

/-! ### The series form of `≼₁` (SUV p. 159) -/

/-- **SUV p. 159, "Here is a special case".** If `∑ uᵢ = α` and `∑ vᵢ = β` are
computable series whose terms are nonnegative rationals for `i > 0` (the starting
points `u₀`, `v₀` may be negative) and `uᵢ ≤ vᵢ` for all `i > 0`, then `α ≼₁ β`. -/
theorem solovayDominates_of_series_le {u v : ℕ → ℚ} {α β : ℝ}
    (hu : Computable u) (hv : Computable v)
    (hu0 : ∀ i, 0 < i → 0 ≤ u i) (hv0 : ∀ i, 0 < i → 0 ≤ v i)
    (hle : ∀ i, 0 < i → u i ≤ v i)
    (hα : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (u i : ℝ)) Filter.atTop (nhds α))
    (hβ : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (v i : ℝ)) Filter.atTop (nhds β)) :
    SolovayDominates α β := by
  -- `hv0` is implied by `hu0`/`hle`; it is part of the frozen statement, so it is
  -- recorded here rather than dropped.
  have _hv0 := hv0
  have hcastU : ∀ n : ℕ,
      ((ratRangeSum u n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((u i : ℚ) : ℝ) := by
    intro n; rw [ratRangeSum_eq]; push_cast; ring
  have hcastV : ∀ n : ℕ,
      ((ratRangeSum v n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((v i : ℚ) : ℝ) := by
    intro n; rw [ratRangeSum_eq]; push_cast; ring
  have hstep : ∀ N : ℕ, 0 < N → ∀ m : ℕ, N ≤ m →
      (0 : ℝ) ≤ (∑ i ∈ Finset.range m, ((u i : ℚ) : ℝ))
          - (∑ i ∈ Finset.range N, ((u i : ℚ) : ℝ)) ∧
      (∑ i ∈ Finset.range m, ((u i : ℚ) : ℝ)) - (∑ i ∈ Finset.range N, ((u i : ℚ) : ℝ))
        ≤ (∑ i ∈ Finset.range m, ((v i : ℚ) : ℝ))
          - (∑ i ∈ Finset.range N, ((v i : ℚ) : ℝ)) := by
    intro N hN m hm
    rw [← Finset.sum_Ico_eq_sub _ hm, ← Finset.sum_Ico_eq_sub _ hm]
    refine ⟨Finset.sum_nonneg (fun i hi => ?_), Finset.sum_le_sum (fun i hi => ?_)⟩
    · have hi0 : 0 < i := lt_of_lt_of_le hN (Finset.mem_Ico.1 hi).1
      exact_mod_cast hu0 i hi0
    · have hi0 : 0 < i := lt_of_lt_of_le hN (Finset.mem_Ico.1 hi).1
      exact_mod_cast hle i hi0
  have hUle : ∀ N : ℕ, 0 < N → (∑ i ∈ Finset.range N, ((u i : ℚ) : ℝ)) ≤ α := by
    intro N hN
    have h1 := hα.sub_const (∑ i ∈ Finset.range N, ((u i : ℚ) : ℝ))
    have h2 : (0 : ℝ) ≤ α - ∑ i ∈ Finset.range N, ((u i : ℚ) : ℝ) :=
      ge_of_tendsto h1 (Filter.eventually_atTop.2 ⟨N, fun m hm => (hstep N hN m hm).1⟩)
    linarith
  have hgapN : ∀ N : ℕ, 0 < N →
      α - (∑ i ∈ Finset.range N, ((u i : ℚ) : ℝ))
        ≤ β - (∑ i ∈ Finset.range N, ((v i : ℚ) : ℝ)) :=
    fun N hN => le_of_tendsto_of_tendsto (hα.sub_const _) (hβ.sub_const _)
      (Filter.eventually_atTop.2 ⟨N, fun m hm => (hstep N hN m hm).2⟩)
  have hAc : Computable (fun n : ℕ => ratRangeSum u (n + 1) - invSucc n) :=
    Computable₂.comp computable₂_ratSub
      ((computable_ratRangeSum hu).comp Primrec.succ.to_comp) computable_invSucc
  have hBc : Computable (fun n : ℕ => ratRangeSum v (n + 1) - invSucc n) :=
    Computable₂.comp computable₂_ratSub
      ((computable_ratRangeSum hv).comp Primrec.succ.to_comp) computable_invSucc
  have hBlim : Filter.Tendsto
      (fun n : ℕ => ((ratRangeSum v (n + 1) - invSucc n : ℚ) : ℝ)) Filter.atTop (nhds β) := by
    have hcast : (fun n : ℕ => ((ratRangeSum v (n + 1) - invSucc n : ℚ) : ℝ))
        = fun n : ℕ => (∑ i ∈ Finset.range (n + 1), ((v i : ℚ) : ℝ))
            - ((invSucc n : ℚ) : ℝ) := by
      funext n; simp only [Rat.cast_sub, hcastV]
    rw [hcast]
    have hshift : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), ((v i : ℚ) : ℝ))
        Filter.atTop (nhds β) := hβ.comp (Filter.tendsto_add_atTop_nat 1)
    simpa using hshift.sub tendsto_invSucc
  refine solovayDominates_of_approxPair hAc hBc (fun n => ?_) (fun n => ?_)
    (fun r hr => exists_rat_lt_of_tendsto hBlim hr)
  · have h1 := hUle (n + 1) (Nat.succ_pos n)
    have h2 : (0 : ℝ) < ((invSucc n : ℚ) : ℝ) := by exact_mod_cast invSucc_pos n
    simp only [Rat.cast_sub, hcastU]
    linarith
  · have h1 := hgapN (n + 1) (Nat.succ_pos n)
    simp only [Rat.cast_sub, hcastU, hcastV]
    linarith

/-- **SUV p. 159, "The reverse statement is also true".** If `α ≼₁ β` then one can
find computable series `∑ uᵢ = α` and `∑ vᵢ = β` with `0 ≤ uᵢ ≤ vᵢ` for `i > 0`. -/
theorem exists_series_of_solovayDominates {α β : ℝ}
    (hα : IsLowerSemicomputableReal α) (hβ : IsLowerSemicomputableReal β)
    (h : SolovayDominates α β) :
    ∃ u v : ℕ → ℚ, Computable u ∧ Computable v ∧
      (∀ i, 0 < i → 0 ≤ u i ∧ u i ≤ v i) ∧
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (u i : ℝ)) Filter.atTop (nhds α) ∧
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (v i : ℝ)) Filter.atTop (nhds β) := by
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hα
  obtain ⟨b⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hβ
  obtain ⟨f, hf, hspec⟩ := convergesBetter_of_solovayDominates a b h
  set A : ℕ → ℚ := ratRunMax (fun i => a.seq (f i)) with hAdef
  have hAc : Computable A := computable_ratRunMax (a.isComputable.comp hf)
  have hAmono : Monotone A := monotone_ratRunMax _
  have hAlt : ∀ i, ((A i : ℚ) : ℝ) < α :=
    fun i => ratRunMax_lt_real (fun k => a.seq_lt (f k)) i
  have hgapA : ∀ i, α - ((A i : ℚ) : ℝ) ≤ β - ((b.seq i : ℚ) : ℝ) := by
    intro i
    have h1 := hspec i
    have h2 : ((a.seq (f i) : ℚ) : ℝ) ≤ ((A i : ℚ) : ℝ) := by
      exact_mod_cast le_ratRunMax (fun i => a.seq (f i)) i
    linarith
  set v : ℕ → ℚ := increments b.seq with hvdef
  have hvc : Computable v := computable_increments b.isComputable
  have hvpos : ∀ i, 0 ≤ v (i + 1) := by
    intro i
    have hb := b.isStrictMono (Nat.lt_succ_self i)
    simp only [hvdef, increments_succ]
    linarith
  set A' : ℕ → ℚ := cappedApprox A v with hA'def
  have hA'c : Computable A' := computable_cappedApprox hAc hvc
  have hA'le : ∀ i, A' i ≤ A i := fun i => cappedApprox_le i
  have hA'mono : ∀ i, A' i ≤ A' (i + 1) := by
    intro i
    rw [hA'def, cappedApprox_succ]
    refine le_min (le_trans (hA'le i) (hAmono (Nat.le_succ i))) ?_
    linarith [hvpos i]
  have hgapA' : ∀ i, α - ((A' i : ℚ) : ℝ) ≤ β - ((b.seq i : ℚ) : ℝ) := by
    intro i
    induction i with
    | zero =>
        have h0 : A' 0 = A 0 := rfl
        rw [h0]
        exact hgapA 0
    | succ i ih =>
        have hstep : A' (i + 1) = min (A (i + 1)) (A' i + v (i + 1)) := rfl
        have hvi : ((v (i + 1) : ℚ) : ℝ)
            = ((b.seq (i + 1) : ℚ) : ℝ) - ((b.seq i : ℚ) : ℝ) := by
          simp only [hvdef, increments_succ]
          push_cast
          ring
        rcases min_cases (A (i + 1)) (A' i + v (i + 1)) with ⟨he, _⟩ | ⟨he, _⟩
        · rw [hstep, he]
          exact hgapA (i + 1)
        · rw [hstep, he]
          push_cast
          rw [hvi]
          linarith
  have hA'lim : Filter.Tendsto (fun i => ((A' i : ℚ) : ℝ)) Filter.atTop (nhds α) := by
    have hb0 : Filter.Tendsto (fun i => β - ((b.seq i : ℚ) : ℝ)) Filter.atTop (nhds 0) := by
      have hbb := b.tendsto.const_sub β
      simpa using hbb
    have hlow : ∀ i, (0 : ℝ) ≤ α - ((A' i : ℚ) : ℝ) := by
      intro i
      have h1 : ((A' i : ℚ) : ℝ) ≤ ((A i : ℚ) : ℝ) := by exact_mod_cast hA'le i
      have h2 := hAlt i
      linarith
    have h0 : Filter.Tendsto (fun i => α - ((A' i : ℚ) : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb0 hlow hgapA'
    have hconst : Filter.Tendsto (fun _ : ℕ => α) Filter.atTop (nhds α) := tendsto_const_nhds
    have h1 := hconst.sub h0
    have h2 : (fun i : ℕ => α - (α - ((A' i : ℚ) : ℝ))) = fun i => ((A' i : ℚ) : ℝ) := by
      funext i; ring
    rw [h2] at h1
    simpa using h1
  set u : ℕ → ℚ := increments A' with hudef
  have huc : Computable u := computable_increments hA'c
  have hcond : ∀ i, 0 < i → 0 ≤ u i ∧ u i ≤ v i := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    refine ⟨?_, ?_⟩
    · simp only [hudef, increments_succ]
      linarith [hA'mono j]
    · simp only [hudef, increments_succ]
      have hmin : A' (j + 1) ≤ A' j + v (j + 1) := by
        rw [hA'def, cappedApprox_succ]
        exact min_le_right _ _
      linarith
  have hsumu : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), ((u i : ℚ) : ℝ) = ((A' n : ℚ) : ℝ) := by
    intro n
    have hq : ∑ i ∈ Finset.range (n + 1), u i = A' n := by
      rw [hudef]; exact sum_range_increments A' n
    have hcast := congrArg (fun q : ℚ => ((q : ℚ) : ℝ)) hq
    push_cast at hcast
    exact hcast
  have hsumv : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), ((v i : ℚ) : ℝ)
      = ((b.seq n : ℚ) : ℝ) := by
    intro n
    have hq : ∑ i ∈ Finset.range (n + 1), v i = b.seq n := by
      rw [hvdef]; exact sum_range_increments b.seq n
    have hcast := congrArg (fun q : ℚ => ((q : ℚ) : ℝ)) hq
    push_cast at hcast
    exact hcast
  refine ⟨u, v, huc, hvc, hcond, ?_, ?_⟩
  · rw [← Filter.tendsto_add_atTop_iff_nat 1]
    exact Filter.Tendsto.congr (fun n => (hsumu n).symm) hA'lim
  · rw [← Filter.tendsto_add_atTop_iff_nat 1]
    exact Filter.Tendsto.congr (fun n => (hsumv n).symm) b.tendsto

/-- **SUV p. 159.** For a lower semicomputable but not computable `α` one has
`α ≼₁ 2α ≼₁ 3α ≼₁ ⋯`, and none of the reverse relations holds. -/
theorem solovayDominates_nsmul_succ {α : ℝ}
    (hα : IsLowerSemicomputableReal α) (hα' : ¬ ComputableReals.IsComputableReal α) (k : ℕ)
    (hk : 0 < k) :
    SolovayDominates ((k : ℝ) * α) (((k + 1 : ℕ) : ℝ) * α) ∧
      ¬ SolovayDominates (((k + 1 : ℕ) : ℝ) * α) ((k : ℝ) * α) := by
  have hcastk : ((((k : ℕ)) : ℚ) : ℝ) = ((k : ℕ) : ℝ) := by push_cast; ring
  have hcastk1 : ((((k + 1 : ℕ)) : ℚ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hlsck : IsLowerSemicomputableReal ((k : ℝ) * α) := by
    have h := hα.rat_mul (c := ((k : ℕ) : ℚ)) (by positivity)
    rwa [hcastk] at h
  have hlsck1 : IsLowerSemicomputableReal (((k + 1 : ℕ) : ℝ) * α) := by
    have h := hα.rat_mul (c := ((k + 1 : ℕ) : ℚ)) (by positivity)
    rwa [hcastk1] at h
  constructor
  · refine solovayDominates_of_isLowerSemicomputableReal_sub hlsck ?_
    have heq : ((k + 1 : ℕ) : ℝ) * α - (k : ℝ) * α = α := by push_cast; ring
    rw [heq]
    exact hα
  · intro hcon
    have hneg := isLowerSemicomputableReal_sub_of_solovayDominates
      hlsck1 hlsck hcon
    have heq : (k : ℝ) * α - ((k + 1 : ℕ) : ℝ) * α = -α := by push_cast; ring
    rw [heq] at hneg
    exact hα' (isComputableReal_of_lowerSemicomputable_neg hα hneg)

/-! ### Solovay reducibility (SUV p. 160) -/

/-- **SUV p. 160, "A convenient notation".** For a positive rational `c`,
`α ≼_c β` means `α ≼₁ cβ`. -/
def SolovayReducibleWith (c : ℚ) (α β : ℝ) : Prop := SolovayDominates α ((c : ℝ) * β)

/-- **SUV p. 160.** `α` is *Solovay reducible* to `β` (`α ≼ β`) if `α ≼₁ cβ` for
some positive integer `c > 0`. -/
def SolovayReducible (α β : ℝ) : Prop := ∃ c : ℕ, 0 < c ∧ SolovayDominates α ((c : ℝ) * β)

/-- **SUV p. 160.** The integer and the rational form of the constant define the
same relation. -/
theorem solovayReducible_iff_exists_rat {α β : ℝ} (hβ : IsLowerSemicomputableReal β) :
    SolovayReducible α β ↔ ∃ c : ℚ, 0 < c ∧ SolovayReducibleWith c α β := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨(c : ℚ), by exact_mod_cast hc, ?_⟩
    have hcast : (((c : ℕ) : ℚ) : ℝ) = ((c : ℕ) : ℝ) := by push_cast; ring
    have hgoal : SolovayDominates α ((((c : ℕ) : ℚ) : ℝ) * β) := by rw [hcast]; exact h
    exact hgoal
  · rintro ⟨c, hc, h⟩
    refine ⟨⌈c⌉₊, Nat.ceil_pos.2 hc, ?_⟩
    have hle : c ≤ ((⌈c⌉₊ : ℕ) : ℚ) := Nat.le_ceil c
    have hstep : SolovayDominates ((c : ℝ) * β) (((⌈c⌉₊ : ℕ) : ℝ) * β) := by
      refine solovayDominates_of_isLowerSemicomputableReal_sub
        (hβ.rat_mul hc.le) ?_
      have heq : ((⌈c⌉₊ : ℕ) : ℝ) * β - (c : ℝ) * β
          = ((((⌈c⌉₊ : ℕ) : ℚ) - c : ℚ) : ℝ) * β := by push_cast; ring
      rw [heq]
      exact hβ.rat_mul (by linarith)
    have h' : SolovayDominates α ((c : ℝ) * β) := h
    exact h'.trans hstep

/-- **SUV p. 160.** Solovay reducibility is reflexive. -/
theorem solovayReducible_refl {α : ℝ} (hα : IsLowerSemicomputableReal α) :
    SolovayReducible α α := by
  refine ⟨1, one_pos, ?_⟩
  simpa using solovayDominates_refl hα

/-- **SUV p. 160.** Solovay reducibility is transitive. -/
theorem SolovayReducible.trans {α β γ : ℝ}
    (hαβ : SolovayReducible α β) (hβγ : SolovayReducible β γ) : SolovayReducible α γ := by
  obtain ⟨c, hc, h1⟩ := hαβ
  obtain ⟨d, hd, h2⟩ := hβγ
  refine ⟨c * d, Nat.mul_pos hc hd, ?_⟩
  have hcq : (0 : ℚ) < ((c : ℕ) : ℚ) := by exact_mod_cast hc
  have h3 := SolovayDominates.rat_mul hcq h2
  have hcast1 : ((((c : ℕ) : ℚ)) : ℝ) = ((c : ℕ) : ℝ) := by push_cast; ring
  rw [hcast1] at h3
  have hcast2 : ((c : ℕ) : ℝ) * (((d : ℕ) : ℝ) * γ) = ((c * d : ℕ) : ℝ) * γ := by
    push_cast; ring
  rw [hcast2] at h3
  exact h1.trans h3

/-- **SUV p. 160.** A lower semicomputable real is *Solovay complete* if it is a
biggest element for the `≼`-preorder: every lower semicomputable real is Solovay
reducible to it. -/
def IsSolovayComplete (β : ℝ) : Prop :=
  IsLowerSemicomputableReal β ∧ ∀ α, IsLowerSemicomputableReal α → SolovayReducible α β

/-! ### Theorem 102 -/

/-- **SUV Theorem 102 (Section 5.7, p. 160), the form produced by the proof.** The
weighted sum `α = ∑ wᵢ αᵢ` of an enumeration of all lower semicomputable reals in
`[0,1]` with computable positive weights is a biggest element among the lower
semicomputable reals of `[0,1]`, with `αᵢ ≼_{1/wᵢ} α`. -/
theorem exists_isSolovayComplete_unitInterval :
    ∃ β : ℝ, β ∈ Set.Icc (0 : ℝ) 1 ∧ IsLowerSemicomputableReal β ∧
      ∀ α ∈ Set.Icc (0 : ℝ) 1, IsLowerSemicomputableReal α → SolovayReducible α β := by
  refine ⟨bigBeta, bigBeta_mem_Icc, ?_, ?_⟩
  · exact isLowerSemicomputableReal_of_series computable_bigU (fun i => bigU_nonneg i)
      tendsto_bigU
  · intro α hmem hα
    obtain ⟨e, he⟩ := exists_lscReal_eq hmem hα
    refine ⟨2 ^ (e + 1), by positivity, ?_⟩
    rw [← he]
    have hv : Computable (fun m => (2 ^ (e + 1) : ℚ) * bigU m) :=
      Computable₂.comp computable₂_ratMul (Computable.const ((2 : ℚ) ^ (e + 1))) computable_bigU
    have hvlim : Filter.Tendsto
        (fun n => ∑ m ∈ Finset.range n, (((2 ^ (e + 1) : ℚ) * bigU m : ℚ) : ℝ))
        Filter.atTop (nhds (((2 ^ (e + 1) : ℕ) : ℝ) * bigBeta)) := by
      have hfun : (fun n => ∑ m ∈ Finset.range n, (((2 ^ (e + 1) : ℚ) * bigU m : ℚ) : ℝ))
          = fun n => ((2 ^ (e + 1) : ℕ) : ℝ) * ∑ m ∈ Finset.range n, ((bigU m : ℚ) : ℝ) := by
        funext n
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        push_cast
        ring
      rw [hfun]
      exact tendsto_bigU.const_mul _
    have hvnn : ∀ m : ℕ, 0 ≤ (2 ^ (e + 1) : ℚ) * bigU m :=
      fun m => mul_nonneg (by positivity) (bigU_nonneg m)
    exact solovayDominates_of_series_le (computable_colU e) hv
      (fun i _ => colU_nonneg e i) (fun i _ => hvnn i)
      (fun i _ => colU_le_scaled e i) (tendsto_colU e) hvlim

/- The general form of Theorem 102 is *derived* from the construction-shaped form
above by the source's own rational shift and rescaling (p. 160: "randomness does not
change if we add a rational number or multiply by a positive rational factor").  Its
statement is unchanged; only its position in the file moved, so that it can appear
after the leaf it uses. -/

/-- There exists a biggest lower semicomputable real with respect to Solovay reducibility.  SUV
Theorem 102 (Section 5.7, p. 160). -/
theorem exists_isSolovayComplete : ∃ β : ℝ, IsSolovayComplete β := by
  obtain ⟨β, -, hlscβ, hdomβ⟩ := exists_isSolovayComplete_unitInterval
  have hnatcast : ∀ n : ℕ, (((n : ℕ) : ℚ) : ℝ) = ((n : ℕ) : ℝ) := fun n => by push_cast; ring
  have hlscmul : ∀ n : ℕ, IsLowerSemicomputableReal (((n : ℕ) : ℝ) * β) := by
    intro n
    have h := hlscβ.rat_mul (c := ((n : ℕ) : ℚ)) (by positivity)
    rwa [hnatcast n] at h
  refine ⟨β, hlscβ, fun α hα => ?_⟩
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hα
  have hqlt : ((a.seq 0 : ℚ) : ℝ) < α := a.seq_lt 0
  have hsub : IsLowerSemicomputableReal (α - ((a.seq 0 : ℚ) : ℝ)) := by
    have h := hα.add_rat (-(a.seq 0))
    have heq : α + ((-(a.seq 0) : ℚ) : ℝ) = α - ((a.seq 0 : ℚ) : ℝ) := by push_cast; ring
    rwa [heq] at h
  obtain ⟨N, hN⟩ := exists_nat_ge (α - ((a.seq 0 : ℚ) : ℝ))
  have hMpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hMq : (0 : ℚ) < (((N + 1 : ℕ) : ℚ))⁻¹ := by positivity
  have hα'lsc : IsLowerSemicomputableReal
      ((((((N + 1 : ℕ) : ℚ))⁻¹ : ℚ) : ℝ) * (α - ((a.seq 0 : ℚ) : ℝ))) :=
    hsub.rat_mul hMq.le
  have hcR : ((((((N + 1 : ℕ) : ℚ))⁻¹ : ℚ)) : ℝ) = (((N + 1 : ℕ) : ℝ))⁻¹ := by
    push_cast; ring
  have hmem01 : ((((((N + 1 : ℕ) : ℚ))⁻¹ : ℚ) : ℝ) * (α - ((a.seq 0 : ℚ) : ℝ)))
      ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hcR]
    have h0 : (0 : ℝ) ≤ α - ((a.seq 0 : ℚ) : ℝ) := by linarith
    have hle : α - ((a.seq 0 : ℚ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast at hN ⊢; linarith
    refine ⟨mul_nonneg (by positivity) h0, ?_⟩
    have hmul : (((N + 1 : ℕ) : ℝ))⁻¹ * (α - ((a.seq 0 : ℚ) : ℝ))
        ≤ (((N + 1 : ℕ) : ℝ))⁻¹ * ((N + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    rwa [inv_mul_cancel₀ (ne_of_gt hMpos)] at hmul
  obtain ⟨k, hk, hd⟩ := hdomβ _ hmem01 hα'lsc
  have hscaled := SolovayDominates.rat_mul (c := ((N + 1 : ℕ) : ℚ)) (by positivity) hd
  have hne : ((N : ℝ) + 1) ≠ 0 := by positivity
  have heq1 : ((((N + 1 : ℕ) : ℚ)) : ℝ) *
      ((((((N + 1 : ℕ) : ℚ))⁻¹ : ℚ) : ℝ) * (α - ((a.seq 0 : ℚ) : ℝ)))
      = α - ((a.seq 0 : ℚ) : ℝ) := by
    rw [hcR]
    push_cast
    field_simp
  have heq2 : ((((N + 1 : ℕ) : ℚ)) : ℝ) * (((k : ℕ) : ℝ) * β)
      = (((N + 1) * k : ℕ) : ℝ) * β := by push_cast; ring
  rw [heq1, heq2] at hscaled
  have hsublsc := isLowerSemicomputableReal_sub_of_solovayDominates
    hsub (hlscmul ((N + 1) * k)) hscaled
  have hfinal : IsLowerSemicomputableReal ((((N + 1) * k : ℕ) : ℝ) * β - α) := by
    have h := hsublsc.add_rat (-(a.seq 0))
    have heq : ((((N + 1) * k : ℕ) : ℝ) * β - (α - ((a.seq 0 : ℚ) : ℝ)))
        + ((-(a.seq 0) : ℚ) : ℝ) = (((N + 1) * k : ℕ) : ℝ) * β - α := by push_cast; ring
    rwa [heq] at h
  exact ⟨(N + 1) * k, Nat.mul_pos (Nat.succ_pos N) hk,
    solovayDominates_of_isLowerSemicomputableReal_sub hα hfinal⟩

/-- **SUV p. 160.** The *completeness deficiency* of `β` relative to a fixed Solovay
complete real `α`: the minimal `c` with `α ≼₁ cβ` (`⊤` when no such `c` exists). -/
noncomputable def completenessDeficiency (α β : ℝ) : ℝ≥0∞ :=
  sInf {c : ℝ≥0∞ | ∃ q : ℚ, 0 < q ∧ c = ENNReal.ofReal (q : ℝ) ∧ SolovayReducibleWith q α β}

/-- **SUV p. 160.** "The deficiency of `β` is finite if and only if `β` is Solovay
complete." -/
theorem completenessDeficiency_ne_top_iff {α β : ℝ} (hα : IsSolovayComplete α)
    (hβ : IsLowerSemicomputableReal β) :
    completenessDeficiency α β ≠ ⊤ ↔ IsSolovayComplete β := by
  constructor
  · intro h
    refine ⟨hβ, fun γ hγ => ?_⟩
    have hne : {c : ℝ≥0∞ | ∃ q : ℚ, 0 < q ∧ c = ENNReal.ofReal (q : ℝ) ∧
        SolovayReducibleWith q α β}.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [completenessDeficiency, hempty, sInf_empty] at h
      exact h rfl
    obtain ⟨_, q, hq, -, hred⟩ := hne
    exact (hα.2 γ hγ).trans ((solovayReducible_iff_exists_rat hβ).2 ⟨q, hq, hred⟩)
  · intro hcomp
    obtain ⟨c, hc, hd⟩ := hcomp.2 α hα.1
    have hcast : ((((c : ℕ) : ℚ)) : ℝ) = ((c : ℕ) : ℝ) := by push_cast; ring
    have hmem : ENNReal.ofReal ((((c : ℕ) : ℚ)) : ℝ) ∈ {x : ℝ≥0∞ | ∃ q : ℚ, 0 < q ∧
        x = ENNReal.ofReal (q : ℝ) ∧ SolovayReducibleWith q α β} := by
      refine ⟨((c : ℕ) : ℚ), by exact_mod_cast hc, rfl, ?_⟩
      have hgoal : SolovayDominates α ((((c : ℕ) : ℚ) : ℝ) * β) := by rw [hcast]; exact hd
      exact hgoal
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (sInf_le hmem)

/-- **SUV p. 160.** "The deficiency function depends on the choice of `α`, but is
still defined up to the `O(1)`-factor." -/
theorem completenessDeficiency_equiv_of_isSolovayComplete {α α' : ℝ}
    (hα : IsSolovayComplete α) (hα' : IsSolovayComplete α') :
    ∃ d : ℝ≥0∞, 0 < d ∧ d ≠ ⊤ ∧ ∀ β, IsLowerSemicomputableReal β →
      completenessDeficiency α β ≤ d * completenessDeficiency α' β ∧
      completenessDeficiency α' β ≤ d * completenessDeficiency α β := by
  have main : ∀ (x y : ℝ) (k : ℕ), 0 < k → SolovayDominates x (((k : ℕ) : ℝ) * y) →
      ∀ β, completenessDeficiency x β
        ≤ ENNReal.ofReal (((k : ℕ) : ℝ)) * completenessDeficiency y β := by
    intro x y k hk hkd β
    have hkR : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hk
    have ha0 : ENNReal.ofReal (((k : ℕ) : ℝ)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hkR
    have hatop : ENNReal.ofReal (((k : ℕ) : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hle : ∀ z ∈ {c : ℝ≥0∞ | ∃ q : ℚ, 0 < q ∧ c = ENNReal.ofReal (q : ℝ) ∧
        SolovayReducibleWith q y β}, completenessDeficiency x β
          ≤ ENNReal.ofReal (((k : ℕ) : ℝ)) * z := by
      rintro z ⟨q, hq, rfl, hred⟩
      have hq' : (0 : ℚ) < ((k : ℕ) : ℚ) * q := by
        have : (0 : ℚ) < ((k : ℕ) : ℚ) := by exact_mod_cast hk
        exact mul_pos this hq
      have hstep : SolovayDominates (((k : ℕ) : ℝ) * y) ((((k : ℕ) : ℚ) * q : ℚ) * β) := by
        have h := SolovayDominates.rat_mul (c := ((k : ℕ) : ℚ))
          (by exact_mod_cast hk) (show SolovayDominates y ((q : ℝ) * β) from hred)
        have heq1 : ((((k : ℕ) : ℚ)) : ℝ) * y = ((k : ℕ) : ℝ) * y := by push_cast; ring
        have heq2 : ((((k : ℕ) : ℚ)) : ℝ) * ((q : ℝ) * β)
            = ((((k : ℕ) : ℚ) * q : ℚ) : ℝ) * β := by push_cast; ring
        rwa [heq1, heq2] at h
      have hmem : ENNReal.ofReal (((((k : ℕ) : ℚ) * q : ℚ)) : ℝ)
          ∈ {c : ℝ≥0∞ | ∃ q' : ℚ, 0 < q' ∧ c = ENNReal.ofReal (q' : ℝ) ∧
            SolovayReducibleWith q' x β} := ⟨((k : ℕ) : ℚ) * q, hq', rfl, hkd.trans hstep⟩
      have hsplit : ENNReal.ofReal (((((k : ℕ) : ℚ) * q : ℚ)) : ℝ)
          = ENNReal.ofReal (((k : ℕ) : ℝ)) * ENNReal.ofReal ((q : ℚ) : ℝ) := by
        rw [← ENNReal.ofReal_mul hkR.le]
        congr 1
        push_cast
        ring
      rw [← hsplit]
      exact sInf_le hmem
    have hkey : ∀ z ∈ {c : ℝ≥0∞ | ∃ q : ℚ, 0 < q ∧ c = ENNReal.ofReal (q : ℝ) ∧
        SolovayReducibleWith q y β},
        (ENNReal.ofReal (((k : ℕ) : ℝ)))⁻¹ * completenessDeficiency x β ≤ z := by
      intro z hz
      calc (ENNReal.ofReal (((k : ℕ) : ℝ)))⁻¹ * completenessDeficiency x β
          ≤ (ENNReal.ofReal (((k : ℕ) : ℝ)))⁻¹
              * (ENNReal.ofReal (((k : ℕ) : ℝ)) * z) := by gcongr; exact hle z hz
        _ = z := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul]
    have hinf : (ENNReal.ofReal (((k : ℕ) : ℝ)))⁻¹ * completenessDeficiency x β
        ≤ completenessDeficiency y β := le_sInf hkey
    calc completenessDeficiency x β
        = ENNReal.ofReal (((k : ℕ) : ℝ))
            * ((ENNReal.ofReal (((k : ℕ) : ℝ)))⁻¹ * completenessDeficiency x β) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel ha0 hatop, one_mul]
      _ ≤ ENNReal.ofReal (((k : ℕ) : ℝ)) * completenessDeficiency y β := by gcongr
  obtain ⟨k, hk, hkd⟩ := hα'.2 α hα.1
  obtain ⟨k', hk', hkd'⟩ := hα.2 α' hα'.1
  refine ⟨ENNReal.ofReal ((k : ℕ) : ℝ) + ENNReal.ofReal ((k' : ℕ) : ℝ), ?_, ?_, fun β _ => ?_⟩
  · have hkR : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hk
    have h1 : 0 < ENNReal.ofReal (((k : ℕ) : ℝ)) := ENNReal.ofReal_pos.2 hkR
    exact lt_of_lt_of_le h1 le_self_add
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  · refine ⟨le_trans (main α α' k hk hkd β) ?_, le_trans (main α' α k' hk' hkd' β) ?_⟩
    · gcongr
      exact le_self_add
    · gcongr
      exact le_add_self

/-! ### Theorem 103 -/

/-- The sum of a maximal lower semicomputable semimeasure on `ℕ` is a Solovay complete lower
semicomputable real.  SUV Theorem 103 (Section 5.7, p. 160), "vice versa" direction. -/
theorem isSolovayComplete_of_isOmegaNumber {α : ℝ} (hα : IsOmegaNumber α) :
    IsSolovayComplete α := by
  obtain ⟨m, hm, rfl⟩ := hα
  have hΩ : IsLowerSemicomputableReal (omegaReal m) := isLowerSemicomputableReal_omegaReal hm
  refine ⟨hΩ, fun γ hγ => ?_⟩
  obtain ⟨K, hK, hlsc⟩ := exists_rat_isLowerSemicomputableReal_mul_omega_sub hm hγ
  refine (solovayReducible_iff_exists_rat hΩ).mpr ⟨K, hK, ?_⟩
  exact solovayDominates_of_isLowerSemicomputableReal_sub hγ hlsc

/-- Every Solovay complete lower semicomputable real in `(0,1)` is the sum of some maximal
(universal) semimeasure on `ℕ`, i.e. an `Ω`-number.  SUV Theorem 103 (Section 5.7, p. 160),
forward direction. -/
theorem isOmegaNumber_of_isSolovayComplete {α : ℝ}
    (hmem : α ∈ Set.Ioo (0 : ℝ) 1) (hα : IsSolovayComplete α) : IsOmegaNumber α := by
  obtain ⟨m, hm⟩ := exists_isUniversalSemimeasureNat
  have hΩlsc : IsLowerSemicomputableReal (omegaReal m) := isLowerSemicomputableReal_omegaReal hm
  obtain ⟨c, hc, hdom⟩ := hα.2 (omegaReal m) hΩlsc
  -- enlarge the constant so that `Ω ≤ C·α`
  obtain ⟨c', hc'⟩ := exists_nat_gt (omegaReal m / α)
  refine isOmegaNumber_of_scaled hm (c := max c c') (lt_of_lt_of_le hc (le_max_left _ _))
    hmem.2.le hmem.1.le ?_ ?_
  · have h1 : omegaReal m < ((c' : ℕ) : ℝ) * α := by
      rw [div_lt_iff₀ hmem.1] at hc'
      exact hc'
    have h2 : ((c' : ℕ) : ℝ) ≤ ((max c c' : ℕ) : ℝ) := by
      exact_mod_cast Nat.cast_le.mpr (le_max_right c c')
    nlinarith [hmem.1]
  · -- `C·α − Ω = (c·α − Ω) + (C − c)·α`
    have hcα : IsLowerSemicomputableReal (((c : ℕ) : ℝ) * α) := by
      have h := hα.1.rat_mul (c := ((c : ℕ) : ℚ)) (by positivity)
      have hcast : ((((c : ℕ) : ℚ)) : ℝ) = ((c : ℕ) : ℝ) := by push_cast; ring
      rwa [hcast] at h
    have h1 : IsLowerSemicomputableReal (((c : ℕ) : ℝ) * α - omegaReal m) :=
      isLowerSemicomputableReal_sub_of_solovayDominates hΩlsc hcα hdom
    have h2 : IsLowerSemicomputableReal ((((max c c' - c : ℕ)) : ℝ) * α) := by
      have h := hα.1.rat_mul (c := (((max c c' - c : ℕ)) : ℚ)) (by positivity)
      have hcast : (((((max c c' - c : ℕ)) : ℚ)) : ℝ) = (((max c c' - c : ℕ)) : ℝ) := by
        push_cast; ring
      rwa [hcast] at h
    have hsplit : ((max c c' : ℕ) : ℝ) * α - omegaReal m
        = (((c : ℕ) : ℝ) * α - omegaReal m) + (((max c c' - c : ℕ)) : ℝ) * α := by
      have hle : c ≤ max c c' := le_max_left c c'
      have hcast : ((max c c' - c : ℕ) : ℝ) = ((max c c' : ℕ) : ℝ) - ((c : ℕ) : ℝ) :=
        Nat.cast_sub hle
      rw [hcast]
      ring
    rw [hsplit]
    exact h1.add h2

/-- On `(0,1)`, the Solovay complete lower semicomputable reals are exactly the `Ω`-numbers.
SUV Theorem 103 (Section 5.7, p. 160). -/
theorem isSolovayComplete_iff_isOmegaNumber {α : ℝ}
    (hmem : α ∈ Set.Ioo (0 : ℝ) 1) : IsSolovayComplete α ↔ IsOmegaNumber α :=
  ⟨isOmegaNumber_of_isSolovayComplete hmem,
    isSolovayComplete_of_isOmegaNumber⟩

/-! ### Section 5.7.2: Solovay complete reals are random (SUV pp. 160–161) -/

/-- **SUV Section 5.7.2 (pp. 160–161).** Randomness is upward closed for `≼₁`: the
interval-transfer argument of Levin's footnote turns a cover of `β` into a cover of
`α` of the same or smaller total length. -/
theorem isMartinLofRandomReal_of_solovayDominates {α β : ℝ}
    (hα : IsLowerSemicomputableReal α) (hβ : IsLowerSemicomputableReal β)
    (h : SolovayDominates α β) (hrand : IsMartinLofRandomReal α) :
    IsMartinLofRandomReal β := by
  classical
  -- `hα`, `hβ` belong to the frozen statement; the transfer argument needs neither.
  have _ := hα
  have _ := hβ
  intro X hX hbetaX
  obtain ⟨p, hp, hpspec⟩ := h
  obtain ⟨E, hE, hEmono, hEspec⟩ := exists_stepEval_of_partrec hp
  obtain ⟨cover, hcov, hcspec⟩ := hX
  set nc : ℚ → ℕ → Option (ℚ × ℚ) := fun ε n =>
    (cover ε n.unpair.1).bind
      (fun I => (stepFirst E I.1 n.unpair.2).map (fun q => (q, q + (I.2 - I.1)))) with hnc
  have hncval : ∀ (ε : ℚ) (k s : ℕ), nc ε (Nat.pair k s)
      = (cover ε k).bind
        (fun I => (stepFirst E I.1 s).map (fun q => (q, q + (I.2 - I.1)))) := by
    intro ε k s
    rw [hnc]
    simp [Nat.unpair_pair]
  have hnccomp : Computable₂ nc := by
    rw [hnc]
    have hcov' : Computable (fun y : ℚ × ℕ => cover y.1 y.2) := hcov
    have hu1 : Computable (fun n : ℕ => n.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
    have hu2 : Computable (fun n : ℕ => n.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
    have hk : Computable (fun x : ℚ × ℕ => cover x.1 x.2.unpair.1) :=
      hcov'.comp (Computable.pair Computable.fst (hu1.comp Computable.snd))
    have hgg : Computable (fun y : (ℚ × ℕ) × (ℚ × ℚ) => ((y.2.1, y.1.2.unpair.2) : ℚ × ℕ)) :=
      Computable.pair (Computable.fst.comp Computable.snd)
        (hu2.comp (Computable.snd.comp Computable.fst))
    have hsf := (computable_stepFirst hE).comp hgg
    have hpairmap : Computable₂ (fun (y : (ℚ × ℕ) × (ℚ × ℚ)) (q : ℚ) =>
        ((q, q + (y.2.2 - y.2.1)) : ℚ × ℚ)) := by
      have h1 : Computable (fun z : ((ℚ × ℕ) × (ℚ × ℚ)) × ℚ => z.2) := Computable.snd
      have h2 : Computable (fun z : ((ℚ × ℕ) × (ℚ × ℚ)) × ℚ =>
          z.2 + (z.1.2.2 - z.1.2.1)) :=
        Computable₂.comp computable₂_ratAdd h1
          (Computable₂.comp computable₂_ratSub
            (Computable.snd.comp (Computable.snd.comp Computable.fst))
            (Computable.fst.comp (Computable.snd.comp Computable.fst)))
      exact Computable.pair h1 h2
    exact Computable.option_bind hk (Computable.option_map hsf hpairmap)
  refine hrand {α} ⟨nc, hnccomp, ?_⟩ rfl
  intro ε hε
  obtain ⟨hsub, hlen⟩ := hcspec ε hε
  constructor
  · rintro y hy
    have hyα : y = α := hy
    rw [hyα]
    have hβmem := hsub hbetaX
    rw [Set.mem_iUnion] at hβmem
    obtain ⟨k, hk⟩ := hβmem
    rcases hcase : cover ε k with _ | I
    · rw [hcase] at hk; simp at hk
    · rw [hcase] at hk
      have hkI : ((I.1 : ℚ) : ℝ) < β ∧ β < ((I.2 : ℚ) : ℝ) := hk
      obtain ⟨q, hq, hqlt, hqgap⟩ := hpspec I.1 hkI.1
      obtain ⟨s0, hs0⟩ := exists_stepFirst hEmono ((hEspec I.1 q).mp hq)
      rw [Set.mem_iUnion]
      refine ⟨Nat.pair k s0, ?_⟩
      rw [hncval ε k s0, hcase]
      change α ∈ ((stepFirst E I.1 s0).map
        (fun q => (q, q + (I.2 - I.1)))).elim ∅ ratInterval
      rw [hs0]
      change α ∈ Set.Ioo ((q : ℚ) : ℝ) (((q + (I.2 - I.1) : ℚ)) : ℝ)
      refine Set.mem_Ioo.mpr ⟨hqlt, ?_⟩
      have h2 := hkI.2
      push_cast
      linarith
  · have hval : ∀ (k s : ℕ) (I : ℚ × ℚ), cover ε k = some I →
        (nc ε (Nat.pair k s)).elim (0 : ℝ≥0∞) ratIntervalLength
          = (stepFirst E I.1 s).elim 0 (fun _ => ratIntervalLength I) := by
      intro k s I hcase
      rw [hncval ε k s, hcase]
      change ((stepFirst E I.1 s).map (fun q => (q, q + (I.2 - I.1)))).elim 0 ratIntervalLength
          = (stepFirst E I.1 s).elim 0 (fun _ => ratIntervalLength I)
      rcases hsf : stepFirst E I.1 s with _ | q
      · rfl
      · change ratIntervalLength (q, q + (I.2 - I.1)) = ratIntervalLength I
        simp only [ratIntervalLength]
        congr 1
        push_cast
        ring
    have hstep : ∀ k : ℕ, (∑' s : ℕ, (nc ε (Nat.pair k s)).elim 0 ratIntervalLength)
        ≤ (cover ε k).elim 0 ratIntervalLength := by
      intro k
      rcases hcase : cover ε k with _ | I
      · have hz : ∀ s : ℕ, (nc ε (Nat.pair k s)).elim (0 : ℝ≥0∞) ratIntervalLength = 0 := by
          intro s; rw [hncval ε k s, hcase]; rfl
        simp [hz]
      · by_cases hex : ∃ s, (stepFirst E I.1 s).isSome = true
        · obtain ⟨s0, hs0⟩ := hex
          obtain ⟨q0, hq0⟩ := Option.isSome_iff_exists.mp hs0
          have huniq : ∀ s, s ≠ s0 →
              (nc ε (Nat.pair k s)).elim (0 : ℝ≥0∞) ratIntervalLength = 0 := by
            intro s hs
            rw [hval k s I hcase]
            rcases hsf : stepFirst E I.1 s with _ | q
            · rfl
            · exact absurd (stepFirst_unique hEmono hsf hq0) hs
          rw [tsum_eq_single s0 huniq, hval k s0 I hcase, hq0]
          exact le_rfl
        · push Not at hex
          have hz : ∀ s : ℕ, (nc ε (Nat.pair k s)).elim (0 : ℝ≥0∞) ratIntervalLength = 0 := by
            intro s
            rw [hval k s I hcase]
            rcases hsf : stepFirst E I.1 s with _ | q
            · rfl
            · exact absurd (by simp [hsf] : (stepFirst E I.1 s).isSome = true) (hex s)
          simp [hz]
    calc (∑' n : ℕ, (nc ε n).elim 0 ratIntervalLength)
        = ∑' x : ℕ × ℕ, (nc ε (Nat.pair x.1 x.2)).elim 0 ratIntervalLength := by
          rw [← Equiv.tsum_eq Nat.pairEquiv
            (fun n => (nc ε n).elim (0 : ℝ≥0∞) ratIntervalLength)]
          rfl
      _ = ∑' k : ℕ, ∑' s : ℕ, (nc ε (Nat.pair k s)).elim 0 ratIntervalLength :=
          ENNReal.tsum_prod (f := fun k s => (nc ε (Nat.pair k s)).elim 0 ratIntervalLength)
      _ ≤ ∑' k : ℕ, (cover ε k).elim 0 ratIntervalLength := ENNReal.tsum_le_tsum hstep
      _ ≤ ENNReal.ofReal (ε : ℝ) := hlen

/-- **SUV Section 5.7.2 (pp. 160–161).** Randomness is upward closed for Solovay
reducibility: if `α ≼ β` and `α` is random, then `β` is random. -/
theorem isMartinLofRandomReal_of_solovayReducible {α β : ℝ}
    (hα : IsLowerSemicomputableReal α) (hβ : IsLowerSemicomputableReal β)
    (h : SolovayReducible α β) (hrand : IsMartinLofRandomReal α) :
    IsMartinLofRandomReal β := by
  obtain ⟨c, hc, hd⟩ := h
  have hcq : (0 : ℚ) < ((c : ℕ) : ℚ) := by exact_mod_cast hc
  have hcast : ((((c : ℕ) : ℚ)) : ℝ) = ((c : ℕ) : ℝ) := by push_cast; ring
  have hcβ : IsLowerSemicomputableReal (((c : ℕ) : ℝ) * β) := by
    have := hβ.rat_mul hcq.le
    rwa [hcast] at this
  have hr2 : IsMartinLofRandomReal (((c : ℕ) : ℝ) * β) :=
    isMartinLofRandomReal_of_solovayDominates hα hcβ hd hrand
  rw [← hcast] at hr2
  exact (isMartinLofRandomReal_rat_mul hcq β).1 hr2

/-- Solovay complete lower semicomputable reals are ML-random.  SUV Section 5.7.2 (p. 161). -/
theorem isMartinLofRandomReal_of_isSolovayComplete {β : ℝ} (h : IsSolovayComplete β) :
    IsMartinLofRandomReal β := by
  obtain ⟨x, hxlsc, hxrand⟩ := exists_isLowerSemicomputableReal_isMartinLofRandomReal
  exact isMartinLofRandomReal_of_solovayReducible hxlsc h.1 (h.2 x hxlsc) hxrand

/-- **SUV Theorem 100 (Section 5.7, p. 157), real-number form.**  Every `Ω`-number is an
ML-random real.

This is the content of the frozen leaf `isMartinLofRandomReal_omegaReal` of
`Omega/Basic.lean`, proved here rather than there because the source's own §5.7.2 route
— `Ω` is Solovay complete (Theorem 103) and randomness is upward closed for Solovay
reducibility, applied to the lower semicomputable random real of Problem 86 — uses
vocabulary (`SolovayReducible`, Theorem 101) that is defined in *this* file, which
imports `Basic.lean`. -/
theorem isMartinLofRandomReal_omegaReal {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) :
    IsMartinLofRandomReal (omegaReal m) :=
  isMartinLofRandomReal_of_isSolovayComplete
    (isSolovayComplete_of_isOmegaNumber ⟨m, hm, rfl⟩)

/-! ### Theorem 100, moved here from `Omega/Basic.lean`

The four statements below live here rather than at the end of `Omega/Basic.lean`
because the §5.7.2 route to Theorem 100 uses `SolovayReducible` and Theorem 101,
which are defined in *this* file; the last three consume Theorem 100.  Nothing in
`Omega/Basic.lean` uses any of the four. -/

/-- **SUV p. 160** (presupposed by Theorems 102–103): the sum of a maximal lower
semicomputable semimeasure is strictly *less* than `1`.

This is **not** a consequence of the semimeasure axioms alone, which only give
`∑ₙ m n ≤ 1` (`omegaReal_le_one`); it is an extra fact about *maximal* semimeasures,
and the audit (item 1) correctly refused to let it hide inside `Set.Ioo`. -/
theorem omegaReal_lt_one {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) :
    omegaReal m < 1 := by
  refine lt_of_le_of_ne (omegaReal_le_one hm) ?_
  have hne := ne_ratCast_of_isMartinLofRandomReal
    (isMartinLofRandomReal_omegaReal hm) 1
  simpa using hne

/-- **SUV p. 160** (presupposed by Theorem 103): the sum of a maximal lower
semicomputable semimeasure lies strictly between `0` and `1`.  Derived from the two
explicit leaves `omegaReal_pos` and `omegaReal_lt_one`. -/
theorem omegaReal_mem_Ioo {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) :
    omegaReal m ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨omegaReal_pos hm, omegaReal_lt_one hm⟩

end Kolmogorov
