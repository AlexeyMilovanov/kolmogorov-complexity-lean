/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.PredictCover
import KolmogorovMathlib.MonotoneComplexity.Omega.DisjointCover

/-!
# The multiply covered set (Solovay's criterion for reals, SUV Theorem 106, p. 162)

The reverse direction of SUV Theorem 106 is the constructive Borel–Cantelli lemma: from
`∑ hᵢ < ∞` and `α ≤ aᵢ + hᵢ` for infinitely many `i` one has to produce, for every
rational `ε > 0`, a cover of `α` of total length at most `ε`.  The hypothesis gives no
*effective* tail bound, so the cover cannot be a tail of the family; it has to be the set
of reals covered **at least `m` times**, whose measure is at most `(∑ hᵢ)/m`.

Two things are needed and are supplied here.

* `measure_le_of_multiplicity` — the Markov bound: if every point of `A` lies in at least
  `m` of the `Jᵢ`, then `m · volume A ≤ ∑ᵢ volume Jᵢ`.
* `topRat` — the `k`-th largest of `b 0, …, b (j-1)`, written as a *nested pair of
  parameterised loops* (a bounded count inside a bounded maximum) so that it is computable
  in `(k, j)` jointly, with no doubly recursive definition.  Its point is
  `topRat_lt_iff`: `x < topRat b c₀ k j` iff at least `k` of `b 0, …, b (j-1)` exceed `x`.

Together with `Omega/DisjointCover.lean` these turn the multiply covered set of a family
with *non-decreasing left endpoints* into an effectively null set.  No statement of the
source is rendered in this file.
-/

namespace Kolmogorov

open ENNReal MeasureTheory

/-! ### The Markov bound -/

/-- If every point of `A` lies in at least `m` of the sets `J i`, then
`m · volume A ≤ ∑ᵢ volume (J i)`. -/
theorem measure_le_of_multiplicity {J : ℕ → Set ℝ} (hJ : ∀ i, MeasurableSet (J i))
    {A : Set ℝ} (hA : MeasurableSet A) {m : ℕ}
    (hmult : ∀ x ∈ A, ∃ F : Finset ℕ, m ≤ F.card ∧ ∀ i ∈ F, x ∈ J i) :
    (m : ℝ≥0∞) * volume A ≤ ∑' i, volume (J i) := by
  classical
  have hfmeas : ∀ i, Measurable ((J i).indicator (fun _ => (1 : ℝ≥0∞))) :=
    fun i => measurable_const.indicator (hJ i)
  have hint : (∫⁻ x, ∑' i, (J i).indicator (fun _ => (1 : ℝ≥0∞)) x)
      = ∑' i, volume (J i) := by
    rw [MeasureTheory.lintegral_tsum (fun i => (hfmeas i).aemeasurable)]
    refine tsum_congr (fun i => ?_)
    rw [MeasureTheory.lintegral_indicator_const (hJ i) 1, one_mul]
  have hle : A.indicator (fun _ => (m : ℝ≥0∞))
      ≤ fun x => ∑' i, (J i).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      obtain ⟨F, hFcard, hF⟩ := hmult x hx
      have h1 : ∑ i ∈ F, (J i).indicator (fun _ => (1 : ℝ≥0∞)) x = (F.card : ℝ≥0∞) := by
        rw [Finset.sum_congr rfl (fun i hi => Set.indicator_of_mem (hF i hi) _)]
        simp
      have h2 : (m : ℝ≥0∞) ≤ (F.card : ℝ≥0∞) := by exact_mod_cast hFcard
      refine le_trans h2 (le_trans (le_of_eq h1.symm) ?_)
      exact ENNReal.sum_le_tsum F
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc (m : ℝ≥0∞) * volume A
      = ∫⁻ x, A.indicator (fun _ => (m : ℝ≥0∞)) x :=
        (MeasureTheory.lintegral_indicator_const hA _).symm
    _ ≤ ∫⁻ x, ∑' i, (J i).indicator (fun _ => (1 : ℝ≥0∞)) x := lintegral_mono hle
    _ = ∑' i, volume (J i) := hint

/-! ### A parameterised bounded maximum -/

variable {σ : Type}

/-- `max c₀ (u p 0) … (u p (n-1))`, in the shape `Computable.nat_rec` accepts, with `p` as
the recursion parameter (so that the *diagonal* use, where the bound depends on `p`, is
computable). -/
def ratRangeMaxP (u : σ → ℕ → ℚ) (c₀ : ℚ) (p : σ) : ℕ → ℚ
  | 0 => c₀
  | n + 1 => max (ratRangeMaxP u c₀ p n) (u p n)

/-- The running maximum is at least its floor `c₀`. -/
theorem le_ratRangeMaxP (u : σ → ℕ → ℚ) (c₀ : ℚ) (p : σ) (n : ℕ) :
    c₀ ≤ ratRangeMaxP u c₀ p n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact le_trans ih (le_max_left _ _)

/-- Every entry below the bound is at most the running maximum. -/
theorem le_ratRangeMaxP_of_lt (u : σ → ℕ → ℚ) (c₀ : ℚ) (p : σ) :
    ∀ (n i : ℕ), i < n → u p i ≤ ratRangeMaxP u c₀ p n := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact le_trans (ih i h) (le_max_left _ _)
      · rw [h]
        exact le_max_right _ _

/-- The bounded maximum is attained, either at `c₀` or at one of the entries. -/
theorem ratRangeMaxP_cases (u : σ → ℕ → ℚ) (c₀ : ℚ) (p : σ) :
    ∀ n : ℕ, ratRangeMaxP u c₀ p n = c₀ ∨ ∃ i, i < n ∧ ratRangeMaxP u c₀ p n = u p i := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      rcases max_cases (ratRangeMaxP u c₀ p n) (u p n) with ⟨he, _⟩ | ⟨he, _⟩
      · rcases ih with h | ⟨i, hi, hval⟩
        · exact Or.inl (by rw [ratRangeMaxP, he, h])
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, by rw [ratRangeMaxP, he, hval]⟩
      · exact Or.inr ⟨n, Nat.lt_succ_self n, by rw [ratRangeMaxP, he]⟩

/-- The parameterised running maximum of a computable family is computable. -/
theorem computable_ratRangeMaxP [Primcodable σ] {u : σ → ℕ → ℚ} (c₀ : ℚ)
    (hu : Computable₂ u) : Computable (fun q : σ × ℕ => ratRangeMaxP u c₀ q.1 q.2) := by
  have hstep : Computable₂ (fun (q : σ × ℕ) (r : ℕ × ℚ) => max r.2 (u q.1 r.1)) := by
    have h1 : Computable (fun s : (σ × ℕ) × ℕ × ℚ => s.2.2) :=
      Computable.snd.comp Computable.snd
    have h2 : Computable (fun s : (σ × ℕ) × ℕ × ℚ => u s.1.1 s.2.1) :=
      hu.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
    exact Computable₂.comp computable₂_ratMax h1 h2
  have hrec := Computable.nat_rec (σ := ℚ) Computable.snd (Computable.const c₀) hstep
  refine hrec.of_eq (fun q => ?_)
  obtain ⟨p, n⟩ := q
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) c₀
      (fun y IH => max IH (u p y)) m) = ratRangeMaxP u c₀ p m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [ratRangeMaxP]; rw [ih]
  exact key n

/-! ### The `k`-th largest entry of an initial segment -/

/-- The number of `i' < j` with `b i ≤ b i'`, as a rational. -/
def cntGE (b : ℕ → ℚ) (i : ℕ) (j : ℕ) : ℚ :=
  ratRangeSumP (fun (i : ℕ) (i' : ℕ) => cond (ratLtPair (b i', b i)) (0 : ℚ) 1) i j

/-- The counting function counts the entries below `j` that are at least `b i`. -/
theorem cntGE_eq (b : ℕ → ℚ) (i j : ℕ) :
    cntGE b i j = (((Finset.range j).filter (fun i' => b i ≤ b i')).card : ℚ) := by
  rw [cntGE, ratRangeSumP_eq]
  have hterm : ∀ i' ∈ Finset.range j,
      cond (ratLtPair (b i', b i)) (0 : ℚ) 1 = if b i ≤ b i' then (1 : ℚ) else 0 := by
    intro i' _
    rcases hlt : ratLtPair (b i', b i) with _ | _
    · have hle : b i ≤ b i' := by
        rw [ratLtPair] at hlt
        exact not_lt.1 (of_decide_eq_false hlt)
      rw [Bool.cond_false, ite_eq_left hle]
    · have hnle : ¬ (b i ≤ b i') := by
        rw [ratLtPair] at hlt
        exact not_le.2 (of_decide_eq_true hlt)
      rw [Bool.cond_true, ite_eq_right hnle]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]

/-- The counting function of a computable sequence is computable. -/
theorem computable_cntGE {b : ℕ → ℚ} (hb : Computable b) :
    Computable (fun q : ℕ × ℕ => cntGE b q.1 q.2) := by
  have hbi' : Computable (fun s : ℕ × ℕ => b s.2) := hb.comp Computable.snd
  have hbi : Computable (fun s : ℕ × ℕ => b s.1) := hb.comp Computable.fst
  have hb2 := computable_ratLtPair.comp (Computable.pair hbi' hbi)
  have hu : Computable₂ (fun (i : ℕ) (i' : ℕ) => cond (ratLtPair (b i', b i)) (0 : ℚ) 1) :=
    Computable.cond hb2 (Computable.const (0 : ℚ)) (Computable.const (1 : ℚ))
  exact computable_ratRangeSumP hu

attribute [irreducible] cntGE

/-- The value of `b i`, kept only if at least `q.1` of the first `q.2` entries are
`≥ b i`. -/
def topCand (b : ℕ → ℚ) (c₀ : ℚ) (q : ℕ × ℕ) (i : ℕ) : ℚ :=
  cond (ratLtPair (cntGE b i q.2, (q.1 : ℚ))) c₀ (b i)

/-- A candidate is either the floor `c₀`, when too few entries dominate it, or the entry itself. -/
theorem topCand_cases (b : ℕ → ℚ) (c₀ : ℚ) (q : ℕ × ℕ) (i : ℕ) :
    (topCand b c₀ q i = c₀ ∧ cntGE b i q.2 < (q.1 : ℚ)) ∨
      (topCand b c₀ q i = b i ∧ (q.1 : ℚ) ≤ cntGE b i q.2) := by
  rcases hlt : ratLtPair (cntGE b i q.2, (q.1 : ℚ)) with _ | _
  · refine Or.inr ⟨by rw [topCand, hlt, Bool.cond_false], ?_⟩
    rw [ratLtPair] at hlt
    exact not_lt.1 (of_decide_eq_false hlt)
  · refine Or.inl ⟨by rw [topCand, hlt, Bool.cond_true], ?_⟩
    rw [ratLtPair] at hlt
    exact of_decide_eq_true hlt

/-- The candidate function of a computable sequence is computable. -/
theorem computable_topCand {b : ℕ → ℚ} (hb : Computable b) (c₀ : ℚ) :
    Computable₂ (topCand b c₀) := by
  have hcnt := computable_cntGE hb
  have hpair : Computable (fun s : (ℕ × ℕ) × ℕ => (s.2, s.1.2)) :=
    Computable.snd.pair (Computable.snd.comp Computable.fst)
  have h1 := hcnt.comp hpair
  have hk : Computable (fun s : (ℕ × ℕ) × ℕ => s.1.1) := Computable.fst.comp Computable.fst
  have h2 := computable_nat_to_rat.comp hk
  have h3 := computable_ratLtPair.comp (Computable.pair h1 h2)
  have h4 := hb.comp (Computable.snd : Computable (fun s : (ℕ × ℕ) × ℕ => s.2))
  have h5 := Computable.cond h3 (Computable.const c₀) h4
  exact h5.of_eq (fun s => rfl)

attribute [irreducible] topCand

/-- The `k`-th largest of `b 0, …, b (j-1)`, floored at `c₀`. -/
def topRat (b : ℕ → ℚ) (c₀ : ℚ) (k j : ℕ) : ℚ :=
  ratRangeMaxP (topCand b c₀) c₀ (k, j) j

/-- The `k`-th largest entry is at least the floor `c₀`. -/
theorem le_topRat (b : ℕ → ℚ) (c₀ : ℚ) (k j : ℕ) : c₀ ≤ topRat b c₀ k j :=
  le_ratRangeMaxP _ _ _ _

/-- If `x` is below the `k`-th largest entry, then at least `k` entries exceed `x`. -/
theorem exists_finset_of_lt_topRat {b : ℕ → ℚ} {c₀ : ℚ} {k j : ℕ} {x : ℝ}
    (hc₀ : ((c₀ : ℚ) : ℝ) ≤ x) (h : x < ((topRat b c₀ k j : ℚ) : ℝ)) :
    ∃ F : Finset ℕ, k ≤ F.card ∧ ∀ i ∈ F, i < j ∧ x < ((b i : ℚ) : ℝ) := by
  rcases ratRangeMaxP_cases (topCand b c₀) c₀ (k, j) j with hc | ⟨i, hij, hval⟩
  · rw [topRat, hc] at h
    exact absurd hc₀ (not_le.2 h)
  · rw [topRat, hval] at h
    rcases topCand_cases b c₀ (k, j) i with ⟨heq, _⟩ | ⟨heq, hcnt⟩
    · rw [heq] at h
      exact absurd hc₀ (not_le.2 h)
    · rw [heq] at h
      refine ⟨(Finset.range j).filter (fun i' => b i ≤ b i'), ?_, ?_⟩
      · have hcnt' : ((k : ℕ) : ℚ)
            ≤ ((((Finset.range j).filter (fun i' => b i ≤ b i')).card : ℕ) : ℚ) := by
          rw [← cntGE_eq]
          exact hcnt
        exact_mod_cast hcnt'
      · intro i' hi'
        rw [Finset.mem_filter, Finset.mem_range] at hi'
        refine ⟨hi'.1, lt_of_lt_of_le h ?_⟩
        exact_mod_cast hi'.2

/-- If at least `k` of the first `j` entries exceed `x`, then so does the `k`-th
largest. -/
theorem lt_topRat {b : ℕ → ℚ} {c₀ : ℚ} {k j : ℕ} {x : ℝ} {F : Finset ℕ}
    (hne : F.Nonempty) (hk : k ≤ F.card) (hF : ∀ i ∈ F, i < j ∧ x < ((b i : ℚ) : ℝ)) :
    x < ((topRat b c₀ k j : ℚ) : ℝ) := by
  obtain ⟨i₀, hi₀F, hi₀min⟩ := F.exists_min_image b hne
  have hsub : F ⊆ (Finset.range j).filter (fun i' => b i₀ ≤ b i') := by
    intro i' hi'
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨(hF i' hi').1, hi₀min i' hi'⟩
  have hcard : ((k : ℕ) : ℚ) ≤ cntGE b i₀ j := by
    rw [cntGE_eq]
    have h1 : F.card ≤ ((Finset.range j).filter (fun i' => b i₀ ≤ b i')).card :=
      Finset.card_le_card hsub
    have h2 : k ≤ ((Finset.range j).filter (fun i' => b i₀ ≤ b i')).card := le_trans hk h1
    exact_mod_cast h2
  have hcand : topCand b c₀ (k, j) i₀ = b i₀ := by
    rcases topCand_cases b c₀ (k, j) i₀ with ⟨_, hlt⟩ | ⟨heq, _⟩
    · exact absurd hcard (not_le.2 hlt)
    · exact heq
  have hle : b i₀ ≤ topRat b c₀ k j := by
    rw [topRat, ← hcand]
    exact le_ratRangeMaxP_of_lt (topCand b c₀) c₀ (k, j) j i₀ (hF i₀ hi₀F).1
  have hleR : ((b i₀ : ℚ) : ℝ) ≤ ((topRat b c₀ k j : ℚ) : ℝ) := by exact_mod_cast hle
  exact lt_of_lt_of_le (hF i₀ hi₀F).2 hleR

/-- The `k`-th largest of the first `j` entries of a computable sequence is computable. -/
theorem computable_topRat {b : ℕ → ℚ} (hb : Computable b) (c₀ : ℚ) :
    Computable₂ (topRat b c₀) := by
  have hmax := computable_ratRangeMaxP (σ := ℕ × ℕ) c₀ (computable_topCand hb c₀)
  have hre : Computable (fun q : ℕ × ℕ => ((q.1, q.2), q.2)) :=
    (Computable.fst.pair Computable.snd).pair Computable.snd
  have hfin := hmax.comp hre
  exact hfin.of_eq (fun q => rfl)

end Kolmogorov
