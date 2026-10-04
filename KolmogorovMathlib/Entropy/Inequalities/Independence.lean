import KolmogorovMathlib.Entropy.Inequalities.Basic

/-!
# Independence and the basic inequality

SUV Sections 7.2.3–7.2.4 (Theorems 144–145, Problems 221–222), pp. 221–223.

The entropy criterion for independence of two random variables (Theorem 144) and of a finite
family (`independentFamily_iff_entropy_eq_sum`), and the basic inequality `I(ξ:η|α) ≥ 0`
(Theorem 145) in its equivalent forms.
-/

namespace Kolmogorov

open Finset

variable {Ω : Type*} [Fintype Ω] {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ### Theorem 144: independence -/

/-- **The entropy criterion for independence**: `ξ` and `η` are independent if and only if
`H(⟨ξ, η⟩) = H(ξ) + H(η)`.  SUV Theorem 144, p. 221. -/
theorem independent_iff_entropy_pairRV_eq_add (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    Independent μ X Y ↔ entropy μ (pairRV X Y) = entropy μ X + entropy μ Y := by
  constructor
  · intro h
    rw [entropy_pairRV_eq_sum_sum]
    unfold Independent at h
    simp_rw [h, negMulLog2_mul]
    calc ∑ b ∈ rangeFinset Y, ∑ a ∈ rangeFinset X,
          (μ.dist Y b * negMulLog2 (μ.dist X a) + μ.dist X a * negMulLog2 (μ.dist Y b))
        = ∑ b ∈ rangeFinset Y, (μ.dist Y b * entropy μ X + negMulLog2 (μ.dist Y b)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, μ.sum_dist_eq_one,
            one_mul]
          rfl
      _ = entropy μ X + entropy μ Y := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, μ.sum_dist_eq_one, one_mul]
          rfl
  · intro h
    have hc : condEntropy μ X Y = entropy μ X := by
      have := entropy_pairRV_eq_add_condEntropy μ X Y
      linarith
    rw [condEntropy_eq_sum_sum, Finset.sum_comm, entropy] at hc
    have hterm := (Finset.sum_eq_sum_iff_of_le
      fun a _ => sum_dist_mul_negMulLog2_condDist_le μ X Y a).1 hc
    intro a b
    by_cases hb : b ∈ rangeFinset Y
    · by_cases ha : a ∈ rangeFinset X
      · rcases (μ.dist_nonneg Y b).lt_or_eq with hq | hq
        · have h1 := hterm a ha
          rw [← μ.sum_dist_mul_condDist_fiber X Y a] at h1
          have h2 := eq_sum_of_sum_mul_negMulLog2_eq _ _ _ (fun b _ => μ.dist_nonneg Y b)
            (μ.sum_dist_eq_one Y) (fun b _ => div_nonneg (μ.dist_nonneg _ _) (μ.dist_nonneg _ _))
            h1 b hb hq.ne'
          rw [μ.sum_dist_mul_condDist_fiber X Y a] at h2
          rw [← mul_div_cancel₀ (μ.dist (pairRV X Y) (a, b)) hq.ne', h2, mul_comm]
        · rw [μ.dist_pairRV_eq_zero_of_snd X Y a hq.symm, ← hq, mul_zero]
      · have h0 : (a, b) ∉ rangeFinset (pairRV X Y) := fun hab => by
          obtain ⟨ω, hω⟩ := mem_rangeFinset.1 hab
          exact ha (mem_rangeFinset.2 ⟨ω, congrArg Prod.fst hω⟩)
        rw [μ.dist_eq_zero_of_not_mem_range h0, μ.dist_eq_zero_of_not_mem_range ha, zero_mul]
    · rw [μ.dist_eq_zero_of_not_mem_range hb, mul_zero]
      exact μ.dist_pairRV_eq_zero_of_snd X Y a (μ.dist_eq_zero_of_not_mem_range hb)

/-- **The conditional form of the independence criterion**: `ξ` and `η` are independent if and
only if `H(ξ|η) = H(ξ)`.  This is the form the book obtains from Theorem 144 through
Theorem 142, and proving it from Theorem 142 is the content of the problem.
SUV Problem 221, p. 222. -/
theorem independent_iff_condEntropy_eq_entropy (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    Independent μ X Y ↔ condEntropy μ X Y = entropy μ X := by
  rw [independent_iff_entropy_pairRV_eq_add, entropy_pairRV_eq_add_condEntropy]
  constructor <;> intro h <;> linarith

private theorem dist_tuple_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : FiniteProbSpace Ω) (e : ι ≃ κ)
    (X : κ → Ω → α) (a : κ → α) :
    μ.dist (fun ω i => X (e i) ω) (fun i => a (e i)) =
      μ.dist (fun ω j => X j ω) a := by
  classical
  unfold FiniteProbSpace.dist
  congr 1
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    funext j
    simpa using congrFun h (e.symm j)
  · intro h
    funext i
    exact congrFun h (e i)

private theorem independentFamily_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (μ : FiniteProbSpace Ω) (e : ι ≃ κ)
    (X : κ → Ω → α) :
    IndependentFamily μ (fun i => X (e i)) ↔ IndependentFamily μ X := by
  constructor
  · intro h a
    rw [← dist_tuple_reindex μ e X a, h]
    simpa only using e.prod_comp (fun j => μ.dist (X j) (a j))
  · intro h a
    let b : κ → α := fun j => a (e.symm j)
    have hb : (fun i => b (e i)) = a := by
      funext i
      simp [b]
    rw [← hb, dist_tuple_reindex μ e X b, h]
    simpa only using (e.prod_comp (fun j => μ.dist (X j) (b j))).symm

private theorem entropy_tuple_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : FiniteProbSpace Ω) (e : ι ≃ κ)
    (X : κ → Ω → α) :
    entropy μ (fun ω i => X (e i) ω) = entropy μ (fun ω j => X j ω) := by
  classical
  let f : (κ → α) → (ι → α) := fun a i => a (e i)
  have hf : Function.Injective f := by
    intro a b h
    funext j
    simpa [f] using congrFun h (e.symm j)
  simpa [f, Function.comp_def] using
    entropy_comp_of_injective μ (fun ω j => X j ω) hf

private theorem dist_option_tuple_eq_pairRV {ι : Type*} [Fintype ι]
    (μ : FiniteProbSpace Ω) (X : Option ι → Ω → α) (b : α) (a : ι → α) :
    μ.dist (fun ω j => X j ω) (fun j => j.elim b a) =
      μ.dist (pairRV (X none) (fun ω i => X (some i) ω)) (b, a) := by
  classical
  unfold FiniteProbSpace.dist
  congr 1
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact Prod.ext (congrFun h none) (funext fun i => congrFun h (some i))
  · intro h
    funext j
    cases j with
    | none => exact congrArg Prod.fst h
    | some i => exact congrFun (congrArg Prod.snd h) i

private theorem entropy_option_tuple_eq_pairRV {ι : Type*} [Fintype ι]
    (μ : FiniteProbSpace Ω) (X : Option ι → Ω → α) :
    entropy μ (fun ω j => X j ω) =
      entropy μ (pairRV (X none) (fun ω i => X (some i) ω)) := by
  classical
  let f : (α × (ι → α)) → (Option ι → α) := fun p j => j.elim p.1 p.2
  have hf : Function.Injective f := by
    intro p q h
    exact Prod.ext (congrFun h none) (funext fun i => congrFun h (some i))
  have h := entropy_comp_of_injective μ
    (pairRV (X none) (fun ω i => X (some i) ω)) hf
  rw [show (fun ω j => X j ω) =
      f ∘ pairRV (X none) (fun ω i => X (some i) ω) by
    funext ω j
    cases j <;> rfl]
  exact h

private theorem independentFamily_option_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteProbSpace Ω) (X : Option ι → Ω → α) :
    IndependentFamily μ X ↔
      IndependentFamily μ (fun i => X (some i)) ∧
        Independent μ (X none) (fun ω i => X (some i) ω) := by
  constructor
  · intro h
    have htail : IndependentFamily μ (fun i => X (some i)) := by
      intro a
      rw [← μ.sum_dist_pairRV_fst (X none) (fun ω i => X (some i) ω) a]
      calc
        ∑ b ∈ rangeFinset (X none),
            μ.dist (pairRV (X none) (fun ω i => X (some i) ω)) (b, a) =
            ∑ b ∈ rangeFinset (X none),
              μ.dist (fun ω j => X j ω) (fun j => j.elim b a) := by
                refine Finset.sum_congr rfl fun b _ => ?_
                exact (dist_option_tuple_eq_pairRV μ X b a).symm
        _ = ∑ b ∈ rangeFinset (X none),
              ∏ j, μ.dist (X j) ((fun j => j.elim b a) j) := by
                refine Finset.sum_congr rfl fun b _ => h _
        _ = ∏ i, μ.dist (X (some i)) (a i) := by
                simp_rw [Fintype.prod_option, Option.elim_none, Option.elim_some]
                rw [← Finset.sum_mul, μ.sum_dist_eq_one, one_mul]
    refine ⟨htail, ?_⟩
    intro b a
    rw [← dist_option_tuple_eq_pairRV μ X b a, h, Fintype.prod_option, htail a]
    simp only [Option.elim_none, Option.elim_some]
  · rintro ⟨htail, hpair⟩ a
    let b : ι → α := fun i => a (some i)
    have ha : (fun j => j.elim (a none) b) = a := by
      funext j
      cases j <;> rfl
    rw [← ha, dist_option_tuple_eq_pairRV μ X (a none) b, hpair, htail,
      Fintype.prod_option]
    simp only [Option.elim_none, Option.elim_some]

private theorem entropy_const (μ : FiniteProbSpace Ω) (a : α) :
    entropy μ (fun _ => a) = 0 := by
  have : Nonempty Ω := by
    by_contra hΩ
    have : IsEmpty Ω := not_nonempty_iff.mp hΩ
    simpa using μ.sum_prob
  have hrange : rangeFinset (fun _ : Ω => a) = {a} := by
    ext b
    simp [rangeFinset, eq_comm]
  have hdist : μ.dist (fun _ : Ω => a) a = 1 := by
    simp [FiniteProbSpace.dist, FiniteProbSpace.probOf, μ.sum_prob]
  rw [entropy, hrange, Finset.sum_singleton, hdist, negMulLog2_one]

private theorem finite_family_entropy_option {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteProbSpace Ω) (Y : Option ι → Ω → α)
    (htail : entropy μ (fun ω i => Y (some i) ω) ≤ ∑ i, entropy μ (Y (some i)) ∧
      (IndependentFamily μ (fun i => Y (some i)) ↔
        entropy μ (fun ω i => Y (some i) ω) = ∑ i, entropy μ (Y (some i)))) :
    entropy μ (fun ω j => Y j ω) ≤ ∑ j, entropy μ (Y j) ∧
      (IndependentFamily μ Y ↔
        entropy μ (fun ω j => Y j ω) = ∑ j, entropy μ (Y j)) := by
  have hpair := entropy_pairRV_le_add μ (Y none) (fun ω i => Y (some i) ω)
  have he := entropy_option_tuple_eq_pairRV μ Y
  have hsum : (∑ j, entropy μ (Y j)) =
      entropy μ (Y none) + ∑ i, entropy μ (Y (some i)) := by
    rw [Fintype.sum_option]
  constructor
  · linarith [htail.1]
  · constructor
    · intro h
      have hs := (independentFamily_option_iff μ Y).1 h
      have hZ := htail.2.1 hs.1
      have hhead := (independent_iff_entropy_pairRV_eq_add μ
        (Y none) (fun ω i => Y (some i) ω)).1 hs.2
      linarith
    · intro h
      have hZ : entropy μ (fun ω i => Y (some i) ω) =
          ∑ i, entropy μ (Y (some i)) := by
        linarith [htail.1]
      have hhead : entropy μ (pairRV (Y none) (fun ω i => Y (some i) ω)) =
          entropy μ (Y none) + entropy μ (fun ω i => Y (some i) ω) := by
        linarith
      exact (independentFamily_option_iff μ Y).2 ⟨htail.2.2 hZ,
        (independent_iff_entropy_pairRV_eq_add μ
          (Y none) (fun ω i => Y (some i) ω)).2 hhead⟩

private theorem finite_family_entropy_fin (n : ℕ) (μ : FiniteProbSpace Ω)
    (X : Fin n → Ω → α) :
    entropy μ (fun ω i => X i ω) ≤ ∑ i, entropy μ (X i) ∧
      (IndependentFamily μ X ↔
        entropy μ (fun ω i => X i ω) = ∑ i, entropy μ (X i)) := by
  induction n with
  | zero =>
      have htuple : (fun ω i => X i ω) = (fun _ => fun i => Fin.elim0 i) := by
        funext ω i
        exact Fin.elim0 i
      have he : entropy μ (fun ω i => X i ω) = 0 := by
        rw [htuple, entropy_const]
      have hi : IndependentFamily μ X := by
        intro a
        rw [Fintype.prod_empty]
        unfold FiniteProbSpace.dist FiniteProbSpace.probOf
        have hfilter : (Finset.univ.filter fun ω => (fun i => X i ω) = a) =
            Finset.univ := by
          ext ω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact Subsingleton.elim _ _
        rw [hfilter]
        simpa using μ.sum_prob
      constructor
      · simpa only [Fintype.sum_empty, he] using (le_refl 0)
      · rw [he, Fintype.sum_empty]
        exact iff_of_true hi rfl
  | succ n ih =>
      let e : Option (Fin n) ≃ Fin (n + 1) := finSuccEquivLast.symm
      let Y : Option (Fin n) → Ω → α := fun j => X (e j)
      have hY := finite_family_entropy_option μ Y (ih (fun i => Y (some i)))
      have hent := entropy_tuple_reindex μ e X
      have hsum := e.sum_comp (fun i => entropy μ (X i))
      have hind := independentFamily_reindex μ e X
      constructor
      · calc
          entropy μ (fun ω i => X i ω) = entropy μ (fun ω j => Y j ω) := hent.symm
          _ ≤ ∑ j, entropy μ (Y j) := hY.1
          _ = ∑ i, entropy μ (X i) := hsum
      · constructor
        · intro hX
          have hYX := hY.2.1 (hind.mpr hX)
          calc
            entropy μ (fun ω i => X i ω) = entropy μ (fun ω j => Y j ω) := hent.symm
            _ = ∑ j, entropy μ (Y j) := hYX
            _ = ∑ i, entropy μ (X i) := hsum
        · intro hX
          apply hind.mp
          apply hY.2.2
          calc
            entropy μ (fun ω j => Y j ω) = entropy μ (fun ω i => X i ω) := hent
            _ = ∑ i, entropy μ (X i) := hX
            _ = ∑ j, entropy μ (Y j) := hsum.symm

private theorem finite_family_entropy_induction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteProbSpace Ω) (X : ι → Ω → α) :
    entropy μ (fun ω i => X i ω) ≤ ∑ i, entropy μ (X i) ∧
      (IndependentFamily μ X ↔
        entropy μ (fun ω i => X i ω) = ∑ i, entropy μ (X i)) := by
  let e := Fintype.equivFin ι
  let Y : Fin (Fintype.card ι) → Ω → α := fun j => X (e.symm j)
  have hY := finite_family_entropy_fin (Fintype.card ι) μ Y
  have hent := entropy_tuple_reindex μ e.symm X
  have hsum := e.symm.sum_comp (fun i => entropy μ (X i))
  have hind := independentFamily_reindex μ e.symm X
  constructor
  · calc
      entropy μ (fun ω i => X i ω) = entropy μ (fun ω j => Y j ω) := hent.symm
      _ ≤ ∑ j, entropy μ (Y j) := hY.1
      _ = ∑ i, entropy μ (X i) := hsum
  · constructor
    · intro hX
      have hYX := hY.2.1 (hind.mpr hX)
      calc
        entropy μ (fun ω i => X i ω) = entropy μ (fun ω j => Y j ω) := hent.symm
        _ = ∑ j, entropy μ (Y j) := hYX
        _ = ∑ i, entropy μ (X i) := hsum
    · intro hX
      apply hind.mp
      apply hY.2.2
      calc
        entropy μ (fun ω j => Y j ω) = entropy μ (fun ω i => X i ω) := hent
        _ = ∑ i, entropy μ (X i) := hX
        _ = ∑ j, entropy μ (Y j) := hsum.symm

/-- **The entropy criterion for mutual independence of a family**: the members of a finite family
of random variables are mutually independent if and only if the entropy of the tuple is the sum of
the entropies.

**Stronger than the printed statement**: the book states this for three variables `α, β, γ`, the
statement here is for an arbitrary finite index type.  All members take values in one type, which
costs nothing — finitely many finite ranges can be injected into a common type, and entropy is
invariant under such an injection.  SUV Problem 222, p. 222. -/
theorem independentFamily_iff_entropy_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteProbSpace Ω) (X : ι → Ω → α) :
    IndependentFamily μ X ↔ entropy μ (fun ω i => X i ω) = ∑ i, entropy μ (X i) := by
  exact (finite_family_entropy_induction μ X).2

/-! ### Theorem 145: the basic inequality -/

/-- **Relativized subadditivity**: `H(⟨ξ, η⟩ | α) ≤ H(ξ|α) + H(η|α)`, the conditional version of
Theorem 141 obtained by conditioning on each value of `α` and averaging.
SUV Section 7.2.4, p. 223. -/
theorem condEntropy_pairRV_le_add (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    condEntropy μ (pairRV X Y) Z ≤ condEntropy μ X Z + condEntropy μ Y Z := by
  unfold condEntropy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [← mul_add]
  rcases (μ.dist_nonneg Z c).lt_or_eq with hq | hq
  · refine mul_le_mul_of_nonneg_left ?_ hq.le
    rw [← μ.entropy_condSpace hq, ← μ.entropy_condSpace hq, ← μ.entropy_condSpace hq]
    exact entropy_pairRV_le_add _ X Y
  · rw [← hq]
    simp

/-- **The basic inequality**: `H(ξ, η, α) + H(α) ≤ H(ξ, α) + H(η, α)`, where `H(ξ, η, α)` is the
entropy of `⟨⟨ξ, η⟩, α⟩`.  SUV Theorem 145, p. 223. -/
theorem entropy_triple_add_entropy_le_add_entropy_pair (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) :
    entropy μ (pairRV (pairRV X Y) Z) + entropy μ Z ≤
      entropy μ (pairRV X Z) + entropy μ (pairRV Y Z) := by
  have h1 := entropy_pairRV_eq_add_condEntropy μ (pairRV X Y) Z
  have h2 := entropy_pairRV_eq_add_condEntropy μ X Z
  have h3 := entropy_pairRV_eq_add_condEntropy μ Y Z
  have h4 := condEntropy_pairRV_le_add μ X Y Z
  linarith

/-- **The basic inequality in the form `I(α:β|γ) ≥ 0`.**  SUV Theorem 145, p. 223. -/
theorem condMutualInfo_nonneg (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    0 ≤ condMutualInfo μ X Y Z := by
  unfold condMutualInfo
  linarith [condEntropy_pairRV_le_add μ X Y Z]

end Kolmogorov
