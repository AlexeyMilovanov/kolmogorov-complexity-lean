import KolmogorovMathlib.Entropy.Complexity.Basic
import KolmogorovMathlib.CommonInformation.FixedHistogramRank.PlainAndFibreDecoders
import KolmogorovMathlib.Complexity.CanonicalObjects.Counting
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Entropy.Conditional
import KolmogorovMathlib.Entropy.Inequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.EquivFin

/-!
# Conditional Shannon coding (Problem 241)

SUV Section 7.3.5, p. 232, Problem 241.

The conditional version of Theorem 151, in which the side information `η^N` is known to both the
encoder and the decoder.  The book leaves the statement to the reader; the statement here is the
expected one, with threshold `m = N H(ξ|η) ± c√N`: with `N H(ξ|η) + c√N` bits the error can be
made at most `ε` (`exists_const_cond_code_error_le`), and with `N H(ξ|η) − c√N` bits the
probability of correct decoding is at most `ε` (`exists_const_cond_prob_correct_le`).
-/

namespace Kolmogorov

open Finset

/-! ### Problem 241: conditional coding -/

private lemma power_expect_centered_sq {Ω : Type*} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (g : Ω → ℝ) (hg : μ.expect g = 0) (N : ℕ) :
    (μ.power N).expect (fun w => (∑ i, g (w i)) ^ 2) =
      N * μ.expect (fun ω => (g ω) ^ 2) := by
  classical
  have hcoord : ∀ i j : Fin N,
      ∑ w : Fin N → Ω, (∏ k, μ.prob (w k)) * (g (w i) * g (w j)) =
        if i = j then μ.expect (fun ω => (g ω) ^ 2) else 0 := by
    intro i j
    have hw : ∀ w : Fin N → Ω,
        (∏ k, μ.prob (w k)) * (g (w i) * g (w j)) =
          ∏ k, if k = i then
            if k = j then μ.prob (w k) * (g (w k) ^ 2)
            else μ.prob (w k) * g (w k)
          else if k = j then μ.prob (w k) * g (w k) else μ.prob (w k) := by
      intro w
      by_cases hij : i = j
      · subst j
        have hk : ∀ k : Fin N, (if k = i then
              if k = i then μ.prob (w k) * g (w k) ^ 2 else μ.prob (w k) * g (w k)
              else if k = i then μ.prob (w k) * g (w k) else μ.prob (w k)) =
              μ.prob (w k) * (if k = i then g (w k) ^ 2 else 1) := by
          intro k
          split_ifs <;> ring
        simp_rw [hk]
        rw [Finset.prod_mul_distrib,
          Finset.prod_ite_eq' Finset.univ i (fun k => g (w k) ^ 2)]
        simp [Finset.mem_univ, pow_two]
      · have hk : ∀ k : Fin N, (if k = i then
              if k = j then μ.prob (w k) * g (w k) ^ 2 else μ.prob (w k) * g (w k)
              else if k = j then μ.prob (w k) * g (w k) else μ.prob (w k)) =
              μ.prob (w k) * (if k = i then g (w k) else 1) *
                (if k = j then g (w k) else 1) := by
          intro k
          split_ifs <;> simp_all
        simp_rw [hk]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_ite_eq' Finset.univ i (fun k => g (w k)),
          Finset.prod_ite_eq' Finset.univ j (fun k => g (w k))]
        simp [Finset.mem_univ]
        ring
    simp_rw [hw]
    rw [← Fintype.piFinset_univ,
      Finset.sum_prod_piFinset Finset.univ (fun k ω => if k = i then
        if k = j then μ.prob ω * (g ω ^ 2) else μ.prob ω * g ω
        else if k = j then μ.prob ω * g ω else μ.prob ω)]
    by_cases hij : i = j
    · subst j
      simp_rw [Finset.sum_ite_irrel]
      rw [μ.sum_prob]
      have hk : ∀ k : Fin N, (if k = i then
            if k = i then ∑ ω, μ.prob ω * g ω ^ 2 else ∑ ω, μ.prob ω * g ω
            else if k = i then ∑ ω, μ.prob ω * g ω else 1) =
            (if k = i then ∑ ω, μ.prob ω * g ω ^ 2 else 1) := by
        intro k
        split_ifs <;> rfl
      simp_rw [hk]
      rw [Finset.prod_ite_eq' Finset.univ i]
      simp [Finset.mem_univ, FiniteProbSpace.expect]
    · simp_rw [Finset.sum_ite_irrel]
      rw [μ.sum_prob]
      have hgsum : ∑ ω, μ.prob ω * g ω = 0 := hg
      have hk : ∀ k : Fin N, (if k = i then
            if k = j then ∑ ω, μ.prob ω * g ω ^ 2 else ∑ ω, μ.prob ω * g ω
            else if k = j then ∑ ω, μ.prob ω * g ω else 1) =
            (if k = i then (∑ ω, μ.prob ω * g ω) else 1) *
              (if k = j then (∑ ω, μ.prob ω * g ω) else 1) := by
        intro k
        split_ifs <;> simp_all
      simp_rw [hk]
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i,
        Finset.prod_ite_eq' Finset.univ j]
      simp [Finset.mem_univ, hgsum, hij]
  change (∑ w : Fin N → Ω, (∏ i, μ.prob (w i)) * (∑ i, g (w i)) ^ 2) = _
  rw [Finset.sum_congr rfl fun w _ => by rw [pow_two, Finset.sum_mul_sum]]
  rw [Finset.sum_congr rfl fun w _ => Finset.mul_sum .., Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  calc
    (∑ i : Fin N, ∑ j : Fin N,
        ∑ w : Fin N → Ω, (∏ k, μ.prob (w k)) * (g (w i) * g (w j))) =
        ∑ i : Fin N, ∑ j : Fin N,
          if i = j then μ.expect (fun ω => (g ω) ^ 2) else 0 := by
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => hcoord i j
    _ = N * μ.expect (fun ω => (g ω) ^ 2) := by
      simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma exists_nat_power_prob_sum_gt {Ω : Type*} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (f : Ω → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N : ℕ,
      (μ.power N).probOfPred
        (fun w => (N : ℝ) * μ.expect f + c * Real.sqrt N < ∑ i, f (w i)) ≤ ε := by
  classical
  let g : Ω → ℝ := fun ω => f ω - μ.expect f
  let V : ℝ := μ.expect fun ω => (g ω) ^ 2
  have hV : 0 ≤ V := Finset.sum_nonneg fun ω _ =>
    mul_nonneg (μ.prob_nonneg ω) (sq_nonneg _)
  obtain ⟨c, hc⟩ := exists_nat_gt (Real.sqrt (V / ε))
  have hc0 : 0 < (c : ℝ) := (Real.sqrt_nonneg _).trans_lt hc
  have hcε : V ≤ ε * (c : ℝ) ^ 2 := by
    have hs := Real.sq_sqrt (div_nonneg hV hε.le)
    have hc2 : V / ε < (c : ℝ) ^ 2 := by
      rw [← hs]
      simpa only [pow_two] using mul_self_lt_mul_self (Real.sqrt_nonneg _) hc
    nlinarith [(div_le_iff₀ hε).mp (le_of_lt hc2)]
  refine ⟨c, fun N => ?_⟩
  have hg : μ.expect g = 0 := by
    simp only [g, FiniteProbSpace.expect, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, μ.sum_prob, one_mul, sub_self]
  have hsecond := power_expect_centered_sq μ g hg N
  have hcenter : ∀ w : Fin N → Ω,
      ∑ i, g (w i) = ∑ i, f (w i) - (N : ℝ) * μ.expect f := by
    intro w
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  by_cases hN : N = 0
  · subst N
    simpa [FiniteProbSpace.probOfPred] using hε.le
  have hNR : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hsqrt : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hpoint : ∀ w : Fin N → Ω,
      Set.indicator
          {w | (N : ℝ) * μ.expect f + c * Real.sqrt N < ∑ i, f (w i)}
          (μ.power N).prob w * ((c : ℝ) ^ 2 * N) ≤
        (μ.power N).prob w * ((∑ i, g (w i)) ^ 2) := by
    intro w
    by_cases hw : w ∈
        {w | (N : ℝ) * μ.expect f + c * Real.sqrt N < ∑ i, f (w i)}
    · rw [Set.indicator_of_mem hw]
      have hsum : (c : ℝ) * Real.sqrt N < ∑ i, g (w i) := by
        rw [hcenter]
        convert sub_lt_sub_right hw (N * μ.expect f) using 1
        all_goals ring_nf
      have hsnonneg : 0 ≤ ∑ i, g (w i) := le_trans (mul_nonneg hc0.le (Real.sqrt_nonneg _))
        (le_of_lt hsum)
      apply mul_le_mul_of_nonneg_left _ ((μ.power N).prob_nonneg w)
      calc
        (c : ℝ) ^ 2 * N = (c : ℝ) ^ 2 * (Real.sqrt N) ^ 2 := by rw [hsqrt]
        _ = ((c : ℝ) * Real.sqrt N) ^ 2 := by ring
        _ ≤ (∑ i, g (w i)) ^ 2 :=
          (sq_le_sq₀ (mul_nonneg hc0.le (Real.sqrt_nonneg _)) hsnonneg).2 (le_of_lt hsum)
    · rw [Set.indicator_of_notMem hw]
      simpa using mul_nonneg ((μ.power N).prob_nonneg w) (sq_nonneg (∑ i, g (w i)))
  have hmul : (μ.power N).probOfPred
        (fun w => (N : ℝ) * μ.expect f + c * Real.sqrt N < ∑ i, f (w i)) *
        ((c : ℝ) ^ 2 * N) ≤ N * V := by
    rw [FiniteProbSpace.probOfPred, Finset.sum_mul]
    calc
      _ ≤ ∑ w, (μ.power N).prob w * ((∑ i, g (w i)) ^ 2) :=
        Finset.sum_le_sum fun w _ => hpoint w
      _ = N * V := hsecond
  have hden : 0 < (c : ℝ) ^ 2 * N := mul_pos (sq_pos_of_pos hc0) hNR
  calc
    (μ.power N).probOfPred
          (fun w => (N : ℝ) * μ.expect f + c * Real.sqrt N < ∑ i, f (w i)) ≤
        (N * V) / ((c : ℝ) ^ 2 * N) := (le_div_iff₀ hden).2 hmul
    _ = V / (c : ℝ) ^ 2 := by field_simp
    _ ≤ ε := (div_le_iff₀ (sq_pos_of_pos hc0)).2 (by nlinarith [hcε])

private noncomputable def condSelfInfo {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (μ : FiniteProbSpace (A × B)) (z : A × B) : ℝ :=
  if μ.prob z = 0 then 0 else -Real.logb 2 (μ.prob z / μ.dist Prod.snd z.2)

private lemma nonempty_factors_of_prob {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteProbSpace (A × B)) : Nonempty A ∧ Nonempty B := by
  classical
  constructor
  · by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simpa using μ.sum_prob
  · by_contra h
    have : IsEmpty B := not_nonempty_iff.mp h
    simpa using μ.sum_prob

private lemma expect_condSelfInfo_eq {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (μ : FiniteProbSpace (A × B)) :
    μ.expect (condSelfInfo μ) = condEntropy μ Prod.fst Prod.snd := by
  classical
  obtain ⟨hA, hB⟩ := nonempty_factors_of_prob μ
  let : Nonempty A := hA
  let : Nonempty B := hB
  have hrA : rangeFinset (Prod.fst : A × B → A) = Finset.univ := by
    ext a
    simp [mem_rangeFinset]
  have hrB : rangeFinset (Prod.snd : A × B → B) = Finset.univ := by
    ext b
    simp [mem_rangeFinset]
  have hpair : ∀ a b,
      μ.dist (pairRV Prod.fst Prod.snd) (a, b) = μ.prob (a, b) := by
    intro a b
    rw [μ.dist_pairRV]
    have heq : ((Finset.univ.filter fun z : A × B => Prod.snd z = b).filter
        fun z => Prod.fst z = a) = {(a, b)} := by
      ext z
      rcases z with ⟨x, y⟩
      simp [and_comm]
    simp [FiniteProbSpace.probOf, heq]
  rw [condEntropy_eq_sum_sum, hrA, hrB]
  simp only [FiniteProbSpace.expect, Fintype.sum_prod_type, hpair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : μ.prob (a, b) = 0
  · simp [condSelfInfo, hp, negMulLog2_zero]
  have hq : 0 < μ.dist Prod.snd b := by
    have hle := μ.dist_pairRV_le_snd Prod.fst Prod.snd a b
    rw [hpair] at hle
    exact (μ.dist_nonneg Prod.snd b).lt_of_ne fun h0 => hp (le_antisymm (hle.trans h0.ge)
      (μ.prob_nonneg _))
  rw [condSelfInfo, ite_eq_right hp, negMulLog2_eq]
  field_simp

private noncomputable def condTypicalFiber {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (μ : FiniteProbSpace (A × B)) (N m : ℕ)
    (y : Fin N → B) : Finset (Fin N → A) :=
  Finset.univ.filter fun x =>
    (∀ i, 0 < μ.prob (x i, y i)) ∧ ∑ i, condSelfInfo μ (x i, y i) ≤ m

private lemma sum_prob_fst_eq_dist_snd {A B : Type*} [Fintype A]
    [Fintype B] [DecidableEq B] (μ : FiniteProbSpace (A × B)) (b : B) :
    ∑ a, μ.prob (a, b) = μ.dist Prod.snd b := by
  classical
  unfold FiniteProbSpace.dist FiniteProbSpace.probOf
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hne
    simp [hne]
  · simp

private lemma condTypicalFiber_card_le {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (μ : FiniteProbSpace (A × B)) (N m : ℕ)
    (y : Fin N → B) : (condTypicalFiber μ N m y).card ≤ 2 ^ m := by
  classical
  let S := condTypicalFiber μ N m y
  by_cases hS : S = ∅
  · change S.card ≤ 2 ^ m
    simp [hS]
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have hx₀' := (Finset.mem_filter.mp hx₀).2.1
  let q : Fin N → A → ℝ := fun i a => μ.prob (a, y i) / μ.dist Prod.snd (y i)
  have hden : ∀ i, 0 < μ.dist Prod.snd (y i) := by
    intro i
    have hle : μ.prob (x₀ i, y i) ≤ μ.dist Prod.snd (y i) := by
      have h := μ.dist_pairRV_le_snd Prod.fst Prod.snd (x₀ i) (y i)
      have hp : μ.dist (pairRV Prod.fst Prod.snd) (x₀ i, y i) =
          μ.prob (x₀ i, y i) := by
        rw [μ.dist_pairRV]
        have heq : ((Finset.univ.filter fun z : A × B => Prod.snd z = y i).filter
            fun z => Prod.fst z = x₀ i) = {(x₀ i, y i)} := by
          ext z
          rcases z with ⟨a, b⟩
          simp [and_comm]
        simp [FiniteProbSpace.probOf, heq]
      rwa [hp] at h
    exact (hx₀' i).trans_le hle
  have hqsum : ∀ i, ∑ a, q i a = 1 := by
    intro i
    simp only [q, ← Finset.sum_div]
    rw [sum_prob_fst_eq_dist_snd, div_self (ne_of_gt (hden i))]
  have hqpos : ∀ x ∈ S, ∀ i, 0 < q i (x i) := by
    intro x hx i
    exact div_pos ((Finset.mem_filter.mp hx).2.1 i) (hden i)
  have hweight : ∀ x ∈ S, (2 : ℝ) ^ (-(m : ℝ)) ≤ ∏ i, q i (x i) := by
    intro x hx
    have hinfo := (Finset.mem_filter.mp hx).2.2
    have hlog : Real.logb 2 (∏ i, q i (x i)) = ∑ i, Real.logb 2 (q i (x i)) := by
      exact Real.logb_prod Finset.univ (fun i => q i (x i)) fun i _ => ne_of_gt (hqpos x hx i)
    have hrewrite : ∑ i, condSelfInfo μ (x i, y i) =
        -(∑ i, Real.logb 2 (q i (x i))) := by
      simp only [condSelfInfo, q]
      rw [Finset.sum_congr rfl fun i _ => ite_eq_right (ne_of_gt ((Finset.mem_filter.mp hx).2.1 i)),
        Finset.sum_neg_distrib]
    have hlelog : -(m : ℝ) ≤ Real.logb 2 (∏ i, q i (x i)) := by
      rw [hlog]
      linarith
    exact (Real.le_logb_iff_rpow_le one_lt_two
      (Finset.prod_pos fun i _ => hqpos x hx i)).1 hlelog
  have hsumupper : ∑ x ∈ S, ∏ i, q i (x i) ≤ 1 := by
    calc
      _ ≤ ∑ x : Fin N → A, ∏ i, q i (x i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ =>
          Finset.prod_nonneg fun i _ => div_nonneg (μ.prob_nonneg _) (hden i).le
      _ = 1 := by
        rw [← Fintype.piFinset_univ,
          Finset.sum_prod_piFinset Finset.univ (fun i a => q i a)]
        simp [hqsum]
  have hlower : (S.card : ℝ) * (2 : ℝ) ^ (-(m : ℝ)) ≤
      ∑ x ∈ S, ∏ i, q i (x i) := by
    calc
      (S.card : ℝ) * (2 : ℝ) ^ (-(m : ℝ)) =
          ∑ _x ∈ S, (2 : ℝ) ^ (-(m : ℝ)) := by simp
      _ ≤ ∑ x ∈ S, ∏ i, q i (x i) := Finset.sum_le_sum fun x hx => hweight x hx
  have hcardR : (S.card : ℝ) ≤ (2 ^ m : ℕ) := by
    have hpow : (2 : ℝ) ^ (-(m : ℝ)) = ((2 ^ m : ℕ) : ℝ)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      norm_num
    rw [hpow] at hlower
    have := hlower.trans hsumupper
    have hpos : (0 : ℝ) < (2 ^ m : ℕ) := by positivity
    rw [inv_eq_one_div, mul_one_div] at this
    exact (div_le_one hpos).mp this
  exact_mod_cast hcardR

/-- **Conditional coding, achievability.**  Let `⟨ξ, η⟩` have joint distribution `μ` on `A × B`
and make `N` independent trials; the value of `η^N` is known to both the sender and the receiver.
Then `N H(ξ|η) + c√N` bits suffice to transmit `ξ^N` with error probability at most `ε`.  The book
asks for the statement ("how large should `m` be?"); this is the expected answer, stated for an
arbitrary joint distribution.  SUV Problem 241, p. 232. -/
theorem exists_const_cond_code_error_le (A B : Type*) [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (μ : FiniteProbSpace (A × B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N m : ℕ,
      (N : ℝ) * condEntropy μ Prod.fst Prod.snd + c * Real.sqrt N ≤ m →
      ∃ (e : (Fin N → A) → (Fin N → B) → Fin m → Bool)
        (d : (Fin m → Bool) → (Fin N → B) → Fin N → A),
        (μ.power N).probOfPred
          (fun w => d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) ≠ Prod.fst ∘ w) ≤ ε := by
  classical
  obtain ⟨c, hc⟩ := exists_nat_power_prob_sum_gt μ (condSelfInfo μ) hε
  refine ⟨c, fun N m hm => ?_⟩
  obtain ⟨hA, hB⟩ := nonempty_factors_of_prob μ
  let : Nonempty A := hA
  let : Nonempty B := hB
  let S : (Fin N → B) → Finset (Fin N → A) := fun y => condTypicalFiber μ N m y
  have hcard : ∀ y, Fintype.card (↥(S y)) ≤ Fintype.card (Fin m → Bool) := by
    intro y
    rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact condTypicalFiber_card_le μ N m y
  let emb : ∀ y, ↥(S y) ↪ (Fin m → Bool) := fun y =>
    Classical.choice (Function.Embedding.nonempty_of_card_le (hcard y))
  let e : (Fin N → A) → (Fin N → B) → Fin m → Bool := fun x y =>
    if hx : x ∈ S y then emb y ⟨x, hx⟩ else fun _ => false
  let d : (Fin m → Bool) → (Fin N → B) → Fin N → A := fun z y =>
    if hz : ∃ x : ↥(S y), emb y x = z then (Classical.choose hz).1
    else fun _ => Classical.choice hA
  have hcorrect : ∀ x y, x ∈ S y → d (e x y) y = x := by
    intro x y hx
    let sx : ↥(S y) := ⟨x, hx⟩
    have hex : ∃ t : ↥(S y), emb y t = emb y sx := ⟨sx, rfl⟩
    rw [show e x y = emb y sx by simp [e, sx, hx]]
    rw [show d (emb y sx) y = (Classical.choose hex).1 by simp only [d, dite_eq_left hex]]
    exact congrArg Subtype.val ((emb y).injective (Classical.choose_spec hex))
  refine ⟨e, d, ?_⟩
  calc
    (μ.power N).probOfPred
        (fun w => d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) ≠
          Prod.fst ∘ w) ≤
      (μ.power N).probOfPred
        (fun w => (N : ℝ) * condEntropy μ Prod.fst Prod.snd + c * Real.sqrt N <
          ∑ i, condSelfInfo μ (w i)) := by
      unfold FiniteProbSpace.probOfPred
      apply Finset.sum_le_sum
      intro w _
      by_cases hp : (μ.power N).prob w = 0
      · simp only [Set.indicator_apply]
        split <;> split <;> simp [hp]
      have hpcoord : ∀ i, 0 < μ.prob (w i) := by
        intro i
        change (∏ i, μ.prob (w i)) ≠ 0 at hp
        have hne : μ.prob (w i) ≠ 0 :=
          (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
        exact lt_of_le_of_ne (μ.prob_nonneg _) (Ne.symm hne)
      by_cases hbad : (N : ℝ) * condEntropy μ Prod.fst Prod.snd +
          c * Real.sqrt N < ∑ i, condSelfInfo μ (w i)
      · have hbmem : w ∈ {w | (N : ℝ) * condEntropy μ Prod.fst Prod.snd +
            c * Real.sqrt N < ∑ i, condSelfInfo μ (w i)} := hbad
        rw [Set.indicator_of_mem hbmem]
        by_cases herr : d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) ≠
            Prod.fst ∘ w
        · have hemem : w ∈ {w | d (e (Prod.fst ∘ w) (Prod.snd ∘ w))
              (Prod.snd ∘ w) ≠ Prod.fst ∘ w} := herr
          rw [Set.indicator_of_mem hemem]
        · have henmem : w ∉ {w | d (e (Prod.fst ∘ w) (Prod.snd ∘ w))
              (Prod.snd ∘ w) ≠ Prod.fst ∘ w} := herr
          rw [Set.indicator_of_notMem henmem]
          exact (μ.power N).prob_nonneg w
      · have hmem : (Prod.fst ∘ w) ∈ S (Prod.snd ∘ w) := by
          change (Prod.fst ∘ w) ∈ condTypicalFiber μ N m (Prod.snd ∘ w)
          unfold condTypicalFiber
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, fun i => ?_, ?_⟩
          · exact hpcoord i
          · exact (le_of_not_gt hbad).trans hm
        have heq := hcorrect (Prod.fst ∘ w) (Prod.snd ∘ w) hmem
        simp [Set.indicator_of_notMem, hbad, heq]
    _ ≤ ε := by
      rw [← expect_condSelfInfo_eq μ]
      exact hc N

/-- The pair distribution of the identity components is the joint weight itself. -/
private lemma dist_pairRV_fst_snd_eq_prob {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (μ : FiniteProbSpace (A × B)) (z : A × B) :
    μ.dist (pairRV Prod.fst Prod.snd) z = μ.prob z := by
  classical
  obtain ⟨a, b⟩ := z
  rw [μ.dist_pairRV]
  have heq : ((Finset.univ.filter fun z : A × B => Prod.snd z = b).filter
      fun z => Prod.fst z = a) = {(a, b)} := by
    ext z
    rcases z with ⟨x, y⟩
    simp [and_comm]
  simp [FiniteProbSpace.probOf, heq]

/-- A joint weight is at most the marginal weight of its second coordinate. -/
private lemma prob_le_dist_snd {A B : Type*} [Fintype A]
    [Fintype B] [DecidableEq B] (μ : FiniteProbSpace (A × B)) (z : A × B) :
    μ.prob z ≤ μ.dist Prod.snd z.2 := by
  classical
  have h := μ.dist_pairRV_le_snd Prod.fst Prod.snd z.1 z.2
  rw [dist_pairRV_fst_snd_eq_prob] at h
  simpa using h

/-- Factorisation of a positive joint weight through the conditional self-information:
`p(z) = p_η(z.2) · 2^(−I(z))`. -/
private lemma prob_eq_dist_snd_mul {A B : Type*} [Fintype A]
    [Fintype B] [DecidableEq B] (μ : FiniteProbSpace (A × B)) (z : A × B)
    (hz : 0 < μ.prob z) :
    μ.prob z = μ.dist Prod.snd z.2 * (2 : ℝ) ^ (-condSelfInfo μ z) := by
  have hq : 0 < μ.dist Prod.snd z.2 := lt_of_lt_of_le hz (prob_le_dist_snd μ z)
  have hdiv : 0 < μ.prob z / μ.dist Prod.snd z.2 := div_pos hz hq
  rw [condSelfInfo, ite_eq_right hz.ne', neg_neg,
    Real.rpow_logb (by norm_num) (by norm_num) hdiv]
  field_simp

/-- The marginal distribution of the second coordinate sums to one over the whole alphabet. -/
private lemma sum_dist_snd_eq_one {A B : Type*} [Fintype A]
    [Fintype B] [DecidableEq B] (μ : FiniteProbSpace (A × B)) :
    ∑ b, μ.dist Prod.snd b = 1 := by
  classical
  simp_rw [← sum_prob_fst_eq_dist_snd μ]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact μ.sum_prob

/-- A predicate whose truth forces one of two others has probability at most the sum of theirs. -/
private lemma probOfPred_le_add {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (P Q R : Ω → Prop) (h : ∀ ω, P ω → Q ω ∨ R ω) :
    μ.probOfPred P ≤ μ.probOfPred Q + μ.probOfPred R := by
  classical
  unfold FiniteProbSpace.probOfPred
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have hQnn : (0 : ℝ) ≤ Set.indicator {ω | Q ω} μ.prob ω := by
    by_cases hq : ω ∈ {ω | Q ω}
    · rw [Set.indicator_of_mem hq]; exact μ.prob_nonneg ω
    · rw [Set.indicator_of_notMem hq]
  have hRnn : (0 : ℝ) ≤ Set.indicator {ω | R ω} μ.prob ω := by
    by_cases hr : ω ∈ {ω | R ω}
    · rw [Set.indicator_of_mem hr]; exact μ.prob_nonneg ω
    · rw [Set.indicator_of_notMem hr]
  by_cases hP : ω ∈ {ω | P ω}
  · rw [Set.indicator_of_mem hP]
    rcases h ω hP with hQ | hR
    · have hQ' : ω ∈ {ω | Q ω} := hQ
      rw [Set.indicator_of_mem hQ']; linarith
    · have hR' : ω ∈ {ω | R ω} := hR
      rw [Set.indicator_of_mem hR']; linarith
  · rw [Set.indicator_of_notMem hP]; linarith

/-- Two pointwise-equivalent predicates have equal probability. -/
private lemma probOfPred_congr {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (P Q : Ω → Prop) (h : ∀ ω, P ω ↔ Q ω) :
    μ.probOfPred P = μ.probOfPred Q := by
  have hset : {ω | P ω} = {ω | Q ω} := Set.ext h
  unfold FiniteProbSpace.probOfPred
  rw [hset]

/-- **Counting bound for the converse.**  For side information `η^N` the correctly decoded
`ξ`-words form a set of at most `2^m` elements, so the probability that decoding succeeds *and*
the conditional self-information is at least `t` is at most `2^m · 2^(−t)`: on that event each
word has probability at most `2^(−t)` times the marginal weight of its `η^N`, and the marginal
weights of the `η^N` sum to one.  This is the algorithmic core of SUV Theorem 151(b), relativised
to `η` as in Problem 241. -/
private lemma prob_correct_ge_le {A B : Type*} [Fintype A]
    [Fintype B] [DecidableEq B] (μ : FiniteProbSpace (A × B)) (N m : ℕ) (t : ℝ)
    (e : (Fin N → A) → (Fin N → B) → Fin m → Bool)
    (d : (Fin m → Bool) → (Fin N → B) → Fin N → A) :
    (μ.power N).probOfPred
        (fun w => d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w ∧
          t ≤ ∑ i, condSelfInfo μ (w i)) ≤ (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (-t) := by
  classical
  have hpt : ∀ w : Fin N → A × B,
      Set.indicator
          {w | d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w ∧
            t ≤ ∑ i, condSelfInfo μ (w i)} (μ.power N).prob w ≤
        (2 : ℝ) ^ (-t) *
          ((if d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w
              then (1 : ℝ) else 0) * ∏ i, μ.dist Prod.snd (w i).2) := by
    intro w
    have hdist_nonneg : (0 : ℝ) ≤ ∏ i, μ.dist Prod.snd (w i).2 :=
      Finset.prod_nonneg fun i _ => μ.dist_nonneg _ _
    have hrhs_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-t) *
        ((if d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w
            then (1 : ℝ) else 0) * ∏ i, μ.dist Prod.snd (w i).2) := by
      apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      apply mul_nonneg _ hdist_nonneg
      split_ifs <;> norm_num
    by_cases hmem : w ∈
        {w | d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w ∧
          t ≤ ∑ i, condSelfInfo μ (w i)}
    · rw [Set.indicator_of_mem hmem]
      obtain ⟨hcorr, hge⟩ := hmem
      rw [ite_eq_left hcorr, one_mul]
      change (∏ i, μ.prob (w i)) ≤ _
      by_cases hpos : ∀ i, 0 < μ.prob (w i)
      · have hfac : (∏ i, μ.prob (w i)) =
            (∏ i, μ.dist Prod.snd (w i).2) * (2 : ℝ) ^ (-∑ i, condSelfInfo μ (w i)) := by
          rw [Finset.prod_congr rfl (fun i _ => prob_eq_dist_snd_mul μ (w i) (hpos i)),
            Finset.prod_mul_distrib,
            ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)
              (fun i => -condSelfInfo μ (w i)) Finset.univ,
            Finset.sum_neg_distrib]
        rw [hfac]
        calc (∏ i, μ.dist Prod.snd (w i).2) * (2 : ℝ) ^ (-∑ i, condSelfInfo μ (w i))
            ≤ (∏ i, μ.dist Prod.snd (w i).2) * (2 : ℝ) ^ (-t) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hge)) hdist_nonneg
          _ = (2 : ℝ) ^ (-t) * ∏ i, μ.dist Prod.snd (w i).2 := mul_comm _ _
      · push Not at hpos
        obtain ⟨i, hi⟩ := hpos
        have hzero : μ.prob (w i) = 0 := le_antisymm hi (μ.prob_nonneg _)
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hdist_nonneg
    · rw [Set.indicator_of_notMem hmem]
      exact hrhs_nonneg
  have hydist : ∑ y : Fin N → B, ∏ i, μ.dist Prod.snd (y i) = 1 := by
    rw [← Fintype.piFinset_univ,
      Finset.sum_prod_piFinset Finset.univ (fun _ b => μ.dist Prod.snd b)]
    simp [sum_dist_snd_eq_one μ]
  have hcount : (∑ w : Fin N → A × B,
      (if d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w
        then (1 : ℝ) else 0) * ∏ i, μ.dist Prod.snd (w i).2) ≤ (2 : ℝ) ^ (m : ℝ) := by
    have hreindex : (∑ w : Fin N → A × B,
        (if d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w
          then (1 : ℝ) else 0) * ∏ i, μ.dist Prod.snd (w i).2) =
        ∑ p : (Fin N → A) × (Fin N → B),
          (if d (e p.1 p.2) p.2 = p.1 then (1 : ℝ) else 0) * ∏ i, μ.dist Prod.snd (p.2 i) := by
      exact Fintype.sum_equiv
        (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ : Fin N => A) (fun _ : Fin N => B)) _ _
        (fun w => rfl)
    rw [hreindex, Fintype.sum_prod_type_right]
    calc ∑ y : Fin N → B, ∑ x : Fin N → A,
          (if d (e x y) y = x then (1 : ℝ) else 0) * ∏ i, μ.dist Prod.snd (y i)
        = ∑ y : Fin N → B, (∏ i, μ.dist Prod.snd (y i)) *
            ((Finset.univ.filter fun x => d (e x y) y = x).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [← Finset.sum_mul, Finset.sum_boole]
          ring
      _ ≤ ∑ y : Fin N → B, (∏ i, μ.dist Prod.snd (y i)) * (2 : ℝ) ^ (m : ℝ) := by
          apply Finset.sum_le_sum
          intro y _
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => μ.dist_nonneg _ _)
          have h1 : (Finset.univ.filter fun x : Fin N → A => d (e x y) y = x).card ≤ 2 ^ m := by
            calc (Finset.univ.filter fun x : Fin N → A => d (e x y) y = x).card
                ≤ (Finset.univ.image fun z : Fin m → Bool => d z y).card := by
                  apply Finset.card_le_card
                  intro x hx
                  rw [Finset.mem_filter] at hx
                  exact Finset.mem_image.mpr ⟨e x y, Finset.mem_univ _, hx.2⟩
              _ ≤ Fintype.card (Fin m → Bool) := by
                  rw [← Finset.card_univ]; exact Finset.card_image_le
              _ = 2 ^ m := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
          calc ((Finset.univ.filter fun x : Fin N → A => d (e x y) y = x).card : ℝ)
              ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h1
            _ = (2 : ℝ) ^ (m : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
      _ = (∑ y : Fin N → B, ∏ i, μ.dist Prod.snd (y i)) * (2 : ℝ) ^ (m : ℝ) := by
          rw [← Finset.sum_mul]
      _ = 1 * (2 : ℝ) ^ (m : ℝ) := by rw [hydist]
      _ = (2 : ℝ) ^ (m : ℝ) := one_mul _
  rw [FiniteProbSpace.probOfPred]
  calc ∑ w, Set.indicator
          {w | d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w ∧
            t ≤ ∑ i, condSelfInfo μ (w i)} (μ.power N).prob w
      ≤ ∑ w : Fin N → A × B, (2 : ℝ) ^ (-t) *
          ((if d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w
              then (1 : ℝ) else 0) * ∏ i, μ.dist Prod.snd (w i).2) :=
        Finset.sum_le_sum fun w _ => hpt w
    _ = (2 : ℝ) ^ (-t) * ∑ w : Fin N → A × B,
          ((if d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w
              then (1 : ℝ) else 0) * ∏ i, μ.dist Prod.snd (w i).2) := by
        rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (-t) * (2 : ℝ) ^ (m : ℝ) :=
        mul_le_mul_of_nonneg_left hcount (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (-t) := mul_comm _ _

/-- **Conditional coding, converse.**  With the side information `η^N` known to both ends, any
code of length at most `N H(ξ|η) − c√N` recovers `ξ^N` with probability at most `ε`.  As in
Theorem 151(b), `N = 0` is excluded.  The book leaves the statement to the reader; this is the
expected one.  SUV Problem 241, p. 232. -/
theorem exists_const_cond_prob_correct_le (A B : Type*) [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (μ : FiniteProbSpace (A × B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N m : ℕ, 0 < N →
      (m : ℝ) ≤ (N : ℝ) * condEntropy μ Prod.fst Prod.snd - c * Real.sqrt N →
      ∀ (e : (Fin N → A) → (Fin N → B) → Fin m → Bool)
        (d : (Fin m → Bool) → (Fin N → B) → Fin N → A),
        (μ.power N).probOfPred
          (fun w => d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w) ≤ ε := by
  classical
  set H : ℝ := condEntropy μ Prod.fst Prod.snd with hH
  obtain ⟨c₁, hc₁⟩ := exists_nat_power_prob_sum_gt μ (fun z => -condSelfInfo μ z) (half_pos hε)
  obtain ⟨c₂, hc₂pow⟩ := exists_nat_gt (2 / ε)
  refine ⟨c₁ + c₂, fun N m hN hm e d => ?_⟩
  push_cast at hm
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  set t : ℝ := (N : ℝ) * H - c₁ * Real.sqrt N with ht
  have hsplit : (μ.power N).probOfPred
      (fun w => d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w) ≤
      (μ.power N).probOfPred
        (fun w => d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w ∧
          t ≤ ∑ i, condSelfInfo μ (w i)) +
      (μ.power N).probOfPred (fun w => ∑ i, condSelfInfo μ (w i) < t) := by
    apply probOfPred_le_add
    intro w hcorr
    by_cases hgt : t ≤ ∑ i, condSelfInfo μ (w i)
    · exact Or.inl ⟨hcorr, hgt⟩
    · exact Or.inr (lt_of_not_ge hgt)
  have hterm2 : (μ.power N).probOfPred (fun w => ∑ i, condSelfInfo μ (w i) < t) ≤ ε / 2 := by
    have hkey := hc₁ N
    have hexp : μ.expect (fun z => -condSelfInfo μ z) = -H := by
      rw [hH, ← expect_condSelfInfo_eq μ]
      simp only [FiniteProbSpace.expect, mul_neg, Finset.sum_neg_distrib]
    have hpredeq : ∀ w : Fin N → A × B,
        (∑ i, condSelfInfo μ (w i) < t) ↔
        ((N : ℝ) * μ.expect (fun z => -condSelfInfo μ z) + (c₁ : ℝ) * Real.sqrt (N : ℝ) <
          ∑ i, (fun z => -condSelfInfo μ z) (w i)) := by
      intro w
      have hsum : ∑ i, (fun z => -condSelfInfo μ z) (w i) = -∑ i, condSelfInfo μ (w i) := by
        simp only [Finset.sum_neg_distrib]
      rw [hsum, hexp, ht, mul_neg]
      constructor <;> intro h <;> linarith
    rw [probOfPred_congr (μ.power N) _ _ hpredeq]
    exact hkey
  have hc2_final : (2 : ℝ) ^ (-(c₂ : ℝ)) ≤ ε / 2 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have hP : (0 : ℝ) < (2 : ℝ) ^ c₂ := by positivity
    have hle : (c₂ : ℝ) ≤ (2 : ℝ) ^ c₂ := by
      calc (c₂ : ℝ) ≤ ((2 ^ c₂ : ℕ) : ℝ) := by exact_mod_cast c₂.lt_two_pow_self.le
        _ = (2 : ℝ) ^ c₂ := by push_cast; ring
    have h2 : (2 : ℝ) < (2 : ℝ) ^ c₂ * ε := by
      have hlt : (2 : ℝ) / ε < (2 : ℝ) ^ c₂ := lt_of_lt_of_le hc₂pow hle
      calc (2 : ℝ) = (2 / ε) * ε := by field_simp
        _ < (2 : ℝ) ^ c₂ * ε := mul_lt_mul_of_pos_right hlt hε
    have h3 : (1 : ℝ) ≤ (ε / 2) * (2 : ℝ) ^ c₂ := by nlinarith [h2]
    calc ((2 : ℝ) ^ c₂)⁻¹ = 1 * ((2 : ℝ) ^ c₂)⁻¹ := (one_mul _).symm
      _ ≤ ((ε / 2) * (2 : ℝ) ^ c₂) * ((2 : ℝ) ^ c₂)⁻¹ :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ε / 2 := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hP), mul_one]
  have hterm1 : (μ.power N).probOfPred
      (fun w => d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w ∧
        t ≤ ∑ i, condSelfInfo μ (w i)) ≤ ε / 2 := by
    refine le_trans (prob_correct_ge_le μ N m t e d) ?_
    have hexp_le : (m : ℝ) + (-t) ≤ -(c₂ : ℝ) := by
      have hnn : (0 : ℝ) ≤ (c₂ : ℝ) * (Real.sqrt N - 1) :=
        mul_nonneg (Nat.cast_nonneg _) (by linarith [hsqrt1])
      rw [ht]
      nlinarith [hm, hnn]
    calc (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (-t) = (2 : ℝ) ^ ((m : ℝ) + (-t)) := by
          rw [← Real.rpow_add (by norm_num)]
      _ ≤ (2 : ℝ) ^ (-(c₂ : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
      _ ≤ ε / 2 := hc2_final
  calc (μ.power N).probOfPred
        (fun w => d (e (Prod.fst ∘ w) (Prod.snd ∘ w)) (Prod.snd ∘ w) = Prod.fst ∘ w)
      ≤ _ + _ := hsplit
    _ ≤ ε / 2 + ε / 2 := add_le_add hterm1 hterm2
    _ = ε := by ring

end Kolmogorov
