import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.REChar
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveSLLN
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveSLLNBernoulli
import KolmogorovMathlib.AlgorithmicRandomness.StrongLaw
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveOpen
import KolmogorovMathlib.AlgorithmicRandomness.Measure

/-!
# Effective laws of large numbers, and the operations that preserve randomness

What a Martin-Löf random sequence must look like, and what may be done to it.

`tendsto_freqOne_of_isMartinLofRandom_uniform` and
`tendsto_freqOne_of_isMartinLofRandom_bernoulli` are the effective strong law: the frequency
of ones in a random sequence converges to `1/2`, respectively to the computable parameter `p`.
`not_isMartinLofRandom_of_re_char_seq` is the complementary negative fact — the characteristic
sequence of a computably enumerable set is never random — and `exists_isMartinLofRandom_uniform`
and `exists_singleton_not_isEffectivelyNull_uniform` (SUV Problem 72) say random sequences
exist.

The second half transports tests along the two one-bit operations, through the re-enumerations
`gTail` and `gCons` and their measure bounds, giving
`isMartinLofRandom_cons_of_isMartinLofRandom_uniform` and
`isMartinLofRandom_tail_of_isMartinLofRandom_uniform`: prepending a bit and deleting the first
bit both preserve randomness for the uniform measure.
-/

namespace Kolmogorov


open ComputableReals
open MeasureTheory Filter Topology
open scoped ENNReal

-- Theorem 32: The set of all bit sequences that do not have limit frequency 1/2 is an
-- effectively null set with respect to the uniform measure.
/-- In a Martin-Löf random sequence for the uniform measure the frequency of ones tends
to `1/2`. -/
lemma tendsto_freqOne_of_isMartinLofRandom_uniform {x : CantorSeq}
    (hx : IsMartinLofRandom uniformMeasure x) :
    Tendsto (fun n => freqOne x n) atTop (𝓝 (1/2 : ℚ)) := by
  by_contra h_not_tendsto
  have H1 := isEffectivelyNull_notTendsto_freqOne
  have H2 := (isEffectivelyNull_iff_forall_not_random isComputableMeasure_uniform
    {y : CantorSeq | ¬ Tendsto (fun n => freqOne y n) atTop (𝓝 (1/2 : ℚ))}).mp H1 x h_not_tendsto
  exact H2 hx

-- Theorem 34: Any ML-random sequence with respect to Bernoulli measure with computable
-- parameters q, p has limit frequency p.
/-- In a sequence random for a Bernoulli measure with computable parameter `p` the frequency of
ones tends to `p`. -/
lemma tendsto_freqOne_of_isMartinLofRandom_bernoulli {p : NNReal} (hp : p ≤ 1)
    (hp_comp : IsComputableReal (p : ℝ))
    {x : CantorSeq} (hx : IsMartinLofRandom (bernoulliMeasure p hp) x) :
    Tendsto (fun n => (freqOne x n : ℝ)) atTop (𝓝 (p : ℝ)) :=
  tendsto_freqOne_of_isMartinLofRandom_bernoulli' hp hp_comp hx

-- Theorem 36: The characteristic sequence of an r.e. set is not ML-random.
-- Let A be an enumerable set of natural numbers. Consider its characteristic
-- sequence a₀a₁a₂... (aᵢ = 0 for i ∉ A and aᵢ = 1 for i ∈ A).
-- This sequence is not ML-random (under uniform measure).
/-- The characteristic sequence of a computably enumerable set of naturals is not Martin-Löf
random for the uniform measure. -/
lemma not_isMartinLofRandom_of_re_char_seq (f : ℕ → Option ℕ) (hf : Computable f)
    (x : CantorSeq)
    (hx : ∀ n, x n = true ↔ ∃ i, f i = some n) :
    ¬ IsMartinLofRandom uniformMeasure x :=
  not_isMartinLofRandom_of_reChar hf hx

-- Theorem 37: There exists an ML-random sequence with respect to the uniform measure.
-- (The source states this for O'-computable sequences; we prove mere existence here.)
/-- Martin-Löf random sequences for the uniform measure exist. -/
lemma exists_isMartinLofRandom_uniform :
    ∃ x : CantorSeq, IsMartinLofRandom uniformMeasure x := by
  rcases exists_universal_martinLof_test isComputableMeasure_uniform with ⟨U, hU⟩
  -- The universal test has measure ≤ 2⁻ⁿ for each n, so ⋂ n, U n has measure 0
  have h_meas_zero : uniformMeasure (⋂ n, U n) = 0 := by
    have h_eff : IsEffectivelyNull uniformMeasure (⋂ n, U n) :=
      ⟨U, hU.1.1, Set.Subset.refl _, hU.1.2⟩
    exact h_eff.measure_eq_zero
  -- Since uniformMeasure is a probability measure (total mass = 1),
  -- the complement of a measure-zero set is nonempty.
  have h_compl_nonempty : (⋂ n, U n)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro h_eq
    rw [h_eq] at h_meas_zero
    simp at h_meas_zero
  rcases h_compl_nonempty with ⟨x, hx⟩
  refine ⟨x, fun V hV hx_in_V => ?_⟩
  -- x ∈ ⋂ n, V n, and V is an ML test, so x ∈ ⋂ n, U n by universality
  have h_null_V : IsEffectivelyNull uniformMeasure (⋂ n, V n) :=
    ⟨V, hV.1, Set.Subset.refl _, hV.2⟩
  have h_sub := hU.2 _ h_null_V
  exact hx (h_sub hx_in_V)

/-- **SUV Problem 72.** Some singleton is not effectively null for the uniform
measure. -/
theorem exists_singleton_not_isEffectivelyNull_uniform :
    ∃ w : CantorSeq, ¬ IsEffectivelyNull uniformMeasure {w} := by
  obtain ⟨w, hw⟩ := exists_isMartinLofRandom_uniform
  refine ⟨w, fun hnull => ?_⟩
  have hnrand :=
    (isEffectivelyNull_iff_forall_not_random isComputableMeasure_uniform {w}).mp hnull
  exact hnrand w (Set.mem_singleton w) hw

-- Theorem 35: Any sequence obtained from an ML-random sequence (uniform measure) by a
-- finite number of insertions/deletions/changes is also ML-random.
-- We state this for adding a single bit at the beginning, from which the rest follows.
/-- The bijection `Bool × ℕ ≃ ℕ` sending `(b, n)` to `2n` or `2n + 1` according to `b`. -/
def boolProdNatEquivNat : Bool × ℕ ≃ ℕ where
  toFun := fun ⟨b, n⟩ => if b then 2 * n + 1 else 2 * n
  invFun := fun n => ⟨n % 2 == 1, n / 2⟩
  left_inv := fun ⟨b, n⟩ => by
    cases b
    · dsimp
      have h3 : (2 * n) / 2 = n := by omega
      simp [h3]
    · dsimp
      have h3 : (2 * n + 1) / 2 = n := by omega
      simp [h3]
  right_inv := fun n => by
    have := Nat.div_add_mod n 2
    cases h_mod : n % 2
    · simp [h_mod]
      omega
    · rename_i m
      have : m = 0 := by omega
      subst this
      simp [h_mod]
      omega

/-- A sum over the naturals splits into the sums over the even and the odd indices. -/
lemma tsum_bool_prod_nat (f : ℕ → ℝ≥0∞) :
    ∑' n, f n = (∑' n, f (2 * n)) + (∑' n, f (2 * n + 1)) := by
  have H : ∑' n, f n = ∑' (p : Bool × ℕ), f (boolProdNatEquivNat p) :=
    (Equiv.tsum_eq boolProdNatEquivNat f).symm
  rw [H]
  have H_prod : ∑' (p : Bool × ℕ), f (boolProdNatEquivNat p)
      = ∑' (b : Bool) (n : ℕ), f (boolProdNatEquivNat (b, n)) := by
    exact @ENNReal.tsum_prod Bool ℕ (fun b n => f (boolProdNatEquivNat (b, n)))
  rw [H_prod, tsum_fintype, Fintype.sum_bool]
  dsimp [boolProdNatEquivNat]
  rw [add_comm]

/-- The enumeration obtained from `f` by prefixing each emitted string with one further bit, used
to transport a test through the shift. -/
def gTail (f : ℕ → Option BitString) (j : ℕ) : Option BitString :=
  (f (j / 2)).map fun s => (j % 2 == 1) :: s

/-- The shifted enumeration is computable when the original one is. -/
lemma computable_g_tail {f : ℕ → Option BitString} (hf : Computable f) :
    Computable (gTail f) := by
  apply Computable.option_map
  · exact hf.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp
  · exact (Primrec.list_cons.comp
      (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 1))
      Primrec.snd).to_comp

/-- Each set of the shifted enumeration has half the uniform measure of the set it comes
from. -/
lemma g_tail_measure_bound (f : ℕ → Option BitString) (j : ℕ) :
    (gTail f j).elim 0 (cantorMass uniformMeasure)
      = (2:ℝ≥0∞)⁻¹ * (f (j / 2)).elim 0 (cantorMass uniformMeasure) := by
  unfold gTail
  cases hfj : f (j / 2)
  · simp
  · rename_i s
    dsimp
    have H_s : cantorMass uniformMeasure ((j % 2 == 1) :: s)
        = (2:ℝ≥0∞)⁻¹ * cantorMass uniformMeasure s := by
      rw [cantorMass_uniformMeasure, cantorMass_uniformMeasure]
      simp only [List.length_cons, pow_add, pow_one, mul_comm]
    rw [H_s]

/-- The shifted enumeration has finite total uniform measure whenever the original one has. -/
lemma sum_g_tail (f : ℕ → Option BitString)
    (hf_sum : (∑' j, (f j).elim 0 (cantorMass uniformMeasure)) < ∞) :
    (∑' j, (gTail f j).elim 0 (cantorMass uniformMeasure)) < ∞ := by
  rw [tsum_bool_prod_nat]
  have H_even : ∑' (n : ℕ), (gTail f (2 * n)).elim 0 (cantorMass uniformMeasure)
      = (2:ℝ≥0∞)⁻¹ * ∑' n, (f n).elim 0 (cantorMass uniformMeasure) := by
    have H1 : (fun n => (gTail f (2 * n)).elim 0 (cantorMass uniformMeasure))
        = fun n => (2:ℝ≥0∞)⁻¹ * (f n).elim 0 (cantorMass uniformMeasure) := by
      ext n
      rw [g_tail_measure_bound]
      have H_div : (2 * n) / 2 = n := by omega
      rw [H_div]
    rw [H1]
    exact ENNReal.tsum_mul_left
  have H_odd : ∑' (n : ℕ), (gTail f (2 * n + 1)).elim 0 (cantorMass uniformMeasure)
      = (2:ℝ≥0∞)⁻¹ * ∑' n, (f n).elim 0 (cantorMass uniformMeasure) := by
    have H1 : (fun n => (gTail f (2 * n + 1)).elim 0 (cantorMass uniformMeasure))
        = fun n => (2:ℝ≥0∞)⁻¹ * (f n).elim 0 (cantorMass uniformMeasure) := by
      ext n
      rw [g_tail_measure_bound]
      have H_div : (2 * n + 1) / 2 = n := by omega
      rw [H_div]
    rw [H1]
    exact ENNReal.tsum_mul_left
  rw [H_even, H_odd, ← add_mul]
  have H_inv : (2:ℝ≥0∞)⁻¹ + (2:ℝ≥0∞)⁻¹ = 1 := by
    have : (2:ℝ≥0∞)⁻¹ + (2:ℝ≥0∞)⁻¹ = 2 * (2:ℝ≥0∞)⁻¹ := by
      calc (2:ℝ≥0∞)⁻¹ + (2:ℝ≥0∞)⁻¹
          = 1 * (2:ℝ≥0∞)⁻¹ + 1 * (2:ℝ≥0∞)⁻¹ := by rw [one_mul]
        _ = (1 + 1) * (2:ℝ≥0∞)⁻¹ := by rw [add_mul]
        _ = 2 * (2:ℝ≥0∞)⁻¹ := by norm_num
    rw [this]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [H_inv, one_mul]
  exact hf_sum

/-- The enumeration obtained from `f` by deleting the leading bit `b`, used to transport a test
through prepending a bit. -/
def gCons (b : Bool) (f : ℕ → Option BitString) (j : ℕ) : Option BitString :=
  (f j).bind fun s =>
    (s.head?).casesOn (some []) (fun c => bif c == b then some s.tail else none)

/-- The enumeration obtained by deleting a leading bit is computable when the original one is. -/
lemma computable_g_cons (b : Bool) {f : ℕ → Option BitString} (hf : Computable f) :
    Computable (gCons b f) := by
  apply Computable.option_bind hf
  have hc_head : Computable (fun (ps : ℕ × BitString) => ps.2.head?) :=
    (Primrec.list_head?.comp Primrec.snd).to_comp
  have h_none : Computable (fun (ps : ℕ × BitString) => (some [] : Option BitString)) :=
    (Primrec.const (some [])).to_comp
  have h_some : Computable₂ (fun (ps : ℕ × BitString) (c : Bool) =>
      bif c == b then some ps.2.tail else none) := by
    have h_cond : Computable (fun (psc : (ℕ × BitString) × Bool) => psc.2 == b) :=
      (Primrec.beq.comp Primrec.snd (Primrec.const b)).to_comp
    have h_then : Computable (fun (psc : (ℕ × BitString) × Bool) => some psc.1.2.tail) :=
      (Primrec.option_some.comp (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst))).to_comp
    have h_else : Computable (fun (psc : (ℕ × BitString) × Bool) => @none BitString) :=
      (Primrec.const none).to_comp
    exact Computable.cond h_cond h_then h_else
  exact Computable.option_casesOn hc_head h_none h_some

/-- Deleting the leading bit at most doubles the uniform measure of each enumerated set. -/
lemma g_cons_measure_bound (b : Bool) (f : ℕ → Option BitString) (j : ℕ) :
    (gCons b f j).elim 0 (cantorMass uniformMeasure)
      ≤ 2 * (f j).elim 0 (cantorMass uniformMeasure) := by
  unfold gCons
  cases hfj : f j
  · simp
  · rename_i s
    simp only [Option.bind_some]
    cases s with
    | nil =>
      have H : cantorMass uniformMeasure [] = 1 := by rw [cantorMass_uniformMeasure]; simp
      dsimp
      rw [H]
      calc (1 : ℝ≥0∞) ≤ 2 := by norm_num
        _ = 2 * 1 := by rw [mul_one]
    | cons c tail =>
      dsimp
      cases hc : c == b
      · simp only [Bool.cond_false, Option.elim_none]
        exact bot_le
      · simp only [Bool.cond_true, Option.elim_some]
        have h_eq : c = b := of_decide_eq_true hc
        have H_s : cantorMass uniformMeasure (c :: tail)
            = (2:ℝ≥0∞)⁻¹ * cantorMass uniformMeasure tail := by
          rw [cantorMass_uniformMeasure, cantorMass_uniformMeasure]
          simp only [List.length_cons, pow_add, pow_one, mul_comm]
        rw [H_s, ← mul_assoc]
        have H_two : (2:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [H_two, one_mul]

/-- Deleting the leading bit keeps the total uniform measure of the enumeration finite. -/
lemma sum_g_cons (b : Bool) (f : ℕ → Option BitString)
    (hf_sum : (∑' j, (f j).elim 0 (cantorMass uniformMeasure)) < ∞) :
    (∑' j, (gCons b f j).elim 0 (cantorMass uniformMeasure)) < ∞ := by
  have H : (∑' j, (gCons b f j).elim 0 (cantorMass uniformMeasure))
      ≤ 2 * ∑' j, (f j).elim 0 (cantorMass uniformMeasure) := by
    have H_mul : 2 * (∑' (j : ℕ), (f j).elim 0 (cantorMass uniformMeasure))
        = ∑' j, 2 * (f j).elim 0 (cantorMass uniformMeasure) := by
      exact ENNReal.tsum_mul_left.symm
    rw [H_mul]
    exact ENNReal.tsum_le_tsum (fun j => g_cons_measure_bound b f j)
  exact lt_of_le_of_lt H (ENNReal.mul_lt_top (by norm_num) hf_sum)

/-- Prepending one bit to a uniformly random sequence keeps it Martin-Löf random. -/
lemma isMartinLofRandom_cons_of_isMartinLofRandom_uniform (b : Bool) {x : CantorSeq}
    (hx : IsMartinLofRandom uniformMeasure x) :
    IsMartinLofRandom uniformMeasure (fun n => if n = 0 then b else x (n - 1)) := by
  by_contra h_not_rand
  rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_uniform] at h_not_rand
  rcases h_not_rand with ⟨f, hf_comp, hf_sum, hf_inf⟩
  have h_not_rand_x : ¬ IsMartinLofRandom uniformMeasure x := by
    rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_uniform]
    use gCons b f
    refine ⟨computable_g_cons b hf_comp, sum_g_cons b f hf_sum, ?_⟩
    intro h_fin
    apply hf_inf
    have H_sub :
        {i | (fun n => if n = 0 then b else x (n - 1)) ∈ (f i).elim ∅ cantorCylinder} ⊆
        {j | x ∈ (gCons b f j).elim ∅ cantorCylinder} := by
      intro i hi
      simp only [Set.mem_ofPred_eq] at hi ⊢
      cases hfi : f i
      · rw [hfi] at hi
        simp only [Option.elim_none, Set.mem_empty_iff_false] at hi
      · rename_i s
        rw [hfi] at hi
        simp only [Option.elim_some] at hi
        dsimp [cantorCylinder, IsCantorPrefix] at hi
        unfold gCons
        simp only [hfi, Option.bind_some]
        cases s with
        | nil =>
          dsimp [cantorCylinder, IsCantorPrefix]
          intro k hk
          have hk0 : k < 0 := hk
          omega
        | cons c tail =>
          dsimp [cantorCylinder, IsCantorPrefix]
          have h_x0 : (fun n => if n = 0 then b else x (n - 1)) 0 = b := ite_eq_left rfl
          have h0_lt : 0 < (c :: tail).length := Nat.zero_lt_succ _
          have hk_0 : (fun n => if n = 0 then b else x (n - 1)) 0 = (c :: tail)[0]'h0_lt := by
            have H_mem := hi 0 h0_lt
            exact H_mem
          have h_c_eq_b : c = b := by
            have h_c_val : (c :: tail)[0]'h0_lt = c := rfl
            rw [← h_x0, hk_0, h_c_val]
          have hc_dec : (c == b) = true := decide_eq_true h_c_eq_b
          rw [hc_dec]
          intro k hk
          have hk_lt : k + 1 < (c :: tail).length := Nat.succ_lt_succ hk
          have hk_tail := hi (k + 1) hk_lt
          have h_x_k : (if k + 1 = 0 then b else x (k + 1 - 1)) = x k := by simp
          rw [h_x_k] at hk_tail
          have h_s_tail : (c :: tail)[k + 1]'hk_lt = tail[k]'hk := rfl
          rw [h_s_tail] at hk_tail
          exact hk_tail
    exact Set.Finite.subset h_fin H_sub
  exact h_not_rand_x hx

/-- The tail of a uniformly Martin-Löf random sequence is Martin-Löf random. -/
lemma isMartinLofRandom_tail_of_isMartinLofRandom_uniform {x : CantorSeq}
    (hx : IsMartinLofRandom uniformMeasure x) :
    IsMartinLofRandom uniformMeasure (fun n => x (n + 1)) := by
  by_contra h_not_rand
  rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_uniform] at h_not_rand
  rcases h_not_rand with ⟨f, hf_comp, hf_sum, hf_inf⟩
  have h_not_rand_x : ¬ IsMartinLofRandom uniformMeasure x := by
    rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_uniform]
    use gTail f
    refine ⟨computable_g_tail hf_comp, sum_g_tail f hf_sum, ?_⟩
    intro h_fin
    apply hf_inf
    let j_fun := fun i => if x 0 then 2 * i + 1 else 2 * i
    have h_inj : Function.Injective j_fun := by
      intro i1 i2 h
      dsimp [j_fun] at h
      split at h
      · omega
      · omega
    have H_sub : {i | (fun n => x (n + 1)) ∈ (f i).elim ∅ cantorCylinder} ⊆
        j_fun ⁻¹' {j | x ∈ (gTail f j).elim ∅ cantorCylinder} := by
      intro i hi
      simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hi ⊢
      cases hfi : f i
      · rw [hfi] at hi
        simp only [Option.elim_none, Set.mem_empty_iff_false] at hi
      · rename_i s
        rw [hfi] at hi
        simp only [Option.elim_some] at hi
        dsimp [cantorCylinder, IsCantorPrefix] at hi
        let j := j_fun i
        unfold gTail
        have hj_div : j / 2 = i := by
          dsimp [j, j_fun]
          split
          · omega
          · omega
        have hj_mod : (j % 2 == 1) = x 0 := by
          dsimp [j, j_fun]
          split
          · rename_i hx0
            have : (2 * i + 1) % 2 = 1 := by omega
            have h1 : ((2 * i + 1) % 2 == 1) = true := decide_eq_true this
            rw [h1, hx0]
          · rename_i hx0
            have : (2 * i) % 2 = 0 := by omega
            have h1 : ((2 * i) % 2 == 1) = false := by simp [this]
            have hx0_false : x 0 = false := Bool.eq_false_of_ne_true hx0
            rw [h1, hx0_false]
        rw [hj_div, hfi]
        simp only [Option.map, Option.elim_some]
        dsimp [cantorCylinder, IsCantorPrefix]
        rw [hj_mod]
        intro k hk
        cases k
        · rfl
        · rename_i k
          have hk_lt : k < s.length := by omega
          have H_hi := hi k hk_lt
          exact H_hi
    exact (Set.Finite.preimage h_inj.injOn h_fin).subset H_sub
  exact h_not_rand_x hx

end Kolmogorov
