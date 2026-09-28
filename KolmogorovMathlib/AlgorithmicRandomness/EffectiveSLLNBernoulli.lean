import KolmogorovMathlib.AlgorithmicRandomness.EffectiveSLLN
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable

/-!
# The effective strong law for a Bernoulli measure with computable parameter

This file proves SUV Theorem 34: if `p` is a computable real in `[0, 1]`, then every
sequence that is Martin-Löf random for the Bernoulli measure with parameter `p` has
limit frequency of ones equal to `p`.

The construction mirrors the uniform case in `EffectiveSLLN.lean`.  The only new
ingredient is that the deviation test cannot mention `p` itself, which is merely a
computable real; instead it compares the observed frequency with a rational
approximation `pApp approx k` of `p` accurate to `1/(3(k+1))`, and asks for a deviation
of at least `2/(3(k+1))`.  Such a deviation forces a true deviation of at least
`1/(3(k+1))`, which is what Hoeffding's inequality bounds; conversely a true deviation
of at least `1/(k+1)` is detected by the test.
-/

namespace Kolmogorov


open ComputableReals
open MeasureTheory ProbabilityTheory Filter Topology ENNReal

/-! ### The rational approximation of the parameter -/

/-- The rational approximation of the parameter used at level `k`, accurate to
`1/(3(k+1))`. -/
def pApp (approx : ℚ → ℚ) (k : ℕ) : ℚ := approx (1 / (3 * ((k : ℚ) + 1)))

/-- The sequence of rational accuracy levels `1 / (3(k+1))` is computable. -/
lemma computable_ratLevel : Computable (fun k : ℕ => (1 : ℚ) / (3 * ((k : ℚ) + 1))) := by
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun k : ℕ => 3 * (k + 1))
    (Computable.const 1)
    (Primrec.nat_mul.comp (Primrec.const 3) (Primrec.succ.comp Primrec.id)).to_comp
    (fun k => by positivity) (fun k => by push_cast; ring)

/-- The rational approximations of the Bernoulli parameter at the accuracy levels form a
computable sequence. -/
lemma computable_pApp {approx : ℚ → ℚ} (h : Computable approx) :
    Computable (pApp approx) :=
  h.comp computable_ratLevel

/-! ### The deviation predicate -/

/-- `devBoolP approx k n c` says that a string of length `n` with `c` ones deviates from
the rational approximation `pApp approx k` by at least `2/(3(k+1))`. -/
def devBoolP (approx : ℚ → ℚ) (k n c : ℕ) : Bool :=
  (2 * n * (pApp approx k).den
      - 3 * (k + 1)
        * ((c : ℤ) * ((pApp approx k).den : ℤ) - (n : ℤ) * (pApp approx k).num).natAbs) == 0

/-- The deviation test, unfolded into an inequality between integers. -/
lemma devBoolP_iff (approx : ℚ → ℚ) (k n c : ℕ) :
    devBoolP approx k n c = true ↔
      2 * n * (pApp approx k).den
        ≤ 3 * (k + 1)
          * ((c : ℤ) * ((pApp approx k).den : ℤ) - (n : ℤ) * (pApp approx k).num).natAbs := by
  unfold devBoolP
  rw [beq_iff_eq, Nat.sub_eq_zero_iff_le]

/-- The absolute deviation of the empirical frequency `c / n` from the approximated parameter,
written as a single rational quotient. -/
lemma devAbsP_eq (approx : ℚ → ℚ) (k n c : ℕ) (hn : 0 < n) :
    |(c : ℚ) / n - pApp approx k|
      = (((c : ℤ) * ((pApp approx k).den : ℤ) - (n : ℤ) * (pApp approx k).num).natAbs : ℚ)
        / (n * (pApp approx k).den) := by
  set q := pApp approx k with hq
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hb : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.pos
  have hnum : (q.num : ℚ) = q * (q.den : ℚ) := (Rat.mul_den_eq_num q).symm
  have hstep : (c : ℚ) / n - q
      = ((c : ℚ) * (q.den : ℚ) - (n : ℚ) * (q.num : ℚ)) / ((n : ℚ) * (q.den : ℚ)) := by
    rw [hnum]
    field_simp
  calc |(c : ℚ) / n - q|
      = |((c : ℚ) * q.den - (n : ℚ) * q.num) / ((n : ℚ) * q.den)| := by rw [hstep]
    _ = |(c : ℚ) * q.den - (n : ℚ) * q.num| / ((n : ℚ) * q.den) := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < (n : ℚ) * q.den)]
    _ = _ := by
        congr 1
        rw [Nat.cast_natAbs]
        push_cast
        ring_nf

/-- The deviation test succeeds exactly when the empirical frequency differs from the approximated
parameter by at least `2 / (3(k+1))`. -/
lemma devBoolP_iff_rat (approx : ℚ → ℚ) (k n c : ℕ) (hn : 0 < n) :
    devBoolP approx k n c = true ↔
      2 / (3 * ((k : ℚ) + 1)) ≤ |(c : ℚ) / n - pApp approx k| := by
  set q := pApp approx k with hq
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hb : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.pos
  rw [devBoolP_iff, devAbsP_eq approx k n c hn,
    div_le_div_iff₀ (by positivity : (0 : ℚ) < 3 * ((k : ℚ) + 1))
      (by positivity : (0 : ℚ) < (n : ℚ) * q.den)]
  constructor
  · intro h
    have hcast : ((2 * n * q.den : ℕ) : ℚ)
        ≤ ((3 * (k + 1) * ((c : ℤ) * (q.den : ℤ) - (n : ℤ) * q.num).natAbs : ℕ) : ℚ) := by
      exact_mod_cast h
    push_cast at hcast ⊢
    nlinarith [hcast]
  · intro h
    have hcast : ((2 * n * q.den : ℕ) : ℚ)
        ≤ ((3 * (k + 1) * ((c : ℤ) * (q.den : ℤ) - (n : ℤ) * q.num).natAbs : ℕ) : ℚ) := by
      push_cast
      nlinarith [h]
    exact_mod_cast hcast

/-- The set of sequences whose length-`n` prefix deviates at level `k`. -/
def devSetP (approx : ℚ → ℚ) (k n : ℕ) : Set CantorSeq :=
  {w | devBoolP approx k n ((cantorPrefix w n).count true) = true}

/-- Membership in the deviation set is decided by the number of ones in the length-`n` prefix. -/
lemma mem_devSetP_iff_prefix (approx : ℚ → ℚ) (k n : ℕ) (w : CantorSeq) :
    w ∈ devSetP approx k n ↔ devBoolP approx k n ((cantorPrefix w n).count true) = true :=
  Iff.rfl

/-! ### Computability of the deviation test -/

/-- The deviation test is computable in the accuracy level, the length and the count. -/
lemma computable_devBoolP {α : Type} [Primcodable α] {approx : ℚ → ℚ}
    (happrox : Computable approx) {k n c : α → ℕ}
    (hk : Computable k) (hn : Computable n) (hc : Computable c) :
    Computable (fun a => devBoolP approx (k a) (n a) (c a)) := by
  have hq : Computable (fun a => pApp approx (k a)) := (computable_pApp happrox).comp hk
  have hden : Computable (fun a => (pApp approx (k a)).den) := computable_ratDen.comp hq
  have hnum : Computable (fun a => (pApp approx (k a)).num) := computable_ratNum.comp hq
  have hlhs : Computable (fun a => 2 * n a * (pApp approx (k a)).den) :=
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) hn) hden
  have hcz : Computable (fun a => ((c a : ℤ))) := ComputableReals.primrec_natCastInt.to_comp.comp hc
  have hnz : Computable (fun a => ((n a : ℤ))) := ComputableReals.primrec_natCastInt.to_comp.comp hn
  have hdz : Computable (fun a => (((pApp approx (k a)).den : ℤ))) :=
    ComputableReals.primrec_natCastInt.to_comp.comp hden
  have hp1 : Computable (fun a => (c a : ℤ) * ((pApp approx (k a)).den : ℤ)) :=
    Computable₂.comp primrec_intMul.to_comp hcz hdz
  have hp2 : Computable (fun a => (n a : ℤ) * (pApp approx (k a)).num) :=
    Computable₂.comp primrec_intMul.to_comp hnz hnum
  have hdiff : Computable (fun a =>
      (c a : ℤ) * ((pApp approx (k a)).den : ℤ) - (n a : ℤ) * (pApp approx (k a)).num) :=
    Computable₂.comp primrec_intSub.to_comp hp1 hp2
  have habs : Computable (fun a =>
      ((c a : ℤ) * ((pApp approx (k a)).den : ℤ)
        - (n a : ℤ) * (pApp approx (k a)).num).natAbs) :=
    ComputableReals.primrec_intNatAbs.to_comp.comp hdiff
  have hk3 : Computable (fun a => 3 * (k a + 1)) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 3) (Computable.succ.comp hk)
  have hrhs : Computable (fun a => 3 * (k a + 1)
      * ((c a : ℤ) * ((pApp approx (k a)).den : ℤ)
        - (n a : ℤ) * (pApp approx (k a)).num).natAbs) :=
    Primrec.nat_mul.to_comp.comp hk3 habs
  have hsub : Computable (fun a => 2 * n a * (pApp approx (k a)).den
      - 3 * (k a + 1) * ((c a : ℤ) * ((pApp approx (k a)).den : ℤ)
        - (n a : ℤ) * (pApp approx (k a)).num).natAbs) :=
    Primrec.nat_sub.to_comp.comp hlhs hrhs
  exact Primrec.beq.to_comp.comp hsub (Computable.const 0)

/-- The computable enumeration of the deviating cylinders of level `k` and length at
least `T`. -/
def devEnumP (approx : ℚ → ℚ) (k T j : ℕ) : Option BitString :=
  bif devBoolP approx k (T + j.unpair.1) ((bitsAux (T + j.unpair.1) j.unpair.2).2.2)
    then some ((bitsAux (T + j.unpair.1) j.unpair.2).2.1) else none

/-- The enumeration of the cylinders making up the deviation sets is computable. -/
lemma computable_devEnumP {α : Type} [Primcodable α] {approx : ℚ → ℚ}
    (happrox : Computable approx) {k T j : α → ℕ}
    (hk : Computable k) (hT : Computable T) (hj : Computable j) :
    Computable (fun a => devEnumP approx (k a) (T a) (j a)) := by
  have hj1 : Computable (fun a => (j a).unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp hj
  have hj2 : Computable (fun a => (j a).unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp hj
  have hn : Computable (fun a => T a + (j a).unpair.1) :=
    Primrec.nat_add.to_comp.comp hT hj1
  have haux : Computable (fun a => bitsAux (T a + (j a).unpair.1) (j a).unpair.2) :=
    computable_bitsAux.comp hn hj2
  have hcnt : Computable (fun a => (bitsAux (T a + (j a).unpair.1) (j a).unpair.2).2.2) :=
    Computable.snd.comp (Computable.snd.comp haux)
  have hstr : Computable (fun a => (bitsAux (T a + (j a).unpair.1) (j a).unpair.2).2.1) :=
    Computable.fst.comp (Computable.snd.comp haux)
  have hdev : Computable (fun a => devBoolP approx (k a) (T a + (j a).unpair.1)
      (bitsAux (T a + (j a).unpair.1) (j a).unpair.2).2.2) :=
    computable_devBoolP happrox hk hn hcnt
  exact Computable.cond_some_none hdev hstr

/-- The cylinders enumerated from stage `T` on cover exactly the union of the deviation sets of
length at least `T`. -/
lemma iUnion_devEnumP (approx : ℚ → ℚ) (k T : ℕ) :
    (⋃ j, (devEnumP approx k T j).elim ∅ cantorCylinder)
      = ⋃ j : ℕ, devSetP approx k (T + j) := by
  ext w
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    set n := T + j.unpair.1 with hn
    by_cases hdev : devBoolP approx k n ((bitsAux n j.unpair.2).2.2) = true
    · refine ⟨j.unpair.1, ?_⟩
      rw [devEnumP] at hj
      rw [hdev] at hj
      simp only [cond_true, Option.elim_some] at hj
      have hpref : cantorPrefix w n = natToBits n j.unpair.2 := by
        have hlen : (natToBits n j.unpair.2).length = n := natToBits_length _ _
        have h := (isCantorPrefix_iff_cantorPrefix_eq (natToBits n j.unpair.2) w).1 hj
        rw [hlen] at h
        exact h
      rw [mem_devSetP_iff_prefix, ← hn, hpref, ← bitsAux_count]
      exact hdev
    · exfalso
      rw [devEnumP] at hj
      have hfalse : devBoolP approx k n ((bitsAux n j.unpair.2).2.2) = false := by
        simpa using hdev
      rw [hfalse] at hj
      simp at hj
  · rintro ⟨j, hj⟩
    set n := T + j with hn
    rw [mem_devSetP_iff_prefix] at hj
    obtain ⟨i, hi⟩ := exists_natToBits (cantorPrefix w n)
    rw [cantorPrefix_length] at hi
    refine ⟨Nat.pair j i, ?_⟩
    have hdev : devBoolP approx k n ((bitsAux n i).2.2) = true := by
      rw [bitsAux_count, hi]
      exact hj
    rw [devEnumP, Nat.unpair_pair]
    simp only [← hn, hdev, cond_true, Option.elim_some]
    have hbits : (bitsAux n i).2.1 = cantorPrefix w n := hi
    rw [hbits]
    exact mem_cantorCylinder_cantorPrefix w n

/-! ### The effectively null family -/

/-- The threshold from which the tail union of the level-`k` deviation sets has measure
at most `2⁻ᵐ`.  It is the threshold of `EffectiveSLLN` for the level `3k+2`. -/
def devThreshP (k m : ℕ) : ℕ := devThresh (3 * k + 2) m

/-- The tail union of the level-`k` deviation sets from `devThreshP k m` on. -/
def devUnionP (approx : ℚ → ℚ) (k m : ℕ) : Set CantorSeq :=
  ⋃ j : ℕ, devSetP approx k (devThreshP k m + j)

/-- The uniformly effective open family witnessing effective nullity. -/
def devWP (approx : ℚ → ℚ) (i : ℕ) : Set CantorSeq :=
  devUnionP approx i.unpair.1 i.unpair.2

/-- The sequences that deviate at level `k` infinitely often. -/
def devInfSetP (approx : ℚ → ℚ) (k : ℕ) : Set CantorSeq :=
  {x | ∀ M, ∃ n, M ≤ n ∧ x ∈ devSetP approx k n}

/-- The threshold length chosen for accuracy `k` and level `m` is computable. -/
lemma computable_devThreshP {α : Type} [Primcodable α] {k m : α → ℕ}
    (hk : Computable k) (hm : Computable m) :
    Computable (fun a => devThreshP (k a) (m a)) := by
  have h : Computable (fun a => 3 * k a + 2) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 3) hk) (Computable.const 2)
  exact computable_devThresh h hm

/-- The deviation test levels form a uniformly effectively open family. -/
lemma isUniformlyEffectiveOpen_devWP {approx : ℚ → ℚ} (happrox : Computable approx) :
    IsUniformlyEffectiveOpen (devWP approx) := by
  refine ⟨fun i j => devEnumP approx i.unpair.1 (devThreshP i.unpair.1 i.unpair.2) j,
    ?_, fun i => ?_⟩
  · have hp1 : Computable (fun q : ℕ × ℕ => q.1.unpair.1) :=
      (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.fst
    have hp2 : Computable (fun q : ℕ × ℕ => q.1.unpair.2) :=
      (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst
    exact computable_devEnumP happrox hp1 (computable_devThreshP hp1 hp2) Computable.snd
  · exact (iUnion_devEnumP approx i.unpair.1 (devThreshP i.unpair.1 i.unpair.2)).symm

/-- The set of sequences deviating infinitely often at accuracy `k` is contained in every level of
the corresponding test. -/
lemma devInfSetP_subset_iInter (approx : ℚ → ℚ) (k : ℕ) :
    devInfSetP approx k ⊆ ⋂ m, devWP approx (Nat.pair k m) := by
  intro x hx
  refine Set.mem_iInter.2 fun m => ?_
  have hw : devWP approx (Nat.pair k m) = devUnionP approx k m := by
    simp [devWP, Nat.unpair_pair]
  rw [hw]
  obtain ⟨n, hn, hxn⟩ := hx (devThreshP k m)
  refine Set.mem_iUnion.2 ⟨n - devThreshP k m, ?_⟩
  have hsum : devThreshP k m + (n - devThreshP k m) = n := by omega
  rw [hsum]
  exact hxn

/-! ### Probabilistic estimates for the Bernoulli measure -/

/-- Each coordinate has expectation `p` under the Bernoulli measure with parameter `p`. -/
lemma bernoulli_integral_bitVal (p : NNReal) (hp : p ≤ 1) (i : ℕ) :
    ∫ w, bitVal (w i) ∂(bernoulliMeasure p hp) = (p : ℝ) := by
  rw [(bernoulli_identDistrib p hp i).integral_eq, bernoulli_integral_coord p hp]

/-- A centred Bernoulli coordinate is sub-Gaussian with variance proxy `1/4`. -/
lemma hasSubgaussian_bernoulli_centered (p : NNReal) (hp : p ≤ 1) (i : ℕ) :
    HasSubgaussianMGF (fun w : CantorSeq => bitVal (w i) - (p : ℝ)) (1 / 4 : NNReal)
      (bernoulliMeasure p hp) := by
  have hm : AEMeasurable (fun w : CantorSeq => bitVal (w i)) (bernoulliMeasure p hp) :=
    (measurable_bitVal.comp (measurable_pi_apply i)).aemeasurable
  have hb : ∀ᵐ w ∂(bernoulliMeasure p hp), bitVal (w i) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards with w
    cases w i <;> simp [bitVal]
  have h := hasSubgaussianMGF_of_mem_Icc (μ := bernoulliMeasure p hp)
    (X := fun w : CantorSeq => bitVal (w i)) hm hb
  rw [bernoulli_integral_bitVal p hp i] at h
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = (1 / 4 : NNReal) := by
    simp
    norm_num
  rwa [hc] at h

/-- The negative of a centred Bernoulli coordinate is sub-Gaussian with variance proxy `1/4`. -/
lemma hasSubgaussian_bernoulli_centered_neg (p : NNReal) (hp : p ≤ 1) (i : ℕ) :
    HasSubgaussianMGF (fun w : CantorSeq => (p : ℝ) - bitVal (w i)) (1 / 4 : NNReal)
      (bernoulliMeasure p hp) := by
  have h := (hasSubgaussian_bernoulli_centered p hp i).neg
  have heq : (-(fun w : CantorSeq => bitVal (w i) - (p : ℝ)))
      = fun w : CantorSeq => (p : ℝ) - bitVal (w i) := by
    funext w; simp [neg_sub]
  rwa [heq] at h

/-- The centred coordinates are independent under a Bernoulli measure. -/
lemma iIndepFun_bernoulli_centered (p : NNReal) (hp : p ≤ 1) :
    iIndepFun (fun (i : ℕ) (w : CantorSeq) => bitVal (w i) - (p : ℝ))
      (bernoulliMeasure p hp) := by
  have h := bernoulli_iIndepFun p hp
  have h2 := h.comp (fun (_ : ℕ) (x : ℝ) => x - (p : ℝ))
    (fun _ => measurable_id.sub_const _)
  simpa [Function.comp] using h2

/-- The negatives of the centred coordinates are independent under a Bernoulli measure. -/
lemma iIndepFun_bernoulli_centered_neg (p : NNReal) (hp : p ≤ 1) :
    iIndepFun (fun (i : ℕ) (w : CantorSeq) => (p : ℝ) - bitVal (w i))
      (bernoulliMeasure p hp) := by
  have h := bernoulli_iIndepFun p hp
  have h2 := h.comp (fun (_ : ℕ) (x : ℝ) => (p : ℝ) - x)
    (fun _ => measurable_const.sub measurable_id)
  simpa [Function.comp] using h2

/-! ### The measure of a deviation set -/

/-- A deviation of the empirical frequency forces a large deviation of the centred sum in one of
the two directions. -/
lemma devSetP_subset_union {p : NNReal} {approx : ℚ → ℚ}
    (happrox : ∀ ε : ℚ, 0 < ε → |(approx ε : ℝ) - (p : ℝ)| ≤ (ε : ℝ)) (k n : ℕ) :
    devSetP approx k n
      ⊆ {w : CantorSeq | (n : ℝ) / (3 * ((k : ℝ) + 1))
            ≤ ∑ i ∈ Finset.range n, (bitVal (w i) - (p : ℝ))}
        ∪ {w : CantorSeq | (n : ℝ) / (3 * ((k : ℝ) + 1))
            ≤ ∑ i ∈ Finset.range n, ((p : ℝ) - bitVal (w i))} := by
  intro w hw
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left; simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (0 : ℝ) < 3 * ((k : ℝ) + 1) := by positivity
  set c := (cantorPrefix w n).count true with hc
  have hqrat : 2 / (3 * ((k : ℚ) + 1)) ≤ |(c : ℚ) / n - pApp approx k| :=
    (devBoolP_iff_rat approx k n c hn).1 hw
  have hqreal : 2 / (3 * ((k : ℝ) + 1)) ≤ |(c : ℝ) / n - ((pApp approx k : ℚ) : ℝ)| := by
    have h := (Rat.cast_le (K := ℝ)).2 hqrat
    push_cast at h
    exact h
  have happ : |((pApp approx k : ℚ) : ℝ) - (p : ℝ)| ≤ 1 / (3 * ((k : ℝ) + 1)) := by
    have hpos : (0 : ℚ) < 1 / (3 * ((k : ℚ) + 1)) := by positivity
    have h := happrox _ hpos
    rw [pApp]
    push_cast at h ⊢
    exact h
  have hr : 1 / (3 * ((k : ℝ) + 1)) ≤ |(c : ℝ) / n - (p : ℝ)| := by
    have htri : |(c : ℝ) / n - ((pApp approx k : ℚ) : ℝ)|
        ≤ |(c : ℝ) / n - (p : ℝ)| + |((pApp approx k : ℚ) : ℝ) - (p : ℝ)| := by
      have h1 := abs_sub_le ((c : ℝ) / n) ((p : ℝ)) (((pApp approx k : ℚ) : ℝ))
      have h2 : |(p : ℝ) - ((pApp approx k : ℚ) : ℝ)|
          = |((pApp approx k : ℚ) : ℝ) - (p : ℝ)| := abs_sub_comm _ _
      linarith [h1, h2.le, h2.ge]
    have hsplit : 2 / (3 * ((k : ℝ) + 1))
        ≤ |(c : ℝ) / n - (p : ℝ)| + 1 / (3 * ((k : ℝ) + 1)) := by
      linarith [hqreal, htri, happ]
    have h2 : (2 : ℝ) / (3 * ((k : ℝ) + 1))
        = 1 / (3 * ((k : ℝ) + 1)) + 1 / (3 * ((k : ℝ) + 1)) := by
      field_simp
      ring
    linarith [hsplit, h2.le, h2.ge]
  have hsum1 : ∑ i ∈ Finset.range n, (bitVal (w i) - (p : ℝ)) = (c : ℝ) - n * p := by
    rw [Finset.sum_sub_distrib, sum_bitVal_eq_count, ← hc, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hsum2 : ∑ i ∈ Finset.range n, ((p : ℝ) - bitVal (w i)) = (n : ℝ) * p - c := by
    rw [Finset.sum_sub_distrib, sum_bitVal_eq_count, ← hc, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  rcases le_abs.1 hr with h | h
  · left
    have h2 : (n : ℝ) * (1 / (3 * ((k : ℝ) + 1))) ≤ (n : ℝ) * ((c : ℝ) / n - (p : ℝ)) :=
      mul_le_mul_of_nonneg_left h hn'.le
    have h3 : (n : ℝ) * ((c : ℝ) / n - (p : ℝ)) = (c : ℝ) - n * p := by
      field_simp
    have h4 : (n : ℝ) * (1 / (3 * ((k : ℝ) + 1))) = (n : ℝ) / (3 * ((k : ℝ) + 1)) := by ring
    change (n : ℝ) / (3 * ((k : ℝ) + 1)) ≤ _
    rw [hsum1]
    linarith
  · right
    have h2 : (n : ℝ) * (1 / (3 * ((k : ℝ) + 1))) ≤ (n : ℝ) * (-((c : ℝ) / n - (p : ℝ))) :=
      mul_le_mul_of_nonneg_left h hn'.le
    have h3 : (n : ℝ) * (-((c : ℝ) / n - (p : ℝ))) = (n : ℝ) * p - c := by
      field_simp
      ring
    have h4 : (n : ℝ) * (1 / (3 * ((k : ℝ) + 1))) = (n : ℝ) / (3 * ((k : ℝ) + 1)) := by ring
    change (n : ℝ) / (3 * ((k : ℝ) + 1)) ≤ _
    rw [hsum2]
    linarith

/-- Hoeffding's bound for the deviation sets: their Bernoulli measure decays exponentially in the
length. -/
lemma measure_devSetP_le {p : NNReal} (hp : p ≤ 1) {approx : ℚ → ℚ}
    (happrox : ∀ ε : ℚ, 0 < ε → |(approx ε : ℝ) - (p : ℝ)| ≤ (ε : ℝ)) (k n : ℕ) :
    bernoulliMeasure p hp (devSetP approx k n)
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * n) / (((3 * k + 2 : ℕ) : ℝ) + 1) ^ 2)) := by
  have hcast : (((3 * k + 2 : ℕ) : ℝ) + 1) = 3 * ((k : ℝ) + 1) := by push_cast; ring
  rw [hcast]
  set A : Set CantorSeq :=
    {w : CantorSeq | (n : ℝ) / (3 * ((k : ℝ) + 1))
      ≤ ∑ i ∈ Finset.range n, (bitVal (w i) - (p : ℝ))} with hA
  set B : Set CantorSeq :=
    {w : CantorSeq | (n : ℝ) / (3 * ((k : ℝ) + 1))
      ≤ ∑ i ∈ Finset.range n, ((p : ℝ) - bitVal (w i))} with hB
  have hAle : bernoulliMeasure p hp A
      ≤ ENNReal.ofReal (Real.exp (-(2 * n) / (3 * ((k : ℝ) + 1)) ^ 2)) := by
    have h := measureReal_sum_ge (bernoulliMeasure p hp) (3 * k + 2) n
      (fun i w => bitVal (w i) - (p : ℝ))
      (iIndepFun_bernoulli_centered p hp) (hasSubgaussian_bernoulli_centered p hp)
    rw [hcast] at h
    have hfin : bernoulliMeasure p hp A ≠ ⊤ := measure_ne_top _ _
    calc bernoulliMeasure p hp A = ENNReal.ofReal ((bernoulliMeasure p hp).real A) :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  have hBle : bernoulliMeasure p hp B
      ≤ ENNReal.ofReal (Real.exp (-(2 * n) / (3 * ((k : ℝ) + 1)) ^ 2)) := by
    have h := measureReal_sum_ge (bernoulliMeasure p hp) (3 * k + 2) n
      (fun i w => (p : ℝ) - bitVal (w i))
      (iIndepFun_bernoulli_centered_neg p hp) (hasSubgaussian_bernoulli_centered_neg p hp)
    rw [hcast] at h
    have hfin : bernoulliMeasure p hp B ≠ ⊤ := measure_ne_top _ _
    calc bernoulliMeasure p hp B = ENNReal.ofReal ((bernoulliMeasure p hp).real B) :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  have hsub : bernoulliMeasure p hp (devSetP approx k n) ≤ bernoulliMeasure p hp (A ∪ B) :=
    measure_mono (devSetP_subset_union happrox k n)
  refine hsub.trans ?_
  refine (measure_union_le A B).trans ?_
  have hexp : (0 : ℝ) ≤ Real.exp (-(2 * n) / (3 * ((k : ℝ) + 1)) ^ 2) := (Real.exp_pos _).le
  calc bernoulliMeasure p hp A + bernoulliMeasure p hp B
      ≤ ENNReal.ofReal (Real.exp (-(2 * n) / (3 * ((k : ℝ) + 1)) ^ 2))
        + ENNReal.ofReal (Real.exp (-(2 * n) / (3 * ((k : ℝ) + 1)) ^ 2)) := add_le_add hAle hBle
    _ = ENNReal.ofReal (2 * Real.exp (-(2 * n) / (3 * ((k : ℝ) + 1)) ^ 2)) := by
        rw [← ENNReal.ofReal_add hexp hexp]
        ring_nf

/-- Beyond the chosen threshold, the union of the deviation sets has measure at most `2^{-m}`. -/
lemma measure_devUnionP_le {p : NNReal} (hp : p ≤ 1) {approx : ℚ → ℚ}
    (happrox : ∀ ε : ℚ, 0 < ε → |(approx ε : ℝ) - (p : ℝ)| ≤ (ε : ℝ)) (k m : ℕ) :
    bernoulliMeasure p hp (devUnionP approx k m) ≤ dyadicValue 1 m := by
  have hle : bernoulliMeasure p hp (devUnionP approx k m)
      ≤ ∑' j : ℕ, bernoulliMeasure p hp (devSetP approx k (devThreshP k m + j)) :=
    measure_iUnion_le _
  have hterm : ∀ j : ℕ, bernoulliMeasure p hp (devSetP approx k (devThreshP k m + j))
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * (((devThreshP k m : ℕ) : ℝ) + j))
          / (((3 * k + 2 : ℕ) : ℝ) + 1) ^ 2)) := by
    intro j
    have h := measure_devSetP_le hp happrox k (devThreshP k m + j)
    rwa [Nat.cast_add] at h
  refine hle.trans ((ENNReal.tsum_le_tsum hterm).trans ?_)
  have hnonneg : ∀ j : ℕ, (0 : ℝ) ≤ 2 * Real.exp (-(2 * (((devThreshP k m : ℕ) : ℝ) + j))
      / (((3 * k + 2 : ℕ) : ℝ) + 1) ^ 2) := by
    intro j; positivity
  have hsum := (ENNReal.ofReal_tsum_of_nonneg hnonneg
    (expTail_summable (3 * k + 2) (devThreshP k m))).symm
  rw [hsum]
  have hT : ((devThreshP k m : ℕ) : ℝ)
      = (((3 * k + 2 : ℕ) : ℝ) + 1) ^ 2 * ((m : ℝ) + 2 * ((3 * k + 2 : ℕ) : ℝ) + 4) := by
    rw [devThreshP, devThresh]; push_cast; ring
  have hb := expTail_le (3 * k + 2) m (devThreshP k m) hT
  refine (ENNReal.ofReal_le_ofReal hb).trans ?_
  rw [dyadicValue_one_eq_inv_two_pow']
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- For a computably approximated Bernoulli parameter, the sets of sequences deviating infinitely
often are uniformly effectively null. -/
lemma isUniformlyEffectivelyNull_devInfSetP {p : NNReal} (hp : p ≤ 1) {approx : ℚ → ℚ}
    (hcomp : Computable approx)
    (happrox : ∀ ε : ℚ, 0 < ε → |(approx ε : ℝ) - (p : ℝ)| ≤ (ε : ℝ)) :
    IsUniformlyEffectivelyNull (bernoulliMeasure p hp) (devInfSetP approx) := by
  refine ⟨devWP approx, isUniformlyEffectiveOpen_devWP hcomp,
    devInfSetP_subset_iInter approx, fun k m => ?_⟩
  have hw : devWP approx (Nat.pair k m) = devUnionP approx k m := by
    simp [devWP, Nat.unpair_pair]
  rw [hw]
  exact measure_devUnionP_le hp happrox k m

/-- A sequence whose frequency of ones does not converge to `p` deviates infinitely often at some
accuracy level. -/
lemma notTendsto_subset_iUnion_devInfSetP {p : NNReal} {approx : ℚ → ℚ}
    (happrox : ∀ ε : ℚ, 0 < ε → |(approx ε : ℝ) - (p : ℝ)| ≤ (ε : ℝ)) :
    {x : CantorSeq | ¬ Tendsto (fun n => (freqOne x n : ℝ)) atTop (𝓝 ((p : ℝ)))}
      ⊆ ⋃ k, devInfSetP approx k := by
  intro x hx
  by_contra hmem
  apply hx
  simp only [Set.mem_iUnion, not_exists] at hmem
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hnk := hmem k
  simp only [devInfSetP, Set.mem_setOf_eq, not_forall, not_exists, not_and] at hnk
  obtain ⟨M, hM⟩ := hnk
  refine ⟨max M 1, fun n hn => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right M 1) hn)
  have hnM : M ≤ n := le_trans (le_max_left M 1) hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  set c := (cantorPrefix x n).count true with hc
  have hnot : ¬ (devBoolP approx k n c = true) := hM n hnM
  rw [devBoolP_iff_rat approx k n c hn1] at hnot
  push_neg at hnot
  have hqreal : |(c : ℝ) / n - ((pApp approx k : ℚ) : ℝ)| < 2 / (3 * ((k : ℝ) + 1)) := by
    have h := (Rat.cast_lt (K := ℝ)).2 hnot
    push_cast at h
    exact h
  have happ : |((pApp approx k : ℚ) : ℝ) - (p : ℝ)| ≤ 1 / (3 * ((k : ℝ) + 1)) := by
    have hpos : (0 : ℚ) < 1 / (3 * ((k : ℚ) + 1)) := by positivity
    have h := happrox _ hpos
    rw [pApp]
    push_cast at h ⊢
    exact h
  have htri : |(c : ℝ) / n - (p : ℝ)|
      ≤ |(c : ℝ) / n - ((pApp approx k : ℚ) : ℝ)| + |((pApp approx k : ℚ) : ℝ) - (p : ℝ)| :=
    abs_sub_le _ _ _
  have hfreq : ((freqOne x n : ℚ) : ℝ) = (c : ℝ) / n := by
    rw [freqOne, hc]
    push_cast
    ring
  have hkey : |((freqOne x n : ℚ) : ℝ) - (p : ℝ)| < 1 / ((k : ℝ) + 1) := by
    rw [hfreq]
    have h3 : (2 : ℝ) / (3 * ((k : ℝ) + 1)) + 1 / (3 * ((k : ℝ) + 1)) = 1 / ((k : ℝ) + 1) := by
      have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      field_simp
      ring
    linarith [htri, hqreal, happ, h3.le, h3.ge]
  rw [Real.dist_eq]
  exact lt_trans hkey hk

/-- **SUV Theorem 32 for a Bernoulli measure with computable parameter.**  The set of
bit sequences that do not have limit frequency `p` is effectively null. -/
theorem isEffectivelyNull_notTendsto_freqOne_bernoulli {p : NNReal} (hp : p ≤ 1)
    (hp_comp : IsComputableReal (p : ℝ)) :
    IsEffectivelyNull (bernoulliMeasure p hp)
      {x : CantorSeq | ¬ Tendsto (fun n => (freqOne x n : ℝ)) atTop (𝓝 ((p : ℝ)))} := by
  obtain ⟨approx, hcomp, happrox⟩ := hp_comp
  replace happrox : ∀ ε : ℚ, 0 < ε → |((approx ε : ℚ) : ℝ) - (p : ℝ)| ≤ (ε : ℝ) :=
    fun ε hε => by rw [abs_sub_comm]; exact happrox ε hε
  exact ((isUniformlyEffectivelyNull_devInfSetP hp hcomp happrox).isEffectivelyNull_iUnion).mono
    (notTendsto_subset_iUnion_devInfSetP happrox)

/-- **SUV Theorem 34.** -/
theorem tendsto_freqOne_of_isMartinLofRandom_bernoulli' {p : NNReal} (hp : p ≤ 1)
    (hp_comp : IsComputableReal (p : ℝ))
    {x : CantorSeq} (hx : IsMartinLofRandom (bernoulliMeasure p hp) x) :
    Tendsto (fun n => (freqOne x n : ℝ)) atTop (𝓝 ((p : ℝ))) := by
  by_contra hnot
  obtain ⟨U, hU1, hU2, hU3⟩ := isEffectivelyNull_notTendsto_freqOne_bernoulli hp hp_comp
  exact hx U ⟨hU1, hU3⟩ (hU2 hnot)

end Kolmogorov
