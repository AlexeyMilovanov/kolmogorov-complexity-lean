import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ThmCardLog
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AnyCurve

/-!
# The normal-string half of VS40 Theorem `card`

Realizing the auxiliary boundary by a *normal* string (square-root precision,
`stat-any-curve-1`) and appending a conditionally random tail produces
`2 ^ (k_P - m_P)`-many normal strings whose plain description profiles are all
`O(sqrt (n log n))`-close to the target profile.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Square-root slacks at the same budget combine by adding their constants. -/
theorem sqrtSlack_add_const (c c' n : ℕ) :
    sqrtSlack c n + sqrtSlack c' n = sqrtSlack (c + c') n := by
  unfold sqrtSlack; ring

/-- Scaling a square-root slack multiplies its constant. -/
theorem sqrtSlack_mul (m c n : ℕ) : m * sqrtSlack c n = sqrtSlack (m * c) n := by
  unfold sqrtSlack; ring

/-- The additive constant of a square-root slack is a lower bound for it. -/
theorem le_sqrtSlack (c n : ℕ) : c ≤ sqrtSlack c n := by
  unfold sqrtSlack
  have : 0 ≤ c * Nat.sqrt (n * (Nat.bits n).length) := Nat.zero_le _
  omega

/-- A logarithmic enlargement of the visible budget is absorbed by a larger
slack constant. -/
theorem logSlack_shifted_arg (a c n : ℕ) :
    logSlack a (n + logSlack c n) ≤ logSlack (a + a * c + a) n := by
  have h1 : logSlack a (n + logSlack c n) ≤ logSlack a n + logSlack a (logSlack c n) :=
    logSlack_add_le a _ _
  have h2 : logSlack a (logSlack c n) ≤ a * logSlack c n + a := by
    unfold logSlack
    have := length_natBits_le_self (c * (Nat.bits n).length + c)
    have h : a * (Nat.bits (c * (Nat.bits n).length + c)).length ≤
        a * (c * (Nat.bits n).length + c) := Nat.mul_le_mul_left _ this
    omega
  have h3 : a * logSlack c n = logSlack (a * c) n := logSlack_mul a c n
  have h4 : logSlack a n + logSlack (a * c) n + logSlack a n =
      logSlack (a + a * c + a) n := by
    unfold logSlack; ring
  have h5 : a ≤ logSlack a n := by
    unfold logSlack
    have : 0 ≤ a * (Nat.bits n).length := Nat.zero_le _
    omega
  omega

/-- The epigraph of a profile boundary is the family-curve target of its
height function. -/
theorem profileSet_eq_familyCurveTarget {V : Map} (b : ProfileBoundary V) :
    {q : ℕ × ℕ | FamilyCurveTarget b.k_P b.height q.1 q.2} = profileSet V b := by
  ext ⟨i, j⟩
  simp only [Set.mem_ofPred_eq, FamilyCurveTarget, profileSet]
  constructor
  · intro h
    rcases Nat.lt_or_ge i b.k_P with hi | hi
    · exact h hi.le
    · rw [b.height_zero_of_ge i hi]
      exact Nat.zero_le _
  · intro h _
    exact h

/-- **Normal-string half of Theorem `card`.**  For every admissible profile with
a boundary `b` there are `2 ^ (k_P - m_P)`-many normal strings whose plain
description profiles are `O(b.KP + sqrt (n log n))`-close to the profile. -/
theorem thm_card_normal_branch
    (V U T : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : ℕ, ∀ (P : Set (Nat × Nat)) (kp mp np : ℕ) (b : ProfileBoundary V),
      IsAdmissibleProfileSet P →
      profileSet V b = P →
      k_P P = (kp : ENat) →
      m_P P kp = (mp : ENat) →
      n_P P = (np : ENat) →
      ∃ S : Finset BitString,
        S.Nonempty ∧
        (S : Set BitString) ⊆
          {x | IsNormalString V T x (logSlack c np) (sqrtSlack c np) ∧
            ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V x) P
              (c * b.KP + sqrtSlack c np)} ∧
        ((kp - mp : ℕ) : ENat) ≤ (finiteSetLogCard S : ENat) + (c : ENat) := by
  classical
  obtain ⟨C1, hAux⟩ := auxiliaryProfile_boundary V U hV hU
  obtain ⟨C5, hCurve⟩ := exists_normal_string_with_curve V U T hV hU hT
  obtain ⟨C4, hAssm⟩ := exists_noise_finset_near_profile V U hV hU
  obtain ⟨Cn, hNormalPair⟩ := normal_pair_of_conditionally_random_tail V U T hV hU hT
  obtain ⟨Cls, hClsBound, hCls⟩ := logSlack_le_sqrtSlack_linear
  -- Slack constants of the conclusion.
  set aLog := C5 + (Cn + Cn * C5 + Cn) with haLog
  set aSqrt := 2 * Cn * C5 + Cn * C4 + Cls (Cn + Cn * C5 + Cn) +
    2 * C4 * C5 + Cls (C4 + C4 * C5 + C4) + C4 + 1 with haSqrt
  refine ⟨aLog + aSqrt, ?_⟩
  intro P kp mp np b hadm hbP hkP hmP hnP
  set c := aLog + aSqrt with hc
  -- Endpoint facts.
  have hmpkp : mp ≤ kp := by
    have h := m_P_le_k_P_of_eq P kp hkP
    rw [hmP, hkP] at h
    exact_mod_cast h
  have hkpnp : kp ≤ np := by
    have h := k_P_le_n_P_of_admissible hadm
    rw [hkP, hnP] at h
    exact_mod_cast h
  set d := kp - mp with hd
  -- The auxiliary boundary.
  obtain ⟨bt, hbtk, hbtn, hbtP, -⟩ := hAux P kp mp np b hadm hbP hkP hmP hnP
  have hntnp : bt.n_P ≤ np := by omega
  have hmpnt : mp ≤ bt.n_P := by omega
  -- Realize the auxiliary boundary by a normal string.
  have hcurve0 : bt.height 0 ≤ bt.n_P := le_of_eq bt.height_zero
  have hcurvek : bt.height mp = 0 := by
    rw [← hbtk]
    exact bt.height_zero_of_ge bt.k_P le_rfl
  have hstrict : ∀ i : ℕ, i < mp → bt.height (i + 1) < bt.height i := by
    intro i hi
    have hpos : 0 < bt.height i := bt.height_pos_of_lt i (by omega)
    rcases bt.slope i with hzero | hlt
    · omega
    · exact hlt
  obtain ⟨y, n', hylen, hn'low, hn'up, hkyUp, hkyLow, hyprofile, hynormal⟩ :=
    hCurve bt.n_P mp bt.height hmpnt hcurve0 hcurvek hstrict
  have htarget : {q : ℕ × ℕ | FamilyCurveTarget mp bt.height q.1 q.2} =
      auxiliaryProfile P mp kp := by
    rw [← hbtP, ← hbtk]
    exact profileSet_eq_familyCurveTarget bt
  rw [htarget] at hyprofile
  -- Complexity of the head.
  have hyFinite : plainK V y ≠ ⊤ := condK_ne_top_of_optimal V hV y []
  set ky := (plainK V y).toNat with hky
  have hkyval : plainK V y = (ky : ENat) := (ENat.natCast_toNat hyFinite).symm
  set e := sqrtSlack C5 bt.n_P with he
  have hkyup : ky ≤ mp + e := by
    rw [hkyval] at hkyUp
    exact_mod_cast hkyUp
  have hkylow : mp ≤ ky + e := by
    rw [hkyval] at hkyLow
    exact_mod_cast hkyLow
  -- The random tails.
  obtain ⟨R, hRne, hRmem, hRcard⟩ :=
    hAssm P kp mp y e e ky hadm hkP hmP hkyval hkyup hkylow hyprofile
  -- Slack bookkeeping.
  have hlensum : y.length + (kp - mp) ≤ np + logSlack C5 np := by
    have h1 : y.length = n' := hylen
    have h2 : n' ≤ bt.n_P + logSlack C5 bt.n_P := hn'up
    have h3 : logSlack C5 bt.n_P ≤ logSlack C5 np := logSlack_mono_right C5 hntnp
    have h4 : bt.n_P + (kp - mp) ≤ np := by omega
    omega
  have hlogsum : logSlack Cn (y.length + (kp - mp)) ≤
      logSlack (Cn + Cn * C5 + Cn) np :=
    (logSlack_mono_right Cn hlensum).trans (logSlack_shifted_arg Cn C5 np)
  have hlogsum4 : logSlack C4 (y.length + (kp - mp)) ≤
      logSlack (C4 + C4 * C5 + C4) np :=
    (logSlack_mono_right C4 hlensum).trans (logSlack_shifted_arg C4 C5 np)
  have hent : e ≤ sqrtSlack C5 np := sqrtSlack_mono_right C5 hntnp
  refine ⟨R.image (fun z => pairCode y z), hRne.image _, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨hzlen, hzrand, hznb⟩ := hRmem z hz
    constructor
    · -- Normality of the pair.
      have hpair := hNormalPair y z (kp - mp) (logSlack C5 bt.n_P)
        (2 * sqrtSlack C5 bt.n_P) C4
        hynormal hzlen hzrand
      refine (hpair.mono_delta ?_).mono_epsilon ?_
      · -- Deficiency bound.
        have h1 : Cn * (2 * sqrtSlack C5 bt.n_P + C4) =
            sqrtSlack (2 * Cn * C5) bt.n_P + Cn * C4 := by
          have : Cn * (2 * sqrtSlack C5 bt.n_P + C4) =
              (2 * Cn) * sqrtSlack C5 bt.n_P + Cn * C4 := by ring
          rw [this, sqrtSlack_mul]
        have h2 : sqrtSlack (2 * Cn * C5) bt.n_P ≤ sqrtSlack (2 * Cn * C5) np :=
          sqrtSlack_mono_right _ hntnp
        have h3 : Cn * C4 ≤ sqrtSlack (Cn * C4) np := le_sqrtSlack _ _
        have h4 : logSlack (Cn + Cn * C5 + Cn) np ≤
            sqrtSlack (Cls (Cn + Cn * C5 + Cn)) np := hCls _ _
        have h5 : sqrtSlack (2 * Cn * C5) np + sqrtSlack (Cn * C4) np +
            sqrtSlack (Cls (Cn + Cn * C5 + Cn)) np =
            sqrtSlack (2 * Cn * C5 + Cn * C4 + Cls (Cn + Cn * C5 + Cn)) np := by
          rw [sqrtSlack_add_const, sqrtSlack_add_const]
        have h6 : sqrtSlack (2 * Cn * C5 + Cn * C4 + Cls (Cn + Cn * C5 + Cn)) np ≤
            sqrtSlack c np := by
          apply sqrtSlack_mono_left
          rw [hc, haSqrt]; omega
        omega
      · -- Strength bound.
        have h1 : logSlack C5 bt.n_P ≤ logSlack C5 np := logSlack_mono_right C5 hntnp
        have h2 : logSlack C5 np + logSlack (Cn + Cn * C5 + Cn) np =
            logSlack aLog np := by
          rw [haLog]; exact logSlack_add_const _ _ _
        have h3 : logSlack aLog np ≤ logSlack c np :=
          logSlack_mono_left (by rw [hc]; omega) _
        omega
    · -- Profile of the pair.
      refine hznb.mono ?_
      have h1 : C4 * (e + e) ≤ sqrtSlack (2 * C4 * C5) np := by
        have h : C4 * (e + e) = (2 * C4) * sqrtSlack C5 bt.n_P := by rw [he]; ring
        rw [h, sqrtSlack_mul]
        exact sqrtSlack_mono_right _ hntnp
      have h2 : logSlack (C4 + C4 * C5 + C4) np ≤
          sqrtSlack (Cls (C4 + C4 * C5 + C4)) np := hCls _ _
      have h3 : sqrtSlack (2 * C4 * C5) np + sqrtSlack (Cls (C4 + C4 * C5 + C4)) np =
          sqrtSlack (2 * C4 * C5 + Cls (C4 + C4 * C5 + C4)) np :=
        sqrtSlack_add_const _ _ _
      have h4 : sqrtSlack (2 * C4 * C5 + Cls (C4 + C4 * C5 + C4)) np ≤
          sqrtSlack c np := by
        apply sqrtSlack_mono_left
        rw [hc, haSqrt]; omega
      have h5 : 0 ≤ c * b.KP := Nat.zero_le _
      omega
  · rw [finiteSetLogCard_image_pairCode]
    refine hRcard.trans ?_
    gcongr
    exact_mod_cast (show C4 ≤ c by rw [hc, haSqrt]; omega)

end Kolmogorov
