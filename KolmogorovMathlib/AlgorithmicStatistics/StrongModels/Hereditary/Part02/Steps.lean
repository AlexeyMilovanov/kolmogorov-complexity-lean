import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LchLemma
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropMinHereditary
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Budget

/-!
# The two construction steps of the hereditary assembly

The hereditary theorem turns a point `(i, j)` of the plain description profile of the code
of a model `A` of `x` into a family `F` of set-codes containing the code of `A`.  The
construction runs `G → L → M` (lift the profile family `G` to a model `L ∋ x`, then apply
Lemma `lch` to obtain a strong model `M`) and then `M → M₁ → F₁ → F` (partition `M` and `A`,
build the hereditary family for the partition classes and transport it back along the total
equivalence of `A₁` and `A`).  This module proves the two steps separately; the assembly in
`CoreAssembly` only has to add up the two budgets.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- For an optimal conditional machine the plain set complexity of a nonempty finite set of
strings is finite, hence equal to the coercion of a natural number. -/
lemma exists_plainSetComplexity_eq_coe (V : Map) (hV : isOptimalConditional V)
    (S : Finset BitString) (hS : S.Nonempty) :
    ∃ k : Nat, plainSetComplexity V S hS = (k : ENat) :=
  ⟨_, (ENat.natCast_toNat (condK_ne_top_of_optimal V hV (codedUniformOn S hS).code [])).symm⟩

/-- An `epsilon`-sufficient statistic `A` for a string of length `n` with `epsilon ≤ n` has
plain set complexity and log-cardinality at most `2 * n + c`, for a constant `c` depending
only on the machine. -/
lemma sufficientStatistic_complexity_le_two_mul_length (V : Map)
    (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x n A (hA : A.Nonempty) epsilon,
      x.length = n → epsilon ≤ n → IsSufficientStatistic V x A hA epsilon →
      plainSetComplexity V A hA ≤ ((2 * n + c : Nat) : ENat) ∧
        finiteSetLogCard A ≤ 2 * n + c := by
  obtain ⟨cLen, hLen⟩ := plainK_le_length V hV
  refine ⟨cLen, ?_⟩
  intro x n A hA epsilon hn heps hSuff
  have hboth : plainSetComplexity V A hA + (finiteSetLogCard A : ENat) ≤
      ((2 * n + cLen : Nat) : ENat) := by
    calc plainSetComplexity V A hA + (finiteSetLogCard A : ENat)
        ≤ plainK V x + (epsilon : ENat) := hSuff.2
      _ ≤ ((n + cLen : Nat) : ENat) + (epsilon : ENat) := by
          gcongr
          simpa [hn] using hLen x
      _ ≤ ((2 * n + cLen : Nat) : ENat) := by
          exact_mod_cast (show n + cLen + epsilon ≤ 2 * n + cLen by omega)
  refine ⟨le_trans (le_add_right le_rfl) hboth, ?_⟩
  exact_mod_cast le_trans (le_add_left le_rfl) hboth

/-- `HereditaryCoreModel V T x A hA M hM epsilon b i j` collects what the lifting and LCH
steps produce out of a plain description point `(i, j)` of the code of `A`: the set `M`
contains `x`, is a strong `epsilon`-model of `x`, its code has conditional complexity at
most `b` given the code of `A`, its plain set complexity is at most `i + b`, and its
two-part cost is at most `i + j + log #A + b`. -/
def HereditaryCoreModel (V T : Map) (x : BitString) (A : Finset BitString) (hA : A.Nonempty)
    (M : Finset BitString) (hM : M.Nonempty) (epsilon b i j : Nat) : Prop :=
  x ∈ M ∧
    IsStrongSetModel T x M hM epsilon ∧
    condK V (codedUniformOn M hM).code (codedUniformOn A hA).code ≤ (b : ENat) ∧
    plainSetComplexity V M hM ≤ ((i + b : Nat) : ENat) ∧
    plainSetComplexity V M hM + (finiteSetLogCard M : ENat) ≤
      ((i + j + finiteSetLogCard A + b : Nat) : ENat)

/-- **The lifting and LCH steps of the hereditary construction.**  For a normal string `x`
of length `n` with a minimal sufficient model `A`, every point `(i, j)` of the plain
description profile of the code of `A` that is below the complexity of `A` by more than the
slack yields a strong `epsilon`-model `M` of `x` satisfying `HereditaryCoreModel`, with the
single budget `hereditarySlack cStep delta epsilon n`. -/
lemma hereditary_core_lch_model (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ cKappa cStep : Nat,
      ∀ x n A (hA : A.Nonempty) epsilon delta i j,
        x.length = n →
        IsMinimalModel V x A hA delta (logSlack cKappa n) →
        IsSufficientStatistic V x A hA epsilon →
        IsNormalString V T x epsilon epsilon →
        epsilon ≤ n →
        epsilon * 2 < Nat.sqrt n →
        ((i + hereditarySlack cStep delta epsilon n : Nat) : ENat) <
          plainSetComplexity V A hA →
        InPlainDescriptionProfile V (codedUniformOn A hA).code i j →
        ∃ M, ∃ hM : M.Nonempty,
          HereditaryCoreModel V T x A hA M hM epsilon
            (hereditarySlack cStep delta epsilon n) i j := by
  obtain ⟨cLift, hLift⟩ := hereditary_lift_model V hV
  obtain ⟨cLch, hLch⟩ := lemma_lch_with_mem V T hV hT
  obtain ⟨cOmegaKappa, cOmegaOut, hOmega⟩ := hereditary_omega_chain V T hV hT cLch
  obtain ⟨cLen, hLen⟩ := plainK_le_length V hV
  obtain ⟨q, hq⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  refine ⟨cOmegaKappa, (cLift + cLch + cOmegaOut + cLen + 3) ^ 5, ?_⟩
  intro x n A hA epsilon delta i j hn hMin hSuff hNorm heps_le heps_sqrt h_i_lt h_prof
  set b := cLift + cLch + cOmegaOut + cLen + 3 with hbdef
  set S := hereditarySlack (b ^ 5) delta epsilon n with hSdef
  have hb : 3 ≤ b := by omega
  have hsqrt1 : 1 ≤ Nat.sqrt n :=
    Nat.succ_le_iff.mpr ((Nat.zero_le (epsilon * 2)).trans_lt heps_sqrt)
  -- Step 1: lift the profile family `G` to a model `L ∋ x`.
  obtain ⟨G, hG, hx_G, hG_i, hG_j⟩ := h_prof
  have hxA : x ∈ A := hMin.1
  obtain ⟨L, hL, hx_L, hLcomp, hLcard⟩ := hLift x A hA G hG hxA hx_G
  -- Step 2: Lemma `lch` turns `L` into a strong model `M ∋ x`.
  obtain ⟨M, hM, hx_M, hM_strong, hM_bound, hM_omega, hM_plain⟩ :=
    hLch x n L hL epsilon epsilon q hq hn hx_L heps_le heps_sqrt hNorm
  -- The log-cardinality of `A` is at most `2 * n + b`, by sufficiency.
  have hcardA : finiteSetLogCard A ≤ 2 * n + b := by
    have hcardA_ENat : (finiteSetLogCard A : ENat) ≤ ((2 * n + b : Nat) : ENat) := by
      calc (finiteSetLogCard A : ENat)
          ≤ plainSetComplexity V A hA + (finiteSetLogCard A : ENat) := le_add_left le_rfl
        _ ≤ plainK V x + (epsilon : ENat) := hSuff.2
        _ ≤ ((n + cLen : Nat) : ENat) + (epsilon : ENat) := by
            gcongr
            simpa [hn] using hLen x
        _ ≤ ((2 * n + b : Nat) : ENat) := by
            exact_mod_cast (show n + cLen + epsilon ≤ 2 * n + b by omega)
    exact_mod_cast hcardA_ENat
  -- The whole overhead of the two steps fits into the single slack `S`.
  have hbudget :
      logSlack cLift (finiteSetLogCard A) + epsilon +
        cLch * (epsilon + logSlack cLch n) * Nat.sqrt n ≤ S :=
    hereditary_lch_step_budget hb hsqrt1 hcardA (by omega) (by omega)
  -- Numeric form of the complexities involved.
  obtain ⟨mComp, hmVal⟩ := exists_plainSetComplexity_eq_coe V hV M hM
  obtain ⟨lComp, hlVal⟩ := exists_plainSetComplexity_eq_coe V hV L hL
  obtain ⟨gComp, hgVal⟩ := exists_plainSetComplexity_eq_coe V hV G hG
  have n13 : mComp ≤ lComp + epsilon := by
    rw [hmVal, hlVal] at hM_plain; exact_mod_cast hM_plain
  have n5 : lComp ≤ gComp + logSlack cLift (finiteSetLogCard A) := by
    rw [hlVal, hgVal] at hLcomp; exact_mod_cast hLcomp
  have n6 : gComp ≤ i := by rw [hgVal] at hG_i; exact_mod_cast hG_i
  have n4 : mComp + finiteSetLogCard M ≤
      lComp + finiteSetLogCard L + cLch * (epsilon + logSlack cLch n) * Nat.sqrt n := by
    rw [hmVal, hlVal] at hM_bound; exact_mod_cast hM_bound
  have n8 : finiteSetLogCard G ≤ j := (finiteSetLogCard_le_iff G j).mpr hG_j
  have hMcompNat : mComp ≤ i + S := by omega
  have hMcomp : plainSetComplexity V M hM ≤ ((i + S : Nat) : ENat) := by
    rw [hmVal]; exact_mod_cast hMcompNat
  -- `M` is at most `delta` above `A`, which feeds the `Ω`-chain.
  have hMA : plainSetComplexity V M hM ≤ plainSetComplexity V A hA + (delta : ENat) :=
    (hMcomp.trans h_i_lt.le).trans (le_add_right le_rfl)
  have hcond := hOmega x n A hA M hM delta q hq hn hMin hMA hM_omega
  have hcondNat :
      cOmegaOut * delta + cOmegaOut * Nat.sqrt n + logSlack cOmegaOut n ≤ S := by
    refine le_trans (hereditary_omega_step_budget (eps := epsilon) hb hsqrt1 (by omega)) ?_
    exact hereditarySlack_mono_c (Nat.pow_le_pow_right (by omega) (by norm_num))
  refine ⟨M, hM, hx_M, hM_strong, ?_, hMcomp, ?_⟩
  · refine hcond.trans ?_
    calc (cOmegaOut * delta + cOmegaOut * Nat.sqrt n + logSlack cOmegaOut n : ENat)
        = ((cOmegaOut * delta + cOmegaOut * Nat.sqrt n + logSlack cOmegaOut n : Nat) : ENat) := by
          push_cast; ring
      _ ≤ (S : ENat) := by exact_mod_cast hcondNat
  · rw [hmVal]
    have : mComp + finiteSetLogCard M ≤ i + j + finiteSetLogCard A + S := by omega
    exact_mod_cast this
/-- A total-conditional bound for `T` gives an ordinary conditional bound for a machine `V`
that simulates `T` with constant `c`, at the cost of that constant. -/
lemma condK_le_of_totalCondK_le_of_sim {V T : Map} {u v : BitString} {p c : Nat}
    (hSim : ∀ a b, condK V a b ≤ condK T a b + (c : ENat))
    (h : totalCondK T u v ≤ (p : ENat)) :
    condK V u v ≤ ((p + c : Nat) : ENat) := by
  calc condK V u v ≤ condK T u v + (c : ENat) := hSim _ _
    _ ≤ totalCondK T u v + (c : ENat) := by
        gcongr
        exact condK_le_totalCondK T _ _
    _ ≤ (p : ENat) + (c : ENat) := by gcongr
    _ = ((p + c : Nat) : ENat) := by push_cast; ring

/-- **The intersection estimate of the hereditary construction.**  Let `A` be an
`epsilon`-sufficient statistic for `x` of polynomial complexity, let `A₁ ∋ x` be describable
from the code of `A` at cost `pPlain` and `M₁ ∋ x` describable from the code of `A₁` at cost
`dChain`.  If both costs are inside the unit budget, then intersecting the two classes loses
at most the hereditary slack of `b ^ 20` in log-cardinality. -/
lemma hereditary_core_intersection_gap (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ b x n A (hA : A.Nonempty) A1 (hA1 : x ∈ A1) M1 (hM1 : x ∈ M1)
        (epsilon delta pPlain dChain : Nat),
      c ≤ b → 3 ≤ b → 1 ≤ Nat.sqrt n →
      IsSufficientStatistic V x A hA epsilon →
      plainSetComplexity V A hA ≤ ((2 * n + b : Nat) : ENat) →
      pPlain ≤ b ^ 4 * hereditaryUnit delta epsilon n →
      dChain ≤ b ^ 7 * hereditaryUnit delta epsilon n →
      condK V (codedUniformOn A1 ⟨x, hA1⟩).code (codedUniformOn A hA).code ≤ (pPlain : ENat) →
      condK V (codedUniformOn M1 ⟨x, hM1⟩).code (codedUniformOn A1 ⟨x, hA1⟩).code ≤
        (dChain : ENat) →
      finiteSetLogCard A ≤
        finiteSetLogCard (A1 ∩ M1) + b ^ 20 * hereditaryUnit delta epsilon n := by
  obtain ⟨cSuffLower, hSuffLower⟩ := hereditary_sufficiency_model_lower_bound V hV
  obtain ⟨cInter, hInter⟩ := plainSetComplexity_inter_le_of_condK V hV
  obtain ⟨cTwo, hTwo⟩ := plainK_two_stage V hV
  refine ⟨cSuffLower + cInter + cTwo, ?_⟩
  intro b x n A hA A1 hA1 M1 hM1 epsilon delta pPlain dChain hcb hb hsqrt hSuffA hAle
    hpPlain hdChain hA1_A hM1_A1
  have hIne : (A1 ∩ M1).Nonempty := ⟨x, by simp [hA1, hM1]⟩
  obtain ⟨aComp, hAVal⟩ := exists_plainSetComplexity_eq_coe V hV A hA
  obtain ⟨a1Comp, hA1Val⟩ := exists_plainSetComplexity_eq_coe V hV A1 ⟨x, hA1⟩
  obtain ⟨iComp, hIVal⟩ := exists_plainSetComplexity_eq_coe V hV (A1 ∩ M1) hIne
  have haCompLe : aComp ≤ 2 * n + b := by
    rw [hAVal] at hAle; exact_mod_cast hAle
  -- The class `A₁` costs at most the transfer plus the address of `A`.
  have ha1Comp : a1Comp ≤ aComp + (pPlain + 2 * (Nat.bits aComp).length + cTwo) := by
    have h : plainSetComplexity V A1 ⟨x, hA1⟩ ≤
        ((aComp + pPlain + 2 * (Nat.bits aComp).length + cTwo : Nat) : ENat) :=
      hTwo (codedUniformOn A1 ⟨x, hA1⟩).code (codedUniformOn A hA).code aComp pPlain
        (le_of_eq hAVal) hA1_A
    rw [hA1Val] at h
    have hnat : a1Comp ≤ aComp + pPlain + 2 * (Nat.bits aComp).length + cTwo := by
      exact_mod_cast h
    omega
  -- The intersection costs at most the class plus the chain cost.
  have hiComp : iComp ≤ a1Comp + (dChain + 2 * (Nat.bits a1Comp).length + cInter) := by
    have h := hInter A1 ⟨x, hA1⟩ M1 ⟨x, hM1⟩ hIne a1Comp dChain hA1Val hM1_A1
    rw [hIVal] at h
    have hnat : iComp ≤ a1Comp + dChain + 2 * (Nat.bits a1Comp).length + cInter := by
      exact_mod_cast h
    omega
  set deltaOrig := pPlain + 2 * (Nat.bits aComp).length + cTwo +
    (dChain + 2 * (Nat.bits a1Comp).length + cInter) with hdeltaOrig
  have hiOrig : iComp ≤ aComp + deltaOrig := by omega
  -- Sufficiency turns that complexity gap into a log-cardinality gap.
  have hLogGap := hSuffLower x A hA (A1 ∩ M1) hIne epsilon deltaOrig (aComp + deltaOrig)
    aComp iComp hSuffA (by simp [hA1, hM1]) hAVal hIVal hiOrig le_rfl
  have hdeltaOrigU : deltaOrig ≤ b ^ 13 * hereditaryUnit delta epsilon n :=
    hereditary_intersection_step_budget hb hsqrt (show cTwo ≤ b by omega)
      (show cInter ≤ b by omega) haCompLe ha1Comp hpPlain hdChain
  have hgapU : epsilon + deltaOrig + logSlack cSuffLower (aComp + deltaOrig) ≤
      b ^ 20 * hereditaryUnit delta epsilon n :=
    hereditary_gap_step_budget hb hsqrt (show cSuffLower ≤ b by omega) haCompLe hdeltaOrigU
  omega

/-- `HereditaryCoreFamily V T A hA M hM F hF b` collects what the partition, family and
transport steps produce out of a strong model `M`: the family `F` contains the code of `A`,
is a strong `b`-model of that code, its plain set complexity exceeds that of `M` by at most
`b`, and its log-cardinality plus that of `A` is at most that of `M` plus `b`. -/
def HereditaryCoreFamily (V T : Map) (A : Finset BitString) (hA : A.Nonempty)
    (M : Finset BitString) (hM : M.Nonempty) (F : Finset BitString) (hF : F.Nonempty)
    (b : Nat) : Prop :=
  (codedUniformOn A hA).code ∈ F ∧
    IsStrongSetModel T (codedUniformOn A hA).code F hF b ∧
    plainSetComplexity V F hF ≤ plainSetComplexity V M hM + (b : ENat) ∧
    finiteSetLogCard F + finiteSetLogCard A ≤ finiteSetLogCard M + b

/-- **The partition, family and transport steps of the hereditary construction.**  A strong
`epsilon`-model `M` of `x` whose code is within the slack of `cIn` of the code of the
sufficient model `A`, and which costs at most `delta` more than `A`, yields a family `F` of
set-codes satisfying `HereditaryCoreFamily`, with the single budget
`hereditarySlack cOut delta epsilon n`. -/
lemma hereditary_core_family_from_model (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) (cIn : Nat) :
    ∃ cOut : Nat,
      ∀ x n A (hA : A.Nonempty) M (hM : M.Nonempty) (epsilon delta : Nat),
        x.length = n →
        epsilon * 2 < Nat.sqrt n →
        x ∈ M →
        IsSufficientStatistic V x A hA epsilon →
        IsStrongSetModel T x A hA epsilon →
        IsStrongSetModel T x M hM epsilon →
        plainSetComplexity V M hM ≤ plainSetComplexity V A hA + (delta : ENat) →
        condK V (codedUniformOn M hM).code (codedUniformOn A hA).code ≤
          (hereditarySlack cIn delta epsilon n : ENat) →
        ∃ F, ∃ hF : F.Nonempty,
          HereditaryCoreFamily V T A hA M hM F hF
            (hereditarySlack cOut delta epsilon n) := by
  obtain ⟨cPart, hPart⟩ := IsStrongSetModel.exists_partition V hV T hT
  obtain ⟨cFam, hFam⟩ := hereditary_family_model_sharp V T hV hT
  obtain ⟨cGap, hGap⟩ := partition_member_totalCondK_of_logCard_gap V T hV hT
  obtain ⟨cGapLem, hGapLem⟩ := hereditary_core_intersection_gap V hV
  obtain ⟨cTrans, hTrans⟩ := strong_model_of_totalEquivalentWithin V T hV hT
  obtain ⟨cChain, hChain⟩ := hereditary_partition_condK_chain V T hV hT
  obtain ⟨cTwo, hTwo⟩ := plainK_two_stage V hV
  obtain ⟨cSimT, hSimT⟩ := hV.2 T hT.1
  obtain ⟨cSuffBd, hSuffBd⟩ := sufficientStatistic_complexity_le_two_mul_length V hV
  refine ⟨(cPart + cFam + cGap + cGapLem + cTrans + cChain + cTwo + cSimT +
    cSuffBd + cIn + 3) ^ 34, ?_⟩
  intro x n A hA M hM epsilon delta hn heps_sqrt hxM hSuffA hStrongA hStrongM hMA hcond
  set b := cPart + cFam + cGap + cGapLem + cTrans + cChain + cTwo + cSimT +
    cSuffBd + cIn + 3 with hbdef
  have hb : 3 ≤ b := by omega
  have hsqrt1 : 1 ≤ Nat.sqrt n :=
    Nat.succ_le_iff.mpr ((Nat.zero_le (epsilon * 2)).trans_lt heps_sqrt)
  have heps_le : epsilon ≤ n :=
    le_trans (by omega) ((Nat.le_of_lt heps_sqrt).trans (Nat.sqrt_le_self n))
  have hxA : x ∈ A := hSuffA.1
  obtain ⟨hAle0, hcardA0⟩ := hSuffBd x n A hA epsilon hn heps_le hSuffA
  have hcardA : finiteSetLogCard A ≤ 2 * n + b := by omega
  have hAle : plainSetComplexity V A hA ≤ ((2 * n + b : Nat) : ENat) :=
    hAle0.trans (by exact_mod_cast (show 2 * n + cSuffBd ≤ 2 * n + b by omega))
  -- Partition the model and the sufficient statistic.
  obtain ⟨Q, M1, hM1_x, hQ_part, hM1_Q, hM1_card, hQ_comp, hM_M1, hM1_M⟩ :=
    hPart x n hn M hxM epsilon hStrongM
  obtain ⟨P, A1, hA1_x, hP_part, hA1_P, hA1_card, hP_comp, hA_A1, hA1_A⟩ :=
    hPart x n hn A hxA epsilon hStrongA
  set p_F1 := epsilon + logSlack cPart n with hpF1def
  let dIn := hereditarySlack cIn delta epsilon n
  let dChain := cChain * (p_F1 + dIn) + cChain
  have hA1M1_nonempty : (A1 ∩ M1).Nonempty := ⟨x, by simp [hM1_x, hA1_x]⟩
  -- The ordinary chain `A₁ → A → M → M₁`.
  have hM1_A1_plain :
      condK V (codedUniformOn M1 ⟨x, hM1_x⟩).code
          (codedUniformOn A1 ⟨x, hA1_x⟩).code ≤ (dChain : ENat) := by
    apply hChain (codedUniformOn A1 ⟨x, hA1_x⟩).code
      (codedUniformOn A hA).code (codedUniformOn M hM).code
      (codedUniformOn M1 ⟨x, hM1_x⟩).code p_F1 dIn
    · simpa [p_F1] using hA_A1
    · exact hcond
    · simpa [p_F1] using hM1_M
  let pPlain := p_F1 + cSimT
  have hA1_A_plain :
      condK V (codedUniformOn A1 ⟨x, hA1_x⟩).code (codedUniformOn A hA).code ≤
        (pPlain : ENat) :=
    condK_le_of_totalCondK_le_of_sim hSimT (by simpa [p_F1] using hA1_A)
  have hM1_M_plain :
      condK V (codedUniformOn M1 ⟨x, hM1_x⟩).code (codedUniformOn M hM).code ≤
        (pPlain : ENat) :=
    condK_le_of_totalCondK_le_of_sim hSimT (by simpa [p_F1] using hM1_M)
  obtain ⟨hpF1U, hpPlainU⟩ :=
    hereditary_partition_cost_budget (delta := delta) hb hsqrt1 (show cPart ≤ b by omega)
      (show cSimT ≤ b by omega)
  have hdChainU : dChain ≤ b ^ 7 * hereditaryUnit delta epsilon n :=
    hereditary_chain_cost_budget hb (show cChain ≤ b by omega) (show cIn ≤ b by omega) hpF1U
  -- The intersection of the two partition classes loses little log-cardinality.
  have hgapCard : finiteSetLogCard A ≤
      finiteSetLogCard (A1 ∩ M1) + b ^ 20 * hereditaryUnit delta epsilon n :=
    hGapLem b x n A hA A1 hA1_x M1 hM1_x epsilon delta pPlain dChain (by omega) hb hsqrt1
      hSuffA hAle hpPlainU hdChainU hA1_A_plain hM1_A1_plain
  set gap := finiteSetLogCard A1 - finiteSetLogCard (A1 ∩ M1) with hgapdef
  have hA1Log : finiteSetLogCard A1 ≤ finiteSetLogCard A := finiteSetLogCard_mono hA1_card
  have hgapU : gap ≤ b ^ 20 * hereditaryUnit delta epsilon n := by omega
  have hM1_A1_gap :
      totalCondK T (codedUniformOn M1 ⟨x, hM1_x⟩).code
          (codedUniformOn A1 ⟨x, hA1_x⟩).code ≤
        (cGap * p_F1 + gap + logSlack cGap (finiteSetLogCard A) : ENat) :=
    hGap Q M1 ⟨x, hM1_x⟩ A1 ⟨x, hA1_x⟩ p_F1 (finiteSetLogCard A) gap hQ_part hM1_Q
      hA1M1_nonempty (by simpa [p_F1] using hQ_comp) hA1Log (by omega)
  -- The hereditary family of the partition class, transported back to `A`.
  set s_F1 := cGap * p_F1 + gap + logSlack cGap (finiteSetLogCard A) with hsF1def
  obtain ⟨F1, hF1, hA1_F1, hF1_strong, hF1_comp, hF1_card⟩ :=
    hFam P A1 ⟨x, hA1_x⟩ M1 ⟨x, hM1_x⟩ p_F1 s_F1 hP_part hA1_P hA1M1_nonempty
      (by simpa [p_F1] using hP_comp) hM1_A1_gap
  obtain ⟨F, hF, hA_F, hF_strong, hF_comp, hF_card⟩ :=
    hTrans (codedUniformOn A1 ⟨x, hA1_x⟩).code (codedUniformOn A hA).code p_F1
      (cFam * (p_F1 + s_F1) + cFam) F1 hF1 hA1_F1 ⟨hA1_A, hA_A1⟩ hF1_strong
  -- Numeric form of the three complexity steps `M → M₁ → F₁ → F`.
  obtain ⟨fComp, hFVal⟩ := exists_plainSetComplexity_eq_coe V hV F hF
  obtain ⟨f1Comp, hF1Val⟩ := exists_plainSetComplexity_eq_coe V hV F1 hF1
  obtain ⟨mComp, hMVal⟩ := exists_plainSetComplexity_eq_coe V hV M hM
  obtain ⟨m1Comp, hM1Val⟩ := exists_plainSetComplexity_eq_coe V hV M1 ⟨x, hM1_x⟩
  have n1 : fComp ≤ f1Comp + (2 * p_F1 + cTrans) := by
    rw [hFVal, hF1Val] at hF_comp; exact_mod_cast hF_comp
  have n2 : f1Comp ≤ m1Comp + (cFam * p_F1 + logSlack cFam (finiteSetLogCard A1)) := by
    rw [hF1Val, hM1Val] at hF1_comp; exact_mod_cast hF1_comp
  have n3 : m1Comp ≤ mComp + (pPlain + 2 * (Nat.bits mComp).length + cTwo) := by
    have h : plainSetComplexity V M1 ⟨x, hM1_x⟩ ≤
        ((mComp + pPlain + 2 * (Nat.bits mComp).length + cTwo : Nat) : ENat) :=
      hTwo (codedUniformOn M1 ⟨x, hM1_x⟩).code (codedUniformOn M hM).code
        mComp pPlain (le_of_eq hMVal) hM1_M_plain
    rw [hM1Val] at h
    have hnat : m1Comp ≤ mComp + pPlain + 2 * (Nat.bits mComp).length + cTwo := by
      exact_mod_cast h
    omega
  -- Every accumulated overhead is inside the hereditary slack of `b ^ 34`.
  have hcardA1 : finiteSetLogCard A1 ≤ 2 * n + b := hA1Log.trans hcardA
  have hmCompMix : mComp ≤ 2 * n + b + hereditaryUnit delta epsilon n := by
    have h : (mComp : ENat) ≤ ((2 * n + b + delta : Nat) : ENat) := by
      rw [← hMVal]
      refine hMA.trans ?_
      calc plainSetComplexity V A hA + (delta : ENat)
          ≤ ((2 * n + b : Nat) : ENat) + (delta : ENat) := by gcongr
        _ = ((2 * n + b + delta : Nat) : ENat) := by push_cast; ring
    have hnat : mComp ≤ 2 * n + b + delta := by exact_mod_cast h
    have := delta_le_hereditaryUnit delta epsilon n
    omega
  have hbud : 2 * p_F1 + b + (b * p_F1 + logSlack b (finiteSetLogCard A1)) +
      (pPlain + 2 * (Nat.bits mComp).length + b) +
      b ^ 20 * hereditaryUnit delta epsilon n + 2 ≤
      hereditarySlack (b ^ 27) delta epsilon n :=
    hereditary_family_step_budget hb hsqrt1 hcardA1 hmCompMix hpF1U hpPlainU
  have hslackMono : hereditarySlack (b ^ 27) delta epsilon n ≤
      hereditarySlack (b ^ 34) delta epsilon n :=
    hereditarySlack_mono_c (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hmono : cFam * p_F1 + logSlack cFam (finiteSetLogCard A1) ≤
      b * p_F1 + logSlack b (finiteSetLogCard A1) :=
    Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (logSlack_mono_left (by omega) _)
  -- The transported strength is inside the same slack.
  have hstrength :
      hereditaryStrongTransportStrength cTrans p_F1 (cFam * (p_F1 + s_F1) + cFam) ≤
        hereditarySlack (b ^ 34) delta epsilon n := by
    rw [hereditarySlack_eq_mul_unit, hsF1def]
    exact hereditary_core_budget_strength hb (one_le_hereditaryUnit delta epsilon n)
      (bitsLength_le_hereditaryUnit delta epsilon hsqrt1) (show cGap ≤ b by omega)
      (show cFam ≤ b by omega) (show cTrans ≤ b by omega) hcardA hpF1U hgapU
  refine ⟨F, hF, hA_F, hF_strong.mono hstrength, ?_, ?_⟩
  · rw [hFVal, hMVal]
    have : fComp ≤ mComp + hereditarySlack (b ^ 34) delta epsilon n := by omega
    exact_mod_cast this
  · have n11 : finiteSetLogCard M1 ≤ finiteSetLogCard M := finiteSetLogCard_mono hM1_card
    omega

end Kolmogorov
