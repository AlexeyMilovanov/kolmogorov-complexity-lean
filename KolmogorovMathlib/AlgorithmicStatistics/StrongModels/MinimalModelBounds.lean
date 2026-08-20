import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.StandardDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

theorem setComplexity_le_plainSetComplexity_of_logSlack_budget
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ C : Nat, ∀ S (hS : S.Nonempty) (N : Nat),
      plainSetComplexity V S hS ≤ (N : ENat) →
      setComplexity U S hS ≤ plainSetComplexity V S hS + (logSlack C N : ENat) := by
  obtain ⟨C, hC⟩ := KP_le_condK_of_logSlack_budget V U hV hU
  refine ⟨C, fun S hS N hbudget => ?_⟩
  -- `plainSetComplexity V S hS` is finite, so it equals its `toNat` value `k ≤ N`.
  have hfin : plainSetComplexity V S hS ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top N) hbudget
  set k := (plainSetComplexity V S hS).toNat with hk_def
  have hk : plainSetComplexity V S hS = (k : ENat) := (ENat.coe_toNat hfin).symm
  have hkN : k ≤ N := by
    have h : (k : ENat) ≤ (N : ENat) := hk ▸ hbudget
    exact_mod_cast h
  -- `plainSetComplexity V S hS = plainK V c = condK V c []` definitionally.
  have hcond : condK V (codedUniformOn S hS).code [] = (k : ENat) := hk
  have hKP := hC (codedUniformOn S hS).code [] k N hcond hkN
  calc setComplexity U S hS
      = KP U (codedUniformOn S hS).code [] := rfl
    _ ≤ ((k + logSlack C N : Nat) : ENat) := hKP
    _ = plainSetComplexity V S hS + (logSlack C N : ENat) := by
        rw [hk]; push_cast; ring

theorem isIJDescription_of_plain_model
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ C : Nat, ∀ x (A : Finset BitString) (hA : A.Nonempty) (i j N : Nat),
      x ∈ A →
      plainSetComplexity V A hA ≤ (i : ENat) →
      i ≤ N →
      finiteSetLogCard A ≤ (j : ENat) →
      IsIJDescription U x A hA (i + logSlack C N) j := by
  obtain ⟨C, hC⟩ := setComplexity_le_plainSetComplexity_of_logSlack_budget V U hV hU
  refine ⟨C, fun x A hA i j N hxA hcomp hiN hcard => ?_⟩
  refine ⟨hxA, ?_, ?_⟩
  · -- `setComplexity U A hA ≤ i + logSlack C N`.
    have hbudget : plainSetComplexity V A hA ≤ (N : ENat) :=
      hcomp.trans (by exact_mod_cast hiN)
    calc setComplexity U A hA
        ≤ plainSetComplexity V A hA + (logSlack C N : ENat) := hC A hA N hbudget
      _ ≤ (i : ENat) + (logSlack C N : ENat) := by gcongr
      _ = ((i + logSlack C N : Nat) : ENat) := by push_cast; ring
  · -- `A.card ≤ 2 ^ j` from `finiteSetLogCard A ≤ j`.
    have hj : finiteSetLogCard A ≤ j := by exact_mod_cast hcard
    exact (finiteSetLogCard_le_iff A j).mp hj

theorem minimalModel_competitor_complexity_gap
    {V : Map} {x : BitString} {A : Finset BitString} {hA : A.Nonempty} {delta kappa : Nat}
    (hmin : IsMinimalModel V x A hA delta kappa)
    {B : Finset BitString} {hB : B.Nonempty}
    (hxB : x ∈ B)
    (htwo :
      plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
      plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
        (kappa : ENat)) :
    plainSetComplexity V A hA ≤
      plainSetComplexity V B hB + (delta : ENat) :=
  -- `IsMinimalModel` forbids the competitor `B` from strictly improving on `A` by
  -- `delta`; in the linear order `ENat` the negation is exactly the desired bound.
  le_of_lt (not_le.mp (hmin.2 B hB hxB htwo))

theorem minimalModel_plainSetComplexity_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ cKappa c : Nat, ∀ x n A (hA : A.Nonempty) delta,
      x.length = n →
      IsMinimalModel V x A hA delta (logSlack cKappa n) →
      plainSetComplexity V A hA ≤
        (n + delta + logSlack c n : ENat) := by
  -- The full length-`n` cube `B ∋ x` has `C(B) = O(log n)` and `log #B = n`, and
  -- always contains `x`.  If its two-part parameters make the minimality premise
  -- hold, minimality forces `C(A) ≤ C(B) + delta`; otherwise the premise fails,
  -- which already bounds `C(A) < C(B) + n`.  Either way `C(A) ≤ n + delta + O(log n)`.
  -- The bound holds for every `kappa`, so we may pick `cKappa := 0`.
  obtain ⟨cCube, hCube⟩ := plainSetComplexity_fullCube_le_logSlack V hV
  refine ⟨0, cCube, fun x n A hA delta hxlen hmin => ?_⟩
  have hB : (stringsOfLength n).Nonempty := codedStringsOfLength_nonempty n
  have hxB : x ∈ stringsOfLength n := (memStringsOfLength n x).mpr hxlen
  have hCB : plainSetComplexity V (stringsOfLength n) hB ≤ (logSlack cCube n : ENat) :=
    hCube n
  have hlogB : (finiteSetLogCard (stringsOfLength n) : ENat) ≤ (n : ENat) := by
    have : finiteSetLogCard (stringsOfLength n) ≤ n :=
      (finiteSetLogCard_le_iff _ n).mpr (le_of_eq (cardStringsOfLength n))
    exact_mod_cast this
  by_cases hprem :
      plainSetComplexity V (stringsOfLength n) hB + (finiteSetLogCard (stringsOfLength n) : ENat) ≤
        plainSetComplexity V A hA + (finiteSetLogCard A : ENat) + (logSlack 0 n : ENat)
  · -- The full cube satisfies the two-part premise: minimality gives `C(A) ≤ C(B) + delta`.
    calc plainSetComplexity V A hA
        ≤ plainSetComplexity V (stringsOfLength n) hB + (delta : ENat) :=
          minimalModel_competitor_complexity_gap hmin hxB hprem
      _ ≤ (logSlack cCube n : ENat) + (delta : ENat) := by gcongr
      _ ≤ (n + delta + logSlack cCube n : ENat) := by
          have h : logSlack cCube n + delta ≤ n + delta + logSlack cCube n := by omega
          exact_mod_cast h
  · -- Otherwise the premise fails, directly bounding `C(A) < C(B) + log #B`.
    rw [not_le] at hprem
    have hstep : plainSetComplexity V A hA <
        plainSetComplexity V (stringsOfLength n) hB +
          (finiteSetLogCard (stringsOfLength n) : ENat) :=
      lt_of_le_of_lt (le_self_add.trans le_self_add) hprem
    have hbound : plainSetComplexity V A hA ≤ (logSlack cCube n : ENat) + (n : ENat) :=
      le_of_lt (lt_of_lt_of_le hstep (add_le_add hCB hlogB))
    calc plainSetComplexity V A hA
        ≤ (logSlack cCube n : ENat) + (n : ENat) := hbound
      _ ≤ (n + delta + logSlack cCube n : ENat) := by
          have h : logSlack cCube n + n ≤ n + delta + logSlack cCube n := by omega
          exact_mod_cast h

theorem standardModel_package
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (q : Code) (hq : IsCodeFor q V) :
    ∃ C : Nat, ∀ (x : BitString) (n i j : Nat)
      (A : Finset BitString) (hA : A.Nonempty),
      x.length = n →
      x ∈ A →
      plainSetComplexity V A hA = (i : ENat) →
      finiteSetLogCard A = (j : ENat) →
      ∃ (m r : Nat) (hxB : x ∈ standardBlock q m r x),
        let B := standardBlock q m r x
        let hB : B.Nonempty := ⟨x, hxB⟩
        -- m bound
        m ≤ min n (i + j + logSlack C (i + j)) + logSlack C n ∧
        -- cardinality bound
        B.card = 2 ^ r ∧
        -- no-worse two-part parameters (using r instead of logCard since B.card = 2^r)
        plainSetComplexity V B hB + (r : ENat) ≤
          (i + j : Nat) + (logSlack C n : ENat) ∧
        -- logarithmic C(B'|B)
        condK V (codedUniformOn B hB).code (codedUniformOn A hA).code ≤ (logSlack C n : ENat) ∧
        -- both C(B'|Ω_{C(B')}) and C(Ω_{C(B')}|B')
        condK V (codedUniformOn B hB).code
          (omegaFixedCode q (plainK V (codedUniformOn B hB).code).toNat) ≤ (logSlack C m : ENat) ∧
        condK V (omegaFixedCode q (plainK V (codedUniformOn B hB).code).toNat)
          (codedUniformOn B hB).code ≤ (logSlack C m : ENat) := by
  obtain ⟨C₃, h₃⟩ := isIJDescription_of_plain_model V U hV hU
  obtain ⟨C_bs, hbs⟩ := prop_better_std V U hV hU q hq
  obtain ⟨C_om, hom⟩ := prop_std_omega V hV q hq
  obtain ⟨Cf, hCf⟩ := logSlack_linear_bound C_bs (C_bs + 1) C_bs
  refine ⟨C₃ + C_bs + Cf + C_om, fun x n i j A hA hn hxA hcompeq hcardeq => ?_⟩
  set C := C₃ + C_bs + Cf + C_om with hCdef
  -- Convert the ordinary-plain `(i,j)`-data of `A` into a prefix `(i',j)`-description.
  have hIJ : IsIJDescription U x A hA (i + logSlack C₃ (i + j)) j :=
    h₃ x A hA i j (i + j) hxA (le_of_eq hcompeq) (Nat.le_add_right i j) (le_of_eq hcardeq)
  -- Run the standard-block improvement `prop_better_std`.
  obtain ⟨m, r, hxB, hmbound, hbcard, -, -, -, hnoworse, hcondBA⟩ :=
    hbs x n (i + logSlack C₃ (i + j)) j A hA hn hIJ
  have hB : (standardBlock q m r x).Nonempty := ⟨x, hxB⟩
  set B := standardBlock q m r x with hBdef
  -- `m` is capped by `n` up to `O(log n)`.
  have hm_le_n : m ≤ n + logSlack C_bs n :=
    le_trans hmbound (Nat.add_le_add_right (Nat.min_le_left _ _) _)
  -- Folding lemma: `a ≤ n + logSlack C_bs n ⇒ logSlack C_bs a ≤ logSlack Cf n`.
  have hfold : ∀ a : ℕ, a ≤ n + logSlack C_bs n → logSlack C_bs a ≤ logSlack Cf n := by
    intro a ha
    have hlen := length_natBits_le_self n
    have hmul : C_bs * (Nat.bits n).length ≤ C_bs * n := Nat.mul_le_mul_left _ hlen
    have ha2 : a ≤ (C_bs + 1) * n + C_bs := by
      calc a ≤ n + logSlack C_bs n := ha
        _ = n + (C_bs * (Nat.bits n).length + C_bs) := by rw [logSlack]
        _ ≤ n + (C_bs * n + C_bs) := by omega
        _ = (C_bs + 1) * n + C_bs := by ring
    exact (logSlack_mono_right C_bs ha2).trans (hCf n)
  -- `min n (i'+j') ≤ i + j + logSlack C₃ n` (unconditional; the crux of the two-part bound).
  have hmin_ij : min n (i + logSlack C₃ (i + j) + j) ≤ i + j + logSlack C₃ n := by
    rcases Nat.lt_or_ge (i + j) n with h | h
    · refine le_trans (Nat.min_le_right _ _) ?_
      have heq : i + logSlack C₃ (i + j) + j = i + j + logSlack C₃ (i + j) := by ring
      rw [heq]
      exact Nat.add_le_add_left (logSlack_mono_right C₃ h.le) _
    · exact le_trans (Nat.min_le_left _ _) (le_trans h (Nat.le_add_right _ _))
  have hm_le_ij : m ≤ i + j + logSlack C₃ n + logSlack C_bs n := by
    have h := Nat.add_le_add_right hmin_ij (logSlack C_bs n)
    omega
  -- (m-bound conjunct)
  have hmb : m ≤ min n (i + j + logSlack C (i + j)) + logSlack C n := by
    refine le_trans hmbound (Nat.add_le_add ?_ (logSlack_mono_left (by omega) n))
    refine min_le_min (le_refl n) ?_
    have heq : i + logSlack C₃ (i + j) + j = i + j + logSlack C₃ (i + j) := by ring
    rw [heq]
    exact Nat.add_le_add_left (logSlack_mono_left (by omega) _) _
  -- (two-part conjunct)
  have htwo : plainSetComplexity V B hB + (r : ENat) ≤ (i + j : Nat) + (logSlack C n : ENat) := by
    have hmn : (m : ENat) ≤ ((i + j + logSlack C₃ n + logSlack C_bs n : ℕ) : ENat) := by
      exact_mod_cast hm_le_ij
    have hsn : (logSlack C_bs m : ENat) ≤ (logSlack Cf n : ENat) := by
      exact_mod_cast hfold m hm_le_n
    have hsum : i + j + logSlack C₃ n + logSlack C_bs n + logSlack Cf n ≤ i + j + logSlack C n := by
      have hfold3 : logSlack C₃ n + logSlack C_bs n + logSlack Cf n ≤ logSlack C n := by
        rw [logSlack_add_const, logSlack_add_const]
        exact logSlack_mono_left (by omega) n
      omega
    calc plainSetComplexity V B hB + (r : ENat)
        = plainK V (codedUniformOn B hB).code + (r : ENat) := rfl
      _ ≤ (m : ENat) + (logSlack C_bs m : ENat) := hnoworse
      _ ≤ ((i + j + logSlack C₃ n + logSlack C_bs n : ℕ) : ENat) + (logSlack Cf n : ENat) :=
          add_le_add hmn hsn
      _ = ((i + j + logSlack C₃ n + logSlack C_bs n + logSlack Cf n : ℕ) : ENat) := by
          push_cast; ring
      _ ≤ ((i + j : Nat) : ENat) + (logSlack C n : ENat) := by
          calc ((i + j + logSlack C₃ n + logSlack C_bs n + logSlack Cf n : ℕ) : ENat)
              ≤ (((i + j) + logSlack C n : ℕ) : ENat) := by exact_mod_cast hsum
            _ = ((i + j : Nat) : ENat) + (logSlack C n : ENat) := by push_cast; ring
  -- (C(B|A) conjunct)
  have hcondBA' : condK V (codedUniformOn B hB).code (codedUniformOn A hA).code ≤
      (logSlack C n : ENat) := by
    calc condK V (codedUniformOn B hB).code (codedUniformOn A hA).code
        ≤ (logSlack C_bs m : ENat) := hcondBA
      _ ≤ (logSlack Cf n : ENat) := by exact_mod_cast hfold m hm_le_n
      _ ≤ (logSlack C n : ENat) := by exact_mod_cast logSlack_mono_left (by omega) n
  -- (omega conjuncts)
  have hne : plainK V (codedUniformOn B hB).code ≠ ⊤ := condK_ne_top_of_optimal V hV _ []
  set kB := (plainK V (codedUniformOn B hB).code).toNat with hkBdef
  have hkB_eq : plainK V (codedUniformOn B hB).code = (kB : ENat) := (ENat.coe_toNat hne).symm
  obtain ⟨hBOm, hOmB⟩ := hom m r kB x hxB hkB_eq
  have hBOmega : condK V (codedUniformOn B hB).code (omegaFixedCode q kB) ≤
      (logSlack C m : ENat) := by
    calc condK V (codedUniformOn B hB).code (omegaFixedCode q kB)
        ≤ (logSlack C_om m : ENat) := hBOm
      _ ≤ (logSlack C m : ENat) := by exact_mod_cast logSlack_mono_left (by omega) m
  have hOmegaB : condK V (omegaFixedCode q kB) (codedUniformOn B hB).code ≤
      (logSlack C m : ENat) := by
    calc condK V (omegaFixedCode q kB) (codedUniformOn B hB).code
        ≤ (logSlack C_om m : ENat) := hOmB
      _ ≤ (logSlack C m : ENat) := by exact_mod_cast logSlack_mono_left (by omega) m
  exact ⟨m, r, hxB, hmb, hbcard, htwo, hcondBA', hBOmega, hOmegaB⟩

end Kolmogorov
