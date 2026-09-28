import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock.PrefixEquiv

/-!
# Standard blocks against the finite Omega code

The conditional bounds between a standard block and the fixed-width code `omegaFixedCode c m` of
`omegaCount c m`, at indices above and below `m - j`: `omegaFixedCode_cond_shorter_le`,
`omegaFixedCode_cond_longer_le`, `omegaFixedCode_close_logSlack` and
`omegaFixedCode_bridge_linear`, assembled into the endpoint `prop_std_omega` (VS40 Section 4,
Milestone B7).
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- A number inside the budget `m + logSlack C₀ m` has binary length inside the slightly larger
slack `logSlack (C₀ + 2) m`. -/
theorem bitsLength_le_logSlack_of_le_budget (C₀ m q : ℕ) (hq : q ≤ m + logSlack C₀ m) :
    (Nat.bits q).length ≤ logSlack (C₀ + 2) m := by
  calc
    (Nat.bits q).length
        ≤ (Nat.bits (m + logSlack C₀ m)).length := length_natBits_mono hq
    _ ≤ (Nat.bits m).length + (Nat.bits (logSlack C₀ m)).length + 1 :=
      length_natBits_add_le m (logSlack C₀ m)
    _ ≤ (Nat.bits m).length + logSlack C₀ m + 1 := by
      gcongr
      exact length_natBits_le (logSlack C₀ m)
    _ ≤ logSlack (C₀ + 2) m := by
      unfold logSlack
      calc
        (Nat.bits m).length + (C₀ * (Nat.bits m).length + C₀) + 1
          = (C₀ + 1) * (Nat.bits m).length + (C₀ + 1) := by ring
        _ ≤ (C₀ + 2) * (Nat.bits m).length + (C₀ + 2) := by gcongr <;> omega

/-- The shorter of two finite Omega codes is determined by the longer one with logarithmic
advice, as soon as both indices are inside the budget `m + logSlack C₀ m`. -/
theorem omegaFixedCode_cond_shorter_le
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ (m lo hi : ℕ), lo ≤ hi →
      lo ≤ m + logSlack C₀ m → hi ≤ m + logSlack C₀ m →
      condK V (omegaFixedCode c lo) (omegaFixedCode c hi) ≤ (logSlack C m : ENat) := by
  obtain ⟨Ceq, heq⟩ := prop_omega_equivalence V hV c hc
  obtain ⟨Ctake, htake⟩ := condK_take_le V hV
  obtain ⟨Ctrans, htrans⟩ := condK_trans_nat V hV
  refine ⟨(Ceq + 2) * (C₀ + 2) + 2 * Ctake + Ceq + Ctrans, ?_⟩
  set C := (Ceq + 2) * (C₀ + 2) + 2 * Ctake + Ceq + Ctrans with hC
  intro m lo hi hlohi hloM hhiM
  set H := logSlack (C₀ + 2) m with hH
  let pref := (omegaFixedCode c hi).take lo
  have htakeNat :
      condK V pref (omegaFixedCode c hi) ≤
        (((Nat.bits lo).length + Ctake : ℕ) : ENat) := by
    simpa [pref] using htake (omegaFixedCode c hi) lo
  have heqNat :
      condK V (omegaFixedCode c lo) pref ≤ (logSlack Ceq hi : ENat) := by
    simpa [pref] using (heq hi lo hlohi).1
  have hcomposed :=
    htrans (omegaFixedCode c hi) pref (omegaFixedCode c lo)
      ((Nat.bits lo).length + Ctake) (logSlack Ceq hi) htakeNat heqNat
  have hloBits := bitsLength_le_logSlack_of_le_budget C₀ m lo hloM
  have hhiBits := bitsLength_le_logSlack_of_le_budget C₀ m hi hhiM
  have hbudget :
      2 * ((Nat.bits lo).length + Ctake) + logSlack Ceq hi + Ctrans ≤ logSlack C m := by
    have hcoefficient : (Ceq + 2) * (C₀ + 2) ≤ C := by
      rw [hC]
      omega
    calc
      2 * ((Nat.bits lo).length + Ctake) + logSlack Ceq hi + Ctrans
          = 2 * (Nat.bits lo).length + 2 * Ctake +
              (Ceq * (Nat.bits hi).length + Ceq) + Ctrans := by
            unfold logSlack
            ring
      _ ≤ 2 * H + 2 * Ctake + (Ceq * H + Ceq) + Ctrans := by gcongr
      _ = (Ceq + 2) * (C₀ + 2) * (Nat.bits m).length + C := by
            rw [hH, hC]
            unfold logSlack
            ring
      _ ≤ C * (Nat.bits m).length + C :=
        Nat.add_le_add (Nat.mul_le_mul_right (Nat.bits m).length hcoefficient) le_rfl
      _ = logSlack C m := by
        unfold logSlack
        ring
  exact hcomposed.trans (by exact_mod_cast hbudget)

/-- The longer of two finite Omega codes is determined by the shorter one with logarithmic
advice, as soon as its index is inside the budget `m + logSlack C₀ m` and exceeds the shorter
index by at most `logSlack C₀ m`. -/
theorem omegaFixedCode_cond_longer_le
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ (m lo hi : ℕ), lo ≤ hi →
      hi ≤ m + logSlack C₀ m → hi ≤ lo + logSlack C₀ m →
      condK V (omegaFixedCode c hi) (omegaFixedCode c lo) ≤ (logSlack C m : ENat) := by
  obtain ⟨Ceq, heq⟩ := prop_omega_equivalence V hV c hc
  obtain ⟨Cdrop, hdrop⟩ := condK_of_take_le V hV
  obtain ⟨Ctrans, htrans⟩ := condK_trans_nat V hV
  refine ⟨(2 * Ceq + 1) * (C₀ + 2) + 2 * Ceq + Cdrop + Ctrans + 1, ?_⟩
  set C := (2 * Ceq + 1) * (C₀ + 2) + 2 * Ceq + Cdrop + Ctrans + 1 with hC
  intro m lo hi hlohi hhiM hhilo
  set S := logSlack C₀ m with hS
  set H := logSlack (C₀ + 2) m with hH
  let pref := (omegaFixedCode c hi).take lo
  have heqNat :
      condK V pref (omegaFixedCode c lo) ≤ (logSlack Ceq hi : ENat) := by
    simpa [pref] using (heq hi lo hlohi).2
  have hdropNat :
      condK V (omegaFixedCode c hi) pref ≤
        ((((omegaFixedCode c hi).drop lo).length + Cdrop : ℕ) : ENat) := by
    simpa [pref] using hdrop (omegaFixedCode c hi) lo
  have hcomposed :=
    htrans (omegaFixedCode c lo) pref (omegaFixedCode c hi)
      (logSlack Ceq hi) (((omegaFixedCode c hi).drop lo).length + Cdrop) heqNat hdropNat
  have hhiBits := bitsLength_le_logSlack_of_le_budget C₀ m hi hhiM
  have hdropLen : ((omegaFixedCode c hi).drop lo).length ≤ S + 1 := by
    rw [List.length_drop, omegaFixedCode_length]
    omega
  have hbudget :
      2 * logSlack Ceq hi + (((omegaFixedCode c hi).drop lo).length + Cdrop) + Ctrans ≤
        logSlack C m := by
    have hcoefficient : 2 * Ceq * (C₀ + 2) + C₀ ≤ C := by
      rw [hC]
      calc
        2 * Ceq * (C₀ + 2) + C₀
            ≤ 2 * Ceq * (C₀ + 2) + (C₀ + 2) + 2 * Ceq + Cdrop + Ctrans + 1 := by omega
        _ = (2 * Ceq + 1) * (C₀ + 2) + 2 * Ceq + Cdrop + Ctrans + 1 := by ring
    have hconstant :
        2 * Ceq * (C₀ + 2) + 2 * Ceq + C₀ + 1 + Cdrop + Ctrans ≤ C := by
      rw [hC]
      calc
        2 * Ceq * (C₀ + 2) + 2 * Ceq + C₀ + 1 + Cdrop + Ctrans
            ≤ 2 * Ceq * (C₀ + 2) + (C₀ + 2) + 2 * Ceq + Cdrop + Ctrans + 1 := by omega
        _ = (2 * Ceq + 1) * (C₀ + 2) + 2 * Ceq + Cdrop + Ctrans + 1 := by ring
    calc
      2 * logSlack Ceq hi + (((omegaFixedCode c hi).drop lo).length + Cdrop) + Ctrans
          = 2 * (Ceq * (Nat.bits hi).length + Ceq) +
              ((omegaFixedCode c hi).drop lo).length + Cdrop + Ctrans := by
            unfold logSlack
            ring
      _ ≤ 2 * (Ceq * H + Ceq) + (S + 1) + Cdrop + Ctrans := by gcongr
      _ = (2 * Ceq * (C₀ + 2) + C₀) * (Nat.bits m).length +
            (2 * Ceq * (C₀ + 2) + 2 * Ceq + C₀ + 1 + Cdrop + Ctrans) := by
            rw [hH, hS]
            unfold logSlack
            ring
      _ ≤ C * (Nat.bits m).length + C :=
        Nat.add_le_add
          (Nat.mul_le_mul_right (Nat.bits m).length hcoefficient) hconstant
      _ = logSlack C m := by
        unfold logSlack
        ring
  exact hcomposed.trans (by exact_mod_cast hbudget)

/-- Finite Omega codes at logarithmically close indices determine each other
with logarithmic advice.  This is the explicit nearby-index bridge needed when
the exact plain complexity of a standard block is slightly above or below its
position coordinate `m-j`. -/
theorem omegaFixedCode_close_logSlack
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ (m a b : ℕ),
      a ≤ m + logSlack C₀ m →
      b ≤ m + logSlack C₀ m →
      a ≤ b + logSlack C₀ m →
      b ≤ a + logSlack C₀ m →
      condK V (omegaFixedCode c a) (omegaFixedCode c b) ≤
          (logSlack C m : ENat) ∧
      condK V (omegaFixedCode c b) (omegaFixedCode c a) ≤
          (logSlack C m : ENat) := by
  obtain ⟨CShort, hShort⟩ := omegaFixedCode_cond_shorter_le V hV c hc C₀
  obtain ⟨CLong, hLong⟩ := omegaFixedCode_cond_longer_le V hV c hc C₀
  refine ⟨CShort + CLong, fun m a b haM hbM hab hba => ?_⟩
  have hmonoShort : (logSlack CShort m : ENat) ≤ (logSlack (CShort + CLong) m : ENat) := by
    exact_mod_cast logSlack_mono_left (by omega) m
  have hmonoLong : (logSlack CLong m : ENat) ≤ (logSlack (CShort + CLong) m : ENat) := by
    exact_mod_cast logSlack_mono_left (by omega) m
  by_cases hab' : a ≤ b
  · exact ⟨(hShort m a b hab' haM hbM).trans hmonoShort,
      (hLong m a b hab' hbM hba).trans hmonoLong⟩
  · have hba' : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab')
    exact ⟨(hLong m b a hba' haM hab).trans hmonoLong,
      (hShort m b a hba' hbM haM).trans hmonoShort⟩

/-- Finite Omega codes at a linear gap determine one another with linear advice.
This is the explicit bridge needed for the minimal-model hereditary property. -/
theorem omegaFixedCode_bridge_linear
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ (m a b : ℕ),
      a ≤ m + logSlack C₀ m →
      b ≤ m + logSlack C₀ m →
      condK V (omegaFixedCode c a) (omegaFixedCode c b) ≤
          ((a - b) + logSlack C m : ENat) := by
  obtain ⟨Ceq, heq⟩ := prop_omega_equivalence V hV c hc
  obtain ⟨Ctake, htake⟩ := condK_take_le V hV
  obtain ⟨Cdrop, hdrop⟩ := condK_of_take_le V hV
  obtain ⟨Ctrans, htrans⟩ := condK_trans_nat V hV
  let C₁ := (Ceq + 2) * (C₀ + 2) + 2 * Ctake + Ceq + Ctrans + 2
  let C₂ := 2 * Ceq * (C₀ + 2) + Cdrop + Ctrans + 2 * Ceq + 2
  let C := C₁ + C₂
  refine ⟨C, fun m a b haM hbM => ?_⟩
  let S := logSlack C₀ m
  let H := logSlack (C₀ + 2) m
  have hS : S ≤ H := logSlack_mono_left (by omega) m
  have hbits_of_le : ∀ q, q ≤ m + S → (Nat.bits q).length ≤ H := by
    intro q hq
    calc
      (Nat.bits q).length ≤ (Nat.bits (m + S)).length := length_natBits_mono hq
      _ ≤ (Nat.bits m).length + (Nat.bits S).length + 1 := length_natBits_add_le m S
      _ ≤ (Nat.bits m).length + S + 1 := by gcongr; exact length_natBits_le S
      _ ≤ H := by
        dsimp [H, S]; unfold logSlack
        calc (Nat.bits m).length + (C₀ * (Nat.bits m).length + C₀) + 1
          = (C₀ + 1) * (Nat.bits m).length + (C₀ + 1) := by ring
        _ ≤ (C₀ + 2) * (Nat.bits m).length + (C₀ + 2) := by gcongr <;> omega
  by_cases hab : a ≤ b
  · let pref := (omegaFixedCode c b).take a
    have htakeNat : condK V pref (omegaFixedCode c b) ≤
        (((Nat.bits a).length + Ctake : ℕ) : ENat) := by
      simpa [pref] using htake (omegaFixedCode c b) a
    have heqNat : condK V (omegaFixedCode c a) pref ≤ (logSlack Ceq b : ENat) := by
      simpa [pref] using (heq b a hab).1
    have hcomposed := htrans (omegaFixedCode c b) pref (omegaFixedCode c a)
      ((Nat.bits a).length + Ctake) (logSlack Ceq b) htakeNat heqNat
    have hbudget : (a - b) + 2 * ((Nat.bits a).length + Ctake) + logSlack Ceq b + Ctrans ≤
        (a - b) + logSlack C₁ m := by
      have hab_zero : a - b = 0 := Nat.sub_eq_zero_of_le hab
      rw [hab_zero, zero_add, zero_add]
      calc 2 * ((Nat.bits a).length + Ctake) + logSlack Ceq b + Ctrans
        = 2 * (Nat.bits a).length + 2 * Ctake +
          (Ceq * (Nat.bits b).length + Ceq) + Ctrans := by unfold logSlack; omega
        _ ≤ 2 * H + 2 * Ctake + (Ceq * H + Ceq) + Ctrans := by
          gcongr
          · exact hbits_of_le a haM
          · exact hbits_of_le b hbM
        _ = (Ceq + 2) * H + 2 * Ctake + Ceq + Ctrans := by ring
        _ = (Ceq + 2) * ( (C₀ + 2) * (Nat.bits m).length + (C₀ + 2) ) +
            2 * Ctake + Ceq + Ctrans := by dsimp [H]; unfold logSlack; rfl
        _ = (Ceq + 2) * (C₀ + 2) * (Nat.bits m).length +
            ( (Ceq + 2) * (C₀ + 2) + 2 * Ctake + Ceq + Ctrans ) := by ring
        _ ≤ C₁ * (Nat.bits m).length + C₁ := by
          apply Nat.add_le_add
          · apply Nat.mul_le_mul_right; dsimp [C₁]; omega
          · dsimp [C₁]; omega
        _ = logSlack C₁ m := by unfold logSlack; rfl
    have hC : logSlack C₁ m ≤ logSlack C m := logSlack_mono_left (by dsimp [C, C₁, C₂]; omega) m
    calc condK V (omegaFixedCode c a) (omegaFixedCode c b)
      ≤ ↑(2 * ((Nat.bits a).length + Ctake) + logSlack Ceq b + Ctrans) := hcomposed
      _ = ↑((a - b) + 2 * ((Nat.bits a).length + Ctake) + logSlack Ceq b + Ctrans) := by
          have hab_zero : a - b = 0 := Nat.sub_eq_zero_of_le hab
          rw [hab_zero, zero_add]
      _ ≤ ((a - b) + logSlack C m : ENat) := by
          exact_mod_cast (hbudget.trans (Nat.add_le_add_left hC _))
  · have hba : b ≤ a := Nat.le_of_lt (not_le.mp hab)
    let pref := (omegaFixedCode c a).take b
    have hdropNat : condK V (omegaFixedCode c a) pref ≤
        ((((omegaFixedCode c a).drop b).length + Cdrop : ℕ) : ENat) := by
      simpa [pref] using hdrop (omegaFixedCode c a) b
    have heqNat : condK V pref (omegaFixedCode c b) ≤ (logSlack Ceq a : ENat) := by
      simpa [pref] using (heq a b hba).2
    have hcomposed := htrans (omegaFixedCode c b) pref (omegaFixedCode c a)
      (logSlack Ceq a) (((omegaFixedCode c a).drop b).length + Cdrop) heqNat hdropNat
    have hdropLen : ((omegaFixedCode c a).drop b).length = (a - b) + 1 := by
      rw [List.length_drop, omegaFixedCode_length]
      omega
    have hbudget : 2 * logSlack Ceq a + (((omegaFixedCode c a).drop b).length + Cdrop) +
        Ctrans ≤ (a - b) + logSlack C₂ m := by
      rw [hdropLen]
      calc 2 * logSlack Ceq a + (a - b + 1 + Cdrop) + Ctrans
        = (a - b) + (2 * logSlack Ceq a + 1 + Cdrop + Ctrans) := by omega
        _ ≤ (a - b) + (2 * (Ceq * H + Ceq) + 1 + Cdrop + Ctrans) := by
          unfold logSlack; gcongr; exact hbits_of_le a haM
        _ = (a - b) + (2 * Ceq * H + 2 * Ceq + 1 + Cdrop + Ctrans) := by ring
        _ = (a - b) + (2 * Ceq * ((C₀ + 2) * (Nat.bits m).length + (C₀ + 2)) +
            2 * Ceq + 1 + Cdrop + Ctrans) := by dsimp [H]; unfold logSlack; rfl
        _ = (a - b) + (2 * Ceq * (C₀ + 2) * (Nat.bits m).length +
            (2 * Ceq * (C₀ + 2) + 2 * Ceq + 1 + Cdrop + Ctrans)) := by ring
        _ ≤ (a - b) + (C₂ * (Nat.bits m).length + C₂) := by
          apply Nat.add_le_add_left
          apply Nat.add_le_add
          · apply Nat.mul_le_mul_right; dsimp [C₂]; omega
          · dsimp [C₂]; omega
        _ = (a - b) + logSlack C₂ m := by unfold logSlack; rfl
    have hC : logSlack C₂ m ≤ logSlack C m := logSlack_mono_left (by dsimp [C, C₁, C₂]; omega) m
    calc condK V (omegaFixedCode c a) (omegaFixedCode c b)
      ≤ ↑(2 * logSlack Ceq a + (((omegaFixedCode c a).drop b).length + Cdrop) + Ctrans) := hcomposed
      _ ≤ ((a - b) + logSlack C m : ENat) := by
          exact_mod_cast (hbudget.trans (Nat.add_le_add_left hC _))

/-- Proposition `prop:std-omega`.  If a standard block has exact plain
complexity `i`, its canonical code and the fixed-width finite Omega code
`omegaFixedCode c i` determine one another with uniform plain conditional
advice. -/
theorem prop_std_omega
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j i : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code =
            (i : ENat) →
      condK V (codedUniformOn (standardBlock c m j x) hA).code
          (omegaFixedCode c i) ≤ (logSlack C m : ENat) ∧
      condK V (omegaFixedCode c i)
          (codedUniformOn (standardBlock c m j x) hA).code ≤
            (logSlack C m : ENat) := by
  obtain ⟨Cclose, hclose⟩ :=
    standardBlock_plainK_index_close_plain V hV c hc
  obtain ⟨Cblock, hblock⟩ :=
    standardBlock_omegaPrefix_equiv V hV c
  obtain ⟨Comega, homega⟩ :=
    prop_omega_equivalence V hV c hc
  obtain ⟨Cnear, hnear⟩ :=
    omegaFixedCode_close_logSlack V hV c hc Cclose
  obtain ⟨Ctrans, htrans⟩ :=
    condK_trans_nat V hV
  let C :=
    4 * (Cnear + Cblock + Comega + Ctrans + 1)
  refine ⟨C, fun m j i x hx => ?_⟩
  intro hA hplain
  let k := m - j
  let BCode :=
    (codedUniformOn (standardBlock c m j x) hA).code
  let pref := (omegaFixedCode c m).take k
  let omegaK := omegaFixedCode c k
  let omegaI := omegaFixedCode c i
  have hkM : k ≤ m := by
    dsimp [k]
    omega
  have hidx := hclose m j i x hx hplain
  have hiUpper :
      i ≤ m + logSlack Cclose m := by
    omega
  have hkUpper :
      k ≤ m + logSlack Cclose m := by
    omega
  have hnearKI :
      condK V omegaK omegaI ≤
          (logSlack Cnear m : ENat) ∧
      condK V omegaI omegaK ≤
          (logSlack Cnear m : ENat) := by
    apply hnear m k i hkUpper hiUpper
    · simpa [k] using hidx.2
    · simpa [k] using hidx.1
  have homegaKP :
      condK V omegaK pref ≤
          (logSlack Comega m : ENat) ∧
      condK V pref omegaK ≤
          (logSlack Comega m : ENat) := by
    simpa [omegaK, pref, k] using homega m k hkM
  have hblockBP :
      condK V BCode pref ≤
          (logSlack Cblock m : ENat) ∧
      condK V pref BCode ≤
          (logSlack Cblock m : ENat) := by
    simpa [BCode, pref, k] using hblock m j x hx
  have hOmegaIToPref :
      condK V pref omegaI ≤
        ((2 * logSlack Cnear m +
          logSlack Comega m + Ctrans : ℕ) : ENat) :=
    htrans omegaI omegaK pref
      (logSlack Cnear m) (logSlack Comega m)
      hnearKI.1 homegaKP.2
  have hOmegaIToBlock :
      condK V BCode omegaI ≤
        ((2 * (2 * logSlack Cnear m +
          logSlack Comega m + Ctrans) +
          logSlack Cblock m + Ctrans : ℕ) : ENat) :=
    htrans omegaI pref BCode
      (2 * logSlack Cnear m +
        logSlack Comega m + Ctrans)
      (logSlack Cblock m)
      hOmegaIToPref hblockBP.1
  have hBlockToOmegaK :
      condK V omegaK BCode ≤
        ((2 * logSlack Cblock m +
          logSlack Comega m + Ctrans : ℕ) : ENat) :=
    htrans BCode pref omegaK
      (logSlack Cblock m) (logSlack Comega m)
      hblockBP.2 homegaKP.1
  have hBlockToOmegaI :
      condK V omegaI BCode ≤
        ((2 * (2 * logSlack Cblock m +
          logSlack Comega m + Ctrans) +
          logSlack Cnear m + Ctrans : ℕ) : ENat) :=
    htrans BCode omegaK omegaI
      (2 * logSlack Cblock m +
        logSlack Comega m + Ctrans)
      (logSlack Cnear m)
      hBlockToOmegaK hnearKI.2
  have hbudget₁ :
      2 * (2 * logSlack Cnear m +
          logSlack Comega m + Ctrans) +
          logSlack Cblock m + Ctrans ≤
        logSlack C m := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le (Cnear * (Nat.bits m).length),
      Nat.zero_le (Cblock * (Nat.bits m).length),
      Nat.zero_le (Comega * (Nat.bits m).length)]
  have hbudget₂ :
      2 * (2 * logSlack Cblock m +
          logSlack Comega m + Ctrans) +
          logSlack Cnear m + Ctrans ≤
        logSlack C m := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le (Cnear * (Nat.bits m).length),
      Nat.zero_le (Cblock * (Nat.bits m).length),
      Nat.zero_le (Comega * (Nat.bits m).length)]
  exact ⟨
    hOmegaIToBlock.trans (by exact_mod_cast hbudget₁),
    hBlockToOmegaI.trans (by exact_mod_cast hbudget₂)⟩

/-- Five successive conditional descriptions compose: if each `x_{i+1}` is described from `x_i`
in `a_i` bits, then `x₅` is described from `x₀` in `16a₁ + 8a₂ + 4a₃ + 2a₄ + a₅ + C` bits,
the doubling paying for the delimiters of the concatenated programs. -/
theorem condK_chain_five
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ x₀ x₁ x₂ x₃ x₄ x₅ (a₁ a₂ a₃ a₄ a₅ : Nat),
      condK V x₁ x₀ ≤ (a₁ : ENat) →
      condK V x₂ x₁ ≤ (a₂ : ENat) →
      condK V x₃ x₂ ≤ (a₃ : ENat) →
      condK V x₄ x₃ ≤ (a₄ : ENat) →
      condK V x₅ x₄ ≤ (a₅ : ENat) →
      condK V x₅ x₀ ≤
        ((16*a₁ + 8*a₂ + 4*a₃ + 2*a₄ + a₅ + C : Nat) : ENat) := by
  obtain ⟨C, hC⟩ := condK_trans_nat V hV
  use 15 * C
  intro x₀ x₁ x₂ x₃ x₄ x₅ a₁ a₂ a₃ a₄ a₅ h1 h2 h3 h4 h5
  have h20 := hC x₀ x₁ x₂ a₁ a₂ h1 h2
  have h30 := hC x₀ x₂ x₃ _ a₃ h20 h3
  have h40 := hC x₀ x₃ x₄ _ a₄ h30 h4
  have h50 := hC x₀ x₄ x₅ _ a₅ h40 h5
  apply le_trans h50
  norm_cast
  omega

end Kolmogorov


