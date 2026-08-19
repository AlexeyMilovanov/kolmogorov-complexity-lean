import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rel
import Mathlib.Data.Nat.Choose.Basic
import KolmogorovMathlib.CommonInformation.RectangleCover

namespace Kolmogorov

variable {α β : Type*}

lemma ceilHalf_pow_square_bounds (γ : Nat) :
  2 ^ γ ≤ (2 ^ ((γ + 1) / 2)) ^ 2 ∧
  Nat.choose (2 ^ ((γ + 1) / 2)) 2 ≤ 2 ^ γ := by
  let h := (γ + 1) / 2
  have hγ : γ ≤ 2 * h := by
    dsimp [h]
    omega
  have hh : 2 * h ≤ γ + 1 := by
    dsimp [h]
    omega
  have hpγ : 2 ^ γ ≤ 2 ^ (2 * h) :=
    Nat.pow_le_pow_right (by omega) hγ
  have hph : 2 ^ (2 * h) = (2 ^ h) ^ 2 := by
    rw [mul_comm, pow_mul]
  constructor
  · simpa [hph] using hpγ
  · rw [Nat.choose_two_right]
    apply Nat.div_le_of_le_mul
    calc
      2 ^ h * (2 ^ h - 1) ≤ 2 ^ h * 2 ^ h :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (2 ^ h) ^ 2 := by rw [pow_two]
      _ = 2 ^ (2 * h) := hph.symm
      _ ≤ 2 ^ (γ + 1) := Nat.pow_le_pow_right (by omega) hh
      _ = 2 * 2 ^ γ := by rw [pow_succ, mul_comm]

open Classical in
lemma noFourCycle_interedges_card_le_pow
    (r : α → β → Prop) {A : Finset α} {B : Finset β} {β' γ : Nat} :
  NoFourCycle r →
  A.card ≤ 2 ^ β' →
  B.card ≤ 2 ^ γ →
  (Rel.interedges r A B).card ≤
    2 ^ (γ + 1) +
      2 ^ (β' + (γ + 1) / 2 + 1) := by
  intro hfour hAcard hBcard
  let h := (γ + 1) / 2
  let q := 2 ^ h
  have hceil := ceilHalf_pow_square_bounds γ
  have hγ : γ ≤ 2 * h := by
    dsimp [h]
    omega
  by_cases hsmall : A.card ≤ q
  · have hcoarse := card_interedges_le_card_right_add_choose_two_left r A B hfour
    have hchoose : Nat.choose A.card 2 ≤ 2 ^ γ :=
      (Nat.choose_le_choose 2 hsmall).trans (by simpa [q, h] using hceil.2)
    calc
      (Rel.interedges r A B).card
          ≤ B.card + Nat.choose A.card 2 := hcoarse
      _ ≤ 2 ^ γ + 2 ^ γ := Nat.add_le_add hBcard hchoose
      _ = 2 ^ (γ + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ (γ + 1) + 2 ^ (β' + (γ + 1) / 2 + 1) :=
        Nat.le_add_right _ _
  · have hqA : q ≤ A.card := by omega
    have hsample := noFourCycle_sampled_interedges_bound r A B hfour hqA
    have hchoose : Nat.choose q 2 ≤ 2 ^ γ := by
      simpa [q, h] using hceil.2
    have hsum : B.card + Nat.choose q 2 ≤ 2 ^ (γ + 1) := by
      calc
        B.card + Nat.choose q 2 ≤ 2 ^ γ + 2 ^ γ :=
          Nat.add_le_add hBcard hchoose
        _ = 2 ^ (γ + 1) := by rw [pow_succ]; omega
    have hrhs : A.card * (B.card + Nat.choose q 2) ≤
        q * 2 ^ (β' + h + 1) := by
      calc
        A.card * (B.card + Nat.choose q 2)
            ≤ 2 ^ β' * 2 ^ (γ + 1) := Nat.mul_le_mul hAcard hsum
        _ = 2 ^ (β' + (γ + 1)) := (pow_add 2 β' (γ + 1)).symm
        _ ≤ 2 ^ (h + (β' + h + 1)) := by
          apply Nat.pow_le_pow_right (by omega)
          omega
        _ = q * 2 ^ (β' + h + 1) := by simp [q, pow_add]
    have hmul : q * (Rel.interedges r A B).card ≤
        q * 2 ^ (β' + h + 1) := hsample.trans hrhs
    have hedge : (Rel.interedges r A B).card ≤ 2 ^ (β' + h + 1) :=
      Nat.le_of_mul_le_mul_left hmul (by positivity)
    exact hedge.trans (Nat.le_add_left _ _)

open Classical in
lemma noFourCycle_interedges_card_le_pow_transpose
    (r : α → β → Prop) {A : Finset α} {B : Finset β} {β' γ : Nat} :
  NoFourCycle r →
  A.card ≤ 2 ^ β' →
  B.card ≤ 2 ^ γ →
  (Rel.interedges r A B).card ≤
    2 ^ (β' + 1) +
      2 ^ (γ + (β' + 1) / 2 + 1) := by
  intro hfour hA hB
  let rt : β → α → Prop := fun b a => r a b
  have hfourT : NoFourCycle rt := by
    intro b₁ b₂ a₁ a₂ h₁₁ h₁₂ h₂₁ h₂₂
    exact (hfour h₁₁ h₂₁ h₁₂ h₂₂).symm
  have hbound := noFourCycle_interedges_card_le_pow rt
    (A := B) (B := A) hfourT hB hA
  have hcard : (Rel.interedges r A B).card =
      (Rel.interedges rt B A).card := by
    apply Finset.card_bij (fun e _ => e.swap)
    · intro e he
      rw [Rel.mem_interedges_iff] at he ⊢
      exact ⟨he.2.1, he.1, he.2.2⟩
    · intro e₁ he₁ e₂ he₂ heq
      exact Prod.swap_injective heq
    · intro e he
      refine ⟨e.swap, ?_, by simp⟩
      rw [Rel.mem_interedges_iff] at he ⊢
      exact ⟨he.2.1, he.1, he.2.2⟩
  rwa [hcard]

open Classical in
lemma noFourCycle_rectangleFamilyEdges_card_le_pow_of_noFourCycle
    (r : α → β → Prop) {𝓡 : Finset (CombinatorialRectangle α β)}
    {α' β' γ : Nat} :
  NoFourCycle r →
  𝓡.card ≤ 2 ^ α' →
  (∀ R ∈ 𝓡,
    R.1.card ≤ 2 ^ β' ∧ R.2.card ≤ 2 ^ γ) →
  (rectangleFamilyEdges r 𝓡).card ≤
    2 ^ (α' + γ + 1) +
      2 ^ (α' + β' + (γ + 1) / 2 + 1) := by
  intro hfour hcard hbounds
  let M := 2 ^ (γ + 1) + 2 ^ (β' + (γ + 1) / 2 + 1)
  have heach : ∀ R ∈ 𝓡, (Rel.interedges r R.1 R.2).card ≤ M := by
    intro R hR
    exact noFourCycle_interedges_card_le_pow r hfour
      (hbounds R hR).1 (hbounds R hR).2
  calc
    (rectangleFamilyEdges r 𝓡).card
        ≤ ∑ R ∈ 𝓡, (Rel.interedges r R.1 R.2).card :=
      card_rectangleFamilyEdges_le_sum r 𝓡
    _ ≤ ∑ _R ∈ 𝓡, M := Finset.sum_le_sum fun R hR => heach R hR
    _ = 𝓡.card * M := by simp
    _ ≤ 2 ^ α' * M := Nat.mul_le_mul_right M hcard
    _ = 2 ^ (α' + γ + 1) +
        2 ^ (α' + β' + (γ + 1) / 2 + 1) := by
      dsimp [M]
      rw [mul_add]
      apply congrArg₂ (· + ·)
      · calc
          2 ^ α' * 2 ^ (γ + 1) = 2 ^ (α' + (γ + 1)) :=
            (pow_add 2 α' (γ + 1)).symm
          _ = 2 ^ (α' + γ + 1) := rfl
      · calc
          2 ^ α' * 2 ^ (β' + (γ + 1) / 2 + 1) =
              2 ^ (α' + (β' + (γ + 1) / 2 + 1)) :=
            (pow_add 2 α' (β' + (γ + 1) / 2 + 1)).symm
          _ = 2 ^ (α' + β' + (γ + 1) / 2 + 1) := by
            congr 1
            omega

open Classical in
lemma noFourCycle_rectangleFamilyEdges_card_le_pow
    (r : α → β → Prop) {𝓡 : Finset (CombinatorialRectangle α β)} {α' β' γ : Nat} :
  NoFourCycle r →
  𝓡.card ≤ 2 ^ α' →
  (∀ R ∈ 𝓡,
    R.1.card ≤ 2 ^ β' ∧ R.2.card ≤ 2 ^ γ) →
  (rectangleFamilyEdges r 𝓡).card ≤
    2 ^ (α' + γ + 1) +
      2 ^ (α' + β' + (γ + 1) / 2 + 1) :=
  noFourCycle_rectangleFamilyEdges_card_le_pow_of_noFourCycle r

end Kolmogorov
