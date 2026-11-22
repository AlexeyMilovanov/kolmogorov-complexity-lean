/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.CommonInformation.MutualInformationBounds

/-!
# Finite Iteration

This module proves a finite-iteration result for relativized common information. Its main theorem
uses a stage dichotomy to obtain a common string with controlled complexity from a sequence of
oracle replacements whose extracted information and threshold satisfy explicit bounds.
-/

namespace Kolmogorov.Relativization
open Filter Asymptotics

private structure theorem2_finite_iteration_State where
  oracle : BitString
  extracted : ℕ
  threshold : ℕ
  size : ℕ

private def theorem2_finite_iteration_StateValid
    (D : Map) (c B : ℕ) (x₁ x₂ : BitString) (q t M δ i : ℕ)
    (S : theorem2_finite_iteration_State) : Prop :=
  S.size = natK D (pairCode (pairCode x₁ x₂) S.oracle) ∧
  MutualInfoLe D (pairCode x₁ x₂) S.oracle S.threshold ∧
  CommonInfoExtractableRel D x₁ x₂ S.oracle S.extracted S.threshold ∧
  q + i * (δ / 2) ≤ S.extracted ∧
  S.threshold ≤ 3 ^ i * (t + logSlack B M) ∧
  logSlack (max c 1) S.size ≤ logSlack B M

private structure theorem2_finite_iteration_Prefix
    (D : Map) (c B : ℕ) (x₁ x₂ z : BitString) (q t M δ n : ℕ) where
  state : ℕ → theorem2_finite_iteration_State
  initial : state 0 = ⟨z, q, t, M⟩
  valid : ∀ i, i ≤ n →
    theorem2_finite_iteration_StateValid
      D c B x₁ x₂ q t M δ i (state i)
  stageReady : ∀ i, i < n →
    (state i).threshold ≤ (state i).size ∧
      8 * ((state i).threshold + logSlack 1 (state i).size) ≤ δ
  replacement : ∀ i, i < n →
    2 * (state i).extracted + δ ≤ 2 * (state (i + 1)).extracted ∧
    (state (i + 1)).threshold =
      3 * (state i).threshold + logSlack c (state i).size ∧
    (state (i + 1)).size ≤
      4 * (state i).size + logSlack c (state i).size

/- Iteration of the stage dichotomy records each oracle, extracted amount, threshold, and tuple
complexity. It ends with a successful stage, an oversized threshold, or a complete sequence of
replacements. -/
/-- From a valid prefix, apply the stage dichotomy at its last state. A successful stage or an
oversized threshold gives a terminal result; otherwise a replacement extends the prefix while
preserving the size and threshold estimates needed at later rounds. -/
private theorem theorem2_extend_prefix
    (D : Map) (c B : ℕ)
    (hStage : ∀ (x₁ x₂ z : BitString) (q t δ M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M → 8 * (t + logSlack 1 M) ≤ δ →
      (∃ w : BitString,
        q ≤ natK D w + 2 * δ + logSlack c M ∧
        natCondK D w x₁ ≤ 3 * δ + logSlack c M ∧
        natCondK D w x₂ ≤ 3 * δ + logSlack c M ∧
        natK D w ≤ c * (M + 1)) ∨
      (∃ (z' : BitString) (q' : ℕ),
        2 * q + δ ≤ 2 * q' ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (3 * t + logSlack c M) ∧
        CommonInfoExtractableRel D x₁ x₂ z' q' (3 * t + logSlack c M) ∧
        natK D (pairCode (pairCode x₁ x₂) z') ≤ 4 * M + logSlack c M))
    (x₁ x₂ z : BitString) (q t M δ s n : ℕ)
    (hB : 4 * max c 1 ≤ B)
    (hM : M = natK D (pairCode (pairCode x₁ x₂) z))
    (hs : s ≤ (Nat.bits M).length) (hDelta : δ ≤ M)
    (hGrowth : 8 * 3 ^ s * (t + logSlack B M) ≤ δ)
    (P : theorem2_finite_iteration_Prefix
      D c B x₁ x₂ z q t M δ n)
    (hn : n < s)
    (hSize : ∀ i, i ≤ n →
      (P.state i).size ≤ 5 ^ i * M)
    (hThreshold : ∀ i, i ≤ n →
      (P.state i).threshold ≤ 3 ^ i * t +
        (3 ^ i - 1) * logSlack B M) :
    (∃ w : BitString,
      (P.state n).extracted ≤ natK D w + 2 * δ +
        logSlack c (P.state n).size ∧
      natCondK D w x₁ ≤ 3 * δ + logSlack c (P.state n).size ∧
      natCondK D w x₂ ≤ 3 * δ + logSlack c (P.state n).size ∧
      natK D w ≤ c * ((P.state n).size + 1)) ∨
    (P.state n).threshold > (P.state n).size ∨
    ∃ P' : theorem2_finite_iteration_Prefix
      D c B x₁ x₂ z q t M δ (n + 1),
      (∀ i, i ≤ n + 1 → (P'.state i).size ≤ 5 ^ i * M) ∧
    (∀ i, i ≤ n + 1 →
        (P'.state i).threshold ≤ 3 ^ i * t +
          (3 ^ i - 1) * logSlack B M) := by
  let L := logSlack B M
  let S := P.state n
  have hvalid := P.valid n (Nat.le_refl n)
  rcases hvalid with ⟨hSsize, hSMI, hSExtract, hSprogress, hSThreshold, hSlog⟩
  have hLleM : L ≤ M := by
    have hPowPos : 0 < 3 ^ s := by positivity
    have hCoeff : 1 ≤ 8 * 3 ^ s := by omega
    have hCoeff' : t + L ≤ 8 * 3 ^ s * (t + L) := by
      have h := Nat.mul_le_mul_right (t + L) hCoeff
      simpa using h
    have h := hCoeff'.trans hGrowth
    omega
  have hlogC : logSlack c S.size ≤ L := by
    exact (logSlack_mono_left (Nat.le_max_left c 1) S.size).trans hSlog
  have hlog1 : logSlack 1 S.size ≤ L := by
    exact (logSlack_mono_left (by omega : 1 ≤ max c 1) S.size).trans hSlog
  have htnOuter : S.threshold ≤ 3 ^ n * t + (3 ^ n - 1) * L := hThreshold n (Nat.le_refl n)
  have htnCoarse : S.threshold ≤ 3 ^ n * (t + L) := by
    calc
      S.threshold ≤ 3 ^ n * t + (3 ^ n - 1) * L := htnOuter
      _ ≤ 3 ^ n * (t + L) := by
        rw [Nat.mul_add]
        have hmul := Nat.mul_le_mul_right L (Nat.sub_le (3 ^ n) 1)
        omega
  have hReadySum : S.threshold + logSlack 1 S.size ≤ 3 ^ n * (t + L) := by
    have hPowPos : 0 < 3 ^ n := by positivity
    have hpow : 1 ≤ 3 ^ n := by omega
    calc
      S.threshold + logSlack 1 S.size ≤
          3 ^ n * t + (3 ^ n - 1) * L + L := Nat.add_le_add htnOuter hlog1
      _ = 3 ^ n * t + ((3 ^ n - 1) * L + 1 * L) := by simp [Nat.add_assoc]
      _ = 3 ^ n * t + ((3 ^ n - 1 + 1) * L) := by rw [← Nat.add_mul]
      _ = 3 ^ n * t + 3 ^ n * L := by rw [Nat.sub_add_cancel hpow]
      _ = 3 ^ n * (t + L) := by rw [Nat.mul_add]
  have hpow3 : 3 ^ n ≤ 3 ^ s := by
    exact Nat.pow_le_pow_right (by omega) hn.le
  have hReady : 8 * (S.threshold + logSlack 1 S.size) ≤ δ := by
    calc
      8 * (S.threshold + logSlack 1 S.size) ≤ 8 * (3 ^ n * (t + L)) :=
        Nat.mul_le_mul_left 8 hReadySum
      _ ≤ 8 * 3 ^ s * (t + L) := by
        calc
          8 * (3 ^ n * (t + L)) = (8 * 3 ^ n) * (t + L) := by ring
          _ ≤ (8 * 3 ^ s) * (t + L) :=
            Nat.mul_le_mul_right (t + L) (Nat.mul_le_mul_left 8 hpow3)
          _ = 8 * 3 ^ s * (t + L) := by ring
      _ ≤ δ := hGrowth
  by_cases hOvershoot : S.threshold > S.size
  · exact Or.inr (Or.inl hOvershoot)
  · have hSthreshold : S.threshold ≤ S.size := Nat.le_of_not_gt hOvershoot
    rcases hStage x₁ x₂ S.oracle S.extracted S.threshold δ S.size hSsize hSMI
        hSExtract hSthreshold hReady with hSuccess | hReplace
    · exact Or.inl hSuccess
    · rcases hReplace with ⟨z', q', hGain, hMI', hExtract', hSize'⟩
      let T : theorem2_finite_iteration_State :=
        ⟨z', q', 3 * S.threshold + logSlack c S.size,
          natK D (pairCode (pairCode x₁ x₂) z')⟩
      have hTsize : T.size ≤ 5 ^ (n + 1) * M := by
        calc
          T.size ≤ 4 * S.size + logSlack c S.size := hSize'
          _ ≤ 4 * (5 ^ n * M) + L := by
            exact Nat.add_le_add
              (Nat.mul_le_mul_left 4 (hSize n (Nat.le_refl n))) hlogC
          _ ≤ 4 * (5 ^ n * M) + 5 ^ n * M := by
            have hPowPos : 0 < 5 ^ n := by positivity
            have hpow : 1 ≤ 5 ^ n := by omega
            have h : M ≤ 5 ^ n * M := by
              simpa using Nat.mul_le_mul_right M hpow
            exact Nat.add_le_add_left (hLleM.trans h) (4 * (5 ^ n * M))
          _ = 5 ^ (n + 1) * M := by rw [pow_succ]; ring
      have hTthresholdOuter :
          T.threshold ≤ 3 ^ (n + 1) * t + (3 ^ (n + 1) - 1) * L := by
        have hPowPos : 0 < 3 ^ n := by positivity
        have hpow : 1 ≤ 3 ^ n := by omega
        have hpowSub : 3 ^ n * 3 - 1 = 3 * (3 ^ n - 1) + 2 := by omega
        calc
          T.threshold ≤ 3 * (3 ^ n * t + (3 ^ n - 1) * L) + L := by
            dsimp [T]
            exact Nat.add_le_add (Nat.mul_le_mul_left 3 htnOuter) hlogC
          _ ≤ 3 ^ (n + 1) * t + (3 ^ (n + 1) - 1) * L := by
            rw [pow_succ]
            nlinarith [hpowSub, Nat.zero_le t, Nat.zero_le L]
      have hTthresholdCoarse : T.threshold ≤ 3 ^ (n + 1) * (t + L) := by
        calc
          T.threshold ≤ 3 ^ (n + 1) * t + (3 ^ (n + 1) - 1) * L := hTthresholdOuter
          _ ≤ 3 ^ (n + 1) * (t + L) := by
            rw [Nat.mul_add]
            have hmul := Nat.mul_le_mul_right L (Nat.sub_le (3 ^ (n + 1)) 1)
            omega
      have hHalf : 2 * (δ / 2) ≤ δ := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self δ 2
      have hOneGain : S.extracted + δ / 2 ≤ q' := by omega
      have hRoundGain : q + (n + 1) * (δ / 2) ≤ q' := by
        have hmul : (n + 1) * (δ / 2) = n * (δ / 2) + δ / 2 := by
          rw [Nat.add_mul]
          simp
        calc
          q + (n + 1) * (δ / 2) = q + (n * (δ / 2) + δ / 2) := by rw [hmul]
          _ = (q + n * (δ / 2)) + δ / 2 := by omega
          _ ≤ S.extracted + δ / 2 := Nat.add_le_add_right hSprogress _
          _ ≤ q' := hOneGain
      have hlenM : M < 2 ^ (Nat.bits M).length := by
        rw [Nat.size_eq_bits_len]
        exact Nat.lt_size_self M
      have hpow58 : ∀ k : ℕ, 5 ^ k ≤ 8 ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ, pow_succ]
          exact Nat.mul_le_mul ih (by omega)
      have h8pow : 8 ^ (n + 1) = 2 ^ (3 * (n + 1)) := by
        calc
          8 ^ (n + 1) = (2 ^ 3) ^ (n + 1) := by norm_num
          _ = 2 ^ (3 * (n + 1)) := by rw [← pow_mul]
      have hlenT : (Nat.bits T.size).length ≤
          (Nat.bits M).length + 3 * (n + 1) := by
        have hlt : T.size <
            2 ^ ((Nat.bits M).length + 3 * (n + 1)) := by
          calc
            T.size ≤ 5 ^ (n + 1) * M := hTsize
            _ ≤ 2 ^ (3 * (n + 1)) * M := by
              rw [← h8pow]
              exact Nat.mul_le_mul_right M (hpow58 (n + 1))
            _ < 2 ^ (3 * (n + 1)) * 2 ^ (Nat.bits M).length := by
              gcongr
            _ = 2 ^ ((Nat.bits M).length + 3 * (n + 1)) := by
              rw [← pow_add]
              congr 1
              omega
        rw [Nat.size_eq_bits_len]
        exact Nat.size_le.mpr hlt
      have hklen : n + 1 ≤ (Nat.bits M).length := by omega
      have hlenT' : (Nat.bits T.size).length ≤ 4 * (Nat.bits M).length := by omega
      have hSlackT : logSlack (max c 1) T.size ≤ L := by
        change max c 1 * (Nat.bits T.size).length + max c 1 ≤
          B * (Nat.bits M).length + B
        have hcoeff : (4 * max c 1) * (Nat.bits M).length ≤
            B * (Nat.bits M).length := Nat.mul_le_mul_right _ hB
        have hmax : max c 1 ≤ B := by omega
        calc
          max c 1 * (Nat.bits T.size).length + max c 1 ≤
              max c 1 * (4 * (Nat.bits M).length) + max c 1 := by
            exact Nat.add_le_add_right
              (Nat.mul_le_mul_left _ hlenT') _
          _ = (4 * max c 1) * (Nat.bits M).length + max c 1 := by ring
          _ ≤ B * (Nat.bits M).length + B := by omega
      let P' : theorem2_finite_iteration_Prefix
          D c B x₁ x₂ z q t M δ (n + 1) :=
        { state := fun i => if i = n + 1 then T else P.state i
          initial := by
            simpa using P.initial
          valid := by
            intro i hi
            by_cases hiOld : i ≤ n
            · have hiNe : i ≠ n + 1 := by omega
              simpa [hiNe] using P.valid i hiOld
            · have hiEq : i = n + 1 := by omega
              subst i
              simpa using
                (show theorem2_finite_iteration_StateValid
                  D c B x₁ x₂ q t M δ (n + 1) T from
                  ⟨rfl, hMI', hExtract', hRoundGain, hTthresholdCoarse, hSlackT⟩)
          stageReady := by
            intro i hi
            by_cases hiOld : i < n
            · have hiNe : i ≠ n + 1 := by omega
              simpa [hiNe] using P.stageReady i hiOld
            · have hiEq : i = n := by omega
              subst i
              have hNe : n ≠ n + 1 := by omega
              simpa [hNe] using (show (P.state n).threshold ≤ (P.state n).size ∧
                8 * ((P.state n).threshold + logSlack 1 (P.state n).size) ≤ δ from
                ⟨hSthreshold, hReady⟩)
          replacement := by
            intro i hi
            by_cases hiOld : i < n
            · have hiNe : i ≠ n + 1 := by omega
              have hiNeAt : i ≠ n := by omega
              simpa [hiNe, hiNeAt] using P.replacement i hiOld
            · have hiEq : i = n := by omega
              subst i
              have hNe : n ≠ n + 1 := by omega
              simpa [hNe] using
                (show 2 * (P.state n).extracted + δ ≤ 2 * T.extracted ∧
                    T.threshold = 3 * (P.state n).threshold + logSlack c (P.state n).size ∧
                    T.size ≤ 4 * (P.state n).size + logSlack c (P.state n).size from
                  ⟨hGain, rfl, hSize'⟩) }
      refine Or.inr (Or.inr ⟨P', ?_, ?_⟩)
      · intro i hi
        by_cases hiOld : i ≤ n
        · have hiNe : i ≠ n + 1 := by omega
          simpa [P', hiNe] using hSize i hiOld
        · have hiEq : i = n + 1 := by omega
          subst i
          simpa [P'] using hTsize
      · intro i hi
        by_cases hiOld : i ≤ n
        · have hiNe : i ≠ n + 1 := by omega
          simpa [P', hiNe] using hThreshold i hiOld
        · have hiEq : i = n + 1 := by omega
          subst i
          simpa [P'] using hTthresholdOuter

/-- Iterating the stage dichotomy records the oracle, extracted amount, threshold, and tuple
complexity at every round. The result is a first-branch stage, a round where the threshold exceeds
the current tuple complexity, or a complete sequence of replacements. -/
private theorem theorem2_iterate_stages
    (D : Map) (c : ℕ)
    (hStage : ∀ (x₁ x₂ z : BitString) (q t δ M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M → 8 * (t + logSlack 1 M) ≤ δ →
      (∃ w : BitString,
        q ≤ natK D w + 2 * δ + logSlack c M ∧
        natCondK D w x₁ ≤ 3 * δ + logSlack c M ∧
        natCondK D w x₂ ≤ 3 * δ + logSlack c M ∧
        natK D w ≤ c * (M + 1)) ∨
      (∃ (z' : BitString) (q' : ℕ),
        2 * q + δ ≤ 2 * q' ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (3 * t + logSlack c M) ∧
        CommonInfoExtractableRel D x₁ x₂ z' q' (3 * t + logSlack c M) ∧
        natK D (pairCode (pairCode x₁ x₂) z') ≤ 4 * M + logSlack c M)) :
    ∃ B : ℕ, max c 1 ≤ B ∧ ∀ (x₁ x₂ z : BitString) (q t M δ s : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M → 2 ≤ M → s ≤ (Nat.bits M).length → δ ≤ M →
      8 * 3 ^ s * (t + logSlack B M) ≤ δ →
      (∃ n : ℕ, n ≤ s ∧
        ∃ P : theorem2_finite_iteration_Prefix
          D c B x₁ x₂ z q t M δ n,
          (n < s ∧
            ∃ w : BitString,
              (P.state n).extracted ≤ natK D w + 2 * δ +
                logSlack c (P.state n).size ∧
              natCondK D w x₁ ≤ 3 * δ + logSlack c (P.state n).size ∧
              natCondK D w x₂ ≤ 3 * δ + logSlack c (P.state n).size ∧
              natK D w ≤ c * ((P.state n).size + 1)) ∨
          (P.state n).threshold > (P.state n).size) ∨
      (∃ _P : theorem2_finite_iteration_Prefix
        D c B x₁ x₂ z q t M δ s, True) := by
  let C := max c 1
  let B := 4 * C
  have hBfour : 4 * max c 1 ≤ B := by rfl
  have hBc : max c 1 ≤ B := by dsimp [B]; omega
  refine ⟨B, hBc, ?_⟩
  intro x₁ x₂ z q t M δ s hM hMI hExtract ht hTwo hs hDelta hGrowth
  let L := logSlack B M
  let P₀ : theorem2_finite_iteration_Prefix
      D c B x₁ x₂ z q t M δ 0 :=
    { state := fun _ => ⟨z, q, t, M⟩
      initial := rfl
      valid := by
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        change M = natK D (pairCode (pairCode x₁ x₂) z) ∧
          MutualInfoLe D (pairCode x₁ x₂) z t ∧
          CommonInfoExtractableRel D x₁ x₂ z q t ∧
          q + 0 * (δ / 2) ≤ q ∧
          t ≤ 3 ^ 0 * (t + logSlack B M) ∧
          logSlack (max c 1) M ≤ logSlack B M
        refine ⟨hM, hMI, hExtract, by omega, by simp,
          logSlack_mono_left hBc M⟩
      stageReady := by intro i hi; omega
      replacement := by intro i hi; omega }
  have hIter : ∀ k, k ≤ s →
      ((∃ n, n ≤ s ∧
        ∃ P : theorem2_finite_iteration_Prefix
          D c B x₁ x₂ z q t M δ n,
          (n < s ∧
            ∃ w : BitString,
              (P.state n).extracted ≤ natK D w + 2 * δ +
                logSlack c (P.state n).size ∧
              natCondK D w x₁ ≤ 3 * δ + logSlack c (P.state n).size ∧
              natCondK D w x₂ ≤ 3 * δ + logSlack c (P.state n).size ∧
              natK D w ≤ c * ((P.state n).size + 1)) ∨
          (P.state n).threshold > (P.state n).size)) ∨
      (∃ P : theorem2_finite_iteration_Prefix
        D c B x₁ x₂ z q t M δ k,
        (∀ i, i ≤ k → (P.state i).size ≤ 5 ^ i * M) ∧
        (∀ i, i ≤ k →
          (P.state i).threshold ≤ 3 ^ i * t + (3 ^ i - 1) * L)) := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact Or.inr ⟨P₀, by
          intro i hi
          have : i = 0 := by omega
          subst i
          simp [P₀], by
          intro i hi
          have : i = 0 := by omega
          subst i
          simp [P₀, L]⟩
    | succ k ih =>
        intro hk
        rcases ih (by omega) with hTerminal | ⟨P, hSize, hThreshold⟩
        · exact Or.inl hTerminal
        · have hklt : k < s := by omega
          have hRound :=
            theorem2_extend_prefix
              D c B hStage x₁ x₂ z q t M δ s k hBfour hM hs hDelta hGrowth
              P hklt hSize hThreshold
          rcases hRound with hSuccess | hRound
          · exact Or.inl ⟨k, by omega, P, Or.inl ⟨hklt, hSuccess⟩⟩
          · rcases hRound with hOvershoot | ⟨P', hSize', hThreshold'⟩
            · exact Or.inl ⟨k, by omega, P, Or.inr hOvershoot⟩
            · exact Or.inr ⟨P', hSize', hThreshold'⟩
  rcases hIter s (Nat.le_refl s) with hTerminal | ⟨P, hSize, hThreshold⟩
  · exact Or.inl hTerminal
  · exact Or.inr ⟨P, True.intro⟩

/-- The conditional mutual-information inequality rules out a complete sequence of oracle
replacements when the extracted amount increases by the stipulated amount at each round. -/
private theorem theorem2_rule_out_replacements
    (D : Map) (hD : isOptimalConditional D) (c B : ℕ) :
    ∃ A : ℕ, ∀ (x₁ x₂ z : BitString) (q t M δ s : ℕ)
      (_P : theorem2_finite_iteration_Prefix
        D c B x₁ x₂ z q t M δ s),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      2 ≤ M → s ≤ (Nat.bits M).length → δ ≤ M →
      logSlack A M ≤ M →
      8 * M + 2 * logSlack A M ≤ s * (δ / 2) →
      8 * 3 ^ s * (t + logSlack B M) ≤ δ → False := by
  obtain ⟨cProj, hProj⟩ := pairPlainK_left_le D hD
  obtain ⟨cCtx, hCtx⟩ := condK_le_condK_pair_add_two_plainK D hD
  let A := 4 * cProj + cCtx + 1
  refine ⟨A, ?_⟩
  intro x₁ x₂ z q t M δ s P hM hTwo hs hDelta hLogA hProgress hGrowth
  let S := P.state s
  have hvalid := P.valid s (Nat.le_refl s)
  rcases hvalid with ⟨_, _, hExtract, hExtractProgress, hThreshold, _⟩
  rcases hExtract with ⟨v, hExtractV, hV₁, _⟩
  have hV₁' : natCondK D v (pairCode x₁ S.oracle) ≤ S.threshold := by
    simpa [S] using hV₁
  have hThreshold8 : 8 * S.threshold ≤ M := by
    calc
      8 * S.threshold ≤ 8 * (3 ^ s * (t + logSlack B M)) :=
        Nat.mul_le_mul_left 8 hThreshold
      _ = 8 * 3 ^ s * (t + logSlack B M) := by ring
      _ ≤ δ := hGrowth
      _ ≤ M := hDelta
  have hx₁Tuple : natK D x₁ ≤ natK D (pairCode x₁ x₂) + cProj := by
    have hh := hProj x₁ x₂
    change plainK D x₁ ≤ plainK D (pairCode x₁ x₂) + (cProj : ℕ∞) at hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD x₁,
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂)] at hh
    exact_mod_cast hh
  have hTupleM : natK D (pairCode x₁ x₂) ≤ M + cProj := by
    have hh := hProj (pairCode x₁ x₂) z
    change plainK D (pairCode x₁ x₂) ≤
      plainK D (pairCode (pairCode x₁ x₂) z) + (cProj : ℕ∞) at hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂),
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode (pairCode x₁ x₂) z)] at hh
    have hNat : natK D (pairCode x₁ x₂) ≤
        natK D (pairCode (pairCode x₁ x₂) z) + cProj := by
      exact_mod_cast hh
    simpa [hM] using hNat
  have hx₁M : natK D x₁ ≤ M + 2 * cProj := by omega
  have hContext : natCondK D v S.oracle ≤
      natCondK D v (pairCode x₁ S.oracle) + (2 * natK D x₁ + cCtx) := by
    have hh := hCtx v x₁ S.oracle
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD v S.oracle),
      ← ENat.natCast_toNat
        (condK_ne_top_of_optimal D hD v (pairCode x₁ S.oracle))] at hh
    have hcv : cVal D x₁ = natK D x₁ := rfl
    rw [hcv] at hh
    change (condK D v S.oracle).toNat ≤
      (condK D v (pairCode x₁ S.oracle)).toNat + (2 * natK D x₁ + cCtx)
    exact_mod_cast hh
  have hExtractUpper : S.extracted ≤ 3 * M + 4 * cProj + cCtx := by
    have hThresholdM : S.threshold ≤ M := by omega
    calc
      S.extracted ≤ natCondK D v S.oracle := hExtractV
      _ ≤ natCondK D v (pairCode x₁ S.oracle) + (2 * natK D x₁ + cCtx) := hContext
      _ ≤ S.threshold + (2 * natK D x₁ + cCtx) :=
        Nat.add_le_add_right hV₁' _
      _ ≤ 3 * M + 4 * cProj + cCtx := by omega
  have hExtractLower : 8 * M + 2 * A ≤ S.extracted := by
    have hAlog : A ≤ logSlack A M := by
      unfold logSlack
      exact Nat.le_add_left _ _
    have hProgress' : 8 * M + 2 * logSlack A M ≤ S.extracted := by
      calc
        8 * M + 2 * logSlack A M ≤ s * (δ / 2) := hProgress
        _ ≤ q + s * (δ / 2) := by exact Nat.le_add_left _ _
        _ ≤ S.extracted := hExtractProgress
    omega
  dsimp [A] at hExtractLower
  omega

/-- At a first-branch stage, transfer its bounds to the original threshold and use pair coding to
obtain a witness whose plain complexity is linear in the original tuple complexity. -/
private theorem theorem2_finish_successful_stage
    (D : Map) (hD : isOptimalConditional D) (c B : ℕ) :
    ∃ A C : ℕ, B ≤ A ∧ ∀ (x₁ x₂ z : BitString) (q t M δ s n : ℕ)
      (P : theorem2_finite_iteration_Prefix
        D c B x₁ x₂ z q t M δ n) (w : BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      n < s → B ≤ A → logSlack A M ≤ M → δ ≤ M →
      (P.state n).extracted ≤ natK D w + 2 * δ +
        logSlack c (P.state n).size →
      natCondK D w x₁ ≤ 3 * δ + logSlack c (P.state n).size →
      natCondK D w x₂ ≤ 3 * δ + logSlack c (P.state n).size →
      q ≤ natK D w + 4 * δ + logSlack A M ∧
      natCondK D w x₁ ≤ 4 * δ + logSlack A M ∧
      natCondK D w x₂ ≤ 4 * δ + logSlack A M ∧
      natK D w ≤ C * (M + 1) := by
  obtain ⟨cLeft, hLeft⟩ := pairPlainK_left_le D hD
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le D hD
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log_add_condK D hD
  let A := max B 4
  let C := 7 + 2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight
  refine ⟨A, C, Nat.le_max_left _ _, ?_⟩
  intro x₁ x₂ z q t M δ s n P w hM hn hBA hLog hDelta hqStage hx₁Stage hx₂Stage
  have hvalid := P.valid n (Nat.le_refl n)
  rcases hvalid with ⟨_, _, _, hProgress, _, hLogCurrent⟩
  have hq : q ≤ (P.state n).extracted := by omega
  have hStageLog : logSlack c (P.state n).size ≤ logSlack A M := by
    calc
      logSlack c (P.state n).size ≤ logSlack (max c 1) (P.state n).size :=
        logSlack_mono_left (Nat.le_max_left c 1) _
      _ ≤ logSlack B M := hLogCurrent
      _ ≤ logSlack A M := logSlack_mono_left hBA M
  have hX12 : natK D x₁ ≤ natK D (pairCode x₁ x₂) + cLeft := by
    have hh := hLeft x₁ x₂
    change plainK D x₁ ≤ plainK D (pairCode x₁ x₂) + (cLeft : ℕ∞) at hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD x₁,
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂)] at hh
    have hNat : natK D x₁ ≤ natK D (pairCode x₁ x₂) + cLeft := by
      exact_mod_cast hh
    exact hNat
  have hPairM : natK D (pairCode x₁ x₂) ≤ M + cLeft := by
    have hh := hLeft (pairCode x₁ x₂) z
    change plainK D (pairCode x₁ x₂) ≤
      plainK D (pairCode (pairCode x₁ x₂) z) + (cLeft : ℕ∞) at hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂),
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode (pairCode x₁ x₂) z)] at hh
    have hNat : natK D (pairCode x₁ x₂) ≤
        natK D (pairCode (pairCode x₁ x₂) z) + cLeft := by
      exact_mod_cast hh
    simpa [hM] using hNat
  have hX₁ : natK D x₁ ≤ M + 2 * cLeft := by omega
  have hWPair : natK D w ≤ natK D (pairCode x₁ w) + cRight := by
    have hh := hRight x₁ w
    change plainK D w ≤ plainK D (pairCode x₁ w) + (cRight : ℕ∞) at hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD w,
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ w)] at hh
    have hNat : natK D w ≤ natK D (pairCode x₁ w) + cRight := by
      exact_mod_cast hh
    exact hNat
  have hCode : natK D (pairCode x₁ w) ≤
      natK D x₁ + natCondK D w x₁ + 2 * Nat.log 2 (natK D x₁) + cPair := by
    have hh := hPair x₁ w
    change plainK D (pairCode x₁ w) ≤ plainK D x₁ + condK D w x₁ +
      ((2 * Nat.log 2 (cVal D x₁) + cPair : ℕ) : ℕ∞) at hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ w),
      commonInfo_le_mutualInfo_hasPlainValue D hD x₁,
      commonInfo_le_mutualInfo_hasCondValue D hD w x₁] at hh
    have hcv : cVal D x₁ = natK D x₁ := rfl
    rw [hcv] at hh
    have hNat : natK D (pairCode x₁ w) ≤
        natK D x₁ + natCondK D w x₁ + (2 * Nat.log 2 (natK D x₁) + cPair) := by
      exact_mod_cast hh
    omega
  have hLogX₁ : Nat.log 2 (natK D x₁) ≤
      (Nat.bits M).length + 2 * (Nat.bits cLeft).length + 2 := by
    calc
      Nat.log 2 (natK D x₁) ≤ Nat.log 2 (M + 2 * cLeft) :=
        Nat.log_mono_right hX₁
      _ ≤ (Nat.bits (M + 2 * cLeft)).length :=
        commonInfo_le_mutualInfo_natLog_le_bits _
      _ ≤ (Nat.bits M).length + (Nat.bits (2 * cLeft)).length + 1 :=
        length_natBits_add_le M (2 * cLeft)
      _ ≤ (Nat.bits M).length + 2 * (Nat.bits cLeft).length + 2 := by
        have hbits := length_natBits_add_le cLeft cLeft
        have hbits' : (Nat.bits (2 * cLeft)).length ≤
            2 * (Nat.bits cLeft).length + 1 := by
          simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbits
        omega
  have hCondW : natCondK D w x₁ ≤ 3 * δ + logSlack c (P.state n).size := hx₁Stage
  have hW : natK D w ≤ 7 * M +
      (2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight) := by
    calc
      natK D w ≤ natK D (pairCode x₁ w) + cRight := hWPair
      _ ≤ natK D x₁ + natCondK D w x₁ + 2 * Nat.log 2 (natK D x₁) + cPair + cRight := by omega
      _ ≤ M + 2 * cLeft + 3 * δ + logSlack c (P.state n).size +
            2 * ((Nat.bits M).length + 2 * (Nat.bits cLeft).length + 2) + cPair + cRight := by
        omega
      _ ≤ 7 * M + (2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight) := by
        have hBitsM : (Nat.bits M).length ≤ M := length_natBits_le M
        have hSlack : logSlack c (P.state n).size ≤ M := by
          exact hStageLog.trans hLog
        omega
  have hC : 7 * M +
      (2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight) ≤ C * (M + 1) := by
    dsimp [C]
    have hcoeff : 7 ≤ 7 + 2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight := by
      omega
    have hconst : 2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight ≤
        7 + 2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight := by omega
    calc
      7 * M + (2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight)
          ≤ (7 + 2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight) * M +
              (7 + 2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight) := by
            exact Nat.add_le_add (Nat.mul_le_mul_right M hcoeff) hconst
      _ = (7 + 2 * cLeft + 4 * (Nat.bits cLeft).length + 4 + cPair + cRight) * (M + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
  refine ⟨?_, ?_, ?_, hW.trans hC⟩
  · calc
      q ≤ (P.state n).extracted := hq
      _ ≤ natK D w + 2 * δ + logSlack c (P.state n).size := hqStage
      _ ≤ natK D w + 4 * δ + logSlack A M := by omega
  · calc
      natCondK D w x₁ ≤ 3 * δ + logSlack c (P.state n).size := hx₁Stage
      _ ≤ 4 * δ + logSlack A M := by omega
  · calc
      natCondK D w x₂ ≤ 3 * δ + logSlack c (P.state n).size := hx₂Stage
      _ ≤ 4 * δ + logSlack A M := by omega

/-- When the current threshold exceeds the current tuple complexity, the empty string is a
suitable witness because the extraction and mutual-information bounds control the extracted
amount. -/
private theorem theorem2_finish_overshoot
    (D : Map) (hD : isOptimalConditional D) (c B : ℕ) :
    ∃ A C : ℕ, ∀ (x₁ x₂ z : BitString) (q t M δ s n : ℕ)
      (P : theorem2_finite_iteration_Prefix
        D c B x₁ x₂ z q t M δ n),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      n ≤ s → 2 ≤ M → s ≤ (Nat.bits M).length → δ ≤ M →
      8 * 3 ^ s * (t + logSlack B M) ≤ δ →
      logSlack A M ≤ M →
      (P.state n).threshold > (P.state n).size →
      ∃ w : BitString,
        q ≤ natK D w + 4 * δ + logSlack A M ∧
        natCondK D w x₁ ≤ 4 * δ + logSlack A M ∧
        natCondK D w x₂ ≤ 4 * δ + logSlack A M ∧
        natK D w ≤ C * (M + 1) := by
  obtain ⟨cCtx, hCtx⟩ := condK_le_condK_pair_add_two_plainK D hD
  obtain ⟨cProj, hProj⟩ := pairPlainK_left_le D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  let A := max (4 * cProj + cCtx) (cCond + cLen)
  let C := cCond + cLen
  refine ⟨A, C, ?_⟩
  intro x₁ x₂ z q t M δ s n P hM hn hTwo hs hDelta hGrowth hLog hover
  have hvalid := P.valid n (Nat.le_refl n)
  rcases hvalid with ⟨hSize, _, hExtract, hProgress, hThreshold, _⟩
  rcases hExtract with ⟨v, hqV, hv₁, hv₂⟩
  have hTime : 8 * (P.state n).threshold ≤ δ := by
    have hpow : 3 ^ n ≤ 3 ^ s := Nat.pow_le_pow_right (by omega) hn
    calc
      8 * (P.state n).threshold ≤ 8 * (3 ^ n * (t + logSlack B M)) :=
        Nat.mul_le_mul_left 8 hThreshold
      _ ≤ 8 * (3 ^ s * (t + logSlack B M)) := by
        exact Nat.mul_le_mul_left 8
          (Nat.mul_le_mul_right (t + logSlack B M) hpow)
      _ = 8 * 3 ^ s * (t + logSlack B M) := by ring
      _ ≤ δ := hGrowth
  have hXPair : natK D (pairCode x₁ x₂) ≤
      (P.state n).size + cProj := by
    have hh := hProj (pairCode x₁ x₂) (P.state n).oracle
    change plainK D (pairCode x₁ x₂) ≤
      plainK D (pairCode (pairCode x₁ x₂) (P.state n).oracle) + (cProj : ℕ∞) at hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂),
      commonInfo_le_mutualInfo_hasPlainValue D hD
        (pairCode (pairCode x₁ x₂) (P.state n).oracle)] at hh
    have hNat : natK D (pairCode x₁ x₂) ≤
        natK D (pairCode (pairCode x₁ x₂) (P.state n).oracle) + cProj := by
      exact_mod_cast hh
    simpa [hSize] using hNat
  have hX₁ : natK D x₁ ≤ (P.state n).size + 2 * cProj := by
    have hh := hProj x₁ x₂
    change plainK D x₁ ≤ plainK D (pairCode x₁ x₂) + (cProj : ℕ∞) at hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD x₁,
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂)] at hh
    have hNat : natK D x₁ ≤ natK D (pairCode x₁ x₂) + cProj := by
      exact_mod_cast hh
    omega
  have hX₁' : natK D x₁ ≤ (P.state n).threshold + 2 * cProj := by omega
  have hqBound : q ≤ 3 * (P.state n).threshold + (4 * cProj + cCtx) := by
    have hContext := hCtx v x₁ (P.state n).oracle
    rw [commonInfo_le_mutualInfo_hasCondValue D hD v (P.state n).oracle,
      commonInfo_le_mutualInfo_hasCondValue D hD v (pairCode x₁ (P.state n).oracle)] at hContext
    have hcv : cVal D x₁ = natK D x₁ := rfl
    rw [hcv] at hContext
    have hContextN : natCondK D v (P.state n).oracle ≤
        natCondK D v (pairCode x₁ (P.state n).oracle) +
          (2 * natK D x₁ + cCtx) := by
      exact_mod_cast hContext
    have hqExtracted : q ≤ (P.state n).extracted := by omega
    have hqCurrent : q ≤ natCondK D v (P.state n).oracle := hqExtracted.trans hqV
    have hNat : q ≤ natCondK D v (pairCode x₁ (P.state n).oracle) +
        (2 * natK D x₁ + cCtx) := hqCurrent.trans hContextN
    have hNat' := Nat.add_le_add_right hv₁ (2 * natK D x₁ + cCtx)
    omega
  have hlogLower : 4 * cProj + cCtx ≤ logSlack A M := by
    dsimp [A]
    unfold logSlack
    omega
  have hlogLowerC : C ≤ logSlack A M := by
    dsimp [A, C]
    unfold logSlack
    omega
  have hEmptyK : natK D [] ≤ cLen := by
    have hh := hLen []
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD []] at hh
    exact_mod_cast (by simpa using hh)
  have hEmpty₁ : natCondK D [] x₁ ≤ C := by
    have hh := hCond [] x₁
    rw [commonInfo_le_mutualInfo_hasCondValue D hD [] x₁,
      commonInfo_le_mutualInfo_hasPlainValue D hD []] at hh
    have hNat : natCondK D [] x₁ ≤ natK D [] + cCond := by exact_mod_cast hh
    dsimp [C]
    omega
  have hEmpty₂ : natCondK D [] x₂ ≤ C := by
    have hh := hCond [] x₂
    rw [commonInfo_le_mutualInfo_hasCondValue D hD [] x₂,
      commonInfo_le_mutualInfo_hasPlainValue D hD []] at hh
    have hNat : natCondK D [] x₂ ≤ natK D [] + cCond := by exact_mod_cast hh
    dsimp [C]
    omega
  have hK : natK D [] ≤ C := by dsimp [C]; omega
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · calc
      q ≤ 3 * (P.state n).threshold + (4 * cProj + cCtx) := hqBound
      _ ≤ 4 * δ + logSlack A M := by omega
      _ ≤ natK D [] + 4 * δ + logSlack A M := by omega
  · calc
      natCondK D [] x₁ ≤ C := hEmpty₁
      _ ≤ 4 * δ + logSlack A M := by omega
  · calc
      natCondK D [] x₂ ≤ C := hEmpty₂
      _ ≤ 4 * δ + logSlack A M := by omega
  · calc
      natK D [] ≤ C := hK
      _ ≤ C * (M + 1) := by
        calc
          C = C * 1 := by omega
          _ ≤ C * (M + 1) := Nat.mul_le_mul_left C (by omega)

/-- Under a fixed error budget, the stage dichotomy either supplies a common string or replaces
the oracle and raises the extracted amount. The recurrence bounds force a successful stage in
finitely many rounds, yielding a witness with linear complexity in the original tuple size. -/
theorem theorem2_finite_iteration
    (D : Map) (hD : isOptimalConditional D) (c : ℕ)
    (hStage : ∀ (x₁ x₂ z : BitString) (q t δ M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M → 8 * (t + logSlack 1 M) ≤ δ →
      (∃ w : BitString,
        q ≤ natK D w + 2 * δ + logSlack c M ∧
        natCondK D w x₁ ≤ 3 * δ + logSlack c M ∧
        natCondK D w x₂ ≤ 3 * δ + logSlack c M ∧
        natK D w ≤ c * (M + 1)) ∨
      (∃ (z' : BitString) (q' : ℕ),
        2 * q + δ ≤ 2 * q' ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (3 * t + logSlack c M) ∧
        CommonInfoExtractableRel D x₁ x₂ z' q' (3 * t + logSlack c M) ∧
        natK D (pairCode (pairCode x₁ x₂) z') ≤ 4 * M + logSlack c M)) :
    ∃ A B C : ℕ, ∀ (x₁ x₂ z : BitString) (q t M δ s : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M → 2 ≤ M →
      s ≤ (Nat.bits M).length → δ ≤ M → logSlack A M ≤ M →
      8 * M + 2 * logSlack A M ≤ s * (δ / 2) →
      8 * 3 ^ s * (t + logSlack B M) ≤ δ →
      ∃ w : BitString,
        q ≤ natK D w + 4 * δ + logSlack A M ∧
        natCondK D w x₁ ≤ 4 * δ + logSlack A M ∧
        natCondK D w x₂ ≤ 4 * δ + logSlack A M ∧
        natK D w ≤ C * (M + 1) := by
  obtain ⟨B, hBc, hIterate⟩ :=
    theorem2_iterate_stages D c hStage
  obtain ⟨A₁, hNoRun⟩ :=
    theorem2_rule_out_replacements
      D hD c B
  obtain ⟨A₂, C₂, hBA₂, hFinishStage⟩ :=
    theorem2_finish_successful_stage
      D hD c B
  obtain ⟨A₃, C₃, hFinishOvershoot⟩ :=
    theorem2_finish_overshoot
      D hD c B
  let A := max A₁ (max A₂ (max A₃ B))
  let C := max C₂ C₃
  refine ⟨A, B, C, ?_⟩
  intro x₁ x₂ z q t M δ s hM hMI hExtract ht hTwo hs hDelta hA hProgress hGrowth
  have hA₁ : A₁ ≤ A := by dsimp [A]; omega
  have hA₂ : A₂ ≤ A := by dsimp [A]; omega
  have hA₃ : A₃ ≤ A := by dsimp [A]; omega
  have hB : B ≤ A := by dsimp [A]; omega
  have hLogA₁ : logSlack A₁ M ≤ M := by
    exact (logSlack_mono_left hA₁ M).trans hA
  have hLogA₂ : logSlack A₂ M ≤ M := by
    exact (logSlack_mono_left hA₂ M).trans hA
  have hLogA₃ : logSlack A₃ M ≤ M := by
    exact (logSlack_mono_left hA₃ M).trans hA
  have hIter := hIterate x₁ x₂ z q t M δ s hM hMI hExtract ht hTwo hs hDelta hGrowth
  rcases hIter with ⟨n, hn, P, hTerminal⟩ | ⟨P, _⟩
  · rcases hTerminal with ⟨hnlt, w, hq, hx₁, hx₂, hw⟩ | hover
    · obtain ⟨hq', hx₁', hx₂', hw'⟩ :=
        hFinishStage x₁ x₂ z q t M δ s n P w hM hnlt hBA₂ hLogA₂ hDelta
          hq hx₁ hx₂
      refine ⟨w, ?_, ?_, ?_, ?_⟩
      · calc
          q ≤ natK D w + 4 * δ + logSlack A₂ M := hq'
          _ ≤ natK D w + 4 * δ + logSlack A M :=
            Nat.add_le_add_left (logSlack_mono_left hA₂ M) _
      · calc
          natCondK D w x₁ ≤ 4 * δ + logSlack A₂ M := hx₁'
          _ ≤ 4 * δ + logSlack A M :=
            Nat.add_le_add_left (logSlack_mono_left hA₂ M) _
      · calc
          natCondK D w x₂ ≤ 4 * δ + logSlack A₂ M := hx₂'
          _ ≤ 4 * δ + logSlack A M :=
            Nat.add_le_add_left (logSlack_mono_left hA₂ M) _
      · exact Nat.le_trans hw' (Nat.mul_le_mul_right (M + 1) (by dsimp [C]; omega))
    · obtain ⟨w, hq', hx₁', hx₂', hw'⟩ :=
        hFinishOvershoot x₁ x₂ z q t M δ s n P hM hn hTwo hs hDelta
          hGrowth hLogA₃ hover
      refine ⟨w, ?_, ?_, ?_, ?_⟩
      · calc
          q ≤ natK D w + 4 * δ + logSlack A₃ M := hq'
          _ ≤ natK D w + 4 * δ + logSlack A M :=
            Nat.add_le_add_left (logSlack_mono_left hA₃ M) _
      · calc
          natCondK D w x₁ ≤ 4 * δ + logSlack A₃ M := hx₁'
          _ ≤ 4 * δ + logSlack A M :=
            Nat.add_le_add_left (logSlack_mono_left hA₃ M) _
      · calc
          natCondK D w x₂ ≤ 4 * δ + logSlack A₃ M := hx₂'
          _ ≤ 4 * δ + logSlack A M :=
            Nat.add_le_add_left (logSlack_mono_left hA₃ M) _
      · exact Nat.le_trans hw' (Nat.mul_le_mul_right (M + 1) (by dsimp [C]; omega))
  · have hLogA₁' : logSlack A₁ M ≤ logSlack A M := logSlack_mono_left hA₁ M
    have hProgress₁ : 8 * M + 2 * logSlack A₁ M ≤ s * (δ / 2) := by omega
    exact False.elim (hNoRun x₁ x₂ z q t M δ s P hM hTwo hs hDelta
      hLogA₁ hProgress₁ hGrowth)

end Kolmogorov.Relativization
