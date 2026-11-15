/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Adaptive
import KolmogorovMathlib.RandomStrings.TTMeet2014.OptimalBridge

/-!
# Theorem 4.1 of Cai, Downey, Epstein, Lempp, Miller

* `theorem_4_1`: for a noncomputable `X` there is an optimal prefix machine `U` with `X ≰_tt R_U`.
* `ttMeet_iff_computable`: `X` is tt-reducible to `R_U` for every optimal `U` iff `X` is computable.
* `theorem_4_1_unconditional`: the same for the paper's unconditional universal machines.
* `computablePred_of_forall_polyTime`: the corollary for the adaptive class `P^{R_U}`, by one
  inclusion (Conjecture 1.3 of the paper, in its deterministic form).
* `mem_EXPSPACE_of_forall_polyTime`: with the existing conditional theorem of Allender, Friedman and
  Gasarch, the hypothesis that `X` is decidable can be dropped.

The quantifiers are those of the paper: for each `U` there may be a different reduction.  The proof
fixes a universal `V`, builds three machines from `X` and `V`, and combines three reductions
into one by `posner_combine` before applying `no_common_reduction`.  The effectivity of the
construction enters through `oursB_computable` and `agreedBit_computable` (`Verification.lean`).
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Kolmogorov

/-- The opponent's move on `τ`: `K_V(τ) + 5 < |τ|`. -/
def OppCompresses (V : Map) (τ : BitString) : Prop := (KPPlain V τ).toNat + 5 < τ.length

/-- The opponent's moves are c.e. -/
theorem oppCompresses_re {V : Map} (hV : IsOptimalPrefixConditional V) :
    REPred (OppCompresses V) := by
  have hre := REPred_KPPlain_toNat_le hV
  have hg : Computable fun τ : BitString => (τ, τ.length - 6) :=
    Computable.id.pair (Primrec.nat_sub.to_comp.comp
      (Primrec.list_length.to_comp) (Computable.const 6))
  have h1 : Partrec fun τ : BitString =>
      Part.assert ((KPPlain V τ).toNat ≤ τ.length - 6) fun _ => Part.some () :=
    Partrec.comp hre hg
  have hc : Computable fun τ : BitString => decide (6 ≤ τ.length) :=
    Primrec.nat_le.decide.to_comp.comp (Computable.const 6) Primrec.list_length.to_comp
  have h2 := Partrec.cond hc h1 Partrec.none
  refine h2.dom_re.of_eq fun τ => ?_
  unfold OppCompresses
  by_cases h : 6 ≤ τ.length
  · simp only [h, decide_true, Bool.cond_true]
    constructor
    · rintro ⟨hle, -⟩
      omega
    · intro hlt
      exact ⟨by omega, trivial⟩
  · simp only [h, decide_false, Bool.cond_false]
    exact ⟨fun hd => (hd : False).elim, fun hlt => absurd hlt (by omega)⟩

/-- **The opponent's budget.**  A move on `τ` costs the opponent at least `2 ^ (-(|τ| - 1))`, in the
normalization where the opponent's total measure is `2 ^ (-5)`. -/
theorem oppCompresses_budget {V : Map} (hV : IsOptimalPrefixConditional V) (S : Finset BitString)
    (hS : ∀ τ ∈ S, OppCompresses V τ) : trueCost S ≤ 1 / 32 := by
  have hkraft := KPPlain_toNat_kraft hV S
  have hterm : ∀ τ ∈ S, ((realCost τ : ℚ) : ℝ) ≤ (1 / 32) * (2 : ℝ)⁻¹ ^ (KPPlain V τ).toNat := by
    intro τ hτ
    have hlt := hS τ hτ
    unfold OppCompresses at hlt
    -- `KPPlain` is reducible in the library (`KP V τ []`); fix the atom so that `norm_num` does not
    -- unfold it in the goal but not in the hypotheses.
    generalize (KPPlain V τ).toNat = k at hlt ⊢
    have hk : τ.length = k + 6 + (τ.length - (k + 6)) := by omega
    unfold realCost
    push_cast
    rw [hk, pow_add, pow_add, inv_pow]
    have h1 : (0 : ℝ) < 2 ^ k := by positivity
    have h2 : (1 : ℝ) ≤ 2 ^ (τ.length - (k + 6)) := one_le_pow₀ (by norm_num)
    rw [div_eq_mul_inv, mul_inv, mul_inv]
    have h3 : ((2 : ℝ) ^ (τ.length - (k + 6)))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
    have h4 : (0 : ℝ) < ((2 : ℝ) ^ k)⁻¹ := by positivity
    norm_num
    nlinarith
  have hsum : ((trueCost S : ℚ) : ℝ) ≤ 1 / 32 := by
    have : ((trueCost S : ℚ) : ℝ) = ∑ τ ∈ S, ((realCost τ : ℚ) : ℝ) := by
      simp [trueCost]
    rw [this]
    calc ∑ τ ∈ S, ((realCost τ : ℚ) : ℝ)
        ≤ ∑ τ ∈ S, (1 / 32) * (2 : ℝ)⁻¹ ^ (KPPlain V τ).toNat := Finset.sum_le_sum hterm
      _ = (1 / 32) * ∑ τ ∈ S, (2 : ℝ)⁻¹ ^ (KPPlain V τ).toNat := by rw [Finset.mul_sum]
      _ ≤ 1 / 32 := by linarith
  have : ((trueCost S : ℚ) : ℝ) ≤ ((1 / 32 : ℚ) : ℝ) := by
    calc ((trueCost S : ℚ) : ℝ) ≤ 1 / 32 := hsum
      _ = ((1 / 32 : ℚ) : ℝ) := by norm_num
  exact Rat.cast_le.1 this

/-- **Exact realisation of a board.**  The machine from `min (K_V + 5, F + 3)` has exactly the final
oracle of the board as its random strings.  So the opponent's moves and ours are the only
compressions: no unintended game moves occur. -/
theorem exists_machine_of_board {V : Map} (hV : IsOptimalPrefixConditional V) {I : Input}
    (hI : I.Valid) (hopp : ∀ τ, (∃ s, I.opp s τ = true) ↔ OppCompresses V τ) (j : Fin 3) :
    ∃ U : Map, IsOptimalPrefixConditional U ∧ prefixRandom U = finalR I j := by
  have hF : IsEntropyFun (realizingF I j) := ⟨realizingF_kraft hI j, realizingF_re hI j⟩
  obtain ⟨U, hU, hmin⟩ := exists_isOptimalPrefixConditional_min_toNat hV hF
  refine ⟨U, hU, ?_⟩
  ext x
  have hexact : x ∈ prefixRandom U ↔ x.length ≤ (KPPlain U x).toNat := by
    change (x.length : ℕ∞) ≤ KPPlain U x ↔ _
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (KPPlain_ne_top_of_isOptimalPrefixConditional hU x)
    rw [← hk, ENat.toNat_natCast, Nat.cast_le]
  rw [hexact, hmin, le_min_iff, length_le_realizingF_iff]
  refine and_congr_left fun _ => ?_
  have h1 := hopp x
  unfold OppCompresses at h1
  constructor
  · intro hle s
    by_contra hne
    have hs : I.opp s x = true := by simpa using hne
    have := h1.1 ⟨s, hs⟩
    omega
  · intro hall
    by_contra hlt
    obtain ⟨s, hs⟩ := h1.2 (by omega)
    have := hall s
    simp [hs] at this

/-- If `X` is tt-reducible to some `R_U`, then `X` has a computable approximation. -/
theorem exists_approx_of_tt {X : Set BitString} {U : Map} (hU : IsOptimalPrefixConditional U)
    (h : TTReducible X (prefixRandom U)) :
    ∃ Xs : ℕ → BitString → Bool, (Computable fun p : ℕ × BitString => Xs p.1 p.2) ∧
      ∀ x, ∃ s₀, ∀ s ≥ s₀, (Xs s x = true ↔ x ∈ X) := by
  obtain ⟨g, hg, hgX⟩ := h
  have hco : REPred fun z : BitString => z ∉ prefixRandom U := by
    have hre := REPred_KPPlain_toNat_le hU
    have hgc : Computable fun τ : BitString => (τ, τ.length - 1) :=
      Computable.id.pair (Primrec.nat_sub.to_comp.comp
        (Primrec.list_length.to_comp) (Computable.const 1))
    have h1 : Partrec fun τ : BitString =>
        Part.assert ((KPPlain U τ).toNat ≤ τ.length - 1) fun _ => Part.some () :=
      Partrec.comp hre hgc
    have hc : Computable fun τ : BitString => decide (1 ≤ τ.length) :=
      Primrec.nat_le.decide.to_comp.comp (Computable.const 1) Primrec.list_length.to_comp
    have h2 := Partrec.cond hc h1 Partrec.none
    refine h2.dom_re.of_eq fun z => ?_
    have hnot : z ∉ prefixRandom U ↔ (KPPlain U z).toNat < z.length := by
      change ¬ ((z.length : ℕ∞) ≤ KPPlain U z) ↔ _
      obtain ⟨k, hk⟩ :=
        ENat.ne_top_iff_exists.1 (KPPlain_ne_top_of_isOptimalPrefixConditional hU z)
      rw [← hk, ENat.toNat_natCast, Nat.cast_le]
      omega
    rw [hnot]
    by_cases hz : 1 ≤ z.length
    · simp only [hz, decide_true, Bool.cond_true]
      constructor
      · rintro ⟨hle, -⟩
        omega
      · intro hlt
        exact ⟨by omega, trivial⟩
    · simp only [hz, decide_false, Bool.cond_false]
      exact ⟨fun hd => (hd : False).elim, fun hlt => absurd hlt (by omega)⟩
  obtain ⟨f, hf, hmono, hspec⟩ := exists_mono_stage hco
  obtain ⟨hcomp, hlim⟩ := approximation_of_tt (R := prefixRandom U) ⟨hf, hmono, hspec⟩ hg hgX
  exact ⟨fun s x => (g x).evalB fun z => !(f s z), hcomp, hlim⟩

/-- **Three machines.**  For a noncomputable `X` that is tt-reducible to `R_V`, there are three
optimal machines that have no common reduction of `X`. -/
theorem exists_three_machines {X : Set BitString} (hX : ¬ ComputablePred fun x => x ∈ X)
    {V : Map} (hV : IsOptimalPrefixConditional V) (hXV : TTReducible X (prefixRandom V)) :
    ∃ U : Fin 3 → Map, (∀ j, IsOptimalPrefixConditional (U j)) ∧
      ¬ ∃ g : BitString → TTable, Computable g ∧ ∀ j, IsTTReduction g X (prefixRandom (U j)) := by
  classical
  obtain ⟨Xs, hXs, hlim⟩ := exists_approx_of_tt hV hXV
  obtain ⟨opp, hopp, hmono, hspec⟩ := exists_mono_stage (oppCompresses_re hV)
  let I : Input := ⟨opp, Xs⟩
  have hI : I.Valid :=
    { opp_computable := hopp.to_comp
      X_computable := hXs
      opp_mono := hmono
      opp_budget := fun S hS =>
        oppCompresses_budget hV S fun τ hτ => (hspec τ).2 (hS τ hτ) }
  have hmachines : ∀ j, ∃ U : Map, IsOptimalPrefixConditional U ∧ prefixRandom U = finalR I j :=
    fun j => exists_machine_of_board hV hI (fun τ => (hspec τ).symm) j
  choose U hU hUR using hmachines
  refine ⟨U, hU, ?_⟩
  rintro ⟨g, hg, hgj⟩
  refine no_common_reduction hI hlim hX ⟨g, hg, fun j => ?_⟩
  rw [← hUR j]
  exact hgj j

/-- **Theorem 4.1.**  Given a noncomputable set `X`, there is an optimal prefix machine `U` such
that `X` is not truth-table reducible to `R_U`. -/
theorem theorem_4_1 (X : Set BitString) (hX : ¬ ComputablePred fun x => x ∈ X) :
    ∃ U : Map, IsOptimalPrefixConditional U ∧ ¬ TTReducible X (prefixRandom U) := by
  classical
  by_contra hcon
  have hall : ∀ U : Map, IsOptimalPrefixConditional U → TTReducible X (prefixRandom U) := by
    intro U hU
    by_contra hno
    exact hcon ⟨U, hU, hno⟩
  obtain ⟨V, hV⟩ := exists_isOptimalPrefixConditional
  obtain ⟨U, hU, hno⟩ := exists_three_machines hX hV (hall V hV)
  -- Per-oracle reductions, possibly different, combine into one by Posner's trick.
  have hred : ∀ j, ∃ g : BitString → TTable,
      Computable g ∧ IsTTReduction g X (prefixRandom (U j)) :=
    fun j => hall (U j) (hU j)
  choose g hg hgX using hred
  exact hno (posner_combine hg hgX)

/-- **Main statement.**  `X` is truth-table reducible to `R_U` for every optimal prefix machine `U`
iff `X` is computable.  The reduction may depend on `U`. -/
theorem ttMeet_iff_computable (X : Set BitString) :
    (∀ U : Map, IsOptimalPrefixConditional U → TTReducible X (prefixRandom U)) ↔
      ComputablePred fun x => x ∈ X := by
  constructor
  · intro h
    by_contra hX
    obtain ⟨U, hU, hno⟩ := theorem_4_1 X hX
    exact hno (h U hU)
  · exact fun h U _ => ttReducible_of_computablePred h _

/-- **Theorem 4.1 for the paper's unconditional universal machines.** -/
theorem theorem_4_1_unconditional (X : Set BitString) (hX : ¬ ComputablePred fun x => x ∈ X) :
    ∃ U : Machine, IsUniversalMachine U ∧ ¬ TTReducible X (randomOf U) := by
  obtain ⟨U, hU, hno⟩ := theorem_4_1 X hX
  exact ⟨restrictEmpty U, restrictEmpty_universal hU, by rwa [randomOf_restrictEmpty]⟩

/-- **The corollary for the adaptive class** `P^{R_U}`, by the inclusion in tt.  There is no
converse here: not every computable set is claimed to be in `⋂_U P^{R_U}`. -/
theorem computablePred_of_forall_polyTime (X : Set BitString)
    (h : ∀ U : Map, IsOptimalPrefixConditional U → X ∈ PolyTimeOracle (prefixRandom U)) :
    ComputablePred fun x => x ∈ X :=
  (ttMeet_iff_computable X).1 fun U hU => ttReducible_of_polyTimeOracle (h U hU)

/-- **With the theorem of Allender, Friedman and Gasarch**, decidability can be dropped from the
hypothesis of the existing `dec_inter_polyTime_prefixRandom_subset_EXPSPACE`. -/
theorem mem_EXPSPACE_of_forall_polyTime (X : Set BitString)
    (h : ∀ U : Map, IsOptimalPrefixConditional U → X ∈ PolyTimeOracle (prefixRandom U)) :
    X ∈ EXPSPACE :=
  dec_inter_polyTime_prefixRandom_subset_EXPSPACE X (computablePred_of_forall_polyTime X h) h

end Kolmogorov.RandomStrings.TTMeet
