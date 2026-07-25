/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.Improving
import KolmogorovMathlib.Restricted.GapCountingIn
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Deficiencies
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems

/-!
# M5: Restricted Deficiency Equivalence
-/

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-
From a *given* family member `A ∋ x` (with `setComplexity ≤ alpha` and randomness
deficiency `≤ beta`), extract a realized optimality gap plus the visible-budget
control, exactly as `exists_realizedGap_uniformSet_of_stochastic` does for level
sets — but here `A` is supplied, so no level-set construction is needed.
-/
theorem restricted_exists_realizedGap_of_member (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n alpha beta : ℕ),
      x.length = n →
      setComplexity U A hA ≤ (alpha : ENat) →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x beta →
      ∃ (delta i j kx d : ℕ),
        RealizedSetOptimalityGap U A hA x delta i j kx ∧
        CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d ∧
        d ≤ delta + c ∧
        (i : ℕ) ≤ alpha + logSlack c (n + alpha + beta) ∧
        d ≤ beta + logSlack c (n + alpha + beta) ∧
        n + delta + d ≤ 4 * (n + alpha + beta) + c := by
  use (KPPlain_toNat_le_setComplexity_add_condKP U hU).choose + (KP_le_KPPlain U hU).choose + (KPPlain_le_length_add_log U hU).choose + 100;
  intro A hA x n alpha beta hn hcompA hdefA
  obtain ⟨i, hi⟩ : ∃ i : ℕ, setComplexity U A hA = (i : ENat) ∧ i ≤ alpha := by
    cases h : setComplexity U A hA <;> aesop
  obtain ⟨j, hj_lower, hj_upper⟩ : ∃ j : ℕ, (2 : ℝ≥0∞) ^ j / 2 ≤ (A.card : ℝ≥0∞) ∧ A.card ≤ 2 ^ j := by
    convert exists_card_dyadic_bracket A hA using 1
  set kx := (KPPlain U x).toNat
  have hkx_eq : (kx : ENat) = KPPlain U x := by
    exact ENat.coe_toNat ( KPPlain_ne_top_of_optimal U hU x )
  set delta := i + j - kx
  have h_realized : RealizedSetOptimalityGap U A hA x delta i j kx := by
    have h_mass_pos : (codedUniformOn A hA).mass x > 0 := by
      apply mass_pos_of_deficiencyLe_of_KP_ne_top hdefA (KP_ne_top_of_optimal U hU x (codedUniformOn A hA).code);
    exact ⟨ by contrapose! h_mass_pos; rw [ codedUniformOn_mass_of_not_mem ] ; aesop, hi.1, hj_upper, hj_lower, hkx_eq, rfl ⟩
  have h_def_soi : CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x (delta + (KPPlain_toNat_le_setComplexity_add_condKP U hU).choose) := by
    have := Exists.choose_spec (KPPlain_toNat_le_setComplexity_add_condKP U hU) A hA x (by
    exact h_realized.1)
    generalize_proofs at *;
    unfold CodedFiniteDistribution.DeficiencyLe;
    rw [ codedUniformOn_mass_of_mem A hA x h_realized.1 ];
    rw [ ← ENat.coe_toNat (KP_ne_top_of_optimal U hU x (codedUniformOn A hA).code) ];
    refine le_trans ?_ ( mul_le_mul_right ( show ( A.card : ENNReal ) ⁻¹ ≥ ( 2 ^ j : ENNReal ) ⁻¹ from ?_ ) _ );
    · rw [ show delta = i + j - kx from rfl, show kx = ( KPPlain U x ).toNat from rfl ] at * ; norm_cast at * ; simp_all +decide ;
      rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
      · field_simp;
        rw [ div_pow, div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast <;> norm_num [ pow_add, pow_mul ];
        rw [ ← pow_add, ← pow_add ];
        exact pow_le_pow_right₀ ( by decide ) ( by omega );
      · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
    · gcongr ; norm_cast
  set d := min beta (delta + (KPPlain_toNat_le_setComplexity_add_condKP U hU).choose)
  have h_def_d : CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d := by
    grind;
  have h_j_bound : j ≤ (KP U x (codedUniformOn A hA).code).toNat + beta + 1 := by
    obtain ⟨j', hj'_card, hj'_le⟩ : ∃ j' : ℕ, A.card ≤ 2 ^ j' ∧ (j' : ENat) ≤ KP U x (codedUniformOn A hA).code + beta := by
      apply card_le_of_deficiency h_realized.left hdefA;
    have h_bound_j : j - 1 ≤ j' := by
      have h_bound_j : (2 : ℝ≥0∞) ^ j / 2 ≤ (2 : ℝ≥0∞) ^ j' := by
        exact le_trans hj_lower ( mod_cast hj'_card );
      convert dyadic_bracket_lower_bound h_bound_j using 1;
    cases h : KP U x ( codedUniformOn A hA ).code <;> simp_all +decide;
    · exact absurd h ( KP_ne_top_of_optimal U hU x _ );
    · norm_cast at * ; linarith;
  have h_kc_bound : (KP U x (codedUniformOn A hA).code).toNat ≤ n + 2 * (Nat.bits n).length + (KPPlain_le_length_add_log U hU).choose + (KP_le_KPPlain U hU).choose := by
    have hKP_le : KP U x (codedUniformOn A hA).code ≤ KPPlain U x + ((KP_le_KPPlain U hU).choose : ENat) := by
      grind
    have hKPP_le : KPPlain U x ≤ (n : ENat) + 2 * (Nat.bits n).length + ((KPPlain_le_length_add_log U hU).choose : ENat) := by
      grind +splitIndPred
    have hle : KP U x (codedUniformOn A hA).code ≤
        ((n + 2 * (Nat.bits n).length + (KPPlain_le_length_add_log U hU).choose
          + (KP_le_KPPlain U hU).choose : ℕ) : ENat) := by
      refine le_trans hKP_le ?_
      have hstep : KPPlain U x + ((KP_le_KPPlain U hU).choose : ENat) ≤
          ((n : ENat) + 2 * (Nat.bits n).length + ((KPPlain_le_length_add_log U hU).choose : ENat))
            + ((KP_le_KPPlain U hU).choose : ENat) := by gcongr
      refine le_trans hstep (le_of_eq ?_)
      push_cast; ring
    calc (KP U x (codedUniformOn A hA).code).toNat
        ≤ (((n + 2 * (Nat.bits n).length + (KPPlain_le_length_add_log U hU).choose
            + (KP_le_KPPlain U hU).choose : ℕ) : ENat)).toNat :=
          ENat.toNat_le_toNat hle (ENat.coe_ne_top _)
      _ = _ := ENat.toNat_coe _
  have h_bits_length : (Nat.bits n).length ≤ n := length_natBits_le_self n
  refine ⟨ delta, i, j, kx, d, h_realized, h_def_d, ?_, ?_, ?_, ?_ ⟩ <;> omega

noncomputable def descriptionsWithComplexityLeAndSizeLeMem
    (mem : Finset BitString → Prop) (U : Map) (i j : ℕ) : Finset (Finset BitString) := by
  classical
  exact (descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => mem S)

noncomputable def ManyIJDescriptionsMem
    (mem : Finset BitString → Prop) (U : Map) (x : BitString) (i j k : ℕ) : Prop :=
  2 ^ k ≤ ((descriptionsWithComplexityLeAndSizeLeMem mem U i j).filter
    (fun S => x ∈ S)).card

/-- Every set in the size/complexity-bounded description universe is nonempty. -/
theorem nonempty_of_mem_descriptionsWithComplexityLeAndSizeLe {U : Map} {i j : ℕ}
    {S : Finset BitString} (hS : S ∈ descriptionsWithComplexityLeAndSizeLe U i j) :
    S.Nonempty := by
  unfold descriptionsWithComplexityLeAndSizeLe at hS
  exact nonempty_of_mem_descriptionsWithComplexityLe (Finset.mem_filter.mp hS).1

/-- A `PreDescriptionFamily` (VS40 condition (1) only) built from an arbitrary
computable staged enumeration for a fixed program `p`.  Membership is the given
`mem` intersected with nonemptiness so that `nonempty_of_mem` holds. -/
noncomputable def uniformPreFamily (p : BitString) (mem : Finset BitString → Prop)
    (enum : BitString → ℕ → List BitString)
    (henum : Computable (fun p_t : BitString × ℕ => enum p_t.1 p_t.2))
    (hmono : ∀ t, enum p t <+: enum p (t + 1))
    (hsound : ∀ t, ∀ w ∈ enum p t, ∃ (S : Finset BitString) (hS : S.Nonempty),
      mem S ∧ w = (codedUniformOn S hS).code)
    (hcomplete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S →
      ∃ t, (codedUniformOn S hS).code ∈ enum p t) :
    PreDescriptionFamily where
  mem := fun S => mem S ∧ S.Nonempty
  nonempty_of_mem := fun h => h.2
  enumeration :=
    { enum := enum p
      computable := henum.comp (Computable.pair (Computable.const p) Computable.id)
      mono := hmono
      sound := fun t w hw => by
        obtain ⟨S, hS, hmemS, hwcode⟩ := hsound t w hw
        exact ⟨S, hS, ⟨hmemS, hS⟩, hwcode⟩
      complete := fun S hS h => hcomplete S hS h.1 }

/-- The membership predicate of `uniformPreFamily` agrees with `mem` on the
nonempty description universe, so the two multiplicity finsets coincide. -/
theorem descriptionsWithComplexityLeAndSizeLeMem_eq_in
    (p : BitString) (mem : Finset BitString → Prop) (enum : BitString → ℕ → List BitString)
    (henum : Computable (fun p_t : BitString × ℕ => enum p_t.1 p_t.2))
    (hmono : ∀ t, enum p t <+: enum p (t + 1))
    (hsound : ∀ t, ∀ w ∈ enum p t, ∃ (S : Finset BitString) (hS : S.Nonempty),
      mem S ∧ w = (codedUniformOn S hS).code)
    (hcomplete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S →
      ∃ t, (codedUniformOn S hS).code ∈ enum p t)
    (U : Map) (i j : ℕ) :
    descriptionsWithComplexityLeAndSizeLeMem mem U i j
      = descriptionsWithComplexityLeAndSizeLeIn
          (uniformPreFamily p mem enum henum hmono hsound hcomplete) U i j := by
  classical
  unfold descriptionsWithComplexityLeAndSizeLeMem descriptionsWithComplexityLeAndSizeLeIn
  refine Finset.filter_congr ?_
  intro S hS
  have hne : S.Nonempty := nonempty_of_mem_descriptionsWithComplexityLeAndSizeLe hS
  simp only [uniformPreFamily, hne, and_true]

/-- `ManyIJDescriptionsMem` for `mem` equals `ManyIJDescriptionsIn` for the
induced `uniformPreFamily`. -/
theorem manyIJDescriptionsMem_iff_in
    (p : BitString) (mem : Finset BitString → Prop) (enum : BitString → ℕ → List BitString)
    (henum : Computable (fun p_t : BitString × ℕ => enum p_t.1 p_t.2))
    (hmono : ∀ t, enum p t <+: enum p (t + 1))
    (hsound : ∀ t, ∀ w ∈ enum p t, ∃ (S : Finset BitString) (hS : S.Nonempty),
      mem S ∧ w = (codedUniformOn S hS).code)
    (hcomplete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S →
      ∃ t, (codedUniformOn S hS).code ∈ enum p t)
    (U : Map) (x : BitString) (i j k : ℕ) :
    ManyIJDescriptionsMem mem U x i j k ↔
      ManyIJDescriptionsIn
        (uniformPreFamily p mem enum henum hmono hsound hcomplete) U x i j k := by
  unfold ManyIJDescriptionsMem ManyIJDescriptionsIn
  rw [descriptionsWithComplexityLeAndSizeLeMem_eq_in p mem enum henum hmono hsound hcomplete U i j]

/-- A fixed universal programmed enumerator using `Code.evaln`.
  `p` is interpreted as a program that outputs the enumeration at stage `t`. -/
def programmedEnum (p : BitString) (t : ℕ) : List BitString :=
  let c := (Encodable.decode (α := Code) (Encodable.encode p)).getD Code.zero
  match Code.evaln t c (Encodable.encode t) with
  | some r => (Encodable.decode r).getD []
  | none => []

theorem programmedEnum_computable : Computable (fun p_t : BitString × ℕ => programmedEnum p_t.1 p_t.2) := by
  unfold programmedEnum
  have h_eval : Computable (fun p_t : BitString × ℕ =>
      Code.evaln p_t.2
        ((Encodable.decode (α := Code) (Encodable.encode p_t.1)).getD Code.zero)
        (Encodable.encode p_t.2)) := by
    let evalInput : BitString × ℕ → (ℕ × Code) × ℕ := fun p_t =>
      ((p_t.2,
        (Encodable.decode (α := Code) (Encodable.encode p_t.1)).getD Code.zero),
        Encodable.encode p_t.2)
    have h_evalInput : Computable evalInput := by
      dsimp [evalInput]
      exact Computable.pair
        (Computable.pair
          (Computable.snd : Computable (fun p_t : BitString × ℕ => p_t.2))
          (Computable.option_getD
            ((Computable.decode (α := Code)).comp
              ((Computable.encode (α := BitString)).comp
                (Computable.fst : Computable (fun p_t : BitString × ℕ => p_t.1))))
            (Computable.const Code.zero)))
        ((Computable.encode (α := ℕ)).comp
          (Computable.snd : Computable (fun p_t : BitString × ℕ => p_t.2)))
    change Computable (fun p_t : BitString × ℕ =>
      Nat.Partrec.Code.evaln (evalInput p_t).1.1 (evalInput p_t).1.2 (evalInput p_t).2)
    exact Nat.Partrec.Code.primrec_evaln.to_comp.comp h_evalInput
  have h_none : Computable (fun _p_t : BitString × ℕ => ([] : List BitString)) :=
    Computable.const []
  have h_getD : Computable (fun r : ℕ =>
      (Encodable.decode r : Option (List BitString)).getD []) :=
    Computable.option_getD
      (Computable.decode (α := List BitString))
      (Computable.const [])
  have h_some : Computable₂ (fun (_p_t : BitString × ℕ) (r : ℕ) =>
      (Encodable.decode r : Option (List BitString)).getD []) :=
    (h_getD.comp
      (Computable.snd : Computable (fun p_r : (BitString × ℕ) × ℕ => p_r.2))).to₂
  convert Computable.option_casesOn h_eval h_none h_some using 1
  funext p_t
  cases h : Code.evaln p_t.2
      ((Encodable.decode (α := Code) (Encodable.encode p_t.1)).getD Code.zero)
      (Encodable.encode p_t.2) <;> simp
  all_goals simp at h
  all_goals simp [h]

-- `programmedEnum` is now sealed: its computability is captured once in
-- `programmedEnum_computable`.  Keeping it reducible makes later `Computable.comp`
-- unifications unfold the `Code.evaln` body and blow up `whnf`; sealing it keeps
-- those elaborations fast while the structural (projection-level) `rfl`s below
-- still go through.
attribute [irreducible] programmedEnum

structure IsProgramForFamily (p : BitString) (mem : Finset BitString → Prop) : Prop where
  mono : ∀ t, programmedEnum p t <+: programmedEnum p (t + 1)
  sound : ∀ t, ∀ w ∈ programmedEnum p t, ∃ (S : Finset BitString) (hS : S.Nonempty), mem S ∧ w = (codedUniformOn S hS).code
  complete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S → ∃ t, (codedUniformOn S hS).code ∈ programmedEnum p t

noncomputable def programmedFamily (p : BitString) (mem : Finset BitString → Prop) (hp : IsProgramForFamily p mem) : PreDescriptionFamily :=
  uniformPreFamily p mem programmedEnum programmedEnum_computable hp.mono hp.sound hp.complete

/-!
### Universal (program-indexed) index selector

To prove the *uniform* description-count leaf — where the slack constant `c` is
chosen **before** the family program `p`, and the extra cost is paid by
`KPPlain U p` — we need a single partial-recursive index selector that reads the
family program `p` from part of its input.  The standard family selector
`familyIndexSelectorFn c 𝒜` fixes the family `𝒜` first, so its
`KP_partrec_cond_first_map_le` constant depends on `p`.  Here we build
`univSelectorFn c`, a program-indexed version whose value on input `pairCode p w`
agrees with `familyIndexSelectorFn c (programmedFamily p mem hp)` on `w`, and
which is jointly partial recursive in `(p, w)` because `programmedEnum` is jointly
computable.  Feeding the input `pairCode p w` then charges `KPPair U p w ≤
KPPlain U p + KPPlain U w + O(1)`, i.e. exactly the extra `KPPlain U p` term.
-/

/-- Program-indexed candidate codes: the candidate slice at stage `t` filtered by
appearance in `programmedEnum p`.  Definitionally equal to
`familyCandidateCodes c i (programmedFamily p mem hp) j x t`. -/
def progCandidateCodes (c : Code) (i : ℕ) (p : BitString) (j : ℕ) (x : BitString) (t : ℕ) :
    List BitString :=
  (candidateCodes c i j x t).filter (fun w => decide (w ∈ programmedEnum p t))

/-- Program-indexed online appearance enumeration, using `programmedEnum p`. -/
def progAppearanceListCodes (c : Code) (i : ℕ) (p : BitString) (j : ℕ) (x : BitString) :
    ℕ → List BitString
  | 0 => (progCandidateCodes c i p j x 0).eraseDups
  | t + 1 =>
      (progAppearanceListCodes c i p j x t ++ progCandidateCodes c i p j x (t + 1)).eraseDups

/-- The program-indexed appearance list equals the family appearance list of the
induced `programmedFamily`, for any membership predicate and witness. -/
theorem progAppearanceListCodes_eq_family (c : Code) (i : ℕ) (p : BitString)
    (mem : Finset BitString → Prop) (hp : IsProgramForFamily p mem) (j : ℕ) (x : BitString) :
    progAppearanceListCodes c i p j x = familyAppearanceListCodes c i (programmedFamily p mem hp) j x := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => simp only [progAppearanceListCodes, familyAppearanceListCodes, ih]; rfl

/-- Program-indexed index selector, using `progAppearanceListCodes`. -/
def progIndexSelectorFn (c : Code) (p : BitString) : BitString → BitString →. BitString := fun y w =>
  let x := decodeFirst y
  let i := selNat w
  let j := selAlpha w
  let h := selH w
  (Nat.rfind (fun t => Part.some (decide (h < (progAppearanceListCodes c i p j x t).length)))).bind
    (fun t => Part.some (match (progAppearanceListCodes c i p j x t).drop h with
      | [] => []
      | a :: _ => a))

/-- The program-indexed selector agrees with the family selector of the induced
`programmedFamily`. -/
theorem progIndexSelectorFn_eq_family (c : Code) (p : BitString)
    (mem : Finset BitString → Prop) (hp : IsProgramForFamily p mem) (y w : BitString) :
    progIndexSelectorFn c p y w = familyIndexSelectorFn c (programmedFamily p mem hp) y w := by
  simp only [progIndexSelectorFn, familyIndexSelectorFn,
    progAppearanceListCodes_eq_family c (selNat w) p mem hp (selAlpha w) (decodeFirst y)]
  rfl

/-- The universal selector: reads the family program `p` from the first component
of its input and the rich selector word `w` from the second. -/
def univSelectorFn (c : Code) : BitString → BitString →. BitString := fun y s =>
  progIndexSelectorFn c (decodeFirst s) y (decodeSecond s)

-- We use `.of_eq` so unification never eagerly unfolds `candidateCodes`/`programmedEnum`.
/-- Joint computability of the program-indexed candidate slice. -/
theorem progCandidateCodes_computable (c : Code) :
    Computable (fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ =>
      progCandidateCodes c q.1.1.1.1 q.1.2 q.1.1.1.2 q.1.1.2 q.2) := by
  have h_filter : Computable (fun p : List BitString × List BitString => p.1.filter (fun w => decide (w ∈ p.2))) :=
    (list_filter_primrec (f := fun (p : List BitString × List BitString) => p.1) (p := fun p w => decide (w ∈ p.2)) Primrec.fst (bitString_mem_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to_comp
  have hcand : Computable (fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ =>
      candidateCodes c q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.2) :=
    ((candidateCodes_primrec c).to_comp.comp (Computable.pair (Computable.pair (Computable.pair (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))) (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))) (Computable.snd.comp (Computable.fst.comp Computable.fst))) Computable.snd)).of_eq (by intro _; rfl)
  have henum : Computable (fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ =>
      programmedEnum q.1.2 q.2) :=
    (programmedEnum_computable.comp (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)).of_eq (by intro _; rfl)
  exact (h_filter.comp (Computable.pair hcand henum)).of_eq (by intro _; rfl)

/-- Joint computability of the program-indexed appearance list. -/
theorem progAppearanceListCodes_computable (c : Code) :
    Computable (fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ =>
      progAppearanceListCodes c q.1.1.1.1 q.1.2 q.1.1.1.2 q.1.1.2 q.2) := by
  have h_eraseDups : Computable (fun l : List BitString => l.eraseDups) :=
    eraseDups_bitstring_primrec.to_comp
  have hg : Computable (fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ =>
      (progCandidateCodes c q.1.1.1.1 q.1.2 q.1.1.1.2 q.1.1.2 0).eraseDups) :=
    (h_eraseDups.comp ((progCandidateCodes_computable c).comp
      (Computable.pair Computable.fst (Computable.const 0)))).of_eq (by intro _; rfl)
  have hh : Computable₂ (fun (q : (((ℕ × ℕ) × BitString) × BitString) × ℕ) (r : ℕ × List BitString) =>
      (r.2 ++ progCandidateCodes c q.1.1.1.1 q.1.2 q.1.1.1.2 q.1.1.2 (r.1 + 1)).eraseDups) :=
    (h_eraseDups.comp (Computable.list_append.comp
      (Computable.snd.comp Computable.snd)
      ((progCandidateCodes_computable c).comp
        (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.succ.comp (Computable.fst.comp Computable.snd)))))).of_eq (by intro _; rfl)
  refine (Computable.nat_rec (f := fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ => q.2)
    Computable.snd hg hh).of_eq ?_
  intro q
  obtain ⟨qs, t⟩ := q
  change Nat.rec _ _ _ = progAppearanceListCodes c qs.1.1.1 qs.2 qs.1.1.2 qs.1.2 t
  induction t with
  | zero => rfl
  | succ t ih => simp only [progAppearanceListCodes]; rw [← ih]

/-- The universal selector is jointly partial recursive. -/
theorem partrec_univSelectorFn (c : Code) :
    Partrec (fun q : BitString × BitString => univSelectorFn c q.2 q.1) := by
  unfold univSelectorFn progIndexSelectorFn;
  refine Partrec.bind ?_ ?_;
  · refine Partrec.of_eq
      (f := fun n : BitString × BitString => Nat.rfind fun t => Part.some
        (decide (selH (decodeSecond n.1) <
          (progAppearanceListCodes c (selNat (decodeSecond n.1))
            (decodeFirst n.1) (selAlpha (decodeSecond n.1))
            (decodeFirst n.2) t).length))) ?_ (by intro _; rfl);
    · refine Partrec.rfind ?_;
      refine Computable.of_eq
        (f := fun n : (BitString × BitString) × ℕ =>
          decide (selH (decodeSecond n.1.1) <
            (progAppearanceListCodes c (selNat (decodeSecond n.1.1))
              (decodeFirst n.1.1) (selAlpha (decodeSecond n.1.1))
              (decodeFirst n.1.2) n.2).length)) ?_ (by intro _; rfl);
      · have h_app : Computable (fun (n : ((BitString × BitString) × ℕ)) => progAppearanceListCodes c (selNat (decodeSecond n.1.1)) (decodeFirst n.1.1) (selAlpha (decodeSecond n.1.1)) (decodeFirst n.1.2) n.2) :=
          ((progAppearanceListCodes_computable c).comp (Computable.pair (Computable.pair (Computable.pair (Computable.pair (selNat_primrec.to_comp.comp (decodeSecond_primrec.to_comp.comp (Computable.fst.comp Computable.fst))) (selAlpha_primrec.to_comp.comp (decodeSecond_primrec.to_comp.comp (Computable.fst.comp Computable.fst)))) (decodeFirst_primrec.to_comp.comp (Computable.snd.comp Computable.fst))) (decodeFirst_primrec.to_comp.comp (Computable.fst.comp Computable.fst))) Computable.snd)).of_eq (by intro _; rfl)
        have h_len : Computable (fun (n : ((BitString × BitString) × ℕ)) => (progAppearanceListCodes c (selNat (decodeSecond n.1.1)) (decodeFirst n.1.1) (selAlpha (decodeSecond n.1.1)) (decodeFirst n.1.2) n.2).length) :=
          Computable.list_length.comp h_app
        have h_sel : Computable (fun (n : ((BitString × BitString) × ℕ)) => selH (decodeSecond n.1.1)) :=
          selH_primrec.to_comp.comp (decodeSecond_primrec.to_comp.comp (Computable.fst.comp Computable.fst))
        exact ((PrimrecPred.decide Primrec.nat_lt).to_comp.comp (Computable.pair h_sel h_len)).of_eq (by intro _; rfl)
  · refine Partrec.comp ?_ ?_;
    · exact Computable.id;
    · refine Computable.of_eq
        (f := fun n : (BitString × BitString) × ℕ =>
          List.headI (List.drop (selH (decodeSecond n.1.1))
            (progAppearanceListCodes c (selNat (decodeSecond n.1.1))
              (decodeFirst n.1.1) (selAlpha (decodeSecond n.1.1))
              (decodeFirst n.1.2) n.2))) ?_ ?_;
      · have h_drop : Computable (fun (n : ℕ × List BitString) => List.drop n.1 n.2) :=
          Primrec.list_drop.to_comp
        have h_head : Computable (fun (l : List BitString) => l.headI) :=
          Primrec.list_headI.to_comp
        convert h_head.comp ( h_drop.comp ( Computable.pair _ _ ) ) using 1;
        · exact selH_primrec.to_comp.comp ( decodeSecond_primrec.to_comp.comp ( Computable.fst.comp ( Computable.fst.comp Computable.id ) ) );
        · exact ((progAppearanceListCodes_computable c).comp (Computable.pair (Computable.pair (Computable.pair (Computable.pair (selNat_primrec.to_comp.comp (decodeSecond_primrec.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.id)))) (selAlpha_primrec.to_comp.comp (decodeSecond_primrec.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.id))))) (decodeFirst_primrec.to_comp.comp (Computable.snd.comp (Computable.fst.comp Computable.id)))) (decodeFirst_primrec.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.id)))) Computable.snd)).of_eq (by intro _; rfl)
      · intro n
        cases h : List.drop (selH (decodeSecond n.1.1))
            (progAppearanceListCodes c (selNat (decodeSecond n.1.1))
              (decodeFirst n.1.1) (selAlpha (decodeSecond n.1.1))
              (decodeFirst n.1.2) n.2) with
        | nil =>
            simp
            rfl
        | cons _ _ => simp

/-- Uniform family rank lemma. -/
theorem uniform_description_count_of_conditional_complexity_gap (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop),
      IsProgramForFamily p mem →
      ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n i j m kx : ℕ),
      x.length = n →
      mem A →
      x ∈ A →
      setComplexity U A hA ≤ (i : ENat) →
      A.card ≤ 2 ^ j →
      HasPrefixComplexityValue U x kx →
      ¬ ManyIJDescriptionsMem mem U x i j m →
      KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤ (m + logSlack c (n + i + j) + KPPlain U p : ENat) := by
  obtain ⟨c_opt, hc_opt⟩ : ∃ c_opt : Code, IsCodeFor c_opt U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c_kp, hkp⟩ := KP_partrec_cond_first_map_le U hU (univSelectorFn c_opt)
    (partrec_univSelectorFn c_opt)
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound 2 3 7
  let C1 := C2 + c_kp + c_plain + c_pair + c_len + 6
  refine ⟨C1, ?_⟩
  intro p mem hp A hA x n i j m kx hn hmem hx hi hj hkx h_not_many
  set 𝒜 := programmedFamily p mem hp with h𝒜
  have hmem𝒜 : 𝒜.mem A := ⟨hmem, hA⟩
  have h_not_in : ¬ ManyIJDescriptionsIn 𝒜 U x i j m := fun h => h_not_many
    ((manyIJDescriptionsMem_iff_in p mem programmedEnum programmedEnum_computable
      hp.mono hp.sound hp.complete U x i j m).mpr h)
  obtain ⟨t₀, ht₀⟩ := code_mem_familyAppearanceListCodes hc_opt 𝒜 A hA x i j hmem𝒜 hx hi hj
  set y := prefixComplexityContext x kx
  set code := (codedUniformOn A hA).code
  have hy : decodeFirst y = x := by
    dsimp [y, prefixComplexityContext]
    rw [decodeFirst_pairCode]
  obtain ⟨r, hr_lt, hr_spec⟩ := familyIndexSelectorFn_eq_code c_opt i 𝒜 j x code t₀ ht₀
  set w := richInput i j 0 r
  have hw_i : selNat w = i := selNat_richInput i j 0 r
  have hw_j : selAlpha w = j := selAlpha_richInput i j 0 r
  have hw_h : selH w = r := selH_richInput i j 0 r
  have h_some : familyIndexSelectorFn c_opt 𝒜 y w = Part.some code := hr_spec y w hy hw_i hw_j hw_h
  have huniv : univSelectorFn c_opt y (pairCode p w) = Part.some code := by
    unfold univSelectorFn
    rw [decodeFirst_pairCode, decodeSecond_pairCode, progIndexSelectorFn_eq_family c_opt p mem hp]
    exact h_some
  have h_in : code ∈ univSelectorFn c_opt y (pairCode p w) := Part.eq_some_iff.mp huniv
  have h_bound1 : KP U code y ≤ KP U (pairCode p w) y + (c_kp : ENat) := hkp (pairCode p w) code y h_in
  have h_bound2 : KP U (pairCode p w) y ≤ KPPlain U (pairCode p w) + (c_plain : ENat) :=
    hc_plain (pairCode p w) y
  have h_bound3 : KPPlain U (pairCode p w) ≤ KPPlain U p + KPPlain U w + (c_pair : ENat) :=
    hc_pair p w
  have h_bound4 : KPPlain U w ≤ (w.length : ENat) + 2 * (Nat.bits w.length).length + c_len := hc_len w
  have h_w_len_r : w.length ≤ 2 * (Nat.bits i).length + 2 * (Nat.bits j).length + (Nat.bits r).length + 6 := by
    unfold w richInput selectorInput pack4
    simp [length_pairCode]
    omega
  have hr_lt_2m : r < 2 ^ m :=
    lt_trans hr_lt (familyAppearanceListCodes_length_lt_of_not_manyIJIn hc_opt h_not_in t₀)
  have hr_lt_2i : r < 2 ^ (i + 1) :=
    lt_of_lt_of_le hr_lt (familyAppearanceListCodes_length_le_two_pow_i hc_opt 𝒜 i j x t₀)
  set M := n + i + j with hM
  have h_w_len_M : w.length ≤ 3 * M + 7 := by
    have hi_len : (Nat.bits i).length ≤ i := length_natBits_le_self i
    have hj_len : (Nat.bits j).length ≤ j := length_natBits_le_self j
    have hr_len : (Nat.bits r).length ≤ i + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr hr_lt_2i
    omega
  have h_r_m : (Nat.bits r).length ≤ m := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hr_lt_2m
  have h_slack : c_kp + c_plain + c_pair + c_len + 2 * (Nat.bits i).length + 2 * (Nat.bits j).length + 6 + 2 * (Nat.bits w.length).length ≤ logSlack C1 M := by
    have hw1 : (Nat.bits w.length).length ≤ (Nat.bits (3 * M + 7)).length := by
      have h : w.length < 2 ^ (Nat.size (3 * M + 7)) := lt_of_le_of_lt h_w_len_M (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hw3 : 2 * (Nat.bits (3 * M + 7)).length ≤ logSlack 2 (3 * M + 7) := by unfold logSlack; omega
    have hw5 : logSlack C2 M = C2 * (Nat.bits M).length + C2 := rfl
    have hw6 : logSlack C1 M = (C2 + c_kp + c_plain + c_pair + c_len + 6) * (Nat.bits M).length + (C2 + c_kp + c_plain + c_pair + c_len + 6) := rfl
    have hiM : i ≤ M := by omega
    have hjM : j ≤ M := by omega
    have hi_len : (Nat.bits i).length ≤ (Nat.bits M).length := by
      have h : i < 2 ^ (Nat.size M) := lt_of_le_of_lt hiM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hj_len : (Nat.bits j).length ≤ (Nat.bits M).length := by
      have h : j < 2 ^ (Nat.size M) := lt_of_le_of_lt hjM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hC2_M := hC2 M
    nlinarith
  have hnat : w.length + 2 * (Nat.bits w.length).length + c_len + (c_pair + c_plain + c_kp)
      ≤ m + logSlack C1 M := by omega
  calc KP U code y ≤ KP U (pairCode p w) y + c_kp := h_bound1
    _ ≤ KPPlain U (pairCode p w) + c_plain + c_kp := by gcongr
    _ ≤ (KPPlain U p + KPPlain U w + c_pair) + c_plain + c_kp := by gcongr
    _ = KPPlain U p + (KPPlain U w + (c_pair + c_plain + c_kp : ℕ)) := by push_cast; ring
    _ ≤ KPPlain U p + (((w.length : ENat) + 2 * (Nat.bits w.length).length + c_len)
          + (c_pair + c_plain + c_kp : ℕ)) := by gcongr
    _ = KPPlain U p + ((w.length + 2 * (Nat.bits w.length).length + c_len + (c_pair + c_plain + c_kp) : ℕ) : ENat) := by
          push_cast; ring
    _ ≤ KPPlain U p + ((m + logSlack C1 M : ℕ) : ENat) := by
          gcongr
    _ = (m + logSlack C1 M + KPPlain U p : ENat) := by push_cast; ring

/-!
### Universal (program-indexed) marked-code selector

The uniform *selected-set* leaf is proved by the same device: a single
partial-recursive marked-code selector that reads the family program `p` from part
of its input, so the `KPPlain_partrec_map_le` constant is uniform in `p`, and the
extra cost is `KPPlain U p` (paid via `pairCode p (familyMarkedInput …)`).
-/

/-- Program-indexed candidate model-code slice, using `programmedEnum p`. -/
def progCandidateModelCodesList (c : Code) (i : ℕ) (p : BitString) (j t : ℕ) : List BitString :=
  (programmedEnum p t).filter (fun w =>
    decide (w ∈ (snapshotCodes c i t)) && isFamilyModelCodeBool j w)

/-- Program-indexed staged model-code list, using `programmedEnum p`. -/
def progStageModelCodesList (c : Code) (i : ℕ) (p : BitString) (j : ℕ) : ℕ → List BitString
  | 0 => (progCandidateModelCodesList c i p j 0).eraseDups
  | t + 1 => (progStageModelCodesList c i p j t ++ progCandidateModelCodesList c i p j (t + 1)).eraseDups

/-- Program-indexed marked-code stream, using `programmedEnum p`. -/
def progMarkedCodeStream (c : Code) (i : ℕ) (p : BitString) (n j k t : ℕ) : List BitString :=
  selectionStrategyOnline n i j k (progStageModelCodesList c i p j t)

theorem progStageModelCodesList_eq_family (c : Code) (i : ℕ) (p : BitString)
    (mem : Finset BitString → Prop) (hp : IsProgramForFamily p mem) (j : ℕ) :
    progStageModelCodesList c i p j = familyStageModelCodesList c i (programmedFamily p mem hp) j := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => simp only [progStageModelCodesList, familyStageModelCodesList, ih]; rfl

theorem progMarkedCodeStream_eq_family (c : Code) (i : ℕ) (p : BitString)
    (mem : Finset BitString → Prop) (hp : IsProgramForFamily p mem) (n j k t : ℕ) :
    progMarkedCodeStream c i p n j k t = familyMarkedCodeStream c i (programmedFamily p mem hp) n j k t := by
  unfold progMarkedCodeStream familyMarkedCodeStream
  rw [progStageModelCodesList_eq_family c i p mem hp j]

/-
Joint computability of the program-indexed candidate model-code slice.
-/
theorem progCandidateModelCodesList_computable (c : Code) :
    Computable (fun q : ((ℕ × BitString) × ℕ) × ℕ =>
      progCandidateModelCodesList c q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have h_filter : Computable (fun (p : List BitString × List BitString × ℕ) => p.1.filter (fun w => decide (w ∈ p.2.1) && isFamilyModelCodeBool p.2.2 w)) := by
    have hp : Primrec₂ (fun (p : List BitString × List BitString × ℕ) (w : BitString) => decide (w ∈ p.2.1) && isFamilyModelCodeBool p.2.2 w) :=
      Primrec.of_eq
        (Primrec.and.comp
          (bitString_mem_primrec.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
          (isFamilyModelCodeBool_primrec_uniform.comp
            (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
        (by intro a; dsimp only [Function.comp_apply, Prod.fst, Prod.snd])
    exact (list_filter_primrec (f := fun (p : List BitString × List BitString × ℕ) => p.1) (p := fun p w => decide (w ∈ p.2.1) && isFamilyModelCodeBool p.2.2 w) Primrec.fst hp).to_comp
  have hcand : Computable (fun q : ((ℕ × BitString) × ℕ) × ℕ => (programmedEnum q.1.1.2 q.2, snapshotCodes c q.1.1.1 q.2, q.1.2)) :=
    (Computable.pair
      (programmedEnum_computable.comp (Computable.pair (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd))
      (Computable.pair
        ((snapshotCodes_primrec c |> Primrec.to_comp).comp (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd))
        (Computable.snd.comp Computable.fst))).of_eq (by intro _; rfl)
  exact (h_filter.comp hcand).of_eq (by intro _; rfl)

/-
Joint computability of the program-indexed staged model-code list.
-/
theorem progStageModelCodesList_computable (c : Code) :
    Computable (fun q : ((ℕ × BitString) × ℕ) × ℕ =>
      progStageModelCodesList c q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have h_eraseDups : Computable (fun l : List BitString => l.eraseDups) :=
    eraseDups_bitstring_primrec.to_comp
  have hg : Computable (fun q : ((ℕ × BitString) × ℕ) × ℕ => (progCandidateModelCodesList c q.1.1.1 q.1.1.2 q.1.2 0).eraseDups) :=
    (h_eraseDups.comp ((progCandidateModelCodesList_computable c).comp (Computable.pair Computable.fst (Computable.const 0)))).of_eq (by intro _; rfl)
  have hh : Computable₂ (fun (q : ((ℕ × BitString) × ℕ) × ℕ) (r : ℕ × List BitString) => (r.2 ++ progCandidateModelCodesList c q.1.1.1 q.1.1.2 q.1.2 (r.1 + 1)).eraseDups) :=
    (h_eraseDups.comp (Computable.list_append.comp (Computable.snd.comp Computable.snd) ((progCandidateModelCodesList_computable c).comp (Computable.pair (Computable.fst.comp Computable.fst) (Computable.succ.comp (Computable.fst.comp Computable.snd)))))).of_eq (by intro _; rfl)
  convert Computable.nat_rec (f := fun q => q.2) Computable.snd hg hh using 1;
  exact funext fun q => by induction q.2 <;> simp +decide [ *, progStageModelCodesList ] ;

/-
Joint computability of the program-indexed marked-code stream.
-/
theorem progMarkedCodeStream_computable (c : Code) :
    Computable (fun q : (((((ℕ × BitString) × ℕ) × ℕ) × ℕ) × ℕ) =>
      progMarkedCodeStream c q.1.1.1.1.1 q.1.1.1.1.2 q.1.1.1.2 q.1.1.2 q.1.2 q.2) := by
  revert c;
  intro c
  unfold progMarkedCodeStream
  exact (selectionStrategyOnline_primrec_uniform.to_comp.comp (Computable.pair (Computable.pair (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))) (Computable.pair (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))) (Computable.pair (Computable.snd.comp (Computable.fst.comp Computable.fst)) (Computable.snd.comp Computable.fst)))) ((progStageModelCodesList_computable c).comp (Computable.pair (Computable.pair (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))) (Computable.snd.comp (Computable.fst.comp Computable.fst))) Computable.snd)))).of_eq (by intro _; rfl)

/-- Program-indexed marked-code selector, using `progMarkedCodeStream`. -/
noncomputable def progMarkedCodeSelectorFn (c : Code) (p : BitString) : BitString →. BitString :=
  fun s =>
    let n := selN s
    let i := selI s
    let j := selJ s
    let k := selK s
    let r := selR s
    (Nat.rfind (fun t => Part.some (decide (r < (progMarkedCodeStream c i p n j k t).eraseDups.length)))).bind
      (fun t =>
        let stream := (progMarkedCodeStream c i p n j k t).eraseDups
        Part.some (stream.getD r []))

theorem progMarkedCodeSelectorFn_eq_family (c : Code) (p : BitString)
    (mem : Finset BitString → Prop) (hp : IsProgramForFamily p mem) (s : BitString) :
    progMarkedCodeSelectorFn c p s = familyMarkedCodeSelectorFn c (programmedFamily p mem hp) s := by
  simp only [progMarkedCodeSelectorFn, familyMarkedCodeSelectorFn,
    progMarkedCodeStream_eq_family c (selI s) p mem hp (selN s) (selJ s) (selK s)]

/-- Universal marked-code selector: reads the family program `p` from the first
component of its input and the marked-selector word from the second. -/
noncomputable def univMarkedCodeSelectorFn (c : Code) : BitString →. BitString :=
  fun s => progMarkedCodeSelectorFn c (decodeFirst s) (decodeSecond s)

section UnivMarkedSelectorPartrec
-- Mirror `familyMarkedCodeSelectorFn_partrec`: sealing these `def`s prevents a
-- `whnf` blow-up when the final `of_eq` reconciles the composed function with the
-- unfolded selector.
attribute [local irreducible] progMarkedCodeStream selN selI selJ selK selR

/-- The universal marked-code selector is partial recursive. -/
theorem univMarkedCodeSelectorFn_partrec (c : Code) : Partrec (univMarkedCodeSelectorFn c) := by
  have dS : Computable (fun st : BitString × ℕ => decodeSecond st.1) :=
    decodeSecond_computable.comp Computable.fst
  have dF : Computable (fun st : BitString × ℕ => decodeFirst st.1) :=
    decodeFirst_computable.comp Computable.fst
  have h_stream : Computable (fun st : BitString × ℕ =>
      (progMarkedCodeStream c (selI (decodeSecond st.1)) (decodeFirst st.1) (selN (decodeSecond st.1))
        (selJ (decodeSecond st.1)) (selK (decodeSecond st.1)) st.2).eraseDups) :=
    eraseDups_bitstring_primrec.to_comp.comp
      ((progMarkedCodeStream_computable c).comp
        (((((((selI_computable.comp dS).pair dF).pair (selN_computable.comp dS)).pair
          (selJ_computable.comp dS)).pair (selK_computable.comp dS)).pair Computable.snd)))
  have h_lt : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
    obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel (α := ℕ) (· < ·))
    convert h.to_comp
  have h_check : Computable (fun st : BitString × ℕ =>
      decide (selR (decodeSecond st.1) <
        (progMarkedCodeStream c (selI (decodeSecond st.1)) (decodeFirst st.1) (selN (decodeSecond st.1))
          (selJ (decodeSecond st.1)) (selK (decodeSecond st.1)) st.2).eraseDups.length)) :=
    h_lt.comp ((selR_computable.comp dS).pair (Computable.list_length.comp h_stream))
  have h_post : Computable (fun st : BitString × ℕ =>
      (progMarkedCodeStream c (selI (decodeSecond st.1)) (decodeFirst st.1) (selN (decodeSecond st.1))
        (selJ (decodeSecond st.1)) (selK (decodeSecond st.1)) st.2).eraseDups.getD
        (selR (decodeSecond st.1)) []) :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp h_stream (selR_computable.comp dS)
  exact (Partrec.bind (Partrec.rfind h_check.to₂.partrec₂) h_post.to₂.partrec₂).of_eq
    (fun s => rfl)

end UnivMarkedSelectorPartrec

/-- Uniform (program-indexed) version of `selected_family_code_setComplexity_bound`,
charging `KPPlain U p` via the universal marked-code selector. -/
theorem uniform_selected_code_setComplexity_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) :
    ∃ c_slack : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop)
      (hp : IsProgramForFamily p mem)
      (n i j k t : ℕ) (w : BitString) (S : Finset BitString) (hS : S.Nonempty),
      k ≤ i →
      w ∈ familyMarkedCodeStream c i (programmedFamily p mem hp) n j k t →
      w = (codedUniformOn S hS).code →
      setComplexity U S hS ≤ (i - k : ENat) + logSlack c_slack (n + i + j) + KPPlain U p := by
  obtain ⟨c_map, hc_map⟩ := KPPlain_partrec_map_le U hU (univMarkedCodeSelectorFn c)
    (univMarkedCodeSelectorFn_partrec c)
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_input, hc_input⟩ := familyMarkedInput_KPPlain_le_addr U hU (c_pair + c_map)
  obtain ⟨c_fold, hc_fold⟩ := logSlack_linear_bound c_input 5 10
  refine ⟨c_fold + 20, fun p mem hp n i j k t w S hS hk hw_stream hcode => ?_⟩
  set 𝒜 := programmedFamily p mem hp with h𝒜
  obtain ⟨r, hr_stage, hget_t⟩ :=
    exists_rank_getD_eraseDups (familyMarkedCodeStream c i 𝒜 n j k t) hw_stream
  have hr_bound : r < (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) := by
    exact lt_of_lt_of_le hr_stage
      (le_trans (eraseDups_bitString_length_le _)
        (selected_family_code_index_bound c i 𝒜 n j k t))
  let M := n + i + j
  let P := 2 * ((i + 2) * (i + 1) * (n + 1))
  let q := (Nat.bits P).length
  let m := i - k + q
  have hpowP : P < 2 ^ q := by
    simpa [P, q] using lt_two_pow_length_natBits P
  have hexp : i + 1 - k = i - k + 1 := by omega
  have hbound_eq :
      (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) =
        P * 2 ^ (i - k) := by
    simp [P, hexp, pow_succ]
    ring
  have hr_pow_m : r < 2 ^ (m + 1) := by
    have hlt : r < P * 2 ^ (i - k) := by
      simpa [hbound_eq] using hr_bound
    have hmul : P * 2 ^ (i - k) ≤ 2 ^ q * 2 ^ (i - k) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hpowP)
    have hpow : 2 ^ q * 2 ^ (i - k) = 2 ^ m := by
      rw [show m = q + (i - k) by omega, pow_add]
    exact lt_of_lt_of_le hlt (by
      calc P * 2 ^ (i - k) ≤ 2 ^ q * 2 ^ (i - k) := hmul
        _ = 2 ^ m := hpow
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ m))
  let h_exists : ∃ u, r < (familyMarkedCodeStream c i 𝒜 n j k u).eraseDups.length := ⟨t, hr_stage⟩
  let t0 := Nat.find h_exists
  have ht0_lt : r < (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups.length :=
    Nat.find_spec h_exists
  have ht0_le_t : t0 ≤ t :=
    Nat.find_le (p := fun u => r < (familyMarkedCodeStream c i 𝒜 n j k u).eraseDups.length) hr_stage
  have hfirst : ∀ t' < t0, ¬(r < (familyMarkedCodeStream c i 𝒜 n j k t').eraseDups.length) := by
    intro t' ht'
    exact Nat.find_min h_exists ht'
  have hpre : (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups <+:
      (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups :=
    familyMarkedCodeStream_eraseDups_prefix_of_le c i 𝒜 n j k ht0_le_t
  have hget_t0 : (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups.getD r [] = w := by
    have hget := StagedEnumeration.getD_eq_of_prefix
      (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups
      (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups hpre r [] ht0_lt
    rw [← hget_t]
    exact hget.symm
  have hsel_eq := familyMarkedCodeSelectorFn_eq_of_rank c 𝒜 n i j k r t0 ht0_lt hfirst
  rw [hget_t0] at hsel_eq
  -- Bridge to the universal selector on the `p`-padded input.
  have huniv : univMarkedCodeSelectorFn c (pairCode p (familyMarkedInput n i j k r)) = Part.some w := by
    unfold univMarkedCodeSelectorFn
    rw [decodeFirst_pairCode, decodeSecond_pairCode, progMarkedCodeSelectorFn_eq_family c p mem hp]
    exact hsel_eq
  have hw_sel : w ∈ univMarkedCodeSelectorFn c (pairCode p (familyMarkedInput n i j k r)) :=
    Part.eq_some_iff.mp huniv
  have hcomp1 : KPPlain U w ≤ KPPlain U (pairCode p (familyMarkedInput n i j k r)) + (c_map : ENat) :=
    hc_map (pairCode p (familyMarkedInput n i j k r)) w hw_sel
  have hchain : KPPlain U w ≤
      KPPlain U p + (KPPlain U (familyMarkedInput n i j k r) + ((c_pair + c_map : ℕ) : ENat)) := by
    calc KPPlain U w ≤ KPPlain U (pairCode p (familyMarkedInput n i j k r)) + (c_map : ENat) := hcomp1
      _ ≤ (KPPlain U p + KPPlain U (familyMarkedInput n i j k r) + (c_pair : ENat)) + (c_map : ENat) := by
            gcongr
            exact hc_pair p (familyMarkedInput n i j k r)
      _ = KPPlain U p + (KPPlain U (familyMarkedInput n i j k r) + ((c_pair + c_map : ℕ) : ENat)) := by
            push_cast; ring
  have hcomp2 : KPPlain U (familyMarkedInput n i j k r) + ((c_pair + c_map : ℕ) : ENat) ≤
      ((m : ENat) + 1) + logSlack c_input (n + i + j + k + m) :=
    hc_input n i j k r m hr_pow_m
  have hq : q ≤ 3 * (Nat.bits M).length + 10 := by
    simpa [M, P, q] using markedStream_poly_bits_bound n i j
  have hbudget : n + i + j + k + m ≤ 5 * M + 10 := by
    have hWle : (Nat.bits M).length ≤ M := length_natBits_le_self M
    simp [M, m]
    omega
  have hfold : logSlack c_input (n + i + j + k + m) ≤ logSlack c_fold M := by
    exact (logSlack_mono (c := c_input) hbudget).trans (hc_fold M)
  have hqslack : 3 * (Nat.bits M).length + 11 + logSlack c_fold M ≤
      logSlack (c_fold + 20) M := by
    unfold logSlack
    nlinarith [Nat.zero_le (17 * (Nat.bits M).length)]
  have htotal : ((m : ENat) + 1) + logSlack c_input (n + i + j + k + m) ≤
      (i - k : ENat) + logSlack (c_fold + 20) M := by
    have hm_le : m + 1 ≤ (i - k) + (3 * (Nat.bits M).length + 11) := by
      simp [m]
      omega
    have hnat : m + 1 + logSlack c_input (n + i + j + k + m) ≤
        (i - k) + logSlack (c_fold + 20) M := by
      have hnat1 : m + 1 + logSlack c_input (n + i + j + k + m) ≤
          (i - k) + (3 * (Nat.bits M).length + 11 + logSlack c_fold M) := by
        omega
      omega
    exact_mod_cast hnat
  have hfinal : KPPlain U w ≤ KPPlain U p + ((i - k : ENat) + logSlack (c_fold + 20) M) := by
    refine hchain.trans ?_
    exact add_le_add_right (hcomp2.trans htotal) (KPPlain U p)
  unfold setComplexity
  rw [← hcode]
  calc KPPlain U w ≤ KPPlain U p + ((i - k : ENat) + logSlack (c_fold + 20) M) := hfinal
    _ = (i - k : ENat) + logSlack (c_fold + 20) M + KPPlain U p := by ring

/-- Uniform selected-set complexity lemma. -/
theorem uniform_familyComplexityRefinedSet (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop),
      IsProgramForFamily p mem →
      ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsMem mem U x i j k →
      k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), mem S ∧ x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) + KPPlain U p : ENat) ∧
        S.card ≤ 2 ^ (j + logSlack c (n + i + j)) := by
  obtain ⟨c_opt, hc_opt⟩ : ∃ c_opt : Code, IsCodeFor c_opt U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c_slack, hc_slack⟩ := uniform_selected_code_setComplexity_bound U hU c_opt
  refine ⟨c_slack, ?_⟩
  intro p mem hp x n i j k hn hmany hk
  set 𝒜 := programmedFamily p mem hp with h𝒜
  have hmany_in : ManyIJDescriptionsIn 𝒜 U x i j k :=
    (manyIJDescriptionsMem_iff_in p mem programmedEnum programmedEnum_computable
      hp.mono hp.sound hp.complete U x i j k).mp hmany
  obtain ⟨t, ht⟩ := manyIJDescriptionsIn_visible_stage hc_opt 𝒜 x n i j k hn hmany_in
  obtain ⟨w, hw_stream, hw_desc⟩ := familyMarkedCodeStream_covers_many c_opt i 𝒜 n j k t x hn ht
  rcases hw_desc with ⟨S, hS, hmemS, hcode_eq, hcard, hxS⟩
  have hcomp := hc_slack p mem hp n i j k t w S hS hk hw_stream hcode_eq
  refine ⟨S, hS, hmemS.1, hxS, ?_, ?_⟩
  · calc setComplexity U S hS
        ≤ (i - k : ENat) + logSlack c_slack (n + i + j) + KPPlain U p := hcomp
      _ = (i - k + logSlack c_slack (n + i + j) + KPPlain U p : ENat) := by ring
  · refine le_trans (Nat.cast_le.mpr hcard) ?_
    exact Nat.cast_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))

/-!
### `enum`-dependent forms of the two uniform leaves

The two uniform leaves above place `∃ c` *before* the family program `p`.  This is
sound precisely because the family is presented through the *fixed universal
interpreter* `programmedEnum` (so `c` is a single constant for that interpreter)
and the extra representation cost is paid by `KPPlain U p`.  With an *arbitrary*
host-language enumerator `enum` the same quantifier order would be unsound (an
adversarial `enum` could hide an arbitrarily complex family behind a trivial `p`),
so the lemmas below record the paper-faithful `enum`-relative statements, where the
constant is chosen after the enumerator.  They are proved by transporting the
fixed-family results (`restricted_description_count_of_conditional_complexity_gap_aux`,
`exists_familyComplexityRefinedSet`) along the `uniformPreFamily` bridge; no
`KPPlain U p` budget is needed once `c` may depend on `enum`. -/

/-- Sound form of `uniform_description_count_of_conditional_complexity_gap`:
the constant is chosen after the enumerator. -/
theorem uniform_description_count_of_conditional_complexity_gap_ofEnum
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (p : BitString) (mem : Finset BitString → Prop) (enum : BitString → ℕ → List BitString)
    (henum : Computable (fun p_t : BitString × ℕ => enum p_t.1 p_t.2))
    (hmono : ∀ t, enum p t <+: enum p (t + 1))
    (hsound : ∀ t, ∀ w ∈ enum p t, ∃ (S : Finset BitString) (hS : S.Nonempty),
      mem S ∧ w = (codedUniformOn S hS).code)
    (hcomplete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S →
      ∃ t, (codedUniformOn S hS).code ∈ enum p t) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n i j m kx : ℕ),
      x.length = n →
      mem A →
      x ∈ A →
      setComplexity U A hA ≤ (i : ENat) →
      A.card ≤ 2 ^ j →
      HasPrefixComplexityValue U x kx →
      ¬ ManyIJDescriptionsMem mem U x i j m →
      KP U (codedUniformOn A hA).code (prefixComplexityContext x kx)
        ≤ (m + logSlack c (n + i + j) : ENat) := by
  obtain ⟨c, hc⟩ := restricted_description_count_of_conditional_complexity_gap_aux U hU
    (uniformPreFamily p mem enum henum hmono hsound hcomplete)
  refine ⟨c, fun A hA x n i j m kx hn hmem hx hi hj hkx hnm => ?_⟩
  refine hc A hA x n i j m kx hn ⟨hmem, hA⟩ hx hi hj hkx ?_
  intro hIn
  exact hnm ((manyIJDescriptionsMem_iff_in p mem enum henum hmono hsound hcomplete
    U x i j m).mpr hIn)

/-- Sound form of `uniform_familyComplexityRefinedSet`: the constant is chosen
after the enumerator. -/
theorem uniform_familyComplexityRefinedSet_ofEnum
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (p : BitString) (mem : Finset BitString → Prop) (enum : BitString → ℕ → List BitString)
    (henum : Computable (fun p_t : BitString × ℕ => enum p_t.1 p_t.2))
    (hmono : ∀ t, enum p t <+: enum p (t + 1))
    (hsound : ∀ t, ∀ w ∈ enum p t, ∃ (S : Finset BitString) (hS : S.Nonempty),
      mem S ∧ w = (codedUniformOn S hS).code)
    (hcomplete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S →
      ∃ t, (codedUniformOn S hS).code ∈ enum p t) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsMem mem U x i j k →
      k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), mem S ∧ x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) : ENat) ∧
        S.card ≤ 2 ^ (j + logSlack c (n + i + j)) := by
  obtain ⟨c, hc⟩ := exists_familyComplexityRefinedSet U hU
    (uniformPreFamily p mem enum henum hmono hsound hcomplete)
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hmemS, hxS, hcomp, hcard⟩ := hc x n i j k hn
    ((manyIJDescriptionsMem_iff_in p mem enum henum hmono hsound hcomplete
      U x i j k).mp hmany) hk
  exact ⟨S, hS, hmemS.1, hxS, hcomp, hcard⟩

theorem manyIJDescriptionsMem_zero_of_mem {mem : Finset BitString → Prop} {U : Map} {x : BitString} {A : Finset BitString} {i j : ℕ}
    (hA : A.Nonempty) (hx : x ∈ A) (hmem : mem A) (hi : setComplexity U A hA ≤ (i : ENat))
    (hj : A.card ≤ 2 ^ j) :
    ManyIJDescriptionsMem mem U x i j 0 := by
  classical
  unfold ManyIJDescriptionsMem
  rw [pow_zero]
  refine Finset.card_pos.mpr ?_
  refine ⟨A, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hx⟩
  unfold descriptionsWithComplexityLeAndSizeLeMem
  rw [Finset.mem_filter]
  refine ⟨?_, hmem⟩
  unfold descriptionsWithComplexityLeAndSizeLe
  rw [Finset.mem_filter]
  exact ⟨mem_descriptionsWithComplexityLe_of_complexity hA hi, hj⟩

theorem ManyIJDescriptionsMem.mono_j {mem : Finset BitString → Prop} {U : Map} {x : BitString} {i j j' k : ℕ}
    (h : ManyIJDescriptionsMem mem U x i j k) (hj : j ≤ j') : ManyIJDescriptionsMem mem U x i j' k := by
  classical
  unfold ManyIJDescriptionsMem at *
  refine h.trans (Finset.card_le_card ?_)
  refine Finset.filter_subset_filter _ ?_
  intro S hS
  unfold descriptionsWithComplexityLeAndSizeLeMem at hS ⊢
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨descriptionsWithComplexityLeAndSizeLe_subset_of_le_right U i hj hS.1, hS.2⟩

theorem ManyIJDescriptionsMem.mono_k {mem : Finset BitString → Prop} {U : Map} {x : BitString} {i j k k' : ℕ}
    (h : ManyIJDescriptionsMem mem U x i j k) (hk : k' ≤ k) : ManyIJDescriptionsMem mem U x i j k' := by
  unfold ManyIJDescriptionsMem at *
  exact le_trans (Nat.pow_le_pow_right (by norm_num) hk) h

theorem uniform_manyIJDescriptionsMem_of_realizedSetOptimalityGap (U : Map) (hU : IsOptimalPrefixConditional U) :
  ∃ c : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop),
    IsProgramForFamily p mem →
    ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n delta d i j kx c_soi : ℕ),
    x.length = n →
    mem A →
    RealizedSetOptimalityGap U A hA x delta i j kx →
    CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
    d ≤ delta + c_soi →
    ∃ slack : ℕ, slack ≤ logSlack c (n + delta + d) + (KPPlain U p).toNat ∧
      ManyIJDescriptionsMem mem U x i j (delta - d - slack) := by
  rcases gap_lowerBound_conditional_setComplexity_tight_of_le_add U hU with ⟨c1, hc1⟩
  rcases uniform_description_count_of_conditional_complexity_gap U hU with ⟨c2, hc2⟩
  rcases gapCounting_slack_arithmetic U hU c1 c2 with ⟨c3, hc3⟩
  refine ⟨c3, fun p mem hp
      A hA x n delta d i j kx c_soi hn hmem h_realized hdef_cond hd => ?_⟩
  have hxA := h_realized.1
  have hi := h_realized.2.1
  have hj := h_realized.2.2.1
  have hj_lower := h_realized.2.2.2.1
  have hkx := h_realized.2.2.2.2.1
  have hdelta_eq := h_realized.2.2.2.2.2
  have hi_bound : (i : ENat) ≤ KPPlain U x + (delta : ENat) := by
    have hkx_eq : KPPlain U x = (kx : ENat) := hkx.symm
    rw [hkx_eq]
    norm_cast
    omega
  rcases card_le_of_deficiency hxA hdef_cond with ⟨j_opt, hj_opt, hj_bound⟩
  have h_gap := hc1 A hA x n delta d i j kx c_soi hn
    ⟨hxA, hi, hj, hj_lower, hkx, hdelta_eq⟩ hdef_cond hd
  have hj_min : A.card ≤ 2 ^ min j j_opt := by
    by_cases hle : j ≤ j_opt
    · rw [Nat.min_eq_left hle]
      exact hj
    · rw [Nat.min_eq_right (le_of_not_ge hle)]
      exact hj_opt
  clear hdelta_eq
  set kp := (KPPlain U p).toNat
  have hkp_eq : (kp : ENat) = KPPlain U p := ENat.coe_toNat (KPPlain_ne_top_of_optimal U hU p)
  set slack := logSlack c3 (n + delta + d) + kp
  use slack
  refine ⟨le_rfl, ?_⟩
  by_cases h_zero : delta - d ≤ slack
  · rw [Nat.sub_eq_zero_of_le h_zero]
    exact manyIJDescriptionsMem_zero_of_mem hA hxA hmem (le_of_eq hi) hj
  · by_contra hnot_goal
    have hnot_min :
        ¬ ManyIJDescriptionsMem mem U x i (min j j_opt) (delta - d - slack) := by
      intro hmany
      exact hnot_goal (ManyIJDescriptionsMem.mono_j hmany (min_le_left _ _))
    have h_count := hc2 p mem hp
      A hA x n i (min j j_opt) (delta - d - slack) kx
      hn hmem hxA (le_of_eq hi) hj_min hkx hnot_min
    have h_count' :
        KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤
          (delta - d - slack + logSlack c2 (n + i + min j j_opt) + kp : ENat) := by
      rw [← hkp_eq] at h_count
      simpa using h_count
    have h_arith := hc3 n delta d i (min j j_opt) x (codedUniformOn A hA).code
      hn hi_bound (le_trans (mod_cast min_le_right _ _) hj_bound)
    have hsum_lt :
        logSlack c2 (n + i + min j j_opt) + logSlack c1 (n + delta + d) <
          logSlack c3 (n + delta + d) := by
      simpa using h_arith
    have hslack_lt : slack < delta - d := Nat.lt_of_not_ge h_zero
    have hnat_lt :
        delta - d - slack + logSlack c2 (n + i + min j j_opt) + kp +
            logSlack c1 (n + delta + d) < delta - d := by
      omega
    have hcontra : (delta - d : ENat) < (delta - d : ENat) := by
      calc
        (delta - d : ENat)
            ≤ KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) +
                (logSlack c1 (n + delta + d) : ENat) := h_gap
        _ ≤ (delta - d - slack + logSlack c2 (n + i + min j j_opt) + kp : ENat) +
                (logSlack c1 (n + delta + d) : ENat) := by
              exact add_le_add h_count' le_rfl
        _ = (delta - d - slack + logSlack c2 (n + i + min j j_opt) + kp +
                logSlack c1 (n + delta + d) : ENat) := by
              ring
        _ < (delta - d : ENat) := by
              exact_mod_cast hnat_lt
    exact not_lt_of_ge le_rfl hcontra

theorem manyIJDescriptionsMem_k_le_i_add_one {mem : Finset BitString → Prop} {U : Map}
    {x : BitString} {i j k : ℕ} (h : ManyIJDescriptionsMem mem U x i j k) : k ≤ i + 1 := by
  contrapose! h
  simp +decide [ManyIJDescriptionsMem]
  apply lt_of_le_of_lt (Finset.card_le_card ?_) ?_
  exact descriptionsWithComplexityLeAndSizeLe U i j
  · simp +contextual [Finset.subset_iff, descriptionsWithComplexityLeAndSizeLeMem]
  · exact lt_of_le_of_lt (card_descriptionsWithComplexityLeAndSizeLe U i j)
      (pow_lt_pow_right₀ (by decide) h)

theorem uniform_deficiencies_theorem_tight (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop),
      IsProgramForFamily p mem →
      ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j kx c_soi : ℕ),
      x.length = n →
      mem A →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), mem B ∧ x ∈ B ∧
        setComplexity U B hB + (delta - d : ℕ) ≤
          setComplexity U A hA + (logSlack c (n + delta + d) + 2 * KPPlain U p : ENat) ∧
        SetOptimalityDeficiencyLe U B hB x (d + logSlack c (n + delta + d) + 2 * (KPPlain U p).toNat) := by
  obtain ⟨c1, hc1⟩ := uniform_manyIJDescriptionsMem_of_realizedSetOptimalityGap U hU
  obtain ⟨c2, hc2⟩ := uniform_familyComplexityRefinedSet U hU
  obtain ⟨bb, hbb⟩ := visible_param_linear_bound U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c2 4 bb
  refine ⟨c1 + 2 * C0 + 2, ?_⟩
  intro p mem hp A hA x n delta d i j kx c_soi
    hn hmem h_realized h_def hd
  obtain ⟨slack1, hslack1, h_many⟩ :=
    hc1 p mem hp
      A hA x n delta d i j kx c_soi hn hmem h_realized h_def hd
  set k := min (delta - d - slack1) i with hk_def
  have hk_le_i : k ≤ i := Nat.min_le_right _ _
  have h_many' : ManyIJDescriptionsMem mem U x i j k :=
    ManyIJDescriptionsMem.mono_k h_many (Nat.min_le_left _ _)
  have hkc : delta - d - slack1 ≤ i + 1 :=
    manyIJDescriptionsMem_k_le_i_add_one h_many
  obtain ⟨B, hB, hmemB, hxB, hcompB, hsizeB⟩ :=
    hc2 p mem hp x n i j k hn h_many' hk_le_i
  set kp := (KPPlain U p).toNat with hkp_def
  have hkp_eq : (kp : ENat) = KPPlain U p := by
    rw [hkp_def]
    exact ENat.coe_toNat (KPPlain_ne_top_of_optimal U hU p)
  rw [← hkp_eq] at hcompB
  have hj_bound : (j : ENat) + i ≤ KPPlain U x + delta := by
    have hdelta := h_realized.2.2.2.2.2
    have hkx := h_realized.2.2.2.2.1
    rw [show KPPlain U x = kx from hkx.symm]
    norm_cast
    omega
  have hvis : n + i + j ≤ 4 * (n + delta + d) + bb := by
    have h := hbb x n i j delta d hn hj_bound
    omega
  have hslackvis : logSlack c2 (n + i + j) ≤ logSlack C0 (n + delta + d) :=
    le_trans (logSlack_mono_right c2 hvis) (hC0 (n + delta + d))
  have hdk : (delta - d) - k ≤ slack1 + 1 := by omega
  have hdeltak : delta - k ≤ d + slack1 + 1 := by omega
  have hcomb : logSlack c1 (n + delta + d) + 2 * logSlack C0 (n + delta + d) + 1 ≤
      logSlack (c1 + 2 * C0 + 2) (n + delta + d) := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits (n + delta + d)).length)]
  refine ⟨B, hB, hmemB, hxB, ?_, ?_⟩
  · refine le_trans (add_le_add hcompB (le_refl ((delta - d : ℕ) : ENat))) ?_
    rw [show setComplexity U A hA = (i : ENat) from h_realized.2.1, ← hkp_eq]
    norm_cast
    omega
  · apply setOptimalityDeficiencyLe_of_profile hxB hcompB hsizeB
    rw [show KPPlain U x = kx from h_realized.2.2.2.2.1.symm]
    norm_cast
    change (i - k + logSlack c2 (n + i + j) + kp) + (j + logSlack c2 (n + i + j)) ≤
      kx + (d + logSlack (c1 + 2 * C0 + 2) (n + delta + d) + 2 * kp)
    have hdelta_eq := h_realized.2.2.2.2.2
    omega

/-- The uniform proposition for arbitrary enumerable 𝒜 (slack `O(K(p) + log K(A) + log n + log log #A)`).
Stated with the enumeration program `p` in the condition. -/
theorem restricted_stochasticity_to_optimal_set_uniform (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop),
      IsProgramForFamily p mem →
      ∀ (x : BitString) (n alpha beta : ℕ),
      x.length = n →
      (∃ (A : Finset BitString) (hA : A.Nonempty), mem A ∧ setComplexity U A hA ≤ (alpha : ENat) ∧ CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x beta) →
      (∃ (A : Finset BitString) (hA : A.Nonempty), mem A ∧ setComplexity U A hA ≤ (alpha + logSlack c (n + alpha + beta) + 2 * KPPlain U p : ENat) ∧ SetOptimalityDeficiencyLe U A hA x (beta + logSlack c (n + alpha + beta) + 2 * (KPPlain U p).toNat)) := by
  obtain ⟨c_def, hc_def⟩ := uniform_deficiencies_theorem_tight U hU
  obtain ⟨c_br, hc_br⟩ := restricted_exists_realizedGap_of_member U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c_def 4 c_br
  refine ⟨max (c_br + C0) (c_def + c_br + 1) + 1, ?_⟩
  intro p mem hp x n alpha beta hn hyp
  obtain ⟨A, hA, hmemA, hcompA, hdefA⟩ := hyp
  obtain ⟨delta, i, j, kx, d, hgap, hdef, hdd, hi, hd, hlin⟩ :=
    hc_br A hA x n alpha beta hn hcompA hdefA
  obtain ⟨B, hB, hmemB, hxB, hcompB, hoptB⟩ :=
    hc_def p mem hp A hA x n delta d i j kx c_br hn hmemA hgap hdef hdd
  have hlogSlack : logSlack c_def (n + delta + d) ≤ logSlack C0 (n + alpha + beta) :=
    le_trans (logSlack_mono_right _ hlin) (hC0 _)
  have hcompA_i : setComplexity U A hA = (i : ENat) := hgap.2.1
  have hslack : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
      ≤ logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) := by
    have h1 : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
        ≤ logSlack (c_br + C0 + 1) (n + alpha + beta) := by
      unfold logSlack; ring_nf; linarith
    exact le_trans h1 (logSlack_mono_left (Nat.succ_le_succ (le_max_left _ _)) _)
  refine ⟨B, hB, hmemB, ?_, ?_⟩
  · have h_le1 : setComplexity U B hB ≤ (i : ENat) + (logSlack c_def (n + delta + d) : ENat) + 2 * KPPlain U p := by
      rw [hcompA_i] at hcompB
      have h_rhs : (logSlack c_def (n + delta + d) + 2 * KPPlain U p : ENat) = (logSlack c_def (n + delta + d) : ENat) + 2 * KPPlain U p := by rfl
      rw [h_rhs] at hcompB
      have h_assoc : (i : ENat) + ((logSlack c_def (n + delta + d) : ENat) + 2 * KPPlain U p) = (i : ENat) + (logSlack c_def (n + delta + d) : ENat) + 2 * KPPlain U p := by exact (add_assoc _ _ _).symm
      rw [h_assoc] at hcompB
      have h_self : setComplexity U B hB ≤ setComplexity U B hB + (delta - d : ℕ) := le_add_right le_rfl
      exact le_trans h_self hcompB
    have h_le2 : (i : ENat) + (logSlack c_def (n + delta + d) : ENat) + 2 * KPPlain U p ≤ (alpha : ENat) + (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) : ENat) + 2 * KPPlain U p := by
      have hnat : i + logSlack c_def (n + delta + d) ≤ alpha + logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) := by omega
      have hcast : (i : ENat) + (logSlack c_def (n + delta + d) : ENat) ≤ (alpha : ENat) + (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) : ENat) := by
        exact_mod_cast hnat
      exact add_le_add hcast le_rfl
    have h_le3 : (alpha : ENat) + (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) : ENat) + 2 * KPPlain U p = (alpha + logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) + 2 * KPPlain U p : ENat) := by rfl
    rw [← h_le3]
    exact le_trans h_le1 h_le2
  · refine hoptB.mono_beta ?_
    omega

theorem restricted_manyIJDescriptionsIn_of_realizedSetOptimalityGap (U : Map) (hU : IsOptimalPrefixConditional U) (𝒜 : PreDescriptionFamily) :
  ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n delta d i j kx c_soi : ℕ),
    x.length = n →
    𝒜.mem A →
    RealizedSetOptimalityGap U A hA x delta i j kx →
    CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
    d ≤ delta + c_soi →
    ∃ slack : ℕ, slack ≤ logSlack c (n + delta + d) ∧
      ManyIJDescriptionsIn 𝒜 U x i j (delta - d - slack) := by
  rcases gap_lowerBound_conditional_setComplexity_tight_of_le_add U hU with ⟨c1, hc1⟩
  rcases restricted_description_count_of_conditional_complexity_gap_aux U hU 𝒜 with ⟨c2, hc2⟩
  rcases gapCounting_slack_arithmetic U hU c1 c2 with ⟨c3, hc3⟩
  refine ⟨c3, fun A hA x n delta d i j kx c_soi hn hmem h_realized hdef_cond hd => ?_⟩
  have hxA := h_realized.1
  have hi := h_realized.2.1
  have hj := h_realized.2.2.1
  have hj_lower := h_realized.2.2.2.1
  have hkx := h_realized.2.2.2.2.1
  have hdelta := h_realized.2.2.2.2.2
  have hi_bound : (i : ENat) ≤ KPPlain U x + (delta : ENat) := by
    have hkx_eq : KPPlain U x = (kx : ENat) := hkx.symm
    rw [hkx_eq]
    norm_cast
    omega
  rcases card_le_of_deficiency hxA hdef_cond with ⟨j_opt, hj_opt, hj_bound⟩
  have h_gap := hc1 A hA x n delta d i j kx c_soi hn
    ⟨hxA, hi, hj, hj_lower, hkx, h_realized.2.2.2.2.2⟩ hdef_cond hd
  have hj_min : A.card ≤ 2 ^ min j j_opt := by
    by_cases hle : j ≤ j_opt
    · rw [Nat.min_eq_left hle]; exact hj
    · rw [Nat.min_eq_right (le_of_not_ge hle)]; exact hj_opt
  set slack := logSlack c3 (n + delta + d)
  use slack
  refine ⟨le_rfl, ?_⟩
  by_cases h_zero : delta - d ≤ slack
  · rw [Nat.sub_eq_zero_of_le h_zero]
    exact manyIJDescriptionsIn_zero_of_mem hA hxA hmem (le_of_eq hi) hj
  · by_contra hnot_goal
    have hnot_min : ¬ ManyIJDescriptionsIn 𝒜 U x i (min j j_opt) (delta - d - slack) := by
      intro hmany
      exact hnot_goal (ManyIJDescriptionsIn.mono_j hmany (min_le_left _ _))
    have h_count := hc2 A hA x n i (min j j_opt) (delta - d - slack) kx
      hn hmem hxA (le_of_eq hi) hj_min hkx hnot_min
    have h_arith := hc3 n delta d i (min j j_opt) x (codedUniformOn A hA).code
      hn hi_bound (le_trans (mod_cast min_le_right _ _) hj_bound)
    have hsum_lt : logSlack c2 (n + i + min j j_opt) + logSlack c1 (n + delta + d) <
          logSlack c3 (n + delta + d) := by simpa using h_arith
    have hnat_lt : delta - d - slack + logSlack c2 (n + i + min j j_opt) +
            logSlack c1 (n + delta + d) < delta - d := by omega
    have hcontra : (delta - d : ENat) < (delta - d : ENat) := by
      calc (delta - d : ENat)
            ≤ KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) +
                (logSlack c1 (n + delta + d) : ENat) := h_gap
        _ ≤ (delta - d - slack + logSlack c2 (n + i + min j j_opt) : ENat) +
                (logSlack c1 (n + delta + d) : ENat) := add_le_add (by exact_mod_cast h_count) le_rfl
        _ = (delta - d - slack + logSlack c2 (n + i + min j j_opt) +
                logSlack c1 (n + delta + d) : ENat) := by ring
        _ < (delta - d : ENat) := by exact_mod_cast hnat_lt
    exact not_lt_of_ge le_rfl hcontra

theorem manyIJDescriptionsIn_k_le_i_add_one {𝒜 : PreDescriptionFamily} {U : Map}
    {x : BitString} {i j k : ℕ} (h : ManyIJDescriptionsIn 𝒜 U x i j k) : k ≤ i + 1 := by
  contrapose! h
  simp +decide [ManyIJDescriptionsIn]
  apply lt_of_le_of_lt (Finset.card_le_card ?_) ?_
  exact descriptionsWithComplexityLeAndSizeLe U i j
  · simp +contextual [Finset.subset_iff, descriptionsWithComplexityLeAndSizeLeIn]
  · exact lt_of_le_of_lt (card_descriptionsWithComplexityLeAndSizeLe U i j)
      (pow_lt_pow_right₀ (by decide) h)

theorem restricted_deficiencies_theorem_tight
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒜 : PreDescriptionFamily) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
      (n delta d i j kx c_soi : ℕ),
      x.length = n →
      𝒜.mem A →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), 𝒜.mem B ∧ x ∈ B ∧
        setComplexity U B hB + (delta - d : ℕ) ≤
          setComplexity U A hA + (logSlack c (n + delta + d) : ENat) ∧
        SetOptimalityDeficiencyLe U B hB x (d + logSlack c (n + delta + d)) := by
  obtain ⟨c1, hc1⟩ := restricted_manyIJDescriptionsIn_of_realizedSetOptimalityGap U hU 𝒜
  obtain ⟨c2, hc2⟩ := exists_familyComplexityRefinedSet U hU 𝒜
  obtain ⟨bb, hbb⟩ := visible_param_linear_bound U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c2 4 bb
  refine ⟨c1 + 2 * C0 + 2, ?_⟩
  intro A hA x n delta d i j kx c_soi hn hmem h_realized h_def hd
  obtain ⟨slack1, hslack1, h_many⟩ :=
    hc1 A hA x n delta d i j kx c_soi hn hmem h_realized h_def hd
  set k := min (delta - d - slack1) i with hk_def
  have hk_le_i : k ≤ i := Nat.min_le_right _ _
  have h_many' : ManyIJDescriptionsIn 𝒜 U x i j k :=
    ManyIJDescriptionsIn.mono_k h_many (Nat.min_le_left _ _)
  have hkc : delta - d - slack1 ≤ i + 1 :=
    manyIJDescriptionsIn_k_le_i_add_one h_many
  obtain ⟨B, hB, hmemB, hxB, hcompB, hsizeB⟩ :=
    hc2 x n i j k hn h_many' hk_le_i
  have hj_bound : (j : ENat) + i ≤ KPPlain U x + delta := by
    have hdelta := h_realized.2.2.2.2.2
    have hkx := h_realized.2.2.2.2.1
    rw [show KPPlain U x = kx from hkx.symm]
    norm_cast
    omega
  have hvis : n + i + j ≤ 4 * (n + delta + d) + bb := by
    have h := hbb x n i j delta d hn hj_bound
    omega
  have hslackvis : logSlack c2 (n + i + j) ≤ logSlack C0 (n + delta + d) :=
    le_trans (logSlack_mono_right c2 hvis) (hC0 (n + delta + d))
  have hdk : (delta - d) - k ≤ slack1 + 1 := by omega
  have hdeltak : delta - k ≤ d + slack1 + 1 := by omega
  have hcomb : logSlack c1 (n + delta + d) + 2 * logSlack C0 (n + delta + d) + 1 ≤
      logSlack (c1 + 2 * C0 + 2) (n + delta + d) := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits (n + delta + d)).length)]
  refine ⟨B, hB, hmemB, hxB, ?_, ?_⟩
  · refine le_trans (add_le_add hcompB (le_refl ((delta - d : ℕ) : ENat))) ?_
    rw [show setComplexity U A hA = (i : ENat) from h_realized.2.1]
    norm_cast
    omega
  · apply setOptimalityDeficiencyLe_of_profile hxB hcompB hsizeB
    rw [show KPPlain U x = kx from h_realized.2.2.2.2.1.symm]
    norm_cast
    change (i - k + logSlack c2 (n + i + j)) + (j + logSlack c2 (n + i + j)) ≤
      kx + (d + logSlack (c1 + 2 * C0 + 2) (n + delta + d))
    have hdelta_eq := h_realized.2.2.2.2.2
    omega

theorem restricted_stochasticity_to_optimal_set_thm (U : Map) (hU : IsOptimalPrefixConditional U) (𝒜 : PreDescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n alpha beta : ℕ),
      x.length = n →
      (∃ (A : Finset BitString) (hA : A.Nonempty), 𝒜.mem A ∧ setComplexity U A hA ≤ (alpha : ENat) ∧ CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x beta) →
      (∃ (A : Finset BitString) (hA : A.Nonempty), 𝒜.mem A ∧ setComplexity U A hA ≤ (alpha + logSlack c (n + alpha + beta) : ENat) ∧ SetOptimalityDeficiencyLe U A hA x (beta + logSlack c (n + alpha + beta))) := by
  obtain ⟨c_def, hc_def⟩ := restricted_deficiencies_theorem_tight U hU 𝒜
  obtain ⟨c_br, hc_br⟩ := restricted_exists_realizedGap_of_member U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c_def 4 c_br
  refine ⟨max (c_br + C0) (c_def + c_br + 1) + 1, ?_⟩
  intro x n alpha beta hn hyp
  obtain ⟨A, hA, hmemA, hcompA, hdefA⟩ := hyp
  obtain ⟨delta, i, j, kx, d, hgap, hdef, hdd, hi, hd, hlin⟩ :=
    hc_br A hA x n alpha beta hn hcompA hdefA
  obtain ⟨B, hB, hmemB, hxB, hcompB, hoptB⟩ :=
    hc_def A hA x n delta d i j kx c_br hn hmemA hgap hdef hdd
  have hlogSlack : logSlack c_def (n + delta + d) ≤ logSlack C0 (n + alpha + beta) :=
    le_trans (logSlack_mono_right _ hlin) (hC0 _)
  have hcompA_i : setComplexity U A hA = (i : ENat) := hgap.2.1
  have hslack : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
      ≤ logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) := by
    have h1 : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
        ≤ logSlack (c_br + C0 + 1) (n + alpha + beta) := by
      unfold logSlack; ring_nf; linarith
    exact le_trans h1 (logSlack_mono_left (Nat.succ_le_succ (le_max_left _ _)) _)
  refine ⟨B, hB, hmemB, ?_, ?_⟩
  · have h_le1 : setComplexity U B hB ≤ (i : ENat) + (logSlack c_def (n + delta + d) : ENat) := by
      rw [hcompA_i] at hcompB
      have h_self : setComplexity U B hB ≤ setComplexity U B hB + (delta - d : ℕ) := le_add_right le_rfl
      exact le_trans h_self hcompB
    have h_le2 : (i : ENat) + (logSlack c_def (n + delta + d) : ENat) ≤ (alpha : ENat) + (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) : ENat) := by
      have hnat : i + logSlack c_def (n + delta + d) ≤ alpha + logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) := by omega
      have hcast : (i : ENat) + (logSlack c_def (n + delta + d) : ENat) ≤ (alpha : ENat) + (logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) : ENat) := by
        exact_mod_cast hnat
      exact hcast
    exact le_trans h_le1 h_le2
  · refine hoptB.mono_beta ?_
    omega

theorem restricted_improving_descriptions_conditional (U : Map) (hU : IsOptimalPrefixConditional U) (𝒜 : DescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsIn 𝒜.toPre U x i j k →
      k ≤ i →
      InDescriptionProfileIn 𝒜 U x (i - k + logSlack c (n + i + j)) (j + logSlack c (n + i + j)) := by
  obtain ⟨c, hc⟩ := exists_familyComplexityRefinedSet U hU 𝒜
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hmemS, hxS, hcomp, hcard⟩ := hc x n i j k hn hmany hk
  refine ⟨S, hS, hmemS, hxS, hcomp, hcard⟩

end Kolmogorov
