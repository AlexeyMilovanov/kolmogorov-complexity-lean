import KolmogorovMathlib.Restricted.Improving
import KolmogorovMathlib.Restricted.GapCountingIn
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Deficiencies
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems

/-!
# Restricted Deficiency Equivalence
-/

namespace Kolmogorov
open CodedFiniteDistribution
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
  use (KPPlain_toNat_le_setComplexity_add_condKP U hU).choose + (KP_le_KPPlain U hU).choose +
      (KPPlain_le_length_add_log U hU).choose + 100;
  intro A hA x n alpha beta hn hcompA hdefA
  obtain ⟨i, hi⟩ : ∃ i : ℕ, setComplexity U A hA = (i : ENat) ∧ i ≤ alpha := by
    cases h : setComplexity U A hA <;> aesop
  obtain ⟨j, hj_lower, hj_upper⟩ : ∃ j : ℕ,
      (2 : ℝ≥0∞) ^ j / 2 ≤ (A.card : ℝ≥0∞) ∧ A.card ≤ 2 ^ j := by
    convert exists_card_dyadic_bracket A hA using 1
  set kx := (KPPlain U x).toNat
  have hkx_eq : (kx : ENat) = KPPlain U x := by
    exact ENat.natCast_toNat ( KPPlain_ne_top_of_optimal U hU x )
  set delta := i + j - kx
  have h_realized : RealizedSetOptimalityGap U A hA x delta i j kx := by
    have h_mass_pos : (codedUniformOn A hA).mass x > 0 := by
      apply mass_pos_of_deficiencyLe_of_KP_ne_top hdefA (KP_ne_top_of_optimal U hU x
          (codedUniformOn A hA).code);
    exact ⟨ by contrapose! h_mass_pos; rw [ codedUniformOn_mass_of_not_mem ] ; aesop, hi.1,
        hj_upper, hj_lower, hkx_eq, rfl ⟩
  have h_def_soi : CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x (delta +
      (KPPlain_toNat_le_setComplexity_add_condKP U hU).choose) := by
    have := Exists.choose_spec (KPPlain_toNat_le_setComplexity_add_condKP U hU) A hA x (by
    exact h_realized.1)
    generalize_proofs at *;
    unfold CodedFiniteDistribution.DeficiencyLe;
    rw [ codedUniformOn_mass_of_mem A hA x h_realized.1 ];
    rw [ ← ENat.natCast_toNat (KP_ne_top_of_optimal U hU x (codedUniformOn A hA).code) ];
    refine le_trans ?_ ( mul_le_mul_right ( show ( A.card : ENNReal ) ⁻¹ ≥ ( 2 ^ j : ENNReal )
        ⁻¹ from ?_ ) _ );
    · rw [ show delta = i + j - kx from rfl,
        show kx = ( KPPlain U x ).toNat from rfl ] at * ; norm_cast at *
      simp_all +decide only [Nat.cast_le, KPPlain_eq_KP, ENat.natCast_toNat_eq_self, ne_eq,
        ENat.toNat_natCast, Nat.cast_pow, Nat.cast_ofNat, complexityWeight_coe]
      rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
      · field_simp;
        rw [ div_pow, div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast <;> norm_num [ pow_add,
            pow_mul ];
        rw [ ← pow_add, ← pow_add ];
        exact pow_le_pow_right₀ ( by decide ) ( by omega );
      · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
    · gcongr ; norm_cast
  set d := min beta (delta + (KPPlain_toNat_le_setComplexity_add_condKP U hU).choose)
  have h_def_d : CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d := by
    grind;
  have h_j_bound : j ≤ (KP U x (codedUniformOn A hA).code).toNat + beta + 1 := by
    obtain ⟨j', hj'_card, hj'_le⟩ : ∃ j' : ℕ,
        A.card ≤ 2 ^ j' ∧ (j' : ENat) ≤ KP U x (codedUniformOn A hA).code + beta := by
      apply card_le_of_deficiency h_realized.left hdefA;
    have h_bound_j : j - 1 ≤ j' := by
      have h_bound_j : (2 : ℝ≥0∞) ^ j / 2 ≤ (2 : ℝ≥0∞) ^ j' := by
        exact le_trans hj_lower ( mod_cast hj'_card );
      convert dyadic_bracket_lower_bound h_bound_j using 1;
    cases h : KP U x ( codedUniformOn A hA ).code <;>
      simp_all +decide only [Nat.cast_le, KPPlain_eq_KP, top_add, le_top, tsub_le_iff_right,
        ENat.toNat_top, zero_add, ge_iff_le, ENat.toNat_natCast];
    · exact absurd h ( KP_ne_top_of_optimal U hU x _ );
    · norm_cast at * ; linarith;
  have h_kc_bound : (KP U x (codedUniformOn A hA).code).toNat ≤ n + 2 * (Nat.bits n).length +
      (KPPlain_le_length_add_log U hU).choose + (KP_le_KPPlain U hU).choose := by
    have hKP_le : KP U x (codedUniformOn A hA).code ≤ KPPlain U x + ((KP_le_KPPlain U
        hU).choose : ENat) := by
      grind
    have hKPP_le : KPPlain U x ≤ (n : ENat) + 2 * (Nat.bits n).length +
        ((KPPlain_le_length_add_log U hU).choose : ENat) := by
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
          ENat.toNat_le_toNat hle (ENat.natCast_ne_top _)
      _ = _ := ENat.toNat_natCast _
  have h_bits_length : (Nat.bits n).length ≤ n := length_natBits_le n
  refine ⟨ delta, i, j, kx, d, h_realized, h_def_d, ?_, ?_, ?_, ?_ ⟩ <;> omega

/-- The sets satisfying the predicate `mem` that have complexity at most `i` and at most `2 ^ j`
elements. -/
noncomputable def descriptionsWithComplexityLeAndSizeLeMem
    (mem : Finset BitString → Prop) (U : Map) (i j : ℕ) : Finset (Finset BitString) := by
  classical
  exact (descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => mem S)

/-- `x` has at least `2 ^ k` descriptions satisfying `mem` with complexity at most `i` and size
at most `2 ^ j`. -/
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

/-- The enumeration determined by a program is computable in the program and the stage. -/
theorem programmedEnum_computable : Computable (fun p_t : BitString × ℕ =>
    programmedEnum p_t.1 p_t.2) := by
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
  have h_dec : (Encodable.decode (α := Code) (Encodable.encode p_t.1)).getD Code.zero
      = Denumerable.ofNat Code (Encodable.encode p_t.1) := by rfl
  cases h : Code.evaln p_t.2
      ((Encodable.decode (α := Code) (Encodable.encode p_t.1)).getD Code.zero)
      (Encodable.encode p_t.2)
  · rw [h_dec] at h ⊢; simp_all []
  · rw [h_dec] at h ⊢; simp_all []

-- `programmedEnum` is now sealed: its computability is captured once in
-- `programmedEnum_computable`.  Keeping it reducible makes later `Computable.comp`
-- unifications unfold the `Code.evaln` body and blow up `whnf`; sealing it keeps
-- those elaborations fast while the structural (projection-level) `rfl`s below
-- still go through.
attribute [irreducible] programmedEnum

/-- `p` is a program for the family `mem`: the enumeration it drives is sound and complete for
the sets satisfying `mem`. -/
structure IsProgramForFamily (p : BitString) (mem : Finset BitString → Prop) : Prop where
  mono : ∀ t, programmedEnum p t <+: programmedEnum p (t + 1)
  sound : ∀ t, ∀ w ∈ programmedEnum p t, ∃ (S : Finset BitString) (hS : S.Nonempty),
      mem S ∧ w = (codedUniformOn S hS).code
  complete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S → ∃ t,
      (codedUniformOn S hS).code ∈ programmedEnum p t

/-- The description family enumerated by a program, packaged as a `PreDescriptionFamily`. -/
noncomputable def programmedFamily (p : BitString) (mem : Finset BitString → Prop)
    (hp : IsProgramForFamily p mem) : PreDescriptionFamily :=
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
    progAppearanceListCodes c i p j x = familyAppearanceListCodes c i (programmedFamily p mem
        hp) j x := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => simp only [progAppearanceListCodes, familyAppearanceListCodes, ih]; rfl

/-- Program-indexed index selector, using `progAppearanceListCodes`. -/
def progIndexSelectorFn (c : Code) (p : BitString) : BitString → BitString →. BitString :=
    fun y w =>
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
  have h_filter : Computable (fun p : List BitString × List BitString =>
      p.1.filter (fun w => decide (w ∈ p.2))) := by
    have h1 : Primrec₂ (fun (p : List BitString × List BitString) (w : BitString) =>
      decide (w ∈ p.2)) := bitString_mem_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
    exact (list_filter_primrec (f := fun (p : List BitString × List BitString) => p.1)
      Primrec.fst h1).to_comp
  have hcand : Computable (fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ =>
      candidateCodes c q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.2) := by
    refine ((candidateCodes_primrec c).to_comp.comp (Computable.pair
      (Computable.pair (Computable.pair
        (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
        (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))))
        (Computable.snd.comp (Computable.fst.comp Computable.fst)))
      Computable.snd)).of_eq ?_
    intro q; rfl
  have henum : Computable (fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ =>
      programmedEnum q.1.2 q.2) := by
    refine (programmedEnum_computable.comp
      (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)).of_eq ?_
    intro q; rfl
  refine (h_filter.comp (Computable.pair hcand henum)).of_eq ?_
  intro q; rfl

/-- Joint computability of the program-indexed appearance list. -/
theorem progAppearanceListCodes_computable (c : Code) :
    Computable (fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ =>
      progAppearanceListCodes c q.1.1.1.1 q.1.2 q.1.1.1.2 q.1.1.2 q.2) := by
  have h_eraseDups : Computable (fun l : List BitString => l.eraseDups) :=
    eraseDups_bitstring_primrec.to_comp
  have hg : Computable (fun q : (((ℕ × ℕ) × BitString) × BitString) × ℕ =>
      (progCandidateCodes c q.1.1.1.1 q.1.2 q.1.1.1.2 q.1.1.2 0).eraseDups) := by
    refine (h_eraseDups.comp ((progCandidateCodes_computable c).comp
      (Computable.pair Computable.fst (Computable.const 0)))).of_eq ?_
    intro q; rfl
  have hh : Computable₂ (fun (q : (((ℕ × ℕ) × BitString) × BitString) × ℕ)
      (r : ℕ × List BitString) =>
      (r.2 ++ progCandidateCodes c q.1.1.1.1 q.1.2 q.1.1.1.2 q.1.1.2 (r.1 + 1)).eraseDups) := by
    refine (h_eraseDups.comp (Computable.list_append.comp
      (Computable.snd.comp (Computable.snd
        (α := (((ℕ × ℕ) × BitString) × BitString) × ℕ) (β := ℕ × List BitString)))
      ((progCandidateCodes_computable c).comp
        (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.succ.comp (Computable.fst.comp Computable.snd)))))).of_eq ?_
    intro q; rfl
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
  have h_appearance : Computable (fun n : (BitString × BitString) × ℕ =>
      progAppearanceListCodes c (selNat (decodeSecond n.1.1)) (decodeFirst n.1.1)
        (selAlpha (decodeSecond n.1.1)) (decodeFirst n.1.2) n.2) :=
    ((progAppearanceListCodes_computable c).comp
      (Computable.pair
        (Computable.pair
          (Computable.pair
            (Computable.pair
              (selNat_primrec.to_comp.comp
                (decodeSecond_primrec.to_comp.comp (Computable.fst.comp Computable.fst)))
              (selAlpha_primrec.to_comp.comp
                (decodeSecond_primrec.to_comp.comp (Computable.fst.comp Computable.fst))))
            (decodeFirst_primrec.to_comp.comp (Computable.snd.comp Computable.fst)))
          (decodeFirst_primrec.to_comp.comp (Computable.fst.comp Computable.fst)))
        Computable.snd)).of_eq fun _ => rfl
  refine Partrec.bind ?_ ?_;
  · refine Partrec.of_eq
      (f := fun n : BitString × BitString => Nat.rfind fun t => Part.some
        (decide (selH (decodeSecond n.1) <
          (progAppearanceListCodes c (selNat (decodeSecond n.1))
            (decodeFirst n.1) (selAlpha (decodeSecond n.1))
            (decodeFirst n.2) t).length))) ?_ ?_;
    · refine Partrec.rfind ?_;
      refine Computable.of_eq
        (f := fun n : (BitString × BitString) × ℕ =>
          decide (selH (decodeSecond n.1.1) <
            (progAppearanceListCodes c (selNat (decodeSecond n.1.1))
              (decodeFirst n.1.1) (selAlpha (decodeSecond n.1.1))
              (decodeFirst n.1.2) n.2).length)) ?_ ?_;
      · have h_len : Computable (fun (n : ((BitString × BitString) × ℕ)) =>
          (progAppearanceListCodes c (selNat (decodeSecond n.1.1)) (decodeFirst n.1.1)
            (selAlpha (decodeSecond n.1.1)) (decodeFirst n.1.2) n.2).length) :=
          Computable.list_length.comp h_appearance
        have h_selH : Computable (fun (n : ((BitString × BitString) × ℕ)) =>
            selH (decodeSecond n.1.1)) := by
          exact selH_primrec.to_comp.comp ( decodeSecond_primrec.to_comp.comp (
              Computable.fst.comp ( Computable.fst ) ) );
        have h_pair : Computable (fun (n : ((BitString × BitString) × ℕ)) =>
            (selH (decodeSecond n.1.1), (progAppearanceListCodes c
              (selNat (decodeSecond n.1.1)) (decodeFirst n.1.1)
              (selAlpha (decodeSecond n.1.1)) (decodeFirst n.1.2) n.2).length)) :=
          Computable.pair h_selH h_len
        have h_lt : Computable (fun (n : ℕ × ℕ) => decide (n.1 < n.2)) :=
          (PrimrecPred.decide (PrimrecRel.comp Primrec.nat_lt Primrec.fst Primrec.snd)).to_comp
        convert h_lt.comp h_pair using 1;
      · exact fun _ => rfl;
    · exact fun _ => rfl;
  · refine Partrec.comp ?_ ?_;
    · exact Computable.id;
    · refine Computable.of_eq
        (f := fun n : (BitString × BitString) × ℕ =>
          List.headI (List.drop (selH (decodeSecond n.1.1))
            (progAppearanceListCodes c (selNat (decodeSecond n.1.1))
              (decodeFirst n.1.1) (selAlpha (decodeSecond n.1.1))
              (decodeFirst n.1.2) n.2))) ?_ ?_;
      · have h_drop : Computable (fun (n : ℕ × List BitString) => List.drop n.1 n.2) :=
          Primrec.list_drop.to_comp.comp Computable.fst Computable.snd
        have h_head : Computable (fun (l : List BitString) => l.headI) := by
          convert Primrec.list_headI.to_comp using 1;
        convert h_head.comp ( h_drop.comp ( Computable.pair _ _ ) ) using 1;
        · exact selH_primrec.to_comp.comp ( decodeSecond_primrec.to_comp.comp (
            Computable.fst.comp ( Computable.fst.comp Computable.id ) ) );
        · exact h_appearance
      · intro n
        cases h : List.drop (selH (decodeSecond n.1.1))
            (progAppearanceListCodes c (selNat (decodeSecond n.1.1))
              (decodeFirst n.1.1) (selAlpha (decodeSecond n.1.1))
              (decodeFirst n.1.2) n.2) with
        | nil =>
            simp []
            rfl
        | cons _ _ => simp []

/-- Uniform family rank lemma. -/
theorem uniform_description_count_of_conditional_complexity_gap (U : Map)
    (hU : IsOptimalPrefixConditional U) :
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
      KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤ (m + logSlack c (n + i
          + j) + KPPlain U p : ENat) := by
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
  have h_bound1 : KP U code y ≤ KP U (pairCode p w) y + (c_kp : ENat) :=
      hkp (pairCode p w) code y h_in
  have h_bound2 : KP U (pairCode p w) y ≤ KPPlain U (pairCode p w) + (c_plain : ENat) :=
    hc_plain (pairCode p w) y
  have h_bound3 : KPPlain U (pairCode p w) ≤ KPPlain U p + KPPlain U w + (c_pair : ENat) :=
    hc_pair p w
  have h_bound4 : KPPlain U w ≤ (w.length : ENat) + 2 * (Nat.bits w.length).length + c_len :=
      hc_len w
  have h_w_len_r : w.length ≤ 2 * (Nat.bits i).length + 2 * (Nat.bits j).length + (Nat.bits
      r).length + 6 := by
    unfold w richInput selectorInput pack4
    simp [length_pairCode]
    omega
  have hr_lt_2m : r < 2 ^ m :=
    lt_trans hr_lt (familyAppearanceListCodes_length_lt_of_not_manyIJIn hc_opt h_not_in t₀)
  have hr_lt_2i : r < 2 ^ (i + 1) :=
    lt_of_lt_of_le hr_lt (familyAppearanceListCodes_length_le_two_pow_i hc_opt 𝒜 i j x t₀)
  set M := n + i + j with hM
  have h_w_len_M : w.length ≤ 3 * M + 7 := by
    have hi_len : (Nat.bits i).length ≤ i := length_natBits_le i
    have hj_len : (Nat.bits j).length ≤ j := length_natBits_le j
    have hr_len : (Nat.bits r).length ≤ i + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr hr_lt_2i
    omega
  have h_r_m : (Nat.bits r).length ≤ m := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hr_lt_2m
  have h_slack : c_kp + c_plain + c_pair + c_len + 2 * (Nat.bits i).length + 2 * (Nat.bits
      j).length + 6 + 2 * (Nat.bits w.length).length ≤ logSlack C1 M := by
    have hw1 : (Nat.bits w.length).length ≤ (Nat.bits (3 * M + 7)).length := by
      have h : w.length < 2 ^ (Nat.size (3 * M + 7)) :=
          lt_of_le_of_lt h_w_len_M (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hw3 : 2 * (Nat.bits (3 * M + 7)).length ≤ logSlack 2 (3 * M + 7) :=
        by unfold logSlack; omega
    have hw5 : logSlack C2 M = C2 * (Nat.bits M).length + C2 := rfl
    have hw6 : logSlack C1 M = (C2 + c_kp + c_plain + c_pair + c_len + 6) * (Nat.bits
        M).length + (C2 + c_kp + c_plain + c_pair + c_len + 6) := rfl
    have hiM : i ≤ M := by omega
    have hjM : j ≤ M := by omega
    have hi_len : (Nat.bits i).length ≤ (Nat.bits M).length := by
      have h : i < 2 ^ (Nat.size M) := lt_of_le_of_lt hiM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hj_len : (Nat.bits j).length ≤ (Nat.bits M).length := by
      have h : j < 2 ^ (Nat.size M) := lt_of_le_of_lt hjM (Nat.lt_size_self _)
      simpa [← Nat.size_eq_bits_len] using Nat.size_le.mpr h
    have hC2_M := hC2 M
    have h_ring : (C2 + c_kp + c_plain + c_pair + c_len + 6) * (Nat.bits M).length +
        (C2 + c_kp + c_plain + c_pair + c_len + 6) =
        (C2 * (Nat.bits M).length + C2) + c_kp * (Nat.bits M).length +
        c_plain * (Nat.bits M).length + c_pair * (Nat.bits M).length +
        c_len * (Nat.bits M).length + 6 * (Nat.bits M).length +
        (c_kp + c_plain + c_pair + c_len + 6) := by ring
    rw [hw6, h_ring, ← hw5]
    omega
  have hnat : w.length + 2 * (Nat.bits w.length).length + c_len + (c_pair + c_plain + c_kp)
      ≤ m + logSlack C1 M := by omega
  calc KP U code y ≤ KP U (pairCode p w) y + c_kp := h_bound1
    _ ≤ KPPlain U (pairCode p w) + c_plain + c_kp := by gcongr
    _ ≤ (KPPlain U p + KPPlain U w + c_pair) + c_plain + c_kp := by gcongr
    _ = KPPlain U p + (KPPlain U w + (c_pair + c_plain + c_kp : ℕ)) := by push_cast; ring
    _ ≤ KPPlain U p + (((w.length : ENat) + 2 * (Nat.bits w.length).length + c_len)
          + (c_pair + c_plain + c_kp : ℕ)) := by gcongr
    _ = KPPlain U p + ((w.length + 2 * (Nat.bits w.length).length + c_len + (c_pair + c_plain
        + c_kp) : ℕ) : ENat) := by
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
  | t + 1 =>
      (progStageModelCodesList c i p j t ++ progCandidateModelCodesList c i p j (t + 1)).eraseDups

/-- Program-indexed marked-code stream, using `programmedEnum p`. -/
def progMarkedCodeStream (c : Code) (i : ℕ) (p : BitString) (n j k t : ℕ) : List BitString :=
  selectionStrategyOnline n i j k (progStageModelCodesList c i p j t)

/-- The stage model codes computed from a program agree with those of the family it enumerates. -/
theorem progStageModelCodesList_eq_family (c : Code) (i : ℕ) (p : BitString)
    (mem : Finset BitString → Prop) (hp : IsProgramForFamily p mem) (j : ℕ) :
    progStageModelCodesList c i p j = familyStageModelCodesList c i (programmedFamily p mem
        hp) j := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => simp only [progStageModelCodesList, familyStageModelCodesList, ih]; rfl

/-- The marked code stream computed from a program agrees with that of the family it enumerates. -/
theorem progMarkedCodeStream_eq_family (c : Code) (i : ℕ) (p : BitString)
    (mem : Finset BitString → Prop) (hp : IsProgramForFamily p mem) (n j k t : ℕ) :
    progMarkedCodeStream c i p n j k t = familyMarkedCodeStream c i (programmedFamily p mem
        hp) n j k t := by
  unfold progMarkedCodeStream familyMarkedCodeStream
  rw [progStageModelCodesList_eq_family c i p mem hp j]

end Kolmogorov
