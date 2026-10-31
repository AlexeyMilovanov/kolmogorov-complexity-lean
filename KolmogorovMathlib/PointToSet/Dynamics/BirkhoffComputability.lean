/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.ComputableMetric
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.AlgorithmicRandomness.ProbabilityBounded
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.TopologicalEntropy.DynamicalEntourage
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Computable Birkhoff sums and Bowen distances

For an admissible oracle, Birkhoff sums and finite orbit distances at ideal points
have uniform rational approximations (blueprint node `metric:birkhoff`). We construct
computable Cauchy names for the orbits, evaluate the represented potentials on those
names, and control the errors in finite sums and maxima.

This module also defines `bowenDist` and `bowenBall`, used by the Bowen topology results
in `Dynamics.BowenBalls` (blueprint node `metric:bowen`). The computability results supply
the effective orbit data used in the pointwise pressure and presentation comparison
arguments.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- The finite orbit distance is the maximum of distances at times strictly below `n`;
the empty maximum is zero. Blueprint node `metric:birkhoff`. -/
noncomputable def bowenDist (T : X → X) (n : ℕ) (x y : X) : ℝ :=
  ↑((Finset.range n).sup (fun k ↦ nndist (T^[k] x) (T^[k] y)))

/-- A Bowen ball is the section of Mathlib's dynamical entourage at its center. In
particular its order-zero value is the whole space. Blueprint node `metric:bowen`. -/
def bowenBall (T : X → X) (n : ℕ) (x : X) (ε : ℝ) : Set X :=
  {y | (x, y) ∈ _root_.Dynamics.dynEntourage T {z : X × X | dist z.1 z.2 < ε} n}

/-- Constant functions have oracle program indices computable uniformly in their values. -/
private lemma exists_constant_oracle_indices
    (A : Set ℕ) :
    ∃ c : ℕ → ℕ, Computable c ∧
      ∀ i p, oracleEval A (c i) p = Part.some i := by
  classical
  let c : ℕ → ℕ := fun i ↦
    Encodable.encode (Nat.Partrec.Code.const i)
  refine ⟨c, (Primrec.encode.comp
    Nat.Partrec.Code.primrec_const).to_comp, ?_⟩
  intro i p
  have hs : ∀ t w, oracleStage A t (c i) p = some w → w = i := by
    intro t w hw
    unfold oracleStage at hw
    obtain ⟨r, _, hr⟩ := List.exists_of_findSome?_eq_some hw
    have hm := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hr)
    simpa only [c, Denumerable.ofNat_encode,
      Nat.Partrec.Code.eval_const, Part.mem_some_iff] using hm
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp
    (show i ∈ Nat.Partrec.Code.eval (Nat.Partrec.Code.const i)
      (Encodable.encode (([] : List ℕ), p)) by simp)
  have hex : ∃ t, oracleStage A t (c i) p = some i := by
    let t := Nat.pair 0 k + 1
    cases ht : oracleStage A t (c i) p with
    | none =>
      unfold oracleStage at ht
      have hn := List.findSome?_eq_none_iff.mp ht
        (Nat.pair 0 k)
        (List.mem_range.mpr (Nat.lt_succ_self _))
      simp only [c, Denumerable.ofNat_encode,
        Nat.unpair_pair, List.range_zero, List.map_nil] at hn
      have hk' := Option.mem_def.mp hk
      rw [hk'] at hn
      contradiction
    | some w =>
      have hw := hs t w ht
      subst w
      exact ⟨t, ht⟩
  apply Part.eq_some_iff.mpr
  change i ∈ Nat.rfindOpt (fun t ↦ oracleStage A t (c i) p)
  apply (Nat.rfindOpt_mono (fun {a m n} hmn ha ↦
    Option.mem_def.mpr (oracleStage_persistent A (c i) p a m n
      hmn (Option.mem_def.mp ha)))).mpr
  obtain ⟨t, ht⟩ := hex
  exact ⟨t, Option.mem_def.mpr ht⟩

/-- A relative partial computation admits computable specialization of its first argument. -/
private lemma exists_oracle_specialization
    (A : Set ℕ) (E : ℕ × ℕ →. ℕ) (hE : PartrecIn {charOracle A} E) :
    ∃ s : ℕ → ℕ, Computable s ∧
      ∀ e p, oracleEval A (s e) p = E (e, p) := by
  classical
  let f : ℕ →. ℕ := fun z ↦ E (Nat.unpair z)
  have hf : PartrecIn {charOracle A} f := hE.comp Computable.unpair.computableIn
  obtain ⟨Φ, hΦ, _, hex⟩ :=
    exists_exact_string_operator (fun j ↦ if j ∈ A then 1 else 0) f hf
  let g : ℕ →. ℕ := fun z ↦
    (Part.ofOption (Encodable.decode (α := List ℕ × ℕ) z.unpair.2)).bind
      (fun q ↦ Φ (q.1, Nat.pair z.unpair.1 q.2))
  have hg : Nat.Partrec g := by
    apply Partrec.nat_iff.mp
    have hdecode : Partrec (fun z : ℕ ↦
        Part.ofOption (Encodable.decode (α := List ℕ × ℕ) z.unpair.2)) :=
      Computable.ofOption (Computable.decode.comp (Computable.snd.comp Computable.unpair))
    have hargs : Computable (fun zq : ℕ × (List ℕ × ℕ) ↦
        (zq.2.1, Nat.pair zq.1.unpair.1 zq.2.2)) :=
      (Computable.fst.comp Computable.snd).pair
        (((Computable.fst.comp Computable.unpair).comp Computable.fst).pair
          (Computable.snd.comp Computable.snd))
    exact Partrec.bind hdecode (hΦ.comp hargs)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  obtain ⟨smn, hsmn, heval⟩ := Nat.Partrec.Code.smn
  let s : ℕ → ℕ := fun e ↦ Encodable.encode (smn c e)
  refine ⟨s, Computable.encode.comp (hsmn.comp (Computable.const c) Computable.id), ?_⟩
  intro e p
  have hcode (pref : List ℕ) (v : ℕ) :
      v ∈ Φ (pref, Nat.pair e p) ↔
        ∃ k, Nat.Partrec.Code.evaln k (Denumerable.ofNat Nat.Partrec.Code (s e))
          (Encodable.encode (pref, p)) = some v := by
    have heq : (smn c e).eval (Encodable.encode (pref, p)) =
        Φ (pref, Nat.pair e p) := by
      rw [heval, hc]
      simp [g]
    simpa only [s, Denumerable.ofNat_encode, heq, Option.mem_def] using
      (@Nat.Partrec.Code.evaln_complete (smn c e) (Encodable.encode (pref, p)) v)
  have hstage (v : ℕ) : v ∈ oracleEval A (s e) p ↔
      ∃ t, oracleStage A t (s e) p = some v :=
    Nat.rfindOpt_mono (fun hts ha ↦ oracleStage_persistent A (s e) p _ _ _ hts ha)
  have hmem (u k v : ℕ)
      (h : Nat.Partrec.Code.evaln k (Denumerable.ofNat Nat.Partrec.Code (s e))
        (Encodable.encode ((List.range u).map (fun j ↦ if j ∈ A then 1 else 0), p)) =
          some v) : v ∈ E (e, p) := by
    have hv := (hex (Nat.pair e p) v).mpr ⟨u, (hcode _ v).mpr ⟨k, h⟩⟩
    simpa only [f, Nat.unpair_pair] using hv
  apply Part.ext
  intro v
  rw [hstage]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨r, _, hr⟩ := List.exists_of_findSome?_eq_some ht
    exact hmem r.unpair.1 r.unpair.2 v hr
  · intro hv
    have hvf : v ∈ f (Nat.pair e p) := by
      simpa only [f, Nat.unpair_pair] using hv
    obtain ⟨u, hu⟩ := (hex (Nat.pair e p) v).mp hvf
    obtain ⟨k, hk⟩ := (hcode _ v).mp hu
    refine ⟨Nat.pair u k + 1, ?_⟩
    cases ht : oracleStage A (Nat.pair u k + 1) (s e) p with
    | none =>
      have hn := List.findSome?_eq_none_iff.mp ht (Nat.pair u k)
        (List.mem_range.mpr (Nat.lt_succ_self _))
      simp only [Nat.unpair_pair] at hn
      rw [hk] at hn
      contradiction
    | some w =>
      obtain ⟨r, _, hr⟩ := List.exists_of_findSome?_eq_some ht
      exact congrArg some (Part.mem_unique (hmem r.unpair.1 r.unpair.2 w hr) hv)

/-- Computable initialization and update functions give computable iteration indices. -/
private lemma exists_iterate_indices
    (c s : ℕ → ℕ) (hc : Computable c) (hs : Computable s) :
    ∃ e : ℕ × ℕ → ℕ, Computable (fun p : ℕ × ℕ ↦ e p) ∧
      (∀ i, e (0, i) = c i) ∧
      (∀ n i, e (n + 1, i) = s (e (n, i))) := by
  let e (n i : ℕ) : ℕ := Nat.rec (motive := fun _ ↦ ℕ) (c i) (fun _ IH ↦ s IH) n
  use fun p ↦ e p.1 p.2
  refine ⟨?_, ?_, ?_⟩
  · exact Computable.nat_rec Computable.fst (hc.comp Computable.snd)
      (hs.comp (Computable.snd.comp Computable.snd)).to₂
  · intro i; rfl
  · intro n i; rfl

/-- Iterating indices for a represented map produces valid names for its orbit points. -/
private lemma isCauchyName_of_iterate_indices
    (P : Presentation X) (T : X → X) (A : Set ℕ)
    (E : ℕ × ℕ →. ℕ)
    (hE : ∀ x a e, IsCauchyName P x a → (∀ p, a p ∈ oracleEval A e p) →
      ∀ p, ∃ i, i ∈ E (e, p) ∧ dist (P.ι i) (T x) < dyadicRadius p)
    (c s : ℕ → ℕ)
    (hc : ∀ i p, oracleEval A (c i) p = Part.some i)
    (hs : ∀ e p, oracleEval A (s e) p = E (e, p))
    (e : ℕ × ℕ → ℕ)
    (h_base : ∀ i, e (0, i) = c i)
    (h_step : ∀ n i, e (n + 1, i) = s (e (n, i))) :
    ∀ n i, ∃ a : ℕ → ℕ, IsCauchyName P (T^[n] (P.ι i)) a ∧
      ∀ p, a p ∈ oracleEval A (e (n, i)) p := by
  intro n i
  induction n with
  | zero =>
    use fun _ ↦ i
    constructor
    · intro p
      rw [Function.iterate_zero, id_eq]
      rw [dist_self]
      unfold dyadicRadius
      positivity
    · intro p
      rw [h_base]
      rw [hc i p]
      exact Part.mem_some i
  | succ n ih =>
    obtain ⟨a_n, h_cauchy_n, h_mem_n⟩ := ih
    have h_next : ∀ p, ∃ i_next, i_next ∈ E (e (n, i), p) ∧
        dist (P.ι i_next) (T (T^[n] (P.ι i))) < dyadicRadius p := by
      intro p
      apply hE (T^[n] (P.ι i)) a_n (e (n, i)) h_cauchy_n h_mem_n p
    choose a_next h_next_mem h_next_dist using h_next
    use a_next
    constructor
    · intro p
      rw [Function.iterate_succ_apply']
      exact h_next_dist p
    · intro p
      rw [h_step]
      rw [hs]
      exact h_next_mem p

/-- A computable family of total oracle programs gives a uniformly computable family of names. -/
private lemma computable_names_of_total_oracle_indices
    (A : Set ℕ) (e : ℕ × ℕ → ℕ) (hcomp : Computable (fun p : ℕ × ℕ ↦ e p))
    (htotal : ∀ n i p, (oracleEval A (e (n, i)) p).Dom) :
    ∃ a : (ℕ × ℕ) → ℕ → ℕ,
      ComputableIn {charOracle A} (fun z : (ℕ × ℕ) × ℕ ↦ a z.1 z.2) ∧
      ∀ n i p, a (n, i) p ∈ oracleEval A (e (n, i)) p := by
  let f : (ℕ × ℕ) × ℕ → ℕ := fun z ↦ (oracleEval A (e z.1) z.2).get (htotal z.1.1 z.1.2 z.2)
  have hf : ComputableIn {charOracle A} f := by
    have hargs : ComputableIn {charOracle A}
        (fun z : (ℕ × ℕ) × ℕ ↦ (e z.1, z.2)) :=
      (hcomp.computableIn.comp ComputableIn.fst).pair ComputableIn.snd
    apply PartrecIn.of_eq ((oracleStage_evaluator A).comp hargs)
    intro z
    exact (Part.some_get (htotal z.1.1 z.1.2 z.2)).symm
  use fun ni p ↦ f (ni, p)
  exact ⟨hf, fun n i p ↦ Part.get_mem (htotal n i p)⟩

/-- Ideal-point orbits have Cauchy names computable uniformly in time, center and precision. -/
private theorem exists_computable_orbit_names
    (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A)
    (hT : IsRepresentedMapIn P P A T) :
    ∃ a : (ℕ × ℕ) → ℕ → ℕ,
      ComputableIn {charOracle A} (fun z : (ℕ × ℕ) × ℕ ↦ a z.1 z.2) ∧
      ∀ n i, IsCauchyName P (T^[n] (P.ι i)) (a (n, i)) := by
  have ⟨E, hE, hE_sound⟩ := eval_computable_names_uniform P P A hP hP T hT
  obtain ⟨c, hc_comp, hc⟩ := exists_constant_oracle_indices A
  obtain ⟨s, hs_comp, hs⟩ := exists_oracle_specialization A E hE
  obtain ⟨e, he_comp, he_base, he_step⟩ := exists_iterate_indices c s hc_comp hs_comp
  have H_sound := isCauchyName_of_iterate_indices P T A E hE_sound c s hc hs e he_base he_step
  have H_total : ∀ n i p, (oracleEval A (e (n, i)) p).Dom := by
    intro n i p
    obtain ⟨a, _, ha2⟩ := H_sound n i
    exact Part.dom_iff_mem.mpr ⟨a p, ha2 p⟩
  obtain ⟨a, ha_comp, ha_sound⟩ := computable_names_of_total_oracle_indices A e he_comp H_total
  use a, ha_comp
  intro n i
  obtain ⟨a', ha'_cauchy, ha'_mem⟩ := H_sound n i
  have H_eq : a (n, i) = a' := by
    ext p
    exact Part.mem_unique (ha_sound n i p) (ha'_mem p)
  rwa [H_eq]

/-- A uniformly computable family of names has an ordinarily computable family of oracle indices. -/
private theorem exists_oracle_indices_for_names
    (A : Set ℕ) (a : (ℕ × ℕ) → ℕ → ℕ)
    (hacomp : ComputableIn {charOracle A}
      (fun z : (ℕ × ℕ) × ℕ ↦ a z.1 z.2)) :
    ∃ e : (ℕ × ℕ) → ℕ, Computable e ∧
      ∀ u p, a u p ∈ oracleEval A (e u) p := by
  let E : ℕ × ℕ →. ℕ := fun rp ↦ Part.some (a (Nat.unpair rp.1) rp.2)
  have hE : PartrecIn {charOracle A} E := by
    have h1 : ComputableIn {charOracle A} (fun rp : ℕ × ℕ ↦ (Nat.unpair rp.1, rp.2)) :=
      (Computable.unpair.computableIn.comp ComputableIn.fst).pair ComputableIn.snd
    have h2 : ComputableIn {charOracle A} (fun rp : ℕ × ℕ ↦ a (Nat.unpair rp.1) rp.2) :=
        hacomp.comp h1
    exact PartrecIn.comp PartrecIn.some h2
  have ⟨s, hs, hseq⟩ := exists_oracle_specialization A E hE
  use fun u ↦ s (Nat.pair u.1 u.2)
  constructor
  · exact hs.comp (Computable.pair Computable.fst Computable.snd)
  · intro u p
    have h_eq := hseq (Nat.pair u.1 u.2) p
    dsimp [E] at h_eq
    rw [Nat.unpair_pair] at h_eq
    exact h_eq.symm ▸ Part.mem_some _

/-- The rational decoding used by the real presentation is computable. -/
private lemma computable_decode_rat :
    Computable (fun n : ℕ ↦ (@Encodable.decode ℚ Rat.instEncodable n).getD 0) := by
  have hd : ∀ n : ℕ, (@Encodable.decode ℚ Rat.instEncodable n).getD 0 = ratOfCode n := by
    intro n
    by_cases hn : IsRatCode n
    · have he_eq : @Encodable.encode ℚ Rat.instEncodable (ratOfCode n) = n := ratCode_ratOfCode hn
      have hdec : @Encodable.decode ℚ Rat.instEncodable n = some (ratOfCode n) := by
        simpa only [he_eq] using (@Encodable.encodek ℚ Rat.instEncodable (ratOfCode n))
      simp only [hdec, Option.getD_some]
    · dsimp [ratOfCode]
      rw [ite_eq_right_iff.mpr (fun h ↦ False.elim (hn h))]
      unfold Rat.instEncodable
      rw [Encodable.decode_ofEquiv, Encodable.decode_sigma_val]
      have h1 : Encodable.decode (α := ℤ) (Nat.unpair n).1 =
          some (Denumerable.ofNat ℤ (Nat.unpair n).1) :=
        Denumerable.decode_eq_ofNat ℤ (Nat.unpair n).1
      rw [h1]
      dsimp
      have h_abs : (Denumerable.ofNat ℤ (Nat.unpair n).1).natAbs =
          ((Nat.unpair n).1 + 1) / 2 := int_natAbs_ofNat (Nat.unpair n).1
      have h2 : Encodable.decode
          (α := { d // 0 < d ∧ (Denumerable.ofNat ℤ (Nat.unpair n).1).natAbs.Coprime d })
          (Nat.unpair n).2 = none := by
        rw [h_abs]
        change (Encodable.decode (Nat.unpair n).2).bind
          (fun a ↦ if h : 0 < a ∧ (((Nat.unpair n).1 + 1) / 2).Coprime a
            then some (Subtype.mk a h) else none) = none
        have h4 : Encodable.decode (α := ℕ) (Nat.unpair n).2 = some (Nat.unpair n).2 :=
          Denumerable.decode_eq_ofNat ℕ (Nat.unpair n).2
        rw [h4]
        dsimp
        have h6 : ¬ (0 < (Nat.unpair n).2 ∧
            (((Nat.unpair n).1 + 1) / 2).Coprime (Nat.unpair n).2) := hn
        rw [dite_eq_right_iff.mpr (fun h ↦ False.elim (h6 h))]
      rw [h2]
      rfl
  exact computable_ratOfCode.of_eq (fun n ↦ (hd n).symm)

/-- The standard rational presentation of the reals is computable in every oracle. -/
private lemma computable_realPresentation (A : Set ℕ) :
    ComputablePresentationIn realPresentation A := by
  have habs : Computable (fun q : ℚ ↦ |q|) := by
    have h := Computable₂.comp ComputableReals.primrec_ratMax.to_comp
      (Computable.id : Computable (fun q : ℚ ↦ q)) ComputableReals.computable_ratNeg
    change Computable (fun a ↦ max a (-a)) at h
    simpa only [abs_eq_max_neg] using h
  let d : ℕ → ℚ := fun n ↦ (@Encodable.decode ℚ Rat.instEncodable n).getD 0
  have hdcomp : Computable d := computable_decode_rat
  let m : (ℕ × ℕ) × ℕ → ℚ := fun z ↦ |d z.1.1 - d z.1.2|
  have hmcomp : Computable m :=
    habs.comp (Computable₂.comp
      ComputableReals.computable_ratSub
      (hdcomp.comp (Computable.fst.comp Computable.fst))
      (hdcomp.comp (Computable.snd.comp Computable.fst)))
  change IsComputableRealFamilyIn A
    (fun ij : ℕ × ℕ ↦
      dist (realPresentation.ι ij.1) (realPresentation.ι ij.2))
  refine ⟨m, hmcomp.computableIn, ?_⟩
  intro ij p
  have hexact : (m (ij, p) : ℝ) =
      dist (realPresentation.ι ij.1) (realPresentation.ι ij.2) := by
    simp only [m, d, realPresentation,
      Rat.cast_abs, Rat.cast_sub, Real.dist_eq]
  rw [hexact, sub_self, abs_zero]
  have hd_pos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ p := by positivity
  exact hd_pos

/-- A represented real-valued map can be evaluated uniformly on computably indexed names. -/
private theorem computable_real_family_of_indexed_names
    {X : Type*} [MetricSpace X]
    (P : Presentation X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A)
    (f : X → ℝ) (hf : IsRepresentedMapIn P realPresentation A f)
    (x : (ℕ × ℕ) → X) (a : (ℕ × ℕ) → ℕ → ℕ)
    (e : (ℕ × ℕ) → ℕ) (he : Computable e)
    (ha : ∀ u, IsCauchyName P (x u) (a u))
    (hia : ∀ u p, a u p ∈ oracleEval A (e u) p) :
    IsComputableRealFamilyIn A (fun u ↦ f (x u)) := by
  let d : ℕ → ℚ := fun n ↦ (@Encodable.decode ℚ Rat.instEncodable n).getD 0
  have hdcomp : Computable d := computable_decode_rat
  have hReal := computable_realPresentation A
  have ⟨E, hE, hE_sound⟩ := eval_computable_names_uniform P realPresentation A hP hReal f hf
  have hE_dom : ∀ u p, (E (e u, p)).Dom := by
    intro u p
    have H := hE_sound (x u) (a u) (e u) (ha u) (hia u) p
    obtain ⟨i, hi, _⟩ := H
    exact Part.dom_iff_mem.mpr ⟨i, hi⟩
  let g : (ℕ × ℕ) × ℕ → ℕ := fun up ↦ (E (e up.1, up.2)).get (hE_dom up.1 up.2)
  have hg : ComputableIn {charOracle A} g := by
    have hE' : PartrecIn {charOracle A} (fun up : (ℕ × ℕ) × ℕ ↦ E (e up.1, up.2)) :=
      PartrecIn.comp hE (ComputableIn.pair (he.computableIn.comp ComputableIn.fst) ComputableIn.snd)
    have H : ∀ up, g up ∈ E (e up.1, up.2) := fun up ↦ Part.get_mem (hE_dom up.1 up.2)
    exact PartrecIn.of_eq_tot hE' H
  let q : (ℕ × ℕ) × ℕ → ℚ := fun up ↦ d (g up)
  have hq : ComputableIn {charOracle A} q := hdcomp.computableIn.comp hg
  use q
  constructor
  · exact hq
  · intro u p
    have H := hE_sound (x u) (a u) (e u) (ha u) (hia u) p
    obtain ⟨i, hi, hdist⟩ := H
    have H_g : g (u, p) = i := Part.mem_unique (Part.get_mem (hE_dom u p)) hi
    dsimp [q, d]
    rw [H_g]
    exact hdist

/-- Finitely many computable real families form a jointly computable family. -/
private theorem computable_real_family_fin
    {α : Type*} [Primcodable α] {k : ℕ}
    (A : Set ℕ) (F : Fin k → α → ℝ)
    (hF : ∀ j, IsComputableRealFamilyIn A (F j)) :
    IsComputableRealFamilyIn A
      (fun z : Fin k × α ↦ F z.1 z.2) := by
  have hfinite (s : Finset (Fin k)) : ∃ q : (Fin k × α) × ℕ → ℚ,
      ComputableIn {charOracle A} q ∧
      ∀ j ∈ s, ∀ x p, |(q ((j, x), p) : ℝ) - F j x| < (2 : ℝ)⁻¹ ^ p := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ ↦ 0, ComputableIn.const 0, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨qold, hqold, hqold_bound⟩ := ih
      obtain ⟨qi, hqi, hqi_bound⟩ := hF i
      let qnew : (Fin k × α) × ℕ → ℚ := fun z ↦
        bif decide (z.1.1 = i) then qi (z.1.2, z.2) else qold z
      have hguard : ComputableIn {charOracle A} (fun j : Fin k ↦ decide (j = i)) :=
        (Primrec.dom_finite (fun j : Fin k ↦ decide (j = i))).to_comp.computableIn
      have hcond : ComputableIn {charOracle A}
          (fun z : (Fin k × α) × ℕ ↦ decide (z.1.1 = i)) :=
        hguard.comp (ComputableIn.fst.comp ComputableIn.fst)
      have htrue : ComputableIn {charOracle A}
          (fun z : (Fin k × α) × ℕ ↦ qi (z.1.2, z.2)) :=
        hqi.comp ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd)
      have hqnew : ComputableIn {charOracle A} qnew := by
        apply PartrecIn.of_eq_tot (PartrecIn.cond hcond htrue.partrecIn hqold.partrecIn)
        intro z
        by_cases hz : z.1.1 = i <;> simp [qnew, hz]
      refine ⟨qnew, hqnew, ?_⟩
      intro j hj x p
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa [qnew] using hqi_bound x p
      · have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
        simpa [qnew, hji] using hqold_bound j hj x p
  obtain ⟨q, hq, hq_bound⟩ := hfinite Finset.univ
  exact ⟨q, hq, fun z p ↦ hq_bound z.1 (Finset.mem_univ z.1) z.2 p⟩

/-- A finite family of represented potentials can be evaluated uniformly on named orbits. -/
private theorem computable_potentials_of_orbit_names
    {k : ℕ} (P : Presentation X) (T : X → X) (v : Fin k → X → ℝ)
    (A : Set ℕ) (hP : ComputablePresentationIn P A)
    (hv : ∀ j, IsRepresentedMapIn P realPresentation A (v j))
    (a : (ℕ × ℕ) → ℕ → ℕ)
    (ha : ∀ n i, IsCauchyName P (T^[n] (P.ι i)) (a (n, i)))
    (hacomp : ComputableIn {charOracle A}
      (fun z : (ℕ × ℕ) × ℕ ↦ a z.1 z.2)) :
    IsComputableRealFamilyIn A
      (fun ji : Fin k × ℕ × ℕ ↦ v ji.1 (T^[ji.2.1] (P.ι ji.2.2))) := by
  obtain ⟨e, he_comp, he_eval⟩ := exists_oracle_indices_for_names A a hacomp
  have H_single : ∀ j, IsComputableRealFamilyIn A (fun u : ℕ × ℕ ↦ v j (T^[u.1] (P.ι u.2))) := by
    intro j
    exact computable_real_family_of_indexed_names P A hP (v j) (hv j)
      (fun (u : ℕ × ℕ) ↦ T^[u.1] (P.ι u.2)) a e he_comp (fun (u : ℕ × ℕ) ↦ ha u.1 u.2) he_eval
  have H_comp := computable_real_family_fin A (fun j (u : ℕ × ℕ) ↦ v j (T^[u.1] (P.ι u.2))) H_single
  exact H_comp

/-- Admissible potentials have uniformly computable values along ideal-point orbits. -/
private theorem computable_orbit_potentials {k : ℕ} (P : Presentation X)
    (T : X → X) (v : Fin k → X → ℝ) (A : Set ℕ)
    (hA : IsAdmissible P T v A) :
    IsComputableRealFamilyIn A
      (fun ji : Fin k × ℕ × ℕ ↦ v ji.1 (T^[ji.2.1] (P.ι ji.2.2))) := by
  rcases hA with ⟨hP, hT, hv⟩
  obtain ⟨a, hacomp, ha⟩ := exists_computable_orbit_names P T A hP hT
  exact computable_potentials_of_orbit_names P T v A hP hv a ha hacomp

/-- Rational partial sums with precision shifted by the summation length are computable. -/
private theorem computable_shifted_rat_sums
    {α β : Type*} [Primcodable α] [Primcodable β] (A : Set ℕ)
    (q : (α × ℕ × β) × ℕ → ℚ)
    (hq : ComputableIn {Kolmogorov.charOracle A} q) :
    ComputableIn {Kolmogorov.charOracle A}
      (fun z : (α × ℕ × β) × ℕ ↦
        Nat.rec (motive := fun _ ↦ ℚ) (0 : ℚ)
          (fun t ih ↦ ih + q ((z.1.1, t, z.1.2.2), z.2 + z.1.2.1 + 2))
          z.1.2.1) := by
  have hlength : Computable (fun z : (α × ℕ × β) × ℕ ↦ z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hprec : Computable (fun z : (α × ℕ × β) × ℕ ↦ z.2 + z.1.2.1 + 2) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable₂.comp Primrec.nat_add.to_comp Computable.snd hlength) (Computable.const 2)
  have hparams : Computable (fun z : ((α × ℕ × β) × ℕ) × (ℕ × ℚ) ↦ z.1.1) :=
    Computable.fst.comp Computable.fst
  have hquery : Computable (fun z : ((α × ℕ × β) × ℕ) × (ℕ × ℚ) ↦
      ((z.1.1.1, z.2.1, z.1.1.2.2), z.1.2 + z.1.1.2.1 + 2)) :=
    ((Computable.fst.comp hparams).pair
      ((Computable.fst.comp Computable.snd).pair
        (Computable.snd.comp (Computable.snd.comp hparams)))).pair
      (hprec.comp Computable.fst)
  have hacc : ComputableIn {charOracle A}
      (fun z : ((α × ℕ × β) × ℕ) × (ℕ × ℚ) ↦ z.2.2) :=
    (Computable.snd.comp Computable.snd).computableIn
  have hupdate : ComputableIn₂ {charOracle A}
      (fun (z : (α × ℕ × β) × ℕ) (p : ℕ × ℚ) ↦
        p.2 + q ((z.1.1, p.1, z.1.2.2), z.2 + z.1.2.1 + 2)) :=
    ComputableReals.computable_ratAdd.computableIn₂.comp hacc (hq.comp hquery.computableIn)
  exact ComputableIn.nat_rec hlength.computableIn (ComputableIn.const 0) hupdate

/-- Approximating each of `n` summands at precision `p + n + 2` gives precision `p` for the sum. -/
private theorem abs_sum_approx_lt
    {α β : Type*} (F : α → ℕ → β → ℝ) (q : (α × ℕ × β) × ℕ → ℚ)
    (hq_bound : ∀ (i : α × ℕ × β) (p : ℕ),
      |(q (i, p) : ℝ) - F i.1 i.2.1 i.2.2| < (2 : ℝ)⁻¹ ^ p) :
    ∀ (i : α × ℕ × β) (p : ℕ),
      |(∑ t ∈ Finset.range i.2.1, (q ((i.1, t, i.2.2), p + i.2.1 + 2) : ℝ)) -
        ∑ t ∈ Finset.range i.2.1, F i.1 t i.2.2| < (2 : ℝ)⁻¹ ^ p := by
  intro x p
  rw [← Finset.sum_sub_distrib]
  have h_le := Finset.abs_sum_le_sum_abs
    (fun t ↦ (q ((x.1, t, x.2.2), p + x.2.1 + 2) : ℝ) - F x.1 t x.2.2)
    (Finset.range x.2.1)
  by_cases h_n : x.2.1 = 0
  · rw [h_n, Finset.range_zero]
    simp only [Finset.sum_empty, abs_zero]
    positivity
  have h_lt : ∑ t ∈ Finset.range x.2.1, |(q ((x.1, t, x.2.2), p + x.2.1 + 2) : ℝ) - F x.1 t x.2.2| <
      ∑ t ∈ Finset.range x.2.1, (2 : ℝ)⁻¹ ^ (p + x.2.1 + 2) := by
    apply Finset.sum_lt_sum_of_nonempty
    · rw [Finset.nonempty_range_iff]
      exact h_n
    · intro i _
      exact hq_bound (x.1, i, x.2.2) (p + x.2.1 + 2)
  have h_sum_eq : ∑ _ ∈ Finset.range x.2.1, (2 : ℝ)⁻¹ ^ (p + x.2.1 + 2) =
      x.2.1 * (2 : ℝ)⁻¹ ^ (p + x.2.1 + 2) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [h_sum_eq] at h_lt
  have h_bound : (x.2.1 : ℝ) * (2 : ℝ)⁻¹ ^ (p + x.2.1 + 2) ≤ (2 : ℝ)⁻¹ ^ p := by
    calc (x.2.1 : ℝ) * (2 : ℝ)⁻¹ ^ (p + x.2.1 + 2)
      _ ≤ (2 : ℝ) ^ x.2.1 * (2 : ℝ)⁻¹ ^ (p + x.2.1 + 2) := by
        apply mul_le_mul_of_nonneg_right
        · norm_cast
          exact (Nat.lt_two_pow_self).le
        · positivity
      _ = (2 : ℝ) ^ x.2.1 * ((2 : ℝ)⁻¹ ^ x.2.1 * (2 : ℝ)⁻¹ ^ (p + 2)) := by
        have h_eq : p + x.2.1 + 2 = x.2.1 + (p + 2) := by omega
        rw [h_eq, pow_add]
      _ = ((2 : ℝ) ^ x.2.1 * (2 : ℝ)⁻¹ ^ x.2.1) * (2 : ℝ)⁻¹ ^ (p + 2) := by
        ring
      _ = (2 : ℝ)⁻¹ ^ (p + 2) := by
        have h_inv : (2 : ℝ) ^ x.2.1 * (2 : ℝ)⁻¹ ^ x.2.1 = 1 := by
          rw [← mul_pow]
          norm_num
        rw [h_inv, one_mul]
      _ ≤ (2 : ℝ)⁻¹ ^ p := by
        have hp : (2 : ℝ)⁻¹ ^ (p + 2) = (2 : ℝ)⁻¹ ^ p * (2 : ℝ)⁻¹ ^ 2 := by
          rw [pow_add]
        rw [hp]
        calc (2 : ℝ)⁻¹ ^ p * (2 : ℝ)⁻¹ ^ 2 ≤ (2 : ℝ)⁻¹ ^ p * 1 := by
                apply mul_le_mul_of_nonneg_left
                · have hs : (2 : ℝ)⁻¹ ^ 2 ≤ 1 := by norm_num
                  exact hs
                · positivity
             _ = (2 : ℝ)⁻¹ ^ p := by ring
  exact lt_of_le_of_lt h_le (h_lt.trans_le h_bound)

/-- Finite sums of a uniformly computable real family are uniformly computable. -/
private theorem computable_real_family_sum {α β : Type*} [Primcodable α]
    [Primcodable β] (A : Set ℕ) (F : α → ℕ → β → ℝ)
    (hF : IsComputableRealFamilyIn A
      (fun x : α × ℕ × β ↦ F x.1 x.2.1 x.2.2)) :
    IsComputableRealFamilyIn A
      (fun x : α × ℕ × β ↦ ∑ t ∈ Finset.range x.2.1, F x.1 t x.2.2) := by
  rcases hF with ⟨q, hq_comp, hq_bound⟩
  let r : (α × ℕ × β) × ℕ → ℚ := fun z ↦
    Nat.rec (motive := fun _ ↦ ℚ) (0 : ℚ)
      (fun t ih ↦ ih + q ((z.1.1, t, z.1.2.2), z.2 + z.1.2.1 + 2))
      z.1.2.1
  use r
  constructor
  · exact computable_shifted_rat_sums A q hq_comp
  · intro x p
    have h_rec_eq : (r (x, p) : ℝ) =
        ∑ t ∈ Finset.range x.2.1, (q ((x.1, t, x.2.2), p + x.2.1 + 2) : ℝ) := by
      dsimp [r]
      have H (n : ℕ) :
          Nat.rec (0 : ℚ) (fun t ih ↦ ih + q ((x.1, t, x.2.2), p + x.2.1 + 2)) n =
            ∑ t ∈ Finset.range n, q ((x.1, t, x.2.2), p + x.2.1 + 2) := by
        induction n with
        | zero => rfl
        | succ n hn => rw [Finset.sum_range_succ, ← hn]
      rw [H x.2.1]
      push_cast
      rfl
    rw [h_rec_eq]
    exact abs_sum_approx_lt F q hq_bound x p

/-- Birkhoff sums at ideal points have uniform relative rational approximations, including
the empty sum at order zero. Blueprint node `metric:birkhoff`. -/
theorem birkhoff_computableIn {k : ℕ} (P : Presentation X) (T : X → X)
    (v : Fin k → X → ℝ) (A : Set ℕ) (hA : IsAdmissible P T v A) :
    IsComputableRealFamilyIn A
      (fun jni : Fin k × ℕ × ℕ => birkhoffSum T (v jni.1) jni.2.1 (P.ι jni.2.2)) := by
  have hEval := computable_orbit_potentials P T v A hA
  have hSum := computable_real_family_sum A (fun j t i ↦ v j (T^[t] (P.ι i))) hEval
  convert hSum using 1
  ext ⟨j, n, i⟩
  simp only [birkhoffSum]

/-- Two members of a computable family can be queried together at a common precision. -/
private lemma computable_paired_names {α : Type*} [Primcodable α] (A : Set ℕ)
    (a : α → ℕ → ℕ) (ha : ComputableIn {charOracle A} (fun z : α × ℕ ↦ a z.1 z.2)) :
    ComputableIn {charOracle A}
      (fun z : (α × α) × ℕ ↦ ((a z.1.1 z.2, a z.1.2 z.2), z.2)) := by
  have hl : Computable (fun z : (α × α) × ℕ ↦ (z.1.1, z.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have hr : Computable (fun z : (α × α) × ℕ ↦ (z.1.2, z.2)) :=
    (Computable.snd.comp Computable.fst).pair Computable.snd
  exact ((ha.comp hl.computableIn).pair (ha.comp hr.computableIn)).pair ComputableIn.snd

/-- The metric table can be evaluated at the ideal points selected by computable names. -/
private lemma exists_metric_table_approx {X : Type*} [MetricSpace X] (P : Presentation X)
    (A : Set ℕ) (hP : ComputablePresentationIn P A)
    (a : (ℕ × ℕ) → ℕ → ℕ) (ha : ComputableIn {charOracle A} (fun z : (ℕ × ℕ) × ℕ ↦ a z.1 z.2)) :
    ∃ q : (ℕ × (ℕ × ℕ)) × ℕ → ℚ, ComputableIn {charOracle A} q ∧
      ∀ t_ij p, |(q (t_ij, p) : ℝ) -
        dist (P.ι (a (t_ij.1, t_ij.2.1) (p + 2))) (P.ι (a (t_ij.1, t_ij.2.2) (p + 2)))| <
          (2 : ℝ)⁻¹ ^ (p + 2) := by
  obtain ⟨m, hm, hm_err⟩ := hP
  have hprec : Computable (fun z : (ℕ × ℕ × ℕ) × ℕ ↦ z.2 + 2) :=
    Computable₂.comp Primrec.nat_add.to_comp Computable.snd (Computable.const 2)
  have htime : Computable (fun z : (ℕ × ℕ × ℕ) × ℕ ↦ z.1.1) :=
    Computable.fst.comp Computable.fst
  have hcenters : Computable (fun z : (ℕ × ℕ × ℕ) × ℕ ↦ z.1.2) :=
    Computable.snd.comp Computable.fst
  have hreindex : Computable (fun z : (ℕ × ℕ × ℕ) × ℕ ↦
      (((z.1.1, z.1.2.1), (z.1.1, z.1.2.2)), z.2 + 2)) :=
    ((htime.pair (Computable.fst.comp hcenters)).pair
      (htime.pair (Computable.snd.comp hcenters))).pair hprec
  have hquery := (computable_paired_names A a ha).comp hreindex.computableIn
  refine ⟨_, hm.comp hquery, ?_⟩
  intro t_ij p
  exact hm_err _ _

/-- Two name errors and one metric-table error at precision `p + 2` give precision `p`. -/
private lemma abs_orbit_dist_approx_lt {X : Type*} [MetricSpace X] (P : Presentation X)
    (T : X → X) (a : (ℕ × ℕ) → ℕ → ℕ)
    (ha_cauchy : ∀ n i, IsCauchyName P (T^[n] (P.ι i)) (a (n, i)))
    (q : (ℕ × (ℕ × ℕ)) × ℕ → ℚ)
    (hq_err : ∀ t_ij p, |(q (t_ij, p) : ℝ) -
      dist (P.ι (a (t_ij.1, t_ij.2.1) (p + 2))) (P.ι (a (t_ij.1, t_ij.2.2) (p + 2)))| <
        (2 : ℝ)⁻¹ ^ (p + 2)) :
    ∀ t_ij p, |(q (t_ij, p) : ℝ) - dist (T^[t_ij.1] (P.ι t_ij.2.1)) (T^[t_ij.1] (P.ι t_ij.2.2))| <
        (2 : ℝ)⁻¹ ^ p := by
  intro t_ij p
  let u := P.ι (a (t_ij.1, t_ij.2.1) (p + 2))
  let v := P.ι (a (t_ij.1, t_ij.2.2) (p + 2))
  let x := T^[t_ij.1] (P.ι t_ij.2.1)
  let y := T^[t_ij.1] (P.ι t_ij.2.2)
  have h1 : dist u x < dyadicRadius (p + 2) := ha_cauchy _ _ _
  have h2 : dist v y < dyadicRadius (p + 2) := ha_cauchy _ _ _
  have h_tri : |dist u v - dist x y| ≤ dist u x + dist v y :=
    dist_dist_dist_le u v x y
  have h3 : |(q (t_ij, p) : ℝ) - dist u v| < (2 : ℝ)⁻¹ ^ (p + 2) := hq_err t_ij p
  have H : |(q (t_ij, p) : ℝ) - dist x y| ≤
      |(q (t_ij, p) : ℝ) - dist u v| + |dist u v - dist x y| := abs_sub_le _ _ _
  have H3 : |(q (t_ij, p) : ℝ) - dist u v| + (dist u x + dist v y) <
      (2 : ℝ)⁻¹ ^ (p + 2) + ((2 : ℝ)⁻¹ ^ (p + 2) + (2 : ℝ)⁻¹ ^ (p + 2)) := by
    apply add_lt_add
    · exact h3
    · apply add_lt_add
      · exact h1
      · exact h2
  have H4 : (2 : ℝ)⁻¹ ^ (p + 2) + ((2 : ℝ)⁻¹ ^ (p + 2) + (2 : ℝ)⁻¹ ^ (p + 2)) < (2 : ℝ)⁻¹ ^ p := by
    have h_eq : (2 : ℝ)⁻¹ ^ (p + 2) = (2 : ℝ)⁻¹ ^ p * (2 : ℝ)⁻¹ ^ 2 := by rw [pow_add]
    rw [h_eq]
    have h_eval : (2 : ℝ)⁻¹ ^ 2 = (1 / 4 : ℝ) := by norm_num
    rw [h_eval]
    have hp : 0 < (2 : ℝ)⁻¹ ^ p := by positivity
    linarith
  exact lt_of_le_of_lt H (lt_of_le_of_lt (add_le_add le_rfl h_tri) (lt_of_lt_of_le H3 H4.le))

/-- Distances between ideal-point orbits are computable uniformly in time and both centers. -/
private theorem computable_orbit_distances {k : ℕ} (P : Presentation X)
    (T : X → X) (v : Fin k → X → ℝ) (A : Set ℕ) (hA : IsAdmissible P T v A) :
    IsComputableRealFamilyIn A (fun t_ij : ℕ × (ℕ × ℕ) ↦ dist (T^[t_ij.1] (P.ι t_ij.2.1))
        (T^[t_ij.1] (P.ι t_ij.2.2))) := by
  rcases hA with ⟨hP, hT, _⟩
  obtain ⟨a, hacomp, ha_cauchy⟩ := exists_computable_orbit_names P T A hP hT
  obtain ⟨q, hqcomp, hq_err⟩ := exists_metric_table_approx P A hP a hacomp
  use q
  constructor
  · exact hqcomp
  · exact abs_orbit_dist_approx_lt P T a ha_cauchy q hq_err

/-- The rational running maximum of a computable rational family is computable. -/
private theorem computable_rat_running_max
    {α β : Type*} [Primcodable α] [Primcodable β] (A : Set ℕ)
    (q : (α × ℕ × β) × ℕ → ℚ)
    (hq : ComputableIn {Kolmogorov.charOracle A} q) :
    ComputableIn {Kolmogorov.charOracle A}
      (fun z : (α × ℕ × β) × ℕ ↦
        Nat.rec (motive := fun _ ↦ ℚ) (0 : ℚ)
          (fun (t : ℕ) (ih : ℚ) ↦ max ih (q ((z.1.1, t, z.1.2.2), z.2))) z.1.2.1) := by
  have hlength : Computable (fun z : (α × ℕ × β) × ℕ ↦ z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hparams : Computable (fun z : ((α × ℕ × β) × ℕ) × (ℕ × ℚ) ↦ z.1.1) :=
    Computable.fst.comp Computable.fst
  have hquery : Computable (fun z : ((α × ℕ × β) × ℕ) × (ℕ × ℚ) ↦
      ((z.1.1.1, z.2.1, z.1.1.2.2), z.1.2)) :=
    ((Computable.fst.comp hparams).pair
      ((Computable.fst.comp Computable.snd).pair
        (Computable.snd.comp (Computable.snd.comp hparams)))).pair
      (Computable.snd.comp Computable.fst)
  have hacc : ComputableIn {charOracle A}
      (fun z : ((α × ℕ × β) × ℕ) × (ℕ × ℚ) ↦ z.2.2) :=
    (Computable.snd.comp Computable.snd).computableIn
  have hupdate : ComputableIn₂ {charOracle A}
      (fun (z : (α × ℕ × β) × ℕ) (p : ℕ × ℚ) ↦
        max p.2 (q ((z.1.1, p.1, z.1.2.2), z.2))) :=
    ComputableReals.primrec_ratMax.to_comp.computableIn₂.comp hacc
      (hq.comp hquery.computableIn)
  exact ComputableIn.nat_rec hlength.computableIn (ComputableIn.const 0) hupdate

/-- A running maximum preserves a uniform strict error bound for nonnegative real values. -/
private theorem abs_running_max_approx_lt
    {α β : Type*} (F : α → ℕ → β → ℝ) (q : (α × ℕ × β) × ℕ → ℚ)
    (hq_bound : ∀ (i : α × ℕ × β) (p : ℕ),
      |(q (i, p) : ℝ) - F i.1 i.2.1 i.2.2| < (2 : ℝ)⁻¹ ^ p)
    (h_nonneg : ∀ (a : α) (t : ℕ) (b : β), 0 ≤ F a t b) :
    ∀ (i : α × ℕ × β) (p : ℕ),
      |((Nat.rec (motive := fun _ ↦ ℚ) (0 : ℚ)
          (fun t ih ↦ max ih (q ((i.1, t, i.2.2), p))) i.2.1 : ℚ) : ℝ) -
        (↑((Finset.range i.2.1).sup
          (fun t ↦ (⟨F i.1 t i.2.2, h_nonneg i.1 t i.2.2⟩ : NNReal))) : ℝ)| <
          (2 : ℝ)⁻¹ ^ p := by
  rintro ⟨a, n, b⟩ p
  let R : ℕ → ℚ := fun k ↦
    Nat.rec (motive := fun _ ↦ ℚ) 0
      (fun t ih ↦ max ih (q ((a, t, b), p))) k
  let M : ℕ → ℝ := fun k ↦
    ↑((Finset.range k).sup
      (fun t ↦ (⟨F a t b, h_nonneg a t b⟩ : NNReal)))
  have hR (k : ℕ) :
      R (k + 1) = max (R k) (q ((a, k, b), p)) := rfl
  have hM (k : ℕ) :
      M (k + 1) = max (M k) (F a k b) := by
    dsimp only [M]
    rw [Finset.range_add_one, Finset.sup_insert]
    exact (NNReal.coe_max _ _).trans (max_comm _ _)
  change |(R n : ℝ) - M n| < (2 : ℝ)⁻¹ ^ p
  induction n with
  | zero =>
    simp [R, M]
  | succ n ih =>
    rw [hR, hM, Rat.cast_max]
    calc
      |max (R n : ℝ) (q ((a, n, b), p) : ℝ) - max (M n) (F a n b)| ≤
          max |(R n : ℝ) - M n| |(q ((a, n, b), p) : ℝ) - F a n b| :=
        abs_max_sub_max_le_max _ _ _ _
      _ < (2 : ℝ)⁻¹ ^ p := max_lt ih (hq_bound (a, n, b) p)

/-- Finite maxima of a nonnegative computable real family are uniformly computable. -/
private theorem computable_real_family_max {α β : Type*} [Primcodable α] [Primcodable β] (A : Set ℕ)
    (F : α → ℕ → β → ℝ) (hF : IsComputableRealFamilyIn A (fun x : α × ℕ × β ↦ F x.1 x.2.1 x.2.2))
    (h_nonneg : ∀ a t b, 0 ≤ F a t b) :
    IsComputableRealFamilyIn A (fun x : α × ℕ × β ↦
      (↑((Finset.range x.2.1).sup
        (fun t ↦ (⟨F x.1 t x.2.2, h_nonneg x.1 t x.2.2⟩ : NNReal))) : ℝ)) := by
  rcases hF with ⟨q, hq_comp, hq_bound⟩
  let r : (α × ℕ × β) × ℕ → ℚ := fun z ↦
    Nat.rec (motive := fun _ ↦ ℚ) (0 : ℚ) (fun t ih ↦ max ih (q ((z.1.1, t, z.1.2.2), z.2))) z.1.2.1
  use r
  constructor
  · exact computable_rat_running_max A q hq_comp
  · intro x p
    have Hbound := abs_running_max_approx_lt F q hq_bound h_nonneg
    exact Hbound x p

/-- Reindexing a computable real family by a computable function preserves computability. -/
theorem IsComputableRealFamilyIn.comp {α β : Type*} [Primcodable α] [Primcodable β] (A : Set ℕ)
    (v : β → ℝ) (hv : IsComputableRealFamilyIn A v) (f : α → β) (hf : Computable f) :
    IsComputableRealFamilyIn A (v ∘ f) := by
  rcases hv with ⟨q, hq_comp, hq_bound⟩
  use fun ap ↦ q (f ap.1, ap.2)
  constructor
  · apply hq_comp.comp
    exact (hf.comp Computable.fst).pair Computable.snd |>.computableIn
  · intro i p
    exact hq_bound (f i) p

/-- Finite orbit distances at ideal points have approximations uniform in both centers,
time and precision. Blueprint node `metric:birkhoff`. -/
theorem birkhoff_computableIn_dist {k : ℕ} (P : Presentation X) (T : X → X)
    (v : Fin k → X → ℝ) (A : Set ℕ) (hA : IsAdmissible P T v A) :
    IsComputableRealFamilyIn A
      (fun nij : ℕ × ℕ × ℕ => bowenDist T nij.1 (P.ι nij.2.1) (P.ι nij.2.2)) := by
  let F : Unit → ℕ → (ℕ × ℕ) → ℝ := fun _ t ij ↦ dist (T^[t] (P.ι ij.1)) (T^[t] (P.ι ij.2))
  have h_dist : IsComputableRealFamilyIn A (fun x : Unit × ℕ × (ℕ × ℕ) ↦ F x.1 x.2.1 x.2.2) := by
    exact IsComputableRealFamilyIn.comp A _ (computable_orbit_distances P T v A hA)
      (fun x : Unit × ℕ × (ℕ × ℕ) ↦ x.2) Computable.snd
  have h_nonneg : ∀ a t b, 0 ≤ F a t b := fun _ _ _ ↦ dist_nonneg
  have h_max := computable_real_family_max A F h_dist h_nonneg
  have h_max2 := IsComputableRealFamilyIn.comp A _ h_max
    (fun nij : ℕ × ℕ × ℕ ↦ ((), nij.1, (nij.2.1, nij.2.2)))
    ((Computable.const ()).pair (Computable.fst.pair Computable.snd))
  convert h_max2 using 1
  ext ⟨n, i, j⟩
  dsimp [bowenDist, F, Function.comp_def]
  congr 1

end Kolmogorov.PointToSet
