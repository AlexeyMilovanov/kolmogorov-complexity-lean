/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.PrefixComplexity
import KolmogorovMathlib.Oracle.Joins
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Order.LiminfLimsup
import KolmogorovMathlib.PointToSet.ForMathlib

/-!
# Fixed metric presentations and represented maps

A `Presentation` of a complete metric space `X` is one fixed dense sequence of ideal points,
chosen before any oracle is. Points of `X` are accessed through Cauchy names, i.e. index
sequences `a` with `dist (ι (a p)) x < 2⁻ᵖ`, and a continuous map is accessed through a
represented-map relation: an enumerable set of pairs of rational basic balls that is sound
(the image of the first ball lies in the second) and complete (every basic neighbourhood of
`f x` has a listed preimage ball around `x`).

This file defines these notions together with the relative computability of the metric table
(`ComputablePresentationIn`) and the oracle-admissibility of dynamical data (`IsAdmissible`).
It proves that a represented map transforms an `A`-computable name of `x` into an
`A`-computable name of `f x` (`eval_computable_names`), uniformly in the index of the input
name (`eval_computable_names_uniform`), and that represented maps compose
(`eval_computable_names_comp`); these are the blueprint nodes `metric:names`,
`metric:evaluation` and `metric:admissible`.  The files on static dimensions, pressure and
the Bowen equation use them to show that every quantity built from the dynamics is
computable relative to a sufficiently strong oracle.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-- A complete metric space with one fixed dense ideal sequence, chosen before oracles.
Nonemptiness and separability follow from the sequence. Blueprint node `metric:presentation`. -/
structure Presentation (X : Type*) [MetricSpace X] where
  /-- The fixed ideal sequence, shared by all oracles. -/
  ι : ℕ → X
  /-- Every nonempty open subset contains an ideal point. -/
  dense : DenseRange ι
  /-- The presented metric space is complete. -/
  complete : CompleteSpace X

/-- Positive dyadic radii give the precision convention used throughout the blueprint.
Blueprint node `metric:presentation`. -/
noncomputable def dyadicRadius (p : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ p

/-- Dyadic radii are positive. -/
theorem dyadicRadius_pos (p : ℕ) : 0 < dyadicRadius p := by
  unfold dyadicRadius
  positivity

/-- The dyadic radii `dyadicRadius p` decrease with `p`. -/
theorem dyadicRadius_antitone : Antitone dyadicRadius := fun _ _ hpq ↦
  pow_le_pow_of_le_one (by norm_num) (by norm_num) hpq

/-- Dyadic radii become arbitrarily small. -/
theorem exists_dyadicRadius_lt {ε : ℝ} (hε : 0 < ε) : ∃ p, dyadicRadius p < ε :=
  exists_pow_lt_of_lt_one hε (by norm_num)

/-- The binary logarithm of `dyadicRadius p` is `-p`. -/
theorem neg_logb_dyadicRadius (p : ℕ) : -Real.logb 2 (dyadicRadius p) = p := by
  rw [dyadicRadius, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  ring

/-- The logarithms of consecutive dyadic radii have ratio tending to `1`. -/
theorem tendsto_log_dyadicRadius_succ_div :
    Filter.Tendsto (fun m : ℕ ↦ Real.log (dyadicRadius (m + 1)) / Real.log (dyadicRadius m))
      Filter.atTop (nhds 1) :=
  Real.tendsto_log_pow_succ_div_log_pow (β := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)

/-- A Cauchy name approximates its point with strict dyadic errors at every precision.
Blueprint node `metric:names`. -/
def IsCauchyName (P : Presentation X) (x : X) (a : ℕ → ℕ) : Prop :=
  ∀ p, dist (P.ι (a p)) x < dyadicRadius p

/-- A rational basic ball is specified on the ambient primcodable type of center and
radius codes. Nonpositive radii give empty balls. Blueprint node `metric:names`. -/
def basicBall (P : Presentation X) (b : ℕ × ℚ) : Set X :=
  Metric.ball (P.ι b.1) (b.2 : ℝ)

/-- A presentation has a relative computable metric table when its ideal distances have
uniform rational approximations. Blueprint node `metric:names`. -/
def ComputablePresentationIn (P : Presentation X) (A : Set ℕ) : Prop :=
  IsComputableRealFamilyIn A (fun ij : ℕ × ℕ => dist (P.ι ij.1) (P.ι ij.2))

/-- A represented map has an enumerable sound relation between positive rational basic
balls, complete at every point and every target basic neighborhood.
Blueprint node `metric:names`. -/
def IsRepresentedMapIn (P : Presentation X) (Q : Presentation Y) (A : Set ℕ)
    (f : X → Y) : Prop :=
  ∃ R : (ℕ × ℚ) × (ℕ × ℚ) → Prop, IsREIn A R ∧
    (∀ b c, R (b, c) → 0 < b.2 ∧ 0 < c.2 ∧ f '' basicBall P b ⊆ basicBall Q c) ∧
    ∀ x c, f x ∈ basicBall Q c → ∃ b, R (b, c) ∧ x ∈ basicBall P b

/-- The fixed real presentation enumerates the existing rational codes; it is independent
of all oracles. Blueprint node `metric:names`. -/
noncomputable def realPresentation : Presentation ℝ where
  ι n := ((Encodable.decode (α := ℚ) n).getD 0 : ℝ)
  dense := by
    have h : Set.range (fun n => ((Encodable.decode (α := ℚ) n).getD 0 : ℝ)) =
        Set.range (fun q : ℚ => (q : ℝ)) := by
      ext x
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨Encodable.encode q, by simp⟩
    change Dense (Set.range (fun n => ((Encodable.decode (α := ℚ) n).getD 0 : ℝ)))
    rw [h]
    exact Rat.denseRange_cast
  complete := inferInstance

/-! ### Dyadic radii and rational certificates -/

/-- A pair of rational basic balls, the type of entries of a represented-map relation. -/
private abbrev BallPair := (ℕ × ℚ) × (ℕ × ℚ)

/-- The rational power `2⁻ᵖ` casts to the dyadic radius. -/
private lemma cast_inv_two_pow (p : ℕ) : (((2 : ℚ)⁻¹ ^ p : ℚ) : ℝ) = dyadicRadius p := by
  simp only [dyadicRadius, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]

/-- Comparing a rational with `2⁻ᵖ` is the same as comparing its cast with `dyadicRadius p`. -/
private lemma lt_inv_two_pow_iff {r : ℚ} {p : ℕ} :
    r < (2 : ℚ)⁻¹ ^ p ↔ (r : ℝ) < dyadicRadius p := by
  rw [← cast_inv_two_pow p, Rat.cast_lt]

/-- The rational form of the certificate inequality is equivalent to its real form. -/
private lemma add_inv_two_pow_lt_iff {r s : ℚ} {k m : ℕ} :
    r + (2 : ℚ)⁻¹ ^ k + (2 : ℚ)⁻¹ ^ m < s ↔
      (r : ℝ) + dyadicRadius k + dyadicRadius m < s := by
  rw [← cast_inv_two_pow k, ← cast_inv_two_pow m, ← Rat.cast_add, ← Rat.cast_add, Rat.cast_lt]

/-- The rational dyadic radii `2⁻ᵖ` are computable from the precision index. -/
private lemma computable_inv_two_pow : Computable (fun p : ℕ => (2 : ℚ)⁻¹ ^ p) := by
  have hc := ComputableReals.computable_invSucc.comp
    ((Primrec.nat_sub.comp primrec_two_pow_aux (Primrec.const 1)).to_comp)
  refine hc.of_eq fun p => ?_
  have hpos : 0 < (2 : ℕ) ^ p := by positivity
  have heq : ((2 ^ p - 1 : ℕ) : ℚ) + 1 = (2 : ℚ) ^ p := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  change 1 / (((2 ^ p - 1 : ℕ) : ℚ) + 1) = _
  rw [heq, one_div, inv_pow]

/-- A point lies in an open rational ball exactly when some name stage and the rational
distance approximation certify it; the two added dyadic errors account for the metric
approximation and for the name. -/
private lemma mem_basicBall_iff_exists_certificate
    (P : Presentation X) (q : (ℕ × ℕ) × ℕ → ℚ)
    (hq : ∀ ij p, |(q (ij, p) : ℝ) - dist (P.ι ij.1) (P.ι ij.2)| < dyadicRadius p)
    (x : X) (a : ℕ → ℕ) (ha : IsCauchyName P x a) (b : ℕ × ℚ) :
    x ∈ basicBall P b ↔ ∃ m,
      q ((a m, b.1), m) + (2 : ℚ)⁻¹ ^ m + (2 : ℚ)⁻¹ ^ m < b.2 := by
  simp only [add_inv_two_pow_lt_iff]
  constructor
  · intro hx
    have hx' : dist x (P.ι b.1) < b.2 := Metric.mem_ball.mp hx
    obtain ⟨m, hm⟩ := exists_dyadicRadius_lt
      (show 0 < ((b.2 : ℝ) - dist x (P.ι b.1)) / 4 by linarith)
    refine ⟨m, ?_⟩
    have herr := (abs_lt.mp (hq (a m, b.1) m)).2
    have hname := ha m
    have htri := dist_triangle (P.ι (a m)) x (P.ι b.1)
    linarith
  · rintro ⟨m, hm⟩
    refine Metric.mem_ball.mpr ?_
    have herr := (abs_lt.mp (hq (a m, b.1) m)).1
    have hname : dist x (P.ι (a m)) < dyadicRadius m := by
      rw [dist_comm]
      exact ha m
    have htri := dist_triangle x (P.ι (a m)) (P.ι b.1)
    linarith

/-- Every point of a presented space has a rational basic neighborhood whose radius is below
any requested dyadic error. -/
private lemma exists_basicBall_radius_lt (Q : Presentation Y) (y : Y) (p : ℕ) :
    ∃ c : ℕ × ℚ, y ∈ basicBall Q c ∧ (c.2 : ℝ) < dyadicRadius p := by
  have hpos : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp Q.dense y (dyadicRadius p / 2) (by positivity)
  obtain ⟨r, hr, hr'⟩ := exists_rat_btwn (show dyadicRadius p / 2 < dyadicRadius p by linarith)
  exact ⟨(j, r), hj.trans hr, hr'⟩

/-- A relatively computable Boolean test with a successful candidate at each input admits
a relatively computable choice of successful candidates, by unbounded search. -/
private lemma exists_computableIn_of_forall_exists_test
    (A : Set ℕ) (test : ℕ → ℕ → Bool)
    (htest : ComputableIn₂ {charOracle A} test)
    (htotal : ∀ p, ∃ n, test p n = true) :
    ∃ s : ℕ → ℕ, ComputableIn {charOracle A} s ∧ ∀ p, test p (s p) = true := by
  let E : ℕ →. ℕ := fun p => Nat.rfind (fun n => Part.some (test p n))
  have hE : PartrecIn {charOracle A} E := PartrecIn.rfind htest.partrecIn₂
  have hdom : ∀ p, (E p).Dom := by
    intro p
    obtain ⟨n, hn⟩ := htotal p
    exact Nat.rfind_dom.mpr ⟨n, by simp [hn], fun _ => trivial⟩
  let s : ℕ → ℕ := fun p => (E p).get (hdom p)
  refine ⟨s, PartrecIn.of_eq_tot hE (fun p => Part.get_mem (hdom p)), ?_⟩
  intro p
  have hs := Nat.rfind_spec (Part.get_mem (hdom p))
  exact (Part.mem_some_iff.mp hs).symm

/-! ### Evaluation of represented maps on a single name -/

/-- The rational test for a listed ball pair and a name stage, encoded by one natural.
The positive output radius excludes the all-zero default at idle enumeration stages. -/
private def nameCertificateTest (q : (ℕ × ℕ) × ℕ → ℚ) (a : ℕ → ℕ)
    (d : ℕ → BallPair) (p n : ℕ) : Bool :=
  (decide (0 < (d n.unpair.1).2.2) &&
    decide ((d n.unpair.1).2.2 < (2 : ℚ)⁻¹ ^ p)) &&
      decide (q ((a n.unpair.2, (d n.unpair.1).1.1), n.unpair.2) +
        (2 : ℚ)⁻¹ ^ n.unpair.2 + (2 : ℚ)⁻¹ ^ n.unpair.2 < (d n.unpair.1).1.2)

/-- The finite rational certificate test is computable relative to the metric table, the
input name and the list of ball pairs. -/
private lemma computableIn₂_nameCertificateTest
    (A : Set ℕ) (q : (ℕ × ℕ) × ℕ → ℚ) (a : ℕ → ℕ) (d : ℕ → BallPair)
    (hq : ComputableIn {charOracle A} q) (ha : ComputableIn {charOracle A} a)
    (hd : ComputableIn {charOracle A} d) :
    ComputableIn₂ {charOracle A} (nameCertificateTest q a d) := by
  have ht : Computable (fun z : ℕ × ℕ => z.2.unpair.1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hm : Computable (fun z : ℕ × ℕ => z.2.unpair.2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hlist := hd.comp ht.computableIn
  have hbi := ComputableIn.fst.comp (ComputableIn.fst.comp hlist)
  have hbq := ComputableIn.snd.comp (ComputableIn.fst.comp hlist)
  have hcq := ComputableIn.snd.comp (ComputableIn.snd.comp hlist)
  have hdist := hq.comp (((ha.comp hm.computableIn).pair hbi).pair hm.computableIn)
  have hδm := (computable_inv_two_pow.computableIn (O := {charOracle A})).comp hm.computableIn
  have hδp := (computable_inv_two_pow.computableIn (O := {charOracle A})).comp
    (Computable.fst (α := ℕ) (β := ℕ)).computableIn
  have hsum := ComputableReals.computable_ratAdd.computableIn₂.comp
    (ComputableReals.computable_ratAdd.computableIn₂.comp hdist hδm) hδm
  have hpos := ComputableReals.primrec_ratLt.decide.to_comp.computableIn.comp
    ((Computable.const (0 : ℚ)).computableIn.pair hcq)
  have hsmall := ComputableReals.primrec_ratLt.decide.to_comp.computableIn.comp
    (hcq.pair hδp)
  have hcert := ComputableReals.primrec_ratLt.decide.to_comp.computableIn.comp
    (hsum.pair hbq)
  exact (Primrec.and.to_comp.computableIn₂.comp
    (Primrec.and.to_comp.computableIn₂.comp hpos hsmall) hcert).to₂

/-- A represented map out of a computable presentation sends a computable name to a computable
name; the output name is read off the listed target balls. Blueprint node `metric:evaluation`. -/
theorem eval_computable_names (P : Presentation X) (Q : Presentation Y) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (f : X → Y) (hf : IsRepresentedMapIn P Q A f) (x : X)
    (a : ℕ → ℕ)
    (ha : IsCauchyName P x a) (hcomp : ComputableIn {charOracle A} a) :
    ∃ b : ℕ → ℕ, IsCauchyName Q (f x) b ∧ ComputableIn {charOracle A} b := by
  obtain ⟨q, hq, hqerr⟩ := hP
  obtain ⟨R, hR, hsound, hcomplete⟩ := hf
  obtain ⟨e, he, herange⟩ := (relative_enumeration A R).mp hR
  let d : ℕ → BallPair := fun t => (e t).getD ((0, 0), (0, 0))
  have hd : ComputableIn {charOracle A} d :=
    Primrec.option_getD.to_comp.computableIn₂.comp he
      (Computable.const ((0, 0), (0, 0))).computableIn
  have htest := computableIn₂_nameCertificateTest A q a d hq hcomp hd
  have htotal : ∀ p, ∃ n, nameCertificateTest q a d p n = true := by
    intro p
    obtain ⟨c, hc, hcsmall⟩ := exists_basicBall_radius_lt Q (f x) p
    obtain ⟨b, hRbc, hxb⟩ := hcomplete x c hc
    obtain ⟨t, ht⟩ := (herange (b, c)).mp hRbc
    obtain ⟨m, hm⟩ := (mem_basicBall_iff_exists_certificate P q hqerr x a ha b).mp hxb
    refine ⟨Nat.pair t m, ?_⟩
    simp only [nameCertificateTest, Nat.unpair_pair, d, ht, Option.getD_some,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨(hsound b c hRbc).2.1, lt_inv_two_pow_iff.mpr hcsmall⟩, hm⟩
  obtain ⟨s, hscomp, hs⟩ := exists_computableIn_of_forall_exists_test A _ htest htotal
  refine ⟨fun p => (d (s p).unpair.1).2.1, ?_, ?_⟩
  · intro p
    have hp := hs p
    simp only [nameCertificateTest, Bool.and_eq_true, decide_eq_true_eq] at hp
    have hlisted : R (d (s p).unpair.1) := by
      cases ht : e (s p).unpair.1 with
      | none => simp [d, ht] at hp
      | some bc =>
        have hd' : d (s p).unpair.1 = bc := by simp [d, ht]
        rw [hd']
        exact (herange bc).mpr ⟨_, ht⟩
    have hxb : x ∈ basicBall P (d (s p).unpair.1).1 :=
      (mem_basicBall_iff_exists_certificate P q hqerr x a ha _).mpr ⟨(s p).unpair.2, hp.2⟩
    have hy := (hsound _ _ hlisted).2.2 (Set.mem_image_of_mem f hxb)
    exact (Metric.mem_ball'.mp hy).trans (lt_inv_two_pow_iff.mp hp.1.2)
  · have ht : ComputableIn {charOracle A} (fun p => (s p).unpair.1) :=
      ((Primrec.fst.comp Primrec.unpair).to_comp.computableIn).comp hscomp
    exact ComputableIn.fst.comp (ComputableIn.snd.comp (hd.comp ht))

/-! ### Uniform evaluation -/

/-- The input of the rational certificate test: an index pair `(e, p)`, a search index, a
listed ball pair and an oracle-computed name approximation. -/
private abbrev CertificateInput := ((ℕ × ℕ) × ℕ) × BallPair × ℕ

/-- The finite rational test: the output ball `c` is positive and of radius below `2⁻ᵖ`, and
the name approximation `n` lies in the input ball `b` with margin `2⁻ᵏ + 2⁻ᵐ` after the
metric approximation of precision `k`. -/
private def certificateCheck (q : (ℕ × ℕ) × ℕ → ℚ) (p m k n : ℕ) (b c : ℕ × ℚ) : Bool :=
  decide (0 < c.2) && decide (c.2 < (2 : ℚ)⁻¹ ^ p) &&
    decide (q ((n, b.1), k) + (2 : ℚ)⁻¹ ^ k + (2 : ℚ)⁻¹ ^ m < b.2)

/-- The search over listed pairs and oracle stages: the search index `z` codes a position `t`
in the enumeration of the relation, a name stage `m`, an oracle stage `s` and a metric
precision `k`; the test outputs the target ball when the certificate check succeeds. -/
private noncomputable def certificateSearchTest
    (q : (ℕ × ℕ) × ℕ → ℚ) (e_R : ℕ → Option BallPair)
    (A : Set ℕ) (ep : ℕ × ℕ) (z : ℕ) : Option (ℕ × ℚ) :=
  let t := z.unpair.1
  let m := z.unpair.2.unpair.1
  let s := z.unpair.2.unpair.2.unpair.1
  let k := z.unpair.2.unpair.2.unpair.2
  match e_R t, oracleStage A s ep.1 m with
  | some (b, c), some n => if certificateCheck q ep.2 m k n b c then some c else none
  | _, _ => none

/-- The output ball `c` is certified for the name enumerated by the oracle program `e` at
precision `p`: some listed pair `(b, c)` has input ball `b` containing the name approximation
computed at stage `m`, with margin `dyadicRadius m`, and `c` is a positive ball of radius
below `dyadicRadius p`. -/
private def IsCertifiedOutput (P : Presentation X) (A : Set ℕ) (R : BallPair → Prop)
    (e p : ℕ) (c : ℕ × ℚ) : Prop :=
  ∃ b m n, R (b, c) ∧ n ∈ oracleEval A e m ∧
    dist (P.ι n) (P.ι b.1) + dyadicRadius m < b.2 ∧ 0 < c.2 ∧ (c.2 : ℝ) < dyadicRadius p

/-- Membership of a value in the oracle evaluation is witnessed by some stage. -/
private lemma mem_oracleEval_iff (A : Set ℕ) (e m n : ℕ) :
    n ∈ oracleEval A e m ↔ ∃ s, oracleStage A s e m = some n :=
  Nat.rfindOpt_mono (fun hts ha => oracleStage_persistent A e m _ _ _ hts ha)

/-- The rational certificate check is computable relative to the metric table. -/
private lemma computableIn_certificateCheck (q : (ℕ × ℕ) × ℕ → ℚ) (A : Set ℕ)
    (hq : ComputableIn {charOracle A} q) :
    ComputableIn {charOracle A} fun w : CertificateInput =>
      certificateCheck q w.1.1.2 w.1.2.unpair.2.unpair.1 w.1.2.unpair.2.unpair.2.unpair.2
        w.2.2 w.2.1.1 w.2.1.2 := by
  have hz : ComputableIn {charOracle A} fun w : CertificateInput => w.1.2 :=
    ComputableIn.snd.comp ComputableIn.fst
  have hp : ComputableIn {charOracle A} fun w : CertificateInput => w.1.1.2 :=
    ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)
  have hb : ComputableIn {charOracle A} fun w : CertificateInput => w.2.1.1 :=
    ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.snd)
  have hc : ComputableIn {charOracle A} fun w : CertificateInput => w.2.1.2 :=
    ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.snd)
  have hn : ComputableIn {charOracle A} fun w : CertificateInput => w.2.2 :=
    ComputableIn.snd.comp ComputableIn.snd
  have hm' : Primrec fun z : ℕ => z.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hk' : Primrec fun z : ℕ => z.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hm : ComputableIn {charOracle A} fun w : CertificateInput => w.1.2.unpair.2.unpair.1 :=
    hm'.to_comp.computableIn.comp hz
  have hk : ComputableIn {charOracle A} fun w : CertificateInput =>
      w.1.2.unpair.2.unpair.2.unpair.2 :=
    hk'.to_comp.computableIn.comp hz
  have hc2 := ComputableIn.snd.comp hc
  have hδp := (computable_inv_two_pow.computableIn (O := {charOracle A})).comp hp
  have hδk := (computable_inv_two_pow.computableIn (O := {charOracle A})).comp hk
  have hδm := (computable_inv_two_pow.computableIn (O := {charOracle A})).comp hm
  have hqarg := hq.comp ((hn.pair (ComputableIn.fst.comp hb)).pair hk)
  have hsum := ComputableReals.computable_ratAdd.computableIn₂.comp
    (ComputableReals.computable_ratAdd.computableIn₂.comp hqarg hδk) hδm
  have hpos := ComputableReals.primrec_ratLt.decide.to_comp.computableIn.comp
    ((Computable.const (0 : ℚ)).computableIn.pair hc2)
  have hsmall := ComputableReals.primrec_ratLt.decide.to_comp.computableIn.comp
    (hc2.pair hδp)
  have hcert := ComputableReals.primrec_ratLt.decide.to_comp.computableIn.comp
    (hsum.pair (ComputableIn.snd.comp hb))
  exact Primrec.and.to_comp.computableIn₂.comp
    (Primrec.and.to_comp.computableIn₂.comp hpos hsmall) hcert

/-- The certificate search test is computable relative to the metric table and the
enumeration of the relation, uniformly in both arguments. -/
private lemma computableIn₂_certificateSearchTest
    (q : (ℕ × ℕ) × ℕ → ℚ) (e_R : ℕ → Option BallPair) (A : Set ℕ)
    (hq : ComputableIn {charOracle A} q) (he_R : ComputableIn {charOracle A} e_R) :
    ComputableIn₂ {charOracle A} (certificateSearchTest q e_R A) := by
  let D := (ℕ × ℕ) × ℕ
  let r : D → Option BallPair := fun x => e_R x.2.unpair.1
  let o : D → Option ℕ := fun x =>
    oracleStage A x.2.unpair.2.unpair.2.unpair.1 x.1.1 x.2.unpair.2.unpair.1
  have hu : Primrec (fun x : D => x.2.unpair) := Primrec.unpair.comp Primrec.snd
  have ht : Primrec (fun x : D => x.2.unpair.2) := Primrec.snd.comp hu
  have hu' : Primrec (fun x : D => x.2.unpair.2.unpair) := Primrec.unpair.comp ht
  have hr : ComputableIn {charOracle A} r := he_R.comp (Primrec.fst.comp hu).computableIn
  have hm : Primrec (fun x : D => x.2.unpair.2.unpair.1) := Primrec.fst.comp hu'
  have ht' : Primrec (fun x : D => x.2.unpair.2.unpair.2) := Primrec.snd.comp hu'
  have hu'' : Primrec (fun x : D => x.2.unpair.2.unpair.2.unpair) := Primrec.unpair.comp ht'
  have hs : Primrec (fun x : D => x.2.unpair.2.unpair.2.unpair.1) := Primrec.fst.comp hu''
  have he : Primrec (fun x : D => x.1.1) := Primrec.fst.comp Primrec.fst
  have hstage := (oracleStage_computable A).comp (hs.pair (he.pair hm)).computableIn
  have ho : ComputableIn {charOracle A} o := hstage.of_eq (fun x => rfl)
  let b₀ : D → BallPair := fun x => (r x).getD ((0, 0), (0, 0))
  let n₀ : D → ℕ := fun x => (o x).getD 0
  have hb₀ : ComputableIn {charOracle A} b₀ :=
    Primrec.option_getD.to_comp.computableIn₂.comp hr
      (ComputableIn.const ((0, 0), (0, 0)))
  have hn₀ : ComputableIn {charOracle A} n₀ :=
    Primrec.option_getD.to_comp.computableIn₂.comp ho (ComputableIn.const 0)
  have htest := (computableIn_certificateCheck q A hq).comp
    (ComputableIn.id.pair (hb₀.pair hn₀))
  have hrSome := Primrec.option_isSome.to_comp.computableIn.comp hr
  have hoSome := Primrec.option_isSome.to_comp.computableIn.comp ho
  have hgood := Primrec.and.to_comp.computableIn₂.comp
    (Primrec.and.to_comp.computableIn₂.comp hrSome hoSome) htest
  have hpost : Computable (fun p : Bool × (ℕ × ℚ) => cond p.1 (some p.2) none) :=
    Computable.cond Computable.fst (Computable.option_some.comp Computable.snd)
      (Computable.const none)
  have hresult := hpost.computableIn.comp (hgood.pair (ComputableIn.snd.comp hb₀))
  refine (hresult.of_eq (g := fun x : D => certificateSearchTest q e_R A x.1 x.2) ?_).to₂
  intro x
  dsimp [b₀, n₀, r, o, certificateSearchTest]
  cases e_R x.2.unpair.1 with
  | none => simp
  | some bc =>
    rcases bc with ⟨b, c⟩
    cases oracleStage A x.2.unpair.2.unpair.2.unpair.1 x.1.1 x.2.unpair.2.unpair.1 with
    | none => simp
    | some n => simp [Bool.cond_eq_ite]

/-- Whatever the certificate search outputs is a certified output ball. -/
private lemma isCertifiedOutput_of_mem_search
    (P : Presentation X) (A : Set ℕ) (R : BallPair → Prop)
    (q : (ℕ × ℕ) × ℕ → ℚ) (e_R : ℕ → Option BallPair)
    (hqerr : ∀ ij p, |(q (ij, p) : ℝ) - dist (P.ι ij.1) (P.ι ij.2)| < dyadicRadius p)
    (heR : ∀ w, R w ↔ ∃ t, e_R t = some w) (e p : ℕ) (c : ℕ × ℚ)
    (hc : c ∈ Nat.rfindOpt (certificateSearchTest q e_R A (e, p))) :
    IsCertifiedOutput P A R e p c := by
  obtain ⟨z, hz⟩ := Nat.rfindOpt_spec hc
  have hz : certificateSearchTest q e_R A (e, p) z = some c := hz
  obtain ⟨t, m, s, k, rfl⟩ : ∃ t m s k, z = t.pair (m.pair (s.pair k)) :=
    ⟨z.unpair.1, z.unpair.2.unpair.1, z.unpair.2.unpair.2.unpair.1,
      z.unpair.2.unpair.2.unpair.2, by simp⟩
  simp only [certificateSearchTest, Nat.unpair_pair] at hz
  split at hz
  · rename_i b c' n hb hs'
    split at hz
    · rename_i hcheck
      injection hz with hz'
      subst c'
      simp only [certificateCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hcert := add_inv_two_pow_lt_iff.mp hcheck.2
      have herr := (abs_lt.mp (hqerr (n, b.1) k)).1
      refine ⟨b, m, n, (heR (b, c)).2 ⟨t, hb⟩, (mem_oracleEval_iff A e m n).2 ⟨s, hs'⟩, ?_,
        hcheck.1.1, lt_inv_two_pow_iff.mp hcheck.1.2⟩
      linarith
    · contradiction
  · contradiction

/-- Every certified output ball is found by the certificate search. -/
private lemma exists_mem_search_of_isCertifiedOutput
    (P : Presentation X) (A : Set ℕ) (R : BallPair → Prop)
    (q : (ℕ × ℕ) × ℕ → ℚ) (e_R : ℕ → Option BallPair)
    (hqerr : ∀ ij p, |(q (ij, p) : ℝ) - dist (P.ι ij.1) (P.ι ij.2)| < dyadicRadius p)
    (heR : ∀ w, R w ↔ ∃ t, e_R t = some w) (e p : ℕ)
    (hex : ∃ c, IsCertifiedOutput P A R e p c) :
    ∃ c, c ∈ Nat.rfindOpt (certificateSearchTest q e_R A (e, p)) := by
  obtain ⟨c, b, m, n, hR, hn, hdist, hpos, hrad⟩ := hex
  obtain ⟨t, ht⟩ := (heR (b, c)).mp hR
  obtain ⟨s, hs⟩ := (mem_oracleEval_iff A e m n).mp hn
  obtain ⟨k, hk⟩ := exists_dyadicRadius_lt
    (show 0 < ((b.2 : ℝ) - dist (P.ι n) (P.ι b.1) - dyadicRadius m) / 2 by linarith)
  have hcheck : certificateCheck q p m k n b c = true := by
    simp only [certificateCheck, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hpos, lt_inv_two_pow_iff.mpr hrad⟩, add_inv_two_pow_lt_iff.mpr ?_⟩
    have herr := (abs_lt.mp (hqerr (n, b.1) k)).2
    linarith
  have hmem : c ∈ certificateSearchTest q e_R A (e, p) (t.pair (m.pair (s.pair k))) := by
    rw [Option.mem_def]
    simp only [certificateSearchTest, Nat.unpair_pair, ht, hs, hcheck, ↓reduceIte]
  have hdom : (Nat.rfindOpt (certificateSearchTest q e_R A (e, p))).Dom :=
    Nat.rfindOpt_dom.mpr ⟨_, c, hmem⟩
  exact ⟨_, Part.get_mem hdom⟩

/-- For a represented relation over a computable presentation, one relatively partial
recursive search finds, from an oracle program `e` and a precision `p`, exactly the certified
output balls. -/
private lemma exists_partrecIn_certified_search
    (P : Presentation X) (A : Set ℕ) (hP : ComputablePresentationIn P A)
    (R : BallPair → Prop) (hR : IsREIn A R) :
    ∃ E : ℕ × ℕ →. ℕ × ℚ, PartrecIn {charOracle A} E ∧
      (∀ e p c, c ∈ E (e, p) → IsCertifiedOutput P A R e p c) ∧
      ∀ e p, (∃ c, IsCertifiedOutput P A R e p c) → ∃ c, c ∈ E (e, p) := by
  obtain ⟨q, hq, hqerr⟩ := hP
  obtain ⟨e_R, heR_comp, heR⟩ := (relative_enumeration A R).mp hR
  refine ⟨fun ep => Nat.rfindOpt (certificateSearchTest q e_R A ep),
    PartrecIn.rfindOpt (computableIn₂_certificateSearchTest q e_R A hq heR_comp), ?_, ?_⟩
  · intro e p c hc
    exact isCertifiedOutput_of_mem_search P A R q e_R hqerr heR e p c hc
  · intro e p hex
    exact exists_mem_search_of_isCertifiedOutput P A R q e_R hqerr heR e p hex

/-- Completeness of a represented relation gives, for every valid name index and precision,
a certified output ball. -/
private lemma exists_isCertifiedOutput
    (P : Presentation X) (Q : Presentation Y) (A : Set ℕ)
    (f : X → Y) (R : BallPair → Prop)
    (hsound : ∀ b c, R (b, c) → 0 < b.2 ∧ 0 < c.2 ∧ f '' basicBall P b ⊆ basicBall Q c)
    (hcomp : ∀ x c, f x ∈ basicBall Q c → ∃ b, R (b, c) ∧ x ∈ basicBall P b)
    (x : X) (a : ℕ → ℕ) (e : ℕ)
    (ha : IsCauchyName P x a) (he : ∀ p, a p ∈ oracleEval A e p) (p : ℕ) :
    ∃ c, IsCertifiedOutput P A R e p c := by
  obtain ⟨c, hc, hcr⟩ := exists_basicBall_radius_lt Q (f x) p
  obtain ⟨b, hR, hb⟩ := hcomp x c hc
  have hxb : dist x (P.ι b.1) < b.2 := Metric.mem_ball.mp hb
  obtain ⟨m, hm⟩ := exists_dyadicRadius_lt
    (show 0 < ((b.2 : ℝ) - dist x (P.ι b.1)) / 4 by linarith)
  refine ⟨c, b, m, a m, hR, he m, ?_, (hsound b c hR).2.1, hcr⟩
  have hname := ha m
  have htri := dist_triangle (P.ι (a m)) x (P.ι b.1)
  linarith

/-- A certified output ball for a valid name index is within the requested precision of the
image point. -/
private lemma dist_lt_of_isCertifiedOutput
    (P : Presentation X) (Q : Presentation Y) (A : Set ℕ)
    (f : X → Y) (R : BallPair → Prop)
    (hsound : ∀ b c, R (b, c) → 0 < b.2 ∧ 0 < c.2 ∧ f '' basicBall P b ⊆ basicBall Q c)
    (x : X) (a : ℕ → ℕ) (e : ℕ) (ha : IsCauchyName P x a)
    (he : ∀ p, a p ∈ oracleEval A e p) {p : ℕ} {c : ℕ × ℚ}
    (hc : IsCertifiedOutput P A R e p c) :
    dist (Q.ι c.1) (f x) < dyadicRadius p := by
  obtain ⟨b, m, n, hR, hn, hcert, -, hrad⟩ := hc
  obtain rfl : a m = n := Part.mem_unique (he m) hn
  have hname := ha m
  have hxb : x ∈ basicBall P b := by
    refine Metric.mem_ball.mpr ?_
    have htri := dist_triangle_left x (P.ι b.1) (P.ι (a m))
    linarith
  have hfx := (hsound b c hR).2.2 (Set.mem_image_of_mem f hxb)
  exact (Metric.mem_ball'.mp hfx).trans hrad

/-- One relative partial algorithm computes output approximants uniformly from an index
of a valid input name and a precision; it is total on every valid name index.
Blueprint node `metric:evaluation`. -/
theorem eval_computable_names_uniform (P : Presentation X) (Q : Presentation Y) (A : Set ℕ)
    (hP : ComputablePresentationIn P A)
    (f : X → Y) (hf : IsRepresentedMapIn P Q A f) :
    ∃ E : ℕ × ℕ →. ℕ, PartrecIn {charOracle A} E ∧
      ∀ x a e, IsCauchyName P x a → (∀ p, a p ∈ oracleEval A e p) →
        ∀ p, ∃ i, i ∈ E (e, p) ∧ dist (Q.ι i) (f x) < dyadicRadius p := by
  obtain ⟨R, hR, hsound, hcomp⟩ := hf
  obtain ⟨E, hE, hE_sound, hE_complete⟩ := exists_partrecIn_certified_search P A hP R hR
  refine ⟨fun p => (E p).map (fun c => c.1),
    hE.map (ComputableIn₂.mk (Computable.fst.comp Computable.snd).computableIn), ?_⟩
  intro x a e ha he p
  obtain ⟨c, hc⟩ := exists_isCertifiedOutput P Q A f R hsound hcomp x a e ha he p
  obtain ⟨c', hc'⟩ := hE_complete e p ⟨c, hc⟩
  exact ⟨c'.1, (Part.mem_map_iff _).mpr ⟨c', hc', rfl⟩,
    dist_lt_of_isCertifiedOutput P Q A f R hsound x a e ha he (hE_sound e p c' hc')⟩

/-! ### Composition of represented maps -/

/-- The entry of the composed relation at a pair of listed entries: the outer pair of the
first entry and the inner pair of the second one, when the middle balls agree. -/
private def composeEntry (o₁ o₂ : Option BallPair) : Option BallPair :=
  o₁.bind fun p₁ => o₂.bind fun p₂ => if p₁.2 = p₂.1 then some (p₁.1, p₂.2) else none

/-- Composition of listed entries is primitive recursive. -/
private lemma primrec₂_composeEntry : Primrec₂ composeEntry := by
  have hcond : PrimrecPred fun r : ((Option BallPair × Option BallPair) × BallPair) × BallPair =>
      r.1.2.2 = r.2.1 :=
    Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)
  have hmatch : Primrec fun r : ((Option BallPair × Option BallPair) × BallPair) × BallPair =>
      if r.1.2.2 = r.2.1 then some (r.1.2.1, r.2.2) else none :=
    Primrec.ite hcond
      (Primrec.option_some.comp (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd)))
      (Primrec.const none)
  exact (Primrec.option_bind Primrec.fst
    (Primrec.option_bind (Primrec.snd.comp Primrec.fst) hmatch.to₂).to₂).of_eq fun p => rfl

/-- The relational composite of two relatively enumerable relations on ball pairs is
relatively enumerable. -/
private lemma isREIn_relationComp (A : Set ℕ) {Sf Sg : BallPair → Prop}
    (hSf : IsREIn A Sf) (hSg : IsREIn A Sg) :
    IsREIn A fun bd : BallPair => ∃ c, Sf (bd.1, c) ∧ Sg (c, bd.2) := by
  obtain ⟨ef, hef, hf⟩ := (relative_enumeration A Sf).mp hSf
  obtain ⟨eg, heg, hg⟩ := (relative_enumeration A Sg).mp hSg
  refine (relative_enumeration A _).mpr
    ⟨fun t => composeEntry (ef t.unpair.1) (eg t.unpair.2), ?_, ?_⟩
  · have h₁ : ComputableIn {charOracle A} fun t : ℕ => ef t.unpair.1 :=
      hef.comp (Primrec.fst.comp Primrec.unpair).to_comp.computableIn
    have h₂ : ComputableIn {charOracle A} fun t : ℕ => eg t.unpair.2 :=
      heg.comp (Primrec.snd.comp Primrec.unpair).to_comp.computableIn
    exact primrec₂_composeEntry.to_comp.computableIn₂.comp h₁ h₂
  · intro w
    constructor
    · rintro ⟨c, hcf, hcg⟩
      obtain ⟨tf, htf⟩ := (hf _).mp hcf
      obtain ⟨tg, htg⟩ := (hg _).mp hcg
      exact ⟨tf.pair tg, by simp [composeEntry, htf, htg]⟩
    · rintro ⟨t, ht⟩
      have ht : composeEntry (ef t.unpair.1) (eg t.unpair.2) = some w := ht
      rcases h_ef : ef t.unpair.1 with _ | ⟨b, c⟩
      · simp [composeEntry, h_ef] at ht
      rcases h_eg : eg t.unpair.2 with _ | ⟨c', d⟩
      · simp [composeEntry, h_ef, h_eg] at ht
      by_cases hcc : c = c'
      · subst hcc
        have hw : (b, d) = w := by simpa [composeEntry, h_ef, h_eg] using ht
        subst hw
        exact ⟨c, (hf _).mpr ⟨_, h_ef⟩, (hg _).mpr ⟨_, h_eg⟩⟩
      · simp [composeEntry, h_ef, h_eg, hcc] at ht

/-- Composition preserves representations; the composite relation is built from the listed
balls. Blueprint node `metric:evaluation`. -/
theorem eval_computable_names_comp (P : Presentation X) (Q : Presentation Y) (R : Presentation Z)
    (A : Set ℕ) (f : X → Y) (g : Y → Z) (hf : IsRepresentedMapIn P Q A f)
    (hg : IsRepresentedMapIn Q R A g) : IsRepresentedMapIn P R A (g ∘ f) := by
  obtain ⟨Sf, hSf, hfsound, hfcomplete⟩ := hf
  obtain ⟨Sg, hSg, hgsound, hgcomplete⟩ := hg
  refine ⟨fun bd => ∃ c, Sf (bd.1, c) ∧ Sg (c, bd.2), isREIn_relationComp A hSf hSg, ?_, ?_⟩
  · rintro b d ⟨c, hbc, hcd⟩
    obtain ⟨hb, -, hfimg⟩ := hfsound b c hbc
    obtain ⟨-, hd, hgimg⟩ := hgsound c d hcd
    refine ⟨hb, hd, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hgimg (Set.mem_image_of_mem g (hfimg (Set.mem_image_of_mem f hx)))
  · intro x d hd
    obtain ⟨c, hcd, hc⟩ := hgcomplete (f x) d hd
    obtain ⟨b, hbc, hb⟩ := hfcomplete x c hc
    exact ⟨b, ⟨c, hbc, hcd⟩, hb⟩

/-- An admissible oracle computes the fixed metric table, a represented dynamics, and
each of the specified finitely many real potentials. Blueprint node `metric:admissible`. -/
def IsAdmissible {k : ℕ} (P : Presentation X) (T : X → X)
    (v : Fin k → X → ℝ) (A : Set ℕ) : Prop :=
  ComputablePresentationIn P A ∧ IsRepresentedMapIn P P A T ∧
    ∀ j, IsRepresentedMapIn P realPresentation A (v j)

end Kolmogorov.PointToSet
