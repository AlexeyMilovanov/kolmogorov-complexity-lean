/-
Copyright (c) 2024 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The KolmogorovMathlib Authors
-/
import KolmogorovMathlib.StoppingComplexity.PathBudget
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.LSCApproximation
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable

/-!
# Time semimeasures and request streams

Time semimeasures (blueprint part 01, section F3; part 03, sections 1 and 4.1). A time
semimeasure is a function `ν : BitString → ℝ≥0∞` whose sum over the `|v| + 1` prefixes of
every word `v` (the empty word and `v` included) is at most `1` (condition (TS)); this finite
condition is equivalent to the bound on every infinite path (F3-TS-PATH) and is *not* the
continuous-semimeasure inequality. Lower semicomputability is the repository's uniform dyadic
approximation `IsLSC` (F3-DEF). The pointwise supremum of an increasing sequence of time
semimeasures is a time semimeasure (03 §1, `timeSemimeasure_of_monotoneApprox`).

The effective representation used by the diagonalization is a computable stage enumerator of
dyadic requests `(z, k, L)` meaning "add `k / 2^L` at `z`", at most one per stage
(`RequestStream`, F3-STREAM); its cumulative table `streamStageMass` satisfies the path budget
at every stage (`IsBudgetedRequestStream`), and `requestLimit` is its limit. F3.1 says the
limit is a lower semicomputable time semimeasure, F3.2 that disjoint input-tape tags
`natCode c = 1^c 0` cost no extra mass, and 03 §4.1 that every lower semicomputable time
semimeasure is the limit of such a stream (normal form).

Recorded deviations: values in `ℝ≥0∞` (repository convention); one request per stage; the
`(z, k, L)` request form (deviations.tsv F3-DEF, F3-STREAM).
-/

open scoped ENNReal

namespace Kolmogorov

/-! ### Time semimeasures -/

/-- The sum of `ν` over the `|v| + 1` prefixes of `v` (`[]` and `v` included): the left-hand
side of condition (TS). Blueprint 01 F3-DEF. -/
noncomputable def prefixLoad (ν : BitString → ℝ≥0∞) (v : BitString) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (v.length + 1), ν (v.take k)

/-- A *time semimeasure*: the prefix sums of `ν` are bounded by `1` at every word
(condition (TS)). Blueprint 01 F3-DEF. -/
def IsTimeSemimeasure (ν : BitString → ℝ≥0∞) : Prop := ∀ v, prefixLoad ν v ≤ 1

/-- Every value of a time semimeasure is at most `1`. Blueprint 01 F3-DEF. -/
theorem IsTimeSemimeasure.le_one {ν : BitString → ℝ≥0∞} (h : IsTimeSemimeasure ν)
    (v : BitString) : ν v ≤ 1 := by
  calc ν v = ν (v.take v.length) := by rw [List.take_length]
    _ ≤ prefixLoad ν v :=
        Finset.single_le_sum (f := fun k => ν (v.take k)) (fun _ _ => zero_le)
          (Finset.mem_range.2 (Nat.lt_succ_self _))
    _ ≤ 1 := h v

/-- Every value of a time semimeasure is finite. Blueprint 01 F3-DEF. -/
theorem IsTimeSemimeasure.ne_top {ν : BitString → ℝ≥0∞} (h : IsTimeSemimeasure ν)
    (v : BitString) : ν v ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (h.le_one v)

/-- Condition (TS) is equivalent to the bound `≤ 1` on the series of prefix weights along
every infinite path. Blueprint 01 F3 (F3-TS-PATH). -/
theorem isTimeSemimeasure_iff_forall_cantorSeq (ν : BitString → ℝ≥0∞) :
    IsTimeSemimeasure ν ↔ ∀ w : CantorSeq, ∑' k, ν (cantorPrefix w k) ≤ 1 := by
  constructor
  · intro h w
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    calc ∑ k ∈ Finset.range n, ν (cantorPrefix w k)
        ≤ ∑ k ∈ Finset.range (n + 1), ν (cantorPrefix w k) :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ n))
      _ = prefixLoad ν (cantorPrefix w n) := by
          unfold prefixLoad
          rw [cantorPrefix_length]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [cantorPrefix_take w k n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
      _ ≤ 1 := h _
  · intro h v
    set w : CantorSeq := prependCantor v fun _ => false
    have hw : cantorPrefix w v.length = v := cantorPrefix_prepend v _
    calc prefixLoad ν v = ∑ k ∈ Finset.range (v.length + 1), ν (cantorPrefix w k) := by
          unfold prefixLoad
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [← cantorPrefix_take w k v.length (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), hw]
      _ ≤ ∑' k, ν (cantorPrefix w k) := ENNReal.sum_le_tsum _
      _ ≤ 1 := h w

/-- A *lower semicomputable time semimeasure*: a time semimeasure with a uniform computable
monotone dyadic approximation (the repository's `IsLSC`, context ignored).
Blueprint 01 F3-DEF. -/
def IsLowerSemicomputableTimeSemimeasure (ν : BitString → ℝ≥0∞) : Prop :=
  IsTimeSemimeasure ν ∧ IsLSC fun x _ => ν x

/-- The pointwise supremum of an increasing sequence of time semimeasures is a time
semimeasure: a finite sum of suprema is the supremum of the finite sums.
Blueprint 03 §1 `timeSemimeasure_of_monotoneApprox` (03-1-MONO). -/
theorem isTimeSemimeasure_iSup {ν : ℕ → BitString → ℝ≥0∞} (hmono : Monotone ν)
    (h : ∀ s, IsTimeSemimeasure (ν s)) : IsTimeSemimeasure fun x => ⨆ s, ν s x := by
  intro v
  unfold prefixLoad
  dsimp only
  rw [ENNReal.finsetSum_iSup_of_monotone (f := fun k s => ν s (v.take k))
    fun k _ _ hss' => hmono hss' _]
  exact iSup_le fun s => h s v

/-! ### Request streams -/

/-- A dyadic request `(z, k, L)`: add the mass `k / 2^L` at the word `z`.
Blueprint 03 §4.1 (F3-STREAM). -/
abbrev DyadicRequest := BitString × ℕ × ℕ

/-- The rational mass `k / 2^L` of the request `(z, k, L)`. Blueprint 03 §4.1 (F3-STREAM). -/
def DyadicRequest.weight (r : DyadicRequest) : ℚ := (r.2.1 : ℚ) / 2 ^ r.2.2

/-- A stage enumerator of dyadic requests: at most one request per stage (`none` is an idle
stage). Blueprint 01 F3 / 03 §4.1 (F3-STREAM). -/
abbrev RequestStream := ℕ → Option DyadicRequest

/-- The rational mass requested at `z` by the stages `< s`. Blueprint 01 F3 (F3-STREAM). -/
def streamStageMass (ρ : RequestStream) (s : ℕ) (z : BitString) : ℚ :=
  ((((List.range s).filterMap ρ).filter fun r => decide (r.1 = z)).map
    DyadicRequest.weight).sum

/-- The cumulative load at stage `s` along the prefixes of `v` (`[]` and `v` included).
Blueprint 01 F3 (F3-STREAM). -/
def streamStageLoad (ρ : RequestStream) (s : ℕ) (v : BitString) : ℚ :=
  ∑ k ∈ Finset.range (v.length + 1), streamStageMass ρ s (v.take k)

/-- A *budgeted* request stream: the finite cumulative table satisfies the path budget `1`
at every stage. Blueprint 01 F3 / 03 §1 (F3-STREAM). -/
def IsBudgetedRequestStream (ρ : RequestStream) : Prop := ∀ s v, streamStageLoad ρ s v ≤ 1

/-- The limit of the cumulative table: the supremum over the stages of the requested mass.
Blueprint 01 F3 (F3-STREAM). -/
noncomputable def requestLimit (ρ : RequestStream) (z : BitString) : ℝ≥0∞ :=
  ⨆ s, ENNReal.ofReal ((streamStageMass ρ s z : ℚ) : ℝ)

/-- The mass that one stage output puts at `z`: the weight of the request when it is placed
at `z`, and `0` for an idle stage or a request at another word. -/
private def stageMass (o : Option DyadicRequest) (z : BitString) : ℚ :=
  o.elim 0 fun r => if r.1 = z then r.weight else 0

/-- Request weights are nonnegative. -/
private theorem DyadicRequest.weight_nonneg (r : DyadicRequest) : 0 ≤ r.weight := by
  unfold DyadicRequest.weight
  positivity

/-- The mass of one stage output is nonnegative. -/
private theorem stageMass_nonneg (o : Option DyadicRequest) (z : BitString) :
    0 ≤ stageMass o z := by
  cases o with
  | none => exact le_rfl
  | some r =>
    by_cases h : r.1 = z
    · simp only [stageMass, Option.elim, h, ite_true]
      exact r.weight_nonneg
    · simp [stageMass, h]

/-- The cumulative table is the sum, over the stages `t < s`, of the mass that stage `t`
puts at `z`. -/
private theorem streamStageMass_eq_sum (ρ : RequestStream) (s : ℕ) (z : BitString) :
    streamStageMass ρ s z = ∑ t ∈ Finset.range s, stageMass (ρ t) z := by
  induction s with
  | zero => simp [streamStageMass]
  | succ s ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold streamStageMass
    rw [List.range_succ, List.filterMap_append, List.filter_append, List.map_append,
      List.sum_append]
    congr 1
    cases h : ρ s with
    | none => simp [stageMass, h]
    | some r => by_cases hr : r.1 = z <;> simp [stageMass, h, hr]

/-- The cumulative mass at a word is nondecreasing in the stage.
Blueprint 01 F3 (F3-STREAM). -/
theorem streamStageMass_mono (ρ : RequestStream) {s s' : ℕ} (h : s ≤ s') (z : BitString) :
    streamStageMass ρ s z ≤ streamStageMass ρ s' z := by
  rw [streamStageMass_eq_sum, streamStageMass_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
    fun t _ _ => stageMass_nonneg _ _

/-- The cumulative mass is nonnegative. Blueprint 01 F3 (F3-STREAM). -/
theorem streamStageMass_nonneg (ρ : RequestStream) (s : ℕ) (z : BitString) :
    0 ≤ streamStageMass ρ s z := by
  rw [streamStageMass_eq_sum]
  exact Finset.sum_nonneg fun t _ => stageMass_nonneg _ _

/-- The weight `k / 2^L` of a request is computable. -/
private theorem computable_weight : Computable DyadicRequest.weight :=
  computable_of_num_den (N := fun r : DyadicRequest => (r.2.1 : ℤ)) (D := fun r => 2 ^ r.2.2)
    ((ComputableReals.primrec_natCastInt.to_comp.comp
      (Computable.fst.comp Computable.snd)).of_eq fun _ => rfl)
    ((comp_pow.comp (Computable.snd.comp Computable.snd)).of_eq fun _ => rfl)
    (fun _ => Nat.two_pow_pos _) (fun r => by simp [DyadicRequest.weight])

/-- The mass that a stage output puts at a word is computable. -/
private theorem computable_stageMass :
    Computable fun p : Option DyadicRequest × BitString => stageMass p.1 p.2 := by
  have hg : Computable₂ fun (p : Option DyadicRequest × BitString) (r : DyadicRequest) =>
      bif decide (r.1 = p.2) then r.weight else 0 :=
    (Computable.cond ((PrimrecRel.decide Primrec.eq).to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.fst))
      (computable_weight.comp Computable.snd) (Computable.const 0)).of_eq fun _ => rfl
  refine (Computable.option_casesOn Computable.fst (Computable.const (0 : ℚ)) hg).of_eq
    fun p => ?_
  obtain ⟨o, z⟩ := p
  cases o with
  | none => rfl
  | some r => by_cases h : r.1 = z <;> simp [stageMass, h]

/-- For a computable stream the cumulative table is computable in `(s, z)`.
Blueprint 01 F3 (F3-STREAM). -/
theorem streamStageMass_computable {ρ : RequestStream} (hρ : Computable ρ) :
    Computable fun a : ℕ × BitString => streamStageMass ρ a.1 a.2 := by
  have hstep : Computable₂ fun (a : ℕ × BitString) (p : ℕ × ℚ) =>
      p.2 + stageMass (ρ p.1) a.2 :=
    (computable₂_ratAdd.comp (Computable.snd.comp Computable.snd)
      (computable_stageMass.comp ((hρ.comp (Computable.fst.comp Computable.snd)).pair
        (Computable.snd.comp Computable.fst)))).of_eq fun _ => rfl
  refine (Computable.nat_rec Computable.fst (Computable.const (0 : ℚ)) hstep).of_eq
    fun a => ?_
  obtain ⟨s, z⟩ := a
  rw [streamStageMass_eq_sum]
  induction s with
  | zero => simp
  | succ s ih => rw [Finset.sum_range_succ, ← ih]

/-- Limit budget: the limit of a computable budgeted request stream is a lower semicomputable
time semimeasure. Blueprint 01 F3.1. -/
theorem requestLimit_isLowerSemicomputableTimeSemimeasure {ρ : RequestStream}
    (hρ : Computable ρ) (hb : IsBudgetedRequestStream ρ) :
    IsLowerSemicomputableTimeSemimeasure (requestLimit ρ) := by
  refine ⟨isTimeSemimeasure_iSup
    (ν := fun s z => ENNReal.ofReal ((streamStageMass ρ s z : ℚ) : ℝ))
    (fun s s' hss' z => ENNReal.ofReal_le_ofReal (Rat.cast_le.2 (streamStageMass_mono ρ hss' z)))
    (fun s v => ?_), ?_⟩
  · unfold prefixLoad
    dsimp only
    rw [← ENNReal.ofReal_sum_of_nonneg
      (f := fun k => ((streamStageMass ρ s (v.take k) : ℚ) : ℝ))
      fun k _ => Rat.cast_nonneg.2 (streamStageMass_nonneg ρ s _), ENNReal.ofReal_le_one]
    have hv := hb s v
    unfold streamStageLoad at hv
    exact_mod_cast hv
  · refine ⟨fun s x _ => ratDyadicFloor (streamStageMass ρ s x) s, fun s x _ => ?_,
      fun x _ => ?_, ?_⟩
    · exact dyadicValue_ratDyadicFloor_mono_of_le (streamStageMass_mono ρ (Nat.le_succ s) x) s
    · exact iSup_dyadicValue_ratDyadicFloor fun s s' h => streamStageMass_mono ρ h x
    · exact (computable_ratDyadicFloor.comp
        ((streamStageMass_computable hρ).comp
          (Computable.fst.pair (Computable.fst.comp Computable.snd)))
        Computable.fst).of_eq fun _ => rfl

/-- If the only request at `z` is `(z, 1, n)` (at stage `s`), the limit at `z` is `2^{-n}`.
Blueprint 01 F3.1 (single-request case used by the diagonalization). -/
theorem requestLimit_eq_of_single_request {ρ : RequestStream} {s n : ℕ} {z : BitString}
    (hs : ρ s = some (z, 1, n)) (huniq : ∀ s' r, ρ s' = some r → r.1 = z → s' = s) :
    requestLimit ρ z = (2 : ℝ≥0∞)⁻¹ ^ n := by
  have hzero : ∀ t, t ≠ s → stageMass (ρ t) z = 0 := by
    intro t ht
    cases h : ρ t with
    | none => rfl
    | some r =>
      have hr : r.1 ≠ z := fun hr => ht (huniq t r h hr)
      simp [stageMass, hr]
  have hmass : ∀ s', streamStageMass ρ s' z = if s < s' then (1 / 2 ^ n : ℚ) else 0 := by
    intro s'
    rw [streamStageMass_eq_sum]
    split_ifs with hss'
    · rw [Finset.sum_eq_single_of_mem s (Finset.mem_range.2 hss') fun t _ ht => hzero t ht]
      simp [stageMass, hs, DyadicRequest.weight]
    · exact Finset.sum_eq_zero fun t ht =>
        hzero t fun hts => hss' (hts ▸ Finset.mem_range.1 ht)
  have hval : ENNReal.ofReal (((1 / 2 ^ n : ℚ)) : ℝ) = (2 : ℝ≥0∞)⁻¹ ^ n := by
    have h1 : (((1 / 2 ^ n : ℚ)) : ℝ) = ((2 : ℝ)⁻¹) ^ n := by
      rw [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat, one_div, ← inv_pow]
    rw [h1, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  unfold requestLimit
  refine le_antisymm (iSup_le fun s' => ?_) (le_iSup_of_le (s + 1) ?_)
  · rw [hmass s']
    split_ifs
    · exact hval.le
    · simp
  · rw [hmass (s + 1), ite_eq_left (Nat.lt_succ_self s), hval]

/-- Disjoint tags cost no extra mass: if every request lies below a tag `natCode c = 1^c 0`
and every tagged local table satisfies the path budget `1`, the whole stream is budgeted.
Blueprint 01 F3.2. -/
theorem isBudgetedRequestStream_of_tagged {ρ : RequestStream}
    (htag : ∀ s r, ρ s = some r → ∃ c x, r.1 = natCode c ++ x)
    (hloc : ∀ c s v, streamStageLoad ρ s (natCode c ++ v) ≤ 1) :
    IsBudgetedRequestStream ρ := by
  intro s v
  by_cases hv : ∃ c, natCode c <+: v
  · obtain ⟨c, v', rfl⟩ := hv
    exact hloc c s v'
  · push Not at hv
    have hzero : ∀ k, streamStageMass ρ s (v.take k) = 0 := by
      intro k
      rw [streamStageMass_eq_sum]
      refine Finset.sum_eq_zero fun t _ => ?_
      cases h : ρ t with
      | none => rfl
      | some r =>
        have hr : r.1 ≠ v.take k := by
          intro hr
          obtain ⟨c, x, hcx⟩ := htag t r h
          have h1 : r.1 <+: v := by rw [hr]; exact List.take_prefix k v
          rw [hcx] at h1
          exact hv c ((List.prefix_append _ _).trans h1)
        simp [stageMass, hr]
    unfold streamStageLoad
    simp [hzero]

/-- The rational `n / 2^k` embeds in `ℝ≥0∞` as the dyadic value of `n` at scale `k`. -/
private theorem ofReal_natCast_div_two_pow (n k : ℕ) :
    ENNReal.ofReal ((n : ℝ) / 2 ^ k) = dyadicValue n k := by
  rw [dyadicValue, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- The request stream of the dyadic increments of an `IsLSC` numerator table: stage `t`
codes a pair `(z, k)` and requests the `k`-th increment `incNum approx k z [] / 2^k` of the
approximation at `z` (03 §4.1: the positive coordinate increments of `b_{s+1} - b_s`, one per
stage). -/
private def lscRequestStream (approx : ℕ → BitString → BitString → ℕ) : RequestStream :=
  fun t => (evOut t).map fun z => (z, incNum approx (evK t) z [], evK t)

/-- The increment stream of a computable numerator table is computable. -/
private theorem computable_lscRequestStream {approx : ℕ → BitString → BitString → ℕ}
    (hcomp : Computable fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2) :
    Computable (lscRequestStream approx) := by
  have hinc : Computable fun p : ℕ × BitString => incNum approx (evK p.1) p.2 [] :=
    ((incNum_computable hcomp).comp ((evK_computable.comp Computable.fst).pair
      (Computable.snd.pair (Computable.const [])))).of_eq fun _ => rfl
  have hg : Computable₂ fun (t : ℕ) (z : BitString) => (z, incNum approx (evK t) z [], evK t) :=
    (Computable.snd.pair (hinc.pair (evK_computable.comp Computable.fst))).of_eq fun _ => rfl
  exact (Computable.option_map evOut_computable hg).of_eq fun _ => rfl

/-- A stage that enumerates an increment at `z` is the pair of the code of `z` and the index
of the increment. -/
private theorem eq_pair_of_evOut_eq_some {t : ℕ} {z : BitString} (h : evOut t = some z) :
    t = Nat.pair (Encodable.encode z) (evK t) := by
  have h1 : Encodable.encode z = (Nat.unpair t).1 := Encodable.mem_decode₂.1 h
  rw [evK, h1, Nat.pair_unpair]

/-- The stage-`s` table of the increment stream at `z` is the sum of the increments at `z`
enumerated before stage `s`. -/
private theorem ofReal_streamStageMass_lscRequestStream
    (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (z : BitString) :
    ENNReal.ofReal ((streamStageMass (lscRequestStream approx) s z : ℚ) : ℝ) =
      ∑ t ∈ (Finset.range s).filter (fun t => evOut t = some z),
        dyadicValue (incNum approx (evK t) z []) (evK t) := by
  rw [streamStageMass_eq_sum, Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg
    fun t _ => Rat.cast_nonneg.2 (stageMass_nonneg _ _), Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold lscRequestStream
  cases h : evOut t with
  | none => simp [stageMass]
  | some z' =>
    by_cases hz : z' = z
    · subst hz
      simp [stageMass, DyadicRequest.weight, ofReal_natCast_div_two_pow]
    · simp [stageMass, hz]

/-- Every stage of the increment stream stays below the limit: its table at `z` is a finite
sub-sum of the increment series at `z`, whose sum is `ν z` (03 §4.1: each intermediate
function is bounded by the limit). -/
private theorem ofReal_streamStageMass_lscRequestStream_le {ν : BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
      ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = ν out) (s : ℕ) (z : BitString) :
    ENNReal.ofReal ((streamStageMass (lscRequestStream approx) s z : ℚ) : ℝ) ≤ ν z := by
  have htsum : ∑' k, dyadicValue (incNum approx k z []) k = ν z :=
    tsum_dyadicValue_incNum hmono hsup z []
  rw [ofReal_streamStageMass_lscRequestStream, ← htsum,
    ← Finset.sum_image (g := evK) (f := fun k => dyadicValue (incNum approx k z []) k)]
  · exact ENNReal.sum_le_tsum _
  · intro t ht t' ht' hk
    have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2
    have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 ht')).2
    rw [eq_pair_of_evOut_eq_some h1, eq_pair_of_evOut_eq_some h2, hk]

/-- The increment stream converges to `ν`: the first `K` increments at `z` are enumerated
before stage `pair (encode z) K`, so the stage tables reach every partial sum of the
increment series (03 §4.1: the supremum is the original function). -/
private theorem iSup_ofReal_streamStageMass_lscRequestStream {ν : BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
      ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = ν out) (z : BitString) :
    ⨆ s, ENNReal.ofReal ((streamStageMass (lscRequestStream approx) s z : ℚ) : ℝ) = ν z := by
  refine le_antisymm
    (iSup_le fun s => ofReal_streamStageMass_lscRequestStream_le hmono hsup s z) ?_
  have htsum : ∑' k, dyadicValue (incNum approx k z []) k = ν z :=
    tsum_dyadicValue_incNum hmono hsup z []
  rw [← htsum, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun K => le_iSup_of_le (Nat.pair (Encodable.encode z) K) ?_
  rw [ofReal_streamStageMass_lscRequestStream]
  have hinj : Set.InjOn (Nat.pair (Encodable.encode z)) (Finset.range K) :=
    fun k _ k' _ h => (Nat.pair_eq_pair.1 h).2
  calc ∑ k ∈ Finset.range K, dyadicValue (incNum approx k z []) k
      = ∑ t ∈ (Finset.range K).image (Nat.pair (Encodable.encode z)),
          dyadicValue (incNum approx (evK t) z []) (evK t) := by
        rw [Finset.sum_image hinj]
        simp [evK, Nat.unpair_pair]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset fun t ht => ?_
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ht
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2
          (Nat.pair_lt_pair_right _ (Finset.mem_range.1 hk)), ?_⟩
        simp [evOut, Nat.unpair_pair]

/-- Normal form: every lower semicomputable time semimeasure is the limit of a computable
budgeted request stream. Blueprint 03 §4.1 (03-4-1-NORMAL). -/
theorem exists_requestStream_of_isLowerSemicomputableTimeSemimeasure {ν : BitString → ℝ≥0∞}
    (hν : IsLowerSemicomputableTimeSemimeasure ν) :
    ∃ ρ : RequestStream, Computable ρ ∧ IsBudgetedRequestStream ρ ∧
      ∀ z, requestLimit ρ z = ν z := by
  obtain ⟨hts, approx, hmono, hsup, hcomp⟩ := hν
  refine ⟨lscRequestStream approx, computable_lscRequestStream hcomp, fun s v => ?_,
    fun z => iSup_ofReal_streamStageMass_lscRequestStream hmono hsup z⟩
  have hle : ENNReal.ofReal ((streamStageLoad (lscRequestStream approx) s v : ℚ) : ℝ) ≤ 1 := by
    unfold streamStageLoad
    rw [Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg
      fun k _ => Rat.cast_nonneg.2 (streamStageMass_nonneg _ _ _)]
    exact (Finset.sum_le_sum fun k _ =>
      ofReal_streamStageMass_lscRequestStream_le hmono hsup s _).trans (hts v)
  exact_mod_cast ENNReal.ofReal_le_one.1 hle

end Kolmogorov
