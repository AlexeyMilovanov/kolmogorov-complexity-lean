import KolmogorovMathlib.StoppingComplexity.UpperBoundStreams
import KolmogorovMathlib.StoppingComplexity.Universal
import KolmogorovMathlib.StoppingComplexity.MassDepth
import KolmogorovMathlib.Foundation.UnboundedSearch

/-!
# Level colouring and the upper bound on the stopping gap

Blueprint 03 §9 (Lemmas U1–U4) and 04 Interface UPPER (U-local). The level sets
`T_n = {z | M_stop(z) > 2^{-n}}` are uniformly c.e. and every input path meets fewer than `2^n` of
them; running the seed allocator on the fixed depth-`n` grid colours every member of `T_n` by one of
`2^n` atoms so that comparable distinct strings get different colours (U1). A c.e. antichain is the
exact input stopping set of a deterministic machine consuming no random bits (U2); one machine that
reads the unary code `1^n 0` and then exactly `n` random bits `j` recognises the colour class
`L_{n,j}`, whence `K_stop(z) ≤ 2n + 1 + C₀` on `T_n` (U3, unary route). With `n = ⌈m(z)⌉ + 1` this
bounds the stopping gap by `2⌈m(z)⌉ + 3 + C₀` (U-local), and a sequence with unbounded gaps has
unbounded mass depth (U4).

The prefix-complexity form of U3 (Remark 6, `K_stop(z) ≤ K(n) + n + C₀`) is parked and not stated
here.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### U1: the level sets and their effective enumeration -/

/-- The level set `T_n = {z | M_stop(z) > 2^{-n}}` of strings whose stopping probability under the
universal machine exceeds `2^{-n}`. Blueprint 03 Lemma U1 (`T_n`). -/
def stopLevelSet (n : ℕ) : Set BitString := {z | (2 : ℝ≥0∞)⁻¹ ^ n < univStopProb z}

/-- Membership in the level sets is computably enumerable, uniformly in the level `n`: a strict
rational lower threshold is detected from the lower approximation of `M_stop`.
Blueprint 03 Lemma U1 (`T_n` is uniformly c.e.). -/
theorem stopLevelSet_isRE : IsRE fun a : ℕ × BitString => a.2 ∈ stopLevelSet a.1 := by
  have hchk : Primrec fun b : (ℕ × BitString) × ℕ =>
      decide (2 ^ b.2 < univStopProbNum b.2 b.1.2 * 2 ^ b.1.1) :=
    (Primrec.nat_lt.comp (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.snd)
      (Primrec.nat_mul.comp
        (primrec_univStopProbNum.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))
        (nat_pow_primrec₂.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst)))).decide
  have hRE : IsRE fun b : (ℕ × BitString) × ℕ =>
      2 ^ b.2 < univStopProbNum b.2 b.1.2 * 2 ^ b.1.1 :=
    isRE_of_computable_bool _ _ (fun _ => decide_eq_true_iff) hchk.to_comp
  exact (IsRE.exists_encodable
    (R := fun (a : ℕ × BitString) (t : ℕ) => 2 ^ t < univStopProbNum t a.2 * 2 ^ a.1) hRE).of_iff
    fun a => (two_pow_neg_lt_univStopProb_iff a.1 a.2).symm

/-- A member of `T_n` has mass depth below `n`. Blueprint 03 Lemma U3
(`M_stop(z) > 2^{-n}` reads `m(z) < n`). -/
theorem massDepth_lt_of_mem_stopLevelSet {n : ℕ} {z : BitString} (hz : z ∈ stopLevelSet n) :
    massDepth z < n := by
  have hne : univStopProb z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (univStopProb_le_one z)
  have hr : (1 / 2 : ℝ) ^ n < (univStopProb z).toReal := by
    simpa [ENNReal.toReal_pow, ENNReal.toReal_inv] using
      (ENNReal.toReal_lt_toReal (by simp) hne).2 hz
  have hlog := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hr
  rw [Real.logb_pow, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)] at hlog
  unfold massDepth
  linarith

/-- Every input path contains fewer than `2^n` members of `T_n`: the prefixes of any `v` that lie in
`T_n` number less than `2^n`, otherwise their stopping probabilities would exceed the
time-semimeasure budget one. Counted with `Set.ncard` (membership in a c.e. set has no
`DecidablePred`).
Blueprint 03 Lemma U1 (fewer than `2^n` members of `T_n` on a path). -/
theorem ncard_stopLevelSet_prefixes_lt (n : ℕ) (v : BitString) :
    {k | k ≤ v.length ∧ v.take k ∈ stopLevelSet n}.ncard < 2 ^ n := by
  classical
  set K := (Finset.range (v.length + 1)).filter fun k => v.take k ∈ stopLevelSet n
  have hK : {k | k ≤ v.length ∧ v.take k ∈ stopLevelSet n} = ↑K := by
    ext k
    simp [K]
  rw [hK, Set.ncard_coe_finset]
  by_contra hge
  push_neg at hge
  have hne : K.Nonempty := Finset.card_pos.1 (lt_of_lt_of_le (Nat.two_pow_pos n) hge)
  have hsum : ∑ k ∈ K, univStopProb (v.take k) ≤ 1 :=
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
      (stopProb_isTimeSemimeasure univStopping v)
  have hlt : ∑ _k ∈ K, (2 : ℝ≥0∞)⁻¹ ^ n < ∑ k ∈ K, univStopProb (v.take k) :=
    ENNReal.sum_lt_sum_of_nonempty hne fun k hk => (Finset.mem_filter.1 hk).2
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have h1 : (1 : ℝ≥0∞) ≤ K.card * (2 : ℝ≥0∞)⁻¹ ^ n := by
    calc (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ n := by
          rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
      _ ≤ K.card * (2 : ℝ≥0∞)⁻¹ ^ n := by gcongr; exact_mod_cast hge
  exact lt_irrefl _ (h1.trans_lt (hlt.trans_le hsum))

/-- Stage-`t` lower approximation of `M_stop(z)`: the weights `2^{-|p|}` of the random prefixes
`p` of length at most `t` recognised as witnesses of the universal machine within `t` steps.
Blueprint 03 Lemma U1 (lower approximation of `M_stop`). -/
def univStopProbApprox (t : ℕ) (z : BitString) : ℚ :=
  (((boundedPrograms t).filter fun p => univWitnessWithin t z p).map
    fun p => (1 / 2 : ℚ) ^ p.length).sum

/-- The stage approximation as a finite sum of the weights `2^{-|p|}` over the stage-`t`
accepted strings (the filtered list has no duplicates). Blueprint 03 Lemma U1. -/
private theorem univStopProbApprox_eq_sum (t : ℕ) (z : BitString) :
    univStopProbApprox t z =
      ∑ p ∈ ((boundedPrograms t).filter fun p => univWitnessWithin t z p).toFinset,
        (1 / 2 : ℚ) ^ p.length := by
  unfold univStopProbApprox
  rw [List.sum_toFinset _ ((boundedPrograms_nodup t).filter _)]

/-- The stage approximation is the dyadic rational `univStopProbNum t z / 2^t`: every accepted
string has length `≤ t`. Blueprint 03 Lemma U1 (lower approximation of `M_stop`). -/
private theorem univStopProbApprox_eq_div (t : ℕ) (z : BitString) :
    univStopProbApprox t z = (univStopProbNum t z : ℚ) / 2 ^ t := by
  unfold univStopProbApprox univStopProbNum
  rw [Nat.cast_list_sum, List.map_map, eq_div_iff (by positivity), ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  have hlen : p.length ≤ t := (mem_boundedPrograms_iff p t).1 (List.mem_filter.1 hp).1
  simp only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_sub₀ (2 : ℚ) two_ne_zero hlen, one_div_pow, div_mul_eq_mul_div, one_mul,
    div_eq_mul_inv]

/-- The strict threshold `2^{-n} < univStopProbApprox t z` read in natural numbers through the
stage numerator: `2^t < univStopProbNum t z · 2^n`.
Blueprint 03 Lemma U1 (strict rational thresholds are decidable at each stage). -/
private theorem half_pow_lt_univStopProbApprox_iff (n t : ℕ) (z : BitString) :
    (1 / 2 : ℚ) ^ n < univStopProbApprox t z ↔ 2 ^ t < univStopProbNum t z * 2 ^ n := by
  rw [univStopProbApprox_eq_div, one_div_pow, lt_div_iff₀ (by positivity), one_div_mul_eq_div,
    div_lt_iff₀ (by positivity)]
  norm_cast

/-- The approximations are computable in `(t, z)`. Blueprint 03 Lemma U1. -/
theorem univStopProbApprox_computable :
    Computable fun a : ℕ × BitString => univStopProbApprox a.1 a.2 := by
  refine computable_of_num_den (N := fun a : ℕ × BitString => (univStopProbNum a.1 a.2 : ℤ))
    (D := fun a => 2 ^ a.1) ?_ (comp_pow.comp Computable.fst) (fun _ => Nat.two_pow_pos _)
    fun a => ?_
  · exact ComputableReals.primrec_natCastInt.to_comp.comp primrec_univStopProbNum.to_comp
  · rw [univStopProbApprox_eq_div]
    push_cast
    rfl

/-- The approximations increase with the stage. Blueprint 03 Lemma U1. -/
theorem univStopProbApprox_mono (z : BitString) : Monotone fun t => univStopProbApprox t z := by
  intro t t' htt'
  simp only [univStopProbApprox_eq_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
  rw [List.mem_toFinset, List.mem_filter, mem_boundedPrograms_iff] at hp ⊢
  exact ⟨hp.1.trans htt', univWitnessWithin_mono htt' hp.2⟩

/-- `z ∈ T_n` exactly when some stage approximation already exceeds the threshold `2^{-n}`.
Blueprint 03 Lemma U1 (strict thresholds are detected from a lower approximation). -/
theorem mem_stopLevelSet_iff_exists_univStopProbApprox (n : ℕ) (z : BitString) :
    z ∈ stopLevelSet n ↔ ∃ t, (1 / 2 : ℚ) ^ n < univStopProbApprox t z := by
  simp only [half_pow_lt_univStopProbApprox_iff]
  exact two_pow_neg_lt_univStopProb_iff n z

/-- `z` is first detected in `T_n` at stage `t`: `|z| ≤ t`, the stage-`t` approximation exceeds
`2^{-n}`, and this did not already hold at stage `t - 1`. Blueprint 03 Lemma U1
(enumeration without repetitions). -/
def levelNewAt (n t : ℕ) (z : BitString) : Bool :=
  (decide (z.length ≤ t) && decide ((1 / 2 : ℚ) ^ n < univStopProbApprox t z)) &&
    !(decide (0 < t) && decide (z.length ≤ t - 1) &&
      decide ((1 / 2 : ℚ) ^ n < univStopProbApprox (t - 1) z))

/-- The request stream enumerating `T_n` without repetitions: stage `s = ⟨t, i⟩` emits the request
`(z, 1, n)` (mass `2^{-n}` at `z`) for the `i`-th string of length `≤ t` first detected at stage
`t`, if there is one. Blueprint 03 Lemma U1 (each new member of `T_n` gets weight `2^{-n}`). -/
def levelStream (n : ℕ) : RequestStream := fun s =>
  let t := (Nat.unpair s).1
  (((boundedPrograms t).filter (levelNewAt n t))[(Nat.unpair s).2]?).map fun z => (z, 1, n)

/-- The first-detection test is primitive recursive in `(n, t, z)`: its threshold comparisons are
the natural-number tests `2^t < univStopProbNum t z · 2^n`.
Blueprint 03 Lemma U1 (enumeration without repetitions is effective). -/
private theorem primrec_levelNewAt :
    Primrec fun a : ℕ × ℕ × BitString => levelNewAt a.1 a.2.1 a.2.2 := by
  have hn : Primrec fun a : ℕ × ℕ × BitString => a.1 := Primrec.fst
  have ht : Primrec fun a : ℕ × ℕ × BitString => a.2.1 := Primrec.fst.comp Primrec.snd
  have hz : Primrec fun a : ℕ × ℕ × BitString => a.2.2 := Primrec.snd.comp Primrec.snd
  have ht' : Primrec fun a : ℕ × ℕ × BitString => a.2.1 - 1 :=
    Primrec.nat_sub.comp ht (Primrec.const 1)
  have hlen : Primrec fun a : ℕ × ℕ × BitString => a.2.2.length := Primrec.list_length.comp hz
  have hthr : ∀ {f : ℕ × ℕ × BitString → ℕ}, Primrec f → Primrec fun a : ℕ × ℕ × BitString =>
      decide (2 ^ f a < univStopProbNum (f a) a.2.2 * 2 ^ a.1) := fun hf =>
    (Primrec.nat_lt.comp (nat_pow_primrec₂.comp (Primrec.const 2) hf)
      (Primrec.nat_mul.comp (primrec_univStopProbNum.comp (hf.pair hz))
        (nat_pow_primrec₂.comp (Primrec.const 2) hn))).decide
  have hle : ∀ {f : ℕ × ℕ × BitString → ℕ}, Primrec f → Primrec fun a : ℕ × ℕ × BitString =>
      decide (a.2.2.length ≤ f a) := fun hf => (Primrec.nat_le.comp hlen hf).decide
  have hpos : Primrec fun a : ℕ × ℕ × BitString => decide (0 < a.2.1) :=
    (Primrec.nat_lt.comp (Primrec.const 0) ht).decide
  refine (Primrec.and.comp (Primrec.and.comp (hle ht) (hthr ht)) (Primrec.not.comp
    (Primrec.and.comp (Primrec.and.comp hpos (hle ht')) (hthr ht')))).of_eq fun a => ?_
  simp only [levelNewAt, half_pow_lt_univStopProbApprox_iff]

/-- The level streams are computable, uniformly in `n`. Blueprint 03 Lemma U1. -/
theorem levelStream_computable : Computable fun a : ℕ × ℕ => levelStream a.1 a.2 := by
  have ht : Primrec fun a : ℕ × ℕ => (Nat.unpair a.2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hnew : Primrec₂ fun (a : ℕ × ℕ) (z : BitString) => levelNewAt a.1 (Nat.unpair a.2).1 z :=
    primrec_levelNewAt.comp ((Primrec.fst.comp Primrec.fst).pair ((ht.comp Primrec.fst).pair
      Primrec.snd))
  have hget : Primrec fun a : ℕ × ℕ =>
      ((boundedPrograms (Nat.unpair a.2).1).filter (levelNewAt a.1 (Nat.unpair a.2).1))[
        (Nat.unpair a.2).2]? :=
    Primrec.list_getElem?.comp (Primrec.list_filter (primrec_boundedPrograms.comp ht) hnew)
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hreq : Primrec₂ fun (a : ℕ × ℕ) (z : BitString) => ((z, 1, a.1) : DyadicRequest) :=
    Primrec.snd.pair ((Primrec.const 1).pair (Primrec.fst.comp Primrec.fst))
  exact (Primrec.option_map hget hreq).to_comp

/-- `z` is first detected in `T_n` at stage `t` exactly when `t` is the least stage at which
`|z| ≤ t` and the stage approximation exceeds `2^{-n}` (a condition monotone in the stage).
Blueprint 03 Lemma U1 (enumeration without repetitions). -/
private theorem levelNewAt_eq_true_iff {n t : ℕ} {z : BitString} :
    levelNewAt n t z = true ↔
      (z.length ≤ t ∧ (1 / 2 : ℚ) ^ n < univStopProbApprox t z) ∧
        ∀ t' < t, ¬ (z.length ≤ t' ∧ (1 / 2 : ℚ) ^ n < univStopProbApprox t' z) := by
  simp only [levelNewAt, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  refine and_congr_right fun _ => ⟨fun h t' ht' hP => ?_, fun h => ?_⟩
  · rcases h with (h | h) | h
    · exact h (by omega)
    · exact h (by omega)
    · exact h (hP.2.trans_le (univStopProbApprox_mono z (by omega)))
  · by_contra hcon
    push_neg at hcon
    exact h (t - 1) (by omega) ⟨hcon.1.2, hcon.2⟩

/-- A string is first detected in `T_n` at one stage only. Blueprint 03 Lemma U1
(enumeration without repetitions). -/
private theorem eq_of_levelNewAt {n t t' : ℕ} {z : BitString} (h : levelNewAt n t z = true)
    (h' : levelNewAt n t' z = true) : t = t' := by
  rw [levelNewAt_eq_true_iff] at h h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2 t hlt h.1
  · exact h.2 t' hlt h'.1

/-- The level stream requests every string at most once. Blueprint 03 Lemma U1
(enumeration without repetitions). -/
theorem levelStream_stage_unique {n s s' : ℕ} {r : DyadicRequest} (h : levelStream n s = some r)
    (h' : levelStream n s' = some r) : s = s' := by
  simp only [levelStream, Option.map_eq_some_iff] at h h'
  obtain ⟨z, hz, rfl⟩ := h
  obtain ⟨z', hz', hzz'⟩ := h'
  obtain rfl : z' = z := congrArg Prod.fst hzz'
  have ht : (Nat.unpair s).1 = (Nat.unpair s').1 :=
    eq_of_levelNewAt (List.mem_filter.1 (List.mem_of_getElem? hz)).2
      (List.mem_filter.1 (List.mem_of_getElem? hz')).2
  rw [← ht] at hz'
  have hi : (Nat.unpair s).2 = (Nat.unpair s').2 :=
    List.getElem?_inj (List.getElem?_eq_some_iff.1 hz).1
      ((boundedPrograms_nodup _).filter _) (hz.trans hz'.symm)
  rw [← Nat.pair_unpair s, ← Nat.pair_unpair s', ht, hi]

/-- Every request of the level stream is the request `(z, 1, n)` of mass `2^{-n}` at a member
`z` of `T_n`. Blueprint 03 Lemma U1 (each new member of `T_n` gets weight `2^{-n}`). -/
private theorem levelStream_eq_some {n s : ℕ} {r : DyadicRequest}
    (h : levelStream n s = some r) : r = (r.1, 1, n) ∧ r.1 ∈ stopLevelSet n := by
  simp only [levelStream, Option.map_eq_some_iff] at h
  obtain ⟨z, hz, rfl⟩ := h
  refine ⟨rfl, (mem_stopLevelSet_iff_exists_univStopProbApprox n z).2 ⟨(Nat.unpair s).1, ?_⟩⟩
  exact (levelNewAt_eq_true_iff.1 (List.mem_filter.1 (List.mem_of_getElem? hz)).2).1.2

/-- At every stage the level stream has put mass at most `2^{-n}` on a string, and no mass
outside `T_n`. Blueprint 03 Lemma U1 (each new member of `T_n` gets weight `2^{-n}` once). -/
private theorem streamStageMass_levelStream_le (n s : ℕ) (u : BitString) :
    streamStageMass (levelStream n) s u ≤
      (stopLevelSet n).indicator (fun _ => (1 / 2 : ℚ) ^ n) u := by
  have huniq : ∀ s s' r r', levelStream n s = some r → levelStream n s' = some r' →
      r.1 = r'.1 → s = s' := by
    intro s s' r r' h h' hrr'
    refine levelStream_stage_unique h ?_
    rw [h', (levelStream_eq_some h').1, ← hrr', ← (levelStream_eq_some h).1]
  rcases streamStageMass_eq_zero_or_weight huniq s u with h0 | ⟨s', -, r, hr, hru, hmass⟩
  · rw [h0]
    exact Set.indicator_nonneg (fun _ _ => by positivity) u
  · obtain ⟨hr1, hmem⟩ := levelStream_eq_some hr
    rw [hmass, Set.indicator_of_mem (hru ▸ hmem), hr1]
    simp [DyadicRequest.weight]

/-- The level stream respects the path budget at every stage: fewer than `2^n` requests of weight
`2^{-n}` lie on any path. Blueprint 03 Lemma U1 (the allocator of §4 applies). -/
theorem levelStream_budgeted (n : ℕ) : IsBudgetedRequestStream (levelStream n) := by
  classical
  intro s v
  set K := (Finset.range (v.length + 1)).filter fun k => v.take k ∈ stopLevelSet n
  have hcard : K.card < 2 ^ n := by
    have hset : {k | k ≤ v.length ∧ v.take k ∈ stopLevelSet n} = ↑K := by
      ext k
      simp [K]
    have h := ncard_stopLevelSet_prefixes_lt n v
    rwa [hset, Set.ncard_coe_finset] at h
  calc streamStageLoad (levelStream n) s v
      ≤ ∑ k ∈ Finset.range (v.length + 1),
          (stopLevelSet n).indicator (fun _ => (1 / 2 : ℚ) ^ n) (v.take k) :=
        Finset.sum_le_sum fun k _ => streamStageMass_levelStream_le n s _
    _ = K.card * (1 / 2 : ℚ) ^ n := by
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ n * (1 / 2 : ℚ) ^ n := by
        gcongr
        exact_mod_cast hcard.le
    _ = 1 := by
        rw [← mul_pow]
        norm_num

/-- The level stream enumerates exactly `T_n`, each member as the request `(z, 1, n)`.
Blueprint 03 Lemma U1 (`T_n` enumerated without repetitions). -/
theorem mem_stopLevelSet_iff_exists_levelStream (n : ℕ) (z : BitString) :
    z ∈ stopLevelSet n ↔ ∃ s, levelStream n s = some (z, 1, n) := by
  constructor
  · intro hz
    obtain ⟨t, ht⟩ := (mem_stopLevelSet_iff_exists_univStopProbApprox n z).1 hz
    have hex : ∃ t, z.length ≤ t ∧ (1 / 2 : ℚ) ^ n < univStopProbApprox t z :=
      ⟨max t z.length, le_max_right _ _,
        ht.trans_le (univStopProbApprox_mono z (le_max_left _ _))⟩
    have hnew : levelNewAt n (Nat.find hex) z = true :=
      levelNewAt_eq_true_iff.2 ⟨Nat.find_spec hex, fun _ ht' => Nat.find_min hex ht'⟩
    have hmem : z ∈ (boundedPrograms (Nat.find hex)).filter (levelNewAt n (Nat.find hex)) :=
      List.mem_filter.2 ⟨(mem_boundedPrograms_iff z _).2 (Nat.find_spec hex).1, hnew⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
    refine ⟨Nat.pair (Nat.find hex) i, ?_⟩
    simp only [levelStream, Nat.unpair_pair]
    rw [hi]
    rfl
  · rintro ⟨s, hs⟩
    exact (levelStream_eq_some hs).2

/-- The colour class `L_{n,j}`: the strings to which the allocator run on the level stream of `T_n`
ever assigns the atom `j` of the depth-`n` grid.
Blueprint 03 Lemma U1 (`L_{n,j} = {z ∈ T_n | j(z) = j}`). -/
def levelColourClass (n j : ℕ) : Set BitString :=
  {z | ∃ s, j ∈ (allocRun (levelStream n) s).atoms z}

/-- The colour classes are computably enumerable, uniformly in `(n, j)`.
Blueprint 03 Lemma U1 (uniformly c.e. antichains). -/
theorem levelColourClass_isRE :
    IsRE fun a : ℕ × ℕ × BitString => a.2.2 ∈ levelColourClass a.1 a.2.1 := by
  exact isRE_exists_mem_allocRun_atoms (ρ := levelStream) levelStream_computable

/-- Each colour class is an input antichain: comparable distinct strings receive different colours.
Blueprint 03 Lemma U1 (the `L_{n,j}` are antichains). -/
theorem levelColourClass_isPrefixFree (n j : ℕ) : IsPrefixFree (levelColourClass n j) := by
  rintro z ⟨s₁, h₁⟩ w ⟨s₂, h₂⟩ hzw
  by_contra hne
  obtain ⟨mass, hinv, -⟩ := allocRun_invariant (levelStream_budgeted n) (max s₁ s₂)
  have hρ : ∀ s r, levelStream n s = some r → r.2.2 = n := fun _ _ h => by
    rw [(levelStream_eq_some h).1]
  exact hinv.disjoint z w (Or.inl hzw) hne j
    (mem_allocRun_atoms_of_le hρ (le_max_left s₁ s₂) h₁)
    (mem_allocRun_atoms_of_le hρ (le_max_right s₁ s₂) h₂)

/-- Every member of `T_n` receives one of the `2^n` colours of the depth-`n` grid.
Blueprint 03 Lemma U1 (each `z ∈ T_n` gets a colour `j(z) < 2^n`). -/
theorem stopLevelSet_subset_biUnion_levelColourClass (n : ℕ) :
    stopLevelSet n ⊆ ⋃ j < 2 ^ n, levelColourClass n j := by
  intro z hz
  obtain ⟨s, hs⟩ := (mem_stopLevelSet_iff_exists_levelStream n z).mp hz
  obtain ⟨mass, hinv, hmass⟩ := allocRun_invariant (levelStream_budgeted n) (s + 1)
  have hpos : 0 < mass z := by
    have h1 : DyadicRequest.weight (z, 1, n) ≤
        (mass z : ℚ) / 2 ^ (allocRun (levelStream n) (s + 1)).prec := by
      rw [hmass z]
      exact weight_le_streamStageMass_succ hs
    have h2 : (0 : ℚ) < DyadicRequest.weight (z, 1, n) := by
      simp [DyadicRequest.weight]
    rcases Nat.eq_zero_or_pos (mass z) with h0 | h0
    · rw [h0] at h1
      simp only [Nat.cast_zero, zero_div] at h1
      linarith
    · exact h0
  obtain ⟨j, hj⟩ := List.exists_mem_of_length_pos (by rw [hinv.card z]; exact hpos)
  have hprec : (allocRun (levelStream n) (s + 1)).prec ≤ n := by
    rcases allocRun_prec_eq_or_empty (ρ := levelStream n)
      (fun _ _ h => by rw [(levelStream_eq_some h).1]) (s + 1) with h | ⟨h, -⟩ <;> omega
  simp only [Set.mem_iUnion]
  exact ⟨j, lt_of_lt_of_le (hinv.atoms_lt z j hj) (Nat.pow_le_pow_right two_pos hprec), s + 1, hj⟩

/-- A computable enumeration of `L_{n,j}`: stage `s = ⟨t, i⟩` returns the `i`-th occupied string of
the stage-`t` allocation table whose atoms contain `j`. Blueprint 03 Lemma U1 / U3
(enumeration index of the antichain `L_{n,j}`). -/
def levelColourEnum (n j s : ℕ) : Option BitString :=
  (((allocRun (levelStream n) (Nat.unpair s).1).table.filter
    fun e => decide (j ∈ e.2)).map Prod.fst)[(Nat.unpair s).2]?

/-- The colour-class enumerations are computable, uniformly in `(n, j, s)`.
Blueprint 03 Lemma U1 (uniformly c.e.). -/
theorem levelColourEnum_computable :
    Computable fun a : ℕ × ℕ × ℕ => levelColourEnum a.1 a.2.1 a.2.2 := by
  have hs : Computable fun a : ℕ × ℕ × ℕ => Nat.unpair a.2.2 :=
    Computable.unpair.comp (Computable.snd.comp Computable.snd)
  have hrun : Computable fun a : ℕ × ℕ × ℕ =>
      (allocRun (levelStream a.1) (Nat.unpair a.2.2).1).table :=
    ((Primrec.snd.comp (Primrec.of_equiv (e := AllocState.equivProd))).to_comp.comp
      ((allocRun_computable_family (ρ := levelStream) levelStream_computable).comp
        (Computable.pair Computable.fst (Computable.fst.comp hs)))).of_eq fun _ => rfl
  have hsel : Primrec fun p : List (BitString × List ℕ) × ℕ × ℕ =>
      ((p.1.filter fun e => decide (p.2.1 ∈ e.2)).map Prod.fst)[p.2.2]? :=
    Primrec.list_getElem?.comp
      (Primrec.list_map (Primrec.list_filter Primrec.fst
        (primrec_decide_mem_list.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)).to₂)
        (Primrec.fst.comp Primrec.snd).to₂)
      (Primrec.snd.comp Primrec.snd)
  exact (hsel.to_comp.comp (Computable.pair hrun (Computable.pair
    (Computable.fst.comp Computable.snd) (Computable.snd.comp hs)))).of_eq fun _ => rfl

/-- `levelColourEnum n j` enumerates exactly `L_{n,j}`. Blueprint 03 Lemma U1. -/
theorem mem_levelColourClass_iff_exists_levelColourEnum (n j : ℕ) (z : BitString) :
    z ∈ levelColourClass n j ↔ ∃ s, levelColourEnum n j s = some z := by
  simp only [levelColourClass, levelColourEnum, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp
      ((mem_map_fst_filter_iff_mem_atoms (allocRun_keys_nodup _ t) z j).mpr ht)
    exact ⟨Nat.pair t i, by simpa only [Nat.unpair_pair] using hi⟩
  · rintro ⟨s, hs⟩
    exact ⟨_, (mem_map_fst_filter_iff_mem_atoms (allocRun_keys_nodup _ _) z j).mp
      (List.mem_of_getElem? hs)⟩

/-! ### U2: deterministic recognition of a c.e. antichain -/

/-- The deterministic recogniser of the set enumerated by `enum`: at the consumed input prefix `x`
search for the first stage `t` whose enumerated string extends `x`; halt if that string is `x`
itself, otherwise read one input bit. It never requests a random bit and waits forever when no
extension of `x` is enumerated. Blueprint 03 Lemma U2 (construction). -/
def antichainRecognizer (enum : ℕ → Option BitString) : StoppingController := fun xq =>
  (Nat.rfind fun t => Part.some ((enum t).any fun y => decide (xq.1 <+: y))).bind fun t =>
    match enum t with
    | some y => Part.some (if y = xq.1 then StopAction.halt else StopAction.readInput)
    | none => Part.none

/-- The prefix test on bit strings is primitive recursive: `x <+: y` iff `y.take |x| = x`.
Blueprint 03 Lemma U2 (the search test of the recogniser). -/
private theorem primrec_decide_isPrefix : Primrec₂ fun x y : BitString => decide (x <+: y) := by
  have h : Primrec fun p : BitString × BitString => decide (p.2.take p.1.length = p.1) :=
    (PrimrecRel.comp Primrec.eq (Primrec.list_take.comp Primrec.snd
      (Primrec.list_length.comp Primrec.fst)) Primrec.fst).decide
  exact h.of_eq fun p => decide_eq_decide.mpr (eq_comm.trans List.prefix_iff_eq_take.symm)

/-- The recogniser is partial recursive, uniformly in a computable parameter of the enumeration
(the parameter type `α` carries the level and colour in U3; `α = Unit` is the plain statement).
Blueprint 03 Lemma U2 (uniform in an enumeration index). -/
theorem antichainRecognizer_partrec {α : Type} [Primcodable α] {enum : α → ℕ → Option BitString}
    (henum : Computable fun a : α × ℕ => enum a.1 a.2) :
    Partrec fun a : α × (BitString × BitString) => antichainRecognizer (enum a.1) a.2 := by
  have henum' : Computable fun p : (α × (BitString × BitString)) × ℕ => enum p.1.1 p.2 :=
    henum.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have hany : Computable₂ fun (a : α × (BitString × BitString)) (t : ℕ) =>
      (enum a.1 t).any fun y => decide (a.2.1 <+: y) :=
    (Computable.option_casesOn henum' (Computable.const false)
      (primrec_decide_isPrefix.to_comp.comp
        (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
        Computable.snd).to₂).of_eq fun p => by dsimp only; cases enum p.1.1 p.2 <;> rfl
  have hans : Computable₂ fun (a : α × (BitString × BitString)) (t : ℕ) =>
      (enum a.1 t).map fun y => if y = a.2.1 then StopAction.halt else StopAction.readInput :=
    Computable.option_map henum' (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.const _) (Primrec.const _)).to_comp.to₂
  refine ((Partrec.rfind hany.partrec₂).bind (Computable.ofOption hans).to₂).of_eq fun a => ?_
  simp only [antichainRecognizer]
  congr 1
  funext t
  cases enum a.1 t <;> rfl

/-- The recogniser answers `a` at `(x, q)` exactly when the least stage `t` whose enumerated
string `y` extends `x` exists, and `a` is `halt` for `y = x` and `readInput` otherwise.
Blueprint 03 Lemma U2 (construction). -/
private theorem mem_antichainRecognizer_iff {enum : ℕ → Option BitString} {x q : BitString}
    {a : StopAction} :
    a ∈ antichainRecognizer enum (x, q) ↔ ∃ t y, enum t = some y ∧ x <+: y ∧
      (∀ m < t, ∀ y', enum m = some y' → ¬ x <+: y') ∧
      a = if y = x then StopAction.halt else StopAction.readInput := by
  simp only [antichainRecognizer, Part.mem_bind_iff, Nat.mem_rfind, Part.mem_some_iff]
  constructor
  · rintro ⟨t, ⟨ht, hmin⟩, ha⟩
    cases he : enum t with
    | none => simp [he] at ht
    | some y =>
      rw [he] at ht ha
      simp only [Option.any_some, true_eq_decide_iff, Part.mem_some_iff] at ht ha
      refine ⟨t, y, he, ht, fun m hm y' hy' hxy' => ?_, ha⟩
      have := hmin hm
      rw [hy'] at this
      simp [hxy'] at this
  · rintro ⟨t, y, he, hxy, hmin, rfl⟩
    refine ⟨t, ⟨?_, fun {m} hm => ?_⟩, ?_⟩
    · simp [he, hxy]
    · cases hm' : enum m with
      | none => rfl
      | some y' => simp [hmin m hm y' hm']
    · simp [he]

/-- The recogniser never requests a random bit. Blueprint 03 Lemma U2 (no random bits). -/
private theorem readRandom_not_mem_antichainRecognizer (enum : ℕ → Option BitString)
    (x q : BitString) : StopAction.readRandom ∉ antichainRecognizer enum (x, q) := by
  intro h
  obtain ⟨t, y, -, -, -, hy⟩ := mem_antichainRecognizer_iff.1 h
  split_ifs at hy

/-- A run of the recogniser consumes no random bit: every reached pair has random part `[]`.
Blueprint 03 Lemma U2 (the stopping points use the empty random prefix). -/
private theorem Reaches.random_eq_nil_of_antichainRecognizer {enum : ℕ → Option BitString}
    {z p x q : BitString} (h : Reaches (antichainRecognizer enum) z p x q) : q = [] := by
  induction h with
  | nil => rfl
  | readInput _ _ _ ih => exact ih
  | @readRandom x q _ _ ha _ => exact absurd ha (readRandom_not_mem_antichainRecognizer enum x q)

/-- If some enumerated string extends `x`, the search of the recogniser at `(x, q)` stops: the
least stage enumerating an extension `y` of `x` gives the answer `halt` when `y = x` and
`readInput` otherwise. Blueprint 03 Lemma U2 (the search terminates). -/
private theorem exists_mem_antichainRecognizer {enum : ℕ → Option BitString} {x z : BitString}
    {t₀ : ℕ} (ht₀ : enum t₀ = some z) (hxz : x <+: z) (q : BitString) :
    ∃ y, (∃ t, enum t = some y) ∧ x <+: y ∧
      (if y = x then StopAction.halt else StopAction.readInput) ∈
        antichainRecognizer enum (x, q) := by
  classical
  have hex : ∃ t y, enum t = some y ∧ x <+: y := ⟨t₀, z, ht₀, hxz⟩
  obtain ⟨y, hy, hxy⟩ := Nat.find_spec hex
  exact ⟨y, ⟨_, hy⟩, hxy, mem_antichainRecognizer_iff.2 ⟨Nat.find hex, y, hy, hxy,
    fun m hm y' hy' hxy' => Nat.find_min hex hm ⟨y', hy', hxy'⟩, rfl⟩⟩

/-- A run that requests an input bit at every strict prefix of the input buffer `z` while no
random bit is read reaches every prefix of `z` with empty random part. Blueprint 03 Lemma U2
(the recogniser reads `z` bit by bit). -/
private theorem reaches_nil_of_readInput {R : StoppingController} {z : BitString}
    (hR : ∀ x, x <+: z → x.length < z.length → StopAction.readInput ∈ R (x, [])) :
    ∀ x, x <+: z → Reaches R z [] x [] := by
  intro x
  induction x using List.reverseRecOn with
  | nil => intro _; exact Reaches.nil
  | append_singleton x b ih =>
    intro hxb
    have hx : x <+: z := (List.prefix_append x [b]).trans hxb
    have hlt : x.length < z.length := by
      have := hxb.length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
    have hstep := Reaches.readInput (ih hx) hlt (hR x hx hlt)
    have hb : z[x.length]'hlt = b := by
      rw [← hxb.getElem (by simp)]
      simp
    rwa [hb] at hstep

/-- When the enumerated set is an antichain, the recogniser halts with exact consumption `(z, p)`
precisely for the enumerated strings `z` and the empty random prefix `p = []`.
Blueprint 03 Lemma U2 (correctness: exact input stopping points, no random bits). -/
theorem witness_antichainRecognizer_iff {enum : ℕ → Option BitString}
    (hpf : IsPrefixFree {y | ∃ t, enum t = some y}) (z p : BitString) :
    Witness (antichainRecognizer enum) z p ↔ (∃ t, enum t = some z) ∧ p = [] := by
  constructor
  · rintro ⟨hreach, hhalt⟩
    obtain ⟨t, y, hty, -, -, hy⟩ := mem_antichainRecognizer_iff.1 hhalt
    refine ⟨⟨t, ?_⟩, hreach.random_eq_nil_of_antichainRecognizer⟩
    split_ifs at hy with hyz
    · rwa [← hyz]
  · rintro ⟨⟨t₀, ht₀⟩, rfl⟩
    refine ⟨reaches_nil_of_readInput (fun x hxz hlt => ?_) z List.prefix_rfl, ?_⟩
    · obtain ⟨y, hy, hxy, ha⟩ := exists_mem_antichainRecognizer ht₀ hxz []
      have hyx : y ≠ x := by
        intro hyx
        subst hyx
        exact hlt.ne (congrArg List.length (hpf hy ⟨t₀, ht₀⟩ hxz))
      rwa [if_neg hyx] at ha
    · obtain ⟨y, hy, hzy, ha⟩ := exists_mem_antichainRecognizer ht₀ List.prefix_rfl []
      rwa [if_pos (hpf ⟨t₀, ht₀⟩ hy hzy).symm] at ha

/-! ### U3: the uniform length bound via the unary level code -/

/-- The level-colour machine: read the unary code `1^n 0` of the level bit by bit from the random
tape, then exactly `n` further random bits `j`, then run the recogniser of `L_{n, j}` on the input
tape without any further random request. An incomplete code or an incomplete colour keeps requesting
random bits. Blueprint 03 Lemma U3 (unary route, no lookahead). -/
def levelColourMachine : StoppingController := fun xq =>
  let n := (xq.2.takeWhile id).length
  let rest := xq.2.drop (n + 1)
  if n < xq.2.length ∧ n ≤ rest.length then
    antichainRecognizer (levelColourEnum n (natOfBits (rest.take n))) (xq.1, [])
  else Part.some StopAction.readRandom

/-- The level-colour machine is partial recursive. Blueprint 03 Lemma U3. -/
theorem levelColourMachine_partrec : Partrec levelColourMachine := by
  have hk : Primrec fun xq : BitString × BitString => (xq.2.takeWhile id).length :=
    Primrec.list_length.comp ((Primrec.list_takeWhile Primrec.id).comp Primrec.snd)
  have hrest : Primrec fun xq : BitString × BitString =>
      xq.2.drop ((xq.2.takeWhile id).length + 1) :=
    Primrec.list_drop.comp Primrec.snd (Primrec.succ.comp hk)
  have hc : Primrec fun xq : BitString × BitString =>
      decide ((xq.2.takeWhile id).length < xq.2.length ∧
        (xq.2.takeWhile id).length ≤ (xq.2.drop ((xq.2.takeWhile id).length + 1)).length) :=
    (Primrec.and.comp (Primrec.nat_lt.comp hk (Primrec.list_length.comp Primrec.snd)).decide
      (Primrec.nat_le.comp hk (Primrec.list_length.comp hrest)).decide).of_eq
      fun xq => (Bool.decide_and _ _).symm
  have henum : Computable fun a : (ℕ × ℕ) × ℕ => levelColourEnum a.1.1 a.1.2 a.2 :=
    Computable.comp (f := fun a : ℕ × ℕ × ℕ => levelColourEnum a.1 a.2.1 a.2.2)
      (g := fun a : (ℕ × ℕ) × ℕ => (a.1.1, a.1.2, a.2)) levelColourEnum_computable
      (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))
  have hrec : Partrec fun a : (ℕ × ℕ) × (BitString × BitString) =>
      antichainRecognizer (levelColourEnum a.1.1 a.1.2) a.2 :=
    antichainRecognizer_partrec (enum := fun a : ℕ × ℕ => levelColourEnum a.1 a.2) henum
  have hf : Partrec fun xq : BitString × BitString =>
      antichainRecognizer (levelColourEnum (xq.2.takeWhile id).length
        (natOfBits ((xq.2.drop ((xq.2.takeWhile id).length + 1)).take
          (xq.2.takeWhile id).length))) (xq.1, []) :=
    Partrec.comp (f := fun a : (ℕ × ℕ) × (BitString × BitString) =>
        antichainRecognizer (levelColourEnum a.1.1 a.1.2) a.2)
      (g := fun xq : BitString × BitString => (((xq.2.takeWhile id).length,
        natOfBits ((xq.2.drop ((xq.2.takeWhile id).length + 1)).take
          (xq.2.takeWhile id).length)), (xq.1, [])))
      hrec (Computable.pair (Computable.pair hk.to_comp
        (primrec_natOfBits.comp (Primrec.list_take.comp hrest hk)).to_comp)
        (Computable.pair Computable.fst (Computable.const [])))
  refine (Partrec.cond hc.to_comp hf (Partrec.const' (Part.some StopAction.readRandom))).of_eq ?_
  intro xq
  simp only [levelColourMachine]
  split_ifs with h
  · rw [decide_eq_true h]; rfl
  · rw [decide_eq_false h]; rfl

/-- After a complete level code `natCode n` and exactly `n` colour bits `j`, the level-colour
machine acts as the recogniser of the colour class `L_{n, j}` with no random bit consumed.
Blueprint 03 Lemma U3 (the machine runs the recogniser of `L_{n,j}`). -/
private theorem levelColourMachine_natCode_append {n : ℕ} {j : BitString} (hj : j.length = n)
    (x : BitString) :
    levelColourMachine (x, natCode n ++ j) =
      antichainRecognizer (levelColourEnum n (natOfBits j)) (x, []) := by
  have htw : ((natCode n ++ j).takeWhile id).length = n := by simp [natCode]
  have hdrop : (natCode n ++ j).drop (n + 1) = j := List.drop_left' (length_natCode n)
  simp only [levelColourMachine, htw, hdrop, List.length_append, length_natCode, hj]
  rw [if_pos (by omega), List.take_of_length_le (by omega)]

/-- Before the level code and the colour are complete the machine asks for another random bit:
at every strict prefix `q` of `natCode n ++ j` with `|j| = n`, whatever the input prefix.
Blueprint 03 Lemma U3 (unary parse without lookahead). -/
private theorem levelColourMachine_of_prefix_lt {n : ℕ} {j q : BitString} (hj : j.length = n)
    (hq : q <+: natCode n ++ j) (hlt : q.length < (natCode n ++ j).length) (x : BitString) :
    levelColourMachine (x, q) = Part.some StopAction.readRandom := by
  rw [List.prefix_iff_eq_take.mp hq, List.take_append]
  simp only [List.length_append, length_natCode] at hlt
  rcases Nat.lt_or_ge q.length (n + 1) with hk | hk
  · have hcode : (natCode n).take q.length = List.replicate q.length true := by
      rw [natCode, List.take_append_of_le_length (by simp; omega), List.take_replicate,
        min_eq_left (by omega)]
    rw [hcode, show q.length - (natCode n).length = 0 by simp; omega, List.take_zero,
      List.append_nil]
    simp [levelColourMachine]
  · have htw : ((natCode n ++ j.take (q.length - (n + 1))).takeWhile id).length = n := by
      simp [natCode]
    have hdrop : (natCode n ++ j.take (q.length - (n + 1))).drop (n + 1) =
        j.take (q.length - (n + 1)) := List.drop_left' (length_natCode n)
    rw [List.take_of_length_le (by simp; omega), length_natCode]
    simp only [levelColourMachine, htw, hdrop, List.length_append, length_natCode,
      List.length_take, hj]
    rw [if_neg (by omega)]

/-- A run that requests a random bit at every strict prefix of the random buffer `p` while no
input is read reaches every prefix of `p` with empty input. Blueprint 03 Lemma U3 (the random
phase of the level-colour machine). -/
private theorem reaches_nil_of_readRandom {R : StoppingController} {z p : BitString}
    (hR : ∀ q, q <+: p → q.length < p.length → StopAction.readRandom ∈ R ([], q)) :
    ∀ q, q <+: p → Reaches R z p [] q := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro _; exact Reaches.nil
  | append_singleton q b ih =>
    intro hqb
    have hq : q <+: p := (List.prefix_append q [b]).trans hqb
    have hlt : q.length < p.length := by
      have := hqb.length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
    have hstep := Reaches.readRandom (ih hq) hlt (hR q hq hlt)
    have hb : p[q.length]'hlt = b := by
      rw [← hqb.getElem (by simp)]
      simp
    rwa [hb] at hstep

/-- Shifting a random-bit-free run behind a fixed random prefix `p`: if `R'` acts at `(x, p)` as
`R` at `(x, [])` and reaches `([], p)`, every pair `(x, [])` reached by `R` on the empty random
buffer is reached by `R'` as `(x, p)`. Blueprint 03 Lemma U3 (running the recogniser after the
random phase). -/
private theorem Reaches.shift_random_prefix {R R' : StoppingController} {z p x q : BitString}
    (hR : ∀ x, R' (x, p) = R (x, [])) (h0 : Reaches R' z p [] p) (h : Reaches R z [] x q) :
    Reaches R' z p x p := by
  induction h with
  | nil => exact h0
  | @readInput x q hxq hx ha ih =>
    obtain rfl : q = [] := List.prefix_nil.mp hxq.prefix.2
    exact Reaches.readInput ih hx (by rw [hR]; exact ha)
  | readRandom _ hq _ _ => exact absurd hq (by simp)

/-- A member `z` of `T_n` has a witness `1^n 0 j` of the level-colour machine with `|j| = n`: its
colour `j` in the depth-`n` grid. Blueprint 03 Lemma U3 (the colour supplies a witness). -/
theorem exists_witness_levelColourMachine {n : ℕ} {z : BitString} (hz : z ∈ stopLevelSet n) :
    ∃ j : BitString, j.length = n ∧ Witness levelColourMachine z (natCode n ++ j) := by
  obtain ⟨j0, hj0, hzj⟩ : ∃ j0, j0 < 2 ^ n ∧ z ∈ levelColourClass n j0 := by
    simpa using stopLevelSet_subset_biUnion_levelColourClass n hz
  have hmem := mem_levelColourClass_iff_exists_levelColourEnum n j0
  have hpf : IsPrefixFree {y | ∃ t, levelColourEnum n j0 t = some y} :=
    fun y hy y' hy' hyy' =>
      levelColourClass_isPrefixFree n j0 ((hmem y).2 hy) ((hmem y').2 hy') hyy'
  obtain ⟨hreach, hhalt⟩ :=
    (witness_antichainRecognizer_iff hpf z []).2 ⟨(hmem z).1 hzj, rfl⟩
  have hj := length_bitsOfNatBE n j0
  have hcode : ∀ x, levelColourMachine (x, natCode n ++ bitsOfNatBE n j0) =
      antichainRecognizer (levelColourEnum n j0) (x, []) := fun x => by
    rw [levelColourMachine_natCode_append hj, natOfBits_bitsOfNatBE hj0]
  have hrandom : Reaches levelColourMachine z (natCode n ++ bitsOfNatBE n j0) []
      (natCode n ++ bitsOfNatBE n j0) :=
    reaches_nil_of_readRandom (fun q hq hlt => by
      rw [levelColourMachine_of_prefix_lt hj hq hlt]; exact Part.mem_some _) _ List.prefix_rfl
  exact ⟨bitsOfNatBE n j0, hj, Reaches.shift_random_prefix hcode hrandom hreach, by rwa [hcode]⟩

/-- Uniform length bound with the unary level code: one constant `C₀` such that every `z ∈ T_n`
has `K_stop(z) ≤ 2n + 1 + C₀`, the constant being the universal code length of the level-colour
machine. Blueprint 03 Lemma U3 (`K_stop(z) ≤ 2n + 1 + C₀`). -/
theorem univStopComplexity_le_of_mem_stopLevelSet :
    ∃ C₀ : ℕ, ∀ n : ℕ, ∀ z : BitString, z ∈ stopLevelSet n →
      univStopComplexity z ≤ (2 * n + 1 + C₀ : ℕ) := by
  obtain ⟨e, he⟩ := exists_stoppingMachine_eq levelColourMachine_partrec
  refine ⟨e + 1, fun n z hz => ?_⟩
  obtain ⟨j, hj, hw⟩ := exists_witness_levelColourMachine hz
  have hK : stopComplexity (stoppingMachine e) z ≤ (2 * n + 1 : ℕ) := by
    have h := stopComplexity_le_of_witness (he ▸ hw)
    rw [List.length_append, length_natCode, hj] at h
    exact h.trans (by norm_cast; omega)
  calc univStopComplexity z ≤ stopComplexity (stoppingMachine e) z + (e + 1 : ℕ) :=
        univStopComplexity_le_stoppingMachine e z
    _ ≤ (2 * n + 1 : ℕ) + (e + 1 : ℕ) := by gcongr
    _ = (2 * n + 1 + (e + 1) : ℕ) := by push_cast; ring

/-! ### U-local and U4 -/

/-- U-local: one constant `C₀` such that `g(z) ≤ 2⌈m(z)⌉ + 3 + C₀` for every `z` (apply U3 at the
level `n = ⌈m(z)⌉ + 1`). Blueprint 03 Lemma U3 (unary route) and 04 Interface UPPER (U-local). -/
theorem stoppingGap_le_massDepth :
    ∃ C₀ : ℕ, ∀ z : BitString, stoppingGap z ≤ 2 * ⌈massDepth z⌉₊ + 3 + C₀ := by
  obtain ⟨C₀, hC₀⟩ := univStopComplexity_le_of_mem_stopLevelSet
  refine ⟨C₀, fun z => ?_⟩
  have hmem : z ∈ stopLevelSet (⌈massDepth z⌉₊ + 1) := by
    have hlt : (2 : ℝ≥0∞)⁻¹ ^ (⌈massDepth z⌉₊ + 1) < (2 : ℝ≥0∞)⁻¹ ^ ⌈massDepth z⌉₊ := by
      rw [pow_succ, ← div_eq_mul_inv]
      exact ENNReal.half_lt_self (by simp) (by simp)
    exact hlt.trans_le (two_pow_neg_ceil_le z)
  have hK := hC₀ _ z hmem
  rw [← univStopComplexityNat_eq_coe, Nat.cast_le] at hK
  have hKr : (univStopComplexityNat z : ℝ) ≤ 2 * (⌈massDepth z⌉₊ + 1 : ℕ) + 1 + C₀ := by
    exact_mod_cast hK
  have hm := massDepth_nonneg z
  unfold stoppingGap
  push_cast at hKr
  linarith

/-- Interface UPPER in its weak local form: for every real `T` there is a bound `G` on the stopping
gap of all strings of mass depth at most `T` (`G = 2⌈T⌉ + 3 + C₀`).
Blueprint 04 Interface UPPER (U-local: `m(z) ≤ T → g(z) ≤ H_T`). -/
theorem exists_stoppingGap_bound_of_massDepth_le (T : ℝ) :
    ∃ G : ℝ, ∀ z : BitString, massDepth z ≤ T → stoppingGap z ≤ G := by
  obtain ⟨C₀, hC₀⟩ := stoppingGap_le_massDepth
  use 2 * ⌈T⌉₊ + 3 + C₀
  intro z hz
  have hz_ceil : (⌈massDepth z⌉₊ : ℝ) ≤ (⌈T⌉₊ : ℝ) := by
    norm_cast
    exact Nat.ceil_mono hz
  linarith [hC₀ z]

/-- U4: a sequence of strings whose gaps grow at least like `c - a` has mass depth tending to
infinity: for every real `T`, all but finitely many terms have `m(z_c) > T`.
Blueprint 03 Corollary U4 (eventual large-`m` domain). -/
theorem massDepth_unbounded_of_stoppingGap_gt {z : ℕ → BitString} {a : ℕ}
    (h : ∀ c : ℕ, (c : ℝ) - a < stoppingGap (z c)) (T : ℝ) :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → T < massDepth (z c) := by
  rcases exists_stoppingGap_bound_of_massDepth_le T with ⟨G, hG⟩
  use ⌈G + a⌉₊
  intro c hc
  by_contra hcontra
  rw [not_lt] at hcontra
  have h1 : (c : ℝ) - a < stoppingGap (z c) := h c
  have h2 : stoppingGap (z c) ≤ G := hG (z c) hcontra
  have h3 : (c : ℝ) - a < G := lt_of_lt_of_le h1 h2
  have h4 : (c : ℝ) < G + a := sub_lt_iff_lt_add.mp h3
  have h5 : G + a ≤ (⌈G + a⌉₊ : ℝ) := Nat.le_ceil (G + a)
  have h6 : (⌈G + a⌉₊ : ℝ) ≤ (c : ℝ) := Nat.cast_le.mpr hc
  linarith

end Kolmogorov
