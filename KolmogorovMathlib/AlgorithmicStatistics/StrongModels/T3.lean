import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1

/-!
# Many strange strings

Exact target vocabulary and finite counting leaves for VS40 Section 7,
Theorem `t3`.  The source modifies the `t1` marking construction so that a
model is rebuilt after `2 ^ (k - epsilon - delta)` newly marked elements.  The
resulting model still has `2 ^ (k - epsilon)` elements, but only the displayed
exceptional quota may fail the `t1` profile conclusions.

As for `t1_strange_string`, the symmetric strong-profile conclusion below
uses strength `epsilon + O(log n)`: filling the solid boundary still invokes
`strong_description_shift`.  The ordinary complexity and both neighborhood
radii use the source's `O(delta + log n)` accuracy, represented by
`delta + logSlack cProfile n`.

This file does not assert the existence of a `T3Witness`; that is the remaining
batched marking/replay theorem.  In particular, none of the fields below
assumes a winning construction or a profile-neighborhood hypothesis.
-/

namespace Kolmogorov

/-- The per-element conclusion of Theorem `t3`, with the logarithmic strength
loss from the strong description shift exposed exactly as in `t1_strange_string`. -/
def T3GoodElement
    (V T : Map) (x : BitString) (n k epsilon delta : Nat)
    (cStrength cProfile : Nat) : Prop :=
  x.length = n ∧
  (k : ENat) ≤ plainK V x ∧
  plainK V x ≤ (k + delta + logSlack cProfile n : ENat) ∧
  ProfileSetsWithinNeighborhood
    (plainDescriptionProfileSet V x)
    (t1PlainPolygon n k epsilon)
    (delta + logSlack cProfile n) ∧
  ProfileSetsWithinNeighborhood
    (strongDescriptionProfileSet V T x
      (epsilon + logSlack cStrength n))
    (t1StrongPolygon n k)
    (delta + logSlack cProfile n)

/-- Exact witness package for the conclusion of Theorem `t3` at fixed
parameters.  A single simple model `A` and a single exceptional subset serve
all good elements; this prevents the witnesses and constants from depending
on the chosen element. -/
structure T3Witness
    (V T : Map) (n k epsilon delta : Nat)
    (cStrength cProfile : Nat) where
  A : Finset BitString
  A_nonempty : A.Nonempty
  A_subset_cube : A ⊆ stringsOfLength n
  A_card : A.card = 2 ^ (k - epsilon)
  A_complexity :
    plainSetComplexity V A A_nonempty ≤
      (epsilon + delta + logSlack cProfile n : ENat)
  exceptional : Finset BitString
  exceptional_subset : exceptional ⊆ A
  exceptional_card : exceptional.card ≤ 2 ^ (k - epsilon - delta)
  good : ∀ x ∈ A \ exceptional,
    T3GoodElement V T x n k epsilon delta cStrength cProfile

/-- Honest, unproved target proposition for VS40 Theorem `t3`.  The three
uniform constants precede every varying numerical parameter.  A future public
theorem `t3` must prove this proposition from optimality of `V` and `T`; merely
constructing a `T3Witness` from an assumed profile neighborhood would not
discharge the source claim. -/
def T3Statement (V T : Map) : Prop :=
  ∃ c0 cStrength cProfile : Nat,
    ∀ n k epsilon delta : Nat,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k ≤ n →
      delta ≤ k - epsilon →
      Nonempty
        (T3Witness V T n k epsilon delta cStrength cProfile)

/-- The source's rebuild-scale identity: the exceptional quota times the
`2 ^ (epsilon + delta)` charging budget is the full `2 ^ k` mark budget. -/
theorem t3_rebuild_scale_identity
    {k epsilon delta : ℕ}
    (hepsilon : epsilon ≤ k)
    (hdelta : delta ≤ k - epsilon) :
    2 ^ (k - epsilon - delta) * 2 ^ (epsilon + delta) = 2 ^ k := by
  rw [← pow_add]
  congr 1
  omega

/-- Removing at most `q` bad elements leaves at least `A.card - q` good
elements. -/
theorem t3_good_card_lower
    {α : Type*} [DecidableEq α]
    (A bad : Finset α) (hbad : bad ⊆ A) {q : ℕ}
    (hq : bad.card ≤ q) :
    A.card - q ≤ (A \ bad).card := by
  have : (A \ bad).card = A.card - bad.card := Finset.card_sdiff_of_subset hbad
  rw [this]
  omega

/-- Every finite set contains a subset of each cardinality not exceeding its
own.  This is the exact extraction leaf used when the batched `t3` run selects
a new model or a charged batch. -/
theorem t3_extract_smaller_model
    {α : Type*} (A : Finset α)
    (m : Nat) (hm : m ≤ A.card) :
    ∃ B : Finset α, B ⊆ A ∧ B.card = m := by
  classical
  exact Finset.exists_subset_card_eq hm

/-- The exceptional quota is no larger than the model size. -/
theorem t3_exception_quota_le_model_size
    (k epsilon delta : Nat) :
    2 ^ (k - epsilon - delta) ≤ 2 ^ (k - epsilon) :=
  Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

/-- A model of the `t3` target size contains an exact rebuild batch of the
exceptional-quota size. -/
theorem t3_extract_rebuild_batch
    {α : Type*} (A : Finset α)
    {k epsilon delta : Nat}
    (hA : A.card = 2 ^ (k - epsilon)) :
    ∃ batch : Finset α,
      batch ⊆ A ∧ batch.card = 2 ^ (k - epsilon - delta) := by
  classical
  apply t3_extract_smaller_model A
  rw [hA]
  exact t3_exception_quota_le_model_size k epsilon delta

/-- Cancelling the smaller `t3` saturation quota increases the T1 rebuild
bound by exactly the advertised factor `2 ^ delta`. -/
theorem t3_saturation_rebuilds_le
    (epsilon k delta saturation t : Nat)
    (hepsilon : epsilon ≤ k)
    (hdelta : delta ≤ k - epsilon)
    (hCharge :
      saturation * 2 ^ (k - epsilon - delta) ≤
        2 ^ (k + 1) * t + 2 ^ k) :
    saturation ≤ 2 ^ (epsilon + delta) * (2 * t + 1) := by
  have hsum : epsilon + delta ≤ k := by omega
  have h := t1_saturation_rebuilds_le
    (epsilon + delta) k saturation t hsum
  have hquota : k - (epsilon + delta) = k - epsilon - delta := by
    omega
  rw [hquota] at h
  exact h hCharge

/-- Separate-total form of `t3_saturation_rebuilds_le`, matching the counters
supplied by a reachable batched run. -/
theorem t3_saturation_rebuilds_le_of_totals
    (epsilon k delta saturation totalC totalD t : Nat)
    (hepsilon : epsilon ≤ k)
    (hdelta : delta ≤ k - epsilon)
    (hC : totalC ≤ 2 ^ (k + 1) * t)
    (hD : totalD ≤ 2 ^ k)
    (hCharge :
      saturation * 2 ^ (k - epsilon - delta) ≤ totalC + totalD) :
    saturation ≤ 2 ^ (epsilon + delta) * (2 * t + 1) := by
  apply t3_saturation_rebuilds_le epsilon k delta saturation t
    hepsilon hdelta
  exact hCharge.trans (Nat.add_le_add hC hD)

/-- The nonexceptional part of a `T3Witness` has the source's advertised
cardinality lower bound. -/
theorem T3Witness.good_card_lower
    {V T : Map} {n k epsilon delta cStrength cProfile : Nat}
    (w : T3Witness V T n k epsilon delta cStrength cProfile) :
    2 ^ (k - epsilon) - 2 ^ (k - epsilon - delta) ≤
      (w.A \ w.exceptional).card := by
  rw [← w.A_card]
  exact t3_good_card_lower w.A w.exceptional
    w.exceptional_subset w.exceptional_card

/-- Pointwise elimination form of the good-element field. -/
theorem T3Witness.good_of_mem_not_exceptional
    {V T : Map} {n k epsilon delta cStrength cProfile : Nat}
    (w : T3Witness V T n k epsilon delta cStrength cProfile)
    {x : BitString} (hxA : x ∈ w.A) (hxBad : x ∉ w.exceptional) :
    T3GoodElement V T x n k epsilon delta cStrength cProfile := by
  exact w.good x (Finset.mem_sdiff.mpr ⟨hxA, hxBad⟩)

theorem T3Witness.good_subset_highComplexity
    {V T : Map} {n k epsilon delta cStrength cProfile : Nat}
    (w : T3Witness V T n k epsilon delta cStrength cProfile) :
    w.A \ w.exceptional ⊆
      (stringsOfLength n).filter
        (fun x => (k : ENat) ≤ plainK V x) := by
  intro x hx
  have hgood := w.good x hx
  rw [Finset.mem_filter]
  constructor
  · rw [memStringsOfLength]
    exact hgood.1
  · exact hgood.2.1

theorem T3Witness.good_card_le_highComplexity
    {V T : Map} {n k epsilon delta cStrength cProfile : Nat}
    (w : T3Witness V T n k epsilon delta cStrength cProfile) :
    (w.A \ w.exceptional).card ≤
      ((stringsOfLength n).filter
        (fun x => (k : ENat) ≤ plainK V x)).card := by
  exact Finset.card_le_card w.good_subset_highComplexity

/-- The existing executable marking run satisfies its full structural
invariant at the smaller T3 saturation quota.  Its current model still has
`2 ^ (k - epsilon)` elements; only the C/D-hit threshold is changed to
`2 ^ (k - epsilon - delta)`.  This is the structural half of the batched-run
reuse needed by the public theorem `t3`. -/
theorem t3RunFromEvents_core_spec
    (V : Map) (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon delta t
      (events : List T1MarkEvent),
      c0 ≤ epsilon →
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k + 4 ≤ n →
      events <+: t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t →
      T1RunCoreInvariant cSparse n k epsilon
        (2 ^ (k - epsilon - delta)) events
        (t1RunFromEvents cSparse n k epsilon
          (2 ^ (k - epsilon - delta))
          (t1InitialRunState n k epsilon) events) := by
  intro cDesc
  obtain ⟨c0, cSparse, hcore⟩ :=
    t1RunFromEvents_core_spec_of_quota_pos V c hc cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon delta t events hc0 hepsilon _hdelta hkn hprefix
  exact hcore n k epsilon (2 ^ (k - epsilon - delta)) t events
    hc0 hepsilon hkn (Nat.two_pow_pos _) hprefix

/-- Every historical model in the exact T3-quota run remains duplicate-free,
has `2 ^ (k - epsilon)` elements, and lies in the length-`n` cube. -/
theorem t3RunFromEvents_versions_model_spec
    (V : Map) (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon delta t,
      c0 ≤ epsilon →
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k + 4 ≤ n →
      let quota := 2 ^ (k - epsilon - delta)
      let events := t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t
      let s := t1RunFromEvents cSparse n k epsilon quota
        (t1InitialRunState n k epsilon) events
      T1RunCoreInvariant cSparse n k epsilon quota events s ∧
      T1RunVersionsModelInvariant n k epsilon s := by
  intro cDesc
  obtain ⟨c0, cSparse, hcore⟩ :=
    t3RunFromEvents_core_spec V c hc cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon delta t hc0 hepsilon hdelta hkn
  let quota := 2 ^ (k - epsilon - delta)
  let events := t1MarkingEventStage c n k epsilon
    (epsilon + logSlack cDesc n) t
  let s := t1RunFromEvents cSparse n k epsilon quota
    (t1InitialRunState n k epsilon) events
  have hfull :
      T1RunCoreInvariant cSparse n k epsilon quota events s := by
    simpa [quota, events, s] using
      hcore n k epsilon delta t events hc0 hepsilon hdelta hkn
        (List.prefix_refl events)
  refine ⟨hfull, ?_⟩
  apply t1RunFromEvents_versions_model_of_prefix_model
  intro pref hpref
  exact (hcore n k epsilon delta t pref hc0 hepsilon hdelta hkn
    (hpref.trans (List.prefix_refl events))).1

/-- The quota-parametric charging invariant charges every saturation rebuild
of the T3 run by the smaller exceptional quota. -/
theorem t3RunAt_saturation_charge
    (c : Nat.Partrec.Code)
    (cDesc cSparse n k epsilon delta t : Nat) :
    let quota := 2 ^ (k - epsilon - delta)
    let s := t1RunAt c cDesc cSparse n k epsilon quota t
    s.saturation * quota ≤ s.totalC + s.totalD := by
  dsimp only
  have hcharge :=
    (t1RunFromEvents_quota_charge_spec cSparse n k epsilon
      (2 ^ (k - epsilon - delta))
      (t1InitialRunState n k epsilon)
      (t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t)
      (by simpa [t1InitialRunState] using
        t1InitialCurrent_nodup n k epsilon)
      (by simp [T1RunQuotaChargeInvariant, t1RunPendingCharge,
        t1InitialRunState])).2
  unfold T1RunQuotaChargeInvariant at hcharge
  simp only [t1RunAt]
  omega

/-- Rebuild-count arithmetic for the smaller T3 saturation quota. -/
theorem t3_change_count_arith :
  ∀ cDesc cSparse, ∃ cRun, ∀
    n k epsilon delta external saturation totalC totalD,
    epsilon ≤ k →
    delta ≤ k - epsilon →
    k + 4 ≤ n →
    external ≤
      2 ^ (epsilon + 1) +
      2 ^ (epsilon + logSlack cDesc n + 1) →
    totalC ≤ 2 ^ (k + 1) * (cSparse * n + cSparse) →
    totalD ≤ 2 ^ k →
    saturation * 2 ^ (k - epsilon - delta) ≤ totalC + totalD →
    external + saturation <
      2 ^ (epsilon + delta + logSlack cRun n) := by
  intro cDesc cSparse
  obtain ⟨cRun, hRun⟩ := t1_change_count_arith cDesc cSparse
  use cRun
  intro n k epsilon delta external saturation totalC totalD hepsilon hdelta hn hext hC hD hsat
  have hext_bound :
    external ≤
      2 ^ ((epsilon + delta) + 1) +
      2 ^ ((epsilon + delta) + logSlack cDesc n + 1) := by
    calc external
      _ ≤ 2 ^ (epsilon + 1) + 2 ^ (epsilon + logSlack cDesc n + 1) := hext
      _ ≤ 2 ^ (epsilon + delta + 1) + 2 ^ (epsilon + delta + logSlack cDesc n + 1) := by
        gcongr <;> omega
  have hsub : k - (epsilon + delta) = k - epsilon - delta := by omega
  have hsat_bound : saturation * 2 ^ (k - (epsilon + delta)) ≤ totalC + totalD := by
    rw [hsub]
    exact hsat
  exact hRun n k (epsilon + delta) external saturation totalC totalD (by omega) hn hext_bound hC
    hD hsat_bound

/-- The C-mark charge of the exact T3-quota run has the same global bound as
the T1 run because its current model and sparse-intersection invariant are
unchanged. -/
theorem t3RunAt_totalC_le
    (V : Map) (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon delta t,
      c0 ≤ epsilon →
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k + 4 ≤ n →
      let quota := 2 ^ (k - epsilon - delta)
      let s := t1RunAt c cDesc cSparse n k epsilon quota t
      s.totalC ≤ 2 ^ (k + 1) * (cSparse * n + cSparse) := by
  intro cDesc
  obtain ⟨c0, cSparse, hcore⟩ :=
    t3RunFromEvents_core_spec V c hc cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon delta t hc0 hepsilon hdelta hkn
  let quota := 2 ^ (k - epsilon - delta)
  let events := t1MarkingEventStage c n k epsilon
    (epsilon + logSlack cDesc n) t
  let s := t1RunAt c cDesc cSparse n k epsilon quota t
  have hprefixModel : ∀ pref, pref <+: events →
      T1RunModelInvariant cSparse n k epsilon quota
        (t1RunFromEvents cSparse n k epsilon quota
          (t1InitialRunState n k epsilon) pref) := by
    intro pref hpref
    exact (hcore n k epsilon delta t pref hc0 hepsilon hdelta hkn
      (hpref.trans (List.prefix_refl events))).1
  have hraw := t1RunAt_totalC_le_of_model_spec hprefixModel
  have hcount :
      (events.filter t1RunCPrimeEvent).length ≤ 2 ^ (k + 1) :=
    (t1MarkingEventStage_cPrime_count_le c n k epsilon
      (epsilon + logSlack cDesc n) t).trans
        (t1CPrimeStage_length_lt c k t).le
  have hbound := hraw.trans
    (Nat.mul_le_mul_right (cSparse * n + cSparse) hcount)
  simpa [s, t1RunAt, events, quota] using hbound

/-- The exact T3-quota run has fewer than
`2 ^ (epsilon + delta + O(log n))` historical versions. -/
theorem t3RunAt_rebuild_count_lt
    (V : Map) (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse cRun, ∀ n k epsilon delta t,
      c0 ≤ epsilon →
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k + 4 ≤ n →
      let quota := 2 ^ (k - epsilon - delta)
      let s := t1RunAt c cDesc cSparse n k epsilon quota t
      s.external + s.saturation <
        2 ^ (epsilon + delta + logSlack cRun n) := by
  intro cDesc
  obtain ⟨c0, cSparse, hC⟩ :=
    t3RunAt_totalC_le V c hc cDesc
  obtain ⟨cRun, hcount⟩ :=
    t3_change_count_arith cDesc cSparse
  refine ⟨c0, cSparse, cRun, ?_⟩
  intro n k epsilon delta t hc0 hepsilon hdelta hkn
  let quota := 2 ^ (k - epsilon - delta)
  let s := t1RunAt c cDesc cSparse n k epsilon quota t
  apply hcount n k epsilon delta s.external s.saturation
    s.totalC s.totalD hepsilon hdelta hkn
  · exact t1RunAt_external_rebuilds_le_of_quota
      c cDesc cSparse n k epsilon quota t
  · exact hC n k epsilon delta t hc0 hepsilon hdelta hkn
  · exact t1RunAt_totalD_le_of_quota
      c cDesc cSparse n k epsilon quota t
  · exact t3RunAt_saturation_charge
      c cDesc cSparse n k epsilon delta t

/-- Every reachable T3 version ordinal fits the fixed-width address furnished
by `t3RunAt_rebuild_count_lt`. -/
theorem t3RunAt_version_lt_width
    (V : Map) (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse cWidth, ∀ n k epsilon delta t version,
      c0 ≤ epsilon →
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k + 4 ≤ n →
      version <
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon - delta)) t).versions.length →
      version <
        2 ^ (epsilon + delta + logSlack cWidth n) := by
  intro cDesc
  obtain ⟨c0, cSparse, cWidth, hcount⟩ :=
    t3RunAt_rebuild_count_lt V c hc cDesc
  refine ⟨c0, cSparse, cWidth, ?_⟩
  intro n k epsilon delta t version hc0 hepsilon hdelta hkn hversion
  have hlength :=
    t1RunAt_versions_length c cDesc cSparse n k epsilon
      (2 ^ (k - epsilon - delta)) t
  have hcount' :=
    hcount n k epsilon delta t hc0 hepsilon hdelta hkn
  omega

/-- At a terminal unsaturated state, the marked portion of the current model
itself is a valid exceptional set. -/
theorem t3_exceptional_of_unsaturated
    {α : Type*} [DecidableEq α]
    (A marked : Finset α) {q : Nat}
    (hunsaturated : (A ∩ marked).card ≤ q) :
    ∃ bad : Finset α,
      bad ⊆ A ∧ bad.card ≤ q ∧
      ∀ x ∈ A \ bad, x ∉ marked := by
  use A ∩ marked
  constructor
  · exact Finset.inter_subset_left
  · constructor
    · exact hunsaturated
    · intro x hx hx_marked
      rw [Finset.mem_sdiff] at hx
      have h : x ∈ A ∩ marked := Finset.mem_inter.mpr ⟨hx.1, hx_marked⟩
      exact hx.2 h

/-- A bounded T3 version ordinal fits in the advertised fixed-width binary
address. -/
theorem t3_version_bits_le
    {version epsilon delta width : Nat}
    (hversion :
      version < 2 ^ (epsilon + delta + width)) :
    (Nat.bits version).length ≤ epsilon + delta + width := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr hversion

/-- A self-delimiting T3 run header followed by a fixed-width version address.
Unlike `t1VersionProgram`, the header records `delta`, which determines the
smaller saturation quota used when replaying the run. -/
def t3VersionProgram
    (cWidth n k epsilon delta version : Nat) : BitString :=
  pairCode
    (listCode [Nat.bits n, Nat.bits k, Nat.bits epsilon, Nat.bits delta])
    (chunkAddress version
      (epsilon + delta + logSlack cWidth n))

/-- The T3 version program recovers all four run parameters and its version
ordinal. -/
theorem t3VersionProgram_roundtrip
    (cWidth n k epsilon delta version : Nat)
    (hv : version < 2 ^ (epsilon + delta + logSlack cWidth n)) :
    decodeListCode (decodeFirst
      (t3VersionProgram cWidth n k epsilon delta version)) =
        [Nat.bits n, Nat.bits k, Nat.bits epsilon, Nat.bits delta] ∧
    bitsToNat (decodeSecond
      (t3VersionProgram cWidth n k epsilon delta version)) = version := by
  have hwidth := chunkAddress_length version
    (epsilon + delta + logSlack cWidth n) hv
  clear hwidth
  constructor
  · rw [t3VersionProgram, decodeFirst_pairCode, decodeListCode_listCode]
  · simp [t3VersionProgram, decodeSecond_pairCode, bitsToNat_chunkAddress]

/-- The T3 version decoder replays the run with the quota encoded by the
additional `delta` header field. -/
noncomputable def t3VersionDecoder
    (c : Nat.Partrec.Code) (cDesc cSparse : Nat) :
    BitString →. BitString := fun input => do
  let header := decodeListCode (decodeFirst input)
  let n := bitsToNat (header.getD 0 [])
  let k := bitsToNat (header.getD 1 [])
  let epsilon := bitsToNat (header.getD 2 [])
  let delta := bitsToNat (header.getD 3 [])
  let version := bitsToNat (decodeSecond input)
  let quota := 2 ^ (k - epsilon - delta)
  let t ← Nat.rfind fun m =>
    Part.some (decide (version <
      (t1RunAt c cDesc cSparse n k epsilon quota m).versions.length))
  let L := (t1RunAt c cDesc cSparse n k epsilon quota t).versions.getD version []
  Part.some (canonicalImageCodeOfList L)

/-- The quota-aware T3 version decoder is partial recursive. -/
theorem t3VersionDecoder_partrec
    (c : Nat.Partrec.Code) (cDesc cSparse : Nat) :
    Partrec (t3VersionDecoder c cDesc cSparse) := by
  have hversions : Computable (fun input : T1RunInput => input.run.versions) := by
    have ht : Primrec (fun s : T1RunState => s.toProd) := Primrec.of_equiv
    have hv : Primrec (fun p : T1RunStateData => p.2.2.2.2.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp Primrec.snd)))))
    exact (hv.comp ht).to_comp.comp t1RunAt_computable_uniform
  open Nat.Partrec (Code) in
  have hheader : Computable (fun input : BitString =>
      decodeListCode (decodeFirst input)) :=
    decodeListCode_computable.comp decodeFirst_computable
  have hget : Computable₂
      (fun (l : List BitString) (i : Nat) => l.getD i []) :=
    (Primrec.list_getD []).to_comp
  have hn : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 0 [])) :=
    bitsToNat_primrec.to_comp.comp
      (hget.comp hheader (Computable.const 0))
  have hk : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 1 [])) :=
    bitsToNat_primrec.to_comp.comp
      (hget.comp hheader (Computable.const 1))
  have hepsilon : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 2 [])) :=
    bitsToNat_primrec.to_comp.comp
      (hget.comp hheader (Computable.const 2))
  have hdelta : Computable (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD 3 [])) :=
    bitsToNat_primrec.to_comp.comp
      (hget.comp hheader (Computable.const 3))
  have hversion : Computable (fun input : BitString =>
      bitsToNat (decodeSecond input)) :=
    bitsToNat_primrec.to_comp.comp decodeSecond_computable
  have hquota : Computable (fun input : BitString =>
      2 ^ (bitsToNat ((decodeListCode (decodeFirst input)).getD 1 []) -
        bitsToNat ((decodeListCode (decodeFirst input)).getD 2 []) -
        bitsToNat ((decodeListCode (decodeFirst input)).getD 3 []))) :=
    Kolmogorov.CodedFiniteDistribution.twoPow_primrec.to_comp.comp
      (Primrec.nat_sub.to_comp.comp
        (Primrec.nat_sub.to_comp.comp hk hepsilon) hdelta)
  have hinput : Computable (fun p : BitString × Nat =>
      ({ c := c
       , cDesc := cDesc
       , cSparse := cSparse
       , n := bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 [])
       , k := bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 [])
       , epsilon := bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 [])
       , quota := 2 ^ (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []) -
           bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []) -
           bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 []))
       , t := p.2 } : T1RunInput)) := by
    have h1 : Computable (fun p : BitString × Nat => c) := Computable.const c
    have h2 : Computable (fun p : BitString × Nat => cDesc) := Computable.const cDesc
    have h3 : Computable (fun p : BitString × Nat => cSparse) := Computable.const cSparse
    have h4 : Computable (fun p : BitString × Nat =>
        bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 [])) := hn.comp Computable.fst
    have h5 : Computable (fun p : BitString × Nat =>
        bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 [])) := hk.comp Computable.fst
    have h6 : Computable (fun p : BitString × Nat =>
        bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 [])) := hepsilon.comp Computable.fst
    have h7 : Computable (fun p : BitString × Nat =>
        2 ^ (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []) -
          bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []) -
          bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 []))) :=
      hquota.comp Computable.fst
    have h8 : Computable (fun p : BitString × Nat => p.2) := Computable.snd
    -- Use the same pattern as T1VersionDecoder
    let Data := ((Nat.Partrec.Code × Nat) × (Nat × Nat)) × ((Nat × Nat) × (Nat × Nat))
    let ofData : Data → T1RunInput := fun p =>
      { c := p.1.1.1
      , cDesc := p.1.1.2
      , cSparse := p.1.2.1
      , n := p.1.2.2
      , k := p.2.1.1
      , epsilon := p.2.1.2
      , quota := p.2.2.1
      , t := p.2.2.2 }
    have hofData : Computable ofData := by
      exact Primrec.of_equiv_symm.to_comp
    let buildData : BitString × Nat → Data := fun p =>
      ⟨((c, cDesc), (cSparse, bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))),
       ((bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []),
         bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 [])),
        (2 ^ (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []) -
              bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []) -
              bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 [])), p.2))⟩
    have hbuildData : Computable buildData := by
      have ha : Computable (fun p : BitString × Nat => (c, cDesc)) :=
        (Computable.const c).pair (Computable.const cDesc)
      have hb : Computable (fun p : BitString × Nat =>
          (cSparse, bitsToNat
            ((decodeListCode (decodeFirst p.1)).getD 0 []))) :=
        (Computable.const cSparse).pair (hn.comp Computable.fst)
      have hc : Computable (fun p : BitString × Nat =>
          ((c, cDesc), (cSparse, bitsToNat
            ((decodeListCode (decodeFirst p.1)).getD 0 [])))) :=
        ha.pair hb
      have hd : Computable (fun p : BitString × Nat =>
          (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []),
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))) :=
        (hk.comp Computable.fst).pair (hepsilon.comp Computable.fst)
      have he : Computable (fun p : BitString × Nat =>
          (2 ^ (bitsToNat
              ((decodeListCode (decodeFirst p.1)).getD 1 []) -
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []) -
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 [])), p.2)) :=
        (hquota.comp Computable.fst).pair Computable.snd
      have hf : Computable (fun p : BitString × Nat =>
          ((bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []),
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 [])),
           (2 ^ (bitsToNat
                ((decodeListCode (decodeFirst p.1)).getD 1 []) -
              bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []) -
              bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 [])), p.2))) :=
        hd.pair he
      exact hc.pair hf
    have := hofData.comp hbuildData
    exact this.of_eq (fun p => rfl)
  have hruns : Computable (fun p : BitString × Nat =>
      (t1RunAt c cDesc cSparse
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))
        (2 ^ (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []) -
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []) -
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 [])))
        p.2).versions) := by
    exact (hversions.comp hinput).of_eq (fun p => by rfl)
  have hversionR : Computable (fun p : BitString × Nat =>
      bitsToNat (decodeSecond p.1)) :=
    hversion.comp Computable.fst
  have hlength : Computable (fun p : BitString × Nat =>
      (t1RunAt c cDesc cSparse
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))
        (2 ^ (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []) -
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []) -
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 [])))
        p.2).versions.length) :=
    Computable.list_length.comp hruns
  have hlt : Computable₂
      (fun a b : Nat => decide (a < b)) :=
    (PrimrecPred.decide Primrec.nat_lt).to_comp
  have hcheck : Computable₂
      (fun (input : BitString) (m : Nat) =>
        decide (bitsToNat (decodeSecond input) <
          (t1RunAt c cDesc cSparse
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 0 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 2 []))
            (2 ^ (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []) -
                bitsToNat
                  ((decodeListCode (decodeFirst input)).getD 2 []) -
                bitsToNat
                  ((decodeListCode (decodeFirst input)).getD 3 [])))
            m).versions.length)) :=
    hlt.comp hversionR hlength
  have hfind : Partrec (fun input : BitString =>
      Nat.rfind fun m =>
        Part.some (decide (bitsToNat (decodeSecond input) <
          (t1RunAt c cDesc cSparse
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 0 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 2 []))
            (2 ^ (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []) -
                bitsToNat
                  ((decodeListCode (decodeFirst input)).getD 2 []) -
                bitsToNat
                  ((decodeListCode (decodeFirst input)).getD 3 [])))
            m).versions.length))) :=
    Partrec.rfind hcheck.partrec₂
  have hgetVersion : Computable₂
      (fun (l : List (List BitString)) (i : Nat) =>
        l.getD i []) :=
    (Primrec.list_getD []).to_comp
  have hlist : Computable (fun p : BitString × Nat =>
      (t1RunAt c cDesc cSparse
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 0 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []))
        (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []))
        (2 ^ (bitsToNat ((decodeListCode (decodeFirst p.1)).getD 1 []) -
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 2 []) -
            bitsToNat ((decodeListCode (decodeFirst p.1)).getD 3 [])))
        p.2).versions.getD
          (bitsToNat (decodeSecond p.1)) []) :=
    hgetVersion.comp hruns hversionR
  have hpost : Computable₂
      (fun (input : BitString) (m : Nat) =>
        canonicalImageCodeOfList
          ((t1RunAt c cDesc cSparse
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 0 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []))
            (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 2 []))
            (2 ^ (bitsToNat
              ((decodeListCode (decodeFirst input)).getD 1 []) -
                bitsToNat
                  ((decodeListCode (decodeFirst input)).getD 2 []) -
                bitsToNat
                  ((decodeListCode (decodeFirst input)).getD 3 [])))
            m).versions.getD
              (bitsToNat (decodeSecond input)) [])) :=
    (canonicalImageCodeOfList_computable.comp hlist).to₂
  exact (Partrec.bind hfind hpost.partrec₂).of_eq
    (fun _ => rfl)

theorem t3VersionDecoder_eval
    (c : Nat.Partrec.Code)
    (cDesc cSparse cWidth n k epsilon delta t version : Nat)
    (hseen : version <
      (t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon - delta)) t).versions.length)
    (hwidth : version <
      2 ^ (epsilon + delta + logSlack cWidth n)) :
    canonicalImageCodeOfList
      ((t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon - delta)) t).versions.getD version [])
      ∈ t3VersionDecoder c cDesc cSparse
        (t3VersionProgram cWidth n k epsilon delta version) := by
  obtain ⟨hheader, hversion⟩ :=
    t3VersionProgram_roundtrip
      cWidth n k epsilon delta version hwidth
  have hnparse : bitsToNat
      ((decodeListCode (decodeFirst
        (t3VersionProgram cWidth n k epsilon delta version))).getD
          0 []) = n := by
    rw [hheader]
    simp [bitsToNat_bits]
  have hkparse : bitsToNat
      ((decodeListCode (decodeFirst
        (t3VersionProgram cWidth n k epsilon delta version))).getD
          1 []) = k := by
    rw [hheader]
    simp [bitsToNat_bits]
  have heparse : bitsToNat
      ((decodeListCode (decodeFirst
        (t3VersionProgram cWidth n k epsilon delta version))).getD
          2 []) = epsilon := by
    rw [hheader]
    simp [bitsToNat_bits]
  have hdparse : bitsToNat
      ((decodeListCode (decodeFirst
        (t3VersionProgram cWidth n k epsilon delta version))).getD
          3 []) = delta := by
    rw [hheader]
    simp [bitsToNat_bits]
  let run := fun m =>
    t1RunAt c cDesc cSparse n k epsilon
      (2 ^ (k - epsilon - delta)) m
  let hex : ∃ m, version < (run m).versions.length :=
    ⟨t, hseen⟩
  let t0 := Nat.find hex
  have ht0 : version < (run t0).versions.length :=
    Nat.find_spec hex
  have ht0_le : t0 ≤ t :=
    Nat.find_min' hex hseen
  have hfind : Nat.rfind (fun m =>
      Part.some
        (decide (version < (run m).versions.length))) =
      Part.some t0 := by
    rw [Part.eq_some_iff]
    exact Nat.mem_rfind.mpr ⟨by simpa using ht0, fun {m} hm => by
      simpa using Nat.find_min hex hm⟩
  have hget :
      (run t).versions.getD version [] =
        (run t0).versions.getD version [] := by
    exact t1RunAt_version_getD_eq_of_le
      c cDesc cSparse n k epsilon (2 ^ (k - epsilon - delta))
      ht0_le ht0
  unfold t3VersionDecoder
  simp only [hnparse, hkparse, heparse, hdparse, hversion]
  change canonicalImageCodeOfList
      ((t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon - delta)) t).versions.getD version []) ∈
    (Nat.rfind (fun m => Part.some (decide (version <
      (t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon - delta)) m).versions.length)))).bind
      (fun m => Part.some (canonicalImageCodeOfList
        ((t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon - delta)) m).versions.getD version [])))
  rw [Part.mem_bind_iff]
  refine ⟨t0, ?_, ?_⟩
  · rw [hfind]
    exact ⟨trivial, rfl⟩
  · exact
      ⟨trivial, congrArg canonicalImageCodeOfList hget.symm⟩

end Kolmogorov
