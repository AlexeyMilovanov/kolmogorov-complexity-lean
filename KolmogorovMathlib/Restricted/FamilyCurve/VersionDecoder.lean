import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain

/-!
# M7: the version decoder

The concrete partial-recursive decoder that reconstructs a terminal sampled
model of the anchored run from the encoded grid plus a bounded version
ordinal.  This module proves the decoder's partial recursiveness and its
canonical-code identities.  Replay correctness and the bounded ordinal/
complexity accounting remain in the final M7 leaf.

The decoder input is the self-delimiting bundle
`listCode [gridCode, bits q0, bits s, bits v]`; every grid-derived parameter
(`n`, `N`, `Δ`, ambient length) is recomputed from `gridCode`, while the
covering overhead `q0` — which is not computable from the family — travels in
the bundle.
-/

namespace Kolmogorov

/- `Primcodable` instance terms are kept opaque during definitional checks:
the uniform computability lemmas below compose at 4–5-component product
types, where reducible instance diamonds make `whnf` blow up past 10^8
heartbeats.  Both sides of every check derive the instances identically, so
opaque comparison succeeds syntactically. -/
attribute [local irreducible] Primcodable.prod Primcodable.list

open Nat.Partrec (Code)
open CodedFiniteDistribution

/-- Canonical uniform code of a list of points (the inverse of
`decodeCoverCodeList`).  We reuse the established primitive-recursive encoder;
only nonempty canonical lists occur in the correctness theorem. -/
noncomputable def uniformCodeOfList (l : List BitString) : BitString :=
  canonicalUniformCodeOfList l

/-- Canonical uniform coding of a model list is primitive recursive. -/
theorem uniformCodeOfList_primrec : Primrec uniformCodeOfList := by
  exact canonicalUniformCodeOfList_primrec

/-- On canonical enumerations the list-level encoder recovers the canonical
uniform set code. -/
lemma uniformCodeOfList_canonical (S : Finset BitString) (hS : S.Nonempty) :
    uniformCodeOfList (canonicalFinsetList S) = (codedUniformOn S hS).code := by
  exact canonicalUniformCodeOfList_canonicalFinsetList S hS

/-- Sampling a decoded grid point from the grid code is primitive recursive. -/
lemma decode_restrictedCurveGridCode_sample_primrec :
    Primrec (fun p : BitString × ℕ =>
      decode_restrictedCurveGridCode_sample p.1 p.2) := by
  have hpair : Primrec (fun p : BitString × ℕ =>
      (decodeListCode p.1).getD p.2 []) :=
    (Primrec.list_getD []).comp
      (decodeListCode_primrec.comp Primrec.fst) Primrec.snd
  exact Primrec.pair
    (bitsToNat_primrec.comp (decodeFirst_primrec.comp hpair))
    (bitsToNat_primrec.comp (decodeSecond_primrec.comp hpair))

/-- The sampled size schedule is computable jointly in every numeric
parameter.  Earlier executor lemmas fixed `gridSteps` and `Δ`; the version
decoder needs them to be recovered from its input grid. -/
lemma restrictedEffectiveSampledSizes_computable_all :
    Computable (fun p : (BitString × ℕ) × ℕ =>
      restrictedEffectiveSampledSizes p.1.1 p.1.2 p.2) := by
  have hrange : Primrec (fun p : (BitString × ℕ) × ℕ =>
      List.range (p.1.2 + 1)) :=
    Primrec.list_range.comp
      (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
  have hbody : Primrec₂ (fun (p : (BitString × ℕ) × ℕ) (s : ℕ) =>
      2 ^ ((decode_restrictedCurveGridCode_sample p.1.1 s).2 - (p.2 + 1))) := by
    have hsample : Primrec (fun q : ((BitString × ℕ) × ℕ) × ℕ =>
        decode_restrictedCurveGridCode_sample q.1.1.1 q.2) :=
      decode_restrictedCurveGridCode_sample_primrec.comp (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
    exact twoPow_primrec.comp (Primrec.nat_sub.comp
      (Primrec.snd.comp hsample)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)))
  exact (Primrec.list_map hrange hbody).to_comp

/-! ### Uniform one-event executor -/

/-- Code-level anchored size schedule. -/
def restrictedAnchoredSizesFromCode (gridCode : BitString)
    (gridSteps Δ ambientLength : ℕ) : List ℕ :=
  2 ^ ambientLength :: restrictedEffectiveSampledSizes gridCode gridSteps Δ

/-- On a genuine grid code, the decoded size list is the anchored size list. -/
lemma restrictedAnchoredSizesFromCode_eq
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (Δ ambientLength : ℕ) :
    restrictedAnchoredSizesFromCode (restrictedCurveGridCode grid) N Δ
      ambientLength =
      restrictedEffectiveAnchoredSizes ambientLength Δ grid := rfl

/-- The canonical full-cube uniform code, primitively in the ambient length. -/
lemma fullCubeUniformCode_primrec : Primrec (fun ambientLength : ℕ =>
    (codedUniformOn (stringsOfLength ambientLength)
      (codedStringsOfLength_nonempty ambientLength)).code) := by
  have h := canonicalUniformCodeOfList_primrec.comp
    (canonicalFinsetList_toFinset_primrec.comp allStrings_primrec)
  refine h.of_eq (fun ambientLength => ?_)
  simpa [stringsOfLength] using
    (canonicalUniformCodeOfList_canonicalFinsetList
      (stringsOfLength ambientLength)
      (codedStringsOfLength_nonempty ambientLength))

/-- The rebuild-suffix input packet is primitive recursive in all fields. -/
lemma restrictedEffectiveRebuildSuffixInput_primrec_all :
    Primrec (fun p : (BitString × BitString) × (List ℕ × ℕ) =>
      restrictedEffectiveRebuildSuffixInput p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hsizesBits : Primrec (fun p : (BitString × BitString) × (List ℕ × ℕ) =>
      p.2.1.map Nat.bits) :=
    Primrec.list_map (Primrec.fst.comp Primrec.snd)
      (primrecNatBits.comp Primrec.snd).to₂
  unfold restrictedEffectiveRebuildSuffixInput
  exact listCode_primrec.comp
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.list_cons.comp (listCode_primrec.comp hsizesBits)
          (Primrec.list_cons.comp
            (primrecNatBits.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.const [])))))

/-- Code-level anchored initializer with an explicit overhead argument. -/
noncomputable def restrictedAnchoredInitialFromCode (𝒜 : DescriptionFamily)
    (q0 : ℕ) (gridCode : BitString) (gridSteps Δ ambientLength : ℕ) :
    Part BitString :=
  let Acode := (codedUniformOn (stringsOfLength ambientLength)
    (codedStringsOfLength_nonempty ambientLength)).code
  (restrictedEffectiveRebuildSuffix 𝒜
    (restrictedEffectiveRebuildSuffixInput Acode Acode
      (restrictedEffectiveSampledSizes gridCode gridSteps Δ) q0)).map
    (fun output =>
      restrictedEffectiveSampledStateCode Acode (decodeListCode output))

/-- With matching overhead, the code-level initializer is the anchored one. -/
lemma restrictedAnchoredInitialFromCode_eq (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (Δ ambientLength : ℕ) :
    restrictedAnchoredInitialFromCode 𝒜 (𝒜.overhead ambientLength)
      (restrictedCurveGridCode grid) N Δ ambientLength =
      restrictedEffectiveAnchoredInitialState 𝒜 ambientLength Δ grid := rfl

/-- Grid-derived decoder parameters, written using primitive-recursive binary
length rather than `Nat.log2`.  `max 1` also gives the intended denominator at
`n = 0`. -/
def anchoredDecodedLength (gridCode : BitString) : ℕ :=
  (decode_restrictedCurveGridCode_sample gridCode 0).2

/-- Decoded interval count `√(n / log n) + 1`, recomputed from the grid code. -/
def anchoredDecodedSteps (gridCode : BitString) : ℕ :=
  let n := anchoredDecodedLength gridCode
  Nat.sqrt (n / max 1 (Nat.bits n).length) + 1

/-- Decoded slack `sqrtSlack 8 n`, recomputed from the grid code. -/
def anchoredDecodedSlack (gridCode : BitString) : ℕ :=
  sqrtSlack 8 (anchoredDecodedLength gridCode)

/-- Decoded ambient length `n + logSlack 8 n`, recomputed from the grid code. -/
def anchoredDecodedAmbientLength (gridCode : BitString) : ℕ :=
  let n := anchoredDecodedLength gridCode
  n + logSlack 8 n

/-- The decoded base length is primitive recursive in the grid code. -/
lemma anchoredDecodedLength_primrec : Primrec anchoredDecodedLength := by
  unfold anchoredDecodedLength
  exact Primrec.snd.comp
    (decode_restrictedCurveGridCode_sample_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const 0)))

/-- The decoded interval count is primitive recursive in the grid code. -/
lemma anchoredDecodedSteps_primrec : Primrec anchoredDecodedSteps := by
  unfold anchoredDecodedSteps
  have hbitsLength : Primrec (fun gridCode : BitString =>
      (Nat.bits (anchoredDecodedLength gridCode)).length) :=
    Primrec.list_length.comp
      (primrecNatBits.comp anchoredDecodedLength_primrec)
  have hdenom := Primrec.nat_max.comp (Primrec.const 1) hbitsLength
  exact Primrec.succ.comp (Primrec.nat_sqrt.comp
    (Primrec.nat_div.comp anchoredDecodedLength_primrec hdenom))

/-- The decoded slack is primitive recursive in the grid code. -/
lemma anchoredDecodedSlack_primrec : Primrec anchoredDecodedSlack := by
  unfold anchoredDecodedSlack sqrtSlack
  have hbitsLength : Primrec (fun gridCode : BitString =>
      (Nat.bits (anchoredDecodedLength gridCode)).length) :=
    Primrec.list_length.comp
      (primrecNatBits.comp anchoredDecodedLength_primrec)
  have hsqrt := Primrec.nat_sqrt.comp (Primrec.nat_mul.comp
    anchoredDecodedLength_primrec hbitsLength)
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) hsqrt) (Primrec.const 8)

/-- The decoded ambient length is primitive recursive in the grid code. -/
lemma anchoredDecodedAmbientLength_primrec :
    Primrec anchoredDecodedAmbientLength := by
  unfold anchoredDecodedAmbientLength logSlack
  have hbitsLength : Primrec (fun gridCode : BitString =>
      (Nat.bits (anchoredDecodedLength gridCode)).length) :=
    Primrec.list_length.comp
      (primrecNatBits.comp anchoredDecodedLength_primrec)
  have hlogSlack := Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) hbitsLength) (Primrec.const 8)
  exact Primrec.nat_add.comp anchoredDecodedLength_primrec hlogSlack

/-- On a genuine grid code, the decoder recovers the ambient string length. -/
@[simp] lemma anchoredDecodedLength_eq
    {n k N : ℕ} {t : ℕ → ℕ} (grid : RestrictedCurveGrid n k N t) :
    anchoredDecodedLength (restrictedCurveGridCode grid) = n := by
  simp [anchoredDecodedLength, grid.j_start]

/-- Binary length with a `max 1` guard matches `Nat.log2 + 1`. -/
private lemma max_one_bits_length_eq_log2_add_one (n : ℕ) :
    max 1 (Nat.bits n).length = Nat.log2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hbits : (Nat.bits n).length = Nat.log2 n + 1 := by
      rw [Nat.size_eq_bits_len, Nat.le_antisymm_iff]
      constructor
      · rw [Nat.size_le]
        exact Nat.lt_log2_self
      · rw [Nat.add_one_le_iff, Nat.log2_lt hn.ne']
        exact Nat.lt_size_self n
    rw [hbits, max_eq_right]
    omega

/-- On a genuine balanced grid, the decoder recovers its number of sampled
intervals. -/
@[simp] lemma anchoredDecodedSteps_eq
    {n k N : ℕ} {t : ℕ → ℕ} (grid : RestrictedCurveGrid n k N t)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1) :
    anchoredDecodedSteps (restrictedCurveGridCode grid) = N := by
  unfold anchoredDecodedSteps
  simp only [anchoredDecodedLength_eq grid, max_one_bits_length_eq_log2_add_one n]
  rw [← hN]

@[simp] lemma anchoredDecodedSlack_eq
    {n k N : ℕ} {t : ℕ → ℕ} (grid : RestrictedCurveGrid n k N t) :
    anchoredDecodedSlack (restrictedCurveGridCode grid) = sqrtSlack 8 n := by
  simp [anchoredDecodedSlack]

@[simp] lemma anchoredDecodedAmbientLength_eq
    {n k N : ℕ} {t : ℕ → ℕ} (grid : RestrictedCurveGrid n k N t) :
    anchoredDecodedAmbientLength (restrictedCurveGridCode grid) =
      n + logSlack 8 n := by
  simp [anchoredDecodedAmbientLength]

/-- The decoder's event trace: search the first stream stage carrying `m`
events, then run the event-prefix executor from the code-level initializer.
All grid parameters are recomputed from `gridCode`. -/
noncomputable def anchoredDecoderTrace (𝒜 : DescriptionFamily) (c : Code)
    (gridCode : BitString) (q0 m : ℕ) : Part BitString :=
  let Nst := anchoredDecodedSteps gridCode
  let Δ := anchoredDecodedSlack gridCode
  let amb := anchoredDecodedAmbientLength gridCode
  (Nat.rfind (fun τ => Part.some (decide (m ≤
      (restrictedSampledBadCodeStream c gridCode 𝒜.toPre Nst Δ
        τ).length)))).bind
    (fun τ => (restrictedAnchoredInitialFromCode 𝒜 q0 gridCode Nst Δ
        amb).bind
      (fun st0 => restrictedEventPrefixRun 𝒜 q0
        (restrictedAnchoredSizesFromCode gridCode Nst Δ amb) st0
        (restrictedSampledBadCodeStream c gridCode 𝒜.toPre Nst Δ τ) m))

/-- Decoded level-`s+1` model list of a state code. -/
def anchoredModelListAt (s : ℕ) (stateCode : BitString) : List BitString :=
  decodeCoverCodeList
    ((decodeListCode (restrictedSelectorField stateCode 1)).getD (s + 1) [])

/-- Decoding the level-`s+1` model list is primitive recursive. -/
theorem anchoredModelListAt_primrec :
    Primrec₂ (fun (s : ℕ) (stateCode : BitString) =>
      anchoredModelListAt s stateCode) := by
  unfold anchoredModelListAt
  exact decodeCoverCodeList_primrec.comp
    ((Primrec.list_getD []).comp
      (decodeListCode_primrec.comp
        (restrictedSelectorField_primrec.comp Primrec.snd (Primrec.const 1)))
      (Primrec.succ.comp Primrec.fst))

/-- Reading sampled level `s` from a decoded anchored state gives its
canonical model list. -/
lemma anchoredModelListAt_eq
    {𝒜 : DescriptionFamily} {n k N ambientLength Δ : ℕ}
    {target : ℕ → ℕ} {grid : RestrictedCurveGrid n k N target}
    {stateCode : BitString}
    {state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
      (2 * 𝒜.overhead ambientLength)
      (restrictedAnchoredTarget ambientLength Δ grid)}
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (s : ℕ) (hs : s ≤ N) :
    anchoredModelListAt s stateCode =
      canonicalFinsetList (state.B (s + 1)) := by
  exact restrictedAnchoredRun_sample_getD hstate s hs

/-- Consequently the list-level encoder recovers the sampled model's
canonical uniform code. -/
lemma uniformCodeOfList_anchoredModelListAt_eq
    {𝒜 : DescriptionFamily} {n k N ambientLength Δ : ℕ}
    {target : ℕ → ℕ} {grid : RestrictedCurveGrid n k N target}
    {stateCode : BitString}
    {state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
      (2 * 𝒜.overhead ambientLength)
      (restrictedAnchoredTarget ambientLength Δ grid)}
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (s : ℕ) (hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty) :
    uniformCodeOfList (anchoredModelListAt s stateCode) =
      (codedUniformOn (state.B (s + 1)) hS).code := by
  rw [anchoredModelListAt_eq hstate s hs]
  exact uniformCodeOfList_canonical _ _

/-- Change-counting trace: after `m` events, the number of times the decoded
level-`s+1` model list has changed, together with its current value. -/
noncomputable def anchoredChangeTrace (𝒜 : DescriptionFamily) (c : Code)
    (gridCode : BitString) (q0 s : ℕ) : ℕ → Part (ℕ × List BitString)
  | 0 => (anchoredDecoderTrace 𝒜 c gridCode q0 0).map
      (fun code => (0, anchoredModelListAt s code))
  | m + 1 => (anchoredChangeTrace 𝒜 c gridCode q0 s m).bind (fun p =>
      (anchoredDecoderTrace 𝒜 c gridCode q0 (m + 1)).map (fun code =>
        if anchoredModelListAt s code = p.2 then (p.1, p.2)
        else (p.1 + 1, anchoredModelListAt s code)))

/-- The version decoder.  Input: `listCode [gridCode, bits q0, bits s,
bits v]`.  Output: the canonical uniform code of the sampled model at grid
scale `s` right after the `v`-th change of its decoded trace. -/
noncomputable def anchoredVersionDecoder (𝒜 : DescriptionFamily) (c : Code)
    (bundle : BitString) : Part BitString :=
  let parts := decodeListCode bundle
  let gridCode := parts.getD 0 []
  let q0 := bitsToNat (parts.getD 1 [])
  let s := bitsToNat (parts.getD 2 [])
  let v := bitsToNat (parts.getD 3 [])
  (Nat.rfind (fun m => (anchoredChangeTrace 𝒜 c gridCode q0 s m).map
      (fun p => decide (v ≤ p.1)))).bind
    (fun m => (anchoredChangeTrace 𝒜 c gridCode q0 s m).map
      (fun p => uniformCodeOfList p.2))

/-- On a genuine grid, the decoder trace replays any available event prefix:
the stage search may stop before `T`, and stream prefix monotonicity ensures
that the first `m` events — hence the executor result — agree. -/
lemma anchoredDecoderTrace_replay
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (T m : ℕ) (code : BitString)
    (hm : m ≤ (restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n) T).length)
    (hfold :
      (restrictedEffectiveAnchoredInitialState 𝒜
          (n + logSlack 8 n) (sqrtSlack 8 n) grid).bind
        (fun st0 => restrictedEventPrefixRun 𝒜
          (𝒜.overhead (n + logSlack 8 n))
          (restrictedEffectiveAnchoredSizes
            (n + logSlack 8 n) (sqrtSlack 8 n) grid) st0
          (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
            𝒜.toPre N (sqrtSlack 8 n) T) m) = Part.some code) :
    anchoredDecoderTrace 𝒜 c (restrictedCurveGridCode grid)
      (𝒜.overhead (n + logSlack 8 n)) m = Part.some code := by
  have hex : ∃ τ, m ≤ (restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n) τ).length :=
    ⟨T, hm⟩
  have hfind : Nat.rfind (fun τ => Part.some (decide (m ≤
      (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) τ).length))) = Part.some (Nat.find hex) :=
    Part.eq_some_iff.mpr (Nat.mem_rfind.mpr
      ⟨by simpa using Nat.find_spec hex,
        fun {j} hj => by simpa using Nat.find_min hex hj⟩)
  have hprefix : restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
        (Nat.find hex) <+:
      restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T :=
    restrictedSampledBadCodeStream_prefix_of_le _ _ _ _ _
      (Nat.find_min' hex hm)
  have hrun : (fun st0 : BitString => restrictedEventPrefixRun 𝒜
        (𝒜.overhead (n + logSlack 8 n))
        (restrictedEffectiveAnchoredSizes (n + logSlack 8 n) (sqrtSlack 8 n)
          grid) st0
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) (Nat.find hex)) m) =
      (fun st0 : BitString => restrictedEventPrefixRun 𝒜
        (𝒜.overhead (n + logSlack 8 n))
        (restrictedEffectiveAnchoredSizes (n + logSlack 8 n) (sqrtSlack 8 n)
          grid) st0
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T) m) :=
    funext fun st0 => restrictedEventPrefixRun_congr 𝒜 _ _ _ m
      (fun i hi => (prefix_getD_eq hprefix
        (lt_of_lt_of_le hi (Nat.find_spec hex))).symm)
  unfold anchoredDecoderTrace
  simp only [anchoredDecodedSteps_eq grid hN, anchoredDecodedSlack_eq grid,
    anchoredDecodedAmbientLength_eq grid]
  rw [hfind, Part.bind_some]
  simp only [restrictedAnchoredSizesFromCode_eq grid,
    restrictedAnchoredInitialFromCode_eq 𝒜 grid]
  rw [hrun]
  exact hfold

end Kolmogorov
