import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver

/-!
# The tail of the bounded enumeration: what it contains

`enumerationTail m s` is the set of outputs of plain complexity at most `m` that have still
not appeared when the enumeration for the smaller bound `m - s` has completed, and
`enumerationTailCount` is its cardinality.  The tail is the reservoir the standard-block
construction draws its non-stochastic strings from: its members are hard to name at bound
`m - s` but easy at bound `m`.

This part fixes what the tail is and how large it is from above.  `mem_enumerationTail` and
`mem_enumerationTail_iff_plainK_le` characterise membership, `plainK_gt_of_mem_enumerationTail`
gives the complexity lower bound its members enjoy, and
`stageLength_add_enumerationTailCount` is the bookkeeping identity — current distinct outputs
plus tail count equals the final count — from which the upper bounds
`enumerationTailCount_le_omegaCount` and `enumerationTailCount_le_omegaCount_sub` follow,
together with the boundary case `enumerationTailCount_zero_slack`.

The lower bound and the description of a tail member are in `Part02`.
-/



namespace Kolmogorov

open Nat.Partrec (Code)

/-- Outputs of plain complexity at most `m` that have not appeared by the
completion time for bound `m - s`. -/
noncomputable def enumerationTail (c : Code) (m s : ℕ) : Finset BitString :=
  completedBoundedOutputFinset c m \
    (boundedOutputStage c m (boundedOutputCompletionTime c (m - s))).toFinset

/-- Cardinality of the exact enumeration tail. -/
noncomputable def enumerationTailCount (c : Code) (m s : ℕ) : ℕ :=
  (enumerationTail c m s).card

/-- The tail at slack `s` consists of the outputs of bound `m` that have not yet
appeared by the stage at which the bound `m - s` is complete. -/
@[simp] theorem mem_enumerationTail (c : Code) (m s : ℕ) (x : BitString) :
    x ∈ enumerationTail c m s ↔
      x ∈ completedBoundedOutput c m ∧
      x ∉ boundedOutputStage c m (boundedOutputCompletionTime c (m - s)) := by
  simp [enumerationTail, completedBoundedOutputFinset]

/-- Membership in the tail, stated through plain complexity: `x` has complexity at
most `m` and is missing at the completion stage of `m - s`. -/
theorem mem_enumerationTail_iff_plainK_le
    {V : Map} {c : Code} (hc : IsCodeFor c V) (m s : ℕ) (x : BitString) :
    x ∈ enumerationTail c m s ↔
      plainK V x ≤ (m : ENat) ∧
      x ∉ boundedOutputStage c m (boundedOutputCompletionTime c (m - s)) := by
  rw [mem_enumerationTail, mem_completedBoundedOutput_iff_plainK_le hc]

/-- By time `B'(m-s)`, the bound-`m` enumeration contains every output of
complexity at most `m-s`. -/
theorem mem_stage_at_lower_completion_of_plainK_le
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {m s : ℕ} {x : BitString} (hx : plainK V x ≤ ((m - s : ℕ) : ENat)) :
    x ∈ boundedOutputStage c m (boundedOutputCompletionTime c (m - s)) := by
  have hxcomp : x ∈ completedBoundedOutput c (m - s) :=
    (mem_completedBoundedOutput_iff_plainK_le hc (m - s) x).mpr hx
  have hxstage :
      x ∈ boundedOutputStage c (m - s)
        (boundedOutputCompletionTime c (m - s)) := by
    rw [boundedOutputStage_eq_completed_at_completion]
    exact hxcomp
  exact boundedOutputStage_mem_of_bound_le (Nat.sub_le m s) hxstage

/-- Every string still missing at time `B'(m-s)` has complexity strictly above
the completed lower bound `m-s`. -/
theorem plainK_gt_of_mem_enumerationTail
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {m s : ℕ} {x : BitString} (hx : x ∈ enumerationTail c m s) :
    ((m - s : ℕ) : ENat) < plainK V x := by
  apply lt_of_not_ge
  intro hle
  exact (mem_enumerationTail c m s x).mp hx |>.2
    (mem_stage_at_lower_completion_of_plainK_le hc hle)

/-- The semantic tail count agrees with "final count minus current distinct
count"; no duplicate correction is hidden in this identity. -/
theorem enumerationTailCount_eq_sub (c : Code) (m s : ℕ) :
    enumerationTailCount c m s =
      omegaCount c m -
        (boundedOutputStage c m
          (boundedOutputCompletionTime c (m - s))).length := by
  unfold enumerationTailCount enumerationTail
  rw [Finset.card_sdiff_of_subset
    (boundedOutputStage_toFinset_subset_completed c m
      (boundedOutputCompletionTime c (m - s)))]
  unfold completedBoundedOutputFinset omegaCount
  rw [List.toFinset_card_of_nodup
      (by
        unfold completedBoundedOutput
        exact boundedOutputStage_nodup c m (maxHaltingStage c m)),
    List.toFinset_card_of_nodup
      (boundedOutputStage_nodup c m
        (boundedOutputCompletionTime c (m - s)))]

/-- The current distinct-output count plus the exact tail count is the final
count.  This is the completion target used by the lower-bound reconstruction:
once `enumerationTailCount c m s` further outputs have appeared after the
lower-bound completion stage, the bound-`m` enumeration is complete. -/
theorem stageLength_add_enumerationTailCount (c : Code) (m s : ℕ) :
    (boundedOutputStage c m
        (boundedOutputCompletionTime c (m - s))).length +
      enumerationTailCount c m s =
        omegaCount c m := by
  rw [enumerationTailCount_eq_sub]
  exact Nat.add_sub_of_le
    ((boundedOutputStage_prefix_completed c m
      (boundedOutputCompletionTime c (m - s))).length_le)

/-- Reaching the lower-stage count plus the exact tail count is equivalent to
reaching the final distinct-output count, and therefore identifies the
completed bound-`m` list. -/
theorem boundedOutputStage_eq_completed_of_length_eq_lower_add_tail
    (c : Code) (m s t : ℕ)
    (hlen :
      (boundedOutputStage c m t).length =
        (boundedOutputStage c m
          (boundedOutputCompletionTime c (m - s))).length +
          enumerationTailCount c m s) :
    boundedOutputStage c m t = completedBoundedOutput c m := by
  apply boundedOutputStage_eq_completed_of_length_eq
  rw [hlen, stageLength_add_enumerationTailCount]

/-- Boundary case: after the bound-`m` enumeration has completed, no bound-`m`
output remains. -/
@[simp] theorem enumerationTail_zero_slack (c : Code) (m : ℕ) :
    enumerationTail c m 0 = ∅ := by
  unfold enumerationTail completedBoundedOutputFinset
  rw [Nat.sub_zero, boundedOutputStage_eq_completed_at_completion]
  simp

/-- At slack zero the tail is empty. -/
@[simp] theorem enumerationTailCount_zero_slack (c : Code) (m : ℕ) :
    enumerationTailCount c m 0 = 0 := by
  simp [enumerationTailCount]

/-- The tail count is at most the total number of outputs of bound `m`. -/
theorem enumerationTailCount_le_omegaCount (c : Code) (m s : ℕ) :
    enumerationTailCount c m s ≤ omegaCount c m := by
  rw [enumerationTailCount_eq_sub]
  exact Nat.sub_le _ _

/-- At a stage past the completion time of a lower bound `r`, the outputs of bound
`k` still missing are at most the tail count at slack `k - r`. -/
theorem missingAtStage_le_enumerationTailCount
    (c : Code) {k r t : ℕ}
    (hr : r ≤ k)
    (ht : boundedOutputCompletionTime c r ≤ t) :
    omegaCount c k - (boundedOutputStage c k t).length ≤
      enumerationTailCount c k (k - r) := by
  have h_sub : k - (k - r) = r := by omega
  rw [enumerationTailCount_eq_sub, h_sub]
  apply Nat.sub_le_sub_left
  exact (boundedOutputStage_prefix_of_le c k ht).length_le

/-- Every output of bound `m - s` has appeared in the bound-`m` enumeration by the
completion stage of `m - s`. -/
theorem completedLower_subset_stageAtLowerCompletion
    (c : Code) (m s : ℕ) :
    completedBoundedOutputFinset c (m - s) ⊆
      (boundedOutputStage c m
        (boundedOutputCompletionTime c (m - s))).toFinset := by
  intro x hx
  rw [completedBoundedOutputFinset, List.mem_toFinset] at hx
  rw [List.mem_toFinset]
  have hxstage :
      x ∈ boundedOutputStage c (m - s)
        (boundedOutputCompletionTime c (m - s)) := by
    rw [boundedOutputStage_eq_completed_at_completion]
    exact hx
  exact boundedOutputStage_mem_of_bound_le (Nat.sub_le m s) hxstage

/-- The tail count is at most the difference of the two output counts. -/
theorem enumerationTailCount_le_omegaCount_sub
    (c : Code) (m s : ℕ) :
    enumerationTailCount c m s ≤
      omegaCount c m - omegaCount c (m - s) := by
  rw [enumerationTailCount_eq_sub]
  apply Nat.sub_le_sub_left
  have h_sub := completedLower_subset_stageAtLowerCompletion c m s
  have h_card := Finset.card_le_card h_sub
  have h_card1 : (completedBoundedOutputFinset c (m - s)).card = omegaCount c (m - s) := by
    unfold completedBoundedOutputFinset omegaCount
    rw [List.toFinset_card_of_nodup]
    unfold completedBoundedOutput
    exact boundedOutputStage_nodup c (m - s) (maxHaltingStage c (m - s))
  have h_card2 :
      (boundedOutputStage c m (boundedOutputCompletionTime c (m - s))).toFinset.card =
        (boundedOutputStage c m (boundedOutputCompletionTime c (m - s))).length := by
    rw [List.toFinset_card_of_nodup]
    exact boundedOutputStage_nodup c m _
  rw [h_card1, h_card2] at h_card
  exact h_card

/-- A rank below `2 ^ (s - logSlack C m)` is written in at most `s - logSlack C m`
bits, so its length plus the slack stays below `s`. -/
theorem bits_length_add_logSlack_le_of_lt_pow_sub
    {C m s r : ℕ}
    (hslack : logSlack C m ≤ s)
    (hr : r < 2 ^ (s - logSlack C m)) :
    (Nat.bits r).length + logSlack C m ≤ s := by
  have hlen : (Nat.bits r).length ≤ s - logSlack C m := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hr
  exact Nat.add_le_of_le_sub hslack hlen

/-- Canonical input for the lower-tail diagonal reconstruction.  The short
self-delimiting header carries `m` and `s`; the undoubled payload carries the
fixed-width code of `Ω_(m-s)` followed by the proposed fixed-width tail count.
Keeping the long payload in the second component of `pairCode` is essential:
only the logarithmic-size header is doubled. -/
noncomputable def enumerationTailLowerInput
    (c : Code) (m s tailWidth : ℕ) : BitString :=
  pairCode (pairCode (Nat.bits m) (Nat.bits s))
    (omegaFixedCode c (m - s) ++
      fixedWidthNatCode (enumerationTailCount c m s) tailWidth)

/-- Exact length accounting for the lower-tail reconstruction input. -/
theorem enumerationTailLowerInput_length
    {c : Code} {m s tailWidth : ℕ}
    (htail : enumerationTailCount c m s < 2 ^ tailWidth) :
    (enumerationTailLowerInput c m s tailWidth).length =
      m - s + tailWidth +
        4 * (Nat.bits m).length + 2 * (Nat.bits s).length + 4 := by
  unfold enumerationTailLowerInput
  rw [length_pairCode, length_pairCode, List.length_append,
    omegaFixedCode_length, fixedWidthNatCode_length htail]
  omega


/-- The lower-tail input exposes exactly the two parameters and the two counts
consumed by the reconstruction procedure. -/
theorem enumerationTailLowerInput_decode
    (c : Code) (m s tailWidth : ℕ) :
    bitsToNat (decodeFirst (decodeFirst
      (enumerationTailLowerInput c m s tailWidth))) = m ∧
    bitsToNat (decodeSecond (decodeFirst
      (enumerationTailLowerInput c m s tailWidth))) = s ∧
    decodeFixedWidthNatCode
      ((decodeSecond (enumerationTailLowerInput c m s tailWidth)).take
        (m - s + 1)) = omegaCount c (m - s) ∧
    decodeFixedWidthNatCode
      ((decodeSecond (enumerationTailLowerInput c m s tailWidth)).drop
        (m - s + 1)) = enumerationTailCount c m s := by
  unfold enumerationTailLowerInput
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  rw [← omegaFixedCode_length c (m - s), List.take_left, List.drop_left,
    decode_omegaFixedCode, decodeFixedWidthNatCode_encode]
  simp

/-- The visible complexity bound carried by a lower-tail reconstruction input. -/
def enumerationTailLowerM (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeFirst z))

/-- The visible tail parameter carried by a lower-tail reconstruction input. -/
def enumerationTailLowerS (z : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeFirst z))

/-- The fixed-width `Ω_(m-s)` field of a lower-tail reconstruction input. -/
def enumerationTailLowerOmegaCode (z : BitString) : BitString :=
  (decodeSecond z).take
    (enumerationTailLowerM z - enumerationTailLowerS z + 1)

/-- The proposed exact number of outputs remaining after `B'(m-s)`. -/
def enumerationTailLowerCount (z : BitString) : ℕ :=
  decodeFixedWidthNatCode
    ((decodeSecond z).drop
      (enumerationTailLowerM z - enumerationTailLowerS z + 1))

/-- The bound is read back from an assembled lower-tail input. -/
@[simp] theorem enumerationTailLowerM_input
    (c : Code) (m s tailWidth : ℕ) :
    enumerationTailLowerM (enumerationTailLowerInput c m s tailWidth) = m := by
  unfold enumerationTailLowerM enumerationTailLowerInput
  simp only [decodeFirst_pairCode, bitsToNat_bits]

/-- The slack is read back from an assembled lower-tail input. -/
@[simp] theorem enumerationTailLowerS_input
    (c : Code) (m s tailWidth : ℕ) :
    enumerationTailLowerS (enumerationTailLowerInput c m s tailWidth) = s := by
  unfold enumerationTailLowerS enumerationTailLowerInput
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

/-- The fixed-width count of the lower bound is read back from an assembled
lower-tail input. -/
@[simp] theorem enumerationTailLowerOmegaCode_input
    (c : Code) (m s tailWidth : ℕ) :
    enumerationTailLowerOmegaCode (enumerationTailLowerInput c m s tailWidth) =
      omegaFixedCode c (m - s) := by
  unfold enumerationTailLowerOmegaCode
  rw [enumerationTailLowerM_input, enumerationTailLowerS_input]
  unfold enumerationTailLowerInput
  rw [decodeSecond_pairCode, ← omegaFixedCode_length c (m - s),
    List.take_left]

/-- The tail count is read back from an assembled lower-tail input. -/
@[simp] theorem enumerationTailLowerCount_input
    (c : Code) (m s tailWidth : ℕ) :
    enumerationTailLowerCount (enumerationTailLowerInput c m s tailWidth) =
      enumerationTailCount c m s := by
  unfold enumerationTailLowerCount
  rw [enumerationTailLowerM_input, enumerationTailLowerS_input]
  unfold enumerationTailLowerInput
  rw [decodeSecond_pairCode, ← omegaFixedCode_length c (m - s),
    List.drop_left, decodeFixedWidthNatCode_encode]

/-- Partial reconstruction used by the lower tail estimate.  It first recovers
`B'(m-s)` from the fixed-width lower Omega count, then uses the proposed tail
count to recognize completion of the bound-`m` enumeration, and finally returns
a length-`m+1` string outside that completed enumeration. -/
noncomputable def enumerationTailLowerSelector
    (c : Code) (z : BitString) : Part BitString := do
  let tBits ← completionFromOmega c (enumerationTailLowerOmegaCode z)
  let t₀ := bitsToNat tBits
  let target :=
    (boundedOutputStage c (enumerationTailLowerM z) t₀).length +
      enumerationTailLowerCount z
  let t ← Nat.rfind (fun t => Part.some
    ((boundedOutputStage c (enumerationTailLowerM z) t).length == target))
  let x ← Part.ofOption
    ((canonicalFinsetList
      (stringsOfLength (enumerationTailLowerM z + 1))).find?
        (fun x => decide
          (x ∉ boundedOutputStage c (enumerationTailLowerM z) t)))
  Part.some x

/-- Reading the bound off a lower-tail input is primitive recursive. -/
theorem enumerationTailLowerM_primrec : Primrec enumerationTailLowerM := by
  exact bitsToNat_primrec.comp
    (CodedFiniteDistribution.decodeFirst_primrec.comp CodedFiniteDistribution.decodeFirst_primrec)

/-- Reading the slack off a lower-tail input is primitive recursive. -/
theorem enumerationTailLowerS_primrec : Primrec enumerationTailLowerS := by
  exact bitsToNat_primrec.comp
    (CodedFiniteDistribution.decodeSecond_primrec.comp CodedFiniteDistribution.decodeFirst_primrec)

/-- The width `m - s + 1` of the lower count block is primitive recursive in the
input. -/
theorem enumerationTailLowerWidth_primrec :
    Primrec (fun z : BitString =>
      enumerationTailLowerM z - enumerationTailLowerS z + 1) := by
  exact Primrec.nat_add.comp
    (Primrec.nat_sub.comp enumerationTailLowerM_primrec
      enumerationTailLowerS_primrec)
    (Primrec.const 1)

/-- Reading the lower count block off a lower-tail input is primitive recursive. -/
theorem enumerationTailLowerOmegaCode_primrec :
    Primrec enumerationTailLowerOmegaCode := by
  unfold enumerationTailLowerOmegaCode
  exact Primrec.list_take.comp enumerationTailLowerWidth_primrec
    CodedFiniteDistribution.decodeSecond_primrec

/-- Reading the tail count off a lower-tail input is primitive recursive. -/
theorem enumerationTailLowerCount_primrec :
    Primrec enumerationTailLowerCount := by
  unfold enumerationTailLowerCount
  exact decodeFixedWidthNatCode_primrec.comp
    (Primrec.list_drop.comp enumerationTailLowerWidth_primrec
      CodedFiniteDistribution.decodeSecond_primrec)

/-- The lower-tail selector is a partial recursive function of its input. -/
theorem enumerationTailLowerSelector_partrec
    (c : Code) :
    Partrec (enumerationTailLowerSelector c) := by
  have hcompletion : Partrec (fun z : BitString =>
      completionFromOmega c (enumerationTailLowerOmegaCode z)) :=
    Partrec.comp (completionFromOmega_partrec c)
      enumerationTailLowerOmegaCode_primrec.to_comp
  have ht₀ : Primrec (fun q : (BitString × BitString) × ℕ =>
      bitsToNat q.1.2) :=
    bitsToNat_primrec.comp (Primrec.snd.comp Primrec.fst)
  have hm : Primrec (fun q : (BitString × BitString) × ℕ =>
      enumerationTailLowerM q.1.1) :=
    enumerationTailLowerM_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hstageAtLower : Primrec (fun q : (BitString × BitString) × ℕ =>
      boundedOutputStage c (enumerationTailLowerM q.1.1)
        (bitsToNat q.1.2)) :=
    (boundedOutputStage_primrec c).comp (Primrec.pair hm ht₀)
  have htail : Primrec (fun q : (BitString × BitString) × ℕ =>
      enumerationTailLowerCount q.1.1) :=
    enumerationTailLowerCount_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  have htarget : Primrec (fun q : (BitString × BitString) × ℕ =>
      (boundedOutputStage c (enumerationTailLowerM q.1.1)
          (bitsToNat q.1.2)).length +
        enumerationTailLowerCount q.1.1) :=
    Primrec.nat_add.comp
      (Primrec.list_length.comp hstageAtLower) htail
  have hstage : Primrec (fun q : (BitString × BitString) × ℕ =>
      boundedOutputStage c (enumerationTailLowerM q.1.1) q.2) :=
    (boundedOutputStage_primrec c).comp (Primrec.pair hm Primrec.snd)
  have hcheck : Computable₂
      (fun (q : BitString × BitString) (t : ℕ) =>
        (boundedOutputStage c (enumerationTailLowerM q.1) t).length ==
          ((boundedOutputStage c (enumerationTailLowerM q.1)
              (bitsToNat q.2)).length +
            enumerationTailLowerCount q.1)) :=
    (Primrec.beq.comp (Primrec.list_length.comp hstage) htarget).to_comp.to₂
  have hsearch : Partrec (fun q : BitString × BitString =>
      Nat.rfind (fun t => Part.some
        ((boundedOutputStage c (enumerationTailLowerM q.1) t).length ==
          ((boundedOutputStage c (enumerationTailLowerM q.1)
              (bitsToNat q.2)).length +
            enumerationTailLowerCount q.1)))) :=
    Partrec.rfind hcheck.partrec₂
  have hstrings : Primrec (fun q : (BitString × BitString) × ℕ =>
      canonicalFinsetList
        (stringsOfLength (enumerationTailLowerM q.1.1 + 1))) := by
    exact canonicalFinsetList_toFinset_primrec.comp
      (Kolmogorov.CodedFiniteDistribution.allStrings_primrec.comp
        (Primrec.succ.comp
          (enumerationTailLowerM_primrec.comp
            (Primrec.fst.comp Primrec.fst))))
  have hnotmem : Primrec₂
      (fun (q : (BitString × BitString) × ℕ) (x : BitString) =>
        decide
          (x ∉ boundedOutputStage c
            (enumerationTailLowerM q.1.1) q.2)) := by
    refine (Primrec.not.comp
      (bitString_mem_primrec.comp Primrec.snd
        (hstage.comp Primrec.fst))).to₂.of_eq ?_
    intro q x
    simp
  have hfindOpt : Primrec (fun q : (BitString × BitString) × ℕ =>
      (canonicalFinsetList
        (stringsOfLength (enumerationTailLowerM q.1.1 + 1))).find?
          (fun x => decide
            (x ∉ boundedOutputStage c
              (enumerationTailLowerM q.1.1) q.2))) :=
    list_find?_primrec hstrings hnotmem
  have hfindPart : Partrec (fun q : (BitString × BitString) × ℕ =>
      Part.ofOption
        ((canonicalFinsetList
          (stringsOfLength (enumerationTailLowerM q.1.1 + 1))).find?
            (fun x => decide
              (x ∉ boundedOutputStage c
                (enumerationTailLowerM q.1.1) q.2)))) :=
    hfindOpt.to_comp.ofOption
  have hpure : Partrec₂
      (fun (_ : (BitString × BitString) × ℕ) (x : BitString) =>
        Part.some x) :=
    (Partrec.comp Partrec.some Computable.snd).to₂
  have hfind : Partrec₂
      (fun (q : BitString × BitString) (t : ℕ) =>
        (Part.ofOption
          ((canonicalFinsetList
            (stringsOfLength (enumerationTailLowerM q.1 + 1))).find?
              (fun x => decide
                (x ∉ boundedOutputStage c
                  (enumerationTailLowerM q.1) t)))).bind
          (fun x => Part.some x)) :=
    (Partrec.bind hfindPart hpure).to₂
  have hafter : Partrec₂
      (fun (z tBits : BitString) =>
        (Nat.rfind (fun t => Part.some
          ((boundedOutputStage c (enumerationTailLowerM z) t).length ==
            ((boundedOutputStage c (enumerationTailLowerM z)
                (bitsToNat tBits)).length +
              enumerationTailLowerCount z)))).bind
          (fun t =>
            (Part.ofOption
              ((canonicalFinsetList
                (stringsOfLength (enumerationTailLowerM z + 1))).find?
                  (fun x => decide
                    (x ∉ boundedOutputStage c
                      (enumerationTailLowerM z) t)))).bind
              (fun x => Part.some x))) :=
    (Partrec.bind hsearch hfind).to₂
  exact (Partrec.bind hcompletion hafter).of_eq (fun _ => rfl)

/-- On its intended input the lower-tail selector outputs a string of length `m + 1`
of plain complexity greater than `m`. -/
theorem enumerationTailLowerSelector_intended_input
    (c : Code) (m s tailWidth : ℕ) :
    ∃ x,
      x ∈ enumerationTailLowerSelector c
        (enumerationTailLowerInput c m s tailWidth) ∧
      x.length = m + 1 ∧
      x ∉ completedBoundedOutput c m := by
  let lowerTime := boundedOutputCompletionTime c (m - s)
  let completeTime := boundedOutputCompletionTime c m
  have hlowerTarget :
      (boundedOutputStage c m lowerTime).length +
        enumerationTailCount c m s = omegaCount c m := by
    simpa [lowerTime] using stageLength_add_enumerationTailCount c m s
  have hcompleteLength :
      (boundedOutputStage c m completeTime).length = omegaCount c m := by
    simpa [completeTime, omegaCount] using
      boundedOutputCompletionTime_spec c m
  have hcompleteNodup :
      (boundedOutputStage c m completeTime).Nodup :=
    boundedOutputStage_nodup c m completeTime
  have hcompleteShort :
      (boundedOutputStage c m completeTime).length < 2 ^ (m + 1) := by
    rw [hcompleteLength]
    exact omegaCount_lt_two_pow_succ c m
  obtain ⟨x₀, hx₀all, hx₀missing⟩ :=
    exists_mem_allStrings_not_mem_of_length_lt
      hcompleteNodup hcompleteShort
  let fullList := canonicalFinsetList (stringsOfLength (m + 1))
  have hx₀full : x₀ ∈ fullList := by
    apply mem_canonicalFinsetList.mpr
    exact (mem_stringsOfLength (m + 1) x₀).mpr
      ((mem_allStrings (m + 1) x₀).mp hx₀all)
  obtain ⟨x, hxfind⟩ :
      ∃ x, fullList.find?
        (fun y => decide
          (y ∉ boundedOutputStage c m completeTime)) = some x := by
    apply Option.isSome_iff_exists.mp
    rw [List.find?_isSome]
    exact ⟨x₀, hx₀full, by simp [hx₀missing]⟩
  have hxfull : x ∈ fullList :=
    List.mem_of_find?_eq_some hxfind
  have hxlen : x.length = m + 1 := by
    exact (mem_stringsOfLength (m + 1) x).mp
      (mem_canonicalFinsetList.mp hxfull)
  have hxmissingStage :
      x ∉ boundedOutputStage c m completeTime := by
    have hpred := List.find?_some hxfind
    simpa using hpred
  have hxmissingCompleted : x ∉ completedBoundedOutput c m := by
    rw [← boundedOutputStage_eq_completed_at_completion c m]
    simpa [completeTime] using hxmissingStage
  have hcompleteSearch :
      completeTime ∈ Nat.rfind
        ((fun t : ℕ => Part.some
          ((boundedOutputStage c m t).length ==
            ((boundedOutputStage c m lowerTime).length +
              enumerationTailCount c m s))) : ℕ →. Bool) := by
    rw [@Nat.mem_rfind
      ((fun t : ℕ => Part.some
        ((boundedOutputStage c m t).length ==
          ((boundedOutputStage c m lowerTime).length +
            enumerationTailCount c m s))) : ℕ →. Bool)
      completeTime]
    refine ⟨?_, ?_⟩
    · simp [hcompleteLength, hlowerTarget]
    · intro n hn
      have hne :
          (boundedOutputStage c m n).length ≠ omegaCount c m := by
        intro heq
        have hle : boundedOutputCompletionTime c m ≤ n :=
          boundedOutputCompletionTime_le_complete_stage c m n
            (by simpa [omegaCount] using heq)
        dsimp [completeTime] at hn
        omega
      rw [hlowerTarget]
      simp [hne]
  refine ⟨x, ?_, hxlen, hxmissingCompleted⟩
  unfold enumerationTailLowerSelector
  simp only [enumerationTailLowerOmegaCode_input,
    enumerationTailLowerM_input, enumerationTailLowerCount_input]
  change x ∈ (completionFromOmega c (omegaFixedCode c (m - s))).bind
    (fun tBits =>
      (Nat.rfind (fun t => Part.some
        ((boundedOutputStage c m t).length ==
          ((boundedOutputStage c m (bitsToNat tBits)).length +
            enumerationTailCount c m s)))).bind
        (fun t =>
          (Part.ofOption
            ((canonicalFinsetList (stringsOfLength (m + 1))).find?
              (fun y => decide
                (y ∉ boundedOutputStage c m t)))).bind
            (fun y => Part.some y)))
  rw [Part.mem_bind_iff]
  refine ⟨Nat.bits lowerTime, ?_, ?_⟩
  · simpa [enumerationTailLowerOmegaCode_input, lowerTime] using
      completionFromOmega_omegaFixedCode c (m - s)
  · simp only [bitsToNat_bits]
    rw [Part.mem_bind_iff]
    refine ⟨completeTime, hcompleteSearch, ?_⟩
    rw [show
      (canonicalFinsetList (stringsOfLength (m + 1))).find?
          (fun y => decide
            (y ∉ boundedOutputStage c m completeTime)) = some x by
        simpa [fullList] using hxfind]
    rw [Part.mem_bind_iff]
    exact ⟨x, Part.mem_some x, Part.mem_some x⟩

end Kolmogorov
