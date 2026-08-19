import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.BusyBeaver

/-!
# VS40 Section 4, Milestone B3: exact enumeration-tail coordinates

This file fixes the finite object whose asymptotic size is estimated in
`prop:enumeration-tail`.  At time `B'(m-s)` it contains exactly the completed
bound-`m` outputs that have not yet appeared in the bound-`m` enumeration.

The exact `s = 0` theorem is deliberately exposed: the tail after `B'(m)` is
empty.  Consequently a later positive power-of-two lower bound needs a genuine
large-`s` hypothesis, not only `s ≤ m`.
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

@[simp] theorem mem_enumerationTail (c : Code) (m s : ℕ) (x : BitString) :
    x ∈ enumerationTail c m s ↔
      x ∈ completedBoundedOutput c m ∧
      x ∉ boundedOutputStage c m (boundedOutputCompletionTime c (m - s)) := by
  simp [enumerationTail, completedBoundedOutputFinset]

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

@[simp] theorem enumerationTailCount_zero_slack (c : Code) (m : ℕ) :
    enumerationTailCount c m 0 = 0 := by
  simp [enumerationTailCount]

theorem enumerationTailCount_le_omegaCount (c : Code) (m s : ℕ) :
    enumerationTailCount c m s ≤ omegaCount c m := by
  rw [enumerationTailCount_eq_sub]
  exact Nat.sub_le _ _

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

@[simp] theorem enumerationTailLowerM_input
    (c : Code) (m s tailWidth : ℕ) :
    enumerationTailLowerM (enumerationTailLowerInput c m s tailWidth) = m := by
  unfold enumerationTailLowerM enumerationTailLowerInput
  simp only [decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem enumerationTailLowerS_input
    (c : Code) (m s tailWidth : ℕ) :
    enumerationTailLowerS (enumerationTailLowerInput c m s tailWidth) = s := by
  unfold enumerationTailLowerS enumerationTailLowerInput
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem enumerationTailLowerOmegaCode_input
    (c : Code) (m s tailWidth : ℕ) :
    enumerationTailLowerOmegaCode (enumerationTailLowerInput c m s tailWidth) =
      omegaFixedCode c (m - s) := by
  unfold enumerationTailLowerOmegaCode
  rw [enumerationTailLowerM_input, enumerationTailLowerS_input]
  unfold enumerationTailLowerInput
  rw [decodeSecond_pairCode, ← omegaFixedCode_length c (m - s),
    List.take_left]

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

theorem enumerationTailLowerM_primrec : Primrec enumerationTailLowerM := by
  exact bitsToNat_primrec.comp
    (decodeFirst_primrec'.comp decodeFirst_primrec')

theorem enumerationTailLowerS_primrec : Primrec enumerationTailLowerS := by
  exact bitsToNat_primrec.comp
    (decodeSecond_primrec'.comp decodeFirst_primrec')

theorem enumerationTailLowerWidth_primrec :
    Primrec (fun z : BitString =>
      enumerationTailLowerM z - enumerationTailLowerS z + 1) := by
  exact Primrec.nat_add.comp
    (Primrec.nat_sub.comp enumerationTailLowerM_primrec
      enumerationTailLowerS_primrec)
    (Primrec.const 1)

theorem enumerationTailLowerOmegaCode_primrec :
    Primrec enumerationTailLowerOmegaCode := by
  unfold enumerationTailLowerOmegaCode
  exact Primrec.list_take.comp enumerationTailLowerWidth_primrec
    decodeSecond_primrec'

theorem enumerationTailLowerCount_primrec :
    Primrec enumerationTailLowerCount := by
  unfold enumerationTailLowerCount
  exact decodeFixedWidthNatCode_primrec.comp
    (Primrec.list_drop.comp enumerationTailLowerWidth_primrec
      decodeSecond_primrec')

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
  unfold enumerationTailLowerSelector
  exact (Partrec.bind hcompletion hafter).of_eq fun z => rfl

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
    exact (memStringsOfLength (m + 1) x₀).mpr
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
    exact (memStringsOfLength (m + 1) x).mp
      (mem_canonicalFinsetList.mp hxfull)
  have hxmissingStage :
      x ∉ boundedOutputStage c m completeTime := by
    have hpred := List.find?_some hxfind
    simpa using hpred
  have hxmissingCompleted : x ∉ completedBoundedOutput c m := by
    rw [← boundedOutputStage_eq_completed_at_completion c m]
    simpa [completeTime] using hxmissingStage
  have hcompleteSearch :
      completeTime ∈ Nat.rfind (fun t => Part.some
        ((boundedOutputStage c m t).length ==
          ((boundedOutputStage c m lowerTime).length +
            enumerationTailCount c m s))) := by
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
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

theorem enumerationTailCount_lower_bound
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m s : ℕ, s ≤ m →
      logSlack C m ≤ s →
      2 ^ (s - logSlack C m) ≤ enumerationTailCount c m s := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV (enumerationTailLowerSelector c)
      (enumerationTailLowerSelector_partrec c)
  obtain ⟨Clen, hlen⟩ := plainKLeLength V hV
  let C := 6 + Clen + Cmap
  refine ⟨C, fun m s hsm hslack => ?_⟩
  by_contra htail
  push Not at htail
  let tailWidth := s - logSlack C m
  obtain ⟨x, hxSelector, _, hxMissing⟩ :=
    enumerationTailLowerSelector_intended_input c m s tailWidth
  have hxLower : (m : ENat) < plainK V x :=
    plainK_gt_of_not_mem_completed hc hxMissing
  have hinputLength :
      (enumerationTailLowerInput c m s tailWidth).length =
        m - s + tailWidth +
          4 * (Nat.bits m).length + 2 * (Nat.bits s).length + 4 :=
    enumerationTailLowerInput_length htail
  have hbits :
      (Nat.bits s).length ≤ (Nat.bits m).length :=
    length_natBits_mono hsm
  have hbudget :
      6 * (Nat.bits m).length + 4 + Clen + Cmap ≤
        logSlack C m := by
    dsimp [C, logSlack]
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le Clen, Nat.zero_le Cmap]
  have htotal :
      (enumerationTailLowerInput c m s tailWidth).length +
        Clen + Cmap ≤ m := by
    rw [hinputLength]
    dsimp [tailWidth]
    omega
  have hxUpper : plainK V x ≤ (m : ENat) := by
    calc
      plainK V x ≤
          plainK V (enumerationTailLowerInput c m s tailWidth) +
            (Cmap : ENat) :=
        hmap _ _ hxSelector
      _ ≤
          (((enumerationTailLowerInput c m s tailWidth).length : ENat) +
            (Clen : ENat)) + (Cmap : ENat) := by
        gcongr
        exact hlen _
      _ = (((enumerationTailLowerInput c m s tailWidth).length +
          Clen + Cmap : ℕ) : ENat) := by
        push_cast
        ring
      _ ≤ (m : ENat) := by
        exact_mod_cast htotal
  exact (not_lt_of_ge hxUpper) hxLower

/-- A self-delimiting header `(m,s,d)` followed by an undoubled fixed-width
block index.  This is the short description used by the upper-tail block
argument. -/
def enumerationTailUpperInput
    (m s d blockIdx blockWidth : ℕ) : BitString :=
  pairCode
    (pairCode (Nat.bits m) (pairCode (Nat.bits s) (Nat.bits d)))
    (fixedWidthNatCode blockIdx blockWidth)

def enumerationTailUpperM (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeFirst z))

def enumerationTailUpperS (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond (decodeFirst z)))

def enumerationTailUpperD (z : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeSecond (decodeFirst z)))

def enumerationTailUpperBlockIndex (z : BitString) : ℕ :=
  decodeFixedWidthNatCode (decodeSecond z)

@[simp] theorem enumerationTailUpperM_input
    (m s d blockIdx blockWidth : ℕ) :
    enumerationTailUpperM
      (enumerationTailUpperInput m s d blockIdx blockWidth) = m := by
  unfold enumerationTailUpperM enumerationTailUpperInput
  simp only [decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem enumerationTailUpperS_input
    (m s d blockIdx blockWidth : ℕ) :
    enumerationTailUpperS
      (enumerationTailUpperInput m s d blockIdx blockWidth) = s := by
  unfold enumerationTailUpperS enumerationTailUpperInput
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem enumerationTailUpperD_input
    (m s d blockIdx blockWidth : ℕ) :
    enumerationTailUpperD
      (enumerationTailUpperInput m s d blockIdx blockWidth) = d := by
  unfold enumerationTailUpperD enumerationTailUpperInput
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem enumerationTailUpperBlockIndex_input
    (m s d blockIdx blockWidth : ℕ) :
    enumerationTailUpperBlockIndex
      (enumerationTailUpperInput m s d blockIdx blockWidth) = blockIdx := by
  unfold enumerationTailUpperBlockIndex enumerationTailUpperInput
  simp only [decodeSecond_pairCode, decodeFixedWidthNatCode_encode]

theorem enumerationTailUpperInput_length
    {m s d blockIdx blockWidth : ℕ}
    (hblock : blockIdx < 2 ^ blockWidth) :
    (enumerationTailUpperInput m s d blockIdx blockWidth).length =
      blockWidth + 4 * (Nat.bits m).length +
        4 * (Nat.bits s).length + 2 * (Nat.bits d).length + 5 := by
  unfold enumerationTailUpperInput
  rw [length_pairCode, length_pairCode, length_pairCode,
    fixedWidthNatCode_length hblock]
  omega

/-- From `(m,s,d)` and a block index, wait until the bound-`m` enumeration has
reached the end of that block.  The returned natural is enlarged to at least
`m-s`, so `lateCutoff_complexity_implication` can be applied directly. -/
noncomputable def enumerationTailUpperSelector
    (c : Code) (z : BitString) : Part BitString := do
  let blockEnd :=
    enumerationTailUpperBlockIndex z *
      2 ^ (enumerationTailUpperS z + enumerationTailUpperD z)
  let t ← Nat.rfind (fun t => Part.some
    (decide (blockEnd ≤
      (boundedOutputStage c (enumerationTailUpperM z) t).length)))
  Part.some (Nat.bits (max
    (enumerationTailUpperM z - enumerationTailUpperS z) t))

theorem enumerationTailUpperM_primrec : Primrec enumerationTailUpperM := by
  exact bitsToNat_primrec.comp
    (decodeFirst_primrec'.comp decodeFirst_primrec')

theorem enumerationTailUpperS_primrec : Primrec enumerationTailUpperS := by
  exact bitsToNat_primrec.comp
    (decodeFirst_primrec'.comp
      (decodeSecond_primrec'.comp decodeFirst_primrec'))

theorem enumerationTailUpperD_primrec : Primrec enumerationTailUpperD := by
  exact bitsToNat_primrec.comp
    (decodeSecond_primrec'.comp
      (decodeSecond_primrec'.comp decodeFirst_primrec'))

theorem enumerationTailUpperBlockIndex_primrec :
    Primrec enumerationTailUpperBlockIndex := by
  exact decodeFixedWidthNatCode_primrec.comp decodeSecond_primrec'

theorem enumerationTailUpperSelector_partrec
    (c : Code) :
    Partrec (enumerationTailUpperSelector c) := by
  have hm : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperM q.1) :=
    enumerationTailUpperM_primrec.comp Primrec.fst
  have hs : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperS q.1) :=
    enumerationTailUpperS_primrec.comp Primrec.fst
  have hd : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperD q.1) :=
    enumerationTailUpperD_primrec.comp Primrec.fst
  have hpow : Primrec (fun q : BitString × ℕ =>
      2 ^ (enumerationTailUpperS q.1 +
        enumerationTailUpperD q.1)) :=
    Kolmogorov.CodedFiniteDistribution.twoPow_primrec.comp
      (Primrec.nat_add.comp hs hd)
  have hblock : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperBlockIndex q.1) :=
    enumerationTailUpperBlockIndex_primrec.comp Primrec.fst
  have hend : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperBlockIndex q.1 *
        2 ^ (enumerationTailUpperS q.1 +
          enumerationTailUpperD q.1)) :=
    Primrec.nat_mul.comp hblock hpow
  have hstage : Primrec (fun q : BitString × ℕ =>
      boundedOutputStage c (enumerationTailUpperM q.1) q.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair hm Primrec.snd)
  have hcheck : Computable₂ (fun (z : BitString) (t : ℕ) =>
      decide
        (enumerationTailUpperBlockIndex z *
            2 ^ (enumerationTailUpperS z + enumerationTailUpperD z) ≤
          (boundedOutputStage c (enumerationTailUpperM z) t).length)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp hend
        (Primrec.list_length.comp hstage))).to_comp.to₂
  have hsearch : Partrec (fun z : BitString =>
      Nat.rfind (fun t => Part.some
        (decide
          (enumerationTailUpperBlockIndex z *
              2 ^ (enumerationTailUpperS z +
                enumerationTailUpperD z) ≤
            (boundedOutputStage c
              (enumerationTailUpperM z) t).length)))) :=
    Partrec.rfind hcheck.partrec₂
  have hpost : Computable₂ (fun (z : BitString) (t : ℕ) =>
      Nat.bits (max
        (enumerationTailUpperM z - enumerationTailUpperS z) t)) := by
    have hlower : Primrec (fun q : BitString × ℕ =>
        enumerationTailUpperM q.1 - enumerationTailUpperS q.1) :=
      Primrec.nat_sub.comp hm hs
    exact (natBitsComputable.comp
      (Primrec.nat_max.comp hlower Primrec.snd).to_comp).to₂
  unfold enumerationTailUpperSelector
  exact (Partrec.bind hsearch hpost.partrec₂).of_eq (fun _ => rfl)

theorem enumerationTailUpperSelector_intended_input
    (c : Code) (m s d blockIdx blockWidth : ℕ)
    (hbefore :
      (boundedOutputStage c m
        (boundedOutputCompletionTime c (m - s))).length <
          blockIdx * 2 ^ (s + d))
    (hcomplete :
      blockIdx * 2 ^ (s + d) < omegaCount c m) :
    ∃ t,
      Nat.bits (max (m - s) t) ∈
        enumerationTailUpperSelector c
          (enumerationTailUpperInput m s d blockIdx blockWidth) ∧
      boundedOutputCompletionTime c (m - s) < t := by
  let blockEnd := blockIdx * 2 ^ (s + d)
  let hex : ∃ t,
      blockEnd ≤ (boundedOutputStage c m t).length :=
    ⟨boundedOutputCompletionTime c m, by
      rw [show
        (boundedOutputStage c m
          (boundedOutputCompletionTime c m)).length =
            omegaCount c m by
        simpa [omegaCount] using
          boundedOutputCompletionTime_spec c m]
      exact hcomplete.le⟩
  let t := Nat.find hex
  have htSpec :
      blockEnd ≤ (boundedOutputStage c m t).length :=
    Nat.find_spec hex
  have htSearch :
      t ∈ Nat.rfind (fun t => Part.some
        (decide
          (blockEnd ≤ (boundedOutputStage c m t).length))) := by
    refine Nat.mem_rfind.mpr ⟨by simp [htSpec], ?_⟩
    intro n hn
    have hnot := Nat.find_min hex hn
    simp [hnot]
  have hlowerTime :
      boundedOutputCompletionTime c (m - s) < t := by
    by_contra hnot
    push Not at hnot
    have hprefix :=
      boundedOutputStage_prefix_of_le c m hnot
    have hle := hprefix.length_le
    dsimp [blockEnd] at htSpec
    exact (not_lt_of_ge (htSpec.trans hle)) hbefore
  refine ⟨t, ?_, hlowerTime⟩
  unfold enumerationTailUpperSelector
  simp only [enumerationTailUpperM_input,
    enumerationTailUpperS_input, enumerationTailUpperD_input,
    enumerationTailUpperBlockIndex_input]
  change Nat.bits (max (m - s) t) ∈
    (Nat.rfind (fun t => Part.some
      (decide
        (blockIdx * 2 ^ (s + d) ≤
          (boundedOutputStage c m t).length)))).bind
      (fun t => Part.some (Nat.bits (max (m - s) t)))
  rw [Part.mem_bind_iff]
  exact ⟨t, by simpa [blockEnd] using htSearch,
    Part.mem_some (Nat.bits (max (m - s) t))⟩

/-- If more than one `2^(s+d)`-block remains, the first block boundary strictly
after the current stage is still strictly before completion.  Its block index
fits in `m-s-d+2` bits. -/
theorem exists_enumerationTail_full_block
    (c : Code) (m s d : ℕ)
    (htail : 2 ^ (s + d) < enumerationTailCount c m s) :
    ∃ blockIdx,
      (boundedOutputStage c m
          (boundedOutputCompletionTime c (m - s))).length <
        blockIdx * 2 ^ (s + d) ∧
      blockIdx * 2 ^ (s + d) < omegaCount c m ∧
      s + d ≤ m ∧
      blockIdx < 2 ^ (m - s - d + 2) := by
  let a :=
    (boundedOutputStage c m
      (boundedOutputCompletionTime c (m - s))).length
  let q := 2 ^ (s + d)
  let blockIdx := a / q + 1
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hsum : a + enumerationTailCount c m s = omegaCount c m := by
    simpa [a] using stageLength_add_enumerationTailCount c m s
  have hdivle : a / q * q ≤ a := Nat.div_mul_le_self a q
  have hmodlt : a % q < q := Nat.mod_lt a hqpos
  have hdivmod : a / q * q + a % q = a :=
    by simpa [Nat.mul_comm] using Nat.div_add_mod a q
  have habove : a < blockIdx * q := by
    dsimp [blockIdx]
    nlinarith
  have hbelow : blockIdx * q < omegaCount c m := by
    have hblockLe : blockIdx * q ≤ a + q := by
      dsimp [blockIdx]
      nlinarith
    omega
  have hsd : s + d ≤ m := by
    have hpow :
        2 ^ (s + d) < 2 ^ (m + 1) :=
      lt_trans htail
        (lt_of_le_of_lt
          (enumerationTailCount_le_omegaCount c m s)
          (omegaCount_lt_two_pow_succ c m))
    have hexp : s + d < m + 1 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow
    omega
  have haPow : a < 2 ^ (m + 1) := by
    exact lt_trans (lt_trans habove hbelow)
      (omegaCount_lt_two_pow_succ c m)
  have hquot :
      a / q < 2 ^ (m - s - d + 1) := by
    rw [Nat.div_lt_iff_lt_mul hqpos]
    dsimp [q]
    calc
      a < 2 ^ (m + 1) := haPow
      _ = 2 ^ (m - s - d + 1 + (s + d)) := by
        congr 1
        omega
      _ = 2 ^ (m - s - d + 1) * 2 ^ (s + d) := by
        rw [pow_add]
  have hblockWidth :
      blockIdx < 2 ^ (m - s - d + 2) := by
    have hpowpos : 0 < 2 ^ (m - s - d + 1) := by positivity
    have hle : blockIdx ≤ 2 ^ (m - s - d + 1) := by
      dsimp [blockIdx]
      omega
    rw [show m - s - d + 2 = (m - s - d + 1) + 1 by omega,
      pow_succ]
    omega
  exact ⟨blockIdx, by simpa [a, q] using habove,
    by simpa [q] using hbelow, hsd, hblockWidth⟩

/-- The binary length of a logarithmic slack is itself logarithmic.  The
constant's binary length is kept explicit because the upper-tail proof chooses
that constant only after all machine overheads are known. -/
theorem length_natBits_logSlack_le (C m : ℕ) :
    (Nat.bits (logSlack C m)).length ≤
      (Nat.bits m).length + (Nat.bits C).length + 1 := by
  let B := (Nat.bits m).length
  let LC := (Nat.bits C).length
  have hB : B + 1 ≤ 2 ^ (B + 1) := by
    exact Nat.recOn (B + 1) (by norm_num) fun n ihn => by
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n :=
        Nat.one_le_pow n 2 zero_lt_two
      omega
  have hC : C < 2 ^ LC := by
    simpa [LC] using lt_two_pow_length_natBits C
  apply length_natBits_lt_pow
  calc
    logSlack C m = C * (B + 1) := by
      dsimp [B, logSlack]
      ring
    _ < 2 ^ LC * (B + 1) :=
      Nat.mul_lt_mul_of_pos_right hC (Nat.succ_pos B)
    _ ≤ 2 ^ LC * 2 ^ (B + 1) :=
      Nat.mul_le_mul_left _ hB
    _ = 2 ^ (B + LC + 1) := by
      rw [← pow_add]
      congr 1
      omega
    _ = 2 ^ ((Nat.bits m).length + (Nat.bits C).length + 1) := by
      rfl

theorem three_mul_add_twenty_two_le_two_pow_add_ten (K : ℕ) :
    3 * K + 22 ≤ 2 ^ (K + 10) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [show K + 1 + 10 = (K + 10) + 1 by omega, pow_succ]
      omega

theorem enumerationTailCount_upper_bound
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m s : ℕ, s ≤ m →
      enumerationTailCount c m s ≤ 2 ^ (s + logSlack C m) := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV (enumerationTailUpperSelector c)
      (enumerationTailUpperSelector_partrec c)
  obtain ⟨Clen, hlen⟩ := plainKLeLength V hV
  obtain ⟨Ccut, hcut⟩ :=
    lateCutoff_complexity_implication V hV c hc
  let K := 9 + Clen + Cmap + Ccut
  let C := 2 ^ (K + 10)
  refine ⟨C, fun m s hsm => ?_⟩
  by_contra htail
  push Not at htail
  let d := logSlack C m
  obtain ⟨blockIdx, hbefore, hcomplete, hsd, hblock⟩ :=
    exists_enumerationTail_full_block c m s d (by
      simpa [d] using htail)
  let blockWidth := m - s - d + 2
  obtain ⟨t, htSelector, hlowerTime⟩ :=
    enumerationTailUpperSelector_intended_input
      c m s d blockIdx blockWidth hbefore hcomplete
  let N := max (m - s) t
  have hqN : m - s ≤ N := by
    exact le_max_left _ _
  have hdone :
      boundedOutputCompletionTime c (m - s) ≤ N := by
    exact le_trans hlowerTime.le (le_max_right _ _)
  have hlate :
      ((m - s : ℕ) : ENat) <
        plainKNat V N + (Ccut : ENat) :=
    hcut (m - s) N hqN hdone
  have hselector :
      plainKNat V N ≤
        plainK V
          (enumerationTailUpperInput
            m s d blockIdx blockWidth) + (Cmap : ENat) := by
    exact hmap _ _ (by simpa [N] using htSelector)
  have hinputLength :
      (enumerationTailUpperInput
        m s d blockIdx blockWidth).length =
          blockWidth + 4 * (Nat.bits m).length +
            4 * (Nat.bits s).length +
              2 * (Nat.bits d).length + 5 :=
    enumerationTailUpperInput_length (by
      simpa [blockWidth] using hblock)
  have hbitsS :
      (Nat.bits s).length ≤ (Nat.bits m).length :=
    length_natBits_mono hsm
  have hbitsD :
      (Nat.bits d).length ≤
        (Nat.bits m).length + (Nat.bits C).length + 1 := by
    simpa [d] using length_natBits_logSlack_le C m
  have hCbits :
      (Nat.bits C).length ≤ K + 11 := by
    apply length_natBits_lt_pow
    dsimp [C]
    exact (Nat.pow_lt_pow_iff_right
      (by norm_num : 1 < 2)).mpr (by omega)
  have hCten : 10 ≤ C := by
    dsimp [C]
    exact le_trans (by norm_num : 10 ≤ 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 10 K))
  have hCconst :
      2 * (Nat.bits C).length + K ≤ C := by
    calc
      2 * (Nat.bits C).length + K ≤ 3 * K + 22 := by
        omega
      _ ≤ 2 ^ (K + 10) :=
        three_mul_add_twenty_two_le_two_pow_add_ten K
      _ = C := rfl
  have hbudget :
      10 * (Nat.bits m).length +
          2 * (Nat.bits C).length + K ≤ d := by
    dsimp [d, logSlack]
    have hmul :
        10 * (Nat.bits m).length ≤
          C * (Nat.bits m).length :=
      Nat.mul_le_mul_right _ hCten
    omega
  have htotal :
      (enumerationTailUpperInput
          m s d blockIdx blockWidth).length +
        Clen + Cmap + Ccut ≤ m - s := by
    rw [hinputLength]
    dsimp [blockWidth, K] at *
    omega
  have hupper :
      plainKNat V N + (Ccut : ENat) ≤
        ((m - s : ℕ) : ENat) := by
    calc
      plainKNat V N + (Ccut : ENat) ≤
          (plainK V
            (enumerationTailUpperInput
              m s d blockIdx blockWidth) +
                (Cmap : ENat)) + (Ccut : ENat) := by
        gcongr
      _ ≤
          ((((enumerationTailUpperInput
              m s d blockIdx blockWidth).length : ENat) +
                (Clen : ENat)) + (Cmap : ENat)) +
                  (Ccut : ENat) := by
        gcongr
        exact hlen _
      _ = (((enumerationTailUpperInput
          m s d blockIdx blockWidth).length +
            Clen + Cmap + Ccut : ℕ) : ENat) := by
        push_cast
        ring
      _ ≤ ((m - s : ℕ) : ENat) := by
        exact_mod_cast htotal
  exact (not_lt_of_ge hupper) hlate

theorem prop_enumeration_tail
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m s : ℕ, s ≤ m →
      (logSlack C m ≤ s → 2 ^ (s - logSlack C m) ≤ enumerationTailCount c m s) ∧
      enumerationTailCount c m s ≤ 2 ^ (s + logSlack C m) := by
  obtain ⟨Clower, hlower⟩ := enumerationTailCount_lower_bound V hV c hc
  obtain ⟨Cupper, hupper⟩ := enumerationTailCount_upper_bound V hV c hc
  let C := max Clower Cupper
  refine ⟨C, fun m s hsm => ⟨fun hslack => ?_, ?_⟩⟩
  · have hC_lower : logSlack Clower m ≤ logSlack C m := by
      dsimp [logSlack, C]
      have h1 : Clower ≤ max Clower Cupper := le_max_left _ _
      have h2 :
          Clower * (Nat.bits m).length ≤
            max Clower Cupper * (Nat.bits m).length :=
        Nat.mul_le_mul_right _ h1
      omega
    have hslack_lower : logSlack Clower m ≤ s :=
      le_trans hC_lower hslack
    have h_pow := hlower m s hsm hslack_lower
    have h_sub : s - logSlack C m ≤ s - logSlack Clower m := by
      omega
    exact (Nat.pow_le_pow_right (by decide) h_sub).trans h_pow
  · have hC_upper : logSlack Cupper m ≤ logSlack C m := by
      dsimp [logSlack, C]
      have h1 : Cupper ≤ max Clower Cupper := le_max_right _ _
      have h2 :
          Cupper * (Nat.bits m).length ≤
            max Clower Cupper * (Nat.bits m).length :=
        Nat.mul_le_mul_right _ h1
      omega
    have h_pow := hupper m s hsm
    have h_add : s + logSlack Cupper m ≤ s + logSlack C m := by
      omega
    exact h_pow.trans (Nat.pow_le_pow_right (by decide) h_add)

end Kolmogorov
