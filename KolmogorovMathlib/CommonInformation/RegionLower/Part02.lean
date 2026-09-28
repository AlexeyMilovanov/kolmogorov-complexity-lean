import KolmogorovMathlib.CommonInformation.RegionEnvelopes
import KolmogorovMathlib.CommonInformation.OverlapExtraction
import KolmogorovMathlib.CommonInformation.RegionLower.Part01

/-!
# The upper extremizer of the lower envelope

`common_information_upper_envelope_achieved` is the remaining extremal direction of SUV
Theorem 225: overlapping lengths realize the top of the envelope.  The witness pair comes from
`exists_incompressibleOverlapPairProfile`, which splits one incompressible `3n`-bit string
into three blocks and takes the two overlapping factors — their complexities are pinned by
`plainK_left_shared_lower_bound`, `plainK_shared_right_lower_bound`,
`pairPlainK_overlap_upper_bound` and `pairPlainK_overlap_lower_bound`.

The witnesses for the material-bit families are built with `insertVisibleContext`, which
inserts a middle block into a coded context, and the completion coding
(`overlapMaterialCompletionCode_length_le`, `recoverRightOverlapFactor_computable`,
`condK_overlapFactors_given_materialPrefixes_le`), giving
`commonInformationRegion_contains_overlapMaterialProfiles`.  The other directions are in
`RegionLower/Part01`.
-/

namespace Kolmogorov

/-- Uniform bound on `logSlack c (3 * n + 1)` when `c ≤ cWitness`, `hFold` folds `cWitness`,
and `cFold ≤ C`. -/
private lemma logSlack_three_block_bound {c cWitness cFold C n : Nat}
    (hc : c ≤ cWitness)
    (hFold : logSlack cWitness (3 * n + 1) ≤ logSlack cFold n)
    (hcFold : cFold ≤ C) :
    logSlack c (n + n + n + 1) ≤ logSlack C n := by
  calc
    logSlack c (n + n + n + 1) ≤ logSlack cWitness (3 * n + 1) := by
      have h := logSlack_mono_left hc (3 * n + 1)
      simpa [show n + n + n + 1 = 3 * n + 1 by omega] using h
    _ ≤ logSlack cFold n := hFold
    _ ≤ logSlack C n := logSlack_mono_left hcFold n

/-- Complexity upper bound for a pair of `n`-bit blocks from string length and length bound. -/
private lemma plainK_twoBlock_le_of_length {V : Map} {cLen C n kx : Nat}
    {left shared : BitString}
    (hLen : plainK V (left ++ shared) ≤ ((left ++ shared).length : ENat) + (cLen : ENat))
    (hx : HasPlainComplexityValue V (left ++ shared) kx)
    (hLeft : left.length = n) (hShared : shared.length = n)
    (hcLen : cLen ≤ logSlack C n) :
    kx ≤ 2 * n + logSlack C n := by
  have h := hLen
  rw [hx] at h
  have hNat : kx ≤ (left ++ shared).length + cLen := by exact_mod_cast h
  simp only [List.length_append, hLeft, hShared] at hNat
  omega

/-- Lower bound on plain complexity of the first overlapping factor from three-block
reconstruction. -/
private lemma plainK_left_shared_lower_bound {V : Map} {cThree C n kx : Nat}
    {left shared right u : BitString}
    (huIncompressible : (3 * n : ENat) ≤ plainK V u)
    (hFactor : left ++ shared ++ right = u)
    (hx : HasPlainComplexityValue V (left ++ shared) kx)
    (hThree : plainK V (([] : BitString) ++ (left ++ shared) ++ right) ≤
      plainK V (left ++ shared) +
        ((([] : BitString).length + right.length +
          logSlack cThree ((([] : BitString) ++ (left ++ shared) ++ right).length + 1) : Nat) :
            ENat))
    (hRight : right.length = n)
    (hSlack : logSlack cThree (left.length + shared.length + right.length + 1) ≤ logSlack C n) :
    2 * n ≤ kx + logSlack C n := by
  have hReconstruct := hThree
  simp only [List.nil_append, List.length_nil, Nat.zero_add, List.length_append] at hReconstruct
  rw [hFactor, hx] at hReconstruct
  have hE := huIncompressible.trans hReconstruct
  have hNat : 3 * n ≤ kx + (right.length +
      logSlack cThree (left.length + shared.length + right.length + 1)) := by
    exact_mod_cast hE
  omega

/-- Lower bound on plain complexity of the second overlapping factor from three-block
reconstruction. -/
private lemma plainK_shared_right_lower_bound {V : Map} {cThree C n ky : Nat}
    {left shared right u : BitString}
    (huIncompressible : (3 * n : ENat) ≤ plainK V u)
    (hFactor : left ++ shared ++ right = u)
    (hy : HasPlainComplexityValue V (shared ++ right) ky)
    (hThree : plainK V (left ++ (shared ++ right) ++ ([] : BitString)) ≤
      plainK V (shared ++ right) +
        ((left.length + ([] : BitString).length +
          logSlack cThree ((left ++ (shared ++ right) ++ ([] : BitString)).length + 1) : Nat) :
            ENat))
    (hLeft : left.length = n)
    (hSlack : logSlack cThree (left.length + shared.length + right.length + 1) ≤ logSlack C n) :
    2 * n ≤ ky + logSlack C n := by
  have hReconstruct := hThree
  simp only [List.append_nil, List.length_nil, Nat.add_zero, List.length_append] at hReconstruct
  have hFactor' : left ++ (shared ++ right) = u := by simpa [List.append_assoc] using hFactor
  rw [hFactor', hy] at hReconstruct
  have hE := huIncompressible.trans hReconstruct
  have hNat : 3 * n ≤ ky + (left.length +
      logSlack cThree (left.length + (shared.length + right.length) + 1)) := by
    exact_mod_cast hE
  have hSlack' : logSlack cThree (left.length + (shared.length + right.length) + 1) ≤
      logSlack C n := by
    simpa [Nat.add_assoc] using hSlack
  omega

/-- Upper bound on pair complexity of overlapping factors from
`pairPlainK_overlapFactors_le_length`. -/
private lemma pairPlainK_overlap_upper_bound {V : Map} {cPairUpper C n kxy : Nat}
    {left shared right : BitString}
    (hPairUpper : pairPlainK V (left ++ shared) (shared ++ right) ≤
      (left.length + shared.length + right.length : ENat) +
        (logSlack cPairUpper (left.length + shared.length + right.length + 1) : ENat))
    (hxy : HasPlainComplexityValue V (pairCode (left ++ shared) (shared ++ right)) kxy)
    (hLeft : left.length = n) (hShared : shared.length = n) (hRight : right.length = n)
    (hSlack : logSlack cPairUpper (left.length + shared.length + right.length + 1) ≤ logSlack C n) :
    kxy ≤ 3 * n + logSlack C n := by
  rw [pairPlainK, hxy] at hPairUpper
  have hNat : kxy ≤ left.length + shared.length + right.length +
      logSlack cPairUpper (left.length + shared.length + right.length + 1) := by
    exact_mod_cast hPairUpper
  omega

/-- Lower bound on pair complexity of overlapping factors for an incompressible string. -/
private lemma pairPlainK_overlap_lower_bound {V : Map} {cPairLower C n kxy : Nat}
    {left shared right u : BitString}
    (huIncompressible : (3 * n : ENat) ≤ plainK V u)
    (hFactor : left ++ shared ++ right = u)
    (hPairLower : plainK V (left ++ shared ++ right) ≤
      pairPlainK V (left ++ shared) (shared ++ right) +
        (logSlack cPairLower (left.length + shared.length + right.length + 1) : ENat))
    (hxy : HasPlainComplexityValue V (pairCode (left ++ shared) (shared ++ right)) kxy)
    (hSlack : logSlack cPairLower (left.length + shared.length + right.length + 1) ≤ logSlack C n) :
    3 * n ≤ kxy + logSlack C n := by
  have h := hPairLower
  rw [hFactor, pairPlainK, hxy] at h
  have hE : (3 * n : ENat) ≤ (kxy : ENat) +
      (logSlack cPairLower (left.length + shared.length + right.length + 1) : ENat) :=
    huIncompressible.trans h
  have hNat : 3 * n ≤ kxy +
      logSlack cPairLower (left.length + shared.length + right.length + 1) := by
    exact_mod_cast hE
  omega

/-- Profile-construction leaf for the upper extremizer.  Split one
incompressible `3n`-bit string into three `n`-bit blocks; the left-plus-middle
and middle-plus-right factors have the required exact finite complexity
profile up to one uniform logarithmic error. -/
theorem exists_incompressibleOverlapPairProfile
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ n : Nat,
      ∃ left shared right : BitString, ∃ kx ky kxy : Nat,
        left.length = n ∧ shared.length = n ∧ right.length = n ∧
        HasPlainComplexityValue V (left ++ shared) kx ∧
        HasPlainComplexityValue V (shared ++ right) ky ∧
        HasPlainComplexityValue V
          (pairCode (left ++ shared) (shared ++ right)) kxy ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) := by
  obtain ⟨cLen, hLen⟩ := plainK_le_length V hV
  obtain ⟨cThree, hThree⟩ := plainK_threeBlock_le V hV
  obtain ⟨cPairUpper, hPairUpper⟩ :=
    pairPlainK_overlapFactors_le_length V hV
  obtain ⟨cPairLower, hPairLower⟩ :=
    plainK_threeBlocks_le_overlapPair V hV
  let cWitness := cThree + cPairUpper + cPairLower
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cWitness 3 1
  let C := cLen + cFold
  refine ⟨C, fun n => ?_⟩
  obtain ⟨u, huLength, huIncompressible⟩ :=
    exists_incompressible_string V [] (3 * n)
  let left := u.take n
  let rest := u.drop n
  let shared := rest.take n
  let right := rest.drop n
  have hLeftLength : left.length = n := by
    dsimp [left]
    rw [List.length_take, huLength]
    omega
  have hRestLength : rest.length = 2 * n := by
    dsimp [rest]
    rw [List.length_drop, huLength]
    omega
  have hSharedLength : shared.length = n := by
    dsimp [shared]
    rw [List.length_take, hRestLength]
    omega
  have hRightLength : right.length = n := by
    dsimp [right]
    rw [List.length_drop, hRestLength]
    omega
  have hFactor : left ++ shared ++ right = u := by
    rw [List.append_assoc]
    change u.take n ++ ((u.drop n).take n ++ (u.drop n).drop n) = u
    rw [List.take_append_drop, List.take_append_drop]
  obtain ⟨kx, hx⟩ :=
    exists_plainComplexityValue V hV (left ++ shared)
  obtain ⟨ky, hy⟩ :=
    exists_plainComplexityValue V hV (shared ++ right)
  obtain ⟨kxy, hxy⟩ :=
    exists_plainComplexityValue V hV
      (pairCode (left ++ shared) (shared ++ right))
  have hcThree : cThree ≤ cWitness := by dsimp [cWitness]; omega
  have hcPairUpper : cPairUpper ≤ cWitness := by dsimp [cWitness]; omega
  have hcPairLower : cPairLower ≤ cWitness := by dsimp [cWitness]; omega
  have hcFold : cFold ≤ C := by dsimp [C]; omega
  have hThreeSlack : logSlack cThree (left.length + shared.length + right.length + 1) ≤
      logSlack C n := by
    rw [hLeftLength, hSharedLength, hRightLength]
    exact logSlack_three_block_bound hcThree (hFold n) hcFold
  have hPairUpperSlack : logSlack cPairUpper (left.length + shared.length + right.length + 1) ≤
      logSlack C n := by
    rw [hLeftLength, hSharedLength, hRightLength]
    exact logSlack_three_block_bound hcPairUpper (hFold n) hcFold
  have hPairLowerSlack : logSlack cPairLower (left.length + shared.length + right.length + 1) ≤
      logSlack C n := by
    rw [hLeftLength, hSharedLength, hRightLength]
    exact logSlack_three_block_bound hcPairLower (hFold n) hcFold
  have hLenSlack : cLen ≤ logSlack C n := by
    dsimp [C]; unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits n).length]
  have hxUpper : kx ≤ 2 * n + logSlack C n :=
    plainK_twoBlock_le_of_length (hLen _) hx hLeftLength hSharedLength hLenSlack
  have hyUpper : ky ≤ 2 * n + logSlack C n :=
    plainK_twoBlock_le_of_length (hLen _) hy hSharedLength hRightLength hLenSlack
  have hxLower : 2 * n ≤ kx + logSlack C n :=
    plainK_left_shared_lower_bound huIncompressible hFactor hx
      (hThree [] (left ++ shared) right) hRightLength hThreeSlack
  have hyLower : 2 * n ≤ ky + logSlack C n :=
    plainK_shared_right_lower_bound huIncompressible hFactor hy
      (hThree left (shared ++ right) []) hLeftLength hThreeSlack
  have hxyUpper : kxy ≤ 3 * n + logSlack C n :=
    pairPlainK_overlap_upper_bound (hPairUpper left shared right) hxy
      hLeftLength hSharedLength hRightLength hPairUpperSlack
  have hxyLower : 3 * n ≤ kxy + logSlack C n :=
    pairPlainK_overlap_lower_bound huIncompressible hFactor
      (hPairLower left shared right) hxy hPairLowerSlack
  exact ⟨left, shared, right, kx, ky, kxy,
    hLeftLength, hSharedLength, hRightLength, hx, hy, hxy,
    ⟨hxUpper, hxLower⟩, ⟨hyUpper, hyLower⟩,
    ⟨hxyUpper, hxyLower⟩⟩

/-- Code for inserting the visible condition between two literal blocks. -/
def insertVisibleContextCode (before after : BitString) : BitString :=
  pairCode (Nat.bits before.length) (before ++ after)

/-- Inserting a middle block between the two blocks coded by the context. -/
def insertVisibleContext (p context : BitString) : BitString :=
  let beforeLength := decodeBits (decodeFirst p)
  let body := decodeSecond p
  body.take beforeLength ++ context ++ body.drop beforeLength

/-- Inserting a block into a coded context is computable. -/
theorem insertVisibleContext_computable :
    Computable (fun p : BitString × BitString =>
      insertVisibleContext p.1 p.2) := by
  have hLength : Computable (fun p : BitString × BitString =>
      decodeBits (decodeFirst p.1)) :=
    (decodeBits_computable.comp decodeFirst_computable).comp Computable.fst
  have hBody : Computable (fun p : BitString × BitString =>
      decodeSecond p.1) := decodeSecond_computable.comp Computable.fst
  have hBefore := Primrec.list_take.to_comp.comp hBody hLength
  have hAfter := Primrec.list_drop.to_comp.comp hBody hLength
  exact Computable.list_append.comp
    (Computable.list_append.comp hBefore Computable.snd) hAfter

/-- Inserting `middle` into the context coding `before` and `after` returns the
concatenation. -/
@[simp] theorem insertVisibleContext_spec
    (before middle after : BitString) :
    insertVisibleContext (insertVisibleContextCode before after) middle =
      before ++ middle ++ after := by
  simp only [insertVisibleContext, insertVisibleContextCode,
    decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
  rw [List.take_left, List.drop_left]

/-- The context code costs only a logarithmic overhead over the lengths of the two blocks. -/
theorem insertVisibleContextCode_length_le
    (before middle after : BitString) :
    (insertVisibleContextCode before after).length ≤
      before.length + after.length +
        logSlack 3 (before.length + middle.length + after.length + 1) := by
  have hBits :
      (Nat.bits before.length).length ≤
        (Nat.bits (before.length + middle.length + after.length + 1)).length :=
    length_natBits_mono (by omega)
  simp only [insertVisibleContextCode, length_pairCode, List.length_append]
  unfold logSlack
  nlinarith [Nat.zero_le
    (Nat.bits (before.length + middle.length + after.length + 1)).length]

/-- Literal blocks around a visible condition cost exactly their total length,
plus logarithmic metadata for the insertion point. -/
theorem condK_insert_visible_context_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ before middle after : BitString,
      condK V (before ++ middle ++ after) middle ≤
        ((before.length + after.length +
          logSlack c (before.length + middle.length + after.length + 1) : Nat) : ENat) := by
  let D : Map := fun pr => Part.some (insertVisibleContext pr.1 pr.2)
  have hD : isDecompressor D :=
    Computable.partrec insertVisibleContext_computable
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  let C := 3 + cD
  refine ⟨C, fun before middle after => ?_⟩
  let prog := insertVisibleContextCode before after
  have hProd : produces D prog middle (before ++ middle ++ after) := by
    change before ++ middle ++ after ∈
      Part.some (insertVisibleContext prog middle)
    rw [show insertVisibleContext prog middle = before ++ middle ++ after by
      exact insertVisibleContext_spec before middle after]
    exact Part.mem_some _
  have hBound : condK V (before ++ middle ++ after) middle ≤
      (prog.length : ENat) + (cD : ENat) := by
    calc
      condK V (before ++ middle ++ after) middle ≤
          condK D (before ++ middle ++ after) middle + (cD : ENat) :=
        hcD _ _
      _ ≤ (prog.length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hProd, rfl⟩
  have hLength := insertVisibleContextCode_length_le before middle after
  have hSlack := logSlack_add_nat_le 3 cD
    (before.length + middle.length + after.length + 1)
  exact hBound.trans (by
    rw [← Nat.cast_add]
    exact_mod_cast (Nat.add_le_add_right hLength cD |>.trans (by
      dsimp [C]
      omega)))

/-- The completion code carrying the shared and left-prefix lengths together with the payload. -/
def overlapMaterialCompletionCode
    (sharedLength leftPrefixLength : Nat) (payload : BitString) : BitString :=
  pairCode (Nat.bits sharedLength)
    (pairCode (Nat.bits leftPrefixLength) payload)

/-- The shared block length read off from a completion code. -/
def overlapMaterialSharedLength (p : BitString) : Nat :=
  decodeBits (decodeFirst p)

/-- The left prefix length read off from a completion code. -/
def overlapMaterialLeftPrefixLength (p : BitString) : Nat :=
  decodeBits (decodeFirst (decodeSecond p))

/-- The payload read off from a completion code. -/
def overlapMaterialPayload (p : BitString) : BitString :=
  decodeSecond (decodeSecond p)

/-- The left overlapping factor recovered from a completion code and a context. -/
def recoverLeftOverlapFactor (p context : BitString) : BitString :=
  (context.drop (overlapMaterialSharedLength p)).take
      (overlapMaterialLeftPrefixLength p) ++
    overlapMaterialPayload p ++
    context.take (overlapMaterialSharedLength p)

/-- The right overlapping factor recovered from a completion code and a context. -/
def recoverRightOverlapFactor (p context : BitString) : BitString :=
  context.take (overlapMaterialSharedLength p) ++
    context.drop
      (overlapMaterialSharedLength p +
        overlapMaterialLeftPrefixLength p) ++
    overlapMaterialPayload p

/-- The shared length of a completion code is computable. -/
theorem overlapMaterialSharedLength_computable :
    Computable overlapMaterialSharedLength :=
  decodeBits_computable.comp decodeFirst_computable

/-- The left prefix length of a completion code is computable. -/
theorem overlapMaterialLeftPrefixLength_computable :
    Computable overlapMaterialLeftPrefixLength :=
  decodeBits_computable.comp
    (decodeFirst_computable.comp decodeSecond_computable)

/-- The payload of a completion code is computable. -/
theorem overlapMaterialPayload_computable :
    Computable overlapMaterialPayload :=
  decodeSecond_computable.comp decodeSecond_computable

/-- Recovering the left overlapping factor is computable. -/
theorem recoverLeftOverlapFactor_computable :
    Computable (fun p : BitString × BitString =>
      recoverLeftOverlapFactor p.1 p.2) := by
  have hShared : Computable (fun p : BitString × BitString =>
      overlapMaterialSharedLength p.1) :=
    overlapMaterialSharedLength_computable.comp Computable.fst
  have hLeft : Computable (fun p : BitString × BitString =>
      overlapMaterialLeftPrefixLength p.1) :=
    overlapMaterialLeftPrefixLength_computable.comp Computable.fst
  have hPayload : Computable (fun p : BitString × BitString =>
      overlapMaterialPayload p.1) :=
    overlapMaterialPayload_computable.comp Computable.fst
  have hDrop : Computable (fun p : BitString × BitString =>
      p.2.drop (overlapMaterialSharedLength p.1)) :=
    Primrec.list_drop.to_comp.comp Computable.snd hShared
  have hPrefix : Computable (fun p : BitString × BitString =>
      (p.2.drop (overlapMaterialSharedLength p.1)).take
        (overlapMaterialLeftPrefixLength p.1)) :=
    Primrec.list_take.to_comp.comp hDrop hLeft
  have hSharedPrefix : Computable (fun p : BitString × BitString =>
      p.2.take (overlapMaterialSharedLength p.1)) :=
    Primrec.list_take.to_comp.comp Computable.snd hShared
  exact Computable.list_append.comp
    (Computable.list_append.comp hPrefix hPayload) hSharedPrefix

/-- Recovering the right overlapping factor is computable. -/
theorem recoverRightOverlapFactor_computable :
    Computable (fun p : BitString × BitString =>
      recoverRightOverlapFactor p.1 p.2) := by
  have hShared : Computable (fun p : BitString × BitString =>
      overlapMaterialSharedLength p.1) :=
    overlapMaterialSharedLength_computable.comp Computable.fst
  have hLeft : Computable (fun p : BitString × BitString =>
      overlapMaterialLeftPrefixLength p.1) :=
    overlapMaterialLeftPrefixLength_computable.comp Computable.fst
  have hPayload : Computable (fun p : BitString × BitString =>
      overlapMaterialPayload p.1) :=
    overlapMaterialPayload_computable.comp Computable.fst
  have hSum : Computable (fun p : BitString × BitString =>
      overlapMaterialSharedLength p.1 +
        overlapMaterialLeftPrefixLength p.1) :=
    Primrec.nat_add.to_comp.comp hShared hLeft
  have hSharedPrefix : Computable (fun p : BitString × BitString =>
      p.2.take (overlapMaterialSharedLength p.1)) :=
    Primrec.list_take.to_comp.comp Computable.snd hShared
  have hRightPrefix : Computable (fun p : BitString × BitString =>
      p.2.drop (overlapMaterialSharedLength p.1 +
        overlapMaterialLeftPrefixLength p.1)) :=
    Primrec.list_drop.to_comp.comp Computable.snd hSum
  exact Computable.list_append.comp
    (Computable.list_append.comp hSharedPrefix hRightPrefix) hPayload

/-- The completion code costs only a logarithmic overhead over the payload length. -/
theorem overlapMaterialCompletionCode_length_le
    (sharedLength leftPrefixLength : Nat) (payload : BitString) (N : Nat)
    (hShared : sharedLength ≤ N) (hLeft : leftPrefixLength ≤ N) :
    (overlapMaterialCompletionCode
        sharedLength leftPrefixLength payload).length ≤
      payload.length + logSlack 6 (N + 1) := by
  have hBitsShared :
      (Nat.bits sharedLength).length ≤ (Nat.bits (N + 1)).length :=
    length_natBits_mono (by omega)
  have hBitsLeft :
      (Nat.bits leftPrefixLength).length ≤ (Nat.bits (N + 1)).length :=
    length_natBits_mono (by omega)
  simp only [overlapMaterialCompletionCode, length_pairCode]
  unfold logSlack
  nlinarith [Nat.zero_le (Nat.bits (N + 1)).length]

/-- Completing the private prefixes stored beside the entire shared block
recovers both overlapping factors with the exact missing-private-bit costs. -/
theorem condK_overlapFactors_given_materialPrefixes_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ left shared right : BitString, ∀ i j : Nat,
      i ≤ left.length → j ≤ right.length →
      let z := shared ++ left.take i ++ right.take j
      condK V (left ++ shared) z ≤
          ((left.length - i +
            logSlack c (left.length + shared.length + right.length + 1) : Nat) : ENat) ∧
        condK V (shared ++ right) z ≤
          ((right.length - j +
            logSlack c (left.length + shared.length + right.length + 1) : Nat) : ENat) := by
  let Dx : Map := fun pr => Part.some (recoverLeftOverlapFactor pr.1 pr.2)
  let Dy : Map := fun pr => Part.some (recoverRightOverlapFactor pr.1 pr.2)
  have hDx : isDecompressor Dx :=
    Computable.partrec recoverLeftOverlapFactor_computable
  have hDy : isDecompressor Dy :=
    Computable.partrec recoverRightOverlapFactor_computable
  obtain ⟨cx, hcx⟩ := hV.2 Dx hDx
  obtain ⟨cy, hcy⟩ := hV.2 Dy hDy
  let C := 6 + cx + cy
  refine ⟨C, ?_⟩
  intro left shared right i j hi hj
  let z := shared ++ left.take i ++ right.take j
  let N := left.length + shared.length + right.length
  let px := overlapMaterialCompletionCode shared.length i (left.drop i)
  let py := overlapMaterialCompletionCode shared.length i (right.drop j)
  have hLeftTake : (left.take i).length = i := by
    rw [List.length_take]
    omega
  have hRightTake : (right.take j).length = j := by
    rw [List.length_take]
    omega
  have hRecoverX : recoverLeftOverlapFactor px z = left ++ shared := by
    have hDrop : z.drop shared.length = left.take i ++ right.take j := by
      dsimp [z]
      rw [show shared ++ left.take i ++ right.take j =
          shared ++ (left.take i ++ right.take j) by simp,
        List.drop_left]
    have hPrefix : (z.drop shared.length).take i = left.take i := by
      rw [hDrop, List.take_append_of_le_length (by omega),
        List.take_take, Nat.min_self]
    have hSharedPrefix : z.take shared.length = shared := by
      dsimp [z]
      rw [show shared ++ left.take i ++ right.take j =
          shared ++ (left.take i ++ right.take j) by simp,
        List.take_left]
    simp only [recoverLeftOverlapFactor, px,
      overlapMaterialCompletionCode, overlapMaterialSharedLength,
      overlapMaterialLeftPrefixLength, overlapMaterialPayload,
      decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
    rw [hPrefix, hSharedPrefix, List.take_append_drop]
  have hRecoverY : recoverRightOverlapFactor py z = shared ++ right := by
    have hSharedPrefix : z.take shared.length = shared := by
      dsimp [z]
      rw [show shared ++ left.take i ++ right.take j =
          shared ++ (left.take i ++ right.take j) by simp,
        List.take_left]
    have hRightPrefix : z.drop (shared.length + i) = right.take j := by
      dsimp [z]
      rw [← List.drop_drop, show shared ++ left.take i ++ right.take j =
          shared ++ (left.take i ++ right.take j) by simp,
        List.drop_left,
        List.drop_append_of_le_length hLeftTake.symm.le,
        List.drop_eq_nil_of_le hLeftTake.le, List.nil_append]
    simp only [recoverRightOverlapFactor, py,
      overlapMaterialCompletionCode, overlapMaterialSharedLength,
      overlapMaterialLeftPrefixLength, overlapMaterialPayload,
      decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
    rw [hSharedPrefix, hRightPrefix]
    calc
      shared ++ right.take j ++ right.drop j =
          shared ++ (right.take j ++ right.drop j) := by simp
      _ = shared ++ right := by rw [List.take_append_drop]
  have hProdX : produces Dx px z (left ++ shared) := by
    change left ++ shared ∈ Part.some (recoverLeftOverlapFactor px z)
    rw [hRecoverX]
    exact Part.mem_some _
  have hProdY : produces Dy py z (shared ++ right) := by
    change shared ++ right ∈ Part.some (recoverRightOverlapFactor py z)
    rw [hRecoverY]
    exact Part.mem_some _
  have hBoundX : condK V (left ++ shared) z ≤
      (px.length : ENat) + (cx : ENat) := by
    calc
      condK V (left ++ shared) z ≤ condK Dx (left ++ shared) z + (cx : ENat) :=
        hcx _ _
      _ ≤ (px.length : ENat) + (cx : ENat) := by
        gcongr
        exact sInf_le ⟨px, hProdX, rfl⟩
  have hBoundY : condK V (shared ++ right) z ≤
      (py.length : ENat) + (cy : ENat) := by
    calc
      condK V (shared ++ right) z ≤ condK Dy (shared ++ right) z + (cy : ENat) :=
        hcy _ _
      _ ≤ (py.length : ENat) + (cy : ENat) := by
        gcongr
        exact sInf_le ⟨py, hProdY, rfl⟩
  have hSharedN : shared.length ≤ N := by dsimp [N]; omega
  have hiN : i ≤ N := by dsimp [N]; omega
  have hPxLength := overlapMaterialCompletionCode_length_le
    shared.length i (left.drop i) N hSharedN hiN
  have hPyLength := overlapMaterialCompletionCode_length_le
    shared.length i (right.drop j) N hSharedN hiN
  have hSlackX := logSlack_add_nat_le 6 cx (N + 1)
  have hSlackY := logSlack_add_nat_le (6 + cx) cy (N + 1)
  have hFinalSlackX :
      logSlack 6 (N + 1) + cx ≤ logSlack C (N + 1) := by
    exact hSlackX.trans
      (logSlack_mono_left (by dsimp [C]; omega) (N + 1))
  have hFinalSlackY :
      logSlack 6 (N + 1) + cy ≤ logSlack C (N + 1) := by
    calc
      logSlack 6 (N + 1) + cy ≤
          logSlack (6 + cx) (N + 1) + cy :=
        Nat.add_le_add_right
          (logSlack_mono_left (by omega) (N + 1)) cy
      _ ≤ logSlack C (N + 1) := by
        simpa [C] using hSlackY
  have hNatX :
      px.length + cx ≤ left.length - i +
        logSlack C (left.length + shared.length + right.length + 1) := by
    have hL : px.length ≤ left.length - i +
        logSlack 6 (left.length + shared.length + right.length + 1) := by
      simpa [px, N, List.length_drop] using hPxLength
    have hS :
        logSlack 6 (left.length + shared.length + right.length + 1) + cx ≤
          logSlack C (left.length + shared.length + right.length + 1) := by
      simpa [N] using hFinalSlackX
    omega
  have hNatY :
      py.length + cy ≤ right.length - j +
        logSlack C (left.length + shared.length + right.length + 1) := by
    have hL : py.length ≤ right.length - j +
        logSlack 6 (left.length + shared.length + right.length + 1) := by
      simpa [py, N, List.length_drop] using hPyLength
    have hS :
        logSlack 6 (left.length + shared.length + right.length + 1) + cy ≤
          logSlack C (left.length + shared.length + right.length + 1) := by
      simpa [N] using hFinalSlackY
    omega
  constructor
  · exact hBoundX.trans (by
      rw [← Nat.cast_add]
      exact_mod_cast hNatX)
  · exact hBoundY.trans (by
      rw [← Nat.cast_add]
      exact_mod_cast hNatY)

/-- Decoder leaf for the two material-bit families in the source proof of the
upper extremizer.  A common string is either a prefix of the shared block, or
the whole shared block together with prefixes of the two private blocks. -/
theorem commonInformationRegion_contains_overlapMaterialProfiles
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ left shared right : BitString,
      (∀ i : Nat, i ≤ shared.length →
        commonInformationTripleInflate
            (logSlack c (left.length + shared.length + right.length + 1))
            (i,
              (left.length + shared.length - i,
                shared.length + right.length - i)) ∈
          CommonInformationRegion V
            (left ++ shared) (shared ++ right)) ∧
      (∀ i j : Nat, i ≤ left.length → j ≤ right.length →
        commonInformationTripleInflate
            (logSlack c (left.length + shared.length + right.length + 1))
            (shared.length + i + j,
              (left.length - i, right.length - j)) ∈
          CommonInformationRegion V
            (left ++ shared) (shared ++ right)) := by
  obtain ⟨cLen, hLen⟩ := plainK_le_length V hV
  obtain ⟨cInsert, hInsert⟩ := condK_insert_visible_context_le V hV
  obtain ⟨cPrivate, hPrivate⟩ :=
    condK_overlapFactors_given_materialPrefixes_le V hV
  let C := cLen + cInsert + cPrivate + 1
  refine ⟨C, fun left shared right => ?_⟩
  let N := left.length + shared.length + right.length + 1
  have hLenSlack : cLen < logSlack C N := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have hInsertSlack : logSlack cInsert N < logSlack C N := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have hPrivateSlack : logSlack cPrivate N < logSlack C N := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  constructor
  · intro i hi
    let z := shared.take i
    have hzLength : z.length = i := by
      dsimp [z]
      rw [List.length_take]
      omega
    have hxRaw := hInsert left z (shared.drop i)
    have hyRaw := hInsert [] z (shared.drop i ++ right)
    have hTakeDrop : shared.take i ++ shared.drop i = shared :=
      List.take_append_drop i shared
    have hxBound : condK V (left ++ shared) z ≤
        ((left.length + shared.length - i + logSlack cInsert N : Nat) : ENat) := by
      have h := hxRaw
      rw [show left ++ z ++ shared.drop i = left ++ shared by
        simp [z, List.append_assoc, hTakeDrop]] at h
      have hArg :
          left.length + z.length + (shared.drop i).length + 1 ≤ N := by
        dsimp [N]
        rw [hzLength, List.length_drop]
        omega
      have hNat :
          left.length + (shared.drop i).length +
              logSlack cInsert
                (left.length + z.length + (shared.drop i).length + 1) ≤
            left.length + shared.length - i + logSlack cInsert N := by
        have hArg' :
            left.length + z.length + (shared.length - i) + 1 ≤ N := by
          simpa [List.length_drop] using hArg
        have hSlack := logSlack_mono_right cInsert hArg'
        rw [List.length_drop]
        omega
      exact h.trans (by exact_mod_cast hNat)
    have hyBound : condK V (shared ++ right) z ≤
        ((shared.length + right.length - i + logSlack cInsert N : Nat) : ENat) := by
      have h := hyRaw
      rw [show [] ++ z ++ (shared.drop i ++ right) = shared ++ right by
        simp only [List.nil_append]
        rw [← List.append_assoc, hTakeDrop]] at h
      have hArg :
          0 + z.length + (shared.drop i ++ right).length + 1 ≤ N := by
        dsimp [N]
        rw [hzLength, List.length_append, List.length_drop]
        omega
      have hNat :
          0 + (shared.drop i ++ right).length +
              logSlack cInsert
                (0 + z.length + (shared.drop i ++ right).length + 1) ≤
            shared.length + right.length - i + logSlack cInsert N := by
        have hArg' :
            z.length + (shared.length - i + right.length) + 1 ≤ N := by
          simpa [List.length_append, List.length_drop] using hArg
        have hSlack := logSlack_mono_right cInsert hArg'
        simp only [List.length_append, List.length_drop,
          Nat.zero_add]
        omega
      exact h.trans (by exact_mod_cast hNat)
    change ∃ w,
      plainK V w < ((i + logSlack C N : Nat) : ENat) ∧
        condK V (left ++ shared) w <
          ((left.length + shared.length - i + logSlack C N : Nat) : ENat) ∧
        condK V (shared ++ right) w <
          ((shared.length + right.length - i + logSlack C N : Nat) : ENat)
    refine ⟨z, ?_, ?_, ?_⟩
    · have h := hLen z
      change plainK V z ≤ (z.length : ENat) + (cLen : ENat) at h
      rw [hzLength] at h
      exact h.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hLenSlack i)
    · exact hxBound.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hInsertSlack
          (left.length + shared.length - i))
    · exact hyBound.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hInsertSlack
          (shared.length + right.length - i))
  · intro i j hi hj
    let z := shared ++ left.take i ++ right.take j
    have hzLength : z.length = shared.length + i + j := by
      dsimp [z]
      simp only [List.length_append, List.length_take]
      omega
    obtain ⟨hxBound, hyBound⟩ := hPrivate left shared right i j hi hj
    change ∃ w,
      plainK V w <
          ((shared.length + i + j + logSlack C N : Nat) : ENat) ∧
        condK V (left ++ shared) w <
          ((left.length - i + logSlack C N : Nat) : ENat) ∧
        condK V (shared ++ right) w <
          ((right.length - j + logSlack C N : Nat) : ENat)
    refine ⟨z, ?_, ?_, ?_⟩
    · have h := hLen z
      change plainK V z ≤ (z.length : ENat) + (cLen : ENat) at h
      rw [hzLength] at h
      exact h.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hLenSlack
          (shared.length + i + j))
    · exact hxBound.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hPrivateSlack (left.length - i))
    · exact hyBound.trans_lt (by
        exact_mod_cast Nat.add_lt_add_left hPrivateSlack (right.length - j))

/-- The remaining extremal direction of SUV Theorem 225: overlapping length
`2n` factors of an incompressible length-`3n` string realize the universal
upper envelope.  The two quantified containments state equality up to one
uniform coordinatewise logarithmic inflation. -/
theorem common_information_upper_envelope_achieved
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ n : Nat,
      ∃ x y : BitString, ∃ kx ky kxy : Nat,
        HasPlainComplexityValue V x kx ∧
        HasPlainComplexityValue V y ky ∧
        HasPlainComplexityValue V (pairCode x y) kxy ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        (∀ t ∈ CommonInformationUpperEnvelope (2 * n) (2 * n) (3 * n),
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationRegion V x y) ∧
        (∀ t ∈ CommonInformationRegion V x y,
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationUpperEnvelope (2 * n) (2 * n) (3 * n)) := by
  obtain ⟨cProfile, hProfile⟩ :=
    exists_incompressibleOverlapPairProfile V hV
  obtain ⟨cMaterial, hMaterial⟩ :=
    commonInformationRegion_contains_overlapMaterialProfiles V hV
  obtain ⟨cUpper, hUpper⟩ :=
    common_information_profile_upper V hV cProfile
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cMaterial 3 1
  let C := cProfile + cUpper + cFold
  refine ⟨C, fun n => ?_⟩
  obtain ⟨left, shared, right, kx, ky, kxy,
    hLeftLength, hSharedLength, hRightLength,
    hx, hy, hxy, hxClose, hyClose, hxyClose⟩ := hProfile n
  let x := left ++ shared
  let y := shared ++ right
  have hcProfile : cProfile ≤ C := by dsimp [C]; omega
  have hcUpper : cUpper ≤ C := by dsimp [C]; omega
  have hcFold : cFold ≤ C := by dsimp [C]; omega
  have hProfileSlack : logSlack cProfile n ≤ logSlack C n :=
    logSlack_mono_left hcProfile n
  have hUpperSlack : logSlack cUpper n ≤ logSlack C n :=
    logSlack_mono_left hcUpper n
  have hMaterialSlack :
      logSlack cMaterial
          (left.length + shared.length + right.length + 1) ≤
        logSlack C n := by
    rw [hLeftLength, hSharedLength, hRightLength]
    have hArgument : n + n + n + 1 = 3 * n + 1 := by omega
    rw [hArgument]
    exact (hFold n).trans (logSlack_mono_left hcFold n)
  have hMaterialSlack' :
      logSlack cMaterial (n + n + n + 1) ≤ logSlack C n := by
    simpa only [hLeftLength, hSharedLength, hRightLength] using
      hMaterialSlack
  refine ⟨x, y, kx, ky, kxy, hx, hy, hxy,
    hxClose.mono hProfileSlack, hyClose.mono hProfileSlack,
    hxyClose.mono hProfileSlack, ?_, ?_⟩
  · intro t ht
    obtain ⟨hSharedProfiles, hPrivateProfiles⟩ :=
      hMaterial left shared right
    rcases commonInformationUpperEnvelope_overlap_case_cover ht with
      hSharedCase | hPrivateCase
    · rcases hSharedCase with ⟨i, hi, hFirst, hLeft, hRight⟩
      have hMem := hSharedProfiles i (by simpa [hSharedLength] using hi)
      refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
      all_goals
        simp only [commonInformationTripleInflate,
          hLeftLength, hSharedLength, hRightLength]
        omega
    · rcases hPrivateCase with
        ⟨i, j, hi, hj, hFirst, hLeft, hRight⟩
      have hMem := hPrivateProfiles i j
        (by simpa [hLeftLength] using hi)
        (by simpa [hRightLength] using hj)
      refine commonInformationRegion_upward_closed ?_ ?_ ?_ hMem
      all_goals
        simp only [commonInformationTripleInflate,
          hLeftLength, hSharedLength, hRightLength]
        omega
  · intro t ht
    have hContainment := hUpper n x y kx ky kxy hx hy hxy
      hxClose hyClose hxyClose t ht
    refine commonInformationUpperEnvelope_upward_closed
      (2 * n) (2 * n) (3 * n) hContainment ?_ ?_ ?_
    all_goals
      simp only [commonInformationTripleInflate]
      omega

end Kolmogorov
