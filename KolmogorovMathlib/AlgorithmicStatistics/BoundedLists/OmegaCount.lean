import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.Basic
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.AlgorithmicProbability.ConditionalCoding

/-!
# The finite Omega: counting the strings of bounded complexity

`omegaCount c m` is the number of distinct outputs of the programs of length at most `m` — the
finite counterpart of the halting probability, in the sense that knowing it lets one run the
enumeration of `BoundedLists/Basic` to completion.  `omegaFixedCode` writes that number in
exactly `m + 1` bits, using the fixed-width numeral `fixedWidthNatCode` and its decoder
`decodeFixedWidthNatCode`.

The facts recorded here are the ones every later use needs: the count is below `2 ^ (m + 1)`
(`omegaCount_lt_two_pow_succ`) and below the number of programs
(`omegaCount_le_boundedPrograms`); it depends on the code `c` only through the map it computes
(`omegaCount_eq_of_isCodeFor`, `omegaFixedCode_eq_of_isCodeFor`); and a stage whose
enumeration already has `omegaCount c m` entries is the completed list
(`boundedOutputStage_eq_completed_of_length_eq`), which is how a program that is given the
count recognises that it may stop.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- The number of distinct outputs of the programs of length at most `m`, the finite
counterpart of Chaitin's `Ω`. -/
noncomputable def omegaCount (c : Code) (m : ℕ) : ℕ :=
  (completedBoundedOutput c m).length

/-- The binary numeral of `omegaCount c m`. -/
noncomputable def omegaNatCode (c : Code) (m : ℕ) : List Bool :=
  Nat.bits (omegaCount c m)

/-- The number `n` written in exactly `width` bits, most significant bit first. -/
def fixedWidthNatCode (n width : ℕ) : BitString :=
  (chunkAddress n width).reverse

/-- The number read off a fixed-width code. -/
def decodeFixedWidthNatCode (z : BitString) : ℕ :=
  bitsToNat z.reverse

/-- A number below `2 ^ width` is coded in exactly `width` bits. -/
theorem fixedWidthNatCode_length
    {n width : ℕ} (h : n < 2 ^ width) :
    (fixedWidthNatCode n width).length = width := by
  unfold fixedWidthNatCode
  rw [List.length_reverse, chunkAddress_length _ _ h]

/-- Decoding a fixed-width code returns the coded number. -/
@[simp] theorem decodeFixedWidthNatCode_encode
    (n width : ℕ) :
    decodeFixedWidthNatCode (fixedWidthNatCode n width) = n := by
  unfold decodeFixedWidthNatCode fixedWidthNatCode
  rw [List.reverse_reverse, bitsToNat_chunkAddress]

/-- The count `omegaCount c m` written in exactly `m + 1` bits. -/
noncomputable def omegaFixedCode (c : Code) (m : ℕ) : List Bool :=
  fixedWidthNatCode (omegaCount c m) (m + 1)

/-- Fewer than `2 ^ (m + 1)` strings have plain complexity at most `m`. -/
theorem omegaCount_lt_two_pow_succ (c : Code) (m : ℕ) :
    omegaCount c m < 2 ^ (m + 1) := by
  unfold omegaCount completedBoundedOutput
  have h1 : (boundedOutputStage c m (maxHaltingStage c m)).length =
      (boundedOutputStage c m (maxHaltingStage c m)).toFinset.card :=
    (List.toFinset_card_of_nodup (boundedOutputStage_nodup c m (maxHaltingStage c m))).symm
  rw [h1, boundedOutputStage_toFinset_eq_snapshotCodes c m (maxHaltingStage c m)]
  have h2 : (snapshotCodes c m (maxHaltingStage c m)).toFinset.card ≤
      (snapshotCodes c m (maxHaltingStage c m)).length :=
    List.toFinset_card_le (snapshotCodes c m (maxHaltingStage c m))
  have h3 : (snapshotCodes c m (maxHaltingStage c m)).length ≤ (boundedPrograms m).length :=
    List.length_filterMap_le _ _
  have h4 := length_boundedPrograms_lt m
  omega

/-- There are at most as many outputs as there are programs of length at most `m`. -/
theorem omegaCount_le_boundedPrograms (c : Code) (m : ℕ) :
    omegaCount c m ≤ (boundedPrograms m).length := by
  unfold omegaCount completedBoundedOutput
  have h1 : (boundedOutputStage c m (maxHaltingStage c m)).length =
      (boundedOutputStage c m (maxHaltingStage c m)).toFinset.card :=
    (List.toFinset_card_of_nodup (boundedOutputStage_nodup c m (maxHaltingStage c m))).symm
  rw [h1, boundedOutputStage_toFinset_eq_snapshotCodes c m (maxHaltingStage c m)]
  have h2 : (snapshotCodes c m (maxHaltingStage c m)).toFinset.card ≤
      (snapshotCodes c m (maxHaltingStage c m)).length :=
    List.toFinset_card_le (snapshotCodes c m (maxHaltingStage c m))
  have h3 : (snapshotCodes c m (maxHaltingStage c m)).length ≤ (boundedPrograms m).length :=
    List.length_filterMap_le _ _
  omega

/-- `omegaCount` depends on the code `c` only through the map it computes: two
codes for the same map `V` enumerate the same completed bounded-output set
(membership is characterized by `plainK V ≤ m`, which is code-independent), and
both completed lists are duplicate-free, so they have equal length. -/
theorem omegaCount_eq_of_isCodeFor
    {V : Map} {c₁ c₂ : Code} (hc₁ : IsCodeFor c₁ V) (hc₂ : IsCodeFor c₂ V)
    (m : ℕ) :
    omegaCount c₁ m = omegaCount c₂ m := by
  have hset : (completedBoundedOutput c₁ m).toFinset
      = (completedBoundedOutput c₂ m).toFinset := by
    ext x
    rw [List.mem_toFinset, List.mem_toFinset,
      mem_completedBoundedOutput_iff_plainK_le hc₁ m x,
      mem_completedBoundedOutput_iff_plainK_le hc₂ m x]
  have h1 : (completedBoundedOutput c₁ m).length
      = (completedBoundedOutput c₁ m).toFinset.card :=
    (List.toFinset_card_of_nodup
      (boundedOutputStage_nodup c₁ m (maxHaltingStage c₁ m))).symm
  have h2 : (completedBoundedOutput c₂ m).length
      = (completedBoundedOutput c₂ m).toFinset.card :=
    (List.toFinset_card_of_nodup
      (boundedOutputStage_nodup c₂ m (maxHaltingStage c₂ m))).symm
  unfold omegaCount
  rw [h1, h2, hset]

/-- `omegaFixedCode` depends on the code `c` only through the map it computes:
any two codes for the same map `V` yield identical finite-Omega codes.  This is
the code-swap step that lets the arbitrary code `q` in
`PropMinHereditaryStatement` be replaced by the concrete code driving the
standard-block / omega machinery. -/
theorem omegaFixedCode_eq_of_isCodeFor
    {V : Map} {c₁ c₂ : Code} (hc₁ : IsCodeFor c₁ V) (hc₂ : IsCodeFor c₂ V)
    (m : ℕ) :
    omegaFixedCode c₁ m = omegaFixedCode c₂ m := by
  unfold omegaFixedCode
  rw [omegaCount_eq_of_isCodeFor hc₁ hc₂ m]

/-- A repetition-free list shorter than `2 ^ n` misses some string of length `n`. -/
theorem exists_mem_allStrings_not_mem_of_length_lt
    {L : List BitString} {n : ℕ}
    (hL : L.Nodup) (hlen : L.length < 2 ^ n) :
    ∃ x, x ∈ allStrings n ∧ x ∉ L := by
  by_contra h
  push_neg at h
  have hsub : (allStrings n).toFinset ⊆ L.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact h x hx
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (allStrings_nodup n),
    List.toFinset_card_of_nodup hL, length_allStrings] at hcard
  omega

/-- A stage whose enumeration already has `omegaCount c m` entries is the completed
list. -/
theorem boundedOutputStage_eq_completed_of_length_eq
    (c : Code) (m t : ℕ)
    (hlen : (boundedOutputStage c m t).length = omegaCount c m) :
    boundedOutputStage c m t = completedBoundedOutput c m := by
  apply boundedOutputStage_eq_completed_of_completion_le
  apply boundedOutputCompletionTime_le_complete_stage
  simpa [omegaCount] using hlen

/-- The fixed-width code of the count has length `m + 1`. -/
theorem omegaFixedCode_length (c : Code) (m : ℕ) :
    (omegaFixedCode c m).length = m + 1 := by
  exact fixedWidthNatCode_length (omegaCount_lt_two_pow_succ c m)

/-- Decoding the fixed-width code of the count returns the count. -/
theorem decode_omegaFixedCode (c : Code) (m : ℕ) :
    decodeFixedWidthNatCode (omegaFixedCode c m) = omegaCount c m :=
  decodeFixedWidthNatCode_encode _ _

-- plainK_partrec_map_le
/-- Applying a fixed partial recursive map raises plain complexity by at most an
additive constant. -/
theorem plainK_partrec_map_le (V : Map) (hV : isOptimalConditional V)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ x w : BitString, w ∈ f x → plainK V w ≤ plainK V x + (c : ENat) := by
  set D : Map := fun pr ↦ (V pr).bind (fun z ↦ f z) with hDdef
  have hD_decomp : isDecompressor D :=
    Partrec.bind hV.1 (hf.comp Computable.snd)
  obtain ⟨c, hc⟩ := hV.2 D hD_decomp
  refine ⟨c, fun x w hw ↦ ?_⟩
  calc
    plainK V w ≤ plainK D w + (c : ENat) := hc w []
    _ ≤ plainK V x + (c : ENat) := by
      have : plainK D w ≤ plainK V x := by
        unfold plainK condK
        apply le_sInf
        rintro n ⟨p, hp, rfl⟩
        apply sInf_le
        refine ⟨p, ?_, rfl⟩
        simp only [produces, hDdef]
        exact Part.mem_bind_iff.mpr ⟨x, hp, hw⟩
      gcongr

open Classical in
-- omegaDiagonalSelector
/-- The selector that reads a program for the count `omegaCount c m` together with
the offset `e`, waits until the enumeration has that many entries, and returns
the first length-`m + 1` string outside it. -/
noncomputable def omegaDiagonalSelector (V : Map) (c : Code) (z : BitString) : Part BitString := do
  let e_bits := decodeFirst z
  let p := decodeSecond z
  let e := bitsToNat e_bits
  let m := p.length + e
  let omega_bits ← V (p, [])
  let count := bitsToNat omega_bits
  let t ← Nat.rfind (fun t => Part.some ((boundedOutputStage c m t).length == count))
  let S := boundedOutputStage c m t
  let L := canonicalFinsetList (stringsOfLength (m + 1))
  let x ← Part.ofOption (L.find? (fun s => decide (s ∉ S)))
  Part.some x

/-- The diagonal selector is a partial recursive function of its input. -/
theorem omegaDiagonalSelector_partrec
    (V : Map) (hV : isDecompressor V)
    (c : Nat.Partrec.Code) :
    Partrec (omegaDiagonalSelector V c) := by
  have hrun : Partrec (fun z : BitString => V (decodeSecond z, [])) :=
    Partrec.comp hV
      (Computable.pair decodeSecond_computable (Computable.const []))
  have hm : Primrec (fun st : (BitString × BitString) × ℕ =>
      (decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) :=
    Primrec.nat_add.comp
      (Primrec.list_length.comp
        (decodeSecond_primrec.comp (Primrec.fst.comp Primrec.fst)))
      (bitsToNat_primrec.comp
        (decodeFirst_primrec.comp (Primrec.fst.comp Primrec.fst)))
  have hstage : Primrec (fun st : (BitString × BitString) × ℕ =>
      boundedOutputStage c
        ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) st.2) :=
    (boundedOutputStage_primrec c).comp (Primrec.pair hm Primrec.snd)
  have hcheck : Computable₂ (fun (q : BitString × BitString) (t : ℕ) =>
      (boundedOutputStage c
        ((decodeSecond q.1).length + bitsToNat (decodeFirst q.1)) t).length ==
          bitsToNat q.2) :=
    (Primrec.beq.comp
      (Primrec.list_length.comp hstage)
      (bitsToNat_primrec.comp (Primrec.snd.comp Primrec.fst))).to_comp.to₂
  have hsearch : Partrec (fun q : BitString × BitString =>
      Nat.rfind (fun t => Part.some
        ((boundedOutputStage c
          ((decodeSecond q.1).length + bitsToNat (decodeFirst q.1)) t).length ==
            bitsToNat q.2))) :=
    Partrec.rfind hcheck.partrec₂
  have hstrings : Primrec (fun st : (BitString × BitString) × ℕ =>
      canonicalFinsetList (stringsOfLength
        ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1) + 1))) := by
    convert canonicalFinsetList_toFinset_primrec.comp
      (allStrings_primrec.comp (Primrec.succ.comp hm)) using 1
  have hnotmem : Primrec₂
      (fun (st : (BitString × BitString) × ℕ) (s : BitString) =>
        decide (s ∉ boundedOutputStage c
          ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) st.2)) := by
    refine (Primrec.not.comp
      (bitString_mem_primrec.comp Primrec.snd (hstage.comp Primrec.fst))).to₂.of_eq ?_
    intro st s
    simp
  have hfindOpt : Primrec (fun st : (BitString × BitString) × ℕ =>
      (canonicalFinsetList (stringsOfLength
        ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1) + 1))).find?
          (fun s => decide (s ∉ boundedOutputStage c
            ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) st.2))) :=
    list_find?_primrec hstrings hnotmem
  have hfindPart : Partrec (fun st : (BitString × BitString) × ℕ =>
      Part.ofOption
        ((canonicalFinsetList (stringsOfLength
          ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1) + 1))).find?
            (fun s => decide (s ∉ boundedOutputStage c
              ((decodeSecond st.1.1).length + bitsToNat (decodeFirst st.1.1)) st.2)))) :=
    hfindOpt.to_comp.ofOption
  have hpure : Partrec₂
      (fun (_ : (BitString × BitString) × ℕ) (x : BitString) => Part.some x) :=
    (Partrec.comp Partrec.some Computable.snd).to₂
  have hfind : Partrec₂ (fun (q : BitString × BitString) (t : ℕ) =>
      (Part.ofOption
        ((canonicalFinsetList (stringsOfLength
          ((decodeSecond q.1).length + bitsToNat (decodeFirst q.1) + 1))).find?
            (fun s => decide (s ∉ boundedOutputStage c
              ((decodeSecond q.1).length + bitsToNat (decodeFirst q.1)) t)))).bind
        (fun x => Part.some x)) :=
    (Partrec.bind hfindPart hpure).to₂
  have hafter : Partrec₂ (fun (z omegaBits : BitString) =>
      (Nat.rfind (fun t => Part.some
        ((boundedOutputStage c
          ((decodeSecond z).length + bitsToNat (decodeFirst z)) t).length ==
            bitsToNat omegaBits))).bind
        (fun t =>
          (Part.ofOption
            ((canonicalFinsetList (stringsOfLength
              ((decodeSecond z).length + bitsToNat (decodeFirst z) + 1))).find?
                (fun s => decide (s ∉ boundedOutputStage c
                  ((decodeSecond z).length + bitsToNat (decodeFirst z)) t)))).bind
            (fun x => Part.some x))) :=
    (Partrec.bind hsearch hfind).to₂
  unfold omegaDiagonalSelector
  convert Partrec.bind hrun hafter using 1

/-- On a program producing the count for `m = |p| + e`, the selector outputs a
string of length `m + 1` of plain complexity greater than `m`. -/
theorem omegaDiagonalSelector_intended_input
    {V : Map} (_hdec : isDecompressor V)
    (c : Nat.Partrec.Code) {m e : ℕ} {p : BitString}
    (hm : m = p.length + e)
    (hp : produces V p [] (Nat.bits (omegaCount c m))) :
    ∃ x,
      x ∈ omegaDiagonalSelector V c
        (pairCode (Nat.bits e) p) ∧
      x.length = m + 1 ∧
      x ∉ completedBoundedOutput c m := by
  subst m
  let M := p.length + e
  let completeTime := boundedOutputCompletionTime c M
  have hcompleteLength :
      (boundedOutputStage c M completeTime).length = omegaCount c M := by
    simpa [completeTime, omegaCount] using boundedOutputCompletionTime_spec c M
  let hex : ∃ t, (boundedOutputStage c M t).length = omegaCount c M :=
    ⟨completeTime, hcompleteLength⟩
  let t0 := Nat.find hex
  have ht0Length : (boundedOutputStage c M t0).length = omegaCount c M :=
    Nat.find_spec hex
  have ht0Complete :
      boundedOutputStage c M t0 = completedBoundedOutput c M :=
    boundedOutputStage_eq_completed_of_length_eq c M t0 ht0Length
  have ht0Nodup : (boundedOutputStage c M t0).Nodup :=
    boundedOutputStage_nodup c M t0
  have ht0Short : (boundedOutputStage c M t0).length < 2 ^ (M + 1) := by
    rw [ht0Length]
    exact omegaCount_lt_two_pow_succ c M
  obtain ⟨x0, hx0all, hx0missing⟩ :=
    exists_mem_allStrings_not_mem_of_length_lt ht0Nodup ht0Short
  let fullList := canonicalFinsetList (stringsOfLength (M + 1))
  have hx0full : x0 ∈ fullList := by
    apply mem_canonicalFinsetList.mpr
    exact (mem_stringsOfLength (M + 1) x0).mpr
      ((mem_allStrings (M + 1) x0).mp hx0all)
  have hfindSome :
      ∃ x, fullList.find?
        (fun s => decide (s ∉ boundedOutputStage c M t0)) = some x := by
    apply Option.isSome_iff_exists.mp
    rw [List.find?_isSome]
    exact ⟨x0, hx0full, by simp [hx0missing]⟩
  obtain ⟨x, hxfind⟩ := hfindSome
  have hxfull : x ∈ fullList :=
    List.mem_of_find?_eq_some hxfind
  have hxlen : x.length = M + 1 := by
    exact (mem_stringsOfLength (M + 1) x).mp
      (mem_canonicalFinsetList.mp hxfull)
  have hxmissingStage : x ∉ boundedOutputStage c M t0 := by
    have hpred := List.find?_some hxfind
    simpa using hpred
  have hxmissingCompleted : x ∉ completedBoundedOutput c M := by
    simpa [ht0Complete] using hxmissingStage
  have ht0Search :
      t0 ∈ Nat.rfind (fun t => Part.some
        ((boundedOutputStage c M t).length == omegaCount c M)) := by
    rw [Nat.mem_rfind]
    refine ⟨?_, ?_⟩
    · simp [ht0Length]
    · intro t ht
      have hne : (boundedOutputStage c M t).length ≠ omegaCount c M :=
        Nat.find_min hex ht
      simp [hne]
  refine ⟨x, ?_, hxlen, hxmissingCompleted⟩
  unfold omegaDiagonalSelector
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  change x ∈ (V (p, [])).bind (fun omegaBits =>
    (Nat.rfind (fun t => Part.some
      ((boundedOutputStage c M t).length == bitsToNat omegaBits))).bind
        (fun t =>
          (Part.ofOption
            ((canonicalFinsetList (stringsOfLength (M + 1))).find?
              (fun s => decide (s ∉ boundedOutputStage c M t)))).bind
                (fun y => Part.some y)))
  rw [Part.mem_bind_iff]
  refine ⟨Nat.bits (omegaCount c M), ?_, ?_⟩
  · simpa [M] using hp
  · simp only [bitsToNat_bits]
    rw [Part.mem_bind_iff]
    refine ⟨t0, ht0Search, ?_⟩
    rw [show (canonicalFinsetList (stringsOfLength (M + 1))).find?
      (fun s => decide (s ∉ boundedOutputStage c M t0)) = some x by
        simpa [fullList] using hxfind]
    rw [Part.mem_bind_iff]
    exact ⟨x, Part.mem_some x, Part.mem_some x⟩

/-- The binary numeral of the count has plain complexity at most `m` plus a
constant. -/
theorem plainK_omegaCount_upper_bound (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ const : ℕ, ∀ m : ℕ, plainK V (omegaNatCode c m) ≤ (m : ENat) + (const : ENat) := by
  obtain ⟨C, hC⟩ := plainK_le_length V hV
  refine ⟨C + 1, fun m => ?_⟩
  have hlen : (omegaNatCode c m).length ≤ m + 1 := by
    exact length_natBits_lt_pow (omegaCount_lt_two_pow_succ c m)
  calc
    plainK V (omegaNatCode c m)
        ≤ ((omegaNatCode c m).length : ENat) + (C : ENat) := hC _
    _ ≤ ((m + 1 : ℕ) : ENat) + (C : ENat) := by
      gcongr
    _ = (m : ENat) + ((C + 1 : ℕ) : ENat) := by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
      simp [add_comm, add_left_comm]

/-- The count itself has plain complexity at most `m` plus a constant. -/
theorem plainKNat_omegaCount_upper
    (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ m,
      plainKNat V (omegaCount c m) ≤ ((m + C : ℕ) : ENat) := by
  obtain ⟨C, hC⟩ := plainK_omegaCount_upper_bound V hV c
  refine ⟨C, fun m => ?_⟩
  simpa [plainKNat, omegaNatCode, Nat.cast_add] using hC m

/-- From some point on the count is at least `2 ^ (m - C)`. -/
theorem omegaCount_lower_of_plainK_length
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m, C ≤ m →
      2 ^ (m - C) ≤ omegaCount c m := by
  obtain ⟨C, hC⟩ := plainK_le_length V hV
  refine ⟨C, fun m hCm => ?_⟩
  have hsub : stringsOfLength (m - C) ⊆
      (completedBoundedOutput c m).toFinset := by
    intro x hx
    rw [List.mem_toFinset]
    apply (mem_completedBoundedOutput_iff_plainK_le hc m x).mpr
    have hxlen : x.length = m - C :=
      (mem_stringsOfLength (m - C) x).mp hx
    calc
      plainK V x ≤ (x.length : ENat) + (C : ENat) := hC x
      _ = (((m - C) + C : ℕ) : ENat) := by
        rw [hxlen, Nat.cast_add]
      _ ≤ (m : ENat) := by
        exact_mod_cast (by omega : m - C + C ≤ m)
  calc
    2 ^ (m - C) = (stringsOfLength (m - C)).card :=
      (card_stringsOfLength (m - C)).symm
    _ ≤ (completedBoundedOutput c m).toFinset.card :=
      Finset.card_le_card hsub
    _ = (completedBoundedOutput c m).length :=
      List.toFinset_card_of_nodup
        (boundedOutputStage_nodup c m (maxHaltingStage c m))
    _ = omegaCount c m := rfl

/-- A string missing from the completed output list for `m` has plain complexity
greater than `m`. -/
theorem plainK_gt_of_not_mem_completed
    {V : Map} {c : Code}
    (hc : IsCodeFor c V) {m : ℕ} {x : BitString}
    (hx : x ∉ completedBoundedOutput c m) :
    (m : ENat) < plainK V x := by
  apply lt_of_not_ge
  intro hle
  exact hx ((mem_completedBoundedOutput_iff_plainK_le hc m x).mpr hle)

/-- The number of binary digits of `e` is at most `√e + 2`. -/
theorem bits_length_le_sqrt_add_two (e : ℕ) :
    (Nat.bits e).length ≤ Nat.sqrt e + 2 := by
  have hsquarePow : ∀ q : ℕ, (q + 1) * (q + 1) ≤ 2 ^ (q + 2) := by
    intro q
    rcases q with (_ | _ | q)
    · norm_num
    · norm_num
    · induction q with
      | zero => norm_num
      | succ q ih =>
        norm_num [Nat.pow_succ'] at ih ⊢
        nlinarith
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  calc
    e < (Nat.sqrt e + 1) * (Nat.sqrt e + 1) := Nat.lt_succ_sqrt e
    _ ≤ 2 ^ (Nat.sqrt e + 2) := hsquarePow (Nat.sqrt e)

/-- The numbers `e` with `e ≤ 2 * |bits e| + A` are bounded by a constant depending
only on `A`. -/
theorem deficit_bounded_of_le_two_mul_bits_length_add
    (A : ℕ) :
    ∃ D : ℕ, ∀ e : ℕ,
      e ≤ 2 * (Nat.bits e).length + A →
      e ≤ D := by
  refine ⟨(A + 5) ^ 2, fun e he => ?_⟩
  have hbits := bits_length_le_sqrt_add_two e
  have he' : e ≤ 2 * Nat.sqrt e + (A + 4) := by omega
  have hsqrt : Nat.sqrt e ≤ A + 4 := by
    by_contra h
    have hgt : A + 4 < Nat.sqrt e := Nat.lt_of_not_ge h
    have hsquare := Nat.sqrt_le e
    nlinarith
  have hupper := Nat.lt_succ_sqrt e
  nlinarith

/-- The count has plain complexity at least `m` up to an additive constant. -/
theorem plainKNat_omegaCount_lower
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m : ℕ,
      (m : ENat) ≤ plainKNat V (omegaCount c m) + (C : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV (omegaDiagonalSelector V c)
      (omegaDiagonalSelector_partrec V hV.1 c)
  obtain ⟨Clen, hlen⟩ := plainK_le_length V hV
  obtain ⟨D, hD⟩ :=
    deficit_bounded_of_le_two_mul_bits_length_add (Clen + Cmap)
  refine ⟨D, fun m => ?_⟩
  have hfinite : plainK V (Nat.bits (omegaCount c m)) ≠ ⊤ := by
    intro htop
    have h := hlen (Nat.bits (omegaCount c m))
    rw [htop, top_le_iff] at h
    exact ENat.coe_ne_top _ h
  have hfinite' : KP V (Nat.bits (omegaCount c m)) [] ≠ ⊤ := by
    change plainK V (Nat.bits (omegaCount c m)) ≠ ⊤
    exact hfinite
  obtain ⟨p, hp, hpLength⟩ :=
    exists_program_of_KP_ne_top hfinite'
  by_cases hpm : m ≤ p.length
  · calc
      (m : ENat) ≤ (p.length : ENat) := by exact_mod_cast hpm
      _ = plainKNat V (omegaCount c m) := by
        simpa [plainKNat] using hpLength
      _ ≤ plainKNat V (omegaCount c m) + (D : ENat) :=
        le_add_right le_rfl
  · have hplt : p.length < m := Nat.lt_of_not_ge hpm
    let e := m - p.length
    have hm : m = p.length + e := by
      dsimp [e]
      omega
    obtain ⟨x, hxSelector, _, hxMissing⟩ :=
      omegaDiagonalSelector_intended_input hV.1 c hm hp
    have hxLower : (m : ENat) < plainK V x :=
      plainK_gt_of_not_mem_completed hc hxMissing
    have hxUpper :
        plainK V x ≤
          plainK V (pairCode (Nat.bits e) p) + (Cmap : ENat) :=
      hmap _ _ hxSelector
    have hinput :
        plainK V (pairCode (Nat.bits e) p) ≤
          ((pairCode (Nat.bits e) p).length : ENat) + (Clen : ENat) :=
      hlen _
    have hmx :
        (m : ENat) <
          ((pairCode (Nat.bits e) p).length : ENat) +
            (Clen : ENat) + (Cmap : ENat) := by
      exact lt_of_lt_of_le hxLower (hxUpper.trans (by
        gcongr))
    have hmxNat :
        m < (pairCode (Nat.bits e) p).length + Clen + Cmap := by
      exact_mod_cast hmx
    have heDeficit :
        e ≤ 2 * (Nat.bits e).length + (Clen + Cmap) := by
      rw [length_pairCode] at hmxNat
      omega
    have heD : e ≤ D := hD e heDeficit
    have hmD : m ≤ p.length + D := by omega
    calc
      (m : ENat) ≤ ((p.length + D : ℕ) : ENat) := by
        exact_mod_cast hmD
      _ = (p.length : ENat) + (D : ENat) := by
        rw [Nat.cast_add]
      _ = plainKNat V (omegaCount c m) + (D : ENat) := by
        rw [hpLength]
        rfl

/-- The four properties of the finite counts `omegaCount c m` together: the upper
bound `2 ^ (m + 1)`, the lower bound `2 ^ (m - C)`, and the two-sided estimate
of their plain complexity by `m`. -/
theorem prop_omegas
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ,
      (∀ m : ℕ, omegaCount c m < 2 ^ (m + 1)) ∧
      (∀ m : ℕ, C ≤ m →
        2 ^ (m - C) ≤ omegaCount c m) ∧
      (∀ m : ℕ,
        (m : ENat) ≤
          plainKNat V (omegaCount c m) + (C : ENat)) ∧
      (∀ m : ℕ,
        plainKNat V (omegaCount c m) ≤
          ((m + C : ℕ) : ENat)) := by
  obtain ⟨Ccard, hcard⟩ :=
    omegaCount_lower_of_plainK_length V hV c hc
  obtain ⟨Clower, hlower⟩ :=
    plainKNat_omegaCount_lower V hV c hc
  obtain ⟨Cupper, hupper⟩ :=
    plainKNat_omegaCount_upper V hV c
  let C := Ccard + Clower + Cupper
  refine ⟨C, fun m => omegaCount_lt_two_pow_succ c m, ?_, ?_, ?_⟩
  · intro m hCm
    have hCcard : Ccard ≤ m := by
      dsimp [C] at hCm
      omega
    have hexp : m - C ≤ m - Ccard := by
      dsimp [C]
      omega
    exact (Nat.pow_le_pow_right (by decide) hexp).trans (hcard m hCcard)
  · intro m
    calc
      (m : ENat) ≤
          plainKNat V (omegaCount c m) + (Clower : ENat) :=
        hlower m
      _ ≤ plainKNat V (omegaCount c m) + (C : ENat) := by
        gcongr
        exact_mod_cast (show Clower ≤ C by
          dsimp [C]
          omega)
  · intro m
    calc
      plainKNat V (omegaCount c m) ≤
          ((m + Cupper : ℕ) : ENat) :=
        hupper m
      _ ≤ ((m + C : ℕ) : ENat) := by
        exact_mod_cast (show m + Cupper ≤ m + C by
          dsimp [C]
          omega)

/-- **Upper bound for the fixed-width Omega code.**  Since `omegaFixedCode c m`
has length `m + 1`, its plain complexity is at most `m + O(1)`.  This is the
fixed-width companion of `plainK_omegaCount_upper_bound`. -/
theorem plainK_omegaFixedCode_upper
    (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ m : ℕ, plainK V (omegaFixedCode c m) ≤ ((m + C : ℕ) : ENat) := by
  obtain ⟨Clen, hlen⟩ := plainK_le_length V hV
  refine ⟨Clen + 1, fun m => ?_⟩
  calc
    plainK V (omegaFixedCode c m)
        ≤ ((omegaFixedCode c m).length : ENat) + (Clen : ENat) := hlen _
    _ = ((m + 1 : ℕ) : ENat) + (Clen : ENat) := by rw [omegaFixedCode_length]
    _ = ((m + (Clen + 1) : ℕ) : ENat) := by push_cast; ring

/-- **Lower bound for the fixed-width Omega code.**  The number `omegaCount c m`
is a computable image of `omegaFixedCode c m` (decode the fixed-width number,
then re-encode its bits), so `omegaNatCode c m` is `O(1)`-simple given the fixed
code.  Combined with `plainKNat_omegaCount_lower` this yields
`m ≤ plainK V (omegaFixedCode c m) + O(1)`.  This is the fixed-width companion of
`plainKNat_omegaCount_lower`, and the lower half needed to pin the complexity of
a finite Omega prefix to `m ± O(1)`. -/
theorem plainK_omegaFixedCode_lower
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m : ℕ,
      (m : ENat) ≤ plainK V (omegaFixedCode c m) + (C : ENat) := by
  obtain ⟨COmega, hOmega⟩ := plainKNat_omegaCount_lower V hV c hc
  have hf : Computable (fun w : BitString => Nat.bits (decodeFixedWidthNatCode w)) := by
    have hp : Primrec (fun w : BitString => Nat.bits (decodeFixedWidthNatCode w)) := by
      unfold decodeFixedWidthNatCode
      exact primrec_natBits.comp (bitsToNat_primrec.comp Primrec.list_reverse)
    exact hp.to_comp
  obtain ⟨Cmap, hmap⟩ := plainK_map_le V hV _ hf
  refine ⟨Cmap + COmega, fun m => ?_⟩
  have hmapm := hmap (omegaFixedCode c m)
  simp only [decode_omegaFixedCode] at hmapm
  calc
    (m : ENat) ≤ plainKNat V (omegaCount c m) + (COmega : ENat) := hOmega m
    _ = plainK V (Nat.bits (omegaCount c m)) + (COmega : ENat) := rfl
    _ ≤ (plainK V (omegaFixedCode c m) + (Cmap : ENat)) + (COmega : ENat) := by
        gcongr
    _ = plainK V (omegaFixedCode c m) + ((Cmap + COmega : ℕ) : ENat) := by
        push_cast; ring

end Kolmogorov
