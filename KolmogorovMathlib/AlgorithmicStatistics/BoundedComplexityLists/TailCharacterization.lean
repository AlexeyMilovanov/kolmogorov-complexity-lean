import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.Position
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization

/-!
# VS40 Section 4, Milestone B6: relation to the ordinary profile

This file develops the bridge between the prefix-machine description profile
`InDescriptionProfile U x i j` (Section 3) and the plain-complexity bounded
list `completedBoundedOutput c m` (Section 4, machine `V` with `IsCodeFor c V`).

The public endpoint is `tail_characterization`, with both directions:

* if `x` has an `(i,j)`-description then `x` is at least `2^(j-O(log n))` from
  the end of the `(i+j+O(log n))`-list;
* if at least `2^j` elements follow `x` in the `(i+j)`-list then `x` has an
  `(i+O(log n),j)`-description.

This file proves the **direction-1 membership workhorse**: every member of an
`(i,j)`-description has plain complexity `i+j+O(log j)`, hence appears in the
`(i+j+O(log j))`-list.  The argument is the two-part code
`y = decodeElement (S.code, address of y in S)`, whose plain complexity is
bounded by `setComplexity U S + |address| + O(1) ≤ i + j + O(log j)` using the
plain/prefix pair comparison `plainK_pair_le_KPPlain_add_KPPlain`.

For the forward direction, a uniform partial-recursive selector waits until
every member of the model has appeared, reads the exact number of remaining
outputs, and reconstructs `omegaCount`.  Its complexity bound contradicts
`plainKNat_omegaCount_lower` if the suffix is too short.  For the converse, a
second uniform selector reconstructs the full dyadic block containing `x`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- The block index of a member `y` of `S` fits in `j` bits when `|S| ≤ 2^j`. -/
theorem findIdx_lt_two_pow_of_card_le
    (S : Finset BitString) {y : BitString} (hy : y ∈ S)
    {j : ℕ} (hcard : S.card ≤ 2 ^ j) :
    (canonicalFinsetList S).findIdx (· == y) < 2 ^ j := by
  have h1 : (canonicalFinsetList S).findIdx (· == y) < (canonicalFinsetList S).length := by
    rw [List.findIdx_lt_length]
    exact ⟨y, mem_canonicalFinsetList.mpr hy, by simp⟩
  rw [length_canonicalFinsetList] at h1
  exact lt_of_lt_of_le h1 hcard

/-- **B6 direction-1 workhorse (complexity form).** Every member `y` of an
`(i,j)`-description of `x` has plain complexity at most `i + j + O(log j)`.

The description code `S.code` has `setComplexity U S ≤ i`; the address of `y`
inside `S` is a `j`-bit block address; `decodeElement` recovers `y` from the
pair of the two.  The plain complexity of that pair is bounded via the
plain/prefix pair comparison, giving the stated logarithmic slack. -/
theorem plainK_mem_le_of_isIJDescription
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (x y : BitString) (i j : ℕ) (S : Finset BitString) (hS : S.Nonempty),
      IsIJDescription U x S hS i j → y ∈ S →
      plainK V y ≤ ((i + j + logSlack C j : ℕ) : ENat) := by
  obtain ⟨Cmap, hmap⟩ := plainKMapLe V hV decodeElement decodeElement_computable
  obtain ⟨Cpair, hpair⟩ := plainK_pair_le_KPPlain_add_KPPlain V U hV hU
  obtain ⟨Clen, hlen⟩ := KPPlain_le_length_add_log U hU
  refine ⟨Clen + Cpair + Cmap + 2, fun x y i j S hS hdesc hy => ?_⟩
  obtain ⟨_, hcomp, hcard⟩ := hdesc
  -- The block index of `y`, its `j`-bit address, and the decoder identity.
  have hblockLt : (canonicalFinsetList S).findIdx (· == y) < 2 ^ j :=
    findIdx_lt_two_pow_of_card_le S hy hcard
  have hzlen :
      (chunkAddress ((canonicalFinsetList S).findIdx (· == y)) j).length = j :=
    chunkAddress_length _ j hblockLt
  have hdec :
      decodeElement (pairCode (codedUniformOn S hS).code
        (chunkAddress ((canonicalFinsetList S).findIdx (· == y)) j)) = y :=
    decodeElement_eq S hS y hy j
  set z := chunkAddress ((canonicalFinsetList S).findIdx (· == y)) j with hz
  set code := (codedUniformOn S hS).code with hcode
  -- `setComplexity U S hS = KPPlain U code`.
  have hcompCode : KPPlain U code ≤ (i : ENat) := by
    simpa [setComplexity, hcode] using hcomp
  have hzK : KPPlain U z ≤ ((j + 2 * (Nat.bits j).length + Clen : ℕ) : ENat) := by
    have h := hlen z
    rw [hzlen] at h
    calc KPPlain U z
        ≤ (j : ENat) + 2 * ((Nat.bits j).length : ENat) + (Clen : ENat) := h
      _ = ((j + 2 * (Nat.bits j).length + Clen : ℕ) : ENat) := by push_cast; ring
  -- The two-part code chain.
  have hchain :
      plainK V y ≤ ((i + (j + 2 * (Nat.bits j).length + Clen) + Cpair + Cmap : ℕ) : ENat) := by
    calc
      plainK V y = plainK V (decodeElement (pairCode code z)) := by rw [hdec]
      _ ≤ plainK V (pairCode code z) + (Cmap : ENat) := hmap _
      _ ≤ (KPPlain U code + KPPlain U z + (Cpair : ENat)) + (Cmap : ENat) := by
            gcongr; exact hpair _ _
      _ ≤ ((i : ENat) + ((j + 2 * (Nat.bits j).length + Clen : ℕ) : ENat)
            + (Cpair : ENat)) + (Cmap : ENat) := by gcongr
      _ = ((i + (j + 2 * (Nat.bits j).length + Clen) + Cpair + Cmap : ℕ) : ENat) := by
            push_cast; ring
  -- Absorb into `logSlack`.
  refine hchain.trans ?_
  have hnat :
      i + (j + 2 * (Nat.bits j).length + Clen) + Cpair + Cmap
        ≤ i + j + logSlack (Clen + Cpair + Cmap + 2) j := by
    have hDb : 2 * (Nat.bits j).length ≤ (Clen + Cpair + Cmap + 2) * (Nat.bits j).length :=
      Nat.mul_le_mul_right _ (by omega)
    unfold logSlack; omega
  exact_mod_cast hnat

/-- **B6 direction-1 workhorse (membership form).** Every member `y` of an
`(i,j)`-description of `x` appears in the completed `(i+j+O(log j))`-list.

This is the "wait until all elements of `A` appear in the `(i+j+O(log n))`-list"
step of `thm:tail-characterization` (direction 1): it certifies that the entire
description sits inside the bounded-complexity list at budget `i+j+O(log j)`. -/
theorem mem_completed_of_isIJDescription
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x y : BitString) (i j : ℕ) (S : Finset BitString) (hS : S.Nonempty),
      IsIJDescription U x S hS i j → y ∈ S →
      y ∈ completedBoundedOutput c (i + j + logSlack C j) := by
  obtain ⟨C, hC⟩ := plainK_mem_le_of_isIJDescription V U hV hU
  refine ⟨C, fun x y i j S hS hdesc hy => ?_⟩
  exact (mem_completedBoundedOutput_iff_plainK_le hc _ y).mpr
    (hC x y i j S hS hdesc hy)

/-- Specialisation to the description itself: an `(i,j)`-description of `x`
places `x` inside the `(i+j+O(log j))`-list. -/
theorem mem_completed_of_inDescriptionProfile
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (i j : ℕ),
      InDescriptionProfile U x i j →
      x ∈ completedBoundedOutput c (i + j + logSlack C j) := by
  obtain ⟨C, hC⟩ := mem_completed_of_isIJDescription V U hV hU c hc
  refine ⟨C, fun x i j hprof => ?_⟩
  obtain ⟨S, hS, hdesc⟩ := hprof
  exact hC x x i j S hS hdesc hdesc.1

/-! ## Direction 1: the forward Omega reconstruction selector -/

theorem exists_stage_covering_finset
    (c : Code) (m : ℕ) (S : Finset BitString)
    (hS : ∀ y ∈ S, y ∈ completedBoundedOutput c m) :
    ∃ t, ∀ y ∈ S, y ∈ boundedOutputStage c m t := by
  refine ⟨boundedOutputCompletionTime c m, fun y hy => ?_⟩
  have hy_comp := hS y hy
  rw [← boundedOutputStage_eq_completed_at_completion c m] at hy_comp
  exact hy_comp

theorem prefix_remainder_length_le_tailAfter
    {L T : List BitString} {x : BitString}
    (hpre : L <+: T) (hx : x ∈ L) :
    ∃ R, T = L ++ R ∧ R.length ≤ tailAfter T x := by
  obtain ⟨R, hR⟩ := hpre
  refine ⟨R, hR.symm, ?_⟩
  induction L generalizing T with
  | nil => contradiction
  | cons y ys ih =>
    cases T with
    | nil => contradiction
    | cons z zs =>
      simp only [List.cons_append, List.cons.injEq] at hR
      obtain ⟨hz, hzs⟩ := hR
      subst hz
      unfold tailAfter
      by_cases h_yx : y = x
      · rw [if_pos h_yx]
        rw [← hzs]
        simp only [List.length_append, Nat.le_add_left]
      · rw [if_neg h_yx]
        have hx_in_ys : x ∈ ys := by
          cases List.mem_cons.mp hx with
          | inl h => exact False.elim (h_yx h.symm)
          | inr h => exact h
        exact ih hx_in_ys hzs

def descriptionTailOmegaInput (scode : BitString) (m count : ℕ) : BitString :=
  pairCode scode (pairCode (Nat.bits m) (Nat.bits count))

def descriptionTailOmegaInputSCode (z : BitString) : BitString :=
  decodeFirst z

def descriptionTailOmegaInputM (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond z))

def descriptionTailOmegaInputCount (z : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeSecond z))

@[simp] theorem descriptionTailOmegaInputSCode_input (scode : BitString) (m count : ℕ) :
    descriptionTailOmegaInputSCode (descriptionTailOmegaInput scode m count) = scode := by
  unfold descriptionTailOmegaInputSCode descriptionTailOmegaInput
  rw [decodeFirst_pairCode]

@[simp] theorem descriptionTailOmegaInputM_input (scode : BitString) (m count : ℕ) :
    descriptionTailOmegaInputM (descriptionTailOmegaInput scode m count) = m := by
  unfold descriptionTailOmegaInputM descriptionTailOmegaInput
  rw [decodeSecond_pairCode, decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem descriptionTailOmegaInputCount_input (scode : BitString) (m count : ℕ) :
    descriptionTailOmegaInputCount (descriptionTailOmegaInput scode m count) = count := by
  unfold descriptionTailOmegaInputCount descriptionTailOmegaInput
  rw [decodeSecond_pairCode, decodeSecond_pairCode, bitsToNat_bits]

noncomputable def descriptionTailOmegaSelector
    (c : Code) : BitString →. BitString := fun z =>
  let S_code := descriptionTailOmegaInputSCode z
  let m := descriptionTailOmegaInputM z
  let count := descriptionTailOmegaInputCount z
  let S_list := (decodeDistributionData S_code).map CodedDistributionEntry.point
  (Nat.rfind (fun t => Part.some
    (S_list.all (fun y =>
      (boundedOutputStage c m t).elem y)))).bind fun t₀ =>
    Part.some (Nat.bits ((boundedOutputStage c m t₀).length + count))

theorem list_all_primrec
    {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).all (p a)) := by
  have heq :
      (fun a => (f a).all (p a)) =
        (fun a => (f a).foldr (fun b acc => p a b && acc) true) := by
    funext a
    induction f a with
    | nil => rfl
    | cons b t ih => simp [List.all_cons, ih]
  rw [heq]
  have hstep : Primrec₂
      (fun (a : α) (q : β × Bool) => p a q.1 && q.2) :=
    (Primrec.and.comp
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const true) hstep

theorem descriptionTailOmegaSelector_partrec
    (c : Code) :
    Partrec (descriptionTailOmegaSelector c) := by
  have hS_code : Primrec descriptionTailOmegaInputSCode :=
    decodeFirst_primrec'
  have hm : Primrec descriptionTailOmegaInputM :=
    bitsToNat_primrec.comp (decodeFirst_primrec'.comp decodeSecond_primrec')
  have hcount : Primrec descriptionTailOmegaInputCount :=
    bitsToNat_primrec.comp (decodeSecond_primrec'.comp decodeSecond_primrec')
  have hS_list : Primrec (fun z =>
      (decodeDistributionData
        (descriptionTailOmegaInputSCode z)).map
          CodedDistributionEntry.point) :=
    Primrec.list_map
      (decodeDistributionData_primrec.comp hS_code)
      (entry_point_primrec.comp Primrec.snd).to₂
  have h_m_t : Primrec (fun p : BitString × ℕ =>
      boundedOutputStage c
        (descriptionTailOmegaInputM p.1) p.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair (hm.comp Primrec.fst) Primrec.snd)
  have h_decide : Computable₂ (fun (z : BitString) (t : ℕ) =>
      (decodeDistributionData
        (descriptionTailOmegaInputSCode z)).map
          CodedDistributionEntry.point |>.all (fun y =>
            (boundedOutputStage c
              (descriptionTailOmegaInputM z) t).elem y)) := by
    have hpred : Primrec₂ (fun (q : BitString × ℕ) (y : BitString) =>
      decide (y ∈ boundedOutputStage c (descriptionTailOmegaInputM q.1) q.2)) :=
      (bitString_mem_primrec.comp Primrec.snd (h_m_t.comp Primrec.fst)).to₂
    have hall : Primrec (fun (q : BitString × ℕ) =>
        (decodeDistributionData
          (descriptionTailOmegaInputSCode q.1)).map
            CodedDistributionEntry.point |>.all (fun y =>
              decide (y ∈ boundedOutputStage c
                (descriptionTailOmegaInputM q.1) q.2))) :=
      list_all_primrec (hS_list.comp Primrec.fst) hpred
    have heq : ∀ (q : BitString × ℕ) (y : BitString),
        decide (y ∈ boundedOutputStage c
          (descriptionTailOmegaInputM q.1) q.2) =
        (boundedOutputStage c
          (descriptionTailOmegaInputM q.1) q.2).elem y := by
      intro q y
      simp only [List.elem_eq_mem]
    have hall2 : Primrec (fun (q : BitString × ℕ) =>
        (decodeDistributionData
          (descriptionTailOmegaInputSCode q.1)).map
            CodedDistributionEntry.point |>.all (fun y =>
              (boundedOutputStage c
                (descriptionTailOmegaInputM q.1) q.2).elem y)) := by
      exact hall.of_eq (fun q => by simp only [heq])
    exact hall2.to_comp.to₂
  have h_rfind : Partrec (fun z =>
      Nat.rfind (fun t => Part.some
        ((decodeDistributionData
          (descriptionTailOmegaInputSCode z)).map
            CodedDistributionEntry.point |>.all (fun y =>
              (boundedOutputStage c
                (descriptionTailOmegaInputM z) t).elem y)))) :=
    Partrec.rfind h_decide.partrec₂
  have h_len : Computable₂ (fun (z : BitString) (t : ℕ) =>
      (boundedOutputStage c
        (descriptionTailOmegaInputM z) t).length) :=
    Primrec.list_length.to_comp.comp₂ h_m_t.to_comp
  have h_res : Computable₂ (fun (z : BitString) (t : ℕ) =>
      Nat.bits ((boundedOutputStage c
        (descriptionTailOmegaInputM z) t).length +
          descriptionTailOmegaInputCount z)) :=
    natBitsComputable.comp₂
      (Primrec.nat_add.to_comp.comp₂ h_len
        (hcount.to_comp.comp Computable.fst).to₂)
  unfold descriptionTailOmegaSelector
  exact Partrec.bind h_rfind h_res.partrec₂

/-! ## Direction 2: the full dyadic block containing `x` -/

/-- For a present element, its zero-based first index plus the size of the
suffix beginning at that element is the length of the whole list. -/
theorem findIdx_add_suffixCountIncluding_eq_length
    {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    (L : List α) (x : α) (hx : x ∈ L) :
    L.findIdx (· == x) + suffixCountIncluding L x = L.length := by
  induction L with
  | nil => simp at hx
  | cons y ys ih =>
      by_cases hy : y = x
      · subst y
        rw [List.findIdx_cons]
        simp [suffixCountIncluding]
      · have hxys : x ∈ ys := by
          rw [List.mem_cons] at hx
          exact hx.resolve_left (Ne.symm hy)
        rw [List.findIdx_cons]
        have hbeq : (y == x) = false :=
          beq_eq_false_iff_ne.mpr hy
        rw [hbeq]
        unfold suffixCountIncluding
        rw [if_neg hy]
        change
          (ys.findIdx (· == x) + 1) + suffixCountIncluding ys x =
            ys.length + 1
        have hi := ih hxys
        omega

/-- Pure list form of the full-block observation used in direction 2.  If the
suffix beginning at `x` has at least `b` elements, then the consecutive
length-`b` block containing the first occurrence of `x` is complete. -/
theorem full_block_at_findIdx
    {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    (L : List α) (x : α) (b : ℕ)
    (hb : 0 < b) (hx : x ∈ L)
    (hbelow : b ≤ suffixCountIncluding L x) :
    x ∈ (L.drop ((L.findIdx (· == x) / b) * b)).take b ∧
      ((L.drop ((L.findIdx (· == x) / b) * b)).take b).length = b := by
  let idx := L.findIdx (· == x)
  let start := (idx / b) * b
  have hidx : idx < L.length := by
    dsimp [idx]
    rw [List.findIdx_lt_length]
    exact ⟨x, hx, by simp⟩
  have hstartLe : start ≤ idx := by
    dsimp [start]
    exact Nat.div_mul_le_self idx b
  have hidxLt : idx < start + b := by
    dsimp [start]
    nlinarith [Nat.div_add_mod idx b, Nat.mod_lt idx hb]
  have hlength :
      idx + suffixCountIncluding L x = L.length := by
    simpa [idx] using findIdx_add_suffixCountIncluding_eq_length L x hx
  have hblockEnd : start + b ≤ L.length := by
    rw [← hlength]
    omega
  have hblockLen :
      ((L.drop start).take b).length = b := by
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    omega
  refine ⟨?_, hblockLen⟩
  rw [List.mem_iff_getElem]
  let offset := idx - start
  have hoffset : offset < ((L.drop start).take b).length := by
    rw [hblockLen]
    dsimp [offset]
    omega
  refine ⟨offset, hoffset, ?_⟩
  simp only [List.getElem_take, List.getElem_drop]
  have hsum : start + offset = idx := by
    dsimp [offset]
    omega
  have hfound : L[idx] = x := eq_of_beq
    (List.findIdx_getElem (xs := L) (p := (· == x)))
  exact (getElem_congr rfl hsum _).trans hfound

/-- Index of the dyadic `2^j`-block containing `x` in the completed
bound-`m` list. -/
noncomputable def completedDyadicBlockIndex
    (c : Code) (m j : ℕ) (x : BitString) : ℕ :=
  (completedBoundedOutput c m).findIdx (· == x) / 2 ^ j

/-- The completed dyadic block containing `x`, kept as a list so that its
enumeration order and exact length remain visible. -/
noncomputable def completedDyadicBlockList
    (c : Code) (m j : ℕ) (x : BitString) : List BitString :=
  (completedBoundedOutput c m).drop
      (completedDyadicBlockIndex c m j x * 2 ^ j) |>.take (2 ^ j)

/-- Finset form of `completedDyadicBlockList`, used as the eventual
`InDescriptionProfile` witness. -/
noncomputable def completedDyadicBlock
    (c : Code) (m j : ℕ) (x : BitString) : Finset BitString :=
  (completedDyadicBlockList c m j x).toFinset

/-- A suffix of size at least `2^j` makes the dyadic block containing `x`
complete and ensures that it contains `x`. -/
theorem completedDyadicBlockList_mem_and_length
    (c : Code) (m j : ℕ) (x : BitString)
    (htail : 2 ^ j ≤ suffixCoordinate c m x) :
    x ∈ completedDyadicBlockList c m j x ∧
      (completedDyadicBlockList c m j x).length = 2 ^ j := by
  have hx : x ∈ completedBoundedOutput c m := by
    apply suffixCountIncluding_pos_iff_mem.mp
    simpa [suffixCoordinate] using
      (lt_of_lt_of_le (by positivity : 0 < 2 ^ j) htail)
  simpa only [completedDyadicBlockList, completedDyadicBlockIndex,
    suffixCoordinate, Nat.mul_comm] using
    full_block_at_findIdx (completedBoundedOutput c m) x (2 ^ j)
      (by positivity) hx htail

theorem mem_completedDyadicBlock
    (c : Code) (m j : ℕ) (x : BitString)
    (htail : 2 ^ j ≤ suffixCoordinate c m x) :
    x ∈ completedDyadicBlock c m j x := by
  rw [completedDyadicBlock, List.mem_toFinset]
  exact (completedDyadicBlockList_mem_and_length c m j x htail).1

theorem completedDyadicBlock_nonempty
    (c : Code) (m j : ℕ) (x : BitString)
    (htail : 2 ^ j ≤ suffixCoordinate c m x) :
    (completedDyadicBlock c m j x).Nonempty :=
  ⟨x, mem_completedDyadicBlock c m j x htail⟩

/-- The dyadic block has exactly `2^j` distinct elements. -/
theorem card_completedDyadicBlock
    (c : Code) (m j : ℕ) (x : BitString)
    (htail : 2 ^ j ≤ suffixCoordinate c m x) :
    (completedDyadicBlock c m j x).card = 2 ^ j := by
  rw [completedDyadicBlock, List.toFinset_card_of_nodup]
  · exact (completedDyadicBlockList_mem_and_length c m j x htail).2
  · unfold completedDyadicBlockList
    exact ((by
      unfold completedBoundedOutput
      exact boundedOutputStage_nodup c m (maxHaltingStage c m)) :
        (completedBoundedOutput c m).Nodup).drop.take

/-- In the bound-`i+j` list, every dyadic `2^j`-block index fits in `i+1`
bits.  This is the exact block-count estimate behind the complexity half of
direction 2. -/
theorem completedDyadicBlockIndex_lt_two_pow
    (c : Code) (i j : ℕ) (x : BitString) :
    completedDyadicBlockIndex c (i + j) j x < 2 ^ (i + 1) := by
  unfold completedDyadicBlockIndex
  apply Nat.div_lt_of_lt_mul
  calc
    (completedBoundedOutput c (i + j)).findIdx (· == x)
        ≤ (completedBoundedOutput c (i + j)).length :=
      List.findIdx_le_length
    _ = omegaCount c (i + j) := rfl
    _ < 2 ^ (i + j + 1) :=
      omegaCount_lt_two_pow_succ c (i + j)
    _ = 2 ^ j * 2 ^ (i + 1) := by
      rw [show i + j + 1 = (i + 1) + j by omega, pow_add,
        Nat.mul_comm]

/-! ## A uniform decoder for completed dyadic blocks -/

/-- Self-delimiting block parameters followed by an undoubled fixed-width
block index. -/
def completedDyadicBlockInput
    (m j blockIdx blockWidth : ℕ) : BitString :=
  pairCode (pairCode (Nat.bits m) (Nat.bits j))
    (fixedWidthNatCode blockIdx blockWidth)

def completedDyadicBlockInputM (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeFirst z))

def completedDyadicBlockInputJ (z : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeFirst z))

def completedDyadicBlockInputIndex (z : BitString) : ℕ :=
  decodeFixedWidthNatCode (decodeSecond z)

@[simp] theorem completedDyadicBlockInputM_input
    (m j blockIdx blockWidth : ℕ) :
    completedDyadicBlockInputM
      (completedDyadicBlockInput m j blockIdx blockWidth) = m := by
  unfold completedDyadicBlockInputM completedDyadicBlockInput
  rw [decodeFirst_pairCode, decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem completedDyadicBlockInputJ_input
    (m j blockIdx blockWidth : ℕ) :
    completedDyadicBlockInputJ
      (completedDyadicBlockInput m j blockIdx blockWidth) = j := by
  unfold completedDyadicBlockInputJ completedDyadicBlockInput
  rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem completedDyadicBlockInputIndex_input
    (m j blockIdx blockWidth : ℕ) :
    completedDyadicBlockInputIndex
      (completedDyadicBlockInput m j blockIdx blockWidth) = blockIdx := by
  unfold completedDyadicBlockInputIndex completedDyadicBlockInput
  rw [decodeSecond_pairCode, decodeFixedWidthNatCode_encode]

theorem completedDyadicBlockInput_length
    {m j blockIdx blockWidth : ℕ}
    (hidx : blockIdx < 2 ^ blockWidth) :
    (completedDyadicBlockInput m j blockIdx blockWidth).length =
      blockWidth + 4 * (Nat.bits m).length +
        2 * (Nat.bits j).length + 3 := by
  unfold completedDyadicBlockInput
  rw [length_pairCode, length_pairCode,
    fixedWidthNatCode_length hidx]
  omega

/-- Given `(m,j,blockIdx)`, wait until the requested full `2^j`-block has
appeared and return its canonical uniform-set code.  Malformed inputs may
diverge; all parameters remain explicit inputs to one fixed partial-recursive
map. -/
noncomputable def completedDyadicBlockSelector
    (c : Code) : BitString →. BitString := fun z =>
  (Nat.rfind (fun t => Part.some (decide
    ((completedDyadicBlockInputIndex z + 1) *
        2 ^ completedDyadicBlockInputJ z ≤
      (boundedOutputStage c
        (completedDyadicBlockInputM z) t).length)))).bind
    (fun t => Part.some
      (canonicalUniformCodeOfList
        (canonicalFinsetList
          (((boundedOutputStage c
              (completedDyadicBlockInputM z) t).drop
                (completedDyadicBlockInputIndex z *
                  2 ^ completedDyadicBlockInputJ z) |>.take
                    (2 ^ completedDyadicBlockInputJ z)).toFinset))))

theorem completedDyadicBlockSelector_partrec
    (c : Code) :
    Partrec (completedDyadicBlockSelector c) := by
  have hm : Primrec completedDyadicBlockInputM :=
    bitsToNat_primrec.comp
      (decodeFirst_primrec'.comp decodeFirst_primrec')
  have hj : Primrec completedDyadicBlockInputJ :=
    bitsToNat_primrec.comp
      (decodeSecond_primrec'.comp decodeFirst_primrec')
  have hidx : Primrec completedDyadicBlockInputIndex :=
    decodeFixedWidthNatCode_primrec.comp decodeSecond_primrec'
  have hm' : Primrec (fun q : BitString × ℕ =>
      completedDyadicBlockInputM q.1) :=
    hm.comp Primrec.fst
  have hj' : Primrec (fun q : BitString × ℕ =>
      completedDyadicBlockInputJ q.1) :=
    hj.comp Primrec.fst
  have hidx' : Primrec (fun q : BitString × ℕ =>
      completedDyadicBlockInputIndex q.1) :=
    hidx.comp Primrec.fst
  have hpow : Primrec (fun q : BitString × ℕ =>
      2 ^ completedDyadicBlockInputJ q.1) :=
    Kolmogorov.CodedFiniteDistribution.twoPow_primrec.comp hj'
  have hend : Primrec (fun q : BitString × ℕ =>
      (completedDyadicBlockInputIndex q.1 + 1) *
        2 ^ completedDyadicBlockInputJ q.1) :=
    Primrec.nat_mul.comp
      (Primrec.nat_add.comp hidx' (Primrec.const 1)) hpow
  have hstage : Primrec (fun q : BitString × ℕ =>
      boundedOutputStage c
        (completedDyadicBlockInputM q.1) q.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair hm' Primrec.snd)
  have hcheck : Computable₂ (fun (z : BitString) (t : ℕ) =>
      decide
        ((completedDyadicBlockInputIndex z + 1) *
            2 ^ completedDyadicBlockInputJ z ≤
          (boundedOutputStage c
            (completedDyadicBlockInputM z) t).length)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp hend
        (Primrec.list_length.comp hstage))).to_comp.to₂
  have hsearch : Partrec (fun z : BitString =>
      Nat.rfind (fun t => Part.some (decide
        ((completedDyadicBlockInputIndex z + 1) *
            2 ^ completedDyadicBlockInputJ z ≤
          (boundedOutputStage c
            (completedDyadicBlockInputM z) t).length)))) :=
    Partrec.rfind hcheck.partrec₂
  have hstart : Primrec (fun q : BitString × ℕ =>
      completedDyadicBlockInputIndex q.1 *
        2 ^ completedDyadicBlockInputJ q.1) :=
    Primrec.nat_mul.comp hidx' hpow
  have hblock : Primrec (fun q : BitString × ℕ =>
      (boundedOutputStage c
        (completedDyadicBlockInputM q.1) q.2).drop
          (completedDyadicBlockInputIndex q.1 *
            2 ^ completedDyadicBlockInputJ q.1) |>.take
              (2 ^ completedDyadicBlockInputJ q.1)) :=
    Primrec.list_take.comp
      hpow (Primrec.list_drop.comp hstart hstage)
  have hcode : Computable₂ (fun (z : BitString) (t : ℕ) =>
      canonicalUniformCodeOfList
        (canonicalFinsetList
          (((boundedOutputStage c
              (completedDyadicBlockInputM z) t).drop
                (completedDyadicBlockInputIndex z *
                  2 ^ completedDyadicBlockInputJ z) |>.take
                    (2 ^ completedDyadicBlockInputJ z)).toFinset))) :=
    (canonicalUniformCodeOfList_primrec.comp
      (canonicalFinsetList_toFinset_primrec.comp hblock)).to_comp.to₂
  unfold completedDyadicBlockSelector
  exact (Partrec.bind hsearch hcode.partrec₂).of_eq (fun _ => rfl)

/-- The uniform decoder returns the canonical code of the completed block
containing `x` whenever the suffix hypothesis makes that block full. -/
theorem completedDyadicBlockSelector_recovers
    (c : Code) (i j : ℕ) (x : BitString)
    (htail : 2 ^ j ≤ suffixCoordinate c (i + j) x) :
    (codedUniformOn
      (completedDyadicBlock c (i + j) j x)
      (completedDyadicBlock_nonempty c (i + j) j x htail)).code ∈
        completedDyadicBlockSelector c
          (completedDyadicBlockInput (i + j) j
            (completedDyadicBlockIndex c (i + j) j x) (i + 1)) := by
  let blockIdx := completedDyadicBlockIndex c (i + j) j x
  let blockSize := 2 ^ j
  let blockEnd := (blockIdx + 1) * blockSize
  have hidx : blockIdx < 2 ^ (i + 1) :=
    completedDyadicBlockIndex_lt_two_pow c i j x
  have hblockLength :
      (completedDyadicBlockList c (i + j) j x).length = blockSize := by
    simpa [blockSize] using
      (completedDyadicBlockList_mem_and_length c (i + j) j x htail).2
  have hblockEnd :
      blockEnd ≤ (completedBoundedOutput c (i + j)).length := by
    have htake :
        (((completedBoundedOutput c (i + j)).drop
            (blockIdx * blockSize)).take blockSize).length =
          blockSize := by
      simpa [completedDyadicBlockList, blockIdx, blockSize] using hblockLength
    simp only [List.length_take, List.length_drop] at htake
    have hle :
        blockSize ≤
          (completedBoundedOutput c (i + j)).length -
            blockIdx * blockSize :=
      min_eq_left_iff.mp htake
    have hend :
        (blockIdx + 1) * blockSize =
          blockIdx * blockSize + blockSize := by ring
    have hbpos : 0 < blockSize := by
      dsimp [blockSize]
      positivity
    dsimp [blockEnd]
    rw [hend]
    omega
  let completeTime := boundedOutputCompletionTime c (i + j)
  have hex :
      ∃ t, blockEnd ≤ (boundedOutputStage c (i + j) t).length := by
    refine ⟨completeTime, ?_⟩
    rw [boundedOutputStage_eq_completed_at_completion]
    exact hblockEnd
  let t₀ := Nat.find hex
  have ht₀ :
      t₀ ∈ Nat.rfind (fun t => Part.some
        (decide (blockEnd ≤
          (boundedOutputStage c (i + j) t).length))) := by
    rw [Nat.mem_rfind]
    refine ⟨by simpa using Nat.find_spec hex, ?_⟩
    intro t ht
    simpa using Nat.find_min hex ht
  have hprefix :
      boundedOutputStage c (i + j) t₀ <+:
        completedBoundedOutput c (i + j) :=
    boundedOutputStage_prefix_completed c (i + j) t₀
  obtain ⟨rest, hrest⟩ := hprefix
  have ht₀len :
      blockEnd ≤ (boundedOutputStage c (i + j) t₀).length :=
    Nat.find_spec hex
  have htake :
      (boundedOutputStage c (i + j) t₀).take blockEnd =
        (completedBoundedOutput c (i + j)).take blockEnd := by
    rw [← hrest, List.take_append_of_le_length ht₀len]
  have hblockEndEq :
      blockIdx * blockSize + blockSize = blockEnd := by
    dsimp [blockEnd]
    ring
  have hblockEq :
      ((boundedOutputStage c (i + j) t₀).drop
          (blockIdx * blockSize)).take blockSize =
        completedDyadicBlockList c (i + j) j x := by
    unfold completedDyadicBlockList
    rw [show completedDyadicBlockIndex c (i + j) j x = blockIdx from rfl,
      show 2 ^ j = blockSize from rfl]
    rw [List.take_drop, List.take_drop, hblockEndEq, htake]
  let z := completedDyadicBlockInput (i + j) j blockIdx (i + 1)
  have ht₀' :
      t₀ ∈ Nat.rfind (fun t => Part.some (decide
        ((completedDyadicBlockInputIndex z + 1) *
            2 ^ completedDyadicBlockInputJ z ≤
          (boundedOutputStage c
            (completedDyadicBlockInputM z) t).length))) := by
    simpa [z, blockEnd, blockSize] using ht₀
  unfold completedDyadicBlockSelector
  rw [Part.mem_bind_iff]
  refine ⟨t₀, ht₀', ?_⟩
  simp only [completedDyadicBlockInputM_input,
    completedDyadicBlockInputJ_input,
    completedDyadicBlockInputIndex_input]
  rw [show completedDyadicBlockIndex c (i + j) j x = blockIdx from rfl,
    show 2 ^ j = blockSize from rfl, hblockEq]
  have hcanonical :
      canonicalUniformCodeOfList
          (canonicalFinsetList
            (completedDyadicBlockList c (i + j) j x).toFinset) =
        (codedUniformOn
          (completedDyadicBlock c (i + j) j x)
          (completedDyadicBlock_nonempty c (i + j) j x htail)).code := by
    exact canonicalUniformCodeOfList_canonicalFinsetList
      (completedDyadicBlock c (i + j) j x)
      (completedDyadicBlock_nonempty c (i + j) j x htail)
  rw [hcanonical]
  exact Part.mem_some _

/-- **Coding core of B6 direction 2.** The set-complexity of the completed
dyadic block containing `x` in the bound-`i+j` list is at most `i+O(log(i+j))`.
The block index uses `i+1` bits and the decoder header contributes only
logarithmic overhead.  Isolated so that both the existential profile endpoint
and the concrete chopped-block description (`chopped_standard_blocks`) share the
single coding argument. -/
theorem setComplexity_completedDyadicBlock_le
    (U : Map) (hU : IsOptimalPrefixConditional U) (c : Code) :
    ∃ C : ℕ, ∀ (x : BitString) (i j : ℕ)
      (htail : 2 ^ j ≤ suffixCoordinate c (i + j) x),
      setComplexity U (completedDyadicBlock c (i + j) j x)
          (completedDyadicBlock_nonempty c (i + j) j x htail) ≤
        ((i + logSlack C (i + j) : ℕ) : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    KPPlain_partrec_map_le U hU
      (completedDyadicBlockSelector c)
      (completedDyadicBlockSelector_partrec c)
  obtain ⟨Clen, hlen⟩ := KPPlain_le_length_add_log U hU
  let C := Clen + Cmap + 12
  refine ⟨C, fun x i j htail => ?_⟩
  let A := completedDyadicBlock c (i + j) j x
  let hA : A.Nonempty :=
    completedDyadicBlock_nonempty c (i + j) j x htail
  let blockIdx := completedDyadicBlockIndex c (i + j) j x
  let input :=
    completedDyadicBlockInput (i + j) j blockIdx (i + 1)
  have hidx : blockIdx < 2 ^ (i + 1) :=
    completedDyadicBlockIndex_lt_two_pow c i j x
  have hinputLength :
      input.length =
        i + 1 + 4 * (Nat.bits (i + j)).length +
          2 * (Nat.bits j).length + 3 := by
    simpa [input, blockIdx] using
      completedDyadicBlockInput_length hidx
  have hselector :
      (codedUniformOn A hA).code ∈
        completedDyadicBlockSelector c input := by
    simpa [A, hA, blockIdx, input] using
      completedDyadicBlockSelector_recovers c i j x htail
  let M := i + j
  let L := (Nat.bits M).length
  have hjBits : (Nat.bits j).length ≤ L := by
    dsimp [L, M]
    exact length_natBits_mono (Nat.le_add_left j i)
  have hiM : i ≤ M := by
    dsimp [M]
    omega
  have hinputLinear : input.length ≤ i + 6 * L + 4 := by
    rw [hinputLength]
    rw [show (Nat.bits (i + j)).length = L from rfl]
    omega
  have hMpow : M < 2 ^ L := by
    simpa [L] using lt_two_pow_length_natBits M
  have hLpow : L ≤ 2 ^ L := by
    exact Nat.recOn L (by norm_num) fun n ihn => by
      rw [pow_succ']
      linarith [Nat.one_le_pow n 2 zero_lt_two]
  have hinputPow : input.length < 2 ^ (L + 4) := by
    have hlin : input.length ≤ M + 6 * L + 4 :=
      hinputLinear.trans (by omega)
    have hpow : (2 : ℕ) ^ (L + 4) = 16 * 2 ^ L := by rw [pow_add]; ring
    rw [hpow]
    omega
  have hinputBits :
      (Nat.bits input.length).length ≤ L + 4 :=
    length_natBits_lt_pow hinputPow
  have hbudget :
      input.length + 2 * (Nat.bits input.length).length +
          Clen + Cmap ≤
        i + logSlack C M := by
    have hC : C = Clen + Cmap + 12 := rfl
    have hCL : 8 * L ≤ C * L := Nat.mul_le_mul_right L (by omega)
    change input.length + 2 * (Nat.bits input.length).length + Clen + Cmap ≤
        i + (C * L + C)
    omega
  change setComplexity U A hA ≤ ((i + logSlack C (i + j) : ℕ) : ENat)
  unfold setComplexity
  calc
    KPPlain U (codedUniformOn A hA).code
        ≤ KPPlain U input + (Cmap : ENat) :=
      hmap input _ hselector
    _ ≤ (input.length : ENat) +
          2 * (Nat.bits input.length).length +
          (Clen : ENat) + (Cmap : ENat) := by
      have h := hlen input
      exact add_le_add h le_rfl
    _ = ((input.length +
          2 * (Nat.bits input.length).length +
          Clen + Cmap : ℕ) : ENat) := by
      push_cast
      ring
    _ ≤ ((i + logSlack C M : ℕ) : ENat) := by
      exact_mod_cast hbudget
    _ = ((i + logSlack C (i + j) : ℕ) : ENat) := rfl

/-- **B6 direction 2.** A dyadic suffix of size at least `2^j` in the
bound-`i+j` list yields an `(i+O(log(i+j)),j)` description.  The witness is the
full dyadic block containing `x`; its index uses `i+1` bits, while the decoder
header contributes only logarithmic overhead. -/
theorem inDescriptionProfile_of_suffixCoordinate
    (U : Map) (hU : IsOptimalPrefixConditional U) (c : Code) :
    ∃ C : ℕ, ∀ (x : BitString) (i j : ℕ),
      2 ^ j ≤ suffixCoordinate c (i + j) x →
      InDescriptionProfile U x (i + logSlack C (i + j)) j := by
  obtain ⟨C, hC⟩ := setComplexity_completedDyadicBlock_le U hU c
  refine ⟨C, fun x i j htail => ?_⟩
  exact ⟨completedDyadicBlock c (i + j) j x,
    completedDyadicBlock_nonempty c (i + j) j x htail,
    mem_completedDyadicBlock c (i + j) j x htail,
    hC x i j htail,
    le_of_eq (card_completedDyadicBlock c (i + j) j x htail)⟩

/-- The strict tail is zero when the queried element is absent. -/
theorem tailAfter_eq_zero_of_not_mem
    {α : Type*} [DecidableEq α] {L : List α} {x : α}
    (hx : x ∉ L) :
    tailAfter L x = 0 := by
  induction L with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.mem_cons, not_or] at hx
      unfold tailAfter
      rw [if_neg (Ne.symm hx.1)]
      exact ih hx.2

/-- Source-facing converse direction, stated using the number of elements
strictly following `x`.  Restricting `i+j ≤ n` turns the decoder's
`O(log(i+j))` header into the advertised uniform `O(log n)` slack. -/
theorem tail_characterization_reverse
    (V U : Map) (_hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (_hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (n i j : ℕ),
      x.length = n →
      i + j ≤ n →
      2 ^ j ≤ tailAfter (completedBoundedOutput c (i + j)) x →
      InDescriptionProfile U x (i + logSlack C n) j := by
  obtain ⟨C, hC⟩ :=
    inDescriptionProfile_of_suffixCoordinate U hU c
  refine ⟨C, fun x n i j _hn hmn htail => ?_⟩
  have htailPos :
      0 < tailAfter (completedBoundedOutput c (i + j)) x :=
    lt_of_lt_of_le (by positivity) htail
  have hx :
      x ∈ completedBoundedOutput c (i + j) := by
    by_contra hx
    have hzero := tailAfter_eq_zero_of_not_mem hx
    omega
  have hsuffix :
      2 ^ j ≤ suffixCoordinate c (i + j) x := by
    unfold suffixCoordinate
    rw [suffixCountIncluding_eq_tailAfter_add_one hx]
    omega
  exact (hC x i j hsuffix).mono_i
    (Nat.add_le_add_left (logSlack_mono_right C hmn) i)

theorem descriptionTailOmegaSelector_recovers
    (c : Code) (m : ℕ)
    (S_code : BitString) (S_list : List BitString)
    (hS_list : S_list = (decodeDistributionData S_code).map CodedDistributionEntry.point)
    (_hS_subset : ∀ y ∈ S_list, y ∈ completedBoundedOutput c m)
    (count : ℕ)
    (hcount : ∃ t₀,
      Part.some t₀ = Nat.rfind (fun t => Part.some
        (S_list.all (fun y =>
          (boundedOutputStage c m t).elem y))) ∧
      count = omegaCount c m - (boundedOutputStage c m t₀).length) :
    descriptionTailOmegaSelector c (descriptionTailOmegaInput S_code m count) =
      Part.some (Nat.bits (omegaCount c m)) := by
  unfold descriptionTailOmegaSelector
  unfold descriptionTailOmegaInputSCode descriptionTailOmegaInputM descriptionTailOmegaInputCount
  unfold descriptionTailOmegaInput
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode, decodeSecond_pairCode]
  rw [bitsToNat_bits, bitsToNat_bits]
  dsimp only
  rw [← hS_list]
  obtain ⟨t₀, ht₀, hcount_eq⟩ := hcount
  rw [← ht₀]
  rw [Part.bind_some]
  apply congrArg Part.some
  apply congrArg Nat.bits
  rw [hcount_eq]
  have hpre : boundedOutputStage c m t₀ <+: completedBoundedOutput c m :=
    boundedOutputStage_prefix_completed c m t₀
  have hle : (boundedOutputStage c m t₀).length ≤ omegaCount c m := by
    change (boundedOutputStage c m t₀).length ≤ (completedBoundedOutput c m).length
    exact List.IsPrefix.length_le hpre
  omega

theorem tail_characterization_forward
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (n i j : ℕ),
      x.length = n →
      i + j ≤ n →
      InDescriptionProfile U x i j →
      2 ^ j ≤ suffixCoordinate c (i + j + logSlack C n) x := by
  obtain ⟨C_mem, hC_mem⟩ := mem_completed_of_isIJDescription V U hV hU c hc
  obtain ⟨C_omega, hC_omega⟩ := plainKNat_omegaCount_lower V hV c hc
  obtain ⟨C_map, hC_map⟩ := plainK_partrec_map_le V hV
    (descriptionTailOmegaSelector c)
    (descriptionTailOmegaSelector_partrec c)
  obtain ⟨C_pair, hC_pair⟩ := plainK_pair_le_KPPlain_add_KPPlain V U hV hU
  obtain ⟨C_len, hC_len⟩ := KPPlain_le_length_add_log U hU
  let K := C_mem + C_omega + C_map + C_pair + C_len + 64
  let C := 2 ^ (K + 10)
  refine ⟨C, fun x n i j _hn hij hprof => ?_⟩
  obtain ⟨S, hS, hdesc⟩ := hprof
  let S_code := (codedUniformOn S hS).code
  let S_list := canonicalFinsetList S
  let m := i + j + logSlack C n
  have hCmemC : C_mem ≤ C := by
    have hCK : C_mem ≤ K := by
      dsimp [K]
      omega
    have hKpow : K ≤ 2 ^ K := by
      exact Nat.recOn K (by norm_num) fun q hq => by
        rw [pow_succ']
        linarith [Nat.one_le_pow q 2 zero_lt_two]
    have hpow :
        2 ^ K ≤ 2 ^ (K + 10) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right K 10)
    exact hCK.trans (hKpow.trans (by simpa [C] using hpow))
  have hjn : j ≤ n := by omega
  have hmemBudget :
      i + j + logSlack C_mem j ≤ m := by
    dsimp [m]
    have hslack :
        logSlack C_mem j ≤ logSlack C n :=
      (logSlack_mono_left hCmemC j).trans
        (logSlack_mono_right C hjn)
    omega
  have hSsubset :
      ∀ y ∈ S_list, y ∈ completedBoundedOutput c m := by
    intro y hy
    have hyS : y ∈ S := by
      simpa [S_list] using hy
    have hySmall :
        y ∈ completedBoundedOutput c
          (i + j + logSlack C_mem j) :=
      hC_mem x y i j S hS hdesc hyS
    have hyK :
        plainK V y ≤
          ((i + j + logSlack C_mem j : ℕ) : ENat) :=
      (mem_completedBoundedOutput_iff_plainK_le hc _ y).mp hySmall
    exact (mem_completedBoundedOutput_iff_plainK_le hc m y).mpr
      (hyK.trans (by exact_mod_cast hmemBudget))
  have hcover :
      ∃ t, S_list.all
        (fun y => (boundedOutputStage c m t).elem y) = true := by
    obtain ⟨t, ht⟩ :=
      exists_stage_covering_finset c m S (fun y hy =>
        hSsubset y (mem_canonicalFinsetList.mpr hy))
    refine ⟨t, ?_⟩
    rw [List.all_eq_true]
    intro y hy
    rw [List.elem_eq_mem]
    exact decide_eq_true (ht y (mem_canonicalFinsetList.mp hy))
  by_contra htail
  push Not at htail
  let t₀ := Nat.find hcover
  have ht₀spec :
      S_list.all
        (fun y => (boundedOutputStage c m t₀).elem y) = true :=
    Nat.find_spec hcover
  have ht₀mem :
      t₀ ∈ Nat.rfind (fun t => Part.some
        (S_list.all
          (fun y => (boundedOutputStage c m t).elem y))) := by
    rw [Nat.mem_rfind]
    refine ⟨by simpa using ht₀spec, ?_⟩
    intro t ht
    have hnot := Nat.find_min hcover ht
    simpa using hnot
  have hxList : x ∈ S_list := by
    exact mem_canonicalFinsetList.mpr hdesc.1
  have hxStage : x ∈ boundedOutputStage c m t₀ := by
    rw [List.all_eq_true] at ht₀spec
    have hxElem := ht₀spec x hxList
    simpa [List.elem_eq_mem] using hxElem
  have hprefix :
      boundedOutputStage c m t₀ <+:
        completedBoundedOutput c m :=
    boundedOutputStage_prefix_completed c m t₀
  obtain ⟨R, hR, hRtail⟩ :=
    prefix_remainder_length_le_tailAfter hprefix hxStage
  let count :=
    omegaCount c m - (boundedOutputStage c m t₀).length
  have hcountR : count = R.length := by
    dsimp [count, omegaCount]
    rw [hR, List.length_append]
    omega
  have hcountLt : count < 2 ^ j := by
    have htailLe :
        tailAfter (completedBoundedOutput c m) x <
          suffixCoordinate c m x := by
      have hxCompleted : x ∈ completedBoundedOutput c m :=
        List.IsPrefix.subset hprefix hxStage
      unfold suffixCoordinate
      rw [suffixCountIncluding_eq_tailAfter_add_one hxCompleted]
      omega
    rw [hcountR]
    exact lt_of_le_of_lt hRtail (htailLe.trans htail)
  have hrecover :
      descriptionTailOmegaSelector c
          (descriptionTailOmegaInput S_code m count) =
        Part.some (Nat.bits (omegaCount c m)) := by
    apply descriptionTailOmegaSelector_recovers
        c m S_code S_list
    · exact (dataPoints_codedUniformOn S hS).symm
    · exact hSsubset
    · exact ⟨t₀, (Part.eq_some_iff.mpr ht₀mem).symm, rfl⟩
  have hselector :
      Nat.bits (omegaCount c m) ∈
        descriptionTailOmegaSelector c
          (descriptionTailOmegaInput S_code m count) :=
    Part.eq_some_iff.mp hrecover
  let payload := pairCode (Nat.bits m) (Nat.bits count)
  let input := descriptionTailOmegaInput S_code m count
  have hinput :
      input = pairCode S_code payload := by
    rfl
  have hcountBits :
      (Nat.bits count).length ≤ j :=
    length_natBits_lt_pow hcountLt
  let L := (Nat.bits n).length
  let LC := (Nat.bits C).length
  have hijBits :
      (Nat.bits (i + j)).length ≤ L := by
    dsimp [L]
    exact length_natBits_mono hij
  have hslackBits :
      (Nat.bits (logSlack C n)).length ≤ L + LC + 1 := by
    simpa [L, LC] using length_natBits_logSlack_le C n
  have hmBits :
      (Nat.bits m).length ≤ 2 * L + LC + 2 := by
    dsimp [m]
    calc
      (Nat.bits (i + j + logSlack C n)).length
          ≤ (Nat.bits (i + j)).length +
              (Nat.bits (logSlack C n)).length + 1 :=
        length_natBits_add_le (i + j) (logSlack C n)
      _ ≤ 2 * L + LC + 2 := by omega
  have hpayloadLength :
      payload.length =
        2 * (Nat.bits m).length +
          (Nat.bits count).length + 1 := by
    dsimp [payload]
    rw [length_pairCode]
    omega
  have hpayloadLinear :
      payload.length ≤ j + 4 * L + 2 * LC + 5 := by
    rw [hpayloadLength]
    omega
  have hnPow : n < 2 ^ L := by
    simpa [L] using lt_two_pow_length_natBits n
  have hLPow : L ≤ 2 ^ L := by
    exact Nat.recOn L (by norm_num) fun q hq => by
      rw [pow_succ']
      linarith [Nat.one_le_pow q 2 zero_lt_two]
  have hLCPow : LC ≤ 2 ^ LC := by
    exact Nat.recOn LC (by norm_num) fun q hq => by
      rw [pow_succ']
      linarith [Nat.one_le_pow q 2 zero_lt_two]
  have hpayloadPow :
      payload.length < 2 ^ (L + LC + 6) := by
    rw [show L + LC + 6 = L + LC + 6 by rfl, pow_add, pow_add]
    have hjPow : j < 2 ^ L := lt_of_le_of_lt hjn hnPow
    let P := 2 ^ L * 2 ^ LC
    have hLP : 2 ^ L ≤ P := by
      dsimp [P]
      calc
        2 ^ L = 2 ^ L * 1 := by rw [mul_one]
        _ ≤ 2 ^ L * 2 ^ LC := by
          gcongr
          exact Nat.one_le_pow LC 2 zero_lt_two
    have hLCP : 2 ^ LC ≤ P := by
      dsimp [P]
      calc
        2 ^ LC = 1 * 2 ^ LC := by rw [one_mul]
        _ ≤ 2 ^ L * 2 ^ LC := by
          gcongr
          exact Nat.one_le_pow L 2 zero_lt_two
    have hPpos : 0 < P := by
      dsimp [P]
      positivity
    calc
      payload.length
          ≤ j + 4 * L + 2 * LC + 5 := hpayloadLinear
      _ < 12 * P := by
        have hOneP : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr hPpos.ne'
        omega
      _ < P * 2 ^ 6 := by
        rw [show 12 * P = P * 12 by ring]
        exact Nat.mul_lt_mul_of_pos_left (by norm_num) hPpos
      _ = 2 ^ L * 2 ^ LC * 2 ^ 6 := rfl
  have hpayloadBits :
      (Nat.bits payload.length).length ≤ L + LC + 6 :=
    length_natBits_lt_pow hpayloadPow
  have hcodeComplexity :
      KPPlain U S_code ≤ (i : ENat) := by
    simpa [S_code, setComplexity] using hdesc.2.1
  have hpayloadComplexity :
      KPPlain U payload ≤
        ((payload.length +
          2 * (Nat.bits payload.length).length + C_len : ℕ) : ENat) := by
    calc
      KPPlain U payload
          ≤ (payload.length : ENat) +
              2 * (Nat.bits payload.length).length +
                (C_len : ENat) :=
        hC_len payload
      _ = ((payload.length +
          2 * (Nat.bits payload.length).length + C_len : ℕ) : ENat) := by
        push_cast
        ring
  have hmENat :
      (m : ENat) ≤
        ((i + payload.length +
          2 * (Nat.bits payload.length).length +
            C_len + C_pair + C_map + C_omega : ℕ) : ENat) := by
    calc
      (m : ENat)
          ≤ plainKNat V (omegaCount c m) + (C_omega : ENat) :=
        hC_omega m
      _ ≤ (plainK V input + (C_map : ENat)) +
          (C_omega : ENat) := by
        gcongr
        exact hC_map input _ (by simpa [input] using hselector)
      _ ≤ ((KPPlain U S_code + KPPlain U payload +
          (C_pair : ENat)) + (C_map : ENat)) +
            (C_omega : ENat) := by
        gcongr
        rw [hinput]
        exact hC_pair S_code payload
      _ ≤ (((i : ENat) +
          ((payload.length +
            2 * (Nat.bits payload.length).length + C_len : ℕ) : ENat) +
              (C_pair : ENat)) + (C_map : ENat)) +
                (C_omega : ENat) := by
        gcongr
      _ = ((i + payload.length +
          2 * (Nat.bits payload.length).length +
            C_len + C_pair + C_map + C_omega : ℕ) : ENat) := by
        push_cast
        ring
  have hmNat :
      m ≤ i + payload.length +
        2 * (Nat.bits payload.length).length +
          C_len + C_pair + C_map + C_omega := by
    exact_mod_cast hmENat
  have hraw :
      m ≤ i + j + 6 * L + 4 * LC + 17 +
        C_len + C_pair + C_map + C_omega := by
    omega
  have hCbits : LC ≤ K + 11 := by
    apply length_natBits_lt_pow
    dsimp [LC, C]
    exact (Nat.pow_lt_pow_iff_right
      (by norm_num : 1 < 2)).mpr (by omega)
  have hCseven : 7 ≤ C := by
    dsimp [C]
    exact le_trans (by norm_num : 7 ≤ 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 10 K))
  have hKpow : K ≤ 2 ^ K := by
    exact Nat.recOn K (by norm_num) fun q hq => by
      rw [pow_succ']
      linarith [Nat.one_le_pow q 2 zero_lt_two]
  have hCconstant : 5 * K + 61 < C := by
    dsimp [C]
    rw [pow_add]
    have hpowOne : 1 ≤ 2 ^ K :=
      Nat.one_le_pow K 2 zero_lt_two
    have hsmall : 5 * K + 61 ≤ 66 * 2 ^ K := by
      omega
    calc
      5 * K + 61 ≤ 66 * 2 ^ K := hsmall
      _ < 2 ^ K * 2 ^ 10 := by
        rw [show 66 * 2 ^ K = 2 ^ K * 66 by ring]
        exact Nat.mul_lt_mul_of_pos_left (by norm_num) (by positivity)
  have hlarge :
      6 * L + 4 * LC + 17 +
          C_len + C_pair + C_map + C_omega <
        logSlack C n := by
    have hmul :
        7 * L ≤ C * L :=
      Nat.mul_le_mul_right L hCseven
    have hconst :
        4 * LC + 17 +
            C_len + C_pair + C_map + C_omega ≤
          5 * K + 61 := by
      dsimp [K] at *
      omega
    dsimp [logSlack, L]
    dsimp [L] at hmul
    omega
  dsimp [m] at hraw
  omega

/-- **VS40 `thm:tail-characterization` (B6).**  On the source-relevant range
`i+j ≤ n`, the ordinary description profile and the suffix position in the
plain bounded-complexity list determine one another up to uniform logarithmic
coordinate shifts.

The two constants are fixed before all strings and parameters.  They are kept
separate because the forward direction changes the plain-list budget, whereas
the reverse direction changes the prefix-profile complexity coordinate; taking
a post-hoc maximum would require a false monotonicity claim about enumeration
positions. -/
theorem tail_characterization
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C_forward C_reverse : ℕ,
      ∀ (x : BitString) (n i j : ℕ),
        x.length = n →
        i + j ≤ n →
        (InDescriptionProfile U x i j →
          2 ^ j ≤
            suffixCoordinate c
              (i + j + logSlack C_forward n) x) ∧
        (2 ^ j ≤
            tailAfter (completedBoundedOutput c (i + j)) x →
          InDescriptionProfile U x
            (i + logSlack C_reverse n) j) := by
  obtain ⟨C_forward, hforward⟩ :=
    tail_characterization_forward V U hV hU c hc
  obtain ⟨C_reverse, hreverse⟩ :=
    tail_characterization_reverse V U hV hU c hc
  exact ⟨C_forward, C_reverse, fun x n i j hn hij =>
    ⟨hforward x n i j hn hij, hreverse x n i j hn hij⟩⟩

end Kolmogorov
