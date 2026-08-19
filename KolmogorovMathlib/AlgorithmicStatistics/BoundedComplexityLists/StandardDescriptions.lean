import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.TailCharacterization

/-!
# VS40 Section 4, Milestone B7: standard descriptions

The completed bound-`m` list has length `omegaCount c m`.  Its standard
decomposition is the binary decomposition of that length: when bit `j` is set,
the corresponding block starts after all blocks belonging to higher bits and
has size `2^j`.  This is distinct from the arbitrary aligned dyadic blocks used
in the reverse direction of `tail_characterization`; those are the chopped
standard blocks.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- If the suffix including `x` contains a full block of size `2^(j+1)`, then
at least `2^j` elements occur strictly after `x`. -/
theorem pow_le_tailAfter_of_pow_succ_le_suffixCoordinate
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ completedBoundedOutput c m)
    (h : 2 ^ (j + 1) ≤ suffixCoordinate c m x) :
    2 ^ j ≤ tailAfter (completedBoundedOutput c m) x := by
  have h1 : suffixCountIncluding (completedBoundedOutput c m) x =
      tailAfter (completedBoundedOutput c m) x + 1 :=
    suffixCountIncluding_eq_tailAfter_add_one hx
  have h2 : suffixCoordinate c m x =
      tailAfter (completedBoundedOutput c m) x + 1 := by
    exact h1.symm ▸ rfl
  rw [h2] at h
  omega

/-- The source-standard `2^j` block in the binary decomposition of the
completed bound-`m` list.  It is empty when bit `j` of `omegaCount c m` is not
set.  The `x` argument records which object this block is intended to describe;
membership is required by the public propositions below. -/
noncomputable def standardBlock
    (c : Code) (m j : ℕ) (_x : BitString) : Finset BitString :=
  if (omegaCount c m).testBit j then
    (((completedBoundedOutput c m).drop
      ((omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1))).take
        (2 ^ j)).toFinset
  else ∅

/-- Membership in a standard block certifies that the corresponding binary bit
of `omegaCount` is set. -/
theorem standardBlock_testBit_of_mem
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    (omegaCount c m).testBit j = true := by
  unfold standardBlock at hx
  split at hx
  · assumption
  · simp at hx

/-- A set binary bit guarantees that the corresponding source-standard block
fits completely inside the list length. -/
theorem standardBlock_start_add_size_le
    {n j : ℕ} (hbit : n.testBit j = true) :
    (n / 2 ^ (j + 1)) * 2 ^ (j + 1) + 2 ^ j ≤ n := by
  unfold Nat.testBit at hbit
  rw [Nat.shiftRight_eq_div_pow] at hbit
  simp only [Nat.one_and_eq_mod_two] at hbit
  have hmod : n / 2 ^ j % 2 = 1 := by
    simp_all
  have htwo := Nat.mod_add_div (n / 2 ^ j) 2
  have hpow := Nat.mod_add_div n (2 ^ j)
  have hdiv :
      n / 2 ^ (j + 1) = (n / 2 ^ j) / 2 := by
    rw [pow_succ', Nat.mul_comm 2]
    exact (Nat.div_div_eq_div_mul n (2 ^ j) 2).symm
  rw [hdiv, pow_succ']
  have hquot :
      n / 2 ^ j = 1 + 2 * (n / 2 ^ j / 2) := by
    omega
  have hblock :
      n / 2 ^ j / 2 * (2 * 2 ^ j) + 2 ^ j =
        2 ^ j * (n / 2 ^ j) := by
    calc
      n / 2 ^ j / 2 * (2 * 2 ^ j) + 2 ^ j =
          2 ^ j * (1 + 2 * (n / 2 ^ j / 2)) := by ring
      _ = 2 ^ j * (n / 2 ^ j) :=
        congrArg (fun q => 2 ^ j * q) hquot.symm
  rw [hblock]
  omega

/-- Every index below `n` lies in one of the dyadic pieces selected by a
set bit in the binary decomposition of `n`. -/
theorem exists_standardBlock_index {n k : ℕ} (hk : k < n) :
    ∃ j : ℕ,
      n.testBit j = true ∧
      (n / 2 ^ (j + 1)) * 2 ^ (j + 1) ≤ k ∧
      k < (n / 2 ^ (j + 1)) * 2 ^ (j + 1) + 2 ^ j := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases hn : n = 0
    · omega
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hk_odd : k = n - 1 ∧ n % 2 = 1
    · use 0
      rcases hk_odd with ⟨hk_eq, hn_odd⟩
      have h_testBit : n.testBit 0 = true := by
        rw [Nat.testBit_zero, hn_odd]
        rfl
      refine ⟨h_testBit, ?_, ?_⟩
      · have h_div : n / 2 * 2 = n - 1 := by omega
        omega
      · have h_div : n / 2 * 2 = n - 1 := by omega
        omega
    · have h_k_div : k / 2 < n / 2 := by omega
      rcases ih (n / 2) (by omega) h_k_div with ⟨j, hj_bit, hj_lb, hj_ub⟩
      use j + 1
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.testBit_succ]
        exact hj_bit
      · have h_pow : j + 1 + 1 = j + 2 := rfl
        have h_div_div : n / 2 ^ (j + 2) = (n / 2) / 2 ^ (j + 1) := by
          have h1 : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ, mul_comm]
          rw [h1, ← Nat.div_div_eq_div_mul]
        rw [h_pow, h_div_div]
        have h2 : 2 ^ (j + 2) = 2 ^ (j + 1) * 2 := rfl
        rw [h2]
        have h_mul :
            ((n / 2) / 2 ^ (j + 1)) * (2 ^ (j + 1) * 2) =
              (((n / 2) / 2 ^ (j + 1)) * 2 ^ (j + 1)) * 2 := by
          ring
        rw [h_mul]
        omega
      · have h_pow : j + 1 + 1 = j + 2 := rfl
        have h_div_div : n / 2 ^ (j + 2) = (n / 2) / 2 ^ (j + 1) := by
          have h1 : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ, mul_comm]
          rw [h1, ← Nat.div_div_eq_div_mul]
        rw [h_pow, h_div_div]
        have h2 : 2 ^ (j + 2) = 2 ^ (j + 1) * 2 := rfl
        rw [h2]
        have h_mul :
            ((n / 2) / 2 ^ (j + 1)) * (2 ^ (j + 1) * 2) =
              (((n / 2) / 2 ^ (j + 1)) * 2 ^ (j + 1)) * 2 := by
          ring
        rw [h_mul]
        omega

/-- Every member of the completed output belongs to one of its source-standard
binary-decomposition blocks. -/
theorem exists_standardBlock_of_mem_completed
    (c : Code) (m : ℕ) (x : BitString)
    (hx : x ∈ completedBoundedOutput c m) :
    ∃ r, x ∈ standardBlock c m r x := by
  -- Get the index of x in the list
  have hnodup : (completedBoundedOutput c m).Nodup := by
    exact boundedOutputStage_nodup c m (maxHaltingStage c m)
  let idx := (completedBoundedOutput c m).idxOf x
  have hidx : idx < (completedBoundedOutput c m).length :=
    List.idxOf_lt_length_of_mem hx
  -- The length of completedBoundedOutput is omegaCount
  have hlen : (completedBoundedOutput c m).length = omegaCount c m := rfl
  rw [hlen] at hidx
  -- Use exists_standardBlock_index to find j
  obtain ⟨j, hjbit, hjle, hjlt⟩ := exists_standardBlock_index hidx
  -- Show x is in the standard block
  use j
  unfold standardBlock
  rw [if_pos hjbit]
  -- x is in the toFinset iff x is in the list after drop and take
  rw [List.mem_toFinset]
  -- Use that x = l[idx] and idx is in the right range
  have hx_eq : x = (completedBoundedOutput c m)[idx] := by
    rw [List.getElem_idxOf hidx]
  -- Show x is in take (drop ...)
  let L := completedBoundedOutput c m
  let start := omegaCount c m / 2 ^ (j + 1) * 2 ^ (j + 1)
  have hx_drop : x ∈ L.drop start := by
    rw [List.mem_drop_iff_getElem]
    refine ⟨idx - start, ?_, ?_⟩
    · unfold L start; rw [hlen]; omega
    · have hidx' : start + (idx - start) = idx := by omega
      simp only [hidx']
      exact hx_eq.symm
  -- Now show x is in take (2^j) (drop start L)
  -- We have hx_drop : x ∈ L.drop start with index idx - start
  have hklt : idx - start < 2 ^ j := by
    unfold L start at *
    omega
  -- Need to show (L.drop start)[idx - start] = x
  have hidx_valid : idx - start < (L.drop start).length := by
    simp only [List.length_drop]
    unfold L start
    omega
  have hx_drop_eq : (L.drop start)[idx - start] = x := by
    have hidx' : start + (idx - start) = idx := by omega
    rw [List.getElem_drop]
    simp only [hidx', L]
    exact hx_eq.symm
  have hidx_valid : idx - start < (L.drop start).length := by
    simp only [List.length_drop]
    unfold L start
    omega
  -- Now show x ∈ take (2^j) (drop start L)
  rw [List.mem_take_iff_getElem]
  refine ⟨idx - start, ?_, hx_drop_eq⟩
  exact Nat.lt_min.mpr ⟨hklt, hidx_valid⟩

/-- Every standard block is a subfamily of the completed bound-`m` output. -/
theorem standardBlock_subset_completed
    (c : Code) (m j : ℕ) (x : BitString) :
    standardBlock c m j x ⊆
      (completedBoundedOutput c m).toFinset := by
  intro y hy
  unfold standardBlock at hy
  split at hy
  · rw [List.mem_toFinset] at hy ⊢
    exact List.mem_of_mem_drop (List.mem_of_mem_take hy)
  · simp at hy

/-- In particular, an object described by a standard block has plain
complexity at most the bound used to enumerate that block. -/
theorem mem_completedBoundedOutput_of_mem_standardBlock
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    x ∈ completedBoundedOutput c m := by
  exact List.mem_toFinset.mp
    (standardBlock_subset_completed c m j x hx)

/-- Every genuine source-standard block has the advertised exact dyadic
cardinality. -/
theorem card_standardBlock_of_mem
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    (standardBlock c m j x).card = 2 ^ j := by
  have hbit := standardBlock_testBit_of_mem c m j x hx
  unfold standardBlock
  rw [if_pos hbit, List.toFinset_card_of_nodup]
  · simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    have hfit :=
      standardBlock_start_add_size_le
        (n := omegaCount c m) hbit
    change
      2 ^ j ≤
        (completedBoundedOutput c m).length -
          omegaCount c m / 2 ^ (j + 1) * 2 ^ (j + 1)
    change
      2 ^ j ≤
        omegaCount c m -
          omegaCount c m / 2 ^ (j + 1) * 2 ^ (j + 1)
    omega
  · exact ((boundedOutputStage_nodup c m
      (maxHaltingStage c m)).drop.take)

/-- The number of elements following the source-standard `2^j` block.  Under
membership in `standardBlock`, these are exactly the blocks belonging to the
lower `j` bits of `omegaCount c m`. -/
noncomputable def standardBlockTail (c : Code) (m j : ℕ) : ℕ :=
  omegaCount c m % 2 ^ j

/-- Exact arithmetic decomposition at the end of a genuine standard block:
the aligned higher-bit prefix, the `2^j` block itself, and the lower-bit
remainder add up to `omegaCount`. -/
theorem standardBlock_end_add_tail
    (c : Code) (m j : ℕ)
    (hbit : (omegaCount c m).testBit j = true) :
    (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1) +
        2 ^ j + standardBlockTail c m j =
      omegaCount c m := by
  unfold standardBlockTail
  unfold Nat.testBit at hbit
  rw [Nat.shiftRight_eq_div_pow] at hbit
  simp only [Nat.one_and_eq_mod_two] at hbit
  have hmod : omegaCount c m / 2 ^ j % 2 = 1 := by
    simpa using hbit
  have htwo := Nat.mod_add_div (omegaCount c m / 2 ^ j) 2
  have hpow := Nat.mod_add_div (omegaCount c m) (2 ^ j)
  have hdiv :
      omegaCount c m / 2 ^ (j + 1) =
        (omegaCount c m / 2 ^ j) / 2 := by
    rw [pow_succ', Nat.mul_comm 2]
    exact (Nat.div_div_eq_div_mul (omegaCount c m) (2 ^ j) 2).symm
  rw [hdiv, pow_succ']
  have hquot :
      omegaCount c m / 2 ^ j =
        1 + 2 * (omegaCount c m / 2 ^ j / 2) := by
    omega
  calc
    omegaCount c m / 2 ^ j / 2 * (2 * 2 ^ j) +
          2 ^ j + omegaCount c m % 2 ^ j =
        omegaCount c m % 2 ^ j +
          2 ^ j * (1 + 2 * (omegaCount c m / 2 ^ j / 2)) := by
      ring
    _ = omegaCount c m % 2 ^ j +
          2 ^ j * (omegaCount c m / 2 ^ j) := by
      exact congrArg
        (fun q => omegaCount c m % 2 ^ j + 2 ^ j * q)
        hquot.symm
    _ = omegaCount c m := hpow

/-- The numerical remainder `standardBlockTail` is exactly the length of the
completed-list suffix strictly following a genuine standard block.  This is
the promised translation between the source's possibly-zero strict tail and
the formalization's positive `tail + 1` convention. -/
theorem standardBlockTail_eq_length_drop_block_end
    (c : Code) (m j : ℕ)
    (hbit : (omegaCount c m).testBit j = true) :
    standardBlockTail c m j =
      ((completedBoundedOutput c m).drop
        ((omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1) +
          2 ^ j)).length := by
  rw [List.length_drop]
  change standardBlockTail c m j =
    omegaCount c m -
      (omegaCount c m / 2 ^ (j + 1) * 2 ^ (j + 1) + 2 ^ j)
  have hdecomp := standardBlock_end_add_tail c m j hbit
  omega

/-- A source-standard block containing `x` is the aligned completed dyadic
block containing `x`.  This is the exact bridge from B7's binary decomposition
to the concrete B6 block decoder. -/
theorem standardBlock_eq_completedDyadicBlock
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    standardBlock c m j x = completedDyadicBlock c m j x := by
  let L := completedBoundedOutput c m
  let p := 2 ^ j
  let q := omegaCount c m / 2 ^ (j + 1)
  let start := q * 2 ^ (j + 1)
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hxList : x ∈ (L.drop start).take p := by
    unfold standardBlock at hx
    rw [if_pos hbit, List.mem_toFinset] at hx
    simpa [L, p, q, start] using hx
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hxList
  have hklt : k < p := by
    exact lt_of_lt_of_le hk (List.length_take_le p (L.drop start))
  have hglobal : start + k < L.length := by
    simp only [List.length_take, List.length_drop] at hk
    omega
  have hget : L[start + k] = x := by
    simpa only [List.getElem_take, List.getElem_drop] using hkx
  have hnodup : L.Nodup := by
    dsimp [L, completedBoundedOutput]
    exact boundedOutputStage_nodup c m (maxHaltingStage c m)
  have hidx :
      L.findIdx (· == x) = start + k := by
    change L.idxOf x = start + k
    rw [← hget]
    exact hnodup.idxOf_getElem (start + k) hglobal
  have hstart :
      start = (2 * q) * p := by
    dsimp [start, p]
    rw [pow_succ']
    ring
  have hquot :
      L.findIdx (· == x) / p = 2 * q := by
    apply Nat.div_eq_of_lt_le
    · rw [hidx, ← hstart]
      omega
    · rw [hidx]
      calc
        start + k < start + p := by omega
        _ = (2 * q + 1) * p := by rw [hstart]; ring
  unfold standardBlock
  rw [if_pos hbit]
  unfold completedDyadicBlock completedDyadicBlockList
  apply congrArg List.toFinset
  change (L.drop start).take p =
    (L.drop ((L.findIdx (· == x) / p) * p)).take p
  rw [hquot, ← hstart]

/-- The inclusive version of the standard-block tail is always positive and at
most the block size.  The `+1` is the chapter-wide convention avoiding
`log 0` for the last standard block. -/
theorem standardBlockTail_add_one_le (c : Code) (m j : ℕ) :
    standardBlockTail c m j + 1 ≤ 2 ^ j := by
  unfold standardBlockTail
  exact Nat.succ_le_of_lt (Nat.mod_lt _ (by positivity))

/-- A genuine standard block exponent cannot exceed the plain-complexity
budget of the completed list containing it. -/
theorem standardBlock_exponent_le
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    j ≤ m := by
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hjOmega : 2 ^ j ≤ omegaCount c m := by
    have hfit :=
      standardBlock_start_add_size_le
        (n := omegaCount c m) hbit
    omega
  have hpow : 2 ^ j < 2 ^ (m + 1) :=
    lt_of_le_of_lt hjOmega (omegaCount_lt_two_pow_succ c m)
  have hjlt : j < m + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  omega

/-- The generic completed-dyadic-block decoder also recovers a genuine source
standard block.  Unlike `completedDyadicBlockSelector_recovers`, this statement
does not need a suffix hypothesis: exact standard-block cardinality already
certifies that the requested aligned block is complete. -/
theorem completedDyadicBlockSelector_recovers_standardBlock
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
    (codedUniformOn (standardBlock c m j x) hA).code ∈
      completedDyadicBlockSelector c
        (completedDyadicBlockInput m j
          (completedDyadicBlockIndex c m j x) (m - j + 1)) := by
  intro hA
  let blockIdx := completedDyadicBlockIndex c m j x
  let blockSize := 2 ^ j
  let blockEnd := (blockIdx + 1) * blockSize
  have hblockNodup :
      (completedDyadicBlockList c m j x).Nodup := by
    unfold completedDyadicBlockList
    exact ((boundedOutputStage_nodup c m
      (maxHaltingStage c m)).drop.take)
  have hblockLength :
      (completedDyadicBlockList c m j x).length = blockSize := by
    rw [← List.toFinset_card_of_nodup hblockNodup]
    change (completedDyadicBlock c m j x).card = blockSize
    rw [← standardBlock_eq_completedDyadicBlock c m j x hx,
      card_standardBlock_of_mem c m j x hx]
  have hblockEnd :
      blockEnd ≤ (completedBoundedOutput c m).length := by
    have htake :
        (((completedBoundedOutput c m).drop
            (blockIdx * blockSize)).take blockSize).length =
          blockSize := by
      simpa [completedDyadicBlockList, blockIdx, blockSize] using
        hblockLength
    simp only [List.length_take, List.length_drop] at htake
    have hle :
        blockSize ≤
          (completedBoundedOutput c m).length -
            blockIdx * blockSize :=
      min_eq_left_iff.mp htake
    have hend :
        (blockIdx + 1) * blockSize =
          blockIdx * blockSize + blockSize := by ring
    have hpos : 0 < blockSize := by
      dsimp [blockSize]
      positivity
    dsimp [blockEnd]
    rw [hend]
    omega
  let completeTime := boundedOutputCompletionTime c m
  have hex :
      ∃ t, blockEnd ≤ (boundedOutputStage c m t).length := by
    refine ⟨completeTime, ?_⟩
    rw [boundedOutputStage_eq_completed_at_completion]
    exact hblockEnd
  let t₀ := Nat.find hex
  have ht₀ :
      t₀ ∈ Nat.rfind (fun t => Part.some
        (decide (blockEnd ≤
          (boundedOutputStage c m t).length))) := by
    refine Nat.mem_rfind.mpr ⟨by simpa using Nat.find_spec hex, ?_⟩
    intro t ht
    simpa using Nat.find_min hex ht
  have hprefix :
      boundedOutputStage c m t₀ <+:
        completedBoundedOutput c m :=
    boundedOutputStage_prefix_completed c m t₀
  obtain ⟨rest, hrest⟩ := hprefix
  have ht₀len :
      blockEnd ≤ (boundedOutputStage c m t₀).length :=
    Nat.find_spec hex
  have htake :
      (boundedOutputStage c m t₀).take blockEnd =
        (completedBoundedOutput c m).take blockEnd := by
    rw [← hrest, List.take_append_of_le_length ht₀len]
  have hblockEndEq :
      blockIdx * blockSize + blockSize = blockEnd := by
    dsimp [blockEnd]
    ring
  have hblockEq :
      ((boundedOutputStage c m t₀).drop
          (blockIdx * blockSize)).take blockSize =
        completedDyadicBlockList c m j x := by
    unfold completedDyadicBlockList
    rw [show completedDyadicBlockIndex c m j x = blockIdx from rfl,
      show 2 ^ j = blockSize from rfl]
    rw [List.take_drop, List.take_drop, hblockEndEq, htake]
  let z := completedDyadicBlockInput m j blockIdx (m - j + 1)
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
  rw [show completedDyadicBlockIndex c m j x = blockIdx from rfl,
    show 2 ^ j = blockSize from rfl, hblockEq]
  have hcanonical :
      canonicalUniformCodeOfList
          (canonicalFinsetList
            (completedDyadicBlockList c m j x).toFinset) =
        (codedUniformOn (standardBlock c m j x) hA).code := by
    change
      canonicalUniformCodeOfList
          (canonicalFinsetList
            (completedDyadicBlock c m j x)) =
        (codedUniformOn (standardBlock c m j x) hA).code
    rw [← standardBlock_eq_completedDyadicBlock c m j x hx]
    exact canonicalUniformCodeOfList_canonicalFinsetList
      (standardBlock c m j x) hA
  rw [hcanonical]
  exact Part.mem_some _

theorem plainK_standardBlock_upper
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C, ∀ m j x (hx : x ∈ standardBlock c m j x),
      let hA := ⟨x, hx⟩
      plainK V (codedUniformOn (standardBlock c m j x) hA).code ≤
        ((m - j + logSlack C m : ℕ) : ENat) := by
  have _hc := hc
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV
      (completedDyadicBlockSelector c)
      (completedDyadicBlockSelector_partrec c)
  obtain ⟨Clen, hlen⟩ := plainKLeLength V hV
  let C := Clen + Cmap + 8
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  have hjm : j ≤ m :=
    standardBlock_exponent_le c m j x hx
  have hjlen :
      (Nat.bits j).length ≤ (Nat.bits m).length :=
    length_natBits_mono hjm
  let blockIdx := completedDyadicBlockIndex c m j x
  have hidx : blockIdx < 2 ^ (m - j + 1) := by
    have h :=
      completedDyadicBlockIndex_lt_two_pow c (m - j) j x
    rw [Nat.sub_add_cancel hjm] at h
    exact h
  let input :=
    completedDyadicBlockInput m j blockIdx (m - j + 1)
  have hinputLength :
      input.length =
        (m - j + 1) + 4 * (Nat.bits m).length +
          2 * (Nat.bits j).length + 3 := by
    simpa [input] using
      (completedDyadicBlockInput_length (m := m) (j := j)
        (blockIdx := blockIdx) (blockWidth := m - j + 1) hidx)
  have hselector :
      (codedUniformOn (standardBlock c m j x) hA).code ∈
        completedDyadicBlockSelector c input := by
    simpa [input, blockIdx] using
      (completedDyadicBlockSelector_recovers_standardBlock
        c m j x hx)
  have hbudget :
      input.length + Clen + Cmap ≤
        m - j + logSlack C m := by
    have hcoefficient : 6 ≤ C := by dsimp [C]; omega
    have hconstant : Clen + Cmap + 4 ≤ C := by dsimp [C]; omega
    calc
      input.length + Clen + Cmap
        = (m - j + 1 + 4 * (Nat.bits m).length +
            2 * (Nat.bits j).length + 3) + Clen + Cmap := by rw [hinputLength]
      _ ≤ (m - j + 1 + 4 * (Nat.bits m).length +
            2 * (Nat.bits m).length + 3) + Clen + Cmap := by gcongr
      _ = (m - j) + 6 * (Nat.bits m).length + (Clen + Cmap + 4) := by ring
      _ ≤ (m - j) + C * (Nat.bits m).length + C := by gcongr
      _ = m - j + logSlack C m := by unfold logSlack; ring
  calc
    plainK V
          (codedUniformOn (standardBlock c m j x) hA).code
        ≤ plainK V input + (Cmap : ENat) :=
      hmap input _ hselector
    _ ≤ ((input.length : ENat) + (Clen : ENat)) +
          (Cmap : ENat) := by
      gcongr
      exact hlen input
    _ = ((input.length + Clen + Cmap : ℕ) : ENat) := by
      push_cast
      ring
    _ ≤ ((m - j + logSlack C m : ℕ) : ENat) := by
      exact_mod_cast hbudget

/-- Prefix set-complexity companion to `plainK_standardBlock_upper`.  The same
uniform block decoder is charged with a self-delimiting input, adding only
logarithmic overhead to the `m-j`-bit block index. -/
theorem setComplexity_standardBlock_upper
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) :
    ∃ C, ∀ m j x (hx : x ∈ standardBlock c m j x),
      let hA := ⟨x, hx⟩
      setComplexity U (standardBlock c m j x) hA ≤
        ((m - j + logSlack C m : ℕ) : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    KPPlain_partrec_map_le U hU
      (completedDyadicBlockSelector c)
      (completedDyadicBlockSelector_partrec c)
  obtain ⟨Clen, hlen⟩ := KPPlain_le_length_add_log U hU
  let C := Clen + Cmap + 12
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  have hjm : j ≤ m :=
    standardBlock_exponent_le c m j x hx
  let i := m - j
  let blockIdx := completedDyadicBlockIndex c m j x
  have hidx : blockIdx < 2 ^ (i + 1) := by
    have h :=
      completedDyadicBlockIndex_lt_two_pow c (m - j) j x
    rw [Nat.sub_add_cancel hjm] at h
    exact h
  let input :=
    completedDyadicBlockInput m j blockIdx (i + 1)
  have hinputLength :
      input.length =
        i + 1 + 4 * (Nat.bits m).length +
          2 * (Nat.bits j).length + 3 := by
    simpa [input, blockIdx, i] using
      (completedDyadicBlockInput_length (m := m) (j := j)
        (blockIdx := blockIdx) (blockWidth := i + 1) hidx)
  have hselector :
      (codedUniformOn (standardBlock c m j x) hA).code ∈
        completedDyadicBlockSelector c input := by
    simpa [input, blockIdx, i] using
      (completedDyadicBlockSelector_recovers_standardBlock
        c m j x hx)
  let L := (Nat.bits m).length
  have hjBits : (Nat.bits j).length ≤ L := by
    dsimp [L]
    exact length_natBits_mono hjm
  have hinputLinear : input.length ≤ i + 6 * L + 4 := by
    rw [hinputLength]
    rw [show (Nat.bits m).length = L from rfl]
    omega
  have hmpow : m < 2 ^ L := by
    simpa [L] using lt_two_pow_length_natBits m
  have hLpow : L ≤ 2 ^ L := by
    exact Nat.recOn L (by norm_num) fun n ihn => by
      rw [pow_succ']
      linarith [Nat.one_le_pow n 2 zero_lt_two]
  have hinputPow : input.length < 2 ^ (L + 4) := by
    have hpow : (2 : ℕ) ^ (L + 4) = 16 * 2 ^ L := by
      rw [pow_add]
      ring
    rw [hpow]
    have hlin : input.length ≤ m + 6 * L + 4 := by
      calc
        input.length ≤ i + 6 * L + 4 := hinputLinear
        _ = (m - j) + 6 * L + 4 := rfl
        _ ≤ m + 6 * L + 4 := by omega
    generalize 2 ^ L = P at hmpow hLpow ⊢
    omega
  have hinputBits :
      (Nat.bits input.length).length ≤ L + 4 :=
    length_natBits_lt_pow hinputPow
  have hbudget :
      input.length + 2 * (Nat.bits input.length).length +
          Clen + Cmap ≤
        i + logSlack C m := by
    have hcoefficient : 8 ≤ C := by dsimp [C]; omega
    calc
      input.length + 2 * (Nat.bits input.length).length + Clen + Cmap
        ≤ (i + 6 * L + 4) + 2 * (L + 4) + Clen + Cmap := by gcongr
      _ = i + 8 * L + (Clen + Cmap + 12) := by ring
      _ = i + 8 * L + C := rfl
      _ ≤ i + C * L + C := by gcongr
      _ = i + logSlack C m := by unfold logSlack; ring
  unfold setComplexity
  calc
    KPPlain U
          (codedUniformOn (standardBlock c m j x) hA).code
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
    _ ≤ ((i + logSlack C m : ℕ) : ENat) := by
      exact_mod_cast hbudget
    _ = ((m - j + logSlack C m : ℕ) : ENat) := rfl

/-- Chopping the completed list into full aligned `2^j` blocks covers every
object with an inclusive suffix of size at least `2^j`.  The displayed block is
the concrete chopped block, not merely an existential profile witness. -/
theorem chopped_standard_blocks
    (U : Map) (hU : IsOptimalPrefixConditional U) (c : Code) :
    ∃ C : ℕ, ∀ (x : BitString) (i j : ℕ),
      (htail : 2 ^ j ≤ suffixCoordinate c (i + j) x) →
      let A := completedDyadicBlock c (i + j) j x
      let hA : A.Nonempty :=
        completedDyadicBlock_nonempty c (i + j) j x htail
      x ∈ A ∧ A.card = 2 ^ j ∧
        IsIJDescription U x A hA
          (i + logSlack C (i + j)) j := by
  obtain ⟨C, hC⟩ := setComplexity_completedDyadicBlock_le U hU c
  refine ⟨C, fun x i j htail => ?_⟩
  intro A hA
  exact ⟨mem_completedDyadicBlock c (i + j) j x htail,
    card_completedDyadicBlock c (i + j) j x htail,
    mem_completedDyadicBlock c (i + j) j x htail,
    hC x i j htail,
    le_of_eq (card_completedDyadicBlock c (i + j) j x htail)⟩

/-- Logarithmic advice carrying the list bound and the standard-block
exponent.  The described object itself is supplied as the condition. -/
def standardBlockAdvice (m j : ℕ) : BitString :=
  pairCode (Nat.bits m) (Nat.bits j)

def standardBlockAdviceM (z : BitString) : ℕ :=
  bitsToNat (decodeFirst z)

def standardBlockAdviceJ (z : BitString) : ℕ :=
  bitsToNat (decodeSecond z)

@[simp] theorem standardBlockAdviceM_advice (m j : ℕ) :
    standardBlockAdviceM (standardBlockAdvice m j) = m := by
  unfold standardBlockAdviceM standardBlockAdvice
  rw [decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem standardBlockAdviceJ_advice (m j : ℕ) :
    standardBlockAdviceJ (standardBlockAdvice m j) = j := by
  unfold standardBlockAdviceJ standardBlockAdvice
  rw [decodeSecond_pairCode, bitsToNat_bits]

theorem standardBlockAdvice_length (m j : ℕ) :
    (standardBlockAdvice m j).length =
      2 * (Nat.bits m).length + (Nat.bits j).length + 1 := by
  unfold standardBlockAdvice
  rw [length_pairCode]
  omega

def standardBlockReady
    (c : Code) (x z : BitString) (t : ℕ) : Bool :=
  let L := boundedOutputStage c (standardBlockAdviceM z) t
  let p := 2 ^ standardBlockAdviceJ z
  let idx := L.findIdx (fun y => decide (y = x))
  decide (idx < L.length ∧ (idx / p + 1) * p ≤ L.length)

/-- Given a condition `x` and advice `(m,j)`, wait until the bound-`m`
enumeration contains `x` and has completed the aligned `2^j` block containing
it, then return that block's canonical uniform-set code. -/
noncomputable def standardBlockFromMemberSelector
    (c : Code) : BitString → BitString →. BitString := fun x z =>
  (Nat.rfind (fun t => Part.some (standardBlockReady c x z t))).bind
    (fun t =>
      let L := boundedOutputStage c (standardBlockAdviceM z) t
      let p := 2 ^ standardBlockAdviceJ z
      let idx := L.findIdx (fun y => decide (y = x))
      Part.some
        (canonicalUniformCodeOfList
          (canonicalFinsetList
            (((L.drop ((idx / p) * p)).take p).toFinset))))

theorem standardBlockFromMemberSelector_partrec
    (c : Code) :
    Partrec (fun q : BitString × BitString =>
      standardBlockFromMemberSelector c q.1 q.2) := by
  have hm : Primrec standardBlockAdviceM :=
    bitsToNat_primrec.comp decodeFirst_primrec'
  have hj : Primrec standardBlockAdviceJ :=
    bitsToNat_primrec.comp decodeSecond_primrec'
  have hm' : Primrec (fun q : (BitString × BitString) × ℕ =>
      standardBlockAdviceM q.1.2) :=
    hm.comp (Primrec.snd.comp Primrec.fst)
  have hj' : Primrec (fun q : (BitString × BitString) × ℕ =>
      standardBlockAdviceJ q.1.2) :=
    hj.comp (Primrec.snd.comp Primrec.fst)
  have hstage : Primrec (fun q : (BitString × BitString) × ℕ =>
      boundedOutputStage c (standardBlockAdviceM q.1.2) q.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair hm' Primrec.snd)
  have hidx : Primrec (fun q : (BitString × BitString) × ℕ =>
      (boundedOutputStage c
        (standardBlockAdviceM q.1.2) q.2).findIdx
          (fun y => decide (y = q.1.1))) := by
    exact Primrec.list_findIdx hstage
      (PrimrecPred.decide
        (Primrec.eq.comp Primrec.snd
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).to₂
  have hlen : Primrec (fun q : (BitString × BitString) × ℕ =>
      (boundedOutputStage c
        (standardBlockAdviceM q.1.2) q.2).length) :=
    Primrec.list_length.comp hstage
  have hp : Primrec (fun q : (BitString × BitString) × ℕ =>
      2 ^ standardBlockAdviceJ q.1.2) :=
    Kolmogorov.CodedFiniteDistribution.twoPow_primrec.comp hj'
  have hblockEnd : Primrec (fun q : (BitString × BitString) × ℕ =>
      ((boundedOutputStage c
        (standardBlockAdviceM q.1.2) q.2).findIdx
          (fun y => decide (y = q.1.1)) /
            (2 ^ standardBlockAdviceJ q.1.2) + 1) *
            2 ^ standardBlockAdviceJ q.1.2) :=
    Primrec.nat_mul.comp
      (Primrec.nat_add.comp
        (Primrec.nat_div.comp hidx hp) (Primrec.const 1)) hp
  have hcheck : Computable₂ (fun (q : BitString × BitString) (t : ℕ) =>
      standardBlockReady c q.1 q.2 t) := by
    exact (PrimrecPred.decide
      ((Primrec.nat_lt.comp hidx hlen).and
        (Primrec.nat_le.comp hblockEnd hlen))).to_comp.to₂ |>.of_eq
          (fun _ => rfl)
  have hsearch : Partrec (fun q : BitString × BitString =>
      Nat.rfind (fun t => Part.some
        (standardBlockReady c q.1 q.2 t))) :=
    Partrec.rfind hcheck.partrec₂
  have hstart : Primrec (fun q : (BitString × BitString) × ℕ =>
      ((boundedOutputStage c
        (standardBlockAdviceM q.1.2) q.2).findIdx
          (fun y => decide (y = q.1.1)) /
            (2 ^ standardBlockAdviceJ q.1.2)) *
            2 ^ standardBlockAdviceJ q.1.2) :=
    Primrec.nat_mul.comp (Primrec.nat_div.comp hidx hp) hp
  have hblock : Primrec (fun q : (BitString × BitString) × ℕ =>
      (boundedOutputStage c
        (standardBlockAdviceM q.1.2) q.2).drop
          (((boundedOutputStage c
            (standardBlockAdviceM q.1.2) q.2).findIdx
              (fun y => decide (y = q.1.1)) /
                (2 ^ standardBlockAdviceJ q.1.2)) *
                  2 ^ standardBlockAdviceJ q.1.2) |>.take
                    (2 ^ standardBlockAdviceJ q.1.2)) :=
    Primrec.list_take.comp
      hp (Primrec.list_drop.comp hstart hstage)
  have hcode : Computable₂ (fun (q : BitString × BitString) (t : ℕ) =>
      canonicalUniformCodeOfList
        (canonicalFinsetList
          (((boundedOutputStage c
              (standardBlockAdviceM q.2) t).drop
                ((((boundedOutputStage c
                  (standardBlockAdviceM q.2) t).findIdx
                    (fun y => decide (y = q.1))) /
                      (2 ^ standardBlockAdviceJ q.2)) *
                        2 ^ standardBlockAdviceJ q.2) |>.take
                          (2 ^ standardBlockAdviceJ q.2)).toFinset))) :=
    (canonicalUniformCodeOfList_primrec.comp
      (canonicalFinsetList_toFinset_primrec.comp hblock)).to_comp.to₂
  unfold standardBlockFromMemberSelector
  exact (Partrec.bind hsearch hcode.partrec₂).of_eq (fun _ => rfl)

theorem findIdx_decide_eq_eq_idxOf
    (L : List BitString) (x : BitString) :
    L.findIdx (fun y => decide (y = x)) = L.idxOf x := by
  unfold List.idxOf
  congr 1
  funext y
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]

theorem standardBlockFromMemberSelector_recovers
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
    (codedUniformOn (standardBlock c m j x) hA).code ∈
      standardBlockFromMemberSelector c x
        (standardBlockAdvice m j) := by
  intro hA
  let L := completedBoundedOutput c m
  let p := 2 ^ j
  let idx := L.findIdx (fun y => decide (y = x))
  let blockStart := (idx / p) * p
  let blockEnd := (idx / p + 1) * p
  have hxL : x ∈ L :=
    mem_completedBoundedOutput_of_mem_standardBlock c m j x hx
  have hidxLt : idx < L.length := by
    dsimp [idx]
    rw [List.findIdx_lt_length]
    exact ⟨x, hxL, by simp⟩
  have hblockListNodup :
      ((L.drop blockStart).take p).Nodup :=
    by
      exact ((boundedOutputStage_nodup c m
        (maxHaltingStage c m)).drop.take)
  have hblockSet :
      ((L.drop blockStart).take p).toFinset =
        standardBlock c m j x := by
    have hidxEq :
        L.findIdx (fun y => decide (y = x)) =
          L.findIdx (· == x) := by
      rw [findIdx_decide_eq_eq_idxOf]
      rfl
    rw [show blockStart =
        completedDyadicBlockIndex c m j x * 2 ^ j by
      dsimp [blockStart, idx, p, completedDyadicBlockIndex]
      rw [hidxEq]]
    exact (standardBlock_eq_completedDyadicBlock c m j x hx).symm
  have hblockLength :
      ((L.drop blockStart).take p).length = p := by
    rw [← List.toFinset_card_of_nodup hblockListNodup, hblockSet,
      card_standardBlock_of_mem c m j x hx]
  have hblockEndLe : blockEnd ≤ L.length := by
    have hle : p ≤ L.length - blockStart := by
      simp only [List.length_take, List.length_drop] at hblockLength
      exact min_eq_left_iff.mp hblockLength
    have hstartLe : blockStart ≤ idx := by
      dsimp [blockStart]
      exact Nat.div_mul_le_self idx p
    have hend : blockEnd = blockStart + p := by
      dsimp [blockEnd, blockStart]
      ring
    rw [hend]
    omega
  let completeTime := boundedOutputCompletionTime c m
  have hreadyComplete :
      standardBlockReady c x (standardBlockAdvice m j) completeTime = true := by
    unfold standardBlockReady
    simp only [standardBlockAdviceM_advice, standardBlockAdviceJ_advice,
      decide_eq_true_eq]
    rw [boundedOutputStage_eq_completed_at_completion]
    exact ⟨hidxLt, hblockEndLe⟩
  let hex : ∃ t,
      standardBlockReady c x (standardBlockAdvice m j) t = true :=
    ⟨completeTime, hreadyComplete⟩
  let t₀ := Nat.find hex
  have ht₀ :
      t₀ ∈ Nat.rfind (fun t => Part.some
        (standardBlockReady c x (standardBlockAdvice m j) t)) := by
    refine Nat.mem_rfind.mpr ⟨by simpa using Nat.find_spec hex, ?_⟩
    intro t ht
    simpa using Nat.find_min hex ht
  let S := boundedOutputStage c m t₀
  have hready : standardBlockReady c x
      (standardBlockAdvice m j) t₀ = true :=
    Nat.find_spec hex
  have hready' :
      let idxS := S.findIdx (fun y => decide (y = x))
      idxS < S.length ∧ (idxS / p + 1) * p ≤ S.length := by
    simpa [standardBlockReady, S, p] using hready
  let idxS := S.findIdx (fun y => decide (y = x))
  have hidxSLt : idxS < S.length := hready'.1
  have hendS : (idxS / p + 1) * p ≤ S.length := hready'.2
  have hprefix : S <+: L :=
    boundedOutputStage_prefix_completed c m t₀
  have hgetS : S[idxS] = x := by
    have hfound :=
      List.findIdx_getElem
        (p := fun y : BitString => decide (y = x))
        (xs := S) (w := hidxSLt)
    exact of_decide_eq_true hfound
  have hidxSL : idxS < L.length :=
    lt_of_lt_of_le hidxSLt hprefix.length_le
  have hgetL : L[idxS]'hidxSL = x := by
    exact (hprefix.getElem hidxSLt).symm.trans hgetS
  have hnodupL : L.Nodup := by
    dsimp [L, completedBoundedOutput]
    exact boundedOutputStage_nodup c m (maxHaltingStage c m)
  have hidxEq : idx = idxS := by
    dsimp [idx]
    rw [findIdx_decide_eq_eq_idxOf, ← hgetL]
    exact hnodupL.idxOf_getElem idxS hidxSL
  have htake :
      S.take ((idxS / p + 1) * p) =
        L.take ((idxS / p + 1) * p) := by
    obtain ⟨rest, hrest⟩ := hprefix
    rw [← hrest, List.take_append_of_le_length hendS]
  have hslice :
      (S.drop ((idxS / p) * p)).take p =
        (L.drop ((idxS / p) * p)).take p := by
    have hendEq :
        (idxS / p) * p + p = (idxS / p + 1) * p := by
      ring
    rw [List.take_drop, List.take_drop, hendEq, htake]
  unfold standardBlockFromMemberSelector
  rw [Part.mem_bind_iff]
  refine ⟨t₀, ht₀, ?_⟩
  simp only [standardBlockAdviceM_advice,
    standardBlockAdviceJ_advice]
  have houtput :
      canonicalUniformCodeOfList
        (canonicalFinsetList
          (((S.drop ((idxS / p) * p)).take p).toFinset)) =
        (codedUniformOn (standardBlock c m j x) hA).code := by
    rw [hslice, show ((L.drop ((idxS / p) * p)).take p).toFinset =
        standardBlock c m j x by
          rw [← hidxEq]
          exact hblockSet]
    exact canonicalUniformCodeOfList_canonicalFinsetList
      (standardBlock c m j x) hA
  change (codedUniformOn (standardBlock c m j x) hA).code ∈
    Part.some
      (canonicalUniformCodeOfList
        (canonicalFinsetList
          (((S.drop ((idxS / p) * p)).take p).toFinset)))
  rw [houtput]
  exact Part.mem_some _

/-- Simplicity of a standard description given x. -/
theorem standard_description_simple_given_x
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      condK V
        (codedUniformOn (standardBlock c m j x) hA).code x ≤
          (logSlack C m : ENat) := by
  have _hc := hc
  obtain ⟨Cmap, hmap⟩ :=
    condK_partrec_cond_map_le V hV
      (standardBlockFromMemberSelector c)
      (standardBlockFromMemberSelector_partrec c)
  let C := Cmap + 4
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  have hjm : j ≤ m :=
    standardBlock_exponent_le c m j x hx
  have hjlen :
      (Nat.bits j).length ≤ (Nat.bits m).length :=
    length_natBits_mono hjm
  have hrec :=
    standardBlockFromMemberSelector_recovers c m j x hx
  calc
    condK V
          (codedUniformOn (standardBlock c m j x) hA).code x
        ≤ ((standardBlockAdvice m j).length : ENat) +
            (Cmap : ENat) :=
      hmap x (standardBlockAdvice m j)
        (codedUniformOn (standardBlock c m j x) hA).code hrec
    _ = (((standardBlockAdvice m j).length + Cmap : ℕ) : ENat) := by
      rw [Nat.cast_add]
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast (show
        (standardBlockAdvice m j).length + Cmap ≤
          logSlack C m by
        rw [standardBlockAdvice_length]
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits m).length)])

theorem stageMissing_le_standardBlockTail
    (c : Code) (m j t : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x)
    (hcover : ∀ y ∈ standardBlock c m j x,
      y ∈ boundedOutputStage c m t) :
    omegaCount c m - (boundedOutputStage c m t).length ≤
      standardBlockTail c m j := by
  let L := completedBoundedOutput c m
  let S := boundedOutputStage c m t
  let p := 2 ^ j
  let start :=
    (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1)
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hfit : start + p ≤ L.length := by
    change
      (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1) +
          2 ^ j ≤ omegaCount c m
    exact standardBlock_start_add_size_le hbit
  have hp : 0 < p := by
    dsimp [p]
    positivity
  let k := p - 1
  have hk : k < ((L.drop start).take p).length := by
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    · dsimp [k]
      omega
    · omega
  let y := ((L.drop start).take p)[k]
  have hySlice : y ∈ (L.drop start).take p :=
    List.getElem_mem hk
  have hyBlock : y ∈ standardBlock c m j x := by
    unfold standardBlock
    rw [if_pos hbit, List.mem_toFinset]
    simpa [L, start, p] using hySlice
  have hyS : y ∈ S := hcover y hyBlock
  have hprefix : S <+: L :=
    boundedOutputStage_prefix_completed c m t
  have hyIdxLt : L.idxOf y < S.length :=
    (hprefix.mem_iff_idxOf_lt_length y).mp hyS
  have hglobal : start + k < L.length := by
    omega
  have hyGet : L[start + k] = y := by
    dsimp [y]
    simp only [List.getElem_take, List.getElem_drop]
  have hnodup : L.Nodup := by
    dsimp [L, completedBoundedOutput]
    exact boundedOutputStage_nodup c m
      (maxHaltingStage c m)
  have hidx : L.idxOf y = start + k := by
    rw [← hyGet]
    exact hnodup.idxOf_getElem (start + k) hglobal
  have hendLe : start + p ≤ S.length := by
    rw [hidx] at hyIdxLt
    dsimp [k] at hyIdxLt
    omega
  have hdecomp :=
    standardBlock_end_add_tail c m j hbit
  change omegaCount c m - S.length ≤
    standardBlockTail c m j
  omega

def plainProgramAdvice (p : BitString) (m count : ℕ) : BitString :=
  pairCode (Nat.bits p.length)
    (p ++ pairCode (Nat.bits m) (Nat.bits count))

theorem plainProgramAdvice_length (p : BitString) (m count : ℕ) :
    (plainProgramAdvice p m count).length =
      p.length + 2 * (Nat.bits p.length).length +
        2 * (Nat.bits m).length + (Nat.bits count).length + 2 := by
  unfold plainProgramAdvice
  rw [length_pairCode, List.length_append, length_pairCode]
  omega

noncomputable def standardBlockOmegaDecoder
    (V : Map) (c : Code) : BitString →. BitString := fun z =>
  let payload := decodeSecond z
  let pLength := bitsToNat (decodeFirst z)
  let p := payload.take pLength
  let advice := payload.drop pLength
  (V (p, [])).bind fun SCode =>
    descriptionTailOmegaSelector c
      (descriptionTailOmegaInput SCode
        (bitsToNat (decodeFirst advice))
        (bitsToNat (decodeSecond advice)))

theorem standardBlockOmegaDecoder_partrec
    (V : Map) (hV : isDecompressor V) (c : Code) :
    Partrec (standardBlockOmegaDecoder V c) := by
  have hpLength : Primrec (fun z : BitString =>
      bitsToNat (decodeFirst z)) :=
    bitsToNat_primrec.comp decodeFirst_primrec'
  have hp : Computable (fun z : BitString =>
      (decodeSecond z).take
        (bitsToNat (decodeFirst z))) :=
    (Primrec.list_take.comp hpLength
      decodeSecond_primrec').to_comp
  have hrun : Partrec (fun z : BitString =>
      V (((decodeSecond z).take
        (bitsToNat (decodeFirst z))), [])) :=
    Partrec.comp hV
      (Computable.pair hp (Computable.const []))
  have hadvice : Primrec (fun z : BitString =>
      (decodeSecond z).drop
        (bitsToNat (decodeFirst z))) :=
    Primrec.list_drop.comp hpLength
      decodeSecond_primrec'
  have hm : Primrec (fun z : BitString =>
      bitsToNat (decodeFirst
        ((decodeSecond z).drop
          (bitsToNat (decodeFirst z))))) :=
    bitsToNat_primrec.comp
      (decodeFirst_primrec'.comp hadvice)
  have hcount : Primrec (fun z : BitString =>
      bitsToNat (decodeSecond
        ((decodeSecond z).drop
          (bitsToNat (decodeFirst z))))) :=
    bitsToNat_primrec.comp
      (decodeSecond_primrec'.comp hadvice)
  have hinput : Primrec (fun q : BitString × BitString =>
      descriptionTailOmegaInput q.2
        (bitsToNat (decodeFirst
          ((decodeSecond q.1).drop
            (bitsToNat (decodeFirst q.1)))))
        (bitsToNat (decodeSecond
          ((decodeSecond q.1).drop
            (bitsToNat (decodeFirst q.1)))))) := by
    unfold descriptionTailOmegaInput
    exact pairCode_primrec.comp Primrec.snd
      (pairCode_primrec.comp
        (primrecNatBits.comp (hm.comp Primrec.fst))
        (primrecNatBits.comp (hcount.comp Primrec.fst)))
  have hpost : Partrec (fun q : BitString × BitString =>
      descriptionTailOmegaSelector c
        (descriptionTailOmegaInput q.2
          (bitsToNat (decodeFirst
            ((decodeSecond q.1).drop
              (bitsToNat (decodeFirst q.1)))))
          (bitsToNat (decodeSecond
            ((decodeSecond q.1).drop
              (bitsToNat (decodeFirst q.1))))))) :=
    Partrec.comp (descriptionTailOmegaSelector_partrec c)
      hinput.to_comp
  unfold standardBlockOmegaDecoder
  exact Partrec.bind hrun hpost

theorem standardBlockOmegaDecoder_recovers
    (V : Map) (c : Code) (m j : ℕ) (x p : BitString)
    (hx : x ∈ standardBlock c m j x)
    (hp : produces V p []
      (codedUniformOn (standardBlock c m j x) ⟨x, hx⟩).code) :
    ∃ count ≤ standardBlockTail c m j,
      omegaNatCode c m ∈
        standardBlockOmegaDecoder V c
          (plainProgramAdvice p m count) := by
  let B := standardBlock c m j x
  let hB : B.Nonempty := ⟨x, hx⟩
  let SCode := (codedUniformOn B hB).code
  let SList := canonicalFinsetList B
  have hSList :
      SList =
        (decodeDistributionData SCode).map
          CodedDistributionEntry.point := by
    exact (dataPoints_codedUniformOn B hB).symm
  have hsubset :
      ∀ y ∈ SList, y ∈ completedBoundedOutput c m := by
    intro y hy
    change y ∈ canonicalFinsetList B at hy
    rw [mem_canonicalFinsetList] at hy
    rw [← List.mem_toFinset]
    exact standardBlock_subset_completed c m j x hy
  have hex :
      ∃ t, SList.all (fun y =>
        (boundedOutputStage c m t).elem y) = true := by
    obtain ⟨t, ht⟩ :=
      exists_stage_covering_finset c m B
        (fun y hy => hsubset y
          (mem_canonicalFinsetList.mpr hy))
    refine ⟨t, ?_⟩
    rw [List.all_eq_true]
    intro y hy
    rw [List.elem_eq_mem]
    exact decide_eq_true
      (ht y (mem_canonicalFinsetList.mp hy))
  let t₀ := Nat.find hex
  have ht₀spec :
      SList.all (fun y =>
        (boundedOutputStage c m t₀).elem y) = true :=
    Nat.find_spec hex
  have ht₀mem :
      t₀ ∈ Nat.rfind (fun t => Part.some
        (SList.all (fun y =>
          (boundedOutputStage c m t).elem y))) := by
    refine Nat.mem_rfind.mpr ⟨by simpa using ht₀spec, ?_⟩
    intro t ht
    simpa using Nat.find_min hex ht
  let count :=
    omegaCount c m -
      (boundedOutputStage c m t₀).length
  have hcoverAt :
      ∀ y ∈ standardBlock c m j x,
        y ∈ boundedOutputStage c m t₀ := by
    rw [List.all_eq_true] at ht₀spec
    intro y hy
    have hyElem :=
      ht₀spec y
        (mem_canonicalFinsetList.mpr hy)
    simpa [List.elem_eq_mem] using hyElem
  have hcountLe :
      count ≤ standardBlockTail c m j :=
    stageMissing_le_standardBlockTail
      c m j t₀ x hx hcoverAt
  have hrecover :
      descriptionTailOmegaSelector c
          (descriptionTailOmegaInput SCode m count) =
        Part.some (Nat.bits (omegaCount c m)) := by
    apply descriptionTailOmegaSelector_recovers
      c m SCode SList hSList hsubset count
    exact
      ⟨t₀, (Part.eq_some_iff.mpr ht₀mem).symm, rfl⟩
  have hselector :
      omegaNatCode c m ∈
        descriptionTailOmegaSelector c
          (descriptionTailOmegaInput SCode m count) :=
    Part.eq_some_iff.mp hrecover
  refine ⟨count, hcountLe, ?_⟩
  unfold standardBlockOmegaDecoder
  simp only [plainProgramAdvice, decodeSecond_pairCode,
    decodeFirst_pairCode, bitsToNat_bits, List.take_left,
    List.drop_left]
  rw [Part.mem_bind_iff]
  refine ⟨SCode, ?_, ?_⟩
  · simpa [SCode, B, hB] using hp
  · simpa using hselector

theorem standardBlock_omega_coding_bound
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C, ∀ m j x (hx : x ∈ standardBlock c m j x),
      (m : ENat) ≤
        plainK V
          (codedUniformOn (standardBlock c m j x) ⟨x, hx⟩).code +
        ((Nat.bits (standardBlockTail c m j)).length : ENat) +
        (logSlack C m : ENat) := by
  obtain ⟨COmega, hOmega⟩ :=
    plainKNat_omegaCount_lower V hV c hc
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV
      (standardBlockOmegaDecoder V c)
      (standardBlockOmegaDecoder_partrec V hV.1 c)
  obtain ⟨Clen, hlen⟩ := plainKLeLength V hV
  obtain ⟨Cupper, hupper⟩ :=
    plainK_standardBlock_upper V hV c hc
  let C :=
    2 * (Nat.bits Cupper).length +
      Clen + Cmap + COmega + 10
  refine ⟨C, fun m j x hx => ?_⟩
  let B := standardBlock c m j x
  let hB : B.Nonempty := ⟨x, hx⟩
  let BCode := (codedUniformOn B hB).code
  have hfinite : plainK V BCode ≠ ⊤ := by
    intro htop
    have h := hlen BCode
    rw [htop] at h
    exact ENat.natCast_ne_top _
      (top_le_iff.mp h)
  obtain ⟨p, hp, hpLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := BCode) (y := []) hfinite
  have hpLengthEq :
      (p.length : ENat) = plainK V BCode := by
    exact hpLength
  have hpLengthUpper :
      p.length ≤ m - j + logSlack Cupper m := by
    have h := hupper m j x hx
    change plainK V BCode ≤
      ((m - j + logSlack Cupper m : ℕ) : ENat) at h
    rw [← hpLengthEq] at h
    exact_mod_cast h
  obtain ⟨count, hcountLe, hrecover⟩ :=
    standardBlockOmegaDecoder_recovers
      V c m j x p hx
        (by simpa [BCode, B, hB] using hp)
  have hcountBits :
      (Nat.bits count).length ≤
        (Nat.bits (standardBlockTail c m j)).length :=
    length_natBits_mono hcountLe
  let input := plainProgramAdvice p m count
  have hinputLength :
      input.length =
        p.length + 2 * (Nat.bits p.length).length +
          2 * (Nat.bits m).length +
          (Nat.bits count).length + 2 := by
    exact plainProgramAdvice_length p m count
  have hpBits :
      (Nat.bits p.length).length ≤
        2 * (Nat.bits m).length +
          (Nat.bits Cupper).length + 2 := by
    have hpLe :
        p.length ≤ m + logSlack Cupper m := by
      omega
    calc
      (Nat.bits p.length).length
          ≤ (Nat.bits
              (m + logSlack Cupper m)).length :=
        length_natBits_mono hpLe
      _ ≤ (Nat.bits m).length +
          (Nat.bits (logSlack Cupper m)).length + 1 :=
        length_natBits_add_le m (logSlack Cupper m)
      _ ≤ 2 * (Nat.bits m).length +
          (Nat.bits Cupper).length + 2 := by
        have hlog :=
          length_natBits_logSlack_le Cupper m
        omega
  have hoverhead :
      2 * (Nat.bits p.length).length +
          2 * (Nat.bits m).length + 2 +
          Clen + Cmap + COmega ≤
        logSlack C m := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le ((Nat.bits Cupper).length),
      Nat.zero_le Clen, Nat.zero_le Cmap,
      Nat.zero_le COmega]
  have hdecode :
      plainKNat V (omegaCount c m) ≤
        plainK V input + (Cmap : ENat) := by
    exact hmap input (omegaNatCode c m)
      (by simpa [input] using hrecover)
  calc
    (m : ENat)
        ≤ plainKNat V (omegaCount c m) +
            (COmega : ENat) :=
      hOmega m
    _ ≤ (plainK V input + (Cmap : ENat)) +
          (COmega : ENat) := by
      gcongr
    _ ≤ (((input.length : ENat) + (Clen : ENat)) +
          (Cmap : ENat)) + (COmega : ENat) := by
      gcongr
      exact hlen input
    _ = ((p.length +
          2 * (Nat.bits p.length).length +
          2 * (Nat.bits m).length +
          (Nat.bits count).length + 2 +
          Clen + Cmap + COmega : ℕ) : ENat) := by
      rw [hinputLength]
      push_cast
      ring
    _ ≤ ((p.length +
          (Nat.bits (standardBlockTail c m j)).length +
          logSlack C m : ℕ) : ENat) := by
      exact_mod_cast (by omega)
    _ = plainK V BCode +
          ((Nat.bits
            (standardBlockTail c m j)).length : ENat) +
          (logSlack C m : ENat) := by
      rw [← hpLengthEq]
      push_cast
      rfl
    _ = plainK V
          (codedUniformOn
            (standardBlock c m j x) ⟨x, hx⟩).code +
          ((Nat.bits
            (standardBlockTail c m j)).length : ENat) +
          (logSlack C m : ENat) := rfl

theorem pow_sub_two_mul_le_add_one
    {m j k t S : ℕ}
    (hjm : j ≤ m)
    (hrec : m ≤ k + (Nat.bits t).length + S)
    (hk : k ≤ m - j + S) :
    2 ^ (j - (2 * S + 1)) ≤ t + 1 := by
  by_cases hS : j ≤ 2 * S
  · have hzero : j - (2 * S + 1) = 0 := by omega
    rw [hzero]
    simp
  · by_contra h
    push Not at h
    have ht : t < 2 ^ (j - (2 * S + 1)) := by omega
    have hlen : (Nat.bits t).length ≤ j - (2 * S + 1) := length_natBits_lt_pow ht
    have hmj : m - j + j = m := Nat.sub_add_cancel hjm
    omega

theorem two_mul_logSlack_add_one_le (C m : ℕ) :
    2 * logSlack C m + 1 ≤ logSlack (2 * C + 1) m := by
  unfold logSlack
  calc
    2 * (C * (Nat.bits m).length + C) + 1 = 2 * C * (Nat.bits m).length + 2 * C + 1 := by ring
    _ ≤ 2 * C * (Nat.bits m).length + (Nat.bits m).length + 2 * C + 1 := by omega
    _ = (2 * C + 1) * (Nat.bits m).length + (2 * C + 1) := by ring

/-- Proposition `prop:std-pos`.  For every genuine standard block containing
`x`, both its source-facing plain complexity and its profile-facing prefix
set-complexity are `m-j` up to a uniform logarithmic slack.  The inclusive
number of elements following the block is `2^(j+O(log m))`. -/
theorem prop_std_pos (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString),
      (hx : x ∈ standardBlock c m j x) →
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      ((m - j : ℕ) : ENat) ≤
          plainK V
            (codedUniformOn (standardBlock c m j x) hA).code +
            (logSlack C m : ENat) ∧
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code ≤
            ((m - j + logSlack C m : ℕ) : ENat) ∧
      ((m - j : ℕ) : ENat) ≤
          setComplexity U (standardBlock c m j x) hA +
            (logSlack C m : ENat) ∧
      setComplexity U (standardBlock c m j x) hA ≤
          ((m - j + logSlack C m : ℕ) : ENat) ∧
      2 ^ (j - logSlack C m) ≤ standardBlockTail c m j + 1 ∧
      standardBlockTail c m j + 1 ≤ 2 ^ j := by
  obtain ⟨Ccoding, hcoding⟩ :=
    standardBlock_omega_coding_bound V hV c hc
  obtain ⟨Cplain, hplain⟩ :=
    plainK_standardBlock_upper V hV c hc
  obtain ⟨Cset, hset⟩ :=
    setComplexity_standardBlock_upper U hU c
  obtain ⟨Cbridge, hbridge⟩ :=
    plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  let D := Ccoding + Cplain
  let C := 2 * D + 1 + Cset + Cbridge
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  let BCode :=
    (codedUniformOn (standardBlock c m j x) hA).code
  have hplainUpper := hplain m j x hx
  change plainK V BCode ≤
    ((m - j + logSlack Cplain m : ℕ) : ENat)
      at hplainUpper
  have hfinite : plainK V BCode ≠ ⊤ := by
    intro htop
    rw [htop] at hplainUpper
    exact ENat.natCast_ne_top _ (top_le_iff.mp hplainUpper)
  obtain ⟨k, hkRaw⟩ :=
    ENat.ne_top_iff_exists.mp hfinite
  have hk : plainK V BCode = (k : ENat) := hkRaw.symm
  have htailLt :
      standardBlockTail c m j < 2 ^ j := by
    have h := standardBlockTail_add_one_le c m j
    omega
  have htailBits :
      (Nat.bits (standardBlockTail c m j)).length ≤ j :=
    length_natBits_lt_pow htailLt
  have hcodingNat :
      m ≤ k +
        (Nat.bits (standardBlockTail c m j)).length +
        logSlack Ccoding m := by
    have h := hcoding m j x hx
    change (m : ENat) ≤
      plainK V BCode +
        ((Nat.bits
          (standardBlockTail c m j)).length : ENat) +
        (logSlack Ccoding m : ENat) at h
    rw [hk] at h
    exact_mod_cast h
  have hkUpperNat :
      k ≤ m - j + logSlack Cplain m := by
    rw [hk] at hplainUpper
    exact_mod_cast hplainUpper
  have hCcoding :
      logSlack Ccoding m ≤ logSlack C m := by
    apply logSlack_mono_left
    dsimp [C, D]
    omega
  have hCplain :
      logSlack Cplain m ≤ logSlack C m := by
    apply logSlack_mono_left
    dsimp [C, D]
    omega
  have hCset :
      logSlack Cset m ≤ logSlack C m := by
    apply logSlack_mono_left
    dsimp [C, D]
    omega
  have hLowerPlain :
      ((m - j : ℕ) : ENat) ≤
        plainK V BCode + (logSlack C m : ENat) := by
    rw [hk]
    exact_mod_cast (show
      m - j ≤ k + logSlack C m by omega)
  have hUpperPlain :
      plainK V BCode ≤
        ((m - j + logSlack C m : ℕ) : ENat) := by
    exact hplainUpper.trans (by
      exact_mod_cast
        Nat.add_le_add_left hCplain (m - j))
  have hLowerSet :
      ((m - j : ℕ) : ENat) ≤
        setComplexity U
          (standardBlock c m j x) hA +
          (logSlack C m : ENat) := by
    have hb := hbridge BCode
    change plainK V BCode ≤
      setComplexity U
        (standardBlock c m j x) hA +
        (Cbridge : ENat) at hb
    calc
      ((m - j : ℕ) : ENat)
          ≤ plainK V BCode +
              (logSlack Ccoding m : ENat) := by
        rw [hk]
        exact_mod_cast (show
          m - j ≤ k + logSlack Ccoding m by omega)
      _ ≤ (setComplexity U
            (standardBlock c m j x) hA +
              (Cbridge : ENat)) +
            (logSlack Ccoding m : ENat) := by
        gcongr
      _ ≤ setComplexity U
            (standardBlock c m j x) hA +
            (logSlack C m : ENat) := by
        have habsorb :
            Cbridge + logSlack Ccoding m ≤
              logSlack C m := by
          have hcoefficient : Ccoding ≤ C := by
            dsimp [C, D]
            omega
          have hconstant : Ccoding + Cbridge ≤ C := by
            dsimp [C, D]
            omega
          calc
            Cbridge + logSlack Ccoding m
                = Ccoding * (Nat.bits m).length +
                    (Ccoding + Cbridge) := by
                  unfold logSlack
                  ring
            _ ≤ C * (Nat.bits m).length + C :=
              Nat.add_le_add
                (Nat.mul_le_mul_right
                  (Nat.bits m).length hcoefficient)
                hconstant
            _ = logSlack C m := by
              unfold logSlack
              ring
        rw [add_assoc]
        gcongr
        exact_mod_cast habsorb
  have hUpperSet :
      setComplexity U
          (standardBlock c m j x) hA ≤
        ((m - j + logSlack C m : ℕ) : ENat) := by
    exact (hset m j x hx).trans (by
      exact_mod_cast
        Nat.add_le_add_left hCset (m - j))
  have hDcoding :
      logSlack Ccoding m ≤ logSlack D m := by
    exact logSlack_mono_left
      (by dsimp [D]; omega) m
  have hDplain :
      logSlack Cplain m ≤ logSlack D m := by
    exact logSlack_mono_left
      (by dsimp [D]; omega) m
  have hrecD :
      m ≤ k +
        (Nat.bits (standardBlockTail c m j)).length +
        logSlack D m := by
    omega
  have hkD :
      k ≤ m - j + logSlack D m := by
    omega
  have hpow :=
    pow_sub_two_mul_le_add_one
      (standardBlock_exponent_le c m j x hx)
      hrecD hkD
  have htwo :
      2 * logSlack D m + 1 ≤
        logSlack (2 * D + 1) m :=
    two_mul_logSlack_add_one_le D m
  have htailSlack :
      2 * logSlack D m + 1 ≤ logSlack C m := by
    exact htwo.trans
      (logSlack_mono_left
        (by dsimp [C]; omega) m)
  have hsub :
      j - logSlack C m ≤
        j - (2 * logSlack D m + 1) := by
    omega
  have hLowerTail :
      2 ^ (j - logSlack C m) ≤
        standardBlockTail c m j + 1 :=
    (Nat.pow_le_pow_right (by norm_num) hsub).trans hpow
  exact ⟨hLowerPlain, hUpperPlain, hLowerSet,
    hUpperSet, hLowerTail,
    standardBlockTail_add_one_le c m j⟩

def lengthFilteredModel
    (A : Finset BitString) (n : ℕ) : Finset BitString :=
  A.filter (fun y => y.length = n)

def lengthFilterUniformCode (s : BitString) : BitString :=
  let w := decodeFirst s
  let n := bitsToNat (decodeSecond s)
  let points :=
    ((decodeDistributionData w).map
      CodedDistributionEntry.point).filter
        (fun y => decide (y.length = n))
  let L := canonicalFinsetList points.toFinset
  codedDistributionDataCode (L.map fun y =>
    { point := y,
      mass := ratMassInvNat (max 1 L.length) (by positivity) })

theorem lengthFilterUniformCode_computable :
    Computable lengthFilterUniformCode := by
  have hlen :
      Primrec (fun q : BitString × BitString =>
        q.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hn :
      Primrec (fun q : BitString × BitString =>
        bitsToNat (decodeSecond q.1)) :=
    bitsToNat_primrec.comp
      (decodeSecond_primrec.comp Primrec.fst)
  have hp : Primrec₂ (fun (a : BitString) (b : BitString) =>
      decide (b.length = bitsToNat (decodeSecond a))) :=
    PrimrecPred.decide (Primrec.eq.comp hlen hn)
  exact Primrec.to_comp (Primrec.of_eq
    (Primrec.comp codedUniformEncoder_primrec
      (canonicalFinsetList_toFinset_primrec.comp
        (list_filter_primrec
          (Primrec.list_map
            (decodeDistributionData_primrec.comp decodeFirst_primrec)
            (entry_point_primrec.comp Primrec.snd).to₂)
          hp)))
    (by intro a; rfl))

theorem lengthFilterUniformCode_eq
    (A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) (n : ℕ)
    (hx : x ∈ A) (hxn : x.length = n) :
    lengthFilterUniformCode
        (pairCode (codedUniformOn A hA).code (Nat.bits n)) =
      (codedUniformOn (lengthFilteredModel A n)
        ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩).code := by
  let B := lengthFilteredModel A n
  let hB : B.Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩
  have hpoints :
      (((decodeDistributionData
          (codedUniformOn A hA).code).map
          CodedDistributionEntry.point).filter
            (fun y => decide (y.length = n))).toFinset = B := by
    rw [dataPoints_codedUniformOn]
    ext y
    simp [B, lengthFilteredModel]
  unfold lengthFilterUniformCode
  simp only [decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]
  let S :=
    (((decodeDistributionData
        (codedUniformOn A hA).code).map
        CodedDistributionEntry.point).filter
          (fun y => decide (y.length = n))).toFinset
  let hS : S.Nonempty := by
    dsimp [S]
    rw [hpoints]
    exact hB
  change
    codedDistributionDataCode
        ((canonicalFinsetList S).map fun y =>
          { point := y,
            mass := ratMassInvNat
              (max 1 (canonicalFinsetList S).length)
              (by positivity) }) =
      (codedUniformOn B hB).code
  calc
    _ = (codedUniformOn S hS).code := by
      rw [codedUniformOn_code_eq S hS]
      have hcard :
          max 1 (canonicalFinsetList S).length = S.card := by
        rw [length_canonicalFinsetList]
        exact max_eq_right
          (Finset.one_le_card.mpr hS)
      apply congrArg codedDistributionDataCode
      apply List.map_congr_left
      intro y _
      apply congrArg (fun mass =>
        ({ point := y, mass := mass } :
          CodedDistributionEntry))
      apply RatMass.code_injective
      simp only [RatMass.code, ratMassInvNat, hcard]
    _ = (codedUniformOn B hB).code :=
      codedUniformOn_code_congr hS hB hpoints

noncomputable def lengthFilterUniformCodeSelector :
    BitString →. BitString := fun s =>
  Part.some (lengthFilterUniformCode s)

theorem lengthFilterUniformCodeSelector_partrec :
    Partrec lengthFilterUniformCodeSelector := by
  exact lengthFilterUniformCode_computable.partrec

theorem lengthFilterUniformCodeSelector_recovers
    (A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) (n : ℕ)
    (hx : x ∈ A) (hxn : x.length = n) :
    (codedUniformOn (lengthFilteredModel A n)
      ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩).code ∈
      lengthFilterUniformCodeSelector
        (pairCode (codedUniformOn A hA).code (Nat.bits n)) := by
  unfold lengthFilterUniformCodeSelector
  rw [lengthFilterUniformCode_eq A hA x n hx hxn]
  exact Part.mem_some _

theorem setComplexity_lengthFilteredModel_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C, ∀ A hA x n (hx : x ∈ A) (hxn : x.length = n),
      setComplexity U (lengthFilteredModel A n)
          ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩ ≤
        setComplexity U A hA + (logSlack C n : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    KPPlain_map_le U hU lengthFilterUniformCode
      lengthFilterUniformCode_computable
  obtain ⟨Cpair, hpair⟩ :=
    KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨Clen, hlen⟩ :=
    KPPlain_le_two_mul_length U hU
  let C := Cmap + Cpair + Clen + 3
  refine ⟨C, fun A hA x n hx hxn => ?_⟩
  let hB : (lengthFilteredModel A n).Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩
  have heq :=
    lengthFilterUniformCode_eq A hA x n hx hxn
  have hbits :
      KPPlain U (Nat.bits n) ≤
        ((2 * (Nat.bits n).length + Clen : ℕ) : ENat) := by
    exact_mod_cast hlen (Nat.bits n)
  calc
    setComplexity U (lengthFilteredModel A n) hB =
        KPPlain U
          (lengthFilterUniformCode
            (pairCode (codedUniformOn A hA).code
              (Nat.bits n))) := by
      unfold setComplexity
      rw [heq]
    _ ≤ KPPlain U
          (pairCode (codedUniformOn A hA).code
            (Nat.bits n)) + (Cmap : ENat) :=
      hmap _
    _ = KPPair U (codedUniformOn A hA).code
          (Nat.bits n) + (Cmap : ENat) := rfl
    _ ≤ (KPPlain U (codedUniformOn A hA).code +
          KPPlain U (Nat.bits n) + (Cpair : ENat)) +
          (Cmap : ENat) := by
      gcongr
      exact hpair _ _
    _ ≤ (setComplexity U A hA +
          ((2 * (Nat.bits n).length + Clen : ℕ) : ENat) +
          (Cpair : ENat)) + (Cmap : ENat) := by
      change
        (KPPlain U (codedUniformOn A hA).code +
            KPPlain U (Nat.bits n) + (Cpair : ENat)) +
            (Cmap : ENat) ≤
          (KPPlain U (codedUniformOn A hA).code +
            ((2 * (Nat.bits n).length + Clen : ℕ) : ENat) +
            (Cpair : ENat)) + (Cmap : ENat)
      have hbase :=
        add_le_add
          (le_refl
            (KPPlain U (codedUniformOn A hA).code))
          hbits
      have hpair' :=
        add_le_add_right hbase (Cpair : ENat)
      have hmap' :=
        add_le_add_right hpair' (Cmap : ENat)
      calc
        (KPPlain U (codedUniformOn A hA).code +
            KPPlain U (Nat.bits n) + (Cpair : ENat)) +
            (Cmap : ENat) =
          (Cmap : ENat) + ((Cpair : ENat) +
            (KPPlain U (codedUniformOn A hA).code +
              KPPlain U (Nat.bits n))) := by abel
        _ ≤ (Cmap : ENat) + ((Cpair : ENat) +
            (KPPlain U (codedUniformOn A hA).code +
              ((2 * (Nat.bits n).length + Clen : ℕ) :
                ENat))) := hmap'
        _ = (KPPlain U (codedUniformOn A hA).code +
            ((2 * (Nat.bits n).length + Clen : ℕ) : ENat) +
            (Cpair : ENat)) + (Cmap : ENat) := by abel
    _ = setComplexity U A hA +
          ((2 * (Nat.bits n).length + Clen + Cpair +
            Cmap : ℕ) : ENat) := by
      push_cast
      abel
    _ ≤ setComplexity U A hA +
          (logSlack C n : ENat) := by
      gcongr
      exact_mod_cast (show
        2 * (Nat.bits n).length + Clen + Cpair + Cmap
          ≤ logSlack C n by
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits n).length)])

/-- A member of a source-standard block has inclusive suffix coordinate strictly
below the size of two adjacent blocks. -/
theorem suffixCoordinate_lt_pow_succ_standardBlock
    (c : Code) (m r : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m r x) :
    suffixCoordinate c m x < 2 ^ (r + 1) := by
  -- Get the testBit condition from membership
  have hbit := standardBlock_testBit_of_mem c m r x hx
  -- x is in completedBoundedOutput
  have hxList : x ∈ completedBoundedOutput c m :=
    mem_completedBoundedOutput_of_mem_standardBlock c m r x hx
  -- The list is nodup
  have hnodup : (completedBoundedOutput c m).Nodup :=
    boundedOutputStage_nodup c m (maxHaltingStage c m)
  -- Let's set up the notation used in the proof
  let L := completedBoundedOutput c m
  let start := omegaCount c m / 2 ^ (r + 1) * 2 ^ (r + 1)
  let p := 2 ^ r
  -- Unfold standardBlock to get the structural information
  unfold standardBlock at hx
  rw [if_pos hbit, List.mem_toFinset] at hx
  -- x is in (L.drop start).take p
  -- Get the index of x in L
  let idx := L.idxOf x
  have hidx_lt : idx < L.length := List.idxOf_lt_length_of_mem hxList
  -- x is in (L.drop start).take p
  -- x is in (L.drop start).take p
  -- x is in (L.drop start).take p
  have hx_take : x ∈ (L.drop start).take p := hx
  -- Get k and the bounds without destroying hx_take
  have ⟨k, hk, hkx⟩ := List.mem_take_iff_getElem.mp hx_take
  -- k < p
  have hk_lt_p : k < p := Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)
  -- x is in L.drop start
  have hx_drop : x ∈ L.drop start := List.mem_of_mem_take hx_take
  -- x is in L.drop start |>.take p, so its index satisfies start ≤ idx < start + p
  have hidx_bounds : start ≤ idx ∧ idx < start + p := by
    have hglobal : start + k < L.length := by
      simp only [List.length_drop] at hk
      omega
    have hidx_eq : idx = start + k := by
      have := hnodup.idxOf_getElem (start + k) hglobal
      simp only [List.getElem_drop] at hkx
      rwa [hkx] at this
    exact ⟨by omega, by omega⟩
  -- suffixCoordinate c m x = suffixCountIncluding L x
  unfold suffixCoordinate
  -- For a nodup list, suffixCountIncluding L x = L.length - idx
  have hsuff : suffixCountIncluding L x = L.length - idx := by
    have h1 := findIdx_add_suffixCountIncluding_eq_length L x hxList
    have h2 : L.findIdx (· == x) = idx := by
      have : L.findIdx (· == x) = L.findIdx (fun y => decide (y = x)) := by
        congr 1; funext y; simp [Bool.beq_eq_decide_eq]
      rw [this, findIdx_decide_eq_eq_idxOf]
    rw [h2] at h1
    omega
  rw [hsuff]
  -- L.length = omegaCount c m
  have hlen : L.length = omegaCount c m := rfl
  rw [hlen]
  -- Since idx ≥ start, omegaCount c m - idx ≤ omegaCount c m - start
  have hle : omegaCount c m - idx < 2 ^ (r + 1) := by
    have hlt : omegaCount c m - start < 2 ^ (r + 1) := by
      unfold start
      have hmod :
          omegaCount c m -
              omegaCount c m / 2 ^ (r + 1) * 2 ^ (r + 1) =
            omegaCount c m % 2 ^ (r + 1) := by
        have := Nat.mod_add_div (omegaCount c m) (2 ^ (r + 1))
        rw [mul_comm] at this
        omega
      rw [hmod]
      exact Nat.mod_lt _ (by norm_num : 0 < 2 ^ (r + 1))
    exact lt_of_le_of_lt (Nat.sub_le_sub_left hidx_bounds.1 _) hlt
  exact hle

/-- Comparing a suffix-coordinate lower bound with the geometry of a
source-standard block bounds the block's complexity gap. -/
theorem standardBlock_gap_le_of_suffix_lower
    (c : Code) (m r q S : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m r x)
    (hsuffix :
      2 ^ (m - q - S) ≤ suffixCoordinate c m x) :
    m - r ≤ q + S := by
  have h1 := suffixCoordinate_lt_pow_succ_standardBlock c m r x hx
  have h2 : 2 ^ (m - q - S) < 2 ^ (r + 1) := lt_of_le_of_lt hsuffix h1
  have h3 : m - q - S < r + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

theorem suffixCoordinate_lower_of_model_code
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C, ∀ m (q : ℕ) x (A : Finset BitString) (hA : A.Nonempty),
      x ∈ A →
      (∀ y ∈ A, y ∈ completedBoundedOutput c m) →
      plainK V (codedUniformOn A hA).code ≤ (q : ENat) →
      2 ^ (m - q - logSlack C m) ≤ suffixCoordinate c m x := by
  obtain ⟨COmega, hOmega⟩ :=
    plainKNat_omegaCount_lower V hV c hc
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV
      (standardBlockOmegaDecoder V c)
      (standardBlockOmegaDecoder_partrec V hV.1 c)
  obtain ⟨Clen, hlen⟩ := plainKLeLength V hV
  let C := COmega + Cmap + Clen + 5
  refine ⟨C, fun m q x A hA hxA hsubset hcode => ?_⟩
  have hxCompleted : x ∈ completedBoundedOutput c m :=
    hsubset x hxA
  have hsuffixPos : 0 < suffixCoordinate c m x := by
    unfold suffixCoordinate
    exact suffixCountIncluding_pos_iff_mem.mpr hxCompleted
  by_cases hsmall : m ≤ q + logSlack C m
  · have hzero : m - q - logSlack C m = 0 := by omega
    rw [hzero]
    exact hsuffixPos
  · have hqm : q < m := by omega
    have hmPos : 0 < m := by omega
    let ACode := (codedUniformOn A hA).code
    obtain ⟨p, hpLength, hp⟩ :
        ∃ p, p.length ≤ q ∧ produces V p [] ACode := by
      exact (condKLeIff V ACode [] q).mp hcode
    let AList := canonicalFinsetList A
    have hAList :
        AList =
          (decodeDistributionData ACode).map
            CodedDistributionEntry.point := by
      exact (dataPoints_codedUniformOn A hA).symm
    have hAListSubset :
        ∀ y ∈ AList, y ∈ completedBoundedOutput c m := by
      intro y hy
      apply hsubset y
      exact mem_canonicalFinsetList.mp hy
    have hcover :
        ∃ t, AList.all (fun y =>
          (boundedOutputStage c m t).elem y) = true := by
      obtain ⟨t, ht⟩ :=
        exists_stage_covering_finset c m A hsubset
      refine ⟨t, ?_⟩
      rw [List.all_eq_true]
      intro y hy
      rw [List.elem_eq_mem]
      exact decide_eq_true
        (ht y (mem_canonicalFinsetList.mp hy))
    let t₀ := Nat.find hcover
    have ht₀spec :
        AList.all (fun y =>
          (boundedOutputStage c m t₀).elem y) = true :=
      Nat.find_spec hcover
    have ht₀mem :
        t₀ ∈ Nat.rfind (fun t => Part.some
          (AList.all (fun y =>
            (boundedOutputStage c m t).elem y))) := by
      refine Nat.mem_rfind.mpr ⟨by simpa using ht₀spec, ?_⟩
      intro t ht
      simpa using Nat.find_min hcover ht
    have hxList : x ∈ AList :=
      mem_canonicalFinsetList.mpr hxA
    have hxStage :
        x ∈ boundedOutputStage c m t₀ := by
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
      omegaCount c m -
        (boundedOutputStage c m t₀).length
    have hcountR : count = R.length := by
      dsimp [count, omegaCount]
      rw [hR, List.length_append]
      omega
    have hcountLt :
        count < suffixCoordinate c m x := by
      have htail :
          tailAfter (completedBoundedOutput c m) x <
            suffixCoordinate c m x := by
        unfold suffixCoordinate
        rw [suffixCountIncluding_eq_tailAfter_add_one
          hxCompleted]
        omega
      rw [hcountR]
      exact lt_of_le_of_lt hRtail htail
    have hrecover :
        descriptionTailOmegaSelector c
            (descriptionTailOmegaInput ACode m count) =
          Part.some (Nat.bits (omegaCount c m)) := by
      apply descriptionTailOmegaSelector_recovers
        c m ACode AList hAList hAListSubset count
      exact
        ⟨t₀, (Part.eq_some_iff.mpr ht₀mem).symm, rfl⟩
    have htailSelector :
        omegaNatCode c m ∈
          descriptionTailOmegaSelector c
            (descriptionTailOmegaInput ACode m count) :=
      Part.eq_some_iff.mp hrecover
    have hdecoder :
        omegaNatCode c m ∈
          standardBlockOmegaDecoder V c
            (plainProgramAdvice p m count) := by
      unfold standardBlockOmegaDecoder
      simp only [plainProgramAdvice, decodeSecond_pairCode,
        decodeFirst_pairCode, bitsToNat_bits, List.take_left,
        List.drop_left]
      rw [Part.mem_bind_iff]
      refine ⟨ACode, hp, ?_⟩
      simpa using htailSelector
    let input := plainProgramAdvice p m count
    have hinputLength :
        input.length =
          p.length + 2 * (Nat.bits p.length).length +
            2 * (Nat.bits m).length +
            (Nat.bits count).length + 2 :=
      plainProgramAdvice_length p m count
    have hpBits :
        (Nat.bits p.length).length ≤
          (Nat.bits m).length := by
      exact length_natBits_mono
        (hpLength.trans (Nat.le_of_lt hqm))
    have hmBitsPos : 0 < (Nat.bits m).length := by
      simpa [Nat.size_eq_bits_len] using Nat.size_pos.mpr hmPos
    have hcoefficient : 4 ≤ C := by dsimp [C]; omega
    have hconstant : Clen + Cmap + COmega + 2 < C := by dsimp [C]; omega
    have hSlackBound : 4 * (Nat.bits m).length +
        (Clen + Cmap + COmega + 2) < logSlack C m := by
      unfold logSlack
      calc
        4 * (Nat.bits m).length + (Clen + Cmap + COmega + 2)
          ≤ C * (Nat.bits m).length + (Clen + Cmap + COmega + 2) := by gcongr
        _ < C * (Nat.bits m).length + C := by gcongr
    have hoverhead :
        2 * (Nat.bits p.length).length +
            2 * (Nat.bits m).length + 2 +
            Clen + Cmap + COmega <
          logSlack C m := by
      calc
        2 * (Nat.bits p.length).length + 2 * (Nat.bits m).length + 2 +
            Clen + Cmap + COmega
          ≤ 2 * (Nat.bits m).length + 2 * (Nat.bits m).length + 2 +
            Clen + Cmap + COmega := by gcongr
        _ = 4 * (Nat.bits m).length + (Clen + Cmap + COmega + 2) := by ring
        _ < logSlack C m := hSlackBound
    have hdecode :
        plainKNat V (omegaCount c m) ≤
          plainK V input + (Cmap : ENat) := by
      exact hmap input (omegaNatCode c m)
        (by simpa [input] using hdecoder)
    have hmBoundENat :
        (m : ENat) ≤
          ((p.length + (Nat.bits count).length +
            (2 * (Nat.bits p.length).length +
              2 * (Nat.bits m).length + 2 +
              Clen + Cmap + COmega) : ℕ) : ENat) := by
      calc
        (m : ENat)
            ≤ plainKNat V (omegaCount c m) +
                (COmega : ENat) :=
          hOmega m
        _ ≤ (plainK V input + (Cmap : ENat)) +
              (COmega : ENat) := by
          gcongr
        _ ≤ (((input.length : ENat) + (Clen : ENat)) +
              (Cmap : ENat)) + (COmega : ENat) := by
          gcongr
          exact hlen input
        _ = ((p.length + (Nat.bits count).length +
              (2 * (Nat.bits p.length).length +
                2 * (Nat.bits m).length + 2 +
                Clen + Cmap + COmega) : ℕ) : ENat) := by
          rw [hinputLength]
          push_cast
          ring
    have hmBound :
        m ≤ p.length + (Nat.bits count).length +
          (2 * (Nat.bits p.length).length +
            2 * (Nat.bits m).length + 2 +
            Clen + Cmap + COmega) := by
      exact_mod_cast hmBoundENat
    by_contra hpow
    push Not at hpow
    have hcountPow :
        count < 2 ^ (m - q - logSlack C m) :=
      lt_trans hcountLt hpow
    have hcountBits :
        (Nat.bits count).length ≤
          m - q - logSlack C m :=
      length_natBits_lt_pow hcountPow
    omega

/-! ## The conditional selector required by `prop_better_std`

The selector first waits until every point decoded from the condition model has
appeared in the bound-`m` enumeration.  It then takes the last such point in
enumeration order.  The requested source-standard block is either the aligned
`2^r` block containing that point or the immediately preceding aligned block;
one flag selects the branch.  A final call to
`standardBlockFromMemberSelector` waits until the selected block is complete.
-/

def betterStandardBlockAdvice (m r : ℕ) (current : Bool) : BitString :=
  pairCode (Nat.bits m)
    (pairCode (Nat.bits r) [current])

def betterStandardBlockAdviceM (z : BitString) : ℕ :=
  bitsToNat (decodeFirst z)

def betterStandardBlockAdviceR (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond z))

def betterStandardBlockAdviceCurrent (z : BitString) : Bool :=
  (decodeSecond (decodeSecond z)).headI

@[simp] theorem betterStandardBlockAdviceM_advice
    (m r : ℕ) (current : Bool) :
    betterStandardBlockAdviceM
      (betterStandardBlockAdvice m r current) = m := by
  unfold betterStandardBlockAdviceM
    betterStandardBlockAdvice
  rw [decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem betterStandardBlockAdviceR_advice
    (m r : ℕ) (current : Bool) :
    betterStandardBlockAdviceR
      (betterStandardBlockAdvice m r current) = r := by
  unfold betterStandardBlockAdviceR
    betterStandardBlockAdvice
  rw [decodeSecond_pairCode, decodeFirst_pairCode,
    bitsToNat_bits]

@[simp] theorem betterStandardBlockAdviceCurrent_advice
    (m r : ℕ) (current : Bool) :
    betterStandardBlockAdviceCurrent
      (betterStandardBlockAdvice m r current) = current := by
  unfold betterStandardBlockAdviceCurrent
    betterStandardBlockAdvice
  rw [decodeSecond_pairCode, decodeSecond_pairCode]
  rfl

theorem betterStandardBlockAdvice_length
    (m r : ℕ) (current : Bool) :
    (betterStandardBlockAdvice m r current).length =
      2 * (Nat.bits m).length +
        2 * (Nat.bits r).length + 3 := by
  simp [betterStandardBlockAdvice, length_pairCode]
  omega

def betterStandardModelList (ACode : BitString) :
    List BitString :=
  (decodeDistributionData ACode).map
    CodedDistributionEntry.point

def betterStandardModelSeen
    (c : Code) (ACode advice : BitString) (t : ℕ) : Bool :=
  (betterStandardModelList ACode).all (fun y =>
    (boundedOutputStage c
      (betterStandardBlockAdviceM advice) t).elem y)

def betterStandardLastMember
    (c : Code) (ACode advice : BitString) (t : ℕ) : BitString :=
  (((boundedOutputStage c
      (betterStandardBlockAdviceM advice) t).filter
        (fun y => decide
          (y ∈ betterStandardModelList ACode))).reverse).headI

def betterStandardAnchor
    (c : Code) (ACode advice : BitString) (t : ℕ) : BitString :=
  let L := boundedOutputStage c
    (betterStandardBlockAdviceM advice) t
  let last := betterStandardLastMember c ACode advice t
  let p := 2 ^ betterStandardBlockAdviceR advice
  let start :=
    (L.findIdx (fun y => decide (y = last)) / p) * p
  if betterStandardBlockAdviceCurrent advice then
    last
  else
    L.getD (start - 1) []

noncomputable def betterStandardBlockSelector
    (c : Code) : BitString → BitString →. BitString :=
  fun ACode advice =>
    (Nat.rfind (fun t => Part.some
      (betterStandardModelSeen c ACode advice t))).bind
        (fun t =>
          standardBlockFromMemberSelector c
            (betterStandardAnchor c ACode advice t)
            (standardBlockAdvice
              (betterStandardBlockAdviceM advice)
              (betterStandardBlockAdviceR advice)))

theorem betterStandardBlockSelector_partrec
    (c : Code) :
    Partrec (fun q : BitString × BitString =>
      betterStandardBlockSelector c q.1 q.2) := by
  have hm : Primrec betterStandardBlockAdviceM :=
    bitsToNat_primrec.comp decodeFirst_primrec'
  have hr : Primrec betterStandardBlockAdviceR :=
    bitsToNat_primrec.comp
      (decodeFirst_primrec'.comp decodeSecond_primrec')
  have hcurrent : Primrec betterStandardBlockAdviceCurrent :=
    Primrec.list_headI.comp
      (decodeSecond_primrec'.comp decodeSecond_primrec')
  have hmodel : Primrec betterStandardModelList :=
    Primrec.list_map decodeDistributionData_primrec
      (entry_point_primrec.comp Primrec.snd).to₂
  have hstage : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        boundedOutputStage c
          (betterStandardBlockAdviceM q.1.2) q.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair
        (hm.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have hseenPred : Primrec₂
      (fun (q : (BitString × BitString) × ℕ)
        (y : BitString) =>
          decide (y ∈ boundedOutputStage c
            (betterStandardBlockAdviceM q.1.2) q.2)) :=
    (bitString_mem_primrec.comp Primrec.snd
      (hstage.comp Primrec.fst)).to₂
  have hseen : Computable₂
      (fun (q : BitString × BitString) (t : ℕ) =>
        betterStandardModelSeen c q.1 q.2 t) := by
    have hall : Primrec
        (fun q : (BitString × BitString) × ℕ =>
          (betterStandardModelList q.1.1).all
            (fun y => decide (y ∈ boundedOutputStage c
              (betterStandardBlockAdviceM q.1.2) q.2))) :=
      list_all_primrec
        (hmodel.comp (Primrec.fst.comp Primrec.fst))
        hseenPred
    exact hall.to_comp.to₂ |>.of_eq (fun _ => by
      simp only [betterStandardModelSeen, List.elem_eq_mem])
  have hsearch : Partrec
      (fun q : BitString × BitString =>
        Nat.rfind (fun t => Part.some
          (betterStandardModelSeen c q.1 q.2 t))) :=
    Partrec.rfind hseen.partrec₂
  have hmodelMem : Primrec₂
      (fun (q : (BitString × BitString) × ℕ)
        (y : BitString) =>
          decide (y ∈ betterStandardModelList q.1.1)) :=
    (bitString_mem_primrec.comp Primrec.snd
      (hmodel.comp
        (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))).to₂
  have hfiltered : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        (boundedOutputStage c
          (betterStandardBlockAdviceM q.1.2) q.2).filter
            (fun y => decide
              (y ∈ betterStandardModelList q.1.1))) :=
    list_filter_primrec hstage hmodelMem
  have hlast : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        betterStandardLastMember c q.1.1 q.1.2 q.2) := by
    exact (Primrec.list_headI.comp
      (Primrec.list_reverse.comp hfiltered)).of_eq
        (fun _ => rfl)
  have hidx : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        (boundedOutputStage c
          (betterStandardBlockAdviceM q.1.2) q.2).findIdx
            (fun y => decide
              (y = betterStandardLastMember c
                q.1.1 q.1.2 q.2))) :=
    Primrec.list_findIdx hstage
      ((PrimrecPred.decide
        (Primrec.eq.comp Primrec.snd
          (hlast.comp Primrec.fst))).to₂)
  have hp : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        2 ^ betterStandardBlockAdviceR q.1.2) :=
    Kolmogorov.CodedFiniteDistribution.twoPow_primrec.comp
      (hr.comp (Primrec.snd.comp Primrec.fst))
  have hstart : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        ((boundedOutputStage c
          (betterStandardBlockAdviceM q.1.2) q.2).findIdx
            (fun y => decide
              (y = betterStandardLastMember c
                q.1.1 q.1.2 q.2)) /
            2 ^ betterStandardBlockAdviceR q.1.2) *
              2 ^ betterStandardBlockAdviceR q.1.2) :=
    Primrec.nat_mul.comp
      (Primrec.nat_div.comp hidx hp) hp
  have hprevious : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        (boundedOutputStage c
          (betterStandardBlockAdviceM q.1.2) q.2).getD
            ((((boundedOutputStage c
              (betterStandardBlockAdviceM q.1.2) q.2).findIdx
                (fun y => decide
                  (y = betterStandardLastMember c
                    q.1.1 q.1.2 q.2)) /
                2 ^ betterStandardBlockAdviceR q.1.2) *
                  2 ^ betterStandardBlockAdviceR q.1.2) - 1) []) :=
    (Primrec.list_getD []).comp hstage
      (Primrec.pred.comp hstart)
  have hanchor : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        betterStandardAnchor c q.1.1 q.1.2 q.2) := by
    exact (Primrec.cond
      (hcurrent.comp (Primrec.snd.comp Primrec.fst))
      hlast hprevious).of_eq (fun q => by
        simp [betterStandardAnchor])
  have hadvice : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        standardBlockAdvice
          (betterStandardBlockAdviceM q.1.2)
          (betterStandardBlockAdviceR q.1.2)) := by
    unfold standardBlockAdvice
    exact pairCode_primrec.comp
      (primrecNatBits.comp
        (hm.comp (Primrec.snd.comp Primrec.fst)))
      (primrecNatBits.comp
        (hr.comp (Primrec.snd.comp Primrec.fst)))
  have hpost : Partrec₂
      (fun (q : BitString × BitString) (t : ℕ) =>
        standardBlockFromMemberSelector c
          (betterStandardAnchor c q.1 q.2 t)
          (standardBlockAdvice
            (betterStandardBlockAdviceM q.2)
            (betterStandardBlockAdviceR q.2))) := by
    exact ((standardBlockFromMemberSelector_partrec c).comp
      (hanchor.to_comp.pair hadvice.to_comp)).to₂
  unfold betterStandardBlockSelector
  exact (Partrec.bind hsearch hpost).of_eq (fun _ => rfl)

/-- Absorption: two `logSlack` terms in the same argument sum to one. -/
theorem logSlack_add_same (a b m : ℕ) :
    logSlack a m + logSlack b m = logSlack (a + b) m := by
  unfold logSlack; ring

/-- A constant below the slack constant is dominated by the whole slack. -/
theorem const_le_logSlack {k C m : ℕ} (h : k ≤ C) : k ≤ logSlack C m := by
  unfold logSlack; omega

/-- Composed selector for the length-filtered branch of `prop_better_std`.  The
paired advice carries the real block advice in its first component and `Nat.bits
n` in its second; the selector length-filters the conditioning model to `n`-bit
strings before running the block selector.  This lets the length-restricted
model be reconstructed from the *original* model code inside one selector. -/
noncomputable def betterStandardFilterSelector
    (c : Code) : BitString → BitString →. BitString :=
  fun ACode p =>
    betterStandardBlockSelector c
      (lengthFilterUniformCode (pairCode ACode (decodeSecond p)))
      (decodeFirst p)

theorem betterStandardFilterSelector_partrec (c : Code) :
    Partrec (fun q : BitString × BitString =>
      betterStandardFilterSelector c q.1 q.2) := by
  have hinner := Computable.pair (Computable.fst (α := BitString) (β := BitString))
    (decodeSecond_computable.comp (Computable.snd (α := BitString) (β := BitString)))
  have hpair := pairCode_computable.comp hinner
  have hpre := lengthFilterUniformCode_computable.comp hpair
  have hpost := decodeFirst_computable.comp (Computable.snd (α := BitString) (β := BitString))
  have hmap := Computable.pair hpre hpost
  have hcomp := (betterStandardBlockSelector_partrec c).comp hmap
  exact hcomp

/-- The last element selected by reversing a filtered duplicate-free list is a
filtered member at least as late as every specified filtered member. -/
theorem last_filtered_member_idxOf_ge
    (P : BitString → Bool) (L : List BitString) (hL : L.Nodup)
    (x : BitString) (hxL : x ∈ L) (hxP : P x = true) :
    let last := ((L.filter P).reverse).headI
    last ∈ L ∧ P last = true ∧ L.idxOf x ≤ L.idxOf last := by
  induction L generalizing x with
  | nil => simp at hxL
  | cons a L ih =>
      have hnodup := List.nodup_cons.mp hL
      rcases List.mem_cons.mp hxL with rfl | hxTail
      · by_cases htail : ∃ y ∈ L, P y = true
        · have hfilter : L.filter P ≠ [] := by
            simpa [List.filter_eq_nil_iff] using htail
          have hrev : (L.filter P).reverse ≠ [] := by
            simpa using hfilter
          obtain ⟨y, hy, hPy⟩ := htail
          have hlast := ih hnodup.2 y hy hPy
          rw [show (List.filter P (x :: L)).reverse =
              (L.filter P).reverse ++ [x] by simp [hxP]]
          rw [show (((L.filter P).reverse ++ [x]).headI) =
              ((L.filter P).reverse).headI by
            cases hq : (L.filter P).reverse with
            | nil => exact (hrev hq).elim
            | cons _ _ => rfl]
          dsimp only at hlast
          obtain ⟨hlastMem, hlastP, _⟩ := hlast
          have hlastNe : ((L.filter P).reverse).headI ≠ x := by
            intro heq
            exact hnodup.1 (heq.symm ▸ hlastMem)
          simp [hlastMem, hlastP,
            List.idxOf_cons_ne _ hlastNe.symm]
        · have hfilter : L.filter P = [] := by
            rw [List.filter_eq_nil_iff]
            exact fun y hy hPy => htail ⟨y, hy, hPy⟩
          simp [hxP, hfilter]
      · have hne : x ≠ a := fun h => hnodup.1 (h ▸ hxTail)
        have htailResult := ih hnodup.2 x hxTail hxP
        by_cases hPa : P a = true
        · by_cases hfilter : L.filter P = []
          · have hcontra : P x = false := by
              have := List.filter_eq_nil_iff.mp hfilter x hxTail
              simpa using this
            simp_all
          · have hrev : (L.filter P).reverse ≠ [] := by
              simpa using hfilter
            rw [show (List.filter P (a :: L)).reverse =
                (L.filter P).reverse ++ [a] by simp [hPa]]
            rw [show (((L.filter P).reverse ++ [a]).headI) =
                ((L.filter P).reverse).headI by
              cases hq : (L.filter P).reverse with
              | nil => exact (hrev hq).elim
              | cons _ _ => rfl]
            dsimp only at htailResult
            obtain ⟨hlastMem, hlastP, hidx⟩ := htailResult
            have hlastNe : ((L.filter P).reverse).headI ≠ a := by
              intro heq
              exact hnodup.1 (heq.symm ▸ hlastMem)
            refine ⟨List.mem_cons_of_mem _ hlastMem, hlastP, ?_⟩
            rw [List.idxOf_cons_ne _ hne.symm,
              List.idxOf_cons_ne _ hlastNe.symm]
            omega
        · have hPaf : P a = false := Bool.eq_false_iff.mpr hPa
          simp only [List.filter_cons_of_neg hPa]
          dsimp only at htailResult
          obtain ⟨hlastMem, hlastP, hidx⟩ := htailResult
          have hlastNe : ((L.filter P).reverse).headI ≠ a := by
            intro heq
            rw [heq] at hlastP
            simp [hPaf] at hlastP
          refine ⟨List.mem_cons_of_mem _ hlastMem, hlastP, ?_⟩
          rw [List.idxOf_cons_ne _ hne.symm,
            List.idxOf_cons_ne _ hlastNe.symm]
          omega

/-- Every completed-output element whose index is in the interval defining a
nonempty standard block belongs to that block. -/
theorem getElem_mem_standardBlock_of_bounds
    (c : Code) (m r : ℕ) (x : BitString)
    (hxB : x ∈ standardBlock c m r x)
    (k : ℕ)
    (hk : k < (completedBoundedOutput c m).length)
    (hlo :
      omegaCount c m / 2 ^ (r + 1) * 2 ^ (r + 1) ≤ k)
    (hhi :
      k < omegaCount c m / 2 ^ (r + 1) * 2 ^ (r + 1) + 2 ^ r) :
    (completedBoundedOutput c m)[k] ∈ standardBlock c m r x := by
  have hbit := standardBlock_testBit_of_mem c m r x hxB
  unfold standardBlock
  rw [if_pos hbit, List.mem_toFinset, List.mem_take_iff_getElem]
  let start :=
    omegaCount c m / 2 ^ (r + 1) * 2 ^ (r + 1)
  refine ⟨k - start, ?_, ?_⟩
  · simp only [List.length_drop]
    exact Nat.lt_min.mpr
      ⟨by dsimp [start]; omega, by dsimp [start]; omega⟩
  · have hsum : start + (k - start) = k := by omega
    rw [List.getElem_drop]
    change (completedBoundedOutput c m)[start + (k - start)] =
      (completedBoundedOutput c m)[k]
    exact getElem_congr rfl hsum _

/-- **Conditional selector geometry leaf for `prop:better-std`.**  From the
canonical code of any model `M` that contains `x` and whose members all appear
in the completed bound-`m` list, together with the `(m, r, flag)` advice, the
selector recovers the canonical code of the source-standard block containing
`x`.

* Let `L = completedBoundedOutput c m`, `sStart = (omegaCount c m / 2^(r+1)) * 2^(r+1)`,
  so `standardBlock c m r x = ((L.drop sStart).take (2^r)).toFinset` and
  `sStart ≤ L.idxOf x < sStart + 2^r` (`standardBlock_eq_completedDyadicBlock`,
  `standardBlock_start_add_size_le`).
* The `rfind` in `betterStandardBlockSelector` terminates: at
  `boundedOutputCompletionTime c m` every member of `M ⊆ L` has appeared
  (`exists_stage_covering_finset`), so `betterStandardModelSeen … = true`. Let
  `t₀` be its `Nat.find`; `boundedOutputStage c m t₀ <+: L`
  (`boundedOutputStage_prefix_completed`).
* `betterStandardLastMember … t₀` is the `M`-member of maximal index in `L`
  (last in enumeration order; the stage is a prefix and contains all of `M`).
  Call it `last`; since `x ∈ M`, `L.idxOf last ≥ L.idxOf x ≥ sStart`, and
  `L.idxOf last < omegaCount c m ≤ sStart + 2^(r+1)` (block fits + tail `< 2^r`).
* Choose `flag := decide (L.idxOf last < sStart + 2^r)`.  In both branches the
  `betterStandardAnchor` lands at an index in `[sStart, sStart + 2^r)`, hence in
  `standardBlock c m r x` (`standardBlock` ignores its last argument).
* Finish with `standardBlockFromMemberSelector_recovers c m r anchor _`; the
  block code is anchor-independent (`standardBlock c m r anchor =
  standardBlock c m r x`) and `codedUniformOn … .code` is independent of the
  nonemptiness witness. -/
theorem betterStandardBlockSelector_recovers
    (c : Code) (m r : ℕ) (x : BitString)
    (M : Finset BitString) (hM : M.Nonempty)
    (hxM : x ∈ M)
    (hsubset : ∀ y ∈ M, y ∈ completedBoundedOutput c m)
    (hxB : x ∈ standardBlock c m r x) :
    ∃ flag : Bool,
      (codedUniformOn (standardBlock c m r x) ⟨x, hxB⟩).code ∈
        betterStandardBlockSelector c
          (codedUniformOn M hM).code
          (betterStandardBlockAdvice m r flag) := by
  let ACode := (codedUniformOn M hM).code
  have hModelList :
      betterStandardModelList ACode = canonicalFinsetList M := by
    dsimp [ACode, betterStandardModelList]
    exact dataPoints_codedUniformOn M hM
  obtain ⟨tCover, htCover⟩ :=
    exists_stage_covering_finset c m M hsubset
  have hseenCover :
      betterStandardModelSeen c ACode
        (betterStandardBlockAdvice m r false) tCover = true := by
    rw [betterStandardModelSeen, betterStandardBlockAdviceM_advice,
      List.all_eq_true]
    intro y hy
    rw [List.elem_eq_mem, decide_eq_true_eq]
    apply htCover y
    exact mem_canonicalFinsetList.mp (hModelList ▸ hy)
  let hex : ∃ t,
      betterStandardModelSeen c ACode
        (betterStandardBlockAdvice m r false) t = true :=
    ⟨tCover, hseenCover⟩
  let t₀ := Nat.find hex
  have ht₀False :
      t₀ ∈ Nat.rfind (fun t => Part.some
        (betterStandardModelSeen c ACode
          (betterStandardBlockAdvice m r false) t)) := by
    refine Nat.mem_rfind.mpr ⟨by simpa using Nat.find_spec hex, ?_⟩
    intro t ht
    simpa using Nat.find_min hex ht
  let S := boundedOutputStage c m t₀
  let L := completedBoundedOutput c m
  have hseen :
      betterStandardModelSeen c ACode
        (betterStandardBlockAdvice m r false) t₀ = true :=
    Nat.find_spec hex
  have hMstage : ∀ y ∈ M, y ∈ S := by
    intro y hy
    have hyModel : y ∈ betterStandardModelList ACode := by
      rw [hModelList, mem_canonicalFinsetList]
      exact hy
    have hall := List.all_eq_true.mp hseen
    have hySeen := hall y hyModel
    simpa only [betterStandardModelSeen,
      betterStandardBlockAdviceM_advice, List.elem_eq_mem,
      decide_eq_true_eq, S] using hySeen
  have hxS : x ∈ S := hMstage x hxM
  have hSnodup : S.Nodup :=
    boundedOutputStage_nodup c m t₀
  let last := betterStandardLastMember c ACode
    (betterStandardBlockAdvice m r false) t₀
  have hlast :
      last ∈ S ∧ last ∈ betterStandardModelList ACode ∧
        S.idxOf x ≤ S.idxOf last := by
    have h :=
      last_filtered_member_idxOf_ge
        (fun y => decide (y ∈ betterStandardModelList ACode))
        S hSnodup x hxS (by simp [hModelList, hxM])
    simpa only [decide_eq_true_eq, last,
      betterStandardLastMember, betterStandardBlockAdviceM_advice, S] using h
  have hlastS : last ∈ S := hlast.1
  have hprefix : S <+: L :=
    boundedOutputStage_prefix_completed c m t₀
  have hlastL : last ∈ L := hprefix.sublist.subset hlastS
  let ix := S.idxOf x
  let il := S.idxOf last
  have hixEq : ix = L.idxOf x :=
    hprefix.idxOf_eq_of_mem hxS
  have hilEq : il = L.idxOf last :=
    hprefix.idxOf_eq_of_mem hlastS
  have hixil : ix ≤ il := hlast.2.2
  have hilLtS : il < S.length :=
    List.idxOf_lt_length_of_mem hlastS
  let p := 2 ^ r
  let start :=
    omegaCount c m / 2 ^ (r + 1) * 2 ^ (r + 1)
  have hpow : 2 ^ (r + 1) = 2 * p := by
    dsimp [p]
    rw [pow_succ']
  have hbit := standardBlock_testBit_of_mem c m r x hxB
  have hxBounds :
      start ≤ L.idxOf x ∧ L.idxOf x < start + p := by
    unfold standardBlock at hxB
    rw [if_pos hbit, List.mem_toFinset] at hxB
    have hnodupL : L.Nodup :=
      boundedOutputStage_nodup c m (maxHaltingStage c m)
    obtain ⟨k, hk, hkx⟩ :=
      List.mem_take_iff_getElem.mp hxB
    have hkP : k < p :=
      Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)
    have hglobal : start + k < L.length := by
      simp only [List.length_drop] at hk
      dsimp [start, p, L] at *
      omega
    have hidx : L.idxOf x = start + k := by
      have hi := hnodupL.idxOf_getElem (start + k) hglobal
      simp only [List.getElem_drop] at hkx
      rw [hkx] at hi
      exact hi
    omega
  have hstartIl : start ≤ il := by
    rw [hixEq] at hixil
    omega
  have hcountLt :
      omegaCount c m < start + 2 ^ (r + 1) := by
    have hmod := Nat.mod_lt (omegaCount c m)
      (show 0 < 2 ^ (r + 1) by positivity)
    have hdecomp :=
      Nat.mod_add_div (omegaCount c m) (2 ^ (r + 1))
    have hstart' :
        start =
          2 ^ (r + 1) *
            (omegaCount c m / 2 ^ (r + 1)) := by
      dsimp [start]
      ring
    rw [hstart']
    omega
  have hilLt : il < start + 2 ^ (r + 1) := by
    have hlenS : S.length ≤ L.length := hprefix.length_le
    have hlenL : L.length = omegaCount c m := rfl
    omega
  have hilLtL : il < L.length :=
    lt_of_lt_of_le hilLtS hprefix.length_le
  have hlastAt :
      L[il]'hilLtL = last := by
    have hidxLt : L.idxOf last < L.length :=
      List.idxOf_lt_length_of_mem hlastL
    have heq :
        L[il]'hilLtL = L[L.idxOf last]'hidxLt :=
      getElem_congr rfl hilEq hilLtL
    exact heq.trans (List.getElem_idxOf hidxLt)
  by_cases hcurrent : il < start + p
  · refine ⟨true, ?_⟩
    have ht₀ :
        t₀ ∈ Nat.rfind (fun t => Part.some
          (betterStandardModelSeen c ACode
            (betterStandardBlockAdvice m r true) t)) := by
      simpa only [betterStandardModelSeen,
        betterStandardBlockAdviceM_advice] using ht₀False
    have hlastBlock : last ∈ standardBlock c m r x := by
      have hmem :=
        getElem_mem_standardBlock_of_bounds c m r x hxB il
          (by rw [hilEq]
              exact List.idxOf_lt_length_of_mem hlastL)
          (by simpa [start] using hstartIl)
          (by simpa [start, p] using hcurrent)
      rw [hlastAt] at hmem
      exact hmem
    unfold betterStandardBlockSelector
    rw [Part.mem_bind_iff]
    refine ⟨t₀, ht₀, ?_⟩
    simp only [betterStandardAnchor,
      betterStandardBlockAdviceM_advice,
      betterStandardBlockAdviceR_advice,
      betterStandardBlockAdviceCurrent_advice, ↓reduceIte]
    have hlastTrue :
        betterStandardLastMember c ACode
            (betterStandardBlockAdvice m r true) t₀ =
          last := by
      dsimp [last]
      simp only [betterStandardLastMember,
        betterStandardBlockAdviceM_advice]
    rw [hlastTrue]
    have hrec :=
      standardBlockFromMemberSelector_recovers c m r last
        (by simpa only [standardBlock] using hlastBlock)
    simpa only [standardBlock] using hrec
  · refine ⟨false, ?_⟩
    have ht₀ :
        t₀ ∈ Nat.rfind (fun t => Part.some
          (betterStandardModelSeen c ACode
            (betterStandardBlockAdvice m r false) t)) :=
      ht₀False
    have hafter : start + p ≤ il := by omega
    let q := omegaCount c m / 2 ^ (r + 1)
    have hstart : start = (2 * q) * p := by
      dsimp [start, q]
      rw [hpow]
      ring
    have hilLt' : il < start + 2 * p := by
      rw [← hpow]
      exact hilLt
    have hilDiv : il / p = 2 * q + 1 := by
      apply Nat.div_eq_of_lt_le
      · calc
          (2 * q + 1) * p = start + p := by
            rw [hstart]
            ring
          _ ≤ il := hafter
      · calc
          il < start + 2 * p := hilLt'
          _ = (2 * q + 1 + 1) * p := by
            rw [hstart]
            ring
    have hblockStart :
        (S.findIdx (fun y => decide (y = last)) / p) * p =
          start + p := by
      rw [findIdx_decide_eq_eq_idxOf]
      change (il / p) * p = start + p
      rw [hilDiv, hstart]
      ring
    let k := start + p - 1
    have hkLtS : k < S.length := by
      dsimp [k]
      omega
    have hkLower : start ≤ k := by
      dsimp [k]
      omega
    have hkUpper : k < start + p := by
      dsimp [k]
      omega
    have hanchorEq :
        S.getD
            (((S.findIdx (fun y => decide (y = last)) / p) * p) - 1) [] =
          L[k]'(lt_of_lt_of_le hkLtS hprefix.length_le) := by
      rw [hblockStart]
      change S.getD k [] = _
      rw [List.getD_eq_getElem S [] hkLtS]
      exact hprefix.getElem hkLtS
    have hanchorBlock :
        S.getD
            (((S.findIdx (fun y => decide (y = last)) / p) * p) - 1) []
          ∈ standardBlock c m r x := by
      rw [hanchorEq]
      exact getElem_mem_standardBlock_of_bounds c m r x hxB k
        (lt_of_lt_of_le hkLtS hprefix.length_le)
        (by simpa [start] using hkLower)
        (by simpa [start, p] using hkUpper)
    unfold betterStandardBlockSelector
    rw [Part.mem_bind_iff]
    refine ⟨t₀, ht₀, ?_⟩
    simp only [betterStandardAnchor,
      betterStandardBlockAdviceM_advice,
      betterStandardBlockAdviceR_advice,
      betterStandardBlockAdviceCurrent_advice, Bool.false_eq_true,
      ↓reduceIte]
    have hrec :=
      standardBlockFromMemberSelector_recovers c m r
        (S.getD
          (((S.findIdx (fun y => decide (y = last)) / p) * p) - 1) [])
        (by simpa only [standardBlock] using hanchorBlock)
    simpa only [standardBlock] using hrec

/-- Proposition 4.11 (prop:better-std): For every description A for x there is a better
standard description that is simple given A. -/
theorem prop_better_std
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (n i j : ℕ)
      (A : Finset BitString) (hA : A.Nonempty),
      x.length = n →
      IsIJDescription U x A hA i j →
      ∃ (m r : ℕ) (hxB : x ∈ standardBlock c m r x),
        m ≤ min n (i + j) + logSlack C n ∧
        let B := standardBlock c m r x
        let hB : B.Nonempty := ⟨x, hxB⟩
        B.card = 2 ^ r ∧
        plainK V (codedUniformOn B hB).code ≤
          ((i + logSlack C m : ℕ) : ENat) ∧
        setComplexity U B hB ≤
          ((i + logSlack C m : ℕ) : ENat) ∧
        (m : ENat) ≤
          plainK V (codedUniformOn B hB).code + (r : ENat) +
            (logSlack C m : ENat) ∧
        plainK V (codedUniformOn B hB).code + (r : ENat) ≤
          (m : ENat) + (logSlack C m : ENat) ∧
        condK V (codedUniformOn B hB).code
          (codedUniformOn A hA).code ≤
            (logSlack C m : ENat) := by
  obtain ⟨Cpos, hpos⟩ := prop_std_pos V U hV hU c hc
  obtain ⟨Csuff, hsuff⟩ := suffixCoordinate_lower_of_model_code V hV c hc
  obtain ⟨Cmem, hmemC⟩ := mem_completed_of_isIJDescription V U hV hU c hc
  obtain ⟨Cbridge, hbridge⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨Cfilter, hfilterC⟩ := setComplexity_lengthFilteredModel_le U hU
  obtain ⟨Clen, hlenC⟩ := plainKLeLength V hV
  obtain ⟨Ccond0, hcond0⟩ :=
    condK_partrec_cond_map_le V hV
      (betterStandardBlockSelector c) (betterStandardBlockSelector_partrec c)
  obtain ⟨Ccond1, hcond1⟩ :=
    condK_partrec_cond_map_le V hV
      (betterStandardFilterSelector c) (betterStandardFilterSelector_partrec c)
  set Cq := Cfilter + Cbridge + 1 with hCq
  set C := Cpos + Csuff + Cq + Cmem + Cbridge + Cfilter + Clen + Ccond0 + Ccond1 + 20 with hC
  refine ⟨C, fun x n i j A hA hn hdesc => ?_⟩
  obtain ⟨hxA, hcompA, hcardA⟩ := hdesc
  -- Common assembly from any normalized model whose members lie in the completed list.
  have hCommon : ∀ (mm : ℕ) (M : Finset BitString) (hM : M.Nonempty) (qq : ℕ),
      x ∈ M →
      (∀ y ∈ M, y ∈ completedBoundedOutput c mm) →
      plainK V (codedUniformOn M hM).code ≤ (qq : ENat) →
      qq ≤ i + logSlack Cq mm →
      mm ≤ min n (i + j) + logSlack C n →
      (∀ (r : ℕ) (hxB : x ∈ standardBlock c mm r x),
        condK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code
          (codedUniformOn A hA).code ≤ (logSlack C mm : ENat)) →
      ∃ (m r : ℕ) (hxB : x ∈ standardBlock c m r x),
        m ≤ min n (i + j) + logSlack C n ∧
        (let B := standardBlock c m r x
         let hB : B.Nonempty := ⟨x, hxB⟩
         B.card = 2 ^ r ∧
         plainK V (codedUniformOn B hB).code ≤ ((i + logSlack C m : ℕ) : ENat) ∧
         setComplexity U B hB ≤ ((i + logSlack C m : ℕ) : ENat) ∧
         (m : ENat) ≤ plainK V (codedUniformOn B hB).code + (r : ENat) + (logSlack C m : ENat) ∧
         plainK V (codedUniformOn B hB).code + (r : ENat) ≤ (m : ENat) + (logSlack C m : ENat) ∧
         condK V (codedUniformOn B hB).code
            (codedUniformOn A hA).code ≤
              (logSlack C m : ENat)) := by
    intro mm M hM qq hxM hMsub hqM hqi hmMin hcondC
    have hxComp : x ∈ completedBoundedOutput c mm := hMsub x hxM
    obtain ⟨r, hxB⟩ := exists_standardBlock_of_mem_completed c mm x hxComp
    have hrm : r ≤ mm := standardBlock_exponent_le c mm r x hxB
    obtain ⟨hP1, hP2, hP3, hP4, hP5, hP6⟩ := hpos mm r x hxB
    have hsuffLower : 2 ^ (mm - qq - logSlack Csuff mm) ≤ suffixCoordinate c mm x :=
      hsuff mm qq x M hM hxM hMsub hqM
    have hgap : mm - r ≤ qq + logSlack Csuff mm :=
      standardBlock_gap_le_of_suffix_lower c mm r qq (logSlack Csuff mm) x hxB hsuffLower
    have hmr_le : mm - r ≤ i + logSlack (Cq + Csuff) mm := by
      calc mm - r ≤ qq + logSlack Csuff mm := hgap
        _ ≤ (i + logSlack Cq mm) + logSlack Csuff mm := Nat.add_le_add_right hqi _
        _ = i + (logSlack Cq mm + logSlack Csuff mm) := by ring
        _ = i + logSlack (Cq + Csuff) mm := by rw [logSlack_add_same]
    have hnat2 : mm - r + logSlack Cpos mm ≤ i + logSlack C mm := by
      calc mm - r + logSlack Cpos mm
          ≤ (i + logSlack (Cq + Csuff) mm) + logSlack Cpos mm := Nat.add_le_add_right hmr_le _
        _ = i + logSlack (Cq + Csuff + Cpos) mm := by rw [add_assoc, logSlack_add_same]
        _ ≤ i + logSlack C mm := Nat.add_le_add_left (logSlack_mono_left (by omega) mm) i
    have hslCpos : (logSlack Cpos mm : ENat) ≤ (logSlack C mm : ENat) := by
      exact_mod_cast logSlack_mono_left (show Cpos ≤ C by omega) mm
    refine ⟨mm, r, hxB, hmMin, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact card_standardBlock_of_mem c mm r x hxB
    · exact le_trans hP2 (by exact_mod_cast hnat2)
    · exact le_trans hP4 (by exact_mod_cast hnat2)
    · have h4a : (mm : ENat) ≤
          plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code
            + (logSlack Cpos mm : ENat) + (r : ENat) := by
        have h := add_le_add hP1 (le_refl (r : ENat))
        rwa [← Nat.cast_add, Nat.sub_add_cancel hrm] at h
      calc (mm : ENat)
          ≤ plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code
              + (logSlack Cpos mm : ENat) + (r : ENat) := h4a
        _ = plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code
              + (r : ENat) + (logSlack Cpos mm : ENat) := by rw [add_right_comm]
        _ ≤ plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code
              + (r : ENat) + (logSlack C mm : ENat) := add_le_add le_rfl hslCpos
    · calc plainK V (codedUniformOn (standardBlock c mm r x) ⟨x, hxB⟩).code + (r : ENat)
          ≤ ((mm - r + logSlack Cpos mm : ℕ) : ENat) + (r : ENat) := add_le_add hP2 le_rfl
        _ = ((mm - r + logSlack Cpos mm + r : ℕ) : ENat) := by rw [← Nat.cast_add]
        _ = ((mm + logSlack Cpos mm : ℕ) : ENat) := by congr 1; omega
        _ = (mm : ENat) + (logSlack Cpos mm : ENat) := by rw [Nat.cast_add]
        _ ≤ (mm : ENat) + (logSlack C mm : ENat) := add_le_add le_rfl hslCpos
    · exact hcondC r hxB
  -- Case split on whether the description already sits below length `n`.
  by_cases hcase : i + j ≤ n
  · -- Retain the original model.
    refine hCommon (i + j + logSlack Cmem j) A hA (i + Cbridge) hxA
      (fun y hy => hmemC x y i j A hA ⟨hxA, hcompA, hcardA⟩ hy) ?_ ?_ ?_ ?_
    · calc plainK V (codedUniformOn A hA).code
          ≤ setComplexity U A hA + (Cbridge : ENat) := hbridge (codedUniformOn A hA).code
        _ ≤ (i : ENat) + (Cbridge : ENat) := add_le_add hcompA le_rfl
        _ = ((i + Cbridge : ℕ) : ENat) := by rw [Nat.cast_add]
    · exact Nat.add_le_add_left (const_le_logSlack (by rw [hCq]; omega)) i
    · have h1 : logSlack Cmem j ≤ logSlack C n :=
        le_trans (logSlack_mono_right Cmem (by omega : j ≤ n)) (logSlack_mono_left (by omega) n)
      have hmin : min n (i + j) = i + j := by omega
      omega
    · intro r hxB
      have hrm : r ≤ i + j + logSlack Cmem j := standardBlock_exponent_le c _ r x hxB
      obtain ⟨flag, hrec⟩ :=
        betterStandardBlockSelector_recovers c (i + j + logSlack Cmem j) r x A hA hxA
          (fun y hy => hmemC x y i j A hA ⟨hxA, hcompA, hcardA⟩ hy) hxB
      have hcondbd :=
        hcond0 (codedUniformOn A hA).code
          (betterStandardBlockAdvice (i + j + logSlack Cmem j) r flag)
          (codedUniformOn (standardBlock c (i + j + logSlack Cmem j) r x) ⟨x, hxB⟩).code hrec
      refine le_trans hcondbd ?_
      rw [betterStandardBlockAdvice_length]
      have hLr : (Nat.bits r).length ≤ (Nat.bits (i + j + logSlack Cmem j)).length :=
        length_natBits_mono hrm
      have hCL : 4 * (Nat.bits (i + j + logSlack Cmem j)).length
          ≤ C * (Nat.bits (i + j + logSlack Cmem j)).length :=
        Nat.mul_le_mul (show 4 ≤ C by omega) (le_refl _)
      have hnat : 2 * (Nat.bits (i + j + logSlack Cmem j)).length
          + 2 * (Nat.bits r).length + 3 + Ccond0
            ≤ logSlack C (i + j + logSlack Cmem j) := by
        rw [show logSlack C (i + j + logSlack Cmem j)
              = C * (Nat.bits (i + j + logSlack Cmem j)).length + C from rfl]
        omega
      exact_mod_cast hnat
  · -- Length-filter the model to `n`-bit strings.
    push Not at hcase
    have hmemfilt : ∀ y, y ∈ lengthFilteredModel A n ↔ y ∈ A ∧ y.length = n := by
      intro y; simp only [lengthFilteredModel, Finset.mem_filter]
    have hxmem : x ∈ lengthFilteredModel A n := (hmemfilt x).mpr ⟨hxA, hn⟩
    have hA' : (lengthFilteredModel A n).Nonempty := ⟨x, hxmem⟩
    have hMsub : ∀ y ∈ lengthFilteredModel A n, y ∈ completedBoundedOutput c (n + Clen) := by
      intro y hy
      have hyn : y.length = n := ((hmemfilt y).mp hy).2
      have hyk : plainK V y ≤ ((n + Clen : ℕ) : ENat) := by
        calc plainK V y ≤ (programLength y : ENat) + (Clen : ENat) := hlenC y
          _ = ((n + Clen : ℕ) : ENat) := by
              simp only [programLength, hyn]; rw [Nat.cast_add]
      exact (mem_completedBoundedOutput_iff_plainK_le hc (n + Clen) y).mpr hyk
    refine hCommon (n + Clen) (lengthFilteredModel A n) hA'
      (i + logSlack Cfilter n + Cbridge) hxmem hMsub ?_ ?_ ?_ ?_
    · have hfilt : setComplexity U (lengthFilteredModel A n) hA'
          ≤ setComplexity U A hA + (logSlack Cfilter n : ENat) :=
        hfilterC A hA x n hxA hn
      calc plainK V (codedUniformOn (lengthFilteredModel A n) hA').code
          ≤ setComplexity U (lengthFilteredModel A n) hA' + (Cbridge : ENat) :=
            hbridge (codedUniformOn (lengthFilteredModel A n) hA').code
        _ ≤ (setComplexity U A hA + (logSlack Cfilter n : ENat)) + (Cbridge : ENat) :=
            add_le_add hfilt le_rfl
        _ ≤ ((i : ENat) + (logSlack Cfilter n : ENat)) + (Cbridge : ENat) :=
            add_le_add (add_le_add hcompA le_rfl) le_rfl
        _ = ((i + logSlack Cfilter n + Cbridge : ℕ) : ENat) := by
            rw [Nat.cast_add, Nat.cast_add]
    · have h1 : logSlack Cfilter n ≤ logSlack Cfilter (n + Clen) :=
        logSlack_mono_right Cfilter (by omega)
      have h2 : Cbridge ≤ logSlack Cbridge (n + Clen) := const_le_logSlack (le_refl _)
      have h3 : logSlack Cfilter (n + Clen) + logSlack Cbridge (n + Clen)
          = logSlack (Cfilter + Cbridge) (n + Clen) := logSlack_add_same _ _ _
      have h4 : logSlack (Cfilter + Cbridge) (n + Clen) ≤ logSlack Cq (n + Clen) :=
        logSlack_mono_left (by rw [hCq]; omega) (n + Clen)
      omega
    · have hmin : min n (i + j) = n := by omega
      have h1 : Clen ≤ logSlack C n := const_le_logSlack (by omega)
      omega
    · intro r hxB
      have hrm : r ≤ n + Clen := standardBlock_exponent_le c (n + Clen) r x hxB
      obtain ⟨flag, hrec⟩ :=
        betterStandardBlockSelector_recovers c (n + Clen) r x
          (lengthFilteredModel A n) hA' hxmem hMsub hxB
      have hAcode : (codedUniformOn (lengthFilteredModel A n) hA').code =
          lengthFilterUniformCode (pairCode (codedUniformOn A hA).code (Nat.bits n)) :=
        (lengthFilterUniformCode_eq A hA x n hxA hn).symm
      have hrec2 :
          (codedUniformOn (standardBlock c (n + Clen) r x) ⟨x, hxB⟩).code ∈
            betterStandardFilterSelector c (codedUniformOn A hA).code
              (pairCode (betterStandardBlockAdvice (n + Clen) r flag) (Nat.bits n)) := by
        unfold betterStandardFilterSelector
        rw [decodeFirst_pairCode, decodeSecond_pairCode, ← hAcode]
        exact hrec
      have hcondbd :=
        hcond1 (codedUniformOn A hA).code
          (pairCode (betterStandardBlockAdvice (n + Clen) r flag) (Nat.bits n))
          (codedUniformOn (standardBlock c (n + Clen) r x) ⟨x, hxB⟩).code hrec2
      refine le_trans hcondbd ?_
      rw [length_pairCode, betterStandardBlockAdvice_length]
      have hLr : (Nat.bits r).length ≤ (Nat.bits (n + Clen)).length := length_natBits_mono hrm
      have hLn : (Nat.bits n).length ≤ (Nat.bits (n + Clen)).length :=
        length_natBits_mono (by omega)
      have hCL : 9 * (Nat.bits (n + Clen)).length
          ≤ C * (Nat.bits (n + Clen)).length :=
        Nat.mul_le_mul (show 9 ≤ C by omega) (le_refl _)
      have hnat :
          (2 * (Nat.bits (n + Clen)).length + 2 * (Nat.bits r).length + 3) + 1
            + (2 * (Nat.bits (n + Clen)).length + 2 * (Nat.bits r).length + 3)
            + (Nat.bits n).length + Ccond1 ≤ logSlack C (n + Clen) := by
        unfold logSlack
        omega
      exact_mod_cast hnat

/-- The high `m-j` bits of `Ω_m` identify the source-standard block containing
`x`.  They decode to the quotient by `2^(j+1)`; multiplying that quotient by
two gives the aligned `2^j`-block index used by `completedDyadicBlockSelector`.
The factor of two is essential: the set `j` bit is the low bit of the block
index and is not present in the strict high prefix. -/
theorem completedDyadicBlockIndex_eq_two_mul_omegaPrefix
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    completedDyadicBlockIndex c m j x =
      2 * decodeFixedWidthNatCode
        ((omegaFixedCode c m).take (m - j)) := by
  let L := completedBoundedOutput c m
  let p := 2 ^ j
  let q := omegaCount c m / 2 ^ (j + 1)
  let start := q * 2 ^ (j + 1)
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hxList : x ∈ (L.drop start).take p := by
    unfold standardBlock at hx
    rw [if_pos hbit, List.mem_toFinset] at hx
    simpa [L, p, q, start] using hx
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hxList
  have hklt : k < p :=
    lt_of_lt_of_le hk (List.length_take_le p (L.drop start))
  have hglobal : start + k < L.length := by
    simp only [List.length_take, List.length_drop] at hk
    omega
  have hget : L[start + k] = x := by
    simpa only [List.getElem_take, List.getElem_drop] using hkx
  have hnodup : L.Nodup := by
    dsimp [L, completedBoundedOutput]
    exact boundedOutputStage_nodup c m (maxHaltingStage c m)
  have hidx :
      L.findIdx (· == x) = start + k := by
    change L.idxOf x = start + k
    rw [← hget]
    exact hnodup.idxOf_getElem (start + k) hglobal
  have hstart :
      start = (2 * q) * p := by
    dsimp [start, p]
    rw [pow_succ']
    ring
  have hquot :
      L.findIdx (· == x) / p = 2 * q := by
    apply Nat.div_eq_of_lt_le
    · rw [hidx, ← hstart]
      omega
    · rw [hidx]
      calc
        start + k < start + p := by omega
        _ = (2 * q + 1) * p := by rw [hstart]; ring
  have hjm := standardBlock_exponent_le c m j x hx
  have hdecode :
      decodeFixedWidthNatCode
          ((omegaFixedCode c m).take (m - j)) =
        q := by
    rw [decode_take_omegaFixedCode]
    have hsub : m + 1 - (m - j) = j + 1 := by omega
    rw [hsub]
  change L.findIdx (· == x) / p =
    2 * decodeFixedWidthNatCode
      ((omegaFixedCode c m).take (m - j))
  simpa [hdecode] using hquot

/-- From the high `m-j` bits of `Ω_m` and logarithmic advice `(m,j)`, build the
exact input expected by the completed-dyadic-block selector. -/
noncomputable def standardBlockFromOmegaPrefixSelector
    (c : Code) : BitString → BitString →. BitString := fun pref z =>
  completedDyadicBlockSelector c
    (completedDyadicBlockInput
      (standardBlockAdviceM z)
      (standardBlockAdviceJ z)
      (2 * decodeFixedWidthNatCode pref)
      (pref.length + 1))

theorem standardBlockFromOmegaPrefixSelector_partrec
    (c : Code) :
    Partrec (fun q : BitString × BitString =>
      standardBlockFromOmegaPrefixSelector c q.1 q.2) := by
  have hm : Primrec (fun q : BitString × BitString =>
      standardBlockAdviceM q.2) :=
    (bitsToNat_primrec.comp decodeFirst_primrec').comp Primrec.snd
  have hj : Primrec (fun q : BitString × BitString =>
      standardBlockAdviceJ q.2) :=
    (bitsToNat_primrec.comp decodeSecond_primrec').comp Primrec.snd
  have hdecode : Primrec (fun q : BitString × BitString =>
      decodeFixedWidthNatCode q.1) :=
    decodeFixedWidthNatCode_primrec.comp Primrec.fst
  have hidx : Primrec (fun q : BitString × BitString =>
      2 * decodeFixedWidthNatCode q.1) :=
    Primrec.nat_mul.comp (Primrec.const 2) hdecode
  have hwidth : Primrec (fun q : BitString × BitString =>
      q.1.length + 1) :=
    Primrec.nat_add.comp
      (Primrec.list_length.comp Primrec.fst)
      (Primrec.const 1)
  have hinput : Computable (fun q : BitString × BitString =>
      completedDyadicBlockInput
        (standardBlockAdviceM q.2)
        (standardBlockAdviceJ q.2)
        (2 * decodeFixedWidthNatCode q.1)
        (q.1.length + 1)) := by
    unfold completedDyadicBlockInput
    exact (pairCode_primrec.comp
      (pairCode_primrec.comp
        (primrecNatBits.comp hm)
        (primrecNatBits.comp hj))
      (fixedWidthNatCode_primrec.comp
        (Primrec.pair hidx hwidth))).to_comp
  unfold standardBlockFromOmegaPrefixSelector
  exact Partrec.comp (completedDyadicBlockSelector_partrec c) hinput

theorem standardBlockFromOmegaPrefixSelector_recovers
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
    (codedUniformOn (standardBlock c m j x) hA).code ∈
      standardBlockFromOmegaPrefixSelector c
        ((omegaFixedCode c m).take (m - j))
        (standardBlockAdvice m j) := by
  intro hA
  have hjm := standardBlock_exponent_le c m j x hx
  have hprefixLength :
      ((omegaFixedCode c m).take (m - j)).length = m - j := by
    rw [List.length_take, omegaFixedCode_length, Nat.min_eq_left]
    omega
  have hidx :=
    completedDyadicBlockIndex_eq_two_mul_omegaPrefix
      c m j x hx
  unfold standardBlockFromOmegaPrefixSelector
  simp only [standardBlockAdviceM_advice,
    standardBlockAdviceJ_advice, hprefixLength]
  rw [← hidx]
  simpa using
    (completedDyadicBlockSelector_recovers_standardBlock
      c m j x hx)

/-- The forward half of the block/high-prefix equivalence.  The high
`m-j`-bit prefix of `Ω_m`, together with self-delimiting advice `(m,j)`,
reconstructs the canonical standard-block code with logarithmic cost. -/
theorem condK_standardBlock_le_omegaPrefix
    (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      condK V
          (codedUniformOn (standardBlock c m j x) hA).code
          ((omegaFixedCode c m).take (m - j)) ≤
        (logSlack C m : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    condK_partrec_cond_map_le V hV
      (standardBlockFromOmegaPrefixSelector c)
      (standardBlockFromOmegaPrefixSelector_partrec c)
  let C := Cmap + 4
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  have hjm := standardBlock_exponent_le c m j x hx
  have hjBits :
      (Nat.bits j).length ≤ (Nat.bits m).length :=
    length_natBits_mono hjm
  have hrecover :=
    standardBlockFromOmegaPrefixSelector_recovers c m j x hx
  calc
    condK V
        (codedUniformOn (standardBlock c m j x) hA).code
        ((omegaFixedCode c m).take (m - j))
      ≤ ((standardBlockAdvice m j).length : ENat) +
          (Cmap : ENat) :=
        hmap ((omegaFixedCode c m).take (m - j))
          (standardBlockAdvice m j)
          (codedUniformOn (standardBlock c m j x) hA).code
          hrecover
    _ = (((standardBlockAdvice m j).length + Cmap : ℕ) : ENat) := by
      rw [Nat.cast_add]
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast (show
        (standardBlockAdvice m j).length + Cmap ≤
          logSlack C m by
        rw [standardBlockAdvice_length]
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits m).length)])

/-- Once a stage contains every member of a genuine standard block, its prefix
has reached at least the end of that block. -/
theorem standardBlock_end_le_stage_of_cover
    (c : Code) (m j t : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x)
    (hcover : ∀ y ∈ standardBlock c m j x,
      y ∈ boundedOutputStage c m t) :
    (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1) +
        2 ^ j ≤ (boundedOutputStage c m t).length := by
  let L := completedBoundedOutput c m
  let S := boundedOutputStage c m t
  let p := 2 ^ j
  let start :=
    (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1)
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hfit : start + p ≤ L.length := by
    change
      (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1) +
          2 ^ j ≤ omegaCount c m
    exact standardBlock_start_add_size_le hbit
  have hpPos : 0 < p := by
    dsimp [p]
    positivity
  let k := p - 1
  have hk : k < ((L.drop start).take p).length := by
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    · dsimp [k, p]
      omega
    · omega
  let y := ((L.drop start).take p)[k]
  have hySlice : y ∈ (L.drop start).take p :=
    List.getElem_mem hk
  have hyBlock : y ∈ standardBlock c m j x := by
    unfold standardBlock
    rw [if_pos hbit, List.mem_toFinset]
    simpa [L, start, p] using hySlice
  have hyS : y ∈ S := hcover y hyBlock
  have hprefix : S <+: L :=
    boundedOutputStage_prefix_completed c m t
  have hyIdxLt : L.idxOf y < S.length :=
    (hprefix.mem_iff_idxOf_lt_length y).mp hyS
  have hglobal : start + k < L.length := by
    have hkDrop : k < (L.drop start).length :=
      lt_of_lt_of_le hk (by simp)
    simp only [List.length_drop] at hkDrop
    omega
  have hyGet : L[start + k] = y := by
    dsimp [y]
    simp only [List.getElem_take, List.getElem_drop]
  have hnodup : L.Nodup := by
    dsimp [L, completedBoundedOutput]
    exact boundedOutputStage_nodup c m
      (maxHaltingStage c m)
  have hidx : L.idxOf y = start + k := by
    rw [← hyGet]
    exact hnodup.idxOf_getElem (start + k) hglobal
  change start + p ≤ S.length
  rw [hidx] at hyIdxLt
  dsimp [k] at hyIdxLt
  omega

/-- Given a canonical standard-block code and advice `(m,j)`, wait until every
block member has appeared and emit the final high quotient of `Ω_m`. -/
noncomputable def omegaPrefixFromStandardBlockSelector
    (c : Code) : BitString → BitString →. BitString := fun SCode z =>
  let SList :=
    (decodeDistributionData SCode).map
      CodedDistributionEntry.point
  (Nat.rfind (fun t => Part.some
    (SList.all (fun y =>
      decide
        (y ∈ boundedOutputStage c
          (standardBlockAdviceM z) t))))).bind
    (fun t => Part.some
      (fixedWidthNatCode
        ((boundedOutputStage c
          (standardBlockAdviceM z) t).length /
            2 ^ (standardBlockAdviceJ z + 1))
        (standardBlockAdviceM z - standardBlockAdviceJ z)))

theorem omegaPrefixFromStandardBlockSelector_partrec
    (c : Code) :
    Partrec (fun q : BitString × BitString =>
      omegaPrefixFromStandardBlockSelector c q.1 q.2) := by
  have hm : Primrec standardBlockAdviceM :=
    bitsToNat_primrec.comp decodeFirst_primrec'
  have hj : Primrec standardBlockAdviceJ :=
    bitsToNat_primrec.comp decodeSecond_primrec'
  have hSList : Primrec (fun q : BitString × BitString =>
      (decodeDistributionData q.1).map
        CodedDistributionEntry.point) :=
    Primrec.list_map
      (decodeDistributionData_primrec.comp Primrec.fst)
      (entry_point_primrec.comp Primrec.snd).to₂
  have hstage : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        boundedOutputStage c
          (standardBlockAdviceM q.1.2) q.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair
        ((hm.comp Primrec.snd).comp Primrec.fst)
        Primrec.snd)
  have hcheck : Computable₂
      (fun (q : BitString × BitString) (t : ℕ) =>
        (decodeDistributionData q.1).map
            CodedDistributionEntry.point |>.all
          (fun y =>
            decide (y ∈ boundedOutputStage c
              (standardBlockAdviceM q.2) t))) := by
    have hpred : Primrec₂
        (fun (q : (BitString × BitString) × ℕ)
          (y : BitString) =>
          decide (y ∈ boundedOutputStage c
            (standardBlockAdviceM q.1.2) q.2)) :=
      (bitString_mem_primrec.comp Primrec.snd
        (hstage.comp Primrec.fst)).to₂
    have hall : Primrec
        (fun q : (BitString × BitString) × ℕ =>
          (decodeDistributionData q.1.1).map
              CodedDistributionEntry.point |>.all
            (fun y => decide
              (y ∈ boundedOutputStage c
                (standardBlockAdviceM q.1.2) q.2))) :=
      list_all_primrec (hSList.comp Primrec.fst) hpred
    exact hall.to_comp.to₂
  have hsearch : Partrec (fun q : BitString × BitString =>
      Nat.rfind (fun t => Part.some
        ((decodeDistributionData q.1).map
            CodedDistributionEntry.point |>.all
          (fun y =>
            decide (y ∈ boundedOutputStage c
              (standardBlockAdviceM q.2) t))))) :=
    Partrec.rfind hcheck.partrec₂
  have hlen : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        (boundedOutputStage c
          (standardBlockAdviceM q.1.2) q.2).length) :=
    Primrec.list_length.comp hstage
  have hjSucc : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        standardBlockAdviceJ q.1.2 + 1) :=
    Primrec.nat_add.comp
      ((hj.comp Primrec.snd).comp Primrec.fst)
      (Primrec.const 1)
  have hpow : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        2 ^ (standardBlockAdviceJ q.1.2 + 1)) :=
    Kolmogorov.CodedFiniteDistribution.twoPow_primrec.comp
      hjSucc
  have hquot : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        (boundedOutputStage c
          (standardBlockAdviceM q.1.2) q.2).length /
            2 ^ (standardBlockAdviceJ q.1.2 + 1)) :=
    Primrec.nat_div.comp hlen hpow
  have hwidth : Primrec
      (fun q : (BitString × BitString) × ℕ =>
        standardBlockAdviceM q.1.2 -
          standardBlockAdviceJ q.1.2) :=
    Primrec.nat_sub.comp
      ((hm.comp Primrec.snd).comp Primrec.fst)
      ((hj.comp Primrec.snd).comp Primrec.fst)
  have hresult : Computable₂
      (fun (q : BitString × BitString) (t : ℕ) =>
        fixedWidthNatCode
          ((boundedOutputStage c
            (standardBlockAdviceM q.2) t).length /
              2 ^ (standardBlockAdviceJ q.2 + 1))
          (standardBlockAdviceM q.2 -
            standardBlockAdviceJ q.2)) :=
    (fixedWidthNatCode_primrec.comp
      (Primrec.pair hquot hwidth)).to_comp.to₂
  unfold omegaPrefixFromStandardBlockSelector
  exact Partrec.bind hsearch hresult.partrec₂

theorem omegaPrefixFromStandardBlockSelector_recovers
    (c : Code) (m j : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x) :
    let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
    (omegaFixedCode c m).take (m - j) ∈
      omegaPrefixFromStandardBlockSelector c
        (codedUniformOn (standardBlock c m j x) hA).code
        (standardBlockAdvice m j) := by
  intro hA
  let B := standardBlock c m j x
  let SCode := (codedUniformOn B hA).code
  let SList := canonicalFinsetList B
  have hSList :
      SList =
        (decodeDistributionData SCode).map
          CodedDistributionEntry.point :=
    (dataPoints_codedUniformOn B hA).symm
  have hsubset :
      ∀ y ∈ SList, y ∈ completedBoundedOutput c m := by
    intro y hy
    apply List.mem_toFinset.mp
    exact standardBlock_subset_completed c m j x
      (mem_canonicalFinsetList.mp hy)
  have hex :
      ∃ t, SList.all (fun y =>
        decide (y ∈ boundedOutputStage c m t)) = true := by
    obtain ⟨t, ht⟩ :=
      exists_stage_covering_finset c m B
        (fun y hy => hsubset y
          (mem_canonicalFinsetList.mpr hy))
    refine ⟨t, ?_⟩
    rw [List.all_eq_true]
    intro y hy
    exact decide_eq_true
      (ht y (mem_canonicalFinsetList.mp hy))
  let t₀ := Nat.find hex
  have ht₀spec :
      SList.all (fun y =>
        decide (y ∈ boundedOutputStage c m t₀)) = true :=
    Nat.find_spec hex
  have ht₀mem :
      t₀ ∈ Nat.rfind (fun t => Part.some
        (SList.all (fun y =>
          decide (y ∈ boundedOutputStage c m t)))) := by
    refine Nat.mem_rfind.mpr ⟨by simpa using ht₀spec, ?_⟩
    intro t ht
    simpa using Nat.find_min hex ht
  have hcover :
      ∀ y ∈ standardBlock c m j x,
        y ∈ boundedOutputStage c m t₀ := by
    rw [List.all_eq_true] at ht₀spec
    intro y hy
    simpa using
      ht₀spec y (mem_canonicalFinsetList.mpr hy)
  have hendAt :=
    standardBlock_end_le_stage_of_cover
      c m j t₀ x hx hcover
  have hstageLe :
      (boundedOutputStage c m t₀).length ≤
        omegaCount c m :=
    (boundedOutputStage_prefix_completed c m t₀).length_le
  let q := omegaCount c m / 2 ^ (j + 1)
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hdecomp := standardBlock_end_add_tail c m j hbit
  have htailLt :
      standardBlockTail c m j < 2 ^ j := by
    have h := standardBlockTail_add_one_le c m j
    omega
  have hlower :
      q * 2 ^ (j + 1) + 2 ^ j ≤
        (boundedOutputStage c m t₀).length := by
    simpa [q] using hendAt
  have hupper :
      (boundedOutputStage c m t₀).length <
        (q + 1) * 2 ^ (j + 1) := by
    have homega :
        omegaCount c m =
          q * 2 ^ (j + 1) + 2 ^ j +
            standardBlockTail c m j := by
      simpa [q] using hdecomp.symm
    calc
      (boundedOutputStage c m t₀).length
          ≤ omegaCount c m := hstageLe
      _ = q * 2 ^ (j + 1) + 2 ^ j +
          standardBlockTail c m j := homega
      _ < q * 2 ^ (j + 1) + 2 ^ j + 2 ^ j :=
        Nat.add_lt_add_left htailLt _
      _ = (q + 1) * 2 ^ (j + 1) := by
        rw [pow_succ']
        ring
  have hquot :
      (boundedOutputStage c m t₀).length /
          2 ^ (j + 1) =
        q := by
    apply Nat.div_eq_of_lt_le
    · omega
    · exact hupper
  have hjm := standardBlock_exponent_le c m j x hx
  have hsub : m + 1 - (m - j) = j + 1 := by omega
  have hpref :
      (omegaFixedCode c m).take (m - j) =
        fixedWidthNatCode q (m - j) := by
    rw [omegaFixedCode_take_eq c m (show m - j ≤ m + 1 by omega)]
    rw [hsub]
  unfold omegaPrefixFromStandardBlockSelector
  rw [Part.mem_bind_iff]
  refine ⟨t₀, ?_, ?_⟩
  · simpa [SCode, B, hSList] using ht₀mem
  · simp only [standardBlockAdviceM_advice,
      standardBlockAdviceJ_advice]
    rw [hquot, ← hpref]
    exact Part.mem_some _

/-- The reverse half of the block/high-prefix equivalence. -/
theorem condK_omegaPrefix_le_standardBlock
    (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      condK V
          ((omegaFixedCode c m).take (m - j))
          (codedUniformOn (standardBlock c m j x) hA).code ≤
        (logSlack C m : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    condK_partrec_cond_map_le V hV
      (omegaPrefixFromStandardBlockSelector c)
      (omegaPrefixFromStandardBlockSelector_partrec c)
  let C := Cmap + 4
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  have hjm := standardBlock_exponent_le c m j x hx
  have hjBits :
      (Nat.bits j).length ≤ (Nat.bits m).length :=
    length_natBits_mono hjm
  have hrecover :=
    omegaPrefixFromStandardBlockSelector_recovers c m j x hx
  calc
    condK V
        ((omegaFixedCode c m).take (m - j))
        (codedUniformOn (standardBlock c m j x) hA).code
      ≤ ((standardBlockAdvice m j).length : ENat) +
          (Cmap : ENat) :=
        hmap
          (codedUniformOn (standardBlock c m j x) hA).code
          (standardBlockAdvice m j)
          ((omegaFixedCode c m).take (m - j))
          hrecover
    _ = (((standardBlockAdvice m j).length + Cmap : ℕ) : ENat) := by
      rw [Nat.cast_add]
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast (show
        (standardBlockAdvice m j).length + Cmap ≤
          logSlack C m by
        rw [standardBlockAdvice_length]
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits m).length)])

/-- A genuine standard block and the high `m-j` bits of the same finite Omega
count determine one another with uniform logarithmic advice. -/
theorem standardBlock_omegaPrefix_equiv
    (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      condK V
          (codedUniformOn (standardBlock c m j x) hA).code
          ((omegaFixedCode c m).take (m - j)) ≤
          (logSlack C m : ENat) ∧
      condK V
          ((omegaFixedCode c m).take (m - j))
          (codedUniformOn (standardBlock c m j x) hA).code ≤
          (logSlack C m : ENat) := by
  obtain ⟨C₁, hforward⟩ :=
    condK_standardBlock_le_omegaPrefix V hV c
  obtain ⟨C₂, hreverse⟩ :=
    condK_omegaPrefix_le_standardBlock V hV c
  refine ⟨C₁ + C₂, fun m j x hx => ?_⟩
  intro hA
  have hslack₁ :
      logSlack C₁ m ≤ logSlack (C₁ + C₂) m :=
    logSlack_mono_left (Nat.le_add_right C₁ C₂) m
  have hslack₂ :
      logSlack C₂ m ≤ logSlack (C₁ + C₂) m :=
    logSlack_mono_left (Nat.le_add_left C₂ C₁) m
  constructor
  · exact (hforward m j x hx).trans (by
      exact_mod_cast hslack₁)
  · exact (hreverse m j x hx).trans (by
      exact_mod_cast hslack₂)

/-- Plain-machine-only form of the standard-block index estimate.  Unlike the
profile-facing `standardBlock_plainK_index_close` below, this lemma needs no
prefix machine: its lower bound is the direct finite-Omega reconstruction
inequality and its upper bound is the explicit standard-block encoder. -/
theorem standardBlock_plainK_index_close_plain
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j i : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code =
            (i : ENat) →
      i ≤ m - j + logSlack C m ∧
      m - j ≤ i + logSlack C m := by
  obtain ⟨Ccoding, hcoding⟩ :=
    standardBlock_omega_coding_bound V hV c hc
  obtain ⟨Cplain, hplain⟩ :=
    plainK_standardBlock_upper V hV c hc
  let C := Ccoding + Cplain
  refine ⟨C, fun m j i x hx => ?_⟩
  intro hA hplainEq
  have htailLt :
      standardBlockTail c m j < 2 ^ j := by
    have h := standardBlockTail_add_one_le c m j
    omega
  have htailBits :
      (Nat.bits (standardBlockTail c m j)).length ≤ j :=
    length_natBits_lt_pow htailLt
  have hcodingNat :
      m ≤ i +
        (Nat.bits (standardBlockTail c m j)).length +
        logSlack Ccoding m := by
    have h := hcoding m j x hx
    rw [hplainEq] at h
    exact_mod_cast h
  have hupperNat :
      i ≤ m - j + logSlack Cplain m := by
    have h := hplain m j x hx
    change plainK V
      (codedUniformOn (standardBlock c m j x) hA).code ≤
        ((m - j + logSlack Cplain m : ℕ) : ENat) at h
    rw [hplainEq] at h
    exact_mod_cast h
  have hcodingSlack :
      logSlack Ccoding m ≤ logSlack C m :=
    logSlack_mono_left (by dsimp [C]; omega) m
  have hplainSlack :
      logSlack Cplain m ≤ logSlack C m :=
    logSlack_mono_left (by dsimp [C]; omega) m
  exact ⟨by omega, by omega⟩

/-- If the canonical code of a genuine standard block has exact plain
complexity `i`, then `i` is logarithmically close to its position parameter
`m-j`. -/
theorem standardBlock_plainK_index_close
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j i : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code =
            (i : ENat) →
      i ≤ m - j + logSlack C m ∧
      m - j ≤ i + logSlack C m := by
  obtain ⟨C, hpos⟩ := prop_std_pos V U hV hU c hc
  refine ⟨C, fun m j i x hx => ?_⟩
  intro hA hplain
  have hbounds := hpos m j x hx
  change
      ((m - j : ℕ) : ENat) ≤
          plainK V
            (codedUniformOn (standardBlock c m j x) hA).code +
            (logSlack C m : ENat) ∧
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code ≤
            ((m - j + logSlack C m : ℕ) : ENat) ∧
      _ at hbounds
  rw [hplain] at hbounds
  have hlower :
      m - j ≤ i + logSlack C m := by
    exact_mod_cast hbounds.1
  have hupper :
      i ≤ m - j + logSlack C m := by
    exact_mod_cast hbounds.2.1
  exact ⟨hupper, hlower⟩

/-- A two-stage plain conditional decompressor.  Its program is a concrete
pair of programs: the first produces an intermediate string from the original
condition and the second produces the final string from that intermediate
condition. -/
def conditionalComposeDecompressor (V : Map) : Map := fun pr =>
  (V (decodeFirst pr.1, pr.2)).bind fun y =>
    V (decodeSecond pr.1, y)

theorem conditionalComposeDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    Partrec (conditionalComposeDecompressor V) := by
  have hfirst :
      Partrec (fun pr : BitString × BitString =>
        V (decodeFirst pr.1, pr.2)) :=
    Partrec.comp hV
      (Computable.pair
        (decodeFirst_computable.comp Computable.fst)
        Computable.snd)
  have hsecond :
      Partrec (fun q : (BitString × BitString) × BitString =>
        V (decodeSecond q.1.1, q.2)) :=
    Partrec.comp hV
      (Computable.pair
        (decodeSecond_computable.comp
          (Computable.fst.comp Computable.fst))
        Computable.snd)
  exact Partrec.bind hfirst hsecond

/-- Plain conditional complexity is transitive with the explicit overhead of
the concrete self-delimiting pair of the two witness programs.  The factor two
on the first bound is the unary length header in `pairCode`. -/
theorem condK_trans_nat
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (x y z : BitString) (a b : ℕ),
      condK V y x ≤ (a : ENat) →
      condK V z y ≤ (b : ENat) →
      condK V z x ≤ ((2 * a + b + C : ℕ) : ENat) := by
  obtain ⟨C, hC⟩ :=
    hV.2 (conditionalComposeDecompressor V)
      (conditionalComposeDecompressor_partrec V hV.1)
  refine ⟨C + 1, fun x y z a b hxy hyz => ?_⟩
  obtain ⟨p, hpLen, hp⟩ :=
    (condKLeIff V y x a).mp hxy
  obtain ⟨q, hqLen, hq⟩ :=
    (condKLeIff V z y b).mp hyz
  change p.length ≤ a at hpLen
  change q.length ≤ b at hqLen
  change y ∈ V (p, x) at hp
  change z ∈ V (q, y) at hq
  have hprod :
      produces (conditionalComposeDecompressor V)
        (pairCode p q) x z := by
    unfold produces conditionalComposeDecompressor
    rw [Part.mem_bind_iff]
    refine ⟨y, ?_, ?_⟩
    · rw [decodeFirst_pairCode]
      exact hp
    · rw [decodeSecond_pairCode]
      exact hq
  calc
    condK V z x ≤
        condK (conditionalComposeDecompressor V) z x +
          (C : ENat) := hC z x
    _ ≤ ((pairCode p q).length : ENat) + (C : ENat) := by
      gcongr
      exact sInf_le ⟨pairCode p q, hprod, rfl⟩
    _ ≤ ((2 * a + b + (C + 1) : ℕ) : ENat) := by
      rw [length_pairCode]
      exact_mod_cast (show
        p.length + 1 + p.length + q.length + C ≤
          2 * a + b + (C + 1) by omega)

/-- A condition can be truncated to any requested prefix using only the binary
code of the requested length as advice. -/
def takePrefixSelector (y p : BitString) : Part BitString :=
  Part.some (y.take (bitsToNat p))

theorem takePrefixSelector_partrec :
    Partrec (fun q : BitString × BitString =>
      takePrefixSelector q.1 q.2) := by
  exact (Primrec.list_take.comp (bitsToNat_primrec.comp Primrec.snd)
    Primrec.fst).to_comp.partrec

theorem condK_take_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (y : BitString) (k : ℕ),
      condK V (y.take k) y ≤
        (((Nat.bits k).length + C : ℕ) : ENat) := by
  obtain ⟨C, hC⟩ :=
    condK_partrec_cond_map_le V hV
      takePrefixSelector takePrefixSelector_partrec
  refine ⟨C, fun y k => ?_⟩
  have hmem :
      y.take k ∈ takePrefixSelector y (Nat.bits k) := by
    simp [takePrefixSelector, bitsToNat_bits]
  simpa [Nat.cast_add] using hC y (Nat.bits k) (y.take k) hmem

/-- A string is reconstructible from one of its prefixes by supplying the
literal remaining suffix as the plain advice program. -/
def appendSuffixSelector (y p : BitString) : Part BitString :=
  Part.some (y ++ p)

theorem appendSuffixSelector_partrec :
    Partrec (fun q : BitString × BitString =>
      appendSuffixSelector q.1 q.2) := by
  exact (Primrec.list_append.comp Primrec.fst Primrec.snd).to_comp.partrec

theorem condK_of_take_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ (y : BitString) (k : ℕ),
      condK V y (y.take k) ≤
        (((y.drop k).length + C : ℕ) : ENat) := by
  obtain ⟨C, hC⟩ :=
    condK_partrec_cond_map_le V hV
      appendSuffixSelector appendSuffixSelector_partrec
  refine ⟨C, fun y k => ?_⟩
  have hmem :
      y ∈ appendSuffixSelector (y.take k) (y.drop k) := by
    simp [appendSuffixSelector]
  simpa [Nat.cast_add] using
    hC (y.take k) (y.drop k) y hmem

/-- Finite Omega codes at logarithmically close indices determine each other
with logarithmic advice.  This is the explicit nearby-index bridge needed when
the exact plain complexity of a standard block is slightly above or below its
position coordinate `m-j`. -/
theorem omegaFixedCode_close_logSlack
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ (m a b : ℕ),
      a ≤ m + logSlack C₀ m →
      b ≤ m + logSlack C₀ m →
      a ≤ b + logSlack C₀ m →
      b ≤ a + logSlack C₀ m →
      condK V (omegaFixedCode c a) (omegaFixedCode c b) ≤
          (logSlack C m : ENat) ∧
      condK V (omegaFixedCode c b) (omegaFixedCode c a) ≤
          (logSlack C m : ENat) := by
  obtain ⟨Ceq, heq⟩ :=
    prop_omega_equivalence V hV c hc
  obtain ⟨Ctake, htake⟩ := condK_take_le V hV
  obtain ⟨Cdrop, hdrop⟩ := condK_of_take_le V hV
  obtain ⟨Ctrans, htrans⟩ := condK_trans_nat V hV
  let C₁ :=
    (Ceq + 2) * (C₀ + 2) +
      2 * Ctake + Ceq + Ctrans
  let C₂ :=
    (2 * Ceq + 1) * (C₀ + 2) +
      2 * Ceq + Cdrop + Ctrans + 1
  let C := C₁ + C₂
  refine ⟨C, fun m a b haM hbM hab hba => ?_⟩
  let S := logSlack C₀ m
  let H := logSlack (C₀ + 2) m
  have hS : S ≤ H := by
    exact logSlack_mono_left (by omega) m
  have hbits_of_le :
      ∀ q, q ≤ m + S → (Nat.bits q).length ≤ H := by
    intro q hq
    calc
      (Nat.bits q).length
          ≤ (Nat.bits (m + S)).length :=
        length_natBits_mono hq
      _ ≤ (Nat.bits m).length +
          (Nat.bits S).length + 1 :=
        length_natBits_add_le m S
      _ ≤ (Nat.bits m).length + S + 1 := by
        gcongr
        exact length_natBits_le_self S
      _ ≤ H := by
        dsimp [H, S]
        unfold logSlack
        calc
          (Nat.bits m).length +
              (C₀ * (Nat.bits m).length + C₀) + 1
            = (C₀ + 1) * (Nat.bits m).length + (C₀ + 1) := by ring
          _ ≤ (C₀ + 2) * (Nat.bits m).length + (C₀ + 2) := by
            gcongr <;> omega
  have hC₁ : C₁ ≤ C := by
    dsimp [C]
    omega
  have hC₂ : C₂ ≤ C := by
    dsimp [C]
    omega
  have hforward_of_le :
      ∀ {lo hi : ℕ}, lo ≤ hi →
        lo ≤ m + S → hi ≤ m + S →
        hi ≤ lo + S →
        condK V (omegaFixedCode c lo)
            (omegaFixedCode c hi) ≤
          (logSlack C m : ENat) := by
    intro lo hi hlohi hloM hhiM hhilo
    let pref := (omegaFixedCode c hi).take lo
    have htakeNat :
        condK V pref (omegaFixedCode c hi) ≤
          (((Nat.bits lo).length + Ctake : ℕ) : ENat) := by
      simpa [pref] using htake (omegaFixedCode c hi) lo
    have heqNat :
        condK V (omegaFixedCode c lo) pref ≤
          (logSlack Ceq hi : ENat) := by
      simpa [pref] using (heq hi lo hlohi).1
    have hcomposed :=
      htrans (omegaFixedCode c hi) pref
        (omegaFixedCode c lo)
        ((Nat.bits lo).length + Ctake)
        (logSlack Ceq hi)
        htakeNat heqNat
    have hloBits := hbits_of_le lo hloM
    have hhiBits := hbits_of_le hi hhiM
    have hbudget :
        2 * ((Nat.bits lo).length + Ctake) +
            logSlack Ceq hi + Ctrans ≤
          logSlack C m := by
      have hbase :
          2 * ((Nat.bits lo).length + Ctake) +
              logSlack Ceq hi + Ctrans ≤
            logSlack C₁ m := by
        have hcoefficient :
            (Ceq + 2) * (C₀ + 2) ≤ C₁ := by
          dsimp [C₁]
          omega
        calc
          2 * ((Nat.bits lo).length + Ctake) +
                logSlack Ceq hi + Ctrans
              = 2 * (Nat.bits lo).length + 2 * Ctake +
                  (Ceq * (Nat.bits hi).length + Ceq) +
                  Ctrans := by
                unfold logSlack
                ring
          _ ≤ 2 * H + 2 * Ctake +
                (Ceq * H + Ceq) + Ctrans := by
              gcongr
          _ = (Ceq + 2) * (C₀ + 2) *
                  (Nat.bits m).length + C₁ := by
                dsimp [H, C₁]
                unfold logSlack
                ring
          _ ≤ C₁ * (Nat.bits m).length + C₁ :=
            Nat.add_le_add
              (Nat.mul_le_mul_right
                (Nat.bits m).length hcoefficient)
              le_rfl
          _ = logSlack C₁ m := by
            unfold logSlack
            ring
      exact hbase.trans (logSlack_mono_left hC₁ m)
    exact hcomposed.trans (by exact_mod_cast hbudget)
  have hreverse_of_le :
      ∀ {lo hi : ℕ}, lo ≤ hi →
        lo ≤ m + S → hi ≤ m + S →
        hi ≤ lo + S →
        condK V (omegaFixedCode c hi)
            (omegaFixedCode c lo) ≤
          (logSlack C m : ENat) := by
    intro lo hi hlohi hloM hhiM hhilo
    let pref := (omegaFixedCode c hi).take lo
    have heqNat :
        condK V pref (omegaFixedCode c lo) ≤
          (logSlack Ceq hi : ENat) := by
      simpa [pref] using (heq hi lo hlohi).2
    have hdropNat :
        condK V (omegaFixedCode c hi) pref ≤
          ((((omegaFixedCode c hi).drop lo).length +
            Cdrop : ℕ) : ENat) := by
      simpa [pref] using hdrop (omegaFixedCode c hi) lo
    have hcomposed :=
      htrans (omegaFixedCode c lo) pref
        (omegaFixedCode c hi)
        (logSlack Ceq hi)
        (((omegaFixedCode c hi).drop lo).length + Cdrop)
        heqNat hdropNat
    have hhiBits := hbits_of_le hi hhiM
    have hdropLen :
        ((omegaFixedCode c hi).drop lo).length ≤ S + 1 := by
      rw [List.length_drop, omegaFixedCode_length]
      omega
    have hbudget :
        2 * logSlack Ceq hi +
            (((omegaFixedCode c hi).drop lo).length + Cdrop) +
            Ctrans ≤
          logSlack C m := by
      have hbase :
          2 * logSlack Ceq hi +
              (((omegaFixedCode c hi).drop lo).length + Cdrop) +
              Ctrans ≤
            logSlack C₂ m := by
        have hcoefficient :
            2 * Ceq * (C₀ + 2) + C₀ ≤ C₂ := by
          dsimp [C₂]
          calc
            2 * Ceq * (C₀ + 2) + C₀
                ≤ 2 * Ceq * (C₀ + 2) + (C₀ + 2) +
                    2 * Ceq + Cdrop + Ctrans + 1 := by
                  omega
            _ = (2 * Ceq + 1) * (C₀ + 2) +
                  2 * Ceq + Cdrop + Ctrans + 1 := by
                ring
        have hconstant :
            2 * Ceq * (C₀ + 2) + 2 * Ceq + C₀ + 1 +
                Cdrop + Ctrans ≤
              C₂ := by
          dsimp [C₂]
          calc
            2 * Ceq * (C₀ + 2) + 2 * Ceq + C₀ + 1 +
                  Cdrop + Ctrans
                ≤ 2 * Ceq * (C₀ + 2) + (C₀ + 2) +
                    2 * Ceq + Cdrop + Ctrans + 1 := by
                  omega
            _ = (2 * Ceq + 1) * (C₀ + 2) +
                  2 * Ceq + Cdrop + Ctrans + 1 := by
                ring
        calc
          2 * logSlack Ceq hi +
                (((omegaFixedCode c hi).drop lo).length + Cdrop) +
                Ctrans
              = 2 * (Ceq * (Nat.bits hi).length + Ceq) +
                  ((omegaFixedCode c hi).drop lo).length +
                  Cdrop + Ctrans := by
                unfold logSlack
                ring
          _ ≤ 2 * (Ceq * H + Ceq) +
                (S + 1) + Cdrop + Ctrans := by
              gcongr
          _ = (2 * Ceq * (C₀ + 2) + C₀) *
                  (Nat.bits m).length +
                (2 * Ceq * (C₀ + 2) + 2 * Ceq + C₀ + 1 +
                  Cdrop + Ctrans) := by
                dsimp [H, S]
                unfold logSlack
                ring
          _ ≤ C₂ * (Nat.bits m).length + C₂ :=
            Nat.add_le_add
              (Nat.mul_le_mul_right
                (Nat.bits m).length hcoefficient)
              hconstant
          _ = logSlack C₂ m := by
            unfold logSlack
            ring
      exact hbase.trans (logSlack_mono_left hC₂ m)
    exact hcomposed.trans (by exact_mod_cast hbudget)
  by_cases hab' : a ≤ b
  · exact ⟨
      hforward_of_le hab'
        (by simpa [S] using haM)
        (by simpa [S] using hbM)
        (by simpa [S] using hba),
      hreverse_of_le hab'
        (by simpa [S] using haM)
        (by simpa [S] using hbM)
        (by simpa [S] using hba)⟩
  · have hba' : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab')
    exact ⟨
      hreverse_of_le hba'
        (by simpa [S] using hbM)
        (by simpa [S] using haM)
        (by simpa [S] using hab),
      hforward_of_le hba'
        (by simpa [S] using hbM)
        (by simpa [S] using haM)
        (by simpa [S] using hab)⟩

/-- Finite Omega codes at a linear gap determine one another with linear advice.
This is the explicit bridge needed for the minimal-model hereditary property. -/
theorem omegaFixedCode_bridge_linear
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ (m a b : ℕ),
      a ≤ m + logSlack C₀ m →
      b ≤ m + logSlack C₀ m →
      condK V (omegaFixedCode c a) (omegaFixedCode c b) ≤
          ((a - b) + logSlack C m : ENat) := by
  obtain ⟨Ceq, heq⟩ := prop_omega_equivalence V hV c hc
  obtain ⟨Ctake, htake⟩ := condK_take_le V hV
  obtain ⟨Cdrop, hdrop⟩ := condK_of_take_le V hV
  obtain ⟨Ctrans, htrans⟩ := condK_trans_nat V hV
  let C₁ := (Ceq + 2) * (C₀ + 2) + 2 * Ctake + Ceq + Ctrans + 2
  let C₂ := 2 * Ceq * (C₀ + 2) + Cdrop + Ctrans + 2 * Ceq + 2
  let C := C₁ + C₂
  refine ⟨C, fun m a b haM hbM => ?_⟩
  let S := logSlack C₀ m
  let H := logSlack (C₀ + 2) m
  have hS : S ≤ H := logSlack_mono_left (by omega) m
  have hbits_of_le : ∀ q, q ≤ m + S → (Nat.bits q).length ≤ H := by
    intro q hq
    calc
      (Nat.bits q).length ≤ (Nat.bits (m + S)).length := length_natBits_mono hq
      _ ≤ (Nat.bits m).length + (Nat.bits S).length + 1 := length_natBits_add_le m S
      _ ≤ (Nat.bits m).length + S + 1 := by gcongr; exact length_natBits_le_self S
      _ ≤ H := by
        dsimp [H, S]; unfold logSlack
        calc (Nat.bits m).length + (C₀ * (Nat.bits m).length + C₀) + 1
          = (C₀ + 1) * (Nat.bits m).length + (C₀ + 1) := by ring
        _ ≤ (C₀ + 2) * (Nat.bits m).length + (C₀ + 2) := by gcongr <;> omega
  by_cases hab : a ≤ b
  · let pref := (omegaFixedCode c b).take a
    have htakeNat : condK V pref (omegaFixedCode c b) ≤
        (((Nat.bits a).length + Ctake : ℕ) : ENat) := by
      simpa [pref] using htake (omegaFixedCode c b) a
    have heqNat : condK V (omegaFixedCode c a) pref ≤ (logSlack Ceq b : ENat) := by
      simpa [pref] using (heq b a hab).1
    have hcomposed := htrans (omegaFixedCode c b) pref (omegaFixedCode c a)
      ((Nat.bits a).length + Ctake) (logSlack Ceq b) htakeNat heqNat
    have hbudget : (a - b) + 2 * ((Nat.bits a).length + Ctake) + logSlack Ceq b + Ctrans ≤
        (a - b) + logSlack C₁ m := by
      have hab_zero : a - b = 0 := Nat.sub_eq_zero_of_le hab
      rw [hab_zero, zero_add, zero_add]
      calc 2 * ((Nat.bits a).length + Ctake) + logSlack Ceq b + Ctrans
        = 2 * (Nat.bits a).length + 2 * Ctake +
          (Ceq * (Nat.bits b).length + Ceq) + Ctrans := by unfold logSlack; omega
        _ ≤ 2 * H + 2 * Ctake + (Ceq * H + Ceq) + Ctrans := by
          gcongr
          · exact hbits_of_le a haM
          · exact hbits_of_le b hbM
        _ = (Ceq + 2) * H + 2 * Ctake + Ceq + Ctrans := by ring
        _ = (Ceq + 2) * ( (C₀ + 2) * (Nat.bits m).length + (C₀ + 2) ) +
            2 * Ctake + Ceq + Ctrans := by dsimp [H]; unfold logSlack; rfl
        _ = (Ceq + 2) * (C₀ + 2) * (Nat.bits m).length +
            ( (Ceq + 2) * (C₀ + 2) + 2 * Ctake + Ceq + Ctrans ) := by ring
        _ ≤ C₁ * (Nat.bits m).length + C₁ := by
          apply Nat.add_le_add
          · apply Nat.mul_le_mul_right; dsimp [C₁]; omega
          · dsimp [C₁]; omega
        _ = logSlack C₁ m := by unfold logSlack; rfl
    have hC : logSlack C₁ m ≤ logSlack C m := logSlack_mono_left (by dsimp [C, C₁, C₂]; omega) m
    calc condK V (omegaFixedCode c a) (omegaFixedCode c b)
      ≤ ↑(2 * ((Nat.bits a).length + Ctake) + logSlack Ceq b + Ctrans) := hcomposed
      _ = ↑((a - b) + 2 * ((Nat.bits a).length + Ctake) + logSlack Ceq b + Ctrans) := by
          have hab_zero : a - b = 0 := Nat.sub_eq_zero_of_le hab
          rw [hab_zero, zero_add]
      _ ≤ ((a - b) + logSlack C m : ENat) := by
          exact_mod_cast (hbudget.trans (Nat.add_le_add_left hC _))
  · have hba : b ≤ a := Nat.le_of_lt (not_le.mp hab)
    let pref := (omegaFixedCode c a).take b
    have hdropNat : condK V (omegaFixedCode c a) pref ≤
        ((((omegaFixedCode c a).drop b).length + Cdrop : ℕ) : ENat) := by
      simpa [pref] using hdrop (omegaFixedCode c a) b
    have heqNat : condK V pref (omegaFixedCode c b) ≤ (logSlack Ceq a : ENat) := by
      simpa [pref] using (heq a b hba).2
    have hcomposed := htrans (omegaFixedCode c b) pref (omegaFixedCode c a)
      (logSlack Ceq a) (((omegaFixedCode c a).drop b).length + Cdrop) heqNat hdropNat
    have hdropLen : ((omegaFixedCode c a).drop b).length = (a - b) + 1 := by
      rw [List.length_drop, omegaFixedCode_length]
      omega
    have hbudget : 2 * logSlack Ceq a + (((omegaFixedCode c a).drop b).length + Cdrop) +
        Ctrans ≤ (a - b) + logSlack C₂ m := by
      rw [hdropLen]
      calc 2 * logSlack Ceq a + (a - b + 1 + Cdrop) + Ctrans
        = (a - b) + (2 * logSlack Ceq a + 1 + Cdrop + Ctrans) := by omega
        _ ≤ (a - b) + (2 * (Ceq * H + Ceq) + 1 + Cdrop + Ctrans) := by
          unfold logSlack; gcongr; exact hbits_of_le a haM
        _ = (a - b) + (2 * Ceq * H + 2 * Ceq + 1 + Cdrop + Ctrans) := by ring
        _ = (a - b) + (2 * Ceq * ((C₀ + 2) * (Nat.bits m).length + (C₀ + 2)) +
            2 * Ceq + 1 + Cdrop + Ctrans) := by dsimp [H]; unfold logSlack; rfl
        _ = (a - b) + (2 * Ceq * (C₀ + 2) * (Nat.bits m).length +
            (2 * Ceq * (C₀ + 2) + 2 * Ceq + 1 + Cdrop + Ctrans)) := by ring
        _ ≤ (a - b) + (C₂ * (Nat.bits m).length + C₂) := by
          apply Nat.add_le_add_left
          apply Nat.add_le_add
          · apply Nat.mul_le_mul_right; dsimp [C₂]; omega
          · dsimp [C₂]; omega
        _ = (a - b) + logSlack C₂ m := by unfold logSlack; rfl
    have hC : logSlack C₂ m ≤ logSlack C m := logSlack_mono_left (by dsimp [C, C₁, C₂]; omega) m
    calc condK V (omegaFixedCode c a) (omegaFixedCode c b)
      ≤ ↑(2 * logSlack Ceq a + (((omegaFixedCode c a).drop b).length + Cdrop) + Ctrans) := hcomposed
      _ ≤ ((a - b) + logSlack C m : ENat) := by
          exact_mod_cast (hbudget.trans (Nat.add_le_add_left hC _))

/-- Proposition `prop:std-omega`.  If a standard block has exact plain
complexity `i`, its canonical code and the fixed-width finite Omega code
`omegaFixedCode c i` determine one another with uniform plain conditional
advice. -/
theorem prop_std_omega
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j i : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code =
            (i : ENat) →
      condK V (codedUniformOn (standardBlock c m j x) hA).code
          (omegaFixedCode c i) ≤ (logSlack C m : ENat) ∧
      condK V (omegaFixedCode c i)
          (codedUniformOn (standardBlock c m j x) hA).code ≤
            (logSlack C m : ENat) := by
  obtain ⟨Cclose, hclose⟩ :=
    standardBlock_plainK_index_close_plain V hV c hc
  obtain ⟨Cblock, hblock⟩ :=
    standardBlock_omegaPrefix_equiv V hV c
  obtain ⟨Comega, homega⟩ :=
    prop_omega_equivalence V hV c hc
  obtain ⟨Cnear, hnear⟩ :=
    omegaFixedCode_close_logSlack V hV c hc Cclose
  obtain ⟨Ctrans, htrans⟩ :=
    condK_trans_nat V hV
  let C :=
    4 * (Cnear + Cblock + Comega + Ctrans + 1)
  refine ⟨C, fun m j i x hx => ?_⟩
  intro hA hplain
  let k := m - j
  let BCode :=
    (codedUniformOn (standardBlock c m j x) hA).code
  let pref := (omegaFixedCode c m).take k
  let omegaK := omegaFixedCode c k
  let omegaI := omegaFixedCode c i
  have hkM : k ≤ m := by
    dsimp [k]
    omega
  have hidx := hclose m j i x hx hplain
  have hiUpper :
      i ≤ m + logSlack Cclose m := by
    omega
  have hkUpper :
      k ≤ m + logSlack Cclose m := by
    omega
  have hnearKI :
      condK V omegaK omegaI ≤
          (logSlack Cnear m : ENat) ∧
      condK V omegaI omegaK ≤
          (logSlack Cnear m : ENat) := by
    apply hnear m k i hkUpper hiUpper
    · simpa [k] using hidx.2
    · simpa [k] using hidx.1
  have homegaKP :
      condK V omegaK pref ≤
          (logSlack Comega m : ENat) ∧
      condK V pref omegaK ≤
          (logSlack Comega m : ENat) := by
    simpa [omegaK, pref, k] using homega m k hkM
  have hblockBP :
      condK V BCode pref ≤
          (logSlack Cblock m : ENat) ∧
      condK V pref BCode ≤
          (logSlack Cblock m : ENat) := by
    simpa [BCode, pref, k] using hblock m j x hx
  have hOmegaIToPref :
      condK V pref omegaI ≤
        ((2 * logSlack Cnear m +
          logSlack Comega m + Ctrans : ℕ) : ENat) :=
    htrans omegaI omegaK pref
      (logSlack Cnear m) (logSlack Comega m)
      hnearKI.1 homegaKP.2
  have hOmegaIToBlock :
      condK V BCode omegaI ≤
        ((2 * (2 * logSlack Cnear m +
          logSlack Comega m + Ctrans) +
          logSlack Cblock m + Ctrans : ℕ) : ENat) :=
    htrans omegaI pref BCode
      (2 * logSlack Cnear m +
        logSlack Comega m + Ctrans)
      (logSlack Cblock m)
      hOmegaIToPref hblockBP.1
  have hBlockToOmegaK :
      condK V omegaK BCode ≤
        ((2 * logSlack Cblock m +
          logSlack Comega m + Ctrans : ℕ) : ENat) :=
    htrans BCode pref omegaK
      (logSlack Cblock m) (logSlack Comega m)
      hblockBP.2 homegaKP.1
  have hBlockToOmegaI :
      condK V omegaI BCode ≤
        ((2 * (2 * logSlack Cblock m +
          logSlack Comega m + Ctrans) +
          logSlack Cnear m + Ctrans : ℕ) : ENat) :=
    htrans BCode omegaK omegaI
      (2 * logSlack Cblock m +
        logSlack Comega m + Ctrans)
      (logSlack Cnear m)
      hBlockToOmegaK hnearKI.2
  have hbudget₁ :
      2 * (2 * logSlack Cnear m +
          logSlack Comega m + Ctrans) +
          logSlack Cblock m + Ctrans ≤
        logSlack C m := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le (Cnear * (Nat.bits m).length),
      Nat.zero_le (Cblock * (Nat.bits m).length),
      Nat.zero_le (Comega * (Nat.bits m).length)]
  have hbudget₂ :
      2 * (2 * logSlack Cblock m +
          logSlack Comega m + Ctrans) +
          logSlack Cnear m + Ctrans ≤
        logSlack C m := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le (Cnear * (Nat.bits m).length),
      Nat.zero_le (Cblock * (Nat.bits m).length),
      Nat.zero_le (Comega * (Nat.bits m).length)]
  exact ⟨
    hOmegaIToBlock.trans (by exact_mod_cast hbudget₁),
    hBlockToOmegaI.trans (by exact_mod_cast hbudget₂)⟩

theorem condK_chain_five
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ x₀ x₁ x₂ x₃ x₄ x₅ (a₁ a₂ a₃ a₄ a₅ : Nat),
      condK V x₁ x₀ ≤ (a₁ : ENat) →
      condK V x₂ x₁ ≤ (a₂ : ENat) →
      condK V x₃ x₂ ≤ (a₃ : ENat) →
      condK V x₄ x₃ ≤ (a₄ : ENat) →
      condK V x₅ x₄ ≤ (a₅ : ENat) →
      condK V x₅ x₀ ≤
        ((16*a₁ + 8*a₂ + 4*a₃ + 2*a₄ + a₅ + C : Nat) : ENat) := by
  obtain ⟨C, hC⟩ := condK_trans_nat V hV
  use 15 * C
  intro x₀ x₁ x₂ x₃ x₄ x₅ a₁ a₂ a₃ a₄ a₅ h1 h2 h3 h4 h5
  have h20 := hC x₀ x₁ x₂ a₁ a₂ h1 h2
  have h30 := hC x₀ x₂ x₃ _ a₃ h20 h3
  have h40 := hC x₀ x₃ x₄ _ a₄ h30 h4
  have h50 := hC x₀ x₄ x₅ _ a₅ h40 h5
  apply le_trans h50
  norm_cast
  omega

end Kolmogorov
