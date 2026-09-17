import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile.Part01
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile

/-! # Geometry of standard blocks
Defines aligned dyadic blocks and proves their size, membership, containment and tail formulas. -/

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
    · simp only [show start + (idx - start) = idx by omega, hx_eq, L]
      rfl
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
    conv_lhs => rw [List.getElem_drop]
    simp only [show start + (idx - start) = idx by omega, L]
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

/-- A source-standard block containing `x` is the aligned completed dyadic block
containing `x`. -/
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
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · exact Part.mem_some_iff.mpr (decide_eq_true (Nat.find_spec hex)).symm
    · intro t ht
      exact Part.mem_some_iff.mpr (decide_eq_false (Nat.find_min hex ht)).symm
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

/-- The code of the uniform distribution on a standard block of exponent `j` inside the bound-`m`
enumeration has plain complexity at most `m - j` plus a logarithmic term in `m`. -/
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
  obtain ⟨Clen, hlen⟩ := plainK_le_length V hV
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

/-- Extracts the list bound `m` from a standard-block advice string. -/
def standardBlockAdviceM (z : BitString) : ℕ :=
  bitsToNat (decodeFirst z)

/-- Extracts the block exponent `j` from a standard-block advice string. -/
def standardBlockAdviceJ (z : BitString) : ℕ :=
  bitsToNat (decodeSecond z)

/-- Decoding the list bound of the advice for `(m, j)` returns `m`. -/
@[simp] theorem standardBlockAdviceM_advice (m j : ℕ) :
    standardBlockAdviceM (standardBlockAdvice m j) = m := by
  unfold standardBlockAdviceM standardBlockAdvice
  rw [decodeFirst_pairCode, bitsToNat_bits]

/-- Decoding the block exponent of the advice for `(m, j)` returns `j`. -/
@[simp] theorem standardBlockAdviceJ_advice (m j : ℕ) :
    standardBlockAdviceJ (standardBlockAdvice m j) = j := by
  unfold standardBlockAdviceJ standardBlockAdvice
  rw [decodeSecond_pairCode, bitsToNat_bits]

/-- The standard-block advice for `(m, j)` costs twice the bits of `m` plus the bits of `j` plus
one. -/
theorem standardBlockAdvice_length (m j : ℕ) :
    (standardBlockAdvice m j).length =
      2 * (Nat.bits m).length + (Nat.bits j).length + 1 := by
  unfold standardBlockAdvice
  rw [length_pairCode]
  omega

/-- Tests whether by stage `t` the bound-`m` enumeration already contains `x` and has completed the
aligned block of size `2 ^ j` containing it. -/
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

/-- The selector that recovers a standard block from one of its members is partial recursive. -/
theorem standardBlockFromMemberSelector_partrec
    (c : Code) :
    Partrec (fun q : BitString × BitString =>
      standardBlockFromMemberSelector c q.1 q.2) := by
  have hm : Primrec standardBlockAdviceM :=
    bitsToNat_primrec.comp decodeFirst_primrec
  have hj : Primrec standardBlockAdviceJ :=
    bitsToNat_primrec.comp decodeSecond_primrec
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
    Kolmogorov.primrec_two_pow_aux.comp hj'
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
    Primrec.list_take.comp hp
      (Primrec.list_drop.comp hstart hstage)
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

/-- Searching a list for the first entry equal to `x` returns the index of `x`. -/
theorem findIdx_decide_eq_eq_idxOf
    (L : List BitString) (x : BitString) :
    L.findIdx (fun y => decide (y = x)) = L.idxOf x := by
  unfold List.idxOf
  congr 1
  funext y
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]

/-- Run on a member `x` and the advice for `(m, j)`, the selector outputs the code of the uniform
distribution on the standard block of `x`. -/
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
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · exact Part.mem_some_iff.mpr (Nat.find_spec hex).symm
    · intro t ht
      exact Part.mem_some_iff.mpr (Bool.eq_false_iff.mpr (Nat.find_min hex ht)).symm
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

end Kolmogorov
