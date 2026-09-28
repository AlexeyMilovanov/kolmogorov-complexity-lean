import KolmogorovMathlib.MonotoneComplexity.GacsDayV2BlockLayout

/-!
# V2 advantage wide-slot layout (Reading C)

Blueprint Stage C1, audit verdict Reading C: advantage round `r` runs, per
active source-son pair `(i, c)`, a WIDE block of `grayAdvBlockMult q L r`
distinct grandson coordinates, laid out at the cumulative offset
`grayAdvBlockOffset q L r`.  All grandsons are genuine `Fin b` values (a slice
of `List.finRange b`), so no manual bound threading is needed; disjointness
across rounds reuses `nodup_slice_disjoint`.

This is the wide analogue of the flattened `grayTailSlots` (which used the
single grandson `r`).  The round index is no longer readable off the grandson
coordinate — it is carried by the V2 round metadata; here the grandsons of
round `r` occupy the disjoint window `[offset r, offset r + mult r)`.
-/

namespace Kolmogorov

/-- The grandson coordinates of round `r`'s advantage block: the slice
`[offset r, offset r + mult r)` of `List.finRange b`. -/
def grayAdvBlockGrandsons (b q L r : Nat) : List (Fin b) :=
  ((List.finRange b).drop (grayAdvBlockOffset q L r)).take (grayAdvBlockMult q L r)

/-- The grandchildren of an adversary block are listed without repetition. -/
lemma grayAdvBlockGrandsons_nodup (b q L r : Nat) :
    (grayAdvBlockGrandsons b q L r).Nodup :=
  (List.nodup_finRange b).drop.take

/-- Every grandson of round `r`'s block lies in the round's offset window. -/
lemma grayAdvBlockGrandsons_mem_range {b q L r : Nat} {g : Fin b}
    (hg : g ∈ grayAdvBlockGrandsons b q L r) :
    grayInAdvBlock q L r g.val := by
  rw [grayAdvBlockGrandsons] at hg
  obtain ⟨k, hk, hgk⟩ := List.mem_iff_getElem.mp hg
  rw [List.length_take, List.length_drop, List.length_finRange] at hk
  have hkmult : k < grayAdvBlockMult q L r := lt_of_lt_of_le hk (Nat.min_le_left _ _)
  have hkfin : k < b - grayAdvBlockOffset q L r :=
    lt_of_lt_of_le hk (Nat.min_le_right _ _)
  have hval : g.val = grayAdvBlockOffset q L r + k := by
    rw [← hgk]
    simp [List.getElem_take, List.getElem_drop, List.getElem_finRange]
  refine ⟨by omega, by omega⟩

/-- Grandsons of two distinct rounds are disjoint (offset windows disjoint). -/
lemma grayAdvBlockGrandsons_disjoint {b q L r r' : Nat} (hrr : r < r') :
    List.Disjoint (grayAdvBlockGrandsons b q L r)
      (grayAdvBlockGrandsons b q L r') := by
  apply nodup_slice_disjoint (List.nodup_finRange b)
  have hstep : grayAdvBlockOffset q L r + grayAdvBlockMult q L r =
      grayAdvBlockOffset q L (r + 1) := (grayAdvBlockOffset_succ q L r).symm
  have hmono : grayAdvBlockOffset q L (r + 1) ≤ grayAdvBlockOffset q L r' :=
    grayAdvBlockOffset_mono (by omega)
  omega

/-- The wide advantage slots of round `r`: for every source index `i < n` and
source son `c < used`, the whole grandson block of round `r`. -/
def grayAdvBlockSlots (n b used q L r : Nat) : List (GrayTailSlot n b) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange b).filter fun c => c.val < used).flatMap fun c =>
      (grayAdvBlockGrandsons b q L r).map fun g => (i, c, g)

/-- The block-slot count factors as fibres × grandson block. -/
lemma grayAdvBlockGrandsons_length {b q L r : Nat}
    (hfit : grayAdvBlockOffset q L r + grayAdvBlockMult q L r ≤ b) :
    (grayAdvBlockGrandsons b q L r).length = grayAdvBlockMult q L r := by
  rw [grayAdvBlockGrandsons, List.length_take, List.length_drop,
    List.length_finRange, Nat.min_eq_left (by omega)]

/-- Every slot of round `r`'s wide block has a source son `< used` and a
grandson in the round's block range — the data the V2 shape invariant records
(the wide analogue of `slots_round`). -/
lemma grayAdvBlockSlots_mem {n b used q L r : Nat} {sl : GrayTailSlot n b}
    (hsl : sl ∈ grayAdvBlockSlots n b used q L r) :
    sl.2.1.val < used ∧ grayInAdvBlock q L r sl.2.2.val := by
  rw [grayAdvBlockSlots, List.mem_flatMap] at hsl
  obtain ⟨i, -, hsl⟩ := hsl
  rw [List.mem_flatMap] at hsl
  obtain ⟨c, hc, hsl⟩ := hsl
  rw [List.mem_map] at hsl
  obtain ⟨g, hg, rfl⟩ := hsl
  exact ⟨by simpa using (List.mem_filter.mp hc).2,
    grayAdvBlockGrandsons_mem_range hg⟩

/-- **The wide advantage block is nodup.**  Mirrors `grayTailSlots_nodup` with
the extra grandson layer discharged by the nodup grandson slice. -/
lemma grayAdvBlockSlots_nodup (n b used q L r : Nat) :
    (grayAdvBlockSlots n b used q L r).Nodup := by
  unfold grayAdvBlockSlots
  refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
  · intro i _
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro c _
      exact (grayAdvBlockGrandsons_nodup b q L r).map fun g g' h =>
        by exact congrArg (fun p => p.2.2) h
    · refine ((List.nodup_finRange b).filter _).imp ?_
      intro c c' hcc x hxc hxc'
      simp only [List.mem_map] at hxc hxc'
      obtain ⟨gc, _, rfl⟩ := hxc
      obtain ⟨gc', _, h⟩ := hxc'
      exact hcc (congrArg (fun p => p.2.1) h).symm
  · refine (List.nodup_finRange n).imp ?_
    intro i j hij x hxi hxj
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_finRange] at hxi hxj
    obtain ⟨ci, _, gi, _, rfl⟩ := hxi
    obtain ⟨cj, _, gj, _, h⟩ := hxj
    exact hij (congrArg Prod.fst h).symm

/-! ## Capacity facts for used rounds (round < advCount) -/

/-- Every adversary block has positive multiplicity. -/
lemma grayAdvBlockMult_pos (q L r : Nat) : 0 < grayAdvBlockMult q L r := by
  unfold grayAdvBlockMult; positivity

/-- `roundCount ≤ baseBranch`. -/
lemma grayTailRoundCount_le_baseBranch (q L : Nat) :
    grayTailRoundCount q ≤ grayTailBaseBranch q L := by
  rw [grayTailRoundCount]
  refine le_trans ?_ (le_max_right 2 _)
  have hpow : (q + 1) ≤ 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) := by
    have h1 : q + 1 ≤ 2 ^ (q + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
    exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  calc 256 * (q + 1) ^ 2 = 256 * (q + 1) * (q + 1) := by ring
    _ ≤ 256 * (q + 1) * 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) :=
        Nat.mul_le_mul_left _ hpow

/-- A used round's grandson block fits inside the branching. -/
lemma grayAdvBlock_fit_of_lt_advCount {q L a e round : Nat}
    (h : round < grayChargedAdvantageRoundCount q) :
    grayAdvBlockOffset q L round + grayAdvBlockMult q L round ≤
      grayTailBranch q L a e := by
  have hstep : grayAdvBlockOffset q L round + grayAdvBlockMult q L round =
      grayAdvBlockOffset q L (round + 1) := (grayAdvBlockOffset_succ q L round).symm
  have hmono : grayAdvBlockOffset q L (round + 1) ≤
      grayAdvBlockOffset q L (grayChargedAdvantageRoundCount q) :=
    grayAdvBlockOffset_mono (by omega)
  have hcap := grayAdvBlock_capacity q L
  have hbase : grayTailBaseBranch q L ≤ grayTailBranch q L a e := le_max_right _ _
  omega

/-- For a used round, the grandson block has exactly `mult` elements. -/
lemma grayAdvBlockGrandsons_length_used {q L a e round : Nat}
    (h : round < grayChargedAdvantageRoundCount q) :
    (grayAdvBlockGrandsons (grayTailBranch q L a e) q L round).length =
      grayAdvBlockMult q L round :=
  grayAdvBlockGrandsons_length (grayAdvBlock_fit_of_lt_advCount h)

/-- A used round index is below the branching. -/
lemma round_lt_branch_of_lt_advCount {q L a e round : Nat}
    (h : round < grayChargedAdvantageRoundCount q) :
    round < grayTailBranch q L a e := by
  have h1 : grayChargedAdvantageRoundCount q ≤ grayTailRoundCount q := by
    rw [grayChargedAdvantageRoundCount_eq, grayTailRoundCount]; omega
  have h2 := grayTailRoundCount_le_baseBranch q L
  have hbase : grayTailBaseBranch q L ≤ grayTailBranch q L a e := le_max_right _ _
  omega

end Kolmogorov
