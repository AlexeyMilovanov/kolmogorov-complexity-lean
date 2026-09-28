import KolmogorovMathlib.StoppingComplexity.DyadicCells
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# Clean regions and exact repacking

Blueprint part 02, §2 (LEM-REPACK-01, LEM-REPACK-02, LEM-REPACK-03). A finite region `F` of
depth-`D` cells is given as a list of indices. A cell is *clean* when it is a union of cells of
`F`; the maximal clean cells `cleanBlocks D F` are pairwise disjoint, cover `F`, have total length
`|F| / 2^D` and host every clean cell uniquely (LEM-REPACK-01). `packBlocks` places copies of
aligned cells consecutively from address `0`, sorted by depth, without alignment loss
(LEM-REPACK-02). The cell translation `repackMap D F` (the blueprint's `Φ`) sends a clean cell to
the cell with the same relative dyadic address inside the packed copy of its host block; it
preserves depth, lands in `[0, packedCapacity D F)` and preserves and reflects disjointness
(LEM-REPACK-03). Every definition is executable on natural numbers (relative addresses by
Euclidean division, never a signed subtraction) and primitive recursive.
-/

namespace Kolmogorov

/-! ### Clean cells and maximal blocks (LEM-REPACK-01) -/

/-- `IsClean D F c`: the cell `c` has depth at most `D` and is a union of depth-`D` cells of
`F`, i.e. every one of the `2^(D - depth)` depth-`D` descendants of `c` has its index in `F`.
Blueprint 02 LEM-REPACK-01. -/
def IsClean (D : ℕ) (F : List ℕ) (c : DyadicCell) : Prop :=
  c.1 ≤ D ∧ ∀ i < 2 ^ (D - c.1), c.2 * 2 ^ (D - c.1) + i ∈ F

/-- Cleanness is decidable (a bounded search over the descendants). Blueprint 02 LEM-REPACK-01. -/
instance instDecidableIsClean (D : ℕ) (F : List ℕ) (c : DyadicCell) :
    Decidable (IsClean D F c) := by
  unfold IsClean; infer_instance

/-- The ancestors, at the depths `0, …, D`, of the depth-`D` cells of `F`, without duplicates:
the candidates for the maximal clean blocks. Blueprint 02 LEM-REPACK-01 (executable
construction). -/
def cleanCandidates (D : ℕ) (F : List ℕ) : List DyadicCell :=
  (F.flatMap fun i => (List.range (D + 1)).map fun a => cellAncestor (D, i) a).dedup

/-- The maximal clean blocks `R(F)`: the clean candidates whose parent is absent (depth `0`)
or not clean. Blueprint 02 LEM-REPACK-01 (executable construction). -/
def cleanBlocks (D : ℕ) (F : List ℕ) : List DyadicCell :=
  (cleanCandidates D F).filter fun c =>
    decide (IsClean D F c) &&
      (decide (c.1 = 0) || !decide (IsClean D F (cellAncestor c (c.1 - 1))))

/-- The maximal clean blocks are listed without repetition. Blueprint 02 LEM-REPACK-01
(`R(F)` is finite). -/
theorem cleanBlocks_nodup (D : ℕ) (F : List ℕ) : (cleanBlocks D F).Nodup := by
  exact (List.nodup_dedup _).filter _

/-- Iterated ancestors: for `b ≤ a ≤ depth c`, the depth-`b` ancestor of the depth-`a` ancestor
of `c` is the depth-`b` ancestor of `c`. Blueprint 02 LEM-CELL-01. -/
private theorem cellAncestor_cellAncestor (c : DyadicCell) {a b : ℕ} (hba : b ≤ a)
    (hac : a ≤ c.1) : cellAncestor (cellAncestor c a) b = cellAncestor c b := by
  simp only [cellAncestor, Nat.div_div_eq_div_mul, ← pow_add]
  rw [show c.1 - a + (a - b) = c.1 - b by omega]

/-- A cell inside another cell is at least as deep (compare the lengths).
Blueprint 02 LEM-CELL-01. -/
private theorem depth_le_depth_of_cellSubset {c r : DyadicCell} (h : CellSubset c r) :
    r.1 ≤ c.1 := by
  have hlen : cellLength c ≤ cellLength r := by
    rw [cellLength_eq_cellRight_sub_cellLeft, cellLength_eq_cellRight_sub_cellLeft]
    linarith [h.1, h.2]
  unfold cellLength at hlen
  exact (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).1 hlen

/-- Two cells containing a common cell are not disjoint (cells are nonempty).
Blueprint 02 LEM-CELL-01. -/
private theorem not_cellsDisjoint_of_cellSubset_of_cellSubset {q r r' : DyadicCell}
    (h : CellSubset q r) (h' : CellSubset q r') : ¬ CellsDisjoint r r' := by
  intro hd
  have h1 : CellsDisjoint q r' := cellsDisjoint_of_cellSubset_left h hd
  have h2 : CellsDisjoint q q := cellsDisjoint_of_cellSubset_left h' (Or.symm h1)
  have hpos : 0 < cellLength q := by
    unfold cellLength
    positivity
  rw [cellLength_eq_cellRight_sub_cellLeft] at hpos
  rcases h2 with h2 | h2 <;> linarith

/-- A cell of depth at most `D` inside a clean cell is clean: its depth-`D` descendants are
depth-`D` descendants of the clean cell. Blueprint 02 LEM-REPACK-01. -/
private theorem isClean_of_cellSubset {D : ℕ} {F : List ℕ} {c r : DyadicCell}
    (hr : IsClean D F r) (hcr : CellSubset c r) (hc : c.1 ≤ D) : IsClean D F c := by
  refine ⟨hc, fun i hi => ?_⟩
  have hd := depth_le_depth_of_cellSubset hcr
  have hr2 : r.2 = c.2 / 2 ^ (c.1 - r.1) := congrArg Prod.snd (cellAncestor_unique hcr)
  have hP : 0 < 2 ^ (c.1 - r.1) := by positivity
  have hpow : 2 ^ (D - r.1) = 2 ^ (c.1 - r.1) * 2 ^ (D - c.1) := by
    rw [← pow_add]
    congr 1
    omega
  have hmod : c.2 % 2 ^ (c.1 - r.1) + 1 ≤ 2 ^ (c.1 - r.1) := Nat.mod_lt _ hP
  have hlt : c.2 % 2 ^ (c.1 - r.1) * 2 ^ (D - c.1) + i < 2 ^ (D - r.1) := by
    rw [hpow]
    calc c.2 % 2 ^ (c.1 - r.1) * 2 ^ (D - c.1) + i
        < (c.2 % 2 ^ (c.1 - r.1) + 1) * 2 ^ (D - c.1) := by rw [add_one_mul]; omega
      _ ≤ 2 ^ (c.1 - r.1) * 2 ^ (D - c.1) := Nat.mul_le_mul_right _ hmod
  have key := hr.2 _ hlt
  rw [hr2, hpow] at key
  convert key using 1
  conv_lhs => rw [← Nat.div_add_mod c.2 (2 ^ (c.1 - r.1))]
  ring

/-- Membership in the maximal clean blocks: a clean candidate of depth `0` or whose parent is
not clean. Blueprint 02 LEM-REPACK-01. -/
private theorem mem_cleanBlocks_iff {D : ℕ} {F : List ℕ} {c : DyadicCell} :
    c ∈ cleanBlocks D F ↔ c ∈ cleanCandidates D F ∧ IsClean D F c ∧
      (c.1 = 0 ∨ ¬ IsClean D F (cellAncestor c (c.1 - 1))) := by
  simp only [cleanBlocks, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]

/-- A maximal clean block is not strictly inside a clean cell: a clean cell containing it is
the block itself (otherwise the parent of the block would be clean).
Blueprint 02 LEM-REPACK-01. -/
private theorem eq_of_mem_cleanBlocks_of_cellSubset {D : ℕ} {F : List ℕ} {r r' : DyadicCell}
    (hr : r ∈ cleanBlocks D F) (hr' : IsClean D F r') (hsub : CellSubset r r') : r' = r := by
  obtain ⟨-, hrc, hmax⟩ := mem_cleanBlocks_iff.1 hr
  have hanc := cellAncestor_unique hsub
  rcases (depth_le_depth_of_cellSubset hsub).lt_or_eq with hlt | heq
  · exfalso
    rcases hmax with h0 | hmax
    · omega
    · apply hmax
      refine isClean_of_cellSubset hr' ?_ ((Nat.sub_le _ _).trans hrc.1)
      rw [hanc, ← cellAncestor_cellAncestor r (Nat.le_sub_one_of_lt hlt) (Nat.sub_le _ _)]
      exact cellSubset_cellAncestor _ (Nat.le_sub_one_of_lt hlt)
  · rw [hanc, heq]
    simp [cellAncestor]

/-- The maximal clean blocks are pairwise disjoint (dyadic laminarity: two distinct maximal
clean cells cannot be nested). Blueprint 02 LEM-REPACK-01. -/
theorem cleanBlocks_pairwise_disjoint (D : ℕ) (F : List ℕ) :
    (cleanBlocks D F).Pairwise CellsDisjoint := by
  refine (cleanBlocks_nodup D F).pairwise_of_forall_ne fun r hr r' hr' hne => ?_
  rcases cellsDisjoint_or_cellSubset r r' with h | h | h
  · exact h
  · exact absurd (eq_of_mem_cleanBlocks_of_cellSubset hr (mem_cleanBlocks_iff.1 hr').2.1 h).symm
      hne
  · exact absurd (eq_of_mem_cleanBlocks_of_cellSubset hr' (mem_cleanBlocks_iff.1 hr).2.1 h) hne

/-- Every maximal clean block is clean. Blueprint 02 LEM-REPACK-01. -/
theorem cleanBlocks_isClean {D : ℕ} {F : List ℕ} {r : DyadicCell} (hr : r ∈ cleanBlocks D F) :
    IsClean D F r := by
  rw [cleanBlocks, List.mem_filter] at hr
  exact of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hr.2).1

/-- The maximal clean blocks cover `F`: every depth-`D` cell of `F` lies in one of them.
Blueprint 02 LEM-REPACK-01. -/
theorem cleanBlocks_cover {D : ℕ} {F : List ℕ} {i : ℕ} (hi : i ∈ F) :
    ∃ r ∈ cleanBlocks D F, CellSubset (D, i) r := by
  have h_clean : IsClean D F (D, i) := by
    refine ⟨le_rfl, fun j hj => ?_⟩
    have : D - D = 0 := Nat.sub_self D
    rw [this] at hj
    have : j = 0 := by omega
    subst this
    simpa using hi
  let S := { l : ℕ | l ≤ D ∧ IsClean D F (cellAncestor (D, i) l) }
  have hS_nonempty : S.Nonempty := by
    use D
    dsimp [S]
    refine ⟨le_rfl, ?_⟩
    have : cellAncestor (D, i) D = (D, i) := by simp [cellAncestor]
    rw [this]
    exact h_clean
  let l_min := Nat.find hS_nonempty
  have hl_min : l_min ∈ S := Nat.find_spec hS_nonempty
  use cellAncestor (D, i) l_min
  refine ⟨?_, ?_⟩
  · rw [cleanBlocks, List.mem_filter]
    refine ⟨?_, ?_⟩
    · unfold cleanCandidates
      rw [List.mem_dedup, List.mem_flatMap]
      refine ⟨i, hi, ?_⟩
      rw [List.mem_map]
      refine ⟨l_min, ?_, rfl⟩
      simp only [List.mem_range, Order.lt_add_one_iff]
      exact hl_min.1
    · rw [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hl_min.2, ?_⟩
      by_cases h0 : l_min = 0
      · rw [h0]
        exact rfl
      · rw [Bool.or_eq_true]
        right
        rw [Bool.not_eq_true']
        have h_lt : l_min - 1 < l_min := Nat.pred_lt h0
        have h_in_S : l_min - 1 ∉ S := Nat.find_min hS_nonempty h_lt
        have h_eq2 : (cellAncestor (D, i) l_min).1 = l_min := rfl
        have H_not_clean : ¬ IsClean D F (cellAncestor
            (cellAncestor (D, i) l_min) ((cellAncestor (D, i) l_min).1 - 1)) := by
          have h_eq : cellAncestor (cellAncestor (D, i) l_min) ((cellAncestor (D, i) l_min).1 - 1) =
              cellAncestor (D, i) (l_min - 1) := by
            have h_pow : 2 ^ (D - l_min) * 2 ^ (l_min - (l_min - 1)) = 2 ^ (D - (l_min - 1)) := by
              rw [← Nat.pow_add]
              congr 1
              have hl : l_min ≤ D := hl_min.1
              omega
            dsimp only [cellAncestor]
            have h_fst : (cellAncestor (D, i) l_min).1 = l_min := rfl
            have h_snd : (cellAncestor (D, i) l_min).2 = i / 2 ^ (D - l_min) := rfl
            change (l_min - 1, i / 2 ^ (D - l_min) / 2 ^ (l_min - (l_min - 1))) =
              (l_min - 1, i / 2 ^ (D - (l_min - 1)))
            congr 1
            rw [Nat.div_div_eq_div_mul, h_pow]
          rw [h_eq]
          intro H_clean
          apply h_in_S
          dsimp [S]
          have hl : l_min ≤ D := hl_min.1
          exact ⟨by omega, H_clean⟩
        exact decide_eq_false H_not_clean
  · apply cellSubset_cellAncestor
    exact hl_min.1

/-- The depth-`D` cells of the maximal clean blocks, block by block: a block `r` contributes
its `2^(D - r.1)` depth-`D` descendants. Blueprint 02 LEM-REPACK-01. -/
private def blockCells (D : ℕ) (F : List ℕ) : List ℕ :=
  (cleanBlocks D F).flatMap fun r => List.range' (r.2 * 2 ^ (D - r.1)) (2 ^ (D - r.1))

/-- The depth-`D` cells inside a cell `r` of depth at most `D` are the indices
`r.2 · 2^(D - r.1) + i` with `i < 2^(D - r.1)`. Blueprint 02 DEF-02. -/
private theorem cellSubset_iff_mem_range' {D x : ℕ} {r : DyadicCell} (hr : r.1 ≤ D) :
    CellSubset (D, x) r ↔ x ∈ List.range' (r.2 * 2 ^ (D - r.1)) (2 ^ (D - r.1)) := by
  rw [cellSubset_iff_refined, List.mem_range'_1]
  simp only [max_eq_left hr, Nat.sub_self, pow_zero, mul_one, add_one_mul]
  omega

/-- The cells of the blocks are listed without repetition: the descendants of one block are
distinct, and distinct blocks are disjoint. Blueprint 02 LEM-REPACK-01. -/
private theorem blockCells_nodup (D : ℕ) (F : List ℕ) : (blockCells D F).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun r _ => List.nodup_range', ?_⟩
  refine (cleanBlocks_pairwise_disjoint D F).imp_of_mem fun {r r'} hr hr' hd => ?_
  intro x hx hx'
  exact not_cellsDisjoint_of_cellSubset_of_cellSubset
    ((cellSubset_iff_mem_range' (cleanBlocks_isClean hr).1).2 hx)
    ((cellSubset_iff_mem_range' (cleanBlocks_isClean hr').1).2 hx') hd

/-- The cells of the blocks are exactly the cells of `F` (the blocks are clean and cover `F`).
Blueprint 02 LEM-REPACK-01. -/
private theorem mem_blockCells_iff {D : ℕ} {F : List ℕ} {x : ℕ} :
    x ∈ blockCells D F ↔ x ∈ F := by
  unfold blockCells
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hx⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hx
    simpa using (cleanBlocks_isClean hr).2 i hi
  · intro hx
    obtain ⟨r, hr, hsub⟩ := cleanBlocks_cover hx
    exact ⟨r, hr, (cellSubset_iff_mem_range' (cleanBlocks_isClean hr).1).1 hsub⟩

/-- The total length of the maximal clean blocks is the number of their depth-`D` cells times
`2^{-D}`. Blueprint 02 LEM-REPACK-01. -/
private theorem sum_cellLength_cleanBlocks (D : ℕ) (F : List ℕ) :
    ((cleanBlocks D F).map cellLength).sum = ((blockCells D F).length : ℚ) / 2 ^ D := by
  rw [eq_div_iff (by positivity), ← List.sum_map_mul_right, blockCells, List.length_flatMap,
    Nat.cast_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
  have hrD := (cleanBlocks_isClean hr).1
  have h2 : (2 : ℚ) ^ D = 2 ^ (D - r.1) * 2 ^ r.1 := by
    rw [← pow_add, Nat.sub_add_cancel hrD]
  simp only [Function.comp_apply, List.length_range', cellLength, Nat.cast_pow, Nat.cast_ofNat,
    h2, one_div_pow]
  field_simp

/-- The total length of the maximal clean blocks of a region without repeated indices is
`|F| · 2^{-D}`. Blueprint 02 LEM-REPACK-01. -/
theorem cleanBlocks_length_sum {D : ℕ} {F : List ℕ} (hF : F.Nodup) :
    ((cleanBlocks D F).map cellLength).sum = (F.length : ℚ) / 2 ^ D := by
  rw [sum_cellLength_cleanBlocks, ((List.perm_ext_iff_of_nodup (blockCells_nodup D F) hF).2
    fun _ => mem_blockCells_iff).length_eq]

/-- Existence of a host: the shallowest clean ancestor of a clean cell is a maximal clean block
containing it. Blueprint 02 LEM-REPACK-01. -/
private theorem exists_mem_cleanBlocks_cellSubset {D : ℕ} {F : List ℕ} {q : DyadicCell}
    (hq : IsClean D F q) : ∃ r ∈ cleanBlocks D F, CellSubset q r := by
  have hex : ∃ a, a ≤ q.1 ∧ IsClean D F (cellAncestor q a) :=
    ⟨q.1, le_rfl, by simpa [cellAncestor] using hq⟩
  have hspec := Nat.find_spec hex
  refine ⟨cellAncestor q (Nat.find hex), ?_, cellSubset_cellAncestor q hspec.1⟩
  have hfst : (cellAncestor q (Nat.find hex)).1 = Nat.find hex := rfl
  rw [mem_cleanBlocks_iff, hfst]
  refine ⟨?_, hspec.2, ?_⟩
  · have hi : q.2 * 2 ^ (D - q.1) ∈ F := by simpa using hq.2 0 (by positivity)
    have hq' : cellAncestor (D, q.2 * 2 ^ (D - q.1)) q.1 = q := by
      simp [cellAncestor, Nat.mul_div_cancel _ (by positivity : 0 < 2 ^ (D - q.1))]
    unfold cleanCandidates
    rw [List.mem_dedup, List.mem_flatMap]
    refine ⟨_, hi, List.mem_map.2 ⟨Nat.find hex, List.mem_range.2 ?_, ?_⟩⟩
    · have := hq.1
      omega
    · rw [← cellAncestor_cellAncestor (D, q.2 * 2 ^ (D - q.1)) hspec.1 hq.1, hq']
  · by_cases h0 : Nat.find hex = 0
    · exact Or.inl h0
    · right
      have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [cellAncestor_cellAncestor q (Nat.sub_le _ _) hspec.1]
      exact fun hc => hmin ⟨by omega, hc⟩

/-- Every clean cell (of depth at most `D`, a union of cells of `F`) lies in exactly one
maximal clean block, its *host*. Blueprint 02 LEM-REPACK-01. -/
theorem exists_unique_host {D : ℕ} {F : List ℕ} {q : DyadicCell} (hq : IsClean D F q) :
    ∃! r, r ∈ cleanBlocks D F ∧ CellSubset q r := by
  obtain ⟨r₀, hr₀, hqr₀⟩ := exists_mem_cleanBlocks_cellSubset hq
  refine ⟨r₀, ⟨hr₀, hqr₀⟩, fun r ⟨hr, hqr⟩ => ?_⟩
  rcases cellsDisjoint_or_cellSubset r r₀ with h | h | h
  · exact absurd h (not_cellsDisjoint_of_cellSubset_of_cellSubset hqr hqr₀)
  · exact (eq_of_mem_cleanBlocks_of_cellSubset hr (cleanBlocks_isClean hr₀) h).symm
  · exact eq_of_mem_cleanBlocks_of_cellSubset hr₀ (cleanBlocks_isClean hr) h

/-- Powers of two are primitive recursive. Blueprint 02 LEM-EFF-02. -/
private theorem primrec_two_pow : Primrec fun n : ℕ => 2 ^ n :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id

/-- The depth-`a` ancestor of a cell is primitive recursive in the cell and `a`.
Blueprint 02 LEM-CELL-01. -/
private theorem primrec_cellAncestor : Primrec₂ cellAncestor :=
  (Primrec.pair Primrec.snd (Primrec.nat_div.comp (Primrec.snd.comp Primrec.fst)
    (primrec_two_pow.comp (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd)))).of_eq fun _ => rfl

/-- Membership in a list is a primitive recursive relation. Blueprint 02 LEM-EFF-02. -/
private theorem primrecRel_mem {α : Type*} [Primcodable α] :
    PrimrecRel fun (L : List α) (x : α) => x ∈ L :=
  Primrec.eq.exists_mem_list.of_eq fun L x => by simp

/-- Removing duplicates is primitive recursive: `dedup` is the right fold that keeps an element
unless it occurs further right. Blueprint 02 LEM-REPACK-01 (executable construction). -/
private theorem primrec_dedup {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec (List.dedup : List α → List α) := by
  have hstep : Primrec₂ fun (_ : List α) (p : α × List α) =>
      if p.1 ∈ p.2 then p.2 else p.1 :: p.2 :=
    (Primrec.ite (primrecRel_mem.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂
  refine (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [id, List.foldr_cons] at ih ⊢
    rw [ih]
    by_cases h : a ∈ l
    · rw [if_pos (List.mem_dedup.2 h), List.dedup_cons_of_mem h]
    · rw [if_neg (mt List.mem_dedup.1 h), List.dedup_cons_of_notMem h]

/-- Cleanness is a primitive recursive relation between the region `(D, F)` and the cell (a
bounded universal quantifier over the depth-`D` descendants). Blueprint 02 LEM-REPACK-01. -/
private theorem primrecRel_isClean :
    PrimrecRel fun (x : ℕ × List ℕ) (c : DyadicCell) => IsClean x.1 x.2 c := by
  have hdesc : PrimrecRel fun (i : ℕ) (y : (ℕ × List ℕ) × DyadicCell) =>
      y.2.2 * 2 ^ (y.1.1 - y.2.1) + i ∈ y.1.2 :=
    primrecRel_mem.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (primrec_two_pow.comp (Primrec.nat_sub.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))) Primrec.fst)
  have hall : PrimrecPred fun y : (ℕ × List ℕ) × DyadicCell =>
      ∀ i < 2 ^ (y.1.1 - y.2.1), y.2.2 * 2 ^ (y.1.1 - y.2.1) + i ∈ y.1.2 :=
    (hdesc.forall_mem_list.comp (Primrec.list_range.comp (primrec_two_pow.comp
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))))
      Primrec.id).of_eq fun _ => by simp only [List.mem_range, id]
  exact (PrimrecPred.and
    (Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
    hall).of_eq fun _ => Iff.rfl

/-- The maximal clean blocks are computed primitive recursively from `(D, F)`.
Blueprint 02 LEM-REPACK-01 (`R(F)` is finite and computable). -/
theorem primrec_cleanBlocks : Primrec₂ cleanBlocks := by
  have hclean := primrecRel_isClean.decide
  have hcand : Primrec fun x : ℕ × List ℕ => cleanCandidates x.1 x.2 :=
    primrec_dedup.comp (Primrec.list_flatMap Primrec.snd
      (Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec.fst.comp Primrec.fst)))
        (primrec_cellAncestor.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst)) (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂).to₂)
  have hp : Primrec₂ fun (x : ℕ × List ℕ) (c : DyadicCell) => decide (IsClean x.1 x.2 c) &&
      (decide (c.1 = 0) || !decide (IsClean x.1 x.2 (cellAncestor c (c.1 - 1)))) :=
    Primrec.and.comp hclean
      (Primrec.or.comp (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
        (Primrec.not.comp (hclean.comp Primrec.fst (primrec_cellAncestor.comp Primrec.snd
          (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))))))
  exact (Primrec.list_filter hcand hp).of_eq fun _ => rfl

/-! ### Packing blocks without alignment loss (LEM-REPACK-02) -/

/-- The deterministic packing order: increasing depth, then increasing index.
Blueprint 02 LEM-REPACK-02. -/
def blockLE (c c' : DyadicCell) : Bool := decide (c.1 < c'.1 ∨ (c.1 = c'.1 ∧ c.2 ≤ c'.2))

/-- The largest depth among a list of cells (`0` for the empty list): the common grid of the
packing arithmetic. Blueprint 02 LEM-REPACK-02. -/
def maxDepth (rs : List DyadicCell) : ℕ := (rs.map Prod.fst).foldr max 0

/-- Consecutive placement of the (already sorted) cells: `off` is the next free address in
units of `2^{-Dm}`, and the copy of a depth-`l` cell placed at `off` is the cell
`(l, off / 2^(Dm - l))` (exact division, by the alignment argument of LEM-REPACK-02).
Blueprint 02 LEM-REPACK-02. -/
def packBlocksAux (Dm : ℕ) : List DyadicCell → ℕ → List (DyadicCell × DyadicCell)
  | [], _ => []
  | r :: rs, off =>
    (r, (r.1, off / 2 ^ (Dm - r.1))) :: packBlocksAux Dm rs (off + 2 ^ (Dm - r.1))

/-- Pack a list of aligned cells: sort by `(depth, index)` and place copies of their lengths
consecutively from address `0`; each entry pairs a cell with its packed copy.
Blueprint 02 LEM-REPACK-02. -/
def packBlocks (rs : List DyadicCell) : List (DyadicCell × DyadicCell) :=
  packBlocksAux (maxDepth rs) (rs.mergeSort blockLE) 0

/-- The first components of the packing are a permutation of the packed list.
Blueprint 02 LEM-REPACK-02. -/
theorem packBlocks_map_fst_perm (rs : List DyadicCell) :
    ((packBlocks rs).map Prod.fst).Perm rs := by
  have key : ∀ (l : List DyadicCell) (off : ℕ),
      (packBlocksAux (maxDepth rs) l off).map Prod.fst = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons r l ih => intro off; simp [packBlocksAux, ih]
  rw [packBlocks, key]
  exact List.mergeSort_perm rs blockLE

/-- Each packed copy has the depth of its original (copies are aligned).
Blueprint 02 LEM-REPACK-02. -/
theorem packBlocks_depth {rs : List DyadicCell} {e : DyadicCell × DyadicCell}
    (he : e ∈ packBlocks rs) : e.2.1 = e.1.1 := by
  unfold packBlocks at he
  generalize rs.mergeSort blockLE = l at he
  generalize 0 = off at he
  induction l generalizing off with
  | nil => simp [packBlocksAux] at he
  | cons r l ih =>
    rw [packBlocksAux, List.mem_cons] at he
    rcases he with rfl | he
    · rfl
    · exact ih _ he

/-- Consecutive placement from the address `off` (in units of `2^{-Dm}`) of a depth-sorted list
of cells of depth at most `Dm`, with `off` aligned to every depth of the list: the `k`-th copy
starts at `off / 2^Dm` plus the total length of the copies placed before it (each Euclidean
division is exact). Blueprint 02 LEM-REPACK-02. -/
private theorem packBlocksAux_cellLeft {Dm : ℕ} {l : List DyadicCell} {off : ℕ}
    (hl : ∀ c ∈ l, c.1 ≤ Dm ∧ 2 ^ (Dm - c.1) ∣ off) (hs : l.Pairwise fun a b => a.1 ≤ b.1)
    {k : ℕ} (hk : k < (packBlocksAux Dm l off).length) :
    cellLeft ((packBlocksAux Dm l off)[k]).2 =
      (off : ℚ) / 2 ^ Dm + (((packBlocksAux Dm l off).take k).map fun e => cellLength e.2).sum := by
  induction l generalizing off k with
  | nil => simp [packBlocksAux] at hk
  | cons r l ih =>
    obtain ⟨hrD, hrdvd⟩ := hl r (List.mem_cons_self ..)
    have h2 : (2 : ℚ) ^ Dm = 2 ^ (Dm - r.1) * 2 ^ r.1 := by
      rw [← pow_add, Nat.sub_add_cancel hrD]
    rcases k with _ | k
    · simp only [packBlocksAux, List.getElem_cons_zero, List.take_zero, List.map_nil,
        List.sum_nil, add_zero, cellLeft]
      rw [Nat.cast_div hrdvd (by positivity), h2, div_div]
      norm_cast
    · have hl' : ∀ c ∈ l, c.1 ≤ Dm ∧ 2 ^ (Dm - c.1) ∣ off + 2 ^ (Dm - r.1) := by
        intro c hc
        obtain ⟨hcD, hcdvd⟩ := hl c (List.mem_cons_of_mem _ hc)
        have hrc : r.1 ≤ c.1 := List.rel_of_pairwise_cons hs hc
        exact ⟨hcD, dvd_add hcdvd (Nat.pow_dvd_pow 2 (by omega))⟩
      simp only [packBlocksAux, List.getElem_cons_succ, List.take_succ_cons, List.map_cons,
        List.sum_cons]
      rw [ih hl' hs.of_cons]
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, cellLength, h2, one_div_pow]
      field_simp
      ring

/-- The left endpoint of the `k`-th packed copy is the total length of the copies placed
before it: consecutive placement without gaps (the alignment of LEM-REPACK-02 makes the
Euclidean division in `packBlocksAux` exact). Blueprint 02 LEM-REPACK-02. -/
theorem packBlocks_cellLeft_eq (rs : List DyadicCell) {k : ℕ} (hk : k < (packBlocks rs).length) :
    cellLeft ((packBlocks rs)[k]).2 =
      (((packBlocks rs).take k).map fun e => cellLength e.2).sum := by
  have hdepth : ∀ (l : List DyadicCell), ∀ c ∈ l, c.1 ≤ maxDepth l := by
    intro l c hc
    unfold maxDepth
    induction l with
    | nil => simp at hc
    | cons r l ih =>
      rw [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.1 hc with rfl | hc
      · exact le_max_left _ _
      · exact le_max_of_le_right (ih hc)
  have hsorted : (rs.mergeSort blockLE).Pairwise fun a b => a.1 ≤ b.1 := by
    refine (List.pairwise_mergeSort (le := blockLE) (fun a b c hab hbc => ?_) (fun a b => ?_)
      rs).imp fun {a b} h => ?_
    · simp only [blockLE, decide_eq_true_eq] at hab hbc ⊢
      omega
    · simp only [blockLE, Bool.or_eq_true, decide_eq_true_eq]
      omega
    · simp only [blockLE, decide_eq_true_eq] at h
      omega
  have key : cellLeft ((packBlocks rs)[k]).2 = ((0 : ℕ) : ℚ) / 2 ^ maxDepth rs +
      (((packBlocks rs).take k).map fun e => cellLength e.2).sum :=
    packBlocksAux_cellLeft (off := 0)
      (fun c hc => ⟨hdepth rs c ((List.mergeSort_perm rs blockLE).subset hc), dvd_zero _⟩)
      hsorted hk
  rw [key, Nat.cast_zero, zero_div, zero_add]

/-- The right endpoint of the `k`-th packed copy is the total length of the first `k + 1`
copies. Blueprint 02 LEM-REPACK-02. -/
private theorem packBlocks_cellRight_eq (rs : List DyadicCell) {k : ℕ}
    (hk : k < (packBlocks rs).length) :
    cellRight ((packBlocks rs)[k]).2 =
      (((packBlocks rs).map fun e => cellLength e.2).take (k + 1)).sum := by
  rw [List.sum_take_succ _ _ (by simpa using hk), ← List.map_take, ← packBlocks_cellLeft_eq rs hk,
    List.getElem_map, cellLength_eq_cellRight_sub_cellLeft]
  ring

/-- The packed copies are pairwise disjoint. Blueprint 02 LEM-REPACK-02. -/
theorem packBlocks_pairwise_disjoint (rs : List DyadicCell) :
    ((packBlocks rs).map Prod.snd).Pairwise CellsDisjoint := by
  rw [List.pairwise_map, List.pairwise_iff_getElem]
  intro i k hi hk hik
  left
  rw [packBlocks_cellRight_eq rs hi, packBlocks_cellLeft_eq rs hk, List.map_take]
  refine (List.take_sublist_take_left hik).sum_le_sum fun a ha => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take ha)
  unfold cellLength
  positivity

/-- The packed copies tile `[0, U')`: together with `packBlocks_pairwise_disjoint` and
`packBlocks_inCapacity`, their total length is exactly `U' = Σ_r 2^{-l_r}`.
Blueprint 02 LEM-REPACK-02. -/
theorem packBlocks_tile (rs : List DyadicCell) :
    ((packBlocks rs).map fun e => cellLength e.2).sum = (rs.map cellLength).sum := by
  have h : ((packBlocks rs).map fun e => cellLength e.2) =
      ((packBlocks rs).map Prod.fst).map cellLength := by
    rw [List.map_map]
    refine List.map_congr_left fun e he => ?_
    simp only [Function.comp_apply, cellLength, packBlocks_depth he]
  rw [h]
  exact ((packBlocks_map_fst_perm rs).map cellLength).sum_eq

/-- Every packed copy lies in `[0, U')`, where `U'` is the total length of the packed cells.
Blueprint 02 LEM-REPACK-02. -/
theorem packBlocks_inCapacity {rs : List DyadicCell} {e : DyadicCell × DyadicCell}
    (he : e ∈ packBlocks rs) : CellInCapacity ((rs.map cellLength).sum) e.2 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
  unfold CellInCapacity
  rw [packBlocks_cellRight_eq rs hk, ← packBlocks_tile rs]
  refine (List.take_sublist _ _).sum_le_sum fun a ha => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
  unfold cellLength
  positivity

/-- Ordered insertion for a primitive recursive decidable relation is primitive recursive
(a list recursion that keeps the tail). Blueprint 02 LEM-REPACK-02. -/
private theorem primrec_orderedInsert {α : Type*} [Primcodable α] {r : α → α → Prop}
    [DecidableRel r] (hr : PrimrecRel r) :
    Primrec₂ fun (a : α) (l : List α) => l.orderedInsert r a := by
  have h : Primrec fun p : α × List α => List.recOn (motive := fun _ => List α) p.2 [p.1]
      fun b l IH => if r p.1 b then p.1 :: b :: l else b :: IH :=
    Primrec.list_rec Primrec.snd (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
      (Primrec.ite (hr.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) (Primrec.list_cons.comp
          (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
  refine h.of_eq fun p => ?_
  obtain ⟨a, l⟩ := p
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.orderedInsert] at ih ⊢
    rw [← ih]

/-- Insertion sort for a primitive recursive decidable relation is primitive recursive (a right
fold of ordered insertions). Blueprint 02 LEM-REPACK-02. -/
private theorem primrec_insertionSort {α : Type*} [Primcodable α] {r : α → α → Prop}
    [DecidableRel r] (hr : PrimrecRel r) : Primrec (List.insertionSort r) := by
  refine (Primrec.list_foldr Primrec.id (Primrec.const [])
    ((primrec_orderedInsert hr).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [id, List.foldr_cons, List.insertionSort] at ih ⊢

/-- Consecutive placement as a left fold over the sorted cells, with state the entries placed so
far and the next free address. Blueprint 02 LEM-REPACK-02. -/
private theorem packBlocksAux_eq_foldl (Dm : ℕ) (l : List DyadicCell)
    (acc : List (DyadicCell × DyadicCell)) (off : ℕ) :
    (l.foldl (fun s r => (s.1 ++ [(r, (r.1, s.2 / 2 ^ (Dm - r.1)))], s.2 + 2 ^ (Dm - r.1)))
      (acc, off)).1 = acc ++ packBlocksAux Dm l off := by
  induction l generalizing acc off with
  | nil => simp [packBlocksAux]
  | cons r l ih => simp [packBlocksAux, ih]

/-- The packing is primitive recursive. Blueprint 02 LEM-REPACK-02. -/
theorem primrec_packBlocks : Primrec packBlocks := by
  let r : DyadicCell → DyadicCell → Prop := fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)
  letI : DecidableRel r := fun a b =>
    inferInstanceAs (Decidable (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)))
  haveI : Std.Total r := ⟨fun a b => by simp only [r]; omega⟩
  haveI : IsTrans DyadicCell r := ⟨fun a b c hab hbc => by simp only [r] at hab hbc ⊢; omega⟩
  haveI : Std.Antisymm r := ⟨fun a b hab hba => by
    simp only [r] at hab hba
    exact Prod.ext (by omega) (by omega)⟩
  have hr : PrimrecRel r :=
    (PrimrecPred.or (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (PrimrecPred.and (Primrec.eq.comp
        (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.nat_le.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))).of_eq
      fun _ => Iff.rfl
  have hsort : ∀ rs : List DyadicCell, rs.mergeSort blockLE = rs.insertionSort r :=
    fun rs => List.mergeSort_eq_insertionSort (r := r) rs
  have hmax : Primrec maxDepth :=
    (Primrec.list_foldr (Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂)
      (Primrec.const 0) (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  have hpw : Primrec fun q : List DyadicCell × ((List (DyadicCell × DyadicCell) × ℕ) ×
      DyadicCell) => 2 ^ (maxDepth q.1 - q.2.2.1) :=
    primrec_two_pow.comp (Primrec.nat_sub.comp (hmax.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hstep : Primrec₂ fun (rs : List DyadicCell)
      (p : (List (DyadicCell × DyadicCell) × ℕ) × DyadicCell) =>
      (p.1.1 ++ [(p.2, (p.2.1, p.1.2 / 2 ^ (maxDepth rs - p.2.1)))],
        p.1.2 + 2 ^ (maxDepth rs - p.2.1)) :=
    (Primrec.pair (Primrec.list_concat.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.nat_div.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) hpw))))
      (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) hpw)).to₂
  refine (Primrec.fst.comp (Primrec.list_foldl (primrec_insertionSort hr)
    (Primrec.const (([], 0) : List (DyadicCell × DyadicCell) × ℕ)) hstep)).of_eq fun rs => ?_
  rw [packBlocks, hsort, ← List.nil_append (packBlocksAux _ _ _), ← packBlocksAux_eq_foldl]

/-- The packed capacity `U' = |F| · 2^{-D}` of a region `F` of depth-`D` cells (the empty
region gives `0`; no integrality of `U'` is needed). Blueprint 02 LEM-REPACK-02. -/
def packedCapacity (D : ℕ) (F : List ℕ) : ℚ := (F.length : ℚ) / 2 ^ D

/-! ### The cell translation `Φ` (LEM-REPACK-03) -/

/-- The cell translation `Φ` of a region `F` of depth-`D` cells: if `q = (n, b)` lies in the
maximal clean block `r = (l, a)` whose packed copy is `(l, a')`, write
`b = a · 2^(n - l) + rel` with `rel = b % 2^(n - l)` and return `(n, a' · 2^(n - l) + rel)`;
a cell in no block (off the domain) is returned unchanged. Blueprint 02 LEM-REPACK-03. -/
def repackMap (D : ℕ) (F : List ℕ) (q : DyadicCell) : DyadicCell :=
  match (packBlocks (cleanBlocks D F)).find? (fun e => decide (CellSubset q e.1)) with
  | none => q
  | some e => (q.1, e.2.2 * 2 ^ (q.1 - e.1.1) + q.2 % 2 ^ (q.1 - e.1.1))

/-- `Φ` preserves the depth of every cell (on and off its domain).
Blueprint 02 LEM-REPACK-03. -/
theorem repackMap_depth (D : ℕ) (F : List ℕ) (q : DyadicCell) : (repackMap D F q).1 = q.1 := by
  unfold repackMap
  split <;> rfl

/-- `Φ` on a clean cell `q` is computed in a packing entry `e` whose original block contains
`q`: `Φ q = (q.1, e.2.2 · 2^(q.1 - e.1.1) + q.2 % 2^(q.1 - e.1.1))` (the search finds an entry
because the host block of `q` is packed). Blueprint 02 LEM-REPACK-03. -/
private theorem exists_entry_repackMap {D : ℕ} {F : List ℕ} {q : DyadicCell}
    (hq : IsClean D F q) :
    ∃ e ∈ packBlocks (cleanBlocks D F), CellSubset q e.1 ∧
      repackMap D F q = (q.1, e.2.2 * 2 ^ (q.1 - e.1.1) + q.2 % 2 ^ (q.1 - e.1.1)) := by
  obtain ⟨r, hr, hqr⟩ := exists_mem_cleanBlocks_cellSubset hq
  obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 ((packBlocks_map_fst_perm _).symm.subset hr)
  unfold repackMap
  rcases hfind : (packBlocks (cleanBlocks D F)).find? (fun e => decide (CellSubset q e.1)) with
    _ | e
  · exact absurd (List.find?_eq_none.1 hfind e₀ he₀) (by simpa using hqr)
  · have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    exact ⟨e, List.mem_of_find?_eq_some hfind, hp, by rw [hfind]⟩

/-- The translate `(n, a · 2^(n - l) + b % 2^(n - l))` of a cell `(n, b)` with `l ≤ n` lies
inside the cell `(l, a)`. Blueprint 02 LEM-REPACK-03. -/
private theorem cellSubset_translate {q : DyadicCell} {l a : ℕ} (hl : l ≤ q.1) :
    CellSubset (q.1, a * 2 ^ (q.1 - l) + q.2 % 2 ^ (q.1 - l)) (l, a) := by
  have h := cellSubset_cellAncestor (q.1, a * 2 ^ (q.1 - l) + q.2 % 2 ^ (q.1 - l)) hl
  have hP : 0 < 2 ^ (q.1 - l) := by positivity
  have ha : (a * 2 ^ (q.1 - l) + q.2 % 2 ^ (q.1 - l)) / 2 ^ (q.1 - l) = a := by
    rw [mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt (Nat.mod_lt _ hP), add_zero]
  simpa [cellAncestor, ha] using h

/-- Inside a block `(l, b)` with packed copy `(l, a)`, the translate of a cell `q` has its left
endpoint moved by `(a - b) / 2^l`. Blueprint 02 LEM-REPACK-03. -/
private theorem cellLeft_translate {q : DyadicCell} {l b a : ℕ} (hq : CellSubset q (l, b)) :
    cellLeft (q.1, a * 2 ^ (q.1 - l) + q.2 % 2 ^ (q.1 - l)) =
      cellLeft q + ((a : ℚ) - b) / 2 ^ l := by
  have hl : l ≤ q.1 := depth_le_depth_of_cellSubset hq
  have hb : b = q.2 / 2 ^ (q.1 - l) := congrArg Prod.snd (cellAncestor_unique hq)
  have hq2 : (q.2 : ℚ) = b * 2 ^ (q.1 - l) + ((q.2 % 2 ^ (q.1 - l) : ℕ) : ℚ) := by
    rw [hb]
    exact_mod_cast (Nat.div_add_mod' q.2 (2 ^ (q.1 - l))).symm
  have h2 : (2 : ℚ) ^ q.1 = 2 ^ (q.1 - l) * 2 ^ l := by
    rw [← pow_add, Nat.sub_add_cancel hl]
  unfold cellLeft
  rw [hq2, h2]
  push_cast
  field_simp
  ring

/-- `Φ` sends a clean cell into `[0, U')` with `U' = packedCapacity D F`.
Blueprint 02 LEM-REPACK-03. -/
theorem repackMap_inCapacity {D : ℕ} {F : List ℕ} {q : DyadicCell} (hq : IsClean D F q) :
    CellInCapacity (packedCapacity D F) (repackMap D F q) := by
  obtain ⟨e, he, hqe, hΦ⟩ := exists_entry_repackMap hq
  have he2 : e.2 = (e.1.1, e.2.2) := Prod.ext (packBlocks_depth he) rfl
  have hsub : CellSubset (repackMap D F q) e.2 := by
    rw [hΦ, he2]
    exact cellSubset_translate (depth_le_depth_of_cellSubset hqe)
  refine cellInCapacity_of_cellSubset hsub (le_trans (packBlocks_inCapacity he) ?_)
  rw [sum_cellLength_cleanBlocks, packedCapacity]
  gcongr
  exact ((blockCells_nodup D F).subperm fun x hx => mem_blockCells_iff.1 hx).length_le

/-- On clean cells, `Φ` preserves and reflects disjointness: inside one block it is a
translation, and distinct blocks have disjoint originals and disjoint packed copies.
Blueprint 02 LEM-REPACK-03. -/
theorem cellsDisjoint_repackMap_iff {D : ℕ} {F : List ℕ} {q q' : DyadicCell}
    (hq : IsClean D F q) (hq' : IsClean D F q') :
    CellsDisjoint (repackMap D F q) (repackMap D F q') ↔ CellsDisjoint q q' := by
  have hsymm : Symmetric CellsDisjoint := fun _ _ h => Or.symm h
  obtain ⟨e, he, hqe, hΦ⟩ := exists_entry_repackMap hq
  obtain ⟨e', he', hqe', hΦ'⟩ := exists_entry_repackMap hq'
  rw [hΦ, hΦ']
  by_cases hee : e = e'
  · subst hee
    have hR : ∀ (c : DyadicCell) (i : ℕ), cellRight (c.1, i) = cellLeft (c.1, i) + cellLength c :=
      fun c i => by
        rw [show cellLength c = cellLength (c.1, i) from rfl, cellLength_eq_cellRight_sub_cellLeft]
        ring
    have hRq := hR q (e.2.2 * 2 ^ (q.1 - e.1.1) + q.2 % 2 ^ (q.1 - e.1.1))
    have hRq' := hR q' (e.2.2 * 2 ^ (q'.1 - e.1.1) + q'.2 % 2 ^ (q'.1 - e.1.1))
    have hLq := cellLeft_translate (a := e.2.2) hqe
    have hLq' := cellLeft_translate (a := e.2.2) hqe'
    have h1 := cellLength_eq_cellRight_sub_cellLeft q
    have h1' := cellLength_eq_cellRight_sub_cellLeft q'
    unfold CellsDisjoint
    constructor <;> rintro (h | h)
    · left; linarith
    · right; linarith
    · left; linarith
    · right; linarith
  · have hnodup : ((packBlocks (cleanBlocks D F)).map Prod.fst).Nodup :=
      (packBlocks_map_fst_perm _).nodup_iff.2 (cleanBlocks_nodup D F)
    have hmem : ∀ x ∈ packBlocks (cleanBlocks D F), x.1 ∈ cleanBlocks D F :=
      fun x hx => (packBlocks_map_fst_perm _).subset (List.mem_map_of_mem hx)
    have horig : CellsDisjoint e.1 e'.1 := (cleanBlocks_pairwise_disjoint D F).forall hsymm
      (hmem e he) (hmem e' he') fun h => hee (List.inj_on_of_nodup_map hnodup he he' h)
    have hcopy : CellsDisjoint e.2 e'.2 :=
      (List.pairwise_map.1 (packBlocks_pairwise_disjoint _)).forall (fun _ _ h => hsymm h)
        he he' hee
    have hsub : ∀ {x : DyadicCell × DyadicCell} {c : DyadicCell}, x ∈ packBlocks (cleanBlocks D F) →
        CellSubset c x.1 →
        CellSubset (c.1, x.2.2 * 2 ^ (c.1 - x.1.1) + c.2 % 2 ^ (c.1 - x.1.1)) x.2 := by
      intro x c hx hcx
      rw [show x.2 = (x.1.1, x.2.2) from Prod.ext (packBlocks_depth hx) rfl]
      exact cellSubset_translate (depth_le_depth_of_cellSubset hcx)
    constructor
    · intro _
      exact cellsDisjoint_of_cellSubset_left hqe
        (hsymm (cellsDisjoint_of_cellSubset_left hqe' (hsymm horig)))
    · intro _
      exact cellsDisjoint_of_cellSubset_left (hsub he hqe)
        (hsymm (cellsDisjoint_of_cellSubset_left (hsub he' hqe') (hsymm hcopy)))

/-- `List.find?` with a primitive recursive predicate is primitive recursive (a right fold).
Blueprint 02 LEM-REPACK-03. -/
private theorem primrec_find? {α β : Type*} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) := by
  refine (Primrec.list_foldr hf (Primrec.const none)
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldr_cons, List.find?_cons] at ih ⊢
    rw [ih]
    cases p a b <;> rfl

/-- Containment of cells is a primitive recursive relation (integer refinement to the common
depth). Blueprint 02 DEF-02. -/
private theorem primrecRel_cellSubset : PrimrecRel CellSubset := by
  have hM : Primrec fun p : DyadicCell × DyadicCell => max p.1.1 p.2.1 :=
    Primrec.nat_max.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have h1 : Primrec fun p : DyadicCell × DyadicCell => 2 ^ (max p.1.1 p.2.1 - p.1.1) :=
    primrec_two_pow.comp (Primrec.nat_sub.comp hM (Primrec.fst.comp Primrec.fst))
  have h2 : Primrec fun p : DyadicCell × DyadicCell => 2 ^ (max p.1.1 p.2.1 - p.2.1) :=
    primrec_two_pow.comp (Primrec.nat_sub.comp hM (Primrec.fst.comp Primrec.snd))
  exact (PrimrecPred.and
    (Primrec.nat_le.comp (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) h2)
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) h1))
    (Primrec.nat_le.comp (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.snd.comp
      Primrec.fst)) h1) (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.snd.comp
        Primrec.snd)) h2))).of_eq fun p => (cellSubset_iff_refined p.1 p.2).symm

/-- `Φ` is primitive recursive in `(D, F, q)`. Blueprint 02 LEM-REPACK-03. -/
theorem primrec_repackMap :
    Primrec fun a : (ℕ × List ℕ) × DyadicCell => repackMap a.1.1 a.1.2 a.2 := by
  have hfind : Primrec fun a : (ℕ × List ℕ) × DyadicCell =>
      (packBlocks (cleanBlocks a.1.1 a.1.2)).find? fun e => decide (CellSubset a.2 e.1) :=
    primrec_find? (primrec_packBlocks.comp (primrec_cleanBlocks.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))
      (primrecRel_cellSubset.decide.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
  have hpw : Primrec fun q : ((ℕ × List ℕ) × DyadicCell) × (DyadicCell × DyadicCell) =>
      2 ^ (q.1.2.1 - q.2.1.1) :=
    primrec_two_pow.comp (Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
  have hsome : Primrec₂ fun (a : (ℕ × List ℕ) × DyadicCell) (e : DyadicCell × DyadicCell) =>
      ((a.2.1, e.2.2 * 2 ^ (a.2.1 - e.1.1) + a.2.2 % 2 ^ (a.2.1 - e.1.1)) : DyadicCell) :=
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.snd.comp (Primrec.snd.comp
        Primrec.snd)) hpw) (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.snd.comp
          Primrec.fst)) hpw))).to₂
  refine (Primrec.option_casesOn hfind Primrec.snd hsome).of_eq fun a => ?_
  unfold repackMap
  cases List.find? (fun e => decide (CellSubset a.2 e.1)) (packBlocks (cleanBlocks a.1.1 a.1.2))
    <;> rfl

end Kolmogorov
