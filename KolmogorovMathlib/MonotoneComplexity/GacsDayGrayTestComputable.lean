import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.GacsDayEmbedding
import KolmogorovMathlib.MonotoneComplexity.GacsDayEmbedding.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame
import KolmogorovMathlib.MonotoneComplexity.GacsDayReserveComputable
import KolmogorovMathlib.MonotoneComplexity.NestedAllocation

/-!
# The gray-cell test of SUV pp. 140-144 is computable

The endgame controller of SUV p. 144 runs one family game after another and has
to *stop each round at the moment its gray goal is reached*: without freezing a
round at its completion time the accumulated root request of later rounds is no
longer covered by the client's budget at the big root.  Freezing means deciding,
at each time, whether the gray outcome of `familyGrayGoal` already holds, so the
gray area has to be computed, not merely defined.

This file supplies the computational side of the gray area:

* `comparableB` -- the Boolean prefix-comparability test against a finite list of
  cells, matched with the set-level predicate of `neighborhoodCells`;
* `neighborhoodCellsList` and `newGrayCellsList` -- list forms of the two gray
  constructions of `GacsDayGrayArea`, proved to have the corresponding finsets as
  their `toFinset` and to be duplicate free, hence to have the same cardinality;
* `primrec_newGrayCellsList` -- joint primitive recursiveness in the two scales
  and the two cell lists, and `primrec_newGrayCount` for the cardinality;
* `grayMassOfCount` and `familyGrayMass_eq_grayMassOfCount` -- the gray mass as a
  rational function of that (computable) count.
-/

namespace Kolmogorov

/-- `List.zip` written as a map over the common index range. -/
theorem list_zip_eq_map_range {α β : Type*} [Inhabited α] [Inhabited β] :
    ∀ (l1 : List α) (l2 : List β),
      l1.zip l2 = (List.range (min l1.length l2.length)).map
        (fun i => (l1.getD i default, l2.getD i default)) := by
  intro l1
  induction l1 with
  | nil => intro l2; simp
  | cons a t ih =>
    intro l2
    cases l2 with
    | nil => simp
    | cons b s =>
      have h := ih s
      simp only [List.zip_cons_cons, List.length_cons, h]
      rw [show min (t.length + 1) (s.length + 1) =
        min t.length s.length + 1 by omega, List.range_succ_eq_map]
      simp

open Primrec

/-! ### `List.any` is primitive recursive -/

/-! ### The Boolean comparability test -/

/-- `p` is prefix-comparable to some cell of the list `S`. -/
def comparableB (S : List BitString) (p : BitString) : Bool :=
  S.any fun c => p.isPrefixOf c || c.isPrefixOf p

/-- The decidable comparability test holds exactly when some string of the list is comparable
with `p`. -/
lemma comparableB_eq_true_iff (S : List BitString) (p : BitString) :
    comparableB S p = true ↔ ∃ c ∈ S, p <+: c ∨ c <+: p := by
  simp [comparableB, isPrefixOf_eq_decide]

/-- The comparability test fails exactly when no string of the list is comparable with `p`. -/
lemma comparableB_eq_false_iff (S : List BitString) (p : BitString) :
    comparableB S p = false ↔ ¬ ∃ c ∈ S, p <+: c ∨ c <+: p := by
  rw [← Bool.not_eq_true, comparableB_eq_true_iff]

/-- The comparability test is primitive recursive. -/
theorem primrec₂_comparableB : Primrec₂ comparableB := by
  refine list_any_primrec (f := fun q : List BitString × BitString => q.1)
    (p := fun q c => q.2.isPrefixOf c || c.isPrefixOf q.2) Primrec.fst ?_
  exact (Primrec.or.comp
    (primrec₂_isPrefixOf_gen.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
    (primrec₂_isPrefixOf_gen.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂

/-! ### The list of neighborhood cells -/

/-- The list form of `neighborhoodCells`. -/
def neighborhoodCellsList (depth : ℕ) (S : List BitString) : List BitString :=
  (allStrings depth).filter (comparableB S)

/-- The list of neighbourhood cells has no repetitions. -/
lemma neighborhoodCellsList_nodup (depth : ℕ) (S : List BitString) :
    (neighborhoodCellsList depth S).Nodup :=
  (allStrings_nodup depth).filter _

/-- The list of neighbourhood cells contains exactly the strings of the given depth comparable
with a member of `S`. -/
@[simp]
lemma mem_neighborhoodCellsList (depth : ℕ) (S : List BitString) (p : BitString) :
    p ∈ neighborhoodCellsList depth S ↔
      p.length = depth ∧ ∃ c ∈ S, p <+: c ∨ c <+: p := by
  simp [neighborhoodCellsList, comparableB_eq_true_iff, and_comm]

/-- The list of neighbourhood cells enumerates the finite set `neighborhoodCells`. -/
lemma toFinset_neighborhoodCellsList (depth : ℕ) (S : List BitString) :
    (neighborhoodCellsList depth S).toFinset = neighborhoodCells depth S.toFinset := by
  ext p
  simp [mem_neighborhoodCells_iff_prefixComparable]

/-! ### The list of new gray cells -/

/-- The list form of `newGrayCells`. -/
def newGrayCellsList (epsDepth deltaDepth : ℕ) (S U : List BitString) : List BitString :=
  (allStrings deltaDepth).filter fun p =>
    comparableB S (p.take epsDepth) && !comparableB U p

/-- The list of new gray cells has no repetitions. -/
lemma newGrayCellsList_nodup (epsDepth deltaDepth : ℕ) (S U : List BitString) :
    (newGrayCellsList epsDepth deltaDepth S U).Nodup :=
  (allStrings_nodup deltaDepth).filter _

/-- The list of new gray cells contains exactly the strings of depth `deltaDepth` whose
truncation meets `S` and which avoid `U`. -/
lemma mem_newGrayCellsList {epsDepth deltaDepth : ℕ} {S U : List BitString} {p : BitString} :
    p ∈ newGrayCellsList epsDepth deltaDepth S U ↔
      p.length = deltaDepth ∧ (∃ c ∈ S, p.take epsDepth <+: c ∨ c <+: p.take epsDepth) ∧
        ¬ ∃ c ∈ U, p <+: c ∨ c <+: p := by
  rw [newGrayCellsList, List.mem_filter, mem_allStrings, Bool.and_eq_true, Bool.not_eq_true',
    comparableB_eq_true_iff, comparableB_eq_false_iff]

/-- Under `epsDepth ≤ deltaDepth` the list of gray cells is exactly the finset of
`newGrayCells` of the corresponding finsets. -/
lemma toFinset_newGrayCellsList {epsDepth deltaDepth : ℕ} (h : epsDepth ≤ deltaDepth)
    (S U : List BitString) :
    (newGrayCellsList epsDepth deltaDepth S U).toFinset
      = newGrayCells epsDepth deltaDepth S.toFinset U.toFinset := by
  ext p
  rw [List.mem_toFinset, mem_newGrayCellsList, mem_newGrayCells_iff]
  constructor
  · rintro ⟨hlen, h1, h2⟩
    refine ⟨hlen, ?_, ?_⟩
    · rw [mem_neighborhoodCells_iff_prefixComparable]
      refine ⟨by rw [List.length_take, hlen]; omega, ?_⟩
      obtain ⟨c, hc, hcp⟩ := h1
      exact ⟨c, List.mem_toFinset.mpr hc, hcp⟩
    · intro hmem
      obtain ⟨_, c, hc, hcp⟩ := mem_neighborhoodCells_iff_prefixComparable.mp hmem
      exact h2 ⟨c, List.mem_toFinset.mp hc, hcp⟩
  · rintro ⟨hlen, h1, h2⟩
    refine ⟨hlen, ?_, ?_⟩
    · obtain ⟨_, c, hc, hcp⟩ := mem_neighborhoodCells_iff_prefixComparable.mp h1
      exact ⟨c, List.mem_toFinset.mp hc, hcp⟩
    · rintro ⟨c, hc, hcp⟩
      exact h2 (mem_neighborhoodCells_iff_prefixComparable.mpr
        ⟨hlen, c, List.mem_toFinset.mpr hc, hcp⟩)

/-- The number of new gray cells, computed from lists. -/
def newGrayCount (epsDepth deltaDepth : ℕ) (S U : List BitString) : ℕ :=
  (newGrayCellsList epsDepth deltaDepth S U).length

/-- The counting function `newGrayCount` computes the number of new gray cells. -/
lemma card_newGrayCells_eq_newGrayCount {epsDepth deltaDepth : ℕ} (h : epsDepth ≤ deltaDepth)
    (S U : List BitString) :
    (newGrayCells epsDepth deltaDepth S.toFinset U.toFinset).card
      = newGrayCount epsDepth deltaDepth S U := by
  rw [← toFinset_newGrayCellsList h S U,
    List.toFinset_card_of_nodup (newGrayCellsList_nodup epsDepth deltaDepth S U), newGrayCount]

/-! ### Primitive recursiveness -/

private lemma allStrings_eq_natRec (n : ℕ) :
    Nat.rec ([[]] : List BitString)
      (fun (_ : ℕ) (IH : List BitString) =>
        IH.map (List.cons false) ++ IH.map (List.cons true)) n = allStrings n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [allStrings, ← ih]

/-- The parameters of the gray test: the two scales and the two cell lists. -/
abbrev GrayParam := (ℕ × ℕ) × List BitString × List BitString

/-- Listing the new gray cells is primitive recursive in the depths and the two lists. -/
theorem primrec_newGrayCellsList :
    Primrec fun q : GrayParam => newGrayCellsList q.1.1 q.1.2 q.2.1 q.2.2 := by
  have heps : Primrec fun q : GrayParam => q.1.1 := Primrec.fst.comp Primrec.fst
  have hdelta : Primrec fun q : GrayParam => q.1.2 := Primrec.snd.comp Primrec.fst
  have hS : Primrec fun q : GrayParam => q.2.1 := Primrec.fst.comp Primrec.snd
  have hU : Primrec fun q : GrayParam => q.2.2 := Primrec.snd.comp Primrec.snd
  refine list_filter_primrec (CodedFiniteDistribution.allStrings_primrec.comp hdelta) ?_
  have hleft : Primrec fun r : GrayParam × BitString =>
      comparableB r.1.2.1 (r.2.take r.1.1.1) :=
    primrec₂_comparableB.comp (hS.comp Primrec.fst)
      (Primrec.list_take.comp Primrec.snd (heps.comp Primrec.fst))
  have hright : Primrec fun r : GrayParam × BitString => comparableB r.1.2.2 r.2 :=
    primrec₂_comparableB.comp (hU.comp Primrec.fst) Primrec.snd
  exact (Primrec.and.comp hleft (Primrec.not.comp hright)).to₂

/-- Counting the new gray cells is primitive recursive in the depths and the two lists. -/
theorem primrec_newGrayCount :
    Primrec fun q : GrayParam => newGrayCount q.1.1 q.1.2 q.2.1 q.2.2 :=
  Primrec.list_length.comp primrec_newGrayCellsList

/-! ### The gray mass as a function of the count -/

/-- The gray mass attached to a number of gray cells at depth `deltaDepth`. -/
def grayMassOfCount (deltaDepth count : ℕ) : ℚ := (count : ℚ) * (1 / 2 : ℚ) ^ deltaDepth

/-- The gray mass of a family play is the mass attached to the number of new gray cells. -/
lemma familyGrayMass_eq_grayMassOfCount {epsDepth deltaDepth : ℕ}
    (h : epsDepth ≤ deltaDepth) (n T : ℕ) (A : Allocation) (sm : ℕ → FamilyServerMove)
    (S : List BitString) (hS : S.toFinset = familyAllocated n T sm) :
    familyGrayMass epsDepth deltaDepth n T A sm
      = grayMassOfCount deltaDepth (newGrayCount epsDepth deltaDepth S A) := by
  rw [familyGrayMass, grayMassOfCount, ← card_newGrayCells_eq_newGrayCount h S A, hS]

/-! ### The allocated cells of a family, as a list -/

/-- The list form of `familyAllocated`. -/
def familyAllocatedList (n T : ℕ) (sm : ℕ → FamilyServerMove) : List BitString :=
  (List.range n).flatMap fun i => getFamilyAlloc (sm T) i []

/-- The list of allocated strings of a family play enumerates the set `familyAllocated`. -/
lemma toFinset_familyAllocatedList (n T : ℕ) (sm : ℕ → FamilyServerMove) :
    (familyAllocatedList n T sm).toFinset = familyAllocated n T sm := by
  ext p
  simp only [List.mem_toFinset, familyAllocatedList, List.mem_flatMap, List.mem_range,
    familyAllocated, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hp⟩
    exact ⟨⟨i, hi⟩, hp⟩
  · rintro ⟨i, hp⟩
    exact ⟨i.val, i.isLt, hp⟩

/-- The gray mass of a family game is the computable count of gray cells,
weighted by the depth. -/
lemma familyGrayMass_eq_grayMassOfCount_list {epsDepth deltaDepth : ℕ}
    (h : epsDepth ≤ deltaDepth) (n T : ℕ) (A : Allocation) (sm : ℕ → FamilyServerMove) :
    familyGrayMass epsDepth deltaDepth n T A sm
      = grayMassOfCount deltaDepth
          (newGrayCount epsDepth deltaDepth (familyAllocatedList n T sm) A) :=
  familyGrayMass_eq_grayMassOfCount h n T A sm _ (toFinset_familyAllocatedList n T sm)

/-! ### Deciding the gray goal at a fixed time -/

/-- The Boolean form of the three inequalities of `familyGrayGoal`, at a fixed
time `T`.  This is the test that lets the endgame controller of SUV p. 144
*freeze* a round at the moment its gray outcome appears, instead of letting the
round run on and overspend the client's budget at the big root. -/
def familyGrayGoalAtB (kappa beta : ℚ) (epsDepth deltaDepth n : ℕ) (A : Allocation)
    (c : FamilyClientMove) (sList : List BitString) : Bool :=
  let g := grayMassOfCount deltaDepth
    (newGrayCount epsDepth deltaDepth sList A)
  decide ((n : ℚ) * beta ≤ g) && decide (kappa * totalRootRequest n c ≤ g) &&
    decide ((n : ℚ) * beta ≤ kappa * totalRootRequest n c)

/-- The decidable gray goal holds exactly when the gray mass is at least both `n * beta` and
`kappa` times the total root request, and `n * beta` is below that amplified request. -/
lemma familyGrayGoalAtB_eq_true_iff {kappa beta : ℚ} {epsDepth deltaDepth : ℕ}
    (h : epsDepth ≤ deltaDepth) (n T : ℕ) (A : Allocation) (cm : ℕ → FamilyClientMove)
    (sm : ℕ → FamilyServerMove) :
    familyGrayGoalAtB kappa beta epsDepth deltaDepth n A (cm T) (familyAllocatedList n T
      sm) = true ↔
      ((n : ℚ) * beta ≤ familyGrayMass epsDepth deltaDepth n T A sm ∧
        kappa * totalRootRequest n (cm T) ≤ familyGrayMass epsDepth deltaDepth n T A sm ∧
        (n : ℚ) * beta ≤ kappa * totalRootRequest n (cm T)) := by
  rw [familyGrayGoalAtB, familyGrayMass_eq_grayMassOfCount_list h n T A sm]
  simp [and_assoc]

/-! ### The total root request is computable -/

private lemma foldr_add_init (f : ℕ → ℚ) : ∀ (l : List ℕ) (v : ℚ),
    l.foldr (fun i acc => f i + acc) v = l.foldr (fun i acc => f i + acc) 0 + v := by
  intro l
  induction l with
  | nil => intro v; simp
  | cons a t ih => intro v; simp only [List.foldr_cons, ih v]; ring

/-- The sum of the root requests of a family move, as a fold over `List.range`. -/
lemma totalRootRequest_eq_foldr (n : ℕ) (c : FamilyClientMove) :
    totalRootRequest n c = (List.range n).foldr (fun i acc => getFamilyReq c i [] + acc) 0 := by
  rw [totalRootRequest, show (∑ i : Fin n, getFamilyReq c i.val [])
    = ∑ i ∈ Finset.range n, getFamilyReq c i [] from
      (Finset.sum_range fun i => getFamilyReq c i []).symm]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.foldr_append, ih]
    simp only [List.foldr_cons, List.foldr_nil]
    have h := foldr_add_init (fun i => getFamilyReq c i []) (List.range k) (getFamilyReq c k [] + 0)
    simp only at h
    rw [h]
    ring

/-- The total root request is computable in the client count and the move. -/
theorem computable₂_totalRootRequest : Computable₂ (fun (n : ℕ) (c : FamilyClientMove) =>
  totalRootRequest n c) := by
  have hl : Computable (fun (p : ℕ × FamilyClientMove) => List.range p.1) :=
    Primrec.list_range.to_comp.comp Computable.fst
  have hg : Computable (fun (p : ℕ × FamilyClientMove) => (0 : ℚ)) :=
    Computable.const 0
  have hreq : Computable₂ (fun (p : ℕ × FamilyClientMove) (i : ℕ) => getFamilyReq p.2 i []) := by
    have hmove : Computable₂ (fun (p : ℕ × FamilyClientMove) (i : ℕ) => familyClientMoveAt p.2 i) :=
      by
      have hc : Computable (fun p : (ℕ × FamilyClientMove) × ℕ => p.1.2) :=
        Computable.snd.comp Computable.fst
      have hi : Computable (fun p : (ℕ × FamilyClientMove) × ℕ => p.2) := Computable.snd
      have hgetD := (Primrec.list_getD []).to_comp.comp hc hi
      exact hgetD.of_eq (fun _ => rfl)
    have hnode : Computable (fun p : (ℕ × FamilyClientMove) × ℕ => ([] : GacsDayNode)) :=
      Computable.const []
    have hget := primrec_getReq.to_comp.comp (hmove.comp Computable.fst Computable.snd) hnode
    exact hget.of_eq (fun _ => rfl)
  have hh : Computable₂ (fun (p : ℕ × FamilyClientMove) (is : ℕ × ℚ) =>
    getFamilyReq p.2 is.1 [] + is.2) := by
    have h1 : Computable (fun x : (ℕ × FamilyClientMove) × (ℕ × ℚ) =>
      getFamilyReq x.1.2 x.2.1 []) :=
      hreq.comp Computable.fst (Computable.fst.comp Computable.snd)
    have h2 : Computable (fun x : (ℕ × FamilyClientMove) × (ℕ × ℚ) => x.2.2) :=
      Computable.snd.comp Computable.snd
    exact computable₂_ratAdd.comp h1 h2
  have hfold := Computable.list_foldr hl hg hh
  exact hfold.of_eq (fun p => by
    change List.foldr (fun b s =>
      getFamilyReq p.2 b [] + s) 0 (List.range p.1) = totalRootRequest p.1 p.2
    rw [totalRootRequest_eq_foldr])

/-- For a fixed client count, the total root request is computable in the move. -/
theorem computable_totalRootRequest (n : ℕ) :
    Computable (fun c : FamilyClientMove => totalRootRequest n c) :=
  computable₂_totalRootRequest.comp (Computable.const n) Computable.id

/-! ### The dyadic scales are computable -/

/-- The dyadic scale `2 ^ (-d)` is computable in `d`. -/
theorem computable_dyadicScale : Computable dyadicScale := by
  apply computable_of_num_den (Computable.const 1) comp_pow (fun a => Nat.two_pow_pos a)
  intro a
  unfold dyadicScale
  have h1 : ((1 / 2 : ℚ) ^ a) = 1 / (2 ^ a : ℚ) := by
    exact one_div_pow (2:ℚ) a
  rw [h1]
  push_cast
  rfl
/-- The half-step amplification factor is computable in the stage. -/
theorem computable_halfAmplification : Computable halfAmplification := by
  have hk : Computable (fun k : ℕ => (k : ℚ)) := computable_nat_to_rat
  have hk2 : Computable (fun k : ℕ => (k : ℚ) / 2) := by
    have hhalf : Computable (fun k : ℕ => (k : ℚ) / 2) :=
      computable_ratHalf.comp hk
    exact hhalf
  exact computable₂_ratAdd.comp (Computable.const 1) hk2

/-- The packed argument of the gray goal test: the two rationals, the two depths, the client
count and allocation, and the client move with the allocated strings. -/
abbrev GrayGoalParam :=
  ((ℚ × ℚ) × (ℕ × ℕ)) × (ℕ × Allocation) × (FamilyClientMove × List BitString)

/-- Comparison of rationals is computable. -/
lemma computable_ratLe : Computable₂ (fun a b : ℚ => decide (a ≤ b)) := by
  have h1 : Computable₂ (fun a b : ℚ => decide (a - b + 1 ≤ 1)) :=
    computable_ratLeOne.comp (computable₂_ratAdd.comp computable₂_ratSub (Computable.const 1))
  exact h1.of_eq (fun p => by
    have heq : p.1 - p.2 + 1 ≤ 1 ↔ p.1 ≤ p.2 := by
      constructor
      · intro h
        have h2 : p.1 - p.2 ≤ 0 := by linarith
        linarith
      · intro h
        linarith
    exact decide_eq_decide.mpr heq)

/-- The mass attached to a cell count is computable in the depth and the count. -/
lemma computable_grayMassOfCount : Computable₂ grayMassOfCount := by
  have hc : Computable (fun p : ℕ × ℕ => (p.2 : ℚ)) :=
    computable_nat_to_rat.comp Computable.snd
  have hd : Computable (fun p : ℕ × ℕ => dyadicScale p.1) :=
    computable_dyadicScale.comp Computable.fst
  have hmul : Computable (fun p : ℕ × ℕ => (p.2 : ℚ) * dyadicScale p.1) :=
    computable₂_ratMul.comp hc hd
  exact hmul.of_eq (fun p => by
    unfold grayMassOfCount dyadicScale
    rfl)

/-- The gray goal test is computable in all its arguments jointly. -/
theorem computable_familyGrayGoalAtB_joint :
    Computable (fun q : GrayGoalParam =>
      familyGrayGoalAtB q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2.1.1 q.2.1.2 q.2.2.1 q.2.2.2) := by
  have hk : Computable (fun q : GrayGoalParam => q.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp (Computable.fst))
  have hb : Computable (fun q : GrayGoalParam => q.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst))
  have he : Computable (fun q : GrayGoalParam => q.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst))
  have hd : Computable (fun q : GrayGoalParam => q.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst))
  have hn : Computable (fun q : GrayGoalParam => q.2.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hA : Computable (fun q : GrayGoalParam => q.2.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hc : Computable (fun q : GrayGoalParam => q.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun q : GrayGoalParam => q.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have h_count :=
    primrec_newGrayCount.to_comp.comp (Computable.pair (Computable.pair he hd)
    (Computable.pair hs hA))
  have hg := computable_grayMassOfCount.comp hd h_count
  have hn_rat := computable_nat_to_rat.comp hn
  have h_n_beta := computable₂_ratMul.comp hn_rat hb
  have h_req := computable₂_totalRootRequest.comp hn hc
  have h_k_req := computable₂_ratMul.comp hk h_req
  have hd1 := computable_ratLe.comp h_n_beta hg
  have hd2 := computable_ratLe.comp h_k_req hg
  have hd3 := computable_ratLe.comp h_n_beta h_k_req
  have hand1 := (Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp hd1 hd2
  have hand2 := (Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp hand1 hd3
  exact hand2.of_eq (fun q => by
    unfold familyGrayGoalAtB
    rfl)

/-- For fixed parameters, the gray goal test is computable in the client move and the allocated
strings. -/
theorem computable_familyGrayGoalAtB (kappa beta : ℚ) (epsDepth deltaDepth n : ℕ) (A : Allocation) :
    Computable₂ (fun c sList => familyGrayGoalAtB kappa beta epsDepth deltaDepth n A c sList) := by
  have h_joint := computable_familyGrayGoalAtB_joint
  have h_args : Computable (fun p : FamilyClientMove × List BitString =>
      (((kappa, beta), (epsDepth, deltaDepth)), (n, A), p)) :=
    Computable.pair
      (Computable.const ((kappa, beta), (epsDepth, deltaDepth)))
      (Computable.pair (Computable.const (n, A)) Computable.id)
  exact Computable₂.mk ((h_joint.comp h_args).of_eq (fun p => by
    unfold familyGrayGoalAtB
    rfl))

/-- The gray goal is the existence of a time at which the Boolean test fires. -/
lemma familyGrayGoal_iff_exists_familyGrayGoalAtB {kappa beta : ℚ}
    {epsDepth deltaDepth : ℕ} (h : epsDepth ≤ deltaDepth) (n : ℕ)
    (A : Allocation) (cm : ℕ → FamilyClientMove) (sm : ℕ → FamilyServerMove) :
    familyGrayGoal kappa beta epsDepth deltaDepth n A cm sm ↔
      ∃ T, familyGrayGoalAtB kappa beta epsDepth deltaDepth n A
        (cm T) (familyAllocatedList n T sm) = true := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T, (familyGrayGoalAtB_eq_true_iff h n T A cm sm).mpr hT⟩
  · rintro ⟨T, hT⟩
    exact ⟨T, (familyGrayGoalAtB_eq_true_iff h n T A cm sm).mp hT⟩

/-- If a gray goal is reached, it has a first time, before which the Boolean
test is false. -/
lemma exists_least_grayGoalTime {kappa beta : ℚ} {epsDepth deltaDepth : ℕ}
    (h : epsDepth ≤ deltaDepth) (n : ℕ) (A : Allocation)
    (cm : ℕ → FamilyClientMove) (sm : ℕ → FamilyServerMove)
    (hgoal : familyGrayGoal kappa beta epsDepth deltaDepth n A cm sm) :
    ∃ T, (((n : ℚ) * beta ≤ familyGrayMass epsDepth deltaDepth n T A sm ∧
        kappa * totalRootRequest n (cm T) ≤
          familyGrayMass epsDepth deltaDepth n T A sm ∧
        (n : ℚ) * beta ≤ kappa * totalRootRequest n (cm T)) ∧
      ∀ t < T, familyGrayGoalAtB kappa beta epsDepth deltaDepth n A
        (cm t) (familyAllocatedList n t sm) = false) := by
  classical
  have hex : ∃ T, familyGrayGoalAtB kappa beta epsDepth deltaDepth n A
      (cm T) (familyAllocatedList n T sm) = true :=
    (familyGrayGoal_iff_exists_familyGrayGoalAtB h n A cm sm).mp hgoal
  refine ⟨Nat.find hex,
    (familyGrayGoalAtB_eq_true_iff h _ _ A cm sm).mp (Nat.find_spec hex),
    fun t ht => ?_⟩
  simpa using Nat.find_min hex ht

end Kolmogorov


namespace Kolmogorov

/-- The allocation a server move gives to a node is read off by a fold over its entries. -/
lemma getAlloc_eq_foldr (sm : ServerMove) (A : GacsDayNode) :
    getAlloc sm A = sm.foldr (fun p s => bif p.1 == A then p.2 else s) [] := by
  unfold getAlloc
  induction sm with
  | nil => rfl
  | cons p t ih =>
    simp [List.lookup]
    by_cases h : p.1 = A
    · have h1 : (A == p.1) = true := beq_iff_eq.mpr h.symm
      have h2 : (p.1 == A) = true := beq_iff_eq.mpr h
      simp [h1, h2]
    · have h1 : (A == p.1) = false := beq_eq_false_iff_ne.mpr (fun hh => h hh.symm)
      have h2 : (p.1 == A) = false := beq_eq_false_iff_ne.mpr h
      simp [h1, h2, ih]

/-- Reading the allocation of a node out of a server move is computable. -/
theorem computable₂_getAlloc :
    Computable₂ (fun (sm : ServerMove) (A : GacsDayNode) => getAlloc sm A) := by
  have hdec : Computable₂ (fun (a b : GacsDayNode) => a == b) := by
    have h1 : Computable₂ (fun (a b : GacsDayNode) => decide (a = b)) :=
      Primrec.to_comp primrec_decideEq
    exact h1.of_eq (fun p => by
      have hbeq : (p.1 == p.2) = decide (p.1 = p.2) := by
        cases h : p.1 == p.2
        · have : p.1 ≠ p.2 := beq_eq_false_iff_ne.mp h
          simp [this]
        · have : p.1 = p.2 := beq_iff_eq.mp h
          simp [this]
      exact hbeq.symm)
  have hstep : Computable₂ (fun (z : ServerMove × GacsDayNode) (p : (GacsDayNode × Allocation) ×
    Allocation) =>
      bif p.1.1 == z.2 then p.1.2 else p.2) := by
    have h1 : Computable (fun w : (ServerMove × GacsDayNode) × ((GacsDayNode × Allocation) ×
      Allocation) =>
      bif w.2.1.1 == w.1.2 then w.2.1.2 else w.2.2) :=
      Computable.cond
        (hdec.comp (Computable.fst.comp (Computable.fst.comp Computable.snd))
          (Computable.snd.comp Computable.fst))
        (Computable.snd.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd)
    exact Computable₂.mk h1
  have hfold : Computable (fun z : ServerMove × GacsDayNode =>
      z.1.foldr (fun p s => bif p.1 == z.2 then p.2 else s) []) :=
    Computable.list_foldr Computable.fst (Computable.const []) hstep
  apply Computable₂.mk
  apply Computable.of_eq hfold
  intro z
  exact (getAlloc_eq_foldr z.1 z.2).symm

/-- Listing the new gray cells is computable in the depths, the allocated strings and the
unavailable allocation. -/
theorem computable_newGrayCellsList :
    Computable (fun p : (ℕ × ℕ) × (List BitString × Allocation) =>
      newGrayCellsList p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h : Primrec fun q : GrayParam => newGrayCellsList q.1.1 q.1.2 q.2.1 q.2.2 :=
    primrec_newGrayCellsList
  exact h.to_comp

end Kolmogorov
