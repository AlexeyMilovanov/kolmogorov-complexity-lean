import KolmogorovMathlib.Restricted.Family
import KolmogorovMathlib.Restricted.CoverSearch
import KolmogorovMathlib.AlgorithmicStatistics.NonStochastic

/-!
# Computable maximum-intersection cover selection

The covering overhead stored in a `DescriptionFamily` is not assumed to be a
computable function.  Consequently the selector takes the numerical overhead
bound `q0` as part of its input.  At the paper-facing call site this input is
instantiated with `q0 = 𝒜.overhead n`; polynomial overhead bounds pay for its
encoding.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The member of a nonempty list of finite sets that maximizes intersection
with `C`.  The head seed is essential: a fold seeded by `∅` can return `∅` when
all intersections are empty, even if `∅` is not a member of the cover. -/
def coverArgmax (C : Finset BitString) : List (Finset BitString) → Finset BitString
  | [] => ∅
  | B :: cover =>
      cover.foldl
        (fun acc B' => if (B' ∩ C).card > (acc ∩ C).card then B' else acc) B

private lemma coverArgmax_foldl_mem {C : Finset BitString}
    {seed : Finset BitString} {cover : List (Finset BitString)} :
    cover.foldl
        (fun acc B => if (B ∩ C).card > (acc ∩ C).card then B else acc) seed
      ∈ seed :: cover := by
  induction cover generalizing seed with
  | nil => simp
  | cons B cover ih =>
      simp only [List.foldl_cons]
      by_cases h : (B ∩ C).card > (seed ∩ C).card
      · simp only [if_pos h]
        exact List.mem_cons_of_mem seed (ih (seed := B))
      · simp only [if_neg h]
        have hi := List.mem_cons.mp (ih (seed := seed))
        exact List.mem_cons.mpr (hi.elim Or.inl
          (fun hcover => Or.inr (List.mem_cons.mpr (Or.inr hcover))))

lemma cover_argmax_mem {C : Finset BitString} {cover : List (Finset BitString)}
    (h_nonempty : cover ≠ []) :
    coverArgmax C cover ∈ cover := by
  cases cover with
  | nil => exact False.elim (h_nonempty rfl)
  | cons B cover =>
      exact coverArgmax_foldl_mem

private lemma coverArgmax_foldl_max {C : Finset BitString}
    {seed B : Finset BitString} {cover : List (Finset BitString)}
    (hB : B ∈ seed :: cover) :
    (B ∩ C).card ≤
      (cover.foldl
        (fun acc B' => if (B' ∩ C).card > (acc ∩ C).card then B' else acc) seed ∩ C).card := by
  induction cover generalizing seed B with
  | nil =>
      simp only [List.foldl_nil]
      have hEq : B = seed := by simpa using hB
      simp [hEq]
  | cons B' cover ih =>
      simp only [List.foldl_cons]
      by_cases h : (B' ∩ C).card > (seed ∩ C).card
      · simp only [if_pos h]
        rcases List.mem_cons.mp hB with hBseed | hBtail
        · rw [hBseed]
          exact (Nat.le_of_lt h).trans (ih (seed := B') (B := B') (by simp))
        · exact ih (seed := B') (B := B) hBtail
      · simp only [if_neg h]
        rcases List.mem_cons.mp hB with hBseed | hBtail
        · rw [hBseed]
          exact ih (seed := seed) (B := seed) (by simp)
        · rcases List.mem_cons.mp hBtail with hBB' | hBcover
          · rw [hBB']
            exact (Nat.le_of_not_gt h).trans (ih (seed := seed) (B := seed) (by simp))
          · exact ih (seed := seed) (B := B) (by simp [hBcover])

lemma cover_intersection_le_argmax {C B : Finset BitString}
    {cover : List (Finset BitString)} (hB : B ∈ cover) :
    (B ∩ C).card ≤ (coverArgmax C cover ∩ C).card := by
  cases cover with
  | nil => simp at hB
  | cons seed cover =>
      exact coverArgmax_foldl_max hB

lemma cover_argmax_intersection_bound {C : Finset BitString}
    {cover : List (Finset BitString)}
    (h_cover : ∀ x ∈ C, ∃ B ∈ cover, x ∈ B) :
    C.card ≤ cover.length * (coverArgmax C cover ∩ C).card := by
  classical
  let coverSet : Finset (Finset BitString) := cover.toFinset
  have hCsub : C ⊆ coverSet.biUnion (fun B => B ∩ C) := by
    intro x hxC
    obtain ⟨B, hBcover, hxB⟩ := h_cover x hxC
    rw [Finset.mem_biUnion]
    exact ⟨B, List.mem_toFinset.mpr hBcover,
      Finset.mem_inter.mpr ⟨hxB, hxC⟩⟩
  calc
    C.card ≤ (coverSet.biUnion (fun B => B ∩ C)).card :=
      Finset.card_le_card hCsub
    _ ≤ ∑ B ∈ coverSet, (B ∩ C).card := Finset.card_biUnion_le
    _ ≤ coverSet.card * (coverArgmax C cover ∩ C).card :=
      Finset.sum_le_card_nsmul coverSet (fun B => (B ∩ C).card)
        (coverArgmax C cover ∩ C).card (fun B hB =>
          cover_intersection_le_argmax (List.mem_toFinset.mp hB))
    _ ≤ cover.length * (coverArgmax C cover ∩ C).card :=
      Nat.mul_le_mul_right _ (List.toFinset_card_le cover)

/-- Boolean validity of an enumerated cover.  The candidate must be nonempty;
all its codes must occur in one family-enumeration stage; every decoded set has
cardinality at most `c`; it covers `C`; and its length satisfies the supplied
overhead bound `q0 * #A / c` in multiplicative form. -/
def restrictedCoverValidBool (𝒜 : DescriptionFamily)
    (Acode Ccode : BitString) (c q0 p : ℕ) : Bool :=
  let Alist := decodeCoverCodeList Acode
  let Clist := decodeCoverCodeList Ccode
  let stage := (coverDecode p).1
  let cover := (coverDecode p).2
  (decide (cover ≠ [])) &&
    (cover.all (fun w => decide (w ∈ 𝒜.enumeration.enum stage))) &&
    (decide (cover.length * c ≤ q0 * Alist.dedup.length)) &&
    (cover.all (fun w =>
      decide ((decodeCoverCodeList w).dedup.length ≤ c))) &&
    (Clist.all (fun x =>
      cover.any (fun w => decide (x ∈ decodeCoverCodeList w))))

def restrictedCoverValidBool_f1 (a : BitString × BitString × ℕ × ℕ × ℕ) : Bool :=
  decide ((coverDecode a.2.2.2.2).2 ≠ [])

def restrictedCoverValidBool_f2_arg (𝒜 : DescriptionFamily)
    (a : BitString × BitString × ℕ × ℕ × ℕ) : List BitString × List BitString :=
  ((coverDecode a.2.2.2.2).2, 𝒜.enumeration.enum (coverDecode a.2.2.2.2).1)

def restrictedCoverValidBool_f2_fun (p : List BitString × List BitString) : Bool :=
  p.1.all (fun w => decide (w ∈ p.2))

def restrictedCoverValidBool_f3_arg (a : BitString × BitString × ℕ × ℕ × ℕ) : ℕ × ℕ :=
  ((coverDecode a.2.2.2.2).2.length * a.2.2.1, a.2.2.2.1 * (decodeCoverCodeList a.1).dedup.length)

def restrictedCoverValidBool_f3_fun (p : ℕ × ℕ) : Bool :=
  decide (p.1 ≤ p.2)

def restrictedCoverValidBool_f4_arg (a : BitString × BitString × ℕ × ℕ × ℕ) : List BitString × ℕ :=
  ((coverDecode a.2.2.2.2).2, a.2.2.1)

def restrictedCoverValidBool_f4_fun (p : List BitString × ℕ) : Bool :=
  p.1.all (fun w => decide ((decodeCoverCodeList w).dedup.length ≤ p.2))

def restrictedCoverValidBool_f5_arg
    (a : BitString × BitString × ℕ × ℕ × ℕ) : List BitString × List BitString :=
  (decodeCoverCodeList a.2.1, (coverDecode a.2.2.2.2).2)

def restrictedCoverValidBool_f5_fun (p : List BitString × List BitString) : Bool :=
  p.1.all (fun x => p.2.any (fun w => decide (x ∈ decodeCoverCodeList w)))

theorem restrictedCoverValidBool_computable (𝒜 : DescriptionFamily) :
    Computable (fun a : BitString × BitString × ℕ × ℕ × ℕ =>
      restrictedCoverValidBool 𝒜 a.1 a.2.1 a.2.2.1
        a.2.2.2.1 a.2.2.2.2) := by
  have h_nonempty : Computable restrictedCoverValidBool_f1 := by
    have hpos : Primrec (fun a : BitString × BitString × ℕ × ℕ × ℕ =>
        decide (0 < (coverDecode a.2.2.2.2).2.length)) :=
      PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.const 0)
        (Primrec.list_length.comp (Primrec.snd.comp
          (coverDecode_primrec.comp
            (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp (Primrec.snd))))))))
    exact hpos.to_comp.of_eq (fun a => by
      rw [restrictedCoverValidBool_f1]
      cases (coverDecode a.2.2.2.2).2 <;> simp)
  have h_enum : Computable (fun a =>
      restrictedCoverValidBool_f2_fun (restrictedCoverValidBool_f2_arg 𝒜 a)) := by
    have hpairs : Computable (restrictedCoverValidBool_f2_arg 𝒜) := by
      apply Computable.pair
      · exact Computable.snd.comp (coverDecode_primrec.to_comp.comp
          (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp Computable.snd))))
      · exact 𝒜.enumeration.computable.comp
          (Computable.fst.comp (coverDecode_primrec.to_comp.comp
            (Computable.snd.comp (Computable.snd.comp
              (Computable.snd.comp Computable.snd)))))
    have hall : Primrec restrictedCoverValidBool_f2_fun := by
      apply coverSearch_list_all_primrec Primrec.fst
      exact bitString_mem_primrec.comp Primrec.snd
        (Primrec.snd.comp Primrec.fst)
    exact hall.to_comp.comp hpairs
  have h_bound : Computable (fun a =>
      restrictedCoverValidBool_f3_fun (restrictedCoverValidBool_f3_arg a)) := by
    have hargs : Primrec restrictedCoverValidBool_f3_arg := by
      apply Primrec.pair
      · exact Primrec.nat_mul.comp
          (Primrec.list_length.comp (Primrec.snd.comp
            (coverDecode_primrec.comp
              (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd)))))))
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd)))
      · exact Primrec.nat_mul.comp
          (Primrec.fst.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd))))
          (Primrec.list_length.comp (dedup_primrec.comp
            (decodeCoverCodeList_primrec.comp Primrec.fst)))
    have hfun : Primrec restrictedCoverValidBool_f3_fun :=
      PrimrecPred.decide (Primrec.nat_le.comp Primrec.fst Primrec.snd)
    exact hfun.to_comp.comp hargs.to_comp
  have h_small : Computable (fun a =>
      restrictedCoverValidBool_f4_fun (restrictedCoverValidBool_f4_arg a)) := by
    have hargs : Primrec restrictedCoverValidBool_f4_arg := by
      apply Primrec.pair
      · exact Primrec.snd.comp (coverDecode_primrec.comp
          (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd)))))
      · exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd))
    have hfun : Primrec restrictedCoverValidBool_f4_fun := by
      apply coverSearch_list_all_primrec Primrec.fst
      apply PrimrecPred.decide
      exact Primrec.nat_le.comp
        (Primrec.list_length.comp (dedup_primrec.comp
          (decodeCoverCodeList_primrec.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.fst)
    exact hfun.to_comp.comp hargs.to_comp
  have h_cover : Computable (fun a =>
      restrictedCoverValidBool_f5_fun (restrictedCoverValidBool_f5_arg a)) := by
    have hargs : Primrec restrictedCoverValidBool_f5_arg := by
      apply Primrec.pair
      · exact decodeCoverCodeList_primrec.comp
          (Primrec.fst.comp Primrec.snd)
      · exact Primrec.snd.comp (coverDecode_primrec.comp
          (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd)))))
    have hfun : Primrec restrictedCoverValidBool_f5_fun := by
      apply coverSearch_list_all_primrec Primrec.fst
      apply list_any_primrec (Primrec.snd.comp Primrec.fst)
      exact bitString_mem_primrec.comp
        (Primrec.snd.comp Primrec.fst)
        (decodeCoverCodeList_primrec.comp Primrec.snd)
    exact hfun.to_comp.comp hargs.to_comp
  have H := Computable.cond h_nonempty
    (Computable.cond h_enum
      (Computable.cond h_bound
        (Computable.cond h_small h_cover (Computable.const false))
        (Computable.const false))
      (Computable.const false))
    (Computable.const false)
  refine Computable.of_eq H ?_
  intro a
  rw [restrictedCoverValidBool_f1, restrictedCoverValidBool_f2_fun, restrictedCoverValidBool_f2_arg,
      restrictedCoverValidBool_f3_fun, restrictedCoverValidBool_f3_arg,
      restrictedCoverValidBool_f4_fun, restrictedCoverValidBool_f4_arg,
      restrictedCoverValidBool_f5_fun, restrictedCoverValidBool_f5_arg]
  simp [restrictedCoverValidBool, Bool.and_assoc]

/-- Cardinality of the intersection of two decoded code lists.  The explicit
deduplicated-list form is extensionally the corresponding finset cardinality
and is convenient for the computability proof. -/
def decodedCoverIntersectionCard (Ccode w : BitString) : ℕ :=
  ((decodeCoverCodeList w).filter
    (fun x => decide (x ∈ decodeCoverCodeList Ccode))).dedup.length

lemma decodedCoverIntersectionCard_eq (Ccode w : BitString) :
    decodedCoverIntersectionCard Ccode w =
      ((decodeCoverCodeList w).toFinset ∩
        (decodeCoverCodeList Ccode).toFinset).card := by
  unfold decodedCoverIntersectionCard
  rw [← List.card_toFinset]
  rw [List.toFinset_filter]
  congr 1
  ext x
  simp

theorem decodedCoverIntersectionCard_primrec :
    Primrec (fun p : BitString × BitString =>
      decodedCoverIntersectionCard p.1 p.2) := by
  unfold decodedCoverIntersectionCard
  apply Primrec.list_length.comp
  apply dedup_primrec.comp
  apply list_filter_primrec
  · exact decodeCoverCodeList_primrec.comp Primrec.snd
  · exact bitString_mem_primrec.comp Primrec.snd
      (decodeCoverCodeList_primrec.comp (Primrec.fst.comp Primrec.fst))

/-- Select the code in `cover` whose decoded set has largest intersection with
the decoded candidate set `Ccode`. -/
def coverCodeArgmax (Ccode : BitString) : List BitString → BitString
  | [] => []
  | w :: cover =>
      cover.foldl (fun acc w' =>
        if decodedCoverIntersectionCard Ccode w' >
            decodedCoverIntersectionCard Ccode acc
        then w' else acc) w

private lemma coverCodeArgmax_foldl_mem {Ccode seed : BitString}
    {cover : List BitString} :
    cover.foldl (fun acc w =>
      if decodedCoverIntersectionCard Ccode w >
          decodedCoverIntersectionCard Ccode acc then w else acc) seed
      ∈ seed :: cover := by
  induction cover generalizing seed with
  | nil => simp
  | cons w cover ih =>
      simp only [List.foldl_cons]
      by_cases h : decodedCoverIntersectionCard Ccode w >
          decodedCoverIntersectionCard Ccode seed
      · simp only [if_pos h]
        exact List.mem_cons_of_mem seed (ih (seed := w))
      · simp only [if_neg h]
        have hi := List.mem_cons.mp (ih (seed := seed))
        exact List.mem_cons.mpr (hi.elim Or.inl
          (fun hcover => Or.inr (List.mem_cons.mpr (Or.inr hcover))))

lemma coverCodeArgmax_mem {Ccode : BitString} {cover : List BitString}
    (hcover : cover ≠ []) : coverCodeArgmax Ccode cover ∈ cover := by
  cases cover with
  | nil => exact False.elim (hcover rfl)
  | cons w cover => exact coverCodeArgmax_foldl_mem

private lemma coverCodeArgmax_foldl_max {Ccode seed w : BitString}
    {cover : List BitString} (hw : w ∈ seed :: cover) :
    decodedCoverIntersectionCard Ccode w ≤
      decodedCoverIntersectionCard Ccode
        (cover.foldl (fun acc w' =>
          if decodedCoverIntersectionCard Ccode w' >
              decodedCoverIntersectionCard Ccode acc then w' else acc) seed) := by
  induction cover generalizing seed w with
  | nil =>
      simp only [List.foldl_nil]
      have heq : w = seed := by simpa using hw
      simp [heq]
  | cons w' cover ih =>
      simp only [List.foldl_cons]
      by_cases h : decodedCoverIntersectionCard Ccode w' >
          decodedCoverIntersectionCard Ccode seed
      · simp only [if_pos h]
        rcases List.mem_cons.mp hw with hwseed | hwtail
        · rw [hwseed]
          exact (Nat.le_of_lt h).trans (ih (seed := w') (w := w') (by simp))
        · exact ih (seed := w') (w := w) hwtail
      · simp only [if_neg h]
        rcases List.mem_cons.mp hw with hwseed | hwtail
        · rw [hwseed]
          exact ih (seed := seed) (w := seed) (by simp)
        · rcases List.mem_cons.mp hwtail with hww' | hwcover
          · rw [hww']
            exact (Nat.le_of_not_gt h).trans
              (ih (seed := seed) (w := seed) (by simp))
          · exact ih (seed := seed) (w := w) (by simp [hwcover])

lemma decodedCoverIntersectionCard_le_argmax {Ccode w : BitString}
    {cover : List BitString} (hw : w ∈ cover) :
    decodedCoverIntersectionCard Ccode w ≤
      decodedCoverIntersectionCard Ccode (coverCodeArgmax Ccode cover) := by
  cases cover with
  | nil => simp at hw
  | cons seed cover => exact coverCodeArgmax_foldl_max hw

lemma coverCodeArgmax_intersection_bound (Ccode : BitString)
    (C : Finset BitString)
    (hCcode : decodeCoverCodeList Ccode = canonicalFinsetList C)
    {cover : List BitString}
    (hcover : ∀ x ∈ C, ∃ w ∈ cover, x ∈ decodeCoverCodeList w) :
    C.card ≤ cover.length *
      ((decodeCoverCodeList (coverCodeArgmax Ccode cover)).toFinset ∩ C).card := by
  classical
  let coverSet : Finset BitString := cover.toFinset
  have hCdecoded : (decodeCoverCodeList Ccode).toFinset = C := by
    rw [hCcode, canonicalFinsetList_toFinset]
  have hCsub : C ⊆ coverSet.biUnion (fun w =>
      (decodeCoverCodeList w).toFinset ∩ C) := by
    intro x hxC
    obtain ⟨w, hwcover, hxw⟩ := hcover x hxC
    rw [Finset.mem_biUnion]
    exact ⟨w, List.mem_toFinset.mpr hwcover,
      Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hxw, hxC⟩⟩
  calc
    C.card ≤ (coverSet.biUnion (fun w =>
        (decodeCoverCodeList w).toFinset ∩ C)).card :=
      Finset.card_le_card hCsub
    _ ≤ ∑ w ∈ coverSet,
        ((decodeCoverCodeList w).toFinset ∩ C).card :=
      Finset.card_biUnion_le
    _ ≤ coverSet.card *
        ((decodeCoverCodeList (coverCodeArgmax Ccode cover)).toFinset ∩ C).card :=
      Finset.sum_le_card_nsmul coverSet
        (fun w => ((decodeCoverCodeList w).toFinset ∩ C).card)
        ((decodeCoverCodeList (coverCodeArgmax Ccode cover)).toFinset ∩ C).card
        (fun w hw => by
          have hmax := decodedCoverIntersectionCard_le_argmax
            (Ccode := Ccode) (w := w) (List.mem_toFinset.mp hw)
          rw [decodedCoverIntersectionCard_eq,
            decodedCoverIntersectionCard_eq, hCdecoded] at hmax
          exact hmax)
    _ ≤ cover.length *
        ((decodeCoverCodeList (coverCodeArgmax Ccode cover)).toFinset ∩ C).card :=
      Nat.mul_le_mul_right _ (List.toFinset_card_le cover)

theorem coverCodeArgmax_primrec :
    Primrec (fun p : BitString × List BitString =>
      coverCodeArgmax p.1 p.2) := by
  let step : BitString × BitString × BitString → BitString := fun arg =>
    if decodedCoverIntersectionCard arg.1 arg.2.2 >
        decodedCoverIntersectionCard arg.1 arg.2.1 then
      arg.2.2
    else
      arg.2.1
  have hstep : Primrec step := by
    have hpred : PrimrecPred (fun arg : BitString × BitString × BitString =>
        decodedCoverIntersectionCard arg.1 arg.2.1 <
          decodedCoverIntersectionCard arg.1 arg.2.2) :=
      Primrec.nat_lt.comp
        (decodedCoverIntersectionCard_primrec.comp
          (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
        (decodedCoverIntersectionCard_primrec.comp
          (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)))
    exact Primrec.ite hpred (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  let fold : BitString × (BitString × List BitString) → BitString := fun p =>
    p.2.2.foldl (fun acc w => step (p.1, acc, w)) p.2.1
  have hfold : Primrec fold :=
    list_foldl_primrec
      (f := fun p : BitString × (BitString × List BitString) => p.2.2)
      (g := fun p : BitString × (BitString × List BitString) => p.2.1)
      (h := fun p acc w => step (p.1, acc, w))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)
      (hstep.comp
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp Primrec.fst)
            Primrec.snd)))
  refine (Primrec.list_casesOn Primrec.snd (Primrec.const [])
    ((hfold.comp (Primrec.pair
      (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂)).of_eq ?_
  rintro ⟨Ccode, cover⟩
  cases cover <;> rfl

/-- Tuple encoding used by the selector. This uses
the repository's `listCode` convention and explicitly carries `q0`. -/
def restrictedCoverSelectorInput
    (Acode Ccode : BitString) (c q0 : ℕ) : BitString :=
  listCode [Acode, Ccode, Nat.bits c, Nat.bits q0]

def restrictedSelectorField (input : BitString) (i : ℕ) : BitString :=
  (decodeListCode input).getD i []

theorem restrictedSelectorField_computable :
    Computable₂ restrictedSelectorField := by
  exact (Primrec.list_getD []).to_comp.comp
    (decodeListCode_computable.comp Computable.fst) Computable.snd

def restrictedSelectorCheck (𝒜 : DescriptionFamily)
    (input : BitString) (p : ℕ) : Bool :=
  restrictedCoverValidBool 𝒜
    (restrictedSelectorField input 0)
    (restrictedSelectorField input 1)
    (bitsToNat (restrictedSelectorField input 2))
    (bitsToNat (restrictedSelectorField input 3)) p

def restrictedSelectorCheckArgs
    (a : BitString × ℕ) : BitString × BitString × ℕ × ℕ × ℕ :=
  (restrictedSelectorField a.1 0,
    restrictedSelectorField a.1 1,
    bitsToNat (restrictedSelectorField a.1 2),
    bitsToNat (restrictedSelectorField a.1 3), a.2)

theorem restrictedSelectorCheckArgs_computable :
    Computable restrictedSelectorCheckArgs := by
  have hfield (i : ℕ) : Computable (fun input : BitString =>
      restrictedSelectorField input i) :=
    restrictedSelectorField_computable.comp Computable.id (Computable.const i)
  exact Computable.pair ((hfield 0).comp Computable.fst)
    (Computable.pair ((hfield 1).comp Computable.fst)
      (Computable.pair
        (bitsToNat_computable.comp ((hfield 2).comp Computable.fst))
        (Computable.pair
          (bitsToNat_computable.comp ((hfield 3).comp Computable.fst))
          Computable.snd)))

theorem restrictedSelectorCheck_computable (𝒜 : DescriptionFamily) :
    Computable₂ (restrictedSelectorCheck 𝒜) := by
  exact ((restrictedCoverValidBool_computable 𝒜).comp
    restrictedSelectorCheckArgs_computable).of_eq (fun _ => rfl)

def restrictedSelectorPost (input : BitString) (p : ℕ) : BitString :=
  coverCodeArgmax (restrictedSelectorField input 1) (coverDecode p).2

theorem restrictedSelectorPost_computable :
    Computable₂ restrictedSelectorPost := by
  exact coverCodeArgmax_primrec.to_comp.comp
    (Computable.pair
      ((restrictedSelectorField_computable.comp Computable.fst
        (Computable.const 1)))
      (Computable.snd.comp
        (coverDecode_primrec.to_comp.comp Computable.snd)))

/-- Search for the least valid cover and return its maximum-intersection member. -/
def restrictedMaxIntersectionCoverSelector
    (𝒜 : DescriptionFamily) : BitString →. BitString := fun input =>
  (Nat.rfind (fun p =>
    Part.some (restrictedSelectorCheck 𝒜 input p))).bind
      (fun p => Part.some (restrictedSelectorPost input p))

/-- Computability of the maximum-intersection selector. -/
theorem restrictedMaxIntersectionCoverSelector_partrec (𝒜 : DescriptionFamily) :
    Partrec (restrictedMaxIntersectionCoverSelector 𝒜) := by
  exact Partrec.bind
    (Partrec.rfind (restrictedSelectorCheck_computable 𝒜).partrec₂)
    restrictedSelectorPost_computable.partrec₂

/-- The selected cover-member code has plain complexity at most that of the
selector input plus a constant depending only on the machine and family. -/
theorem restrictedMaxIntersectionCoverSelector_KPPlain_le
    (U : Map) (hU : IsOptimalPrefixConditional U) (𝒜 : DescriptionFamily) :
    ∃ c : ℕ, ∀ input output : BitString,
      output ∈ restrictedMaxIntersectionCoverSelector 𝒜 input →
      KPPlain U output ≤ KPPlain U input + (c : ENat) := by
  exact KPPlain_partrec_map_le U hU _
    (restrictedMaxIntersectionCoverSelector_partrec 𝒜)

@[simp] lemma restrictedSelectorField_input_zero
    (Acode Ccode : BitString) (c q0 : ℕ) :
    restrictedSelectorField (restrictedCoverSelectorInput Acode Ccode c q0) 0 = Acode := by
  simp only [restrictedSelectorField, restrictedCoverSelectorInput, decodeListCode_listCode,
    List.getD_cons_zero]

@[simp] lemma restrictedSelectorField_input_one
    (Acode Ccode : BitString) (c q0 : ℕ) :
    restrictedSelectorField (restrictedCoverSelectorInput Acode Ccode c q0) 1 = Ccode := by
  simp only [restrictedSelectorField, restrictedCoverSelectorInput, decodeListCode_listCode,
    List.getD_cons_succ, List.getD_cons_zero]

@[simp] lemma restrictedSelectorField_input_two
    (Acode Ccode : BitString) (c q0 : ℕ) :
    bitsToNat (restrictedSelectorField
      (restrictedCoverSelectorInput Acode Ccode c q0) 2) = c := by
  simp only [restrictedSelectorField, restrictedCoverSelectorInput, decodeListCode_listCode,
    List.getD_cons_succ, List.getD_cons_zero, bitsToNat_bits]

@[simp] lemma restrictedSelectorField_input_three
    (Acode Ccode : BitString) (c q0 : ℕ) :
    bitsToNat (restrictedSelectorField
      (restrictedCoverSelectorInput Acode Ccode c q0) 3) = q0 := by
  simp only [restrictedSelectorField, restrictedCoverSelectorInput, decodeListCode_listCode,
    List.getD_cons_succ, List.getD_cons_zero, bitsToNat_bits]

lemma familyEnumeration_prefix_of_le {mem : Finset BitString → Prop}
    (E : FamilyEnumeration mem) {s t : ℕ} (hst : s ≤ t) :
    E.enum s <+: E.enum t := by
  obtain ⟨ k, hk ⟩ := Nat.exists_eq_add_of_le hst;
  subst hk;
  induction k <;>
    simp_all only [add_zero, le_refl, List.prefix_rfl, le_add_iff_nonneg_right,
      zero_le, forall_const]
  exact List.IsPrefix.trans ‹_› ( E.mono _ )

lemma DescriptionFamily.exists_nonempty_cover {𝒜 : DescriptionFamily}
    {A : Finset BitString} (hA : 𝒜.mem A) (n c : ℕ)
    (hc_pos : 0 < c) (hc_le : c ≤ A.card) :
    ∃ cover : List (Finset BitString),
      cover ≠ [] ∧
      (∀ B ∈ cover, 𝒜.mem B ∧ B.card ≤ c) ∧
      (∀ x ∈ A, x.length = n → ∃ B ∈ cover, x ∈ B) ∧
      cover.length * c ≤ 𝒜.overhead n * A.card := by
  obtain ⟨ cover, hcover₁, hcover₂, hcover₃ ⟩ := 𝒜.cover hA n c hc_pos hc_le;
  by_cases h : cover = [] <;>
    simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, false_and,
      exists_const, imp_false, List.length_nil, zero_mul, zero_le, ne_eq,
      not_isEmpty_of_nonempty, IsEmpty.exists_iff, true_and]
  · refine ⟨ [ { [ ] } ], ?_, ?_, ?_ ⟩ <;> norm_num;
    · exact ⟨ DescriptionFamily.singleton_mem 𝒜 _, hc_pos ⟩;
    · nlinarith [ show 0 < 𝒜.overhead n from 𝒜.overhead_pos n ];
  · exact ⟨ cover, h, hcover₁, hcover₂, hcover₃ ⟩

lemma exists_restrictedCoverValidBool_witness (𝒜 : DescriptionFamily)
    (Acode Ccode : BitString) (n c q0 : ℕ)
    (A C : Finset BitString)
    (hAcode : decodeCoverCodeList Acode = canonicalFinsetList A)
    (hCcode : decodeCoverCodeList Ccode = canonicalFinsetList C)
    (hq0 : q0 = 𝒜.overhead n)
    (hA : 𝒜.mem A) (hC : C ⊆ A) (hC_n : ∀ x ∈ C, x.length = n)
    (hc_pos : 0 < c) (hc_le : c ≤ A.card) :
    ∃ p, restrictedCoverValidBool 𝒜 Acode Ccode c q0 p = true := by
  -- Start with a nonempty finite cover of `A` having the required size bound.
  obtain ⟨cover, hcover_nonempty, hcover_mem, hcover_card, hcover_bound⟩ :
      ∃ cover : List (Finset BitString), cover ≠ [] ∧
        (∀ B ∈ cover, 𝒜.mem B ∧ B.card ≤ c) ∧
        (∀ x ∈ A, x.length = n → ∃ B ∈ cover, x ∈ B) ∧
        cover.length * c ≤ q0 * A.card := by
    convert DescriptionFamily.exists_nonempty_cover hA n c hc_pos hc_le
  -- Monotonicity gives one enumeration stage containing a code for every cover member.
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ∀ B ∈ cover, ∃ w,
      w ∈ 𝒜.enumeration.enum s ∧ decodeCoverCodeList w = canonicalFinsetList B := by
    have h_exists_stage : ∀ B ∈ cover, ∃ s : ℕ, ∃ w,
        w ∈ 𝒜.enumeration.enum s ∧
          decodeCoverCodeList w = canonicalFinsetList B := by
      intro B hB
      obtain ⟨s, hs⟩ : ∃ s : ℕ, (codedUniformOn B (by
        exact 𝒜.nonempty_of_mem (hcover_mem B hB |>.1))).code ∈
          𝒜.enumeration.enum s := by
        all_goals generalize_proofs at *
        exact 𝒜.enumeration.complete B (by solve_by_elim) (hcover_mem B hB |>.1) |>
          fun ⟨s, hs⟩ => ⟨s, hs⟩
      generalize_proofs at *
      exact ⟨s, _, hs, decodeCoverCodeList_code _ _⟩
    generalize_proofs at *
    choose! s w hw hw' using h_exists_stage
    generalize_proofs at *
    use Finset.sup cover.toFinset s
    intro B hB
    use w B
    exact ⟨familyEnumeration_prefix_of_le 𝒜.enumeration
        (Finset.le_sup (f := s) (by simpa using hB)) |>
          fun h => h.subset (hw B hB), hw' B hB⟩
  generalize_proofs at *
  choose! f hf₁ hf₂ using hs
  use Encodable.encode (s, cover.map f)
  simp_all only [ne_eq, restrictedCoverValidBool, Encodable.encode_prod_val,
    Encodable.encode_nat, decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, List.all_eq_true, decide_eq_true_eq,
    mem_canonicalFinsetList, List.any_eq_true]
  have h_cover_decode :
      (coverDecode (Nat.pair s (Encodable.encode (List.map f cover)))).2 =
        List.map f cover := by
    simp only [coverDecode, Encodable.decode_prod_val, Nat.unpair_pair,
      Encodable.decode_nat, Encodable.encodek, Option.map_some, Option.bind_some,
      Option.getD_some]
  simp_all only [coverDecode, Encodable.decode_prod_val, Nat.unpair_pair,
    Encodable.decode_nat, Encodable.encodek, Option.map_some, Option.bind_some,
    Option.getD_some, List.map_eq_nil_iff, not_false_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true, and_self,
    List.length_map, true_and, exists_exists_and_eq_and]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  all_goals generalize_proofs at *
  · convert hcover_bound using 1
    rw [← length_canonicalFinsetList A,
      List.dedup_eq_self.mpr (canonicalFinsetList_nodup A)]
    simp
  · intro B hB
    specialize hcover_mem B hB
    simp_all only [canonicalFinsetList]
    rw [List.dedup_eq_self.mpr] <;> norm_num [hcover_mem]
  · exact fun x hx => by
      obtain ⟨B, hB₁, hB₂⟩ := hcover_card x (hC hx) (hC_n x hx)
      exact ⟨B, hB₁, by
        rw [hf₂ B hB₁]
        simpa only [mem_canonicalFinsetList] using hB₂⟩

/-
On genuine canonical codes, and with the supplied numerical bound equal to
the family's overhead at `n`, the selector returns a genuine family member with
the averaging density promised by condition (3).
-/
theorem restrictedMaxIntersectionCoverSelector_spec (𝒜 : DescriptionFamily)
    (Acode Ccode : BitString) (n c q0 : ℕ)
    (A C : Finset BitString)
    (hAcode : decodeCoverCodeList Acode = canonicalFinsetList A)
    (hCcode : decodeCoverCodeList Ccode = canonicalFinsetList C)
    (hq0 : q0 = 𝒜.overhead n)
    (hA : 𝒜.mem A) (hC : C ⊆ A) (hC_n : ∀ x ∈ C, x.length = n)
    (hc_pos : 0 < c) (hc_le : c ≤ A.card) :
    ∃ Bcode B,
      restrictedMaxIntersectionCoverSelector 𝒜
          (restrictedCoverSelectorInput Acode Ccode c q0) = Part.some Bcode ∧
      decodeCoverCodeList Bcode = canonicalFinsetList B ∧
      𝒜.mem B ∧
      B.card ≤ c ∧
      c * C.card ≤ (𝒜.overhead n * A.card) * (B ∩ C).card := by
  obtain ⟨p, hp⟩ : ∃ p,
      restrictedSelectorCheck 𝒜 (restrictedCoverSelectorInput Acode Ccode c q0) p =
        true := by
    obtain ⟨p, hp⟩ := exists_restrictedCoverValidBool_witness 𝒜 Acode Ccode n c q0
      A C hAcode hCcode hq0 hA hC hC_n hc_pos hc_le
    exact ⟨p, by
      simpa only [restrictedSelectorCheck, restrictedSelectorField_input_zero,
        restrictedSelectorField_input_one, restrictedSelectorField_input_two,
        restrictedSelectorField_input_three] using hp⟩
  obtain ⟨p0, hp0⟩ : ∃ p0,
      restrictedMaxIntersectionCoverSelector 𝒜
          (restrictedCoverSelectorInput Acode Ccode c q0) =
        Part.some (restrictedSelectorPost
          (restrictedCoverSelectorInput Acode Ccode c q0) p0) ∧
      restrictedSelectorCheck 𝒜
          (restrictedCoverSelectorInput Acode Ccode c q0) p0 = true := by
    unfold restrictedMaxIntersectionCoverSelector;
    obtain ⟨p0, hp0⟩ : ∃ p0,
        Nat.rfind (fun p => Part.some (restrictedSelectorCheck 𝒜
          (restrictedCoverSelectorInput Acode Ccode c q0) p)) = Part.some p0 := by
      simp +decide only [Nat.rfind]
      simp +decide only [Part.eq_some_iff, Part.mem_mk_iff, Part.mem_some_iff,
        Bool.true_eq, Part.some_dom, implies_true, and_true, ↓existsAndEq, exists_prop]
      use p;
    have hp0_mem : p0 ∈ Nat.rfind (fun p => Part.some (restrictedSelectorCheck 𝒜
        (restrictedCoverSelectorInput Acode Ccode c q0) p)) := Part.eq_some_iff.mp hp0
    have hp0_spec := Nat.mem_rfind.mp hp0_mem
    refine ⟨p0, ?_, Part.mem_some_iff.mp hp0_spec.1 |>.symm⟩
    rw [hp0, Part.bind_some]
  obtain ⟨h_cover, h_card, h_inter⟩ :
      (coverDecode p0).2 ≠ [] ∧
      (∀ w ∈ (coverDecode p0).2,
        w ∈ 𝒜.enumeration.enum (coverDecode p0).1) ∧
      (coverDecode p0).2.length * c ≤ q0 * A.card ∧
      (∀ w ∈ (coverDecode p0).2, (decodeCoverCodeList w).dedup.length ≤ c) ∧
      (∀ x ∈ C, ∃ w ∈ (coverDecode p0).2, x ∈ decodeCoverCodeList w) := by
    have hv := hp0.2
    simp only [restrictedSelectorCheck, restrictedSelectorField_input_zero,
      restrictedSelectorField_input_one, restrictedSelectorField_input_two,
      restrictedSelectorField_input_three, restrictedCoverValidBool,
      Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.any_eq_true] at hv
    rcases hv with ⟨⟨⟨⟨hne, henum⟩, hbound⟩, hcard⟩, hcover⟩
    refine ⟨hne, henum, ?_, hcard, ?_⟩
    · simpa [hAcode, List.dedup_eq_self.mpr (canonicalFinsetList_nodup A),
        length_canonicalFinsetList] using hbound
    · simpa [hCcode, canonicalFinsetList] using hcover
  obtain ⟨Bcode, hBcode⟩ : ∃ Bcode,
      restrictedSelectorPost (restrictedCoverSelectorInput Acode Ccode c q0) p0 = Bcode ∧
      ∃ B, decodeCoverCodeList Bcode = canonicalFinsetList B ∧
        𝒜.mem B ∧ B.card ≤ c := by
    let w := restrictedSelectorPost
      (restrictedCoverSelectorInput Acode Ccode c q0) p0
    have hw : w ∈ (coverDecode p0).2 := coverCodeArgmax_mem h_cover
    obtain ⟨B, _hB_nonempty, hB_mem, hw_code⟩ :=
      𝒜.enumeration.sound (coverDecode p0).1 w (h_card w hw)
    refine ⟨w, rfl, B, ?_, hB_mem, ?_⟩
    · rw [hw_code, decodeCoverCodeList_code]
    · have hw_card := h_inter.2.1 w hw
      rw [hw_code, decodeCoverCodeList_code,
        List.dedup_eq_self.mpr (canonicalFinsetList_nodup B),
        length_canonicalFinsetList] at hw_card
      exact hw_card
  obtain ⟨B, hB⟩ := hBcode.right
  have hargmax : coverCodeArgmax Ccode (coverDecode p0).2 = Bcode := by
    simpa only [restrictedSelectorPost, restrictedSelectorField_input_one] using hBcode.1
  have h_inter_B : C.card ≤
      (coverDecode p0).2.length * ((decodeCoverCodeList Bcode).toFinset ∩ C).card := by
    simpa only [hargmax] using
      coverCodeArgmax_intersection_bound Ccode C hCcode h_inter.2.2
  refine ⟨Bcode, B, ?_, hB.1, hB.2.1, hB.2.2, ?_⟩
  · rw [hp0.1, hBcode.1]
  have h_inter_B' :
      C.card ≤ (coverDecode p0).2.length * (B ∩ C).card := by
    simpa [hB.1, canonicalFinsetList] using h_inter_B
  have h_bound :
      (coverDecode p0).2.length * c ≤ 𝒜.overhead n * A.card := by
    simpa [hq0] using h_inter.1
  calc
    c * C.card ≤ c * ((coverDecode p0).2.length * (B ∩ C).card) :=
      Nat.mul_le_mul_left c h_inter_B'
    _ = ((coverDecode p0).2.length * c) * (B ∩ C).card := by
      ac_rfl
    _ ≤ (𝒜.overhead n * A.card) * (B ∩ C).card :=
      Nat.mul_le_mul_right (B ∩ C).card h_bound

end Kolmogorov
