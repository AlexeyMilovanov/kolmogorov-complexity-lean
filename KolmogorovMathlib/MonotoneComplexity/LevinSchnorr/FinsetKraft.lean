/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.FinsetDeficiency
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Converse
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.FinsetEventLSC

/-!
# SUV Problem 145: Kraft-Chaitin on the filtration of an exhaustion

SUV p. 150, Problem 145.  Work in progress.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ### Deciding `{0, …, n-1} ⊆ F` -/

/-- Boolean membership test for lists of naturals. -/
def memBool (l : List ℕ) (k : ℕ) : Bool := decide (l.idxOf k < l.length)

/-- `memBool` decides list membership. -/
lemma memBool_eq_true_iff {l : List ℕ} {k : ℕ} : memBool l k = true ↔ k ∈ l := by
  simp [memBool, List.idxOf_lt_length_iff]

/-- `memBool` is primitive recursive. -/
lemma primrec_memBool : Primrec fun p : List ℕ × ℕ => memBool p.1 p.2 := by
  have hidx : Primrec fun p : List ℕ × ℕ => p.1.idxOf p.2 :=
    Primrec₂.comp Primrec.list_idxOf Primrec.snd Primrec.fst
  have hlen : Primrec fun p : List ℕ × ℕ => p.1.length := Primrec.list_length.comp Primrec.fst
  have hlt : Primrec₂ fun x y : ℕ => decide (x < y) := PrimrecPred.decide Primrec.nat_lt
  have h : Primrec fun p : List ℕ × ℕ => decide (p.1.idxOf p.2 < p.1.length) :=
    Primrec₂.comp hlt hidx hlen
  exact h.of_eq fun _ => rfl

/-- Boolean test for `{0, …, n-1} ⊆ F`. -/
def rangeSubsetBool (F : Finset ℕ) (n : ℕ) : Bool :=
  (List.range n).foldr (fun k b => memBool (F.sort (· ≤ ·)) k && b) true

/-- `rangeSubsetBool` decides `{0, …, n-1} ⊆ F`. -/
lemma rangeSubsetBool_eq_true_iff {F : Finset ℕ} {n : ℕ} :
    rangeSubsetBool F n = true ↔ ∀ k, k < n → k ∈ F := by
  have hgen : ∀ l : List ℕ,
      (l.foldr (fun k b => memBool (F.sort (· ≤ ·)) k && b) true) = true ↔ ∀ k ∈ l, k ∈ F := by
    intro l
    induction l with
    | nil => simp
    | cons k t ih =>
      simp only [List.foldr_cons, Bool.and_eq_true, ih, List.mem_cons, memBool_eq_true_iff,
        Finset.mem_sort]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases hj with hj | hj
        · exact hj ▸ h1
        · exact h2 j hj
      · intro h
        exact ⟨h k (Or.inl rfl), fun j hj => h j (Or.inr hj)⟩
  rw [rangeSubsetBool, hgen]
  simp [List.mem_range]

/-- `rangeSubsetBool` is primitive recursive. -/
lemma primrec_rangeSubsetBool : Primrec fun p : Finset ℕ × ℕ => rangeSubsetBool p.1 p.2 := by
  have hsort : Primrec fun z : (Finset ℕ × ℕ) × (ℕ × Bool) => z.1.1.sort (· ≤ ·) :=
    primrec_finsetSort.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec fun z : (Finset ℕ × ℕ) × (ℕ × Bool) => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hmem : Primrec fun z : (Finset ℕ × ℕ) × (ℕ × Bool) =>
      memBool (z.1.1.sort (· ≤ ·)) z.2.1 :=
    Primrec₂.comp (primrec_memBool : Primrec₂ memBool) hsort hk
  have hb : Primrec fun z : (Finset ℕ × ℕ) × (ℕ × Bool) => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ fun (p : Finset ℕ × ℕ) (q : ℕ × Bool) =>
      (memBool (p.1.sort (· ≤ ·)) q.1 && q.2) :=
    (Primrec.cond hmem hb (Primrec.const false)).of_eq fun _ => cond_eq_and _ _
  have hrange : Primrec fun p : Finset ℕ × ℕ => List.range p.2 :=
    Primrec.list_range.comp Primrec.snd
  exact (Primrec.list_foldr hrange (Primrec.const true) hstep).of_eq fun _ => rfl

/-! ### Agreement on an initial block -/

/-- Boolean test that `Z` and `x` agree on the first `n` positions. -/
def agreeBool (Z x : BitString) (n : ℕ) : Bool :=
  (List.range n).foldr (fun j b => decide (Z.getD j false = x.getD j false) && b) true

/-- `agreeBool` decides agreement on the first `n` positions. -/
lemma agreeBool_eq_true_iff {Z x : BitString} {n : ℕ} :
    agreeBool Z x n = true ↔ ∀ j, j < n → Z.getD j false = x.getD j false := by
  have hgen : ∀ l : List ℕ,
      (l.foldr (fun j b => decide (Z.getD j false = x.getD j false) && b) true) = true
        ↔ ∀ j ∈ l, Z.getD j false = x.getD j false := by
    intro l
    induction l with
    | nil => simp
    | cons j t ih =>
      simp only [List.foldr_cons, Bool.and_eq_true, ih, List.mem_cons, decide_eq_true_iff]
      constructor
      · rintro ⟨h1, h2⟩ m hm
        rcases hm with hm | hm
        · exact hm ▸ h1
        · exact h2 m hm
      · intro h
        exact ⟨h j (Or.inl rfl), fun m hm => h m (Or.inr hm)⟩
  rw [agreeBool, hgen]
  simp [List.mem_range]

/-- `agreeBool` is primitive recursive. -/
lemma primrec_agreeBool :
    Primrec fun p : (BitString × BitString) × ℕ => agreeBool p.1.1 p.1.2 p.2 := by
  have hZ : Primrec fun z : ((BitString × BitString) × ℕ) × (ℕ × Bool) =>
      z.1.1.1.getD z.2.1 false :=
    (Primrec.list_getD false).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
  have hx : Primrec fun z : ((BitString × BitString) × ℕ) × (ℕ × Bool) =>
      z.1.1.2.getD z.2.1 false :=
    (Primrec.list_getD false).comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
  have heq : Primrec₂ fun u v : Bool => decide (u = v) := PrimrecPred.decide Primrec.eq
  have hd : Primrec fun z : ((BitString × BitString) × ℕ) × (ℕ × Bool) =>
      decide (z.1.1.1.getD z.2.1 false = z.1.1.2.getD z.2.1 false) :=
    Primrec₂.comp heq hZ hx
  have hb : Primrec fun z : ((BitString × BitString) × ℕ) × (ℕ × Bool) => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ fun (p : (BitString × BitString) × ℕ) (q : ℕ × Bool) =>
      (decide (p.1.1.getD q.1 false = p.1.2.getD q.1 false) && q.2) :=
    (Primrec.cond hd hb (Primrec.const false)).of_eq fun _ => cond_eq_and _ _
  have hrange : Primrec fun p : (BitString × BitString) × ℕ => List.range p.2 :=
    Primrec.list_range.comp Primrec.snd
  exact (Primrec.list_foldr hrange (Primrec.const true) hstep).of_eq fun _ => rfl

/-- Agreement on the first `x.length` positions is `Z.take x.length = x` when lengths fit. -/
lemma take_eq_iff_agreeBool {Z x : BitString} (hZ : x.length ≤ Z.length) :
    Z.take x.length = x ↔ agreeBool Z x x.length = true := by
  rw [agreeBool_eq_true_iff]
  constructor
  · intro h j hj
    have hj' : j < (Z.take x.length).length := by
      rw [List.length_take]
      omega
    have hjx : j < x.length := by omega
    have hjZ : j < Z.length := by omega
    rw [List.getD_eq_getElem _ _ hjZ, List.getD_eq_getElem _ _ hjx]
    have := congrArg (fun l => l.getD j false) h
    simp only at this
    rwa [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hjx,
      List.getElem_take] at this
  · intro h
    refine List.ext_getElem (by rw [List.length_take]; omega) fun j hj₁ hj₂ => ?_
    have hjn : j < x.length := by
      rw [List.length_take] at hj₁
      omega
    have hjZ : j < Z.length := by omega
    have hjx : j < x.length := by omega
    have hgd := h j hjn
    rw [List.getD_eq_getElem _ _ hjZ, List.getD_eq_getElem _ _ hjx] at hgd
    rw [List.getElem_take]
    exact hgd

/-! ### The first exhaustion set containing an initial segment -/

section ExhIdx

variable {F : ℕ → Finset ℕ}

open Classical in
/-- SUV p. 150: the least `i` with `{0, …, n-1} ⊆ F i`. -/
noncomputable def exhIdx (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (n : ℕ) : ℕ :=
  Nat.find (exists_forall_lt_mem_of_exhaustion hmono hcover n)

open Classical in
/-- `F (exhIdx n)` contains the initial segment of length `n`. -/
lemma exhIdx_spec (hmono : ∀ i : ℕ, F i ⊆ F (i + 1)) (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i)
    (n : ℕ) : ∀ k, k < n → k ∈ F (exhIdx hmono hcover n) :=
  Nat.find_spec (exists_forall_lt_mem_of_exhaustion hmono hcover n)

open Classical in
/-- Minimality of `exhIdx`. -/
lemma exhIdx_min (hmono : ∀ i : ℕ, F i ⊆ F (i + 1)) (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i)
    {n i : ℕ} (hi : i < exhIdx hmono hcover n) : ¬ ∀ k, k < n → k ∈ F i :=
  Nat.find_min _ hi

/-- The search function used to compute `exhIdx` by an unbounded search. -/
def exhSearch (F : ℕ → Finset ℕ) (n i : ℕ) : Option ℕ :=
  bif rangeSubsetBool (F i) n then some i else none

/-- The search function is computable. -/
lemma computable₂_exhSearch (hF : Computable F) : Computable₂ (exhSearch F) := by
  have hrs : Computable₂ rangeSubsetBool := primrec_rangeSubsetBool.to_comp
  have hcond : Computable fun p : ℕ × ℕ => rangeSubsetBool (F p.2) p.1 :=
    Computable₂.comp hrs (hF.comp Computable.snd) Computable.fst
  exact Computable.cond hcond (Computable.option_some.comp Computable.snd)
    (Computable.const none)

/-- `exhIdx` is computable. -/
lemma computable_exhIdx (hF : Computable F) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) : Computable (exhIdx hmono hcover) := by
  classical
  refine Partrec.of_eq_tot (Partrec.rfindOpt (computable₂_exhSearch hF)) fun n => ?_
  have hsome : exhSearch F n (exhIdx hmono hcover n) = some (exhIdx hmono hcover n) := by
    have h1 : rangeSubsetBool (F (exhIdx hmono hcover n)) n = true :=
      rangeSubsetBool_eq_true_iff.2 (exhIdx_spec hmono hcover n)
    simp [exhSearch, h1]
  rw [Nat.rfindOpt]
  refine Part.mem_bind_iff.mpr ⟨exhIdx hmono hcover n, ?_, ?_⟩
  · rw [Nat.mem_rfind]
    have hnone : ∀ i : ℕ, i < exhIdx hmono hcover n → exhSearch F n i = none := by
      intro i hi
      have hnot := exhIdx_min hmono hcover hi
      have h2 : rangeSubsetBool (F i) n = false := by
        by_contra hcon
        exact hnot (rangeSubsetBool_eq_true_iff.1 (by simpa using hcon))
      simp [exhSearch, h2]
    refine ⟨by simp [hsome], fun {m} hm => ?_⟩
    simp [hnone m hm]
  · simp [hsome]

end ExhIdx

/-! ### The strings compatible with a covering interval -/

/-- The cardinality of a finite set of naturals is primitive recursive. -/
lemma primrec_finsetCard : Primrec fun F : Finset ℕ => F.card :=
  (Primrec.list_length.comp primrec_finsetSort).of_eq fun _ => Finset.length_sort (· ≤ ·)

/-- The strings of length `Fi.card` that agree with `x` on the first `|x|` positions. -/
def compatList (Fi : Finset ℕ) (x : BitString) : List BitString :=
  (levelList Fi.card).flatMap fun Z => cond (agreeBool Z x x.length) [Z] []

/-- Membership in `compatList`. -/
lemma mem_compatList {Fi : Finset ℕ} {x Z : BitString} :
    Z ∈ compatList Fi x ↔ Z.length = Fi.card ∧ agreeBool Z x x.length = true := by
  rw [compatList, List.mem_flatMap]
  constructor
  · rintro ⟨Z', hZ', hmem⟩
    cases hcase : agreeBool Z' x x.length with
    | false => rw [hcase] at hmem; simp at hmem
    | true =>
      rw [hcase] at hmem
      simp only [cond_true, List.mem_singleton] at hmem
      subst hmem
      exact ⟨mem_levelList.1 hZ', hcase⟩
  · rintro ⟨hlen, hag⟩
    exact ⟨Z, mem_levelList.2 hlen, by simp [hag]⟩

/-- `compatList` has no duplicates. -/
lemma nodup_compatList (Fi : Finset ℕ) (x : BitString) : (compatList Fi x).Nodup := by
  refine List.Nodup.sublist ?_ (nodup_levelList Fi.card)
  rw [compatList]
  refine List.Sublist.trans ?_ (List.Sublist.refl _)
  induction levelList Fi.card with
  | nil => simp
  | cons Z t ih =>
    simp only [List.flatMap_cons]
    cases hcase : agreeBool Z x x.length
    · simpa [hcase] using ih.trans (List.sublist_cons_self Z t)
    · simpa [hcase] using List.Sublist.cons₂ Z ih

/-- `compatList` is primitive recursive. -/
lemma primrec_compatList : Primrec fun p : Finset ℕ × BitString => compatList p.1 p.2 := by
  have hlevel : Primrec fun p : Finset ℕ × BitString => levelList p.1.card :=
    primrec_levelList.comp (primrec_finsetCard.comp Primrec.fst)
  have hargs : Primrec fun q : (Finset ℕ × BitString) × BitString =>
      (((q.2, q.1.2) : BitString × BitString), q.1.2.length) :=
    Primrec.pair (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
  have hag : Primrec fun q : (Finset ℕ × BitString) × BitString =>
      agreeBool q.2 q.1.2 q.1.2.length := primrec_agreeBool.comp hargs
  have hsing : Primrec fun q : (Finset ℕ × BitString) × BitString => ([q.2] : List BitString) :=
    Primrec.list_cons.comp Primrec.snd (Primrec.const [])
  have hinner : Primrec₂ fun (p : Finset ℕ × BitString) (Z : BitString) =>
      cond (agreeBool Z p.2 p.2.length) [Z] ([] : List BitString) :=
    Primrec.cond hag hsing (Primrec.const [])
  exact (Primrec.list_flatMap hlevel hinner).of_eq fun _ => rfl

/-! ### Finite sums over a list, as `tsum`s -/

/-- Summing over the entries of a list, indexed by `ℕ` with `0` outside the range. -/
lemma sum_range_getElem?_elim {α : Type*} (l : List α) (h : α → ℝ≥0∞) :
    ∑ k ∈ Finset.range l.length, ((l[k]?).elim 0 h) = (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.elim_some, ih,
      List.map_cons, List.sum_cons]
    exact add_comm _ _

/-- The `tsum` over `ℕ` of a list-indexed family is the list sum. -/
lemma tsum_getElem?_elim {α : Type*} (l : List α) (h : α → ℝ≥0∞) :
    ∑' k : ℕ, ((l[k]?).elim 0 h) = (l.map h).sum := by
  rw [tsum_eq_sum (s := Finset.range l.length) ?_, sum_range_getElem?_elim]
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  rw [List.getElem?_eq_none hk]
  rfl

/-! ### The events compatible with a covering interval -/

/-- SUV p. 150: the events `v(F) = Z` for `Z` compatible with `x` are disjoint subsets of the
cylinder `Ω_x`, so their masses add up to at most `μ(Ω_x)`. -/
lemma sum_finsetEventMass_compatList_le (μ : Measure CantorSeq) {Fi : Finset ℕ} {x : BitString}
    (hF : ∀ k, k < x.length → k ∈ Fi) :
    ((compatList Fi x).map fun Z => finsetEventMass μ Fi Z).sum ≤ cantorMass μ x := by
  classical
  have hcard : x.length ≤ Fi.card := by
    have hsub : Finset.range x.length ⊆ Fi := fun k hk => hF k (Finset.mem_range.1 hk)
    have h := Finset.card_le_card hsub
    rwa [Finset.card_range] at h
  have hsum : ((compatList Fi x).map fun Z => finsetEventMass μ Fi Z).sum
      = ∑ Z ∈ (compatList Fi x).toFinset, finsetEventMass μ Fi Z :=
    (List.sum_toFinset _ (nodup_compatList Fi x)).symm
  have hdisj : (((compatList Fi x).toFinset : Finset BitString) :
      Set BitString).PairwiseDisjoint fun Z => {v : CantorSeq | restrictSeq Fi v = Z} := by
    intro Z _ Z' _ hne
    refine Set.disjoint_left.mpr fun v hv hv' => ?_
    exact hne (hv.symm.trans hv')
  have hmeas := measure_biUnion_finset (μ := μ) hdisj
    (fun Z _ => measurableSet_setOf_restrictSeq Fi Z)
  rw [hsum, show (∑ Z ∈ (compatList Fi x).toFinset, finsetEventMass μ Fi Z)
      = ∑ Z ∈ (compatList Fi x).toFinset, μ {v : CantorSeq | restrictSeq Fi v = Z} from rfl,
    ← hmeas, cantorMass]
  refine measure_mono fun v hv => ?_
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, List.mem_toFinset] at hv
  obtain ⟨Z, hZmem, hvZ⟩ := hv
  obtain ⟨hlen, hag⟩ := mem_compatList.1 hZmem
  have htake : Z.take x.length = x := (take_eq_iff_agreeBool (by omega)).2 hag
  have hpref : cantorPrefix v x.length = x := by
    rw [← restrictSeq_take Fi hF v, hvZ, htake]
  exact (isCantorPrefix_iff_cantorPrefix_eq x v).2 hpref

/-! ### The Kraft-Chaitin request on pairs -/

variable {F : ℕ → Finset ℕ}

/-- The pair `(F i, Z)` charged by the slot `(c, j, k)`: `j` selects an interval `Ω_x` of the
disjointified level `2c + 2`, `i` is the least index with `{0, …, |x|-1} ⊆ F i`, and `k`
selects one of the strings of length `|F i|` compatible with `x`. -/
noncomputable def kraftPair (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (g : ℕ → ℕ → Option BitString) (c j k : ℕ) :
    Option (Finset ℕ × BitString) :=
  (disjEnum (g (2 * c + 2)) j).bind fun x =>
    ((compatList (F (exhIdx hmono hcover x.length)) x)[k]?).map
      fun Z => (F (exhIdx hmono hcover x.length), Z)

/-- The `μ`-mass charged by the slot `(c, j, k)`. -/
noncomputable def kraftMass (μ : Measure CantorSeq) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (g : ℕ → ℕ → Option BitString) (c j k : ℕ) : ℝ≥0∞ :=
  (kraftPair hmono hcover g c j k).elim 0 fun p => finsetEventMass μ p.1 p.2

/-- The request placed at the output string `y` by the slot `(c, j, k)`. -/
noncomputable def kraftTerm (μ : Measure CantorSeq) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (g : ℕ → ℕ → Option BitString) (c j k : ℕ)
    (y : BitString) : ℝ≥0∞ :=
  (kraftPair hmono hcover g c j k).elim 0
    fun p => if pairCode (finsetCode p.1) p.2 = y then finsetEventMass μ p.1 p.2 else 0

/-- The total Kraft-Chaitin request weight at the output string `y`. -/
noncomputable def kraftWeight (μ : Measure CantorSeq) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (g : ℕ → ℕ → Option BitString) (y : BitString)
    (_ctx : BitString) : ℝ≥0∞ :=
  ∑' n : ℕ, ((2 ^ (Nat.unpair n).1 : ℕ) : ℝ≥0∞) *
    kraftTerm μ hmono hcover g (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1
      (Nat.unpair (Nat.unpair n).2).2 y

/-- Summing the request over all output strings collapses the inner `if`. -/
lemma tsum_kraftTerm (μ : Measure CantorSeq) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (g : ℕ → ℕ → Option BitString) (c j k : ℕ) :
    (∑' y : BitString, kraftTerm μ hmono hcover g c j k y) = kraftMass μ hmono hcover g c j k := by
  classical
  simp only [kraftTerm, kraftMass]
  cases hp : kraftPair hmono hcover g c j k with
  | none => simp
  | some p =>
    simp only [Option.elim_some]
    rw [tsum_eq_single (pairCode (finsetCode p.1) p.2) ?_]
    · simp
    · intro y hy
      simp [Ne.symm hy]

/-- The slots of a fixed interval charge at most the mass of that interval. -/
lemma tsum_kraftMass_le (μ : Measure CantorSeq) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (g : ℕ → ℕ → Option BitString) (c j : ℕ) :
    (∑' k : ℕ, kraftMass μ hmono hcover g c j k)
      ≤ (disjEnum (g (2 * c + 2)) j).elim 0 (cantorMass μ) := by
  classical
  cases hx : disjEnum (g (2 * c + 2)) j with
  | none => simp [kraftMass, kraftPair, hx]
  | some x =>
    have hkey : ∀ k : ℕ, kraftMass μ hmono hcover g c j k
        = (((compatList (F (exhIdx hmono hcover x.length)) x)[k]?).elim 0
            fun Z => finsetEventMass μ (F (exhIdx hmono hcover x.length)) Z) := by
      intro k
      rw [kraftMass, kraftPair, hx]
      cases hz : (compatList (F (exhIdx hmono hcover x.length)) x)[k]? <;> simp [hz]
    simp only [hkey, Option.elim_some]
    rw [tsum_getElem?_elim]
    exact sum_finsetEventMass_compatList_le μ (exhIdx_spec hmono hcover x.length)

/-- The request weight as an iterated sum over the slot indices `(c, j, k)`. -/
lemma kraftWeight_eq_tsum (μ : Measure CantorSeq) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (g : ℕ → ℕ → Option BitString) (y ctx : BitString) :
    kraftWeight μ hmono hcover g y ctx
      = ∑' (c : ℕ) (j : ℕ) (k : ℕ),
          (2 : ℝ≥0∞) ^ c * kraftTerm μ hmono hcover g c j k y := by
  have h1 : kraftWeight μ hmono hcover g y ctx
      = ∑' p : ℕ × ℕ, ((2 ^ p.1 : ℕ) : ℝ≥0∞) *
          kraftTerm μ hmono hcover g p.1 (Nat.unpair p.2).1 (Nat.unpair p.2).2 y := by
    rw [kraftWeight]
    exact tsum_unpair fun p : ℕ × ℕ => ((2 ^ p.1 : ℕ) : ℝ≥0∞) *
      kraftTerm μ hmono hcover g p.1 (Nat.unpair p.2).1 (Nat.unpair p.2).2 y
  have h2 : (∑' p : ℕ × ℕ, ((2 ^ p.1 : ℕ) : ℝ≥0∞) *
        kraftTerm μ hmono hcover g p.1 (Nat.unpair p.2).1 (Nat.unpair p.2).2 y)
      = ∑' (c : ℕ) (m : ℕ), ((2 ^ c : ℕ) : ℝ≥0∞) *
        kraftTerm μ hmono hcover g c (Nat.unpair m).1 (Nat.unpair m).2 y :=
    ENNReal.tsum_prod (f := fun c m => ((2 ^ c : ℕ) : ℝ≥0∞) *
      kraftTerm μ hmono hcover g c (Nat.unpair m).1 (Nat.unpair m).2 y)
  rw [h1, h2]
  refine tsum_congr fun c => ?_
  have h3 : (∑' m : ℕ, ((2 ^ c : ℕ) : ℝ≥0∞) *
        kraftTerm μ hmono hcover g c (Nat.unpair m).1 (Nat.unpair m).2 y)
      = ∑' q : ℕ × ℕ, ((2 ^ c : ℕ) : ℝ≥0∞) * kraftTerm μ hmono hcover g c q.1 q.2 y :=
    tsum_unpair fun q : ℕ × ℕ =>
      ((2 ^ c : ℕ) : ℝ≥0∞) * kraftTerm μ hmono hcover g c q.1 q.2 y
  have h4 : (∑' q : ℕ × ℕ, ((2 ^ c : ℕ) : ℝ≥0∞) * kraftTerm μ hmono hcover g c q.1 q.2 y)
      = ∑' (j : ℕ) (k : ℕ), ((2 ^ c : ℕ) : ℝ≥0∞) * kraftTerm μ hmono hcover g c j k y :=
    ENNReal.tsum_prod (f := fun j k =>
      ((2 ^ c : ℕ) : ℝ≥0∞) * kraftTerm μ hmono hcover g c j k y)
  rw [h3, h4]
  refine tsum_congr fun j => tsum_congr fun k => ?_
  push_cast
  ring

/-- A single slot already contributes its full request. -/
lemma le_kraftWeight (μ : Measure CantorSeq) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (g : ℕ → ℕ → Option BitString) {c j k : ℕ}
    {Fi : Finset ℕ} {Z : BitString} (hp : kraftPair hmono hcover g c j k = some (Fi, Z))
    (ctx : BitString) :
    (2 : ℝ≥0∞) ^ c * finsetEventMass μ Fi Z
      ≤ kraftWeight μ hmono hcover g (pairCode (finsetCode Fi) Z) ctx := by
  rw [kraftWeight]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (Nat.pair c (Nat.pair j k)))
  rw [Nat.unpair_pair, Nat.unpair_pair]
  have hval : kraftTerm μ hmono hcover g c j k (pairCode (finsetCode Fi) Z)
      = finsetEventMass μ Fi Z := by simp [kraftTerm, hp]
  rw [hval]
  push_cast
  ring

/-- SUV p. 150: the total Kraft-Chaitin request weight of the pair filtration is at most `1`. -/
theorem tsum_kraftWeight_le_one (μ : Measure CantorSeq) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) {g : ℕ → ℕ → Option BitString}
    (hsmall : ∀ n, μ (⋃ i, coverSet (g n) i) ≤ (2 : ℝ≥0∞)⁻¹ ^ n) (ctx : BitString) :
    (∑' y : BitString, kraftWeight μ hmono hcover g y ctx) ≤ 1 := by
  have hstep1 : (∑' y : BitString, kraftWeight μ hmono hcover g y ctx)
      = ∑' (c : ℕ) (j : ℕ) (k : ℕ), (2 : ℝ≥0∞) ^ c * kraftMass μ hmono hcover g c j k := by
    simp only [kraftWeight_eq_tsum]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun c => ?_
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun j => ?_
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun k => ?_
    rw [ENNReal.tsum_mul_left, tsum_kraftTerm]
  rw [hstep1]
  have hlevel : ∀ c : ℕ,
      (∑' (j : ℕ) (k : ℕ), (2 : ℝ≥0∞) ^ c * kraftMass μ hmono hcover g c j k)
        ≤ (2 : ℝ≥0∞)⁻¹ ^ (c + 2) := by
    intro c
    have hj : ∀ j : ℕ, (∑' k : ℕ, (2 : ℝ≥0∞) ^ c * kraftMass μ hmono hcover g c j k)
        ≤ (2 : ℝ≥0∞) ^ c * (disjEnum (g (2 * c + 2)) j).elim 0 (cantorMass μ) := by
      intro j
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul' le_rfl (tsum_kraftMass_le μ hmono hcover g c j)
    refine le_trans (ENNReal.tsum_le_tsum hj) ?_
    rw [ENNReal.tsum_mul_left, tsum_measure_disjEnum]
    refine le_trans (mul_le_mul' le_rfl (hsmall (2 * c + 2))) (le_of_eq ?_)
    have hcancel : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ c = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    calc (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ (2 * c + 2)
        = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c * (2 : ℝ≥0∞)⁻¹ ^ (c + 2)) := by
          rw [← pow_add]
          congr 2
          omega
      _ = (2 : ℝ≥0∞)⁻¹ ^ (c + 2) := by rw [← mul_assoc, hcancel, one_mul]
  refine le_trans (ENNReal.tsum_le_tsum hlevel) ?_
  have hgeo : (∑' c : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (c + 2))
      = (2 : ℝ≥0∞)⁻¹ ^ 2 * ∑' c : ℕ, (2 : ℝ≥0∞)⁻¹ ^ c := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun c => by rw [← pow_add, Nat.add_comm]
  rw [hgeo, ENNReal.tsum_geometric]
  have hone : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.sub_eq_of_eq_add (by norm_num) ?_]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [hone, inv_inv, pow_two, mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  exact ENNReal.inv_le_one.2 one_le_two

/-! ### Lower semicomputability of the request -/

/-- The inner selection step of `kraftPair`: the `k`-th string of the exhaustion level of `x`
compatible with `x`, paired with that level. -/
noncomputable def kraftInner (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (k : ℕ) (x : BitString) :
    Option (Finset ℕ × BitString) :=
  ((compatList (F (exhIdx hmono hcover x.length)) x)[k]?).map
    fun Z => (F (exhIdx hmono hcover x.length), Z)

/-- `kraftPair` is the bind of the interval enumeration with `kraftInner`. -/
lemma kraftPair_eq_bind (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) (g : ℕ → ℕ → Option BitString) (c j k : ℕ) :
    kraftPair hmono hcover g c j k
      = (disjEnum (g (2 * c + 2)) j).bind (kraftInner hmono hcover k) := rfl

/-- `kraftInner` is computable. -/
lemma computable_kraftInner (hF : Computable F) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) :
    Computable₂ (kraftInner hmono hcover) := by
  have hidx : Computable fun q : ℕ × BitString => exhIdx hmono hcover q.2.length :=
    (computable_exhIdx hF hmono hcover).comp (Computable.list_length.comp Computable.snd)
  have hFi : Computable fun q : ℕ × BitString => F (exhIdx hmono hcover q.2.length) :=
    hF.comp hidx
  have hcl : Computable fun q : ℕ × BitString =>
      compatList (F (exhIdx hmono hcover q.2.length)) q.2 :=
    Computable₂.comp (primrec_compatList.to_comp : Computable₂ compatList) hFi Computable.snd
  have hget : Computable fun q : ℕ × BitString =>
      (compatList (F (exhIdx hmono hcover q.2.length)) q.2)[q.1]? :=
    Computable₂.comp (Primrec₂.to_comp Primrec.list_getElem? :
      Computable₂ fun (l : List BitString) (n : ℕ) => l[n]?) hcl Computable.fst
  have hmk : Computable₂ fun (q : ℕ × BitString) (Z : BitString) =>
      ((F (exhIdx hmono hcover q.2.length), Z) : Finset ℕ × BitString) :=
    Computable.pair (hFi.comp Computable.fst) Computable.snd
  exact Computable.option_map hget hmk

/-- The pair selected by the `n`-th slot, as a computable function of `n`. -/
lemma computable_kraftPair (hF : Computable F) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g) :
    Computable fun n : ℕ => kraftPair hmono hcover g (Nat.unpair n).1
      (Nat.unpair (Nat.unpair n).2).1 (Nat.unpair (Nat.unpair n).2).2 := by
  have hlevel : Computable fun n : ℕ => 2 * (Nat.unpair n).1 + 2 :=
    Primrec.to_comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.unpair))
      (Primrec.const 2))
  have hj : Computable fun n : ℕ => (Nat.unpair (Nat.unpair n).2).1 :=
    Primrec.to_comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hk : Computable fun n : ℕ => (Nat.unpair (Nat.unpair n).2).2 :=
    Primrec.to_comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hdisj : Computable fun n : ℕ =>
      disjEnum (g (2 * (Nat.unpair n).1 + 2)) (Nat.unpair (Nat.unpair n).2).1 :=
    (computable_disjEnum hg).comp hlevel hj
  have hinner : Computable₂ fun (n : ℕ) (x : BitString) =>
      kraftInner hmono hcover (Nat.unpair (Nat.unpair n).2).2 x :=
    Computable₂.comp (computable_kraftInner hF hmono hcover) (hk.comp Computable.fst)
      Computable.snd
  exact Computable.option_bind hdisj hinner

/-- The stage-`s` approximation `A₀ s Fi Z`, guarded by the request `y`: it is `A₀ s Fi Z` when
`pairCode (finsetCode Fi) Z = y`, and `0` at every pair that does not code `y`. -/
def kraftApproxAt (A₀ : ℕ → Finset ℕ → BitString → ℕ) (s : ℕ) (y : BitString)
    (Fi : Finset ℕ) (Z : BitString) : ℕ :=
  if pairCode (finsetCode Fi) Z = y then A₀ s Fi Z else 0

/-- `kraftApproxAt` written with `Bool.cond`. -/
lemma kraftApproxAt_eq_cond (A₀ : ℕ → Finset ℕ → BitString → ℕ) (s : ℕ) (y : BitString)
    (Fi : Finset ℕ) (Z : BitString) :
    kraftApproxAt A₀ s y Fi Z =
      cond (decide (pairCode (finsetCode Fi) Z = y)) (A₀ s Fi Z) 0 := by
  by_cases h : pairCode (finsetCode Fi) Z = y <;> simp [kraftApproxAt, h]

/-- The output code of a requested pair is computable. -/
lemma computable_kraftCode {α : Type} [Primcodable α] {G : α → Finset ℕ} {Zf : α → BitString}
    (hG : Computable G) (hZ : Computable Zf) :
    Computable fun a : α => pairCode (finsetCode (G a)) (Zf a) :=
  Computable₂.comp (pairCode_computable : Computable₂ pairCode)
    (computable_finsetCode.comp hG) hZ

/-- Deciding equality of two computable bit strings, in any parameters. -/
lemma computable_bitStringEq {α : Type} [Primcodable α] {C Y : α → BitString}
    (hC : Computable C) (hY : Computable Y) :
    Computable fun a : α => decide (C a = Y a) := by
  have heq : Computable₂ fun u v : BitString => decide (u = v) :=
    Primrec₂.to_comp
      (PrimrecPred.decide Primrec.eq : Primrec₂ fun u v : BitString => decide (u = v))
  exact Computable₂.comp heq hC hY

/-- The match test of the request is computable. -/
lemma computable_kraftMatch {α : Type} [Primcodable α] {G : α → Finset ℕ}
    {Zf Y : α → BitString} (hG : Computable G) (hZ : Computable Zf) (hY : Computable Y) :
    Computable fun a : α => decide (pairCode (finsetCode (G a)) (Zf a) = Y a) :=
  computable_bitStringEq (computable_kraftCode hG hZ) hY

/-- `kraftApproxAt` is computable, with the ambient type kept abstract. -/
lemma computable_kraftApproxAt {α : Type} [Primcodable α] {A₀ : ℕ → Finset ℕ → BitString → ℕ}
    (hA₀ : Computable fun q : ℕ × Finset ℕ × BitString => A₀ q.1 q.2.1 q.2.2)
    {S : α → ℕ} {Y : α → BitString} {G : α → Finset ℕ} {Zf : α → BitString}
    (hS : Computable S) (hY : Computable Y) (hG : Computable G) (hZ : Computable Zf) :
    Computable fun a : α => kraftApproxAt A₀ (S a) (Y a) (G a) (Zf a) := by
  have hval : Computable fun a : α => A₀ (S a) (G a) (Zf a) :=
    hA₀.comp (Computable.pair hS (Computable.pair hG hZ))
  exact (Computable.cond (computable_kraftMatch hG hZ hY) hval (Computable.const 0)).of_eq
    fun a => (kraftApproxAt_eq_cond A₀ (S a) (Y a) (G a) (Zf a)).symm

/-- The stage-`s` approximation of the `n`-th request term. -/
noncomputable def kraftApprox (A₀ : ℕ → Finset ℕ → BitString → ℕ)
    (hmono : ∀ i : ℕ, F i ⊆ F (i + 1)) (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i)
    (g : ℕ → ℕ → Option BitString) (n s : ℕ) (y : BitString) : ℕ :=
  ((kraftPair hmono hcover g (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1
      (Nat.unpair (Nat.unpair n).2).2).map fun p => kraftApproxAt A₀ s y p.1 p.2).getD 0

/-- SUV p. 150: the Kraft-Chaitin request of the pair filtration is lower semicomputable. -/
theorem isLSC_kraftWeight {μ : Measure CantorSeq} (hμ : IsComputableMeasure μ)
    (hF : Computable F) (hmono : ∀ i : ℕ, F i ⊆ F (i + 1))
    (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g) :
    IsLSC (kraftWeight μ hmono hcover g) := by
  obtain ⟨A₀, hA₀comp, hA₀mono, hA₀sup⟩ := exists_uniform_lsc_finsetEventMass hμ
  have hwt : Computable fun n : ℕ => 2 ^ (Nat.unpair n).1 :=
    Primrec.to_comp (primrec_two_pow_aux.comp (Primrec.fst.comp Primrec.unpair))
  refine isLSC_tsum_nsmul_of_uniform (wt := fun n : ℕ => 2 ^ (Nat.unpair n).1)
    (b := fun n y => kraftTerm μ hmono hcover g (Nat.unpair n).1
      (Nat.unpair (Nat.unpair n).2).1 (Nat.unpair (Nat.unpair n).2).2 y)
    (A := fun n s y => kraftApprox A₀ hmono hcover g n s y) hwt ?_ ?_ ?_
  · intro n s y
    simp only [kraftApprox]
    cases hp : kraftPair hmono hcover g (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1
        (Nat.unpair (Nat.unpair n).2).2 with
    | none => simp [dyadicValue]
    | some p =>
      simp only [Option.map_some, Option.getD_some, kraftApproxAt]
      by_cases hm : pairCode (finsetCode p.1) p.2 = y
      · simp only [if_pos hm]
        exact hA₀mono s p.1 p.2
      · simp [hm, dyadicValue]
  · intro n y
    simp only [kraftApprox, kraftTerm]
    cases hp : kraftPair hmono hcover g (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1
        (Nat.unpair (Nat.unpair n).2).2 with
    | none => simp [dyadicValue]
    | some p =>
      simp only [Option.map_some, Option.getD_some, Option.elim_some, kraftApproxAt]
      by_cases hm : pairCode (finsetCode p.1) p.2 = y
      · simp only [if_pos hm]
        exact hA₀sup p.1 p.2
      · simp [hm, dyadicValue]
  · have hKP : Computable fun q : ℕ × ℕ × BitString =>
        kraftPair hmono hcover g (Nat.unpair q.1).1 (Nat.unpair (Nat.unpair q.1).2).1
          (Nat.unpair (Nat.unpair q.1).2).2 :=
      (computable_kraftPair hF hmono hcover hg).comp Computable.fst
    have hinner : Computable₂ fun (q : ℕ × ℕ × BitString) (p : Finset ℕ × BitString) =>
        kraftApproxAt A₀ q.2.1 q.2.2 p.1 p.2 :=
      computable_kraftApproxAt hA₀comp
        (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.snd.comp (Computable.snd.comp Computable.fst))
        (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)
    exact Computable.option_getD (Computable.option_map hKP hinner) (Computable.const 0)

/-! ### The prefix-complexity bound on the requested pairs -/

/-- SUV p. 150: Kraft-Chaitin turns the request into a prefix-free decompressor, and optimality
of `U` transfers the bound to `K`: every requested pair `(F i, Z)` of level `2c + 2` satisfies
`K(F i, Z) ≤ -log p_{F i, Z} - c + c₀`. -/
theorem exists_const_kraft_bound {μ : Measure CantorSeq} (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) (hF : Computable F)
    (hmono : ∀ i : ℕ, F i ⊆ F (i + 1)) (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i)
    {g : ℕ → ℕ → Option BitString} (hg : Computable₂ g)
    (hsmall : ∀ n, μ (⋃ i, coverSet (g n) i) ≤ (2 : ℝ≥0∞)⁻¹ ^ n) :
    ∃ c₀ : ℕ, ∀ (c j k : ℕ) (Fi : Finset ℕ) (Z : BitString),
      kraftPair hmono hcover g c j k = some (Fi, Z) →
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * ((2 : ℝ≥0∞) ^ c * finsetEventMass μ Fi Z)
        ≤ complexityWeight (KPPair U (finsetCode Fi) Z) := by
  obtain ⟨M', hM', c₁, hc₁⟩ := kraftChaitin_realization_bound_unit
    (isLSC_kraftWeight hμ hF hmono hcover hg)
    (fun ctx => tsum_kraftWeight_le_one μ hmono hcover hsmall ctx)
  obtain ⟨c₂, hc₂⟩ := hU.invariance hM'
  refine ⟨c₁ + c₂, fun c j k Fi Z hp => ?_⟩
  have hstep : complexityWeight (KP M' (pairCode (finsetCode Fi) Z) [])
        * (2 : ℝ≥0∞)⁻¹ ^ c₂
      ≤ complexityWeight (KPPair U (finsetCode Fi) Z) := by
    rw [← complexityWeight_add_nat]
    exact complexityWeight_le_of_le (hc₂ (pairCode (finsetCode Fi) Z) [])
  calc (2 : ℝ≥0∞)⁻¹ ^ (c₁ + c₂) * ((2 : ℝ≥0∞) ^ c * finsetEventMass μ Fi Z)
      = ((2 : ℝ≥0∞)⁻¹ ^ c₁ * ((2 : ℝ≥0∞) ^ c * finsetEventMass μ Fi Z))
          * (2 : ℝ≥0∞)⁻¹ ^ c₂ := by
        rw [pow_add]; ring
    _ ≤ ((2 : ℝ≥0∞)⁻¹ ^ c₁ * kraftWeight μ hmono hcover g (pairCode (finsetCode Fi) Z) [])
          * (2 : ℝ≥0∞)⁻¹ ^ c₂ := by
        gcongr
        exact le_kraftWeight μ hmono hcover g hp []
    _ ≤ complexityWeight (KP M' (pairCode (finsetCode Fi) Z) []) * (2 : ℝ≥0∞)⁻¹ ^ c₂ := by
        gcongr
        exact hc₁ (pairCode (finsetCode Fi) Z) []
    _ ≤ complexityWeight (KPPair U (finsetCode Fi) Z) := hstep

/-! ### Problem 145 -/

/-- **SUV Problem 145** (Section 5.6, p. 150): let `F 0 ⊆ F 1 ⊆ …` be a computable sequence of
finite sets with `⋃ᵢ F i = ℕ`.  If `K(F i, w(F i)) ≥ -log p_{F i, w(F i)} - c` for some `c` and
all `i`, then `w` is Martin-Löf random with respect to `μ`. -/
theorem problem_145_isMartinLofRandom_of_computable_exhaustion' {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) (hF : Computable F)
    (hmono : ∀ i : ℕ, F i ⊆ F (i + 1)) (hcover : ∀ k : ℕ, ∃ i : ℕ, k ∈ F i) {w : CantorSeq}
    (hw : ∃ c : ℕ, ∀ i : ℕ,
      complexityWeight (KPPair U (finsetCode (F i)) (restrictSeq (F i) w))
        ≤ (2 : ℝ≥0∞) ^ c * finsetEventMass μ (F i) (restrictSeq (F i) w)) :
    IsMartinLofRandom μ w := by
  classical
  by_contra hcon
  obtain ⟨cw, hcw⟩ := hw
  obtain ⟨V, hV⟩ := exists_universal_martinLof_test hμ
  have hmemV : w ∈ ⋂ n, V n := (not_isMartinLofRandom_iff_mem_universal_test hV w).1 hcon
  obtain ⟨g, hg, hgV⟩ := hV.1.1
  have hsmall : ∀ n, μ (⋃ i, coverSet (g n) i) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    have hb := hV.1.2 n
    rw [dyadicValue_one_eq_inv_two_pow'] at hb
    rw [show (⋃ i, coverSet (g n) i) = V n from (hgV n).symm]
    exact hb
  obtain ⟨c₀, hc₀⟩ := exists_const_kraft_bound hμ hU hF hmono hcover hg hsmall
  obtain ⟨cK, hcK⟩ := KPPlain_le_two_mul_length U hU
  set C : ℕ := cw + c₀ + 1 with hC
  have hwV : w ∈ V (2 * C + 2) := Set.mem_iInter.1 hmemV _
  have hveq : V (2 * C + 2) = ⋃ j, coverSet (g (2 * C + 2)) j := hgV (2 * C + 2)
  have hcover' : w ∈ ⋃ i, coverSet (disjEnum (g (2 * C + 2))) i := by
    rw [coverSet_disjEnum_iUnion, ← hveq]
    exact hwV
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hcover'
  rcases hx : disjEnum (g (2 * C + 2)) j with _ | x
  · rw [coverSet, hx] at hj
    exact absurd hj (Set.notMem_empty w)
  · rw [coverSet, hx] at hj
    have hpref : cantorPrefix w x.length = x := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hj
    set i : ℕ := exhIdx hmono hcover x.length with hi
    set Fi : Finset ℕ := F i with hFi
    set Z : BitString := restrictSeq Fi w with hZ
    have hFspec : ∀ m, m < x.length → m ∈ Fi := exhIdx_spec hmono hcover x.length
    have hcard : x.length ≤ Fi.card := by
      have hsub : Finset.range x.length ⊆ Fi := fun m hm => hFspec m (Finset.mem_range.1 hm)
      have h := Finset.card_le_card hsub
      rwa [Finset.card_range] at h
    have hZlen : Z.length = Fi.card := length_restrictSeq Fi w
    have htake : Z.take x.length = x := by
      rw [hZ, restrictSeq_take Fi hFspec w, hpref]
    have hZmem : Z ∈ compatList Fi x :=
      mem_compatList.2 ⟨hZlen, (take_eq_iff_agreeBool (by omega)).1 htake⟩
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hZmem
    have hpair : kraftPair hmono hcover g C j k = some (Fi, Z) := by
      rw [kraftPair_eq_bind, hx]
      simp only [Option.bind_some, kraftInner, ← hi, ← hFi, hk, Option.map_some]
    have hlow := hc₀ C j k Fi Z hpair
    have hhigh := hcw i
    rw [← hFi, ← hZ] at hhigh
    rcases eq_or_ne (finsetEventMass μ Fi Z) 0 with hzero | hpos
    · rw [hzero, mul_zero] at hhigh
      have hposw : 0 < complexityWeight (KPPair U (finsetCode Fi) Z) := by
        refine (complexityWeight_pos_iff _).2 ?_
        exact ne_top_of_le_ne_top (ENat.coe_ne_top _) (hcK (pairCode (finsetCode Fi) Z))
      exact absurd hhigh (not_le.2 hposw)
    · have hmasstop : finsetEventMass μ Fi Z ≠ ⊤ := measure_ne_top μ _
      have hkey : (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞) ^ C * finsetEventMass μ Fi Z
          ≤ (2 : ℝ≥0∞) ^ cw * finsetEventMass μ Fi Z := by
        rw [mul_assoc]
        exact le_trans hlow hhigh
      have hcancel : (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞) ^ C ≤ (2 : ℝ≥0∞) ^ cw :=
        (ENNReal.mul_le_mul_iff_left hpos hmasstop).1 hkey
      have heval : (2 : ℝ≥0∞)⁻¹ ^ c₀ * (2 : ℝ≥0∞) ^ C = (2 : ℝ≥0∞) ^ (cw + 1) := by
        rw [hC, show cw + c₀ + 1 = c₀ + (cw + 1) by omega, pow_add, ← mul_assoc,
          ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, one_mul]
      rw [heval] at hcancel
      have hscale : (2 : ℝ≥0∞) ^ (cw + 1) * (2 : ℝ≥0∞)⁻¹ ^ cw
          ≤ (2 : ℝ≥0∞) ^ cw * (2 : ℝ≥0∞)⁻¹ ^ cw := by gcongr
      have hL : (2 : ℝ≥0∞) ^ (cw + 1) * (2 : ℝ≥0∞)⁻¹ ^ cw = 2 := by
        rw [pow_succ, mul_comm ((2 : ℝ≥0∞) ^ cw) 2, mul_assoc, ← mul_pow,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, mul_one]
      have hR : (2 : ℝ≥0∞) ^ cw * (2 : ℝ≥0∞)⁻¹ ^ cw = 1 := by
        rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
      rw [hL, hR] at hscale
      exact absurd hscale (by norm_num)

end Kolmogorov
