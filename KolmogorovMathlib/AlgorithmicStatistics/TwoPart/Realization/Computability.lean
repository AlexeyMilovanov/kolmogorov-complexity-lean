import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.TemporalBadSets
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.FinalWindow
import KolmogorovMathlib.Restricted.EffectiveSelection.Part01
import KolmogorovMathlib.Restricted.Selection

/-!
# The realization construction is computable

Curve realization is stated with abstract finite sets — bad sets, temporal enumerations, the
greedy window — but the decoder has to run on lists.  This module proves the list mirrors and
the abstract notions agree, and that the list versions are computable.

`badSetsUpToTimeList_eq`, `newBadSetsAtTimeList_eq` and `temporalBadEnumListList_eq` match the
executable enumerations with the semantic families; `mergeSort_encode_eq_canonical`,
`firstElements_eq_take`, `canonical_filter_eq` and `canonical_prefix` show the canonical
enumeration of a finite set is what the list operations produce; `refresh_window_eq`,
`greedy_fold_correspondence` and `greedyWindowFoldList_eq` carry the correspondence through
the greedy fold.

The computability statements the decoder needs follow: `finalWindowFn_refreshCount_computable`,
`finalWindowFn_window_computable`, `finalWindowFn_window_nonempty_computable` and
`finalWindowFn_version_computable`.
-/

namespace Kolmogorov
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- The executable list of bad sets up to a time matches the semantic family, once
its entries are read as finite sets. -/
theorem badSetsUpToTimeList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen :
    ℕ)
    (t : ℕ) :
    (badSetsUpToTimeList c n curve m c_gen t).map List.toFinset = badSetsUpToTime c n
        (decodeCurve curve) m c_gen t := by
  unfold badSetsUpToTimeList badSetsUpToTime
  rw [← List.map_flatMap]
  have hinj : ∀ a ∈ List.flatMap
      (fun j => snapshotDescList c j (decodeCurve curve j - (m + logSlack c_gen n)) t)
      (List.filter (fun j => decide (m + logSlack c_gen n < decodeCurve curve j)) (List.range
          n)),
      ∀ b ∈ List.flatMap
      (fun j => snapshotDescList c j (decodeCurve curve j - (m + logSlack c_gen n)) t)
      (List.filter (fun j => decide (m + logSlack c_gen n < decodeCurve curve j)) (List.range
          n)),
      List.toFinset a = List.toFinset b → a = b := by
    intro a ha b hb hab
    rw [List.mem_flatMap] at ha hb
    obtain ⟨ja, _, ha⟩ := ha
    obtain ⟨jb, _, hb⟩ := hb
    have hca := snapshotDescList_canonical c ja _ t a ha
    have hcb := snapshotDescList_canonical c jb _ t b hb
    rw [← hca, ← hcb, hab]
  exact dedup_map_injOn List.toFinset _ hinj

/-- Every set in the list mirror `badSetsUpToTimeList` is in canonical form. -/
theorem badSetsUpToTimeList_canonical (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString)
    (m c_gen t : ℕ) :
    ∀ x ∈ badSetsUpToTimeList c n curve m c_gen t, canonicalFinsetList x.toFinset = x := by
  intro x hx
  unfold badSetsUpToTimeList at hx
  rw [mem_List.dedup, List.mem_flatMap] at hx
  obtain ⟨j, _, hx⟩ := hx
  exact snapshotDescList_canonical c j _ t x hx

/-- `List.map f` commutes with a `List.filter` provided the predicates agree on the
images of the list's elements. -/
theorem map_filter_congr {α β} (f : α → β) (p : α → Bool) (q : β → Bool) (l : List
    α)
    (h : ∀ x ∈ l, p x = q (f x)) : (l.filter p).map f = (l.map f).filter q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ht : ∀ x ∈ t, p x = q (f x) := fun x hx => h x (by simp [hx])
    have ha : p a = q (f a) := h a (by simp)
    by_cases hp : p a
    · rw [List.filter_cons_of_pos hp, List.map_cons, List.map_cons,
        List.filter_cons_of_pos (by rw [← ha]; exact hp), ih ht]
    · rw [List.filter_cons_of_neg hp, List.map_cons,
        List.filter_cons_of_neg (by rw [← ha]; simpa using hp), ih ht]

/-- The executable list of new bad sets at a time matches the semantic family. -/
theorem newBadSetsAtTimeList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen :
    ℕ)
    (t : ℕ) :
    (newBadSetsAtTimeList c n curve m c_gen t).map List.toFinset = newBadSetsAtTime c n
        (decodeCurve curve) m c_gen t := by
  cases t with
  | zero =>
    exact badSetsUpToTimeList_eq c n curve m c_gen 0
  | succ k =>
    unfold newBadSetsAtTimeList newBadSetsAtTime
    simp only
    rw [map_filter_congr (q := fun S => decide (S ∉ badSetsUpToTime c n (decodeCurve curve) m
        c_gen k)),
        badSetsUpToTimeList_eq c n curve m c_gen (k + 1)]
    intro x hx
    rw [← badSetsUpToTimeList_eq c n curve m c_gen k]
    have hxcanon := badSetsUpToTimeList_canonical c n curve m c_gen (k + 1) x hx
    -- `x ∈ list k ↔ x.toFinset ∈ (list k).map toFinset`, using canonicality.
    have key : x ∈ badSetsUpToTimeList c n curve m c_gen k ↔
        x.toFinset ∈ (badSetsUpToTimeList c n curve m c_gen k).map List.toFinset := by
      constructor
      · intro hmem; exact List.mem_map_of_mem hmem
      · intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨r, hr, hrf⟩ := hmem
        have hrcanon := badSetsUpToTimeList_canonical c n curve m c_gen k r hr
        have : x = r := by rw [← hxcanon, ← hrcanon, hrf]
        exact this ▸ hr
    rw [List.elem_eq_mem, ← decide_not]
    exact decide_eq_decide.mpr (not_congr key)

/-- The executable temporal enumeration matches the semantic temporal enumeration. -/
theorem temporalBadEnumListList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen
    : ℕ)
    (t_max : ℕ) :
    (temporalBadEnumListList c n curve m c_gen t_max).map List.toFinset = temporalBadEnumList c
        n
        (decodeCurve curve) m c_gen t_max := by
  unfold temporalBadEnumListList temporalBadEnumList
  rw [List.map_flatMap]
  congr 1
  funext t
  exact newBadSetsAtTimeList_eq c n curve m c_gen t

/-- The `mergeSort` used inside `firstElements`/`firstBlock` produces exactly the
canonical enumeration `canonicalFinsetList`.  Both are `Nodup`, `bitStringLE`-sorted
permutations of `S.toList`, so they coincide by uniqueness of the sorted list. -/
theorem mergeSort_encode_eq_canonical (S : Finset BitString) :
    S.toList.mergeSort (fun a b => decide (Encodable.encode a ≤ Encodable.encode b))
      = canonicalFinsetList S := by
  set le := (fun a b : BitString => decide (Encodable.encode a ≤ Encodable.encode b)) with hle
  have hperm := List.mergeSort_perm S.toList le
  have hnd : (S.toList.mergeSort le).Nodup := hperm.nodup_iff.mpr S.nodup_toList
  have htrans : ∀ a b c, le a b = true → le b c = true → le a c = true := by
    intro a b c; simp only [hle, decide_eq_true_eq]; exact le_trans
  have htotal : ∀ a b, (le a b || le b a) = true := by
    intro a b; simp only [hle, Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _
  have hpair : (S.toList.mergeSort le).Pairwise bitStringLE := by
    have hp := List.pairwise_mergeSort htrans htotal S.toList
    refine hp.imp ?_
    intro a b hab
    exact of_decide_eq_true hab
  have htf : (S.toList.mergeSort le).toFinset = S := by
    ext x
    rw [List.mem_toFinset, hperm.mem_iff, Finset.mem_toList]
  have hcanon := canonicalFinsetList_of_sorted (S.toList.mergeSort le) hnd hpair
  rw [htf] at hcanon
  exact hcanon.symm

/-- `firstElements S size` is the `toFinset` of the first `size` elements of the
canonical enumeration of `S`. -/
theorem firstElements_eq_take (S : Finset BitString) (size : ℕ) :
    firstElements S size = ((canonicalFinsetList S).take size).toFinset := by
  unfold firstElements GreedyWindow.firstBlock
  rw [mergeSort_encode_eq_canonical]

/-- Filtering the canonical enumeration commutes with `Finset.filter`. -/
theorem canonical_filter_eq (G : Finset BitString) (p : BitString → Bool) :
    (canonicalFinsetList G).filter p = canonicalFinsetList (G.filter (fun x => p x)) := by
  have hnd : ((canonicalFinsetList G).filter p).Nodup :=
    (canonicalFinsetList_nodup G).filter p
  have hpairG : (canonicalFinsetList G).Pairwise bitStringLE := Finset.pairwise_sort G
      bitStringLE
  have hpair : ((canonicalFinsetList G).filter p).Pairwise bitStringLE :=
    List.Pairwise.filter p hpairG
  have htf : ((canonicalFinsetList G).filter p).toFinset = G.filter (fun x => p x) := by
    rw [List.toFinset_filter, canonicalFinsetList_toFinset]
  have hcanon := canonicalFinsetList_of_sorted _ hnd hpair
  rw [htf] at hcanon
  exact hcanon.symm

/-- A prefix of the canonical enumeration is its own canonical enumeration. -/
theorem canonical_prefix (S : Finset BitString) (k : ℕ) :
    canonicalFinsetList (((canonicalFinsetList S).take k).toFinset) = (canonicalFinsetList
        S).take k
        := by
  apply canonicalFinsetList_of_sorted
  · exact (List.take_sublist k _).nodup (canonicalFinsetList_nodup S)
  · exact (Finset.pairwise_sort S bitStringLE).sublist (List.take_sublist k _)

/-- The list-side refreshed window equals the canonical enumeration of the
abstract refreshed window `firstElements (G \ deleted) size`. -/
theorem refresh_window_eq (G : Finset BitString) (size : ℕ) (deleted_list : List BitString)
    (deleted_fin : Finset BitString) (hd : deleted_list.toFinset = deleted_fin) :
    ((canonicalFinsetList G).filter (fun x => !(deleted_list.elem x))).take size
      = canonicalFinsetList (firstElements (G \ deleted_fin) size) := by
  have hfilter : (canonicalFinsetList G).filter (fun x => !(deleted_list.elem x))
      = canonicalFinsetList (G \ deleted_fin) := by
    rw [canonical_filter_eq]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Bool.not_eq_true', List.elem_eq_mem,
      decide_eq_false_iff_not, List.mem_toFinset, ← hd]
  rw [hfilter, firstElements_eq_take, canonical_prefix]

/-- Correspondence between the computable list fold and the abstract `GreedyWindow.fold`,
carried along the invariant `dl.toFinset = df`, `wl = canonicalFinsetList wf`, `cl = cf`. -/
theorem greedy_fold_correspondence (G : Finset BitString) (size : ℕ) :
    ∀ (L : List (List BitString)) (dl wl : List BitString) (cl : ℕ)
      (df wf : Finset BitString) (cf : ℕ),
      dl.toFinset = df → wl = canonicalFinsetList wf → cl = cf →
      let stl' := L.foldl (greedyWindowStepList (canonicalFinsetList G) size) (dl, wl, cl)
      let stf' := (L.map List.toFinset).foldl
        (GreedyWindow.step G (fun S => firstElements S size)) (df, wf, cf)
      stl'.1.toFinset = stf'.1 ∧ stl'.2.1 = canonicalFinsetList stf'.2.1 ∧ stl'.2.2 =
          stf'.2.2 := by
  intro L
  induction L with
  | nil =>
    intro dl wl cl df wf cf h1 h2 h3
    exact ⟨h1, h2, h3⟩
  | cons d rest ih =>
    intro dl wl cl df wf cf h1 h2 h3
    -- new deleted set (list side) and its `toFinset`.
    have hdel : (List.dedup (dl ++ (d.filter (fun x => (canonicalFinsetList G).elem
        x)))).toFinset
        = df ∪ (d.toFinset ∩ G) := by
      ext x
      simp only [List.mem_toFinset, mem_List.dedup, List.mem_append, List.mem_filter,
        List.elem_eq_mem, decide_eq_true_eq, Finset.mem_union, Finset.mem_inter,
        mem_canonicalFinsetList, ← h1]
    -- the emptiness test agrees on both sides.
    have htest : (wl.all (fun x => (List.dedup (dl ++ (d.filter (fun x => (canonicalFinsetList
        G).elem x)))).elem x) = true)
        ↔ (wf ⊆ df ∪ (d.toFinset ∩ G)) := by
      rw [List.all_eq_true]
      constructor
      · intro hall y hy
        have hyl : y ∈ wl := by rw [h2, mem_canonicalFinsetList]; exact hy
        have h := hall y hyl
        rw [List.elem_eq_mem, decide_eq_true_eq, ← List.mem_toFinset, hdel] at h
        exact h
      · intro hsub x hx
        rw [List.elem_eq_mem, decide_eq_true_eq, ← List.mem_toFinset, hdel]
        apply hsub
        rw [← mem_canonicalFinsetList, ← h2]; exact hx
    -- reduce one fold step on both sides, then apply the induction hypothesis.
    simp only [List.foldl_cons, List.map_cons, greedyWindowStepList, GreedyWindow.step]
    by_cases hb : wf ⊆ df ∪ (d.toFinset ∩ G)
    · rw [ite_eq_left (htest.mpr hb), ite_eq_left hb]
      apply ih
      · exact hdel
      · exact refresh_window_eq G size _ _ hdel
      · rw [h3]
    · rw [ite_eq_right (fun hc => hb (htest.mp hc)), ite_eq_right hb]
      apply ih
      · exact hdel
      · exact h2
      · exact h3

/-- The list-level greedy-window fold agrees with the finite-set-level one. -/
theorem greedyWindowFoldList_eq (G : Finset BitString) (size : ℕ) (L : List (List BitString))
    :
    let st' := greedyWindowFoldList (canonicalFinsetList G) size L
    (st'.1.toFinset, st'.2.1.toFinset, st'.2.2) = GreedyWindow.fold G
        (fun S => firstElements S size) (L.map List.toFinset) := by
  have hinit_w : (canonicalFinsetList G).take size = canonicalFinsetList (firstElements G size)
      :=
      by
    rw [firstElements_eq_take, canonical_prefix]
  obtain ⟨e1, e2, e3⟩ := greedy_fold_correspondence G size L [] ((canonicalFinsetList
      G).take size) 0
    ∅ (firstElements G size) 0 (by simp) hinit_w rfl
  simp only [greedyWindowFoldList, GreedyWindow.fold]
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨e1, ?_, e3⟩
  rw [e2, canonicalFinsetList_toFinset]

/-- The list-side window is the canonical enumeration of the abstract window. -/
theorem greedyWindowFoldList_window_canonical (G : Finset BitString) (size : ℕ)
    (L : List (List BitString)) :
    (greedyWindowFoldList (canonicalFinsetList G) size L).2.1
      = canonicalFinsetList
          (GreedyWindow.fold G (fun S => firstElements S size) (L.map List.toFinset)).2.1 := by
  have hinit_w : (canonicalFinsetList G).take size = canonicalFinsetList (firstElements G size)
      :=
      by
    rw [firstElements_eq_take, canonical_prefix]
  obtain ⟨_, e2, _⟩ := greedy_fold_correspondence G size L [] ((canonicalFinsetList G).take
      size) 0
    ∅ (firstElements G size) 0 (by simp) hinit_w rfl
  simpa only [greedyWindowFoldList, GreedyWindow.fold] using e2

/-- The executable refresh count agrees with the semantic refresh count. -/
theorem temporalRefreshCountList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString)
    (m c_gen i t : ℕ) :
    temporalRefreshCountList c n curve m c_gen i t = temporalRefreshCount c n (decodeCurve
        curve) m
        c_gen i t := by
  unfold temporalRefreshCountList temporalRefreshCount
  have h := greedyWindowFoldList_eq ((allStrings n).toFinset) (2 ^ decodeCurve curve i)
    (temporalBadEnumListList c n curve m c_gen t)
  have h2 := congrArg (fun p : Finset BitString × Finset BitString × ℕ => p.2.2) h
  simp only at h2
  rw [h2, temporalBadEnumListList_eq]
  rfl

/-
Computability plumbing for the list-mirror layer:
* `snapshotDescList_primrec` gives the `c`-parameterized enumeration as `Primrec`.
* the general primitive-recursion helpers `natPow_primrec`, `natSize_primrec`,
  `logSlack_primrec`, `decodeCurve_primrec`, `list_mem_decide_primrec` and
  `list_dedup_gen_primrec`.
* `badSetsUpToTimeList_primrec` = `List.dedup` of a `flatMap`/`filter` over
  `List.range n` whose predicate uses `decodeCurve` and `logSlack`, then
  `newBadSetsAtTimeList_primrec` / `temporalBadEnumListList_primrec` by
  `filter`/`flatMap` composition, and finally `temporalRefreshCountList_computable`
  / `temporalWindowList_computable` by composing `greedyWindowFoldList_computable`
  with `canonicalFinsetList`/`decodeCurve` computability.

Natural-number exponentiation is primitive recursive in both arguments.
-/
theorem natPow_primrec : Primrec₂ (fun a b : ℕ => a ^ b) :=
  Primrec.nat_iff.mpr Nat.Primrec.pow
/-
`Nat.size` (the binary length) is primitive recursive.  Uses the closed form
`Nat.size n = #{k ∈ range (n+1) | 2^k ≤ n}`.
-/
theorem natSize_primrec : Primrec (fun n => Nat.size n) := by
  -- Express `Nat.size` using primitive-recursive list operations.
  have h_size_primrec : Primrec
      (fun n : ℕ => (List.range (n + 1)).filter (fun k => decide (2 ^ k ≤ n)) |>.length) :=
          by
    convert Primrec.comp ( Primrec.list_length ) ( list_filter_primrec ( Primrec.comp (
        Primrec.list_range ) ( Primrec.succ ) ) _ ) using 1;
    convert Primrec.nat_le.comp ( natPow_primrec.comp ( Primrec.const 2 ) ( Primrec.snd ) ) (
        Primrec.fst ) using 1;
    constructor <;> intro h <;> simp_all +decide only [Primrec₂, PrimrecPred];
    · exact ⟨ inferInstance, h ⟩;
    · grind
  generalize_proofs at *
  convert h_size_primrec using 1
  ext n
  rw [show (List.filter (fun k => decide (2 ^ k ≤ n)) (List.range (n + 1))) =
    List.range (Nat.size n) from ?_]
  · simp +decide
  · have h_filter : ∀ k ∈ List.range (n + 1), 2 ^ k ≤ n ↔ k < Nat.size n := by
      simp +decide [Nat.lt_size]
    generalize_proofs at *
    have h_filter_eq : List.filter (fun k => k < Nat.size n) (List.range (n + 1)) =
        List.range (Nat.size n) := by
      have h_filter_eq : ∀ m n : ℕ, m ≤ n →
          List.filter (fun k => k < m) (List.range n) = List.range m := by
        intros m n hmn
        induction hmn <;> simp_all +decide [List.range_succ]
      apply h_filter_eq
      exact Nat.size_le.mpr (by
        exact Nat.recOn n (by norm_num) fun n ihn => by
          norm_num [Nat.pow_succ'] at ihn ⊢
          linarith)
    generalize_proofs at *
    rw [← h_filter_eq, List.filter_congr]
    aesop (simp_config := { singlePass := true })

/-
`logSlack` is primitive recursive in both arguments.  Recall
`logSlack c n = c * (Nat.bits n).length + c = c * Nat.size n + c`.
-/
theorem logSlack_primrec : Primrec₂ (fun c n : ℕ => logSlack c n) := by
  unfold logSlack;
  convert Primrec.nat_add.comp ( Primrec.nat_mul.comp ( Primrec.fst ) ( natSize_primrec.comp (
      Primrec.snd ) ) ) ( Primrec.fst ) using 1;
  simp +decide [ Primrec₂, Nat.size_eq_bits_len ]

/-
`decodeCurve` is primitive recursive in the code bitstring and the index.
-/
theorem decodeCurve_primrec : Primrec₂ (fun (code : BitString) (i : ℕ) => decodeCurve code
    i) := by
  have h_splitOnP : ∀ code : BitString,
      (List.splitOnP (fun x : Bool => !x) code).map List.length =
        code.foldr (fun b acc => if b then (acc.headI + 1) :: acc.tail else 0 :: acc) [0] := by
    intro code
    induction code with
    | nil => simp [List.splitOnP_nil]
    | cons b code ih =>
      cases b
      · simp only [List.splitOnP_cons_eq_ite_modifyHead, Bool.not_false,
          ↓reduceIte, List.map_cons, List.length_nil]
        exact congrArg (fun xs => 0 :: xs) ih
      · simp only [List.splitOnP_cons_eq_ite_modifyHead, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
        cases hs : List.splitOnP (fun x : Bool => !x) code with
        | nil => exact (List.splitOnP_ne_nil (fun x : Bool => !x) code hs).elim
        | cons head tail =>
          have ih' := ih
          rw [hs] at ih'
          simp only [List.foldr_cons]
          rw [← ih']
          simp [List.modifyHead]
  have h_splitOn : ∀ code : BitString,
      (code.splitOn false).map List.length =
        code.foldr (fun b acc => if b then (acc.headI + 1) :: acc.tail else 0 :: acc) [0] := by
    intro code
    simpa [List.splitOn] using h_splitOnP code
  have hstep : Primrec₂
      (fun (_ : BitString × List ℕ) (q : Bool × List ℕ) =>
        if q.1 then (q.2.headI + 1) :: q.2.tail else 0 :: q.2) := by
    have hcond : PrimrecPred
        (fun p : (BitString × List ℕ) × (Bool × List ℕ) => p.2.1 = true) :=
      Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true)
    have hthen : Primrec
        (fun p : (BitString × List ℕ) × (Bool × List ℕ) =>
          (p.2.2.headI + 1) :: p.2.2.tail) :=
      Primrec.list_cons.comp
        (Primrec.nat_add.comp
          (Primrec.list_headI.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.const 1))
        (Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd))
    have helse : Primrec
        (fun p : (BitString × List ℕ) × (Bool × List ℕ) => 0 :: p.2.2) :=
      Primrec.list_cons.comp (Primrec.const 0) (Primrec.snd.comp Primrec.snd)
    exact Primrec.ite hcond hthen helse
  have hfold : Primrec
      (fun p : BitString × List ℕ =>
        p.1.foldr (fun b acc => if b then (acc.headI + 1) :: acc.tail else 0 :: acc) p.2) :=
    (Primrec.list_foldr Primrec.fst Primrec.snd hstep).of_eq fun _ => rfl
  have hgetD : Primrec (fun p : List ℕ × ℕ => p.1.getD p.2 0) :=
    (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const 0)).of_eq fun _ => rfl
  have hraw : Primrec₂
      (fun (code : BitString) (i : ℕ) =>
        (code.foldr (fun b acc => if b then (acc.headI + 1) :: acc.tail else 0 :: acc) [0]).getD
          i 0) := by
    exact hgetD.comp
      (Primrec.pair
        (hfold.comp (Primrec.pair Primrec.fst (Primrec.const [0])))
        Primrec.snd)
  refine hraw.of_eq ?_
  intro code i
  unfold decodeCurve
  rw [h_splitOn code]

/-- Membership `a ∈ l` is a primitive-recursive relation for any primcodable type
with decidable equality. -/
theorem list_mem_decide_primrec {α} [Primcodable α] [DecidableEq α] :
    Primrec₂ (fun (a : α) (l : List α) => decide (a ∈ l)) := by
  have key : ∀ (a : α) (l : List α),
      decide (a ∈ l) = l.foldr (fun x acc => if x = a then true else acc) false := by
    intro a l; induction l with
    | nil => simp
    | cons x t ih =>
      simp only [List.mem_cons, List.foldr_cons, ← ih]
      by_cases h : x = a
      · simp only [h, true_or, decide_true, ↓reduceIte]
      · simp only [Bool.decide_or, h, ↓reduceIte, eq_comm, Bool.eq_or_self,
          true_eq_decide_iff]
        exact fun heq => absurd heq.symm h
  have hcond : PrimrecPred (fun a : (α × List α) × (α × Bool) => a.2.1 = a.1.1) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)
  have hstep : Primrec₂ (fun (p : α × List α) (q : α × Bool) => if q.1 = p.1 then true
      else q.2) :=
    Primrec.ite hcond (Primrec.const true) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.snd (Primrec.const false) hstep).of_eq (fun p => (key p.1
      p.2).symm)

/-
The project-local `List.dedup` agrees with Mathlib's `_root_.List.dedup`
(general element type).
-/
theorem list_dedup_eq_root_gen {α} [DecidableEq α] (l : List α) :
    List.dedup l = _root_.List.dedup l := by
      induction l <;> simp_all +decide [ List.dedup ];
      aesop

/-- The project-local `List.dedup` is primitive recursive for any primcodable type
with decidable equality. -/
theorem list_dedup_gen_primrec {α} [Primcodable α] [DecidableEq α] :
    Primrec (fun l : List α => List.dedup l) := by
  have key : ∀ l : List α,
      List.dedup l = l.foldr (fun a acc => if a ∈ acc then acc else a :: acc) [] := by
    intro l; induction l with
    | nil => rfl
    | cons a t ih => simp only [List.dedup, List.foldr_cons, ih]
  have hmem := @list_mem_decide_primrec α _ _
  have hbool : Primrec (fun p : List α × (α × List α) => decide (p.2.1 ∈ p.2.2)) :=
    hmem.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ (fun (_ : List α) (q : α × List α) => if q.1 ∈ q.2 then q.2 else
      q.1 :: q.2)
      := by
    have := Primrec.cond hbool (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    exact this.of_eq (fun p => by cases h : decide (p.2.1 ∈ p.2.2) <;> simp_all)
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq (fun l => (key l).symm)

/-- Primitive-recursive version of `badSetsUpToTimeList_computable`. -/
theorem badSetsUpToTimeList_primrec (c : Nat.Partrec.Code) :
    Primrec
        (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => badSetsUpToTimeList c p.1.1 p.1.2.1
            p.1.2.2.1 p.1.2.2.2 p.2) := by
  let P := ℕ × BitString × ℕ × ℕ
  have hlist : Primrec
      (fun p : P × ℕ => List.filter
        (fun j => p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1 < decodeCurve p.1.2.1 j)
        (List.range p.1.1)) := by
    have hrange : Primrec (fun p : P × ℕ => List.range p.1.1) :=
      Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)
    have hcgen : Primrec (fun p : P × ℕ => p.1.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hn : Primrec (fun p : P × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
    have hm : Primrec (fun p : P × ℕ => p.1.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hlhs : Primrec (fun p : P × ℕ => p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1) :=
      Primrec.nat_add.comp hm (logSlack_primrec.comp hcgen hn)
    have hcurve : Primrec (fun p : P × ℕ => p.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hpred : Primrec₂
        (fun (p : P × ℕ) (j : ℕ) =>
          decide (p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1 < decodeCurve p.1.2.1 j)) := by
      exact PrimrecPred.decide
        (Primrec.nat_lt.comp
          (hlhs.comp Primrec.fst)
          (decodeCurve_primrec.comp (hcurve.comp Primrec.fst) Primrec.snd))
    exact list_filter_primrec hrange hpred
  have hcurveAt : Primrec
      (fun q : (P × ℕ) × ℕ => decodeCurve q.1.1.2.1 q.2) := by
    exact decodeCurve_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd
  have hlhs : Primrec
      (fun q : (P × ℕ) × ℕ =>
        q.1.1.2.2.1 + logSlack q.1.1.2.2.2 q.1.1.1) := by
    have hm : Primrec (fun q : (P × ℕ) × ℕ => q.1.1.2.2.1) :=
      Primrec.fst.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have hcgen : Primrec (fun q : (P × ℕ) × ℕ => q.1.1.2.2.2) :=
      Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have hn : Primrec (fun q : (P × ℕ) × ℕ => q.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    exact Primrec.nat_add.comp hm (logSlack_primrec.comp hcgen hn)
  have hargs : Primrec
      (fun q : (P × ℕ) × ℕ =>
        ((q.2, q.1.2), decodeCurve q.1.1.2.1 q.2 -
          (q.1.1.2.2.1 + logSlack q.1.1.2.2.2 q.1.1.1))) := by
    exact Primrec.pair
      (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.nat_sub.comp hcurveAt hlhs)
  have hbody : Primrec₂
      (fun (p : P × ℕ) (j : ℕ) =>
        snapshotDescList c j
          (decodeCurve p.1.2.1 j - (p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1)) p.2) := by
    exact ((snapshotDescList_primrec c).comp hargs).of_eq fun _ => rfl
  exact (list_dedup_gen_primrec.comp (Primrec.list_flatMap hlist hbody)).of_eq fun _ => rfl

/-- The executable list of bad sets up to a time is computable in its parameters. -/
theorem badSetsUpToTimeList_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => badSetsUpToTimeList c p.1.1
        p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) :=
  (badSetsUpToTimeList_primrec c).to_comp

/-
Primitive-recursive version of `newBadSetsAtTimeList_computable`.
-/
theorem newBadSetsAtTimeList_primrec (c : Nat.Partrec.Code) :
    Primrec
        (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => newBadSetsAtTimeList c p.1.1 p.1.2.1
            p.1.2.2.1 p.1.2.2.2 p.2) := by
  have h := listNewAt_primrec (badSetsUpToTimeList_primrec c)
  refine h.of_eq ?_
  intro p
  cases p.2 with
  | zero => rfl
  | succ t =>
    simp only [newBadSetsAtTimeList, Nat.add_sub_cancel]
    rw [ite_eq_right (Nat.add_one_ne_zero t)]
    congr 1
    funext S
    rw [List.elem_eq_mem]

/-- The executable list of new bad sets at a time is computable. -/
theorem newBadSetsAtTimeList_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => newBadSetsAtTimeList c p.1.1
        p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) :=
  (newBadSetsAtTimeList_primrec c).to_comp

/-
Primitive-recursive version of `temporalBadEnumListList_computable`.
-/
theorem temporalBadEnumListList_primrec (c : Nat.Partrec.Code) :
    Primrec
        (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => temporalBadEnumListList c p.1.1
            p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  have hrange : Primrec
      (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => List.range (p.2 + 1)) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have hargs : Primrec
      (fun q : (((ℕ × BitString × ℕ × ℕ) × ℕ) × ℕ) => (q.1.1, q.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hbody : Primrec₂
      (fun (p : (ℕ × BitString × ℕ × ℕ) × ℕ) (t : ℕ) =>
        newBadSetsAtTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 t) :=
    ((newBadSetsAtTimeList_primrec c).comp hargs).of_eq fun _ => rfl
  exact (Primrec.list_flatMap hrange hbody).of_eq fun _ => rfl

/-- The executable temporal enumeration is computable. -/
theorem temporalBadEnumListList_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => temporalBadEnumListList c
        p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) :=
  (temporalBadEnumListList_primrec c).to_comp

/-- `List.take` as a `filterMap` over `List.range`, used to establish its
primitive recursiveness. -/
theorem take_eq_filterMap {α} (l : List α) (k : ℕ) :
    l.take k = (List.range k).filterMap (fun i => l[i]?) := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    cases l with
    | nil => simp
    | cons a t =>
      simp only [List.take_succ_cons, List.range_succ_eq_map, List.filterMap_cons,
        List.getElem?_cons_zero, List.filterMap_map, Function.comp_def,
        List.getElem?_cons_succ, ih t]

/-- The project-local `List.dedup` agrees with Mathlib's `_root_.List.dedup`. -/
theorem list_dedup_eq_root (l : List BitString) : List.dedup l = _root_.List.dedup l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    unfold List.dedup
    rw [ih]
    by_cases h : a ∈ t
    · rw [ite_eq_left (List.mem_dedup.mpr h), _root_.List.dedup_cons_of_mem h]
    · rw [ite_eq_right (fun hc => h (List.mem_dedup.mp hc)), _root_.List.dedup_cons_of_notMem h]

/-- The project-local `List.dedup` is primitive recursive. -/
theorem local_dedup_primrec : Primrec (fun l : List BitString => List.dedup l) :=
  dedup_primrec.of_eq (fun l => (list_dedup_eq_root l).symm)

/-- One greedy-window step on lists is primitive recursive. -/
theorem greedyWindowStepList_primrec :
    Primrec (fun p : (List BitString × ℕ) × (List BitString × List BitString × ℕ) ×
        List BitString =>
      greedyWindowStepList p.1.1 p.1.2 p.2.1 p.2.2) := by
  set P := (List BitString × ℕ) × (List BitString × List BitString × ℕ) × List
      BitString with hP
  have hG : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have hsize : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have hst1 : Primrec (fun p : P => p.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hst21 : Primrec (fun p : P => p.2.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hst22 : Primrec (fun p : P => p.2.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hd : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  -- d ∩ G  (list side)
  have hfilt : Primrec (fun p : P => p.2.2.filter (fun x => decide (x ∈ p.1.1))) :=
    list_filter_primrec hd
      (bitString_mem_primrec.comp Primrec.snd (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  -- deleted := dedup (st.1 ++ d.filter (· ∈ G))
  have hdel : Primrec (fun p : P =>
      List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1)))) :=
    local_dedup_primrec.comp (Primrec.list_append.comp hst1 hfilt)
  -- membership in `deleted` (decide form)
  have hmemdel : Primrec₂ (fun (p : P) (x : BitString) =>
      decide (x ∈ List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1))))) :=
    bitString_mem_primrec.comp Primrec.snd (hdel.comp Primrec.fst)
  -- test: window ⊆ deleted
  have htest : Primrec (fun p : P =>
      p.2.1.2.1.all (fun x =>
        decide (x ∈ List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1)))))) :=
    list_all_primrec hst21 hmemdel
  -- refreshed window: (G.filter (· ∉ deleted)).take size
  have hnewwin : Primrec (fun p : P =>
      ((p.1.1).filter (fun x =>
        ! decide (x ∈ List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈
            p.1.1)))))).take p.1.2) :=
    KraftChaitin.take_primrec.comp (list_filter_primrec hG (Primrec.not.comp hmemdel)) hsize
  -- assemble
  have hthen : Primrec (fun p : P =>
      (List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1))),
        ((p.1.1).filter (fun x =>
          ! decide (x ∈ List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈
              p.1.1)))))).take p.1.2,
        p.2.1.2.2 + 1)) :=
    Primrec.pair hdel (Primrec.pair hnewwin (Primrec.succ.comp hst22))
  have helse : Primrec (fun p : P =>
      (List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1))),
        p.2.1.2.1, p.2.1.2.2)) :=
    Primrec.pair hdel (Primrec.pair hst21 hst22)
  have hcond : PrimrecPred (fun p : P =>
      (p.2.1.2.1.all (fun x =>
        decide (x ∈ List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1)))))) =
            true) :=
    Primrec.eq.comp htest (Primrec.const true)
  refine (Primrec.ite hcond hthen helse).of_eq (fun p => ?_)
  simp only [greedyWindowStepList, List.elem_eq_mem]

/-- One greedy-window step on lists is computable. -/
theorem greedyWindowStepList_computable :
    Computable (fun p : (List BitString × ℕ) × (List BitString × List BitString × ℕ) ×
        List BitString =>
      greedyWindowStepList p.1.1 p.1.2 p.2.1 p.2.2) :=
  greedyWindowStepList_primrec.to_comp

/-- The greedy-window fold on lists is computable. -/
theorem greedyWindowFoldList_computable :
    Computable (fun p : (List BitString × ℕ) × List (List BitString) =>
      greedyWindowFoldList p.1.1 p.1.2 p.2) := by
  apply Primrec.to_comp
  set Q := (List BitString × ℕ) × List (List BitString) with hQ
  have hf : Primrec (fun p : Q => p.2) := Primrec.snd
  have hg : Primrec (fun p : Q => (([] : List BitString), (p.1.1).take p.1.2, 0)) :=
    Primrec.pair (Primrec.const [])
      (Primrec.pair
        (KraftChaitin.take_primrec.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.fst))
        (Primrec.const 0))
  have hh : Primrec₂ (fun (p : Q) (sb : (List BitString × List BitString × ℕ) × List
      BitString) =>
      greedyWindowStepList p.1.1 p.1.2 sb.1 sb.2) :=
    greedyWindowStepList_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  refine (Primrec.list_foldl hf hg hh).of_eq (fun p => ?_)
  rw [greedyWindowFoldList]

/-- The executable refresh count is computable in its parameters. -/
theorem temporalRefreshCountList_computable (c : Nat.Partrec.Code) :
    Computable
        (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => temporalRefreshCountList c
            p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2)
        := by
  have hG : Computable
      (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => canonicalFinsetList (allStrings
          p.1.1).toFinset)
      := by
    convert ( Primrec.to_comp (canonicalFinsetList_toFinset_primrec.comp
        (allStrings_primrec.comp (Primrec.fst.comp (Primrec.fst))))) using 1
  have hsize : Computable
      (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => 2 ^ (decodeCurve p.1.2.1
          p.1.2.2.2.2)) := by
    have hsize : Computable (fun p : BitString × ℕ => 2 ^ (decodeCurve p.1 p.2)) := by
      have hsize : Primrec (fun p : BitString × ℕ => 2 ^ (decodeCurve p.1 p.2)) := by
        exact natPow_primrec.comp ( Primrec.const 2 ) ( decodeCurve_primrec.comp ( Primrec.fst )
            ( Primrec.snd ) );
      exact hsize.to_comp;
    convert hsize.comp ( Computable.fst.comp ( Computable.snd.comp ( Computable.fst ) ) |>
        Computable.pair <| Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp (
        Computable.snd.comp ( Computable.fst ) ) ) ) ) using 1
  have hbad : Computable
      (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => temporalBadEnumListList c p.1.1
          p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2)
      := by
    have := temporalBadEnumListList_computable c;
    convert this.comp ( show Computable ( fun p : ( ℕ × BitString × ℕ × ℕ × ℕ ) ×
        ℕ => ( ( p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1 ), p.2 ) ) from ?_ ) using 1;
    exact Computable.pair ( Computable.pair ( Computable.fst.comp ( Computable.fst ) ) (
        Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.fst ) ) ) (
        Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp (
        Computable.fst ) ) ) ) ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp
        ( Computable.snd.comp ( Computable.fst ) ) ) ) ) ) ) ) ( Computable.snd );
  exact (Computable.snd.comp
    (Computable.snd.comp
      (greedyWindowFoldList_computable.comp
        (Computable.pair (Computable.pair hG hsize) hbad)))).of_eq fun _ => rfl

/-- The computability of the temporal refresh count. -/
theorem temporalRefreshCount_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ =>
      temporalRefreshCount c p.1.1 (decodeCurve p.1.2.1) p.1.2.2.1 p.1.2.2.2.1
        p.1.2.2.2.2 p.2) := by
  refine Computable.of_eq (temporalRefreshCountList_computable c) ?_
  intro p
  exact temporalRefreshCountList_eq c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1
    p.1.2.2.2.2 p.2

/-- The computability of the temporal window via its canonical enumeration.

The statement uses the codebase's canonical computable enumeration
`canonicalFinsetList S = S.sort bitStringLE` (see `CodedFiniteDistribution.lean`),
which is also the representation used elsewhere in this development
(e.g. `snapshotDescList`, `codedUniformOn … .code`).  This is the form actually
needed by `partrec_finalWindowFn`, whose window code is built through
`codedUniformEncoder ∘ canonicalFinsetList`.  In contrast, `Finset.toList` uses
the `Classical.choice`-based quotient representative and is not computable. -/
theorem temporalWindowList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen i t
    : ℕ) :
    temporalWindowList c n curve m c_gen i t = canonicalFinsetList
        (temporalWindow c n (decodeCurve curve) m c_gen i t) := by
  unfold temporalWindowList temporalWindow
  rw [greedyWindowFoldList_window_canonical, temporalBadEnumListList_eq]
  rfl

/-- The executable temporal window is computable in its parameters. -/
theorem temporalWindowList_computable (c : Nat.Partrec.Code) :
    Computable
        (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => temporalWindowList c p.1.1
            p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2)
        := by
  have hG : Computable
      (fun p : (Nat × BitString × Nat × Nat × Nat) => canonicalFinsetList (allStrings
          p.1).toFinset)
      := by
    have hG : Primrec (fun p : ℕ => canonicalFinsetList (allStrings p).toFinset) :=
      canonicalFinsetList_toFinset_primrec.comp allStrings_primrec
    exact hG.comp ( Primrec.fst ) |> Primrec.to_comp;
  have hsize : Computable
      (fun p : (Nat × BitString × Nat × Nat × Nat) => 2 ^ (decodeCurve p.2.1 p.2.2.2.2)) :=
          by
    have hsize : Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) => decodeCurve
        p.2.1 p.2.2.2.2) :=
        by
      have hsize : Computable (fun p : (BitString × ℕ) => decodeCurve p.1 p.2) := by
        exact decodeCurve_primrec.to_comp;
      convert hsize.comp ( Computable.fst.comp ( Computable.snd ) |> Computable.pair <|
          Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) )
          ) using 1;
    convert Computable.comp ( show Computable ( fun n : ℕ => 2 ^ n ) from ?_ ) hsize using 1;
    have h_exp : Primrec (fun n : ℕ => 2 ^ n) :=
      (natPow_primrec.comp (Primrec.const 2) Primrec.id).of_eq fun _ => rfl
    exact h_exp.to_comp;
  have hp2 : Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ =>
          ((p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1), p.2)) :=
    let hn := Computable.fst.comp Computable.fst
    let hcurve := Computable.fst.comp (Computable.snd.comp Computable.fst)
    let hm := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
    let hcGen := Computable.fst.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    Computable.pair (Computable.pair hn (Computable.pair hcurve (Computable.pair hm hcGen)))
      Computable.snd
  have h_bad : Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ =>
      temporalBadEnumListList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2) :=
    ((temporalBadEnumListList_computable c).comp hp2).of_eq (fun _ => rfl)
  have h_args : Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ =>
      ((canonicalFinsetList (allStrings p.1.1).toFinset,
          2 ^ decodeCurve p.1.2.1 p.1.2.2.2.2),
        temporalBadEnumListList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2)) :=
    Computable.pair (Computable.pair (hG.comp Computable.fst) (hsize.comp Computable.fst)) h_bad
  have h_proj : Computable (fun p : List BitString × List BitString × ℕ => p.2.1) :=
    Computable.fst.comp Computable.snd
  exact (h_proj.comp (greedyWindowFoldList_computable.comp h_args)).of_eq
    (fun _ => rfl)

/-- The canonical listing of the semantic temporal window is computable in its
parameters. -/
theorem temporalWindow_computable (c : Nat.Partrec.Code) :
    Computable
        (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => canonicalFinsetList
            (temporalWindow c p.1.1 (decodeCurve p.1.2.1) p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2
            p.2))
        := by
  refine Computable.of_eq (temporalWindowList_computable c) ?_
  intro p
  exact temporalWindowList_eq c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2

/-- The computability of testing whether the temporal window is empty. -/
theorem temporalWindow_nonempty_bool_computable (c : Nat.Partrec.Code) :
    Computable
        (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => decide ((temporalWindow c
            p.1.1 (decodeCurve p.1.2.1) p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2).Nonempty))
        := by
      refine Computable.of_eq (f := fun p => decide ( ( canonicalFinsetList ( temporalWindow c
          p.1.1 ( decodeCurve p.1.2.1 ) p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2 ) ).length > 0 ))
          ?_ ?_
      · -- The length of a list is computable.
        have h_length_computable : Computable (fun l : List BitString => l.length) := by
          exact Computable.list_length;
        have h_length_computable : Computable (fun n : ℕ => decide (n > 0)) := by
          have hsucc : Computable₂ (fun (_ _ : ℕ) => true) := Computable.const true
          refine Computable.of_eq
            (Computable.nat_casesOn Computable.id (Computable.const false)
              hsucc) ?_
          rintro (_ | _) <;> simp +decide
        exact h_length_computable.comp ( ‹Computable fun l : List BitString =>
            l.length›.comp ( temporalWindow_computable c ) );
      · intro p
        rw [length_canonicalFinsetList]
        simp only [Finset.card_pos]

/-
Computability of the parameter packer for the final-window decoder: it maps the
decoder input `s` (paired with a time `t`) to the tuple
`((fwNatN s, fwCurveCode s, fwNatM s, fwNatCGen s, fwNatI s), t)` expected by
`temporalRefreshCount_computable` / `temporalWindow_computable`.
-/
theorem fwPacker_computable :
    Computable (fun s : BitString × ℕ =>
      (((fwNatN s.1, fwCurveCode s.1, fwNatM s.1, fwNatCGen s.1, fwNatI s.1) :
        ℕ × BitString × ℕ × ℕ × ℕ), s.2)) := by
  apply Computable.pair;
  · apply Computable.pair;
    · exact ((decodeNatCode_primrec.comp
        (decodeFirst_primrec.comp Primrec.fst)).to_comp).of_eq fun _ => rfl
    · apply Computable.pair;
      · have h_decodeSecond : Computable (fun s : BitString => decodeSecond s) := by
          exact decodeSecond_primrec.to_comp;
        exact h_decodeSecond.comp ( h_decodeSecond.comp ( h_decodeSecond.comp (
            h_decodeSecond.comp ( h_decodeSecond.comp ( Computable.fst ) ) ) ) );
      · apply Computable.pair;
        · apply Computable.comp (Primrec.to_comp (decodeNatCode_primrec.comp
            (decodeFirst_primrec.comp (decodeSecond_primrec.comp (decodeSecond_primrec.comp
            (Primrec.id))))) ) (Computable.fst);
        · apply Computable.pair;
          · apply Computable.comp (Primrec.to_comp decodeNatCode_primrec);
            exact Computable.comp ( Primrec.to_comp decodeFirst_primrec ) ( Computable.comp (
                Primrec.to_comp decodeSecond_primrec ) ( Computable.comp ( Primrec.to_comp
                decodeSecond_primrec ) ( Computable.comp ( Primrec.to_comp decodeSecond_primrec
                ) ( Computable.fst ) ) ) );
          · apply Computable.comp;
            · -- `fwNatI` is a composition of computable functions.
              apply Computable.comp (decodeNatCode_primrec.to_comp)
                  (decodeFirst_primrec.to_comp.comp (decodeSecond_primrec.to_comp));
            · exact Computable.fst;
  · exact Computable.snd

/-- Refresh count as a computable function of the decoder input paired with a time. -/
theorem finalWindowFn_refreshCount_computable (c : Nat.Partrec.Code) :
    Computable (fun p : BitString × ℕ => temporalRefreshCount c (fwNatN p.1)
      (decodeCurve (fwCurveCode p.1)) (fwNatM p.1) (fwNatCGen p.1) (fwNatI p.1) p.2) := by
  refine Computable.of_eq ((temporalRefreshCount_computable c).comp fwPacker_computable) ?_
  intro p; dsimp only

/-- The (canonical list of the) temporal window as a computable function of the
decoder input paired with a time. -/
theorem finalWindowFn_window_computable (c : Nat.Partrec.Code) :
    Computable (fun p : BitString × ℕ => canonicalFinsetList (temporalWindow c (fwNatN p.1)
      (decodeCurve (fwCurveCode p.1)) (fwNatM p.1) (fwNatCGen p.1) (fwNatI p.1) p.2)) := by
  refine Computable.of_eq ((temporalWindow_computable c).comp fwPacker_computable) ?_
  intro p; dsimp only

/-- Nonemptiness test of the temporal window as a computable function of the decoder
input paired with a time. -/
theorem finalWindowFn_window_nonempty_computable (c : Nat.Partrec.Code) :
    Computable (fun p : BitString × ℕ => decide ((temporalWindow c (fwNatN p.1)
      (decodeCurve (fwCurveCode p.1)) (fwNatM p.1) (fwNatCGen p.1) (fwNatI p.1)
          p.2).Nonempty)) := by
  refine Computable.of_eq ((temporalWindow_nonempty_bool_computable c).comp fwPacker_computable)
      ?_
  intro p; dsimp only

/-- Reading the version number off a final-window input is computable. -/
theorem finalWindowFn_version_computable :
    Computable (fun p : BitString × ℕ => fwNatVersion p.1) :=
  (bitsToNat_primrec.comp (decodeFirst_primrec.comp (decodeSecond_primrec.comp
    (decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec))))).to_comp.comp
    Computable.fst

end Kolmogorov
