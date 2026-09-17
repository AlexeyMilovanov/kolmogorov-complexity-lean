import KolmogorovMathlib.Restricted.Selection
import KolmogorovMathlib.Restricted.EffectiveSelection.Part01

/-!
# The marked code stream is short and still covers

The two properties the marked stream must have. It is computable and grows monotonically in the
stage (`familyMarkedCodeStream_computable`, `familyMarkedCodeStream_mono`), every entry is a
genuine family model code (`familyMarkedCodeStream_sound`), and it is short:
`familyMarkedCodeStream_length_bound` gives at most `(i + 2)(i + 1)(n + 1) 2 ^ (i + 1 - k)`
entries, via the window bound `online_window_length_le` and the per-block estimate
`blockSelection_length_mul_threshold`. Yet nothing is lost:
`selectionStrategyOnline_covers_of_list` and `familyMarkedCodeStream_covers` show every string
with `2 ^ k` descriptions at a stage still has one in the stream. The online strategy itself is
primitive recursive (`selectionStrategyOnline_primrec`).
-/

namespace Kolmogorov
open CodedFiniteDistribution
open Nat.Partrec (Code)

/-- The online selection strategy is a total primitive-recursive list operation
(built from `range`, `take`, `drop`, `filter`, `flatMap`, `sublists`, `find?`). -/
theorem selectionStrategyOnline_primrec (n i j k : ℕ) :
    Primrec (fun S : List BitString => selectionStrategyOnline n i j k S) := by
  have hbs : Primrec₂ (fun (s : ℕ) (L : List BitString) => blockSelection n i j k s L) :=
    ((blockSelection_primrec n i j k 0).comp Primrec.snd).of_eq (fun _ => rfl)
  have key : Primrec (fun S : List BitString =>
      (List.range S.length).flatMap (fun m =>
        ((List.range (i + 2)).filter (fun s => (m + 1) % 2 ^ s == 0)).flatMap
          (fun s => blockSelection n i j k s ((S.take (m + 1)).drop ((m + 1) - 2 ^ s))))) := by
    refine Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) ?_
    refine Primrec.list_flatMap ?_ ?_
    · exact list_filter_primrec (Primrec.const (List.range (i + 2)))
        ((Primrec.beq.comp
          (Primrec.nat_mod.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
            (primrec_two_pow_aux.comp Primrec.snd))
          (Primrec.const 0)).to₂)
    · exact hbs.comp Primrec.snd
        (Primrec.list_drop.comp
          (Primrec.nat_sub.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
            (primrec_two_pow_aux.comp Primrec.snd))
          (Primrec.list_take.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp Primrec.fst)))
  exact key.of_eq (fun S => rfl)

/-- The marked code stream is computable in the stage. -/
theorem familyMarkedCodeStream_computable (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k : ℕ) :
  Computable (fun t => familyMarkedCodeStream c i 𝒜 n j k t) := by
  have h := (selectionStrategyOnline_primrec n i j k).to_comp.comp
    (familyStageModelCodesList_computable c i 𝒜 j)
  exact h

/-- Each stage of the marked code stream is a prefix of the next. -/
theorem familyMarkedCodeStream_mono (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (n j k t : ℕ) :
  familyMarkedCodeStream c i 𝒜 n j k t <+: familyMarkedCodeStream c i 𝒜 n j k (t + 1) := by
  exact selectionStrategyOnline_prefix_of_prefix n i j k
    (familyStageModelCodesList_mono c i 𝒜 j t)

/-- Every code in the marked stream is a family model code for the size bound `j`. -/
theorem familyMarkedCodeStream_sound (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (n j k t : ℕ) :
  ∀ w ∈ familyMarkedCodeStream c i 𝒜 n j k t, IsFamilyModelCode 𝒜 j w := by
  intro w hw
  exact familyStageModelCodesList_sound c i 𝒜 j t w
    (selectionStrategyOnline_mem_input n i j k _ w hw)

/-- Each window `(S.take (m+1)).drop (m+1 - 2^s)` used by the online strategy has
length at most `2^s`. -/
theorem online_window_length_le (S : List BitString) (m s : ℕ) :
    ((S.take (m + 1)).drop (m + 1 - 2 ^ s)).length ≤ 2 ^ s := by
  rw [List.length_drop, List.length_take]
  exact (Nat.sub_le_sub_right (Nat.min_le_left _ _) _).trans
    (by rw [Nat.sub_sub_eq_min]; exact Nat.min_le_right _ _)

/-- Per-block bound: multiplying the number of selected block elements by the
selection threshold is at most `B.length * (n+1)`. -/
theorem blockSelection_length_mul_threshold (n i j k s : ℕ) (B : List BitString) :
    (blockSelection n i j k s B).length * selectionThreshold i k ≤ B.length * (n + 1) := by
  calc (blockSelection n i j k s B).length * selectionThreshold i k
      ≤ (B.length * (n + 1) / selectionThreshold i k) * selectionThreshold i k := by
        gcongr
        exact blockSelection_length_le n i j k s B
    _ ≤ B.length * (n + 1) := Nat.div_mul_le_self _ _

/-
Abstract combinatorial core of the online length bound.  Given per-pair data
`f m s` (the number of selected elements) and `w m s` (the window length) with
`f m s * m0 ≤ w m s * c` and `w m s ≤ 2 ^ s`, the total over the dyadic online
schedule is bounded by `cnt * L * c`.  The key point is that for each fixed block
size `s`, the windows are disjoint dyadic blocks, so their total length is at most
`L` (there are at most `L / 2^s` of them, each of length at most `2^s`).
-/
theorem online_double_sum_bound {cnt L m0 c : ℕ} (f w : ℕ → ℕ → ℕ)
    (hfw : ∀ m s, f m s * m0 ≤ w m s * c)
    (hw : ∀ m s, w m s ≤ 2 ^ s) :
    (((List.range L).map (fun m =>
        (((List.range cnt).filter (fun s => (m + 1) % 2 ^ s == 0)).map
          (fun s => f m s)).sum)).sum) * m0 ≤ cnt * L * c := by
  have hinner (m : ℕ) :
      (((List.range cnt).filter (fun s => (m + 1) % 2 ^ s == 0)).map
        (fun s => f m s)).sum =
        ∑ s ∈ Finset.filter
          (fun s => ((m + 1) % 2 ^ s == 0) = true) (Finset.range cnt), f m s := by
    simpa only [List.toFinset_filter, List.toFinset_range] using
      (List.sum_toFinset (fun s => f m s) (List.nodup_range.filter _)).symm
  have hlist :
      ((List.range L).map (fun m =>
        (((List.range cnt).filter (fun s => (m + 1) % 2 ^ s == 0)).map
          (fun s => f m s)).sum)).sum =
        ∑ m ∈ Finset.range L, ∑ s ∈ Finset.filter
          (fun s => ((m + 1) % 2 ^ s == 0) = true) (Finset.range cnt), f m s := by
    calc
      _ = ∑ m ∈ Finset.range L,
          (((List.range cnt).filter (fun s => (m + 1) % 2 ^ s == 0)).map
            (fun s => f m s)).sum := by
        simpa only [List.toFinset_range] using
          (List.sum_toFinset
            (fun m => (((List.range cnt).filter
              (fun s => (m + 1) % 2 ^ s == 0)).map (fun s => f m s)).sum)
            List.nodup_range).symm
      _ = _ := Finset.sum_congr rfl fun m _ => hinner m
  have hfubini :
      ∑ m ∈ Finset.range L, ∑ s ∈ Finset.filter
          (fun s => ((m + 1) % 2 ^ s == 0) = true) (Finset.range cnt),
          f m s * m0 ≤
        ∑ s ∈ Finset.range cnt, ∑ m ∈ Finset.filter
          (fun m => ((m + 1) % 2 ^ s == 0) = true) (Finset.range L),
          w m s * c := by
    calc
      _ ≤ ∑ m ∈ Finset.range L, ∑ s ∈ Finset.filter
          (fun s => ((m + 1) % 2 ^ s == 0) = true) (Finset.range cnt),
          w m s * c :=
        Finset.sum_le_sum fun m _ =>
          Finset.sum_le_sum fun s _ => hfw m s
      _ = _ := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
  have hcard (s : ℕ) :
      (Finset.filter (fun m => ((m + 1) % 2 ^ s == 0) = true)
        (Finset.range L)).card ≤ L / 2 ^ s := by
    have hset :
        Finset.filter (fun m => ((m + 1) % 2 ^ s == 0) = true) (Finset.range L) =
          Finset.filter (fun m => 2 ^ s ∣ m + 1) (Finset.range L) := by
      ext m
      simp [Nat.dvd_iff_mod_eq_zero]
    rw [hset, Nat.card_multiples]
  have hcolumn (s : ℕ) :
      ∑ m ∈ Finset.filter
          (fun m => ((m + 1) % 2 ^ s == 0) = true) (Finset.range L),
          w m s * c ≤ L * c := by
    calc
      _ ≤ ∑ _m ∈ Finset.filter
          (fun m => ((m + 1) % 2 ^ s == 0) = true) (Finset.range L),
          2 ^ s * c :=
        Finset.sum_le_sum fun m _ => Nat.mul_le_mul_right c (hw m s)
      _ = (Finset.filter
          (fun m => ((m + 1) % 2 ^ s == 0) = true)
          (Finset.range L)).card * (2 ^ s * c) := by simp
      _ ≤ (L / 2 ^ s) * (2 ^ s * c) :=
        Nat.mul_le_mul_right _ (hcard s)
      _ ≤ L * c := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right c (Nat.div_mul_le_self L (2 ^ s))
  have htotal :
      ∑ s ∈ Finset.range cnt, ∑ m ∈ Finset.filter
          (fun m => ((m + 1) % 2 ^ s == 0) = true) (Finset.range L),
          w m s * c ≤ cnt * L * c := by
    calc
      _ ≤ ∑ _s ∈ Finset.range cnt, L * c :=
        Finset.sum_le_sum fun s _ => hcolumn s
      _ = cnt * L * c := by simp [Nat.mul_assoc]
  calc
    (((List.range L).map (fun m =>
        (((List.range cnt).filter (fun s => (m + 1) % 2 ^ s == 0)).map
          (fun s => f m s)).sum)).sum) * m0 =
        (∑ m ∈ Finset.range L, ∑ s ∈ Finset.filter
          (fun s => ((m + 1) % 2 ^ s == 0) = true) (Finset.range cnt),
          f m s) * m0 := by rw [hlist]
    _ = ∑ m ∈ Finset.range L, ∑ s ∈ Finset.filter
          (fun s => ((m + 1) % 2 ^ s == 0) = true) (Finset.range cnt),
          f m s * m0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_mul _ _ _
    _ ≤ _ := hfubini
    _ ≤ _ := htotal

/-- The selection is short: its length times the threshold is at most `(i + 2)(n + 1)` times the
length of the input. -/
theorem selectionStrategyOnline_length_mul_threshold (n i j k : ℕ) (S : List BitString) :
    (selectionStrategyOnline n i j k S).length * selectionThreshold i k ≤
      (i + 2) * S.length * (n + 1) := by
  have heq : (selectionStrategyOnline n i j k S).length =
      ((List.range S.length).map (fun m =>
        (((List.range (i + 2)).filter (fun s => (m + 1) % 2 ^ s == 0)).map (fun s =>
          (blockSelection n i j k s ((S.take (m + 1)).drop (m + 1 - 2 ^
              s))).length)).sum)).sum := by
    unfold selectionStrategyOnline
    simp only [List.length_flatMap]
  rw [heq]
  have h := online_double_sum_bound
      (cnt := i + 2) (L := S.length) (m0 := selectionThreshold i k) (c := n + 1)
      (f := fun m s => (blockSelection n i j k s ((S.take (m + 1)).drop (m + 1 - 2 ^ s))).length)
      (w := fun m s => ((S.take (m + 1)).drop (m + 1 - 2 ^ s)).length)
      (fun m s => blockSelection_length_mul_threshold n i j k s _)
      (fun m s => online_window_length_le S m s)
  exact h

/-- From `L · 2 ^ k ≤ C · 2 ^ (i + 1)` one gets `L ≤ C · 2 ^ (i + 1 - k)`. -/
theorem bound_of_mul_pow_le_mul_pow {L C i k : ℕ} (h : L * 2 ^ k ≤ C * 2 ^ (i + 1)) :
    L ≤ C * 2 ^ (i + 1 - k) := by
  by_cases hk : k ≤ i + 1
  · have hpow :
        C * 2 ^ (i + 1) = (C * 2 ^ (i + 1 - k)) * 2 ^ k := by
      calc
        C * 2 ^ (i + 1) = C * 2 ^ (i + 1 - k + k) := by
          rw [Nat.sub_add_cancel hk]
        _ = C * (2 ^ (i + 1 - k) * 2 ^ k) := by
          rw [pow_add]
        _ = (C * 2 ^ (i + 1 - k)) * 2 ^ k := by
          ring
    have hmul : L * 2 ^ k ≤ (C * 2 ^ (i + 1 - k)) * 2 ^ k := by
      simpa [hpow] using h
    exact Nat.le_of_mul_le_mul_right hmul (pow_pos (by decide : 0 < 2) k)
  · have hk' : i + 1 ≤ k := by omega
    have hpowle : 2 ^ (i + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hk'
    have hmul : L * 2 ^ k ≤ C * 2 ^ k :=
      h.trans (Nat.mul_le_mul_left C hpowle)
    have hLC : L ≤ C :=
      Nat.le_of_mul_le_mul_right hmul (pow_pos (by decide : 0 < 2) k)
    have hsub : i + 1 - k = 0 := by omega
    simpa [hsub] using hLC

/-- For an input of at most `2 ^ (i + 1)` codes the selection has at most
`(i + 2)(i + 1)(n + 1) 2 ^ (i + 1 - k)` entries. -/
theorem selectionStrategyOnline_length_bound_of_le (n i j k : ℕ) (S : List BitString)
    (h : S.length ≤ 2 ^ (i + 1)) :
    (selectionStrategyOnline n i j k S).length ≤ (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) := by
  have h1 : (selectionStrategyOnline n i j k S).length * selectionThreshold i k ≤ (i + 2) *
      S.length * (n + 1) :=
    selectionStrategyOnline_length_mul_threshold n i j k S
  have h2 : (i + 2) * S.length * (n + 1) ≤ (i + 2) * 2 ^ (i + 1) * (n + 1) := by gcongr
  have h3 : (selectionStrategyOnline n i j k S).length * 2 ^ k ≤ (selectionStrategyOnline n i
      j k S).length * ((i + 1) * selectionThreshold i k) := by
    gcongr
    exact pow_le_mul_selectionThreshold i k
  have h4 : (selectionStrategyOnline n i j k S).length * ((i + 1) * selectionThreshold i k) =
      (i + 1) * ((selectionStrategyOnline n i j k S).length * selectionThreshold i k) := by ring
  have h5 : (i + 1) * ((selectionStrategyOnline n i j k S).length * selectionThreshold i k) ≤
      (i + 1) * ((i + 2) * 2 ^ (i + 1) * (n + 1)) :=
    Nat.mul_le_mul_left (i + 1) (le_trans h1 h2)
  have h6 : (i + 1) * ((i + 2) * 2 ^ (i + 1) * (n + 1)) = (i + 2) * (i + 1) * (n + 1) * 2 ^ (i
      + 1) := by ring
  have h7 : (selectionStrategyOnline n i j k S).length * 2 ^ k ≤ (i + 2) * (i + 1) * (n + 1) *
      2 ^ (i + 1) :=
    calc (selectionStrategyOnline n i j k S).length * 2 ^ k
      _ ≤ (selectionStrategyOnline n i j k S).length * ((i + 1) * selectionThreshold i k) := h3
      _ = (i + 1) * ((selectionStrategyOnline n i j k S).length * selectionThreshold i k) := h4
      _ ≤ (i + 1) * ((i + 2) * 2 ^ (i + 1) * (n + 1)) := h5
      _ = (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1) := h6
  exact bound_of_mul_pow_le_mul_pow h7

/-- Membership completeness for the accumulated stage list: every candidate code
visible at stage `t` is retained in the accumulated list at stage `t`. -/
theorem mem_familyStageModelCodesList_of_candidate (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j t : ℕ) (w : BitString)
    (hw : w ∈ familyCandidateModelCodesList c i 𝒜 j t) :
    w ∈ familyStageModelCodesList c i 𝒜 j t := by
  cases t with
  | zero =>
      change w ∈ (familyCandidateModelCodesList c i 𝒜 j 0).eraseDups
      exact mem_eraseDups_bitString.mpr hw
  | succ t =>
      change w ∈ (familyStageModelCodesList c i 𝒜 j t ++
        familyCandidateModelCodesList c i 𝒜 j (t + 1)).eraseDups
      exact mem_eraseDups_bitString.mpr (List.mem_append_right _ hw)

/-- Completeness + cover: every visible family-description code of `x` is present
in the accumulated stage list, and its decoded model cover contains `x`. -/
theorem mem_familyStageModelCodesList_and_cover_of_description (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j t : ℕ) (x w : BitString)
    (hw : w ∈ familyStageDescriptionCodes c i 𝒜 j t x) :
    w ∈ familyStageModelCodesList c i 𝒜 j t ∧
      x ∈ canonicalFinsetList
        (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset) := by
  rw [mem_familyStageDescriptionCodes] at hw
  obtain ⟨hmem, hdesc⟩ := hw
  obtain ⟨hEnum, hSnap⟩ := Finset.mem_inter.mp hmem
  rw [List.mem_toFinset] at hEnum hSnap
  obtain ⟨Sset, hSne, hSmem, hcode, hScard, hxS⟩ := hdesc
  -- cover contains x
  have hcover : x ∈ canonicalFinsetList
      (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset) := by
    rw [hcode, dataPoints_codedUniformOn, canonicalFinsetList_toFinset,
      mem_canonicalFinsetList]
    exact hxS
  refine ⟨?_, hcover⟩
  -- w is in the candidate list, hence in the stage list
  have hbool : isFamilyModelCodeBool j w = true := by
    unfold isFamilyModelCodeBool
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · rw [isCanonicalUniformCodeBool_iff, hcode]
      exact isCanonicalUniformCode_codedUniformOn Sset hSne
    · refine decide_eq_true ?_
      rw [hcode, dataPoints_codedUniformOn, canonicalFinsetList_toFinset]
      exact hScard
  have hcand : w ∈ familyCandidateModelCodesList c i 𝒜 j t := by
    rw [familyCandidateModelCodesList, List.mem_filter]
    exact ⟨hEnum, Bool.and_eq_true_iff.mpr ⟨decide_eq_true hSnap, hbool⟩⟩
  exact mem_familyStageModelCodesList_of_candidate c i 𝒜 j t w hcand

/-- A family-model code whose decoded model cover contains `x` is a
family-description code of `x`. -/
theorem isFamilyDescriptionCode_of_model_cover (𝒜 : PreDescriptionFamily) (j : ℕ)
    (x w : BitString) (hmodel : IsFamilyModelCode 𝒜 j w)
    (hxw : x ∈ canonicalFinsetList
      (((decodeDistributionData w).map CodedDistributionEntry.point).toFinset)) :
    IsFamilyDescriptionCode 𝒜 j x w := by
  obtain ⟨Sset, hSne, hmem, hcode, hcard⟩ := hmodel
  refine ⟨Sset, hSne, hmem, hcode, hcard, ?_⟩
  rw [hcode, dataPoints_codedUniformOn, canonicalFinsetList_toFinset,
    mem_canonicalFinsetList] at hxw
  exact hxw

/-- If some short sublist covers `T`, the one found by the search covers `T` too. -/
theorem computableGreedyCover_covers_of_exists {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : List α) (S : List β) (cover : β → List α) (m bound : ℕ)
    (h_exists : ∃ C : List β, C.Sublist S ∧ C.length ≤ bound ∧ ∀ x ∈ T,
        0 < (C.filter (fun b => decide (x ∈ cover b))).length) :
    ∀ x ∈ T, 0 < ((computableGreedyCover T S cover m bound).filter (fun b =>
        decide (x ∈ cover b))).length := by
  let good : List β → Bool := fun C =>
    (T.all (fun x => decide (0 < (C.filter (fun b => decide (x ∈ cover b))).length))) &&
      decide (C.length ≤ bound)
  have hgood : ∃ C ∈ S.sublists, good C = true := by
    obtain ⟨C, hCS, hlen, hcov⟩ := h_exists
    refine ⟨C, List.mem_sublists.mpr hCS, ?_⟩
    rw [Bool.and_eq_true_iff]
    refine ⟨?_, decide_eq_true hlen⟩
    rw [List.all_eq_true]
    intro x hx
    exact decide_eq_true (hcov x hx)
  unfold computableGreedyCover
  cases hfind : S.sublists.find? (fun C =>
      (T.all (fun x => decide (0 < (C.filter (fun b => decide (x ∈ cover b))).length))) &&
        decide (C.length ≤ bound)) with
  | none =>
      obtain ⟨C, hCS, hCgood⟩ := hgood
      have hfind_good : S.sublists.find? good = none := by
        simpa [good] using hfind
      have hfalse := List.find?_eq_none.mp hfind_good C hCS
      simp [hCgood] at hfalse
  | some C =>
      have hpred : good C = true := List.find?_some hfind
      rw [Bool.and_eq_true_iff] at hpred
      have hall := hpred.1
      rw [List.all_eq_true] at hall
      intro x hx
      have hx' := hall x hx
      simpa using (decide_eq_true_eq.mp hx')

/-- Pairing the entries of a list with their indices produces a duplicate-free list. -/
theorem zipIdx_nodup {α : Type} (L : List α) (start : ℕ) : (L.zipIdx start).Nodup := by
  apply List.Nodup.of_map Prod.snd
  rw [List.zipIdx_map_snd]
  exact List.nodup_range'

/-- Forgetting the indices after pairing returns the original list. -/
theorem zipIdx_map_fst {α : Type} (L : List α) (start : ℕ) :
    (L.zipIdx start).map Prod.fst = L := by
  induction L generalizing start with
  | nil => simp [List.zipIdx]
  | cons a as ih => simp [List.zipIdx, ih]

/-- Filtering the indexed list by a predicate on the entries and forgetting the indices is the
same as filtering the original list. -/
theorem zipIdx_filter_map_fst {α : Type} (L : List α) (P : α → Bool) (start : ℕ) :
    ((L.zipIdx start).filter (fun p => P p.1)).map Prod.fst = L.filter P := by
  induction L generalizing start with
  | nil => simp [List.zipIdx]
  | cons a as ih =>
      by_cases h : P a = true
      · simp [List.zipIdx, h, ih]
      · have hf : P a = false := by
          cases hpa : P a <;> simp_all
        simp [List.zipIdx, hf, ih]

/-- Selecting indexed entries by membership in a finite set yields a sublist of the original. -/
theorem zipIdx_filter_mem_map_fst_sublist {α : Type} [DecidableEq α]
    (L : List α) (C : Finset (α × ℕ)) :
    (((L.zipIdx 0).filter (fun p => decide (p ∈ C))).map Prod.fst).Sublist L := by
  have hsub : ((L.zipIdx 0).filter (fun p => decide (p ∈ C))).Sublist (L.zipIdx 0) :=
    List.filter_sublist
  have hmap := hsub.map Prod.fst
  simpa [zipIdx_map_fst] using hmap

/-- A string described by at least `selectionThreshold i k` models of a block is described by one
of the models selected from that block. -/
theorem blockSelection_covers_of_count (n i j k s : ℕ) (B : List BitString) (x : BitString)
    (hxlen : x.length = n) (hcount : selectionThreshold i k ≤ (B.filter (fun b =>
        decide (x ∈ canonicalFinsetList (((decodeDistributionData b).map
          CodedDistributionEntry.point).toFinset)))).length) :
    0 < ((blockSelection n i j k s B).filter (fun b =>
        decide (x ∈ canonicalFinsetList (((decodeDistributionData b).map
          CodedDistributionEntry.point).toFinset)))).length := by
  classical
  let m := selectionThreshold i k
  let cover : BitString → List BitString := fun b =>
    canonicalFinsetList (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)
  let T : List BitString := (allStrings n).filter (fun y =>
    decide (m ≤ (B.filter (fun b => decide (y ∈ cover b))).length))
  let Sidx : Finset (BitString × ℕ) := (B.zipIdx 0).toFinset
  let coverIdx : BitString × ℕ → Finset BitString := fun p => (cover p.1).toFinset
  let bound := B.length * (n + 1) / m
  let targetPred : BitString → Bool := fun b => decide (x ∈ cover b)
  have hxT : x ∈ T := by
    rw [List.mem_filter]
    refine ⟨(mem_allStrings n x).mpr hxlen, ?_⟩
    exact decide_eq_true (by simpa [m, cover] using hcount)
  have hm_pos : 0 < m := by simpa [m] using selectionThreshold_pos i k
  have hm : ∀ y ∈ T.toFinset, m ≤ (Sidx.filter (fun p => y ∈ coverIdx p)).card := by
    intro y hy
    have hyT : y ∈ T := List.mem_toFinset.mp hy
    rw [List.mem_filter] at hyT
    have hycount : m ≤ (B.filter (fun b => decide (y ∈ cover b))).length :=
      decide_eq_true_eq.mp hyT.2
    let Lidx : List (BitString × ℕ) := (B.zipIdx 0).filter (fun p => decide (y ∈ cover p.1))
    have hnod : Lidx.Nodup := by
      exact List.Sublist.nodup (l₁ := Lidx) (l₂ := B.zipIdx 0)
        List.filter_sublist (zipIdx_nodup B 0)
    have hfin : Lidx.toFinset = Sidx.filter (fun p => y ∈ coverIdx p) := by
      ext p
      simp [Lidx, Sidx, coverIdx]
    have hlen : Lidx.length = (B.filter (fun b => decide (y ∈ cover b))).length := by
      have hmap : Lidx.map Prod.fst = B.filter (fun b => decide (y ∈ cover b)) := by
        simpa [Lidx] using zipIdx_filter_map_fst B (fun b => decide (y ∈ cover b)) 0
      simpa using congrArg List.length hmap
    calc m ≤ (B.filter (fun b => decide (y ∈ cover b))).length := hycount
      _ = Lidx.length := hlen.symm
      _ = Lidx.toFinset.card := (List.toFinset_card_of_nodup hnod).symm
      _ = (Sidx.filter (fun p => y ∈ coverIdx p)).card := by rw [hfin]
  obtain ⟨C, hCS, hcov, hCbound⟩ := greedy_cover_indexed T.toFinset Sidx coverIdx m hm_pos hm
  have hTlog : Nat.log2 T.toFinset.card + 1 ≤ n + 1 := by
    have hcard : T.toFinset.card ≤ 2 ^ n := by
      calc T.toFinset.card ≤ T.length := List.toFinset_card_le _
        _ ≤ (allStrings n).length := List.Sublist.length_le List.filter_sublist
        _ = 2 ^ n := length_allStrings n
    by_cases hzero : T.toFinset.card = 0
    · simp [hzero]
    · have hltpow : T.toFinset.card < 2 ^ (n + 1) :=
        lt_of_le_of_lt hcard (Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
      have hloglt : Nat.log 2 T.toFinset.card < n + 1 :=
        Nat.log_lt_of_lt_pow hzero hltpow
      have hlogle : Nat.log2 T.toFinset.card ≤ n := by
        rw [Nat.log2_eq_log_two]
        omega
      omega
  have hSidx_card : Sidx.card = B.length := by
    simp [Sidx, List.toFinset_card_of_nodup (zipIdx_nodup B 0), List.length_zipIdx]
  have hCmul : C.card * m ≤ B.length * (n + 1) := by
    calc C.card * m ≤ Sidx.card * (Nat.log2 T.toFinset.card + 1) := hCbound
      _ ≤ B.length * (n + 1) := by
        exact Nat.mul_le_mul (le_of_eq hSidx_card) hTlog
  have hCcard : C.card ≤ bound := by
    simpa [bound] using (Nat.le_div_iff_mul_le hm_pos).mpr hCmul
  let CList : List BitString := ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).map Prod.fst
  have hCList_sub : CList.Sublist B := by
    simpa [CList] using zipIdx_filter_mem_map_fst_sublist B C
  have hCList_len : CList.length ≤ bound := by
    have hnod : ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).Nodup := by
      exact List.Sublist.nodup
        (l₁ := (B.zipIdx 0).filter (fun p => decide (p ∈ C)))
        (l₂ := B.zipIdx 0) List.filter_sublist (zipIdx_nodup B 0)
    have hsubC : ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).toFinset ⊆ C := by
      intro p hp
      rw [List.mem_toFinset, List.mem_filter] at hp
      exact decide_eq_true_eq.mp hp.2
    calc CList.length = ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).length := by simp [CList]
      _ = ((B.zipIdx 0).filter (fun p => decide (p ∈ C))).toFinset.card :=
          (List.toFinset_card_of_nodup hnod).symm
      _ ≤ C.card := Finset.card_le_card hsubC
      _ ≤ bound := hCcard
  let : BEq BitString := instBEqOfDecidableEq
  let : LawfulBEq BitString := inferInstance
  have h_exists : ∃ C' : List BitString, C'.Sublist B ∧ C'.length ≤ bound ∧
      ∀ y ∈ T, 0 < (C'.filter (fun b => decide (y ∈ cover b))).length := by
    refine ⟨CList, hCList_sub, hCList_len, ?_⟩
    intro y hyT
    have hyFin : y ∈ T.toFinset := List.mem_toFinset.mpr hyT
    have hyUnion : y ∈ C.biUnion coverIdx := hcov hyFin
    rw [Finset.mem_biUnion] at hyUnion
    rcases hyUnion with ⟨p, hpC, hyp⟩
    have hpS : p ∈ Sidx := hCS hpC
    have hpZip : p ∈ B.zipIdx 0 := by
      exact List.mem_toFinset.mp hpS
    have hpFilt : p ∈ (B.zipIdx 0).filter (fun p => decide (p ∈ C)) := by
      rw [List.mem_filter]
      exact ⟨hpZip, decide_eq_true hpC⟩
    have hyCover : y ∈ cover p.1 := List.mem_toFinset.mp hyp
    have hyMem : p.1 ∈ CList.filter (fun b => decide (y ∈ cover b)) := by
      rw [List.mem_filter]
      refine ⟨?_, decide_eq_true hyCover⟩
      exact List.mem_map.mpr ⟨p, hpFilt, rfl⟩
    exact List.length_pos_of_mem hyMem
  have hgreedy := computableGreedyCover_covers_of_exists T B cover m bound h_exists x hxT
  have hfilter_eq :
      ((computableGreedyCover T B cover m bound).filter targetPred).length =
        ((computableGreedyCover T B cover m bound).filter (fun b =>
            decide (x ∈ cover b))).length := by
    congr 1
    apply List.filter_congr
    intro b _hb
    dsimp [targetPred]
    by_cases h : x ∈ cover b <;> simp [h]
  have hfinal : 0 < ((computableGreedyCover T B cover m bound).filter targetPred).length := by
    rw [hfilter_eq]
    exact hgreedy
  simpa [blockSelection, m, cover, T, bound, targetPred] using hfinal

/-- Arithmetic bridge: `selectionThreshold i k = (2^k + i)/(i+1)`, so a count `c`
with `2^k ≤ (i+1) * c` already reaches the threshold. -/
theorem selectionThreshold_le_of_pow_le (i k c : ℕ) (h : 2 ^ k ≤ (i + 1) * c) :
    selectionThreshold i k ≤ c := by
  unfold selectionThreshold
  rw [Nat.div_le_iff_le_mul_add_pred (Nat.succ_pos i)]
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  nlinarith [h, Nat.mul_comm c (i + 1)]

/-
**Dyadic averaging core.** For any list of length `≤ 2^b` (with `b ≥ 1`), the
whole segment `[0, len)` decomposes into at most `b` aligned dyadic windows (one
per set bit of `len`), so by pigeonhole one such window `[M - 2^s, M)` carries at
least a `1/b` share of the total filtered count. Proved by induction on `b`,
splitting `L` at the midpoint `2^(b-1)` into a full left dyadic block and a right
remainder handled by the induction hypothesis.
-/
theorem dyadic_core {α : Type} (b : ℕ) (hb : 1 ≤ b) (L : List α) (P : α → Bool)
    (hL : L.length ≤ 2 ^ b) :
    ∃ M s, M ≤ L.length ∧ s ≤ b ∧ M % 2 ^ s = 0 ∧
      (L.filter P).length ≤ b * (((L.take M).drop (M - 2 ^ s)).filter P).length := by
  induction b, Nat.succ_le_iff.mpr hb using Nat.le_induction generalizing L P with
  | base =>
    simp_all +decide only [Nat.succ_eq_add_one, zero_add, one_mul, exists_and_left]
    rcases L with ( _ | ⟨ x, _ | ⟨ y, L ⟩ ⟩ ) <;>
      simp_all +arith +decide only [List.length_nil, pow_one, zero_le, nonpos_iff_eq_zero,
        List.filter_nil, List.take_nil, List.drop_nil, le_refl, and_true, exists_eq_left,
        List.length_cons, zero_add, Nat.one_le_ofNat, Order.add_one_le_iff,
        List.length_eq_zero_iff, Nat.reduceAdd];
    · exact ⟨ 1, by norm_num, 0, by norm_num, by norm_num, by cases P x <;> simp +decide ⟩;
    · rw [ List.filter_cons, List.filter_cons ] ; aesop;
  | succ b hb ih =>
    simp_all +decide only [Nat.succ_eq_add_one, zero_add, exists_and_left, forall_const,
      le_add_iff_nonneg_left, zero_le, pow_succ']
    -- Consider two cases: $L.length \leq 2^b$ and $2^b < L.length \leq 2^{b+1}$.
    by_cases h_case : L.length ≤ 2^b;
    · obtain ⟨ M, hM₁, x, hx₁, hx₂, hx₃ ⟩ :=
        ih L P h_case; exact ⟨ M, hM₁, x, Nat.le_succ_of_le hx₁, hx₂, by nlinarith ⟩ ;
    · obtain ⟨M', s', hM's', hs', hM's'_mod, hM's'_bound⟩ : ∃ M' s',
        M' ≤ L.length - 2^b ∧ s' ≤ b ∧ M' % 2^s' = 0 ∧
          ((List.filter P (L.drop (2^b))).length ≤
            b * ((List.filter P ((L.drop (2^b)).take M' |>.drop
              (M' - 2^s'))).length)) := by
        specialize ih (L.drop (2^b)) P (by
        grind);
        aesop;
      by_cases h_case2 : (b + 1) * ((List.filter P (L.take (2^b))).length) ≥ (List.filter P
          L).length;
      · refine ⟨ 2 ^ b, ?_, b, ?_, ?_, ?_ ⟩ <;> norm_num;
        · linarith;
        · lia;
      · refine ⟨ 2 ^ b + M', ?_, s', ?_, ?_, ?_ ⟩ <;> try omega;
        · exact Nat.mod_eq_zero_of_dvd ( dvd_add ( pow_dvd_pow _ hs' )
            ( Nat.dvd_of_mod_eq_zero hM's'_mod ) );
        · rw [ show List.take ( 2 ^ b + M' ) L =
            List.take ( 2 ^ b ) L ++ List.take M' ( List.drop ( 2 ^ b ) L ) from ?_,
            show List.drop ( 2 ^ b + M' - 2 ^ s' ) ( List.take ( 2 ^ b ) L ++
              List.take M' ( List.drop ( 2 ^ b ) L ) ) = List.drop ( M' - 2 ^ s' ) (
                List.take M' ( List.drop ( 2 ^ b ) L ) ) from ?_ ];
          · have h_filter_decomp : List.filter P L =
                List.filter P ( List.take ( 2 ^ b ) L ) ++
                  List.filter P ( List.drop ( 2 ^ b ) L ) := by
              rw [ ← List.filter_append, List.take_append_drop ]
            rw [ h_filter_decomp ]
            rw [ h_filter_decomp ] at h_case2
            norm_num at *
            nlinarith
          · rw [ Nat.add_sub_assoc ];
            · rw [ List.drop_append ];
              rw [ List.drop_eq_nil_of_le ] <;> norm_num;
              grind;
            · by_cases hM'_zero : M' = 0;
              · rw [ show List.filter P L = List.filter P ( List.take ( 2 ^ b ) L ) from ?_ ]
                  at h_case2;
                · nlinarith;
                · rw [ ← List.take_append_drop ( 2 ^ b ) L, List.filter_append ] ; aesop;
              · exact Nat.le_of_dvd ( Nat.pos_of_ne_zero hM'_zero )
                  ( Nat.dvd_of_mod_eq_zero hM's'_mod );
          · rw [ List.take_add ]

/-- If a list of at most `2 ^ (i + 1)` entries has `2 ^ k` entries satisfying `P`, then some
dyadic block of it contains at least `selectionThreshold i k` of them. -/
theorem dyadic_block_of_many_positions {α : Type} (L : List α) (P : α → Bool)
    (i k : ℕ) (hL : L.length ≤ 2 ^ (i + 1)) (hP : 2 ^ k ≤ (L.filter P).length) :
    ∃ M s, M ≤ L.length ∧ s ≤ i + 1 ∧ M % 2 ^ s = 0 ∧
      selectionThreshold i k ≤ (((L.take M).drop (M - 2 ^ s)).filter P).length := by
  obtain ⟨M, s, hM, hs, hmod, hcount⟩ :=
    dyadic_core (i + 1) (Nat.le_add_left 1 i) L P hL
  exact ⟨M, s, hM, hs, hmod,
    selectionThreshold_le_of_pow_le i k _ (le_trans hP hcount)⟩

/-- A string with `2 ^ k` descriptions among the stage codes has one among the selected models. -/
theorem selectionStrategyOnline_covers_of_list (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k t : ℕ) :
    ∀ x : BitString, x.length = n →
      2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card →
      ∃ w ∈ selectionStrategyOnline n i j k (familyStageModelCodesList c i 𝒜 j t),
        IsFamilyDescriptionCode 𝒜 j x w := by
  intro x hxlen hcount
  set S := familyStageModelCodesList c i 𝒜 j t with hS
  let P :=
      fun (w : BitString) =>
          decide (x ∈ canonicalFinsetList (((decodeDistributionData w).map
            CodedDistributionEntry.point).toFinset))
  have hSlen : S.length ≤ 2 ^ (i + 1) := by
    rw [hS]
    exact familyStageModelCodesList_length_le c i 𝒜 j t
  have hP : 2 ^ k ≤ (S.filter P).length := by
    have hsub :
        familyStageDescriptionCodes c i 𝒜 j t x ⊆ (S.filter P).toFinset := by
      intro w hw
      obtain ⟨hwS, hcover⟩ :=
        mem_familyStageModelCodesList_and_cover_of_description c i 𝒜 j t x w hw
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨by simpa [hS] using hwS, decide_eq_true hcover⟩
    have hcard_le :
        (familyStageDescriptionCodes c i 𝒜 j t x).card ≤ (S.filter P).toFinset.card :=
      Finset.card_le_card hsub
    exact hcount.trans (hcard_le.trans (List.toFinset_card_le _))
  obtain ⟨M, s, hM, hs, hmod, hthresh⟩ := dyadic_block_of_many_positions S P i k hSlen hP
  have hM_pos : 0 < M := by
    by_contra h0
    have : M = 0 := by omega
    subst this
    simp at hthresh
    have := selectionThreshold_pos i k
    omega
  set m_idx := M - 1
  have hM_eq : M = m_idx + 1 := by omega
  have hthresh2 : selectionThreshold i k ≤ (((S.take (m_idx + 1)).drop ((m_idx + 1) - 2 ^
      s)).filter P).length := by
    rwa [← hM_eq]
  have hsel : 0 < ((blockSelection n i j k s ((S.take (m_idx + 1)).drop ((m_idx + 1) - 2 ^
      s))).filter P).length := by
    exact blockSelection_covers_of_count n i j k s _ x hxlen hthresh2
  obtain ⟨w, hw⟩ := List.length_pos_iff_exists_mem.mp hsel
  rw [List.mem_filter] at hw
  refine ⟨w, ?_, ?_⟩
  · unfold selectionStrategyOnline
    rw [List.mem_flatMap]
    refine ⟨m_idx, ?_, ?_⟩
    · rw [List.mem_range]
      omega
    · rw [List.mem_flatMap]
      refine ⟨s, ?_, hw.1⟩
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [List.mem_range]
        omega
      · have heq : (m_idx + 1) % 2 ^ s = 0 := by
          rwa [← hM_eq]
        exact decide_eq_true heq
  · have hsub := blockSelection_sublist n i j k s ((S.take (m_idx + 1)).drop ((m_idx + 1) - 2 ^ s))
    have hwS : w ∈ ((S.take (m_idx + 1)).drop ((m_idx + 1) - 2 ^ s)) := hsub.subset hw.1
    have hwS2 : w ∈ S := List.mem_of_mem_take (List.mem_of_mem_drop hwS)
    have hmodel : IsFamilyModelCode 𝒜 j w := by
      rw [hS] at hwS2
      exact familyStageModelCodesList_sound c i 𝒜 j t w hwS2
    exact isFamilyDescriptionCode_of_model_cover 𝒜 j x w hmodel (decide_eq_true_eq.mp hw.2)

/-- The marked stream has at most `(i + 2)(i + 1)(n + 1) 2 ^ (i + 1 - k)` entries. -/
theorem familyMarkedCodeStream_length_bound (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k t : ℕ) :
  (familyMarkedCodeStream c i 𝒜 n j k t).length ≤ (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 -
      k) := by
  unfold familyMarkedCodeStream
  apply selectionStrategyOnline_length_bound_of_le
  exact familyStageModelCodesList_length_le c i 𝒜 j t

/-- Every string with `2 ^ k` descriptions at stage `t` has one in the marked stream. -/
theorem familyMarkedCodeStream_covers (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (n j k t : ℕ) :
  ∀ x : BitString, x.length = n →
    2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card →
    ∃ w ∈ familyMarkedCodeStream c i 𝒜 n j k t, IsFamilyDescriptionCode 𝒜 j x w := by
  intro x hxlen hmany
  unfold familyMarkedCodeStream
  exact selectionStrategyOnline_covers_of_list c i 𝒜 n j k t x hxlen hmany

end Kolmogorov
