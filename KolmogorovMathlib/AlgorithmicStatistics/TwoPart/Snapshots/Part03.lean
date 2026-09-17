import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Part02

/-!
# Emitted chunks of the snapshot: counting

`emittedHalfRichChunks_length_le`: the snapshot emits at most `2 ^ (i - k + 3)` chunks.  Full
chunks are counted by their size; the work is bounding the *non-full* ones, which is
`emittedHalfRichChunks_nonfull_count_le`.

The argument charges each non-full chunk to a fresh element:
`nonfullChunkEmissionTime_strict_mono` orders their emission times,
`nonfullChunkTrigger_not_halfrich_prev` and `nonfullChunkTrigger_rich_curr` identify the
element that triggered one, and `nonfull_chunk_fresh_descriptions` shows two consecutive
non-full chunks are separated by an element that becomes half-rich in between, of which there
are at most `2 ^ (i - k + O(1))`.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Folding the chunk-building step over a list of half-rich elements creates at most one new
non-full chunk, and if it does create one then every half-rich element has been emitted. -/
theorem emittedHalfRichChunks_foldStep_nonfull_count (j : ℕ) (half_rich : List BitString)
    (L : List BitString) (acc : List (List BitString)) (hL : ∀ x ∈ L, x ∈ half_rich) :
    ((L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).filter
        (fun l => l.length < 2 ^ j)).length
      ≤ (acc.filter (fun l => l.length < 2 ^ j)).length + 1
    ∧ ((acc.filter (fun l => l.length < 2 ^ j)).length + 1
        ≤ ((L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).filter
            (fun l => l.length < 2 ^ j)).length
      → ∀ y ∈ half_rich,
          y ∈ (L.foldl (emittedHalfRichChunksFoldStep j half_rich) acc).flatten) := by
  induction L using List.reverseRecOn generalizing acc with
  | nil => simp_all +decide
  | append_singleton L x ih =>
      have hL' : ∀ y ∈ L, y ∈ half_rich := by
        intro y hy
        exact hL y (List.mem_append.mpr (Or.inl hy))
      have hx_half : x ∈ half_rich :=
        hL x (List.mem_append.mpr (Or.inr (List.mem_singleton_self x)))
      let prev := List.foldl (emittedHalfRichChunksFoldStep j half_rich) acc L
      have ih' := ih acc hL'
      change
        ((prev.filter (fun l => l.length < 2 ^ j)).length ≤
          (acc.filter (fun l => l.length < 2 ^ j)).length + 1) ∧
        ((acc.filter (fun l => l.length < 2 ^ j)).length + 1 ≤
            (prev.filter (fun l => l.length < 2 ^ j)).length →
          ∀ y ∈ half_rich, y ∈ prev.flatten) at ih'
      by_cases hx_prev : x ∈ prev.flatten
      · have hdec : decide (x ∈ prev.flatten) = true := decide_eq_true hx_prev
        simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
          emittedHalfRichChunksFoldStep, prev, hdec, cond_true] using ih'
      · have hdec : decide (x ∈ prev.flatten) = false := decide_eq_false hx_prev
        let unplaced := half_rich.filter (fun y =>
          bif decide (y ∈ prev.flatten) then false else true)
        let base := x :: unplaced.filter (fun y =>
          bif decide (y = x) then false else true)
        let newChunk := base.take (2 ^ j)
        have hstep : emittedHalfRichChunksFoldStep j half_rich prev x =
            prev ++ [newChunk] := by
          simp only [emittedHalfRichChunksFoldStep, hdec, cond_false, unplaced,
            base, newChunk]
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hstep]
        by_cases hnew : newChunk.length < 2 ^ j
        · have hprev_le : (prev.filter (fun l => l.length < 2 ^ j)).length ≤
              (acc.filter (fun l => l.length < 2 ^ j)).length := by
            apply Nat.le_of_not_gt
            intro hinc
            exact hx_prev (ih'.2 (by omega) x hx_half)
          have hcount :
              ((prev ++ [newChunk]).filter (fun l => l.length < 2 ^ j)).length =
                (prev.filter (fun l => l.length < 2 ^ j)).length + 1 := by
            simp +decide [hnew]
          constructor
          · rw [hcount]
            exact Nat.add_le_add_right hprev_le 1
          · intro _ y hy
            by_cases hy_prev : y ∈ prev.flatten
            · simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
                List.append_nil, List.mem_append] using Or.inl hy_prev
            · have hbase_le : base.length ≤ 2 ^ j := by
                simp only [newChunk, List.length_take] at hnew
                omega
              have hy_base : y ∈ base := by
                by_cases hyx : y = x
                · exact List.mem_cons.mpr (Or.inl hyx)
                · apply List.mem_cons.mpr
                  apply Or.inr
                  apply List.mem_filter.mpr
                  refine ⟨?_, ?_⟩
                  · apply List.mem_filter.mpr
                    refine ⟨hy, ?_⟩
                    rw [decide_eq_false hy_prev]
                    exact rfl
                  · rw [decide_eq_false hyx]
                    exact rfl
              have hy_new : y ∈ newChunk := by
                simpa only [newChunk, List.take_of_length_le hbase_le] using hy_base
              simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
                List.append_nil, List.mem_append] using Or.inr hy_new
        · have hcount :
              ((prev ++ [newChunk]).filter (fun l => l.length < 2 ^ j)).length =
                (prev.filter (fun l => l.length < 2 ^ j)).length := by
            simp +decide [hnew]
          constructor
          · rw [hcount]
            exact ih'.1
          · intro hinc y hy
            rw [hcount] at hinc
            have hy_prev := ih'.2 hinc y hy
            simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil, List.mem_append] using Or.inl hy_prev

/-
A single online time step appends at most one nonfull chunk.
-/
theorem emittedHalfRichChunksList_numNonfull_succ_le (c : Code) (i j k t : ℕ) :
    ((emittedHalfRichChunksList c i j k (t + 1)).filter (fun l => l.length < 2 ^ j)).length
      ≤ ((emittedHalfRichChunksList c i j k t).filter (fun l => l.length < 2 ^ j)).length + 1 := by
  have hsubset : ∀ x ∈ (snapshotRichElementsList c i j k (t + 1)).eraseDups,
      x ∈ (snapshotRichElementsList c i j (k - 1) (t + 1)).eraseDups := by
    intro x hx
    apply mem_eraseDups_iff.mpr
    exact snapshotRichElementsList_subset_threshold c i j (t + 1)
      (Nat.sub_le k 1) (mem_eraseDups_iff.mp hx)
  simpa [emittedHalfRichChunksList, emittedHalfRichChunksStep] using
    (emittedHalfRichChunks_foldStep_nonfull_count j
      ((snapshotRichElementsList c i j (k - 1) (t + 1)).eraseDups)
      ((snapshotRichElementsList c i j k (t + 1)).eraseDups)
      (emittedHalfRichChunksList c i j k t) hsubset).1

/-
At time `0` at most one nonfull chunk exists (the first online step opens at
most one nonfull chunk from the empty accumulator).
-/
theorem emittedHalfRichChunksList_numNonfull_zero_le (c : Code) (i j k : ℕ) :
    ((emittedHalfRichChunksList c i j k 0).filter (fun l => l.length < 2 ^ j)).length ≤ 1 := by
  simp only [emittedHalfRichChunksList, emittedHalfRichChunksStep,
    snapshotRichElementsList_zero, List.eraseDups_nil, List.foldl_nil,
    List.filter_nil, List.length_nil, Nat.zero_le]

/-
The finset-form and list-form counts of nonfull chunks agree.
-/
theorem emittedHalfRich_nonfull_len_eq (c : Code) (i j k t : ℕ) :
    ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length
      = ((emittedHalfRichChunksList c i j k t).filter (fun l => l.length < 2 ^ j)).length := by
  rw [ emittedHalfRichChunks, List.filter_map ];
  rw [ List.length_map, List.filter_congr ];
  intro x hx;
  have := List.Nodup.sublist (List.sublist_flatten_of_mem hx)
    (emittedHalfRichChunksList_flatten_nodup c i j k t);
  simp_all +decide [ List.toFinset_card_of_nodup ];

/-
Emission times of consecutive nonfull chunks are strictly increasing.
-/
theorem nonfullChunkEmissionTime_strict_mono (c : Code) (i j k t m : ℕ)
    (h_lt : m + 1 < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length) :
    nonfullChunkEmissionTime c i j k t m < nonfullChunkEmissionTime c i j k t (m + 1) := by
  -- The final nonfull-chunk list preserves the chronological order of first
  -- emission times, and distinct nonempty chunks cannot first appear at the
  -- same time.
  obtain ⟨l_m, hl_m⟩ : ∃ l_m,
      (List.drop m (List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k t))).head? = some l_m := by
    simp +zetaDelta only [List.head?_drop] at *;
    rw [ emittedHalfRich_nonfull_len_eq ] at h_lt;
    exact ⟨ _, List.getElem?_eq_getElem <| by linarith ⟩;
  obtain ⟨l₁, hl₁⟩ : ∃ l₁,
      (List.drop (m + 1) (List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k t))).head? = some l₁ := by
    simp_all +decide [ emittedHalfRich_nonfull_len_eq ];
  have h_mem_iff_count : ∀ τ ≤ t, l_m ∈ emittedHalfRichChunksList c i j k τ ↔ m <
      ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k τ)).length) := by
    intros τ hτ
    have h_mem_iff_count : l_m ∈ List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k τ) ↔ m <
        ((List.filter (fun l => l.length < 2 ^ j)
          (emittedHalfRichChunksList c i j k τ)).length) := by
      have h_mem_iff_count : List.Nodup
          (List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k t)) := by
        exact List.Nodup.filter _ ( emittedHalfRichChunksList_Nodup c i j k t );
      obtain ⟨rest, hrest⟩ := emittedHalfRichChunksList_filter_prefix c i j k hτ
        (fun l => l.length < 2 ^ j);
      rw [ List.head?_drop ] at hl_m;
      grind;
    simp +zetaDelta at *;
    grind;
  have h_mem_iff_count₁ : ∀ τ ≤ t, l₁ ∈ emittedHalfRichChunksList c i j k τ ↔ m + 1 <
      ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k τ)).length) := by
    intro τ hτ;
    have h_mem_iff_count₁ : l₁ ∈ List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k τ) ↔ m + 1 <
        ((List.filter (fun l => l.length < 2 ^ j)
          (emittedHalfRichChunksList c i j k τ)).length) := by
      have h_mem_iff_count₁ : List.Nodup
          (List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k t)) := by
        exact List.Nodup.filter _ ( emittedHalfRichChunksList_Nodup c i j k t );
      obtain ⟨rest, hrest⟩ := emittedHalfRichChunksList_filter_prefix c i j k hτ
        (fun l => l.length < 2 ^ j);
      rw [ List.head?_drop ] at hl₁;
      grind;
    grind +suggestions;
  obtain ⟨A, hA⟩ : ∃ A, A ≤ t ∧ m <
      ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k A)).length) ∧ ∀ τ
      < A,
      ¬(m < ((List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k τ)).length)) := by
    have h_exists_A : ∃ A ≤ t, m <
        ((List.filter (fun l => l.length < 2 ^ j)
          (emittedHalfRichChunksList c i j k A)).length) := by
      exact ⟨ t, le_rfl, by linarith [ emittedHalfRich_nonfull_len_eq c i j k t ] ⟩;
    exact ⟨Nat.find h_exists_A, Nat.find_spec h_exists_A |>.1,
      Nat.find_spec h_exists_A |>.2, fun τ hτ => fun h =>
        Nat.find_min h_exists_A hτ
          ⟨Nat.le_trans (Nat.le_of_lt hτ) (Nat.find_spec h_exists_A |>.1), h⟩⟩;
  obtain ⟨B, hB⟩ : ∃ B, B ≤ t ∧ m + 1 <
      ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k B)).length) ∧ ∀ τ
      < B,
      ¬(m + 1 < ((List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k τ)).length)) := by
    have hB_exists : ∃ B ≤ t, m + 1 <
        ((List.filter (fun l => l.length < 2 ^ j)
          (emittedHalfRichChunksList c i j k B)).length) := by
      exact ⟨ t, le_rfl, by simpa only [ emittedHalfRich_nonfull_len_eq ] using h_lt ⟩;
    exact ⟨Nat.find hB_exists, Nat.find_spec hB_exists |>.1,
      Nat.find_spec hB_exists |>.2, fun τ hτ => fun h =>
        Nat.find_min hB_exists hτ
          ⟨Nat.le_trans (Nat.le_of_lt hτ) (Nat.find_spec hB_exists |>.1), h⟩⟩;
  have hA_lt_B : A < B := by
    have h_nf_A :
        ((List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k A)).length) ≤ m
        + 1 := by
      rcases A with _ | A
      · exact le_trans (emittedHalfRichChunksList_numNonfull_zero_le c i j k)
          (Nat.succ_le_succ (Nat.zero_le m))
      · exact le_trans (emittedHalfRichChunksList_numNonfull_succ_le c i j k A)
          (Nat.add_le_add_right
            (Nat.le_of_not_gt (hA.2.2 A (Nat.lt_succ_self A))) 1)
    grind;
  unfold nonfullChunkEmissionTime
  dsimp only
  rw [hl_m, hl₁]
  dsimp only
  rw [show List.find? (fun τ => decide (l_m ∈ emittedHalfRichChunksList c i j k τ))
      (List.range (t + 1)) = some A from ?_,
    show List.find? (fun τ => decide (l₁ ∈ emittedHalfRichChunksList c i j k τ))
      (List.range (t + 1)) = some B from ?_];
  · exact hA_lt_B;
  · apply List.find?_range_eq_some.mpr
    refine ⟨decide_eq_true (h_mem_iff_count₁ B hB.1 |>.mpr hB.2.1),
      List.mem_range.mpr (Nat.lt_succ_of_le hB.1), ?_⟩
    intro τ hτ
    have hnot : l₁ ∉ emittedHalfRichChunksList c i j k τ := by
      intro hmem
      exact hB.2.2 τ hτ ((h_mem_iff_count₁ τ (by omega)).mp hmem)
    rw [decide_eq_false hnot]
    exact rfl
  · apply List.find?_range_eq_some.mpr
    refine ⟨decide_eq_true (h_mem_iff_count A hA.1 |>.mpr hA.2.1),
      List.mem_range.mpr (Nat.lt_succ_of_le hA.1), ?_⟩
    intro τ hτ
    have hnot : l_m ∉ emittedHalfRichChunksList c i j k τ := by
      intro hmem
      exact hA.2.2 τ hτ ((h_mem_iff_count τ (by omega)).mp hmem)
    rw [decide_eq_false hnot]
    exact rfl

/-
The trigger of the `m+1`-th nonfull chunk was not half-rich at the emission
time of the `m`-th nonfull chunk.
-/
theorem nonfullChunkTrigger_not_halfrich_prev (c : Code) (i j k t m : ℕ)
    (h_lt : m + 1 < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length) :
    nonfullChunkTrigger c i j k t (m + 1) ∉ snapshotRichElementsList c i j (k - 1)
        (nonfullChunkEmissionTime c i j k t m) := by
  -- A nonfull emission exhausts all currently unplaced half-rich elements, so
  -- the later trigger was not half-rich at the previous nonfull emission time.
  have h_nonfullChunkEmissionTime : nonfullChunkEmissionTime c i j k t m < nonfullChunkEmissionTime
      c i j k t (m + 1) := by
    apply nonfullChunkEmissionTime_strict_mono c i j k t m h_lt;
  have h_nonfullChunkTrigger : ∃ l_m,
      (List.drop m (List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k t))).head? = some l_m ∧
      l_m.length < 2 ^ j ∧ l_m ≠ [] ∧
      l_m ∈ emittedHalfRichChunksList c i j k t := by
    let L := List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k t)
    have hm_lt : m < L.length := by
      rw [show L.length = ((emittedHalfRichChunks c i j k t).filter
          (fun S => S.card < 2 ^ j)).length by
        exact (emittedHalfRich_nonfull_len_eq c i j k t).symm]
      omega
    refine ⟨L[m], ?_, ?_, ?_, ?_⟩
    · rw [List.head?_drop]
      exact List.getElem?_eq_getElem hm_lt
    · exact of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hm_lt)).2
    · exact emittedHalfRichChunksList_mem_ne_nil c i j k t L[m]
        (List.mem_filter.mp (List.getElem_mem hm_lt)).1
    · exact (List.mem_filter.mp (List.getElem_mem hm_lt)).1
  obtain ⟨l_m, hl_m⟩ := h_nonfullChunkTrigger
  obtain ⟨l₁, hl₁⟩ : ∃ l₁,
      (List.drop (m + 1) (List.filter (fun l => l.length < 2 ^ j)
        (emittedHalfRichChunksList c i j k t))).head? = some l₁ ∧
      l₁.length < 2 ^ j ∧ l₁ ≠ [] ∧
      l₁ ∈ emittedHalfRichChunksList c i j k t := by
    let L := List.filter (fun l => l.length < 2 ^ j) (emittedHalfRichChunksList c i j k t)
    have hm1_lt : m + 1 < L.length := by
      rw [show L.length = ((emittedHalfRichChunks c i j k t).filter
          (fun S => S.card < 2 ^ j)).length by
        exact (emittedHalfRich_nonfull_len_eq c i j k t).symm]
      exact h_lt
    refine ⟨L[m + 1], ?_, ?_, ?_, ?_⟩
    · rw [List.head?_drop]
      exact List.getElem?_eq_getElem hm1_lt
    · exact of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hm1_lt)).2
    · exact emittedHalfRichChunksList_mem_ne_nil c i j k t L[m + 1]
        (List.mem_filter.mp (List.getElem_mem hm1_lt)).1
    · exact (List.mem_filter.mp (List.getElem_mem hm1_lt)).1
  have h_l₁_unplaced : ∀ y ∈ l₁, y ∉
      (emittedHalfRichChunksList c i j k (nonfullChunkEmissionTime c i j k t m)).flatten := by
    intros y hy₁ hy₂
    have h_l₁_not_in_chunk : l₁ ∉ emittedHalfRichChunksList c i j k
        (nonfullChunkEmissionTime c i j k t m) := by
      unfold nonfullChunkEmissionTime at *; simp_all +decide ;
      cases h : List.find? (fun τ => decide
          (l₁ ∈ emittedHalfRichChunksList c i j k τ)) (List.range (t + 1))
        <;> simp_all +decide;
    have h_l₁_not_in_chunk : ∃ rest, emittedHalfRichChunksList c i j k t = emittedHalfRichChunksList
        c i j k (nonfullChunkEmissionTime c i j k t m) ++ rest := by
      apply emittedHalfRichChunksList_prefix;
      exact nonfullChunkEmissionTime_le c i j k t m;
    obtain ⟨ rest, hrest ⟩ := h_l₁_not_in_chunk; simp_all +decide [ List.mem_append ] ;
    have h_l₁_not_in_chunk : List.Nodup
        (List.flatten (emittedHalfRichChunksList c i j k
          (nonfullChunkEmissionTime c i j k t m) ++ rest)) := by
      exact hrest ▸ emittedHalfRichChunksList_flatten_nodup c i j k t;
    grind;
  have h_nonfullChunkTrigger_not_in_chunk :
      l_m.toFinset ∈ emittedHalfRichChunks c i j k
        (nonfullChunkEmissionTime c i j k t m) ∧
      (nonfullChunkEmissionTime c i j k t m > 0 →
        l_m.toFinset ∉ emittedHalfRichChunks c i j k
          (nonfullChunkEmissionTime c i j k t m - 1)) ∧
      l_m.toFinset.card < 2 ^ j := by
    have h_nonfullChunkTrigger_not_in_chunk : l_m ∈ emittedHalfRichChunksList c i j k
        (nonfullChunkEmissionTime c i j k t m) ∧
        (nonfullChunkEmissionTime c i j k t m > 0 →
          l_m ∉ emittedHalfRichChunksList c i j k
            (nonfullChunkEmissionTime c i j k t m - 1)) := by
      unfold nonfullChunkEmissionTime at *; simp_all +decide ;
      cases h : List.find? (fun τ => decide
          (l_m ∈ emittedHalfRichChunksList c i j k τ)) (List.range (t + 1))
        <;> simp_all +decide [ List.find?_eq_none ];
    unfold emittedHalfRichChunks;
    simp_all +decide only [List.mem_map, gt_iff_lt, not_exists, not_and];
    refine ⟨ ⟨ l_m, h_nonfullChunkTrigger_not_in_chunk.1, rfl ⟩, ?_, ?_ ⟩;
    · intro h_pos x hx h_eq;
      have h_eq_lists : x = l_m := by
        have h_eq_lists : x ∈ emittedHalfRichChunksList c i j k
            (nonfullChunkEmissionTime c i j k t m) := by
          have := emittedHalfRichChunksList_prefix c i j k
            (Nat.sub_le (nonfullChunkEmissionTime c i j k t m) 1);
          aesop;
        have h_eq_lists : List.Nodup
            (List.map List.toFinset (emittedHalfRichChunksList c i j k
              (nonfullChunkEmissionTime c i j k t m))) := by
          exact emittedHalfRichChunks_nodup c i j k ( nonfullChunkEmissionTime c i j k t m );
        rw [ List.nodup_map_iff_inj_on ] at h_eq_lists;
        · exact h_eq_lists x ‹_› l_m h_nonfullChunkTrigger_not_in_chunk.1 h_eq;
        · exact emittedHalfRichChunksList_Nodup c i j k (nonfullChunkEmissionTime c i j k t m);
      grind;
    · exact lt_of_le_of_lt ( List.toFinset_card_le _ ) hl_m.2.1;
  have := nonfull_chunk_emit_time c i j k
    (nonfullChunkEmissionTime c i j k t m) l_m.toFinset
    h_nonfullChunkTrigger_not_in_chunk.1 h_nonfullChunkTrigger_not_in_chunk.2.1
    h_nonfullChunkTrigger_not_in_chunk.2.2;
  unfold nonfullChunkTrigger
  dsimp only
  rw [hl₁.1]
  cases l₁ with
  | nil => exact (hl₁.2.2.1 rfl).elim
  | cons y ys =>
      intro hy
      exact h_l₁_unplaced y (List.mem_cons_self)
        (this y hy)

/-
The trigger of a nonfull chunk is rich at its emission time.
-/
theorem nonfullChunkTrigger_rich_curr (c : Code) (i j k t m : ℕ)
    (h_lt : m < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length) :
    nonfullChunkTrigger c i j k t m ∈ snapshotRichElementsList c i j k
        (nonfullChunkEmissionTime c i j k t m) := by
  -- The head of an emitted chunk is exactly the rich trigger element that
  -- caused that chunk to be opened.
  let L := (emittedHalfRichChunksList c i j k t).filter (fun l => l.length < 2 ^ j)
  have hm_lt : m < L.length := by
    rw [← emittedHalfRich_nonfull_len_eq c i j k t]
    exact h_lt
  let l := L[m]
  have hl_mem : l ∈ L := List.getElem_mem hm_lt
  have hl_drop : l ∈ L.drop m := by
    rw [List.mem_iff_getElem]
    exact ⟨0, by simpa [l]⟩
  have hl_ne : l ≠ [] := by
    apply emittedHalfRichChunksList_mem_ne_nil c i j k t
    exact (List.mem_filter.mp hl_mem).1
  have hl_head : (L.drop m).head? = some l := by
    rw [List.head?_drop]
    exact List.getElem?_eq_getElem hm_lt
  have hl : l ∈ L.drop m ∧ l ≠ [] ∧ (L.drop m).head? = some l :=
    ⟨hl_drop, hl_ne, hl_head⟩
  obtain ⟨τ, hτ⟩ : ∃ τ ∈ List.range (t + 1),
      l ∈ emittedHalfRichChunksList c i j k τ ∧
        ∀ τ' < τ, l ∉ emittedHalfRichChunksList c i j k τ' := by
    have h_exists_τ : ∃ τ ∈ List.range (t + 1),
        l ∈ emittedHalfRichChunksList c i j k τ := by
      exact ⟨t, List.mem_range.mpr (Nat.lt_succ_self t),
        List.mem_of_mem_filter (List.mem_of_mem_drop hl.1)⟩
    refine ⟨Nat.find h_exists_τ, (Nat.find_spec h_exists_τ).1,
      (Nat.find_spec h_exists_τ).2, ?_⟩
    intro τ' hτ' hmem
    apply Nat.find_min h_exists_τ hτ'
    exact ⟨List.mem_range.mpr (by
      linarith [List.mem_range.mp (Nat.find_spec h_exists_τ).1]), hmem⟩
  have h_l_head : ∃ x ∈ (snapshotRichElementsList c i j k τ).eraseDups,
      l ≠ [] ∧ l.head? = some x := by
    have h_l_head : ∀ {L : List BitString} {acc : List (List BitString)}, l ∈ List.foldl
        (emittedHalfRichChunksFoldStep j ((snapshotRichElementsList c i j (k - 1) τ).eraseDups))
        acc L → l ∉ acc → ∃ x ∈ L, l ≠ [] ∧ l.head? = some x := by
      intros L acc hl hacc
      induction L using List.reverseRecOn generalizing acc with
      | nil => exact (hacc hl).elim
      | append_singleton L x ih =>
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hl
          let acc' := List.foldl (emittedHalfRichChunksFoldStep j
            (snapshotRichElementsList c i j (k - 1) τ).eraseDups) acc L
          change l ∈ emittedHalfRichChunksFoldStep j
            (snapshotRichElementsList c i j (k - 1) τ).eraseDups acc' x at hl
          by_cases hx : x ∈ acc'.flatten
          · have hdec : decide (x ∈ acc'.flatten) = true := decide_eq_true hx
            simp only [emittedHalfRichChunksFoldStep, hdec, cond_true] at hl
            obtain ⟨y, hy, hne, hhead⟩ := ih hl hacc
            exact ⟨y, List.mem_append.mpr (Or.inl hy), hne, hhead⟩
          · have hdec : decide (x ∈ acc'.flatten) = false := decide_eq_false hx
            simp only [emittedHalfRichChunksFoldStep, hdec, cond_false,
              List.mem_append, List.mem_singleton] at hl
            rcases hl with hl | hl
            · obtain ⟨y, hy, hne, hhead⟩ := ih hl hacc
              exact ⟨y, List.mem_append.mpr (Or.inl hy), hne, hhead⟩
            · rw [hl]
              obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero
                (Nat.ne_of_gt (pow_pos (by omega : 0 < 2) j))
              refine ⟨x, List.mem_append.mpr (Or.inr (List.mem_singleton_self x)), ?_, ?_⟩
              · rw [hq, List.take_succ_cons]
                exact List.cons_ne_nil x _
              · simp only [hq, List.take_succ_cons, List.head?_cons]
    rcases τ with _ | τ
    · have : l ∈ ([] : List (List BitString)) := by
        simpa only [emittedHalfRichChunksList, emittedHalfRichChunksStep,
          snapshotRichElementsList_zero, List.eraseDups_nil, List.foldl_nil]
          using hτ.2.1
      exact (List.not_mem_nil this).elim
    · exact h_l_head hτ.2.1 (hτ.2.2 τ (Nat.lt_succ_self τ))
  obtain ⟨x, hx⟩ := h_l_head
  have hx_rich : x ∈ snapshotRichElementsList c i j k τ := by
    have h_eraseDups : ∀ {L : List BitString}, x ∈ L.eraseDups → x ∈ L := by
      intros L hL; induction L using List.reverseRecOn
      case' nil => simp_all +decide
      case' append_singleton L ih _ => simp_all +decide [ List.eraseDups_append ]
      simp_all +decide [ List.removeAll ];
      grind;
    exact h_eraseDups hx.1;
  simp only [nonfullChunkTrigger, nonfullChunkEmissionTime]
  change (match (L.drop m).head? with
    | none => []
    | some [] => []
    | some (x :: _) => x) ∈
      snapshotRichElementsList c i j k
        (match (L.drop m).head? with
        | none => 0
        | some l => (List.find? (fun τ => decide
            (l ∈ emittedHalfRichChunksList c i j k τ)) (List.range (t + 1))).getD 0)
  rw [hl_head]
  simp only
  rw [show List.find? (fun τ => decide (l ∈ emittedHalfRichChunksList c i j k τ))
      (List.range (t + 1)) = some τ from ?_]
  · cases hcase : l with
    | nil => exact (hl_ne hcase).elim
    | cons a tail =>
      have hax : a = x := by simpa [hcase] using hx.2.2
      simpa [hax] using hx_rich
  · apply List.find?_range_eq_some.mpr
    refine ⟨decide_eq_true hτ.2.1, hτ.1, ?_⟩
    intro τ' hτ'
    have hnot := hτ.2.2 τ' hτ'
    rw [decide_eq_false hnot]
    exact rfl

/-- Strictly-monotone emission times give a plain monotonicity: for `a < b` both
below the number of nonfull chunks, `τ a < τ b`. -/
theorem nonfullChunkEmissionTime_lt_of_lt (c : Code) (i j k t : ℕ) {a : ℕ} : ∀ {b : ℕ},
    a < b →
    b < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length →
    nonfullChunkEmissionTime c i j k t a < nonfullChunkEmissionTime c i j k t b
  | 0, hab, _ => absurd hab (by omega)
  | n + 1, hab, hb => by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hab) with h' | h'
    · exact lt_trans (nonfullChunkEmissionTime_lt_of_lt c i j k t h' (by omega))
        (nonfullChunkEmissionTime_strict_mono c i j k t n (by omega))
    · subst h'
      exact nonfullChunkEmissionTime_strict_mono c i j k t a (by omega)

/-- Weak monotonicity of nonfull-chunk emission times. -/
theorem nonfullChunkEmissionTime_mono (c : Code) (i j k t : ℕ) {a b : ℕ}
    (hab : a ≤ b)
    (hb : b < ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length) :
    nonfullChunkEmissionTime c i j k t a ≤ nonfullChunkEmissionTime c i j k t b := by
  rcases lt_or_eq_of_le hab with h | h
  · exact le_of_lt (nonfullChunkEmissionTime_lt_of_lt c i j k t h hb)
  · exact le_of_eq (by rw [h])

/-- Between any two non-full chunks, there is at least one trigger element that
moves from not-half-rich to rich, requiring 2^(k-1) fresh descriptions on
disjoint time intervals.

Assembled from the indexed helpers: each nonfull chunk `m` (index `< F`) has a
trigger `y m` that is not half-rich at the *previous* nonfull emission time
`prevT m` but is rich at its own emission time `τ m`.  By
`trigger_gains_fresh_finset` this forces at least `2 ^ (k-1)` descriptions
containing `y m` to be *fresh* on the interval `(prevT m, τ m]`.  Strict
monotonicity of the emission times makes these fresh sets pairwise disjoint and
all contained in the final description universe, so the count multiplies out. -/
theorem nonfull_chunk_fresh_descriptions (c : Code) (i j k : ℕ) (t : ℕ) :
    ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length * 2 ^ (k - 1) ≤
      (snapshotDescList c i j t).length := by
  rw [snapshotDescList_length_eq_card]
  set F := ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length with hF
  -- The fresh-description finset charged to the `m`-th nonfull chunk.
  let D : ℕ → Finset (Finset BitString) := fun m =>
    (snapshotDescriptionsAndSizeLe c i j (nonfullChunkEmissionTime c i j k t m)).filter
        (fun s => nonfullChunkTrigger c i j k t m ∈ s) \
      (snapshotDescriptionsAndSizeLe c i j
        (if m = 0 then 0 else nonfullChunkEmissionTime c i j k t (m - 1))).filter
        (fun s => nonfullChunkTrigger c i j k t m ∈ s)
  have hDm : ∀ m, D m =
      (snapshotDescriptionsAndSizeLe c i j (nonfullChunkEmissionTime c i j k t m)).filter
          (fun s => nonfullChunkTrigger c i j k t m ∈ s) \
        (snapshotDescriptionsAndSizeLe c i j
          (if m = 0 then 0 else nonfullChunkEmissionTime c i j k t (m - 1))).filter
          (fun s => nonfullChunkTrigger c i j k t m ∈ s) := fun m => rfl
  -- Lower bound: each charged finset has at least `2 ^ (k-1)` elements.
  have lower : ∀ m ∈ Finset.range F, 2 ^ (k - 1) ≤ (D m).card := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [hDm m]
    by_cases hm0 : m = 0
    · subst hm0
      simp only
      refine trigger_gains_fresh_finset c i j k 0 (nonfullChunkEmissionTime c i j k t 0)
        _ ?_ (nonfullChunkTrigger_rich_curr c i j k t 0 (by omega))
      rw [snapshotRichElementsList_zero]
      simp
    · rw [if_neg hm0]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      exact trigger_gains_fresh_finset c i j k (nonfullChunkEmissionTime c i j k t m')
        (nonfullChunkEmissionTime c i j k t (m' + 1))
        _ (nonfullChunkTrigger_not_halfrich_prev c i j k t m' (by omega))
        (nonfullChunkTrigger_rich_curr c i j k t (m' + 1) (by omega))
  -- Core disjointness for `p < q`: a fresh description of chunk `q` cannot already
  -- be present at `τ p ≤ τ (q-1) = prevT q`.
  have key : ∀ p q, p < F → q < F → p < q → Disjoint (D p) (D q) := by
    intro p q _ hq hpq
    rw [Finset.disjoint_left]
    intro s hsp hsq
    rw [hDm p, Finset.mem_sdiff, Finset.mem_filter] at hsp
    rw [hDm q, Finset.mem_sdiff] at hsq
    obtain ⟨⟨hsp_mem, _⟩, _⟩ := hsp
    obtain ⟨hsq_mem, hsq_not⟩ := hsq
    rw [Finset.mem_filter] at hsq_mem
    apply hsq_not
    rw [Finset.mem_filter]
    refine ⟨?_, hsq_mem.2⟩
    have hq0 : q ≠ 0 := by omega
    rw [if_neg hq0]
    refine snapshotDescriptionsAndSizeLe_subset_of_le c i j ?_ hsp_mem
    exact nonfullChunkEmissionTime_mono c i j k t (by omega) (by omega)
  -- The charged finsets are pairwise disjoint.
  have disjoint : (↑(Finset.range F) : Set ℕ).PairwiseDisjoint D := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    change Disjoint (D a) (D b)
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact key a b ha hb hlt
    · exact (key b a hb ha hlt).symm
  -- Every charged finset lives in the final description universe.
  have subset : ∀ m ∈ Finset.range F,
      D m ⊆ snapshotDescriptionsAndSizeLe c i j t := by
    intro m _ s hs
    rw [hDm m, Finset.mem_sdiff] at hs
    obtain ⟨hs_mem, _⟩ := hs
    rw [Finset.mem_filter] at hs_mem
    exact snapshotDescriptionsAndSizeLe_subset_of_le c i j
      (nonfullChunkEmissionTime_le c i j k t m) hs_mem.1
  calc F * 2 ^ (k - 1)
      = ∑ _m ∈ Finset.range F, 2 ^ (k - 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ∑ m ∈ Finset.range F, (D m).card := Finset.sum_le_sum lower
    _ = ((Finset.range F).biUnion D).card := (Finset.card_biUnion disjoint).symm
    _ ≤ (snapshotDescriptionsAndSizeLe c i j t).card := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_biUnion] at hs
        obtain ⟨m, hm, hsm⟩ := hs
        exact subset m hm hsm

/-- Non-full chunks are bounded by the number of fresh occurrences needed,
`<= 2^(i - k + O(1))`. -/
theorem emittedHalfRichChunks_nonfull_count_le (U : Map) (c : Code) (_hc : IsCodeFor c U)
    (i j k : ℕ) (t : ℕ) :
    ((emittedHalfRichChunks c i j k t).filter
      (fun S => S.card < 2 ^ j)).length ≤ 2 ^ (i - k + 2) := by
  have hfresh := nonfull_chunk_fresh_descriptions c i j k t
  have hlen := snapshotDescList_length_le c i j t
  set F := ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length
  have h1 : F * 2 ^ (k - 1) ≤ 2 ^ (i + 1) := le_trans hfresh hlen
  have h2 : F * 2 ^ (k - 1) ≤ 2 ^ (i - k + 2) * 2 ^ (k - 1) := by
    refine le_trans h1 ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

/-- The total number of chunks is bounded by `2^(i - k + 3)`. -/
theorem emittedHalfRichChunks_length_le (U : Map) (c : Code) (hc : IsCodeFor c U) (i j k : ℕ)
    (t : ℕ) :
    (emittedHalfRichChunks c i j k t).length ≤ 2 ^ (i - k + 3) := by
  have hfull := emittedHalfRichChunks_full_count_le U c hc i j k t
  have hnonfull := emittedHalfRichChunks_nonfull_count_le U c hc i j k t
  have hlen : (emittedHalfRichChunks c i j k t).length =
      ((emittedHalfRichChunks c i j k t).filter (fun S => S.card = 2 ^ j)).length +
      ((emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j)).length := by
    -- Every chunk has card ≤ 2^j, so `card < 2^j` is exactly the negation of `card = 2^j`;
    -- the two filters therefore partition the list.
    have hcong : (emittedHalfRichChunks c i j k t).filter (fun S => !decide (S.card = 2 ^ j))
        = (emittedHalfRichChunks c i j k t).filter (fun S => S.card < 2 ^ j) := by
      apply List.filter_congr
      intro S hS
      have hSle := emittedHalfRichChunks_card_le c i j k t S hS
      have hiff : (S.card < 2 ^ j) ↔ ¬ (S.card = 2 ^ j) := by omega
      simp [hiff]
    rw [List.length_eq_length_filter_add (l := emittedHalfRichChunks c i j k t)
      (fun S => decide (S.card = 2 ^ j))]
    congr 1
    exact congrArg List.length hcong
  rw [hlen]
  have hp : (2 : ℕ) ^ (i - k + 3) = 2 ^ (i - k + 2) + 2 ^ (i - k + 2) := by
    rw [pow_succ 2 (i - k + 2), mul_two]
  omega

/-- Given `i, j, k, h`, run the online stream until the `h`-th chunk is emitted
and output its canonical uniform code. -/
noncomputable def onlineHalfRichChunkSelectorFn (c : Code) : BitString →. BitString :=
  fun s =>
    let i := selNat s
    let j := selAlpha s
    let k := selMaxK s
    let h := selH s
    (Nat.rfind (fun t => Part.some
      (decide (h < (emittedHalfRichChunksList c i j k t).length)))).bind
      (fun t =>
        let chunks := emittedHalfRichChunksList c i j k t
        Part.some (match chunks.drop h with
          | [] => []
          | S :: _ =>
            codedDistributionDataCode
              ((canonicalFinsetList S.toFinset).map fun x =>
                { point := x,
                  mass := ratMassInvNat
                    (max 1 (canonicalFinsetList S.toFinset).length) (by positivity) })))

/-
The output body of the online chunk selector, as a function of the input
bitstring `s` and the discovered time `t`, is primitive recursive.  This is the
deterministic post-`rfind` computation: read the parameters off `s`, run the
stream to time `t`, drop the first `h` chunks, and emit the canonical-uniform
code of the head chunk (or the empty string if no chunk is present).
-/
theorem onlineHalfRichChunkBody_primrec (c : Code) :
    Primrec (fun p : BitString × ℕ =>
      (match (emittedHalfRichChunksList c (selNat p.1) (selAlpha p.1)
        (selMaxK p.1) p.2).drop (selH p.1) with
        | [] => ([] : BitString)
        | S :: _ =>
          codedDistributionDataCode ((canonicalFinsetList S.toFinset).map fun x =>
            { point := x,
              mass := ratMassInvNat
                (max 1 (canonicalFinsetList S.toFinset).length) (by positivity) }))) := by
  have h_list_drop_primrec : Primrec
      (fun p : BitString × ℕ => List.drop (selH p.1)
        (emittedHalfRichChunksList c (selNat p.1) (selAlpha p.1)
          (selMaxK p.1) p.2)) := by
    have h_index : Primrec (fun p : BitString × ℕ => selH p.1) :=
      selH_primrec.comp Primrec.fst
    have h_args : Primrec
        (fun p : BitString × ℕ => (selNat p.1, selAlpha p.1, selMaxK p.1, p.2)) :=
      Primrec.pair (selNat_primrec.comp Primrec.fst)
        (Primrec.pair (selAlpha_primrec.comp Primrec.fst)
          (Primrec.pair (selMaxK_primrec.comp Primrec.fst) Primrec.snd))
    have h_nestedArgs : Primrec
        (fun p : ℕ × ℕ × ℕ × ℕ => (((p.1, p.2.1), p.2.2.1), p.2.2.2)) :=
      Primrec.pair
        (Primrec.pair
          (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have h_chunks : Primrec
        (fun p : ℕ × ℕ × ℕ × ℕ =>
          emittedHalfRichChunksList c p.1 p.2.1 p.2.2.1 p.2.2.2) :=
      ((emittedHalfRichChunksList_primrec c).comp h_nestedArgs).of_eq (fun _ => rfl)
    exact KraftChaitin.drop_primrec.comp (h_chunks.comp h_args) h_index
  have h_cons : Primrec₂ (fun (_ : BitString × ℕ)
      (q : List BitString × List (List BitString)) =>
      codedDistributionDataCode
        ((canonicalFinsetList q.1.toFinset).map fun x =>
          { point := x,
            mass := ratMassInvNat
              (max 1 (canonicalFinsetList q.1.toFinset).length) (by positivity) })) :=
    ((codedUniformEncoder_primrec.comp
      (canonicalFinsetList_toFinset_primrec.comp
        (Primrec.fst.comp Primrec.snd))).of_eq (fun _ => rfl)).to₂
  exact (Primrec.list_casesOn h_list_drop_primrec (Primrec.const []) h_cons).of_eq
    (fun p => by
      cases List.drop (selH p.1) (emittedHalfRichChunksList c (selNat p.1)
        (selAlpha p.1) (selMaxK p.1) p.2) <;> rfl)

/-- The online selector of half-rich chunks is partial recursive. -/
theorem partrec_onlineHalfRichChunkSelectorFn (c : Code) :
    Partrec (onlineHalfRichChunkSelectorFn c) := by
  -- Ordinal selector computability for the emitted half-rich chunk stream.
  have h_args : Primrec (fun p : BitString × ℕ =>
      (((selNat p.1, selAlpha p.1), selMaxK p.1), p.2)) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.pair (selNat_primrec.comp Primrec.fst)
          (selAlpha_primrec.comp Primrec.fst))
        (selMaxK_primrec.comp Primrec.fst)) Primrec.snd
  have h_check : Computable₂ (fun (s : BitString) (t : ℕ) =>
      decide (selH s <
        (emittedHalfRichChunksList c (selNat s) (selAlpha s) (selMaxK s) t).length)) :=
    (PrimrecPred.decide (Primrec.nat_lt.comp
      (selH_primrec.comp Primrec.fst)
      (Primrec.list_length.comp
        ((emittedHalfRichChunksList_primrec c).comp h_args)))).to_comp.to₂
  have h_body := (onlineHalfRichChunkBody_primrec c).to_comp.to₂
  exact (Partrec.bind (Partrec.rfind h_check.partrec₂) h_body.partrec₂).of_eq
    (fun _ => rfl)

/-- Equal chunk lists yield the same chunk (as a finset) at a common index,
independent of the index-bound proof. -/
theorem toFinset_get_eq_of_listEq {l l' : List (List BitString)} (hll : l = l')
    {n : ℕ} (hn : n < l.length) (hn' : n < l'.length) :
    (l.get ⟨n, hn⟩).toFinset = (l'.get ⟨n, hn'⟩).toFinset := by
  subst hll; rfl

/-- `ratMassInvNat` depends only on its numerator, not the positivity proof. -/
theorem ratMassInvNat_congr {a b : ℕ} (hab : a = b) (ha : 0 < a) (hb : 0 < b) :
    ratMassInvNat a ha = ratMassInvNat b hb := by subst hab; rfl

/-
Evaluating the online ordinal selector at `richInput i j k h` with a valid
ordinal `h` returns the canonical-uniform code of the `h`-th emitted chunk.
-/
theorem onlineHalfRichChunkSelectorFn_eq (c : Code) (i j k h t : ℕ)
    (h_lt : h < (emittedHalfRichChunksList c i j k t).length)
    (h_first : ∀ t' < t, ¬(h < (emittedHalfRichChunksList c i j k t').length))
    (hne : ((emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩).toFinset.Nonempty) :
    onlineHalfRichChunkSelectorFn c (richInput i j k h)
      = Part.some
          ((codedUniformOn
            ((emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩).toFinset hne).code) := by
  apply Part.eq_some_iff.mpr
  unfold onlineHalfRichChunkSelectorFn
  simp only [selH_richInput, selNat_richInput, selAlpha_richInput,
    selMaxK_richInput]
  rw [Part.mem_bind_iff]
  refine ⟨t, ?_, ?_⟩
  · let test : PFun Nat Bool := fun t' => Part.some
      (decide (h < (emittedHalfRichChunksList c i j k t').length))
    change t ∈ Nat.rfind test
    rw [Nat.mem_rfind]
    constructor
    · simp [test, h_lt]
    · intro m hm
      simp [test, h_first m hm]
  · simp only [Part.mem_some_iff]
    have hcard : max 1
        (emittedHalfRichChunksList c i j k t)[h].toFinset.card =
        (emittedHalfRichChunksList c i j k t)[h].toFinset.card :=
      Nat.max_eq_right (Finset.Nonempty.card_pos hne)
    rw [List.drop_eq_getElem_cons h_lt]
    rw [codedUniformOn_code_eq]
    simp only [length_canonicalFinsetList]
    congr 3
    funext x
    congr 1
    exact ratMassInvNat_congr hcard.symm _ _

/-- Stability of a fixed chunk index across time: once chunk `h` exists at time
`t`, it has the same value (as a finset) at any later time `t'`. -/
theorem emittedHalfRichChunksList_get_stable (c : Code) (i j k h : ℕ) {t t' : ℕ}
    (htt : t ≤ t') (h_lt : h < (emittedHalfRichChunksList c i j k t).length)
    (h_lt' : h < (emittedHalfRichChunksList c i j k t').length) :
    (emittedHalfRichChunksList c i j k t').get ⟨h, h_lt'⟩
      = (emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩ := by
  obtain ⟨rest, hrest⟩ := emittedHalfRichChunksList_prefix c i j k htt
  simp only [hrest, List.get_eq_getElem, List.getElem_append_left h_lt]

/-
Minimality-free evaluation of the online ordinal selector: if chunk `h`
exists and is nonempty at *some* time `t`, the selector returns its
canonical-uniform code.  Derived from `onlineHalfRichChunkSelectorFn_eq` by
running to the first time the chunk appears and using stability.
-/
theorem onlineHalfRichChunkSelectorFn_eq_of_mem (c : Code) (i j k h t : ℕ)
    (h_lt : h < (emittedHalfRichChunksList c i j k t).length)
    (hne : ((emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩).toFinset.Nonempty) :
    onlineHalfRichChunkSelectorFn c (richInput i j k h)
      = Part.some
          ((codedUniformOn
            ((emittedHalfRichChunksList c i j k t).get ⟨h, h_lt⟩).toFinset hne).code) := by
  apply Eq.symm; exact (by
    have := onlineHalfRichChunkSelectorFn_eq c i j k h
      (Nat.find (⟨t, h_lt⟩ : ∃ t,
        h < (emittedHalfRichChunksList c i j k t).length))
      (Nat.find_spec (⟨t, h_lt⟩ : ∃ t,
        h < (emittedHalfRichChunksList c i j k t).length))
      (fun t' ht' => Nat.find_min (⟨t, h_lt⟩ : ∃ t,
        h < (emittedHalfRichChunksList c i j k t).length) ht') (by
    grind +suggestions)
    grind +suggestions
  )

/-
**Complexity-portion selector obligation (primary target).**

This is the selector/coding obligation corresponding to the standard main
statement `A -> C`: many `(i,j)` descriptions imply an `(i-k,j)` description, up
to visible logarithmic slack.  The size-improvement statement should be derived
from this one rather than proved by an independent size selector.

The intended construction is the online half-rich covering stream: enumerate
chunks as they are created
and address a chunk by its ordinal, not by a final snapshot/halt-count.

The complexity-improvement analogue of `richSizePortion_selector_correct`, with
batches of size `≤ 2 ^ j` addressed by `h < 2 ^ (i - k + 4)`.  This is proved
from the effective `emittedHalfRichChunks` stream and is the
foundational step of the complexity chain
(`setComplexity_halfRichComplexityPortion_le` → … →
`ImprovingDescriptionsComplexityLogSlack`).
-/
theorem halfRichComplexityPortion_selector_correct (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ f : BitString →. BitString, Partrec f ∧
      ∀ x n i j k, x.length = n → ManyIJDescriptions U x i j k → k ≤ i →
        ∃ h < 2 ^ (i - k + 4),
          ∃ (S : Finset BitString) (hS : S.Nonempty),
            x ∈ S ∧
            S.card ≤ 2 ^ j ∧
            f (richInput i j k h) = Part.some ((codedUniformOn S hS).code) := by
  -- Proved from the effective `emittedHalfRichChunks` stream above: coverage of
  -- rich elements, the full/non-full online counting bounds, and a
  -- partial-recursive ordinal selector that runs until the requested chunk is
  -- emitted.
  obtain ⟨c, hcRaw⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  have hc : IsCodeFor c U := by
    exact hcRaw
  refine ⟨ _, partrec_onlineHalfRichChunkSelectorFn c, ?_ ⟩;
  intro x n i j k hx hmany hk;
  obtain ⟨t, S, hS₁, hS₂⟩ := emittedHalfRichChunks_cover_rich U c hc i j k x
    (mem_richDescriptionElements_of_many U x i j k hmany);
  obtain ⟨ h, hh₁, hh₂ ⟩ := List.mem_map.mp hS₁;
  obtain ⟨ h', hh'₁, hh'₂ ⟩ := List.mem_iff_getElem.mp hh₁;
  refine ⟨ h', ?_, S, ?_, ?_, ?_, ?_ ⟩;
  any_goals assumption;
  any_goals exact Finset.nonempty_of_ne_empty ( by rintro rfl; simp_all +decide );
  · exact lt_of_lt_of_le hh'₁ (by
      simpa [emittedHalfRichChunks] using
        emittedHalfRichChunks_length_le U c hc i j k t |> le_trans <|
          Nat.pow_le_pow_right (by decide) <| by omega);
  · exact emittedHalfRichChunks_card_le c i j k t S hS₁;
  · have hset :
        ((emittedHalfRichChunksList c i j k t).get ⟨h', hh'₁⟩).toFinset = S := by
      change (emittedHalfRichChunksList c i j k t)[h'].toFinset = S
      rw [hh'₂, hh₂]
    have hne :
        ((emittedHalfRichChunksList c i j k t).get ⟨h', hh'₁⟩).toFinset.Nonempty :=
      hset.symm ▸ Finset.nonempty_of_ne_empty (by rintro rfl; simp_all +decide)
    calc
      onlineHalfRichChunkSelectorFn c (richInput i j k h') =
          Part.some ((codedUniformOn _ hne).code) :=
        onlineHalfRichChunkSelectorFn_eq_of_mem c i j k h' t hh'₁ hne
      _ = Part.some ((codedUniformOn S _).code) :=
        congrArg Part.some (codedUniformOn_code_congr hne _ hset)

/-- Half-rich dump bound: the objects with many descriptions are few.  This is
the proved whole-rich cardinality estimate; the genuine complexity-half work is
to refine this into a computable portion family with only about `2^(i-k)` viable
portion addresses. -/
theorem halfRich_dump_card_le (U : Map) :
    ∀ i j k : ℕ,
      (richDescriptionElements U i j k).card ≤ 2 ^ (i + 1 + j - k) := by
  intro i j k
  exact card_richDescriptionElements_le U i j k

/-
7. `setComplexity` bound and complexity portion assembly.

The coding wrapper around `halfRichComplexityPortion_selector_correct`. Here the
batch address is small, `h < 2 ^ (i - k + 4)`, so the address-parameterized
bound `richInput_KPPlain_le_addr` (with `m = i - k + 3`) yields complexity
`(i - k + 1) + logSlack`, and `logSlack_one_add_le_two_mul` absorbs the `+1` and
the slack argument `i + j + k + (i - k) = 2 * i + j` into the visible-parameter
slack `n + i + j`.
-/
theorem setComplexity_halfRichComplexityPortion_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x n i j k, x.length = n → ManyIJDescriptions U x i j k → k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) : ENat) ∧
        S.card ≤ 2 ^ j := by
  obtain ⟨f, hf, hf_spec⟩ := halfRichComplexityPortion_selector_correct U hU
  obtain ⟨c₃, hc₃⟩ := KPPlain_partrec_map_le U hU f hf
  obtain ⟨c₄, hc₄⟩ := richInput_KPPlain_le_addr U hU c₃
  refine ⟨4 * c₄ + 4, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨h, hh, S, hS, hxS, hcard, hfeq⟩ := hf_spec x n i j k hn hmany hk
  refine ⟨S, hS, hxS, ?_, hcard⟩
  have hmem : (codedUniformOn S hS).code ∈ f (richInput i j k h) := by
    rw [hfeq]; exact Part.mem_some _
  have hbound : setComplexity U S hS
      ≤ ((i - k : ℕ) : ENat) + 4 + logSlack c₄ (i + j + k + (i - k + 3)) :=
    le_trans (hc₃ _ _ hmem) (hc₄ i j k h (i - k + 3) hh)
  have habs : 4 + logSlack c₄ (i + j + k + (i - k + 3)) ≤ logSlack (4 * c₄ + 4) (n + i + j) := by
    apply logSlack_four_add_le
    omega
  refine le_trans hbound ?_
  rw [← ENat.natCast_sub, add_assoc]
  gcongr
  exact_mod_cast habs

/-- Selector/coding interface for the complexity-improvement half. -/
theorem exists_halfRichComplexityRefinedSet_logSlack (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x n i j k,
      x.length = n → ManyIJDescriptions U x i j k → k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) : ENat) ∧
        S.card ≤ 2 ^ (j + logSlack c (n + i + j)) := by
  obtain ⟨c, hc⟩ := setComplexity_halfRichComplexityPortion_le U hU
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hx, hcomp, hcard⟩ := hc x n i j k hn hmany hk
  refine ⟨S, hS, hx, hcomp, ?_⟩
  exact hcard.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- Faithful logarithmic-slack target for the complexity-improvement half. -/
theorem exists_description_smaller_complexity_of_many_logSlack
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ImprovingDescriptionsComplexityLogSlack U := by
  obtain ⟨c, hc⟩ := exists_halfRichComplexityRefinedSet_logSlack U hU
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hxS, hcomp, hcard⟩ := hc x n i j k hn hmany hk
  exact ⟨S, hS, hxS, hcomp, hcard⟩

end Kolmogorov
