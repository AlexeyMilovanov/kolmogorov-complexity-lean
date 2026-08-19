import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1EffectiveRun
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T3

/-!
# T3 boundary density (VS40 Section 7, Theorem `t3`, boundary case)

Self-contained counting leaves for the `k ≤ n < k + 4` boundary of Theorem `t3`.
The interior `t1`/`t3` construction already covers `k + 4 ≤ n`; the boundary
endpoint (in particular `n = k`) is established by a direct program-budget count.

Key fact (`highComplexity_lengthSlice_card_lower`): there is a uniform constant
`c` such that whenever `c ≤ eps ≤ k ≤ n`, at least `2 ^ (k - eps)` strings of
length `n` have plain complexity at least `k`, **even at the endpoint `n = k`**.

The proof: the `< 2^k` compressible words of budget `k - 1` must include every
string of length `m := k - (cLen + 1)` (they are short, hence compressible) as
well as every length-`n` string of plain complexity `< k`.  These two length
slices are disjoint (`m < n`), so the low-complexity length-`n` slice has at most
`2^k - 1 - 2^m` elements, leaving at least `2^m ≥ 2^(k - eps)` high-complexity
length-`n` strings.

These lemmas use only plain complexity and finite counting; they are independent
of symmetry of information and of the deferred add-noise transport.
-/

namespace Kolmogorov

/-- Program-budget membership: a string whose conditional complexity is strictly
below `k` is a compressible word of budget `k - 1`. -/
theorem mem_compressibleWords_of_condK_lt
    (V : Map) (x y : BitString) (k : ℕ) (hk : 1 ≤ k)
    (h : condK V x y < (k : ENat)) :
    x ∈ compressibleWords V y (k - 1) := by
  rw [compressibleWords, Finset.mem_filter]
  have h' : sInf (candidateLengths V x y) < (k : ENat) := h
  obtain ⟨len, h_mem_len, h_val_lt⟩ := sInf_lt_iff.mp h'
  obtain ⟨p, hp_prod, rfl⟩ := h_mem_len
  have h_len_lt : programLength p < k := by exact_mod_cast h_val_lt
  have h_len_le : programLength p ≤ k - 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨p, mem_programsLe (k - 1) p h_len_le, progToOut_eq_some.mpr hp_prod⟩
  · have hmem : (programLength p : ENat) ∈ candidateLengths V x y := ⟨p, hp_prod, rfl⟩
    calc condK V x y ≤ (programLength p : ENat) := sInf_le hmem
      _ ≤ ((k - 1 : ℕ) : ENat) := by exact_mod_cast h_len_le

/-- Boundary density for Theorem `t3`.  For a uniform constant `c = cLen + 1`
(where `cLen` is the plain literal-coding constant of `V`), whenever
`c ≤ eps ≤ k ≤ n`, at least `2 ^ (k - eps)` strings of length `n` have plain
complexity at least `k`.  The bound holds including the endpoint `n = k`. -/
theorem highComplexity_lengthSlice_card_lower (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n k eps : ℕ),
      c ≤ eps → eps ≤ k → k ≤ n →
      2 ^ (k - eps) ≤
        ((stringsOfLength n).filter (fun x => (k : ENat) ≤ plainK V x)).card := by
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  refine ⟨cLen + 1, fun n k eps hc heps hkn => ?_⟩
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 cLen) (le_trans hc heps)
  set m := k - (cLen + 1) with hm_def
  -- Short slice: every length-`m` string is compressible of budget `k - 1`.
  have h_short_sub : stringsOfLength m ⊆ compressibleWords V [] (k - 1) := by
    intro x hx
    rw [memStringsOfLength] at hx
    have hpk : plainK V x < (k : ENat) := by
      have h1 : plainK V x ≤ (x.length : ENat) + (cLen : ENat) := hLen x
      rw [hx] at h1
      have hlt : (m : ENat) + (cLen : ENat) < (k : ENat) := by
        rw [← Nat.cast_add]; exact_mod_cast (show m + cLen < k by omega)
      exact lt_of_le_of_lt h1 hlt
    exact mem_compressibleWords_of_condK_lt V x [] k hk1 hpk
  -- Low slice: length-`n` strings of plain complexity `< k` are compressible.
  have h_low_sub :
      (stringsOfLength n).filter (fun x => ¬ ((k : ENat) ≤ plainK V x)) ⊆
        compressibleWords V [] (k - 1) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact mem_compressibleWords_of_condK_lt V x [] k hk1 (not_le.mp hx.2)
  -- The two length slices are disjoint since `m < n`.
  have hmn : m < n := by omega
  have h_disj : Disjoint (stringsOfLength m)
      ((stringsOfLength n).filter (fun x => ¬ ((k : ENat) ≤ plainK V x))) := by
    rw [Finset.disjoint_left]
    intro x hxm hxn
    rw [memStringsOfLength] at hxm
    rw [Finset.mem_filter, memStringsOfLength] at hxn
    omega
  -- Disjoint union of both slices sits inside the compressible words.
  have h_union_sub :
      stringsOfLength m ∪
        (stringsOfLength n).filter (fun x => ¬ ((k : ENat) ≤ plainK V x)) ⊆
        compressibleWords V [] (k - 1) :=
    Finset.union_subset h_short_sub h_low_sub
  have h_inter :
      stringsOfLength m ∩
        (stringsOfLength n).filter (fun x => ¬ ((k : ENat) ≤ plainK V x)) = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp h_disj
  have h_union_card :
      (stringsOfLength m ∪
        (stringsOfLength n).filter (fun x => ¬ ((k : ENat) ≤ plainK V x))).card =
      (stringsOfLength m).card +
        ((stringsOfLength n).filter (fun x => ¬ ((k : ENat) ≤ plainK V x))).card := by
    have hci := Finset.card_union_add_card_inter (stringsOfLength m)
      ((stringsOfLength n).filter (fun x => ¬ ((k : ENat) ≤ plainK V x)))
    rw [h_inter, Finset.card_empty] at hci
    omega
  have h_card_union :
      (stringsOfLength m).card +
        ((stringsOfLength n).filter (fun x => ¬ ((k : ENat) ≤ plainK V x))).card ≤
        (compressibleWords V [] (k - 1)).card := by
    rw [← h_union_card]
    exact Finset.card_le_card h_union_sub
  have h_comp_lt : (compressibleWords V [] (k - 1)).card < 2 ^ k := by
    have h := cardCompressibleWordsLt V [] (k - 1)
    have hk_eq : (k - 1) + 1 = k := by omega
    rwa [hk_eq] at h
  -- Partition of the length-`n` cube into high- and low-complexity slices.
  have h_part :
      ((stringsOfLength n).filter (fun x => (k : ENat) ≤ plainK V x)).card +
        ((stringsOfLength n).filter (fun x => ¬ ((k : ENat) ≤ plainK V x))).card =
        (stringsOfLength n).card :=
    Finset.card_filter_add_card_filter_not (fun x => (k : ENat) ≤ plainK V x)
  rw [cardStringsOfLength] at h_part
  rw [cardStringsOfLength] at h_card_union
  have h2m_le : 2 ^ (k - eps) ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h2k_le : 2 ^ k ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hkn
  omega

structure T3BoundaryDRunState where
  current : List BitString
  dSeen : List BitString
  rebuilds : ℕ

def t3BoundaryDInitial (n k epsilon : ℕ) : T3BoundaryDRunState :=
  let S := canonicalFinsetList (stringsOfLength n)
  let current := S.take (2 ^ (k - epsilon))
  ⟨current, [], 0⟩

def t3BoundaryDQuotaReached
    (c : Nat.Partrec.Code) (n k epsilon delta t : ℕ)
    (s : T3BoundaryDRunState) : Bool :=
  let quota := 2 ^ (k - epsilon - delta)
  let dStage := t1DStage c n k t
  let marked := s.current.filter (fun x => dStage.contains x)
  marked.length ≥ quota

def t3BoundaryDRebuild
    (c : Nat.Partrec.Code) (n k epsilon t : ℕ)
    (s : T3BoundaryDRunState) : T3BoundaryDRunState :=
  let dStage := t1DStage c n k t
  let newDSeen := (s.dSeen ++ (s.current.filter (fun x => dStage.contains x))).eraseDups
  let S := canonicalFinsetList (stringsOfLength n)
  let available := S.filter (fun x => ¬ newDSeen.contains x)
  let newCurrent := available.take (2 ^ (k - epsilon))
  ⟨newCurrent, newDSeen, s.rebuilds + 1⟩

def t3BoundaryDStep
    (c : Nat.Partrec.Code) (n k epsilon delta t : ℕ)
    (s : T3BoundaryDRunState) : T3BoundaryDRunState :=
  if t3BoundaryDQuotaReached c n k epsilon delta t s then
    t3BoundaryDRebuild c n k epsilon t s
  else
    s

def t3BoundaryDRun (c : Nat.Partrec.Code) (n k epsilon delta t : ℕ) : T3BoundaryDRunState :=
  match t with
  | 0 => t3BoundaryDInitial n k epsilon
  | t' + 1 =>
      t3BoundaryDStep c n k epsilon delta (t' + 1)
        (t3BoundaryDRun c n k epsilon delta t')

theorem t3BoundaryD_rebuild_available (V : Map) (hV : isOptimalConditional V) :
    ∃ c0 : ℕ, ∀ (n k epsilon : ℕ) (dSeen : List BitString),
      c0 ≤ epsilon → epsilon ≤ k → k ≤ n →
      (∀ x ∈ dSeen, ¬ ((k : ENat) ≤ plainK V x)) →
      2 ^ (k - epsilon) ≤
        ((canonicalFinsetList (stringsOfLength n)).filter
          (fun x => ¬ dSeen.contains x)).length := by
  obtain ⟨c0, hhigh⟩ := highComplexity_lengthSlice_card_lower V hV
  refine ⟨c0, ?_⟩
  intro n k epsilon dSeen hc0 hepsilon hkn hSeen
  let high := (stringsOfLength n).filter
    (fun x => (k : ENat) ≤ plainK V x)
  let available := (canonicalFinsetList (stringsOfLength n)).filter
    (fun x => ¬ dSeen.contains x)
  have havailable_nodup : available.Nodup := by
    exact List.Nodup.filter _ (canonicalFinsetList_nodup _)
  have hsubset : high ⊆ available.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨mem_canonicalFinsetList.mpr hx.1, ?_⟩
    simp only [Bool.not_eq_true, decide_eq_true_eq]
    apply Bool.eq_false_iff.mpr
    intro hxd
    exact (hSeen x (by simpa using hxd)) hx.2
  calc
    2 ^ (k - epsilon) ≤ high.card := hhigh n k epsilon hc0 hepsilon hkn
    _ ≤ available.toFinset.card := Finset.card_le_card hsubset
    _ = available.length := List.toFinset_card_of_nodup havailable_nodup

/-- The elementary freshness/charging invariant of the boundary D-only run.
It is independent of any machine-correctness assumption: correctness is needed
only later to interpret D marks as low-complexity strings. -/
structure T3BoundaryDRunInvariant (quota : ℕ) (s : T3BoundaryDRunState) : Prop where
  current_nodup : s.current.Nodup
  dSeen_nodup : s.dSeen.Nodup
  current_fresh : ∀ x ∈ s.current, x ∉ s.dSeen
  charged : s.rebuilds * quota ≤ s.dSeen.length

theorem t3BoundaryDInitial_invariant (n k epsilon delta : ℕ) :
    T3BoundaryDRunInvariant (2 ^ (k - epsilon - delta))
      (t3BoundaryDInitial n k epsilon) := by
  refine ⟨?_, by simp [t3BoundaryDInitial], ?_, by simp [t3BoundaryDInitial]⟩
  · simp only [t3BoundaryDInitial]
    exact (List.take_sublist _ _).nodup
      (canonicalFinsetList_nodup _)
  · simp [t3BoundaryDInitial]

theorem t3BoundaryDRebuild_preserves_invariant
    (c : Nat.Partrec.Code) (n k epsilon t quota : ℕ)
    (s : T3BoundaryDRunState)
    (hs : T3BoundaryDRunInvariant quota s)
    (hreached : quota ≤
      (s.current.filter (fun x => (t1DStage c n k t).contains x)).length) :
    T3BoundaryDRunInvariant quota
      (t3BoundaryDRebuild c n k epsilon t s) := by
  let marked := s.current.filter
    (fun x => (t1DStage c n k t).contains x)
  have hmarked_nodup : marked.Nodup := hs.current_nodup.filter _
  have happend_nodup : (s.dSeen ++ marked).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hs.dSeen_nodup, hmarked_nodup, ?_⟩
    intro x hxd y hym hxy
    subst y
    exact hs.current_fresh x (List.mem_of_mem_filter hym) hxd
  have herase : (s.dSeen ++ marked).eraseDups = s.dSeen ++ marked :=
    eraseDups_eq_self_of_nodup happend_nodup
  let newDSeen := (s.dSeen ++ marked).eraseDups
  let available := (canonicalFinsetList (stringsOfLength n)).filter
    (fun x => ¬ newDSeen.contains x)
  let newCurrent := available.take (2 ^ (k - epsilon))
  have hnewCurrent_nodup : newCurrent.Nodup := by
    exact (List.take_sublist _ _).nodup
      ((List.filter_sublist).nodup (canonicalFinsetList_nodup _))
  have hnewDSeen_nodup : newDSeen.Nodup := nodup_eraseDups_bitString _
  have hfresh : ∀ x ∈ newCurrent, x ∉ newDSeen := by
    intro x hx hxd
    have hxavailable : x ∈ available := List.mem_of_mem_take hx
    rw [List.mem_filter] at hxavailable
    have hfalse : newDSeen.contains x = false := by
      simpa only [Bool.not_eq_true, decide_eq_true_eq] using hxavailable.2
    exact Bool.eq_false_iff.mp hfalse (by simpa using hxd)
  have hcharged : (s.rebuilds + 1) * quota ≤ newDSeen.length := by
    have hlen : newDSeen.length = s.dSeen.length + marked.length := by
      simp only [newDSeen, herase, List.length_append]
    rw [hlen]
    have hmarked : quota ≤ marked.length := by simpa [marked] using hreached
    nlinarith [hs.charged]
  simpa [t3BoundaryDRebuild, marked, newDSeen, available, newCurrent] using
    (show T3BoundaryDRunInvariant quota
      ⟨newCurrent, newDSeen, s.rebuilds + 1⟩ from
        ⟨hnewCurrent_nodup, hnewDSeen_nodup, hfresh, hcharged⟩)

theorem t3BoundaryDRun_invariant
    (c : Nat.Partrec.Code) (n k epsilon delta t : ℕ) :
    T3BoundaryDRunInvariant (2 ^ (k - epsilon - delta))
      (t3BoundaryDRun c n k epsilon delta t) := by
  induction t with
  | zero => exact t3BoundaryDInitial_invariant n k epsilon delta
  | succ t ih =>
      rw [t3BoundaryDRun]
      by_cases hreach :
          t3BoundaryDQuotaReached c n k epsilon delta (t + 1)
            (t3BoundaryDRun c n k epsilon delta t) = true
      · rw [t3BoundaryDStep, if_pos hreach]
        apply t3BoundaryDRebuild_preserves_invariant c n k epsilon (t + 1)
          (2 ^ (k - epsilon - delta)) _ ih
        simpa [t3BoundaryDQuotaReached] using hreach
      · rw [t3BoundaryDStep, if_neg hreach]
        exact ih

/-- Every accumulated D mark is a genuine length-`n` string of plain
complexity below `k`, provided the executable stream uses a code for `V`. -/
theorem t3BoundaryDRun_dSeen_sound
    {V : Map} {c : Nat.Partrec.Code} (hc : IsCodeFor c V)
    (n k epsilon delta : ℕ) : ∀ t x,
      x ∈ (t3BoundaryDRun c n k epsilon delta t).dSeen →
        x.length = n ∧ plainK V x < (k : ENat) := by
  intro t
  induction t with
  | zero => simp [t3BoundaryDRun, t3BoundaryDInitial]
  | succ t ih =>
      intro x hx
      rw [t3BoundaryDRun] at hx
      by_cases hreach :
          t3BoundaryDQuotaReached c n k epsilon delta (t + 1)
            (t3BoundaryDRun c n k epsilon delta t) = true
      · rw [t3BoundaryDStep, if_pos hreach,
          t3BoundaryDRebuild] at hx
        rcases List.mem_append.mp (mem_eraseDups_bitString.mp hx) with hold | hnew
        · exact ih x hold
        · exact t1DStage_sound hc (by
            simpa using (List.mem_filter.mp hnew).2)
      · rw [t3BoundaryDStep, if_neg hreach] at hx
        exact ih x hx

/-- Availability keeps every historical boundary model at the exact target
cardinality.  This is the run-level use of the boundary density theorem. -/
theorem t3BoundaryDRun_current_length
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c0 : ℕ, ∀ {c : Nat.Partrec.Code}, IsCodeFor c V →
      ∀ (n k epsilon delta t : ℕ),
        c0 ≤ epsilon → epsilon ≤ k → k ≤ n →
        (t3BoundaryDRun c n k epsilon delta t).current.length =
          2 ^ (k - epsilon) := by
  obtain ⟨c0, havailable⟩ := t3BoundaryD_rebuild_available V hV
  refine ⟨c0, ?_⟩
  intro c hc n k epsilon delta t hc0 hepsilon hkn
  induction t with
  | zero =>
      simp only [t3BoundaryDRun, t3BoundaryDInitial, List.length_take,
        length_canonicalFinsetList, cardStringsOfLength]
      exact Nat.min_eq_left
        (Nat.pow_le_pow_right (by decide) (by omega))
  | succ t ih =>
      have hsound := t3BoundaryDRun_dSeen_sound hc
        n k epsilon delta (t + 1)
      rw [t3BoundaryDRun]
      by_cases hreach :
          t3BoundaryDQuotaReached c n k epsilon delta (t + 1)
            (t3BoundaryDRun c n k epsilon delta t) = true
      · rw [t3BoundaryDStep, if_pos hreach, t3BoundaryDRebuild,
          List.length_take]
        apply Nat.min_eq_left
        apply havailable n k epsilon _ hc0 hepsilon hkn
        intro x hx
        exact not_le_of_gt (hsound x (by
          simpa [t3BoundaryDRun, t3BoundaryDStep, hreach,
            t3BoundaryDRebuild] using hx)).2
      · rw [t3BoundaryDStep, if_neg hreach]
        exact ih

/-- Every historical current model stays inside the length-`n` cube. -/
theorem t3BoundaryDRun_current_subset_cube
    (c : Nat.Partrec.Code) (n k epsilon delta t : ℕ) :
    (t3BoundaryDRun c n k epsilon delta t).current.toFinset ⊆
      stringsOfLength n := by
  induction t with
  | zero =>
      intro x hx
      rw [List.mem_toFinset] at hx
      exact mem_canonicalFinsetList.mp
        (List.mem_of_mem_take hx)
  | succ t ih =>
      rw [t3BoundaryDRun]
      by_cases hreach :
          t3BoundaryDQuotaReached c n k epsilon delta (t + 1)
            (t3BoundaryDRun c n k epsilon delta t) = true
      · rw [t3BoundaryDStep, if_pos hreach]
        intro x hx
        rw [List.mem_toFinset] at hx
        exact mem_canonicalFinsetList.mp
          (List.mem_of_mem_filter (List.mem_of_mem_take hx))
      · rw [t3BoundaryDStep, if_neg hreach]
        exact ih

theorem t3BoundaryD_rebuilds_le (c : Nat.Partrec.Code) (n k epsilon delta t : ℕ) :
    (t3BoundaryDRun c n k epsilon delta t).rebuilds * 2 ^ (k - epsilon - delta) ≤
      (t3BoundaryDRun c n k epsilon delta t).dSeen.length :=
  (t3BoundaryDRun_invariant c n k epsilon delta t).charged

/-- Fewer than `2^k` distinct low-complexity strings can ever have been
charged by a correct D stream. -/
theorem t3BoundaryDRun_dSeen_length_lt
    {V : Map} {c : Nat.Partrec.Code} (hc : IsCodeFor c V)
    (n k epsilon delta t : ℕ) :
    (t3BoundaryDRun c n k epsilon delta t).dSeen.length < 2 ^ k := by
  let L := (t3BoundaryDRun c n k epsilon delta t).dSeen
  have hsound := t3BoundaryDRun_dSeen_sound hc n k epsilon delta t
  cases k with
  | zero =>
      have hL : L = [] := by
        by_contra hne
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil L hne
        have := (hsound x hx).2
        simp at this
      simp [L, hL]
  | succ k =>
      have hsubset : L.toFinset ⊆ compressibleWords V [] k := by
        intro x hx
        have hxL : x ∈ L := List.mem_toFinset.mp hx
        have hlow := (hsound x hxL).2
        simpa only [Nat.succ_sub_one] using
          (mem_compressibleWords_of_condK_lt V x [] (k + 1)
            (Nat.succ_le_succ (Nat.zero_le k)) hlow)
      calc
        L.length = L.toFinset.card :=
          (List.toFinset_card_of_nodup
            (t3BoundaryDRun_invariant c n (k + 1) epsilon delta t).dSeen_nodup).symm
        _ ≤ (compressibleWords V [] k).card := Finset.card_le_card hsubset
        _ < 2 ^ (k + 1) := cardCompressibleWordsLt V [] k

/-- The strict version bound obtained by charging each rebuild to a fresh
quota-sized batch of D marks. -/
theorem t3BoundaryD_rebuilds_lt
    {V : Map} {c : Nat.Partrec.Code} (hc : IsCodeFor c V)
    (n k epsilon delta t : ℕ)
    (hepsilon : epsilon ≤ k) (hdelta : delta ≤ k - epsilon) :
    (t3BoundaryDRun c n k epsilon delta t).rebuilds <
      2 ^ (epsilon + delta) := by
  let rebuilds := (t3BoundaryDRun c n k epsilon delta t).rebuilds
  let quota := 2 ^ (k - epsilon - delta)
  have hcharge : rebuilds * quota ≤
      (t3BoundaryDRun c n k epsilon delta t).dSeen.length :=
    t3BoundaryD_rebuilds_le c n k epsilon delta t
  have hmarks := t3BoundaryDRun_dSeen_length_lt hc n k epsilon delta t
  have hproduct : rebuilds * quota < 2 ^ k := hcharge.trans_lt hmarks
  have hscale : quota * 2 ^ (epsilon + delta) = 2 ^ k := by
    simpa [quota] using
      t3_rebuild_scale_identity hepsilon hdelta
  have hquota_pos : 0 < quota := by simp [quota]
  nlinarith

theorem exists_t3_boundary_d_only_structural (V : Map) (hV : isOptimalConditional V) :
    ∃ c0 : ℕ, ∀ (n k epsilon delta : ℕ),
      c0 ≤ epsilon → epsilon ≤ k → delta ≤ k - epsilon → k ≤ n →
      ∃ (A : Finset BitString) (bad : Finset BitString) (rebuilds : ℕ),
        A ⊆ stringsOfLength n ∧
        A.card = 2 ^ (k - epsilon) ∧
        bad ⊆ A ∧
        bad.card ≤ 2 ^ (k - epsilon - delta) ∧
        (∀ x ∈ A \ bad, (k : ENat) ≤ plainK V x) ∧
        rebuilds ≤ 2 ^ (epsilon + delta + 1) := by
  obtain ⟨c0, hhigh⟩ := highComplexity_lengthSlice_card_lower V hV
  refine ⟨c0, ?_⟩
  intro n k epsilon delta hc0 hepsilon _hdelta hkn
  let high := (stringsOfLength n).filter
    (fun x => (k : ENat) ≤ plainK V x)
  obtain ⟨A, hAhigh, hAcard⟩ :=
    Finset.exists_subset_card_eq (hhigh n k epsilon hc0 hepsilon hkn)
  refine ⟨A, ∅, 0, ?_, hAcard, by simp, by simp, ?_, by simp⟩
  · intro x hx
    exact (Finset.mem_filter.mp (hAhigh hx)).1
  · intro x hx
    exact (Finset.mem_filter.mp (hAhigh (Finset.mem_sdiff.mp hx).1)).2

/-- Filtering with a weaker predicate can only shrink the list. -/
theorem t3Boundary_length_filter_mono {α : Type*} (L : List α)
    (p q : α → Bool) (h : ∀ a, p a = true → q a = true) :
    (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
      by_cases hp : p a = true
      · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h a hp)]
        simpa using ih
      · rw [List.filter_cons_of_neg (by simpa using hp)]
        by_cases hq : q a = true
        · rw [List.filter_cons_of_pos hq, List.length_cons]
          omega
        · rw [List.filter_cons_of_neg (by simpa using hq)]
          exact ih

/-- The `D` stream only grows with the stage index. -/
theorem t3Boundary_t1DStage_mono (c : Nat.Partrec.Code) (n k : ℕ) {u t : ℕ}
    (h : u ≤ t) : t1DStage c n k u <+: t1DStage c n k t := by
  induction t with
  | zero => rw [Nat.le_zero.mp h]
  | succ t ih =>
      rcases Nat.lt_or_ge u (t + 1) with hu | hu
      · exact (ih (Nat.lt_succ_iff.mp hu)).trans (t1DStage_prefix c n k t)
      · rw [Nat.le_antisymm h hu]

/-- The quota test is monotone in the stage index: a state that has already
reached its quota at stage `u` still has it at any later stage. -/
theorem t3BoundaryDQuotaReached_mono
    (c : Nat.Partrec.Code) (n k epsilon delta : ℕ) {u t : ℕ} (h : u ≤ t)
    (s : T3BoundaryDRunState)
    (hu : t3BoundaryDQuotaReached c n k epsilon delta u s = true) :
    t3BoundaryDQuotaReached c n k epsilon delta t s = true := by
  simp only [t3BoundaryDQuotaReached, ge_iff_le, decide_eq_true_eq] at hu ⊢
  refine hu.trans (t3Boundary_length_filter_mono _ _ _ ?_)
  intro a ha
  have hmem : a ∈ t1DStage c n k u := by simpa using ha
  simpa using (t3Boundary_t1DStage_mono c n k h).subset hmem

/-- A rebuild step increments the version counter by exactly one. -/
theorem t3BoundaryDRun_rebuilds_succ_of_reached
    (c : Nat.Partrec.Code) (n k epsilon delta t : ℕ)
    (h : t3BoundaryDQuotaReached c n k epsilon delta (t + 1)
      (t3BoundaryDRun c n k epsilon delta t) = true) :
    (t3BoundaryDRun c n k epsilon delta (t + 1)).rebuilds =
      (t3BoundaryDRun c n k epsilon delta t).rebuilds + 1 := by
  rw [t3BoundaryDRun, t3BoundaryDStep, if_pos h, t3BoundaryDRebuild]

/-- Without a quota hit the run state is unchanged. -/
theorem t3BoundaryDRun_eq_of_not_reached
    (c : Nat.Partrec.Code) (n k epsilon delta t : ℕ)
    (h : t3BoundaryDQuotaReached c n k epsilon delta (t + 1)
      (t3BoundaryDRun c n k epsilon delta t) = false) :
    t3BoundaryDRun c n k epsilon delta (t + 1) =
      t3BoundaryDRun c n k epsilon delta t := by
  rw [t3BoundaryDRun, t3BoundaryDStep, if_neg (by simp [h])]

/-- The version counter is monotone in the stage index. -/
theorem t3BoundaryDRun_rebuilds_mono (c : Nat.Partrec.Code) (n k epsilon delta : ℕ) :
    Monotone (fun t => (t3BoundaryDRun c n k epsilon delta t).rebuilds) := by
  apply monotone_nat_of_le_succ
  intro t
  by_cases hreach :
      t3BoundaryDQuotaReached c n k epsilon delta (t + 1)
        (t3BoundaryDRun c n k epsilon delta t) = true
  · rw [t3BoundaryDRun_rebuilds_succ_of_reached c n k epsilon delta t hreach]
    omega
  · rw [t3BoundaryDRun_eq_of_not_reached c n k epsilon delta t
      (by simpa using hreach)]

/-- Since the number of rebuilds is bounded, the run stops rebuilding, and
since the `D` stream stabilizes it is eventually complete.  Hence there is a
stage at which the boundary run is terminal: every low-complexity length-`n`
string has already been enumerated, and the current model is not marked often
enough to trigger another rebuild. -/
theorem exists_t3BoundaryD_terminal_stage
    {V : Map} {c : Nat.Partrec.Code} (hc : IsCodeFor c V)
    (n k epsilon delta : ℕ)
    (hepsilon : epsilon ≤ k) (hdelta : delta ≤ k - epsilon) :
    ∃ t,
      (∀ x : BitString, x.length = n → plainK V x < (k : ENat) →
        x ∈ t1DStage c n k t) ∧
      t3BoundaryDQuotaReached c n k epsilon delta t
        (t3BoundaryDRun c n k epsilon delta t) = false := by
  set f : ℕ → ℕ := fun t => (t3BoundaryDRun c n k epsilon delta t).rebuilds with hf
  have hmono : Monotone f := t3BoundaryDRun_rebuilds_mono c n k epsilon delta
  have hbdd : ∀ t, f t ≤ 2 ^ (epsilon + delta) := fun t =>
    (t3BoundaryD_rebuilds_lt hc n k epsilon delta t hepsilon hdelta).le
  obtain ⟨T1, hT1⟩ : ∃ T1, ∀ t, T1 ≤ t → f t = f T1 := by
    have hne : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
    have hbd : BddAbove (Set.range f) :=
      ⟨2 ^ (epsilon + delta), by rintro _ ⟨t, rfl⟩; exact hbdd t⟩
    obtain ⟨T1, hT1⟩ := Nat.sSup_mem hne hbd
    refine ⟨T1, fun t ht => le_antisymm ?_ (hmono ht)⟩
    rw [hT1]
    exact le_csSup hbd ⟨t, rfl⟩
  obtain ⟨T0, hT0⟩ := t1DStage_stabilizes c n k
  refine ⟨max T0 T1, ?_, ?_⟩
  · intro x hlen hlow
    obtain ⟨u, hu⟩ := t1DStage_complete hc hlen hlow
    have hxT0 : x ∈ t1DStage c n k T0 := by
      have hle : x ∈ t1DStage c n k (max u T0) :=
        (t3Boundary_t1DStage_mono c n k (le_max_left u T0)).subset hu
      rwa [hT0 _ (le_max_right u T0)] at hle
    rw [hT0 _ (le_max_left T0 T1)]
    exact hxT0
  · by_contra hreach
    have hreach' :
        t3BoundaryDQuotaReached c n k epsilon delta (max T0 T1)
          (t3BoundaryDRun c n k epsilon delta (max T0 T1)) = true := by
      simpa using hreach
    have hnext :
        t3BoundaryDQuotaReached c n k epsilon delta (max T0 T1 + 1)
          (t3BoundaryDRun c n k epsilon delta (max T0 T1)) = true :=
      t3BoundaryDQuotaReached_mono c n k epsilon delta (Nat.le_succ _) _ hreach'
    have hsucc := t3BoundaryDRun_rebuilds_succ_of_reached c n k epsilon delta
      (max T0 T1) hnext
    have h1 : f (max T0 T1) = f T1 := hT1 _ (le_max_right T0 T1)
    have h2 : f (max T0 T1 + 1) = f T1 :=
      hT1 _ (le_trans (le_max_right T0 T1) (Nat.le_succ _))
    simp only [hf] at h1 h2
    omega

/-- Terminal boundary model.  At a terminal stage the current model `A` is a
genuine length-`n` model of the exact target size `2 ^ (k - epsilon)`, its
exceptional subset `bad` (the strings already marked by the `D` stream) is
smaller than the quota `2 ^ (k - epsilon - delta)`, every string of `A \ bad`
has plain complexity at least `k`, and the version counter is below
`2 ^ (epsilon + delta)`. -/
theorem exists_t3BoundaryD_terminal_model (V : Map) (hV : isOptimalConditional V) :
    ∃ c0 : ℕ, ∀ {c : Nat.Partrec.Code}, IsCodeFor c V →
      ∀ (n k epsilon delta : ℕ),
        c0 ≤ epsilon → epsilon ≤ k → delta ≤ k - epsilon → k ≤ n →
        ∃ (t : ℕ) (A bad : Finset BitString),
          A = (t3BoundaryDRun c n k epsilon delta t).current.toFinset ∧
          bad = ((t3BoundaryDRun c n k epsilon delta t).current.filter
                  (fun x => (t1DStage c n k t).contains x)).toFinset ∧
          A ⊆ stringsOfLength n ∧
          A.card = 2 ^ (k - epsilon) ∧
          bad ⊆ A ∧
          bad.card < 2 ^ (k - epsilon - delta) ∧
          (∀ x ∈ A \ bad, (k : ENat) ≤ plainK V x) ∧
          (t3BoundaryDRun c n k epsilon delta t).rebuilds < 2 ^ (epsilon + delta) := by
  obtain ⟨c0, hlen⟩ := t3BoundaryDRun_current_length V hV
  refine ⟨c0, ?_⟩
  intro c hc n k epsilon delta hc0 hepsilon hdelta hkn
  obtain ⟨t, hcomplete, hnot⟩ :=
    exists_t3BoundaryD_terminal_stage hc n k epsilon delta hepsilon hdelta
  refine ⟨t, (t3BoundaryDRun c n k epsilon delta t).current.toFinset,
    ((t3BoundaryDRun c n k epsilon delta t).current.filter
      (fun x => (t1DStage c n k t).contains x)).toFinset,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact t3BoundaryDRun_current_subset_cube c n k epsilon delta t
  · rw [List.toFinset_card_of_nodup
      (t3BoundaryDRun_invariant c n k epsilon delta t).current_nodup]
    exact hlen hc n k epsilon delta t hc0 hepsilon hkn
  · intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact List.mem_of_mem_filter hx
  · have hcard :
        (((t3BoundaryDRun c n k epsilon delta t).current.filter
            (fun x => (t1DStage c n k t).contains x)).toFinset).card ≤
          ((t3BoundaryDRun c n k epsilon delta t).current.filter
            (fun x => (t1DStage c n k t).contains x)).length :=
      List.toFinset_card_le _
    have hlt :
        ((t3BoundaryDRun c n k epsilon delta t).current.filter
            (fun x => (t1DStage c n k t).contains x)).length <
          2 ^ (k - epsilon - delta) := by
      have hn := hnot
      simp only [t3BoundaryDQuotaReached, ge_iff_le, decide_eq_false_iff_not,
        not_le] at hn
      exact hn
    omega
  · intro x hx
    rw [Finset.mem_sdiff, List.mem_toFinset, List.mem_toFinset,
      List.mem_filter] at hx
    obtain ⟨hxcur, hxbad⟩ := hx
    have hxlen : x.length = n := by
      have hxcube : x ∈ stringsOfLength n :=
        t3BoundaryDRun_current_subset_cube c n k epsilon delta t
          (List.mem_toFinset.mpr hxcur)
      exact (memStringsOfLength n x).mp hxcube
    by_contra hlow
    exact hxbad ⟨hxcur, by simpa using hcomplete x hxlen (not_le.mp hlow)⟩
  · exact t3BoundaryD_rebuilds_lt hc n k epsilon delta t hepsilon hdelta

end Kolmogorov
