import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelTree
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings

/-!
# Finite stages of the a priori sublevel tree

`kaSublevel k` is a prefix-closed set of bitstrings.  For the address-assignment
construction one needs to exhaust it by an increasing sequence of *finite* sets.
Here we cut it by length: `kaSublevelStage k s` collects the members of
`kaSublevel k` of length at most `s`.  These stages are monotone in `s` and
their union is all of `kaSublevel k`.

We also record the counting facts needed to produce fresh addresses: there are
exactly `2 ^ k` bitstrings of length `k`, so any set of fewer than `2 ^ k`
strings misses one of them.
-/

noncomputable section

namespace Kolmogorov

open Classical in
/-- Stage `s` of the a priori sublevel tree: the elements of `kaSublevel k`
of length at most `s`. -/
noncomputable def kaSublevelStage (k s : ℕ) : Finset BitString :=
  ((Finset.range (s + 1)).biUnion levelFinset).filter (fun x => x ∈ kaSublevel k)

/-- The stage-`s` approximation of the `k`-th sublevel consists of its members of length at most
`s`. -/
lemma mem_kaSublevelStage {k s : ℕ} {x : BitString} :
    x ∈ kaSublevelStage k s ↔ x.length ≤ s ∧ x ∈ kaSublevel k := by
  classical
  simp only [kaSublevelStage, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    mem_levelFinset]
  constructor
  · rintro ⟨⟨n, hn, hx⟩, hmem⟩
    exact ⟨by omega, hmem⟩
  · rintro ⟨hlen, hmem⟩
    exact ⟨⟨x.length, by omega, rfl⟩, hmem⟩

/-- The stage approximations of a sublevel grow with the stage. -/
lemma kaSublevelStage_subset {k s t : ℕ} (hst : s ≤ t) :
    kaSublevelStage k s ⊆ kaSublevelStage k t := by
  intro x hx
  rw [mem_kaSublevelStage] at hx ⊢
  exact ⟨hx.1.trans hst, hx.2⟩

/-- Each stage approximation of a sublevel is contained in the next. -/
lemma kaSublevelStage_mono {k s : ℕ} : kaSublevelStage k s ⊆ kaSublevelStage k (s + 1) :=
  kaSublevelStage_subset (Nat.le_succ s)

/-- Every stage approximation is contained in the sublevel it approximates. -/
lemma kaSublevelStage_subset_kaSublevel {k s : ℕ} :
    (kaSublevelStage k s : Set BitString) ⊆ kaSublevel k := by
  intro x hx
  exact (mem_kaSublevelStage.1 (by exact_mod_cast hx)).2

/-- The stage approximations exhaust the sublevel. -/
lemma iUnion_kaSublevelStage_eq (k : ℕ) :
    ⋃ s, ((kaSublevelStage k s : Finset BitString) : Set BitString) = kaSublevel k := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_coe, mem_kaSublevelStage]
  constructor
  · rintro ⟨s, -, hx⟩
    exact hx
  · intro hx
    exact ⟨x.length, le_rfl, hx⟩

/-- Every stage of the sublevel tree is prefix-closed. -/
lemma kaSublevelStage_prefixClosed {k s : ℕ} {x y : BitString}
    (hxy : x <+: y) (hy : y ∈ kaSublevelStage k s) : x ∈ kaSublevelStage k s := by
  rw [mem_kaSublevelStage] at hy ⊢
  refine ⟨le_trans ?_ hy.1, kaSublevel_prefixClosed hxy hy.2⟩
  exact hxy.length_le

/-- There are exactly `2 ^ n` bitstrings of length `n`. -/
lemma card_levelFinset (n : ℕ) : (levelFinset n).card = 2 ^ n := by
  classical
  induction n with
  | zero => simp [levelFinset, levelList]
  | succ n ih =>
      have hcard : (levelFinset (n + 1)).card = (levelList (n + 1)).length := by
        rw [levelFinset, List.toFinset_card_of_nodup (nodup_levelList (n + 1))]
      have hlen : (levelList (n + 1)).length = 2 * (levelList n).length := by
        simp [levelList, two_mul]
      have hn : (levelList n).length = (levelFinset n).card := by
        rw [levelFinset, List.toFinset_card_of_nodup (nodup_levelList n)]
      rw [hcard, hlen, hn, ih]
      ring

open Classical in
/-- The sublevel tree `kaSublevel k` has at most `2 ^ k` nodes on each level:
same-length strings form a prefix antichain, so the Kraft bound applies. -/
lemma kaSublevel_level_card_le (k n : ℕ) :
    ((levelFinset n).filter (fun x => x ∈ kaSublevel k)).card ≤ 2 ^ k := by
  classical
  refine kaSublevel_card_le_pow _ (fun x hx => (Finset.mem_filter.1 hx).2) ?_
  intro x hx y hy hxy
  have hxn : x.length = n := mem_levelFinset.1 (Finset.mem_filter.1 hx).1
  have hyn : y.length = n := mem_levelFinset.1 (Finset.mem_filter.1 hy).1
  exact hxy.eq_of_length (by omega)

open Classical in
/-- Each stage is finite with an explicit size bound. -/
lemma kaSublevelStage_card_le (k s : ℕ) :
    (kaSublevelStage k s).card ≤ (s + 1) * 2 ^ k := by
  classical
  have hsub : kaSublevelStage k s ⊆
      (Finset.range (s + 1)).biUnion
        (fun n => (levelFinset n).filter (fun x => x ∈ kaSublevel k)) := by
    intro x hx
    rw [mem_kaSublevelStage] at hx
    exact Finset.mem_biUnion.2 ⟨x.length, Finset.mem_range.2 (by omega),
      Finset.mem_filter.2 ⟨mem_levelFinset.2 rfl, hx.2⟩⟩
  calc (kaSublevelStage k s).card
      ≤ ((Finset.range (s + 1)).biUnion
          (fun n => (levelFinset n).filter (fun x => x ∈ kaSublevel k))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ n ∈ Finset.range (s + 1),
          ((levelFinset n).filter (fun x => x ∈ kaSublevel k)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _n ∈ Finset.range (s + 1), 2 ^ k :=
        Finset.sum_le_sum (fun n _ => kaSublevel_level_card_le k n)
    _ = (s + 1) * 2 ^ k := by simp

/-- If fewer than `2 ^ k` strings have been used up, some bitstring of length `k`
is still free. -/
lemma exists_fresh_address {k : ℕ} (assigned : Finset BitString)
    (hsize : assigned.card < 2 ^ k) :
    ∃ a : BitString, a.length = k ∧ a ∉ assigned := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : levelFinset k ⊆ assigned := by
    intro a ha
    exact hcon a (mem_levelFinset.1 ha)
  have := Finset.card_le_card hsub
  rw [card_levelFinset] at this
  omega

end Kolmogorov
