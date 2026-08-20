import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingPredicates
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation

/-!
# Static union bound for the strange-string marking construction

This file connects the extensional marking predicates `T1BMarked`, `T1CMarked`,
`T1DMarked` (defined in `T1MarkingPredicates.lean`) to the already-proved finite
counting core `t1_marked_union_count_lt_half` (in `Separation.lean`).

The main result, `t1_marked_predicates_card_lt_half`, is the source's feasibility
statement: *"the family `B ∪ C ∪ D` covers at most `2^(ε+1)·2^(n-ε-4) +
2^(k+1)·2^(n-k-4) + 2^k < 2^(n-1)` strings, hence at least half of the `n`-bit
cube is non-covered."*  It is the exact premise consumed by the marking run's
availability step (`t1_current_unmarked_card_ge_half` in the strategic plan): at
every rebuild there are at least `2^(n-1)` currently unmarked length-`n` strings.

The counting is honest: the number of *distinct* finite models of plain
complexity at most `ε` is bounded by the number of length-`≤ ε` programs
(`cardCompressibleWordsLt`), because the canonical uniform code is injective on
finite sets; each such model has at most `2^(n-ε-4)` elements.  The `C`-family
bound drops the extra description-profile condition (it only shrinks the family),
exactly as in the source.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Recover a finite set from a canonical distribution code by reading its data
points.  It is a left inverse of `fun S => (codedUniformOn S _).code`. -/
noncomputable def t1CodeToSet (w : BitString) : Finset BitString :=
  ((decodeDistributionData w).map CodedDistributionEntry.point).toFinset

/-- `t1CodeToSet` inverts the canonical uniform code of a nonempty finite set. -/
theorem t1CodeToSet_codedUniformOn (B : Finset BitString) (hB : B.Nonempty) :
    t1CodeToSet (codedUniformOn B hB).code = B := by
  unfold t1CodeToSet
  rw [dataPoints_codedUniformOn, canonicalFinsetList_toFinset]

/-- A string of conditional complexity at most `ε` occurs in the finite set of
compressible words.  This is the membership half implicit in
`existsIncompressibleString`, isolated for reuse. -/
private theorem mem_compressibleWords_of_condK_le
    {V : Map} {w y : BitString} {ε : ℕ} (h : condK V w y ≤ (ε : ENat)) :
    w ∈ compressibleWords V y ε := by
  obtain ⟨p, hlen, hprod⟩ := (condKLeIff V w y ε).mp h
  unfold compressibleWords
  rw [Finset.mem_filter]
  refine ⟨?_, h⟩
  unfold generatedWords
  rw [List.mem_toFinset, List.mem_filterMap]
  exact ⟨p, mem_programsLe ε p hlen, progToOut_eq_some.mpr hprod⟩

/-- **Family cardinality bound.**  If every element of a finite set `M` lies in
some finite model of plain complexity at most `ε` and cardinality at most
`bound`, then `M` has at most `#{compressible codes of budget ε} · bound`
elements.  No dependence on the ambient length: the number of distinct low
complexity models is what limits the union. -/
theorem t1_family_marked_card_le (V : Map) (ε bound : Nat)
    (M : Finset BitString)
    (hM : ∀ x ∈ M, ∃ (B : Finset BitString) (hB : B.Nonempty),
        x ∈ B ∧ plainSetComplexity V B hB ≤ (ε : ENat) ∧ B.card ≤ bound) :
    M.card ≤ (compressibleWords V [] ε).card * bound := by
  classical
  set goodCodes :=
    (compressibleWords V [] ε).filter (fun w => (t1CodeToSet w).card ≤ bound)
    with hgood
  have hsub : M ⊆ goodCodes.biUnion t1CodeToSet := by
    intro x hx
    obtain ⟨B, hB, hxB, hcomp, hcard⟩ := hM x hx
    have hcode_low : condK V (codedUniformOn B hB).code [] ≤ (ε : ENat) := hcomp
    have hmemc : (codedUniformOn B hB).code ∈ compressibleWords V [] ε :=
      mem_compressibleWords_of_condK_le hcode_low
    have hfw : t1CodeToSet (codedUniformOn B hB).code = B :=
      t1CodeToSet_codedUniformOn B hB
    have hgc : (codedUniformOn B hB).code ∈ goodCodes := by
      rw [hgood, Finset.mem_filter]
      exact ⟨hmemc, by rw [hfw]; exact hcard⟩
    rw [Finset.mem_biUnion]
    exact ⟨(codedUniformOn B hB).code, hgc, by rw [hfw]; exact hxB⟩
  calc
    M.card ≤ (goodCodes.biUnion t1CodeToSet).card := Finset.card_le_card hsub
    _ ≤ ∑ w ∈ goodCodes, (t1CodeToSet w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ goodCodes, bound := by
        apply Finset.sum_le_sum
        intro w hw
        rw [hgood, Finset.mem_filter] at hw
        exact hw.2
    _ = goodCodes.card * bound := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (compressibleWords V [] ε).card * bound := by
        have hle : goodCodes.card ≤ (compressibleWords V [] ε).card := by
          rw [hgood]; apply Finset.card_filter_le
        gcongr

/-- **Low-complexity cardinality bound.**  A finite set of strings each of plain
complexity strictly below `k` has at most `2^k` elements. -/
theorem t1_lowComplexity_card_le (V : Map) (k : Nat) (M : Finset BitString)
    (hM : ∀ x ∈ M, plainK V x < (k : ENat)) :
    M.card ≤ 2 ^ k := by
  cases k with
  | zero =>
      rcases M.eq_empty_or_nonempty with hE | ⟨x, hx⟩
      · simp [hE]
      · exact absurd (hM x hx) (by simp)
  | succ k =>
      have hsub : M ⊆ compressibleWords V [] k := by
        intro x hx
        have hlt : condK V x [] < (((k + 1 : ℕ)) : ENat) := hM x hx
        have hne : condK V x [] ≠ ⊤ := ne_top_of_lt hlt
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
        have hle : condK V x [] ≤ (k : ENat) := by
          rw [← hm] at hlt ⊢
          have hmk : m < k + 1 := by exact_mod_cast hlt
          exact_mod_cast Nat.lt_succ_iff.mp hmk
        exact mem_compressibleWords_of_condK_le hle
      exact (Finset.card_le_card hsub).trans
        (le_of_lt (cardCompressibleWordsLt V [] k))

/-- **Static union bound for the marking construction (feasibility).**

Let `M` be any finite set of strings, each of which is `b`-marked, `c`-marked
(for some description budget `d`), or `d`-marked in the sense of the strange
string construction.  If `ε + 4 ≤ n` and `k + 4 ≤ n`, then `M` has fewer than
`2^(n-1)` elements.

Consequently, whenever `M ⊆ stringsOfLength n`, at least `2^(n-1)` length-`n`
strings avoid all three marked families, so the marking run always has a fresh
element to select.  The `c`-disjunct is quantified over `d`, so it subsumes the
run's fixed budget `d = ε + O(log n)`. -/
theorem t1_marked_predicates_card_lt_half (V : Map) (n k ε : Nat)
    (hεn : ε + 4 ≤ n) (hkn : k + 4 ≤ n)
    (M : Finset BitString)
    (hM : ∀ x ∈ M,
      T1BMarked V n ε x ∨ (∃ d, T1CMarked V n k d x) ∨ T1DMarked V n k x) :
    M.card < 2 ^ (n - 1) := by
  classical
  have hcover : M ⊆
      M.filter (fun x => T1BMarked V n ε x) ∪
        (M.filter (fun x => ∃ d, T1CMarked V n k d x) ∪
          M.filter (fun x => T1DMarked V n k x)) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases hM x hx with hb | hc | hd
    · exact Or.inl ⟨hx, hb⟩
    · exact Or.inr (Or.inl ⟨hx, hc⟩)
    · exact Or.inr (Or.inr ⟨hx, hd⟩)
  have hcardB :
      (M.filter (fun x => T1BMarked V n ε x)).card ≤
        2 ^ (ε + 1) * 2 ^ (n - ε - 4) := by
    have h := t1_family_marked_card_le V ε (2 ^ (n - ε - 4))
      (M.filter (fun x => T1BMarked V n ε x)) (fun x hx => by
        obtain ⟨_, B, hB, hxB, hcomp, hcard⟩ := (Finset.mem_filter.mp hx).2
        exact ⟨B, hB, hxB, hcomp, hcard⟩)
    have hcw : (compressibleWords V [] ε).card ≤ 2 ^ (ε + 1) :=
      le_of_lt (cardCompressibleWordsLt V [] ε)
    refine h.trans ?_
    gcongr
  have hcardC :
      (M.filter (fun x => ∃ d, T1CMarked V n k d x)).card ≤
        2 ^ (k + 1) * 2 ^ (n - k - 4) := by
    have h := t1_family_marked_card_le V k (2 ^ (n - k - 4))
      (M.filter (fun x => ∃ d, T1CMarked V n k d x)) (fun x hx => by
        obtain ⟨d, _, M', hM', hxM', hcomp, hcard, _⟩ := (Finset.mem_filter.mp hx).2
        exact ⟨M', hM', hxM', hcomp, hcard⟩)
    have hcw : (compressibleWords V [] k).card ≤ 2 ^ (k + 1) :=
      le_of_lt (cardCompressibleWordsLt V [] k)
    refine h.trans ?_
    gcongr
  have hcardD :
      (M.filter (fun x => T1DMarked V n k x)).card ≤ 2 ^ k := by
    apply t1_lowComplexity_card_le V k (M.filter (fun x => T1DMarked V n k x))
    intro x hx
    exact (Finset.mem_filter.mp hx).2.2
  calc
    M.card ≤ (M.filter (fun x => T1BMarked V n ε x) ∪
        (M.filter (fun x => ∃ d, T1CMarked V n k d x) ∪
          M.filter (fun x => T1DMarked V n k x))).card :=
      Finset.card_le_card hcover
    _ ≤ (M.filter (fun x => T1BMarked V n ε x)).card +
          (M.filter (fun x => ∃ d, T1CMarked V n k d x) ∪
            M.filter (fun x => T1DMarked V n k x)).card :=
      Finset.card_union_le _ _
    _ ≤ (M.filter (fun x => T1BMarked V n ε x)).card +
          ((M.filter (fun x => ∃ d, T1CMarked V n k d x)).card +
            (M.filter (fun x => T1DMarked V n k x)).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ 2 ^ (ε + 1) * 2 ^ (n - ε - 4) +
          (2 ^ (k + 1) * 2 ^ (n - k - 4) + 2 ^ k) :=
      Nat.add_le_add hcardB (Nat.add_le_add hcardC hcardD)
    _ = 2 ^ (ε + 1) * 2 ^ (n - ε - 4) +
          2 ^ (k + 1) * 2 ^ (n - k - 4) + 2 ^ k := by ring
    _ < 2 ^ (n - 1) := t1_marked_union_count_lt_half n k ε hεn hkn

/-- **Availability for the marking run.**  If every marked string is `b`-, `c`-,
or `d`-marked, then at least `2^(n-1)` length-`n` strings are unmarked.  This is
the exact premise the chronological rebuild step needs: there is always a fresh
`2^(k-ε)`-element cube to select from (since `2^(k-ε) ≤ 2^(n-1)`). -/
theorem t1_unmarked_card_ge_half (V : Map) (n k ε : Nat)
    (hεn : ε + 4 ≤ n) (hkn : k + 4 ≤ n)
    (Marked : Finset BitString)
    (hMarked : ∀ x ∈ Marked,
      T1BMarked V n ε x ∨ (∃ d, T1CMarked V n k d x) ∨ T1DMarked V n k x) :
    2 ^ (n - 1) ≤ (stringsOfLength n \ Marked).card := by
  have hlt := t1_marked_predicates_card_lt_half V n k ε hεn hkn Marked hMarked
  have hge : (stringsOfLength n).card - Marked.card ≤ (stringsOfLength n \ Marked).card :=
    Finset.le_card_sdiff Marked (stringsOfLength n)
  rw [cardStringsOfLength] at hge
  have hsplit : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  omega

/-- Canonical list presentation of the currently unmarked length-`n` universe.
These are the three bookkeeping facts required by the total sparse selector:
no duplicates, exact extensional contents, and exact list length. -/
theorem t1_unmarked_list_spec (n : Nat) (Marked : Finset BitString) :
    let U := canonicalFinsetList (stringsOfLength n \ Marked)
    U.Nodup ∧
      U.toFinset = stringsOfLength n \ Marked ∧
      U.length = (stringsOfLength n \ Marked).card := by
  dsimp
  exact ⟨canonicalFinsetList_nodup _,
    canonicalFinsetList_toFinset _,
    length_canonicalFinsetList _⟩

end Kolmogorov
