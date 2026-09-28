import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Foundation.UnboundedSearch
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaPrefix.Part01
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.Position

/-!
# Dovetailing over programs and stages

This file is the entry point for every construction that needs to **enumerate all strings
of complexity at most `m`** — the strings of **bounded complexity**, the
**low-complexity strings**, the strings with `plainK ≤ m` — to **decide compressibility
in the limit**, or to **dovetail over programs and stages**.  The engine for all three
already exists in this library; it is indexed below so that it is *found* rather than
rebuilt.  Anything you are tempted to write with `evaln`, `boundedPrograms` and a step
counter is almost certainly one of the declarations listed here.

## Index of the existing engine

`KolmogorovMathlib/AlgorithmicStatistics/Selector.lean`:
* `IsCodeFor c U` — the code `c` computes the map `U` (via the encode/decode graph).
* `runOut c t p`, `haltsWithin c t p` — one program, one step budget.
* `countHalts c m t`, `snapshotCodes c m t` — one dovetailing round: all programs of
  length `≤ m` run for `t` steps, with their halting count and their outputs.
* `exists_max_countHalts` — the halting count is eventually maximal, so the round-by-round
  enumeration stabilizes.
* `list_any_primrec`, `list_find?_primrec` — primitive recursive list combinators.

`KolmogorovMathlib/AlgorithmicStatistics/BoundedLists/Basic.lean`:
* `boundedOutputStage c m t` — **the** bounded-complexity list: the outputs of programs of
  length `≤ m` produced within `t` steps, in order of first appearance, duplicates removed.
* `boundedOutputStage_nodup`, `boundedOutputStage_prefix`, `boundedOutputStage_prefix_of_le`
  — no repetitions, and prefix monotonicity in the stage.
* `boundedOutputStage_primrec`, `boundedOutputStage_computable` — the stage list is
  primitive recursive in `(m, t)`.
* `completedBoundedOutput c m`, `completedBoundedOutputFinset c m` — the limit list and
  finset (noncomputable).
* `boundedOutputCompletionTime c m` — the least stage at which the limit is reached, with
  `boundedOutputCompletionTime_spec`, `boundedOutputCompletionTime_le_complete_stage`,
  `boundedOutputStage_eq_completed_at_completion`,
  `boundedOutputStage_eq_completed_of_completion_le` and
  `boundedOutputStage_prefix_completed`.
* `mem_completedBoundedOutput_iff_plainK_le` — **the central bridge**:
  `x ∈ completedBoundedOutput c m ↔ plainK U x ≤ m`, for any `IsCodeFor c U`.

`KolmogorovMathlib/AlgorithmicStatistics/BoundedLists/Position.lean`:
* `boundedOutputEnumeration c m : StagedEnumeration` — the stage list packaged as a staged
  enumeration (per-`m` constants only; see the warning in that file).

`KolmogorovMathlib/Foundation/EnumerationComplexity.lean`:
* `StagedEnumeration` (fields `enum`, `computable`, `mono`) and the index-to-complexity
  theorems `KPPlain_le_log_index_of_enumeration`,
  `KP_le_log_index_of_cond_enumeration`, `setComplexity_le_log_index_of_enumeration`.

`KolmogorovMathlib/Foundation/RecursivelyEnumerable.lean`:
* `IsRE`, `IsCoRE`, and `IsRE.existsInList` (bounded existential search over an RE
  relation, itself proved by dovetailing).
* `exactLengthPrograms n`, `boundedPrograms N`, `primrec_exactLengthPrograms`.

`KolmogorovMathlib/Foundation/UnboundedSearch.lean`:
* `Computable.natFind` — a total decidable unbounded search is computable.

## What this file adds

* `exists_isCodeFor` — the `Partrec`-to-`Code` bridge, previously copy-pasted at six call
  sites as `Nat.Partrec.Code.exists_code.mp hU.1`.
* `isRE_plainK_le` — `{x | plainK U x ≤ m}` is recursively enumerable, read straight off
  the staged enumeration.  This is "compressibility is decidable in the limit".
* the count-as-advice witness: `lengthSlice`, `sliceCount`, `firstStageWithCount`,
  `firstMissing` and `plainK_firstMissing_gt`.  Given the exact number of length-`n`
  strings of complexity `≤ m` as advice, one obtains a *specific* length-`n` string of
  complexity `> m`; this is the shape used by the counting arguments of SUV problems 53,
  250 and 364.  `firstMissing` is declared `noncomputable`; see the docstring of
  `firstStageWithCount` for what is and is not being claimed about that.  Its
  computational content is `missingSearch`, a partial recursive search whose domain is
  pinned down by `missingSearch_dom_iff`.
* `adviceCode`, `missingSelector` and `condK_firstMissing_le` — the advice triple
  `(m, n, N)` packed into one self-delimiting condition string, the partial recursive
  selector that parses it and runs `missingSearch`, and the resulting
  `condK V (firstMissing c m n N) (adviceCode m n N) ≤ C` for a constant `C` depending
  only on `V` and `c`.  Together with `plainK_firstMissing_gt` this is the object the
  counting arguments of SUV problems 53(b), 250 and 364 ask for: a length-`n` string of
  plain complexity `> m` that is `O(1)` given the advice.
-/

namespace Kolmogorov.Dovetailing

open Nat.Partrec (Code)

/-! ### The `Partrec`-to-`Code` bridge -/

/-- Every optimal conditional decompressor has a `Nat.Partrec.Code`.  This is the bridge
`Nat.Partrec.Code.exists_code.mp hU.1`, which the library used to inline at every use. -/
theorem exists_isCodeFor {U : Map} (hU : isOptimalConditional U) :
    ∃ c : Code, IsCodeFor c U :=
  Nat.Partrec.Code.exists_code.mp hU.1

/-! ### Compressibility in the limit -/

/-- Membership in the stage-`t` bounded-complexity list is computable in the string and
the stage. -/
theorem computable_mem_boundedOutputStage (c : Code) (m : ℕ) :
    Computable₂ (fun (x : BitString) (t : ℕ) => decide (x ∈ boundedOutputStage c m t)) :=
  bitString_mem_primrec.to_comp.comp Computable.fst
    ((boundedOutputStage_computable c).comp
      (Computable.pair (Computable.const m) Computable.snd))

/-- A string turns up at some stage of the bound-`m` enumeration exactly when its plain
complexity is at most `m`. -/
theorem exists_stage_mem_iff_plainK_le {U : Map} {c : Code} (hc : IsCodeFor c U)
    (m : ℕ) (x : BitString) :
    (∃ t, x ∈ boundedOutputStage c m t) ↔ plainK U x ≤ (m : ENat) := by
  constructor
  · rintro ⟨t, ht⟩
    exact (mem_completedBoundedOutput_iff_plainK_le hc m x).mp
      ((boundedOutputStage_prefix_completed c m t).sublist.subset ht)
  · intro hx
    refine ⟨boundedOutputCompletionTime c m, ?_⟩
    rw [boundedOutputStage_eq_completed_at_completion c m]
    exact (mem_completedBoundedOutput_iff_plainK_le hc m x).mpr hx

/-- **Compressibility is decidable in the limit.**  The set of strings of plain complexity
at most `m` — the strings of **bounded complexity**, the **low-complexity strings**, the
**strings with `plainK ≤ m`** — is recursively enumerable: dovetail over stages and wait
for the string to appear in `boundedOutputStage c m t`. -/
theorem isRE_plainK_le {U : Map} {c : Code} (hc : IsCodeFor c U) (m : ℕ) :
    IsRE (fun x : BitString => plainK U x ≤ (m : ENat)) := by
  have hp2 : Partrec₂ (fun (x : BitString) (t : ℕ) =>
      (Part.some (decide (x ∈ boundedOutputStage c m t)) : Part Bool)) :=
    (computable_mem_boundedOutputStage c m).partrec₂
  refine ⟨fun x => (Nat.rfind fun t =>
    Part.some (decide (x ∈ boundedOutputStage c m t))).map (fun _ => ()), ?_, ?_⟩
  · exact (Partrec.rfind hp2).map (Computable.const ()).to₂
  · intro x
    change (Nat.rfind fun t =>
      Part.some (decide (x ∈ boundedOutputStage c m t))).Dom ↔ plainK U x ≤ (m : ENat)
    rw [Nat.rfind_dom, ← exists_stage_mem_iff_plainK_le hc m x]
    constructor
    · rintro ⟨t, ht, -⟩
      exact ⟨t, of_decide_eq_true (Part.mem_some_iff.mp ht).symm⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, Part.mem_some_iff.mpr (decide_eq_true ht).symm, fun _ => Part.some_dom _⟩

/-! ### The count-as-advice witness -/

/-- The entries of the stage-`t` bounded-complexity list whose length is exactly `n`:
the length-`n` **low-complexity strings** discovered so far.  Relative to a machine `U`
with `IsCodeFor c U` the limit of these slices is the set of length-`n` **strings with
`plainK ≤ m`** (`mem_completedLengthSlice_iff`). -/
def lengthSlice (c : Code) (m n t : ℕ) : List BitString :=
  (boundedOutputStage c m t).filter (fun x => decide (x.length = n))

/-- Membership in a stage slice. -/
theorem mem_lengthSlice {c : Code} {m n t : ℕ} {x : BitString} :
    x ∈ lengthSlice c m n t ↔ x ∈ boundedOutputStage c m t ∧ x.length = n := by
  simp [lengthSlice, List.mem_filter]

/-- The slice is primitive recursive in the bound, the length and the stage. -/
theorem lengthSlice_primrec (c : Code) :
    Primrec (fun p : ℕ × ℕ × ℕ => lengthSlice c p.1 p.2.1 p.2.2) := by
  have hlist : Primrec (fun p : ℕ × ℕ × ℕ => boundedOutputStage c p.1 p.2.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
  have hpred : Primrec₂
      (fun (p : ℕ × ℕ × ℕ) (x : BitString) => decide (x.length = p.2.1)) := by
    have hbeq : Primrec (fun q : (ℕ × ℕ × ℕ) × BitString => q.2.length == q.1.2.1) :=
      Primrec.beq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    exact hbeq.of_eq (fun q => Bool.beq_eq_decide_eq _ _)
  exact list_filter_primrec hlist hpred

/-- The limit of the length-`n` slices: the length-`n` entries of
`completedBoundedOutput c m`, i.e. every length-`n` string that the code `c` ever emits
from a program of length `≤ m`.

As a definition this speaks about `c` only: it filters the completed output list, and
no notion of complexity is built into it.  The reading as the length-`n` strings of
**bounded complexity** — the **low-complexity strings**, the **strings with
`plainK ≤ m`** — is available only *relative to a machine* `U` together with
`IsCodeFor c U`, and that reading is exactly `mem_completedLengthSlice_iff`. -/
noncomputable def completedLengthSlice (c : Code) (m n : ℕ) : List BitString :=
  (completedBoundedOutput c m).filter (fun x => decide (x.length = n))

/-- The number of entries of `completedLengthSlice c m n`.

Like `completedLengthSlice`, this counts completed outputs of the code `c` and by itself
says nothing about complexity.  It is the number of length-`n` strings of **bounded
complexity** — of **low-complexity strings**, of **strings with `plainK ≤ m`** — only
relative to a machine `U` with `IsCodeFor c U`, through
`mem_completedLengthSlice_iff`. -/
noncomputable def sliceCount (c : Code) (m n : ℕ) : ℕ :=
  (completedLengthSlice c m n).length

/-- `sliceCount` unfolded. -/
@[simp] theorem sliceCount_eq_length (c : Code) (m n : ℕ) :
    sliceCount c m n = (completedLengthSlice c m n).length := rfl

/-- The completed slice is exactly the set of length-`n` strings of complexity `≤ m`. -/
theorem mem_completedLengthSlice_iff {U : Map} {c : Code} (hc : IsCodeFor c U) (m n : ℕ)
    (x : BitString) :
    x ∈ completedLengthSlice c m n ↔ plainK U x ≤ (m : ENat) ∧ x.length = n := by
  unfold completedLengthSlice
  rw [List.mem_filter, mem_completedBoundedOutput_iff_plainK_le hc]
  simp only [decide_eq_true_eq]

/-- Every stage slice is a prefix of the completed slice. -/
theorem lengthSlice_prefix_completed (c : Code) (m n t : ℕ) :
    lengthSlice c m n t <+: completedLengthSlice c m n := by
  obtain ⟨r, hr⟩ := boundedOutputStage_prefix_completed c m t
  refine ⟨r.filter (fun x => decide (x.length = n)), ?_⟩
  unfold lengthSlice completedLengthSlice
  rw [← hr, List.filter_append]

/-- Past the completion time of the bound-`m` enumeration the slice has settled. -/
theorem lengthSlice_eq_completed_of_completion_le (c : Code) (m n t : ℕ)
    (hle : boundedOutputCompletionTime c m ≤ t) :
    lengthSlice c m n t = completedLengthSlice c m n := by
  unfold lengthSlice completedLengthSlice
  rw [boundedOutputStage_eq_completed_of_completion_le c m t hle]

/-- With the true count as the target, the stage search does terminate. -/
theorem exists_stage_with_sliceCount (c : Code) (m n : ℕ) :
    ∃ t, sliceCount c m n ≤ (lengthSlice c m n t).length := by
  refine ⟨boundedOutputCompletionTime c m, ?_⟩
  rw [lengthSlice_eq_completed_of_completion_le c m n _ le_rfl]
  exact Nat.le_of_eq (sliceCount_eq_length c m n)

open Classical in
/-- The least stage whose length-`n` slice has at least `N` entries, and `0` when no
stage ever does.

Why the definition is `noncomputable`.  It picks the stage by `Nat.find` applied to an
unbounded `Σ₁` condition.  No total computable stage selector meeting this specification
exists uniformly in arbitrary codes, and for a universal code such a selector would
decide a halting-equivalent reachability predicate.  Both halves matter: for a single
fixed code the claim can fail outright — for a code that never outputs anything the
constant-`0` selector is correct and computable — and turning the reachability predicate
"some program of length `≤ m` eventually outputs `N` strings of length exactly `n`" into
the halting problem is an argument about the code, not an immediate identification.  This
is why the definition is `noncomputable`; the computable content lives in
`computable_firstMissingAtStage` and `partrec_missingSearch`, with the exact domain of
the search given by `missingSearch_dom_iff`.

None of the preceding paragraph is formalised here: it is prose explaining a modifier,
not a theorem.  In particular nothing is claimed about `firstMissing` itself, whose
value need not reveal whether the target stage was reachable. -/
noncomputable def firstStageWithCount (c : Code) (m n N : ℕ) : ℕ :=
  if h : ∃ t, N ≤ (lengthSlice c m n t).length then Nat.find h else 0

/-- The stage found by `firstStageWithCount` does have `N` entries, provided some stage
does. -/
theorem firstStageWithCount_spec {c : Code} {m n N : ℕ}
    (hex : ∃ t, N ≤ (lengthSlice c m n t).length) :
    N ≤ (lengthSlice c m n (firstStageWithCount c m n N)).length := by
  unfold firstStageWithCount
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- Minimality of the stage found by `firstStageWithCount`. -/
theorem firstStageWithCount_min {c : Code} {m n N : ℕ}
    (hex : ∃ t, N ≤ (lengthSlice c m n t).length) {k : ℕ}
    (hk : k < firstStageWithCount c m n N) :
    ¬ N ≤ (lengthSlice c m n k).length := by
  unfold firstStageWithCount at hk
  rw [dif_pos hex] at hk
  exact Nat.find_min hex hk

/-- At the first stage carrying `sliceCount c m n` length-`n` strings, the stage slice is already
the completed slice:
`lengthSlice c m n (firstStageWithCount c m n (sliceCount c m n)) = completedLengthSlice c m n`.
This is an equality of lists for the given code `c`; no optimality of `c` is assumed. -/
theorem lengthSlice_firstStageWithCount (c : Code) (m n : ℕ) :
    lengthSlice c m n (firstStageWithCount c m n (sliceCount c m n))
      = completedLengthSlice c m n := by
  have hex := exists_stage_with_sliceCount c m n
  have hpre := lengthSlice_prefix_completed c m n
    (firstStageWithCount c m n (sliceCount c m n))
  refine hpre.eq_of_length (Nat.le_antisymm hpre.length_le ?_)
  rw [← sliceCount_eq_length]
  exact firstStageWithCount_spec hex

/-- The least length-`n` bitstring, in the order of `exactLengthPrograms n`, that is
missing from the stage-`t` slice; the all-zero string if none is missing. -/
def firstMissingAtStage (c : Code) (m n t : ℕ) : BitString :=
  ((exactLengthPrograms n).find?
    (fun x => decide (x ∉ lengthSlice c m n t))).getD (List.replicate n false)

/-- The witness has length `n`, whether or not one was actually found. -/
theorem firstMissingAtStage_length (c : Code) (m n t : ℕ) :
    (firstMissingAtStage c m n t).length = n := by
  have h : ∀ o : Option BitString, (∀ w, o = some w → w ∈ exactLengthPrograms n) →
      (o.getD (List.replicate n false)).length = n := by
    intro o ho
    cases o with
    | none => simp
    | some w => exact exactLengthPrograms_length_eq n w (ho w rfl)
  exact h _ (fun _ hw => List.mem_of_find?_eq_some hw)

/-- If some length-`n` string is missing from the stage-`t` slice, the returned witness
is one. -/
theorem firstMissingAtStage_not_mem {c : Code} {m n t : ℕ}
    (hex : ∃ x ∈ exactLengthPrograms n, x ∉ lengthSlice c m n t) :
    firstMissingAtStage c m n t ∉ lengthSlice c m n t := by
  obtain ⟨x0, hx0mem, hx0miss⟩ := hex
  unfold firstMissingAtStage
  rcases hfind : (exactLengthPrograms n).find?
      (fun x => decide (x ∉ lengthSlice c m n t)) with _ | w
  · rw [List.find?_eq_none] at hfind
    have h0 := hfind x0 hx0mem
    simp only [decide_eq_true_eq] at h0
    exact absurd hx0miss h0
  · have hw := List.find?_some hfind
    simpa using hw

/-- The stage-indexed witness is primitive recursive in the bound, the length and the
stage. -/
theorem firstMissingAtStage_primrec (c : Code) :
    Primrec (fun p : ℕ × ℕ × ℕ => firstMissingAtStage c p.1 p.2.1 p.2.2) := by
  have hlist : Primrec (fun p : ℕ × ℕ × ℕ => exactLengthPrograms p.2.1) :=
    primrec_exactLengthPrograms.comp (Primrec.fst.comp Primrec.snd)
  have hmem : Primrec (fun q : (ℕ × ℕ × ℕ) × BitString =>
      decide (q.2 ∈ lengthSlice c q.1.1 q.1.2.1 q.1.2.2)) :=
    bitString_mem_primrec.comp Primrec.snd ((lengthSlice_primrec c).comp Primrec.fst)
  have hpred : Primrec₂ (fun (p : ℕ × ℕ × ℕ) (x : BitString) =>
      decide (x ∉ lengthSlice c p.1 p.2.1 p.2.2)) :=
    (Primrec.not.comp hmem).of_eq (fun q => by simp)
  have hdef : Primrec (fun p : ℕ × ℕ × ℕ => List.replicate p.2.1 false) := by
    have hmap : Primrec
        (fun p : ℕ × ℕ × ℕ => (List.range p.2.1).map (fun _ : ℕ => false)) :=
      Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const false).to₂
    exact hmap.of_eq (fun p => by simp [List.map_const', List.length_range])
  exact Primrec.option_getD.comp (list_find?_primrec hlist hpred) hdef

/-- The stage-indexed witness is computable in the bound, the length and the stage. -/
theorem computable_firstMissingAtStage (c : Code) :
    Computable (fun p : ℕ × ℕ × ℕ => firstMissingAtStage c p.1 p.2.1 p.2.2) :=
  (firstMissingAtStage_primrec c).to_comp

/-- With the count `N` as advice: the least length-`n` bitstring missing from the slice at
the first stage that carries `N` of them. -/
noncomputable def firstMissing (c : Code) (m n N : ℕ) : BitString :=
  firstMissingAtStage c m n (firstStageWithCount c m n N)

/-- The witness is a length-`n` string. -/
theorem firstMissing_length (c : Code) (m n N : ℕ) :
    (firstMissing c m n N).length = n :=
  firstMissingAtStage_length c m n (firstStageWithCount c m n N)

/-- **The witness lemma, at a fixed stage.**  If the stage-`t` slice has caught up with
the completed slice, and fewer than `2 ^ n` strings of length `n` have complexity `≤ m`,
then the witness returned at stage `t` has complexity `> m`. -/
theorem plainK_firstMissingAtStage_gt {U : Map} {c : Code} (hc : IsCodeFor c U) {m n t : ℕ}
    (hstage : lengthSlice c m n t = completedLengthSlice c m n)
    (hlt : sliceCount c m n < 2 ^ n) :
    (m : ENat) < plainK U (firstMissingAtStage c m n t) := by
  have hex : ∃ x ∈ exactLengthPrograms n, x ∉ lengthSlice c m n t := by
    by_contra hall
    push_neg at hall
    have hsub : exactLengthPrograms n ⊆ completedLengthSlice c m n := by
      intro x hx
      rw [← hstage]
      exact hall x hx
    have hle := ((exactLengthPrograms_nodup n).subperm hsub).length_le
    rw [length_exactLengthPrograms, ← sliceCount_eq_length] at hle
    exact absurd hlt (Nat.not_lt.mpr hle)
  have hmiss := firstMissingAtStage_not_mem hex
  rw [hstage] at hmiss
  have hlen := firstMissingAtStage_length c m n t
  refine not_le.mp (fun hK => hmiss ?_)
  exact (mem_completedLengthSlice_iff hc m n _).mpr ⟨hK, hlen⟩

/-- **With the true count as advice the witness really is incompressible.**  If `N` is the
number of length-`n` strings of plain complexity at most `m`, and not all `2 ^ n` strings
of length `n` are that simple, then `firstMissing c m n N` is a length-`n` string of plain
complexity greater than `m`.  This is the form used by the counting arguments of SUV
problems 53, 250 and 364. -/
theorem plainK_firstMissing_gt {U : Map} {c : Code} (hc : IsCodeFor c U) {m n N : ℕ}
    (hN : N = sliceCount c m n) (hlt : N < 2 ^ n) :
    (m : ENat) < plainK U (firstMissing c m n N) := by
  subst hN
  exact plainK_firstMissingAtStage_gt hc (lengthSlice_firstStageWithCount c m n) hlt

/-! ### The computational content: dovetailing with the count as advice -/

/-- The dovetailing search behind `firstMissing`: run stages until the length-`n` slice
carries `N` entries, then return the least length-`n` string missing from it.  Partial
recursive in `(m, n, N)` (`partrec_missingSearch`), and convergent exactly when some
stage carries `N` entries (`missingSearch_dom_iff`) — in particular for the true count
`N = sliceCount c m n` (`missingSearch_dom_sliceCount`). -/
def missingSearch (c : Code) : ℕ × ℕ × ℕ →. BitString := fun p =>
  (Nat.rfind fun t =>
      Part.some (decide (p.2.2 ≤ (lengthSlice c p.1 p.2.1 t).length))).map
    fun t => firstMissingAtStage c p.1 p.2.1 t

/-- The count-as-advice search is partial recursive. -/
theorem partrec_missingSearch (c : Code) : Partrec (missingSearch c) := by
  have hin : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => (q.1.1, q.1.2.1, q.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have hslice : Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ =>
      lengthSlice c q.1.1 q.1.2.1 q.2) :=
    Primrec.of_eq ((lengthSlice_primrec c).comp hin) (fun _ => rfl)
  have hcheck : Computable₂ (fun (p : ℕ × ℕ × ℕ) (t : ℕ) =>
      decide (p.2.2 ≤ (lengthSlice c p.1 p.2.1 t).length)) :=
    (Primrec.nat_le.decide.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_length.comp hslice)).to_comp
  have hval : Computable₂ (fun (p : ℕ × ℕ × ℕ) (t : ℕ) =>
      firstMissingAtStage c p.1 p.2.1 t) :=
    (Primrec.of_eq ((firstMissingAtStage_primrec c).comp hin) (fun _ => rfl)).to_comp
  exact Partrec.map (Partrec.rfind hcheck.partrec₂) hval

/-- **The domain of the search, exactly.**  `missingSearch c (m, n, N)` converges if and
only if some stage of the bound-`m` enumeration carries `N` strings of length `n`.  The
`Part.map` wrapper is transparent for domains, so this is the domain of the underlying
`Nat.rfind`. -/
theorem missingSearch_dom_iff (c : Code) (m n N : ℕ) :
    (missingSearch c (m, n, N)).Dom ↔ ∃ t, N ≤ (lengthSlice c m n t).length := by
  change (Nat.rfind fun t =>
    Part.some (decide (N ≤ (lengthSlice c m n t).length))).Dom ↔ _
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨t, ht, -⟩
    exact ⟨t, of_decide_eq_true (Part.mem_some_iff.mp ht).symm⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, Part.mem_some_iff.mpr (decide_eq_true ht).symm, fun _ => Part.some_dom _⟩

/-- The advice is always reachable for the true count, so the search converges there. -/
theorem missingSearch_dom_sliceCount (c : Code) (m n : ℕ) :
    (missingSearch c (m, n, sliceCount c m n)).Dom :=
  (missingSearch_dom_iff c m n _).mpr (exists_stage_with_sliceCount c m n)

/-- On the true count the search converges, and it converges to `firstMissing`. -/
theorem firstMissing_mem_missingSearch (c : Code) (m n : ℕ) :
    firstMissing c m n (sliceCount c m n) ∈ missingSearch c (m, n, sliceCount c m n) := by
  have hex := exists_stage_with_sliceCount c m n
  refine Part.mem_map_iff _ |>.mpr
    ⟨firstStageWithCount c m n (sliceCount c m n), ?_, rfl⟩
  rw [Nat.mem_rfind]
  refine ⟨Part.mem_some_iff.mpr (decide_eq_true (firstStageWithCount_spec hex)).symm, ?_⟩
  intro k hk
  exact Part.mem_some_iff.mpr (decide_eq_false (firstStageWithCount_min hex hk)).symm

/-! ### The advice as a condition: the witness is `O(1)` given the count -/

/-- The advice triple `(m, n, N)` packed into a single self-delimiting condition string:
`pairCode` applied to the binary expansions.  Primitive recursive
(`adviceCode_primrec`), and parsed back by `decodeAdvice`. -/
def adviceCode (m n N : ℕ) : BitString :=
  pairCode (Nat.bits m) (pairCode (Nat.bits n) (Nat.bits N))

/-- The advice string is primitive recursive in the triple. -/
theorem adviceCode_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ => adviceCode p.1 p.2.1 p.2.2) :=
  CodedFiniteDistribution.pairCode_primrec.comp (primrec_natBits.comp Primrec.fst)
    (CodedFiniteDistribution.pairCode_primrec.comp (primrec_natBits.comp (Primrec.fst.comp
      Primrec.snd))
      (primrec_natBits.comp (Primrec.snd.comp Primrec.snd)))

/-- Parsing an advice string back into the triple `(m, n, N)`. -/
def decodeAdvice (y : BitString) : ℕ × ℕ × ℕ :=
  (bitsToNat (decodeFirst y), bitsToNat (decodeFirst (decodeSecond y)),
    bitsToNat (decodeSecond (decodeSecond y)))

/-- The parser is primitive recursive. -/
theorem decodeAdvice_primrec : Primrec decodeAdvice :=
  (bitsToNat_primrec.comp CodedFiniteDistribution.decodeFirst_primrec).pair
    ((bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp
      CodedFiniteDistribution.decodeSecond_primrec)).pair
      (bitsToNat_primrec.comp (CodedFiniteDistribution.decodeSecond_primrec.comp
        CodedFiniteDistribution.decodeSecond_primrec)))

/-- Round trip: the condition string really does carry the advice triple. -/
@[simp] theorem decodeAdvice_adviceCode (m n N : ℕ) :
    decodeAdvice (adviceCode m n N) = (m, n, N) := by
  simp [decodeAdvice, adviceCode, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

/-- **The conditional selector.**  Parse the advice triple off the condition string and
run `missingSearch` on it.  The program argument is ignored, so the empty program already
suffices — which is what turns the bound of `condK_partrec_cond_map_le` into `O(1)`. -/
def missingSelector (c : Code) : BitString → BitString →. BitString :=
  fun y _ => missingSearch c (decodeAdvice y)

/-- The conditional selector is partial recursive in the pair (condition, program). -/
theorem partrec_missingSelector (c : Code) :
    Partrec (fun q : BitString × BitString => missingSelector c q.1 q.2) :=
  (partrec_missingSearch c).comp (decodeAdvice_primrec.to_comp.comp Computable.fst)

/-- On the true count the selector converges to `firstMissing`, from any program and in
particular from the empty one. -/
theorem firstMissing_mem_missingSelector (c : Code) (m n : ℕ) (p : BitString) :
    firstMissing c m n (sliceCount c m n) ∈
      missingSelector c (adviceCode m n (sliceCount c m n)) p := by
  change firstMissing c m n (sliceCount c m n) ∈
    missingSearch c (decodeAdvice (adviceCode m n (sliceCount c m n)))
  rw [decodeAdvice_adviceCode]
  exact firstMissing_mem_missingSearch c m n

/-- **The advertised application.**  Given the count `N = sliceCount c m n` as a
*condition*, the witness `firstMissing c m n N` costs `O(1)` conditional bits: the
constant depends on `V` and `c` only, not on `m` or `n`.

Read together with `plainK_firstMissing_gt`, which gives `plainK U (firstMissing …) > m`
under the same hypothesis `sliceCount c m n < 2 ^ n`, this is the object the counting
arguments of SUV problems 53(b), 250 and 364 need: a length-`n` string of plain
complexity greater than `m` that is nevertheless `O(1)` given `⟨m, n, N⟩`.

The hypothesis `sliceCount c m n < 2 ^ n` is not used in this proof — the search
converges on the true count in any case — and is carried only so that the statement
composes directly with `plainK_firstMissing_gt`. -/
theorem condK_firstMissing_le {V : Map} (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ m n : ℕ, sliceCount c m n < 2 ^ n →
      condK V (firstMissing c m n (sliceCount c m n)) (adviceCode m n (sliceCount c m n))
        ≤ (C : ENat) := by
  obtain ⟨C, hC⟩ :=
    condK_partrec_cond_map_le V hV (missingSelector c) (partrec_missingSelector c)
  refine ⟨C, fun m n _ => ?_⟩
  have h := hC (adviceCode m n (sliceCount c m n)) [] _
    (firstMissing_mem_missingSelector c m n [])
  simpa using h

end Kolmogorov.Dovetailing
