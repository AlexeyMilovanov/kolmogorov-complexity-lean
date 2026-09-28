import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots
import Mathlib.Data.List.SplitOn
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow.StepFold
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow.CountInvariants
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow

/-!
# Curve realization: curves, bad sets and coverable sets

The vocabulary and the counting of the realization theorem of VS40 §3.

A curve is named by a program: `curveEncode` writes the values `h 0, …, h K` in unary,
`decodeCurve` reads them back (`decodeCurve_curveEncode`, `exists_code_decoding_curve`), and
`ProfileCurve` bundles a curve with the shape conditions a profile of a length-`n` string of
complexity `kx` must satisfy.

The two families of sets: `coverableSet U i hi` collects the strings covered by some set of
complexity `i` and log-size `hi`, with `coverableSet_card_le` and
`inDescriptionProfile_of_mem_coverableSet`; `badSetsUnion` collects the sets that would push
the profile below the curve, with `badSetsUnion_card_le`.  A string in every coverable set and
no bad set realizes the curve.

`visitedVersionCountOfList` and `greedyFold_version_count_le_of_survivor_curve` are the
version-count bound for the greedy window in the form the construction uses, and
`badSetsUpToTime_eq_of_max` records that the bad-set enumeration stabilises.
-/

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- Total decoder for a coded curve.  The program bits are read as a **run-length
code**: the maximal blocks of `true`, in order and separated by `false`, name the
successive curve values `h 0, h 1, …` (so `[t,t,f,t,f]` decodes to `2, 1, 0, …`).
Reading past the encoded prefix returns `0`.

The decoder is total and surjective.  Every finite value sequence is named by some
bitstring (`curveEncode`, `decodeCurve_curveEncode`), so the
`curveDecodes` field of `ProfileCurve` is satisfiable for an arbitrary curve
(`exists_code_decoding_curve`) and `ProfileCurve` is non-vacuous.  Consequently, the
decoder can represent the curves required by the realization theorems below. -/
def decodeCurve (code : BitString) (i : ℕ) : ℕ :=
  ((code.splitOn false).map List.length).getD i 0

/-- Canonical program bitstring naming the curve `h` up to budget `K`: the values
`h 0, …, h K` written as `false`-separated unary (run-length) blocks. -/
def curveEncode (h : ℕ → ℕ) (K : ℕ) : BitString :=
  ((List.range (K + 1)).map h).flatMap (fun v => List.replicate v true ++ [false])

/-- Run-length reading inverts run-length writing: splitting the unary encoding of a
value list on `false` and taking block lengths recovers the list (with a trailing `0`
contributed by the final separator). -/
theorem splitOn_map_length_flatMap (vals : List ℕ) :
    (((vals.flatMap (fun v => List.replicate v true ++ [false])).splitOn false).map
      List.length) = vals ++ [0] := by
  induction vals with
  | nil => simp [List.splitOn_nil]
  | cons v vs ih =>
    have hsep : ∀ x ∈ List.replicate v true, ¬ ((· == false) x = true) := by
      intro x hx
      rw [List.eq_of_mem_replicate hx]; decide
    have hcat : (v :: vs).flatMap (fun v => List.replicate v true ++ [false])
        = List.replicate v true ++
          (false :: vs.flatMap (fun v => List.replicate v true ++ [false])) := by
      simp
    rw [hcat]
    change (((List.replicate v true ++ false ::
      vs.flatMap (fun v => List.replicate v true ++ [false])).splitOnP (· == false)).map
      List.length) = _
    rw [List.splitOnP_first (fun x : Bool => x == false) (List.replicate v true)
      hsep false (by decide) (vs.flatMap (fun v => List.replicate v true ++ [false]))]
    simp only [List.map_cons, List.length_replicate]
    change v :: (((vs.flatMap (fun v => List.replicate v true ++ [false])).splitOn false).map
      List.length) = _
    rw [ih]
    rfl

/-- The canonical encoding `curveEncode h K` decodes back to `h` on `[0, K]`.  Hence
`decodeCurve` is surjective onto every finite curve prefix. -/
theorem decodeCurve_curveEncode (h : ℕ → ℕ) (K : ℕ) {i : ℕ} (hi : i ≤ K) :
    decodeCurve (curveEncode h K) i = h i := by
  unfold decodeCurve curveEncode
  rw [splitOn_map_length_flatMap]
  have hlen : i < ((List.range (K + 1)).map h).length := by
    simp only [List.length_map, List.length_range]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen,
    List.getElem?_map, List.getElem?_range (by omega)]
  simp

/-- Decoding an encoded curve beyond its support index `K` returns zero. -/
theorem decodeCurve_curveEncode_out_of_bounds (h : ℕ → ℕ) (K : ℕ) {i : ℕ} (hi : K < i)
    :
    decodeCurve (curveEncode h K) i = 0 := by
  unfold decodeCurve curveEncode
  rw [splitOn_map_length_flatMap]
  by_cases h_eq : i = K + 1
  · subst h_eq
    have hlen : ((List.range (K + 1)).map h).length = K + 1 := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
    simp
  · apply List.getD_eq_default
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton]
    omega

/-- Non-vacuity of the `curveDecodes` field: for *any* curve `h` and budget `K` there is
a program bitstring whose `decodeCurve` reading agrees with `h` on `[0, K]`.  (Its plain
complexity — the `m` of `ProfileCurve` — is unconstrained here; for the low-complexity
curves the realization theorem is about, `m = O(log n)`.) -/
theorem exists_code_decoding_curve (h : ℕ → ℕ) (K : ℕ) :
    ∃ code : BitString, ∀ i, i ≤ K → decodeCurve code i = h i :=
  ⟨curveEncode h K, fun _ hi => decodeCurve_curveEncode h K hi⟩

/-- A valid profile curve `h` for a string of length `n` and complexity `kx`,
satisfying the shape constraints of a genuine description-profile boundary up to a
slack constant `c` and code complexity `m`.

The fields mirror the hypotheses of the article's `stat-any-curve` theorem:

* `code` / `curveDecodes` / `curveComplexity`: the curve is encoded by a bitstring
  whose plain complexity is bounded by `m` (it `decodeCurve`s to `h` on the relevant
  range).  This is satisfiable for an arbitrary `h` — see `exists_code_decoding_curve` —
  so the structure is non-vacuous; `m` is the description complexity of the curve.
* `antitone` / `slope`: the boundary decreases with slope at least `-1`, i.e. the
  sequence `t_i = h i` strictly decreases until it reaches `0` (`t_0 > … > t_k = 0`);
* `top`: the left endpoint `(0, n)` — at complexity budget `0` the best log-size is
  the full cube, so `h 0 ≤ n`;
* `bottom`: the right endpoint `(kx, 0)` — at budget `kx + O(log n)` the singleton
  bottoms the curve out at `0`;
* `sufficient`: the boundary stays above the sufficiency line `i + j ≥ kx`. -/
structure ProfileCurve (U : Map) (c : ℕ) (n kx m : ℕ) (h : ℕ → ℕ) where
  code : BitString
  curveDecodes : ∀ i, decodeCurve code i = h i
  curveComplexity : KPPlain U code ≤ (m : ENat)
  antitone   : Antitone h
  /-- Slope at least `-1`: while positive, the curve strictly decreases, matching the
  article's strictly decreasing sequence `t_0 > t_1 > … > t_k = 0`. -/
  slope      : ∀ i, h i = 0 ∨ h (i + 1) < h i
  /-- Left endpoint: `h 0 ≤ n`.  Together with antitonicity, this gives
  `i + h i ≤ n` throughout the positive region, as required by the genericity count. -/
  top        : h 0 ≤ n
  bottom     : h (kx + logSlack c n) = 0
  sufficient : ∀ i, kx ≤ i + h i + logSlack c (n + i + h i) + m

/-- The union of all sets of complexity at most `i` and log-size at most
`h i - (m + logSlack c_gen n)`: the strings excluded at budget `i`. -/
noncomputable def badSetsUnion (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (i : ℕ) :
    Finset
    BitString :=
  (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))).biUnion id

/-- The union of the bad sets at budget `i` has at most
`2^{i + h i - (m + logSlack c_gen n) + 1}`. -/
theorem badSetsUnion_card_le (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen i : ℕ) :
    (badSetsUnion U n h m c_gen i).card ≤ 2 ^ (i + 1 + (h i - (m + logSlack c_gen n))) := by
  unfold badSetsUnion
  have h_sum : (Finset.sum (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen
      n))) (fun S => S.card)) ≤
    (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))).card * 2 ^
        (h i - (m + logSlack c_gen n)) := by
    apply Finset.sum_le_card_nsmul
    intro S hS
    unfold descriptionsWithComplexityLeAndSizeLe at hS
    rw [Finset.mem_filter] at hS
    exact hS.2
  have h_card := card_descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))
  calc ((descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))).biUnion
      id).card
      ≤ Finset.sum (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n)))
          (fun S => S.card) := Finset.card_biUnion_le
    _ ≤ (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))).card * 2 ^
        (h i - (m + logSlack c_gen n)) := h_sum
    _ ≤ 2 ^ (i + 1) * 2 ^ (h i - (m + logSlack c_gen n)) := by gcongr
    _ = 2 ^ (i + 1 + (h i - (m + logSlack c_gen n))) := by rw [← pow_add]

/-- The union of all sets of complexity at most `i` and log-size at most `hi`: the strings
covered by some `(i, hi)`-description. -/
noncomputable def coverableSet (U : Map) (i : ℕ) (hi : ℕ) : Finset BitString :=
  (descriptionsWithComplexityLeAndSizeLe U i hi).biUnion id

/-- The coverable set at budget `i` and log-size `hi` has at most `2 ^ (i + 1 + hi)`
elements. -/
theorem coverableSet_card_le (U : Map) (i : ℕ) (hi : ℕ) :
    (coverableSet U i hi).card ≤ 2 ^ (i + 1 + hi) := by
  unfold coverableSet
  have h_sum : (Finset.sum (descriptionsWithComplexityLeAndSizeLe U i hi) (fun S => S.card)) ≤
    (descriptionsWithComplexityLeAndSizeLe U i hi).card * 2 ^ hi := by
    apply Finset.sum_le_card_nsmul
    intro S hS
    unfold descriptionsWithComplexityLeAndSizeLe at hS
    rw [Finset.mem_filter] at hS
    exact hS.2
  have h_card := card_descriptionsWithComplexityLeAndSizeLe U i hi
  calc ((descriptionsWithComplexityLeAndSizeLe U i hi).biUnion id).card
      ≤ Finset.sum (descriptionsWithComplexityLeAndSizeLe U i hi) (fun S => S.card) :=
          Finset.card_biUnion_le
    _ ≤ (descriptionsWithComplexityLeAndSizeLe U i hi).card * 2 ^ hi := h_sum
    _ ≤ 2 ^ (i + 1) * 2 ^ hi := by gcongr
    _ = 2 ^ (i + 1 + hi) := by rw [← pow_add]

/-- Up to an additive constant, every element of `coverableSet U i j` lies in the description
profile at `(i, j)`. -/
theorem inDescriptionProfile_of_mem_coverableSet (U : Map) :
    ∃ c, ∀ i j x, x ∈ coverableSet U i j → InDescriptionProfile U x (i + c) j := by
  obtain ⟨c, hc⟩ := setComplexity_le_of_mem_descriptionsWithComplexityLe U
  use c
  intro i j x hx
  unfold coverableSet at hx
  rw [Finset.mem_biUnion] at hx
  rcases hx with ⟨S, hS_mem, hx_mem⟩
  have hS_ne : S.Nonempty := ⟨x, hx_mem⟩
  refine ⟨S, hS_ne, ?_⟩
  unfold IsIJDescription
  refine ⟨hx_mem, ?_, ?_⟩
  · have h_comp := hc i S hS_ne
    unfold descriptionsWithComplexityLeAndSizeLe at hS_mem
    rw [Finset.mem_filter] at hS_mem
    exact h_comp hS_mem.1
  · unfold descriptionsWithComplexityLeAndSizeLe at hS_mem
    rw [Finset.mem_filter] at hS_mem
    exact hS_mem.2

/-- Any concrete `(i, j)`-description deposits its elements into `coverableSet U i j`: if `A`
is nonempty with `x ∈ A`, `setComplexity U A ≤ i` and `A.card ≤ 2 ^ j`, then
`x ∈ coverableSet U i j`.  This is the introduction rule converse to
`inDescriptionProfile_of_mem_coverableSet`. -/
theorem mem_coverableSet_of_isIJDescription (U : Map) {i j : ℕ} {A : Finset BitString}
    (hA : A.Nonempty) {x : BitString} (hx : x ∈ A)
    (hcomp : setComplexity U A hA ≤ (i : ENat)) (hsize : A.card ≤ 2 ^ j) :
    x ∈ coverableSet U i j := by
  unfold coverableSet
  rw [Finset.mem_biUnion]
  refine ⟨A, ?_, hx⟩
  unfold descriptionsWithComplexityLeAndSizeLe
  rw [Finset.mem_filter]
  exact ⟨mem_descriptionsWithComplexityLe_of_complexity hA hcomp, hsize⟩

/-
Gate E3c (corrected): the bad sets that the generic point must actually avoid
have, in total, `< 2^n` elements.

Only the levels `i` with `logSlack c_gen n < h i` matter: at every other level the
avoidance clause of `exists_generic_point` is discharged by its `h i ≤ logSlack c_gen n`
escape hatch (there is nothing to avoid), and `h i - logSlack c_gen n` truncates to `0`
so `badSetsUnion` there is the set of *all* low-complexity singletons — whose count
(`~2^i` at level `i ≈ kx ≈ n`) already exceeds `2^n`.  Hence the original,
unrestricted `∑_{i ≤ kx}` form of this gate was **false**; the sum must range over the
levels the construction genuinely needs.

Over the restricted index set the counting closes: for such `i`, `h i ≥ 1`, so
`i + h i ≤ h 0 ≤ n` (using the corrected `top` and the `slope` field), and
`badSetsUnion_card_le` gives each term `≤ 2^{i + 1 + (h i - L)} ≤ 2^{n + 1 - L}` with
`L = logSlack c_gen n`.  There are at most `n` such terms, so the sum is
`≤ n · 2^{n + 1 - L} < 2^n` once `2^L > 2n`, which holds for `c_gen = 3`.
-/
theorem sum_badSetsUnion_card_lt_of_le (U : Map) (c_gen : ℕ) (hc_gen : 3 ≤ c_gen) :
    ∀ c n kx m h, ProfileCurve U c n kx m h →
      ((Finset.range n).filter (fun i => (m + logSlack c_gen n) < h i)).sum
        (fun i => (badSetsUnion U n h m c_gen i).card) < 2 ^ n := by
  intro c n kx m h hc
  -- Abbreviation for the log-slack budget.
  set A := m + logSlack c_gen n with hAdef
  -- Descent: while `h` is positive, `i + h i` is non-increasing, so `i + h i ≤ h 0`.
  have hdesc : ∀ i, 0 < h i → i + h i ≤ h 0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hpos
      have hle : h (i + 1) ≤ h i := hc.antitone (Nat.le_succ i)
      have hposi : 0 < h i := lt_of_lt_of_le hpos hle
      have hlt : h (i + 1) < h i := by
        rcases hc.slope i with h0 | hlt
        · exact absurd h0 (by omega)
        · exact hlt
      have := ih hposi
      omega
  -- The relevant index set and its two key facts.
  set s := (Finset.range n).filter (fun i => A < h i) with hsdef
  have key : ∀ i ∈ s, (badSetsUnion U n h m c_gen i).card ≤ 2 ^ (n + 1 - A) ∧ i < n :=
      by
    intro i hi
    rw [hsdef, Finset.mem_filter] at hi
    obtain ⟨_, hAi⟩ := hi
    have hpos : 0 < h i := lt_of_le_of_lt (Nat.zero_le _) hAi
    have hihi : i + h i ≤ n := le_trans (hdesc i hpos) hc.top
    refine ⟨?_, by omega⟩
    refine le_trans (badSetsUnion_card_le U n h m c_gen i) ?_
    rw [← hAdef]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  -- At most `n` indices contribute.
  have hcard : s.card ≤ n := by
    refine le_trans (Finset.card_le_card (fun i hi => Finset.mem_range.mpr (key i hi).2)) ?_
    simp
  -- Bound the sum by `s.card * 2 ^ (n + 1 - A)`.
  have hbound : s.sum (fun i => (badSetsUnion U n h m c_gen i).card) ≤ s.card * 2 ^ (n + 1 -
      A) :=
      by
    calc s.sum (fun i => (badSetsUnion U n h m c_gen i).card)
        ≤ s.sum (fun _ => 2 ^ (n + 1 - A)) := Finset.sum_le_sum (fun i hi => (key i hi).1)
      _ = s.card * 2 ^ (n + 1 - A) := by rw [Finset.sum_const, smul_eq_mul]
  refine lt_of_le_of_lt hbound ?_
  -- Final arithmetic.  If `s` is empty the product is `0`; otherwise `A < n`.
  rcases Finset.eq_empty_or_nonempty s with hE | ⟨i0, hi0⟩
  · rw [hE, Finset.card_empty, zero_mul]; positivity
  · -- Recover `A < n` from a witness index.
    rw [hsdef, Finset.mem_filter] at hi0
    obtain ⟨_, hAi0⟩ := hi0
    have hpos0 : 0 < h i0 := lt_of_le_of_lt (Nat.zero_le _) hAi0
    have hi0n : i0 + h i0 ≤ n := le_trans (hdesc i0 hpos0) hc.top
    have hAn : A < n := lt_of_lt_of_le hAi0 (by omega)
    have hA1 : 1 ≤ A := by rw [hAdef]; unfold logSlack; omega
    -- `n < 2 ^ (A - 1)` using `n < 2 ^ (Nat.bits n).length` and `(bits n).length ≤ A - 1`.
    have hn2 : n < 2 ^ (A - 1) := by
      have hbits : n < 2 ^ (Nat.bits n).length := by
        have := Nat.lt_size_self n; rwa [← Nat.size_eq_bits_len] at this
      refine lt_of_lt_of_le hbits (Nat.pow_le_pow_right (by norm_num) ?_)
      rw [hAdef]; unfold logSlack
      have hPL : (Nat.bits n).length ≤ c_gen * (Nat.bits n).length :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    -- Conclude via the geometric split `2 ^ n = 2 ^ (A - 1) * 2 ^ (n + 1 - A)`.
    have hp : 0 < 2 ^ (n + 1 - A) := pow_pos (by norm_num) _
    have hsplit : 2 ^ n = 2 ^ (A - 1) * 2 ^ (n + 1 - A) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    calc s.card * 2 ^ (n + 1 - A) ≤ n * 2 ^ (n + 1 - A) := by gcongr
      _ < 2 ^ (A - 1) * 2 ^ (n + 1 - A) := (Nat.mul_lt_mul_right hp).mpr hn2

/-- Existential form of the counting bound.  Any `c_gen ≥ 3` works
(`sum_badSetsUnion_card_lt_of_le`); the witness `3` is the smallest such.  Downstream
constructions that need extra slack to absorb an *absolute* coding constant pick a larger
`c_gen` via `sum_badSetsUnion_card_lt_of_le` directly. -/
theorem sum_badSetsUnion_card_lt (U : Map) :
    ∃ c_gen, ∀ c n kx m h, ProfileCurve U c n kx m h →
      ((Finset.range n).filter (fun i => (m + logSlack c_gen n) < h i)).sum
        (fun i => (badSetsUnion U n h m c_gen i).card) < 2 ^ n :=
  ⟨3, sum_badSetsUnion_card_lt_of_le U 3 (by norm_num)⟩

/-- Bridge: a real (i, h i − L)-description forces membership in badSetsUnion. -/
theorem mem_badSetsUnion_of_inDescriptionProfile
    (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen i : ℕ) {x : BitString}
    (hx : InDescriptionProfile U x i (h i - (m + logSlack c_gen n))) :
    x ∈ badSetsUnion U n h m c_gen i := by
  unfold badSetsUnion
  rcases hx with ⟨S, hS_nonempty, hx_in_S, hS_comp, hS_card⟩
  simp only [Finset.mem_biUnion, id_eq]
  refine ⟨S, ?_, hx_in_S⟩
  unfold descriptionsWithComplexityLeAndSizeLe
  simp only [Finset.mem_filter]
  exact ⟨mem_descriptionsWithComplexityLe_of_complexity hS_nonempty hS_comp, hS_card⟩

/-- Standalone lower half (drops the membership clause of exists_generic_point).

The optimality hypothesis `_hU` is kept for signature-parallelism with the other
realization gates but is genuinely unused: this half is a pure counting argument
(`sum_badSetsUnion_card_lt`) valid for any machine `U`. -/
theorem exists_string_avoiding_curve (U : Map) (_hU : IsOptimalPrefixConditional U) :
    ∃ c_gen, ∀ n kx m h, ProfileCurve U c_gen n kx m h →
      ∃ x : BitString, x.length = n ∧
        (∀ i, ¬ InDescriptionProfile U x i (h i - (m + logSlack c_gen n)) ∨ h i ≤ m +
            logSlack c_gen n)
            := by
  obtain ⟨c_gen, hgen⟩ := sum_badSetsUnion_card_lt U
  refine ⟨c_gen, fun n kx m h hc => ?_⟩
  have hgen := hgen c_gen
  have hsum := hgen n kx m h hc
  set s := (Finset.range n).filter (fun i => m + logSlack c_gen n < h i)
  set bad_union := s.biUnion (fun i => badSetsUnion U n h m c_gen i)
  have h_card_bad : bad_union.card < 2 ^ n := by
    calc bad_union.card ≤ s.sum (fun i => (badSetsUnion U n h m c_gen i).card) :=
        Finset.card_biUnion_le
      _ < 2 ^ n := hsum
  have h_card_all : (stringsOfLength n).card = 2 ^ n := card_stringsOfLength n
  have h_exists : ∃ x ∈ stringsOfLength n, x ∉ bad_union := by
    apply Finset.exists_mem_notMem_of_card_lt_card (s := bad_union)
    rw [h_card_all]
    exact h_card_bad
  rcases h_exists with ⟨x, hx_len, hx_not_bad⟩
  refine ⟨x, (mem_stringsOfLength n x).mp hx_len, fun i => ?_⟩
  by_cases hle : h i ≤ m + logSlack c_gen n
  · exact Or.inr hle
  · refine Or.inl (fun h_prof => ?_)
    have hlt : m + logSlack c_gen n < h i := by omega
    have h_in_bad := mem_badSetsUnion_of_inDescriptionProfile U n h m c_gen i h_prof
    have hi_n : i < n := by
      have hpos : 0 < h i := by omega
      have hdesc : ∀ j, 0 < h j → j + h j ≤ h 0 := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          intro hposj
          have hle_j : h (j + 1) ≤ h j := hc.antitone (Nat.le_succ j)
          have hpos_j : 0 < h j := lt_of_lt_of_le hposj hle_j
          have hlt_slope : h (j + 1) < h j := by
            rcases hc.slope j with h0 | hlt_slope
            · exact absurd h0 (by omega)
            · exact hlt_slope
          have := ih hpos_j
          omega
      have hihi : i + h i ≤ n := le_trans (hdesc i hpos) hc.top
      omega
    have h_in_s : i ∈ s := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hi_n, hlt⟩
    have h_not_in_bad_i : x ∉ badSetsUnion U n h m c_gen i := by
      intro h_in
      have h_in_bad_union : x ∈ bad_union := by
        apply Finset.mem_biUnion.mpr
        exact ⟨i, h_in_s, h_in⟩
      exact hx_not_bad h_in_bad_union
    exact h_not_in_bad_i h_in_bad

/-- Structure-function form of the standalone lower half.  For every admissible
`ProfileCurve h` there is a length-`n` string whose structure function stays *above*
the curve (up to the log-slack floor `L = m + O(log n)`): at each budget `i`, either
the curve has already dropped into the slack band (`h i ≤ L`) or the structure
function strictly exceeds the curve there (`h i − L < h_x(i)`).  This is
`exists_string_avoiding_curve` transported through
`inDescriptionProfile_iff_structureFunction_le`, expressing the article's "the
description profile does not cross below the boundary curve" directly on
`structureFunction`. -/
theorem exists_string_structureFunction_above_curve
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_gen, ∀ n kx m h, ProfileCurve U c_gen n kx m h →
      ∃ x : BitString, x.length = n ∧
        (∀ i, ((h i - (m + logSlack c_gen n) : ℕ) : ℕ∞) < structureFunction U x i
              ∨ h i ≤ m + logSlack c_gen n) := by
  obtain ⟨c_gen, hgen⟩ := exists_string_avoiding_curve U hU
  refine ⟨c_gen, fun n kx m h hc => ?_⟩
  obtain ⟨x, hxlen, hxavoid⟩ := hgen n kx m h hc
  refine ⟨x, hxlen, fun i => ?_⟩
  rcases hxavoid i with hno | hle
  · refine Or.inl ?_
    rw [inDescriptionProfile_iff_structureFunction_le] at hno
    exact not_le.mp hno
  · exact Or.inr hle

/-- Removes duplicates from a list, keeping the last occurrence of each element. -/
def List.dedup {α} [DecidableEq α] : List α → List α
| [] => []
| a :: l => if a ∈ List.dedup l then List.dedup l else a :: List.dedup l

/-- Deduplication preserves membership. -/
theorem mem_List.dedup {α} [DecidableEq α] (l : List α) (x : α) :
    x ∈ List.dedup l ↔ x ∈ l := by
  induction l with
  | nil =>
    simp [List.dedup]
  | cons a l ih =>
    unfold List.dedup
    split_ifs with h
    · rw [ih]
      constructor
      · intro hx
        exact List.mem_cons_of_mem a hx
      · intro hx
        cases hx with
        | head _ => rwa [← ih]
        | tail _ h_tail => exact h_tail
    · simp only [List.mem_cons]
      rw [ih]

/-- Auxiliary: snapshot-based bad sets up to time `t`.
    This uses the computable `snapshotDescList` which enumerates the valid
    canonical-uniform models. Note: `snapshotDescList` lists them in `boundedPrograms`
    order (length/lexicographic), so it is not chronological. -/
def badSetsUpToTime (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t : ℕ)
    : List
    (Finset BitString) :=
  List.dedup (((List.range n).filter (fun j => m + logSlack c_gen n < h j)).flatMap (fun j =>
    (snapshotDescList c j (h j - (m + logSlack c_gen n)) t).map List.toFinset))

/-- Auxiliary: bad sets discovered exactly at time `t`. -/
def newBadSetsAtTime (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t :
    ℕ) : List
    (Finset BitString) :=
  let all_at_t := badSetsUpToTime c n h m c_gen t
  match t with
  | 0 => all_at_t
  | t_minus_1 + 1 =>
    let all_at_t_minus_1 := badSetsUpToTime c n h m c_gen t_minus_1
    all_at_t.filter (fun S => S ∉ all_at_t_minus_1)

/-- The chronological enumeration of bad sets up to `t_max`.
    This concatenates the newly discovered sets at each time `t`, ensuring
    the list matches the time-of-discovery order required by the machine model. -/
def temporalBadEnumList (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ)
    (t_max : ℕ) : List
    (Finset BitString) :=
  (List.range (t_max + 1)).flatMap (fun t => newBadSetsAtTime c n h m c_gen t)

/-- B0: Flattened list of all bad sets across all levels `j ≤ kx + logSlack c_gen n`.
This uses the extensional `Finset.toList` order.  The machine-model simulation instead
uses `temporalBadEnumList`, whose order records when `evaln` discovers each set. -/
noncomputable def badEnumList (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen _kx : ℕ) : List
    (Finset BitString) :=
  (((Finset.range n).filter (fun j => m + logSlack c_gen n < h j)).biUnion
    (fun j => descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)))).toList

/-- Given a list of bad sets, the union of the first `k` sets. -/
def badUnionUpTo (L : List (Finset BitString)) (k : ℕ) : Finset BitString :=
  (L.take k).foldl (· ∪ ·) ∅

/-- Take the first `size` elements of a Finset of BitStrings according to the canonical
`ℕ`-encoding order (`decodeBits`).  This is now a concrete object built on the verified
abstract selector `GreedyWindow.firstBlock`; in particular `GreedyWindow.firstBlock_subset`
and `GreedyWindow.firstBlock_card` give `firstElements S size ⊆ S` and
`(firstElements S size).card = min size S.card`. -/
noncomputable def firstElements (S : Finset BitString) (size : ℕ) : Finset BitString :=
  GreedyWindow.firstBlock Encodable.encode size S

/-- The first `size` elements of `S` form a subset of `S`. -/
theorem firstElements_subset (S : Finset BitString) (size : ℕ) :
    firstElements S size ⊆ S := GreedyWindow.firstBlock_subset _ _ _

/-- Taking the first `size` elements of `S` yields `size` elements, or all of `S` if it is smaller.
Taking the first `size` elements of `S` yields `size` elements, or all of `S` if it is smaller. -/
theorem firstElements_card (S : Finset BitString) (size : ℕ) :
    (firstElements S size).card = min size S.card := GreedyWindow.firstBlock_card _ _ _

/-- The number of window refreshes performed by the greedy process after processing the bad sets
enumerated up to stage `t`. -/
noncomputable def temporalRefreshCount (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m
    c_gen i t : ℕ)
    : ℕ :=
  GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
      (temporalBadEnumList c n h m c_gen t) |>.2.2

/-- The window of `2 ^ h i` strings of length `n` current after processing the bad sets enumerated
up to stage `t`. -/
noncomputable def temporalWindow (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen i t
    : ℕ) :
    Finset BitString :=
  GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
      (temporalBadEnumList c n h m c_gen t) |>.2.1

/-- The first length-`n` string outside the finite union of the bad sets, and the empty string
when there is none.  The lexicographic choice pins the same survivor for every window. -/
noncomputable def lexLeastSurvivor (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ) :
    BitString :=
  let L := badEnumList U n h m c_gen kx
  let rem := stringsOfLength n \ badUnionUpTo L L.length
  if _hne : rem.Nonempty then
    let first1 : Finset BitString := firstElements rem 1
    if h1 : first1.toList ≠ [] then first1.toList.head h1 else []
  else []

/-- The refresh times of the greedy window: `windowRefreshSequence … k` is the index in the bad
enumeration at which the `k`-th refresh happens, namely the first index at which the current
`2 ^ (h i)`-window has been deleted entirely (or the end of the enumeration). -/
noncomputable def windowRefreshSequence (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i :
    ℕ) : ℕ → ℕ
| 0 => 0
| (k + 1) =>
  let L := badEnumList U n h m c_gen kx
  let r_k := windowRefreshSequence U n h m c_gen kx i k
  let W_k := firstElements ((stringsOfLength n) \ badUnionUpTo L r_k) (2 ^ h i)
  let valid_t := (Finset.Icc r_k L.length).filter (fun t => (W_k \ badUnionUpTo L t) = ∅)
  if hne : valid_t.Nonempty then valid_t.min' hne else L.length

/-- The window at step `k`: the first `2 ^ h i` strings of length `n` that survive the bad sets
enumerated up to the refresh time `windowRefreshSequence … k`. -/
noncomputable def greedyWindow (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ) (k :
    ℕ) : Finset
    BitString :=
  let L := badEnumList U n h m c_gen kx
  let r_k := windowRefreshSequence U n h m c_gen kx i k
  firstElements ((stringsOfLength n) \ badUnionUpTo L r_k) (2 ^ h i)

/-- The greedy window always respects the size budget `2 ^ h i`.  Each version is a
`firstElements`-block of width `2 ^ h i`, so `firstElements_card` bounds its cardinality
by `min (2 ^ h i) …`, regardless of how many survivors remain. -/
theorem temporalWindow_card_le (c_U : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen i T
    : ℕ) :
    (temporalWindow c_U n h m c_gen i T).card ≤ 2 ^ h i := by
  have h_step : ∀ (L' : List (Finset BitString)) (st : Finset BitString × Finset BitString ×
      ℕ),
      st.2.1.card ≤ 2 ^ h i →
      (L'.foldl (GreedyWindow.step (stringsOfLength n) (fun S => firstElements S (2 ^ h i)))
          st).2.1.card
      ≤ 2 ^ h i := by
    intro L'
    induction L' with
    | nil => intro st hst; exact hst
    | cons d L' ih =>
      intro st hst
      apply ih
      unfold GreedyWindow.step
      dsimp only
      split_ifs
      · rw [firstElements_card]; exact min_le_left _ _
      · exact hst
  unfold temporalWindow GreedyWindow.fold
  apply h_step
  rw [firstElements_card]
  exact min_le_left _ _

/-- The concrete final greedy window always respects the size budget `2 ^ h i`. -/
theorem greedyWindow_card_le (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i k : ℕ) :
    (greedyWindow U n h m c_gen kx i k).card ≤ 2 ^ h i := by
  unfold greedyWindow
  rw [firstElements_card]
  exact min_le_left _ _

/-- Monotonicity of `firstElements` in the requested size (delegates to
`GreedyWindow.firstBlock_mono_size`). -/
theorem firstElements_mono_size (S : Finset BitString) {a b : ℕ} (hab : a ≤ b) :
    firstElements S a ⊆ firstElements S b :=
  GreedyWindow.firstBlock_mono_size _ hab _

/-- Monotonicity of the running bad-union: taking a longer prefix only enlarges the
deleted set. -/
theorem badUnionUpTo_mono (L : List (Finset BitString)) {a b : ℕ} (hab : a ≤ b) :
    badUnionUpTo L a ⊆ badUnionUpTo L b := by
  have hgrow : ∀ (l : List (Finset BitString)) (s : Finset BitString),
      s ⊆ l.foldl (· ∪ ·) s := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons x xs ih => intro s; exact Finset.subset_union_left.trans (ih (s ∪ x))
  obtain ⟨t, ht⟩ := (List.take_prefix_take_left hab : L.take a <+: L.take b)
  unfold badUnionUpTo
  rw [← ht, List.foldl_append]
  exact hgrow t _

/-- Membership in the full running bad-union is witnessed by some list element. -/
theorem mem_badUnionUpTo_full {L : List (Finset BitString)} {x : BitString} :
    x ∈ badUnionUpTo L L.length ↔ ∃ d ∈ L, x ∈ d := by
  unfold badUnionUpTo
  rw [List.take_length]
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton l d ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Finset.mem_union, List.mem_append,
      List.mem_singleton, ih]
    constructor
    · rintro (⟨d', hd', hx⟩ | hx)
      · exact ⟨d', Or.inl hd', hx⟩
      · exact ⟨d, Or.inr rfl, hx⟩
    · rintro ⟨d', hd' | rfl, hx⟩
      · exact Or.inl ⟨d', hd', hx⟩
      · exact Or.inr hx

/-- Every element of a bad-set list is contained in the full running bad-union.
A direct corollary of `mem_badUnionUpTo_full`. -/
theorem subset_badUnionUpTo_full (L : List (Finset BitString)) {d : Finset BitString}
    (hd : d ∈ L) : d ⊆ badUnionUpTo L L.length := by
  intro x hx
  exact mem_badUnionUpTo_full.mpr ⟨d, hd, hx⟩

/-- The refresh index never exceeds the length of the bad-set enumeration. -/
theorem windowRefreshSequence_le_length (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i k :
    ℕ) :
    windowRefreshSequence U n h m c_gen kx i k ≤ (badEnumList U n h m c_gen kx).length := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    simp only [windowRefreshSequence]
    split
    · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ ‹_›)).1).2
    · exact le_rfl

/-- Under the survivor-existence hypothesis the greedy running-window process reaches
its final snapshot: after `L.length` potential refreshes the refresh index equals
`L.length` (the whole bad enumeration has been consumed).  This is the finite
termination fact of the Vereshchagin–Vitányi running-window construction. -/
theorem windowRefreshSequence_stabilizes (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i :
    ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    windowRefreshSequence U n h m c_gen kx i (badEnumList U n h m c_gen kx).length
      = (badEnumList U n h m c_gen kx).length := by
  -- By induction on `k`, either `seq k = L.length` or `k ≤ seq k`.
  have h_ind : ∀ k, windowRefreshSequence U n h m c_gen kx i k =
      (badEnumList U n h m c_gen kx).length ∨ k ≤ windowRefreshSequence U n h m c_gen kx i k
          := by
    intro k
    induction k with
    | zero => simp +arith +decide [windowRefreshSequence]
    | succ k ih =>
      simp only [windowRefreshSequence]
      split_ifs with hne
      · -- A refresh occurs: the new index is the minimum of a valid window.
        have hmem := Finset.min'_mem _ hne
        have hfilt := Finset.mem_filter.mp hmem
        have hIcc := Finset.mem_Icc.mp hfilt.1
        rcases ih with hih | hih
        · left; omega
        · right
          have hsurv :
              (firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
                  (windowRefreshSequence U n h m c_gen kx i k)) (2 ^ h i)).Nonempty := by
            have hrem' :
                (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
                    (windowRefreshSequence U n h m c_gen kx i k)).Nonempty :=
              hrem.mono (Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
                (badUnionUpTo_mono _ (windowRefreshSequence_le_length U n h m c_gen kx i k)))
            exact Finset.card_pos.mp (by
              rw [firstElements_card]
              exact lt_min (Nat.one_le_pow _ _ (by decide)) (Finset.card_pos.mpr hrem'))
          have hnotsub :
              ¬ (firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
                  (windowRefreshSequence U n h m c_gen kx i k)) (2 ^ h i))
                ⊆ badUnionUpTo (badEnumList U n h m c_gen kx)
                    (windowRefreshSequence U n h m c_gen kx i k) := by
            intro hsub
            obtain ⟨x, hx⟩ := hsurv
            exact (Finset.mem_sdiff.mp (firstElements_subset _ _ hx)).2 (hsub hx)
          have hne_rk :
              Finset.min' _ hne ≠ windowRefreshSequence U n h m c_gen kx i k := by
            intro hcontra
            rw [hcontra] at hmem
            exact hnotsub
              (Finset.sdiff_eq_empty_iff_subset.mp (Finset.mem_filter.mp hmem).2)
          omega
      · left; rfl
  cases h_ind ( List.length ( badEnumList U n h m c_gen kx ) ) <;> [ tauto; exact le_antisymm (
      windowRefreshSequence_le_length U n h m c_gen kx i _ ) ‹_› ]

/-- Some greedy window contains the lex-least survivor.  The nonemptiness hypothesis is
essential: without it the bad enumeration may cover every length-`n` string. -/
theorem greedyWindow_contains_survivor (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i :
    ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    ∃ v, lexLeastSurvivor U n h m c_gen kx ∈ greedyWindow U n h m c_gen kx i v := by
  use (badEnumList U n h m c_gen kx).length;
  unfold lexLeastSurvivor greedyWindow;
  simp +zetaDelta only [ne_eq, Finset.toList_eq_nil, dite_not, dite_eq_ite] at *;
  split_ifs;
  · rename_i h;
    replace h := congr_arg Finset.card h ; simp_all +decide [ firstElements_card ];
  · rw [ windowRefreshSequence_stabilizes U n h m c_gen kx i hrem ];
    exact firstElements_mono_size _ ( Nat.one_le_pow _ _ ( by decide ) ) ( Finset.mem_toList.mp
        ( List.head_mem _ ) )

/-- The `v = L.length` final snapshot of the concrete greedy process contains the
lex-least final survivor.  This is the membership fact needed by the final
`coverableSet` assembly; it uses concrete `windowRefreshSequence` stabilization,
rather than the temporal-fold formulation. -/
theorem greedyWindow_final_contains_survivor (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i
    : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    lexLeastSurvivor U n h m c_gen kx ∈
      greedyWindow U n h m c_gen kx i (badEnumList U n h m c_gen kx).length := by
  unfold lexLeastSurvivor greedyWindow
  simp +zetaDelta only [ne_eq, Finset.toList_eq_nil, dite_not, dite_eq_ite] at *
  split_ifs
  · rename_i h
    replace h := congr_arg Finset.card h
    simp_all +decide [firstElements_card]
  · rw [windowRefreshSequence_stabilizes U n h m c_gen kx i hrem]
    exact firstElements_mono_size _ (Nat.one_le_pow _ _ (by decide))
      (Finset.mem_toList.mp (List.head_mem _))

/-- The final concrete greedy window is nonempty under the survivor hypothesis. -/
theorem greedyWindow_final_nonempty (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    (greedyWindow U n h m c_gen kx i (badEnumList U n h m c_gen kx).length).Nonempty :=
  ⟨_, greedyWindow_final_contains_survivor U n h m c_gen kx i hrem⟩

/-- The bucket-1 test on a bad-set entry: `d` is one of the descriptions of complexity at
most `i`. -/
noncomputable def bucket1Pred (U : Map) (i : ℕ) (d : Finset BitString) : Bool :=
  decide (d ∈ descriptionsWithComplexityLe U i)

/-- At most `2 ^ (i + 1)` entries of the bad enumeration pass the bucket-1 test, since there
are at most that many descriptions of complexity at most `i`. -/
theorem bucket1_bound (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ) :
    ((badEnumList U n h m c_gen kx).filter (bucket1Pred U i)).length ≤ 2 ^ (i + 1) := by
  have h_nodup : (badEnumList U n h m c_gen kx).Nodup := by
    unfold badEnumList
    exact Finset.nodup_toList _
  have h_len : ((badEnumList U n h m c_gen kx).filter (bucket1Pred U i)).length =
      ((badEnumList U n h m c_gen kx).toFinset.filter (fun d => bucket1Pred U i d)).card := by
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ h_nodup), List.toFinset_filter]
  rw [h_len]
  have h_subset : ((badEnumList U n h m c_gen kx).toFinset.filter (fun d => bucket1Pred U i d))
      ⊆
      descriptionsWithComplexityLe U i := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact of_decide_eq_true hx.right
  exact (Finset.card_le_card h_subset).trans (card_descriptionsWithComplexityLe U i)

/-- Diagonal descent from the `ProfileCurve` slope: on the positive region the map
`j ↦ j + h j` is non-increasing.  If `i ≤ j` and `h j > 0` then `j + h j ≤ i + h i`.
(Since `h` is antitone, `h j > 0` forces `h k > 0` for all `k ≤ j`, so the `slope` field
`h k = 0 ∨ h (k+1) < h k` gives `h (k+1) < h k`, i.e. `(k+1) + h (k+1) ≤ k + h k`.) -/
theorem profileCurve_diag_le (U : Map) (c n kx m : ℕ) (h : ℕ → ℕ)
    (hc : ProfileCurve U c n kx m h) (i j : ℕ) (hij : i ≤ j) (hpos : 0 < h j) :
    j + h j ≤ i + h i := by
  induction hij with
  | refl => exact le_rfl
  | @step k hij ih =>
      have hpos_k : 0 < h k := lt_of_lt_of_le hpos (hc.antitone (Nat.le_succ k))
      have hdrop : h (k + 1) < h k := (hc.slope k).resolve_left (Nat.ne_of_gt hpos_k)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm] using
        Nat.add_le_add_left (Nat.succ_le_iff.mpr hdrop) k |>.trans (ih hpos_k)

/-- Per-level card-sum bound: the total size of all descriptions at level `j` with size budget
`t` is at most `2 ^ (j + 1 + t)`, since there are at most `2 ^ (j + 1)` of them and each has
cardinality at most `2 ^ t`. -/
theorem bucket2_level_card_sum_le (U : Map) (j t : ℕ) (G : Finset BitString) :
    ∑ d ∈ descriptionsWithComplexityLeAndSizeLe U j t, (d ∩ G).card ≤ 2 ^ (j + 1 + t) :=
        by
  refine le_trans (Finset.sum_le_card_nsmul _ _ (2 ^ t) ?_) ?_
  · intro x hx
    exact le_trans (Finset.card_le_card Finset.inter_subset_left) (Finset.mem_filter.mp hx).2
  · rw [smul_eq_mul, pow_add]
    gcongr
    exact card_descriptionsWithComplexityLeAndSizeLe U j t

/-- Bound on the total size of the bad-set entries that fail the bucket-1 test: their
intersections with the length-`n` cube sum to at most `n * 2 ^ (i + 1 + h i)`, for a curve `h`
satisfying the `ProfileCurve` shape constraints. -/
theorem bucket2_bound_of_curve (U : Map) (c n kx m c_gen : ℕ) (h : ℕ → ℕ)
    (hc : ProfileCurve U c n kx m h) (i : ℕ) :
    (((badEnumList U n h m c_gen kx).filter (fun d => !(bucket1Pred U i d))).map (fun d => (d
        ∩ (stringsOfLength n)).card)).sum ≤
    n * 2 ^ (i + 1 + h i) := by
  have h_filter : ∀ d ∈ (badEnumList U n h m c_gen kx).filter (fun d => !bucket1Pred U i
      d), ∃ j ∈
      (Finset.range n).filter (fun j => m + logSlack c_gen n < h j), j ≥ i + 1 ∧ d ∈
      descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)) := by
    intro d hd
    obtain ⟨hd_bad, hd_not_bucket1⟩ := List.mem_filter.mp hd
    rw [badEnumList, Finset.mem_toList, Finset.mem_biUnion] at hd_bad
    obtain ⟨j, hj, hdj⟩ := hd_bad
    refine ⟨j, hj, ?_, hdj⟩
    rw [ge_iff_le, Order.add_one_le_iff]
    by_contra hij
    have hji : j ≤ i := Nat.le_of_not_gt hij
    have hdj' : d ∈ descriptionsWithComplexityLe U j :=
      (Finset.mem_filter.mp hdj).1
    have hdi : d ∈ descriptionsWithComplexityLe U i :=
      descriptionsWithComplexityLe_subset_of_le U hji hdj'
    simp [bucket1Pred, hdi] at hd_not_bucket1
  have h_filter_sum : ∑ d ∈ (badEnumList U n h m c_gen kx).toFinset.filter
      (fun d => !bucket1Pred U i d), (d ∩ stringsOfLength n).card ≤ ∑ j ∈ (Finset.range
          n).filter
      (fun j => m + logSlack c_gen n < h j), if j ≥ i + 1 then ∑ d ∈
      descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)),
      (d ∩ stringsOfLength n).card else 0 := by
    have h_filter_sum : ∑ d ∈ (badEnumList U n h m c_gen kx).toFinset.filter
        (fun d => !bucket1Pred U i d), (d ∩ stringsOfLength n).card ≤ ∑ j ∈
            (Finset.range n).filter
        (fun j => m + logSlack c_gen n < h j), ∑ d ∈ (badEnumList U n h m c_gen
            kx).toFinset.filter
        (fun d => !bucket1Pred U i d), if d ∈ descriptionsWithComplexityLeAndSizeLe U j
        (h j - (m + logSlack c_gen n)) ∧ j ≥ i + 1 then (d ∩ stringsOfLength n).card else
            0 := by
      rw [ Finset.sum_comm ];
      gcongr;
      simp +zetaDelta only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        Finset.mem_filter, Finset.mem_range, ge_iff_le, Order.add_one_le_iff, and_imp,
        List.mem_toFinset] at *;
      obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := h_filter _ ( by tauto ) ( by tauto ) ; exact
          le_trans ( by aesop ) ( Finset.single_le_sum ( fun x _ => Nat.zero_le _ ) (
          Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hj₁.1, hj₁.2 ⟩ ) ) ;
    refine le_trans h_filter_sum <| Finset.sum_le_sum fun j hj => ?_;
    split_ifs <;> simp_all +decide only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      Finset.mem_filter, Finset.mem_range, ge_iff_le, Order.add_one_le_iff, and_imp,
          Finset.sum_ite,
      not_and, not_lt, Finset.sum_const_zero, add_zero, and_true, implies_true,
      Finset.filter_true, nonpos_iff_eq_zero, Finset.sum_eq_zero_iff, List.mem_toFinset,
      Finset.card_eq_zero, isEmpty_Prop, IsEmpty.forall_iff];
    exact Finset.sum_le_sum_of_subset ( Finset.inter_subset_right );
  have h_filter_sum_le : ∑ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h
      j),
      (if j ≥ i + 1 then 2 ^ (j + 1 + (h j - (m + logSlack c_gen n))) else 0) ≤ n * 2 ^
      (i + 1 + h i) := by
    have h_filter_sum_le : ∀ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h
        j), j ≥
        i + 1 → 2 ^ (j + 1 + (h j - (m + logSlack c_gen n))) ≤ 2 ^ (i + 1 + h i) := by
      intros j hj hj_ge_i
      have h_diag : j + h j ≤ i + h i := by
        apply profileCurve_diag_le U c n kx m h hc i j (by linarith) (by
        grind);
      exact pow_le_pow_right₀ ( by decide ) ( by linarith [ Nat.sub_le ( h j ) ( m + logSlack
          c_gen n ) ] );
    calc ∑ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j),
            (if j ≥ i + 1 then 2 ^ (j + 1 + (h j - (m + logSlack c_gen n))) else 0)
        ≤ ∑ _j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j),
            2 ^ (i + 1 + h i) := by
          apply Finset.sum_le_sum
          intro x hx
          split_ifs with hx1
          · exact h_filter_sum_le x hx hx1
          · exact Nat.zero_le _
      _ ≤ n * 2 ^ (i + 1 + h i) := by
          rw [Finset.sum_const, smul_eq_mul]
          gcongr
          exact le_trans (Finset.card_filter_le _ _) (by simp)
  calc
    (((badEnumList U n h m c_gen kx).filter (fun d => !bucket1Pred U i d)).map
        (fun d => (d ∩ stringsOfLength n).card)).sum =
        ∑ d ∈ (badEnumList U n h m c_gen kx).toFinset.filter
          (fun d => !bucket1Pred U i d), (d ∩ stringsOfLength n).card := by
      rw [← List.sum_toFinset]
      · congr! 1
        ext
        simp [List.mem_toFinset]
      · exact List.Nodup.filter _ (Finset.nodup_toList _)
    _ ≤ ∑ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j),
        if j ≥ i + 1 then ∑ d ∈ descriptionsWithComplexityLeAndSizeLe U j
          (h j - (m + logSlack c_gen n)), (d ∩ stringsOfLength n).card else 0 := h_filter_sum
    _ ≤ ∑ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j),
        if j ≥ i + 1 then 2 ^ (j + 1 + (h j - (m + logSlack c_gen n))) else 0 := by
      gcongr
      split_ifs <;> [exact bucket2_level_card_sum_le _ _ _ _; exact Nat.zero_le _]
    _ ≤ n * 2 ^ (i + 1 + h i) := h_filter_sum_le

/-- The number of physical refreshes made by the sequence `seq` over a bad-set list `L`: the
number of indices `k < L.length` with `seq k < seq (k + 1)`. -/
noncomputable def visitedVersionCountOfList (L : List (Finset BitString)) (seq : ℕ → ℕ) :
    ℕ :=
  (Finset.range L.length).filter (fun k => seq k < seq (k + 1)) |>.card

/- `windowRefreshSequence` hardcodes `badEnumList`, so the temporal analysis below uses
`GreedyWindow.fold` directly on `temporalBadEnumList`. -/

/-- **Abstract greedy-fold version-count bound (survivor + curve form).**  This combines
the abstract survivor combinatorics `GreedyWindow.fold_count_split_div_le_of_survivor`
with the survivor-nonempty hypothesis `hsurv` and the two bucket bounds:
`bucket1_bound` (bucket 1: sets that are themselves descriptions of complexity `≤ i`,
at most `2 ^ (i+1)` of them, each triggering at most one refresh) and
`bucket2_bound_of_curve` (bucket 2: the higher-level deletion mass, `≤ n · 2 ^ (i+1+h i)`
under the `ProfileCurve` slope, divided by the window width `2 ^ h i`).  Hence the number
of refreshes of the abstract greedy fold over `badEnumList` is at most
`2 ^ (i+1) + n · 2 ^ (i+1) = (n+1) · 2 ^ (i+1)`.  In bits this is `i + O(log n)`, which is
exactly the Vereshchagin–Vitányi version-count budget consumed inside `coverableSet`. -/
theorem greedyFold_version_count_le_of_survivor_curve
    (U : Map) (c n kx m c_gen : ℕ) (h : ℕ → ℕ) (hc : ProfileCurve U c n kx m h) (i :
        ℕ)
    (hsurv : (stringsOfLength n \
      (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
        (badEnumList U n h m c_gen kx)).1).Nonempty) :
    (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
        (badEnumList U n h m c_gen kx)).2.2 ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) := by
  have hW : 0 < 2 ^ h i := pow_pos (by norm_num) (h i)
  have hbound := GreedyWindow.fold_count_split_div_le_of_survivor
    (stringsOfLength n) (2 ^ h i) hW (fun S => firstElements S (2 ^ h i))
    (fun S => firstElements_subset S (2 ^ h i))
    (fun S => firstElements_card S (2 ^ h i))
    (badEnumList U n h m c_gen kx) (bucket1Pred U i) hsurv
  refine hbound.trans (add_le_add (bucket1_bound U n h m c_gen kx i) ?_)
  calc (((badEnumList U n h m c_gen kx).filter (fun d => !bucket1Pred U i d)).map
          (fun d => (d ∩ stringsOfLength n).card)).sum / 2 ^ h i
      ≤ (n * 2 ^ (i + 1 + h i)) / 2 ^ h i :=
        Nat.div_le_div_right (bucket2_bound_of_curve U c n kx m c_gen h hc i)
    _ = n * 2 ^ (i + 1) := by
        rw [pow_add, ← mul_assoc, Nat.mul_div_cancel _ hW]

/- A global room estimate for this fold is unavailable: at the top of a profile curve the
window can already occupy the whole cube while level-zero bad sets are nonempty.  The
version bound therefore uses `GreedyWindow.fold_count_split_div_le_of_survivor`, not a
cardinality bound for the accumulated deleted set. -/

/- A held temporal window need not contain the globally least final survivor: smaller
elements may be deleted only after the last refresh.  The temporal bridge below uses a
complete later enumeration and refresh-count stability to rule out that obstruction. -/

/-- Two functions agreeing on the members of a list induce the same flat map. -/
theorem List.flatMap_congr_loc {α β} (l : List α) (f g : α → List β) (h : ∀ x ∈ l, f
    x = g x) :
    l.flatMap f = l.flatMap g := by
  have : List.map f l = List.map g l := List.map_congr_left h
  unfold List.flatMap
  rw [this]

/-- Once the halting counts below `n` have stabilised at stage `t₀`, the enumeration of bad sets no
longer changes. -/
theorem badSetsUpToTime_eq_of_max (c : Nat.Partrec.Code) {U : Map} (hc : IsCodeFor c U) (n :
    ℕ)
    (h : ℕ → ℕ) (m c_gen : ℕ) (t t₀ : ℕ)
    (h_ge : t₀ ≤ t)
    (hmax : ∀ j, j < n → ∀ t', countHalts c j t' ≤ countHalts c j t₀) :
    badSetsUpToTime c n h m c_gen t = badSetsUpToTime c n h m c_gen t₀ := by
  unfold badSetsUpToTime
  congr 1
  apply List.flatMap_congr_loc
  intro j hj
  simp only [List.mem_filter, List.mem_range] at hj
  exact congrArg (fun L => L.map List.toFinset) (snapshotDescList_eq_of_max hc j (h j - (m +
      logSlack c_gen n)) t t₀ h_ge (hmax j hj.1))

end Kolmogorov
