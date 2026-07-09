import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionSnapshot
import Mathlib.Data.List.SplitOn

/-!
# Section 3: profile / curve realization (`stat-any-curve`)

This module states the Section 3 realization theorem of the algorithmic-statistics
article (Theorem `stat-any-curve`, attributed to Vereshchagin–Vitányi): every
admissible boundary curve is, up to logarithmic precision, the boundary of the
description profile `P_x` of some string `x`.

The curve is modelled by a function `h : ℕ → ℕ` (`h i = t_i` = admissible log-size
at complexity budget `i`).  `ProfileCurve` collects the article's admissibility
conditions: the boundary connects `(0, n)` to `(kx, 0)`, decreases with slope at
least `-1` (`t_0 > t_1 > … > t_k`), and stays above the sufficiency line
`i + j ≥ kx` (all up to logarithmic slack).

The construction is decomposed into named components:

* Gate E1 (`curveCode`, `KPPlain_curveCode_le`): *removed* — the claim that a
  faithful whole-curve encoding costs only `O(log n)` is false (a generic
  admissible curve has `~n` bits of information) and it was unused; see the
  comment where it stood.  The true incremental content lives in Gate E2's
  `realizingFamily_setComplexity_le`.
* Temporal greedy windows replace the informal nested family of "good" sets `A_i`:
  each held window has size `≤ 2^{h i}` and complexity `≤ i + O(log n)`.
* The constructed string is the lexicographically first length-`n` string that avoids
  all "bad" `(i, h i)`-descriptions; temporal stabilization puts it in every coded
  window.
* Gate F (`realization_upper`): membership in every coded window gives the *upper* half of
  the profile — an `(i + O(log n), h i + O(log n))`-description for every `i`.
* Gate H0 (`exists_string_with_profile`): the main theorem, assembled here from
  Gates F and E3.
-/

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- Total decoder for a coded curve.  The program bits are read as a **run-length
code**: the maximal blocks of `true`, in order and separated by `false`, name the
successive curve values `h 0, h 1, …` (so `[t,t,f,t,f]` decodes to `2, 1, 0, …`).
Reading past the encoded prefix returns `0`.

This is a genuine total, *surjective* decoder — not a placeholder.  Every finite value
sequence is named by some bitstring (`curveEncode`, `decodeCurve_curveEncode`), so the
`curveDecodes` field of `ProfileCurve` is satisfiable for an arbitrary curve
(`exists_code_decoding_curve`) and `ProfileCurve` is *non-vacuous*.  The earlier version
returned the constant `0`; through `curveDecodes` that silently forced `h = 0` on the
whole decoded range, making every `ProfileCurve` hypothesis — and hence the realization
theorems below — vacuous. -/
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

theorem decodeCurve_curveEncode_out_of_bounds (h : ℕ → ℕ) (K : ℕ) {i : ℕ} (hi : K < i) :
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
  /-- Left endpoint: `h 0 ≤ n`.  (This is the faithful `(0, n)` endpoint of the
  article's boundary.  The previous, weaker `h (logSlack c n) ≤ n` was a defect: with
  only that bound `slope` permits `h 0 = n + logSlack c n`, which forces `i + h i` up
  to `n + O(log n)` and makes the genericity counting `sum_badSetsUnion_card_lt` false
  — the level-`0` bad sets alone can have `2^{n+1}` elements.  Requiring `h 0 ≤ n`
  gives `i + h i ≤ n` throughout the positive region, restoring the counting.) -/
  top        : h 0 ≤ n
  bottom     : h (kx + logSlack c n) = 0
  sufficient : ∀ i, kx ≤ i + h i + logSlack c (n + i + h i) + m

/-- Gate E3a: The union of bad sets at budget `i`. -/
noncomputable def badSetsUnion (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (i : ℕ) : Finset BitString :=
  (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))).biUnion id

/-- Gate E3b: The total number of elements in all bad sets at budget `i` is bounded by `2^{i + h i - (m + logSlack c_gen n) + 1}`. -/
theorem badSetsUnion_card_le (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen i : ℕ) :
    (badSetsUnion U n h m c_gen i).card ≤ 2 ^ (i + 1 + (h i - (m + logSlack c_gen n))) := by
  unfold badSetsUnion
  have h_sum : (Finset.sum (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))) (fun S => S.card)) ≤
    (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))).card * 2 ^ (h i - (m + logSlack c_gen n)) := by
    apply Finset.sum_le_card_nsmul
    intro S hS
    unfold descriptionsWithComplexityLeAndSizeLe at hS
    rw [Finset.mem_filter] at hS
    exact hS.2
  have h_card := card_descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))
  calc ((descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))).biUnion id).card
      ≤ Finset.sum (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))) (fun S => S.card) := Finset.card_biUnion_le
    _ ≤ (descriptionsWithComplexityLeAndSizeLe U i (h i - (m + logSlack c_gen n))).card * 2 ^ (h i - (m + logSlack c_gen n)) := h_sum
    _ ≤ 2 ^ (i + 1) * 2 ^ (h i - (m + logSlack c_gen n)) := by gcongr
    _ = 2 ^ (i + 1 + (h i - (m + logSlack c_gen n))) := by rw [← pow_add]

/-- Gate E4a: The set of all elements coverable by an `(i, h i)`-description.
This universe is used to construct the generic point. -/
noncomputable def coverableSet (U : Map) (i : ℕ) (hi : ℕ) : Finset BitString :=
  (descriptionsWithComplexityLeAndSizeLe U i hi).biUnion id

/-- Gate E4b: The total number of elements in all coverable sets at budget `i`
is bounded by `2^{i + h i + 1}`. -/
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
      ≤ Finset.sum (descriptionsWithComplexityLeAndSizeLe U i hi) (fun S => S.card) := Finset.card_biUnion_le
    _ ≤ (descriptionsWithComplexityLeAndSizeLe U i hi).card * 2 ^ hi := h_sum
    _ ≤ 2 ^ (i + 1) * 2 ^ hi := by gcongr
    _ = 2 ^ (i + 1 + hi) := by rw [← pow_add]

/-- Gate G1 (replacing family wrapper): coverableSet gives a profile description. -/
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

/-- Gate G1' (introduction companion to `inDescriptionProfile_of_mem_coverableSet`):
any concrete `(i, j)`-description deposits its elements into `coverableSet U i j`.
If `A ∋ x` is nonempty with `setComplexity U A ≤ i` and `A.card ≤ 2 ^ j`, then
`x ∈ coverableSet U i j`.

This is the membership *introduction* rule the greedy-window step (`STAT_ANY_CURVE`
Gate B5) needs: once the running window `A` is built with `x ∈ A`, size `≤ 2 ^ (h i)`
and (via `setComplexity_le_of_computable_code`, Gate C) complexity
`≤ i + m + O(log n)`, this lemma places `x` into
`coverableSet U (i + m + logSlack c_gen n) (h i)`, exactly the shape consumed by
`exists_point_in_all_coverableSets`.  It is the converse of the elimination lemma
above, so the two together are a clean iff-style bridge between coverable membership
and concrete descriptions. -/
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
  have key : ∀ i ∈ s, (badSetsUnion U n h m c_gen i).card ≤ 2 ^ (n + 1 - A) ∧ i < n := by
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
  have hbound : s.sum (fun i => (badSetsUnion U n h m c_gen i).card) ≤ s.card * 2 ^ (n + 1 - A) := by
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
        (∀ i, ¬ InDescriptionProfile U x i (h i - (m + logSlack c_gen n)) ∨ h i ≤ m + logSlack c_gen n) := by
  obtain ⟨c_gen, hgen⟩ := sum_badSetsUnion_card_lt U
  refine ⟨c_gen, fun n kx m h hc => ?_⟩
  have hgen := hgen c_gen
  have hsum := hgen n kx m h hc
  set s := (Finset.range n).filter (fun i => m + logSlack c_gen n < h i)
  set bad_union := s.biUnion (fun i => badSetsUnion U n h m c_gen i)
  have h_card_bad : bad_union.card < 2 ^ n := by
    calc bad_union.card ≤ s.sum (fun i => (badSetsUnion U n h m c_gen i).card) := Finset.card_biUnion_le
      _ < 2 ^ n := hsum
  have h_card_all : (stringsOfLength n).card = 2 ^ n := cardStringsOfLength n
  have h_exists : ∃ x ∈ stringsOfLength n, x ∉ bad_union := by
    apply Finset.exists_mem_notMem_of_card_lt_card (s := bad_union)
    rw [h_card_all]
    exact h_card_bad
  rcases h_exists with ⟨x, hx_len, hx_not_bad⟩
  refine ⟨x, (memStringsOfLength n x).mp hx_len, fun i => ?_⟩
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

def List.dedup {α} [DecidableEq α] : List α → List α
| [] => []
| a :: l => if a ∈ List.dedup l then List.dedup l else a :: List.dedup l

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
def badSetsUpToTime (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t : ℕ) : List (Finset BitString) :=
  List.dedup (((List.range n).filter (fun j => m + logSlack c_gen n < h j)).flatMap (fun j =>
    (snapshotDescList c j (h j - (m + logSlack c_gen n)) t).map List.toFinset))

/-- Auxiliary: bad sets discovered exactly at time `t`. -/
def newBadSetsAtTime (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t : ℕ) : List (Finset BitString) :=
  let all_at_t := badSetsUpToTime c n h m c_gen t
  match t with
  | 0 => all_at_t
  | t_minus_1 + 1 =>
    let all_at_t_minus_1 := badSetsUpToTime c n h m c_gen t_minus_1
    all_at_t.filter (fun S => S ∉ all_at_t_minus_1)

/-- The chronological enumeration of bad sets up to `t_max`.
    This concatenates the newly discovered sets at each time `t`, ensuring
    the list matches the time-of-discovery order required by the machine model. -/
def temporalBadEnumList (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t_max : ℕ) : List (Finset BitString) :=
  (List.range (t_max + 1)).flatMap (fun t => newBadSetsAtTime c n h m c_gen t)

/-- B0: Flattened list of all bad sets across all levels `j ≤ kx + logSlack c_gen n`.
    WARNING (Blocker identified in Iteration 3): This uses `Finset.toList`, which
    produces a lexicographical order, not the chronological (time-of-discovery) order
    produced by `evaln`. The Vereshchagin-Vitányi machine model simulation requires
    the online, temporal order (`temporalBadEnumList`). Bridging the greedy process
    requires updating the remaining gates to use the temporal list. -/
noncomputable def badEnumList (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen _kx : ℕ) : List (Finset BitString) :=
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

theorem firstElements_subset (S : Finset BitString) (size : ℕ) :
    firstElements S size ⊆ S := GreedyWindow.firstBlock_subset _ _ _

theorem firstElements_card (S : Finset BitString) (size : ℕ) :
    (firstElements S size).card = min size S.card := GreedyWindow.firstBlock_card _ _ _

noncomputable def temporalRefreshCount (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen i t : ℕ) : ℕ :=
  GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i)) (temporalBadEnumList c n h m c_gen t) |>.2.2

noncomputable def temporalWindow (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen i t : ℕ) : Finset BitString :=
  GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i)) (temporalBadEnumList c n h m c_gen t) |>.2.1

/-- B1: The lex-least survivor shared between both halves of the proof.
Intended construction: choose the first length-`n` string outside the finite union of
bad sets.  Existence is the already-proved lower-half counting argument, and the
lexicographic choice pins the same `x` for all windows. -/
noncomputable def lexLeastSurvivor (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ) : BitString :=
  let L := badEnumList U n h m c_gen kx
  let rem := stringsOfLength n \ badUnionUpTo L L.length
  if _hne : rem.Nonempty then
    let first1 : Finset BitString := firstElements rem 1
    if h1 : first1.toList ≠ [] then first1.toList.head h1 else []
  else []

/-- B2: The greedy window sequence. `refresh_k` is the index in `L` where the `k`-th
refresh happens.  Intended construction: scan the finite bad-set enumeration and
advance exactly when the current `2^(h i)`-window has been fully deleted; this is the
finite Vereshchagin-Vitányi running-window process. -/
noncomputable def windowRefreshSequence (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ) : ℕ → ℕ
| 0 => 0
| (k + 1) =>
  let L := badEnumList U n h m c_gen kx
  let r_k := windowRefreshSequence U n h m c_gen kx i k
  let W_k := firstElements ((stringsOfLength n) \ badUnionUpTo L r_k) (2 ^ h i)
  let valid_t := (Finset.Icc r_k L.length).filter (fun t => (W_k \ badUnionUpTo L t) = ∅)
  if hne : valid_t.Nonempty then valid_t.min' hne else L.length

/-- The greedy window itself at step `k`. -/
noncomputable def greedyWindow (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ) (k : ℕ) : Finset BitString :=
  let L := badEnumList U n h m c_gen kx
  let r_k := windowRefreshSequence U n h m c_gen kx i k
  firstElements ((stringsOfLength n) \ badUnionUpTo L r_k) (2 ^ h i)

/-- The greedy window always respects the size budget `2 ^ h i`.  Each version is a
`firstElements`-block of width `2 ^ h i`, so `firstElements_card` bounds its cardinality
by `min (2 ^ h i) …`, regardless of how many survivors remain.  This is the
*unconditional* size half of B5 (`mem_coverableSet_of_window`): only the `setComplexity`
half still needs the version-count core (B4). -/
theorem temporalWindow_card_le (c_U : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen i T : ℕ) :
    (temporalWindow c_U n h m c_gen i T).card ≤ 2 ^ h i := by
  have h_step : ∀ (L' : List (Finset BitString)) (st : Finset BitString × Finset BitString × ℕ), st.2.1.card ≤ 2 ^ h i → (L'.foldl (GreedyWindow.step (stringsOfLength n) (fun S => firstElements S (2 ^ h i))) st).2.1.card ≤ 2 ^ h i := by
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

/-- Every element of a bad-set list is contained in the full running bad-union. -/
theorem subset_badUnionUpTo_full (L : List (Finset BitString)) {d : Finset BitString}
    (hd : d ∈ L) : d ⊆ badUnionUpTo L L.length := by
  unfold badUnionUpTo
  rw [List.take_length]
  have hgrow : ∀ (l : List (Finset BitString)) (s : Finset BitString),
      s ⊆ l.foldl (· ∪ ·) s := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons x xs ih => intro s; exact Finset.subset_union_left.trans (ih (s ∪ x))
  have key : ∀ (l : List (Finset BitString)) (s : Finset BitString),
      d ∈ l → d ⊆ l.foldl (· ∪ ·) s := by
    intro l
    induction l with
    | nil => intro s hd'; simp at hd'
    | cons x xs ih =>
      intro s hd'
      rcases List.mem_cons.mp hd' with rfl | hmem
      · exact Finset.subset_union_right.trans (hgrow xs (s ∪ d))
      · exact ih (s ∪ x) hmem
  exact key L ∅ hd

/-- The refresh index never exceeds the length of the bad-set enumeration. -/
theorem windowRefreshSequence_le_length (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i k : ℕ) :
    windowRefreshSequence U n h m c_gen kx i k ≤ (badEnumList U n h m c_gen kx).length := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    by_cases hne : Finset.Nonempty ( Finset.filter ( fun t => ( firstElements ( ( stringsOfLength n ) \ badUnionUpTo ( badEnumList U n h m c_gen kx ) ( windowRefreshSequence U n h m c_gen kx i k ) ) ( 2 ^ h i ) \ badUnionUpTo ( badEnumList U n h m c_gen kx ) t ) = ∅ ) ( Finset.Icc ( windowRefreshSequence U n h m c_gen kx i k ) ( List.length ( badEnumList U n h m c_gen kx ) ) ) ) <;> simp_all +decide [ windowRefreshSequence ]
    · exact Finset.mem_Icc.mp ( Finset.mem_filter.mp ( Finset.min'_mem _ hne ) |>.1 ) |>.2
    · grind

/-- Under the survivor-existence hypothesis the greedy running-window process reaches
its final snapshot: after `L.length` potential refreshes the refresh index equals
`L.length` (the whole bad enumeration has been consumed).  This is the finite
termination fact of the Vereshchagin–Vitányi running-window construction. -/
theorem windowRefreshSequence_stabilizes (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    windowRefreshSequence U n h m c_gen kx i (badEnumList U n h m c_gen kx).length
      = (badEnumList U n h m c_gen kx).length := by
  -- By induction on `k`, either `seq k = L.length` or `k ≤ seq k`.
  have h_ind : ∀ k, windowRefreshSequence U n h m c_gen kx i k = (badEnumList U n h m c_gen kx).length ∨ k ≤ windowRefreshSequence U n h m c_gen kx i k := by
    intro k
    induction k with
    | zero => simp +arith +decide [windowRefreshSequence]
    | succ k ih =>
      simp +arith +decide [ *, windowRefreshSequence ]
      split_ifs <;> simp_all +decide [ Finset.min' ]
      have h_firstElements_nonempty : (firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (windowRefreshSequence U n h m c_gen kx i k)) (2 ^ h i)).Nonempty := by
        have h_firstElements_nonempty : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (windowRefreshSequence U n h m c_gen kx i k)).Nonempty := by
          refine hrem.mono ?_
          apply Finset.sdiff_subset_sdiff
          · exact Finset.Subset.refl _
          · exact badUnionUpTo_mono _ (windowRefreshSequence_le_length U n h m c_gen kx i k)
        exact Finset.card_pos.mp ( by rw [ firstElements_card ] ; exact lt_min ( Nat.one_le_pow _ _ ( by decide ) ) ( Finset.card_pos.mpr h_firstElements_nonempty ) )
      have h_firstElements_not_subset : ¬(firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (windowRefreshSequence U n h m c_gen kx i k)) (2 ^ h i)) ⊆ badUnionUpTo (badEnumList U n h m c_gen kx) (windowRefreshSequence U n h m c_gen kx i k) := by
        intro h_subset
        obtain ⟨ x, hx ⟩ := h_firstElements_nonempty
        exact Finset.mem_sdiff.mp ( firstElements_subset _ _ hx ) |>.2 ( h_subset hx )
      grind
  cases h_ind ( List.length ( badEnumList U n h m c_gen kx ) ) <;> [ tauto; exact le_antisymm ( windowRefreshSequence_le_length U n h m c_gen kx i _ ) ‹_› ]

/-- B3 (corrected): the final greedy window contains the lex-least survivor.

**The original statement (below, commented out) was FALSE as stated** because it had
no hypothesis guaranteeing that a survivor exists.  For an adversarial curve `h` the
bad enumeration can cover *all* length-`n` strings, so
`stringsOfLength n \ badUnionUpTo L L.length = ∅`; then `lexLeastSurvivor = []`
(the empty string, via the `else` branch of its definition), which for `n ≥ 1` lies
in *no* window (every window is a set of length-`n` strings).  The corrected version
adds the hypothesis `hrem` that the survivor set is nonempty (this is exactly what
the lower-half counting argument `exists_string_avoiding_curve` provides in the
assembled proof).  Under `hrem`, the greedy process stabilizes
(`windowRefreshSequence_stabilizes`) at snapshot `L.length`, where the window is
`firstElements (survivors) (2^{h i})` and contains the smallest survivor, i.e.
`lexLeastSurvivor`. -/
theorem greedyWindow_contains_survivor (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    ∃ v, lexLeastSurvivor U n h m c_gen kx ∈ greedyWindow U n h m c_gen kx i v := by
  use (badEnumList U n h m c_gen kx).length;
  unfold lexLeastSurvivor greedyWindow;
  simp +zetaDelta at *;
  split_ifs;
  · rename_i h;
    replace h := congr_arg Finset.card h ; simp_all +decide [ firstElements_card ];
  · rw [ windowRefreshSequence_stabilizes U n h m c_gen kx i hrem ];
    exact firstElements_mono_size _ ( Nat.one_le_pow _ _ ( by decide ) ) ( Finset.mem_toList.mp ( List.head_mem _ ) )

/-- The `v = L.length` final snapshot of the concrete greedy process contains the
lex-least final survivor.  This is the membership fact needed by the final
`coverableSet` assembly; it uses concrete `windowRefreshSequence` stabilization,
not the temporal fold scaffold. -/
theorem greedyWindow_final_contains_survivor (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    lexLeastSurvivor U n h m c_gen kx ∈
      greedyWindow U n h m c_gen kx i (badEnumList U n h m c_gen kx).length := by
  unfold lexLeastSurvivor greedyWindow
  simp +zetaDelta at *
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

/-- B4 bucket 1 predicate. -/
noncomputable def bucket1_pred (U : Map) (i : ℕ) (d : Finset BitString) : Bool :=
  decide (d ∈ descriptionsWithComplexityLe U i)

/-- B4 bucket 1 bound (fully proved). -/
theorem bucket1_bound (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ) :
    ((badEnumList U n h m c_gen kx).filter (bucket1_pred U i)).length ≤ 2 ^ (i + 1) := by
  have h_nodup : (badEnumList U n h m c_gen kx).Nodup := by
    unfold badEnumList
    exact Finset.nodup_toList _
  have h_len : ((badEnumList U n h m c_gen kx).filter (bucket1_pred U i)).length =
      ((badEnumList U n h m c_gen kx).toFinset.filter (fun d => bucket1_pred U i d)).card := by
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ h_nodup), List.toFinset_filter]
  rw [h_len]
  have h_subset : ((badEnumList U n h m c_gen kx).toFinset.filter (fun d => bucket1_pred U i d)) ⊆ descriptionsWithComplexityLe U i := by
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
  induction hij <;> simp_all +decide
  rename_i k hk ih
  cases hc.slope k <;> linarith [ih (by linarith [hc.antitone (Nat.le_succ k)]), hc.antitone (Nat.le_succ k)]

/-
Per-level card-sum bound (curve-free): the total size of all descriptions at level `j`
with size budget `t` is at most `2 ^ (j + 1 + t)` (there are `≤ 2^(j+1)` of them, each of
card `≤ 2^t`).  Mirrors `badSetsUnion_card_le`.
-/
theorem bucket2_level_card_sum_le (U : Map) (j t : ℕ) (G : Finset BitString) :
    ∑ d ∈ descriptionsWithComplexityLeAndSizeLe U j t, (d ∩ G).card ≤ 2 ^ (j + 1 + t) := by
  refine le_trans (Finset.sum_le_card_nsmul _ _ (2 ^ t) ?_) ?_
  · intro x hx
    exact le_trans (Finset.card_le_card Finset.inter_subset_left) (Finset.mem_filter.mp hx).2
  · rw [smul_eq_mul, pow_add]
    gcongr
    exact card_descriptionsWithComplexityLeAndSizeLe U j t

/-
B4 bucket 2 bound (corrected: with the `ProfileCurve` shape hypothesis, which supplies
the `slope`/`antitone` diagonal descent the bound genuinely needs — see the false-as-stated
original above).
-/
theorem bucket2_bound_of_curve (U : Map) (c n kx m c_gen : ℕ) (h : ℕ → ℕ)
    (hc : ProfileCurve U c n kx m h) (i : ℕ) :
    (((badEnumList U n h m c_gen kx).filter (fun d => !(bucket1_pred U i d))).map (fun d => (d ∩ (stringsOfLength n)).card)).sum ≤
    n * 2 ^ (i + 1 + h i) := by
  have h_filter : ∀ d ∈ (badEnumList U n h m c_gen kx).filter (fun d => !bucket1_pred U i d), ∃ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j), j ≥ i + 1 ∧ d ∈ descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)) := by
    intros d hd; simp_all +decide [ bucket1_pred, badEnumList ] ;
    obtain ⟨ ⟨ j, hj₁, hj₂ ⟩, hj₃ ⟩ := hd;
    refine ⟨ j, hj₁, ?_, hj₂ ⟩;
    contrapose! hj₃;
    unfold descriptionsWithComplexityLeAndSizeLe at hj₂; simp_all +decide;
    unfold descriptionsWithComplexityLe at *; simp_all +decide;
    obtain ⟨ a, ha₁, ha₂ ⟩ := hj₂.1;
    unfold modelsWithComplexityLe at *; simp_all +decide;
    obtain ⟨ b, hb₁, hb₂ ⟩ := ha₁; use b; simp_all +decide [ boundedPrograms ] ;
    exact ⟨ hb₁.choose, le_trans hb₁.choose_spec.1 hj₃, hb₁.choose_spec.2 ⟩;
  have h_filter_sum : ∑ d ∈ (badEnumList U n h m c_gen kx).toFinset.filter (fun d => !bucket1_pred U i d), (d ∩ stringsOfLength n).card ≤ ∑ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j), if j ≥ i + 1 then ∑ d ∈ descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)), (d ∩ stringsOfLength n).card else 0 := by
    have h_filter_sum : ∑ d ∈ (badEnumList U n h m c_gen kx).toFinset.filter (fun d => !bucket1_pred U i d), (d ∩ stringsOfLength n).card ≤ ∑ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j), ∑ d ∈ (badEnumList U n h m c_gen kx).toFinset.filter (fun d => !bucket1_pred U i d), if d ∈ descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)) ∧ j ≥ i + 1 then (d ∩ stringsOfLength n).card else 0 := by
      rw [ Finset.sum_comm ];
      gcongr;
      simp +zetaDelta at *;
      obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := h_filter _ ( by tauto ) ( by tauto ) ; exact le_trans ( by aesop ) ( Finset.single_le_sum ( fun x _ => Nat.zero_le _ ) ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hj₁.1, hj₁.2 ⟩ ) ) ;
    refine le_trans h_filter_sum <| Finset.sum_le_sum fun j hj => ?_;
    split_ifs <;> simp_all +decide [ Finset.sum_ite ];
    exact Finset.sum_le_sum_of_subset ( Finset.inter_subset_right );
  have h_filter_sum_le : ∑ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j), (if j ≥ i + 1 then 2 ^ (j + 1 + (h j - (m + logSlack c_gen n))) else 0) ≤ n * 2 ^ (i + 1 + h i) := by
    have h_filter_sum_le : ∀ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j), j ≥ i + 1 → 2 ^ (j + 1 + (h j - (m + logSlack c_gen n))) ≤ 2 ^ (i + 1 + h i) := by
      intros j hj hj_ge_i
      have h_diag : j + h j ≤ i + h i := by
        apply profileCurve_diag_le U c n kx m h hc i j (by linarith) (by
        grind);
      exact pow_le_pow_right₀ ( by decide ) ( by linarith [ Nat.sub_le ( h j ) ( m + logSlack c_gen n ) ] );
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
  convert h_filter_sum.trans _ |> le_trans <| h_filter_sum_le using 1;
  · rw [ ← List.sum_toFinset ];
    · congr! 1;
      ext; simp [List.mem_toFinset];
    · exact List.Nodup.filter _ (Finset.nodup_toList _)
  · gcongr;
    split_ifs <;> [ exact bucket2_level_card_sum_le _ _ _ _; exact Nat.zero_le _ ]

/- B4: the true visited version count.
   This counts the number of physical refreshes the running window makes over
   a list of bad sets `L`, once the concrete refresh sequence has been refactored
   to take `L` as an explicit input. -/
noncomputable def visitedVersionCountOfList (L : List (Finset BitString)) (seq : ℕ → ℕ) : ℕ :=
  (Finset.range L.length).filter (fun k => seq k < seq (k + 1)) |>.card

/-
The temporal bridge is intentionally not stated as a theorem yet: the current
`windowRefreshSequence` still hardcodes `badEnumList`, so a faithful statement first
needs the refresh process parameterized by a list and then related to
`GreedyWindow.fold` for `temporalBadEnumList`.
-/

/-- **Abstract greedy-fold version-count bound (survivor + curve form).**  This assembles
the abstract survivor combinatorics `GreedyWindow.fold_count_split_div_le_of_survivor`
(which replaces the false `greedyWindow_fold_room` room hypothesis by the *satisfiable*
survivor-nonempty hypothesis `hsurv`) with the two fully-proved bucket bounds:
`bucket1_bound` (bucket 1: sets that are themselves descriptions of complexity `≤ i`,
at most `2 ^ (i+1)` of them, each triggering at most one refresh) and
`bucket2_bound_of_curve` (bucket 2: the higher-level deletion mass, `≤ n · 2 ^ (i+1+h i)`
under the `ProfileCurve` slope, divided by the window width `2 ^ h i`).  Hence the number
of refreshes of the abstract greedy fold over `badEnumList` is at most
`2 ^ (i+1) + n · 2 ^ (i+1) = (n+1) · 2 ^ (i+1)`.  In bits this is `i + O(log n)`, which is
exactly the Vereshchagin–Vitányi version-count budget consumed inside `coverableSet`.
The live proof uses the temporal enumeration/decoder path below; the older static
`windowRefreshSequence` bridge is intentionally left retired because its fallback counter
does not track strict temporal refreshes. -/
theorem greedyFold_version_count_le_of_survivor_curve
    (U : Map) (c n kx m c_gen : ℕ) (h : ℕ → ℕ) (hc : ProfileCurve U c n kx m h) (i : ℕ)
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
    (badEnumList U n h m c_gen kx) (bucket1_pred U i) hsurv
  refine hbound.trans (add_le_add (bucket1_bound U n h m c_gen kx i) ?_)
  calc (((badEnumList U n h m c_gen kx).filter (fun d => !bucket1_pred U i d)).map
          (fun d => (d ∩ stringsOfLength n).card)).sum / 2 ^ h i
      ≤ (n * 2 ^ (i + 1 + h i)) / 2 ^ h i :=
        Nat.div_le_div_right (bucket2_bound_of_curve U c n kx m c_gen h hc i)
    _ = n * 2 ^ (i + 1) := by
        rw [pow_add, ← mul_assoc, Nat.mul_div_cancel _ hW]

/- **Room hypothesis for the greedy window fold — FALSE as literally stated.**

The accumulated deleted set of the fold is exactly `badUnionUpTo L L.length ∩ stringsOfLength n`
(the `step` always unions `d ∩ G` into `deleted`, independent of the window), so the claim is
`|badUnion ∩ strings_n| + 2 ^ (h i) ≤ 2 ^ n`.  This is false already for `n = 0, h ≡ 1`
(`0 + 2 ≤ 1`), and even under `ProfileCurve` it fails at the top of the curve: when
`h 0 = n` (allowed by the `top` field) the level-`0` bad sets are nonempty while
`2 ^ (h 0) = 2 ^ n`, so no room remains.  A correct room bound must delete only the bad
sets of the *relevant* levels (`≥ i`).  The live proof avoids this false room condition by
using the survivor-based split bound (`GreedyWindow.fold_count_split_div_le_of_survivor`)
and the temporal enumeration/decoder construction.  This block is kept only to explain why
the old room route was retired.

```
theorem greedyWindow_fold_room (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ) :
    (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
            (badEnumList U n h m c_gen kx)).1.card + 2 ^ h i ≤ (stringsOfLength n).card := by
  -- retired false route
```
-/
/- The live `greedyWindow_fold_room` theorem is commented out: it is FALSE as stated (see
above).  It fed only the now-dead `greedyWindow_version_count_le`.
```
theorem greedyWindow_fold_room (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i : ℕ) :
    (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
            (badEnumList U n h m c_gen kx)).1.card + 2 ^ h i ≤ (stringsOfLength n).card := by
  -- retired false route
```
-/

/- **B4 `greedyWindow_version_count_le` — commented out (dead scaffolding).**

This wrapper is unused anywhere in the development, and it is built from the three
false-as-stated B4 lemmas above (`greedyWindow_version_count_eq_fold` and
`greedyWindow_fold_room`, both false; `bucket2_bound`, false without a curve hypothesis).
The genuine combinatorial content it aimed at is the abstract, fully-proved
`GreedyWindow.fold_count_split_div_le`; the accepted proof instead uses the survivor-based
split bound and the temporal window decoder, so this static wrapper remains only as a record
of the retired approach.

```
theorem greedyWindow_version_count_le (U : Map) (c n kx m c_gen : ℕ) (h : ℕ → ℕ)
    (hc : ProfileCurve U c n kx m h) (i v : ℕ)
    (h_pos : 0 < 2 ^ h i)
    (hv : windowRefreshSequence U n h m c_gen kx i v = (badEnumList U n h m c_gen kx).length) :
    v ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) := by
  have h_eq := greedyWindow_version_count_eq_fold U n h m c_gen kx i v hv
  have h_room := greedyWindow_fold_room U n h m c_gen kx i
  have h_div := GreedyWindow.fold_count_split_div_le (stringsOfLength n) (2 ^ h i) h_pos
    (fun S => firstElements S (2 ^ h i))
    (fun S => firstElements_subset S (2 ^ h i))
    (fun S => firstElements_card S (2 ^ h i))
    (badEnumList U n h m c_gen kx) (bucket1_pred U i) h_room
  have hb1 := bucket1_bound U n h m c_gen kx i
  have hb2 := bucket2_bound_of_curve U c n kx m c_gen h hc i
  calc v ≤ (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i)) (badEnumList U n h m c_gen kx)).2.2 := h_eq
    _ ≤ ((badEnumList U n h m c_gen kx).filter (bucket1_pred U i)).length +
        (((badEnumList U n h m c_gen kx).filter (fun d => !(bucket1_pred U i d))).map (fun d => (d ∩ (stringsOfLength n)).card)).sum / 2 ^ h i := h_div
    _ ≤ 2 ^ (i + 1) + (n * 2 ^ (i + 1 + h i)) / 2 ^ h i := by gcongr
    _ = 2 ^ (i + 1) + n * 2 ^ (i + 1) := by
      have h_pow : n * 2 ^ (i + 1 + h i) = (n * 2 ^ (i + 1)) * 2 ^ h i := by
        rw [pow_add, mul_assoc]
      rw [h_pow, Nat.mul_div_cancel _ h_pos]
```
-/

/-
Old temporal-fold analogue of `greedyWindow_final_contains_survivor` without the
stability/completeness hypotheses.  The static argument alone is false: a held temporal
window can contain some final survivor while excluding the globally lex-least final
survivor, because strings deleted after the last refresh may have smaller `decodeBits`
order and can crowd the lex-least survivor out of the held block.  The live theorem
`temporalWindow_contains_survivor` below repairs this by extending the chronological
enumeration to a complete later time and using refresh-count stability over the suffix.

```
theorem temporalWindow_contains_survivor ... :
    lexLeastSurvivor U n h m c_gen kx ∈ temporalWindow c_U n h m c_gen i T := by
  -- retired false route
```
-/

theorem List.flatMap_congr_loc {α β} (l : List α) (f g : α → List β) (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  have : List.map f l = List.map g l := List.map_congr_left h
  unfold List.flatMap
  rw [this]

theorem badSetsUpToTime_eq_of_max (c : Nat.Partrec.Code) {U : Map} (hc : IsCodeFor c U) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t t₀ : ℕ)
    (h_ge : t₀ ≤ t)
    (hmax : ∀ j, j < n → ∀ t', countHalts c j t' ≤ countHalts c j t₀) :
    badSetsUpToTime c n h m c_gen t = badSetsUpToTime c n h m c_gen t₀ := by
  unfold badSetsUpToTime
  congr 1
  apply List.flatMap_congr_loc
  intro j hj
  simp only [List.mem_filter, List.mem_range] at hj
  exact congrArg (fun L => L.map List.toFinset) (snapshotDescList_eq_of_max hc j (h j - (m + logSlack c_gen n)) t t₀ h_ge (hmax j hj.1))

theorem newBadSetsAtTime_eq_nil_of_gt (c : Nat.Partrec.Code) {U : Map} (hc : IsCodeFor c U) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t t₀ : ℕ)
    (h_gt : t₀ < t)
    (hmax : ∀ j, j < n → ∀ t', countHalts c j t' ≤ countHalts c j t₀) :
    newBadSetsAtTime c n h m c_gen t = [] := by
  obtain ⟨t_minus_1, ht⟩ : ∃ x, t = x + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) h_gt))
  subst ht
  have h_ge : t₀ ≤ t_minus_1 := Nat.le_of_lt_succ h_gt
  have ht_ge : t₀ ≤ t_minus_1 + 1 := Nat.le_succ_of_le h_ge
  have h1 := badSetsUpToTime_eq_of_max c hc n h m c_gen (t_minus_1 + 1) t₀ ht_ge hmax
  have h2 := badSetsUpToTime_eq_of_max c hc n h m c_gen t_minus_1 t₀ h_ge hmax
  unfold newBadSetsAtTime
  simp only [h1, h2]
  exact List.filter_eq_nil_iff.mpr (fun S hS => by simp_all)

theorem temporalBadEnumList_eq_of_max_aux (c : Nat.Partrec.Code) {U : Map} (hc : IsCodeFor c U) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t₀ k : ℕ)
    (h_ge : t₀ ≤ k)
    (hmax : ∀ j, j < n → ∀ t', countHalts c j t' ≤ countHalts c j t₀) :
    temporalBadEnumList c n h m c_gen k = temporalBadEnumList c n h m c_gen t₀ := by
  induction k, h_ge using Nat.le_induction with
  | base => rfl
  | succ k h_ge_k ih =>
    unfold temporalBadEnumList
    have h_range : List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] := by
      exact List.range_succ
    rw [h_range]
    rw [List.flatMap_append, List.flatMap_singleton]
    have h_ih : (List.range (k + 1)).flatMap (fun t => newBadSetsAtTime c n h m c_gen t) = temporalBadEnumList c n h m c_gen k := rfl
    rw [h_ih]
    have h_nil : newBadSetsAtTime c n h m c_gen (k + 1) = [] := by
      have h_gt : t₀ < k + 1 := Nat.lt_succ_of_le h_ge_k
      exact newBadSetsAtTime_eq_nil_of_gt c hc n h m c_gen (k + 1) t₀ h_gt hmax
    rw [h_nil, List.append_nil]
    exact ih

theorem temporalBadEnumList_eq_of_max (c : Nat.Partrec.Code) {U : Map} (hc : IsCodeFor c U) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ) (t t₀ : ℕ)
    (h_ge : t₀ ≤ t)
    (hmax : ∀ j, j < n → ∀ t', countHalts c j t' ≤ countHalts c j t₀) :
    temporalBadEnumList c n h m c_gen t = temporalBadEnumList c n h m c_gen t₀ :=
  temporalBadEnumList_eq_of_max_aux c hc n h m c_gen t₀ t h_ge hmax

/-- Split sublemma: Bounding the total number of refreshes for the temporal bad enum list.
    This separates the combinatorics (Nodup, mapping to descriptions) from the stabilization loop. -/
theorem temporalBadEnumList_sublist_badEnumList (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx T : ℕ) :
    ∀ x, x ∈ temporalBadEnumList c_U n h m c_gen T → x ∈ badEnumList U n h m c_gen kx := by
  intro d hd
  unfold temporalBadEnumList at hd
  obtain ⟨t, _ht⟩ : ∃ t, d ∈ newBadSetsAtTime c_U n h m c_gen t ∧ t ≤ T := by
    simp only [List.mem_flatMap, List.mem_range] at hd
    rcases hd with ⟨t, _, hd⟩
    exact ⟨t, hd, by omega⟩
  have h_subset : d ∈ badSetsUpToTime c_U n h m c_gen t := by
    cases t <;> simp_all [newBadSetsAtTime]
  obtain ⟨j, hj⟩ : ∃ j, j ∈ (List.range n).filter (fun j => m + logSlack c_gen n < h j) ∧ d ∈ (snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map List.toFinset := by
    unfold badSetsUpToTime at h_subset
    rw [mem_List.dedup] at h_subset
    aesop
  have h_subset_desc : d ∈ descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)) := by
    have h_mem : d ∈ (snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map List.toFinset → d ∈ snapshotDescriptionsAndSizeLe c_U j (h j - (m + logSlack c_gen n)) t := by
      intro hd_map
      have h_nodup := snapshotDescList_nodup_map_toFinset c_U j (h j - (m + logSlack c_gen n)) t
      rcases List.mem_map.mp hd_map with ⟨orig, horig, heq⟩
      subst heq
      rw [← h_nodup.2]
      exact List.mem_toFinset.mpr (List.mem_map_of_mem (f := List.toFinset) horig)
    exact snapshotDescriptionsAndSizeLe_subset_descriptions hc_code j (h j - (m + logSlack c_gen n)) t (h_mem hj.2)
  have h_final : d ∈ (badEnumList U n h m c_gen kx).toFinset := by
    unfold badEnumList
    aesop
  exact List.mem_toFinset.mp h_final

theorem filter_length_le_of_subset_of_nodup {α} (L1 L2 : List α) (p : α → Bool)
    (h_nodup1 : L1.Nodup) (h_nodup2 : L2.Nodup)
    (h_sub : ∀ x ∈ L1, x ∈ L2) :
    (L1.filter p).length ≤ (L2.filter p).length := by
  classical
  have h1 : (L1.filter p).length = (L1.toFinset.filter (fun x => p x = true)).card := by
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter p h_nodup1)]
    exact congr_arg Finset.card (List.toFinset_filter L1 p)
  have h2 : (L2.filter p).length = (L2.toFinset.filter (fun x => p x = true)).card := by
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter p h_nodup2)]
    exact congr_arg Finset.card (List.toFinset_filter L2 p)
  rw [h1, h2]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨List.mem_toFinset.mpr (h_sub x (List.mem_toFinset.mp hx.1)), hx.2⟩

theorem filter_sum_toFinset_eq {α} [DecidableEq α] (L : List α) (p : α → Bool) (f : α → ℕ)
    (h_nodup : L.Nodup) :
    ((L.toFinset.filter (fun x => p x = true)).toList.map f).sum = ((L.filter p).map f).sum := by
  let S := L.toFinset.filter (fun x => p x = true)
  have hleft : ((L.toFinset.filter (fun x => p x = true)).toList.map f).sum = S.sum f := by
    symm
    simp [S]
  have hright : ((L.filter p).map f).sum = S.sum f := by
    symm
    have hnod : (L.filter p).Nodup := List.Nodup.filter p h_nodup
    simpa [S, List.toFinset_filter] using (List.sum_toFinset f (l := L.filter p) hnod)
  rw [hleft, hright]

theorem filter_sum_le_of_subset_of_nodup {α} (L1 L2 : List α) (p : α → Bool) (f : α → ℕ)
    (h_nodup1 : L1.Nodup) (h_nodup2 : L2.Nodup)
    (h_sub : ∀ x ∈ L1, x ∈ L2) :
    ((L1.filter p).map f).sum ≤ ((L2.filter p).map f).sum := by
  classical
  let S1 := L1.toFinset.filter (fun x => p x = true)
  let S2 := L2.toFinset.filter (fun x => p x = true)
  have h1 : ((L1.filter p).map f).sum = S1.sum f := by
    symm
    have hnod : (L1.filter p).Nodup := List.Nodup.filter p h_nodup1
    simpa [S1, List.toFinset_filter] using (List.sum_toFinset f (l := L1.filter p) hnod)
  have h2 : ((L2.filter p).map f).sum = S2.sum f := by
    symm
    have hnod : (L2.filter p).Nodup := List.Nodup.filter p h_nodup2
    simpa [S2, List.toFinset_filter] using (List.sum_toFinset f (l := L2.filter p) hnod)
  rw [h1, h2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨List.mem_toFinset.mpr (h_sub x (List.mem_toFinset.mp hx.1)), hx.2⟩
  · intro x _ _
    exact Nat.zero_le (f x)

/-- `List.dedup` produces a duplicate-free list. -/
theorem List.dedup_nodup {α} [DecidableEq α] (l : List α) : (List.dedup l).Nodup := by
  induction l with
  | nil => simp [List.dedup]
  | cons a l ih =>
    unfold List.dedup
    split_ifs with hmem
    · exact ih
    · exact List.nodup_cons.mpr ⟨hmem, ih⟩

/-- The snapshot bad-set enumeration up to time `t` is duplicate-free. -/
theorem badSetsUpToTime_nodup (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen t : ℕ) :
    (badSetsUpToTime c n h m c_gen t).Nodup := by
  unfold badSetsUpToTime
  exact List.dedup_nodup _

/-- Membership in `badSetsUpToTime` is monotone in the time budget: the snapshot
description universe only grows. -/
theorem badSetsUpToTime_mem_mono (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ)
    {t t' : ℕ} (hle : t ≤ t') {d : Finset BitString}
    (hd : d ∈ badSetsUpToTime c n h m c_gen t) :
    d ∈ badSetsUpToTime c n h m c_gen t' := by
  unfold badSetsUpToTime at hd ⊢
  rw [mem_List.dedup] at hd ⊢
  rw [List.mem_flatMap] at hd ⊢
  obtain ⟨j, hj, hdj⟩ := hd
  refine ⟨j, hj, ?_⟩
  -- Convert list membership to membership in `snapshotDescriptionsAndSizeLe`,
  -- use its monotonicity, and convert back.
  have hkey : ∀ s, (d ∈ (snapshotDescList c j (h j - (m + logSlack c_gen n)) s).map List.toFinset)
      ↔ d ∈ snapshotDescriptionsAndSizeLe c j (h j - (m + logSlack c_gen n)) s := by
    intro s
    rw [← List.mem_toFinset, snapshotDescList_nodup_map_toFinset c j (h j - (m + logSlack c_gen n)) s |>.2]
  rw [hkey] at hdj ⊢
  exact snapshotDescriptionsAndSizeLe_subset_of_le c j (h j - (m + logSlack c_gen n)) hle hdj

/-- The newly-discovered bad sets at time `t` are among those discovered up to `t`. -/
theorem newBadSetsAtTime_mem_badSetsUpToTime (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ)
    (m c_gen t : ℕ) {d : Finset BitString}
    (hd : d ∈ newBadSetsAtTime c n h m c_gen t) :
    d ∈ badSetsUpToTime c n h m c_gen t := by
  cases t with
  | zero => simpa [newBadSetsAtTime] using hd
  | succ s =>
    rw [newBadSetsAtTime, List.mem_filter] at hd
    exact hd.1

/-- The newly-discovered bad sets at time `t` are duplicate-free. -/
theorem newBadSetsAtTime_nodup (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen t : ℕ) :
    (newBadSetsAtTime c n h m c_gen t).Nodup := by
  cases t with
  | zero => simpa [newBadSetsAtTime] using badSetsUpToTime_nodup c n h m c_gen 0
  | succ s =>
    rw [newBadSetsAtTime]
    exact (badSetsUpToTime_nodup c n h m c_gen (s + 1)).filter _

/-- Bad sets discovered at distinct times are disjoint: a set first discovered at
time `t` is already in `badSetsUpToTime` at every later time, so it is filtered out
of `newBadSetsAtTime` there. -/
theorem newBadSetsAtTime_disjoint (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ)
    {t t' : ℕ} (hlt : t < t') :
    List.Disjoint (newBadSetsAtTime c n h m c_gen t) (newBadSetsAtTime c n h m c_gen t') := by
  intro d hd hd'
  obtain ⟨s, rfl⟩ : ∃ s, t' = s + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rw [newBadSetsAtTime, List.mem_filter] at hd'
  have hts : t ≤ s := Nat.lt_succ_iff.mp hlt
  have : d ∈ badSetsUpToTime c n h m c_gen s :=
    badSetsUpToTime_mem_mono c n h m c_gen hts
      (newBadSetsAtTime_mem_badSetsUpToTime c n h m c_gen t hd)
  simp only [decide_eq_true_eq] at hd'
  exact hd'.2 this

theorem temporalBadEnumList_nodup (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen t : ℕ) :
    (temporalBadEnumList c n h m c_gen t).Nodup := by
  unfold temporalBadEnumList
  rw [List.nodup_flatMap]
  refine ⟨fun x _ => newBadSetsAtTime_nodup c n h m c_gen x, ?_⟩
  refine (List.pairwise_lt_range (n := t + 1)).imp ?_
  intro a b hab
  exact newBadSetsAtTime_disjoint c n h m c_gen hab

theorem temporalBadEnumList_bound (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U) (n kx : ℕ) (h : ℕ → ℕ) (m c_gen i t : ℕ) (c : ℕ) (hc : ProfileCurve U c n kx m h) (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length).Nonempty) :
    (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
      (temporalBadEnumList c_U n h m c_gen t)).2.2 ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) := by
  have hW : 0 < 2 ^ h i := pow_pos (by decide) _
  have h_surv : (stringsOfLength n \ (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i)) (temporalBadEnumList c_U n h m c_gen t)).1).Nonempty := by
    -- The temporal deletions are all elements of `badEnumList`, so the fold's deleted
    -- set is contained in the full `badUnionUpTo`, and `hrem` supplies a survivor.
    obtain ⟨x, hx⟩ := hrem
    rw [Finset.mem_sdiff] at hx
    refine ⟨x, ?_⟩
    rw [Finset.mem_sdiff]
    refine ⟨hx.1, fun hxdel => hx.2 ?_⟩
    have hsub : (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i))
        (temporalBadEnumList c_U n h m c_gen t)).1
          ⊆ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length := by
      refine GreedyWindow.fold_deleted_subset _ _ _ _ (fun d hd => ?_)
      have hdmem : d ∈ badEnumList U n h m c_gen kx :=
        temporalBadEnumList_sublist_badEnumList U c_U hc_code n h m c_gen kx t d hd
      exact Finset.inter_subset_left.trans (subset_badUnionUpTo_full _ hdmem)
    exact hsub hxdel
  have h_bound := GreedyWindow.fold_count_split_div_le_of_survivor_toFinset (stringsOfLength n) (2 ^ h i) hW (fun S => firstElements S (2 ^ h i)) (fun S => firstElements_subset S (2 ^ h i)) (fun S => firstElements_card S (2 ^ h i)) (temporalBadEnumList c_U n h m c_gen t) (bucket1_pred U i) (temporalBadEnumList_nodup c_U n h m c_gen t) h_surv
  have h_nodup1 := temporalBadEnumList_nodup c_U n h m c_gen t
  have h_nodup2 : (badEnumList U n h m c_gen kx).Nodup := by
    unfold badEnumList
    exact Finset.nodup_toList _
  have h_sub := temporalBadEnumList_sublist_badEnumList U c_U hc_code n h m c_gen kx t
  have h_len_le := filter_length_le_of_subset_of_nodup _ _ (bucket1_pred U i) h_nodup1 h_nodup2 h_sub
  have h_sum_le := filter_sum_le_of_subset_of_nodup _ _ (fun d => !bucket1_pred U i d) (fun d => (d ∩ stringsOfLength n).card) h_nodup1 h_nodup2 h_sub
  have h_len_b1 := bucket1_bound U n h m c_gen kx i
  have h_sum_b2 := bucket2_bound_of_curve U c n kx m c_gen h hc i
  have h_len_eq : ((temporalBadEnumList c_U n h m c_gen t).toFinset.filter (fun d => bucket1_pred U i d = true)).card = ((temporalBadEnumList c_U n h m c_gen t).filter (bucket1_pred U i)).length := by
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ h_nodup1)]
    exact congr_arg Finset.card (List.toFinset_filter _ _).symm
  have h_sum_eq : (((temporalBadEnumList c_U n h m c_gen t).toFinset.filter (fun d => !(bucket1_pred U i d) = true)).toList.map (fun d => (d ∩ stringsOfLength n).card)).sum = (((temporalBadEnumList c_U n h m c_gen t).filter (fun d => !bucket1_pred U i d)).map (fun d => (d ∩ stringsOfLength n).card)).sum := by
    simpa using (filter_sum_toFinset_eq (temporalBadEnumList c_U n h m c_gen t)
      (fun d => !bucket1_pred U i d) (fun d => (d ∩ stringsOfLength n).card) h_nodup1)
  calc (GreedyWindow.fold (stringsOfLength n) (fun S => firstElements S (2 ^ h i)) (temporalBadEnumList c_U n h m c_gen t)).2.2
    _ ≤ ((temporalBadEnumList c_U n h m c_gen t).toFinset.filter (fun d => bucket1_pred U i d = true)).card +
        (((temporalBadEnumList c_U n h m c_gen t).toFinset.filter (fun d => !(bucket1_pred U i d) = true)).toList.map (fun d => (d ∩ stringsOfLength n).card)).sum / 2 ^ h i := h_bound
    _ = ((temporalBadEnumList c_U n h m c_gen t).filter (bucket1_pred U i)).length +
        (((temporalBadEnumList c_U n h m c_gen t).filter (fun d => !bucket1_pred U i d)).map (fun d => (d ∩ stringsOfLength n).card)).sum / 2 ^ h i := by
      rw [h_len_eq, h_sum_eq]
    _ ≤ ((badEnumList U n h m c_gen kx).filter (bucket1_pred U i)).length +
        (((badEnumList U n h m c_gen kx).filter (fun d => !bucket1_pred U i d)).map (fun d => (d ∩ stringsOfLength n).card)).sum / 2 ^ h i := by
      apply Nat.add_le_add
      · exact h_len_le
      · exact Nat.div_le_div_right h_sum_le
    _ ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1 + h i) / 2 ^ h i := by
      apply Nat.add_le_add
      · exact h_len_b1
      · exact Nat.div_le_div_right h_sum_b2
    _ = 2 ^ (i + 1) + n * 2 ^ (i + 1) := by
      have h_pow : 2 ^ (i + 1 + h i) = 2 ^ (i + 1) * 2 ^ h i := pow_add 2 (i + 1) (h i)
      rw [h_pow]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_div_cancel _ hW]

/-
Simultaneous stabilization of the halting-count snapshots across all finitely many
levels `j < n`.  Each `countHalts c j ·` is monotone (`countHalts_mono`) and bounded
(`countHalts_le_length`), hence eventually constant at its maximum (`exists_max_countHalts`);
taking the maximum of the finitely many stabilization times yields a single `t₀` that is
simultaneously a stabilization point and a level-wise maximum.
-/
theorem exists_simultaneous_stable_countHalts (c : Nat.Partrec.Code) (n : ℕ) :
    ∃ t₀, (∀ j < n, ∀ t ≥ t₀, countHalts c j t = countHalts c j t₀) ∧
          (∀ j < n, ∀ t', countHalts c j t' ≤ countHalts c j t₀) := by
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, ∀ j < n, ∀ t ≥ t₀, countHalts c j t = countHalts c j t₀ := by
    have h_const : ∀ j < n, ∃ t₀, ∀ t ≥ t₀, countHalts c j t = countHalts c j t₀ := by
      intro j hj
      obtain ⟨t₀, ht₀⟩ : ∃ t₀, ∀ t', countHalts c j t' ≤ countHalts c j t₀ := exists_max_countHalts c j;
      exact ⟨ t₀, fun t ht => le_antisymm ( ht₀ t ) ( countHalts_mono c j ht ) ⟩;
    choose! t₀ ht₀ using h_const;
    use Finset.sup (Finset.range n) t₀;
    intro j hj t ht;
    rw [ ht₀ j hj t ( le_trans ( Finset.le_sup ( f := t₀ ) ( Finset.mem_range.mpr hj ) ) ht ), ht₀ j hj ( Finset.sup ( Finset.range n ) t₀ ) ( Finset.le_sup ( f := t₀ ) ( Finset.mem_range.mpr hj ) ) ];
  use t₀;
  grind +suggestions

/-- T1: The temporal refresh count is bounded and stabilizes to `version*`. -/
theorem temporalRefreshCount_stabilizes (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U) (c n kx m c_gen i : ℕ) (h : ℕ → ℕ) (hc : ProfileCurve U c n kx m h)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length).Nonempty) :
    ∃ T version, version ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) + 1 ∧
      temporalRefreshCount c_U n h m c_gen i T = version ∧
      ∀ t ≥ T, temporalRefreshCount c_U n h m c_gen i t = version := by
  obtain ⟨t₀, _ht₀, hmax⟩ := exists_simultaneous_stable_countHalts c_U n
  use t₀
  use temporalRefreshCount c_U n h m c_gen i t₀
  refine ⟨?_, rfl, ?_⟩
  · have h_bound := temporalBadEnumList_bound U c_U hc_code n kx h m c_gen i t₀ c hc hrem
    unfold temporalRefreshCount
    exact Nat.le_succ_of_le h_bound
  · intro t ht
    unfold temporalRefreshCount
    rw [temporalBadEnumList_eq_of_max c_U hc_code n h m c_gen t t₀ ht hmax]

/-
**T2/T4 `temporalWindow_contains_survivor` — retired (FALSE as stated).**

This asserted `lexLeastSurvivor … ∈ temporalWindow …`.  Unlike `windowRefreshSequence`
(whose `_stabilizes` lemma pins the final refresh index at `L.length`, so the final window
is `firstElements (survivors) (2^{h i})`), the abstract `GreedyWindow.fold` only refreshes
when the window is fully deleted; at the end the window is the block installed at the *last*
refresh, `firstElements (G \ deletedₖ) (2^{h i})` for an earlier `deletedₖ ⊆ deleted_final`.
Because `firstElements` keeps the `decodeBits`-smallest elements and
`G \ deletedₖ ⊇ G \ deleted_final`, the globally lex-least survivor need not be among the
smallest elements of the larger set `G \ deletedₖ` — smaller strings deleted only *after* the
last refresh can crowd it out.  So the final window contains *some* survivor, but not
necessarily *this* one from a static argument alone.

The repaired route below adds the missing temporal information: extend the chronological
enumeration to a complete later time and use stability of the refresh count over the suffix.
If a smaller still-live element crowded out the global survivor at time `T`, the suffix would
eventually delete it and force another refresh, contradicting stability.

Conditional bridge from the abstract greedy-window survivor lemma to the concrete
temporal process.

This conditional bridge is used below after the completeness/stability lemmas provide
a later time `T_full` whose temporal list is the old list plus a suffix containing all
still-missing bad sets, and whose suffix adds no refresh.  The final hypothesis packages
the lex-minimality fact for the chosen complete list.
-/
theorem temporalWindow_contains_survivor_of_append_no_refresh
    (c_U : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen i T T_full : ℕ)
    (x : BitString) (hxG : x ∈ stringsOfLength n)
    (L_rest : List (Finset BitString))
    (h_append :
      temporalBadEnumList c_U n h m c_gen T_full =
        temporalBadEnumList c_U n h m c_gen T ++ L_rest)
    (h_no_refresh :
      temporalRefreshCount c_U n h m c_gen i T_full =
        temporalRefreshCount c_U n h m c_gen i T)
    (h_surv :
      ∀ d ∈ temporalBadEnumList c_U n h m c_gen T_full,
        x ∉ d)
    (h_min :
      ∀ y, y ∈ stringsOfLength n →
        (∀ d ∈ temporalBadEnumList c_U n h m c_gen T_full, y ∉ d) →
          Encodable.encode x ≤ Encodable.encode y) :
    x ∈ temporalWindow c_U n h m c_gen i T := by
  have := @Kolmogorov.GreedyWindow.temporalWindow_contains_survivor_aux;
  unfold temporalWindow;
  convert this ( stringsOfLength n ) Encodable.encode ( 2 ^ h i ) ( pow_pos ( by decide ) _ ) ( temporalBadEnumList c_U n h m c_gen T ) L_rest x _ hxG _ _ _ using 1;
  · exact fun d hd => h_surv d <| h_append ▸ hd;
  · convert h_no_refresh using 1;
    exact h_append ▸ rfl;
  · exact fun y hy hy' => h_min y hy fun d hd => hy' d <| h_append ▸ hd;
  · exact fun a b ha hb h => Encodable.encode_injective h

-- `temporalWindow_contains_survivor` is now proved below (after the completeness
-- helper lemmas and `temporalBadEnumList_subset_fullBadUnion`, which it depends on).

/-
Every set appearing in the temporal bad-set enumeration is one of the genuine
`badEnumList` bad sets, hence contained in the full bad union.  Needs `IsCodeFor c_U U`
(without it `snapshotDescList c_U …` may enumerate arbitrary sets).  Chain:
`temporalBadEnumList` flattens `newBadSetsAtTime ⊆ badSetsUpToTime`, whose sets come, per
level `j < n` with `m + logSlack c_gen n < h j`, from `snapshotDescList` which
(`snapshotDescriptionsAndSizeLe_subset_descriptions`) lies inside
`descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n))` — exactly the sets
`badEnumList` unions.
-/
theorem temporalBadEnumList_subset_fullBadUnion (U : Map) (c_U : Nat.Partrec.Code)
    (hc_code : IsCodeFor c_U U) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx T : ℕ)
    {d : Finset BitString} (hd : d ∈ temporalBadEnumList c_U n h m c_gen T) :
    d ⊆ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length := by
  unfold temporalBadEnumList at hd;
  obtain ⟨t, ht⟩ : ∃ t, d ∈ newBadSetsAtTime c_U n h m c_gen t ∧ t ≤ T := by
    grind;
  have h_subset : d ∈ badSetsUpToTime c_U n h m c_gen t := by
    cases t <;> simp_all +decide [ newBadSetsAtTime ];
  obtain ⟨j, hj⟩ : ∃ j, j ∈ (List.range n).filter (fun j => m + logSlack c_gen n < h j) ∧ d ∈ (snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map List.toFinset := by
    unfold badSetsUpToTime at h_subset; rw [mem_List.dedup] at h_subset; aesop;
  have h_subset : d ∈ descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)) := by
    have h_subset : d ∈ (snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map List.toFinset → d ∈ snapshotDescriptionsAndSizeLe c_U j (h j - (m + logSlack c_gen n)) t := by
      intro hd
      have := snapshotDescList_nodup_map_toFinset c_U j (h j - (m + logSlack c_gen n)) t
      simp_all +decide [ List.mem_map ];
      exact this.2 ▸ List.mem_toFinset.mpr ( List.mem_map.mpr ⟨ _, hd.choose_spec.1, hd.choose_spec.2 ⟩ );
    exact snapshotDescriptionsAndSizeLe_subset_descriptions hc_code j ( h j - ( m + logSlack c_gen n ) ) t ( h_subset hj.2 );
  have h_subset : d ∈ (badEnumList U n h m c_gen kx).toFinset := by
    unfold badEnumList; aesop;
  have h_subset : ∀ (L : List (Finset BitString)) (init : Finset BitString) (x : Finset BitString), x ∈ L → x ⊆ L.foldl (· ∪ ·) init := by
    intros L init x hx; induction L using List.reverseRecOn <;> simp_all +decide [ Finset.subset_iff ] ;
    grind;
  convert h_subset _ _ _ _;
  rw [ List.take_of_length_le ] <;> aesop

/-- The stabilized temporal window is nonempty.  Proved directly (no survivor-containment):
the survivor set `stringsOfLength n \ fullBadUnion` is nonempty (`hrem`) and disjoint from
every temporal deletion (`temporalBadEnumList_subset_fullBadUnion`), so
`GreedyWindow.fold_window_nonempty` applies. -/
theorem temporalWindow_nonempty (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i T : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    (temporalWindow c_U n h m c_gen i T).Nonempty := by
  unfold temporalWindow
  have hfirst_ne : ∀ S : Finset BitString, S.Nonempty → (firstElements S (2 ^ h i)).Nonempty := by
    intro S hS
    rw [← Finset.card_pos, firstElements_card]
    exact lt_min (Nat.one_le_pow _ _ (by decide)) (Finset.card_pos.mpr hS)
  have hdisj : ∀ d ∈ temporalBadEnumList c_U n h m c_gen T,
      Disjoint (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
        (badEnumList U n h m c_gen kx).length) (d ∩ stringsOfLength n) := by
    intro d hd
    have hsub := temporalBadEnumList_subset_fullBadUnion U c_U hc_code n h m c_gen kx (T := T) hd
    rw [Finset.disjoint_left]
    intro x hxS hxd
    exact (Finset.mem_sdiff.mp hxS).2 (hsub (Finset.mem_inter.mp hxd).1)
  exact GreedyWindow.fold_window_nonempty (stringsOfLength n)
    (fun S => firstElements S (2 ^ h i)) hfirst_ne _ hrem Finset.sdiff_subset _ hdisj

/-! ### Completeness bridge for `temporalWindow_contains_survivor`

The following helpers let us apply `temporalWindow_contains_survivor_of_append_no_refresh`
with the concrete `lexLeastSurvivor`: at a simultaneous stabilization time the temporal
enumeration covers every static bad set, so a temporal survivor is a full survivor, and
`lexLeastSurvivor` is the encoding-minimal full survivor. -/

/-
Membership in the full running bad-union is witnessed by some list element.
-/
theorem mem_badUnionUpTo_full {L : List (Finset BitString)} {x : BitString} :
    x ∈ badUnionUpTo L L.length ↔ ∃ d ∈ L, x ∈ d := by
  unfold badUnionUpTo; simp +decide [ List.foldl_eq_foldr ] ;
  induction L <;> aesop

/-
The chronological list at a later time extends the one at an earlier time.
-/
theorem temporalBadEnumList_append_of_le (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ)
    (m c_gen : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∃ L_rest, temporalBadEnumList c n h m c_gen b =
      temporalBadEnumList c n h m c_gen a ++ L_rest := by
  -- Let's denote the range up to b+1 as L_b and the range up to a+1 as L_a.
  set L_b := List.range (b + 1)
  set L_a := List.range (a + 1);
  -- By definition of `temporalBadEnumList`, we can split the list into two parts: the part up to `a` and the part from `a+1` to `b`.
  have h_split : L_b = L_a ++ (L_b.drop (a + 1)) := by
    rw [ ← List.take_append_drop ( a + 1 ) L_b, List.take_range ];
    grind;
  -- By definition of `temporalBadEnumList`, we can split the list into two parts: the part up to `a` and the part from `a+1` to `b`, and then apply the flatMap operation.
  have h_flatMap_split : List.flatMap (fun t => newBadSetsAtTime c n h m c_gen t) L_b = List.flatMap (fun t => newBadSetsAtTime c n h m c_gen t) L_a ++ List.flatMap (fun t => newBadSetsAtTime c n h m c_gen t) (L_b.drop (a + 1)) := by
    rw [ ← List.flatMap_append, ← h_split ];
  exact ⟨ _, h_flatMap_split ⟩

/-
Any set present in `badSetsUpToTime` at time `t` occurs in the chronological
enumeration up to `t`.
-/
theorem badSetsUpToTime_mem_temporal (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen : ℕ)
    {d : Finset BitString} (t : ℕ) (hd : d ∈ badSetsUpToTime c n h m c_gen t) :
    d ∈ temporalBadEnumList c n h m c_gen t := by
  induction t generalizing d with
  | zero =>
    simp_all +decide [ temporalBadEnumList ]
    unfold newBadSetsAtTime; aesop
  | succ t ih =>
    simp_all +decide [ temporalBadEnumList ]
    by_cases h : d ∈ badSetsUpToTime c n h m c_gen t
    · exact Exists.elim ( ih h ) fun a ha => ⟨ a, Nat.le_succ_of_le ha.1, ha.2 ⟩
    · use t + 1; simp [newBadSetsAtTime, h]
      assumption

/-
At a simultaneous stabilization time, every static bad set occurs in the temporal
enumeration.
-/
theorem badEnumList_mem_temporal_of_max (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (m c_gen kx t : ℕ)
    (hmax : ∀ j < n, ∀ t', countHalts c_U j t' ≤ countHalts c_U j t)
    {d : Finset BitString} (hd : d ∈ badEnumList U n h m c_gen kx) :
    d ∈ temporalBadEnumList c_U n h m c_gen t := by
  obtain ⟨j, hj, hd⟩ : ∃ j ∈ (Finset.range n).filter (fun j => m + logSlack c_gen n < h j), d ∈ descriptionsWithComplexityLeAndSizeLe U j (h j - (m + logSlack c_gen n)) := by
    unfold badEnumList at hd;
    aesop;
  have hd : d ∈ ((snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map List.toFinset).toFinset := by
    convert hd using 1;
    convert snapshotDescList_nodup_map_toFinset c_U j ( h j - ( m + logSlack c_gen n ) ) t |>.2 using 1;
    exact Eq.symm ( snapshotDescriptionsAndSizeLe_eq_descriptionsWithComplexityLeAndSizeLe hc_code j ( h j - ( m + logSlack c_gen n ) ) t ( hmax j ( Finset.mem_range.mp ( Finset.mem_filter.mp hj |>.1 ) ) ) );
  have hd : d ∈ List.dedup (((List.range n).filter (fun j => m + logSlack c_gen n < h j)).flatMap (fun j => (snapshotDescList c_U j (h j - (m + logSlack c_gen n)) t).map List.toFinset)) := by
    simp +zetaDelta at *;
    grind +suggestions;
  exact badSetsUpToTime_mem_temporal c_U n h m c_gen t hd

/-- Completeness: at a stabilization time the temporal union covers the full bad union. -/
theorem badUnion_subset_temporal_of_max (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (m c_gen kx t : ℕ)
    (hmax : ∀ j < n, ∀ t', countHalts c_U j t' ≤ countHalts c_U j t) :
    badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length ⊆
      badUnionUpTo (temporalBadEnumList c_U n h m c_gen t)
        (temporalBadEnumList c_U n h m c_gen t).length := by
  intro x hx
  rw [mem_badUnionUpTo_full] at hx ⊢
  obtain ⟨d, hd, hxd⟩ := hx
  exact ⟨d, badEnumList_mem_temporal_of_max U c_U hc_code n h m c_gen kx t hmax hd, hxd⟩

/-
Auxiliary: `lexLeastSurvivor` really is a survivor — a length-`n` string outside the
full bad-union — provided that set is nonempty.
-/
theorem lexLeastSurvivor_mem_rem (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty) :
    lexLeastSurvivor U n h m c_gen kx ∈
      stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
        (badEnumList U n h m c_gen kx).length := by
  unfold lexLeastSurvivor;
  have h_first1_nonempty : (firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length) 1).Nonempty := by
    exact Finset.card_pos.mp ( by rw [ firstElements_card ] ; exact lt_min ( by norm_num ) ( Finset.card_pos.mpr hrem ) );
  simp +zetaDelta at *;
  split_ifs <;> simp_all +decide [ Finset.Nonempty ];
  exact ⟨ Finset.mem_sdiff.mp ( firstElements_subset _ _ |> Finset.mem_of_subset <| Finset.mem_toList.mp <| List.head_mem <| by aesop ) |>.1, Finset.mem_sdiff.mp ( firstElements_subset _ _ |> Finset.mem_of_subset <| Finset.mem_toList.mp <| List.head_mem <| by aesop ) |>.2 ⟩

/-
`lexLeastSurvivor` is the encoding-minimal element of the full survivor set.
-/
theorem lexLeastSurvivor_encode_le (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty)
    {y : BitString}
    (hy : y ∈ stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length) :
    Encodable.encode (lexLeastSurvivor U n h m c_gen kx) ≤ Encodable.encode y := by
  unfold lexLeastSurvivor;
  obtain ⟨x, hx⟩ : ∃ x, x ∈ firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length) 1 ∧ x = (firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length) 1).toList.head (by
  exact List.ne_nil_of_mem ( Finset.mem_toList.mpr ( Classical.choose_spec ( Finset.card_pos.mp ( by erw [ firstElements_card ] ; exact Nat.pos_of_ne_zero ( by aesop ) ) ) ) )) := by
    all_goals generalize_proofs at *;
    exact ⟨ _, Finset.mem_toList.mp ( List.head_mem <| by solve_by_elim ), rfl ⟩
  generalize_proofs at *;
  by_cases hyx : y ∈ firstElements (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length) 1;
  · have := firstElements_card ( stringsOfLength n \ badUnionUpTo ( badEnumList U n h m c_gen kx ) ( badEnumList U n h m c_gen kx |> List.length ) ) 1; simp_all +decide ;
    rw [ Finset.card_eq_one ] at this ; aesop ( simp_config := { singlePass := true } ) ;
  · have := GreedyWindow.firstBlock_le_of_mem_of_not_mem Encodable.encode 1 (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length) x hx.1 y hy hyx; aesop;

/-- The stabilized temporal window contains the shared lex-least survivor. -/
theorem temporalWindow_contains_survivor (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i T : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length).Nonempty)
    (h_stable : ∀ t ≥ T, temporalRefreshCount c_U n h m c_gen i t = temporalRefreshCount c_U n h m c_gen i T) :
    lexLeastSurvivor U n h m c_gen kx ∈ temporalWindow c_U n h m c_gen i T := by
  obtain ⟨t₀, _hstab, hmax0⟩ := exists_simultaneous_stable_countHalts c_U n
  set T_full := max T t₀ with hTfull
  have hmaxF : ∀ j < n, ∀ t', countHalts c_U j t' ≤ countHalts c_U j T_full := by
    intro j hj t'
    exact le_trans (hmax0 j hj t') (countHalts_mono c_U j (le_max_right T t₀))
  obtain ⟨L_rest, h_append⟩ :=
    temporalBadEnumList_append_of_le c_U n h m c_gen (le_max_left T t₀)
  have h_no_refresh :
      temporalRefreshCount c_U n h m c_gen i T_full = temporalRefreshCount c_U n h m c_gen i T :=
    h_stable T_full (le_max_left T t₀)
  have hmem := lexLeastSurvivor_mem_rem U n h m c_gen kx hrem
  have h_surv : ∀ d ∈ temporalBadEnumList c_U n h m c_gen T_full,
      lexLeastSurvivor U n h m c_gen kx ∉ d := by
    intro d hd hxd
    have hsub :=
      temporalBadEnumList_subset_fullBadUnion U c_U hc_code n h m c_gen kx (T := T_full) hd
    exact (Finset.mem_sdiff.mp hmem).2 (hsub hxd)
  have h_min : ∀ y, y ∈ stringsOfLength n →
      (∀ d ∈ temporalBadEnumList c_U n h m c_gen T_full, y ∉ d) →
        Encodable.encode (lexLeastSurvivor U n h m c_gen kx) ≤ Encodable.encode y := by
    intro y hyG hy_avoid
    have hy_rem : y ∈ stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
        (badEnumList U n h m c_gen kx).length := by
      rw [Finset.mem_sdiff]
      refine ⟨hyG, fun hy_bad => ?_⟩
      have hcov := badUnion_subset_temporal_of_max U c_U hc_code n h m c_gen kx T_full hmaxF hy_bad
      rw [mem_badUnionUpTo_full] at hcov
      obtain ⟨d, hd, hyd⟩ := hcov
      exact hy_avoid d hd hyd
    exact lexLeastSurvivor_encode_le U n h m c_gen kx hrem hy_rem
  exact temporalWindow_contains_survivor_of_append_no_refresh c_U n h m c_gen i T T_full
    (lexLeastSurvivor U n h m c_gen kx) (Finset.mem_sdiff.mp hmem).1 L_rest h_append
    h_no_refresh h_surv h_min

/-- Gate C (partrec variant): set-complexity from a partial-recursive code.
If a partrec `enc` maps a code `w` to the canonical uniform-set code of `A`,
then `setComplexity U A ≤ KPPlain U w + O(1)`. -/
theorem setComplexity_le_of_partrec_code (U : Map) (hU : IsOptimalPrefixConditional U)
    (enc : BitString →. BitString) (henc : Partrec enc) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (w : BitString),
      (codedUniformOn A hA).code ∈ enc w →
      setComplexity U A hA ≤ KPPlain U w + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_partrec_map_le U hU enc henc
  refine ⟨c, fun A hA w hw => ?_⟩
  unfold setComplexity
  exact hc w ((codedUniformOn A hA).code) hw

/-- Extract `n` from the decoder input tuple. -/
def fwNat_n (s : BitString) : ℕ := decodeNatCode (decodeFirst s)

/-- Extract `i` from the decoder input tuple. -/
def fwNat_i (s : BitString) : ℕ := decodeNatCode (decodeFirst (decodeSecond s))

/-- Extract `m` from the decoder input tuple. -/
def fwNat_m (s : BitString) : ℕ := decodeNatCode (decodeFirst (decodeSecond (decodeSecond s)))

/-- Extract `c_gen` from the decoder input tuple. -/
def fwNat_c_gen (s : BitString) : ℕ := decodeNatCode (decodeFirst (decodeSecond (decodeSecond (decodeSecond s))))

/-- Extract `version` from the decoder input tuple. -/
def fwNat_version (s : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond (decodeSecond (decodeSecond (decodeSecond s)))))

/-- Extract `curve code` from the decoder input tuple. -/
def fwCurveCode (s : BitString) : BitString := decodeSecond (decodeSecond (decodeSecond (decodeSecond (decodeSecond s))))

/-- Pack the parameters used by the final-window decoder. -/
def finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) : BitString :=
  pairCode (natCode n) (pairCode (natCode i) (pairCode (natCode m)
    (pairCode (natCode c_gen) (pairCode (Nat.bits version) curve))))

@[simp] theorem fwNat_n_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNat_n (finalWindowInput n i m c_gen version curve) = n := by
  simp [finalWindowInput, fwNat_n, decodeFirst_pairCode, decodeNatCode_natCode]

@[simp] theorem fwNat_i_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNat_i (finalWindowInput n i m c_gen version curve) = i := by
  simp [finalWindowInput, fwNat_i, decodeFirst_pairCode, decodeSecond_pairCode,
    decodeNatCode_natCode]

@[simp] theorem fwNat_m_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNat_m (finalWindowInput n i m c_gen version curve) = m := by
  simp [finalWindowInput, fwNat_m, decodeFirst_pairCode, decodeSecond_pairCode,
    decodeNatCode_natCode]

@[simp] theorem fwNat_c_gen_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNat_c_gen (finalWindowInput n i m c_gen version curve) = c_gen := by
  simp [finalWindowInput, fwNat_c_gen, decodeFirst_pairCode, decodeSecond_pairCode,
    decodeNatCode_natCode]

@[simp] theorem fwNat_version_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNat_version (finalWindowInput n i m c_gen version curve) = version := by
  simp [finalWindowInput, fwNat_version, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

@[simp] theorem fwCurveCode_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwCurveCode (finalWindowInput n i m c_gen version curve) = curve := by
  simp [finalWindowInput, fwCurveCode, decodeSecond_pairCode]

/-- Named decoder shape: rfind the first time `P s t` holds, then emit the canonical
uniform code of the held window `W s t` (or diverge if empty).  Naming this (rather than
inlining the `dite`) lets `finalWindowFn` be *definitionally* `codedWindowDecoder _ _`, so
matching `finalWindowFn` against the skeleton lemma is a delta step on `codedWindowDecoder`
and never exposes the heavy `temporalWindow` `Decidable`-nonempty instance to `whnf`. -/
noncomputable def codedWindowDecoder {α : Type} [Primcodable α]
    (P : α → ℕ → Bool) (W : α → ℕ → Finset BitString) : α →. BitString := fun s =>
  (Nat.rfind (fun t => Part.some (P s t))).bind
    (fun t => if hne : (W s t).Nonempty then Part.some (codedUniformOn (W s t) hne).code
      else Part.none)

/-- G2: The machine-model decoder function for the held temporal window. -/
noncomputable def finalWindowFn (c : Nat.Partrec.Code) : BitString →. BitString :=
  codedWindowDecoder
    (fun s t => decide (temporalRefreshCount c (fwNat_n s) (decodeCurve (fwCurveCode s))
      (fwNat_m s) (fwNat_c_gen s) (fwNat_i s) t = fwNat_version s))
    (fun s t => temporalWindow c (fwNat_n s) (decodeCurve (fwCurveCode s))
      (fwNat_m s) (fwNat_c_gen s) (fwNat_i s) t)

theorem badSetsUpToTime_congr (c : Nat.Partrec.Code) (n m c_gen t : ℕ) {h1 h2 : ℕ → ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j) :
    badSetsUpToTime c n h1 m c_gen t = badSetsUpToTime c n h2 m c_gen t := by
  unfold badSetsUpToTime
  congr 1
  have filter_eq : (List.range n).filter (fun j => m + logSlack c_gen n < h1 j) = (List.range n).filter (fun j => m + logSlack c_gen n < h2 j) := by
    have h_congr : ∀ l : List ℕ, (∀ j ∈ l, j < n) → l.filter (fun j => m + logSlack c_gen n < h1 j) = l.filter (fun j => m + logSlack c_gen n < h2 j) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a l ih =>
        intro hl
        have hl_a : a < n := hl a (by simp)
        have hl_l : ∀ j ∈ l, j < n := fun j hj => hl j (by simp [hj])
        have ih_l := ih hl_l
        simp only [List.filter_cons]
        have heq_a : (m + logSlack c_gen n < h1 a) ↔ (m + logSlack c_gen n < h2 a) := heq a hl_a
        have dec_eq : decide (m + logSlack c_gen n < h1 a) = decide (m + logSlack c_gen n < h2 a) := decide_eq_decide.mpr heq_a
        rw [dec_eq, ih_l]
    apply h_congr
    intro j hj
    exact List.mem_range.mp hj
  rw [filter_eq]
  apply List.flatMap_congr_loc
  intro j hj
  rw [List.mem_filter, List.mem_range] at hj
  have hj_h2 : m + logSlack c_gen n < h2 j := of_decide_eq_true hj.2
  have hj_h1 : m + logSlack c_gen n < h1 j := (heq j hj.1).mpr hj_h2
  have h_eq : h1 j = h2 j := heq2 j hj.1 hj_h1
  rw [h_eq]

theorem newBadSetsAtTime_congr (c : Nat.Partrec.Code) (n m c_gen t : ℕ) {h1 h2 : ℕ → ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j) :
    newBadSetsAtTime c n h1 m c_gen t = newBadSetsAtTime c n h2 m c_gen t := by
  unfold newBadSetsAtTime
  cases t
  · exact badSetsUpToTime_congr c n m c_gen 0 heq heq2
  · simp only
    rw [badSetsUpToTime_congr c n m c_gen _ heq heq2, badSetsUpToTime_congr c n m c_gen _ heq heq2]

theorem temporalBadEnumList_congr (c : Nat.Partrec.Code) (n m c_gen t_max : ℕ) {h1 h2 : ℕ → ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j) :
    temporalBadEnumList c n h1 m c_gen t_max = temporalBadEnumList c n h2 m c_gen t_max := by
  unfold temporalBadEnumList
  apply List.flatMap_congr_loc
  intro t _
  exact newBadSetsAtTime_congr c n m c_gen t heq heq2

/-- Congruence for temporal refresh count over the curve function. -/
theorem temporalRefreshCount_congr (c : Nat.Partrec.Code) (n m c_gen i t : ℕ) {h1 h2 : ℕ → ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j)
    (heqi : h1 i = h2 i) :
    temporalRefreshCount c n h1 m c_gen i t = temporalRefreshCount c n h2 m c_gen i t := by
  unfold temporalRefreshCount
  rw [heqi]
  rw [temporalBadEnumList_congr c n m c_gen t heq heq2]

/-- Congruence for temporal window over the curve function. -/
theorem temporalWindow_congr (c : Nat.Partrec.Code) (n m c_gen i t : ℕ) {h1 h2 : ℕ → ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j)
    (heqi : h1 i = h2 i) :
    temporalWindow c n h1 m c_gen i t = temporalWindow c n h2 m c_gen i t := by
  unfold temporalWindow
  rw [heqi]
  rw [temporalBadEnumList_congr c n m c_gen t heq heq2]

/-- Computable list mirror of `badSetsUpToTime`. -/
def badSetsUpToTimeList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen : ℕ) (t : ℕ) : List (List BitString) :=
  List.dedup (((List.range n).filter (fun j => decide (m + logSlack c_gen n < decodeCurve curve j))).flatMap (fun j =>
    snapshotDescList c j (decodeCurve curve j - (m + logSlack c_gen n)) t))

/-- Computable list mirror of `newBadSetsAtTime`. -/
def newBadSetsAtTimeList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen : ℕ) (t : ℕ) : List (List BitString) :=
  let all_at_t := badSetsUpToTimeList c n curve m c_gen t
  match t with
  | 0 => all_at_t
  | t_minus_1 + 1 =>
    let all_at_t_minus_1 := badSetsUpToTimeList c n curve m c_gen t_minus_1
    all_at_t.filter (fun S => ! (all_at_t_minus_1.elem S))

/-- Computable list mirror of `temporalBadEnumList`. -/
def temporalBadEnumListList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen : ℕ) (t_max : ℕ) : List (List BitString) :=
  (List.range (t_max + 1)).flatMap (fun t => newBadSetsAtTimeList c n curve m c_gen t)

/-- Computable list mirror of `GreedyWindow.step`. -/
def greedyWindowStepList (G : List BitString) (size : ℕ) (st : List BitString × List BitString × ℕ) (d : List BitString) : List BitString × List BitString × ℕ :=
  let deleted := List.dedup (st.1 ++ (d.filter (fun x => G.elem x)))
  if st.2.1.all (fun x => deleted.elem x) then
    let new_window_full := G.filter (fun x => ! (deleted.elem x))
    (deleted, new_window_full.take size, st.2.2 + 1)
  else
    (deleted, st.2.1, st.2.2)

/-- Computable list mirror of `GreedyWindow.fold`. -/
def greedyWindowFoldList (G : List BitString) (size : ℕ) (L : List (List BitString)) : List BitString × List BitString × ℕ :=
  L.foldl (greedyWindowStepList G size) ([], G.take size, 0)

/-- Computable list mirror of `temporalRefreshCount`. -/
def temporalRefreshCountList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen i t : ℕ) : ℕ :=
  let G := canonicalFinsetList (allStrings n).toFinset
  greedyWindowFoldList G (2 ^ (decodeCurve curve i)) (temporalBadEnumListList c n curve m c_gen t) |>.2.2

/-- Computable list mirror of `temporalWindow`. -/
def temporalWindowList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen i t : ℕ) : List BitString :=
  let G := canonicalFinsetList (allStrings n).toFinset
  greedyWindowFoldList G (2 ^ (decodeCurve curve i)) (temporalBadEnumListList c n curve m c_gen t) |>.2.1

/-
List↔Finset correspondence chain.  These discharge the `*_eq` lemmas that bridge
the computable list mirrors (`badSetsUpToTimeList`, `greedyWindowFoldList`, …)
with their abstract `Finset`-valued counterparts.
-/

/-- Injective image commutes with `List.dedup`. -/
theorem dedup_map_injOn {α β} [DecidableEq α] [DecidableEq β] (f : α → β) (l : List α)
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    List.map f (List.dedup l) = List.dedup (List.map f l) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hft : ∀ x ∈ t, ∀ y ∈ t, f x = f y → x = y :=
      fun x hx y hy => hf x (by simp [hx]) y (by simp [hy])
    have iht := ih hft
    have hmemA : a ∈ List.dedup t ↔ a ∈ t := mem_List.dedup t a
    have hmemB : f a ∈ List.dedup (List.map f t) ↔ f a ∈ List.map f t :=
      mem_List.dedup (List.map f t) (f a)
    change List.map f (if a ∈ List.dedup t then List.dedup t else a :: List.dedup t)
      = (if f a ∈ List.dedup (List.map f t) then List.dedup (List.map f t)
          else f a :: List.dedup (List.map f t))
    by_cases h : a ∈ t
    · rw [if_pos (hmemA.mpr h), if_pos (hmemB.mpr (List.mem_map_of_mem h)), iht]
    · have hfa : f a ∉ List.dedup (List.map f t) := by
        intro hd
        rw [hmemB, List.mem_map] at hd
        obtain ⟨x, hx, hfx⟩ := hd
        exact h (hf x (by simp [hx]) a (by simp) hfx ▸ hx)
      rw [if_neg (fun hd => h (hmemA.mp hd)), if_neg hfa, List.map_cons, iht]

/-- Every description list produced by `snapshotDescList` is in canonical form,
i.e. it is a fixed point of `canonicalFinsetList ∘ List.toFinset`.  This is the
injectivity input needed to swap `List.dedup` past `List.toFinset`. -/
theorem snapshotDescList_canonical (c : Nat.Partrec.Code) (i j t : ℕ) :
    ∀ x ∈ snapshotDescList c i j t, canonicalFinsetList x.toFinset = x := by
  intro x hx
  unfold snapshotDescList at hx
  rw [List.mem_filter] at hx
  rw [List.mem_map] at hx
  obtain ⟨⟨w, _, rfl⟩, _⟩ := hx
  rw [canonicalFinsetList_toFinset]

theorem badSetsUpToTimeList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen : ℕ) (t : ℕ) :
    (badSetsUpToTimeList c n curve m c_gen t).map List.toFinset = badSetsUpToTime c n (decodeCurve curve) m c_gen t := by
  unfold badSetsUpToTimeList badSetsUpToTime
  rw [← List.map_flatMap]
  have hinj : ∀ a ∈ List.flatMap
      (fun j => snapshotDescList c j (decodeCurve curve j - (m + logSlack c_gen n)) t)
      (List.filter (fun j => decide (m + logSlack c_gen n < decodeCurve curve j)) (List.range n)),
      ∀ b ∈ List.flatMap
      (fun j => snapshotDescList c j (decodeCurve curve j - (m + logSlack c_gen n)) t)
      (List.filter (fun j => decide (m + logSlack c_gen n < decodeCurve curve j)) (List.range n)),
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
theorem map_filter_congr {α β} (f : α → β) (p : α → Bool) (q : β → Bool) (l : List α)
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

theorem newBadSetsAtTimeList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen : ℕ) (t : ℕ) :
    (newBadSetsAtTimeList c n curve m c_gen t).map List.toFinset = newBadSetsAtTime c n (decodeCurve curve) m c_gen t := by
  cases t with
  | zero =>
    exact badSetsUpToTimeList_eq c n curve m c_gen 0
  | succ k =>
    unfold newBadSetsAtTimeList newBadSetsAtTime
    simp only
    rw [map_filter_congr (q := fun S => decide (S ∉ badSetsUpToTime c n (decodeCurve curve) m c_gen k)),
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

theorem temporalBadEnumListList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen : ℕ) (t_max : ℕ) :
    (temporalBadEnumListList c n curve m c_gen t_max).map List.toFinset = temporalBadEnumList c n (decodeCurve curve) m c_gen t_max := by
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
  have hpairG : (canonicalFinsetList G).Pairwise bitStringLE := Finset.pairwise_sort G bitStringLE
  have hpair : ((canonicalFinsetList G).filter p).Pairwise bitStringLE :=
    List.Pairwise.filter p hpairG
  have htf : ((canonicalFinsetList G).filter p).toFinset = G.filter (fun x => p x) := by
    rw [List.toFinset_filter, canonicalFinsetList_toFinset]
  have hcanon := canonicalFinsetList_of_sorted _ hnd hpair
  rw [htf] at hcanon
  exact hcanon.symm

/-- A prefix of the canonical enumeration is its own canonical enumeration. -/
theorem canonical_prefix (S : Finset BitString) (k : ℕ) :
    canonicalFinsetList (((canonicalFinsetList S).take k).toFinset) = (canonicalFinsetList S).take k := by
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
      stl'.1.toFinset = stf'.1 ∧ stl'.2.1 = canonicalFinsetList stf'.2.1 ∧ stl'.2.2 = stf'.2.2 := by
  intro L
  induction L with
  | nil =>
    intro dl wl cl df wf cf h1 h2 h3
    exact ⟨h1, h2, h3⟩
  | cons d rest ih =>
    intro dl wl cl df wf cf h1 h2 h3
    -- new deleted set (list side) and its `toFinset`.
    have hdel : (List.dedup (dl ++ (d.filter (fun x => (canonicalFinsetList G).elem x)))).toFinset
        = df ∪ (d.toFinset ∩ G) := by
      ext x
      simp only [List.mem_toFinset, mem_List.dedup, List.mem_append, List.mem_filter,
        List.elem_eq_mem, decide_eq_true_eq, Finset.mem_union, Finset.mem_inter,
        mem_canonicalFinsetList, ← h1]
    -- the emptiness test agrees on both sides.
    have htest : (wl.all (fun x => (List.dedup (dl ++ (d.filter (fun x => (canonicalFinsetList G).elem x)))).elem x) = true)
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
    · rw [if_pos (htest.mpr hb), if_pos hb]
      apply ih
      · exact hdel
      · exact refresh_window_eq G size _ _ hdel
      · rw [h3]
    · rw [if_neg (fun hc => hb (htest.mp hc)), if_neg hb]
      apply ih
      · exact hdel
      · exact h2
      · exact h3

theorem greedyWindowFoldList_eq (G : Finset BitString) (size : ℕ) (L : List (List BitString)) :
    let st' := greedyWindowFoldList (canonicalFinsetList G) size L
    (st'.1.toFinset, st'.2.1.toFinset, st'.2.2) = GreedyWindow.fold G (fun S => firstElements S size) (L.map List.toFinset) := by
  have hinit_w : (canonicalFinsetList G).take size = canonicalFinsetList (firstElements G size) := by
    rw [firstElements_eq_take, canonical_prefix]
  obtain ⟨e1, e2, e3⟩ := greedy_fold_correspondence G size L [] ((canonicalFinsetList G).take size) 0
    ∅ (firstElements G size) 0 (by simp) hinit_w rfl
  simp only [greedyWindowFoldList, GreedyWindow.fold]
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨e1, ?_, e3⟩
  rw [e2, canonicalFinsetList_toFinset]

/-- The list-side window is the canonical enumeration of the abstract window. -/
theorem greedyWindowFoldList_window_canonical (G : Finset BitString) (size : ℕ) (L : List (List BitString)) :
    (greedyWindowFoldList (canonicalFinsetList G) size L).2.1
      = canonicalFinsetList (GreedyWindow.fold G (fun S => firstElements S size) (L.map List.toFinset)).2.1 := by
  have hinit_w : (canonicalFinsetList G).take size = canonicalFinsetList (firstElements G size) := by
    rw [firstElements_eq_take, canonical_prefix]
  obtain ⟨_, e2, _⟩ := greedy_fold_correspondence G size L [] ((canonicalFinsetList G).take size) 0
    ∅ (firstElements G size) 0 (by simp) hinit_w rfl
  simpa only [greedyWindowFoldList, GreedyWindow.fold] using e2

theorem temporalRefreshCountList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen i t : ℕ) :
    temporalRefreshCountList c n curve m c_gen i t = temporalRefreshCount c n (decodeCurve curve) m c_gen i t := by
  unfold temporalRefreshCountList temporalRefreshCount
  have h := greedyWindowFoldList_eq ((allStrings n).toFinset) (2 ^ decodeCurve curve i)
    (temporalBadEnumListList c n curve m c_gen t)
  have h2 := congrArg (fun p : Finset BitString × Finset BitString × ℕ => p.2.2) h
  simp only at h2
  rw [h2, temporalBadEnumListList_eq]
  rfl

/-
Computability plumbing for the list-mirror layer.  This entire layer is now fully
proved (no placeholders remain in it); the `*_eq` correspondence chain and the
`c`-independent fold lemmas `greedyWindowStepList_computable` /
`greedyWindowFoldList_computable` above are also complete.

The development proceeds through:
* `snapshotDescList_primrec` (DescriptionSnapshot.lean:234), which gives the hard
  `c`-parameterized enumeration as `Primrec`.
* the general primitive-recursion helpers `natPow_primrec`, `natSize_primrec`,
  `logSlack_primrec`, `decodeCurve_primrec`, `list_mem_decide_primrec` and
  `list_dedup_gen_primrec` proved just below.
* `badSetsUpToTimeList_primrec` = `List.dedup` of a `flatMap`/`filter` over
  `List.range n` whose predicate uses `decodeCurve` and `logSlack`, then
  `newBadSetsAtTimeList_primrec` / `temporalBadEnumListList_primrec` by
  `filter`/`flatMap` composition, and finally `temporalRefreshCountList_computable`
  / `temporalWindowList_computable` by composing `greedyWindowFoldList_computable`
  with `canonicalFinsetList`/`decodeCurve` computability.

Natural-number exponentiation is primitive recursive in both arguments.
-/
theorem natPow_primrec : Primrec₂ (fun a b : ℕ => a ^ b) := by
  refine Primrec.nat_iff.2 ?_;
  convert Nat.Primrec.pow using 1

/-
`Nat.size` (the binary length) is primitive recursive.  Uses the closed form
`Nat.size n = #{k ∈ range (n+1) | 2^k ≤ n}`.
-/
theorem natSize_primrec : Primrec (fun n => Nat.size n) := by
  -- The function `Nat.size` is primitive recursive because it can be expressed using the `Nat.rec` function.
  have h_size_primrec : Primrec (fun n : ℕ => (List.range (n + 1)).filter (fun k => decide (2 ^ k ≤ n)) |>.length) := by
    convert Primrec.comp ( Primrec.list_length ) ( list_filter_primrec ( Primrec.comp ( Primrec.list_range ) ( Primrec.succ ) ) _ ) using 1;
    convert Primrec.nat_le.comp ( natPow_primrec.comp ( Primrec.const 2 ) ( Primrec.snd ) ) ( Primrec.fst ) using 1;
    constructor <;> intro h <;> simp_all +decide [ Primrec₂, PrimrecPred ];
    · exact ⟨ inferInstance, h ⟩;
    · grind
  generalize_proofs at *; (
  convert h_size_primrec using 1;
  ext n; rw [ show ( List.filter ( fun k => decide ( 2 ^ k ≤ n ) ) ( List.range ( n + 1 ) ) ) = List.range ( Nat.size n ) from ?_ ] ; simp +decide ;
  have h_filter : ∀ k ∈ List.range (n + 1), 2 ^ k ≤ n ↔ k < Nat.size n := by
    simp +decide [ Nat.lt_size ]
  generalize_proofs at *; (
  have h_filter_eq : List.filter (fun k => k < Nat.size n) (List.range (n + 1)) = List.range (Nat.size n) := by
    have h_filter_eq : ∀ m n : ℕ, m ≤ n → List.filter (fun k => k < m) (List.range n) = List.range m := by
      intros m n hmn; induction hmn <;> simp_all +decide [ List.range_succ ] ;
    generalize_proofs at *; (
    apply h_filter_eq; exact Nat.size_le.mpr (by
    exact Nat.recOn n ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at ihn ⊢ ; linarith;))
  generalize_proofs at *; (
  rw [ ← h_filter_eq, List.filter_congr ] ; aesop ( simp_config := { singlePass := true } ) ;)))

/-
`logSlack` is primitive recursive in both arguments.  Recall
`logSlack c n = c * (Nat.bits n).length + c = c * Nat.size n + c`.
-/
theorem logSlack_primrec : Primrec₂ (fun c n : ℕ => logSlack c n) := by
  unfold logSlack;
  convert Primrec.nat_add.comp ( Primrec.nat_mul.comp ( Primrec.fst ) ( natSize_primrec.comp ( Primrec.snd ) ) ) ( Primrec.fst ) using 1;
  simp +decide [ Primrec₂, Nat.size_eq_bits_len ]

/-
`decodeCurve` is primitive recursive in the code bitstring and the index.
-/
theorem decodeCurve_primrec : Primrec₂ (fun (code : BitString) (i : ℕ) => decodeCurve code i) := by
  have h_splitOnP : ∀ (code : BitString),
      (List.splitOnP (fun x : Bool => !x) code).map List.length =
        code.foldr (fun b acc => if b then ((acc.headI + 1) :: acc.tail) else 0 :: acc) [0] := by
    intro code
    induction code with
    | nil => simp [List.splitOnP_nil]
    | cons b code ih =>
      cases b
      · simp only [List.splitOnP_cons, Bool.not_false, ↓reduceIte, List.map_cons, List.length_nil]
        exact congrArg (fun xs => 0 :: xs) ih
      · simp only [List.splitOnP_cons, Bool.not_true]
        cases hs : List.splitOnP (fun x : Bool => !x) code with
        | nil => exact (List.splitOnP_ne_nil (fun x : Bool => !x) code hs).elim
        | cons head tail =>
          have ih' := ih
          rw [hs] at ih'
          simp only [List.foldr_cons]
          rw [← ih']
          simp [List.modifyHead]
  have h_splitOn : ∀ (code : BitString),
      (code.splitOn false).map List.length =
        code.foldr (fun b acc => if b then ((acc.headI + 1) :: acc.tail) else 0 :: acc) [0] := by
    intro code
    simpa [List.splitOn] using h_splitOnP code
  convert Primrec₂.of_eq _ _;
  exact fun code i => (code.foldr (fun b acc => if b then ((acc.headI + 1) :: acc.tail) else 0 :: acc) [0]).getD i 0;
  · refine Primrec₂.of_eq (f := fun code i => ( List.foldr ( fun b acc => if b = true then ( acc.headI + 1 ) :: acc.tail else 0 :: acc ) [ 0 ] code ).getD i 0) ?_ ?_
    · have h_foldr : Primrec (fun (p : BitString × ℕ) => (List.foldr (fun b acc => if b = true then (acc.headI + 1) :: acc.tail else 0 :: acc) [0] p.1).getD p.2 0) := by
        have h_foldr : Primrec (fun (p : BitString × List ℕ) => (List.foldr (fun b acc => if b = true then (acc.headI + 1) :: acc.tail else 0 :: acc) p.2 p.1)) := by
          convert Primrec.list_foldr _ _ _;
          rotate_left;
          exact inferInstance;
          exact fun p q => if q.1 then ( q.2.headI + 1 ) :: q.2.tail else 0 :: q.2;
          · exact Primrec.fst;
          · exact Primrec.snd;
          · convert Primrec.ite _ _ _ using 1;
            · exact Primrec.eq.comp ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.const true );
            · convert Primrec.list_cons.comp ( Primrec.nat_add.comp ( Primrec.list_headI.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) ( Primrec.const 1 ) ) ( Primrec.list_tail.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) using 1;
            · exact Primrec.list_cons.comp ( Primrec.const 0 ) ( Primrec.snd.comp ( Primrec.snd ) );
          · rfl
        have h_getD : Primrec (fun (p : List ℕ × ℕ) => p.1.getD p.2 0) := by
          convert Primrec.option_getD.comp ( Primrec.list_getElem? ) ( Primrec.const 0 ) using 1;
        convert h_getD.comp ( h_foldr.comp ( Primrec.fst.pair ( Primrec.const [ 0 ] ) ) |> Primrec.pair <| Primrec.snd ) using 1;
      exact h_foldr;
    · exact fun _ _ => rfl;
  · unfold decodeCurve; aesop;

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
      by_cases h : x = a <;> simp [h, eq_comm]
      · exact fun heq => absurd heq.symm h
  have hcond : PrimrecPred (fun a : (α × List α) × (α × Bool) => a.2.1 = a.1.1) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)
  have hstep : Primrec₂ (fun (p : α × List α) (q : α × Bool) => if q.1 = p.1 then true else q.2) :=
    Primrec.ite hcond (Primrec.const true) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.snd (Primrec.const false) hstep).of_eq (fun p => (key p.1 p.2).symm)

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
  have hstep : Primrec₂ (fun (_ : List α) (q : α × List α) => if q.1 ∈ q.2 then q.2 else q.1 :: q.2) := by
    have := Primrec.cond hbool (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    exact this.of_eq (fun p => by cases h : decide (p.2.1 ∈ p.2.2) <;> simp_all)
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq (fun l => (key l).symm)

/-- Primitive-recursive version of `badSetsUpToTimeList_computable`. -/
theorem badSetsUpToTimeList_primrec (c : Nat.Partrec.Code) :
    Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => badSetsUpToTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  have h_filter : Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => List.filter (fun j => p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1 < decodeCurve p.1.2.1 j) (List.range p.1.1)) := by
    apply list_filter_primrec;
    · exact Primrec.list_range.comp ( Primrec.fst.comp ( Primrec.fst ) );
    · have h_pred : Primrec (fun (p : (ℕ × BitString × ℕ × ℕ) × ℕ) => p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1) ∧ Primrec (fun (p : (ℕ × BitString × ℕ × ℕ) × ℕ) => decodeCurve p.1.2.1 p.2) := by
        constructor;
        · have h_logSlack_primrec : Primrec₂ (fun (c n : ℕ) => logSlack c n) := by
            exact logSlack_primrec;
          exact Primrec.nat_add.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp Primrec.fst ) ) ) ( h_logSlack_primrec.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp Primrec.fst ) ) ) ( Primrec.fst.comp Primrec.fst ) );
        · exact decodeCurve_primrec.comp ( Primrec.fst.comp ( Primrec.snd.comp Primrec.fst ) ) ( Primrec.snd );
      have h_pred : Primrec (fun (p : (ℕ × BitString × ℕ × ℕ) × ℕ) => decide (p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1 < decodeCurve p.1.2.1 p.2)) := by
        have h_pred : Primrec (fun (p : ℕ × ℕ) => decide (p.1 < p.2)) := by
          convert Primrec.nat_lt using 1;
          constructor <;> intro h <;> simp_all +decide [ PrimrecRel ];
          · convert h using 1;
            constructor <;> intro h <;> rw [ PrimrecPred ] at * <;> aesop;
          · convert h using 1;
            constructor <;> intro h <;> simp_all +decide [ PrimrecPred ];
            grind +revert;
        convert h_pred.comp ( Primrec.pair ( ‹ ( Primrec fun p : ( ℕ × BitString × ℕ × ℕ ) × ℕ => p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1 ) ∧ Primrec fun p : ( ℕ × BitString × ℕ × ℕ ) × ℕ => decodeCurve p.1.2.1 p.2 ›.1 ) ( ‹ ( Primrec fun p : ( ℕ × BitString × ℕ × ℕ ) × ℕ => p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1 ) ∧ Primrec fun p : ( ℕ × BitString × ℕ × ℕ ) × ℕ => decodeCurve p.1.2.1 p.2 ›.2 ) ) using 1;
      convert h_pred.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) using 1;
  have h_flatMap : Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => List.flatMap (fun j => snapshotDescList c j (decodeCurve p.1.2.1 j - (p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1)) p.2) (List.filter (fun j => p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1 < decodeCurve p.1.2.1 j) (List.range p.1.1))) := by
    have h_flatMap : Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ × ℕ => snapshotDescList c p.2.2 (decodeCurve p.1.2.1 p.2.2 - (p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1)) p.2.1) := by
      have h_flatMap : Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ × ℕ => ((p.2.2, p.2.1), decodeCurve p.1.2.1 p.2.2 - (p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1))) := by
        apply Primrec.pair;
        · exact Primrec.pair ( Primrec.snd.comp ( Primrec.snd ) ) ( Primrec.fst.comp ( Primrec.snd ) );
        · have h_flatMap : Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => decodeCurve p.1.2.1 p.2) := by
            exact decodeCurve_primrec.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ( Primrec.snd );
          have h_flatMap : Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => p.1.2.2.1 + logSlack p.1.2.2.2 p.1.1) := by
            convert Primrec.nat_add.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) ( logSlack_primrec.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) ( Primrec.fst.comp ( Primrec.fst ) ) ) using 1;
          convert Primrec.nat_sub.comp ( ‹Primrec fun p : ( ℕ × BitString × ℕ × ℕ ) × ℕ => decodeCurve p.1.2.1 p.2›.comp ( Primrec.fst.comp Primrec.id |> Primrec.pair <| Primrec.snd.comp <| Primrec.snd.comp Primrec.id ) ) ( h_flatMap.comp ( Primrec.fst.comp Primrec.id |> Primrec.pair <| Primrec.snd.comp <| Primrec.snd.comp Primrec.id ) ) using 1;
      convert snapshotDescList_primrec c |> Primrec.comp <| h_flatMap using 1;
    convert Primrec.list_flatMap _ _ using 1;
    all_goals try infer_instance;
    · exact h_filter;
    · convert h_flatMap.comp ( show Primrec ( fun p : ( ( ℕ × BitString × ℕ × ℕ ) × ℕ ) × ℕ => ( p.1.1, p.1.2, p.2 ) ) from ?_ ) using 1;
      exact Primrec.pair ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.pair ( Primrec.snd.comp ( Primrec.fst ) ) ( Primrec.snd ) );
  convert list_dedup_gen_primrec.comp h_flatMap using 1

theorem badSetsUpToTimeList_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => badSetsUpToTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) :=
  (badSetsUpToTimeList_primrec c).to_comp

/-
Primitive-recursive version of `newBadSetsAtTimeList_computable`.
-/
theorem newBadSetsAtTimeList_primrec (c : Nat.Partrec.Code) :
    Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => newBadSetsAtTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  -- The function `newBadSetsAtTimeList` is a conditional function that depends on `t`. We can use the `Primrec.ite` constructor to handle the condition.
  have h_cond : Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => if p.2 = 0 then badSetsUpToTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 0 else (badSetsUpToTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2).filter (fun S => ! (badSetsUpToTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 (p.2 - 1)).elem S)) := by
    refine Primrec.ite ?_ ?_ ?_;
    · exact Primrec.eq.comp ( Primrec.snd ) ( Primrec.const 0 );
    · convert badSetsUpToTimeList_primrec c |> Primrec.comp <| _ using 1;
      rotate_left;
      exact fun p => ( p.1, 0 );
      · exact Primrec.pair ( Primrec.fst ) ( Primrec.const 0 );
      · rfl;
    · have h_filter : Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => badSetsUpToTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
        convert badSetsUpToTimeList_primrec c using 1;
      have h_filter : Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => badSetsUpToTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 (p.2 - 1)) := by
        convert h_filter.comp ( Primrec.fst.comp ( Primrec.id ) |> Primrec.pair <| Primrec.nat_sub.comp ( Primrec.snd.comp ( Primrec.id ) ) ( Primrec.const 1 ) ) using 1;
      convert list_filter_primrec _ _ using 1;
      · assumption;
      · convert Primrec.not.comp _ using 1;
        convert list_mem_decide_primrec.comp ( Primrec.snd ) ( h_filter.comp ( Primrec.fst ) ) using 1;
        grind +revert;
  convert h_cond using 1;
  funext p; cases p.2 <;> simp +decide [ newBadSetsAtTimeList ] ;

theorem newBadSetsAtTimeList_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => newBadSetsAtTimeList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) :=
  (newBadSetsAtTimeList_primrec c).to_comp

/-
Primitive-recursive version of `temporalBadEnumListList_computable`.
-/
theorem temporalBadEnumListList_primrec (c : Nat.Partrec.Code) :
    Primrec (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => temporalBadEnumListList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  have := @newBadSetsAtTimeList_primrec;
  specialize this c;
  convert Primrec.list_flatMap _ _;
  all_goals try infer_instance;
  · convert Primrec.comp ( Primrec.list_range ) ( Primrec.succ.comp ( Primrec.snd ) ) using 1;
  · exact this.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.snd ) |> Primrec.comp <| Primrec.id

theorem temporalBadEnumListList_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ) × ℕ => temporalBadEnumListList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) :=
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

/-- `List.take` is primitive recursive in the list and the length. -/
theorem list_take_primrec {α} [Primcodable α] :
    Primrec₂ (fun (l : List α) (n : ℕ) => l.take n) := by
  have h : Primrec₂ (fun (l : List α) (n : ℕ) => (List.range n).filterMap (fun i => l[i]?)) :=
    Primrec.listFilterMap (Primrec.list_range.comp Primrec.snd)
      (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact h.of_eq (fun l n => (take_eq_filterMap l n).symm)

/-- `List.all` is primitive recursive (dual of `list_any_primrec`). -/
theorem list_all_primrec {α β} [Primcodable α] [Primcodable β] {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec (fun a => (f a).all (p a)) := by
  have heq : (fun a => (f a).all (p a))
      = (fun a => (f a).foldr (fun b acc => p a b && acc) true) := by
    funext a; induction f a with
    | nil => rfl
    | cons b t ih => simp [List.all_cons, ih]
  rw [heq]
  have hstep : Primrec₂ (fun (a : α) (q : β × Bool) => p a q.1 && q.2) :=
    ((Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd) (Primrec.const false)).to₂).of_eq
      (fun a q => by cases p a q.1 <;> simp)
  exact Primrec.list_foldr hf (Primrec.const true) hstep

/-- The project-local `List.dedup` agrees with Mathlib's `_root_.List.dedup`. -/
theorem list_dedup_eq_root (l : List BitString) : List.dedup l = _root_.List.dedup l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    unfold List.dedup
    rw [ih]
    by_cases h : a ∈ t
    · rw [if_pos (List.mem_dedup.mpr h), _root_.List.dedup_cons_of_mem h]
    · rw [if_neg (fun hc => h (List.mem_dedup.mp hc)), _root_.List.dedup_cons_of_notMem h]

/-- The project-local `List.dedup` is primitive recursive. -/
theorem local_dedup_primrec : Primrec (fun l : List BitString => List.dedup l) :=
  dedup_primrec.of_eq (fun l => (list_dedup_eq_root l).symm)

theorem greedyWindowStepList_primrec :
    Primrec (fun p : (List BitString × ℕ) × (List BitString × List BitString × ℕ) × List BitString =>
      greedyWindowStepList p.1.1 p.1.2 p.2.1 p.2.2) := by
  set P := (List BitString × ℕ) × (List BitString × List BitString × ℕ) × List BitString with hP
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
        ! decide (x ∈ List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1)))))).take p.1.2) :=
    list_take_primrec.comp (list_filter_primrec hG (Primrec.not.comp hmemdel)) hsize
  -- assemble
  have hthen : Primrec (fun p : P =>
      (List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1))),
        ((p.1.1).filter (fun x =>
          ! decide (x ∈ List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1)))))).take p.1.2,
        p.2.1.2.2 + 1)) :=
    Primrec.pair hdel (Primrec.pair hnewwin (Primrec.succ.comp hst22))
  have helse : Primrec (fun p : P =>
      (List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1))),
        p.2.1.2.1, p.2.1.2.2)) :=
    Primrec.pair hdel (Primrec.pair hst21 hst22)
  have hcond : PrimrecPred (fun p : P =>
      (p.2.1.2.1.all (fun x =>
        decide (x ∈ List.dedup (p.2.1.1 ++ p.2.2.filter (fun x => decide (x ∈ p.1.1)))))) = true) :=
    Primrec.eq.comp htest (Primrec.const true)
  refine (Primrec.ite hcond hthen helse).of_eq (fun p => ?_)
  simp only [greedyWindowStepList, List.elem_eq_mem]

theorem greedyWindowStepList_computable :
    Computable (fun p : (List BitString × ℕ) × (List BitString × List BitString × ℕ) × List BitString =>
      greedyWindowStepList p.1.1 p.1.2 p.2.1 p.2.2) :=
  greedyWindowStepList_primrec.to_comp

theorem greedyWindowFoldList_computable :
    Computable (fun p : (List BitString × ℕ) × List (List BitString) =>
      greedyWindowFoldList p.1.1 p.1.2 p.2) := by
  apply Primrec.to_comp
  set Q := (List BitString × ℕ) × List (List BitString) with hQ
  have hf : Primrec (fun p : Q => p.2) := Primrec.snd
  have hg : Primrec (fun p : Q => (([] : List BitString), (p.1.1).take p.1.2, 0)) :=
    Primrec.pair (Primrec.const [])
      (Primrec.pair
        (list_take_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
        (Primrec.const 0))
  have hh : Primrec₂ (fun (p : Q) (sb : (List BitString × List BitString × ℕ) × List BitString) =>
      greedyWindowStepList p.1.1 p.1.2 sb.1 sb.2) :=
    greedyWindowStepList_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  refine (Primrec.list_foldl hf hg hh).of_eq (fun p => ?_)
  rw [greedyWindowFoldList]

theorem temporalRefreshCountList_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => temporalRefreshCountList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2) := by
  have hG : Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => canonicalFinsetList (allStrings p.1.1).toFinset) := by
    convert ( Primrec.to_comp (canonicalFinsetList_toFinset_primrec.comp (allStrings_primrec.comp (Primrec.fst.comp (Primrec.fst))))) using 1
  have hsize : Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => 2 ^ (decodeCurve p.1.2.1 p.1.2.2.2.2)) := by
    have hsize : Computable (fun p : BitString × ℕ => 2 ^ (decodeCurve p.1 p.2)) := by
      have hsize : Primrec (fun p : BitString × ℕ => 2 ^ (decodeCurve p.1 p.2)) := by
        exact natPow_primrec.comp ( Primrec.const 2 ) ( decodeCurve_primrec.comp ( Primrec.fst ) ( Primrec.snd ) );
      exact hsize.to_comp;
    convert hsize.comp ( Computable.fst.comp ( Computable.snd.comp ( Computable.fst ) ) |> Computable.pair <| Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst ) ) ) ) ) using 1
  have hbad : Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => temporalBadEnumListList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2) := by
    have := temporalBadEnumListList_computable c;
    convert this.comp ( show Computable ( fun p : ( ℕ × BitString × ℕ × ℕ × ℕ ) × ℕ => ( ( p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1 ), p.2 ) ) from ?_ ) using 1;
    exact Computable.pair ( Computable.pair ( Computable.fst.comp ( Computable.fst ) ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.fst ) ) ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst ) ) ) ) ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst ) ) ) ) ) ) ) ) ( Computable.snd );
  convert Computable.snd.comp ( Computable.snd.comp ( greedyWindowFoldList_computable.comp ( Computable.pair ( Computable.pair hG hsize ) hbad ) ) ) using 1

/-- The computability of the temporal refresh count. -/
theorem temporalRefreshCount_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ =>
      temporalRefreshCount c p.1.1 (decodeCurve p.1.2.1) p.1.2.2.1 p.1.2.2.2.1
        p.1.2.2.2.2 p.2) := by
  refine Computable.of_eq (temporalRefreshCountList_computable c) ?_
  intro p
  exact temporalRefreshCountList_eq c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1
    p.1.2.2.2.2 p.2

/-- The computability of the temporal window.

CORRECTNESS REPAIR (this pass).  The previous statement used
`(temporalWindow ...).toList` as the codomain.  That gate is *false as stated*,
independently of the greedy construction: `Finset.toList` is
`Multiset.toList = Quotient.out`, which is `Classical.choice`-based and hence
not a computable function — there is no algorithm reproducing the particular
list representative that `Quotient.out` selects.  So `fun p => (…).toList` is
not `Computable` no matter how the window is built.

The faithful statement uses the codebase's canonical *computable* enumeration
`canonicalFinsetList S = S.sort bitStringLE` (see `CodedFiniteDistribution.lean`),
which is exactly the representation used everywhere else in this development
(e.g. `snapshotDescList`, `codedUniformOn … .code`).  This is the form actually
needed by `partrec_finalWindowFn`, whose window code is built through
`codedUniformEncoder ∘ canonicalFinsetList`, not through `Finset.toList`.

The original false statement is preserved (commented out) below for the record. -/
theorem temporalWindowList_eq (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen i t : ℕ) :
    temporalWindowList c n curve m c_gen i t = canonicalFinsetList (temporalWindow c n (decodeCurve curve) m c_gen i t) := by
  unfold temporalWindowList temporalWindow
  rw [greedyWindowFoldList_window_canonical, temporalBadEnumListList_eq]
  rfl

theorem temporalWindowList_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => temporalWindowList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2) := by
  have hG : Computable (fun p : (Nat × BitString × Nat × Nat × Nat) => canonicalFinsetList (allStrings p.1).toFinset) := by
    have hG : Primrec (fun p : ℕ => canonicalFinsetList (allStrings p).toFinset) := by
      convert canonicalFinsetList_toFinset_primrec.comp ( allStrings_primrec ) using 1;
    exact hG.comp ( Primrec.fst ) |> Primrec.to_comp;
  have hsize : Computable (fun p : (Nat × BitString × Nat × Nat × Nat) => 2 ^ (decodeCurve p.2.1 p.2.2.2.2)) := by
    have hsize : Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) => decodeCurve p.2.1 p.2.2.2.2) := by
      have hsize : Computable (fun p : (BitString × ℕ) => decodeCurve p.1 p.2) := by
        exact decodeCurve_primrec.to_comp;
      convert hsize.comp ( Computable.fst.comp ( Computable.snd ) |> Computable.pair <| Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) ) ) using 1;
    convert Computable.comp ( show Computable ( fun n : ℕ => 2 ^ n ) from ?_ ) hsize using 1;
    have h_exp : Primrec (fun n : ℕ => 2 ^ n) := by
      convert natPow_primrec.comp ( Primrec.const 2 ) ( Primrec.id ) using 1;
    exact h_exp.to_comp;
  convert Computable.comp ( show Computable ( fun p : ( List BitString × List BitString × ℕ ) => p.2.1 ) from ?_ ) ( greedyWindowFoldList_computable.comp ( show Computable ( fun p : ( ( List BitString × ℕ ) × List ( List BitString ) ) => p ) from ?_ ) ) |> Computable.comp <| show Computable ( fun p : ( ( Nat × BitString × Nat × Nat × Nat ) × ℕ ) => ( ( canonicalFinsetList ( allStrings p.1.1 ).toFinset, 2 ^ decodeCurve p.1.2.1 p.1.2.2.2.2 ), temporalBadEnumListList c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2 ) ) from ?_ using 1;
  · exact Computable.fst.comp ( Computable.snd );
  · exact Computable.id;
  · apply Computable.pair;
    · exact Computable.pair ( hG.comp ( Computable.fst ) ) ( hsize.comp ( Computable.fst ) );
    · convert temporalBadEnumListList_computable c using 1;
      constructor <;> intro h;
      · convert h using 1;
        constructor <;> intro h;
        · assumption;
        · convert h.comp ( show Computable ( fun p : ( Nat × BitString × Nat × Nat ) × ℕ => ( ( p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2, 0 ), p.2 ) ) from ?_ ) using 1;
          exact Computable.pair ( Computable.pair ( Computable.fst.comp Computable.fst ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp Computable.fst ) ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) ) ( Computable.pair ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) ) ( Computable.const 0 ) ) ) ) ) Computable.snd;
      · convert h.comp ( show Computable ( fun p : ( Nat × BitString × Nat × Nat × Nat ) × ℕ => ( ( p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1 ), p.2 ) ) from ?_ ) using 1;
        exact Computable.pair ( Computable.pair ( Computable.fst.comp ( Computable.fst ) ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.fst ) ) ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst ) ) ) ) ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst ) ) ) ) ) ) ) ) ( Computable.snd )

theorem temporalWindow_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => canonicalFinsetList (temporalWindow c p.1.1 (decodeCurve p.1.2.1) p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2)) := by
  refine Computable.of_eq (temporalWindowList_computable c) ?_
  intro p
  exact temporalWindowList_eq c p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2

/- FALSE as stated (`Finset.toList = Quotient.out` is noncomputable); superseded by the
`canonicalFinsetList` version above:

    theorem temporalWindow_computable (c : Nat.Partrec.Code) :
        Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ =>
          (temporalWindow c p.1.1 (decodeCurve p.1.2.1) p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2).toList) :=
      -- retired false route
-/

/-- The computability of testing whether the temporal window is empty. -/
theorem temporalWindow_nonempty_bool_computable (c : Nat.Partrec.Code) :
    Computable (fun p : (ℕ × BitString × ℕ × ℕ × ℕ) × ℕ => decide ((temporalWindow c p.1.1 (decodeCurve p.1.2.1) p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2).Nonempty)) := by
      refine Computable.of_eq (f := fun p => decide ( ( canonicalFinsetList ( temporalWindow c p.1.1 ( decodeCurve p.1.2.1 ) p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2 ) ).length > 0 )) ?_ ?_
      · -- The length of a list is computable.
        have h_length_computable : Computable (fun l : List BitString => l.length) := by
          exact Computable.list_length;
        have h_length_computable : Computable (fun n : ℕ => decide (n > 0)) := by
          convert Computable.of_eq _ _;
          exact fun n => Nat.recOn n Bool.false fun _ _ => Bool.true;
          · exact Computable.nat_casesOn ( Computable.id ) ( Computable.const false ) ( Computable.const true );
          · rintro ( _ | _ ) <;> simp +decide;
        exact h_length_computable.comp ( ‹Computable fun l : List BitString => l.length›.comp ( temporalWindow_computable c ) );
      · simp +decide [ Finset.Nonempty ]

/-
Computability of the parameter packer for the final-window decoder: it maps the
decoder input `s` (paired with a time `t`) to the tuple
`((fwNat_n s, fwCurveCode s, fwNat_m s, fwNat_c_gen s, fwNat_i s), t)` expected by
`temporalRefreshCount_computable` / `temporalWindow_computable`.
-/
theorem fwPacker_computable :
    Computable (fun s : BitString × ℕ =>
      (((fwNat_n s.1, fwCurveCode s.1, fwNat_m s.1, fwNat_c_gen s.1, fwNat_i s.1) :
        ℕ × BitString × ℕ × ℕ × ℕ), s.2)) := by
  apply Computable.pair;
  · apply Computable.pair;
    · convert Primrec.to_comp (decodeNatCode_primrec.comp (decodeFirst_primrec.comp Primrec.fst)) using 1;
    · apply Computable.pair;
      · have h_decodeSecond : Computable (fun s : BitString => decodeSecond s) := by
          exact decodeSecond_primrec.to_comp;
        exact h_decodeSecond.comp ( h_decodeSecond.comp ( h_decodeSecond.comp ( h_decodeSecond.comp ( h_decodeSecond.comp ( Computable.fst ) ) ) ) );
      · apply Computable.pair;
        · apply Computable.comp (Primrec.to_comp (decodeNatCode_primrec.comp (decodeFirst_primrec.comp (decodeSecond_primrec.comp (decodeSecond_primrec.comp (Primrec.id))))) ) (Computable.fst);
        · apply Computable.pair;
          · apply Computable.comp (Primrec.to_comp decodeNatCode_primrec);
            exact Computable.comp ( Primrec.to_comp decodeFirst_primrec ) ( Computable.comp ( Primrec.to_comp decodeSecond_primrec ) ( Computable.comp ( Primrec.to_comp decodeSecond_primrec ) ( Computable.comp ( Primrec.to_comp decodeSecond_primrec ) ( Computable.fst ) ) ) );
          · apply Computable.comp;
            · -- The function `fwNat_i` is computable because it is a composition of computable functions.
              apply Computable.comp (decodeNatCode_primrec.to_comp) (decodeFirst_primrec.to_comp.comp (decodeSecond_primrec.to_comp));
            · exact Computable.fst;
  · exact Computable.snd

/-- Refresh count as a computable function of the decoder input paired with a time. -/
theorem finalWindowFn_refreshCount_computable (c : Nat.Partrec.Code) :
    Computable (fun p : BitString × ℕ => temporalRefreshCount c (fwNat_n p.1)
      (decodeCurve (fwCurveCode p.1)) (fwNat_m p.1) (fwNat_c_gen p.1) (fwNat_i p.1) p.2) := by
  refine Computable.of_eq ((temporalRefreshCount_computable c).comp fwPacker_computable) ?_
  intro p; dsimp only

/-- The (canonical list of the) temporal window as a computable function of the
decoder input paired with a time. -/
theorem finalWindowFn_window_computable (c : Nat.Partrec.Code) :
    Computable (fun p : BitString × ℕ => canonicalFinsetList (temporalWindow c (fwNat_n p.1)
      (decodeCurve (fwCurveCode p.1)) (fwNat_m p.1) (fwNat_c_gen p.1) (fwNat_i p.1) p.2)) := by
  refine Computable.of_eq ((temporalWindow_computable c).comp fwPacker_computable) ?_
  intro p; dsimp only

/-- Nonemptiness test of the temporal window as a computable function of the decoder
input paired with a time. -/
theorem finalWindowFn_window_nonempty_computable (c : Nat.Partrec.Code) :
    Computable (fun p : BitString × ℕ => decide ((temporalWindow c (fwNat_n p.1)
      (decodeCurve (fwCurveCode p.1)) (fwNat_m p.1) (fwNat_c_gen p.1) (fwNat_i p.1) p.2).Nonempty)) := by
  refine Computable.of_eq ((temporalWindow_nonempty_bool_computable c).comp fwPacker_computable) ?_
  intro p; dsimp only

theorem finalWindowFn_version_computable :
    Computable (fun p : BitString × ℕ => fwNat_version p.1) :=
  (bitsToNat_primrec.comp (decodeFirst_primrec.comp (decodeSecond_primrec.comp
    (decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec))))).to_comp.comp
    Computable.fst

/-- Abstract decoder skeleton: for any computable step predicate `P` and any window
family `W` whose canonical list and nonemptiness test are computable, the map that
rfind-searches for the first time `P s t` holds and then emits the canonical uniform
code of the held window `W s t` (or diverges if empty) is partial recursive.  This is
the general shape of `finalWindowFn`, isolated so the partial-recursiveness proof does
not force `whnf` to unfold the heavy `temporalRefreshCount`/`temporalWindow` defs. -/
theorem partrec_codedWindow_decoder {α : Type} [Primcodable α]
    (P : α → ℕ → Bool) (W : α → ℕ → Finset BitString)
    (hP : Computable (fun x : α × ℕ => P x.1 x.2))
    (hWlist : Computable (fun x : α × ℕ => canonicalFinsetList (W x.1 x.2))) :
    Partrec (codedWindowDecoder P W) := by
  unfold codedWindowDecoder
  -- The nonemptiness guard is derived from the (computable) canonical list: a finset is
  -- nonempty iff its sorted list has positive length.  Deriving it here (rather than taking
  -- it as a hypothesis) keeps `decide (·.Nonempty)` out of the caller's unification problem.
  have hlt : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
    obtain ⟨inst, hpl⟩ := (Primrec.nat_lt : PrimrecRel (· < ·))
    exact (hpl.of_eq (fun p => by congr 1)).to_comp
  have hpos : Computable (fun n : ℕ => decide (0 < n)) :=
    hlt.comp (Computable.pair (Computable.const 0) Computable.id)
  have hWne : Computable (fun x : α × ℕ => decide (W x.1 x.2).Nonempty) := by
    refine Computable.of_eq (hpos.comp (Computable.list_length.comp hWlist)) (fun x => ?_)
    simp [canonicalFinsetList, Finset.length_sort, Finset.card_pos]
  apply Partrec.bind
  · exact Partrec.rfind (Computable₂.partrec₂ hP)
  · refine Partrec.of_eq (Partrec.cond hWne
      ((canonicalUniformCodeOfList_computable.comp hWlist).partrec) Partrec.none) ?_
    intro x
    by_cases h : (W x.1 x.2).Nonempty
    · have hd : decide (W x.1 x.2).Nonempty = true := by simp [h]
      simp only [hd, cond_true, dif_pos h, PFun.coe_val]
      rw [canonicalUniformCodeOfList_canonicalFinsetList _ h]
    · have hd : decide (W x.1 x.2).Nonempty = false := by simp [h]
      simp only [hd, cond_false, dif_neg h]

/- G3: The decoder is partial recursive.

The genuine content is fully discharged by the reusable, proved skeleton
`partrec_codedWindow_decoder` together with the proved computable primitives
`finalWindowFn_refreshCount_computable`, `finalWindowFn_version_computable`, and
`finalWindowFn_window_computable`.  `finalWindowFn c` is now *definitionally*
`codedWindowDecoder P W` with
`P s t = decide (temporalRefreshCount c (fwNat_n s) … t = fwNat_version s)` and
`W s t = temporalWindow c (fwNat_n s) … t`, so it matches the skeleton by a delta step
on `codedWindowDecoder`.

Historical note.  The earlier formulation inlined the `rfind`/`dite` shape directly into
`finalWindowFn`, and matching it against the skeleton drove `isDefEq` to `whnf`-reduce the
`decide (· = ·)` / `Decidable (·.Nonempty)` guards, unfolding the heavy `GreedyWindow.fold`
bodies of `temporalRefreshCount`/`temporalWindow` and timing out.  Two changes remove that
obstacle: (i) naming the decoder shape (`codedWindowDecoder`) so the caller unifies at the
named application rather than the raw guards, and (ii) `seal`-ing the two heavy defs for the
duration of this proof so no residual `whnf` can unfold them. -/
/-- G3: The decoder `finalWindowFn c` is partial recursive. -/
theorem partrec_finalWindowFn (c : Nat.Partrec.Code) :
    Partrec (finalWindowFn c) := by
  -- The step predicate is `Nat`-equality of the (computable) refresh count and version.
  -- Building it with `Computable₂.comp` (rather than `comp` with a `Computable.pair`) keeps
  -- the guard in the clean `decide (· = ·)` shape, so unifying it against the skeleton's
  -- predicate is a beta step and never forces `whnf` to evaluate the heavy `decide`.
  have heq2 : Computable₂ (fun a b : ℕ => decide (a = b)) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.fst Primrec.snd)).to_comp
  have hP := heq2.comp (finalWindowFn_refreshCount_computable c) finalWindowFn_version_computable
  -- `finalWindowFn c` is *definitionally* `codedWindowDecoder P W`; unfolding exposes only the
  -- named decoder application, so matching the skeleton is structural.
  unfold finalWindowFn
  exact partrec_codedWindow_decoder _ _ hP (finalWindowFn_window_computable c)

/-- G4: The decoder correctness (evaluation matches the window). -/
theorem finalWindowFn_eval_decoded (c_U : Nat.Partrec.Code)
    (n m c_gen i T version : ℕ) (curve : BitString)
    (hne : (temporalWindow c_U n (decodeCurve curve) m c_gen i T).Nonempty)
    (hfind : Nat.rfind (fun t => Part.some
      (decide (temporalRefreshCount c_U n (decodeCurve curve) m c_gen i t = version))) = Part.some T) :
    (codedUniformOn (temporalWindow c_U n (decodeCurve curve) m c_gen i T) hne).code ∈
      finalWindowFn c_U (finalWindowInput n i m c_gen version curve) := by
  unfold finalWindowFn codedWindowDecoder
  simp only [fwNat_n_finalWindowInput, fwCurveCode_finalWindowInput,
    fwNat_m_finalWindowInput, fwNat_c_gen_finalWindowInput, fwNat_i_finalWindowInput,
    fwNat_version_finalWindowInput]
  rw [hfind]
  simp only [Part.bind_some]
  simp [hne]

/-- Decoder correctness for the intended curve `h`.

This uses the current strengthened `ProfileCurve.curveDecodes` field, which gives full
equality `decodeCurve hc.code = h`.  Older bounded-prefix variants of this field were too
weak here because `temporalBadEnumList` scans all levels `j < n`; with full equality the
decoded temporal process and the process for `h` are definitionally aligned after rewriting. -/
lemma codedUniformOn_congr {W1 W2 : Finset BitString} (hW : W1 = W2) (h1 : W1.Nonempty) (h2 : W2.Nonempty) :
    (codedUniformOn W1 h1).code = (codedUniformOn W2 h2).code := by
  cases hW
  rfl

theorem finalWindowFn_eval (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (c n kx m c_gen i T version : ℕ) (h : ℕ → ℕ) (hc : ProfileCurve U c n kx m h)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length).Nonempty)
    (_hT : temporalRefreshCount c_U n h m c_gen i T = version)
    (hfind : Nat.rfind (fun t => Part.some
      (decide (temporalRefreshCount c_U n h m c_gen i t = version))) = Part.some T) :
    (codedUniformOn (temporalWindow c_U n h m c_gen i T) (temporalWindow_nonempty U c_U hc_code n h m c_gen kx i T hrem)).code ∈
      finalWindowFn c_U (finalWindowInput n i m c_gen version hc.code) := by
  have h_decode : decodeCurve hc.code = h := funext hc.curveDecodes
  have hfind' : Nat.rfind (fun t => Part.some (decide (temporalRefreshCount c_U n (decodeCurve hc.code) m c_gen i t = version))) = Part.some T := by
    have hR : (fun t => Part.some (decide (temporalRefreshCount c_U n (decodeCurve hc.code) m c_gen i t = version))) =
              (fun t => Part.some (decide (temporalRefreshCount c_U n h m c_gen i t = version))) := by rw [h_decode]
    rwa [hR]
  have hne : (temporalWindow c_U n (decodeCurve hc.code) m c_gen i T).Nonempty := by
    have hW : temporalWindow c_U n (decodeCurve hc.code) m c_gen i T = temporalWindow c_U n h m c_gen i T := by rw [h_decode]
    rw [hW]
    exact temporalWindow_nonempty U c_U hc_code n h m c_gen kx i T hrem
  have heval := finalWindowFn_eval_decoded c_U n m c_gen i T version hc.code hne hfind'
  have heq : (codedUniformOn (temporalWindow c_U n (decodeCurve hc.code) m c_gen i T) hne).code =
             (codedUniformOn (temporalWindow c_U n h m c_gen i T) (temporalWindow_nonempty U c_U hc_code n h m c_gen kx i T hrem)).code := by
    apply codedUniformOn_congr
    rw [h_decode]
  rwa [heq] at heval

theorem GreedyWindow_fold_count_mono {α : Type} [DecidableEq α] (G : Finset α) (first : Finset α → Finset α)
    (L : List (Finset α)) (st : Finset α × Finset α × ℕ) (L_suffix : List (Finset α)) :
    (L.foldl (GreedyWindow.step G first) st).2.2 ≤ ((L ++ L_suffix).foldl (GreedyWindow.step G first) st).2.2 := by
  rw [List.foldl_append]
  generalize (L.foldl (GreedyWindow.step G first) st) = st'
  induction L_suffix generalizing st' with
  | nil => rfl
  | cons hd tl ih =>
    exact (GreedyWindow.step_count_mono G first st' hd).trans (ih (GreedyWindow.step G first st' hd))

theorem temporalBadEnumList_prefix (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen t1 t2 : ℕ) (ht : t1 ≤ t2) :
    ∃ L_suffix, temporalBadEnumList c n h m c_gen t2 = temporalBadEnumList c n h m c_gen t1 ++ L_suffix := by
  unfold temporalBadEnumList
  have h_range : List.range (t2 + 1) = List.range (t1 + 1) ++ (List.range (t2 + 1)).drop (t1 + 1) := by
    have h1 := List.take_append_drop (t1 + 1) (List.range (t2 + 1))
    have h2 : List.take (t1 + 1) (List.range (t2 + 1)) = List.range (t1 + 1) := by
      rw [List.take_range]
      exact congr_arg List.range (Nat.min_eq_left (Nat.succ_le_succ ht))
    rw [h2] at h1
    exact h1.symm
  rw [h_range, List.flatMap_append]
  exact ⟨_, rfl⟩

theorem temporalRefreshCount_mono (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen i t1 t2 : ℕ) (ht : t1 ≤ t2) :
    temporalRefreshCount c n h m c_gen i t1 ≤ temporalRefreshCount c n h m c_gen i t2 := by
  unfold temporalRefreshCount
  obtain ⟨L_suffix, h_suffix⟩ := temporalBadEnumList_prefix c n h m c_gen t1 t2 ht
  rw [h_suffix]
  exact GreedyWindow_fold_count_mono _ _ _ _ L_suffix

/-- Gate B5-sim-core: The VV-faithful decoder for the held temporal window.
Replaces the overstrong `exists_fullBadUnionWindowDecoder`. -/
theorem exists_temporalWindowDecoder (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ enc : BitString →. BitString, Partrec enc ∧
      ∃ (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U),
      ∀ (c n kx m c_gen : ℕ) (h : ℕ → ℕ) (hc : ProfileCurve U c n kx m h) (i : ℕ)
        (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
            (badEnumList U n h m c_gen kx).length).Nonempty),
        ∃ version : ℕ, version ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) + 1 ∧
        ∃ T : ℕ, (temporalRefreshCount c_U n h m c_gen i T = version) ∧
        (∀ t ≥ T, temporalRefreshCount c_U n h m c_gen i t = version) ∧
        (codedUniformOn
            (temporalWindow c_U n h m c_gen i T)
            (temporalWindow_nonempty U c_U hc_code n h m c_gen kx i T hrem)).code
          ∈ enc (finalWindowInput n i m c_gen version hc.code) := by
  obtain ⟨c_U, hc_code⟩ : ∃ c_U : Nat.Partrec.Code, IsCodeFor c_U U := by
    convert Nat.Partrec.Code.exists_code.mp hU.isDecompressor using 1
  refine ⟨finalWindowFn c_U, partrec_finalWindowFn c_U, c_U, hc_code, ?_⟩
  intro c n kx m c_gen h hc i hrem
  obtain ⟨T, version, hbound, hT, hstable⟩ := temporalRefreshCount_stabilizes U c_U hc_code c n kx m c_gen i h hc hrem
  have hrfind : ∃ t, temporalRefreshCount c_U n h m c_gen i t = version := ⟨T, hT⟩
  set T_find := Nat.find hrfind
  have hT_find : temporalRefreshCount c_U n h m c_gen i T_find = version := Nat.find_spec hrfind
  have hfind : Nat.rfind (fun t => Part.some (decide (temporalRefreshCount c_U n h m c_gen i t = version))) = Part.some T_find := by
    have h_mem : T_find ∈ Nat.rfind (fun t => Part.some (decide (temporalRefreshCount c_U n h m c_gen i t = version))) := by
      rw [Nat.mem_rfind]
      constructor
      · simp [hT_find]
      · intro m hm
        simp [Nat.find_min hrfind hm]
    exact Part.eq_some_iff.mpr h_mem
  have hstable_find : ∀ t ≥ T_find, temporalRefreshCount c_U n h m c_gen i t = version := by
    intro t ht
    by_cases h_le_T : t ≤ T
    · have h1 : version ≤ temporalRefreshCount c_U n h m c_gen i t := by
        rw [←hT_find]
        exact temporalRefreshCount_mono _ _ _ _ _ _ _ _ ht
      have h2 : temporalRefreshCount c_U n h m c_gen i t ≤ version := by
        rw [←hT]
        exact temporalRefreshCount_mono _ _ _ _ _ _ _ _ h_le_T
      exact le_antisymm h2 h1
    · exact hstable t (le_of_not_ge h_le_T)
  refine ⟨version, hbound, T_find, hT_find, hstable_find, ?_⟩
  exact finalWindowFn_eval U c_U hc_code c n kx m c_gen i T_find version h hc hrem hT_find hfind

/-- **Gate B5-core (the genuine Vereshchagin–Vitányi machine-model coding gate).**

This is the set-complexity content of the VV coding step: the final greedy window
— a set of size `≤ 2^{h i}` — has set-complexity at most `i + m + O(log n)`.

Proof idea (VV): the final window is `firstElements (survivors r) (2^{h i})` where
`r` is the version number reached by the running-window process.  That window is
recoverable by a computable, dove-tailed simulation of the greedy process from the
inputs `(n, i, curve code of h, version number r)`; feeding this computable decoder
to `setComplexity_le_of_computable_code` gives
`setComplexity ≤ KPPlain(n) + KPPlain(i) + KPPlain(curve) + KPPlain(r) + O(1)`.
Here `KPPlain(curve) ≤ m` (`hc.curveComplexity`), `KPPlain(n), KPPlain(i) = O(log n)`
(with `i ≤ kx ≤ n` on the positive region), and the *version number is bounded* by
`r ≤ 2^{i+1} + n·2^{i+1}` (via the already-proved `bucket1_bound` and
`bucket2_bound_of_curve`), so `KPPlain(r) = O(log r) = i + O(log n)`.  Summing gives
the `i + m + O(log n)` bound.

**Statement shape (fixed this pass).**  The `O(log n)` coding overhead is an
*absolute* constant `c_code` coming from the (fixed) computable decoder — it depends
only on `U`, **not** on the construction slack `c_gen` used to build `badEnumList`.
The earlier statement wrote the bound as `logSlack c_gen n` and reused the *counting*
constant `c_gen` (fixed to `3` by `sum_badSetsUnion_card_lt`).  That was the wrong
shape: the coding overhead `KPPlain(n) + KPPlain(i) + KPPlain(r) + O(1) ≈ 5·log n`
generally exceeds `logSlack 3 n = 3·(bits n).length + 3`, so the gate as previously
stated was very likely *false*.  It is now `∃ c_code, ∀ …, setComplexity ≤
i + m + logSlack c_code n` with `c_code` independent of the construction parameter
`c_gen`; the caller then picks a working `c_gen ≥ max(3, c_code)` (counting still
holds, via `sum_badSetsUnion_card_lt_of_le`, for that larger `c_gen`).

The hypotheses match the VV proof exactly: `hc : ProfileCurve` supplies both the
curve budget `m` and the diagonal descent that bounds the version count; `hrem`
supplies nonemptiness of the window.  The implementation below uses the concrete
temporal simulation, rather than the false literal bridge
`greedyWindow_version_count_eq_fold` documented above. -/
lemma ENat_add_five_mul (A B C D E F c_pair : ENat) :
  A + (B + (C + (D + (E + F + c_pair) + c_pair) + c_pair) + c_pair) + c_pair =
  A + B + C + D + E + F + (c_pair + c_pair + c_pair + c_pair + c_pair) := by
  ac_rfl

lemma ENat_five_mul (c : ℕ) : (c + c + c + c + c : ENat) = (5 * c : ℕ) := by
  rw [←ENat.coe_add, ←ENat.coe_add, ←ENat.coe_add, ←ENat.coe_add]
  congr 1
  omega

/-- A small arithmetic consequence of the VV refresh-count bound: if the version
number is at most `(n + 1) * 2^(i+1) + 1`, then its binary representation has
`i + O(log n)` bits.  The extra `+2` absorbs the final `+1` and the strict
`Nat.size` bound. -/
theorem version_bits_length_le (n i version : ℕ)
    (hversion : version ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) + 1) :
    (Nat.bits version).length ≤ i + (Nat.bits (n + 1)).length + 2 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hpow_pos : 1 ≤ 2 ^ (i + 1) := Nat.one_le_pow (i + 1) 2 (by norm_num)
  have hnlt : n + 1 < 2 ^ (Nat.bits (n + 1)).length := by
    simpa [Nat.size_eq_bits_len] using Nat.lt_size_self (n + 1)
  have hversion' : version ≤ (n + 1) * 2 ^ (i + 1) + 1 := by
    nlinarith
  have hlt1 : (n + 1) * 2 ^ (i + 1) + 1 <
      (2 ^ (Nat.bits (n + 1)).length + 1) * 2 ^ (i + 1) := by
    nlinarith
  have hlt2 : (2 ^ (Nat.bits (n + 1)).length + 1) * 2 ^ (i + 1) ≤
      2 ^ ((Nat.bits (n + 1)).length + 1) * 2 ^ (i + 1) := by
    gcongr
    calc 2 ^ (Nat.bits (n + 1)).length + 1
        ≤ 2 ^ (Nat.bits (n + 1)).length + 2 ^ (Nat.bits (n + 1)).length := by
            gcongr
            exact Nat.one_le_pow (Nat.bits (n + 1)).length 2 (by norm_num)
      _ = 2 ^ ((Nat.bits (n + 1)).length + 1) := by
            rw [pow_succ]
            ring
  have hpow_eq : 2 ^ ((Nat.bits (n + 1)).length + 1) * 2 ^ (i + 1) =
      2 ^ (i + (Nat.bits (n + 1)).length + 2) := by
    rw [← pow_add]
    congr 1
    omega
  exact lt_of_le_of_lt hversion' (lt_of_lt_of_le hlt1 (by simpa [hpow_eq] using hlt2))

/-- **Set-complexity of the `m`-free first block.**  The window
`firstElements (stringsOfLength n) (2^s)` is computable from `(n, s)` alone: by
`firstElements_eq_take` it is the `toFinset` of the first `2^s` entries of the canonical
enumeration of the length-`n` cube, and that enumeration is itself computable from `n`
(`canonicalFinsetList_toFinset_primrec` composed with `allStrings`).  Hence, feeding the
computable encoder
`w ↦ canonicalUniformCodeOfList ((canonicalFinsetList (stringsOfLength …)).take (2^…))`
to `setComplexity_le_of_computable_code`, its set-complexity is
`≤ KPPlain (pairCode (natCode n) (natCode s)) + O(1) ≤ 2·log n + 2·log s + O(1)`.  When
`s ≤ n` this collapses to a single `logSlack c_fe n`.  This is the `m`-independent coding
step for the `m > n` regime of the final greedy window, where `badEnumList` is empty and the
window collapses to this block. -/
theorem firstElementsCube_setComplexity_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_fe : ℕ, 3 ≤ c_fe ∧ ∀ (n s : ℕ)
      (hne : (firstElements (stringsOfLength n) (2 ^ s)).Nonempty),
      s ≤ n →
      setComplexity U (firstElements (stringsOfLength n) (2 ^ s)) hne
        ≤ ((logSlack c_fe n : ℕ) : ENat) := by
  -- The computable `(n, s)`-encoder producing the code of the first block.
  have henc : Computable (fun w : BitString => canonicalUniformCodeOfList
      ((canonicalFinsetList (stringsOfLength (decodeNatCode (decodeFirst w)))).take
        (2 ^ decodeNatCode (decodeSecond w)))) := by
    refine canonicalUniformCodeOfList_computable.comp (Primrec.to_comp ?_)
    refine list_take_primrec.comp ?_ ?_
    · exact canonicalFinsetList_toFinset_primrec.comp
        (allStrings_primrec.comp (decodeNatCode_primrec.comp decodeFirst_primrec))
    · exact natPow_primrec.comp (Primrec.const 2)
        (decodeNatCode_primrec.comp decodeSecond_primrec)
  obtain ⟨c, hc⟩ := setComplexity_le_of_partrec_code U hU _ henc.partrec
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_nat, hc_nat⟩ := KPPlain_natCode_le_log U hU
  refine ⟨4 + 2 * c_nat + c_pair + c + 3, by omega, ?_⟩
  intro n s hne hs
  -- Code identity: the encoder on `pairCode (natCode n) (natCode s)` yields the window code.
  have hid : (fun w : BitString => canonicalUniformCodeOfList
      ((canonicalFinsetList (stringsOfLength (decodeNatCode (decodeFirst w)))).take
        (2 ^ decodeNatCode (decodeSecond w)))) (pairCode (natCode n) (natCode s))
      = (codedUniformOn (firstElements (stringsOfLength n) (2 ^ s)) hne).code := by
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeNatCode_natCode]
    set L := (canonicalFinsetList (stringsOfLength n)).take (2 ^ s) with hL
    have hnd : L.Nodup := (canonicalFinsetList_nodup _).sublist (List.take_sublist _ _)
    have hpw : L.Pairwise bitStringLE :=
      (Finset.pairwise_sort _ bitStringLE).sublist (List.take_sublist _ _)
    have hLtf : L.toFinset = firstElements (stringsOfLength n) (2 ^ s) :=
      (firstElements_eq_take _ _).symm
    have hcanon : canonicalFinsetList L.toFinset = L := canonicalFinsetList_of_sorted L hnd hpw
    have hne' : L.toFinset.Nonempty := by rw [hLtf]; exact hne
    calc canonicalUniformCodeOfList L
        = canonicalUniformCodeOfList (canonicalFinsetList L.toFinset) := by rw [hcanon]
      _ = (codedUniformOn L.toFinset hne').code :=
            canonicalUniformCodeOfList_canonicalFinsetList _ _
      _ = (codedUniformOn (firstElements (stringsOfLength n) (2 ^ s)) hne).code :=
            codedUniformOn_code_congr _ _ hLtf
  -- Complexity bound and arithmetic.
  have hmem : (codedUniformOn (firstElements (stringsOfLength n) (2 ^ s)) hne).code
      ∈ (fun w : BitString => Part.some (canonicalUniformCodeOfList
          ((canonicalFinsetList (stringsOfLength (decodeNatCode (decodeFirst w)))).take
            (2 ^ decodeNatCode (decodeSecond w))))) (pairCode (natCode n) (natCode s)) :=
    Part.mem_some_iff.mpr hid.symm
  have hstep := hc (firstElements (stringsOfLength n) (2 ^ s)) hne
    (pairCode (natCode n) (natCode s)) hmem
  have hpairbd : KPPlain U (pairCode (natCode n) (natCode s))
      ≤ KPPlain U (natCode n) + KPPlain U (natCode s) + (c_pair : ENat) :=
    hc_pair (natCode n) (natCode s)
  have hsize : (Nat.bits s).length ≤ (Nat.bits n).length := by
    simpa [Nat.size_eq_bits_len] using Nat.size_le_size hs
  have hbound : setComplexity U (firstElements (stringsOfLength n) (2 ^ s)) hne
      ≤ ((4 * (Nat.bits n).length + 2 * c_nat + c_pair + c : ℕ) : ENat) := by
    calc setComplexity U (firstElements (stringsOfLength n) (2 ^ s)) hne
        ≤ KPPlain U (pairCode (natCode n) (natCode s)) + (c : ENat) := hstep
      _ ≤ (KPPlain U (natCode n) + KPPlain U (natCode s) + (c_pair : ENat)) + (c : ENat) := by
            gcongr
      _ ≤ ((2 * (Nat.bits n).length + c_nat : ℕ) + (2 * (Nat.bits s).length + c_nat : ℕ)
            + (c_pair : ENat)) + (c : ENat) := by
            gcongr <;> [exact hc_nat n; exact hc_nat s]
      _ ≤ ((4 * (Nat.bits n).length + 2 * c_nat + c_pair + c : ℕ) : ENat) := by
            push_cast
            have : (Nat.bits s).length ≤ (Nat.bits n).length := hsize
            have hb : (0 : ℕ) ≤ (Nat.bits n).length := Nat.zero_le _
            calc ((2 * (Nat.bits n).length + c_nat : ℕ) : ENat)
                  + ((2 * (Nat.bits s).length + c_nat : ℕ) : ENat) + (c_pair : ENat) + (c : ENat)
                ≤ ((2 * (Nat.bits n).length + c_nat : ℕ) : ENat)
                  + ((2 * (Nat.bits n).length + c_nat : ℕ) : ENat) + (c_pair : ENat) + (c : ENat) := by
                    gcongr
              _ = ((4 * (Nat.bits n).length + 2 * c_nat + c_pair + c : ℕ) : ENat) := by
                    push_cast; ring
  refine hbound.trans ?_
  have : 4 * (Nat.bits n).length + 2 * c_nat + c_pair + c
      ≤ logSlack (4 + 2 * c_nat + c_pair + c + 3) n := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  exact_mod_cast this

/-
**Statement repair (this pass): the `m ≤ n` regime.**  The general statement (any `m`)
is *unprovable with the current decoder* `exists_temporalWindowDecoder`, whose input
`finalWindowInput` contains `natCode m`; coding it costs `≈ 2·log m` plain-complexity bits,
and `logSlack c_work n = c_work·(bits n).length + c_work` depends only on `n`, so `2·log m`
cannot be absorbed once `m > n`.  This is not a mere Lean obstacle: for `m > n` the held
temporal window is `firstElements (stringsOfLength n) (2^{h i})` (the bad-set list is empty,
since `badEnumList` is nonempty only when some `h j > m + logSlack ≥ m`, while `h j ≤ h 0 ≤ n`),
which is `m`-independent and would need a *different, `m`-free* decoder to code within budget.

The restriction `m ≤ n` is faithful to the article: there `m = K(h)` is the complexity of the
admissible curve `h`, which is a monotone function on `{0,…,n}` bounded by `h 0 ≤ n`, so
`K(h) ≤ n + O(log n)`; the coding bound `i + m + O(log n)` is stated exactly in that regime.
	Under `m ≤ n` we have `log m ≤ log n`, which the current decoder can absorb into `logSlack`.
	The unrestricted main-theorem chain uses this lemma only in the internal `m ≤ n` branch;
	the complementary `m > n` branch is discharged directly by the `m`-free first-elements
	decoder.
	-/
theorem temporalWindow_setComplexity_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ _c_code c_work : ℕ, 3 ≤ c_work ∧
    (∀ (n s : ℕ) (hne : (firstElements (stringsOfLength n) (2 ^ s)).Nonempty),
        s ≤ n → setComplexity U (firstElements (stringsOfLength n) (2 ^ s)) hne
          ≤ ((logSlack c_work n : ℕ) : ENat)) ∧
    ∀ (c n kx m : ℕ) (h : ℕ → ℕ) (_hc : ProfileCurve U c n kx m h) (i : ℕ)
      (_hi : i ≤ n) (_hmn : m ≤ n)
      (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_work kx)
        (badEnumList U n h m c_work kx).length).Nonempty),
      ∃ (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U) (T : ℕ),
        (∀ t ≥ T, temporalRefreshCount c_U n h m c_work i t = temporalRefreshCount c_U n h m c_work i T) ∧
        setComplexity U (temporalWindow c_U n h m c_work i T)
          (temporalWindow_nonempty U c_U hc_code n h m c_work kx i T hrem)
        ≤ ((i + m + logSlack c_work n : ℕ) : ENat) := by
  obtain ⟨enc, hpartrec, c_U, hc_code, h_enc⟩ := exists_temporalWindowDecoder U hU
  obtain ⟨c_sim, hc_map⟩ := setComplexity_le_of_partrec_code U hU enc hpartrec
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_nat, hc_nat⟩ := KPPlain_natCode_le_log U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_fe, _hc_fe3, hc_fe⟩ := firstElementsCube_setComplexity_le U hU
  -- `c_work` must be large enough to absorb the *self-encoding* cost of `c_work` itself:
  -- the decoder input `finalWindowInput` contains `natCode c_work`, costing `≈ 2·log c_work`
  -- bits, and this must fit inside `logSlack c_work n` even when `n` is small (`B = 0, 1`).
  -- Taking `c_work = base + 2·size base + 300` guarantees `2·size c_work ≤ 2·size base + O(1)`,
  -- which the `+300` slack covers.
  let base := 5 * c_pair + 4 * c_nat + c_len + c_sim + c_fe
  let c_work := base + 2 * Nat.size base + 300
  use base + 10, c_work
  refine ⟨by unfold c_work; omega, ?_, ?_⟩
  · -- The `m`-free first-block bound, transported to `c_work` via monotonicity of `logSlack`.
    intro n' s hne hsn
    refine (hc_fe n' s hne hsn).trans ?_
    have hle : c_fe ≤ c_work := by unfold c_work base; omega
    have hmono : logSlack c_fe n' ≤ logSlack c_work n' := by
      unfold logSlack; nlinarith [Nat.zero_le ((Nat.bits n').length), hle]
    exact_mod_cast hmono
  intro c n kx m h hc i hi hmn hrem
  use c_U, hc_code
  obtain ⟨version, h_version_bound, T, hT, hstable, h_enc_eval⟩ :=
    h_enc c n kx m c_work h hc i hrem
  use T
  have hstable' : ∀ t ≥ T, temporalRefreshCount c_U n h m c_work i t = temporalRefreshCount c_U n h m c_work i T := by
    intro t ht
    rw [hstable t ht, hT]
  refine ⟨hstable', ?_⟩
  have h_comp := hc_map _ (temporalWindow_nonempty U c_U hc_code n h m c_work kx i T hrem) _ h_enc_eval
  -- Now we bound the complexity.
  have h_pair1 := hc_pair (natCode n) (pairCode (natCode i) (pairCode (natCode m) (pairCode (natCode c_work) (pairCode (Nat.bits version) hc.code))))
  have h_pair2 := hc_pair (natCode i) (pairCode (natCode m) (pairCode (natCode c_work) (pairCode (Nat.bits version) hc.code)))
  have h_pair3 := hc_pair (natCode m) (pairCode (natCode c_work) (pairCode (Nat.bits version) hc.code))
  have h_pair4 := hc_pair (natCode c_work) (pairCode (Nat.bits version) hc.code)
  have h_pair5 := hc_pair (Nat.bits version) hc.code
  have h_tuple_bound : KPPlain U (finalWindowInput n i m c_work version hc.code) ≤
      KPPlain U (natCode n) + KPPlain U (natCode i) + KPPlain U (natCode m) + KPPlain U (natCode c_work) + KPPlain U (Nat.bits version) + KPPlain U hc.code + (5 * c_pair : ℕ) := by
    calc
      KPPlain U (finalWindowInput n i m c_work version hc.code)
        ≤ KPPlain U (natCode n) + KPPlain U (pairCode (natCode i) (pairCode (natCode m) (pairCode (natCode c_work) (pairCode (Nat.bits version) hc.code)))) + c_pair := h_pair1
      _ ≤ KPPlain U (natCode n) + (KPPlain U (natCode i) + KPPlain U (pairCode (natCode m) (pairCode (natCode c_work) (pairCode (Nat.bits version) hc.code))) + c_pair) + c_pair := by
        gcongr; exact h_pair2
      _ ≤ KPPlain U (natCode n) + (KPPlain U (natCode i) + (KPPlain U (natCode m) + KPPlain U (pairCode (natCode c_work) (pairCode (Nat.bits version) hc.code)) + c_pair) + c_pair) + c_pair := by
        gcongr; exact h_pair3
      _ ≤ KPPlain U (natCode n) + (KPPlain U (natCode i) + (KPPlain U (natCode m) + (KPPlain U (natCode c_work) + KPPlain U (pairCode (Nat.bits version) hc.code) + c_pair) + c_pair) + c_pair) + c_pair := by
        gcongr; exact h_pair4
      _ ≤ KPPlain U (natCode n) + (KPPlain U (natCode i) + (KPPlain U (natCode m) + (KPPlain U (natCode c_work) + (KPPlain U (Nat.bits version) + KPPlain U hc.code + c_pair) + c_pair) + c_pair) + c_pair) + c_pair := by
        gcongr; exact h_pair5
      _ = KPPlain U (natCode n) + KPPlain U (natCode i) + KPPlain U (natCode m) + KPPlain U (natCode c_work) + KPPlain U (Nat.bits version) + KPPlain U hc.code + (5 * c_pair : ℕ) := by
        rw [ENat_add_five_mul, ENat_five_mul]
  -- We have `version ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) + 1` from `h_version_bound`.
  -- The bit-length arithmetic is now isolated in `version_bits_length_le`; closing
  -- this line still needs the matching plain-complexity coding lemma for raw
  -- binary numerals, or a slightly larger slack constant using `KPPlain_le_length_add_log`.
  have h_version_bits := version_bits_length_le n i version h_version_bound
  have h_len_version : (KPPlain U (Nat.bits version) : ENat) ≤ (i + (Nat.bits (n + 1)).length + 2 + 2 * (Nat.bits (Nat.bits version).length).length + c_len : ℕ) := by
    calc (KPPlain U (Nat.bits version) : ENat)
      _ ≤ ((Nat.bits version).length + 2 * (Nat.bits (Nat.bits version).length).length + c_len : ℕ) := hc_len _
      _ ≤ (i + (Nat.bits (n + 1)).length + 2 + 2 * (Nat.bits (Nat.bits version).length).length + c_len : ℕ) := by gcongr
  have h_m : KPPlain U hc.code ≤ m := hc.curveComplexity
  have h_n : KPPlain U (natCode n) ≤ 2 * (Nat.bits n).length + c_nat := hc_nat n
  have h_i : KPPlain U (natCode i) ≤ 2 * (Nat.bits i).length + c_nat := hc_nat i
  have h_m_code : KPPlain U (natCode m) ≤ 2 * (Nat.bits m).length + c_nat := hc_nat m
  have h_c_work : KPPlain U (natCode c_work) ≤ 2 * (Nat.bits c_work).length + c_nat := hc_nat c_work
  -- Final absorption: under `hmn : m ≤ n` every non-`i`, non-`m` term is `O(log n)`, and the
  -- self-referential `natCode c_work` cost `2·log c_work` is covered by the `+300` slack in
  -- `c_work`.  The bit-length arithmetic is packaged in the `have`s below.
  have h_2size : ∀ k : ℕ, 2 * Nat.size k ≤ k + 6 := by
    intro k
    by_cases hk : k < 16;
    · interval_cases k <;> decide;
    · have := Nat.size_le.mp ( show Nat.size k ≤ k / 2 + 3 from ?_ );
      · have := Nat.size_le.mpr this; norm_num at this; omega;
      · rw [ Nat.size_le ];
        rw [ ← Nat.mod_add_div k 2 ] ; have := Nat.mod_lt k two_pos; interval_cases k % 2 <;> norm_num at hk ⊢;
        · exact Nat.recOn ( k / 2 ) ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at ihn ⊢ ; linarith;
        · norm_num [ Nat.add_div ];
          exact Nat.recOn ( k / 2 ) ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at ihn ⊢ ; linarith;
  simp +arith +decide [ Nat.size_eq_bits_len ] at *;
  have h_2size_c_work : 2 * Nat.size c_work ≤ 2 * Nat.size base + 20 := by
    have h_2size_c_work : Nat.size c_work ≤ Nat.size base + 10 := by
      rw [ Nat.size_le ];
      have h_2size_c_work : base < 2 ^ Nat.size base := Nat.lt_size_self base
      grind +locals;
    linarith;
  have h_2size_version : 2 * Nat.size (Nat.size version) ≤ 2 * Nat.size n + 4 := by
    have h_2size_version : Nat.size (Nat.size version) ≤ Nat.size (i + Nat.size n + 3) := by
      apply Nat.size_le_size;
      linarith [ show Nat.size ( n + 1 ) ≤ Nat.size n + 1 from Nat.size_le.mpr ( by
                  exact Nat.lt_of_le_of_lt ( Nat.succ_le_of_lt ( Nat.lt_size_self _ ) ) ( pow_lt_pow_right₀ ( by decide ) ( Nat.lt_succ_self _ ) ) ) ];
    have h_2size_version : Nat.size (i + Nat.size n + 3) ≤ Nat.size n + 2 := by
      rw [ Nat.size_le ];
      have := Nat.lt_size_self n;
      by_cases hn : n < 16;
      · interval_cases n <;> interval_cases i <;> trivial;
      · grind +qlia;
    linarith;
  refine le_trans ( hc_map _ _ _ h_enc_eval ) ?_;
  refine le_trans ( add_le_add h_tuple_bound le_rfl ) ?_;
  unfold logSlack; norm_cast; simp +arith +decide [ Nat.size_eq_bits_len ] at *;
  refine le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add h_n h_i ) h_m_code ) h_c_work ) h_len_version ) h_m ) le_rfl ) le_rfl ) ?_ ; norm_cast ; simp +arith +decide at *;
  have h_size_mono : Nat.size i ≤ Nat.size n ∧ Nat.size m ≤ Nat.size n := by
    exact ⟨ Nat.size_le_size hi, Nat.size_le_size hmn ⟩;
  have h_size_mono : (n + 1).size ≤ n.size + 1 := by
    rw [ Nat.size_le ];
    exact Nat.lt_of_le_of_lt ( Nat.succ_le_of_lt ( Nat.lt_size_self _ ) ) ( by norm_num [ pow_succ' ] );
  grind

/- Gate B5 (corrected): The final visited window is an `(i + m + O(log n), h i)`-description.
This is the machine-model coding step of Vereshchagin-Vitanyi. By targeting specifically
the final visited window at `v = L.length`, we avoid the vacuous over-generalization to all `v`.

To bound the complexity by `i + m + O(log n)`, one must code this window by its
*true visited version number* (which is bounded by `poly(n) * 2^i` via finite combinatorics),
along with the parameters `n, i` and the curve `h` (which costs `m`). The proof requires
a computable, dove-tailed simulation of the greedy process to map the bounded version
number back to the window, applying `setComplexity_le_of_computable_code`.

Old statement `mem_coverableSet_of_window` was technically true but misleading,
as coding the literal large index `v` does not fit in `O(log n)` bits.

**Statement repair (this pass).**  The earlier version of this gate carried no
`ProfileCurve` hypothesis, which made it *under-hypothesized to the point of being
false*: the coding bound `setComplexity ≤ i + m + O(log n)` genuinely needs (a)
`m` to be an actual description budget for the curve `h` — supplied by `hc.curveComplexity`. -/

theorem badEnumList_nil_of_m_eq_n (U : Map) (n : ℕ) (h : ℕ → ℕ) (c_gen kx : ℕ)
    (h_top : h 0 ≤ n) (h_antitone : Antitone h) :
    badEnumList U n h n c_gen kx = [] := by
  unfold badEnumList
  have h_empty : (Finset.range n).filter (fun j => n + logSlack c_gen n < h j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j _
    have h_le : h j ≤ n := by
      calc h j ≤ h 0 := h_antitone (Nat.zero_le j)
        _ ≤ n := h_top
    omega
  rw [h_empty]
  simp

theorem temporalBadEnumList_eq_nil_of_m_eq_n (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (c_gen kx t : ℕ) (h_empty : badEnumList U n h n c_gen kx = []) :
    temporalBadEnumList c_U n h n c_gen t = [] := by
  have h_sub := temporalBadEnumList_sublist_badEnumList U c_U hc_code n h n c_gen kx t
  cases h_temp : temporalBadEnumList c_U n h n c_gen t with
  | nil => rfl
  | cons head tail =>
    have h_in : head ∈ temporalBadEnumList c_U n h n c_gen t := by rw [h_temp]; simp
    have h_bad := h_sub head h_in
    rw [h_empty] at h_bad
    contradiction

theorem temporalWindow_zero_m_eq_n (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (c_work kx i : ℕ) (h_empty : badEnumList U n h n c_work kx = []) :
    temporalWindow c_U n h n c_work i 0 = firstElements (stringsOfLength n) (2 ^ h i) := by
  unfold temporalWindow
  have h_temp := temporalBadEnumList_eq_nil_of_m_eq_n U c_U hc_code n h c_work kx 0 h_empty
  rw [h_temp]
  simp [GreedyWindow.fold]

theorem badEnumList_nil_of_m_gt_n (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ)
    (h_top : h 0 ≤ n) (h_antitone : Antitone h) (hmn : n < m) :
    badEnumList U n h m c_gen kx = [] := by
  unfold badEnumList
  have h_empty : (Finset.range n).filter (fun j => m + logSlack c_gen n < h j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j _
    have h_le : h j ≤ n := by
      calc h j ≤ h 0 := h_antitone (Nat.zero_le j)
        _ ≤ n := h_top
    omega
  rw [h_empty]
  simp

theorem finalWindow_mem_coverableSet (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_work : ℕ, 3 ≤ c_work ∧
    ∀ (c n kx m : ℕ) (h : ℕ → ℕ) (_hc : ProfileCurve U c n kx m h) (i : ℕ)
      (_hi : i ≤ n)
      (_hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_work kx)
        (badEnumList U n h m c_work kx).length).Nonempty),
      ∃ S, lexLeastSurvivor U n h m c_work kx ∈ S ∧
           S ∈ descriptionsWithComplexityLeAndSizeLe U (i + m + logSlack c_work n) (h i) := by
  -- Use the temporal decoder code (`temporalWindow_setComplexity_le`) to bypass the static greedy
  -- window entirely. The coded temporal window maintains the required set complexity, and
  -- `temporalWindow_contains_survivor` ensures the realizing point is within the output.
  obtain ⟨c_code, c_work, hc_work, h_firstEl, h_temp⟩ := temporalWindow_setComplexity_le U hU
  refine ⟨c_work, hc_work, fun c n kx m h hc i hi hrem => ?_⟩
  by_cases hmn : m ≤ n
  · obtain ⟨c_U, hc_code_U, T, h_stable, h_comp⟩ := h_temp c n kx m h hc i hi hmn hrem
    have hne := temporalWindow_nonempty U c_U hc_code_U n h m c_work kx i T hrem
    have h_mem_S := temporalWindow_contains_survivor U c_U hc_code_U n h m c_work kx i T hrem h_stable
    have h_S_code : temporalWindow c_U n h m c_work i T ∈
        descriptionsWithComplexityLeAndSizeLe U (i + m + logSlack c_work n) (h i) := by
      rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
      exact ⟨mem_descriptionsWithComplexityLe_of_complexity hne h_comp,
        temporalWindow_card_le c_U n h m c_work i T⟩
    exact ⟨temporalWindow c_U n h m c_work i T, h_mem_S, h_S_code⟩
  · push_neg at hmn
    have h_badEnum_nil : badEnumList U n h m c_work kx = [] :=
      badEnumList_nil_of_m_gt_n U n h m c_work kx hc.top hc.antitone hmn
    have h_hi : h i ≤ n := le_trans (hc.antitone (Nat.zero_le i)) hc.top
    have heq : stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_work kx) (badEnumList U n h m c_work kx).length = stringsOfLength n := by
      rw [h_badEnum_nil]
      simp [badUnionUpTo]
    have hne2 : (firstElements (stringsOfLength n) (2 ^ h i)).Nonempty := by
      exact Finset.card_pos.mp ( by rw [ firstElements_card ] ; exact lt_min ( by norm_num ) ( Finset.card_pos.mpr (by rwa [heq] at hrem) ) )
    have h_mem_S : lexLeastSurvivor U n h m c_work kx ∈ firstElements (stringsOfLength n) (2 ^ h i) := by
      unfold lexLeastSurvivor
      simp only [heq]
      split_ifs with h_ne h_ne2
      · exact firstElements_mono_size (stringsOfLength n) Nat.one_le_two_pow (Finset.mem_toList.mp (List.head_mem h_ne2))
      · exfalso
        have h_eq_nil : (firstElements (stringsOfLength n) 1).toList = [] := by
          by_contra h_not_nil
          exact h_ne2 h_not_nil
        have h_empty : firstElements (stringsOfLength n) 1 = ∅ := Finset.toList_eq_nil.mp h_eq_nil
        have h_card := firstElements_card (stringsOfLength n) 1
        rw [h_empty] at h_card
        have h_pos : 0 < (stringsOfLength n).card := Finset.card_pos.mpr h_ne
        have h_min : min 1 (stringsOfLength n).card = 1 := min_eq_left h_pos
        rw [h_min] at h_card
        simp at h_card
      · exfalso
        exact h_ne (by rwa [heq] at hrem)
    have h_S_code : firstElements (stringsOfLength n) (2 ^ h i) ∈
        descriptionsWithComplexityLeAndSizeLe U (i + m + logSlack c_work n) (h i) := by
      rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
      have hcomp := h_firstEl n (h i) hne2 h_hi
      have hcomp2 : setComplexity U (firstElements (stringsOfLength n) (2 ^ h i)) hne2 ≤ ((i + m + logSlack c_work n : ℕ) : ENat) := by
        refine hcomp.trans ?_
        exact_mod_cast Nat.le_add_left (logSlack c_work n) (i + m)
      exact ⟨mem_descriptionsWithComplexityLe_of_complexity hne2 hcomp2,
        by rw [firstElements_card]; exact min_le_left _ _⟩
    exact ⟨firstElements (stringsOfLength n) (2 ^ h i), h_mem_S, h_S_code⟩

/-
Auxiliary: the full running bad-union (deleting every set of the enumeration) equals
the level-indexed union of `badSetsUnion`.  `badEnumList` is the `toList` of the finset
`((range n).filter …).biUnion (fun j => descriptions j)`, and `badUnionUpTo … L.length`
folds `∪` over that whole list; flattening the two `biUnion`s gives the level union.
-/
theorem badUnionUpTo_full_eq (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ) :
    badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length =
      ((Finset.range n).filter (fun j => m + logSlack c_gen n < h j)).biUnion
        (fun j => badSetsUnion U n h m c_gen j) := by
  unfold badUnionUpTo badEnumList badSetsUnion;
  rw [ List.take_length ];
  induction ( Finset.filter ( fun j => m + logSlack c_gen n < h j ) ( Finset.range n ) ) using Finset.induction <;> simp_all +decide [ Finset.biUnion_insert ];
  have h_foldl_union : ∀ (A B : Finset (Finset BitString)), (A ∪ B).toList.foldl (· ∪ ·) ∅ = A.toList.foldl (· ∪ ·) ∅ ∪ B.toList.foldl (· ∪ ·) ∅ := by
    intros A B
    have h_foldl_union : ∀ (l : List (Finset BitString)), List.foldl (fun x1 x2 => x1 ∪ x2) ∅ l = l.toFinset.biUnion id := by
      intro l; induction l using List.reverseRecOn <;> aesop;
    simp +decide [ h_foldl_union, Finset.ext_iff ];
    exact fun x => ⟨ fun ⟨ y, hy, hx ⟩ => by cases hy <;> [ left; right ] <;> exact ⟨ y, by assumption, hx ⟩, fun hx => hx.elim ( fun ⟨ y, hy, hx ⟩ => ⟨ y, Or.inl hy, hx ⟩ ) fun ⟨ y, hy, hx ⟩ => ⟨ y, Or.inr hy, hx ⟩ ⟩;
  have h_foldl_union : ∀ (A : Finset (Finset BitString)), A.toList.foldl (· ∪ ·) ∅ = A.biUnion id := by
    intro A; induction A using Finset.induction <;> simp_all +decide [ Finset.biUnion_insert ] ;
    convert h_foldl_union { ‹_› } ‹_› using 1 ; aesop;
  aesop

/-
Descent consequence: on the positive region an index is `< n`.  If `0 < h i` then
`i < i + h i ≤ h 0 ≤ n` by the `slope`/`antitone`/`top` fields of `ProfileCurve`.
-/
theorem profileCurve_pos_index_lt (U : Map) (c n kx m : ℕ) (h : ℕ → ℕ)
    (hc : ProfileCurve U c n kx m h) {i : ℕ} (hpos : 0 < h i) : i < n := by
  have hdesc : ∀ j, 0 < h j → j + h j ≤ h 0 := by
    intro j hj_pos
    induction j with
    | zero => norm_num;
    | succ j ih => cases hc.slope j <;> linarith [ ih ( by linarith [ hc.antitone ( Nat.le_succ j ) ] ), hc.antitone ( Nat.le_succ j ) ];
  linarith [ hdesc i hpos, hc.top ]

/-
Auxiliary: the survivor set is nonempty once the counting bound holds.  The full
bad-union has cardinality `≤ ∑ card (badSetsUnion j) < 2 ^ n = (stringsOfLength n).card`,
so some length-`n` string escapes it.
-/
theorem survivor_set_nonempty (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ)
    (hsum : ((Finset.range n).filter (fun i => m + logSlack c_gen n < h i)).sum
        (fun i => (badSetsUnion U n h m c_gen i).card) < 2 ^ n) :
    (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty := by
  contrapose! hsum;
  rw [ Finset.ext_iff ] at hsum;
  have h_card : (stringsOfLength n).card ≤ (badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length).card := by
    exact Finset.card_le_card fun x hx => by specialize hsum x; aesop;
  refine le_trans ?_ ( h_card.trans ?_ );
  · rw [ cardStringsOfLength ];
  · rw [ badUnionUpTo_full_eq ];
    exact Finset.card_biUnion_le

-- `lexLeastSurvivor_mem_rem` moved earlier (needed by `temporalWindow_contains_survivor`).

/-- Existence of a string in all coverable sets avoiding all bad sets.
This is the joint counting/greedy heart of Vereshchagin–Vitányi.

The *lower/avoidance* half is already fully proved without this gate
(`exists_string_avoiding_curve`, a pure counting argument via
`sum_badSetsUnion_card_lt`).  The remaining content is the *membership* clause
`x ∈ coverableSet U i (h i)` for every budget `i ≤ kx + logSlack c n`.

That clause genuinely requires the Vereshchagin–Vitányi greedy/staircase
construction of nested realizing sets and cannot be obtained by counting the
complement: by `coverableSet_card_le`, `coverableSet U i (h i)` has only
`≤ 2^{i+1+h i}` elements, so at low budgets *most* length-`n` strings are not
coverable and the union over levels of the non-coverable strings already fills
almost the whole cube.  Hence a purely enumerative existence argument (as used for
the avoidance half) is provably insufficient here; the proof below uses the
temporal greedy-window construction (each held window has `|A_i| ≤ 2^{h i}` and
complexity `≤ i + O(log n)`) to provide the upper half of the profile-realization
theorem `stat-any-curve`.

Why the obvious sub-cube construction does *not* suffice: fixing an `(n-h i)`-bit
prefix of `x` gives a set of size `2^{h i}` containing `x`, but its set complexity is
`≈ n - h i`, and along an admissible curve `i + h i ≤ h 0 ≤ n` (descent), so
`n - h i ≥ i` — the sub-cube is generally an `(n-h i, h i)`-description, *not* the
required `(i, h i)`-description (equality only for the exact slope `-1` diagonal).
The gate-free diagonal upper bound realizable this way is exactly
`structureFunction_prefix_upper_of_optimal` (`h_x(i) ≤ n - i + O(log n)`).  Reaching
complexity `≤ i` on the *interior* of the curve therefore forces the genuine VV
construction, whose `≈ i` "address" bits selecting the held window must be chosen
jointly with `x` (via the survival/greedy argument), not read off `x`'s prefix. -/
theorem exists_point_in_all_coverableSets (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_gen, ∀ c n kx m h, ProfileCurve U c n kx m h →
      ∃ x : BitString, x.length = n ∧
        (∀ i, i ≤ kx + logSlack c n → x ∈ coverableSet U (i + m + logSlack c_gen n) (h i)) ∧
        (∀ i, x ∉ badSetsUnion U n h m c_gen i ∨ h i ≤ m + logSlack c_gen n) := by
  -- Use the single construction slack chosen by the final-window coding gate; it is
  -- large enough for both counting (`≥ 3`) and machine-model coding overhead.
  obtain ⟨c_gen, hge3, hcode⟩ := finalWindow_mem_coverableSet U hU
  refine ⟨c_gen, fun c n kx m h hcurve => ?_⟩
  have hsum := sum_badSetsUnion_card_lt_of_le U c_gen hge3 c n kx m h hcurve
  have hrem := survivor_set_nonempty U n h m c_gen kx hsum
  have hxrem := lexLeastSurvivor_mem_rem U n h m c_gen kx hrem
  rw [Finset.mem_sdiff] at hxrem
  obtain ⟨hxlen0, hxnotbad⟩ := hxrem
  have hxlen : (lexLeastSurvivor U n h m c_gen kx).length = n :=
    (memStringsOfLength n _).mp hxlen0
  refine ⟨lexLeastSurvivor U n h m c_gen kx, hxlen, ?_, ?_⟩
  · -- Upper/membership half: the lex-least survivor lies in some coded window
    -- which is an `(i + m + O(log n), h i)`-description, hence in the coverable set.
    intro i _hi
    by_cases hi_le_n : i ≤ n
    · obtain ⟨S, h_mem_S, h_S_code⟩ := hcode c n kx m h hcurve i hi_le_n hrem
      unfold coverableSet
      rw [Finset.mem_biUnion]
      exact ⟨S, h_S_code, h_mem_S⟩
    · have h_zero : h i = 0 := by
        by_contra hpos
        have h_lt_n := profileCurve_pos_index_lt U c n kx m h hcurve (Nat.pos_of_ne_zero hpos)
        omega
      have hn_le_n : n ≤ n := le_rfl
      obtain ⟨S_n, h_mem_Sn, h_Sn_code⟩ := hcode c n kx m h hcurve n hn_le_n hrem
      have hile_n : n + m + logSlack c_gen n ≤ i + m + logSlack c_gen n := by
        have : n ≤ i := le_of_not_ge hi_le_n
        omega
      have hn_zero : h n = 0 := by
        by_contra hpos
        have h_lt_n := profileCurve_pos_index_lt U c n kx m h hcurve (Nat.pos_of_ne_zero hpos)
        omega
      rw [hn_zero] at h_Sn_code
      rw [h_zero]
      have hmem_n := descriptionsWithComplexityLeAndSizeLe_subset_of_le_left U 0 hile_n h_Sn_code
      unfold coverableSet
      rw [Finset.mem_biUnion]
      exact ⟨S_n, hmem_n, h_mem_Sn⟩
  · -- Lower/avoidance half: the survivor escapes the full bad-union, hence every
    -- level-`i` bad set (for the levels that actually appear in the enumeration).
    intro i
    by_cases hle : h i ≤ m + logSlack c_gen n
    · exact Or.inr hle
    · refine Or.inl (fun hxbad => hxnotbad ?_)
      rw [badUnionUpTo_full_eq]
      rw [Finset.mem_biUnion]
      refine ⟨i, ?_, hxbad⟩
      rw [Finset.mem_filter, Finset.mem_range]
      have hlt : m + logSlack c_gen n < h i := by omega
      refine ⟨profileCurve_pos_index_lt U c n kx m h hcurve (by omega), hlt⟩

/-- Gate C: set-complexity from a computable code.
If a computable `enc` maps a code `w` to the canonical uniform-set code of `A`,
then `setComplexity U A ≤ KPPlain U w + O(1)`. -/
theorem setComplexity_le_of_computable_code (U : Map) (hU : IsOptimalPrefixConditional U)
    (enc : BitString → BitString) (henc : Computable enc) :
    ∃ c, ∀ (A : Finset BitString) (hA : A.Nonempty) (w : BitString),
      enc w = (codedUniformOn A hA).code →
      setComplexity U A hA ≤ KPPlain U w + c := by
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU enc henc
  refine ⟨c, fun A hA w hw => ?_⟩
  unfold setComplexity
  rw [← hw]
  exact hc w

/- **Gate E3 (removed: UNPROVABLE as stated).**
`exists_generic_point` claimed `x ∈ realizingFamily U n h m c_gen i`, which is false
because `realizingFamily` was an arbitrary `choose`. Superseded by `exists_point_in_all_coverableSets`. -/

/-- Gate F: Upper half of the realization theorem.  A string lying in every coverable set
`coverableSet U i (h i)` inherits, for each budget `i`, an `(i + O(1), h i)`-description,
so its profile contains the curve up to logarithmic slack. -/
theorem realization_upper (U : Map) :
    ∃ c_up, ∀ c_in c n kx m h, ProfileCurve U c n kx m h → ∀ x,
      (∀ i, i ≤ kx + logSlack c n → x ∈ coverableSet U (i + m + logSlack c_in n) (h i)) →
      ∀ i, i ≤ kx + logSlack c n → InDescriptionProfile U x (i + m + logSlack (c_in + c_up) n) (h i + logSlack (c_in + c_up) n) := by
  obtain ⟨c_fam, hc_fam⟩ := inDescriptionProfile_of_mem_coverableSet U
  use c_fam
  intro c_in c n kx m h hcurve x hxmem i hi_le
  have h_in := hc_fam (i + m + logSlack c_in n) (h i) x (hxmem i hi_le)
  have h1 : i + m + logSlack c_in n + c_fam ≤ i + m + logSlack (c_in + c_fam) n := by
    unfold logSlack
    have : c_in * (Nat.bits n).length + c_in + c_fam ≤ (c_in + c_fam) * (Nat.bits n).length + (c_in + c_fam) := by
      rw [Nat.add_mul]
      omega
    omega
  have h2 : h i ≤ h i + logSlack (c_in + c_fam) n := by
    unfold logSlack
    have : h i ≤ h i + ((c_in + c_fam) * (Nat.bits n).length + (c_in + c_fam)) := by omega
    exact this
  exact (h_in.mono_i h1).mono_j h2

/-- Gate H0: The main profile / curve realization theorem (`stat-any-curve`).

For every admissible `ProfileCurve h` there is a length-`n` string `x` whose
description profile follows the curve up to logarithmic slack: `x` has an
`(i + O(log n), h i + O(log n))`-description for every `i` (the profile contains the
curve, upper half) and, wherever `h i` exceeds the slack, `x` has *no*
`(i, h i - O(log n))`-description (the profile does not cross below the curve, lower
half).

This is assembled here from the *upper* gate `realization_upper` (Gate F) applied to
the generic point produced by `exists_point_in_all_coverableSets` (Gate E4c), whose avoidance
clause is exactly the *lower* half. -/
theorem exists_string_with_profile (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_real, ∀ c n kx m h, ProfileCurve U c n kx m h →
      ∃ x : BitString, x.length = n ∧
        (∀ i, InDescriptionProfile U x (i + m + logSlack c_real n) (h i + logSlack c_real n)) ∧
        (∀ i, ¬ InDescriptionProfile U x i (h i - (m + logSlack c_real n)) ∨ h i ≤ m + logSlack c_real n) := by
  obtain ⟨c_gen, hgen⟩ := exists_point_in_all_coverableSets U hU
  obtain ⟨c_up, hup⟩ := realization_upper U
  refine ⟨c_gen + c_up, fun c n kx m h hcurve => ?_⟩
  -- The generic point: lies in every coverable set, and avoids every small description.
  obtain ⟨x, hxlen, hxmem, hxavoid⟩ := hgen c n kx m h hcurve
  have hslack_gen : logSlack c_gen n ≤ logSlack (c_gen + c_up) n :=
    logSlack_mono_left (Nat.le_add_right _ _) n
  refine ⟨x, hxlen, fun i => ?_, fun i => ?_⟩
  · -- Upper half
    by_cases hle : i ≤ kx + logSlack c n
    · exact hup c_gen c n kx m h hcurve x (fun j hj => hxmem j hj) i hle
    · have h_k_le : kx + logSlack c n ≤ kx + logSlack c n := le_rfl
      have hF_k := hup c_gen c n kx m h hcurve x (fun j hj => hxmem j hj) (kx + logSlack c n) h_k_le
      have hi_gt := not_le.mp hle
      have hi_le : kx + logSlack c n ≤ i := le_of_lt hi_gt
      have hF_k' : InDescriptionProfile U x (i + m + logSlack (c_gen + c_up) n) (h (kx + logSlack c n) + logSlack (c_gen + c_up) n) :=
        hF_k.mono_i (by omega)
      have h_zero : h (kx + logSlack c n) = 0 := hcurve.bottom
      rw [h_zero] at hF_k'
      have h_zero_i : h i = 0 := by
        have h_antitone := hcurve.antitone hi_le
        rw [h_zero] at h_antitone
        omega
      rw [h_zero_i]
      exact hF_k'
  · -- Lower half: relax the generic point's avoidance clause to the larger slack.
    rcases hxavoid i with hno | hle
    · -- No `(i, h i - (m + logSlack c_gen n))`-description ⟹ none with the larger subtrahend.
      refine Or.inl (fun hcontra => hno ?_)
      have h_prof : InDescriptionProfile U x i (h i - (m + logSlack c_gen n)) :=
        hcontra.mono_j (Nat.sub_le_sub_left (Nat.add_le_add_left hslack_gen m) (h i))
      exact mem_badSetsUnion_of_inDescriptionProfile U n h m c_gen i h_prof
    · exact Or.inr (le_trans hle (Nat.add_le_add_left hslack_gen m))

/- Gate H1: antistochastic / extremal-profile strings exist.

An *antistochastic* string of length `n` and complexity `k` should have an almost
minimal description profile.  For budgets below `k`, every `(i, j)`-description
must lie near the full-cube boundary.  The correct lower-bound shape is
`i + j >= n - O(log n)`, not `j >= n - O(log n)` by itself.

This gate should be treated as a corollary of Gate H0 (`exists_string_with_profile`),
not as an independent construction.  Use the simple extremal curve
`h i = if i < k then n - i else 0` (encoded by the parameters `n,k`, hence with
only logarithmic/`m` overhead) and apply the lower half of the curve-realization
theorem.  That lower half gives `j >= h i - O(log n)` for `i` below the complexity
threshold, hence `i + j >= n - O(log n)`.  The endpoint/right-tail lemmas give
that `KPPlain U x` is equal to `k` up to `O(log n)`.

This replaces two earlier mistakes: a version with
`forall i >= k, not InDescriptionProfile U x i 0`, which is false because the singleton
`{x}` is available once `i >= K(x)`, and an overstrong version asking for
`j >= n - O(log n)` instead of the profile-boundary inequality `i + j >= n - O(log n)`. -/
-- Gate H1a: curve code complexity

/-- `natCode` is primitive recursive (written via `List.range`/`List.map`). -/
theorem natCode_primrec : Primrec natCode := by
  have h : natCode = fun n => ((List.range n).map (fun _ => true)) ++ [false] := by
    funext n; simp [natCode]
  rw [h]
  exact (Primrec.list_append.comp
    (Primrec.list_map Primrec.list_range (Primrec.const true).to₂) (Primrec.const [false]))

/-- The antistochastic extremal curve `i ↦ if i < k then n - i else 0`, encoded up to
budget `K` by `curveEncode`, viewed as a *computable* function of a bitstring that
codes the triple `(n, k, K)` as `pairCode (natCode n) (pairCode (natCode k) (natCode K))`.
This is the witness making the curve code's plain complexity only `O(log (n+K))`. -/
noncomputable def antiCurveOfTriple (w : BitString) : BitString :=
  curveEncode (fun i => if i < decodeNatCode (decodeFirst (decodeSecond w))
                        then decodeNatCode (decodeFirst w) - i else 0)
              (decodeNatCode (decodeSecond (decodeSecond w)))

theorem antiCurveOfTriple_computable : Computable antiCurveOfTriple := by
  unfold antiCurveOfTriple curveEncode
  have hn : Primrec (fun w => decodeNatCode (decodeFirst w)) :=
    decodeNatCode_primrec.comp decodeFirst_primrec
  have hk : Primrec (fun w => decodeNatCode (decodeFirst (decodeSecond w))) :=
    decodeNatCode_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)
  have hK : Primrec (fun w => decodeNatCode (decodeSecond (decodeSecond w))) :=
    decodeNatCode_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec)
  have hrange : Primrec (fun w => List.range (decodeNatCode (decodeSecond (decodeSecond w)) + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp hK)
  have hg : Primrec₂ (fun (w : BitString) (i : ℕ) =>
      if i < decodeNatCode (decodeFirst (decodeSecond w))
      then decodeNatCode (decodeFirst w) - i else 0) := by
    apply Primrec.ite (Primrec.nat_lt.comp Primrec.snd (hk.comp Primrec.fst))
    · exact Primrec.nat_sub.comp (hn.comp Primrec.fst) Primrec.snd
    · exact Primrec.const 0
  have hmap : Primrec (fun w => (List.range (decodeNatCode (decodeSecond (decodeSecond w)) + 1)).map
      (fun i => if i < decodeNatCode (decodeFirst (decodeSecond w))
                then decodeNatCode (decodeFirst w) - i else 0)) :=
    Primrec.list_map hrange hg
  have hfinal : Primrec (fun w => (( (List.range (decodeNatCode (decodeSecond (decodeSecond w)) + 1)).map
      (fun i => if i < decodeNatCode (decodeFirst (decodeSecond w))
                then decodeNatCode (decodeFirst w) - i else 0)).flatMap
      (fun v => List.replicate v true ++ [false]))) := by
    apply Primrec.list_flatMap hmap
    have h2 : Primrec₂ (fun (_ : BitString) (v : ℕ) => natCode v) := natCode_primrec.comp Primrec.snd
    simpa [natCode] using h2
  exact hfinal.to_comp

theorem antiCurveOfTriple_triple (n k K : ℕ) :
    antiCurveOfTriple (pairCode (natCode n) (pairCode (natCode k) (natCode K)))
      = curveEncode (fun i => if i < k then n - i else 0) K := by
  simp [antiCurveOfTriple, decodeFirst_pairCode, decodeSecond_pairCode, decodeNatCode_natCode]

theorem exists_antistochastic_curve_code (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_code, ∀ n k K, k ≤ n → k ≤ K →
      ∃ code : BitString,
        (∀ i, decodeCurve code i = if i < k then n - i else 0) ∧
        KPPlain U code ≤ (logSlack c_code (n + K) : ENat) := by
  obtain ⟨c_map, hc_map⟩ := KPPlain_map_le U hU antiCurveOfTriple antiCurveOfTriple_computable
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_nat, hc_nat⟩ := KPPlain_natCode_le_log U hU
  refine ⟨6 + (3*c_nat + 2*c_pair + c_map), fun n k K hk hkK => ?_⟩
  refine ⟨curveEncode (fun i => if i < k then n - i else 0) K,
    fun i => ?_, ?_⟩
  · by_cases hi : i ≤ K
    · rw [decodeCurve_curveEncode _ _ hi]
    · push_neg at hi
      rw [decodeCurve_curveEncode_out_of_bounds _ _ hi]
      have : ¬ (i < k) := by omega
      rw [if_neg this]
  rw [(antiCurveOfTriple_triple n k K).symm]
  set w := pairCode (natCode n) (pairCode (natCode k) (natCode K)) with hw
  have hwbound : KPPlain U w
      ≤ ((2*(Nat.bits n).length + 2*(Nat.bits k).length + 2*(Nat.bits K).length
          + (3*c_nat + 2*c_pair) : ℕ) : ENat) := by
    calc KPPlain U w
        ≤ KPPlain U (natCode n) + KPPlain U (pairCode (natCode k) (natCode K)) + c_pair :=
          hc_pair (natCode n) (pairCode (natCode k) (natCode K))
      _ ≤ KPPlain U (natCode n)
            + (KPPlain U (natCode k) + KPPlain U (natCode K) + c_pair) + c_pair := by
          gcongr; exact hc_pair (natCode k) (natCode K)
      _ ≤ ((2*(Nat.bits n).length + c_nat : ℕ):ENat)
            + (((2*(Nat.bits k).length + c_nat:ℕ):ENat)
              + ((2*(Nat.bits K).length + c_nat:ℕ):ENat) + c_pair) + c_pair := by
          gcongr
          · exact hc_nat n
          · exact hc_nat k
          · exact hc_nat K
      _ = _ := by push_cast; ring
  have hbound : KPPlain U (antiCurveOfTriple w)
      ≤ ((2*(Nat.bits n).length + 2*(Nat.bits k).length + 2*(Nat.bits K).length
          + (3*c_nat + 2*c_pair + c_map) : ℕ) : ENat) := by
    calc KPPlain U (antiCurveOfTriple w)
        ≤ KPPlain U w + c_map := hc_map w
      _ ≤ ((2*(Nat.bits n).length + 2*(Nat.bits k).length + 2*(Nat.bits K).length
          + (3*c_nat + 2*c_pair) : ℕ) : ENat) + c_map := by gcongr
      _ = _ := by push_cast; ring
  refine le_trans hbound ?_
  have hL : (Nat.bits n).length ≤ (Nat.bits (n+K)).length := length_natBits_mono (by omega)
  have hLk : (Nat.bits k).length ≤ (Nat.bits (n+K)).length := length_natBits_mono (by omega)
  have hLK : (Nat.bits K).length ≤ (Nat.bits (n+K)).length := length_natBits_mono (by omega)
  have hnat : 2*(Nat.bits n).length + 2*(Nat.bits k).length + 2*(Nat.bits K).length
      + (3*c_nat + 2*c_pair + c_map) ≤ logSlack (6 + (3*c_nat + 2*c_pair + c_map)) (n+K) := by
    unfold logSlack
    set L := (Nat.bits (n+K)).length
    have h6 : 6 * L ≤ (6 + (3*c_nat + 2*c_pair + c_map)) * L := Nat.mul_le_mul_right L (by omega)
    nlinarith [hL, hLk, hLK]
  exact_mod_cast hnat

/-- Pure log-slack folding for `exists_antistochastic`: the finitely many
logarithmic overheads produced by the profile construction (`c_real`), the curve
code (`c_code`), the two-part decoder (`c_plain`) and the singleton endpoint
(`c_sing`) all fold into a single `logSlack c n`.  Every argument to an inner
`logSlack` is linear in `n` (since `k ≤ n` and each `logSlack _ n ≤ n + O(1)`), so
`logSlack_linear_bound`/`logSlack_le_add_const` and additivity discharge it. -/
theorem antistochastic_slack (c_real c_code c_plain c_sing c_len : ℕ) :
    ∃ c : ℕ, ∃ C_M : ℕ, ∀ n k : ℕ, k ≤ n →
      (logSlack c_code (n + max (k + logSlack c_real n) n) ≤ logSlack C_M n) ∧
      (logSlack c_code (n + max (k + logSlack c_real n) n) + 2 * logSlack c_real n
        + logSlack c_plain
            (n + (k + logSlack c_code (n + max (k + logSlack c_real n) n) + logSlack c_real n)
              + logSlack c_real n)
        ≤ logSlack c n)
      ∧ (logSlack c_sing n
          + logSlack c_code (n + max (k + logSlack c_real n) n) + logSlack c_real n
          ≤ logSlack c n)
      ∧ (n < logSlack C_M n → n + 2 * (Nat.bits n).length + c_len ≤ logSlack c n) := by
  obtain ⟨b_r, hb_r⟩ := logSlack_le_add_const c_real
  obtain ⟨C_M, hC_M⟩ := logSlack_linear_bound c_code 4 b_r
  obtain ⟨b_M, hb_M⟩ := logSlack_le_add_const C_M
  obtain ⟨C_P, hC_P⟩ := logSlack_linear_bound c_plain 5 (b_M + 2 * b_r)
  refine ⟨C_M + 2 * c_real + C_P + c_sing + c_real + (2 * C_M + c_len + 2), C_M, fun n k hk => ?_⟩
  have hM : logSlack c_code (n + max (k + logSlack c_real n) n) ≤ logSlack C_M n := by
    have harg : n + max (k + logSlack c_real n) n ≤ 4 * n + b_r := by have := hb_r n; omega
    exact le_trans (logSlack_mono_right _ harg) (hC_M n)
  have hMlin : logSlack c_code (n + max (k + logSlack c_real n) n) ≤ n + b_M :=
    le_trans hM (hb_M n)
  have hP : logSlack c_plain
      (n + (k + logSlack c_code (n + max (k + logSlack c_real n) n) + logSlack c_real n)
        + logSlack c_real n) ≤ logSlack C_P n := by
    have harg : n + (k + logSlack c_code (n + max (k + logSlack c_real n) n) + logSlack c_real n)
        + logSlack c_real n ≤ 5 * n + (b_M + 2 * b_r) := by
      have h1 := hb_r n; have h2 := hMlin; omega
    exact le_trans (logSlack_mono_right _ harg) (hC_P n)
  refine ⟨hM, ?_, ?_, ?_⟩
  · refine le_trans (add_le_add (add_le_add hM le_rfl) hP) ?_
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  · refine le_trans (add_le_add (add_le_add le_rfl hM) le_rfl) ?_
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  · intro hn
    unfold logSlack at hn ⊢
    nlinarith [Nat.zero_le ((Nat.bits n).length)]

theorem exists_antistochastic (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n k : ℕ, k ≤ n →
      ∃ x : BitString, x.length = n ∧
        KPPlain U x ≤ (k + logSlack c n : ENat) ∧
        (k : ENat) ≤ KPPlain U x + logSlack c n ∧
        (∀ i j : ℕ, i + logSlack c n < k → InDescriptionProfile U x i j →
          n ≤ i + j + logSlack c n) := by
  obtain ⟨c_real, h_real⟩ := exists_string_with_profile U hU
  obtain ⟨c_code, h_code⟩ := exists_antistochastic_curve_code U hU
  obtain ⟨c_plain, h_plain⟩ := KPPlain_le_of_inDescriptionProfile U hU
  obtain ⟨c_sing, h_sing⟩ := mem_descriptionProfileSet_singleton_of_optimal U hU
  obtain ⟨c_len, h_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c, C_M, hc⟩ := antistochastic_slack c_real c_code c_plain c_sing c_len
  refine ⟨c, fun n k hk => ?_⟩
  obtain ⟨hM_le, hA, hB, hn_small_bound⟩ := hc n k hk
  set s := logSlack c_real n with hs
  set m := logSlack c_code (n + max (k + s) n) with hm
  by_cases hmn : m ≤ n
  · -- Build the extremal antistochastic curve and realize it.
    have hkK : k ≤ max (k + s) n := le_trans (Nat.le_add_right k s) (le_max_left _ _)
    obtain ⟨code, h_dec, h_comp⟩ := h_code n k (max (k + s) n) hk hkK
    set h_func : ℕ → ℕ := fun i => if i < k then n - i else 0 with hfunc
    have h_curve : ProfileCurve U c_real n k m h_func := by
      refine ⟨code, h_dec, h_comp, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij; simp only [hfunc]; split <;> split <;> omega
      · intro i; simp only [hfunc]; split <;> split <;> omega
      · simp only [hfunc]; split <;> omega
      · simp only [hfunc]; rw [if_neg (by omega)]
      · intro i; simp only [hfunc]; split <;> omega
    obtain ⟨x, hx_len, hx_up, hx_low⟩ := h_real c_real n k m h_func h_curve
    -- `KPPlain U x` is finite, so name it `kx`.
    have hxne : KPPlain U x ≠ ⊤ := ne_top_of_le_ne_top (by
      have h : (↑(List.length x) + 2 * (↑(List.length x).bits.length : ENat) + ↑c_len)
          = ((List.length x + 2 * (List.length x).bits.length + c_len : ℕ) : ENat) := by
        push_cast; ring
      rw [h]; exact ENat.coe_ne_top _) (h_len x)
    obtain ⟨kx, hkx⟩ : ∃ kx : ℕ, KPPlain U x = (kx : ENat) :=
      ⟨(KPPlain U x).toNat, (ENat.coe_toNat hxne).symm⟩
    refine ⟨x, hx_len, ?_, ?_, ?_⟩
    · -- Upper complexity bound: `K(x) ≤ k + O(log n)`.
      have h_k := hx_up k
      have h_func_k : h_func k = 0 := by simp only [hfunc]; rw [if_neg (by omega)]
      rw [h_func_k, zero_add] at h_k
      have h_plain_k := h_plain x n (k + m + s) s hx_len h_k
      refine le_trans h_plain_k ?_
      have : (k + m + s) + s + logSlack c_plain (n + (k + m + s) + s)
          ≤ k + logSlack c n := by
        have := hA; omega
      exact_mod_cast this
    · -- Lower complexity bound: `k ≤ K(x) + O(log n)`.
      have h_i0 : InDescriptionProfile U x (kx + logSlack c_sing n) 0 :=
        h_sing x n kx hx_len hkx
      have hlow := hx_low (kx + logSlack c_sing n)
      have hknat : k ≤ kx + logSlack c n := by
        by_cases hik : (kx + logSlack c_sing n) < k
        · -- `h_func i0 = n - i0`; the singleton forbids the small-description escape.
          have hfi : h_func (kx + logSlack c_sing n) = n - (kx + logSlack c_sing n) := by
            simp only [hfunc]; rw [if_pos hik]
          rw [hfi] at hlow
          rcases hlow with hno | hle
          · exact absurd (h_i0.mono_j (Nat.zero_le _)) hno
          · have hB' := hB; omega
        · have hB' := hB; omega
      calc (k : ENat) ≤ ((kx + logSlack c n : ℕ) : ENat) := by exact_mod_cast hknat
        _ = KPPlain U x + logSlack c n := by rw [hkx]; push_cast; ring
    · -- Profile stays above the sufficiency line `n - O(log n)` below budget `k`.
      intro i j hij hprof
      have hik : i < k := by omega
      have hfi : h_func i = n - i := by simp only [hfunc]; rw [if_pos hik]
      have hlow := hx_low i
      rw [hfi] at hlow
      rcases hlow with hno | hle
      · by_cases hj : j ≤ (n - i) - (m + s)
        · exact absurd (hprof.mono_j hj) hno
        · have := hA; omega
      · have := hA; omega
  · -- m > n case: n is small, so ANY string satisfies the conditions trivially.
    have h_n_lt_M : n < logSlack C_M n := by
      have h1 : n < m := not_le.mp hmn
      exact lt_of_lt_of_le h1 hM_le
    let x := List.replicate n false
    have hx_len : x.length = n := List.length_replicate
    have hkpx_enat : KPPlain U x ≤ ((n + 2 * (Nat.bits n).length + c_len : ℕ) : ENat) := by
      have := h_len x
      rw [hx_len] at this
      have h_eq : (↑n + 2 * ↑(Nat.bits n).length + ↑c_len : ENat) = ↑(n + 2 * (Nat.bits n).length + c_len) := by push_cast; ring
      rw [h_eq] at this
      exact this
    have hx_ne_top : KPPlain U x ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hkpx_enat
    obtain ⟨kx, hkx⟩ : ∃ kx : ℕ, KPPlain U x = (kx : ENat) :=
      ⟨(KPPlain U x).toNat, (ENat.coe_toNat hx_ne_top).symm⟩
    have hkpx : kx ≤ n + 2 * (Nat.bits n).length + c_len := by
      rw [hkx] at hkpx_enat
      exact_mod_cast hkpx_enat
    have hn_bound := hn_small_bound h_n_lt_M
    have hkpx_le_c : kx ≤ logSlack c n := by omega
    refine ⟨x, hx_len, ?_, ?_, ?_⟩
    · rw [hkx]; exact_mod_cast (by omega : kx ≤ k + logSlack c n)
    · rw [hkx]; exact_mod_cast (by omega : k ≤ kx + logSlack c n)
    · intro i j _ _
      exact_mod_cast (by omega : n ≤ i + j + logSlack c n)

/-- Gate H2 (proved): profile-level restatement of non-stochastic existence
(Shen, article Proposition `existence-nonstochastic`(1)).  If `2α + β < n − O(log n)`
then some `n`-bit string is not `(α, β)`-stochastic.  This is exactly the already
proved `first_nonstochastic_existence`; the two `IsNonStochastic` definitions
(`Stochasticity` vs `CodedFiniteDistribution`) are definitionally equal, so the
theorem transports verbatim into the profile-realization layer. -/
theorem exists_nonstochastic_of_profile (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n alpha beta : ℕ,
      2 * alpha + beta + c * (Nat.bits n).length < n →
      ∃ x : BitString, x.length = n ∧ IsNonStochastic U x alpha beta :=
  first_nonstochastic_existence U hU

end Kolmogorov
