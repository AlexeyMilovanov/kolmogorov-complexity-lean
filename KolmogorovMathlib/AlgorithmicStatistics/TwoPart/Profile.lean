/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Deficiencies
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.Complexity.Incompressibility
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.UpperLower.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.Selector

/-!
# Description Profiles and Structure Functions

This file packages two-part description profiles as upper sets and proves the
basic structure-function frontier statements used by the Section 3 realization
modules.
-/

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

def decodeElement (t : BitString) : BitString :=
  let S_code := decodeFirst t
  let z := decodeSecond t
  let blockIdx := bitsToNat z
  let L := (decodeDistributionData S_code).map CodedDistributionEntry.point
  (L.drop blockIdx).headI

theorem decodeElement_computable : Computable decodeElement := by
  have hd : Primrec (fun t : BitString =>
      ((decodeDistributionData (decodeFirst t)).map CodedDistributionEntry.point).drop
        (bitsToNat (decodeSecond t))) := by
    have h_drop : Primrec₂ (fun (l : List BitString) (n : ℕ) => l.drop n) := by
      have h : (fun (l : List BitString) (n : ℕ) => l.drop n) = fun l n => Nat.rec l (fun _ ih => ih.tail) n := by
        funext l n; induction n with | zero => rfl | succ n ih => rw [← List.tail_drop, ih]
      rw [h]; exact Primrec.nat_rec' Primrec.snd Primrec.fst (Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd)).to₂
    have h_L : Primrec (fun t : BitString => (decodeDistributionData (decodeFirst t)).map CodedDistributionEntry.point) :=
      Primrec.list_map (decodeDistributionData_primrec.comp decodeFirst_primrec) (entry_point_primrec.comp Primrec.snd).to₂
    have h_idx : Primrec (fun t : BitString => bitsToNat (decodeSecond t)) :=
      bitsToNat_primrec.comp decodeSecond_primrec
    exact h_drop.comp h_L h_idx
  exact ((Primrec.list_headI.comp hd).of_eq (fun _ => rfl)).to_comp

theorem decodeElement_eq (S : Finset BitString) (hS : S.Nonempty) (x : BitString) (hx : x ∈ S) (j : ℕ) :
    let blockIdx := (canonicalFinsetList S).findIdx (· == x)
    let z := chunkAddress blockIdx j
    decodeElement (pairCode (codedUniformOn S hS).code z) = x := by
  intro blockIdx z
  unfold decodeElement
  simp only [decodeFirst_pairCode, decodeSecond_pairCode]
  have h_data : (decodeDistributionData (codedUniformOn S hS).code).map CodedDistributionEntry.point = canonicalFinsetList S :=
    dataPoints_codedUniformOn S hS
  rw [h_data]
  have h_idx : bitsToNat z = blockIdx := bitsToNat_chunkAddress _ _
  rw [h_idx]
  have h_mem : x ∈ canonicalFinsetList S := mem_canonicalFinsetList.mpr hx
  have h_idx_val : blockIdx < (canonicalFinsetList S).length := by
    dsimp [blockIdx]
    rw [List.findIdx_lt_length]; exact ⟨x, h_mem, by simp⟩
  have h_drop : ((canonicalFinsetList S).drop blockIdx) = (canonicalFinsetList S)[blockIdx] :: ((canonicalFinsetList S).drop (blockIdx + 1)) := by
    apply List.drop_eq_getElem_cons
  rw [h_drop]
  have h_get : (canonicalFinsetList S)[blockIdx] = x := by
    dsimp [blockIdx]
    exact eq_of_beq (List.findIdx_getElem (xs := canonicalFinsetList S) (p := (· == x)))
  rw [h_get]
  rfl

/-- The description profile as an explicit up-set in the `(complexity, log-size)` plane. -/
def descriptionProfileSet (U : Map) (x : BitString) : Set (ℕ × ℕ) :=
  { p | InDescriptionProfile U x p.1 p.2 }

/-- The structure function `h_x(i) = least log-size of an `(i, ·)`-description of `x`
(`⊤` if none, but for `i ≥ K(x)` a singleton makes it finite). -/
noncomputable def structureFunction (U : Map) (x : BitString) (i : ℕ) : ℕ∞ :=
  ⨅ j ∈ { j | InDescriptionProfile U x i j }, (j : ℕ∞)

/-- Curve admissibility (A1)–(A5) *as originally stated by a previous pass*.

**Warning (mathematically flawed – kept only to document the fix).**  This
predicate is **unsatisfiable**: no `h : ℕ → ℕ` can meet all five fields at once, so
any `∃ h, AdmissibleCurve n h` claim (e.g. the old `profile_is_admissible`, now
commented out below) is false.  See `AdmissibleCurve_unsatisfiable`.

The defect is the interaction of `antitone` + `bottom` + `sufficient`: `bottom`
gives a zero `k₀`, `antitone` propagates it to `k₀ + 1`, and `sufficient` at
`i := k₀`, `k := k₀ + 1` then demands `k₀ + 1 ≤ k₀`.  The intended `sufficient`
(sufficiency line `i + h_x(i) ≥ K(x) - O(log)`) must be quantified at the *minimal*
zero (or over `i ≤` that zero) and carry logarithmic slack, not universally over
all zeros `k`.  Independently, `slope` ("the log-size drops by at most one per unit
of complexity budget") is **not** a universal property of structure functions:
non-stochastic strings (cf. `NonStochastic.lean`) have arbitrarily steep drops, so
no slope-≤1 curve can stay within a fixed `logSlack` band of such a structure
function.  The corrected, provable Section-3 statement is
`structureFunction_admissible` below, phrased directly on `structureFunction`. -/
structure AdmissibleCurve (n : ℕ) (h : ℕ → ℕ) : Prop where
  antitone   : ∀ i, h (i + 1) ≤ h i                         -- (A1)
  top        : h 0 ≤ n                                       -- (A2a)
  bottom     : ∃ k ≤ n, h k = 0                              -- (A2b)
  slope      : ∀ i, h i ≤ h (i + 1) + 1                      -- (A3)
  sufficient : ∀ i k, h k = 0 → k ≤ i + h i                  -- (A4)

/-- The `AdmissibleCurve` predicate above is unsatisfiable, so the earlier
`profile_is_admissible` (which asserted such a curve exists) was false as stated.
Proof: a zero of `h` (from `bottom`) is propagated one step by `antitone`, and
`sufficient` applied to those two points forces `k₀ + 1 ≤ k₀`. -/
theorem AdmissibleCurve_unsatisfiable (n : ℕ) : ¬ ∃ h : ℕ → ℕ, AdmissibleCurve n h := by
  rintro ⟨h, hac⟩
  obtain ⟨k0, _, hk0⟩ := hac.bottom
  have h1 : h (k0 + 1) = 0 := Nat.le_zero.mp (hk0 ▸ hac.antitone k0)
  have h2 := hac.sufficient k0 (k0 + 1) h1
  omega

/-- Gate A: Two-part description upper bound `KP(x) ≤ i + j + O(log n)`.

Proof idea: unfold `InDescriptionProfile` to a witness set
`S ∋ x` with `setComplexity U S ≤ i` and `S.card ≤ 2^j`.  A two-part description of
`x` is the code of `S` (length `≤ i`) followed by the `⌈log |S|⌉ ≤ j`-bit index of
`x` inside the canonical enumeration of `S`; decoding runs the set decoder and
selects that index.  Hence `KP(x) ≤ i + j + O(log(i + j))`, and enlarging the slack
argument to `n + i + j` only weakens the bound.  This is the standard
two-part-code inequality, the upper companion of the profile lower bound
`i + h_x(i) ≥ KP(x) − O(log n)`. -/
theorem KPPlain_le_of_inDescriptionProfile (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j : ℕ),
      x.length = n →
      InDescriptionProfile U x i j →
      KPPlain U x ≤ (i + j + logSlack c (n + i + j) : ENat) := by
  obtain ⟨c_map, hc_map⟩ := KPPlain_map_le U hU decodeElement decodeElement_computable
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  let c := c_map + c_pair + c_len + 2
  use c
  intro x n i j hn hprof
  obtain ⟨S, hS, hx, hcomp, hcard⟩ := hprof
  have h_dec := decodeElement_eq S hS x hx j
  let blockIdx := (canonicalFinsetList S).findIdx (· == x)
  let z := chunkAddress blockIdx j
  have hz_len : z.length = j := by
    have h_lt : blockIdx < 2^j := by
      calc blockIdx < (canonicalFinsetList S).length := by
            dsimp [blockIdx]
            rw [List.findIdx_lt_length]; exact ⟨x, mem_canonicalFinsetList.mpr hx, by simp⟩
        _ = S.card := length_canonicalFinsetList S
        _ ≤ 2^j := hcard
    exact chunkAddress_length blockIdx j h_lt
  have h_z_plain : KPPlain U z ≤ (j : ENat) + 2 * (Nat.bits j).length + c_len := by
    have h := hc_len z
    rw [hz_len] at h
    exact h
  calc KPPlain U x = KPPlain U (decodeElement (pairCode (codedUniformOn S hS).code z)) := by rw [h_dec]
    _ ≤ KPPlain U (pairCode (codedUniformOn S hS).code z) + c_map := hc_map _
    _ = KPPair U (codedUniformOn S hS).code z + c_map := by rw [KPPlain_eq_KP, KPPair_eq_KP_pairCode]
    _ ≤ (KPPlain U (codedUniformOn S hS).code + KPPlain U z + c_pair) + c_map := by
        gcongr
        exact hc_pair _ _
    _ ≤ ((i : ENat) + KPPlain U z + c_pair) + c_map := by
        gcongr
        exact hcomp
    _ ≤ ((i : ENat) + ((j : ENat) + 2 * (Nat.bits j).length + c_len) + c_pair) + c_map := by
        gcongr
    _ = ((i + j + 2 * (Nat.bits j).length + c_len + c_pair + c_map : ℕ) : ENat) := by push_cast; ring
    _ ≤ (i + j + logSlack c (n + i + j) : ENat) := by
        have h_mono : (Nat.bits j).length ≤ (Nat.bits (n + i + j)).length :=
          length_natBits_mono (by omega)
        have h_c : c = c_map + c_pair + c_len + 2 := rfl
        have h_le : i + j + 2 * (Nat.bits j).length + c_len + c_pair + c_map ≤ i + j + logSlack c (n + i + j) := by
          unfold logSlack
          nlinarith
        exact_mod_cast h_le

/-- Gate B1: The set complexity of a singleton `{x}` is bounded by its plain complexity. -/
def SingletonSetComplexityGate (U : Map) : Prop :=
  ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ),
    x.length = n →
    KPPlain U x = (kx : ENat) →
    setComplexity U {x} (Finset.singleton_nonempty x) ≤ (kx + logSlack c n : ENat)

/-- Gate B2: The set complexity of the full length-n cube is bounded by O(log n). -/
def FullSetComplexityGate (U : Map) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ) (hn : (stringsOfLength n).Nonempty),
    setComplexity U (stringsOfLength n) hn ≤ (logSlack c n : ENat)

/- **Admissibility Note:** The corrected Section-3 statement, phrased directly
on `structureFunction`, is `structureFunction_admissible` at the end of this file. -/

theorem descriptionProfileSet_isUpperSet (U : Map) (x : BitString) :
    IsUpperSet (descriptionProfileSet U x) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hle h_in
  exact InDescriptionProfile.mono_j hle.2 (InDescriptionProfile.mono_i hle.1 h_in)

theorem mem_descriptionProfileSet_singleton (U : Map) (h_gate : SingletonSetComplexityGate U) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain U x = (kx : ENat) →
      (kx + logSlack c n, 0) ∈ descriptionProfileSet U x := by
  rcases h_gate with ⟨c, hc⟩
  refine ⟨c, fun x n kx hn hk => ?_⟩
  unfold descriptionProfileSet InDescriptionProfile
  simp only [Set.mem_setOf_eq]
  refine ⟨{x}, Finset.singleton_nonempty x, Finset.mem_singleton.mpr rfl, ?_, ?_⟩
  · exact hc x n kx hn hk
  · norm_num

theorem mem_descriptionProfileSet_full (U : Map) (h_gate : FullSetComplexityGate U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ), x.length = n →
      (logSlack c n, n) ∈ descriptionProfileSet U x := by
  rcases h_gate with ⟨c, hc⟩
  refine ⟨c, fun x n hn => ?_⟩
  unfold descriptionProfileSet InDescriptionProfile
  simp only [Set.mem_setOf_eq]
  have h_mem : x ∈ stringsOfLength n := (memStringsOfLength n x).mpr hn
  have hn_nonempty : (stringsOfLength n).Nonempty := ⟨x, h_mem⟩
  refine ⟨stringsOfLength n, hn_nonempty, h_mem, ?_, ?_⟩
  · exact hc n hn_nonempty
  · exact le_of_eq (cardStringsOfLength n)

theorem structureFunction_antitone (U : Map) (x : BitString) :
    Antitone (structureFunction U x) := by
  -- Enlarging the complexity budget `i` can only enlarge the set of admissible
  -- log-sizes (`InDescriptionProfile.mono_i`), so the infimum over that set drops.
  intro i i' hii
  exact biInf_mono (fun _ hj => InDescriptionProfile.mono_i hii hj)

theorem inDescriptionProfile_iff_structureFunction_le (U : Map) (x : BitString) (i j : ℕ) :
    InDescriptionProfile U x i j ↔ structureFunction U x i ≤ j := by
  -- For fixed `i` the admissible log-sizes form an up-set in `j` (`mono_j`), so it
  -- is `∅` or `[m, ∞)` with `m = structureFunction U x i`; membership of `j` is then
  -- exactly `m ≤ j`. The `←` direction is proved contrapositively: if `j` is not
  -- admissible every admissible `j'` exceeds `j`, forcing the infimum above `j`.
  unfold structureFunction
  constructor
  · intro h
    apply biInf_le
    exact h
  · intro h
    by_contra hj
    have hlt : (↑(j + 1) : ℕ∞) ≤ ⨅ j' ∈ { j | InDescriptionProfile U x i j }, (j' : ℕ∞) := by
      refine le_iInf₂ (fun j' hj' => ?_)
      have hjj' : j < j' := by
        by_contra hle
        push Not at hle
        exact hj (InDescriptionProfile.mono_j hle hj')
      exact_mod_cast hjj'
    have hcontra : (↑(j + 1) : ℕ∞) ≤ (j : ℕ∞) := hlt.trans h
    have : j + 1 ≤ j := by exact_mod_cast hcontra
    omega

/-- The description profile of `x` is exactly the epigraph of its structure function:
`(i, j)` is a profile point iff `structureFunction U x i ≤ j`.  This is the
article's "the structure function is the lower boundary of the description profile"
view, packaging `inDescriptionProfile_iff_structureFunction_le` at the set level.
Combined with `descriptionProfileSet_isUpperSet` it exhibits `descriptionProfileSet`
as the up-set determined by the antitone boundary `structureFunction`. -/
theorem descriptionProfileSet_eq_epigraph (U : Map) (x : BitString) :
    descriptionProfileSet U x = { p : ℕ × ℕ | structureFunction U x p.1 ≤ (p.2 : ℕ∞) } := by
  ext ⟨i, j⟩
  simp only [descriptionProfileSet, Set.mem_setOf_eq]
  exact inDescriptionProfile_iff_structureFunction_le U x i j

/-- **Gate D1 (proved): structure-function portion / slope ≥ −1.**  The genuine
slope content of the description profile.  If `(i, j)` is a profile point (i.e.
`h_x(i) ≤ j`) and `s ≤ j`, then spending `s + 2·|bits s| + c` extra units of
complexity budget buys a drop of almost `s` in log-size:
`h_x(i + s + 2|bits s| + c) ≤ j − s + 1`.  Instantiating `j := h_x(i)` yields the
article's "slope ≥ −1" property — the structure function decreases by at least
`s − 1` when the budget grows by `s + O(log s)`.  Proof: convert `h_x(i) ≤ j` to a
profile point via `inDescriptionProfile_iff_structureFunction_le`, apply the
chunk-slicing move `inDescriptionProfile_portion`, and convert the resulting profile
point back to a structure-function bound. -/
theorem structureFunction_portion (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (i j s : ℕ),
      structureFunction U x i ≤ (j : ℕ∞) → s ≤ j →
      structureFunction U x (i + s + 2 * (Nat.bits s).length + c)
        ≤ ((j - s + 1 : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := inDescriptionProfile_portion U hU
  refine ⟨c, fun x i j s hij hsj => ?_⟩
  have hprof : InDescriptionProfile U x i j :=
    (inDescriptionProfile_iff_structureFunction_le U x i j).mpr hij
  exact (inDescriptionProfile_iff_structureFunction_le U x _ _).mp (hc x i j s hprof hsj)

theorem structureFunction_eq_zero_of_ge_complexity
    (U : Map) (h_gate : SingletonSetComplexityGate U) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain U x = (kx : ENat) →
      structureFunction U x (kx + logSlack c n) = 0 := by
  -- Once the budget reaches `K(x) + O(log n)` the singleton `{x}` is an admissible
  -- `(·, 0)`-description, so the structure function has already bottomed out at `0`.
  obtain ⟨c, hc⟩ := mem_descriptionProfileSet_singleton U h_gate
  refine ⟨c, fun x n kx hn hk => ?_⟩
  have hmem : InDescriptionProfile U x (kx + logSlack c n) 0 := hc x n kx hn hk
  have hle : structureFunction U x (kx + logSlack c n) ≤ (0 : ℕ) :=
    (inDescriptionProfile_iff_structureFunction_le U x _ 0).mp hmem
  exact le_antisymm (by exact_mod_cast hle) zero_le

/-! ### Corrected Section-3 admissibility (replacing the false `profile_is_admissible`)

The genuine, provable Section-3 statements are phrased directly on the structure
function, avoiding the unsatisfiable `AdmissibleCurve` packaging.  The four true
admissibility facts are: (A1) antitonicity (`structureFunction_antitone`), (A2a) the
full-cube top endpoint, (A2b) the singleton bottom endpoint, and (A4) the
sufficiency-line lower bound.  (The naive slope field (A3) of the old
`AdmissibleCurve` is deliberately omitted: it is not a universal property, cf. the
steep drops of non-stochastic strings; the true slope content is the one-sided
`structureFunction_portion` proved above.) -/

/-- **Sufficiency line (A4).**  If `x` has an `(i, j)`-description (equivalently
`structureFunction U x i ≤ j`) then `K(x) ≤ i + j + O(log(n+i+j))`.  This is the
two-part-code lower bound `KPPlain_le_of_inDescriptionProfile` transported through
`inDescriptionProfile_iff_structureFunction_le`. -/
theorem structureFunction_sufficiency (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j : ℕ),
      x.length = n →
      structureFunction U x i ≤ (j : ℕ∞) →
      KPPlain U x ≤ (i + j + logSlack c (n + i + j) : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_le_of_inDescriptionProfile U hU
  exact ⟨c, fun x n i j hn hij =>
    hc x n i j hn ((inDescriptionProfile_iff_structureFunction_le U x i j).mpr hij)⟩

/-- **Corrected `profile_is_admissible`.**  For an optimal prefix-conditional `U`
(with the two coding gates), the structure function of every length-`n` string `x`
with `K(x) = kx` satisfies, up to logarithmic slack, the four admissibility
properties of the Section-3 description profile:

* (A1) `structureFunction U x` is antitone;
* (A2a) top endpoint: `structureFunction U x (logSlack c n) ≤ n`;
* (A2b) bottom endpoint: `structureFunction U x (kx + logSlack c n) = 0`;
* (A4) sufficiency line: any `(i, j)` profile point obeys `kx ≤ i + j + O(log)`.

This replaces the earlier, false `profile_is_admissible` (see the commented block
and `AdmissibleCurve_unsatisfiable`). -/
theorem structureFunction_admissible (U : Map) (hU : IsOptimalPrefixConditional U)
    (h_single : SingletonSetComplexityGate U) (h_full : FullSetComplexityGate U) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain U x = (kx : ENat) →
      Antitone (structureFunction U x) ∧
      structureFunction U x (logSlack c n) ≤ (n : ℕ∞) ∧
      structureFunction U x (kx + logSlack c n) = 0 ∧
      (∀ i j : ℕ, structureFunction U x i ≤ (j : ℕ∞) →
        kx ≤ i + j + logSlack c (n + i + j)) := by
  obtain ⟨c_full, hfull⟩ := mem_descriptionProfileSet_full U h_full
  obtain ⟨c_bot, hbot⟩ := structureFunction_eq_zero_of_ge_complexity U h_single
  obtain ⟨c_suf, hsuf⟩ := structureFunction_sufficiency U hU
  refine ⟨c_full + c_bot + c_suf, fun x n kx hn hk =>
    ⟨structureFunction_antitone U x, ?_, ?_, ?_⟩⟩
  · -- (A2a) top endpoint
    have hmem : InDescriptionProfile U x (logSlack c_full n) n := hfull x n hn
    have hle : structureFunction U x (logSlack c_full n) ≤ (n : ℕ∞) :=
      (inDescriptionProfile_iff_structureFunction_le U x _ n).mp hmem
    refine le_trans (structureFunction_antitone U x ?_) hle
    unfold logSlack; nlinarith [Nat.zero_le ((Nat.bits n).length)]
  · -- (A2b) bottom endpoint
    have h0 : structureFunction U x (kx + logSlack c_bot n) = 0 := hbot x n kx hn hk
    have hmono : structureFunction U x (kx + logSlack (c_full + c_bot + c_suf) n)
        ≤ structureFunction U x (kx + logSlack c_bot n) :=
      structureFunction_antitone U x (by
        have : logSlack c_bot n ≤ logSlack (c_full + c_bot + c_suf) n := by
          unfold logSlack; nlinarith [Nat.zero_le ((Nat.bits n).length)]
        omega)
    rw [h0] at hmono
    exact le_antisymm hmono zero_le
  · -- (A4) sufficiency line
    intro i j hij
    have hcast : KPPlain U x ≤ (i + j + logSlack c_suf (n + i + j) : ENat) := hsuf x n i j hn hij
    rw [hk] at hcast
    have hnat : kx ≤ i + j + logSlack c_suf (n + i + j) := by exact_mod_cast hcast
    have hmono : logSlack c_suf (n + i + j) ≤ logSlack (c_full + c_bot + c_suf) (n + i + j) := by
      unfold logSlack; nlinarith [Nat.zero_le ((Nat.bits (n + i + j)).length)]
    omega

end Kolmogorov
