import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionSnapshot
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution

/-!
# Section 3: profile endpoints and curve-realization coding gates

This module discharges the two "coding" gates of the Section 3 description-profile
layer and packages the resulting endpoint facts about the description profile
`descriptionProfileSet` / structure function `structureFunction` as unconditional
statements (for an optimal prefix-conditional machine `U`).

The key technical ingredient is that the canonical uniform code of a finite set
is a *computable* function of a computable enumeration of the set.  We isolate
this as `canonicalUniformCodeOfList`, whose computability is inherited from the
Section 2 encoder `codedUniformEncoder_primrec` and whose correctness against
`codedUniformOn` is `canonicalUniformCodeOfList_canonicalFinsetList`.

From this we obtain:

* `singletonSetComplexityGate` (Gate B1): `setComplexity U {x} ≤ K(x) + O(log n)`;
* `fullSetComplexityGate` (Gate B2): `setComplexity U (cube n) ≤ O(log n)`.

These in turn make the profile-endpoint theorems of `Profile.lean` unconditional
(the `_of_optimal` wrappers below), together with a paper-facing wrapper packaging
both halves of the improving-descriptions proposition.
-/

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- The canonical uniform code of a *list* of points, using the exact rational
mass `1 / (max 1 |t|)` at each listed point.  This is definitionally the encoder
proved primitive recursive in `codedUniformEncoder_primrec`, isolated as a named
function so we can feed it computable enumerations of finite sets. -/
noncomputable def canonicalUniformCodeOfList (t : List BitString) : BitString :=
  codedDistributionDataCode (t.map fun x =>
    ({point := x, mass := ratMassInvNat (max 1 t.length) (by positivity)} :
      CodedDistributionEntry))

theorem canonicalUniformCodeOfList_primrec : Primrec canonicalUniformCodeOfList :=
  codedUniformEncoder_primrec

theorem canonicalUniformCodeOfList_computable : Computable canonicalUniformCodeOfList :=
  canonicalUniformCodeOfList_primrec.to_comp

/-
Correctness of the list encoder against `codedUniformOn`: applied to the
canonical sorted enumeration `canonicalFinsetList S` of a nonempty finite set,
it produces exactly the canonical uniform code of `S`.  (The denominator
`max 1 |canonicalFinsetList S|` equals `S.card` because `S` is nonempty.)
-/
theorem canonicalUniformCodeOfList_canonicalFinsetList (S : Finset BitString) (hS : S.Nonempty) :
    canonicalUniformCodeOfList (canonicalFinsetList S) = (codedUniformOn S hS).code := by
  refine congr_arg _ (List.map_congr_left ?_)
  simp_all +decide

/-
**Gate B1.** The set complexity of a singleton `{x}` is bounded by the plain
prefix complexity of `x` up to logarithmic slack.  Proof: the map
`x ↦ canonicalUniformCodeOfList [x]` is computable and equals the code of
`codedUniformOn {x}` (since `canonicalFinsetList {x} = [x]`), so by
`KPPlain_map_le` the code has complexity `≤ K(x) + O(1) ≤ K(x) + logSlack c n`.
-/
theorem singletonSetComplexityGate (U : Map) (hU : IsOptimalPrefixConditional U) :
    SingletonSetComplexityGate U := by
  obtain ⟨ c, hc ⟩ := KPPlain_map_le U hU ( fun x => canonicalUniformCodeOfList [ x ] ) ( by
    exact canonicalUniformCodeOfList_computable.comp
        ( Computable.list_cons.comp Computable.id ( Computable.const [] ) ) );
  refine ⟨c, fun x n kx hn hk => le_trans ?_ (le_trans (hc x) ?_)⟩
  · rw [show setComplexity U {x} _
        = KPPlain U (codedUniformOn {x} _ |> CodedFiniteDistribution.code) from rfl]
    convert le_rfl
    convert canonicalUniformCodeOfList_canonicalFinsetList {x} (Finset.singleton_nonempty x) using 1
    unfold canonicalFinsetList; aesop
  · exact add_le_add hk.le
      (mod_cast by unfold logSlack; nlinarith [Nat.zero_le ((Nat.bits n).length)])

/-
**Gate B2.** The set complexity of the full length-`n` cube is `O(log n)`.
Proof: the map `natCode n ↦ canonicalUniformCodeOfList (canonicalFinsetList
(stringsOfLength n))` is computable (composing `decodeNatCode`, `allStrings`,
`canonicalFinsetList ∘ ·.toFinset`, and the list encoder) and equals the code of
`codedUniformOn (stringsOfLength n)`, so by `KPPlain_map_le` and
`KPPlain_natCode_le_log` its complexity is `≤ 2·|bits n| + O(1) ≤ logSlack c n`.
-/
theorem fullSetComplexityGate (U : Map) (hU : IsOptimalPrefixConditional U) :
    FullSetComplexityGate U := by
  obtain ⟨c₁,
           hc₁⟩ :=KPPlain_map_le U hU (fun w =>
               canonicalUniformCodeOfList
                   (canonicalFinsetList (stringsOfLength (decodeNatCode w)))) (by
  convert canonicalUniformCodeOfList_computable.comp
      ( _ : Computable fun w => canonicalFinsetList ( stringsOfLength ( decodeNatCode w ) ) ) using
          1;
  convert canonicalFinsetList_toFinset_primrec.comp
      ( allStrings_primrec.comp ( decodeNatCode_primrec ) ) |> Primrec.to_comp using 1)
  obtain ⟨c₂, hc₂⟩ :=KPPlain_natCode_le_log U hU
  use c₁ + c₂ + 2;
  intro n hn; specialize hc₁ ( natCode n ) ; specialize hc₂ n; simp_all +decide [ logSlack ] ;
  convert hc₁.trans ( add_le_add hc₂ le_rfl ) |> le_trans <| ?_ using 1;
  · convert rfl using 2;
    convert congr_arg ( fun x : BitString => KP U x [] )
        ( canonicalUniformCodeOfList_canonicalFinsetList ( stringsOfLength n ) hn ) using 1;
  · norm_cast ; nlinarith [ Nat.zero_le ( List.length ( Nat.bits n ) ) ]

/-! ### Unconditional profile endpoints -/

/-- Singleton endpoint of the description profile, unconditional for an optimal
prefix-conditional machine: `(K(x) + O(log n), 0)` lies in the profile of `x`. -/
theorem mem_descriptionProfileSet_singleton_of_optimal
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain U x = (kx : ENat) →
      (kx + logSlack c n, 0) ∈ descriptionProfileSet U x :=
  mem_descriptionProfileSet_singleton U (singletonSetComplexityGate U hU)

/-- Full-cube endpoint of the description profile, unconditional for an optimal
prefix-conditional machine: `(O(log n), n)` lies in the profile of every
length-`n` string. -/
theorem mem_descriptionProfileSet_full_of_optimal
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ), x.length = n →
      (logSlack c n, n) ∈ descriptionProfileSet U x :=
  mem_descriptionProfileSet_full U (fullSetComplexityGate U hU)

/-- Structure function bottoms out at `0` once the budget reaches `K(x) + O(log n)`,
unconditional for an optimal prefix-conditional machine. -/
theorem structureFunction_eq_zero_of_ge_complexity_of_optimal
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain U x = (kx : ENat) →
      structureFunction U x (kx + logSlack c n) = 0 :=
  structureFunction_eq_zero_of_ge_complexity U (singletonSetComplexityGate U hU)

/-- The structure function stays at `0` for *every* budget `i ≥ K(x) + O(log n)`,
not merely at the single threshold point.  This is the article's actual right-tail
statement `h_x(i) = 0` for `i ≥ K(x)` (up to logarithmic slack): once the singleton
`{x}` becomes an admissible `(·, 0)`-description, antitonicity (`structureFunction_antitone`)
keeps the structure function pinned at its floor `0` for all larger budgets. -/
theorem structureFunction_eq_zero_of_ge_of_optimal
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain U x = (kx : ENat) →
      ∀ i, kx + logSlack c n ≤ i → structureFunction U x i = 0 := by
  obtain ⟨c, hc⟩ := structureFunction_eq_zero_of_ge_complexity_of_optimal U hU
  refine ⟨c, fun x n kx hn hk i hi => ?_⟩
  have h0 : structureFunction U x (kx + logSlack c n) = 0 := hc x n kx hn hk
  have hmono : structureFunction U x i ≤ structureFunction U x (kx + logSlack c n) :=
    structureFunction_antitone U x hi
  rw [h0] at hmono
  exact le_antisymm hmono (zero_le _)

/-- Right tail of the description profile, unconditional for an optimal
prefix-conditional machine: for *every* budget `i ≥ K(x) + O(log n)` the zero-log-size
point `(i, 0)` lies in the profile of `x`.  This is the profile-set form of
`structureFunction_eq_zero_of_ge_of_optimal`: once the singleton `{x}` is an
admissible `(·, 0)`-description, it remains one for all larger budgets, so the whole
right ray `{(i, 0) : i ≥ K(x) + O(log n)}` is contained in `descriptionProfileSet U x`.
Combined with `descriptionProfileSet_isUpperSet` this pins the profile's lower
boundary to the axis `j = 0` on its entire right tail. -/
theorem mem_descriptionProfileSet_zero_of_ge_of_optimal
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain U x = (kx : ENat) →
      ∀ i, kx + logSlack c n ≤ i → (i, 0) ∈ descriptionProfileSet U x := by
  obtain ⟨c, hc⟩ := structureFunction_eq_zero_of_ge_of_optimal U hU
  refine ⟨c, fun x n kx hn hk i hi => ?_⟩
  rw [descriptionProfileSet_eq_epigraph, Set.mem_setOf_eq, hc x n kx hn hk i hi]
  simp

/-! ### Paper-facing improving-descriptions wrapper -/

/-- Both halves of the Section 3 improving-descriptions proposition, packaged
together: from `2^k` distinct `(i,j)`-descriptions of `x` one obtains an
`(i-k, j)`-description (complexity half) and an `(i, j-k)`-description (size half),
each up to visible logarithmic slack. -/
theorem improving_descriptions_both (U : Map) (hU : IsOptimalPrefixConditional U) :
    ImprovingDescriptionsComplexityLogSlack U ∧ ImprovingDescriptionsSizeLogSlack U :=
  ⟨exists_description_smaller_complexity_of_many_logSlack U hU,
   exists_description_smaller_size_of_many_logSlack U hU⟩

/-! ### Corrected profile-admissibility endpoint, unconditional for optimal `U` -/

/-- The corrected Section-3 admissibility of the structure function, discharged of
its two coding-gate hypotheses: for an optimal prefix-conditional `U`, every
length-`n` string `x` with `K(x) = kx` has an antitone structure function meeting
the top endpoint (`≤ n` at budget `O(log n)`), the bottom endpoint (`= 0` at budget
`kx + O(log n)`), and the sufficiency line (`kx ≤ i + j + O(log)` on every profile
point).  This is the honest replacement for the (false) `profile_is_admissible`. -/
theorem structureFunction_admissible_of_optimal
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain U x = (kx : ENat) →
      Antitone (structureFunction U x) ∧
      structureFunction U x (logSlack c n) ≤ (n : ℕ∞) ∧
      structureFunction U x (kx + logSlack c n) = 0 ∧
      (∀ i j : ℕ, structureFunction U x i ≤ (j : ℕ∞) →
        kx ≤ i + j + logSlack c (n + i + j)) :=
  structureFunction_admissible U hU (singletonSetComplexityGate U hU) (fullSetComplexityGate U hU)

/-! ### Trivial (prefix-cube) upper bound on the structure function

The structure function of any length-`n` string admits the *diagonal* upper bound
`h_x(i) ≤ n - i + O(log n)`: the prefix cube `{y : y.take i = x.take i}` is a set of
`2^{n-i}` strings, contains `x`, and has set complexity only `i + O(log n)` (it is
computable from the `i`-bit prefix and `n`).  This is the honest upper envelope of the
description profile, complementing the sufficiency-line lower bound of
`structureFunction_admissible_of_optimal`.  It is *gate-free* (does not depend on the
profile/curve realization coverage gate `exists_point_in_all_coverableSets`).  The
result is fully proved in this file. -/

/-- The length-`|p|+m` prefix cube determined by a prefix `p`: all strings `p ++ s`
with `s` of length `m`.  As a finite set it has exactly `2^m` elements. -/
noncomputable def prefixCubeSet (p : BitString) (m : ℕ) : Finset BitString :=
  ((allStrings m).map (fun s => p ++ s)).toFinset

/-- Canonical uniform code of the prefix cube, as a computable function of the
packed input `pairCode p (natCode m)` (via `decodeFirst`/`decodeSecond`). -/
noncomputable def prefixCubeCode (w : BitString) : BitString :=
  canonicalUniformCodeOfList
    (canonicalFinsetList (prefixCubeSet (decodeFirst w) (decodeNatCode (decodeSecond w))))

/-- `prefixCubeCode` is computable: it composes the primitive-recursive enumeration
`allStrings`, list-map with the (computable) prefix append, the canonical
list-of-finset normalizer, and the list encoder, following the `fullSetComplexityGate`
pattern. -/
theorem prefixCubeCode_computable : Computable prefixCubeCode := by
  unfold prefixCubeCode
  have hlist : Primrec (fun w : BitString =>
      (allStrings (decodeNatCode (decodeSecond w))).map (fun s => decodeFirst w ++ s)) := by
    apply Primrec.list_map
      (allStrings_primrec.comp (decodeNatCode_primrec.comp decodeSecond_primrec))
    exact Primrec.list_append.comp (decodeFirst_primrec.comp Primrec.fst) Primrec.snd
  have hfin : Primrec (fun w : BitString =>
      canonicalFinsetList (prefixCubeSet (decodeFirst w) (decodeNatCode (decodeSecond w)))) := by
    have := canonicalFinsetList_toFinset_primrec.comp hlist
    simpa [prefixCubeSet] using this
  exact canonicalUniformCodeOfList_computable.comp hfin.to_comp

/-- The prefix cube has exactly `2^m` elements: `p ++ ·` is injective and `allStrings m`
is a duplicate-free enumeration of the `2^m` strings of length `m`. -/
theorem prefixCubeSet_card (p : BitString) (m : ℕ) : (prefixCubeSet p m).card = 2 ^ m := by
  unfold prefixCubeSet
  rw [List.toFinset_card_of_nodup]
  · rw [List.length_map, length_allStrings]
  · exact (allStrings_nodup m).map (fun a b h => List.append_cancel_left h)

/-- The prefix cube is nonempty. -/
theorem prefixCubeSet_nonempty (p : BitString) (m : ℕ) : (prefixCubeSet p m).Nonempty := by
  rw [← Finset.card_pos, prefixCubeSet_card]
  positivity

/-- A length-`n` string lies in the prefix cube of its own length-`i` prefix (with
`m = n - i`), since `x = x.take i ++ x.drop i` and `x.drop i` has length `n - i`. -/
theorem mem_prefixCubeSet (x : BitString) (n i : ℕ) (hn : x.length = n) :
    x ∈ prefixCubeSet (x.take i) (n - i) := by
  unfold prefixCubeSet
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨x.drop i, by rw [mem_allStrings, List.length_drop, hn], List.take_append_drop i x⟩

/-
The trivial upper envelope of the description profile: for every length-`n`
string `x` and budget `i ≤ n`, the prefix cube `{y : y.take i = x.take i}` is an
`(i + O(log n), n - i)`-description of `x`.  Hence `h_x(i + O(log n)) ≤ n - i`, the
diagonal upper bound complementing the sufficiency-line lower bound.  Gate-free.
-/
theorem structureFunction_prefix_upper_of_optimal (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n i : ℕ), x.length = n → i ≤ n →
      InDescriptionProfile U x (i + logSlack c n) (n - i) := by
  obtain ⟨c_map, hc_map⟩ := KPPlain_map_le U hU prefixCubeCode prefixCubeCode_computable
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_nat, hc_nat⟩ := KPPlain_natCode_le_log U hU
  refine ⟨c_len + c_nat + c_pair + c_map + 4, fun x n i hn hi => ?_⟩
  set p := x.take i with hp
  set m := n - i with hm
  set S := prefixCubeSet p m with hSdef
  have hSne : S.Nonempty := prefixCubeSet_nonempty p m
  refine ⟨S, hSne, mem_prefixCubeSet x n i hn, ?_, ?_⟩
  · -- Complexity bound: the cube is describable from the `i`-bit prefix and `n`.
    have hcode : (codedUniformOn S hSne).code = prefixCubeCode (pairCode p (natCode m)) := by
      rw [prefixCubeCode]
      simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeNatCode_natCode]
      exact (canonicalUniformCodeOfList_canonicalFinsetList S hSne).symm
    have hsc : setComplexity U S hSne = KPPlain U (prefixCubeCode (pairCode p (natCode m))) := by
      rw [setComplexity, hcode]
    have hplen : p.length = i := by rw [hp, List.length_take, hn, Nat.min_eq_left hi]
    have hLi : (Nat.bits i).length ≤ (Nat.bits n).length := length_natBits_mono hi
    have hLm : (Nat.bits m).length ≤ (Nat.bits n).length := length_natBits_mono (by rw [hm]; omega)
    have harith :
        i + 2 * (Nat.bits i).length + c_len + (2 * (Nat.bits m).length + c_nat) + c_pair + c_map
          ≤ i + logSlack (c_len + c_nat + c_pair + c_map + 4) n := by
      unfold logSlack; nlinarith [hLi, hLm, Nat.zero_le ((Nat.bits n).length)]
    calc setComplexity U S hSne
        = KPPlain U (prefixCubeCode (pairCode p (natCode m))) := hsc
      _ ≤ KPPlain U (pairCode p (natCode m)) + (c_map : ENat) := hc_map _
      _ ≤ (KPPlain U p + KPPlain U (natCode m) + (c_pair : ENat)) + (c_map : ENat) := by
          gcongr; exact hc_pair p (natCode m)
      _ ≤ ((p.length + 2 * (Nat.bits p.length).length + (c_len : ENat))
            + (2 * (Nat.bits m).length + (c_nat : ENat)) + (c_pair : ENat)) + (c_map : ENat) := by
          gcongr; exacts [hc_len p, hc_nat m]
      _ = ((i + 2 * (Nat.bits i).length + c_len + (2 * (Nat.bits m).length + c_nat)
              + c_pair + c_map : ℕ) : ENat) := by rw [hplen]; push_cast; ring
      _ ≤ ((i + logSlack (c_len + c_nat + c_pair + c_map + 4) n : ℕ) : ENat) := by
          exact_mod_cast harith
  · -- Size bound: the cube has exactly `2^(n-i)` elements.
    rw [hSdef]; exact le_of_eq (prefixCubeSet_card p m)

/-- Structure-function form of the prefix-cube upper bound: for every length-`n`
string `x` and budget `i ≤ n`, `h_x(i + O(log n)) ≤ n - i`.  This is the diagonal
upper envelope of the Kolmogorov structure function, the companion of the
sufficiency-line lower bound in `structureFunction_admissible_of_optimal`.  Gate-free. -/
theorem structureFunction_le_length_sub_of_optimal (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n i : ℕ), x.length = n → i ≤ n →
      structureFunction U x (i + logSlack c n) ≤ ((n - i : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := structureFunction_prefix_upper_of_optimal U hU
  exact ⟨c, fun x n i hn hi =>
    (inDescriptionProfile_iff_structureFunction_le U x _ _).mp (hc x n i hn hi)⟩

end Kolmogorov
