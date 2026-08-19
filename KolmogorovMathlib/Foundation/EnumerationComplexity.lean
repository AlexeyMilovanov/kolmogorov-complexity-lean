import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution

/-!
# Complexity via computable enumerations

The single most-used informal step of VS40 §6: *"the selected set can be
described by its ordinal number in an enumeration, so its complexity is
≤ log₂(index) + O(1)"*. The same move exists ad hoc in
`TwoPart/GapCounting.lean` (`candidateCodes`, `appearanceListCodes`,
`indexSelectorFn`, `code_mem_appearanceListCodes`).  The construction here
packages that argument for reuse.  Constants are per enumeration (the
enumeration is a fixed computable object, as in `KPPlain_map_le`); the
conditional variant also carries the context `y`.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- A staged computable enumeration of bitstrings: `enum t` is the finite
list produced within `t` steps, prefix-monotone in `t` (repetitions allowed;
distinctness is handled by `distinctAt`). -/
structure StagedEnumeration where
  enum : ℕ → List BitString
  computable : Computable enum
  mono : ∀ t, enum t <+: enum (t + 1)

namespace StagedEnumeration

/-- The distinct enumerated strings at stage `t`, in order of first
appearance. -/
def distinctAt (E : StagedEnumeration) (t : ℕ) : List BitString :=
  (E.enum t).eraseDups

/-- Stability: once an element has an index in `distinctAt`, later stages
preserve that index (prefix-monotonicity survives `eraseDups`). -/
theorem distinctAt_mono (E : StagedEnumeration) (t : ℕ) :
    E.distinctAt t <+: E.distinctAt (t + 1) := by
  obtain ⟨l, hl⟩ := E.mono t
  dsimp [distinctAt]
  rw [← hl, List.eraseDups_append]
  exact List.prefix_append _ _

theorem prefix_of_le (E : StagedEnumeration) {t1 t2 : ℕ} (hle : t1 ≤ t2) :
    E.distinctAt t1 <+: E.distinctAt t2 := by
  induction hle with
  | refl => exact List.prefix_refl _
  | step ht ih => exact List.IsPrefix.trans ih (distinctAt_mono E _)

/-- Extractor function. -/
def F (E : StagedEnumeration) : BitString →. BitString := fun w =>
  let k := w.length - 1
  (Nat.rfind (fun t => Part.some (decide (k < (E.distinctAt t).length)))).bind
    (fun t => Part.some ((E.distinctAt t).getD k []))

theorem F_partrec (E : StagedEnumeration) : Partrec (F E) := by
  have hk : Computable (fun (p : BitString × ℕ) => p.1.length - 1) :=
    Computable.pred.comp (Computable.list_length.comp Computable.fst)
  have hc : Computable (fun (p : BitString × ℕ) => E.enum p.2) :=
    E.computable.comp Computable.snd
  have h_distinctAt : Computable (fun (p : BitString × ℕ) => E.distinctAt p.2) :=
    eraseDups_bitstring_primrec.to_comp.comp hc
  have hl : Computable (fun (p : BitString × ℕ) => (E.distinctAt p.2).length) :=
    Computable.list_length.comp h_distinctAt
  have h_lt : Computable₂ (fun a b : ℕ => decide (a < b)) :=
    (PrimrecPred.decide Primrec.nat_lt).to_comp
  have h_check : Computable₂
      (fun (w : BitString) (t : ℕ) => decide (w.length - 1 < (E.distinctAt t).length)) :=
    h_lt.comp hk hl
  have h_getD : Computable₂ (fun (l : List BitString) (n : ℕ) => l.getD n []) :=
    (Primrec.list_getD []).to_comp
  have h_post : Computable₂
      (fun (w : BitString) (t : ℕ) => (E.distinctAt t).getD (w.length - 1) []) :=
    h_getD.comp h_distinctAt hk
  exact Partrec.bind (Partrec.rfind h_check.partrec₂) h_post.partrec₂

theorem getD_eq_of_prefix {α} (l1 l2 : List α) (h : l1 <+: l2) (k : ℕ) (d : α) (hk : k < l1.length)
    :
    l2.getD k d = l1.getD k d := by
  obtain ⟨r, rfl⟩ := h
  exact List.getD_append l1 r d k hk

theorem F_eval (E : StagedEnumeration) (t k : ℕ) (hk : k < (E.distinctAt t).length) :
    ((E.distinctAt t).getD k []) ∈ F E (natCode k) := by
  unfold F
  have hlen : (natCode k).length - 1 = k := by
    simp [length_natCode]
  simp only [hlen]
  rw [Part.mem_bind_iff]
  let h_exists : ∃ t', k < (E.distinctAt t').length := ⟨t, hk⟩
  let t0 := Nat.find h_exists
  refine ⟨t0, ?_, ?_⟩
  · refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · simpa using Nat.find_spec h_exists
    · intro m hm
      have hnot := Nat.find_min h_exists hm
      simp [hnot]
  · have ht0 : k < (E.distinctAt t0).length := Nat.find_spec h_exists
    have ht0_le_t : t0 ≤ t :=
      Nat.find_le (p := fun t' => k < (E.distinctAt t').length) hk
    have hpre : E.distinctAt t0 <+: E.distinctAt t := prefix_of_le E ht0_le_t
    have hget := getD_eq_of_prefix (E.distinctAt t0) (E.distinctAt t) hpre k [] ht0
    simpa [hget]

def condDistinctAt (enum : BitString → ℕ → List BitString)
    (y : BitString) (t : ℕ) : List BitString :=
  (enum y t).eraseDups

theorem condDistinctAt_mono (enum : BitString → ℕ → List BitString)
    (hmono : ∀ y t, enum y t <+: enum y (t + 1)) (y : BitString) (t : ℕ) :
    condDistinctAt enum y t <+: condDistinctAt enum y (t + 1) := by
  obtain ⟨l, hl⟩ := hmono y t
  dsimp [condDistinctAt]
  rw [← hl, List.eraseDups_append]
  exact List.prefix_append _ _

theorem condPrefix_of_le (enum : BitString → ℕ → List BitString)
    (hmono : ∀ y t, enum y t <+: enum y (t + 1))
    (y : BitString) {t1 t2 : ℕ} (hle : t1 ≤ t2) :
    condDistinctAt enum y t1 <+: condDistinctAt enum y t2 := by
  induction hle with
  | refl => exact List.prefix_refl _
  | step ht ih => exact List.IsPrefix.trans ih (condDistinctAt_mono enum hmono y _)

/-- Conditional extractor: from context `y` and unary index code `w`, return the
corresponding distinct element of the staged enumeration depending on `y`. -/
def condF (enum : BitString → ℕ → List BitString) :
    BitString → BitString →. BitString := fun y w =>
  let k := w.length - 1
  (Nat.rfind (fun t => Part.some (decide (k < (condDistinctAt enum y t).length)))).bind
    (fun t => Part.some ((condDistinctAt enum y t).getD k []))

theorem condF_partrec (enum : BitString → ℕ → List BitString)
    (henum : Computable fun p : BitString × ℕ => enum p.1 p.2) :
    Partrec (fun p : BitString × BitString => condF enum p.2 p.1) := by
  have hk : Computable (fun (p : (BitString × BitString) × ℕ) => p.1.1.length - 1) :=
    Computable.pred.comp (Computable.list_length.comp (Computable.fst.comp Computable.fst))
  have hc : Computable (fun (p : (BitString × BitString) × ℕ) => enum p.1.2 p.2) :=
    henum.comp (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)
  have h_distinctAt : Computable (fun (p : (BitString × BitString) × ℕ) =>
      condDistinctAt enum p.1.2 p.2) :=
    eraseDups_bitstring_primrec.to_comp.comp hc
  have hl : Computable (fun (p : (BitString × BitString) × ℕ) =>
      (condDistinctAt enum p.1.2 p.2).length) :=
    Computable.list_length.comp h_distinctAt
  have h_lt : Computable₂ (fun a b : ℕ => decide (a < b)) :=
    (PrimrecPred.decide Primrec.nat_lt).to_comp
  have h_check : Computable₂ (fun (p : BitString × BitString) (t : ℕ) =>
      decide (p.1.length - 1 < (condDistinctAt enum p.2 t).length)) :=
    h_lt.comp hk hl
  have h_getD : Computable₂ (fun (l : List BitString) (n : ℕ) => l.getD n []) :=
    (Primrec.list_getD []).to_comp
  have h_post : Computable₂ (fun (p : BitString × BitString) (t : ℕ) =>
      (condDistinctAt enum p.2 t).getD (p.1.length - 1) []) :=
    h_getD.comp h_distinctAt hk
  exact Partrec.bind (Partrec.rfind h_check.partrec₂) h_post.partrec₂

theorem condF_eval (enum : BitString → ℕ → List BitString)
    (hmono : ∀ y t, enum y t <+: enum y (t + 1))
    (y : BitString) (t k : ℕ) (hk : k < (condDistinctAt enum y t).length) :
    ((condDistinctAt enum y t).getD k []) ∈ condF enum y (natCode k) := by
  unfold condF
  have hlen : (natCode k).length - 1 = k := by
    simp [length_natCode]
  simp only [hlen]
  rw [Part.mem_bind_iff]
  let h_exists : ∃ t', k < (condDistinctAt enum y t').length := ⟨t, hk⟩
  let t0 := Nat.find h_exists
  refine ⟨t0, ?_, ?_⟩
  · refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · simpa using Nat.find_spec h_exists
    · intro m hm
      have hnot := Nat.find_min h_exists hm
      simp [hnot]
  · have ht0 : k < (condDistinctAt enum y t0).length := Nat.find_spec h_exists
    have ht0_le_t : t0 ≤ t :=
      Nat.find_le (p := fun t' => k < (condDistinctAt enum y t').length) hk
    have hpre : condDistinctAt enum y t0 <+: condDistinctAt enum y t :=
      condPrefix_of_le enum hmono y ht0_le_t
    have hget := getD_eq_of_prefix (condDistinctAt enum y t0)
      (condDistinctAt enum y t) hpre k [] ht0
    simpa [hget]

/-- **M0 core (plain form).** The `k`-th distinct enumerated string has
prefix complexity at most `2·|bits k| + O(1)`; the constant depends only on
the enumeration `E` and the machine `U`. -/
theorem KPPlain_le_log_index_of_enumeration (U : Map)
    (hU : IsOptimalPrefixConditional U) (E : StagedEnumeration) :
    ∃ c : ℕ, ∀ (t k : ℕ),
      k < (E.distinctAt t).length →
      KPPlain U ((E.distinctAt t).getD k []) ≤
        2 * (Nat.bits k).length + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_partrec_map_le U hU (F E) (F_partrec E)
  obtain ⟨c_log, hc_log⟩ := KPPlain_natCode_le_log U hU
  refine ⟨c + c_log, fun t k hk => ?_⟩
  have h_eval := F_eval E t k hk
  calc KPPlain U ((E.distinctAt t).getD k [])
      ≤ KPPlain U (natCode k) + (c : ENat) := hc _ _ h_eval
    _ ≤ 2 * (Nat.bits k).length + (c_log : ENat) + (c : ENat) := add_le_add (hc_log k) le_rfl
    _ = 2 * (Nat.bits k).length + ((c + c_log : ℕ) : ENat) := by push_cast; ring

/-- **M0 core (conditional form).** Same bound for enumerations whose stage
lists depend computably on a context `y`; the index bound holds given `y`. -/
theorem KP_le_log_index_of_cond_enumeration (U : Map)
    (hU : IsOptimalPrefixConditional U)
    (enum : BitString → ℕ → List BitString)
    (henum : Computable fun p : BitString × ℕ => enum p.1 p.2)
    (hmono : ∀ y t, enum y t <+: enum y (t + 1)) :
    ∃ c : ℕ, ∀ (y : BitString) (t k : ℕ),
      k < ((enum y t).eraseDups).length →
      KP U (((enum y t).eraseDups).getD k []) y ≤
        2 * (Nat.bits k).length + (c : ENat) := by
  obtain ⟨c_map, hc_map⟩ :=
    KP_partrec_cond_first_map_le U hU (condF enum) (condF_partrec enum henum)
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_log, hc_log⟩ := KPPlain_natCode_le_log U hU
  refine ⟨c_map + c_plain + c_log, fun y t k hk => ?_⟩
  have h_eval : (((enum y t).eraseDups).getD k []) ∈ condF enum y (natCode k) := by
    exact condF_eval enum hmono y t k hk
  calc KP U (((enum y t).eraseDups).getD k []) y
      ≤ KP U (natCode k) y + (c_map : ENat) := hc_map (natCode k) _ y h_eval
    _ ≤ KPPlain U (natCode k) + (c_plain : ENat) + (c_map : ENat) := by
          gcongr
          exact hc_plain (natCode k) y
    _ ≤ (2 * (Nat.bits k).length + (c_log : ENat)) + (c_plain : ENat) + (c_map : ENat) := by
          gcongr
          exact hc_log k
    _ = 2 * (Nat.bits k).length + ((c_map + c_plain + c_log : ℕ) : ENat) := by
          push_cast
          ring

/-- **M0 for set codes.** If the enumeration produces canonical uniform codes
of finite sets, the `k`-th distinct enumerated set has `setComplexity` at
most `2·|bits k| + O(1)`. (Bridge form used by the restricted-family theory;
derive from `KPPlain_le_log_index_of_enumeration`.) -/
theorem setComplexity_le_log_index_of_enumeration (U : Map)
    (hU : IsOptimalPrefixConditional U) (E : StagedEnumeration) :
    ∃ c : ℕ, ∀ (t k : ℕ) (S : Finset BitString) (hS : S.Nonempty),
      k < (E.distinctAt t).length →
      (E.distinctAt t).getD k [] = (codedUniformOn S hS).code →
      setComplexity U S hS ≤ 2 * (Nat.bits k).length + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_le_log_index_of_enumeration U hU E
  refine ⟨c, fun t k S hS hk heq => ?_⟩
  have hk_eval := hc t k hk
  rw [heq] at hk_eval
  exact hk_eval

/-- Fixed-length conditional extractor: from context `y` and a fixed-length index code `z`,
return the corresponding distinct element of the staged enumeration. -/
def condFFixedLength (enum : BitString → ℕ → List BitString) :
    BitString → BitString →. BitString := fun y z =>
  let k := bitsToNat z
  (Nat.rfind (fun t => Part.some (decide (k < (condDistinctAt enum y t).length)))).bind
    (fun t => Part.some ((condDistinctAt enum y t).getD k []))

theorem condFFixedLength_partrec (enum : BitString → ℕ → List BitString)
    (henum : Computable fun p : BitString × ℕ => enum p.1 p.2) :
    Partrec (fun p : BitString × BitString => condFFixedLength enum p.2 p.1) := by
  have hk : Computable (fun (p : (BitString × BitString) × ℕ) => bitsToNat p.1.1) :=
    bitsToNat_primrec.to_comp.comp (Computable.fst.comp Computable.fst)
  have hc : Computable (fun (p : (BitString × BitString) × ℕ) => enum p.1.2 p.2) :=
    henum.comp (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)
  have h_distinctAt : Computable (fun (p : (BitString × BitString) × ℕ) =>
      condDistinctAt enum p.1.2 p.2) :=
    eraseDups_bitstring_primrec.to_comp.comp hc
  have hl : Computable (fun (p : (BitString × BitString) × ℕ) =>
      (condDistinctAt enum p.1.2 p.2).length) :=
    Computable.list_length.comp h_distinctAt
  have h_lt : Computable₂ (fun a b : ℕ => decide (a < b)) :=
    (PrimrecPred.decide Primrec.nat_lt).to_comp
  have h_check : Computable₂ (fun (p : BitString × BitString) (t : ℕ) =>
      decide (bitsToNat p.1 < (condDistinctAt enum p.2 t).length)) :=
    h_lt.comp hk hl
  have h_getD : Computable₂ (fun (l : List BitString) (n : ℕ) => l.getD n []) :=
    (Primrec.list_getD []).to_comp
  have h_post : Computable₂ (fun (p : BitString × BitString) (t : ℕ) =>
      (condDistinctAt enum p.2 t).getD (bitsToNat p.1) []) :=
    h_getD.comp h_distinctAt hk
  exact Partrec.bind (Partrec.rfind h_check.partrec₂) h_post.partrec₂

theorem condFFixedLength_eval (enum : BitString → ℕ → List BitString)
    (hmono : ∀ y t, enum y t <+: enum y (t + 1))
    (y z : BitString) (t : ℕ) (hk : bitsToNat z < (condDistinctAt enum y t).length) :
    ((condDistinctAt enum y t).getD (bitsToNat z) []) ∈ condFFixedLength enum y z := by
  unfold condFFixedLength
  rw [Part.mem_bind_iff]
  let k := bitsToNat z
  let h_exists : ∃ t', k < (condDistinctAt enum y t').length := ⟨t, hk⟩
  let t0 := Nat.find h_exists
  refine ⟨t0, ?_, ?_⟩
  · refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · simpa using Nat.find_spec h_exists
    · intro m hm
      have hnot := Nat.find_min h_exists hm
      simpa [k] using hnot
  · have ht0 : k < (condDistinctAt enum y t0).length := Nat.find_spec h_exists
    have ht0_le_t : t0 ≤ t :=
      Nat.find_le (p := fun t' => k < (condDistinctAt enum y t').length) hk
    have hpre : condDistinctAt enum y t0 <+: condDistinctAt enum y t :=
      condPrefix_of_le enum hmono y ht0_le_t
    have hget := getD_eq_of_prefix (condDistinctAt enum y t0)
      (condDistinctAt enum y t) hpre k [] ht0
    simpa [k, hget]

/-- **M0 fixed-length core (conditional form).** Same as `KP_le_log_index_of_cond_enumeration`,
but the index is given as a string `z` of length `s` encoding the index. The cost is
`s + 2·|bits s| + O(1)` instead of `2·|bits k| + O(1)`. -/
theorem KP_le_fixed_length_index_of_cond_enumeration (U : Map)
    (hU : IsOptimalPrefixConditional U)
    (enum : BitString → ℕ → List BitString)
    (henum : Computable fun p : BitString × ℕ => enum p.1 p.2)
    (hmono : ∀ y t, enum y t <+: enum y (t + 1)) :
    ∃ c : ℕ, ∀ (y z : BitString) (t : ℕ),
      bitsToNat z < ((enum y t).eraseDups).length →
      KP U (((enum y t).eraseDups).getD (bitsToNat z) []) y ≤
        z.length + 2 * (Nat.bits z.length).length + (c : ENat) := by
  obtain ⟨c_map, hc_map⟩ :=
    KP_partrec_cond_first_map_le U hU (condFFixedLength enum)
      (condFFixedLength_partrec enum henum)
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  refine ⟨c_map + c_plain + c_len, fun y z t hk => ?_⟩
  have h_eval : (((enum y t).eraseDups).getD (bitsToNat z) []) ∈
      condFFixedLength enum y z := by
    exact condFFixedLength_eval enum hmono y z t hk
  calc KP U (((enum y t).eraseDups).getD (bitsToNat z) []) y
      ≤ KP U z y + (c_map : ENat) := hc_map z _ y h_eval
    _ ≤ KPPlain U z + (c_plain : ENat) + (c_map : ENat) := by
          gcongr
          exact hc_plain z y
    _ ≤ (z.length + 2 * (Nat.bits z.length).length + (c_len : ENat))
          + (c_plain : ENat) + (c_map : ENat) := by
          gcongr
          exact hc_len z
    _ = z.length + 2 * (Nat.bits z.length).length
          + ((c_map + c_plain + c_len : ℕ) : ENat) := by
          push_cast
          ring

end StagedEnumeration

end Kolmogorov
