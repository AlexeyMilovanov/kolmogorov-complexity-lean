/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.FinitePrograms
import KolmogorovMathlib.Prefix.EntropyFunctions
import KolmogorovMathlib.MonotoneComplexity.SharedCoding
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison

/-!
# Duplicate-free discovery of short-program outputs

An `Option` at each stage allows the stream to pause forever after its last output.
The mathematical final remainder is defined from a finite completed list; no program
is required to recognize that the stream has ended.
Blueprint nodes: `enum:blocks`, `enum:indices-ce`, `enum:layer`.
-/

namespace Kolmogorov.MDLPrediction

/-! ## Discovery streams -/

/-- Filter an injective request enumeration by level and decode its outputs. -/
private lemma exists_filtered_request_stream
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ stream : ℕ → ℕ → Option ℕ, Computable₂ stream ∧
      ∀ a, (∀ n, ((List.range n).filterMap (stream a)).Nodup) ∧
        (∀ i, (KPPlain U (natToBitString i)).toNat ≤ a ↔
          ∃ n, stream a n = some i) := by
  have hF := REPred_KPPlain_toNat_le hU
  obtain ⟨req, hcomp, hsound, hexhaustive, hinjective⟩ :=
    exists_requestStream_of_overgraph hF
  let F : BitString → ℕ := fun x => (KPPlain U x).toNat
  have key : ∀ a k i, ((req k).bind fun p => if p.2 = a then some (bitStringToNat p.1) else
    none) = some i ↔ req k = some (natToBitString i, a) := by
    intro a k i
    cases h : req k with
    | none => simp
    | some p =>
      obtain ⟨x, n⟩ := p
      by_cases hn : n = a
      · subst hn
        constructor
        · intro hx
          simp only [Option.bind_some, ite_true, Option.some.injEq] at hx
          subst hx
          simp [natToBitString_bitStringToNat]
        · intro hx
          simp only [Option.some.injEq, Prod.mk.injEq, and_true] at hx
          subst hx
          simp [bitStringToNat_natToBitString]
      · simp [hn]
  refine ⟨fun a k => (req k).bind fun p => if p.2 = a then some (bitStringToNat p.1) else none,
    ?_, fun a => ⟨fun n => ?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩⟩
  · have hinner : Primrec₂ fun (ak : ℕ × ℕ) (p : BitString × ℕ) =>
      if p.2 = ak.1 then some (bitStringToNat p.1) else none :=
      Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.option_some.comp (primrec_bitStringToNat.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.const none)
    exact Computable.option_bind (hcomp.comp Computable.snd) hinner.to_comp
  · refine List.Nodup.filterMap ?_ List.nodup_range
    intro k k' i hk hk'
    exact hinjective k k' _ ((key a k i).1 hk) ((key a k' i).1 hk')
  · obtain ⟨k, hk⟩ := hexhaustive _ _ hi
    exact ⟨k, (key a k i).2 hk⟩
  · obtain ⟨k, hk⟩ := hi
    exact hsound k _ _ ((key a k i).1 hk)

/-- One uniformly computable, duplicate-free discovery family for all complexity sublevels.
Blueprint node `enum:indices-ce`. -/
def IsDiscoveryStream (U : Map) (stream : ℕ → ℕ → Option ℕ) : Prop :=
  Computable₂ stream ∧
    ∀ a, (∀ n, ((List.range n).filterMap (stream a)).Nodup) ∧
      (∀ i, KPNat U i ≤ a ↔ ∃ n, stream a n = some i)

/-- Dovetail short programs into a duplicate-free, possibly nonterminating stream.
Blueprint node `enum:indices-ce`. -/
theorem enum_indices_ce (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ stream : ℕ → ℕ → Option ℕ, IsDiscoveryStream U stream := by
  obtain ⟨stream, hs_comp, hs_prop⟩ := exists_filtered_request_stream U hU
  use stream
  constructor
  · exact hs_comp
  · intro a
    have hprop_a := hs_prop a
    constructor
    · exact hprop_a.1
    · intro i
      have hprop_a_2 := hprop_a.2 i
      have hne := KPPlain_ne_top_of_isOptimalPrefixConditional hU (natToBitString i)
      have eq1 : KPNat U i = KPPlain U (natToBitString i) := KPNat_def U i
      rw [eq1]
      have h1 : (KPPlain U (natToBitString i)).toNat ≤ a ↔
           KPPlain U (natToBitString i) ≤ (a : ℕ∞) := by
        refine ⟨fun h => ?_, ENat.toNat_le_of_le_natCast⟩
        calc KPPlain U (natToBitString i) = ((KPPlain U (natToBitString i)).toNat : ℕ∞) :=
          (ENat.natCast_toNat hne).symm
          _ ≤ (a : ℕ∞) := by exact_mod_cast h
      rw [← h1]
      exact hprop_a_2

/-- One classically selected uniformly computable discovery family.
Blueprint node `enum:indices-ce`. -/
noncomputable def discoveryStream (U : Map) (hU : IsOptimalPrefixConditional U)
    : ℕ → ℕ → Option ℕ :=
  Classical.choose (enum_indices_ce U hU)

/-! ## Complete ordinal blocks -/

/-- The ordinal `j` block in a finite discovery list, with size `2^r`.
Blueprint node `enum:blocks`. -/
def ordinalBlock (L : List ℕ) (r j : ℕ) : List ℕ :=
  (L.drop (j * 2 ^ r)).take (2 ^ r)

/-- A complete block is witnessed by a finite discovery stage at which all its
members have appeared. Blueprint node `enum:blocks`. -/
def IsCompleteBlock (U : Map) (hU : IsOptimalPrefixConditional U)
    (a r j : ℕ) (G : List ℕ) : Prop :=
  ∃ n : ℕ, G = ordinalBlock ((List.range n).filterMap (discoveryStream U hU a)) r j ∧
    G.length = 2 ^ r

/-- Every finite discovery order splits into complete consecutive blocks and
one remainder smaller than `2^r`. Blueprint node `enum:blocks`. -/
private lemma discoveryStream_complete_at_stage (U : Map)
    (hU : IsOptimalPrefixConditional U) (a : ℕ) :
    ∃ n : ℕ, ∀ i, i ∈ (List.range n).filterMap (discoveryStream U hU a) ↔
      KPNat U i ≤ a := by
  have h1 : IsDiscoveryStream U (discoveryStream U hU) := by
    unfold discoveryStream
    exact Classical.choose_spec (enum_indices_ce U hU)
  unfold IsDiscoveryStream at h1
  have ⟨_, h_iff⟩ := h1.2 a
  have h_fin := (finite_model_indices_complexity_le U a).1
  let S := h_fin.toFinset
  have h_exists : ∀ i ∈ S, ∃ n, discoveryStream U hU a n = some i := by
    intro i hi
    have : KPNat U i ≤ a := (Set.Finite.mem_toFinset h_fin).mp hi
    exact (h_iff i).mp this
  let f : ℕ → ℕ := fun i => if hi : i ∈ S then Classical.choose (h_exists i hi) else 0
  let N := S.sup f + 1
  use N
  intro i
  constructor
  · intro hi
    rw [List.mem_filterMap] at hi
    rcases hi with ⟨n, _, hn⟩
    exact (h_iff i).mpr ⟨n, hn⟩
  · intro hi
    have hi_S : i ∈ S := (Set.Finite.mem_toFinset h_fin).mpr hi
    rw [List.mem_filterMap]
    have h_choose := Classical.choose_spec (h_exists i hi_S)
    use Classical.choose (h_exists i hi_S)
    constructor
    · apply List.mem_range.mpr
      have h_f_eq : f i = Classical.choose (h_exists i hi_S) := by
        dsimp [f]
        have : (if hi : i ∈ S then Classical.choose (h_exists i hi) else 0) =
            Classical.choose (h_exists i hi_S) := by
          rw [dite_eq_left hi_S]
        exact this
      rw [<- h_f_eq]
      have h_le : f i ≤ S.sup f := Finset.le_sup hi_S
      omega
    · exact h_choose

/-- Each finite prefix of the selected discovery stream is duplicate-free. -/
private lemma discoveryStream_nodup_at_stage (U : Map)
    (hU : IsOptimalPrefixConditional U) (a n : ℕ) :
    ((List.range n).filterMap (discoveryStream U hU a)).Nodup := by
  have h1 : IsDiscoveryStream U (discoveryStream U hU) := by
    unfold discoveryStream
    exact Classical.choose_spec (enum_indices_ce U hU)
  unfold IsDiscoveryStream at h1
  exact h1.2 a |>.1 n

/-- A list splits into consecutive full ordinal blocks and a short remainder. -/
private lemma ordinalBlock_decomposition (L : List ℕ) (r : ℕ) :
    ∃ remainder : List ℕ,
      L = ((List.range (L.length / 2 ^ r)).flatMap (ordinalBlock L r)) ++
        remainder ∧
      remainder = L.drop ((L.length / 2 ^ r) * 2 ^ r) ∧
      remainder.length < 2 ^ r := by
  use L.drop ((L.length / 2 ^ r) * 2 ^ r)
  have h1 : ((List.range (L.length / 2 ^ r)).flatMap (ordinalBlock L r)) =
    L.take ((L.length / 2 ^ r) * 2 ^ r) := by
    generalize L.length / 2 ^ r = k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton,
        ordinalBlock, Nat.succ_mul, <- List.take_add]
  constructor
  · rw [h1, List.take_append_drop]
  constructor
  · rfl
  · rw [List.length_drop]
    have h2 := Nat.div_add_mod L.length (2 ^ r)
    rw [mul_comm] at h2
    have h3 : L.length % 2 ^ r = L.length - (L.length / 2 ^ r) * 2 ^ r := by
      exact Eq.symm (Nat.sub_eq_of_eq_add' (Eq.symm h2))
    rw [<- h3]
    apply Nat.mod_lt
    positivity

/-- Every full ordinal block has a finite discovery witness. -/
private lemma ordinalBlock_isComplete (U : Map)
    (hU : IsOptimalPrefixConditional U) (a r n : ℕ) (j : ℕ)
    (hj : j < ((List.range n).filterMap (discoveryStream U hU a)).length / 2 ^ r) :
    IsCompleteBlock U hU a r j
      (ordinalBlock ((List.range n).filterMap (discoveryStream U hU a)) r j) := by
  unfold IsCompleteBlock
  use n
  constructor
  · rfl
  · unfold ordinalBlock
    rw [List.length_take, List.length_drop]
    have h1 : (j + 1) * 2 ^ r ≤ ((List.range n).filterMap (discoveryStream U hU a)).length := by
      have h2 : j + 1 ≤ ((List.range n).filterMap (discoveryStream U hU a)).length / 2 ^ r := hj
      exact Nat.mul_le_of_le_div _ _ _ h2
    have h3 : j * 2 ^ r + 2 ^ r ≤ ((List.range n).filterMap (discoveryStream U hU a)).length := by
      linarith
    have h4 : 2 ^ r ≤ ((List.range n).filterMap (discoveryStream U hU a)).length - j * 2 ^ r := by
      omega
    exact Nat.min_eq_left h4

/-- Partition the finite discovery order into complete blocks of size `2^r` and a
short final remainder. Blueprint node `enum:blocks`. -/
theorem enum_blocks (U : Map) (hU : IsOptimalPrefixConditional U) (a r : ℕ) :
    ∃ (L remainder : List ℕ) (n : ℕ),
      L = (List.range n).filterMap (discoveryStream U hU a) ∧
      (∀ i, i ∈ L ↔ KPNat U i ≤ a) ∧ L.Nodup ∧
      L = ((List.range (L.length / 2 ^ r)).flatMap (ordinalBlock L r)) ++
        remainder ∧ remainder = L.drop ((L.length / 2 ^ r) * 2 ^ r) ∧
      remainder.length < 2 ^ r ∧
      ∀ j < L.length / 2 ^ r, IsCompleteBlock U hU a r j (ordinalBlock L r j) := by
  have ⟨n, hn_cutoff⟩ := discoveryStream_complete_at_stage U hU a
  let L := (List.range n).filterMap (discoveryStream U hU a)
  have ⟨remainder, hrem_eq, hrem_drop, hrem_len⟩ := ordinalBlock_decomposition L r
  use L, remainder, n
  constructor
  · rfl
  constructor
  · exact hn_cutoff
  constructor
  · apply discoveryStream_nodup_at_stage
  constructor
  · exact hrem_eq
  constructor
  · exact hrem_drop
  constructor
  · exact hrem_len
  · intro j hj
    apply ordinalBlock_isComplete U hU a r n j hj

/-- The complexity layer is finite and uniformly enumerable; the final incomplete
block need not be detected by the enumeration. Blueprint node `enum:layer`. -/
theorem enumerate_low_complexity_indices (U : Map)
    (hU : IsOptimalPrefixConditional U) (a r : ℕ) :
    (Set.Finite {i : ℕ | KPNat U i ≤ a}) ∧
      Set.ncard {i : ℕ | KPNat U i ≤ a} < 2 ^ (a + 1) ∧
      IsDiscoveryStream U (discoveryStream U hU) ∧
      ∃ (L remainder : List ℕ) (n : ℕ),
        L = (List.range n).filterMap (discoveryStream U hU a) ∧
        (∀ i, i ∈ L ↔ KPNat U i ≤ a) ∧ L.Nodup ∧
        L = ((List.range (L.length / 2 ^ r)).flatMap (ordinalBlock L r)) ++
          remainder ∧ remainder.length < 2 ^ r := by
  have h12 := finite_model_indices_complexity_le U a
  have h3 : IsDiscoveryStream U (discoveryStream U hU) :=
    Classical.choose_spec (enum_indices_ce U hU)
  obtain ⟨L, remainder, n, h4, h5, h6, h7, _, h9, _⟩ := enum_blocks U hU a r
  exact ⟨h12.1, h12.2, h3, L, remainder, n, h4, h5, h6, h7, h9⟩
end Kolmogorov.MDLPrediction
