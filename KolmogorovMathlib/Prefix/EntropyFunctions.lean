/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Properties.StableAliasesSUVTheorem
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinOnline
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison

/-!
# Entropy functions and the exact `min` construction for prefix complexity

An *entropy function* (Muchnik–Positselsky; Allender–Friedman–Gasarch, *Limits on the
computational power of random strings*) is a total `F : BitString → ℕ` with

* the Kraft condition on finite partial sums, `∑_{x ∈ S} 2^{-F x} ≤ 1` for every finite `S`;
* a computably enumerable overgraph `{(x, n) | F x ≤ n}` (Mathlib's `REPred`).

The plain prefix complexity `KPPlain U` of an optimal prefix decompressor `U` is such a
function (after `ENat.toNat`, which is harmless because `KPPlain U x ≠ ⊤`), and by the
Kraft–Chaitin theorem it is minimal among them up to an additive constant.

The main result of this module is the *exact* realisation of the minimum of a universal
prefix complexity and an entropy function by a prefix complexity:

> `exists_isOptimalPrefixConditional_min`: for every optimal prefix decompressor `U` and
> every entropy function `F` there is an optimal prefix decompressor `U'` with
> `KPPlain U' x = min (KPPlain U x + 5) (F x + 3)` for **every** `x`.

This is Claim 1 of Allender–Friedman–Gasarch for prefix machines, with the constants
`5` and `3` of the Lean formalisation of their Theorem 10 (the `AFG` project, `Hmin`).
Exactness matters there: the oracle is the set `{x | |x| ≤ H x}` of `H`-random strings, so
`H` must be realised as the prefix complexity of a genuine machine, not merely up to `O(1)`.

## Construction

1. `exists_requestStream_of_overgraph`: from the c.e. overgraph of `F`, a computable stream
   `req : ℕ → Option (BitString × ℕ)` that lists every pair `(x, n)` with `F x ≤ n` exactly
   once (first stage of appearance), and nothing else.
2. `exists_exact_prefixDecompressor`: the online Kraft–Chaitin allocator
   (`exists_online_prefixFree_of_kraft_le_one`) applied to the lengths `n + 1` of that stream
   (total weight `∑_x ∑_{n ≥ F x} 2^{-(n+1)} = ∑_x 2^{-F x} ≤ 1`) gives a prefix decompressor
   `D` with `KPPlain D x = F x + 1` exactly: the shortest code for `x` is the one allocated to
   the request `(x, F x)`.
3. `KP_taggedUnion_eq_iInf`: the complexity of a tagged union (`taggedUnion`, tag `1^i 0`) is
   exactly `⨅ i, KP (M i) x y + (i + 1)`.
4. `exists_isOptimalPrefixConditional_min`: the tagged union of the family
   `M 4 = U`, `M 1 = D`, `M i = ∅` otherwise, has `KP = min (KP U + 5, KP D + 2)` and is
   optimal because it is bounded by `KP U + 5` (`isOptimalPrefixConditional_of_KP_le`).

## Interface for the `AFG` project

`KPPlain_toNat_kraft`, `REPred_KPPlain_toNat_le` and `exists_isOptimalPrefixConditional_min_toNat`
state the three facts in the `ℕ`-valued form (`(KPPlain U x).toNat`) used by the
`AprioriComplexity` structure of that project.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Entropy functions -/

/-- The Kraft condition of an entropy function, on finite partial sums (over `ℝ`). -/
def IsKraftFun (F : BitString → ℕ) : Prop :=
  ∀ S : Finset BitString, ∑ x ∈ S, (2 : ℝ)⁻¹ ^ F x ≤ 1

/-- The overgraph `{(x, n) | F x ≤ n}` of `F` is computably enumerable. -/
def HasREOvergraph (F : BitString → ℕ) : Prop :=
  REPred fun p : BitString × ℕ => F p.1 ≤ p.2

/-- An *entropy function*: the Kraft condition on finite sums and a c.e. overgraph. -/
structure IsEntropyFun (F : BitString → ℕ) : Prop where
  /-- `∑_{x ∈ S} 2^{-F x} ≤ 1` for every finite `S`. -/
  kraft : IsKraftFun F
  /-- `{(x, n) | F x ≤ n}` is computably enumerable. -/
  re : HasREOvergraph F

/-! ### Step 1: the overgraph as a computable request stream -/

/-- The request stream of `exists_requestStream_of_overgraph` for a code `c` of the overgraph:
`req k = some p` iff `k = pair m s`, `decode m = some p`, and `c` halts on `encode p` within
`s + 1` steps but not within `s` steps. -/
private def exists_requestStream_of_overgraph_req (c : Nat.Partrec.Code) (k : ℕ)
    : Option (BitString × ℕ) :=
  (Encodable.decode k.unpair.1 : Option (BitString × ℕ)).bind fun p =>
    if (Nat.Partrec.Code.evaln (k.unpair.2 + 1) c (Encodable.encode p)).isSome &&
       !(Nat.Partrec.Code.evaln k.unpair.2 c (Encodable.encode p)).isSome then
      some p
    else
      none

/-- Towards `exists_requestStream_of_overgraph`: getting a code from REPred. -/
private lemma exists_requestStream_of_overgraph_step0_code
    {F : BitString → ℕ} (hF : HasREOvergraph F) :
  ∃ c : Nat.Partrec.Code, ∀ a : BitString × ℕ, F a.1 ≤ a.2
    ↔ (c.eval (Encodable.encode a)).Dom := by
  unfold HasREOvergraph at hF
  unfold REPred at hF
  unfold Partrec at hF
  rcases Nat.Partrec.Code.exists_code.mp hF with ⟨c, hc⟩
  use c
  intro a
  rw [hc]
  simp [Encodable.encodek, Part.map, Part.dom_iff_mem]

/-- Towards `exists_requestStream_of_overgraph`: the request stream is computable. -/
private lemma exists_requestStream_of_overgraph_step1_computable (c : Nat.Partrec.Code) :
  Computable (exists_requestStream_of_overgraph_req c) := by
  have H1 : Primrec₂ fun (k : ℕ) (p : BitString × ℕ) =>
    (Nat.Partrec.Code.evaln ((Nat.unpair k).2 + 1) c (Encodable.encode p)).isSome &&
       !(Nat.Partrec.Code.evaln (Nat.unpair k).2 c (Encodable.encode p)).isSome := by
    exact Primrec₂.comp Primrec.and
      (Primrec.option_isSome.comp <| Nat.Partrec.Code.primrec_evaln.comp <|
        (Primrec.pair
          (Primrec.pair
            (Primrec₂.comp Primrec.nat_add (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
              (Primrec.const 1))
            (Primrec.const c))
          (Primrec.encode.comp Primrec.snd)
        )
      )
      (Primrec.not.comp <| Primrec.option_isSome.comp <| Nat.Partrec.Code.primrec_evaln.comp <|
        (Primrec.pair
          (Primrec.pair
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
            (Primrec.const c))
          (Primrec.encode.comp Primrec.snd)
        ))
  have H2 : Computable₂ fun (k : ℕ) (p : BitString × ℕ) =>
    (Nat.Partrec.Code.evaln ((Nat.unpair k).2 + 1) c (Encodable.encode p)).isSome &&
       !(Nat.Partrec.Code.evaln (Nat.unpair k).2 c (Encodable.encode p)).isSome := H1.to_comp
  have H3 : Computable₂ fun (k : ℕ) (p : BitString × ℕ) =>
    if (Nat.Partrec.Code.evaln ((Nat.unpair k).2 + 1) c (Encodable.encode p)).isSome &&
       !(Nat.Partrec.Code.evaln (Nat.unpair k).2 c (Encodable.encode p)).isSome then
      some p
    else
      none := (Computable.cond H2 (Computable.option_some.comp Computable.snd)
        (Computable.const none)).of_eq (by
    intro ⟨k, p⟩
    dsimp
    cases h : (Nat.Partrec.Code.evaln ((Nat.unpair k).2 + 1) c (Encodable.encode p)).isSome &&
      !(Nat.Partrec.Code.evaln (Nat.unpair k).2 c (Encodable.encode p)).isSome
    · rfl
    · rfl
  )
  have H4 : Computable fun k : ℕ => Encodable.decode (Nat.unpair k).1 (α := BitString × ℕ) :=
    Computable.decode.comp (Primrec.fst.comp Primrec.unpair).to_comp
  exact Computable.option_bind H4 H3

/-- Towards `exists_requestStream_of_overgraph`: the request stream is sound. -/
private lemma exists_requestStream_of_overgraph_step2_sound
    {F : BitString → ℕ} (c : Nat.Partrec.Code)
  (hc : ∀ a : BitString × ℕ, F a.1 ≤ a.2 ↔ (c.eval (Encodable.encode a)).Dom)
  (k : ℕ) (x : BitString) (n : ℕ) (h : exists_requestStream_of_overgraph_req c k = some (x, n)) :
  F x ≤ n := by
  dsimp [exists_requestStream_of_overgraph_req] at h
  cases h_decode : Encodable.decode (α := BitString × ℕ) k.unpair.1 with
  | none =>
    rw [h_decode] at h
    dsimp at h
    contradiction
  | some p =>
    rw [h_decode] at h
    dsimp at h
    split at h
    · injection h with h_eq
      subst h_eq
      apply (hc (x, n)).mpr
      rename_i h_if
      have h1 := Bool.and_elim_left h_if
      simp only [Option.isSome_iff_exists] at h1
      obtain ⟨v, hv⟩ := h1
      exact Part.dom_iff_mem.mpr ⟨v, Nat.Partrec.Code.evaln_sound hv⟩
    · contradiction

/-- Towards `exists_requestStream_of_overgraph`: the request stream is exhaustive. -/
private lemma exists_requestStream_of_overgraph_step3_exhaustive
    {F : BitString → ℕ} (c : Nat.Partrec.Code)
  (hc : ∀ a : BitString × ℕ, F a.1 ≤ a.2 ↔ (c.eval (Encodable.encode a)).Dom)
  (x : BitString) (n : ℕ) (h : F x ≤ n) :
  ∃ k, exists_requestStream_of_overgraph_req c k = some (x, n) := by
  have h_dom : (c.eval (Encodable.encode (x, n))).Dom := (hc (x, n)).mp h
  have h_ex_val := Part.dom_iff_mem.mp h_dom
  rcases h_ex_val with ⟨v, hv⟩
  have h_ex_s := Nat.Partrec.Code.evaln_complete.mp hv
  rcases h_ex_s with ⟨s, hs⟩
  have hS_nonempty :
      ∃ s, (Nat.Partrec.Code.evaln s c (Encodable.encode (x, n))).isSome := by
    use s
    exact Option.isSome_iff_exists.mpr ⟨v, hs⟩
  let s_min := Nat.find hS_nonempty
  have hs_min :
      (Nat.Partrec.Code.evaln s_min c (Encodable.encode (x, n))).isSome := Nat.find_spec hS_nonempty
  have hs_min_pos : 0 < s_min := by
    by_contra h0
    have hz : s_min = 0 := by omega
    have h_eval0 : ¬ (Nat.Partrec.Code.evaln s_min c (Encodable.encode (x, n))).isSome := by
      rw [hz]
      simp [Nat.Partrec.Code.evaln]
    exact h_eval0 hs_min
  let s_idx := s_min - 1
  have hs_min_eq : s_min = s_idx + 1 := (Nat.sub_add_cancel hs_min_pos).symm
  have hs_idx_not : ¬(Nat.Partrec.Code.evaln s_idx c (Encodable.encode (x, n))).isSome := by
    have h_lt : s_idx < s_min := Nat.sub_lt hs_min_pos (by decide)
    exact Nat.find_min hS_nonempty h_lt
  have hs_idx_not' :
      (Nat.Partrec.Code.evaln s_idx c (Encodable.encode (x, n))).isSome = false := by
    by_contra h'
    have h'' : (Nat.Partrec.Code.evaln s_idx c (Encodable.encode (x, n))).isSome = true := by
      cases hx : (Nat.Partrec.Code.evaln s_idx c (Encodable.encode (x, n))).isSome
      · contradiction
      · rfl
    exact hs_idx_not h''
  let p_idx := Encodable.encode (x, n)
  let k := Nat.pair p_idx s_idx
  use k
  unfold exists_requestStream_of_overgraph_req
  have h_unpair1 : (Nat.unpair k).1 = p_idx := Nat.unpair_pair p_idx s_idx ▸ rfl
  have h_unpair2 : (Nat.unpair k).2 = s_idx := Nat.unpair_pair p_idx s_idx ▸ rfl
  rw [h_unpair1, h_unpair2, Encodable.encodek]
  simp only [Option.bind_some]
  have h_cond1 :
      (Nat.Partrec.Code.evaln (s_idx + 1) c (Encodable.encode (x, n))).isSome = true := by
    rw [← hs_min_eq]
    exact hs_min
  have h_cond2 : !(Nat.Partrec.Code.evaln s_idx c (Encodable.encode (x, n))).isSome = true := by
    rw [hs_idx_not']
    rfl
  rw [h_cond1]
  change (if (true && ! (Nat.Partrec.Code.evaln s_idx c (Encodable.encode (x, n))).isSome) = true
    then some (x, n) else none) = some (x, n)
  rw [hs_idx_not']
  rfl

/-- Towards `exists_requestStream_of_overgraph`: whenever `Encodable.decode n` succeeds on `Bool`,
the result encodes back to `n` (the decoder is injective on its range). -/
private lemma exists_requestStream_of_overgraph_step4_injective_encode_bool (n : ℕ) (b : Bool)
    (h : (Encodable.decode n : Option Bool) = some b) : Encodable.encode b = n := by
  rcases n with _ | _ | n
  · rw [Encodable.decode_zero] at h
    cases Option.some.inj h
    rfl
  · rw [Encodable.decode_one] at h
    cases Option.some.inj h
    rfl
  · rw [Encodable.decode_ge_two (n + 1 + 1) (by omega)] at h
    exact absurd h (by simp)

/-- Towards `exists_requestStream_of_overgraph`: whenever `Encodable.decode n` succeeds on
`BitString`, the result encodes back to `n` (the decoder is injective on its range). -/
private lemma exists_requestStream_of_overgraph_step4_injective_encode_list :
    ∀ (n : ℕ) (l : BitString), (Encodable.decode n : Option BitString) = some l →
      Encodable.encode l = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l h
    rcases n with _ | n
    · rw [Encodable.decode_list_zero] at h
      cases Option.some.inj h
      rfl
    · rw [Encodable.decode_list_succ] at h
      cases hb : (Encodable.decode (Nat.unpair n).1 : Option Bool) with
      | none =>
        rw [hb] at h
        exact absurd (show (none : Option BitString) = some l from h) (by simp)
      | some b =>
        cases hl : (Encodable.decode (Nat.unpair n).2 : Option BitString) with
        | none =>
          rw [hb, hl] at h
          exact absurd (show (none : Option BitString) = some l from h) (by simp)
        | some l' =>
          simp only [hb, hl] at h
          cases Option.some.inj h
          have h1 := exists_requestStream_of_overgraph_step4_injective_encode_bool _ _ hb
          have h2 := ih (Nat.unpair n).2 (Nat.lt_succ_of_le (Nat.unpair_right_le n)) l' hl
          rw [Encodable.encode_list_cons, h1, h2, Nat.pair_unpair]

/-- Towards `exists_requestStream_of_overgraph`: whenever `Encodable.decode m` succeeds on
`BitString × ℕ`, the result encodes back to `m` (the decoder is injective on its range). -/
private lemma exists_requestStream_of_overgraph_step4_injective_encode_prod (m : ℕ)
    (p : BitString × ℕ) (h : (Encodable.decode m : Option (BitString × ℕ)) = some p) :
    Encodable.encode p = m := by
  rw [Encodable.decode_prod_val] at h
  cases hl : (Encodable.decode (Nat.unpair m).1 : Option BitString) with
  | none => simp [hl] at h
  | some l =>
    simp only [hl, Option.bind_some, Encodable.decode_nat, Option.map_some] at h
    cases Option.some.inj h
    rw [Encodable.encode_prod_val,
      exists_requestStream_of_overgraph_step4_injective_encode_list _ _ hl,
      Encodable.encode_nat, Nat.pair_unpair]

/-- Towards `exists_requestStream_of_overgraph`: if `req c j = some p`, then the first component of
`unpair j` is the code of `p`, and `c` halts on it within `(unpair j).2 + 1` steps but not
within `(unpair j).2` steps. -/
private lemma exists_requestStream_of_overgraph_step4_injective_unfold (c : Nat.Partrec.Code)
    (j : ℕ) (p : BitString × ℕ) (h : exists_requestStream_of_overgraph_req c j = some p) :
    (Nat.unpair j).1 = Encodable.encode p ∧
      (Nat.Partrec.Code.evaln ((Nat.unpair j).2 + 1) c (Encodable.encode p)).isSome = true ∧
      (Nat.Partrec.Code.evaln (Nat.unpair j).2 c (Encodable.encode p)).isSome = false := by
  unfold exists_requestStream_of_overgraph_req at h
  cases hd : (Encodable.decode (Nat.unpair j).1 : Option (BitString × ℕ)) with
  | none =>
    rw [hd] at h
    exact absurd h (by simp)
  | some q =>
    rw [hd, Option.bind_some] at h
    split at h
    · rename_i hif
      obtain rfl : q = p := Option.some.inj h
      refine ⟨(exists_requestStream_of_overgraph_step4_injective_encode_prod _ _ hd).symm,
        Bool.and_elim_left hif, ?_⟩
      simpa using Bool.and_elim_right hif
    · exact absurd h (by simp)

/-- Towards `exists_requestStream_of_overgraph`: `evaln` is monotone in the step bound, so if `c`
halts on `n` within `s` steps but not within `s'` steps, then `s' < s`. -/
private lemma exists_requestStream_of_overgraph_step4_injective_stage_lt (c : Nat.Partrec.Code)
    (n s s' : ℕ) (h : (Nat.Partrec.Code.evaln s c n).isSome = true)
    (h' : (Nat.Partrec.Code.evaln s' c n).isSome = false) : s' < s := by
  by_contra hle
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  have hmono := Nat.Partrec.Code.evaln_mono (not_lt.mp hle) hv
  rw [hmono] at h'
  exact absurd h' (by simp)

/-- Towards `exists_requestStream_of_overgraph`: the request stream is injective. -/
private lemma exists_requestStream_of_overgraph_step4_injective (c : Nat.Partrec.Code)
  (k k' : ℕ) (p : BitString × ℕ) (hk : exists_requestStream_of_overgraph_req c k = some p)
    (hk' : exists_requestStream_of_overgraph_req c k' = some p) :
  k = k' := by
  obtain ⟨h1, h2, h3⟩ := exists_requestStream_of_overgraph_step4_injective_unfold c k p hk
  obtain ⟨h1', h2', h3'⟩ := exists_requestStream_of_overgraph_step4_injective_unfold c k' p hk'
  have hlt := exists_requestStream_of_overgraph_step4_injective_stage_lt c _ _ _ h2 h3'
  have hlt' := exists_requestStream_of_overgraph_step4_injective_stage_lt c _ _ _ h2' h3
  have hs : (Nat.unpair k).2 = (Nat.unpair k').2 := by omega
  calc k = Nat.pair (Nat.unpair k).1 (Nat.unpair k).2 := (Nat.pair_unpair k).symm
    _ = Nat.pair (Nat.unpair k').1 (Nat.unpair k').2 := by rw [h1, h1', hs]
    _ = k' := Nat.pair_unpair k'

/-- A c.e. overgraph can be listed by a computable stream that produces every pair `(x, n)`
with `F x ≤ n` exactly once and never produces a pair outside the overgraph.

Proof sketch: `REPred` gives a code `c` with `(x, n)` in the overgraph iff `c` halts on
`encode (x, n)` (`Nat.Partrec.Code.exists_code`). Let `req k := some (x, n)` iff, for
`(m, s) := Nat.unpair k` and `(x, n) := decode m`, the code halts on `encode (x, n)` within
`s + 1` steps (`Nat.Partrec.Code.evaln`) but not within `s` steps (first stage of appearance);
`req k := none` otherwise. Decidability of the two `evaln` tests makes `req` computable; the
first-stage condition makes the listing injective; `evaln_complete`/`evaln_sound` make it
exhaustive and sound. Compare `REPred.exists_stage` and `exists_reEnum` in the `AFG`
formalisation and `appearsAt` in `Prefix/OptimalExistence.lean`. -/
theorem exists_requestStream_of_overgraph {F : BitString → ℕ} (hF : HasREOvergraph F) :
    ∃ req : ℕ → Option (BitString × ℕ),
      Computable req ∧
      (∀ k x n, req k = some (x, n) → F x ≤ n) ∧
      (∀ x n, F x ≤ n → ∃ k, req k = some (x, n)) ∧
      (∀ k k' p, req k = some p → req k' = some p → k = k') := by
  have ⟨c, hc⟩ := exists_requestStream_of_overgraph_step0_code hF
  use exists_requestStream_of_overgraph_req c
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact exists_requestStream_of_overgraph_step1_computable c
  · exact exists_requestStream_of_overgraph_step2_sound c hc
  · exact exists_requestStream_of_overgraph_step3_exhaustive c hc
  · exact exists_requestStream_of_overgraph_step4_injective c

/-- Towards `requestKraftWeight_succ_le_one_of_isKraftFun`: the geometric tail sum. -/
private lemma requestKraftWeight_succ_le_one_of_isKraftFun_geom (a : ℕ) :
    ∑' n : ℕ, (if a ≤ n then (2 : ℝ≥0∞)⁻¹ ^ (n + 1) else 0) = (2 : ℝ≥0∞)⁻¹ ^ a := by
  have hs : ∑' m : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (m + 1) = 1 := by
    rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hsupp : Function.support
      (fun n : ℕ => if a ≤ n then (2 : ℝ≥0∞)⁻¹ ^ (n + 1) else 0) ⊆ Set.range (a + ·) := by
    intro n hn
    by_cases h : a ≤ n
    · exact ⟨n - a, by change a + (n - a) = n; omega⟩
    · exact (Function.mem_support.mp hn (by simp [h])).elim
  rw [← (add_right_injective a).tsum_eq hsupp]
  calc _ = ∑' m : ℕ, (2 : ℝ≥0∞)⁻¹ ^ a * (2 : ℝ≥0∞)⁻¹ ^ (m + 1) :=
        tsum_congr fun m => by rw [ite_eq_left (Nat.le_add_right a m), add_assoc, pow_add]
    _ = _ := by rw [ENNReal.tsum_mul_left, hs, mul_one]

/-- Towards `requestKraftWeight_succ_le_one_of_isKraftFun`: the Kraft sum of `F` as a `tsum` is at
most `1`. -/
private lemma requestKraftWeight_succ_le_one_of_isKraftFun_kraft_tsum {F : BitString → ℕ}
    (hF : IsKraftFun F) : ∑' x : BitString, (2 : ℝ≥0∞)⁻¹ ^ F x ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  have key : ∀ x, ENNReal.ofReal ((2 : ℝ)⁻¹ ^ F x) = (2 : ℝ≥0∞)⁻¹ ^ F x := fun x => by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  calc ∑ x ∈ S, (2 : ℝ≥0∞)⁻¹ ^ F x = ∑ x ∈ S, ENNReal.ofReal ((2 : ℝ)⁻¹ ^ F x) := by
        simp_rw [key]
    _ = ENNReal.ofReal (∑ x ∈ S, (2 : ℝ)⁻¹ ^ F x) :=
        (ENNReal.ofReal_sum_of_nonneg fun x _ => by positivity).symm
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hF S)
    _ = 1 := ENNReal.ofReal_one

/-- Towards `requestKraftWeight_succ_le_one_of_isKraftFun`: a listing injective on `some` values
weighs at most the sum over all pairs. -/
private lemma requestKraftWeight_succ_le_one_of_isKraftFun_inj_le
    (req : ℕ → Option (BitString × ℕ)) (w : BitString × ℕ → ℝ≥0∞)
    (hinj : ∀ k k' p, req k = some p → req k' = some p → k = k') :
    (∑' k, match req k with | some p => w p | none => 0) ≤ ∑' p, w p := by
  have hex : ∀ k : {k : ℕ // ∃ p, req k = some p}, ∃ p, req k.1 = some p := fun k => k.2
  choose f hf using hex
  have hfi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact hinj a.1 b.1 (f a) (hf a) (by rw [h]; exact hf b)
  have hsupp : Function.support (fun k : ℕ => match req k with | some p => w p | none => 0) ⊆
      Set.range (Subtype.val : {k : ℕ // ∃ p, req k = some p} → ℕ) := by
    intro k hk
    cases hreq : req k with
    | none => exact (Function.mem_support.mp hk (by simp [hreq])).elim
    | some p => exact ⟨⟨k, p, hreq⟩, rfl⟩
  calc (∑' k, match req k with | some p => w p | none => 0)
      = ∑' k : {k : ℕ // ∃ p, req k = some p},
          (match req k.1 with | some p => w p | none => 0) :=
        (Subtype.val_injective.tsum_eq hsupp).symm
    _ = ∑' k : {k : ℕ // ∃ p, req k = some p}, w (f k) :=
        tsum_congr fun k => by simp [hf k]
    _ ≤ ∑' p, w p := ENNReal.tsum_comp_le_tsum_of_injective hfi w

/-- The Kraft weight of the length stream `n + 1` over an injective listing of the overgraph of
a Kraft function is at most `1`: `∑_x ∑_{n ≥ F x} 2^{-(n+1)} = ∑_x 2^{-F x} ≤ 1`.

Proof sketch: the stream is an injection into `{(x, n) | F x ≤ n}`, so its weight is at most
the `tsum` over that set, which is `∑_x ∑_{n ≥ F x} 2^{-(n+1)} = ∑_x 2^{-F x}`; the finite
Kraft sums bound this `tsum` by `1` (`ENNReal.tsum_eq_iSup_sum`, `ENNReal.ofReal` transfer
of `IsKraftFun`). -/
theorem requestKraftWeight_succ_le_one_of_isKraftFun {F : BitString → ℕ} (hF : IsKraftFun F)
    (req : ℕ → Option (BitString × ℕ))
    (hsound : ∀ k x n, req k = some (x, n) → F x ≤ n)
    (hinj : ∀ k k' p, req k = some p → req k' = some p → k = k') :
    requestKraftWeight (fun k => (req k).map fun p => p.2 + 1) ≤ 1 := by
  obtain ⟨W, hW⟩ : ∃ W : BitString × ℕ → ℝ≥0∞,
      ∀ p, W p = if F p.1 ≤ p.2 then (2 : ℝ≥0∞)⁻¹ ^ (p.2 + 1) else 0 :=
    ⟨fun p => if F p.1 ≤ p.2 then (2 : ℝ≥0∞)⁻¹ ^ (p.2 + 1) else 0, fun _ => rfl⟩
  have h1 : requestKraftWeight (fun k => (req k).map fun p => p.2 + 1) =
      ∑' k, match req k with | some p => W p | none => 0 := by
    rw [requestKraftWeight]
    refine tsum_congr fun k => ?_
    cases hk : req k with
    | none => simp
    | some p =>
      obtain ⟨x, n⟩ := p
      simp [hW, hsound k x n hk]
  calc requestKraftWeight (fun k => (req k).map fun p => p.2 + 1)
      = ∑' k, match req k with | some p => W p | none => 0 := h1
    _ ≤ ∑' p, W p := requestKraftWeight_succ_le_one_of_isKraftFun_inj_le req W hinj
    _ = ∑' x : BitString, ∑' n : ℕ, W (x, n) := ENNReal.tsum_prod'
    _ = ∑' x : BitString, (2 : ℝ≥0∞)⁻¹ ^ F x := tsum_congr fun x => by
        simp only [hW]
        exact requestKraftWeight_succ_le_one_of_isKraftFun_geom (F x)
    _ ≤ 1 := requestKraftWeight_succ_le_one_of_isKraftFun_kraft_tsum hF

/-! ### Step 2: a prefix decompressor realising `F + 1` exactly -/

/-- The decompressor of `exists_exact_prefixDecompressor`: on the program `c` (the context is
ignored) search with `Nat.rfind` for the index `k` with `alloc k = some c` and output the string
of the request `req k`. -/
private def exists_exact_prefixDecompressor_map
    (req : ℕ → Option (BitString × ℕ)) (alloc : ℕ → Option BitString) : Map := fun pr =>
  (Nat.rfind fun k => Part.some (decide (alloc k = some pr.1))).bind
    fun k => (↑((req k).map Prod.fst) : Part BitString)

/-- Towards `exists_exact_prefixDecompressor`: the decompressor is
partial recursive when the request stream and the allocator are computable (the `rfind` is on
a decidable, computable predicate). -/
private lemma exists_exact_prefixDecompressor_partrec
    {req : ℕ → Option (BitString × ℕ)} {alloc : ℕ → Option BitString}
    (hreq : Computable req) (halloc : Computable alloc) :
    Partrec (exists_exact_prefixDecompressor_map req alloc) := by
  have hcheck : Computable fun q : (BitString × BitString) × ℕ =>
      decide (alloc q.2 = some q.1.1) :=
    (Primrec.eq.decide.to_comp : Computable₂ fun a b : Option BitString => decide (a = b)).comp
      (halloc.comp Computable.snd)
      (Computable.option_some.comp (Computable.fst.comp Computable.fst))
  have hout : Computable fun q : (BitString × BitString) × ℕ =>
      (req q.2).map Prod.fst :=
    Computable.option_map (hreq.comp Computable.snd) (Computable.fst.comp Computable.snd)
  unfold exists_exact_prefixDecompressor_map
  exact Partrec.bind (Partrec.rfind (Computable.to₂ hcheck).partrec₂)
    (Computable.ofOption hout).to₂

/-- Towards `exists_exact_prefixDecompressor`: a code allocated to two
indices contradicts the prefix clause of the allocator (with `cn = cm`), so `alloc` is injective
on the indices that receive a code. -/
private lemma exists_exact_prefixDecompressor_inj {alloc : ℕ → Option BitString}
    (hprefix : ∀ n m cn cm, alloc n = some cn → alloc m = some cm → n ≠ m →
      ¬ List.IsPrefix cn cm) :
    ∀ k k' c, alloc k = some c → alloc k' = some c → k = k' := by
  intro k k' c hk hk'
  by_contra hne
  exact hprefix k k' c c hk hk' hne (List.prefix_refl c)

/-- Towards `exists_exact_prefixDecompressor`: the decompressor produces
`x` from the program `c` (in any context) iff `c` is the code `alloc k` allocated to an index
`k` whose request has the string `x`. -/
private lemma exists_exact_prefixDecompressor_mem_iff
    {req : ℕ → Option (BitString × ℕ)} {alloc : ℕ → Option BitString}
    (hinj : ∀ k k' c, alloc k = some c → alloc k' = some c → k = k') {c y x : BitString} :
    x ∈ exists_exact_prefixDecompressor_map req alloc (c, y) ↔
      ∃ k, alloc k = some c ∧ (req k).map Prod.fst = some x := by
  unfold exists_exact_prefixDecompressor_map
  constructor
  · intro h
    obtain ⟨k, hk, hx⟩ := Part.mem_bind_iff.mp h
    refine ⟨k, ?_, Part.mem_coe.mp hx⟩
    simpa using Nat.rfind_spec hk
  · rintro ⟨k, hk, hx⟩
    refine Part.mem_bind_iff.mpr ⟨k, ?_, Part.mem_coe.mpr hx⟩
    refine Nat.mem_rfind.mpr ⟨by simp [hk], fun {m} hm => ?_⟩
    have hne : alloc m ≠ some c := fun hm' => absurd (hinj m k c hm' hk) hm.ne
    simp [hne]

/-- Towards `exists_exact_prefixDecompressor`: the decompressor is a
prefix machine, because two halting programs are codes allocated to two indices, which are either
equal (so the codes are equal) or have prefix-incomparable codes. -/
private lemma exists_exact_prefixDecompressor_isPrefixMachine
    {req : ℕ → Option (BitString × ℕ)} {alloc : ℕ → Option BitString}
    (hprefix : ∀ n m cn cm, alloc n = some cn → alloc m = some cm → n ≠ m →
      ¬ List.IsPrefix cn cm) :
    IsPrefixMachine (exists_exact_prefixDecompressor_map req alloc) := by
  have hinj := exists_exact_prefixDecompressor_inj hprefix
  intro y p hp q hq hpq
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hp
  obtain ⟨x', hx'⟩ := Part.dom_iff_mem.mp hq
  obtain ⟨k, hk, -⟩ := (exists_exact_prefixDecompressor_mem_iff hinj).mp hx
  obtain ⟨k', hk', -⟩ := (exists_exact_prefixDecompressor_mem_iff hinj).mp hx'
  by_cases hkk : k = k'
  · subst hkk
    exact Option.some.inj (hk.symm.trans hk')
  · exact absurd hpq (hprefix k k' p q hk hk' hkk)

/-- Towards `exists_exact_prefixDecompressor`: the exact complexity.
Every program of `x` is a code `alloc k` with `req k = some (x, n)`, hence of length `n + 1` with
`F x ≤ n`; the request `(x, F x)` of the stream gives a program of length `F x + 1`. -/
private lemma exists_exact_prefixDecompressor_KPPlain
    {F : BitString → ℕ} {req : ℕ → Option (BitString × ℕ)} {alloc : ℕ → Option BitString}
    (hsound : ∀ k x n, req k = some (x, n) → F x ≤ n)
    (hexh : ∀ x n, F x ≤ n → ∃ k, req k = some (x, n))
    (halen : ∀ k l, (req k).map (fun p => p.2 + 1) = some l →
      ∃ c, alloc k = some c ∧ c.length = l)
    (hinj : ∀ k k' c, alloc k = some c → alloc k' = some c → k = k') (x : BitString) :
    KPPlain (exists_exact_prefixDecompressor_map req alloc) x = ((F x + 1 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · obtain ⟨k, hk⟩ := hexh x (F x) le_rfl
    obtain ⟨c, hc, hclen⟩ := halen k (F x + 1) (by simp [hk])
    have hprod : produces (exists_exact_prefixDecompressor_map req alloc) c [] x :=
      (exists_exact_prefixDecompressor_mem_iff hinj).mpr ⟨k, hc, by simp [hk]⟩
    calc KPPlain (exists_exact_prefixDecompressor_map req alloc) x
        ≤ (programLength c : ℕ∞) := KP_le_programLength_of_produces hprod
      _ = ((F x + 1 : ℕ) : ℕ∞) := by rw [programLength, hclen]
  · refine le_sInf ?_
    rintro n ⟨p, hp, rfl⟩
    obtain ⟨k, hk, hkx⟩ := (exists_exact_prefixDecompressor_mem_iff hinj).mp hp
    obtain ⟨⟨x', m⟩, hreq, hfst⟩ := Option.map_eq_some_iff.mp hkx
    have hx' : x' = x := hfst
    rw [hx'] at hreq
    obtain ⟨c, hc, hclen⟩ := halen k (m + 1) (by simp [hreq])
    obtain rfl : c = p := Option.some.inj (hc.symm.trans hk)
    have hFm := hsound k x m hreq
    exact_mod_cast (by omega : F x + 1 ≤ c.length)

/-- For every entropy function `F` there is a prefix decompressor `D` with
`KPPlain D x = F x + 1` for every `x` (and the same programs in every context).

Proof sketch: take `req` from `exists_requestStream_of_overgraph` and `alloc` from
`exists_online_prefixFree_of_kraft_le_one` for the lengths `n + 1`
(`requestKraftWeight_succ_le_one_of_isKraftFun`). Define
`D (c, y) := (Nat.rfind fun k => alloc k = some c).bind fun k => (req k).map Prod.fst`
(the `rfind` is on a decidable predicate, so `D` is `Partrec`; the context `y` is ignored).
Prefix-freeness: distinct halting programs are codes allocated to distinct `k`, and the
allocator keeps them prefix-incomparable; a code allocated twice contradicts the same clause
with `cn = cm`. Exactness: `D` produces `x` from `c` iff `c = alloc k` with `req k = some (x, n)`,
`F x ≤ n`, and `|c| = n + 1`; the minimum over `n ≥ F x` is `F x + 1`, attained at the request
`(x, F x)`, which the stream lists. -/
theorem exists_exact_prefixDecompressor {F : BitString → ℕ} (hF : IsEntropyFun F) :
    ∃ D : Map, IsPrefixDecompressor D ∧ ∀ x, KPPlain D x = ((F x + 1 : ℕ) : ℕ∞) := by
  obtain ⟨req, hreqc, hsound, hexh, hreqinj⟩ := exists_requestStream_of_overgraph hF.re
  have hlenc : IsComputableRequestStream fun k => (req k).map fun p => p.2 + 1 :=
    Computable.option_map hreqc (Computable.succ.comp (Computable.snd.comp Computable.snd))
  obtain ⟨alloc, hallocc, halen, -, hprefix⟩ :=
    exists_online_prefixFree_of_kraft_le_one _ hlenc
      (requestKraftWeight_succ_le_one_of_isKraftFun hF.kraft req hsound hreqinj)
  exact ⟨exists_exact_prefixDecompressor_map req alloc,
    ⟨exists_exact_prefixDecompressor_partrec hreqc hallocc,
      exists_exact_prefixDecompressor_isPrefixMachine hprefix⟩,
    exists_exact_prefixDecompressor_KPPlain hsound hexh halen
      (exists_exact_prefixDecompressor_inj hprefix)⟩

/-! ### Step 3: the exact complexity of a tagged union -/

/-- Every program of `taggedUnion M` producing `x` in context `y` is `natCode i ++ q` with
`M i` producing `x` from `q`; the length bookkeeping is `i + 1 + |q|`.

Proof sketch: `taggedUnion_dom_decompose` gives the shape `natCode i ++ q`, and the evaluation
equation of `taggedUnion` on such a program (as in `taggedUnion_produces_natCode`) identifies
the output with that of `M i`. -/
theorem produces_taggedUnion_iff {M : ℕ → Map} {p y x : BitString} :
    produces (taggedUnion M) p y x ↔ ∃ i q, p = natCode i ++ q ∧ produces (M i) q y x := by
  constructor
  · intro h
    have hdom : (taggedUnion M (p, y)).Dom := Part.dom_iff_mem.mpr ⟨x, h⟩
    obtain ⟨i, q, hp, _⟩ := taggedUnion_dom_decompose hdom
    use i, q, hp
    subst hp
    have hlt : i < (natCode i ++ q).length := by
      simp only [List.length_append, length_natCode]; omega
    have heq : taggedUnion M (natCode i ++ q, y) = M i (q, y) := by
      simp only [taggedUnion, length_takeWhile_natCode_append, drop_natCode_append]
      rw [ite_eq_left hlt]
    change x ∈ taggedUnion M (natCode i ++ q, y) at h
    change x ∈ M i (q, y)
    rwa [heq] at h
  · intro ⟨i, q, hp, hq⟩
    rw [hp]
    exact taggedUnion_produces_natCode hq

/-- The exact prefix complexity of a tagged union:
`KP (taggedUnion M) x y = ⨅ i, KP (M i) x y + (i + 1)`.

Proof sketch: `≤` is `taggedUnion_KP_le_of_produces` over all `i` and all programs of `M i`;
`≥` is `produces_taggedUnion_iff` applied to each candidate length of the union
(`KP` is the `sInf` of `candidateLengths`, see `KP_eq_condK`). -/
theorem KP_taggedUnion_eq_iInf (M : ℕ → Map) (x y : BitString) :
    KP (taggedUnion M) x y = ⨅ i : ℕ, KP (M i) x y + ((i + 1 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    by_cases h : KP (M i) x y = ⊤
    · rw [h, top_add]; exact le_top
    · rcases KP_mem_candidateLengths_of_ne_top h with ⟨q, hq, hqlen⟩
      have hle := taggedUnion_KP_le_of_produces hq
      rw [← hqlen]
      exact hle.trans (by norm_cast; linarith)
  · by_cases h : KP (taggedUnion M) x y = ⊤
    · rw [h]; exact le_top
    · rcases KP_mem_candidateLengths_of_ne_top h with ⟨p, hp, hplen⟩
      rcases produces_taggedUnion_iff.mp hp with ⟨i, q, rfl, hq⟩
      have hle := iInf_le (fun i => KP (M i) x y + ((i + 1 : ℕ) : ℕ∞)) i
      rw [← hplen]
      have hlen : programLength (natCode i ++ q) = i + 1 + q.length := by
        simp [programLength, List.length_append, length_natCode]
      rw [hlen]
      apply le_trans hle
      have hkp := KP_le_programLength_of_produces hq
      have hadd : ((i + 1 + q.length : ℕ) : ℕ∞) = (q.length : ℕ∞) + ((i + 1 : ℕ) : ℕ∞) := by
        push_cast
        rw [add_comm]
      rw [hadd]
      exact add_le_add hkp (le_refl _)

/-! ### Step 4: the optimal prefix decompressor realising `min (K + 5) (F + 3)` -/

/-- A prefix decompressor dominated by an optimal one up to a constant is itself optimal.

Proof sketch: for any prefix decompressor `N`, `KP U ≤ KP N + c_N` by optimality of `U`, so
`KP U' ≤ KP U + c ≤ KP N + (c_N + c)`. -/
theorem isOptimalPrefixConditional_of_KP_le {U U' : Map} (hU : IsOptimalPrefixConditional U)
    (hU' : IsPrefixDecompressor U') (c : ℕ) (h : ∀ x y, KP U' x y ≤ KP U x y + (c : ℕ∞)) :
    IsOptimalPrefixConditional U' := by
  refine ⟨hU', fun N hN => ?_⟩
  obtain ⟨cN, hcN⟩ := hU.2 N hN
  refine ⟨cN + c, fun x y => ?_⟩
  calc KP U' x y ≤ KP U x y + c := h x y
    _ ≤ KP N x y + cN + c := add_le_add (hcN x y) le_rfl
    _ = KP N x y + ((cN + c : ℕ) : ℕ∞) := by rw [Nat.cast_add, add_assoc]

/-- The three-member family `M 4 = U`, `M 1 = D`, `M i = ∅` otherwise, is uniformly partial
recursive when `U` and `D` are decompressors (so `taggedUnion_isDecompressor_of_uniform`
applies).

Proof sketch: the family is `fun t => if t.1 = 4 then U t.2 else if t.1 = 1 then D t.2 else
Part.none`; both tests are decidable (`Primrec.eq`), and `Partrec` is closed under `cond`
with computable guards (`Partrec.cond`, or `Partrec.ite` via `PrimrecPred`). -/
theorem minFamily_uniform_partrec {U D : Map} (hU : isDecompressor U) (hD : isDecompressor D) :
    Partrec (fun t : ℕ × BitString × BitString =>
      (fun i : ℕ => if i = 4 then U else if i = 1 then D else fun _ => Part.none) t.1 t.2) := by
  have h_eq4 : Computable fun t : ℕ × BitString × BitString => decide (t.1 = 4) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.fst (Primrec.const 4))).to_comp
  have h_eq1 : Computable fun t : ℕ × BitString × BitString => decide (t.1 = 1) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.fst (Primrec.const 1))).to_comp
  have H : Partrec (fun t : ℕ × BitString × BitString =>
    cond (t.1 == 4) (U t.2) (cond (t.1 == 1) (D t.2) Part.none)) := by
    apply Partrec.cond
    · exact h_eq4
    · exact hU.comp Computable.snd
    · apply Partrec.cond
      · exact h_eq1
      · exact hD.comp Computable.snd
      · exact Partrec.none
  exact H.of_eq (fun t => by
    by_cases h1 : t.1 = 4
    · simp [h1]
    · by_cases h2 : t.1 = 1
      · simp [h2]
      · simp [h1, h2])

/-- Towards `exists_isOptimalPrefixConditional_min`: every member of
the three-member family `M 4 = U`, `M 1 = D`, `M i = fun _ => Part.none` otherwise is a prefix
machine when `U` and `D` are. -/
private lemma exists_isOptimalPrefixConditional_min_step1_prefixMachine {U D : Map}
    (hU : IsPrefixMachine U) (hD : IsPrefixMachine D) (i : ℕ) :
    IsPrefixMachine
      ((fun i : ℕ => if i = 4 then U else if i = 1 then D else fun _ => Part.none) i) := by
  by_cases h4 : i = 4
  · simpa [h4] using hU
  · by_cases h1 : i = 1
    · simpa [h4, h1] using hD
    · simpa [h4, h1] using isPrefixMachine_const_none

/-- Towards `exists_isOptimalPrefixConditional_min`: the never-halting
map has infinite conditional prefix complexity, i.e. the members `M i`, `i ∉ {1, 4}`, of the
family contribute `⊤` to the infimum of `KP_taggedUnion_eq_iInf`. -/
private lemma exists_isOptimalPrefixConditional_min_step2_KP_none (x y : BitString) :
    KP (fun _ => Part.none) x y = ⊤ :=
  KP_eq_top_of_no_program fun _ => Part.notMem_none x

/-- Towards `exists_isOptimalPrefixConditional_min`: the complexity of
the tagged union of the three-member family is
`KP (taggedUnion M) x y = min (KP U x y + 5) (KP D x y + 2)`
(`KP_taggedUnion_eq_iInf`; the other members contribute `⊤`). -/
private lemma exists_isOptimalPrefixConditional_min_step3_KP_taggedUnion (U D : Map)
    (x y : BitString) :
    KP (taggedUnion fun i : ℕ => if i = 4 then U else if i = 1 then D else fun _ => Part.none)
        x y = min (KP U x y + 5) (KP D x y + 2) := by
  rw [KP_taggedUnion_eq_iInf]
  apply le_antisymm
  · exact le_min ((iInf_le _ 4).trans (by simp)) ((iInf_le _ 1).trans (by simp))
  · refine le_iInf fun i => ?_
    by_cases h4 : i = 4
    · subst h4
      simp
    · by_cases h1 : i = 1
      · subst h1
        simp
      · simp [h4, h1, exists_isOptimalPrefixConditional_min_step2_KP_none]

/-- **Exact `min` construction.** For every optimal prefix decompressor `U` and every entropy
function `F` there is an optimal prefix decompressor `U'` with
`KPPlain U' x = min (KPPlain U x + 5) (F x + 3)` for every `x`.

Proof sketch: let `D` be the decompressor of `exists_exact_prefixDecompressor` and
`U' := taggedUnion M` for the family `M 4 = U`, `M 1 = D`, `M i = fun _ => Part.none`
otherwise. `taggedUnion_isPrefixMachine` and `taggedUnion_isDecompressor_of_uniform`
(`minFamily_uniform_partrec`) make `U'` a prefix decompressor. `KP_taggedUnion_eq_iInf` gives
`KP U' x y = min (KP U x y + 5) (KP D x y + 2)` (the other members contribute `⊤`), hence
`KPPlain U' x = min (KPPlain U x + 5) (F x + 1 + 2)`. Optimality is
`isOptimalPrefixConditional_of_KP_le` with the bound `KP U' ≤ KP U + 5`. -/
theorem exists_isOptimalPrefixConditional_min {U : Map} (hU : IsOptimalPrefixConditional U)
    {F : BitString → ℕ} (hF : IsEntropyFun F) :
    ∃ U' : Map, IsOptimalPrefixConditional U' ∧
      ∀ x, KPPlain U' x = min (KPPlain U x + 5) ((F x + 3 : ℕ) : ℕ∞) := by
  obtain ⟨D, hD, hDF⟩ := exists_exact_prefixDecompressor hF
  have hpd : IsPrefixDecompressor
      (taggedUnion fun i : ℕ => if i = 4 then U else if i = 1 then D else fun _ => Part.none) :=
    ⟨taggedUnion_isDecompressor_of_uniform
        (minFamily_uniform_partrec hU.isDecompressor hD.isDecompressor),
      taggedUnion_isPrefixMachine
        (exists_isOptimalPrefixConditional_min_step1_prefixMachine hU.isPrefixMachine
          hD.isPrefixMachine)⟩
  refine ⟨_, isOptimalPrefixConditional_of_KP_le hU hpd 5 fun x y => ?_, fun x => ?_⟩
  · rw [exists_isOptimalPrefixConditional_min_step3_KP_taggedUnion]
    exact min_le_left _ _
  · have h3 : ((F x + 1 : ℕ) : ℕ∞) + 2 = ((F x + 3 : ℕ) : ℕ∞) := by
      push_cast
      ring
    rw [KPPlain_eq_KP, exists_isOptimalPrefixConditional_min_step3_KP_taggedUnion,
      ← KPPlain_eq_KP, ← KPPlain_eq_KP, hDF x, h3]

/-! ### `KPPlain` of an optimal prefix decompressor is an entropy function -/

/-- The finite Kraft sums of `(KPPlain U ·).toNat` are at most `1` for an optimal prefix
decompressor `U`.

Proof sketch: `KPPlain U x ≠ ⊤` (`KPPlain_ne_top_of_isOptimalPrefixConditional`), so
`(2 : ℝ)⁻¹ ^ (KPPlain U x).toNat = (complexityWeight (KPPlain U x)).toReal`; a finite partial
sum of the `tsum` in `KPPlain_kraft_sum_le_one` is bounded by the `tsum`
(`ENNReal.sum_le_tsum`), and `ENNReal.toReal` is monotone. -/
theorem KPPlain_toNat_kraft {U : Map} (hU : IsOptimalPrefixConditional U) :
    IsKraftFun fun x => (KPPlain U x).toNat := by
  intro S
  have hterm : ∀ x, complexityWeight (KPPlain U x) = (2 : ℝ≥0∞)⁻¹ ^ (KPPlain U x).toNat :=
    fun x => by
      rw [← complexityWeight_coe,
        ENat.natCast_toNat (KPPlain_ne_top_of_isOptimalPrefixConditional hU x)]
  have hfin : ∀ x ∈ S, complexityWeight (KPPlain U x) ≠ ⊤ := fun x _ => by
    rw [hterm]
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero)
  have hle : ∑ x ∈ S, complexityWeight (KPPlain U x) ≤ 1 :=
    (ENNReal.sum_le_tsum S).trans (KPPlain_kraft_sum_le_one U hU.1)
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top hle
  rw [ENNReal.toReal_sum hfin, ENNReal.toReal_one] at hreal
  refine le_of_eq_of_le (Finset.sum_congr rfl fun x _ => ?_) hreal
  rw [hterm, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]


/-- `(KPPlain U x).toNat ≤ n` iff some program of length `≤ n` produces `x` from `[]`. -/
private lemma REPred_KPPlain_toNat_le_aux1 {U : Map} (hU : IsOptimalPrefixConditional U)
    (x : BitString) (n : ℕ) :
    (KPPlain U x).toNat ≤ n ↔ ∃ p ∈ boundedPrograms n, produces U p [] x := by
  have hne : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_isOptimalPrefixConditional hU x
  have h1 : (KPPlain U x).toNat ≤ n ↔ KPPlain U x ≤ (n : ℕ∞) := by
    refine ⟨fun h => ?_, ENat.toNat_le_of_le_natCast⟩
    calc KPPlain U x = ((KPPlain U x).toNat : ℕ∞) := (ENat.natCast_toNat hne).symm
      _ ≤ (n : ℕ∞) := by exact_mod_cast h
  refine h1.trans ?_
  refine (condK_le_iff U x [] n).trans ?_
  exact ⟨fun ⟨p, hlen, hprod⟩ => ⟨p, (mem_boundedPrograms_iff p n).mpr hlen, hprod⟩,
    fun ⟨p, hmem, hprod⟩ => ⟨p, (mem_boundedPrograms_iff p n).mp hmem, hprod⟩⟩

/-- Bounded dovetailing over `boundedPrograms n` against `U`: this relation is c.e. -/
private lemma REPred_KPPlain_toNat_le_aux2 {U : Map} (hU : IsOptimalPrefixConditional U) :
    IsRE (fun a : BitString × ℕ => ∃ p ∈ boundedPrograms a.2, produces U p [] a.1) := by
  have hgraph : IsRE (fun p : (BitString × BitString) × BitString => p.2 ∈ U p.1) :=
    Partrec.graphIsRe U hU.isDecompressor
  have hg : Computable (fun z : (BitString × ℕ) × BitString =>
      (((z.2, ([] : BitString)) : BitString × BitString), z.1.1)) :=
    Computable.pair (Computable.pair Computable.snd (Computable.const ([] : BitString)))
      (Computable.fst.comp Computable.fst)
  have hR : IsRE (fun z : (BitString × ℕ) × BitString => produces U z.2 [] z.1.1) :=
    IsRE.comp_computable (R := fun p : (BitString × BitString) × BitString => p.2 ∈ U p.1)
      hgraph hg
  exact IsRE.existsInList
    (R := fun (a : BitString × ℕ) (p : BitString) => produces U p [] a.1) hR
    (fun a => boundedPrograms a.2) (Computable.boundedPrograms.comp Computable.snd)

/-- The overgraph `{(x, n) | (KPPlain U x).toNat ≤ n}` is computably enumerable for a prefix
decompressor `U`.

Proof sketch: `(KPPlain U x).toNat ≤ n` iff some program `p` of length `≤ n` produces `x`
(finiteness of `KPPlain U x` from optimality). Dovetail the finitely many programs of length
`≤ n` against `U`: `REPred` is closed under bounded existential quantification over a
`List` (`List.range`-style enumeration of `BitString`s of length `≤ n`) and under the halting
predicate `x ∈ U (p, [])` of a `Partrec` map (`Partrec.dom_re` after `Part.assert`).
Compare `condK_le_isRE` in `Complexity/Properties.lean`, which proves the analogous statement
for plain complexity, and `isRE_plainK_le` in `Interface/Dovetailing.lean`. -/
theorem REPred_KPPlain_toNat_le {U : Map} (hU : IsOptimalPrefixConditional U) :
    HasREOvergraph fun x => (KPPlain U x).toNat := by
  change REPred fun p : BitString × ℕ => (KPPlain U p.1).toNat ≤ p.2
  obtain ⟨f, hf, hdom⟩ := REPred_KPPlain_toNat_le_aux2 hU
  exact (Partrec.dom_re hf).of_eq fun a =>
    (hdom a).trans (REPred_KPPlain_toNat_le_aux1 hU a.1 a.2).symm

/-- `(KPPlain U ·).toNat` is an entropy function for an optimal prefix decompressor `U`. -/
theorem isEntropyFun_KPPlain_toNat {U : Map} (hU : IsOptimalPrefixConditional U) :
    IsEntropyFun fun x => (KPPlain U x).toNat :=
  ⟨KPPlain_toNat_kraft hU, REPred_KPPlain_toNat_le hU⟩

/-- Helper lemma for `exists_isOptimalPrefixConditional_min_toNat`. -/
private lemma exists_isOptimalPrefixConditional_min_toNat_step_toNat_min {m n : ℕ∞} (hm : m ≠ ⊤)
    (hn : n ≠ ⊤) :
    (min m n).toNat = min m.toNat n.toNat := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  have h : min (↑m : ℕ∞) (↑n : ℕ∞) = ↑(min m n) := by exact (WithTop.coe_inf _ _).symm
  rw [h]
  rw [ENat.toNat_natCast, ENat.toNat_natCast, ENat.toNat_natCast]

/-- The exact `min` construction in `ℕ`-valued form: `(KPPlain U' x).toNat =
min ((KPPlain U x).toNat + 5) (F x + 3)`.

Proof sketch: `exists_isOptimalPrefixConditional_min` and
`KPPlain_ne_top_of_isOptimalPrefixConditional` for `U` and `U'`; `ENat.toNat` commutes with
`min` and with `+ (c : ℕ)` on finite values (`ENat.toNat_add`, `ENat.toNat_coe`). -/
theorem exists_isOptimalPrefixConditional_min_toNat {U : Map} (hU : IsOptimalPrefixConditional U)
    {F : BitString → ℕ} (hF : IsEntropyFun F) :
    ∃ U' : Map, IsOptimalPrefixConditional U' ∧
      ∀ x, (KPPlain U' x).toNat = min ((KPPlain U x).toNat + 5) (F x + 3) := by
  obtain ⟨U', hU', hmin⟩ := exists_isOptimalPrefixConditional_min hU hF
  use U', hU'
  intro x
  rw [hmin x, exists_isOptimalPrefixConditional_min_toNat_step_toNat_min]
  · rw [ENat.toNat_add (KPPlain_ne_top_of_isOptimalPrefixConditional hU x) (by simp)]
    rfl
  · intro h_add
    have h1 := KPPlain_ne_top_of_isOptimalPrefixConditional hU x
    have h2 : (5 : ℕ∞) ≠ ⊤ := WithTop.natCast_ne_top 5
    exact (WithTop.add_ne_top.mpr ⟨h1, h2⟩) h_add
  · exact ENat.natCast_ne_top _

end Kolmogorov
