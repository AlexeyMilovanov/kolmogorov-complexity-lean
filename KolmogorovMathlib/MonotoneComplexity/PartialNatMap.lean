/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.MonotoneComplexity.Stream
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# Continuous partial maps from streams to naturals

The flat domain `ℕ⊥` of partial natural values, presented as a total map on streams whose value
persists along extensions: `partialNatLowerGraph` is the graph,
`IsContinuousPartialNatMap` the continuity condition and `IsComputablePartialNatMap` its
effective form, requiring the lower graph to be recursively enumerable. The basic facts are that
such a map is single-valued on comparable streams (`value_eq_of_le`,
`value_unique_of_compatible`), that a value on an infinite sequence is already attained on a
finite prefix (`exists_finite_witness`), that the lower graph determines the map
(`continuousPartialNatMap_ext_of_lowerGraph_eq`), and that constants are computable.
-/

namespace Kolmogorov

/-- SUV's flat domain `ℕ⊥` of partial natural values, as a total map on `E`. -/
def partialNatLowerGraph (f : BitStream → Option ℕ) (x : BitString) (n : ℕ) : Prop :=
  f (.finite x) = some n

/-- A partial map from streams to naturals whose value, once defined, persists along extensions and
is already determined by a finite prefix. -/
def IsContinuousPartialNatMap (f : BitStream → Option ℕ) : Prop :=
  (∀ s t : BitStream, s ≤ t → ∀ n, f s = some n → f t = some n) ∧
  (∀ w : CantorSeq, ∀ n, f (.infinite w) = some n →
      ∃ k, f (.finite (cantorPrefix w k)) = some n)

/-- A continuous partial map from streams to naturals whose lower graph is recursively enumerable.
-/
def IsComputablePartialNatMap (f : BitStream → Option ℕ) : Prop :=
  IsContinuousPartialNatMap f ∧
    IsRE fun q : BitString × ℕ => partialNatLowerGraph f q.1 q.2

/-- A continuous partial map takes the same value on comparable streams where both are defined. -/
lemma IsContinuousPartialNatMap.value_eq_of_le {f : BitStream → Option ℕ}
    (hf : IsContinuousPartialNatMap f) {s t : BitStream} (hst : s ≤ t) {n m : ℕ}
    (hn : f s = some n) (hm : f t = some m) : n = m := by
  have h1 : f t = some n := hf.1 s t hst n hn
  simpa using h1.symm.trans hm

/-- A continuous partial map takes the same value on two prefixes of a common string. -/
lemma IsContinuousPartialNatMap.value_unique_of_compatible
    {f : BitStream → Option ℕ} (hf : IsContinuousPartialNatMap f)
    {x y z : BitString} (hx : x <+: z) (hy : y <+: z) {n m : ℕ}
    (hn : f (.finite x) = some n) (hm : f (.finite y) = some m) : n = m := by
  have h1 : f (.finite z) = some n := hf.1 _ _ hx n hn
  have h2 : f (.finite z) = some m := hf.1 _ _ hy m hm
  simpa using h1.symm.trans h2

/-- A value taken on an infinite sequence is already taken on one of its finite prefixes. -/
lemma IsContinuousPartialNatMap.exists_finite_witness {f : BitStream → Option ℕ}
    (hf : IsContinuousPartialNatMap f) {w : CantorSeq} {n : ℕ}
    (hn : f (.infinite w) = some n) :
    ∃ x : BitString, BitStream.finite x ≤ .infinite w ∧ f (.finite x) = some n := by
  obtain ⟨k, hk⟩ := hf.2 w n hn
  have H : BitStream.finite (cantorPrefix w k) ≤ .infinite w := by
    change IsCantorPrefix _ _
    rw [isCantorPrefix_iff_cantorPrefix_eq]
    simp
  exact ⟨cantorPrefix w k, H, hk⟩

/-- A continuous partial map is determined by its lower graph. -/
lemma continuousPartialNatMap_ext_of_lowerGraph_eq {f g : BitStream → Option ℕ}
    (hf : IsContinuousPartialNatMap f) (hg : IsContinuousPartialNatMap g)
    (h_eq : ∀ x n, partialNatLowerGraph f x n ↔ partialNatLowerGraph g x n) :
    f = g := by
  ext s
  cases s with
  | finite x =>
    rcases hf_val : f (.finite x) with _ | n
    · rcases hg_val : g (.finite x) with _ | m
      · rfl
      · have : partialNatLowerGraph g x m := hg_val
        rw [← h_eq x m] at this
        have : f (.finite x) = some m := this
        rw [this] at hf_val
        contradiction
    · have : partialNatLowerGraph f x n := hf_val
      rw [h_eq x n] at this
      rcases hg_val : g (.finite x) with _ | m
      · have : g (.finite x) = some n := this
        rw [this] at hg_val
        contradiction
      · have eq1 : g (.finite x) = some n := this
        rw [eq1] at hg_val
        injection hg_val with h_n_m
        rw [h_n_m]
  | infinite w =>
    rcases hf_val : f (.infinite w) with _ | n
    · rcases hg_val : g (.infinite w) with _ | m
      · rfl
      · obtain ⟨x, hxw, hxm⟩ := hg.exists_finite_witness hg_val
        have : partialNatLowerGraph g x m := hxm
        rw [← h_eq x m] at this
        have H := hf.1 (.finite x) (.infinite w) hxw m this
        rw [H] at hf_val
        contradiction
    · obtain ⟨x, hxw, hxn⟩ := hf.exists_finite_witness hf_val
      have : partialNatLowerGraph f x n := hxn
      rw [h_eq x n] at this
      have H := hg.1 (.finite x) (.infinite w) hxw n this
      rw [H]

/-- A constant map from streams to naturals is a computable partial map. -/
lemma isComputablePartialNatMap_const (c : ℕ) :
    IsComputablePartialNatMap (fun _ => some c) := by
  constructor
  · constructor
    · intro s t _ n hn
      exact hn
    · intro w n hn
      exact ⟨0, hn⟩
  · have H : IsRE (fun (q : BitString × ℕ) => q.2 = c) := by
      have : (fun (q : BitString × ℕ) => q.2 = c)
          = (fun q => q.2 ∈ (Part.some c : Part ℕ)) := by
        ext q
        simp [Part.mem_some_iff, eq_comm]
      rw [this]
      apply Partrec.graphIsRe (fun (_ : BitString) => (Part.some c : Part ℕ))
        (Computable.partrec (Computable.const c))
    have eq1 : (fun (q : BitString × ℕ) => partialNatLowerGraph (fun _ => some c) q.1 q.2)
        = (fun q => q.2 = c) := by
      ext q
      simp [partialNatLowerGraph, eq_comm]
    rwa [eq1]

end Kolmogorov
