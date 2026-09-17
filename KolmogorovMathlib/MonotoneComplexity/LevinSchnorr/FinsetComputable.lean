/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Computability.Partrec
import Mathlib.Logic.Equiv.Finset
import Mathlib.Tactic
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.FinsetRestriction

/-!
# Computability of the `Finset ℕ` coding

`Mathlib`'s `Primcodable (Finset ℕ)` instance is `Primcodable.ofDenumerable`, so the code of a
finite set is its **rank** in the `Denumerable` enumeration, not the `Encodable` code of its
sorted list.  Consequently neither

* `Computable fun F : Finset ℕ => F.sort (· ≤ ·)`, nor
* `Computable fun i : ℕ => Finset.range i`

is available off the shelf, and both are needed by SUV Problems 144 and 145 (p. 149).

This file supplies them.  The point is that `Denumerable.finset` is built from the
`lower'`/`raise'` pair of `Mathlib/Logic/Equiv/Finset.lean`, so the sorted list of `F` is
recovered from its rank *primitively recursively*:

`(Denumerable.ofNat (Finset ℕ) n).sort (· ≤ ·) = Denumerable.raise' (ofNat (List ℕ) n) 0`.

The only work is that `Denumerable.raise'` recurses with a moving accumulator; the shift lemma
`raise'_eq_map_add` turns it into the plain `List.foldr` `raiseFold`, which `Primrec.list_foldr`
handles directly.

## Main results

* `Kolmogorov.sort_ofNat_finset` — the sorted list from the rank;
* `Kolmogorov.primrec_finsetSort`, `Kolmogorov.computable_finsetSort` —
  `F ↦ F.sort (· ≤ ·)` is primitive recursive;
* `Kolmogorov.primrec_finsetRange`, `Kolmogorov.computable_finsetRange` —
  `i ↦ Finset.range i` is primitive recursive;
* `Kolmogorov.primrec_restrictStr`, `Kolmogorov.computable_restrictStr` — the restriction
  `(F, x) ↦ x(F)` of `LevinSchnorr/FinsetRestriction.lean` is primitive recursive;
* `Kolmogorov.primrec_finsetCode`, `Kolmogorov.computable_finsetCode` — the canonical code of
  a finite set (`MonotoneComplexity/SharedCoding.lean`) is primitive recursive.
-/

namespace Kolmogorov

/-! ### `Denumerable.raise'` as a `foldr` -/

/-- `Denumerable.raise'` at a shifted base point is the shift of `Denumerable.raise'` at `0`. -/
lemma raise'_eq_map_add (l : List ℕ) (n : ℕ) :
    Denumerable.raise' l n = (Denumerable.raise' l 0).map (· + n) := by
  induction l generalizing n with
  | nil => rfl
  | cons m t ih =>
    have e1 : Denumerable.raise' (m :: t) n = (m + n) :: Denumerable.raise' t (m + n + 1) := rfl
    have e2 : Denumerable.raise' (m :: t) 0 = m :: Denumerable.raise' t (m + 1) := rfl
    rw [e1, e2, List.map_cons, ih (m + n + 1), ih (m + 1), List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply]
    omega

/-- `Denumerable.raise'` at base point `0`, written as a plain `List.foldr`. -/
def raiseFold (l : List ℕ) : List ℕ :=
  l.foldr (fun m s => m :: s.map (· + (m + 1))) []

/-- `raiseFold` computes `Denumerable.raise' l 0`. -/
lemma raiseFold_eq_raise' (l : List ℕ) : raiseFold l = Denumerable.raise' l 0 := by
  induction l with
  | nil => rfl
  | cons m t ih =>
    have e2 : Denumerable.raise' (m :: t) 0 = m :: Denumerable.raise' t (m + 1) := rfl
    have e3 : raiseFold (m :: t) = m :: (raiseFold t).map (· + (m + 1)) := rfl
    rw [e3, ih, e2, raise'_eq_map_add t (m + 1)]

/-- `raiseFold` is primitive recursive. -/
lemma primrec_raiseFold : Primrec raiseFold := by
  have h : Primrec₂ fun (_ : List ℕ) (p : ℕ × List ℕ) => p.1 :: p.2.map (· + (p.1 + 1)) :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.nat_add.comp Primrec.snd
          (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))))
  exact (Primrec.list_foldr Primrec.id (Primrec.const ([] : List ℕ)) h).of_eq fun _ => rfl

/-! ### The sorted list of a finite set of naturals -/

/-- The `Denumerable (Finset ℕ)` decoding is `Denumerable.raise'Finset` of the decoded list. -/
lemma ofNat_finset_eq_raise'Finset (n : ℕ) :
    Denumerable.ofNat (Finset ℕ) n
      = Denumerable.raise'Finset (Denumerable.ofNat (List ℕ) n) 0 := by
  have h : (Denumerable.eqv ℕ).symm.toEmbedding = Function.Embedding.refl ℕ := by
    ext m; rfl
  have h2 : Denumerable.ofNat (Finset ℕ) n
      = Finset.map (Denumerable.eqv ℕ).symm.toEmbedding
        (Denumerable.raise'Finset (Denumerable.ofNat (List ℕ) n) 0) := rfl
  rw [h2, h, Finset.map_refl]

/-- SUV p. 149, the plumbing: the sorted list of the `n`-th finite set of naturals is
`Denumerable.raise'` of the `n`-th list of naturals. -/
theorem sort_ofNat_finset (n : ℕ) :
    (Denumerable.ofNat (Finset ℕ) n).sort (· ≤ ·)
      = Denumerable.raise' (Denumerable.ofNat (List ℕ) n) 0 := by
  have hnd : (Denumerable.raise' (Denumerable.ofNat (List ℕ) n) 0).Nodup :=
    (Denumerable.raise'_sorted _ _).nodup
  have hfs : Denumerable.raise'Finset (Denumerable.ofNat (List ℕ) n) 0
      = (Denumerable.raise' (Denumerable.ofNat (List ℕ) n) 0).toFinset := List.toFinset_eq hnd
  rw [ofNat_finset_eq_raise'Finset, hfs]
  exact (List.toFinset_sort _ hnd).2 (Denumerable.raise'_sorted _ _).sortedLE.pairwise

/-- SUV p. 149, the plumbing: `F ↦ F.sort (· ≤ ·)` is primitive recursive. -/
theorem primrec_finsetSort : Primrec fun F : Finset ℕ => F.sort (· ≤ ·) :=
  Primrec.ofNat_iff.2 <|
    (primrec_raiseFold.comp (Primrec.ofNat (List ℕ))).of_eq fun n => by
      rw [raiseFold_eq_raise', ← sort_ofNat_finset]

/-- SUV p. 149, the plumbing: `F ↦ F.sort (· ≤ ·)` is computable. -/
theorem computable_finsetSort : Computable fun F : Finset ℕ => F.sort (· ≤ ·) :=
  primrec_finsetSort.to_comp

/-! ### The initial segments `Finset.range i` -/

/-- `Denumerable.raise'` of a run of zeros is an arithmetic progression. -/
lemma raise'_replicate_zero (i : ℕ) :
    ∀ n : ℕ, Denumerable.raise' (List.replicate i (0 : ℕ)) n = List.range' n i := by
  induction i with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    have e : Denumerable.raise' (0 :: List.replicate k (0 : ℕ)) n
        = (0 + n) :: Denumerable.raise' (List.replicate k (0 : ℕ)) (0 + n + 1) := rfl
    rw [List.replicate_succ, e, ih (0 + n + 1)]
    simp only [Nat.zero_add]
    rfl

/-- The `n`-th finite set of naturals is `Finset.range i` when `n` codes the list of `i`
zeros. -/
lemma ofNat_finset_encode_replicate (i : ℕ) :
    Denumerable.ofNat (Finset ℕ) (Encodable.encode (List.replicate i (0 : ℕ)))
      = Finset.range i := by
  rw [ofNat_finset_eq_raise'Finset, Denumerable.ofNat_encode]
  refine Finset.eq_of_veq ?_
  have h : (Denumerable.raise'Finset (List.replicate i (0 : ℕ)) 0).val
      = ((Denumerable.raise' (List.replicate i (0 : ℕ)) 0 : List ℕ) : Multiset ℕ) := rfl
  rw [h, raise'_replicate_zero i 0, ← List.range_eq_range']
  rfl

/-- `i ↦ List.replicate i 0` is primitive recursive. -/
lemma primrec_replicateZero : Primrec fun i : ℕ => List.replicate i (0 : ℕ) := by
  have h : Primrec₂ fun (_ : ℕ) (_ : ℕ) => (0 : ℕ) := Primrec.const (0 : ℕ)
  exact (Primrec.list_map Primrec.list_range h).of_eq fun i => by
    simp [List.map_const']

/-- SUV p. 150, the plumbing: `i ↦ Finset.range i` is primitive recursive. -/
theorem primrec_finsetRange : Primrec fun i : ℕ => Finset.range i :=
  ((Primrec.ofNat (Finset ℕ)).comp (Primrec.encode.comp primrec_replicateZero)).of_eq
    fun i => ofNat_finset_encode_replicate i

/-- SUV p. 150, the plumbing: `i ↦ Finset.range i` is computable. -/
theorem computable_finsetRange : Computable fun i : ℕ => Finset.range i :=
  primrec_finsetRange.to_comp

/-! ### The restriction of a string to a finite index set -/

/-- SUV p. 149: `(F, x) ↦ x(F)` is primitive recursive. -/
theorem primrec_restrictStr :
    Primrec fun p : Finset ℕ × BitString => restrictStr p.1 p.2 := by
  refine Primrec.list_map (primrec_finsetSort.comp Primrec.fst) ?_
  exact (Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst) Primrec.snd

/-- SUV p. 149: `(F, x) ↦ x(F)` is computable. -/
theorem computable_restrictStr :
    Computable fun p : Finset ℕ × BitString => restrictStr p.1 p.2 :=
  primrec_restrictStr.to_comp

/-! ### The canonical code of a finite set -/

/-- SUV p. 149: the `Encodable` code of `F` used by `finsetCode` is the code of the sorted list
of `F`.  (`Mathlib` carries two `Encodable (Finset ℕ)` instances: `Finset.encodable`, which
`Encodable.encode` picks and which `finsetCode` therefore uses, and the `Denumerable` rank,
which is the one hidden inside `Primcodable (Finset ℕ)`.) -/
lemma finsetCode_eq_natToBitString_encode_sort (F : Finset ℕ) :
    finsetCode F = natToBitString (Encodable.encode (F.sort (· ≤ ·))) := rfl

/-- SUV p. 149: the canonical code of a finite set is primitive recursive. -/
theorem primrec_finsetCode : Primrec finsetCode :=
  (primrec_natToBitString.comp (Primrec.encode.comp primrec_finsetSort)).of_eq fun _ => rfl

/-- SUV p. 149: the canonical code of a finite set is computable. -/
theorem computable_finsetCode : Computable finsetCode := primrec_finsetCode.to_comp

end Kolmogorov
