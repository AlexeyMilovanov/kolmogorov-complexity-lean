import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalComplexity

/-!
# Uniform execution of a total program over a finite list

This module implements the missing S0 primitive of VS40 Section 7: running a
single program `p` of a partial-recursive decompressor `D` on *every* string of
a finite input list, uniformly in both `p` and the list.  This is the
computational content behind Proposition `prop:equivalence`: if `p` witnesses
`x -ε-> y` (a total program mapping `x` to `y`), then from the list of elements
of an `(i * j)`-description `A` of `x` one produces the list
`{D(p, x') | x' ∈ A}`, an `((i + O(ε)) * j)`-description of `y`.  Totality of `p`
is exactly what guarantees the traversal halts for every list.

The executor is genuinely `Partrec` (built from the established `Partrec.nat_rec`
pattern, cf. `restrictedEffectiveSampledRunProcess_partrec`); no computation uses
`Classical.choose`.  Correctness is stated relationally with `List.Forall₂`.
-/

namespace Kolmogorov

/-- Run the program `p` of `D` on the first `r` entries of `xs`, accumulating the
outputs in order.  At step `idx` it feeds `xs.getD idx []` to `D (p, ·)` and
appends the result to the running prefix. -/
def totalProgramMapListAux
    (D : Map) (p : BitString) (xs : List BitString)
    (r : Nat) : Part (List BitString) :=
  Nat.rec (motive := fun _ => Part (List BitString))
    (Part.some [])
    (fun idx state =>
      state.bind fun ys =>
        (D (p, xs.getD idx [])).map fun y => ys ++ [y])
    r

/-- The uniform executor: on input `(p, xs)`, run `p` on every entry of `xs`. -/
def totalProgramMapList
    (D : Map) : BitString × List BitString →. List BitString :=
  fun input =>
    totalProgramMapListAux D input.1 input.2 input.2.length

@[simp] lemma totalProgramMapListAux_zero
    (D : Map) (p : BitString) (xs : List BitString) :
    totalProgramMapListAux D p xs 0 = Part.some [] := rfl

lemma totalProgramMapListAux_succ
    (D : Map) (p : BitString) (xs : List BitString) (r : Nat) :
    totalProgramMapListAux D p xs (r + 1) =
      (totalProgramMapListAux D p xs r).bind
        (fun ys => (D (p, xs.getD r [])).map (fun y => ys ++ [y])) := rfl

/-! ### Partial recursiveness -/

/-- The uniform list executor is partial recursive, uniformly in the program `p`
and the input list `xs`. -/
theorem totalProgramMapList_partrec (D : Map) (hD : isDecompressor D) :
    Partrec (totalProgramMapList D) := by
  have hcount : Computable (fun input : BitString × List BitString => input.2.length) :=
    Computable.list_length.comp Computable.snd
  have hinitial : Partrec (fun _ : BitString × List BitString =>
      (Part.some ([] : List BitString))) :=
    (Computable.const ([] : List BitString)).partrec
  have hDcall : Partrec (fun q : (BitString × List BitString) × (ℕ × List BitString) =>
      D (q.1.1, q.1.2.getD q.2.1 [])) := by
    refine hD.comp ?_
    apply Primrec.to_comp
    exact Primrec.pair (Primrec.fst.comp Primrec.fst)
      ((Primrec.list_getD []).comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
  have happend : Computable₂ (fun (q : (BitString × List BitString) × (ℕ × List BitString))
      (y : BitString) => q.2.2 ++ [y]) := by
    apply Primrec.to_comp
    exact Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  have hnext : Partrec₂ (fun input : BitString × List BitString =>
      fun indexed : ℕ × List BitString =>
        (D (input.1, input.2.getD indexed.1 [])).map (fun y => indexed.2 ++ [y])) :=
    Partrec.map hDcall happend
  refine (Partrec.nat_rec hcount hinitial hnext).of_eq ?_
  intro input
  rfl

/-! ### Termination under totality -/

/-- If the program `p` is total for `D`, the traversal halts on every list and
every prefix length. -/
lemma totalProgramMapListAux_dom
    {D : Map} {p : BitString}
    (hp : IsTotalProgram D p)
    (xs : List BitString) (r : Nat) :
    (totalProgramMapListAux D p xs r).Dom := by
  induction r with
  | zero => exact trivial
  | succ r ih =>
    rw [Part.dom_iff_mem] at ih ⊢
    obtain ⟨zs, hzs⟩ := ih
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp (hp (xs.getD r []))
    refine ⟨zs ++ [y], ?_⟩
    rw [totalProgramMapListAux_succ, Part.mem_bind_iff]
    exact ⟨zs, hzs, (Part.mem_map_iff _).2 ⟨y, hy, rfl⟩⟩

/-- The full executor halts for every total program and every input list. -/
theorem totalProgramMapList_dom_of_total
    {D : Map} {p : BitString}
    (hp : IsTotalProgram D p)
    (xs : List BitString) :
    (totalProgramMapList D (p, xs)).Dom :=
  totalProgramMapListAux_dom hp xs xs.length

/-! ### Correctness -/

/-- Every output of the prefix executor is, entry by entry, an output of `p` on
the corresponding input.  The input side is `xs.take r` because exactly `r`
entries have been processed. -/
lemma totalProgramMapListAux_correct
    {D : Map} {p : BitString} (xs : List BitString) :
    ∀ (r : Nat), r ≤ xs.length → ∀ {ys : List BitString},
      ys ∈ totalProgramMapListAux D p xs r →
      List.Forall₂ (fun x y => produces D p x y) (xs.take r) ys := by
  intro r
  induction r with
  | zero =>
    intro _ ys hys
    rw [totalProgramMapListAux_zero, Part.mem_some_iff] at hys
    subst hys
    simp
  | succ r ih =>
    intro hr ys hys
    rw [totalProgramMapListAux_succ, Part.mem_bind_iff] at hys
    obtain ⟨zs, hzs, hmem⟩ := hys
    rw [Part.mem_map_iff] at hmem
    obtain ⟨y, hy, rfl⟩ := hmem
    have hrlt : r < xs.length := hr
    have ih' := ih (Nat.le_of_succ_le hr) hzs
    have htake : xs.take (r + 1) = xs.take r ++ [xs.getD r []] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hrlt, List.getD_eq_getElem xs [] hrlt]
      rfl
    rw [htake]
    exact List.rel_append ih' (List.Forall₂.cons hy List.Forall₂.nil)

/-- Full correctness: each output entry is `D`'s output of `p` on the
corresponding input entry, over the whole list. -/
theorem totalProgramMapList_correct
    {D : Map} {p : BitString} {xs ys : List BitString}
    (hys : ys ∈ totalProgramMapList D (p, xs)) :
    List.Forall₂ (fun x y => produces D p x y) xs ys := by
  have h := totalProgramMapListAux_correct (D := D) (p := p) xs xs.length le_rfl hys
  rwa [List.take_length] at h

/-! ### Finite-set corollaries

These feed the `prop:equivalence` image bound: the image list has the same
length as the input list, so its finite-set image is nonempty when the input is
nonempty and has cardinality at most that of the (deduplicated) input. -/

/-- The output has the same length as the input list. -/
theorem totalProgramMapList_length_eq
    {D : Map} {p : BitString} {xs ys : List BitString}
    (hys : ys ∈ totalProgramMapList D (p, xs)) :
    ys.length = xs.length :=
  (totalProgramMapList_correct hys).length_eq.symm

/-- A nonempty input list produces a nonempty image finite set. -/
theorem totalProgramMapList_result_nonempty
    {D : Map} {p : BitString} {xs ys : List BitString}
    (hxs : xs ≠ [])
    (hys : ys ∈ totalProgramMapList D (p, xs)) :
    ys.toFinset.Nonempty := by
  rw [List.toFinset_nonempty_iff]
  intro hnil
  apply hxs
  have hlen := totalProgramMapList_length_eq hys
  rw [hnil, List.length_nil] at hlen
  exact List.eq_nil_of_length_eq_zero hlen.symm

/-- If the input list has no duplicates, the image finite set is no larger than
the input finite set. -/
theorem totalProgramMapList_result_card_le
    {D : Map} {p : BitString} {xs ys : List BitString}
    (hxs : xs.Nodup)
    (hys : ys ∈ totalProgramMapList D (p, xs)) :
    ys.toFinset.card ≤ xs.toFinset.card := by
  calc ys.toFinset.card
      ≤ ys.length := List.toFinset_card_le ys
    _ = xs.length := totalProgramMapList_length_eq hys
    _ = xs.toFinset.card := (List.toFinset_card_of_nodup hxs).symm

end Kolmogorov
