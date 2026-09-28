import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition.Part01

/-!
# The fibre partition, and the converse of the partition proposition

`IsStrongSetModel.exists_partition`: an `ε`-strong model of a string of length `n` arises from
a partition, which is the converse direction of Proposition `part`.  The partition is built by
fibres: `selfMemberPairs` keeps the pairs `(x', out)` with `x'` in the set decoded from its own
output, `fiberOverCode` collects the fibre over a given set code, and
`isPartition_fiberPartition` and `partitionCode_fiberPartition` show the fibres form a genuine
partition with a computable code.

Three decompressors give the complexity estimates the converse needs: one recovering the
original model from a fibre model, one going the other way, and one reconstructing the whole
partition.  `strong_description_shift`, the description-shift property of strong models, is
the consequence drawn at the end.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- Pairing two lists of strings entrywise is primitive recursive. -/
theorem zipStrings_primrec :
    Primrec₂ zipStrings := by
  unfold zipStrings
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) ?_
  exact (Primrec.pair
    ((Primrec.list_getD []).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    ((Primrec.list_getD []).comp (Primrec.snd.comp Primrec.fst) Primrec.snd))

/-- Zipping a list with its image under `f` gives the list of pairs `(x, f x)`. -/
theorem zipStrings_map_self (xs : List BitString)
    (f : BitString → BitString) :
    zipStrings xs (xs.map f) = xs.map (fun x => (x, f x)) := by
  apply List.ext_getElem
  · simp [zipStrings]
  · intro k hk1 hk2
    simp only [zipStrings, List.length_map, List.length_range] at hk1
    have hk : k < xs.length := by
      simpa [List.length_map] using hk1
    rw [List.getElem_map]
    simp only [zipStrings, List.getElem_map, List.getElem_range]
    have h1 : xs.getD k [] = xs[k] := by
      rw [List.getD_eq_getElem xs [] hk]
    have h2 : (xs.map f).getD k [] = f xs[k] := by
      rw [List.getD_eq_getElem (xs.map f) [] (by simpa using hk),
        List.getElem_map]
    rw [h1, h2]

/-! ### Fiber lists over aligned pairs -/

/-- The pairs `(x', out)` where `x'` belongs to the set decoded from its own
output `out`. -/
noncomputable def selfMemberPairs (pairs : List (BitString × BitString)) :
    List (BitString × BitString) :=
  pairs.filter (fun q => decide (q.1 ∈ canonicalPointListOfCode q.2))

/-- The fiber of the value `B`: those self-member strings whose output is `B`. -/
noncomputable def fiberOverCode (pairs : List (BitString × BitString))
    (B : BitString) : List BitString :=
  ((selfMemberPairs pairs).filter (fun q => decide (q.2 = B))).map Prod.fst

/-- Membership in a fiber list, for arbitrary aligned pairs. -/
theorem mem_fiberOverCode (pairs : List (BitString × BitString))
    (B a : BitString) :
    a ∈ fiberOverCode pairs B ↔
      (a, B) ∈ pairs ∧ a ∈ canonicalPointListOfCode B := by
  unfold fiberOverCode selfMemberPairs
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists]
  constructor
  · rintro ⟨a', b', ⟨⟨hmem, hself⟩, hb⟩, ha⟩
    subst ha; subst hb
    exact ⟨hmem, hself⟩
  · rintro ⟨hmem, hself⟩
    exact ⟨a, B, ⟨⟨hmem, hself⟩, rfl⟩, rfl⟩

/-- Membership in a fiber list computed from the `f`-paired input list. -/
theorem mem_fiberOverCode_map (xs : List BitString)
    (f : BitString → BitString) (B a : BitString) :
    a ∈ fiberOverCode (xs.map (fun x => (x, f x))) B ↔
      a ∈ xs ∧ f a = B ∧ a ∈ canonicalPointListOfCode B := by
  rw [mem_fiberOverCode]
  constructor
  · rintro ⟨hmem, hself⟩
    rw [List.mem_map] at hmem
    obtain ⟨a', ha'mem, ha'eq⟩ := hmem
    rw [Prod.mk.injEq] at ha'eq
    obtain ⟨rfl, hfe⟩ := ha'eq
    exact ⟨ha'mem, hfe, hself⟩
  · rintro ⟨hmem, hfa, hself⟩
    refine ⟨?_, hself⟩
    rw [List.mem_map]
    exact ⟨a, hmem, by rw [hfa]⟩

/-- Functional property of a fiber: every fiber element maps to the fiber's value. -/
theorem fiberOverCode_map_output {xs : List BitString}
    {f : BitString → BitString} {B a : BitString}
    (h : a ∈ fiberOverCode (xs.map (fun x => (x, f x))) B) :
    f a = B :=
  ((mem_fiberOverCode_map xs f B a).mp h).2.1

/-- The canonical code of a finite set equals the canonical image code of any
list whose `toFinset` is that set. -/
theorem canonicalFiniteSetCode_toFinset (l : List BitString) :
    canonicalFiniteSetCode l.toFinset = canonicalImageCodeOfList l := rfl

/-- Selecting the pairs whose first component belongs to its own fibre is primitive
recursive. -/
theorem selfMemberPairs_primrec :
    Primrec selfMemberPairs := by
  unfold selfMemberPairs
  refine list_filter_primrec Primrec.id ?_
  exact (bitString_mem_primrec.comp (Primrec.fst.comp Primrec.snd)
    (canonicalPointListOfCode_primrec.comp (Primrec.snd.comp Primrec.snd))).to₂

/-- Extracting the fibre over a given set code is primitive recursive. -/
theorem fiberOverCode_primrec :
    Primrec₂ fiberOverCode := by
  unfold fiberOverCode
  have heq : Primrec₂ (fun (a b : BitString) => decide (a = b)) := by
    convert Primrec.eq
    any_goals exact BitString
    · convert Iff.rfl
      exact primrecRel_iff_primrec_decide
  have hfilter : Primrec (fun input : List (BitString × BitString) × BitString =>
      (selfMemberPairs input.1).filter (fun q => decide (q.2 = input.2))) := by
    refine list_filter_primrec (selfMemberPairs_primrec.comp Primrec.fst) ?_
    exact (heq.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  exact (Primrec.list_map hfilter (Primrec.fst.comp Primrec.snd).to₂)

/-- The head of the canonical enumeration of a nonempty finite set is a member. -/
theorem headI_mem_canonicalFinsetList {S : Finset BitString} (hS : S.Nonempty) :
    (canonicalFinsetList S).headI ∈ S := by
  have hne : canonicalFinsetList S ≠ [] := by
    rw [← List.length_pos_iff_ne_nil, length_canonicalFinsetList]
    exact hS.card_pos
  cases h : canonicalFinsetList S with
  | nil => exact absurd h hne
  | cons a t =>
    have ha : a ∈ canonicalFinsetList S := by rw [h]; exact List.mem_cons_self
    change (a :: t).headI ∈ S
    exact mem_canonicalFinsetList.mp ha

/-! ### Decompressor 1: obtain the original model from a fibre model (`CT(A|A')`) -/

/-- On input `(p, B')`, decode the finite set `B'`, take any element (its head),
and run the total program `p` on it.  For the fibre model `A'`, its head lies in
`A'`, so the program's value there is the code of the original model `A`. -/
noncomputable def elementThenProgDecompressor (T : Map) : Map :=
  fun input => T (input.1, (canonicalPointListOfCode input.2).headI)

/-- Running a program on the first element of a coded set again gives a
decompressor. -/
theorem elementThenProgDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (elementThenProgDecompressor T) := by
  have h : Partrec (fun input : BitString × BitString =>
      T (input.1, (canonicalPointListOfCode input.2).headI)) :=
    Partrec.comp hT
      (Computable.pair Computable.fst
        ((Primrec.list_headI.to_comp).comp
          (canonicalPointListOfCode_computable.comp Computable.snd)))
  exact h

/-- Totality of a program is preserved by conditioning on the first element of a
coded set. -/
theorem elementThenProgDecompressor_total
    {T : Map} {p : BitString} (hp : IsTotalProgram T p) :
    IsTotalProgram (elementThenProgDecompressor T) p := by
  intro B'
  exact hp _

/-- If the coded set has first element `x₀`, the decompressor reproduces on it what
the program produces on `x₀`. -/
theorem elementThenProgDecompressor_produces
    {T : Map} {p x₀ B' out : BitString}
    (hhead : (canonicalPointListOfCode B').headI = x₀)
    (hp : produces T p x₀ out) :
    produces (elementThenProgDecompressor T) p B' out := by
  unfold produces elementThenProgDecompressor
  rw [hhead]
  exact hp

/-! ### Decompressor 2: obtain the fibre model from the original model (`CT(A'|A)`) -/

/-- Post-processing: from the aligned outputs and the target set-code `input.2`,
return the canonical code of the fibre over `input.2`. -/
noncomputable def fiberPostFn
    (input : BitString × BitString) (ys : List BitString) : BitString :=
  canonicalImageCodeOfList
    (fiberOverCode
      (zipStrings (allStrings (decodeBits (decodeFirst input.1))) ys)
      input.2)

/-- The post-processing that returns the code of the fibre over the conditioned set
code is computable. -/
theorem fiberPostFn_computable : Computable₂ fiberPostFn := by
  have h : Primrec (fun q : (BitString × BitString) × List BitString =>
      canonicalImageCodeOfList
        (fiberOverCode
          (zipStrings (allStrings (decodeBits (decodeFirst q.1.1))) q.2)
          q.1.2)) :=
    canonicalImageCodeOfList_primrec.comp
      (fiberOverCode_primrec.comp
        (zipStrings_primrec.comp
          (allStrings_primrec.comp
            (primrec_decodeBits.comp
              (decodeFirst_primrec.comp (Primrec.fst.comp Primrec.fst))))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  exact h.to_comp

/-- On program `pairCode (bits n) p` and condition set-code `B`, run the total
program `p` over all length-`n` strings and return the canonical code of the
fibre `{x' : x' ∈ p(x'), p(x') = B}`. -/
noncomputable def fiberFromSetCodeDecompressor (T : Map) : Map :=
  fun input =>
    (totalProgramMapList T (decodeSecond input.1,
        allStrings (decodeBits (decodeFirst input.1)))).map (fiberPostFn input)

/-- The fibre-from-set-code map is a decompressor. -/
theorem fiberFromSetCodeDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (fiberFromSetCodeDecompressor T) := by
  have hexec : Partrec (fun input : BitString × BitString =>
      totalProgramMapList T (decodeSecond input.1,
        allStrings (decodeBits (decodeFirst input.1)))) :=
    Partrec.comp (totalProgramMapList_partrec T hT)
      (Computable.pair
        (decodeSecond_computable.comp Computable.fst)
        (allStrings_primrec.to_comp.comp
          (decodeBits_computable.comp
            (decodeFirst_computable.comp Computable.fst))))
  exact Partrec.map hexec fiberPostFn_computable

/-! ### Decompressor 3: reconstruct the whole partition (partition complexity) -/

/-- The list of member set-codes of the fibre partition determined by aligned
pairs. -/
noncomputable def partitionMemberCodesFromPairs
    (pairs : List (BitString × BitString)) : List BitString :=
  (selfMemberPairs pairs).map
    (fun q => canonicalImageCodeOfList (fiberOverCode pairs q.2))

/-- Computing the member codes of the fibre partition from aligned pairs is
primitive recursive. -/
theorem partitionMemberCodesFromPairs_primrec :
    Primrec partitionMemberCodesFromPairs := by
  unfold partitionMemberCodesFromPairs
  refine Primrec.list_map selfMemberPairs_primrec ?_
  exact (canonicalImageCodeOfList_primrec.comp
    (fiberOverCode_primrec.comp Primrec.fst
      (Primrec.snd.comp Primrec.snd))).to₂

/-- Post-processing: from the aligned outputs, return the canonical code of the
whole fibre partition. -/
noncomputable def partitionPostFn
    (input : BitString × BitString) (ys : List BitString) : BitString :=
  canonicalImageCodeOfList
    (partitionMemberCodesFromPairs
      (zipStrings (allStrings (decodeBits (decodeFirst input.1))) ys))

/-- The post-processing that returns the code of the whole fibre partition is
computable. -/
theorem partitionPostFn_computable : Computable₂ partitionPostFn := by
  have h : Primrec (fun q : (BitString × BitString) × List BitString =>
      canonicalImageCodeOfList
        (partitionMemberCodesFromPairs
          (zipStrings (allStrings (decodeBits (decodeFirst q.1.1))) q.2))) :=
    canonicalImageCodeOfList_primrec.comp
      (partitionMemberCodesFromPairs_primrec.comp
        (zipStrings_primrec.comp
          (allStrings_primrec.comp
            (primrec_decodeBits.comp
              (decodeFirst_primrec.comp (Primrec.fst.comp Primrec.fst))))
          Primrec.snd))
  exact h.to_comp

/-- On program `pairCode (bits n) p`, run `p` over all length-`n` strings and
return the canonical code of the whole fibre partition. -/
noncomputable def partitionFromProgDecompressor (T : Map) : Map :=
  fun input =>
    (totalProgramMapList T (decodeSecond input.1,
        allStrings (decodeBits (decodeFirst input.1)))).map (partitionPostFn input)

/-- The partition-from-program map is a decompressor. -/
theorem partitionFromProgDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (partitionFromProgDecompressor T) := by
  have hexec : Partrec (fun input : BitString × BitString =>
      totalProgramMapList T (decodeSecond input.1,
        allStrings (decodeBits (decodeFirst input.1)))) :=
    Partrec.comp (totalProgramMapList_partrec T hT)
      (Computable.pair
        (decodeSecond_computable.comp Computable.fst)
        (allStrings_primrec.to_comp.comp
          (decodeBits_computable.comp
            (decodeFirst_computable.comp Computable.fst))))
  exact Partrec.map hexec partitionPostFn_computable

/-! ### Evaluations, totality, and production of the post decompressors -/

/-- On outputs aligned with all strings of length `n`, the fibre post-processing
returns the code of the fibre of the graph of `f` over the given set code. -/
theorem fiberPostFn_eval (p : BitString) (n : Nat)
    (f : BitString → BitString) (B : BitString) :
    fiberPostFn (pairCode (Nat.bits n) p, B) ((allStrings n).map f) =
      canonicalImageCodeOfList
        (fiberOverCode ((allStrings n).map (fun x => (x, f x))) B) := by
  unfold fiberPostFn
  simp only [decodeFirst_pairCode, decodeBits_natBits]
  rw [zipStrings_map_self]

/-- On outputs aligned with all strings of length `n`, the partition
post-processing returns the code of the fibre partition of the graph of `f`. -/
theorem partitionPostFn_eval (p : BitString) (n : Nat)
    (f : BitString → BitString) :
    partitionPostFn (pairCode (Nat.bits n) p, []) ((allStrings n).map f) =
      canonicalImageCodeOfList
        (partitionMemberCodesFromPairs
          ((allStrings n).map (fun x => (x, f x)))) := by
  unfold partitionPostFn
  simp only [decodeFirst_pairCode, decodeBits_natBits]
  rw [zipStrings_map_self]

/-- A total program, paired with a length parameter, is total in the
fibre-from-set-code decompressor. -/
theorem fiberFromSetCodeDecompressor_total
    {T : Map} {p : BitString} (hp : IsTotalProgram T p) (n : Nat) :
    IsTotalProgram (fiberFromSetCodeDecompressor T) (pairCode (Nat.bits n) p) := by
  intro B
  unfold fiberFromSetCodeDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits]
  rw [Part.dom_iff_mem]
  obtain ⟨ys, hys⟩ :=
    Part.dom_iff_mem.mp (totalProgramMapList_dom_of_total hp (allStrings n))
  exact ⟨fiberPostFn (pairCode (Nat.bits n) p, B) ys,
    (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩⟩

/-- The fibre decompressor produces on the condition `B` the value of the fibre
post-processing at the aligned outputs. -/
theorem fiberFromSetCodeDecompressor_produces
    {T : Map} {p : BitString} (n : Nat)
    {B : BitString} {ys : List BitString}
    (hys : ys ∈ totalProgramMapList T (p, allStrings n)) :
    produces (fiberFromSetCodeDecompressor T) (pairCode (Nat.bits n) p) B
      (fiberPostFn (pairCode (Nat.bits n) p, B) ys) := by
  unfold produces fiberFromSetCodeDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits]
  exact (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩

/-- The partition decompressor produces the value of the partition post-processing
at the aligned outputs. -/
theorem partitionFromProgDecompressor_produces
    {T : Map} {p : BitString} (n : Nat) {y : BitString}
    {ys : List BitString}
    (hys : ys ∈ totalProgramMapList T (p, allStrings n)) :
    produces (partitionFromProgDecompressor T) (pairCode (Nat.bits n) p) y
      (partitionPostFn (pairCode (Nat.bits n) p, y) ys) := by
  unfold produces partitionFromProgDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits]
  exact (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩

/-! ### The fibre partition and its properties -/

/-- The fibre partition determined by aligned pairs. -/
noncomputable def fiberPartition (pairs : List (BitString × BitString)) :
    Finset (Finset BitString) :=
  ((selfMemberPairs pairs).map
    (fun q => (fiberOverCode pairs q.2).toFinset)).toFinset

/-- The canonical code of the fibre partition is the canonical image code of its
member-code list — connecting the finite-set definition with the computed value. -/
theorem partitionCode_fiberPartition (pairs : List (BitString × BitString)) :
    partitionCode (fiberPartition pairs) =
      canonicalImageCodeOfList (partitionMemberCodesFromPairs pairs) := by
  unfold partitionCode
  rw [← canonicalFiniteSetCode_toFinset]
  congr 1
  unfold fiberPartition partitionMemberCodesFromPairs
  ext w
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨B, ⟨q, hq, hBeq⟩, hwB⟩
    exact ⟨q, hq, by rw [← hwB, ← hBeq, canonicalFiniteSetCode_toFinset]⟩
  · rintro ⟨q, hq, hweq⟩
    exact ⟨(fiberOverCode pairs q.2).toFinset, ⟨q, hq, rfl⟩,
      by rw [← hweq, canonicalFiniteSetCode_toFinset]⟩

/-- Membership in a mapped pair list. -/
theorem mem_map_pair {xs : List BitString} {f : BitString → BitString}
    {z b : BitString} :
    (z, b) ∈ xs.map (fun x => (x, f x)) ↔ z ∈ xs ∧ f z = b := by
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, hae⟩
    rw [Prod.mk.injEq] at hae
    obtain ⟨rfl, rfl⟩ := hae
    exact ⟨ha, rfl⟩
  · rintro ⟨hz, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- The fibre partition of an `f`-paired input list is a genuine partition. -/
theorem isPartition_fiberPartition
    (xs : List BitString) (f : BitString → BitString) :
    IsPartition (fiberPartition (xs.map (fun x => (x, f x)))) := by
  intro B hB C hC hBC
  simp only [fiberPartition, List.mem_toFinset, List.mem_map] at hB hC
  obtain ⟨qB, _, hBeq⟩ := hB
  obtain ⟨qC, _, hCeq⟩ := hC
  rw [Finset.disjoint_left]
  intro z hzB hzC
  rw [← hBeq, List.mem_toFinset] at hzB
  rw [← hCeq, List.mem_toFinset] at hzC
  have hfb : f z = qB.2 := fiberOverCode_map_output hzB
  have hfc : f z = qC.2 := fiberOverCode_map_output hzC
  apply hBC
  rw [← hBeq, ← hCeq, hfb.symm.trans hfc]

/-- Conversely, if $A$ is an $\varepsilon$-strong model for $x$ of length $n$,
there exists a partition of complexity at most $\varepsilon + O(\log n)$
containing a model $A'$ for $x$ such that $\# A' \le \# A$, and both
$\CT(A \mid A')$ and $\CT(A' \mid A)$ are bounded by $\varepsilon + O(\log n)$. -/
theorem IsStrongSetModel.exists_partition
    (U : Map) (hU : isOptimalConditional U)
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀
      (x : BitString) (n : Nat), x.length = n →
      ∀ (S : Finset BitString) (hS : x ∈ S)
        (epsilon : Nat), IsStrongSetModel T x S ⟨x, hS⟩ epsilon →
    ∃ (P : Finset (Finset BitString)) (S' : Finset BitString) (hS' : x ∈ S'),
      IsPartition P ∧
      S' ∈ P ∧
      S'.card ≤ S.card ∧
      partitionComplexity U P ≤
        (epsilon : ENat) + (logSlack c n : ENat) ∧
      totalCondK T (codedUniformOn S ⟨x, hS⟩).code
        (codedUniformOn S' ⟨x, hS'⟩).code ≤
          (epsilon : ENat) + (logSlack c n : ENat) ∧
      totalCondK T (codedUniformOn S' ⟨x, hS'⟩).code
        (codedUniformOn S ⟨x, hS⟩).code ≤
          (epsilon : ENat) + (logSlack c n : ENat) := by
  obtain ⟨c1, hc1⟩ :=
    hT.2 (elementThenProgDecompressor T)
      (elementThenProgDecompressor_partrec T hT.1)
  obtain ⟨c2, hc2⟩ :=
    hT.2 (fiberFromSetCodeDecompressor T)
      (fiberFromSetCodeDecompressor_partrec T hT.1)
  obtain ⟨c3, hc3⟩ :=
    hU.2 (partitionFromProgDecompressor T)
      (partitionFromProgDecompressor_partrec T hT.1)
  refine ⟨c1 + c2 + c3 + 2, ?_⟩
  intro x n hn S hxS epsilon hstrong
  -- Total program witnessing the strong model.
  obtain ⟨p, hpTotal, hpLen, hpProd⟩ :=
    (totalCondK_le_iff T (codedUniformOn S ⟨x, hxS⟩).code x epsilon).mp hstrong
  change p.length ≤ epsilon at hpLen
  set codeS := (codedUniformOn S ⟨x, hxS⟩).code with hcodeS_def
  set f := totalProgOutput T p hpTotal with hf_def
  have hfx : f x = codeS := (produces_eq_totalProgOutput hpTotal hpProd).symm
  set pairs := (allStrings n).map (fun x' => (x', f x')) with hpairs_def
  set S' := (fiberOverCode pairs codeS).toFinset with hS'_def
  have hcode : canonicalPointListOfCode codeS = canonicalFinsetList S :=
    canonicalPointListOfCode_codedUniformOn S ⟨x, hxS⟩
  -- x is in S'.
  have hxS' : x ∈ S' := by
    rw [hS'_def, List.mem_toFinset, mem_fiberOverCode_map]
    refine ⟨(mem_allStrings n x).mpr hn, hfx, ?_⟩
    rw [hcode, mem_canonicalFinsetList]; exact hxS
  set codeS' := (codedUniformOn S' ⟨x, hxS'⟩).code with hcodeS'_def
  -- S' ⊆ S, hence the cardinality bound.
  have hS'subset : S' ⊆ S := by
    intro a ha
    rw [hS'_def, List.mem_toFinset, mem_fiberOverCode_map] at ha
    have := ha.2.2
    rw [hcode, mem_canonicalFinsetList] at this
    exact this
  have hcard : S'.card ≤ S.card := Finset.card_le_card hS'subset
  -- The partition and its properties.
  set P := fiberPartition pairs with hP_def
  have hPart : IsPartition P := isPartition_fiberPartition (allStrings n) f
  have hS'memP : S' ∈ P := by
    rw [hP_def, fiberPartition, List.mem_toFinset, List.mem_map]
    refine ⟨(x, codeS), ?_, ?_⟩
    · rw [selfMemberPairs, List.mem_filter, decide_eq_true_eq]
      refine ⟨(mem_map_pair).mpr ⟨(mem_allStrings n x).mpr hn, hfx⟩, ?_⟩
      rw [hcode, mem_canonicalFinsetList]; exact hxS
    · rfl
  -- The actual output list of the executor.
  obtain ⟨ys, hys⟩ :=
    Part.dom_iff_mem.mp (totalProgramMapList_dom_of_total hpTotal (allStrings n))
  have hys_eq : ys = (allStrings n).map f := totalProgramMapList_eq_map hpTotal hys
  -- The fibre code equals codeS'.
  have hS'ne : S'.Nonempty := ⟨x, hxS'⟩
  have hfiber_code :
      canonicalImageCodeOfList (fiberOverCode pairs codeS) = codeS' := by
    rw [canonicalImageCodeOfList_eq_codedUniformOn (fiberOverCode pairs codeS) hS'ne]
  refine ⟨P, S', hxS', hPart, hS'memP, hcard, ?_, ?_, ?_⟩
  · -- Partition complexity bound.
    have hval : partitionPostFn (pairCode (Nat.bits n) p, []) ys = partitionCode P := by
      rw [hys_eq, partitionPostFn_eval, hP_def, partitionCode_fiberPartition]
    have hprod := partitionFromProgDecompressor_produces (T := T) n (y := ([] : BitString)) hys
    rw [hval] at hprod
    have hlen : (pairCode (Nat.bits n) p).length ≤ 2 * (Nat.bits n).length + 1 + epsilon := by
      rw [length_pairCode]; omega
    calc
      partitionComplexity U P
          = plainK U (partitionCode P) := rfl
      _ = condK U (partitionCode P) [] := rfl
      _ ≤ condK (partitionFromProgDecompressor T) (partitionCode P) [] + (c3 : ENat) :=
          hc3 (partitionCode P) []
      _ ≤ ((pairCode (Nat.bits n) p).length : ENat) + (c3 : ENat) := by
          gcongr
          exact sInf_le ⟨pairCode (Nat.bits n) p, hprod, rfl⟩
      _ ≤ (epsilon : ENat) + (logSlack (c1 + c2 + c3 + 2) n : ENat) := by
          have : (pairCode (Nat.bits n) p).length + c3 ≤
              epsilon + logSlack (c1 + c2 + c3 + 2) n := by
            unfold logSlack
            have h := hlen
            nlinarith [Nat.zero_le ((Nat.bits n).length)]
          exact_mod_cast this
  · -- CT(A | A'): decompressor 1.
    have hheadmem : (canonicalPointListOfCode codeS').headI ∈ S' := by
      rw [hcodeS'_def, canonicalPointListOfCode_codedUniformOn]
      exact headI_mem_canonicalFinsetList hS'ne
    have hfhead : f ((canonicalPointListOfCode codeS').headI) = codeS := by
      rw [hS'_def, List.mem_toFinset] at hheadmem
      exact fiberOverCode_map_output hheadmem
    have hprodhead : produces T p ((canonicalPointListOfCode codeS').headI) codeS := by
      have := totalProgOutput_produces T p hpTotal ((canonicalPointListOfCode codeS').headI)
      rw [← hf_def] at this
      rwa [hfhead] at this
    have hprod : produces (elementThenProgDecompressor T) p codeS' codeS :=
      elementThenProgDecompressor_produces rfl hprodhead
    have htotal : IsTotalProgram (elementThenProgDecompressor T) p :=
      elementThenProgDecompressor_total hpTotal
    calc
      totalCondK T codeS codeS'
          ≤ totalCondK (elementThenProgDecompressor T) codeS codeS' + (c1 : ENat) :=
          hc1 codeS codeS'
      _ ≤ (p.length : ENat) + (c1 : ENat) := by
          gcongr
          exact totalCondK_le_programLength htotal hprod
      _ ≤ (epsilon : ENat) + (logSlack (c1 + c2 + c3 + 2) n : ENat) := by
          have : p.length + c1 ≤ epsilon + logSlack (c1 + c2 + c3 + 2) n := by
            unfold logSlack
            nlinarith [Nat.zero_le ((Nat.bits n).length)]
          exact_mod_cast this
  · -- CT(A' | A): decompressor 2.
    have hval : fiberPostFn (pairCode (Nat.bits n) p, codeS) ys = codeS' := by
      rw [hys_eq, fiberPostFn_eval, ← hpairs_def, hfiber_code]
    have hprod := fiberFromSetCodeDecompressor_produces (T := T) n (B := codeS) hys
    rw [hval] at hprod
    have htotal : IsTotalProgram (fiberFromSetCodeDecompressor T) (pairCode (Nat.bits n) p) :=
      fiberFromSetCodeDecompressor_total hpTotal n
    have hlen : (pairCode (Nat.bits n) p).length ≤ 2 * (Nat.bits n).length + 1 + epsilon := by
      rw [length_pairCode]; omega
    calc
      totalCondK T codeS' codeS
          ≤ totalCondK (fiberFromSetCodeDecompressor T) codeS' codeS + (c2 : ENat) :=
          hc2 codeS' codeS
      _ ≤ ((pairCode (Nat.bits n) p).length : ENat) + (c2 : ENat) := by
          gcongr
          exact totalCondK_le_programLength htotal hprod
      _ ≤ (epsilon : ENat) + (logSlack (c1 + c2 + c3 + 2) n : ENat) := by
          have : (pairCode (Nat.bits n) p).length + c2 ≤
              epsilon + logSlack (c1 + c2 + c3 + 2) n := by
            unfold logSlack
            nlinarith [Nat.zero_le ((Nat.bits n).length)]
          exact_mod_cast this

/-! ### Strong Description Shift -/

/-- Strong models satisfy the description-shift property: if $A$ is an
$\varepsilon$-strong model for $x$, and $i \le \log \# A$, there is an
$\varepsilon + O(\log i)$-strong model $A'$ for $x$ with
$\# A' \le \# A / 2^i$ and $\KS(A') \le \KS(A) + i + O(\log i)$. -/
theorem strong_description_shift
    (U : Map) (hU : isOptimalConditional U)
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀
      (x : BitString) (S : Finset BitString) (hS : x ∈ S)
      (epsilon : Nat), IsStrongSetModel T x S ⟨x, hS⟩ epsilon →
      ∀ (i : Nat), 2^i ≤ S.card →
    ∃ S' : Finset BitString, ∃ (hS' : x ∈ S'),
      IsStrongSetModel T x S' ⟨x, hS'⟩
        (epsilon + logSlack c i) ∧
      S'.card * 2^i ≤ S.card ∧
      plainSetComplexity U S' ⟨x, hS'⟩ ≤
        plainSetComplexity U S ⟨x, hS⟩ +
          (i : ENat) + (logSlack c i : ENat) := by
  obtain ⟨cTotal, hTotal⟩ :=
    hT.2 (strongDescriptionChunkDecompressor T)
      (strongDescriptionChunkDecompressor_partrec T hT.1)
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_descriptionChunk_succ U hU
  let c := cTotal + cPlain + 10
  refine ⟨c, ?_⟩
  intro x S hxS epsilon hstrong i hi
  have hS : S.Nonempty := ⟨x, hxS⟩
  obtain ⟨p, hpTotal, hpLen, hpProd⟩ :=
    (totalCondK_le_iff T (codedUniformOn S hS).code x
      epsilon).mp hstrong
  change p.length ≤ epsilon at hpLen
  let S' := descriptionChunk S x (i + 1)
  have hxS' : x ∈ S' :=
    mem_descriptionChunk S x (i + 1) hxS
  refine ⟨S', hxS', ?_, ?_, ?_⟩
  · unfold IsStrongSetModel
    have hencodedTotal :
        IsTotalProgram (strongDescriptionChunkDecompressor T)
          (pairCode (Nat.bits i) p) :=
      strongDescriptionChunkDecompressor_total hpTotal i
    have hencodedProd :
        produces (strongDescriptionChunkDecompressor T)
          (pairCode (Nat.bits i) p) x
          (codedUniformOn S' ⟨x, hxS'⟩).code := by
      exact strongDescriptionChunkDecompressor_produces
        hS i hpProd hxS
    have hslack :
        2 * (Nat.bits i).length + 1 + cTotal ≤
          logSlack c i := by
      unfold logSlack c
      nlinarith [Nat.zero_le (Nat.bits i).length]
    calc
      totalCondK T (codedUniformOn S' ⟨x, hxS'⟩).code x
          ≤ totalCondK (strongDescriptionChunkDecompressor T)
              (codedUniformOn S' ⟨x, hxS'⟩).code x +
              (cTotal : ENat) :=
        hTotal _ _
      _ ≤ ((pairCode (Nat.bits i) p).length : ENat) +
            (cTotal : ENat) := by
        gcongr
        exact totalCondK_le_programLength
          hencodedTotal hencodedProd
      _ ≤ ((epsilon + logSlack c i : Nat) : ENat) := by
        rw [length_pairCode]
        exact_mod_cast (show
          (Nat.bits i).length + 1 + (Nat.bits i).length +
              p.length + cTotal ≤ epsilon + logSlack c i by
            omega)
  · exact card_descriptionChunk_succ_mul_pow_le S x i hi
  · have hbits :
        (Nat.bits (i + 1)).length ≤
          (Nat.bits i).length + 2 := by
      have hadd := length_natBits_add_le i 1
      norm_num at hadd ⊢
      exact hadd
    have hslack :
        1 + 2 * (Nat.bits (i + 1)).length + cPlain ≤
          logSlack c i := by
      unfold logSlack c
      nlinarith [Nat.zero_le (Nat.bits i).length]
    calc
      plainSetComplexity U S' ⟨x, hxS'⟩
          ≤ plainSetComplexity U S hS +
              ((i + 1 + 2 * (Nat.bits (i + 1)).length +
                cPlain : Nat) : ENat) :=
        hPlain S hS x i hxS
      _ ≤ plainSetComplexity U S hS +
            (i : ENat) + (logSlack c i : ENat) := by
        have hnat :
            i + 1 + 2 * (Nat.bits (i + 1)).length + cPlain ≤
              i + logSlack c i := by
          omega
        have henat :
            ((i + 1 + 2 * (Nat.bits (i + 1)).length +
              cPlain : Nat) : ENat) ≤
              ((i + logSlack c i : Nat) : ENat) := by
          exact_mod_cast hnat
        calc
          plainSetComplexity U S hS +
              ((i + 1 + 2 * (Nat.bits (i + 1)).length +
                cPlain : Nat) : ENat)
              ≤ plainSetComplexity U S hS +
                  ((i + logSlack c i : Nat) : ENat) :=
            add_le_add (le_refl _) henat
          _ = plainSetComplexity U S hS +
                (i : ENat) + (logSlack c i : ENat) := by
            push_cast
            rw [add_assoc]

end Kolmogorov
