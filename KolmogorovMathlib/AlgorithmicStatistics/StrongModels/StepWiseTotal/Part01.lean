import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition.Converse
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties

/-!
# Total reductions through a preimage

The machinery of VS40 `thm:step-wise` on the total side: if a total program `p` maps a model
`B` onto the code of a model `A`, then the preimage of `[A]` inside `B` is itself a model, and
the reduction can be run in both directions.

`reductionPreimage` is that preimage, with its membership characterisation, the inclusion in
`B`, the cardinality bounds `reductionPreimage_card_le` and `reductionPreimage_card_lower`,
and `IsStrongSetModel.exists_reductionPreimage_program`, which extracts the program from a
strong model.  `reductionPreimageDecompressor` computes it: it runs `p` over the decoded
members of `B` and keeps the fibre over the target code (`reductionFiberList`,
`reductionPreimagePostFn`).

The counting of heavy fibres — `heavyOutputList`, `heavy_output_count`,
`list_count_map_eq_card_filter` — prepares the selector of `StepWiseTotal/Reduction`, and
`StrongSufficientStatisticTotalReductionStatement` states the conclusion those two modules
prove.
-/



namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- The preimage of the canonical model code of `A` inside `B` under `p`.

The predicate is extensional in the partial computation: membership means that
the computation actually produces the displayed code.  Later complexity
lemmas must assume that `p` is total; without totality this finite filter is not
uniformly computable from its inputs. -/
noncomputable def reductionPreimage
    (T : Map) (p : BitString) (B A : Finset BitString) (hA : A.Nonempty) :
    Finset BitString := by
  classical
  exact B.filter
    (fun x' => produces T p x' (codedUniformOn A hA).code)

/-- Exact membership characterization of the reduction preimage. -/
theorem mem_reductionPreimage
    (T : Map) (p : BitString) (B A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) :
    x ∈ reductionPreimage T p B A hA ↔
      x ∈ B ∧ produces T p x (codedUniformOn A hA).code := by
  classical
  simp [reductionPreimage]

/-- The reduction preimage is a subset of the conditioning model `B`. -/
theorem reductionPreimage_subset
    (T : Map) (p : BitString) (B A : Finset BitString) (hA : A.Nonempty) :
    reductionPreimage T p B A hA ⊆ B := by
  intro x hx
  exact (mem_reductionPreimage T p B A hA x).mp hx |>.1

/-- Consequently the reduction preimage has no more elements than `B`. -/
theorem reductionPreimage_card_le
    (T : Map) (p : BitString) (B A : Finset BitString) (hA : A.Nonempty) :
    (reductionPreimage T p B A hA).card ≤ B.card :=
  Finset.card_le_card (reductionPreimage_subset T p B A hA)

/-- A member of `B` on which `p` produces `[A]` witnesses that the preimage is
nonempty. -/
theorem reductionPreimage_nonempty_of_produces
    {T : Map} {p x : BitString} {B A : Finset BitString} {hA : A.Nonempty}
    (hxB : x ∈ B)
    (hpx : produces T p x (codedUniformOn A hA).code) :
    (reductionPreimage T p B A hA).Nonempty := by
  exact ⟨x, (mem_reductionPreimage T p B A hA x).mpr ⟨hxB, hpx⟩⟩

/-- Extract the source's total program `p` and the resulting nonempty preimage
from strongness of `A` and membership of `x` in `B`.  This closes the first
logical leaf of the second half of `thm:step-wise`; no computability conclusion
about the filter is assumed. -/
theorem IsStrongSetModel.exists_reductionPreimage_program
    {T : Map} {x : BitString} {A B : Finset BitString} {hA : A.Nonempty}
    {epsilon : Nat}
    (hxB : x ∈ B)
    (hstrong : IsStrongSetModel T x A hA epsilon) :
    ∃ p : BitString,
      IsTotalProgram T p ∧
      p.length ≤ epsilon ∧
      x ∈ reductionPreimage T p B A hA ∧
      (reductionPreimage T p B A hA).Nonempty := by
  obtain ⟨p, hpTotal, hpLen, hpProd⟩ :=
    (totalCondK_le_iff T (codedUniformOn A hA).code x epsilon).mp hstrong
  have hxD : x ∈ reductionPreimage T p B A hA :=
    (mem_reductionPreimage T p B A hA x).mpr ⟨hxB, hpProd⟩
  exact ⟨p, hpTotal, hpLen, hxD, ⟨x, hxD⟩⟩

/-! ### Executing the finite preimage filter -/

/-- Given aligned `(input, output)` pairs, retain the inputs whose output is
the requested target code. -/
def reductionFiberList
    (pairs : List (BitString × BitString)) (target : BitString) :
    List BitString :=
  (pairs.filter (fun q => decide (q.2 = target))).map Prod.fst

/-- Membership in a reduction fibre computed from the graph of a function. -/
theorem mem_reductionFiberList_map
    (xs : List BitString) (f : BitString → BitString)
    (target a : BitString) :
    a ∈ reductionFiberList (xs.map (fun x => (x, f x))) target ↔
      a ∈ xs ∧ f a = target := by
  unfold reductionFiberList
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists]
  constructor
  · rintro ⟨a', out, ⟨hpairs, hout⟩, rfl⟩
    obtain ⟨a'', ha'', hpair⟩ := hpairs
    rw [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨ha'', hout⟩
  · rintro ⟨ha, hfa⟩
    exact ⟨a, f a, ⟨⟨a, ha, rfl⟩, hfa⟩, rfl⟩

/-- Post-process the outputs of `p` on the decoded members of `B`: filter for
the target code `[A]` and return the canonical code of that fibre. -/
noncomputable def reductionPreimagePostFn
    (input : BitString × BitString) (ys : List BitString) : BitString :=
  canonicalImageCodeOfList
    (reductionFiberList
      (zipStrings
        (canonicalPointListOfCode (decodeSecond input.2)) ys)
      (decodeFirst input.2))

/-- Selecting the fibre over the target code and encoding it is computable in both arguments. -/
theorem reductionPreimagePostFn_computable :
    Computable₂ reductionPreimagePostFn := by
  have hfilter : Primrec₂ reductionFiberList := by
    unfold reductionFiberList
    have heq : Primrec₂ (fun (a b : BitString) => decide (a = b)) := by
      convert Primrec.eq
      any_goals exact BitString
      · convert Iff.rfl
        exact primrecRel_iff_primrec_decide
    have hfiltered : Primrec
        (fun input : List (BitString × BitString) × BitString =>
          input.1.filter (fun q => decide (q.2 = input.2))) := by
      refine list_filter_primrec Primrec.fst ?_
      exact (heq.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)).to₂
    exact (Primrec.list_map hfiltered
      (Primrec.fst.comp Primrec.snd).to₂)
  have h : Primrec
      (fun q : (BitString × BitString) × List BitString =>
        canonicalImageCodeOfList
          (reductionFiberList
            (zipStrings
              (canonicalPointListOfCode (decodeSecond q.1.2)) q.2)
            (decodeFirst q.1.2))) :=
    canonicalImageCodeOfList_primrec.comp
      (hfilter.comp
        (zipStrings_primrec.comp
          (canonicalPointListOfCode_primrec.comp
            (decodeSecond_primrec.comp
              (Primrec.snd.comp Primrec.fst)))
          Primrec.snd)
        (decodeFirst_primrec.comp
          (Primrec.snd.comp Primrec.fst)))
  exact h.to_comp

/-- A decompressor whose program is `p` and whose condition is the pair
`([A],[B])`; it runs `p` over all decoded members of `B` and emits the canonical
code of the `[A]` fibre. -/
noncomputable def reductionPreimageDecompressor (T : Map) : Map :=
  fun input =>
    (totalProgramMapList T
      (input.1, canonicalPointListOfCode (decodeSecond input.2))).map
      (reductionPreimagePostFn input)

/-- The machine computing the preimage of `[A]` inside `B` under a total program is a decompressor.
The machine computing the preimage of `[A]` inside `B` under a total program is a decompressor. -/
theorem reductionPreimageDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (reductionPreimageDecompressor T) := by
  have hexec : Partrec
      (fun input : BitString × BitString =>
        totalProgramMapList T
          (input.1, canonicalPointListOfCode (decodeSecond input.2))) :=
    Partrec.comp (totalProgramMapList_partrec T hT)
      (Computable.pair Computable.fst
        (canonicalPointListOfCode_computable.comp
          (decodeSecond_computable.comp Computable.snd)))
  exact Partrec.map hexec reductionPreimagePostFn_computable

/-- The finite preimage executor halts on every condition whenever `p` is a
total program of `T`. -/
theorem reductionPreimageDecompressor_total
    {T : Map} {p : BitString} (hp : IsTotalProgram T p) :
    IsTotalProgram (reductionPreimageDecompressor T) p := by
  intro condition
  unfold reductionPreimageDecompressor
  rw [Part.dom_iff_mem]
  obtain ⟨ys, hys⟩ := Part.dom_iff_mem.mp
    (totalProgramMapList_dom_of_total hp
      (canonicalPointListOfCode (decodeSecond condition)))
  exact ⟨reductionPreimagePostFn (p, condition) ys,
    (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩⟩

/-- The output fibre list has exactly the reduction preimage as its finite set. -/
theorem reductionFiberList_toFinset_eq_reductionPreimage
    {T : Map} {p : BitString} (hp : IsTotalProgram T p)
    (B A : Finset BitString) (hA : A.Nonempty) :
    (reductionFiberList
      ((canonicalFinsetList B).map
        (fun x => (x, totalProgOutput T p hp x)))
      (codedUniformOn A hA).code).toFinset =
        reductionPreimage T p B A hA := by
  ext x
  rw [List.mem_toFinset, mem_reductionFiberList_map,
    mem_canonicalFinsetList, mem_reductionPreimage]
  constructor
  · rintro ⟨hxB, hout⟩
    have hprod := totalProgOutput_produces T p hp x
    rw [hout] at hprod
    exact ⟨hxB, hprod⟩
  · rintro ⟨hxB, hprod⟩
    exact ⟨hxB, (produces_eq_totalProgOutput hp hprod).symm⟩

/-- Evaluation of the finite preimage decompressor on canonical model codes. -/
theorem reductionPreimageDecompressor_produces
    {T : Map} {p : BitString} (hp : IsTotalProgram T p)
    (B A : Finset BitString) (hA : A.Nonempty) (hB : B.Nonempty)
    (hD : (reductionPreimage T p B A hA).Nonempty) :
    produces (reductionPreimageDecompressor T) p
      (pairCode (codedUniformOn A hA).code
        (codedUniformOn B hB).code)
      (codedUniformOn (reductionPreimage T p B A hA) hD).code := by
  obtain ⟨ys, hys⟩ := Part.dom_iff_mem.mp
    (totalProgramMapList_dom_of_total hp (canonicalFinsetList B))
  have hys_eq : ys = (canonicalFinsetList B).map (totalProgOutput T p hp) :=
    totalProgramMapList_eq_map hp hys
  let L := reductionFiberList
    ((canonicalFinsetList B).map (fun x => (x, totalProgOutput T p hp x)))
    (codedUniformOn A hA).code
  have hLset : L.toFinset = reductionPreimage T p B A hA :=
    reductionFiberList_toFinset_eq_reductionPreimage hp B A hA
  have hL : L.toFinset.Nonempty := hLset.symm ▸ hD
  have hout : reductionPreimagePostFn
      (p, pairCode (codedUniformOn A hA).code (codedUniformOn B hB).code) ys =
      (codedUniformOn (reductionPreimage T p B A hA) hD).code := by
    unfold reductionPreimagePostFn
    simp only [decodeSecond_pairCode, decodeFirst_pairCode,
      canonicalPointListOfCode_codedUniformOn]
    rw [hys_eq, zipStrings_map_self]
    change canonicalImageCodeOfList L = _
    rw [canonicalImageCodeOfList_eq_codedUniformOn L hL]
    exact codedUniformOn_code_congr hL hD hLset
  unfold produces reductionPreimageDecompressor
  simp only [decodeSecond_pairCode, canonicalPointListOfCode_codedUniformOn]
  exact (Part.mem_map_iff _).2 ⟨ys, hys, hout⟩

/-! ### Statements of the total-reduction conclusions -/

/-- Executable-filter coding leaf, with both models supplied in the condition.

The source informally writes `C(D | A) ≤ |p| + O(1)`, although its `D` also
depends on `B`.  The literal computable fact conditions on the canonical codes
of both `A` and `B`.  Totality of `p` is explicit and is what makes it possible
to run `p` on every member of `B`. -/
def ReductionPreimageCondKGivenModelsStatement (V T : Map) : Prop :=
  ∃ c : Nat, ∀ (p : BitString) (B A : Finset BitString)
      (hA : A.Nonempty) (hB : B.Nonempty)
      (hD : (reductionPreimage T p B A hA).Nonempty),
    IsTotalProgram T p →
    condK V
        (codedUniformOn (reductionPreimage T p B A hA) hD).code
        (pairCode (codedUniformOn A hA).code (codedUniformOn B hB).code) ≤
      (p.length + c : Nat)

/-- The executable-filter coding statement is discharged for an optimal plain
machine and a computable total-program machine.  Notice that the conclusion is
ordinary conditional complexity; totality is used to make the finite traversal
halt, not to change the target complexity notion. -/
theorem reductionPreimage_condK_given_models
    (V : Map) (hV : isOptimalConditional V)
    (T : Map) (hT : isDecompressor T) :
    ReductionPreimageCondKGivenModelsStatement V T := by
  obtain ⟨c, hc⟩ := hV.2 (reductionPreimageDecompressor T)
    (reductionPreimageDecompressor_partrec T hT)
  refine ⟨c, ?_⟩
  intro p B A hA hB hD hp
  have hprod :=
    reductionPreimageDecompressor_produces hp B A hA hB hD
  calc
    condK V
        (codedUniformOn (reductionPreimage T p B A hA) hD).code
        (pairCode (codedUniformOn A hA).code (codedUniformOn B hB).code)
      ≤ condK (reductionPreimageDecompressor T)
          (codedUniformOn (reductionPreimage T p B A hA) hD).code
          (pairCode (codedUniformOn A hA).code
            (codedUniformOn B hB).code) + (c : ENat) :=
        hc _ _
    _ ≤ (p.length : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨p, hprod, rfl⟩
    _ = ((p.length + c : Nat) : ENat) := by norm_cast

/-! ### Composing a conditional description of `A` with the total filter -/

/-- First use an ordinary program to obtain `[A]` from `[B]`, then use the
total program `p` to compute the `[A]` fibre inside `B`.  The two programs are
packed with the binary-length framing from `TotalReduction`. -/
noncomputable def reductionPreimageFromBDecompressor (V T : Map) : Map :=
  fun input =>
    (V (decodeTotalProgramPairFirst input.1, input.2)).bind fun codeA =>
      reductionPreimageDecompressor T
        (decodeTotalProgramPairSecond input.1,
          pairCode codeA input.2)

/-- The input transformation for the second half of
`reductionPreimageFromBDecompressor`, separated so its computability proof is
checked once instead of being unfolded throughout the `Partrec.bind` term. -/
def reductionPreimageFromBSecondInput
    (q : (BitString × BitString) × BitString) : BitString × BitString :=
  (decodeTotalProgramPairSecond q.1.1, pairCode q.2 q.1.2)

/-- Assembling the input of the second stage of the preimage machine is computable. -/
theorem reductionPreimageFromBSecondInput_computable :
    Computable reductionPreimageFromBSecondInput := by
  have houterFirst : Computable
      (fun q : (BitString × BitString) × BitString => q.1) :=
    Computable.fst
  have hprogram : Computable
      (fun q : (BitString × BitString) × BitString =>
        decodeTotalProgramPairSecond q.1.1) :=
    decodeTotalProgramPairSecond_computable.comp
      (Computable.fst.comp houterFirst)
  have hcodes : Primrec
      (fun q : (BitString × BitString) × BitString =>
        pairCode q.2 q.1.2) :=
    pairCode_primrec.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)
  exact hprogram.pair hcodes.to_comp

/-- The machine that first describes `[A]` from `[B]` and then takes the preimage is a decompressor.
The machine that first describes `[A]` from `[B]` and then takes the preimage is a decompressor. -/
theorem reductionPreimageFromBDecompressor_partrec
    (V T : Map) (hV : isDecompressor V) (hT : isDecompressor T) :
    isDecompressor (reductionPreimageFromBDecompressor V T) := by
  have hfirst : Partrec
      (fun input : BitString × BitString =>
        V (decodeTotalProgramPairFirst input.1, input.2)) :=
    Partrec.comp hV
      (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp Computable.fst)
        Computable.snd)
  have hsecond : Partrec
      (fun q : (BitString × BitString) × BitString =>
        reductionPreimageDecompressor T
          (decodeTotalProgramPairSecond q.1.1,
            pairCode q.2 q.1.2)) :=
    Partrec.comp (reductionPreimageDecompressor_partrec T hT)
      reductionPreimageFromBSecondInput_computable
  exact Partrec.bind hfirst hsecond

/-- On the framed pair of a program describing `[A]` from `[B]` and a program computing the fibre,
the composite machine outputs the fibre code from `[B]` alone. -/
theorem reductionPreimageFromBDecompressor_produces
    {V T : Map} {q p codeA codeB codeD : BitString}
    (hq : produces V q codeB codeA)
    (hp : produces (reductionPreimageDecompressor T) p
      (pairCode codeA codeB) codeD) :
    produces (reductionPreimageFromBDecompressor V T)
      (totalProgramPairCode q p) codeB codeD := by
  unfold produces reductionPreimageFromBDecompressor
  rw [decodeTotalProgramPairFirst_pair,
    decodeTotalProgramPairSecond_pair, Part.mem_bind_iff]
  exact ⟨codeA, hq, hp⟩

/-- The source's first quantitative preimage bound.

Here both `A` and `B` retain their theorem-level sufficiency hypotheses so the
self-delimiting cost of composing a shortest program for `[A]` from `[B]` with
`p` can be absorbed uniformly into `O(epsilon + log n)`.  Omitting totality of
`p`, or allowing arbitrary nonsufficient `A`, would make this statement stronger
than the proof in the source. -/
def ReductionPreimageCondKGivenBStatement (V T : Map) : Prop :=
  ∃ c : Nat, ∀ (x p : BitString) (n epsilon : Nat)
      (B A : Finset BitString) (hA : A.Nonempty) (hB : B.Nonempty)
      (hD : (reductionPreimage T p B A hA).Nonempty),
    x.length = n →
    IsTotalProgram T p →
    p.length ≤ epsilon →
    x ∈ reductionPreimage T p B A hA →
    IsSufficientStatistic V x A hA epsilon →
    IsSufficientStatistic V x B hB epsilon →
    condK V
        (codedUniformOn (reductionPreimage T p B A hA) hD).code
        (codedUniformOn B hB).code ≤
      condK V (codedUniformOn A hA).code (codedUniformOn B hB).code +
        (c * epsilon + logSlack c n : Nat)

/-- Discharge the first quantitative preimage statement.  The only
self-delimiting overhead is the binary length of the ordinary program for
`[A]` from `[B]`; sufficiency of `A` and the literal bound for `x` bound that
program by `n + epsilon + O(1)`, allowing the header to be absorbed into the
displayed `O(epsilon + log n)` budget. -/
theorem reductionPreimage_condK_given_B
    (V : Map) (hV : isOptimalConditional V)
    (T : Map) (hT : isDecompressor T) :
    ReductionPreimageCondKGivenBStatement V T := by
  obtain ⟨cSim, hSim⟩ := hV.2 (reductionPreimageFromBDecompressor V T)
    (reductionPreimageFromBDecompressor_partrec V T hV.1 hT)
  obtain ⟨cLiteral, hLiteral⟩ := plainK_le_length V hV
  obtain ⟨cDrop, hDrop⟩ := condK_le_plainK V hV
  let c := 2 * (cLiteral + cDrop) + cSim + 5
  refine ⟨c, ?_⟩
  intro x p n epsilon B A hA hB hD hxlen hpTotal hpLen hxD hstatA hstatB
  have hAcomp : plainSetComplexity V A hA ≤
      plainK V x + (epsilon : ENat) := by
    exact (le_add_of_nonneg_right (zero_le)).trans
      hstatA.2
  have hcondBound :
      condK V (codedUniformOn A hA).code (codedUniformOn B hB).code ≤
        ((n + epsilon + cLiteral + cDrop : Nat) : ENat) := by
    calc
      condK V (codedUniformOn A hA).code (codedUniformOn B hB).code
        ≤ plainK V (codedUniformOn A hA).code + (cDrop : ENat) :=
          hDrop _ _
      _ = plainSetComplexity V A hA + (cDrop : ENat) := rfl
      _ ≤ (plainK V x + (epsilon : ENat)) + (cDrop : ENat) := by
        gcongr
      _ ≤ (((n : Nat) : ENat) + (cLiteral : ENat)) +
          (epsilon : ENat) + (cDrop : ENat) := by
        gcongr
        simpa [hxlen] using hLiteral x
      _ = ((n + epsilon + cLiteral + cDrop : Nat) : ENat) := by
        push_cast
        ring
  have hcondFinite :
      condK V (codedUniformOn A hA).code
        (codedUniformOn B hB).code ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hcondBound
  let qLen := (condK V (codedUniformOn A hA).code
    (codedUniformOn B hB).code).toNat
  have hqLenValue :
      condK V (codedUniformOn A hA).code
        (codedUniformOn B hB).code = (qLen : ENat) := by
    exact (ENat.natCast_toNat hcondFinite).symm
  have hqLenBound : qLen ≤ n + epsilon + cLiteral + cDrop := by
    rw [hqLenValue] at hcondBound
    exact_mod_cast hcondBound
  obtain ⟨q, hqLength, hqProd⟩ :=
    (condK_le_iff V (codedUniformOn A hA).code
      (codedUniformOn B hB).code qLen).mp (by rw [hqLenValue])
  change q.length ≤ qLen at hqLength
  have hpFilter :=
    reductionPreimageDecompressor_produces hpTotal B A hA hB hD
  have hprod := reductionPreimageFromBDecompressor_produces hqProd hpFilter
  have hqBits : (Nat.bits q.length).length ≤
      (Nat.bits (n + epsilon + cLiteral + cDrop)).length :=
    length_natBits_mono (hqLength.trans hqLenBound)
  have hsumBits :
      (Nat.bits (n + epsilon + cLiteral + cDrop)).length ≤
        (Nat.bits n).length + epsilon + cLiteral + cDrop + 1 := by
    calc
      (Nat.bits (n + epsilon + cLiteral + cDrop)).length =
          (Nat.bits (n + (epsilon + cLiteral + cDrop))).length := by
            congr 2
            omega
      _ ≤ (Nat.bits n).length +
          (Nat.bits (epsilon + cLiteral + cDrop)).length + 1 :=
            length_natBits_add_le n (epsilon + cLiteral + cDrop)
      _ ≤ (Nat.bits n).length + epsilon + cLiteral + cDrop + 1 := by
        have htail := length_natBits_le (epsilon + cLiteral + cDrop)
        omega
  have hframe :
      p.length + 2 * (Nat.bits q.length).length + 1 + cSim ≤
        c * epsilon + logSlack c n := by
    dsimp [c]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  calc
    condK V
        (codedUniformOn (reductionPreimage T p B A hA) hD).code
        (codedUniformOn B hB).code
      ≤ condK (reductionPreimageFromBDecompressor V T)
          (codedUniformOn (reductionPreimage T p B A hA) hD).code
          (codedUniformOn B hB).code + (cSim : ENat) := hSim _ _
    _ ≤ ((totalProgramPairCode q p).length : ENat) + (cSim : ENat) := by
      gcongr
      exact sInf_le ⟨totalProgramPairCode q p, hprod, rfl⟩
    _ = ((q.length + p.length + 2 * (Nat.bits q.length).length + 1 + cSim : Nat) :
        ENat) := by
      rw [length_totalProgramPairCode]
      norm_cast
    _ ≤ ((qLen + (c * epsilon + logSlack c n) : Nat) : ENat) := by
      exact_mod_cast (show
        q.length + p.length + 2 * (Nat.bits q.length).length + 1 + cSim ≤
          qLen + (c * epsilon + logSlack c n) by omega)
    _ = (qLen : ENat) + (c * epsilon + logSlack c n : Nat) := by
      norm_cast
    _ = condK V (codedUniformOn A hA).code (codedUniformOn B hB).code +
        (c * epsilon + logSlack c n : Nat) := by rw [hqLenValue]

/-! ### Describing an element through a conditionally described model -/

/-- Plain fixed-length index decoder for a canonical finite-set code.  Unlike
the prefix decoder used elsewhere in the library, this decoder only needs to
be a plain partial-recursive map; the caller supplies the exact
`finiteSetLogCard`-bit address. -/
noncomputable def reductionSetIndexDecompressor : Map := fun input =>
  Part.some
    ((canonicalPointListOfCode input.2).getD (bitsToNat input.1) [])

/-- The plain fixed-length index decoder for canonical set codes is a decompressor. -/
theorem reductionSetIndexDecompressor_partrec :
    isDecompressor reductionSetIndexDecompressor := by
  have hout : Computable (fun input : BitString × BitString =>
      (canonicalPointListOfCode input.2).getD (bitsToNat input.1) []) :=
    (Primrec.list_getD ([] : BitString)).to_comp.comp
      (canonicalPointListOfCode_computable.comp Computable.snd)
      (bitsToNat_primrec.to_comp.comp Computable.fst)
  exact hout.partrec

/-- Given the code of the uniform distribution on `S` and the address of `x` in the canonical
listing of `S`, the index decoder outputs `x`. -/
theorem reductionSetIndexDecompressor_produces
    (S : Finset BitString) (hS : S.Nonempty) (x : BitString)
    (hx : x ∈ S) :
    let s := finiteSetLogCard S
    let idx := (canonicalFinsetList S).findIdx (· == x)
    produces reductionSetIndexDecompressor (chunkAddress idx s)
      (codedUniformOn S hS).code x := by
  intro s idx
  have hxList : x ∈ canonicalFinsetList S :=
    mem_canonicalFinsetList.mpr hx
  have hidx : idx < (canonicalFinsetList S).length := by
    dsimp [idx]
    rw [List.findIdx_lt_length]
    exact ⟨x, hxList, by simp⟩
  have hget : (canonicalFinsetList S).getD idx [] = x := by
    rw [List.getD_eq_getElem _ _ hidx]
    exact eq_of_beq
      (List.findIdx_getElem (p := (· == x)) (w := hidx))
  unfold produces reductionSetIndexDecompressor
  simp only [Part.mem_some_iff,
    canonicalPointListOfCode_codedUniformOn,
    bitsToNat_chunkAddress]
  exact hget.symm

/-- First decode a finite-set code from the original condition, then decode a
fixed-length ordinal inside that set.  The two programs use the binary-length
framing from `TotalReduction`, so the first program is charged only once. -/
noncomputable def reductionModelElementDecompressor (V : Map) : Map :=
  fun input =>
    (V (decodeTotalProgramPairFirst input.1, input.2)).bind fun codeS =>
      reductionSetIndexDecompressor
        (decodeTotalProgramPairSecond input.1, codeS)

/-- The machine that describes a model from `[B]` and then indexes into it is a decompressor. -/
theorem reductionModelElementDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (reductionModelElementDecompressor V) := by
  have hfirst : Partrec
      (fun input : BitString × BitString =>
        V (decodeTotalProgramPairFirst input.1, input.2)) :=
    Partrec.comp hV
      (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp Computable.fst)
        Computable.snd)
  have hsecond : Partrec
      (fun input : (BitString × BitString) × BitString =>
        reductionSetIndexDecompressor
          (decodeTotalProgramPairSecond input.1.1, input.2)) :=
    Partrec.comp reductionSetIndexDecompressor_partrec
      (Computable.pair
        (decodeTotalProgramPairSecond_computable.comp
          (Computable.fst.comp Computable.fst))
        Computable.snd)
  exact Partrec.bind hfirst hsecond

/-- On the framed pair of a program describing the model code from `[B]` and an address inside that
model, the composite machine outputs the addressed element. -/
theorem reductionModelElementDecompressor_produces
    {V : Map} {q r codeB codeS x : BitString}
    (hq : produces V q codeB codeS)
    (hr : produces reductionSetIndexDecompressor r codeS x) :
    produces (reductionModelElementDecompressor V)
      (totalProgramPairCode q r) codeB x := by
  unfold produces reductionModelElementDecompressor
  rw [decodeTotalProgramPairFirst_pair,
    Part.mem_bind_iff]
  refine ⟨codeS, hq, ?_⟩
  simpa using hr

/-- Conditional two-stage coding through a finite set.  If the set code costs
at most `a` bits given the original condition, an element costs `a` plus its
exact ceiling-log ordinal and the self-delimiting header for the first
program. -/
theorem condK_element_via_model
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (B D : Finset BitString)
        (hB : B.Nonempty) (hD : D.Nonempty)
        (x : BitString) (a : Nat),
      x ∈ D →
      condK V (codedUniformOn D hD).code
          (codedUniformOn B hB).code ≤ (a : ENat) →
      condK V x (codedUniformOn B hB).code ≤
        (a + finiteSetLogCard D +
          2 * (Nat.bits a).length + c : Nat) := by
  obtain ⟨cSim, hSim⟩ := hV.2 (reductionModelElementDecompressor V)
    (reductionModelElementDecompressor_partrec V hV.1)
  refine ⟨cSim + 1, ?_⟩
  intro B D hB hD x a hxD hcond
  obtain ⟨q, hqLen, hqProd⟩ :=
    (condK_le_iff V (codedUniformOn D hD).code
      (codedUniformOn B hB).code a).mp hcond
  change q.length ≤ a at hqLen
  let s := finiteSetLogCard D
  let idx := (canonicalFinsetList D).findIdx (· == x)
  let r := chunkAddress idx s
  have hidxCard : idx < D.card := by
    dsimp [idx]
    rw [← length_canonicalFinsetList, List.findIdx_lt_length]
    exact ⟨x, mem_canonicalFinsetList.mpr hxD, by simp⟩
  have hidxPow : idx < 2 ^ s :=
    hidxCard.trans_le (finiteSetLogCard_spec D)
  have hrLen : r.length = s :=
    chunkAddress_length idx s hidxPow
  have hrProd : produces reductionSetIndexDecompressor r
      (codedUniformOn D hD).code x := by
    exact reductionSetIndexDecompressor_produces D hD x hxD
  have hprod := reductionModelElementDecompressor_produces hqProd hrProd
  have hqBits : (Nat.bits q.length).length ≤ (Nat.bits a).length :=
    length_natBits_mono hqLen
  calc
    condK V x (codedUniformOn B hB).code
      ≤ condK (reductionModelElementDecompressor V) x
          (codedUniformOn B hB).code + (cSim : ENat) := hSim _ _
    _ ≤ ((totalProgramPairCode q r).length : ENat) + (cSim : ENat) := by
      gcongr
      exact sInf_le ⟨totalProgramPairCode q r, hprod, rfl⟩
    _ = ((q.length + r.length +
          2 * (Nat.bits q.length).length + 1 + cSim : Nat) : ENat) := by
      rw [length_totalProgramPairCode]
      norm_cast
    _ ≤ ((a + s + 2 * (Nat.bits a).length + (cSim + 1) : Nat) : ENat) := by
      exact_mod_cast (show q.length + r.length +
        2 * (Nat.bits q.length).length + 1 + cSim ≤
          a + s + 2 * (Nat.bits a).length + (cSim + 1) by
        rw [hrLen]
        omega)

/-- The easy, logarithmically sharp two-stage plain coding inequality.  This
is only the subadditive direction and does not use symmetry of information. -/
theorem plainK_two_stage
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x y : BitString) (a b : Nat),
      plainK V y ≤ (a : ENat) →
      condK V x y ≤ (b : ENat) →
      plainK V x ≤
        (a + b + 2 * (Nat.bits a).length + c : Nat) := by
  obtain ⟨cSim, hSim⟩ := hV.2
    (totalLengthPrefixedComposeDecompressor V)
    (totalLengthPrefixedComposeDecompressor_partrec hV.1)
  refine ⟨cSim + 1, ?_⟩
  intro x y a b hy hxy
  obtain ⟨p, hpLen, hpProd⟩ :=
    (condK_le_iff V y [] a).mp hy
  obtain ⟨q, hqLen, hqProd⟩ :=
    (condK_le_iff V x y b).mp hxy
  change p.length ≤ a at hpLen
  change q.length ≤ b at hqLen
  have hprod := totalLengthPrefixedComposeDecompressor_produces
    hpProd hqProd
  have hpBits : (Nat.bits p.length).length ≤ (Nat.bits a).length :=
    length_natBits_mono hpLen
  calc
    plainK V x
      ≤ condK (totalLengthPrefixedComposeDecompressor V) x [] +
          (cSim : ENat) := hSim _ _
    _ ≤ ((totalProgramPairCode p q).length : ENat) + (cSim : ENat) := by
      gcongr
      exact sInf_le ⟨totalProgramPairCode p q, hprod, rfl⟩
    _ = ((p.length + q.length +
          2 * (Nat.bits p.length).length + 1 + cSim : Nat) : ENat) := by
      rw [length_totalProgramPairCode]
      norm_cast
    _ ≤ ((a + b + 2 * (Nat.bits a).length + (cSim + 1) : Nat) : ENat) := by
      exact_mod_cast (show p.length + q.length +
        2 * (Nat.bits p.length).length + 1 + cSim ≤
          a + b + 2 * (Nat.bits a).length + (cSim + 1) by omega)

/-- Cardinality consequence of the preimage argument.

This is the precise form used in the source: sufficiency of `B`, the
conditional two-part description of `x` through `D`, and the easy plain
two-stage coding inequality imply that `D` occupies at least a
`2^(-C(A|B)-O(epsilon+log n))` fraction of `B`.  Both sufficiency hypotheses
are retained for the same uniform coding-budget reason as above. -/
def ReductionPreimageCardLowerStatement (V T : Map) : Prop :=
  ∃ c : Nat, ∀ (x p : BitString) (n epsilon : Nat)
      (B A : Finset BitString) (hA : A.Nonempty) (hB : B.Nonempty),
    x.length = n →
    IsTotalProgram T p →
    p.length ≤ epsilon →
    x ∈ reductionPreimage T p B A hA →
    IsSufficientStatistic V x A hA epsilon →
    IsSufficientStatistic V x B hB epsilon →
    (finiteSetLogCard B : ENat) ≤
      (finiteSetLogCard (reductionPreimage T p B A hA) : ENat) +
      condK V (codedUniformOn A hA).code (codedUniformOn B hB).code +
      (c * epsilon + logSlack c n : Nat)

/-- Bounding the bit-length of a number bounded by `n + tail`. -/
private theorem length_natBits_le_of_le_add {x n tail : Nat} (h : x ≤ n + tail) :
    (Nat.bits x).length ≤ (Nat.bits n).length + tail + 1 := by
  calc
    (Nat.bits x).length ≤ (Nat.bits (n + tail)).length := length_natBits_mono h
    _ ≤ (Nat.bits n).length + (Nat.bits tail).length + 1 :=
      length_natBits_add_le n tail
    _ ≤ (Nat.bits n).length + tail + 1 := by
      have htail := length_natBits_le tail
      omega

/-- Upper bound on the plain set complexity of a sufficient statistic set. -/
private theorem plainSetComplexity_le_of_isSufficientStatistic
    {V : Map} {x : BitString} {A : Finset BitString} {hA : A.Nonempty} {epsilon : Nat}
    (hstat : IsSufficientStatistic V x A hA epsilon) :
    plainSetComplexity V A hA ≤ plainK V x + (epsilon : ENat) :=
  (le_add_of_nonneg_right (zero_le)).trans hstat.2

/-- Upper bound on plain set complexity in terms of string length and sufficiency slack. -/
private theorem plainSetComplexity_le_length_add_epsilon
    (V : Map) (cLiteral : Nat) (hLiteral : ∀ x, plainK V x ≤ x.length + cLiteral)
    {x : BitString} {A : Finset BitString} {hA : A.Nonempty} {n epsilon : Nat}
    (hxlen : x.length = n) (hstat : IsSufficientStatistic V x A hA epsilon) :
    plainSetComplexity V A hA ≤ ((n + epsilon + cLiteral : Nat) : ENat) := by
  calc
    plainSetComplexity V A hA
      ≤ plainK V x + (epsilon : ENat) := plainSetComplexity_le_of_isSufficientStatistic hstat
    _ ≤ (((n : Nat) : ENat) + (cLiteral : ENat)) + (epsilon : ENat) := by
      gcongr
      simpa [hxlen] using hLiteral x
    _ = ((n + epsilon + cLiteral : Nat) : ENat) := by
      push_cast
      ring

/-- Upper bound on conditional set complexity in terms of string length and sufficiency slack. -/
private theorem condK_set_le_length_add_epsilon
    (V : Map) (cLiteral cDrop : Nat)
    (hLiteral : ∀ x, plainK V x ≤ x.length + cLiteral)
    (hDrop : ∀ A B, condK V A B ≤ plainK V A + cDrop)
    {x : BitString} {A : Finset BitString} {hA : A.Nonempty}
    (B : Finset BitString) (hB : B.Nonempty) {n epsilon : Nat}
    (hxlen : x.length = n) (hstatA : IsSufficientStatistic V x A hA epsilon) :
    condK V (codedUniformOn A hA).code (codedUniformOn B hB).code ≤
      ((n + epsilon + cLiteral + cDrop : Nat) : ENat) := by
  calc
    condK V (codedUniformOn A hA).code (codedUniformOn B hB).code
      ≤ plainK V (codedUniformOn A hA).code + (cDrop : ENat) := hDrop _ _
    _ = plainSetComplexity V A hA + (cDrop : ENat) := rfl
    _ ≤ (plainK V x + (epsilon : ENat)) + (cDrop : ENat) := by
      gcongr
      exact plainSetComplexity_le_of_isSufficientStatistic hstatA
    _ ≤ (((n : Nat) : ENat) + (cLiteral : ENat)) + (epsilon : ENat) + (cDrop : ENat) := by
      gcongr
      simpa [hxlen] using hLiteral x
    _ = ((n + epsilon + cLiteral + cDrop : Nat) : ENat) := by
      push_cast
      ring

/-- Pure arithmetic budget bound for the preimage cardinality lower bound. -/
private theorem reductionPreimage_budget_le
    (cPre cLiteral cDrop cElem cTwo epsilon n q b logD : Nat)
    (hq : q ≤ n + epsilon + cLiteral + cDrop)
    (hb : b ≤ n + epsilon + cLiteral) :
    let c := 4 * cPre + 4 * cLiteral + 2 * cDrop + cElem + cTwo + 10
    let preSlack := cPre * epsilon + logSlack cPre n
    let a := q + preSlack
    let dBound := a + logD + 2 * (Nat.bits a).length + cElem
    let rest := dBound + 2 * (Nat.bits b).length + cTwo + epsilon
    rest ≤ logD + q + (c * epsilon + logSlack c n) := by
  intro c preSlack a dBound rest
  have haBound : a ≤ n + ((cPre + 1) * epsilon + cPre * (Nat.bits n).length +
      cPre + cLiteral + cDrop) := by
    dsimp [a, preSlack, logSlack]
    nlinarith
  have haBits : (Nat.bits a).length ≤ (Nat.bits n).length +
      ((cPre + 1) * epsilon + cPre * (Nat.bits n).length + cPre + cLiteral + cDrop) + 1 :=
    length_natBits_le_of_le_add haBound
  have hbBits : (Nat.bits b).length ≤ (Nat.bits n).length + (epsilon + cLiteral) + 1 :=
    length_natBits_le_of_le_add (by omega)
  dsimp [rest, dBound, a, preSlack, c, logSlack] at *
  nlinarith [Nat.zero_le ((Nat.bits n).length)]

/-- The preimage-cardinality lower bound.  The proof uses only the easy
two-stage coding direction: conditionally describe the fibre from `B`, index
`x` inside that fibre, and then prepend a shortest plain description of `B`.
Sufficiency of `B` cancels the latter description length.  No symmetry of
information is used. -/
theorem reductionPreimage_card_lower
    (V : Map) (hV : isOptimalConditional V)
    (T : Map) (hT : isDecompressor T) :
    ReductionPreimageCardLowerStatement V T := by
  obtain ⟨cPre, hPre⟩ := reductionPreimage_condK_given_B V hV T hT
  obtain ⟨cElem, hElem⟩ := condK_element_via_model V hV
  obtain ⟨cTwo, hTwo⟩ := plainK_two_stage V hV
  obtain ⟨cLiteral, hLiteral⟩ := plainK_le_length V hV
  obtain ⟨cDrop, hDrop⟩ := condK_le_plainK V hV
  let c := 4 * cPre + 4 * cLiteral + 2 * cDrop + cElem + cTwo + 10
  refine ⟨c, ?_⟩
  intro x p n epsilon B A hA hB hxlen hpTotal hpLen hxD hstatA hstatB
  let D := reductionPreimage T p B A hA
  have hD : D.Nonempty := ⟨x, hxD⟩
  have hABBound :=
    condK_set_le_length_add_epsilon V cLiteral cDrop hLiteral hDrop B hB hxlen hstatA
  have hABFinite : condK V (codedUniformOn A hA).code (codedUniformOn B hB).code ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hABBound
  let q := (condK V (codedUniformOn A hA).code (codedUniformOn B hB).code).toNat
  have hqValue : condK V (codedUniformOn A hA).code (codedUniformOn B hB).code = (q : ENat) :=
    (ENat.natCast_toNat hABFinite).symm
  have hqBound : q ≤ n + epsilon + cLiteral + cDrop := by
    rw [hqValue] at hABBound
    exact_mod_cast hABBound
  have hBBound :=
    plainSetComplexity_le_length_add_epsilon V cLiteral hLiteral hxlen hstatB
  have hBFinite : plainSetComplexity V B hB ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hBBound
  let b := (plainSetComplexity V B hB).toNat
  have hbValue : plainSetComplexity V B hB = (b : ENat) :=
    (ENat.natCast_toNat hBFinite).symm
  have hbBound : b ≤ n + epsilon + cLiteral := by
    rw [hbValue] at hBBound
    exact_mod_cast hBBound
  let preSlack := cPre * epsilon + logSlack cPre n
  let a := q + preSlack
  have hDB : condK V (codedUniformOn D hD).code (codedUniformOn B hB).code ≤ (a : ENat) := by
    have h := hPre x p n epsilon B A hA hB hD hxlen hpTotal hpLen hxD hstatA hstatB
    change condK V (codedUniformOn D hD).code (codedUniformOn B hB).code ≤ _ at h
    rw [hqValue] at h
    simpa [a, preSlack, Nat.cast_add] using h
  have hxGivenB : condK V x (codedUniformOn B hB).code ≤
      (a + finiteSetLogCard D + 2 * (Nat.bits a).length + cElem : Nat) :=
    hElem B D hB hD x a hxD hDB
  let dBound := a + finiteSetLogCard D + 2 * (Nat.bits a).length + cElem
  have hxPlain : plainK V x ≤ (b + dBound + 2 * (Nat.bits b).length + cTwo : Nat) := by
    apply hTwo x (codedUniformOn B hB).code b dBound
    · change plainSetComplexity V B hB ≤ (b : ENat)
      exact le_of_eq hbValue
    · exact hxGivenB
  let rest := dBound + 2 * (Nat.bits b).length + cTwo + epsilon
  have hcancelInput : (b : ENat) + (finiteSetLogCard B : ENat) ≤ (b : ENat) + (rest : ENat) := by
    calc
      (b : ENat) + (finiteSetLogCard B : ENat)
        = plainSetComplexity V B hB + (finiteSetLogCard B : ENat) := by rw [hbValue]
      _ ≤ plainK V x + (epsilon : ENat) := hstatB.2
      _ ≤ ((b + dBound + 2 * (Nat.bits b).length + cTwo : Nat) : ENat) + (epsilon : ENat) := by
        gcongr
      _ = (b : ENat) + (rest : ENat) := by
        simp [rest]
        norm_cast
        omega
  have hlogB : (finiteSetLogCard B : ENat) ≤ (rest : ENat) :=
    (ENat.add_le_add_iff_left (ENat.natCast_ne_top b)).mp hcancelInput
  have hbudget : rest ≤ finiteSetLogCard D + q + (c * epsilon + logSlack c n) :=
    reductionPreimage_budget_le cPre cLiteral cDrop cElem cTwo epsilon n q b
      (finiteSetLogCard D) hqBound hbBound
  calc
    (finiteSetLogCard B : ENat) ≤ (rest : ENat) := hlogB
    _ ≤ ((finiteSetLogCard D + q + (c * epsilon + logSlack c n) : Nat) : ENat) := by
      exact_mod_cast hbudget
    _ = (finiteSetLogCard D : ENat) +
        condK V (codedUniformOn A hA).code (codedUniformOn B hB).code +
        (c * epsilon + logSlack c n : Nat) := by
      rw [hqValue]
      norm_cast

/-- The number of heavy output fibres is bounded by `2^(logCard B - l + 1)`. -/
theorem heavy_output_count
    (B : Finset BitString) (f : BitString → BitString) (l : Nat) :
    let fiber y := B.filter (fun z => f z = y)
    ((B.image f).filter
      (fun y => l ≤ finiteSetLogCard (fiber y))).card ≤
        2 ^ (finiteSetLogCard B - l + 1) := by
  intro fiber
  set F := (B.image f).filter (fun y => l ≤ finiteSetLogCard (fiber y))
  have h_disj : ∀ y₁ ∈ F, ∀ y₂ ∈ F, y₁ ≠ y₂ → Disjoint (fiber y₁) (fiber y₂) := by
    intro y₁ _ y₂ _ hneq
    simp only [fiber, Finset.disjoint_filter]
    intro x _ h1 h2
    rw [h1] at h2
    exact hneq h2
  have h_sum : ∑ y ∈ F, (fiber y).card = (F.biUnion fiber).card := by
    rw [Finset.card_biUnion h_disj]
  have h_sub : F.biUnion fiber ⊆ B := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨y, _, hx_fib⟩
    rw [Finset.mem_filter] at hx_fib
    exact hx_fib.1
  have h_sum_le_B : ∑ y ∈ F, (fiber y).card ≤ B.card := by
    rw [h_sum]
    exact Finset.card_le_card h_sub
  by_cases hl : l = 0
  · subst hl
    have hF : F.card ≤ (B.image f).card := Finset.card_filter_le _ _
    have h_img : (B.image f).card ≤ B.card := Finset.card_image_le
    have h_B : B.card ≤ 2 ^ finiteSetLogCard B := finiteSetLogCard_spec B
    calc F.card ≤ B.card := hF.trans h_img
      _ ≤ 2 ^ finiteSetLogCard B := h_B
      _ ≤ 2 ^ (finiteSetLogCard B - 0 + 1) := by
        rw [Nat.sub_zero]
        exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  · have h_fib_size : ∀ y ∈ F, 2 ^ (l - 1) ≤ (fiber y).card := by
      intro y hy
      have hy_F : y ∈ (B.image f).filter (fun y => l ≤ finiteSetLogCard (fiber y)) := hy
      rw [Finset.mem_filter] at hy_F
      have h1 : l ≤ finiteSetLogCard (fiber y) := hy_F.2
      have h2 : 1 < (fiber y).card := by
        by_contra h_not
        push Not at h_not
        have : finiteSetLogCard (fiber y) ≤ 1 := by
          apply (finiteSetLogCard_le_iff _ 1).mpr
          exact h_not.trans (by decide)
        have : finiteSetLogCard (fiber y) = 0 := by
          apply Nat.le_zero.mp
          apply (finiteSetLogCard_le_iff _ 0).mpr
          exact h_not.trans (by decide)
        omega
      have h3 : 2 ^ (finiteSetLogCard (fiber y) - 1) < (fiber y).card :=
        finiteSetLogCard_pred_lt _ h2
      have h4 : 2 ^ (l - 1) ≤ 2 ^ (finiteSetLogCard (fiber y) - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h_mul : F.card * 2 ^ (l - 1) ≤ ∑ y ∈ F, (fiber y).card := by
      calc F.card * 2 ^ (l - 1) = ∑ _y ∈ F, 2 ^ (l - 1) := by simp [mul_comm]
        _ ≤ ∑ y ∈ F, (fiber y).card := Finset.sum_le_sum (fun y hy => h_fib_size y hy)
    have h_bound : F.card * 2 ^ (l - 1) ≤ 2 ^ finiteSetLogCard B :=
      h_mul.trans (h_sum_le_B.trans (finiteSetLogCard_spec B))
    have h_pow : 2 ^ (l - 1) * F.card ≤ 2 ^ finiteSetLogCard B := by
      rw [mul_comm]
      exact h_bound
    have hd : 2 ^ (l - 1) * F.card ≤ 2 ^ (l - 1) * 2 ^ (finiteSetLogCard B - l + 1) := by
      calc 2 ^ (l - 1) * F.card ≤ 2 ^ finiteSetLogCard B := h_pow
        _ ≤ 2 ^ (l - 1 + (finiteSetLogCard B - l + 1)) := by
          apply Nat.pow_le_pow_right (by decide)
          omega
        _ = 2 ^ (l - 1) * 2 ^ (finiteSetLogCard B - l + 1) := by rw [Nat.pow_add]
    exact Nat.le_of_mul_le_mul_left hd (by positivity)

/-- The number of occurrences of an output in the image of a duplicate-free
list is the cardinality of its corresponding finite-set fibre. -/
theorem list_count_map_eq_card_filter
    (xs : List BitString) (hxs : xs.Nodup)
    (f : BitString → BitString) (y : BitString) :
    (xs.map f).count y =
      (xs.toFinset.filter (fun x => f x = y)).card := by
  unfold List.count
  rw [List.countP_map, List.countP_eq_length_filter]
  have hset :
      (xs.filter ((fun z => z == y) ∘ f)).toFinset =
        xs.toFinset.filter (fun x => f x = y) := by
    ext x
    rw [List.mem_toFinset, List.mem_filter, Finset.mem_filter,
      List.mem_toFinset]
    simp only [Function.comp_apply, beq_iff_eq]
  rw [← List.toFinset_card_of_nodup
    (hxs.filter ((fun z => z == y) ∘ f)), hset]

/-- A duplicate-free list of the outputs whose fibres have at least
`2^(l-1)` elements.  This slightly rounded threshold includes every output
whose fibre has logarithmic cardinality at least `l`, including the `l = 0`
boundary, and still has the required `2^(log #B-l+1)` length bound. -/
def heavyOutputList (ys : List BitString) (l : Nat) : List BitString :=
  ys.dedup.filter (fun y => 2 ^ (l - 1) ≤ ys.count y)

/-- The second conclusion of `thm:step-wise`, as a statement.

It says that, for two sufficient statistics, strongness of `A` upgrades its
ordinary conditional description from `B` to a total one at the source's
`O(epsilon + log n)` extra cost.  Proving it requires constructing the finite
list of heavy output fibres of `p`; no such list or decoder is included as a
hypothesis. -/
def StrongSufficientStatisticTotalReductionStatement (V T : Map) : Prop :=
  ∃ c : Nat, ∀ (x : BitString) (n epsilon : Nat)
      (A B : Finset BitString) (hA : A.Nonempty) (hB : B.Nonempty),
    x.length = n →
    IsSufficientStatistic V x A hA epsilon →
    IsSufficientStatistic V x B hB epsilon →
    IsStrongSetModel T x A hA epsilon →
    totalCondK T (codedUniformOn A hA).code (codedUniformOn B hB).code ≤
      condK V (codedUniformOn A hA).code (codedUniformOn B hB).code +
        (c * epsilon + logSlack c n : Nat)

end Kolmogorov
