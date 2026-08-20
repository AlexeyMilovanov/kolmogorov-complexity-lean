import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic

/-!
# Strong sufficient statistics

This file starts the S6 proof of the total-complexity conclusion of VS40
Theorem `thm:step-wise`.  If a total program `p` maps `x` to the canonical code
of `A`, and `B` is another sufficient statistic for `x`, the source considers

`D = {x' in B | p(x') = [A]}`.

The elementary set-theoretic and witness-extraction facts, the executable
finite filter, and its two conditional-complexity bounds are proved below.
The cardinality stage uses exact plain two-stage coding.  The final heavy-fibre
stage constructs an explicit total selector, proves its evaluation on a
fixed-width heavy-output index, and transfers it to an optimal total machine.
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

/-! ### Faithful remaining S6 statements -/

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
`p`, or allowing arbitrary nonsufficient `A`, would make this draft stronger
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
  obtain ⟨cLiteral, hLiteral⟩ := plainKLeLength V hV
  obtain ⟨cDrop, hDrop⟩ := condKLePlainK V hV
  let c := 2 * (cLiteral + cDrop) + cSim + 5
  refine ⟨c, ?_⟩
  intro x p n epsilon B A hA hB hD hxlen hpTotal hpLen hxD hstatA hstatB
  have hAcomp : plainSetComplexity V A hA ≤
      plainK V x + (epsilon : ENat) := by
    exact (le_add_of_nonneg_right (zero_le (finiteSetLogCard A : ENat))).trans
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
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hcondBound
  let qLen := (condK V (codedUniformOn A hA).code
    (codedUniformOn B hB).code).toNat
  have hqLenValue :
      condK V (codedUniformOn A hA).code
        (codedUniformOn B hB).code = (qLen : ENat) := by
    exact (ENat.coe_toNat hcondFinite).symm
  have hqLenBound : qLen ≤ n + epsilon + cLiteral + cDrop := by
    rw [hqLenValue] at hcondBound
    exact_mod_cast hcondBound
  obtain ⟨q, hqLength, hqProd⟩ :=
    (condKLeIff V (codedUniformOn A hA).code
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

theorem reductionSetIndexDecompressor_partrec :
    isDecompressor reductionSetIndexDecompressor := by
  have hout : Computable (fun input : BitString × BitString =>
      (canonicalPointListOfCode input.2).getD (bitsToNat input.1) []) :=
    (Primrec.list_getD ([] : BitString)).to_comp.comp
      (canonicalPointListOfCode_computable.comp Computable.snd)
      (bitsToNat_primrec.to_comp.comp Computable.fst)
  exact hout.partrec

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
    (condKLeIff V (codedUniformOn D hD).code
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
    (condKLeIff V y [] a).mp hy
  obtain ⟨q, hqLen, hqProd⟩ :=
    (condKLeIff V x y b).mp hxy
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
  obtain ⟨cLiteral, hLiteral⟩ := plainKLeLength V hV
  obtain ⟨cDrop, hDrop⟩ := condKLePlainK V hV
  let c := 4 * cPre + 4 * cLiteral + 2 * cDrop + cElem + cTwo + 10
  refine ⟨c, ?_⟩
  intro x p n epsilon B A hA hB hxlen hpTotal hpLen hxD hstatA hstatB
  let D := reductionPreimage T p B A hA
  have hD : D.Nonempty := ⟨x, hxD⟩
  have hAcomp : plainSetComplexity V A hA ≤
      plainK V x + (epsilon : ENat) := by
    exact (le_add_of_nonneg_right (zero_le (finiteSetLogCard A : ENat))).trans
      hstatA.2
  have hABBound :
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
  have hABFinite :
      condK V (codedUniformOn A hA).code
        (codedUniformOn B hB).code ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hABBound
  let q := (condK V (codedUniformOn A hA).code
    (codedUniformOn B hB).code).toNat
  have hqValue :
      condK V (codedUniformOn A hA).code
        (codedUniformOn B hB).code = (q : ENat) :=
    (ENat.coe_toNat hABFinite).symm
  have hqBound : q ≤ n + epsilon + cLiteral + cDrop := by
    rw [hqValue] at hABBound
    exact_mod_cast hABBound
  have hBcomp : plainSetComplexity V B hB ≤
      plainK V x + (epsilon : ENat) := by
    exact (le_add_of_nonneg_right (zero_le (finiteSetLogCard B : ENat))).trans
      hstatB.2
  have hBBound : plainSetComplexity V B hB ≤
      ((n + epsilon + cLiteral : Nat) : ENat) := by
    calc
      plainSetComplexity V B hB
        ≤ plainK V x + (epsilon : ENat) := hBcomp
      _ ≤ (((n : Nat) : ENat) + (cLiteral : ENat)) +
          (epsilon : ENat) := by
        gcongr
        simpa [hxlen] using hLiteral x
      _ = ((n + epsilon + cLiteral : Nat) : ENat) := by
        push_cast
        ring
  have hBFinite : plainSetComplexity V B hB ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hBBound
  let b := (plainSetComplexity V B hB).toNat
  have hbValue : plainSetComplexity V B hB = (b : ENat) :=
    (ENat.coe_toNat hBFinite).symm
  have hbBound : b ≤ n + epsilon + cLiteral := by
    rw [hbValue] at hBBound
    exact_mod_cast hBBound
  let preSlack := cPre * epsilon + logSlack cPre n
  let a := q + preSlack
  have hDB : condK V (codedUniformOn D hD).code
      (codedUniformOn B hB).code ≤ (a : ENat) := by
    have h := hPre x p n epsilon B A hA hB hD hxlen hpTotal hpLen hxD
      hstatA hstatB
    change condK V (codedUniformOn D hD).code
      (codedUniformOn B hB).code ≤ _ at h
    rw [hqValue] at h
    simpa [a, preSlack, Nat.cast_add] using h
  have hxGivenB : condK V x (codedUniformOn B hB).code ≤
      (a + finiteSetLogCard D + 2 * (Nat.bits a).length + cElem : Nat) :=
    hElem B D hB hD x a hxD hDB
  let dBound :=
    a + finiteSetLogCard D + 2 * (Nat.bits a).length + cElem
  have hxPlain : plainK V x ≤
      (b + dBound + 2 * (Nat.bits b).length + cTwo : Nat) := by
    apply hTwo x (codedUniformOn B hB).code b dBound
    · change plainSetComplexity V B hB ≤ (b : ENat)
      exact le_of_eq hbValue
    · exact hxGivenB
  let rest := dBound + 2 * (Nat.bits b).length + cTwo + epsilon
  have hcancelInput :
      (b : ENat) + (finiteSetLogCard B : ENat) ≤
        (b : ENat) + (rest : ENat) := by
    calc
      (b : ENat) + (finiteSetLogCard B : ENat)
        = plainSetComplexity V B hB +
            (finiteSetLogCard B : ENat) := by rw [hbValue]
      _ ≤ plainK V x + (epsilon : ENat) := hstatB.2
      _ ≤ ((b + dBound + 2 * (Nat.bits b).length + cTwo : Nat) : ENat) +
          (epsilon : ENat) := by
        gcongr
      _ = (b : ENat) + (rest : ENat) := by
        simp [rest]
        norm_cast
        omega
  have hlogB : (finiteSetLogCard B : ENat) ≤ (rest : ENat) :=
    (ENat.add_le_add_iff_left (ENat.coe_ne_top b)).mp hcancelInput
  let tailA := (cPre + 1) * epsilon + cPre * (Nat.bits n).length +
    cPre + cLiteral + cDrop
  have haBound : a ≤ n + tailA := by
    dsimp [a, preSlack, tailA, logSlack]
    nlinarith
  have haBits : (Nat.bits a).length ≤
      (Nat.bits n).length + tailA + 1 := by
    calc
      (Nat.bits a).length ≤ (Nat.bits (n + tailA)).length :=
        length_natBits_mono haBound
      _ ≤ (Nat.bits n).length + (Nat.bits tailA).length + 1 :=
        length_natBits_add_le n tailA
      _ ≤ (Nat.bits n).length + tailA + 1 := by
        have htail := length_natBits_le tailA
        omega
  let tailB := epsilon + cLiteral
  have hbBits : (Nat.bits b).length ≤
      (Nat.bits n).length + tailB + 1 := by
    calc
      (Nat.bits b).length ≤ (Nat.bits (n + tailB)).length := by
        apply length_natBits_mono
        dsimp [tailB]
        omega
      _ ≤ (Nat.bits n).length + (Nat.bits tailB).length + 1 :=
        length_natBits_add_le n tailB
      _ ≤ (Nat.bits n).length + tailB + 1 := by
        have htail := length_natBits_le tailB
        omega
  have hbudget : rest ≤ finiteSetLogCard D + q +
      (c * epsilon + logSlack c n) := by
    dsimp [rest, dBound, a, preSlack, tailA, tailB, c, logSlack] at *
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  calc
    (finiteSetLogCard B : ENat) ≤ (rest : ENat) := hlogB
    _ ≤ ((finiteSetLogCard D + q +
        (c * epsilon + logSlack c n) : Nat) : ENat) := by
      exact_mod_cast hbudget
    _ = (finiteSetLogCard D : ENat) +
        condK V (codedUniformOn A hA).code
          (codedUniformOn B hB).code +
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
        push_neg at h_not
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

/-- Honest S6 target for the second conclusion of `thm:step-wise`.

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

/-- The target code `[A]` belongs to the heavy-output list of `B` under `p`,
for the threshold `l` derived from `reductionPreimage_card_lower`. -/
theorem target_in_heavy_output_list
    (V T : Map) (hV : isOptimalConditional V) (hT : isDecompressor T) :
    ∃ c : Nat, ∀ (x : BitString) (n epsilon : Nat)
      (A B : Finset BitString) (hA : A.Nonempty) (hB : B.Nonempty),
      x.length = n →
      IsSufficientStatistic V x A hA epsilon →
      IsSufficientStatistic V x B hB epsilon →
      ∀ (p : BitString) (hp : IsTotalProgram T p),
      produces T p x (codedUniformOn A hA).code →
      programLength p ≤ epsilon →
      let q := (condK V (codedUniformOn A hA).code
        (codedUniformOn B hB).code).toNat
      let l := finiteSetLogCard B - q - (c * epsilon + logSlack c n)
      let ys := (canonicalFinsetList B).map (fun z => totalProgOutput T p hp z)
      (codedUniformOn A hA).code ∈ heavyOutputList ys l := by
  obtain ⟨c, hc⟩ := reductionPreimage_card_lower V hV T hT
  obtain ⟨cDrop, hDrop⟩ := condKLePlainK V hV
  obtain ⟨cLiteral, hLiteral⟩ := plainKLeLength V hV
  refine ⟨c, ?_⟩
  intro x n epsilon A B hA hB hx hS_A hS_B p hp hprod hpe
  let codeA := (codedUniformOn A hA).code
  let codeB := (codedUniformOn B hB).code
  have hqBound : condK V codeA codeB ≤
      ((codeA.length + cLiteral + cDrop : Nat) : ENat) := by
    calc
      condK V codeA codeB ≤ plainK V codeA + (cDrop : ENat) := hDrop _ _
      _ ≤ ((codeA.length : Nat) : ENat) + (cLiteral : ENat) +
          (cDrop : ENat) := by gcongr; exact hLiteral codeA
      _ = ((codeA.length + cLiteral + cDrop : Nat) : ENat) := by norm_cast
  have hqFinite : condK V codeA codeB ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hqBound
  let q := (condK V codeA codeB).toNat
  have hqValue : condK V codeA codeB = (q : ENat) :=
    (ENat.coe_toNat hqFinite).symm
  let D := reductionPreimage T p B A hA
  have hxD : x ∈ D :=
    (mem_reductionPreimage T p B A hA x).mpr ⟨hS_B.1, hprod⟩
  have hcard := hc x p n epsilon B A hA hB hx hp hpe hxD hS_A hS_B
  change (finiteSetLogCard B : ENat) ≤
    (finiteSetLogCard D : ENat) + condK V codeA codeB +
      (c * epsilon + logSlack c n : Nat) at hcard
  rw [hqValue] at hcard
  have hcardNat : finiteSetLogCard B ≤
      finiteSetLogCard D + q + (c * epsilon + logSlack c n) := by
    exact_mod_cast hcard
  let l := finiteSetLogCard B - q - (c * epsilon + logSlack c n)
  have hlD : l ≤ finiteSetLogCard D := by
    dsimp [l]
    omega
  let f : BitString → BitString := fun z => totalProgOutput T p hp z
  let ys := (canonicalFinsetList B).map f
  have hfiber : B.filter (fun z => f z = codeA) = D := by
    ext z
    rw [Finset.mem_filter, mem_reductionPreimage]
    constructor
    · rintro ⟨hzB, hfz⟩
      refine ⟨hzB, ?_⟩
      change produces T p z codeA
      rw [← hfz]
      exact totalProgOutput_produces T p hp z
    · rintro ⟨hzB, hzprod⟩
      refine ⟨hzB, ?_⟩
      exact (produces_eq_totalProgOutput hp hzprod).symm
  have hcount : ys.count codeA = D.card := by
    change ((canonicalFinsetList B).map f).count codeA = D.card
    rw [show ((canonicalFinsetList B).map f).count codeA =
        ((canonicalFinsetList B).toFinset.filter (fun z => f z = codeA)).card from
      (by
        apply list_count_map_eq_card_filter
        exact canonicalFinsetList_nodup B),
      canonicalFinsetList_toFinset, hfiber]
  dsimp only
  change codeA ∈ heavyOutputList ys l
  unfold heavyOutputList
  rw [List.mem_filter]
  constructor
  · rw [List.mem_dedup]
    apply List.mem_map.mpr
    exact ⟨x, mem_canonicalFinsetList.mpr hS_B.1,
      (produces_eq_totalProgOutput hp hprod).symm⟩
  · simp only [decide_eq_true_eq, hcount]
    by_cases hl : l = 0
    · rw [hl]
      simpa using Finset.card_pos.mpr ⟨x, hxD⟩
    · have hDcard : 1 < D.card := by
        by_contra hle
        push_neg at hle
        have hlog0 : finiteSetLogCard D = 0 := by
          apply Nat.le_zero.mp
          exact (finiteSetLogCard_le_iff D 0).mpr (hle.trans (by decide))
        omega
      have hpow := finiteSetLogCard_pred_lt D hDcard
      have hmono : 2 ^ (l - 1) ≤ 2 ^ (finiteSetLogCard D - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega

/-- The executable heavy-output list has the fixed-width bound used by the
selector program. -/
theorem heavyOutputList_length_le
    (B : Finset BitString) (f : BitString → BitString) (l : Nat) :
    (heavyOutputList ((canonicalFinsetList B).map f) l).length ≤
      2 ^ (finiteSetLogCard B - l + 1) := by
  let ys := (canonicalFinsetList B).map f
  let F := heavyOutputList ys l
  let fiber := fun y => B.filter (fun z => f z = y)
  have hcount : ∀ y, ys.count y = (fiber y).card := by
    intro y
    change ((canonicalFinsetList B).map f).count y =
      (B.filter (fun z => f z = y)).card
    rw [show ((canonicalFinsetList B).map f).count y =
        ((canonicalFinsetList B).toFinset.filter (fun z => f z = y)).card from
      (by
        apply list_count_map_eq_card_filter
        exact canonicalFinsetList_nodup B),
      canonicalFinsetList_toFinset]
  have hFnodup : F.Nodup := (List.nodup_dedup ys).filter _
  have hysset : ys.toFinset = B.image f := by
    ext y
    simp [ys]
  have hFset : F.toFinset =
      (B.image f).filter (fun y => 2 ^ (l - 1) ≤ (fiber y).card) := by
    ext y
    simp only [F, heavyOutputList, List.mem_toFinset, List.mem_filter,
      List.mem_dedup, decide_eq_true_eq, Finset.mem_filter]
    rw [hcount]
    have hymem : y ∈ ys ↔ y ∈ B.image f := by
      rw [← List.mem_toFinset, hysset]
    tauto
  let G := (B.image f).filter
    (fun y => 2 ^ (l - 1) ≤ (fiber y).card)
  have hFG : F.length = G.card := by
    rw [← List.toFinset_card_of_nodup hFnodup, hFset]
  rw [hFG]
  have h_disj : ∀ y₁ ∈ G, ∀ y₂ ∈ G, y₁ ≠ y₂ →
      Disjoint (fiber y₁) (fiber y₂) := by
    intro y₁ _ y₂ _ hneq
    simp only [fiber, Finset.disjoint_filter]
    intro z _ h1 h2
    rw [h1] at h2
    exact hneq h2
  have h_sum : ∑ y ∈ G, (fiber y).card = (G.biUnion fiber).card := by
    rw [Finset.card_biUnion h_disj]
  have h_sub : G.biUnion fiber ⊆ B := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    rcases hz with ⟨y, _, hzy⟩
    exact (Finset.mem_filter.mp hzy).1
  have h_sum_le : ∑ y ∈ G, (fiber y).card ≤ B.card := by
    rw [h_sum]
    exact Finset.card_le_card h_sub
  have h_each : ∀ y ∈ G, 2 ^ (l - 1) ≤ (fiber y).card := by
    intro y hy
    exact (Finset.mem_filter.mp hy).2
  have h_mul : G.card * 2 ^ (l - 1) ≤ ∑ y ∈ G, (fiber y).card := by
    calc
      G.card * 2 ^ (l - 1) = ∑ _y ∈ G, 2 ^ (l - 1) := by simp [mul_comm]
      _ ≤ ∑ y ∈ G, (fiber y).card :=
        Finset.sum_le_sum (fun y hy => h_each y hy)
  have h_bound : G.card * 2 ^ (l - 1) ≤ 2 ^ finiteSetLogCard B :=
    h_mul.trans (h_sum_le.trans (finiteSetLogCard_spec B))
  have hd : 2 ^ (l - 1) * G.card ≤
      2 ^ (l - 1) * 2 ^ (finiteSetLogCard B - l + 1) := by
    calc
      2 ^ (l - 1) * G.card ≤ 2 ^ finiteSetLogCard B := by
        simpa [mul_comm] using h_bound
      _ ≤ 2 ^ (l - 1 + (finiteSetLogCard B - l + 1)) := by
        apply Nat.pow_le_pow_right (by decide)
        omega
      _ = 2 ^ (l - 1) * 2 ^ (finiteSetLogCard B - l + 1) := by
        rw [Nat.pow_add]
  exact Nat.le_of_mul_le_mul_left hd (by positivity)

/-- The heavy-output filter is uniformly computable in its output list and
threshold. -/
theorem heavyOutputList_computable : Computable₂ heavyOutputList := by
  have hcount : Primrec
      (fun q : (List BitString × Nat) × BitString => q.1.1.count q.2) := by
    have hp : Primrec₂ (fun a : (List BitString × Nat) × BitString =>
        fun x : BitString => decide (x = a.2)) := by
      exact (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
        (Primrec.snd : Primrec (fun q :
          ((List BitString × Nat) × BitString) × BitString => q.2))
        (Primrec.snd.comp Primrec.fst : Primrec (fun q :
          ((List BitString × Nat) × BitString) × BitString => q.1.2)))).to₂
    convert (list_countP_primrec
      (α := (List BitString × Nat) × BitString) (β := BitString)
      (Primrec.fst.comp Primrec.fst) hp) using 1
    ext q
    simp only [List.count]
    congr 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp
  have hpow : Primrec
      (fun q : (List BitString × Nat) × BitString => 2 ^ (q.1.2 - 1)) :=
    CodedFiniteDistribution.twoPow_primrec.comp
      (Primrec.pred.comp (Primrec.snd.comp Primrec.fst))
  have hpred : Primrec₂
      (fun q : List BitString × Nat => fun y : BitString =>
        decide (2 ^ (q.2 - 1) ≤ q.1.count y)) := by
    exact (PrimrecPred.decide (Primrec.nat_le.comp hpow hcount)).to₂
  exact (list_filter_primrec
    (dedup_primrec.comp Primrec.fst) hpred).to_comp

/-- Post-processing for the selector.  The outer input is retained so that the
threshold and fixed-width index can be decoded after the total map has
finished evaluating on the condition's canonical point list. -/
def strongReductionSelectorPostFn
    (input : BitString × BitString) (ys : List BitString) : BitString :=
  let params := decodeTotalProgramPairSecond input.1
  let l := decodeBits (decodeTotalProgramPairFirst params)
  let idx := bitsToNat (decodeTotalProgramPairSecond params)
  (heavyOutputList ys l).getD idx []

theorem strongReductionSelectorPostFn_computable :
    Computable₂ strongReductionSelectorPostFn := by
  have hl : Computable
      (fun q : (BitString × BitString) × List BitString =>
        decodeBits (decodeTotalProgramPairFirst
          (decodeTotalProgramPairSecond q.1.1))) :=
    decodeBitsComputable.comp
      (decodeTotalProgramPairFirst_computable.comp
        (decodeTotalProgramPairSecond_computable.comp
          (Computable.fst.comp Computable.fst)))
  have hlist : Computable
      (fun q : (BitString × BitString) × List BitString =>
        heavyOutputList q.2
          (decodeBits (decodeTotalProgramPairFirst
            (decodeTotalProgramPairSecond q.1.1)))) :=
    heavyOutputList_computable.comp Computable.snd hl
  have hidx : Computable
      (fun q : (BitString × BitString) × List BitString =>
        bitsToNat (decodeTotalProgramPairSecond
          (decodeTotalProgramPairSecond q.1.1))) :=
    bitsToNat_primrec.to_comp.comp
      (decodeTotalProgramPairSecond_computable.comp
        (decodeTotalProgramPairSecond_computable.comp
          (Computable.fst.comp Computable.fst)))
  exact (Primrec.list_getD ([] : BitString)).to_comp.comp hlist hidx

/-- Run the encoded total program on every element of the finite set decoded
from the condition, then select a heavy output by its fixed-width ordinal. -/
noncomputable def strongReductionSelectorFn (T : Map) : Map :=
  fun input =>
    (totalProgramMapList T
      (decodeTotalProgramPairFirst input.1,
        canonicalPointListOfCode input.2)).map
      (strongReductionSelectorPostFn input)

theorem strongReductionSelectorFn_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (strongReductionSelectorFn T) := by
  have hexec : Partrec (fun input : BitString × BitString =>
      totalProgramMapList T
        (decodeTotalProgramPairFirst input.1,
          canonicalPointListOfCode input.2)) :=
    Partrec.comp (totalProgramMapList_partrec T hT)
      (decodeTotalProgramPairFirst_computable.comp Computable.fst |>.pair
        (canonicalPointListOfCode_computable.comp Computable.snd))
  exact Partrec.map hexec strongReductionSelectorPostFn_computable

theorem strongReductionSelectorFn_total
    {T : Map} {p header z : BitString} (hp : IsTotalProgram T p) :
    IsTotalProgram (strongReductionSelectorFn T)
      (totalProgramPairCode p (totalProgramPairCode header z)) := by
  intro condition
  unfold strongReductionSelectorFn
  rw [decodeTotalProgramPairFirst_pair]
  obtain ⟨ys, hys⟩ := Part.dom_iff_mem.mp
    (totalProgramMapList_dom_of_total hp
      (canonicalPointListOfCode condition))
  apply Part.dom_iff_mem.mpr
  exact ⟨strongReductionSelectorPostFn
      (totalProgramPairCode p (totalProgramPairCode header z), condition) ys,
    (Part.mem_map_iff _).2 ⟨ys, hys, rfl⟩⟩

theorem strongReductionSelectorFn_produces
    {T : Map} {p : BitString} (hp : IsTotalProgram T p)
    (B : Finset BitString) (hB : B.Nonempty) (l : Nat)
    (target : BitString)
    (hmem : target ∈ heavyOutputList
      ((canonicalFinsetList B).map (totalProgOutput T p hp)) l) :
    let F := heavyOutputList
      ((canonicalFinsetList B).map (totalProgOutput T p hp)) l
    let idx := F.findIdx (fun y => decide (y = target))
    ∀ s, idx < 2 ^ s →
      produces (strongReductionSelectorFn T)
        (totalProgramPairCode p
          (totalProgramPairCode (Nat.bits l) (chunkAddress idx s)))
        (codedUniformOn B hB).code target := by
  intro F idx s hidxPow
  obtain ⟨ys, hys⟩ := Part.dom_iff_mem.mp
    (totalProgramMapList_dom_of_total hp (canonicalFinsetList B))
  have hysEq : ys = (canonicalFinsetList B).map (totalProgOutput T p hp) :=
    totalProgramMapList_eq_map hp hys
  have hidxLen : idx < F.length := by
    dsimp [idx]
    rw [List.findIdx_lt_length]
    exact ⟨target, hmem, by simp⟩
  have hget : F.getD idx [] = target := by
    rw [List.getD_eq_getElem F [] hidxLen]
    exact of_decide_eq_true
      (List.findIdx_getElem (p := fun y => decide (y = target)) (w := hidxLen))
  unfold produces strongReductionSelectorFn
  simp only [decodeTotalProgramPairFirst_pair,
    canonicalPointListOfCode_codedUniformOn]
  apply (Part.mem_map_iff _).2
  refine ⟨ys, hys, ?_⟩
  unfold strongReductionSelectorPostFn
  simp only [decodeTotalProgramPairSecond_pair,
    decodeTotalProgramPairFirst_pair, decodeBits_natBits,
    bitsToNat_chunkAddress]
  rw [hysEq]
  exact hget

/-- The complete total reduction theorem verifying
`StrongSufficientStatisticTotalReductionStatement`. -/
theorem strongSufficientStatistic_total_reduction
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    StrongSufficientStatisticTotalReductionStatement V T := by
  obtain ⟨cHeavy, hHeavy⟩ := target_in_heavy_output_list V T hV hT.1
  obtain ⟨cSim, hSim⟩ := hT.2 (strongReductionSelectorFn T)
    (strongReductionSelectorFn_partrec T hT.1)
  obtain ⟨cLiteral, hLiteral⟩ := plainKLeLength V hV
  obtain ⟨cDrop, hDrop⟩ := condKLePlainK V hV
  let c := cHeavy + cSim + 3 * cLiteral + cDrop + 10
  refine ⟨c, ?_⟩
  intro x n epsilon A B hA hB hx hS_A hS_B hStrong
  let codeA := (codedUniformOn A hA).code
  let codeB := (codedUniformOn B hB).code
  obtain ⟨p, hp, hpLen, hpProd⟩ :=
    (totalCondK_le_iff T codeA x epsilon).mp hStrong
  change p.length ≤ epsilon at hpLen
  have hqBound : condK V codeA codeB ≤
      ((codeA.length + cLiteral + cDrop : Nat) : ENat) := by
    calc
      condK V codeA codeB ≤ plainK V codeA + (cDrop : ENat) := hDrop _ _
      _ ≤ ((codeA.length : Nat) : ENat) + (cLiteral : ENat) +
          (cDrop : ENat) := by gcongr; exact hLiteral codeA
      _ = ((codeA.length + cLiteral + cDrop : Nat) : ENat) := by norm_cast
  have hqFinite : condK V codeA codeB ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hqBound
  let q := (condK V codeA codeB).toNat
  have hqValue : condK V codeA codeB = (q : ENat) :=
    (ENat.coe_toNat hqFinite).symm
  let slack := cHeavy * epsilon + logSlack cHeavy n
  let l := finiteSetLogCard B - q - slack
  let ys := (canonicalFinsetList B).map (fun z => totalProgOutput T p hp z)
  have htarget : codeA ∈ heavyOutputList ys l := by
    exact hHeavy x n epsilon A B hA hB hx hS_A hS_B p hp hpProd hpLen
  let F := heavyOutputList ys l
  let idx := F.findIdx (fun y => decide (y = codeA))
  let s := finiteSetLogCard B - l + 1
  have hidxLen : idx < F.length := by
    dsimp [idx]
    rw [List.findIdx_lt_length]
    exact ⟨codeA, htarget, by simp⟩
  have hFLen : F.length ≤ 2 ^ s := by
    exact heavyOutputList_length_le B
      (fun z => totalProgOutput T p hp z) l
  have hidxPow : idx < 2 ^ s := hidxLen.trans_le hFLen
  let z := chunkAddress idx s
  have hzLen : z.length = s := chunkAddress_length idx s hidxPow
  let header := Nat.bits l
  let inner := totalProgramPairCode header z
  let r := totalProgramPairCode p inner
  have hrTotal : IsTotalProgram (strongReductionSelectorFn T) r := by
    exact strongReductionSelectorFn_total hp
  have hrProd : produces (strongReductionSelectorFn T) r codeB codeA := by
    exact strongReductionSelectorFn_produces hp B hB l codeA htarget s hidxPow
  have hlogBENat : (finiteSetLogCard B : ENat) ≤
      ((n + epsilon + cLiteral : Nat) : ENat) := by
    calc
      (finiteSetLogCard B : ENat) ≤
          plainSetComplexity V B hB + (finiteSetLogCard B : ENat) :=
        le_add_of_nonneg_left (zero_le _)
      _ ≤ plainK V x + (epsilon : ENat) := hS_B.2
      _ ≤ ((n : Nat) : ENat) + (cLiteral : ENat) + (epsilon : ENat) := by
        gcongr
        simpa [hx] using hLiteral x
      _ = ((n + epsilon + cLiteral : Nat) : ENat) := by
        norm_cast
        omega
  have hlogB : finiteSetLogCard B ≤ n + epsilon + cLiteral := by
    exact_mod_cast hlogBENat
  have hlBound : l ≤ n + epsilon + cLiteral :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hlogB)
  have hbitsL : (Nat.bits l).length ≤
      (Nat.bits n).length + epsilon + cLiteral + 1 := by
    calc
      (Nat.bits l).length ≤ (Nat.bits (n + epsilon + cLiteral)).length :=
        length_natBits_mono hlBound
      _ = (Nat.bits (n + (epsilon + cLiteral))).length := by
        congr 2
        omega
      _ ≤ (Nat.bits n).length + (Nat.bits (epsilon + cLiteral)).length + 1 :=
        length_natBits_add_le n (epsilon + cLiteral)
      _ ≤ (Nat.bits n).length + epsilon + cLiteral + 1 := by
        have htail := length_natBits_le (epsilon + cLiteral)
        omega
  have hbitsBitsL : (Nat.bits (Nat.bits l).length).length ≤
      (Nat.bits l).length := length_natBits_le _
  have hpBits : (Nat.bits p.length).length ≤ (Nat.bits epsilon).length :=
    length_natBits_mono hpLen
  have hepsilonBits : (Nat.bits epsilon).length ≤ epsilon :=
    length_natBits_le epsilon
  have hs : s ≤ q + slack + 1 := by
    dsimp [s, l]
    omega
  have hrLen : r.length = p.length +
      ((Nat.bits l).length + s +
        2 * (Nat.bits (Nat.bits l).length).length + 1) +
      2 * (Nat.bits p.length).length + 1 := by
    dsimp [r, inner, header]
    rw [length_totalProgramPairCode, length_totalProgramPairCode, hzLen]
  have hrCrude : r.length + cSim ≤
      q + slack + 6 * epsilon + 3 * (Nat.bits n).length +
        3 * cLiteral + 6 + cSim := by
    rw [hrLen]
    omega
  have hAbsorb : slack + 6 * epsilon + 3 * (Nat.bits n).length +
      3 * cLiteral + 6 + cSim ≤ c * epsilon + logSlack c n := by
    dsimp [c, slack]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  have hframe : r.length + cSim ≤ q + c * epsilon + logSlack c n := by
    calc
      r.length + cSim ≤ q +
          (slack + 6 * epsilon + 3 * (Nat.bits n).length +
            3 * cLiteral + 6 + cSim) := by
        omega
      _ ≤ q + (c * epsilon + logSlack c n) := Nat.add_le_add_left hAbsorb q
      _ = q + c * epsilon + logSlack c n := by omega
  calc
    totalCondK T codeA codeB ≤
        totalCondK (strongReductionSelectorFn T) codeA codeB +
          (cSim : ENat) := hSim _ _
    _ ≤ (r.length : ENat) + (cSim : ENat) := by
      gcongr
      exact totalCondK_le_programLength hrTotal hrProd
    _ ≤ ((q + c * epsilon + logSlack c n : Nat) : ENat) := by
      exact_mod_cast hframe
    _ = (q : ENat) + (c * epsilon + logSlack c n : Nat) := by
      rw [show q + c * epsilon + logSlack c n =
        q + (c * epsilon + logSlack c n) by omega, ENat.coe_add]
    _ = condK V codeA codeB +
        (c * epsilon + logSlack c n : Nat) := by rw [hqValue]

private lemma stepWise_total_linear_arith
    (cRed cPlain epsilon : Nat) (delta : ENat) :
    (cPlain : ENat) * delta + (cRed : ENat) * epsilon ≤
      ((cRed + cPlain : Nat) : ENat) * ((epsilon : ENat) + delta) := by
  rw [Nat.cast_add, add_mul, mul_add, mul_add]
  rw [add_comm (↑cPlain * delta) (↑cRed * ↑epsilon)]
  -- RHS is a + c + (d + b), want (a + b) + (c + d)
  have h : (↑cRed : ENat) * ↑epsilon + ↑cRed * delta + (↑cPlain * ↑epsilon + ↑cPlain * delta) =
           (↑cRed * ↑epsilon + ↑cPlain * delta) + (↑cRed * delta + ↑cPlain * ↑epsilon) := by
    ac_rfl
  rw [h]
  apply le_add_of_nonneg_right
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le _))
    (mul_nonneg (Nat.cast_nonneg _) (zero_le _))

private lemma stepWise_logSlack_add
    (cRed cPlain n : Nat) :
    (logSlack cPlain n : ENat) + (logSlack cRed n : ENat) =
      (logSlack (cRed + cPlain) n : ENat) := by
  simp [logSlack]
  ring

private lemma stepWise_total_slack_rearrange
    (cRed cPlain epsilon n : Nat) (delta : ENat) :
    (cPlain * delta + logSlack cPlain n : ENat) +
        (cRed * epsilon + logSlack cRed n : Nat) =
      ((cPlain : ENat) * delta + (cRed : ENat) * epsilon) +
        ((logSlack cPlain n : ENat) + (logSlack cRed n : ENat)) := by
  simp [add_assoc, add_comm, add_left_comm]

private lemma stepWise_total_slack_arith
    (cRed cPlain epsilon n : Nat) (delta : ENat) :
    (cPlain * delta + logSlack cPlain n : ENat) +
        (cRed * epsilon + logSlack cRed n : Nat) ≤
      ((cRed + cPlain : Nat) : ENat) * ((epsilon : ENat) + delta) +
        (logSlack (cRed + cPlain) n : ENat) := by
  rw [stepWise_total_slack_rearrange, stepWise_logSlack_add]
  gcongr
  exact stepWise_total_linear_arith cRed cPlain epsilon delta

/-- Combining the strong sufficient-statistic reduction with an ordinary
conditional bound yields the total conditional conclusion of the step-wise
theorem, with a uniformly enlarged slack constant. -/
theorem stepWise_total_conclusion_of_plain
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∀ cPlain, ∃ cTotal, ∀ x n A (hA : A.Nonempty)
        B (hB : B.Nonempty) epsilon delta,
      x.length = n →
      IsSufficientStatistic V x A hA epsilon →
      IsSufficientStatistic V x B hB epsilon →
      IsStrongSetModel T x A hA epsilon →
      condK V (codedUniformOn A hA).code
          (codedUniformOn B hB).code ≤
        (cPlain * delta + logSlack cPlain n : ENat) →
      totalCondK T (codedUniformOn A hA).code
          (codedUniformOn B hB).code ≤
        (cTotal * (epsilon + delta) +
          logSlack cTotal n : ENat) := by
  intro cPlain
  obtain ⟨c, hc⟩ := strongSufficientStatistic_total_reduction V T hV hT
  refine ⟨c + cPlain, ?_⟩
  intro x n A hA B hB epsilon delta hxlen hSuff_A hSuff_B hStrong hBound
  have h1 := hc x n epsilon A B hA hB hxlen hSuff_A hSuff_B hStrong
  calc totalCondK T (codedUniformOn A hA).code (codedUniformOn B hB).code
      ≤ condK V (codedUniformOn A hA).code (codedUniformOn B hB).code +
          (c * epsilon + logSlack c n : Nat) := h1
    _ ≤ (cPlain * delta + logSlack cPlain n : ENat) +
          (c * epsilon + logSlack c n : Nat) := by gcongr
    _ ≤ ((c + cPlain : Nat) : ENat) * ((epsilon : ENat) + delta) +
          (logSlack (c + cPlain) n : ENat) := stepWise_total_slack_arith c cPlain epsilon n delta

/-- The step-wise theorem follows from its ordinary conditional-complexity half
and the proved total reduction for strong sufficient statistics. -/
theorem thmStepWise_of_plain
    (V T : Map)
    (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T)
    (hPlain :
      ∃ cKappa cPlain : Nat,
        ∀ x n A (hA : A.Nonempty) B (hB : B.Nonempty)
            epsilon delta,
          x.length = n →
          IsSufficientStatistic V x A hA epsilon →
          IsSufficientStatistic V x B hB epsilon →
          IsMinimalModel V x A hA delta
            (epsilon + logSlack cKappa n) →
          condK V (codedUniformOn A hA).code
              (codedUniformOn B hB).code ≤
            (cPlain * delta + logSlack cPlain n : ENat)) :
    ThmStepWiseStatement V T := by
  obtain ⟨cKappa, cPlain, hPlain⟩ := hPlain
  obtain ⟨cTotal, hTotal⟩ :=
    stepWise_total_conclusion_of_plain V T hV hT cPlain
  refine ⟨cKappa, cPlain, cTotal, ?_⟩
  intro x n A hA B hB epsilon delta hx hAstat hBstat hMinimal
  have hCond := hPlain x n A hA B hB epsilon delta
    hx hAstat hBstat hMinimal
  refine ⟨hCond, ?_⟩
  intro hStrong
  exact hTotal x n A hA B hB epsilon delta hx hAstat hBstat hStrong hCond

end Kolmogorov
