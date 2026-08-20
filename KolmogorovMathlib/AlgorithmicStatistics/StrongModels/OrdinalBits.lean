import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaCount
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting

/-!
# Ordinal bits and total-equivalence of strong models

This module formalizes the total equivalence between an $\epsilon$-strong model $A$
for $x$ and the pair $(A, u)$, where $u$ is the ordinal number of $x$ in the
canonical enumeration of $A$. It also provides the fixed-width primitive
`strongModelOrdinalBits` which encodes $u$ in exactly $\log |A|$ bits.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- The ordinal number of `x` in the canonical enumeration of `A`. -/
def strongModelOrdinal (A : Finset BitString) (x : BitString) : Nat :=
  (canonicalFinsetList A).findIdx (fun w => decide (w = x))

theorem strongModelOrdinal_lt_card
    (A : Finset BitString) (x : BitString)
    (hx : x ∈ A) :
    strongModelOrdinal A x < A.card := by
  unfold strongModelOrdinal
  have H : x ∈ canonicalFinsetList A := mem_canonicalFinsetList.mpr hx
  have hlt :
      (canonicalFinsetList A).findIdx (fun w => decide (w = x)) <
        (canonicalFinsetList A).length := by
    rw [List.findIdx_lt_length]
    exact ⟨x, H, by simp⟩
  rw [length_canonicalFinsetList] at hlt
  exact hlt

/-- The pair `(A, u)`: the canonical model code of `A` together with the
ordinal number of `x` in `A`, encoded self-delimitingly. -/
noncomputable def strongModelOrdinalPair
    (A : Finset BitString) (hA : A.Nonempty) (x : BitString) : BitString :=
  pairCode (codedUniformOn A hA).code (natCode (strongModelOrdinal A x))

/-- The canonical enumeration recovers a member from its own ordinal. -/
theorem getD_findIdx_decide_self
    (l : List BitString) (x : BitString) (hx : x ∈ l) :
    l.getD (l.findIdx (fun w => decide (w = x))) [] = x := by
  have hlt : l.findIdx (fun w => decide (w = x)) < l.length := by
    rw [List.findIdx_lt_length]
    exact ⟨x, hx, by simp⟩
  rw [List.getD_eq_getElem l [] hlt]
  exact of_decide_eq_true
    (List.findIdx_getElem (p := fun w => decide (w = x)) (w := hlt))

/-! ### Direction 1: `KT(x | A,u) = O(1)` -/

/-- On a condition `pairCode [A] (natCode u)`, return the `u`-th element of the
canonical enumeration of `A`.  This is a total computable map, independent of
the (ignored) program. -/
noncomputable def indexedElementDecompressor : Map :=
  fun input =>
    Part.some
      ((canonicalPointListOfCode (decodeFirst input.2)).getD
        (decodeNatCode (decodeSecond input.2)) [])

theorem indexedElementDecompressor_partrec :
    isDecompressor indexedElementDecompressor := by
  have hlist : Computable (fun input : BitString × BitString =>
      canonicalPointListOfCode (decodeFirst input.2)) :=
    canonicalPointListOfCode_computable.comp
      (decodeFirst_computable.comp Computable.snd)
  have hidx : Computable (fun input : BitString × BitString =>
      decodeNatCode (decodeSecond input.2)) :=
    decodeNatCode_primrec.to_comp.comp
      (decodeSecond_computable.comp Computable.snd)
  exact (((Primrec.list_getD ([] : BitString)).to_comp).comp hlist hidx)

theorem indexedElementDecompressor_total (q : BitString) :
    IsTotalProgram indexedElementDecompressor q :=
  fun _ => trivial

theorem indexedElementDecompressor_produces
    (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (hx : x ∈ A) :
    produces indexedElementDecompressor []
      (strongModelOrdinalPair A hA x) x := by
  unfold produces indexedElementDecompressor strongModelOrdinalPair strongModelOrdinal
  simp only [decodeFirst_pairCode, decodeSecond_pairCode,
    canonicalPointListOfCode_codedUniformOn, decodeNatCode_natCode,
    Part.mem_some_iff]
  exact (getD_findIdx_decide_self (canonicalFinsetList A) x
    (mem_canonicalFinsetList.mpr hx)).symm

/-! ### Direction 2: `KT(A,u | x) ≤ ε + O(1)` -/

/-- Post-processing: from a produced set-code `c` and the context `x'`, form the
pair of `c` with the ordinal of `x'` in the set decoded from `c`. -/
noncomputable def ordinalPairPostFn
    (input : BitString × BitString) (c : BitString) : BitString :=
  pairCode c
    (natCode ((canonicalPointListOfCode c).findIdx (fun w => decide (w = input.2))))

theorem ordinalPairPostFn_computable : Computable₂ ordinalPairPostFn := by
  have hfindidx : Primrec (fun q : (BitString × BitString) × BitString =>
      (canonicalPointListOfCode q.2).findIdx (fun w => decide (w = q.1.2))) :=
    Primrec.list_findIdx
      (canonicalPointListOfCode_primrec.comp Primrec.snd)
      ((Primrec.eq.decide.comp Primrec.snd
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).to₂)
  have h : Primrec (fun q : (BitString × BitString) × BitString =>
      pairCode q.2
        (natCode ((canonicalPointListOfCode q.2).findIdx
          (fun w => decide (w = q.1.2))))) :=
    CodedFiniteDistribution.pairCode_primrec.comp Primrec.snd
      (CodedFiniteDistribution.natCode_primrec.comp hfindidx)
  exact h.to_comp

/-- On a program `p` (the strong program) and context `x'`, run `p` to obtain a
set-code and pair it with the ordinal of `x'` in that set. -/
noncomputable def pairWithOrdinalDecompressor (T : Map) : Map :=
  fun input => (T input).map (ordinalPairPostFn input)

theorem pairWithOrdinalDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (pairWithOrdinalDecompressor T) :=
  Partrec.map hT ordinalPairPostFn_computable

theorem pairWithOrdinalDecompressor_total
    {T : Map} {p : BitString} (hp : IsTotalProgram T p) :
    IsTotalProgram (pairWithOrdinalDecompressor T) p := by
  intro y
  unfold pairWithOrdinalDecompressor
  rw [Part.dom_iff_mem]
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp (hp y)
  exact ⟨_, (Part.mem_map_iff _).2 ⟨v, hv, rfl⟩⟩

theorem pairWithOrdinalDecompressor_produces
    {T : Map} {p : BitString} {A : Finset BitString} {hA : A.Nonempty}
    {x : BitString}
    (hpx : produces T p x (codedUniformOn A hA).code) :
    produces (pairWithOrdinalDecompressor T) p x
      (strongModelOrdinalPair A hA x) := by
  unfold produces pairWithOrdinalDecompressor strongModelOrdinalPair
    strongModelOrdinal
  rw [Part.mem_map_iff]
  refine ⟨(codedUniformOn A hA).code, hpx, ?_⟩
  unfold ordinalPairPostFn
  rw [canonicalPointListOfCode_codedUniformOn]

/-! ### The unary ordinal equivalence -/

/-- **Properties of strong models, opening claim.**  If `A` is an `ε`-strong
model for `x` (with `x ∈ A`), then `x` is total-`(ε + O(1))`-equivalent to the
pair `(A, u)`, where `u` is the ordinal number of `x` in `A`.  The additive
constant is uniform in `x`, `A`, and `ε`. -/
theorem strong_model_equivalent_ordinal_pair
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (x : BitString) (A : Finset BitString) (hA : A.Nonempty)
      (epsilon : Nat),
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      TotalEquivalentWithin T x (strongModelOrdinalPair A hA x)
        (epsilon + c) := by
  obtain ⟨c₁, hc₁⟩ :=
    hT.2 indexedElementDecompressor indexedElementDecompressor_partrec
  obtain ⟨c₂, hc₂⟩ :=
    hT.2 (pairWithOrdinalDecompressor T)
      (pairWithOrdinalDecompressor_partrec T hT.1)
  refine ⟨c₁ + c₂, ?_⟩
  intro x A hA epsilon hx hstrong
  refine ⟨?_, ?_⟩
  · have hprod := indexedElementDecompressor_produces A hA x hx
    have htot := indexedElementDecompressor_total ([] : BitString)
    calc
      totalCondK T x (strongModelOrdinalPair A hA x)
          ≤ totalCondK indexedElementDecompressor x
              (strongModelOrdinalPair A hA x) + (c₁ : ENat) :=
            hc₁ x (strongModelOrdinalPair A hA x)
      _ ≤ (programLength ([] : BitString) : ENat) + (c₁ : ENat) := by
            gcongr
            exact totalCondK_le_programLength htot hprod
      _ = (c₁ : ENat) := by simp [programLength]
      _ ≤ ((epsilon + (c₁ + c₂) : Nat) : ENat) := by
            exact_mod_cast (by omega : c₁ ≤ epsilon + (c₁ + c₂))
  · obtain ⟨p, hptot, hplen, hpx⟩ :=
      (totalCondK_le_iff T (codedUniformOn A hA).code x epsilon).mp hstrong
    have hprod := pairWithOrdinalDecompressor_produces (hA := hA) hpx
    have htot := pairWithOrdinalDecompressor_total hptot
    calc
      totalCondK T (strongModelOrdinalPair A hA x) x
          ≤ totalCondK (pairWithOrdinalDecompressor T)
              (strongModelOrdinalPair A hA x) x + (c₂ : ENat) :=
            hc₂ (strongModelOrdinalPair A hA x) x
      _ ≤ (epsilon : ENat) + (c₂ : ENat) := by
            gcongr
            exact (totalCondK_le_programLength htot hprod).trans
              (by exact_mod_cast hplen)
      _ ≤ ((epsilon + (c₁ + c₂) : Nat) : ENat) := by
            exact_mod_cast (by omega : epsilon + c₂ ≤ epsilon + (c₁ + c₂))

/-! ### New Primitives (Fixed-width) -/

def strongModelOrdinalBits
    (A : Finset BitString) (x : BitString) : BitString :=
  chunkAddress (strongModelOrdinal A x) (finiteSetLogCard A)

noncomputable def strongModelOrdinalBitsPair
    (A : Finset BitString) (hA : A.Nonempty) (x : BitString) : BitString :=
  pairCode (codedUniformOn A hA).code (strongModelOrdinalBits A x)

theorem finiteSetLogCard_eq_bits_card_pred
    (A : Finset BitString) (hA : A.Nonempty) :
    finiteSetLogCard A = (Nat.bits (A.card - 1)).length := by
  rw [Nat.size_eq_bits_len]
  apply eq_of_forall_ge_iff
  intro j
  rw [finiteSetLogCard_le_iff, Nat.size_le]
  have hcard : 0 < A.card := hA.card_pos
  have hpow : 0 < 2 ^ j := pow_pos (by decide) j
  omega

theorem strongModelOrdinal_lt_two_pow_logCard
    (A : Finset BitString) (x : BitString) (hx : x ∈ A) :
    strongModelOrdinal A x < 2 ^ finiteSetLogCard A := by
  exact (strongModelOrdinal_lt_card A x hx).trans_le
    (finiteSetLogCard_spec A)

theorem strongModelOrdinalBits_length
    (A : Finset BitString) (x : BitString) (hx : x ∈ A) :
    (strongModelOrdinalBits A x).length = finiteSetLogCard A := by
  exact chunkAddress_length _ _
    (strongModelOrdinal_lt_two_pow_logCard A x hx)

@[simp] theorem bitsToNat_strongModelOrdinalBits
    (A : Finset BitString) (x : BitString) :
    bitsToNat (strongModelOrdinalBits A x) = strongModelOrdinal A x := by
  exact bitsToNat_chunkAddress _ _

/-- Width determined from the decoded canonical support.  The predecessor
formula is executable even for malformed codes and agrees with
`finiteSetLogCard` on every nonempty canonical finite-set code. -/
noncomputable def ordinalWidthOfCode (c : BitString) : Nat :=
  (Nat.bits ((canonicalPointListOfCode c).length - 1)).length

theorem ordinalWidthOfCode_codedUniformOn (A : Finset BitString) (hA : A.Nonempty) :
  ordinalWidthOfCode (codedUniformOn A hA).code = finiteSetLogCard A := by
  unfold ordinalWidthOfCode
  rw [canonicalPointListOfCode_codedUniformOn, length_canonicalFinsetList]
  exact (finiteSetLogCard_eq_bits_card_pred A hA).symm

noncomputable def fixedOrdinalElementDecompressor : Map :=
  fun input =>
    Part.some
      ((canonicalPointListOfCode (decodeFirst input.2)).getD
        (bitsToNat (decodeSecond input.2)) [])

theorem fixedOrdinalElementDecompressor_partrec :
    isDecompressor fixedOrdinalElementDecompressor := by
  have hlist : Computable (fun input : BitString × BitString =>
      canonicalPointListOfCode (decodeFirst input.2)) :=
    canonicalPointListOfCode_computable.comp
      (decodeFirst_computable.comp Computable.snd)
  have hidx : Computable (fun input : BitString × BitString =>
      bitsToNat (decodeSecond input.2)) :=
    bitsToNat_primrec.to_comp.comp
      (decodeSecond_computable.comp Computable.snd)
  exact (((Primrec.list_getD ([] : BitString)).to_comp).comp hlist hidx)

theorem fixedOrdinalElementDecompressor_total (q : BitString) :
    IsTotalProgram fixedOrdinalElementDecompressor q :=
  fun _ => trivial

theorem fixedOrdinalElementDecompressor_produces
    (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (hx : x ∈ A) :
    produces fixedOrdinalElementDecompressor []
      (strongModelOrdinalBitsPair A hA x) x := by
  unfold produces fixedOrdinalElementDecompressor strongModelOrdinalBitsPair
  simp only [decodeFirst_pairCode, decodeSecond_pairCode,
    canonicalPointListOfCode_codedUniformOn,
    bitsToNat_strongModelOrdinalBits, Part.mem_some_iff]
  exact (getD_findIdx_decide_self (canonicalFinsetList A) x
    (mem_canonicalFinsetList.mpr hx)).symm

noncomputable def ordinalBitsPairPostFn
    (input : BitString × BitString) (c : BitString) : BitString :=
  pairCode c
    (chunkAddress ((canonicalPointListOfCode c).findIdx (fun w => decide (w = input.2)))
      (ordinalWidthOfCode c))

theorem ordinalBitsPairPostFn_computable : Computable₂ ordinalBitsPairPostFn := by
  have hfindidx : Primrec (fun q : (BitString × BitString) × BitString =>
      (canonicalPointListOfCode q.2).findIdx (fun w => decide (w = q.1.2))) :=
    Primrec.list_findIdx
      (canonicalPointListOfCode_primrec.comp Primrec.snd)
      ((Primrec.eq.decide.comp Primrec.snd
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).to₂)
  have hwidth : Primrec (fun q : (BitString × BitString) × BitString =>
      ordinalWidthOfCode q.2) := by
    unfold ordinalWidthOfCode
    exact Primrec.list_length.comp
      (primrecNatBits.comp
        (Primrec.pred.comp
          (Primrec.list_length.comp
            (canonicalPointListOfCode_primrec.comp Primrec.snd))))
  have hchunk : Primrec (fun q : (BitString × BitString) × BitString =>
      chunkAddress
        ((canonicalPointListOfCode q.2).findIdx (fun w => decide (w = q.1.2)))
        (ordinalWidthOfCode q.2)) :=
    chunkAddress_primrec.comp hfindidx hwidth
  exact (CodedFiniteDistribution.pairCode_primrec.comp Primrec.snd hchunk).to_comp

noncomputable def pairWithOrdinalBitsDecompressor (T : Map) : Map :=
  fun input => (T input).map (ordinalBitsPairPostFn input)

theorem pairWithOrdinalBitsDecompressor_partrec
    (T : Map) (hT : isDecompressor T) :
    isDecompressor (pairWithOrdinalBitsDecompressor T) := by
  exact Partrec.map hT ordinalBitsPairPostFn_computable

theorem pairWithOrdinalBitsDecompressor_total
    {T : Map} {p : BitString} (hp : IsTotalProgram T p) :
    IsTotalProgram (pairWithOrdinalBitsDecompressor T) p := by
  intro y
  unfold pairWithOrdinalBitsDecompressor
  rw [Part.dom_iff_mem]
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp (hp y)
  exact ⟨_, (Part.mem_map_iff _).2 ⟨v, hv, rfl⟩⟩

theorem pairWithOrdinalBitsDecompressor_produces
    {T : Map} {p : BitString} {A : Finset BitString} {hA : A.Nonempty}
    {x : BitString}
    (hpx : produces T p x (codedUniformOn A hA).code) :
    produces (pairWithOrdinalBitsDecompressor T) p x
      (strongModelOrdinalBitsPair A hA x) := by
  unfold produces pairWithOrdinalBitsDecompressor strongModelOrdinalBitsPair
  rw [Part.mem_map_iff]
  refine ⟨(codedUniformOn A hA).code, hpx, ?_⟩
  unfold ordinalBitsPairPostFn strongModelOrdinalBits strongModelOrdinal
  rw [canonicalPointListOfCode_codedUniformOn,
    ordinalWidthOfCode_codedUniformOn]

theorem strong_model_equivalent_fixed_ordinal_pair
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x A (hA : A.Nonempty) epsilon,
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      TotalEquivalentWithin T x
        (strongModelOrdinalBitsPair A hA x) (epsilon + c) := by
  obtain ⟨c₁, hc₁⟩ :=
    hT.2 fixedOrdinalElementDecompressor
      fixedOrdinalElementDecompressor_partrec
  obtain ⟨c₂, hc₂⟩ :=
    hT.2 (pairWithOrdinalBitsDecompressor T)
      (pairWithOrdinalBitsDecompressor_partrec T hT.1)
  refine ⟨c₁ + c₂, ?_⟩
  intro x A hA epsilon hx hstrong
  refine ⟨?_, ?_⟩
  · have hprod := fixedOrdinalElementDecompressor_produces A hA x hx
    have htot := fixedOrdinalElementDecompressor_total ([] : BitString)
    calc
      totalCondK T x (strongModelOrdinalBitsPair A hA x)
          ≤ totalCondK fixedOrdinalElementDecompressor x
              (strongModelOrdinalBitsPair A hA x) + (c₁ : ENat) :=
            hc₁ x (strongModelOrdinalBitsPair A hA x)
      _ ≤ (programLength ([] : BitString) : ENat) + (c₁ : ENat) := by
            gcongr
            exact totalCondK_le_programLength htot hprod
      _ = (c₁ : ENat) := by simp [programLength]
      _ ≤ ((epsilon + (c₁ + c₂) : Nat) : ENat) := by
            exact_mod_cast (by omega : c₁ ≤ epsilon + (c₁ + c₂))
  · obtain ⟨p, hptot, hplen, hpx⟩ :=
      (totalCondK_le_iff T (codedUniformOn A hA).code x epsilon).mp hstrong
    have hprod := pairWithOrdinalBitsDecompressor_produces (hA := hA) hpx
    have htot := pairWithOrdinalBitsDecompressor_total hptot
    calc
      totalCondK T (strongModelOrdinalBitsPair A hA x) x
          ≤ totalCondK (pairWithOrdinalBitsDecompressor T)
              (strongModelOrdinalBitsPair A hA x) x + (c₂ : ENat) :=
            hc₂ (strongModelOrdinalBitsPair A hA x) x
      _ ≤ (epsilon : ENat) + (c₂ : ENat) := by
            gcongr
            exact (totalCondK_le_programLength htot hprod).trans
              (by exact_mod_cast hplen)
      _ ≤ ((epsilon + (c₁ + c₂) : Nat) : ENat) := by
            exact_mod_cast (by omega : epsilon + c₂ ≤ epsilon + (c₁ + c₂))

/-! ### Conditional randomness of the fixed-width ordinal -/

/-- A uniform-model deficiency bound forces the ceiling log-cardinality below
the conditional prefix complexity of the member plus the deficiency budget. -/
theorem finiteSetLogCard_le_condKP_add_of_deficiency
    {U : Map} {A : Finset BitString} {hA : A.Nonempty}
    {x : BitString} {epsilon : Nat}
    (hx : x ∈ A)
    (hdef : CodedFiniteDistribution.DeficiencyLe U
      (codedUniformOn A hA) x epsilon) :
    (finiteSetLogCard A : ENat) ≤
      KP U x (codedUniformOn A hA).code + (epsilon : ENat) := by
  obtain ⟨j, hcard, hj⟩ := card_le_of_deficiency hx hdef
  have hlog : finiteSetLogCard A ≤ j :=
    (finiteSetLogCard_le_iff A j).mpr hcard
  exact (by exact_mod_cast hlog : (finiteSetLogCard A : ENat) ≤ (j : ENat)).trans hj

/-- Recover the member selected by fixed-width ordinal bits from a canonical
finite-set model code.  `getD` makes this a total function on malformed codes
and out-of-range ordinals as well. -/
noncomputable def ordinalBitsElementFn
    (modelCode ordinalBits : BitString) : BitString :=
  (canonicalPointListOfCode modelCode).getD
    (bitsToNat ordinalBits) []

theorem ordinalBitsElementFn_computable :
    Computable (fun p : BitString × BitString =>
      ordinalBitsElementFn p.1 p.2) := by
  unfold ordinalBitsElementFn
  exact ((Primrec.list_getD ([] : BitString)).to_comp).comp
    (canonicalPointListOfCode_computable.comp Computable.fst)
    (bitsToNat_primrec.to_comp.comp Computable.snd)

theorem ordinalBitsElementFn_eval
    (A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) (hx : x ∈ A) :
    ordinalBitsElementFn (codedUniformOn A hA).code
      (strongModelOrdinalBits A x) = x := by
  unfold ordinalBitsElementFn
  rw [canonicalPointListOfCode_codedUniformOn,
    bitsToNat_strongModelOrdinalBits]
  exact getD_findIdx_decide_self (canonicalFinsetList A) x
    (mem_canonicalFinsetList.mpr hx)

/-- Conditional prefix complexity cannot increase by more than a uniform
constant when the model code and ordinal bits are postprocessed to recover the
member. -/
theorem KP_member_le_KP_ordinalBits_given_modelCode
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ A (hA : A.Nonempty) x,
      x ∈ A →
      KP U x (codedUniformOn A hA).code ≤
        KP U (strongModelOrdinalBits A x)
          (codedUniformOn A hA).code + (c : ENat) := by
  obtain ⟨c, hc⟩ := KP_cond_first_map_le U hU ordinalBitsElementFn
    ordinalBitsElementFn_computable
  refine ⟨c, ?_⟩
  intro A hA x hx
  simpa [ordinalBitsElementFn_eval A hA x hx] using
    hc (strongModelOrdinalBits A x) (codedUniformOn A hA).code

/-- The fixed-width ordinal of a low-deficiency member is conditionally random
given the canonical model code, up to the original deficiency and one uniform
machine constant. -/
theorem strongModelOrdinalBits_random_given_model
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ A (hA : A.Nonempty) x epsilon,
      x ∈ A →
      CodedFiniteDistribution.DeficiencyLe U
        (codedUniformOn A hA) x epsilon →
      (finiteSetLogCard A : ENat) ≤
        KP U (strongModelOrdinalBits A x)
          (codedUniformOn A hA).code +
        (epsilon + c : Nat) := by
  obtain ⟨c, hc⟩ := KP_member_le_KP_ordinalBits_given_modelCode U hU
  refine ⟨c, ?_⟩
  intro A hA x epsilon hx hdef
  calc
    (finiteSetLogCard A : ENat)
        ≤ KP U x (codedUniformOn A hA).code + (epsilon : ENat) :=
          finiteSetLogCard_le_condKP_add_of_deficiency hx hdef
    _ ≤ (KP U (strongModelOrdinalBits A x) (codedUniformOn A hA).code +
          (c : ENat)) + (epsilon : ENat) := by
          gcongr
          exact hc A hA x hx
    _ = KP U (strongModelOrdinalBits A x) (codedUniformOn A hA).code +
          (epsilon + c : Nat) := by
          rw [Nat.cast_add]
          ac_rfl

end Kolmogorov
