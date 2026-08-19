import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseTruncation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongSufficientStatistic

/-!
# Fibre stratification for the add-noise reverse direction

The ordinary first-coordinate truncation can be much larger than the target
size when the fibres of a pair model are unbalanced.  This file isolates the
finite-set part of the required repair: retain only first coordinates whose
fibres have logarithmic cardinality at least a chosen threshold.  The generic
heavy-output count from `StrongSufficientStatistic.lean` then gives the desired
size reduction, with the one-bit loss caused by `finiteSetLogCard` rounding.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The fibre of a finite pair model over a first coordinate. -/
def finiteSetFstFiber (B : Finset BitString) (x : BitString) :
    Finset BitString :=
  B.filter (fun z => decodeFirst z = x)

/-- The executable rounded heavy truncation.  The threshold `2^(l-1)` includes
every first coordinate whose fibre has logarithmic cardinality at least `l`;
the one-bit rounding is exactly the loss in the counting theorem. -/
def finiteSetFstHeavyTruncation (B : Finset BitString) (l : Nat) :
    Finset BitString :=
  (heavyOutputList ((canonicalFinsetList B).map decodeFirst) l).toFinset

/-- A nonempty set whose log-cardinality is at least `l` meets the rounded
`2^(l-1)` threshold. -/
theorem pow_pred_le_card_of_le_finiteSetLogCard
    {S : Finset BitString} {l : Nat} (hS : S.Nonempty)
    (hlog : l ≤ finiteSetLogCard S) :
    2 ^ (l - 1) ≤ S.card := by
  by_cases hl : l = 0
  · subst l
    simpa using hS.card_pos
  · have hlt : l - 1 < finiteSetLogCard S := by omega
    unfold finiteSetLogCard at hlt
    exact Nat.le_of_lt ((Nat.lt_clog_iff_pow_lt (by norm_num)).mp hlt)

/-- A represented first coordinate belongs to the heavy truncation whenever
its actual fibre meets the threshold. -/
theorem finiteSetFstHeavyTruncation_mem
    {B : Finset BitString} {x y : BitString} {l : Nat}
    (hxy : pairCode x y ∈ B)
    (hheavy : l ≤ finiteSetLogCard (finiteSetFstFiber B x)) :
    x ∈ finiteSetFstHeavyTruncation B l := by
  have hfiber : (finiteSetFstFiber B x).Nonempty := by
    refine ⟨pairCode x y, ?_⟩
    rw [finiteSetFstFiber, Finset.mem_filter]
    exact ⟨hxy, decodeFirst_pairCode x y⟩
  have hcount :
      ((canonicalFinsetList B).map decodeFirst).count x =
        (finiteSetFstFiber B x).card := by
    simpa [finiteSetFstFiber, canonicalFinsetList_toFinset] using
      (list_count_map_eq_card_filter (canonicalFinsetList B)
        (canonicalFinsetList_nodup B) decodeFirst x)
  rw [finiteSetFstHeavyTruncation, List.mem_toFinset, heavyOutputList,
    List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [List.mem_dedup]
    exact List.mem_map.mpr
      ⟨pairCode x y, mem_canonicalFinsetList.mpr hxy,
        decodeFirst_pairCode x y⟩
  · rw [decide_eq_true_eq, hcount]
    exact pow_pred_le_card_of_le_finiteSetLogCard hfiber hheavy

/-- The heavy truncation is nonempty when the distinguished fibre is heavy. -/
theorem finiteSetFstHeavyTruncation_nonempty
    {B : Finset BitString} {x y : BitString} {l : Nat}
    (hxy : pairCode x y ∈ B)
    (hheavy : l ≤ finiteSetLogCard (finiteSetFstFiber B x)) :
    (finiteSetFstHeavyTruncation B l).Nonempty :=
  ⟨x, finiteSetFstHeavyTruncation_mem hxy hheavy⟩

/-- Heavy first-coordinate fibres consume disjoint portions of `B`, so their
number is at most `2^(log #B - l + 1)`. -/
theorem finiteSetFstHeavyTruncation_card_le
    (B : Finset BitString) (l : Nat) :
    (finiteSetFstHeavyTruncation B l).card ≤
      2 ^ (finiteSetLogCard B - l + 1) := by
  have hnodup :
      (heavyOutputList ((canonicalFinsetList B).map decodeFirst) l).Nodup := by
    unfold heavyOutputList
    exact (List.nodup_dedup _).filter _
  rw [finiteSetFstHeavyTruncation,
    List.toFinset_card_of_nodup hnodup]
  exact heavyOutputList_length_le B decodeFirst l

/-- Log-cardinality form of the heavy-fibre count. -/
theorem finiteSetFstHeavyTruncation_logCard_le
    (B : Finset BitString) (l : Nat) :
    finiteSetLogCard (finiteSetFstHeavyTruncation B l) ≤
      finiteSetLogCard B - l + 1 :=
  (finiteSetLogCard_le_iff _ _).mpr
    (finiteSetFstHeavyTruncation_card_le B l)

/-- Decode a canonical finite-set code, form the rounded heavy
first-coordinate list, and canonically encode its extensional finite set. -/
noncomputable def finiteSetFstHeavyTruncationCode
    (w lCode : BitString) : BitString :=
  canonicalImageCodeOfList
    (heavyOutputList
      ((canonicalPointListOfCode w).map decodeFirst)
      (bitsToNat lCode))

theorem finiteSetFstHeavyTruncationCode_computable :
    Computable₂ finiteSetFstHeavyTruncationCode := by
  have hpoints : Primrec (fun p : BitString × BitString =>
      canonicalPointListOfCode p.1) :=
    canonicalPointListOfCode_primrec.comp Primrec.fst
  have houtputs : Primrec (fun p : BitString × BitString =>
      (canonicalPointListOfCode p.1).map decodeFirst) :=
    Primrec.list_map hpoints
      ((decodeFirst_primrec.comp Primrec.snd).to₂)
  have hthreshold : Computable (fun p : BitString × BitString =>
      bitsToNat p.2) :=
    (bitsToNat_primrec.comp Primrec.snd).to_comp
  have hheavy : Computable (fun p : BitString × BitString =>
      heavyOutputList
        ((canonicalPointListOfCode p.1).map decodeFirst)
        (bitsToNat p.2)) :=
    heavyOutputList_computable.comp houtputs.to_comp hthreshold
  exact (canonicalImageCodeOfList_computable.comp hheavy).to₂

theorem finiteSetFstHeavyTruncationCode_codedUniformOn
    (B : Finset BitString) (hB : B.Nonempty) (l : Nat)
    (hH : (finiteSetFstHeavyTruncation B l).Nonempty) :
    finiteSetFstHeavyTruncationCode
        (codedUniformOn B hB).code (Nat.bits l) =
      (codedUniformOn (finiteSetFstHeavyTruncation B l) hH).code := by
  let L := heavyOutputList
    ((canonicalFinsetList B).map decodeFirst) l
  have hL : L.toFinset.Nonempty := by
    simpa [L, finiteSetFstHeavyTruncation] using hH
  unfold finiteSetFstHeavyTruncationCode
  simp only [canonicalPointListOfCode_codedUniformOn, bitsToNat_bits]
  change canonicalImageCodeOfList L = _
  rw [canonicalImageCodeOfList_eq_codedUniformOn L hL]
  exact codedUniformOn_code_congr hL hH rfl

/-- Plain decompressor that carries the logarithmic fibre threshold alongside
a program for the original pair model. -/
noncomputable def finiteSetFstHeavyTruncationPlainDecompressor
    (V : Map) : Map :=
  fun pr => (V (decodeSecond pr.1, [])).map (fun Bcode =>
    finiteSetFstHeavyTruncationCode Bcode (decodeFirst pr.1))

theorem finiteSetFstHeavyTruncationPlainDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (finiteSetFstHeavyTruncationPlainDecompressor V) := by
  unfold finiteSetFstHeavyTruncationPlainDecompressor
  refine Partrec.map ?_ ?_
  · exact Partrec.comp hV
      (Computable.pair (decodeSecond_computable.comp Computable.fst)
        (Computable.const []))
  · exact finiteSetFstHeavyTruncationCode_computable.comp Computable.snd
      (decodeFirst_computable.comp (Computable.fst.comp Computable.fst))

theorem finiteSetFstHeavyTruncationPlainDecompressor_produces
    (V : Map) (Bcode p : BitString) (l : Nat)
    (h : produces V p [] Bcode) :
    produces (finiteSetFstHeavyTruncationPlainDecompressor V)
      (pairCode (Nat.bits l) p) []
      (finiteSetFstHeavyTruncationCode Bcode (Nat.bits l)) := by
  unfold produces finiteSetFstHeavyTruncationPlainDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode]
  exact (Part.mem_map_iff _).2 ⟨Bcode, h, rfl⟩

/-- The executable heavy truncation costs only logarithmic advice for its
threshold in ordinary plain complexity. -/
theorem plainK_finiteSetFstHeavyTruncationCode_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (Bcode : BitString) (l : Nat),
      plainK V
          (finiteSetFstHeavyTruncationCode Bcode (Nat.bits l)) ≤
        plainK V Bcode + (logSlack c l : ENat) := by
  obtain ⟨cSim, hSim⟩ := hV.2
    (finiteSetFstHeavyTruncationPlainDecompressor V)
    (finiteSetFstHeavyTruncationPlainDecompressor_partrec V hV.1)
  refine ⟨cSim + 2, fun Bcode l => ?_⟩
  set M : Nat := 2 * (Nat.bits l).length + 1 with hM
  clear_value M
  have hbound :
      condK (finiteSetFstHeavyTruncationPlainDecompressor V)
          (finiteSetFstHeavyTruncationCode Bcode (Nat.bits l)) [] ≤
        condK V Bcode [] + (M : ENat) := by
    apply sInfLeSInfAdd
    rintro s₂ ⟨p, hp, rfl⟩
    refine ⟨(programLength (pairCode (Nat.bits l) p) : ENat),
      ⟨pairCode (Nat.bits l) p,
        finiteSetFstHeavyTruncationPlainDecompressor_produces
          V Bcode p l hp, rfl⟩, ?_⟩
    have hlen : (pairCode (Nat.bits l) p).length ≤ p.length + M := by
      rw [length_pairCode, hM]
      omega
    exact_mod_cast hlen
  calc
    plainK V (finiteSetFstHeavyTruncationCode Bcode (Nat.bits l))
        ≤ condK (finiteSetFstHeavyTruncationPlainDecompressor V)
            (finiteSetFstHeavyTruncationCode Bcode (Nat.bits l)) [] +
            (cSim : ENat) := hSim _ _
    _ ≤ (condK V Bcode [] + (M : ENat)) + (cSim : ENat) := by
      gcongr
    _ = plainK V Bcode + ((M : ENat) + (cSim : ENat)) := by
      change (condK V Bcode [] + (M : ENat)) + (cSim : ENat) =
        condK V Bcode [] + ((M : ENat) + (cSim : ENat))
      rw [add_assoc]
    _ ≤ plainK V Bcode + (logSlack (cSim + 2) l : ENat) := by
      gcongr
      have hle : M + cSim ≤ logSlack (cSim + 2) l := by
        rw [hM]
        unfold logSlack
        nlinarith [Nat.zero_le (cSim * (Nat.bits l).length)]
      calc
        (M : ENat) + (cSim : ENat) = ((M + cSim : Nat) : ENat) := by
          norm_cast
        _ ≤ (logSlack (cSim + 2) l : ENat) := by
          exact_mod_cast hle

/-- Ordinary plain set-complexity bound for the heavy truncation. -/
theorem finiteSetFstHeavyTruncation_plainSetComplexity_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (B : Finset BitString) (hB : B.Nonempty) (l : Nat)
        (hH : (finiteSetFstHeavyTruncation B l).Nonempty),
      plainSetComplexity V (finiteSetFstHeavyTruncation B l) hH ≤
        plainSetComplexity V B hB + (logSlack c l : ENat) := by
  obtain ⟨c, hc⟩ := plainK_finiteSetFstHeavyTruncationCode_le V hV
  refine ⟨c, fun B hB l hH => ?_⟩
  unfold plainSetComplexity
  rw [← finiteSetFstHeavyTruncationCode_codedUniformOn B hB l hH]
  exact hc (codedUniformOn B hB).code l

end Kolmogorov
