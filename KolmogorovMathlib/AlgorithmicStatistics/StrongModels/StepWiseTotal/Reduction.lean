import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWiseTotal.Part01

/-!
# The total reduction theorem

`strongSufficientStatistic_total_reduction` verifies
`StrongSufficientStatisticTotalReductionStatement`, the second conclusion of VS40
`thm:step-wise`: a strong sufficient statistic reduces totally to the model it describes.

The witness is `strongReductionSelectorFn`, which runs the encoded total program on every
element of the model decoded from the condition and returns the indexed heavy output; it is a
decompressor (`strongReductionSelectorFn_partrec`), total on a total program
(`strongReductionSelectorFn_total`), and outputs every `l`-heavy value
(`strongReductionSelectorFn_produces`).  `target_in_heavy_output_list` places the target among
those values and `heavyOutputList_length_le` bounds their number, so the fixed-width index is
short.  `stepWise_total_linear_arith` and `stepWise_logSlack_add` are the arithmetic.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

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
  obtain ⟨cDrop, hDrop⟩ := condK_le_plainK V hV
  obtain ⟨cLiteral, hLiteral⟩ := plainK_le_length V hV
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

/-- The heavy-output list of the image of `B` under `f` at level `l` has length at most
`2 ^ (finiteSetLogCard B - l + 1)`. -/
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
    Kolmogorov.primrec_two_pow_aux.comp
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

/-- The post-processing step of the strong reduction selector, which picks the indexed heavy
output, is computable in the outer input and the produced list. -/
theorem strongReductionSelectorPostFn_computable :
    Computable₂ strongReductionSelectorPostFn := by
  have hl : Computable
      (fun q : (BitString × BitString) × List BitString =>
        decodeBits (decodeTotalProgramPairFirst
          (decodeTotalProgramPairSecond q.1.1))) :=
    decodeBits_computable.comp
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

/-- The strong reduction selector built on a decompressor is again a decompressor. -/
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

/-- The selector's program built from a total program of `T` is total. -/
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

/-- The selector outputs every `l`-heavy value of a total program on the canonical list of `B`,
at the index recorded in its parameter block. -/
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
  obtain ⟨cLiteral, hLiteral⟩ := plainK_le_length V hV
  obtain ⟨cDrop, hDrop⟩ := condK_le_plainK V hV
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
