import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Support
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CanonicalImage
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaCount
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.StandardDescriptions
namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- From an entrywise `produces`-relation between an input list and an output
list, every input entry has a matching output entry (used to place `p(y)` in the
image set). -/
private theorem forall₂_produces_exists_output
    {T : Map} {p : BitString} {xs ys : List BitString}
    (hrel : List.Forall₂ (fun x y => produces T p x y) xs ys)
    {x : BitString} (hx : x ∈ xs) :
    ∃ y ∈ ys, produces T p x y := by
  induction hrel with
  | nil => simp at hx
  | @cons x' y' xs' ys' hxy htail ih =>
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨y', List.mem_cons_self, hxy⟩
    · obtain ⟨y, hy, hR⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem y' hy, hR⟩

theorem exists_plain_fullCube_image_of_total_program
    (V T : Map)
    (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
  ∃ c, ∀ p y b,
    IsTotalProgram T p →
    produces T p y b →
    ∃ (D : Finset BitString) (hD : D.Nonempty),
      b ∈ D ∧
      D.card ≤ 2 ^ y.length ∧
      plainSetComplexity V D hD ≤
        (programLength p + logSlack c y.length : ENat) := by
  -- A plain decompressor `E` reading a program `pairCode (Nat.bits ny) p`,
  -- recovering the length `ny` and the total program `p`, running `p` over the
  -- entire cube `allStrings ny`, and returning the canonical image-set code.
  let E : Map := fun input =>
    totalProgramImageCode T
      (decodeSecond input.1, allStrings (bitsToNat (decodeFirst input.1)))
  have hE : isDecompressor E :=
    Partrec.comp (totalProgramImageCode_partrec T hT.1)
      (Computable.pair (decodeSecond_computable.comp Computable.fst)
        (allStrings_primrec.to_comp.comp
          (bitsToNat_primrec.to_comp.comp
            (decodeFirst_computable.comp Computable.fst))))
  obtain ⟨cV, hcV⟩ := hV.2 E hE
  refine ⟨cV + 2, ?_⟩
  intro p y b hp hprod
  set ny := y.length with hny_def
  have hxs_nodup : (allStrings ny).Nodup := allStrings_nodup ny
  have hlen_pos : 0 < (allStrings ny).length := by
    rw [length_allStrings]; positivity
  have hxs_ne : allStrings ny ≠ [] := fun h => by
    rw [h] at hlen_pos; simp at hlen_pos
  have hy_mem : y ∈ allStrings ny := (mem_allStrings ny y).mpr hny_def.symm
  obtain ⟨ys, hys⟩ :=
    Part.dom_iff_mem.mp (totalProgramMapList_dom_of_total hp (allStrings ny))
  have hrel : List.Forall₂ (fun x y => produces T p x y) (allStrings ny) ys :=
    totalProgramMapList_correct hys
  have hD_ne : ys.toFinset.Nonempty :=
    totalProgramMapList_result_nonempty hxs_ne hys
  have hcode_eq :
      canonicalImageCodeOfList ys = (codedUniformOn ys.toFinset hD_ne).code :=
    canonicalImageCodeOfList_eq_codedUniformOn ys hD_ne
  refine ⟨ys.toFinset, hD_ne, ?_, ?_, ?_⟩
  · -- `b = p(y)` for `y ∈ allStrings ny`, hence `b` is in the image set
    rw [List.mem_toFinset]
    obtain ⟨y', hy'mem, hy'prod⟩ := forall₂_produces_exists_output hrel hy_mem
    have hby' : b = y' := Part.mem_unique hprod hy'prod
    rw [hby']; exact hy'mem
  · -- the image is no larger than the cube of size `2 ^ ny`
    calc ys.toFinset.card
        ≤ (allStrings ny).toFinset.card :=
          totalProgramMapList_result_card_le hxs_nodup hys
      _ = 2 ^ ny := by
          rw [List.toFinset_card_of_nodup hxs_nodup, length_allStrings]
  · -- plain set complexity ≤ |p| + O(log ny) via the decompressor `E`
    unfold plainSetComplexity
    have hcondE :
        condK E (codedUniformOn ys.toFinset hD_ne).code [] ≤
          (programLength (pairCode (Nat.bits ny) p) : ENat) := by
      apply sInf_le
      refine ⟨pairCode (Nat.bits ny) p, ?_, rfl⟩
      change (codedUniformOn ys.toFinset hD_ne).code ∈
        totalProgramImageCode T
          (decodeSecond (pairCode (Nat.bits ny) p),
            allStrings (bitsToNat (decodeFirst (pairCode (Nat.bits ny) p))))
      rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
      change (codedUniformOn ys.toFinset hD_ne).code ∈
        (totalProgramMapList T (p, allStrings ny)).map canonicalImageCodeOfList
      exact (Part.mem_map_iff _).2 ⟨ys, hys, hcode_eq⟩
    have hlen :
        programLength (pairCode (Nat.bits ny) p) =
          (Nat.bits ny).length + 1 + (Nat.bits ny).length + programLength p :=
      length_pairCode (Nat.bits ny) p
    calc plainK V (codedUniformOn ys.toFinset hD_ne).code
        ≤ condK E (codedUniformOn ys.toFinset hD_ne).code [] + (cV : ENat) :=
          hcV _ _
      _ ≤ (programLength (pairCode (Nat.bits ny) p) : ENat) + (cV : ENat) := by
          gcongr
      _ ≤ (programLength p + logSlack (cV + 2) ny : ENat) := by
          have harith :
              programLength (pairCode (Nat.bits ny) p) + cV ≤
                programLength p + logSlack (cV + 2) ny := by
            rw [hlen]; unfold logSlack
            nlinarith [Nat.zero_le (cV * (Nat.bits ny).length)]
          exact_mod_cast harith

theorem boundedOutputStage_remainder_lt_two_pow_succ_of_mem_standardBlock
    (q : Nat.Partrec.Code) (m j t : Nat) (b : BitString)
    (hb : b ∈ standardBlock q m j [])
    (hstage : b ∈ boundedOutputStage q m t) :
    omegaCount q m - (boundedOutputStage q m t).length <
      2 ^ (j + 1) := by
  -- The block `standardBlock q m j []` is the `j`-th dyadic block of the
  -- completed bound-`m` list, occupying positions `[start, start + 2^j)` where
  -- `start = (omegaCount q m / 2^(j+1)) * 2^(j+1)`.  Membership of `b` there
  -- forces its index `≥ start`; membership in the stage `t` prefix forces its
  -- index `< length`.  Hence `start < length` and the remainder
  -- `omegaCount q m - length ≤ omegaCount q m - start = omegaCount q m % 2^(j+1)
  -- < 2^(j+1)`.
  unfold standardBlock at hb
  split at hb
  · rw [List.mem_toFinset] at hb
    have hb_drop : b ∈ (completedBoundedOutput q m).drop
        (omegaCount q m / 2 ^ (j + 1) * 2 ^ (j + 1)) :=
      List.mem_of_mem_take hb
    set start := omegaCount q m / 2 ^ (j + 1) * 2 ^ (j + 1) with hstart_def
    have hnodup : (completedBoundedOutput q m).Nodup :=
      boundedOutputStage_nodup q m (maxHaltingStage q m)
    have hpref : boundedOutputStage q m t <+: completedBoundedOutput q m :=
      boundedOutputStage_prefix_completed q m t
    have hbL : b ∈ completedBoundedOutput q m := hpref.subset hstage
    -- index of `b` is below the length of the stage-`t` prefix
    have hidx_lt : (completedBoundedOutput q m).idxOf b <
        (boundedOutputStage q m t).length := by
      have hb_take : b ∈ (completedBoundedOutput q m).take
          (boundedOutputStage q m t).length := by
        rw [← List.prefix_iff_eq_take.mp hpref]; exact hstage
      exact (List.mem_take_iff_idxOf_lt hbL).mp hb_take
    -- index of `b` is at least `start`
    have hidx_ge : start ≤ (completedBoundedOutput q m).idxOf b := by
      by_contra hcon
      push Not at hcon
      have hb_take : b ∈ (completedBoundedOutput q m).take start :=
        (List.mem_take_iff_idxOf_lt hbL).mpr hcon
      have hnodup' : ((completedBoundedOutput q m).take start ++
          (completedBoundedOutput q m).drop start).Nodup := by
        rw [List.take_append_drop]; exact hnodup
      exact (List.disjoint_of_nodup_append hnodup') hb_take hb_drop
    have hstart_lt : start < (boundedOutputStage q m t).length :=
      lt_of_le_of_lt hidx_ge hidx_lt
    have key : start + omegaCount q m % 2 ^ (j + 1) = omegaCount q m := by
      rw [hstart_def, Nat.mul_comm (omegaCount q m / 2 ^ (j + 1)) (2 ^ (j + 1))]
      exact Nat.div_add_mod (omegaCount q m) (2 ^ (j + 1))
    have hmod_lt : omegaCount q m % 2 ^ (j + 1) < 2 ^ (j + 1) :=
      Nat.mod_lt _ (by positivity)
    omega
  · simp at hb

open Classical in
noncomputable def lemma4Decoder (V : Map) : Map := fun input => do
  let z := input.1
  let Dcode := decodeFirst (decodeFirst z)
  let qcode := decodeSecond (decodeFirst z)
  let m_bits := decodeFirst (decodeSecond z)
  let r_bits := decodeSecond (decodeSecond z)
  let m := bitsToNat m_bits
  let r := bitsToNat r_bits
  let code_D ← V (Dcode, [])
  let L := (decodeDistributionData code_D).map CodedDistributionEntry.point
  let q_enum ← V (qcode, [])
  let q_code ← Part.ofOption (Encodable.decode (α := Nat.Partrec.Code) (bitsToNat q_enum))
  let t ← Nat.rfind (fun t => Part.some
    (L.all (fun z => decide (z ∈ boundedOutputStage q_code m t))))
  let result := (boundedOutputStage q_code m t).length + r
  Part.some (Nat.bits result)

/- Keep the nested encodings opaque while composing the uniform decoder with
unbounded search. -/
attribute [local irreducible] Primcodable.prod Primcodable.list

theorem lemma4Decoder_partrec (V : Map) (hV : isDecompressor V) :
    Partrec (lemma4Decoder V) := by
  let Input := BitString × BitString
  let AfterD := Input × BitString
  let AfterQ := AfterD × BitString
  have hDcode : Computable (fun input : Input =>
      decodeFirst (decodeFirst input.1)) :=
    decodeFirst_computable.comp
      (decodeFirst_computable.comp Computable.fst)
  have hQcode : Computable (fun input : Input =>
      decodeSecond (decodeFirst input.1)) :=
    decodeSecond_computable.comp
      (decodeFirst_computable.comp Computable.fst)
  have hm : Computable (fun input : Input =>
      bitsToNat (decodeFirst (decodeSecond input.1))) :=
    bitsToNat_primrec.to_comp.comp
      (decodeFirst_computable.comp
        (decodeSecond_computable.comp Computable.fst))
  have hr : Computable (fun input : Input =>
      bitsToNat (decodeSecond (decodeSecond input.1))) :=
    bitsToNat_primrec.to_comp.comp
      (decodeSecond_computable.comp
        (decodeSecond_computable.comp Computable.fst))
  have hrunD : Partrec (fun input : Input =>
      V (decodeFirst (decodeFirst input.1), [])) :=
    Partrec.comp hV
      (Computable.pair hDcode (Computable.const []))
  have hrunQ : Partrec (fun input : AfterD =>
      V (decodeSecond (decodeFirst input.1.1), [])) :=
    Partrec.comp hV
      (Computable.pair (hQcode.comp Computable.fst)
        (Computable.const []))
  have hdecodeQ : Computable (fun input : AfterQ =>
      Encodable.decode (α := Nat.Partrec.Code) (bitsToNat input.2)) :=
    Computable.decode.comp
      (bitsToNat_primrec.to_comp.comp Computable.snd)
  have hdecodeQPart : Partrec (fun input : AfterQ =>
      Part.ofOption
        (Encodable.decode (α := Nat.Partrec.Code)
          (bitsToNat input.2))) :=
    Computable.ofOption hdecodeQ
  have hL : Primrec (fun input : AfterQ =>
      (decodeDistributionData input.1.2).map
        CodedDistributionEntry.point) :=
    Primrec.list_map
      (decodeDistributionData_primrec.comp
        (Primrec.snd.comp Primrec.fst))
      (entry_point_primrec.comp Primrec.snd).to₂
  have hmR : Primrec (fun input : AfterQ =>
      bitsToNat (decodeFirst (decodeSecond input.1.1.1))) :=
    bitsToNat_primrec.comp
      (decodeFirst_primrec.comp
        (decodeSecond_primrec.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have hstage : Primrec
      (fun input : ((AfterQ × Nat.Partrec.Code) × Nat) =>
        boundedOutputStage input.1.2
          (bitsToNat
            (decodeFirst (decodeSecond input.1.1.1.1.1)))
          input.2) :=
    boundedOutputStage_primrec_uniform.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          (hmR.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd)
  have hlist : Primrec
      (fun input : ((AfterQ × Nat.Partrec.Code) × Nat) =>
        (decodeDistributionData input.1.1.1.2).map
          CodedDistributionEntry.point) :=
    hL.comp (Primrec.fst.comp Primrec.fst)
  have hpred : Primrec₂
      (fun (input : ((AfterQ × Nat.Partrec.Code) × Nat))
        (z : BitString) =>
          decide (z ∈ boundedOutputStage input.1.2
            (bitsToNat
              (decodeFirst (decodeSecond input.1.1.1.1.1)))
            input.2)) :=
    (bitString_mem_primrec.comp Primrec.snd
      (hstage.comp Primrec.fst)).to₂
  have hcheckPair : Computable
      (fun input : (AfterQ × Nat.Partrec.Code) × Nat =>
        ((decodeDistributionData input.1.1.1.2).map
          CodedDistributionEntry.point).all
            (fun z => decide (z ∈ boundedOutputStage input.1.2
              (bitsToNat
                (decodeFirst (decodeSecond input.1.1.1.1.1))) input.2))) :=
    (list_all_primrec hlist hpred).to_comp
  have hcheck : Computable₂
      (fun (input : AfterQ × Nat.Partrec.Code) (t : Nat) =>
        ((decodeDistributionData input.1.1.2).map
          CodedDistributionEntry.point).all
            (fun z => decide (z ∈ boundedOutputStage input.2
              (bitsToNat
                (decodeFirst (decodeSecond input.1.1.1.1))) t))) := by
    exact hcheckPair.to₂
  have hfind : Partrec (fun input : AfterQ × Nat.Partrec.Code =>
      Nat.rfind (fun t => Part.some
        (((decodeDistributionData input.1.1.2).map
          CodedDistributionEntry.point).all
            (fun z => decide (z ∈ boundedOutputStage input.2
              (bitsToNat
                (decodeFirst (decodeSecond input.1.1.1.1))) t))))) :=
    Partrec.rfind hcheck.partrec₂
  have hstageR : Computable
      (fun input : (AfterQ × Nat.Partrec.Code) × Nat =>
        boundedOutputStage input.1.2
          (bitsToNat
            (decodeFirst (decodeSecond input.1.1.1.1.1)))
          input.2) :=
    hstage.to_comp
  have hrR : Computable (fun input : AfterQ × Nat.Partrec.Code =>
      bitsToNat
        (decodeSecond (decodeSecond input.1.1.1.1))) :=
    hr.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hpost : Computable₂
      (fun (input : AfterQ × Nat.Partrec.Code) (t : Nat) =>
        Nat.bits
          ((boundedOutputStage input.2
            (bitsToNat
              (decodeFirst (decodeSecond input.1.1.1.1))) t).length +
            bitsToNat
              (decodeSecond (decodeSecond input.1.1.1.1)))) := by
    exact natBitsComputable.comp
      (Primrec.nat_add.to_comp.comp
        (Computable.list_length.comp hstageR)
        (hrR.comp Computable.fst)) |>.to₂
  let searchThen : AfterQ × Nat.Partrec.Code →. BitString :=
      fun input =>
        (Nat.rfind (fun t => Part.some
          (((decodeDistributionData input.1.1.2).map
            CodedDistributionEntry.point).all
              (fun z => decide (z ∈ boundedOutputStage input.2
                (bitsToNat
                  (decodeFirst (decodeSecond input.1.1.1.1))) t))))).bind
          (fun t => Part.some
            (Nat.bits
              ((boundedOutputStage input.2
                (bitsToNat
                  (decodeFirst (decodeSecond input.1.1.1.1))) t).length +
                bitsToNat
                  (decodeSecond (decodeSecond input.1.1.1.1)))))
  have hsearchThen : Partrec searchThen := by
    exact (Partrec.bind hfind hpost.partrec₂).of_eq (fun _ => rfl)
  let decodeThen : AfterQ →. BitString := fun input =>
      (Part.ofOption
        (Encodable.decode (α := Nat.Partrec.Code)
          (bitsToNat input.2))).bind
        (fun q_code => searchThen (input, q_code))
  have hdecodeThen : Partrec decodeThen := by
    exact (Partrec.bind hdecodeQPart hsearchThen.to₂).of_eq (fun _ => rfl)
  let qThen : AfterD →. BitString := fun input =>
      (V (decodeSecond (decodeFirst input.1.1), [])).bind
        (fun q_enum => decodeThen (input, q_enum))
  have hqThen : Partrec qThen := by
    exact (Partrec.bind hrunQ hdecodeThen.to₂).of_eq (fun _ => rfl)
  let all : Input →. BitString := fun input =>
      (V (decodeFirst (decodeFirst input.1), [])).bind
        (fun code_D => qThen (input, code_D))
  have hall : Partrec all := by
    exact (Partrec.bind hrunD hqThen.to₂).of_eq (fun _ => rfl)
  exact hall.of_eq (fun _ => rfl)

theorem lemma4Decoder_eval
    (V : Map) (q : Nat.Partrec.Code) (m : Nat)
    (D : Finset BitString) (hD : D.Nonempty) (t r : Nat)
    (pD pQ : BitString)
    (hDprog : produces V pD [] (codedUniformOn D hD).code)
    (hQprog : produces V pQ [] (standardEnumeratorCode q))
    (hcover : ∀ z ∈ D, z ∈ boundedOutputStage q m t)
    (hmin : ∀ t', t' < t →
      ¬ (∀ z ∈ D, z ∈ boundedOutputStage q m t')) :
    Nat.bits ((boundedOutputStage q m t).length + r) ∈
      lemma4Decoder V
        (pairCode (pairCode pD pQ)
          (pairCode (Nat.bits m) (Nat.bits r)), []) := by
  have hall : (canonicalFinsetList D).all
      (fun z => decide (z ∈ boundedOutputStage q m t)) = true := by
    rw [List.all_eq_true]
    intro z hz
    simp only [decide_eq_true_eq]
    exact hcover z (mem_canonicalFinsetList.mp hz)
  have hnone : ∀ t', t' < t →
      (canonicalFinsetList D).all
        (fun z => decide (z ∈ boundedOutputStage q m t')) = false := by
    intro t' ht'
    rw [Bool.eq_false_iff]
    intro hall'
    apply hmin t' ht'
    intro z hz
    have hzList : z ∈ canonicalFinsetList D :=
      mem_canonicalFinsetList.mpr hz
    have hzTrue := (List.all_eq_true.mp hall') z hzList
    simpa only [decide_eq_true_eq] using hzTrue
  have hfind : t ∈ Nat.rfind (fun t' => Part.some
      ((canonicalFinsetList D).all
        (fun z => decide (z ∈ boundedOutputStage q m t')))) := by
    rw [Nat.mem_rfind]
    refine ⟨by simp [hall], ?_⟩
    intro t' ht'
    simp [hnone t' ht']
  unfold lemma4Decoder
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  change Nat.bits ((boundedOutputStage q m t).length + r) ∈
    (V (pD, [])).bind (fun code_D =>
      (V (pQ, [])).bind (fun q_enum =>
        (Part.ofOption
          (Encodable.decode (α := Nat.Partrec.Code)
            (bitsToNat q_enum))).bind (fun q_code =>
          (Nat.rfind (fun t' => Part.some
            (((decodeDistributionData code_D).map
              CodedDistributionEntry.point).all
                (fun z => decide
                  (z ∈ boundedOutputStage q_code m t'))))).bind
            (fun t' => Part.some
              (Nat.bits ((boundedOutputStage q_code m t').length + r))))))
  rw [Part.mem_bind_iff]
  refine ⟨(codedUniformOn D hD).code, hDprog, ?_⟩
  simp only [dataPoints_codedUniformOn]
  rw [Part.mem_bind_iff]
  refine ⟨standardEnumeratorCode q, hQprog, ?_⟩
  unfold standardEnumeratorCode
  simp only [bitsToNat_bits, Encodable.encodek]
  rw [Part.mem_bind_iff]
  refine ⟨q, by simp, ?_⟩
  rw [Part.mem_bind_iff]
  exact ⟨t, hfind, by simp⟩

/-- The complexity bound delivered by the currently implemented nested decoder
input.  This records its *actual* framing coefficients and separates the
computability/semantic work from the still-open coefficient-one accounting
needed below. -/
theorem plainKNat_omegaCount_le_of_stage_cover_nested
    (V : Map) (hV : isOptimalConditional V) :
  ∃ c, ∀ q m D (hD : D.Nonempty) t,
    (∀ z ∈ D, z ∈ boundedOutputStage q m t) →
    (∀ t', t' < t → ¬ (∀ z ∈ D, z ∈ boundedOutputStage q m t')) →
    let r := omegaCount q m - (boundedOutputStage q m t).length
    plainKNat V (omegaCount q m) ≤
      4 * plainSetComplexity V D hD +
        2 * plainK V (standardEnumeratorCode q) +
        2 * ((Nat.bits m).length : ENat) +
        ((Nat.bits r).length : ENat) +
        (c : ENat) := by
  have hDecoder : Partrec (fun z : BitString => lemma4Decoder V (z, [])) :=
    (lemma4Decoder_partrec V hV.1).comp
      (Computable.pair Computable.id (Computable.const []))
  obtain ⟨cMap, hMap⟩ :=
    plainK_partrec_map_le V hV
      (fun z : BitString => lemma4Decoder V (z, [])) hDecoder
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  let c := 4 + cLen + cMap
  refine ⟨c, ?_⟩
  intro q m D hD t hcover hmin
  dsimp only
  have hDfinite : plainK V (codedUniformOn D hD).code ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top
        ((codedUniformOn D hD).code.length + cLen)))
      (hLen (codedUniformOn D hD).code)
  obtain ⟨pD, hpD, hpDLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := (codedUniformOn D hD).code) (y := []) hDfinite
  have hQfinite : plainK V (standardEnumeratorCode q) ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top
        ((standardEnumeratorCode q).length + cLen)))
      (hLen (standardEnumeratorCode q))
  obtain ⟨pQ, hpQ, hpQLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := standardEnumeratorCode q) (y := []) hQfinite
  let r := omegaCount q m - (boundedOutputStage q m t).length
  let input := pairCode (pairCode pD pQ)
    (pairCode (Nat.bits m) (Nat.bits r))
  have hstageLength :
      (boundedOutputStage q m t).length ≤ omegaCount q m := by
    unfold omegaCount
    exact (boundedOutputStage_prefix_completed q m t).length_le
  have heval : Nat.bits (omegaCount q m) ∈ lemma4Decoder V (input, []) := by
    have h := lemma4Decoder_eval V q m D hD t r pD pQ hpD hpQ hcover hmin
    simpa only [input, r, Nat.add_sub_of_le hstageLength] using h
  have hinputLength : input.length =
      4 * pD.length + 2 * pQ.length +
        2 * (Nat.bits m).length + (Nat.bits r).length + 4 := by
    simp only [input, length_pairCode]
    ring
  have hpDLengthEq : (pD.length : ENat) = plainSetComplexity V D hD := hpDLength
  have hpQLengthEq : (pQ.length : ENat) =
      plainK V (standardEnumeratorCode q) := hpQLength
  calc
    plainKNat V (omegaCount q m)
        ≤ plainK V input + (cMap : ENat) := hMap input _ heval
    _ ≤ ((input.length : ENat) + (cLen : ENat)) + (cMap : ENat) := by
      gcongr
      exact hLen input
    _ = 4 * plainSetComplexity V D hD +
          2 * plainK V (standardEnumeratorCode q) +
          2 * ((Nat.bits m).length : ENat) +
          ((Nat.bits r).length : ENat) + (c : ENat) := by
      rw [hinputLength]
      push_cast
      rw [hpDLengthEq, hpQLengthEq]
      dsimp [c]
      push_cast
      ring


end Kolmogorov
