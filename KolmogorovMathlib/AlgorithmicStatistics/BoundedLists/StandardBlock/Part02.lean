import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock.Part01

/-!
# Standard blocks: coding, and the positive branch

`prop_std_pos` (VS40 Proposition `prop:std-pos`) is the statement this part proves: for a
genuine standard block containing `x`, both the complexity of the block's code and its
cardinality are what the source claims, so the block is a two-part description of `x` of the
intended shape.

Its coding half is the decoder `standardBlockOmegaDecoder`, which runs an embedded program to
obtain a block code and then uses the tail selector to identify the block; it reads the input
format `plainProgramAdvice` (program, bound, count), is partial recursive
(`standardBlockOmegaDecoder_partrec`), recovers the block
(`standardBlockOmegaDecoder_recovers`), and therefore bounds `m` by the complexity of a block
code plus a logarithmic term (`standardBlock_omega_coding_bound`).  The slack arithmetic
turning that into `prop_std_pos` is `pow_sub_two_mul_le_add_one`,
`two_mul_logSlack_add_one_le`, `logSlack_add_const_le_of_add_le` and
`pow_sub_logSlack_le_add_one`.

The module closes with the length filter: `lengthFilteredModel` keeps the members of a model
of one length, `lengthFilterUniformCodeSelector` computes its code, and
`setComplexity_lengthFilteredModel_le` shows the restriction costs only logarithmic slack.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- Simplicity of a standard description given x. -/
theorem standard_description_simple_given_x
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m j x),
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      condK V
        (codedUniformOn (standardBlock c m j x) hA).code x ≤
          (logSlack C m : ENat) := by
  have _hc := hc
  obtain ⟨Cmap, hmap⟩ :=
    condK_partrec_cond_map_le V hV
      (standardBlockFromMemberSelector c)
      (standardBlockFromMemberSelector_partrec c)
  let C := Cmap + 4
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  have hjm : j ≤ m :=
    standardBlock_exponent_le c m j x hx
  have hjlen :
      (Nat.bits j).length ≤ (Nat.bits m).length :=
    length_natBits_mono hjm
  have hrec :=
    standardBlockFromMemberSelector_recovers c m j x hx
  calc
    condK V
          (codedUniformOn (standardBlock c m j x) hA).code x
        ≤ ((standardBlockAdvice m j).length : ENat) +
            (Cmap : ENat) :=
      hmap x (standardBlockAdvice m j)
        (codedUniformOn (standardBlock c m j x) hA).code hrec
    _ = (((standardBlockAdvice m j).length + Cmap : ℕ) : ENat) := by
      rw [Nat.cast_add]
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast (show
        (standardBlockAdvice m j).length + Cmap ≤
          logSlack C m by
        rw [standardBlockAdvice_length]
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits m).length)])

/-- At a stage covering the whole standard block of `x`, the outputs still missing
number at most the tail of that block. -/
theorem stageMissing_le_standardBlockTail
    (c : Code) (m j t : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m j x)
    (hcover : ∀ y ∈ standardBlock c m j x,
      y ∈ boundedOutputStage c m t) :
    omegaCount c m - (boundedOutputStage c m t).length ≤
      standardBlockTail c m j := by
  let L := completedBoundedOutput c m
  let S := boundedOutputStage c m t
  let p := 2 ^ j
  let start :=
    (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1)
  have hbit := standardBlock_testBit_of_mem c m j x hx
  have hfit : start + p ≤ L.length := by
    change
      (omegaCount c m / 2 ^ (j + 1)) * 2 ^ (j + 1) +
          2 ^ j ≤ omegaCount c m
    exact standardBlock_start_add_size_le hbit
  have hp : 0 < p := by
    dsimp [p]
    positivity
  let k := p - 1
  have hk : k < ((L.drop start).take p).length := by
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    · dsimp [k]
      omega
    · omega
  let y := ((L.drop start).take p)[k]
  have hySlice : y ∈ (L.drop start).take p :=
    List.getElem_mem hk
  have hyBlock : y ∈ standardBlock c m j x := by
    unfold standardBlock
    rw [if_pos hbit, List.mem_toFinset]
    simpa [L, start, p] using hySlice
  have hyS : y ∈ S := hcover y hyBlock
  have hprefix : S <+: L :=
    boundedOutputStage_prefix_completed c m t
  have hyIdxLt : L.idxOf y < S.length :=
    (hprefix.mem_iff_idxOf_lt_length y).mp hyS
  have hglobal : start + k < L.length := by
    omega
  have hyGet : L[start + k] = y := by
    dsimp [y]
    simp only [List.getElem_take, List.getElem_drop]
  have hnodup : L.Nodup := by
    dsimp [L, completedBoundedOutput]
    exact boundedOutputStage_nodup c m
      (maxHaltingStage c m)
  have hidx : L.idxOf y = start + k := by
    rw [← hyGet]
    exact hnodup.idxOf_getElem (start + k) hglobal
  have hendLe : start + p ≤ S.length := by
    rw [hidx] at hyIdxLt
    dsimp [k] at hyIdxLt
    omega
  have hdecomp :=
    standardBlock_end_add_tail c m j hbit
  change omegaCount c m - S.length ≤
    standardBlockTail c m j
  omega

/-- A program with its length in front, followed by the bound `m` and a count: the
input format of the standard-block decoder. -/
def plainProgramAdvice (p : BitString) (m count : ℕ) : BitString :=
  pairCode (Nat.bits p.length)
    (p ++ pairCode (Nat.bits m) (Nat.bits count))

/-- The exact length of an advice string in terms of the program length, the bound
and the count. -/
theorem plainProgramAdvice_length (p : BitString) (m count : ℕ) :
    (plainProgramAdvice p m count).length =
      p.length + 2 * (Nat.bits p.length).length +
        2 * (Nat.bits m).length + (Nat.bits count).length + 2 := by
  unfold plainProgramAdvice
  rw [length_pairCode, List.length_append, length_pairCode]
  omega

/-- The decoder that runs the embedded program to obtain a block code and then uses
the tail selector to output the binary numeral of `omegaCount c m`. -/
noncomputable def standardBlockOmegaDecoder
    (V : Map) (c : Code) : BitString →. BitString := fun z =>
  let payload := decodeSecond z
  let pLength := bitsToNat (decodeFirst z)
  let p := payload.take pLength
  let advice := payload.drop pLength
  (V (p, [])).bind fun SCode =>
    descriptionTailOmegaSelector c
      (descriptionTailOmegaInput SCode
        (bitsToNat (decodeFirst advice))
        (bitsToNat (decodeSecond advice)))

/-- The standard-block decoder is a partial recursive function of its input. -/
theorem standardBlockOmegaDecoder_partrec
    (V : Map) (hV : isDecompressor V) (c : Code) :
    Partrec (standardBlockOmegaDecoder V c) := by
  have hpLength : Primrec (fun z : BitString =>
      bitsToNat (decodeFirst z)) :=
    bitsToNat_primrec.comp decodeFirst_primrec
  have hp : Computable (fun z : BitString =>
      (decodeSecond z).take
        (bitsToNat (decodeFirst z))) :=
    (Primrec.list_take.comp hpLength decodeSecond_primrec).to_comp
  have hrun : Partrec (fun z : BitString =>
      V (((decodeSecond z).take
        (bitsToNat (decodeFirst z))), [])) :=
    Partrec.comp hV
      (Computable.pair hp (Computable.const []))
  have hadvice : Primrec (fun z : BitString =>
      (decodeSecond z).drop
        (bitsToNat (decodeFirst z))) :=
    Primrec.list_drop.comp hpLength decodeSecond_primrec
  have hm : Primrec (fun z : BitString =>
      bitsToNat (decodeFirst
        ((decodeSecond z).drop
          (bitsToNat (decodeFirst z))))) :=
    bitsToNat_primrec.comp
      (decodeFirst_primrec.comp hadvice)
  have hcount : Primrec (fun z : BitString =>
      bitsToNat (decodeSecond
        ((decodeSecond z).drop
          (bitsToNat (decodeFirst z))))) :=
    bitsToNat_primrec.comp
      (decodeSecond_primrec.comp hadvice)
  have hinput : Primrec (fun q : BitString × BitString =>
      descriptionTailOmegaInput q.2
        (bitsToNat (decodeFirst
          ((decodeSecond q.1).drop
            (bitsToNat (decodeFirst q.1)))))
        (bitsToNat (decodeSecond
          ((decodeSecond q.1).drop
            (bitsToNat (decodeFirst q.1)))))) := by
    unfold descriptionTailOmegaInput
    exact pairCode_primrec.comp Primrec.snd
      (pairCode_primrec.comp
        (primrec_natBits.comp (hm.comp Primrec.fst))
        (primrec_natBits.comp (hcount.comp Primrec.fst)))
  have hpost : Partrec (fun q : BitString × BitString =>
      descriptionTailOmegaSelector c
        (descriptionTailOmegaInput q.2
          (bitsToNat (decodeFirst
            ((decodeSecond q.1).drop
              (bitsToNat (decodeFirst q.1)))))
          (bitsToNat (decodeSecond
            ((decodeSecond q.1).drop
              (bitsToNat (decodeFirst q.1))))))) :=
    Partrec.comp (descriptionTailOmegaSelector_partrec c)
      hinput.to_comp
  unfold standardBlockOmegaDecoder
  exact Partrec.bind hrun hpost

/-- From a program for the code of a standard block, together with a count bounded
by the block tail, the decoder outputs the numeral of `omegaCount c m`. -/
theorem standardBlockOmegaDecoder_recovers
    (V : Map) (c : Code) (m j : ℕ) (x p : BitString)
    (hx : x ∈ standardBlock c m j x)
    (hp : produces V p []
      (codedUniformOn (standardBlock c m j x) ⟨x, hx⟩).code) :
    ∃ count ≤ standardBlockTail c m j,
      omegaNatCode c m ∈
        standardBlockOmegaDecoder V c
          (plainProgramAdvice p m count) := by
  let B := standardBlock c m j x
  let hB : B.Nonempty := ⟨x, hx⟩
  let SCode := (codedUniformOn B hB).code
  let SList := canonicalFinsetList B
  have hSList :
      SList =
        (decodeDistributionData SCode).map
          CodedDistributionEntry.point := by
    exact (dataPoints_codedUniformOn B hB).symm
  have hsubset :
      ∀ y ∈ SList, y ∈ completedBoundedOutput c m := by
    intro y hy
    change y ∈ canonicalFinsetList B at hy
    rw [mem_canonicalFinsetList] at hy
    rw [← List.mem_toFinset]
    exact standardBlock_subset_completed c m j x hy
  have hex :
      ∃ t, SList.all (fun y =>
        (boundedOutputStage c m t).elem y) = true := by
    obtain ⟨t, ht⟩ :=
      exists_stage_covering_finset c m B
        (fun y hy => hsubset y
          (mem_canonicalFinsetList.mpr hy))
    refine ⟨t, ?_⟩
    rw [List.all_eq_true]
    intro y hy
    rw [List.elem_eq_mem]
    exact decide_eq_true
      (ht y (mem_canonicalFinsetList.mp hy))
  let t₀ := Nat.find hex
  have ht₀spec :
      SList.all (fun y =>
        (boundedOutputStage c m t₀).elem y) = true :=
    Nat.find_spec hex
  have ht₀mem :
      t₀ ∈ Nat.rfind (fun t => Part.some
        (SList.all (fun y =>
          (boundedOutputStage c m t).elem y))) := by
    let p : ℕ →. Bool := fun t => Part.some (SList.all (fun y => (boundedOutputStage c m t).elem y))
    change t₀ ∈ Nat.rfind p
    rw [Nat.mem_rfind]
    dsimp [p]
    refine ⟨Part.mem_some_iff.mpr ht₀spec.symm, ?_⟩
    intro t ht
    exact Part.mem_some_iff.mpr (Bool.eq_false_iff.mpr (Nat.find_min hex ht)).symm
  let count :=
    omegaCount c m -
      (boundedOutputStage c m t₀).length
  have hcoverAt :
      ∀ y ∈ standardBlock c m j x,
        y ∈ boundedOutputStage c m t₀ := by
    rw [List.all_eq_true] at ht₀spec
    intro y hy
    have hyElem :=
      ht₀spec y
        (mem_canonicalFinsetList.mpr hy)
    simpa [List.elem_eq_mem] using hyElem
  have hcountLe :
      count ≤ standardBlockTail c m j :=
    stageMissing_le_standardBlockTail
      c m j t₀ x hx hcoverAt
  have hrecover :
      descriptionTailOmegaSelector c
          (descriptionTailOmegaInput SCode m count) =
        Part.some (Nat.bits (omegaCount c m)) := by
    apply descriptionTailOmegaSelector_recovers
      c m SCode SList hSList hsubset count
    exact
      ⟨t₀, (Part.eq_some_iff.mpr ht₀mem).symm, rfl⟩
  have hselector :
      omegaNatCode c m ∈
        descriptionTailOmegaSelector c
          (descriptionTailOmegaInput SCode m count) :=
    Part.eq_some_iff.mp hrecover
  refine ⟨count, hcountLe, ?_⟩
  unfold standardBlockOmegaDecoder
  simp only [plainProgramAdvice, decodeSecond_pairCode,
    decodeFirst_pairCode, bitsToNat_bits, List.take_left,
    List.drop_left]
  rw [Part.mem_bind_iff]
  refine ⟨SCode, ?_, ?_⟩
  · simpa [SCode, B, hB] using hp
  · simpa using hselector

/-- The bound `m` is at most the plain complexity of the code of a standard block
plus the bits of its tail, up to logarithmic slack. -/
theorem standardBlock_omega_coding_bound
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C, ∀ m j x (hx : x ∈ standardBlock c m j x),
      (m : ENat) ≤
        plainK V
          (codedUniformOn (standardBlock c m j x) ⟨x, hx⟩).code +
        ((Nat.bits (standardBlockTail c m j)).length : ENat) +
        (logSlack C m : ENat) := by
  obtain ⟨COmega, hOmega⟩ :=
    plainKNat_omegaCount_lower V hV c hc
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV
      (standardBlockOmegaDecoder V c)
      (standardBlockOmegaDecoder_partrec V hV.1 c)
  obtain ⟨Clen, hlen⟩ := plainK_le_length V hV
  obtain ⟨Cupper, hupper⟩ :=
    plainK_standardBlock_upper V hV c hc
  let C :=
    2 * (Nat.bits Cupper).length +
      Clen + Cmap + COmega + 10
  refine ⟨C, fun m j x hx => ?_⟩
  let B := standardBlock c m j x
  let hB : B.Nonempty := ⟨x, hx⟩
  let BCode := (codedUniformOn B hB).code
  have hfinite : plainK V BCode ≠ ⊤ := by
    intro htop
    have h := hlen BCode
    rw [htop] at h
    exact ENat.natCast_ne_top _
      (top_le_iff.mp h)
  obtain ⟨p, hp, hpLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := BCode) (y := []) hfinite
  have hpLengthEq :
      (p.length : ENat) = plainK V BCode := by
    exact hpLength
  have hpLengthUpper :
      p.length ≤ m - j + logSlack Cupper m := by
    have h := hupper m j x hx
    change plainK V BCode ≤
      ((m - j + logSlack Cupper m : ℕ) : ENat) at h
    rw [← hpLengthEq] at h
    exact_mod_cast h
  obtain ⟨count, hcountLe, hrecover⟩ :=
    standardBlockOmegaDecoder_recovers
      V c m j x p hx
        (by simpa [BCode, B, hB] using hp)
  have hcountBits :
      (Nat.bits count).length ≤
        (Nat.bits (standardBlockTail c m j)).length :=
    length_natBits_mono hcountLe
  let input := plainProgramAdvice p m count
  have hinputLength :
      input.length =
        p.length + 2 * (Nat.bits p.length).length +
          2 * (Nat.bits m).length +
          (Nat.bits count).length + 2 := by
    exact plainProgramAdvice_length p m count
  have hpBits :
      (Nat.bits p.length).length ≤
        2 * (Nat.bits m).length +
          (Nat.bits Cupper).length + 2 := by
    have hpLe :
        p.length ≤ m + logSlack Cupper m := by
      omega
    calc
      (Nat.bits p.length).length
          ≤ (Nat.bits
              (m + logSlack Cupper m)).length :=
        length_natBits_mono hpLe
      _ ≤ (Nat.bits m).length +
          (Nat.bits (logSlack Cupper m)).length + 1 :=
        length_natBits_add_le m (logSlack Cupper m)
      _ ≤ 2 * (Nat.bits m).length +
          (Nat.bits Cupper).length + 2 := by
        have hlog :=
          length_natBits_logSlack_le Cupper m
        omega
  have hoverhead :
      2 * (Nat.bits p.length).length +
          2 * (Nat.bits m).length + 2 +
          Clen + Cmap + COmega ≤
        logSlack C m := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le ((Nat.bits Cupper).length),
      Nat.zero_le Clen, Nat.zero_le Cmap,
      Nat.zero_le COmega]
  have hdecode :
      plainKNat V (omegaCount c m) ≤
        plainK V input + (Cmap : ENat) := by
    exact hmap input (omegaNatCode c m)
      (by simpa [input] using hrecover)
  calc
    (m : ENat)
        ≤ plainKNat V (omegaCount c m) +
            (COmega : ENat) :=
      hOmega m
    _ ≤ (plainK V input + (Cmap : ENat)) +
          (COmega : ENat) := by
      gcongr
    _ ≤ (((input.length : ENat) + (Clen : ENat)) +
          (Cmap : ENat)) + (COmega : ENat) := by
      gcongr
      exact hlen input
    _ = ((p.length +
          2 * (Nat.bits p.length).length +
          2 * (Nat.bits m).length +
          (Nat.bits count).length + 2 +
          Clen + Cmap + COmega : ℕ) : ENat) := by
      rw [hinputLength]
      push_cast
      ring
    _ ≤ ((p.length +
          (Nat.bits (standardBlockTail c m j)).length +
          logSlack C m : ℕ) : ENat) := by
      exact_mod_cast (by omega)
    _ = plainK V BCode +
          ((Nat.bits
            (standardBlockTail c m j)).length : ENat) +
          (logSlack C m : ENat) := by
      rw [← hpLengthEq]
      push_cast
      rfl
    _ = plainK V
          (codedUniformOn
            (standardBlock c m j x) ⟨x, hx⟩).code +
          ((Nat.bits
            (standardBlockTail c m j)).length : ENat) +
          (logSlack C m : ENat) := rfl

/-- An arithmetic step of the block estimate: under the stated inequalities,
`2 ^ (j - (2 * S + 1)) ≤ t + 1`. -/
theorem pow_sub_two_mul_le_add_one
    {m j k t S : ℕ}
    (hjm : j ≤ m)
    (hrec : m ≤ k + (Nat.bits t).length + S)
    (hk : k ≤ m - j + S) :
    2 ^ (j - (2 * S + 1)) ≤ t + 1 := by
  by_cases hS : j ≤ 2 * S
  · have hzero : j - (2 * S + 1) = 0 := by omega
    rw [hzero]
    simp
  · by_contra h
    push Not at h
    have ht : t < 2 ^ (j - (2 * S + 1)) := by omega
    have hlen : (Nat.bits t).length ≤ j - (2 * S + 1) := length_natBits_lt_pow ht
    have hmj : m - j + j = m := Nat.sub_add_cancel hjm
    omega

/-- Twice a logarithmic slack term plus one is again a logarithmic slack term, with
constant `2 * C + 1`. -/
theorem two_mul_logSlack_add_one_le (C m : ℕ) :
    2 * logSlack C m + 1 ≤ logSlack (2 * C + 1) m := by
  unfold logSlack
  calc
    2 * (C * (Nat.bits m).length + C) + 1 = 2 * C * (Nat.bits m).length + 2 * C + 1 := by ring
    _ ≤ 2 * C * (Nat.bits m).length + (Nat.bits m).length + 2 * C + 1 := by omega
    _ = (2 * C + 1) * (Nat.bits m).length + (2 * C + 1) := by ring

/-- Absorbing an additive constant into logarithmic slack when the constants satisfy
`B + A ≤ C`. -/
private theorem logSlack_add_const_le_of_add_le (A B C m : ℕ) (h : B + A ≤ C) :
    A + logSlack B m ≤ logSlack C m := by
  have hB : B ≤ C := by omega
  unfold logSlack
  calc
    A + (B * (Nat.bits m).length + B) = B * (Nat.bits m).length + (B + A) := by ring
    _ ≤ C * (Nat.bits m).length + C :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hB) h

/-- Lower bound on `t + 1` in terms of `2 ^ (j - logSlack C m)` given standard coding bounds. -/
private theorem pow_sub_logSlack_le_add_one
    {m j k t Ccoding Cplain C : ℕ}
    (hjm : j ≤ m)
    (hcoding : m ≤ k + (Nat.bits t).length + logSlack Ccoding m)
    (hkUpper : k ≤ m - j + logSlack Cplain m)
    (hC : 2 * (Ccoding + Cplain) + 1 ≤ C) :
    2 ^ (j - logSlack C m) ≤ t + 1 := by
  let D := Ccoding + Cplain
  have hDcoding : logSlack Ccoding m ≤ logSlack D m :=
    logSlack_mono_left (by dsimp [D]; omega) m
  have hDplain : logSlack Cplain m ≤ logSlack D m :=
    logSlack_mono_left (by dsimp [D]; omega) m
  have hrecD : m ≤ k + (Nat.bits t).length + logSlack D m := by omega
  have hkD : k ≤ m - j + logSlack D m := by omega
  have hpow := pow_sub_two_mul_le_add_one hjm hrecD hkD
  have htwo := two_mul_logSlack_add_one_le D m
  have htailSlack : 2 * logSlack D m + 1 ≤ logSlack C m :=
    htwo.trans (logSlack_mono_left hC m)
  have hsub : j - logSlack C m ≤ j - (2 * logSlack D m + 1) := by omega
  exact (Nat.pow_le_pow_right (by norm_num) hsub).trans hpow

/-- Proposition `prop:std-pos`.  For every genuine standard block containing
`x`, both its source-facing plain complexity and its profile-facing prefix
set-complexity are `m-j` up to a uniform logarithmic slack.  The inclusive
number of elements following the block is `2^(j+O(log m))`. -/
theorem prop_std_pos (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m j : ℕ) (x : BitString),
      (hx : x ∈ standardBlock c m j x) →
      let hA : (standardBlock c m j x).Nonempty := ⟨x, hx⟩
      ((m - j : ℕ) : ENat) ≤
          plainK V
            (codedUniformOn (standardBlock c m j x) hA).code +
            (logSlack C m : ENat) ∧
      plainK V
          (codedUniformOn (standardBlock c m j x) hA).code ≤
            ((m - j + logSlack C m : ℕ) : ENat) ∧
      ((m - j : ℕ) : ENat) ≤
          setComplexity U (standardBlock c m j x) hA +
            (logSlack C m : ENat) ∧
      setComplexity U (standardBlock c m j x) hA ≤
          ((m - j + logSlack C m : ℕ) : ENat) ∧
      2 ^ (j - logSlack C m) ≤ standardBlockTail c m j + 1 ∧
      standardBlockTail c m j + 1 ≤ 2 ^ j := by
  obtain ⟨Ccoding, hcoding⟩ :=
    standardBlock_omega_coding_bound V hV c hc
  obtain ⟨Cplain, hplain⟩ :=
    plainK_standardBlock_upper V hV c hc
  obtain ⟨Cset, hset⟩ :=
    setComplexity_standardBlock_upper U hU c
  obtain ⟨Cbridge, hbridge⟩ :=
    plain_le_prefix V U hV hU.isPrefixDecompressor
  let C := 2 * (Ccoding + Cplain) + 1 + Cset + Cbridge
  refine ⟨C, fun m j x hx => ?_⟩
  intro hA
  let BCode :=
    (codedUniformOn (standardBlock c m j x) hA).code
  have hplainUpper := hplain m j x hx
  change plainK V BCode ≤
    ((m - j + logSlack Cplain m : ℕ) : ENat)
      at hplainUpper
  have hfinite : plainK V BCode ≠ ⊤ := by
    intro htop
    rw [htop] at hplainUpper
    exact ENat.natCast_ne_top _ (top_le_iff.mp hplainUpper)
  obtain ⟨k, hkRaw⟩ :=
    ENat.ne_top_iff_exists.mp hfinite
  have hk : plainK V BCode = (k : ENat) := hkRaw.symm
  have hcodingNat :
      m ≤ k +
        (Nat.bits (standardBlockTail c m j)).length +
        logSlack Ccoding m := by
    have h := hcoding m j x hx
    change (m : ENat) ≤
      plainK V BCode +
        ((Nat.bits
          (standardBlockTail c m j)).length : ENat) +
        (logSlack Ccoding m : ENat) at h
    rw [hk] at h
    exact_mod_cast h
  have hkUpperNat :
      k ≤ m - j + logSlack Cplain m := by
    rw [hk] at hplainUpper
    exact_mod_cast hplainUpper
  have hCcoding :
      logSlack Ccoding m ≤ logSlack C m :=
    logSlack_mono_left (by dsimp [C]; omega) m
  have hCplain :
      logSlack Cplain m ≤ logSlack C m :=
    logSlack_mono_left (by dsimp [C]; omega) m
  have hCset :
      logSlack Cset m ≤ logSlack C m :=
    logSlack_mono_left (by dsimp [C]; omega) m
  have hCcodingNat' : m - j ≤ k + logSlack Ccoding m := by
    have htailLt := standardBlockTail_add_one_le c m j
    have htailBits : (Nat.bits (standardBlockTail c m j)).length ≤ j :=
      length_natBits_lt_pow (by omega)
    omega
  have hLowerPlain :
      ((m - j : ℕ) : ENat) ≤
        plainK V BCode + (logSlack C m : ENat) := by
    rw [hk]
    exact_mod_cast (show m - j ≤ k + logSlack C m by omega)
  have hUpperPlain :
      plainK V BCode ≤
        ((m - j + logSlack C m : ℕ) : ENat) :=
    hplainUpper.trans
      (by exact_mod_cast Nat.add_le_add_left hCplain (m - j))
  have hLowerSet :
      ((m - j : ℕ) : ENat) ≤
        setComplexity U
          (standardBlock c m j x) hA +
          (logSlack C m : ENat) := by
    have hb := hbridge BCode
    change plainK V BCode ≤
      setComplexity U
        (standardBlock c m j x) hA +
        (Cbridge : ENat) at hb
    have habsorb :
        Cbridge + logSlack Ccoding m ≤ logSlack C m :=
      logSlack_add_const_le_of_add_le Cbridge Ccoding C m (by dsimp [C]; omega)
    calc
      ((m - j : ℕ) : ENat)
          ≤ plainK V BCode +
              (logSlack Ccoding m : ENat) := by
        rw [hk]
        exact_mod_cast hCcodingNat'
      _ ≤ (setComplexity U
            (standardBlock c m j x) hA +
              (Cbridge : ENat)) +
            (logSlack Ccoding m : ENat) := by gcongr
      _ ≤ setComplexity U
            (standardBlock c m j x) hA +
            (logSlack C m : ENat) := by
        rw [add_assoc]
        gcongr
        exact_mod_cast habsorb
  have hUpperSet :
      setComplexity U
          (standardBlock c m j x) hA ≤
        ((m - j + logSlack C m : ℕ) : ENat) :=
    (hset m j x hx).trans
      (by exact_mod_cast Nat.add_le_add_left hCset (m - j))
  have hLowerTail :
      2 ^ (j - logSlack C m) ≤
        standardBlockTail c m j + 1 :=
    pow_sub_logSlack_le_add_one
      (standardBlock_exponent_le c m j x hx)
      hcodingNat hkUpperNat (by dsimp [C]; omega)
  exact ⟨hLowerPlain, hUpperPlain, hLowerSet,
    hUpperSet, hLowerTail,
    standardBlockTail_add_one_le c m j⟩

/-- The members of `A` of length exactly `n`. -/
def lengthFilteredModel
    (A : Finset BitString) (n : ℕ) : Finset BitString :=
  A.filter (fun y => y.length = n)

/-- From the pair of a model code and a length, the canonical uniform code of the
members of that length. -/
def lengthFilterUniformCode (s : BitString) : BitString :=
  let w := decodeFirst s
  let n := bitsToNat (decodeSecond s)
  let points :=
    ((decodeDistributionData w).map
      CodedDistributionEntry.point).filter
        (fun y => decide (y.length = n))
  let L := canonicalFinsetList points.toFinset
  codedDistributionDataCode (L.map fun y =>
    { point := y,
      mass := ratMassInvNat (max 1 L.length) (by positivity) })

/-- The length filter on codes is computable. -/
theorem lengthFilterUniformCode_computable :
    Computable lengthFilterUniformCode := by
  unfold lengthFilterUniformCode
  have hlen : Primrec (fun q : BitString × BitString => q.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hn : Primrec (fun q : BitString × BitString => bitsToNat (decodeSecond q.1)) :=
    bitsToNat_primrec.comp (decodeSecond_primrec.comp Primrec.fst)
  have h_filter : Primrec₂ (fun s y : BitString =>
      decide (y.length = bitsToNat (decodeSecond s))) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.eq hlen hn)
  have h_map : Primrec (fun s =>
      List.map CodedDistributionEntry.point (decodeDistributionData (decodeFirst s))) :=
    Primrec.list_map (decodeDistributionData_primrec.comp decodeFirst_primrec)
      (entry_point_primrec.comp Primrec.snd).to₂
  have h_list : Primrec (fun s => canonicalFinsetList (List.toFinset
      (List.filter (fun y => decide (y.length = bitsToNat (decodeSecond s)))
        (List.map CodedDistributionEntry.point
          (decodeDistributionData (decodeFirst s)))))) :=
    canonicalFinsetList_toFinset_primrec.comp (list_filter_primrec h_map h_filter)
  exact (Primrec.comp codedUniformEncoder_primrec h_list).to_comp

/-- On the canonical code of `A` and a length attained in `A`, the filter returns
the canonical code of `lengthFilteredModel A n`. -/
theorem lengthFilterUniformCode_eq
    (A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) (n : ℕ)
    (hx : x ∈ A) (hxn : x.length = n) :
    lengthFilterUniformCode
        (pairCode (codedUniformOn A hA).code (Nat.bits n)) =
      (codedUniformOn (lengthFilteredModel A n)
        ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩).code := by
  let B := lengthFilteredModel A n
  let hB : B.Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩
  have hpoints :
      (((decodeDistributionData
          (codedUniformOn A hA).code).map
          CodedDistributionEntry.point).filter
            (fun y => decide (y.length = n))).toFinset = B := by
    rw [dataPoints_codedUniformOn]
    ext y
    simp [B, lengthFilteredModel]
  unfold lengthFilterUniformCode
  simp only [decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]
  let S :=
    (((decodeDistributionData
        (codedUniformOn A hA).code).map
        CodedDistributionEntry.point).filter
          (fun y => decide (y.length = n))).toFinset
  let hS : S.Nonempty := by
    dsimp [S]
    rw [hpoints]
    exact hB
  change
    codedDistributionDataCode
        ((canonicalFinsetList S).map fun y =>
          { point := y,
            mass := ratMassInvNat
              (max 1 (canonicalFinsetList S).length)
              (by positivity) }) =
      (codedUniformOn B hB).code
  calc
    _ = (codedUniformOn S hS).code := by
      rw [codedUniformOn_code_eq S hS]
      have hcard :
          max 1 (canonicalFinsetList S).length = S.card := by
        rw [length_canonicalFinsetList]
        exact max_eq_right
          (Finset.one_le_card.mpr hS)
      apply congrArg codedDistributionDataCode
      apply List.map_congr_left
      intro y _
      apply congrArg (fun mass =>
        ({ point := y, mass := mass } :
          CodedDistributionEntry))
      apply RatMass.code_injective
      simp only [RatMass.code, ratMassInvNat, hcard]
    _ = (codedUniformOn B hB).code :=
      codedUniformOn_code_congr hS hB hpoints

/-- The length filter as a partial map on codes. -/
noncomputable def lengthFilterUniformCodeSelector :
    BitString →. BitString := fun s =>
  Part.some (lengthFilterUniformCode s)

/-- The length-filter selector is partial recursive. -/
theorem lengthFilterUniformCodeSelector_partrec :
    Partrec lengthFilterUniformCodeSelector := by
  exact lengthFilterUniformCode_computable.partrec

/-- The selector outputs the canonical code of the length-filtered model. -/
theorem lengthFilterUniformCodeSelector_recovers
    (A : Finset BitString) (hA : A.Nonempty)
    (x : BitString) (n : ℕ)
    (hx : x ∈ A) (hxn : x.length = n) :
    (codedUniformOn (lengthFilteredModel A n)
      ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩).code ∈
      lengthFilterUniformCodeSelector
        (pairCode (codedUniformOn A hA).code (Nat.bits n)) := by
  unfold lengthFilterUniformCodeSelector
  rw [lengthFilterUniformCode_eq A hA x n hx hxn]
  exact Part.mem_some _

/-- Restricting a model to its length-`n` members costs at most logarithmic slack in
set complexity. -/
theorem setComplexity_lengthFilteredModel_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C, ∀ A hA x n (hx : x ∈ A) (hxn : x.length = n),
      setComplexity U (lengthFilteredModel A n)
          ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩ ≤
        setComplexity U A hA + (logSlack C n : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    KPPlain_map_le U hU lengthFilterUniformCode
      lengthFilterUniformCode_computable
  obtain ⟨Cpair, hpair⟩ :=
    KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨Clen, hlen⟩ :=
    KPPlain_le_two_mul_length U hU
  let C := Cmap + Cpair + Clen + 3
  refine ⟨C, fun A hA x n hx hxn => ?_⟩
  let hB : (lengthFilteredModel A n).Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨hx, hxn⟩⟩
  have heq :=
    lengthFilterUniformCode_eq A hA x n hx hxn
  have hbits :
      KPPlain U (Nat.bits n) ≤
        ((2 * (Nat.bits n).length + Clen : ℕ) : ENat) := by
    have h_len := hlen (Nat.bits n)
    exact h_len.trans (by push_cast; rfl)
  calc
    setComplexity U (lengthFilteredModel A n) hB =
        KPPlain U
          (lengthFilterUniformCode
            (pairCode (codedUniformOn A hA).code
              (Nat.bits n))) := by
      unfold setComplexity
      rw [heq]
    _ ≤ KPPlain U
          (pairCode (codedUniformOn A hA).code
            (Nat.bits n)) + (Cmap : ENat) :=
      hmap _
    _ = KPPair U (codedUniformOn A hA).code
          (Nat.bits n) + (Cmap : ENat) := rfl
    _ ≤ (KPPlain U (codedUniformOn A hA).code +
          KPPlain U (Nat.bits n) + (Cpair : ENat)) +
          (Cmap : ENat) := by
      gcongr
      exact hpair _ _
    _ ≤ (setComplexity U A hA +
          ((2 * (Nat.bits n).length + Clen : ℕ) : ENat) +
          (Cpair : ENat)) + (Cmap : ENat) := by
      change
        (KPPlain U (codedUniformOn A hA).code +
            KPPlain U (Nat.bits n) + (Cpair : ENat)) +
            (Cmap : ENat) ≤
          (KPPlain U (codedUniformOn A hA).code +
            ((2 * (Nat.bits n).length + Clen : ℕ) : ENat) +
            (Cpair : ENat)) + (Cmap : ENat)
      have hbase :=
        add_le_add
          (le_refl
            (KPPlain U (codedUniformOn A hA).code))
          hbits
      have hpair' :=
        add_le_add_right hbase (Cpair : ENat)
      have hmap' :=
        add_le_add_right hpair' (Cmap : ENat)
      calc
        (KPPlain U (codedUniformOn A hA).code +
            KPPlain U (Nat.bits n) + (Cpair : ENat)) +
            (Cmap : ENat) =
          (Cmap : ENat) + ((Cpair : ENat) +
            (KPPlain U (codedUniformOn A hA).code +
              KPPlain U (Nat.bits n))) := by abel
        _ ≤ (Cmap : ENat) + ((Cpair : ENat) +
            (KPPlain U (codedUniformOn A hA).code +
              ((2 * (Nat.bits n).length + Clen : ℕ) :
                ENat))) := hmap'
        _ = (KPPlain U (codedUniformOn A hA).code +
            ((2 * (Nat.bits n).length + Clen : ℕ) : ENat) +
            (Cpair : ENat)) + (Cmap : ENat) := by abel
    _ = setComplexity U A hA +
          ((2 * (Nat.bits n).length + Clen + Cpair +
            Cmap : ℕ) : ENat) := by
      push_cast
      abel
    _ ≤ setComplexity U A hA +
          (logSlack C n : ENat) := by
      gcongr
      exact_mod_cast (show
        2 * (Nat.bits n).length + Clen + Cpair + Cmap
          ≤ logSlack C n by
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits n).length)])

/-- A member of a source-standard block has inclusive suffix coordinate strictly
below the size of two adjacent blocks. -/
theorem suffixCoordinate_lt_pow_succ_standardBlock
    (c : Code) (m r : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m r x) :
    suffixCoordinate c m x < 2 ^ (r + 1) := by
  -- Get the testBit condition from membership
  have hbit := standardBlock_testBit_of_mem c m r x hx
  -- x is in completedBoundedOutput
  have hxList : x ∈ completedBoundedOutput c m :=
    mem_completedBoundedOutput_of_mem_standardBlock c m r x hx
  -- The list is nodup
  have hnodup : (completedBoundedOutput c m).Nodup :=
    boundedOutputStage_nodup c m (maxHaltingStage c m)
  -- Let's set up the notation used in the proof
  let L := completedBoundedOutput c m
  let start := omegaCount c m / 2 ^ (r + 1) * 2 ^ (r + 1)
  let p := 2 ^ r
  -- Unfold standardBlock to get the structural information
  unfold standardBlock at hx
  rw [if_pos hbit, List.mem_toFinset] at hx
  -- x is in (L.drop start).take p
  -- Get the index of x in L
  let idx := L.idxOf x
  have hidx_lt : idx < L.length := List.idxOf_lt_length_of_mem hxList
  -- x is in (L.drop start).take p
  -- x is in (L.drop start).take p
  -- x is in (L.drop start).take p
  have hx_take : x ∈ (L.drop start).take p := hx
  -- Get k and the bounds without destroying hx_take
  have ⟨k, hk, hkx⟩ := List.mem_take_iff_getElem.mp hx_take
  -- k < p
  have hk_lt_p : k < p := Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)
  -- x is in L.drop start
  have hx_drop : x ∈ L.drop start := List.mem_of_mem_take hx_take
  -- x is in L.drop start |>.take p, so its index satisfies start ≤ idx < start + p
  have hidx_bounds : start ≤ idx ∧ idx < start + p := by
    have hglobal : start + k < L.length := by
      simp only [List.length_drop] at hk
      omega
    have hidx_eq : idx = start + k := by
      have := hnodup.idxOf_getElem (start + k) hglobal
      simp only [List.getElem_drop] at hkx
      rwa [hkx] at this
    exact ⟨by omega, by omega⟩
  -- suffixCoordinate c m x = suffixCountIncluding L x
  unfold suffixCoordinate
  -- For a nodup list, suffixCountIncluding L x = L.length - idx
  have hsuff : suffixCountIncluding L x = L.length - idx := by
    have h1 := findIdx_add_suffixCountIncluding_eq_length L x hxList
    have h2 : L.findIdx (· == x) = idx := by
      have : L.findIdx (· == x) = L.findIdx (fun y => decide (y = x)) := by
        congr 1; funext y; simp [Bool.beq_eq_decide_eq]
      rw [this, findIdx_decide_eq_eq_idxOf]
    rw [h2] at h1
    omega
  rw [hsuff]
  -- L.length = omegaCount c m
  have hlen : L.length = omegaCount c m := rfl
  rw [hlen]
  -- Since idx ≥ start, omegaCount c m - idx ≤ omegaCount c m - start
  have hle : omegaCount c m - idx < 2 ^ (r + 1) := by
    have hlt : omegaCount c m - start < 2 ^ (r + 1) := by
      unfold start
      have hmod :
          omegaCount c m -
              omegaCount c m / 2 ^ (r + 1) * 2 ^ (r + 1) =
            omegaCount c m % 2 ^ (r + 1) := by
        have := Nat.mod_add_div (omegaCount c m) (2 ^ (r + 1))
        rw [mul_comm] at this
        omega
      rw [hmod]
      exact Nat.mod_lt _ (by norm_num : 0 < 2 ^ (r + 1))
    exact lt_of_le_of_lt (Nat.sub_le_sub_left hidx_bounds.1 _) hlt
  exact hle

/-- Comparing a suffix-coordinate lower bound with the geometry of a
source-standard block bounds the block's complexity gap. -/
theorem standardBlock_gap_le_of_suffix_lower
    (c : Code) (m r q S : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m r x)
    (hsuffix :
      2 ^ (m - q - S) ≤ suffixCoordinate c m x) :
    m - r ≤ q + S := by
  have h1 := suffixCoordinate_lt_pow_succ_standardBlock c m r x hx
  have h2 : 2 ^ (m - q - S) < 2 ^ (r + 1) := lt_of_le_of_lt hsuffix h1
  have h3 : m - q - S < r + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

end Kolmogorov
