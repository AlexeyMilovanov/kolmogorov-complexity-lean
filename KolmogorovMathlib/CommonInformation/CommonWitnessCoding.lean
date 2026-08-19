import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# Coefficient-one common-witness coding

This file starts the coding layer needed for SUV Theorem 225.  Each raw
program occurs exactly once.  Only the two split positions are encoded
self-delimitingly.
-/

namespace Kolmogorov

/-- Code two raw programs, recording only the length of the first. -/
def commonWitnessOneProgramCode (p q : BitString) : BitString :=
  pairCode (Nat.bits p.length) (p ++ q)

/-- Code three raw programs, recording the lengths of the first two. -/
def commonWitnessPairProgramCode (p q r : BitString) : BitString :=
  pairCode
    (pairCode (Nat.bits p.length) (Nat.bits q.length))
    (p ++ q ++ r)

/-- Run the first raw program without a condition and feed its output as the
condition to the second raw program. -/
def commonWitnessOneProgramMap (V : Map) : Map := fun input =>
  let body := decodeSecond input.1
  let pLength := decodeBits (decodeFirst input.1)
  let p := body.take pLength
  let q := body.drop pLength
  (V (p, [])).bind fun z => V (q, z)

/-- Run one unconditional program and two conditional programs using the
identical recovered witness, then return the canonical pair of their outputs. -/
def commonWitnessPairProgramMap (V : Map) : Map := fun input =>
  let lengths := decodeFirst input.1
  let body := decodeSecond input.1
  let pLength := decodeBits (decodeFirst lengths)
  let qLength := decodeBits (decodeSecond lengths)
  let p := body.take pLength
  let rest := body.drop pLength
  let q := rest.take qLength
  let r := rest.drop qLength
  (V (p, [])).bind fun z =>
    (V (q, z)).bind fun x =>
      (V (r, z)).map fun y => pairCode x y

theorem commonWitnessOneProgramCode_length_le :
    ∃ c, ∀ p q : BitString,
      (commonWitnessOneProgramCode p q).length ≤
        p.length + q.length +
          logSlack c (p.length + q.length + 1) := by
  refine ⟨2, fun p q => ?_⟩
  have hBits :
      (Nat.bits p.length).length ≤
        (Nat.bits (p.length + q.length + 1)).length :=
    length_natBits_mono (by omega)
  simp only [commonWitnessOneProgramCode, length_pairCode,
    List.length_append, logSlack]
  omega

theorem commonWitnessPairProgramCode_length_le :
    ∃ c, ∀ p q r : BitString,
      (commonWitnessPairProgramCode p q r).length ≤
        p.length + q.length + r.length +
          logSlack c (p.length + q.length + r.length + 1) := by
  refine ⟨6, fun p q r => ?_⟩
  have hPBits :
      (Nat.bits p.length).length ≤
        (Nat.bits (p.length + q.length + r.length + 1)).length :=
    length_natBits_mono (by omega)
  have hQBits :
      (Nat.bits q.length).length ≤
        (Nat.bits (p.length + q.length + r.length + 1)).length :=
    length_natBits_mono (by omega)
  simp only [commonWitnessPairProgramCode, length_pairCode,
    List.length_append, logSlack]
  omega

theorem commonWitnessOneProgramMap_produces
    {V : Map} {p q z x : BitString}
    (hp : produces V p [] z) (hq : produces V q z x) :
    produces (commonWitnessOneProgramMap V)
      (commonWitnessOneProgramCode p q) [] x := by
  unfold commonWitnessOneProgramMap commonWitnessOneProgramCode produces
  simp only [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits,
    List.take_left, List.drop_left, Part.mem_bind_iff]
  exact ⟨z, hp, hq⟩

theorem commonWitnessPairProgramMap_produces
    {V : Map} {p q r z x y : BitString}
    (hp : produces V p [] z)
    (hq : produces V q z x)
    (hr : produces V r z y) :
    produces (commonWitnessPairProgramMap V)
      (commonWitnessPairProgramCode p q r) [] (pairCode x y) := by
  unfold commonWitnessPairProgramMap commonWitnessPairProgramCode produces
  simp only [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits]
  rw [List.append_assoc]
  simp only [List.take_left, List.drop_left, Part.mem_bind_iff,
    Part.mem_map_iff]
  exact ⟨z, hp, x, hq, y, hr, rfl⟩

theorem commonWitnessOneProgramMap_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (commonWitnessOneProgramMap V) := by
  have hBody : Computable (fun input : BitString × BitString =>
      decodeSecond input.1) :=
    decodeSecond_computable.comp Computable.fst
  have hLength : Computable (fun input : BitString × BitString =>
      decodeBits (decodeFirst input.1)) :=
    decodeBitsComputable.comp
      (decodeFirst_computable.comp Computable.fst)
  have hP : Computable (fun input : BitString × BitString =>
      (decodeSecond input.1).take
        (decodeBits (decodeFirst input.1))) :=
    Primrec.list_take.to_comp.comp hLength hBody
  have hQ : Computable (fun input : BitString × BitString =>
      (decodeSecond input.1).drop
        (decodeBits (decodeFirst input.1))) :=
    Primrec.list_drop.to_comp.comp hLength hBody
  have hRunP : Partrec (fun input : BitString × BitString =>
      V ((decodeSecond input.1).take
        (decodeBits (decodeFirst input.1)), [])) :=
    Partrec.comp hV
      (Computable.pair hP (Computable.const []))
  have hRunQ : Partrec
      (fun state : (BitString × BitString) × BitString =>
        V ((decodeSecond state.1.1).drop
          (decodeBits (decodeFirst state.1.1)), state.2)) :=
    Partrec.comp hV
      (Computable.pair (hQ.comp Computable.fst) Computable.snd)
  unfold commonWitnessOneProgramMap
  exact Partrec.bind hRunP hRunQ.to₂

theorem commonWitnessPairProgramMap_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (commonWitnessPairProgramMap V) := by
  have hLengths : Computable (fun input : BitString × BitString =>
      decodeFirst input.1) :=
    decodeFirst_computable.comp Computable.fst
  have hBody : Computable (fun input : BitString × BitString =>
      decodeSecond input.1) :=
    decodeSecond_computable.comp Computable.fst
  have hPLength : Computable (fun input : BitString × BitString =>
      decodeBits (decodeFirst (decodeFirst input.1))) :=
    decodeBitsComputable.comp
      (decodeFirst_computable.comp hLengths)
  have hQLength : Computable (fun input : BitString × BitString =>
      decodeBits (decodeSecond (decodeFirst input.1))) :=
    decodeBitsComputable.comp
      (decodeSecond_computable.comp hLengths)
  have hP : Computable (fun input : BitString × BitString =>
      (decodeSecond input.1).take
        (decodeBits (decodeFirst (decodeFirst input.1)))) :=
    Primrec.list_take.to_comp.comp hPLength hBody
  have hRest : Computable (fun input : BitString × BitString =>
      (decodeSecond input.1).drop
        (decodeBits (decodeFirst (decodeFirst input.1)))) :=
    Primrec.list_drop.to_comp.comp hPLength hBody
  have hQ : Computable (fun input : BitString × BitString =>
      ((decodeSecond input.1).drop
        (decodeBits (decodeFirst (decodeFirst input.1)))).take
          (decodeBits (decodeSecond (decodeFirst input.1)))) :=
    Primrec.list_take.to_comp.comp hQLength hRest
  have hR : Computable (fun input : BitString × BitString =>
      ((decodeSecond input.1).drop
        (decodeBits (decodeFirst (decodeFirst input.1)))).drop
          (decodeBits (decodeSecond (decodeFirst input.1)))) :=
    Primrec.list_drop.to_comp.comp hQLength hRest
  have hRunP : Partrec (fun input : BitString × BitString =>
      V ((decodeSecond input.1).take
        (decodeBits (decodeFirst (decodeFirst input.1))), [])) :=
    Partrec.comp hV
      (Computable.pair hP (Computable.const []))
  have hRunQ : Partrec
      (fun state : (BitString × BitString) × BitString =>
        V (((decodeSecond state.1.1).drop
          (decodeBits (decodeFirst (decodeFirst state.1.1)))).take
            (decodeBits (decodeSecond (decodeFirst state.1.1))),
          state.2)) :=
    Partrec.comp hV
      (Computable.pair (hQ.comp Computable.fst) Computable.snd)
  have hRunR : Partrec
      (fun state :
          ((BitString × BitString) × BitString) × BitString =>
        V (((decodeSecond state.1.1.1).drop
          (decodeBits (decodeFirst (decodeFirst state.1.1.1)))).drop
            (decodeBits (decodeSecond (decodeFirst state.1.1.1))),
          state.1.2)) :=
    Partrec.comp hV
      (Computable.pair
        (hR.comp (Computable.fst.comp Computable.fst))
        (Computable.snd.comp Computable.fst))
  have hPair : Computable
      (fun state :
          (((BitString × BitString) × BitString) × BitString) ×
            BitString =>
        pairCode state.1.2 state.2) :=
    (show Computable₂ (fun x y : BitString => pairCode x y) from
      pairCode_computable).comp
      (Computable.snd.comp Computable.fst) Computable.snd
  have hRunPair : Partrec
      (fun state :
          ((BitString × BitString) × BitString) × BitString =>
        (V (((decodeSecond state.1.1.1).drop
          (decodeBits (decodeFirst (decodeFirst state.1.1.1)))).drop
            (decodeBits (decodeSecond (decodeFirst state.1.1.1))),
          state.1.2)).map fun y => pairCode state.2 y) :=
    Partrec.map hRunR hPair
  have hAfterQ : Partrec
      (fun state : (BitString × BitString) × BitString =>
        (V (((decodeSecond state.1.1).drop
          (decodeBits (decodeFirst (decodeFirst state.1.1)))).take
            (decodeBits (decodeSecond (decodeFirst state.1.1))),
          state.2)).bind fun x =>
            (V (((decodeSecond state.1.1).drop
              (decodeBits (decodeFirst (decodeFirst state.1.1)))).drop
                (decodeBits (decodeSecond (decodeFirst state.1.1))),
              state.2)).map fun y => pairCode x y) :=
    Partrec.bind hRunQ hRunPair.to₂
  unfold commonWitnessPairProgramMap
  exact Partrec.bind hRunP hAfterQ.to₂

theorem plainK_output_from_commonPrograms_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p q z x : BitString,
      produces V p [] z →
      produces V q z x →
      plainK V x ≤
        ((p.length + q.length +
          logSlack c (p.length + q.length + 1) : Nat) : ENat) := by
  obtain ⟨cLength, hLength⟩ :=
    commonWitnessOneProgramCode_length_le
  obtain ⟨cMap, hMap⟩ :=
    hV.2 (commonWitnessOneProgramMap V)
      (commonWitnessOneProgramMap_partrec V hV.1)
  let C := cLength + cMap
  refine ⟨C, fun p q z x hp hq => ?_⟩
  have hProduced :=
    commonWitnessOneProgramMap_produces hp hq
  have hCode :
      plainK (commonWitnessOneProgramMap V) x ≤
        ((commonWitnessOneProgramCode p q).length : ENat) := by
    apply sInf_le
    exact ⟨commonWitnessOneProgramCode p q, hProduced, rfl⟩
  have hSlack :
      logSlack cLength (p.length + q.length + 1) + cMap ≤
        logSlack C (p.length + q.length + 1) := by
    simp only [C, logSlack]
    nlinarith [Nat.zero_le
      (Nat.bits (p.length + q.length + 1)).length]
  calc
    plainK V x ≤
        plainK (commonWitnessOneProgramMap V) x + (cMap : ENat) :=
      hMap x []
    _ ≤ ((commonWitnessOneProgramCode p q).length : ENat) +
        (cMap : ENat) := by gcongr
    _ ≤ ((p.length + q.length +
          logSlack cLength (p.length + q.length + 1) : Nat) : ENat) +
        (cMap : ENat) := by
      gcongr
      exact_mod_cast hLength p q
    _ ≤ ((p.length + q.length +
          logSlack C (p.length + q.length + 1) : Nat) : ENat) := by
      exact_mod_cast (by omega :
        p.length + q.length +
            logSlack cLength (p.length + q.length + 1) + cMap ≤
          p.length + q.length +
            logSlack C (p.length + q.length + 1))

theorem pairPlainK_output_from_commonPrograms_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ p q r z x y : BitString,
      produces V p [] z →
      produces V q z x →
      produces V r z y →
      pairPlainK V x y ≤
        ((p.length + q.length + r.length +
          logSlack c
            (p.length + q.length + r.length + 1) : Nat) : ENat) := by
  obtain ⟨cLength, hLength⟩ :=
    commonWitnessPairProgramCode_length_le
  obtain ⟨cMap, hMap⟩ :=
    hV.2 (commonWitnessPairProgramMap V)
      (commonWitnessPairProgramMap_partrec V hV.1)
  let C := cLength + cMap
  refine ⟨C, fun p q r z x y hp hq hr => ?_⟩
  have hProduced :=
    commonWitnessPairProgramMap_produces hp hq hr
  have hCode :
      plainK (commonWitnessPairProgramMap V) (pairCode x y) ≤
        ((commonWitnessPairProgramCode p q r).length : ENat) := by
    apply sInf_le
    exact ⟨commonWitnessPairProgramCode p q r, hProduced, rfl⟩
  have hSlack :
      logSlack cLength (p.length + q.length + r.length + 1) + cMap ≤
        logSlack C (p.length + q.length + r.length + 1) := by
    simp only [C, logSlack]
    nlinarith [Nat.zero_le
      (Nat.bits (p.length + q.length + r.length + 1)).length]
  calc
    pairPlainK V x y = plainK V (pairCode x y) := rfl
    _ ≤ plainK (commonWitnessPairProgramMap V) (pairCode x y) +
        (cMap : ENat) := hMap (pairCode x y) []
    _ ≤ ((commonWitnessPairProgramCode p q r).length : ENat) +
        (cMap : ENat) := by gcongr
    _ ≤ ((p.length + q.length + r.length +
          logSlack cLength
            (p.length + q.length + r.length + 1) : Nat) : ENat) +
        (cMap : ENat) := by
      gcongr
      exact_mod_cast hLength p q r
    _ ≤ ((p.length + q.length + r.length +
          logSlack C
            (p.length + q.length + r.length + 1) : Nat) : ENat) := by
      exact_mod_cast (by omega :
        p.length + q.length + r.length +
            logSlack cLength
              (p.length + q.length + r.length + 1) + cMap ≤
          p.length + q.length + r.length +
            logSlack C
              (p.length + q.length + r.length + 1))

/-- Value-level one-output common-witness inequality, using actual minimizing
programs for both finite complexity values. -/
theorem plainK_le_commonWitness_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ z x : BitString, ∀ kz kxz kx : Nat,
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V x z kxz →
      HasPlainComplexityValue V x kx →
      kx ≤ kz + kxz + logSlack c (kz + kxz + 1) := by
  obtain ⟨c, hc⟩ :=
    plainK_output_from_commonPrograms_le V hV
  refine ⟨c, fun z x kz kxz kx hz hxz hx => ?_⟩
  obtain ⟨p, hp, hpLength⟩ := hz.exists_program
  obtain ⟨q, hq, hqLength⟩ := hxz.exists_program
  have h := hc p q z x hp hq
  rw [hx, hpLength, hqLength] at h
  exact_mod_cast h

/-- Value-level joint common-witness inequality with coefficient one on all
three shortest-program lengths. -/
theorem pairPlainK_le_commonWitness_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ z x y : BitString,
      ∀ kz kxz kyz kxy : Nat,
        HasPlainComplexityValue V z kz →
        HasPlainConditionalComplexityValue V x z kxz →
        HasPlainConditionalComplexityValue V y z kyz →
        HasPlainComplexityValue V (pairCode x y) kxy →
        kxy ≤ kz + kxz + kyz +
          logSlack c (kz + kxz + kyz + 1) := by
  obtain ⟨c, hc⟩ :=
    pairPlainK_output_from_commonPrograms_le V hV
  refine ⟨c, fun z x y kz kxz kyz kxy hz hxz hyz hxy => ?_⟩
  obtain ⟨p, hp, hpLength⟩ := hz.exists_program
  obtain ⟨q, hq, hqLength⟩ := hxz.exists_program
  obtain ⟨r, hr, hrLength⟩ := hyz.exists_program
  have h := hc p q r z x y hp hq hr
  rw [pairPlainK, hxy, hpLength, hqLength, hrLength] at h
  exact_mod_cast h

/-- The left marginal profile of every common-information triple lies above
`C(x)`, up to logarithmic coding overhead. -/
theorem commonInformationRegion_left_profile_bound_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ {x y : BitString} {t : CommonInformationTriple} {kx : Nat},
      HasPlainComplexityValue V x kx →
      t ∈ CommonInformationRegion V x y →
      kx < t.1 + t.2.1 +
        logSlack c (t.1 + t.2.1 + 1) := by
  obtain ⟨c, hc⟩ := plainK_le_commonWitness_values V hV
  refine ⟨c, ?_⟩
  intro x y t kx hx ht
  rcases ht with ⟨z, hz, hxz, _⟩
  obtain ⟨kz, hkz⟩ := exists_plainComplexityValue V hV z
  obtain ⟨kxz, hkxz⟩ :=
    exists_plainConditionalComplexityValue V hV x z
  have hzNat : kz < t.1 := by
    rw [hkz] at hz
    exact_mod_cast hz
  have hxzNat : kxz < t.2.1 := by
    rw [hkxz] at hxz
    exact_mod_cast hxz
  have hmain := hc z x kz kxz kx hkz hkxz hx
  have hslack :
      logSlack c (kz + kxz + 1) ≤
        logSlack c (t.1 + t.2.1 + 1) :=
    logSlack_mono_right c (by omega)
  omega

/-- The right marginal profile of every common-information triple lies above
`C(y)`, up to logarithmic coding overhead. -/
theorem commonInformationRegion_right_profile_bound_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ {x y : BitString} {t : CommonInformationTriple} {ky : Nat},
      HasPlainComplexityValue V y ky →
      t ∈ CommonInformationRegion V x y →
      ky < t.1 + t.2.2 +
        logSlack c (t.1 + t.2.2 + 1) := by
  obtain ⟨c, hc⟩ := plainK_le_commonWitness_values V hV
  refine ⟨c, ?_⟩
  intro x y t ky hy ht
  rcases ht with ⟨z, hz, _, hyz⟩
  obtain ⟨kz, hkz⟩ := exists_plainComplexityValue V hV z
  obtain ⟨kyz, hkyz⟩ :=
    exists_plainConditionalComplexityValue V hV y z
  have hzNat : kz < t.1 := by
    rw [hkz] at hz
    exact_mod_cast hz
  have hyzNat : kyz < t.2.2 := by
    rw [hkyz] at hyz
    exact_mod_cast hyz
  have hmain := hc z y kz kyz ky hkz hkyz hy
  have hslack :
      logSlack c (kz + kyz + 1) ≤
        logSlack c (t.1 + t.2.2 + 1) :=
    logSlack_mono_right c (by omega)
  omega

/-- The joint profile of every common-information triple lies above `C(x,y)`,
up to logarithmic coding overhead. -/
theorem commonInformationRegion_pair_profile_bound_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ {x y : BitString} {t : CommonInformationTriple} {kxy : Nat},
      HasPlainComplexityValue V (pairCode x y) kxy →
      t ∈ CommonInformationRegion V x y →
      kxy < t.1 + t.2.1 + t.2.2 +
        logSlack c (t.1 + t.2.1 + t.2.2 + 1) := by
  obtain ⟨c, hc⟩ := pairPlainK_le_commonWitness_values V hV
  refine ⟨c, ?_⟩
  intro x y t kxy hxy ht
  rcases ht with ⟨z, hz, hxz, hyz⟩
  obtain ⟨kz, hkz⟩ := exists_plainComplexityValue V hV z
  obtain ⟨kxz, hkxz⟩ :=
    exists_plainConditionalComplexityValue V hV x z
  obtain ⟨kyz, hkyz⟩ :=
    exists_plainConditionalComplexityValue V hV y z
  have hzNat : kz < t.1 := by
    rw [hkz] at hz
    exact_mod_cast hz
  have hxzNat : kxz < t.2.1 := by
    rw [hkxz] at hxz
    exact_mod_cast hxz
  have hyzNat : kyz < t.2.2 := by
    rw [hkyz] at hyz
    exact_mod_cast hyz
  have hmain := hc z x y kz kxz kyz kxy hkz hkxz hkyz hxy
  have hslack :
      logSlack c (kz + kxz + kyz + 1) ≤
        logSlack c (t.1 + t.2.1 + t.2.2 + 1) :=
    logSlack_mono_right c (by omega)
  omega

end Kolmogorov
