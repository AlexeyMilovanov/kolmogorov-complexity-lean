import KolmogorovMathlib.CommonInformation.SharedDescription
import KolmogorovMathlib.CommonInformation.Interfaces

/-!
# Common Information: extracting a literal overlap

Checked leaves for the reverse implication of the overlap conjecture.  The
geometry lemmas identify the literal overlap as a slice of each represented
block.  The complexity lemma gives the coding inequality used to compare the
complexity of that overlap with its length: the private left and right blocks
are supplied literally, while a shortest plain program supplies the middle
block.
-/

namespace Kolmogorov

/-- In the overlap case, the literal overlap is exactly the suffix of the
visible prefix beginning at position `kxy - ly`. -/
theorem literalOverlap_eq_prefix_drop
    {u : BitString} {lx ly kxy : Nat}
    (hu : u.length = kxy)
    (hlx : lx ≤ kxy) (hly : ly ≤ kxy)
    (hov : kxy ≤ lx + ly) :
    literalOverlap u lx ly =
      (u.take lx).drop (kxy - ly) := by
  let z := literalOverlap u lx ly
  obtain ⟨left, right, hfac, hleft, _hright⟩ :=
    literalOverlap_factorization hu hlx hly hov
  have hfac' : u = left ++ z ++ right := by
    simpa [z] using hfac
  have hoverlap' : z.length = lx + ly - kxy := by
    dsimp [z]
    exact
    literalOverlap_length hu hlx hly hov
  have hpref :
      (left ++ z ++ right).take lx = left ++ z := by
    have hlen :
        (left ++ z).length = lx := by
      simp only [List.length_append, hleft, hoverlap']
      omega
    rw [← hlen, List.take_left]
  change z = (u.take lx).drop (kxy - ly)
  rw [hfac', hpref, ← hleft, List.drop_left]

/-- In the overlap case, the literal overlap is exactly the corresponding
prefix of the visible suffix. -/
theorem literalOverlap_eq_suffix_take
    {u : BitString} {lx ly kxy : Nat}
    (hu : u.length = kxy) :
    literalOverlap u lx ly =
      (u.drop (kxy - ly)).take (lx + ly - kxy) := by
  unfold literalOverlap
  rw [hu]

/-- Conditional plain complexity composes through a concrete self-delimiting
pair of the two witness programs.  The first program is stored in the unary
header of `pairCode`, hence the visible `2*a + b` bound. -/
theorem condK_trans_visible_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ (x y z : BitString) (a b : Nat),
      condK V y x ≤ (a : ENat) →
      condK V z y ≤ (b : ENat) →
      condK V z x ≤ ((2 * a + b + C : Nat) : ENat) := by
  let D : Map := fun pr =>
    (V (decodeFirst pr.1, pr.2)).bind fun y =>
      V (decodeSecond pr.1, y)
  have hFirst :
      Partrec (fun pr : BitString × BitString =>
        V (decodeFirst pr.1, pr.2)) :=
    Partrec.comp hV.1
      ((decodeFirst_computable.comp Computable.fst).pair
        Computable.snd)
  have hSecond :
      Partrec (fun q : (BitString × BitString) × BitString =>
        V (decodeSecond q.1.1, q.2)) :=
    Partrec.comp hV.1
      ((decodeSecond_computable.comp
        (Computable.fst.comp Computable.fst)).pair
          Computable.snd)
  have hD : isDecompressor D := Partrec.bind hFirst hSecond
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  refine ⟨cD + 1, fun x y z a b hxy hyz => ?_⟩
  obtain ⟨p, hpLength, hp⟩ :=
    (condKLeIff V y x a).mp hxy
  obtain ⟨q, hqLength, hq⟩ :=
    (condKLeIff V z y b).mp hyz
  change p.length ≤ a at hpLength
  change q.length ≤ b at hqLength
  have hDProd : produces D (pairCode p q) x z := by
    change z ∈ (V (decodeFirst (pairCode p q), x)).bind fun y =>
      V (decodeSecond (pairCode p q), y)
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    exact Part.mem_bind_iff.mpr ⟨y, hp, hq⟩
  have hBound :
      condK V z x ≤
        ((pairCode p q).length : ENat) + (cD : ENat) := by
    calc
      condK V z x ≤ condK D z x + (cD : ENat) := hcD z x
      _ ≤ ((pairCode p q).length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨pairCode p q, hDProd, rfl⟩
  have hLength :
      (pairCode p q).length + cD ≤
        2 * a + b + (cD + 1) := by
    rw [length_pairCode]
    omega
  exact hBound.trans (by
    rw [← Nat.cast_add]
    exact_mod_cast hLength)

/-- A three-block string can be described by a shortest plain program for its
middle block, the two private blocks literally, and logarithmic split metadata.
Unlike a bare subadditivity interface, the proof constructs the decoder that
parses and runs the middle program. -/
theorem plainK_threeBlock_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ left middle right : BitString,
      plainK V (left ++ middle ++ right) ≤
        plainK V middle +
          ((left.length + right.length +
            logSlack c ((left ++ middle ++ right).length + 1) : Nat) : ENat) := by
  let leftLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst q)
  let middleLength : BitString → Nat := fun q =>
    decodeBits (decodeFirst (decodeSecond q))
  let body : BitString → BitString := fun q =>
    decodeSecond (decodeSecond q)
  let leftPart : BitString → BitString := fun q =>
    (body q).take (leftLength q)
  let middleProgram : BitString → BitString := fun q =>
    ((body q).drop (leftLength q)).take (middleLength q)
  let rightPart : BitString → BitString := fun q =>
    (body q).drop (leftLength q + middleLength q)
  let D : Map := fun pr =>
    (V (middleProgram pr.1, [])).map fun decoded =>
      leftPart pr.1 ++ decoded ++ rightPart pr.1
  have hLeftLength : Computable leftLength :=
    decodeBitsComputable.comp decodeFirst_computable
  have hMiddleLength : Computable middleLength :=
    decodeBitsComputable.comp
      (decodeFirst_computable.comp decodeSecond_computable)
  have hBody : Computable body :=
    decodeSecond_computable.comp decodeSecond_computable
  have hLeftPart : Computable leftPart :=
    Primrec.list_take.to_comp.comp hBody hLeftLength
  have hMiddleProgram : Computable middleProgram :=
    Primrec.list_take.to_comp.comp
      (Primrec.list_drop.to_comp.comp hBody hLeftLength)
      hMiddleLength
  have hLengths : Computable (fun q =>
      leftLength q + middleLength q) :=
    (show Computable₂ (fun a b : Nat => a + b) from
      Primrec.nat_add.to_comp).comp hLeftLength hMiddleLength
  have hRightPart : Computable rightPart :=
    Primrec.list_drop.to_comp.comp hBody hLengths
  have hRun :
      Partrec (fun pr : BitString × BitString =>
        V (middleProgram pr.1, [])) :=
    Partrec.comp hV.1
      ((hMiddleProgram.comp Computable.fst).pair
        (Computable.const []))
  have hOutput :
      Computable
        (fun q : (BitString × BitString) × BitString =>
          leftPart q.1.1 ++ q.2 ++ rightPart q.1.1) :=
    Computable.list_append.comp
      (Computable.list_append.comp
        (hLeftPart.comp (Computable.fst.comp Computable.fst))
        Computable.snd)
      (hRightPart.comp (Computable.fst.comp Computable.fst))
  have hD : isDecompressor D := Partrec.map hRun hOutput
  obtain ⟨cD, hcD⟩ := hV.2 D hD
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  let cMeta := cD + 6
  obtain ⟨C, hFold⟩ := logSlack_linear_bound cMeta 1 cLen
  refine ⟨C, fun left middle right => ?_⟩
  obtain ⟨km, hkm⟩ :=
    exists_plainComplexityValue V hV middle
  obtain ⟨p, hp, hpLen⟩ := hkm.exists_program
  set prog : BitString :=
    pairCode (Nat.bits left.length)
      (pairCode (Nat.bits p.length) (left ++ p ++ right)) with hProg
  have hMiddleEval : middleProgram prog = p := by
    dsimp [middleProgram, body, leftLength, middleLength]
    rw [hProg]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits]
    rw [List.append_assoc, List.drop_left, List.take_left]
  have hLeftEval : leftPart prog = left := by
    dsimp [leftPart, body, leftLength]
    rw [hProg]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits]
    rw [List.append_assoc, List.take_left]
  have hRightEval : rightPart prog = right := by
    dsimp [rightPart, body, leftLength, middleLength]
    rw [hProg]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode,
      decodeBits_natBits]
    rw [← List.length_append, List.drop_left]
  have hDProd :
      produces D prog [] (left ++ middle ++ right) := by
    change left ++ middle ++ right ∈
      (V (middleProgram prog, [])).map fun decoded =>
        leftPart prog ++ decoded ++ rightPart prog
    rw [hMiddleEval, hLeftEval, hRightEval]
    exact Part.mem_map (fun decoded => left ++ decoded ++ right) hp
  have hDBound :
      plainK V (left ++ middle ++ right) ≤
        (prog.length : ENat) + (cD : ENat) := by
    calc
      plainK V (left ++ middle ++ right)
          ≤ plainK D (left ++ middle ++ right) + (cD : ENat) :=
        hcD (left ++ middle ++ right) []
      _ ≤ (prog.length : ENat) + (cD : ENat) := by
        gcongr
        exact sInf_le ⟨prog, hDProd, rfl⟩
  let N := (left ++ middle ++ right).length + 1
  have hkmLength : km ≤ middle.length + cLen := by
    have h := hLen middle
    rw [hkm] at h
    exact_mod_cast h
  have hpVisible : p.length ≤ N + cLen := by
    rw [hpLen]
    dsimp [N]
    simp only [List.length_append]
    omega
  have hleftVisible : left.length ≤ N + cLen := by
    dsimp [N]
    simp only [List.length_append]
    omega
  have hBitsLeft :
      (Nat.bits left.length).length ≤
        (Nat.bits (N + cLen)).length :=
    length_natBits_mono hleftVisible
  have hBitsP :
      (Nat.bits p.length).length ≤
        (Nat.bits (N + cLen)).length :=
    length_natBits_mono hpVisible
  have hProgLength :
      prog.length =
        2 * (Nat.bits left.length).length +
        2 * (Nat.bits p.length).length +
        left.length + p.length + right.length + 2 := by
    rw [hProg, length_pairCode, length_pairCode]
    simp only [List.length_append]
    omega
  have hMeta :
      prog.length + cD ≤
        p.length + left.length + right.length +
          logSlack cMeta (N + cLen) := by
    unfold logSlack
    rw [hProgLength]
    dsimp [cMeta]
    nlinarith
  have hFinal :
      prog.length + cD ≤
        p.length + left.length + right.length +
          logSlack C N := by
    have hFold' :
        logSlack cMeta (N + cLen) ≤ logSlack C N := by
      simpa using hFold N
    exact hMeta.trans
      (Nat.add_le_add_left hFold'
        (p.length + left.length + right.length))
  calc
    plainK V (left ++ middle ++ right)
        ≤ (prog.length : ENat) + (cD : ENat) := hDBound
    _ = ((prog.length + cD : Nat) : ENat) := by push_cast; ring
    _ ≤ ((p.length + left.length + right.length +
          logSlack C N : Nat) : ENat) := by
      exact_mod_cast hFinal
    _ = plainK V middle +
          ((left.length + right.length +
            logSlack C ((left ++ middle ++ right).length + 1) : Nat) : ENat) := by
      rw [hpLen, hkm]
      dsimp [N]
      push_cast
      ring

/-- The reverse implication behind the overlap conjecture: a literal overlap
representation supplies an extractable common string.  In the overlap case the
witness is the actual intersection of the represented prefix and suffix.  In
the gap case the witness is empty, and the additive mutual-information
inequality proves that `m` is already within the output error budget. -/
theorem overlapRepresentation_yields_extractableCommonInformation
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C, ∀ x y u kx ky kxy m d,
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V y ky →
      HasPlainComplexityValue V (pairCode x y) kxy →
      MutualInformationWithin V x y m d →
      OverlapRepresentationWithin V x y u kx ky kxy d →
      ∃ z, ExtractableCommonInformationWithin V x y z m
        (commonInformationSlack C d (kxy + 1)) := by
  obtain ⟨cTrans, hTrans⟩ := condK_trans_visible_le V hV
  obtain ⟨cSlice, hSlice⟩ := condK_slice_le V hV
  obtain ⟨cThree, hThree⟩ := plainK_threeBlock_le V hV
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cEmpty, hEmpty⟩ :=
    condKComp V hV (fun _ : BitString => ([] : BitString))
      (Computable.const [])
  let C := cTrans + cSlice + cThree + cLen + cEmpty + 10
  refine ⟨C, fun x y u kx ky kxy m d hx hy hxy hI hOverlap => ?_⟩
  rcases hOverlap with
    ⟨lx, ly, hu, hlxU, hlyU, hlxClose, hlyClose,
      hxEq, hyEq, _hpairEq, huInc⟩
  have hlx : lx ≤ kxy := by simpa [hu] using hlxU
  have hly : ly ≤ kxy := by simpa [hu] using hlyU
  have hMI₁ : kxy + m ≤ kx + ky + d := by
    have h := hI.1
    rw [pairPlainK, hxy, hx, hy] at h
    exact_mod_cast h
  have hMI₂ : kx + ky ≤ kxy + m + d := by
    have h := hI.2
    rw [pairPlainK, hxy, hx, hy] at h
    exact_mod_cast h
  let D := commonInformationSlack C d (kxy + 1)
  have hCondBudget :
      2 * d + logSlack cSlice (kxy + 1) + cTrans ≤ D := by
    dsimp [D, C]
    unfold commonInformationSlack logSlack
    nlinarith
  have hUpperBudget : 3 * d + cLen ≤ D := by
    dsimp [D, C]
    unfold commonInformationSlack logSlack
    nlinarith
  have hLowerBudget :
      4 * d + logSlack cThree (kxy + 1) ≤ D := by
    dsimp [D, C]
    unfold commonInformationSlack logSlack
    nlinarith
  have hEmptyCondBudget : cEmpty ≤ D := by
    dsimp [D, C]
    unfold commonInformationSlack logSlack
    nlinarith
  have hEmptyPlainBudget : cLen ≤ D := by
    dsimp [D, C]
    unfold commonInformationSlack logSlack
    nlinarith
  by_cases hov : kxy ≤ lx + ly
  · let z := literalOverlap u lx ly
    let s := lx + ly - kxy
    have hzLength : z.length = s := by
      dsimp [z, s]
      exact literalOverlap_length hu hlx hly hov
    have hPrefixLength : (u.take lx).length = lx := by
      rw [List.length_take, hu, Nat.min_eq_left hlx]
    have hSuffixLength :
        (u.drop (u.length - ly)).length = ly := by
      rw [List.length_drop, hu]
      omega
    have hStartPrefix : kxy - ly ≤ (u.take lx).length := by
      rw [hPrefixLength]
      omega
    have hsPrefix : s ≤ (u.take lx).length := by
      rw [hPrefixLength]
      dsimp [s]
      omega
    have hsSuffix : s ≤ (u.drop (u.length - ly)).length := by
      rw [hSuffixLength]
      dsimp [s]
      omega
    have hzPrefixSlice :
        ((u.take lx).drop (kxy - ly)).take s = z := by
      rw [← literalOverlap_eq_prefix_drop hu hlx hly hov]
      exact (List.take_eq_self_iff z).mpr (by rw [hzLength])
    have hzSuffixSlice :
        ((u.drop (u.length - ly)).drop 0).take s = z := by
      simp only [List.drop_zero]
      dsimp [z, s]
      simpa [hu] using
        (literalOverlap_eq_suffix_take
          (u := u) (lx := lx) (ly := ly) (kxy := kxy) hu).symm
    have hSliceX :
        condK V z (u.take lx) ≤
          (logSlack cSlice (kxy + 1) : ENat) := by
      have h :=
        hSlice (u.take lx) (kxy - ly) s hStartPrefix hsPrefix
      rw [hzPrefixSlice] at h
      exact h.trans (by
        exact_mod_cast
          logSlack_mono_right cSlice (by
            rw [hPrefixLength]
            omega))
    have hSliceY :
        condK V z (u.drop (u.length - ly)) ≤
          (logSlack cSlice (kxy + 1) : ENat) := by
      have h :=
        hSlice (u.drop (u.length - ly)) 0 s
          (Nat.zero_le _) hsSuffix
      rw [hzSuffixSlice] at h
      exact h.trans (by
        exact_mod_cast
          logSlack_mono_right cSlice (by
            rw [hSuffixLength]
            omega))
    have hzGivenX :
        condK V z x ≤
          ((2 * d + logSlack cSlice (kxy + 1) + cTrans : Nat) : ENat) :=
      hTrans x (u.take lx) z d
        (logSlack cSlice (kxy + 1)) hxEq.2 hSliceX
    have hzGivenY :
        condK V z y ≤
          ((2 * d + logSlack cSlice (kxy + 1) + cTrans : Nat) : ENat) :=
      hTrans y (u.drop (u.length - ly)) z d
        (logSlack cSlice (kxy + 1)) hyEq.2 hSliceY
    have hsUpper : s ≤ m + 3 * d := by
      dsimp [s]
      unfold NatCloseWithin at hlxClose hlyClose
      omega
    have hmByS : m ≤ s + 3 * d := by
      dsimp [s]
      unfold NatCloseWithin at hlxClose hlyClose
      omega
    obtain ⟨kz, hkz⟩ :=
      exists_plainComplexityValue V hV z
    have hkzLength : kz ≤ s + cLen := by
      have h := hLen z
      change plainK V z ≤ (z.length : ENat) + (cLen : ENat) at h
      rw [hkz, hzLength] at h
      exact_mod_cast h
    obtain ⟨ku, hku⟩ :=
      exists_plainComplexityValue V hV u
    have huIncNat : kxy ≤ ku + d := by
      unfold PlainIncompressibleWithin at huInc
      rw [hu, hku] at huInc
      exact_mod_cast huInc
    obtain ⟨left, right, hfac, hleftLength, hrightLength⟩ :=
      literalOverlap_factorization hu hlx hly hov
    have hThreeNat :
        ku ≤ kz +
          (left.length + right.length +
            logSlack cThree (kxy + 1)) := by
      have h := hThree left z right
      rw [← hfac, hku, hkz, hu] at h
      exact_mod_cast h
    have hsLower :
        s ≤ kz + logSlack cThree (kxy + 1) + d := by
      dsimp [s]
      omega
    have hkzUpper : kz ≤ m + (3 * d + cLen) := by
      omega
    have hmLower :
        m ≤ kz + (4 * d + logSlack cThree (kxy + 1)) := by
      omega
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    · exact hzGivenX.trans (by exact_mod_cast hCondBudget)
    · exact hzGivenY.trans (by exact_mod_cast hCondBudget)
    · rw [hkz]
      exact_mod_cast hkzUpper.trans
        (Nat.add_le_add_left hUpperBudget m)
    · rw [hkz]
      exact_mod_cast hmLower.trans
        (Nat.add_le_add_left hLowerBudget kz)
  · have hmSmall : m ≤ 3 * d := by
      unfold NatCloseWithin at hlxClose hlyClose
      omega
    refine ⟨[], ?_, ?_, ?_, ?_⟩
    · exact (hEmpty x).trans (by exact_mod_cast hEmptyCondBudget)
    · exact (hEmpty y).trans (by exact_mod_cast hEmptyCondBudget)
    · have h := hLen ([] : BitString)
      simp only [List.length_nil, Nat.cast_zero, zero_add] at h
      exact h.trans (by
        exact_mod_cast
          (cLen.le_add_left m).trans
            (Nat.add_le_add_left hEmptyPlainBudget m))
    · have hThreeDBudget : 3 * d ≤ D := by
        dsimp [D, C]
        unfold commonInformationSlack
        nlinarith
      have hmD : m ≤ D := hmSmall.trans hThreeDBudget
      calc
        (m : ENat) ≤ (D : ENat) := by exact_mod_cast hmD
        _ ≤ plainK V [] + (D : ENat) := le_add_left le_rfl

/-- Source-facing logarithmic specialization of
`overlapRepresentation_yields_extractableCommonInformation`, with a uniform
constant preceding all varying strings and complexity values. -/
theorem overlapRepresentation_yields_extractableCommonInformation_log
    (V : Map) (hV : isOptimalConditional V) (a : Nat) :
    ∃ C, ∀ x y u kx ky kxy m,
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V y ky →
      HasPlainComplexityValue V (pairCode x y) kxy →
      MutualInformationWithin V x y m (logSlack a (kxy + 1)) →
      OverlapRepresentationWithin V x y u kx ky kxy
        (logSlack a (kxy + 1)) →
      ∃ z, ExtractableCommonInformationWithin V x y z m
        (logSlack C (kxy + 1)) := by
  obtain ⟨c, hc⟩ :=
    overlapRepresentation_yields_extractableCommonInformation V hV
  refine ⟨c * (a + 1), fun x y u kx ky kxy m hx hy hxy hI hu => ?_⟩
  obtain ⟨z, hz⟩ :=
    hc x y u kx ky kxy m (logSlack a (kxy + 1))
      hx hy hxy hI hu
  refine ⟨z, hz.mono ?_⟩
  unfold commonInformationSlack logSlack
  ring_nf
  exact le_rfl

end Kolmogorov
