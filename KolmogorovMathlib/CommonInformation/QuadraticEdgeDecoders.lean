import KolmogorovMathlib.CommonInformation.QuadraticIncidenceDecoders

/-!
# Edge codecs for the quadratic-extension incidence graph

Building on the point decoder of `QuadraticIncidenceDecoders.lean`, this file
supplies the line decoder, the `6 * (m + 1)`-bit code of an incident pair, and
the resulting plain and conditional complexity bounds.
-/

namespace Kolmogorov

open AffineIncidence


/-- From the code of a point and the code of the line's slope, reconstruct the
code of the incident line. -/
def quadLineFromPointCode (pointCode program : BitString) : BitString :=
  program ++
    (fixedWidthNatCode
        ((quadChunk (pointCode.length / 4) 2 pointCode +
            concretePrime (pointCode.length / 4 - 1) -
          quadMulNat0 (pointCode.length / 4 - 1)
            (quadChunk (pointCode.length / 4) 0 program)
            (quadChunk (pointCode.length / 4) 1 program)
            (quadChunk (pointCode.length / 4) 0 pointCode)
            (quadChunk (pointCode.length / 4) 1 pointCode)) %
          concretePrime (pointCode.length / 4 - 1))
        (pointCode.length / 4) ++
      fixedWidthNatCode
        ((quadChunk (pointCode.length / 4) 3 pointCode +
            concretePrime (pointCode.length / 4 - 1) -
          quadMulNat1 (pointCode.length / 4 - 1)
            (quadChunk (pointCode.length / 4) 0 program)
            (quadChunk (pointCode.length / 4) 1 program)
            (quadChunk (pointCode.length / 4) 0 pointCode)
            (quadChunk (pointCode.length / 4) 1 pointCode)) %
          concretePrime (pointCode.length / 4 - 1))
        (pointCode.length / 4))

lemma quadLineFromPointCode_incident {m : Nat} {p : Point (ConcreteQuadraticField m)}
    {ell : Line (ConcreteQuadraticField m)} (hinc : Incident p ell) :
    quadLineFromPointCode (quadraticPointCode m p) (quadraticFieldCode m ell.1) =
      quadraticLineCode m ell := by
  have hwidth : (quadraticPointCode m p).length / 4 = m + 1 := by
    rw [quadraticPointCode_length]
    omega
  obtain ⟨hc0, hc1, hc2, hc3⟩ := quadChunk_pointCode m p
  have ha0 := quadChunk_fieldCode_zero m ell.1
  have ha1 := quadChunk_fieldCode_one m ell.1
  obtain ⟨hm0, hm1⟩ := quadMul_repr m ell.1 p.1
  have hell2 : ell.2 = p.2 - ell.1 * p.1 := by
    have hp2 : p.2 = ell.1 * p.1 + ell.2 := hinc
    rw [hp2]; ring
  have hval0 :
      (((concreteQuadraticBasis m).repr p.2 0).val + concretePrime m -
          quadMulNat0 m ((concreteQuadraticBasis m).repr ell.1 0).val
            ((concreteQuadraticBasis m).repr ell.1 1).val
            ((concreteQuadraticBasis m).repr p.1 0).val
            ((concreteQuadraticBasis m).repr p.1 1).val) % concretePrime m =
        ((concreteQuadraticBasis m).repr ell.2 0).val := by
    rw [hell2, quadSub_repr, hm0]
  have hval1 :
      (((concreteQuadraticBasis m).repr p.2 1).val + concretePrime m -
          quadMulNat1 m ((concreteQuadraticBasis m).repr ell.1 0).val
            ((concreteQuadraticBasis m).repr ell.1 1).val
            ((concreteQuadraticBasis m).repr p.1 0).val
            ((concreteQuadraticBasis m).repr p.1 1).val) % concretePrime m =
        ((concreteQuadraticBasis m).repr ell.2 1).val := by
    rw [hell2, quadSub_repr, hm1]
  simp only [quadLineFromPointCode, hwidth, Nat.add_sub_cancel, hc0, hc1, hc2, hc3,
    ha0, ha1, hval0, hval1]
  rfl

lemma quadLineFromPointCode_primrec : Primrec₂ quadLineFromPointCode := by
  have hwidth : Primrec (fun q : BitString × BitString => q.1.length / 4) :=
    Primrec.nat_div.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 4)
  have hm : Primrec (fun q : BitString × BitString => q.1.length / 4 - 1) :=
    Primrec.nat_sub.comp hwidth (Primrec.const 1)
  have hprime : Primrec (fun q : BitString × BitString =>
      concretePrime (q.1.length / 4 - 1)) :=
    boundedPrimeSearch_primrec.comp hm
  have hchunk : ∀ (i : Nat) (sel : BitString × BitString → BitString), Primrec sel →
      Primrec (fun q : BitString × BitString => quadChunk (q.1.length / 4) i (sel q)) := by
    intro i sel hsel
    exact quadChunk_primrec.comp
      (Primrec.pair (Primrec.pair hwidth (Primrec.const i)) hsel)
  have ht0 := hchunk 0 Prod.fst Primrec.fst
  have ht1 := hchunk 1 Prod.fst Primrec.fst
  have hy0 := hchunk 2 Prod.fst Primrec.fst
  have hy1 := hchunk 3 Prod.fst Primrec.fst
  have ha0 := hchunk 0 Prod.snd Primrec.snd
  have ha1 := hchunk 1 Prod.snd Primrec.snd
  have harg : Primrec (fun q : BitString × BitString =>
      ((((q.1.length / 4 - 1, quadChunk (q.1.length / 4) 0 q.2),
        (quadChunk (q.1.length / 4) 1 q.2, quadChunk (q.1.length / 4) 0 q.1)),
        quadChunk (q.1.length / 4) 1 q.1) : ((Nat × Nat) × Nat × Nat) × Nat)) :=
    Primrec.pair (Primrec.pair (Primrec.pair hm ha0) (Primrec.pair ha1 ht0)) ht1
  have hmul0 := quadMulNat0_primrec.comp harg
  have hmul1 := quadMulNat1_primrec.comp harg
  have hcode0 := fixedWidthNatCode_primrec.comp
    (Primrec.pair
      (Primrec.nat_mod.comp
        (Primrec.nat_sub.comp (Primrec.nat_add.comp hy0 hprime) hmul0) hprime)
      hwidth)
  have hcode1 := fixedWidthNatCode_primrec.comp
    (Primrec.pair
      (Primrec.nat_mod.comp
        (Primrec.nat_sub.comp (Primrec.nat_add.comp hy1 hprime) hmul1) hprime)
      hwidth)
  exact ((Primrec.list_append.comp Primrec.snd
    (Primrec.list_append.comp hcode0 hcode1)).of_eq (fun _ => rfl)).to₂


/-! ### Reconstructing the whole incident pair -/

/-- The `6 * (m + 1)`-bit description of an incident pair: the line followed by
the first coordinate of the point. -/
noncomputable def quadraticIncidentEdgeCode (m : Nat) (p : Point (ConcreteQuadraticField m))
    (ell : Line (ConcreteQuadraticField m)) : BitString :=
  quadraticLineCode m ell ++ quadraticFieldCode m p.1

@[simp]
lemma quadraticIncidentEdgeCode_length (m : Nat) (p : Point (ConcreteQuadraticField m))
    (ell : Line (ConcreteQuadraticField m)) :
    (quadraticIncidentEdgeCode m p ell).length = 6 * (m + 1) := by
  simp [quadraticIncidentEdgeCode]
  ring

/-- Decode an incident-pair description into the pair code of point and line. -/
def quadIncidentPairFromEdgeCode (s : BitString) : BitString :=
  pairCode
    (quadPointFromLineCode (s.take (4 * (s.length / 6))) (s.drop (4 * (s.length / 6))))
    (s.take (4 * (s.length / 6)))

lemma quadIncidentPairFromEdgeCode_edge {m : Nat} {p : Point (ConcreteQuadraticField m)}
    {ell : Line (ConcreteQuadraticField m)} (hinc : Incident p ell) :
    quadIncidentPairFromEdgeCode (quadraticIncidentEdgeCode m p ell) =
      pairCode (quadraticPointCode m p) (quadraticLineCode m ell) := by
  have hwidth : (quadraticIncidentEdgeCode m p ell).length / 6 = m + 1 := by
    rw [quadraticIncidentEdgeCode_length]
    omega
  have hlen : (quadraticLineCode m ell).length = 4 * (m + 1) := quadraticLineCode_length m ell
  have htake : (quadraticIncidentEdgeCode m p ell).take (4 * (m + 1)) =
      quadraticLineCode m ell := by
    rw [quadraticIncidentEdgeCode, List.take_left' hlen]
  have hdrop : (quadraticIncidentEdgeCode m p ell).drop (4 * (m + 1)) =
      quadraticFieldCode m p.1 := by
    rw [quadraticIncidentEdgeCode, List.drop_left' hlen]
  simp only [quadIncidentPairFromEdgeCode, hwidth, htake, hdrop,
    quadPointFromLineCode_incident hinc]

lemma quadIncidentPairFromEdgeCode_primrec : Primrec quadIncidentPairFromEdgeCode := by
  have hwidth : Primrec (fun s : BitString => 4 * (s.length / 6)) :=
    Primrec.nat_mul.comp (Primrec.const 4)
      (Primrec.nat_div.comp Primrec.list_length (Primrec.const 6))
  have htake : Primrec (fun s : BitString => s.take (4 * (s.length / 6))) :=
    primrec_list_take.comp Primrec.id hwidth
  have hdrop : Primrec (fun s : BitString => s.drop (4 * (s.length / 6))) :=
    primrec_list_drop.comp Primrec.id hwidth
  have hpoint : Primrec (fun s : BitString =>
      quadPointFromLineCode (s.take (4 * (s.length / 6))) (s.drop (4 * (s.length / 6)))) :=
    quadPointFromLineCode_primrec.comp htake hdrop
  exact (pairCode_primrec.comp hpoint htake).of_eq (fun _ => rfl)

/-! ### The resulting complexity bounds -/

theorem pairPlainK_quadraticIncident_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ (m : Nat) (p : Point (ConcreteQuadraticField m))
      (ell : Line (ConcreteQuadraticField m)), Incident p ell →
      pairPlainK V (quadraticPointCode m p) (quadraticLineCode m ell) ≤
        ((6 * (m + 1) + c : Nat) : ENat) := by
  let f : BitString →. BitString := fun w => Part.some (quadIncidentPairFromEdgeCode w)
  have hf : Partrec f := quadIncidentPairFromEdgeCode_primrec.to_comp.partrec
  obtain ⟨cMap, hMap⟩ := plainK_partrec_map_le V hV f hf
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  refine ⟨cLength + cMap, fun m p ell hinc => ?_⟩
  have hrec : pairCode (quadraticPointCode m p) (quadraticLineCode m ell) ∈
      f (quadraticIncidentEdgeCode m p ell) := by
    change pairCode (quadraticPointCode m p) (quadraticLineCode m ell) ∈
      Part.some (quadIncidentPairFromEdgeCode (quadraticIncidentEdgeCode m p ell))
    rw [quadIncidentPairFromEdgeCode_edge hinc]
    exact Part.mem_some _
  calc
    pairPlainK V (quadraticPointCode m p) (quadraticLineCode m ell)
        ≤ plainK V (quadraticIncidentEdgeCode m p ell) + (cMap : ENat) := hMap _ _ hrec
    _ ≤ ((quadraticIncidentEdgeCode m p ell).length : ENat) + (cLength : ENat) +
          (cMap : ENat) := by
        gcongr
        exact hLength _
    _ = ((6 * (m + 1) + (cLength + cMap) : Nat) : ENat) := by
        rw [quadraticIncidentEdgeCode_length]
        push_cast
        ring

theorem condK_quadraticPoint_given_line_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ (m : Nat) (p : Point (ConcreteQuadraticField m))
      (ell : Line (ConcreteQuadraticField m)), Incident p ell →
      condK V (quadraticPointCode m p) (quadraticLineCode m ell) ≤
        ((2 * (m + 1) + c : Nat) : ENat) := by
  let g : BitString → BitString →. BitString := fun y prog =>
    Part.some (quadPointFromLineCode y prog)
  have hg : Partrec (fun q : BitString × BitString => g q.1 q.2) :=
    quadPointFromLineCode_primrec.to_comp.partrec
  obtain ⟨c, hc⟩ := condK_partrec_cond_map_le V hV g hg
  refine ⟨c, fun m p ell hinc => ?_⟩
  have hrec : quadraticPointCode m p ∈
      g (quadraticLineCode m ell) (quadraticFieldCode m p.1) := by
    change quadraticPointCode m p ∈
      Part.some (quadPointFromLineCode (quadraticLineCode m ell) (quadraticFieldCode m p.1))
    rw [quadPointFromLineCode_incident hinc]
    exact Part.mem_some _
  calc
    condK V (quadraticPointCode m p) (quadraticLineCode m ell)
        ≤ ((quadraticFieldCode m p.1).length : ENat) + (c : ENat) := hc _ _ _ hrec
    _ = ((2 * (m + 1) + c : Nat) : ENat) := by
        rw [quadraticFieldCode_length]
        push_cast
        ring

theorem condK_quadraticLine_given_point_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ (m : Nat) (p : Point (ConcreteQuadraticField m))
      (ell : Line (ConcreteQuadraticField m)), Incident p ell →
      condK V (quadraticLineCode m ell) (quadraticPointCode m p) ≤
        ((2 * (m + 1) + c : Nat) : ENat) := by
  let g : BitString → BitString →. BitString := fun y prog =>
    Part.some (quadLineFromPointCode y prog)
  have hg : Partrec (fun q : BitString × BitString => g q.1 q.2) :=
    quadLineFromPointCode_primrec.to_comp.partrec
  obtain ⟨c, hc⟩ := condK_partrec_cond_map_le V hV g hg
  refine ⟨c, fun m p ell hinc => ?_⟩
  have hrec : quadraticLineCode m ell ∈
      g (quadraticPointCode m p) (quadraticFieldCode m ell.1) := by
    change quadraticLineCode m ell ∈
      Part.some (quadLineFromPointCode (quadraticPointCode m p) (quadraticFieldCode m ell.1))
    rw [quadLineFromPointCode_incident hinc]
    exact Part.mem_some _
  calc
    condK V (quadraticLineCode m ell) (quadraticPointCode m p)
        ≤ ((quadraticFieldCode m ell.1).length : ENat) + (c : ENat) := hc _ _ _ hrec
    _ = ((2 * (m + 1) + c : Nat) : ENat) := by
        rw [quadraticFieldCode_length]
        push_cast
        ring

end Kolmogorov
