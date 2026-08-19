import KolmogorovMathlib.CommonInformation.ConcreteField
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaCount

/-!
# Fixed-width codecs for the concrete affine incidence graph

This file supplies the exact finite encodings needed before the complexity
claims in Exercises 309--310 can be stated honestly. A field element uses
`n + 1` bits because `ConcreteField n` has cardinality at most `2 ^ (n + 1)`.
Points and nonvertical lines therefore use `2 * (n + 1)` bits. An incident
edge is determined by its line and the point's `x`-coordinate, so it uses
`3 * (n + 1)` bits.

No complexity conclusion is drawn here: effective enumeration and the
plain-complexity transport for these codes remain separate dependencies.
-/

namespace Kolmogorov

/-- Fixed-width code of a residue in the concrete prime field. -/
def concreteFieldCode (n : Nat) (a : ConcreteField n) : BitString :=
  fixedWidthNatCode a.val (n + 1)

/-- Decode a fixed-width natural code as a residue in the concrete field. -/
def concreteFieldDecode (n : Nat) (w : BitString) : ConcreteField n :=
  (decodeFixedWidthNatCode w : ZMod (concretePrime n))

@[simp]
lemma concreteFieldCode_length (n : Nat) (a : ConcreteField n) :
    (concreteFieldCode n a).length = n + 1 := by
  apply fixedWidthNatCode_length
  exact (ZMod.val_lt a).trans_le (concretePrime_upper n)

@[simp]
lemma concreteFieldDecode_code (n : Nat) (a : ConcreteField n) :
    concreteFieldDecode n (concreteFieldCode n a) = a := by
  simp [concreteFieldDecode, concreteFieldCode]

lemma concreteFieldCode_injective (n : Nat) :
    Function.Injective (concreteFieldCode n) :=
  Function.LeftInverse.injective (concreteFieldDecode_code n)

/-- Concatenated fixed-width coordinates of a concrete affine point. -/
def concretePointCode (n : Nat)
    (p : AffineIncidence.Point (ConcreteField n)) : BitString :=
  concreteFieldCode n p.1 ++ concreteFieldCode n p.2

/-- Split and decode the two fixed-width coordinates of a point. -/
def concretePointDecode (n : Nat) (w : BitString) :
    AffineIncidence.Point (ConcreteField n) :=
  (concreteFieldDecode n (w.take (n + 1)),
    concreteFieldDecode n (w.drop (n + 1)))

@[simp]
lemma concretePointCode_length (n : Nat)
    (p : AffineIncidence.Point (ConcreteField n)) :
    (concretePointCode n p).length = 2 * (n + 1) := by
  simp [concretePointCode]
  omega

@[simp]
lemma concretePointDecode_code (n : Nat)
    (p : AffineIncidence.Point (ConcreteField n)) :
    concretePointDecode n (concretePointCode n p) = p := by
  simp [concretePointDecode, concretePointCode]

lemma concretePointCode_injective (n : Nat) :
    Function.Injective (concretePointCode n) :=
  Function.LeftInverse.injective (concretePointDecode_code n)

/-- Concatenated fixed-width slope and intercept of a nonvertical line. -/
def concreteLineCode (n : Nat)
    (ell : AffineIncidence.Line (ConcreteField n)) : BitString :=
  concreteFieldCode n ell.1 ++ concreteFieldCode n ell.2

/-- Split and decode the fixed-width slope and intercept of a line. -/
def concreteLineDecode (n : Nat) (w : BitString) :
    AffineIncidence.Line (ConcreteField n) :=
  (concreteFieldDecode n (w.take (n + 1)),
    concreteFieldDecode n (w.drop (n + 1)))

@[simp]
lemma concreteLineCode_length (n : Nat)
    (ell : AffineIncidence.Line (ConcreteField n)) :
    (concreteLineCode n ell).length = 2 * (n + 1) := by
  simp [concreteLineCode]
  omega

@[simp]
lemma concreteLineDecode_code (n : Nat)
    (ell : AffineIncidence.Line (ConcreteField n)) :
    concreteLineDecode n (concreteLineCode n ell) = ell := by
  simp [concreteLineDecode, concreteLineCode]

lemma concreteLineCode_injective (n : Nat) :
    Function.Injective (concreteLineCode n) :=
  Function.LeftInverse.injective (concreteLineDecode_code n)

/-- The subtype of actual edges in the concrete affine incidence graph. -/
abbrev ConcreteIncidentEdge (n : Nat) :=
  ↑(AffineIncidence.incidentEdges (ConcreteField n))

/-- An incident edge is encoded by its line and the point's `x`-coordinate. -/
def concreteIncidentEdgeCode (n : Nat) (e : ConcreteIncidentEdge n) : BitString :=
  concreteLineCode n e.1.2 ++ concreteFieldCode n e.1.1.1

/-- Reconstruct the unique incident point from a decoded line and `x`-coordinate. -/
def concreteIncidentEdgeDecode (n : Nat) (w : BitString) : ConcreteIncidentEdge n :=
  let ell := concreteLineDecode n (w.take (2 * (n + 1)))
  let x := concreteFieldDecode n (w.drop (2 * (n + 1)))
  ⟨((x, ell.1 * x + ell.2), ell), AffineIncidence.mem_incidentEdges_iff.mpr rfl⟩

@[simp]
lemma concreteIncidentEdgeCode_length (n : Nat) (e : ConcreteIncidentEdge n) :
    (concreteIncidentEdgeCode n e).length = 3 * (n + 1) := by
  simp [concreteIncidentEdgeCode]
  omega

@[simp]
lemma concreteIncidentEdgeDecode_code (n : Nat) (e : ConcreteIncidentEdge n) :
    concreteIncidentEdgeDecode n (concreteIncidentEdgeCode n e) = e := by
  have hinc : AffineIncidence.Incident e.1.1 e.1.2 :=
    AffineIncidence.mem_incidentEdges_iff.mp e.2
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · simp [concreteIncidentEdgeDecode, concreteIncidentEdgeCode]
    · simpa [AffineIncidence.Incident, concreteIncidentEdgeDecode,
        concreteIncidentEdgeCode] using hinc.symm
  · simp [concreteIncidentEdgeDecode, concreteIncidentEdgeCode]

lemma concreteIncidentEdgeCode_injective (n : Nat) :
    Function.Injective (concreteIncidentEdgeCode n) :=
  Function.LeftInverse.injective (concreteIncidentEdgeDecode_code n)

/-- An explicit list of all valid code pairs for incident edges in the concrete field. -/
def concreteIncidentEdgeCodePairs (n : Nat) : List (BitString × BitString) :=
  let p := concretePrime n
  let range := List.range p
  range.flatMap fun m =>
    range.flatMap fun b =>
      range.map fun x =>
        let y := (m * x + b) % p
        let pt : AffineIncidence.Point (ConcreteField n) := (x, y)
        let ln : AffineIncidence.Line (ConcreteField n) := (m, b)
        (concretePointCode n pt, concreteLineCode n ln)

lemma concreteIncidentEdgeCodePairs_mem_iff (n : Nat) (pair : BitString × BitString) :
    pair ∈ concreteIncidentEdgeCodePairs n ↔
      ∃ e : ConcreteIncidentEdge n,
        pair = (concretePointCode n e.1.1,
                concreteLineCode n e.1.2) := by
  constructor
  · intro h
    simp only [concreteIncidentEdgeCodePairs, List.mem_flatMap, List.mem_range,
      List.mem_map] at h
    rcases h with ⟨m, hm, b, hb, x, hx, hp⟩
    let pt : AffineIncidence.Point (ConcreteField n) :=
      (x, (m * x + b) % concretePrime n)
    let ell : AffineIncidence.Line (ConcreteField n) := (m, b)
    have hinc : AffineIncidence.Incident pt ell := by
      simp [pt, ell, AffineIncidence.Incident, ZMod.natCast_mod]
    refine ⟨⟨(pt, ell), AffineIncidence.mem_incidentEdges_iff.mpr hinc⟩, ?_⟩
    exact hp.symm
  · rintro ⟨e, rfl⟩
    let m := e.1.2.1.val
    let b := e.1.2.2.val
    let x := e.1.1.1.val
    have hm : m < concretePrime n := ZMod.val_lt _
    have hb : b < concretePrime n := ZMod.val_lt _
    have hx : x < concretePrime n := ZMod.val_lt _
    simp only [concreteIncidentEdgeCodePairs, List.mem_flatMap, List.mem_range,
      List.mem_map]
    refine ⟨m, hm, b, hb, x, hx, ?_⟩
    have hinc : AffineIncidence.Incident e.1.1 e.1.2 :=
      AffineIncidence.mem_incidentEdges_iff.mp e.2
    have hpoint :
        ((x : ConcreteField n),
          ((m * x + b) % concretePrime n : ConcreteField n)) = e.1.1 := by
      apply Prod.ext
      · simp [x]
      · simpa [m, b, x, ZMod.natCast_mod] using hinc.symm
    have hline : ((m : ConcreteField n), (b : ConcreteField n)) = e.1.2 := by
      apply Prod.ext <;> simp [m, b]
    rw [hpoint, hline]

private lemma concreteIncidentEdgeCodePairs_length_aux (n : Nat) :
    (concreteIncidentEdgeCodePairs n).length = concretePrime n ^ 3 := by
  simp [concreteIncidentEdgeCodePairs, pow_succ]
  ring

lemma concreteIncidentEdgeCodePairs_nodup (n : Nat) :
    (concreteIncidentEdgeCodePairs n).Nodup := by
  let f : ConcreteIncidentEdge n → BitString × BitString := fun e =>
    (concretePointCode n e.1.1, concreteLineCode n e.1.2)
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    apply Subtype.ext
    apply Prod.ext
    · exact concretePointCode_injective n (Prod.ext_iff.mp h).1
    · exact concreteLineCode_injective n (Prod.ext_iff.mp h).2
  have himage : (concreteIncidentEdgeCodePairs n).toFinset =
      Finset.univ.image f := by
    ext pair
    simp only [List.mem_toFinset, concreteIncidentEdgeCodePairs_mem_iff,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨e, rfl⟩
  have hcard : (concreteIncidentEdgeCodePairs n).toFinset.card =
      (concreteIncidentEdgeCodePairs n).length := by
    rw [himage, Finset.card_image_of_injective _ hf, Finset.card_univ,
      Fintype.card_coe, AffineIncidence.incidentEdges_card,
      concreteField_card_eq, concreteIncidentEdgeCodePairs_length_aux]
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp hcard

lemma concreteIncidentEdgeCodePairs_length (n : Nat) :
    (concreteIncidentEdgeCodePairs n).length = concretePrime n ^ 3 :=
  concreteIncidentEdgeCodePairs_length_aux n

lemma concreteIncidentEdgeCodePairs_code_lengths
    {n : Nat} {pair : BitString × BitString}
    (hpair : pair ∈ concreteIncidentEdgeCodePairs n) :
    pair.1.length = 2 * (n + 1) ∧
      pair.2.length = 2 * (n + 1) := by
  obtain ⟨e, rfl⟩ := (concreteIncidentEdgeCodePairs_mem_iff n pair).mp hpair
  simp

private lemma fixedWidthNatCode_primrec_local :
    Primrec (fun p : Nat × Nat => fixedWidthNatCode p.1 p.2) := by
  have hbits : Primrec (fun p : Nat × Nat => Nat.bits p.1) :=
    primrecNatBits.comp Primrec.fst
  have hpadLength : Primrec (fun p : Nat × Nat =>
      p.2 - (Nat.bits p.1).length) :=
    Primrec.nat_sub.comp Primrec.snd
      (Primrec.list_length.comp hbits)
  have hpadding : Primrec (fun p : Nat × Nat =>
      List.replicate (p.2 - (Nat.bits p.1).length) false) :=
    Primrec.list_replicate.comp hpadLength (Primrec.const false)
  unfold fixedWidthNatCode chunkAddress
  exact Primrec.list_reverse.comp
    (Primrec.list_append.comp hbits hpadding)

private def concreteIncidentEdgeCodePairNat
    (n m b x : Nat) : BitString × BitString :=
  let p := concretePrime n
  let width := n + 1
  let code (a : Nat) := fixedWidthNatCode (a % p) width
  (code x ++ code ((m * x + b) % p), code m ++ code b)

private lemma concreteIncidentEdgeCodePairNat_eq (n m b x : Nat) :
    concreteIncidentEdgeCodePairNat n m b x =
      let y := (m * x + b) % concretePrime n
      let pt : AffineIncidence.Point (ConcreteField n) := (x, y)
      let ln : AffineIncidence.Line (ConcreteField n) := (m, b)
      (concretePointCode n pt, concreteLineCode n ln) := by
  simp [concreteIncidentEdgeCodePairNat, concretePointCode, concreteLineCode,
    concreteFieldCode, ZMod.val_natCast, ZMod.val_add, ZMod.val_mul,
    Nat.add_mod, Nat.mul_mod]

lemma concreteIncidentEdgeCodePairs_primrec :
    Primrec concreteIncidentEdgeCodePairs := by
  let Q := (((Nat × Nat) × Nat) × Nat)
  have hn : Primrec (fun q : Q => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))
  have hm : Primrec (fun q : Q => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))
  have hb : Primrec (fun q : Q => q.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.id)
  have hx : Primrec (fun q : Q => q.2) := Primrec.snd
  have hp : Primrec (fun q : Q => concretePrime q.1.1.1) :=
    boundedPrimeSearch_primrec.comp hn
  have hwidth : Primrec (fun q : Q => q.1.1.1 + 1) :=
    Primrec.succ.comp hn
  have hxm : Primrec (fun q : Q => q.2 % concretePrime q.1.1.1) :=
    Primrec.nat_mod.comp hx hp
  have hmm : Primrec (fun q : Q => q.1.1.2 % concretePrime q.1.1.1) :=
    Primrec.nat_mod.comp hm hp
  have hbm : Primrec (fun q : Q => q.1.2 % concretePrime q.1.1.1) :=
    Primrec.nat_mod.comp hb hp
  have hy : Primrec (fun q : Q =>
      (q.1.1.2 * q.2 + q.1.2) % concretePrime q.1.1.1) :=
    Primrec.nat_mod.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hm hx) hb) hp
  have hym : Primrec (fun q : Q =>
      ((q.1.1.2 * q.2 + q.1.2) % concretePrime q.1.1.1) %
        concretePrime q.1.1.1) :=
    Primrec.nat_mod.comp hy hp
  have hcodex : Primrec (fun q : Q =>
      fixedWidthNatCode (q.2 % concretePrime q.1.1.1) (q.1.1.1 + 1)) :=
    fixedWidthNatCode_primrec_local.comp (Primrec.pair hxm hwidth)
  have hcodey : Primrec (fun q : Q =>
      fixedWidthNatCode
        (((q.1.1.2 * q.2 + q.1.2) % concretePrime q.1.1.1) %
          concretePrime q.1.1.1) (q.1.1.1 + 1)) :=
    fixedWidthNatCode_primrec_local.comp (Primrec.pair hym hwidth)
  have hcodem : Primrec (fun q : Q =>
      fixedWidthNatCode (q.1.1.2 % concretePrime q.1.1.1) (q.1.1.1 + 1)) :=
    fixedWidthNatCode_primrec_local.comp (Primrec.pair hmm hwidth)
  have hcodeb : Primrec (fun q : Q =>
      fixedWidthNatCode (q.1.2 % concretePrime q.1.1.1) (q.1.1.1 + 1)) :=
    fixedWidthNatCode_primrec_local.comp (Primrec.pair hbm hwidth)
  have hout : Primrec (fun q : Q =>
      concreteIncidentEdgeCodePairNat q.1.1.1 q.1.1.2 q.1.2 q.2) :=
    (Primrec.list_append.comp hcodex hcodey).pair
      (Primrec.list_append.comp hcodem hcodeb)
  let T := (Nat × Nat) × Nat
  have hnT : Primrec (fun q : T => q.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.id)
  have hpT : Primrec (fun q : T => concretePrime q.1.1) :=
    boundedPrimeSearch_primrec.comp hnT
  have hrangeT : Primrec (fun q : T => List.range (concretePrime q.1.1)) :=
    Primrec.list_range.comp hpT
  have hmapT : Primrec (fun q : T =>
      (List.range (concretePrime q.1.1)).map
        (fun x => concreteIncidentEdgeCodePairNat q.1.1 q.1.2 q.2 x)) :=
    Primrec.list_map hrangeT hout.to₂
  let S := Nat × Nat
  have hnS : Primrec (fun q : S => q.1) := Primrec.fst
  have hpS : Primrec (fun q : S => concretePrime q.1) :=
    boundedPrimeSearch_primrec.comp hnS
  have hrangeS : Primrec (fun q : S => List.range (concretePrime q.1)) :=
    Primrec.list_range.comp hpS
  have hflatS : Primrec (fun q : S =>
      (List.range (concretePrime q.1)).flatMap fun b =>
        (List.range (concretePrime q.1)).map
          (fun x => concreteIncidentEdgeCodePairNat q.1 q.2 b x)) :=
    Primrec.list_flatMap hrangeS hmapT.to₂
  have hrangeN : Primrec (fun n => List.range (concretePrime n)) :=
    Primrec.list_range.comp boundedPrimeSearch_primrec
  have hflatN : Primrec (fun n =>
      (List.range (concretePrime n)).flatMap fun m =>
        (List.range (concretePrime n)).flatMap fun b =>
          (List.range (concretePrime n)).map fun x =>
            concreteIncidentEdgeCodePairNat n m b x) :=
    Primrec.list_flatMap hrangeN hflatS.to₂
  exact hflatN.of_eq fun n => by
    simp only [concreteIncidentEdgeCodePairs]
    congr 1
    funext m
    congr 1
    funext b
    congr 1
    funext x
    exact concreteIncidentEdgeCodePairNat_eq n m b x

lemma concreteIncidentEdgeCodePairs_computable :
    Computable concreteIncidentEdgeCodePairs :=
  concreteIncidentEdgeCodePairs_primrec.to_comp

end Kolmogorov
