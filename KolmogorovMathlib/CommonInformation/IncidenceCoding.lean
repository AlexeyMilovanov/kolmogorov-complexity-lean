import KolmogorovMathlib.CommonInformation.IncidenceCodecs
import KolmogorovMathlib.CommonInformation.Interfaces
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaEquivalence

namespace Kolmogorov

def concreteIncidentPairCodes (n : Nat) : List BitString :=
  (concreteIncidentEdgeCodePairs n).map fun p => pairCode p.1 p.2

lemma concreteIncidentPairCodes_mem_iff (n : Nat) (w : BitString) :
    w ∈ concreteIncidentPairCodes n ↔
      ∃ e : ConcreteIncidentEdge n,
        w = pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2) :=
  by
    simp only [concreteIncidentPairCodes, List.mem_map]
    constructor
    · rintro ⟨pair, hpair, rfl⟩
      obtain ⟨e, rfl⟩ :=
        (concreteIncidentEdgeCodePairs_mem_iff n pair).mp hpair
      exact ⟨e, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨_,
        (concreteIncidentEdgeCodePairs_mem_iff n _).mpr ⟨e, rfl⟩,
        rfl⟩

lemma concreteIncidentPairCodes_nodup (n : Nat) :
    (concreteIncidentPairCodes n).Nodup :=
  by
    apply List.Nodup.map _ (concreteIncidentEdgeCodePairs_nodup n)
    intro a b hab
    apply Prod.ext
    · simpa only [decodeFirst_pairCode] using congrArg decodeFirst hab
    · simpa only [decodeSecond_pairCode] using congrArg decodeSecond hab

lemma concreteIncidentPairCodes_length (n : Nat) :
    (concreteIncidentPairCodes n).length = concretePrime n ^ 3 :=
  by
    rw [concreteIncidentPairCodes, List.length_map,
      concreteIncidentEdgeCodePairs_length]

lemma concreteIncidentPairCodes_primrec :
    Primrec concreteIncidentPairCodes :=
  by
    exact Primrec.list_map concreteIncidentEdgeCodePairs_primrec
      ((pairCode_primrec.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)

def concretePointFromLineCode (lineCode program : BitString) : BitString :=
  let width := lineCode.length / 2
  let n := width - 1
  let m := decodeFixedWidthNatCode (lineCode.take width)
  let b := decodeFixedWidthNatCode (lineCode.drop width)
  let x := decodeFixedWidthNatCode program
  program ++ fixedWidthNatCode
    ((m * x + b) % concretePrime n) width

lemma concretePointFromLineCode_incident {n : Nat}
    {p : AffineIncidence.Point (ConcreteField n)}
    {ell : AffineIncidence.Line (ConcreteField n)}
    (hinc : AffineIncidence.Incident p ell) :
    concretePointFromLineCode (concreteLineCode n ell)
        (concreteFieldCode n p.1) =
      concretePointCode n p :=
  by
    have hwidth : (concreteLineCode n ell).length / 2 = n + 1 := by
      rw [concreteLineCode_length]
      omega
    have hy :
        (ell.1.val * p.1.val + ell.2.val) % concretePrime n =
          p.2.val := by
      have hval := congrArg ZMod.val hinc
      simpa [ZMod.val_add, ZMod.val_mul, Nat.add_mod,
        Nat.mul_mod] using hval.symm
    have hmTake :
        (concreteLineCode n ell).take (n + 1) =
          concreteFieldCode n ell.1 := by
      simp [concreteLineCode]
    have hbDrop :
        (concreteLineCode n ell).drop (n + 1) =
          concreteFieldCode n ell.2 := by
      simp [concreteLineCode]
    simp only [concretePointFromLineCode, hwidth]
    rw [hmTake, hbDrop]
    simp [concretePointCode, concreteFieldCode, hy]

lemma concretePointFromLineCode_primrec :
    Primrec₂ concretePointFromLineCode :=
  by
    have hwidth : Primrec (fun q : BitString × BitString =>
        q.1.length / 2) :=
      Primrec.nat_div.comp
        (Primrec.list_length.comp Primrec.fst) (Primrec.const 2)
    have hn : Primrec (fun q : BitString × BitString =>
        q.1.length / 2 - 1) :=
      Primrec.nat_sub.comp hwidth (Primrec.const 1)
    have hp : Primrec (fun q : BitString × BitString =>
        concretePrime (q.1.length / 2 - 1)) :=
      boundedPrimeSearch_primrec.comp hn
    have htake : Primrec (fun q : BitString × BitString =>
        q.1.take (q.1.length / 2)) :=
      primrec_list_take.comp Primrec.fst hwidth
    have hdrop : Primrec (fun q : BitString × BitString =>
        q.1.drop (q.1.length / 2)) :=
      primrec_list_drop.comp Primrec.fst hwidth
    have hm : Primrec (fun q : BitString × BitString =>
        decodeFixedWidthNatCode (q.1.take (q.1.length / 2))) :=
      decodeFixedWidthNatCode_primrec.comp htake
    have hb : Primrec (fun q : BitString × BitString =>
        decodeFixedWidthNatCode (q.1.drop (q.1.length / 2))) :=
      decodeFixedWidthNatCode_primrec.comp hdrop
    have hx : Primrec (fun q : BitString × BitString =>
        decodeFixedWidthNatCode q.2) :=
      decodeFixedWidthNatCode_primrec.comp Primrec.snd
    have hy : Primrec (fun q : BitString × BitString =>
        (decodeFixedWidthNatCode (q.1.take (q.1.length / 2)) *
              decodeFixedWidthNatCode q.2 +
            decodeFixedWidthNatCode (q.1.drop (q.1.length / 2))) %
          concretePrime (q.1.length / 2 - 1)) :=
      Primrec.nat_mod.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp hm hx) hb) hp
    have hcode : Primrec (fun q : BitString × BitString =>
        fixedWidthNatCode
          ((decodeFixedWidthNatCode (q.1.take (q.1.length / 2)) *
                decodeFixedWidthNatCode q.2 +
              decodeFixedWidthNatCode (q.1.drop (q.1.length / 2))) %
            concretePrime (q.1.length / 2 - 1))
          (q.1.length / 2)) :=
      fixedWidthNatCode_primrec.comp (Primrec.pair hy hwidth)
    exact (Primrec.list_append.comp Primrec.snd hcode).of_eq
      (fun q => rfl)

def concreteIncidentPairFromEdgeCode (w : BitString) : BitString :=
  let width := w.length / 3
  let lineCode := w.take (2 * width)
  let xCode := w.drop (2 * width)
  pairCode (concretePointFromLineCode lineCode xCode) lineCode

lemma concreteIncidentPairFromEdgeCode_edge (n : Nat) (e : ConcreteIncidentEdge n) :
    concreteIncidentPairFromEdgeCode (concreteIncidentEdgeCode n e) =
      pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2) :=
  by
    have hwidth :
        (concreteIncidentEdgeCode n e).length / 3 = n + 1 := by
      rw [concreteIncidentEdgeCode_length]
      omega
    have hline :
        (concreteIncidentEdgeCode n e).take (2 * (n + 1)) =
          concreteLineCode n e.1.2 := by
      simp [concreteIncidentEdgeCode]
    have hx :
        (concreteIncidentEdgeCode n e).drop (2 * (n + 1)) =
          concreteFieldCode n e.1.1.1 := by
      simp [concreteIncidentEdgeCode]
    have hinc : AffineIncidence.Incident e.1.1 e.1.2 :=
      AffineIncidence.mem_incidentEdges_iff.mp e.2
    simp only [concreteIncidentPairFromEdgeCode, hwidth]
    rw [hline, hx, concretePointFromLineCode_incident hinc]

lemma concreteIncidentPairFromEdgeCode_primrec :
    Primrec concreteIncidentPairFromEdgeCode :=
  by
    have hwidth : Primrec (fun w : BitString => w.length / 3) :=
      Primrec.nat_div.comp Primrec.list_length (Primrec.const 3)
    have htwice : Primrec (fun w : BitString => 2 * (w.length / 3)) :=
      Primrec.nat_mul.comp (Primrec.const 2) hwidth
    have hline : Primrec (fun w : BitString =>
        w.take (2 * (w.length / 3))) :=
      primrec_list_take.comp Primrec.id htwice
    have hx : Primrec (fun w : BitString =>
        w.drop (2 * (w.length / 3))) :=
      primrec_list_drop.comp Primrec.id htwice
    have hpoint : Primrec (fun w : BitString =>
        concretePointFromLineCode
          (w.take (2 * (w.length / 3)))
          (w.drop (2 * (w.length / 3)))) :=
      concretePointFromLineCode_primrec.comp hline hx
    exact (pairCode_primrec.comp hpoint hline).of_eq (fun w => rfl)

private def concreteHalfCodeWidth (w : BitString) : Nat :=
  w.length / 2

private def concreteFirstHalfNat (w : BitString) : Nat :=
  decodeFixedWidthNatCode (w.take (concreteHalfCodeWidth w))

private def concreteSecondHalfNat (w : BitString) : Nat :=
  decodeFixedWidthNatCode (w.drop (concreteHalfCodeWidth w))

private def concreteLineInterceptNat
    (pointCode program : BitString) : Nat :=
  let width := concreteHalfCodeWidth pointCode
  let q := concretePrime (width - 1)
  let mx := (decodeFixedWidthNatCode program *
    concreteFirstHalfNat pointCode) % q
  (concreteSecondHalfNat pointCode + q - mx) % q

private def concreteLineInterceptData
    (q : BitString × BitString) : Nat × Nat :=
  (concreteLineInterceptNat q.1 q.2, concreteHalfCodeWidth q.1)

private def concreteLineInterceptCode
    (q : BitString × BitString) : BitString :=
  fixedWidthNatCode (concreteLineInterceptData q).1
    (concreteLineInterceptData q).2

private def concreteLineFromPointCodePair
    (q : BitString × BitString) : BitString :=
  q.2 ++ concreteLineInterceptCode q

def concreteLineFromPointCode (pointCode program : BitString) : BitString :=
  concreteLineFromPointCodePair (pointCode, program)

private lemma concreteHalfCodeWidth_primrec :
    Primrec concreteHalfCodeWidth := by
  unfold concreteHalfCodeWidth
  exact Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)

private lemma concreteFirstHalfNat_primrec :
    Primrec concreteFirstHalfNat := by
  unfold concreteFirstHalfNat
  exact decodeFixedWidthNatCode_primrec.comp
    (primrec_list_take.comp Primrec.id concreteHalfCodeWidth_primrec)

private lemma concreteSecondHalfNat_primrec :
    Primrec concreteSecondHalfNat := by
  unfold concreteSecondHalfNat
  exact decodeFixedWidthNatCode_primrec.comp
    (primrec_list_drop.comp Primrec.id concreteHalfCodeWidth_primrec)

private lemma concreteLineInterceptNat_primrec :
    Primrec₂ concreteLineInterceptNat := by
  have hwidth : Primrec (fun q : BitString × BitString =>
      concreteHalfCodeWidth q.1) :=
    concreteHalfCodeWidth_primrec.comp Primrec.fst
  have hn : Primrec (fun q : BitString × BitString =>
      concreteHalfCodeWidth q.1 - 1) :=
    Primrec.nat_sub.comp hwidth (Primrec.const 1)
  have hp : Primrec (fun q : BitString × BitString =>
      concretePrime (concreteHalfCodeWidth q.1 - 1)) :=
    boundedPrimeSearch_primrec.comp hn
  have hx : Primrec (fun q : BitString × BitString =>
      concreteFirstHalfNat q.1) :=
    concreteFirstHalfNat_primrec.comp Primrec.fst
  have hy : Primrec (fun q : BitString × BitString =>
      concreteSecondHalfNat q.1) :=
    concreteSecondHalfNat_primrec.comp Primrec.fst
  have hm : Primrec (fun q : BitString × BitString =>
      decodeFixedWidthNatCode q.2) :=
    decodeFixedWidthNatCode_primrec.comp Primrec.snd
  have hmx : Primrec (fun q : BitString × BitString =>
      (decodeFixedWidthNatCode q.2 * concreteFirstHalfNat q.1) %
        concretePrime (concreteHalfCodeWidth q.1 - 1)) :=
    Primrec.nat_mod.comp (Primrec.nat_mul.comp hm hx) hp
  exact (Primrec.nat_mod.comp
    (Primrec.nat_sub.comp (Primrec.nat_add.comp hy hp) hmx) hp).of_eq
      (fun q => rfl)

private lemma concreteLineInterceptData_primrec :
    Primrec concreteLineInterceptData := by
  unfold concreteLineInterceptData
  exact Primrec.pair concreteLineInterceptNat_primrec
    (concreteHalfCodeWidth_primrec.comp Primrec.fst)

private lemma concreteLineInterceptCode_primrec :
    Primrec concreteLineInterceptCode := by
  unfold concreteLineInterceptCode
  exact fixedWidthNatCode_primrec.comp concreteLineInterceptData_primrec

lemma concreteLineFromPointCode_incident {n : Nat} {p : AffineIncidence.Point (ConcreteField n)}
    {ell : AffineIncidence.Line (ConcreteField n)}
    (hinc : AffineIncidence.Incident p ell) :
    concreteLineFromPointCode (concretePointCode n p) (concreteFieldCode n ell.1) =
      concreteLineCode n ell :=
  by
    have hwidth : (concretePointCode n p).length / 2 = n + 1 := by
      rw [concretePointCode_length]
      omega
    have hxTake :
        (concretePointCode n p).take (n + 1) =
          concreteFieldCode n p.1 := by
      simp [concretePointCode]
    have hyDrop :
        (concretePointCode n p).drop (n + 1) =
          concreteFieldCode n p.2 := by
      simp [concretePointCode]
    let q := concretePrime n
    let a := (ell.1.val * p.1.val) % q
    have hq : 0 < q := by
      dsimp [q]
      exact lt_of_le_of_lt (Nat.zero_le _) (concretePrime_lower n)
    have ha_lt : a < q := Nat.mod_lt _ hq
    have ha_le : a ≤ p.2.val + q := by omega
    have hfield : p.2 - ell.1 * p.1 = ell.2 := by
      rw [hinc]
      ring
    have hcast :
        ((((p.2.val + q - a) % q : Nat) : ZMod q)) = ell.2 := by
      calc
        ((((p.2.val + q - a) % q : Nat) : ZMod q))
            = ((p.2.val + q - a : Nat) : ZMod q) := by
                simp [ZMod.natCast_mod]
        _ = ((p.2.val + q : Nat) : ZMod q) - (a : Nat) := by
              rw [Nat.cast_sub ha_le]
        _ = p.2 - ell.1 * p.1 := by
              simp [a, q, ZMod.natCast_mod]
        _ = ell.2 := hfield
    have hb :
        (p.2.val + concretePrime n -
            (ell.1.val * p.1.val) % concretePrime n) %
              concretePrime n = ell.2.val := by
      simpa [a, q] using congrArg ZMod.val hcast
    simp only [concreteLineFromPointCode,
      concreteLineFromPointCodePair, concreteLineInterceptCode,
      concreteLineInterceptData, concreteHalfCodeWidth, hwidth,
      concreteLineInterceptNat, concreteFirstHalfNat, concreteSecondHalfNat]
    rw [hxTake, hyDrop]
    simp [concreteLineCode, concreteFieldCode, hb]

private lemma concreteLineFromPointCodePair_primrec :
    Primrec concreteLineFromPointCodePair := by
  unfold concreteLineFromPointCodePair
  exact Primrec.list_append.comp Primrec.snd
    concreteLineInterceptCode_primrec

lemma concreteLineFromPointCode_primrec :
    Primrec₂ concreteLineFromPointCode :=
  by
    simpa only [concreteLineFromPointCode] using
      concreteLineFromPointCodePair_primrec

theorem plainK_concreteIncidentPair_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ n (e : ConcreteIncidentEdge n),
      pairPlainK V (concretePointCode n e.1.1) (concreteLineCode n e.1.2)
        ≤ ((3 * (n + 1) + c : Nat) : ENat) :=
  by
    let f : BitString →. BitString := fun w =>
      Part.some (concreteIncidentPairFromEdgeCode w)
    have hf : Partrec f := by
      dsimp only [f]
      exact concreteIncidentPairFromEdgeCode_primrec.to_comp.partrec
    obtain ⟨cMap, hMap⟩ := plainK_partrec_map_le V hV f hf
    obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
    refine ⟨cLength + cMap, fun n e => ?_⟩
    have hrec :
        pairCode (concretePointCode n e.1.1)
            (concreteLineCode n e.1.2) ∈
          f (concreteIncidentEdgeCode n e) := by
      change pairCode (concretePointCode n e.1.1)
          (concreteLineCode n e.1.2) ∈
        Part.some (concreteIncidentPairFromEdgeCode
          (concreteIncidentEdgeCode n e))
      rw [concreteIncidentPairFromEdgeCode_edge]
      exact Part.mem_some _
    calc
      pairPlainK V (concretePointCode n e.1.1)
          (concreteLineCode n e.1.2)
          ≤ plainK V (concreteIncidentEdgeCode n e) +
              (cMap : ENat) :=
        hMap _ _ hrec
      _ ≤ ((concreteIncidentEdgeCode n e).length : ENat) +
            (cLength : ENat) + (cMap : ENat) := by
          gcongr
          exact hLength _
      _ = ((3 * (n + 1) + (cLength + cMap) : Nat) : ENat) := by
          rw [concreteIncidentEdgeCode_length]
          push_cast
          ring

theorem condK_concreteLine_given_point_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ n (e : ConcreteIncidentEdge n),
      condK V (concreteLineCode n e.1.2) (concretePointCode n e.1.1)
        ≤ ((n + 1 + c : Nat) : ENat) :=
  by
    let g : BitString → BitString →. BitString := fun y p =>
      Part.some (concreteLineFromPointCode y p)
    have hg : Partrec (fun q : BitString × BitString => g q.1 q.2) := by
      dsimp only [g]
      exact concreteLineFromPointCode_primrec.to_comp.partrec
    obtain ⟨c, hc⟩ := condK_partrec_cond_map_le V hV g hg
    refine ⟨c, fun n e => ?_⟩
    have hinc : AffineIncidence.Incident e.1.1 e.1.2 :=
      AffineIncidence.mem_incidentEdges_iff.mp e.2
    have hrec :
        concreteLineCode n e.1.2 ∈
          g (concretePointCode n e.1.1)
            (concreteFieldCode n e.1.2.1) := by
      change concreteLineCode n e.1.2 ∈
        Part.some (concreteLineFromPointCode
          (concretePointCode n e.1.1)
          (concreteFieldCode n e.1.2.1))
      rw [concreteLineFromPointCode_incident hinc]
      exact Part.mem_some _
    calc
      condK V (concreteLineCode n e.1.2)
          (concretePointCode n e.1.1)
          ≤ ((concreteFieldCode n e.1.2.1).length : ENat) +
              (c : ENat) :=
        hc _ _ _ hrec
      _ = ((n + 1 + c : Nat) : ENat) := by
          rw [concreteFieldCode_length]
          push_cast
          ring

theorem condK_concretePoint_given_line_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ n (e : ConcreteIncidentEdge n),
      condK V (concretePointCode n e.1.1) (concreteLineCode n e.1.2)
        ≤ ((n + 1 + c : Nat) : ENat) :=
  by
    let g : BitString → BitString →. BitString := fun y p =>
      Part.some (concretePointFromLineCode y p)
    have hg : Partrec (fun q : BitString × BitString => g q.1 q.2) := by
      dsimp only [g]
      exact concretePointFromLineCode_primrec.to_comp.partrec
    obtain ⟨c, hc⟩ := condK_partrec_cond_map_le V hV g hg
    refine ⟨c, fun n e => ?_⟩
    have hinc : AffineIncidence.Incident e.1.1 e.1.2 :=
      AffineIncidence.mem_incidentEdges_iff.mp e.2
    have hrec :
        concretePointCode n e.1.1 ∈
          g (concreteLineCode n e.1.2)
            (concreteFieldCode n e.1.1.1) := by
      change concretePointCode n e.1.1 ∈
        Part.some (concretePointFromLineCode
          (concreteLineCode n e.1.2)
          (concreteFieldCode n e.1.1.1))
      rw [concretePointFromLineCode_incident hinc]
      exact Part.mem_some _
    calc
      condK V (concretePointCode n e.1.1)
          (concreteLineCode n e.1.2)
          ≤ ((concreteFieldCode n e.1.1.1).length : ENat) +
              (c : ENat) :=
        hc _ _ _ hrec
      _ = ((n + 1 + c : Nat) : ENat) := by
          rw [concreteFieldCode_length]
          push_cast
          ring

end Kolmogorov
