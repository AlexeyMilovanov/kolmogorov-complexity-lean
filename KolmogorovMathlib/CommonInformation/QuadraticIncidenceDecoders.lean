import KolmogorovMathlib.CommonInformation.QuadraticModel
import KolmogorovMathlib.CommonInformation.IncidenceCodecs
import KolmogorovMathlib.CommonInformation.IncidenceCoding

/-!
# Executable codecs for the quadratic-extension incidence graph

This file supplies the effective content behind SUV Exercise 311.  Elements of
`ConcreteQuadraticField m` are coded by their two coordinates in the basis
`concreteQuadraticBasis m = (1, quadGen m)` of `QuadraticModel.lean`, each
coordinate being a fixed-width code of a prime-field residue.

Because the structure constants `quadCoeffA m`, `quadCoeffB m` of that basis are
primitive recursive in `m`, all the coordinate arithmetic of the extension is
primitive recursive as well.  Consequently:

* an incident point/line pair is reconstructed from the line plus the point's
  first coordinate (`quadPointFromLineCode`), i.e. from `6 * (m + 1)` bits;
* the line is reconstructed from the point plus the slope
  (`quadLineFromPointCode`), i.e. from `2 * (m + 1)` extra bits;
* both endpoints of an incidence class are reconstructed from the class key
  plus two prime-field parameters (`quadClassPointCode`, `quadClassLineCode`).
-/

namespace Kolmogorov

open AffineIncidence

/-! ### Fixed-width codes over the quadratic extension -/

/-- A coordinate code for an element of the quadratic extension. -/
noncomputable def quadraticFieldCode (m : Nat) (a : ConcreteQuadraticField m) : BitString :=
  concreteFieldCode m ((concreteQuadraticBasis m).repr a 0) ++
  concreteFieldCode m ((concreteQuadraticBasis m).repr a 1)

/-- An element of the quadratic extension is coded by `2 * (m + 1)` bits, one
fixed-width block per basis coordinate. -/
@[simp]
lemma quadraticFieldCode_length (m : Nat) (a : ConcreteQuadraticField m) :
    (quadraticFieldCode m a).length = 2 * (m + 1) := by
  simp [quadraticFieldCode]
  omega

/-- Distinct elements of the quadratic extension have distinct codes. -/
lemma quadraticFieldCode_injective (m : Nat) :
    Function.Injective (quadraticFieldCode m) := by
  intro a b hab
  apply (concreteQuadraticBasis m).repr.injective
  ext i
  fin_cases i
  · apply concreteFieldCode_injective m
    have htake := congrArg (List.take (m + 1)) hab
    simpa [quadraticFieldCode] using htake
  · apply concreteFieldCode_injective m
    have hdrop := congrArg (List.drop (m + 1)) hab
    simpa [quadraticFieldCode] using hdrop

/-- Encodes an affine point over the quadratic field (4 prime-field codes total). -/
noncomputable def quadraticPointCode (m : Nat) (p : Point (ConcreteQuadraticField m)) : BitString :=
  quadraticFieldCode m p.1 ++ quadraticFieldCode m p.2

/-- A point over the quadratic extension is coded by `4 * (m + 1)` bits, two
coordinates of two blocks each. -/
@[simp]
lemma quadraticPointCode_length (m : Nat) (p : Point (ConcreteQuadraticField m)) :
    (quadraticPointCode m p).length = 4 * (m + 1) := by
  simp [quadraticPointCode]
  omega

/-- Distinct points over the quadratic extension have distinct codes. -/
lemma quadraticPointCode_injective (m : Nat) :
    Function.Injective (quadraticPointCode m) := by
  intro p q hpq
  apply Prod.ext
  · apply quadraticFieldCode_injective m
    have htake := congrArg (List.take (2 * (m + 1))) hpq
    simpa [quadraticPointCode] using htake
  · apply quadraticFieldCode_injective m
    have hdrop := congrArg (List.drop (2 * (m + 1))) hpq
    simpa [quadraticPointCode] using hdrop

/-- Encodes an affine line over the quadratic field (4 prime-field codes total). -/
noncomputable def quadraticLineCode (m : Nat) (ell : Line (ConcreteQuadraticField m)) : BitString :=
  quadraticFieldCode m ell.1 ++ quadraticFieldCode m ell.2

/-- A line over the quadratic extension is coded by `4 * (m + 1)` bits, its slope
and its intercept. -/
@[simp]
lemma quadraticLineCode_length (m : Nat) (ell : Line (ConcreteQuadraticField m)) :
    (quadraticLineCode m ell).length = 4 * (m + 1) := by
  simp [quadraticLineCode]
  omega

/-- Distinct lines over the quadratic extension have distinct codes. -/
lemma quadraticLineCode_injective (m : Nat) :
    Function.Injective (quadraticLineCode m) := by
  intro ell ell' hell
  apply Prod.ext
  · apply quadraticFieldCode_injective m
    have htake := congrArg (List.take (2 * (m + 1))) hell
    simpa [quadraticLineCode] using htake
  · apply quadraticFieldCode_injective m
    have hdrop := congrArg (List.drop (2 * (m + 1))) hell
    simpa [quadraticLineCode] using hdrop

/-! ### Reading fixed-width chunks -/

/-- The `i`-th `w`-bit chunk of a bit string, decoded as a natural number. -/
def quadChunk (w i : Nat) (s : BitString) : Nat :=
  decodeFixedWidthNatCode ((s.drop (i * w)).take w)

/-- Reading the `i`-th block of width `w` out of a string is primitive recursive in
the width, the index and the string. -/
lemma quadChunk_primrec :
    Primrec (fun q : (Nat × Nat) × BitString => quadChunk q.1.1 q.1.2 q.2) := by
  have hoffset : Primrec (fun q : (Nat × Nat) × BitString => q.1.2 * q.1.1) :=
    Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)
  have hdrop : Primrec (fun q : (Nat × Nat) × BitString => q.2.drop (q.1.2 * q.1.1)) :=
    primrec_list_drop.comp Primrec.snd hoffset
  have htake : Primrec (fun q : (Nat × Nat) × BitString =>
      (q.2.drop (q.1.2 * q.1.1)).take q.1.1) :=
    primrec_list_take.comp hdrop (Primrec.fst.comp Primrec.fst)
  exact (decodeFixedWidthNatCode_primrec.comp htake).of_eq (fun _ => rfl)

/-- **Reading one block out of a concatenation of equal-width blocks.** If the prefix
`pre` occupies exactly the first `i` blocks of width `w` and `c` is the next block, then
the `i`-th `w`-wide chunk of `pre ++ (c ++ rest)` decodes `c`, whatever follows. All the
fixed-arity chunk lemmas below are instances of this one. -/
lemma quadChunk_append_block (w i : Nat) (pre c rest : BitString)
    (hpre : pre.length = i * w) (hc : c.length = w) :
    quadChunk w i (pre ++ (c ++ rest)) = decodeFixedWidthNatCode c := by
  simp only [quadChunk]
  rw [List.drop_left' hpre, List.take_left' hc]

/-- The zeroth block of the concatenation of two blocks of width `w` decodes the
first one. -/
lemma quadChunk_two_zero (w : Nat) (c0 c1 : BitString)
    (h0 : c0.length = w) :
    quadChunk w 0 (c0 ++ c1) = decodeFixedWidthNatCode c0 := by
  simpa using quadChunk_append_block w 0 [] c0 c1 (by simp) h0

/-- A string of length `w` is its own prefix of length `w`. -/
lemma quadChunk_take_self (w : Nat) (c : BitString) (h : c.length = w) :
    c.take w = c := by
  subst h; simp

/-- The first block of the concatenation of two blocks of width `w` decodes the
second one. -/
lemma quadChunk_two_one (w : Nat) (c0 c1 : BitString)
    (h0 : c0.length = w) (h1 : c1.length = w) :
    quadChunk w 1 (c0 ++ c1) = decodeFixedWidthNatCode c1 := by
  simpa using quadChunk_append_block w 1 c0 c1 [] (by simp [h0]) h1

/-- The zeroth block of a concatenation of four blocks of width `w` decodes the
first one. -/
lemma quadChunk_four_zero (w : Nat) (c0 c1 c2 c3 : BitString)
    (h0 : c0.length = w) :
    quadChunk w 0 ((c0 ++ c1) ++ (c2 ++ c3)) = decodeFixedWidthNatCode c0 := by
  simpa [List.append_assoc] using
    quadChunk_append_block w 0 [] c0 (c1 ++ (c2 ++ c3)) (by simp) h0

/-- The first block of a concatenation of four blocks of width `w` decodes the
second one. -/
lemma quadChunk_four_one (w : Nat) (c0 c1 c2 c3 : BitString)
    (h0 : c0.length = w) (h1 : c1.length = w) :
    quadChunk w 1 ((c0 ++ c1) ++ (c2 ++ c3)) = decodeFixedWidthNatCode c1 := by
  simpa [List.append_assoc] using
    quadChunk_append_block w 1 c0 c1 (c2 ++ c3) (by simp [h0]) h1

/-- The second block of a concatenation of four blocks of width `w` decodes the
third one. -/
lemma quadChunk_four_two (w : Nat) (c0 c1 c2 c3 : BitString)
    (h0 : c0.length = w) (h1 : c1.length = w) (h2 : c2.length = w) :
    quadChunk w 2 ((c0 ++ c1) ++ (c2 ++ c3)) = decodeFixedWidthNatCode c2 := by
  have h01 : (c0 ++ c1).length = 2 * w := by rw [List.length_append, h0, h1]; ring
  simpa [List.append_assoc] using quadChunk_append_block w 2 (c0 ++ c1) c2 c3 h01 h2

/-- The third block of a concatenation of four blocks of width `w` decodes the last
one. -/
lemma quadChunk_four_three (w : Nat) (c0 c1 c2 c3 : BitString)
    (h0 : c0.length = w) (h1 : c1.length = w) (h2 : c2.length = w) (h3 : c3.length = w) :
    quadChunk w 3 ((c0 ++ c1) ++ (c2 ++ c3)) = decodeFixedWidthNatCode c3 := by
  have h012 : ((c0 ++ c1) ++ c2).length = 3 * w := by
    rw [List.length_append, List.length_append, h0, h1, h2]; ring
  simpa [List.append_assoc] using
    quadChunk_append_block w 3 ((c0 ++ c1) ++ c2) c3 [] h012 h3

/-- Decoding the fixed-width code of a prime-field element returns its
representative. -/
lemma decode_concreteFieldCode (m : Nat) (u : ConcreteField m) :
    decodeFixedWidthNatCode (concreteFieldCode m u) = u.val := by
  simp [concreteFieldCode]

/-- The four chunks of the code of a pair of extension elements. -/
lemma quadChunk_append_field (m : Nat) (a b : ConcreteQuadraticField m) :
    quadChunk (m + 1) 0 (quadraticFieldCode m a ++ quadraticFieldCode m b) =
        ((concreteQuadraticBasis m).repr a 0).val ∧
      quadChunk (m + 1) 1 (quadraticFieldCode m a ++ quadraticFieldCode m b) =
        ((concreteQuadraticBasis m).repr a 1).val ∧
      quadChunk (m + 1) 2 (quadraticFieldCode m a ++ quadraticFieldCode m b) =
        ((concreteQuadraticBasis m).repr b 0).val ∧
      quadChunk (m + 1) 3 (quadraticFieldCode m a ++ quadraticFieldCode m b) =
        ((concreteQuadraticBasis m).repr b 1).val := by
  have h0 := concreteFieldCode_length m ((concreteQuadraticBasis m).repr a 0)
  have h1 := concreteFieldCode_length m ((concreteQuadraticBasis m).repr a 1)
  have h2 := concreteFieldCode_length m ((concreteQuadraticBasis m).repr b 0)
  have h3 := concreteFieldCode_length m ((concreteQuadraticBasis m).repr b 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show quadraticFieldCode m a ++ quadraticFieldCode m b =
        (concreteFieldCode m ((concreteQuadraticBasis m).repr a 0) ++
          concreteFieldCode m ((concreteQuadraticBasis m).repr a 1)) ++
        (concreteFieldCode m ((concreteQuadraticBasis m).repr b 0) ++
          concreteFieldCode m ((concreteQuadraticBasis m).repr b 1)) from rfl,
      quadChunk_four_zero _ _ _ _ _ h0, decode_concreteFieldCode]
  · rw [show quadraticFieldCode m a ++ quadraticFieldCode m b =
        (concreteFieldCode m ((concreteQuadraticBasis m).repr a 0) ++
          concreteFieldCode m ((concreteQuadraticBasis m).repr a 1)) ++
        (concreteFieldCode m ((concreteQuadraticBasis m).repr b 0) ++
          concreteFieldCode m ((concreteQuadraticBasis m).repr b 1)) from rfl,
      quadChunk_four_one _ _ _ _ _ h0 h1, decode_concreteFieldCode]
  · rw [show quadraticFieldCode m a ++ quadraticFieldCode m b =
        (concreteFieldCode m ((concreteQuadraticBasis m).repr a 0) ++
          concreteFieldCode m ((concreteQuadraticBasis m).repr a 1)) ++
        (concreteFieldCode m ((concreteQuadraticBasis m).repr b 0) ++
          concreteFieldCode m ((concreteQuadraticBasis m).repr b 1)) from rfl,
      quadChunk_four_two _ _ _ _ _ h0 h1 h2, decode_concreteFieldCode]
  · rw [show quadraticFieldCode m a ++ quadraticFieldCode m b =
        (concreteFieldCode m ((concreteQuadraticBasis m).repr a 0) ++
          concreteFieldCode m ((concreteQuadraticBasis m).repr a 1)) ++
        (concreteFieldCode m ((concreteQuadraticBasis m).repr b 0) ++
          concreteFieldCode m ((concreteQuadraticBasis m).repr b 1)) from rfl,
      quadChunk_four_three _ _ _ _ _ h0 h1 h2 h3, decode_concreteFieldCode]

/-- The zeroth block of the code of an extension element is the representative of
its first basis coordinate. -/
lemma quadChunk_fieldCode_zero (m : Nat) (a : ConcreteQuadraticField m) :
    quadChunk (m + 1) 0 (quadraticFieldCode m a) =
      ((concreteQuadraticBasis m).repr a 0).val := by
  rw [quadraticFieldCode,
    quadChunk_two_zero _ _ _ (concreteFieldCode_length m _), decode_concreteFieldCode]

/-- The first block of the code of an extension element is the representative of its
second basis coordinate. -/
lemma quadChunk_fieldCode_one (m : Nat) (a : ConcreteQuadraticField m) :
    quadChunk (m + 1) 1 (quadraticFieldCode m a) =
      ((concreteQuadraticBasis m).repr a 1).val := by
  rw [quadraticFieldCode,
    quadChunk_two_one _ _ _ (concreteFieldCode_length m _) (concreteFieldCode_length m _),
    decode_concreteFieldCode]

/-! ### Coordinate arithmetic at the level of natural numbers -/

/-- Casting the representative of a prime-field element back into the field returns
that element. -/
lemma concreteField_natCast_val (m : Nat) (u : ConcreteField m) :
    ((u.val : Nat) : ConcreteField m) = u := by
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- In the prime field, the cast of `p - k` for `k ≤ p` is the negative of the cast
of `k`. -/
lemma concreteField_cast_prime_sub (m k : Nat) (h : k ≤ concretePrime m) :
    ((concretePrime m - k : Nat) : ConcreteField m) = -((k : Nat) : ConcreteField m) := by
  rw [Nat.cast_sub h]
  simp

/-- Coordinate `0` of a product, as a natural number. -/
def quadMulNat0 (m a0 a1 t0 t1 : Nat) : Nat :=
  (a0 * t0 + (concretePrime m - quadCoeffB m) * (a1 * t1)) % concretePrime m

/-- Coordinate `1` of a product, as a natural number. -/
def quadMulNat1 (m a0 a1 t0 t1 : Nat) : Nat :=
  (a0 * t1 + a1 * t0 + (concretePrime m - quadCoeffA m) * (a1 * t1)) % concretePrime m

/-- The first coordinate of a product, computed on representatives, is a residue
below `concretePrime m`. -/
lemma quadMulNat0_lt (m a0 a1 t0 t1 : Nat) :
    quadMulNat0 m a0 a1 t0 t1 < concretePrime m :=
  Nat.mod_lt _ (concretePrime_prime m).pos

/-- The second coordinate of a product, computed on representatives, is a residue
below `concretePrime m`. -/
lemma quadMulNat1_lt (m a0 a1 t0 t1 : Nat) :
    quadMulNat1 m a0 a1 t0 t1 < concretePrime m :=
  Nat.mod_lt _ (concretePrime_prime m).pos

/-- The representative arithmetic `quadMulNat0`, `quadMulNat1` computes the two
basis coordinates of a product in the quadratic extension. -/
lemma quadMul_repr (m : Nat) (a t : ConcreteQuadraticField m) :
    ((concreteQuadraticBasis m).repr (a * t) 0).val =
        quadMulNat0 m ((concreteQuadraticBasis m).repr a 0).val
          ((concreteQuadraticBasis m).repr a 1).val
          ((concreteQuadraticBasis m).repr t 0).val
          ((concreteQuadraticBasis m).repr t 1).val ∧
      ((concreteQuadraticBasis m).repr (a * t) 1).val =
        quadMulNat1 m ((concreteQuadraticBasis m).repr a 0).val
          ((concreteQuadraticBasis m).repr a 1).val
          ((concreteQuadraticBasis m).repr t 0).val
          ((concreteQuadraticBasis m).repr t 1).val := by
  set a0 := (concreteQuadraticBasis m).repr a 0 with ha0
  set a1 := (concreteQuadraticBasis m).repr a 1 with ha1
  set t0 := (concreteQuadraticBasis m).repr t 0 with ht0
  set t1 := (concreteQuadraticBasis m).repr t 1 with ht1
  have hexp : a * t =
      quadMk m (a0 * t0 - quadFieldB m * (a1 * t1))
        (a0 * t1 + a1 * t0 - quadFieldA m * (a1 * t1)) := by
    conv_lhs => rw [← quadMk_repr_self m a, ← quadMk_repr_self m t]
    rw [quadMk_mul]
  have hcast0 :
      ((a0.val * t0.val + (concretePrime m - quadCoeffB m) * (a1.val * t1.val) : Nat) :
          ConcreteField m) = a0 * t0 - quadFieldB m * (a1 * t1) := by
    push_cast [concreteField_cast_prime_sub m (quadCoeffB m) (quadCoeffB_lt m).le]
    rw [concreteField_natCast_val, concreteField_natCast_val, concreteField_natCast_val,
      concreteField_natCast_val]
    ring
  have hcast1 :
      ((a0.val * t1.val + a1.val * t0.val +
            (concretePrime m - quadCoeffA m) * (a1.val * t1.val) : Nat) :
          ConcreteField m) = a0 * t1 + a1 * t0 - quadFieldA m * (a1 * t1) := by
    push_cast [concreteField_cast_prime_sub m (quadCoeffA m) (quadCoeffA_lt m).le]
    rw [concreteField_natCast_val, concreteField_natCast_val, concreteField_natCast_val,
      concreteField_natCast_val]
    ring
  constructor
  · rw [hexp, quadMk_repr_zero, ← hcast0, ZMod.val_natCast]
    rfl
  · rw [hexp, quadMk_repr_one, ← hcast1, ZMod.val_natCast]
    rfl

/-- Basis coordinates of a sum are the sums of the coordinates modulo the prime. -/
lemma quadAdd_repr (m : Nat) (u b : ConcreteQuadraticField m) (i : Fin 2) :
    ((concreteQuadraticBasis m).repr (u + b) i).val =
      (((concreteQuadraticBasis m).repr u i).val +
        ((concreteQuadraticBasis m).repr b i).val) % concretePrime m := by
  have hsum : (concreteQuadraticBasis m).repr (u + b) i =
      (concreteQuadraticBasis m).repr u i + (concreteQuadraticBasis m).repr b i := by
    simp
  rw [hsum]
  rw [show (concreteQuadraticBasis m).repr u i + (concreteQuadraticBasis m).repr b i =
      (((((concreteQuadraticBasis m).repr u i).val +
        ((concreteQuadraticBasis m).repr b i).val : Nat)) : ConcreteField m) by
    push_cast
    rw [concreteField_natCast_val, concreteField_natCast_val]]
  rw [ZMod.val_natCast]

/-- Basis coordinates of a difference are the differences of the coordinates modulo
the prime, computed with a shift by the prime to stay in `ℕ`. -/
lemma quadSub_repr (m : Nat) (y u : ConcreteQuadraticField m) (i : Fin 2) :
    ((concreteQuadraticBasis m).repr (y - u) i).val =
      (((concreteQuadraticBasis m).repr y i).val + concretePrime m -
        ((concreteQuadraticBasis m).repr u i).val) % concretePrime m := by
  have hsub : (concreteQuadraticBasis m).repr (y - u) i =
      (concreteQuadraticBasis m).repr y i - (concreteQuadraticBasis m).repr u i := by
    simp
  have hle : ((concreteQuadraticBasis m).repr u i).val ≤
      ((concreteQuadraticBasis m).repr y i).val + concretePrime m := by
    have := ZMod.val_lt ((concreteQuadraticBasis m).repr u i)
    omega
  have hcast :
      (((((concreteQuadraticBasis m).repr y i).val + concretePrime m -
          ((concreteQuadraticBasis m).repr u i).val : Nat)) : ConcreteField m) =
        (concreteQuadraticBasis m).repr y i - (concreteQuadraticBasis m).repr u i := by
    rw [Nat.cast_sub hle]
    push_cast
    rw [concreteField_natCast_val, concreteField_natCast_val]
    simp
  rw [hsub, ← hcast, ZMod.val_natCast]

/-- Primitive recursiveness of the first product coordinate, as a function of the
tuple `((((m, a0), (a1, t0)), t1)`. -/
lemma quadMulNat0_primrec :
    Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat =>
      quadMulNat0 v.1.1.1 v.1.1.2 v.1.2.1 v.1.2.2 v.2) := by
  have hm : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha0 : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ha1 : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ht0 : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ht1 : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.2) := Primrec.snd
  have hp : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat =>
      concretePrime v.1.1.1) := boundedPrimeSearch_primrec.comp hm
  exact (Primrec.nat_mod.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp ha0 ht0)
      (Primrec.nat_mul.comp
        (Primrec.nat_sub.comp hp (quadCoeffB_primrec.comp hm))
        (Primrec.nat_mul.comp ha1 ht1))) hp).of_eq (fun _ => rfl)

/-- Primitive recursiveness of the second product coordinate. -/
lemma quadMulNat1_primrec :
    Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat =>
      quadMulNat1 v.1.1.1 v.1.1.2 v.1.2.1 v.1.2.2 v.2) := by
  have hm : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha0 : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ha1 : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ht0 : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ht1 : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.2) := Primrec.snd
  have hp : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat =>
      concretePrime v.1.1.1) := boundedPrimeSearch_primrec.comp hm
  exact (Primrec.nat_mod.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp ha0 ht1)
        (Primrec.nat_mul.comp ha1 ht0))
      (Primrec.nat_mul.comp
        (Primrec.nat_sub.comp hp (quadCoeffA_primrec.comp hm))
        (Primrec.nat_mul.comp ha1 ht1))) hp).of_eq (fun _ => rfl)

/-! ### Reconstructing a point from a line -/

/-- From the code of a line and the code of the point's first coordinate,
reconstruct the code of the incident point. -/
def quadPointFromLineCode (lineCode program : BitString) : BitString :=
  program ++
    (fixedWidthNatCode
        ((quadMulNat0 (lineCode.length / 4 - 1)
            (quadChunk (lineCode.length / 4) 0 lineCode)
            (quadChunk (lineCode.length / 4) 1 lineCode)
            (quadChunk (lineCode.length / 4) 0 program)
            (quadChunk (lineCode.length / 4) 1 program) +
          quadChunk (lineCode.length / 4) 2 lineCode) %
          concretePrime (lineCode.length / 4 - 1))
        (lineCode.length / 4) ++
      fixedWidthNatCode
        ((quadMulNat1 (lineCode.length / 4 - 1)
            (quadChunk (lineCode.length / 4) 0 lineCode)
            (quadChunk (lineCode.length / 4) 1 lineCode)
            (quadChunk (lineCode.length / 4) 0 program)
            (quadChunk (lineCode.length / 4) 1 program) +
          quadChunk (lineCode.length / 4) 3 lineCode) %
          concretePrime (lineCode.length / 4 - 1))
        (lineCode.length / 4))

/-- The four blocks of the code of a line are the two coordinates of its slope
followed by the two coordinates of its intercept. -/
lemma quadChunk_lineCode (m : Nat) (ell : Line (ConcreteQuadraticField m)) :
    quadChunk (m + 1) 0 (quadraticLineCode m ell) =
        ((concreteQuadraticBasis m).repr ell.1 0).val ∧
      quadChunk (m + 1) 1 (quadraticLineCode m ell) =
        ((concreteQuadraticBasis m).repr ell.1 1).val ∧
      quadChunk (m + 1) 2 (quadraticLineCode m ell) =
        ((concreteQuadraticBasis m).repr ell.2 0).val ∧
      quadChunk (m + 1) 3 (quadraticLineCode m ell) =
        ((concreteQuadraticBasis m).repr ell.2 1).val :=
  quadChunk_append_field m ell.1 ell.2

/-- The four blocks of the code of a point are the two coordinates of its abscissa
followed by the two coordinates of its ordinate. -/
lemma quadChunk_pointCode (m : Nat) (p : Point (ConcreteQuadraticField m)) :
    quadChunk (m + 1) 0 (quadraticPointCode m p) =
        ((concreteQuadraticBasis m).repr p.1 0).val ∧
      quadChunk (m + 1) 1 (quadraticPointCode m p) =
        ((concreteQuadraticBasis m).repr p.1 1).val ∧
      quadChunk (m + 1) 2 (quadraticPointCode m p) =
        ((concreteQuadraticBasis m).repr p.2 0).val ∧
      quadChunk (m + 1) 3 (quadraticPointCode m p) =
        ((concreteQuadraticBasis m).repr p.2 1).val :=
  quadChunk_append_field m p.1 p.2

/-- For an incident pair, the line code together with the code of the point's
abscissa returns the code of the point. -/
lemma quadPointFromLineCode_incident {m : Nat} {p : Point (ConcreteQuadraticField m)}
    {ell : Line (ConcreteQuadraticField m)} (hinc : Incident p ell) :
    quadPointFromLineCode (quadraticLineCode m ell) (quadraticFieldCode m p.1) =
      quadraticPointCode m p := by
  have hwidth : (quadraticLineCode m ell).length / 4 = m + 1 := by
    rw [quadraticLineCode_length]
    omega
  obtain ⟨hc0, hc1, hc2, hc3⟩ := quadChunk_lineCode m ell
  have ht0 := quadChunk_fieldCode_zero m p.1
  have ht1 := quadChunk_fieldCode_one m p.1
  obtain ⟨hm0, hm1⟩ := quadMul_repr m ell.1 p.1
  have hp2 : p.2 = ell.1 * p.1 + ell.2 := hinc
  have hval0 :
      (quadMulNat0 m ((concreteQuadraticBasis m).repr ell.1 0).val
          ((concreteQuadraticBasis m).repr ell.1 1).val
          ((concreteQuadraticBasis m).repr p.1 0).val
          ((concreteQuadraticBasis m).repr p.1 1).val +
        ((concreteQuadraticBasis m).repr ell.2 0).val) % concretePrime m =
        ((concreteQuadraticBasis m).repr p.2 0).val := by
    rw [hp2, quadAdd_repr, hm0]
  have hval1 :
      (quadMulNat1 m ((concreteQuadraticBasis m).repr ell.1 0).val
          ((concreteQuadraticBasis m).repr ell.1 1).val
          ((concreteQuadraticBasis m).repr p.1 0).val
          ((concreteQuadraticBasis m).repr p.1 1).val +
        ((concreteQuadraticBasis m).repr ell.2 1).val) % concretePrime m =
        ((concreteQuadraticBasis m).repr p.2 1).val := by
    rw [hp2, quadAdd_repr, hm1]
  simp only [quadPointFromLineCode, hwidth, Nat.add_sub_cancel, hc0, hc1, hc2, hc3,
    ht0, ht1, hval0, hval1]
  rfl

/-- Recovering a point from a line code and an abscissa code is primitive recursive. -/
lemma quadPointFromLineCode_primrec : Primrec₂ quadPointFromLineCode := by
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
  have ha0 := hchunk 0 Prod.fst Primrec.fst
  have ha1 := hchunk 1 Prod.fst Primrec.fst
  have hb0 := hchunk 2 Prod.fst Primrec.fst
  have hb1 := hchunk 3 Prod.fst Primrec.fst
  have ht0 := hchunk 0 Prod.snd Primrec.snd
  have ht1 := hchunk 1 Prod.snd Primrec.snd
  have harg : Primrec (fun q : BitString × BitString =>
      ((((q.1.length / 4 - 1, quadChunk (q.1.length / 4) 0 q.1),
        (quadChunk (q.1.length / 4) 1 q.1, quadChunk (q.1.length / 4) 0 q.2)),
        quadChunk (q.1.length / 4) 1 q.2) : ((Nat × Nat) × Nat × Nat) × Nat)) :=
    Primrec.pair (Primrec.pair (Primrec.pair hm ha0) (Primrec.pair ha1 ht0)) ht1
  have hmul0 := quadMulNat0_primrec.comp harg
  have hmul1 := quadMulNat1_primrec.comp harg
  have hcode0 := fixedWidthNatCode_primrec.comp
    (Primrec.pair (Primrec.nat_mod.comp (Primrec.nat_add.comp hmul0 hb0) hprime) hwidth)
  have hcode1 := fixedWidthNatCode_primrec.comp
    (Primrec.pair (Primrec.nat_mod.comp (Primrec.nat_add.comp hmul1 hb1) hprime) hwidth)
  exact ((Primrec.list_append.comp Primrec.snd
    (Primrec.list_append.comp hcode0 hcode1)).of_eq (fun _ => rfl)).to₂

end Kolmogorov
