import KolmogorovMathlib.CommonInformation.QuadraticEdgeDecoders

/-!
# Class-key codecs for the quadratic-extension incidence graph

An incident pair `(p, ell)` over `ConcreteQuadraticField m` is described by six
base-field coordinates.  Writing

* `ell.1 = f + r * α`, `p.1 = g + t * α`, `ell.2 = h + s' * α`,

the *class key* of the pair is the triple `(r, t, s)` with `s = s' + f * t`.  It
occupies `3 * (m + 1)` bits.  Given the key,

* the point `p` is recovered from the two extra coordinates `(g, v₀)`, because
  the second coordinate of `p.2` equals `s + r * g - A * (r * t)`;
* the line `ell` is recovered from the two extra coordinates `(f, h)`, because
  `s' = s - f * t`.

Each of these programs is `2 * (m + 1)` bits long, and both decoders are
primitive recursive.  This is exactly the coding behind the common-information
witness `(3n/2, n, n)` of SUV Exercise 311, with `n = 2 * m`.
-/

namespace Kolmogorov

open AffineIncidence

/-! ### Base-field coordinate arithmetic -/

/-- The second coordinate of the point, as a natural number:
`s + r * g - A * (r * t)`. -/
def quadClassV1Nat (m r t s g : Nat) : Nat :=
  (s + r * g + (concretePrime m - quadCoeffA m) * (r * t)) % concretePrime m

/-- The second coordinate of the intercept, as a natural number: `s - f * t`. -/
def quadClassS0Nat (m t s f : Nat) : Nat :=
  (s + concretePrime m * concretePrime m - f * t) % concretePrime m

lemma quadClassV1Nat_val (m : Nat) (r t s g : ConcreteField m) :
    quadClassV1Nat m r.val t.val s.val g.val =
      (s + r * g - quadFieldA m * (r * t)).val := by
  have hcast :
      ((s.val + r.val * g.val +
          (concretePrime m - quadCoeffA m) * (r.val * t.val) : Nat) : ConcreteField m) =
        s + r * g - quadFieldA m * (r * t) := by
    push_cast [concreteField_cast_prime_sub m (quadCoeffA m) (quadCoeffA_lt m).le]
    rw [concreteField_natCast_val, concreteField_natCast_val, concreteField_natCast_val,
      concreteField_natCast_val]
    ring
  rw [← hcast, ZMod.val_natCast]
  rfl

lemma quadClassS0Nat_val (m : Nat) (t s f : ConcreteField m) :
    quadClassS0Nat m t.val s.val f.val = (s - f * t).val := by
  have hlt : f.val * t.val ≤ concretePrime m * concretePrime m :=
    Nat.mul_le_mul (ZMod.val_lt f).le (ZMod.val_lt t).le
  have hle : f.val * t.val ≤ s.val + concretePrime m * concretePrime m := by omega
  have hcast :
      ((s.val + concretePrime m * concretePrime m - f.val * t.val : Nat) :
          ConcreteField m) = s - f * t := by
    rw [Nat.cast_sub hle]
    push_cast
    rw [concreteField_natCast_val, concreteField_natCast_val, concreteField_natCast_val]
    simp
  rw [← hcast, ZMod.val_natCast]
  rfl

/-! ### Element-level coordinates of sums and products -/

lemma quadRepr_add (m : Nat) (u v : ConcreteQuadraticField m) (i : Fin 2) :
    (concreteQuadraticBasis m).repr (u + v) i =
      (concreteQuadraticBasis m).repr u i + (concreteQuadraticBasis m).repr v i := by
  simp

lemma quadRepr_mul_one (m : Nat) (a u : ConcreteQuadraticField m) :
    (concreteQuadraticBasis m).repr (a * u) 1 =
      (concreteQuadraticBasis m).repr a 0 * (concreteQuadraticBasis m).repr u 1 +
        (concreteQuadraticBasis m).repr a 1 * (concreteQuadraticBasis m).repr u 0 -
      quadFieldA m *
        ((concreteQuadraticBasis m).repr a 1 * (concreteQuadraticBasis m).repr u 1) := by
  conv_lhs => rw [← quadMk_repr_self m a, ← quadMk_repr_self m u]
  rw [quadMk_mul, quadMk_repr_one]

/-! ### The class key and its two programs -/

/-- The `3 * (m + 1)`-bit class key `(r, t, s)`. -/
noncomputable def quadClassKeyCode (m : Nat) (r t s : ConcreteField m) : BitString :=
  concreteFieldCode m r ++ (concreteFieldCode m t ++ concreteFieldCode m s)

@[simp]
lemma quadClassKeyCode_length (m : Nat) (r t s : ConcreteField m) :
    (quadClassKeyCode m r t s).length = 3 * (m + 1) := by
  simp [quadClassKeyCode]
  ring

/-- The class key of an incident pair. -/
noncomputable def quadClassKeyOf (m : Nat) (p : Point (ConcreteQuadraticField m))
    (ell : Line (ConcreteQuadraticField m)) : BitString :=
  quadClassKeyCode m ((concreteQuadraticBasis m).repr ell.1 1)
    ((concreteQuadraticBasis m).repr p.1 1)
    ((concreteQuadraticBasis m).repr ell.2 1 +
      (concreteQuadraticBasis m).repr ell.1 0 * (concreteQuadraticBasis m).repr p.1 1)

@[simp]
lemma quadClassKeyOf_length (m : Nat) (p : Point (ConcreteQuadraticField m))
    (ell : Line (ConcreteQuadraticField m)) :
    (quadClassKeyOf m p ell).length = 3 * (m + 1) := by
  simp [quadClassKeyOf]

/-- The `2 * (m + 1)`-bit program describing the point inside its class. -/
noncomputable def quadClassPointProgram (m : Nat)
    (p : Point (ConcreteQuadraticField m)) : BitString :=
  concreteFieldCode m ((concreteQuadraticBasis m).repr p.1 0) ++
    concreteFieldCode m ((concreteQuadraticBasis m).repr p.2 0)

@[simp]
lemma quadClassPointProgram_length (m : Nat) (p : Point (ConcreteQuadraticField m)) :
    (quadClassPointProgram m p).length = 2 * (m + 1) := by
  simp [quadClassPointProgram]
  ring

/-- The `2 * (m + 1)`-bit program describing the line inside its class. -/
noncomputable def quadClassLineProgram (m : Nat)
    (ell : Line (ConcreteQuadraticField m)) : BitString :=
  concreteFieldCode m ((concreteQuadraticBasis m).repr ell.1 0) ++
    concreteFieldCode m ((concreteQuadraticBasis m).repr ell.2 0)

@[simp]
lemma quadClassLineProgram_length (m : Nat) (ell : Line (ConcreteQuadraticField m)) :
    (quadClassLineProgram m ell).length = 2 * (m + 1) := by
  simp [quadClassLineProgram]
  ring

/-! ### Reading the three chunks of a class key -/

lemma quadChunk_three_zero (w : Nat) (c0 c1 c2 : BitString) (h0 : c0.length = w) :
    quadChunk w 0 (c0 ++ (c1 ++ c2)) = decodeFixedWidthNatCode c0 := by
  simp [quadChunk, List.take_left' h0]

lemma quadChunk_three_one (w : Nat) (c0 c1 c2 : BitString)
    (h0 : c0.length = w) (h1 : c1.length = w) :
    quadChunk w 1 (c0 ++ (c1 ++ c2)) = decodeFixedWidthNatCode c1 := by
  simp only [quadChunk, one_mul]
  rw [List.drop_left' h0, List.take_left' h1]

lemma quadChunk_three_two (w : Nat) (c0 c1 c2 : BitString)
    (h0 : c0.length = w) (h1 : c1.length = w) (h2 : c2.length = w) :
    quadChunk w 2 (c0 ++ (c1 ++ c2)) = decodeFixedWidthNatCode c2 := by
  simp only [quadChunk]
  rw [show 2 * w = w + w by ring, ← List.drop_drop, List.drop_left' h0,
    List.drop_left' h1, quadChunk_take_self w c2 h2]

lemma quadChunk_classKey (m : Nat) (r t s : ConcreteField m) :
    quadChunk (m + 1) 0 (quadClassKeyCode m r t s) = r.val ∧
      quadChunk (m + 1) 1 (quadClassKeyCode m r t s) = t.val ∧
      quadChunk (m + 1) 2 (quadClassKeyCode m r t s) = s.val := by
  refine ⟨?_, ?_, ?_⟩
  · rw [quadClassKeyCode, quadChunk_three_zero _ _ _ _ (concreteFieldCode_length m r),
      decode_concreteFieldCode]
  · rw [quadClassKeyCode, quadChunk_three_one _ _ _ _ (concreteFieldCode_length m r)
      (concreteFieldCode_length m t), decode_concreteFieldCode]
  · rw [quadClassKeyCode, quadChunk_three_two _ _ _ _ (concreteFieldCode_length m r)
      (concreteFieldCode_length m t) (concreteFieldCode_length m s),
      decode_concreteFieldCode]

lemma quadChunk_fieldPair (m : Nat) (a b : ConcreteField m) :
    quadChunk (m + 1) 0 (concreteFieldCode m a ++ concreteFieldCode m b) = a.val ∧
      quadChunk (m + 1) 1 (concreteFieldCode m a ++ concreteFieldCode m b) = b.val := by
  constructor
  · rw [quadChunk_two_zero _ _ _ (concreteFieldCode_length m a), decode_concreteFieldCode]
  · rw [quadChunk_two_one _ _ _ (concreteFieldCode_length m a) (concreteFieldCode_length m b),
      decode_concreteFieldCode]

/-! ### The two class decoders -/

/-- From the class key and the point's own program, reconstruct the point code. -/
def quadClassPointFromKey (key program : BitString) : BitString :=
  (fixedWidthNatCode (quadChunk (key.length / 3) 0 program) (key.length / 3) ++
      fixedWidthNatCode (quadChunk (key.length / 3) 1 key) (key.length / 3)) ++
    (fixedWidthNatCode (quadChunk (key.length / 3) 1 program) (key.length / 3) ++
      fixedWidthNatCode
        (quadClassV1Nat (key.length / 3 - 1) (quadChunk (key.length / 3) 0 key)
          (quadChunk (key.length / 3) 1 key) (quadChunk (key.length / 3) 2 key)
          (quadChunk (key.length / 3) 0 program))
        (key.length / 3))

/-- From the class key and the line's own program, reconstruct the line code. -/
def quadClassLineFromKey (key program : BitString) : BitString :=
  (fixedWidthNatCode (quadChunk (key.length / 3) 0 program) (key.length / 3) ++
      fixedWidthNatCode (quadChunk (key.length / 3) 0 key) (key.length / 3)) ++
    (fixedWidthNatCode (quadChunk (key.length / 3) 1 program) (key.length / 3) ++
      fixedWidthNatCode
        (quadClassS0Nat (key.length / 3 - 1) (quadChunk (key.length / 3) 1 key)
          (quadChunk (key.length / 3) 2 key) (quadChunk (key.length / 3) 0 program))
        (key.length / 3))

lemma quadClassPointFromKey_incident {m : Nat} {p : Point (ConcreteQuadraticField m)}
    {ell : Line (ConcreteQuadraticField m)} (hinc : Incident p ell) :
    quadClassPointFromKey (quadClassKeyOf m p ell) (quadClassPointProgram m p) =
      quadraticPointCode m p := by
  have hwidth : (quadClassKeyOf m p ell).length / 3 = m + 1 := by
    rw [quadClassKeyOf_length]
    omega
  have hk0 : quadChunk (m + 1) 0 (quadClassKeyOf m p ell) =
      ((concreteQuadraticBasis m).repr ell.1 1).val := (quadChunk_classKey m _ _ _).1
  have hk1 : quadChunk (m + 1) 1 (quadClassKeyOf m p ell) =
      ((concreteQuadraticBasis m).repr p.1 1).val := (quadChunk_classKey m _ _ _).2.1
  have hk2 : quadChunk (m + 1) 2 (quadClassKeyOf m p ell) =
      ((concreteQuadraticBasis m).repr ell.2 1 +
        (concreteQuadraticBasis m).repr ell.1 0 *
          (concreteQuadraticBasis m).repr p.1 1).val := (quadChunk_classKey m _ _ _).2.2
  have hp0 : quadChunk (m + 1) 0 (quadClassPointProgram m p) =
      ((concreteQuadraticBasis m).repr p.1 0).val := (quadChunk_fieldPair m _ _).1
  have hp1 : quadChunk (m + 1) 1 (quadClassPointProgram m p) =
      ((concreteQuadraticBasis m).repr p.2 0).val := (quadChunk_fieldPair m _ _).2
  have hv1 : (concreteQuadraticBasis m).repr p.2 1 =
      ((concreteQuadraticBasis m).repr ell.2 1 +
          (concreteQuadraticBasis m).repr ell.1 0 * (concreteQuadraticBasis m).repr p.1 1) +
        (concreteQuadraticBasis m).repr ell.1 1 * (concreteQuadraticBasis m).repr p.1 0 -
      quadFieldA m *
        ((concreteQuadraticBasis m).repr ell.1 1 * (concreteQuadraticBasis m).repr p.1 1) := by
    have hp2 : p.2 = ell.1 * p.1 + ell.2 := hinc
    rw [hp2, quadRepr_add, quadRepr_mul_one]
    ring
  simp only [quadClassPointFromKey, hwidth,
    Nat.add_sub_cancel, hk0, hk1, hk2, hp0, hp1, quadClassV1Nat_val, ← hv1]
  rfl

lemma quadClassLineFromKey_incident {m : Nat} {p : Point (ConcreteQuadraticField m)}
    {ell : Line (ConcreteQuadraticField m)} :
    quadClassLineFromKey (quadClassKeyOf m p ell) (quadClassLineProgram m ell) =
      quadraticLineCode m ell := by
  have hwidth : (quadClassKeyOf m p ell).length / 3 = m + 1 := by
    rw [quadClassKeyOf_length]
    omega
  have hk0 : quadChunk (m + 1) 0 (quadClassKeyOf m p ell) =
      ((concreteQuadraticBasis m).repr ell.1 1).val := (quadChunk_classKey m _ _ _).1
  have hk1 : quadChunk (m + 1) 1 (quadClassKeyOf m p ell) =
      ((concreteQuadraticBasis m).repr p.1 1).val := (quadChunk_classKey m _ _ _).2.1
  have hk2 : quadChunk (m + 1) 2 (quadClassKeyOf m p ell) =
      ((concreteQuadraticBasis m).repr ell.2 1 +
        (concreteQuadraticBasis m).repr ell.1 0 *
          (concreteQuadraticBasis m).repr p.1 1).val := (quadChunk_classKey m _ _ _).2.2
  have hl0 : quadChunk (m + 1) 0 (quadClassLineProgram m ell) =
      ((concreteQuadraticBasis m).repr ell.1 0).val := (quadChunk_fieldPair m _ _).1
  have hl1 : quadChunk (m + 1) 1 (quadClassLineProgram m ell) =
      ((concreteQuadraticBasis m).repr ell.2 0).val := (quadChunk_fieldPair m _ _).2
  have hs0 : (concreteQuadraticBasis m).repr ell.2 1 =
      ((concreteQuadraticBasis m).repr ell.2 1 +
          (concreteQuadraticBasis m).repr ell.1 0 * (concreteQuadraticBasis m).repr p.1 1) -
        (concreteQuadraticBasis m).repr ell.1 0 * (concreteQuadraticBasis m).repr p.1 1 := by
    ring
  simp only [quadClassLineFromKey, hwidth,
    Nat.add_sub_cancel, hk0, hk1, hk2, hl0, hl1, quadClassS0Nat_val, ← hs0]
  rfl

/-! ### Primitive recursiveness -/

lemma quadClassV1Nat_primrec :
    Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat =>
      quadClassV1Nat v.1.1.1 v.1.1.2 v.1.2.1 v.1.2.2 v.2) := by
  have hm : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ht : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hs : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hg : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat => v.2) := Primrec.snd
  have hp : Primrec (fun v : ((Nat × Nat) × Nat × Nat) × Nat =>
      concretePrime v.1.1.1) := boundedPrimeSearch_primrec.comp hm
  exact (Primrec.nat_mod.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp hs (Primrec.nat_mul.comp hr hg))
      (Primrec.nat_mul.comp
        (Primrec.nat_sub.comp hp (quadCoeffA_primrec.comp hm))
        (Primrec.nat_mul.comp hr ht))) hp).of_eq (fun _ => rfl)

lemma quadClassS0Nat_primrec :
    Primrec (fun v : (Nat × Nat) × Nat × Nat =>
      quadClassS0Nat v.1.1 v.1.2 v.2.1 v.2.2) := by
  have hm : Primrec (fun v : (Nat × Nat) × Nat × Nat => v.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun v : (Nat × Nat) × Nat × Nat => v.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hs : Primrec (fun v : (Nat × Nat) × Nat × Nat => v.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hf : Primrec (fun v : (Nat × Nat) × Nat × Nat => v.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hp : Primrec (fun v : (Nat × Nat) × Nat × Nat =>
      concretePrime v.1.1) := boundedPrimeSearch_primrec.comp hm
  exact (Primrec.nat_mod.comp
    (Primrec.nat_sub.comp
      (Primrec.nat_add.comp hs (Primrec.nat_mul.comp hp hp))
      (Primrec.nat_mul.comp hf ht)) hp).of_eq (fun _ => rfl)

lemma quadClassPointFromKey_primrec : Primrec₂ quadClassPointFromKey := by
  have hwidth : Primrec (fun q : BitString × BitString => q.1.length / 3) :=
    Primrec.nat_div.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 3)
  have hm : Primrec (fun q : BitString × BitString => q.1.length / 3 - 1) :=
    Primrec.nat_sub.comp hwidth (Primrec.const 1)
  have hchunk : ∀ (i : Nat) (sel : BitString × BitString → BitString), Primrec sel →
      Primrec (fun q : BitString × BitString => quadChunk (q.1.length / 3) i (sel q)) := by
    intro i sel hsel
    exact quadChunk_primrec.comp
      (Primrec.pair (Primrec.pair hwidth (Primrec.const i)) hsel)
  have hr := hchunk 0 Prod.fst Primrec.fst
  have ht := hchunk 1 Prod.fst Primrec.fst
  have hs := hchunk 2 Prod.fst Primrec.fst
  have hg := hchunk 0 Prod.snd Primrec.snd
  have hv0 := hchunk 1 Prod.snd Primrec.snd
  have harg : Primrec (fun q : BitString × BitString =>
      ((((q.1.length / 3 - 1, quadChunk (q.1.length / 3) 0 q.1),
        (quadChunk (q.1.length / 3) 1 q.1, quadChunk (q.1.length / 3) 2 q.1)),
        quadChunk (q.1.length / 3) 0 q.2) : ((Nat × Nat) × Nat × Nat) × Nat)) :=
    Primrec.pair (Primrec.pair (Primrec.pair hm hr) (Primrec.pair ht hs)) hg
  have hv1 := quadClassV1Nat_primrec.comp harg
  have hcode0 := fixedWidthNatCode_primrec.comp (Primrec.pair hg hwidth)
  have hcode1 := fixedWidthNatCode_primrec.comp (Primrec.pair ht hwidth)
  have hcode2 := fixedWidthNatCode_primrec.comp (Primrec.pair hv0 hwidth)
  have hcode3 := fixedWidthNatCode_primrec.comp (Primrec.pair hv1 hwidth)
  exact ((Primrec.list_append.comp (Primrec.list_append.comp hcode0 hcode1)
    (Primrec.list_append.comp hcode2 hcode3)).of_eq (fun _ => rfl)).to₂

lemma quadClassLineFromKey_primrec : Primrec₂ quadClassLineFromKey := by
  have hwidth : Primrec (fun q : BitString × BitString => q.1.length / 3) :=
    Primrec.nat_div.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 3)
  have hm : Primrec (fun q : BitString × BitString => q.1.length / 3 - 1) :=
    Primrec.nat_sub.comp hwidth (Primrec.const 1)
  have hchunk : ∀ (i : Nat) (sel : BitString × BitString → BitString), Primrec sel →
      Primrec (fun q : BitString × BitString => quadChunk (q.1.length / 3) i (sel q)) := by
    intro i sel hsel
    exact quadChunk_primrec.comp
      (Primrec.pair (Primrec.pair hwidth (Primrec.const i)) hsel)
  have hr := hchunk 0 Prod.fst Primrec.fst
  have ht := hchunk 1 Prod.fst Primrec.fst
  have hs := hchunk 2 Prod.fst Primrec.fst
  have hf := hchunk 0 Prod.snd Primrec.snd
  have hh := hchunk 1 Prod.snd Primrec.snd
  have harg : Primrec (fun q : BitString × BitString =>
      (((q.1.length / 3 - 1, quadChunk (q.1.length / 3) 1 q.1),
        (quadChunk (q.1.length / 3) 2 q.1, quadChunk (q.1.length / 3) 0 q.2)) :
          (Nat × Nat) × Nat × Nat)) :=
    Primrec.pair (Primrec.pair hm ht) (Primrec.pair hs hf)
  have hs0 := quadClassS0Nat_primrec.comp harg
  have hcode0 := fixedWidthNatCode_primrec.comp (Primrec.pair hf hwidth)
  have hcode1 := fixedWidthNatCode_primrec.comp (Primrec.pair hr hwidth)
  have hcode2 := fixedWidthNatCode_primrec.comp (Primrec.pair hh hwidth)
  have hcode3 := fixedWidthNatCode_primrec.comp (Primrec.pair hs0 hwidth)
  exact ((Primrec.list_append.comp (Primrec.list_append.comp hcode0 hcode1)
    (Primrec.list_append.comp hcode2 hcode3)).of_eq (fun _ => rfl)).to₂

/-! ### The resulting conditional complexity bounds -/

theorem condK_quadraticPoint_given_classKey_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ (m : Nat) (p : Point (ConcreteQuadraticField m))
      (ell : Line (ConcreteQuadraticField m)), Incident p ell →
      condK V (quadraticPointCode m p) (quadClassKeyOf m p ell) ≤
        ((2 * (m + 1) + c : Nat) : ENat) := by
  let g : BitString → BitString →. BitString := fun key prog =>
    Part.some (quadClassPointFromKey key prog)
  have hg : Partrec (fun q : BitString × BitString => g q.1 q.2) :=
    quadClassPointFromKey_primrec.to_comp.partrec
  obtain ⟨c, hc⟩ := condK_partrec_cond_map_le V hV g hg
  refine ⟨c, fun m p ell hinc => ?_⟩
  have hrec : quadraticPointCode m p ∈
      g (quadClassKeyOf m p ell) (quadClassPointProgram m p) := by
    change quadraticPointCode m p ∈
      Part.some (quadClassPointFromKey (quadClassKeyOf m p ell) (quadClassPointProgram m p))
    rw [quadClassPointFromKey_incident hinc]
    exact Part.mem_some _
  calc
    condK V (quadraticPointCode m p) (quadClassKeyOf m p ell)
        ≤ ((quadClassPointProgram m p).length : ENat) + (c : ENat) := hc _ _ _ hrec
    _ = ((2 * (m + 1) + c : Nat) : ENat) := by
        rw [quadClassPointProgram_length]
        push_cast
        ring

theorem condK_quadraticLine_given_classKey_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ (m : Nat) (p : Point (ConcreteQuadraticField m))
      (ell : Line (ConcreteQuadraticField m)),
      condK V (quadraticLineCode m ell) (quadClassKeyOf m p ell) ≤
        ((2 * (m + 1) + c : Nat) : ENat) := by
  let g : BitString → BitString →. BitString := fun key prog =>
    Part.some (quadClassLineFromKey key prog)
  have hg : Partrec (fun q : BitString × BitString => g q.1 q.2) :=
    quadClassLineFromKey_primrec.to_comp.partrec
  obtain ⟨c, hc⟩ := condK_partrec_cond_map_le V hV g hg
  refine ⟨c, fun m p ell => ?_⟩
  have hrec : quadraticLineCode m ell ∈
      g (quadClassKeyOf m p ell) (quadClassLineProgram m ell) := by
    change quadraticLineCode m ell ∈
      Part.some (quadClassLineFromKey (quadClassKeyOf m p ell) (quadClassLineProgram m ell))
    rw [quadClassLineFromKey_incident]
    exact Part.mem_some _
  calc
    condK V (quadraticLineCode m ell) (quadClassKeyOf m p ell)
        ≤ ((quadClassLineProgram m ell).length : ENat) + (c : ENat) := hc _ _ _ hrec
    _ = ((2 * (m + 1) + c : Nat) : ENat) := by
        rw [quadClassLineProgram_length]
        push_cast
        ring

end Kolmogorov
