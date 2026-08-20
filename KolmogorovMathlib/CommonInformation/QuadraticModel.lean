import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree
import KolmogorovMathlib.CommonInformation.ConcreteField

/-!
# A computably presented quadratic extension of the concrete prime field

`ConcreteQuadraticField m` is the Galois field `GF(q ^ 2)` over the concrete
prime field `ConcreteField m` with `q = concretePrime m`.  Mathlib's
construction of this field (and of an arbitrary power basis for it) is
noncomputable, so a coordinate description of its elements carries no
executable content by itself.

This file fixes that by pinning down a *specific* basis whose structure
constants are produced by a primitive-recursive search:

* `quadCoeffA m`, `quadCoeffB m` are the coefficients of the first monic
  quadratic `X ^ 2 + A * X + B` over `ConcreteField m` (in lexicographic order
  of `(A, B)`) that has no root in the prime field; such a polynomial exists
  because the minimal polynomial of a primitive element of `GF(q ^ 2)` is one.
* `quadGen m` is a root of that polynomial inside `GF(q ^ 2)`.
* `concreteQuadraticBasis m` is the basis `(1, quadGen m)`.

The last section records the coordinate arithmetic of this basis
(`quadMk_add`, `quadMk_mul`, ...), which is what makes the Exercise 311 codes
effectively decodable: multiplication of two coordinate pairs is an explicit
polynomial expression in the *computable* structure constants
`quadCoeffA m`, `quadCoeffB m`.
-/

namespace Kolmogorov

open Polynomial

/-- A concrete mathematical `GF(q²)` extension over the concrete prime field. -/
abbrev ConcreteQuadraticField (m : Nat) := GaloisField (concretePrime m) 2

noncomputable instance concreteQuadraticFieldFintype (m : Nat) :
    Fintype (ConcreteQuadraticField m) :=
  Fintype.ofFinite (ConcreteQuadraticField m)

noncomputable instance concreteQuadraticFieldDecidableEq (m : Nat) :
    DecidableEq (ConcreteQuadraticField m) :=
  Classical.decEq (ConcreteQuadraticField m)

instance concretePrimeNeZero (m : Nat) : NeZero (concretePrime m) :=
  ⟨(concretePrime_prime m).ne_zero⟩

/-! ### Searching for an irreducible monic quadratic -/

/-- `quadTest p i` tests whether the monic quadratic with coefficient pair
`(i / p, i % p)` has no root modulo `p`.  The `foldr` shape is chosen so that
primitive recursiveness is immediate. -/
def quadTest (p i : Nat) : Bool :=
  (List.range p).foldr
    (fun t acc => if (t * t + (i / p) * t + (i % p)) % p = 0 then false else acc) true

private lemma foldr_ite_eq_true_iff (f : Nat → Nat) (l : List Nat) :
    (l.foldr (fun t acc => if f t = 0 then false else acc) true) = true ↔
      ∀ t ∈ l, f t ≠ 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.foldr_cons]
      by_cases hfa : f a = 0
      · rw [if_pos hfa]
        constructor
        · intro hcontra
          exact absurd hcontra (by simp)
        · intro h
          exact absurd (h a (List.mem_cons_self ..)) (by simp [hfa])
      · rw [if_neg hfa, ih]
        constructor
        · intro h t ht
          rcases List.mem_cons.mp ht with rfl | ht'
          · exact hfa
          · exact h t ht'
        · intro h t ht
          exact h t (List.mem_cons_of_mem _ ht)

theorem quadTest_eq_true_iff (p i : Nat) :
    quadTest p i = true ↔ ∀ t < p, (t * t + (i / p) * t + (i % p)) % p ≠ 0 := by
  rw [quadTest, foldr_ite_eq_true_iff]
  constructor
  · intro h t ht
    exact h t (List.mem_range.mpr ht)
  · intro h t htmem
    exact h t (List.mem_range.mp htmem)

theorem quadTest_iff (p : Nat) [NeZero p] (i : Nat) :
    quadTest p i = true ↔
      ∀ x : ZMod p, x ^ 2 + ((i / p : Nat) : ZMod p) * x + ((i % p : Nat) : ZMod p) ≠ 0 := by
  rw [quadTest_eq_true_iff]
  have key : ∀ t : Nat, ((t * t + (i / p) * t + (i % p) : Nat) : ZMod p) =
      (t : ZMod p) ^ 2 + ((i / p : Nat) : ZMod p) * (t : ZMod p) +
        ((i % p : Nat) : ZMod p) := by
    intro t; push_cast; ring
  have hzero : ∀ n : Nat, n % p = 0 ↔ ((n : ZMod p) = 0) := by
    intro n
    rw [ZMod.natCast_eq_zero_iff n p, Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h x hx
    have hval := h x.val (ZMod.val_lt x)
    apply hval
    rw [hzero, key, ZMod.natCast_val, ZMod.cast_id]
    exact hx
  · intro h t _ hcontra
    rw [hzero, key] at hcontra
    exact h t hcontra

/-- Existence of a monic quadratic without roots over the prime field: the
minimal polynomial of a primitive element of `GF(p ^ 2)` is one. -/
theorem exists_quadratic_without_root (p : Nat) [Fact p.Prime] :
    ∃ A B : ZMod p, ∀ t : ZMod p, t ^ 2 + A * t + B ≠ 0 := by
  classical
  set K := GaloisField p 2
  haveI : Fintype K := Fintype.ofFinite K
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) K
  have hdim : pb.dim = 2 := by
    rw [← pb.finrank, GaloisField.finrank p (by omega)]
  set f := minpoly (ZMod p) pb.gen with hf
  have hmonic : f.Monic := minpoly.monic (IsIntegral.of_finite _ _)
  have hirr : Irreducible f := minpoly.irreducible (IsIntegral.of_finite _ _)
  have hdeg : f.natDegree = 2 := by
    rw [hf, pb.natDegree_minpoly, hdim]
  refine ⟨f.coeff 1, f.coeff 0, ?_⟩
  intro t ht
  have hroot : f.IsRoot t := by
    have heval : f.eval t = t ^ 2 + f.coeff 1 * t + f.coeff 0 := by
      rw [Polynomial.eval_eq_sum_range, hdeg]
      simp [Finset.sum_range_succ]
      ring_nf
      rw [show f.coeff 2 = 1 by simpa [hdeg] using hmonic.coeff_natDegree]
      ring
    exact heval.trans ht
  exact hirr.not_isRoot_of_natDegree_ne_one (by omega) hroot

/-- The index of the first coefficient pair passing `quadTest`. -/
def quadIndex (m : Nat) : Nat :=
  ((List.range (concretePrime m * concretePrime m)).find? (quadTest (concretePrime m))).getD 0

/-- The linear coefficient of the chosen irreducible quadratic. -/
def quadCoeffA (m : Nat) : Nat := quadIndex m / concretePrime m

/-- The constant coefficient of the chosen irreducible quadratic. -/
def quadCoeffB (m : Nat) : Nat := quadIndex m % concretePrime m

theorem quadIndex_spec (m : Nat) :
    quadIndex m < concretePrime m * concretePrime m ∧
      quadTest (concretePrime m) (quadIndex m) = true := by
  classical
  set p := concretePrime m with hp
  haveI : Fact (Nat.Prime p) := ⟨concretePrime_prime m⟩
  obtain ⟨A, B, hAB⟩ := exists_quadratic_without_root p
  have hppos : 0 < p := (concretePrime_prime m).pos
  set i0 := A.val * p + B.val with hi0
  have hBlt : B.val < p := ZMod.val_lt B
  have hAlt : A.val < p := ZMod.val_lt A
  have hdiv : i0 / p = A.val := by
    rw [hi0, mul_comm, Nat.mul_add_div hppos, Nat.div_eq_of_lt hBlt, Nat.add_zero]
  have hmod : i0 % p = B.val := by
    rw [hi0, mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hBlt]
  have hi0lt : i0 < p * p := by
    have hstep : A.val * p + B.val < (A.val + 1) * p := by
      rw [Nat.add_mul, one_mul]; omega
    calc i0 < (A.val + 1) * p := hstep
      _ ≤ p * p := by
          apply Nat.mul_le_mul_right
          omega
  have hi0test : quadTest p i0 = true := by
    rw [quadTest_iff]
    intro x
    rw [hdiv, hmod, ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
    exact hAB x
  have hmem : i0 ∈ List.range (p * p) := List.mem_range.mpr hi0lt
  have hisSome : ((List.range (p * p)).find? (quadTest p)).isSome = true :=
    List.find?_isSome.mpr ⟨i0, hmem, hi0test⟩
  cases hfind : (List.range (p * p)).find? (quadTest p) with
  | none => rw [hfind] at hisSome; simp at hisSome
  | some j =>
      have hjtest : quadTest p j = true := List.find?_some hfind
      have hjmem : j ∈ List.range (p * p) := by
        obtain ⟨_, k, hk, heq, _⟩ := List.find?_eq_some_iff_getElem.mp hfind
        exact List.mem_of_getElem heq
      have hjlt : j < p * p := List.mem_range.mp hjmem
      have hval : quadIndex m = j := by
        simp [quadIndex, ← hp, hfind]
      rw [hval]
      exact ⟨hjlt, hjtest⟩

theorem quadCoeffA_lt (m : Nat) : quadCoeffA m < concretePrime m := by
  have h := (quadIndex_spec m).1
  rw [quadCoeffA]
  exact Nat.div_lt_of_lt_mul (by omega)

theorem quadCoeffB_lt (m : Nat) : quadCoeffB m < concretePrime m :=
  Nat.mod_lt _ (concretePrime_prime m).pos

/-- The chosen quadratic has no root in the prime field. -/
theorem quadCoeff_no_root (m : Nat) (x : ConcreteField m) :
    x ^ 2 + ((quadCoeffA m : Nat) : ConcreteField m) * x +
      ((quadCoeffB m : Nat) : ConcreteField m) ≠ 0 := by
  have h := (quadIndex_spec m).2
  rw [quadTest_iff] at h
  exact h x

/-! ### Primitive recursiveness of the structure constants -/

lemma quadTest_primrec : Primrec₂ quadTest := by
  have hbody : Primrec (fun z : (Nat × Nat) × Nat × Bool =>
      (z.2.1 * z.2.1 + (z.1.2 / z.1.1) * z.2.1 + (z.1.2 % z.1.1)) % z.1.1) := by
    have ht : Primrec (fun z : (Nat × Nat) × Nat × Bool => z.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hp : Primrec (fun z : (Nat × Nat) × Nat × Bool => z.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hi : Primrec (fun z : (Nat × Nat) × Nat × Bool => z.1.2) :=
      Primrec.snd.comp Primrec.fst
    exact Primrec.nat_mod.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp ht ht)
          (Primrec.nat_mul.comp (Primrec.nat_div.comp hi hp) ht))
        (Primrec.nat_mod.comp hi hp))
      hp
  have hstep : Primrec₂ (fun (q : Nat × Nat) (z : Nat × Bool) =>
      if (z.1 * z.1 + (q.2 / q.1) * z.1 + (q.2 % q.1)) % q.1 = 0 then false else z.2) :=
    (Primrec.ite (Primrec.eq.comp hbody (Primrec.const 0)) (Primrec.const false)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr (Primrec.list_range.comp Primrec.fst)
    (Primrec.const true) hstep).to₂

lemma quadIndex_primrec : Primrec quadIndex := by
  have hpow : Primrec (fun m : Nat => concretePrime m * concretePrime m) :=
    Primrec.nat_mul.comp boundedPrimeSearch_primrec boundedPrimeSearch_primrec
  have hwindow : Primrec (fun m : Nat => List.range (concretePrime m * concretePrime m)) :=
    Primrec.list_range.comp hpow
  have hstep : Primrec₂ (fun (m : Nat) (z : Nat × Option Nat) =>
      bif quadTest (concretePrime m) z.1 then some z.1 else z.2) :=
    (Primrec.cond
      (quadTest_primrec.comp (boundedPrimeSearch_primrec.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have hfind : Primrec (fun m : Nat =>
      (List.range (concretePrime m * concretePrime m)).find? (quadTest (concretePrime m))) := by
    have heq : ∀ (p : Nat) (l : List Nat),
        l.foldr (fun i out => bif quadTest p i then some i else out) none =
          l.find? (quadTest p) := by
      intro p l
      induction l with
      | nil => rfl
      | cons i l ih =>
          simp only [List.foldr_cons, ih]
          cases hi : quadTest p i <;> simp [List.find?, hi]
    exact (Primrec.list_foldr hwindow (Primrec.const none) hstep).of_eq
      (fun m => heq (concretePrime m) (List.range (concretePrime m * concretePrime m)))
  exact (Primrec.option_getD.comp hfind (Primrec.const 0)).of_eq (fun _ => rfl)

lemma quadCoeffA_primrec : Primrec quadCoeffA :=
  Primrec.nat_div.comp quadIndex_primrec boundedPrimeSearch_primrec

lemma quadCoeffB_primrec : Primrec quadCoeffB :=
  Primrec.nat_mod.comp quadIndex_primrec boundedPrimeSearch_primrec

/-! ### The chosen irreducible quadratic and its root -/

/-- The monic quadratic `X ^ 2 + A * X + B` selected by the search. -/
noncomputable def quadPoly (m : Nat) : Polynomial (ConcreteField m) :=
  X ^ 2 + C ((quadCoeffA m : Nat) : ConcreteField m) * X +
    C ((quadCoeffB m : Nat) : ConcreteField m)

lemma quadPoly_natDegree (m : Nat) : (quadPoly m).natDegree = 2 := by
  unfold quadPoly
  compute_degree!

lemma quadPoly_eval (m : Nat) (t : ConcreteField m) :
    (quadPoly m).eval t =
      t ^ 2 + ((quadCoeffA m : Nat) : ConcreteField m) * t +
        ((quadCoeffB m : Nat) : ConcreteField m) := by
  simp [quadPoly]

lemma quadPoly_irreducible (m : Nat) : Irreducible (quadPoly m) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quadPoly_natDegree]; decide
  · intro t hroot
    exact quadCoeff_no_root m t (by simpa [Polynomial.IsRoot, quadPoly_eval] using hroot)

/-- The chosen quadratic has a root inside `GF(q ^ 2)`. -/
lemma exists_quadPoly_root (m : Nat) :
    ∃ g : ConcreteQuadraticField m,
      g ^ 2 + algebraMap (ConcreteField m) (ConcreteQuadraticField m)
            ((quadCoeffA m : Nat) : ConcreteField m) * g +
          algebraMap (ConcreteField m) (ConcreteQuadraticField m)
            ((quadCoeffB m : Nat) : ConcreteField m) = 0 := by
  classical
  set f := quadPoly m with hfdef
  haveI : Fact (Irreducible f) := ⟨quadPoly_irreducible m⟩
  have hf0 : f ≠ 0 := (quadPoly_irreducible m).ne_zero
  let pb := AdjoinRoot.powerBasis hf0
  haveI : FiniteDimensional (ConcreteField m) (AdjoinRoot f) := pb.finite
  haveI : Fintype (AdjoinRoot f) := Module.fintypeOfFintype pb.basis
  have hcard : Fintype.card (AdjoinRoot f) = concretePrime m ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := ConcreteField m), ZMod.card]
    congr 1
    rw [pb.finrank]
    simpa [pb, AdjoinRoot.powerBasis_dim] using quadPoly_natDegree m
  let e := GaloisField.algEquivGaloisFieldOfFintype (concretePrime m) 2 hcard
  refine ⟨e (AdjoinRoot.root f), ?_⟩
  have haeval : (Polynomial.aeval (e (AdjoinRoot.root f))) f = 0 := by
    rw [Polynomial.aeval_algHom_apply]
    simp [AdjoinRoot.aeval_eq]
  simpa [hfdef, quadPoly, Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow] using haeval

/-! ### The chosen basis and its coordinate arithmetic -/

/-- The chosen generator of the quadratic extension: a root of `quadPoly m`. -/
noncomputable def quadGen (m : Nat) : ConcreteQuadraticField m :=
  (exists_quadPoly_root m).choose

/-- The base-field image of the linear coefficient of the chosen quadratic. -/
abbrev quadFieldA (m : Nat) : ConcreteField m := ((quadCoeffA m : Nat) : ConcreteField m)

/-- The base-field image of the constant coefficient of the chosen quadratic. -/
abbrev quadFieldB (m : Nat) : ConcreteField m := ((quadCoeffB m : Nat) : ConcreteField m)

lemma quadGen_root (m : Nat) :
    quadGen m ^ 2 +
        algebraMap (ConcreteField m) (ConcreteQuadraticField m) (quadFieldA m) * quadGen m +
      algebraMap (ConcreteField m) (ConcreteQuadraticField m) (quadFieldB m) = 0 :=
  (exists_quadPoly_root m).choose_spec

lemma quadGen_sq (m : Nat) :
    quadGen m ^ 2 =
      -(algebraMap (ConcreteField m) (ConcreteQuadraticField m) (quadFieldA m) * quadGen m) -
        algebraMap (ConcreteField m) (ConcreteQuadraticField m) (quadFieldB m) := by
  have h := quadGen_root m
  linear_combination h

lemma quadFieldB_ne_zero (m : Nat) : quadFieldB m ≠ 0 := by
  have h := quadCoeff_no_root m 0
  simpa using h

lemma quadGen_ne_zero (m : Nat) : quadGen m ≠ 0 := by
  intro h0
  have h := quadGen_root m
  rw [h0] at h
  simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero,
    zero_add, add_zero] at h
  exact quadFieldB_ne_zero m
    ((algebraMap (ConcreteField m) (ConcreteQuadraticField m)).injective (by simpa using h))

lemma quadGen_not_base (m : Nat) (t : ConcreteField m) :
    algebraMap (ConcreteField m) (ConcreteQuadraticField m) t ≠ quadGen m := by
  intro ht
  have h := quadGen_root m
  rw [← ht] at h
  have hcast :
      algebraMap (ConcreteField m) (ConcreteQuadraticField m)
        (t ^ 2 + quadFieldA m * t + quadFieldB m) = 0 := by
    push_cast [map_add, map_mul, map_pow]
    exact h
  have := (algebraMap (ConcreteField m) (ConcreteQuadraticField m)).injective
    (by simpa using hcast : algebraMap (ConcreteField m) (ConcreteQuadraticField m)
      (t ^ 2 + quadFieldA m * t + quadFieldB m) =
      algebraMap (ConcreteField m) (ConcreteQuadraticField m) 0)
  exact quadCoeff_no_root m t this

lemma quadGen_linearIndependent (m : Nat) :
    LinearIndependent (ConcreteField m) ![(1 : ConcreteQuadraticField m), quadGen m] := by
  rw [linearIndependent_fin2]
  refine ⟨by simpa using quadGen_ne_zero m, ?_⟩
  intro a ha
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at ha
  rw [Algebra.smul_def] at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have halg : algebraMap (ConcreteField m) (ConcreteQuadraticField m) a ≠ 0 := by
    simpa using ha0
  have hstep :
      algebraMap (ConcreteField m) (ConcreteQuadraticField m) a * quadGen m =
        algebraMap (ConcreteField m) (ConcreteQuadraticField m) a *
          algebraMap (ConcreteField m) (ConcreteQuadraticField m) a⁻¹ := by
    rw [ha, ← map_mul, mul_inv_cancel₀ ha0, map_one]
  exact quadGen_not_base m a⁻¹ (mul_left_cancel₀ halg hstep).symm

lemma concreteQuadraticField_finrank (m : Nat) :
    Module.finrank (ConcreteField m) (ConcreteQuadraticField m) = 2 :=
  GaloisField.finrank (concretePrime m) (by omega)

/-- The chosen basis `(1, quadGen m)` of the quadratic extension. -/
noncomputable def concreteQuadraticBasis (m : Nat) :
    Module.Basis (Fin 2) (ConcreteField m) (ConcreteQuadraticField m) :=
  basisOfLinearIndependentOfCardEqFinrank (quadGen_linearIndependent m)
    (by simp [concreteQuadraticField_finrank])

lemma concreteQuadraticBasis_zero (m : Nat) :
    concreteQuadraticBasis m 0 = 1 := by
  rw [concreteQuadraticBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  simp

lemma concreteQuadraticBasis_one (m : Nat) :
    concreteQuadraticBasis m 1 = quadGen m := by
  rw [concreteQuadraticBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  simp

/-- The element of the quadratic extension with coordinates `(u0, u1)`. -/
noncomputable def quadMk (m : Nat) (u0 u1 : ConcreteField m) : ConcreteQuadraticField m :=
  algebraMap (ConcreteField m) (ConcreteQuadraticField m) u0 +
    algebraMap (ConcreteField m) (ConcreteQuadraticField m) u1 * quadGen m

lemma quadMk_eq_smul (m : Nat) (u0 u1 : ConcreteField m) :
    quadMk m u0 u1 =
      u0 • concreteQuadraticBasis m 0 + u1 • concreteQuadraticBasis m 1 := by
  rw [concreteQuadraticBasis_zero, concreteQuadraticBasis_one]
  simp [quadMk, Algebra.smul_def]

@[simp]
lemma quadMk_repr_zero (m : Nat) (u0 u1 : ConcreteField m) :
    (concreteQuadraticBasis m).repr (quadMk m u0 u1) 0 = u0 := by
  rw [quadMk_eq_smul, map_add, map_smul, map_smul, Module.Basis.repr_self,
    Module.Basis.repr_self]
  simp

@[simp]
lemma quadMk_repr_one (m : Nat) (u0 u1 : ConcreteField m) :
    (concreteQuadraticBasis m).repr (quadMk m u0 u1) 1 = u1 := by
  rw [quadMk_eq_smul, map_add, map_smul, map_smul, Module.Basis.repr_self,
    Module.Basis.repr_self]
  simp

/-- Every element is the `quadMk` of its coordinates. -/
lemma quadMk_repr_self (m : Nat) (a : ConcreteQuadraticField m) :
    quadMk m ((concreteQuadraticBasis m).repr a 0) ((concreteQuadraticBasis m).repr a 1) = a := by
  rw [quadMk_eq_smul]
  have hsum := (concreteQuadraticBasis m).sum_repr a
  rw [Fin.sum_univ_two] at hsum
  exact hsum

lemma quadMk_add (m : Nat) (u0 u1 v0 v1 : ConcreteField m) :
    quadMk m u0 u1 + quadMk m v0 v1 = quadMk m (u0 + v0) (u1 + v1) := by
  simp [quadMk, map_add]
  ring

lemma quadMk_mul (m : Nat) (u0 u1 v0 v1 : ConcreteField m) :
    quadMk m u0 u1 * quadMk m v0 v1 =
      quadMk m (u0 * v0 - quadFieldB m * (u1 * v1))
        (u0 * v1 + u1 * v0 - quadFieldA m * (u1 * v1)) := by
  simp only [quadMk, map_add, map_mul, map_sub]
  linear_combination
    (algebraMap (ConcreteField m) (ConcreteQuadraticField m) u1 *
      algebraMap (ConcreteField m) (ConcreteQuadraticField m) v1) * quadGen_sq m

end Kolmogorov
