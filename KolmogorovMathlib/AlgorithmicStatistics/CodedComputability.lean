import KolmogorovMathlib.AlgorithmicStatistics.CodedFiniteDistribution
import KolmogorovMathlib.Prefix.Properties

/-!
# Computability infrastructure for coded finite distributions

This file collects the `Primcodable` instances for the coded-distribution
structures and the primitive-recursiveness of the *encoders* (`natCode`,
`pairCode`, `RatMass.code`, `CodedDistributionEntry.code`,
`codedDistributionDataCode`) together with the computable enumeration
`allStrings`.  These are shared by the stochasticity layer (for the
length-uniform model code) and the normalization layer (for `normalizeCode`).
-/

namespace Kolmogorov

namespace CodedFiniteDistribution

/-! ### Primcodable instances for the coded distribution structures -/

/-- `RatMass` is equivalent to the subtype of pairs with positive second
component. -/
def RatMass.equivSubtype : RatMass ≃ {p : ℕ × ℕ // 0 < p.2} where
  toFun q := ⟨(q.num, q.den), q.den_pos⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv := by intro q; cases q; rfl
  right_inv := by intro p; cases p; rfl

instance : Primcodable {p : ℕ × ℕ // 0 < p.2} :=
  Primcodable.subtype (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd)

instance : Primcodable RatMass := Primcodable.ofEquiv _ RatMass.equivSubtype

/-- `CodedDistributionEntry` is equivalent to a pair of its point and mass. -/
def CodedDistributionEntry.equivProd : CodedDistributionEntry ≃ BitString × RatMass where
  toFun e := (e.point, e.mass)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro e; cases e; rfl
  right_inv := by intro p; cases p; rfl

instance : Primcodable CodedDistributionEntry :=
  Primcodable.ofEquiv _ CodedDistributionEntry.equivProd

/-- `CodedFiniteDistribution` is equivalent to its underlying list of entries. -/
def equivList :
    CodedFiniteDistribution ≃ List CodedDistributionEntry where
  toFun P := P.data
  invFun l := ⟨l⟩
  left_inv := by intro P; cases P; rfl
  right_inv := by intro l; rfl

instance : Primcodable CodedFiniteDistribution :=
  Primcodable.ofEquiv _ equivList

/-! ### Primitive recursiveness of the encoders -/

/-- The unary natural-number encoder is primitive recursive. -/
theorem natCode_primrec : Primrec natCode := by
  have hrep : Primrec (fun n : ℕ => List.replicate n true) := by
    have h : (fun n : ℕ => List.replicate n true)
        = fun n => Nat.rec ([] : List Bool) (fun _ ih => true :: ih) n := by
      funext n; induction n with
      | zero => rfl
      | succ n ih => rw [List.replicate_succ, ih]
    rw [h]
    exact Primrec.nat_rec' Primrec.id (Primrec.const [])
      (Primrec.list_cons.comp (Primrec.const true) (Primrec.snd.comp Primrec.snd)).to₂
  have h : natCode = fun n => List.replicate n true ++ [false] := rfl
  rw [h]
  exact Primrec.list_append.comp hrep (Primrec.const [false])

/-- The self-delimiting pair encoder is primitive recursive. -/
theorem pairCode_primrec : Primrec₂ pairCode :=
  (Primrec.list_append.comp
    (Primrec.list_append.comp
      (natCode_primrec.comp (Primrec.list_length.comp Primrec.fst))
      Primrec.fst)
    Primrec.snd).of_eq (fun _ => rfl)

/-- The `num` projection of a rational mass is primitive recursive. -/
theorem ratMass_num_primrec : Primrec (fun q : RatMass => q.num) :=
  Primrec.fst.comp (Primrec.subtype_val.comp Primrec.of_equiv)

/-- The `den` projection of a rational mass is primitive recursive. -/
theorem ratMass_den_primrec : Primrec (fun q : RatMass => q.den) :=
  Primrec.snd.comp (Primrec.subtype_val.comp Primrec.of_equiv)

/-- The map `k ↦ 2^k` is primitive recursive. -/
theorem twoPow_primrec : Primrec (fun k : ℕ => 2 ^ k) := by
  have h :
      (fun k : ℕ => 2 ^ k) =
        fun k => Nat.rec 1 (fun _ ih => ih * 2) k := by
    funext k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Nat.pow_succ, ih]
  rw [h]
  exact Primrec.nat_rec' Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp
      (Primrec.snd.comp (Primrec.snd : Primrec (fun p : ℕ × (ℕ × ℕ) => p.2)))
      (Primrec.const 2)).to₂

/-- The rational threshold test `q.den ≤ q.num * 2^k` is primitive recursive. -/
theorem ratMass_ge_invPow2_primrec : Primrec₂ RatMass.ge_invPow2 := by
  have hden : Primrec₂ (fun q : RatMass => fun _k : ℕ => q.den) :=
    (ratMass_den_primrec.comp (Primrec.fst : Primrec (fun p : RatMass × ℕ => p.1))).to₂
  have hrhs : Primrec₂ (fun q : RatMass => fun k : ℕ => q.num * 2 ^ k) :=
    (Primrec.nat_mul.comp
      (ratMass_num_primrec.comp (Primrec.fst : Primrec (fun p : RatMass × ℕ => p.1)))
      (twoPow_primrec.comp (Primrec.snd : Primrec (fun p : RatMass × ℕ => p.2)))).to₂
  exact (PrimrecRel.decide (PrimrecRel.comp₂ Primrec.nat_le hden hrhs)).of_eq
    (fun q k => rfl)

/-- The rational-mass encoder is primitive recursive. -/
theorem ratMass_code_primrec : Primrec RatMass.code :=
  (pairCode_primrec.comp (natCode_primrec.comp ratMass_num_primrec)
    (natCode_primrec.comp ratMass_den_primrec)).of_eq (fun _ => rfl)

/-- The `point` projection of an entry is primitive recursive. -/
theorem entry_point_primrec :
    Primrec (fun e : CodedDistributionEntry => e.point) :=
  Primrec.fst.comp Primrec.of_equiv

/-- The `mass` projection of an entry is primitive recursive. -/
theorem entry_mass_primrec :
    Primrec (fun e : CodedDistributionEntry => e.mass) :=
  Primrec.snd.comp Primrec.of_equiv

/-- The entry encoder is primitive recursive. -/
theorem entry_code_primrec : Primrec CodedDistributionEntry.code :=
  (pairCode_primrec.comp entry_point_primrec
    (ratMass_code_primrec.comp entry_mass_primrec)).of_eq (fun _ => rfl)

/-- The list-of-entries encoder is primitive recursive. -/
theorem codedDistributionDataCode_primrec :
    Primrec codedDistributionDataCode := by
  have h := Primrec.list_rec
    (show Primrec (fun l : List CodedDistributionEntry => l) from Primrec.id)
    (show Primrec (fun _ : List CodedDistributionEntry => [false]) from Primrec.const [false])
    (show Primrec₂ (fun _ (p : CodedDistributionEntry ×
        (List CodedDistributionEntry × List Bool)) =>
        true :: pairCode (CodedDistributionEntry.code p.1) p.2.2) from
      (Primrec.list_cons.comp (Primrec.const true)
        (pairCode_primrec.comp (entry_code_primrec.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂)
  exact h.of_eq (fun l => by induction l with
    | nil => rfl
    | cons hd tl ih => exact congrArg (fun x => true :: pairCode hd.code x) ih)

/-
The computable enumeration `allStrings` is primitive recursive.
-/
theorem allStrings_primrec : Primrec allStrings := by
  convert Primrec.nat_rec' _ _ _ using 1;
  rotate_left;
  · exact fun n => n
  · exact fun n => [[]]
  · exact fun n p => p.2.map (List.cons false) ++ p.2.map (List.cons true)
  · exact Primrec.id;
  · exact Primrec.const [ [] ];
  · apply Primrec₂.comp;
    · exact Primrec.list_append;
    · apply Primrec.list_map;
      · exact Primrec.snd.comp ( Primrec.snd );
      · exact Primrec₂.comp ( Primrec.list_cons ) ( Primrec.const false ) ( Primrec.snd );
    · apply Primrec.list_map;
      · exact Primrec.snd.comp ( Primrec.snd );
      · exact Primrec.list_cons.comp ( Primrec.const true ) ( Primrec.snd );
  · funext n; induction n <;> simp +decide [ *, allStrings ] ;

/-
The rational mass `1 / 2 ^ n` is a primitive-recursive function of `n`.
-/
theorem ratMassInvPow2_primrec :
    Primrec (fun n : ℕ => ratMassInvNat (2 ^ n) (pow_pos (by decide) n)) :=
  let h_pow := twoPow_primrec
  let h : Primrec (fun n : ℕ => ⟨(1, 2 ^ n), by simp +decide⟩ : ℕ → {p : ℕ × ℕ // 0 < p.2}) :=
    Primrec.subtype_mk (Primrec.pair (Primrec.const 1) h_pow)
  (Primrec.of_equiv_symm.comp h).of_eq (fun _ => rfl)

/-
The length-uniform data list is a primitive-recursive function of `n`.
-/
theorem lengthUniformData_primrec : Primrec lengthUniformData := by
  have hf : Primrec (fun n => (allStrings n).map fun x =>
      (⟨x, ratMassInvNat (2 ^ n)
        (pow_pos (by decide) n)⟩ : CodedDistributionEntry)) := by
    exact (Primrec.list_map allStrings_primrec
      (Primrec.of_equiv_symm.comp
        (Primrec.pair Primrec.snd (ratMassInvPow2_primrec.comp Primrec.fst))).to₂).of_eq
          (fun _ => rfl)
  exact hf.of_eq (fun _ => rfl)

/-- The canonical code of the length-uniform model is a primitive-recursive
function of `n`. -/
theorem codedLengthUniform_code_primrec :
    Primrec (fun n : ℕ => (codedLengthUniform n).code) :=
  (codedDistributionDataCode_primrec.comp lengthUniformData_primrec).of_eq (fun _ => rfl)

end CodedFiniteDistribution

end Kolmogorov
