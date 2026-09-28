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

/-- The self-delimiting pair encoder is primitive recursive. -/
theorem pairCode_primrec : Primrec₂ pairCode :=
  (Primrec.list_append.comp
    (Primrec.list_append.comp
      (primrec_natCode.comp (Primrec.list_length.comp Primrec.fst))
      Primrec.fst)
    Primrec.snd).of_eq (fun _ => rfl)

/-- The `num`–`den` pair of a rational mass is primitive recursive. This is the general
statement behind `ratMass_num_primrec` and `ratMass_den_primrec`, which are its two
components. -/
theorem ratMass_numDen_primrec : Primrec (fun q : RatMass => (q.num, q.den)) := by
  have := @Primrec.of_equiv
  convert this.comp ( Primrec.id ) |> Primrec.comp ( Primrec.subtype_val ) using 1

/-- The `num` projection of a rational mass is primitive recursive. -/
theorem ratMass_num_primrec : Primrec (fun q : RatMass => q.num) :=
  Primrec.fst.comp ratMass_numDen_primrec

/-- The `den` projection of a rational mass is primitive recursive. -/
theorem ratMass_den_primrec : Primrec (fun q : RatMass => q.den) :=
  Primrec.snd.comp ratMass_numDen_primrec

/-- The rational threshold test `q.den ≤ q.num * 2^k` is primitive recursive. -/
theorem ratMass_ge_invPow2_primrec : Primrec₂ RatMass.geInvPow2 := by
  have hden : Primrec₂ (fun q : RatMass => fun _k : ℕ => q.den) :=
    (ratMass_den_primrec.comp (Primrec.fst : Primrec (fun p : RatMass × ℕ => p.1))).to₂
  have hrhs : Primrec₂ (fun q : RatMass => fun k : ℕ => q.num * 2 ^ k) :=
    (Primrec.nat_mul.comp
      (ratMass_num_primrec.comp (Primrec.fst : Primrec (fun p : RatMass × ℕ => p.1)))
      (primrec_two_pow_aux.comp (Primrec.snd : Primrec (fun p : RatMass × ℕ => p.2)))).to₂
  exact (PrimrecRel.decide (PrimrecRel.comp₂ Primrec.nat_le hden hrhs)).of_eq
    (fun q k => rfl)

/-- The rational-mass encoder is primitive recursive. -/
theorem ratMass_code_primrec : Primrec RatMass.code :=
  (pairCode_primrec.comp (primrec_natCode.comp ratMass_num_primrec)
    (primrec_natCode.comp ratMass_den_primrec)).of_eq (fun _ => rfl)

/-- The `point` projection of an entry is primitive recursive. -/
theorem entry_point_primrec :
    Primrec (fun e : CodedDistributionEntry => e.point) := by
  have := @Primrec.of_equiv
  convert Primrec.fst.comp (this.comp Primrec.id) using 1

/-- The `mass` projection of an entry is primitive recursive. -/
theorem entry_mass_primrec :
    Primrec (fun e : CodedDistributionEntry => e.mass) := by
  have := @Primrec.of_equiv
  convert Primrec.snd.comp (this.comp Primrec.id) using 1

/-- The entry encoder is primitive recursive. -/
theorem entry_code_primrec : Primrec CodedDistributionEntry.code :=
  (pairCode_primrec.comp entry_point_primrec
    (ratMass_code_primrec.comp entry_mass_primrec)).of_eq (fun _ => rfl)

/-- The list-of-entries encoder is primitive recursive. -/
theorem codedDistributionDataCode_primrec : Primrec codedDistributionDataCode := by
  refine Primrec.of_eq
    (f := fun l : List CodedDistributionEntry =>
      List.recOn l [false] fun e _ IH => true :: pairCode (CodedDistributionEntry.code e) IH)
    (g := codedDistributionDataCode) ?_ ?_
  · convert Primrec.list_rec _ _ _ using 1
    rotate_left
    · exact CodedDistributionEntry
    · exact inferInstance
    · exact fun l => l
    · exact fun _ => [false]
    · exact fun _ p => true :: pairCode p.1.code p.2.2
    · exact Primrec.id
    · exact Primrec.const [false]
    · convert Primrec.list_cons.comp (Primrec.const true)
        (pairCode_primrec.comp (entry_code_primrec.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) using 1
    · rfl
  · intro l; induction l <;> simp +decide [*, codedDistributionDataCode]

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
    Primrec (fun n : ℕ => ratMassInvNat (2 ^ n) (pow_pos (by decide) n)) := by
      have h : Primrec (fun n : ℕ => ⟨(1, 2 ^ n), by simp +decide⟩ : ℕ → {p : ℕ × ℕ // 0 < p.2}) :=
          by
        -- The constant function 1 is primitive recursive.
        have h_const : Primrec (fun _ : ℕ => 1 : ℕ → ℕ) := by
          exact Primrec.const 1;
        -- The function `Nat.pow 2 n` is primitive recursive.
        have h_pow : Primrec (fun n : ℕ => 2 ^ n : ℕ → ℕ) := by
          have h_pow : Primrec (fun n : ℕ => Nat.pow 2 n) := by
            have h_pow_def : ∀ n : ℕ, Nat.pow 2 n = Nat.rec 1 (fun _ p => 2 * p) n := by
              intro n
              induction n with
              | zero => rfl
              | succ n ih =>
                calc
                  Nat.pow 2 (n + 1) = 2 * Nat.pow 2 n :=
                    (Nat.pow_succ' : Nat.pow 2 (n + 1) = 2 * Nat.pow 2 n)
                  _ = 2 * Nat.rec 1 (fun _ p => 2 * p) n := congrArg (2 * ·) ih
            convert Primrec.nat_rec' _ _ _ using 1;
            rotate_left;
            · exact fun n => n
            · exact fun _ => 1
            · exact fun n p => 2 * p.2
            · exact Primrec.id;
            · exact h_const;
            · exact Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.snd.comp Primrec.snd );
            · exact funext h_pow_def;
          exact h_pow;
        exact Primrec.subtype_mk ( Primrec.pair h_const h_pow );
      convert h using 1

/-
The length-uniform data list is a primitive-recursive function of `n`.
-/
theorem lengthUniformData_primrec : Primrec lengthUniformData := by
  have hf : Primrec (fun n => (allStrings n).map fun x =>
      (⟨x, ratMassInvNat (2 ^ n) (pow_pos (by decide) n)⟩ : CodedDistributionEntry)) := by
    refine Primrec.list_map allStrings_primrec ?_
    convert Primrec.of_equiv_symm.comp
      (Primrec.pair Primrec.snd (ratMassInvPow2_primrec.comp Primrec.fst)) using 1
  exact hf.of_eq (fun _ => rfl)

/-- The canonical code of the length-uniform model is a primitive-recursive
function of `n`. -/
theorem codedLengthUniform_code_primrec :
    Primrec (fun n : ℕ => (codedLengthUniform n).code) :=
  (codedDistributionDataCode_primrec.comp lengthUniformData_primrec).of_eq (fun _ => rfl)

end CodedFiniteDistribution

end Kolmogorov
