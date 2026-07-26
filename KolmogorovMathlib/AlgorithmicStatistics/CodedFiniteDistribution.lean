/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.AlgorithmicStatistics.Basic
import KolmogorovMathlib.Prefix.Symmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Coded finite rational distributions

This file introduces the faithful model object needed for algorithmic
statistics.  A finite distribution is represented by a finite list of pairs
`(x, q)`, where `x : BitString` and `q` is a non-negative rational mass encoded as
natural numerator and positive natural denominator.  The code of the model is the
canonical code of this finite list, not an arbitrary label.

The older `FiniteDistribution` module is still present as legacy code.  The
main algorithmic-statistics definitions use this coded replacement foundation.
-/

namespace Kolmogorov

/-- A non-negative rational mass, represented by `num / den` with `0 < den`. -/
structure RatMass where
  /-- Numerator of the rational mass. -/
  num : Nat
  /-- Denominator of the rational mass. -/
  den : Nat
  den_pos : 0 < den

namespace RatMass

/-- The `ENNReal` value represented by the rational mass. -/
noncomputable def value (q : RatMass) : ENNReal :=
  (q.num : ENNReal) / (q.den : ENNReal)

/-- Encode a rational mass as a pair of unary natural-number codes. -/
def code (q : RatMass) : BitString :=
  pairCode (natCode q.num) (natCode q.den)

/-- The rational-mass code is injective. -/
theorem code_injective : Function.Injective code := by
  intro q r h
  unfold code at h
  have hp : (natCode q.num, natCode q.den) = (natCode r.num, natCode r.den) :=
    pairCode_injective (by simpa using h)
  have hn : q.num = r.num := natCode_injective (congrArg Prod.fst hp)
  have hd : q.den = r.den := natCode_injective (congrArg Prod.snd hp)
  cases q
  cases r
  simp_all

/-- A computable predicate for whether `2^-k ≤ q.value`. -/
def geInvPow2 (q : RatMass) (k : ℕ) : Bool :=
  decide (q.den ≤ q.num * 2 ^ k)

theorem ge_invPow2_iff (q : RatMass) (k : ℕ) :
    (2 : ENNReal)⁻¹ ^ k ≤ q.value ↔ q.den ≤ q.num * 2 ^ k := by
  have hden0 : (q.den : ENNReal) ≠ 0 := by
    exact_mod_cast ne_of_gt q.den_pos
  have hdenTop : (q.den : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpow0 : ((2 : ENNReal) ^ k) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hpowTop : ((2 : ENNReal) ^ k) ≠ ⊤ := by
    simp
  have hdiv :
      (2 : ENNReal)⁻¹ ^ k * (q.den : ENNReal) =
        (q.den : ENNReal) / (2 : ENNReal) ^ k := by
    rw [← ENNReal.inv_pow, ENNReal.div_eq_inv_mul]
  calc
    (2 : ENNReal)⁻¹ ^ k ≤ q.value
        ↔ (2 : ENNReal)⁻¹ ^ k * (q.den : ENNReal) ≤ (q.num : ENNReal) := by
          unfold value
          rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)]
    _ ↔ (q.den : ENNReal) / (2 : ENNReal) ^ k ≤ (q.num : ENNReal) := by
          rw [hdiv]
    _ ↔ (q.den : ENNReal) ≤ (q.num : ENNReal) * (2 : ENNReal) ^ k := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl hpow0) (Or.inl hpowTop)]
    _ ↔ q.den ≤ q.num * 2 ^ k := by
          constructor <;> intro h <;> exact_mod_cast h

end RatMass

/-- One coded atom of a finite rational distribution. -/
structure CodedDistributionEntry where
  /-- The string point assigned the mass. -/
  point : BitString
  /-- The rational mass assigned to the point. -/
  mass : RatMass

namespace CodedDistributionEntry

/-- Encode an atom as the pair of its point and its rational mass code. -/
def code (e : CodedDistributionEntry) : BitString :=
  pairCode e.point e.mass.code

/-- The atom code is injective. -/
theorem code_injective : Function.Injective code := by
  intro e f h
  unfold code at h
  have hp : (e.point, e.mass.code) = (f.point, f.mass.code) :=
    pairCode_injective (by simpa using h)
  have hm : e.mass = f.mass := RatMass.code_injective (congrArg Prod.snd hp)
  cases e
  cases f
  simp_all

end CodedDistributionEntry

/-- Encode a finite list of distribution atoms.  The leading boolean separates
`nil` from `cons`; the cons payload is a pair of the head code and the tail code. -/
def codedDistributionDataCode : List CodedDistributionEntry -> BitString
  | [] => [false]
  | e :: es => true :: pairCode e.code (codedDistributionDataCode es)

/-- The finite-list distribution code is injective. -/
theorem codedDistributionDataCode_injective : Function.Injective codedDistributionDataCode := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys => simp [codedDistributionDataCode] at h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp [codedDistributionDataCode] at h
      | cons y ys =>
          simp only [codedDistributionDataCode, List.cons.injEq] at h
          have hp : (x.code, codedDistributionDataCode xs) =
              (y.code, codedDistributionDataCode ys) :=
            pairCode_injective (by simpa using h.2)
          have hx : x = y := CodedDistributionEntry.code_injective (congrArg Prod.fst hp)
          have hxs : xs = ys := ih (congrArg Prod.snd hp)
          simp [hx, hxs]

/-- Finite support represented by a list of rational atoms.  Repeated points are
allowed at this level and their masses are summed by `mass`; later canonicality
conditions can impose `Nodup` or sortedness when a unique normal form is needed. -/
structure CodedFiniteDistribution where
  /-- The list of entries in the distribution. -/
  data : List CodedDistributionEntry

namespace CodedFiniteDistribution

/-- The finite support of a coded distribution. -/
def support (P : CodedFiniteDistribution) : Finset BitString :=
  P.data.foldr (fun e acc ↦ insert e.point acc) Finset.empty

/-- The mass assigned to a string by the finite rational data. -/
noncomputable def mass (P : CodedFiniteDistribution) (x : BitString) : ENNReal :=
  P.data.foldr (fun e acc ↦ (if e.point = x then e.mass.value else 0) + acc) 0

/-
Membership in the support is membership in the list of points.
-/
theorem mem_support_iff (P : CodedFiniteDistribution) (x : BitString) :
    x ∈ P.support ↔ x ∈ P.data.map CodedDistributionEntry.point := by
  -- By definition of `support`, we know that `x ∈ P.support` if and only if
  -- there exists an element `e` in `P.data` such that `e.point = x`.
  simp only [CodedFiniteDistribution.support]
  induction P.data with
  | nil => simp +decide [ Finset.empty ]
  | cons e P ih => grind

/-
A string outside the support carries zero mass.
-/
theorem mass_eq_zero_of_not_mem_support (P : CodedFiniteDistribution) (x : BitString)
    (hx : x ∉ P.support) : P.mass x = 0 := by
  -- By definition of mass, if x is not in the support, then in the foldr, each
  -- if e.point = x condition will be false. Therefore, each term in the sum
  -- will be zero, and the entire sum will be zero.
  have h_foldr_zero : ∀ e ∈ P.data, e.point ≠ x := by
    exact fun e he ↦ fun h ↦ hx <| mem_support_iff P x |>.2 <| List.mem_map.2 ⟨ e, he, h ⟩;
  have h_foldr_zero : ∀ (es : List CodedDistributionEntry), (∀ e ∈ es, e.point ≠ x) →
      List.foldr (fun e acc ↦ (if e.point = x then e.mass.value else 0) + acc) 0 es = 0 := by
    intro es hes; induction es <;> aesop;
  exact h_foldr_zero _ ‹_›

/-- Predicate asserting that the coded finite mass function is a probability distribution. -/
noncomputable def IsProbability (P : CodedFiniteDistribution) : Prop :=
  Finset.sum P.support (fun x ↦ P.mass x) = 1

/-- The canonical code of the distribution. -/
def code (P : CodedFiniteDistribution) : BitString :=
  codedDistributionDataCode P.data

/-- The model complexity of a coded finite distribution. -/
noncomputable def complexity (U : Map) (P : CodedFiniteDistribution) : ENat :=
  KPPlain U P.code

/-- The distribution code is injective on the finite rational data. -/
theorem code_injective : Function.Injective code := by
  intro P Q h
  cases P
  cases Q
  simp only [code] at h
  exact congrArg CodedFiniteDistribution.mk (codedDistributionDataCode_injective h)

/-- `DeficiencyLe` for a coded finite distribution, in multiplicative form. -/
noncomputable def DeficiencyLe (U : Map) (P : CodedFiniteDistribution)
    (x : BitString) (beta : Nat) : Prop :=
  complexityWeight (KP U x P.code) <= (2 : ENNReal) ^ beta * P.mass x

/-- Coded stochasticity: the model complexity is the complexity of the canonical
finite rational list code. -/
noncomputable def IsStochastic (U : Map) (x : BitString) (alpha beta : Nat) : Prop :=
  Exists fun P : CodedFiniteDistribution ↦
    P.IsProbability /\ P.complexity U <= (alpha : ENat) /\ P.DeficiencyLe U x beta

/-- Coded non-stochasticity is the negation of coded stochasticity. -/
def IsNonStochastic (U : Map) (x : BitString) (alpha beta : Nat) : Prop :=
  Not (IsStochastic U x alpha beta)

end CodedFiniteDistribution

/-! ### Canonical coded constructors -/

/-- The rational mass `1`. -/
def ratMassOne : RatMass where
  num := 1
  den := 1
  den_pos := by decide

@[simp] theorem ratMassOne_value : ratMassOne.value = 1 := by
  norm_num [ratMassOne, RatMass.value]

/-- The rational mass `1 / n`, for positive natural `n`. -/
def ratMassInvNat (n : Nat) (hn : 0 < n) : RatMass where
  num := 1
  den := n
  den_pos := hn

/-- The coded Dirac distribution concentrated at `x`.

Its code is the canonical code of the one-entry rational distribution data, so
it changes with `x` and cannot be replaced by an arbitrary fixed label. -/
def codedDirac (x : BitString) : CodedFiniteDistribution where
  data := [{ point := x, mass := ratMassOne }]

@[simp] theorem codedDirac_code (x : BitString) :
    (codedDirac x).code =
      codedDistributionDataCode [{ point := x, mass := ratMassOne }] := rfl

@[simp] theorem codedDirac_mass_self (x : BitString) :
    (codedDirac x).mass x = 1 := by
  simp [codedDirac, CodedFiniteDistribution.mass]

@[simp] theorem codedDirac_mass_ne (x y : BitString) (h : y ≠ x) :
    (codedDirac x).mass y = 0 := by
  have hxy : x ≠ y := fun hxy ↦ h hxy.symm
  simp [codedDirac, CodedFiniteDistribution.mass, hxy]

@[simp] theorem codedDirac_support (x : BitString) :
    (codedDirac x).support = {x} := by
  rfl

@[simp] theorem codedDirac_isProbability (x : BitString) :
    (codedDirac x).IsProbability := by
  simp [CodedFiniteDistribution.IsProbability]

/-! ### A computable canonical enumeration of a finite set

`Finset.toList` is noncomputable (it relies on `Multiset.toList`, which uses
choice), so codes built from it cannot be reproduced by a computable function.
We instead use `Finset.sort` with the fixed decidable total order obtained by
comparing `Encodable` codes; this gives a deterministic, *computable* canonical
list whose induced distribution code is a computable function of the set. -/

/-- A fixed decidable total order on `BitString`, comparing `Encodable` codes. -/
def bitStringLE (a b : BitString) : Prop := Encodable.encode a ≤ Encodable.encode b

instance : DecidableRel bitStringLE := fun a b ↦
  inferInstanceAs (Decidable (Encodable.encode a ≤ Encodable.encode b))

instance : IsTrans BitString bitStringLE := ⟨fun _ _ _ ↦ le_trans⟩

instance : Std.Antisymm bitStringLE :=
  ⟨fun _ _ h₁ h₂ ↦ Encodable.encode_injective (le_antisymm h₁ h₂)⟩

instance : Std.Total bitStringLE := ⟨fun _ _ ↦ le_total _ _⟩

/-- The canonical *computable* enumeration of a finite set of bit strings: its
elements sorted by their `Encodable` codes.  Unlike `Finset.toList`, this is
computable, so codes built from it are computable functions of the set. -/
def canonicalFinsetList (S : Finset BitString) : List BitString := S.sort bitStringLE

@[simp] theorem canonicalFinsetList_toFinset (S : Finset BitString) :
    (canonicalFinsetList S).toFinset = S := Finset.sort_toFinset S bitStringLE

theorem canonicalFinsetList_nodup (S : Finset BitString) :
    (canonicalFinsetList S).Nodup := Finset.sort_nodup S bitStringLE

@[simp] theorem mem_canonicalFinsetList {S : Finset BitString} {x : BitString} :
    x ∈ canonicalFinsetList S ↔ x ∈ S := Finset.mem_sort bitStringLE

@[simp] theorem length_canonicalFinsetList (S : Finset BitString) :
    (canonicalFinsetList S).length = S.card := Finset.length_sort bitStringLE

/-- Auxiliary: a `foldr` selecting a single point that is absent vanishes. -/
theorem foldr_uniform_zero (l : List BitString) (v : ENNReal) (x : BitString)
    (hx : x ∉ l) :
    l.foldr (fun y acc ↦ (if y = x then v else 0) + acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.mem_cons, not_or] at hx
    rw [List.foldr_cons, if_neg (fun h ↦ hx.1 h.symm), ih hx.2, add_zero]

/-- Auxiliary: over a `Nodup` list containing `x`, the selecting `foldr` yields
the single selected value. -/
theorem foldr_uniform_aux (l : List BitString) (v : ENNReal) (x : BitString)
    (hx : x ∈ l) (hnd : l.Nodup) :
    l.foldr (fun y acc ↦ (if y = x then v else 0) + acc) 0 = v := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · rw [if_pos h.symm, foldr_uniform_zero l v x (by rw [h]; exact hnd.1), add_zero]
    · have hax : a ≠ x := by rintro rfl; exact hnd.1 h
      rw [if_neg hax, zero_add, ih h hnd.2]

/-- A coded uniform distribution on a nonempty finite set.  The data list is the
finite set's canonical *computable* enumeration (`canonicalFinsetList`), with
exact rational mass `1 / S.card` at each point.  Because the enumeration is
computable, the canonical code of this distribution is a computable function of
`S`. -/
def codedUniformOn (S : Finset BitString) (hS : S.Nonempty) :
    CodedFiniteDistribution where
  data := (canonicalFinsetList S).map fun x ↦
    { point := x, mass := ratMassInvNat S.card (Finset.Nonempty.card_pos hS) }

/-
The support of the coded uniform finite-set model is the set itself.
-/
theorem codedUniformOn_support (S : Finset BitString) (hS : S.Nonempty) :
    (codedUniformOn S hS).support = S := by
  have h : ∀ (l : List BitString),
      (List.foldr (fun e acc ↦ insert e.point acc) Finset.empty
        (l.map fun x ↦
          ({ point := x, mass := ratMassInvNat S.card (Finset.Nonempty.card_pos hS) } :
            CodedDistributionEntry)))
        = l.toFinset := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  unfold CodedFiniteDistribution.support codedUniformOn
  rw [h]; exact canonicalFinsetList_toFinset S

/-
The coded uniform finite-set model gives mass `1 / |S|` to each member.
-/
theorem codedUniformOn_mass_of_mem (S : Finset BitString) (hS : S.Nonempty)
    (x : BitString) (hx : x ∈ S) :
    (codedUniformOn S hS).mass x = (S.card : ENNReal)⁻¹ := by
  unfold CodedFiniteDistribution.mass codedUniformOn
  rw [List.foldr_map,
    foldr_uniform_aux _ (ratMassInvNat S.card (Finset.Nonempty.card_pos hS)).value x
      (mem_canonicalFinsetList.mpr hx) (canonicalFinsetList_nodup S)]
  simp [ratMassInvNat, RatMass.value]

/-
The coded uniform finite-set model gives mass zero off the set.
-/
theorem codedUniformOn_mass_of_not_mem (S : Finset BitString) (hS : S.Nonempty)
    (x : BitString) (hx : x ∉ S) :
    (codedUniformOn S hS).mass x = 0 := by
  apply CodedFiniteDistribution.mass_eq_zero_of_not_mem_support
  rw [codedUniformOn_support]; exact hx

/-
The coded uniform finite-set model is a probability distribution.
-/
theorem codedUniformOn_isProbability (S : Finset BitString) (hS : S.Nonempty) :
    (codedUniformOn S hS).IsProbability := by
  unfold CodedFiniteDistribution.IsProbability;
  rw [codedUniformOn_support]
  rw [Finset.sum_congr rfl fun x hx ↦ codedUniformOn_mass_of_mem S hS x hx]
  norm_num [hS.ne_empty]
  rw [ENNReal.mul_inv_cancel] <;> aesop

/-- A `Nodup`, `bitStringLE`-sorted list is exactly the canonical enumeration of
its own underlying set.  (Uniqueness of the sorted enumeration.) -/
theorem canonicalFinsetList_of_sorted (L : List BitString) (hnd : L.Nodup)
    (hsorted : L.Pairwise bitStringLE) : canonicalFinsetList L.toFinset = L := by
  apply List.Perm.eq_of_pairwise (le := bitStringLE) ?_ (Finset.pairwise_sort _ _) hsorted
  · apply List.perm_of_nodup_nodup_toFinset_eq (canonicalFinsetList_nodup _) hnd
    rw [canonicalFinsetList_toFinset]
  · intro a b _ _ hab hba; exact Std.Antisymm.antisymm a b hab hba

/-- The canonical uniform code depends only on the underlying set, not on the
chosen nonemptiness proof. -/
theorem codedUniformOn_code_congr {S T : Finset BitString} (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : S = T) : (codedUniformOn S hS).code = (codedUniformOn T hT).code := by
  subst hST; rfl

/-- Definitional unfolding of the canonical uniform code in terms of
`canonicalFinsetList`. -/
theorem codedUniformOn_code_eq (S : Finset BitString) (hS : S.Nonempty) :
    (codedUniformOn S hS).code = codedDistributionDataCode ((canonicalFinsetList S).map fun x ↦
      { point := x, mass := ratMassInvNat S.card (Finset.Nonempty.card_pos hS) }) := rfl

/-- Nonemptiness of the finite set of strings of a fixed length. -/
theorem codedStringsOfLength_nonempty (n : Nat) : (stringsOfLength n).Nonempty := by
  rw [Finset.card_pos.symm, cardStringsOfLength]
  exact pow_pos (by decide) n

/-- The data list of the coded uniform distribution on all strings of length `n`,
built from the *computable* enumeration `allStrings n` (rather than the
noncomputable `Finset.toList`).  Each string gets exact rational mass `1 / 2 ^ n`. -/
def lengthUniformData (n : Nat) : List CodedDistributionEntry :=
  (allStrings n).map fun x ↦
    { point := x, mass := ratMassInvNat (2 ^ n) (pow_pos (by decide) n) }

/-- The coded uniform distribution on all strings of length `n`.

It is defined through the computable list `allStrings n`, so its canonical code is
a computable function of `n`. -/
def codedLengthUniform (n : Nat) : CodedFiniteDistribution where
  data := lengthUniformData n

theorem codedLengthUniform_mass_of_mem (n : Nat) (x : BitString) (hx : x.length = n) :
    (codedLengthUniform n).mass x = (2 : ENNReal)⁻¹ ^ n := by
      unfold CodedFiniteDistribution.mass; simp +decide only [RatMass.value];
      unfold codedLengthUniform; simp +decide only [lengthUniformData];
      rw [ List.foldr_map ];
      have h_exists : x ∈ allStrings n := by
        rw [ ← hx ];
        -- By definition of `allStrings`, `x` is in `allStrings (List.length x)`
        -- if and only if `x` has length `List.length x`.
        simp [mem_allStrings];
      have h_unique : List.count x (allStrings n) = 1 := by
        exact List.count_eq_one_of_mem ( allStrings_nodup n ) h_exists;
      have h_foldr : ∀ {l : List BitString}, List.count x l = 1 →
          List.foldr (fun x_1 y ↦ (if x_1 = x then (1 : ENNReal) / (2 ^ n : ENNReal) else 0) + y)
            0 l = (1 : ENNReal) / (2 ^ n : ENNReal) := by
        intros l hl; induction l <;> simp_all +decide [ List.count_cons ];
        split_ifs at hl ⊢ <;> simp_all +decide [ List.count ];
        induction ‹List BitString› <;> aesop;
      convert h_foldr h_unique using 1;
      · norm_num [ ratMassInvNat ];
      · norm_num [ ENNReal.inv_pow ]

theorem codedLengthUniform_mass_of_not_mem (n : Nat) (x : BitString) (hx : x.length ≠ n) :
    (codedLengthUniform n).mass x = 0 := by
      -- By definition of `codedLengthUniform`, we know that the mass of `x` is
      -- zero if `x` is not in the support of `lengthUniformData n`.
      have h_mass_zero : ∀ e ∈ lengthUniformData n, e.point ≠ x := by
        intro e he
        simp [lengthUniformData] at he;
        grind;
      have h_mass_zero : ∀ (l : List CodedDistributionEntry), (∀ e ∈ l, e.point ≠ x) →
          (List.foldr (fun e acc ↦ (if e.point = x then e.mass.value else 0) + acc) 0 l) = 0 := by
        intro l hl; induction l <;> aesop;
      exact h_mass_zero _ ‹_›

theorem codedLengthUniform_support (n : Nat) :
    (codedLengthUniform n).support = stringsOfLength n := by
      unfold CodedFiniteDistribution.support codedLengthUniform lengthUniformData
      rw [List.foldr_map]
      have h_foldr : ∀ (l : List BitString),
          List.foldr (fun e acc ↦ insert e acc) Finset.empty l = l.toFinset := by
        intro l
        induction l with
        | nil => rfl
        | cons a l ih => simp only [List.foldr_cons, List.toFinset_cons]; rw [ih]
      rw [h_foldr]
      rfl

theorem codedLengthUniform_isProbability (n : Nat) :
    (codedLengthUniform n).IsProbability := by
      unfold CodedFiniteDistribution.IsProbability; simp +decide only [codedLengthUniform];
      -- By definition of `codedLengthUniform`, the support is `stringsOfLength n`
      -- and the mass is `(2 : ENNReal)⁻¹ ^ n` for all `x` in the support.
      have h_support : ( codedLengthUniform n ).support = stringsOfLength n := by
        grind +suggestions
      have h_mass : ∀ x ∈ stringsOfLength n,
          (codedLengthUniform n).mass x = (2 : ENNReal)⁻¹ ^ n := by
        grind +suggestions;
      convert Finset.sum_congr rfl h_mass using 1;
      · exact h_support ▸ rfl;
      · norm_num [ cardStringsOfLength ];
        rw [ ← mul_pow, ENNReal.mul_inv_cancel ] <;> norm_num

end Kolmogorov
