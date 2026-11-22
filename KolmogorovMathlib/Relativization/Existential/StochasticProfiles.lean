/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Existential.ProfileRelativization

/-!
# Stochastic Profiles

This module develops the existential relativization argument for stochastic profiles using
finite counting, conditional chain rules, and symmetry of information. It formalizes the
extended counting result and profile construction associated with Theorem 5 of Muchnik and
Romashchenko's *Stability of properties of Kolmogorov complexity under relativization*.
-/

namespace Kolmogorov.Relativization
open Finset

/-- Counting in a finite set selects a tuple with conditional complexity at least the
logarithm of the set's size. This supplies the counting bound used by
`theorem5_extended_counting_choice`. -/
private theorem theorem5_extended_finite_counting
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∀ (x : Fin n → BitString) (Q : Finset (Fin m → BitString)), Q.Nonempty →
      ∃ y' ∈ Q,
        Nat.log2 Q.card ≤ natCondK D (tupleCode y') (tupleCode x) := by
  classical
  intro x Q hQ
  have hTupleCodeInj : Function.Injective (tupleCode : (Fin m → BitString) → BitString) := by
    intro u v huv
    apply List.ofFn_injective
    exact listCode_injective huv
  let A : Finset BitString := Q.image tupleCode
  have hAcard : 2 ^ Nat.log2 Q.card ≤ A.card := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ hTupleCodeInj]
    have hpos : 0 < Q.card := Finset.card_pos.mpr hQ
    exact (Nat.le_log2 (n := Q.card) (Nat.ne_of_gt hpos)).mp (by rfl)
  obtain ⟨w, hwA, hwK⟩ :=
    Kolmogorov.exists_condK_ge_of_finset_card_pow D A (tupleCode x) (Nat.log2 Q.card) hAcard
  obtain ⟨y', hy'Q, rfl⟩ := Finset.mem_image.mp hwA
  have hfinite := condK_ne_top_of_optimal D hD (tupleCode y') (tupleCode x)
  have hNatEq : (natCondK D (tupleCode y') (tupleCode x) : ℕ∞) =
      condK D (tupleCode y') (tupleCode x) := ENat.natCast_toNat hfinite
  refine ⟨y', hy'Q, ?_⟩
  have hcast : (Nat.log2 Q.card : ℕ∞) ≤
      (natCondK D (tupleCode y') (tupleCode x) : ℕ∞) := by
    rw [hNatEq]
    exact hwK
  exact_mod_cast hcast

/-- The conditional chain rule bounds the complexity of the joined tuple given `z` by the two
successive descriptions, with its logarithmic error measured at the coded original tuple and
oracle. This bound is used in `theorem5_extended_counting_choice`. -/
private theorem theorem5_extended_conditional_chain
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y : Fin m → BitString),
      natCondK D (tupleCode (Fin.append x y)) z ≤
        natCondK D (tupleCode x) z +
          natCondK D (tupleCode y) (pairCode (tupleCode x) z) +
            logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  let joinPair (w : BitString) :=
    listCode (decodeListCode (decodeFirst w) ++ decodeListCode (decodeSecond w))
  have hJoinPair : Computable joinPair := by
    dsimp [joinPair]
    have hfirst : Computable (fun w : BitString => decodeListCode (decodeFirst w)) :=
      decodeListCode_computable.comp decodeFirst_computable
    have hsecond : Computable (fun w : BitString => decodeListCode (decodeSecond w)) :=
      decodeListCode_computable.comp decodeSecond_computable
    exact listCode_computable.comp
      (Computable₂.comp Primrec.list_append.to_comp hfirst hsecond)
  have hJoinPair_append (x : Fin n → BitString) (y : Fin m → BitString) :
      joinPair (pairCode (tupleCode x) (tupleCode y)) =
        tupleCode (Fin.append x y) := by
    unfold joinPair tupleCode
    rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeListCode_listCode,
      decodeListCode_listCode, List.ofFn_fin_append]
  let splitTuple (w : BitString) :=
    pairCode (listCode ((decodeListCode w).take n))
      (listCode ((decodeListCode w).drop n))
  have hSplitTuple : Computable splitTuple := by
    dsimp [splitTuple]
    have hTake : Primrec (fun w : BitString => (decodeListCode w).take n) :=
      Primrec.list_take.comp (Primrec.const n) decodeListCode_primrec
    have hDrop : Primrec (fun w : BitString => (decodeListCode w).drop n) :=
      Primrec.list_drop.comp (Primrec.const n) decodeListCode_primrec
    exact (CodedFiniteDistribution.pairCode_primrec.comp
      (listCode_primrec.comp hTake) (listCode_primrec.comp hDrop)).to_comp
  have hSplitTuple_append (x : Fin n → BitString) (y : Fin m → BitString) :
      splitTuple (tupleCode (Fin.append x y)) = pairCode (tupleCode x) (tupleCode y) := by
    simp [splitTuple, tupleCode, List.ofFn_fin_append]
  obtain ⟨cJoin, hJoin⟩ := condK_map_le D hD joinPair hJoinPair
  obtain ⟨cSplit, hSplitPlain⟩ := plainK_map_le D hD splitTuple hSplitTuple
  obtain ⟨cFirst, hFirst⟩ := plainK_map_le D hD decodeFirst decodeFirst_computable
  obtain ⟨cCond, hCondPlain⟩ := condK_le_plainK D hD
  obtain ⟨cChain, hChain⟩ := condK_pairCode_chain_upper_values D hD
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cChain 1 (cFirst + cSplit + cCond + 1)
  refine ⟨cFold + cJoin, ?_⟩
  intro x z y
  let ux := tupleCode x
  let uy := tupleCode y
  let u := tupleCode (Fin.append x y)
  let p := pairCode ux uy
  let N := natK D (pairCode u z)
  have hJoinRaw := hJoin p z
  rw [hJoinPair_append] at hJoinRaw
  have hJoinNat : natCondK D u z ≤ natCondK D p z + cJoin := by
    have hf₁ := condK_ne_top_of_optimal D hD u z
    have hf₂ := condK_ne_top_of_optimal D hD p z
    rw [← ENat.natCast_toNat hf₁, ← ENat.natCast_toNat hf₂] at hJoinRaw
    exact_mod_cast hJoinRaw
  have hSplitRaw := hSplitPlain u
  rw [hSplitTuple_append] at hSplitRaw
  have hSplitNat : natK D p ≤ natK D u + cSplit := by
    have hf₁ := plainK_ne_top D hD p
    have hf₂ := plainK_ne_top D hD u
    rw [← ENat.natCast_toNat hf₁, ← ENat.natCast_toNat hf₂] at hSplitRaw
    exact_mod_cast hSplitRaw
  have hFirstRaw := hFirst (pairCode u z)
  rw [decodeFirst_pairCode] at hFirstRaw
  have hFirstNat : natK D u ≤ N + cFirst := by
    have hf₁ := plainK_ne_top D hD u
    have hf₂ := plainK_ne_top D hD (pairCode u z)
    rw [← ENat.natCast_toNat hf₁, ← ENat.natCast_toNat hf₂] at hFirstRaw
    exact_mod_cast hFirstRaw
  have hCondRaw := hCondPlain p z
  have hCondNat : natCondK D p z ≤ natK D p + cCond := by
    have hf₁ := condK_ne_top_of_optimal D hD p z
    have hf₂ := plainK_ne_top D hD p
    rw [← ENat.natCast_toNat hf₁, ← ENat.natCast_toNat hf₂] at hCondRaw
    exact_mod_cast hCondRaw
  have hPairBound : natCondK D p z + 1 ≤ N + (cFirst + cSplit + cCond + 1) := by
    omega
  have hVx : HasPlainConditionalComplexityValue D ux z (natCondK D ux z) := by
    unfold HasPlainConditionalComplexityValue natCondK
    exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD ux z)).symm
  have hVy : HasPlainConditionalComplexityValue D uy (pairCode ux z)
      (natCondK D uy (pairCode ux z)) := by
    unfold HasPlainConditionalComplexityValue natCondK
    exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD uy (pairCode ux z))).symm
  have hVp : HasPlainConditionalComplexityValue D p z (natCondK D p z) := by
    unfold HasPlainConditionalComplexityValue natCondK
    exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD p z)).symm
  have hPairChain := hChain ux uy z (natCondK D ux z)
    (natCondK D uy (pairCode ux z)) (natCondK D p z) hVx hVy hVp
  have hPairChain' : natCondK D p z ≤ natCondK D ux z +
      natCondK D uy (pairCode ux z) + logSlack cFold N := by
    have hErr := logSlack_le_of_linear_bound
      (p := natCondK D p z + 1) (M := N) (a := 1)
      (b := cFirst + cSplit + cCond + 1) hFold (by omega)
    exact (hPairChain.trans (Nat.add_le_add_left hErr _))
  have hOut : natCondK D u z ≤
      natCondK D ux z + natCondK D uy (pairCode ux z) +
        logSlack (cFold + cJoin) N := by
    calc
      natCondK D u z ≤ natCondK D p z + cJoin := hJoinNat
      _ ≤ natCondK D ux z + natCondK D uy (pairCode ux z) + logSlack cFold N + cJoin :=
        Nat.add_le_add_right hPairChain' cJoin
      _ ≤ natCondK D ux z + natCondK D uy (pairCode ux z) +
          logSlack (cFold + cJoin) N := by
        rw [Nat.add_assoc]
        exact Nat.add_le_add_left (logSlack_add_nat_le cFold cJoin N) _
  simpa [ux, uy, u, N] using hOut

/-- Symmetry of information converts a tuple with high complexity given `x` into high
unconditional complexity of the joined tuple. The component length bound controls the logarithmic
error by the original tuple-and-oracle complexity, as used in
`theorem5_extended_counting_choice`. -/
private theorem theorem5_extended_tuple_symmetry
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (y y' : Fin m → BitString),
      (∀ i : Fin m, (y' i).length ≤
        natK D (pairCode (tupleCode (Fin.append x y)) z)) →
      (natK D (tupleCode x) : ℤ) + natCondK D (tupleCode y') (tupleCode x) ≤
        (natK D (tupleCode (Fin.append x y')) : ℤ) +
          logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  let splitTuple (w : BitString) :=
    pairCode (listCode ((decodeListCode w).take n))
      (listCode ((decodeListCode w).drop n))
  have hSplitTuple : Computable splitTuple := by
    dsimp [splitTuple]
    have hTake : Primrec (fun w : BitString => (decodeListCode w).take n) :=
      Primrec.list_take.comp (Primrec.const n) decodeListCode_primrec
    have hDrop : Primrec (fun w : BitString => (decodeListCode w).drop n) :=
      Primrec.list_drop.comp (Primrec.const n) decodeListCode_primrec
    exact (CodedFiniteDistribution.pairCode_primrec.comp
      (listCode_primrec.comp hTake) (listCode_primrec.comp hDrop)).to_comp
  have hSplitTuple_append (x : Fin n → BitString) (y : Fin m → BitString) :
      splitTuple (tupleCode (Fin.append x y)) = pairCode (tupleCode x) (tupleCode y) := by
    simp [splitTuple, tupleCode, List.ofFn_fin_append]
  let firstTuple (w : BitString) :=
    listCode ((decodeListCode (decodeFirst w)).take n)
  have hFirstTuple : Computable firstTuple := by
    dsimp [firstTuple]
    have hTake : Primrec (fun w : BitString => (decodeListCode (decodeFirst w)).take n) :=
      Primrec.list_take.comp (Primrec.const n)
        (decodeListCode_primrec.comp CodedFiniteDistribution.decodeFirst_primrec)
    exact (listCode_primrec.comp hTake).to_comp
  have hFirstTuple_pair (x : Fin n → BitString) (y : Fin m → BitString) (z : BitString) :
      firstTuple (pairCode (tupleCode (Fin.append x y)) z) = tupleCode x := by
    unfold firstTuple tupleCode
    rw [decodeFirst_pairCode, decodeListCode_listCode, List.ofFn_fin_append]
    simp
  obtain ⟨cSplit, hSplit⟩ := plainK_map_le D hD splitTuple hSplitTuple
  obtain ⟨cFirst, hFirst⟩ := plainK_map_le D hD firstTuple hFirstTuple
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  obtain ⟨cPairUpper, hPairUpper⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨cPairSym, hPairSym⟩ := pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cArg, hArgFold⟩ :=
    logSlack_linear_bound cPairSym (3 + 2 * m)
      (3 * cFirst + m + cLit + cPairUpper + 1)
  refine ⟨cArg + cSplit, ?_⟩
  intro x z y y' hyLen
  let ux := tupleCode x
  let uy := tupleCode y'
  let u := tupleCode (Fin.append x y)
  let u' := tupleCode (Fin.append x y')
  let p := pairCode ux uy
  let N := natK D (pairCode u z)
  have hFirstRaw := hFirst (pairCode u z)
  rw [hFirstTuple_pair] at hFirstRaw
  have hXBound : natK D ux ≤ N + cFirst := by
    have hf₁ := plainK_ne_top D hD ux
    have hf₂ := plainK_ne_top D hD (pairCode u z)
    rw [← ENat.natCast_toNat hf₁, ← ENat.natCast_toNat hf₂] at hFirstRaw
    exact_mod_cast hFirstRaw
  have hListBound : ∀ l : List BitString,
      (∀ s ∈ l, s.length ≤ N) → (listCode l).length ≤ l.length * (2 * N + 1) := by
    intro l
    induction l with
    | nil =>
        intro _
        simp [listCode]
    | cons s l ih =>
        intro hall
        have hs := hall s (by simp)
        have ht : ∀ t ∈ l, t.length ≤ N := by
          intro t ht
          exact hall t (by simp [ht])
        have htail := ih ht
        rw [length_listCode_cons, List.length_cons]
        nlinarith
  have hCodeLength : uy.length ≤ m * (2 * N + 1) := by
    have h := hListBound (List.ofFn y') (by
      intro s hs
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
      exact hyLen i)
    simpa [uy, tupleCode] using h
  have hYLiteral : natK D uy ≤ m * (2 * N + 1) + cLit := by
    have hRaw := hLit uy
    have hf := plainK_ne_top D hD uy
    have hCast : (natK D uy : ℕ∞) ≤ ((uy.length + cLit : ℕ) : ℕ∞) := by
      change ((plainK D uy).toNat : ℕ∞) ≤ _
      rw [ENat.natCast_toNat hf]
      simpa [programLength] using hRaw
    exact (Nat.le_trans (by exact_mod_cast hCast) (Nat.add_le_add_right hCodeLength cLit))
  have hSplitRaw := hSplit u'
  rw [hSplitTuple_append] at hSplitRaw
  have hPairToTuple : natK D p ≤ natK D u' + cSplit := by
    have hf₁ := plainK_ne_top D hD p
    have hf₂ := plainK_ne_top D hD u'
    rw [← ENat.natCast_toNat hf₁, ← ENat.natCast_toNat hf₂] at hSplitRaw
    exact_mod_cast hSplitRaw
  have hUxValue : HasPlainComplexityValue D ux (natK D ux) := by
    unfold HasPlainComplexityValue natK
    exact (ENat.natCast_toNat (plainK_ne_top D hD ux)).symm
  have hUyValue : HasPlainComplexityValue D uy (natK D uy) := by
    unfold HasPlainComplexityValue natK
    exact (ENat.natCast_toNat (plainK_ne_top D hD uy)).symm
  have hCondValue : HasPlainConditionalComplexityValue D uy ux
      (natCondK D uy ux) := by
    unfold HasPlainConditionalComplexityValue natCondK
    exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD uy ux)).symm
  have hPairValue : HasPlainComplexityValue D p (natK D p) := by
    unfold HasPlainComplexityValue natK
    exact (ENat.natCast_toNat (plainK_ne_top D hD p)).symm
  have hPairSym := hPairSym ux uy (natK D ux) (natCondK D uy ux) (natK D p)
    hUxValue hCondValue hPairValue
  have hPairUpperRaw := hPairUpper ux uy
  have hPairUpperNat : natK D p ≤ natK D ux + natK D uy +
      (2 * Nat.log 2 (natK D ux) + cPairUpper) := by
    have hf₁ := plainK_ne_top D hD p
    have hf₂ := plainK_ne_top D hD ux
    have hf₃ := plainK_ne_top D hD uy
    rw [cPair, ← ENat.natCast_toNat hf₁,
      ← ENat.natCast_toNat hf₂, ← ENat.natCast_toNat hf₃,
      cVal, ← ENat.natCast_toNat hf₂] at hPairUpperRaw
    exact_mod_cast hPairUpperRaw
  have hLogX : Nat.log 2 (natK D ux) ≤ natK D ux := Nat.log_le_self 2 _
  have hPairLinear : natK D p + 1 ≤
      (3 + 2 * m) * N + (3 * cFirst + m + cLit + cPairUpper + 1) := by
    have hPairCoarse : natK D p ≤ 3 * natK D ux + natK D uy + cPairUpper := by
      nlinarith [hPairUpperNat, hLogX]
    nlinarith [hPairCoarse, hXBound, hYLiteral]
  have hErr : logSlack cPairSym (natK D p + 1) ≤ logSlack cArg N := by
    exact logSlack_le_of_linear_bound hArgFold hPairLinear
  have hSymNat : natK D ux + natCondK D uy ux ≤
      natK D p + logSlack cPairSym (natK D p + 1) := hPairSym.2
  have hSymFolded : natK D ux + natCondK D uy ux ≤
      natK D u' + logSlack (cArg + cSplit) N := by
    calc
      natK D ux + natCondK D uy ux ≤ natK D p + logSlack cPairSym (natK D p + 1) := hSymNat
      _ ≤ natK D u' + cSplit + logSlack cArg N := by omega
      _ ≤ natK D u' + logSlack (cArg + cSplit) N := by
        have h := logSlack_add_nat_le cArg cSplit N
        omega
  exact_mod_cast (by simpa [ux, uy, u, u', p, N] using hSymFolded)

/-- Counting in a sufficiently large section selects a tuple whose unconditional complexity
compensates for the information in `x`, providing the counting choice in `theorem5_extended`. -/
private theorem theorem5_extended_counting_choice (D : Map)
    (hD : isOptimalConditional D) (n m cQ : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (y : Fin m → BitString) (Q : Finset (Fin m → BitString)),
      Q.Nonempty →
      natCondK D (tupleCode y) (pairCode (tupleCode x) z) ≤
        Nat.log2 Q.card +
          logSlack cQ (natK D (pairCode (tupleCode (Fin.append x y)) z)) →
      (∀ y' ∈ Q, ∀ i : Fin m,
        (y' i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) →
      ∃ y' ∈ Q,
        (natCondK D (tupleCode (Fin.append x y)) z : ℤ) ≤
          (natK D (tupleCode (Fin.append x y')) : ℤ) -
            ((natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z) +
            logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  have hCount := theorem5_extended_finite_counting
    D hD n m
  obtain ⟨cChain, hChain⟩ :=
    theorem5_extended_conditional_chain D hD n m
  obtain ⟨cSym, hSym⟩ :=
    theorem5_extended_tuple_symmetry D hD n m
  refine ⟨cChain + cQ + cSym, ?_⟩
  intro x z y Q hQ hQComplex hQLength
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  obtain ⟨y', hy'Q, hCount'⟩ := hCount x Q hQ
  have hHyp : (natCondK D (tupleCode y) (pairCode (tupleCode x) z) : ℤ) ≤
      Nat.log2 Q.card + logSlack cQ N := by
    exact_mod_cast hQComplex
  have hCountInt : (Nat.log2 Q.card : ℤ) ≤
      natCondK D (tupleCode y') (tupleCode x) := by
    exact_mod_cast hCount'
  have hChain := hChain x z y
  have hChainInt : (natCondK D (tupleCode (Fin.append x y)) z : ℤ) ≤
      natCondK D (tupleCode x) z +
        natCondK D (tupleCode y) (pairCode (tupleCode x) z) + logSlack cChain N := by
    exact_mod_cast (by simpa [N] using hChain)
  have hSym := hSym x z y y' (fun i => hQLength y' hy'Q i)
  have hSymInt : (natK D (tupleCode x) : ℤ) +
      (natCondK D (tupleCode y') (tupleCode x) : ℤ) ≤
        (natK D (tupleCode (Fin.append x y')) : ℤ) + (logSlack cSym N : ℤ) := by
    simpa [N] using hSym
  have hSlack : logSlack cChain N + logSlack cQ N + logSlack cSym N ≤
      logSlack (cChain + cQ + cSym) N := by
    unfold logSlack
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have hSlack' : logSlack cChain N + logSlack cQ N + logSlack cSym N ≤
      logSlack (cChain + cQ + cSym) N := hSlack
  refine ⟨y', hy'Q, ?_⟩
  have hTarget : (natCondK D (tupleCode (Fin.append x y)) z : ℤ) ≤
      natK D (tupleCode (Fin.append x y')) -
        ((natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z) +
        logSlack (cChain + cQ + cSym) N := by
    omega
  simpa [N] using hTarget

private lemma theorem5_extended_pair_condition (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ a b : BitString,
      natCondK D a (pairCode b []) ≤ natCondK D a b + c ∧
      natCondK D a b ≤ natCondK D a (pairCode b []) + c := by
  have hPair : Computable (fun b : BitString => pairCode b []) :=
    pairCode_computable.comp (Computable.id.pair (Computable.const []))
  obtain ⟨c₁, hc₁⟩ := condK_cond_map_le D hD (fun b : BitString => pairCode b []) hPair
  obtain ⟨c₂, hc₂⟩ := condK_cond_map_le D hD decodeFirst decodeFirst_computable
  refine ⟨c₁ + c₂, ?_⟩
  intro a b
  constructor
  · have hcond : condK D a (pairCode b []) ≤ condK D a b + (c₂ : ℕ∞) := by
      simpa only [decodeFirst_pairCode] using hc₂ a (pairCode b [])
    have hfiniteA := avgCond_condK_ne_top D hD a (pairCode b [])
    have hfiniteB := avgCond_condK_ne_top D hD a b
    rw [← ENat.natCast_toNat hfiniteA, ← ENat.natCast_toNat hfiniteB] at hcond
    have hnat : natCondK D a (pairCode b []) ≤ natCondK D a b + c₂ := by
      exact_mod_cast hcond
    omega
  · have hcond : condK D a b ≤ condK D a (pairCode b []) + (c₁ : ℕ∞) :=
      hc₁ a b
    have hfiniteA := avgCond_condK_ne_top D hD a b
    have hfiniteB := avgCond_condK_ne_top D hD a (pairCode b [])
    rw [← ENat.natCast_toNat hfiniteA, ← ENat.natCast_toNat hfiniteB] at hcond
    have hnat : natCondK D a b ≤ natCondK D a (pairCode b []) + c₁ := by
      exact_mod_cast hcond
    omega

private lemma theorem5_extended_nat_cond_bound (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ u z : BitString,
      natCondK D u z ≤ natK D u + c := by
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  refine ⟨cCond, ?_⟩
  intro u z
  have hCondRaw := hCond u z
  have hCondFinite : condK D u z ≠ ⊤ := by
    apply ne_top_of_le_natCast_add
    calc
      condK D u z ≤ plainK D u + (cCond : ℕ∞) := hCondRaw
      _ ≤ (programLength u : ℕ∞) + cLen + cCond := by
        gcongr
        exact hLen u
  have hUFinite : plainK D u ≠ ⊤ := plainK_ne_top D hD u
  rw [← ENat.natCast_toNat hCondFinite, ← ENat.natCast_toNat hUFinite] at hCondRaw
  exact_mod_cast hCondRaw

private lemma theorem5_extended_cond_budget (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ u z : BitString,
      natCondK D u z ≤ natK D (pairCode u z) + c := by
  obtain ⟨cCond, hCond⟩ := theorem5_extended_nat_cond_bound D hD
  obtain ⟨cProj, hProj⟩ := plainK_map_le D hD decodeFirst decodeFirst_computable
  refine ⟨cCond + cProj, ?_⟩
  intro u z
  have hUFinite : plainK D u ≠ ⊤ := plainK_ne_top D hD u
  have hCondNat := hCond u z
  have hProjRaw : plainK D (decodeFirst (pairCode u z)) ≤
      plainK D (pairCode u z) + (cProj : ℕ∞) := hProj (pairCode u z)
  rw [decodeFirst_pairCode] at hProjRaw
  have hPairFinite : plainK D (pairCode u z) ≠ ⊤ :=
    plainK_ne_top D hD (pairCode u z)
  rw [← ENat.natCast_toNat hUFinite, ← ENat.natCast_toNat hPairFinite] at hProjRaw
  have hProjNat : natK D u ≤ natK D (pairCode u z) + cProj := by
    exact_mod_cast hProjRaw
  omega

/-- Lemma 3 turns the construction's one-sided profile and complexity bounds into both profile
inequalities for the selected tuple in `theorem5_extended`. -/
private theorem theorem5_extended_apply_lemma3 (D : Map)
    (hD : isOptimalConditional D) (n m cP cB : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (y y' : Fin m → BitString) (δ : ℕ),
      ((natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z) ≤ δ →
      (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        (subCondK D (Fin.append x y') V W : ℤ) ≤
          subCondKRel D (Fin.append x y) z V W +
            ((natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z) +
            logSlack cP (natK D (pairCode (tupleCode (Fin.append x y)) z))) →
      (natCondK D (tupleCode (Fin.append x y)) z : ℤ) ≤
        (natK D (tupleCode (Fin.append x y')) : ℤ) -
          ((natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z) +
          logSlack cB (natK D (pairCode (tupleCode (Fin.append x y)) z)) →
      ExtProfileWithin (subCondKRel D (Fin.append x y) z)
        (subCondK D (Fin.append x y'))
        (δ + logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
  obtain ⟨cRel, hRel⟩ := lemma3_relativized D hD (n + m)
  obtain ⟨cPair, hPair⟩ := theorem5_extended_pair_condition D hD
  obtain ⟨cCond, hCond⟩ := theorem5_extended_nat_cond_bound D hD
  obtain ⟨cBudget, hBudget⟩ := theorem5_extended_cond_budget D hD
  obtain ⟨cFold, hFold⟩ := logSlack_absorb_of_le_linear cRel 1 cBudget
  refine ⟨2 * cP + cB + cFold + 2 * cCond + 3 * cPair, ?_⟩
  intro x z y y' δ hI hProfile hBase
  let u : Fin (n + m) → BitString := Fin.append x y
  let u' : Fin (n + m) → BitString := Fin.append x y'
  let N := natK D (pairCode (tupleCode u) z)
  let I : ℤ := (natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z
  have hIlower : -(cCond : ℤ) ≤ I := by
    have h := hCond (tupleCode x) z
    dsimp [I]
    omega
  have hδ₁nonneg : 0 ≤ I + cCond + logSlack cP N + cPair := by
    have hs : 0 ≤ logSlack cP N := Nat.cast_nonneg _
    omega
  have hProfile' : ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      (subCondKRel D u' [] V W : ℤ) ≤
        subCondKRel D u z V W + (I + cCond + logSlack cP N + cPair) := by
    intro V W hV hdis
    have hP := hProfile V W hV hdis
    have hP' : (subCondK D u' V W : ℤ) ≤
        subCondKRel D u z V W + I + logSlack cP N := by
      simpa [u, u', I, N] using hP
    have hPair' := hPair (subtupleCode u' V) (subtupleCode u' W)
    have hPairZ : (subCondKRel D u' [] V W : ℤ) ≤ subCondK D u' V W + cPair := by
      change (natCondK D (subtupleCode u' V)
        (pairCode (subtupleCode u' W) []) : ℤ) ≤ _
      exact_mod_cast hPair'.1
    omega
  have hBase' : (natCondK D (tupleCode u) z : ℤ) ≤
      natCondK D (tupleCode u') [] +
        (-I + logSlack cB N) := by
    change (natCondK D (tupleCode u) z : ℤ) ≤
      (natK D (tupleCode u') : ℤ) + (-I + logSlack cB N)
    have hB : (natCondK D (tupleCode u) z : ℤ) ≤
        (natK D (tupleCode u') : ℤ) - I + logSlack cB N := by
      simpa [u, u', I, N] using hBase
    calc
      (natCondK D (tupleCode u) z : ℤ) ≤
          (natK D (tupleCode u') : ℤ) - I + logSlack cB N := hB
      _ = (natK D (tupleCode u') : ℤ) + (-I + logSlack cB N) := by ring
  have hRel' := hRel u u' z [] (I + cCond + logSlack cP N + cPair)
    (-I + logSlack cB N) hδ₁nonneg hProfile' hBase'
  have hBudget' := hBudget (tupleCode u) z
  have hFoldN : logSlack cRel (natCondK D (tupleCode u) z) ≤ logSlack cFold N := by
    apply hFold N (natCondK D (tupleCode u) z)
    dsimp [N]
    simpa using hBudget'
  have hSlackNat :
      2 * logSlack cP N + logSlack cB N + logSlack cFold N +
        (2 * cCond + 3 * cPair) ≤
          logSlack (2 * cP + cB + cFold + 2 * cCond + 3 * cPair) N := by
    have hsP : logSlack cP N + logSlack cP N = logSlack (2 * cP) N := by
      simpa [two_mul] using logSlack_add_const cP cP N
    have hsPB : logSlack (2 * cP) N + logSlack cB N =
        logSlack (2 * cP + cB) N := logSlack_add_const (2 * cP) cB N
    have hsPBF : logSlack (2 * cP + cB) N + logSlack cFold N =
        logSlack (2 * cP + cB + cFold) N :=
      logSlack_add_const (2 * cP + cB) cFold N
    calc
      2 * logSlack cP N + logSlack cB N + logSlack cFold N +
          (2 * cCond + 3 * cPair) =
          logSlack (2 * cP + cB + cFold) N + (2 * cCond + 3 * cPair) := by
            rw [show 2 * logSlack cP N =
              logSlack cP N + logSlack cP N by omega, hsP, hsPB, hsPBF]
      _ ≤ logSlack (2 * cP + cB + cFold + 2 * cCond + 3 * cPair) N := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          logSlack_add_nat_le (2 * cP + cB + cFold) (2 * cCond + 3 * cPair) N
  have hSlackZ :
      ((2 * logSlack cP N + logSlack cB N + logSlack cFold N +
        (2 * cCond + 3 * cPair) : ℕ) : ℤ) ≤
        logSlack (2 * cP + cB + cFold + 2 * cCond + 3 * cPair) N := by
    exact_mod_cast hSlackNat
  intro V W hV hdis
  constructor
  · have hR := hRel' V W hV hdis
    have hPair' := hPair (subtupleCode u' V) (subtupleCode u' W)
    have hPairZ : (subCondKRel D u' [] V W : ℤ) ≤ subCondK D u' V W + cPair := by
      change (natCondK D (subtupleCode u' V)
        (pairCode (subtupleCode u' W) []) : ℤ) ≤ _
      exact_mod_cast hPair'.1
    have hFoldZ : (logSlack cRel (natCondK D (tupleCode u) z) : ℤ) ≤
        logSlack cFold N := by exact_mod_cast hFoldN
    have hsmall : I ≤ δ := by simpa [I] using hI
    have hGoal : (subCondKRel D u z V W : ℤ) ≤
        subCondK D u' V W + δ +
          logSlack (2 * cP + cB + cFold + 2 * cCond + 3 * cPair) N := by
      omega
    have hGoalNat : subCondKRel D (Fin.append x y) z V W ≤
        subCondK D (Fin.append x y') V W + δ +
          logSlack (2 * cP + cB + cFold + 2 * cCond + 3 * cPair) N := by
      exact_mod_cast hGoal
    simpa [Nat.add_assoc, u, u', N] using hGoalNat
  · have hP := hProfile V W hV hdis
    have hP' : (subCondK D u' V W : ℤ) ≤
        subCondKRel D u z V W + I + logSlack cP N := by
      simpa [u, u', I, N] using hP
    have hI' : (natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z ≤ δ := hI
    have hSlackP : logSlack cP N ≤
        logSlack (2 * cP + cB + cFold + 2 * cCond + 3 * cPair) N := by
      apply logSlack_mono_left
      omega
    have hGoal : (subCondK D u' V W : ℤ) ≤
        subCondKRel D u z V W + δ +
          logSlack (2 * cP + cB + cFold + 2 * cCond + 3 * cPair) N := by
      have hs : (logSlack cP N : ℤ) ≤
          logSlack (2 * cP + cB + cFold + 2 * cCond + 3 * cPair) N := by
        exact_mod_cast hSlackP
      omega
    have : subCondK D u' V W ≤
        subCondKRel D u z V W + δ +
          logSlack (2 * cP + cB + cFold + 2 * cCond + 3 * cPair) N := by
      exact_mod_cast hGoal
    simpa [Nat.add_assoc, u, u', N] using this

/-- **Theorem 5 for extended profiles.**  If `x̄` is `(a log N₀, a log N₀)`-stochastic,
`N₀ = K(x̄)`, and `I(x̄ : z) ≤ δ`, then for every `ȳ` there is a `ȳ'` with
`ρ(K'(x̄, ȳ | z), K'(x̄, ȳ')) ≤ δ + O(log K(x̄, ȳ, z))`.  This is the last formula of the proof
of Theorem 5 in Section 4 (Steps 1–4, Lemma 7, Remark 3, and Lemma 3 with `δ₁ = −δ₂ = I(x̄ : z)`,
for which see `lemma3_relativized`). -/
theorem theorem5_extended (D : Map) (hD : isOptimalConditional D) (n m a : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (δ : ℕ),
      IsStochasticTuple D x (logSlack a (natK D (tupleCode x)))
          (logSlack a (natK D (tupleCode x))) →
      MutualInfoLe D (tupleCode x) z δ →
        ∀ y : Fin m → BitString, ∃ y' : Fin m → BitString,
          ExtProfileWithin (subCondKRel D (Fin.append x y) z) (subCondK D (Fin.append x y'))
            (δ + logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
  obtain ⟨cModel, hModel⟩ := theorem5_extended_stochastic_model D hD n a
  obtain ⟨cSection, hSection⟩ :=
    theorem5_extended_aggregate_section D hD n m cModel
  obtain ⟨cCount, hCount⟩ :=
    theorem5_extended_counting_choice D hD n m cSection
  obtain ⟨cFinal, hFinal⟩ :=
    theorem5_extended_apply_lemma3 D hD n m cSection cCount
  refine ⟨cFinal, ?_⟩
  intro x z δ hxStoch hxInfo y
  obtain ⟨S, hxS, hSCode, hSCard⟩ := hModel x hxStoch
  obtain ⟨Q, hQNonempty, hQSize, hQLength, hQProfile⟩ :=
    hSection x z S hxS hSCode hSCard y
  obtain ⟨y', hy'Q, hBase⟩ := hCount x z y Q hQNonempty hQSize hQLength
  have hInfoZ : (natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z ≤ δ := by
    change natK D (tupleCode x) ≤ natCondK D (tupleCode x) z + δ at hxInfo
    omega
  exact ⟨y', hFinal x z y y' δ hInfoZ (fun V W hV hdis =>
    hQProfile y' hy'Q V W hV hdis) hBase⟩

/-- **Theorem 5.** Conjecture 3 holds for stochastic `x̄`: if `x̄` is
`(a log N₀, a log N₀)`-stochastic, `N₀ = K(x̄)`, and `I(x̄ : z) ≤ δ`, then for every `ȳ` there is
a `ȳ'` such that the profiles `K(x̄, ȳ | z)` and `K(x̄, ȳ')` differ componentwise by at most
`δ + O(log K(x̄, ȳ, z))`; the constant depends on `n`, `m` and `a`.  Proof: Section 4. -/
theorem theorem5 (D : Map) (hD : isOptimalConditional D) (n m a : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (δ : ℕ),
      IsStochasticTuple D x (logSlack a (natK D (tupleCode x)))
          (logSlack a (natK D (tupleCode x))) →
      MutualInfoLe D (tupleCode x) z δ →
        ∀ y : Fin m → BitString, ∃ y' : Fin m → BitString,
          ProfileWithin (subKRel D (Fin.append x y) z) (subK D (Fin.append x y'))
            (δ + logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
  obtain ⟨c₀, h₀⟩ := theorem5_extended D hD n m a
  obtain ⟨c₁, h₁⟩ := condK_cond_map_le D hD (fun z : BitString => pairCode [] z)
    (pairCode_computable.comp ((Computable.const ([] : BitString)).pair Computable.id))
  obtain ⟨c₂, h₂⟩ := condK_cond_map_le D hD decodeSecond decodeSecond_computable
  let c₃ := max c₁ c₂
  refine ⟨c₀ + c₃, ?_⟩
  intro x z δ hx hz y
  obtain ⟨y', hProf⟩ := h₀ x z δ hx hz y
  refine ⟨y', ?_⟩
  have hNatBound {u v w : BitString} {k : ℕ}
      (h : condK D u v ≤ condK D u w + (k : ℕ∞)) :
      natCondK D u v ≤ natCondK D u w + k := by
    have hv := avgCond_condK_ne_top D hD u v
    have hw := avgCond_condK_ne_top D hD u w
    change (condK D u v).toNat ≤ (condK D u w).toNat + k
    have h' : ((condK D u v).toNat : ℕ∞) ≤
        (((condK D u w).toNat + k : ℕ) : ℕ∞) := by
      calc
        ((condK D u v).toNat : ℕ∞) = condK D u v := ENat.natCast_toNat hv
        _ ≤ condK D u w + (k : ℕ∞) := h
        _ = ((condK D u w).toNat : ℕ∞) + (k : ℕ∞) := by
          rw [ENat.natCast_toNat hw]
        _ = (((condK D u w).toNat + k : ℕ) : ℕ∞) := by
          push_cast
          rfl
    exact_mod_cast h'
  have hConst : c₃ ≤ logSlack c₃
      (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
    unfold logSlack c₃
    omega
  have hSlack : δ + logSlack c₀
        (natK D (pairCode (tupleCode (Fin.append x y)) z)) + c₃ ≤
      δ + logSlack (c₀ + c₃)
        (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
    calc
      δ + logSlack c₀
          (natK D (pairCode (tupleCode (Fin.append x y)) z)) + c₃ ≤
        δ + logSlack c₀
          (natK D (pairCode (tupleCode (Fin.append x y)) z)) +
          logSlack c₃ (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
            omega
      _ = δ + logSlack (c₀ + c₃)
          (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
            rw [Nat.add_assoc, ← logSlack_add_constants]
  intro V hV
  have hdis : Disjoint V (∅ : Finset (Fin (n + m))) := by simp
  obtain ⟨hUpper, hLower⟩ := hProf V ∅ hV hdis
  have hUpper' : natCondK D (subtupleCode (Fin.append x y) V) (pairCode [] z) ≤
      natCondK D (subtupleCode (Fin.append x y') V) [] +
        (δ + logSlack c₀
          (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
    simpa [subCondKRel, subCondK] using hUpper
  have hLower' : natCondK D (subtupleCode (Fin.append x y') V) [] ≤
      natCondK D (subtupleCode (Fin.append x y) V) (pairCode [] z) +
        (δ + logSlack c₀
          (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
    simpa [subCondKRel, subCondK] using hLower
  have hToOracle := hNatBound (h₁ (subtupleCode (Fin.append x y) V) z)
  have hFromOracle := hNatBound (by
    simpa [decodeSecond_pairCode] using
      h₂ (subtupleCode (Fin.append x y) V) (pairCode [] z))
  have hFirst : subKRel D (Fin.append x y) z V ≤
      subK D (Fin.append x y') V +
        (δ + logSlack c₀
          (natK D (pairCode (tupleCode (Fin.append x y)) z)) + c₃) := by
    change natCondK D (subtupleCode (Fin.append x y) V) z ≤
      natCondK D (subtupleCode (Fin.append x y') V) [] +
        (δ + logSlack c₀
          (natK D (pairCode (tupleCode (Fin.append x y)) z)) + c₃)
    unfold c₃ at *
    omega
  have hSecond : subK D (Fin.append x y') V ≤
      subKRel D (Fin.append x y) z V +
        (δ + logSlack c₀
          (natK D (pairCode (tupleCode (Fin.append x y)) z)) + c₃) := by
    change natCondK D (subtupleCode (Fin.append x y') V) [] ≤
      natCondK D (subtupleCode (Fin.append x y) V) z +
        (δ + logSlack c₀
          (natK D (pairCode (tupleCode (Fin.append x y)) z)) + c₃)
    unfold c₃ at *
    omega
  constructor <;> omega

end Kolmogorov.Relativization
