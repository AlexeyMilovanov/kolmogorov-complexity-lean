/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.Relativization.Typization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.PlainSymmetry
import KolmogorovMathlib.CommonInformation.OverlapExtraction
import KolmogorovMathlib.CommonInformation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stochastic Examples

This module proves the stochasticity and complexity bounds used in the examples for
relativization. Its main results are `incompressible_isSetStochastic` and `remark2`,
formalizing the corresponding discussion and Remark 2 of Muchnik and Romashchenko (2010).
-/

namespace Kolmogorov.Relativization

/-- The canonical list of all strings of a given length has logarithmic complexity. -/
private theorem incompressible_isSetStochastic_fullLengthSetComplexity
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ n : ℕ,
      plainK D (finsetListCode (stringsOfLength n)) ≤ (logSlack c n : ENat) := by
  let f : BitString → BitString := fun w =>
    finsetListCode (stringsOfLength (decodeBits w))
  have hf : Computable f := by
    dsimp [f, finsetListCode, stringsOfLength]
    exact listCode_computable.comp
      ((canonicalFinsetList_toFinset_primrec.comp
        (CodedFiniteDistribution.allStrings_primrec.comp primrec_decodeBits)).to_comp)
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD f hf
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  refine ⟨cMap + cLen + 1, fun n => ?_⟩
  have hMap' : plainK D (finsetListCode (stringsOfLength n)) ≤
      plainK D (Nat.bits n) + (cMap : ENat) := by
    simpa [f, decodeBits_natBits] using hMap (Nat.bits n)
  have hLen' : plainK D (Nat.bits n) ≤
      ((Nat.bits n).length + cLen : ℕ∞) := by
    simpa [programLength] using hLen (Nat.bits n)
  have hArith : (Nat.bits n).length + cLen + cMap ≤
      logSlack (cMap + cLen + 1) n := by
    unfold logSlack
    nlinarith [Nat.zero_le ((cMap + cLen) * (Nat.bits n).length)]
  calc
    plainK D (finsetListCode (stringsOfLength n))
        ≤ plainK D (Nat.bits n) + (cMap : ENat) := hMap'
    _ ≤ ((Nat.bits n).length + cLen : ℕ∞) + (cMap : ENat) := by
      gcongr
    _ = ((Nat.bits n).length + cLen + cMap : ℕ) := by push_cast; rfl
    _ ≤ (logSlack (cMap + cLen + 1) n : ENat) := by exact_mod_cast hArith

/-- An incompressible string retains its length worth of conditional complexity when
given the canonical list of all strings of that length, up to logarithmic slack. -/
private theorem incompressible_isSetStochastic_conditionalComplexity
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x : BitString, x.length ≤ natK D x →
      x.length ≤ natCondK D x (finsetListCode (stringsOfLength x.length)) +
        logSlack c x.length := by
  obtain ⟨cSet, hSet⟩ :=
    incompressible_isSetStochastic_fullLengthSetComplexity D hD
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  have hSetComp : Computable (fun w : BitString =>
      finsetListCode (stringsOfLength w.length)) := by
      dsimp [finsetListCode, stringsOfLength]
      exact listCode_computable.comp
        ((canonicalFinsetList_toFinset_primrec.comp
          (CodedFiniteDistribution.allStrings_primrec.comp
            (Primrec.list_length.comp Primrec.id))).to_comp)
  have hPairComp : Computable (fun w : BitString =>
      pairCode (finsetListCode (stringsOfLength w.length)) w) := by
    have hPair : Computable₂ (fun a b : BitString => pairCode a b) := pairCode_computable
    exact hPair.comp hSetComp Computable.id
  obtain ⟨cPairMap, hPairMap⟩ := plainK_map_le D hD
    (fun w => pairCode (finsetListCode (stringsOfLength w.length)) w) hPairComp
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cProj, hProj⟩ := pairPlainK_right_le D hD
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain 1 (cLit + cPairMap + 1)
  let C := cSet + cFold + cProj
  refine ⟨C, fun x hx => ?_⟩
  let a := finsetListCode (stringsOfLength x.length)
  let kA := natK D a
  let kX := natK D x
  let kAX := natK D (pairCode a x)
  let kCond := natCondK D x a
  have hLit' (w : BitString) :
      plainK D w ≤ ((w.length + cLit : ℕ) : ENat) := by
    simpa [programLength] using hLit w
  have hPlainFinite (w : BitString) : plainK D w ≠ ⊤ := by
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hLit' w)
  have hCondFinite (w z : BitString) : condK D w z ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top (w.length + cLit + cCond))
    calc
      condK D w z ≤ plainK D w + (cCond : ENat) := hCond w z
      _ ≤ ((w.length + cLit : ℕ) : ENat) + (cCond : ENat) :=
        calc
          plainK D w + (cCond : ENat) = (cCond : ENat) + plainK D w := add_comm _ _
          _ ≤ (cCond : ENat) + ((w.length + cLit : ℕ) : ENat) :=
            add_le_add_right (hLit' w) _
          _ = ((w.length + cLit : ℕ) : ENat) + (cCond : ENat) := add_comm _ _
      _ = ((w.length + cLit + cCond : ℕ) : ENat) := by push_cast; rfl
  have hAVal : HasPlainComplexityValue D a kA := by
    change plainK D a = ((plainK D a).toNat : ENat)
    exact (ENat.natCast_toNat (hPlainFinite a)).symm
  have hXVal : HasPlainComplexityValue D x kX := by
    change plainK D x = ((plainK D x).toNat : ENat)
    exact (ENat.natCast_toNat (hPlainFinite x)).symm
  have hAXVal : HasPlainComplexityValue D (pairCode a x) kAX := by
    change plainK D (pairCode a x) = ((plainK D (pairCode a x)).toNat : ENat)
    exact (ENat.natCast_toNat (hPlainFinite (pairCode a x))).symm
  have hCondVal : HasPlainConditionalComplexityValue D x a kCond := by
    change condK D x a = ((condK D x a).toNat : ENat)
    exact (ENat.natCast_toNat (hCondFinite x a)).symm
  have hANat : kA ≤ logSlack cSet x.length := by
    change (plainK D a).toNat ≤ _
    exact ENat.toNat_le_of_le_natCast (hSet x.length)
  have hPairMap' : plainK D (pairCode a x) ≤ plainK D x + (cPairMap : ENat) := by
    simpa [a] using hPairMap x
  have hPairMapNat : kAX ≤ kX + cPairMap := by
    have h : (kAX : ENat) ≤ (kX : ENat) + (cPairMap : ENat) := by
      rw [← hAXVal, ← hXVal]
      simpa [Nat.cast_add] using hPairMap'
    exact_mod_cast h
  have hProj' : plainK D x ≤ plainK D (pairCode a x) + (cProj : ENat) := by
    simpa [pairPlainK] using hProj a x
  have hProjNat : kX ≤ kAX + cProj := by
    have h : (kX : ENat) ≤ (kAX : ENat) + (cProj : ENat) := by
      rw [← hXVal, ← hAXVal]
      simpa [Nat.cast_add] using hProj'
    exact_mod_cast h
  have hXLen : kX ≤ x.length + cLit := by
    have h : (kX : ENat) ≤ ((x.length + cLit : ℕ) : ENat) := by
      rw [← hXVal]
      exact hLit' x
    exact_mod_cast h
  have hAXArg : kAX + 1 ≤ x.length + (cLit + cPairMap + 1) := by
    omega
  have hLog : logSlack cChain (kAX + 1) ≤ logSlack cFold x.length :=
    logSlack_le_of_linear_bound hFold (by simpa using hAXArg)
  have hChainInst : kAX ≤ kA + kCond + logSlack cChain (kAX + 1) :=
    hChain a x kA kCond kAX hAVal hCondVal hAXVal
  have hMain : x.length ≤ kCond + logSlack cSet x.length +
      logSlack cFold x.length + cProj := by
    omega
  have hFoldSlack : logSlack cSet x.length + logSlack cFold x.length + cProj ≤
      logSlack C x.length := by
    calc
      logSlack cSet x.length + logSlack cFold x.length + cProj
          = logSlack (cSet + cFold) x.length + cProj := by
            rw [← logSlack_add_constants]
      _ ≤ logSlack ((cSet + cFold) + cProj) x.length :=
        logSlack_add_nat_le (cSet + cFold) cProj x.length
      _ = logSlack C x.length := by simp [C, Nat.add_assoc]
  calc
    x.length ≤ kCond + logSlack cSet x.length + logSlack cFold x.length + cProj := hMain
    _ ≤ kCond + logSlack C x.length := by omega

/-- An incompressible string is stochastic: if `K(x) ≥ |x|`, then `x` is
`(O(log |x|), O(log |x|))`-stochastic (the remark after Definition 1; the set `A` is the set of
all strings of length `|x|`). -/
theorem incompressible_isSetStochastic (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x : BitString, x.length ≤ natK D x →
      IsSetStochastic D x (logSlack c x.length) (logSlack c x.length) := by
  obtain ⟨cSet, hSet⟩ := incompressible_isSetStochastic_fullLengthSetComplexity D hD
  obtain ⟨cCond, hCond⟩ := incompressible_isSetStochastic_conditionalComplexity D hD
  refine ⟨max cSet cCond, fun x hx => ?_⟩
  let c := max cSet cCond
  have hSetNat : natK D (finsetListCode (stringsOfLength x.length)) ≤
      logSlack cSet x.length := by
    change (plainK D (finsetListCode (stringsOfLength x.length))).toNat ≤ _
    exact ENat.toNat_le_of_le_natCast (hSet x.length)
  have hSetNat' : natK D (finsetListCode (stringsOfLength x.length)) ≤
      logSlack c x.length :=
    hSetNat.trans (logSlack_mono_left (Nat.le_max_left _ _) _)
  have hCond' : x.length ≤
      natCondK D x (finsetListCode (stringsOfLength x.length)) + logSlack c x.length :=
    (hCond x hx).trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_max_right _ _) _) _)
  unfold IsSetStochastic
  refine ⟨stringsOfLength x.length, ?_, hSetNat', ?_⟩
  · exact (mem_stringsOfLength _ _).2 rfl
  · rw [card_stringsOfLength]
    exact Nat.pow_le_pow_right (by omega) hCond'

/-- Every string has a representative of length `natK D x` whose conditional complexities in both
directions and whose deficiency are bounded by logarithmic slack. -/
private theorem exists_equiv_stochastic_string_shortest_length_representative
    (D : Map) (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ x : BitString, ∃ p : BitString,
      p.length = natK D x ∧
      natCondK D x p ≤ logSlack C (natK D x) ∧
      natCondK D p x ≤ logSlack C (natK D x) ∧
      p.length ≤ natK D p + logSlack C (natK D x) := by
  obtain ⟨cRep, hRep⟩ := Kolmogorov.exists_incompressibleRepresentation D hD
  obtain ⟨cAbs, hAbs⟩ := logSlack_absorb_of_le_linear cRep 1 1
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  refine ⟨cAbs, fun x => ?_⟩
  have hxFin : plainK D x ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + cLen))
    simpa [programLength] using hLen x
  have hxVal : HasPlainComplexityValue D x (natK D x) := by
    change plainK D x = ((plainK D x).toNat : ENat)
    exact (ENat.natCast_toNat hxFin).symm
  obtain ⟨p, hlen, hequiv, hincomp⟩ := hRep x (natK D x) hxVal
  have hAbsorb : logSlack cRep (natK D x + 1) ≤ logSlack cAbs (natK D x) :=
    hAbs (natK D x) (natK D x + 1) (by omega)
  have hAbsorbE : (logSlack cRep (natK D x + 1) : ENat) ≤
      (logSlack cAbs (natK D x) : ENat) := by exact_mod_cast hAbsorb
  have hxSimple : condK D x p ≤ (logSlack cAbs (natK D x) : ENat) :=
    hequiv.1.trans hAbsorbE
  have hpSimple : condK D p x ≤ (logSlack cAbs (natK D x) : ENat) :=
    hequiv.2.trans hAbsorbE
  have hIncompE : (p.length : ENat) ≤
      plainK D p + (logSlack cAbs (natK D x) : ENat) := by
    exact hincomp.trans (by
      simpa [add_comm] using add_le_add_left hAbsorbE (plainK D p))
  have hpFin : plainK D p ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top (p.length + cLen))
    simpa [programLength] using hLen p
  have hpCast : (natK D p : ENat) = plainK D p := by
    dsimp [natK]
    exact ENat.natCast_toNat hpFin
  have hIncomp : p.length ≤ natK D p + logSlack cAbs (natK D x) := by
    have h : (p.length : ENat) ≤
        ((natK D p + logSlack cAbs (natK D x) : ℕ) : ENat) := by
      calc
        (p.length : ENat) ≤ plainK D p + (logSlack cAbs (natK D x) : ENat) := hIncompE
        _ = ((natK D p + logSlack cAbs (natK D x) : ℕ) : ENat) := by
          rw [← hpCast]
          push_cast
          rfl
    exact_mod_cast h
  exact ⟨p, hlen, ENat.toNat_le_of_le_natCast hxSimple,
    ENat.toNat_le_of_le_natCast hpSimple, hIncomp⟩

/-- If the conditional complexities between two strings are bounded by logarithmic slack, then
they are equivalent at the scale of their joint complexity. -/
private theorem exists_equiv_stochastic_string_equivalent_representative
    (D : Map) (hD : isOptimalConditional D) :
    ∀ c : ℕ, ∃ C : ℕ, ∀ (x p : BitString),
      natCondK D x p ≤ logSlack c (natK D x) →
      natCondK D p x ≤ logSlack c (natK D x) →
      EquivWithin D C x p := by
  intro c
  obtain ⟨cProj, hProj⟩ := Kolmogorov.pairPlainK_left_le D hD
  obtain ⟨cLen, hLen⟩ := Kolmogorov.plainK_le_length D hD
  obtain ⟨cAbs, hAbs⟩ := Kolmogorov.logSlack_absorb_of_le_linear c 1 cProj
  refine ⟨cAbs, fun x p hxp hpx => ?_⟩
  have hxFin : plainK D x ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + cLen))
    simpa [programLength] using hLen x
  have hpairFin : plainK D (pairCode x p) ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (ENat.natCast_ne_top ((pairCode x p).length + cLen))
    simpa [programLength] using hLen (pairCode x p)
  have hxcast : ((natK D x : ℕ) : ℕ∞) = plainK D x := by
    dsimp [natK]
    exact ENat.natCast_toNat hxFin
  have hpaircast : ((natK D (pairCode x p) : ℕ) : ℕ∞) =
      plainK D (pairCode x p) := by
    dsimp [natK]
    exact ENat.natCast_toNat hpairFin
  have hprojNat : natK D x ≤ natK D (pairCode x p) + cProj := by
    have hproj : plainK D x ≤ plainK D (pairCode x p) + cProj := by
      simpa [pairPlainK] using hProj x p
    have hcast : ((natK D x : ℕ) : ℕ∞) ≤
        ((natK D (pairCode x p) + cProj : ℕ) : ℕ∞) := by
      rw [hxcast]
      calc
        plainK D x ≤ plainK D (pairCode x p) + cProj := hproj
        _ = ((natK D (pairCode x p) + cProj : ℕ) : ℕ∞) := by
          rw [← hpaircast]
          push_cast
          rfl
    exact_mod_cast hcast
  have hxp' : natCondK D x p ≤ logSlack cAbs (natK D (pairCode x p)) :=
    hxp.trans (hAbs _ _ (by simpa using hprojNat))
  have hpx' : natCondK D p x ≤ logSlack cAbs (natK D (pairCode x p)) :=
    hpx.trans (hAbs _ _ (by simpa using hprojNat))
  exact ⟨hxp', hpx'⟩

/-- A string whose deficiency from its literal length is logarithmically bounded has a stochastic
model with logarithmic parameters. -/
private theorem exists_equiv_stochastic_string_near_incompressible_is_stochastic
    (D : Map) (hD : isOptimalConditional D) :
    ∀ d : ℕ, ∃ c : ℕ, ∀ x : BitString,
      x.length ≤ natK D x + logSlack d x.length →
      IsSetStochastic D x (logSlack c x.length) (logSlack c x.length) := by
  intro d
  obtain ⟨cSet, hSet⟩ :=
    incompressible_isSetStochastic_fullLengthSetComplexity D hD
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  have hSetComp : Computable (fun w : BitString =>
      finsetListCode (stringsOfLength w.length)) := by
    dsimp [finsetListCode, stringsOfLength]
    exact listCode_computable.comp
      ((canonicalFinsetList_toFinset_primrec.comp
        (CodedFiniteDistribution.allStrings_primrec.comp
          (Primrec.list_length.comp Primrec.id))).to_comp)
  have hPairComp : Computable (fun w : BitString =>
      pairCode (finsetListCode (stringsOfLength w.length)) w) := by
    have hPair : Computable₂ (fun a b : BitString => pairCode a b) := pairCode_computable
    exact hPair.comp hSetComp Computable.id
  obtain ⟨cPairMap, hPairMap⟩ := plainK_map_le D hD
    (fun w => pairCode (finsetListCode (stringsOfLength w.length)) w) hPairComp
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cProj, hProj⟩ := pairPlainK_right_le D hD
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain 1 (cLit + cPairMap + 1)
  let cCondTotal := cSet + cFold + d + cProj
  let C := max cSet cCondTotal
  refine ⟨C, fun x hx => ?_⟩
  let a := finsetListCode (stringsOfLength x.length)
  let kA := natK D a
  let kX := natK D x
  let kAX := natK D (pairCode a x)
  let kCond := natCondK D x a
  have hLit' (w : BitString) :
      plainK D w ≤ ((w.length + cLit : ℕ) : ENat) := by
    simpa [programLength] using hLit w
  have hPlainFinite (w : BitString) : plainK D w ≠ ⊤ := by
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hLit' w)
  have hCondFinite (w z : BitString) : condK D w z ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top (w.length + cLit + cCond))
    calc
      condK D w z ≤ plainK D w + (cCond : ENat) := hCond w z
      _ ≤ ((w.length + cLit : ℕ) : ENat) + (cCond : ENat) := by
        calc
          plainK D w + (cCond : ENat) = (cCond : ENat) + plainK D w := add_comm _ _
          _ ≤ (cCond : ENat) + ((w.length + cLit : ℕ) : ENat) :=
            add_le_add_right (hLit' w) _
          _ = ((w.length + cLit : ℕ) : ENat) + (cCond : ENat) := add_comm _ _
      _ = ((w.length + cLit + cCond : ℕ) : ENat) := by push_cast; rfl
  have hAVal : HasPlainComplexityValue D a kA := by
    change plainK D a = ((plainK D a).toNat : ENat)
    exact (ENat.natCast_toNat (hPlainFinite a)).symm
  have hXVal : HasPlainComplexityValue D x kX := by
    change plainK D x = ((plainK D x).toNat : ENat)
    exact (ENat.natCast_toNat (hPlainFinite x)).symm
  have hAXVal : HasPlainComplexityValue D (pairCode a x) kAX := by
    change plainK D (pairCode a x) = ((plainK D (pairCode a x)).toNat : ENat)
    exact (ENat.natCast_toNat (hPlainFinite (pairCode a x))).symm
  have hCondVal : HasPlainConditionalComplexityValue D x a kCond := by
    change condK D x a = ((condK D x a).toNat : ENat)
    exact (ENat.natCast_toNat (hCondFinite x a)).symm
  have hANat : kA ≤ logSlack cSet x.length := by
    change (plainK D a).toNat ≤ _
    exact ENat.toNat_le_of_le_natCast (hSet x.length)
  have hPairMap' : plainK D (pairCode a x) ≤ plainK D x + (cPairMap : ENat) := by
    simpa [a] using hPairMap x
  have hPairMapNat : kAX ≤ kX + cPairMap := by
    have h : (kAX : ENat) ≤ (kX : ENat) + (cPairMap : ENat) := by
      rw [← hAXVal, ← hXVal]
      simpa [Nat.cast_add] using hPairMap'
    exact_mod_cast h
  have hProj' : plainK D x ≤ plainK D (pairCode a x) + (cProj : ENat) := by
    simpa [pairPlainK] using hProj a x
  have hProjNat : kX ≤ kAX + cProj := by
    have h : (kX : ENat) ≤ (kAX : ENat) + (cProj : ENat) := by
      rw [← hXVal, ← hAXVal]
      simpa [Nat.cast_add] using hProj'
    exact_mod_cast h
  have hXLen : kX ≤ x.length + cLit := by
    have h : (kX : ENat) ≤ ((x.length + cLit : ℕ) : ENat) := by
      rw [← hXVal]
      exact hLit' x
    exact_mod_cast h
  have hAXArg : kAX + 1 ≤ x.length + (cLit + cPairMap + 1) := by omega
  have hLog : logSlack cChain (kAX + 1) ≤ logSlack cFold x.length :=
    logSlack_le_of_linear_bound hFold (by simpa using hAXArg)
  have hChainInst : kAX ≤ kA + kCond + logSlack cChain (kAX + 1) :=
    hChain a x kA kCond kAX hAVal hCondVal hAXVal
  have hMain : x.length ≤ kCond + logSlack cSet x.length +
      logSlack cFold x.length + logSlack d x.length + cProj := by
    omega
  have hFoldSlack : logSlack cSet x.length + logSlack cFold x.length +
      logSlack d x.length + cProj ≤ logSlack cCondTotal x.length := by
    calc
      logSlack cSet x.length + logSlack cFold x.length + logSlack d x.length + cProj
          = logSlack (cSet + cFold + d) x.length + cProj := by
            rw [← logSlack_add_constants, ← logSlack_add_constants]
      _ ≤ logSlack ((cSet + cFold + d) + cProj) x.length :=
        logSlack_add_nat_le (cSet + cFold + d) cProj x.length
      _ = logSlack cCondTotal x.length := by
        simp [cCondTotal, Nat.add_assoc]
  have hLowerCond : x.length ≤ kCond + logSlack cCondTotal x.length := by omega
  have hSetNat : natK D (finsetListCode (stringsOfLength x.length)) ≤
      logSlack cSet x.length := by
    change (plainK D (finsetListCode (stringsOfLength x.length))).toNat ≤ _
    exact ENat.toNat_le_of_le_natCast (hSet x.length)
  have hSetNat' : natK D (finsetListCode (stringsOfLength x.length)) ≤
      logSlack C x.length :=
    hSetNat.trans (logSlack_mono_left (Nat.le_max_left _ _) _)
  have hCond' : x.length ≤
      natCondK D x (finsetListCode (stringsOfLength x.length)) + logSlack C x.length :=
    hLowerCond.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_max_right _ _) _) _)
  unfold IsSetStochastic
  refine ⟨stringsOfLength x.length, ?_, hSetNat', ?_⟩
  · exact (mem_stringsOfLength _ _).2 rfl
  · rw [card_stringsOfLength]
    exact Nat.pow_le_pow_right (by omega) hCond'

/-- Every string is equivalent to a stochastic one: there is `C` such that every `x` has a
`C`-equivalent `(C log K(x), C log K(x))`-stochastic string `x'` (Section 2, before Theorem 6;
`x'` is a shortest description `p` of `x` with `K(p | x) = O(log K(x))`). -/
theorem exists_equiv_stochastic_string (D : Map) (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ x : BitString, ∃ x' : BitString,
      EquivWithin D C x x' ∧
        IsSetStochastic D x' (logSlack C (natK D x)) (logSlack C (natK D x)) := by
  obtain ⟨c₁, hc₁⟩ :=
    exists_equiv_stochastic_string_shortest_length_representative D hD
  obtain ⟨c₂, hc₂⟩ := exists_equiv_stochastic_string_equivalent_representative D hD c₁
  obtain ⟨c₃, hc₃⟩ :=
    exists_equiv_stochastic_string_near_incompressible_is_stochastic D hD c₁
  refine ⟨c₁ + c₂ + c₃, fun x => ?_⟩
  obtain ⟨p, hlen, hxp, hpx, hdef⟩ := hc₁ x
  have hequiv := hc₂ x p hxp hpx
  have hdef' : p.length ≤ natK D p + logSlack c₁ p.length := by
    simpa [hlen] using hdef
  have hstoch := hc₃ p hdef'
  have hlogPair : logSlack c₂ (natK D (pairCode x p)) ≤
      logSlack (c₁ + c₂ + c₃) (natK D (pairCode x p)) := by
    unfold logSlack
    nlinarith [Nat.zero_le ((c₁ + c₃) * (Nat.bits (natK D (pairCode x p))).length)]
  have hlogX : logSlack c₃ (natK D x) ≤
      logSlack (c₁ + c₂ + c₃) (natK D x) := by
    unfold logSlack
    nlinarith [Nat.zero_le ((c₁ + c₂) * (Nat.bits (natK D x)).length)]
  refine ⟨p, ?_, ?_⟩
  · rcases hequiv with ⟨hxp, hpx⟩
    exact ⟨hxp.trans hlogPair, hpx.trans hlogPair⟩
  · have hstoch' : IsSetStochastic D p
        (logSlack c₃ (natK D x)) (logSlack c₃ (natK D x)) := by
      simpa [hlen] using hstoch
    rcases hstoch' with ⟨A, hmem, hmodel, hdeficiency⟩
    refine ⟨A, hmem, hmodel.trans hlogX, ?_⟩
    calc
      A.card ≤ 2 ^ (natCondK D p (finsetListCode A) + logSlack c₃ (natK D x)) :=
        hdeficiency
      _ ≤ 2 ^ (natCondK D p (finsetListCode A) +
          logSlack (c₁ + c₂ + c₃) (natK D x)) := by
        exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left hlogX _)

/-- The first factor has
complexity at least its length up to logarithmic slack, by reconstructing the omitted suffix. -/
private theorem remark2_firstFactor
    (D : Map) (hD : isOptimalConditional D) (B : ℕ) :
    ∃ c : ℕ, ∀ n m p q : ℕ, m + p + q ≤ B * (n + 1) →
      ∀ s : BitString, s.length = m + p + q →
        ((m + p + q : ℕ) : ENat) ≤ plainK D s →
        (m + p : ℕ) ≤ natK D (s.take (m + p)) + logSlack c n := by
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  obtain ⟨cThree, hThree⟩ := plainK_threeBlock_le D hD
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cThree B (B + 1)
  let C := cFold + cLen
  refine ⟨C, fun n m p q hBudget s hslen hsK => ?_⟩
  let total := m + p + q
  let x := s.take (m + p)
  let tail := s.drop (m + p)
  have hPrefixLen : x.length = m + p := by
    dsimp [x]
    rw [List.length_take, hslen]
    omega
  have hTailLen : tail.length = q := by
    dsimp [tail]
    rw [List.length_drop, hslen]
    omega
  have hFactor : x ++ tail = s := by
    dsimp [x, tail]
    exact List.take_append_drop (m + p) s
  have hArg : total + 1 ≤ B * n + (B + 1) := by
    dsimp [total] at *
    rw [Nat.mul_succ] at hBudget
    omega
  have hSlackThree : logSlack cThree (total + 1) ≤ logSlack cFold n := by
    exact (logSlack_mono_right cThree hArg).trans (hFold n)
  have hSlack : logSlack cThree (total + 1) ≤ logSlack C n := by
    exact hSlackThree.trans (logSlack_mono_left (by dsimp [C]; omega) n)
  have hLit (w : BitString) :
      plainK D w ≤ ((w.length + cLen : ℕ) : ENat) := by
    simpa [programLength] using hLen w
  have hValue : plainK D x = (natK D x : ENat) := by
    change plainK D x = ((plainK D x).toNat : ENat)
    exact (ENat.natCast_toNat (by
      refine ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hLit x))).symm
  have hReconstruct :
      plainK D s ≤ plainK D x + ((q + logSlack cThree (total + 1) : ℕ) : ENat) := by
    simpa [List.nil_append, hFactor, hslen, hTailLen, total] using hThree [] x tail
  have hLowerEnat :
      ((total : ℕ) : ENat) ≤ ((natK D x + q + logSlack C n : ℕ) : ENat) := by
    calc
      (total : ENat) ≤ plainK D s := hsK
      _ ≤ plainK D x + ((q + logSlack cThree (total + 1) : ℕ) : ENat) := hReconstruct
      _ = ((natK D x + q + logSlack cThree (total + 1) : ℕ) : ENat) := by
        rw [hValue]
        push_cast
        ring
      _ ≤ ((natK D x + q + logSlack C n : ℕ) : ENat) := by
        exact_mod_cast (by omega :
          natK D x + q + logSlack cThree (total + 1) ≤ natK D x + q + logSlack C n)
  have hNat : m + p + q ≤ natK D x + q + logSlack C n := by
    dsimp [total] at hLowerEnat
    exact_mod_cast hLowerEnat
  have hNat' : (m + p) + q ≤ (natK D x + logSlack C n) + q := by omega
  exact Nat.add_le_add_iff_right.mp (by simpa [Nat.add_assoc] using hNat')

/-- The second factor has
complexity at least its length up to logarithmic slack, by reconstructing the omitted middle block.
-/
private theorem remark2_secondFactor
    (D : Map) (hD : isOptimalConditional D) (B : ℕ) :
    ∃ c : ℕ, ∀ n m p q : ℕ, m + p + q ≤ B * (n + 1) →
      ∀ s : BitString, s.length = m + p + q →
        ((m + p + q : ℕ) : ENat) ≤ plainK D s →
        (m + q : ℕ) ≤ natK D (s.take m ++ s.drop (m + p)) + logSlack c n := by
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  obtain ⟨cThree, hThree⟩ := plainK_threeBlock_le D hD
  let f : BitString → BitString := fun w =>
    let source := decodeSecond (decodeSecond w)
    let commonLen := decodeBits (decodeFirst w)
    let blockLen := decodeBits (decodeFirst (decodeSecond w))
    let visible := source.take blockLen
    visible.take commonLen ++ source.drop blockLen ++ visible.drop commonLen
  have hf : Computable f := by
    let commonLen : BitString → Nat := fun w => decodeBits (decodeFirst w)
    let blockLen : BitString → Nat := fun w => decodeBits (decodeFirst (decodeSecond w))
    let source : BitString → BitString := fun w => decodeSecond (decodeSecond w)
    have hCommon : Computable commonLen := decodeBits_computable.comp decodeFirst_computable
    have hBlock : Computable blockLen :=
      decodeBits_computable.comp (decodeFirst_computable.comp decodeSecond_computable)
    have hSource : Computable source :=
      decodeSecond_computable.comp decodeSecond_computable
    have hVisible : Computable (fun w => (source w).take (blockLen w)) :=
      Primrec.list_take.to_comp.comp hBlock hSource
    have hPrefix : Computable (fun w => ((source w).take (blockLen w)).take (commonLen w)) :=
      Primrec.list_take.to_comp.comp hCommon hVisible
    have hPrivate : Computable (fun w => (source w).drop (blockLen w)) :=
      Primrec.list_drop.to_comp.comp hBlock hSource
    have hSuffix : Computable (fun w =>
        ((source w).take (blockLen w)).drop (commonLen w)) :=
      Primrec.list_drop.to_comp.comp hCommon hVisible
    have hFirstAppend : Computable (fun w =>
        ((source w).take (blockLen w)).take (commonLen w) ++ (source w).drop (blockLen w)) :=
      Computable.list_append.comp hPrefix hPrivate
    have hOutput : Computable (fun w =>
        (((source w).take (blockLen w)).take (commonLen w) ++
          (source w).drop (blockLen w)) ++ ((source w).take (blockLen w)).drop (commonLen w)) :=
      Computable.list_append.comp hFirstAppend hSuffix
    change Computable (fun w =>
      ((decodeSecond (decodeSecond w)).take
        (decodeBits (decodeFirst (decodeSecond w)))).take (decodeBits (decodeFirst w)) ++
        (decodeSecond (decodeSecond w)).drop
          (decodeBits (decodeFirst (decodeSecond w))) ++
        ((decodeSecond (decodeSecond w)).take
          (decodeBits (decodeFirst (decodeSecond w)))).drop (decodeBits (decodeFirst w)))
    exact hOutput
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD f hf
  obtain ⟨cMeta, hMetaFold⟩ := logSlack_linear_bound 1 B (B + 1)
  let a := B + 4 * cMeta + 4
  obtain ⟨cCode, hCodeFold⟩ := logSlack_linear_bound cThree a a
  let C := 4 * cMeta + 2 + cCode + cMap
  refine ⟨C, fun n m p q hBudget s hslen hsK => ?_⟩
  let x₂ := s.take m ++ s.drop (m + p)
  let middleBits := (s.drop m).take p
  let header := pairCode (Nat.bits m) (pairCode (Nat.bits x₂.length) ([] : BitString))
  let code := pairCode (Nat.bits m)
    (pairCode (Nat.bits x₂.length) (x₂ ++ middleBits))
  let L := (Nat.bits (B * (n + 1))).length
  have hmBound : m ≤ B * (n + 1) := by omega
  have hxLenBound : x₂.length ≤ B * (n + 1) := by
    rw [List.length_append, List.length_take, List.length_drop, hslen]
    omega
  have hBitsM : (Nat.bits m).length ≤ L := length_natBits_mono hmBound
  have hBitsX : (Nat.bits x₂.length).length ≤ L := length_natBits_mono hxLenBound
  have hLSlack : L ≤ logSlack cMeta n := by
    have hL : L ≤ logSlack 1 (B * (n + 1) + 1) := by
      dsimp [L, logSlack]
      have hmono : (Nat.bits (B * (n + 1))).length ≤
          (Nat.bits (B * (n + 1) + 1)).length :=
        length_natBits_mono (Nat.le_succ _)
      omega
    have harg : B * (n + 1) + 1 = B * n + (B + 1) := by
      rw [Nat.mul_succ]
      omega
    rw [harg] at hL
    exact hL.trans (hMetaFold n)
  have hMiddleLen : middleBits.length = p := by
    dsimp [middleBits]
    rw [List.length_take, List.length_drop, hslen]
    omega
  have hBodyLen : (x₂ ++ middleBits).length = m + p + q := by
    rw [List.length_append, hMiddleLen, List.length_append,
      List.length_take, List.length_drop, hslen]
    omega
  have hHeaderLen : header.length ≤ 4 * L + 2 := by
    dsimp [header]
    rw [length_pairCode, length_pairCode]
    simp only [List.length_nil]
    omega
  have hCodeBudget : code.length + 1 ≤ a * n + a := by
    dsimp [code, a]
    rw [length_pairCode, length_pairCode, hBodyLen]
    have hL' : L ≤ cMeta * (Nat.bits n).length + cMeta := by
      simpa [logSlack] using hLSlack
    have hBitsN : (Nat.bits n).length ≤ n := length_natBits_le n
    nlinarith [hBudget, hL', hBitsN]
  have hx2Value : plainK D x₂ = (natK D x₂ : ENat) := by
    change plainK D x₂ = ((plainK D x₂).toNat : ENat)
    have hLit : plainK D x₂ ≤ ((x₂.length + cLen : ℕ) : ENat) := by
      simpa [programLength] using hLen x₂
    apply (ENat.natCast_toNat ?_).symm
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top _)
    exact hLit
  have hCodeEq : header ++ x₂ ++ middleBits = code := by
    dsimp [header, code, pairCode]
    simp only [List.append_assoc, List.nil_append]
  have hCodeBound :
      plainK D code ≤ plainK D x₂ +
        ((header.length + middleBits.length + logSlack cThree (code.length + 1) : ℕ) : ENat) := by
    have h := hThree header x₂ middleBits
    simpa [hCodeEq, List.append_assoc] using h
  have hCodeSlack : logSlack cThree (code.length + 1) ≤ logSlack cCode n := by
    exact (logSlack_mono_right cThree hCodeBudget).trans (hCodeFold n)
  have hHeaderSlack : header.length ≤ logSlack (4 * cMeta + 2) n := by
    have hHeader : header.length ≤ 4 * logSlack cMeta n + 2 := by omega
    have hSum : 4 * logSlack cMeta n + 2 ≤ logSlack (4 * cMeta + 2) n := by
      unfold logSlack
      nlinarith [Nat.zero_le ((Nat.bits n).length)]
    exact hHeader.trans hSum
  have hConstSlack : cMap ≤ logSlack cMap n := by unfold logSlack; omega
  have hTotalSlack :
      header.length + logSlack cThree (code.length + 1) + cMap ≤ logSlack C n := by
    calc
      _ ≤ logSlack (4 * cMeta + 2) n + logSlack cCode n + logSlack cMap n := by
        exact Nat.add_le_add (Nat.add_le_add hHeaderSlack hCodeSlack) hConstSlack
      _ = logSlack C n := by
        dsimp [C]
        rw [← logSlack_add_constants (4 * cMeta + 2) cCode n,
          ← logSlack_add_constants (4 * cMeta + 2 + cCode) cMap n]
  have hSpec : f code = s := by
    have hVisibleLen : x₂.length = m + q := by
      dsimp [x₂]
      rw [List.length_append, List.length_take, List.length_drop, hslen]
      omega
    have hPrefixLen : (s.take m).length = m := by
      rw [List.length_take, hslen]
      omega
    have hX₂Take : x₂.take m = s.take m := by
      dsimp [x₂]
      rw [List.take_append_of_le_length hPrefixLen.ge]
      exact List.take_of_length_le hPrefixLen.le
    have hX₂Drop : x₂.drop m = s.drop (m + p) := by
      dsimp [x₂]
      rw [List.drop_append_of_le_length hPrefixLen.ge,
        List.drop_eq_nil_of_le hPrefixLen.le, List.nil_append]
    have hBodyTake : (x₂ ++ middleBits).take x₂.length = x₂ :=
      by rw [List.take_append_of_le_length (le_rfl : x₂.length ≤ x₂.length),
        List.take_of_length_le (le_rfl : x₂.length ≤ x₂.length)]
    have hBodyDrop : (x₂ ++ middleBits).drop x₂.length = middleBits := by
      rw [List.drop_append_of_le_length (le_rfl : x₂.length ≤ x₂.length),
        List.drop_eq_nil_of_le (le_rfl : x₂.length ≤ x₂.length), List.nil_append]
    dsimp [f, code]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      hBodyTake, hBodyDrop]
    rw [hX₂Take, hX₂Drop]
    have hmid : s.take m ++ (s.drop m).take p = s.take (m + p) := by
      symm
      rw [List.take_add]
    rw [hmid, List.take_append_drop]
  have hMap' : plainK D s ≤ plainK D code + (cMap : ENat) := by
    rw [← hSpec]
    exact hMap code
  have hLower :
      ((m + p + q : ℕ) : ENat) ≤
        ((natK D x₂ + p + logSlack C n : ℕ) : ENat) := by
    calc
      (m + p + q : ENat) ≤ plainK D s := hsK
      _ ≤ plainK D code + (cMap : ENat) := hMap'
      _ ≤ plainK D x₂ +
          ((header.length + p + logSlack cThree (code.length + 1) + cMap : ℕ) : ENat) := by
        calc
          _ ≤ (plainK D x₂ +
              ((header.length + middleBits.length + logSlack cThree (code.length + 1) : ℕ) : ENat))
                  +
                (cMap : ENat) := by gcongr
          _ = plainK D x₂ +
              ((header.length + p + logSlack cThree (code.length + 1) + cMap : ℕ) : ENat) := by
            rw [hMiddleLen]
            push_cast
            ring
      _ = ((natK D x₂ + p +
            (header.length + logSlack cThree (code.length + 1) + cMap) : ℕ) : ENat) := by
        rw [hx2Value]
        push_cast
        ring
      _ ≤ ((natK D x₂ + p + logSlack C n : ℕ) : ENat) := by
        exact_mod_cast (Nat.add_le_add_left hTotalSlack (natK D x₂ + p))
  have hNat : m + p + q ≤ natK D x₂ + p + logSlack C n := by
    exact_mod_cast hLower
  have hNat' : (m + q) + p ≤ (natK D x₂ + logSlack C n) + p := by omega
  exact Nat.add_le_add_iff_right.mp (by simpa [Nat.add_assoc] using hNat')

/-- The joint factor code
has complexity at least the total length up to logarithmic slack, by reconstructing the source. -/
private theorem remark2_jointFactor
    (D : Map) (hD : isOptimalConditional D) (B : ℕ) :
    ∃ c : ℕ, ∀ n m p q : ℕ, m + p + q ≤ B * (n + 1) →
      ∀ s : BitString, s.length = m + p + q →
        ((m + p + q : ℕ) : ENat) ≤ plainK D s →
        (m + p + q : ℕ) ≤ natK D
          (pairCode (s.take (m + p)) (s.take m ++ s.drop (m + p))) + logSlack c n := by
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  obtain ⟨cThree, hThree⟩ := plainK_threeBlock_le D hD
  let f : BitString → BitString := fun w =>
    let components := decodeSecond w
    let commonLen := decodeBits (decodeFirst w)
    decodeFirst components ++ (decodeSecond components).drop commonLen
  have hf : Computable f := by
    let commonLen : BitString → Nat := fun w =>
      decodeBits (decodeFirst w)
    let first : BitString → BitString := decodeFirst ∘ decodeSecond
    let second : BitString → BitString := decodeSecond ∘ decodeSecond
    have hCommon : Computable commonLen :=
      decodeBits_computable.comp decodeFirst_computable
    have hFirst : Computable first := decodeFirst_computable.comp decodeSecond_computable
    have hSecond : Computable second := decodeSecond_computable.comp decodeSecond_computable
    have hDrop : Computable (fun w => (second w).drop (commonLen w)) :=
      Primrec.list_drop.to_comp.comp hCommon hSecond
    have hOutput : Computable (fun w => first w ++ (second w).drop (commonLen w)) :=
      Computable.list_append.comp hFirst hDrop
    change Computable (fun w =>
      decodeFirst (decodeSecond w) ++
        (decodeSecond (decodeSecond w)).drop
          (decodeBits (decodeFirst w)))
    exact hOutput
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD f hf
  obtain ⟨cMeta, hMetaFold⟩ := logSlack_linear_bound 1 B (B + 1)
  let a := 3 * B + 2 * cMeta + 3
  obtain ⟨cCode, hCodeFold⟩ := logSlack_linear_bound cThree a a
  let C := 2 * cMeta + 1 + cCode + cMap
  refine ⟨C, fun n m p q hBudget s hslen hsK => ?_⟩
  let x₁ := s.take (m + p)
  let x₂ := s.take m ++ s.drop (m + p)
  let header := pairCode (Nat.bits m) ([] : BitString)
  let components := pairCode x₁ x₂
  let code := pairCode (Nat.bits m) components
  let L := (Nat.bits (B * (n + 1))).length
  have hmBound : m ≤ B * (n + 1) := by omega
  have hBitsM : (Nat.bits m).length ≤ L := length_natBits_mono hmBound
  have hLSlack : L ≤ logSlack cMeta n := by
    have hL : L ≤ logSlack 1 (B * (n + 1) + 1) := by
      dsimp [L, logSlack]
      have hmono : (Nat.bits (B * (n + 1))).length ≤
          (Nat.bits (B * (n + 1) + 1)).length :=
        length_natBits_mono (Nat.le_succ _)
      omega
    have harg : B * (n + 1) + 1 = B * n + (B + 1) := by
      rw [Nat.mul_succ]
      omega
    rw [harg] at hL
    exact hL.trans (hMetaFold n)
  have hLen₁ : x₁.length = m + p := by
    dsimp [x₁]
    rw [List.length_take, hslen]
    omega
  have hLen₂ : x₂.length = m + q := by
    dsimp [x₂]
    rw [List.length_append, List.length_take, List.length_drop, hslen]
    omega
  have hHeaderLen : header.length ≤ 2 * L + 1 := by
    dsimp [header]
    rw [length_pairCode]
    simp only [List.length_nil]
    omega
  have hCodeBudget : code.length + 1 ≤ a * n + a := by
    dsimp [code, components, a]
    rw [length_pairCode, length_pairCode, hLen₁, hLen₂]
    have hL' : L ≤ cMeta * (Nat.bits n).length + cMeta := by
      simpa [logSlack] using hLSlack
    have hBits : (Nat.bits m).length ≤ cMeta * (Nat.bits n).length + cMeta :=
      hBitsM.trans hL'
    have hBitsN : (Nat.bits n).length ≤ n := length_natBits_le n
    nlinarith [hBudget, hBits, hBitsN]
  have hPairValue : plainK D components = (natK D components : ENat) := by
    change plainK D components = ((plainK D components).toNat : ENat)
    have hBound : plainK D components ≤ ((components.length + cLen : ℕ) : ENat) := by
      calc
        plainK D components ≤ ((programLength components : ℕ) : ENat) + (cLen : ENat) :=
          hLen components
        _ = ((components.length + cLen : ℕ) : ENat) := by
          simp [programLength, Nat.cast_add]
    apply (ENat.natCast_toNat ?_).symm
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top _)
    exact hBound
  have hCodeBound :
      plainK D code ≤ plainK D components +
        ((header.length + logSlack cThree (code.length + 1) : ℕ) : ENat) := by
    have hEq : header ++ components = code := by
      dsimp [header, components, code, pairCode]
      simp only [List.nil_append, List.append_assoc]
    have h := hThree header components []
    simpa [List.nil_append, hEq] using h
  have hCodeSlack : logSlack cThree (code.length + 1) ≤ logSlack cCode n := by
    exact (logSlack_mono_right cThree hCodeBudget).trans (hCodeFold n)
  have hHeaderSlack : header.length ≤ logSlack (2 * cMeta + 1) n := by
    have hConst : 1 ≤ logSlack 1 n := by unfold logSlack; omega
    have hFold : 2 * L + 1 ≤ 2 * logSlack cMeta n + 1 := by omega
    have hSum : 2 * logSlack cMeta n + 1 ≤
        logSlack (2 * cMeta + 1) n := by
      unfold logSlack
      nlinarith [Nat.zero_le ((Nat.bits n).length)]
    exact hHeaderLen.trans (hFold.trans hSum)
  have hSpec : f code = s := by
    dsimp [f, code, components, x₁, x₂]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
    have hdrop : (s.take m).drop m = [] := by
      apply List.drop_eq_nil_of_le
      rw [List.length_take]
      omega
    rw [List.drop_append_of_le_length (by rw [List.length_take]; omega), hdrop,
      List.nil_append]
    exact List.take_append_drop (m + p) s
  have hMap' : plainK D s ≤ plainK D code + (cMap : ENat) := by
    rw [← hSpec]
    exact hMap code
  have hConstSlack : cMap ≤ logSlack cMap n := by unfold logSlack; omega
  have hTotalSlack :
      header.length + logSlack cThree (code.length + 1) + cMap ≤ logSlack C n := by
    calc
      _ ≤ logSlack (2 * cMeta + 1) n + logSlack cCode n + logSlack cMap n := by
        exact Nat.add_le_add (Nat.add_le_add hHeaderSlack hCodeSlack) hConstSlack
      _ = logSlack C n := by
        dsimp [C]
        rw [← logSlack_add_constants (2 * cMeta + 1) cCode n,
          ← logSlack_add_constants (2 * cMeta + 1 + cCode) cMap n]
  have hLower :
      ((m + p + q : ℕ) : ENat) ≤
        ((natK D components + logSlack C n : ℕ) : ENat) := by
    calc
      (m + p + q : ENat) ≤ plainK D s := hsK
      _ ≤ plainK D code + (cMap : ENat) := hMap'
      _ ≤ plainK D components +
          ((header.length + logSlack cThree (code.length + 1) + cMap : ℕ) : ENat) := by
        calc
          _ ≤ (plainK D components +
              ((header.length + logSlack cThree (code.length + 1) : ℕ) : ENat)) +
                (cMap : ENat) := by gcongr
          _ = plainK D components +
              ((header.length + logSlack cThree (code.length + 1) + cMap : ℕ) : ENat) := by
            push_cast
            ring
      _ ≤ ((natK D components + logSlack C n : ℕ) : ENat) := by
        rw [hPairValue]
        exact_mod_cast (Nat.add_le_add_left hTotalSlack (natK D components))
  exact_mod_cast hLower

/-- Literal coding of
the two factors with self-delimiting pair metadata gives the joint upper complexity bound. -/
private theorem remark2_jointUpper
    (D : Map) (hD : isOptimalConditional D) (B : ℕ) :
    ∃ c : ℕ, ∀ n m p q : ℕ, m + p + q ≤ B * (n + 1) →
      ∀ s : BitString, s.length = m + p + q →
        natK D (pairCode (s.take (m + p)) (s.take m ++ s.drop (m + p))) ≤
          m + p + q + logSlack c n := by
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  let f : BitString → BitString := fun w =>
      let metadata := decodeFirst w
      let source := decodeSecond w
      let commonLen := decodeBits (decodeFirst metadata)
      let privateLen := decodeBits (decodeSecond metadata)
      pairCode (source.take (commonLen + privateLen))
        (source.take commonLen ++ source.drop (commonLen + privateLen))
  have hf : Computable f := by
    let common : BitString → Nat := fun w => decodeBits (decodeFirst (decodeFirst w))
    let privateLen : BitString → Nat := fun w => decodeBits (decodeSecond (decodeFirst w))
    let source : BitString → BitString := decodeSecond
    have hCommon : Computable common :=
      decodeBits_computable.comp (decodeFirst_computable.comp decodeFirst_computable)
    have hPrivate : Computable privateLen :=
      decodeBits_computable.comp (decodeSecond_computable.comp decodeFirst_computable)
    have hSource : Computable source := decodeSecond_computable
    have hSum : Computable (fun w => common w + privateLen w) :=
      Primrec.nat_add.to_comp.comp hCommon hPrivate
    have hPrefix : Computable (fun w => (source w).take (common w + privateLen w)) :=
      Primrec.list_take.to_comp.comp hSum hSource
    have hCommonPrefix : Computable (fun w => (source w).take (common w)) :=
      Primrec.list_take.to_comp.comp hCommon hSource
    have hSuffix : Computable (fun w => (source w).drop (common w + privateLen w)) :=
      Primrec.list_drop.to_comp.comp hSum hSource
    have hSecond : Computable (fun w =>
        (source w).take (common w) ++ (source w).drop (common w + privateLen w)) :=
      Computable.list_append.comp hCommonPrefix hSuffix
    change Computable (fun w => pairCode
      ((decodeSecond w).take
        (decodeBits (decodeFirst (decodeFirst w)) +
          decodeBits (decodeSecond (decodeFirst w))))
      ((decodeSecond w).take (decodeBits (decodeFirst (decodeFirst w))) ++
        (decodeSecond w).drop
          (decodeBits (decodeFirst (decodeFirst w)) +
            decodeBits (decodeSecond (decodeFirst w)))))
    exact Computable₂.comp pairCode_computable hPrefix hSecond
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD f hf
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound 1 B (B + 1)
  refine ⟨6 * cFold + cLen + cMap + 3, fun n m p q hBudget s hslen => ?_⟩
  let metadata := pairCode (Nat.bits m) (Nat.bits p)
  let code := pairCode metadata s
  let L := (Nat.bits (B * (n + 1))).length
  have hmBound : m ≤ B * (n + 1) := by omega
  have hpBound : p ≤ B * (n + 1) := by omega
  have hBitsM : (Nat.bits m).length ≤ L := length_natBits_mono hmBound
  have hBitsP : (Nat.bits p).length ≤ L := length_natBits_mono hpBound
  have hLSlack : L ≤ logSlack cFold n := by
    have hL : L ≤ logSlack 1 (B * (n + 1) + 1) := by
      dsimp [L, logSlack]
      have hmono : (Nat.bits (B * (n + 1))).length ≤
          (Nat.bits (B * (n + 1) + 1)).length :=
        length_natBits_mono (Nat.le_succ _)
      omega
    have harg : B * (n + 1) + 1 = B * n + (B + 1) := by
      rw [Nat.mul_succ]
      omega
    rw [harg] at hL
    exact hL.trans (hFold n)
  have hCodeLen : code.length ≤ (m + p + q) + 6 * L + 3 := by
    dsimp [code, metadata]
    rw [length_pairCode, length_pairCode, hslen]
    omega
  have hCodeK : plainK D code ≤ ((code.length + cLen : ℕ) : ENat) := by
    simpa [programLength] using hLen code
  have hSpec : f code =
        pairCode (s.take (m + p)) (s.take m ++ s.drop (m + p)) := by
    dsimp [f, code, metadata]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
  have hMap' :
      plainK D (pairCode (s.take (m + p)) (s.take m ++ s.drop (m + p))) ≤
        plainK D code + (cMap : ENat) := by
    rw [← hSpec]
    exact hMap code
  have hAbsorb :
      6 * L + 3 + cLen + cMap ≤
        logSlack (6 * cFold + cLen + cMap + 3) n := by
    have hL' : L ≤ cFold * (Nat.bits n).length + cFold := by
      simpa [logSlack] using hLSlack
    unfold logSlack
    nlinarith [Nat.zero_le ((cLen + cMap + 3) * (Nat.bits n).length)]
  have hCodeCost :
      code.length + cLen + cMap ≤
        m + p + q + logSlack (6 * cFold + cLen + cMap + 3) n := by
    calc
      code.length + cLen + cMap ≤ (m + p + q) + (6 * L + 3) + cLen + cMap :=
        by omega
      _ ≤ m + p + q + logSlack (6 * cFold + cLen + cMap + 3) n := by omega
  have hFinal :
      plainK D (pairCode (s.take (m + p)) (s.take m ++ s.drop (m + p))) ≤
        ((m + p + q + logSlack (6 * cFold + cLen + cMap + 3) n : ℕ) : ENat) := by
    calc
      _ ≤ plainK D code + (cMap : ENat) := hMap'
      _ ≤ ((code.length + cLen : ℕ) : ENat) + (cMap : ENat) := by gcongr
      _ = ((code.length + cLen + cMap : ℕ) : ENat) := by push_cast; rfl
      _ ≤ ((m + p + q + logSlack (6 * cFold + cLen + cMap + 3) n : ℕ) : ENat) := by
        exact_mod_cast hCodeCost
  exact ENat.toNat_le_of_le_natCast hFinal

/-- Splitting an incompressible word of length
`m + p + q` into a common block of length `m` and private blocks of lengths `p` and `q` gives
strings whose individual and joint complexities are the corresponding block sums, up to
logarithmic coding overhead. -/
private theorem remark2_split_incompressible
    (D : Map) (hD : isOptimalConditional D) (B : ℕ) :
    ∃ c : ℕ, ∀ n m p q : ℕ, m + p + q ≤ B * (n + 1) →
      ∀ s : BitString, s.length = m + p + q →
        ((m + p + q : ℕ) : ENat) ≤ plainK D s →
      ∃ x₁ x₂ : BitString,
        x₁ = s.take (m + p) ∧ x₂ = s.take m ++ s.drop (m + p) ∧
        x₁.length = m + p ∧ x₂.length = m + q ∧
        |(natK D x₁ : ℝ) - (m + p : ℝ)| ≤ logSlack c n ∧
        |(natK D x₂ : ℝ) - (m + q : ℝ)| ≤ logSlack c n ∧
        |(natK D (pairCode x₁ x₂) : ℝ) - (m + p + q : ℝ)| ≤ logSlack c n := by
  obtain ⟨c₁, h₁⟩ := remark2_firstFactor D hD B
  obtain ⟨c₂, h₂⟩ := remark2_secondFactor D hD B
  obtain ⟨c₃, h₃⟩ := remark2_jointFactor D hD B
  obtain ⟨c₄, h₄⟩ := remark2_jointUpper D hD B
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  let c := max cLen (max c₁ (max c₂ (max c₃ c₄)))
  refine ⟨c, fun n m p q hBudget s hslen hsK => ?_⟩
  have hcLen : cLen ≤ c := by
    dsimp [c]
    exact Nat.le_max_left _ _
  have hc₁ : c₁ ≤ c := by
    dsimp [c]
    exact (Nat.le_max_left c₁ (max c₂ (max c₃ c₄))).trans (Nat.le_max_right _ _)
  have hc₂ : c₂ ≤ c := by
    dsimp [c]
    exact ((Nat.le_max_left c₂ (max c₃ c₄)).trans
      (Nat.le_max_right c₁ (max c₂ (max c₃ c₄)))).trans (Nat.le_max_right _ _)
  have hc₃ : c₃ ≤ c := by
    dsimp [c]
    exact (((Nat.le_max_left c₃ c₄).trans (Nat.le_max_right c₂ (max c₃ c₄))).trans
      (Nat.le_max_right c₁ (max c₂ (max c₃ c₄)))).trans (Nat.le_max_right _ _)
  have hc₄ : c₄ ≤ c := by
    dsimp [c]
    exact (((Nat.le_max_right c₃ c₄).trans (Nat.le_max_right c₂ (max c₃ c₄))).trans
      (Nat.le_max_right c₁ (max c₂ (max c₃ c₄)))).trans (Nat.le_max_right _ _)
  let x₁ := s.take (m + p)
  let x₂ := s.take m ++ s.drop (m + p)
  have hLen₁ : x₁.length = m + p := by
    dsimp [x₁]
    rw [List.length_take, hslen]
    omega
  have hLen₂ : x₂.length = m + q := by
    dsimp [x₂]
    rw [List.length_append, List.length_take, List.length_drop, hslen]
    omega
  have hLit (w : BitString) :
      plainK D w ≤ ((w.length + cLen : ℕ) : ENat) := by
    simpa [programLength] using hLen w
  have hUpper₁ : natK D x₁ ≤ m + p + logSlack c n := by
    have h : plainK D x₁ ≤ ((m + p + logSlack c n : ℕ) : ENat) := by
      calc
        plainK D x₁ ≤ ((x₁.length + cLen : ℕ) : ENat) := hLit x₁
        _ ≤ ((m + p + logSlack c n : ℕ) : ENat) := by
          have hcLenSlack : cLen ≤ logSlack c n := by
            unfold logSlack
            have : cLen ≤ c := hcLen
            omega
          rw [hLen₁]
          exact_mod_cast Nat.add_le_add_left hcLenSlack (m + p)
    exact ENat.toNat_le_of_le_natCast h
  have hUpper₂ : natK D x₂ ≤ m + q + logSlack c n := by
    have h : plainK D x₂ ≤ ((m + q + logSlack c n : ℕ) : ENat) := by
      calc
        plainK D x₂ ≤ ((x₂.length + cLen : ℕ) : ENat) := hLit x₂
        _ ≤ ((m + q + logSlack c n : ℕ) : ENat) := by
          have hcLenSlack : cLen ≤ logSlack c n := by
            unfold logSlack
            have : cLen ≤ c := hcLen
            omega
          rw [hLen₂]
          exact_mod_cast Nat.add_le_add_left hcLenSlack (m + q)
    exact ENat.toNat_le_of_le_natCast h
  have hUpper₃ : natK D (pairCode x₁ x₂) ≤ m + p + q + logSlack c n := by
    have h := h₄ n m p q hBudget s hslen
    dsimp [x₁, x₂]
    exact h.trans (Nat.add_le_add_left (logSlack_mono_left hc₄ n) _)
  have hLower₁ : m + p ≤ natK D x₁ + logSlack c n := by
    exact (h₁ n m p q hBudget s hslen hsK).trans
      (Nat.add_le_add_left (logSlack_mono_left hc₁ n) (natK D x₁))
  have hLower₂ : m + q ≤ natK D x₂ + logSlack c n := by
    exact (h₂ n m p q hBudget s hslen hsK).trans
      (Nat.add_le_add_left (logSlack_mono_left hc₂ n) (natK D x₂))
  have hLower₃ : m + p + q ≤ natK D (pairCode x₁ x₂) + logSlack c n := by
    exact (h₃ n m p q hBudget s hslen hsK).trans
      (Nat.add_le_add_left (logSlack_mono_left hc₃ n) (natK D (pairCode x₁ x₂)))
  have hRealAbs (k v : ℕ) (hlo : v ≤ k + logSlack c n)
      (hhi : k ≤ v + logSlack c n) :
      |(k : ℝ) - (v : ℝ)| ≤ logSlack c n := by
    rw [abs_le]
    constructor
    · have hvk : (v : ℝ) ≤ (k : ℝ) + logSlack c n := by exact_mod_cast hlo
      linarith
    · have hkv : (k : ℝ) ≤ (v : ℝ) + logSlack c n := by exact_mod_cast hhi
      linarith
  refine ⟨x₁, x₂, rfl, rfl, hLen₁, hLen₂, ?_, ?_, ?_⟩
  · simpa [Nat.cast_add] using hRealAbs _ _ hLower₁ hUpper₁
  · simpa [Nat.cast_add] using hRealAbs _ _ hLower₂ hUpper₂
  · simpa [Nat.cast_add] using hRealAbs _ _ hLower₃ hUpper₃

/-- Flooring the common and private real information
amounts to obtain integer block lengths within a constant of the desired rates, with total
length bounded linearly in `n`. -/
private theorem remark2_rounding (α β γ : ℝ)
    (hα : 0 ≤ α) (hαγ : α ≤ γ) (hβγ : β ≤ γ)
    (hγ : γ ≤ α + β) :
    ∃ B : ℕ, γ ≤ B ∧ ∀ n : ℕ, ∃ m p q : ℕ,
      m = ⌊(α + β - γ) * n⌋₊ ∧
      p = ⌊(γ - β) * n⌋₊ ∧
      q = ⌊(γ - α) * n⌋₊ ∧
      m + p + q ≤ B * (n + 1) ∧
      |(m + p : ℝ) - α * n| ≤ 2 ∧
      |(m + q : ℝ) - β * n| ≤ 2 ∧
      |(m + p + q : ℝ) - γ * n| ≤ 3 := by
  let B : ℕ := ⌊γ⌋₊ + 1
  have hγ0 : 0 ≤ γ := le_trans hα hαγ
  have hB : γ ≤ B := by
    dsimp [B]
    push_cast
    exact (Nat.lt_floor_add_one γ).le
  refine ⟨B, hB, fun n => ?_⟩
  let m : ℕ := ⌊(α + β - γ) * n⌋₊
  let p : ℕ := ⌊(γ - β) * n⌋₊
  let q : ℕ := ⌊(γ - α) * n⌋₊
  have hshared : 0 ≤ (α + β - γ) * (n : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hγ) (Nat.cast_nonneg n)
  have hpv : 0 ≤ (γ - β) * (n : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hβγ) (Nat.cast_nonneg n)
  have hqv : 0 ≤ (γ - α) * (n : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hαγ) (Nat.cast_nonneg n)
  have hmlo : (m : ℝ) ≤ (α + β - γ) * n := by
    dsimp [m]
    exact Nat.floor_le hshared
  have hmhi : (α + β - γ) * n < (m : ℝ) + 1 := by
    dsimp [m]
    exact Nat.lt_floor_add_one _
  have hplo : (p : ℝ) ≤ (γ - β) * n := by
    dsimp [p]
    exact Nat.floor_le hpv
  have hphi : (γ - β) * n < (p : ℝ) + 1 := by
    dsimp [p]
    exact Nat.lt_floor_add_one _
  have hqlo : (q : ℝ) ≤ (γ - α) * n := by
    dsimp [q]
    exact Nat.floor_le hqv
  have hqhi : (γ - α) * n < (q : ℝ) + 1 := by
    dsimp [q]
    exact Nat.lt_floor_add_one _
  have hmp : |(m + p : ℝ) - α * n| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hmlo, hmhi, hplo, hphi]
  have hmq : |(m + q : ℝ) - β * n| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hmlo, hmhi, hqlo, hqhi]
  have htotal : |(m + p + q : ℝ) - γ * n| ≤ 3 := by
    rw [abs_le]
    constructor <;> nlinarith [hmlo, hmhi, hplo, hphi, hqlo, hqhi]
  have hlenReal : (m + p + q : ℝ) ≤ B * (n : ℝ) := by
    calc
      (m : ℝ) + (p : ℝ) + (q : ℝ)
          ≤ (α + β - γ) * n + (γ - β) * n + (γ - α) * n := by
            linarith [hmlo, hplo, hqlo]
      _ = γ * n := by ring
      _ ≤ B * n := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg n)
  have hlen : m + p + q ≤ B * (n + 1) := by
    have hlenN : m + p + q ≤ B * n := by exact_mod_cast hlenReal
    exact hlenN.trans (Nat.mul_le_mul_left B (Nat.le_succ n))
  exact ⟨m, p, q, rfl, rfl, rfl, hlen, hmp, hmq, htotal⟩

/-- **Remark 2.** For reals `0 ≤ α, β ≤ γ ≤ α + β` and every `n` there is a pair `x₁, x₂` with
`K(x₁) = αn + O(log n)`, `K(x₂) = βn + O(log n)`, `K(x₁, x₂) = γn + O(log n)`. -/
theorem remark2 (D : Map) (hD : isOptimalConditional D) (α β γ : ℝ)
    (hα : 0 ≤ α) (_hβ : 0 ≤ β) (hαγ : α ≤ γ) (hβγ : β ≤ γ) (hγ : γ ≤ α + β) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ x₁ x₂ : BitString,
      |(natK D x₁ : ℝ) - α * n| ≤ logSlack c n ∧
      |(natK D x₂ : ℝ) - β * n| ≤ logSlack c n ∧
      |(natK D (pairCode x₁ x₂) : ℝ) - γ * n| ≤ logSlack c n := by
  obtain ⟨B, hB, hRound⟩ := remark2_rounding α β γ hα hαγ hβγ hγ
  obtain ⟨c₀, hSplit⟩ := remark2_split_incompressible D hD B
  refine ⟨c₀ + 3, fun n => ?_⟩
  obtain ⟨m, p, q, hm, hp, hq, hlen, hmp, hmq, htotal⟩ := hRound n
  obtain ⟨s, hslen, hsK⟩ :=
    exists_incompressible_string D [] (m + p + q)
  have hsK' : ((m + p + q : ℕ) : ENat) ≤ plainK D s := by
    simpa [plainK] using hsK
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁len, hx₂len, hK₁, hK₂, hK₁₂⟩ :=
    hSplit n m p q hlen s hslen hsK'
  have h1 : |(natK D x₁ : ℝ) - α * n| ≤ logSlack (c₀ + 3) n := by
    calc
      |(natK D x₁ : ℝ) - α * n|
          = |((natK D x₁ : ℝ) - (m + p : ℝ)) + ((m + p : ℝ) - α * n)| := by ring_nf
      _ ≤ |(natK D x₁ : ℝ) - (m + p : ℝ)| + |(m + p : ℝ) - α * n| := abs_add_le _ _
      _ ≤ logSlack c₀ n + 2 := add_le_add hK₁ hmp
      _ ≤ logSlack (c₀ + 3) n := by
        have h := logSlack_add_nat_le c₀ 3 n
        exact_mod_cast (le_trans (by omega : logSlack c₀ n + 2 ≤ logSlack c₀ n + 3) h)
  have h2 : |(natK D x₂ : ℝ) - β * n| ≤ logSlack (c₀ + 3) n := by
    calc
      |(natK D x₂ : ℝ) - β * n|
          = |((natK D x₂ : ℝ) - (m + q : ℝ)) + ((m + q : ℝ) - β * n)| := by ring_nf
      _ ≤ |(natK D x₂ : ℝ) - (m + q : ℝ)| + |(m + q : ℝ) - β * n| := abs_add_le _ _
      _ ≤ logSlack c₀ n + 2 := add_le_add hK₂ hmq
      _ ≤ logSlack (c₀ + 3) n := by
        have h := logSlack_add_nat_le c₀ 3 n
        exact_mod_cast (le_trans (by omega : logSlack c₀ n + 2 ≤ logSlack c₀ n + 3) h)
  have h3 : |(natK D (pairCode x₁ x₂) : ℝ) - γ * n| ≤ logSlack (c₀ + 3) n := by
    calc
      |(natK D (pairCode x₁ x₂) : ℝ) - γ * n|
          = |((natK D (pairCode x₁ x₂) : ℝ) - (m + p + q : ℝ)) +
              ((m + p + q : ℝ) - γ * n)| := by ring_nf
      _ ≤ |(natK D (pairCode x₁ x₂) : ℝ) - (m + p + q : ℝ)| +
            |(m + p + q : ℝ) - γ * n| := abs_add_le _ _
      _ ≤ logSlack c₀ n + 3 := add_le_add hK₁₂ htotal
      _ ≤ logSlack (c₀ + 3) n := by exact_mod_cast logSlack_add_nat_le c₀ 3 n
  exact ⟨x₁, x₂, h1, h2, h3⟩

end Kolmogorov.Relativization
