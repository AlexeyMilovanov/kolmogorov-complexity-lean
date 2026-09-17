import KolmogorovMathlib.CommonInformation.Splitting

/-!
# Common Information: Basic Definitions

Statement-level infrastructure for SUV Chapter 11.  The chapter uses plain
complexity throughout; pair complexity uses the canonical `pairCode`.
-/

namespace Kolmogorov

/-- SUV Theorem 221: every finite-complexity string has an incompressible
shortest-description representation carrying the same information. -/
theorem exists_incompressibleRepresentation (V : Map) (hV : isOptimalConditional V) :
    exists c : Nat, forall (x : BitString) (k : Nat),
      HasPlainComplexityValue V x k ->
        exists x' : BitString,
          x'.length = k /\
          PlainEquivalentWithin V x x' (logSlack c (k + 1)) /\
          PlainIncompressibleWithin V x' (logSlack c (k + 1)) := by
  obtain ⟨cEval, hEval⟩ := condK_output_given_plainProgram_le V hV
  obtain ⟨cOutput, hOutput⟩ := plainK_output_le_plainK_program V hV
  obtain ⟨cPair, hPair⟩ := pairPlainK_output_program_le_plainK_program V hV
  obtain ⟨cLength, hLength⟩ := plainK_le_length V hV
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_lower_values V hV
  obtain ⟨cClose, hClose⟩ :=
    chain_lower_close_conditional (cLength + cPair) cChain
  let C := cEval + cOutput + cClose
  have hcEval : cEval ≤ C := by dsimp [C]; omega
  have hcOutput : cOutput ≤ C := by dsimp [C]; omega
  have hcClose : cClose ≤ C := by dsimp [C]; omega
  have hC_le_slack (n : Nat) : C ≤ logSlack C n := by
    unfold logSlack
    omega
  refine ⟨C, fun x k hx => ?_⟩
  obtain ⟨p, hp, hpLength⟩ := hx.exists_program
  obtain ⟨kpCond, hkpCond⟩ :=
    exists_plainConditionalComplexityValue V hV p x
  obtain ⟨kPair, hkPair⟩ :=
    exists_plainComplexityValue V hV (pairCode x p)
  have hkPairBoundENat :
      (kPair : ENat) ≤ (k : ENat) + ((cLength + cPair : Nat) : ENat) := by
    calc
      (kPair : ENat) = pairPlainK V x p := by
        rw [pairPlainK, hkPair]
      _ ≤ plainK V p + (cPair : ENat) := hPair p x hp
      _ ≤ ((p.length : Nat) : ENat) + (cLength : ENat) + (cPair : ENat) := by
        gcongr
        exact hLength p
      _ = (k : ENat) + ((cLength + cPair : Nat) : ENat) := by
        simp only [hpLength, Nat.cast_add]
        simp [add_assoc, add_comm]
  have hkPairBound : kPair ≤ k + (cLength + cPair) := by
    exact_mod_cast hkPairBoundENat
  have hChainInst :
      k + kpCond ≤ kPair + logSlack cChain (kPair + 1) :=
    hChain x p k kpCond kPair hx hkpCond hkPair
  have hkpCondClose :
      kpCond ≤ logSlack cClose (k + 1) :=
    hClose k kpCond kPair hkPairBound hChainInst
  have hEvalSlack : cEval ≤ logSlack C (k + 1) :=
    hcEval.trans (hC_le_slack (k + 1))
  have hOutputSlack : cOutput ≤ logSlack C (k + 1) :=
    hcOutput.trans (hC_le_slack (k + 1))
  have hCloseSlack :
      logSlack cClose (k + 1) ≤ logSlack C (k + 1) :=
    logSlack_mono_left hcClose (k + 1)
  refine ⟨p, hpLength, ?_, ?_⟩
  · unfold PlainEquivalentWithin
    constructor
    · exact (hEval p x hp).trans (by exact_mod_cast hEvalSlack)
    · calc
        condK V p x = (kpCond : ENat) := hkpCond
        _ ≤ (logSlack cClose (k + 1) : Nat) := by
          exact_mod_cast hkpCondClose
        _ ≤ (logSlack C (k + 1) : Nat) := by
          exact_mod_cast hCloseSlack
  · unfold PlainIncompressibleWithin
    calc
      (p.length : ENat) = (k : ENat) := by exact_mod_cast hpLength
      _ = plainK V x := hx.symm
      _ ≤ plainK V p + (cOutput : ENat) := hOutput p x hp
      _ ≤ plainK V p + (logSlack C (k + 1) : ENat) := by
        have hs :
            (cOutput : ENat) ≤ (logSlack C (k + 1) : ENat) := by
          exact_mod_cast hOutputSlack
        exact add_le_add_right hs _

/-- Taking the first half of a bit string is computable. -/
private lemma computable_take_half : Computable (fun w : BitString => w.take (w.length / 2)) :=
  (Primrec.list_take.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2))
    Primrec.id).to_comp

/-- Taking the second half of a bit string is computable. -/
private lemma computable_drop_half : Computable (fun w : BitString => w.drop (w.length / 2)) :=
  (Primrec.list_drop.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2))
    Primrec.id).to_comp

/-- A constant bounded by `C` is bounded by `logSlack C (n + 1)`. -/
private lemma nat_le_logSlack (C n d : Nat) (hd : d ≤ C) : d ≤ logSlack C (n + 1) := by
  have hCle : C ≤ logSlack C (n + 1) := by
    unfold logSlack
    exact Nat.le_add_left C (C * (Nat.bits (n + 1)).length)
  exact le_trans hd hCle

/-- A constant bounded by `C` is bounded as an `ENat` by `logSlack C (n + 1)`. -/
private lemma enat_le_logSlack (C n d : Nat) (hd : d ≤ C) :
    (d : ENat) ≤ (logSlack C (n + 1) : ENat) := by
  exact_mod_cast nat_le_logSlack C n d hd

/-- Adding a constant `d` to `logSlack a (n + 1)` is bounded by `logSlack C (n + 1)`
when `a + d ≤ C`. -/
private lemma logSlack_add_nat_le_logSlack (C n a d : Nat) (had : a + d ≤ C) :
    (logSlack a (n + 1) : ENat) + (d : ENat) ≤ (logSlack C (n + 1) : ENat) := by
  have hnat : logSlack a (n + 1) + d ≤ logSlack C (n + 1) :=
    le_trans (logSlack_add_nat_le a d (n + 1)) (logSlack_mono_left had (n + 1))
  calc (logSlack a (n + 1) : ENat) + (d : ENat)
      = ((logSlack a (n + 1) + d : Nat) : ENat) := by push_cast; ring
    _ ≤ (logSlack C (n + 1) : ENat) := by exact_mod_cast hnat

/-- Bounding complexity value `kw` by string length plus `cLen`. -/
private lemma complexity_val_le_length_add
    (V : Map) (w : BitString) (kw cLen : Nat)
    (hkw : HasPlainComplexityValue V w kw)
    (hLen : ∀ y, plainK V y ≤ (y.length : ENat) + (cLen : ENat)) :
    kw ≤ w.length + cLen := by
  have h : (kw : ENat) ≤ ((w.length + cLen : Nat) : ENat) := by
    calc (kw : ENat) = plainK V w := hkw.symm
      _ ≤ (w.length : ENat) + (cLen : ENat) := hLen w
      _ = ((w.length + cLen : Nat) : ENat) := by push_cast; ring
  exact_mod_cast h

/-- If the shortest description `p` of `x` costs at most `logSlack cSD (k + 1)` given `x`, and
`w` is obtained from `p` at an extra cost of `cMap`, then `w` costs at most
`logSlack C (k + 1)` given `x`, for any `C` with `cSD + cMap ≤ C`. -/
private lemma condK_le_logSlack_of_le_add
    (V : Map) (cSD cMap C k : Nat) (x p w : BitString)
    (hSD : condK V p x ≤ (logSlack cSD (k + 1) : ENat))
    (hMap : condK V w x ≤ condK V p x + (cMap : ENat))
    (hbound : cSD + cMap ≤ C) :
    condK V w x ≤ (logSlack C (k + 1) : ENat) := by
  calc condK V w x ≤ condK V p x + (cMap : ENat) := hMap
    _ ≤ (logSlack cSD (k + 1) : ENat) + (cMap : ENat) := by gcongr
    _ ≤ (logSlack C (k + 1) : ENat) := logSlack_add_nat_le_logSlack C k cSD cMap hbound

/-- Plain complexity of a string is bounded by its length plus `logSlack C (k + 1)`. -/
private lemma plainK_le_length_add_logSlack
    (V : Map) (cLen C k : Nat) (w : BitString)
    (hLen : ∀ y, plainK V y ≤ (y.length : ENat) + (cLen : ENat))
    (hcLen : cLen ≤ C) :
    plainK V w ≤ (w.length : ENat) + (logSlack C (k + 1) : ENat) := by
  calc plainK V w ≤ (w.length : ENat) + (cLen : ENat) := hLen w
    _ ≤ (w.length : ENat) + (logSlack C (k + 1) : ENat) := by
      gcongr; exact nat_le_logSlack C k cLen hcLen

/-- Convert a natural inequality on length to `PlainIncompressibleWithin`. -/
private lemma plainIncompressibleWithin_of_length_le
    (V : Map) (w : BitString) (kw C k : Nat)
    (hkw : HasPlainComplexityValue V w kw)
    (hlen : w.length ≤ kw + logSlack C (k + 1)) :
    PlainIncompressibleWithin V w (logSlack C (k + 1)) := by
  unfold PlainIncompressibleWithin
  rw [hkw]
  calc (w.length : ENat)
      ≤ ((kw + logSlack C (k + 1) : Nat) : ENat) := by exact_mod_cast hlen
    _ = (kw : ENat) + (logSlack C (k + 1) : ENat) := by push_cast; ring

/-- SUV Exercise 305: splitting an incompressible shortest-description
representation into literal near-equal halves fulfils all the requirements of
§11.1.  Taking `x'` to be a shortest description of `x` and `x₁, x₂` its two
halves, each half has plain complexity close to its length, is simple relative
to the original string, and together the halves recover the original
information.  All approximate equalities hold with `O(log C(x))` accuracy. -/
theorem exists_split_incompressible_halves
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x : BitString) (k : Nat),
      HasPlainComplexityValue V x k →
      ∃ x₁ x₂ : BitString,
        x₁.length = k / 2 ∧
        x₂.length = k - k / 2 ∧
        PlainEquivalentWithin V x (x₁ ++ x₂) (logSlack c (k + 1)) ∧
        condK V x₁ x ≤ (logSlack c (k + 1) : ENat) ∧
        condK V x₂ x ≤ (logSlack c (k + 1) : ENat) ∧
        condK V x (pairCode x₁ x₂) ≤ (logSlack c (k + 1) : ENat) ∧
        plainK V x₁ ≤
          (x₁.length : ENat) + (logSlack c (k + 1) : ENat) ∧
        PlainIncompressibleWithin V x₁ (logSlack c (k + 1)) ∧
        plainK V x₂ ≤
          (x₂.length : ENat) + (logSlack c (k + 1) : ENat) ∧
        PlainIncompressibleWithin V x₂ (logSlack c (k + 1)) := by
  obtain ⟨cEval, hEval⟩ := condK_output_given_plainProgram_le V hV
  obtain ⟨cRec, hRec⟩ := condK_output_given_appendedPairCode_le V hV
  obtain ⟨cSD, hSD⟩ := condK_shortestDescription_le V hV
  obtain ⟨cLen, hLen⟩ := plainK_le_length V hV
  obtain ⟨cOut, hOut⟩ := plainK_output_le_plainK_program V hV
  obtain ⟨cApp, hApp⟩ := plainK_append_le_pairPlainK V hV
  obtain ⟨cSub, hSub⟩ := pairPlainK_le_plainK_add_plainK_values V hV
  obtain ⟨cTake, hTake⟩ := condK_map_le V hV (fun w => w.take (w.length / 2)) computable_take_half
  obtain ⟨cDrop, hDrop⟩ := condK_map_le V hV (fun w => w.drop (w.length / 2)) computable_drop_half
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cSub 2 cLen
  set C : Nat :=
    cEval + cRec + cSD + cLen + cOut + cApp + cSub + cTake + cDrop + cFold with hCdef
  refine ⟨C, fun x k hx => ?_⟩
  obtain ⟨p, hp, hpLength⟩ := hx.exists_program
  set x₁ := p.take (k / 2) with hx1def
  set x₂ := p.drop (k / 2) with hx2def
  have hx1len : x₁.length = k / 2 := by
    rw [hx1def, List.length_take, hpLength]
    exact Nat.min_eq_left (Nat.div_le_self k 2)
  have hx2len : x₂.length = k - k / 2 := by
    rw [hx2def, List.length_drop, hpLength]
  have happend : x₁ ++ x₂ = p := by
    rw [hx1def, hx2def]; exact List.take_append_drop (k / 2) p
  obtain ⟨k1, hk1⟩ := exists_plainComplexityValue V hV x₁
  obtain ⟨k2, hk2⟩ := exists_plainComplexityValue V hV x₂
  obtain ⟨kpair, hkpair⟩ := exists_plainComplexityValue V hV (pairCode x₁ x₂)
  have hk1_len : k1 ≤ k / 2 + cLen := by
    have h := complexity_val_le_length_add V x₁ k1 cLen hk1 hLen
    rw [hx1len] at h; exact h
  have hk2_len : k2 ≤ (k - k / 2) + cLen := by
    have h := complexity_val_le_length_add V x₂ k2 cLen hk2 hLen
    rw [hx2len] at h; exact h
  have hkpair_len : kpair + 1 ≤ 2 * (k + 1) + cLen := by
    have h := complexity_val_le_length_add V (pairCode x₁ x₂) kpair cLen hkpair hLen
    rw [length_pairCode, hx1len, hx2len] at h
    omega
  have hsub_inst : kpair ≤ k1 + k2 + logSlack cSub (kpair + 1) :=
    hSub x₁ x₂ k1 k2 kpair hk1 hk2 hkpair
  have hkStar : k ≤ kpair + (cApp + cOut) := by
    have h : (k : ENat) ≤ (kpair : ENat) + ((cApp + cOut : Nat) : ENat) := by
      calc (k : ENat) = plainK V x := hx.symm
        _ ≤ plainK V p + (cOut : ENat) := hOut p x hp
        _ = plainK V (x₁ ++ x₂) + (cOut : ENat) := by rw [happend]
        _ ≤ (pairPlainK V x₁ x₂ + (cApp : ENat)) + (cOut : ENat) := by
            gcongr; exact hApp x₁ x₂
        _ = ((kpair : ENat) + (cApp : ENat)) + (cOut : ENat) := by rw [pairPlainK, hkpair]
        _ = (kpair : ENat) + ((cApp + cOut : Nat) : ENat) := by push_cast; ring
    exact_mod_cast h
  have hfoldC : logSlack cFold (k + 1) + (cLen + cApp + cOut) ≤ logSlack C (k + 1) :=
    le_trans (logSlack_add_nat_le cFold (cLen + cApp + cOut) (k + 1))
      (logSlack_mono_left (by omega) (k + 1))
  have hfold_inst : logSlack cSub (kpair + 1) ≤ logSlack cFold (k + 1) :=
    logSlack_le_of_linear_bound hFold hkpair_len
  have hincompNat_x1 : x₁.length ≤ k1 + logSlack C (k + 1) := by omega
  have hincompNat_x2 : x₂.length ≤ k2 + logSlack C (k + 1) := by omega
  have hcondx1 : condK V x₁ x ≤ condK V p x + (cTake : ENat) := by
    have h := hTake p x
    simp only [hpLength] at h
    rw [hx1def]; exact h
  have hcondx2 : condK V x₂ x ≤ condK V p x + (cDrop : ENat) := by
    have h := hDrop p x
    simp only [hpLength] at h
    rw [hx2def]; exact h
  have hSD_inst : condK V p x ≤ (logSlack cSD (k + 1) : ENat) := hSD x p k hx hp hpLength
  refine ⟨x₁, x₂, hx1len, hx2len, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [happend]; exact le_trans (hEval p x hp) (enat_le_logSlack C k cEval (by omega))
  · rw [happend]
    exact le_trans hSD_inst (by exact_mod_cast logSlack_mono_left (show cSD ≤ C by omega) (k + 1))
  · exact condK_le_logSlack_of_le_add V cSD cTake C k x p x₁ hSD_inst hcondx1 (by omega)
  · exact condK_le_logSlack_of_le_add V cSD cDrop C k x p x₂ hSD_inst hcondx2 (by omega)
  · exact le_trans (hRec x x₁ x₂ (by rw [happend]; exact hp)) (enat_le_logSlack C k cRec (by omega))
  · exact plainK_le_length_add_logSlack V cLen C k x₁ hLen (by omega)
  · exact plainIncompressibleWithin_of_length_le V x₁ k1 C k hk1 hincompNat_x1
  · exact plainK_le_length_add_logSlack V cLen C k x₂ hLen (by omega)
  · exact plainIncompressibleWithin_of_length_le V x₂ k2 C k hk2 hincompNat_x2

end Kolmogorov
