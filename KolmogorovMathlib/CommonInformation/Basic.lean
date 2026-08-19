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
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
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
  have htake_comp : Computable (fun w : BitString => w.take (w.length / 2)) :=
    (Primrec.list_take.comp
      (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)) Primrec.id).to_comp
  have hdrop_comp : Computable (fun w : BitString => w.drop (w.length / 2)) :=
    (Primrec.list_drop.comp
      (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)) Primrec.id).to_comp
  obtain ⟨cEval, hEval⟩ := condK_output_given_plainProgram_le V hV
  obtain ⟨cRec, hRec⟩ := condK_output_given_appendedPairCode_le V hV
  obtain ⟨cSD, hSD⟩ := condK_shortestDescription_le V hV
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cOut, hOut⟩ := plainK_output_le_plainK_program V hV
  obtain ⟨cApp, hApp⟩ := plainK_append_le_pairPlainK V hV
  obtain ⟨cSub, hSub⟩ := pairPlainK_le_plainK_add_plainK_values V hV
  obtain ⟨cTake, hTake⟩ := condKMapLe V hV (fun w => w.take (w.length / 2)) htake_comp
  obtain ⟨cDrop, hDrop⟩ := condKMapLe V hV (fun w => w.drop (w.length / 2)) hdrop_comp
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cSub 2 cLen
  set C : Nat :=
    cEval + cRec + cSD + cLen + cOut + cApp + cSub + cTake + cDrop + cFold with hCdef
  -- A constant `≤ C` fits inside one `logSlack C (n+1)` budget.
  have hCbigNat : ∀ (n d : Nat), d ≤ C → d ≤ logSlack C (n + 1) := by
    intro n d hd
    have hCle : C ≤ logSlack C (n + 1) := by
      unfold logSlack
      exact Nat.le_add_left C (C * (Nat.bits (n + 1)).length)
    exact le_trans hd hCle
  have hCbig : ∀ (n d : Nat), d ≤ C → (d : ENat) ≤ (logSlack C (n + 1) : ENat) := by
    intro n d hd
    exact_mod_cast hCbigNat n d hd
  -- Fold `logSlack a (n+1) + d` into one `logSlack C (n+1)`.
  have hfoldE : ∀ (n a d : Nat), a + d ≤ C →
      (logSlack a (n + 1) : ENat) + (d : ENat) ≤ (logSlack C (n + 1) : ENat) := by
    intro n a d had
    have hnat : logSlack a (n + 1) + d ≤ logSlack C (n + 1) :=
      le_trans (logSlack_add_nat_le a d (n + 1)) (logSlack_mono_left had (n + 1))
    calc (logSlack a (n + 1) : ENat) + (d : ENat)
        = ((logSlack a (n + 1) + d : Nat) : ENat) := by push_cast; ring
      _ ≤ (logSlack C (n + 1) : ENat) := by exact_mod_cast hnat
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
  -- length upper bounds on marginal and pair complexities
  have hk1_len : k1 ≤ k / 2 + cLen := by
    have h : (k1 : ENat) ≤ ((x₁.length + cLen : Nat) : ENat) := by
      calc (k1 : ENat) = plainK V x₁ := hk1.symm
        _ ≤ (x₁.length : ENat) + (cLen : ENat) := hLen x₁
        _ = ((x₁.length + cLen : Nat) : ENat) := by push_cast; ring
    have h' : k1 ≤ x₁.length + cLen := by exact_mod_cast h
    rw [hx1len] at h'; exact h'
  have hk2_len : k2 ≤ (k - k / 2) + cLen := by
    have h : (k2 : ENat) ≤ ((x₂.length + cLen : Nat) : ENat) := by
      calc (k2 : ENat) = plainK V x₂ := hk2.symm
        _ ≤ (x₂.length : ENat) + (cLen : ENat) := hLen x₂
        _ = ((x₂.length + cLen : Nat) : ENat) := by push_cast; ring
    have h' : k2 ≤ x₂.length + cLen := by exact_mod_cast h
    rw [hx2len] at h'; exact h'
  have hkpair_len : kpair + 1 ≤ 2 * (k + 1) + cLen := by
    have h : (kpair : ENat) ≤ (((pairCode x₁ x₂).length + cLen : Nat) : ENat) := by
      calc (kpair : ENat) = plainK V (pairCode x₁ x₂) := hkpair.symm
        _ ≤ ((pairCode x₁ x₂).length : ENat) + (cLen : ENat) := hLen (pairCode x₁ x₂)
        _ = (((pairCode x₁ x₂).length + cLen : Nat) : ENat) := by push_cast; ring
    have h' : kpair ≤ (pairCode x₁ x₂).length + cLen := by exact_mod_cast h
    rw [length_pairCode, hx1len, hx2len] at h'
    omega
  -- pair subadditivity and slack fold
  have hsub_inst : kpair ≤ k1 + k2 + logSlack cSub (kpair + 1) :=
    hSub x₁ x₂ k1 k2 kpair hk1 hk2 hkpair
  have hslackfold : logSlack cSub (kpair + 1) ≤ logSlack cFold (k + 1) :=
    le_trans (logSlack_mono_right cSub hkpair_len) (hFold (k + 1))
  -- incompressibility of `x'`: `k ≤ C(pairCode x₁ x₂) + O(1)`
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
  -- the folded logarithmic budget shared by both incompressibility bounds
  have hfoldC : logSlack cFold (k + 1) + (cLen + cApp + cOut) ≤ logSlack C (k + 1) :=
    le_trans (logSlack_add_nat_le cFold (cLen + cApp + cOut) (k + 1))
      (logSlack_mono_left (by omega) (k + 1))
  have hincompNat_x1 : x₁.length ≤ k1 + logSlack C (k + 1) := by
    rw [hx1len]; omega
  have hincompNat_x2 : x₂.length ≤ k2 + logSlack C (k + 1) := by
    rw [hx2len]; omega
  -- conditional simplicity of the halves given `x`
  have hcondx1 : condK V x₁ x ≤ condK V p x + (cTake : ENat) := by
    have h := hTake p x
    simp only [hpLength] at h
    rw [hx1def]; exact h
  have hcondx2 : condK V x₂ x ≤ condK V p x + (cDrop : ENat) := by
    have h := hDrop p x
    simp only [hpLength] at h
    rw [hx2def]; exact h
  refine ⟨x₁, x₂, hx1len, hx2len, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- condK V x (x₁ ++ x₂) ≤ slack
    rw [happend]
    exact le_trans (hEval p x hp) (hCbig k cEval (by omega))
  · -- condK V (x₁ ++ x₂) x ≤ slack
    rw [happend]
    exact le_trans (hSD x p k hx hp hpLength)
      (by exact_mod_cast logSlack_mono_left (show cSD ≤ C by omega) (k + 1))
  · -- condK V x₁ x ≤ slack
    calc condK V x₁ x ≤ condK V p x + (cTake : ENat) := hcondx1
      _ ≤ (logSlack cSD (k + 1) : ENat) + (cTake : ENat) := by
        gcongr
        exact hSD x p k hx hp hpLength
      _ ≤ (logSlack C (k + 1) : ENat) := hfoldE k cSD cTake (by omega)
  · -- condK V x₂ x ≤ slack
    calc condK V x₂ x ≤ condK V p x + (cDrop : ENat) := hcondx2
      _ ≤ (logSlack cSD (k + 1) : ENat) + (cDrop : ENat) := by
        gcongr
        exact hSD x p k hx hp hpLength
      _ ≤ (logSlack C (k + 1) : ENat) := hfoldE k cSD cDrop (by omega)
  · -- condK V x (pairCode x₁ x₂) ≤ slack
    exact le_trans (hRec x x₁ x₂ (by rw [happend]; exact hp)) (hCbig k cRec (by omega))
  · -- plainK V x₁ ≤ x₁.length + slack
    calc plainK V x₁ ≤ (x₁.length : ENat) + (cLen : ENat) := hLen x₁
      _ ≤ (x₁.length : ENat) + (logSlack C (k + 1) : ENat) := by
        gcongr; exact hCbigNat k cLen (by omega)
  · -- PlainIncompressibleWithin V x₁ slack
    unfold PlainIncompressibleWithin
    rw [hk1]
    calc (x₁.length : ENat)
        ≤ ((k1 + logSlack C (k + 1) : Nat) : ENat) := by exact_mod_cast hincompNat_x1
      _ = (k1 : ENat) + (logSlack C (k + 1) : ENat) := by push_cast; ring
  · -- plainK V x₂ ≤ x₂.length + slack
    calc plainK V x₂ ≤ (x₂.length : ENat) + (cLen : ENat) := hLen x₂
      _ ≤ (x₂.length : ENat) + (logSlack C (k + 1) : ENat) := by
        gcongr; exact hCbigNat k cLen (by omega)
  · -- PlainIncompressibleWithin V x₂ slack
    unfold PlainIncompressibleWithin
    rw [hk2]
    calc (x₂.length : ENat)
        ≤ ((k2 + logSlack C (k + 1) : Nat) : ENat) := by exact_mod_cast hincompNat_x2
      _ = (k2 : ENat) + (logSlack C (k + 1) : ENat) := by push_cast; ring

end Kolmogorov
