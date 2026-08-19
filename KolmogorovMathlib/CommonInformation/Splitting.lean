import KolmogorovMathlib.CommonInformation.PlainSymmetry

/-!
# Common Information: literal concatenation and splitting infrastructure

Chapter-local helpers for SUV Exercise 305 (splitting an incompressible
shortest description into halves).  Everything here is expressed in plain
complexity with `logSlack` accuracy.  The four reusable facts are:

* `plainK_append_le_pairPlainK` — a literal concatenation is no more complex
  than the canonical pair code of its parts, up to a constant.
* `pairPlainK_le_plainK_add_plainK_values` — plain pair subadditivity in
  exact-value form (from the two-sided plain SOI).
* `condK_output_given_appendedPairCode_le` — a string is `O(1)`-simple given
  the canonical pair code of two strings whose literal concatenation is one of
  its programs.
* `condK_shortestDescription_le` — the Kolmogorov–Levin step of Theorem 221,
  exposed for an explicitly extracted shortest description.
-/

namespace Kolmogorov

/-- The plain complexity of a literal concatenation is bounded by the plain
complexity of the canonical pair code of its parts, up to a constant.  (Decode
both components of a pair code and concatenate.) -/
theorem plainK_append_le_pairPlainK (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString,
      plainK V (x ++ y) ≤ pairPlainK V x y + (c : ENat) := by
  have hg : Computable (fun w : BitString => decodeFirst w ++ decodeSecond w) :=
    Computable.list_append.comp decodeFirst_computable decodeSecond_computable
  obtain ⟨c, hc⟩ := plainKMapLe V hV (fun w => decodeFirst w ++ decodeSecond w) hg
  refine ⟨c, fun x y => ?_⟩
  have h := hc (pairCode x y)
  simpa [pairPlainK, decodeFirst_pairCode, decodeSecond_pairCode] using h

/-- Plain pair subadditivity in exact-value form: the pair complexity is at
most the sum of the marginal plain complexities plus a logarithmic slack in the
pair complexity.  This is the upper plain symmetry-of-information inequality with
the conditional complexity discharged by `condK V y x ≤ plainK V y + O(1)`. -/
theorem pairPlainK_le_plainK_add_plainK_values (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString, ∀ kx ky kxy : Nat,
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V y ky →
      HasPlainComplexityValue V (pairCode x y) kxy →
      kxy ≤ kx + ky + logSlack c (kxy + 1) := by
  obtain ⟨cUpper, hUpper⟩ := pairPlainK_chain_upper_values V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  refine ⟨cUpper + cCond, fun x y kx ky kxy hx hy hxy => ?_⟩
  obtain ⟨kyx, hkyx⟩ := exists_plainConditionalComplexityValue V hV y x
  have hkyxle : kyx ≤ ky + cCond := by
    have h : (kyx : ENat) ≤ (ky : ENat) + (cCond : ENat) := by
      calc
        (kyx : ENat) = condK V y x := hkyx.symm
        _ ≤ plainK V y + (cCond : ENat) := hCond y x
        _ = (ky : ENat) + (cCond : ENat) := by rw [hy]
    exact_mod_cast h
  have hup := hUpper x y kx kyx kxy hx hkyx hxy
  have hfold :
      logSlack cUpper (kxy + 1) + cCond ≤ logSlack (cUpper + cCond) (kxy + 1) :=
    logSlack_add_nat_le cUpper cCond (kxy + 1)
  omega

/-- A string is `O(1)`-simple given the canonical pair code of any two strings
whose literal concatenation is one of its programs.  (Decode both components,
concatenate, and run `V`.) -/
theorem condK_output_given_appendedPairCode_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x x₁ x₂ : BitString,
      produces V (x₁ ++ x₂) [] x →
      condK V x (pairCode x₁ x₂) ≤ (c : ENat) := by
  let D : Map := fun pr => V (decodeFirst pr.2 ++ decodeSecond pr.2, [])
  have hD : isDecompressor D :=
    Partrec.comp hV.1
      (Computable.pair
        (Computable.list_append.comp
          (decodeFirst_computable.comp Computable.snd)
          (decodeSecond_computable.comp Computable.snd))
        (Computable.const []))
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun x x₁ x₂ hp => ?_⟩
  have hDprod : produces D [] (pairCode x₁ x₂) x := by
    change x ∈ V (decodeFirst (pairCode x₁ x₂) ++ decodeSecond (pairCode x₁ x₂), [])
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    exact hp
  calc
    condK V x (pairCode x₁ x₂) ≤ condK D x (pairCode x₁ x₂) + (c : ENat) :=
      hc x (pairCode x₁ x₂)
    _ ≤ (0 : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨[], hDprod, rfl⟩
    _ = (c : ENat) := zero_add _

/-- The Kolmogorov–Levin step of Theorem 221, exposed for an explicitly
extracted shortest description `p` of `x`: the conditional complexity of `p`
given `x` is logarithmic in `C(x)`. -/
theorem condK_shortestDescription_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x p : BitString) (k : Nat),
      HasPlainComplexityValue V x k →
      produces V p [] x →
      p.length = k →
      condK V p x ≤ (logSlack c (k + 1) : ENat) := by
  obtain ⟨cPair, hPair⟩ := pairPlainK_output_program_le_plainK_program V hV
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_lower_values V hV
  obtain ⟨cClose, hClose⟩ := chain_lower_close_conditional (cLength + cPair) cChain
  refine ⟨cClose, fun x p k hx hp hpLength => ?_⟩
  obtain ⟨kpCond, hkpCond⟩ := exists_plainConditionalComplexityValue V hV p x
  obtain ⟨kPair, hkPair⟩ := exists_plainComplexityValue V hV (pairCode x p)
  have hkPairBoundENat :
      (kPair : ENat) ≤ (k : ENat) + ((cLength + cPair : Nat) : ENat) := by
    calc
      (kPair : ENat) = pairPlainK V x p := by rw [pairPlainK, hkPair]
      _ ≤ plainK V p + (cPair : ENat) := hPair p x hp
      _ ≤ ((p.length : Nat) : ENat) + (cLength : ENat) + (cPair : ENat) := by
        gcongr
        exact hLength p
      _ = (k : ENat) + ((cLength + cPair : Nat) : ENat) := by
        simp only [hpLength, Nat.cast_add]
        simp [add_assoc, add_comm]
  have hkPairBound : kPair ≤ k + (cLength + cPair) := by exact_mod_cast hkPairBoundENat
  have hChainInst : k + kpCond ≤ kPair + logSlack cChain (kPair + 1) :=
    hChain x p k kpCond kPair hx hkpCond hkPair
  have hkpCondClose : kpCond ≤ logSlack cClose (k + 1) :=
    hClose k kpCond kPair hkPairBound hChainInst
  calc
    condK V p x = (kpCond : ENat) := hkpCond
    _ ≤ (logSlack cClose (k + 1) : ENat) := by exact_mod_cast hkpCondClose

end Kolmogorov
