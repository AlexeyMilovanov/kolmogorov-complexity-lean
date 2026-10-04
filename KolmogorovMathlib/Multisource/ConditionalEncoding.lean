/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Multisource.ConditionalEncoding.TwoNode
import KolmogorovMathlib.Multisource.ConditionalEncoding.ProgramCount

/-!
# The two-node request and conditional encoding

The criterion of SUV Section 12.1 for the simplest request (one channel of capacity `k` from
an input node holding `A` to an output node that must produce `B`) and the criterion of
Section 12.2 for the request of Figure 39 (encoder and decoder both know `B`, the channel from
the encoder to the decoder has capacity `k`).

Both are statements about *sequences* of strings, because the precision `O(log n)` is only
meaningful along a sequence; following the book, the lengths and the capacities are required
to be polynomially bounded in the index.  Fulfilment is spelled out directly in terms of the
strings written on the one bounded channel rather than through `IsFulfilled`, exactly as the
book does on p. 368.

The two requests are also written as `InformationRequest`s (`twoNodeRequest`,
`conditionalEncodingRequest`), together with the cuts that give their conditions (part of
Problem 327).

Complexity is plain `C` throughout.

SUV Sections 12.1 and 12.2, pp. 368–369.

This file holds the conditional encoding criterion (Problem 318) and its request; the two-node
request is in `Multisource/ConditionalEncoding/TwoNode.lean`, and the bounds on conditional
shortest descriptions that the criterion uses (Problem 317) are in
`Multisource/ConditionalEncoding/ShortestDescription.lean` and
`Multisource/ConditionalEncoding/ProgramCount.lean`.
-/

namespace Kolmogorov

/-- A message `X` together with a program that decodes `A` from `B` and `X` describes `A`
given `B`: `C(A|B) ≤ l(X) + 2 C(A|B,X) + O(1)`.  The (short) program is stored in the unary
header of `pairCode`, the message in its payload. -/
private theorem condK_le_length_add_two_mul_condK_pair (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A B X : BitString) (e : ℕ), condK D A (pairCode B X) ≤ (e : ℕ∞) →
      condK D A B ≤ (X.length : ℕ∞) + ((2 * e + c : ℕ) : ℕ∞) := by
  let E : Map := fun pr => D (decodeFirst pr.1, pairCode pr.2 (decodeSecond pr.1))
  have hArg : Computable (fun pr : BitString × BitString =>
      (decodeFirst pr.1, pairCode pr.2 (decodeSecond pr.1))) :=
    ((decodeFirst_computable.comp Computable.fst).pair
      (pairCode_computable.comp
        (Computable.snd.pair (decodeSecond_computable.comp Computable.fst)))).of_eq
      (fun _ => rfl)
  have hE : isDecompressor E := Partrec.comp hD.1 hArg
  obtain ⟨C, hC⟩ := hD.2 E hE
  refine ⟨C + 1, fun A B X e hAX => ?_⟩
  obtain ⟨q, hqLen, hq⟩ := (condK_le_iff D A (pairCode B X) e).mp hAX
  change q.length ≤ e at hqLen
  change A ∈ D (q, pairCode B X) at hq
  have hprod : produces E (pairCode q X) B A := by
    change A ∈ D (decodeFirst (pairCode q X), pairCode B (decodeSecond (pairCode q X)))
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    exact hq
  calc
    condK D A B ≤ condK E A B + (C : ℕ∞) := hC A B
    _ ≤ ((pairCode q X).length : ℕ∞) + (C : ℕ∞) := by
      gcongr
      exact sInf_le ⟨pairCode q X, hprod, rfl⟩
    _ ≤ (X.length : ℕ∞) + ((2 * e + (C + 1) : ℕ) : ℕ∞) := by
      rw [length_pairCode]
      exact_mod_cast (show q.length + 1 + q.length + X.length + C ≤
        X.length + (2 * e + (C + 1)) by omega)

/-- The decoder of Figure 39 needs only `O(1)` advice: if `D(X, B) = A`, then
`C(A | B, X) = O(1)`. -/
private theorem condK_given_pair_of_produces (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ A B X : BitString, produces D X B A →
      condK D A (pairCode B X) ≤ (c : ℕ∞) := by
  let E : Map := fun pr => D (decodeSecond pr.2, decodeFirst pr.2)
  have hE : isDecompressor E :=
    Partrec.comp hD.1 ((decodeSecond_computable.comp Computable.snd).pair
      (decodeFirst_computable.comp Computable.snd))
  obtain ⟨C, hC⟩ := hD.2 E hE
  refine ⟨C, fun A B X hX => ?_⟩
  have hprod : produces E [] (pairCode B X) A := by
    change A ∈ D (decodeSecond (pairCode B X), decodeFirst (pairCode B X))
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    exact hX
  calc
    condK D A (pairCode B X) ≤ condK E A (pairCode B X) + (C : ℕ∞) := hC A (pairCode B X)
    _ ≤ ((([] : BitString).length : ℕ) : ℕ∞) + (C : ℕ∞) := by
      gcongr
      exact sInf_le ⟨[], hprod, rfl⟩
    _ = (C : ℕ∞) := by simp

/-- The length of the pair code of two polynomially bounded sequences, plus a constant, is
polynomially bounded. -/
private theorem hasPolynomialBound_pairCode_length {A B : ℕ → BitString}
    (hA : HasPolynomialBound fun n => (A n).length)
    (hB : HasPolynomialBound fun n => (B n).length) (cL : ℕ) :
    HasPolynomialBound fun n => (pairCode (A n) (B n)).length + cL := by
  obtain ⟨CA, dA, hCA⟩ := hA
  obtain ⟨CB, dB, hCB⟩ := hB
  refine ⟨2 * CA + CB + 1 + cL, dA + dB, fun n => ?_⟩
  have hpA : (n + 1) ^ dA ≤ (n + 1) ^ (dA + dB) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpB : (n + 1) ^ dB ≤ (n + 1) ^ (dA + dB) := Nat.pow_le_pow_right (by omega) (by omega)
  have hone : 1 ≤ (n + 1) ^ (dA + dB) := Nat.one_le_pow _ _ (by omega)
  have h1 := hCA n
  have h2 := hCB n
  have hA' : CA * (n + 1) ^ dA ≤ CA * (n + 1) ^ (dA + dB) := Nat.mul_le_mul_left CA hpA
  have hB' : CB * (n + 1) ^ dB ≤ CB * (n + 1) ^ (dA + dB) := Nat.mul_le_mul_left CB hpB
  dsimp only at h1 h2 ⊢
  rw [length_pairCode]
  nlinarith

/-- The logarithm of the complexity `C(Aₙ, Bₙ)` of a polynomially bounded pair is `O(log n)`:
the slack `logSlack c (C(Aₙ,Bₙ) + 1)` is dominated by a slack in the index. -/
private theorem logSlack_pairComplexity_le (D : Map) (hD : isOptimalConditional D)
    {A B : ℕ → BitString}
    (hA : HasPolynomialBound fun n => (A n).length)
    (hB : HasPolynomialBound fun n => (B n).length) (cS : ℕ) :
    ∃ c' : ℕ, ∀ (n kAB : ℕ), HasPlainComplexityValue D (pairCode (A n) (B n)) kAB →
      logSlack cS (kAB + 1) ≤ logSlack c' n := by
  obtain ⟨cL, hL⟩ := plainK_le_length D hD
  obtain ⟨c', hc'⟩ :=
    logSlack_polynomialBound_add_logSlack_le (hasPolynomialBound_pairCode_length hA hB cL) cS 0
  refine ⟨c', fun n kAB hkAB => ?_⟩
  have hk : kAB ≤ (pairCode (A n) (B n)).length + cL := by
    have h : plainK D (pairCode (A n) (B n)) = (kAB : ℕ∞) := hkAB
    have hle : (kAB : ℕ∞) ≤ (((pairCode (A n) (B n)).length + cL : ℕ) : ℕ∞) := by
      rw [← h]; push_cast; exact hL (pairCode (A n) (B n))
    exact_mod_cast hle
  have hzero : logSlack 0 n = 0 := by unfold logSlack; simp
  have h := hc' n
  rw [hzero, add_zero] at h
  exact (logSlack_mono_right cS (by omega)).trans h

/-- The criterion for the conditional-encoding request of SUV Figure 39: the encoder knows
`Aₙ` and `Bₙ` and sends a message `Xₙ` of length at most `kₙ` down a bounded channel, the
decoder knows `Bₙ` and `Xₙ` and must produce `Aₙ`.  This is possible with logarithmic
precision if and only if `C(Aₙ|Bₙ) ≤ kₙ + O(log n)`.

SUV Problem 318, p. 369 ("give the exact statement … and prove it"). -/
theorem conditionalEncoding_criterion (D : Map) (hD : isOptimalConditional D)
    (A B : ℕ → BitString) (k : ℕ → ℕ)
    (hA : HasPolynomialBound fun n => (A n).length)
    (hB : HasPolynomialBound fun n => (B n).length)
    (hk : HasPolynomialBound k) :
    (∃ (c : ℕ) (X : ℕ → BitString), ∀ n : ℕ,
        (X n).length ≤ k n + logSlack c n ∧
        condK D (X n) (pairCode (A n) (B n)) ≤ (logSlack c n : ℕ∞) ∧
        condK D (A n) (pairCode (B n) (X n)) ≤ (logSlack c n : ℕ∞)) ↔
      (∃ c : ℕ, ∀ n : ℕ, condK D (A n) (B n) ≤ (k n : ℕ∞) + (logSlack c n : ℕ∞)) := by
  have _hk := hk
  obtain ⟨cM, hM⟩ := condK_le_length_add_two_mul_condK_pair D hD
  obtain ⟨cDec, hDec⟩ := condK_given_pair_of_produces D hD
  obtain ⟨c317, h317⟩ := condK_conditionalShortestDescription_le_log D hD
  obtain ⟨cPair, hPair⟩ := logSlack_pairComplexity_le D hD hA hB c317
  constructor
  · rintro ⟨c, X, hX⟩
    refine ⟨3 * c + cM, fun n => ?_⟩
    obtain ⟨hlen, -, hAX⟩ := hX n
    refine (hM (A n) (B n) (X n) (logSlack c n) hAX).trans ?_
    have hsum : (X n).length + (2 * logSlack c n + cM) ≤ k n + logSlack (3 * c + cM) n := by
      have hslack : 3 * logSlack c n + cM ≤ logSlack (3 * c + cM) n := by
        unfold logSlack
        nlinarith [Nat.zero_le (cM * (Nat.bits n).length)]
      omega
    calc
      ((X n).length : ℕ∞) + ((2 * logSlack c n + cM : ℕ) : ℕ∞)
          = (((X n).length + (2 * logSlack c n + cM) : ℕ) : ℕ∞) := by push_cast; rfl
      _ ≤ ((k n + logSlack (3 * c + cM) n : ℕ) : ℕ∞) := by exact_mod_cast hsum
      _ = (k n : ℕ∞) + (logSlack (3 * c + cM) n : ℕ∞) := by push_cast; rfl
  · rintro ⟨c, hc⟩
    have hchoice : ∀ n, ∃ X : BitString, X.length ≤ k n + logSlack c n ∧
        condK D X (pairCode (A n) (B n)) ≤ (logSlack cPair n : ℕ∞) ∧
        condK D (A n) (pairCode (B n) X) ≤ (cDec : ℕ∞) := by
      intro n
      obtain ⟨kA, hkA⟩ := exists_plainConditionalComplexityValue D hD (A n) (B n)
      obtain ⟨X, hXprod, hXlen⟩ := hkA.exists_program
      obtain ⟨kAB, hkAB⟩ := exists_plainComplexityValue D hD (pairCode (A n) (B n))
      refine ⟨X, ?_, ?_, hDec (A n) (B n) X hXprod⟩
      · have h : condK D (A n) (B n) = (kA : ℕ∞) := hkA
        have hle : (kA : ℕ∞) ≤ ((k n + logSlack c n : ℕ) : ℕ∞) := by
          rw [← h]; push_cast; exact hc n
        rw [hXlen]
        exact_mod_cast hle
      · exact (h317 (A n) (B n) X kA kAB hkA hXprod hXlen hkAB).trans
          (by exact_mod_cast hPair n kAB hkAB)
    choose X hX using hchoice
    refine ⟨c + cPair + cDec, X, fun n => ?_⟩
    obtain ⟨hlen, hXAB, hAX⟩ := hX n
    refine ⟨hlen.trans (Nat.add_le_add_left (logSlack_mono_left (by omega) n) _),
      hXAB.trans (by exact_mod_cast logSlack_mono_left (by omega) n), hAX.trans ?_⟩
    exact_mod_cast (le_add_left (by omega : cDec ≤ c + cPair + cDec) :
      cDec ≤ (c + cPair + cDec) * (Nat.bits n).length + (c + cPair + cDec))

/-- The request of SUV Figure 39 on three nodes: the encoder `0` holds `A` and receives `B`
from the node `1` through an unlimited channel, the channel `0 → 2` has capacity `k`, the
decoder `2` also receives `B` through an unlimited channel and must produce `A`.

SUV Figure 39, p. 369. -/
def conditionalEncodingRequest (A B : BitString) (k : ℕ) : InformationRequest (Fin 3) where
  edges := {(1, 0), (0, 2), (1, 2)}
  rank v := if v.val = 1 then 0 else if v.val = 0 then 1 else 2
  rank_lt := by decide +kernel
  capacity e := if e = (0, 2) then (k : ℕ∞) else ⊤
  input v := if v = 0 then some A else if v = 1 then some B else none
  output v := if v = 2 then some A else none

/-- The cut of SUV Figure 39 that contains the node of `B` and the decoder: only the channel of
capacity `k` enters it, its input is `B` and its output is `A`, which gives the condition
`C(A|B) ≤ k` of `conditionalEncoding_criterion`.

SUV Problem 327, p. 384. -/
theorem conditionalEncodingRequest_cut (A B : BitString) (k : ℕ) :
    (conditionalEncodingRequest A B k).cutCapacity {1, 2} = (k : ℕ∞) ∧
      (conditionalEncodingRequest A B k).cutInputs {1, 2} = [B] ∧
      (conditionalEncodingRequest A B k).cutOutputs {1, 2} = [A] := by
  have hsort : ({1, 2} : Finset (Fin 3)).sort (· ≤ ·) = [1, 2] := by
    rw [Finset.sort_insert (r := (· ≤ ·)), Finset.sort_singleton]
    · simp
    · decide
  have hcut : (conditionalEncodingRequest A B k).cutEdges {1, 2} = {(0, 2)} := by
    ext e
    simp [InformationRequest.cutEdges, conditionalEncodingRequest]
    aesop
  rw [show (conditionalEncodingRequest A B k).cutCapacity {1, 2} = (k : ℕ∞) by
    rw [InformationRequest.cutCapacity, hcut]
    simp [conditionalEncodingRequest]]
  simp [InformationRequest.cutInputs, InformationRequest.cutOutputs,
    conditionalEncodingRequest, hsort]

end Kolmogorov
