import KolmogorovMathlib.CommonInformation.Definitions
import KolmogorovMathlib.CommonInformation.OverlapExtraction
import KolmogorovMathlib.CommonInformation.Splitting
import KolmogorovMathlib.Multisource.Requests
import KolmogorovMathlib.Foundation.ListUtil

/-!
# The two-node request

SUV Section 12.1, p. 368.

The criterion for the simplest request: one channel of capacity `k` from an input node holding
`A` to an output node that must produce `B` (`twoNode_transmission_criterion`).  The statement
is about sequences of strings whose lengths and capacities are polynomially bounded in the
index (`HasPolynomialBound`); fulfilment is spelled out directly through the string written on
the channel.  The request is also written as an `InformationRequest` (`twoNodeRequest`),
together with its cuts (`twoNodeRequest_cuts`, part of Problem 327).  The logarithmic-slack
estimate `logSlack_polynomialBound_add_logSlack_le` is shared with the conditional encoding
criterion.
-/

namespace Kolmogorov

/-- A sequence is polynomially bounded: `f n ≤ C (n+1)^d` for some constants.

SUV Section 12.1, p. 368 ("bounded by a polynomial in `n`"). -/
def HasPolynomialBound (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ n, f n ≤ C * (n + 1) ^ d

/-- A string is described by a message together with a program that decodes it from the
message: `C(B) ≤ l(X) + 2 C(B|X) + O(1)`.  The (short) program is stored in the unary
header of `pairCode`, the message in its payload. -/
private theorem plainK_le_length_add_two_mul_condK (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (B X : BitString) (e : ℕ), condK D B X ≤ (e : ℕ∞) →
      plainK D B ≤ (X.length : ℕ∞) + ((2 * e + c : ℕ) : ℕ∞) := by
  let E : Map := fun pr => D (decodeFirst pr.1, decodeSecond pr.1)
  have hE : isDecompressor E :=
    Partrec.comp hD.1 ((decodeFirst_computable.comp Computable.fst).pair
      (decodeSecond_computable.comp Computable.fst))
  obtain ⟨C, hC⟩ := hD.2 E hE
  refine ⟨C + 1, fun B X e hBX => ?_⟩
  obtain ⟨q, hqLen, hq⟩ := (condK_le_iff D B X e).mp hBX
  change q.length ≤ e at hqLen
  change B ∈ D (q, X) at hq
  have hprod : produces E (pairCode q X) [] B := by
    change B ∈ D (decodeFirst (pairCode q X), decodeSecond (pairCode q X))
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    exact hq
  calc
    plainK D B ≤ condK E B [] + (C : ℕ∞) := hC B []
    _ ≤ ((pairCode q X).length : ℕ∞) + (C : ℕ∞) := by
      gcongr
      exact sInf_le ⟨pairCode q X, hprod, rfl⟩
    _ ≤ (X.length : ℕ∞) + ((2 * e + (C + 1) : ℕ) : ℕ∞) := by
      rw [length_pairCode]
      exact_mod_cast (show q.length + 1 + q.length + X.length + C ≤
        X.length + (2 * e + (C + 1)) by omega)

private theorem twoNode_message_composition_bounds (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A B X : BitString) (e : ℕ),
      condK D X A ≤ (e : ℕ∞) → condK D B X ≤ (e : ℕ∞) →
      condK D B A ≤ ((3 * e + c : ℕ) : ℕ∞) ∧
        plainK D B ≤ (X.length : ℕ∞) + ((2 * e + c : ℕ) : ℕ∞) := by
  obtain ⟨cT, hT⟩ := condK_trans_visible_le D hD
  obtain ⟨cP, hP⟩ := plainK_le_length_add_two_mul_condK D hD
  refine ⟨cT + cP, fun A B X e hXA hBX => ⟨?_, ?_⟩⟩
  · exact (hT A X B e e hXA hBX).trans
      (by exact_mod_cast (show 2 * e + e + cT ≤ 3 * e + (cT + cP) by omega))
  · exact (hP B X e hBX).trans (by gcongr; omega)

/-- A shortest program `X` for `B` is the message of the sufficiency direction: it has length
`C(B) ≤ b`, it decodes to `B` with `O(1)` advice, and it is simple given `A` because
`C(X|A) ≤ 2 C(B|A) + C(X|B) + O(1)` and `C(X|B) = O(log C(B))` (SUV Theorem 221). -/
private theorem twoNode_shortest_program_bounds (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A B : BitString) (a b : ℕ),
      condK D B A ≤ (a : ℕ∞) → plainK D B ≤ (b : ℕ∞) →
      ∃ X : BitString,
        X.length ≤ b ∧
          condK D X A ≤ ((2 * a + logSlack c (b + 1) : ℕ) : ℕ∞) ∧
          condK D B X ≤ (c : ℕ∞) := by
  obtain ⟨cT, hT⟩ := condK_trans_visible_le D hD
  obtain ⟨cS, hS⟩ := condK_shortestDescription_le D hD
  let E : Map := fun pr => D (pr.2, [])
  have hE : isDecompressor E :=
    Partrec.comp hD.1 (Computable.snd.pair (Computable.const []))
  obtain ⟨cE, hcE⟩ := hD.2 E hE
  refine ⟨cT + cS + cE, fun A B a b hBA hB => ?_⟩
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD B
  obtain ⟨X, hXprod, hXlen⟩ := hkB.exists_program
  have hkBle : kB ≤ b := by
    have h : plainK D B = (kB : ℕ∞) := hkB
    have : (kB : ℕ∞) ≤ (b : ℕ∞) := by rw [← h]; exact hB
    exact_mod_cast this
  refine ⟨X, by rw [hXlen]; exact hkBle, ?_, ?_⟩
  · have hXB : condK D X B ≤ (logSlack cS (b + 1) : ℕ∞) :=
      (hS B X kB hkB hXprod hXlen).trans
        (by exact_mod_cast logSlack_mono_right cS (by omega))
    refine (hT A B X a _ hBA hXB).trans ?_
    have hslack : logSlack cS (b + 1) + cT ≤ logSlack (cT + cS + cE) (b + 1) := by
      unfold logSlack
      nlinarith [Nat.zero_le ((cT + cE) * (Nat.bits (b + 1)).length)]
    exact_mod_cast (show 2 * a + logSlack cS (b + 1) + cT ≤
      2 * a + logSlack (cT + cS + cE) (b + 1) by omega)
  · have hprod : produces E [] X B := by
      change B ∈ D (X, [])
      exact hXprod
    calc
      condK D B X ≤ condK E B X + (cE : ℕ∞) := hcE B X
      _ ≤ ((([] : BitString).length : ℕ) : ℕ∞) + (cE : ℕ∞) := by
        gcongr
        exact sInf_le ⟨[], hprod, rfl⟩
      _ = (cE : ℕ∞) := by simp
      _ ≤ ((cT + cS + cE : ℕ) : ℕ∞) := by exact_mod_cast (show cE ≤ cT + cS + cE by omega)

/-- The logarithmic slack at a polynomially bounded budget, shifted by a logarithmic slack in
the index, is again a logarithmic slack in the index: `log (kₙ + O(log n)) = O(log n)` when
`kₙ` is polynomial in `n`. -/
theorem logSlack_polynomialBound_add_logSlack_le {k : ℕ → ℕ}
    (hk : HasPolynomialBound k) (cS c : ℕ) :
    ∃ c' : ℕ, ∀ n, logSlack cS (k n + logSlack c n + 1) ≤ logSlack c' n := by
  obtain ⟨C, d, hC⟩ := hk
  obtain ⟨cOver, hOver⟩ :=
    polynomialOverhead_bits_le_logSlack (C + c + 1) (d + 1) (by omega)
  refine ⟨cS * cOver + cS, fun n => ?_⟩
  have hpow : (n + 1) ^ d ≤ (n + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hlin : n + 1 ≤ (n + 1) ^ (d + 1) := Nat.le_self_pow (by omega) (n + 1)
  have hm : k n + logSlack c n + 1 ≤ (C + c + 1) * (n + 1) ^ (d + 1) := by
    have h1 := hC n
    have h2 := logSlack_le_self_linear c n
    have hA : C * (n + 1) ^ d ≤ C * (n + 1) ^ (d + 1) := Nat.mul_le_mul_left C hpow
    have hB : c * (n + 1) ≤ c * (n + 1) ^ (d + 1) := Nat.mul_le_mul_left c hlin
    nlinarith
  have hbits : (Nat.bits (k n + logSlack c n + 1)).length ≤
      cOver * (Nat.bits n).length + cOver := by
    calc
      (Nat.bits (k n + logSlack c n + 1)).length = Nat.size (k n + logSlack c n + 1) :=
        Nat.size_eq_bits_len _
      _ ≤ Nat.size ((C + c + 1) * (n + 1) ^ (d + 1)) := Nat.size_le_size hm
      _ = (Nat.bits ((C + c + 1) * (n + 1) ^ (d + 1))).length :=
        (Nat.size_eq_bits_len _).symm
      _ ≤ logSlack cOver n := hOver n
  change cS * (Nat.bits (k n + logSlack c n + 1)).length + cS ≤
    (cS * cOver + cS) * (Nat.bits n).length + (cS * cOver + cS)
  nlinarith [hbits, Nat.zero_le (cS * (Nat.bits n).length)]

private theorem twoNode_messages_imply_conditions (D : Map)
    (hD : isOptimalConditional D) (A B : ℕ → BitString) (k : ℕ → ℕ)
    (_hA : HasPolynomialBound fun n => (A n).length)
    (_hB : HasPolynomialBound fun n => (B n).length)
    (_hk : HasPolynomialBound k) :
    (∃ (c : ℕ) (X : ℕ → BitString), ∀ n : ℕ,
        (X n).length ≤ k n + logSlack c n ∧
        condK D (X n) (A n) ≤ (logSlack c n : ℕ∞) ∧
        condK D (B n) (X n) ≤ (logSlack c n : ℕ∞)) →
      ∃ c : ℕ, ∀ n : ℕ,
        condK D (B n) (A n) ≤ (logSlack c n : ℕ∞) ∧
        plainK D (B n) ≤ (k n : ℕ∞) + (logSlack c n : ℕ∞) := by
  obtain ⟨cComp, hComp⟩ := twoNode_message_composition_bounds D hD
  rintro ⟨c, X, hX⟩
  refine ⟨3 * c + cComp, fun n => ?_⟩
  obtain ⟨hlen, hXA, hBX⟩ := hX n
  obtain ⟨hBA, hB⟩ := hComp (A n) (B n) (X n) (logSlack c n) hXA hBX
  have hslack : 3 * logSlack c n + cComp ≤ logSlack (3 * c + cComp) n := by
    unfold logSlack
    nlinarith [Nat.zero_le (cComp * (Nat.bits n).length)]
  refine ⟨hBA.trans (by exact_mod_cast hslack), ?_⟩
  calc
    plainK D (B n) ≤ ((X n).length : ℕ∞) + ((2 * logSlack c n + cComp : ℕ) : ℕ∞) := hB
    _ = (((X n).length + (2 * logSlack c n + cComp) : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ ((k n + logSlack (3 * c + cComp) n : ℕ) : ℕ∞) := by
      exact_mod_cast (show (X n).length + (2 * logSlack c n + cComp) ≤
        k n + logSlack (3 * c + cComp) n by omega)
    _ = (k n : ℕ∞) + (logSlack (3 * c + cComp) n : ℕ∞) := by push_cast; rfl

private theorem twoNode_conditions_imply_messages (D : Map)
    (hD : isOptimalConditional D) (A B : ℕ → BitString) (k : ℕ → ℕ)
    (_hA : HasPolynomialBound fun n => (A n).length)
    (_hB : HasPolynomialBound fun n => (B n).length)
    (hk : HasPolynomialBound k) :
    (∃ c : ℕ, ∀ n : ℕ,
        condK D (B n) (A n) ≤ (logSlack c n : ℕ∞) ∧
        plainK D (B n) ≤ (k n : ℕ∞) + (logSlack c n : ℕ∞)) →
      ∃ (c : ℕ) (X : ℕ → BitString), ∀ n : ℕ,
        (X n).length ≤ k n + logSlack c n ∧
        condK D (X n) (A n) ≤ (logSlack c n : ℕ∞) ∧
        condK D (B n) (X n) ≤ (logSlack c n : ℕ∞) := by
  obtain ⟨cShort, hShort⟩ := twoNode_shortest_program_bounds D hD
  rintro ⟨c, hc⟩
  obtain ⟨cP, hP⟩ := logSlack_polynomialBound_add_logSlack_le hk cShort c
  choose X hX using fun n =>
    hShort (A n) (B n) (logSlack c n) (k n + logSlack c n) (hc n).1
      (by push_cast; exact (hc n).2)
  refine ⟨2 * c + cP + cShort, X, fun n => ?_⟩
  obtain ⟨hlen, hXA, hBX⟩ := hX n
  refine ⟨hlen.trans (Nat.add_le_add_left (logSlack_mono_left (by omega) n) _), ?_, ?_⟩
  · refine hXA.trans ?_
    have h1 := logSlack_add_constants (c + c) cP n
    have h2 := logSlack_add_constants c c n
    have h3 : logSlack (c + c + cP) n ≤ logSlack (2 * c + cP + cShort) n :=
      logSlack_mono_left (by omega) n
    have h4 := hP n
    exact_mod_cast (show 2 * logSlack c n + logSlack cShort (k n + logSlack c n + 1) ≤
      logSlack (2 * c + cP + cShort) n by omega)
  · refine hBX.trans ?_
    exact_mod_cast (le_add_left (by omega : cShort ≤ 2 * c + cP + cShort) :
      cShort ≤ (2 * c + cP + cShort) * (Nat.bits n).length + (2 * c + cP + cShort))

/-- The criterion for the two-node request of SUV Figure 38.  For polynomially bounded data,
transmitting `Bₙ` from `Aₙ` through a channel of capacity `kₙ` is possible (a sequence `Xₙ`
of messages with `l(Xₙ) ≤ kₙ + O(log n)`, `C(Xₙ|Aₙ) = O(log n)` and `C(Bₙ|Xₙ) = O(log n)`)
if and only if `C(Bₙ|Aₙ) = O(log n)` and `C(Bₙ) ≤ kₙ + O(log n)`.

The book writes "for every `A`, `B` and `k` there exists a string `X`" in the proof of the
second implication, where `k` plays no role.

SUV Section 12.1, p. 368 (unnumbered criterion). -/
theorem twoNode_transmission_criterion (D : Map) (hD : isOptimalConditional D)
    (A B : ℕ → BitString) (k : ℕ → ℕ)
    (hA : HasPolynomialBound fun n => (A n).length)
    (hB : HasPolynomialBound fun n => (B n).length)
    (hk : HasPolynomialBound k) :
    (∃ (c : ℕ) (X : ℕ → BitString), ∀ n : ℕ,
        (X n).length ≤ k n + logSlack c n ∧
        condK D (X n) (A n) ≤ (logSlack c n : ℕ∞) ∧
        condK D (B n) (X n) ≤ (logSlack c n : ℕ∞)) ↔
      (∃ c : ℕ, ∀ n : ℕ,
        condK D (B n) (A n) ≤ (logSlack c n : ℕ∞) ∧
        plainK D (B n) ≤ (k n : ℕ∞) + (logSlack c n : ℕ∞)) := by
  constructor
  · exact twoNode_messages_imply_conditions D hD A B k hA hB hk
  · exact twoNode_conditions_imply_messages D hD A B k hA hB hk

/-- The request of SUV Figure 38 on two nodes: `0` holds `A`, the channel `0 → 1` has
capacity `k`, and `1` must produce `B`.

SUV Figure 38, p. 368. -/
def twoNodeRequest (A B : BitString) (k : ℕ) : InformationRequest (Fin 2) where
  edges := {(0, 1)}
  rank v := v.val
  rank_lt := by decide +kernel
  capacity e := if e = (0, 1) then (k : ℕ∞) else ⊤
  input v := if v = 0 then some A else none
  output v := if v = 1 then some B else none

/-- The two cuts of SUV Figure 38.  The cut `{1}` is entered by the channel of capacity `k`
and contains the output `B` and no input, which gives `C(B) ≤ k`; the cut `{0, 1}` is entered
by no channel and contains the input `A` and the output `B`, which gives `C(B|A) ≈ 0`.  These
are the two conditions of the criterion `twoNode_transmission_criterion`.

SUV Problem 327, p. 384. -/
theorem twoNodeRequest_cuts (A B : BitString) (k : ℕ) :
    ((twoNodeRequest A B k).cutCapacity {1} = (k : ℕ∞) ∧
      (twoNodeRequest A B k).cutInputs {1} = [] ∧
      (twoNodeRequest A B k).cutOutputs {1} = [B]) ∧
    ((twoNodeRequest A B k).cutCapacity {0, 1} = 0 ∧
      (twoNodeRequest A B k).cutInputs {0, 1} = [A] ∧
      (twoNodeRequest A B k).cutOutputs {0, 1} = [B]) := by
  have hsort : ({0, 1} : Finset (Fin 2)).sort (· ≤ ·) = [0, 1] := by
    rw [Finset.sort_insert (r := (· ≤ ·)), Finset.sort_singleton]
    · simp
    · decide
  have hcutOne : (twoNodeRequest A B k).cutEdges {1} = {(0, 1)} := by
    ext e
    simp [InformationRequest.cutEdges, twoNodeRequest]
    aesop
  have hcutFull : (twoNodeRequest A B k).cutEdges {0, 1} = ∅ := by
    ext e
    simp [InformationRequest.cutEdges, twoNodeRequest]
    aesop
  rw [show (twoNodeRequest A B k).cutCapacity {1} = (k : ℕ∞) by
    rw [InformationRequest.cutCapacity, hcutOne]
    simp [twoNodeRequest]]
  rw [show (twoNodeRequest A B k).cutCapacity {0, 1} = 0 by
    rw [InformationRequest.cutCapacity, hcutFull]
    simp]
  simp [InformationRequest.cutInputs, InformationRequest.cutOutputs, twoNodeRequest,
    hsort, Finset.sort_singleton]

end Kolmogorov
