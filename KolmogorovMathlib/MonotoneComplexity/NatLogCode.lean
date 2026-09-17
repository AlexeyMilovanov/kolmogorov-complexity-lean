import KolmogorovMathlib.Prefix.Encoding
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Primrec.List

import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity

/-!
# A self-delimiting code of logarithmic length

`natLogCode k` writes the length of the binary expansion of `k` in a self-delimiting code and
then the expansion itself, so its length is at most `2 log₂ (k + 1) + 3`
(`length_natLogCode_le`). It is uniquely decodable in the strong form needed for concatenation
(`natLogCode_append_inj`) and primitive recursive (`primrec_natLogCode`), which is what makes it
usable inside decompressors.
-/

namespace Kolmogorov

open Real

/-- The self-delimiting code of `k`: `natCode (Nat.bits k).length ++ Nat.bits k`
of length `≤ 2·log₂(k+1) + 3`. -/
def natLogCode (k : ℕ) : BitString := natCode (Nat.bits k).length ++ Nat.bits k

/-- The logarithmic self-delimiting code is uniquely decodable: a coded number followed by a payload
determines both. -/
lemma natLogCode_append_inj {k l : ℕ} {p q : BitString}
    (h : natLogCode k ++ p = natLogCode l ++ q) : k = l ∧ p = q := by
  dsimp [natLogCode] at h
  rw [List.append_assoc, List.append_assoc] at h
  have ⟨hlen, h2⟩ := natCode_append_inj h
  have ⟨hbits, hpq⟩ := List.append_inj h2 (by rw [hlen])
  have heq : k = l := natBits_injective hbits
  exact ⟨heq, hpq⟩

/-- The logarithmic self-delimiting code is primitive recursive. -/
lemma primrec_natLogCode : Primrec natLogCode := by
  have primrec_natCode : Primrec natCode := by
    exact Primrec.list_append.comp
      (Primrec.list_replicate.comp Primrec.id (Primrec.const true))
      (Primrec.const [false])
  exact Primrec.list_append.comp
    (primrec_natCode.comp (Primrec.list_length.comp primrec_natBits))
    primrec_natBits

/-- The logarithmic code of `k` has length at most `2 log₂ (k + 1) + 3`. -/
lemma length_natLogCode_le (k : ℕ) :
    ((natLogCode k).length : ℝ) ≤ 2 * Real.logb 2 (k + 1) + 3 := by
  dsimp [natLogCode]
  have hlen : ((natCode (Nat.bits k).length ++ Nat.bits k).length : ℝ)
      = 2 * (Nat.bits k).length + 1 := by
    simp [length_natCode]
    ring
  rw [hlen]
  have h1 := natBits_length_le_logb_add_one k
  by_cases hk : k = 0
  · subst hk
    simp [Nat.bits]
  · have hlog : Real.logb 2 k ≤ Real.logb 2 (k + 1) := by
      have hl1 : (1 : ℝ) < 2 := by norm_num
      have hl2 : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
      have hl3 : (0 : ℝ) < k + 1 := by positivity
      exact (Real.logb_le_logb hl1 hl2 hl3).mpr (by linarith)
    linarith

end Kolmogorov
