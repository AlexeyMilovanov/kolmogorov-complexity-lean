import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise

/-!
# Exact-budget corollaries

The exact-budget decompressor `conditionalPlainLengthDecompressor` and the
bound `KP_le_condK_given_plain_program_length` live in
`AlgorithmicStatistics/StrongModels/AddNoise.lean`; this module only adds the
two corollaries that turn an exact complexity value into a prefix-complexity
bound with a logarithmic surcharge.  (Both used to be duplicated here, which
made this module impossible to import together with the `KolmogorovMathlib`
aggregate.)
-/

namespace Kolmogorov
open scoped ENNReal

private theorem KP_le_condK_of_exact_budget
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : Nat, ∀ x y (k N : Nat),
      condK V x y = (k : ENat) →
      k ≤ N →
      KP U x y ≤
        ((k + C * (Nat.bits N).length + C : Nat) : ENat) := by
  obtain ⟨c_exact, h_exact⟩ := KP_le_condK_given_plain_program_length V U hV hU
  obtain ⟨c_rem, h_rem⟩ := KP_cond_remove_short_info U hU
  obtain ⟨c_len, h_len⟩ := KPPlain_le_two_mul_length U hU
  let C := c_len + c_exact + c_rem + 2
  refine ⟨C, fun x y k N hk hN => ?_⟩
  have h1 : KP U x (pairCode y (Nat.bits k)) ≤ ((k + c_exact : Nat) : ENat) := by
    exact_mod_cast h_exact x y k hk
  have h2 : KP U x y ≤ KP U x (pairCode y (Nat.bits k)) + KPPlain U (Nat.bits k) + (c_rem : ENat) :=
    h_rem x y (Nat.bits k)
  have h3 : KPPlain U (Nat.bits k) ≤ ((2 * (Nat.bits k).length + c_len : ℕ) : ENat) :=
    h_len (Nat.bits k)
  have h_bound :
      k + c_exact + (2 * (Nat.bits k).length + c_len) + c_rem
        ≤ k + C * (Nat.bits N).length + C := by
    have hk_len : (Nat.bits k).length ≤ (Nat.bits N).length := length_natBits_mono hN
    dsimp [C]
    nlinarith [Nat.zero_le (Nat.bits N).length, Nat.zero_le c_exact,
      Nat.zero_le c_len, Nat.zero_le c_rem]
  calc
    KP U x y ≤ KP U x (pairCode y (Nat.bits k)) + KPPlain U (Nat.bits k) + (c_rem : ENat) := h2
    _ ≤ ((k + c_exact : Nat) : ENat) + ((2 * (Nat.bits k).length + c_len : ℕ) : ENat)
          + (c_rem : ENat) := by gcongr
    _ = ((k + c_exact + (2 * (Nat.bits k).length + c_len) + c_rem : Nat) : ENat) := by
          push_cast; abel
    _ ≤ ((k + C * (Nat.bits N).length + C : Nat) : ENat) := by exact_mod_cast h_bound

private theorem KPPlain_le_plainK_of_exact_budget
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : Nat, ∀ x (k N : Nat),
      plainK V x = (k : ENat) →
      k ≤ N →
      KPPlain U x ≤
        ((k + C * (Nat.bits N).length + C : Nat) : ENat) := by
  obtain ⟨C, hC⟩ := KP_le_condK_of_exact_budget V U hV hU
  use C
  intro x k N hk hN
  exact hC x [] k N hk hN

end Kolmogorov
