import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.Encoding.Tuples

namespace Kolmogorov
open scoped ENNReal

/-- Run the ordinary conditional decompressor `V`, but accept only programs
whose length is encoded in the second component of the context.  For every
fixed context all halting programs therefore have the same length. -/
def conditionalPlainLengthDecompressor (V : Map) : Map := fun pr =>
  bif (pr.1.length == decodeBits (decodeSecond pr.2))
    then V (pr.1, decodeFirst pr.2)
    else Part.none

/-- The fixed-length wrapper remains a partial recursive decompressor. -/
theorem conditionalPlainLengthDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (conditionalPlainLengthDecompressor V) := by
  unfold conditionalPlainLengthDecompressor isDecompressor
  have hcond : Computable (fun (pr : BitString × BitString) =>
      pr.1.length == decodeBits (decodeSecond pr.2)) := by
    apply Primrec.to_comp
    apply Primrec₂.comp Primrec.beq
    · apply Primrec.list_length.comp Primrec.fst
    · apply primrecDecodeBits.comp (decodeSecond_primrec'.comp Primrec.snd)
  have hbody : Partrec (fun (pr : BitString × BitString) => V (pr.1, decodeFirst pr.2)) := by
    apply hV.comp
    apply Computable.pair
    · exact Computable.fst
    · apply Primrec.to_comp (decodeFirst_primrec'.comp Primrec.snd)
  exact Partrec.cond hcond hbody Partrec.none

/-- At each context, the fixed-length wrapper has prefix-free domain. -/
theorem conditionalPlainLengthDecompressor_isPrefixMachine
    (V : Map) :
    IsPrefixMachine (conditionalPlainLengthDecompressor V) := by
  intro y p hp q hq hpre
  unfold domainAt conditionalPlainLengthDecompressor at hp hq
  dsimp at hp hq
  have hp_cond : p.length == decodeBits (decodeSecond y) := by
    cases h : p.length == decodeBits (decodeSecond y)
    · rw [h] at hp; change False at hp; exact False.elim hp
    · rfl
  have hq_cond : q.length == decodeBits (decodeSecond y) := by
    cases h : q.length == decodeBits (decodeSecond y)
    · rw [h] at hq; change False at hq; exact False.elim hq
    · rfl
  have hlen : p.length = q.length := by
    have h1 := beq_iff_eq.mp hp_cond
    have h2 := beq_iff_eq.mp hq_cond
    omega
  exact hpre.eq_of_length hlen

/-- A `V`-program is accepted when its exact length is supplied in the
context. -/
theorem conditionalPlainLengthDecompressor_produces
    {V : Map} {p y x : BitString} {k : Nat}
    (hprod : produces V p y x) (hlen : p.length = k) :
    produces (conditionalPlainLengthDecompressor V) p
      (pairCode y (Nat.bits k)) x := by
  unfold produces conditionalPlainLengthDecompressor
  dsimp
  have hlen' : p.length == decodeBits (decodeSecond (pairCode y (Nat.bits k))) := by
    rw [decodeSecond_pairCode, decodeBits_natBits, hlen]
    exact beq_self_eq_true k
  rw [hlen', cond_true, decodeFirst_pairCode]
  exact hprod

/-- Exact conditional plain complexity becomes an upper bound for conditional
prefix complexity when that exact program length is included in the context.
The additive constant is uniform in the strings and in the complexity value. -/
theorem KP_le_condK_given_plain_program_length
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (k : Nat),
      condK V x y = (k : ENat) →
      KP U x (pairCode y (Nat.bits k)) ≤ (k + c : Nat) := by
  have hM : IsPrefixDecompressor (conditionalPlainLengthDecompressor V) :=
    ⟨conditionalPlainLengthDecompressor_partrec V hV.1,
      conditionalPlainLengthDecompressor_isPrefixMachine V⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, ?_⟩
  intro x y k hk
  have hfinite : KP V x y ≠ ⊤ := by
    rw [KP_eq_condK, hk]
    exact ENat.coe_ne_top k
  obtain ⟨p, hp, hpLen⟩ :=
    exists_program_of_KP_ne_top (M := V) (x := x) (y := y) hfinite
  have hpLenNat : p.length = k := by
    have : (p.length : ENat) = (k : ENat) := by
      rw [hpLen, KP_eq_condK, hk]
    exact_mod_cast this
  have hpWrapped : produces (conditionalPlainLengthDecompressor V) p
      (pairCode y (Nat.bits k)) x :=
    conditionalPlainLengthDecompressor_produces hp hpLenNat
  calc
    KP U x (pairCode y (Nat.bits k))
        ≤ KP (conditionalPlainLengthDecompressor V) x
            (pairCode y (Nat.bits k)) + (c : ENat) :=
          hc x (pairCode y (Nat.bits k))
    _ ≤ (p.length : ENat) + (c : ENat) := by
          gcongr
          exact KP_le_programLength_of_produces hpWrapped
    _ = (k + c : Nat) := by
          rw [hpLenNat]
          norm_cast

theorem KP_le_condK_of_exact_budget
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

theorem KPPlain_le_plainK_of_exact_budget
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
