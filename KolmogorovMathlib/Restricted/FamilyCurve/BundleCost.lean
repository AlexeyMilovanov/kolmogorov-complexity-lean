import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Encoding.TuplesComplexity

/-!
# The cost of a decoder bundle field by field

A model of the anchored run is described by a bundle of four code words: the encoded curve
grid, the covering overhead of the family, the scale index and the version ordinal.  Every
field except the grid is written self-delimited, so its cost is its binary length plus twice
the binary length of that length.

This module bounds each of those field costs by a square-root slack `sqrtSlack c n`, adds the
four bounds up in `decoderBundleFieldCost_le`, and turns that ℕ-level budget into the plain
bound `KPPlain_le_grid_add_bundleCost` on the decoder output.  The bundle-cost lemmas of the
mixed-family and restricted-family assemblies are then a one-line application of these facts.
-/

namespace Kolmogorov

/-- `sqrtSlack` is literally a multiple of `√(n·len n) + 1`. -/
lemma sqrtSlack_eq_mul (m n : ℕ) :
    sqrtSlack m n = m * (Nat.sqrt (n * (Nat.bits n).length) + 1) := by
  unfold sqrtSlack
  ring

/-- The binary length of `n` is at most `√(n · len n)`: it is at most `n` itself. -/
lemma bits_length_le_sqrt_mul (n : ℕ) :
    (Nat.bits n).length ≤ Nat.sqrt (n * (Nat.bits n).length) := by
  refine Nat.le_sqrt.mpr ?_
  have hLn : (Nat.bits n).length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  exact Nat.mul_le_mul_right _ hLn

/-- The covering overhead of a family at the ambient budget has binary length inside the
square-root slack with constant `5 * c_over`. -/
lemma bits_length_overhead_le_sqrtSlack (𝒜 : DescriptionFamily) {c_over : ℕ} (n : ℕ)
    (hover : ∀ m, (Nat.bits (𝒜.overhead m)).length ≤ logSlack c_over m) :
    (Nat.bits (𝒜.overhead (n + logSlack 8 n))).length ≤ sqrtSlack (5 * c_over) n := by
  have hL := bits_length_le_sqrt_mul n
  have h0 : (Nat.bits (𝒜.overhead (n + logSlack 8 n))).length ≤
      c_over * ((Nat.bits n).length + 4) + c_over := by
    refine (hover (n + logSlack 8 n)).trans ?_
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left c_over (bits_length_ambient_le n)) c_over
  rw [sqrtSlack_eq_mul]
  set S := Nat.sqrt (n * (Nat.bits n).length)
  have h1 : (Nat.bits n).length + 4 ≤ 4 * (S + 1) := by omega
  have h2 : c_over * ((Nat.bits n).length + 4) ≤ c_over * (4 * (S + 1)) :=
    Nat.mul_le_mul_left c_over h1
  have h3 : c_over ≤ c_over * (S + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : c_over * (4 * (S + 1)) + c_over * (S + 1) = 5 * c_over * (S + 1) := by ring
  omega

/-- A scale index of at most `n + 1` has binary length inside the unit square-root slack. -/
lemma bits_length_le_sqrtSlack_one {s n : ℕ} (hs : s ≤ n + 1) :
    (Nat.bits s).length ≤ sqrtSlack 1 n := by
  have hn2 : n < 2 ^ (Nat.bits n).length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.lt_size_self n
  have hsbits : (Nat.bits s).length ≤ (Nat.bits n).length + 1 := by
    rw [Nat.size_eq_bits_len]
    refine Nat.size_le.mpr ?_
    have hpow1 : (2 : ℕ) ^ ((Nat.bits n).length + 1) = 2 * 2 ^ (Nat.bits n).length := by
      rw [pow_add]
      ring
    omega
  have hL := bits_length_le_sqrt_mul n
  rw [sqrtSlack_eq_mul]
  omega

/-- A version ordinal below `2 ^ e` has binary length at most `e + 1`. -/
lemma bits_length_le_of_le_two_pow {v e : ℕ} (hv : v ≤ 2 ^ e) :
    (Nat.bits v).length ≤ e + 1 := by
  rw [Nat.size_eq_bits_len]
  refine Nat.size_le.mpr ?_
  exact hv.trans_lt (Nat.pow_lt_pow_right (by omega) (by omega))

/-- The *double* logarithm of a version ordinal whose binary length is at most
`n + sqrtSlack c_P n + 1` is inside the square-root slack with constant
`Nat.size (c_P + 1) + 4`. -/
lemma bits_length_bits_length_le_sqrtSlack {v n c_P : ℕ}
    (hv : (Nat.bits v).length ≤ n + sqrtSlack c_P n + 1) :
    (Nat.bits (Nat.bits v).length).length ≤ sqrtSlack (Nat.size (c_P + 1) + 4) n := by
  set L := (Nat.bits n).length with hLdef
  set S := Nat.sqrt (n * L) with hSdef
  have hn2 : n < 2 ^ L := by
    rw [hLdef, Nat.size_eq_bits_len]
    exact Nat.lt_size_self n
  have hLS : L ≤ S := bits_length_le_sqrt_mul n
  have hprod : n + sqrtSlack c_P n + 1 ≤ (c_P + 1) * ((n + 1) * (L + 1)) := by
    have hSn : S + 1 ≤ (n + 1) * (L + 1) := by
      have hSle : S ≤ n * L := by
        have := Nat.sqrt_le_self (n * L)
        omega
      have h : (n + 1) * (L + 1) = n * L + n + L + 1 := by ring
      omega
    have h1 : sqrtSlack c_P n ≤ c_P * ((n + 1) * (L + 1)) := by
      rw [sqrtSlack_eq_mul, ← hLdef, ← hSdef]
      exact Nat.mul_le_mul_left c_P hSn
    have h2 : n + 1 ≤ (n + 1) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : (c_P + 1) * ((n + 1) * (L + 1)) =
        (n + 1) * (L + 1) + c_P * ((n + 1) * (L + 1)) := by ring
    omega
  have hdlog : (Nat.bits (Nat.bits v).length).length ≤
      Nat.size (c_P + 1) + (L + 1) + (L + 1) + 2 := by
    rw [Nat.size_eq_bits_len]
    refine (Nat.size_le_size (hv.trans hprod)).trans ?_
    have h1 := size_mul_le (c_P + 1) ((n + 1) * (L + 1))
    have h2 := size_mul_le (n + 1) (L + 1)
    have h3 : Nat.size (n + 1) ≤ L + 1 := by
      refine Nat.size_le.mpr ?_
      have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by
        rw [pow_add]
        ring
      omega
    have h4 : Nat.size (L + 1) ≤ L + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  rw [sqrtSlack_eq_mul, ← hLdef, ← hSdef]
  have h1 : Nat.size (c_P + 1) ≤ Nat.size (c_P + 1) * (S + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have e : (Nat.size (c_P + 1) + 4) * (S + 1) =
      Nat.size (c_P + 1) * (S + 1) + 4 * (S + 1) := by ring
  omega

/-- The three self-delimited fields of a decoder bundle — overhead, scale index and version
ordinal — together with the list and final-machine constants, cost at most the grid coordinate
plus a single square-root slack. -/
lemma decoderBundleCost_sum_le {n i q0 q0d s0 s0d v0 v0d : ℕ} (c_over c_P c_lg c_L c_F : ℕ)
    (hq0 : q0 ≤ sqrtSlack (5 * c_over) n) (hq0d : q0d ≤ sqrtSlack (5 * c_over) n)
    (hs0 : s0 ≤ sqrtSlack 1 n) (hs0d : s0d ≤ sqrtSlack 1 n)
    (hv0 : v0 ≤ i + sqrtSlack c_P n + 1)
    (hv0d : v0d ≤ sqrtSlack (Nat.size (c_P + 1) + 4) n) :
    (q0 + 2 * q0d + c_lg) + (s0 + 2 * s0d + c_lg) + (v0 + 2 * v0d + c_lg) +
        c_L * 5 + c_F ≤
      i + sqrtSlack (c_P + 15 * c_over + 3 * c_lg + 5 * c_L + c_F +
        2 * Nat.size (c_P + 1) + 40) n := by
  rw [sqrtSlack_eq_mul] at hq0 hq0d hs0 hs0d hv0 hv0d ⊢
  set T := Nat.sqrt (n * (Nat.bits n).length) + 1 with hT
  have hTpos : 1 ≤ T := by omega
  have hlg : c_lg ≤ c_lg * T := Nat.le_mul_of_pos_right _ (by omega)
  have hL5 : c_L * 5 ≤ 5 * c_L * T := by
    have h : c_L * 5 ≤ c_L * 5 * T := Nat.le_mul_of_pos_right _ (by omega)
    have e : c_L * 5 * T = 5 * c_L * T := by ring
    omega
  have hF : c_F ≤ c_F * T := Nat.le_mul_of_pos_right _ (by omega)
  have hexpand : (c_P + 15 * c_over + 3 * c_lg + 5 * c_L + c_F +
      2 * Nat.size (c_P + 1) + 40) * T =
      c_P * T + 15 * c_over * T + 3 * (c_lg * T) + 5 * c_L * T + c_F * T +
        2 * (Nat.size (c_P + 1) * T) + 40 * T := by ring
  have hq : 5 * c_over * T + 2 * (5 * c_over * T) = 15 * c_over * T := by ring
  have hv : 2 * ((Nat.size (c_P + 1) + 4) * T) =
      2 * (Nat.size (c_P + 1) * T) + 8 * T := by ring
  have h1 : 1 * T = T := by ring
  omega

/-- The cost of describing a code word in self-delimited form: its length, plus twice the
length of the binary expansion of that length (the self-delimiting prefix), plus the constant
`c_lg` of the machine that reads it. -/
def selfDelimitedCost (c_lg : ℕ) (x : BitString) : ℕ :=
  x.length + 2 * (Nat.bits x.length).length + c_lg

/-- A code word costs at most `selfDelimitedCost c_lg` plain bits, once `c_lg` is the constant
supplied by `KPPlain_le_length_add_log`. -/
lemma KPPlain_le_selfDelimitedCost {U : Map} {c_lg : ℕ}
    (hlg : ∀ x : BitString,
      KPPlain U x ≤ x.length + 2 * (Nat.bits x.length).length + (c_lg : ENat))
    (x : BitString) :
    KPPlain U x ≤ ((selfDelimitedCost c_lg x : ℕ) : ENat) := by
  have h := hlg x
  unfold selfDelimitedCost
  push_cast
  exact h

/-- The set complexity of a live set is the plain complexity of the canonical uniform code of
any set equal to it. -/
lemma setComplexity_eq_KPPlain_codedUniformOn (U : Map) {S T : Finset BitString}
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S = T) :
    setComplexity U S hS = KPPlain U (codedUniformOn T hT).code := by
  unfold setComplexity
  congr 1
  exact codedUniformOn_code_congr hS hT hST

/-- **The ℕ-level cost budget of a decoder bundle.**  Along an anchored run over any
description family, the three self-delimited fields of the bundle — the covering overhead at
the ambient budget, the scale index `s`, the version ordinal `v` — together with the list and
final-machine constants cost at most the grid coordinate `grid.i s` plus a single square-root
slack whose constant depends only on the overhead and version-exponent constants.

Both the restricted-family and the mixed-family assemblies use exactly this bound; the family
`𝒜` it is stated for is the one whose overhead and version exponent are being paid for. -/
lemma decoderBundleFieldCost_le
    (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n)
    {c_over c_P : ℕ}
    (hover : ∀ m, (Nat.bits (𝒜.overhead m)).length ≤ logSlack c_over m)
    (hP : anchoredVersionExp 𝒜 n N ≤ sqrtSlack c_P n)
    {s v : ℕ} (hs : s ≤ N)
    (hv : v ≤ 2 ^ (grid.i s + anchoredVersionExp 𝒜 n N))
    (c_lg c_L c_F : ℕ) :
    ((Nat.bits (𝒜.overhead (n + logSlack 8 n))).length +
        2 * (Nat.bits (Nat.bits
          (𝒜.overhead (n + logSlack 8 n))).length).length + c_lg) +
      ((Nat.bits s).length + 2 * (Nat.bits (Nat.bits s).length).length +
        c_lg) +
      ((Nat.bits v).length + 2 * (Nat.bits (Nat.bits v).length).length +
        c_lg) + c_L * 5 + c_F ≤
    grid.i s +
      sqrtSlack (c_P + 15 * c_over + 3 * c_lg + 5 * c_L + c_F +
        2 * Nat.size (c_P + 1) + 40) n := by
  have hsn : s ≤ n + 1 := by
    have hNle : N ≤ n + 1 := by
      rw [hN]
      exact Nat.add_le_add_right
        ((Nat.sqrt_le_self _).trans (Nat.div_le_self n _)) 1
    omega
  have hisn : grid.i s ≤ n := (grid.i_le_k s hs).trans hkn
  have hq0 := bits_length_overhead_le_sqrtSlack 𝒜 n hover
  have hs0 := bits_length_le_sqrtSlack_one hsn
  have hvbits : (Nat.bits v).length ≤ grid.i s + anchoredVersionExp 𝒜 n N + 1 :=
    bits_length_le_of_le_two_pow hv
  have hv0 : (Nat.bits v).length ≤ grid.i s + sqrtSlack c_P n + 1 := by omega
  have hvlen : (Nat.bits v).length ≤ n + sqrtSlack c_P n + 1 := by omega
  exact decoderBundleCost_sum_le c_over c_P c_lg c_L c_F hq0
    ((length_natBits_le _).trans hq0) hs0 ((length_natBits_le _).trans hs0) hv0
    (bits_length_bits_length_le_sqrtSlack hvlen)

/-- **The plain cost of a decoder bundle.**  A code word `code` that the final machine produces
from the four-field list `[grid_code, oh_code, s_code, v_code]` costs at most the grid
coordinate's own plain complexity plus `cost_bound`:
`KPPlain U code ≤ KPPlain U grid_code + cost_bound`.

The six hypotheses are exactly the inputs of that bound: `hKP1` prices the final machine that
reads the list, `hKP2` prices the list code against the sum of its fields, `hq0c`, `hsc` and
`hvc` price the three self-delimited fields — overhead, scale index and version ordinal — by
`selfDelimitedCost c_lg`, and `hNat` says that those three field costs together with the list
and final-machine constants fit inside `cost_bound`. -/
lemma KPPlain_le_grid_add_bundleCost
    (U : Map) (grid_code oh_code s_code v_code code : BitString)
    (c_lg c_L c_F cost_bound : ℕ)
    (hKP1 : KPPlain U code ≤
      KPPlain U (listCode [grid_code, oh_code, s_code, v_code]) + (c_F : ENat))
    (hKP2 : KPPlain U (listCode [grid_code, oh_code, s_code, v_code]) ≤
      (([grid_code, oh_code, s_code, v_code].map fun x => KPPlain U x).sum +
        ((c_L * 5 : ℕ) : ENat)))
    (hq0c : KPPlain U oh_code ≤ ((selfDelimitedCost c_lg oh_code : ℕ) : ENat))
    (hsc : KPPlain U s_code ≤ ((selfDelimitedCost c_lg s_code : ℕ) : ENat))
    (hvc : KPPlain U v_code ≤ ((selfDelimitedCost c_lg v_code : ℕ) : ENat))
    (hNat : selfDelimitedCost c_lg oh_code + selfDelimitedCost c_lg s_code +
      selfDelimitedCost c_lg v_code + c_L * 5 + c_F ≤ cost_bound) :
    KPPlain U code ≤ KPPlain U grid_code + ((cost_bound : ℕ) : ENat) := by
  simp only [selfDelimitedCost] at hq0c hsc hvc hNat
  have hsum :
      (([grid_code, oh_code, s_code, v_code].map fun x => KPPlain U x).sum) =
        KPPlain U grid_code + (KPPlain U oh_code + (KPPlain U s_code + KPPlain U v_code)) := by
    simp [List.sum_cons]
  have h1_cast : ((((oh_code.length + 2 * (Nat.bits oh_code.length).length + c_lg) +
        ((s_code.length + 2 * (Nat.bits s_code.length).length + c_lg) +
          (v_code.length + 2 * (Nat.bits v_code.length).length + c_lg)) +
        c_L * 5 + c_F : ℕ) : ENat)) ≤ ((cost_bound : ℕ) : ENat) := by
    exact_mod_cast (show (oh_code.length + 2 * (Nat.bits oh_code.length).length + c_lg) +
        ((s_code.length + 2 * (Nat.bits s_code.length).length + c_lg) +
          (v_code.length + 2 * (Nat.bits v_code.length).length + c_lg)) +
        c_L * 5 + c_F ≤ cost_bound by omega)
  have h1 : (KPPlain U oh_code + (KPPlain U s_code + KPPlain U v_code)) +
      ((c_L * 5 : ℕ) : ENat) + (c_F : ENat) ≤ ((cost_bound : ℕ) : ENat) := by
    calc
      (KPPlain U oh_code + (KPPlain U s_code + KPPlain U v_code)) +
          ((c_L * 5 : ℕ) : ENat) + (c_F : ENat)
          ≤ ((((oh_code.length + 2 * (Nat.bits oh_code.length).length + c_lg : ℕ) : ENat) +
            (((s_code.length + 2 * (Nat.bits s_code.length).length + c_lg : ℕ) : ENat) +
            ((v_code.length + 2 * (Nat.bits v_code.length).length + c_lg : ℕ) : ENat)))) +
          ((c_L * 5 : ℕ) : ENat) + (c_F : ENat) := by gcongr
      _ = ((((oh_code.length + 2 * (Nat.bits oh_code.length).length + c_lg) +
            ((s_code.length + 2 * (Nat.bits s_code.length).length + c_lg) +
              (v_code.length + 2 * (Nat.bits v_code.length).length + c_lg)) +
            c_L * 5 + c_F : ℕ) : ENat)) := by push_cast; ring
      _ ≤ ((cost_bound : ℕ) : ENat) := h1_cast
  calc
    KPPlain U code
        ≤ KPPlain U (listCode [grid_code, oh_code, s_code, v_code]) + (c_F : ENat) := hKP1
    _ ≤ ((([grid_code, oh_code, s_code, v_code].map fun x => KPPlain U x).sum +
          ((c_L * 5 : ℕ) : ENat))) + (c_F : ENat) := by
      gcongr
    _ = KPPlain U grid_code +
          (KPPlain U oh_code + (KPPlain U s_code + KPPlain U v_code) +
            ((c_L * 5 : ℕ) : ENat) + (c_F : ENat)) := by
      simp only [hsum, add_assoc]
    _ ≤ KPPlain U grid_code + ((cost_bound : ℕ) : ENat) := by
      gcongr

end Kolmogorov
