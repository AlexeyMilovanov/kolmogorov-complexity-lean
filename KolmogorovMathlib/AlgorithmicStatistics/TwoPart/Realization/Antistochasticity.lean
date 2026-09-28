import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.ProfileExistence
import Mathlib.Data.List.SplitOn

/-!
# Antistochastic strings exist

`exists_antistochastic`: for every `k ≤ n` there is a string of length `n` and prefix
complexity `k` whose description profile follows the extremal curve `i ↦ if i < k then n - i
else 0` — an antistochastic string.  It is obtained by realizing that curve.

`antiCurveOfTriple` encodes the extremal curve from the triple `(n, k, K)`, computably
(`antiCurveOfTriple_computable`, `antiCurveOfTriple_triple`), so
`exists_antistochastic_curve_code` gives it a code of low prefix complexity, which is what the
realization theorem requires.  `antistochastic_slack` folds the logarithmic overheads into one
slack term.
-/

namespace Kolmogorov
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- The antistochastic extremal curve `i ↦ if i < k then n - i else 0`, encoded up to
budget `K` by `curveEncode`, viewed as a *computable* function of a bitstring that
codes the triple `(n, k, K)` as `pairCode (natCode n) (pairCode (natCode k) (natCode K))`.
This is the witness making the curve code's plain complexity only `O(log (n+K))`. -/
noncomputable def antiCurveOfTriple (w : BitString) : BitString :=
  curveEncode (fun i => if i < decodeNatCode (decodeFirst (decodeSecond w))
                        then decodeNatCode (decodeFirst w) - i else 0)
              (decodeNatCode (decodeSecond (decodeSecond w)))

/-- The antistochastic curve, as a function of the code of the triple `(n, k, K)`, is computable. -/
theorem antiCurveOfTriple_computable : Computable antiCurveOfTriple := by
  unfold antiCurveOfTriple curveEncode
  have hn : Primrec (fun w => decodeNatCode (decodeFirst w)) :=
    decodeNatCode_primrec.comp decodeFirst_primrec
  have hk : Primrec (fun w => decodeNatCode (decodeFirst (decodeSecond w))) :=
    decodeNatCode_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)
  have hK : Primrec (fun w => decodeNatCode (decodeSecond (decodeSecond w))) :=
    decodeNatCode_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec)
  have hrange : Primrec (fun w => List.range (decodeNatCode (decodeSecond (decodeSecond w)) +
      1)) :=
    Primrec.list_range.comp (Primrec.succ.comp hK)
  have hg : Primrec₂ (fun (w : BitString) (i : ℕ) =>
      if i < decodeNatCode (decodeFirst (decodeSecond w))
      then decodeNatCode (decodeFirst w) - i else 0) := by
    apply Primrec.ite (Primrec.nat_lt.comp Primrec.snd (hk.comp Primrec.fst))
    · exact Primrec.nat_sub.comp (hn.comp Primrec.fst) Primrec.snd
    · exact Primrec.const 0
  have hmap : Primrec (fun w => (List.range (decodeNatCode (decodeSecond (decodeSecond w)) +
      1)).map
      (fun i => if i < decodeNatCode (decodeFirst (decodeSecond w))
                then decodeNatCode (decodeFirst w) - i else 0)) :=
    Primrec.list_map hrange hg
  have hfinal : Primrec (fun w => (( (List.range (decodeNatCode (decodeSecond (decodeSecond w))
      + 1)).map
      (fun i => if i < decodeNatCode (decodeFirst (decodeSecond w))
                then decodeNatCode (decodeFirst w) - i else 0)).flatMap
      (fun v => List.replicate v true ++ [false]))) := by
    apply Primrec.list_flatMap hmap
    have h2 : Primrec₂ (fun (_ : BitString) (v : ℕ) => natCode v) :=
      primrec_natCode.comp
        Primrec.snd
    simpa [natCode] using h2
  exact hfinal.to_comp

/-- On the code of `(n, k, K)` the transformer returns the encoding, to budget `K`, of the curve
`i ↦ if i < k then n - i else 0`. -/
theorem antiCurveOfTriple_triple (n k K : ℕ) :
    antiCurveOfTriple (pairCode (natCode n) (pairCode (natCode k) (natCode K)))
      = curveEncode (fun i => if i < k then n - i else 0) K := by
  simp [antiCurveOfTriple, decodeFirst_pairCode, decodeSecond_pairCode, decodeNatCode_natCode]

/-- The antistochastic curve `i ↦ if i < k then n - i else 0` has a code of plain prefix
complexity `logSlack c_code (n + K)`. -/
theorem exists_antistochastic_curve_code (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_code, ∀ n k K, k ≤ n → k ≤ K →
      ∃ code : BitString,
        (∀ i, decodeCurve code i = if i < k then n - i else 0) ∧
        KPPlain U code ≤ (logSlack c_code (n + K) : ENat) := by
  obtain ⟨c_map, hc_map⟩ := KPPlain_map_le U hU antiCurveOfTriple
      antiCurveOfTriple_computable
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨cNat, hc_nat⟩ := KPPlain_natCode_le_log U hU
  refine ⟨6 + (3*cNat + 2*c_pair + c_map), fun n k K hk hkK => ?_⟩
  refine ⟨curveEncode (fun i => if i < k then n - i else 0) K,
    fun i => ?_, ?_⟩
  · by_cases hi : i ≤ K
    · rw [decodeCurve_curveEncode _ _ hi]
    · push_neg at hi
      rw [decodeCurve_curveEncode_out_of_bounds _ _ hi]
      have : ¬ (i < k) := by omega
      rw [if_neg this]
  rw [(antiCurveOfTriple_triple n k K).symm]
  set w := pairCode (natCode n) (pairCode (natCode k) (natCode K)) with hw
  have hwbound : KPPlain U w
      ≤ ((2*(Nat.bits n).length + 2*(Nat.bits k).length + 2*(Nat.bits K).length
          + (3*cNat + 2*c_pair) : ℕ) : ENat) := by
    calc KPPlain U w
        ≤ KPPlain U (natCode n) + KPPlain U (pairCode (natCode k) (natCode K)) + c_pair :=
          hc_pair (natCode n) (pairCode (natCode k) (natCode K))
      _ ≤ KPPlain U (natCode n)
            + (KPPlain U (natCode k) + KPPlain U (natCode K) + c_pair) + c_pair := by
          gcongr; exact hc_pair (natCode k) (natCode K)
      _ ≤ ((2*(Nat.bits n).length + cNat : ℕ):ENat)
            + (((2*(Nat.bits k).length + cNat:ℕ):ENat)
              + ((2*(Nat.bits K).length + cNat:ℕ):ENat) + c_pair) + c_pair := by
          gcongr
          · exact hc_nat n
          · exact hc_nat k
          · exact hc_nat K
      _ = _ := by push_cast; ring
  have hbound : KPPlain U (antiCurveOfTriple w)
      ≤ ((2*(Nat.bits n).length + 2*(Nat.bits k).length + 2*(Nat.bits K).length
          + (3*cNat + 2*c_pair + c_map) : ℕ) : ENat) := by
    calc KPPlain U (antiCurveOfTriple w)
        ≤ KPPlain U w + c_map := hc_map w
      _ ≤ ((2*(Nat.bits n).length + 2*(Nat.bits k).length + 2*(Nat.bits K).length
          + (3*cNat + 2*c_pair) : ℕ) : ENat) + c_map := by gcongr
      _ = _ := by push_cast; ring
  refine le_trans hbound ?_
  have hL : (Nat.bits n).length ≤ (Nat.bits (n+K)).length := length_natBits_mono (by omega)
  have hLk : (Nat.bits k).length ≤ (Nat.bits (n+K)).length := length_natBits_mono (by omega)
  have hLK : (Nat.bits K).length ≤ (Nat.bits (n+K)).length := length_natBits_mono (by omega)
  have hnat : 2*(Nat.bits n).length + 2*(Nat.bits k).length + 2*(Nat.bits K).length
      + (3*cNat + 2*c_pair + c_map) ≤ logSlack (6 + (3*cNat + 2*c_pair + c_map)) (n+K) := by
    unfold logSlack
    set L := (Nat.bits (n+K)).length
    have h6 : 6 * L ≤ (6 + (3*cNat + 2*c_pair + c_map)) * L := Nat.mul_le_mul_right L (by
        omega)
    nlinarith [hL, hLk, hLK]
  exact_mod_cast hnat

/-- Pure log-slack folding for `exists_antistochastic`: the finitely many
logarithmic overheads produced by the profile construction (`c_real`), the curve
code (`c_code`), the two-part decoder (`c_plain`) and the singleton endpoint
(`c_sing`) all fold into a single `logSlack c n`.  Every argument to an inner
`logSlack` is linear in `n` (since `k ≤ n` and each `logSlack _ n ≤ n + O(1)`), so
`logSlack_linear_bound`/`logSlack_le_add_const` and additivity discharge it. -/
theorem antistochastic_slack (c_real c_code c_plain c_sing c_len : ℕ) :
    ∃ c : ℕ, ∃ C_M : ℕ, ∀ n k : ℕ, k ≤ n →
      (logSlack c_code (n + max (k + logSlack c_real n) n) ≤ logSlack C_M n) ∧
      (logSlack c_code (n + max (k + logSlack c_real n) n) + 2 * logSlack c_real n
        + logSlack c_plain
            (n + (k + logSlack c_code (n + max (k + logSlack c_real n) n) + logSlack c_real n)
              + logSlack c_real n)
        ≤ logSlack c n)
      ∧ (logSlack c_sing n
          + logSlack c_code (n + max (k + logSlack c_real n) n) + logSlack c_real n
          ≤ logSlack c n)
      ∧ (n < logSlack C_M n → n + 2 * (Nat.bits n).length + c_len ≤ logSlack c n) := by
  obtain ⟨b_r, hb_r⟩ := logSlack_le_add_const c_real
  obtain ⟨C_M, hC_M⟩ := logSlack_linear_bound c_code 4 b_r
  obtain ⟨b_M, hb_M⟩ := logSlack_le_add_const C_M
  obtain ⟨C_P, hC_P⟩ := logSlack_linear_bound c_plain 5 (b_M + 2 * b_r)
  refine ⟨C_M + 2 * c_real + C_P + c_sing + c_real + (2 * C_M + c_len + 2), C_M, fun n k hk =>
      ?_⟩
  have hM : logSlack c_code (n + max (k + logSlack c_real n) n) ≤ logSlack C_M n := by
    have harg : n + max (k + logSlack c_real n) n ≤ 4 * n + b_r := by have := hb_r n; omega
    exact le_trans (logSlack_mono_right _ harg) (hC_M n)
  have hMlin : logSlack c_code (n + max (k + logSlack c_real n) n) ≤ n + b_M :=
    le_trans hM (hb_M n)
  have hP : logSlack c_plain
      (n + (k + logSlack c_code (n + max (k + logSlack c_real n) n) + logSlack c_real n)
        + logSlack c_real n) ≤ logSlack C_P n := by
    have harg : n + (k + logSlack c_code (n + max (k + logSlack c_real n) n) + logSlack c_real
        n)
        + logSlack c_real n ≤ 5 * n + (b_M + 2 * b_r) := by
      have h1 := hb_r n; have h2 := hMlin; omega
    exact le_trans (logSlack_mono_right _ harg) (hC_P n)
  refine ⟨hM, ?_, ?_, ?_⟩
  · refine le_trans (add_le_add (add_le_add hM le_rfl) hP) ?_
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  · refine le_trans (add_le_add (add_le_add le_rfl hM) le_rfl) ?_
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  · intro hn
    unfold logSlack at hn ⊢
    nlinarith [Nat.zero_le ((Nat.bits n).length)]

/-- For every `k ≤ n` there is an antistochastic string of length `n`: its prefix complexity is
`k` up to `logSlack c n`, and every description of it with complexity below `k` has two-part
budget at least `n`, again up to `logSlack c n`. -/
theorem exists_antistochastic (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n k : ℕ, k ≤ n →
      ∃ x : BitString, x.length = n ∧
        KPPlain U x ≤ (k + logSlack c n : ENat) ∧
        (k : ENat) ≤ KPPlain U x + logSlack c n ∧
        (∀ i j : ℕ, i + logSlack c n < k → InDescriptionProfile U x i j →
          n ≤ i + j + logSlack c n) := by
  obtain ⟨c_real, h_real⟩ := exists_string_with_profile U hU
  obtain ⟨c_code, h_code⟩ := exists_antistochastic_curve_code U hU
  obtain ⟨c_plain, h_plain⟩ := KPPlain_le_of_inDescriptionProfile U hU
  obtain ⟨c_sing, h_sing⟩ := mem_descriptionProfileSet_singleton_of_optimal U hU
  obtain ⟨c_len, h_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c, C_M, hc⟩ := antistochastic_slack c_real c_code c_plain c_sing c_len
  refine ⟨c, fun n k hk => ?_⟩
  obtain ⟨hM_le, hA, hB, hn_small_bound⟩ := hc n k hk
  set s := logSlack c_real n with hs
  set m := logSlack c_code (n + max (k + s) n) with hm
  by_cases hmn : m ≤ n
  · -- Build the extremal antistochastic curve and realize it.
    have hkK : k ≤ max (k + s) n := le_trans (Nat.le_add_right k s) (le_max_left _ _)
    obtain ⟨code, h_dec, h_comp⟩ := h_code n k (max (k + s) n) hk hkK
    set h_func : ℕ → ℕ := fun i => if i < k then n - i else 0 with hfunc
    have h_curve : ProfileCurve U c_real n k m h_func := by
      refine ⟨code, h_dec, h_comp, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij; simp only [hfunc]; split <;> split <;> omega
      · intro i; simp only [hfunc]; split <;> split <;> omega
      · simp only [hfunc]; split <;> omega
      · simp only [hfunc]; rw [if_neg (by omega)]
      · intro i; simp only [hfunc]; split <;> omega
    obtain ⟨x, hx_len, hx_up, hx_low⟩ := h_real c_real n k m h_func h_curve
    -- `KPPlain U x` is finite, so name it `kx`.
    have hxne : KPPlain U x ≠ ⊤ := ne_top_of_le_ne_top (by
      have h : (↑(List.length x) + 2 * (↑(List.length x).bits.length : ENat) + ↑c_len)
          = ((List.length x + 2 * (List.length x).bits.length + c_len : ℕ) : ENat) := by
        push_cast; ring
      rw [h]; exact ENat.coe_ne_top _) (h_len x)
    obtain ⟨kx, hkx⟩ : ∃ kx : ℕ, KPPlain U x = (kx : ENat) :=
      ⟨(KPPlain U x).toNat, (ENat.coe_toNat hxne).symm⟩
    refine ⟨x, hx_len, ?_, ?_, ?_⟩
    · -- Upper complexity bound: `K(x) ≤ k + O(log n)`.
      have h_k := hx_up k
      have h_func_k : h_func k = 0 := by simp only [hfunc]; rw [if_neg (by omega)]
      rw [h_func_k, zero_add] at h_k
      have h_plain_k := h_plain x n (k + m + s) s hx_len h_k
      refine le_trans h_plain_k ?_
      have : (k + m + s) + s + logSlack c_plain (n + (k + m + s) + s)
          ≤ k + logSlack c n := by
        have := hA; omega
      exact_mod_cast this
    · -- Lower complexity bound: `k ≤ K(x) + O(log n)`.
      have h_i0 : InDescriptionProfile U x (kx + logSlack c_sing n) 0 :=
        h_sing x n kx hx_len hkx
      have hlow := hx_low (kx + logSlack c_sing n)
      have hknat : k ≤ kx + logSlack c n := by
        by_cases hik : (kx + logSlack c_sing n) < k
        · -- `h_func i0 = n - i0`; the singleton forbids the small-description escape.
          have hfi : h_func (kx + logSlack c_sing n) = n - (kx + logSlack c_sing n) := by
            simp only [hfunc]; rw [if_pos hik]
          rw [hfi] at hlow
          rcases hlow with hno | hle
          · exact absurd (h_i0.mono_j (Nat.zero_le _)) hno
          · have hB' := hB; omega
        · have hB' := hB; omega
      calc (k : ENat) ≤ ((kx + logSlack c n : ℕ) : ENat) := by exact_mod_cast hknat
        _ = KPPlain U x + logSlack c n := by rw [hkx]; push_cast; ring
    · -- Profile stays above the sufficiency line `n - O(log n)` below budget `k`.
      intro i j hij hprof
      have hik : i < k := by omega
      have hfi : h_func i = n - i := by simp only [hfunc]; rw [if_pos hik]
      have hlow := hx_low i
      rw [hfi] at hlow
      rcases hlow with hno | hle
      · by_cases hj : j ≤ (n - i) - (m + s)
        · exact absurd (hprof.mono_j hj) hno
        · have := hA; omega
      · have := hA; omega
  · -- m > n case: n is small, so ANY string satisfies the conditions trivially.
    have h_n_lt_M : n < logSlack C_M n := by
      have h1 : n < m := not_le.mp hmn
      exact lt_of_lt_of_le h1 hM_le
    let x := List.replicate n false
    have hx_len : x.length = n := List.length_replicate
    have hkpx_enat : KPPlain U x ≤ ((n + 2 * (Nat.bits n).length + c_len : ℕ) : ENat) := by
      have := h_len x
      rw [hx_len] at this
      have h_eq : (↑n + 2 * ↑(Nat.bits n).length + ↑c_len : ENat) =
          ↑(n + 2 * (Nat.bits n).length + c_len) := by push_cast; ring
      rw [h_eq] at this
      exact this
    have hx_ne_top : KPPlain U x ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hkpx_enat
    obtain ⟨kx, hkx⟩ : ∃ kx : ℕ, KPPlain U x = (kx : ENat) :=
      ⟨(KPPlain U x).toNat, (ENat.coe_toNat hx_ne_top).symm⟩
    have hkpx : kx ≤ n + 2 * (Nat.bits n).length + c_len := by
      rw [hkx] at hkpx_enat
      exact_mod_cast hkpx_enat
    have hn_bound := hn_small_bound h_n_lt_M
    have hkpx_le_c : kx ≤ logSlack c n := by omega
    refine ⟨x, hx_len, ?_, ?_, ?_⟩
    · rw [hkx]; exact_mod_cast (by omega : kx ≤ k + logSlack c n)
    · rw [hkx]; exact_mod_cast (by omega : k ≤ kx + logSlack c n)
    · intro i j _ _
      exact_mod_cast (by omega : n ≤ i + j + logSlack c n)

end Kolmogorov
