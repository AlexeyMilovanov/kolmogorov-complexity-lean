/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LibraryAPI
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubstrings
import KolmogorovMathlib.Complexity.KolmogorovLevin.ShortDescriptions
import KolmogorovMathlib.Prefix.ExtensionTheorem
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Levin Lemma

Levin's lemma on substrings of high plain complexity (SUV Theorem 158 and Problems 244, 245,
p. 241-242).  For every `α < 1` there is an infinite binary sequence all of whose substrings of
large length `n` have plain complexity at least `αn`; conversely every sequence has, for some
`α < 1`, infinitely many substrings of complexity at most `α` per letter.

Main declarations:
* `ncard_plainK_lt_lt`: counting the strings of length `n` with complexity below `αn`;
* `exists_blockLength_KP_increase`, `exists_blockLength_plainK_increase`: the block-length step
  of the proof for prefix and plain complexity;
* `exists_forall_substring_le_plainK`: Levin's theorem;
* `exists_lt_one_infinite_simple_substrings`: the converse statement.
-/

namespace Kolmogorov.Applications

open Filter

private lemma plainK_ne_top (V : Map) (hV : isOptimalConditional V) (x : BitString) :
    plainK V x ≠ ⊤ := by
  obtain ⟨c, hc⟩ := plainK_le_length V hV
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top (programLength x + c)) (hc x)

private lemma plainK_eq_toNat (V : Map) (hV : isOptimalConditional V) (x : BitString) :
    (plainK V x) = ((plainK V x).toNat : ℕ∞) := by
  have h := plainK_ne_top V hV x
  exact (ENat.natCast_toNat h).symm

/-- **SUV p. 241.**  The number of strings of length `n` and plain complexity less than `αn`, for
the optimal `V`, is below `2^{αn + 1}`: the programs shorter than `αn` are that few.  Optimality
makes `plainK V x` finite, so that `toNat` is the complexity itself: for a string with no program at
all, `toNat ⊤ = 0` would put it into the set. -/
theorem ncard_plainK_lt_lt (V : Map) (hV : isOptimalConditional V) {α : ℝ} (hα : 0 ≤ α) (n : ℕ) :
    (({x : BitString | x.length = n ∧ ((plainK V x).toNat : ℝ) < α * n} :
        Set BitString).ncard : ℝ) <
      (2 : ℝ) ^ (α * n + 1) := by
  have H := isUpperSemicomputable_plainK_and_card_lt_two_pow V hV
  have H1 := (H.2 (⌊α * n⌋₊ + 1)).2
  have H2 : {x : BitString | x.length = n ∧ ((plainK V x).toNat : ℝ) < α * n} ⊆ {x : BitString |
      plainK V x < ↑(⌊α * n⌋₊ + 1)} := by
    intro x hx
    have h1 : ((plainK V x).toNat : ℝ) < α * n := hx.2
    have h2 : (plainK V x).toNat ≤ ⌊α * n⌋₊ := Nat.le_floor (le_of_lt h1)
    dsimp
    rw [plainK_eq_toNat V hV x]
    exact ENat.natCast_lt_natCast.mpr (by omega)
  have H3 := Set.ncard_le_ncard H2 (H.2 (⌊α * n⌋₊ + 1)).1
  calc (({x : BitString | x.length = n ∧ ((plainK V x).toNat : ℝ) < α * n} : Set BitString).ncard :
      ℝ)
    _ ≤ ({x : BitString | plainK V x < ↑(⌊α * n⌋₊ + 1)}.ncard : ℝ) := Nat.cast_le.mpr H3
    _ < ((2 ^ (⌊α * n⌋₊ + 1) : ℕ) : ℝ) := Nat.cast_lt.mpr H1
    _ = (2 : ℝ) ^ (⌊α * n⌋₊ + 1 : ℝ) := by norm_cast
    _ ≤ (2 : ℝ) ^ (α * n + 1) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h4 := Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg n))
      linarith


/-- Step 1 of the proof of `exists_blockLength_KP_increase`: combine extension
theorem and subadditivity. -/
private lemma exists_blockLength_KP_increase_KP_bound
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℝ, ∀ x : BitString, ∀ N : ℕ,
      ∃ y : BitString, y.length = N ∧
      ((KPPlain U x).toNat : ℝ) + N ≤
      ((KPPlain U (x ++ y)).toNat : ℝ) + ((KPPlain U (natBits N)).toNat : ℝ) + c := by
  obtain ⟨c', hc'⟩ := Kolmogorov.exists_extension_KP_ge_sub U hU
  use c'
  intro x N
  obtain ⟨y, hy_len, hy_ineq⟩ := hc' x N
  use y, hy_len
  have h_real : (Kolmogorov.kVal U x : ℝ) - (Kolmogorov.kNatVal U N : ℝ) + (N : ℝ) - (c' : ℝ) ≤
      (Kolmogorov.kVal U (x ++ y) : ℝ) := by
    exact_mod_cast hy_ineq
  simp only [Kolmogorov.kVal, Kolmogorov.kNatVal, Kolmogorov.kNat] at h_real ⊢
  linarith

/-- Step 2 of the proof of `exists_blockLength_KP_increase`: asymptotics of KP(N). -/
private lemma exists_blockLength_KP_increase_asymptotics
    (U : Map) (hU : IsOptimalPrefixConditional U) {β : ℝ} (hβ : β < 1) (c : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ((KPPlain U (natBits N)).toNat : ℝ) + c ≤ (1 - β) * N := by
  obtain ⟨c0, hc0⟩ := KPPlain_le_two_mul_length U hU
  have hK_bound : ∀ N : ℕ, (KPPlain U (natBits N)).toNat ≤ 2 * (natBits N).length + c0 := by
    intro N
    have h1 := hc0 (natBits N)
    have h3 : KPPlain U (natBits N) ≤ ↑(2 * (natBits N).length + c0) := by
      exact_mod_cast h1
    exact ENat.toNat_le_of_le_natCast h3
  
  have h_len_pow : ∀ k : ℕ, (natBits (2^k)).length = k + 1 := by
    intro k
    have : (natBits (2^k)).length = (Nat.bits (2^k)).length := rfl
    rw [this, Nat.size_eq_bits_len, Nat.size_pow]
  
  have h_lim1 : Tendsto (fun k : ℕ => ((k : ℝ) / (2^k : ℝ))) atTop (nhds 0) := by
    have h := tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 2 by norm_num)
    simp only [pow_one] at h
    exact h
  
  have h_lim2 : Tendsto (fun k : ℕ => (1 / (2^k : ℝ))) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 2⁻¹ by norm_num) (show (2⁻¹:ℝ) < 1
        by norm_num)
    have h_eq : (fun k : ℕ => (1 / (2^k : ℝ))) = (fun k : ℕ => (2⁻¹ : ℝ)^k) := by
      ext k
      rw [inv_pow, one_div]
    rw [h_eq]
    exact h
  have h_pos : 0 < 1 - β := sub_pos.mpr hβ
  have h_lim3 : Tendsto (fun k : ℕ => (2 * (k : ℝ) + (2 + (c0 : ℝ) + c)) / (2^k : ℝ)) atTop (nhds 0)
      := by
    have h_eq : (fun k : ℕ => (2 * (k : ℝ) + (2 + (c0 : ℝ) + c)) / (2^k : ℝ)) = 
      (fun k : ℕ => 2 * ((k : ℝ) / (2^k : ℝ)) + (2 + (c0 : ℝ) + c) * (1 / (2^k : ℝ))) := by
      ext k
      ring
    rw [h_eq]
    have h_zero : (0 : ℝ) = 2 * 0 + (2 + (c0 : ℝ) + c) * 0 := by ring
    rw [h_zero]
    exact Tendsto.add (Tendsto.const_mul _ h_lim1) (Tendsto.const_mul _ h_lim2)
  
  have h_ev : ∀ᶠ (k : ℕ) in atTop, (2 * (k : ℝ) + (2 + (c0 : ℝ) + c)) / (2^k : ℝ) < 1 - β := by
    apply (tendsto_order.mp h_lim3).2
    exact h_pos
  obtain ⟨k, hk⟩ := h_ev.exists
  use 2^k
  constructor
  · exact Nat.two_pow_pos k
  · have h_k_bound := hK_bound (2^k)
    have h_len := h_len_pow k
    have h_ineq : ((KPPlain U (natBits (2^k))).toNat : ℝ) + c ≤ 2 * ((k : ℝ) + 1) + (c0 : ℝ) + c :=
        by
      have h1 : ((KPPlain U (natBits (2^k))).toNat : ℝ) ≤ 2 * ((natBits (2^k)).length : ℝ) + (c0 :
          ℝ) := by
        exact_mod_cast h_k_bound
      have h2 : ((natBits (2^k)).length : ℝ) = (k : ℝ) + 1 := by exact_mod_cast h_len
      rw [h2] at h1
      linarith
    have h_ineq2 : 2 * ((k : ℝ) + 1) + (c0 : ℝ) + c = 2 * (k : ℝ) + (2 + (c0 : ℝ) + c) := by ring
    rw [h_ineq2] at h_ineq
    have h_mul : 2 * (k : ℝ) + (2 + (c0 : ℝ) + c) < (1 - β) * (2^k : ℝ) := by
      have hk_div := hk
      have hk_pos : (0 : ℝ) < (2^k : ℝ) := by positivity
      exact (div_lt_iff₀ hk_pos).mp hk_div
    have h_final : (1 - β) * (2^k : ℝ) = (1 - β) * (2^k : ℕ) := by push_cast; rfl
    rw [← h_final]
    linarith

/-- **SUV p. 242**, the step of the proof of Theorem 158: from Theorem 71, for `β < 1` there is `N`
such that to each string one can append `N` bits, increasing its prefix complexity at least by
`βN`. -/
theorem exists_blockLength_KP_increase (U : Map) (hU : IsOptimalPrefixConditional U) {β : ℝ}
    (hβ : β < 1) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : BitString, ∃ y : BitString, y.length = N ∧
      ((KPPlain U x).toNat : ℝ) + β * N ≤ ((KPPlain U (x ++ y)).toNat : ℝ) := by
  obtain ⟨c, hc⟩ := exists_blockLength_KP_increase_KP_bound U hU
  obtain ⟨N, hN_pos, hN_bound⟩ := exists_blockLength_KP_increase_asymptotics U hU hβ c
  use N, hN_pos
  intro x
  obtain ⟨y, hy_len, hy_bound⟩ := hc x N
  use y, hy_len
  linarith

/-- There are exactly `2 ^ N` bit strings of length `N`. -/
private lemma exists_blockLength_plainK_increase_ncard_length (N : ℕ) :
    {y : List Bool | y.length = N}.ncard = 2 ^ N := by
  have h : {y : List Bool | y.length = N} =
      (fun v : List.Vector Bool N => v.toList) '' Set.univ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]
    constructor
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨v, rfl⟩; exact v.2
  rw [h, Set.ncard_image_of_injective _ List.Vector.toList_injective, Set.ncard_univ,
    Nat.card_eq_fintype_card, card_vector]
  simp

/-- The decompressor that reads the binary code of `N` from the head of its program, runs the
decompressor `V` on the rest and chops the last `N` bits off the output is partial recursive. -/
private lemma exists_blockLength_plainK_increase_chop_partrec (V : Map)
    (hV : isDecompressor V) :
    Partrec (fun pr : BitString × BitString =>
      (V (decodeSecond pr.1, [])).map
        (fun s => s.take (s.length - decodeBits (decodeFirst pr.1)))) := by
  have hf : Partrec (fun pr : BitString × BitString => V (decodeSecond pr.1, [])) :=
    Partrec.comp hV (Computable.pair (decodeSecond_computable.comp Computable.fst)
      (Computable.const []))
  have hg : Computable₂ (fun (pr : BitString × BitString) (s : BitString) =>
      s.take (s.length - decodeBits (decodeFirst pr.1))) :=
    (Primrec.list_take.comp
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd)
        (primrec_decodeBits.comp (CodedFiniteDistribution.decodeFirst_primrec.comp
          (Primrec.fst.comp Primrec.fst))))
      Primrec.snd).to_comp
  exact Partrec.map hf hg

/-- Step 1 of the proof of `exists_blockLength_plainK_increase`: the extension step for
the conditional complexity given `N`.  The `2 ^ N` extensions `x y` of `x` by `N` bits all have a
program of length at most `t`, the largest of their plain complexities; the decompressor that reads
`bin N` from the `pairCode` header of its program and chops the last `N` bits of the output of
`V` then gives `x` `2 ^ N` descriptions of length at most `t + 2 |bin N| + 1`, and Exercise 39
turns them into `C(x | bin N) ≤ t - N + O(1)`. -/
private lemma exists_blockLength_plainK_increase_cond_bound (V : Map)
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (N : ℕ), ∃ y : BitString, y.length = N ∧
      (condK V x (Nat.bits N)).toNat + N ≤
        (plainK V (x ++ y)).toNat + 2 * (Nat.bits N).length + c := by
  let D : Map := fun pr => (V (decodeSecond pr.1, [])).map
    (fun s => s.take (s.length - decodeBits (decodeFirst pr.1)))
  have hD : isDecompressor D := exists_blockLength_plainK_increase_chop_partrec V hV.1
  obtain ⟨c39, h39⟩ := condK_le_of_many_descriptions V hV D hD
  refine ⟨c39 + 1, fun x N => ?_⟩
  set S : Finset BitString := (finite_length_eq N).toFinset with hS
  have hSne : S.Nonempty := ⟨List.replicate N false, by simp [hS]⟩
  obtain ⟨y0, hy0S, hy0max⟩ :=
    Finset.exists_max_image S (fun y => (plainK V (x ++ y)).toNat) hSne
  have hy0len : y0.length = N := by simpa [hS] using hy0S
  set t := (plainK V (x ++ y0)).toNat with ht
  have hprog : ∀ y : BitString, y.length = N →
      ∃ q : BitString, q.length ≤ t ∧ produces V q [] (x ++ y) := by
    intro y hy
    have hyS : y ∈ S := by simp [hS, hy]
    have hle : (plainK V (x ++ y)).toNat ≤ t := hy0max y hyS
    have hfin := plainK_ne_top V hV (x ++ y)
    have hle' : plainK V (x ++ y) ≤ (t : ℕ∞) := by
      rw [← ENat.natCast_toNat hfin]
      exact_mod_cast hle
    exact (condK_le_iff V (x ++ y) [] t).mp hle'
  choose! q hqlen hq using hprog
  set P : BitString → BitString := fun y => pairCode (Nat.bits N) (q y) with hP
  have hPinj : Set.InjOn P {y | y.length = N} := by
    intro y hy y' hy' hyy'
    have h1 : q y = q y' := by
      have := congrArg decodeSecond hyy'
      simpa [hP, decodeSecond_pairCode] using this
    have h2 : x ++ y = x ++ y' := by
      have a := hq y hy
      have b := hq y' hy'
      rw [h1] at a
      exact Part.mem_unique a b
    exact List.append_cancel_left h2
  set n : ℕ := t + 2 * (Nat.bits N).length + 1 with hn
  have hsub : P '' {y | y.length = N} ⊆ descriptionsLe D x n := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y.length = N := hy
    refine ⟨?_, ?_⟩
    · change x ∈ (V (decodeSecond (pairCode (Nat.bits N) (q y)), [])).map
        (fun s => s.take (s.length - decodeBits (decodeFirst (pairCode (Nat.bits N) (q y)))))
      rw [decodeSecond_pairCode, decodeFirst_pairCode, decodeBits_natBits, Part.mem_map_iff]
      refine ⟨x ++ y, hq y hy', ?_⟩
      rw [List.length_append, hy', Nat.add_sub_cancel, List.take_left]
    · change (pairCode (Nat.bits N) (q y)).length ≤ n
      rw [length_pairCode]
      have := hqlen y hy'
      omega
  have hfin : (descriptionsLe D x n).Finite :=
    (boundedPrograms n).toFinset.finite_toSet.subset
      (ShortDescriptions.descriptionsLe_subset D x n)
  have hcard : 2 ^ N ≤ (descriptionsLe D x n).ncard := by
    calc 2 ^ N = ({y : BitString | y.length = N}).ncard :=
          (exists_blockLength_plainK_increase_ncard_length N).symm
      _ = (P '' {y | y.length = N}).ncard := (Set.InjOn.ncard_image hPinj).symm
      _ ≤ (descriptionsLe D x n).ncard := Set.ncard_le_ncard hsub hfin
  have hNn : N ≤ n := ShortDescriptions.k_le_n_of_many_desc D n N x hfin hcard
  have hcond := h39 n N x hfin hcard
  refine ⟨y0, hy0len, ?_⟩
  have h3 : (condK V x (Nat.bits N)).toNat ≤ n - N + c39 :=
    ENat.toNat_le_of_le_natCast hcond
  omega

/-- Step 2 of the proof of `exists_blockLength_plainK_increase`: the plain complexity is
at most the complexity given `N` plus the price `2 C(bin N) + O(1)` of `N`, which is
`2 |bin N| + O(1)` (Exercise 26 and the length bound for `C`). -/
private lemma exists_blockLength_plainK_increase_plain_le_cond (V : Map)
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (N : ℕ),
      (plainK V x).toNat ≤ (condK V x (Nat.bits N)).toNat + 2 * (Nat.bits N).length + c := by
  obtain ⟨k, hk⟩ := plainK_sub_condK_le_two_mul_plainK V hV
  obtain ⟨cL, hcL⟩ := plainK_le_length V hV
  refine ⟨k + 2 * cL, fun x N => ?_⟩
  have h1 := (hk x (Nat.bits N)).2
  have hfin : condK V x (Nat.bits N) ≠ ⊤ := condK_ne_top_of_optimal V hV x (Nat.bits N)
  have h2 : cVal V (Nat.bits N) ≤ (Nat.bits N).length + cL := by
    have h := hcL (Nat.bits N)
    exact ENat.toNat_le_of_le_natCast (by exact_mod_cast h)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← ha] at h1
  rw [← ha, ENat.toNat_natCast]
  have h3 : (plainK V x).toNat ≤ a + (2 * cVal V (Nat.bits N) + k) :=
    ENat.toNat_le_of_le_natCast (by exact_mod_cast h1)
  omega

/-- Step 3 of the proof of `exists_blockLength_plainK_increase`: the logarithmic price
of `N` is `o(N)`; for `β < 1` and any constant `K` there is `N > 0` (a power of `4`) with
`4 |bin N| + K ≤ (1 - β) N`. -/
private lemma exists_blockLength_plainK_increase_asymptotics {β : ℝ} (hβ : β < 1) (K : ℝ) :
    ∃ N : ℕ, 0 < N ∧ 4 * ((Nat.bits N).length : ℝ) + K ≤ (1 - β) * N := by
  have hε : 0 < 1 - β := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((12 + |K|) / (1 - β))
  have hK0 : 0 ≤ |K| := abs_nonneg K
  have hdiv : 0 < (12 + |K|) / (1 - β) := div_pos (by linarith) hε
  have hmpos : (0 : ℝ) < m := hdiv.trans hm
  have hm' : 12 + |K| < (1 - β) * m := by
    have := (div_lt_iff₀ hε).mp hm
    linarith
  refine ⟨2 ^ (2 * m), by positivity, ?_⟩
  have hlen : ((Nat.bits (2 ^ (2 * m))).length : ℝ) ≤ 2 * m + 1 := by
    have h := length_natBits_le_log (2 ^ (2 * m))
    rw [Nat.log_pow (by norm_num)] at h
    exact_mod_cast h
  have hpow : ((m : ℝ) + 1) ≤ (2 : ℝ) ^ m := by
    have h : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
    exact_mod_cast h
  have hN : ((2 ^ (2 * m) : ℕ) : ℝ) = ((2 : ℝ) ^ m) ^ 2 := by
    push_cast
    ring
  rw [hN]
  have hsq : ((m : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hpow
  have hKle : K ≤ |K| := le_abs_self K
  have h4 : (1 - β) * ((m : ℝ) + 1) ^ 2 ≤ (1 - β) * ((2 : ℝ) ^ m) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hε.le
  nlinarith [mul_pos hε hmpos]

/-- **SUV Problem 245, p. 242.**  The step of the argument for plain complexity: for `β < 1` there
is `N` such that to each string one can append `N` bits, increasing its plain complexity at least by
`βN`.  The hint of the book is Problem 46, the archived `exercise46_append`.  With this step the
proof of Theorem 158 goes through, and the conclusion of Problem 245 is that of Theorem 158. -/
theorem exists_blockLength_plainK_increase (V : Map) (hV : isOptimalConditional V) {β : ℝ}
    (hβ : β < 1) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : BitString, ∃ y : BitString, y.length = N ∧
      ((plainK V x).toNat : ℝ) + β * N ≤ ((plainK V (x ++ y)).toNat : ℝ) := by
  obtain ⟨c1, hc1⟩ := exists_blockLength_plainK_increase_cond_bound V hV
  obtain ⟨c2, hc2⟩ := exists_blockLength_plainK_increase_plain_le_cond V hV
  obtain ⟨N, hNpos, hN⟩ :=
    exists_blockLength_plainK_increase_asymptotics hβ ((c1 + c2 : ℕ) : ℝ)
  refine ⟨N, hNpos, fun x => ?_⟩
  obtain ⟨y, hylen, hy⟩ := hc1 x N
  refine ⟨y, hylen, ?_⟩
  have h2 := hc2 x N
  have h1 : (plainK V x).toNat + N ≤
      (plainK V (x ++ y)).toNat + 4 * (Nat.bits N).length + (c1 + c2) := by omega
  have h1' : ((plainK V x).toNat : ℝ) + N ≤
      ((plainK V (x ++ y)).toNat : ℝ) + 4 * ((Nat.bits N).length : ℝ) + ((c1 + c2 : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith

/-- Step 1 of the proof of `exists_forall_substring_le_plainK`: sequence factor length. -/
private lemma exists_forall_substring_le_plainK_length (w : ℕ → Bool) (i n : ℕ) : (seqFactor w
    i n).length = n := by
  simp [seqFactor]

private lemma exists_forall_substring_le_plainK_occurs (w : ℕ → Bool) (i n : ℕ) : OccursIn
    (seqFactor w i n) w := by
  use i
  have hu_eq : seqFactor w i (seqFactor w i n).length = seqFactor w i n := by
    rw [exists_forall_substring_le_plainK_length]
  exact hu_eq

/-- **SUV Theorem 158, p. 241 (Levin).**  Let `α < 1` be positive.  There is an infinite sequence
all of whose substrings of sufficiently large length `n` have complexity at least `αn`. -/
theorem exists_forall_substring_le_plainK (V : Map) (hV : isOptimalConditional V) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ w : CantorSeq, ∀ᶠ n : ℕ in atTop, ∀ i : ℕ,
      α * n ≤ ((plainK V (seqFactor w i n)).toNat : ℝ) := by
  set β : ℝ := (α + 1) / 2
  have hβ0 : 0 < β := by 
    dsimp [β]
    linarith
  have hβ1 : β < 1 := by
    dsimp [β]
    linarith
  have hβ_sub : 0 < β - α := by
    dsimp [β]
    linarith
  set N : ℕ := ⌊1 / (β - α)⌋₊ + 1
  have hN_1 : 1 / (β - α) < (N : ℝ) := by
    have H : (N : ℝ) = (⌊1 / (β - α)⌋₊ : ℝ) + 1 := by simp [N]
    rw [H]
    exact Nat.lt_floor_add_one (1 / (β - α))
  have hN : 1 ≤ (β - α) * N := by
    have h2 : 1 < (N : ℝ) * (β - α) := (div_lt_iff₀ hβ_sub).mp hN_1
    linarith
  set F : Set (List Bool) := {x : List Bool | N ≤ x.length ∧ ((plainK V x).toNat : ℝ) < α *
      x.length}
  have hF_bound : IsAtMostForbidden β F := by
    intro n
    by_cases hn : N ≤ n
    · have H_subset : {x ∈ F | x.length = n} ⊆ {x : List Bool | x.length = n ∧ ((plainK V x).toNat :
        ℝ) < α * n} := by
        intro x hx
        have hx1 : x ∈ F := hx.1
        have hx2 : x.length = n := hx.2
        simp only [Set.mem_ofPred_eq]
        refine ⟨hx2, ?_⟩
        have hx3 := hx1.2
        rw [hx2] at hx3
        exact hx3
      have H_card : (({x ∈ F | x.length = n} : Set (List Bool)).ncard : ℝ) ≤ (({x : List Bool |
          x.length = n ∧ ((plainK V x).toNat : ℝ) < α * n} : Set (List Bool)).ncard : ℝ) := by
        apply Nat.cast_le.mpr
        have H_fin : {x : List Bool | x.length = n ∧ ↑(plainK V x).toNat < α * ↑n}.Finite := by
          apply Set.Finite.subset (finite_length_eq n)
          intro x hx
          exact hx.1
        exact Set.ncard_le_ncard H_subset H_fin
      have H_ncard_lt := ncard_plainK_lt_lt V hV (le_of_lt hα0) n
      have H_ncard_le : (({x : List Bool | x.length = n ∧ ((plainK V x).toNat : ℝ) < α * n} : Set
          (List Bool)).ncard : ℝ) ≤ (2 : ℝ) ^ (α * n + 1) := le_of_lt H_ncard_lt
      have h_ineq2 : α * n + 1 ≤ β * n := by
        have h_n_le : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
        calc α * n + 1
          _ ≤ α * n + (β - α) * N := by linarith
          _ ≤ α * n + (β - α) * n := by
            have h_gcongr : (β - α) * N ≤ (β - α) * n := mul_le_mul_of_nonneg_left h_n_le (le_of_lt
                hβ_sub)
            linarith
          _ = β * n := by ring
      calc (({x ∈ F | x.length = n} : Set (List Bool)).ncard : ℝ)
        _ ≤ (({x : List Bool | x.length = n ∧ ((plainK V x).toNat : ℝ) < α * n} : Set (List
            Bool)).ncard : ℝ) := H_card
        _ ≤ (2 : ℝ) ^ (α * n + 1) := H_ncard_le
        _ ≤ (2 : ℝ) ^ (β * n) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h_ineq2
    · have H_empty : {x ∈ F | x.length = n} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have h1 : N ≤ x.length := h.1.1
        have h2 : x.length = n := h.2
        rw [h2] at h1
        exact hn h1
      rw [H_empty, Set.ncard_empty, Nat.cast_zero]
      positivity
  obtain ⟨c, w, hw⟩ := exists_avoidsLong hβ0 hβ1 hF_bound
  use w
  rw [eventually_atTop]
  use max N c
  intro n hn i
  have hn_ge_c : c ≤ n := le_trans (le_max_right N c) hn
  have hn_ge_N : N ≤ n := le_trans (le_max_left N c) hn
  set u := seqFactor w i n
  have hu_len : u.length = n := exists_forall_substring_le_plainK_length w i n
  have h_not_in_F : u ∉ F := by
    intro hu
    have H_occurs : OccursIn u w := exists_forall_substring_le_plainK_occurs w i n
    have H_c_le : c ≤ u.length := by rw [hu_len]; exact hn_ge_c
    exact hw u hu H_c_le H_occurs
  have H_not_F2 : ¬ (N ≤ u.length ∧ ((plainK V u).toNat : ℝ) < α * u.length) := h_not_in_F
  rw [hu_len] at H_not_F2
  push Not at H_not_F2
  exact H_not_F2 hn_ge_N

/-- The test whether `u` is an infix of `x`: some position `i` of `x` has `u` as the next
`|u|` letters. -/
private def exists_lt_one_infinite_simple_substrings_hasInfix (u x : BitString) : Bool :=
  decide ((List.range (x.length + 1)).findIdx
    (fun i => decide ((x.drop i).take u.length = u)) < x.length + 1)

/-- The infix test succeeds exactly when `u` is an infix of `x`. -/
private lemma exists_lt_one_infinite_simple_substrings_hasInfix_iff (u x : BitString) :
    exists_lt_one_infinite_simple_substrings_hasInfix u x = true ↔ u <:+: x := by
  unfold exists_lt_one_infinite_simple_substrings_hasInfix
  rw [decide_eq_true_eq]
  have hrlen : (List.range (x.length + 1)).length = x.length + 1 := List.length_range
  have key := List.findIdx_lt_length
    (p := fun i => decide ((x.drop i).take u.length = u))
    (xs := List.range (x.length + 1))
  rw [hrlen] at key
  rw [key]
  constructor
  · rintro ⟨i, -, hi⟩
    rw [decide_eq_true_eq] at hi
    have h1 : (x.drop i).take u.length <:+: x :=
      ((x.drop i).take_prefix u.length).isInfix.trans (x.drop_suffix i).isInfix
    rwa [hi] at h1
  · rintro ⟨s, t, hst⟩
    have hi_mem : s.length ∈ List.range (x.length + 1) := by
      rw [List.mem_range]
      have : s.length ≤ x.length := by
        rw [← hst]
        simp
      omega
    have hi : (x.drop s.length).take u.length = u := by
      rw [← hst, List.append_assoc, List.drop_left' rfl]
      exact List.take_left' rfl
    exact ⟨s.length, hi_mem, by rw [decide_eq_true_eq]; exact hi⟩

/-- The infix test with a fixed `u` is computable. -/
private lemma exists_lt_one_infinite_simple_substrings_hasInfix_computable (u : BitString) :
    Computable (exists_lt_one_infinite_simple_substrings_hasInfix u) := by
  have hrange : Primrec (fun x : BitString => List.range (x.length + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length)
  have hpred : Primrec₂ (fun (x : BitString) (i : ℕ) =>
      decide ((x.drop i).take u.length = u)) := by
    have hdrop : Primrec (fun r : BitString × ℕ => (r.1.drop r.2).take u.length) :=
      Primrec.list_take.comp (Primrec.const u.length)
        (Primrec.list_drop.comp Primrec.snd Primrec.fst)
    have h0 := Primrec.eq.comp hdrop (Primrec.const u)
    unfold PrimrecPred at h0
    obtain ⟨inst, h⟩ := h0
    exact Primrec.of_eq h (fun _ => by rw [decide_eq_decide])
  have hfind : Primrec (fun x : BitString =>
      (List.range (x.length + 1)).findIdx
        (fun i => decide ((x.drop i).take u.length = u))) :=
    Primrec.list_findIdx hrange hpred
  have h0 := Primrec.nat_lt.comp hfind (Primrec.succ.comp Primrec.list_length)
  unfold PrimrecPred at h0
  obtain ⟨inst, h⟩ := h0
  exact (Primrec.of_eq h (fun _ => by
    unfold exists_lt_one_infinite_simple_substrings_hasInfix; rw [decide_eq_decide])).to_comp

/-- The strings of length `m + j` without the infix `u` (of length `m`) are at most `2 ^ m - 1`
times as many as those of length `j`: cut off the first block, which is not `u`. -/
private lemma exists_lt_one_infinite_simple_substrings_card_step (u : BitString) (m j : ℕ)
    (hm : u.length = m) :
    ({x : BitString | x.length = m + j ∧ ¬ u <:+: x}).ncard ≤
      (2 ^ m - 1) * ({x : BitString | x.length = j ∧ ¬ u <:+: x}).ncard := by
  set T : Set BitString := {t : BitString | t.length = m} \ {u} with hT
  have hTfin : T.Finite := (finite_length_eq m).sdiff
  have hTcard : T.ncard = 2 ^ m - 1 := by
    have hu : u ∈ {t : BitString | t.length = m} := hm
    rw [hT, Set.ncard_sdiff_singleton_of_mem hu,
      exists_blockLength_plainK_increase_ncard_length]
  set B : Set BitString := {x : BitString | x.length = j ∧ ¬ u <:+: x} with hB
  have hBfin : B.Finite := (finite_length_eq j).subset (fun x hx => hx.1)
  have hmaps : ∀ x ∈ {x : BitString | x.length = m + j ∧ ¬ u <:+: x},
      (fun x : BitString => (x.take m, x.drop m)) x ∈ T ×ˢ B := by
    intro x hx
    obtain ⟨hlen, hno⟩ := hx
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · change (x.take m).length = m
      rw [List.length_take, hlen]
      omega
    · change x.take m ∉ ({u} : Set BitString)
      intro heq
      rw [Set.mem_singleton_iff] at heq
      exact hno (heq ▸ ((x.take_prefix m).isInfix))
    · change (x.drop m).length = j
      rw [List.length_drop, hlen]
      omega
    · change ¬ u <:+: x.drop m
      intro hinf
      exact hno (hinf.trans (x.drop_suffix m).isInfix)
  have hinj : Set.InjOn (fun x : BitString => (x.take m, x.drop m))
      {x : BitString | x.length = m + j ∧ ¬ u <:+: x} := by
    intro a _ b _ hab
    have h1 : a.take m = b.take m := congrArg Prod.fst hab
    have h2 : a.drop m = b.drop m := congrArg Prod.snd hab
    calc a = a.take m ++ a.drop m := (List.take_append_drop m a).symm
      _ = b.take m ++ b.drop m := by rw [h1, h2]
      _ = b := List.take_append_drop m b
  have := Set.ncard_le_ncard_of_injOn _ hmaps hinj (hTfin.prod hBfin)
  rwa [Set.ncard_prod, hTcard] at this

/-- The strings of length `j m` without the infix `u` (of length `m`) are at most `(2 ^ m - 1) ^ j`:
each of the `j` aligned blocks of length `m` differs from `u`. -/
private lemma exists_lt_one_infinite_simple_substrings_card_le (u : BitString) (m : ℕ)
    (hm : u.length = m) (j : ℕ) :
    ({x : BitString | x.length = j * m ∧ ¬ u <:+: x}).ncard ≤ (2 ^ m - 1) ^ j := by
  induction j with
  | zero =>
    simp only [Nat.zero_mul, pow_zero]
    have hsub : {x : BitString | x.length = 0 ∧ ¬ u <:+: x} ⊆ {[]} := by
      intro x hx
      rw [Set.mem_singleton_iff]
      exact List.length_eq_zero_iff.mp hx.1
    exact (Set.ncard_le_ncard hsub (Set.finite_singleton _)).trans (by simp)
  | succ j ih =>
    have harg : (j + 1) * m = m + j * m := by ring
    rw [harg]
    calc ({x : BitString | x.length = m + j * m ∧ ¬ u <:+: x}).ncard
        ≤ (2 ^ m - 1) * ({x : BitString | x.length = j * m ∧ ¬ u <:+: x}).ncard :=
          exists_lt_one_infinite_simple_substrings_card_step u m (j * m) hm
      _ ≤ (2 ^ m - 1) * (2 ^ m - 1) ^ j := Nat.mul_le_mul_left _ ih
      _ = (2 ^ m - 1) ^ (j + 1) := by ring

/-- The strings of length `j m` without the infix `u` form an enumerable family. -/
private lemma exists_lt_one_infinite_simple_substrings_isEnumerableFamily (u : BitString)
    (m : ℕ) :
    IsEnumerableFamily (fun j : ℕ => {x : BitString | x.length = j * m ∧ ¬ u <:+: x}) := by
  have hlen : Primrec (fun p : ℕ × BitString =>
      decide (p.2.length = p.1 * m)) := by
    have h0 := Primrec.eq.comp ((Primrec.list_length (α := Bool)).comp Primrec.snd)
      (Primrec.nat_mul.comp Primrec.fst (Primrec.const m))
    unfold PrimrecPred at h0
    obtain ⟨inst, h⟩ := h0
    exact Primrec.of_eq h (fun _ => by rw [decide_eq_decide])
  have hinf : Computable (fun p : ℕ × BitString =>
      exists_lt_one_infinite_simple_substrings_hasInfix u p.2) :=
    (exists_lt_one_infinite_simple_substrings_hasInfix_computable u).comp Computable.snd
  have hcheck : Computable (fun p : ℕ × BitString =>
      (decide (p.2.length = p.1 * m) &&
        !(exists_lt_one_infinite_simple_substrings_hasInfix u p.2))) :=
    Primrec.and.to_comp.comp hlen.to_comp (Primrec.not.to_comp.comp hinf)
  refine isRE_of_computable_bool _ _ ?_ hcheck
  intro p
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Set.mem_ofPred_eq]
  rw [Bool.eq_false_iff, ne_eq, exists_lt_one_infinite_simple_substrings_hasInfix_iff]

/-- The coding bound: if the nonempty string `u` is avoided, then for a block length `m ≥ 2` the
strings of length `j m` without the infix `u` have complexity at most `θ |x| + κ`, `θ < 1`.  The
blocks of such a string differ from `u` (`u ++ u` is used to have `m ≥ 2`, so that the number of
admissible blocks `2 ^ m - 1` is at least `3`), so the strings of length `j m` are at most
`(2 ^ m - 1) ^ j` and form an enumerable family, whence the bound
`log₂ ((2 ^ m - 1) ^ j) + O(1)`. -/
private lemma exists_lt_one_infinite_simple_substrings_key (V : Map)
    (hV : isOptimalConditional V) (u : BitString) (hu : u ≠ []) :
    ∃ (m : ℕ) (θ : ℝ) (κ : ℕ), 0 < m ∧ θ < 1 ∧ ∀ (j : ℕ) (x : BitString),
      x.length = j * m → ¬ u <:+: x → ((plainK V x).toNat : ℝ) ≤ θ * x.length + κ := by
  set u' : BitString := u ++ u with hu'
  set m : ℕ := u'.length with hm
  have hulen : 1 ≤ u.length := List.length_pos_iff.mpr hu
  have hm2 : 2 ≤ m := by
    rw [hm, hu', List.length_append]
    omega
  set A : ℕ → Set BitString := fun j => {x : BitString | x.length = j * m ∧ ¬ u' <:+: x} with hA
  have hAenum : IsEnumerableFamily A :=
    exists_lt_one_infinite_simple_substrings_isEnumerableFamily u' m
  have hAfin : ∀ n, (A n).Finite := fun n => (finite_length_eq (n * m)).subset (fun x hx => hx.1)
  have hAcard : ∀ n, (A n).ncard ≤ (2 ^ m - 1) ^ n :=
    fun n => exists_lt_one_infinite_simple_substrings_card_le u' m rfl n
  have hbase : 3 ≤ 2 ^ m - 1 := by
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow
  have hf : Computable (fun j : ℕ => (2 ^ m - 1) ^ j) :=
    (hpow.comp (Primrec.const (2 ^ m - 1)) Primrec.id).to_comp
  have hmono : StrictMono (fun j : ℕ => (2 ^ m - 1) ^ j) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self n)
  set r : ℝ := ((2 ^ m - 1 : ℕ) : ℝ) with hr
  have hr1 : 1 < r := by
    rw [hr]
    exact_mod_cast (by omega : 1 < 2 ^ m - 1)
  have hgrowth : ∀ n, 0 ≤ n →
      r * (((2 ^ m - 1) ^ n : ℕ) : ℝ) ≤ (((2 ^ m - 1) ^ (n + 1) : ℕ) : ℝ) := by
    intro n _
    rw [pow_succ, Nat.cast_mul, mul_comm]
  obtain ⟨k0, hk0⟩ := plainK_le_log_card_of_isEnumerableFamily_of_growth V hV
    (fun j : ℕ => (2 ^ m - 1) ^ j) hf hmono r hr1 0 hgrowth A hAenum hAfin hAcard
  refine ⟨m, Real.logb 2 r / m, k0, by omega, ?_, ?_⟩
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    rw [div_lt_one hmpos]
    have hlt : r < (2 : ℝ) ^ m := by
      rw [hr]
      have : 2 ^ m - 1 < 2 ^ m := Nat.sub_lt (by positivity) (by norm_num)
      exact_mod_cast this
    calc Real.logb 2 r < Real.logb 2 ((2 : ℝ) ^ m) :=
          Real.logb_lt_logb (by norm_num) (by linarith) hlt
      _ = m := by rw [Real.logb_pow]; simp
  · intro j x hxlen hxno
    have hxA : x ∈ A j := ⟨hxlen, fun h => hxno ((List.prefix_append u u).isInfix.trans h)⟩
    have h1 := hk0 j x hxA
    have h2 : (plainK V x).toNat ≤ Nat.log 2 ((2 ^ m - 1) ^ j) + k0 :=
      ENat.toNat_le_of_le_natCast h1
    have h3 : (((plainK V x).toNat : ℕ) : ℝ) ≤ (Nat.log 2 ((2 ^ m - 1) ^ j) : ℝ) + k0 := by
      exact_mod_cast h2
    have h4 : (Nat.log 2 ((2 ^ m - 1) ^ j) : ℝ) ≤ Real.logb 2 ((((2 ^ m - 1) ^ j : ℕ)) : ℝ) :=
      Real.natLog_le_logb _ _
    have h5 : Real.logb 2 ((((2 ^ m - 1) ^ j : ℕ)) : ℝ) = j * Real.logb 2 r := by
      rw [Nat.cast_pow, ← hr, Real.logb_pow]
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have h6 : Real.logb 2 r / m * (x.length : ℝ) = j * Real.logb 2 r := by
      rw [hxlen]
      push_cast
      field_simp
    linarith

/-- The bits of a factor. -/
private lemma exists_lt_one_infinite_simple_substrings_getElem?_seqFactor (w : ℕ → Bool)
    (i n j : ℕ) :
    (seqFactor w i n)[j]? = if j < n then some (w (i + j)) else none := by
  simp [seqFactor, List.getElem?_ofFn]

/-- A substring of a prefix of a sequence occurs in the sequence. -/
private lemma exists_lt_one_infinite_simple_substrings_occursIn_of_infix {u : List Bool}
    {w : ℕ → Bool} {n : ℕ} (h : u <:+: seqFactor w 0 n) : OccursIn u w := by
  obtain ⟨s, t, hst⟩ := h
  have hlen : s.length + u.length + t.length = n := by
    have := congrArg List.length hst
    simp only [List.length_append, exists_forall_substring_le_plainK_length] at this
    omega
  refine ⟨s.length, List.ext_getElem? fun j => ?_⟩
  rw [exists_lt_one_infinite_simple_substrings_getElem?_seqFactor]
  by_cases hj : j < u.length
  · have hjn : s.length + j < n := by omega
    have hat := congrArg (fun l => l[s.length + j]?) hst
    simp only [exists_lt_one_infinite_simple_substrings_getElem?_seqFactor, hjn, ite_true,
      Nat.zero_add] at hat
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_append_left hj] at hat
    rw [ite_eq_left hj, ← hat]
  · rw [ite_eq_right hj, List.getElem?_eq_none (not_lt.mp hj)]

/-- Case 1 of the hint of Problem 244: every string occurs in `w`, so the squares `x ++ x` (which
have complexity at most `|x| + O(1)`) have complexity per letter at most `3 / 4` once `x` is
long. -/
private lemma exists_lt_one_infinite_simple_substrings_all (V : Map)
    (hV : isOptimalConditional V) (w : CantorSeq) (h : ∀ u : BitString, OccursIn u w) :
    ∃ α : ℝ, α < 1 ∧ {u : BitString | OccursIn u w ∧
      ((plainK V u).toNat : ℝ) ≤ α * u.length}.Infinite := by
  have hdbl : Computable (fun x : BitString => x ++ x) :=
    Computable.list_append.comp Computable.id Computable.id
  obtain ⟨c1, hc1⟩ := plainK_map_le V hV (fun x : BitString => x ++ x) hdbl
  obtain ⟨c2, hc2⟩ := plainK_le_length V hV
  refine ⟨3 / 4, by norm_num, ?_⟩
  set M : ℕ := 2 * (c1 + c2) with hM
  apply Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => List.replicate (M + j) false ++ List.replicate (M + j) false)
  · intro a b hab
    have := congrArg List.length hab
    simp only [List.length_append, List.length_replicate] at this
    omega
  · intro j
    refine ⟨h _, ?_⟩
    set x : BitString := List.replicate (M + j) false with hx
    have hxlen : x.length = M + j := by simp [hx]
    have h1 : plainK V (x ++ x) ≤ ((x.length + c2 + c1 : ℕ) : ℕ∞) := by
      calc plainK V (x ++ x) ≤ plainK V x + (c1 : ℕ∞) := hc1 x
        _ ≤ ((x.length : ℕ) : ℕ∞) + (c2 : ℕ∞) + (c1 : ℕ∞) := by
          gcongr
          exact hc2 x
        _ = ((x.length + c2 + c1 : ℕ) : ℕ∞) := by push_cast; ring
    have h2 : (plainK V (x ++ x)).toNat ≤ x.length + c2 + c1 := ENat.toNat_le_of_le_natCast h1
    have h3 : (((plainK V (x ++ x)).toNat : ℕ) : ℝ) ≤ (x.length : ℝ) + c2 + c1 := by
      exact_mod_cast h2
    have hlen2 : ((x ++ x).length : ℝ) = 2 * (x.length : ℝ) := by
      rw [List.length_append]; push_cast; ring
    have hM' : (M : ℝ) = 2 * ((c1 : ℝ) + c2) := by rw [hM]; push_cast; ring
    have hxM : (M : ℝ) ≤ (x.length : ℝ) := by
      rw [hxlen]; push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    change (((plainK V (x ++ x)).toNat : ℕ) : ℝ) ≤ 3 / 4 * ((x ++ x).length : ℝ)
    rw [hlen2]
    nlinarith [(Nat.cast_nonneg c1 : (0 : ℝ) ≤ c1), (Nat.cast_nonneg c2 : (0 : ℝ) ≤ c2)]

/-- Case 2 of the hint of Problem 244: some string `u` does not occur in `w`; the prefixes of `w`
whose length is a multiple of the block length have complexity per letter at most `(θ + 1) / 2`. -/
private lemma exists_lt_one_infinite_simple_substrings_missing (V : Map)
    (hV : isOptimalConditional V) (w : CantorSeq) (u : BitString) (hu : ¬ OccursIn u w) :
    ∃ α : ℝ, α < 1 ∧ {v : BitString | OccursIn v w ∧
      ((plainK V v).toNat : ℝ) ≤ α * v.length}.Infinite := by
  have hune : u ≠ [] := by
    rintro rfl
    exact hu ⟨0, by simp [seqFactor]⟩
  obtain ⟨m, θ, κ, hm, hθ, hbound⟩ :=
    exists_lt_one_infinite_simple_substrings_key V hV u hune
  refine ⟨(θ + 1) / 2, by linarith, ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hθ' : 0 < 1 - θ := by linarith
  obtain ⟨J, hJ⟩ := exists_nat_ge (2 * (κ : ℝ) / ((1 - θ) * m))
  have hJ' : 2 * (κ : ℝ) ≤ J * ((1 - θ) * m) := by
    have := (div_le_iff₀ (mul_pos hθ' hmpos)).mp hJ
    exact this
  apply Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => seqFactor w 0 ((J + j) * m))
  · intro a b hab
    have := congrArg List.length hab
    simp only [exists_forall_substring_le_plainK_length] at this
    have := Nat.eq_of_mul_eq_mul_right hm this
    omega
  · intro j
    refine ⟨exists_forall_substring_le_plainK_occurs w 0 _, ?_⟩
    set x : BitString := seqFactor w 0 ((J + j) * m) with hx
    have hxlen : x.length = (J + j) * m := exists_forall_substring_le_plainK_length w 0 _
    have hno : ¬ u <:+: x := fun hinf =>
      hu (exists_lt_one_infinite_simple_substrings_occursIn_of_infix hinf)
    have h1 := hbound (J + j) x hxlen hno
    have hxreal : (x.length : ℝ) = ((J : ℝ) + j) * m := by rw [hxlen]; push_cast; ring
    have hxJ : (J : ℝ) * m ≤ (x.length : ℝ) := by
      rw [hxreal]
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    change (((plainK V x).toNat : ℕ) : ℝ) ≤ (θ + 1) / 2 * (x.length : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hxJ hθ'.le]

/-- **SUV Problem 244, p. 241.**  For each infinite sequence `ω` there are `α < 1` and infinitely
many substrings with complexity per letter at most `α`. -/
theorem exists_lt_one_infinite_simple_substrings (V : Map) (hV : isOptimalConditional V)
    (w : CantorSeq) :
    ∃ α : ℝ, α < 1 ∧ {u : BitString | OccursIn u w ∧
      ((plainK V u).toNat : ℝ) ≤ α * u.length}.Infinite := by
  by_cases h : ∀ u : BitString, OccursIn u w
  · exact exists_lt_one_infinite_simple_substrings_all V hV w h
  · obtain ⟨u, hu⟩ := not_forall.mp h
    exact exists_lt_one_infinite_simple_substrings_missing V hV w u hu

end Kolmogorov.Applications
