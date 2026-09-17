import KolmogorovMathlib.Complexity.PairComplexity.ConditionalMinimality

/-!
# One logarithm is not enough

`not_plainK_pair_le_add_single_log` (SUV Exercise 17): no constant makes
`C(x, y) ≤ C(x) + log C(x) + C(y) + c` valid for all pairs — the second logarithm cannot be
dropped.  The counterexample is the family `pairCounterexampleSet`, counted by
`block_card`, `block_disjoint`, `outer_disjoint` and `total_card`.

What *is* available is the symmetric form: `symmLogsDecompressor` puts one orientation bit in
front, so the logarithm may be charged to whichever of the two programs is shorter
(`min_log_add_le`).  `exists_minimal_program_cVal`, `overheadInnerStep`, `overheadOuterStep`
and `evalPairCode_partrec` are the composition of the two machine calls these bounds run on.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

private def pairCounterexampleSet (M j c_0 : ℕ) : Finset (BitString × BitString) :=
  (Finset.range (2 ^ j)).biUnion
    (fun i => (stringsOfLength (i + 2 ^ j - c_0)) ×ˢ
              (stringsOfLength (M - (i + 2 ^ j - c_0) - j)))

private lemma card_pairs_le_lt (U : Map) (K : ℕ) (P : Finset (BitString × BitString))
    (hP : ∀ p ∈ P, cPair U p.1 p.2 ≤ (K : ℕ∞)) :
    P.card < 2 ^ (K + 1) := by
  let S := P.image (fun p => pairCode p.1 p.2)
  have hS_card : S.card = P.card := Finset.card_image_of_injective P pairCode_injective
  have hS_sub : S ⊆ compressibleWords U [] K := by
    intro z hz
    rw [Finset.mem_image] at hz
    rcases hz with ⟨p, hp, rfl⟩
    have hcPair := hP p hp
    dsimp [cPair, plainK] at hcPair
    rw [mem_compressibleWords_iff]
    exact hcPair
  have hS_le := Finset.card_le_card hS_sub
  rw [hS_card] at hS_le
  have h_comp := card_compressibleWordsLt U [] K
  exact hS_le.trans_lt h_comp

private lemma block_disjoint (M j c_0 : ℕ) (hc_0 : c_0 < 2 ^ j) :
    (↑(Finset.range (2 ^ j)) : Set ℕ).PairwiseDisjoint
      (fun i => (stringsOfLength (i + 2 ^ j - c_0)) ×ˢ
                (stringsOfLength (M - (i + 2 ^ j - c_0) - j))) := by
  rintro i hi j_idx hj hij
  rw [Finset.mem_coe, Finset.mem_range] at hi hj
  dsimp [Set.PairwiseDisjoint, Function.onFun]
  rw [Finset.disjoint_iff_ne]
  rintro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 h_eq
  injection h_eq with hx hy
  subst hx hy
  rw [Finset.mem_product, mem_stringsOfLength] at h1 h2
  have hlen1 : x1.length = i + 2 ^ j - c_0 := h1.1
  have hlen2 : x1.length = j_idx + 2 ^ j - c_0 := h2.1
  omega

private lemma block_card (M j c_0 : ℕ) (hj_le : j ≤ M) (hc_0 : c_0 < 2 ^ j)
    (h_i_le : ∀ i < 2 ^ j, i + 2 ^ j - c_0 + j ≤ M) :
    (pairCounterexampleSet M j c_0).card = 2 ^ M := by
  dsimp [pairCounterexampleSet]
  rw [Finset.card_biUnion (block_disjoint M j c_0 hc_0)]
  have h_sum : ∑ i ∈ Finset.range (2 ^ j),
      ((stringsOfLength (i + 2 ^ j - c_0)) ×ˢ
       (stringsOfLength (M - (i + 2 ^ j - c_0) - j))).card =
      ∑ i ∈ Finset.range (2 ^ j), 2 ^ (M - j) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h_le := h_i_le i hi
    rw [Finset.card_product, card_stringsOfLength, card_stringsOfLength]
    have h1 : (i + 2 ^ j - c_0) + (M - (i + 2 ^ j - c_0) - j) = M - j := by omega
    rw [← pow_add, h1]
  rw [h_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h2 : 2 ^ j * 2 ^ (M - j) = 2 ^ (j + (M - j)) := (pow_add 2 j (M - j)).symm
  rw [h2, Nat.add_sub_of_le hj_le]

private lemma outer_disjoint (M j_0 B c_0 : ℕ) (hc_0 : c_0 < 2 ^ j_0) :
    (↑(Finset.Ico j_0 (j_0 + B)) : Set ℕ).PairwiseDisjoint
      (fun j => pairCounterexampleSet M j c_0) := by
  rintro j1 hj1 j2 hj2 hj12
  rw [Finset.mem_coe, Finset.mem_Ico] at hj1 hj2
  dsimp [Set.PairwiseDisjoint, Function.onFun]
  rw [Finset.disjoint_iff_ne]
  rintro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 h_eq
  injection h_eq with hx hy
  subst hx hy
  dsimp [pairCounterexampleSet] at h1 h2
  rw [Finset.mem_biUnion] at h1 h2
  rcases h1 with ⟨i1, hi1, h1⟩
  rcases h2 with ⟨i2, hi2, h2⟩
  rw [Finset.mem_range] at hi1 hi2
  rw [Finset.mem_product, mem_stringsOfLength] at h1 h2
  have hlen1 : x1.length = i1 + 2 ^ j1 - c_0 := h1.1
  have hlen2 : x1.length = i2 + 2 ^ j2 - c_0 := h2.1
  have hc1 : c_0 < 2 ^ j1 := calc c_0 < 2 ^ j_0 := hc_0
    _ ≤ 2 ^ j1 := Nat.pow_le_pow_right (by decide) hj1.1
  have hc2 : c_0 < 2 ^ j2 := calc c_0 < 2 ^ j_0 := hc_0
    _ ≤ 2 ^ j2 := Nat.pow_le_pow_right (by decide) hj2.1
  have h_eq_sum : i1 + 2 ^ j1 = i2 + 2 ^ j2 := by omega
  have h_b1 : 2 ^ j1 ≤ i1 + 2 ^ j1 ∧ i1 + 2 ^ j1 < 2 ^ (j1 + 1) := by
    constructor <;> omega
  have h_b2 : 2 ^ j2 ≤ i2 + 2 ^ j2 ∧ i2 + 2 ^ j2 < 2 ^ (j2 + 1) := by
    constructor <;> omega
  have hj_eq : j1 = j2 := by
    rcases lt_trichotomy j1 j2 with hlt | heq | hgt
    · have h1 : i1 + 2 ^ j1 < 2 ^ j2 := by
        calc i1 + 2 ^ j1 < 2 ^ (j1 + 1) := h_b1.2
          _ ≤ 2 ^ j2 := Nat.pow_le_pow_right (by decide) hlt
      omega
    · exact heq
    · have h2 : i2 + 2 ^ j2 < 2 ^ j1 := by
        calc i2 + 2 ^ j2 < 2 ^ (j2 + 1) := h_b2.2
          _ ≤ 2 ^ j1 := Nat.pow_le_pow_right (by decide) hgt
      omega
  exact hj12 hj_eq

private lemma total_card (M j_0 B c_0 : ℕ) (hc_0 : c_0 < 2 ^ j_0)
    (hj_le : ∀ j ∈ Finset.Ico j_0 (j_0 + B), j ≤ M)
    (h_i_le : ∀ j ∈ Finset.Ico j_0 (j_0 + B), ∀ i < 2 ^ j, i + 2 ^ j - c_0 + j ≤ M) :
    ((Finset.Ico j_0 (j_0 + B)).biUnion (fun j => pairCounterexampleSet M j c_0)).card
      = B * 2 ^ M := by
  rw [Finset.card_biUnion (outer_disjoint M j_0 B c_0 hc_0)]
  have h_sum : ∑ j ∈ Finset.Ico j_0 (j_0 + B), (pairCounterexampleSet M j c_0).card =
      ∑ j ∈ Finset.Ico j_0 (j_0 + B), 2 ^ M := by
    apply Finset.sum_congr rfl
    intro j hj
    have hc_j : c_0 < 2 ^ j := by
      rw [Finset.mem_Ico] at hj
      calc c_0 < 2 ^ j_0 := hc_0
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj.1
    exact block_card M j c_0 (hj_le j hj) hc_j (h_i_le j hj)
  rw [h_sum, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, smul_eq_mul]

/-- **Exercise 17.** No constant makes `C(x, y) ≤ C(x) + log C(x) + C(y) + c`
valid for all pairs. -/
theorem not_plainK_pair_le_add_single_log (U : Map) (hU : isOptimalConditional U) :
    ¬ ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + plainK U y + ((Nat.log 2 (cVal U x) + k : ℕ) : ℕ∞) := by
  obtain ⟨c_0, hc_0⟩ := plainK_le_length U hU
  rintro ⟨k, h_hyp⟩
  set C_0 := 2 * c_0 + k
  set j_0 := c_0 + 1
  have hc_0_lt : c_0 < 2 ^ j_0 := by
    have h1 : c_0 < 2 ^ c_0 := (Nat.lt_pow_self (by decide : 1 < 2) : c_0 < 2 ^ c_0)
    have h2 : 2 ^ c_0 ≤ 2 ^ (c_0 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact h1.trans_le h2
  set B := 2 ^ (C_0 + 1) + 1
  set N := 2 ^ (j_0 + B) - 1 - c_0
  set M := N + j_0 + B - 1
  have hj_le : ∀ j ∈ Finset.Ico j_0 (j_0 + B), j ≤ M := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    dsimp [M, N]
    omega
  have h_i_le : ∀ j ∈ Finset.Ico j_0 (j_0 + B), ∀ i < 2 ^ j, i + 2 ^ j - c_0 + j ≤ M := by
    intro j hj i hi
    rw [Finset.mem_Ico] at hj
    have h1 : 2 ^ (j + 1) ≤ 2 ^ (j_0 + B) := Nat.pow_le_pow_right (by decide) hj.2
    have h2 : i + 2 ^ j < 2 ^ (j + 1) := by omega
    dsimp [M, N]
    omega
  set P := (Finset.Ico j_0 (j_0 + B)).biUnion (fun j => pairCounterexampleSet M j c_0)
  have hP_card := total_card M j_0 B c_0 hc_0_lt hj_le h_i_le
  have hlen : ∀ z : BitString, plainK U z ≤ ((z.length + c_0 : ℕ) : ℕ∞) := by
    intro z
    simpa [programLength] using hc_0 z
  have hP_comp : ∀ p ∈ P, cPair U p.1 p.2 ≤ ((M + C_0 : ℕ) : ℕ∞) := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    rcases hp with ⟨j, hj, hp⟩
    dsimp [pairCounterexampleSet] at hp
    rw [Finset.mem_biUnion] at hp
    rcases hp with ⟨i, hi, hp⟩
    rw [Finset.mem_range] at hi
    rw [Finset.mem_product, mem_stringsOfLength, mem_stringsOfLength] at hp
    have hlenx : p.1.length = i + 2 ^ j - c_0 := hp.1
    have hleny : p.2.length = M - (i + 2 ^ j - c_0) - j := hp.2
    have hc_j : c_0 < 2 ^ j := by
      rw [Finset.mem_Ico] at hj
      calc c_0 < 2 ^ j_0 := hc_0_lt
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj.1
    have h_bound : i + 2 ^ j - c_0 + j ≤ M := h_i_le j hj i hi
    have h_cVal : cVal U p.1 ≤ i + 2 ^ j := by
      unfold cVal
      have h1 := hlen p.1
      rw [hlenx] at h1
      have h2 : i + 2 ^ j - c_0 + c_0 = i + 2 ^ j := by omega
      rw [h2] at h1
      exact ENat.toNat_le_of_le_natCast h1
    have h_log : Nat.log 2 (cVal U p.1) ≤ j := by
      have h1 : Nat.log 2 (cVal U p.1) ≤ Nat.log 2 (i + 2 ^ j) := Nat.log_mono_right h_cVal
      have h2 : i + 2 ^ j < 2 ^ (j + 1) := by omega
      have h3 : Nat.log 2 (i + 2 ^ j) = j := by
        rw [Nat.log_eq_iff (Or.inr ⟨by decide, by omega⟩)]
        constructor <;> omega
      omega
    have h_kx : plainK U p.1 ≤ ((i + 2 ^ j : ℕ) : ℕ∞) := by
      have h1 := hlen p.1
      rw [hlenx] at h1
      have h2 : i + 2 ^ j - c_0 + c_0 = i + 2 ^ j := by omega
      rw [h2] at h1
      exact h1
    have h_ky : plainK U p.2 ≤ ((M - (i + 2 ^ j - c_0) - j + c_0 : ℕ) : ℕ∞) := by
      have h1 := hlen p.2
      rw [hleny] at h1
      exact h1
    have h_main := h_hyp p.1 p.2
    have h_arith : (i + 2 ^ j : ℕ) + (M - (i + 2 ^ j - c_0) - j + c_0) + j + k ≤
        M + (2 * c_0 + k) := by omega
    have h_arith_coe : (((i + 2 ^ j : ℕ) + (M - (i + 2 ^ j - c_0) - j + c_0) + j + k : ℕ) : ℕ∞) ≤
        ((M + (2 * c_0 + k) : ℕ) : ℕ∞) := by exact_mod_cast h_arith
    calc cPair U p.1 p.2
        ≤ plainK U p.1 + plainK U p.2 + ((Nat.log 2 (cVal U p.1) + k : ℕ) : ℕ∞) := h_main
      _ ≤ ((i + 2 ^ j : ℕ) : ℕ∞) + ((M - (i + 2 ^ j - c_0) - j + c_0 : ℕ) : ℕ∞) +
          ((j + k : ℕ) : ℕ∞) := by
        gcongr
      _ = (((i + 2 ^ j : ℕ) + (M - (i + 2 ^ j - c_0) - j + c_0) + j + k : ℕ) : ℕ∞) := by
        push_cast; ring
      _ ≤ ((M + (2 * c_0 + k) : ℕ) : ℕ∞) := h_arith_coe
  have hP_lt := card_pairs_le_lt U (M + C_0) P hP_comp
  have h_B_eq : B * 2 ^ M = 2 ^ (M + C_0 + 1) + 2 ^ M := by
    dsimp [B]
    calc (2 ^ (C_0 + 1) + 1) * 2 ^ M
        = 2 ^ (C_0 + 1) * 2 ^ M + 2 ^ M := by ring
      _ = 2 ^ (M + C_0 + 1) + 2 ^ M := by rw [← pow_add]; ring_nf
  have h_pos : 0 < 2 ^ M := by positivity
  rw [hP_card, h_B_eq] at hP_lt
  omega

/-- For an optimal decompressor every string has a program of length exactly `cVal U x`. -/
lemma exists_minimal_program_cVal (U : Map) (hU : isOptimalConditional U) (x : BitString) :
    ∃ p : BitString, produces U p [] x ∧ p.length = cVal U x := by
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_le_cVal U hU x
  have hp_ge : cVal U x ≤ p.length := by
    have h_mem : (p.length : ℕ∞) ∈ candidateLengths U x [] := ⟨p, hp_prod, rfl⟩
    have h_inf := sInf_le h_mem
    have h_toNat := ENat.toNat_le_of_le_natCast h_inf
    exact h_toNat
  exact ⟨p, hp_prod, by omega⟩

/-- Second stage of the composed decompressor: runs `U` on the second field and pairs its output
with the string obtained in the first stage. -/
def overheadInnerStep (U : Map) (q2 : ((BitString × BitString) × BitString) × BitString) :
    Part BitString :=
  (U (decodeSecond q2.1.2, [])).map (fun y => pairCode q2.2 y)

private lemma overheadInnerStep_partrec (U : Map) (hU : Partrec U) :
    Partrec (overheadInnerStep U) := by
  have h_dec : Primrec (fun q2 : ((BitString × BitString) × BitString) × BitString =>
      decodeSecond q2.1.2) :=
    CodedFiniteDistribution.decodeSecond_primrec.comp (Primrec.snd.comp Primrec.fst)
  have h_f : Computable (fun q2 : ((BitString × BitString) × BitString) × BitString =>
      (decodeSecond q2.1.2, ([] : BitString))) :=
    h_dec.to_comp.pair (Computable.const [])
  have h_y : Partrec (fun q2 : ((BitString × BitString) × BitString) × BitString =>
      U (decodeSecond q2.1.2, [])) := Partrec.comp hU h_f
  have h_q2_2 : Primrec (fun q2 : ((BitString × BitString) × BitString) × BitString => q2.2) :=
    Primrec.snd
  have h_pair_p : Primrec
      (fun q2_y : (((BitString × BitString) × BitString) × BitString) × BitString =>
        pairCode q2_y.1.2 q2_y.2) :=
    CodedFiniteDistribution.pairCode_primrec.comp (h_q2_2.comp Primrec.fst) Primrec.snd
  exact Partrec.map h_y h_pair_p.to_comp

/-- First stage of the composed decompressor: runs `U` on the first field and continues with the
second stage. -/
def overheadOuterStep (U : Map) (q1 : (BitString × BitString) × BitString) : Part BitString :=
  (U (decodeFirst q1.2, [])).bind (fun x => overheadInnerStep U (q1, x))

private lemma overheadOuterStep_partrec (U : Map) (hU : Partrec U) :
    Partrec (overheadOuterStep U) := by
  have h_dec : Primrec (fun q1 : (BitString × BitString) × BitString => decodeFirst q1.2) :=
    CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.snd
  have h_f : Computable (fun q1 : (BitString × BitString) × BitString =>
      (decodeFirst q1.2, ([] : BitString))) :=
    h_dec.to_comp.pair (Computable.const [])
  have h_x : Partrec (fun q1 : (BitString × BitString) × BitString => U (decodeFirst q1.2, [])) :=
    Partrec.comp hU h_f
  have h_step3 : Partrec (fun q1_x : ((BitString × BitString) × BitString) × BitString =>
      overheadInnerStep U q1_x) := overheadInnerStep_partrec U hU
  exact Partrec.bind h_x h_step3

/-- Decompressor that runs `U` on the program, reads the result as a code of two programs, and
outputs the pair of their outputs. -/
def overheadComposedDecompressor (U : Map) : Map := fun pr =>
  (U (pr.1, [])).bind (fun p_pair => overheadOuterStep U (pr, p_pair))

private lemma overheadComposedDecompressor_isDecompressor (U : Map) (hU : isOptimalConditional U) :
    isDecompressor (overheadComposedDecompressor U) := by
  have h_U1 : Partrec (fun pr : BitString × BitString => U (pr.1, [])) :=
    Partrec.comp hU.1 (Computable.fst.pair (Computable.const []))
  have h_step2 : Partrec (fun pr_p : (BitString × BitString) × BitString =>
      overheadOuterStep U pr_p) := overheadOuterStep_partrec U hU.1
  exact Partrec.bind h_U1 h_step2

private lemma overhead_length_to_complexity (U : Map) (hU : isOptimalConditional U) (f : ℕ → ℕ)
    (hb : ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ ((x.length + y.length + f x.length + k : ℕ) : ℕ∞)) :
    ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + plainK U y + ((f (cVal U x) + k : ℕ) : ℕ∞) := by
  obtain ⟨k, hk⟩ := hb
  have hD := overheadComposedDecompressor_isDecompressor U hU
  obtain ⟨cD, hcD⟩ := hU.2 (overheadComposedDecompressor U) hD
  refine ⟨k + cD, fun x y => ?_⟩
  have hx_ne : plainK U x ≠ ⊤ := by
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + c))
    calc plainK U x ≤ (x.length : ℕ∞) + (c : ℕ∞) := hc x
      _ = ((x.length + c : ℕ) : ℕ∞) := by push_cast; rfl
  have hy_ne : plainK U y ≠ ⊤ := by
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top (y.length + c))
    calc plainK U y ≤ (y.length : ℕ∞) + (c : ℕ∞) := hc y
      _ = ((y.length + c : ℕ) : ℕ∞) := by push_cast; rfl
  have hx_val : plainK U x = (cVal U x : ℕ∞) := (ENat.natCast_toNat hx_ne).symm
  have hy_val : plainK U y = (cVal U y : ℕ∞) := (ENat.natCast_toNat hy_ne).symm
  obtain ⟨px, hpx, hpx_len⟩ := exists_minimal_program_cVal U hU x
  obtain ⟨py, hpy, hpy_len⟩ := exists_minimal_program_cVal U hU y
  have h_pair_ne : plainK U (pairCode px py) ≠ ⊤ := by
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top ((pairCode px py).length + c))
    calc plainK U (pairCode px py) ≤ ((pairCode px py).length : ℕ∞) + (c : ℕ∞) :=
          hc (pairCode px py)
      _ = (((pairCode px py).length + c : ℕ) : ℕ∞) := by push_cast; rfl
  obtain ⟨q, hq, hq_len⟩ := exists_minimal_program_cVal U hU (pairCode px py)
  have hprod : produces (overheadComposedDecompressor U) q [] (pairCode x y) := by
    dsimp [produces, overheadComposedDecompressor, overheadOuterStep, overheadInnerStep]
    rw [Part.mem_bind_iff]
    refine ⟨pairCode px py, hq, ?_⟩
    rw [Part.mem_bind_iff]
    rw [decodeFirst_pairCode]
    refine ⟨x, hpx, ?_⟩
    rw [Part.mem_map_iff]
    rw [decodeSecond_pairCode]
    refine ⟨y, hpy, rfl⟩
  have h_condK_D : condK (overheadComposedDecompressor U) (pairCode x y) [] ≤ (q.length : ℕ∞) :=
    sInf_le ⟨q, hprod, rfl⟩
  have h_plainK_pair : plainK U (pairCode x y) ≤ (q.length : ℕ∞) + (cD : ℕ∞) := by
    calc plainK U (pairCode x y)
        ≤ condK (overheadComposedDecompressor U) (pairCode x y) [] + (cD : ℕ∞) :=
          hcD (pairCode x y) []
      _ ≤ (q.length : ℕ∞) + (cD : ℕ∞) := by gcongr
  have hq_val : (q.length : ℕ∞) = cPair U px py := by
    unfold cPair
    rw [hq_len]
    exact ENat.natCast_toNat h_pair_ne
  have hk_pair := hk px py
  rw [hpx_len, hpy_len] at hk_pair
  have h_trans : plainK U (pairCode x y) ≤
      ((cVal U x + cVal U y + f (cVal U x) + (k + cD) : ℕ) : ℕ∞) := by
    calc plainK U (pairCode x y)
        ≤ (q.length : ℕ∞) + (cD : ℕ∞) := h_plainK_pair
      _ = cPair U px py + (cD : ℕ∞) := by rw [hq_val]
      _ ≤ ((cVal U x + cVal U y + f (cVal U x) + k : ℕ) : ℕ∞) + (cD : ℕ∞) := by
          gcongr
      _ = ((cVal U x + cVal U y + f (cVal U x) + (k + cD) : ℕ) : ℕ∞) := by
          push_cast
          ring
  unfold cPair
  rw [hx_val, hy_val]
  have h_ring : ((cVal U x : ℕ∞) + (cVal U y : ℕ∞) + ((f (cVal U x) + (k + cD) : ℕ) : ℕ∞)) =
      ((cVal U x + cVal U y + f (cVal U x) + (k + cD) : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [h_ring]
  exact h_trans

private lemma overhead_complexity_to_summable (U : Map) (hU : isOptimalConditional U)
    (f : ℕ → ℕ) (hmono : Monotone f)
    (ha : ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + plainK U y + ((f (cVal U x) + k : ℕ) : ℕ∞)) :
    Summable (fun n : ℕ => (2 : ℝ) ^ (-(f n : ℤ))) := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨cLen, hcLen⟩ := plainK_le_length U hU
  have h_shift_summable : Summable (fun j : ℕ => (2 : ℝ) ^ (-(f (j + cLen) : ℤ))) := by
    apply summable_of_sum_range_le (c := (2 : ℝ) ^ (k + 2 * cLen + 1)) (fun j => by positivity)
    intro N
    set N' := N + f (N + cLen) + k + 2 * cLen
    set J := Finset.range N
    set P := Finset.biUnion J
      (fun j => (stringsOfLength j) ×ˢ (stringsOfLength (N' - j - f (j + cLen))))
    have hdisj : (J : Set ℕ).PairwiseDisjoint
        (fun j => stringsOfLength j ×ˢ stringsOfLength (N' - j - f (j + cLen))) := by
      intro j1 hj1 j2 hj2 hneq
      rw [Function.onFun, Finset.disjoint_iff_ne]
      rintro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 heq
      rw [Finset.mem_product, mem_stringsOfLength] at h1 h2
      injection heq with hx hy
      have h_len1 : x1.length = j1 := h1.1
      have h_len2 : x2.length = j2 := h2.1
      rw [hx] at h_len1
      omega
    have hP_card_sum : P.card = ∑ j ∈ J, 2 ^ (N' - f (j + cLen)) := by
      rw [Finset.card_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.card_product, card_stringsOfLength, card_stringsOfLength]
      rw [Finset.mem_range] at hj
      have hj_le : j ≤ N := by omega
      have h_le_cLen : j + cLen ≤ N + cLen := Nat.add_le_add_right hj_le cLen
      have hfj : f (j + cLen) ≤ f (N + cLen) := hmono h_le_cLen
      have h_mem : j + f (j + cLen) ≤ N' := by
        dsimp [N']
        omega
      rw [← pow_add]
      congr 1
      omega
    set Code := Finset.image (fun p : BitString × BitString => pairCode p.1 p.2) P
    have hCode_card : Code.card = P.card := by
      apply Finset.card_image_of_injective
      intro p1 p2 heq
      exact pairCode_injective heq
    have hCode_sub : Code ⊆ compressibleWords U [] (N' + k + 2 * cLen) := by
      intro z hz
      rw [Finset.mem_image] at hz
      rcases hz with ⟨p, hp, rfl⟩
      rw [Finset.mem_biUnion] at hp
      rcases hp with ⟨j, hj, hp⟩
      rw [Finset.mem_product, mem_stringsOfLength, mem_stringsOfLength] at hp
      have hx_len : p.1.length = j := hp.1
      have hy_len : p.2.length = N' - j - f (j + cLen) := hp.2
      have hk_pair := hk p.1 p.2
      have hkx : plainK U p.1 ≤ (j + cLen : ℕ∞) := by
        calc plainK U p.1 ≤ (p.1.length : ℕ∞) + (cLen : ℕ∞) := hcLen p.1
          _ = ((j + cLen : ℕ) : ℕ∞) := by push_cast [hx_len]; rfl
      have hky : plainK U p.2 ≤ (N' - j - f (j + cLen) + cLen : ℕ∞) := by
        calc plainK U p.2 ≤ (p.2.length : ℕ∞) + (cLen : ℕ∞) := hcLen p.2
          _ = ((N' - j - f (j + cLen) + cLen : ℕ) : ℕ∞) := by push_cast [hy_len]; rfl
      have h1_cVal : plainK U p.1 ≤ ((j + cLen : ℕ) : ℕ∞) := hkx
      have hcVal : cVal U p.1 ≤ j + cLen := by
        unfold cVal
        exact ENat.toNat_le_of_le_natCast h1_cVal
      have hf_le : f (cVal U p.1) ≤ f (j + cLen) := hmono hcVal
      have h1_bound : plainK U p.1 + plainK U p.2 + ((f (cVal U p.1) + k : ℕ) : ℕ∞) ≤
          ((j + cLen : ℕ) : ℕ∞) + ((N' - j - f (j + cLen) + cLen : ℕ) : ℕ∞) +
          ((f (j + cLen) + k : ℕ) : ℕ∞) :=
        add_le_add (add_le_add hkx hky) (by exact_mod_cast Nat.add_le_add_right hf_le k)
      have h2_bound : ((j + cLen : ℕ) : ℕ∞) + ((N' - j - f (j + cLen) + cLen : ℕ) : ℕ∞) +
          ((f (j + cLen) + k : ℕ) : ℕ∞) = ((N' + k + 2 * cLen : ℕ) : ℕ∞) := by
        rw [Finset.mem_range] at hj
        have hj_le : j ≤ N := by omega
        have h_le_cLen : j + cLen ≤ N + cLen := Nat.add_le_add_right hj_le cLen
        have hfj : f (j + cLen) ≤ f (N + cLen) := hmono h_le_cLen
        have h_mem : j + f (j + cLen) ≤ N' := by
          dsimp [N']
          omega
        exact_mod_cast show j + cLen + (N' - j - f (j + cLen) + cLen) + (f (j + cLen) + k) =
          N' + k + 2 * cLen by omega
      have h_bound' : plainK U (pairCode p.1 p.2) ≤ ((N' + k + 2 * cLen : ℕ) : ℕ∞) :=
        hk_pair.trans (h1_bound.trans h2_bound.le)
      exact (mem_compressibleWords_iff U [] (pairCode p.1 p.2) (N' + k + 2 * cLen)).mpr h_bound'
    have hCode_lt := (Finset.card_le_card hCode_sub).trans_lt
      (card_compressibleWordsLt U [] (N' + k + 2 * cLen))
    rw [hCode_card, hP_card_sum] at hCode_lt
    have h_real_lt : ∑ j ∈ J, (2 : ℝ) ^ (-(f (j + cLen) : ℤ)) < (2 : ℝ) ^ (k + 2 * cLen + 1) := by
      have h_sum_pow : (∑ j ∈ J, (2 : ℝ) ^ (N' - f (j + cLen))) <
          (2 : ℝ) ^ (N' + k + 2 * cLen + 1) := by
        exact_mod_cast hCode_lt
      have h2pos : (0 : ℝ) < 2 := zero_lt_two
      have h2Npos : (0 : ℝ) < (2 : ℝ) ^ N' := pow_pos h2pos N'
      have h_div : (∑ j ∈ J, (2 : ℝ) ^ (N' - f (j + cLen))) / (2 : ℝ) ^ N' <
          (2 : ℝ) ^ (N' + k + 2 * cLen + 1) / (2 : ℝ) ^ N' :=
        div_lt_div_of_pos_right h_sum_pow h2Npos
      have h_lhs (j : ℕ) (hj : j ∈ J) : (2 : ℝ) ^ (N' - f (j + cLen)) / (2 : ℝ) ^ N' =
          (2 : ℝ) ^ (-(f (j + cLen) : ℤ)) := by
        rw [Finset.mem_range] at hj
        have hj_le : j ≤ N := by omega
        have h_le_cLen : j + cLen ≤ N + cLen := Nat.add_le_add_right hj_le cLen
        have hfj : f (j + cLen) ≤ f (N + cLen) := hmono h_le_cLen
        have h_le : f (j + cLen) ≤ N' := by
          dsimp [N']
          omega
        have h_sub : (2 : ℝ) ^ (N' - f (j + cLen)) =
            (2 : ℝ) ^ (N' : ℤ) * (2 : ℝ) ^ (-(f (j + cLen) : ℤ)) := by
          rw [← zpow_natCast]
          rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
          congr 1
          zify [h_le]
          ring
        rw [h_sub, zpow_natCast, mul_comm, mul_div_cancel_right₀ _ h2Npos.ne']
      have h_rhs : (2 : ℝ) ^ (N' + k + 2 * cLen + 1) / (2 : ℝ) ^ N' =
          (2 : ℝ) ^ (k + 2 * cLen + 1) := by
        have h_pow_split : (2 : ℝ) ^ (N' + k + 2 * cLen + 1) =
            (2 : ℝ) ^ N' * (2 : ℝ) ^ (k + 2 * cLen + 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [h_pow_split, mul_comm, mul_div_cancel_right₀ _ h2Npos.ne']
      have h_lhs_sum : (∑ j ∈ J, (2 : ℝ) ^ (N' - f (j + cLen))) / (2 : ℝ) ^ N' =
          ∑ j ∈ J, (2 : ℝ) ^ (-(f (j + cLen) : ℤ)) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl h_lhs
      rw [h_lhs_sum, h_rhs] at h_div
      exact h_div
    exact h_real_lt.le
  exact (summable_nat_add_iff cLen).mp h_shift_summable

/-- The word component of a decoder state. -/
def overheadSelWord (q : (BitString × BitString) × ℕ) : BitString := q.1.1
/-- The split position packed into the numeric component of a decoder state. -/
def overheadSelIndex (q : (BitString × BitString) × ℕ) : ℕ := q.2.unpair.1
/-- The prefix length packed into the numeric component of a decoder state. -/
def overheadSelLength (q : (BitString × BitString) × ℕ) : ℕ := q.2.unpair.2

private lemma overheadSelWord_comp : Computable overheadSelWord :=
  Computable.fst.comp Computable.fst
private lemma overheadSelIndex_comp : Computable overheadSelIndex :=
  (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
private lemma overheadSelLength_comp : Computable overheadSelLength :=
  (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd

/-- The output of the allocation decompressor: the word with its first `overheadSelLength` bits
removed, split at `overheadSelIndex` and paired. -/
def overheadDecoderBody (q : (BitString × BitString) × ℕ) : BitString :=
  pairCode (overheadSelWord q |>.drop (overheadSelLength q) |>.take (overheadSelIndex q))
           (overheadSelWord q |>.drop (overheadSelLength q) |>.drop (overheadSelIndex q))

private lemma overheadDecoderBody_comp : Computable overheadDecoderBody := by
  have h_pair : Computable₂ (fun (a : BitString) (b : BitString) => pairCode a b) :=
    pairCode_computable
  have h_drop : Computable (fun (q : (BitString × BitString) × ℕ) =>
      overheadSelWord q |>.drop (overheadSelLength q)) :=
    Primrec.list_drop.to_comp.comp overheadSelLength_comp overheadSelWord_comp
  have h_take : Computable (fun (q : (BitString × BitString) × ℕ) =>
      overheadSelWord q |>.drop (overheadSelLength q) |>.take (overheadSelIndex q)) :=
    Primrec.list_take.to_comp.comp overheadSelIndex_comp h_drop
  have h_drop2 : Computable (fun (q : (BitString × BitString) × ℕ) =>
      overheadSelWord q |>.drop (overheadSelLength q) |>.drop (overheadSelIndex q)) :=
    Primrec.list_drop.to_comp.comp overheadSelIndex_comp h_drop
  exact h_pair.comp h_take h_drop2

private lemma overheadDecoderBody_partrec2 :
    Partrec₂ (fun (pr : BitString × BitString) (m : ℕ) =>
      Part.some (overheadDecoderBody (pr, m))) :=
  overheadDecoderBody_comp.partrec.to₂

private lemma overhead_pred_partrec2 (alloc : BitString → ℕ → Option BitString)
    (hcomp : Computable (fun p : BitString × ℕ => alloc p.1 p.2)) :
    Partrec₂ (fun (pr : BitString × BitString) (m : ℕ) =>
      Part.some (decide (alloc [] m.unpair.1 = some (pr.1.take m.unpair.2)))) := by
  have h_unpair1 : Primrec (fun p : (BitString × BitString) × ℕ => p.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have h_pair1 : Primrec (fun p : (BitString × BitString) × ℕ =>
      (([] : BitString), p.2.unpair.1)) :=
    (Primrec.const []).pair h_unpair1
  have h1 : Computable (fun p : (BitString × BitString) × ℕ => alloc [] p.2.unpair.1) :=
    hcomp.comp h_pair1.to_comp
  have h_unpair2 : Primrec (fun p : (BitString × BitString) × ℕ => p.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have h_pr : Primrec (fun p : (BitString × BitString) × ℕ => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have h_take : Primrec (fun p : (BitString × BitString) × ℕ => p.1.1.take p.2.unpair.2) :=
    Primrec.list_take.comp h_unpair2 h_pr
  have h2 : Computable (fun p : (BitString × BitString) × ℕ => some (p.1.1.take p.2.unpair.2)) :=
    Computable.option_some.comp h_take.to_comp
  have hpred : Computable (fun p : (BitString × BitString) × ℕ =>
      decide (alloc [] p.2.unpair.1 = some (p.1.1.take p.2.unpair.2))) :=
    (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp (h1.pair h2)
  exact hpred.partrec.to₂

/-- Decompressor driven by an allocation function: it searches for a pair `(index, length)` whose
allocated code is the corresponding prefix of the program, and then splits the program. -/
def overheadCodeDecompressor (alloc : BitString → ℕ → Option BitString) : Map := fun pr =>
  (Nat.rfind (fun m =>
      Part.some (decide (alloc [] m.unpair.1 = some (pr.1.take m.unpair.2))))).bind
    (fun m => Part.some (overheadDecoderBody (pr, m)))

private lemma overheadCodeDecompressor_isDecompressor (alloc : BitString → ℕ → Option BitString)
    (hcomp : Computable (fun p : BitString × ℕ => alloc p.1 p.2)) :
    isDecompressor (overheadCodeDecompressor alloc) :=
  Partrec.bind (Partrec.rfind (overhead_pred_partrec2 alloc hcomp)) overheadDecoderBody_partrec2

/-- The request function that asks, in the empty context, for a code of length `f n + C₀` for
the number `n`. -/
def overheadRequest (f : ℕ → ℕ) (C0 : ℕ) : BitString → ℕ → Option (BitString × ℕ) := fun ctx n =>
  bif decide (ctx = []) then some (Nat.bits n, f n + C0) else none

private lemma overheadRequest_comp (f : ℕ → ℕ) (hf : Computable f) (C0 : ℕ) :
    Computable (fun p : BitString × ℕ => overheadRequest f C0 p.1 p.2) := by
  dsimp [overheadRequest]
  have hcond : Computable (fun p : BitString × ℕ => decide (p.1 = [])) := by
    have h1 : Computable (fun p : BitString × ℕ => p.1.length == 0) :=
      (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp
        ((Computable.list_length.comp Computable.fst).pair (Computable.const 0))
    exact h1.of_eq (fun p => by cases p.1 <;> rfl)
  have hf_add : Computable (fun p : BitString × ℕ => f p.2 + C0) :=
    Primrec.nat_add.to_comp.comp (hf.comp Computable.snd) (Computable.const C0)
  have hthen : Computable (fun p : BitString × ℕ =>
      (Nat.bits p.2, f p.2 + C0)) :=
    (natBits_computable.comp Computable.snd).pair hf_add
  have helse : Computable (fun _ : BitString × ℕ => (none : Option (BitString × ℕ))) :=
    Computable.const none
  exact Computable.cond hcond (Computable.option_some.comp hthen) helse

/-- Two prefixes of a common string are comparable: one is a prefix of the other. -/
lemma isPrefix_of_isPrefix_append {c_m c_n : BitString} {rest : BitString}
    (hm : c_m <+: c_n ++ rest) (hn : c_n <+: c_n ++ rest) :
    c_m <+: c_n ∨ c_n <+: c_m := by
  obtain ⟨tm, htm⟩ := hm
  obtain ⟨tn, htn⟩ := hn
  rcases le_total c_m.length c_n.length with hle | hle
  · left
    have h1 : c_m = (c_n ++ rest).take c_m.length := by
      have h_tl := List.take_left (l₁ := c_m) (l₂ := tm)
      rw [htm] at h_tl
      exact h_tl.symm
    rw [h1, List.take_append_of_le_length hle]
    exact List.take_prefix c_m.length c_n
  · right
    have h1 : c_n = (c_n ++ rest).take c_n.length := (List.take_left (l₁ := c_n) (l₂ := rest)).symm
    have h2 : (c_n ++ rest).take c_n.length = c_m.take c_n.length := by
      rw [← htm, List.take_append_of_le_length hle]
    rw [h1, h2]
    exact List.take_prefix c_n.length c_m

private lemma overhead_weight_bound (f : ℕ → ℕ) (C0 : ℕ)
    (hc : Summable (fun n : ℕ => (2 : ℝ) ^ (-(f n : ℤ))))
    (hC0 : (∑' n : ℕ, (2 : ℝ) ^ (-(f n : ℤ))) ≤ (2 : ℝ) ^ C0) (ctx : BitString) :
    (∑' n, match overheadRequest f C0 ctx n with
      | some (_, l) => (2 : ENNReal)⁻¹ ^ l
      | none => 0) ≤ 1 := by
  by_cases hctx : ctx = []
  · subst hctx
    have h_eq : (fun n => match overheadRequest f C0 [] n with
        | some (_, l) => (2 : ENNReal)⁻¹ ^ l
        | none => 0) = (fun n => (2 : ENNReal)⁻¹ ^ (f n + C0)) := rfl
    rw [h_eq]
    have h_term (n : ℕ) : (2 : ENNReal)⁻¹ ^ (f n + C0) =
        (2 : ENNReal)⁻¹ ^ C0 * (2 : ENNReal)⁻¹ ^ f n := by
      rw [pow_add, mul_comm]
    simp_rw [h_term, ENNReal.tsum_mul_left]
    have h_ofReal (n : ℕ) : (2 : ENNReal)⁻¹ ^ f n = ENNReal.ofReal ((2 : ℝ) ^ (-(f n : ℤ))) := by
      rw [zpow_neg, zpow_natCast]
      rw [ENNReal.ofReal_inv_of_pos (by positivity)]
      rw [ENNReal.ofReal_pow (by positivity)]
      rw [ENNReal.ofReal_ofNat]
      rw [ENNReal.inv_pow]
    simp_rw [h_ofReal]
    have h_tsum_le : (∑' n, ENNReal.ofReal ((2 : ℝ) ^ (-(f n : ℤ)))) ≤ (2 : ENNReal) ^ C0 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hc]
      have h_le := ENNReal.ofReal_le_ofReal hC0
      have h_C0_eq : ENNReal.ofReal ((2 : ℝ) ^ C0) = (2 : ENNReal) ^ C0 := by
        rw [ENNReal.ofReal_pow (by positivity)]
        norm_num
      rwa [h_C0_eq] at h_le
    have h_prod : (2 : ENNReal)⁻¹ ^ C0 * (∑' n, ENNReal.ofReal ((2 : ℝ) ^ (-(f n : ℤ)))) ≤
        (2 : ENNReal)⁻¹ ^ C0 * (2 : ENNReal) ^ C0 := by gcongr
    refine h_prod.trans ?_
    rw [← ENNReal.inv_pow]
    rw [ENNReal.inv_mul_cancel (by positivity) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
  · have h_eq : (fun n => match overheadRequest f C0 ctx n with
          | some (_, l) => (2 : ENNReal)⁻¹ ^ l
          | none => 0) = (fun _ => 0) := by
      ext n
      dsimp [overheadRequest]
      have h_dec : decide (ctx = []) = false := decide_eq_false hctx
      rw [h_dec]
      rfl
    rw [h_eq, tsum_zero]
    exact zero_le_one

private lemma overhead_summable_to_length (U : Map) (hU : isOptimalConditional U)
    (f : ℕ → ℕ) (hf : Computable f)
    (hc : Summable (fun n : ℕ => (2 : ℝ) ^ (-(f n : ℤ)))) :
    ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ ((x.length + y.length + f x.length + k : ℕ) : ℕ∞) := by
  have hS_real : ∃ C0 : ℕ, (∑' n : ℕ, (2 : ℝ) ^ (-(f n : ℤ))) ≤ (2 : ℝ) ^ C0 := by
    obtain ⟨C0, hC0⟩ := exists_nat_gt (∑' n : ℕ, (2 : ℝ) ^ (-(f n : ℤ)))
    refine ⟨C0, ?_⟩
    have h1 : (C0 : ℝ) ≤ (2 : ℝ) ^ C0 := by
      have h2 : C0 < 2 ^ C0 := Nat.lt_pow_self (by decide : 1 < 2)
      exact_mod_cast h2.le
    exact hC0.le.trans h1
  obtain ⟨C0, hC0⟩ := hS_real
  have hreq_comp := overheadRequest_comp f hf C0
  have hweight := overhead_weight_bound f C0 hc hC0
  obtain ⟨alloc, halloc_comp, halloc_succ, halloc_pf⟩ :=
    exists_online_prefixFree_family (overheadRequest f C0) hreq_comp hweight
  have hD_decomp := overheadCodeDecompressor_isDecompressor alloc halloc_comp
  obtain ⟨cD, hcD⟩ := hU.2 (overheadCodeDecompressor alloc) hD_decomp
  refine ⟨C0 + cD, fun x y => ?_⟩
  have hreq_n : overheadRequest f C0 [] x.length = some (Nat.bits x.length, f x.length + C0) := rfl
  obtain ⟨c_n, hc_n, hc_n_len⟩ :=
    halloc_succ [] x.length (Nat.bits x.length) (f x.length + C0) hreq_n
  set w := c_n ++ x ++ y
  set m0 := Nat.pair x.length c_n.length
  have hm0_mem : m0 ∈ Nat.rfind (fun m => Part.some
      (decide (alloc [] m.unpair.1 = some (w.take m.unpair.2)))) := by
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · refine Part.mem_some_iff.mpr (decide_eq_true ?_).symm
      dsimp [m0, w]
      rw [Nat.unpair_pair, List.append_assoc, List.take_left]
      exact hc_n
    · intro k hk
      refine Part.mem_some_iff.mpr (decide_eq_false_iff_not.mpr ?_).symm
      intro h_k
      have h_ak : alloc [] k.unpair.1 = some (w.take k.unpair.2) := h_k
      have h_c_found_prefix : (w.take k.unpair.2) <+: c_n ++ (x ++ y) := by
        dsimp [w]
        rw [List.append_assoc]
        exact List.take_prefix k.unpair.2 (c_n ++ (x ++ y))
      have h_cn_prefix : c_n <+: c_n ++ (x ++ y) := ⟨x ++ y, rfl⟩
      have h_or := isPrefix_of_isPrefix_append h_c_found_prefix h_cn_prefix
      have h_nk_eq : k.unpair.1 = x.length := by
        by_contra h_neq
        rcases h_or with h1 | h2
        · exact halloc_pf [] k.unpair.1 x.length (w.take k.unpair.2) c_n h_ak hc_n h_neq h1
        · exact halloc_pf [] x.length k.unpair.1 c_n (w.take k.unpair.2) hc_n h_ak
            (Ne.symm h_neq) h2
      have h_lk_le : k.unpair.2 ≤ c_n.length := by
        by_contra h_gt
        have h_gt' : c_n.length < k.unpair.2 := by omega
        have h_m0_lt : m0 < k := by
          dsimp [m0]
          rw [← Nat.pair_unpair k, h_nk_eq]
          exact Nat.pair_lt_pair_right x.length h_gt'
        omega
      have h_lk_eq : k.unpair.2 = c_n.length := by
        have h_ak' := h_ak
        rw [h_nk_eq, hc_n] at h_ak'
        injection h_ak' with h_eq_str
        have h_len1 := congrArg List.length h_eq_str
        rw [List.length_take] at h_len1
        have h_w_len : w.length = c_n.length + x.length + y.length := by
          dsimp [w]
          rw [List.length_append, List.length_append]
        rw [min_def] at h_len1
        split_ifs at h_len1 with h_le
        · exact h_len1.symm
        · omega
      have hk_eq : k = m0 := by
        dsimp [m0]
        rw [← Nat.pair_unpair k, h_nk_eq, h_lk_eq]
      rw [hk_eq] at hk
      exact lt_irrefl _ hk
  have hprod : produces (overheadCodeDecompressor alloc) w [] (pairCode x y) := by
    rw [produces, overheadCodeDecompressor]
    rw [Part.mem_bind_iff]
    refine ⟨m0, hm0_mem, ?_⟩
    rw [Part.mem_some_iff]
    have h1 : m0.unpair.1 = x.length := by dsimp [m0]; rw [Nat.unpair_pair]
    have h2 : m0.unpair.2 = c_n.length := by dsimp [m0]; rw [Nat.unpair_pair]
    rw [overheadDecoderBody]
    dsimp only [overheadSelWord, overheadSelIndex, overheadSelLength]
    rw [h1, h2]
    dsimp [w]
    rw [List.append_assoc, List.drop_left,
        List.take_left (l₁ := x) (l₂ := y), List.drop_left (l₁ := x) (l₂ := y)]
  have h_condK_D : condK (overheadCodeDecompressor alloc) (pairCode x y) [] ≤ (w.length : ℕ∞) :=
    sInf_le ⟨w, hprod, rfl⟩
  have h_cPair_le : cPair U x y ≤ (w.length : ℕ∞) + (cD : ℕ∞) := by
    unfold cPair
    calc plainK U (pairCode x y)
        ≤ condK (overheadCodeDecompressor alloc) (pairCode x y) [] + (cD : ℕ∞) :=
          hcD (pairCode x y) []
      _ ≤ (w.length : ℕ∞) + (cD : ℕ∞) := by gcongr
  have hw_len : w.length = x.length + y.length + f x.length + C0 := by
    dsimp [w]
    rw [List.length_append, List.length_append, hc_n_len]
    omega
  have h_trans : (w.length : ℕ∞) + (cD : ℕ∞) =
      ((x.length + y.length + f x.length + (C0 + cD) : ℕ) : ℕ∞) := by
    push_cast [hw_len]
    ring
  rw [h_trans] at h_cPair_le
  exact h_cPair_le

/-- **Exercise 19.** For a nondecreasing total computable overhead `f`, the
complexity bound with overhead `f`, its length version, and the convergence of
`∑ 2 ^ (-f n)` are equivalent. -/
theorem pair_overhead_characterization (U : Map) (hU : isOptimalConditional U)
    (f : ℕ → ℕ) (hf : Computable f) (hmono : Monotone f) :
    ((∃ k : ℕ, ∀ x y : BitString,
        cPair U x y ≤ plainK U x + plainK U y + ((f (cVal U x) + k : ℕ) : ℕ∞)) ↔
      (∃ k : ℕ, ∀ x y : BitString,
        cPair U x y ≤ ((x.length + y.length + f x.length + k : ℕ) : ℕ∞))) ∧
    ((∃ k : ℕ, ∀ x y : BitString,
        cPair U x y ≤ plainK U x + plainK U y + ((f (cVal U x) + k : ℕ) : ℕ∞)) ↔
      Summable (fun n : ℕ => (2 : ℝ) ^ (-(f n : ℤ)))) := by
  have h_ba := overhead_length_to_complexity U hU f
  have h_ac := overhead_complexity_to_summable U hU f hmono
  have h_cb := overhead_summable_to_length U hU f hf
  refine ⟨⟨fun ha => h_cb (h_ac ha), h_ba⟩, ⟨h_ac, fun hc => h_ba (h_cb hc)⟩⟩

-- `exercise20_coefficient_one_false` (ch02-exercise-20) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

-- `exercise20_coefficient_one_plus_eps` (ch02-exercise-20) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

/-- Splits a string into the two fields of a self-delimiting pair code. -/
def parsePair (v : BitString) : BitString × BitString :=
  ((decodeSecond v).take (decodeBits (decodeFirst v)),
   (decodeSecond v).drop (decodeBits (decodeFirst v)))

/-- Splitting a pair code into its two fields is computable. -/
theorem parsePair_computable : Computable parsePair := by
  have h1 : Computable (fun v : BitString =>
      (decodeSecond v).take (decodeBits (decodeFirst v))) := by
    exact Primrec.list_take.to_comp.comp
      (decodeBits_computable.comp decodeFirst_computable) decodeSecond_computable
  have h2 : Computable (fun v : BitString =>
      (decodeSecond v).drop (decodeBits (decodeFirst v))) := by
    exact Primrec.list_drop.to_comp.comp
      (decodeBits_computable.comp decodeFirst_computable) decodeSecond_computable
  exact h1.pair h2

/-- Parsing inverts the encoding `pairCode (bits |p|) (p ++ q)`, returning `(p, q)`. -/
theorem parsePair_encode (p q : BitString) :
    parsePair (pairCode (Nat.bits p.length) (p ++ q)) = (p, q) := by
  unfold parsePair
  rw [decodeFirst_pairCode, decodeBits_natBits, decodeSecond_pairCode,
      List.take_left, List.drop_left]

/-- Runs `U` on two programs and returns the code of the pair of their outputs. -/
def evalPairCode (U : Map) (p q : BitString) : Part BitString :=
  (U (p, [])).bind (fun x => (U (q, [])).map (fun y => pairCode x y))

/-- Running `U` on two computable selections of programs and pairing the outputs is partial
computable. -/
theorem evalPairCode_partrec (U : Map) (hU : isDecompressor U)
    (f g : BitString → BitString) (hf : Computable f) (hg : Computable g) :
    Partrec (fun w => evalPairCode U (f w) (g w)) := by
  unfold evalPairCode
  have h1 : Computable (fun w : BitString => (f w, ([] : BitString))) :=
    hf.pair (Computable.const [])
  have hf_part : Partrec (fun w : BitString => U (f w, [])) :=
    Partrec.comp hU h1
  have h2 : Computable (fun (p : BitString × BitString) => (g p.1, ([] : BitString))) :=
    (hg.comp Computable.fst).pair (Computable.const [])
  have hf2 : Partrec (fun (p : BitString × BitString) => U (g p.1, [])) :=
    Partrec.comp hU h2
  have hg2 : Computable (fun (py : (BitString × BitString) × BitString) => pairCode py.1.2 py.2) :=
    (CodedFiniteDistribution.pairCode_primrec.comp (Primrec.snd.comp Primrec.fst)
      Primrec.snd).to_comp
  have hg_part : Partrec₂ (fun (w : BitString) (x : BitString) =>
      (U (g w, [])).map (fun y => pairCode x y)) :=
    Partrec.map hf2 hg2
  exact Partrec.bind hf_part hg_part

/-- Decompressor whose first bit says which of the two programs is given first, so that the
logarithmic overhead can be charged to the shorter of the two. -/
def symmLogsDecompressor (U : Map) : Map := fun pr =>
  match pr.1 with
  | false :: w' =>
    let (p, q) := parsePair w'
    evalPairCode U p q
  | true :: w' =>
    let (q, p) := parsePair w'
    evalPairCode U p q
  | [] => Part.none

/-- The decompressor with a leading orientation bit is a decompressor whenever `U` is. -/
theorem symmLogsDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (symmLogsDecompressor U) := by
  have hp1 : Computable (fun w' : BitString => (parsePair w').1) :=
    Computable.fst.comp parsePair_computable
  have hp2 : Computable (fun w' : BitString => (parsePair w').2) :=
    Computable.snd.comp parsePair_computable
  have h_false : Partrec (fun w' : BitString =>
      evalPairCode U (parsePair w').1 (parsePair w').2) :=
    evalPairCode_partrec U hU _ _ hp1 hp2
  have h_true : Partrec (fun w' : BitString =>
      evalPairCode U (parsePair w').2 (parsePair w').1) :=
    evalPairCode_partrec U hU _ _ hp2 hp1
  have h_tail : Computable (fun (pr : BitString × BitString) => pr.1.tail) :=
    Primrec.list_tail.to_comp.comp Computable.fst
  have h_head : Computable (fun (pr : BitString × BitString) =>
      (pr.1.head?).getD false) :=
    Computable.option_getD
      (Primrec.list_head?.to_comp.comp Computable.fst) (Computable.const false)
  have h_isCons : Computable (fun (pr : BitString × BitString) => decide (pr.1 ≠ [])) := by
    have h1 : Computable (fun (pr : BitString × BitString) => pr.1.length == 0) :=
      (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp
        ((Computable.list_length.comp Computable.fst).pair (Computable.const 0))
    have h2 : Computable (fun (pr : BitString × BitString) =>
        bif pr.1.length == 0 then false else true) :=
      Computable.cond h1 (Computable.const false) (Computable.const true)
    exact h2.of_eq (fun pr => by
      cases pr.1 <;> rfl)
  have h_part_true : Partrec (fun (pr : BitString × BitString) =>
      evalPairCode U (parsePair pr.1.tail).2 (parsePair pr.1.tail).1) :=
    Partrec.comp h_true h_tail
  have h_part_false : Partrec (fun (pr : BitString × BitString) =>
      evalPairCode U (parsePair pr.1.tail).1 (parsePair pr.1.tail).2) :=
    Partrec.comp h_false h_tail
  have h_inner : Partrec (fun (pr : BitString × BitString) =>
      bif (pr.1.head?).getD false
      then evalPairCode U (parsePair pr.1.tail).2 (parsePair pr.1.tail).1
      else evalPairCode U (parsePair pr.1.tail).1 (parsePair pr.1.tail).2) :=
    Partrec.cond h_head h_part_true h_part_false
  have h_outer : Partrec (fun (pr : BitString × BitString) =>
      bif decide (pr.1 ≠ [])
      then
        (bif (pr.1.head?).getD false
         then evalPairCode U (parsePair pr.1.tail).2 (parsePair pr.1.tail).1
         else evalPairCode U (parsePair pr.1.tail).1 (parsePair pr.1.tail).2)
      else Part.none) :=
    Partrec.cond h_isCons h_inner Partrec.none
  exact h_outer.of_eq (fun pr => by
    unfold symmLogsDecompressor
    cases h : pr.1 with
    | nil => rfl
    | cons b w' =>
      cases b <;> rfl)

/-- Twice the logarithm of a minimum is at most the sum of the two logarithms. -/
lemma min_log_add_le (a b : ℕ) : 2 * Nat.log 2 (min a b) ≤ Nat.log 2 a + Nat.log 2 b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    have hlog : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right h
    omega
  · rw [min_eq_right h]
    have hlog : Nat.log 2 b ≤ Nat.log 2 a := Nat.log_mono_right h
    omega

end Kolmogorov
