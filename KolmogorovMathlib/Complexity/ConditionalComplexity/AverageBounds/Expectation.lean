import KolmogorovMathlib.Complexity.ConditionalComplexity.AverageBounds.Tail

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-! ### Machinery for Exercise 42, expectation -/

/-- Conditioning on a string is at least as good as conditioning on its length. -/
private lemma avgCond_condK_le_condK_length (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y : BitString, condK U x y ≤ condK U x (Nat.bits y.length) + (c : ℕ∞) := by
  have hD : isDecompressor (fun pr : BitString × BitString => U (pr.1, Nat.bits pr.2.length)) :=
    hU.1.comp (Computable.fst.pair
      (natBits_computable.comp (Computable.list_length.comp Computable.snd)))
  obtain ⟨c, hc⟩ := hU.2 _ hD
  exact ⟨c, fun x y => (hc x y).trans (le_of_eq rfl)⟩

/-- Conditional complexity with respect to an optimal conditional decompressor is finite. -/
lemma avgCond_condK_ne_top (U : Map) (hU : isOptimalConditional U) (x y : BitString) :
    condK U x y ≠ ⊤ := condK_ne_top_of_optimal U hU x y

/-- The exact value of the partial sums of `∑ d² / 2^d`. -/
private lemma avgCond_sum_sq_div_two_pow (N : ℕ) :
    ∑ d ∈ Finset.range N, ((d : ℝ) ^ 2 / 2 ^ d) = 6 - 2 * ((N : ℝ) ^ 2 + 2 * N + 3) / 2 ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : (2 : ℝ) ^ N ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma avgCond_sum_sq_div_two_pow_le (N : ℕ) :
    ∑ d ∈ Finset.range N, ((d : ℝ) ^ 2 / 2 ^ d) ≤ 6 := by
  rw [avgCond_sum_sq_div_two_pow]
  have h : 0 ≤ 2 * ((N : ℝ) ^ 2 + 2 * N + 3) / 2 ^ N := by positivity
  linarith

private lemma avgCond_sum_ite_zero_le (T : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∑ d ∈ Finset.range T, (if d = 0 then A else 0) ≤ A := by
  induction T with
  | zero => simpa using hA
  | succ T ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos T with h | h
    · subst h
      simp
    · rw [if_neg (by omega)]
      simpa using ih

/-- Layer-cake identity for a truncated difference summed over a list. -/
private lemma avgCond_layer_cake (L : List BitString) (a : BitString → ℕ) (T : ℕ) :
    (L.map (fun y => T - a y)).sum
      = ∑ d ∈ Finset.range T, (L.filter (fun y => decide (a y + d < T))).length := by
  induction L with
  | nil => simp
  | cons y L ih =>
    have hy : T - a y = ∑ d ∈ Finset.range T, (if a y + d < T then 1 else 0) := by
      have hfil : ((Finset.range T).filter (fun d => a y + d < T)) = Finset.range (T - a y) := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      have hcard := Finset.card_filter (fun d => a y + d < T) (Finset.range T)
      rw [hfil, Finset.card_range] at hcard
      exact hcard
    rw [List.map_cons, List.sum_cons, ih, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [List.filter_cons]
    by_cases h : a y + d < T
    · rw [if_pos h, if_pos (by simpa using h), List.length_cons]
      omega
    · rw [if_neg h, if_neg (by simpa using h)]
      omega

private lemma avgCond_split_sum (L : List BitString) (a : BitString → ℕ) (T : ℕ) :
    L.length * T ≤ (L.map a).sum + (L.map (fun y => T - a y)).sum := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **Exercise 42, expectation.** The average of `C(x | y)` over `n`-bit `y` is
`C(x | n) + O(1)`, uniformly in `x` and `n`. -/
theorem average_condK_eq_condK_length (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ),
      |(((allStrings n).map (fun y => (condCVal U x y : ℝ))).sum) / (2 : ℝ) ^ n
          - (condCVal U x (Nat.bits n) : ℝ)| ≤ (c : ℝ) := by
  classical
  obtain ⟨c1, hc1⟩ := avgCond_condK_le_condK_length U hU
  obtain ⟨ct, hct⟩ := fraction_condK_lt_condK_length_le U hU
  refine ⟨c1 + 6 * ct + 1, fun x n => ?_⟩
  set T := condCVal U x (Nat.bits n) with hT
  set a : BitString → ℕ := fun y => condCVal U x y with ha
  set L := allStrings n with hL
  have hlen : L.length = 2 ^ n := length_allStrings n
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hcast : ((L.map (fun y => (a y : ℝ))).sum) = (((L.map a).sum : ℕ) : ℝ) := by
    rw [Nat.cast_list_sum, List.map_map]
    rfl
  have hupper : ∀ y ∈ L, a y ≤ T + c1 := by
    intro y hy
    have hylen : y.length = n := (mem_allStrings n y).mp hy
    have h := hc1 x y
    rw [hylen] at h
    have hne : condK U x (Nat.bits n) ≠ ⊤ := avgCond_condK_ne_top U hU x (Nat.bits n)
    refine ENat.toNat_le_of_le_natCast ?_
    refine h.trans (le_of_eq ?_)
    rw [hT]
    unfold condCVal
    rw [Nat.cast_add, ENat.natCast_toNat hne]
  have hsum_upper : (L.map a).sum ≤ 2 ^ n * (T + c1) := by
    have h := List.sum_le_card_nsmul (L.map a) (T + c1) (by
      intro v hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
      exact hupper y hy)
    simpa [hlen, smul_eq_mul] using h
  have hcount : ∀ d ∈ Finset.range T,
      ((L.filter (fun y => decide (a y + d < T))).length : ℝ)
        ≤ (if d = 0 then (2 : ℝ) ^ n else 0)
            + (ct : ℝ) * (d : ℝ) ^ 2 / 2 ^ d * 2 ^ n := by
    intro d _
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [if_pos hd]
      have hb : (L.filter (fun y => decide (a y + d < T))).length ≤ 2 ^ n := by
        calc (L.filter _).length ≤ L.length := List.length_filter_le _ _
          _ = 2 ^ n := hlen
      have hb' : ((L.filter (fun y => decide (a y + d < T))).length : ℝ) ≤ 2 ^ n := by
        exact_mod_cast hb
      have hnn : (0 : ℝ) ≤ (ct : ℝ) * (d : ℝ) ^ 2 / 2 ^ d * 2 ^ n := by positivity
      linarith
    · rw [if_neg (by omega)]
      have := hct x n d hd
      have hnn : (0 : ℝ) ≤ (ct : ℝ) * (d : ℝ) ^ 2 / 2 ^ d * 2 ^ n := by positivity
      linarith
  have hsum_layer : (((L.map (fun y => T - a y)).sum : ℕ) : ℝ)
      ≤ (1 + 6 * (ct : ℝ)) * 2 ^ n := by
    rw [avgCond_layer_cake]
    push_cast
    calc ∑ d ∈ Finset.range T, ((L.filter (fun y => decide (a y + d < T))).length : ℝ)
        ≤ ∑ d ∈ Finset.range T, ((if d = 0 then (2 : ℝ) ^ n else 0)
            + (ct : ℝ) * (d : ℝ) ^ 2 / 2 ^ d * 2 ^ n) := Finset.sum_le_sum hcount
      _ = (∑ d ∈ Finset.range T, (if d = 0 then (2 : ℝ) ^ n else 0))
            + ∑ d ∈ Finset.range T, ((ct : ℝ) * (d : ℝ) ^ 2 / 2 ^ d * 2 ^ n) :=
          Finset.sum_add_distrib
      _ ≤ (2 : ℝ) ^ n + (ct : ℝ) * 2 ^ n * ∑ d ∈ Finset.range T, ((d : ℝ) ^ 2 / 2 ^ d) := by
          gcongr
          · exact avgCond_sum_ite_zero_le T _ (by positivity)
          · rw [Finset.mul_sum]
            exact le_of_eq (Finset.sum_congr rfl (fun d _ => by ring))
      _ ≤ (1 + 6 * (ct : ℝ)) * 2 ^ n := by
          have h6 := avgCond_sum_sq_div_two_pow_le T
          have hct0 : (0 : ℝ) ≤ (ct : ℝ) := by positivity
          have hmul : (ct : ℝ) * 2 ^ n * ∑ d ∈ Finset.range T, ((d : ℝ) ^ 2 / 2 ^ d)
              ≤ (ct : ℝ) * 2 ^ n * 6 := by
            apply mul_le_mul_of_nonneg_left h6 (by positivity)
          nlinarith [hpow]
  have hTsum : T * 2 ^ n ≤ (L.map a).sum + (L.map (fun y => T - a y)).sum := by
    have h := avgCond_split_sum L a T
    rw [hlen] at h
    rw [Nat.mul_comm T (2 ^ n)]
    exact h
  set Sn := (L.map a).sum with hSn
  set Dn := (L.map (fun y => T - a y)).sum with hDn
  have h1 : (Sn : ℝ) ≤ 2 ^ n * ((T : ℝ) + c1) := by exact_mod_cast hsum_upper
  have h1' : (Sn : ℝ) ≤ (T : ℝ) * 2 ^ n + (c1 : ℝ) * 2 ^ n := by
    rw [mul_add] at h1
    linarith
  have h2 : (T : ℝ) * 2 ^ n ≤ (Sn : ℝ) + (Dn : ℝ) := by exact_mod_cast hTsum
  have h3 : (Dn : ℝ) ≤ (1 + 6 * (ct : ℝ)) * 2 ^ n := hsum_layer
  have hc1P : (c1 : ℝ) * 2 ^ n ≤ ((c1 : ℝ) + 6 * ct + 1) * 2 ^ n := by
    refine mul_le_mul_of_nonneg_right ?_ hpow.le
    have : (0 : ℝ) ≤ (ct : ℝ) := by positivity
    linarith
  have h16P : (1 + 6 * (ct : ℝ)) * 2 ^ n ≤ ((c1 : ℝ) + 6 * ct + 1) * 2 ^ n := by
    refine mul_le_mul_of_nonneg_right ?_ hpow.le
    have : (0 : ℝ) ≤ (c1 : ℝ) := by positivity
    linarith
  rw [hcast]
  have hEq : (Sn : ℝ) / 2 ^ n - (T : ℝ) = ((Sn : ℝ) - (T : ℝ) * 2 ^ n) / 2 ^ n := by
    field_simp
  rw [hEq, abs_div, abs_of_pos hpow, div_le_iff₀ hpow, abs_le]
  have hcc : ((c1 + 6 * ct + 1 : ℕ) : ℝ) = (c1 : ℝ) + 6 * (ct : ℝ) + 1 := by push_cast; ring
  rw [hcc]
  constructor
  · linarith
  · linarith

/-- Helper decompressor for Exercise 43: decodes `x` from `natCode n ++ p` by running `U` on
`(p, Nat.bits k)` where `k = n + 1 + p.length`. -/
noncomputable def shortCondDecompressor (U : Map) : Map := fun pr =>
  let n := (pr.1.takeWhile id).length
  let p := pr.1.drop (n + 1)
  let k := n + 1 + p.length
  U (p, Nat.bits k)

/-- The decompressor that reads the length of its condition off the program is a decompressor
whenever `U` is. -/
lemma shortCondDecompressor_computable (U : Map) (hU : isDecompressor U) :
    isDecompressor (shortCondDecompressor U) := by
  have h_n : Computable (fun pr : BitString × BitString => (pr.1.takeWhile id).length) :=
    ((Primrec.list_findIdx Primrec.id (Primrec.not.comp Primrec.snd).to₂).of_eq
      (fun z => (takeWhile_id_length_eq_findIdx z).symm)).to_comp.comp Computable.fst
  have h_n1 : Computable (fun pr : BitString × BitString => (pr.1.takeWhile id).length + 1) :=
    Computable.succ.comp h_n
  have h_f1 : Computable (fun pr : BitString × BitString =>
      pr.1.drop ((pr.1.takeWhile id).length + 1)) :=
    Primrec.list_drop.to_comp.comp h_n1 Computable.fst
  have h_p_len : Computable (fun pr : BitString × BitString =>
      (pr.1.drop ((pr.1.takeWhile id).length + 1)).length) :=
    Computable.list_length.comp h_f1
  have h_k : Computable (fun pr : BitString × BitString =>
      (pr.1.takeWhile id).length + 1 + (pr.1.drop ((pr.1.takeWhile id).length + 1)).length) :=
    (Primrec.nat_add.comp Primrec.fst Primrec.snd).to_comp.comp (h_n1.pair h_p_len)
  have h_f2 : Computable (fun pr : BitString × BitString =>
      Nat.bits ((pr.1.takeWhile id).length + 1 +
        (pr.1.drop ((pr.1.takeWhile id).length + 1)).length)) :=
    natBits_computable.comp h_k
  have h_f : Computable (fun pr : BitString × BitString =>
      (pr.1.drop ((pr.1.takeWhile id).length + 1),
       Nat.bits ((pr.1.takeWhile id).length + 1 +
        (pr.1.drop ((pr.1.takeWhile id).length + 1)).length))) :=
    h_f1.pair h_f2
  exact (Partrec.comp hU h_f).of_eq (fun pr => rfl)

/-- **Exercise 43.** `C(x | k) < k` implies `C(x) ≤ k + O(1)`. -/
theorem plainK_le_of_condK_lt (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (k : ℕ) (x : BitString), condK U x (Nat.bits k) < (k : ℕ∞) →
      plainK U x ≤ ((k + c : ℕ) : ℕ∞) := by
  have hD : isDecompressor (shortCondDecompressor U) :=
    shortCondDecompressor_computable U hU.1
  obtain ⟨c, hc⟩ := hU.2 (shortCondDecompressor U) hD
  refine ⟨c, ?_⟩
  intro k x hlt
  have hne : condK U x (Nat.bits k) ≠ ⊤ := ne_top_of_lt hlt
  have h_m : ∃ m : ℕ, condK U x (Nat.bits k) = (m : ℕ∞) ∧ m < k := by
    cases h : condK U x (Nat.bits k) with
    | top => contradiction
    | coe m =>
      refine ⟨m, rfl, ?_⟩
      exact_mod_cast (h ▸ hlt)
  obtain ⟨m, hm, hmk⟩ := h_m
  have hle_m : condK U x (Nat.bits k) ≤ (m : ℕ∞) := le_of_eq hm
  obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U x (Nat.bits k) m).mp hle_m
  have hp_len' : p.length ≤ m := hp_len
  have hp_lt_k : p.length < k := by omega
  let n := k - 1 - p.length
  have h_sum : n + 1 + p.length = k := by omega
  let q := natCode n ++ p
  have hq_take : (q.takeWhile id).length = n :=
    length_takeWhile_natCode_append n p
  have hq_drop : q.drop (n + 1) = p :=
    drop_natCode_append n p
  have hq_len : q.length = k := by
    change (natCode n ++ p).length = k
    rw [List.length_append, length_natCode]
    omega
  have hprod_D : produces (shortCondDecompressor U) q [] x := by
    unfold produces shortCondDecompressor
    dsimp
    rw [hq_take, hq_drop]
    have h_k_eq : n + 1 + p.length = k := h_sum
    rw [h_k_eq]
    exact hp_prod
  have h_le_D : condK (shortCondDecompressor U) x [] ≤ (k : ℕ∞) := by
    have hq_prog_len : q.length ≤ k := le_of_eq hq_len
    exact (condK_le_iff (shortCondDecompressor U) x [] k).mpr ⟨q, hq_prog_len, hprod_D⟩
  have h_plain : plainK U x ≤ condK (shortCondDecompressor U) x [] + (c : ℕ∞) :=
    hc x []
  have h_step : condK (shortCondDecompressor U) x [] + (c : ℕ∞) ≤ (k : ℕ∞) + (c : ℕ∞) := by
    simpa [add_comm] using add_le_add_right h_le_D (c : ℕ∞)
  have h_sum_cast : (k : ℕ∞) + (c : ℕ∞) = ((k + c : ℕ) : ℕ∞) := by push_cast; rfl
  exact le_trans h_plain (le_trans h_step (le_of_eq h_sum_cast))

/-- Decompressor which takes the condition to be the total length of the program, so that the
condition need not be supplied separately. -/
def selfCondDecompressor (U : Map) : Map := fun pr =>
  U (decodeSecond pr.1,
    Nat.bits ((decodeSecond pr.1).length + decodeBits (decodeFirst pr.1)))

/-- The self-conditioning decompressor is a decompressor whenever `U` is optimal. -/
lemma selfCondDecompressor_partrec (U : Map) (hU : isOptimalConditional U) :
    isDecompressor (selfCondDecompressor U) := by
  unfold selfCondDecompressor isDecompressor
  have hf : Computable (fun pr : BitString × BitString =>
      (decodeSecond pr.1,
        Nat.bits ((decodeSecond pr.1).length + decodeBits (decodeFirst pr.1)))) := by
    apply Computable.pair
    · apply Primrec.to_comp (decodeSecond_primrec.comp Primrec.fst)
    · apply natBits_computable.comp
      apply Primrec.to_comp
      apply Primrec.nat_add.comp
        (Primrec.list_length.comp (decodeSecond_primrec.comp Primrec.fst))
        (primrec_decodeBits.comp (decodeFirst_primrec.comp Primrec.fst))
  exact hU.1.comp hf

/-- **Exercise 44.** `C(x) = C(x | C(x)) + O(1)`. -/
theorem plainK_eq_condK_self_plainK (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x : BitString,
      plainK U x ≤ condK U x (Nat.bits (cVal U x)) + (c : ℕ∞) ∧
        condK U x (Nat.bits (cVal U x)) ≤ plainK U x + (c : ℕ∞) := by
  obtain ⟨cCond, hCond⟩ := condK_le_plainK U hU
  obtain ⟨cLen, hLen⟩ := plainK_le_length U hU
  obtain ⟨cD, hcD⟩ := hU.2 (selfCondDecompressor U) (selfCondDecompressor_partrec U hU)
  obtain ⟨M, hM⟩ := exists_bits_linear_domination 1 2 (1 + cD + 1)
  have h_cond_ne (x y : BitString) : condK U x y ≠ ⊤ := by
    have h_bound : condK U x y ≤ ((x.length + cLen + cCond : ℕ) : ℕ∞) := by
      calc condK U x y ≤ plainK U x + (cCond : ℕ∞) := hCond x y
        _ ≤ (x.length : ℕ∞) + (cLen : ℕ∞) + (cCond : ℕ∞) := by gcongr; exact hLen x
        _ = ((x.length + cLen + cCond : ℕ) : ℕ∞) := by push_cast; rfl
    intro htop
    rw [htop] at h_bound
    exact (ENat.natCast_ne_top (x.length + cLen + cCond) (le_top.antisymm h_bound)).elim
  refine ⟨max cCond M, fun x => ⟨?_, ?_⟩⟩
  · obtain ⟨cx, hcx⟩ := ENat.ne_top_iff_exists.mp (h_cond_ne x [])
    have h_cx : plainK U x = (cx : ℕ∞) := hcx.symm
    have hcVal : cVal U x = cx := by
      unfold cVal; rw [h_cx, ENat.toNat_natCast]
    obtain ⟨k, hk_eq⟩ := ENat.ne_top_iff_exists.mp (h_cond_ne x (Nat.bits cx))
    by_cases hck : cx < k
    · calc plainK U x = (cx : ℕ∞) := h_cx
        _ ≤ (k : ℕ∞) := by exact_mod_cast hck.le
        _ = condK U x (Nat.bits (cVal U x)) := by rw [hcVal, hk_eq.symm]
        _ ≤ condK U x (Nat.bits (cVal U x)) + (max cCond M : ℕ∞) := le_self_add
    · push Not at hck
      obtain ⟨q, hq_len, hq_prod⟩ := (condK_le_iff U x (Nat.bits cx) k).mp (by rw [hk_eq.symm])
      set diff := cx - q.length with hdiff_def
      set p := pairCode (Nat.bits diff) q with hp_def
      have h_D_prod : produces (selfCondDecompressor U) p [] x := by
        unfold produces selfCondDecompressor
        dsimp
        rw [hp_def, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
        have h_len_sum : q.length + diff = cx := by
          have : q.length ≤ cx := le_trans hq_len hck
          omega
        rw [h_len_sum]
        exact hq_prod
      have h_plainK_D : plainK (selfCondDecompressor U) x ≤ (p.length : ℕ∞) := by
        unfold plainK
        exact sInf_le ⟨p, h_D_prod, rfl⟩
      have h_len_p : p.length = 2 * (Nat.bits diff).length + 1 + q.length := by
        rw [hp_def, length_pairCode]
        omega
      have h_cx_le : cx ≤ q.length + 2 * (Nat.bits diff).length + 1 + cD := by
        have h2 : condK U x [] ≤ (p.length : ℕ∞) + (cD : ℕ∞) := calc
          condK U x [] ≤ condK (selfCondDecompressor U) x [] + (cD : ℕ∞) := hcD x []
          _ ≤ (p.length : ℕ∞) + (cD : ℕ∞) := by gcongr; exact h_plainK_D
        rw [← hcx, h_len_p] at h2
        have h_cx_le' : cx ≤ 2 * (Nat.bits diff).length + 1 + q.length + cD := by exact_mod_cast h2
        omega
      have h_diff_le : diff ≤ 2 * (Nat.bits diff).length + 1 + cD := by
        have : q.length ≤ cx := le_trans hq_len hck
        omega
      have h_diff_lt_M : diff < M := by
        by_contra h_ge
        push Not at h_ge
        have h_dom := hM diff h_ge
        omega
      have h_cx_bound : cx ≤ k + M := by
        have : q.length ≤ k := hq_len
        omega
      calc plainK U x = (cx : ℕ∞) := h_cx
        _ ≤ ((k + M : ℕ) : ℕ∞) := by exact_mod_cast h_cx_bound
        _ = (k : ℕ∞) + (M : ℕ∞) := by push_cast; rfl
        _ = condK U x (Nat.bits (cVal U x)) + (M : ℕ∞) := by rw [hcVal, hk_eq.symm]
        _ ≤ condK U x (Nat.bits (cVal U x)) + (max cCond M : ℕ∞) := by
          gcongr; exact le_max_right _ _
  · have h_right : condK U x (Nat.bits (cVal U x)) ≤ plainK U x + (cCond : ℕ∞) := hCond x _
    exact le_trans h_right (by gcongr; exact le_max_left _ _)

/-! ### Exercise 45: the Kalinina–Bauwens game

SUV problem 45 asks for, in every length `n`, a string `x` with `C(C(x) | x) = log n - O(1)`;
this is the maximal possible value, and it is Gács' theorem, here in the game-theoretic form
found by Kalinina and Bauwens (Bauwens–Shen, *Complexity of complexity and maximal plain versus
prefix-free Kolmogorov complexity*, §1).

The upper half `C(C(x) | x) ≤ log n + O(1)` (`condK_cVal_le_log_length`) holds for every `x`:
given `x` one knows `n = |x|`, and `C(x) ≤ n + O(1)` is a number of `log n + O(1)` bits.

The lower half is the game.  Board `n` has the `2 ^ n` strings of length `n` as columns and the
rows `0, …, n - 1`.  Black blackens the cell `(x, i)` once he discovers `C(i | x) < log n - 1`
(`gameBlack`; at most `2 ^ (log n - 1) - 1` cells per column, so never more than half of a
column) and puts a token strictly below row `r` of column `x` once he discovers `C(x) < r`
(`gameDead`).  White keeps one token per board: on board `n` at stage `T` it stands in column
`gameWCol c n T` — she starts at column `0` and moves one column right exactly when a black
token appears strictly below her — at the topmost cell of that column that is not blackened
(`gameTop`).  Two counting facts make this a winning strategy: every column White abandons has
`C(x) ≤ n - 2`, and there are fewer than `2 ^ n` such strings, so White never runs out of columns
(`gameWCol_lt`); and at most half of a column can be blackened, so White never descends below
row `n / 2` (`game_row_bound`).  Since the board is finite and Black's moves accumulate
monotonically, White's position stabilises (`exists_game_winner`) at a cell `(x, R)`
that is *alive*: `C(x) ≥ R` and `C(R | x) ≥ log n - 1`.

White's whole play is computable, so the tokens she ever places at row `i` can be enumerated
(`gameRowEnum`), and there are at most `2 ^ (i + 2)` of them: those with `C(x) < i` are charged
to the `2 ^ i - 1` programs shorter than `i`, and of the rest there is at most one per board
(`gameRowEnum_length`), the boards reaching row `i` being the `n ≤ 2 * i`.  Reading the
enumeration off its index (`gameDecoder`) gives `C(x) ≤ R + 2 + O(1)` for every token, so for
the winning cell `C(x) = R + O(1)`, whence `C(C(x) | x) ≥ C(R | x) - O(1) ≥ log n - O(1)`. -/

/-- The maximum of a list of naturals (`0` on the empty list). -/
def gameMax (l : List ℕ) : ℕ := l.foldr max 0

/-- Every element of a list is at most its maximum. -/
lemma gameMax_le_of_mem : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ gameMax l := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons b bs ih =>
    intro a h
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

/-- The maximum of a non-empty list is one of its elements. -/
lemma gameMax_mem : ∀ {l : List ℕ}, l ≠ [] → gameMax l ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons b bs ih =>
    intro _
    rcases eq_or_ne bs [] with rfl | hbs
    · simp [gameMax]
    · have hb := ih hbs
      change max b (gameMax bs) ∈ b :: bs
      rcases le_total b (gameMax bs) with h | h
      · rw [max_eq_right h]; exact List.mem_cons_of_mem _ hb
      · rw [max_eq_left h]; exact List.mem_cons_self

/-- The maximum is monotone under inclusion of lists. -/
lemma gameMax_mono : ∀ {l1 l2 : List ℕ}, (∀ a ∈ l1, a ∈ l2) → gameMax l1 ≤ gameMax l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 _; exact Nat.zero_le _
  | cons b bs ih =>
    intro l2 h
    refine max_le (gameMax_le_of_mem (h b List.mem_cons_self)) ?_
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- The maximum of a list of naturals is primitive recursive. -/
lemma gameMax_primrec : Primrec gameMax := by
  have h : Primrec₂ (fun (_ : List ℕ) (p : ℕ × ℕ) => max p.1 p.2) :=
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) h

/-- Column `j` of board `n`: the `j`-th string of length `n`. -/
def gameCol (n j : ℕ) : BitString := (allStrings n).getD j []

/-- `⌊log₂ n⌋`, in a primitive recursive presentation. -/
def gameLog (n : ℕ) : ℕ := Nat.size n - 1

/-- The primitive recursive presentation `Nat.size n - 1` of the binary logarithm agrees with
`Nat.log 2 n`. -/
lemma gameLog_eq (n : ℕ) : gameLog n = Nat.log 2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gameLog]
  · have h1 : Nat.size n ≤ Nat.log 2 n + 1 := by
      rw [Nat.size_le]
      exact Nat.lt_pow_succ_log_self (by norm_num) n
    have h2 : ¬ (Nat.size n ≤ Nat.log 2 n) := by
      rw [Nat.size_le]
      exact Nat.not_lt.mpr (Nat.pow_log_le_self 2 hn.ne')
    unfold gameLog
    omega

/-- Black token strictly below row `r` in column `x`, discovered within `T` steps. -/
def gameDead (c : Code) (x : BitString) (r T : ℕ) : Bool :=
  decide (0 < r) && hitAt c (r - 1) T x []

/-- Cell `(x, i)` of board `n` blackened within `T` steps. -/
def gameBlack (c : Code) (n : ℕ) (x : BitString) (i T : ℕ) : Bool :=
  hitAt c (gameLog n - 2) T (Nat.bits i) x

/-- The non-blackened rows of column `x` of board `n` at stage `T`. -/
def gameFree (c : Code) (n : ℕ) (x : BitString) (T : ℕ) : List ℕ :=
  (List.range n).filter (fun r => !gameBlack c n x r T)

/-- The topmost non-blackened row of column `x` of board `n` at stage `T`. -/
def gameTop (c : Code) (n : ℕ) (x : BitString) (T : ℕ) : ℕ :=
  gameMax (gameFree c n x T)

/-- White's column index on board `n` at stage `T`. -/
def gameWCol (c : Code) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | T + 1 =>
      if gameDead c (gameCol n (gameWCol c n T))
          (gameTop c n (gameCol n (gameWCol c n T)) T) (T + 1)
        then gameWCol c n T + 1 else gameWCol c n T

/-- The column White plays on board `n` at stage `T`. -/
def gameStr (c : Code) (n T : ℕ) : BitString := gameCol n (gameWCol c n T)

/-- The row of White's token on board `n` at stage `T`. -/
def gameRow (c : Code) (n T : ℕ) : ℕ := gameTop c n (gameStr c n T) T

/-- The white tokens sitting at row `i` at stage `T`, over the boards `n ≤ 2 * i`. -/
def gameTokens (c : Code) (i T : ℕ) : List BitString :=
  ((List.range (2 * i + 1)).filterMap
    (fun n => if gameRow c n T = i then some (gameStr c n T) else none)).dedup

/-- All white tokens ever placed at row `i`, in order of first appearance. -/
def gameRowEnum (c : Code) (i : ℕ) : ℕ → List BitString
  | 0 => []
  | T + 1 => gameRowEnum c i T ++
      (gameTokens c i T).filter (fun x => !(decide (x ∈ gameRowEnum c i T)))

/-- The decompressor that reads off the row enumeration. -/
def gameDecoder (c : Code) : Map := fun pr =>
  (Nat.rfind (fun T => Part.some (decide (decodeFixedWidthNatCode pr.1 <
      (gameRowEnum c (pr.1.length - 2) T).length)))).map
    (fun T => (gameRowEnum c (pr.1.length - 2) T).getD (decodeFixedWidthNatCode pr.1) [])

/-! ### Primitive recursiveness of the Exercise 45 constructions -/

/-- The `j`-th column of board `n` is primitive recursive in `n` and `j`. -/
lemma gameCol_primrec : Primrec₂ gameCol :=
  (Primrec.list_getD ([] : BitString)).comp
    (allStrings_primrec.comp Primrec.fst) Primrec.snd

/-- The predicate saying that a column carries a black token below a given row is primitive
recursive in the column, the row and the stage. -/
lemma gameDead_primrec (c : Code) :
    Primrec (fun q : (BitString × ℕ) × ℕ => gameDead c q.1.1 q.1.2 q.2) := by
  unfold gameDead
  refine Primrec.and.comp ?_ ?_
  · exact primrec_decide_of_primrecPred
      (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.snd.comp Primrec.fst))
  · exact (hitAt_primrec c).comp
      (g := fun q : (BitString × ℕ) × ℕ => ((q.1.2 - 1, q.2), (q.1.1, ([] : BitString))))
      (Primrec.pair
        (Primrec.pair
          (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))
          Primrec.snd)
        (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.const [])))

private lemma gameLog_primrec : Primrec gameLog :=
  Primrec.nat_sub.comp natSize_primrec (Primrec.const 1)

private lemma gameBlack_primrec (c : Code) :
    Primrec (fun q : (ℕ × BitString) × ℕ × ℕ => gameBlack c q.1.1 q.1.2 q.2.1 q.2.2) := by
  unfold gameBlack
  exact (hitAt_primrec c).comp
    (g := fun q : (ℕ × BitString) × ℕ × ℕ =>
      ((gameLog q.1.1 - 2, q.2.2), (Nat.bits q.2.1, q.1.2)))
    (Primrec.pair
      (Primrec.pair
        (Primrec.nat_sub.comp (gameLog_primrec.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.const 2))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.pair (primrec_natBits.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)))

/-- The list of non-blackened rows of a column is primitive recursive in the board, the column
and the stage. -/
lemma gameFree_primrec (c : Code) :
    Primrec (fun q : (ℕ × BitString) × ℕ => gameFree c q.1.1 q.1.2 q.2) := by
  unfold gameFree
  refine list_filter_primrec (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.not.comp ?_)
  exact (gameBlack_primrec c).comp
    (g := fun z : ((ℕ × BitString) × ℕ) × ℕ => ((z.1.1.1, z.1.1.2), (z.2, z.1.2)))
    (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))

end Kolmogorov


