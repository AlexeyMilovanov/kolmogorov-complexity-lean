import KolmogorovMathlib.StrongMerging.Upper.Decoders
import KolmogorovMathlib.StrongMerging.Upper.Residual
import KolmogorovMathlib.StrongMerging.Upper.Selector

/-!
# Leaves of the trade-off assembly

The calibrated integer instance, the arithmetic and coding leaves, and the real
arithmetic (pure inequalities between real variables) of the assembly of H06 and H07.

Part of `KolmogorovMathlib.StrongMerging.Upper.Tradeoff`, which imports it.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### The calibrated integer instance -/

/-- A calibrated integer instance of the merging theorems: `n ≥ 2`, `e ≤ n`, `|x| = n`, `A, B` are
`e`-sufficient for `x`, and `p_A, p_B` are total witnesses of length `≤ e` producing the codes of
`A, B` from `x`. -/
structure CalInstance (V : Map) (n e : ℕ) (x : BitString) (A B : Finset BitString)
    (pA pB : BitString) : Prop where
  /-- The data length is at least two. -/
  two_le : 2 ≤ n
  /-- The integer budget is at most the data length. -/
  e_le : e ≤ n
  /-- `x` has length `n`. -/
  len : x.length = n
  /-- `A` is `e`-sufficient for `x`. -/
  suffA : IsSufficientModel V x A e
  /-- `B` is `e`-sufficient for `x`. -/
  suffB : IsSufficientModel V x B e
  /-- The row witness is total. -/
  totA : IsTotalProgram universalDecompressor pA
  /-- The column witness is total. -/
  totB : IsTotalProgram universalDecompressor pB
  /-- The row witness has length at most `e`. -/
  lenA : pA.length ≤ e
  /-- The column witness has length at most `e`. -/
  lenB : pB.length ≤ e
  /-- The row witness produces the code of `A` from `x`. -/
  outA : canonicalFiniteSetCode A ∈ universalDecompressor (pA, x)
  /-- The column witness produces the code of `B` from `x`. -/
  outB : canonicalFiniteSetCode B ∈ universalDecompressor (pB, x)

/-- **Integer calibration** (tex ~118, node H07 obligation "handle real ε by integer ceiling").  A
real-tolerance merging instance is a calibrated integer instance at `e = ⌈ε⌉`: strength gives
total witnesses of length `≤ ⌊ε⌋ ≤ ⌈ε⌉`, and sufficiency is monotone in the tolerance. -/
theorem exists_calInstance {V : Map} {n : ℕ} {ε : ℝ} {x : BitString} {A B : Finset BitString}
    (h : IsMergingInstance V n ε x A B) : ∃ pA pB, CalInstance V n ⌈ε⌉₊ x A B pA pB := by
  obtain ⟨hn, -, hεn, hx, hsA, hfA, hsB, hfB⟩ := h
  obtain ⟨pA, hpA, hlA, hoA⟩ := Lower.exists_totalProgram_of_isStrongModel hsA
  obtain ⟨pB, hpB, hlB, hoB⟩ := Lower.exists_totalProgram_of_isStrongModel hsB
  have hfc : ⌊ε⌋₊ ≤ ⌈ε⌉₊ := Nat.floor_le_ceil ε
  have hce : ε ≤ ⌈ε⌉₊ := Nat.le_ceil ε
  have hcn : ⌈ε⌉₊ ≤ n := Nat.ceil_le.mpr hεn
  exact ⟨pA, pB, ⟨hn, hcn, hx, ⟨hfA.1, by linarith [hfA.2]⟩, ⟨hfB.1, by linarith [hfB.2]⟩, hpA,
    hpB, hlA.trans hfc, hlB.trans hfc, hoA, hoB⟩⟩

/-! ### Arithmetic leaves -/

/-- `n < (⌊n / R⌋ + 1) R` for `R ≥ 1`: the depth `J = ⌊n / R⌋ + 1` exhausts the size bound. -/
theorem lt_div_add_one_mul {n R : ℕ} (hR : 1 ≤ R) : n < (n / R + 1) * R := by
  have h := Nat.lt_div_mul_add (a := n) (b := R) (by omega)
  rw [Nat.add_mul, one_mul]
  exact h

/-- `⌈log₂ (n + 2)⌉ ≥ 2` for `n ≥ 2`, so `H ≥ 2`. -/
theorem two_le_headerLog {n : ℕ} (hn : 2 ≤ n) : 2 ≤ headerLog n := by
  unfold headerLog
  have h4 : Nat.clog 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.clog_pow 2 2 one_lt_two]
  rw [← h4]
  exact Nat.clog_mono_right 2 (by omega)

/-- `⌈log₂ (n + 2)⌉ ≤ n` for `n ≥ 2` (used for `H ≤ 2n`, tex ~525 "`H = O(n)`"). -/
theorem headerLog_le_self {n : ℕ} (hn : 2 ≤ n) : headerLog n ≤ n := by
  unfold headerLog
  rw [Nat.clog_le_iff_le_pow one_lt_two]
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

/-- The base budget `H = e + ⌈log₂ (n + 2)⌉` satisfies `2 ≤ H ≤ 2n` for `n ≥ 2`, `e ≤ n`. -/
theorem baseBudget_bounds {n e : ℕ} (hn : 2 ≤ n) (he : e ≤ n) :
    2 ≤ baseBudget n e ∧ baseBudget n e ≤ 2 * n := by
  have h1 := two_le_headerLog hn
  have h2 := headerLog_le_self hn
  unfold baseBudget
  omega

/-- **Linear arguments of logarithms are `O(H)`.**  For every `β` there is `k` with
`log₂ (β (n + 1) + 2) ≤ k H` for all `n ≥ 2`, `e ≤ n`. -/
theorem logb_le_baseBudget (β : ℕ) :
    ∃ k : ℕ, ∀ n e : ℕ, Real.logb 2 ((β : ℝ) * (n + 1) + 2) ≤ k * baseBudget n e := by
  obtain ⟨c, hc⟩ := logb_linear_le_headerLog β β
  refine ⟨c, fun n e => ?_⟩
  have h := hc n
  have heq : (β : ℝ) * (n + 1) + 2 = (β : ℝ) * n + β + 2 := by ring
  rw [heq]
  refine h.trans ?_
  have : (headerLog n : ℝ) ≤ baseBudget n e := by
    unfold baseBudget
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) e]
  exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg c)

/-- **The accumulated depth loss** (tex ~478): `JL = (⌊n / R⌋ + 1) c₂ H ≤ c₂ (H + n H / R)` for
`R ≥ 1`, with real division on the right. -/
theorem depthLoss_le (c₂ H n R : ℕ) (hR : 1 ≤ R) :
    (((n / R + 1) * (c₂ * H) : ℕ) : ℝ) ≤ c₂ * (H + n * H / R) := by
  have hdiv : ((n / R : ℕ) : ℝ) ≤ (n : ℝ) / R := Nat.cast_div_le
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hc : (0 : ℝ) ≤ c₂ := Nat.cast_nonneg c₂
  have h1 : (n : ℝ) * H / R = (n : ℝ) / R * H := by ring
  rw [h1]
  push_cast
  have h2 : ((n / R : ℕ) : ℝ) * H ≤ (n : ℝ) / R * H := mul_le_mul_of_nonneg_right hdiv hH
  nlinarith

/-- **Header cost in the calibrated instance.**  For a bucket slack `β` there is `k` such that the
header fields of the local decoder cost `hdrCost [n, a, b, R, c₂ H, j, |p_A|, |p_B|] ≤ k H +
⌈log₂ (c₂ + 2)⌉` whenever `n ≥ 2`, `e ≤ n`, `a, b ≤ 2n + β`, `R, j ≤ n`, `|p_A|, |p_B| ≤ e`.

Proof sketch: `headerLog` is monotone (`Nat.clog_mono_right`); `headerLog m ≤ headerLog n +
headerLog β' + 1` for `m ≤ β' (n + 1)` (`Nat.clog` of a product, `Nat.clog_le_iff_le_pow`);
`headerLog (c₂ H) ≤ headerLog c₂ + headerLog H` since `c₂ H + 2 ≤ (c₂ + 2)(H + 2)`, and
`headerLog H ≤ H` (`headerLog_le_self`, `H ≥ 2`); finally `headerLog n ≤ H`. -/
theorem hdrCost_le (β : ℕ) :
    ∃ k : ℕ, ∀ (c₂ n e a b R j : ℕ) (pA pB : BitString), 2 ≤ n → e ≤ n → a ≤ 2 * n + β →
      b ≤ 2 * n + β → R ≤ n → j ≤ n → pA.length ≤ e → pB.length ≤ e →
        hdrCost [n, a, b, R, c₂ * baseBudget n e, j, pA.length, pB.length] ≤
          k * baseBudget n e + headerLog c₂ := by
  refine ⟨12 + 2 * headerLog β, fun c₂ n e a b R j pA pB hn he ha hb hR hj hpA hpB => ?_⟩
  obtain ⟨hH2, -⟩ := baseBudget_bounds hn he
  have hnH : headerLog n ≤ baseBudget n e := by unfold baseBudget; omega
  have hmono : ∀ m, m ≤ n → headerLog m ≤ baseBudget n e := fun m hm =>
    (headerLog_mono hm).trans hnH
  have h2 : headerLog 2 = 2 := by
    unfold headerLog
    rw [show (2 + 2 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.clog_pow 2 2 one_lt_two
  have hp : headerLog β ≤ headerLog β * baseBudget n e := Nat.le_mul_of_pos_right _ (by omega)
  have hab : ∀ m, m ≤ 2 * n + β → headerLog m ≤ (3 + headerLog β) * baseBudget n e := by
    intro m hm
    have h1 := headerLog_mono hm
    have h3 := headerLog_add_le (2 * n) β
    have h4 := headerLog_mul_le 2 n
    rw [h2] at h4
    rw [Nat.add_mul]
    omega
  have hL : headerLog (c₂ * baseBudget n e) ≤ headerLog c₂ + baseBudget n e :=
    (headerLog_mul_le _ _).trans (by have := headerLog_le_self hH2; omega)
  simp only [hdrCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hR' := hmono R hR
  have hj' := hmono j hj
  have hA' := hmono _ (hpA.trans he)
  have hB' := hmono _ (hpB.trans he)
  have ha' := hab a ha
  have hb' := hab b hb
  rw [Nat.add_mul] at ha' hb' ⊢
  rw [Nat.mul_assoc]
  omega

/-- The real binary logarithm of a positive cardinality is below its floor bucket plus one:
`log₂ |A| < ⌊log₂ |A|⌋ + 1` (the ordinal of `x` in the smaller model costs `a + O(1)` bits,
tex ~322). -/
theorem logb_card_lt_log_add_one {A : Finset BitString} (hA : A.Nonempty) :
    Real.logb 2 A.card < Nat.log 2 A.card + 1 := by
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  rw [Real.logb_lt_iff_lt_rpow one_lt_two hpos]
  have h := Nat.lt_pow_succ_log_self (b := 2) one_lt_two A.card
  have e : ((Nat.log 2 A.card : ℝ) + 1) = ((Nat.log 2 A.card + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast]
  exact_mod_cast h

/-! ### Coding leaves -/

/-- **Identity reduction**: `CT(u | u) ≤ c`. -/
theorem totalC_self_le : ∃ c : ℕ, ∀ u : BitString, totalC u u ≤ c := by
  have hD : isDecompressor (fun q : BitString × BitString => Part.some q.2) :=
    Computable.snd.partrec
  obtain ⟨c, hc⟩ := totalC_le_of_decoder _ hD
  refine ⟨c, fun u => ?_⟩
  have h := hc [] (fun _ => trivial) u u (Part.mem_some u)
  simpa using h

/-- **Total index in a model**: a member `x` of a finite model `A` has
`CT(x | A) ≤ log₂ |A| + c` (the index decoder `reductionSetIndexDecompressor` is total). -/
theorem totalC_index_le : ∃ c : ℕ, ∀ (A : Finset BitString) (x : BitString), x ∈ A →
    totalC x (canonicalFiniteSetCode A) ≤ Real.logb 2 A.card + c := by
  obtain ⟨c, hc⟩ := totalC_le_of_decoder reductionSetIndexDecompressor
    reductionSetIndexDecompressor_partrec
  refine ⟨c + 1, fun A x hx => ?_⟩
  obtain ⟨r, hr, hlen⟩ := exists_index_program A x hx
  have h := hc r (fun _ => trivial) _ x hr
  have hcl := clog_le_logb_add_one A.card
  rw [hlen] at h
  push_cast
  linarith

/-- **Swapping a pair costs a constant**: `C(u, v) ≤ C(v, u) + c`. -/
theorem pairC_swap_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, pairC V u v ≤ pairC V v u + c := by
  obtain ⟨c, hc⟩ := plainK_map_le V hV swapPairCode swapPairCode_computable
  refine ⟨c, fun u v => ?_⟩
  have h := hc (pairCode v u)
  rw [swapPairCode_pairCode] at h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV (pairCode v u))
  have h1 : plainK V (pairCode u v) ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have h2 : pairC V v u = k := by rw [pairC, plainC, ← hk, ENat.toNat_natCast]
  rw [h2]
  unfold pairC plainC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **A crude logarithm bound**: `log₂ (t + 2) ≤ 2 t + 2` for `t ≥ 0`.

`Real.log_le_sub_one_of_pos` gives `log (t + 2) ≤ t + 1` and `log 2 ≥ 1/2`. -/
theorem logb_add_two_le {t : ℝ} (ht : 0 ≤ t) : Real.logb 2 (t + 2) ≤ 2 * t + 2 := by
  have h1 : Real.log (t + 2) ≤ t + 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < t + 2)
    linarith
  have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have h' : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
    linarith
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t + 2)
    (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 2)]

/-- **Affine arguments of logarithms**: for naturals `a, b` there is `k` with
`log₂ (a N + b + 2) ≤ k log₂ (N + 2)` for all real `N ≥ 0`. -/
theorem logb_affine_le (a b : ℕ) :
    ∃ k : ℕ, ∀ N : ℝ, 0 ≤ N → Real.logb 2 ((a : ℝ) * N + b + 2) ≤ k * Real.logb 2 (N + 2) := by
  refine ⟨⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ + 1, fun N hN => ?_⟩
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have h1 : (a : ℝ) * N + b + 2 ≤ ((a : ℝ) + b + 2) * (N + 2) := by nlinarith
  have h2 : Real.logb 2 ((a : ℝ) * N + b + 2) ≤
      Real.logb 2 ((a : ℝ) + b + 2) + Real.logb 2 (N + 2) := by
    rw [← Real.logb_mul (by positivity) (by positivity)]
    exact Real.logb_le_logb_of_le one_lt_two (by positivity) h1
  have h5 : Real.logb 2 ((a : ℝ) + b + 2) ≤ ⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ := Nat.le_ceil _
  have hl1 := one_le_logb_add_two hN
  have hC0 : (0 : ℝ) ≤ ⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ := Nat.cast_nonneg _
  have h6 : (⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ : ℝ) ≤
      ⌈Real.logb 2 ((a : ℝ) + b + 2)⌉₊ * Real.logb 2 (N + 2) := le_mul_of_one_le_right hC0 hl1
  push_cast
  linarith

/-- **The fallback reduction** (tex ~322): if `x ∈ A` and a total program `p` produces `u` from
`x`, then `CT(u | A) ≤ log₂ |A| + |p| + 2 log₂ (log₂ |A| + 2) + c`: index `x` in `A`
(`totalC_index_le`) and run `p`, composed by `Lower.totalC_trans`. -/
theorem totalC_fallback_le :
    ∃ c : ℕ, ∀ (x : BitString) (A : Finset BitString) (p u : BitString), x ∈ A →
      IsTotalProgram universalDecompressor p → u ∈ universalDecompressor (p, x) →
        totalC u (canonicalFiniteSetCode A) ≤
          Real.logb 2 A.card + p.length + 2 * Real.logb 2 (Real.logb 2 A.card + 2) + c := by
  obtain ⟨ctr, htr⟩ := Lower.totalC_trans
  obtain ⟨ci, hci⟩ := totalC_index_le
  refine ⟨ci + ctr + 2 * ⌈Real.logb 2 ((ci : ℝ) + 1)⌉₊, fun x A p u hx hp hu => ?_⟩
  have h1 := htr (canonicalFiniteSetCode A) x u
  have h2 := hci A x hx
  have h3 := Lower.totalC_le_length_of_totalProgram hp hu
  have ht0 : 0 ≤ Real.logb 2 A.card := logb_card_nonneg_of_mem hx
  have hT0 := totalC_nonneg x (canonicalFiniteSetCode A)
  have hci0 : (0 : ℝ) ≤ ci := Nat.cast_nonneg ci
  have h4 : Real.logb 2 (totalC x (canonicalFiniteSetCode A) + 2) ≤
      Real.logb 2 (Real.logb 2 A.card + 2) + Real.logb 2 ((ci : ℝ) + 1) := by
    rw [← Real.logb_mul (by positivity) (by positivity)]
    apply Real.logb_le_logb_of_le one_lt_two (by positivity)
    nlinarith
  have h5 : Real.logb 2 ((ci : ℝ) + 1) ≤ ⌈Real.logb 2 ((ci : ℝ) + 1)⌉₊ := Nat.le_ceil _
  push_cast
  linarith

/-- **Score from conditional deficiency** (tex ~468 and ~2760): for every finite `D` and string
`x` with `C(x) + C(D | x) ≤ N`,
`Score(D, x) ≤ (log₂ |D| - C(x | D)) + C(D | x) + c log₂ (N + 2)`.  The chain rules are applied
in the two orders to the pair `(D, x)`; every joint complexity is `O(N + 1)`. -/
theorem modelScore_le_of_deficiency (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (N : ℝ) (x : BitString) (D : Finset BitString),
      plainC V x + condC V (canonicalFiniteSetCode D) x ≤ N →
        modelScore V D x ≤ Real.logb 2 D.card - condC V x (canonicalFiniteSetCode D) +
          condC V (canonicalFiniteSetCode D) x + c * Real.logb 2 (N + 2) := by
  obtain ⟨c₁, h₁⟩ := upperComplexityChain_lower V hV
  obtain ⟨c₂, h₂⟩ := upperComplexityChain_upper V hV
  obtain ⟨c₃, h₃⟩ := upperComplexityChain_trans V hV
  obtain ⟨csw, hsw⟩ := pairC_swap_le V hV
  obtain ⟨ccr, hcr⟩ := pairC_le_crude V hV
  obtain ⟨k, hk⟩ := logb_affine_le (4 + 6 * c₃) (6 * c₃ + ccr)
  refine ⟨c₁ * k + c₂ * k + csw, fun N x D hN => ?_⟩
  have hx0 := plainC_nonneg V x
  have hdx0 := condC_nonneg V (canonicalFiniteSetCode D) x
  have hN0 : 0 ≤ N := by linarith
  have hL1 := one_le_logb_add_two hN0
  have hc₃ : (0 : ℝ) ≤ c₃ := Nat.cast_nonneg c₃
  have hccr : (0 : ℝ) ≤ ccr := Nat.cast_nonneg ccr
  -- `C(D) = O(N + 1)`
  have hD : plainC V (canonicalFiniteSetCode D) ≤ plainC V x +
      condC V (canonicalFiniteSetCode D) x + c₃ * Real.logb 2
        (plainC V x + condC V (canonicalFiniteSetCode D) x + 2) :=
    h₃ (canonicalFiniteSetCode D) x []
  have hlg : Real.logb 2 (plainC V x + condC V (canonicalFiniteSetCode D) x + 2) ≤ 2 * N + 2 :=
    (logb_add_two_mono (by linarith) hN).trans (logb_add_two_le hN0)
  have hlg' := mul_le_mul_of_nonneg_left hlg hc₃
  -- the two joint complexities are `≤ a N + b`
  have hxD := hcr x (canonicalFiniteSetCode D)
  have hDx := hcr (canonicalFiniteSetCode D) x
  have hbound : ∀ s : ℝ, 0 ≤ s → s ≤ ((4 + 6 * c₃ : ℕ) : ℝ) * N + ((6 * c₃ + ccr : ℕ) : ℝ) →
      Real.logb 2 (s + 2) ≤ k * Real.logb 2 (N + 2) := fun s hs hsN =>
    (logb_add_two_mono hs hsN).trans (hk N hN0)
  have hc₃N : (0 : ℝ) ≤ c₃ * N := mul_nonneg hc₃ hN0
  have hlxD := hbound (pairC V x (canonicalFiniteSetCode D)) (pairC_nonneg V _ _)
    (by push_cast; nlinarith)
  have hlDx := hbound (pairC V (canonicalFiniteSetCode D) x) (pairC_nonneg V _ _)
    (by push_cast; nlinarith)
  have e1 := h₁ (canonicalFiniteSetCode D) x
  have e2 := hsw (canonicalFiniteSetCode D) x
  have e3 := h₂ x (canonicalFiniteSetCode D)
  have hc₁ : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg c₁
  have hc₂ : (0 : ℝ) ≤ c₂ := Nat.cast_nonneg c₂
  have m1 := mul_le_mul_of_nonneg_left hlDx hc₁
  have m2 := mul_le_mul_of_nonneg_left hlxD hc₂
  have hcsw : (csw : ℝ) ≤ csw * Real.logb 2 (N + 2) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hL1
  unfold modelScore setC
  push_cast
  nlinarith

/-- **Joint complexities of the selected model** (tex ~474, "Logical order of the score
estimate"): once `CT(D | x) ≤ T₀` is known, `C(D)`, `C(D, x)`, `C(A, D)`, `C(B, D)` are
`O(n + 1 + T₀)` for `e`-sufficient `A, B` of the `n`-bit `x`, `e ≤ n`. -/
theorem jointBounds_of_point (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n e : ℕ) (T₀ : ℝ) (x : BitString) (A B D : Finset BitString),
      x.length = n → e ≤ n → IsSufficientModel V x A e → IsSufficientModel V x B e →
      0 ≤ T₀ → pointTotalC D x ≤ T₀ →
        setC V D ≤ c * (n + 1 + T₀) ∧ pairC V (canonicalFiniteSetCode D) x ≤ c * (n + 1 + T₀) ∧
          setPairC V A D ≤ c * (n + 1 + T₀) ∧ setPairC V B D ≤ c * (n + 1 + T₀) := by
  obtain ⟨c₃, h₃⟩ := upperComplexityChain_trans V hV
  obtain ⟨ct, hct⟩ := condC_le_totalC_add V hV
  obtain ⟨blit, hblit⟩ := plainC_le_length_add V hV
  obtain ⟨ccr, hcr⟩ := pairC_le_crude V hV
  refine ⟨4 * ((1 + 2 * c₃) * (2 + blit + ct) + 2 * c₃) + 4 * blit + ccr + 7,
    fun n e T₀ x A B D hx he hA hB hT₀ hpt => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc₃ : (0 : ℝ) ≤ c₃ := Nat.cast_nonneg c₃
  have hct0 : (0 : ℝ) ≤ ct := Nat.cast_nonneg ct
  have hbl : (0 : ℝ) ≤ blit := Nat.cast_nonneg blit
  have hcr0 : (0 : ℝ) ≤ ccr := Nat.cast_nonneg ccr
  have he' : (e : ℝ) ≤ n := by exact_mod_cast he
  have hM1 : (1 : ℝ) ≤ n + 1 + T₀ := by linarith
  -- the basic bounds
  have hCx : plainC V x ≤ n + blit := by
    have := hblit x
    rw [hx] at this
    exact this
  have hCDx : condC V (canonicalFiniteSetCode D) x ≤ T₀ + ct := by
    have h1 := hct (canonicalFiniteSetCode D) x
    have h2 : totalC (canonicalFiniteSetCode D) x ≤ T₀ := hpt
    linarith
  have hx0 := plainC_nonneg V x
  have hdx0 := condC_nonneg V (canonicalFiniteSetCode D) x
  have hD : plainC V (canonicalFiniteSetCode D) ≤ plainC V x +
      condC V (canonicalFiniteSetCode D) x + c₃ * Real.logb 2
        (plainC V x + condC V (canonicalFiniteSetCode D) x + 2) :=
    h₃ (canonicalFiniteSetCode D) x []
  have hlg := logb_add_two_le (add_nonneg hx0 hdx0)
  have hlg' := mul_le_mul_of_nonneg_left hlg hc₃
  -- `C(D) ≤ K₁ M` with `M = n + 1 + T₀`
  have hs : plainC V x + condC V (canonicalFiniteSetCode D) x ≤
      (2 + blit + ct) * (n + 1 + T₀) := by nlinarith
  have hK₁ : setC V D ≤ ((1 + 2 * c₃) * (2 + blit + ct) + 2 * c₃) * (n + 1 + T₀) := by
    change plainC V (canonicalFiniteSetCode D) ≤ _
    have h1 : (1 + 2 * (c₃ : ℝ)) * (plainC V x + condC V (canonicalFiniteSetCode D) x) ≤
        (1 + 2 * c₃) * ((2 + blit + ct) * (n + 1 + T₀)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith
  have hAx := setC_le_of_sufficient hA
  have hBx := setC_le_of_sufficient hB
  have hA0 := plainC_nonneg V (canonicalFiniteSetCode A)
  have hB0 := plainC_nonneg V (canonicalFiniteSetCode B)
  have hK₁0 : (0 : ℝ) ≤ ((1 + 2 * c₃) * (2 + blit + ct) + 2 * c₃) := by positivity
  have p1 := hcr (canonicalFiniteSetCode D) x
  have p2 := hcr (canonicalFiniteSetCode A) (canonicalFiniteSetCode D)
  have p3 := hcr (canonicalFiniteSetCode B) (canonicalFiniteSetCode D)
  have hD0 := plainC_nonneg V (canonicalFiniteSetCode D)
  have hcrM : (ccr : ℝ) ≤ ccr * (n + 1 + T₀) := le_mul_of_one_le_right hcr0 hM1
  have hblM : (blit : ℝ) ≤ blit * (n + 1 + T₀) := le_mul_of_one_le_right hbl hM1
  have hK₁M : (0 : ℝ) ≤ ((1 + 2 * c₃) * (2 + blit + ct) + 2 * c₃) * (n + 1 + T₀) := by
    positivity
  change plainC V (canonicalFiniteSetCode D) ≤ _ at hK₁
  change plainC V (canonicalFiniteSetCode A) ≤ _ at hAx
  change plainC V (canonicalFiniteSetCode B) ≤ _ at hBx
  refine ⟨?_, ?_, ?_, ?_⟩
  · change plainC V (canonicalFiniteSetCode D) ≤ _
    push_cast
    nlinarith
  · push_cast
    nlinarith
  · change pairC V (canonicalFiniteSetCode A) (canonicalFiniteSetCode D) ≤ _
    push_cast
    nlinarith
  · change pairC V (canonicalFiniteSetCode B) (canonicalFiniteSetCode D) ≤ _
    push_cast
    nlinarith

/-! ### Real arithmetic of the assembly (pure inequalities between real variables) -/

/-- Arithmetic of the fallback endpoint bound. -/
theorem arith_fallback {t L₂ p lam a JL e H kl cfb K : ℝ} (h1 : t ≤ L₂ + p + 2 * lam + cfb)
    (h2 : L₂ < a + 1) (h3 : lam ≤ kl * H) (h4 : a ≤ JL) (h5 : p ≤ e) (h6 : e ≤ H)
    (hH : 1 ≤ H) (hcfb : 0 ≤ cfb) (hK : 2 + 2 * kl + cfb ≤ K) : t ≤ JL + K * H := by
  have hK' := mul_le_mul_of_nonneg_right hK (by linarith : (0 : ℝ) ≤ H)
  have hc := mul_nonneg hcfb (by linarith : (0 : ℝ) ≤ H - 1)
  nlinarith

/-- Arithmetic of a constant endpoint bound. -/
theorem arith_const {t c JL H K : ℝ} (h1 : t ≤ c) (hJL : 0 ≤ JL) (hH : 1 ≤ H) (hc : 0 ≤ c)
    (hK : c ≤ K) : t ≤ JL + K * H := by
  have hK' := mul_le_mul_of_nonneg_right hK (by linarith : (0 : ℝ) ≤ H)
  have hc' := mul_nonneg hc (by linarith : (0 : ℝ) ≤ H - 1)
  nlinarith

/-- Arithmetic of the sufficiency score in the small-degree branch. -/
theorem arith_score_small {s e H R K : ℝ} (h1 : s ≤ e) (h2 : e ≤ H) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hK : 1 ≤ K) : s ≤ R + K * H := by
  have := mul_le_mul_of_nonneg_right hK hH
  linarith

/-- Arithmetic of the sufficiency score in the hierarchy branch. -/
theorem arith_score_big {s d y lg R H cpt ct cskl K : ℝ} (h1 : s ≤ d + y + lg) (h2 : d ≤ R + 3)
    (h3 : y ≤ cpt * H + ct) (h4 : lg ≤ cskl * H) (hH : 1 ≤ H) (hct : 0 ≤ ct)
    (hK : 3 + cpt + ct + cskl ≤ K) : s ≤ R + K * H := by
  have hK' := mul_le_mul_of_nonneg_right hK (by linarith : (0 : ℝ) ≤ H)
  have hc := mul_nonneg hct (by linarith : (0 : ℝ) ≤ H - 1)
  nlinarith

/-- Arithmetic of the local-decoder endpoint bound in the hierarchy branch. -/
theorem arith_endpoint_big {t jL JL pA pB e H cloc hc kh h₂ K : ℝ}
    (h1 : t ≤ jL + pA + pB + cloc * (hc + 1)) (h2 : jL ≤ JL) (h3 : pA ≤ e) (h4 : pB ≤ e)
    (h5 : e ≤ H) (h6 : hc ≤ kh * H + h₂) (hH : 1 ≤ H) (hcloc : 0 ≤ cloc) (hh₂ : 0 ≤ h₂)
    (hK : 2 + cloc * (kh + h₂ + 1) ≤ K) : t ≤ JL + K * H := by
  have e1 : hc + 1 ≤ (kh + h₂ + 1) * H := by nlinarith
  have e2 := mul_le_mul_of_nonneg_left e1 hcloc
  have e3 := mul_le_mul_of_nonneg_right hK (by linarith : (0 : ℝ) ≤ H)
  nlinarith

/-- Arithmetic of the joint-complexity budget of the score chain rule. -/
theorem arith_N {cx cf n blit ct cpt H : ℝ} (h1 : cx ≤ n + blit) (h2 : cf ≤ cpt * H + ct)
    (h3 : H ≤ 2 * n) (hn : 0 ≤ n) (hblit : 0 ≤ blit) (hct : 0 ≤ ct) (hcpt : 0 ≤ cpt) :
    cx + cf ≤ (blit + ct + 2 * cpt + 2) * (n + 1) := by
  have := mul_le_mul_of_nonneg_left h3 hcpt
  nlinarith

/-- Arithmetic of the joint-complexity budget of the mass transfer. -/
theorem arith_joint {n H bj cj cpt : ℝ} (hH : H ≤ 2 * n) (hn : 0 ≤ n) (hbj : 0 ≤ bj)
    (hcj : 0 ≤ cj) (hcpt : 0 ≤ cpt) :
    cj * (n + 1 + cpt * H) ≤ (bj + cj) * (1 + 2 * cpt) * (n + 1) ∧
      bj * (n + 1) ≤ (bj + cj) * (1 + 2 * cpt) * (n + 1) := by
  have h1 := mul_le_mul_of_nonneg_left hH hcpt
  have h2 := mul_le_mul_of_nonneg_left h1 hcj
  constructor
  · nlinarith [mul_nonneg hcj hcpt, mul_nonneg (mul_nonneg hcj hcpt) hn, mul_nonneg hbj hcpt,
      mul_nonneg (mul_nonneg hbj hcpt) hn, mul_nonneg hbj hn]
  · nlinarith [mul_nonneg hcj hcpt, mul_nonneg (mul_nonneg hcj hcpt) hn, mul_nonneg hbj hcpt,
      mul_nonneg (mul_nonneg hbj hcpt) hn, mul_nonneg hcj hn]

/-- Arithmetic of the final conversion to the tradeoff bounds, with
`C = 2 c₂ + 2 k + 2 + c_m k_l + 1`. -/
theorem arith_tradeoff {R H Q e c₂ k cm kl s tA tB m : ℝ} (hR : 0 ≤ R) (hH : 1 ≤ H)
    (hQ : 0 ≤ Q) (he : e ≤ H) (hc₂ : 0 ≤ c₂) (hk : 0 ≤ k) (hcm : 0 ≤ cm) (hkl : 0 ≤ kl)
    (hs : s ≤ R + k * H) (htA : tA ≤ c₂ * (H + Q) + k * H) (htB : tB ≤ c₂ * (H + Q) + k * H)
    (hm : m ≤ 2 * (c₂ * (H + Q) + k * H) + 2 * e + cm * (kl * H)) :
    s ≤ (2 * c₂ + 2 * k + 2 + cm * kl + 1) * (R + H) ∧
      tA ≤ (2 * c₂ + 2 * k + 2 + cm * kl + 1) * (H + Q) ∧
      tB ≤ (2 * c₂ + 2 * k + 2 + cm * kl + 1) * (H + Q) ∧
      m ≤ (2 * c₂ + 2 * k + 2 + cm * kl + 1) * (H + Q) := by
  have hckl : 0 ≤ cm * kl := mul_nonneg hcm hkl
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have a1 := mul_nonneg hk hR
  have a2 := mul_nonneg hc₂ hR
  have a3 := mul_nonneg hckl hR
  have a4 := mul_nonneg hk hQ
  have a5 := mul_nonneg hc₂ hQ
  have a6 := mul_nonneg hckl hQ
  have a7 := mul_nonneg hc₂ hH0
  have a8 := mul_nonneg hckl hH0
  have a9 := mul_nonneg hk hH0
  have a10 : cm * (kl * H) = cm * kl * H := by ring
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end Kolmogorov.StrongMerging.Upper
