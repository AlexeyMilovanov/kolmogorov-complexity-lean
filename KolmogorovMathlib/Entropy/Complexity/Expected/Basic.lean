import KolmogorovMathlib.Entropy.Complexity.Basic
import KolmogorovMathlib.Entropy.Coding
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import KolmogorovMathlib.MonotoneComplexity.MonotoneComplexityBounds
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding
import KolmogorovMathlib.AlgorithmicRandomness.BlockMap
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.DyadicEnumeration

/-!
# The expected complexity of an i.i.d. word: Theorem 147

SUV Section 7.3.2, p. 228.

The expected value of `K(ξ^N | N)` is `N H(ξ) + O(1)`: the lower bound
`N H(ξ) ≤ E K(ξ^N | N)` (`mul_entropyDist_le_expect_KP`) is Shannon's bound for the prefix code
of shortest descriptions, and the upper bound (`exists_expect_KP_le_mul_entropyDist`), for
positive rational probabilities, compares `K` with a Shannon code computed from `N`.  The model
is described in the module docstring of `Entropy/Complexity/Expected.lean`.
-/

namespace Kolmogorov

open Finset

open scoped ENNReal

/-! ### Theorem 147 -/

/-- **Shannon's lower bound for a Kraft length function.**  If the lengths `l ω` satisfy Kraft's
inequality `∑ 2^{-l ω} ≤ 1`, the entropy of `μ` is at most the expected length.  SUV
Theorem 138(a). -/
theorem entropyDist_le_expect_of_kraft {Ω : Type*} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (l : Ω → ℕ)
    (hk : ∑ ω, (2 : ℝ)⁻¹ ^ l ω ≤ 1) :
    entropyDist μ.prob ≤ μ.expect fun ω => (l ω : ℝ) := by
  refine (entropyDist_le_sum_mul_neg_logb μ.prob_nonneg μ.sum_prob
    (q := fun ω => (2 : ℝ)⁻¹ ^ l ω) (fun _ => by positivity) hk).trans ?_
  unfold FiniteProbSpace.expect
  refine le_of_eq (Finset.sum_congr rfl fun ω _ => ?_)
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  ring

/-- The shortest descriptions of the block encodings of all words of length `N`, under one
condition `y`, form a prefix-free set, so their lengths satisfy Kraft's inequality. -/
theorem sum_inv_pow_KP_toNat_le_one (A : Type*) [Fintype A] [Encodable A]
    (U : Map) (hU : IsOptimalPrefixConditional U) (N : ℕ) (y : BitString) :
    ∑ w : Fin N → A, (2 : ℝ)⁻¹ ^ (KP U (finWordBits A w) y).toNat ≤ 1 := by
  classical
  obtain ⟨c₁, hc₁⟩ := KP_le_KPPlain U hU
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_length_add_log U hU
  have hfinite : ∀ w : Fin N → A, KP U (finWordBits A w) y ≠ ⊤ := fun w => by
    apply ne_top_of_le_natCast_add
    exact (hc₁ _ y).trans (by
      calc
        KPPlain U (finWordBits A w) + (c₁ : ENat)
            ≤ ((finWordBits A w).length +
                2 * (Nat.bits (finWordBits A w).length).length + c₂ : ℕ) + (c₁ : ENat) := by
              gcongr
              exact_mod_cast hc₂ (finWordBits A w)
        _ = (((finWordBits A w).length +
              2 * (Nat.bits (finWordBits A w).length).length + c₂ : ℕ) : ENat) + c₁ := by
              rfl)
  let p : (Fin N → A) → BitString := fun w =>
    Classical.choose (exists_program_of_KP_ne_top (hfinite w))
  have hp : ∀ w, produces U (p w) y (finWordBits A w) := fun w =>
    (Classical.choose_spec (exists_program_of_KP_ne_top (hfinite w))).1
  have hplen : ∀ w, (p w).length = (KP U (finWordBits A w) y).toNat := fun w => by
    have h := congrArg ENat.toNat
      (Classical.choose_spec (exists_program_of_KP_ne_top (hfinite w))).2
    simpa [p] using h
  have hpinj : Function.Injective p := by
    intro w w' hww'
    apply List.ofFn_injective
    apply wordBits_injective
    exact Part.mem_unique (hww' ▸ hp w) (hp w')
  let F : Finset BitString := Finset.univ.image p
  have hF : IsPrefixFree (F : Set BitString) := by
    apply (hU.isPrefixMachine y).mono
    intro q hq
    change q ∈ Finset.univ.image p at hq
    rw [Finset.mem_image] at hq
    obtain ⟨w, _, rfl⟩ := hq
    exact produces_mem_domainAt (hp w)
  have hk := finset_kraft_real_le_one F hF
  change ∑ q ∈ Finset.univ.image p, ((1 : ℝ) / 2) ^ q.length ≤ 1 at hk
  rw [Finset.sum_image hpinj.injOn] at hk
  simpa only [one_div, hplen] using hk

/-- The invariance bound `KP U ≤ KP M + c` passes to expectations, provided the complexities
with respect to `M` are finite. -/
theorem expect_KP_toNat_le_add_of_invariance {Ω : Type*} [Fintype Ω]
    (ν : FiniteProbSpace Ω) (U M : Map) (x y : Ω → BitString) (c : ℕ)
    (hfinite : ∀ ω, KP M (x ω) (y ω) ≠ ⊤)
    (hle : ∀ ω, KP U (x ω) (y ω) ≤ KP M (x ω) (y ω) + (c : ENat)) :
    ν.expect (fun ω => ((KP U (x ω) (y ω)).toNat : ℝ)) ≤
      ν.expect (fun ω => ((KP M (x ω) (y ω)).toNat : ℝ)) + c := by
  unfold FiniteProbSpace.expect
  calc
    ∑ ω, ν.prob ω * ((KP U (x ω) (y ω)).toNat : ℝ) ≤
        ∑ ω, ν.prob ω * (((KP M (x ω) (y ω)).toNat : ℝ) + c) := by
      refine Finset.sum_le_sum fun ω _ => ?_
      apply mul_le_mul_of_nonneg_left _ (ν.prob_nonneg ω)
      have hrhs : KP M (x ω) (y ω) + (c : ENat) ≠ ⊤ := by
        rw [← ENat.natCast_toNat (hfinite ω)]
        rw [← ENat.natCast_add]
        exact ENat.natCast_ne_top _
      have h := ENat.toNat_le_toNat (hle ω) hrhs
      exact_mod_cast (by
        simpa [ENat.toNat_add (hfinite ω) (ENat.natCast_ne_top c)] using h)
    _ = ∑ ω, ν.prob ω * ((KP M (x ω) (y ω)).toNat : ℝ) + c := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ν.sum_prob, one_mul]

private theorem exists_common_denominator {A : Type*} [Finite A] (p : A → ℝ)
    (hnonneg : ∀ a, 0 ≤ p a) (hrat : ∀ a, ∃ r : ℚ, p a = (r : ℝ)) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ c : A → ℕ, ∀ a, p a = (c a : ℝ) / Q := by
  classical
  have := Fintype.ofFinite A
  choose r hr using hrat
  set Q := ∏ a, (r a).den with hQdef
  refine ⟨Q, Finset.prod_pos fun a _ => (r a).den_pos,
    fun a => (r a).num.toNat * (Q / (r a).den), fun a => ?_⟩
  have hdvd : (r a).den ∣ Q := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
  have hnum : 0 ≤ (r a).num := Rat.num_nonneg.mpr (by exact_mod_cast (hr a) ▸ hnonneg a)
  have hden : ((r a).den : ℝ) ≠ 0 := by exact_mod_cast (r a).den_ne_zero
  have hQ : (Q : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos fun a _ => (r a).den_pos).ne'
  rw [hr a, Nat.cast_mul, Nat.cast_div hdvd hden, Rat.cast_def]
  have : ((r a).num.toNat : ℝ) = ((r a).num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnum
  rw [this]
  field_simp

private theorem exists_shannon_length {X C : ℕ} (hC : 0 < C) (hCX : C ≤ X) :
    ∃ l, X ≤ 2 ^ l * C ∧ 2 ^ l * C < 2 * X := by
  classical
  have hex : ∃ l, X ≤ 2 ^ l * C :=
    ⟨X, le_trans (Nat.lt_two_pow_self).le (Nat.le_mul_of_pos_right _ hC)⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | m
  · simp; omega
  · have := Nat.find_min hex (show m < Nat.find hex by omega)
    rw [pow_succ]; push Not at this; nlinarith

private theorem shannon_length_unique {X C l m : ℕ} (hl : X ≤ 2 ^ l * C ∧ 2 ^ l * C < 2 * X)
    (hm : X ≤ 2 ^ m * C ∧ 2 ^ m * C < 2 * X) : l = m := by
  by_contra hne
  wlog h : l < m generalizing l m
  · exact this hm hl (Ne.symm hne) (by omega)
  have : 2 ^ (l + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
  rw [pow_succ] at this
  nlinarith

/-- The product of the numerators `c_j` of the letters of a word given by its letter ranks;
the probability of the word is this product divided by `Q ^ N`. -/
private def codedNum (cTab : List ℕ) (L : List ℕ) : ℕ := (L.map fun j => cTab.getD j 0).prod

/-- `l` is the Shannon code length of the word with letter ranks `L` and length `N`:
`2 ^ (-l) ≤ P < 2 ^ (1 - l)` for its probability `P = codedNum / Q ^ N`. -/
private def shannonGood (Q : ℕ) (cTab : List ℕ) (N : ℕ) (L : List ℕ) (l : ℕ) : Bool :=
  decide (L.length = N) && (decide (Q ^ N ≤ 2 ^ l * codedNum cTab L) &&
    decide (2 ^ l * codedNum cTab L < 2 * Q ^ N))

/-- The Kraft–Chaitin request stream of the Shannon code: in context `ctx` (read as
`N = |ctx| - 1`) the request number `⟨L, l⟩` asks for a codeword of length `l` for the word with
letter ranks `L` exactly when `l` is its Shannon length. -/
private def fixedShannonReq (Q : ℕ) (cTab : List ℕ) (codeTab : List BitString)
    (ctx : BitString)
    (n : ℕ) : Option (BitString × ℕ) :=
  (Encodable.decode (α := List ℕ) n.unpair.1).bind fun L =>
    bif shannonGood Q cTab (ctx.length - 1) L n.unpair.2 then
      some ((L.map fun j => codeTab.getD j []).flatten, n.unpair.2) else none

private theorem fixedShannonReq_primrec (Q : ℕ) (cTab : List ℕ) (codeTab : List BitString) :
    Primrec (fun p : BitString × ℕ => fixedShannonReq Q cTab codeTab p.1 p.2) := by
  have hpow : Primrec₂ (fun (a b : ℕ) => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow
  have hnum : Primrec (codedNum cTab) := by
    have : codedNum cTab = fun L => L.foldr (fun j s => cTab.getD j 0 * s) 1 := by
      funext L; induction L <;> simp_all [codedNum]
    rw [this]
    exact Primrec.list_foldr Primrec.id (Primrec.const 1)
      (Primrec.nat_mul.comp ((Primrec.list_getD 0).comp (Primrec.const cTab)
        (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  have hgood : Primrec (fun q : ℕ × List ℕ × ℕ => shannonGood Q cTab q.1 q.2.1 q.2.2) := by
    unfold shannonGood
    have hN : Primrec (fun q : ℕ × List ℕ × ℕ => q.1) := Primrec.fst
    have hL : Primrec (fun q : ℕ × List ℕ × ℕ => q.2.1) := Primrec.fst.comp Primrec.snd
    have hl : Primrec (fun q : ℕ × List ℕ × ℕ => q.2.2) := Primrec.snd.comp Primrec.snd
    have hQN : Primrec (fun q : ℕ × List ℕ × ℕ => Q ^ q.1) := hpow.comp (Primrec.const Q) hN
    have hC : Primrec (fun q : ℕ × List ℕ × ℕ => 2 ^ q.2.2 * codedNum cTab q.2.1) :=
      Primrec.nat_mul.comp (hpow.comp (Primrec.const 2) hl) (hnum.comp hL)
    refine Primrec.and.comp
      ((PrimrecRel.decide Primrec.eq).comp (Primrec.list_length.comp hL) hN)
      (Primrec.and.comp ((PrimrecRel.decide Primrec.nat_le).comp hQN hC)
        ((PrimrecRel.decide Primrec.nat_lt).comp hC
          (Primrec.nat_mul.comp (Primrec.const 2) hQN)))
  unfold fixedShannonReq
  refine Primrec.option_bind (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp
    Primrec.snd))) ?_
  have hl : Primrec (fun q : (BitString × ℕ) × List ℕ => q.1.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))
  refine Primrec.cond (hgood.comp (Primrec.pair (Primrec.nat_sub.comp
    (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1))
      (Primrec.pair Primrec.snd hl))) (Primrec.option_some.comp (Primrec.pair ?_ hl))
    (Primrec.const none)
  exact Primrec.list_flatten.comp (Primrec.list_map Primrec.snd
    ((Primrec.list_getD []).comp (Primrec.const codeTab) Primrec.snd).to₂)

private theorem alphabetIndex_bijective (A : Type*) [Fintype A] [Encodable A] :
    Function.Bijective (fun a : A => (⟨alphabetIndex A a, alphabetIndex_lt_card a⟩ :
      Fin (Fintype.card A))) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨fun a b h => alphabetIndex_injective (Fin.mk.inj_iff.mp h), (Fintype.card_fin _).symm⟩

/-- The numerators `c a`, listed by letter rank. -/
private noncomputable def numeratorTable (A : Type*) [Fintype A] [Encodable A]
    (c : A → ℕ) :
    List ℕ :=
  List.ofFn fun j => c ((Equiv.ofBijective _ (alphabetIndex_bijective A)).symm j)

/-- The fixed-width letter blocks of `wordBits`, listed by letter rank. -/
private def blockTable (A : Type*) [Fintype A] [Encodable A] : List BitString :=
  (List.range (Fintype.card A)).map (natBitsFixed (alphabetWidth A))

/-- The list of letter ranks of a word. -/
private def alphabetWordIdx {A : Type*} [Fintype A] [Encodable A] {N : ℕ}
    (w : Fin N → A) : List ℕ :=
  List.ofFn fun i => alphabetIndex A (w i)

private theorem numeratorTable_getD {A : Type*} [Fintype A] [Encodable A]
    (c : A → ℕ) (a : A) :
    (numeratorTable A c).getD (alphabetIndex A a) 0 = c a := by
  have h := (Equiv.ofBijective _ (alphabetIndex_bijective A)).symm_apply_apply a
  rw [numeratorTable, List.getD_eq_getElem _ _ (by simpa using alphabetIndex_lt_card a),
    List.getElem_ofFn]
  exact congrArg c h

private theorem codedNum_alphabetWordIdx {A : Type*} [Fintype A] [Encodable A]
    (c : A → ℕ) {N : ℕ} (w : Fin N → A) :
    codedNum (numeratorTable A c) (alphabetWordIdx w) = ∏ i, c (w i) := by
  simp only [codedNum, alphabetWordIdx, List.map_ofFn, Function.comp_def,
    numeratorTable_getD,
    List.prod_ofFn]

private theorem flatten_blockTable_alphabetWordIdx {A : Type*} [Fintype A] [Encodable A] {N : ℕ}
    (w : Fin N → A) :
    ((alphabetWordIdx w).map fun j => (blockTable A).getD j []).flatten =
      finWordBits A w := by
  simp only [finWordBits, wordBits, Code.encodeWord, alphabetWordIdx, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, blockTable, alphabetCode]
  rw [List.getD_eq_getElem _ _ (by simpa using alphabetIndex_lt_card (w i))]
  simp

private theorem exists_word_of_codedNum_pos {A : Type*} [Fintype A] [Encodable A] (c : A → ℕ)
    (L : List ℕ) (N : ℕ) (hlen : L.length = N)
    (hL : 0 < codedNum (numeratorTable A c) L) :
    ∃ w : Fin N → A, alphabetWordIdx w = L := by
  subst hlen
  have hlt : ∀ i : Fin L.length, L[i] < Fintype.card A := by
    intro i
    by_contra hge
    have h0 : (numeratorTable A c).getD L[i] 0 = 0 := by
      rw [List.getD_eq_default]; simpa [numeratorTable] using not_lt.mp hge
    have : codedNum (numeratorTable A c) L = 0 := by
      rw [codedNum, List.prod_eq_zero_iff]
      exact List.mem_map.mpr ⟨L[i], List.getElem_mem _, h0⟩
    omega
  refine ⟨fun i => (Equiv.ofBijective _ (alphabetIndex_bijective A)).symm ⟨L[i], hlt i⟩, ?_⟩
  apply List.ext_getElem (by simp [alphabetWordIdx])
  intro n h1 h2
  simp only [alphabetWordIdx, List.getElem_ofFn]
  have := (Equiv.ofBijective _ (alphabetIndex_bijective A)).apply_symm_apply ⟨L[n], hlt ⟨n, h2⟩⟩
  exact Fin.mk.inj_iff.mp this

private theorem fixedShannonReq_word {A : Type*} [Fintype A] [Encodable A]
    (Q : ℕ) (c : A → ℕ)
    (ctx : BitString) {N : ℕ} (hN : ctx.length - 1 = N) (w : Fin N → A) (l : ℕ)
    (hl : Q ^ N ≤ 2 ^ l * ∏ i, c (w i) ∧ 2 ^ l * ∏ i, c (w i) < 2 * Q ^ N) :
    fixedShannonReq Q (numeratorTable A c) (blockTable A) ctx
      (Nat.pair (Encodable.encode (alphabetWordIdx w)) l) =
        some (finWordBits A w, l) := by
  have hlen : (alphabetWordIdx w).length = N := by simp [alphabetWordIdx]
  simp [fixedShannonReq, shannonGood, hN, hlen, codedNum_alphabetWordIdx, hl]
  simpa using flatten_blockTable_alphabetWordIdx w

private theorem fixedShannonReq_eq_some {A : Type*} [Fintype A] [Encodable A]
    (Q : ℕ) (hQ : 0 < Q)
    (c : A → ℕ) (ctx : BitString) (n : ℕ) (o : BitString) (l : ℕ)
    (h : fixedShannonReq Q (numeratorTable A c) (blockTable A) ctx n = some (o, l)) :
    ∃ w : Fin (ctx.length - 1) → A,
      n = Nat.pair (Encodable.encode (alphabetWordIdx w)) l ∧
      Q ^ (ctx.length - 1) ≤ 2 ^ l * ∏ i, c (w i) ∧
      2 ^ l * ∏ i, c (w i) < 2 * Q ^ (ctx.length - 1) := by
  simp only [fixedShannonReq, Option.bind_eq_some_iff] at h
  obtain ⟨L, hL, h⟩ := h
  cases hg : shannonGood Q (numeratorTable A c) (ctx.length - 1) L n.unpair.2
  · simp [hg] at h
  simp only [hg, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
  simp only [shannonGood, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨hlen, h1, h2⟩ := hg
  have hpos : 0 < codedNum (numeratorTable A c) L := by
    rcases Nat.eq_zero_or_pos (codedNum (numeratorTable A c) L) with h0 | h0
    · rw [h0, mul_zero] at h1
      exact absurd h1 (Nat.not_le.mpr (pow_pos hQ _))
    · exact h0
  obtain ⟨w, hw⟩ := exists_word_of_codedNum_pos c L _ hlen hpos
  refine ⟨w, ?_, ?_⟩
  · rw [Denumerable.decode_eq_ofNat, Option.some.injEq] at hL
    rw [hw, ← h.2, ← hL, Denumerable.encode_ofNat, Nat.pair_unpair]
  · rw [← codedNum_alphabetWordIdx, hw, ← h.2]
    exact ⟨h1, h2⟩

private theorem power_prob_eq_div {A : Type*} [Fintype A] (μ : FiniteProbSpace A) (Q : ℕ)
    (c : A → ℕ) (hc : ∀ a, μ.prob a = (c a : ℝ) / Q) {N : ℕ} (w : Fin N → A) :
    (μ.power N).prob w = ((∏ i, c (w i) : ℕ) : ℝ) / (Q : ℝ) ^ N := by
  change ∏ i, μ.prob (w i) = _
  simp [hc, Finset.prod_div_distrib]

private theorem exists_word_shannon_length {A : Type*} (Q : ℕ) (c : A → ℕ)
    (hcpos : ∀ a, 0 < c a) (hcQ : ∀ a, c a ≤ Q) {N : ℕ} (w : Fin N → A) :
    ∃ l, Q ^ N ≤ 2 ^ l * ∏ i, c (w i) ∧ 2 ^ l * ∏ i, c (w i) < 2 * Q ^ N :=
  exists_shannon_length (Finset.prod_pos fun i _ => hcpos (w i))
    (by simpa using Finset.prod_le_prod (s := Finset.univ) (fun i _ => hcQ (w i)))

private theorem fixedShannonReq_kraft {A : Type*} [Fintype A] [Encodable A]
    (μ : FiniteProbSpace A)
    (Q : ℕ) (hQ : 0 < Q) (c : A → ℕ) (hc : ∀ a, μ.prob a = (c a : ℝ) / Q)
    (hcpos : ∀ a, 0 < c a) (hcQ : ∀ a, c a ≤ Q) (ctx : BitString) :
    (∑' n, match fixedShannonReq Q (numeratorTable A c) (blockTable A) ctx n with
      | some (_, l) => (2 : ENNReal)⁻¹ ^ l
      | none => 0) ≤ 1 := by
  classical
  choose l hl using fun w : Fin (ctx.length - 1) → A => exists_word_shannon_length Q c hcpos hcQ w
  let φ : (Fin (ctx.length - 1) → A) → ℕ := fun w =>
    Nat.pair (Encodable.encode (alphabetWordIdx w)) (l w)
  have hφ : Function.Injective φ := by
    intro w w' h
    have h1 := congrArg (fun n => n.unpair.1) h
    simp only [φ, Nat.unpair_pair] at h1
    have h2 := Encodable.encode_injective h1
    simp only [alphabetWordIdx] at h2
    funext i
    exact alphabetIndex_injective (congrFun (List.ofFn_injective h2) i)
  have hreq : ∀ w, fixedShannonReq Q (numeratorTable A c) (blockTable A) ctx (φ w) =
      some (finWordBits A w, l w) := fun w =>
        fixedShannonReq_word Q c ctx rfl w (l w) (hl w)
  rw [tsum_eq_sum (s := Finset.univ.image φ) ?_, Finset.sum_image hφ.injOn]
  · calc _ = ∑ w, (2 : ENNReal)⁻¹ ^ l w := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [hreq w]
      _ ≤ ∑ w, ENNReal.ofReal ((μ.power (ctx.length - 1)).prob w) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [power_prob_eq_div μ Q c hc w]
          have : (2 : ENNReal)⁻¹ ^ l w = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ l w) := by
            rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
            simp
          rw [this]
          apply ENNReal.ofReal_le_ofReal
          rw [inv_pow, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
          exact_mod_cast (hl w).1
      _ = 1 := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun w _ => (μ.power _).prob_nonneg w,
            (μ.power _).sum_prob, ENNReal.ofReal_one]
  · intro n hn
    cases h : fixedShannonReq Q (numeratorTable A c) (blockTable A) ctx n with
    | none => rfl
    | some ol =>
      obtain ⟨o, l'⟩ := ol
      obtain ⟨w, rfl, h1, h2⟩ := fixedShannonReq_eq_some Q hQ c ctx n o l' h
      have := shannon_length_unique ⟨h1, h2⟩ (hl w)
      exact absurd (Finset.mem_image.mpr ⟨w, Finset.mem_univ _, by simp [φ, this]⟩) hn

private theorem mul_length_le_negMulLog2_add {P : ℝ} (hP : 0 < P) {l : ℕ}
    (hl : (2 : ℝ) ^ l * P < 2) : P * l ≤ negMulLog2 P + P := by
  have hlog : Real.logb 2 P ≤ 1 - l := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) hP, Real.rpow_sub (by norm_num), Real.rpow_one,
      Real.rpow_natCast, le_div_iff₀ (by positivity)]
    linarith [mul_comm P (2 ^ l)]
  have : negMulLog2 P = P * (-Real.logb 2 P) := by
    unfold negMulLog2 Real.negMulLog Real.logb; ring
  rw [this]; nlinarith

private theorem exists_shannon_prefix_decompressor (A : Type*) [Fintype A] [Encodable A]
    (μ : FiniteProbSpace A) (hpos : ∀ a, 0 < μ.prob a)
    (hrat : ∀ a, ∃ r : ℚ, μ.prob a = (r : ℝ)) :
    ∃ M : Map, IsPrefixDecompressor M ∧ ∀ N : ℕ,
      (∀ w : Fin N → A, KP M (finWordBits A w) (natCode N) ≠ ⊤) ∧
      ((μ.power N).expect fun w =>
          ((KP M (finWordBits A w) (natCode N)).toNat : ℝ)) ≤
        (N : ℝ) * entropyDist μ.prob + 1 := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := exists_common_denominator μ.prob μ.prob_nonneg hrat
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hcpos : ∀ a, 0 < c a := fun a => by
    have := hpos a
    rw [hc a] at this
    exact_mod_cast (div_pos_iff_of_pos_right hQr).mp this
  have hcQ : ∀ a, c a ≤ Q := fun a => by
    have h1 : μ.prob a ≤ 1 := μ.sum_prob ▸
      Finset.single_le_sum (fun b _ => μ.prob_nonneg b) (Finset.mem_univ a)
    rw [hc a, div_le_one hQr] at h1
    exact_mod_cast h1
  let req : BitString → ℕ → Option (BitString × ℕ) :=
    fixedShannonReq Q (numeratorTable A c) (blockTable A)
  have hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2) :=
    (fixedShannonReq_primrec _ _ _).to_comp
  obtain ⟨alloc, hac, hal, hap⟩ := exists_online_prefixFree_family req hcomp
    (fixedShannonReq_kraft μ Q hQ c hc hcpos hcQ)
  obtain ⟨M, hM, hMout⟩ := construct_prefix_machine req alloc hcomp hac hal hap
  refine ⟨M, hM, fun N => ?_⟩
  choose l hl using fun w : Fin N → A => exists_word_shannon_length Q c hcpos hcQ w
  have hKP : ∀ w : Fin N → A, KP M (finWordBits A w) (natCode N) ≤ (l w : ENat) := by
    intro w
    have hreq : req (natCode N) _ = _ :=
      fixedShannonReq_word Q c (natCode N) (by simp [natCode]) w (l w) (hl w)
    obtain ⟨p, hp, hplen⟩ := hal _ _ _ _ hreq
    have hprod : produces M p (natCode N) (finWordBits A w) := by
      rw [produces, hMout _ _ _ _ _ hreq hp]
      exact Part.mem_some _
    exact (KP_le_programLength_of_produces hprod).trans (by simp [hplen])
  refine ⟨fun w => ne_top_of_le_natCast (hKP w), ?_⟩
  rw [← entropyDist_prod_eq μ.prob_nonneg μ.sum_prob N]
  unfold FiniteProbSpace.expect
  calc ∑ w, (μ.power N).prob w * ((KP M (finWordBits A w) (natCode N)).toNat : ℝ)
      ≤ ∑ w, (μ.power N).prob w * (l w : ℝ) := by
        refine Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_left ?_ ((μ.power N).prob_nonneg w)
        exact_mod_cast ENat.toNat_le_of_le_natCast (hKP w)
    _ ≤ ∑ w, (negMulLog2 ((μ.power N).prob w) + (μ.power N).prob w) := by
        refine Finset.sum_le_sum fun w _ => mul_length_le_negMulLog2_add ?_ ?_
        · rw [power_prob_eq_div μ Q c hc w]
          have := Finset.prod_pos fun i (_ : i ∈ Finset.univ) => hcpos (w i)
          positivity
        · rw [power_prob_eq_div μ Q c hc w, mul_div_assoc', div_lt_iff₀ (by positivity)]
          exact_mod_cast (hl w).2
    _ = entropyDist (fun w : Fin N → A => ∏ i, μ.prob (w i)) + 1 := by
        rw [Finset.sum_add_distrib, (μ.power N).sum_prob]
        rfl

/-- **The expected complexity of an i.i.d. word is at least `N H(ξ)`.**  The shortest descriptions
with respect to a prefix decompressor form a prefix code, so their average length is at least the
entropy `H(ξ^N) = N H(ξ)`.  The complexity is the prefix complexity of the block encoding
`finWordBits` of the word, conditional on `natCode N`.

**Stronger than the printed statement**: the section fixes positive rational `p_i` for the whole
of Theorem 147, and the lower bound needs neither positivity nor rationality nor a constant.
SUV Theorem 147, p. 228. -/
theorem mul_entropyDist_le_expect_KP (A : Type*) [Fintype A] [Encodable A]
    (μ : FiniteProbSpace A) (U : Map) (hU : IsOptimalPrefixConditional U) (N : ℕ) :
    (N : ℝ) * entropyDist μ.prob ≤
      (μ.power N).expect fun w => ((KP U (finWordBits A w) (natCode N)).toNat : ℝ) := by
  rw [← entropyDist_prod_eq μ.prob_nonneg μ.sum_prob N]
  exact entropyDist_le_expect_of_kraft (μ.power N)
    (fun w => (KP U (finWordBits A w) (natCode N)).toNat)
    (sum_inv_pow_KP_toNat_le_one A U hU N (natCode N))

/-- **The expected complexity of an i.i.d. word is at most `N H(ξ) + O(1)`.**  The constant is
quantified before `N`, so it may depend on the alphabet, on the distribution and on the
decompressor but not on the length, exactly as the book requires.  Positivity and rationality of
the `p_i` are what make a prefix code of average length below `H(ξ^N) + 1` computable from `N`.
The complexity is the prefix complexity of the block encoding `finWordBits` of the word,
conditional on `natCode N`.  SUV Theorem 147, p. 228. -/
theorem exists_expect_KP_le_mul_entropyDist (A : Type*) [Fintype A] [Encodable A]
    (μ : FiniteProbSpace A) (hpos : ∀ a, 0 < μ.prob a)
    (hrat : ∀ a, ∃ r : ℚ, μ.prob a = (r : ℝ)) (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ N : ℕ,
      ((μ.power N).expect fun w => ((KP U (finWordBits A w) (natCode N)).toNat : ℝ)) ≤
        (N : ℝ) * entropyDist μ.prob + c := by
  obtain ⟨M, hM, hMbound⟩ := exists_shannon_prefix_decompressor A μ hpos hrat
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c + 1, fun N => ?_⟩
  calc
    (μ.power N).expect (fun w =>
        ((KP U (finWordBits A w) (natCode N)).toNat : ℝ)) ≤
        (μ.power N).expect (fun w =>
          ((KP M (finWordBits A w) (natCode N)).toNat : ℝ)) + c := by
      apply expect_KP_toNat_le_add_of_invariance
      · exact (hMbound N).1
      · exact fun w => hc (finWordBits A w) (natCode N)
    _ ≤ ((N : ℝ) * entropyDist μ.prob + 1) + c := by
      gcongr
      exact (hMbound N).2
    _ = (N : ℝ) * entropyDist μ.prob + (c + 1 : ℕ) := by
      push_cast
      ring

end Kolmogorov
