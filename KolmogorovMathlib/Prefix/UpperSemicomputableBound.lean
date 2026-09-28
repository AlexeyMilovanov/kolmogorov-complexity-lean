/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin

/-!
# SUV Theorem 62 (p. 100): upper semicomputable upper bounds for prefix complexity

Shen-Uspensky-Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness*,
Chapter 4, Theorem 62 (p. 100):

> an upper semicomputable function `f` with integer values is an upper bound for
> `K` up to an additive constant if and only if `∑ 2^{-f(n)}` is finite.

This is a **Chapter-4** statement.  It is recalled verbatim by Chapter 5
(Section 5.7.6, p. 168, in the proof of Theorem 113), so it needs a single owner
that the Chapter-5 clusters can alias instead of restating.  This module is that
owner: `MonotoneComplexity/Omega/SolovayFunctions.lean` (cluster C11) now holds
only a one-line alias, `KPNat_le_iff_tsum_two_pow_neg_ne_top`.

## Statement shape

The book writes `K(n)` for the prefix complexity of a natural number, silently
identifying `ℕ` with the set of binary strings.  Chapter 4's complexity
`KPPlain U : BitString → ENat` lives on strings, so the identification is made an
explicit parameter here: the criterion is stated for an arbitrary encoding
`e : ℕ → BitString`, with exactly the hypotheses each direction needs.

* the "only if" direction (`tsum_two_pow_neg_ne_top_of_KPPlain_le`) is the Kraft
  inequality for the prefix machine `U` and needs `e` **injective**, so that
  distinct `n` really do consume distinct shares of the Kraft budget;
* the "if" direction (`KPPlain_le_of_tsum_two_pow_neg_ne_top`) is the
  Kraft-Chaitin coding theorem, applied to the requests `⟨e n, f n + O(1)⟩` read
  off the upper semicomputable approximation of `f`, and needs `e`
  **computable**, so that the requests can be enumerated.

Chapter 5 instantiates both with the canonical computable bijection
`natToBitString` of `MonotoneComplexity/SharedCoding.lean`, recovering the book's
`K(n) = KPNat U n` literally.

## Status

Both directions are **proved**, so the `↔` form is proved outright and
the Chapter-5 alias `KPNat_le_iff_tsum_two_pow_neg_ne_top` no longer rests on any
leaf.  The "only if" direction is the Kraft inequality for `U`; the "if" direction
runs the Kraft-Chaitin request/allocation machinery of
`AlgorithmicProbability/KraftChaitinCore.lean` directly (`exists_online_prefixFree_family`
followed by `construct_prefix_machine`), with the requests charged only at the stages
at which the upper semicomputable approximation of `f` strictly improves.
-/

namespace Kolmogorov

open ENNReal

/-! ### Upper semicomputable integer-valued functions (SUV p. 100, recalled p. 168) -/

/-- An upper semicomputable integer-valued function: the pointwise limit of a
computable non-increasing family of integers that stabilises at every argument
(SUV p. 168: "decreasing integer upper bounds for `f(n)`"; the notion itself is
introduced in Chapter 4 around Theorem 62, p. 100). -/
def IsUpperSemicomputableNat (f : ℕ → ℕ) : Prop :=
  ∃ g : ℕ → ℕ → ℕ, Computable₂ g ∧ (∀ s n, g (s + 1) n ≤ g s n) ∧
    ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → g s n = f n

/-! ### Theorem 62 -/

/-- If an upper semicomputable integer-valued `f` bounds the prefix complexity of the encoded
naturals, `K(e n) ≤ f(n) + O(1)`, then `∑ₙ 2^{-f(n)}` is finite: the Kraft inequality for
the prefix machine `U` caps `∑ₙ 2^{-K(e n)}`, and injectivity of `e` keeps the terms of that
sum distinct. *Proof.* Antitonicity of `complexityWeight` turns `K(e n) ≤ f n + c` into the
pointwise bound `2^{-f n} · 2^{-c} ≤ 2^{-K(e n)}`; summing over `n`, pulling the constant
out (`ENNReal.tsum_mul_right`), transporting along the injection `e`
(`ENNReal.tsum_comp_le_tsum_of_injective`) and applying the Kraft inequality `∑ₓ 2^{-K(x)} ≤
∑ₓ m_U(x) ≤ 1` (`complexityWeight_KP_le_aprioriMeasure` and `tsum_aprioriMeasure_le_one`,
i.e. the prefix-freeness of the domain of `U`) give `(∑ₙ 2^{-f n}) · 2^{-c} ≤ 1`; as `2^{-c}
≠ 0`, the sum cannot be `⊤`. Upper semicomputability of `f` is not used in this direction.
SUV Theorem 62 (Chapter 4, p. 100), "only if" direction. -/
theorem tsum_two_pow_neg_ne_top_of_KPPlain_le {U : Map} (hU : IsOptimalPrefixConditional U)
    {e : ℕ → BitString} (he : Function.Injective e) {f : ℕ → ℕ}
    (_hf : IsUpperSemicomputableNat f)
    (h : ∃ c : ℕ, ∀ n, KPPlain U (e n) ≤ (f n : ENat) + (c : ENat)) :
    (∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤ := by
  obtain ⟨c, hc⟩ := h
  -- pointwise: `2^{-f n} · 2^{-c} ≤ 2^{-K(e n)}`
  have hpt : ∀ n, (2 : ℝ≥0∞)⁻¹ ^ f n * (2 : ℝ≥0∞)⁻¹ ^ c
      ≤ complexityWeight (KPPlain U (e n)) := by
    intro n
    have h1 := complexityWeight_le_of_le (hc n)
    rwa [complexityWeight_add_nat, complexityWeight_coe] at h1
  -- the Kraft inequality for the prefix machine `U`
  have hkraft : (∑' x : BitString, complexityWeight (KPPlain U x)) ≤ 1 :=
    le_trans (ENNReal.tsum_le_tsum fun x => complexityWeight_KP_le_aprioriMeasure U x [])
      (tsum_aprioriMeasure_le_one U [] hU.isPrefixMachine)
  have hinj : (∑' n : ℕ, complexityWeight (KPPlain U (e n)))
      ≤ ∑' x : BitString, complexityWeight (KPPlain U x) :=
    ENNReal.tsum_comp_le_tsum_of_injective he _
  have hsum : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) * (2 : ℝ≥0∞)⁻¹ ^ c ≤ 1 := by
    rw [← ENNReal.tsum_mul_right]
    exact le_trans (le_trans (ENNReal.tsum_le_tsum hpt) hinj) hkraft
  intro htop
  rw [htop, ENNReal.top_mul (pow_ne_zero c inv_two_ne_zero)] at hsum
  simp at hsum

/-- The Kraft weight of the charged request stream is at most one: for a fixed index the
charged stages carry pairwise distinct estimates above `f`, so the requests reindex
injectively into a geometric family of total weight `2⁻¹ ^ d * ∑ₙ 2⁻¹ ^ f n`. -/
private lemma kraft_weight_of_charged_requests {e : ℕ → BitString} {f : ℕ → ℕ}
    {g : ℕ → ℕ → ℕ} {d : ℕ} {chg : ℕ → Bool} {req : BitString → ℕ → Option (BitString × ℕ)}
    (hgge : ∀ s n, f n ≤ g s n)
    (hdrop : ∀ (n s s' : ℕ), s < s' → (s' = 0 ∨ g s' n < g (s' - 1) n) → g s' n < g s n)
    (hdle : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≤ (2 : ℝ≥0∞) ^ d)
    (hchg_iff : ∀ k : ℕ, chg k = true ↔
      (k.unpair.2 = 0 ∨ g k.unpair.2 k.unpair.1 < g (k.unpair.2 - 1) k.unpair.1))
    (hreqdef : req = fun _ k =>
      cond (chg k) (some (e k.unpair.1, g k.unpair.2 k.unpair.1 + d + 1)) none)
    (ctx : BitString) :
    (∑' k, match req ctx k with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1 := by
  classical
  have hterm : ∀ k : ℕ,
      (match req ctx k with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)
        = Set.indicator {k : ℕ | chg k = true}
            (fun k => (2 : ℝ≥0∞)⁻¹ ^ (g k.unpair.2 k.unpair.1 + d + 1)) k := by
    intro k
    rw [Set.indicator_apply, hreqdef]
    by_cases hk : chg k = true
    · simp [hk, Set.mem_setOf_eq]
    · have hk' : chg k = false := by simpa using hk
      simp [hk', Set.mem_setOf_eq]
  rw [tsum_congr hterm, ← tsum_subtype]
  -- reindex the charged pairs by `⟨n, g s n - f n⟩`
  set ι : {k : ℕ // k ∈ {k : ℕ | chg k = true}} → ℕ := fun k =>
    Nat.pair k.1.unpair.1 (g k.1.unpair.2 k.1.unpair.1 - f k.1.unpair.1) with hιdef
  have hιinj : Function.Injective ι := by
    rintro ⟨k, hk⟩ ⟨k', hk'⟩ hEq
    simp only [Set.mem_setOf_eq] at hk hk'
    have hpair := congrArg Nat.unpair hEq
    simp only [hιdef, Nat.unpair_pair, Prod.mk.injEq] at hpair
    obtain ⟨hn, hv⟩ := hpair
    rw [← hn] at hv
    have hA := hgge k.unpair.2 k.unpair.1
    have hB := hgge k'.unpair.2 k.unpair.1
    have hgn : g k.unpair.2 k.unpair.1 = g k'.unpair.2 k.unpair.1 := by omega
    have hs : k.unpair.2 = k'.unpair.2 := by
      by_contra hne
      rcases Nat.lt_or_ge k.unpair.2 k'.unpair.2 with hlt | hge
      · have hch' := (hchg_iff k').1 hk'
        rw [← hn] at hch'
        have := hdrop k.unpair.1 k.unpair.2 k'.unpair.2 hlt hch'
        omega
      · have hlt' : k'.unpair.2 < k.unpair.2 := by omega
        have := hdrop k.unpair.1 k'.unpair.2 k.unpair.2 hlt' ((hchg_iff k).1 hk)
        omega
    have hkk : k = k' := by
      have h1 : Nat.pair k.unpair.1 k.unpair.2 = Nat.pair k'.unpair.1 k'.unpair.2 := by
        rw [hn, hs]
      rwa [Nat.pair_unpair, Nat.pair_unpair] at h1
    exact Subtype.ext hkk
  set F : ℕ → ℝ≥0∞ := fun j => (2 : ℝ≥0∞)⁻¹ ^ (f j.unpair.1 + j.unpair.2 + d + 1) with hFdef
  have hcomp : ∀ k : {k : ℕ // k ∈ {k : ℕ | chg k = true}},
      (2 : ℝ≥0∞)⁻¹ ^ (g k.1.unpair.2 k.1.unpair.1 + d + 1) = F (ι k) := by
    intro k
    have := hgge k.1.unpair.2 k.1.unpair.1
    simp only [hFdef, hιdef, Nat.unpair_pair]
    congr 1
    omega
  rw [tsum_congr hcomp]
  refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective hιinj F) ?_
  rw [hFdef]
  -- the flattened geometric estimate
  have hflat : (∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (f j.unpair.1 + j.unpair.2 + d + 1))
      = ∑' p : ℕ × ℕ, (2 : ℝ≥0∞)⁻¹ ^ (f p.1 + p.2 + d + 1) := by
    rw [← Equiv.tsum_eq Nat.pairEquiv
      (fun j : ℕ => (2 : ℝ≥0∞)⁻¹ ^ (f j.unpair.1 + j.unpair.2 + d + 1))]
    exact tsum_congr fun p => by simp [Nat.pairEquiv, Function.uncurry, Nat.unpair_pair]
  rw [hflat, ENNReal.tsum_prod (f := fun n v => (2 : ℝ≥0∞)⁻¹ ^ (f n + v + d + 1))]
  have hinner : ∀ n : ℕ, (∑' v : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (f n + v + d + 1))
      = (2 : ℝ≥0∞)⁻¹ ^ (f n + d) := by
    intro n
    have hpow : ∀ v : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (f n + v + d + 1)
        = (2 : ℝ≥0∞)⁻¹ ^ (f n + d + 1) * (2 : ℝ≥0∞)⁻¹ ^ v := by
      intro v
      rw [← pow_add]
      congr 1
      omega
    rw [tsum_congr hpow, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    have hhalf : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
      rw [ENNReal.sub_eq_of_eq_add (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ ⊤)]
      rw [ENNReal.inv_two_add_inv_two]
    rw [hhalf, inv_inv, pow_succ, mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  rw [tsum_congr hinner]
  have hsplit : ∀ n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (f n + d)
      = (2 : ℝ≥0∞)⁻¹ ^ f n * (2 : ℝ≥0∞)⁻¹ ^ d := fun n => pow_add _ _ _
  rw [tsum_congr hsplit, ENNReal.tsum_mul_right]
  calc (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) * (2 : ℝ≥0∞)⁻¹ ^ d
      ≤ (2 : ℝ≥0∞) ^ d * (2 : ℝ≥0∞)⁻¹ ^ d := by gcongr
    _ = 1 := by rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
          one_pow]

/-- If `f` is upper semicomputable with integer values and `∑ₙ 2^{-f(n)}` is finite, then `f` is
an upper bound for the prefix complexity of the encoded naturals up to an additive constant:
`K(e n) ≤ f(n) + O(1)`. This is the Kraft-Chaitin coding theorem, followed by optimality of
`U`. *Proof.* Let `g` be the non-increasing computable approximation of `f` supplied by
`hf`, and let `d` be a budget with `∑ₙ 2^{-f n} ≤ 2^d`. The **request stream** asks, for the
pair `k = ⟨n, s⟩`, for a code word of length `g s n + d + 1` for the output `e n` — but only
at the stages `s` at which the estimate has *just improved* (`s = 0`, or `g s n < g (s-1)
n`). This charging discipline is what makes the Kraft weight finite: for a fixed `n` the
charged stages carry pairwise distinct values `g s n ≥ f n` (a later charged stage strictly
undercuts every earlier stage), so `⟨n, s⟩ ↦ ⟨n, g s n - f n⟩` is injective on the charged
set and the total weight is at most `∑ₙ ∑ᵥ 2^{-(f n + v + d + 1)} = 2^{-d} · ∑ₙ 2^{-f n} ≤
1`. `exists_online_prefixFree_family` then allocates prefix-free code words of exactly the
requested lengths, `construct_prefix_machine` turns the allocation into a prefix
decompressor `M'` that decodes them, and optimality of `U` transfers the bound. The charged
stage `s₀` at which `g s n` first equals `f n` supplies, for each `n`, a code word of length
`f n + d + 1` for `e n`. Injectivity of `e` is not needed.  SUV Theorem 62 (Chapter 4, p.
100), "if" direction. -/
theorem KPPlain_le_of_tsum_two_pow_neg_ne_top {U : Map} (hU : IsOptimalPrefixConditional U)
    {e : ℕ → BitString} (he : Computable e) {f : ℕ → ℕ}
    (hf : IsUpperSemicomputableNat f) (h : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤) :
    ∃ c : ℕ, ∀ n, KPPlain U (e n) ≤ (f n : ENat) + (c : ENat) := by
  classical
  obtain ⟨g, hgc, hgstep, hglim⟩ := hf
  -- `g` is antitone in the stage, and never below `f`
  have hganti : ∀ n, Antitone fun s => g s n := fun n =>
    antitone_nat_of_succ_le fun s => hgstep s n
  have hgge : ∀ s n, f n ≤ g s n := by
    intro s n
    obtain ⟨s₀, hs₀⟩ := hglim n
    have h1 : g (max s s₀) n = f n := hs₀ _ (le_max_right s s₀)
    have h2 : g (max s s₀) n ≤ g s n := hganti n (le_max_left s s₀)
    omega
  -- the budget
  obtain ⟨d, hd⟩ := ENNReal.exists_nat_gt h
  have hdle : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≤ (2 : ℝ≥0∞) ^ d := by
    refine le_trans hd.le ?_
    have hn2 : d < 2 ^ d := Nat.lt_two_pow_self
    calc (d : ℝ≥0∞) ≤ ((2 ^ d : ℕ) : ℝ≥0∞) := by exact_mod_cast hn2.le
      _ = (2 : ℝ≥0∞) ^ d := by push_cast; ring
  -- the charging discipline
  set chg : ℕ → Bool := fun k =>
    decide (k.unpair.2 = 0) ||
      decide (g k.unpair.2 k.unpair.1 < g (k.unpair.2 - 1) k.unpair.1) with hchgdef
  have hchg_iff : ∀ k : ℕ, chg k = true ↔
      (k.unpair.2 = 0 ∨ g k.unpair.2 k.unpair.1 < g (k.unpair.2 - 1) k.unpair.1) := by
    intro k; rw [hchgdef]; simp
  -- a later charged stage strictly undercuts every earlier stage
  have hdrop : ∀ (n s s' : ℕ), s < s' →
      (s' = 0 ∨ g s' n < g (s' - 1) n) → g s' n < g s n := by
    rintro n s s' hss (rfl | hlt)
    · omega
    · exact lt_of_lt_of_le hlt (hganti n (by omega))
  set req : BitString → ℕ → Option (BitString × ℕ) := fun _ k =>
    cond (chg k) (some (e k.unpair.1, g k.unpair.2 k.unpair.1 + d + 1)) none with hreqdef
  -- computability of the request stream
  have hu1 : Computable (fun k : ℕ => k.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
  have hu2 : Computable (fun k : ℕ => k.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
  have hg1 : Computable (fun k : ℕ => g k.unpair.2 k.unpair.1) := hgc.comp hu2 hu1
  have hg0 : Computable (fun k : ℕ => g (k.unpair.2 - 1) k.unpair.1) :=
    hgc.comp (Primrec.nat_sub.to_comp.comp hu2 (Computable.const 1)) hu1
  have hchgc : Computable chg := by
    have hz : Computable (fun k : ℕ => decide (k.unpair.2 = 0)) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp hu2 (Computable.const 0)
    have hlt : Computable (fun k : ℕ =>
        decide (g k.unpair.2 k.unpair.1 < g (k.unpair.2 - 1) k.unpair.1)) :=
      (PrimrecRel.decide Primrec.nat_lt).to_comp.comp hg1 hg0
    exact (Primrec.dom_bool₂ (fun a b => a || b)).to_comp.comp hz hlt
  have hreqc : Computable (fun p : BitString × ℕ => req p.1 p.2) := by
    have hsome : Computable (fun p : BitString × ℕ =>
        (some (e p.2.unpair.1, g p.2.unpair.2 p.2.unpair.1 + d + 1) :
          Option (BitString × ℕ))) :=
      Computable.option_some.comp (Computable.pair (he.comp (hu1.comp Computable.snd))
        (Primrec.nat_add.to_comp.comp
          (Primrec.nat_add.to_comp.comp (hg1.comp Computable.snd) (Computable.const d))
          (Computable.const 1)))
    exact Computable.cond (hchgc.comp Computable.snd) hsome (Computable.const none)
  -- the Kraft weight of the request stream is at most `1`
  have hweight : ∀ ctx : BitString,
      (∑' k, match req ctx k with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1 :=
    fun ctx => kraft_weight_of_charged_requests hgge hdrop hdle hchg_iff hreqdef ctx
  -- the Kraft-Chaitin machine
  obtain ⟨alloc, halloccomp, hallocmatch, hallocprefix⟩ :=
    exists_online_prefixFree_family req hreqc hweight
  obtain ⟨M', hM', hmach⟩ :=
    construct_prefix_machine req alloc hreqc halloccomp hallocmatch hallocprefix
  obtain ⟨c, hc⟩ := hU.invariance hM'
  refine ⟨d + 1 + c, fun n => ?_⟩
  -- the first stage at which `g` reaches `f n` is charged, and asks for length `f n + d + 1`
  have hex : ∃ s, g s n = f n := by
    obtain ⟨s₀, hs₀⟩ := hglim n
    exact ⟨s₀, hs₀ s₀ le_rfl⟩
  obtain ⟨s₀, hval, hmin⟩ : ∃ s, g s n = f n ∧ ∀ t, t < s → g t n ≠ f n :=
    ⟨Nat.find hex, Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩
  have hcharged : chg (Nat.pair n s₀) = true := by
    refine (hchg_iff _).2 ?_
    simp only [Nat.unpair_pair]
    show s₀ = 0 ∨ g s₀ n < g (s₀ - 1) n
    rcases Nat.eq_zero_or_pos s₀ with h0 | hpos
    · exact Or.inl h0
    · refine Or.inr ?_
      have hprev : g (s₀ - 1) n ≠ f n := hmin _ (by omega)
      have hge : f n ≤ g (s₀ - 1) n := hgge _ _
      omega
  have hreqval : req [] (Nat.pair n s₀) = some (e n, f n + d + 1) := by
    rw [hreqdef]
    simp [hcharged, Nat.unpair_pair, hval]
  obtain ⟨p, hp, hplen⟩ := hallocmatch [] (Nat.pair n s₀) (e n) (f n + d + 1) hreqval
  have hprod : produces M' p [] (e n) := by
    have hM'p := hmach [] (Nat.pair n s₀) (e n) (f n + d + 1) p hreqval hp
    change (e n) ∈ M' (p, [])
    rw [hM'p]
    exact Part.mem_some _
  have hM'le : KP M' (e n) [] ≤ ((f n + d + 1 : ℕ) : ENat) := by
    have hkp := KP_le_programLength_of_produces hprod
    simpa [programLength, hplen] using hkp
  calc KPPlain U (e n) = KP U (e n) [] := rfl
    _ ≤ KP M' (e n) [] + (c : ENat) := hc (e n) []
    _ ≤ ((f n + d + 1 : ℕ) : ENat) + (c : ENat) := by gcongr
    _ = (f n : ENat) + ((d + 1 + c : ℕ) : ENat) := by push_cast; ring

/-- For an upper semicomputable integer-valued `f` and a computable injection `e : ℕ →
BitString` coding the naturals as strings, `K(e n) ≤ f(n) + O(1)` holds if and only if `∑ₙ
2^{-f(n)}` is finite. Owner: Chapter 4; the two directions are the honest leaves
`tsum_two_pow_neg_ne_top_of_KPPlain_le` and `KPPlain_le_of_tsum_two_pow_neg_ne_top`, and
this `↔` form is assembled from them. Recalled by SUV p. 168 (Theorem 113), where Chapter 5
aliases it as `KPNat_le_iff_tsum_two_pow_neg_ne_top`.  SUV Theorem 62 (Chapter 4, p. 100). -/
theorem KPPlain_le_iff_tsum_two_pow_neg_ne_top {U : Map}
    (hU : IsOptimalPrefixConditional U) {e : ℕ → BitString} (hcomp : Computable e)
    (hinj : Function.Injective e) {f : ℕ → ℕ} (hf : IsUpperSemicomputableNat f) :
    (∃ c : ℕ, ∀ n, KPPlain U (e n) ≤ (f n : ENat) + (c : ENat)) ↔
      (∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤ :=
  ⟨tsum_two_pow_neg_ne_top_of_KPPlain_le hU hinj hf,
    KPPlain_le_of_tsum_two_pow_neg_ne_top hU hcomp hf⟩

end Kolmogorov
