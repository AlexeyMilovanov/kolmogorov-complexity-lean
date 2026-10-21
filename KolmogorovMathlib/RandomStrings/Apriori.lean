/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Basic

/-!
# A priori complexity functions: entropy functions, existence of a universal one, and `min`

* `ov F`, the overgraph; entropy functions are `Kolmogorov.IsEntropyFun` (Kraft through finite
  partial sums, c.e. overgraph), the two conditions making `F : BitString → ℕ` an
  `AprioriComplexity`.
* `exists_universal_apriori`: a universal a priori complexity function exists, namely `K_U` for an
  optimal prefix decompressor `U` (`Kolmogorov.exists_isOptimalPrefixConditional`); universality
  follows from the exact `min` construction
  `Kolmogorov.exists_isOptimalPrefixConditional_min_toNat`.
* `Hmin K F = min (K.H + 5, F + 3)` and `exists_apriori_min`: for universal `K` and an entropy
  function `F`, `Hmin K F` is again a universal a priori complexity function (Claim 1 of the
  paper, which here needs no prefix machines).
-/

namespace Kolmogorov.RandomStrings

/-- The overgraph `ov F = {(x, y) | F x ≤ y}`. -/
def ov (F : BitString → ℕ) : Set (BitString × ℕ) := {p | F p.1 ≤ p.2}

/-- The function of an `AprioriComplexity` is an entropy function. -/
theorem AprioriComplexity.entropy (K : AprioriComplexity) : IsEntropyFun K.H :=
  ⟨K.kraft, K.re⟩

/-- There are at most `2 ^ n` strings of length `n` in any finite set. -/
theorem card_filter_length_le (S : Finset BitString) (n : ℕ) :
    (S.filter fun x => x.length = n).card ≤ 2 ^ n := by
  classical
  calc (S.filter fun x => x.length = n).card
      ≤ ((Finset.univ : Finset (List.Vector Bool n)).image fun v => v.toList).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_image]
        exact ⟨⟨x, hx.2⟩, Finset.mem_univ _, rfl⟩
    _ ≤ (Finset.univ : Finset (List.Vector Bool n)).card := Finset.card_image_le
    _ = 2 ^ n := by simp [Finset.card_univ, card_vector]

/-- Kraft for `2|x| + 3`: grouped by length, `∑_n 2^n 2^{-(2n+3)} ≤ 1/4`. -/
theorem kraft_two_len_add_three (S : Finset BitString) :
    ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (2 * x.length + 3) ≤ 1 := by
  classical
  obtain ⟨M, hmaps⟩ : ∃ M, ∀ x ∈ S, x.length ∈ Finset.range M := by
    refine ⟨(S.image List.length).sup id + 1, fun x hx => ?_⟩
    rw [Finset.mem_range]
    have : x.length ≤ (S.image List.length).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hx)
    omega
  calc ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (2 * x.length + 3)
      = ∑ n ∈ Finset.range M, ∑ x ∈ S with x.length = n, (2 : ℝ)⁻¹ ^ (2 * x.length + 3) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ n ∈ Finset.range M, (8 : ℝ)⁻¹ * (1 / 2 : ℝ) ^ n := by
        apply Finset.sum_le_sum
        intro n _
        have hc : ∑ x ∈ S with x.length = n, (2 : ℝ)⁻¹ ^ (2 * x.length + 3)
            = ((S.filter fun x => x.length = n).card : ℝ) * (2 : ℝ)⁻¹ ^ (2 * n + 3) := by
          rw [Finset.sum_congr rfl (g := fun _ => (2 : ℝ)⁻¹ ^ (2 * n + 3))
            (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul]
        rw [hc]
        have hcard : ((S.filter fun x => x.length = n).card : ℝ) ≤ 2 ^ n := by
          exact_mod_cast card_filter_length_le S n
        have hpos : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (2 * n + 3) := by positivity
        calc ((S.filter fun x => x.length = n).card : ℝ) * (2 : ℝ)⁻¹ ^ (2 * n + 3)
            ≤ 2 ^ n * (2 : ℝ)⁻¹ ^ (2 * n + 3) := mul_le_mul_of_nonneg_right hcard hpos
          _ = (8 : ℝ)⁻¹ * (1 / 2 : ℝ) ^ n := by
            have h2 : (2 : ℝ)⁻¹ ^ (2 * n + 3) = (2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ ^ n * (8 : ℝ)⁻¹ := by
              rw [show 2 * n + 3 = n + n + 3 by ring, pow_add, pow_add]; norm_num
            have h3 : (2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n = 1 := by
              rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
            rw [h2, one_div]
            calc (2 : ℝ) ^ n * ((2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ ^ n * (8 : ℝ)⁻¹)
                = ((2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n) * ((8 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ n) := by ring
              _ = (8 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ n := by rw [h3, one_mul]
    _ = (8 : ℝ)⁻¹ * ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n := by rw [Finset.mul_sum]
    _ ≤ (8 : ℝ)⁻¹ * 2 := by gcongr; exact sum_geometric_two_le M
    _ ≤ 1 := by norm_num

/-- The `Part` used in `REPred` is defined exactly on the predicate. -/
theorem assert_unit_dom (P : Prop) : (Part.assert P fun _ => Part.some ()).Dom ↔ P :=
  ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩

/-- The union of two c.e. predicates is c.e. -/
theorem REPred_or {α : Type*} [Primcodable α] {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun a => p a ∨ q a := by
  obtain ⟨k, hk, H⟩ := Partrec.merge' (f := fun a => Part.assert (p a) fun _ => Part.some ())
    (g := fun a => Part.assert (q a) fun _ => Part.some ()) hp hq
  exact hk.dom_re.of_eq fun a =>
    (H a).2.trans (or_congr (assert_unit_dom _) (assert_unit_dom _))

/-- Shifting an overgraph: if `ov G` is c.e., so is `ov (G + c)`. -/
theorem REPred_ov_add {G : BitString → ℕ} (c : ℕ)
    (hG : REPred fun p : BitString × ℕ => G p.1 ≤ p.2) :
    REPred fun p : BitString × ℕ => G p.1 + c ≤ p.2 := by
  have hg : Computable fun p : BitString × ℕ => (p.1, p.2 - c) :=
    Computable.fst.pair ((Primrec.nat_sub.to_comp).comp Computable.snd (Computable.const c))
  have h1 : Partrec fun p : BitString × ℕ =>
      Part.assert (G p.1 ≤ p.2 - c) fun _ => Part.some () := Partrec.comp hG hg
  have hc : Computable fun p : BitString × ℕ => decide (c ≤ p.2) :=
    (Primrec.nat_le.decide.to_comp).comp (Computable.const c) Computable.snd
  have h2 := Partrec.cond hc h1 Partrec.none
  refine h2.dom_re.of_eq fun p => ?_
  by_cases h : c ≤ p.2
  · simp only [h, decide_true, Bool.cond_true]
    rw [assert_unit_dom]; omega
  · simp only [h, decide_false, Bool.cond_false]
    exact ⟨fun hd => (hd : False).elim, fun h' => absurd h' (by omega)⟩

/-- `F₀ x = 2|x| + 3` is an entropy function. -/
theorem entropy_two_len_add_three : IsEntropyFun fun x : BitString => 2 * x.length + 3 := by
  refine ⟨kraft_two_len_add_three, ?_⟩
  have hc : Computable fun p : BitString × ℕ => decide (2 * p.1.length + 3 ≤ p.2) :=
    (Primrec.nat_le.decide.to_comp).comp
      ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.list_length.comp Primrec.fst)) (Primrec.const 3)).to_comp)
      Computable.snd
  exact (ComputablePred.to_re (Computable.computablePred hc)).of_eq fun p => Iff.rfl

/-! ### Stage approximations of c.e. predicates -/

/-- Stage approximation of a c.e. predicate: `P b ↔ ∃ k, f b k = true` with `f` primitive
recursive (`f b k`: the code of the semi-decision procedure halts on `b` within `k` steps). -/
theorem REPred.exists_stage {β : Type*} [Primcodable β] {P : β → Prop} (hP : REPred P) :
    ∃ f : β → ℕ → Bool, Primrec₂ f ∧ ∀ b, P b ↔ ∃ k, f b k = true := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hP
  refine ⟨fun b k => (Nat.Partrec.Code.evaln k c (Encodable.encode b)).isSome, ?_, fun b => ?_⟩
  · exact Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.snd.pair (Primrec.const c)).pair (Primrec.encode.comp Primrec.fst)))
  · have key : (Nat.Partrec.Code.eval c (Encodable.encode b)).Dom ↔ P b := by
      rw [hc]
      simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
      exact assert_unit_dom _
    rw [← key]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 (Part.get_mem h)
      exact ⟨k, Option.isSome_iff_exists.2 ⟨_, hk⟩⟩
    · rintro ⟨k, hk⟩
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
      exact Part.dom_iff_mem.2 ⟨y, Nat.Partrec.Code.evaln_sound hy⟩

/-- A projection of a c.e. predicate along `ℕ` is c.e. (dovetailing). -/
theorem REPred_exists_nat {α : Type*} [Primcodable α] {p : ℕ → α → Prop}
    (hp : REPred fun q : ℕ × α => p q.1 q.2) : REPred fun a => ∃ n, p n a := by
  obtain ⟨f, hf, hfP⟩ := REPred.exists_stage hp
  have hg : Computable₂ fun (a : α) (m : ℕ) => f (m.unpair.1, a) m.unpair.2 :=
    (hf.comp ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair Primrec.fst)
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  refine (Partrec.rfind hg.partrec₂).dom_re.of_eq fun a => ?_
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨m, hm, -⟩
    refine ⟨m.unpair.1, (hfP (m.unpair.1, a)).2 ⟨m.unpair.2, ?_⟩⟩
    simpa using hm
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk⟩ := (hfP (n, a)).1 hn
    refine ⟨Nat.pair n k, ?_, fun _ => trivial⟩
    simp [Nat.unpair_pair, hk]

/-! ### A universal a priori complexity function -/

/-- A universal a priori complexity function exists: the prefix complexity `K_U` of an optimal
prefix decompressor `U`.  For an entropy function `F`, the exact `min` construction gives an
optimal `U'` with `K_U' = min (K_U + 5, F + 3)`, and optimality of `U` gives
`K_U ≤ K_U' + c ≤ F + 3 + c`. -/
theorem exists_universal_apriori : ∃ K : AprioriComplexity, K.Universal := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  refine ⟨⟨fun x => (KPPlain U x).toNat, KPPlain_toNat_kraft hU, REPred_KPPlain_toNat_le hU⟩,
    fun F => ?_⟩
  obtain ⟨U', hU', hmin⟩ := exists_isOptimalPrefixConditional_min_toNat hU ⟨F.kraft, F.re⟩
  obtain ⟨c, hc⟩ := hU.2 U' hU'.1
  refine ⟨c + 3, fun x => ?_⟩
  have h1 : (KPPlain U x).toNat ≤ (KPPlain U' x).toNat + c := by
    have hle : KPPlain U x ≤ KPPlain U' x + (c : ℕ∞) := hc x []
    obtain ⟨k, hk⟩ :=
      ENat.ne_top_iff_exists.1 (KPPlain_ne_top_of_isOptimalPrefixConditional hU' x)
    rw [← hk] at hle ⊢
    rw [ENat.toNat_natCast]
    exact ENat.toNat_le_of_le_natCast (by exact_mod_cast hle)
  have h2 := hmin x
  change (KPPlain U x).toNat ≤ F.H x + (c + 3)
  omega

/-- `H = min (K + 5, F + 3)`. -/
def Hmin (K : AprioriComplexity) (F : BitString → ℕ) (x : BitString) :
    ℕ := min (K.H x + 5) (F x + 3)

/-- The Kraft condition for `Hmin`: `2^{-Hmin} ≤ 2^{-5} 2^{-K} + 2^{-3} 2^{-F}`, so the partial
sums are at most `1/32 + 1/8 < 1`. -/
theorem Hmin_kraft (K : AprioriComplexity) (F : BitString → ℕ) (hF : IsEntropyFun F)
    (S : Finset BitString) :
    ∑ x ∈ S, (2 : ℝ)⁻¹ ^ Hmin K F x ≤ 1 := by
  have hpt : ∀ x, (2 : ℝ)⁻¹ ^ Hmin K F x ≤
      (2 : ℝ)⁻¹ ^ 5 * (2 : ℝ)⁻¹ ^ K.H x + (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ F x := by
    intro x
    have a1 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 5 * (2 : ℝ)⁻¹ ^ K.H x := by positivity
    have a2 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ F x := by positivity
    unfold Hmin
    rcases le_total (K.H x + 5) (F x + 3) with h | h
    · rw [min_eq_left h]
      have e1 : (2 : ℝ)⁻¹ ^ (K.H x + 5) = (2 : ℝ)⁻¹ ^ 5 * (2 : ℝ)⁻¹ ^ K.H x := by
        rw [pow_add]; ring
      rw [e1]; linarith
    · rw [min_eq_right h]
      have e1 : (2 : ℝ)⁻¹ ^ (F x + 3) = (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ F x := by
        rw [pow_add]; ring
      rw [e1]; linarith
  calc ∑ x ∈ S, (2 : ℝ)⁻¹ ^ Hmin K F x
      ≤ ∑ x ∈ S, ((2 : ℝ)⁻¹ ^ 5 * (2 : ℝ)⁻¹ ^ K.H x + (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ F x) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = (2 : ℝ)⁻¹ ^ 5 * ∑ x ∈ S, (2 : ℝ)⁻¹ ^ K.H x
          + (2 : ℝ)⁻¹ ^ 3 * ∑ x ∈ S, (2 : ℝ)⁻¹ ^ F x := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (2 : ℝ)⁻¹ ^ 5 * 1 + (2 : ℝ)⁻¹ ^ 3 * 1 := by
        gcongr
        · exact K.kraft S
        · exact hF.kraft S
    _ ≤ 1 := by norm_num

/-- The overgraph of `Hmin` is the union of two c.e. sets, hence c.e. -/
theorem Hmin_re (K : AprioriComplexity) (F : BitString → ℕ) (hF : IsEntropyFun F) :
    REPred fun p : BitString × ℕ => Hmin K F p.1 ≤ p.2 := by
  refine (REPred_or (REPred_ov_add 5 K.re)
    (REPred_ov_add (G := F) 3 (hF.re.of_eq fun _ => Iff.rfl))).of_eq fun p => ?_
  unfold Hmin
  exact min_le_iff.symm

/-- `Hmin K F` as an `AprioriComplexity`. -/
def HminApriori (K : AprioriComplexity) (F : BitString → ℕ) (hF : IsEntropyFun F) :
    AprioriComplexity :=
  ⟨Hmin K F, Hmin_kraft K F hF, Hmin_re K F hF⟩

/-- Claim 1: `Hmin K F` is universal when `K` is (`Hmin K F ≤ K.H + 5`). -/
theorem HminApriori_universal (K : AprioriComplexity) (hK : K.Universal) (F : BitString → ℕ)
    (hF : IsEntropyFun F) : (HminApriori K F hF).Universal := by
  intro G
  obtain ⟨c, hc⟩ := hK G
  refine ⟨c + 5, fun x => ?_⟩
  change min (K.H x + 5) (F x + 3) ≤ G.H x + (c + 5)
  calc min (K.H x + 5) (F x + 3) ≤ K.H x + 5 := min_le_left _ _
    _ ≤ G.H x + c + 5 := by have := hc x; omega
    _ = G.H x + (c + 5) := by ring

end Kolmogorov.RandomStrings
