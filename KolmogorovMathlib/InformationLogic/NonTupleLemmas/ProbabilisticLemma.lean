import KolmogorovMathlib.InformationLogic.NonTupleComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.Complexity.Information.MutualInformation
import KolmogorovMathlib.Complexity.EnumerableFamilies.CountingBounds
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Probabilistic Lemma

A probabilistic (counting) argument for the existence of computable families of functions on
triples of `n`-bit words with prescribed behaviour: finite counts of `n`-bit words and of triples
of them, an abstract counting bound for tables `Q : T → W` with `Q t ∈ D t` for at least `K`
indices `t`, and the computable check that turns this bound into an existence statement.  The
module is part of `KolmogorovMathlib.InformationLogic.NonTupleLemmas` and belongs to the
treatment of non-tuple (non-Shannon-type) inequalities in the book by Shen, Uspensky and
Vereshchagin, "Kolmogorov complexity and algorithmic randomness".
-/

namespace Kolmogorov
namespace InformationLogic
open ProblemCalculus

/-- The set of `n`-bit words is finite with `2 ^ n` elements. -/
private lemma exists_computable_family_problemK_quad_ge_words_ncard (n : ℕ) :
    {w : BitString | w.length = n}.Finite ∧ {w : BitString | w.length = n}.ncard = 2 ^ n := by
  have : {w : BitString | w.length = n} =
      (fun v : List.Vector Bool n => v.toList) '' Set.univ := by
    ext w; simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]; constructor
    · intro h; exact ⟨⟨w, h⟩, rfl⟩
    · rintro ⟨v, rfl⟩; exact v.2
  rw [this]
  refine ⟨Set.toFinite _, ?_⟩
  rw [Set.ncard_image_of_injective _ (fun v w h => List.Vector.toList_injective h), Set.ncard_univ,
    Nat.card_eq_fintype_card, card_vector]
  simp

/-- The set of triples of `n`-bit words is finite with `2 ^ (3n)` elements. -/
private lemma exists_computable_family_problemK_quad_ge_triples_ncard (n : ℕ) :
    {t : BitString × BitString × BitString | t.1.length = n ∧ t.2.1.length = n ∧
      t.2.2.length = n}.Finite ∧
    {t : BitString × BitString × BitString | t.1.length = n ∧ t.2.1.length = n ∧
      t.2.2.length = n}.ncard = 2 ^ (3 * n) := by
  obtain ⟨hf, hc⟩ := exists_computable_family_problemK_quad_ge_words_ncard n
  have : {t : BitString × BitString × BitString | t.1.length = n ∧ t.2.1.length = n ∧
      t.2.2.length = n} = {w : BitString | w.length = n} ×ˢ
        ({w : BitString | w.length = n} ×ˢ {w : BitString | w.length = n}) := by
    ext t; simp [Set.mem_prod]
  rw [this]
  refine ⟨hf.prod (hf.prod hf), ?_⟩
  rw [Set.ncard_prod, Set.ncard_prod, hc]
  ring

/-- Auxiliary definition for the probabilistic proof: the triples `t = (a, b, e)` of `n`-bit words
"served" by a family `F` of pairs of functions `(f, g)` for the function `Qn` and the
orientation `(u, v, w)`: `f (u t) = v t` and `g (w t) = Qn a b e` for some `(f, g) ∈ F`. -/
private def exists_computable_family_problemK_quad_ge_served (n : ℕ)
    (Qn : BitString → BitString → BitString → BitString)
    (F : Set ((BitString → BitString) × (BitString → BitString)))
    (u v w : BitString × BitString × BitString → BitString) :
    Set (BitString × BitString × BitString) :=
  {t | t.1.length = n ∧ t.2.1.length = n ∧ t.2.2.length = n ∧
    ∃ fg ∈ F, fg.1 (u t) = v t ∧ fg.2 (w t) = Qn t.1 t.2.1 t.2.2}

/-- Auxiliary definition for the probabilistic proof: `Qn` is *good* for `n` and the slack
constant `c` if every finite family `F` of pairs of functions with fewer than
`2 ^ (2n − logSlack c n)` members serves less than `1/8` of the triples of `n`-bit words, in
each of the three orientations `(a → c) ∧ (b → Q)`, `(c → b) ∧ (a → Q)`, `(b → a) ∧ (c → Q)`
(`(a, b, e)` the triple, `e` playing the role of the book's `c`). -/
private def exists_computable_family_problemK_quad_ge_good (c n : ℕ)
    (Qn : BitString → BitString → BitString → BitString) : Prop :=
  ∀ F : Set ((BitString → BitString) × (BitString → BitString)), F.Finite →
    F.ncard * 2 ^ logSlack c n < 2 ^ (2 * n) →
    8 * (exists_computable_family_problemK_quad_ge_served n Qn F
      (fun t => t.1) (fun t => t.2.2) (fun t => t.2.1)).ncard < 2 ^ (3 * n) ∧
    8 * (exists_computable_family_problemK_quad_ge_served n Qn F
      (fun t => t.2.2) (fun t => t.2.1) (fun t => t.1)).ncard < 2 ^ (3 * n) ∧
    8 * (exists_computable_family_problemK_quad_ge_served n Qn F
      (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2)).ncard < 2 ^ (3 * n)

/-- Auxiliary: a pair of partial functions on `n`-bit vectors (the restriction of a pair of
functions on all words to `n`-bit words, `none` standing for a value that is not an `n`-bit
word). -/
private abbrev exists_computable_family_problemK_quad_ge_exists_Pair (n : ℕ) : Type :=
  (List.Vector Bool n → Option (List.Vector Bool n)) ×
    (List.Vector Bool n → Option (List.Vector Bool n))

/-- Auxiliary: the abstract (finite-type) version of
`exists_computable_family_problemK_quad_ge_served`: the triples `t` of `n`-bit vectors served by
the finite family `G` of pairs of partial functions for `Qn` in the orientation `(u, v, w)`:
`f (u t) = some (v t)` and `g (w t) = some (Qn t.1 t.2.1 t.2.2)` for some `(f, g) ∈ G`. -/
private def exists_computable_family_problemK_quad_ge_exists_servedAbs (n : ℕ)
    (Qn : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n)
    (G : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n))
    (u v w : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n →
      List.Vector Bool n) :
    Set (List.Vector Bool n × List.Vector Bool n × List.Vector Bool n) :=
  {t | ∃ fg ∈ G, fg.1 (u t) = some (v t) ∧ fg.2 (w t) = some (Qn t.1 t.2.1 t.2.2)}

/-- Auxiliary: abstract version of `exists_computable_family_problemK_quad_ge_good`. -/
private def exists_computable_family_problemK_quad_ge_exists_goodAbs (c n : ℕ)
    (Qn : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n) :
    Prop :=
  ∀ G : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n),
    G.card * 2 ^ logSlack c n < 2 ^ (2 * n) →
    8 * (exists_computable_family_problemK_quad_ge_exists_servedAbs n Qn G
      (fun t => t.1) (fun t => t.2.2) (fun t => t.2.1)).ncard < 2 ^ (3 * n) ∧
    8 * (exists_computable_family_problemK_quad_ge_exists_servedAbs n Qn G
      (fun t => t.2.2) (fun t => t.2.1) (fun t => t.1)).ncard < 2 ^ (3 * n) ∧
    8 * (exists_computable_family_problemK_quad_ge_exists_servedAbs n Qn G
      (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2)).ncard < 2 ^ (3 * n)

/-- Step 3 of the proof of `exists_computable_family_problemK_quad_ge_exists`:
the numerical inequality of the union bound.  For a suitable constant `c` (e.g. `c = 8`) and all
large `n`, with `L = logSlack c n`, `m = 2^n`, `K = 2^(3n-3)` (the threshold `m^3/8` of the
triples), `B = 2^(2n) / 2^L` (the bound for the size of a family) and `P = (m+1)^(2m)` (the number
of pairs of partial functions `W n → Option (W n)`): `(P+1)^B · 3 · 175^K < (2^L)^K`.
(Taking logarithms: `B (2m log(m+1) + 1) + log 3 + K log 175 < L K`, i.e. roughly
`16 (n+1) < 2^L (L - 7.5)`, true for large `n` since `2^L ≥ n^c`.) -/
private theorem exists_computable_family_problemK_quad_ge_arith :
    ∃ c N : ℕ, ∀ n ≥ N, 3 ≤ n ∧
      (((2 ^ n + 1) ^ 2 ^ n) ^ 2 + 1) ^ (2 ^ (2 * n) / 2 ^ logSlack c n) * 3 *
        175 ^ (2 ^ (3 * n - 3)) < (2 ^ logSlack c n) ^ (2 ^ (3 * n - 3)) := by
  have h175 : ∀ k : ℕ, 3 ≤ k → 3 * 175 ^ k < 256 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      rw [pow_succ, pow_succ]
      nlinarith [Nat.zero_le (175 ^ k)]
  refine ⟨8, 3, fun n hn => ⟨hn, ?_⟩⟩
  have hsz : (Nat.bits n).length = n.size := Nat.size_eq_bits_len n
  have hpos : 0 < n.size := Nat.size_pos.2 (by omega)
  have hlt := Nat.lt_size_self n
  have hL : logSlack 8 n = 8 * n.size + 8 := by
    unfold logSlack; rw [hsz]
  rw [hL]
  have h2n : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul]; ring_nf
  have h8K : 8 * 2 ^ (3 * n - 3) = (2 ^ n) ^ 3 := by
    have : 8 * 2 ^ (3 * n - 3) = 2 ^ (3 * n - 3 + 3) := by rw [pow_add]; ring
    rw [this, ← pow_mul]; congr 1; omega
  rw [h2n]
  generalize hm : 2 ^ n = m at *
  generalize hK : 2 ^ (3 * n - 3) = K at *
  have hK3 : 3 ≤ K := by
    rw [← hK]
    calc 3 ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (3 * n - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm1 : 1 ≤ m := by rw [← hm]; exact Nat.one_le_two_pow
  have hs_big : 2 * n + 3 ≤ 2 ^ (8 * n.size + 8) := by
    calc 2 * n + 3 ≤ 256 * 2 ^ n.size := by omega
      _ = 2 ^ (n.size + 8) := by rw [pow_add]; ring
      _ ≤ 2 ^ (8 * n.size + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize hs : 2 ^ (8 * n.size + 8) = s at *
  have hs0 : 0 < s := by rw [← hs]; positivity
  have hB := Nat.div_mul_le_self (m ^ 2) s
  generalize hBdef : m ^ 2 / s = B at *
  have hA : (m + 1) ^ m ≤ 2 ^ ((n + 1) * m) := by
    calc (m + 1) ^ m ≤ (2 ^ (n + 1)) ^ m := by
          apply Nat.pow_le_pow_left
          rw [pow_succ, hm]; omega
      _ = 2 ^ ((n + 1) * m) := by rw [← pow_mul]
  have hP : ((m + 1) ^ m) ^ 2 + 1 ≤ 2 ^ (2 * ((n + 1) * m) + 1) := by
    have h1 : ((m + 1) ^ m) ^ 2 ≤ 2 ^ (2 * ((n + 1) * m)) := by
      calc ((m + 1) ^ m) ^ 2 ≤ (2 ^ ((n + 1) * m)) ^ 2 := Nat.pow_le_pow_left hA 2
        _ = 2 ^ (2 * ((n + 1) * m)) := by rw [← pow_mul]; ring_nf
    have h2 : 1 ≤ 2 ^ (2 * ((n + 1) * m)) := Nat.one_le_two_pow
    rw [pow_succ 2 (2 * ((n + 1) * m))]; omega
  set E := 2 * ((n + 1) * m) + 1 with hE
  have hEB : E * B ≤ 8 * K := by
    have h1 : E * B * s ≤ 8 * K * s := by
      calc E * B * s = E * (B * s) := by ring
        _ ≤ E * m ^ 2 := Nat.mul_le_mul_left _ hB
        _ ≤ (2 * n + 3) * m * m ^ 2 := by
          apply Nat.mul_le_mul_right
          rw [hE]; nlinarith
        _ = (2 * n + 3) * (8 * K) := by rw [h8K]; ring
        _ ≤ s * (8 * K) := Nat.mul_le_mul_right _ hs_big
        _ = 8 * K * s := by ring
    exact Nat.le_of_mul_le_mul_right h1 hs0
  have hpow : (((m + 1) ^ m) ^ 2 + 1) ^ B ≤ 2 ^ (E * B) := by
    calc (((m + 1) ^ m) ^ 2 + 1) ^ B ≤ (2 ^ E) ^ B := Nat.pow_le_pow_left hP B
      _ = 2 ^ (E * B) := by rw [← pow_mul]
  have h3 := h175 K hK3
  have hL16 : 16 * K ≤ (8 * n.size + 8) * K := Nat.mul_le_mul_right _ (by omega)
  calc (((m + 1) ^ m) ^ 2 + 1) ^ B * 3 * 175 ^ K
      ≤ 2 ^ (E * B) * 3 * 175 ^ K := by gcongr
    _ = 2 ^ (E * B) * (3 * 175 ^ K) := by ring
    _ < 2 ^ (E * B) * 256 ^ K := by
        apply Nat.mul_lt_mul_of_pos_left h3 (by positivity)
    _ = 2 ^ (E * B + 8 * K) := by
        rw [pow_add, show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul]
    _ ≤ 2 ^ ((8 * n.size + 8) * K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ (8 * n.size + 8)) ^ K := by rw [pow_mul]
    _ = s ^ K := by rw [hs]

/-- Step 1 of the proof of
`exists_computable_family_problemK_quad_ge_count`:
AM–GM in `ℕ`: for a finset `A` of size `K` and natural numbers `x t`,
`K^K ∏_{t∈A} x t ≤ (∑_{t∈A} x t)^K`. -/
private theorem exists_computable_family_problemK_quad_ge_amgm
    {T : Type*} (A : Finset T) (x : T → ℕ) :
    A.card ^ A.card * ∏ t ∈ A, x t ≤ (∑ t ∈ A, x t) ^ A.card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have h := Real.geom_mean_le_arith_mean A (fun _ => (1 : ℝ)) (fun t => (x t : ℝ))
    (fun _ _ => zero_le_one) (by simpa using hc) (fun _ _ => Nat.cast_nonneg _)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hP : 0 ≤ ∏ t ∈ A, (x t : ℝ) := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  have h2 : ∏ t ∈ A, (x t : ℝ) ≤ ((∑ t ∈ A, (x t : ℝ)) / A.card) ^ A.card := by
    have := pow_le_pow_left₀ (Real.rpow_nonneg hP _) h A.card
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP, inv_mul_cancel₀ hc.ne', Real.rpow_one] at this
    exact this
  have h3 : (A.card : ℝ) ^ A.card * ∏ t ∈ A, (x t : ℝ) ≤ (∑ t ∈ A, (x t : ℝ)) ^ A.card := by
    calc (A.card : ℝ) ^ A.card * ∏ t ∈ A, (x t : ℝ)
        ≤ (A.card : ℝ) ^ A.card * ((∑ t ∈ A, (x t : ℝ)) / A.card) ^ A.card :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; field_simp
  exact_mod_cast h3

/-- Step 2 of the proof of
`exists_computable_family_problemK_quad_ge_count`:
the abstract counting bound.  For finite types `T`, `W`, sets `D t ⊆ W` with `∑_t |D t| ≤ S` and
`K ≤ |T|`, the number of tables `Q : T → W` with `Q t ∈ D t` for at least `K` indices `t`
satisfies `#{Q} · K^K ≤ C(|T|, K) · |W|^(|T|-K) · S^K`.  (Union over the `K`-subsets `A` of the
tables with `Q t ∈ D t` on all of `A`, each of which is `|W|^(|T|-K) ∏_{t∈A} |D t|`, then
AM–GM `K^K ∏_{t∈A}|D t| ≤ (∑_{t∈A}|D t|)^K ≤ S^K`.) -/
private theorem exists_computable_family_problemK_quad_ge_abstract
    {T W : Type*} [Fintype T] [Fintype W] [DecidableEq W]
    (D : T → Finset W) (K S : ℕ)
    (hS : ∑ t, (D t).card ≤ S) :
    {Q : T → W | K ≤ (Finset.univ.filter (fun t => Q t ∈ D t)).card}.ncard * K ^ K ≤
      (Fintype.card T).choose K * Fintype.card W ^ (Fintype.card T - K) * S ^ K := by
  classical
  have hsub : {Q : T → W | K ≤ (Finset.univ.filter (fun t => Q t ∈ D t)).card} ⊆
      ↑((Finset.univ.powersetCard K).biUnion (fun A => Fintype.piFinset
        (fun t => if t ∈ A then D t else Finset.univ))) := by
    intro Q hQ
    simp only [Set.mem_ofPred_eq] at hQ
    obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hQ
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_powersetCard, Fintype.mem_piFinset]
    refine ⟨A, ⟨Finset.subset_univ _, hAc⟩, fun t => ?_⟩
    by_cases ht : t ∈ A
    · have := hA ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      simp [ht, this]
    · simp [ht]
  have hone : ∀ A ∈ Finset.univ.powersetCard K, (Fintype.piFinset
        (fun t => if t ∈ A then D t else Finset.univ)).card * K ^ K ≤
        Fintype.card W ^ (Fintype.card T - K) * S ^ K := by
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    obtain ⟨-, hAc⟩ := hA
    rw [Fintype.card_piFinset]
    have h1 : ∏ t, (if t ∈ A then D t else Finset.univ).card =
        (∏ t ∈ A, (D t).card) * Fintype.card W ^ (Fintype.card T - K) := by
      calc _ = ∏ t, (if t ∈ A then (D t).card else Fintype.card W) := by
            apply Finset.prod_congr rfl
            intro t _
            split_ifs <;> simp
        _ = (∏ t ∈ Finset.univ.filter (· ∈ A), (D t).card) *
            ∏ t ∈ Finset.univ.filter (fun t => ¬ t ∈ A), Fintype.card W := Finset.prod_ite _ _
        _ = _ := by
            congr 1
            · congr 1; ext t; simp
            · rw [Finset.prod_const]
              congr 1
              rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
              simp [hAc]
    have h2 := exists_computable_family_problemK_quad_ge_amgm A
      (fun t => (D t).card)
    rw [hAc] at h2
    have h3 : ∑ t ∈ A, (D t).card ≤ S :=
      le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ A)) hS
    calc _ = Fintype.card W ^ (Fintype.card T - K) * (K ^ K * ∏ t ∈ A, (D t).card) := by
          rw [h1]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (h2.trans (Nat.pow_le_pow_left h3 _))
  calc _ ≤ (↑((Finset.univ.powersetCard K).biUnion (fun A => Fintype.piFinset
        (fun t => if t ∈ A then D t else Finset.univ))) : Set (T → W)).ncard * K ^ K :=
        Nat.mul_le_mul_right _ (Set.ncard_le_ncard hsub (Finset.finite_toSet _))
    _ = ((Finset.univ.powersetCard K).biUnion (fun A => Fintype.piFinset
        (fun t => if t ∈ A then D t else Finset.univ))).card * K ^ K := by
        rw [Set.ncard_coe_finset]
    _ ≤ (∑ A ∈ Finset.univ.powersetCard K, (Fintype.piFinset
        (fun t => if t ∈ A then D t else Finset.univ)).card) * K ^ K :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ A ∈ Finset.univ.powersetCard K, (Fintype.piFinset
        (fun t => if t ∈ A then D t else Finset.univ)).card * K ^ K := Finset.sum_mul _ _ _
    _ ≤ ∑ A ∈ Finset.univ.powersetCard K, Fintype.card W ^ (Fintype.card T - K) * S ^ K :=
        Finset.sum_le_sum hone
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul]; ring

/-- Step 3 of the proof of
`exists_computable_family_problemK_quad_ge_count`:
the binomial estimate `C(8K, K) ≤ (8e)^K ≤ (109/5)^K`, i.e. `C(8K,K) · 5^K ≤ 109^K`
(from `C(N,K) ≤ N^K/K!` and `K^K/K! ≤ e^K`, `8e < 21.8`). -/
private theorem exists_computable_family_problemK_quad_ge_choose
    (K : ℕ) : (8 * K).choose K * 5 ^ K ≤ 109 ^ K := by
  have h1 : (((8 * K).choose K : ℕ) : ℝ) ≤ ((8 * K : ℕ) : ℝ) ^ K / K.factorial :=
    Nat.choose_le_pow_div K (8 * K)
  have h2 : (K : ℝ) ^ K / K.factorial ≤ Real.exp 1 ^ K := by
    have := Real.pow_div_factorial_le_exp (K : ℝ) (Nat.cast_nonneg K) K
    rw [← Real.exp_nat_mul, mul_one]; exact this
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hf : (0 : ℝ) < K.factorial := by exact_mod_cast K.factorial_pos
  have h3 : (((8 * K).choose K : ℕ) : ℝ) ≤ (8 * Real.exp 1) ^ K := by
    calc _ ≤ ((8 * K : ℕ) : ℝ) ^ K / K.factorial := h1
      _ = 8 ^ K * ((K : ℝ) ^ K / K.factorial) := by push_cast; rw [mul_pow]; ring
      _ ≤ 8 ^ K * Real.exp 1 ^ K := by gcongr
      _ = _ := by rw [mul_pow]
  have h4 : (((8 * K).choose K * 5 ^ K : ℕ) : ℝ) ≤ ((109 ^ K : ℕ) : ℝ) := by
    push_cast
    calc (((8 * K).choose K : ℕ) : ℝ) * 5 ^ K ≤ (8 * Real.exp 1) ^ K * 5 ^ K := by gcongr
      _ = (40 * Real.exp 1) ^ K := by rw [← mul_pow]; ring_nf
      _ ≤ 109 ^ K := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
  exact_mod_cast h4

/-- Step 4 of the proof of
`exists_computable_family_problemK_quad_ge_count`:
the sets of admissible values.  If `t ↦ (u t, v t, w t)` is injective on triples of `n`-bit
vectors, then there are sets `D t` of `n`-bit vectors, with `∑_t |D t| ≤ |G| (2^n)^2`, such that
for every table `Q` the served set `servedAbs n Q G u v w` is exactly `{t | Q t.1 t.2.1 t.2.2 ∈ D
t}`.
(`D t = {g (w t) : (f,g) ∈ G, f (u t) = some (v t), g (w t) ≠ none}`, `|D t| ≤ d_t` the number of
`(f,g) ∈ G` with `f (u t) = some (v t)`; `∑_t d_t = ∑_{(f,g) ∈ G} #{t : f (u t) = some (v t)}
≤ |G| (2^n)^2` because such `t` is determined by `(u t, w t)` as `v t = f (u t)` is determined and
`t ↦ (u t, v t, w t)` is injective.) -/
private theorem exists_computable_family_problemK_quad_ge_dsets
    (n : ℕ)
    (G : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n))
    (u v w : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n → List.Vector Bool n)
    (hinj : Function.Injective (fun t => (u t, v t, w t))) :
    ∃ D : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n →
        Finset (List.Vector Bool n),
      ∑ t, (D t).card ≤ G.card * (2 ^ n) ^ 2 ∧
      ∀ Q : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n,
        exists_computable_family_problemK_quad_ge_exists_servedAbs n Q G u v w =
          {t | Q t.1 t.2.1 t.2.2 ∈ D t} := by
  classical
  refine ⟨fun t => Finset.univ.filter (fun y => ∃ fg ∈ G, fg.1 (u t) = some (v t) ∧
    fg.2 (w t) = some y), ?_, ?_⟩
  · have hd : ∀ t : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n,
        (Finset.univ.filter (fun y => ∃ fg ∈ G, fg.1 (u t) = some (v t) ∧
          fg.2 (w t) = some y)).card ≤
        (∑ fg ∈ G, if fg.1 (u t) = some (v t) then 1 else 0) := by
      intro t
      rw [← Finset.card_filter]
      calc _ ≤ ((G.filter (fun fg => fg.1 (u t) = some (v t))).biUnion
            (fun fg => (fg.2 (w t)).toFinset)).card := by
            apply Finset.card_le_card
            intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            obtain ⟨fg, hfg, h1, h2⟩ := hy
            simp only [Finset.mem_biUnion, Finset.mem_filter]
            exact ⟨fg, ⟨hfg, h1⟩, by simp [h2]⟩
        _ ≤ ∑ fg ∈ G.filter (fun fg => fg.1 (u t) = some (v t)),
              ((fg.2 (w t)).toFinset).card := Finset.card_biUnion_le
        _ ≤ ∑ fg ∈ G.filter (fun fg => fg.1 (u t) = some (v t)), 1 := by
            apply Finset.sum_le_sum
            intro fg _
            cases fg.2 (w t) <;> simp
        _ = _ := by simp
    calc ∑ t, (Finset.univ.filter (fun y => ∃ fg ∈ G, fg.1 (u t) = some (v t) ∧
          fg.2 (w t) = some y)).card
        ≤ ∑ t, ∑ fg ∈ G, (if fg.1 (u t) = some (v t) then 1 else 0) := Finset.sum_le_sum fun t _ =>
          hd t
      _ = ∑ fg ∈ G, ∑ t, (if fg.1 (u t) = some (v t) then 1 else 0) := Finset.sum_comm
      _ ≤ ∑ fg ∈ G, (2 ^ n) ^ 2 := by
          apply Finset.sum_le_sum
          intro fg _
          rw [← Finset.card_filter]
          have : Fintype.card (List.Vector Bool n × List.Vector Bool n) = (2 ^ n) ^ 2 := by
            simp [Fintype.card_prod, card_vector]; ring
          rw [← this]
          refine Finset.card_le_card_of_injOn (fun t => (u t, w t)) (fun _ _ => Finset.mem_univ _)
              ?_
          intro t ht t' ht' h
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
            Prod.mk.injEq] at ht ht' h
          have hv : v t = v t' := by
            have := ht.symm.trans (h.1 ▸ ht')
            exact Option.some.inj this
          exact hinj (by simp [h.1, h.2, hv])
      _ = _ := by simp
  · intro Q
    ext t
    simp [exists_computable_family_problemK_quad_ge_exists_servedAbs]

private lemma exists_computable_family_problemK_quad_ge_count_arith
    (b ch g P m K : ℕ) (hK : 0 < K)
    (h1 : b * K ^ K ≤ ch * m ^ (7 * K) * (g * m ^ 2) ^ K)
    (h2 : ch * 5 ^ K ≤ 109 ^ K) (h3 : g * P ≤ m ^ 2) (h4 : m ^ 3 = 8 * K) :
    b * P ^ K ≤ 175 ^ K * m ^ (8 * K) := by
  have hKK : 0 < K ^ K := pow_pos hK K
  have h5 : (g * m ^ 2) ^ K * P ^ K ≤ (m ^ 4) ^ K := by
    rw [← mul_pow]
    apply Nat.pow_le_pow_left
    calc g * m ^ 2 * P = (g * P) * m ^ 2 := by ring
      _ ≤ m ^ 2 * m ^ 2 := Nat.mul_le_mul_right _ h3
      _ = m ^ 4 := by ring
  have h6 : (m ^ 4) ^ K = 8 ^ K * K ^ K * m ^ K := by
    have : m ^ 4 = 8 * K * m := by rw [← h4]; ring
    rw [this, mul_pow, mul_pow]
  have h7 : (b * P ^ K * 5 ^ K) * K ^ K ≤ (875 ^ K * m ^ (8 * K)) * K ^ K := by
    calc (b * P ^ K * 5 ^ K) * K ^ K = (b * K ^ K) * (P ^ K * 5 ^ K) := by ring
      _ ≤ (ch * m ^ (7 * K) * (g * m ^ 2) ^ K) * (P ^ K * 5 ^ K) :=
          Nat.mul_le_mul_right _ h1
      _ = (ch * 5 ^ K) * m ^ (7 * K) * ((g * m ^ 2) ^ K * P ^ K) := by ring
      _ ≤ 109 ^ K * m ^ (7 * K) * (8 ^ K * K ^ K * m ^ K) := by
          rw [← h6]; exact Nat.mul_le_mul (Nat.mul_le_mul_right _ h2) h5
      _ = (109 * 8) ^ K * m ^ (7 * K + K) * K ^ K := by rw [mul_pow, pow_add]; ring
      _ ≤ (875 ^ K * m ^ (8 * K)) * K ^ K := by
          have : 7 * K + K = 8 * K := by ring
          rw [this]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num)
              _))
  have h8 := Nat.le_of_mul_le_mul_right h7 hKK
  have h9 : (b * P ^ K) * 5 ^ K ≤ (175 ^ K * m ^ (8 * K)) * 5 ^ K := by
    calc (b * P ^ K) * 5 ^ K ≤ 875 ^ K * m ^ (8 * K) := h8
      _ = (175 ^ K * m ^ (8 * K)) * 5 ^ K := by
        have : (875 : ℕ) = 175 * 5 := by norm_num
        rw [this, mul_pow]; ring
  exact Nat.le_of_mul_le_mul_right h9 (by positivity)

/-- Step 5 of the proof of
`exists_computable_family_problemK_quad_ge_count`:
the bound for one orientation: from steps 2–4 with `T = (W n)^3`, `|T| = 8K`, `K = 2^(3n-3)`,
`S = |G| m^2`: `#bad · K^K ≤ C(8K,K) m^(8K-K) (|G| m^2)^K`, `|G| 2^L ≤ m^2`, `m^4 = 8 K m`,
`C(8K,K) 5^K ≤ 109^K` hence `#bad · (2^L)^K ≤ (872/5)^K m^(8K) ≤ 175^K m^(8K)`. -/
private theorem exists_computable_family_problemK_quad_ge_oriented
    (n L : ℕ) (hn : 3 ≤ n)
    (G : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n))
    (hG : G.card * 2 ^ L < 2 ^ (2 * n))
    (u v w : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n → List.Vector Bool n)
    (hinj : Function.Injective (fun t => (u t, v t, w t))) :
    {Q : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n |
      2 ^ (3 * n) ≤ 8 * (exists_computable_family_problemK_quad_ge_exists_servedAbs n Q G
        u v w).ncard}.ncard *
        (2 ^ L) ^ (2 ^ (3 * n - 3)) ≤ 175 ^ (2 ^ (3 * n - 3)) * (2 ^ n) ^ (2 ^ (3 * n)) := by
  obtain ⟨D, hDs, hDQ⟩ :=
    exists_computable_family_problemK_quad_ge_dsets n G u v w hinj
  have hcardV : Fintype.card (List.Vector Bool n) = 2 ^ n := by simp [card_vector]
  have e3 : 3 * n - 3 + 3 = 3 * n := by omega
  have hK : 2 ^ (3 * n) = 8 * 2 ^ (3 * n - 3) := by
    calc 2 ^ (3 * n) = 2 ^ (3 * n - 3 + 3) := by rw [e3]
      _ = _ := by rw [pow_add]; ring
  have hcardT : Fintype.card (List.Vector Bool n × List.Vector Bool n × List.Vector Bool n)
      = 8 * 2 ^ (3 * n - 3) := by
    rw [← hK]
    simp only [Fintype.card_prod, hcardV]
    ring
  generalize hKdef : 2 ^ (3 * n - 3) = K at hK hcardT ⊢
  have hKpos : 0 < K := by rw [← hKdef]; positivity
  let F : (List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n) →
      (List.Vector Bool n × List.Vector Bool n × List.Vector Bool n → List.Vector Bool n) :=
    fun Q t => Q t.1 t.2.1 t.2.2
  have hF : Function.Injective F := fun Q Q' h => by
    funext a b c; exact congrFun h (a, b, c)
  have hBC : F '' {Q : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n →
      List.Vector Bool n |
      2 ^ (3 * n) ≤ 8 * (exists_computable_family_problemK_quad_ge_exists_servedAbs n Q G
        u v w).ncard} ⊆
      {Q : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n → List.Vector Bool n |
        K ≤ (Finset.univ.filter (fun t => Q t ∈ D t)).card} := by
    rintro _ ⟨Q, hQ, rfl⟩
    simp only [Set.mem_ofPred_eq] at hQ
    rw [hDQ Q] at hQ
    have : {t : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n |
        Q t.1 t.2.1 t.2.2 ∈ D t} = ↑(Finset.univ.filter (fun t => F Q t ∈ D t)) := by
      ext t; simp [F]
    rw [this, Set.ncard_coe_finset] at hQ
    change K ≤ _
    omega
  have hb := Set.ncard_le_ncard hBC (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ hF] at hb
  have h2 := exists_computable_family_problemK_quad_ge_abstract D K
    (G.card * (2 ^ n) ^ 2) hDs
  rw [hcardT, hcardV] at h2
  have h78 : 8 * K - K = 7 * K := by omega
  rw [h78] at h2
  have h3 := exists_computable_family_problemK_quad_ge_choose K
  have h4 : (2 ^ n) ^ 3 = 8 * K := by rw [← hK, ← pow_mul]; congr 1; ring
  have h5 := exists_computable_family_problemK_quad_ge_count_arith
    _ _ G.card (2 ^ L) (2 ^ n) K hKpos (le_trans (Nat.mul_le_mul_right _ hb) h2) h3
    (by
      have : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul]; congr 1; ring
      rw [← this]; exact hG.le) h4
  have h6 : (2 ^ n) ^ (2 ^ (3 * n)) = (2 ^ n) ^ (8 * K) := by rw [hK]
  rw [h6]
  exact h5

/-- Step 4 of the proof of `exists_computable_family_problemK_quad_ge_exists`:
the counting (Chernoff-type) bound for one family and each orientation.  For a family `G` of
pairs of partial functions on `n`-bit vectors with `|G| 2^L < 2^(2n)` the number of tables
`Qn` serving at least `2^(3n)/8` triples is at most `175^K / (2^L)^K` of all `(2^n)^(2^(3n))`
tables, `K = 2^(3n-3)`.  Proof: a bad table serves a set `A` of exactly `K` triples; for fixed `A`
the number of tables serving all of `A` is at most `m^(m^3 - K) · ∏_{t ∈ A} d_t`, where `d_t`
(`t = (a,b,e)`) is the number of pairs `(f,g) ∈ G` with `f a = some e` (the value `Qn t` must be
one of the `g b`); by AM–GM `∏_{t∈A} d_t ≤ (∑_{t∈A} d_t / K)^K ≤ (8 |G| / m)^K` because
`∑_{t} d_t ≤ |G| m^2`; there are `C(m^3, K) ≤ (8e)^K` choices of `A`; hence
`bad / total ≤ (64 e |G| / m^2)^K ≤ (64 e / 2^L)^K ≤ (175 / 2^L)^K`.  The three orientations are
the same count after permuting the arguments of `Qn`. -/
private theorem exists_computable_family_problemK_quad_ge_count
    (n L : ℕ) (hn : 3 ≤ n)
    (G : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n))
    (hG : G.card * 2 ^ L < 2 ^ (2 * n)) :
    {Q : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n |
      2 ^ (3 * n) ≤ 8 * (exists_computable_family_problemK_quad_ge_exists_servedAbs n Q G
        (fun t => t.1) (fun t => t.2.2) (fun t => t.2.1)).ncard}.ncard *
        (2 ^ L) ^ (2 ^ (3 * n - 3)) ≤ 175 ^ (2 ^ (3 * n - 3)) * (2 ^ n) ^ (2 ^ (3 * n)) ∧
    {Q : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n |
      2 ^ (3 * n) ≤ 8 * (exists_computable_family_problemK_quad_ge_exists_servedAbs n Q G
        (fun t => t.2.2) (fun t => t.2.1) (fun t => t.1)).ncard}.ncard *
        (2 ^ L) ^ (2 ^ (3 * n - 3)) ≤ 175 ^ (2 ^ (3 * n - 3)) * (2 ^ n) ^ (2 ^ (3 * n)) ∧
    {Q : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n |
      2 ^ (3 * n) ≤ 8 * (exists_computable_family_problemK_quad_ge_exists_servedAbs n Q G
        (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2)).ncard}.ncard *
        (2 ^ L) ^ (2 ^ (3 * n - 3)) ≤ 175 ^ (2 ^ (3 * n - 3)) * (2 ^ n) ^ (2 ^ (3 * n)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine exists_computable_family_problemK_quad_ge_oriented
      n L hn G hG _ _ _ ?_
    rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
    simp only [Prod.mk.injEq] at h
    simp_all
  · refine exists_computable_family_problemK_quad_ge_oriented
      n L hn G hG _ _ _ ?_
    rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
    simp only [Prod.mk.injEq] at h
    simp_all
  · refine exists_computable_family_problemK_quad_ge_oriented
      n L hn G hG _ _ _ ?_
    rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
    simp only [Prod.mk.injEq] at h
    simp_all

/-- Step 5 of the proof of `exists_computable_family_problemK_quad_ge_exists`:
the number of families.  There are at most `(P+1)^B` finite families `G` of pairs of partial
functions on `n`-bit vectors with `|G| 2^L < 2^(2n)`, where `P = ((2^n+1)^(2^n))^2` is the number
of pairs (each partial function `W n → Option (W n)` is one of `(2^n+1)^(2^n)`) and
`B = 2^(2n) / 2^L` is the largest allowed size (a family of at most `B` pairs is the image of a map
`Fin B → Option (pair)`, so there are at most `(P+1)^B` of them). -/
private theorem exists_computable_family_problemK_quad_ge_families
    (n L : ℕ) :
    {G : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n) |
      G.card * 2 ^ L < 2 ^ (2 * n)}.ncard ≤
      (((2 ^ n + 1) ^ 2 ^ n) ^ 2 + 1) ^ (2 ^ (2 * n) / 2 ^ L) := by
  classical
  set B := 2 ^ (2 * n) / 2 ^ L with hB
  let φ : (Fin B → Option (exists_computable_family_problemK_quad_ge_exists_Pair n)) →
      Finset (exists_computable_family_problemK_quad_ge_exists_Pair n) :=
    fun f => (Finset.univ.image f).eraseNone
  have hcard : Fintype.card (Fin B → Option
      (exists_computable_family_problemK_quad_ge_exists_Pair n)) =
      (((2 ^ n + 1) ^ 2 ^ n) ^ 2 + 1) ^ B := by
    simp [Fintype.card_option, sq,
      exists_computable_family_problemK_quad_ge_exists_Pair]
  have hsub : {G : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n) |
      G.card * 2 ^ L < 2 ^ (2 * n)} ⊆ Set.range φ := by
    intro G hG
    have hGB : G.card ≤ B := by
      rw [hB]
      apply (Nat.le_div_iff_mul_le (by positivity)).2
      exact le_of_lt hG
    refine ⟨fun i => G.toList[i.val]?, ?_⟩
    ext a
    simp only [φ, Finset.mem_eraseNone, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      have := List.mem_of_getElem? hi
      simpa using this
    · intro ha
      have hm : a ∈ G.toList := by simpa using ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
      have hlen : G.toList.length = G.card := Finset.length_toList G
      exact ⟨⟨i, by omega⟩, by simp⟩
  calc _ ≤ (Set.range φ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card (Fin B → Option
        (exists_computable_family_problemK_quad_ge_exists_Pair n)) :=
        (Nat.card_coe_set_eq (Set.range φ)).symm.le.trans (Finite.card_range_le φ)
    _ = _ := by rw [Nat.card_eq_fintype_card, hcard]

/-- Step 1 of the proof of `exists_computable_family_problemK_quad_ge_exists`:
the probabilistic existence on finite types.  For some `c` and all large `n` there is a table
`Qn` on triples of `n`-bit vectors with `n`-bit values such that every finite family `G` of pairs
of partial functions on `n`-bit vectors with `|G| 2^{logSlack c n} < 2^{2n}` serves less than
`1/8` of the `2^{3n}` triples, in each of the three orientations.  Book's proof: a uniformly
random table, counting (Chernoff) bound for one family and one orientation, union bound over the
finitely many families of at most `2^{2n-logSlack c n}` pairs and over the three orientations
(identical up to permuting the arguments of `Qn`). -/
private theorem exists_computable_family_problemK_quad_ge_exists_abstract :
    ∃ c N : ℕ, ∀ n ≥ N, ∃ Qn : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n →
      List.Vector Bool n,
      exists_computable_family_problemK_quad_ge_exists_goodAbs c n Qn := by
  classical
  obtain ⟨c, N, h⟩ := exists_computable_family_problemK_quad_ge_arith
  refine ⟨c, N, fun n hn => ?_⟩
  obtain ⟨h3, harith⟩ := h n hn
  by_contra hcon
  push Not at hcon
  set L := logSlack c n with hL
  set K := 2 ^ (3 * n - 3) with hK
  let T := List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n
  let b1 : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n) → Set T :=
    fun G => {Q | 2 ^ (3 * n) ≤ 8 *
               (exists_computable_family_problemK_quad_ge_exists_servedAbs
      n Q G (fun t => t.1) (fun t => t.2.2) (fun t => t.2.1)).ncard}
  let b2 : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n) → Set T :=
    fun G => {Q | 2 ^ (3 * n) ≤ 8 *
               (exists_computable_family_problemK_quad_ge_exists_servedAbs
      n Q G (fun t => t.2.2) (fun t => t.2.1) (fun t => t.1)).ncard}
  let b3 : Finset (exists_computable_family_problemK_quad_ge_exists_Pair n) → Set T :=
    fun G => {Q | 2 ^ (3 * n) ≤ 8 *
               (exists_computable_family_problemK_quad_ge_exists_servedAbs
      n Q G (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2)).ncard}
  let 𝒢 : Set (Finset (exists_computable_family_problemK_quad_ge_exists_Pair n)) :=
    {G | G.card * 2 ^ L < 2 ^ (2 * n)}
  have hcov : ∀ Q : T, ∃ G ∈ 𝒢, Q ∈ b1 G ∨ Q ∈ b2 G ∨ Q ∈ b3 G := by
    intro Q
    by_contra hno
    push Not at hno
    apply hcon Q
    intro G hG
    obtain ⟨n1, n2, n3⟩ := hno G hG
    exact ⟨not_le.1 n1, not_le.1 n2, not_le.1 n3⟩
  have hT : Fintype.card T = (2 ^ n) ^ (2 ^ (3 * n)) := by
    have hV : Fintype.card (List.Vector Bool n) = 2 ^ n := by
      simp [card_vector]
    simp only [T, Fintype.card_fun, hV]
    ring
  have hfin : 𝒢.Finite := Set.toFinite _
  have hpos : 0 < (2 ^ n) ^ (2 ^ (3 * n)) := by positivity
  let fb : Set T → Finset T := fun s => (Set.toFinite s).toFinset
  have hcard1 : ∀ s : Set T, s.ncard = (fb s).card :=
    fun s => Set.ncard_eq_toFinset_card s (Set.toFinite s)
  have hmem : ∀ (s : Set T) (Q : T), Q ∈ fb s ↔ Q ∈ s := fun s Q => Set.Finite.mem_toFinset _
  have hsum : (2 ^ n) ^ (2 ^ (3 * n)) ≤
      ∑ G ∈ hfin.toFinset, ((b1 G).ncard + (b2 G).ncard + (b3 G).ncard) := by
    rw [← hT]
    calc Fintype.card T = (Finset.univ : Finset T).card := rfl
      _ ≤ (hfin.toFinset.biUnion
          (fun G => fb (b1 G) ∪ fb (b2 G) ∪ fb (b3 G))).card := by
        apply Finset.card_le_card
        intro Q _
        obtain ⟨G, hG, hQ⟩ := hcov Q
        simp only [Finset.mem_biUnion, Finset.mem_union, hmem, Set.Finite.mem_toFinset]
        exact ⟨G, hG, hQ.elim (fun h => Or.inl (Or.inl h))
          (fun h => h.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr h))⟩
      _ ≤ ∑ G ∈ hfin.toFinset,
          (fb (b1 G) ∪ fb (b2 G) ∪ fb (b3 G)).card := Finset.card_biUnion_le
      _ ≤ ∑ G ∈ hfin.toFinset, ((b1 G).ncard + (b2 G).ncard + (b3 G).ncard) := by
        apply Finset.sum_le_sum
        intro G _
        have u1 := Finset.card_union_le (fb (b1 G)) (fb (b2 G))
        have u2 := Finset.card_union_le (fb (b1 G) ∪ fb (b2 G)) (fb (b3 G))
        have e1 := hcard1 (b1 G)
        have e2 := hcard1 (b2 G)
        have e3 := hcard1 (b3 G)
        omega
  have hterm : ∀ G ∈ hfin.toFinset,
      ((b1 G).ncard + (b2 G).ncard + (b3 G).ncard) * (2 ^ L) ^ K ≤
        3 * (175 ^ K * (2 ^ n) ^ (2 ^ (3 * n))) := by
    intro G hG
    have hG' : G.card * 2 ^ L < 2 ^ (2 * n) := hfin.mem_toFinset.1 hG
    obtain ⟨k1, k2, k3⟩ :=
      exists_computable_family_problemK_quad_ge_count n L h3 G hG'
    have k1' : (b1 G).ncard * (2 ^ L) ^ K ≤ 175 ^ K * (2 ^ n) ^ (2 ^ (3 * n)) := k1
    have k2' : (b2 G).ncard * (2 ^ L) ^ K ≤ 175 ^ K * (2 ^ n) ^ (2 ^ (3 * n)) := k2
    have k3' : (b3 G).ncard * (2 ^ L) ^ K ≤ 175 ^ K * (2 ^ n) ^ (2 ^ (3 * n)) := k3
    rw [add_mul, add_mul]
    linarith
  have hG𝒢 : hfin.toFinset.card ≤
      (((2 ^ n + 1) ^ 2 ^ n) ^ 2 + 1) ^ (2 ^ (2 * n) / 2 ^ L) := by
    rw [← Set.ncard_eq_toFinset_card 𝒢 hfin]
    exact exists_computable_family_problemK_quad_ge_families n L
  have h1 : (2 ^ n) ^ (2 ^ (3 * n)) * (2 ^ L) ^ K ≤
      hfin.toFinset.card * (3 * (175 ^ K * (2 ^ n) ^ (2 ^ (3 * n)))) := by
    calc _ ≤ (∑ G ∈ hfin.toFinset, ((b1 G).ncard + (b2 G).ncard + (b3 G).ncard)) * (2 ^ L) ^ K :=
          Nat.mul_le_mul_right _ hsum
      _ = ∑ G ∈ hfin.toFinset, ((b1 G).ncard + (b2 G).ncard + (b3 G).ncard) * (2 ^ L) ^ K :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ G ∈ hfin.toFinset, 3 * (175 ^ K * (2 ^ n) ^ (2 ^ (3 * n))) :=
          Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  have h2 : hfin.toFinset.card * (3 * (175 ^ K * (2 ^ n) ^ (2 ^ (3 * n)))) ≤
      ((((2 ^ n + 1) ^ 2 ^ n) ^ 2 + 1) ^ (2 ^ (2 * n) / 2 ^ L) * 3 * 175 ^ K) *
        (2 ^ n) ^ (2 ^ (3 * n)) := by
    calc _ ≤ (((2 ^ n + 1) ^ 2 ^ n) ^ 2 + 1) ^ (2 ^ (2 * n) / 2 ^ L) *
          (3 * (175 ^ K * (2 ^ n) ^ (2 ^ (3 * n)))) := Nat.mul_le_mul_right _ hG𝒢
      _ = _ := by ring
  have h3' := Nat.mul_lt_mul_of_pos_right harith hpos
  rw [mul_comm ((2 ^ L) ^ K) _] at h3'
  exact lt_irrefl _ (lt_of_le_of_lt (h1.trans h2) h3')

/-- Step 2 of the proof of `exists_computable_family_problemK_quad_ge_exists`:
transport from `n`-bit vectors to bit strings.  A good abstract table `Q` gives the table
`Qn a b e := Q a b e` on `n`-bit words (and `[]` elsewhere), which is good in the sense of
`exists_computable_family_problemK_quad_ge_good`: a finite family `F` of pairs of functions on all
words is restricted to `n`-bit words (a value which is not an `n`-bit word becomes `none`), giving
a family `G` with `|G| ≤ |F|` whose abstract served sets contain (via `List.Vector.toList`) the
served sets of `F`. -/
private theorem exists_computable_family_problemK_quad_ge_transport
    (c n : ℕ)
    (Q : List.Vector Bool n → List.Vector Bool n → List.Vector Bool n → List.Vector Bool n)
    (hQ : exists_computable_family_problemK_quad_ge_exists_goodAbs c n Q) :
    ∃ Qn : BitString → BitString → BitString → BitString,
      (∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
        (Qn a b e).length = n) ∧
      exists_computable_family_problemK_quad_ge_good c n Qn := by
  classical
  let Qn : BitString → BitString → BitString → BitString := fun a b e =>
    if h : a.length = n ∧ b.length = n ∧ e.length = n then
      (Q ⟨a, h.1⟩ ⟨b, h.2.1⟩ ⟨e, h.2.2⟩).toList else []
  refine ⟨Qn, ?_, ?_⟩
  · intro a b e ha hb he
    have h : a.length = n ∧ b.length = n ∧ e.length = n := ⟨ha, hb, he⟩
    simp only [Qn, dite_eq_left h]
    exact List.Vector.toList_length _
  · intro F hF hcard
    let r : ((BitString → BitString) × (BitString → BitString)) →
        exists_computable_family_problemK_quad_ge_exists_Pair n := fun fg =>
      (fun a => if h : (fg.1 a.toList).length = n then some ⟨fg.1 a.toList, h⟩ else none,
       fun a => if h : (fg.2 a.toList).length = n then some ⟨fg.2 a.toList, h⟩ else none)
    let G := hF.toFinset.image r
    have hGcard : G.card ≤ F.ncard := by
      calc G.card ≤ hF.toFinset.card := Finset.card_image_le
        _ = F.ncard := (Set.ncard_eq_toFinset_card F hF).symm
    have hGlt : G.card * 2 ^ logSlack c n < 2 ^ (2 * n) :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hGcard) hcard
    have key : ∀ (uB vB wB : BitString × BitString × BitString → BitString)
        (uA vA wA : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n →
          List.Vector Bool n),
        (∀ t : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n,
          uB (t.1.toList, t.2.1.toList, t.2.2.toList) = (uA t).toList) →
        (∀ t : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n,
          vB (t.1.toList, t.2.1.toList, t.2.2.toList) = (vA t).toList) →
        (∀ t : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n,
          wB (t.1.toList, t.2.1.toList, t.2.2.toList) = (wA t).toList) →
        (exists_computable_family_problemK_quad_ge_served n Qn F uB vB wB).ncard ≤
          (exists_computable_family_problemK_quad_ge_exists_servedAbs n Q G uA vA wA).ncard :=
              by
      intro uB vB wB uA vA wA hu hv hw
      have hsub : exists_computable_family_problemK_quad_ge_served n Qn F uB vB wB ⊆
          (fun t : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n =>
            (t.1.toList, t.2.1.toList, t.2.2.toList)) ''
            (exists_computable_family_problemK_quad_ge_exists_servedAbs n Q G uA vA wA) := by
        rintro t ⟨h1, h2, h3, fg, hfg, e1, e2⟩
        let t' : List.Vector Bool n × List.Vector Bool n × List.Vector Bool n :=
          (⟨t.1, h1⟩, ⟨t.2.1, h2⟩, ⟨t.2.2, h3⟩)
        have e1' : fg.1 (uA t').toList = (vA t').toList := by
          rw [← hu t', ← hv t']; exact e1
        have e2' : fg.2 (wA t').toList = (Q t'.1 t'.2.1 t'.2.2).toList := by
          rw [← hw t']
          refine e2.trans ?_
          have h : t.1.length = n ∧ t.2.1.length = n ∧ t.2.2.length = n := ⟨h1, h2, h3⟩
          simp only [Qn, dite_eq_left h]
          rfl
        refine ⟨t', ⟨r fg, Finset.mem_image.2 ⟨fg, hF.mem_toFinset.2 hfg, rfl⟩, ?_, ?_⟩, rfl⟩
        · have hl : (fg.1 (uA t').toList).length = n := by
            rw [e1']; exact List.Vector.toList_length _
          simp only [r]
          rw [dite_eq_left hl]
          exact congrArg some (Subtype.ext e1')
        · have hl : (fg.2 (wA t').toList).length = n := by
            rw [e2']; exact List.Vector.toList_length _
          simp only [r]
          rw [dite_eq_left hl]
          exact congrArg some (Subtype.ext e2')
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))
    obtain ⟨g1, g2, g3⟩ := hQ G hGlt
    refine ⟨?_, ?_, ?_⟩
    · exact lt_of_le_of_lt (Nat.mul_le_mul_left 8 (key _ _ _ _ _ _
        (fun t => rfl) (fun t => rfl) (fun t => rfl))) g1
    · exact lt_of_le_of_lt (Nat.mul_le_mul_left 8 (key _ _ _ _ _ _
        (fun t => rfl) (fun t => rfl) (fun t => rfl))) g2
    · exact lt_of_le_of_lt (Nat.mul_le_mul_left 8 (key _ _ _ _ _ _
        (fun t => rfl) (fun t => rfl) (fun t => rfl))) g3

/-- Step 1 of the proof of `exists_computable_family_problemK_quad_ge`: the
probabilistic existence (pure finite combinatorics, no complexity theory).  For some `c` and all
large `n` there is `Qn` on triples of `n`-bit words with `n`-bit values such that every family of
fewer than `2 ^ (2n − logSlack c n)` pairs of functions serves less than `1/8` of the triples,
in each of the three orientations.  Book's proof: a random `Qn` (each value uniform and
independent); for a fixed family `F` the number of served triples is a sum of independent
indicators (one per candidate triple `(a, b, f a)`) with mean at most `|F| 2ⁿ ≤ 2^{3n − logSlack}`;
Chernoff gives probability `≤ 2^{-Ω(2^{3n} · logSlack)}` of serving `≥ 1/8` of all triples, and
the number of families (restricted to `n`-bit words) is at most `2^{2n 2^n |F|}`, smaller for
`c ≥ 2` and `n` large; the three orientations are the same event after permuting the arguments of
`Qn`, so a union bound over the three leaves a positive probability. -/
private theorem exists_computable_family_problemK_quad_ge_exists :
    ∃ c N : ℕ, ∀ n ≥ N, ∃ Qn : BitString → BitString → BitString → BitString,
      (∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
        (Qn a b e).length = n) ∧
      exists_computable_family_problemK_quad_ge_good c n Qn := by
  obtain ⟨c, N, h⟩ := exists_computable_family_problemK_quad_ge_exists_abstract
  refine ⟨c, N, fun n hn => ?_⟩
  obtain ⟨Q, hQ⟩ := h n hn
  exact exists_computable_family_problemK_quad_ge_transport c n Q hQ

/-- Locality of goodness: `good c n Qn` depends only on the values of `Qn` on triples of
`n`-bit words. -/
private lemma exists_computable_family_problemK_quad_ge_search_good_congr (c n : ℕ)
    (Qn Qn' : BitString → BitString → BitString → BitString)
    (hQ : ∀ a b e : BitString, a.length = n → b.length = n → e.length = n → Qn a b e = Qn' a b e)
    (h : exists_computable_family_problemK_quad_ge_good c n Qn) :
    exists_computable_family_problemK_quad_ge_good c n Qn' := by
  have hs : ∀ (F : Set ((BitString → BitString) × (BitString → BitString)))
      (u v w : BitString × BitString × BitString → BitString),
      exists_computable_family_problemK_quad_ge_served n Qn' F u v w =
        exists_computable_family_problemK_quad_ge_served n Qn F u v w := by
    intro F u v w
    ext t
    simp only [exists_computable_family_problemK_quad_ge_served, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3, fg, hfg, e1, e2⟩
      exact ⟨h1, h2, h3, fg, hfg, e1, by rw [e2, hQ _ _ _ h1 h2 h3]⟩
    · rintro ⟨h1, h2, h3, fg, hfg, e1, e2⟩
      exact ⟨h1, h2, h3, fg, hfg, e1, by rw [e2, hQ _ _ _ h1 h2 h3]⟩
  intro F hF hc
  obtain ⟨h1, h2, h3⟩ := h F hF hc
  rw [hs, hs, hs]
  exact ⟨h1, h2, h3⟩

/-- Step 1 of the proof of `exists_computable_family_problemK_quad_ge_search`:
a computable enumeration of function tables.  There is a computable `T n k` (the `k`-th table for
parameter `n`, a function of three words) such that every function `Qn` with `n`-bit values on
triples of `n`-bit words agrees on all triples of `n`-bit words with `T n k` for some `k`.
(For instance `k` decodes to a list of quadruples `(a, b, e, d)`, and `T n k a b e` is the `d` of
the first quadruple of the list starting with `(a, b, e)`, and `[]` if there is none; the list
`[((a, b, e), Qn a b e)]` over the finitely many `n`-bit triples is coded by some `k`.) -/
private theorem exists_computable_family_problemK_quad_ge_enum :
    ∃ T : ℕ → ℕ → BitString → BitString → BitString → BitString,
      Computable (fun x : ℕ × ℕ × BitString × BitString × BitString =>
        T x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∧
      ∀ (n : ℕ) (Qn : BitString → BitString → BitString → BitString),
        (∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
          (Qn a b e).length = n) →
        ∃ k : ℕ, ∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
          T n k a b e = Qn a b e := by
  classical
  let step : BitString → BitString → BitString → BitString →
      BitString × BitString × BitString × BitString → BitString :=
    fun a b e s q => cond (decide (q.1 = a) && decide (q.2.1 = b) && decide (q.2.2.1 = e))
      q.2.2.2 s
  let T : ℕ → ℕ → BitString → BitString → BitString → BitString := fun _ k a b e =>
    ((Encodable.decode (α := List (BitString × BitString × BitString × BitString)) k).getD []).foldl
      (step a b e) []
  have hnomatch : ∀ (a b e : BitString) (l : List (BitString × BitString × BitString × BitString))
      (acc : BitString), (∀ q ∈ l, ¬ (q.1 = a ∧ q.2.1 = b ∧ q.2.2.1 = e)) →
      l.foldl (step a b e) acc = acc := by
    intro a b e l
    induction l with
    | nil => intro acc _; rfl
    | cons q l ih =>
      intro acc hl
      have hq := hl q (List.mem_cons_self)
      simp only [List.foldl_cons, step]
      have : (decide (q.1 = a) && decide (q.2.1 = b) && decide (q.2.2.1 = e)) = false := by
        by_contra hcon
        simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hcon
        exact hq ⟨hcon.1.1, hcon.1.2, hcon.2⟩
      rw [this]
      exact ih acc fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')
  have hmatch : ∀ (a b e v : BitString) (l : List (BitString × BitString × BitString × BitString))
      (acc : BitString), (∀ q ∈ l, (q.1 = a ∧ q.2.1 = b ∧ q.2.2.1 = e) → q.2.2.2 = v) →
      (∃ q ∈ l, q.1 = a ∧ q.2.1 = b ∧ q.2.2.1 = e) → l.foldl (step a b e) acc = v := by
    intro a b e v l
    induction l with
    | nil => intro acc _ hex; obtain ⟨q, hq, _⟩ := hex; simp at hq
    | cons q l ih =>
      intro acc hl hex
      simp only [List.foldl_cons]
      by_cases ht : ∃ q' ∈ l, q'.1 = a ∧ q'.2.1 = b ∧ q'.2.2.1 = e
      · exact ih _ (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')) ht
      · have hqm : q.1 = a ∧ q.2.1 = b ∧ q.2.2.1 = e := by
          obtain ⟨q', hq', hm⟩ := hex
          rcases List.mem_cons.1 hq' with rfl | hq'
          · exact hm
          · exact absurd ⟨q', hq', hm⟩ ht
        have h1 : step a b e acc q = q.2.2.2 := by
          simp [step, hqm.1, hqm.2.1, hqm.2.2]
        rw [h1, hnomatch a b e l _ (fun q' hq' hm => ht ⟨q', hq', hm⟩)]
        exact hl q List.mem_cons_self hqm
  refine ⟨T, ?_, ?_⟩
  · refine Primrec.to_comp ?_
    have hf : Primrec (fun x : ℕ × ℕ × BitString × BitString × BitString =>
        (Encodable.decode (α := List (BitString × BitString × BitString × BitString))
          x.2.1).getD []) :=
      Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const [])
    have pa : Primrec (fun p : (ℕ × ℕ × BitString × BitString × BitString) ×
        (BitString × BitString × BitString × BitString × BitString) => p.1.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have pb : Primrec (fun p : (ℕ × ℕ × BitString × BitString × BitString) ×
        (BitString × BitString × BitString × BitString × BitString) => p.1.2.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    have pe : Primrec (fun p : (ℕ × ℕ × BitString × BitString × BitString) ×
        (BitString × BitString × BitString × BitString × BitString) => p.1.2.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    have ps : Primrec (fun p : (ℕ × ℕ × BitString × BitString × BitString) ×
        (BitString × BitString × BitString × BitString × BitString) => p.2.1) :=
      Primrec.fst.comp Primrec.snd
    have q1 : Primrec (fun p : (ℕ × ℕ × BitString × BitString × BitString) ×
        (BitString × BitString × BitString × BitString × BitString) => p.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have q2 : Primrec (fun p : (ℕ × ℕ × BitString × BitString × BitString) ×
        (BitString × BitString × BitString × BitString × BitString) => p.2.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have q3 : Primrec (fun p : (ℕ × ℕ × BitString × BitString × BitString) ×
        (BitString × BitString × BitString × BitString × BitString) => p.2.2.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have q4 : Primrec (fun p : (ℕ × ℕ × BitString × BitString × BitString) ×
        (BitString × BitString × BitString × BitString × BitString) => p.2.2.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have hdec : Primrec₂ (fun a b : BitString => decide (a = b)) := Primrec.eq.decide
    have hh : Primrec₂ (fun (x : ℕ × ℕ × BitString × BitString × BitString)
        (sq : BitString × BitString × BitString × BitString × BitString) =>
        step x.2.2.1 x.2.2.2.1 x.2.2.2.2 sq.1 sq.2) :=
      Primrec.cond (Primrec.and.comp (Primrec.and.comp (hdec.comp q1 pa)
        (hdec.comp q2 pb)) (hdec.comp q3 pe)) q4 ps
    exact Primrec.list_foldl hf (Primrec.const ([] : BitString)) hh
  · intro n Qn _
    obtain ⟨hfin, _⟩ := exists_computable_family_problemK_quad_ge_triples_ncard n
    let l : List (BitString × BitString × BitString × BitString) :=
      hfin.toFinset.toList.map fun t => (t.1, t.2.1, t.2.2, Qn t.1 t.2.1 t.2.2)
    refine ⟨Encodable.encode l, fun a b e ha hb he => ?_⟩
    simp only [T, Encodable.encodek, Option.getD_some]
    refine hmatch a b e (Qn a b e) l [] ?_ ?_
    · intro q hq hm
      obtain ⟨t, _, rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h2, h3⟩ := hm
      simp only at h1 h2 h3 ⊢
      rw [h1, h2, h3]
    · refine ⟨(a, b, e, Qn a b e), List.mem_map.2 ⟨(a, b, e), ?_, rfl⟩, rfl, rfl, rfl⟩
      simp [ha, hb, he]

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: the list of
all words of length `n`. -/
private def exists_computable_family_problemK_quad_ge_check_wordsList :
    ℕ → List BitString
  | 0 => [[]]
  | n + 1 =>
    (exists_computable_family_problemK_quad_ge_check_wordsList n).flatMap
      fun w => [false :: w, true :: w]

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: the list of
all triples of words of length `n`. -/
private def exists_computable_family_problemK_quad_ge_check_triplesList
    (n : ℕ) : List (BitString × BitString × BitString) :=
  (exists_computable_family_problemK_quad_ge_check_wordsList n).flatMap
    fun a => (exists_computable_family_problemK_quad_ge_check_wordsList
               n).flatMap
      fun b => (exists_computable_family_problemK_quad_ge_check_wordsList n).map
        fun e => (a, b, e)

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: all lists
of length `≤ j` with entries from `ps`. -/
private def exists_computable_family_problemK_quad_ge_check_rlists
    {P : Type} (ps : List P) : ℕ → List (List P)
  | 0 => [[]]
  | j + 1 => [] :: ps.flatMap fun p =>
    (exists_computable_family_problemK_quad_ge_check_rlists ps j).map (p :: ·)

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: a list of
pairs `(x, y)` read as a partial function (the value of the first entry with key `x`). -/
private def exists_computable_family_problemK_quad_ge_check_ev
    (l : List (BitString × BitString)) (x : BitString) : Option BitString :=
  l.foldr (fun p acc => if p.1 = x then some p.2 else acc) none

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: the
restriction of `f` to the `n`-bit words with `n`-bit values, as a list of pairs. -/
private def exists_computable_family_problemK_quad_ge_check_restr (n : ℕ)
    (f : BitString → BitString) : List (BitString × BitString) :=
  (exists_computable_family_problemK_quad_ge_check_wordsList n).filterMap
    fun x => if (f x).length = n then some (x, f x) else none

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: a total
function extending the partial function given by a list of pairs. -/
private def exists_computable_family_problemK_quad_ge_check_lift
    (l : List (BitString × BitString)) (x : BitString) : BitString :=
  (exists_computable_family_problemK_quad_ge_check_ev l x).getD []

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: all pairs of
`n`-bit words. -/
private def exists_computable_family_problemK_quad_ge_check_pairsW (n : ℕ) :
    List (BitString × BitString) :=
  (exists_computable_family_problemK_quad_ge_check_wordsList n).flatMap
    fun x => (exists_computable_family_problemK_quad_ge_check_wordsList n).map
      fun y => (x, y)

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: the lists of
at most `2^n` pairs of `n`-bit words (they include all restrictions of functions). -/
private def exists_computable_family_problemK_quad_ge_check_graphs (n : ℕ) :
    List (List (BitString × BitString)) :=
  exists_computable_family_problemK_quad_ge_check_rlists
    (exists_computable_family_problemK_quad_ge_check_pairsW n)
    (exists_computable_family_problemK_quad_ge_check_wordsList n).length

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: the pairs of
elements of `..._graphs n`. -/
private def exists_computable_family_problemK_quad_ge_check_ps (n : ℕ) :
    List (List (BitString × BitString) × List (BitString × BitString)) :=
  (exists_computable_family_problemK_quad_ge_check_graphs n).flatMap
    fun f => (exists_computable_family_problemK_quad_ge_check_graphs n).map
      fun g => (f, g)

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: the
candidate families, lists of at most `2^(2n)` elements of `..._ps n`. -/
private def exists_computable_family_problemK_quad_ge_check_fams (n : ℕ) :
    List (List (List (BitString × BitString) × List (BitString × BitString))) :=
  exists_computable_family_problemK_quad_ge_check_rlists
    (exists_computable_family_problemK_quad_ge_check_ps n) (2 ^ (2 * n))

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: the number
of entries `(t, d)` of `data` served by the family `R` in the orientation `(u, v, w)`. -/
private def exists_computable_family_problemK_quad_ge_check_cnt
    (R : List (List (BitString × BitString) × List (BitString × BitString)))
    (u v w : BitString × BitString × BitString → BitString)
    (data : List ((BitString × BitString × BitString) × BitString)) : ℕ :=
  (data.filter fun q => R.any fun fg =>
    decide (exists_computable_family_problemK_quad_ge_check_ev fg.1 (u q.1) =
      some (v q.1)) &&
    decide (exists_computable_family_problemK_quad_ge_check_ev fg.2 (w q.1) =
      some q.2)).length

/-- Auxiliary for `exists_computable_family_problemK_quad_ge_check`: the finite
check on the list `data` of the pairs (triple, value of the table): all values are `n`-bit words,
and every candidate family `R` of restricted pairs with `|R| 2^(logSlack c n) < 2^(2n)` serves
less than `1/8` of the entries in each of the three orientations. -/
private def exists_computable_family_problemK_quad_ge_check_chk0 (c n : ℕ)
    (data : List ((BitString × BitString × BitString) × BitString)) : Bool :=
  (data.all fun q => decide (q.2.length = n)) &&
  (exists_computable_family_problemK_quad_ge_check_fams n).all fun R =>
    decide (2 ^ (2 * n) ≤ R.length * 2 ^ logSlack c n) ||
    (decide (8 * exists_computable_family_problemK_quad_ge_check_cnt R
        (fun t => t.1) (fun t => t.2.2) (fun t => t.2.1) data < 2 ^ (3 * n)) &&
     decide (8 * exists_computable_family_problemK_quad_ge_check_cnt R
        (fun t => t.2.2) (fun t => t.2.1) (fun t => t.1) data < 2 ^ (3 * n)) &&
     decide (8 * exists_computable_family_problemK_quad_ge_check_cnt R
        (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2) data < 2 ^ (3 * n)))

/-- Auxiliary: `..._wordsList n` lists exactly the words of length `n`, without repetition. -/
private theorem exists_computable_family_problemK_quad_ge_check_wordsList_spec
    (n : ℕ) :
    (exists_computable_family_problemK_quad_ge_check_wordsList n).Nodup ∧
    ∀ w : BitString,
      w ∈ exists_computable_family_problemK_quad_ge_check_wordsList n ↔
        w.length = n := by
  induction n with
  | zero =>
    refine ⟨by simp [exists_computable_family_problemK_quad_ge_check_wordsList],
      fun w => ?_⟩
    simp [exists_computable_family_problemK_quad_ge_check_wordsList]
  | succ n ih =>
    obtain ⟨hnd, hmem⟩ := ih
    refine ⟨?_, fun w => ?_⟩
    · unfold exists_computable_family_problemK_quad_ge_check_wordsList
      rw [List.nodup_flatMap]
      refine ⟨fun w _ => by simp, ?_⟩
      refine hnd.imp ?_
      intro a b hab
      simp only [Function.onFun, List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl) (h | h) <;> simp_all
    · unfold exists_computable_family_problemK_quad_ge_check_wordsList
      rw [List.mem_flatMap]
      constructor
      · rintro ⟨v, hv, hw⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> simp [(hmem v).1 hv]
      · intro hw
        cases w with
        | nil => simp at hw
        | cons x v =>
          refine ⟨v, (hmem v).2 (by simpa using hw), ?_⟩
          cases x <;> simp

/-- Auxiliary: `..._triplesList n` lists exactly the triples of `n`-bit words, without
repetition. -/
private theorem exists_computable_family_problemK_quad_ge_check_triples_spec
    (n : ℕ) :
    (exists_computable_family_problemK_quad_ge_check_triplesList n).Nodup ∧
    ∀ t : BitString × BitString × BitString,
      t ∈ exists_computable_family_problemK_quad_ge_check_triplesList n ↔
        (t.1.length = n ∧ t.2.1.length = n ∧ t.2.2.length = n) := by
  obtain ⟨hnd, hmem⟩ :=
    exists_computable_family_problemK_quad_ge_check_wordsList_spec n
  unfold exists_computable_family_problemK_quad_ge_check_triplesList
  refine ⟨?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun a _ => ?_, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun b _ => hnd.map (fun x y h => by simpa using h), ?_⟩
      refine hnd.imp ?_
      intro b b' hbb'
      simp only [Function.onFun, List.disjoint_left, List.mem_map]
      rintro x ⟨e, _, rfl⟩ ⟨e', _, h⟩
      simp_all
    · refine hnd.imp ?_
      intro a a' haa'
      simp only [Function.onFun, List.disjoint_left, List.mem_flatMap, List.mem_map]
      rintro x ⟨b, _, e, _, rfl⟩ ⟨b', _, e', _, h⟩
      simp_all
  · rintro ⟨a, b, e⟩
    simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq, hmem]
    constructor
    · rintro ⟨a', ha, b', hb, e', he, rfl, rfl, rfl⟩
      exact ⟨ha, hb, he⟩
    · rintro ⟨ha, hb, he⟩
      exact ⟨a, ha, b, hb, e, he, rfl, rfl, rfl⟩

/-- Auxiliary: membership in `..._rlists ps j`. -/
private theorem exists_computable_family_problemK_quad_ge_check_rlists_spec
    {P : Type} (ps : List P) (j : ℕ) (l : List P) :
    l ∈ exists_computable_family_problemK_quad_ge_check_rlists ps j ↔
      (∀ x ∈ l, x ∈ ps) ∧ l.length ≤ j := by
  induction j generalizing l with
  | zero =>
    simp only [exists_computable_family_problemK_quad_ge_check_rlists,
      List.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]
    constructor
    · rintro rfl; simp
    · rintro ⟨_, rfl⟩; rfl
  | succ j ih =>
    simp only [exists_computable_family_problemK_quad_ge_check_rlists,
      List.mem_cons, List.mem_flatMap, List.mem_map]
    cases l with
    | nil => simp
    | cons x l =>
      simp only [reduceCtorEq, false_or, List.cons.injEq, List.mem_cons, forall_eq_or_imp,
        List.length_cons, Nat.add_le_add_iff_right]
      constructor
      · rintro ⟨p, hp, l', hl', rfl, rfl⟩
        exact ⟨⟨hp, ((ih l').1 hl').1⟩, ((ih l').1 hl').2⟩
      · rintro ⟨⟨hx, hl⟩, hlen⟩
        exact ⟨x, hx, l, (ih l).2 ⟨hl, hlen⟩, rfl, rfl⟩

/-- Auxiliary: one step of `..._ev`. -/
private theorem exists_computable_family_problemK_quad_ge_check_ev_cons
    (p : BitString × BitString) (l : List (BitString × BitString)) (x : BitString) :
    exists_computable_family_problemK_quad_ge_check_ev (p :: l) x =
      if p.1 = x then some p.2 else
        exists_computable_family_problemK_quad_ge_check_ev l x := rfl

/-- Auxiliary: on the graph of a function `f`, `..._ev` evaluates `f`. -/
private theorem exists_computable_family_problemK_quad_ge_check_ev_graph
    (f : BitString → BitString) (l : List (BitString × BitString)) (x : BitString)
    (hl : ∀ p ∈ l, p.2 = f p.1) (hx : (x, f x) ∈ l) :
    exists_computable_family_problemK_quad_ge_check_ev l x = some (f x) := by
  induction l with
  | nil => simp at hx
  | cons p l ih =>
    rw [exists_computable_family_problemK_quad_ge_check_ev_cons]
    split_ifs with h
    · rw [hl p List.mem_cons_self, h]
    · refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) ?_
      rcases List.mem_cons.1 hx with hx | hx
      · exact absurd (by rw [← hx]) h
      · exact hx

/-- Auxiliary: membership in `..._restr n f`. -/
private theorem exists_computable_family_problemK_quad_ge_check_mem_restr
    (n : ℕ) (f : BitString → BitString) (p : BitString × BitString) :
    p ∈ exists_computable_family_problemK_quad_ge_check_restr n f ↔
      p.1.length = n ∧ (f p.1).length = n ∧ p.2 = f p.1 := by
  have hW := (exists_computable_family_problemK_quad_ge_check_wordsList_spec
    n).2
  unfold exists_computable_family_problemK_quad_ge_check_restr
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hp⟩
    split_ifs at hp with h
    simp only [Option.some.injEq] at hp
    subst hp
    exact ⟨(hW x).1 hx, h, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p.1, (hW _).2 h1, ?_⟩
    rw [ite_eq_left h2]
    exact congrArg some (Prod.ext rfl h3.symm)

/-- Auxiliary: `..._ev` of a restriction. -/
private theorem exists_computable_family_problemK_quad_ge_check_ev_restr
    (n : ℕ) (f : BitString → BitString) (x : BitString) (hx : x.length = n)
    (hfx : (f x).length = n) :
    exists_computable_family_problemK_quad_ge_check_ev
      (exists_computable_family_problemK_quad_ge_check_restr n f) x =
        some (f x) :=
  exists_computable_family_problemK_quad_ge_check_ev_graph f _ x
    (fun p hp =>
      ((exists_computable_family_problemK_quad_ge_check_mem_restr n f p).1
        hp).2.2)
    ((exists_computable_family_problemK_quad_ge_check_mem_restr n f
      (x, f x)).2 ⟨hx, hfx, rfl⟩)

/-- Auxiliary: restrictions belong to `..._graphs n`. -/
private theorem exists_computable_family_problemK_quad_ge_check_restr_mem
    (n : ℕ) (f : BitString → BitString) :
    exists_computable_family_problemK_quad_ge_check_restr n f ∈
      exists_computable_family_problemK_quad_ge_check_graphs n := by
  have hW := (exists_computable_family_problemK_quad_ge_check_wordsList_spec
    n).2
  unfold exists_computable_family_problemK_quad_ge_check_graphs
  rw [exists_computable_family_problemK_quad_ge_check_rlists_spec]
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ :=
      (exists_computable_family_problemK_quad_ge_check_mem_restr n f p).1 hp
    unfold exists_computable_family_problemK_quad_ge_check_pairsW
    rw [List.mem_flatMap]
    refine ⟨p.1, (hW _).2 h1, List.mem_map.2 ⟨p.2, (hW _).2 (by rw [h3]; exact h2), rfl⟩⟩
  · unfold exists_computable_family_problemK_quad_ge_check_restr
    exact List.length_filterMap_le _ _

/-- Auxiliary: membership in `..._ps n`. -/
private theorem exists_computable_family_problemK_quad_ge_check_mem_ps
    (n : ℕ) (p : List (BitString × BitString) × List (BitString × BitString)) :
    p ∈ exists_computable_family_problemK_quad_ge_check_ps n ↔
      p.1 ∈ exists_computable_family_problemK_quad_ge_check_graphs n ∧
      p.2 ∈ exists_computable_family_problemK_quad_ge_check_graphs n := by
  unfold exists_computable_family_problemK_quad_ge_check_ps
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨f, hf, hp⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hp
    exact ⟨hf, hg⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p.1, h1, List.mem_map.2 ⟨p.2, h2, rfl⟩⟩

/-- Auxiliary: the length of a filtered list without repetition is the cardinality of the
corresponding set. -/
private theorem exists_computable_family_problemK_quad_ge_check_filter_length
    {α : Type} (L : List α) (hL : L.Nodup) (p : α → Bool) :
    (L.filter p).length = {t | t ∈ L ∧ p t = true}.ncard := by
  classical
  have h1 : {t | t ∈ L ∧ p t = true} = ((L.filter p).toFinset : Set α) := by
    ext t; simp
  rw [h1, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hL.filter p)]

/-- Auxiliary: the elements of a list form a set of cardinality at most its length. -/
private theorem exists_computable_family_problemK_quad_ge_check_ncard_le
    {α : Type} (R : List α) : {p | p ∈ R}.ncard ≤ R.length := by
  classical
  have h1 : {p | p ∈ R} = (R.toFinset : Set α) := by ext; simp
  rw [h1, Set.ncard_coe_finset]
  exact List.toFinset_card_le R

/-- Auxiliary: `..._cnt` on the table of `Q` is the cardinality of a set of triples. -/
private theorem exists_computable_family_problemK_quad_ge_check_cnt_eq
    (n : ℕ) (Q : BitString → BitString → BitString → BitString)
    (R : List (List (BitString × BitString) × List (BitString × BitString)))
    (u v w : BitString × BitString × BitString → BitString) :
    exists_computable_family_problemK_quad_ge_check_cnt R u v w
      ((exists_computable_family_problemK_quad_ge_check_triplesList n).map
        fun t => (t, Q t.1 t.2.1 t.2.2)) =
      {t | t ∈ exists_computable_family_problemK_quad_ge_check_triplesList n ∧
        ∃ p ∈ R, exists_computable_family_problemK_quad_ge_check_ev p.1 (u t) =
          some (v t) ∧
          exists_computable_family_problemK_quad_ge_check_ev p.2 (w t) =
          some (Q t.1 t.2.1 t.2.2)}.ncard := by
  unfold exists_computable_family_problemK_quad_ge_check_cnt
  rw [List.filter_map, List.length_map,
    exists_computable_family_problemK_quad_ge_check_filter_length _
      (exists_computable_family_problemK_quad_ge_check_triples_spec n).1]
  congr 1
  ext t
  simp [List.any_eq_true]

/-- Auxiliary (restriction): the triples served by a finite family `F` are served by the list of
restrictions of its pairs. -/
private theorem exists_computable_family_problemK_quad_ge_check_sub_restr
    (n : ℕ) (Q : BitString → BitString → BitString → BitString)
    (hQ : ∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
      (Q a b e).length = n)
    (F : Set ((BitString → BitString) × (BitString → BitString))) (hF : F.Finite)
    (u v w : BitString × BitString × BitString → BitString)
    (hu : ∀ t : BitString × BitString × BitString, t.1.length = n → t.2.1.length = n →
      t.2.2.length = n → (u t).length = n)
    (hv : ∀ t : BitString × BitString × BitString, t.1.length = n → t.2.1.length = n →
      t.2.2.length = n → (v t).length = n)
    (hw : ∀ t : BitString × BitString × BitString, t.1.length = n → t.2.1.length = n →
      t.2.2.length = n → (w t).length = n) :
    exists_computable_family_problemK_quad_ge_served n Q F u v w ⊆
      {t | t ∈ exists_computable_family_problemK_quad_ge_check_triplesList n ∧
        ∃ p ∈ (hF.toFinset.image fun fg =>
          (exists_computable_family_problemK_quad_ge_check_restr n fg.1,
           exists_computable_family_problemK_quad_ge_check_restr n
            fg.2)).toList,
          exists_computable_family_problemK_quad_ge_check_ev p.1 (u t) =
            some (v t) ∧
          exists_computable_family_problemK_quad_ge_check_ev p.2 (w t) =
            some (Q t.1 t.2.1 t.2.2)} := by
  rintro t ⟨h1, h2, h3, fg, hfg, e1, e2⟩
  refine ⟨((exists_computable_family_problemK_quad_ge_check_triples_spec
    n).2 t).2 ⟨h1, h2, h3⟩, _, Finset.mem_toList.2 (Finset.mem_image.2
      ⟨fg, hF.mem_toFinset.2 hfg, rfl⟩), ?_, ?_⟩
  · rw [← e1]
    exact exists_computable_family_problemK_quad_ge_check_ev_restr n fg.1
      (u t) (hu t h1 h2 h3) (by rw [e1]; exact hv t h1 h2 h3)
  · rw [← e2]
    exact exists_computable_family_problemK_quad_ge_check_ev_restr n fg.2
      (w t) (hw t h1 h2 h3) (by rw [e2]; exact hQ _ _ _ h1 h2 h3)

/-- Auxiliary (lift): the triples served by a list `R` of restricted pairs are served by the
family of the lifted pairs. -/
private theorem exists_computable_family_problemK_quad_ge_check_sub_lift
    (n : ℕ) (Q : BitString → BitString → BitString → BitString)
    (R : List (List (BitString × BitString) × List (BitString × BitString)))
    (u v w : BitString × BitString × BitString → BitString) :
    {t | t ∈ exists_computable_family_problemK_quad_ge_check_triplesList n ∧
        ∃ p ∈ R, exists_computable_family_problemK_quad_ge_check_ev p.1 (u t) =
          some (v t) ∧
          exists_computable_family_problemK_quad_ge_check_ev p.2 (w t) =
          some (Q t.1 t.2.1 t.2.2)} ⊆
      exists_computable_family_problemK_quad_ge_served n Q
        ((fun p => (exists_computable_family_problemK_quad_ge_check_lift p.1,
          exists_computable_family_problemK_quad_ge_check_lift p.2)) ''
          {p | p ∈ R}) u v w := by
  rintro t ⟨ht, p, hp, e1, e2⟩
  obtain ⟨h1, h2, h3⟩ :=
    ((exists_computable_family_problemK_quad_ge_check_triples_spec n).2 t).1 ht
  refine ⟨h1, h2, h3, _, ⟨p, hp, rfl⟩, ?_, ?_⟩
  · simp only [exists_computable_family_problemK_quad_ge_check_lift, e1,
      Option.getD_some]
  · simp only [exists_computable_family_problemK_quad_ge_check_lift, e2,
      Option.getD_some]

/-- Auxiliary: correctness of the finite check.  Restricting a family `F` to `n`-bit words gives a
candidate family serving at least the triples served by `F`; conversely, lifting a candidate
family by a default value gives a family of at most the same size serving at least the same
triples. -/
private theorem exists_computable_family_problemK_quad_ge_check_correct
    (c n : ℕ) (Q : BitString → BitString → BitString → BitString) :
    exists_computable_family_problemK_quad_ge_check_chk0 c n
      ((exists_computable_family_problemK_quad_ge_check_triplesList n).map
        fun t => (t, Q t.1 t.2.1 t.2.2)) = true ↔
      ((∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
          (Q a b e).length = n) ∧
        exists_computable_family_problemK_quad_ge_good c n Q) := by
  classical
  have hspec := (exists_computable_family_problemK_quad_ge_check_triples_spec
    n).2
  have hfinT : {t : BitString × BitString × BitString |
      t ∈ exists_computable_family_problemK_quad_ge_check_triplesList n}.Finite
          :=
    List.finite_toSet _
  have hsfin : ∀ (F : Set ((BitString → BitString) × (BitString → BitString)))
      (u v w : BitString × BitString × BitString → BitString),
      (exists_computable_family_problemK_quad_ge_served n Q F u v w).Finite := fun F u v w =>
    hfinT.subset fun t ht => (hspec t).2 ⟨ht.1, ht.2.1, ht.2.2.1⟩
  unfold exists_computable_family_problemK_quad_ge_check_chk0
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    exists_computable_family_problemK_quad_ge_check_cnt_eq]
  constructor
  · rintro ⟨hlen, hR⟩
    have hQ : ∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
        (Q a b e).length = n := by
      intro a b e ha hb he
      exact hlen ((a, b, e), Q a b e) (List.mem_map.2 ⟨(a, b, e), (hspec _).2 ⟨ha, hb, he⟩, rfl⟩)
    refine ⟨hQ, fun F hF hFc => ?_⟩
    have hRlen : (hF.toFinset.image fun fg =>
        (exists_computable_family_problemK_quad_ge_check_restr n fg.1,
         exists_computable_family_problemK_quad_ge_check_restr n
          fg.2)).toList.length ≤ F.ncard := by
      rw [Finset.length_toList, Set.ncard_eq_toFinset_card F hF]
      exact Finset.card_image_le
    have hlt : (hF.toFinset.image fun fg =>
        (exists_computable_family_problemK_quad_ge_check_restr n fg.1,
         exists_computable_family_problemK_quad_ge_check_restr n
          fg.2)).toList.length * 2 ^ logSlack c n < 2 ^ (2 * n) :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hRlen) hFc
    have hRmem : (hF.toFinset.image fun fg =>
        (exists_computable_family_problemK_quad_ge_check_restr n fg.1,
         exists_computable_family_problemK_quad_ge_check_restr n
          fg.2)).toList ∈ exists_computable_family_problemK_quad_ge_check_fams
              n := by
      unfold exists_computable_family_problemK_quad_ge_check_fams
      rw [exists_computable_family_problemK_quad_ge_check_rlists_spec]
      refine ⟨fun p hp => ?_, ?_⟩
      · rw [Finset.mem_toList, Finset.mem_image] at hp
        obtain ⟨fg, _, rfl⟩ := hp
        exact (exists_computable_family_problemK_quad_ge_check_mem_ps n _).2
          ⟨exists_computable_family_problemK_quad_ge_check_restr_mem n fg.1,
           exists_computable_family_problemK_quad_ge_check_restr_mem n fg.2⟩
      · have : 1 ≤ 2 ^ logSlack c n := Nat.one_le_two_pow
        nlinarith
    rcases hR _ hRmem with h | ⟨⟨g1, g2⟩, g3⟩
    · exact absurd h (not_le.2 hlt)
    · refine ⟨lt_of_le_of_lt (Nat.mul_le_mul_left 8 (Set.ncard_le_ncard
        (exists_computable_family_problemK_quad_ge_check_sub_restr n Q hQ F hF
          _ _ _ (fun t h1 _ _ => h1) (fun t _ _ h3 => h3) (fun t _ h2 _ => h2))
        (hfinT.subset fun t ht => ht.1))) g1,
        lt_of_le_of_lt (Nat.mul_le_mul_left 8 (Set.ncard_le_ncard
        (exists_computable_family_problemK_quad_ge_check_sub_restr n Q hQ F hF
          _ _ _ (fun t _ _ h3 => h3) (fun t _ h2 _ => h2) (fun t h1 _ _ => h1))
        (hfinT.subset fun t ht => ht.1))) g2,
        lt_of_le_of_lt (Nat.mul_le_mul_left 8 (Set.ncard_le_ncard
        (exists_computable_family_problemK_quad_ge_check_sub_restr n Q hQ F hF
          _ _ _ (fun t _ h2 _ => h2) (fun t h1 _ _ => h1) (fun t _ _ h3 => h3))
        (hfinT.subset fun t ht => ht.1))) g3⟩
  · rintro ⟨hQ, hgood⟩
    refine ⟨?_, fun R _ => ?_⟩
    · intro q hq
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h2, h3⟩ := (hspec t).1 ht
      exact hQ _ _ _ h1 h2 h3
    · by_cases hlt : R.length * 2 ^ logSlack c n < 2 ^ (2 * n)
      · right
        have hF : ((fun p =>
          (exists_computable_family_problemK_quad_ge_check_lift
            p.1, exists_computable_family_problemK_quad_ge_check_lift p.2)) ''
            {p | p ∈ R}).Finite := (List.finite_toSet R).image _
        have hFc : ((fun p =>
          (exists_computable_family_problemK_quad_ge_check_lift
            p.1, exists_computable_family_problemK_quad_ge_check_lift p.2)) ''
            {p | p ∈ R}).ncard * 2 ^ logSlack c n < 2 ^ (2 * n) :=
          lt_of_le_of_lt (Nat.mul_le_mul_right _ ((Set.ncard_image_le (List.finite_toSet R)).trans
            (exists_computable_family_problemK_quad_ge_check_ncard_le R))) hlt
        obtain ⟨g1, g2, g3⟩ := hgood _ hF hFc
        exact ⟨⟨lt_of_le_of_lt (Nat.mul_le_mul_left 8 (Set.ncard_le_ncard
          (exists_computable_family_problemK_quad_ge_check_sub_lift n Q R _ _ _)
          (hsfin _ _ _ _))) g1,
          lt_of_le_of_lt (Nat.mul_le_mul_left 8 (Set.ncard_le_ncard
          (exists_computable_family_problemK_quad_ge_check_sub_lift n Q R _ _ _)
          (hsfin _ _ _ _))) g2⟩,
          lt_of_le_of_lt (Nat.mul_le_mul_left 8 (Set.ncard_le_ncard
          (exists_computable_family_problemK_quad_ge_check_sub_lift n Q R _ _ _)
          (hsfin _ _ _ _))) g3⟩
      · left
        exact not_lt.1 hlt

/-- Auxiliary: `..._wordsList` is primitive recursive. -/
private theorem exists_computable_family_problemK_quad_ge_check_wordsList_primrec
    :
    Primrec exists_computable_family_problemK_quad_ge_check_wordsList := by
  have hg : Primrec₂ (fun (_ : ℕ × List BitString) (w : BitString) =>
      [false :: w, true :: w]) :=
    Primrec.list_cons.comp
      (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.const true) Primrec.snd) (Primrec.const []))
  have hf : Primrec₂ (fun (_ : ℕ) (IH : List BitString) =>
      IH.flatMap fun w => [false :: w, true :: w]) :=
    Primrec.list_flatMap Primrec.snd hg
  refine (Primrec.nat_rec₁ [[]] hf).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [exists_computable_family_problemK_quad_ge_check_wordsList]
    rw [← ih]

/-- Auxiliary: `..._triplesList` is primitive recursive. -/
private theorem exists_computable_family_problemK_quad_ge_check_triplesList_primrec :
    Primrec exists_computable_family_problemK_quad_ge_check_triplesList := by
  have hw := exists_computable_family_problemK_quad_ge_check_wordsList_primrec
  unfold exists_computable_family_problemK_quad_ge_check_triplesList
  refine Primrec.list_flatMap hw (Primrec.list_flatMap (hw.comp Primrec.fst)
    (Primrec.list_map (hw.comp (Primrec.fst.comp Primrec.fst)) ?_))
  exact Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)

/-- Auxiliary: `..._rlists` is primitive recursive. -/
private theorem exists_computable_family_problemK_quad_ge_check_rlists_primrec
    {P : Type} [Primcodable P] :
    Primrec₂ (exists_computable_family_problemK_quad_ge_check_rlists
      (P := P)) := by
  have hstep : Primrec₂ (fun (ps : List P) (q : ℕ × List (List P)) =>
      ([] : List P) :: ps.flatMap fun p => q.2.map (p :: ·)) :=
    Primrec.list_cons.comp (Primrec.const []) (Primrec.list_flatMap Primrec.fst
      (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)))
  have h := Primrec.nat_rec' (f := fun x : List P × ℕ => x.2)
    (g := fun _ => ([[]] : List (List P)))
    (h := fun x q => ([] : List P) :: x.1.flatMap fun p => q.2.map (p :: ·))
    Primrec.snd (Primrec.const [[]]) (hstep.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  refine h.of_eq fun x => ?_
  rcases x with ⟨ps, j⟩
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [exists_computable_family_problemK_quad_ge_check_rlists]
    rw [← ih]

/-- Auxiliary: `..._ev` is primitive recursive. -/
private theorem exists_computable_family_problemK_quad_ge_check_ev_primrec :
    Primrec₂ exists_computable_family_problemK_quad_ge_check_ev := by
  have hh : Primrec₂ (fun (a : List (BitString × BitString) × BitString)
      (q : (BitString × BitString) × Option BitString) =>
      if q.1.1 = a.2 then some q.1.2 else q.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.fst (Primrec.const none) hh).of_eq fun _ => rfl

/-- Auxiliary: `..._cnt` is primitive recursive for primitive recursive orientations. -/
private theorem exists_computable_family_problemK_quad_ge_check_cnt_primrec
    {u v w : BitString × BitString × BitString → BitString}
    (hu : Primrec u) (hv : Primrec v) (hw : Primrec w) :
    Primrec₂ (fun (R : List (List (BitString × BitString) × List (BitString × BitString)))
      (data : List ((BitString × BitString × BitString) × BitString)) =>
      exists_computable_family_problemK_quad_ge_check_cnt R u v w data) := by
  have hev := exists_computable_family_problemK_quad_ge_check_ev_primrec
  have hdec : Primrec₂ (fun a b : Option BitString => decide (a = b)) := Primrec.eq.decide
  unfold exists_computable_family_problemK_quad_ge_check_cnt
  refine Primrec.list_length.comp (Primrec.list_filter Primrec.snd ?_)
  refine list_any_primrec (Primrec.fst.comp Primrec.fst) ?_
  refine Primrec.and.comp ?_ ?_
  · exact hdec.comp (hev.comp (Primrec.fst.comp Primrec.snd)
      (hu.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.option_some.comp (hv.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  · exact hdec.comp (hev.comp (Primrec.snd.comp Primrec.snd)
      (hw.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

/-- Auxiliary: `..._fams` is primitive recursive. -/
private theorem exists_computable_family_problemK_quad_ge_check_fams_primrec :
    Primrec exists_computable_family_problemK_quad_ge_check_fams := by
  have hW := exists_computable_family_problemK_quad_ge_check_wordsList_primrec
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hpairs : Primrec exists_computable_family_problemK_quad_ge_check_pairsW :=
      by
    unfold exists_computable_family_problemK_quad_ge_check_pairsW
    exact Primrec.list_flatMap hW (Primrec.list_map (hW.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  have hgraphs : Primrec exists_computable_family_problemK_quad_ge_check_graphs
      := by
    unfold exists_computable_family_problemK_quad_ge_check_graphs
    exact exists_computable_family_problemK_quad_ge_check_rlists_primrec.comp
      hpairs (Primrec.list_length.comp hW)
  have hps : Primrec exists_computable_family_problemK_quad_ge_check_ps := by
    unfold exists_computable_family_problemK_quad_ge_check_ps
    exact Primrec.list_flatMap hgraphs (Primrec.list_map (hgraphs.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  unfold exists_computable_family_problemK_quad_ge_check_fams
  exact exists_computable_family_problemK_quad_ge_check_rlists_primrec.comp
    hps (hpow.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))

/-- Auxiliary: the finite check is primitive recursive. -/
private theorem exists_computable_family_problemK_quad_ge_check_chk0_primrec
    (c : ℕ) :
    Primrec (fun x : ℕ × List ((BitString × BitString × BitString) × BitString) =>
      exists_computable_family_problemK_quad_ge_check_chk0 c x.1 x.2) := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hL : Primrec (fun n => logSlack c n) := by
    unfold logSlack
    exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const c)
      (Primrec.list_length.comp Kolmogorov.primrec_natBits)) (Primrec.const c)
  have hfams := exists_computable_family_problemK_quad_ge_check_fams_primrec
  have hc1 := exists_computable_family_problemK_quad_ge_check_cnt_primrec
    (u := fun t => t.1) (v := fun t => t.2.2) (w := fun t => t.2.1) Primrec.fst
    (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  have hc2 := exists_computable_family_problemK_quad_ge_check_cnt_primrec
    (u := fun t => t.2.2) (v := fun t => t.2.1) (w := fun t => t.1)
    (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hc3 := exists_computable_family_problemK_quad_ge_check_cnt_primrec
    (u := fun t => t.2.1) (v := fun t => t.1) (w := fun t => t.2.2)
    (Primrec.fst.comp Primrec.snd) Primrec.fst (Primrec.snd.comp Primrec.snd)
  -- the bound `2 ^ (3 n)`, as a function of `(x, R)`
  have h3n : Primrec (fun y : (ℕ × List ((BitString × BitString × BitString) × BitString)) ×
      List (List (BitString × BitString) × List (BitString × BitString)) => 2 ^ (3 * y.1.1)) :=
    hpow.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec.fst.comp Primrec.fst))
  have hlt : Primrec₂ (fun a b : ℕ => decide (a < b)) := Primrec.nat_lt.decide
  unfold exists_computable_family_problemK_quad_ge_check_chk0
  refine Primrec.and.comp ?_ ?_
  · exact list_all_primrec Primrec.snd (Primrec.eq.decide.comp
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)) (Primrec.fst.comp Primrec.fst))
  · refine list_all_primrec (hfams.comp Primrec.fst) ?_
    refine Primrec.or.comp ?_ (Primrec.and.comp (Primrec.and.comp ?_ ?_) ?_)
    · exact Primrec.nat_le.decide.comp
        (hpow.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.fst.comp Primrec.fst)))
        (Primrec.nat_mul.comp (Primrec.list_length.comp Primrec.snd)
          (hpow.comp (Primrec.const 2) (hL.comp (Primrec.fst.comp Primrec.fst))))
    · exact hlt.comp (Primrec.nat_mul.comp (Primrec.const 8)
        (hc1.comp Primrec.snd (Primrec.snd.comp Primrec.fst))) h3n
    · exact hlt.comp (Primrec.nat_mul.comp (Primrec.const 8)
        (hc2.comp Primrec.snd (Primrec.snd.comp Primrec.fst))) h3n
    · exact hlt.comp (Primrec.nat_mul.comp (Primrec.const 8)
        (hc3.comp Primrec.snd (Primrec.snd.comp Primrec.fst))) h3n

/-- Step 2 of the proof of `exists_computable_family_problemK_quad_ge_search`:
decidability of goodness, uniformly in the table.  For a computable family of tables `T n k`,
the property "`T n k` has `n`-bit values on triples of `n`-bit words and is good for `c`, `n`" is
computably decidable in `(n, k)`.  Proof idea: goodness depends only on the restriction of `T n k`
to the finitely many `n`-bit triples, and, for the family `F`, only on the restrictions of the
functions of `F` to `n`-bit words with values in `n`-bit words (a value that is not an `n`-bit
word never matches); so it is equivalent to the finite check "every set of fewer than
`2^(2n − logSlack c n)` pairs of such restricted functions serves less than `1/8` of the
`n`-bit triples in each of the three orientations" (a family `F` yields a set of restricted pairs
of at most the same size serving the same triples; a set of restricted pairs lifts to a family by
extending with a default value), a finite computation using `T`. -/
private theorem exists_computable_family_problemK_quad_ge_check (c : ℕ)
    (T : ℕ → ℕ → BitString → BitString → BitString → BitString)
    (hT : Computable (fun x : ℕ × ℕ × BitString × BitString × BitString =>
      T x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)) :
    ∃ Chk : ℕ → ℕ → Bool, Computable (fun x : ℕ × ℕ => Chk x.1 x.2) ∧
      ∀ n k : ℕ, Chk n k = true ↔
        ((∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
          (T n k a b e).length = n) ∧
        exists_computable_family_problemK_quad_ge_good c n (T n k)) := by
  refine ⟨fun n k =>
    exists_computable_family_problemK_quad_ge_check_chk0 c n
      ((exists_computable_family_problemK_quad_ge_check_triplesList n).map
        fun t => (t, T n k t.1 t.2.1 t.2.2)), ?_,
    fun n k =>
      exists_computable_family_problemK_quad_ge_check_correct c n (T n k)⟩
  have hf : Computable₂ (fun (x : ℕ × ℕ) (t : BitString × BitString × BitString) =>
      (t, T x.1 x.2 t.1 t.2.1 t.2.2)) :=
    Computable.pair Computable.snd
      (hT.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp Computable.fst)
          (Computable.pair (Computable.fst.comp Computable.snd)
            (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.snd))
              (Computable.snd.comp (Computable.snd.comp Computable.snd)))))))
  have hl : Computable (fun x : ℕ × ℕ =>
      ((exists_computable_family_problemK_quad_ge_check_triplesList x.1).map
        fun t => (t, T x.1 x.2 t.1 t.2.1 t.2.2))) :=
    Computable.list_map
      (l := fun x : ℕ × ℕ =>
        exists_computable_family_problemK_quad_ge_check_triplesList x.1)
      (exists_computable_family_problemK_quad_ge_check_triplesList_primrec.to_comp.comp
        Computable.fst) hf
  have key : ∀ F : ℕ → List ((BitString × BitString × BitString) × BitString) → Bool,
      Computable (fun x : ℕ × List ((BitString × BitString × BitString) × BitString) =>
        F x.1 x.2) →
      Computable (fun x : ℕ × ℕ => F x.1
        ((exists_computable_family_problemK_quad_ge_check_triplesList x.1).map
          fun t => (t, T x.1 x.2 t.1 t.2.1 t.2.2))) := fun F hF =>
    hF.comp (Computable.pair Computable.fst hl)
  exact key _
    (exists_computable_family_problemK_quad_ge_check_chk0_primrec c).to_comp

/-- Step 2 of the proof of `exists_computable_family_problemK_quad_ge`: exhaustive
search.  If for every `n ≥ N` some `Qn` (with `n`-bit values on `n`-bit triples) is good, then a
*computable* family `Q` of good functions exists: `Q n` is the first function table, in a fixed
enumeration of finite tables on the `2^{3n}` triples of `n`-bit words, passing the (finite,
decidable) check "every family of fewer than `2^(2n − logSlack c n)` pairs of functions on
`n`-bit words serves less than `1/8` of the triples in each orientation", extended by a default
value outside the `n`-bit triples. -/
private theorem exists_computable_family_problemK_quad_ge_search (c N : ℕ)
    (h : ∀ n ≥ N, ∃ Qn : BitString → BitString → BitString → BitString,
      (∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
        (Qn a b e).length = n) ∧
      exists_computable_family_problemK_quad_ge_good c n Qn) :
    ∃ Q : ℕ → BitString → BitString → BitString → BitString,
      Computable (fun t : ℕ × BitString × BitString × BitString =>
        Q t.1 t.2.1 t.2.2.1 t.2.2.2) ∧
      ∀ n ≥ N, (∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
        (Q n a b e).length = n) ∧
      exists_computable_family_problemK_quad_ge_good c n (Q n) := by
  obtain ⟨T, hT, hTenum⟩ := exists_computable_family_problemK_quad_ge_enum
  obtain ⟨Chk, hChk, hChkiff⟩ :=
    exists_computable_family_problemK_quad_ge_check c T hT
  -- the least admissible index (`0` below `N`)
  let Chk' : ℕ → ℕ → Bool := fun n k => decide (n < N) || Chk n k
  have hex : ∀ n, ∃ k, Chk' n k = true := by
    intro n
    by_cases hn : n < N
    · exact ⟨0, by simp [Chk', hn]⟩
    · obtain ⟨Qn, hlen, hgood⟩ := h n (not_lt.1 hn)
      obtain ⟨k, hk⟩ := hTenum n Qn hlen
      refine ⟨k, ?_⟩
      have : Chk n k = true := by
        rw [hChkiff]
        refine ⟨fun a b e ha hb he => by rw [hk a b e ha hb he]; exact hlen a b e ha hb he, ?_⟩
        exact exists_computable_family_problemK_quad_ge_search_good_congr c n Qn _
          (fun a b e ha hb he => (hk a b e ha hb he).symm) hgood
      simp [Chk', this]
  classical
  let K : ℕ → ℕ := fun n => Nat.find (hex n)
  have hChk' : Computable₂ Chk' := by
    have h1 : Computable (fun x : ℕ × ℕ => decide (x.1 < N)) :=
      (Primrec.nat_lt.comp Primrec.fst (Primrec.const N)).decide.to_comp
    exact (Primrec.or.to_comp).comp h1 hChk
  have hK : Computable K := by
    have hp : Partrec₂ (fun n k => (Chk' n k : Part Bool)) := hChk'.partrec₂
    refine Partrec.of_eq_tot (Partrec.rfind hp) fun n => ?_
    refine Nat.mem_rfind.2 ⟨by simpa [K] using Nat.find_spec (hex n), fun {m} hm => ?_⟩
    have := Nat.find_min (hex n) hm
    simpa using this
  have hK' : ∀ n, Chk' n (K n) = true := fun n => Nat.find_spec (hex n)
  refine ⟨fun n a b e =>
    if a.length = n ∧ b.length = n ∧ e.length = n then T n (K n) a b e else [], ?_, ?_⟩
  · have hd : ∀ {f : ℕ × BitString × BitString × BitString → BitString},
        Computable f → Computable (fun t => decide ((f t).length = t.1)) := fun hf =>
      (show Computable₂ (fun a b : ℕ => decide (a = b)) from Primrec.eq.decide.to_comp).comp
        (Computable.list_length.comp hf) Computable.fst
    have hc : Computable (fun t : ℕ × BitString × BitString × BitString =>
        decide (t.2.1.length = t.1 ∧ t.2.2.1.length = t.1 ∧ t.2.2.2.length = t.1)) := by
      have h1 := hd (f := fun t => t.2.1) (Computable.fst.comp Computable.snd)
      have h2 := hd (f := fun t => t.2.2.1)
        (Computable.fst.comp (Computable.snd.comp Computable.snd))
      have h3 := hd (f := fun t => t.2.2.2)
        (Computable.snd.comp (Computable.snd.comp Computable.snd))
      refine Computable.of_eq ((Primrec.and.to_comp).comp h1 ((Primrec.and.to_comp).comp h2 h3))
        fun t => ?_
      simp
    have hKc : Computable (fun t : ℕ × BitString × BitString × BitString => K t.1) :=
      hK.comp Computable.fst
    have hTc : Computable (fun t : ℕ × BitString × BitString × BitString =>
        T t.1 (K t.1) t.2.1 t.2.2.1 t.2.2.2) :=
      hT.comp (Computable.pair Computable.fst (Computable.pair hKc Computable.snd))
    refine Computable.of_eq (Computable.cond hc hTc (Computable.const [])) fun t => ?_
    by_cases hcond : t.2.1.length = t.1 ∧ t.2.2.1.length = t.1 ∧ t.2.2.2.length = t.1
    · simp [hcond]
    · simp [hcond]
  · intro n hn
    have hnN : ¬ n < N := not_lt.2 hn
    have hCk : Chk n (K n) = true := by simpa [Chk', hnN] using hK' n
    obtain ⟨hlen, hgood⟩ := (hChkiff n (K n)).1 hCk
    refine ⟨fun a b e ha hb he => ?_, ?_⟩
    · simp only [ha, hb, he, and_self, ite_true]
      exact hlen a b e ha hb he
    · refine exists_computable_family_problemK_quad_ge_search_good_congr c n (T n (K n)) _
        (fun a b e ha hb he => ?_) hgood
      simp [ha, hb, he]

/-- The function `x ↦ [α](x)` (value of the language, a default if undefined). -/
private noncomputable def exists_computable_family_problemK_quad_ge_serving_fn
    (P : ProblemCalculus) (α : BitString) (a : BitString) : BitString := by
  classical
  exact if h : ∃ y, y ∈ P.lang (α, a) then h.choose else []

/-- The pair of functions `(f_z, g_z)` attached to a string `z`. -/
private noncomputable def exists_computable_family_problemK_quad_ge_serving_pr
    (P : ProblemCalculus) (z : BitString) : (BitString → BitString) × (BitString → BitString) :=
  match P.unpair z with
  | some (α, β) => (exists_computable_family_problemK_quad_ge_serving_fn P α,
      exists_computable_family_problemK_quad_ge_serving_fn P β)
  | none => (fun _ => [], fun _ => [])

private lemma exists_computable_family_problemK_quad_ge_serving_fn_eq
    (P : ProblemCalculus) (α a e : BitString) (h : e ∈ P.lang (α, a)) :
    exists_computable_family_problemK_quad_ge_serving_fn P α a = e := by
  have hex : ∃ y, y ∈ P.lang (α, a) := ⟨e, h⟩
  unfold exists_computable_family_problemK_quad_ge_serving_fn
  rw [dite_eq_left hex]
  exact Part.mem_unique hex.choose_spec h

/-- Step 3 of the proof of `exists_computable_family_problemK_quad_ge`: low-complexity
solutions are few.  For all `n, s` there is a finite set `F` of pairs of functions with
`|F| · 2^s < 2^(2n)` such that whenever the problem `(a → e) ∧ (b → d)` has complexity
`+ s < 2n`, some `(f, g) ∈ F` has `f a = e` and `g b = d`.  Proof: `F` is the set of the pairs
`(f_x, g_x)`, `x = [α, β]` (inverse pairing `P.unpair`), over the fewer than `2^(2n − s)`
strings `x` with `C(x) + s < 2n`, where `f_x a` is the value of `lang (α, a)` (default if
undefined) and `g_x` likewise with `β`; a solution `[α, β]` with `e ∈ lang (α, a)` and
`d ∈ lang (β, b)` gives `f a = e`, `g b = d`.  The count is
`{x | condK D x [] < m}.encard < 2 ^ m`. -/
private theorem exists_computable_family_problemK_quad_ge_serving (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) (n s : ℕ) :
    ∃ F : Set ((BitString → BitString) × (BitString → BitString)),
      F.Finite ∧ F.ncard * 2 ^ s < 2 ^ (2 * n) ∧
      ∀ a b e d : BitString,
        problemK D (quadProblem P ![a, b, e, d]) + (s : ℕ∞) < ((2 * n : ℕ) : ℕ∞) →
          ∃ fg ∈ F, fg.1 a = e ∧ fg.2 b = d := by
  classical
  set m : ℕ := 2 * n - s with hm
  obtain ⟨hXfin, hXcard⟩ :=
    (isEnumerableFamily_complexityBelow_and_card_lt_two_pow D hD).2 m
  set X : Set BitString := {x : BitString | plainK D x < (m : ℕ∞)} with hX
  set F : Set ((BitString → BitString) × (BitString → BitString)) :=
    (fun z => exists_computable_family_problemK_quad_ge_serving_pr P z) '' X with hF
  have hFfin : F.Finite := hXfin.image _
  have hFcard : F.ncard ≤ X.ncard := Set.ncard_image_le hXfin
  refine ⟨F, hFfin, ?_, ?_⟩
  · by_cases hs : s ≤ 2 * n
    · have h1 : F.ncard < 2 ^ m := lt_of_le_of_lt hFcard hXcard
      calc F.ncard * 2 ^ s < 2 ^ m * 2 ^ s :=
            Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos s)
        _ = 2 ^ (2 * n) := by rw [← pow_add]; congr 1; omega
    · have hm0 : m = 0 := by omega
      have : F.ncard = 0 := by
        have h1 : F.ncard < 2 ^ m := lt_of_le_of_lt hFcard hXcard
        rw [hm0] at h1; omega
      rw [this]; simp
  · intro a b e d hlt
    have hne : (quadProblem P ![a, b, e, d]).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      rw [h, problemK_empty] at hlt
      simp at hlt
    obtain ⟨z, hz, hzeq⟩ := exists_mem_plainK_eq_problemK D hne
    rw [← hzeq] at hlt
    obtain ⟨p, hp, q, hq, hpq⟩ := hz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hp hq
    have hzX : z ∈ X := by
      change plainK D z < (m : ℕ∞)
      generalize plainK D z = k at hlt
      induction k using ENat.recTopCoe with
      | top => simp at hlt
      | coe k =>
        have : k + s < 2 * n := by exact_mod_cast hlt
        exact_mod_cast (show k < m by omega)
    have hun : P.unpair z = some (p, q) := by rw [← hpq]; exact hP.2.2.1 p q
    obtain ⟨y1, hy1, hy1'⟩ := hp a rfl
    obtain ⟨y2, hy2, hy2'⟩ := hq b rfl
    simp only [Set.mem_singleton_iff] at hy1 hy2
    subst hy1 hy2
    refine ⟨exists_computable_family_problemK_quad_ge_serving_pr P z, ⟨z, hzX, rfl⟩, ?_, ?_⟩
    · unfold exists_computable_family_problemK_quad_ge_serving_pr
      rw [hun]
      exact exists_computable_family_problemK_quad_ge_serving_fn_eq P p a _ hy1'
    · unfold exists_computable_family_problemK_quad_ge_serving_pr
      rw [hun]
      exact exists_computable_family_problemK_quad_ge_serving_fn_eq P q b _ hy2'

/-- SUV Theorem 247, second Lemma of the probabilistic proof (Section 13.6, printed p. 423).
For all sufficiently large `n` there is a function `Q` on triples of `n`-bit words, of
complexity `log n + O(1)`, such that for more than half of the triples `(a, b, c)` of `n`-bit
words each of the problems `(a → c) ∧ (b → Q(a, b, c))`, `(c → b) ∧ (a → Q(a, b, c))`,
`(b → a) ∧ (c → Q(a, b, c))` has complexity at least `2n − O(log n)`.
"Complexity `log n + O(1)`" is formalized as the book obtains it: `Q` is the `n`-th member of a
computable family (found from `n` by exhaustive search for a decidable property).  This is
stronger than the literal statement (a computable family has `C(Q_n) ≤ log n + O(1)`) and is
what the proof of Theorem 247 uses: `d̃ = Q(ã, b̃, c̃)` is computable from `n` and `(ã, b̃, c̃)`.
The first lemma of the probabilistic proof (printed p. 421: one problem, at least half of the
triples) is a weakening of this one and is not stated separately.
Book's proof: the property "every set of fewer than `2^k` pairs of functions `S → S` serves less
than `1/8` of the quadruples `(a, b, c, Q(a, b, c))`", `k = 2n − log n − O(1)`, holds for a
random `Q` with positive probability (bad/good triples, Chernoff bound, union bound over the
`2^{2^{n+k+log n+1}}` sets), for each of the three symmetric properties; `1/8 + 1/8 + 1/8 < 1/2`.
The problems are written with `quadProblem` (`(q 0 → q 2) ∧ (q 1 → q 3)`). -/
theorem exists_computable_family_problemK_quad_ge (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ (Q : ℕ → BitString → BitString → BitString → BitString) (c N : ℕ),
      Computable (fun t : ℕ × BitString × BitString × BitString =>
        Q t.1 t.2.1 t.2.2.1 t.2.2.2) ∧
      ∀ n ≥ N,
        (∀ a b e : BitString, a.length = n → b.length = n → e.length = n →
          (Q n a b e).length = n) ∧
        2 ^ (3 * n) < 2 * {t : BitString × BitString × BitString |
          t.1.length = n ∧ t.2.1.length = n ∧ t.2.2.length = n ∧
          ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.1, t.2.1, t.2.2,
            Q n t.1 t.2.1 t.2.2]) + (logSlack c n : ℕ∞) ∧
          ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.2, t.1, t.2.1,
            Q n t.1 t.2.1 t.2.2]) + (logSlack c n : ℕ∞) ∧
          ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.1, t.2.2, t.1,
            Q n t.1 t.2.1 t.2.2]) + (logSlack c n : ℕ∞)}.ncard := by
  obtain ⟨c, N, h⟩ := exists_computable_family_problemK_quad_ge_exists
  obtain ⟨Q, hQc, hQ⟩ := exists_computable_family_problemK_quad_ge_search c N h
  refine ⟨Q, c, N, hQc, fun n hn => ⟨(hQ n hn).1, ?_⟩⟩
  obtain ⟨F, hFfin, hFcard, hF⟩ :=
    exists_computable_family_problemK_quad_ge_serving D hD P hP n (logSlack c n)
  obtain ⟨h1, h2, h3⟩ := (hQ n hn).2 F hFfin hFcard
  obtain ⟨hTfin, hTcard⟩ := exists_computable_family_problemK_quad_ge_triples_ncard n
  set T : Set (BitString × BitString × BitString) := {t | t.1.length = n ∧ t.2.1.length = n ∧
      t.2.2.length = n} with hT
  set G : Set (BitString × BitString × BitString) := {t : BitString × BitString × BitString |
          t.1.length = n ∧ t.2.1.length = n ∧ t.2.2.length = n ∧
          ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.1, t.2.1, t.2.2,
            Q n t.1 t.2.1 t.2.2]) + (logSlack c n : ℕ∞) ∧
          ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.2, t.1, t.2.1,
            Q n t.1 t.2.1 t.2.2]) + (logSlack c n : ℕ∞) ∧
          ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.1, t.2.2, t.1,
            Q n t.1 t.2.1 t.2.2]) + (logSlack c n : ℕ∞)} with hG
  set S1 := exists_computable_family_problemK_quad_ge_served n (Q n) F
    (fun t => t.1) (fun t => t.2.2) (fun t => t.2.1) with hS1
  set S2 := exists_computable_family_problemK_quad_ge_served n (Q n) F
    (fun t => t.2.2) (fun t => t.2.1) (fun t => t.1) with hS2
  set S3 := exists_computable_family_problemK_quad_ge_served n (Q n) F
    (fun t => t.2.1) (fun t => t.1) (fun t => t.2.2) with hS3
  have hGT : G ⊆ T := fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩
  have hS1T : S1 ⊆ T := fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩
  have hS2T : S2 ⊆ T := fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩
  have hS3T : S3 ⊆ T := fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩
  have hsub : T ⊆ G ∪ S1 ∪ S2 ∪ S3 := by
    intro t ht
    by_cases hc1 : ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.1, t.2.1, t.2.2,
        Q n t.1 t.2.1 t.2.2]) + (logSlack c n : ℕ∞)
    · by_cases hc2 : ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.2, t.1, t.2.1,
          Q n t.1 t.2.1 t.2.2]) + (logSlack c n : ℕ∞)
      · by_cases hc3 : ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.1, t.2.2, t.1,
            Q n t.1 t.2.1 t.2.2]) + (logSlack c n : ℕ∞)
        · exact Or.inl (Or.inl (Or.inl ⟨ht.1, ht.2.1, ht.2.2, hc1, hc2, hc3⟩))
        · obtain ⟨fg, hfg, e1, e2⟩ := hF _ _ _ _ (not_le.1 hc3)
          exact Or.inr ⟨ht.1, ht.2.1, ht.2.2, fg, hfg, e1, e2⟩
      · obtain ⟨fg, hfg, e1, e2⟩ := hF _ _ _ _ (not_le.1 hc2)
        exact Or.inl (Or.inr ⟨ht.1, ht.2.1, ht.2.2, fg, hfg, e1, e2⟩)
    · obtain ⟨fg, hfg, e1, e2⟩ := hF _ _ _ _ (not_le.1 hc1)
      exact Or.inl (Or.inl (Or.inr ⟨ht.1, ht.2.1, ht.2.2, fg, hfg, e1, e2⟩))
  have hfin : (G ∪ S1 ∪ S2 ∪ S3).Finite :=
    (((hTfin.subset hGT).union (hTfin.subset hS1T)).union (hTfin.subset hS2T)).union
      (hTfin.subset hS3T)
  have hle : T.ncard ≤ G.ncard + S1.ncard + S2.ncard + S3.ncard :=
    calc T.ncard ≤ (G ∪ S1 ∪ S2 ∪ S3).ncard := Set.ncard_le_ncard hsub hfin
      _ ≤ (G ∪ S1 ∪ S2).ncard + S3.ncard := Set.ncard_union_le _ _
      _ ≤ (G ∪ S1).ncard + S2.ncard + S3.ncard := by
          have := Set.ncard_union_le (G ∪ S1) S2; omega
      _ ≤ G.ncard + S1.ncard + S2.ncard + S3.ncard := by
          have := Set.ncard_union_le G S1; omega
  rw [hTcard] at hle
  omega

end InformationLogic
end Kolmogorov
