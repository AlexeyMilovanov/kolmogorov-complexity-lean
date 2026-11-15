/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MuchnikTheorem

/-!
# Church Daley Separation

Separation of Mises–Church–Daley randomness from Mises–Kolmogorov–Loveland randomness.

The main declarations are:

* `not_isMisesChurchRandom_of_computable_bound`: a sequence whose prefixes have complexity at
  most `α n` (`α < 1`) with respect to a computable upper bound for plain complexity is not
  Mises–Church random (Theorem 194 of Shen, Uspensky and Vereshchagin, "Kolmogorov complexity
  and algorithmic randomness"), proved by combining counting bets on the sets of strings of
  small complexity;
* `exists_isMisesChurchDaleyRandom_not_isMisesKLRandom`: there is a Mises–Church–Daley random
  sequence that is not Mises–Kolmogorov–Loveland random (Theorem 195);
* `isMisesChurchDaleyRandom_of_output`: an admissible Kolmogorov–Loveland rule applied to a
  Mises–Kolmogorov–Loveland random sequence gives a Mises–Church–Daley random sequence when
  its output is infinite (Problem 279).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-! ### Proof of Theorem 194

The book's strategy.  For `N` let `A_N` be the set of `N`-bit strings `z` with `k z ≤ (A/B) N`: it
is computable from `N` and has at most `2 ^ ((A/B) N + c + 1)` elements.  The *counting bet* for
`A_N` bets on `0` or `1` in proportion to the difference of the numbers of elements of `A_N`
below the two one-bit extensions of the current prefix; along every element of `A_N` it gains at
least `log 2 · (N - j) - log |A_N|` on the positions `[j, N)`.  The positions are cut into the
blocks `[2^(R t), 2^(R (t+1)))` and the block with end `N = 2^(R (t+1))` uses the bet for `A_N`.
For a large `R` the loss of at most `2^(R t)` on the earlier blocks is negligible, so the gain
after `2^(R (t+1))` steps is `Ω(n)` for infinitely many `n`, contradicting Theorem 170.

All the counts are *tree counts* `x ↦ cnt p (N - |x|) x`, which satisfy
`a x = a (x ++ [false]) + a (x ++ [true])` for `|x| < N`. -/

/-- All bit strings of length `r`. -/
private def ncb_allStr : ℕ → List BitString
  | 0 => [[]]
  | r + 1 =>
    (ncb_allStr r).map (List.cons false) ++
      (ncb_allStr r).map (List.cons true)

/-- The number of strings `u` of length `r` with `p (x ++ u) = true`. -/
private def ncb_cnt (p : BitString → Bool) (r : ℕ)
    (x : BitString) : ℕ :=
  ((ncb_allStr r).filter (fun u => p (x ++ u))).length

/-- The counting bet (positive = bet on `0`, as in `betGain`) for a "tree count" `a`. -/
private def ncb_bet (a : BitString → ℕ)
    (x : BitString) : ℚ :=
  ((a (x ++ [false]) : ℚ) - (a (x ++ [true]) : ℚ)) /
    ((a (x ++ [false]) : ℚ) + (a (x ++ [true]) : ℚ))

/-- The decidable predicate `k z * B ≤ A * N` (i.e. `k z ≤ (A/B) N`). -/
private def ncb_pred (k : BitString → ℕ) (A B N : ℕ)
    (z : BitString) : Bool :=
  decide (k z * B ≤ A * N)

/-- The end of the block containing position `l`: blocks are `[2^(R t), 2^(R (t+1)))`. -/
private def ncb_N (R l : ℕ) : ℕ :=
  2 ^ (R * ((Nat.size l - 1) / R + 1))

/-- The combined strategy: at a prefix `x` use the counting bet for the set `A_N` of the block end
`N` of the position `|x|`. -/
private def ncb_S (k : BitString → ℕ) (A B R : ℕ)
    (x : BitString) : ℚ :=
  ncb_bet
    (fun y => ncb_cnt
      (ncb_pred k A B
        (ncb_N R x.length))
      (ncb_N R x.length - y.length) y) x

/-- The one-step inequality `2q - 1 ≥ log (2q)` with `q = u / (u + v)`. -/
private lemma ncb_A_ineq (u v : ℕ) (hu : 1 ≤ u) :
    Real.log 2 + Real.log (u : ℝ) - Real.log ((u : ℝ) + v) ≤ ((u : ℝ) - v) / ((u : ℝ) + v) := by
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hv' : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have hu0 : (0 : ℝ) < u := by linarith
  have hs0 : (0 : ℝ) < (u : ℝ) + v := by linarith
  have h2u : (0 : ℝ) < 2 * (u : ℝ) := by linarith
  have h1 : Real.log (2 * (u : ℝ) / ((u : ℝ) + v)) ≤ 2 * (u : ℝ) / ((u : ℝ) + v) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos h2u hs0)
  have h2 : Real.log (2 * (u : ℝ) / ((u : ℝ) + v)) =
      Real.log 2 + Real.log (u : ℝ) - Real.log ((u : ℝ) + v) := by
    rw [Real.log_div h2u.ne' hs0.ne', Real.log_mul (by norm_num) hu0.ne']
  have h3 : 2 * (u : ℝ) / ((u : ℝ) + v) - 1 = ((u : ℝ) - v) / ((u : ℝ) + v) := by
    field_simp
    ring
  linarith

/-- One step of the counting bet: the gain dominates the change of the information potential. -/
private lemma ncb_A_step (a : BitString → ℕ) (x : BitString)
    (b : Bool)
    (hadd : a x = a (x ++ [false]) + a (x ++ [true])) (hb : 1 ≤ a (x ++ [b])) :
    Real.log 2 + Real.log (a (x ++ [b]) : ℝ) - Real.log (a x : ℝ) ≤
      (ncb_bet a x : ℝ) * (if b then -1 else 1) := by
  have hx : (a x : ℝ) = (a (x ++ [false]) : ℝ) + (a (x ++ [true]) : ℝ) := by
    exact_mod_cast hadd
  unfold ncb_bet
  push_cast
  rw [hx]
  cases b
  · have := ncb_A_ineq (a (x ++ [false])) (a (x ++ [true]))
      hb
    simpa using this
  · have := ncb_A_ineq (a (x ++ [true])) (a (x ++ [false]))
      hb
    rw [add_comm (a (x ++ [true]) : ℝ) (a (x ++ [false]) : ℝ)] at this
    have h4 : -(((a (x ++ [false]) : ℝ) - (a (x ++ [true]) : ℝ)) /
        ((a (x ++ [false]) : ℝ) + (a (x ++ [true]) : ℝ))) =
        ((a (x ++ [true]) : ℝ) - (a (x ++ [false]) : ℝ)) /
          ((a (x ++ [false]) : ℝ) + (a (x ++ [true]) : ℝ)) := by
      rw [← neg_div]; congr 1; ring
    simpa [h4] using this

/-- The counting bet takes values in `[-1, 1]`. -/
private lemma ncb_abs_bet_le_one (a : BitString → ℕ)
    (x : BitString) : |ncb_bet a x| ≤ 1 := by
  unfold ncb_bet
  have hp0 : (0 : ℚ) ≤ (a (x ++ [false]) : ℚ) := Nat.cast_nonneg _
  have hq0 : (0 : ℚ) ≤ (a (x ++ [true]) : ℚ) := Nat.cast_nonneg _
  by_cases hs : (a (x ++ [false]) : ℚ) + (a (x ++ [true]) : ℚ) = 0
  · rw [hs, div_zero]; simp
  · have hpos : (0 : ℚ) < (a (x ++ [false]) : ℚ) + (a (x ++ [true]) : ℚ) :=
      lt_of_le_of_ne (add_nonneg hp0 hq0) (Ne.symm hs)
    rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
    constructor <;> linarith

/-- **The Lemma of SUV p. 294, for the counting bet.**  If `a` counts the elements of a set of
`n`-bit strings below each prefix (so `a x = a (x ++ [false]) + a (x ++ [true])` below length `n`)
and the first `n` bits of `w` have a positive count, then the counting bet gains on the segment
`[j, n)` at least `(n - j) log 2 - log (a [])`: the sum of the gain and `log 2` times the
information never decreases. -/
private lemma ncb_segment_gain (a : BitString → ℕ) (n : ℕ)
    (hadd : ∀ x : BitString, x.length < n → a x = a (x ++ [false]) + a (x ++ [true]))
    (w : CantorSeq) (hw : 1 ≤ a (cantorPrefix w n)) (j : ℕ) (hj : j ≤ n) :
    ((n : ℝ) - j) * Real.log 2 - Real.log (a []) ≤
      ∑ i ∈ Finset.Ico j n, (ncb_bet a (cantorPrefix w i) :
          ℝ) * (if w i then -1 else 1) := by
  -- the count along the prefixes of `w` is non-increasing up to `n`
  have hstepmono : ∀ i < n, a (cantorPrefix w (i + 1)) ≤ a (cantorPrefix w i) := by
    intro i hi
    have hh := hadd (cantorPrefix w i) (by simpa using hi)
    rw [cantorPrefix_succ]
    cases w i <;> omega
  have hanti : ∀ i j : ℕ, i ≤ j → j ≤ n → a (cantorPrefix w j) ≤ a (cantorPrefix w i) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hj
      exact le_trans (hstepmono j (by omega)) (ih (by omega))
  have hpos : ∀ i ≤ n, 1 ≤ a (cantorPrefix w i) := fun i hi =>
    le_trans hw (hanti i n hi le_rfl)
  have hle0 : ∀ i ≤ n, a (cantorPrefix w i) ≤ a [] := by
    intro i hi
    have := hanti 0 i (Nat.zero_le _) hi
    simpa [cantorPrefix] using this
  have hstep : ∀ i < n, Real.log 2 + Real.log (a (cantorPrefix w (i + 1)) : ℝ) -
      Real.log (a (cantorPrefix w i) : ℝ) ≤
        (ncb_bet a (cantorPrefix w i) : ℝ) *
            (if w i then -1 else 1) := by
    intro i hi
    have h1 : 1 ≤ a (cantorPrefix w i ++ [w i]) := by
      rw [← cantorPrefix_succ]; exact hpos (i + 1) hi
    have := ncb_A_step a (cantorPrefix w i) (w i)
        (hadd _ (by simpa using hi)) h1
    rwa [← cantorPrefix_succ] at this
  -- telescoping
  have htel : ∀ d j : ℕ, j + d = n →
      (d : ℝ) * Real.log 2 - Real.log (a (cantorPrefix w j) : ℝ) +
          Real.log (a (cantorPrefix w n) : ℝ) ≤
        ∑ i ∈ Finset.Ico j n, (ncb_bet a (cantorPrefix w i)
            : ℝ) * (if w i then -1 else 1) := by
    intro d
    induction d with
    | zero =>
      intro j hj0
      have : j = n := by omega
      subst this
      simp
    | succ d ih =>
      intro j hj0
      have hjn : j < n := by omega
      rw [Finset.sum_eq_sum_Ico_succ_bot hjn]
      have h1 := ih (j + 1) (by omega)
      have h2 := hstep j hjn
      push_cast
      linarith
  have h1 := htel (n - j) j (by omega)
  have hnj : ((n - j : ℕ) : ℝ) = (n : ℝ) - j := by
    rw [Nat.cast_sub hj]
  rw [hnj] at h1
  have hlog_n : 0 ≤ Real.log (a (cantorPrefix w n) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hw)
  have hlog_j : Real.log (a (cantorPrefix w j) : ℝ) ≤ Real.log (a [] : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hpos j hj
    · exact_mod_cast hle0 j hj
  linarith
/-- The count of the accepted extensions of `x` of length `r + 1` is the sum of the counts for the
two one-bit extensions of `x`. -/
private lemma ncb_cnt_add (p : BitString → Bool) (r : ℕ)
    (x : BitString) :
    ncb_cnt p (r + 1) x =
        ncb_cnt p r (x ++ [false]) +
        ncb_cnt p r (x ++ [true]) := by
  have h : ∀ b : Bool, ((fun u : BitString => p (x ++ u)) ∘ List.cons b) =
      fun v : BitString => p ((x ++ [b]) ++ v) := by
    intro b
    funext v
    simp [Function.comp]
  unfold ncb_cnt
  rw [ncb_allStr, List.filter_append, List.length_append,
      List.filter_map, List.filter_map,
    List.length_map, List.length_map, h false, h true]

/-- With no bits left to add, the count is `1` if `x` is accepted and `0` otherwise. -/
private lemma ncb_cnt_zero (p : BitString → Bool)
    (x : BitString) :
    ncb_cnt p 0 x = if p x = true then 1 else 0 := by
  unfold ncb_cnt
  simp only [ncb_allStr]
  cases h : p x <;> simp [h]

/-- The tree count `x ↦ cnt p (N - |x|) x` is additive below length `N`. -/
private lemma ncb_tree_add (p : BitString → Bool) (N : ℕ)
    (x : BitString) (hx : x.length < N) :
    ncb_cnt p (N - x.length) x =
      ncb_cnt p (N - (x ++ [false]).length) (x ++ [false]) +
        ncb_cnt p (N - (x ++ [true]).length) (x ++ [true])
            := by
  obtain ⟨r, hr⟩ : ∃ r, N - x.length = r + 1 := ⟨N - x.length - 1, by omega⟩
  have h1 : N - (x ++ [false]).length = r := by
    simp only [List.length_append, List.length_singleton]; omega
  have h2 : N - (x ++ [true]).length = r := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hr, h1, h2]
  exact ncb_cnt_add p r x

/-- At length `N` the tree count of an accepted string is positive. -/
private lemma ncb_tree_leaf (p : BitString → Bool) (N : ℕ)
    (x : BitString)
    (hx : x.length = N) (hp : p x = true) : 1 ≤ ncb_cnt p
        (N - x.length) x := by
  have h0 : N - x.length = 0 := by omega
  rw [h0, ncb_cnt_zero]
  simp [hp]

/-- The list of all bit strings of length `r` has no repetitions. -/
private lemma ncb_B_allStr_nodup (r : ℕ) :
    (ncb_allStr r).Nodup := by
  induction r with
  | zero => simp [ncb_allStr]
  | succ r ih =>
    rw [ncb_allStr, List.nodup_append]
    refine ⟨List.Nodup.map List.cons_injective ih, List.Nodup.map List.cons_injective ih, ?_⟩
    intro a ha b hb hab
    rw [List.mem_map] at ha hb
    obtain ⟨u, _, rfl⟩ := ha
    obtain ⟨v, _, rfl⟩ := hb
    simp at hab

/-- The number of accepted strings of length `N` is at most `2 ^ m` when all accepted strings have
plain complexity below `m` (the counting bound for strings of small complexity). -/
private lemma ncb_cnt_root_le (V : Map)
    (hV : isOptimalConditional V) (p : BitString → Bool)
    (m : ℕ) (hp : ∀ z, p z = true → plainK V z < (m : ℕ∞)) (N : ℕ) :
    ncb_cnt p N [] ≤ 2 ^ m := by
  obtain ⟨_, hS⟩ := isEnumerableFamily_complexityBelow_and_card_lt_two_pow V hV
  obtain ⟨hfin, hcard⟩ := hS m
  have hnd : ((ncb_allStr N).filter
      (fun u => p ([] ++ u))).Nodup :=
    (ncb_B_allStr_nodup N).filter _
  have hsub : (((ncb_allStr N).filter
      (fun u => p ([] ++ u))).toFinset : Set BitString) ⊆
      {z : BitString | plainK V z < (m : ℕ∞)} := by
    intro z hz
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.nil_append] at hz
    exact hp z hz.2
  have h1 : ((ncb_allStr N).filter
      (fun u => p ([] ++ u))).length =
      ((ncb_allStr N).filter (fun u =>
        p ([] ++ u))).toFinset.card :=
    (List.toFinset_card_of_nodup hnd).symm
  have h2 : (((ncb_allStr N).filter
      (fun u => p ([] ++ u))).toFinset : Set BitString).ncard =
      ((ncb_allStr N).filter (fun u =>
        p ([] ++ u))).toFinset.card := Set.ncard_coe_finset _
  have h3 : (((ncb_allStr N).filter
      (fun u => p ([] ++ u))).toFinset : Set BitString).ncard ≤
      {z : BitString | plainK V z < (m : ℕ∞)}.ncard :=
    Set.ncard_le_ncard hsub hfin
  change ((ncb_allStr N).filter
      (fun u => p ([] ++ u))).length ≤ 2 ^ m
  omega
/-- `ncb_allStr` as a `Nat.rec` recursion with a constant
motive. -/
private lemma ncb_C_allStr_eq_rec :
    ncb_allStr = fun r :
        ℕ => Nat.rec (motive := fun _ => List BitString) [[]]
      (fun _ ih => ih.map (List.cons false) ++ ih.map (List.cons true)) r := by
  funext r
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [ncb_allStr, ih]

/-- The list of all bit strings of a given length is computable. -/
private lemma ncb_C_computable_allStr : Computable
    ncb_allStr := by
  rw [ncb_C_allStr_eq_rec]
  have hmap : ∀ b : Bool,
      Primrec₂ (fun (_ : ℕ) (ih : List BitString) => ih.map (List.cons b)) := by
    intro b
    exact Primrec.list_map Primrec.snd
      (Primrec.list_cons.comp (Primrec.const b) Primrec.snd).to₂
  exact (Primrec.nat_rec₁ (f := fun (_ : ℕ) (ih : List BitString) =>
    ih.map (List.cons false) ++ ih.map (List.cons true)) [[]]
    (Primrec.list_append.comp (hmap false) (hmap true))).to_comp

/-- The block end function is computable. -/
private lemma ncb_C_computable_N (R : ℕ) : Computable
    (ncb_N R) := by
  have hsize : Computable (fun l : ℕ => Nat.size l) := computable_nat_size
  have h1 : Computable (fun l : ℕ => Nat.size l - 1) :=
    Computable₂.comp Primrec.nat_sub.to_comp hsize (Computable.const 1)
  have h2 : Computable (fun l : ℕ => (Nat.size l - 1) / R + 1) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable₂.comp Primrec.nat_div.to_comp h1 (Computable.const R)) (Computable.const 1)
  have h3 : Computable (fun l : ℕ => R * ((Nat.size l - 1) / R + 1)) :=
    Computable₂.comp Primrec.nat_mul.to_comp (Computable.const R) h2
  have h4 : Computable (fun l : ℕ => 2 ^ (R * ((Nat.size l - 1) / R + 1))) :=
    Computable₂.comp (f := fun a b : ℕ => a ^ b) nat_pow_primrec₂.to_comp (Computable.const 2)
      h3
  exact h4

/-- The count of the extensions of `x ++ [b]` which are accepted by the predicate of the block
containing `x.length`. -/
private def ncb_C_c (k : BitString → ℕ) (A B R : ℕ)
    (b : Bool) (x : BitString) : ℕ :=
  ncb_cnt (ncb_pred k A B (ncb_N R x.length)) (ncb_N R x.length - (x ++ [b]).length)
    (x ++ [b])

/-- The count as a left fold. -/
private lemma ncb_C_cnt_eq_foldl (p : BitString → Bool)
    (r : ℕ) (x : BitString) :
    ncb_cnt p r x =
      (ncb_allStr r).foldl (fun s u =>
        s + (bif p (x ++ u) then 1 else 0)) 0 := by
  have key : ∀ (L : List BitString) (s : ℕ),
      L.foldl (fun s u => s + (bif p (x ++ u) then 1 else 0)) s =
        s + (L.filter (fun u => p (x ++ u))).length := by
    intro L
    induction L with
    | nil => intro s; simp
    | cons u L ih =>
      intro s
      simp only [List.foldl_cons, List.filter_cons]
      cases h : p (x ++ u) with
      | false =>
        simp only [Bool.cond_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
        exact ih s
      | true =>
        simp only [Bool.cond_true, ↓reduceIte, List.length_cons]
        rw [ih (s + 1)]
        omega
  rw [key]
  simp [ncb_cnt]

/-- The count `ncb_C_c` is computable. -/
private lemma ncb_C_computable_c {k : BitString → ℕ}
    (hk : Computable k) (A B R : ℕ)
    (b : Bool) : Computable (ncb_C_c k A B R b) := by
  have hN : Computable (fun x : BitString => ncb_N R
                                               x.length) :=
    (ncb_C_computable_N R).comp Primrec.list_length.to_comp
  have happ : Computable (fun x : BitString => x ++ [b]) :=
    Computable₂.comp Computable.list_append Computable.id (Computable.const [b])
  have hl : Computable (fun x : BitString =>
      ncb_allStr (ncb_N R x.length - (x ++ [b]).length)) := by
    refine ncb_C_computable_allStr.comp ?_
    exact Computable₂.comp Primrec.nat_sub.to_comp hN (Primrec.list_length.to_comp.comp happ)
  have hg : Computable (fun _ : BitString => (0 : ℕ)) := Computable.const 0
  have hz : Computable (fun q : BitString × (ℕ × BitString) => (q.1 ++ [b]) ++ q.2.2) :=
    Computable₂.comp Computable.list_append
      (Computable₂.comp Computable.list_append Computable.fst (Computable.const [b]))
      (Computable.snd.comp Computable.snd)
  have hlhs : Computable (fun q : BitString × (ℕ × BitString) =>
      k ((q.1 ++ [b]) ++ q.2.2) * B) :=
    Computable₂.comp Primrec.nat_mul.to_comp (hk.comp hz) (Computable.const B)
  have hrhs : Computable (fun q : BitString × (ℕ × BitString) =>
      A * ncb_N R q.1.length) :=
    Computable₂.comp Primrec.nat_mul.to_comp (Computable.const A) (hN.comp Computable.fst)
  have hdec : Computable (fun q : BitString × (ℕ × BitString) =>
      decide (k ((q.1 ++ [b]) ++ q.2.2) * B ≤ A * ncb_N R
          q.1.length)) :=
    Computable₂.comp Primrec.nat_le.decide.to_comp hlhs hrhs
  have hcond : Computable (fun q : BitString × (ℕ × BitString) =>
      bif decide (k ((q.1 ++ [b]) ++ q.2.2) * B ≤ A * ncb_N
          R q.1.length) then 1 else 0) :=
    Computable.cond hdec (Computable.const 1) (Computable.const 0)
  have hh : Computable₂ (fun (x : BitString) (q : ℕ × BitString) =>
      q.1 + (bif decide (k ((x ++ [b]) ++ q.2) * B ≤ A *
          ncb_N R x.length) then 1 else 0)) :=
    Computable₂.comp Primrec.nat_add.to_comp (Computable.fst.comp Computable.snd) hcond
  have hfold := Computable.list_foldl hl hg hh
  refine hfold.of_eq (fun x => ?_)
  unfold ncb_C_c
  rw [ncb_C_cnt_eq_foldl]
  rfl

/-- The combined blockwise counting strategy is computable, as `k` is. -/
private lemma ncb_computable_S {k : BitString → ℕ}
    (hk : Computable k) (A B R : ℕ) :
    Computable (ncb_S k A B R) := by
  have h0 := ncb_C_computable_c hk A B R false
  have h1 := ncb_C_computable_c hk A B R true
  have hNum : Computable (fun x : BitString =>
      (ncb_C_c k A B R false x : ℤ) -
          (ncb_C_c k A B R true x : ℤ)) :=
    Computable₂.comp (f := fun a b : ℕ => (a : ℤ) - (b : ℤ)) primrec_intSubNat.to_comp h0 h1
  have hSum : Computable (fun x : BitString =>
      ncb_C_c k A B R false x +
          ncb_C_c k A B R true x) :=
    Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp h0 h1
  have hDen : Computable (fun x : BitString =>
      max (ncb_C_c k A B R false x +
          ncb_C_c k A B R true x) 1) :=
    Computable₂.comp (f := fun a b : ℕ => max a b) Primrec.nat_max.to_comp hSum
      (Computable.const 1)
  refine computable_of_num_den
    (N := fun x => (ncb_C_c k A B R false x : ℤ) -
                     (ncb_C_c k A B R true x : ℤ))
    (D := fun x => max (ncb_C_c k A B R false x +
                     ncb_C_c k A B R true x) 1)
    hNum hDen ?_ ?_
  · intro x
    exact lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  · intro x
    have hS : ncb_S k A B R x =
        ((ncb_C_c k A B R false x : ℚ) -
            (ncb_C_c k A B R true x : ℚ)) /
          ((ncb_C_c k A B R false x : ℚ) +
              (ncb_C_c k A B R true x : ℚ)) := rfl
    rw [hS]
    by_cases hz : ncb_C_c k A B R false x +
        ncb_C_c k A B R true x = 0
    · have h0z : ncb_C_c k A B R false x = 0 := by omega
      have h1z : ncb_C_c k A B R true x = 0 := by omega
      simp [h0z, h1z]
    · have hm : max (ncb_C_c k A B R false x +
        ncb_C_c k A B R true x) 1 =
          ncb_C_c k A B R false x +
              ncb_C_c k A B R true x := by
        apply max_eq_left
        omega
      rw [hm]
      push_cast
      rfl
/-- Every position of the block `[2^(R t), 2^(R (t+1)))` has the block end `2^(R (t+1))`. -/
private lemma ncb_N_eq_of_mem (R t l : ℕ)
    (h1 : 2 ^ (R * t) ≤ l)
    (h2 : l < 2 ^ (R * (t + 1))) : ncb_N R l =
        2 ^ (R * (t + 1)) := by
  have hl1 : R * t < Nat.size l := Nat.lt_size.mpr h1
  have hl2 : Nat.size l ≤ R * (t + 1) := Nat.size_le.mpr h2
  have hc1 : t * R = R * t := Nat.mul_comm t R
  have hc2 : (t + 1) * R = R * (t + 1) := Nat.mul_comm (t + 1) R
  have hdiv : (Nat.size l - 1) / R = t := by
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  unfold ncb_N
  rw [hdiv]

/-- On a block, the strategy `ncb_S` is the counting bet for
the tree count of the block end. -/
private lemma ncb_D1_S_eq (k : BitString → ℕ) (A B R n : ℕ)
    (x : BitString)
    (hN : ncb_N R x.length = n) :
    ncb_S k A B R x =
      ncb_bet (fun y => ncb_cnt (ncb_pred k A B n) (n - y.length) y) x := by
  unfold ncb_S
  rw [hN]

/-- The strategy `ncb_S` has values in `[-1, 1]`. -/
private lemma ncb_D1_abs_S_le (k : BitString → ℕ)
    (A B R : ℕ) (x : BitString) :
    |(ncb_S k A B R x : ℝ)| ≤ 1 := by
  have h := ncb_abs_bet_le_one
    (fun y => ncb_cnt
                (ncb_pred k A B
                (ncb_N R x.length))
                (ncb_N R x.length - y.length) y) x
  have h2 : ((|ncb_S k A B R x| : ℚ) : ℝ) ≤ 1 := by
    unfold ncb_S
    exact_mod_cast h
  simpa using h2

/-- The gain on the first `m` steps is at least `-m`. -/
private lemma ncb_D1_first_part (k : BitString → ℕ)
    (A B R : ℕ) (w : CantorSeq) (m : ℕ) :
    -(m : ℝ) ≤ ∑ i ∈ Finset.range m,
      (ncb_S k A B R (cantorPrefix w i) : ℝ) *
          (if w i then -1 else 1) := by
  have h : ∀ i ∈ Finset.range m,
      (-1 : ℝ) ≤ (ncb_S k A B R (cantorPrefix w i) : ℝ) *
          (if w i then -1 else 1) := by
    intro i _
    have h1 := ncb_D1_abs_S_le k A B R (cantorPrefix w i)
    rw [abs_le] at h1
    split_ifs <;> linarith [h1.1, h1.2]
  calc -(m : ℝ) = ∑ i ∈ Finset.range m, (-1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum h

/-- The estimate for a block `[m, n)` on which the block end is `n`. -/
private lemma ncb_D1_block_core (V : Map)
    (hV : isOptimalConditional V) {k : BitString → ℕ}
    (c : ℕ) (hbound : ∀ x, plainK V x ≤ ((k x + c : ℕ) : ℕ∞)) (A B R : ℕ) (hB : 0 < B)
    (w : CantorSeq) (n m : ℕ) (hmn : m ≤ n)
    (hblock : ∀ l, m ≤ l → l < n → ncb_N R l = n)
    (hw : k (cantorPrefix w n) * B ≤ A * n) :
    -(m : ℝ) + ((n : ℝ) - m) * Real.log 2 - (((A * n / B : ℕ) : ℝ) + c + 1) * Real.log 2 ≤
      betGain (ncb_S k A B R) w n := by
  set p : BitString → Bool := ncb_pred k A B n with hp_def
  set a : BitString → ℕ := fun y => ncb_cnt p (n - y.length)
                                      y with ha_def
  have hadd : ∀ x : BitString, x.length < n → a x = a (x ++ [false]) + a (x ++ [true]) :=
    fun x hx => ncb_tree_add p n x hx
  have hpn : p (cantorPrefix w n) = true := by
    simp [hp_def, ncb_pred, hw]
  have hw1 : 1 ≤ a (cantorPrefix w n) :=
    ncb_tree_leaf p n (cantorPrefix w n)
        (cantorPrefix_length w n) hpn
  have hseg := ncb_segment_gain a n hadd w hw1 m hmn
  have hsum : ∑ i ∈ Finset.Ico m n,
      (ncb_S k A B R (cantorPrefix w i) : ℝ) *
          (if w i then -1 else 1) =
      ∑ i ∈ Finset.Ico m n, (ncb_bet a (cantorPrefix w i) :
          ℝ) * (if w i then -1 else 1) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    have hN : ncb_N R (cantorPrefix w i).length = n := by
      rw [cantorPrefix_length]
      exact hblock i hi.1 hi.2
    rw [ncb_D1_S_eq k A B R n _ hN]
  have hroot : a [] ≤ 2 ^ (A * n / B + c + 1) := by
    have h0 : a [] = ncb_cnt p n [] := by simp [ha_def]
    rw [h0]
    refine ncb_cnt_root_le V hV p (A * n / B + c + 1) ?_ n
    intro z hz
    have hz' : k z * B ≤ A * n := by simpa [hp_def,
                                       ncb_pred] using hz
    have hkz : k z ≤ A * n / B := (Nat.le_div_iff_mul_le hB).mpr hz'
    calc plainK V z ≤ ((k z + c : ℕ) : ℕ∞) := hbound z
      _ < ((A * n / B + c + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (a [] : ℝ) ≤ (((A * n / B : ℕ) : ℝ) + c + 1) * Real.log 2 := by
    rcases Nat.eq_zero_or_pos (a []) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      positivity
    · have hle : (a [] : ℝ) ≤ 2 ^ (A * n / B + c + 1) := by exact_mod_cast hroot
      calc Real.log (a [] : ℝ) ≤ Real.log (2 ^ (A * n / B + c + 1)) :=
            Real.log_le_log (by exact_mod_cast hpos) hle
        _ = ((A * n / B + c + 1 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
        _ = _ := by push_cast; ring
  have hsplit : betGain (ncb_S k A B R) w n =
      ∑ i ∈ Finset.range m, (ncb_S k A B R
          (cantorPrefix w i) : ℝ) * (if w i then -1 else 1) +
      ∑ i ∈ Finset.Ico m n,
        (ncb_S k A B R (cantorPrefix w i) : ℝ) *
            (if w i then -1 else 1) := by
    unfold betGain
    rw [Finset.sum_range_add_sum_Ico _ hmn]
  have hfirst := ncb_D1_first_part k A B R w m
  rw [hsplit, hsum]
  linarith

/-- The gain of the combined strategy after `2^(R (t+1))` steps, when the prefix of that length is
among the strings of small `k`: the earlier blocks lose at most `2^(R t)`, the last block gains
`(n - 2^(R t)) log 2` minus the logarithm of the number of candidates. -/
private lemma ncb_block_estimate (V : Map)
    (hV : isOptimalConditional V) {k : BitString → ℕ}
    (c : ℕ) (hbound : ∀ x, plainK V x ≤ ((k x + c : ℕ) : ℕ∞)) (A B R : ℕ) (hB : 0 < B)
    (w : CantorSeq) (t : ℕ)
    (hw : k (cantorPrefix w (2 ^ (R * (t + 1)))) * B ≤ A * 2 ^ (R * (t + 1))) :
    -((2 : ℝ) ^ (R * t)) + (((2 : ℝ) ^ (R * (t + 1))) - (2 : ℝ) ^ (R * t)) * Real.log 2 -
        (((A * 2 ^ (R * (t + 1)) / B : ℕ) : ℝ) + c + 1) * Real.log 2 ≤
      betGain (ncb_S k A B R) w (2 ^ (R * (t + 1))) := by
  have hmn : 2 ^ (R * t) ≤ 2 ^ (R * (t + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t))
  have key := ncb_D1_block_core V hV c hbound A B R hB w
      (2 ^ (R * (t + 1))) (2 ^ (R * t)) hmn
    (fun l hl1 hl2 => ncb_N_eq_of_mem R t l hl1 hl2) hw
  push_cast at key
  exact key
/-- For a block ratio `2^R` large enough, the combined strategy has gain at least `ε n` for
infinitely many `n`, with `ε = (1 - A/B) log 2 / 4`. -/
private lemma ncb_final_estimate (V : Map)
    (hV : isOptimalConditional V) {k : BitString → ℕ}
    (c : ℕ) (hbound : ∀ x, plainK V x ≤ ((k x + c : ℕ) : ℕ∞)) (A B R : ℕ) (hB : 0 < B)
    (hAB : A < B) (hR : 2 * (1 + Real.log 2) ≤ 2 ^ R * ((1 - (A : ℝ) / B) * Real.log 2))
    (w : CantorSeq) (hw : ∀ᶠ n : ℕ in atTop, k (cantorPrefix w n) * B ≤ A * n) :
    ∃ᶠ n : ℕ in atTop, ((1 - (A : ℝ) / B) * Real.log 2 / 4) * n ≤
      betGain (ncb_S k A B R) w n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hq1 : (A : ℝ) / B < 1 := by
    rw [div_lt_one hBr]; exact_mod_cast hAB
  have hq0 : (0 : ℝ) ≤ (A : ℝ) / B := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (1 - (A : ℝ) / B) * Real.log 2 := ⟨_, rfl⟩
  rw [← hδ] at hR ⊢
  have hδpos : 0 < δ := by rw [hδ]; exact mul_pos (by linarith) hlog
  have hδle : δ ≤ Real.log 2 := by rw [hδ]; nlinarith
  have hRpos : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_mul] at hR
      linarith
    · exact h0
  rw [Filter.frequently_atTop]
  intro N0
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hw
  obtain ⟨T, hT⟩ := exists_nat_ge (4 * ((c : ℝ) + 1) * Real.log 2 / δ)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = max (max N0 N1) T := ⟨_, rfl⟩
  have ht0 : N0 ≤ t := ht ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have ht1 : N1 ≤ t := ht ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have htT : (T : ℝ) ≤ (t : ℝ) := by
    have : T ≤ t := ht ▸ le_max_right _ _
    exact_mod_cast this
  -- the block end `2 ^ (R * (t + 1))` is large
  have hn1 : t + 1 ≤ 2 ^ (R * (t + 1)) := by
    calc t + 1 ≤ 2 ^ (t + 1) := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ (R * (t + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [hRpos])
  refine ⟨2 ^ (R * (t + 1)), by omega, ?_⟩
  have hwn : k (cantorPrefix w (2 ^ (R * (t + 1)))) * B ≤ A * 2 ^ (R * (t + 1)) :=
    hN1 _ (by omega)
  have hblock := ncb_block_estimate V hV c hbound A B R hB
      w t hwn
  -- real arithmetic
  have hY : (2 : ℝ) ^ (R * (t + 1)) = (2 : ℝ) ^ (R * t) * (2 : ℝ) ^ R := by
    rw [← pow_add, mul_add, mul_one]
  have hXpos : 0 ≤ (2 : ℝ) ^ (R * t) := by positivity
  have hm : (((A * 2 ^ (R * (t + 1)) / B : ℕ) : ℝ)) ≤
      (A : ℝ) / B * (2 : ℝ) ^ (R * (t + 1)) := by
    have h := Nat.cast_div_le (α := ℝ) (m := A * 2 ^ (R * (t + 1))) (n := B)
    push_cast at h
    calc _ ≤ _ := h
      _ = _ := by ring
  have hmL := mul_le_mul_of_nonneg_right hm hlog.le
  have h1 : (2 : ℝ) ^ (R * t) * (2 * (1 + Real.log 2)) ≤
      (2 : ℝ) ^ (R * t) * ((2 : ℝ) ^ R * δ) :=
    mul_le_mul_of_nonneg_left hR hXpos
  have hXPδ : (2 : ℝ) ^ (R * t) * ((2 : ℝ) ^ R * δ) = (2 : ℝ) ^ (R * (t + 1)) * δ := by
    rw [hY]; ring
  have hnR : (4 * ((c : ℝ) + 1) * Real.log 2 / δ) ≤ (2 : ℝ) ^ (R * (t + 1)) := by
    have h : ((t + 1 : ℕ) : ℝ) ≤ ((2 ^ (R * (t + 1)) : ℕ) : ℝ) := by exact_mod_cast hn1
    push_cast at h
    linarith
  have h2 : 4 * ((c : ℝ) + 1) * Real.log 2 ≤ (2 : ℝ) ^ (R * (t + 1)) * δ := by
    rwa [div_le_iff₀ hδpos] at hnR
  have hYδ : (2 : ℝ) ^ (R * (t + 1)) * δ = (2 : ℝ) ^ (R * (t + 1)) * Real.log 2 -
      (A : ℝ) / B * (2 : ℝ) ^ (R * (t + 1)) * Real.log 2 := by
    rw [hδ]; ring
  have hcast : (((2 ^ (R * (t + 1)) : ℕ)) : ℝ) = (2 : ℝ) ^ (R * (t + 1)) := by norm_num
  rw [hcast]
  linarith [hblock, hmL, h1, h2, hYδ, hXPδ]

/-- **SUV Theorem 194, p. 295.**  Let `k` be a computable upper bound for `C`, up to the usual
additive constant, with `k(ω_0 … ω_{n-1}) ≤ αn` for some `α < 1` and all sufficiently large `n`.
Then `ω` is not Mises-Church random: for a *computable* bound, monotone rules are enough. -/
theorem not_isMisesChurchRandom_of_computable_bound (V : Map) (hV : isOptimalConditional V)
    {k : BitString → ℕ} (hk : Computable k)
    (hbound : ∃ c : ℕ, ∀ x, plainK V x ≤ ((k x + c : ℕ) : ℕ∞)) {α : ℝ} (hα : α < 1)
    {w : CantorSeq} (hle : ∀ᶠ n : ℕ in atTop, (k (cantorPrefix w n) : ℝ) ≤ α * n) :
    ¬ IsMisesChurchRandom w := by
  intro hw
  obtain ⟨c, hc⟩ := hbound
  -- a rational `A / B` with `α ≤ A / B < 1`
  obtain ⟨A, B, hB, hAB, hαA⟩ : ∃ A B : ℕ, 0 < B ∧ A < B ∧ α ≤ (A : ℝ) / B := by
    have hα' : max α 0 < 1 := max_lt hα one_pos
    have hδ : 0 < 1 - max α 0 := by linarith
    obtain ⟨B, hB⟩ := exists_nat_gt (1 / (1 - max α 0))
    have hBpos : (0 : ℝ) < B := lt_trans (by positivity) hB
    have hδB : 1 < (1 - max α 0) * B := by
      have := (div_lt_iff₀ hδ).mp hB
      linarith
    have h0 : 0 ≤ max α 0 * B := mul_nonneg (le_max_right _ _) hBpos.le
    refine ⟨⌈max α 0 * B⌉₊, B, by exact_mod_cast hBpos, ?_, ?_⟩
    · have h1 : (⌈max α 0 * B⌉₊ : ℝ) < max α 0 * B + 1 := Nat.ceil_lt_add_one h0
      have h2 : (⌈max α 0 * B⌉₊ : ℝ) < B := by nlinarith
      exact_mod_cast h2
    · rw [le_div_iff₀ hBpos]
      calc α * B ≤ max α 0 * B := mul_le_mul_of_nonneg_right (le_max_left _ _) hBpos.le
        _ ≤ ⌈max α 0 * B⌉₊ := Nat.le_ceil _
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hw' : ∀ᶠ n : ℕ in atTop, k (cantorPrefix w n) * B ≤ A * n := by
    filter_upwards [hle] with n hn
    have h1 : (k (cantorPrefix w n) : ℝ) ≤ ((A : ℝ) / B) * n :=
      hn.trans (mul_le_mul_of_nonneg_right hαA (Nat.cast_nonneg n))
    have h2 : (k (cantorPrefix w n) : ℝ) * B ≤ A * n := by
      calc (k (cantorPrefix w n) : ℝ) * B ≤ (((A : ℝ) / B) * n) * B :=
            mul_le_mul_of_nonneg_right h1 hBpos.le
        _ = A * n := by field_simp
    exact_mod_cast h2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ' : 0 < (1 - (A : ℝ) / B) * Real.log 2 := by
    have : (A : ℝ) / B < 1 := (div_lt_one hBpos).mpr (by exact_mod_cast hAB)
    exact mul_pos (by linarith) hlog2
  obtain ⟨R, hR⟩ : ∃ R : ℕ, 2 * (1 + Real.log 2) ≤ 2 ^ R * ((1 - (A : ℝ) / B) * Real.log 2) := by
    obtain ⟨R, hR⟩ := pow_unbounded_of_one_lt (2 * (1 + Real.log 2) / ((1 - (A : ℝ) / B) * Real.log
        2))
      (by norm_num : (1 : ℝ) < 2)
    exact ⟨R, ((div_lt_iff₀ hδ').mp hR).le⟩
  have hfreq := ncb_final_estimate V hV c hc A B R hB hAB hR
      w hw'
  have hS := ncb_computable_S hk A B R
  have hSb : ∀ x, |ncb_S k A B R x| ≤ 1 :=
      fun x => ncb_abs_bet_le_one _ x
  have hε : 0 < (1 - (A : ℝ) / B) * Real.log 2 / 4 := by positivity
  have hl : (betGain (ncb_S k A B R) w) =o[atTop]
      (fun n : ℕ => (n : ℝ)) :=
    betGain_isLittleO_of_isMisesChurchRandom hS hSb hw
  set ε : ℝ := (1 - (A : ℝ) / B) * Real.log 2 / 4 with hεdef
  have hb : ∀ᶠ n : ℕ in atTop, |betGain (ncb_S k A B R) w n|
      ≤ (ε / 2) * (n : ℝ) := by
    have h1 := Asymptotics.IsLittleO.bound hl (half_pos hε)
    refine h1.mono (fun n hn => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn
    have hn_pos : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [abs_of_nonneg hn_pos] at hn
    exact hn
  have hb2 : ∀ᶠ n : ℕ in atTop, |betGain (ncb_S k A B R) w
      n| ≤ (ε / 2) * (n : ℝ) ∧ 0 < n :=
    hb.and (eventually_gt_atTop 0)
  rcases (hfreq.and_eventually hb2).exists with ⟨n, hn2, hn1, hnpos⟩
  have h3 : ε * (n : ℝ) ≤ (ε / 2) * (n : ℝ) := calc
    ε * (n : ℝ) ≤ betGain (ncb_S k A B R) w n := hn2
    _ ≤ |betGain (ncb_S k A B R) w n| := le_abs_self _
    _ ≤ (ε / 2) * (n : ℝ) := hn1
  have hn_pos_strict : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have h4 : ε ≤ ε / 2 := (mul_le_mul_iff_of_pos_right hn_pos_strict).mp h3
  linarith

/-- Step 1 of the proof of `exists_isMisesChurchDaleyRandom_not_isMisesKLRandom`: for the
slowly growing function `Nat.size`, the bound `Nat.size n * log₂ n + c` of Theorem 189 is eventually
below `n / 2`. -/
private lemma exists_isMisesChurchDaleyRandom_not_isMisesKLRandom_limit (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, (Nat.size n : ℝ) * Real.logb 2 (n : ℝ) + c < 1 / 2 * (n : ℝ) := by
  have h2 : (fun x : ℝ => (Real.logb 2 x) ^ 2) =o[atTop] (id : ℝ → ℝ) := by
    refine ((Real.isLittleO_pow_log_id_atTop (n := 2)).const_mul_left
      (1 / (Real.log 2) ^ 2)).congr_left ?_
    intro x
    simp only [Real.logb, div_pow]
    ring
  have h1 : (fun x : ℝ => Real.logb 2 x) =o[atTop] (id : ℝ → ℝ) := by
    refine (Real.isLittleO_log_id_atTop.const_mul_left (1 / Real.log 2)).congr_left ?_
    intro x
    simp only [Real.logb]
    ring
  have h0 : (fun _ : ℝ => c) =o[atTop] (id : ℝ → ℝ) := Asymptotics.isLittleO_const_id_atTop c
  have hsum : (fun x : ℝ => (Real.logb 2 x) ^ 2 + Real.logb 2 x + c) =o[atTop] (id : ℝ → ℝ) :=
    (h2.add h1).add h0
  have hev : ∀ᶠ x : ℝ in atTop,
      ‖(Real.logb 2 x) ^ 2 + Real.logb 2 x + c‖ ≤ 1 / 4 * ‖(id x : ℝ)‖ :=
    hsum.def (by norm_num)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  filter_upwards [hnat, Filter.eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hL : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) hn1'
  -- `Nat.size n ≤ log₂ n + 1`
  have hs : (Nat.size n : ℝ) ≤ Real.logb 2 (n : ℝ) + 1 := by
    have hpos : 0 < Nat.size n := Nat.size_pos.mpr (by omega)
    have h3 : Nat.size n - 1 < Nat.size n := by omega
    have h4 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp h3
    have h5 : (2 : ℝ) ^ (Nat.size n - 1) ≤ (n : ℝ) := by exact_mod_cast h4
    have h6 : ((Nat.size n - 1 : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_natCast]
      exact h5
    have h7 : ((Nat.size n - 1 : ℕ) : ℝ) = (Nat.size n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    linarith
  have hab : |(Real.logb 2 (n : ℝ)) ^ 2 + Real.logb 2 (n : ℝ) + c| ≤ 1 / 4 * (n : ℝ) := by
    simpa [abs_of_nonneg, Nat.cast_nonneg] using hn
  have hle := (abs_le.mp hab).2
  nlinarith [mul_le_mul_of_nonneg_right hs hL]

/-- **SUV Theorem 195, p. 296.**  There are Mises-Church-Daley random sequences that are not
Mises-Kolmogorov-Loveland random. -/
theorem exists_isMisesChurchDaleyRandom_not_isMisesKLRandom :
    ∃ w, IsMisesChurchDaleyRandom w ∧ ¬ IsMisesKLRandom w := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  have hf : Computable (fun n : ℕ => Nat.size n) := computable_nat_size
  have hmono : Monotone (fun n : ℕ => Nat.size n) := fun _ _ h => Nat.size_le_size h
  have hunb : ∀ B, ∃ n, B ≤ (fun n : ℕ => Nat.size n) n := fun B =>
    ⟨2 ^ B, by simp only [Nat.size_pow]; omega⟩
  obtain ⟨w, hw, c, hc⟩ := exists_isMisesChurchDaleyRandom_plainK_le hf hmono hunb V hV
  refine ⟨w, hw, not_isMisesKLRandom_of_plainK_lt V hV (α := 1 / 2) (by norm_num) ?_⟩
  filter_upwards [exists_isMisesChurchDaleyRandom_not_isMisesKLRandom_limit c] with n hn
  exact lt_of_le_of_lt (hc n) hn

/-- Step 1 of the proof of `isMisesChurchDaleyRandom_of_output`: The composition of an
admissible rule and a Church-Daley admissible rule is Kolmogorov-Loveland admissible. -/
private def isMisesChurchDaleyRandom_of_output_selStep (s : BitString →. Bool) : Unit →
    BitString × BitString → Bool →. BitString × BitString :=
  fun _ st b => (s st.1).map (fun c => (st.1 ++ [b], cond c (st.2 ++ [b]) st.2))

/-- Step 1 of the proof of `isMisesChurchDaleyRandom_of_output`: The composition of an
admissible rule and a Church-Daley admissible rule is Kolmogorov-Loveland admissible. -/
private def isMisesChurchDaleyRandom_of_output_selPart (s : BitString →. Bool) (x : BitString)
    : Part BitString :=
  (pfoldl (isMisesChurchDaleyRandom_of_output_selStep s) () ([], []) x).map Prod.snd

/-- Step 1 of the proof of `isMisesChurchDaleyRandom_of_output`: The composition of an
admissible rule and a Church-Daley admissible rule is Kolmogorov-Loveland admissible. -/
private def isMisesChurchDaleyRandom_of_output_compRule (ρ : KLRule) (r : BitString →. Bool) :
    KLRule where
  next := ρ.next
  sel := fun x => do
    let t ← isMisesChurchDaleyRandom_of_output_selPart ρ.sel x
    let c ← ρ.sel x
    cond c (r t) (Part.some false)
  noRepeat := ρ.noRepeat

/-- Step 2 of the proof of `isMisesChurchDaleyRandom_of_output`: The composition rule is
admissible. -/
private lemma isMisesChurchDaleyRandom_of_output_compRule_isAdmissible {ρ : KLRule}
    (hρ : ρ.IsAdmissible) {r : BitString →. Bool} (hr : Partrec r) :
  (isMisesChurchDaleyRandom_of_output_compRule ρ r).IsAdmissible := by
  have hF : Partrec (fun a : Unit × (BitString × BitString) × Bool =>
    (ρ.sel a.2.1.1).map (fun c => (a.2.1.1 ++ [a.2.2], cond c (a.2.1.2 ++ [a.2.2]) a.2.1.2))) := by
    apply Partrec.map (hρ.2.comp (Computable.fst.comp (Computable.fst.comp Computable.snd)))
    have hc1 : Computable (fun (a : (Unit × (BitString × BitString) × Bool) × Bool) => a.1.2.1.1) :=
      Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    have hc2 : Computable (fun (a : (Unit × (BitString × BitString) × Bool) × Bool) => [a.1.2.2]) :=
      Computable.list_cons.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
          (Computable.const [])
    have h1 : Computable₂ (fun (a : Unit × (BitString × BitString) × Bool) (c : Bool) =>
      a.2.1.1 ++ [a.2.2]) :=
      Computable.list_append.comp hc1 hc2
    have hc3 : Computable (fun (a : (Unit × (BitString × BitString) × Bool) × Bool) => a.2) :=
      Computable.snd
    have hc4 : Computable (fun (a : (Unit × (BitString × BitString) × Bool) × Bool) =>
      a.1.2.1.2 ++ [a.1.2.2]) :=
      Computable.list_append.comp (Computable.snd.comp (Computable.fst.comp (Computable.snd.comp
          Computable.fst))) hc2
    have hc5 : Computable (fun (a : (Unit × (BitString × BitString) × Bool) × Bool) => a.1.2.1.2) :=
      Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    have h2 : Computable₂ (fun (a : Unit × (BitString × BitString) × Bool) (c : Bool) =>
      cond c (a.2.1.2 ++ [a.2.2]) a.2.1.2) :=
      Computable.cond hc3 hc4 hc5
    exact Computable.pair h1 h2
  have hPfoldl : Partrec (fun x : Unit × (BitString × BitString) × List Bool =>
    pfoldl (isMisesChurchDaleyRandom_of_output_selStep ρ.sel) x.1 x.2.1 x.2.2) := by
    exact partrec_pfoldl hF
  have hSelPart : Partrec (isMisesChurchDaleyRandom_of_output_selPart ρ.sel) := by
    have hc6 : Computable (fun (x : BitString) => ((), (([] : BitString), ([] : BitString)), x)) :=
      Computable.pair (Computable.const ()) (Computable.pair (Computable.const ([], []))
          Computable.id)
    exact Partrec.map (hPfoldl.comp hc6) (Computable.snd.comp Computable.snd)
  constructor
  · exact hρ.1
  · have hbind1 : Partrec (fun x => do let t ← isMisesChurchDaleyRandom_of_output_selPart
                                         ρ.sel x; let c ← ρ.sel x; cond c (r t) (Part.some false))
                                         := by
      apply Partrec.bind hSelPart
      apply Partrec.bind (hρ.2.comp Computable.fst)
      have hpr1 : Partrec (fun (p : (BitString × BitString) × Bool) => r p.1.2) :=
          hr.comp (Computable.snd.comp Computable.fst)
      have hpr2 : Partrec (fun (p : (BitString × BitString) × Bool) => Part.some false) :=
          Computable.partrec (Computable.const false)
      exact Partrec.cond Computable.snd hpr1 hpr2
    exact hbind1

private lemma isMisesChurchDaleyRandom_of_output_pfoldl {s : BitString →. Bool}
    {x : BitString}
    (hd : ∀ y, y <+: x → y ≠ x → (s y).Dom) :
    pfoldl (isMisesChurchDaleyRandom_of_output_selStep s) () ([], []) x = Part.some
        (x, selectedBits (partialRuleSet s) x) := by
  induction x using List.reverseRecOn with
  | nil => simp [selectedBits, selectedAux]
  | append_singleton x b ih =>
    have hne : ∀ y : BitString, y <+: x → y ≠ x → y ≠ x ++ [b] := by
      intro y hy _ h
      have h1 := congrArg List.length h
      have h2 := hy.length_le
      simp at h1
      omega
    have hdx : ∀ y, y <+: x → y ≠ x → (s y).Dom := fun y hy hyx =>
      hd y (hy.trans (List.prefix_append _ _)) (hne y hy hyx)
    have hxd : (s x).Dom := hd x (List.prefix_append _ _) (by
      intro h
      have := congrArg List.length h
      simp at this)
    obtain ⟨c, hc⟩ : ∃ c, c ∈ s x := Part.dom_iff_mem.1 hxd
    have hceq : s x = Part.some c := Part.eq_some_iff.2 hc
    have hR : x ∈ partialRuleSet s ↔ c = true := by
      constructor
      · rintro ⟨_, h⟩
        exact (Part.mem_unique h hc).symm
      · rintro rfl
        refine ⟨?_, hc⟩
        intro y hy
        by_cases hyx : y = x
        · subst hyx; exact hxd
        · exact hdx y hy hyx
    rw [pfoldl_append, ih hdx, Part.bind_some]
    simp only [pfoldl_cons, pfoldl_nil, isMisesChurchDaleyRandom_of_output_selStep, hceq,
      Part.map_some, Part.bind_some]
    classical
    rw [selectedBits_append_singleton]
    cases c
    · have : x ∉ partialRuleSet s := fun h => by simpa using hR.1 h
      simp [this]
    · simp [hR.2 rfl]

private lemma isMisesChurchDaleyRandom_of_output_step3_selPart {s : BitString →. Bool}
    {x : BitString}
    (hd : ∀ y, y <+: x → y ≠ x → (s y).Dom) :
    isMisesChurchDaleyRandom_of_output_selPart s x = Part.some
        (selectedBits (partialRuleSet s) x) := by
  unfold isMisesChurchDaleyRandom_of_output_selPart
  rw [isMisesChurchDaleyRandom_of_output_pfoldl hd]
  simp

private lemma isMisesChurchDaleyRandom_of_output_compRule_sel_of_mem {ρ : KLRule}
    {r : BitString →. Bool} {y : BitString} {c : Bool}
    (hd : ∀ z, z <+: y → (ρ.sel z).Dom) (hc : c ∈ ρ.sel y) :
    (isMisesChurchDaleyRandom_of_output_compRule ρ r).sel y =
        cond c (r (selectedBits (partialRuleSet ρ.sel) y)) (Part.some false) := by
  have hsel := isMisesChurchDaleyRandom_of_output_step3_selPart (s := ρ.sel) (x := y)
    (fun z hz _ => hd z hz)
  change (isMisesChurchDaleyRandom_of_output_selPart ρ.sel y).bind
      (fun t => (ρ.sel y).bind (fun c => cond c (r t) (Part.some false))) = _
  rw [hsel, Part.bind_some, Part.eq_some_iff.2 hc, Part.bind_some]

private lemma isMisesChurchDaleyRandom_of_output_prefix_of_selectedBits (R : Set BitString)
    (x p : BitString)
    (hp : p <+: selectedBits R x) :
    p = selectedBits R x ∨ ∃ z, z <+: x ∧ z ∈ R ∧ selectedBits R z = p := by
  classical
  induction x using List.reverseRecOn generalizing p with
  | nil =>
    left
    have : selectedBits R [] = [] := by simp [selectedBits, selectedAux]
    rw [this] at hp ⊢
    exact List.prefix_nil.1 hp
  | append_singleton x b ih =>
    rw [selectedBits_append_singleton] at hp ⊢
    by_cases hx : x ∈ R
    · rw [ite_eq_left hx] at hp ⊢
      rcases List.prefix_concat_iff.1 hp with h | h
      · exact Or.inl h
      · rcases ih p h with h1 | ⟨z, hz, hzR, hzp⟩
        · exact Or.inr ⟨x, List.prefix_append _ _, hx, h1.symm⟩
        · exact Or.inr ⟨z, hz.trans (List.prefix_append _ _), hzR, hzp⟩
    · rw [ite_eq_right hx] at hp ⊢
      simp only [List.append_nil] at hp ⊢
      rcases ih p hp with h1 | ⟨z, hz, hzR, hzp⟩
      · exact Or.inl h1
      · exact Or.inr ⟨z, hz.trans (List.prefix_append _ _), hzR, hzp⟩

private lemma isMisesChurchDaleyRandom_of_output_mem_compSet_iff (ρ : KLRule)
    (r : BitString →. Bool) (x : BitString) :
    x ∈ partialRuleSet (isMisesChurchDaleyRandom_of_output_compRule ρ r).sel ↔
      x ∈ partialRuleSet ρ.sel ∧ selectedBits (partialRuleSet ρ.sel) x ∈ partialRuleSet r := by
  have aux : ∀ y, ((isMisesChurchDaleyRandom_of_output_compRule ρ r).sel y).Dom →
      (ρ.sel y).Dom := by
    intro y hy
    rw [Part.dom_iff_mem] at hy ⊢
    obtain ⟨v, hv⟩ := hy
    simp only [isMisesChurchDaleyRandom_of_output_compRule, Part.bind_eq_bind,
        Part.mem_bind_iff] at hv
    obtain ⟨t, _, c, hc, _⟩ := hv
    exact ⟨c, hc⟩
  constructor
  · rintro ⟨hdom, htrue⟩
    have hdρ : ∀ y, y <+: x → (ρ.sel y).Dom := fun y hy => aux y (hdom y hy)
    obtain ⟨c, hc⟩ := Part.dom_iff_mem.1 (hdρ x (List.prefix_refl x))
    have hL := isMisesChurchDaleyRandom_of_output_compRule_sel_of_mem (r := r) hdρ hc
    rw [hL] at htrue
    cases c with
    | false => simp at htrue
    | true =>
      simp only [Bool.cond_true] at htrue
      refine ⟨⟨hdρ, hc⟩, ?_, htrue⟩
      intro w hw
      rcases isMisesChurchDaleyRandom_of_output_prefix_of_selectedBits _ x w hw with rfl |
          ⟨z, hz, hzR, rfl⟩
      · exact Part.dom_iff_mem.2 ⟨true, htrue⟩
      · have hdz : ∀ y, y <+: z → (ρ.sel y).Dom := fun y hy => hdρ y (hy.trans hz)
        have hL2 := isMisesChurchDaleyRandom_of_output_compRule_sel_of_mem (r := r) hdz hzR.2
        have hd2 := hdom z hz
        rw [hL2] at hd2
        simpa using hd2
  · rintro ⟨⟨hdρ, htx⟩, hrd, hrt⟩
    have hdC : ∀ y, y <+: x → ((isMisesChurchDaleyRandom_of_output_compRule ρ r).sel y).Dom :=
        by
      intro y hy
      obtain ⟨c, hc⟩ := Part.dom_iff_mem.1 (hdρ y hy)
      have hdy : ∀ z, z <+: y → (ρ.sel z).Dom := fun z hz => hdρ z (hz.trans hy)
      rw [isMisesChurchDaleyRandom_of_output_compRule_sel_of_mem (r := r) hdy hc]
      cases c with
      | false => simp
      | true =>
        simp only [Bool.cond_true]
        exact hrd _ (selectedBits_prefix _ hy)
    refine ⟨hdC, ?_⟩
    rw [isMisesChurchDaleyRandom_of_output_compRule_sel_of_mem (r := r) hdρ htx]
    simpa using hrt

private lemma isMisesChurchDaleyRandom_of_output_selectedBits_comp (ρ : KLRule)
    (r : BitString →. Bool) (x : BitString) :
    selectedBits (partialRuleSet (isMisesChurchDaleyRandom_of_output_compRule ρ r).sel) x =
        selectedBits (partialRuleSet r) (selectedBits (partialRuleSet ρ.sel) x) := by
  classical
  induction x using List.reverseRecOn with
  | nil => simp [selectedBits, selectedAux]
  | append_singleton x b ih =>
    rw [selectedBits_append_singleton, selectedBits_append_singleton, ih]
    have hmem := isMisesChurchDaleyRandom_of_output_mem_compSet_iff ρ r x
    by_cases hx : x ∈ partialRuleSet ρ.sel
    · rw [ite_eq_left hx, selectedBits_append_singleton]
      by_cases hr : selectedBits (partialRuleSet ρ.sel) x ∈ partialRuleSet r
      · rw [ite_eq_left hr, ite_eq_left (hmem.2 ⟨hx, hr⟩)]
      · rw [ite_eq_right hr, ite_eq_right (fun h => hr (hmem.1 h).2)]
    · rw [ite_eq_right hx, List.append_nil, ite_eq_right (fun h => hx (hmem.1 h).1),
        List.append_nil]

private lemma isMisesChurchDaleyRandom_of_output_stream {c : ℕ → BitString} (hc : ∀ t,
    c t <+: c (t + 1)) {u : CantorSeq}
    (hu : streamOfChain c hc = .infinite u) (R : Set BitString) :
    streamOfChain (fun t => selectedBits R (c t)) (fun t => selectedBits_prefix R (hc t)) =
        selectStream R u := by
  have hmem (x : BitString) :
      BitStream.finite x ≤ BitStream.infinite u ↔ x ∈ chainPrefixSet c := by
    rw [← hu]
    exact BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet hc) x
  have hpref : ∀ t, c t = cantorPrefix u (c t).length := by
    intro t
    have hp := (hmem _).mpr ⟨t, List.prefix_rfl⟩
    exact ((isCantorPrefix_iff_cantorPrefix_eq _ _).mp hp).symm
  have hlong : ∀ k, ∃ t, k ≤ (c t).length := by
    intro k
    have hp : BitStream.finite (cantorPrefix u k) ≤ BitStream.infinite u := by
      apply BitStream.finite_le_infinite_iff.mpr
      rw [isCantorPrefix_iff_cantorPrefix_eq, cantorPrefix_length]
    obtain ⟨t, ht⟩ := (hmem _).mp hp
    exact ⟨t, by simpa only [cantorPrefix_length] using ht.length_le⟩
  have hsets : chainPrefixSet (fun t => selectedBits R (c t)) =
      chainPrefixSet (selectChain R u) := by
    ext y
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨(c t).length, ?_⟩
      change y <+: selectedBits R (cantorPrefix u _)
      change y <+: selectedBits R (c t) at ht
      rwa [hpref t] at ht
    · rintro ⟨s, hs⟩
      obtain ⟨t, ht⟩ := hlong s
      refine ⟨t, ?_⟩
      change y <+: selectedBits R (c t)
      rw [hpref t]
      exact hs.trans (selectedBits_prefix R (cantorPrefix_mono u ht))
  simp only [selectStream, streamOfChain]
  congr 1

/-- Step 3 of the proof of `isMisesChurchDaleyRandom_of_output`: The output of the
composed rule is the output of the Church-Daley rule on the infinite output of the initial rule. -/
private lemma isMisesChurchDaleyRandom_of_output_compRule_output_of_infinite {w : CantorSeq}
    {ρ : KLRule} {u : CantorSeq} (hu : ρ.output w = .infinite u) (r : BitString →. Bool) :
  (isMisesChurchDaleyRandom_of_output_compRule ρ r).output w = selectStream (partialRuleSet r)
      u := by
  have hrev : ∀ t, (isMisesChurchDaleyRandom_of_output_compRule ρ r).revealed w t = ρ.revealed
      w t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [KLRule.revealed, KLRule.revealed, ih]; rfl
  have hchain : (isMisesChurchDaleyRandom_of_output_compRule ρ r).outputChain w
      = fun t => selectedBits (partialRuleSet r) (ρ.outputChain w t) := by
    funext t
    unfold KLRule.outputChain
    rw [hrev]
    exact isMisesChurchDaleyRandom_of_output_selectedBits_comp ρ r _
  have hu' : streamOfChain (ρ.outputChain w) (ρ.outputChain_prefix w) = .infinite u := hu
  have key := isMisesChurchDaleyRandom_of_output_stream (ρ.outputChain_prefix w) hu'
      (partialRuleSet r)
  have hcongr : ∀ (c c' : ℕ → BitString) (hc : ∀ t, c t <+: c (t+1)) (hc' : ∀ t, c' t <+: c' (t+1)),
      c = c' → streamOfChain c hc = streamOfChain c' hc' := by
    intro c c' hc hc' h
    subst h
    rfl
  exact (hcongr _ _ _ _ hchain).trans key

/-- **SUV Problem 279, p. 309.**  A Kolmogorov-Loveland admissible rule applied to a
Mises-Kolmogorov-Loveland random sequence gives a finite or a Mises-Church-Daley random sequence. -/
theorem isMisesChurchDaleyRandom_of_output {w : CantorSeq} (hw : IsMisesKLRandom w) {ρ : KLRule}
    (hρ : ρ.IsAdmissible) {u : CantorSeq} (hu : ρ.output w = .infinite u) :
    IsMisesChurchDaleyRandom u := by
  intro r hr
  have hadm := isMisesChurchDaleyRandom_of_output_compRule_isAdmissible hρ hr
  have hfreq := hw (isMisesChurchDaleyRandom_of_output_compRule ρ r) hadm
  rw [isMisesChurchDaleyRandom_of_output_compRule_output_of_infinite hu] at hfreq
  exact hfreq

end Kolmogorov.FrequencyGames
