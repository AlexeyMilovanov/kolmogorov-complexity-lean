import KolmogorovMathlib.Complexity.GeneralScheme.Frequencies.MaximalFrequency

/-!
# Exact Frequencies

Exact lower frequencies of computable sequences.  Given a lower semicomputable sequence `q` of
nonnegative reals with partial sums at most `1`, the main theorem `exists_computable_lowerFreq_eq`
produces a computable sequence `f : ℕ → ℕ` whose lower frequency of each symbol `k` is exactly
`q k`.  The construction uses a greedy "largest deficit" rule that builds blocks in which each
symbol `k < m` occurs with frequency `P m k` up to an error of `m`, and a liminf argument along the
concatenation of such blocks.

This formalizes Problem 212 of Section 6.4.3 of the book by Shen, Uspensky and Vereshchagin.
-/

namespace Kolmogorov
namespace GeneralScheme

private lemma exists_computable_lowerFreq_eq_minTable_countOcc_succ (f : ℕ → ℕ) (k n : ℕ) :
    countOcc f k (n + 1) = countOcc f k n + if f n = k then 1 else 0 := by
  unfold countOcc
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : f n = k
  · simp [h]
  · simp [h]

/-- Step 1 of the proof of `exists_computable_lowerFreq_eq_minTable`: the counting
function of a computable sequence is computable. -/
private lemma exists_computable_lowerFreq_eq_countOcc {f : ℕ → ℕ}
    (hf : Computable f) : Computable (fun p : ℕ × ℕ => countOcc f p.1 p.2) := by
  have hstep : Computable₂ (fun (p : ℕ × ℕ) (z : ℕ × ℕ) =>
      z.2 + (if f z.1 = p.1 then 1 else 0)) := by
    have h1 : Computable (fun w : (ℕ × ℕ) × (ℕ × ℕ) => f w.2.1) :=
      hf.comp (Computable.fst.comp Computable.snd)
    have h2 : Computable (fun w : (ℕ × ℕ) × (ℕ × ℕ) => w.1.1) :=
      Computable.fst.comp Computable.fst
    have h3 : Computable (fun w : (ℕ × ℕ) × (ℕ × ℕ) => decide (f w.2.1 = w.1.1)) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp h1 h2
    have h4 : Computable (fun w : (ℕ × ℕ) × (ℕ × ℕ) => if f w.2.1 = w.1.1 then 1 else 0) :=
      (Computable.cond h3 (Computable.const 1) (Computable.const 0)).of_eq fun w => by
        by_cases h : f w.2.1 = w.1.1 <;> simp [h]
    exact (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd) h4)
  have key := Computable.nat_rec (f := fun p : ℕ × ℕ => p.2) (g := fun _ : ℕ × ℕ => (0 : ℕ))
    (h := fun (p : ℕ × ℕ) (z : ℕ × ℕ) => z.2 + (if f z.1 = p.1 then 1 else 0))
    Computable.snd (Computable.const 0) hstep
  refine key.of_eq fun p => ?_
  obtain ⟨k, n⟩ := p
  simp only
  induction n with
  | zero => simp [countOcc]
  | succ n ih =>
      rw [exists_computable_lowerFreq_eq_minTable_countOcc_succ]
      simp only [] at ih ⊢
      rw [← ih]

private lemma exists_computable_lowerFreq_eq_minTable_sum_countOcc_le (f : ℕ → ℕ)
    (N n : ℕ) : ∑ k ∈ Finset.range N, countOcc f k n ≤ n := by
  simp only [countOcc, Finset.card_filter]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ i ∈ Finset.range n, 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, smul_eq_mul, mul_one]
        exact Finset.card_le_one.2 fun a ha b hb => by
          simp only [Finset.mem_filter] at ha hb
          omega
    _ = n := by simp

/-- Step 2 of the proof of `exists_computable_lowerFreq_eq`: a computable table of
rational probability rows whose column `liminf`s are exactly `q`.

Hypotheses: `f₀` is a computable sequence with `q k ≤ lowerFreq f₀ k` (SUV Theorem 136) and `r`
is a computable table in `[0, 1]` with `liminf_n r n k = q k` (Step 1). Put
`P n k = min (countOcc f₀ k n / n) (r n k)` for `k < n` and `P n k = 0` for `n ≤ k`.
Rows are non-negative with sum at most `1` (they are dominated by the frequency rows of `f₀`).
For the `liminf`, `liminf P ≥ min (liminf freq) (liminf r) ≥ q k` and `P ≤ r` gives
`liminf P ≤ liminf r = q k`. Computability: `countOcc f₀ k n` is computable from the computable
`f₀`, and `min` and division are computable on `ℚ`. -/
private theorem exists_computable_lowerFreq_eq_minTable {q : ℕ → ℝ} {f₀ : ℕ → ℕ}
    (hf₀ : Computable f₀) (hle : ∀ k, q k ≤ lowerFreq f₀ k) {r : ℕ → ℕ → ℚ}
    (hr : Computable (fun p : ℕ × ℕ => r p.1 p.2)) (hr0 : ∀ n k, 0 ≤ r n k)
    (hr1 : ∀ n k, r n k ≤ 1)
    (hrlim : ∀ k, Filter.liminf (fun n => (r n k : ℝ)) Filter.atTop = q k) :
    ∃ P : ℕ → ℕ → ℚ, Computable (fun p : ℕ × ℕ => P p.1 p.2) ∧ (∀ n k, 0 ≤ P n k) ∧
      (∀ n k, n ≤ k → P n k = 0) ∧ (∀ n, ∑ k ∈ Finset.range n, P n k ≤ 1) ∧
      ∀ k, Filter.liminf (fun n => (P n k : ℝ)) Filter.atTop = q k := by
  classical
  have hcount := exists_computable_lowerFreq_eq_countOcc hf₀
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → ℕ → ℚ, P = fun n k =>
      if k < n then min ((countOcc f₀ k n : ℚ) / n) (r n k) else 0 := ⟨_, rfl⟩
  have hfreq : Computable (fun p : ℕ × ℕ => (countOcc f₀ p.2 p.1 : ℚ) / p.1) := by
    refine computable_of_num_den (N := fun p : ℕ × ℕ => (countOcc f₀ p.2 p.1 : ℤ))
      (D := fun p : ℕ × ℕ => (p.1 - 1) + 1) ?_ ?_ (fun a => Nat.succ_pos _) ?_
    · exact ComputableReals.primrec_natCastInt.to_comp.comp
        (hcount.comp (Computable.snd.pair Computable.fst))
    · exact (Primrec.succ.comp (Primrec.pred.comp Primrec.fst)).to_comp
    · intro a
      obtain ⟨n, k⟩ := a
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [countOcc]
      · have : n - 1 + 1 = n := Nat.sub_add_cancel hn
        simp [this]
  have hPc : Computable (fun p : ℕ × ℕ => P p.1 p.2) := by
    have hlt1 : Computable (fun p : ℕ × ℕ => decide (p.2 < p.1)) :=
      (PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.snd Computable.fst
    have hlt2 : Computable (fun p : ℕ × ℕ =>
        decide (r p.1 p.2 < (countOcc f₀ p.2 p.1 : ℚ) / p.1)) :=
      computable₂_ratLt.comp hr hfreq
    have hmin : Computable (fun p : ℕ × ℕ =>
        cond (decide (r p.1 p.2 < (countOcc f₀ p.2 p.1 : ℚ) / p.1)) (r p.1 p.2)
          ((countOcc f₀ p.2 p.1 : ℚ) / p.1)) := Computable.cond hlt2 hr hfreq
    refine (Computable.cond hlt1 hmin (Computable.const (0 : ℚ))).of_eq fun p => ?_
    obtain ⟨n, k⟩ := p
    simp only [hPdef]
    by_cases hk : k < n
    · by_cases hc : r n k < (countOcc f₀ k n : ℚ) / n
      · simp [hk, hc, min_eq_right hc.le]
      · simp [hk, hc, min_eq_left (not_lt.mp hc)]
    · simp [hk]
  have hPnonneg : ∀ n k, 0 ≤ P n k := by
    intro n k
    simp only [hPdef]
    split_ifs
    · exact le_min (by positivity) (hr0 n k)
    · exact le_rfl
  have hPzero : ∀ n k, n ≤ k → P n k = 0 := by
    intro n k h
    simp only [hPdef]
    rw [ite_eq_right (not_lt.mpr h)]
  have hPle : ∀ n k, P n k ≤ r n k := by
    intro n k
    simp only [hPdef]
    split_ifs
    · exact min_le_right _ _
    · exact hr0 n k
  have hPfreq : ∀ n k, k < n → P n k ≤ (countOcc f₀ k n : ℚ) / n := by
    intro n k hk
    simp only [hPdef]
    rw [ite_eq_left hk]
    exact min_le_left _ _
  have hPsum : ∀ n, ∑ k ∈ Finset.range n, P n k ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnpos : (0 : ℚ) < n := by exact_mod_cast hn
      calc ∑ k ∈ Finset.range n, P n k
          ≤ ∑ k ∈ Finset.range n, (countOcc f₀ k n : ℚ) / n :=
            Finset.sum_le_sum fun k hk => hPfreq n k (Finset.mem_range.mp hk)
        _ = (∑ k ∈ Finset.range n, (countOcc f₀ k n : ℚ)) / n := by rw [Finset.sum_div]
        _ ≤ 1 := by
            rw [div_le_one hnpos]
            exact_mod_cast exists_computable_lowerFreq_eq_minTable_sum_countOcc_le f₀ n n
  have hPreal : ∀ n k, k < n → (P n k : ℝ) = min ((countOcc f₀ k n : ℝ) / n) (r n k : ℝ) := by
    intro n k hk
    simp only [hPdef, ite_eq_left hk]
    push_cast
    rfl
  have hP1 : ∀ n k, (P n k : ℝ) ≤ 1 := fun n k =>
    ((Rat.cast_le.mpr (hPle n k)).trans (Rat.cast_le.mpr (hr1 n k))).trans (by simp)
  have hP0' : ∀ n k, (0 : ℝ) ≤ (P n k : ℝ) := fun n k => Rat.cast_nonneg.mpr (hPnonneg n k)
  refine ⟨P, hPc, hPnonneg, hPzero, hPsum, fun k => le_antisymm ?_ ?_⟩
  · calc Filter.liminf (fun n => (P n k : ℝ)) Filter.atTop
        ≤ Filter.liminf (fun n => (r n k : ℝ)) Filter.atTop := by
          refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
            (Filter.isBoundedUnder_of ⟨0, fun n => hP0' n k⟩) ?_
          · exact_mod_cast hPle n k
          · exact Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := 1) fun n =>
              (Rat.cast_le.mpr (hr1 n k)).trans (by simp)
      _ = q k := hrlim k
  · refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
    have hfb : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n => (countOcc f₀ k n : ℝ) / n) :=
      Filter.isBoundedUnder_of ⟨0, fun n => by positivity⟩
    have hrb : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => (r n k : ℝ)) :=
      Filter.isBoundedUnder_of ⟨0, fun n => Rat.cast_nonneg.mpr (hr0 n k)⟩
    have h1 : ∀ᶠ n in Filter.atTop, c < (countOcc f₀ k n : ℝ) / n :=
      Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hc (hle k)) hfb
    have h2 : ∀ᶠ n in Filter.atTop, c < (r n k : ℝ) :=
      Filter.eventually_lt_of_lt_liminf (by rw [hrlim k]; exact hc) hrb
    have h3 : ∀ᶠ n in Filter.atTop, k < n := Filter.eventually_gt_atTop k
    refine Filter.le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := 1) fun n => hP1 n k) ?_
    filter_upwards [h1, h2, h3] with n a b hk
    rw [hPreal n k hk]
    exact (lt_min a b).le

/-- Start of block `m` in the block construction: `(m + 1)! - 1`; block `m` has length
`(m + 1) * (m + 1)!`, so that block `m + 1` starts at `(m + 2)! - 1`. -/
private def exists_computable_lowerFreq_eq_blocks_start (m : ℕ) : ℕ := (m + 1).factorial - 1

/-- Index of the block containing position `i`: the largest `m` with `(m + 1)! ≤ i + 1`. -/
private def exists_computable_lowerFreq_eq_blocks_idx (i : ℕ) : ℕ :=
  Nat.findGreatest (fun m => (m + 1).factorial ≤ i + 1) i

/-- The concatenation of the blocks `g 0, g 1, …`: at position `i` in block `m` (starting at
`(m + 1)! - 1`) it takes the value `g m (i - ((m + 1)! - 1))`. -/
private def exists_computable_lowerFreq_eq_blocks_seq (g : ℕ → ℕ → ℕ) (i : ℕ) : ℕ :=
  g (exists_computable_lowerFreq_eq_blocks_idx i)
    (i - exists_computable_lowerFreq_eq_blocks_start
      (exists_computable_lowerFreq_eq_blocks_idx i))

/-- The greedy choice: the least `k < m` whose new deficit
`(L.length + 1) * P m k - L.count k` is positive, and the filler `m` if there is none. -/
private def exists_computable_lowerFreq_eq_greedy_pick (P : ℕ → ℕ → ℚ)
    (m : ℕ) (L : List ℕ) : ℕ :=
  (List.range m).findIdx
    (fun k => decide (0 < ((L.length : ℚ) + 1) * P m k - (L.count k : ℚ)))

/-- The history of the greedy block `m`: the list of its first `t` symbols. -/
private def exists_computable_lowerFreq_eq_greedy_hist (P : ℕ → ℕ → ℚ)
    (m t : ℕ) : List ℕ :=
  Nat.rec ([] : List ℕ)
    (fun _ L => L ++ [exists_computable_lowerFreq_eq_greedy_pick P m L]) t

/-- The greedy block `m`: its symbol at position `t`. -/
private def exists_computable_lowerFreq_eq_greedy_g (P : ℕ → ℕ → ℚ)
    (m t : ℕ) : ℕ :=
  exists_computable_lowerFreq_eq_greedy_pick P m
    (exists_computable_lowerFreq_eq_greedy_hist P m t)

private lemma exists_computable_lowerFreq_eq_greedy_pick_le
    (P : ℕ → ℕ → ℚ) (m : ℕ) (L : List ℕ) :
    exists_computable_lowerFreq_eq_greedy_pick P m L ≤ m := by
  unfold exists_computable_lowerFreq_eq_greedy_pick
  simpa using List.findIdx_le_length (xs := List.range m)
    (p := fun k => decide (0 < ((L.length : ℚ) + 1) * P m k - (L.count k : ℚ)))

private lemma exists_computable_lowerFreq_eq_greedy_pick_spec
    (P : ℕ → ℕ → ℚ) (m : ℕ) (L : List ℕ) :
    (exists_computable_lowerFreq_eq_greedy_pick P m L < m ∧
      0 < ((L.length : ℚ) + 1) *
        P m (exists_computable_lowerFreq_eq_greedy_pick P m L) -
        (L.count (exists_computable_lowerFreq_eq_greedy_pick P m L) : ℚ)) ∨
    (exists_computable_lowerFreq_eq_greedy_pick P m L = m ∧
      ∀ k < m, ((L.length : ℚ) + 1) * P m k - (L.count k : ℚ) ≤ 0) := by
  have hle := exists_computable_lowerFreq_eq_greedy_pick_le P m L
  rcases hle.lt_or_eq with hlt | heq
  · left
    refine ⟨hlt, ?_⟩
    unfold exists_computable_lowerFreq_eq_greedy_pick at hlt ⊢
    have hlt' : (List.range m).findIdx
        (fun k => decide (0 < ((L.length : ℚ) + 1) * P m k - (L.count k : ℚ))) <
        (List.range m).length := by simpa using hlt
    have h := List.findIdx_getElem (xs := List.range m)
      (p := fun k => decide (0 < ((L.length : ℚ) + 1) * P m k - (L.count k : ℚ))) (w := hlt')
    simpa using h
  · right
    refine ⟨heq, fun k hk => ?_⟩
    unfold exists_computable_lowerFreq_eq_greedy_pick at heq
    have h := List.findIdx_eq_length.1 (by simpa using heq :
      (List.range m).findIdx
        (fun k => decide (0 < ((L.length : ℚ) + 1) * P m k - (L.count k : ℚ))) =
        (List.range m).length) k (List.mem_range.2 hk)
    simpa using h

/-- The weights of the greedy block `m`: `P m k` for `k < m`, the filler mass for `k = m`. -/
private def exists_computable_lowerFreq_eq_greedy_w (P : ℕ → ℕ → ℚ)
    (m k : ℕ) : ℚ :=
  if k < m then P m k else if k = m then 1 - ∑ j ∈ Finset.range m, P m j else 0

private lemma exists_computable_lowerFreq_eq_greedy_w_nonneg {P : ℕ → ℕ → ℚ}
    (hP0 : ∀ n k, 0 ≤ P n k) (hPsum : ∀ n, ∑ k ∈ Finset.range n, P n k ≤ 1) (m k : ℕ) :
    0 ≤ exists_computable_lowerFreq_eq_greedy_w P m k := by
  unfold exists_computable_lowerFreq_eq_greedy_w
  split_ifs
  · exact hP0 m k
  · linarith [hPsum m]
  · exact le_rfl

private lemma exists_computable_lowerFreq_eq_greedy_w_sum (P : ℕ → ℕ → ℚ)
    (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), exists_computable_lowerFreq_eq_greedy_w P m k
      = 1 := by
  rw [Finset.sum_range_succ]
  have h1 : ∑ k ∈ Finset.range m,
      exists_computable_lowerFreq_eq_greedy_w P m k =
      ∑ k ∈ Finset.range m, P m k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [exists_computable_lowerFreq_eq_greedy_w, Finset.mem_range.1 hk]
  rw [h1]
  simp [exists_computable_lowerFreq_eq_greedy_w]

private lemma exists_computable_lowerFreq_eq_greedy_hist_succ
    (P : ℕ → ℕ → ℚ) (m t : ℕ) :
    exists_computable_lowerFreq_eq_greedy_hist P m (t + 1) =
      exists_computable_lowerFreq_eq_greedy_hist P m t ++
        [exists_computable_lowerFreq_eq_greedy_pick P m
          (exists_computable_lowerFreq_eq_greedy_hist P m t)] := rfl

private lemma exists_computable_lowerFreq_eq_greedy_inv {P : ℕ → ℕ → ℚ}
    (hP0 : ∀ n k, 0 ≤ P n k) (hPsum : ∀ n, ∑ k ∈ Finset.range n, P n k ≤ 1) (m t : ℕ) :
    (exists_computable_lowerFreq_eq_greedy_hist P m t).length = t ∧
    (∀ x ∈ exists_computable_lowerFreq_eq_greedy_hist P m t, x ≤ m) ∧
    ∑ k ∈ Finset.range (m + 1),
      ((exists_computable_lowerFreq_eq_greedy_hist P m t).count k : ℚ) = t ∧
    ∀ k ≤ m, -1 < (t : ℚ) * exists_computable_lowerFreq_eq_greedy_w P m k -
      ((exists_computable_lowerFreq_eq_greedy_hist P m t).count k : ℚ) := by
  induction t with
  | zero =>
    refine ⟨rfl, by simp [exists_computable_lowerFreq_eq_greedy_hist],
      by simp [exists_computable_lowerFreq_eq_greedy_hist], fun k _ => ?_⟩
    simp [exists_computable_lowerFreq_eq_greedy_hist]
  | succ t ih =>
    obtain ⟨hlen, hmem, hsum, hdef⟩ := ih
    generalize hLdef : exists_computable_lowerFreq_eq_greedy_hist P m t = L
      at hlen hmem hsum hdef
    have hx := exists_computable_lowerFreq_eq_greedy_pick_le P m L
    have hspec := exists_computable_lowerFreq_eq_greedy_pick_spec P m L
    generalize hxdef : exists_computable_lowerFreq_eq_greedy_pick P m L = x
      at hx hspec
    rw [exists_computable_lowerFreq_eq_greedy_hist_succ, hLdef, hxdef]
    have hc : ∀ k, ((L ++ [x]).count k : ℚ) = (L.count k : ℚ) + if x = k then 1 else 0 := by
      intro k
      by_cases h : x = k <;> simp [List.count_append, h]
    have hsum1 : ∑ k ∈ Finset.range (m + 1), ((L ++ [x]).count k : ℚ) = ((t + 1 : ℕ) : ℚ) := by
      simp only [hc, Finset.sum_add_distrib, hsum]
      rw [Finset.sum_ite_eq (Finset.range (m + 1)) x (fun _ => (1 : ℚ))]
      rw [ite_eq_left (Finset.mem_range.2 (Nat.lt_succ_of_le hx))]
      push_cast; ring
    refine ⟨by simp [hlen], ?_, hsum1, ?_⟩
    · intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hmem y hy
      · exact hx
    · intro k hk
      rw [hc k]
      have hw0 := exists_computable_lowerFreq_eq_greedy_w_nonneg hP0 hPsum m k
      have hd := hdef k hk
      push_cast
      by_cases hxk : x = k
      · subst hxk
        rw [ite_eq_left rfl]
        -- the new deficit is `e - 1` with `e > 0`
        have he : 0 < ((t : ℚ) + 1) *
            exists_computable_lowerFreq_eq_greedy_w P m x - (L.count x : ℚ) := by
          rcases hspec with ⟨hlt, hpos⟩ | ⟨hxm, hle⟩
          · have hw : exists_computable_lowerFreq_eq_greedy_w P m x = P m x := by
              simp [exists_computable_lowerFreq_eq_greedy_w, hlt]
            rw [hw, ← hlen]
            exact hpos
          · -- filler: the sum of all new deficits is `1`
            have hsumE : ∑ j ∈ Finset.range (m + 1), (((t : ℚ) + 1) *
                exists_computable_lowerFreq_eq_greedy_w P m j -
                (L.count j : ℚ)) = 1 := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
                exists_computable_lowerFreq_eq_greedy_w_sum, hsum]
              ring
            rw [Finset.sum_range_succ] at hsumE
            have hlt0 : ∑ j ∈ Finset.range m, (((t : ℚ) + 1) *
                exists_computable_lowerFreq_eq_greedy_w P m j -
                (L.count j : ℚ)) ≤ 0 := by
              refine Finset.sum_nonpos fun j hj => ?_
              have hjm := Finset.mem_range.1 hj
              have hw : exists_computable_lowerFreq_eq_greedy_w P m j = P m j :=
                  by
                simp [exists_computable_lowerFreq_eq_greedy_w, hjm]
              rw [hw]
              have := hle j hjm
              rwa [hlen] at this
            subst hxm
            linarith
        linarith
      · rw [ite_eq_right hxk]
        nlinarith

/-- Step 1 of the proof of `exists_computable_lowerFreq_eq_blocks`: the greedy
"largest deficit" blocks. There is a computable family of block sequences `g m : ℕ → ℕ` (the
symbol at position `t` of block `m`; independent of the block length because the rule is online)
using only symbols `≤ m`, such that every prefix of length `t` contains each `k < m` within `m`
of `P m k * t` times.

Proof idea: put `w k = P m k` for `k < m` and `w m = 1 - ∑_{k<m} P m k ≥ 0` (filler), so that
`∑_{k ≤ m} w k = 1`. At step `t` output the symbol `k ≤ m` (least one) maximizing
`e k = (t + 1) * w k - count k t`. The deficits `d k = t * w k - count k t` satisfy `∑ d k = 0`
and `∑ e k = 1`, so the chosen symbol has `e k ≥ 1 / (m + 1) > 0`; hence `d k > -1` stays true
for all `k` by induction, and then `d k = - ∑_{j ≠ k} d j < m`. Computability: the state
(the `m + 1` counters) is updated by a computable rule using the computable table `P`. -/
private theorem exists_computable_lowerFreq_eq_greedy {P : ℕ → ℕ → ℚ}
    (hP : Computable (fun p : ℕ × ℕ => P p.1 p.2)) (hP0 : ∀ n k, 0 ≤ P n k)
    (hPsum : ∀ n, ∑ k ∈ Finset.range n, P n k ≤ 1) :
    ∃ g : ℕ → ℕ → ℕ, Computable (fun p : ℕ × ℕ => g p.1 p.2) ∧ (∀ m t, g m t ≤ m) ∧
      ∀ m k t, k < m → |(countOcc (g m) k t : ℝ) - (P m k : ℝ) * t| ≤ m := by
  have hcount : ∀ m k t, countOcc
      (exists_computable_lowerFreq_eq_greedy_g P m) k t =
      (exists_computable_lowerFreq_eq_greedy_hist P m t).count k := by
    intro m k t
    induction t with
    | zero => simp [countOcc, exists_computable_lowerFreq_eq_greedy_hist]
    | succ t ih =>
      rw [isLowerSemicomputableIn_jumpSet_lowerFreq_countOcc_succ, ih,
        exists_computable_lowerFreq_eq_greedy_hist_succ]
      by_cases h : exists_computable_lowerFreq_eq_greedy_g P m t = k
      · have h' : exists_computable_lowerFreq_eq_greedy_pick P m
            (exists_computable_lowerFreq_eq_greedy_hist P m t) = k := h
        simp [h, h', List.count_append]
      · have h' : ¬ exists_computable_lowerFreq_eq_greedy_pick P m
            (exists_computable_lowerFreq_eq_greedy_hist P m t) = k := h
        simp [h, h', List.count_append]
  -- computability
  have hcnt : Computable (fun r : (ℕ × List ℕ) × ℕ => r.1.2.count r.2) := by
    have hh : Computable₂ (fun (r : (ℕ × List ℕ) × ℕ) (u : ℕ × ℕ) =>
        u.2 + cond (u.1 == r.2) 1 0) :=
      (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
        (Computable.cond (Primrec.beq.to_comp.comp (Computable.fst.comp Computable.snd)
          (Computable.snd.comp Computable.fst)) (Computable.const 1) (Computable.const 0))).to₂
    refine (Computable.list_foldr (l := fun r : (ℕ × List ℕ) × ℕ => r.1.2) (g := fun _ => 0)
      (h := fun (r : (ℕ × List ℕ) × ℕ) (u : ℕ × ℕ) => u.2 + cond (u.1 == r.2) 1 0)
      (Computable.snd.comp Computable.fst) (Computable.const 0) hh).of_eq fun r => ?_
    obtain ⟨⟨m, L⟩, k⟩ := r
    dsimp only
    induction L with
    | nil => simp
    | cons a L ih =>
      rw [List.foldr_cons, ih, List.count_cons]
      by_cases h : a = k <;> simp [h]
  have hpred : Computable (fun r : (ℕ × List ℕ) × ℕ =>
      decide (0 < ((r.1.2.length : ℚ) + 1) * P r.1.1 r.2 - (r.1.2.count r.2 : ℚ))) := by
    have h1 : Computable (fun r : (ℕ × List ℕ) × ℕ => (r.1.2.length : ℚ) + 1) :=
      computable₂_ratAdd.comp (computable_nat_to_rat.comp
        (Computable.list_length.comp (Computable.snd.comp Computable.fst))) (Computable.const 1)
    have h2 : Computable (fun r : (ℕ × List ℕ) × ℕ => P r.1.1 r.2) :=
      Computable.comp (f := fun p : ℕ × ℕ => P p.1 p.2)
        (g := fun r : (ℕ × List ℕ) × ℕ => ((r.1.1, r.2) : ℕ × ℕ)) hP
        (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
    have h3 : Computable (fun r : (ℕ × List ℕ) × ℕ => (r.1.2.count r.2 : ℚ)) :=
      computable_nat_to_rat.comp hcnt
    have h4 := computable₂_ratSub.comp (computable₂_ratMul.comp h1 h2) h3
    exact computable₂_ratLt.comp (Computable.const 0) h4
  have hpick : Computable (fun q : ℕ × List ℕ =>
      exists_computable_lowerFreq_eq_greedy_pick P q.1 q.2) := by
    have hh : Computable₂ (fun (q : ℕ × List ℕ) (u : ℕ × ℕ) =>
        cond (decide (0 < ((q.2.length : ℚ) + 1) * P q.1 u.1 - (q.2.count u.1 : ℚ))) 0
          (u.2 + 1)) := by
      have hsucc : Computable (fun w : (ℕ × List ℕ) × (ℕ × ℕ) => w.2.2 + 1) :=
        Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd) (Computable.const 1)
      have hpr : Computable (fun w : (ℕ × List ℕ) × (ℕ × ℕ) =>
          decide (0 < ((w.1.2.length : ℚ) + 1) * P w.1.1 w.2.1 - (w.1.2.count w.2.1 : ℚ))) :=
        Computable.comp (f := fun r : (ℕ × List ℕ) × ℕ =>
          decide (0 < ((r.1.2.length : ℚ) + 1) * P r.1.1 r.2 - (r.1.2.count r.2 : ℚ)))
          (g := fun w : (ℕ × List ℕ) × (ℕ × ℕ) => ((w.1, w.2.1) : (ℕ × List ℕ) × ℕ)) hpred
          (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
      exact (Computable.cond hpr (Computable.const 0) hsucc).to₂
    refine (Computable.list_foldr (l := fun q : ℕ × List ℕ => List.range q.1) (g := fun _ => 0)
      (h := fun (q : ℕ × List ℕ) (u : ℕ × ℕ) =>
        cond (decide (0 < ((q.2.length : ℚ) + 1) * P q.1 u.1 - (q.2.count u.1 : ℚ))) 0
          (u.2 + 1))
      (Primrec.list_range.to_comp.comp Computable.fst) (Computable.const 0) hh).of_eq
      fun q => ?_
    obtain ⟨m, L⟩ := q
    dsimp only
    unfold exists_computable_lowerFreq_eq_greedy_pick
    generalize List.range m = l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.foldr_cons, ih, List.findIdx_cons]
      by_cases h : 0 < ((L.length : ℚ) + 1) * P m a - (L.count a : ℚ) <;> simp [h]
  have hhist : Computable (fun p : ℕ × ℕ =>
      exists_computable_lowerFreq_eq_greedy_hist P p.1 p.2) := by
    have hh : Computable₂ (fun (p : ℕ × ℕ) (u : ℕ × List ℕ) =>
        u.2 ++ [exists_computable_lowerFreq_eq_greedy_pick P p.1 u.2]) :=
      (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
        (Computable.comp (f := fun q : ℕ × List ℕ =>
            exists_computable_lowerFreq_eq_greedy_pick P q.1 q.2)
          (g := fun w : (ℕ × ℕ) × (ℕ × List ℕ) => ((w.1.1, w.2.2) : ℕ × List ℕ)) hpick
          (Computable.pair (Computable.fst.comp Computable.fst)
            (Computable.snd.comp Computable.snd)))).to₂
    have hrec := Computable.nat_rec (f := fun p : ℕ × ℕ => p.2)
      (g := fun _ => ([] : List ℕ))
      (h := fun (p : ℕ × ℕ) (u : ℕ × List ℕ) =>
        u.2 ++ [exists_computable_lowerFreq_eq_greedy_pick P p.1 u.2])
      Computable.snd (Computable.const []) hh
    exact hrec.of_eq fun p => rfl
  refine ⟨exists_computable_lowerFreq_eq_greedy_g P,
    Computable.comp (f := fun q : ℕ × List ℕ =>
        exists_computable_lowerFreq_eq_greedy_pick P q.1 q.2)
      (g := fun p : ℕ × ℕ => ((p.1, exists_computable_lowerFreq_eq_greedy_hist
        P p.1 p.2) : ℕ × List ℕ)) hpick
      (Computable.pair Computable.fst hhist), fun m t =>
      exists_computable_lowerFreq_eq_greedy_pick_le P m _, ?_⟩
  intro m k t hk
  obtain ⟨hlen, -, hsum, hdef⟩ :=
    exists_computable_lowerFreq_eq_greedy_inv hP0 hPsum m t
  rw [hcount]
  generalize exists_computable_lowerFreq_eq_greedy_hist P m t = L
    at hlen hsum hdef
  have hwk : exists_computable_lowerFreq_eq_greedy_w P m k = P m k := by
    simp [exists_computable_lowerFreq_eq_greedy_w, hk]
  -- `d j + 1 > 0` for all `j ≤ m`, and `∑ (d j + 1) = m + 1`
  have hpos : ∀ j ∈ Finset.range (m + 1), 0 ≤ (t : ℚ) *
      exists_computable_lowerFreq_eq_greedy_w P m j - (L.count j : ℚ) + 1 :=
    fun j hj => by linarith [hdef j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  have htot : ∑ j ∈ Finset.range (m + 1), ((t : ℚ) *
      exists_computable_lowerFreq_eq_greedy_w P m j - (L.count j : ℚ) + 1) =
      ((m : ℚ) + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      exists_computable_lowerFreq_eq_greedy_w_sum, hsum]
    simp
  have hle := Finset.single_le_sum hpos (Finset.mem_range.2 (Nat.lt_succ_of_lt hk))
  rw [htot, hwk] at hle
  have hlow := hdef k hk.le
  rw [hwk] at hlow
  have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have key : |(L.count k : ℚ) - P m k * t| ≤ m := by
    rw [abs_le]; constructor <;> nlinarith
  have key' : |((L.count k : ℕ) : ℝ) - (P m k : ℝ) * t| ≤ m := by
    have := (Rat.cast_le (K := ℝ)).2 key
    push_cast at this
    exact this
  exact key'

private theorem exists_computable_lowerFreq_eq_computable_primrec_factorial :
    Primrec Nat.factorial := by
  have : Primrec (fun n : ℕ => Nat.rec (motive := fun _ => ℕ) 1 (fun k ih => (k+1) * ih) n) :=
    Primrec.nat_rec' (f := id) (g := fun _ => 1) (h := fun _ p => (p.1 + 1) * p.2) Primrec.id
      (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  refine this.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.factorial_succ, ← ih]

/-- Step 2 of the proof of `exists_computable_lowerFreq_eq_blocks`: the
concatenation of the blocks of a computable family is computable (the block index
`Nat.findGreatest (fun m => (m + 1)! ≤ i + 1) i` and the offset are computable from `i`). -/
private theorem exists_computable_lowerFreq_eq_computable {g : ℕ → ℕ → ℕ}
    (hg : Computable (fun p : ℕ × ℕ => g p.1 p.2)) :
    Computable (exists_computable_lowerFreq_eq_blocks_seq g) := by
  have hf := exists_computable_lowerFreq_eq_computable_primrec_factorial
  have hidx : Primrec exists_computable_lowerFreq_eq_blocks_idx := by
    unfold exists_computable_lowerFreq_eq_blocks_idx
    refine Primrec.nat_findGreatest (p := fun (i m : ℕ) => (m + 1).factorial ≤ i + 1)
      Primrec.id ?_
    exact Primrec.nat_le.comp (hf.comp (Primrec.succ.comp Primrec.snd))
      (Primrec.succ.comp Primrec.fst)
  have hstart : Primrec exists_computable_lowerFreq_eq_blocks_start := by
    unfold exists_computable_lowerFreq_eq_blocks_start
    exact Primrec.nat_sub.comp (hf.comp Primrec.succ) (Primrec.const 1)
  have h2 : Primrec (fun i : ℕ => (exists_computable_lowerFreq_eq_blocks_idx i,
      i - exists_computable_lowerFreq_eq_blocks_start
        (exists_computable_lowerFreq_eq_blocks_idx i))) :=
    hidx.pair (Primrec.nat_sub.comp Primrec.id (hstart.comp hidx))
  exact hg.comp h2.to_comp

private theorem exists_computable_lowerFreq_eq_blocks_idx_eq (m s : ℕ)
    (hs : s < (m + 1) * (m + 1).factorial) :
    exists_computable_lowerFreq_eq_blocks_idx ((m + 1).factorial - 1 + s) = m := by
  have hpos := Nat.factorial_pos (m + 1)
  have hself := Nat.self_le_factorial (m + 1)
  unfold exists_computable_lowerFreq_eq_blocks_idx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => by omega, fun n hmn hn => ?_⟩
  have h1 : (m + 2).factorial ≤ (n + 1).factorial := Nat.factorial_le (by omega)
  have h2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  have h4 : (m + 2) * (m + 1).factorial = (m + 1).factorial + (m + 1) * (m + 1).factorial := by
    ring
  intro h
  omega

private theorem exists_computable_lowerFreq_eq_blocks_count_succ (f : ℕ → ℕ) (k n : ℕ) :
    countOcc f k (n + 1) = countOcc f k n + if f n = k then 1 else 0 := by
  unfold countOcc
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

/-- Step 3 of the proof of `exists_computable_lowerFreq_eq_blocks`: counting in
the concatenation. Position `(m + 1)! - 1 + s` with `s < (m + 1) * (m + 1)!` lies in block `m` at
offset `s`, so the occurrences of `k` in `[(m + 1)! - 1, (m + 1)! - 1 + t)` are those of the
block `g m` among its first `t` positions. -/
private theorem exists_computable_lowerFreq_eq_count (g : ℕ → ℕ → ℕ)
    (k m t : ℕ) (ht : t ≤ (m + 1) * (m + 1).factorial) :
    countOcc (exists_computable_lowerFreq_eq_blocks_seq g) k ((m + 1).factorial - 1 + t) =
      countOcc (exists_computable_lowerFreq_eq_blocks_seq g) k ((m + 1).factorial - 1) +
        countOcc (g m) k t := by
  induction t with
  | zero => simp [countOcc]
  | succ t ih =>
    have ht' : t ≤ (m + 1) * (m + 1).factorial := by omega
    have hseq : exists_computable_lowerFreq_eq_blocks_seq g ((m + 1).factorial - 1 + t) =
        g m t := by
      unfold exists_computable_lowerFreq_eq_blocks_seq
      rw [exists_computable_lowerFreq_eq_blocks_idx_eq m t (by omega)]
      unfold exists_computable_lowerFreq_eq_blocks_start
      congr 1
      omega
    rw [← add_assoc, exists_computable_lowerFreq_eq_blocks_count_succ,
      exists_computable_lowerFreq_eq_blocks_count_succ, ih ht', hseq]
    ring

private lemma exists_computable_lowerFreq_eq_liminf_q_lt (m : ℕ) :
    (m + 2).factorial - 1 < (m + 3).factorial - 1 := by
  have h := (Nat.factorial_lt (n := m + 2) (m := m + 3) (Nat.succ_pos _)).2 (by omega)
  have := Nat.factorial_pos (m + 2)
  omega

private lemma exists_computable_lowerFreq_eq_liminf_q_ge (m : ℕ) :
    (m + 1) * (m + 1).factorial ≤ (m + 2).factorial - 1 := by
  have hN := Nat.factorial_pos (m + 1)
  have h2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  have : (m + 2) * (m + 1).factorial = (m + 1) * (m + 1).factorial + (m + 1).factorial := by ring
  omega

private lemma exists_computable_lowerFreq_eq_liminf_block (M n : ℕ)
    (hn : (M + 2).factorial - 1 ≤ n) :
    ∃ m, M ≤ m ∧ (m + 2).factorial - 1 ≤ n ∧ n ≤ (m + 3).factorial - 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨M, le_rfl, le_rfl, (exists_computable_lowerFreq_eq_liminf_q_lt M).le⟩
  | succ n hn ih =>
    obtain ⟨m, hm, h1, h2⟩ := ih
    by_cases h : n + 1 ≤ (m + 3).factorial - 1
    · exact ⟨m, hm, by omega, h⟩
    · have h5 : (m + 3).factorial - 1 < (m + 4).factorial - 1 :=
        exists_computable_lowerFreq_eq_liminf_q_lt (m + 1)
      refine ⟨m + 1, by omega, ?_, ?_⟩
      · change (m + 3).factorial - 1 ≤ n + 1
        omega
      · change n + 1 ≤ (m + 4).factorial - 1
        omega

/-- Step 4a of the proof of `exists_computable_lowerFreq_eq_liminf`:
at the end of block `m`, `F a_{m+1} = p m * a_{m+1} + O ((m + 1)!)`. -/
private lemma exists_computable_lowerFreq_eq_liminf_endblock {F : ℕ → ℕ}
    {p : ℕ → ℝ} (hp0 : ∀ m, 0 ≤ p m) (hp1 : ∀ m, p m ≤ 1) (hF : ∀ n, F n ≤ n) {m₀ : ℕ}
    (hblock : ∀ m, m₀ ≤ m → ∀ t, t ≤ (m + 1) * (m + 1).factorial →
      |(F ((m + 1).factorial - 1 + t) : ℝ) - F ((m + 1).factorial - 1) - p m * t| ≤ m)
    {m : ℕ} (hm : m₀ ≤ m) :
    |(F ((m + 2).factorial - 1) : ℝ) - p m * (((m + 2).factorial - 1 : ℕ) : ℝ)| ≤
      2 * ((m + 1).factorial : ℝ) := by
  have h := hblock m hm ((m + 1) * (m + 1).factorial) le_rfl
  have hN := Nat.factorial_pos (m + 1)
  have h2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  have hq : (m + 1).factorial - 1 + (m + 1) * (m + 1).factorial = (m + 2).factorial - 1 := by
    have : (m + 2) * (m + 1).factorial = (m + 1) * (m + 1).factorial + (m + 1).factorial := by
      ring
    omega
  rw [hq] at h
  have hmN : m + 1 ≤ (m + 1).factorial := Nat.self_le_factorial _
  have hmNr : (m : ℝ) + 1 ≤ ((m + 1).factorial : ℝ) := by exact_mod_cast hmN
  have hNr : (1 : ℝ) ≤ ((m + 1).factorial : ℝ) := by exact_mod_cast hN
  have hFa : (F ((m + 1).factorial - 1) : ℝ) ≤ ((m + 1).factorial : ℝ) - 1 := by
    have h3 : (F ((m + 1).factorial - 1) : ℝ) ≤ (((m + 1).factorial - 1 : ℕ) : ℝ) := by
      exact_mod_cast hF _
    rwa [Nat.cast_sub hN, Nat.cast_one] at h3
  have hFa0 : (0 : ℝ) ≤ F ((m + 1).factorial - 1) := Nat.cast_nonneg _
  have hq2 : (((m + 2).factorial - 1 : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m + 1).factorial : ℝ) - 1 := by
    have h4 : 1 ≤ (m + 2).factorial := Nat.factorial_pos _
    rw [Nat.cast_sub h4, h2]
    push_cast
    ring
  rw [hq2]
  push_cast at h
  have hp0m := hp0 m
  have hp1m := hp1 m
  have hpN0 : 0 ≤ p m * (((m + 1).factorial : ℝ) - 1) := mul_nonneg hp0m (by linarith)
  have hpN1 : p m * (((m + 1).factorial : ℝ) - 1) ≤ ((m + 1).factorial : ℝ) - 1 :=
    mul_le_of_le_one_left (by linarith) hp1m
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [h.1, h.2]

/-- Step 4b of the proof of `exists_computable_lowerFreq_eq_liminf`:
inside block `m + 1`, `F n / n ≥ min (p m) (p (m + 1)) - 3 / (m + 1)`. -/
private lemma exists_computable_lowerFreq_eq_liminf_inblock {F : ℕ → ℕ}
    {p : ℕ → ℝ} (hp0 : ∀ m, 0 ≤ p m) (hp1 : ∀ m, p m ≤ 1) (hF : ∀ n, F n ≤ n) {m₀ : ℕ}
    (hblock : ∀ m, m₀ ≤ m → ∀ t, t ≤ (m + 1) * (m + 1).factorial →
      |(F ((m + 1).factorial - 1 + t) : ℝ) - F ((m + 1).factorial - 1) - p m * t| ≤ m)
    {m : ℕ} (hm : m₀ ≤ m) {t : ℕ} (ht : t ≤ (m + 2) * (m + 2).factorial) :
    min (p m) (p (m + 1)) - 3 / ((m : ℝ) + 1) ≤
      (F ((m + 2).factorial - 1 + t) : ℝ) / (((m + 2).factorial - 1 + t : ℕ) : ℝ) := by
  have hA := exists_computable_lowerFreq_eq_liminf_endblock hp0 hp1 hF hblock hm
  have hB : |(F ((m + 2).factorial - 1 + t) : ℝ) - F ((m + 2).factorial - 1) -
      p (m + 1) * t| ≤ (m : ℝ) + 1 := by
    have := hblock (m + 1) (by omega) t ht
    push_cast at this
    exact this
  have hN := Nat.factorial_pos (m + 1)
  have hqge := exists_computable_lowerFreq_eq_liminf_q_ge m
  have hmN : m + 1 ≤ (m + 1).factorial := Nat.self_le_factorial _
  have hmNr : (m : ℝ) + 1 ≤ ((m + 1).factorial : ℝ) := by exact_mod_cast hmN
  have hNr : (1 : ℝ) ≤ ((m + 1).factorial : ℝ) := by exact_mod_cast hN
  have hqger : ((m : ℝ) + 1) * ((m + 1).factorial : ℝ) ≤ (((m + 2).factorial - 1 : ℕ) : ℝ) := by
    exact_mod_cast hqge
  have hqpos : (0 : ℝ) < ((m + 1).factorial : ℝ) := by linarith
  have hnge : ((m : ℝ) + 1) * ((m + 1).factorial : ℝ) ≤
      (((m + 2).factorial - 1 + t : ℕ) : ℝ) := by
    have : (((m + 2).factorial - 1 + t : ℕ) : ℝ) =
        (((m + 2).factorial - 1 : ℕ) : ℝ) + (t : ℝ) := by push_cast; ring
    rw [this]
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    linarith
  have hnpos : (0 : ℝ) < (((m + 2).factorial - 1 + t : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((m : ℝ) + 1) * ((m + 1).factorial : ℝ) := by positivity
    linarith
  have hn : (((m + 2).factorial - 1 + t : ℕ) : ℝ) =
      (((m + 2).factorial - 1 : ℕ) : ℝ) + (t : ℝ) := by push_cast; ring
  have hmin1 : min (p m) (p (m + 1)) ≤ p m := min_le_left _ _
  have hmin2 : min (p m) (p (m + 1)) ≤ p (m + 1) := min_le_right _ _
  set μ := min (p m) (p (m + 1)) with hμ
  rw [le_div_iff₀ hnpos]
  rw [abs_le] at hA hB
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (((m + 2).factorial - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 : 3 / ((m : ℝ) + 1) * (((m : ℝ) + 1) * ((m + 1).factorial : ℝ)) =
      3 * ((m + 1).factorial : ℝ) := by
    field_simp
  have h4 : 3 / ((m : ℝ) + 1) * (((m : ℝ) + 1) * ((m + 1).factorial : ℝ)) ≤
      3 / ((m : ℝ) + 1) * (((m + 2).factorial - 1 + t : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hnge (by positivity)
  have h5 : μ * (((m + 2).factorial - 1 : ℕ) : ℝ) ≤ p m * (((m + 2).factorial - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hmin1 hq0
  have h6 : μ * (t : ℝ) ≤ p (m + 1) * (t : ℝ) := mul_le_mul_of_nonneg_right hmin2 ht0
  have h7 : (F ((m + 2).factorial - 1 + t) : ℝ) ≥ p m * (((m + 2).factorial - 1 : ℕ) : ℝ) +
      p (m + 1) * (t : ℝ) - 3 * ((m + 1).factorial : ℝ) := by
    nlinarith [hA.1, hA.2, hB.1, hB.2]
  rw [hn] at h4 ⊢
  nlinarith [h3, h4, h5, h6, h7]

/-- Step 4 of the proof of `exists_computable_lowerFreq_eq_blocks`: the analytic
part. Let `F n` be a counting function (`F n ≤ n`) and `p m ∈ [0, 1]` such that for all
`m ≥ m₀` and `t ≤ (m + 1) * (m + 1)!` we have `|F (a_m + t) - F a_m - p m * t| ≤ m` where
`a_m = (m + 1)! - 1`. Then `liminf F n / n = liminf p m`.

Proof idea: `a_{m+1} = a_m + (m + 1) * (a_m + 1)`. At the end of block `m - 1`,
`F a_m / a_m = p (m - 1) + O (1 / m)` (the earlier blocks have length `a_{m-1} ≤ a_m / m` and
the error is `≤ m`). For `n = a_m + t` in block `m`, `F n / n` equals, up to `O (m / a_m) = o (1)`,
the convex combination `(a_m / n) * (F a_m / a_m) + (t / n) * p m`; hence it is
`≥ min (p (m-1), p m) - o (1)` and the liminf is `≥ liminf p`; evaluating at `n = a_m` gives
`liminf ≤ liminf p`. -/
private theorem exists_computable_lowerFreq_eq_liminf {F : ℕ → ℕ} {p : ℕ → ℝ}
    (hp0 : ∀ m, 0 ≤ p m) (hp1 : ∀ m, p m ≤ 1) (hF : ∀ n, F n ≤ n) {m₀ : ℕ}
    (hblock : ∀ m, m₀ ≤ m → ∀ t, t ≤ (m + 1) * (m + 1).factorial →
      |(F ((m + 1).factorial - 1 + t) : ℝ) - F ((m + 1).factorial - 1) - p m * t| ≤ m) :
    Filter.liminf (fun n => (F n : ℝ) / n) Filter.atTop = Filter.liminf p Filter.atTop := by
  have hf0 : ∀ n, 0 ≤ (F n : ℝ) / n := fun n => by positivity
  have hf1 : ∀ n, (F n : ℝ) / n ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [div_le_one (by exact_mod_cast hn)]
      exact_mod_cast hF n
  have hfb1 : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n => (F n : ℝ) / n) :=
    ⟨1, Filter.eventually_map.2 (Filter.Eventually.of_forall hf1)⟩
  have hfb0 : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => (F n : ℝ) / n) :=
    ⟨0, Filter.eventually_map.2 (Filter.Eventually.of_forall hf0)⟩
  have hpb1 : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop p :=
    ⟨1, Filter.eventually_map.2 (Filter.Eventually.of_forall hp1)⟩
  have hpb0 : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop p :=
    ⟨0, Filter.eventually_map.2 (Filter.Eventually.of_forall hp0)⟩
  have hq_tend : Filter.Tendsto (fun m : ℕ => (m + 2).factorial - 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun m => ?_) Filter.tendsto_id
    have := Nat.self_le_factorial (m + 2)
    simp only [id]
    omega
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hfreq : ∃ᶠ m in Filter.atTop, p m < Filter.liminf p Filter.atTop + ε / 2 :=
      Filter.frequently_lt_of_liminf_lt hpb1.isCoboundedUnder_flip (by linarith)
    have hfreq2 : ∃ᶠ m in Filter.atTop,
        (F ((m + 2).factorial - 1) : ℝ) / (((m + 2).factorial - 1 : ℕ) : ℝ) ≤
          Filter.liminf p Filter.atTop + ε :=
      (hfreq.and_eventually (Filter.eventually_ge_atTop (max m₀ ⌈4 / ε⌉₊))).mono fun m ⟨h1, h2⟩ =>
        by
        have hm0 : m₀ ≤ m := (le_max_left _ _).trans h2
        have hm1 : ⌈4 / ε⌉₊ ≤ m := (le_max_right _ _).trans h2
        have hm1' : 4 / ε ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm1)
        have hA :=
          exists_computable_lowerFreq_eq_liminf_endblock hp0 hp1 hF hblock hm0
        rw [abs_le] at hA
        have hN := Nat.factorial_pos (m + 1)
        have hqge :=
          exists_computable_lowerFreq_eq_liminf_q_ge m
        have hqger : ((m : ℝ) + 1) * ((m + 1).factorial : ℝ) ≤
            (((m + 2).factorial - 1 : ℕ) : ℝ) := by exact_mod_cast hqge
        have hNr : (1 : ℝ) ≤ ((m + 1).factorial : ℝ) := by exact_mod_cast hN
        have hqpos : (0 : ℝ) < (((m + 2).factorial - 1 : ℕ) : ℝ) := by
          have : (0 : ℝ) < ((m : ℝ) + 1) * ((m + 1).factorial : ℝ) := by positivity
          linarith
        rw [div_le_iff₀ hqpos]
        have h5 : 2 * ((m + 1).factorial : ℝ) ≤
            ε / 2 * (((m + 2).factorial - 1 : ℕ) : ℝ) := by
          have : 4 ≤ ε * (m : ℝ) := by
            rw [div_le_iff₀ hε] at hm1'
            linarith
          have h6 : ε / 2 * (((m : ℝ) + 1) * ((m + 1).factorial : ℝ)) ≤
              ε / 2 * (((m + 2).factorial - 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hqger (by positivity)
          nlinarith
        nlinarith [hA.1, hA.2]
    have hfreq3 : ∃ᶠ n in Filter.atTop,
        (F n : ℝ) / n ≤ Filter.liminf p Filter.atTop + ε :=
      hq_tend.frequently (p := fun n => (F n : ℝ) / n ≤ Filter.liminf p Filter.atTop + ε) hfreq2
    have := Filter.liminf_le_of_frequently_le hfreq3 hfb0
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hev : ∀ᶠ m in Filter.atTop, Filter.liminf p Filter.atTop - ε / 2 < p m :=
      Filter.eventually_lt_of_lt_liminf (by linarith) hpb0
    obtain ⟨M1, hM1⟩ := Filter.eventually_atTop.1 hev
    have key : ∀ n, (max (max M1 m₀) ⌈6 / ε⌉₊ + 2).factorial - 1 ≤ n →
        Filter.liminf p Filter.atTop - ε ≤ (F n : ℝ) / n := by
      intro n hn
      obtain ⟨m, hm, h1, h2⟩ :=
        exists_computable_lowerFreq_eq_liminf_block _ n hn
      have hm1 : M1 ≤ m := ((le_max_left _ _).trans (le_max_left _ _)).trans hm
      have hm0 : m₀ ≤ m := ((le_max_right _ _).trans (le_max_left _ _)).trans hm
      have hm2 : ⌈6 / ε⌉₊ ≤ m := (le_max_right _ _).trans hm
      have hm2' : 6 / ε ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm2)
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
      have ht : t ≤ (m + 2) * (m + 2).factorial := by
        have h3 : (m + 3).factorial = (m + 3) * (m + 2).factorial := Nat.factorial_succ (m + 2)
        have hN := Nat.factorial_pos (m + 2)
        have : (m + 3) * (m + 2).factorial = (m + 2) * (m + 2).factorial + (m + 2).factorial := by
          ring
        omega
      have hB := exists_computable_lowerFreq_eq_liminf_inblock hp0 hp1 hF
        hblock hm0 ht
      have e1 := hM1 m hm1
      have e2 := hM1 (m + 1) (by omega)
      have e3 : 3 / ((m : ℝ) + 1) ≤ ε / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have : 6 ≤ ε * (m : ℝ) := by
          rw [div_le_iff₀ hε] at hm2'
          linarith
        nlinarith
      have e4 : Filter.liminf p Filter.atTop - ε / 2 < min (p m) (p (m + 1)) :=
        lt_min e1 e2
      linarith
    have hge : Filter.liminf p Filter.atTop - ε ≤
        Filter.liminf (fun n => (F n : ℝ) / n) Filter.atTop :=
      Filter.le_liminf_of_le hfb1.isCoboundedUnder_flip
        (Filter.eventually_atTop.2 ⟨_, key⟩)
    linarith

/-- Step 3 of the proof of `exists_computable_lowerFreq_eq`: from a computable table of
rational rows (non-negative, supported on `k < n`, sum at most `1`) build a computable sequence
`f` whose lower frequencies are the column `liminf`s of the table.

Proof idea: `f` is the concatenation of blocks `B₀, B₁, …`, block `m` having length `L_m` with
`L_m` much larger than `m` and than `L₀ + … + L_{m-1}` (e.g. `L_m = (m+1)·(L₀+…+L_{m-1}+1)·D_m`
for a common denominator `D_m` of row `m`). Inside block `m`, a greedy "largest deficit" rule
makes every prefix contain each `k < m` within `O(m)` of `P m k · t` times; the unused mass
`1 - ∑ P m k` (and the rounding) is given to the filler symbol `m`, which does not occur in the
support of row `m` and whose density is diluted by later blocks. At the end of block `m` the
frequency of `k` is `P m k + o(1)`, and during block `m` it is a convex combination of the
values at the end of block `m-1` and `P m k`, up to `o(1)`; hence its `liminf` equals
`liminf_m P m k`. -/
private theorem exists_computable_lowerFreq_eq_blocks {P : ℕ → ℕ → ℚ}
    (hP : Computable (fun p : ℕ × ℕ => P p.1 p.2)) (hP0 : ∀ n k, 0 ≤ P n k)
    (hPs : ∀ n k, n ≤ k → P n k = 0) (hPsum : ∀ n, ∑ k ∈ Finset.range n, P n k ≤ 1) :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ k, lowerFreq f k = Filter.liminf (fun n => (P n k : ℝ)) Filter.atTop := by
  obtain ⟨g, hg, -, hgc⟩ := exists_computable_lowerFreq_eq_greedy hP hP0 hPsum
  refine ⟨_, exists_computable_lowerFreq_eq_computable hg, fun k => ?_⟩
  refine exists_computable_lowerFreq_eq_liminf
    (F := countOcc (exists_computable_lowerFreq_eq_blocks_seq g) k)
    (p := fun m => (P m k : ℝ)) (m₀ := k + 1) (fun m => by exact_mod_cast hP0 m k) (fun m => ?_)
    (fun n => ?_) (fun m hm t ht => ?_)
  · by_cases hmk : m ≤ k
    · simp [hPs m k hmk]
    · have : P m k ≤ ∑ j ∈ Finset.range m, P m j :=
        Finset.single_le_sum (f := fun j => P m j) (fun j _ => hP0 m j)
          (Finset.mem_range.2 (by omega))
      exact_mod_cast this.trans (hPsum m)
  · exact (Finset.card_filter_le _ _).trans (Finset.card_range n).le
  · rw [exists_computable_lowerFreq_eq_count g k m t ht]
    have := hgc m k t (by omega)
    push_cast
    convert this using 2
    ring

/-- **SUV Problem 212 (Section 6.4.3, printed p. 211).** Under the hypotheses of Theorem 136
there is a computable sequence whose lower frequencies are exactly the `qₖ`.

Proof idea (book's hint): combine the proof of Theorem 136 with the solution of Problem 211. -/
theorem exists_computable_lowerFreq_eq {q : ℕ → ℝ}
    (hq : PointToSet.IsLowerSemicomputableIn jumpSet q) (h0 : ∀ i, 0 ≤ q i)
    (h1 : ∀ N, ∑ i ∈ Finset.range N, q i ≤ 1) :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ k, lowerFreq f k = q k := by
  obtain ⟨f₀, hf₀, hle⟩ := exists_computable_le_lowerFreq hq h0 h1
  obtain ⟨r, hr, hr0, hr1, hrlim⟩ := exists_computable_lowerFreq_eq_uniformLiminf hq h0 h1
  obtain ⟨P, hP, hP0, hPs, hPsum, hPlim⟩ :=
    exists_computable_lowerFreq_eq_minTable hf₀ hle hr hr0 hr1 hrlim
  obtain ⟨f, hf, hfeq⟩ := exists_computable_lowerFreq_eq_blocks hP hP0 hPs hPsum
  exact ⟨f, hf, fun k => (hfeq k).trans (hPlim k)⟩

end GeneralScheme
end Kolmogorov
