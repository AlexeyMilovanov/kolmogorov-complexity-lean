import KolmogorovMathlib.Complexity.GeneralScheme.Frequencies.LowerFrequency

/-!
# Maximal Frequency

Section 6.4.3 of the book by Shen, Uspensky and Vereshchagin: the lower frequency of a computable
sequence realizes a maximal `0'`-lower-semicomputable semimeasure.

Main declarations:

* `exists_computable_liminf_eq`: every `0'`-lower-semicomputable real is the `liminf` of a
  computable bounded sequence of rationals (Problem 211);
* `exists_computable_le_lowerFreq`: every `0'`-lower-semicomputable sequence `q` of non-negative
  reals with `∑ qᵢ ≤ 1` is bounded above by the lower frequencies of a computable sequence
  (Theorem 136);
* `exists_computable_lowerFreq_maximal`: for an appropriate computable sequence `f`, the lower
  frequencies form a maximal `0'`-lower-semicomputable semimeasure;
* `exists_computable_KP_jump_eq_neg_log_lowerFreq`: the resulting description of the
  `0'`-relativized prefix complexity as `-log₂` of a lower frequency, up to an additive constant;
* `exists_computable_lowerFreq_eq_uniformLiminf`: the uniform version of Problem 211.
-/

namespace Kolmogorov
namespace GeneralScheme

private lemma exists_computable_liminf_eq_ratLe :
    Computable₂ (fun a b : ℚ => decide (a ≤ b)) := by
  have h1 : Computable₂ (fun a b : ℚ => decide (a - b + 1 ≤ 1)) :=
    computable_ratLeOne.comp (computable₂_ratAdd.comp computable₂_ratSub (Computable.const 1))
  exact h1.of_eq (fun p => by
    have heq : p.1 - p.2 + 1 ≤ 1 ↔ p.1 ≤ p.2 := by
      constructor
      · intro h
        have h2 : p.1 - p.2 ≤ 0 := by linarith
        linarith
      · intro h
        linarith
    exact decide_eq_decide.mpr heq)

/-- Claim `i` is alive at stage `k`: `R i b` holds for all `b < k`. -/
private def exists_computable_liminf_eq_alive (R : ℕ → ℕ → Bool) (i k : ℕ) : Bool :=
  (List.range k).foldr (fun b acc => R i b && acc) true

/-- Claim `j` dies at the transition from stage `k` to stage `k + 1`. -/
private def exists_computable_liminf_eq_changed (R : ℕ → ℕ → Bool) (j k : ℕ) : Bool :=
  exists_computable_liminf_eq_alive R j k && !exists_computable_liminf_eq_alive R j (k + 1)

/-- No claim `j ≤ i` changes at stage `k`. -/
private def exists_computable_liminf_eq_good (R : ℕ → ℕ → Bool) (i k : ℕ) : Bool :=
  (List.range (i + 1)).foldr
    (fun j acc => !exists_computable_liminf_eq_changed R j k && acc) true

/-- The contribution of claim `i` at stage `k`. -/
private def exists_computable_liminf_eq_val (q : ℕ → ℚ) (R : ℕ → ℕ → Bool) (L U : ℚ)
    (k i : ℕ) : ℚ :=
  if exists_computable_liminf_eq_good R i k && exists_computable_liminf_eq_alive R i (k + 1)
    then min (q i) U else L

/-- The computable sequence of the book: the maximum of the contributions of the claims
`i < k`. -/
private def exists_computable_liminf_eq_seq (q : ℕ → ℚ) (R : ℕ → ℕ → Bool) (L U : ℚ)
    (k : ℕ) : ℚ :=
  (List.range k).foldr (fun i m => max (exists_computable_liminf_eq_val q R L U k i) m) L

private lemma exists_computable_liminf_eq_foldr_and_iff (l : List ℕ) (p : ℕ → Bool) :
    l.foldr (fun b acc => p b && acc) true = true ↔ ∀ b ∈ l, p b = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma exists_computable_liminf_eq_alive_iff (R : ℕ → ℕ → Bool) (i k : ℕ) :
    exists_computable_liminf_eq_alive R i k = true ↔ ∀ b < k, R i b = true := by
  simp [exists_computable_liminf_eq_alive, exists_computable_liminf_eq_foldr_and_iff]

private lemma exists_computable_liminf_eq_changed_iff (R : ℕ → ℕ → Bool) (j k : ℕ) :
    exists_computable_liminf_eq_changed R j k = true ↔
      exists_computable_liminf_eq_alive R j k = true ∧
        ¬ exists_computable_liminf_eq_alive R j (k + 1) = true := by
  simp [exists_computable_liminf_eq_changed]

private lemma exists_computable_liminf_eq_good_iff (R : ℕ → ℕ → Bool) (i k : ℕ) :
    exists_computable_liminf_eq_good R i k = true ↔
      ∀ j ≤ i, ¬ exists_computable_liminf_eq_changed R j k = true := by
  simp [exists_computable_liminf_eq_good, exists_computable_liminf_eq_foldr_and_iff]

private lemma exists_computable_liminf_eq_foldr_le_iff (g : ℕ → ℚ) (L c : ℚ) (l : List ℕ) :
    l.foldr (fun i m => max (g i) m) L ≤ c ↔ L ≤ c ∧ ∀ i ∈ l, g i ≤ c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; tauto

private lemma exists_computable_liminf_eq_seq_le_iff (q R L U) (k : ℕ) (c : ℚ) :
    exists_computable_liminf_eq_seq q R L U k ≤ c ↔
      L ≤ c ∧ ∀ i < k, exists_computable_liminf_eq_val q R L U k i ≤ c := by
  simp [exists_computable_liminf_eq_seq, exists_computable_liminf_eq_foldr_le_iff]

private lemma exists_computable_liminf_eq_le_seq_L (q R L U) (k : ℕ) :
    L ≤ exists_computable_liminf_eq_seq q R L U k := by
  have : ∀ l : List ℕ, L ≤
      l.foldr (fun i m => max (exists_computable_liminf_eq_val q R L U k i) m) L := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [le_max_of_le_right ih]
  exact this _

private lemma exists_computable_liminf_eq_val_le_seq (q R L U) (k i : ℕ) (hi : i < k) :
    exists_computable_liminf_eq_val q R L U k i ≤ exists_computable_liminf_eq_seq q R L U k := by
  have key : ∀ l : List ℕ, i ∈ l →
      exists_computable_liminf_eq_val q R L U k i ≤
        l.foldr (fun i m => max (exists_computable_liminf_eq_val q R L U k i) m) L := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro h
      rcases List.mem_cons.1 h with h | h
      · subst h; exact le_max_left _ _
      · exact le_max_of_le_right (ih h)
  exact key _ (by simpa using hi)

private lemma exists_computable_liminf_eq_changed_unique (R : ℕ → ℕ → Bool) (j k k' : ℕ)
    (h : exists_computable_liminf_eq_changed R j k = true)
    (h' : exists_computable_liminf_eq_changed R j k' = true) : k = k' := by
  rw [exists_computable_liminf_eq_changed_iff, exists_computable_liminf_eq_alive_iff,
    exists_computable_liminf_eq_alive_iff] at h h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h.2 (fun b hb => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · exact h.1 b hb
      · exact h'.1 b hlt)
  · exact h'.2 (fun b hb => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · exact h'.1 b hb
      · exact h.1 b hlt)

private lemma exists_computable_liminf_eq_eventually_unchanged (R : ℕ → ℕ → Bool) (n : ℕ) :
    ∃ K, ∀ k ≥ K, ∀ j ≤ n, ¬ exists_computable_liminf_eq_changed R j k = true := by
  induction n with
  | zero =>
    by_cases h : ∃ k0, exists_computable_liminf_eq_changed R 0 k0 = true
    · obtain ⟨k0, hk0⟩ := h
      refine ⟨k0 + 1, fun k hk j hj hc => ?_⟩
      obtain rfl : j = 0 := by omega
      have := exists_computable_liminf_eq_changed_unique R 0 k0 k hk0 hc
      omega
    · push Not at h
      refine ⟨0, fun k _ j hj hc => ?_⟩
      obtain rfl : j = 0 := by omega
      exact h k hc
  | succ n ih =>
    obtain ⟨K, hK⟩ := ih
    by_cases h : ∃ k0, exists_computable_liminf_eq_changed R (n + 1) k0 = true
    · obtain ⟨k0, hk0⟩ := h
      refine ⟨max K (k0 + 1), fun k hk j hj hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj' | rfl
      · exact hK k (le_trans (le_max_left _ _) hk) j (by omega) hc
      · have := exists_computable_liminf_eq_changed_unique R _ k0 k hk0 hc
        have := le_trans (le_max_right _ _) hk
        omega
    · push Not at h
      refine ⟨K, fun k hk j hj hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj' | rfl
      · exact hK k hk j (by omega) hc
      · exact h k hc

private theorem exists_computable_liminf_eq_comp (q : ℕ → ℚ) (R : ℕ → ℕ → Bool) (L U : ℚ)
    (hq : Computable q) (hR : Computable (fun p : ℕ × ℕ => R p.1 p.2)) :
    Computable (exists_computable_liminf_eq_seq q R L U) := by
  have halive : Computable (fun p : ℕ × ℕ => exists_computable_liminf_eq_alive R p.1 p.2) := by
    have hl : Computable (fun p : ℕ × ℕ => List.range p.2) :=
      Primrec.list_range.to_comp.comp Computable.snd
    have hh : Computable₂ (fun (p : ℕ × ℕ) (u : ℕ × Bool) => R p.1 u.1 && u.2) :=
      (Primrec.and.to_comp.comp
        (hR.comp (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd)))
        (Computable.snd.comp Computable.snd)).to₂
    exact Computable.list_foldr hl (Computable.const true) hh
  have hchanged : Computable (fun p : ℕ × ℕ => exists_computable_liminf_eq_changed R p.1 p.2) :=
    (Primrec.and.to_comp.comp halive
      (Primrec.not.to_comp.comp
        (halive.comp
          (Computable.pair Computable.fst (Primrec.succ.to_comp.comp Computable.snd))))).of_eq
      fun _ => rfl
  have hgood : Computable (fun p : ℕ × ℕ => exists_computable_liminf_eq_good R p.1 p.2) := by
    have hl : Computable (fun p : ℕ × ℕ => List.range (p.1 + 1)) :=
      Primrec.list_range.to_comp.comp (Primrec.succ.to_comp.comp Computable.fst)
    have hh : Computable₂ (fun (p : ℕ × ℕ) (u : ℕ × Bool) =>
        !exists_computable_liminf_eq_changed R u.1 p.2 && u.2) :=
      (Primrec.and.to_comp.comp
        (Primrec.not.to_comp.comp
          (hchanged.comp (Computable.pair (Computable.fst.comp Computable.snd)
            (Computable.snd.comp Computable.fst))))
        (Computable.snd.comp Computable.snd)).to₂
    exact Computable.list_foldr hl (Computable.const true) hh
  have hval : Computable (fun p : ℕ × ℕ => exists_computable_liminf_eq_val q R L U p.1 p.2) := by
    have hc1 : Computable (fun p : ℕ × ℕ => exists_computable_liminf_eq_good R p.2 p.1) := by
      have h := hgood.comp (Computable.pair (Computable.snd (α := ℕ) (β := ℕ))
        (Computable.fst (α := ℕ) (β := ℕ)))
      exact h
    have hc2 : Computable (fun p : ℕ × ℕ => exists_computable_liminf_eq_alive R p.2 (p.1 + 1)) := by
      have h := halive.comp (Computable.pair (Computable.snd (α := ℕ) (β := ℕ))
        (Primrec.succ.to_comp.comp (Computable.fst (α := ℕ) (β := ℕ))))
      exact h
    have hc : Computable (fun p : ℕ × ℕ =>
        exists_computable_liminf_eq_good R p.2 p.1 &&
          exists_computable_liminf_eq_alive R p.2 (p.1 + 1)) :=
      Primrec.and.to_comp.comp hc1 hc2
    have hqi : Computable (fun p : ℕ × ℕ => q p.2) := hq.comp Computable.snd
    have hmin : Computable (fun p : ℕ × ℕ => cond (decide (q p.2 ≤ U)) (q p.2) U) :=
      Computable.cond (exists_computable_liminf_eq_ratLe.comp hqi (Computable.const U)) hqi
        (Computable.const U)
    exact (Computable.cond hc hmin (Computable.const L)).of_eq fun p => by
      simp only [exists_computable_liminf_eq_val]
      cases hg : (exists_computable_liminf_eq_good R p.2 p.1 &&
        exists_computable_liminf_eq_alive R p.2 (p.1 + 1)) <;> simp [min_def]
  have hl : Computable (fun k : ℕ => List.range k) := Primrec.list_range.to_comp
  have hh : Computable₂ (fun (k : ℕ) (u : ℕ × ℚ) =>
      max (exists_computable_liminf_eq_val q R L U k u.1) u.2) := by
    have hv0 := hval.comp (Computable.pair (Computable.fst (α := ℕ) (β := ℕ × ℚ))
      (Computable.fst.comp (Computable.snd (α := ℕ) (β := ℕ × ℚ))))
    have hv : Computable (fun p : ℕ × (ℕ × ℚ) =>
        exists_computable_liminf_eq_val q R L U p.1 p.2.1) := hv0
    have hm : Computable (fun p : ℕ × (ℕ × ℚ) => p.2.2) :=
      Computable.snd.comp Computable.snd
    have hc : Computable (fun p : ℕ × (ℕ × ℚ) =>
        cond (decide (exists_computable_liminf_eq_val q R L U p.1 p.2.1 ≤ p.2.2)) p.2.2
          (exists_computable_liminf_eq_val q R L U p.1 p.2.1)) :=
      Computable.cond (exists_computable_liminf_eq_ratLe.comp hv hm) hm hv
    exact (hc.to₂ (α := ℕ) (β := ℕ × ℚ)).of_eq fun p => by
      simp [max_def]
  have hfin := Computable.list_foldr hl (Computable.const L) hh
  exact hfin

private theorem exists_computable_liminf_eq_step2 {x : ℝ} (q : ℕ → ℚ) (R : ℕ → ℕ → Bool)
    (hq : Computable q) (hR : Computable (fun p : ℕ × ℕ => R p.1 p.2))
    (hx : ∀ y : ℚ, (y : ℝ) < x ↔ ∃ i, q i = y ∧ ∀ b, R i b = true) :
    ∃ r : ℕ → ℚ, Computable r ∧ (∃ B : ℚ, ∀ n, |r n| ≤ B) ∧
      Filter.liminf (fun n => (r n : ℝ)) Filter.atTop = x := by
  classical
  obtain ⟨L, hL⟩ := exists_rat_lt x
  obtain ⟨U, hU⟩ := exists_rat_gt x
  have hLU : L ≤ U := by exact_mod_cast (hL.trans hU).le
  have htrue : ∀ i, (∀ b, R i b = true) → (q i : ℝ) < x :=
    fun i h => (hx (q i)).2 ⟨i, rfl, h⟩
  have hs_ge : ∀ k, L ≤ exists_computable_liminf_eq_seq q R L U k :=
    exists_computable_liminf_eq_le_seq_L q R L U
  have hs_le : ∀ k, exists_computable_liminf_eq_seq q R L U k ≤ U := by
    intro k
    rw [exists_computable_liminf_eq_seq_le_iff]
    refine ⟨hLU, fun i _ => ?_⟩
    unfold exists_computable_liminf_eq_val
    split_ifs
    · exact min_le_right _ _
    · exact hLU
  have hbdd : ∃ B : ℚ, ∀ n, |exists_computable_liminf_eq_seq q R L U n| ≤ B := by
    refine ⟨max |L| |U|, fun n => ?_⟩
    rw [abs_le]
    constructor
    · have h1 := neg_abs_le L
      have h2 := le_max_left |L| |U|
      linarith [hs_ge n]
    · exact (hs_le n).trans ((le_abs_self U).trans (le_max_right _ _))
  refine ⟨exists_computable_liminf_eq_seq q R L U,
    exists_computable_liminf_eq_comp q R L U hq hR, hbdd, ?_⟩
  have hB : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => (exists_computable_liminf_eq_seq q R L U n : ℝ)) :=
    Filter.isBoundedUnder_of ⟨U, fun n => by exact_mod_cast hs_le n⟩
  have hB' : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => (exists_computable_liminf_eq_seq q R L U n : ℝ)) :=
    Filter.isBoundedUnder_of ⟨L, fun n => by exact_mod_cast hs_ge n⟩
  have main : ∀ (c : ℚ), x < (c : ℝ) → ∀ N,
      ∃ k ≥ N, exists_computable_liminf_eq_seq q R L U k ≤ c := by
    intro c hc N
    have hLc : L ≤ c := by exact_mod_cast (hL.trans hc).le
    have hbad_false : ∀ i, c < min (q i) U → ¬ ∀ b, R i b = true := by
      intro i hi h
      have h1 : (q i : ℝ) < c := (htrue i h).trans hc
      have h2 : q i < c := by exact_mod_cast h1
      exact absurd hi (not_lt.2 ((min_le_left _ _).trans h2.le))
    by_cases hS : ∃ j, c < min (q j) U ∧ exists_computable_liminf_eq_alive R j N = true
    · set j0 := Nat.find hS with hj0def
      have hj0 : c < min (q j0) U ∧ exists_computable_liminf_eq_alive R j0 N = true :=
        Nat.find_spec hS
      have hex : ∃ b, ¬ R j0 b = true := by
        by_contra hne
        push Not at hne
        exact hbad_false j0 hj0.1 hne
      set k := Nat.find hex with hkdef
      have hk1 : ¬ R j0 k = true := Nat.find_spec hex
      have hk2 : ∀ b < k, R j0 b = true := fun b hb => by
        have := Nat.find_min hex hb
        simpa using this
      have hkN : N ≤ k := by
        by_contra hlt
        push Not at hlt
        exact hk1 ((exists_computable_liminf_eq_alive_iff R j0 N).1 hj0.2 k hlt)
      refine ⟨k, hkN, ?_⟩
      rw [exists_computable_liminf_eq_seq_le_iff]
      refine ⟨hLc, fun i hi => ?_⟩
      unfold exists_computable_liminf_eq_val
      split_ifs with hcond
      · by_contra hgt
        push Not at hgt
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨hg, ha⟩ := hcond
        have haN : exists_computable_liminf_eq_alive R i N = true :=
          (exists_computable_liminf_eq_alive_iff R i N).2 fun b hb =>
            (exists_computable_liminf_eq_alive_iff R i (k + 1)).1 ha b (by omega)
        have hjle : j0 ≤ i := Nat.find_min' hS ⟨hgt, haN⟩
        exact ((exists_computable_liminf_eq_good_iff R i k).1 hg j0 hjle)
          ((exists_computable_liminf_eq_changed_iff R j0 k).2
            ⟨(exists_computable_liminf_eq_alive_iff R j0 k).2 hk2,
              fun h => hk1 ((exists_computable_liminf_eq_alive_iff R j0 (k + 1)).1 h k
                (by omega))⟩)
      · exact hLc
    · refine ⟨N, le_rfl, ?_⟩
      rw [exists_computable_liminf_eq_seq_le_iff]
      refine ⟨hLc, fun i hi => ?_⟩
      unfold exists_computable_liminf_eq_val
      split_ifs with hcond
      · by_contra hgt
        push Not at hgt
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨hg, ha⟩ := hcond
        exact hS ⟨i, hgt, (exists_computable_liminf_eq_alive_iff R i N).2 fun b hb =>
          (exists_computable_liminf_eq_alive_iff R i (N + 1)).1 ha b (by omega)⟩
      · exact hLc
  have hev : ∀ y : ℚ, (y : ℝ) < x →
      ∀ᶠ k in Filter.atTop, (y : ℝ) ≤ (exists_computable_liminf_eq_seq q R L U k : ℝ) := by
    intro y hy
    obtain ⟨i, hiy, hi⟩ := (hx y).1 hy
    obtain ⟨K, hK⟩ := exists_computable_liminf_eq_eventually_unchanged R i
    filter_upwards [Filter.eventually_ge_atTop (max K (i + 1))] with k hk
    have hk1 : K ≤ k := le_trans (le_max_left _ _) hk
    have hk2 : i < k := lt_of_lt_of_le (Nat.lt_succ_self i) (le_trans (le_max_right _ _) hk)
    have hgood : exists_computable_liminf_eq_good R i k = true :=
      (exists_computable_liminf_eq_good_iff R i k).2 fun j hj => hK k hk1 j hj
    have halive : exists_computable_liminf_eq_alive R i (k + 1) = true :=
      (exists_computable_liminf_eq_alive_iff R i (k + 1)).2 fun b _ => hi b
    have hyU : y ≤ U := by exact_mod_cast (hy.trans hU).le
    have hv : exists_computable_liminf_eq_val q R L U k i = y := by
      unfold exists_computable_liminf_eq_val
      rw [ite_eq_left (by simp [hgood, halive]), hiy]
      exact min_eq_left hyU
    have h3 := exists_computable_liminf_eq_val_le_seq q R L U k i hk2
    rw [hv] at h3
    exact_mod_cast h3
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    refine le_trans (Filter.liminf_le_of_frequently_le (a := (c : ℝ)) ?_ hB') hc2.le
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨k, hkN, hk⟩ := main c hc1 N
    exact ⟨k, hkN, by exact_mod_cast hk⟩
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨y, hy1, hy2⟩ := exists_rat_btwn hc
    exact lt_of_lt_of_le hy1 (Filter.le_liminf_of_le hB.isCoboundedUnder_ge (hev y hy2))

/-- **SUV Problem 211 (Section 6.4.3, printed p. 210).** Every `0'`-lower-semicomputable real is
the `liminf` of a computable (bounded) sequence of rationals.

Proof idea (book's hint): the number is the supremum of a `0'`-computable sequence `rₙ`. Each
`rₙ` is the limit of a stabilizing computable sequence `rₙ,ₖ`. Let `sₖ` be the maximum of
`r₀,ₖ, …, r_{t-1},ₖ`, where `t` is the least index with `r_{t,k} ≠ r_{t,k-1}`. -/
theorem exists_computable_liminf_eq {x : ℝ}
    (hx : PointToSet.IsLowerSemicomputableIn jumpSet (fun _ : Unit => x)) :
    ∃ r : ℕ → ℚ, Computable r ∧ (∃ B : ℚ, ∀ n, |r n| ≤ B) ∧
      Filter.liminf (fun n => (r n : ℝ)) Filter.atTop = x := by
  have hP : PointToSet.IsREIn jumpSet (fun y : ℚ => (y : ℝ) < x) :=
    PointToSet.IsREIn.comp (f := fun y : ℚ => ((), y)) hx
      ((Computable.const ()).pair Computable.id).computableIn
  obtain ⟨R, hR, hRiff⟩ := exists_computable_liminf_eq_sigma2 hP
  have hdec : Computable (fun i : ℕ => (Denumerable.ofNat ℚ (Nat.unpair i).1 : ℚ)) :=
    (Primrec.ofNat ℚ).to_comp.comp (Primrec.fst.comp Primrec.unpair).to_comp
  refine exists_computable_liminf_eq_step2 (x := x)
    (fun i => Denumerable.ofNat ℚ (Nat.unpair i).1)
    (fun i b => R (Denumerable.ofNat ℚ (Nat.unpair i).1) (Nat.unpair i).2 b) hdec ?_ ?_
  · have h := hR.comp (Computable.pair (hdec.comp Computable.fst)
      (Computable.pair ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst)
        Computable.snd))
    exact h
  · intro y
    rw [hRiff y]
    constructor
    · rintro ⟨a, ha⟩
      have he : Denumerable.ofNat ℚ (Denumerable.eqv ℚ y) = y :=
        (Denumerable.eqv ℚ).symm_apply_apply y
      refine ⟨Nat.pair (Denumerable.eqv ℚ y) a, ?_, fun b => ?_⟩
      · show Denumerable.ofNat ℚ (Nat.unpair (Nat.pair (Denumerable.eqv ℚ y) a)).1 = y
        rw [Nat.unpair_pair]
        exact he
      · show R (Denumerable.ofNat ℚ (Nat.unpair (Nat.pair (Denumerable.eqv ℚ y) a)).1)
          (Nat.unpair (Nat.pair (Denumerable.eqv ℚ y) a)).2 b = true
        rw [Nat.unpair_pair]
        dsimp only
        rw [he]
        exact ha b
    · rintro ⟨i, hi, h⟩
      refine ⟨(Nat.unpair i).2, fun b => ?_⟩
      rw [← hi]
      exact h b

/-- `φ_i(i)` halts within `t` steps. -/
private def exists_computable_le_lowerFreq_sigma2_halts (i t : ℕ) : Bool :=
  (Nat.Partrec.Code.evaln t (Denumerable.ofNat Nat.Partrec.Code i) i).isSome

private theorem exists_computable_le_lowerFreq_sigma2_halts_primrec :
    Primrec (fun x : ℕ × ℕ => exists_computable_le_lowerFreq_sigma2_halts x.1 x.2) :=
  Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    ((Primrec.snd.pair ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.fst)).pair Primrec.fst))

private theorem exists_computable_le_lowerFreq_sigma2_halts_sound {i t : ℕ}
    (h : exists_computable_le_lowerFreq_sigma2_halts i t = true) : i ∈ jumpSet := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  exact Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hx)⟩

private theorem exists_computable_le_lowerFreq_sigma2_halts_complete {i : ℕ}
    (h : i ∈ jumpSet) : ∃ t, exists_computable_le_lowerFreq_sigma2_halts i t = true := by
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hx
  exact ⟨t, by simp [exists_computable_le_lowerFreq_sigma2_halts, Option.mem_def.mp ht]⟩

private theorem exists_computable_le_lowerFreq_sigma2_halts_mono {i t t' : ℕ}
    (h : t ≤ t') (hs : exists_computable_le_lowerFreq_sigma2_halts i t = true) :
    exists_computable_le_lowerFreq_sigma2_halts i t' = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  have := Nat.Partrec.Code.evaln_mono h (Option.mem_def.mpr hx)
  simp [exists_computable_le_lowerFreq_sigma2_halts, Option.mem_def.mp this]

private theorem exists_computable_le_lowerFreq_sigma2_exists_bound (u : ℕ) :
    ∃ T, ∀ i < u, i ∈ jumpSet →
      exists_computable_le_lowerFreq_sigma2_halts i T = true := by
  induction u with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ u ih =>
    obtain ⟨T, hT⟩ := ih
    by_cases hu : u ∈ jumpSet
    · obtain ⟨t, ht⟩ := exists_computable_le_lowerFreq_sigma2_halts_complete hu
      refine ⟨max T t, fun i hi hij => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact exists_computable_le_lowerFreq_sigma2_halts_mono (le_max_left _ _)
          (hT i h hij)
      · exact exists_computable_le_lowerFreq_sigma2_halts_mono (le_max_right _ _) ht
    · refine ⟨T, fun i hi hij => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact hT i h hij
      · exact absurd hij hu

open Classical in
/-- Step 1 of the proof of `exists_computable_le_lowerFreq_step1_sigma2`: a set
enumerable in `0'` has a computable stage test over finite prefixes of the characteristic
sequence of `0'` (the finite-prefix operator `Φ` of `exists_exact_string_operator`, with its
domain approximated by `IsRE.exists_stageApprox`): `w ∈ F` iff for some `u`, `s` the test
`D w σ s` succeeds on the true prefix `σ = χ_{0'} ↾ u`. -/
private theorem exists_computable_le_lowerFreq_stage {F : ℕ × ℚ → Prop}
    (hF : PointToSet.IsREIn jumpSet F) :
    ∃ D : ℕ × ℚ → List ℕ → ℕ → Bool,
      Computable (fun p : (ℕ × ℚ) × List ℕ × ℕ => D p.1 p.2.1 p.2.2) ∧
      ∀ w, F w ↔ ∃ u s,
        D w ((List.range u).map (fun n => if n ∈ jumpSet then 1 else 0)) s = true := by
  let : Encodable (ℕ × ℚ) := Primcodable.toEncodable
  obtain ⟨f, hf, hdom⟩ := hF
  have hor : ({charOracle jumpSet} : Set (ℕ →. ℕ)) =
      {totalOracle (fun n => if n ∈ jumpSet then 1 else 0)} := rfl
  have hdec : Computable (fun n : ℕ => (Encodable.decode (α := ℕ × ℚ) n).getD (0, 0)) :=
    Computable.option_getD Computable.decode (Computable.const _)
  have hg : PartrecIn {totalOracle (fun n => if n ∈ jumpSet then 1 else 0)}
      (fun n : ℕ => f ((Encodable.decode (α := ℕ × ℚ) n).getD (0, 0))) := by
    rw [← hor]
    exact hf.comp hdec.computableIn
  obtain ⟨Φ, hΦ, -, hex⟩ := PointToSet.exists_exact_string_operator _ _ hg
  have hre : IsRE (fun x : List ℕ × ℕ => (Φ x).Dom) :=
    ⟨fun x => (Φ x).map (fun _ => ()), hΦ.map (Computable.const ()).to₂, by intro x; simp⟩
  obtain ⟨chk, hchk, -, hiff⟩ := hre.exists_stageApprox
  refine ⟨fun w σ s => chk (σ, Encodable.encode w) s, ?_, fun w => ?_⟩
  · have h1 : Computable (fun p : (ℕ × ℚ) × List ℕ × ℕ => (p.2.1, Encodable.encode p.1)) :=
      Computable.pair
        (Computable.comp (α := (ℕ × ℚ) × List ℕ × ℕ) (σ := List ℕ) Computable.fst Computable.snd)
        (Computable.comp (Computable.encode (α := ℕ × ℚ)) Computable.fst)
    have h2 : Computable (fun p : (ℕ × ℚ) × List ℕ × ℕ =>
        ((p.2.1, Encodable.encode p.1), p.2.2)) :=
      Computable.pair h1 (Computable.snd.comp Computable.snd)
    have h3 := Computable.comp (f := fun q : (List ℕ × ℕ) × ℕ => chk q.1 q.2) hchk h2
    exact h3
  · rw [hdom]
    have e1 : ∀ v, v ∈ f w ↔
        v ∈ f ((Encodable.decode (α := ℕ × ℚ) (Encodable.encode w)).getD (0, 0)) := by
      intro v
      rw [Encodable.encodek]
      rfl
    constructor
    · intro hd
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hd
      obtain ⟨u, hu⟩ := (hex (Encodable.encode w) v).mp ((e1 v).mp hv)
      have : (Φ ((List.range u).map (fun n => if n ∈ jumpSet then 1 else 0),
          Encodable.encode w)).Dom := Part.dom_iff_mem.mpr ⟨v, hu⟩
      obtain ⟨s, hs⟩ := (hiff _).mp this
      exact ⟨u, s, hs⟩
    · rintro ⟨u, s, hs⟩
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp ((hiff _).mpr ⟨s, hs⟩)
      exact Part.dom_iff_mem.mpr ⟨v, (e1 v).mpr ((hex _ v).mpr ⟨u, hv⟩)⟩

open Classical in
/-- Step 2 of the proof of `exists_computable_le_lowerFreq_step1_sigma2`: from a
computable stage test `D` over prefixes of the characteristic sequence of `0'` to a `Σ₂`
representation. The code `a = ⟨u, s, T⟩` names the prefix length `u`, the step bound `s` and a
bound `T` on the halting times of all `i < u` in `0'`; `P (k, r, a, b)` checks that `D` succeeds
on the prefix read off `T`, and that every `i < u` not halting within `T` does not halt within
`b`. -/
private theorem exists_computable_le_lowerFreq_sigma2 {F : ℕ × ℚ → Prop}
    (D : ℕ × ℚ → List ℕ → ℕ → Bool)
    (hD : Computable (fun p : (ℕ × ℚ) × List ℕ × ℕ => D p.1 p.2.1 p.2.2))
    (hFD : ∀ w, F w ↔ ∃ u s,
      D w ((List.range u).map (fun n => if n ∈ jumpSet then 1 else 0)) s = true) :
    ∃ P : ℕ × ℚ × ℕ × ℕ → Bool, Computable P ∧
      ∀ (k : ℕ) (r : ℚ), F (k, r) ↔ ∃ a, ∀ b, P (k, r, a, b) = true := by
  let H := exists_computable_le_lowerFreq_sigma2_halts
  have hHp : Primrec (fun x : ℕ × ℕ => H x.1 x.2) :=
    exists_computable_le_lowerFreq_sigma2_halts_primrec
  have hHs : ∀ {i t : ℕ}, H i t = true → i ∈ jumpSet :=
    exists_computable_le_lowerFreq_sigma2_halts_sound
  have hHc : ∀ {i : ℕ}, i ∈ jumpSet → ∃ t, H i t = true :=
    exists_computable_le_lowerFreq_sigma2_halts_complete
  let P : ℕ × ℚ × ℕ × ℕ → Bool := fun p =>
    D (p.1, p.2.1) ((List.range (Nat.unpair p.2.2.1).1).map
        (fun i => cond (H i (Nat.unpair (Nat.unpair p.2.2.1).2).2) 1 0))
      (Nat.unpair (Nat.unpair p.2.2.1).2).1 &&
    decide (∀ i < (Nat.unpair p.2.2.1).1,
      (H i (Nat.unpair (Nat.unpair p.2.2.1).2).2 || !H i p.2.2.2) = true)
  have hP : Computable P := by
    have ha : Primrec (fun p : ℕ × ℚ × ℕ × ℕ => p.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hb : Primrec (fun p : ℕ × ℚ × ℕ × ℕ => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hu : Primrec (fun p : ℕ × ℚ × ℕ × ℕ => (Nat.unpair p.2.2.1).1) :=
      Primrec.fst.comp (Primrec.unpair.comp ha)
    have hs : Primrec (fun p : ℕ × ℚ × ℕ × ℕ => (Nat.unpair (Nat.unpair p.2.2.1).2).1) :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp ha)))
    have hT : Primrec (fun p : ℕ × ℚ × ℕ × ℕ => (Nat.unpair (Nat.unpair p.2.2.1).2).2) :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp ha)))
    have hlist : Primrec (fun p : ℕ × ℚ × ℕ × ℕ => (List.range (Nat.unpair p.2.2.1).1).map
        (fun i => cond (H i (Nat.unpair (Nat.unpair p.2.2.1).2).2) 1 0)) := by
      refine Primrec.list_map (Primrec.list_range.comp hu) ?_
      have h1 : Primrec (fun x : (ℕ × ℚ × ℕ × ℕ) × ℕ =>
          H x.2 (Nat.unpair (Nat.unpair x.1.2.2.1).2).2) :=
        hHp.comp (Primrec.snd.pair (hT.comp Primrec.fst))
      exact Primrec.cond h1 (Primrec.const 1) (Primrec.const 0)
    have hw : Primrec (fun p : ℕ × ℚ × ℕ × ℕ => (p.1, p.2.1)) :=
      Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
    have hDp : Computable (fun p : ℕ × ℚ × ℕ × ℕ =>
        D (p.1, p.2.1) ((List.range (Nat.unpair p.2.2.1).1).map
          (fun i => cond (H i (Nat.unpair (Nat.unpair p.2.2.1).2).2) 1 0))
        (Nat.unpair (Nat.unpair p.2.2.1).2).1) :=
      hD.comp (hw.to_comp.pair (hlist.to_comp.pair hs.to_comp))
    have hR : PrimrecRel (fun (i : ℕ) (y : ℕ) =>
        (H i (Nat.unpair y).1 || !H i (Nat.unpair y).2) = true) := by
      have hc : Primrec₂ (fun (i : ℕ) (y : ℕ) =>
          H i (Nat.unpair y).1 || !H i (Nat.unpair y).2) :=
        Primrec.or.comp
          (hHp.comp (Primrec.fst.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
          (Primrec.not.comp (hHp.comp
            (Primrec.fst.pair (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))
      exact Primrec.eq.comp hc (Primrec.const true)
    have hfa : PrimrecPred (fun p : ℕ × ℚ × ℕ × ℕ => ∀ i < (Nat.unpair p.2.2.1).1,
        (H i (Nat.unpair (Nat.unpair p.2.2.1).2).2 || !H i p.2.2.2) = true) :=
      PrimrecPred.of_eq (PrimrecRel.comp (R := fun (n : ℕ) (y : ℕ) => ∀ x < n,
        (H x (Nat.unpair y).1 || !H x (Nat.unpair y).2) = true)
        (PrimrecRel.forall_lt hR) hu (Primrec₂.natPair.comp hT hb))
        (fun p => by simp only [Nat.unpair_pair])
    have hfa' : Computable (fun p : ℕ × ℚ × ℕ × ℕ => decide (∀ i < (Nat.unpair p.2.2.1).1,
        (H i (Nat.unpair (Nat.unpair p.2.2.1).2).2 || !H i p.2.2.2) = true)) :=
      hfa.decide.to_comp
    have h3 := Computable.comp (f := fun q : Bool × Bool => q.1 && q.2) Primrec.and.to_comp
      (hDp.pair hfa')
    exact h3
  refine ⟨P, hP, fun k r => ?_⟩
  have hσ : ∀ u T : ℕ, (∀ i < u, (H i T = true ↔ i ∈ jumpSet)) →
      (List.range u).map (fun i => cond (H i T) 1 0) =
        (List.range u).map (fun n => if n ∈ jumpSet then 1 else 0) := by
    intro u T hiff
    refine List.map_congr_left fun i hi => ?_
    have hi' := hiff i (List.mem_range.mp hi)
    cases h : H i T
    · have : i ∉ jumpSet := fun hm => by
        have := hi'.mpr hm
        rw [h] at this
        exact Bool.false_ne_true this
      simp [this]
    · have : i ∈ jumpSet := hi'.mp h
      simp [this]
  rw [hFD (k, r)]
  constructor
  · rintro ⟨u, s, h⟩
    obtain ⟨T, hT⟩ := exists_computable_le_lowerFreq_sigma2_exists_bound u
    refine ⟨Nat.pair u (Nat.pair s T), fun b => ?_⟩
    have hiff : ∀ i < u, (H i T = true ↔ i ∈ jumpSet) :=
      fun i hi => ⟨hHs, hT i hi⟩
    simp only [P, Nat.unpair_pair, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hσ u T hiff]
      exact h
    · by_cases hij : i ∈ jumpSet
      · have h' : H i T = true := hT i hi hij
        rw [h']
        rfl
      · have : H i b = false := by
          cases hb : H i b
          · rfl
          · exact absurd (hHs hb) hij
        simp [this]
  · rintro ⟨a, ha⟩
    refine ⟨(Nat.unpair a).1, (Nat.unpair (Nat.unpair a).2).1, ?_⟩
    have ha' := fun b => by simpa only [P, Bool.and_eq_true, decide_eq_true_eq] using ha b
    have hiff : ∀ i < (Nat.unpair a).1,
        (H i (Nat.unpair (Nat.unpair a).2).2 = true ↔ i ∈ jumpSet) := by
      intro i hi
      refine ⟨hHs, fun hij => ?_⟩
      by_contra hnot
      obtain ⟨t, ht⟩ := hHc hij
      have := (ha' t).2 i hi
      rw [Bool.or_eq_true] at this
      rcases this with h1 | h1
      · exact hnot h1
      · simp [ht] at h1
    rw [← hσ _ _ hiff]
    exact (ha' 0).1

/-- Step 1 of the proof of `exists_computable_le_lowerFreq`: the `Σ₂` representation.
A `0'`-lower-semicomputable real sequence `q` has a computable Boolean predicate `P` such that
`r < qₖ` iff `∃ a, ∀ b, P (k, r, a, b)` (Post's theorem: sets enumerable in `0'` are `Σ₂`; the
request `(k, r, a)` is "make `qₖ` greater than `r`", cancelled at the first `b` with `P = false`).
-/
private theorem exists_computable_le_lowerFreq_step1_sigma2 {q : ℕ → ℝ}
    (hq : PointToSet.IsLowerSemicomputableIn jumpSet q) :
    ∃ P : ℕ × ℚ × ℕ × ℕ → Bool, Computable P ∧
      ∀ (k : ℕ) (r : ℚ), (r : ℝ) < q k ↔ ∃ a, ∀ b, P (k, r, a, b) = true := by
  obtain ⟨D, hD, hFD⟩ :=
    exists_computable_le_lowerFreq_stage
      (F := fun w : ℕ × ℚ => (w.2 : ℝ) < q w.1) hq
  exact exists_computable_le_lowerFreq_sigma2 D hD hFD

/-- Step 2 helper: the value of `k` in the log `st` of accepted requests `(k, r)` (newest first):
the maximum of `0` and the `r` of the entries with first component `k`. -/
private def exists_computable_le_lowerFreq_table_val (st : List (ℕ × ℚ)) (k : ℕ) : ℚ :=
  st.foldr (fun x acc => if x.1 = k then max x.2 acc else acc) 0

/-- Step 2 helper: the row sum of the log `st` over the indices `< n`. -/
private def exists_computable_le_lowerFreq_table_tot (n : ℕ) (st : List (ℕ × ℚ)) : ℚ :=
  (List.range n).foldr (fun k acc => exists_computable_le_lowerFreq_table_val st k + acc) 0

/-- Step 2 helper: one scanning step of row `n` on the request of code `m`. -/
private def exists_computable_le_lowerFreq_table_step (P : ℕ × ℚ × ℕ × ℕ → Bool) (n : ℕ)
    (st : List (ℕ × ℚ)) (m : ℕ) : List (ℕ × ℚ) :=
  cond (decide ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1 < n) &&
      (List.range (n + 1)).all (fun b => P ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1,
        (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.2, b)) &&
      decide (exists_computable_le_lowerFreq_table_tot n
        (((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1) :: st) ≤ 1))
    (((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1) :: st) st

/-- Step 2 helper: the log after scanning the requests of codes `< m` in row `n`. -/
private def exists_computable_le_lowerFreq_table_scan (P : ℕ × ℚ × ℕ × ℕ → Bool) (n : ℕ) :
    ℕ → List (ℕ × ℚ)
  | 0 => []
  | m + 1 => exists_computable_le_lowerFreq_table_step P n
      (exists_computable_le_lowerFreq_table_scan P n m) m

/-- Step 2 helper: the request of code `m` is alive at stage `n`. -/
private def exists_computable_le_lowerFreq_table_alive (P : ℕ × ℚ × ℕ × ℕ → Bool)
    (n m : ℕ) : Prop :=
  (Denumerable.ofNat (ℕ × ℚ × ℕ) m).1 < n ∧ ∀ b ≤ n,
    P ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1,
      (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.2, b) = true

private lemma exists_computable_le_lowerFreq_table_val_nil (k : ℕ) :
    exists_computable_le_lowerFreq_table_val [] k = 0 := rfl

private lemma exists_computable_le_lowerFreq_table_val_cons (x : ℕ × ℚ)
    (st : List (ℕ × ℚ)) (k : ℕ) :
    exists_computable_le_lowerFreq_table_val (x :: st) k =
      if x.1 = k then max x.2 (exists_computable_le_lowerFreq_table_val st k)
      else exists_computable_le_lowerFreq_table_val st k := rfl

private lemma exists_computable_le_lowerFreq_table_val_nonneg (st : List (ℕ × ℚ)) (k : ℕ) :
    0 ≤ exists_computable_le_lowerFreq_table_val st k := by
  induction st with
  | nil => simp [exists_computable_le_lowerFreq_table_val_nil]
  | cons x st ih =>
    rw [exists_computable_le_lowerFreq_table_val_cons]
    split_ifs
    · exact le_trans ih (le_max_right _ _)
    · exact ih

private lemma exists_computable_le_lowerFreq_table_val_zero (n : ℕ) (st : List (ℕ × ℚ))
    (hst : ∀ x ∈ st, x.1 < n) (k : ℕ) (hk : n ≤ k) :
    exists_computable_le_lowerFreq_table_val st k = 0 := by
  induction st with
  | nil => rfl
  | cons x st ih =>
    rw [exists_computable_le_lowerFreq_table_val_cons, ite_eq_right]
    · exact ih fun y hy => hst y (List.mem_cons_of_mem _ hy)
    · have := hst x List.mem_cons_self
      omega

private lemma exists_computable_le_lowerFreq_table_val_le_cons (x : ℕ × ℚ)
    (st : List (ℕ × ℚ)) (k : ℕ) :
    exists_computable_le_lowerFreq_table_val st k ≤
      exists_computable_le_lowerFreq_table_val (x :: st) k := by
  rw [exists_computable_le_lowerFreq_table_val_cons]
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

private lemma exists_computable_le_lowerFreq_table_le_val_cons (x : ℕ × ℚ)
    (st : List (ℕ × ℚ)) :
    x.2 ≤ exists_computable_le_lowerFreq_table_val (x :: st) x.1 := by
  rw [exists_computable_le_lowerFreq_table_val_cons, ite_eq_left rfl]
  exact le_max_left _ _

private lemma exists_computable_le_lowerFreq_table_val_le (st : List (ℕ × ℚ)) (k : ℕ)
    (c : ℝ) (hc : 0 ≤ c) (hst : ∀ x ∈ st, x.1 = k → (x.2 : ℝ) ≤ c) :
    (exists_computable_le_lowerFreq_table_val st k : ℝ) ≤ c := by
  induction st with
  | nil => simpa [exists_computable_le_lowerFreq_table_val_nil] using hc
  | cons x st ih =>
    have ih' := ih fun y hy => hst y (List.mem_cons_of_mem _ hy)
    rw [exists_computable_le_lowerFreq_table_val_cons]
    split_ifs with h
    · push_cast
      exact max_le (hst x List.mem_cons_self h) ih'
    · exact ih'

private lemma exists_computable_le_lowerFreq_table_foldr_sum (f : ℕ → ℚ) (n : ℕ) (c : ℚ) :
    (List.range n).foldr (fun k acc => f k + acc) c = ∑ k ∈ Finset.range n, f k + c := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, Finset.sum_range_succ]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [ih]; ring

private lemma exists_computable_le_lowerFreq_table_tot_eq (n : ℕ) (st : List (ℕ × ℚ)) :
    exists_computable_le_lowerFreq_table_tot n st =
      ∑ k ∈ Finset.range n, exists_computable_le_lowerFreq_table_val st k := by
  unfold exists_computable_le_lowerFreq_table_tot
  rw [exists_computable_le_lowerFreq_table_foldr_sum]; simp

open Classical in
private lemma exists_computable_le_lowerFreq_table_step_eq
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (n : ℕ) (st : List (ℕ × ℚ)) (m : ℕ) :
    exists_computable_le_lowerFreq_table_step P n st m =
      if exists_computable_le_lowerFreq_table_alive P n m ∧
          exists_computable_le_lowerFreq_table_tot n
            (((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1) :: st)
              ≤ 1
        then ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1) :: st
        else st := by
  classical
  unfold exists_computable_le_lowerFreq_table_step
    exists_computable_le_lowerFreq_table_alive
  by_cases h : ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1 < n ∧ ∀ b ≤ n,
    P ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1,
      (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.2, b) = true) ∧
      exists_computable_le_lowerFreq_table_tot n
        (((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1) :: st) ≤ 1
  · rw [ite_eq_left h]
    have : (decide ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1 < n) &&
      (List.range (n + 1)).all (fun b => P ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1,
        (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.2, b)) &&
      decide (exists_computable_le_lowerFreq_table_tot n
        (((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1) :: st) ≤ 1))
        = true := by
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      exact ⟨⟨h1, fun b hb => h2 b (by omega)⟩, h3⟩
    rw [this]; rfl
  · rw [ite_eq_right h]
    have : ¬ (decide ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1 < n) &&
      (List.range (n + 1)).all (fun b => P ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1,
        (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.2, b)) &&
      decide (exists_computable_le_lowerFreq_table_tot n
        (((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1) :: st) ≤ 1))
        = true := by
      intro hh
      apply h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hh
      obtain ⟨⟨h1, h2⟩, h3⟩ := hh
      exact ⟨⟨h1, fun b hb => h2 b (by omega)⟩, h3⟩
    rw [Bool.not_eq_true] at this
    rw [this]; rfl

open Classical in
private lemma exists_computable_le_lowerFreq_table_scan_succ
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (n m : ℕ) :
    exists_computable_le_lowerFreq_table_scan P n (m + 1) =
      if exists_computable_le_lowerFreq_table_alive P n m ∧
          exists_computable_le_lowerFreq_table_tot n
            (((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1) ::
              exists_computable_le_lowerFreq_table_scan P n m) ≤ 1
        then ((Denumerable.ofNat (ℕ × ℚ × ℕ) m).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m).2.1) ::
          exists_computable_le_lowerFreq_table_scan P n m
        else exists_computable_le_lowerFreq_table_scan P n m := by
  rw [exists_computable_le_lowerFreq_table_scan,
    exists_computable_le_lowerFreq_table_step_eq]

private lemma exists_computable_le_lowerFreq_table_mem_scan
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (n : ℕ) (m : ℕ) :
    ∀ x ∈ exists_computable_le_lowerFreq_table_scan P n m, ∃ m' < m,
      exists_computable_le_lowerFreq_table_alive P n m' ∧
        x = ((Denumerable.ofNat (ℕ × ℚ × ℕ) m').1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m').2.1) := by
  classical
  induction m with
  | zero => intro x hx; simp [exists_computable_le_lowerFreq_table_scan] at hx
  | succ m ih =>
    intro x hx
    rw [exists_computable_le_lowerFreq_table_scan_succ] at hx
    split_ifs at hx with h
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨m, Nat.lt_succ_self m, h.1, rfl⟩
      · obtain ⟨m', hm', h'⟩ := ih x hx
        exact ⟨m', Nat.lt_succ_of_lt hm', h'⟩
    · obtain ⟨m', hm', h'⟩ := ih x hx
      exact ⟨m', Nat.lt_succ_of_lt hm', h'⟩

private lemma exists_computable_le_lowerFreq_table_tot_scan
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (n : ℕ) (m : ℕ) :
    exists_computable_le_lowerFreq_table_tot n
      (exists_computable_le_lowerFreq_table_scan P n m) ≤ 1 := by
  classical
  induction m with
  | zero =>
    simp [exists_computable_le_lowerFreq_table_scan,
      exists_computable_le_lowerFreq_table_tot_eq,
      exists_computable_le_lowerFreq_table_val_nil]
  | succ m ih =>
    rw [exists_computable_le_lowerFreq_table_scan_succ]
    split_ifs with h
    · exact h.2
    · exact ih

private lemma exists_computable_le_lowerFreq_table_scan_mono
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (n k : ℕ) {m m' : ℕ} (h : m ≤ m') :
    exists_computable_le_lowerFreq_table_val
        (exists_computable_le_lowerFreq_table_scan P n m) k ≤
      exists_computable_le_lowerFreq_table_val
        (exists_computable_le_lowerFreq_table_scan P n m') k := by
  classical
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    rw [exists_computable_le_lowerFreq_table_scan_succ]
    split_ifs
    · exact exists_computable_le_lowerFreq_table_val_le_cons _ _ _
    · exact le_rfl

private lemma exists_computable_le_lowerFreq_table_scan_lt
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (n m : ℕ) :
    ∀ x ∈ exists_computable_le_lowerFreq_table_scan P n m, x.1 < n := by
  intro x hx
  obtain ⟨m', -, h, rfl⟩ := exists_computable_le_lowerFreq_table_mem_scan P n m x hx
  exact h.1

private lemma exists_computable_le_lowerFreq_table_comp_max :
    Computable₂ (fun a b : ℚ => max a b) := by
  have hle := isLowerSemicomputableIn_jumpSet_liminf_ratLe
  exact (Computable.cond hle Computable.snd Computable.fst).of_eq fun p => by
    simp only [max_def]
    split_ifs with h <;> simp [h]

private lemma exists_computable_le_lowerFreq_table_comp_val :
    Computable (fun p : List (ℕ × ℚ) × ℕ =>
      exists_computable_le_lowerFreq_table_val p.1 p.2) := by
  have hmax := exists_computable_le_lowerFreq_table_comp_max
  have hh : Computable₂ (fun (p : List (ℕ × ℚ) × ℕ) (u : (ℕ × ℚ) × ℚ) =>
      cond (decide (u.1.1 = p.2)) (max u.1.2 u.2) u.2) := by
    refine Computable.cond ?_ ?_ ?_
    · exact (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)).decide.to_comp
    · exact hmax.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd)
    · exact Computable.snd.comp Computable.snd
  refine (Computable.list_foldr Computable.fst (Computable.const (0 : ℚ)) hh).of_eq fun p => ?_
  unfold exists_computable_le_lowerFreq_table_val
  congr 1
  funext x acc
  by_cases h : x.1 = p.2 <;> simp [h]

private lemma exists_computable_le_lowerFreq_table_comp_tot :
    Computable (fun p : ℕ × List (ℕ × ℚ) =>
      exists_computable_le_lowerFreq_table_tot p.1 p.2) := by
  have hv := exists_computable_le_lowerFreq_table_comp_val
  have h1 : Computable (fun a : (ℕ × List (ℕ × ℚ)) × (ℕ × ℚ) =>
      exists_computable_le_lowerFreq_table_val a.1.2 a.2.1) :=
    hv.comp (g := fun a : (ℕ × List (ℕ × ℚ)) × (ℕ × ℚ) => (a.1.2, a.2.1))
      (Computable.pair (Computable.snd.comp Computable.fst) (Computable.fst.comp Computable.snd))
  have h2 : Computable (fun a : (ℕ × List (ℕ × ℚ)) × (ℕ × ℚ) => a.2.2) :=
    Computable.snd.comp Computable.snd
  have hh : Computable₂ (fun (p : ℕ × List (ℕ × ℚ)) (u : ℕ × ℚ) =>
      exists_computable_le_lowerFreq_table_val p.2 u.1 + u.2) :=
    computable₂_ratAdd.comp h1 h2
  exact (Computable.list_foldr (Primrec.list_range.to_comp.comp Computable.fst)
    (Computable.const (0 : ℚ)) hh).of_eq fun p => rfl

private lemma exists_computable_le_lowerFreq_table_all_eq (l : List ℕ) (p : ℕ → Bool) :
    l.all p = l.foldr (fun a b => p a && b) true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private lemma exists_computable_le_lowerFreq_table_comp_step_all
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (hPc : Computable P) (R : ℕ → ℕ × ℚ × ℕ) (hR : Computable R) :
    Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ =>
      (List.range (a.1 + 1)).all (fun b => P ((R a.2.2).1, (R a.2.2).2.1, (R a.2.2).2.2, b))) := by
  have hreq : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => R a.2.2) :=
    hR.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => (R a.2.2).1) :=
    Computable.fst.comp hreq
  have hr : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => (R a.2.2).2.1) :=
    Computable.fst.comp (Computable.snd.comp hreq)
  have ha : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => (R a.2.2).2.2) :=
    Computable.snd.comp (Computable.snd.comp hreq)
  have hp : Computable (fun u : (ℕ × List (ℕ × ℚ) × ℕ) × (ℕ × Bool) =>
      P ((R u.1.2.2).1, (R u.1.2.2).2.1, (R u.1.2.2).2.2, u.2.1)) :=
    hPc.comp (g := fun u : (ℕ × List (ℕ × ℚ) × ℕ) × (ℕ × Bool) =>
        ((R u.1.2.2).1, (R u.1.2.2).2.1, (R u.1.2.2).2.2, u.2.1))
      (Computable.pair (hk.comp Computable.fst) (Computable.pair
        (hr.comp Computable.fst) (Computable.pair (ha.comp Computable.fst)
          (Computable.fst.comp Computable.snd))))
  have hh : Computable₂ (fun (a : ℕ × List (ℕ × ℚ) × ℕ) (u : ℕ × Bool) =>
      P ((R a.2.2).1, (R a.2.2).2.1, (R a.2.2).2.2, u.1) && u.2) :=
    Primrec.and.to_comp.comp hp (Computable.snd.comp Computable.snd)
  refine (Computable.list_foldr (Primrec.list_range.to_comp.comp
    (Primrec.succ.to_comp.comp Computable.fst)) (Computable.const true) hh).of_eq fun a => ?_
  rw [exists_computable_le_lowerFreq_table_all_eq]

private lemma exists_computable_le_lowerFreq_table_comp_step_tot
    (R : ℕ → ℕ × ℚ × ℕ) (hR : Computable R) :
    Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ =>
      decide (exists_computable_le_lowerFreq_table_tot a.1
        (((R a.2.2).1, (R a.2.2).2.1) :: a.2.1) ≤ 1)) := by
  have hreq : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => R a.2.2) :=
    hR.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => (R a.2.2).1) :=
    Computable.fst.comp hreq
  have hr : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => (R a.2.2).2.1) :=
    Computable.fst.comp (Computable.snd.comp hreq)
  have hn : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => a.1) := Computable.fst
  have hst : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hcand : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ =>
      (((R a.2.2).1, (R a.2.2).2.1) :: a.2.1)) :=
    Computable.list_cons.comp (Computable.pair hk hr) hst
  have htot : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ =>
      exists_computable_le_lowerFreq_table_tot a.1
        (((R a.2.2).1, (R a.2.2).2.1) :: a.2.1)) :=
    exists_computable_le_lowerFreq_table_comp_tot.comp
      (g := fun a : ℕ × List (ℕ × ℚ) × ℕ => (a.1, ((R a.2.2).1, (R a.2.2).2.1) :: a.2.1))
      (Computable.pair hn hcand)
  exact computable_ratLeOne.comp (g := fun a : ℕ × List (ℕ × ℚ) × ℕ =>
      exists_computable_le_lowerFreq_table_tot a.1
        (((R a.2.2).1, (R a.2.2).2.1) :: a.2.1)) htot

private lemma exists_computable_le_lowerFreq_table_comp_step_lt
    (R : ℕ → ℕ × ℚ × ℕ) (hR : Computable R) :
    Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => decide ((R a.2.2).1 < a.1)) := by
  have hreq : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => R a.2.2) :=
    hR.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => (R a.2.2).1) :=
    Computable.fst.comp hreq
  have hn : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => a.1) := Computable.fst
  have hlt : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) :=
    Primrec.nat_lt.decide.to_comp
  exact hlt.comp (g := fun a : ℕ × List (ℕ × ℚ) × ℕ => ((R a.2.2).1, a.1))
    (Computable.pair hk hn)

private lemma exists_computable_le_lowerFreq_table_comp_step_guard
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (hPc : Computable P) (R : ℕ → ℕ × ℚ × ℕ) (hR : Computable R) :
    Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ =>
      decide ((R a.2.2).1 < a.1) &&
        (List.range (a.1 + 1)).all (fun b => P ((R a.2.2).1, (R a.2.2).2.1, (R a.2.2).2.2, b)) &&
        decide (exists_computable_le_lowerFreq_table_tot a.1
          (((R a.2.2).1, (R a.2.2).2.1) :: a.2.1) ≤ 1)) :=
  Primrec.and.to_comp.comp
    (Primrec.and.to_comp.comp (exists_computable_le_lowerFreq_table_comp_step_lt R hR)
      (exists_computable_le_lowerFreq_table_comp_step_all P hPc R hR))
    (exists_computable_le_lowerFreq_table_comp_step_tot R hR)

private lemma exists_computable_le_lowerFreq_table_comp_step_aux
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (hPc : Computable P) (R : ℕ → ℕ × ℚ × ℕ) (hR : Computable R) :
    Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ =>
      cond (decide ((R a.2.2).1 < a.1) &&
        (List.range (a.1 + 1)).all (fun b => P ((R a.2.2).1, (R a.2.2).2.1, (R a.2.2).2.2, b)) &&
        decide (exists_computable_le_lowerFreq_table_tot a.1
          (((R a.2.2).1, (R a.2.2).2.1) :: a.2.1) ≤ 1))
      (((R a.2.2).1, (R a.2.2).2.1) :: a.2.1) a.2.1) := by
  have hreq : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => R a.2.2) :=
    hR.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => (R a.2.2).1) :=
    Computable.fst.comp hreq
  have hr : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => (R a.2.2).2.1) :=
    Computable.fst.comp (Computable.snd.comp hreq)
  have hst : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hcand : Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ =>
      (((R a.2.2).1, (R a.2.2).2.1) :: a.2.1)) :=
    Computable.list_cons.comp (Computable.pair hk hr) hst
  exact Computable.cond (exists_computable_le_lowerFreq_table_comp_step_guard P hPc R hR)
    hcand hst

private lemma exists_computable_le_lowerFreq_table_comp_step
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (hPc : Computable P) :
    Computable (fun a : ℕ × List (ℕ × ℚ) × ℕ =>
      exists_computable_le_lowerFreq_table_step P a.1 a.2.1 a.2.2) :=
  exists_computable_le_lowerFreq_table_comp_step_aux P hPc _
    (Computable.ofNat (ℕ × ℚ × ℕ))

private lemma exists_computable_le_lowerFreq_table_comp_scan
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (hPc : Computable P) :
    Computable (fun a : ℕ × ℕ => exists_computable_le_lowerFreq_table_scan P a.1 a.2) := by
  have hs := exists_computable_le_lowerFreq_table_comp_step P hPc
  have hh : Computable₂ (fun (a : ℕ × ℕ) (u : ℕ × List (ℕ × ℚ)) =>
      exists_computable_le_lowerFreq_table_step P a.1 u.2 u.1) :=
    hs.comp (g := fun v : (ℕ × ℕ) × (ℕ × List (ℕ × ℚ)) => (v.1.1, v.2.2, v.2.1))
      (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.snd.comp Computable.snd) (Computable.fst.comp Computable.snd)))
  refine (Computable.nat_rec (f := fun a : ℕ × ℕ => a.2) (g := fun _ => ([] : List (ℕ × ℚ)))
    Computable.snd (Computable.const []) hh).of_eq fun a => ?_
  obtain ⟨n, m⟩ := a
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (fun s => exists_computable_le_lowerFreq_table_step P n s m)
                   ih

/-- The mathematical part of the table (all but computability). -/
private lemma exists_computable_le_lowerFreq_table_math {q : ℕ → ℝ}
    (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ N, ∑ i ∈ Finset.range N, q i ≤ 1)
    (P : ℕ × ℚ × ℕ × ℕ → Bool)
    (hP : ∀ (k : ℕ) (r : ℚ), (r : ℝ) < q k ↔ ∃ a, ∀ b, P (k, r, a, b) = true) :
    (∀ n k, 0 ≤ exists_computable_le_lowerFreq_table_val
        (exists_computable_le_lowerFreq_table_scan P n n) k) ∧
    (∀ n k, n ≤ k → exists_computable_le_lowerFreq_table_val
        (exists_computable_le_lowerFreq_table_scan P n n) k = 0) ∧
    (∀ n N, ∑ k ∈ Finset.range N, exists_computable_le_lowerFreq_table_val
        (exists_computable_le_lowerFreq_table_scan P n n) k ≤ 1) ∧
    ∀ (k : ℕ) (r : ℚ), (r : ℝ) < q k → ∀ᶠ n in Filter.atTop,
      r ≤ exists_computable_le_lowerFreq_table_val
        (exists_computable_le_lowerFreq_table_scan P n n) k := by
  classical
  refine ⟨fun n k => exists_computable_le_lowerFreq_table_val_nonneg _ _,
    fun n k hk => exists_computable_le_lowerFreq_table_val_zero n _
      (exists_computable_le_lowerFreq_table_scan_lt P n n) k hk, ?_, ?_⟩
  · intro n N
    have htot := exists_computable_le_lowerFreq_table_tot_scan P n n
    rw [exists_computable_le_lowerFreq_table_tot_eq] at htot
    refine le_trans ?_ htot
    rcases le_total N n with hNn | hnN
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNn) fun i _ _ =>
        exists_computable_le_lowerFreq_table_val_nonneg _ _
    · refine le_of_eq (Finset.sum_subset (Finset.range_mono hnN) fun i hi hi' => ?_).symm
      exact exists_computable_le_lowerFreq_table_val_zero n _
        (exists_computable_le_lowerFreq_table_scan_lt P n n) i
        (by simpa using hi')
  · intro k r hr
    obtain ⟨a, ha⟩ := (hP k r).1 hr
    obtain ⟨m0, hreq⟩ : ∃ m0 : ℕ, Denumerable.ofNat (ℕ × ℚ × ℕ) m0 = (k, r, a) :=
      ⟨Denumerable.eqv (ℕ × ℚ × ℕ) (k, r, a),
        (Denumerable.eqv (ℕ × ℚ × ℕ)).symm_apply_apply (k, r, a)⟩
    have hev : ∀ᶠ n in Filter.atTop, ∀ m' ∈ Finset.range m0,
        exists_computable_le_lowerFreq_table_alive P n m' →
          ((Denumerable.ofNat (ℕ × ℚ × ℕ) m').2.1 : ℝ) <
            q (Denumerable.ofNat (ℕ × ℚ × ℕ) m').1 := by
      rw [Filter.eventually_all_finset]
      intro m' _
      by_cases hall : ∀ b, P ((Denumerable.ofNat (ℕ × ℚ × ℕ) m').1,
          (Denumerable.ofNat (ℕ × ℚ × ℕ) m').2.1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m').2.2, b)
            = true
      · exact Filter.Eventually.of_forall fun n _ => (hP _ _).2 ⟨_, hall⟩
      · push Not at hall
        obtain ⟨b, hb⟩ := hall
        filter_upwards [Filter.eventually_ge_atTop b] with n hn halive
        exact absurd (halive.2 b hn) (by simpa using hb)
    filter_upwards [hev, Filter.eventually_gt_atTop m0, Filter.eventually_gt_atTop k]
      with n hn hn1 hn2
    have hmem := exists_computable_le_lowerFreq_table_mem_scan P n m0
    have hlt : ∀ x ∈ exists_computable_le_lowerFreq_table_scan P n m0,
        (x.2 : ℝ) < q x.1 := by
      intro x hx
      obtain ⟨m', hm', hal, rfl⟩ := hmem x hx
      exact hn m' (Finset.mem_range.2 hm') hal
    have halive : exists_computable_le_lowerFreq_table_alive P n m0 := by
      refine ⟨by rw [hreq]; exact hn2, fun b _ => ?_⟩
      rw [hreq]; exact ha b
    set st0 := exists_computable_le_lowerFreq_table_scan P n m0 with hst0
    have hcand : exists_computable_le_lowerFreq_table_tot n
        (((Denumerable.ofNat (ℕ × ℚ × ℕ) m0).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m0).2.1) :: st0)
          ≤ 1 := by
      rw [hreq]
      rw [exists_computable_le_lowerFreq_table_tot_eq]
      have hq1 := h1 n
      have : (∑ j ∈ Finset.range n,
          (exists_computable_le_lowerFreq_table_val ((k, r) :: st0) j : ℝ)) ≤
            ∑ j ∈ Finset.range n, q j := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine exists_computable_le_lowerFreq_table_val_le _ _ _ (h0 j) ?_
        intro x hx hxj
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [← hxj]; exact hr.le
        · rw [← hxj]; exact (hlt x hx).le
      have h2 : ((∑ j ∈ Finset.range n,
          exists_computable_le_lowerFreq_table_val ((k, r) :: st0) j : ℚ) : ℝ) ≤ 1 := by
        rw [Rat.cast_sum]; exact this.trans hq1
      dsimp only
      exact_mod_cast h2
    have hs : exists_computable_le_lowerFreq_table_scan P n (m0 + 1) =
        ((Denumerable.ofNat (ℕ × ℚ × ℕ) m0).1, (Denumerable.ofNat (ℕ × ℚ × ℕ) m0).2.1) :: st0 := by
      rw [exists_computable_le_lowerFreq_table_scan_succ, ite_eq_left ⟨halive, hcand⟩]
    have hmono := exists_computable_le_lowerFreq_table_scan_mono P n k
      (Nat.succ_le_of_lt hn1)
    refine le_trans ?_ hmono
    rw [hs, hreq]
    exact exists_computable_le_lowerFreq_table_le_val_cons (k, r) st0

/-- Step 2 of the proof of `exists_computable_le_lowerFreq`: the table of rational
measures. Given the `Σ₂` representation `P` of `q` (with `q ≥ 0` and `∑ qᵢ ≤ 1`), there is a
computable table `p (n, k)` of non-negative rationals, row `n` supported on `k < n` with
`∑ₖ p (n, k) ≤ 1`, such that for every `k` and rational `r < qₖ` eventually `r ≤ p (n, k)`.
(Row `n`: scan the requests `(k, r, a)` with code `< n` that have not been cancelled up to
stage `n`, by age, setting `pₖ := max pₖ r` whenever the row sum stays `≤ 1`. A request that is
never cancelled is eventually preceded only by never-cancelled older requests, whose total is
at most `∑ qᵢ ≤ 1`.) -/
private theorem exists_computable_le_lowerFreq_table {q : ℕ → ℝ}
    (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ N, ∑ i ∈ Finset.range N, q i ≤ 1)
    (P : ℕ × ℚ × ℕ × ℕ → Bool) (hPc : Computable P)
    (hP : ∀ (k : ℕ) (r : ℚ), (r : ℝ) < q k ↔ ∃ a, ∀ b, P (k, r, a, b) = true) :
    ∃ p : ℕ × ℕ → ℚ, Computable p ∧ (∀ n k, 0 ≤ p (n, k)) ∧ (∀ n k, n ≤ k → p (n, k) = 0) ∧
      (∀ n N, ∑ k ∈ Finset.range N, p (n, k) ≤ 1) ∧
      ∀ (k : ℕ) (r : ℚ), (r : ℝ) < q k → ∀ᶠ n in Filter.atTop, r ≤ p (n, k) := by
  obtain ⟨hnn, hzero, hsum, hev⟩ := exists_computable_le_lowerFreq_table_math h0 h1 P hP
  refine ⟨fun nk => exists_computable_le_lowerFreq_table_val
    (exists_computable_le_lowerFreq_table_scan P nk.1 nk.1) nk.2, ?_, hnn, hzero, hsum, hev⟩
  have hsc := exists_computable_le_lowerFreq_table_comp_scan P hPc
  have hd : Computable (fun nk : ℕ × ℕ => (nk.1, nk.1)) :=
    Computable.pair Computable.fst Computable.fst
  have hscd : Computable (fun nk : ℕ × ℕ =>
      exists_computable_le_lowerFreq_table_scan P nk.1 nk.1) :=
    hsc.comp (g := fun nk : ℕ × ℕ => (nk.1, nk.1)) hd
  exact exists_computable_le_lowerFreq_table_comp_val.comp
    (g := fun nk : ℕ × ℕ => (exists_computable_le_lowerFreq_table_scan P nk.1 nk.1, nk.2))
    (Computable.pair hscd Computable.snd)

private def exists_computable_le_lowerFreq_construct_cDf (p : ℕ × ℕ → ℚ)
    (n m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 1 (fun k acc => acc * (p (n, k)).den) m

private def exists_computable_le_lowerFreq_construct_cD (p : ℕ × ℕ → ℚ) (n : ℕ) :
    ℕ := exists_computable_le_lowerFreq_construct_cDf p n n

private def exists_computable_le_lowerFreq_construct_cA (p : ℕ × ℕ → ℚ) (n k : ℕ)
    : ℕ := (p (n, k)).num.natAbs * (exists_computable_le_lowerFreq_construct_cD p
    n / (p (n, k)).den)

private def exists_computable_le_lowerFreq_construct_cC (p : ℕ × ℕ → ℚ) (n k : ℕ)
    : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => acc + exists_computable_le_lowerFreq_construct_cA p
                                                   n j) k

private def exists_computable_le_lowerFreq_construct_cWf (p : ℕ × ℕ → ℚ)
    (n t m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc +
                                                   if exists_computable_le_lowerFreq_construct_cC p
                                                   n (k + 1) ≤ t then 1 else 0) m

private def exists_computable_le_lowerFreq_construct_cW (p : ℕ × ℕ → ℚ) (n t : ℕ)
    : ℕ := exists_computable_le_lowerFreq_construct_cWf p n t n

private def exists_computable_le_lowerFreq_construct_cS (p : ℕ × ℕ → ℚ) (n : ℕ) :
    ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun m acc => acc + exists_computable_le_lowerFreq_construct_cD p
                                                   m * ((m + 1) *
                                                   exists_computable_le_lowerFreq_construct_cD p (m
                                                   + 1))) n

private def exists_computable_le_lowerFreq_construct_cIdx (p : ℕ × ℕ → ℚ) (i : ℕ)
    : ℕ := Nat.findGreatest (fun n => exists_computable_le_lowerFreq_construct_cS
                                        p n ≤ i) i

private def exists_computable_le_lowerFreq_construct_cF (p : ℕ × ℕ → ℚ) (i : ℕ) :
    ℕ :=
  exists_computable_le_lowerFreq_construct_cW p (exists_computable_le_lowerFreq_construct_cIdx p i)
      ((i - exists_computable_le_lowerFreq_construct_cS p
      (exists_computable_le_lowerFreq_construct_cIdx p i)) %
      exists_computable_le_lowerFreq_construct_cD p (exists_computable_le_lowerFreq_construct_cIdx p
      i))

-- computability
private lemma exists_computable_le_lowerFreq_construct_cDf_comp (p : ℕ × ℕ → ℚ)
    (hpc : Computable p) :
    Computable (fun x : ℕ × ℕ => exists_computable_le_lowerFreq_construct_cDf p
                                   x.1 x.2) := by
  have hden : Computable (fun x : (ℕ × ℕ) × (ℕ × ℕ) => (p (x.1.1, x.2.1)).den) :=
    computable_ratDen.comp (hpc.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd)))
  have hh : Computable₂ (fun (x : ℕ × ℕ) (u : ℕ × ℕ) => u.2 * (p (x.1, u.1)).den) :=
    (Primrec.nat_mul.to_comp.comp (Computable.snd.comp Computable.snd) hden).to₂
  exact Computable.nat_rec (f := fun x : ℕ × ℕ => x.2) (g := fun _ => (1 : ℕ))
    (h := fun (x : ℕ × ℕ) (u : ℕ × ℕ) => u.2 * (p (x.1, u.1)).den)
    Computable.snd (Computable.const 1) hh

private lemma exists_computable_le_lowerFreq_construct_cD_comp (p : ℕ × ℕ → ℚ)
    (hpc : Computable p) : Computable
    (exists_computable_le_lowerFreq_construct_cD p) :=
  (exists_computable_le_lowerFreq_construct_cDf_comp p hpc).comp
      (Computable.pair Computable.id Computable.id)

private lemma exists_computable_le_lowerFreq_construct_cA_comp (p : ℕ × ℕ → ℚ)
    (hpc : Computable p) :
    Computable (fun x : ℕ × ℕ => exists_computable_le_lowerFreq_construct_cA p
                                   x.1 x.2) := by
  have h1 : Computable (fun x : ℕ × ℕ => (p x).num.natAbs) :=
    ComputableReals.primrec_intNatAbs.to_comp.comp (computable_ratNum.comp hpc)
  have h2 : Computable (fun x : ℕ × ℕ =>
    exists_computable_le_lowerFreq_construct_cD p x.1 / (p x).den) :=
    Primrec.nat_div.to_comp.comp ((exists_computable_le_lowerFreq_construct_cD_comp p hpc).comp
        Computable.fst)
      (computable_ratDen.comp hpc)
  exact (Primrec.nat_mul.to_comp.comp h1 h2).of_eq fun x => rfl

private lemma exists_computable_le_lowerFreq_construct_cC_comp (p : ℕ × ℕ → ℚ)
    (hpc : Computable p) :
    Computable (fun x : ℕ × ℕ => exists_computable_le_lowerFreq_construct_cC p
                                   x.1 x.2) := by
  have hh : Computable₂ (fun (x : ℕ × ℕ) (u : ℕ × ℕ) =>
      u.2 + exists_computable_le_lowerFreq_construct_cA p x.1 u.1) :=
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      ((exists_computable_le_lowerFreq_construct_cA_comp p hpc).comp
          (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)))).to₂
  exact Computable.nat_rec (f := fun x : ℕ × ℕ => x.2) (g := fun _ => (0 : ℕ))
    (h := fun (x : ℕ × ℕ) (u : ℕ × ℕ) => u.2 + exists_computable_le_lowerFreq_construct_cA p x.1
                                           u.1)
    Computable.snd (Computable.const 0) hh

private lemma exists_computable_le_lowerFreq_construct_cWf_eq_cond (p : ℕ × ℕ →
    ℚ) (n t m : ℕ) :
    exists_computable_le_lowerFreq_construct_cWf p n t m = Nat.rec
        (motive := fun _ => ℕ) 0
      (fun k acc => acc +
                      cond (decide (exists_computable_le_lowerFreq_construct_cC p
                      n (k + 1) ≤ t)) 1 0) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change exists_computable_le_lowerFreq_construct_cWf p n t m + _ = _ + _
    rw [ih]; simp

private lemma exists_computable_le_lowerFreq_construct_cW_comp (p : ℕ × ℕ → ℚ)
    (hpc : Computable p) :
    Computable (fun x : ℕ × ℕ => exists_computable_le_lowerFreq_construct_cW p
                                   x.1 x.2) := by
  have hle2 : Computable₂ (fun a b : ℕ => decide (a ≤ b)) :=
    (Primrec.nat_le.comp Primrec.fst Primrec.snd).decide.to₂.to_comp
  have hle : Computable (fun y : ((ℕ × ℕ) × (ℕ × ℕ)) =>
      decide (exists_computable_le_lowerFreq_construct_cC p y.1.1 (y.2.1 + 1) ≤
          y.1.2)) :=
    hle2.comp
      ((exists_computable_le_lowerFreq_construct_cC_comp p hpc).comp
          (Computable.pair (Computable.fst.comp Computable.fst)
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))))
      (Computable.snd.comp Computable.fst)
  have hh : Computable₂ (fun (x : ℕ × ℕ) (u : ℕ × ℕ) =>
      u.2 + cond (decide (exists_computable_le_lowerFreq_construct_cC p x.1
          (u.1 + 1) ≤ x.2)) 1 0) :=
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.cond hle (Computable.const 1) (Computable.const 0))).to₂
  have h := Computable.nat_rec (f := fun x : ℕ × ℕ => x.1) (g := fun _ => (0 : ℕ))
    (h := fun (x : ℕ × ℕ) (u : ℕ × ℕ) =>
      u.2 + cond (decide (exists_computable_le_lowerFreq_construct_cC p x.1
          (u.1 + 1) ≤ x.2)) 1 0)
    Computable.fst (Computable.const 0) hh
  exact h.of_eq fun x => (exists_computable_le_lowerFreq_construct_cWf_eq_cond p
                           x.1 x.2 x.1).symm

private lemma exists_computable_le_lowerFreq_construct_cS_comp (p : ℕ × ℕ → ℚ)
    (hpc : Computable p) : Computable
    (exists_computable_le_lowerFreq_construct_cS p) := by
  have hD := exists_computable_le_lowerFreq_construct_cD_comp p hpc
  have hu1 : Computable (fun x : ℕ × (ℕ × ℕ) => x.2.1) := Computable.fst.comp Computable.snd
  have hu2 : Computable (fun x : ℕ × (ℕ × ℕ) => x.2.2) := Computable.snd.comp Computable.snd
  have hh : Computable₂ (fun (_ : ℕ) (u : ℕ × ℕ) =>
      u.2 + exists_computable_le_lowerFreq_construct_cD p u.1 *
          ((u.1 + 1) * exists_computable_le_lowerFreq_construct_cD p (u.1 + 1)))
          :=
    (Primrec.nat_add.to_comp.comp hu2
      (Primrec.nat_mul.to_comp.comp (hD.comp hu1)
        (Primrec.nat_mul.to_comp.comp (Primrec.succ.to_comp.comp hu1)
          (hD.comp (Primrec.succ.to_comp.comp hu1))))).to₂
  exact Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ => (0 : ℕ))
    (h := fun (_ : ℕ) (u : ℕ × ℕ) => u.2 + exists_computable_le_lowerFreq_construct_cD p u.1 *
                                       ((u.1 + 1) * exists_computable_le_lowerFreq_construct_cD p
                                       (u.1 + 1)))
    Computable.id (Computable.const 0) hh

private lemma exists_computable_le_lowerFreq_construct_cIdx_eq_rec (p : ℕ × ℕ →
    ℚ) (i m : ℕ) :
    Nat.findGreatest (fun n => exists_computable_le_lowerFreq_construct_cS p n ≤
                                 i) m = Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => cond (decide (exists_computable_le_lowerFreq_construct_cS p
                      (k + 1) ≤ i)) (k + 1) acc) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.findGreatest_succ, ih]
    by_cases h : exists_computable_le_lowerFreq_construct_cS p (m + 1) ≤ i <;>
        simp [h]

private lemma exists_computable_le_lowerFreq_construct_cIdx_comp (p : ℕ × ℕ → ℚ)
    (hpc : Computable p) : Computable
    (exists_computable_le_lowerFreq_construct_cIdx p) := by
  have hle2 : Computable₂ (fun a b : ℕ => decide (a ≤ b)) :=
    (Primrec.nat_le.comp Primrec.fst Primrec.snd).decide.to₂.to_comp
  have hu1 : Computable (fun x : ℕ × (ℕ × ℕ) => x.2.1) := Computable.fst.comp Computable.snd
  have hu2 : Computable (fun x : ℕ × (ℕ × ℕ) => x.2.2) := Computable.snd.comp Computable.snd
  have hle : Computable (fun x : ℕ × (ℕ × ℕ) => decide (exists_computable_le_lowerFreq_construct_cS
                                                  p (x.2.1 + 1) ≤ x.1)) :=
    hle2.comp ((exists_computable_le_lowerFreq_construct_cS_comp p hpc).comp
        (Primrec.succ.to_comp.comp hu1)) Computable.fst
  have hh : Computable₂ (fun (i : ℕ) (u : ℕ × ℕ) =>
      cond (decide (exists_computable_le_lowerFreq_construct_cS p (u.1 + 1) ≤ i))
          (u.1 + 1) u.2) :=
    (Computable.cond hle (Primrec.succ.to_comp.comp hu1) hu2).to₂
  have h := Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ => (0 : ℕ))
    (h := fun (i : ℕ) (u : ℕ × ℕ) => cond (decide (exists_computable_le_lowerFreq_construct_cS p
                                       (u.1 + 1) ≤ i)) (u.1 + 1) u.2)
    Computable.id (Computable.const 0) hh
  exact h.of_eq fun i => (exists_computable_le_lowerFreq_construct_cIdx_eq_rec p
                           i i).symm

private lemma exists_computable_le_lowerFreq_construct_cF_comp (p : ℕ × ℕ → ℚ)
    (hpc : Computable p) : Computable
    (exists_computable_le_lowerFreq_construct_cF p) := by
  have hI := exists_computable_le_lowerFreq_construct_cIdx_comp p hpc
  have hS := exists_computable_le_lowerFreq_construct_cS_comp p hpc
  have hD := exists_computable_le_lowerFreq_construct_cD_comp p hpc
  have hSI : Computable (fun i : ℕ => exists_computable_le_lowerFreq_construct_cS p
                                        (exists_computable_le_lowerFreq_construct_cIdx p i)) :=
                                        hS.comp hI
  have hDI : Computable (fun i : ℕ => exists_computable_le_lowerFreq_construct_cD p
                                        (exists_computable_le_lowerFreq_construct_cIdx p i)) :=
                                        hD.comp hI
  have hsub : Computable (fun i : ℕ => i - exists_computable_le_lowerFreq_construct_cS p
                                         (exists_computable_le_lowerFreq_construct_cIdx p i)) :=
    Primrec.nat_sub.to_comp.comp Computable.id hSI
  have hmod : Computable (fun i : ℕ =>
      (i - exists_computable_le_lowerFreq_construct_cS p
        (exists_computable_le_lowerFreq_construct_cIdx p i)) %
        exists_computable_le_lowerFreq_construct_cD p
          (exists_computable_le_lowerFreq_construct_cIdx p i)) :=
    Primrec.nat_mod.to_comp.comp hsub hDI
  have h := (exists_computable_le_lowerFreq_construct_cW_comp p hpc).comp
      (Computable.pair hI hmod)
  have e : exists_computable_le_lowerFreq_construct_cF p = fun i : ℕ =>
      (fun x : ℕ × ℕ => exists_computable_le_lowerFreq_construct_cW p x.1 x.2)
        (exists_computable_le_lowerFreq_construct_cIdx p i,
          (i - exists_computable_le_lowerFreq_construct_cS p
            (exists_computable_le_lowerFreq_construct_cIdx p i)) %
            exists_computable_le_lowerFreq_construct_cD p
              (exists_computable_le_lowerFreq_construct_cIdx p i)) := by
    funext i; rfl
  rw [e]
  exact h

-- properties
private lemma exists_computable_le_lowerFreq_construct_cDf_pos (p : ℕ × ℕ → ℚ)
    (n m : ℕ) : 1 ≤ exists_computable_le_lowerFreq_construct_cDf p n m := by
  induction m with
  | zero => exact le_refl _
  | succ m ih =>
    change 1 ≤ exists_computable_le_lowerFreq_construct_cDf p n m *
        (p (n, m)).den
    exact Nat.mul_pos ih (p (n, m)).den_pos

private lemma exists_computable_le_lowerFreq_construct_cDf_dvd (p : ℕ × ℕ → ℚ)
    (n m k : ℕ) (hk : k < m) :
    (p (n, k)).den ∣ exists_computable_le_lowerFreq_construct_cDf p n m := by
  induction m with
  | zero => omega
  | succ m ih =>
    change (p (n, k)).den ∣ exists_computable_le_lowerFreq_construct_cDf p n m *
        (p (n, m)).den
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · exact Dvd.dvd.mul_right (ih h) _
    · subst h; exact Dvd.intro_left _ rfl

private lemma exists_computable_le_lowerFreq_construct_cD_pos (p : ℕ × ℕ → ℚ)
    (n : ℕ) : 1 ≤ exists_computable_le_lowerFreq_construct_cD p n :=
    exists_computable_le_lowerFreq_construct_cDf_pos p n n

private lemma exists_computable_le_lowerFreq_construct_cA_cast (p : ℕ × ℕ → ℚ)
    (hp0 : ∀ n k, 0 ≤ p (n, k))
    (hps : ∀ n k, n ≤ k → p (n, k) = 0) (n k : ℕ) :
    (p (n, k) : ℝ) * exists_computable_le_lowerFreq_construct_cD p n =
        exists_computable_le_lowerFreq_construct_cA p n k := by
  by_cases hk : k < n
  · obtain ⟨q, hq⟩ := exists_computable_le_lowerFreq_construct_cDf_dvd p n n k hk
    have hnum : (((p (n, k)).num.natAbs : ℕ) : ℤ) = (p (n, k)).num :=
      Int.natAbs_of_nonneg (Rat.num_nonneg.2 (hp0 n k))
    have hnumQ : (((p (n, k)).num.natAbs : ℕ) : ℚ) = ((p (n, k)).num : ℚ) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hnum
      simpa only [Int.cast_natCast] using this
    have hA : exists_computable_le_lowerFreq_construct_cA p n k =
        (p (n, k)).num.natAbs * q := by
      unfold exists_computable_le_lowerFreq_construct_cA exists_computable_le_lowerFreq_construct_cD
      rw [hq, Nat.mul_div_cancel_left _ (p (n, k)).den_pos]
    have hQ : p (n, k) * (exists_computable_le_lowerFreq_construct_cD p n : ℚ) =
        (exists_computable_le_lowerFreq_construct_cA p n k : ℚ) := by
      rw [hA]
      have hD : exists_computable_le_lowerFreq_construct_cD p n = (p (n, k)).den
          * q := hq
      rw [hD]
      push_cast
      rw [hnumQ, ← mul_assoc, Rat.mul_den_eq_num]
    exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) hQ
  · have h0 := hps n k (not_lt.1 hk)
    simp [exists_computable_le_lowerFreq_construct_cA, h0]

private lemma exists_computable_le_lowerFreq_construct_cC_succ (p : ℕ × ℕ → ℚ)
    (n k : ℕ) : exists_computable_le_lowerFreq_construct_cC p n (k + 1) =
    exists_computable_le_lowerFreq_construct_cC p n k +
    exists_computable_le_lowerFreq_construct_cA p n k := rfl

private lemma exists_computable_le_lowerFreq_construct_cC_eq_sum (p : ℕ × ℕ → ℚ)
    (n k : ℕ) :
    exists_computable_le_lowerFreq_construct_cC p n k = ∑ j ∈ Finset.range k,
        exists_computable_le_lowerFreq_construct_cA p n j := by
  induction k with
  | zero => rfl
  | succ k ih => rw [exists_computable_le_lowerFreq_construct_cC_succ, ih,
                   Finset.sum_range_succ]

private lemma exists_computable_le_lowerFreq_construct_cC_mono (p : ℕ × ℕ → ℚ)
    (n : ℕ) : Monotone (exists_computable_le_lowerFreq_construct_cC p n) :=
  monotone_nat_of_le_succ (fun k => by rw [exists_computable_le_lowerFreq_construct_cC_succ]; omega)

private lemma exists_computable_le_lowerFreq_construct_cC_le_D (p : ℕ × ℕ → ℚ)
    (hp0 : ∀ n k, 0 ≤ p (n, k))
    (hps : ∀ n k, n ≤ k → p (n, k) = 0) (hp1 : ∀ n N, ∑ k ∈ Finset.range N, p (n, k) ≤ 1)
    (n : ℕ) : exists_computable_le_lowerFreq_construct_cC p n n ≤
        exists_computable_le_lowerFreq_construct_cD p n := by
  have h1 : ((exists_computable_le_lowerFreq_construct_cC p n n : ℕ) : ℝ) =
      (∑ k ∈ Finset.range n, (p (n, k) : ℝ)) *
      exists_computable_le_lowerFreq_construct_cD p n := by
    rw [exists_computable_le_lowerFreq_construct_cC_eq_sum, Nat.cast_sum,
        Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ =>
      (exists_computable_le_lowerFreq_construct_cA_cast p hp0 hps n k).symm
  have h2 : (∑ k ∈ Finset.range n, (p (n, k) : ℝ)) ≤ 1 := by exact_mod_cast hp1 n n
  have h3 : ((exists_computable_le_lowerFreq_construct_cC p n n : ℕ) : ℝ) ≤
      exists_computable_le_lowerFreq_construct_cD p n := by
    rw [h1]
    calc (∑ k ∈ Finset.range n, (p (n, k) : ℝ)) *
        exists_computable_le_lowerFreq_construct_cD p n ≤ 1 *
        exists_computable_le_lowerFreq_construct_cD p n :=
          mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
      _ = exists_computable_le_lowerFreq_construct_cD p n := one_mul _
  exact_mod_cast h3

private lemma exists_computable_le_lowerFreq_construct_cWf_eq_card (p : ℕ × ℕ →
    ℚ) (n t m : ℕ) :
    exists_computable_le_lowerFreq_construct_cWf p n t m =
        ((Finset.range m).filter (fun k =>
          exists_computable_le_lowerFreq_construct_cC p n (k + 1) ≤ t)).card :=
          by
  induction m with
  | zero => rfl
  | succ m ih =>
    change exists_computable_le_lowerFreq_construct_cWf p n t m + _ = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : exists_computable_le_lowerFreq_construct_cC p n (m + 1) ≤ t
    · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
    · rw [ite_eq_right h, ite_eq_right h]; rfl

private lemma exists_computable_le_lowerFreq_construct_cW_val (p : ℕ × ℕ → ℚ)
    (n t k : ℕ) (hk : k < n) (h1 : exists_computable_le_lowerFreq_construct_cC p
    n k ≤ t)
    (h2 : t < exists_computable_le_lowerFreq_construct_cC p n (k + 1)) :
        exists_computable_le_lowerFreq_construct_cW p n t = k := by
  unfold exists_computable_le_lowerFreq_construct_cW
  rw [exists_computable_le_lowerFreq_construct_cWf_eq_card]
  have : (Finset.range n).filter (fun j =>
    exists_computable_le_lowerFreq_construct_cC p n (j + 1) ≤ t) = Finset.range
    k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hj⟩
      by_contra hjk
      have := exists_computable_le_lowerFreq_construct_cC_mono p n (show k + 1 ≤
          j + 1 by omega)
      omega
    · intro hj
      refine ⟨by omega, ?_⟩
      have := exists_computable_le_lowerFreq_construct_cC_mono p n (show j + 1 ≤
          k by omega)
      omega
  rw [this, Finset.card_range]

private lemma exists_computable_le_lowerFreq_construct_cW_count (p : ℕ × ℕ → ℚ)
    (hp0 : ∀ n k, 0 ≤ p (n, k))
    (hps : ∀ n k, n ≤ k → p (n, k) = 0) (hp1 : ∀ n N, ∑ k ∈ Finset.range N, p (n, k) ≤ 1)
    (n k : ℕ) :
    (p (n, k) : ℝ) * exists_computable_le_lowerFreq_construct_cD p n ≤
      (((Finset.range (exists_computable_le_lowerFreq_construct_cD p n)).filter
          (fun t => exists_computable_le_lowerFreq_construct_cW p n t = k)).card
          : ℝ) := by
  by_cases hk : k < n
  · rw [exists_computable_le_lowerFreq_construct_cA_cast p hp0 hps n k]
    have hsub : Finset.Ico (exists_computable_le_lowerFreq_construct_cC p n k)
        (exists_computable_le_lowerFreq_construct_cC p n (k + 1)) ⊆
        (Finset.range (exists_computable_le_lowerFreq_construct_cD p n)).filter
            (fun t => exists_computable_le_lowerFreq_construct_cW p n t = k) :=
            by
      intro t ht
      rw [Finset.mem_Ico] at ht
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, exists_computable_le_lowerFreq_construct_cW_val p n t k hk ht.1
          ht.2⟩
      have := exists_computable_le_lowerFreq_construct_cC_mono p n (show k + 1 ≤
          n by omega)
      have := exists_computable_le_lowerFreq_construct_cC_le_D p hp0 hps hp1 n
      omega
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico, exists_computable_le_lowerFreq_construct_cC_succ] at hc
    exact_mod_cast (by omega : exists_computable_le_lowerFreq_construct_cA p n k
                         ≤
      ((Finset.range (exists_computable_le_lowerFreq_construct_cD p n)).filter
          (fun t => exists_computable_le_lowerFreq_construct_cW p n t = k)).card)
  · have h0 := hps n k (not_lt.1 hk)
    rw [h0]
    simp

private lemma exists_computable_le_lowerFreq_construct_cS_succ (p : ℕ × ℕ → ℚ)
    (n : ℕ) :
    exists_computable_le_lowerFreq_construct_cS p (n + 1) =
        exists_computable_le_lowerFreq_construct_cS p n +
        exists_computable_le_lowerFreq_construct_cD p n *
        ((n + 1) * exists_computable_le_lowerFreq_construct_cD p (n + 1)) := rfl

private lemma exists_computable_le_lowerFreq_construct_cS_ge (p : ℕ × ℕ → ℚ)
    (n : ℕ) : n * exists_computable_le_lowerFreq_construct_cD p n ≤
    exists_computable_le_lowerFreq_construct_cS p n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [exists_computable_le_lowerFreq_construct_cS_succ]
    have h := exists_computable_le_lowerFreq_construct_cD_pos p n
    have : (n + 1) * exists_computable_le_lowerFreq_construct_cD p (n + 1) ≤
        exists_computable_le_lowerFreq_construct_cD p n *
        ((n + 1) * exists_computable_le_lowerFreq_construct_cD p (n + 1)) :=
      Nat.le_mul_of_pos_left _ h
    omega

private lemma exists_computable_le_lowerFreq_construct_cS_ge_n (p : ℕ × ℕ → ℚ)
    (n : ℕ) : n ≤ exists_computable_le_lowerFreq_construct_cS p n :=
  le_trans (Nat.le_mul_of_pos_right _
      (exists_computable_le_lowerFreq_construct_cD_pos p n))
      (exists_computable_le_lowerFreq_construct_cS_ge p n)

private lemma exists_computable_le_lowerFreq_construct_cS_mono (p : ℕ × ℕ → ℚ) :
    Monotone (exists_computable_le_lowerFreq_construct_cS p) :=
  monotone_nat_of_le_succ (fun n => by rw [exists_computable_le_lowerFreq_construct_cS_succ]; omega)

private lemma exists_computable_le_lowerFreq_construct_cIdx_eq (p : ℕ × ℕ → ℚ)
    (n i : ℕ) (h1 : exists_computable_le_lowerFreq_construct_cS p n ≤ i)
    (h2 : i < exists_computable_le_lowerFreq_construct_cS p (n + 1)) :
    exists_computable_le_lowerFreq_construct_cIdx p i = n := by
  unfold exists_computable_le_lowerFreq_construct_cIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨le_trans (exists_computable_le_lowerFreq_construct_cS_ge_n p n) h1,
      fun _ => h1, ?_⟩
  intro m hm _ hle
  have := exists_computable_le_lowerFreq_construct_cS_mono p (show n + 1 ≤
      m by omega)
  omega


/-- Step 1 of the proof of `exists_computable_le_lowerFreq_follow`: the
computable block construction. With the hypotheses of the target there are a computable `f`,
block starts `S n` (`S 0 = 0`), periods `D n ≥ 1` and words `w n : ℕ → ℕ` such that: block `n`
is `[S n, S (n+1))`, of length a multiple of `D n`, and on it `f i = w n ((i - S n) % D n)`; the
word `w n` restricted to `[0, D n)` contains at least `p (n, k) * D n` copies of every `k`
(take `D n` a common denominator of row `n`, put the `p (n, k) * D n` copies of `k` one after
the other for `k < n` and pad with `0`; this fits because the row sum is `≤ 1`); and the blocks
grow fast: `n * D n ≤ S n` (for instance block `n` has length `(n + 2) * D n * D (n + 1)`, so that
`S (n + 1) ≥ (n + 2) * D (n + 1)`). Computability of `f` follows from that of `p` by computing the
block `n` containing `i` by a bounded search. -/
private theorem exists_computable_le_lowerFreq_construct
    (p : ℕ × ℕ → ℚ) (hpc : Computable p) (hp0 : ∀ n k, 0 ≤ p (n, k))
    (hps : ∀ n k, n ≤ k → p (n, k) = 0) (hp1 : ∀ n N, ∑ k ∈ Finset.range N, p (n, k) ≤ 1) :
    ∃ (f : ℕ → ℕ) (S D : ℕ → ℕ) (w : ℕ → ℕ → ℕ), Computable f ∧ S 0 = 0 ∧
      (∀ n, 1 ≤ D n) ∧ (∀ n, ∃ c, S (n + 1) = S n + D n * c) ∧ (∀ n, n * D n ≤ S n) ∧
      (∀ n k, (p (n, k) : ℝ) * D n ≤
        (((Finset.range (D n)).filter (fun t => w n t = k)).card : ℝ)) ∧
      (∀ n i, S n ≤ i → i < S (n + 1) → f i = w n ((i - S n) % D n)) := by
  refine ⟨exists_computable_le_lowerFreq_construct_cF p,
    exists_computable_le_lowerFreq_construct_cS p,
    exists_computable_le_lowerFreq_construct_cD p,
    exists_computable_le_lowerFreq_construct_cW p,
    exists_computable_le_lowerFreq_construct_cF_comp p hpc, rfl,
    exists_computable_le_lowerFreq_construct_cD_pos p,
    fun n => ⟨(n + 1) * exists_computable_le_lowerFreq_construct_cD p (n + 1),
      rfl⟩,
    exists_computable_le_lowerFreq_construct_cS_ge p,
    exists_computable_le_lowerFreq_construct_cW_count p hp0 hps hp1, ?_⟩
  intro n i h1 h2
  unfold exists_computable_le_lowerFreq_construct_cF
  rw [exists_computable_le_lowerFreq_construct_cIdx_eq p n i h1 h2]

private theorem exists_computable_le_lowerFreq_follow_countOcc_eq_sum
    (f : ℕ → ℕ) (k n : ℕ) :
    countOcc f k n = ∑ i ∈ Finset.range n, if f i = k then 1 else 0 := by
  unfold countOcc; rw [Finset.card_filter]

private theorem exists_computable_le_lowerFreq_follow_periodic_sum
    (g : ℕ → ℕ) (D : ℕ) (hg : ∀ t, g (t % D) = g t) (q : ℕ) :
    ∑ t ∈ Finset.range (q * D), g t = q * ∑ t ∈ Finset.range D, g t := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Nat.succ_mul]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← hg (q * D + t)]
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · simp at *
    · rw [Nat.mul_comm, Nat.mul_add_mod]
      exact hg t

/-- Step 2 of the proof of `exists_computable_le_lowerFreq_follow`: counting in
periodic blocks. If `f` agrees on block `[S n, S (n+1))` (of length a multiple of `D n`) with the
periodic word `w n` of period `D n`, and `w n` contains at least `p (n, k) * D n` copies of `k` in
one period, then the whole block contains at least `p (n, k)` times its length copies of `k` and
every prefix of length `m` of the block at least `p (n, k) * (m - D n)` copies. -/
private theorem exists_computable_le_lowerFreq_count
    (p : ℕ × ℕ → ℚ) (hp0 : ∀ n k, 0 ≤ p (n, k)) (f : ℕ → ℕ) (S D : ℕ → ℕ) (w : ℕ → ℕ → ℕ)
    (hD : ∀ n, 1 ≤ D n) (hdiv : ∀ n, ∃ c, S (n + 1) = S n + D n * c)
    (hw : ∀ n k, (p (n, k) : ℝ) * D n ≤
      (((Finset.range (D n)).filter (fun t => w n t = k)).card : ℝ))
    (hf : ∀ n i, S n ≤ i → i < S (n + 1) → f i = w n ((i - S n) % D n)) :
    (∀ k n, (p (n, k) : ℝ) * ((S (n + 1) : ℝ) - S n) ≤
      (countOcc f k (S (n + 1)) : ℝ) - countOcc f k (S n)) ∧
    (∀ k n m, S n + m ≤ S (n + 1) → (p (n, k) : ℝ) * ((m : ℝ) - D n) ≤
      (countOcc f k (S n + m) : ℝ) - countOcc f k (S n)) := by
  have key : ∀ k n m, S n + m ≤ S (n + 1) →
      countOcc f k (S n + m) = countOcc f k (S n) +
        ∑ t ∈ Finset.range m, if w n (t % D n) = k then 1 else 0 := by
    intro k n m hm
    rw [exists_computable_le_lowerFreq_follow_countOcc_eq_sum,
      exists_computable_le_lowerFreq_follow_countOcc_eq_sum, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.1 ht
    rw [hf n (S n + t) (by omega) (by omega)]
    simp
  have per : ∀ k n, ∑ t ∈ Finset.range (D n), (if w n (t % D n) = k then 1 else 0) =
      ((Finset.range (D n)).filter (fun t => w n t = k)).card := by
    intro k n
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Nat.mod_eq_of_lt (Finset.mem_range.1 ht)]
  have lowerN : ∀ k n q s, q * ((Finset.range (D n)).filter (fun t => w n t = k)).card ≤
      ∑ t ∈ Finset.range (q * D n + s), if w n (t % D n) = k then 1 else 0 := by
    intro k n q s
    have hper := exists_computable_le_lowerFreq_follow_periodic_sum
      (fun t => if w n (t % D n) = k then 1 else 0) (D n) (fun t => by simp) q
    rw [Finset.sum_range_add, hper, per k n]
    exact Nat.le_add_right _ _
  have lower : ∀ k n q s, (p (n, k) : ℝ) * (q * D n) ≤
      ((∑ t ∈ Finset.range (q * D n + s), if w n (t % D n) = k then 1 else 0 : ℕ) : ℝ) := by
    intro k n q s
    have h1 := hw n k
    have h2 := lowerN k n q s
    calc (p (n, k) : ℝ) * (q * D n) = q * ((p (n, k) : ℝ) * D n) := by ring
      _ ≤ q * (((Finset.range (D n)).filter (fun t => w n t = k)).card : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ ≤ _ := by exact_mod_cast h2
  constructor
  · intro k n
    obtain ⟨c, hc⟩ := hdiv n
    have hS : S (n + 1) = S n + c * D n := by rw [hc, Nat.mul_comm]
    have hk := key k n (c * D n) (by omega)
    rw [← hS] at hk
    have h := lower k n c 0
    simp only [Nat.add_zero] at h
    have e : (S (n + 1) : ℝ) - S n = c * D n := by rw [hS]; push_cast; ring
    rw [e, hk]
    push_cast at h ⊢
    linarith
  · intro k n m hm
    have hk := key k n m hm
    have hm' : m = (m / D n) * D n + m % D n := (Nat.div_add_mod' m (D n)).symm
    have h := lower k n (m / D n) (m % D n)
    rw [← hm'] at h
    have hs : m % D n < D n := Nat.mod_lt _ (hD n)
    have hmR : (m : ℝ) = (m / D n : ℕ) * D n + (m % D n : ℕ) := by
      exact_mod_cast hm'
    have hsR : ((m % D n : ℕ) : ℝ) < D n := by exact_mod_cast hs
    have hp := (show (0 : ℝ) ≤ p (n, k) by exact_mod_cast hp0 n k)
    rw [hk]
    push_cast at h ⊢
    have h3 : (m : ℝ) - D n ≤ ((m / D n : ℕ) : ℝ) * D n := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hp]

/-- Step 3 of the proof of `exists_computable_le_lowerFreq_follow`: the limit
estimate. If the blocks `[S n, S (n+1))` of `f` (with `S 0 = 0`, `D n ≥ 1`, `n * D n ≤ S n`) contain
at least `p (n, k)` times their length copies of `k`, and each prefix of length `m` of block `n`
at least `p (n, k) * (m - D n)` copies, then every real `r` with `r ≤ p (n, k)` for all large `n`
satisfies `r ≤ lowerFreq f k` (the prefix of length `S n + m` has frequency at least
`r * (1 - S N₀ / (S n + m) - 1 / n)`). -/
private theorem exists_computable_le_lowerFreq_limit
    (p : ℕ × ℕ → ℚ) (f : ℕ → ℕ) (S D : ℕ → ℕ) (hS0 : S 0 = 0)
    (hSmono : ∀ n, S n ≤ S (n + 1)) (hD : ∀ n, 1 ≤ D n) (hSD : ∀ n, n * D n ≤ S n)
    (hfull : ∀ k n, (p (n, k) : ℝ) * ((S (n + 1) : ℝ) - S n) ≤
      (countOcc f k (S (n + 1)) : ℝ) - countOcc f k (S n))
    (hpart : ∀ k n m, S n + m ≤ S (n + 1) → (p (n, k) : ℝ) * ((m : ℝ) - D n) ≤
      (countOcc f k (S n + m) : ℝ) - countOcc f k (S n)) :
    ∀ (k : ℕ) (r : ℝ), (∀ᶠ n in Filter.atTop, r ≤ (p (n, k) : ℝ)) → r ≤ lowerFreq f k := by
  intro k r hr
  rcases le_or_gt r 0 with hr0 | hr0
  · exact hr0.trans (lowerFreq_nonneg f k)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hr
  have hSn : ∀ n, n ≤ S n := fun n => by
    have := hSD n
    have := hD n
    nlinarith
  have hSmono' : Monotone S := monotone_nat_of_le_succ hSmono
  -- telescoping
  have htel : ∀ j, r * ((S (N0 + j) : ℝ) - S N0) ≤
      (countOcc f k (S (N0 + j)) : ℝ) - countOcc f k (S N0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := hfull k (N0 + j)
      have h2 : r ≤ (p (N0 + j, k) : ℝ) := hN0 _ (by omega)
      have h3 : (S (N0 + j) : ℝ) ≤ S (N0 + j + 1) := by exact_mod_cast hSmono _
      have h4 : r * ((S (N0 + j + 1) : ℝ) - S (N0 + j)) ≤
          (p (N0 + j, k) : ℝ) * ((S (N0 + j + 1) : ℝ) - S (N0 + j)) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
      rw [← add_assoc]
      nlinarith
  have hcount_nonneg : ∀ n, (0 : ℝ) ≤ countOcc f k n := fun n => Nat.cast_nonneg _
  -- main estimate: for n ≥ N0, S n ≤ m < S (n+1)
  have hmain : ∀ n m, N0 ≤ n → S n ≤ m → m ≤ S (n + 1) →
      r * ((m : ℝ) - S N0 - D n) ≤ countOcc f k m := by
    intro n m hn h1 h2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le h1
    have ht := htel j
    have hp := hpart k (N0 + j) m' h2
    have hr' : r ≤ (p (N0 + j, k) : ℝ) := hN0 _ (by omega)
    have hm'D : (D (N0 + j) : ℝ) ≤ m' ∨ (m' : ℝ) < D (N0 + j) := by
      exact le_or_gt _ _
    have h5 : r * ((m' : ℝ) - D (N0 + j)) ≤ (p (N0 + j, k) : ℝ) * ((m' : ℝ) - D (N0 + j)) ∨
        (m' : ℝ) < D (N0 + j) := by
      rcases hm'D with h | h
      · left; exact mul_le_mul_of_nonneg_right hr' (by linarith)
      · right; exact h
    have hc := hcount_nonneg (S N0)
    push_cast
    rcases h5 with h5 | h5
    · nlinarith
    · -- m' < D: bound by 0
      have : r * ((S (N0 + j) : ℝ) - S N0) ≤ countOcc f k (S (N0 + j)) := by linarith
      have h6 : (countOcc f k (S (N0 + j)) : ℝ) ≤ countOcc f k (S (N0 + j) + m') := by
        exact_mod_cast (by
          unfold countOcc
          exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega))))
      nlinarith
  refine le_of_forall_sub_le fun ε hε => ?_
  have hcob : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => (countOcc f k n : ℝ) / n) := by
    refine Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := 1) fun n => ?_
    have h : (countOcc f k n : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (div_le_one (by exact_mod_cast hn)).2 h
  refine Filter.le_liminf_of_le hcob ?_
  set N1 : ℕ := max N0 (⌈2 * r / ε⌉₊ + 1) with hN1
  set M : ℕ := max (S N1) (⌈2 * r * S N0 / ε⌉₊ + 1) with hM
  filter_upwards [Filter.eventually_ge_atTop M] with m hm
  have hm1 : S N1 ≤ m := (le_max_left _ _).trans hm
  have hm2 : ⌈2 * r * S N0 / ε⌉₊ + 1 ≤ m := (le_max_right _ _).trans hm
  have hmpos : 0 < m := by omega
  have hex : ∃ n, m < S (n + 1) := ⟨m, by have := hSn (m + 1); omega⟩
  classical
  set n := Nat.find hex with hn
  have hn1 : m < S (n + 1) := Nat.find_spec hex
  have hn2 : S n ≤ m := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, hS0]; exact Nat.zero_le _
    · have := Nat.find_min hex (show n - 1 < n by omega)
      have h' : n - 1 + 1 = n := by omega
      rw [h'] at this
      omega
  have hnN1 : N1 ≤ n := by
    by_contra h
    push Not at h
    have := hSmono' (show n + 1 ≤ N1 by omega)
    omega
  have hnN0 : N0 ≤ n := (le_max_left _ _).trans hnN1
  have hmain' := hmain n m hnN0 hn2 hn1.le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  rw [le_div_iff₀ hmR]
  have hnR : 2 * r / ε ≤ n := by
    have : (⌈2 * r / ε⌉₊ : ℝ) ≤ n := by
      exact_mod_cast (show ⌈2 * r / ε⌉₊ ≤ n by
        have := (le_max_right _ _).trans hnN1; omega)
    exact (Nat.le_ceil _).trans this
  have hDn : (n : ℝ) * D n ≤ m := by
    exact_mod_cast (hSD n).trans hn2
  have hrD : r * D n ≤ ε / 2 * m := by
    have h1 : 2 * r ≤ ε * n := by
      rw [div_le_iff₀ hε] at hnR; linarith
    have h2 : (0:ℝ) ≤ D n := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  have hrS : r * S N0 ≤ ε / 2 * m := by
    have : 2 * r * S N0 / ε ≤ m := by
      have : (⌈2 * r * S N0 / ε⌉₊ : ℝ) ≤ m := by
        exact_mod_cast (show ⌈2 * r * S N0 / ε⌉₊ ≤ m by omega)
      exact (Nat.le_ceil _).trans this
    rw [div_le_iff₀ hε] at this
    nlinarith
  nlinarith

/-- Step 3 of the proof of `exists_computable_le_lowerFreq`: following the rows. Given
a computable table `p (n, k)` of non-negative rationals with row sums `≤ 1`, row `n` supported on
`k < n`, there is a computable sequence `f` whose lower frequency of `k` is at least every real
`r` with `r ≤ p (n, k)` for all large `n`.
(Block `n` is periodic with period the common denominator `Dₙ` of row `n`, containing `p (n, k) Dₙ`
copies of `k` and padded with `0`; its length is a multiple of `Dₙ` much larger than `D_{n+1}` and
than all earlier blocks together, so within block `n` the frequency of `k` is at least
`p (n, k) - Dₙ / (total length so far)` up to the contribution of the earlier blocks.) -/
private theorem exists_computable_le_lowerFreq_follow
    (p : ℕ × ℕ → ℚ) (hpc : Computable p) (hp0 : ∀ n k, 0 ≤ p (n, k))
    (hps : ∀ n k, n ≤ k → p (n, k) = 0) (hp1 : ∀ n N, ∑ k ∈ Finset.range N, p (n, k) ≤ 1) :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ (k : ℕ) (r : ℝ), (∀ᶠ n in Filter.atTop, r ≤ (p (n, k) : ℝ)) → r ≤ lowerFreq f k := by
  obtain ⟨f, S, D, w, hfc, hS0, hD, hdiv, hSD, hw, hf⟩ :=
    exists_computable_le_lowerFreq_construct p hpc hp0 hps hp1
  obtain ⟨hfull, hpart⟩ :=
    exists_computable_le_lowerFreq_count p hp0 f S D w hD hdiv hw hf
  exact ⟨f, hfc, exists_computable_le_lowerFreq_limit p f S D hS0
    (fun n => by obtain ⟨c, hc⟩ := hdiv n; omega) hD hSD hfull hpart⟩

/-- **SUV Theorem 136 (Section 6.4.3, printed p. 210).** For every `0'`-lower-semicomputable
sequence `q` of non-negative reals with `∑ qᵢ ≤ 1` there is a computable sequence `f` in which
the lower frequency of every `k` is at least `qₖ`.

Proof idea: write `r < qₖ` as "the requests 'make `qₖ` greater than `r`' are eventually never
cancelled" (a `Σ₂` representation). Build a table of rational measures row by row. In row `n`,
serve the current requests by age, increasing `pₖ` up to `r` while the sum stays `≤ 1`. Then
follow each row for much longer than all the previous ones. -/
theorem exists_computable_le_lowerFreq {q : ℕ → ℝ}
    (hq : PointToSet.IsLowerSemicomputableIn jumpSet q) (h0 : ∀ i, 0 ≤ q i)
    (h1 : ∀ N, ∑ i ∈ Finset.range N, q i ≤ 1) :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ k, q k ≤ lowerFreq f k := by
  obtain ⟨P, hPc, hP⟩ := exists_computable_le_lowerFreq_step1_sigma2 hq
  obtain ⟨p, hpc, hp0, hps, hp1, hlim⟩ :=
    exists_computable_le_lowerFreq_table h0 h1 P hPc hP
  obtain ⟨f, hf, hfreq⟩ := exists_computable_le_lowerFreq_follow p hpc hp0 hps hp1
  refine ⟨f, hf, fun k => le_of_forall_rat_lt_imp_le fun r hr => ?_⟩
  exact hfreq k r ((hlim k r hr).mono fun n hn => by exact_mod_cast hn)

private lemma exists_computable_lowerFreq_maximal_exists_maximal_aux_half_pow :
    Computable (fun a : ℕ => (1 / 2 : ℚ) ^ a) := by
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun a : ℕ => 2 ^ a)
    (Computable.const 1)
    ((nat_pow_primrec₂.comp (Primrec.const 2) Primrec.id).to_comp)
    (fun a => by positivity) (fun a => ?_)
  push_cast
  rw [div_pow, one_pow]

private lemma exists_computable_lowerFreq_maximal_exists_maximal_aux_m_lower :
    PointToSet.IsLowerSemicomputableIn jumpSet
      (fun k : ℕ => ((1 : ℝ) / 2) ^ PointToSet.oracleNatComplexity jumpSet k) := by
  have H : (fun w : ℕ × ℚ =>
      (w.2 : ℝ) < ((1 : ℝ) / 2) ^ PointToSet.oracleNatComplexity jumpSet w.1) =
      fun w => ∃ n : ℕ,
        ((PointToSet.oracleNatComplexity jumpSet w.1 : ℝ) < (((n + 1 : ℕ) : ℚ) : ℝ)) ∧
        w.2 < (1 / 2 : ℚ) ^ n := by
    funext w
    refine propext ⟨fun h => ?_, fun ⟨n, h1, h2⟩ => ?_⟩
    · refine ⟨PointToSet.oracleNatComplexity jumpSet w.1, by push_cast; linarith, ?_⟩
      have : (w.2 : ℝ) <
          (((1 / 2 : ℚ) ^ PointToSet.oracleNatComplexity jumpSet w.1 : ℚ) : ℝ) := by
        push_cast; exact h
      exact_mod_cast this
    · have h1' : PointToSet.oracleNatComplexity jumpSet w.1 ≤ n := by
        have : (PointToSet.oracleNatComplexity jumpSet w.1 : ℝ) < (n : ℝ) + 1 := by
          push_cast at h1; exact h1
        have : PointToSet.oracleNatComplexity jumpSet w.1 < n + 1 := by exact_mod_cast this
        omega
      have h2' : (w.2 : ℝ) < (((1 / 2 : ℚ) ^ n : ℚ) : ℝ) := by exact_mod_cast h2
      push_cast at h2'
      exact h2'.trans_le (pow_le_pow_of_le_one (by norm_num) (by norm_num) h1')
  unfold PointToSet.IsLowerSemicomputableIn
  rw [H]
  refine PointToSet.IsREIn.exists (A := jumpSet) (F := fun x : (ℕ × ℚ) × ℕ =>
    ((PointToSet.oracleNatComplexity jumpSet x.1.1 : ℝ) < (((x.2 + 1 : ℕ) : ℚ) : ℝ)) ∧
        x.1.2 < (1 / 2 : ℚ) ^ x.2) ?_
  refine PointToSet.IsREIn.and ?_ ?_
  · refine (PointToSet.isREIn_oracleNatComplexity_lt jumpSet).comp
      (f := fun x : (ℕ × ℚ) × ℕ => (x.1.1, (((x.2 + 1 : ℕ) : ℚ)))) ?_
    refine ComputableIn.pair (Computable.fst.comp Computable.fst).computableIn ?_
    exact (computable_nat_to_rat.comp (Primrec.succ.to_comp.comp Computable.snd)).computableIn
  · refine PointToSet.isREIn_of_computable_decide ?_
    exact computable₂_ratLt.comp (Computable.snd.comp Computable.fst)
      (exists_computable_lowerFreq_maximal_exists_maximal_aux_half_pow.comp
        Computable.snd)

private lemma exists_computable_lowerFreq_maximal_exists_maximal_aux_m_sum (N : ℕ) :
    ∑ i ∈ Finset.range N, ((1 : ℝ) / 2) ^ PointToSet.oracleNatComplexity jumpSet i ≤ 1 := by
  have h := (ENNReal.sum_le_tsum (Finset.range N)).trans (PointToSet.oracle_kraft jumpSet)
  have h2 : ENNReal.ofReal
      (∑ i ∈ Finset.range N, ((1 : ℝ) / 2) ^ PointToSet.oracleNatComplexity jumpSet i)
      ≤ 1 := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) h
    rw [ENNReal.ofReal_pow (by norm_num)]
    congr 1
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  exact (ENNReal.ofReal_le_one).mp h2

private lemma exists_computable_lowerFreq_maximal_exists_maximal_aux_decode
    (k : ℕ) (w : BitString) (hw : natBits k = w) : decodeBits w = k := by
  subst hw
  exact decodeBits_natBits k

open Classical in
private lemma exists_computable_lowerFreq_maximal_exists_maximal_aux_dominate
    {q : ℕ → ℝ} (hq : PointToSet.IsLowerSemicomputableIn jumpSet q) (h0 : ∀ i, 0 ≤ q i)
    (h1 : ∀ N, ∑ i ∈ Finset.range N, q i ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ k, q k ≤ c * ((1 : ℝ) / 2) ^ PointToSet.oracleNatComplexity jumpSet k := by
  have hex : ∀ k, 0 < q k → ∃ n : ℕ, ((1 : ℝ) / 2) ^ n < q k := fun k hk =>
    exists_pow_lt_of_lt_one hk (by norm_num)
  let N : ℕ → ℕ := fun k => if h : 0 < q k then Nat.find (hex k h) else 0
  have hN1 : ∀ k (hk : 0 < q k), ((1 : ℝ) / 2) ^ N k < q k := fun k hk => by
    simp only [N, dite_eq_left hk]
    exact Nat.find_spec (hex k hk)
  have hN2 : ∀ k (hk : 0 < q k) n, ((1 : ℝ) / 2) ^ n < q k → N k ≤ n := fun k hk n hn => by
    simp only [N, dite_eq_left hk]
    exact Nat.find_min' (hex k hk) hn
  have hN3 : ∀ k (hk : 0 < q k), q k ≤ 2 * ((1 : ℝ) / 2) ^ N k := fun k hk => by
    have hq1 : q k ≤ 1 := by
      have := Finset.single_le_sum (f := q) (fun i _ => h0 i) (Finset.mem_range.2
          (Nat.lt_succ_self k))
      exact this.trans (h1 (k + 1))
    have hne : N k ≠ 0 := fun h => by
      have := hN1 k hk
      rw [h] at this
      simp at this
      linarith
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have hlt : j < N k := by omega
    have : ¬ ((1 : ℝ) / 2) ^ j < q k := fun hh => by
      have := hN2 k hk j hh
      omega
    push Not at this
    rw [hj, pow_succ]
    linarith
  -- the cost-function setup
  let F : BitString → Prop := fun w => ∃ k, natBits k = w ∧ 0 < q k
  let g : Subtype F → ℝ := fun w => (N (decodeBits w.1) : ℝ)
  have hg : PointToSet.IsUpperSemicomputableOnIn jumpSet F g := by
    refine ⟨fun x => ∃ y : ℕ × ℕ, natBits y.1 = x.1 ∧ (((1 / 2 : ℚ) ^ y.2 : ℚ) : ℝ) < q y.1 ∧
      (y.2 : ℚ) < x.2, ?_, ?_, ?_⟩
    · refine PointToSet.IsREIn.exists (A := jumpSet)
        (F := fun z : (BitString × ℚ) × (ℕ × ℕ) => natBits z.2.1 = z.1.1 ∧
          (((1 / 2 : ℚ) ^ z.2.2 : ℚ) : ℝ) < q z.2.1 ∧ (z.2.2 : ℚ) < z.1.2) ?_
      refine PointToSet.IsREIn.and ?_ (PointToSet.IsREIn.and ?_ ?_)
      · refine PointToSet.isREIn_of_computable_decide ?_
        exact (PrimrecRel.decide Primrec.eq).to_comp.comp
          (natBits_computable.comp (Computable.fst.comp Computable.snd))
          (Computable.fst.comp Computable.fst)
      · refine hq.comp (f := fun z : (BitString × ℚ) × (ℕ × ℕ) => (z.2.1, (1 / 2 : ℚ) ^ z.2.2)) ?_
        refine ComputableIn.pair (Computable.fst.comp Computable.snd).computableIn ?_
        exact (exists_computable_lowerFreq_maximal_exists_maximal_aux_half_pow.comp
          (Computable.snd.comp Computable.snd)).computableIn
      · refine PointToSet.isREIn_of_computable_decide ?_
        exact computable₂_ratLt.comp
          (computable_nat_to_rat.comp (Computable.snd.comp Computable.snd))
          (Computable.snd.comp Computable.fst)
    · rintro w s ⟨⟨k, n⟩, hw, hlt, hns⟩
      have hlt' : ((1 : ℝ) / 2) ^ n < q k := by
        have : (((1 / 2 : ℚ) ^ n : ℚ) : ℝ) = ((1 : ℝ) / 2) ^ n := by push_cast; rfl
        rw [← this]; exact hlt
      have hk : 0 < q k := lt_of_le_of_lt (by positivity) hlt'
      have hF : F w := ⟨k, hw, hk⟩
      refine ⟨hF, ?_⟩
      simp only [g]
      rw [exists_computable_lowerFreq_maximal_exists_maximal_aux_decode k w hw]
      have h1': (N k : ℝ) ≤ n := by exact_mod_cast hN2 k hk n hlt'
      have h2' : (n : ℝ) < s := by exact_mod_cast hns
      linarith
    · rintro ⟨w, k, hw, hk⟩ ε hε
      have hk' : decodeBits w = k :=
        exists_computable_lowerFreq_maximal_exists_maximal_aux_decode k w hw
      obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (lt_add_of_pos_right (g ⟨w, k, hw, hk⟩) hε)
      refine ⟨s, ⟨(k, N k), hw, ?_, ?_⟩, hs2⟩
      · have := hN1 k hk
        have h' : (((1 / 2 : ℚ) ^ N k : ℚ) : ℝ) = ((1 : ℝ) / 2) ^ N k := by push_cast; rfl
        rw [h']; exact this
      · have : (N k : ℝ) < s := by
          have e : g ⟨w, k, hw, hk⟩ = (N k : ℝ) := by simp only [g, hk']
          rw [e] at hs1; exact hs1
        exact_mod_cast this
  have hM : (∑' w : Subtype F, (2 : ENNReal) ^ (-g w)) ≤ 1 := by
    have hpt : ∀ w : Subtype F, (2 : ENNReal) ^ (-g w) ≤ ENNReal.ofReal (q (decodeBits w.1)) := by
      rintro ⟨w, k, hw, hk⟩
      have hk' : decodeBits w = k :=
        exists_computable_lowerFreq_maximal_exists_maximal_aux_decode k w hw
      simp only [g, hk']
      have e : (2 : ENNReal) ^ (-(N k : ℝ)) = ENNReal.ofReal (((1 : ℝ) / 2) ^ N k) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.ofReal_pow (by norm_num), one_div,
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        simp [ENNReal.inv_pow]
      rw [e]
      exact ENNReal.ofReal_le_ofReal (hN1 k hk).le
    have hinj : Function.Injective (fun w : Subtype F => decodeBits w.1) := by
      rintro ⟨w, k, hw, _⟩ ⟨w', k', hw', _⟩ h
      have h' : decodeBits w = decodeBits w' := h
      have e1 : decodeBits w = k :=
        exists_computable_lowerFreq_maximal_exists_maximal_aux_decode k w hw
      have e2 : decodeBits w' = k' :=
        exists_computable_lowerFreq_maximal_exists_maximal_aux_decode k' w' hw'
      have hkk : k = k' := by rw [← e1, ← e2, h']
      subst hkk
      have : w = w' := by rw [← hw, ← hw']
      subst this
      rfl
    calc (∑' w : Subtype F, (2 : ENNReal) ^ (-g w))
        ≤ ∑' w : Subtype F, ENNReal.ofReal (q (decodeBits w.1)) := ENNReal.tsum_le_tsum hpt
      _ ≤ ∑' k, ENNReal.ofReal (q k) :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k => ENNReal.ofReal (q k))
      _ ≤ 1 := by
        rw [ENNReal.tsum_eq_iSup_nat]
        refine iSup_le fun N => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i)]
        exact ENNReal.ofReal_le_one.mpr (h1 N)
  obtain ⟨c0, hc0⟩ := PointToSet.oracle_coding_finite_mass jumpSet F g hg 1 hM ENNReal.one_lt_top
  refine ⟨2 * 2 ^ c0, by positivity, fun k => ?_⟩
  by_cases hk : 0 < q k
  · have hKN := hc0 ⟨natBits k, k, rfl, hk⟩
    have hKN' : PointToSet.oracleNatComplexity jumpSet k ≤ N k + c0 := by
      have e : g ⟨natBits k, k, rfl, hk⟩ = (N k : ℝ) := by
        change (N (decodeBits (natBits k)) : ℝ) = N k
        rw [exists_computable_lowerFreq_maximal_exists_maximal_aux_decode k _ rfl]
      rw [e] at hKN
      exact_mod_cast hKN
    have hpow : ((1 : ℝ) / 2) ^ (N k + c0) ≤
        ((1 : ℝ) / 2) ^ PointToSet.oracleNatComplexity jumpSet k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hKN'
    have h2c : (2 : ℝ) ^ c0 * ((1 : ℝ) / 2) ^ c0 = 1 := by
      rw [← mul_pow]; norm_num
    calc q k ≤ 2 * ((1 : ℝ) / 2) ^ N k := hN3 k hk
      _ = 2 * 2 ^ c0 * ((1 : ℝ) / 2) ^ (N k + c0) := by
        rw [pow_add]; linear_combination (-(2 * ((1:ℝ)/2) ^ N k)) * h2c
      _ ≤ 2 * 2 ^ c0 * ((1 : ℝ) / 2) ^ PointToSet.oracleNatComplexity jumpSet k := by
        gcongr
  · have : q k = 0 := le_antisymm (not_lt.mp hk) (h0 k)
    rw [this]; positivity

/-- Step 1 of the proof of `exists_computable_lowerFreq_maximal`: there is a maximal
`0'`-lower-semicomputable semimeasure on `ℕ` (the `0'`-a priori probability): a `0'`-lower
semicomputable sequence `m` of non-negative reals with all finite partial sums `≤ 1` such that
every other such sequence `q` is bounded by `c * m` for some constant `c > 0`.

Proof idea: Levin's construction relativized to `0'`, e.g. `m k = 2 ^ (-K^{0'}(k))` together with
the relativized coding theorem (Kraft–Chaitin for the `0'`-enumerable requests
`(k, ⌈-log₂ q k⌉ + 1)`), or the weighted sum over a `0'`-enumeration of all
`0'`-lower-semicomputable semimeasures. -/
private theorem exists_computable_lowerFreq_maximal_exists_maximal :
    ∃ m : ℕ → ℝ, PointToSet.IsLowerSemicomputableIn jumpSet m ∧ (∀ i, 0 ≤ m i) ∧
      (∀ N, ∑ i ∈ Finset.range N, m i ≤ 1) ∧
      ∀ q : ℕ → ℝ, PointToSet.IsLowerSemicomputableIn jumpSet q → (∀ i, 0 ≤ q i) →
        (∀ N, ∑ i ∈ Finset.range N, q i ≤ 1) → ∃ c : ℝ, 0 < c ∧ ∀ k, q k ≤ c * m k := by
  refine ⟨fun k => ((1 : ℝ) / 2) ^ PointToSet.oracleNatComplexity jumpSet k,
    exists_computable_lowerFreq_maximal_exists_maximal_aux_m_lower,
    fun i => by positivity,
    exists_computable_lowerFreq_maximal_exists_maximal_aux_m_sum,
    fun q hq h0 h1 => ?_⟩
  exact exists_computable_lowerFreq_maximal_exists_maximal_aux_dominate hq h0 h1

/-- **SUV Section 6.4.3 (printed p. 210), corollary of Theorem 136.** For an appropriate
computable sequence `f`, `k ↦ pₖ` is a maximal `0'`-lower-semicomputable semimeasure. It is one
by Theorem 135 and `sum_lowerFreq_le_one`, and it dominates every other one up to a constant
factor.

Proof idea: apply Theorem 136 to a maximal `0'`-lower-semicomputable semimeasure. -/
theorem exists_computable_lowerFreq_maximal :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ q : ℕ → ℝ, PointToSet.IsLowerSemicomputableIn jumpSet q → (∀ i, 0 ≤ q i) →
        (∀ N, ∑ i ∈ Finset.range N, q i ≤ 1) → ∃ c : ℝ, 0 < c ∧ ∀ k, q k ≤ c * lowerFreq f k := by
  obtain ⟨m, hm, hm0, hm1, hmax⟩ := exists_computable_lowerFreq_maximal_exists_maximal
  obtain ⟨f, hf, hmf⟩ := exists_computable_le_lowerFreq hm hm0 hm1
  refine ⟨f, hf, fun q hq hq0 hq1 => ?_⟩
  obtain ⟨c, hc, hqc⟩ := hmax q hq hq0 hq1
  exact ⟨c, hc, fun k => (hqc k).trans (mul_le_mul_of_nonneg_left (hmf k) hc.le)⟩

/-- Step 1 of the proof of `exists_computable_KP_jump_eq_neg_log_lowerFreq`: for an
optimal prefix-free `0'`-decompressor `V`, the complexity `KP V (Nat.bits k) []` is finite. -/
private theorem exists_computable_KP_jump_eq_neg_log_lowerFreq_finite {V : Map}
    (hV : PointToSet.IsOptimalOraclePrefix jumpSet V) (k : ℕ) :
    KP V (Nat.bits k) [] ≠ ⊤ := by
  obtain ⟨hU1, hU2, _⟩ := PointToSet.exists_optimalOraclePrefix_spec jumpSet
  obtain ⟨c, hc⟩ := hV.2.2 _ hU1 hU2
  exact ne_top_of_le_ne_top
    (WithTop.add_ne_top.2 ⟨PointToSet.exists_optimalOraclePrefix_finite jumpSet _ _,
        ENat.natCast_ne_top c⟩)
    (hc (Nat.bits k) [])

/-- Step 2 of the proof of `exists_computable_KP_jump_eq_neg_log_lowerFreq`
(Kraft inequality): for an optimal prefix-free `0'`-decompressor `V`, the weights
`2^{-K^V(k)}` of the naturals `k` (as strings `Nat.bits k`) have all finite partial sums at
most `1`. `V` is a prefix machine, so `∑ₓ 2^{-KP V x []} ≤ ∑ₓ aprioriMeasure V x [] ≤ 1`
(`tsum_aprioriMeasure_le_one`, `complexityWeight_KP_le_aprioriMeasure`), and `k ↦ Nat.bits k`
is injective. -/
private theorem exists_computable_KP_jump_eq_neg_log_lowerFreq_kraft {V : Map}
    (hV : PointToSet.IsOptimalOraclePrefix jumpSet V) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((2 : ℝ)⁻¹) ^ (KP V (Nat.bits k) []).toNat ≤ 1 := by
  have hterm : ∀ k, ((2 : ℝ)⁻¹) ^ (KP V (Nat.bits k) []).toNat =
      (complexityWeight (KP V (Nat.bits k) [])).toReal := by
    intro k
    conv_rhs => rw [← ENat.natCast_toNat
      (exists_computable_KP_jump_eq_neg_log_lowerFreq_finite hV k)]
    simp [complexityWeight_coe, ENNReal.toReal_pow]
  have hfin : ∀ k, complexityWeight (KP V (Nat.bits k) []) ≠ ⊤ := by
    intro k
    rw [← ENat.natCast_toNat (exists_computable_KP_jump_eq_neg_log_lowerFreq_finite hV k),
      complexityWeight_coe]
    exact ENNReal.pow_ne_top (by simp)
  have hle : (∑ k ∈ Finset.range N, complexityWeight (KP V (Nat.bits k) [])) ≤ 1 := by
    have h1 : (∑' x : BitString, aprioriMeasure V x []) ≤ 1 :=
      tsum_aprioriMeasure_le_one V [] hV.2.1
    have h2 : (∑' x : BitString, complexityWeight (KP V x [])) ≤ 1 :=
      (ENNReal.tsum_le_tsum fun x => complexityWeight_KP_le_aprioriMeasure V x []).trans h1
    have h3 := ENNReal.tsum_comp_le_tsum_of_injective natBits_injective
      (fun x => complexityWeight (KP V x []))
    exact (ENNReal.sum_le_tsum _).trans (h3.trans h2)
  simp_rw [hterm]
  rw [← ENNReal.toReal_sum (fun k _ => hfin k)]
  have := ENNReal.toReal_mono ENNReal.one_ne_top hle
  simpa using this

/-- Step 1 of the proof of `exists_computable_KP_jump_eq_neg_log_lowerFreq_lsc`:
the map `a ↦ 2 ^ (-a)` into the rationals is computable. -/
private lemma exists_computable_KP_jump_eq_neg_log_lowerFreq_half_pow :
    Computable (fun a : ℕ => (1 / 2 : ℚ) ^ a) := by
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun a : ℕ => 2 ^ a)
    (Computable.const 1)
    ((nat_pow_primrec₂.comp (Primrec.const 2) Primrec.id).to_comp)
    (fun a => by positivity) (fun a => ?_)
  push_cast
  rw [div_pow, one_pow]

/-- Step 3 of the proof of `exists_computable_KP_jump_eq_neg_log_lowerFreq`: for an
optimal prefix-free `0'`-decompressor `V`, the weights `k ↦ 2^{-K^V(k)}` form a
`0'`-lower-semicomputable function. Indeed `K^V(x) ≤ n` iff some program `p` of length `≤ n`
makes the `0'`-machine `V` output `x` on the empty condition, which is `0'`-enumerable, and
`r < 2^{-K^V(k)}` iff `K^V(k) < -log₂ r` iff `K^V(k) ≤ n` for some natural `n` with
`2^{-n} > r`. -/
private theorem exists_computable_KP_jump_eq_neg_log_lowerFreq_lsc {V : Map}
    (hV : PointToSet.IsOptimalOraclePrefix jumpSet V) :
    PointToSet.IsLowerSemicomputableIn jumpSet
      (fun k : ℕ => ((2 : ℝ)⁻¹) ^ (KP V (Nat.bits k) []).toNat) := by
  have hfin := exists_computable_KP_jump_eq_neg_log_lowerFreq_finite hV
  have hVp : PartrecIn {charOracle jumpSet} V :=
    (PointToSet.isDecompressorIn_iff_partrecIn _ _).mp hV.1
  have hprod : PointToSet.IsREIn jumpSet (fun pw : BitString × BitString =>
      produces V pw.1 [] pw.2) := by
    refine ⟨fun pw => (V (pw.1, [])).bind fun x =>
      cond (decide (x = pw.2)) (Part.some 0) Part.none, ?_, fun pw ↦ ?_⟩
    · have hpair : ComputableIn {charOracle jumpSet}
          (fun pw : BitString × BitString => (pw.1, ([] : BitString))) :=
        (Computable.pair Computable.fst (Computable.const [])).computableIn
      have hguard : ComputableIn {charOracle jumpSet}
          (fun p : (BitString × BitString) × BitString => decide (p.2 = p.1.2)) :=
        ((PrimrecRel.decide Primrec.eq).to_comp.comp Computable.snd
          (Computable.snd.comp Computable.fst)).computableIn
      exact PartrecIn.bind (PartrecIn.comp hVp hpair)
        (PartrecIn.cond hguard (ComputableIn.const 0).partrecIn PartrecIn.none)
    · rw [Part.dom_iff_mem]
      constructor
      · intro h
        exact ⟨0, Part.mem_bind_iff.mpr ⟨pw.2, h, by simp⟩⟩
      · rintro ⟨v, hv⟩
        obtain ⟨x, hx, hcond⟩ := Part.mem_bind_iff.mp hv
        by_cases hxy : x = pw.2
        · rwa [hxy] at hx
        · simp [hxy] at hcond
  have hprod' : PointToSet.IsREIn jumpSet (fun t : (ℕ × ℚ) × BitString =>
      produces V t.2 [] (Nat.bits t.1.1)) :=
    hprod.comp (f := fun t : (ℕ × ℚ) × BitString => (t.2, Nat.bits t.1.1))
      (Computable.snd.pair (natBits_computable.comp
        (Computable.fst.comp Computable.fst))).computableIn
  have hlt : Computable (fun t : (ℕ × ℚ) × BitString =>
      decide (t.1.2 < (1 / 2 : ℚ) ^ t.2.length)) :=
    computable₂_ratLt.comp (Computable.snd.comp Computable.fst)
      (exists_computable_KP_jump_eq_neg_log_lowerFreq_half_pow.comp
        (Primrec.list_length.comp Primrec.snd).to_comp)
  have heq : (fun w : ℕ × ℚ => (w.2 : ℝ) <
      ((2 : ℝ)⁻¹) ^ (KP V (Nat.bits w.1) []).toNat) =
      fun w => ∃ p, produces V p [] (Nat.bits w.1) ∧ w.2 < (1 / 2 : ℚ) ^ p.length := by
    funext w
    refine propext ⟨fun h => ?_, fun ⟨p, hp, hlt⟩ => ?_⟩
    · obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top (hfin w.1)
      refine ⟨p, hp, ?_⟩
      have hn : p.length = (KP V (Nat.bits w.1) []).toNat := by
        have := congrArg ENat.toNat hlen
        simpa [programLength] using this
      rw [hn]
      have h' : (w.2 : ℝ) < (((1 / 2 : ℚ) ^ (KP V (Nat.bits w.1) []).toNat : ℚ) : ℝ) := by
        simpa [one_div, inv_pow] using h
      exact_mod_cast h'
    · have hle : (KP V (Nat.bits w.1) []).toNat ≤ p.length := by
        have := KP_le_programLength_of_produces hp
        rw [← ENat.natCast_toNat (hfin w.1)] at this
        exact_mod_cast this
      have h1 : ((2 : ℝ)⁻¹) ^ p.length ≤ ((2 : ℝ)⁻¹) ^ (KP V (Nat.bits w.1) []).toNat :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
      have h2 : (w.2 : ℝ) < ((2 : ℝ)⁻¹) ^ p.length := by
        have : ((w.2 : ℚ) : ℝ) < (((1 / 2 : ℚ) ^ p.length : ℚ) : ℝ) := by exact_mod_cast hlt
        simpa [one_div, inv_pow] using this
      exact h2.trans_le h1
  unfold PointToSet.IsLowerSemicomputableIn
  rw [heq]
  exact (hprod'.and (PointToSet.isREIn_of_computable_decide hlt)).exists

/-- Step 4 of the proof of `exists_computable_KP_jump_eq_neg_log_lowerFreq` (the
upper bound of the coding theorem, relativized to `0'`): if `p` is a positive
`0'`-lower-semicomputable sequence with all finite partial sums at most `1`, then
`K^V(k) ≤ -log₂ pₖ + O(1)` for every optimal prefix-free `0'`-decompressor `V`.

Proof idea: the integer cost `g k = ⌊-log₂ pₖ⌋ + 1` (the least `n` with `2^{-n} < pₖ`) is
upper semicomputable relative to `0'` (`g k < q` iff some natural `n < q` has `2^{-n} < pₖ`),
and `∑ₖ 2^{-g k} ≤ ∑ₖ pₖ ≤ 1`. Apply `PointToSet.oracle_coding_finite_mass` with the domain
`{w | ∃ k, w = Nat.bits k}` to get `K^{opt}(k) ≤ g k + c`, then pass from the chosen optimal
machine to `V` by optimality of `V`, and `g k ≤ -log₂ pₖ + 1`. -/
private theorem exists_computable_KP_jump_eq_neg_log_lowerFreq_upper {V : Map}
    (hV : PointToSet.IsOptimalOraclePrefix jumpSet V) {p : ℕ → ℝ}
    (hp : PointToSet.IsLowerSemicomputableIn jumpSet p) (hpos : ∀ k, 0 < p k)
    (hsum : ∀ N, ∑ i ∈ Finset.range N, p i ≤ 1) :
    ∃ c : ℝ, ∀ k, ((KP V (Nat.bits k) []).toNat : ℝ) ≤ -Real.logb 2 (p k) + c := by
  classical
  have hex : ∀ k, ∃ n : ℕ, ((2 : ℝ)⁻¹) ^ n < p k := fun k =>
    exists_pow_lt_of_lt_one (hpos k) (by norm_num)
  let G : ℕ → ℕ := fun k => Nat.find (hex k)
  have hG : ∀ k, ((2 : ℝ)⁻¹) ^ (G k) < p k := fun k => Nat.find_spec (hex k)
  have hGmin : ∀ k n, ((2 : ℝ)⁻¹) ^ n < p k → G k ≤ n := fun k n h => Nat.find_min' (hex k) h
  have hp1 : ∀ k, p k ≤ 1 := by
    intro k
    refine le_trans ?_ (hsum (k + 1))
    exact Finset.single_le_sum (f := p) (fun i _ => (hpos i).le) (Finset.self_mem_range_succ k)
  have hGle : ∀ k, (G k : ℝ) ≤ -Real.logb 2 (p k) + 1 := by
    intro k
    rcases hk : G k with _ | m
    · have := Real.logb_nonpos (b := 2) (by norm_num) (hpos k).le (hp1 k)
      simp only [Nat.cast_zero]
      linarith
    · have h1 : p k ≤ ((2 : ℝ)⁻¹) ^ m := by
        by_contra h
        have := hGmin k m (not_le.mp h)
        omega
      have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (hpos k) h1
      have h3 : Real.logb 2 (((2 : ℝ)⁻¹) ^ m) = -(m : ℝ) := by
        rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
        ring
      push_cast
      linarith
  -- the coding domain and the integer cost
  let F : BitString → Prop := fun w => ∃ k, Nat.bits k = w
  let g : Subtype F → ℝ := fun w => (G (Classical.choose w.2) : ℝ)
  have hgk : ∀ (w : Subtype F) (k : ℕ), Nat.bits k = w.val → g w = G k := by
    intro w k hk
    have h1 := Classical.choose_spec w.2
    have : Classical.choose w.2 = k := natBits_injective (h1.trans hk.symm)
    simp only [g, this]
  have hug : PointToSet.IsUpperSemicomputableOnIn jumpSet F g := by
    let Q : (BitString × ℚ) × ((ℕ × ℕ) × ℚ) → Prop := fun x =>
      Nat.bits x.2.1.1 = x.1.1 ∧ ((x.2.1.2 : ℚ) < x.1.2) ∧
        (1 < x.2.2 * ((2 ^ x.2.1.2 : ℕ) : ℚ)) ∧ ((x.2.2 : ℝ) < p x.2.1.1)
    have hQ : PointToSet.IsREIn jumpSet Q := by
      have h1 : PointToSet.IsREIn jumpSet
          (fun x : (BitString × ℚ) × ((ℕ × ℕ) × ℚ) => Nat.bits x.2.1.1 = x.1.1) :=
        PointToSet.isREIn_of_computable_decide
          ((PrimrecRel.decide Primrec.eq).to_comp.comp (natBits_computable.comp (Computable.fst.comp
            (Computable.fst.comp Computable.snd))) (Computable.fst.comp Computable.fst))
      have h2 : PointToSet.IsREIn jumpSet
          (fun x : (BitString × ℚ) × ((ℕ × ℕ) × ℚ) => ((x.2.1.2 : ℚ) < x.1.2)) :=
        PointToSet.isREIn_of_computable_decide
          (computable₂_ratLt.comp
            (computable_nat_to_rat.comp (Computable.snd.comp (Computable.fst.comp Computable.snd)))
            (Computable.snd.comp Computable.fst))
      have h3 : PointToSet.IsREIn jumpSet
          (fun x : (BitString × ℚ) × ((ℕ × ℕ) × ℚ) =>
            (1 < x.2.2 * ((2 ^ x.2.1.2 : ℕ) : ℚ))) :=
        PointToSet.isREIn_of_computable_decide
          (computable₂_ratLt.comp (Computable.const (1 : ℚ))
            (computable₂_ratMul.comp (Computable.snd.comp Computable.snd)
              (computable_nat_to_rat.comp (comp_pow.comp
                (Computable.snd.comp (Computable.fst.comp Computable.snd))))))
      have h4 : PointToSet.IsREIn jumpSet
          (fun x : (BitString × ℚ) × ((ℕ × ℕ) × ℚ) => ((x.2.2 : ℝ) < p x.2.1.1)) :=
        hp.comp (f := fun x : (BitString × ℚ) × ((ℕ × ℕ) × ℚ) => (x.2.1.1, x.2.2))
          ((Computable.fst.comp (Computable.fst.comp Computable.snd)).pair
            (Computable.snd.comp Computable.snd)).computableIn
      exact h1.and (h2.and (h3.and h4))
    refine ⟨fun wq => ∃ b, Q (wq, b), hQ.exists, ?_, ?_⟩
    · rintro w q ⟨⟨⟨k, n⟩, r⟩, hw, hnq, hr1, hrp⟩
      refine ⟨⟨k, hw⟩, ?_⟩
      have hgw := hgk ⟨w, k, hw⟩ k hw
      rw [hgw]
      have hr : ((2 : ℝ)⁻¹) ^ n < r := by
        have : (1 : ℚ) < r * (2 ^ n : ℕ) := hr1
        have h' : (1 : ℝ) < (r : ℝ) * 2 ^ n := by exact_mod_cast this
        have h2n : (0 : ℝ) < 2 ^ n := by positivity
        rw [inv_pow, ← one_div, div_lt_iff₀ h2n]
        linarith
      have := hGmin k n (hr.trans hrp)
      calc (G k : ℝ) ≤ n := by exact_mod_cast this
        _ < q := by exact_mod_cast hnq
    · intro w ε hε
      obtain ⟨k, hk⟩ := w.2
      have hgw := hgk w k hk
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (G k : ℝ) hε)
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (hG k)
      refine ⟨q, ⟨((k, G k), r), hk, ?_, ?_, hr2⟩, ?_⟩
      · exact_mod_cast hq1
      · have h2n : (0 : ℝ) < 2 ^ G k := by positivity
        have h' : (1 : ℝ) < (r : ℝ) * 2 ^ G k := by
          rw [inv_pow, ← one_div, div_lt_iff₀ h2n] at hr1
          exact hr1
        exact_mod_cast h'
      · rw [hgw]; exact hq2
  -- the mass bound
  let e : ℕ ≃ Subtype F := Equiv.ofBijective (fun k => ⟨Nat.bits k, k, rfl⟩)
    ⟨fun a b h => natBits_injective (congrArg Subtype.val h),
      fun w => by
        obtain ⟨k, hk⟩ := w.2
        exact ⟨k, Subtype.ext hk⟩⟩
  have hge : ∀ k, g (e k) = G k := fun k => hgk (e k) k rfl
  have hmass : (∑' w : Subtype F, (2 : ENNReal) ^ (-g w)) ≤ 1 := by
    rw [← e.tsum_eq]
    have hterm : ∀ k, (2 : ENNReal) ^ (-g (e k)) ≤ ENNReal.ofReal (p k) := by
      intro k
      rw [hge, ENNReal.rpow_neg, ENNReal.rpow_natCast]
      have : ENNReal.ofReal (((2 : ℝ)⁻¹) ^ G k) = ((2 : ENNReal) ^ G k)⁻¹ := by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
          ENNReal.inv_pow]
        simp
      rw [← this]
      exact ENNReal.ofReal_le_ofReal (hG k).le
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hpos i).le)]
    simpa using ENNReal.ofReal_le_ofReal (hsum N)
  obtain ⟨c0, hc0⟩ := PointToSet.oracle_coding_finite_mass jumpSet F g hug 1 hmass
      ENNReal.one_lt_top
  obtain ⟨hU1, hU2, _⟩ := PointToSet.exists_optimalOraclePrefix_spec jumpSet
  obtain ⟨c1, hc1⟩ := hV.2.2 _ hU1 hU2
  refine ⟨c0 + c1 + 1, fun k => ?_⟩
  have hfin := PointToSet.exists_optimalOraclePrefix_finite jumpSet (Nat.bits k) []
  have hn : (KP V (Nat.bits k) []).toNat ≤
      PointToSet.oracleComplexity jumpSet (Nat.bits k) + c1 := by
    have h1 := ENat.toNat_le_toNat (hc1 (Nat.bits k) [])
      (WithTop.add_ne_top.2 ⟨hfin, ENat.natCast_ne_top c1⟩)
    rw [ENat.toNat_add hfin (ENat.natCast_ne_top c1), ENat.toNat_natCast] at h1
    exact h1
  have h2 := hc0 ⟨Nat.bits k, k, rfl⟩
  have h3 : g ⟨Nat.bits k, k, rfl⟩ = G k := hgk _ k rfl
  rw [h3] at h2
  have h4 : ((KP V (Nat.bits k) []).toNat : ℝ) ≤
      (PointToSet.oracleComplexity jumpSet (Nat.bits k) : ℝ) + c1 := by exact_mod_cast hn
  have := hGle k
  linarith

/-- Step 5 of the proof of `exists_computable_KP_jump_eq_neg_log_lowerFreq`
(domination turned into a complexity bound): if `p` is positive and `q k = 2^{-K^V(k)}` is
dominated, `q k ≤ c * p k` with `c > 0`, then `-log₂ c ≤ K^V(k) + log₂ pₖ`. -/
private theorem exists_computable_KP_jump_eq_neg_log_lowerFreq_lower {V : Map}
    {p : ℕ → ℝ} (hpos : ∀ k, 0 < p k)
    {c : ℝ} (hc : 0 < c)
    (hdom : ∀ k, ((2 : ℝ)⁻¹) ^ (KP V (Nat.bits k) []).toNat ≤ c * p k) (k : ℕ) :
    -Real.logb 2 c ≤ ((KP V (Nat.bits k) []).toNat : ℝ) + Real.logb 2 (p k) := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hq : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ (KP V (Nat.bits k) []).toNat := by positivity
  have hlog := Real.logb_le_logb_of_le h2 hq (hdom k)
  rw [Real.logb_mul hc.ne' (hpos k).ne', Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one
    h2] at hlog
  linarith

/-- **SUV Section 6.4.3 (printed p. 210), unnumbered.** An equivalent definition of
`0'`-relativized prefix complexity: for an appropriate computable sequence `f`, all lower
frequencies are positive and `K^{0'}(k) = -log₂ pₖ + O(1)`. `K^{0'}(k)` is
`KP V (Nat.bits k) []` for an optimal prefix-free `0'`-decompressor `V`, and the `toNat` is
harmless because it is finite (`exists_optimalOraclePrefix_finite`). The positivity conjunct
excludes the junk value `Real.logb 2 0 = 0`.

Proof idea: `exists_computable_lowerFreq_maximal` and the relativized coding theorem
`K^{0'} = -log m^{0'} + O(1)`. -/
theorem exists_computable_KP_jump_eq_neg_log_lowerFreq :
    ∃ f : ℕ → ℕ, Computable f ∧ (∀ k, 0 < lowerFreq f k) ∧
      ∀ V : Map, PointToSet.IsOptimalOraclePrefix jumpSet V →
        ∃ c : ℝ, ∀ k, |((KP V (Nat.bits k) []).toNat : ℝ) + Real.logb 2 (lowerFreq f k)| ≤ c := by
  obtain ⟨f, hf, hmax⟩ := exists_computable_lowerFreq_maximal
  have hlsc := isLowerSemicomputableIn_jumpSet_lowerFreq hf
  have hsum := sum_lowerFreq_le_one f
  obtain ⟨V0, hV0⟩ := PointToSet.exists_optimalOraclePrefix jumpSet
  have hpos : ∀ k, 0 < lowerFreq f k := by
    intro k
    obtain ⟨c, hc, hdom⟩ := hmax _ (exists_computable_KP_jump_eq_neg_log_lowerFreq_lsc hV0)
      (fun i => by positivity) (exists_computable_KP_jump_eq_neg_log_lowerFreq_kraft hV0)
    have hq : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ (KP V0 (Nat.bits k) []).toNat := by positivity
    exact pos_of_mul_pos_right (hq.trans_le (hdom k)) hc.le
  refine ⟨f, hf, hpos, fun V hV => ?_⟩
  obtain ⟨c1, hc1⟩ := exists_computable_KP_jump_eq_neg_log_lowerFreq_upper hV hlsc hpos hsum
  obtain ⟨c, hc, hdom⟩ := hmax _ (exists_computable_KP_jump_eq_neg_log_lowerFreq_lsc hV)
    (fun i => by positivity) (exists_computable_KP_jump_eq_neg_log_lowerFreq_kraft hV)
  refine ⟨max c1 (Real.logb 2 c), fun k => ?_⟩
  have h1 := hc1 k
  have h2 := exists_computable_KP_jump_eq_neg_log_lowerFreq_lower hpos hc hdom k
  rw [abs_le]
  constructor
  · linarith [le_max_right c1 (Real.logb 2 c)]
  · linarith [le_max_left c1 (Real.logb 2 c)]

private theorem exists_computable_lowerFreq_eq_uniformLiminf_aux_liminf {x : ℝ}
    (q : ℕ → ℚ) (R : ℕ → ℕ → Bool) (L U : ℚ) (hL : (L : ℝ) < x) (hU : x < (U : ℝ))
    (hx : ∀ y : ℚ, (y : ℝ) < x ↔ ∃ i, q i = y ∧ ∀ b, R i b = true) :
    Filter.liminf (fun n => (exists_computable_liminf_eq_seq q R L U n : ℝ)) Filter.atTop = x := by
  classical
  have hLU : L ≤ U := by exact_mod_cast (hL.trans hU).le
  have htrue : ∀ i, (∀ b, R i b = true) → (q i : ℝ) < x :=
    fun i h => (hx (q i)).2 ⟨i, rfl, h⟩
  have hs_ge : ∀ k, L ≤ exists_computable_liminf_eq_seq q R L U k :=
    exists_computable_liminf_eq_le_seq_L q R L U
  have hs_le : ∀ k, exists_computable_liminf_eq_seq q R L U k ≤ U := by
    intro k
    rw [exists_computable_liminf_eq_seq_le_iff]
    refine ⟨hLU, fun i _ => ?_⟩
    unfold exists_computable_liminf_eq_val
    split_ifs
    · exact min_le_right _ _
    · exact hLU
  have hB : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => (exists_computable_liminf_eq_seq q R L U n : ℝ)) :=
    Filter.isBoundedUnder_of ⟨U, fun n => by exact_mod_cast hs_le n⟩
  have hB' : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => (exists_computable_liminf_eq_seq q R L U n : ℝ)) :=
    Filter.isBoundedUnder_of ⟨L, fun n => by exact_mod_cast hs_ge n⟩
  have main : ∀ (c : ℚ), x < (c : ℝ) → ∀ N,
      ∃ k ≥ N, exists_computable_liminf_eq_seq q R L U k ≤ c := by
    intro c hc N
    have hLc : L ≤ c := by exact_mod_cast (hL.trans hc).le
    have hbad_false : ∀ i, c < min (q i) U → ¬ ∀ b, R i b = true := by
      intro i hi h
      have h1 : (q i : ℝ) < c := (htrue i h).trans hc
      have h2 : q i < c := by exact_mod_cast h1
      exact absurd hi (not_lt.2 ((min_le_left _ _).trans h2.le))
    by_cases hS : ∃ j, c < min (q j) U ∧ exists_computable_liminf_eq_alive R j N = true
    · set j0 := Nat.find hS with hj0def
      have hj0 : c < min (q j0) U ∧ exists_computable_liminf_eq_alive R j0 N = true :=
        Nat.find_spec hS
      have hex : ∃ b, ¬ R j0 b = true := by
        by_contra hne
        push Not at hne
        exact hbad_false j0 hj0.1 hne
      set k := Nat.find hex with hkdef
      have hk1 : ¬ R j0 k = true := Nat.find_spec hex
      have hk2 : ∀ b < k, R j0 b = true := fun b hb => by
        have := Nat.find_min hex hb
        simpa using this
      have hkN : N ≤ k := by
        by_contra hlt
        push Not at hlt
        exact hk1 ((exists_computable_liminf_eq_alive_iff R j0 N).1 hj0.2 k hlt)
      refine ⟨k, hkN, ?_⟩
      rw [exists_computable_liminf_eq_seq_le_iff]
      refine ⟨hLc, fun i hi => ?_⟩
      unfold exists_computable_liminf_eq_val
      split_ifs with hcond
      · by_contra hgt
        push Not at hgt
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨hg, ha⟩ := hcond
        have haN : exists_computable_liminf_eq_alive R i N = true :=
          (exists_computable_liminf_eq_alive_iff R i N).2 fun b hb =>
            (exists_computable_liminf_eq_alive_iff R i (k + 1)).1 ha b (by omega)
        have hjle : j0 ≤ i := Nat.find_min' hS ⟨hgt, haN⟩
        exact ((exists_computable_liminf_eq_good_iff R i k).1 hg j0 hjle)
          ((exists_computable_liminf_eq_changed_iff R j0 k).2
            ⟨(exists_computable_liminf_eq_alive_iff R j0 k).2 hk2,
              fun h => hk1 ((exists_computable_liminf_eq_alive_iff R j0 (k + 1)).1 h k
                (by omega))⟩)
      · exact hLc
    · refine ⟨N, le_rfl, ?_⟩
      rw [exists_computable_liminf_eq_seq_le_iff]
      refine ⟨hLc, fun i hi => ?_⟩
      unfold exists_computable_liminf_eq_val
      split_ifs with hcond
      · by_contra hgt
        push Not at hgt
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨hg, ha⟩ := hcond
        exact hS ⟨i, hgt, (exists_computable_liminf_eq_alive_iff R i N).2 fun b hb =>
          (exists_computable_liminf_eq_alive_iff R i (N + 1)).1 ha b (by omega)⟩
      · exact hLc
  have hev : ∀ y : ℚ, (y : ℝ) < x →
      ∀ᶠ k in Filter.atTop, (y : ℝ) ≤ (exists_computable_liminf_eq_seq q R L U k : ℝ) := by
    intro y hy
    obtain ⟨i, hiy, hi⟩ := (hx y).1 hy
    obtain ⟨K, hK⟩ := exists_computable_liminf_eq_eventually_unchanged R i
    filter_upwards [Filter.eventually_ge_atTop (max K (i + 1))] with k hk
    have hk1 : K ≤ k := le_trans (le_max_left _ _) hk
    have hk2 : i < k := lt_of_lt_of_le (Nat.lt_succ_self i) (le_trans (le_max_right _ _) hk)
    have hgood : exists_computable_liminf_eq_good R i k = true :=
      (exists_computable_liminf_eq_good_iff R i k).2 fun j hj => hK k hk1 j hj
    have halive : exists_computable_liminf_eq_alive R i (k + 1) = true :=
      (exists_computable_liminf_eq_alive_iff R i (k + 1)).2 fun b _ => hi b
    have hyU : y ≤ U := by exact_mod_cast (hy.trans hU).le
    have hv : exists_computable_liminf_eq_val q R L U k i = y := by
      unfold exists_computable_liminf_eq_val
      rw [ite_eq_left (by simp [hgood, halive]), hiy]
      exact min_eq_left hyU
    have h3 := exists_computable_liminf_eq_val_le_seq q R L U k i hk2
    rw [hv] at h3
    exact_mod_cast h3
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    refine le_trans (Filter.liminf_le_of_frequently_le (a := (c : ℝ)) ?_ hB') hc2.le
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨k, hkN, hk⟩ := main c hc1 N
    exact ⟨k, hkN, by exact_mod_cast hk⟩
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨y, hy1, hy2⟩ := exists_rat_btwn hc
    exact lt_of_lt_of_le hy1 (Filter.le_liminf_of_le hB.isCoboundedUnder_ge (hev y hy2))
private theorem exists_computable_lowerFreq_eq_uniformLiminf_aux_comp
    (q : ℕ → ℕ → ℚ) (R : ℕ → ℕ → ℕ → Bool) (L U : ℚ)
    (hq : Computable (fun p : ℕ × ℕ => q p.1 p.2))
    (hR : Computable (fun p : ℕ × ℕ × ℕ => R p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × ℕ =>
      exists_computable_liminf_eq_seq (q p.1) (R p.1) L U p.2) := by
  have halive : Computable (fun p : ℕ × ℕ × ℕ =>
      exists_computable_liminf_eq_alive (R p.1) p.2.1 p.2.2) := by
    have hl : Computable (fun p : ℕ × ℕ × ℕ => List.range p.2.2) :=
      Primrec.list_range.to_comp.comp (Computable.snd.comp Computable.snd)
    have hh : Computable₂ (fun (p : ℕ × ℕ × ℕ) (u : ℕ × Bool) => R p.1 p.2.1 u.1 && u.2) :=
      (Primrec.and.to_comp.comp
        (hR.comp (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
            (Computable.fst.comp Computable.snd))))
        (Computable.snd.comp Computable.snd)).to₂
    exact Computable.list_foldr hl (Computable.const true) hh
  have hchanged : Computable (fun p : ℕ × ℕ × ℕ =>
      exists_computable_liminf_eq_changed (R p.1) p.2.1 p.2.2) :=
    (Primrec.and.to_comp.comp halive
      (Primrec.not.to_comp.comp
        (halive.comp
          (Computable.pair Computable.fst
            (Computable.pair (Computable.fst.comp Computable.snd)
              (Primrec.succ.to_comp.comp (Computable.snd.comp Computable.snd))))))).of_eq
      fun _ => rfl
  have hgood : Computable (fun p : ℕ × ℕ × ℕ =>
      exists_computable_liminf_eq_good (R p.1) p.2.1 p.2.2) := by
    have hl : Computable (fun p : ℕ × ℕ × ℕ => List.range (p.2.1 + 1)) :=
      Primrec.list_range.to_comp.comp
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
    have hh : Computable₂ (fun (p : ℕ × ℕ × ℕ) (u : ℕ × Bool) =>
        !exists_computable_liminf_eq_changed (R p.1) u.1 p.2.2 && u.2) :=
      (Primrec.and.to_comp.comp
        (Primrec.not.to_comp.comp
          (hchanged.comp (Computable.pair (Computable.fst.comp Computable.fst)
            (Computable.pair (Computable.fst.comp Computable.snd)
              (Computable.snd.comp (Computable.snd.comp Computable.fst))))))
        (Computable.snd.comp Computable.snd)).to₂
    have key := Computable.list_foldr hl (Computable.const true) hh
    exact key
  have hval : Computable (fun p : ℕ × ℕ × ℕ =>
      exists_computable_liminf_eq_val (q p.1) (R p.1) L U p.2.1 p.2.2) := by
    have hc1 : Computable (fun p : ℕ × ℕ × ℕ =>
        exists_computable_liminf_eq_good (R p.1) p.2.2 p.2.1) :=
      hgood.comp (g := fun p : ℕ × ℕ × ℕ => (p.1, p.2.2, p.2.1)) (Computable.pair Computable.fst
        (Computable.pair (Computable.snd.comp Computable.snd)
          (Computable.fst.comp Computable.snd)))
    have hc2 : Computable (fun p : ℕ × ℕ × ℕ =>
        exists_computable_liminf_eq_alive (R p.1) p.2.2 (p.2.1 + 1)) :=
      halive.comp (g := fun p : ℕ × ℕ × ℕ => (p.1, p.2.2, p.2.1 + 1))
          (Computable.pair Computable.fst
        (Computable.pair (Computable.snd.comp Computable.snd)
          (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))))
    have hc : Computable (fun p : ℕ × ℕ × ℕ =>
        exists_computable_liminf_eq_good (R p.1) p.2.2 p.2.1 &&
          exists_computable_liminf_eq_alive (R p.1) p.2.2 (p.2.1 + 1)) :=
      Primrec.and.to_comp.comp hc1 hc2
    have hqi : Computable (fun p : ℕ × ℕ × ℕ => q p.1 p.2.2) :=
      hq.comp (g := fun p : ℕ × ℕ × ℕ => (p.1, p.2.2))
        (Computable.pair Computable.fst (Computable.snd.comp Computable.snd))
    have hmin : Computable (fun p : ℕ × ℕ × ℕ =>
        cond (decide (q p.1 p.2.2 ≤ U)) (q p.1 p.2.2) U) :=
      Computable.cond (exists_computable_liminf_eq_ratLe.comp hqi (Computable.const U)) hqi
        (Computable.const U)
    exact (Computable.cond hc hmin (Computable.const L)).of_eq fun p => by
      simp only [exists_computable_liminf_eq_val]
      cases hg : (exists_computable_liminf_eq_good (R p.1) p.2.2 p.2.1 &&
        exists_computable_liminf_eq_alive (R p.1) p.2.2 (p.2.1 + 1)) <;> simp [min_def]
  have hl : Computable (fun p : ℕ × ℕ => List.range p.2) :=
    Primrec.list_range.to_comp.comp Computable.snd
  have hh : Computable₂ (fun (p : ℕ × ℕ) (u : ℕ × ℚ) =>
      max (exists_computable_liminf_eq_val (q p.1) (R p.1) L U p.2 u.1) u.2) := by
    have hv : Computable (fun x : (ℕ × ℕ) × (ℕ × ℚ) =>
        exists_computable_liminf_eq_val (q x.1.1) (R x.1.1) L U x.1.2 x.2.1) :=
      hval.comp (g := fun x : (ℕ × ℕ) × (ℕ × ℚ) => (x.1.1, x.1.2, x.2.1))
        (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp Computable.fst)
          (Computable.fst.comp Computable.snd)))
    have hm : Computable (fun x : (ℕ × ℕ) × (ℕ × ℚ) => x.2.2) :=
      Computable.snd.comp Computable.snd
    have hc : Computable (fun x : (ℕ × ℕ) × (ℕ × ℚ) =>
        cond (decide (exists_computable_liminf_eq_val (q x.1.1) (R x.1.1) L U x.1.2 x.2.1
          ≤ x.2.2)) x.2.2
          (exists_computable_liminf_eq_val (q x.1.1) (R x.1.1) L U x.1.2 x.2.1)) :=
      Computable.cond (exists_computable_liminf_eq_ratLe.comp hv hm) hm hv
    exact (hc.to₂ (α := ℕ × ℕ) (β := ℕ × ℚ)).of_eq fun p => by
      simp [max_def]
  have key := Computable.list_foldr hl (Computable.const L) hh
  exact key

/-- Step 1 of the proof of `exists_computable_lowerFreq_eq`: the uniform version of
SUV Problem 211. If `q` is a `0'`-lower-semicomputable sequence in `[0, 1]`, there is a single
computable table of rationals `r n k ∈ [0, 1]` such that, for every `k`, `q k` is the `liminf`
of the column `n ↦ r n k`.

Proof idea (book's hint for Problem 211, run uniformly in `k`): `q k` is the supremum of a
`0'`-computable (in `k`) sequence `r_{k,j}`. Each `r_{k,j}` is the limit of a computable sequence
`r_{k,j,t}` that stabilizes. Let `s_{k,t}` be the maximum of `r_{k,0,t}, …, r_{k,u-1,t}`, where
`u` is the least index with `r_{k,u,t} ≠ r_{k,u,t-1}`. Then `liminf_t s_{k,t} = q k`. Enumerate
the pairs `(k, t)` into a single index `n` that makes the table computable, and clamp to
`[0, 1]` (harmless: `0 ≤ q k ≤ 1`). -/
theorem exists_computable_lowerFreq_eq_uniformLiminf {q : ℕ → ℝ}
    (hq : PointToSet.IsLowerSemicomputableIn jumpSet q) (h0 : ∀ i, 0 ≤ q i)
    (h1 : ∀ N, ∑ i ∈ Finset.range N, q i ≤ 1) :
    ∃ r : ℕ → ℕ → ℚ, Computable (fun p : ℕ × ℕ => r p.1 p.2) ∧ (∀ n k, 0 ≤ r n k) ∧
      (∀ n k, r n k ≤ 1) ∧
      ∀ k, Filter.liminf (fun n => (r n k : ℝ)) Filter.atTop = q k := by
  classical
  obtain ⟨P, hPc, hP⟩ := exists_computable_le_lowerFreq_step1_sigma2 hq
  have hdec : Computable (fun i : ℕ => (Denumerable.ofNat ℚ (Nat.unpair i).1 : ℚ)) :=
    (Primrec.ofNat ℚ).to_comp.comp (Primrec.fst.comp Primrec.unpair).to_comp
  set qe : ℕ → ℚ := fun i => Denumerable.ofNat ℚ (Nat.unpair i).1 with hqe
  set Rk : ℕ → ℕ → ℕ → Bool := fun k i b => P (k, qe i, (Nat.unpair i).2, b) with hRk
  have hq' : Computable (fun p : ℕ × ℕ => (fun _ : ℕ => qe) p.1 p.2) :=
    hdec.comp Computable.snd
  have hR : Computable (fun p : ℕ × ℕ × ℕ => Rk p.1 p.2.1 p.2.2) :=
    hPc.comp (Computable.pair Computable.fst
      (Computable.pair (hdec.comp (Computable.fst.comp Computable.snd))
        (Computable.pair
          ((Primrec.snd.comp Primrec.unpair).to_comp.comp (Computable.fst.comp Computable.snd))
          (Computable.snd.comp Computable.snd))))
  have hcomp := exists_computable_lowerFreq_eq_uniformLiminf_aux_comp
    (fun _ : ℕ => qe) Rk (-1) 2 hq' hR
  have hqle : ∀ k, q k ≤ 1 := fun k =>
    (Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_range.2 (Nat.lt_succ_self k))).trans
      (h1 (k + 1))
  refine ⟨fun n k => min 1 (max 0 (exists_computable_liminf_eq_seq qe (Rk k) (-1) 2 n)),
    ?_, fun n k => ?_, fun n k => min_le_left _ _, fun k => ?_⟩
  · have hs : Computable (fun p : ℕ × ℕ =>
        exists_computable_liminf_eq_seq qe (Rk p.2) (-1) 2 p.1) :=
      Computable.comp (f := fun p : ℕ × ℕ =>
          exists_computable_liminf_eq_seq qe (Rk p.1) (-1) 2 p.2)
        (g := fun p : ℕ × ℕ => (p.2, p.1)) hcomp
        (Computable.pair Computable.snd Computable.fst)
    have hm0 : Computable (fun p : ℕ × ℕ =>
        cond (decide (exists_computable_liminf_eq_seq qe (Rk p.2) (-1) 2 p.1 ≤ 0)) 0
          (exists_computable_liminf_eq_seq qe (Rk p.2) (-1) 2 p.1)) :=
      Computable.cond (exists_computable_liminf_eq_ratLe.comp hs (Computable.const 0))
        (Computable.const 0) hs
    have hm1 : Computable (fun p : ℕ × ℕ =>
        cond (decide ((cond (decide (exists_computable_liminf_eq_seq qe (Rk p.2) (-1) 2 p.1 ≤ 0))
          0 (exists_computable_liminf_eq_seq qe (Rk p.2) (-1) 2 p.1)) ≤ 1))
          (cond (decide (exists_computable_liminf_eq_seq qe (Rk p.2) (-1) 2 p.1 ≤ 0))
            0 (exists_computable_liminf_eq_seq qe (Rk p.2) (-1) 2 p.1)) 1) :=
      Computable.cond (exists_computable_liminf_eq_ratLe.comp hm0 (Computable.const 1))
        hm0 (Computable.const 1)
    refine hm1.of_eq fun p => ?_
    by_cases ha : exists_computable_liminf_eq_seq qe (Rk p.2) (-1) 2 p.1 ≤ 0
    · simp [ha]
    · have ha' := not_le.1 ha
      by_cases hb : exists_computable_liminf_eq_seq qe (Rk p.2) (-1) 2 p.1 ≤ 1
      · simp [ha, hb, ha'.le]
      · simp [ha, hb, ha'.le, (not_le.1 hb).le]
  · exact le_min zero_le_one (le_max_left _ _)
  · have hx : ∀ y : ℚ, (y : ℝ) < q k ↔ ∃ i, qe i = y ∧ ∀ b, Rk k i b = true := by
      intro y
      rw [hP k y]
      constructor
      · rintro ⟨a, ha⟩
        have he : Denumerable.ofNat ℚ (Denumerable.eqv ℚ y) = y :=
          (Denumerable.eqv ℚ).symm_apply_apply y
        refine ⟨Nat.pair (Denumerable.eqv ℚ y) a, ?_, fun b => ?_⟩
        · change Denumerable.ofNat ℚ (Nat.unpair (Nat.pair (Denumerable.eqv ℚ y) a)).1 = y
          rw [Nat.unpair_pair]
          exact he
        · change P (k, Denumerable.ofNat ℚ (Nat.unpair (Nat.pair (Denumerable.eqv ℚ y) a)).1,
            (Nat.unpair (Nat.pair (Denumerable.eqv ℚ y) a)).2, b) = true
          rw [Nat.unpair_pair]
          dsimp only
          rw [he]
          exact ha b
      · rintro ⟨i, hi, h⟩
        refine ⟨(Nat.unpair i).2, fun b => ?_⟩
        rw [← hi]
        exact h b
    have hL : ((-1 : ℚ) : ℝ) < q k := by push_cast; linarith [h0 k]
    have hU : q k < ((2 : ℚ) : ℝ) := by push_cast; linarith [hqle k]
    have hlim := exists_computable_lowerFreq_eq_uniformLiminf_aux_liminf qe (Rk k) (-1) 2
      hL hU hx
    set s : ℕ → ℚ := fun n => exists_computable_liminf_eq_seq qe (Rk k) (-1) 2 n with hs
    have hs_ge : ∀ n, (-1 : ℚ) ≤ s n := fun n =>
      exists_computable_liminf_eq_le_seq_L qe (Rk k) (-1) 2 n
    have hs_le : ∀ n, s n ≤ 2 := by
      intro n
      change exists_computable_liminf_eq_seq qe (Rk k) (-1) 2 n ≤ 2
      rw [exists_computable_liminf_eq_seq_le_iff]
      refine ⟨by norm_num, fun i _ => ?_⟩
      unfold exists_computable_liminf_eq_val
      split_ifs
      · exact min_le_right _ _
      · norm_num
    have hB : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n => (s n : ℝ)) :=
      Filter.isBoundedUnder_of ⟨2, fun n => by exact_mod_cast hs_le n⟩
    have hB' : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => (s n : ℝ)) :=
      Filter.isBoundedUnder_of ⟨-1, fun n => by exact_mod_cast hs_ge n⟩
    have hmono : Monotone (fun x : ℝ => min 1 (max 0 x)) := fun a b hab =>
      min_le_min le_rfl (max_le_max le_rfl hab)
    have hcont : ContinuousAt (fun x : ℝ => min 1 (max 0 x))
        (Filter.liminf (fun n => (s n : ℝ)) Filter.atTop) :=
      (continuous_const.min (continuous_const.max continuous_id)).continuousAt
    have key := Monotone.map_liminf_of_continuousAt hmono (fun n => (s n : ℝ)) hcont
      hB.isCoboundedUnder_ge hB'
    have hlim' : Filter.liminf (fun n => (s n : ℝ)) Filter.atTop = q k := hlim
    rw [hlim'] at key
    have hfix : min 1 (max 0 (q k)) = q k := by
      rw [max_eq_right (h0 k), min_eq_right (hqle k)]
    rw [hfix] at key
    rw [key]
    congr 1
    funext n
    simp [Function.comp]
    rfl

end GeneralScheme
end Kolmogorov
