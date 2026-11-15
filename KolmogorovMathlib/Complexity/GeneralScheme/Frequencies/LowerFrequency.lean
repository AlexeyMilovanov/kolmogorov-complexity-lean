import KolmogorovMathlib.Complexity.GeneralScheme.OracleDefs
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicRandomness.OracleSemidecision
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.Oracle.PrefixComplexity.MonotonicityThreshold
import KolmogorovMathlib.MonotoneComplexity.Omega.PredictCover
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools

/-!
# Lower Frequency

The lower frequency `liminf_n (#{i < n | f i = k} / n)` of a symbol `k` in a sequence
`f : ℕ → ℕ`, together with the facts needed to compute it: the counting function `countOcc`
satisfies the usual recursion, and the rational lower bounds on the lower frequency of a
computable sequence form a set that is lower semicomputable relative to the jump oracle.
-/

namespace Kolmogorov

namespace GeneralScheme

/-- The number of occurrences of `k` among `f 0, …, f (n - 1)`. -/
def countOcc (f : ℕ → ℕ) (k n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => f i = k)).card

/-- The lower frequency of `k` in the sequence `f`: `liminf_n countOcc f k n / n`. The sequence
lies in `[0, 1]`, so the real `liminf` is meaningful. -/
noncomputable def lowerFreq (f : ℕ → ℕ) (k : ℕ) : ℝ :=
  Filter.liminf (fun n => (countOcc f k n : ℝ) / n) Filter.atTop

open Classical in
/-- The number of `i < n` such that the partial function `f` is defined at `i` with value `k`. -/
noncomputable def countOccPart (f : ℕ →. ℕ) (k n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => k ∈ f i)).card

/-- The lower frequency of `k` in a partial sequence `f` (SUV Problem 213). -/
noncomputable def lowerFreqPart (f : ℕ →. ℕ) (k : ℕ) : ℝ :=
  Filter.liminf (fun n => (countOccPart f k n : ℝ) / n) Filter.atTop

/-- **SUV Section 6.4.3 (printed p. 209), helper.** Lower frequencies are non-negative: every
frequency `countOcc f k n / n` lies in `[0, 1]`. -/
theorem lowerFreq_nonneg (f : ℕ → ℕ) (k : ℕ) : 0 ≤ lowerFreq f k := by
  refine Filter.le_liminf_of_le
    (Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := 1) fun n => ?_)
    (Filter.Eventually.of_forall fun n => by positivity)
  have h : (countOcc f k n : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (div_le_one (by exact_mod_cast hn)).2 h

/-- **SUV Section 6.4.3 (printed p. 209), unnumbered.** The lower frequencies of any sequence
satisfy `∑ₖ pₖ ≤ 1`, stated for every finite partial sum.

Proof idea: if a finite sum of `liminf`s exceeded `1`, then for large `n` the sum of the
corresponding frequencies among the first `n` terms would exceed `1`. -/
theorem sum_lowerFreq_le_one (f : ℕ → ℕ) (N : ℕ) :
    ∑ k ∈ Finset.range N, lowerFreq f k ≤ 1 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε' : 0 < ε / (N + 1) := by positivity
  have hb : ∀ k, Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => (countOcc f k n : ℝ) / n) := fun k =>
    Filter.isBoundedUnder_of ⟨0, fun n => by positivity⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ k ∈ Finset.range N,
      lowerFreq f k - ε / (N + 1) < (countOcc f k n : ℝ) / n := by
    rw [Filter.eventually_all_finset]
    intro k _
    exact Filter.eventually_lt_of_lt_liminf (by unfold lowerFreq; linarith) (hb k)
  obtain ⟨n, hn, hn1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsum : ∑ k ∈ Finset.range N, countOcc f k n ≤ n := by
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
  have hsumR : ∑ k ∈ Finset.range N, (countOcc f k n : ℝ) / n ≤ 1 := by
    rw [← Finset.sum_div, div_le_one hnpos]
    exact_mod_cast hsum
  have h1 : ∑ k ∈ Finset.range N, (lowerFreq f k - ε / (N + 1)) ≤
      ∑ k ∈ Finset.range N, (countOcc f k n : ℝ) / n :=
    Finset.sum_le_sum fun k hk => (hn k hk).le
  rw [Finset.sum_sub_distrib] at h1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have h2 : (N : ℝ) * (ε / (N + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Counting recursion: `countOcc f k (n + 1)` is `countOcc f k n` plus one if `f n = k`. -/
lemma isLowerSemicomputableIn_jumpSet_lowerFreq_countOcc_succ (f : ℕ → ℕ) (k n : ℕ) :
    countOcc f k (n + 1) = countOcc f k n + if f n = k then 1 else 0 := by
  unfold countOcc
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : f n = k <;> simp [h]

private lemma isLowerSemicomputableIn_jumpSet_lowerFreq_computable_countOcc {f : ℕ → ℕ}
    (hf : Computable f) : Computable (fun p : ℕ × ℕ => countOcc f p.1 p.2) := by
  have hh : Computable₂ (fun (p : ℕ × ℕ) (u : ℕ × ℕ) =>
      u.2 + cond (f u.1 == p.1) 1 0) :=
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.cond (Primrec.beq.to_comp.comp (hf.comp (Computable.fst.comp Computable.snd))
        (Computable.fst.comp Computable.fst)) (Computable.const 1) (Computable.const 0))).to₂
  have h := Computable.nat_rec (f := fun p : ℕ × ℕ => p.2) (g := fun _ => (0 : ℕ))
    (h := fun (p : ℕ × ℕ) (u : ℕ × ℕ) => u.2 + cond (f u.1 == p.1) 1 0)
    Computable.snd (Computable.const 0) hh
  refine h.of_eq fun p => ?_
  obtain ⟨k, n⟩ := p
  dsimp only
  induction n with
  | zero => simp [countOcc]
  | succ n ih =>
    rw [isLowerSemicomputableIn_jumpSet_lowerFreq_countOcc_succ]
    simp only [← ih]
    by_cases hc : f n = k <;> simp [hc]

private lemma isLowerSemicomputableIn_jumpSet_lowerFreq_div_le_one (f : ℕ → ℕ) (k n : ℕ) :
    (countOcc f k n : ℝ) / n ≤ 1 := by
  have h : (countOcc f k n : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (div_le_one (by exact_mod_cast hn)).2 h

/-- Characterization of `r < pₖ` through the Σ₂ form. -/
private lemma isLowerSemicomputableIn_jumpSet_lowerFreq_iff (f : ℕ → ℕ) (k : ℕ) (r : ℝ) :
    r < lowerFreq f k ↔
      ∃ p : ℚ, r < p ∧ ∃ N : ℕ, ∀ m ≥ N, p * (m : ℚ) ≤ (countOcc f k m : ℚ) := by
  constructor
  · intro hr
    obtain ⟨p, hrp, hpL⟩ := exists_rat_btwn hr
    have hb : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n => (countOcc f k n : ℝ) / n) :=
      Filter.isBoundedUnder_of ⟨0, fun n => by positivity⟩
    have hev := Filter.eventually_lt_of_lt_liminf (show (p : ℝ) < Filter.liminf
      (fun n => (countOcc f k n : ℝ) / n) Filter.atTop from hpL) hb
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨p, hrp, max N 1, fun m hm => ?_⟩
    have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
    have hmN : N ≤ m := (le_max_left _ _).trans hm
    have h := hN m hmN
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    rw [lt_div_iff₀ hmpos] at h
    exact_mod_cast h.le
  · rintro ⟨p, hrp, N, hN⟩
    refine lt_of_lt_of_le hrp (Filter.le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := 1) fun n =>
        isLowerSemicomputableIn_jumpSet_lowerFreq_div_le_one f k n) ?_)
    filter_upwards [Filter.eventually_ge_atTop (max N 1)] with m hm
    have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
    have hmN : N ≤ m := (le_max_left _ _).trans hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    rw [le_div_iff₀ hmpos]
    exact_mod_cast hN m hmN

/-- **SUV Theorem 135 (Section 6.4.3, printed p. 209).** For a computable sequence `f`, the
function `k ↦ pₖ` (lower frequency) is `0'`-lower-semicomputable.

Proof idea: `r < pₖ` iff there are a rational `p > r` and an `N` such that the frequency of `k`
among the first `n` terms exceeds `p` for all `n > N`. The inner property is co-enumerable,
hence `0'`-decidable, so `r < pₖ` is `0'`-enumerable. -/
theorem isLowerSemicomputableIn_jumpSet_lowerFreq {f : ℕ → ℕ} (hf : Computable f) :
    PointToSet.IsLowerSemicomputableIn jumpSet (lowerFreq f) := by
  have hcnt := isLowerSemicomputableIn_jumpSet_lowerFreq_computable_countOcc hf
  -- the co-enumerable inner property, via its enumerable complement
  have hg : Computable₂ (fun (a : ℕ × ℚ × ℕ) (m : ℕ) =>
      decide (a.2.2 ≤ m) && decide ((countOcc f a.1 m : ℚ) < a.2.1 * (m : ℚ))) := by
    have h1 : Computable (fun q : (ℕ × ℚ × ℕ) × ℕ => decide (q.1.2.2 ≤ q.2)) :=
      (PrimrecPred.decide (Primrec.nat_le.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to_comp
    have hpair : Computable (fun q : (ℕ × ℚ × ℕ) × ℕ => ((q.1.1, q.2) : ℕ × ℕ)) :=
      Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
    have hco : Computable (fun q : (ℕ × ℚ × ℕ) × ℕ => countOcc f q.1.1 q.2) :=
      Computable.comp (f := fun p : ℕ × ℕ => countOcc f p.1 p.2)
        (g := fun q : (ℕ × ℚ × ℕ) × ℕ => ((q.1.1, q.2) : ℕ × ℕ)) hcnt hpair
    have hc : Computable (fun q : (ℕ × ℚ × ℕ) × ℕ => (countOcc f q.1.1 q.2 : ℚ)) :=
      computable_nat_to_rat.comp hco
    have hmq : Computable (fun q : (ℕ × ℚ × ℕ) × ℕ => ((q.2 : ℕ) : ℚ)) :=
      computable_nat_to_rat.comp Computable.snd
    have hmul : Computable (fun q : (ℕ × ℚ × ℕ) × ℕ => q.1.2.1 * ((q.2 : ℕ) : ℚ)) :=
      computable₂_ratMul.comp (Computable.fst.comp (Computable.snd.comp Computable.fst)) hmq
    have h2 : Computable (fun q : (ℕ × ℚ × ℕ) × ℕ =>
        decide ((countOcc f q.1.1 q.2 : ℚ) < q.1.2.1 * ((q.2 : ℕ) : ℚ))) :=
      computable₂_ratLt.comp hc hmul
    exact (Primrec.and.to_comp.comp h1 h2).to₂
  obtain ⟨h, hhJ, hhspec⟩ := exists_computableInJump_semidecide hg
  have hhO : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) h := hhJ
  -- the search over the codes of `(p, N)`
  let b : (ℕ × ℚ) × ℕ → Bool := fun w =>
    decide (w.1.2 < (Denumerable.ofNat ℚ (Nat.unpair w.2).1)) &&
      !h (w.1.1, Denumerable.ofNat ℚ (Nat.unpair w.2).1, (Nat.unpair w.2).2)
  have hb : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) b := by
    have hp : Computable (fun w : (ℕ × ℚ) × ℕ => Denumerable.ofNat ℚ (Nat.unpair w.2).1) :=
      (Primrec.ofNat ℚ).to_comp.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hN : Computable (fun w : (ℕ × ℚ) × ℕ => (Nat.unpair w.2).2) :=
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have h1 : Computable (fun w : (ℕ × ℚ) × ℕ =>
        decide (w.1.2 < (Denumerable.ofNat ℚ (Nat.unpair w.2).1))) :=
      computable₂_ratLt.comp (Computable.snd.comp Computable.fst) hp
    have h2 : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) (fun w : (ℕ × ℚ) × ℕ =>
        h (w.1.1, Denumerable.ofNat ℚ (Nat.unpair w.2).1, (Nat.unpair w.2).2)) :=
      hhO.comp (Computable.computableIn (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair hp hN)))
    have h3 : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) (fun w : (ℕ × ℚ) × ℕ =>
        !h (w.1.1, Denumerable.ofNat ℚ (Nat.unpair w.2).1, (Nat.unpair w.2).2)) :=
      ComputableIn.comp (f := fun x : Bool => !x) (Primrec.not.to_comp.computableIn) h2
    have h4 : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) (fun w : (ℕ × ℚ) × ℕ =>
        (decide (w.1.2 < (Denumerable.ofNat ℚ (Nat.unpair w.2).1)),
          !h (w.1.1, Denumerable.ofNat ℚ (Nat.unpair w.2).1, (Nat.unpair w.2).2))) :=
      ComputableIn.pair h1.computableIn h3
    have hand : Computable (fun x : Bool × Bool => x.1 && x.2) := Primrec.and.to_comp
    have hand' : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ))
        (fun x : Bool × Bool => x.1 && x.2) := hand.computableIn
    have h5 := ComputableIn.comp hand' h4
    exact h5
  have hRE : PointToSet.IsREIn jumpSet (fun w : (ℕ × ℚ) × ℕ => b w = true) :=
    PointToSet.isREIn_of_computableIn_decide jumpSet _ (hb.of_eq fun w => by simp)
  obtain ⟨F, hF, hFd⟩ := hRE.exists
  refine ⟨F, hF, fun w => ?_⟩
  refine Iff.trans ?_ (hFd w)
  obtain ⟨k, r⟩ := w
  change (r : ℝ) < lowerFreq f k ↔ ∃ y, b ((k, r), y) = true
  rw [isLowerSemicomputableIn_jumpSet_lowerFreq_iff]
  have hfalse : ∀ (p : ℚ) (N : ℕ), h (k, p, N) = false ↔
      ∀ m ≥ N, p * (m : ℚ) ≤ (countOcc f k m : ℚ) := by
    intro p N
    rw [← Bool.not_eq_true, hhspec]
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_exists, not_and, not_lt]
  constructor
  · rintro ⟨p, hrp, N, hN⟩
    have he : Denumerable.ofNat ℚ (Denumerable.eqv ℚ p) = p :=
      (Denumerable.eqv ℚ).symm_apply_apply p
    refine ⟨Nat.pair (Denumerable.eqv ℚ p) N, ?_⟩
    simp only [b, Nat.unpair_pair, he, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true', hfalse]
    exact ⟨by exact_mod_cast hrp, hN⟩
  · rintro ⟨i, hi⟩
    simp only [b, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', hfalse] at hi
    exact ⟨_, by exact_mod_cast hi.1, _, hi.2⟩

/-- The order relation `a ≤ b` on the rationals is a computable predicate. -/
lemma isLowerSemicomputableIn_jumpSet_liminf_ratLe :
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

/-- Step 1 of the proof of `isLowerSemicomputableIn_jumpSet_liminf`: the predicate
"some rational `p > s` is eventually below `rₙ`" is `0'`-enumerable (its inner part is
co-enumerable, hence `0'`-decidable). -/
private theorem isLowerSemicomputableIn_jumpSet_liminf_re {r : ℕ → ℚ}
    (hr : Computable r) :
    PointToSet.IsREIn jumpSet
      (fun w : Unit × ℚ => ∃ x : ℚ × ℕ, w.2 < x.1 ∧ ∀ n, x.2 ≤ n → x.1 ≤ r n) := by
  classical
  have hle := isLowerSemicomputableIn_jumpSet_liminf_ratLe
  let g : (Unit × ℚ) × (ℚ × ℕ) → ℕ → Bool :=
    fun t n => decide (t.2.2 ≤ n) && !decide (t.2.1 ≤ r n)
  have hg : Computable₂ g := by
    have h1 : Computable (fun p : ((Unit × ℚ) × (ℚ × ℕ)) × ℕ => decide (p.1.2.2 ≤ p.2)) :=
      (Primrec.to_comp (PrimrecPred.decide (Primrec.nat_le.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)))
    have h2 : Computable (fun p : ((Unit × ℚ) × (ℚ × ℕ)) × ℕ => decide (p.1.2.1 ≤ r p.2)) :=
      hle.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (hr.comp Computable.snd)
    exact (Primrec.and.to_comp.comp h1 (Primrec.not.to_comp.comp h2)).to₂
  obtain ⟨h, hh, hspec⟩ := Kolmogorov.exists_computableInJump_semidecide hg
  have hhalt : haltingChi = charOracle jumpSet := by
    funext n
    simp only [haltingChi, charOracle, jumpSet, haltingSet, Set.mem_ofPred_eq]
    congr
  have hh' : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) h := by
    simpa [ComputableInJump, hhalt] using hh
  have hF := PointToSet.IsREIn.exists (A := jumpSet) (α := Unit × ℚ) (β := ℚ × ℕ)
    (F := fun t : (Unit × ℚ) × (ℚ × ℕ) => t.1.2 < t.2.1 ∧ ∀ n, t.2.2 ≤ n → t.2.1 ≤ r n) (by
      refine PointToSet.isREIn_of_computableIn_decide _ _ ?_
      have h1 : Computable (fun t : (Unit × ℚ) × (ℚ × ℕ) => decide (t.2.1 ≤ t.1.2)) :=
        hle.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.fst)
      have h3 : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ))
          (fun t : (Unit × ℚ) × (ℚ × ℕ) => !decide (t.2.1 ≤ t.1.2) && !h t) :=
        (Primrec.and.to_comp.computableIn).comp
          (ComputableIn.pair (Primrec.not.to_comp.comp h1).computableIn
            ((Primrec.not.to_comp.computableIn).comp hh'))
      refine h3.of_eq fun t => ?_
      rw [Bool.eq_iff_iff]
      have hspect := hspec t
      simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not]
      apply Iff.symm
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨not_le.2 h1, ?_⟩
        by_contra hne
        obtain ⟨k, hk⟩ := hspect.1 (by simpa using hne)
        simp only [g, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not,
          not_le] at hk
        exact absurd (h2 k hk.1) (not_le.2 hk.2)
      · rintro ⟨h1, h2⟩
        refine ⟨not_le.1 h1, fun n hn => ?_⟩
        by_contra hlt
        have : h t = true := hspect.2 ⟨n, by simp [g, hn, hlt]⟩
        simp [this] at h2)
  exact hF

/-- **SUV Problem 210 (Section 6.4.3, printed p. 210).** The `liminf` of a computable sequence of
rationals is a `0'`-lower-semicomputable real.

No hypothesis is needed. The book tacitly assumes the `liminf` is finite. When it is infinite,
Mathlib's real `Filter.liminf` returns `0`, which is trivially `0'`-lower-semicomputable.
Deviation: the uniformity claim (the `0'`-algorithm is found effectively from an algorithm for
`rₙ`) is not formalized.

Proof idea: as for Theorem 135. `s < liminf rₙ` iff there are a rational `p > s` and an `N` with
`rₙ > p` for all `n > N`, and the inner property is co-enumerable. -/
theorem isLowerSemicomputableIn_jumpSet_liminf {r : ℕ → ℚ} (hr : Computable r) :
    PointToSet.IsLowerSemicomputableIn jumpSet
      (fun _ : Unit => Filter.liminf (fun n => (r n : ℝ)) Filter.atTop) := by
  classical
  set S : Set ℝ := {a | ∀ᶠ n in Filter.atTop, a ≤ (r n : ℝ)} with hS
  have hlim : Filter.liminf (fun n => (r n : ℝ)) Filter.atTop = sSup S := rfl
  by_cases hgood : S.Nonempty ∧ BddAbove S
  · obtain ⟨hne, hb⟩ := hgood
    have key : ∀ w : Unit × ℚ, ((w.2 : ℝ) < Filter.liminf (fun n => (r n : ℝ)) Filter.atTop) ↔
        ∃ x : ℚ × ℕ, w.2 < x.1 ∧ ∀ n, x.2 ≤ n → x.1 ≤ r n := by
      intro w
      rw [hlim]
      constructor
      · intro h
        obtain ⟨b, hbS, hwb⟩ := (lt_csSup_iff hb hne).1 h
        obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hwb
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hbS
        refine ⟨(p, N), by exact_mod_cast hp1, fun n hn => ?_⟩
        have := (hp2.trans_le (hN n hn)).le
        exact_mod_cast this
      · rintro ⟨⟨p, N⟩, h1, h2⟩
        have hpS : (p : ℝ) ∈ S :=
          Filter.eventually_atTop.2 ⟨N, fun n hn => by exact_mod_cast h2 n hn⟩
        exact lt_of_lt_of_le (by exact_mod_cast h1) (le_csSup hb hpS)
    obtain ⟨f, hf, hdom⟩ := isLowerSemicomputableIn_jumpSet_liminf_re hr
    exact ⟨f, hf, fun w => (key w).trans (hdom w)⟩
  · have h0 : Filter.liminf (fun n => (r n : ℝ)) Filter.atTop = 0 := by
      rw [hlim]
      by_cases hne : S.Nonempty
      · exact Real.sSup_of_not_bddAbove (fun hb => hgood ⟨hne, hb⟩)
      · rw [Set.not_nonempty_iff_eq_empty.1 hne]
        exact Real.sSup_empty
    have hdec : Computable (fun w : Unit × ℚ => !decide (0 ≤ w.2)) :=
      Primrec.not.to_comp.comp
        (isLowerSemicomputableIn_jumpSet_liminf_ratLe.comp (Computable.const 0)
          Computable.snd)
    have hre : PointToSet.IsREIn jumpSet (fun w : Unit × ℚ => w.2 < 0) :=
      PointToSet.isREIn_of_computable_decide (P := fun w : Unit × ℚ => w.2 < 0)
        (hdec.of_eq fun w => by
          by_cases h : (0 : ℚ) ≤ w.2
          · simp [h, not_lt.2 h]
          · simp [h, not_le.1 h])
    obtain ⟨f, hf, hdom⟩ := hre
    refine ⟨f, hf, fun w => ?_⟩
    change ((w.2 : ℝ) < Filter.liminf (fun n => (r n : ℝ)) Filter.atTop) ↔ _
    rw [h0]
    exact Iff.trans (by exact_mod_cast Iff.rfl) (hdom w)

section Step1Sigma2Aux

open Nat.Partrec (Code)

/-- Single check of the `Σ₂` matrix: the `i`-th entry `(c, t)` of the witness list `L` says
either `c = 0` ("`φ_i(i)` has not halted within `b` steps") or `c = 1` ("`φ_i(i)` halts within
`t` steps"). -/
private def exists_computable_liminf_eq_sigma2_test (L : List (ℕ × ℕ)) (b i : ℕ) :
    Bool :=
  bif decide ((L.getD i (0, 0)).1 = 0) then
    (Code.evaln b (Denumerable.ofNat Code i) i).isNone
  else bif decide ((L.getD i (0, 0)).1 = 1) then
    (Code.evaln (L.getD i (0, 0)).2 (Denumerable.ofNat Code i) i).isSome
  else false

/-- The `Σ₂` matrix for the operator with code `e`, on `((L, s), n, b)`. -/
private def exists_computable_liminf_eq_sigma2_chk (e : ℕ)
    (p : (List (ℕ × ℕ) × ℕ) × ℕ × ℕ) : Bool :=
  decide (∀ i ∈ List.range p.1.1.length,
      exists_computable_liminf_eq_sigma2_test p.1.1 p.2.2 i = true) &&
    (Code.evaln p.1.2 (Denumerable.ofNat Code e)
      (Encodable.encode (p.1.1.map Prod.fst, p.2.1))).isSome

private lemma exists_computable_liminf_eq_sigma2_test_primrec :
    Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ =>
      exists_computable_liminf_eq_sigma2_test q.1.1 q.1.2 q.2) := by
  have hL : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => q.1.1) := Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => q.1.2) := Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => q.2) := Primrec.snd
  have hg : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => q.1.1.getD q.2 (0, 0)) :=
    (Primrec.list_getD (0, 0)).comp hL hi
  have hc : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => (q.1.1.getD q.2 (0, 0)).1) :=
    Primrec.fst.comp hg
  have ht : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => (q.1.1.getD q.2 (0, 0)).2) :=
    Primrec.snd.comp hg
  have hcode : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => (Denumerable.ofNat Code q.2 : Code)) :=
    (Primrec.ofNat Code).comp hi
  have hev1 : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ =>
      Code.evaln q.1.2 (Denumerable.ofNat Code q.2) q.2) :=
    Code.primrec_evaln.comp ((hb.pair hcode).pair hi)
  have hev2 : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ =>
      Code.evaln (q.1.1.getD q.2 (0, 0)).2 (Denumerable.ofNat Code q.2) q.2) :=
    Code.primrec_evaln.comp ((ht.pair hcode).pair hi)
  have h0 : PrimrecPred (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => (q.1.1.getD q.2 (0, 0)).1 = 0) :=
    Primrec.eq.comp hc (Primrec.const 0)
  have h1 : PrimrecPred (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => (q.1.1.getD q.2 (0, 0)).1 = 1) :=
    Primrec.eq.comp hc (Primrec.const 1)
  have hnone : Primrec (fun q : (List (ℕ × ℕ) × ℕ) × ℕ =>
      (Code.evaln q.1.2 (Denumerable.ofNat Code q.2) q.2).isNone) :=
    (Primrec.not.comp (Primrec.option_isSome.comp hev1)).of_eq fun q => by
      cases Code.evaln q.1.2 (Denumerable.ofNat Code q.2) q.2 <;> rfl
  exact Primrec.cond h0.decide hnone
    (Primrec.cond h1.decide (Primrec.option_isSome.comp hev2) (Primrec.const false))

private lemma exists_computable_liminf_eq_sigma2_chk_primrec (e : ℕ) :
    Primrec (exists_computable_liminf_eq_sigma2_chk e) := by
  have hrel : PrimrecRel (fun (i : ℕ) (Lb : List (ℕ × ℕ) × ℕ) =>
      exists_computable_liminf_eq_sigma2_test Lb.1 Lb.2 i = true) :=
    Primrec.eq.comp
      (exists_computable_liminf_eq_sigma2_test_primrec.comp
        (Primrec.snd.pair Primrec.fst)) (Primrec.const true)
  have hall : PrimrecPred (fun p : (List (ℕ × ℕ) × ℕ) × ℕ × ℕ =>
      ∀ i ∈ List.range p.1.1.length,
        exists_computable_liminf_eq_sigma2_test p.1.1 p.2.2 i = true) :=
    hrel.forall_mem_list.comp
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))
  have hs : Primrec (fun p : (List (ℕ × ℕ) × ℕ) × ℕ × ℕ =>
      (Code.evaln p.1.2 (Denumerable.ofNat Code e)
        (Encodable.encode (p.1.1.map Prod.fst, p.2.1))).isSome) :=
    Primrec.option_isSome.comp
      (Code.primrec_evaln.comp
        (((Primrec.snd.comp Primrec.fst).pair (Primrec.const _)).pair
          (Primrec.encode.comp
            ((Primrec.list_map (Primrec.fst.comp Primrec.fst)
              (Primrec.fst.comp Primrec.snd).to₂).pair (Primrec.fst.comp Primrec.snd)))))
  exact Primrec.and.comp hall.decide hs

private lemma exists_computable_liminf_eq_sigma2_mem_of_isSome {i k : ℕ}
    (h : (Code.evaln k (Denumerable.ofNat Code i) i).isSome = true) : i ∈ jumpSet := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  exact Part.dom_iff_mem.mpr ⟨v, Code.evaln_sound (Option.mem_def.mpr hv)⟩

private lemma exists_computable_liminf_eq_sigma2_exists_isSome {i : ℕ}
    (hi : i ∈ jumpSet) :
    ∃ k, (Code.evaln k (Denumerable.ofNat Code i) i).isSome = true := by
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp (show ((Denumerable.ofNat Code i).eval i).Dom from hi)
  obtain ⟨k, hk⟩ := Code.evaln_complete.mp hv
  exact ⟨k, Option.isSome_iff_exists.mpr ⟨v, Option.mem_def.mp hk⟩⟩

private lemma exists_computable_liminf_eq_sigma2_none_of_not_mem {i : ℕ}
    (hi : i ∉ jumpSet) (k : ℕ) : Code.evaln k (Denumerable.ofNat Code i) i = none := by
  cases h : Code.evaln k (Denumerable.ofNat Code i) i with
  | none => rfl
  | some v =>
    exact absurd (exists_computable_liminf_eq_sigma2_mem_of_isSome (by rw [h]; rfl)) hi

private lemma exists_computable_liminf_eq_sigma2_chk_iff (e : ℕ) (L : List (ℕ × ℕ))
    (s n b : ℕ) :
    exists_computable_liminf_eq_sigma2_chk e ((L, s), n, b) = true ↔
      (∀ i < L.length, exists_computable_liminf_eq_sigma2_test L b i = true) ∧
        (Code.evaln s (Denumerable.ofNat Code e)
          (Encodable.encode (L.map Prod.fst, n))).isSome = true := by
  simp [exists_computable_liminf_eq_sigma2_chk]

private theorem exists_computable_liminf_eq_sigma2_exists_code_evaln
    {σ : Type*} [Primcodable σ] (Φ : σ →. ℕ) (hΦ : Partrec Φ) :
    ∃ e : ℕ, ∀ (x : σ) (v : ℕ), v ∈ Φ x ↔
      ∃ k, Code.evaln k (Denumerable.ofNat Code e) (Encodable.encode x) = some v := by
  let f : ℕ →. ℕ := fun x => (Part.ofOption (Encodable.decode (α := σ) x)).bind Φ
  have hf : Nat.Partrec f :=
    Partrec.nat_iff.mp
      (Partrec.bind (Computable.ofOption Computable.decode) (hΦ.comp Computable.snd))
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  refine ⟨Encodable.encode c, fun x v => ?_⟩
  have heval : c.eval (Encodable.encode x) = Φ x := by
    rw [hc]
    change (Part.ofOption (Encodable.decode (α := σ) (Encodable.encode x))).bind Φ = Φ x
    rw [Encodable.encodek]
    exact Part.bind_some _ Φ
  rw [Denumerable.ofNat_encode, ← heval]
  exact Code.evaln_complete

end Step1Sigma2Aux

/-- Step 1 of the proof of `exists_computable_liminf_eq`: a predicate that is
enumerable relative to `0'` has a `Σ₂` normal form with a computable matrix (the limit lemma:
a `0'`-computation is approximated by computable stages, so `P w` holds iff for some `a` the
bounded queries to `0'` stabilize on the correct answers, which is `∀ b, R w a b = true`).

Proof idea: `P w` iff the oracle machine halts on `w`; run it with the `0'` answers guessed
by the stage `b` approximation; "the guessed run halts and every guess it used is still
correct at all later stages" is `∃ a ∀ b` over a computable matrix. -/
theorem exists_computable_liminf_eq_sigma2 {α : Type} [Primcodable α]
    {P : α → Prop} (hP : PointToSet.IsREIn jumpSet P) :
    ∃ R : α → ℕ → ℕ → Bool, Computable (fun p : α × ℕ × ℕ => R p.1 p.2.1 p.2.2) ∧
      ∀ w, P w ↔ ∃ a, ∀ b, R w a b = true := by
  classical
  obtain ⟨f, hf, hPdom⟩ := hP
  let f' : ℕ →. ℕ := fun n => (Part.ofOption (Encodable.decode (α := α) n)).bind f
  have hf' : PartrecIn {charOracle jumpSet} f' :=
    PartrecIn.bind (Partrec.partrecIn (Computable.ofOption Computable.decode))
      (PartrecIn.comp hf ComputableIn.snd)
  obtain ⟨Φ, hΦ, -, hex⟩ :=
    PointToSet.exists_exact_string_operator (fun j : ℕ => if j ∈ jumpSet then 1 else 0) f' hf'
  obtain ⟨e, hcode⟩ := exists_computable_liminf_eq_sigma2_exists_code_evaln Φ hΦ
  have hf'enc : ∀ w : α, f' (Encodable.encode w) = f w := fun w => by
    change (Part.ofOption (Encodable.decode (α := α) (Encodable.encode w))).bind f = f w
    rw [Encodable.encodek]
    exact Part.bind_some _ f
  refine ⟨fun w a b => exists_computable_liminf_eq_sigma2_chk e
    (Denumerable.ofNat (List (ℕ × ℕ) × ℕ) a, Encodable.encode w, b), ?_, fun w => ?_⟩
  · have h := (exists_computable_liminf_eq_sigma2_chk_primrec e).to_comp.comp
      (((Primrec.ofNat (List (ℕ × ℕ) × ℕ)).to_comp.comp
        (Computable.fst.comp Computable.snd)).pair
        (((Computable.encode (α := α)).comp Computable.fst).pair
          (Computable.snd.comp Computable.snd)))
    exact h
  · constructor
    · intro hw
      have hd : (f' (Encodable.encode w)).Dom := by rw [hf'enc]; exact (hPdom w).mp hw
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hd
      obtain ⟨u, hu⟩ := (hex _ v).mp hv
      obtain ⟨s, hs⟩ := (hcode _ v).mp hu
      let T : ℕ → ℕ := fun i =>
        if h : ∃ k, (Nat.Partrec.Code.evaln k (Denumerable.ofNat Nat.Partrec.Code i) i).isSome
            = true then Nat.find h
        else 0
      let L : List (ℕ × ℕ) := (List.range u).map fun i => ((if i ∈ jumpSet then 1 else 0), T i)
      refine ⟨Encodable.encode (L, s), fun b => ?_⟩
      change exists_computable_liminf_eq_sigma2_chk e
        (Denumerable.ofNat (List (ℕ × ℕ) × ℕ) (Encodable.encode (L, s)),
          Encodable.encode w, b) = true
      rw [Denumerable.ofNat_encode, exists_computable_liminf_eq_sigma2_chk_iff]
      refine ⟨fun i hi => ?_, ?_⟩
      · have hiu : i < u := by simpa [L] using hi
        have hget : L.getD i (0, 0) = ((if i ∈ jumpSet then 1 else 0), T i) := by
          simp [L, hiu]
        unfold exists_computable_liminf_eq_sigma2_test
        rw [hget]
        by_cases hA : i ∈ jumpSet
        · have hex' := exists_computable_liminf_eq_sigma2_exists_isSome hA
          have hT : (Nat.Partrec.Code.evaln (T i) (Denumerable.ofNat Nat.Partrec.Code i)
              i).isSome = true := by
            simp only [T, dite_eq_left hex']
            exact Nat.find_spec hex'
          simp [hA, hT]
        · simp [hA, exists_computable_liminf_eq_sigma2_none_of_not_mem hA b]
      · have : L.map Prod.fst = (List.range u).map fun i => if i ∈ jumpSet then 1 else 0 := by
          simp [L, List.map_map, Function.comp_def]
        rw [this, hs]
        rfl
    · rintro ⟨a, ha⟩
      have ha' : ∀ b, exists_computable_liminf_eq_sigma2_chk e
          (Denumerable.ofNat (List (ℕ × ℕ) × ℕ) a, Encodable.encode w, b) = true := ha
      generalize Denumerable.ofNat (List (ℕ × ℕ) × ℕ) a = Ls at ha'
      obtain ⟨L, s⟩ := Ls
      have hsplit : ∀ b, (∀ i < L.length,
            exists_computable_liminf_eq_sigma2_test L b i = true) ∧
          (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
            (Encodable.encode (L.map Prod.fst, Encodable.encode w))).isSome = true :=
        fun b => (exists_computable_liminf_eq_sigma2_chk_iff e L s _ b).mp (ha' b)
      have key : ∀ i (hi : i < L.length),
          (L[i]).1 = if i ∈ jumpSet then 1 else 0 := by
        intro i hi
        have ht : ∀ b, exists_computable_liminf_eq_sigma2_test L b i = true :=
          fun b => (hsplit b).1 i hi
        have hg : L.getD i (0, 0) = L[i] := by simp [hi]
        simp only [exists_computable_liminf_eq_sigma2_test, hg] at ht
        generalize L[i] = ct at ht ⊢
        obtain ⟨c, t⟩ := ct
        by_cases hA : i ∈ jumpSet
        · simp only [hA, ite_true]
          by_contra hc1
          by_cases hc0 : c = 0
          · obtain ⟨k, hk⟩ := exists_computable_liminf_eq_sigma2_exists_isSome hA
            have h2 := ht k
            simp [hc0] at h2
            simp [h2] at hk
          · have h2 := ht 0
            simp [hc0, hc1] at h2
        · simp only [hA, ite_false]
          by_contra hc0
          by_cases hc1 : c = 1
          · have h2 := ht 0
            exact hA (exists_computable_liminf_eq_sigma2_mem_of_isSome (by simpa [hc1] using h2))
          · have h2 := ht 0
            simp [hc0, hc1] at h2
      have hσ : L.map Prod.fst =
          (List.range L.length).map (fun j : ℕ => if j ∈ jumpSet then 1 else 0) := by
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        exact key i (by simpa using h1)
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hsplit 0).2
      rw [hσ] at hv
      have hu : v ∈ Φ ((List.range L.length).map (fun j : ℕ => if j ∈ jumpSet then 1 else 0),
          Encodable.encode w) := (hcode _ v).mpr ⟨s, hv⟩
      have hv' := (hex _ v).mpr ⟨_, hu⟩
      rw [hf'enc] at hv'
      exact (hPdom w).mpr (Part.dom_iff_mem.mpr ⟨v, hv'⟩)

end GeneralScheme
end Kolmogorov
