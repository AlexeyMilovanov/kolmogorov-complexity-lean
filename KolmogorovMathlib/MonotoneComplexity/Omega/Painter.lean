/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.LscBasic
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic

/-!
# The painters of SUV Section 5.7.3 (p. 163)

The proof of SUV Theorem 108 pictures the covering intervals as *painters*: portion `n`
of paint, of amount `g n`, is applied starting at the position `p n`, or at the right end
of the already painted region if that is further to the right.  This module isolates that
process, because it is what SUV Theorems 108 and 109 (reverse direction) both need.

Writing `E n` for the right end of the painted region after portion `n` and `b n` for the
place where portion `n` starts,

* `b 0 = p 0`, `E 0 = p 0 + g 0`;
* `b (n+1) = max (p (n+1)) (E n)`, `E (n+1) = b (n+1) + g (n+1)`.

Two facts make the process useful.

* The emitted intervals `[b n, E n]` have length exactly `g n` **by construction**, so no
  measure theory is needed to bound the total length of the cover: it is `∑ g n`.
* `add_sum_le_max_paintEnd`: for **any** "accounting" function `g' ≤ g` supported on
  indices whose start `p n` is at least `c`, one has `c + ∑_{n ≤ N} g' n ≤ max (E N) c`.
  The accounting function need not be computable — it appears only in the proof — which is
  what lets the *cover* consist of all portions while the *estimate* uses only the tail
  of the series that the source's hypothesis speaks about.

Everything here is new infrastructure: no statement of the source is rendered in this
file.
-/

namespace Kolmogorov

open ENNReal

/-! ### The painting recursion -/

/-- `paintEnd p g n`: the right end of the painted region after portion `n` has been
used.  Portion `n` starts at `p n`, or at the right end of the region painted so far if
that is further to the right, and covers `g n` more. -/
def paintEnd (p g : ℕ → ℚ) : ℕ → ℚ
  | 0 => p 0 + g 0
  | n + 1 => max (p (n + 1)) (paintEnd p g n) + g (n + 1)

/-- The left end of the interval painted by portion `n`.  Defined as `paintEnd - g` so
that its computability is free; the two defining equations are
`paintStart_zero` and `paintStart_succ`. -/
def paintStart (p g : ℕ → ℚ) (n : ℕ) : ℚ := paintEnd p g n - g n

/-- The painted region after the first portion ends at `p 0 + g 0`. -/
@[simp] theorem paintEnd_zero (p g : ℕ → ℚ) : paintEnd p g 0 = p 0 + g 0 := rfl

/-- Each portion is painted starting at the later of its own request and the current right end. -/
@[simp] theorem paintEnd_succ (p g : ℕ → ℚ) (n : ℕ) :
    paintEnd p g (n + 1) = max (p (n + 1)) (paintEnd p g n) + g (n + 1) := rfl

/-- The first portion starts at its own request. -/
@[simp] theorem paintStart_zero (p g : ℕ → ℚ) : paintStart p g 0 = p 0 := by
  rw [paintStart, paintEnd_zero]; ring

/-- A later portion starts at the later of its own request and the previous right end. -/
@[simp] theorem paintStart_succ (p g : ℕ → ℚ) (n : ℕ) :
    paintStart p g (n + 1) = max (p (n + 1)) (paintEnd p g n) := by
  rw [paintStart, paintEnd_succ]; ring

/-- Each portion paints an interval of exactly its own length. -/
theorem paintEnd_eq_paintStart_add (p g : ℕ → ℚ) (n : ℕ) :
    paintEnd p g n = paintStart p g n + g n := by rw [paintStart]; ring

/-- With nonnegative portions the painted region only grows. -/
theorem paintEnd_mono {p g : ℕ → ℚ} (hg : ∀ n, 0 ≤ g n) : Monotone (paintEnd p g) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [paintEnd_succ]
  have h1 : paintEnd p g n ≤ max (p (n + 1)) (paintEnd p g n) := le_max_right _ _
  have h2 := hg (n + 1)
  linarith

/-! ### The accounting inequality -/

/-- The key property of the process.  `g` is the *actual* amount of paint used by each
portion; `g'` is any "accounting" function bounded by it and supported on portions that
start at or after `c`.  Then after `N` portions the painted region reaches at least
`c + ∑_{n ≤ N} g' n` — unless it never got as far as `c` at all, which the `max` absorbs.

`g'` is not required to be computable: in the applications it is the restriction of the
paint to the tail of the series, and the tail index is not computable from the budget. -/
theorem add_sum_le_max_paintEnd {p g g' : ℕ → ℚ} (hg : ∀ n, 0 ≤ g n)
    (hg' : ∀ n, 0 ≤ g' n) (hle : ∀ n, g' n ≤ g n) {c : ℚ}
    (hc : ∀ n, 0 < g' n → c ≤ p n) (N : ℕ) :
    c + ∑ n ∈ Finset.range (N + 1), g' n ≤ max (paintEnd p g N) c := by
  induction N with
  | zero =>
      rw [Finset.sum_range_one]
      rcases eq_or_lt_of_le (hg' 0) with h0 | h0
      · rw [← h0, add_zero]
        exact le_max_right _ _
      · have hcp : c ≤ p 0 := hc 0 h0
        have h1 : c + g' 0 ≤ p 0 + g 0 := add_le_add hcp (hle 0)
        rw [← paintEnd_zero p g] at h1
        exact le_trans h1 (le_max_left _ _)
  | succ N ih =>
      rw [Finset.sum_range_succ, ← add_assoc]
      rcases eq_or_lt_of_le (hg' (N + 1)) with h0 | h0
      · rw [← h0, add_zero]
        refine le_trans ih (max_le_max ?_ le_rfl)
        exact paintEnd_mono hg (Nat.le_succ N)
      · have hcp : c ≤ p (N + 1) := hc _ h0
        have h1 : max (paintEnd p g N) c ≤ paintStart p g (N + 1) := by
          rw [paintStart_succ]
          exact max_le (le_max_right _ _) (le_trans hcp (le_max_left _ _))
        have h2 : c + ∑ n ∈ Finset.range (N + 1), g' n + g' (N + 1)
            ≤ paintStart p g (N + 1) + g (N + 1) :=
          add_le_add (le_trans ih h1) (hle _)
        rw [← paintEnd_eq_paintStart_add] at h2
        exact le_trans h2 (le_max_left _ _)

/-! ### From the accounting inequality to a covering interval -/

/-- If the painted region ever passes `α`, then `α` lies in one of the emitted intervals,
padded on the left by an arbitrary positive amount.  The padding is what turns the closed
intervals `[b n, E n]` of the picture into the open intervals `ratInterval` uses. -/
theorem exists_mem_ratInterval_paint_of_lt {p g d : ℕ → ℚ} {α : ℝ}
    (hd : ∀ n, 0 < d n) (hp : ∀ n, ((p n : ℚ) : ℝ) ≤ α)
    (hex : ∃ N, α < ((paintEnd p g N : ℚ) : ℝ)) :
    ∃ n, α ∈ ratInterval (paintStart p g n - d n, paintEnd p g n) := by
  classical
  obtain ⟨n, hn, hmin⟩ : ∃ n, α < ((paintEnd p g n : ℚ) : ℝ) ∧
      ∀ k, k < n → ¬ (α < ((paintEnd p g k : ℚ) : ℝ)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  refine ⟨n, ?_⟩
  have hstart : ((paintStart p g n : ℚ) : ℝ) ≤ α := by
    cases n with
    | zero => rw [paintStart_zero]; exact hp 0
    | succ k =>
        have hk := hmin k (Nat.lt_succ_self k)
        push Not at hk
        rw [paintStart_succ]
        push_cast
        exact max_le (hp _) hk
  have hdn : (0 : ℝ) < ((d n : ℚ) : ℝ) := by exact_mod_cast hd n
  refine Set.mem_Ioo.mpr ⟨?_, hn⟩
  have hcast : ((paintStart p g n - d n : ℚ) : ℝ)
      = ((paintStart p g n : ℚ) : ℝ) - ((d n : ℚ) : ℝ) := by push_cast; ring
  change ((paintStart p g n - d n : ℚ) : ℝ) < α
  rw [hcast]
  linarith

/-- A finite lower bound extracted from an infinite one. -/
theorem exists_range_sum_gt {g : ℕ → ℚ} (hg : ∀ n, 0 ≤ g n) {t δ : ℝ} (hδ : 0 < δ)
    (h : ENNReal.ofReal t ≤ ∑' n, ENNReal.ofReal ((g n : ℚ) : ℝ)) :
    ∃ N, t - δ < ∑ n ∈ Finset.range N, ((g n : ℚ) : ℝ) := by
  rcases lt_or_ge (t - δ) 0 with hlt | hge
  · exact ⟨0, by simpa using hlt⟩
  · have h1 : ENNReal.ofReal (t - δ) < ENNReal.ofReal t :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hge).2 (by linarith)
    have h2 : ENNReal.ofReal (t - δ) < ∑' n, ENNReal.ofReal ((g n : ℚ) : ℝ) :=
      lt_of_lt_of_le h1 h
    rw [ENNReal.tsum_eq_iSup_nat] at h2
    obtain ⟨N, hN⟩ := lt_iSup_iff.1 h2
    refine ⟨N, ?_⟩
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by exact_mod_cast hg n)] at hN
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hge).1 hN

/-- **The painter cover.**  The painter is run with the amounts `b n + d n`, where `b` is
the paint the construction wants to spend and `d` is a positive padding; the interval it
emits for portion `n` is `(b n + d n)`-long, extended by `d n` to the left.  If some
"accounting" restriction `g ≤ b` of the paint, supported on portions starting at or after
`c`, already reaches from `c` up to `α`, then `α` is inside one of these intervals. -/
theorem exists_mem_ratInterval_paint {p b g d : ℕ → ℚ} {α : ℝ} {c : ℚ} {n₀ : ℕ}
    (hb : ∀ n, 0 ≤ b n) (hd : ∀ n, 0 < d n) (hg : ∀ n, 0 ≤ g n) (hgb : ∀ n, g n ≤ b n)
    (hp : ∀ n, ((p n : ℚ) : ℝ) ≤ α) (hcα : ((c : ℚ) : ℝ) ≤ α)
    (hc : ∀ n, 0 < g n → c ≤ p n) (hc₀ : c ≤ p n₀)
    (hsum : ENNReal.ofReal (α - ((c : ℚ) : ℝ)) ≤ ∑' n, ENNReal.ofReal ((g n : ℚ) : ℝ)) :
    ∃ n, α ∈ ratInterval (paintStart p (fun k => b k + d k) n - d n,
      paintEnd p (fun k => b k + d k) n) := by
  classical
  set G : ℕ → ℚ := fun k => b k + d k with hG
  set g' : ℕ → ℚ := fun k => g k + (if k = n₀ then d n₀ else 0) with hg'def
  have hGval : ∀ n, G n = b n + d n := fun _ => rfl
  have hg'val : ∀ n, g' n = g n + (if n = n₀ then d n₀ else 0) := fun _ => rfl
  have hGnn : ∀ n, 0 ≤ G n := by
    intro n
    rw [hGval n]
    linarith [hb n, (hd n).le]
  have hg'nn : ∀ n, 0 ≤ g' n := by
    intro n
    rw [hg'val n]
    by_cases hn : n = n₀
    · rw [if_pos hn]; linarith [hg n, (hd n₀).le]
    · rw [if_neg hn]; linarith [hg n]
  have hg'le : ∀ n, g' n ≤ G n := by
    intro n
    rw [hg'val n, hGval n]
    by_cases hn : n = n₀
    · rw [if_pos hn, hn]; linarith [hgb n₀]
    · rw [if_neg hn]; linarith [hgb n, (hd n).le]
  have hc' : ∀ n, 0 < g' n → c ≤ p n := by
    intro n hn
    by_cases hnn : n = n₀
    · rw [hnn]; exact hc₀
    · rw [hg'val n, if_neg hnn, add_zero] at hn
      exact hc n hn
  -- a finite stage at which the accounting sum already exceeds `α - c`
  have hδ : (0 : ℝ) < ((d n₀ : ℚ) : ℝ) := by exact_mod_cast hd n₀
  obtain ⟨N₁, hN₁⟩ := exists_range_sum_gt hg hδ hsum
  obtain ⟨N, hNa, hNb⟩ : ∃ N, N₁ ≤ N + 1 ∧ n₀ ≤ N :=
    ⟨max N₁ n₀, le_trans (le_max_left _ _) (Nat.le_succ _), le_max_right _ _⟩
  refine exists_mem_ratInterval_paint_of_lt hd hp ⟨N, ?_⟩
  have hkey := add_sum_le_max_paintEnd (p := p) (g := G) (g' := g') hGnn hg'nn hg'le hc' N
  have hmem : n₀ ∈ Finset.range (N + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hNb)
  have hsplit : ∑ n ∈ Finset.range (N + 1), g' n
      = (∑ n ∈ Finset.range (N + 1), g n) + d n₀ := by
    simp only [hg'def]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (N + 1)) n₀ (fun _ => d n₀),
      if_pos hmem]
  have hsub : ∑ n ∈ Finset.range N₁, ((g n : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.range (N + 1), ((g n : ℚ) : ℝ) := by
    have hsubset : Finset.range N₁ ⊆ Finset.range (N + 1) := fun x hx =>
      Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hNa)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => by exact_mod_cast hg n)
  have hlt : α < ((c : ℚ) : ℝ) + ∑ n ∈ Finset.range (N + 1), ((g' n : ℚ) : ℝ) := by
    have hcast : ∑ n ∈ Finset.range (N + 1), ((g' n : ℚ) : ℝ)
        = (∑ n ∈ Finset.range (N + 1), ((g n : ℚ) : ℝ)) + ((d n₀ : ℚ) : ℝ) := by
      have h := congrArg (fun q : ℚ => ((q : ℚ) : ℝ)) hsplit
      push_cast at h ⊢
      exact h
    rw [hcast]
    linarith
  have hcast2 : ((c : ℚ) : ℝ) + ∑ n ∈ Finset.range (N + 1), ((g' n : ℚ) : ℝ)
      ≤ max ((paintEnd p G N : ℚ) : ℝ) ((c : ℚ) : ℝ) := by exact_mod_cast hkey
  have hαmax : α < max ((paintEnd p G N : ℚ) : ℝ) ((c : ℚ) : ℝ) := lt_of_lt_of_le hlt hcast2
  rcases max_cases ((paintEnd p G N : ℚ) : ℝ) ((c : ℚ) : ℝ) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at hαmax; exact hαmax
  · rw [he] at hαmax; exact absurd hcα (not_le.2 hαmax)

/-! ### The length of the emitted intervals -/

/-- Each emitted interval has length exactly `b n + 2 · d n`: no measure theory. -/
theorem ratIntervalLength_paint (p b d : ℕ → ℚ) {n : ℕ} (hb : 0 ≤ b n) (hd : 0 ≤ d n) :
    ratIntervalLength (paintStart p (fun k => b k + d k) n - d n,
        paintEnd p (fun k => b k + d k) n)
      = ENNReal.ofReal ((b n : ℚ) : ℝ)
        + (ENNReal.ofReal ((d n : ℚ) : ℝ) + ENNReal.ofReal ((d n : ℚ) : ℝ)) := by
  have hval : ((paintEnd p (fun k => b k + d k) n : ℚ) : ℝ)
      - ((paintStart p (fun k => b k + d k) n - d n : ℚ) : ℝ)
      = ((b n : ℚ) : ℝ) + (((d n : ℚ) : ℝ) + ((d n : ℚ) : ℝ)) := by
    rw [paintEnd_eq_paintStart_add]
    push_cast
    ring
  rw [ratIntervalLength]
  change ENNReal.ofReal (((paintEnd p (fun k => b k + d k) n : ℚ) : ℝ)
      - ((paintStart p (fun k => b k + d k) n - d n : ℚ) : ℝ)) = _
  rw [hval, ENNReal.ofReal_add (by exact_mod_cast hb) (by positivity),
    ENNReal.ofReal_add (by exact_mod_cast hd) (by exact_mod_cast hd)]

/-! ### Turning a computable family of intervals into an effectively null set -/

/-- If for every rational budget `ε > 0` one can compute a family of rational intervals of
total length at most `ε` one of which contains `α`, then `α` is not ML-random. -/
theorem not_isMartinLofRandomReal_of_ratIntervals {α : ℝ} {C : ℚ → ℕ → ℚ × ℚ}
    (hC : Computable₂ C)
    (hlen : ∀ ε : ℚ, 0 < ε → (∑' n, ratIntervalLength (C ε n)) ≤ ENNReal.ofReal ((ε : ℚ) : ℝ))
    (hmem : ∀ ε : ℚ, 0 < ε → ∃ n, α ∈ ratInterval (C ε n)) :
    ¬ IsMartinLofRandomReal α := by
  intro hrand
  refine hrand {α} ⟨fun ε n => some (C ε n), Computable.option_some.comp hC, ?_⟩ rfl
  intro ε hε
  refine ⟨?_, ?_⟩
  · rintro y rfl
    obtain ⟨n, hn⟩ := hmem ε hε
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  · exact hlen ε hε

/-! ### Computability of the recursion -/

/-- The painting recursion in the shape `Computable.nat_rec` accepts, with a parameter. -/
def paintEndP {σ : Type} (p g : σ → ℕ → ℚ) (x : σ) : ℕ → ℚ
  | 0 => p x 0 + g x 0
  | n + 1 => max (p x (n + 1)) (paintEndP p g x n) + g x (n + 1)

/-- The parameterised painting recursion agrees with the plain one at each parameter. -/
theorem paintEndP_eq {σ : Type} (p g : σ → ℕ → ℚ) (x : σ) (n : ℕ) :
    paintEndP p g x n = paintEnd (p x) (g x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [paintEndP, paintEnd_succ, ih]

/-- The right end of the painted region is computable in the parameter and the portion index. -/
theorem computable_paintEndP {σ : Type} [Primcodable σ] {p g : σ → ℕ → ℚ}
    (hp : Computable₂ p) (hg : Computable₂ g) :
    Computable (fun q : σ × ℕ => paintEndP p g q.1 q.2) := by
  have hbase : Computable (fun q : σ × ℕ => p q.1 0 + g q.1 0) :=
    Computable₂.comp computable₂_ratAdd (hp.comp Computable.fst (Computable.const 0))
      (hg.comp Computable.fst (Computable.const 0))
  have hidx : Computable (fun s : (σ × ℕ) × ℕ × ℚ => s.2.1 + 1) :=
    Computable.succ.comp (Computable.fst.comp Computable.snd)
  have hpar : Computable (fun s : (σ × ℕ) × ℕ × ℚ => s.1.1) :=
    Computable.fst.comp Computable.fst
  have hstep : Computable₂ (fun (q : σ × ℕ) (r : ℕ × ℚ) =>
      max (p q.1 (r.1 + 1)) r.2 + g q.1 (r.1 + 1)) := by
    have h1 : Computable (fun s : (σ × ℕ) × ℕ × ℚ => p s.1.1 (s.2.1 + 1)) :=
      hp.comp hpar hidx
    have h2 : Computable (fun s : (σ × ℕ) × ℕ × ℚ => g s.1.1 (s.2.1 + 1)) :=
      hg.comp hpar hidx
    have h3 : Computable (fun s : (σ × ℕ) × ℕ × ℚ => s.2.2) :=
      Computable.snd.comp Computable.snd
    exact Computable₂.comp computable₂_ratAdd (Computable₂.comp computable₂_ratMax h1 h3) h2
  have hrec := Computable.nat_rec (σ := ℚ) Computable.snd hbase hstep
  refine hrec.of_eq (fun q => ?_)
  obtain ⟨x, n⟩ := q
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) (p x 0 + g x 0)
      (fun y IH => max (p x (y + 1)) IH + g x (y + 1)) m) = paintEndP p g x m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [paintEndP]; rw [ih]
  exact key n

/-- The left end of the painted portion is computable in the parameter and the portion index. -/
theorem computable_paintStartP {σ : Type} [Primcodable σ] {p g : σ → ℕ → ℚ}
    (hp : Computable₂ p) (hg : Computable₂ g) :
    Computable (fun q : σ × ℕ => paintStart (p q.1) (g q.1) q.2) := by
  have h1 : Computable (fun q : σ × ℕ => paintEndP p g q.1 q.2) :=
    computable_paintEndP hp hg
  have h2 : Computable (fun q : σ × ℕ => paintEnd (p q.1) (g q.1) q.2) :=
    h1.of_eq (fun q => paintEndP_eq p g q.1 q.2)
  have h3 : Computable (fun q : σ × ℕ => g q.1 q.2) := hg.comp Computable.fst Computable.snd
  exact (Computable₂.comp computable₂_ratSub h2 h3).of_eq (fun q => rfl)

end Kolmogorov
