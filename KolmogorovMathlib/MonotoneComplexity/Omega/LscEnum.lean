/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic

/-!
# An enumeration of the lower semicomputable reals of `[0,1]` (SUV p. 160)

This module builds the object behind the proof of SUV Theorem 102 ("We can enumerate all
lower semicomputable reals `αᵢ` in `[0,1]` and then take their sum `α = ∑ wᵢ αᵢ` with
computable positive weights"):

* `lscReal e` — the real of `[0,1]` enumerated by the code `e`: dovetail
  `Nat.Partrec.Code.evaln` over (input, step count), clip every value produced to
  `[0,1]`, and take the running maximum.  This is a computable non-decreasing rational
  sequence, so its limit is a lower semicomputable real of `[0,1]`, and *every* lower
  semicomputable real of `[0,1]` occurs (`exists_lscReal_eq`).
* `bigBeta = ∑ₘ w_{e(m)} · (increments of the e(m)-th approximation)`, the weighted sum
  written as one computable series of nonnegative rationals indexed by `ℕ` through
  `Nat.unpair`, with `w e = 2^{-(e+1)}`.
* `colU e`, the same series with all columns but the `e`-th deleted: it sums to
  `lscReal e` and is term-by-term below `2^{e+1} · bigBeta`, which is exactly what the
  proved criterion `solovayDominates_of_series_le` consumes.

Everything here is proved; the module renders no statement of the source.
-/

namespace Kolmogorov


open ComputableReals
open ENNReal

/-! ### A parameterised running maximum -/

/-- The running maximum with the sequence index as a recursion parameter. -/
def ratRunMaxP (f : ℕ → ℕ → ℚ) (e : ℕ) : ℕ → ℚ
  | 0 => f e 0
  | n + 1 => max (ratRunMaxP f e n) (f e (n + 1))

/-- The parameterised running maximum at index `e` is the running maximum of the `e`-th section. -/
theorem ratRunMaxP_eq (f : ℕ → ℕ → ℚ) (e n : ℕ) : ratRunMaxP f e n = ratRunMax (f e) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ratRunMaxP, ratRunMax_succ, ih]

/-- The parameterised running maximum of a computable family is computable in the index and the
step. -/
theorem computable_ratRunMaxP {f : ℕ → ℕ → ℚ} (hf : Computable₂ f) :
    Computable (fun z : ℕ × ℕ => ratRunMaxP f z.1 z.2) := by
  have hstep : Computable₂ (fun (z : ℕ × ℕ) (r : ℕ × ℚ) => max r.2 (f z.1 (r.1 + 1))) := by
    have h1 : Computable (fun q : (ℕ × ℕ) × ℕ × ℚ => q.2.2) :=
      Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : (ℕ × ℕ) × ℕ × ℚ => f q.1.1 (q.2.1 + 1)) :=
      hf.comp (Computable.fst.comp Computable.fst)
        (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
    exact Computable₂.comp computable₂_ratMax h1 h2
  have hbase : Computable (fun z : ℕ × ℕ => f z.1 0) :=
    hf.comp Computable.fst (Computable.const 0)
  have hrec := Computable.nat_rec (σ := ℚ) Computable.snd hbase hstep
  refine hrec.of_eq (fun z => ?_)
  obtain ⟨e, n⟩ := z
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) (f e 0)
      (fun y IH => max IH (f e (y + 1))) m) = ratRunMaxP f e m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simp only [ratRunMaxP]
        exact congrArg (fun x : ℚ => max x (f e (m + 1))) ih
  exact key n

/-! ### The enumeration -/

/-- The raw value produced by the code `e` on the input `(Nat.unpair m).1` within
`(Nat.unpair m).2` steps, read as `0` when it has not converged. -/
def lscRaw (e m : ℕ) : ℚ :=
  ((Nat.Partrec.Code.evaln (Nat.unpair m).2 (Denumerable.ofNat Nat.Partrec.Code e)
      (@Encodable.encode ℕ Primcodable.toEncodable (Nat.unpair m).1)).bind
    (fun v => @Encodable.decode ℚ Primcodable.toEncodable v)).getD 0

/-- The raw dovetailed value of the code `e` at step `m` is computable in both arguments. -/
theorem computable₂_lscRaw : Computable₂ lscRaw := by
  have hcode : Computable (fun z : ℕ × ℕ => Denumerable.ofNat Nat.Partrec.Code z.1) :=
    (Primrec.ofNat Nat.Partrec.Code).to_comp.comp Computable.fst
  have hinp : Computable (fun z : ℕ × ℕ =>
      @Encodable.encode ℕ Primcodable.toEncodable (Nat.unpair z.2).1) :=
    Primrec.encode.to_comp.comp
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hsteps : Computable (fun z : ℕ × ℕ => (Nat.unpair z.2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hev := Nat.Partrec.Code.primrec_evaln.to_comp.comp
    (Computable.pair (Computable.pair hsteps hcode) hinp)
  have hdec : Computable₂ (fun (_ : ℕ × ℕ) (v : ℕ) =>
      @Encodable.decode ℚ Primcodable.toEncodable v) := Computable.decode.comp Computable.snd
  have hbind := Computable.option_bind hev hdec
  have h := Computable.option_getD hbind
    (Computable.const (0 : ℚ) : Computable (fun _ : ℕ × ℕ => (0 : ℚ)))
  exact h

attribute [irreducible] lscRaw

/-- Clipping a rational to `[0,1]`. -/
def clip01 (q : ℚ) : ℚ := min 1 (max 0 q)

/-- Clipping to `[0,1]` gives a nonnegative rational. -/
theorem clip01_nonneg (q : ℚ) : 0 ≤ clip01 q := by
  rw [clip01, le_min_iff]
  exact ⟨by norm_num, le_max_left _ _⟩

/-- Clipping to `[0,1]` gives a rational at most one. -/
theorem clip01_le_one (q : ℚ) : clip01 q ≤ 1 := min_le_left _ _

/-- Clipping fixes the rationals already in `[0,1]`. -/
theorem clip01_eq_self {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : clip01 q = q := by
  rw [clip01, max_eq_right h0, min_eq_right h1]

/-- Clipping fixes zero. -/
@[simp] theorem clip01_zero : clip01 0 = 0 := by norm_num [clip01]

/-- Clipping to `[0,1]` is computable. -/
theorem computable_clip01 : Computable clip01 := by
  have h1 := Computable₂.comp computable₂_ratMax
    (Computable.const (0 : ℚ) : Computable (fun _ : ℚ => (0 : ℚ))) Computable.id
  have h := Computable₂.comp computable₂_ratMin
    (Computable.const (1 : ℚ) : Computable (fun _ : ℚ => (1 : ℚ))) h1
  exact h

/-- The real cast of a clipped rational is the clip of its cast. -/
theorem cast_clip01 (q : ℚ) : ((clip01 q : ℚ) : ℝ) = min 1 (max 0 ((q : ℚ) : ℝ)) := by
  rw [clip01]; push_cast; ring

/-- The raw value clipped to `[0,1]`. -/
def lscClip (e m : ℕ) : ℚ := clip01 (lscRaw e m)

/-- The clipped dovetailed value is computable in the code and the step. -/
theorem computable₂_lscClip : Computable₂ lscClip := by
  have h := computable_clip01.comp computable₂_lscRaw
  exact h

/-- The clipped values are nonnegative. -/
theorem lscClip_nonneg (e m : ℕ) : 0 ≤ lscClip e m := clip01_nonneg _

/-- The clipped values are at most one. -/
theorem lscClip_le_one (e m : ℕ) : lscClip e m ≤ 1 := clip01_le_one _

attribute [irreducible] lscClip

/-- The monotone approximation enumerated by the code `e`. -/
def lscSeq (e : ℕ) : ℕ → ℚ := ratRunMaxP lscClip e

/-- The `e`-th approximation is the running maximum of the clipped values of the code `e`. -/
theorem lscSeq_eq (e n : ℕ) : lscSeq e n = ratRunMax (lscClip e) n := ratRunMaxP_eq _ _ _

/-- The approximating sequence is computable in the code and the step. -/
theorem computable₂_lscSeq : Computable₂ lscSeq := computable_ratRunMaxP computable₂_lscClip

/-- The `e`-th approximation is non-decreasing. -/
theorem monotone_lscSeq (e : ℕ) : Monotone (lscSeq e) := by
  intro i j hij
  rw [lscSeq_eq, lscSeq_eq]
  exact monotone_ratRunMax _ hij

/-- The `e`-th approximation is nonnegative. -/
theorem lscSeq_nonneg (e n : ℕ) : 0 ≤ lscSeq e n := by
  rw [lscSeq_eq]
  exact le_trans (lscClip_nonneg e n) (le_ratRunMax _ n)

/-- The `e`-th approximation stays at most one. -/
theorem lscSeq_le_one (e n : ℕ) : lscSeq e n ≤ 1 := by
  rw [lscSeq_eq]
  exact ratRunMax_le (fun k => lscClip_le_one e k) n

/-- Each clipped value is at most the running maximum reached at its step. -/
theorem lscClip_le_lscSeq (e m : ℕ) : lscClip e m ≤ lscSeq e m := by
  rw [lscSeq_eq]; exact le_ratRunMax _ m

attribute [irreducible] lscSeq

/-- The real enumerated by the code `e`. -/
noncomputable def lscReal (e : ℕ) : ℝ := ⨆ n, ((lscSeq e n : ℚ) : ℝ)

/-- The reals cast from the `e`-th approximation are bounded above, so their supremum exists. -/
theorem bddAbove_lscSeq (e : ℕ) : BddAbove (Set.range (fun n => ((lscSeq e n : ℚ) : ℝ))) := by
  refine ⟨1, ?_⟩
  rintro y ⟨n, rfl⟩
  have h : ((lscSeq e n : ℚ) : ℝ) ≤ 1 := by exact_mod_cast lscSeq_le_one e n
  exact h

/-- Every term of the `e`-th approximation is at most the real it enumerates. -/
theorem lscSeq_le_lscReal (e n : ℕ) : ((lscSeq e n : ℚ) : ℝ) ≤ lscReal e :=
  le_ciSup (bddAbove_lscSeq e) n

/-- An upper bound for all terms of the `e`-th approximation bounds the real it enumerates. -/
theorem lscReal_le_of {e : ℕ} {c : ℝ} (h : ∀ n, ((lscSeq e n : ℚ) : ℝ) ≤ c) :
    lscReal e ≤ c := ciSup_le h

/-- The enumerated real is nonnegative. -/
theorem lscReal_nonneg (e : ℕ) : 0 ≤ lscReal e :=
  le_trans (by exact_mod_cast lscSeq_nonneg e 0) (lscSeq_le_lscReal e 0)

/-- The enumerated real is at most one. -/
theorem lscReal_le_one (e : ℕ) : lscReal e ≤ 1 :=
  lscReal_le_of (fun n => by exact_mod_cast lscSeq_le_one e n)

/-- The enumerated real lies in `[0,1]`. -/
theorem lscReal_mem_Icc (e : ℕ) : lscReal e ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨lscReal_nonneg e, lscReal_le_one e⟩

/-- The `e`-th approximation converges to the real it enumerates. -/
theorem tendsto_lscSeq (e : ℕ) :
    Filter.Tendsto (fun n => ((lscSeq e n : ℚ) : ℝ)) Filter.atTop (nhds (lscReal e)) := by
  refine tendsto_atTop_ciSup ?_ (bddAbove_lscSeq e)
  intro i j hij
  have h : ((lscSeq e i : ℚ) : ℝ) ≤ ((lscSeq e j : ℚ) : ℝ) := by
    exact_mod_cast monotone_lscSeq e hij
  exact h

/-! ### Every lower semicomputable real of `[0,1]` is enumerated -/

/-- Every lower semicomputable real of `[0,1]` is enumerated by some code, so the enumeration is
onto. SUV Theorem 102, p. 160. -/
theorem exists_lscReal_eq {α : ℝ} (hmem : α ∈ Set.Icc (0 : ℝ) 1)
    (hα : IsLowerSemicomputableReal α) : ∃ e : ℕ, lscReal e = α := by
  classical
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal hα
  have hdc : Computable (fun k => clip01 (a.seq k)) := computable_clip01.comp a.isComputable
  have hdle : ∀ k, ((clip01 (a.seq k) : ℚ) : ℝ) ≤ α := by
    intro k
    rw [cast_clip01]
    have h1 : ((a.seq k : ℚ) : ℝ) ≤ α := (a.seq_lt k).le
    exact le_trans (min_le_right _ _) (max_le hmem.1 h1)
  have hdlim : Filter.Tendsto (fun k => ((clip01 (a.seq k) : ℚ) : ℝ)) Filter.atTop (nhds α) := by
    have hcast : (fun k => ((clip01 (a.seq k) : ℚ) : ℝ))
        = fun k => min 1 (max 0 ((a.seq k : ℚ) : ℝ)) := funext (fun k => cast_clip01 _)
    rw [hcast]
    have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds
    have h := hone.min (hzero.max a.tendsto)
    have hval : min (1 : ℝ) (max 0 α) = α := by
      rw [max_eq_right hmem.1, min_eq_right hmem.2]
    rwa [hval] at h
  obtain ⟨cd, hcd⟩ := Nat.Partrec.Code.exists_code.mp hdc
  obtain ⟨e, hcode⟩ : ∃ e : ℕ, Denumerable.ofNat Nat.Partrec.Code e = cd :=
    ⟨Encodable.encode cd, Denumerable.ofNat_encode cd⟩
  have heval : ∀ k : ℕ, Nat.Partrec.Code.eval cd
      (@Encodable.encode ℕ Primcodable.toEncodable k)
      = Part.some (@Encodable.encode ℚ Primcodable.toEncodable (clip01 (a.seq k))) := by
    intro k
    simp only [hcd]
    rw [@Encodable.encodek ℕ Primcodable.toEncodable]
    simp
  have hclipVal : ∀ m : ℕ,
      lscClip e m = 0 ∨ lscClip e m = clip01 (a.seq (Nat.unpair m).1) := by
    intro m
    rcases hv : Nat.Partrec.Code.evaln (Nat.unpair m).2 cd
        (@Encodable.encode ℕ Primcodable.toEncodable (Nat.unpair m).1) with _ | v
    · left
      have hz : lscRaw e m = 0 := by rw [lscRaw, hcode, hv]; rfl
      rw [lscClip, hz, clip01_zero]
    · right
      have hmem2 : v ∈ Nat.Partrec.Code.eval cd
          (@Encodable.encode ℕ Primcodable.toEncodable (Nat.unpair m).1) :=
        Nat.Partrec.Code.evaln_complete.mpr ⟨_, Option.mem_def.mpr hv⟩
      rw [heval] at hmem2
      have hveq : v = @Encodable.encode ℚ Primcodable.toEncodable
          (clip01 (a.seq (Nat.unpair m).1)) := Part.mem_some_iff.mp hmem2
      have hraw : lscRaw e m = clip01 (a.seq (Nat.unpair m).1) := by
        rw [lscRaw, hcode, hv, hveq]
        exact congrArg (fun o : Option ℚ => o.getD 0)
          (@Encodable.encodek ℚ Primcodable.toEncodable _)
      rw [lscClip, hraw,
        clip01_eq_self (clip01_nonneg (a.seq (Nat.unpair m).1))
          (clip01_le_one (a.seq (Nat.unpair m).1))]
  have hcliple : ∀ m, ((lscClip e m : ℚ) : ℝ) ≤ α := by
    intro m
    rcases hclipVal m with h | h
    · rw [h]; simpa using hmem.1
    · rw [h]; exact hdle _
  have hconv : ∀ k : ℕ, ∃ s : ℕ, lscClip e (Nat.pair k s) = clip01 (a.seq k) := by
    intro k
    have hmem2 : (@Encodable.encode ℚ Primcodable.toEncodable (clip01 (a.seq k)))
        ∈ Nat.Partrec.Code.eval cd (@Encodable.encode ℕ Primcodable.toEncodable k) := by
      rw [heval k]; exact Part.mem_some _
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hmem2
    refine ⟨s, ?_⟩
    have hraw : lscRaw e (Nat.pair k s) = clip01 (a.seq k) := by
      rw [lscRaw, hcode, Nat.unpair_pair, Option.mem_def.mp hs]
      exact congrArg (fun o : Option ℚ => o.getD 0)
        (@Encodable.encodek ℚ Primcodable.toEncodable _)
    rw [lscClip, hraw, clip01_eq_self (clip01_nonneg _) (clip01_le_one _)]
  have hrun : ∀ n : ℕ, ((ratRunMax (lscClip e) n : ℚ) : ℝ) ≤ α := by
    intro n
    induction n with
    | zero => simpa using hcliple 0
    | succ n ih =>
        rw [ratRunMax_succ]
        rcases max_cases (ratRunMax (lscClip e) n) (lscClip e (n + 1)) with ⟨hm, _⟩ | ⟨hm, _⟩
        · rw [hm]; exact ih
        · rw [hm]; exact hcliple (n + 1)
  refine ⟨e, le_antisymm ?_ ?_⟩
  · refine lscReal_le_of (fun n => ?_)
    rw [lscSeq_eq]
    exact hrun n
  · refine le_of_tendsto hdlim ?_
    filter_upwards with k
    obtain ⟨s, hs⟩ := hconv k
    calc ((clip01 (a.seq k) : ℚ) : ℝ) = ((lscClip e (Nat.pair k s) : ℚ) : ℝ) := by rw [hs]
      _ ≤ ((lscSeq e (Nat.pair k s) : ℚ) : ℝ) := by exact_mod_cast lscClip_le_lscSeq e _
      _ ≤ lscReal e := lscSeq_le_lscReal e _

/-! ### The weighted sum -/

/-- The weights `w e = 2^{-(e+1)}` of SUV p. 160. -/
def lscW (e : ℕ) : ℚ := 1 / 2 ^ (e + 1)

/-- The weights `2 ^ -(e + 1)` are positive. -/
theorem lscW_pos (e : ℕ) : 0 < lscW e := by rw [lscW]; positivity

/-- The weights are computable. -/
theorem computable_lscW : Computable lscW := by
  have hnat : Primrec (fun n : ℕ => 2 ^ (n + 1)) :=
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.succ)
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ))
    (D := fun e : ℕ => 2 ^ (e + 1)) (Computable.const 1)
    hnat.to_comp (fun _ => by positivity) (fun e => ?_)
  rw [lscW]
  push_cast
  ring

/-- The first `n` weights sum to `1 - 2 ^ -n`. -/
theorem sum_range_lscW (n : ℕ) : ∑ e ∈ Finset.range n, lscW e = 1 - 1 / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, lscW, pow_succ]
      field_simp
      ring

/-- The weights sum to at most one. -/
theorem sum_range_lscW_le_one (n : ℕ) : ∑ e ∈ Finset.range n, lscW e ≤ 1 := by
  rw [sum_range_lscW]
  have : (0 : ℚ) < 1 / 2 ^ n := by positivity
  linarith

/-- The increments of the `e`-th approximation. -/
def lscInc (e : ℕ) : ℕ → ℚ := increments (lscSeq e)

/-- The increments of the `e`-th approximation are nonnegative. -/
theorem lscInc_nonneg (e i : ℕ) : 0 ≤ lscInc e i := by
  cases i with
  | zero => exact lscSeq_nonneg e 0
  | succ i =>
      rw [lscInc, increments_succ, sub_nonneg]
      exact monotone_lscSeq e (Nat.le_succ i)

/-- The increments telescope: their partial sums recover the approximation. -/
theorem sum_range_lscInc (e n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), lscInc e i = lscSeq e n := sum_range_increments _ n

/-- The increments of one approximation sum to at most one. -/
theorem sum_range_lscInc_le_one (e n : ℕ) : ∑ i ∈ Finset.range n, lscInc e i ≤ 1 := by
  cases n with
  | zero => simp
  | succ n => rw [sum_range_lscInc]; exact lscSeq_le_one e n

/-- The increments are computable in the code and the index. -/
theorem computable₂_lscInc : Computable₂ lscInc := by
  have hbase : Computable (fun z : ℕ × ℕ => lscSeq z.1 0) :=
    computable₂_lscSeq.comp Computable.fst (Computable.const 0)
  have hstep : Computable₂ (fun (z : ℕ × ℕ) (i : ℕ) => lscSeq z.1 (i + 1) - lscSeq z.1 i) := by
    have h1 := computable₂_lscSeq.comp
      (Computable.fst.comp Computable.fst : Computable (fun w : (ℕ × ℕ) × ℕ => w.1.1))
      (Primrec.succ.to_comp.comp Computable.snd : Computable (fun w : (ℕ × ℕ) × ℕ => w.2 + 1))
    have h2 := computable₂_lscSeq.comp
      (Computable.fst.comp Computable.fst : Computable (fun w : (ℕ × ℕ) × ℕ => w.1.1))
      (Computable.snd : Computable (fun w : (ℕ × ℕ) × ℕ => w.2))
    have h := Computable₂.comp computable₂_ratSub h1 h2
    exact h
  have hcases := Computable.nat_casesOn
    (Computable.snd : Computable (fun z : ℕ × ℕ => z.2)) hbase hstep
  refine hcases.of_eq (fun z => ?_)
  obtain ⟨e, i⟩ := z
  cases i with
  | zero => rfl
  | succ i => rfl

attribute [irreducible] lscInc

/-- The universal series: the `Nat.unpair`-indexed weighted increments. -/
def bigU (m : ℕ) : ℚ := lscW (Nat.unpair m).1 * lscInc (Nat.unpair m).1 (Nat.unpair m).2

/-- The terms of the universal series are nonnegative. -/
theorem bigU_nonneg (m : ℕ) : 0 ≤ bigU m :=
  mul_nonneg (lscW_pos _).le (lscInc_nonneg _ _)

/-- The universal series is computable. -/
theorem computable_bigU : Computable bigU := by
  have hfst : Computable (fun m : ℕ => (Nat.unpair m).1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp
  have hsnd : Computable (fun m : ℕ => (Nat.unpair m).2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp
  have h := Computable₂.comp computable₂_ratMul (computable_lscW.comp hfst)
    (computable₂_lscInc.comp hfst hsnd)
  exact h

/-- The partial sums of the universal series are at most one. -/
theorem sum_range_bigU_le_one (n : ℕ) : ∑ m ∈ Finset.range n, bigU m ≤ 1 := by
  classical
  have hinj : Set.InjOn Nat.unpair ↑(Finset.range n) := by
    intro x _ y _ hxy
    have h := congrArg (fun p : ℕ × ℕ => Nat.pair p.1 p.2) hxy
    simpa [Nat.pair_unpair] using h
  have h1 : ∑ m ∈ Finset.range n, bigU m
      = ∑ p ∈ (Finset.range n).image Nat.unpair, lscW p.1 * lscInc p.1 p.2 := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun m _ => by rw [bigU])
  have hsub : (Finset.range n).image Nat.unpair ⊆ Finset.range n ×ˢ Finset.range n := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt (Nat.unpair_left_le m) hm),
        Finset.mem_range.mpr (lt_of_le_of_lt (Nat.unpair_right_le m) hm)⟩
  have h2 : ∑ p ∈ (Finset.range n).image Nat.unpair, lscW p.1 * lscInc p.1 p.2
      ≤ ∑ p ∈ Finset.range n ×ˢ Finset.range n, lscW p.1 * lscInc p.1 p.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => mul_nonneg (lscW_pos _).le (lscInc_nonneg _ _))
  have h3 : ∑ p ∈ Finset.range n ×ˢ Finset.range n, lscW p.1 * lscInc p.1 p.2
      = ∑ e ∈ Finset.range n, lscW e * ∑ j ∈ Finset.range n, lscInc e j := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl (fun e _ => by rw [Finset.mul_sum])
  have h4 : ∑ e ∈ Finset.range n, lscW e * ∑ j ∈ Finset.range n, lscInc e j
      ≤ ∑ e ∈ Finset.range n, lscW e := by
    refine Finset.sum_le_sum (fun e _ => ?_)
    calc lscW e * ∑ j ∈ Finset.range n, lscInc e j
        ≤ lscW e * 1 := by
          exact mul_le_mul_of_nonneg_left (sum_range_lscInc_le_one e n) (lscW_pos e).le
      _ = lscW e := by ring
  calc ∑ m ∈ Finset.range n, bigU m = _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := h4
    _ ≤ 1 := sum_range_lscW_le_one n

/-- The supremum of the partial sums of the universal weighted series `bigU`. -/
noncomputable def bigBeta : ℝ := ⨆ n, ∑ m ∈ Finset.range n, ((bigU m : ℚ) : ℝ)

/-- The real partial sums of the universal series are non-decreasing. -/
theorem monotone_bigU_sum :
    Monotone (fun n => ∑ m ∈ Finset.range n, ((bigU m : ℚ) : ℝ)) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [Finset.sum_range_succ]
  have : (0 : ℝ) ≤ ((bigU n : ℚ) : ℝ) := by exact_mod_cast bigU_nonneg n
  linarith

/-- The real partial sums of the universal series are at most one. -/
theorem sum_range_bigU_le_oneR (n : ℕ) :
    ∑ m ∈ Finset.range n, ((bigU m : ℚ) : ℝ) ≤ 1 := by
  have hcast : (((∑ m ∈ Finset.range n, bigU m : ℚ)) : ℝ)
      = ∑ m ∈ Finset.range n, ((bigU m : ℚ) : ℝ) := by push_cast; ring
  rw [← hcast]
  exact_mod_cast sum_range_bigU_le_one n

/-- The real partial sums of the universal series are bounded above, so their supremum exists. -/
theorem bddAbove_bigU_sum :
    BddAbove (Set.range (fun n => ∑ m ∈ Finset.range n, ((bigU m : ℚ) : ℝ))) := by
  refine ⟨1, ?_⟩
  rintro y ⟨n, rfl⟩
  exact sum_range_bigU_le_oneR n

/-- The partial sums of the universal series converge to the weighted sum `bigBeta`. -/
theorem tendsto_bigU :
    Filter.Tendsto (fun n => ∑ m ∈ Finset.range n, ((bigU m : ℚ) : ℝ)) Filter.atTop
      (nhds bigBeta) := tendsto_atTop_ciSup monotone_bigU_sum bddAbove_bigU_sum

/-- The weighted sum lies in `[0,1]`. -/
theorem bigBeta_mem_Icc : bigBeta ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have h0 : (0 : ℝ) = ∑ m ∈ Finset.range 0, ((bigU m : ℚ) : ℝ) := by simp
    rw [h0]
    exact le_ciSup bddAbove_bigU_sum 0
  · exact ciSup_le sum_range_bigU_le_oneR

/-! ### The `e`-th column -/

/-- The universal series with every column but the `e`-th deleted. -/
def colU (e m : ℕ) : ℚ :=
  if (Nat.unpair m).1 = e then lscInc e (Nat.unpair m).2 else 0

/-- The terms of a single column of the universal series are nonnegative. -/
theorem colU_nonneg (e m : ℕ) : 0 ≤ colU e m := by
  rw [colU]
  split_ifs
  · exact lscInc_nonneg _ _
  · exact le_rfl

/-- On the index `Nat.pair e j`, the `e`-th column carries the `j`-th increment of the `e`-th
approximation. -/
theorem colU_pair (e j : ℕ) : colU e (Nat.pair e j) = lscInc e j := by
  rw [colU, Nat.unpair_pair, ite_eq_left rfl]

/-- Each column of the universal series is computable. -/
theorem computable_colU (e : ℕ) : Computable (colU e) := by
  have hfst : Computable (fun m : ℕ => (Nat.unpair m).1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp
  have hsnd : Computable (fun m : ℕ => (Nat.unpair m).2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp
  have hbeq : Computable (fun m : ℕ => ((Nat.unpair m).1 == e)) :=
    Primrec.beq.to_comp.comp hfst (Computable.const e)
  have hval : Computable (fun m : ℕ => lscInc e (Nat.unpair m).2) :=
    computable₂_lscInc.comp (Computable.const e) hsnd
  have h := Computable.cond hbeq hval (Computable.const (0 : ℚ))
  refine h.of_eq (fun m => ?_)
  rw [colU]
  cases hb : ((Nat.unpair m).1 == e) with
  | false => rw [Bool.cond_false, ite_eq_right (beq_eq_false_iff_ne.mp hb)]
  | true => rw [Bool.cond_true, ite_eq_left (beq_iff_eq.mp hb)]

/-- The `e`-th column is term-by-term below `2 ^ (e + 1)` times the universal series. -/
theorem colU_le_scaled (e m : ℕ) : colU e m ≤ (2 ^ (e + 1) : ℚ) * bigU m := by
  rw [colU, bigU]
  split_ifs with h
  · rw [h, lscW]
    refine le_of_eq ?_
    field_simp
  · refine mul_nonneg (by positivity) (bigU_nonneg m)

/-- The partial sums of the `e`-th column are at most those of the increments of the `e`-th
approximation. -/
theorem sum_range_colU_le (e n : ℕ) :
    ∑ m ∈ Finset.range n, colU e m ≤ ∑ j ∈ Finset.range n, lscInc e j := by
  classical
  have h1 : ∑ m ∈ Finset.range n, colU e m
      = ∑ m ∈ (Finset.range n).filter (fun m => (Nat.unpair m).1 = e),
          lscInc e (Nat.unpair m).2 := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun m _ => by rw [colU])
  have hinj : Set.InjOn (fun m => (Nat.unpair m).2)
      ↑((Finset.range n).filter (fun m => (Nat.unpair m).1 = e)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    have hx1 := hx.2
    have hy1 := hy.2
    have hpair : Nat.unpair x = Nat.unpair y := Prod.ext (hx1.trans hy1.symm) hxy
    have h := congrArg (fun p : ℕ × ℕ => Nat.pair p.1 p.2) hpair
    simpa [Nat.pair_unpair] using h
  rw [h1, ← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => lscInc_nonneg e j)
  intro j hj
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨m, ⟨hm, _⟩, rfl⟩ := hj
  exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.unpair_right_le m) hm)

/-- Every value of the `e`-th approximation is reached by a partial sum of the `e`-th column. -/
theorem exists_sum_range_colU_ge (e n : ℕ) :
    ∃ N, lscSeq e n ≤ ∑ m ∈ Finset.range N, colU e m := by
  classical
  refine ⟨(Finset.range (n + 1)).sup (fun j => Nat.pair e j) + 1, ?_⟩
  have hinj : Set.InjOn (fun j => Nat.pair e j) ↑(Finset.range (n + 1)) := by
    intro x _ y _ h
    have h2 := congrArg (fun t => (Nat.unpair t).2) h
    simpa [Nat.unpair_pair] using h2
  have h1 : lscSeq e n = ∑ m ∈ (Finset.range (n + 1)).image (fun j => Nat.pair e j),
      colU e m := by
    rw [Finset.sum_image hinj, ← sum_range_lscInc e n]
    exact Finset.sum_congr rfl (fun j _ => (colU_pair e j).symm)
  rw [h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => colU_nonneg e m)
  intro m hm
  simp only [Finset.mem_image] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hj))

/-- The partial sums of the `e`-th column converge to the real enumerated by `e`. -/
theorem tendsto_colU (e : ℕ) :
    Filter.Tendsto (fun n => ∑ m ∈ Finset.range n, ((colU e m : ℚ) : ℝ)) Filter.atTop
      (nhds (lscReal e)) := by
  have hmono : Monotone (fun n => ∑ m ∈ Finset.range n, ((colU e m : ℚ) : ℝ)) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [Finset.sum_range_succ]
    have h : (0 : ℝ) ≤ ((colU e n : ℚ) : ℝ) := by exact_mod_cast colU_nonneg e n
    linarith
  have hle : ∀ n, ∑ m ∈ Finset.range n, ((colU e m : ℚ) : ℝ) ≤ lscReal e := by
    intro n
    have hcast : (((∑ m ∈ Finset.range n, colU e m : ℚ)) : ℝ)
        = ∑ m ∈ Finset.range n, ((colU e m : ℚ) : ℝ) := by push_cast; ring
    cases n with
    | zero => simpa using lscReal_nonneg e
    | succ n =>
        have h1 := sum_range_colU_le e (n + 1)
        rw [sum_range_lscInc] at h1
        have h2 : (((∑ m ∈ Finset.range (n + 1), colU e m : ℚ)) : ℝ)
            ≤ ((lscSeq e n : ℚ) : ℝ) := by exact_mod_cast h1
        rw [hcast] at h2
        exact le_trans h2 (lscSeq_le_lscReal e n)
  have hbdd : BddAbove (Set.range (fun n => ∑ m ∈ Finset.range n, ((colU e m : ℚ) : ℝ))) := by
    refine ⟨lscReal e, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hle n
  have htend := tendsto_atTop_ciSup hmono hbdd
  have hsup : (⨆ n, ∑ m ∈ Finset.range n, ((colU e m : ℚ) : ℝ)) = lscReal e := by
    refine le_antisymm (ciSup_le hle) ?_
    refine lscReal_le_of (fun n => ?_)
    obtain ⟨N, hN⟩ := exists_sum_range_colU_ge e n
    have hcast : (((∑ m ∈ Finset.range N, colU e m : ℚ)) : ℝ)
        = ∑ m ∈ Finset.range N, ((colU e m : ℚ) : ℝ) := by push_cast; ring
    have h2 : ((lscSeq e n : ℚ) : ℝ) ≤ (((∑ m ∈ Finset.range N, colU e m : ℚ)) : ℝ) := by
      exact_mod_cast hN
    rw [hcast] at h2
    exact le_trans h2 (le_ciSup hbdd N)
  rwa [hsup] at htend

end Kolmogorov
