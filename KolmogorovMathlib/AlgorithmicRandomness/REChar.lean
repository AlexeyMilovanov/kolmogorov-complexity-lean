import KolmogorovMathlib.AlgorithmicRandomness.MartinLof

/-!
# Characteristic sequences of computably enumerable sets

Let `A ⊆ ℕ` be enumerated by a computable function `f : ℕ → Option ℕ` and let `x`
be its characteristic sequence.  This file builds the stage-wise finite
approximations of `x` and assembles them into a Solovay test, showing that `x`
is never Martin-Löf random for the uniform measure (SUV Theorem 36).

The combinatorial point is that, for each length `N`, the approximation
`reSeg f N t` takes at most `N + 1` distinct values as the stage `t` grows, so the
total mass of the enumerated cylinders is at most `∑ N, (N+1) * 2⁻¹ ^ N < ∞`,
while `x` is covered once for every length `N`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open scoped NNReal

/-! ### Stage-wise approximations -/

/-- `reBit f t i` says that `i` shows up among `f 0, …, f (t-1)`. -/
def reBit (f : ℕ → Option ℕ) (t i : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun y IH => IH || ((f y).getD (i + 1) == i)) t

/-- Before any stage no element has been enumerated. -/
@[simp] lemma reBit_zero (f : ℕ → Option ℕ) (i : ℕ) : reBit f 0 i = false := rfl

/-- One more stage of the enumeration sets the bit of the element emitted at that stage. -/
@[simp] lemma reBit_succ (f : ℕ → Option ℕ) (t i : ℕ) :
    reBit f (t + 1) i = (reBit f t i || ((f t).getD (i + 1) == i)) := rfl

/-- The comparison used in the enumeration test succeeds exactly when the enumeration emits the
element in question. -/
lemma getD_beq_iff (f : ℕ → Option ℕ) (j i : ℕ) :
    ((f j).getD (i + 1) == i) = true ↔ f j = some i := by
  rcases h : f j with _ | m
  · simp
  · simp only [Option.getD_some, beq_iff_eq, Option.some.injEq]

/-- The bit of `i` is set at stage `t` exactly when `i` has been enumerated before stage `t`. -/
lemma reBit_true_iff (f : ℕ → Option ℕ) (t i : ℕ) :
    reBit f t i = true ↔ ∃ j < t, f j = some i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [reBit_succ, Bool.or_eq_true, ih, getD_beq_iff]
    constructor
    · rintro (⟨j, hj, hfj⟩ | h)
      · exact ⟨j, by omega, hfj⟩
      · exact ⟨t, by omega, h⟩
    · rintro ⟨j, hj, hfj⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Or.inl ⟨j, h, hfj⟩
      · exact Or.inr (h ▸ hfj)

/-- Once a bit of the approximation is set it stays set. -/
lemma reBit_mono (f : ℕ → Option ℕ) {t t' i : ℕ} (h : t ≤ t')
    (ht : reBit f t i = true) : reBit f t' i = true := by
  rw [reBit_true_iff] at ht ⊢
  obtain ⟨j, hj, hfj⟩ := ht
  exact ⟨j, lt_of_lt_of_le hj h, hfj⟩

/-- The stagewise approximation of the characteristic function is computable. -/
lemma computable_reBit {f : ℕ → Option ℕ} (hf : Computable f) :
    Computable₂ (reBit f) := by
  have hstep : Computable₂ (fun (a : ℕ × ℕ) (p : ℕ × Bool) =>
      p.2 || ((f p.1).getD (a.2 + 1) == a.2)) := by
    have h1 : Computable (fun q : (ℕ × ℕ) × (ℕ × Bool) => q.2.2) :=
      Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : (ℕ × ℕ) × (ℕ × Bool) => f q.2.1) :=
      hf.comp (Computable.fst.comp Computable.snd)
    have h3 : Computable (fun q : (ℕ × ℕ) × (ℕ × Bool) => q.1.2 + 1) :=
      Computable.succ.comp (Computable.snd.comp Computable.fst)
    have h5 : Computable (fun q : (ℕ × ℕ) × (ℕ × Bool) => (f q.2.1).getD (q.1.2 + 1)) :=
      Computable.option_getD h2 h3
    have h4 : Computable (fun q : (ℕ × ℕ) × (ℕ × Bool) =>
        ((f q.2.1).getD (q.1.2 + 1) == q.1.2)) :=
      Primrec.beq.to_comp.comp h5 (Computable.snd.comp Computable.fst)
    exact (Primrec.dom_bool₂ (fun a b => a || b)).to_comp.comp h1 h4
  exact Computable.nat_rec (α := ℕ × ℕ) (σ := Bool) (f := fun a : ℕ × ℕ => a.1)
    (g := fun _ => false)
    (h := fun (a : ℕ × ℕ) (p : ℕ × Bool) => p.2 || ((f p.1).getD (a.2 + 1) == a.2))
    Computable.fst (Computable.const false) hstep

/-- `reSeg f N t` is the length-`N` approximation, at stage `t`, of the characteristic
sequence of the set enumerated by `f`. -/
def reSeg (f : ℕ → Option ℕ) (N t : ℕ) : BitString :=
  Nat.rec (motive := fun _ => BitString) [] (fun y IH => IH ++ [reBit f t y]) N

/-- The empty initial segment of the approximation. -/
@[simp] lemma reSeg_zero (f : ℕ → Option ℕ) (t : ℕ) : reSeg f 0 t = [] := rfl

/-- The initial segment of length `N + 1` extends the one of length `N` by the next bit. -/
@[simp] lemma reSeg_succ (f : ℕ → Option ℕ) (N t : ℕ) :
    reSeg f (N + 1) t = reSeg f N t ++ [reBit f t N] := rfl

/-- The initial segment of index `N` has length `N`. -/
@[simp] lemma reSeg_length (f : ℕ → Option ℕ) (N t : ℕ) : (reSeg f N t).length = N := by
  induction N with
  | zero => simp
  | succ N ih => simp [ih]

/-- The entries of the initial segment are the corresponding approximation bits. -/
lemma reSeg_getElem? (f : ℕ → Option ℕ) (N t i : ℕ) (h : i < N) :
    (reSeg f N t)[i]? = some (reBit f t i) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [reSeg_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · rw [List.getElem?_append_left (by rw [reSeg_length]; exact hlt)]
      exact ih hlt
    · subst heq
      rw [List.getElem?_append_right (by rw [reSeg_length])]
      simp

/-- The initial segments of the approximation are computable in the length and the stage. -/
lemma computable_reSeg {f : ℕ → Option ℕ} (hf : Computable f) :
    Computable₂ (reSeg f) := by
  have hbit := computable_reBit hf
  have hstep : Computable₂ (fun (a : ℕ × ℕ) (p : ℕ × BitString) =>
      p.2 ++ [reBit f a.2 p.1]) := by
    have h1 : Computable (fun q : (ℕ × ℕ) × (ℕ × BitString) => q.2.2) :=
      Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : (ℕ × ℕ) × (ℕ × BitString) => reBit f q.1.2 q.2.1) :=
      hbit.comp (Computable.snd.comp Computable.fst) (Computable.fst.comp Computable.snd)
    exact Computable.list_concat.comp h1 h2
  exact Computable.nat_rec (α := ℕ × ℕ) (σ := BitString) (f := fun a : ℕ × ℕ => a.1)
    (g := fun _ => []) (h := fun (a : ℕ × ℕ) (p : ℕ × BitString) => p.2 ++ [reBit f a.2 p.1])
    Computable.fst (Computable.const []) hstep

/-! ### Counting the ones -/

/-- The number of ones in `reSeg f N t`. -/
def reCnt (f : ℕ → Option ℕ) (N t : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => IH + (if reBit f t y then 1 else 0)) N

/-- The empty initial segment contains no enumerated element. -/
@[simp] lemma reCnt_zero (f : ℕ → Option ℕ) (t : ℕ) : reCnt f 0 t = 0 := rfl

/-- The count over the first `N + 1` positions adds the bit at position `N`. -/
@[simp] lemma reCnt_succ (f : ℕ → Option ℕ) (N t : ℕ) :
    reCnt f (N + 1) t = reCnt f N t + (if reBit f t N then 1 else 0) := rfl

/-- The number of ones among the first `N` bits of a sequence. -/
def bitCnt (x : CantorSeq) (N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => IH + (if x y then 1 else 0)) N

/-- The empty prefix of a sequence contains no one. -/
@[simp] lemma bitCnt_zero (x : CantorSeq) : bitCnt x 0 = 0 := rfl

/-- The number of ones in the first `N + 1` bits adds the bit at position `N`. -/
@[simp] lemma bitCnt_succ (x : CantorSeq) (N : ℕ) :
    bitCnt x (N + 1) = bitCnt x N + (if x N then 1 else 0) := rfl

/-- The count over the first `N` positions is at most `N`. -/
lemma reCnt_le (f : ℕ → Option ℕ) (N t : ℕ) : reCnt f N t ≤ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [reCnt_succ]
    have : (if reBit f t N then 1 else 0) ≤ 1 := by split <;> omega
    omega

/-- The count over a fixed window increases with the stage. -/
lemma reCnt_mono (f : ℕ → Option ℕ) (N : ℕ) {t t' : ℕ} (h : t ≤ t') :
    reCnt f N t ≤ reCnt f N t' := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [reCnt_succ, reCnt_succ]
    have hbit : (if reBit f t N then 1 else 0) ≤ (if reBit f t' N then 1 else 0) := by
      by_cases hb : reBit f t N = true
      · rw [if_pos hb, if_pos (reBit_mono f h hb)]
      · rw [if_neg hb]; positivity
    omega

/-- The count over the first `N` positions is computable in the length and the stage. -/
lemma computable_reCnt {f : ℕ → Option ℕ} (hf : Computable f) :
    Computable₂ (reCnt f) := by
  have hbit := computable_reBit hf
  have hstep : Computable₂ (fun (a : ℕ × ℕ) (p : ℕ × ℕ) =>
      p.2 + (if reBit f a.2 p.1 then 1 else 0)) := by
    have h1 : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.2.2) :=
      Computable.snd.comp Computable.snd
    have h2 : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) => reBit f q.1.2 q.2.1) :=
      hbit.comp (Computable.snd.comp Computable.fst) (Computable.fst.comp Computable.snd)
    have h3 : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
        (if reBit f q.1.2 q.2.1 then 1 else 0)) := by
      have hc := Computable.cond h2 (Computable.const 1) (Computable.const 0)
      exact hc.of_eq (fun q => by cases reBit f q.1.2 q.2.1 <;> simp)
    exact Primrec.nat_add.to_comp.comp h1 h3
  exact Computable.nat_rec (α := ℕ × ℕ) (σ := ℕ) (f := fun a : ℕ × ℕ => a.1)
    (g := fun _ => 0)
    (h := fun (a : ℕ × ℕ) (p : ℕ × ℕ) => p.2 + (if reBit f a.2 p.1 then 1 else 0))
    Computable.fst (Computable.const 0) hstep

/-! ### New stages -/

/-- `reNew f N t` marks the stages at which the number of ones in the length-`N`
approximation increases (together with the initial stage). -/
def reNew (f : ℕ → Option ℕ) (N t : ℕ) : Bool :=
  Nat.casesOn (motive := fun _ => Bool) t true
    (fun s => !(reCnt f N (s + 1) == reCnt f N s))

/-- Stage zero is by convention a stage at which the window has changed. -/
@[simp] lemma reNew_zero (f : ℕ → Option ℕ) (N : ℕ) : reNew f N 0 = true := rfl

/-- A stage is new for the window of size `N` exactly when the count over that window has
increased at that stage. -/
lemma reNew_succ_true_iff (f : ℕ → Option ℕ) (N t : ℕ) :
    reNew f N (t + 1) = true ↔ reCnt f N (t + 1) ≠ reCnt f N t := by
  simp [reNew]

/-- The test for a new stage is computable. -/
lemma computable_reNew {f : ℕ → Option ℕ} (hf : Computable f) :
    Computable₂ (reNew f) := by
  have hcnt := computable_reCnt hf
  have hstep : Computable₂ (fun (a : ℕ × ℕ) (s : ℕ) =>
      !(reCnt f a.1 (s + 1) == reCnt f a.1 s)) := by
    have h1 : Computable (fun q : (ℕ × ℕ) × ℕ => reCnt f q.1.1 (q.2 + 1)) :=
      hcnt.comp (Computable.fst.comp Computable.fst) (Computable.succ.comp Computable.snd)
    have h2 : Computable (fun q : (ℕ × ℕ) × ℕ => reCnt f q.1.1 q.2) :=
      hcnt.comp (Computable.fst.comp Computable.fst) Computable.snd
    have h3 : Computable (fun q : (ℕ × ℕ) × ℕ =>
        (reCnt f q.1.1 (q.2 + 1) == reCnt f q.1.1 q.2)) := Primrec.beq.to_comp.comp h1 h2
    exact (Primrec.dom_bool (fun b => !b)).to_comp.comp h3
  exact Computable.nat_casesOn (α := ℕ × ℕ) (σ := Bool) (f := fun a : ℕ × ℕ => a.2)
    (g := fun _ => true)
    (h := fun (a : ℕ × ℕ) (s : ℕ) => !(reCnt f a.1 (s + 1) == reCnt f a.1 s))
    Computable.snd (Computable.const true) hstep

/-- At a new stage the count over the window strictly increases. -/
lemma reCnt_lt_of_new (f : ℕ → Option ℕ) (N t : ℕ) (h : reNew f N (t + 1) = true) :
    reCnt f N t < reCnt f N (t + 1) := by
  rw [reNew_succ_true_iff] at h
  have hmono : reCnt f N t ≤ reCnt f N (t + 1) := reCnt_mono f N (by omega)
  omega

/-- Distinct new stages have distinct counts over the window. -/
lemma reNew_injOn_reCnt (f : ℕ → Option ℕ) (N : ℕ) :
    Set.InjOn (reCnt f N) {t | reNew f N t = true} := by
  have key : ∀ t1 t2, t1 < t2 → reNew f N t2 = true → reCnt f N t1 < reCnt f N t2 := by
    intro t1 t2 hlt h2
    obtain ⟨s, rfl⟩ : ∃ s, t2 = s + 1 := ⟨t2 - 1, by omega⟩
    have h1 : reCnt f N t1 ≤ reCnt f N s := reCnt_mono f N (by omega)
    exact lt_of_le_of_lt h1 (reCnt_lt_of_new f N s h2)
  intro t1 h1 t2 h2 heq
  rcases lt_trichotomy t1 t2 with h | h | h
  · exact absurd heq (ne_of_lt (key t1 t2 h h2))
  · exact h
  · exact absurd heq.symm (ne_of_lt (key t2 t1 h h1))

/-- Only finitely many stages are new for a given window. -/
lemma reNew_finite (f : ℕ → Option ℕ) (N : ℕ) : {t | reNew f N t = true}.Finite := by
  refine Set.Finite.of_finite_image ?_ (reNew_injOn_reCnt f N)
  refine Set.Finite.subset (Set.finite_Iic N) ?_
  rintro _ ⟨t, -, rfl⟩
  exact reCnt_le f N t

/-- There are at most `N + 1` new stages for the window of size `N`. -/
lemma reNew_card_le (f : ℕ → Option ℕ) (N : ℕ) :
    (reNew_finite f N).toFinset.card ≤ (Finset.range (N + 1)).card := by
  refine Finset.card_le_card_of_injOn (reCnt f N) ?_ ?_
  · intro t _
    simp only [Finset.coe_range, Set.mem_Iio]
    have : reCnt f N t ≤ N := reCnt_le f N t
    omega
  · intro t1 h1 t2 h2 heq
    refine reNew_injOn_reCnt f N ?_ ?_ heq
    · simpa using h1
    · simpa using h2

/-! ### The total mass of the test is finite -/

/-- The Solovay test associated with the enumeration `f`: at index `⟨N, t⟩` it outputs
the length-`N` approximation at stage `t`, but only at the stages where the number of
ones has just increased. -/
def reTest (f : ℕ → Option ℕ) (n : ℕ) : Option BitString :=
  bif reNew f n.unpair.1 n.unpair.2 then some (reSeg f n.unpair.1 n.unpair.2) else none

/-- The test built from a computable enumeration is computable. -/
lemma computable_reTest {f : ℕ → Option ℕ} (hf : Computable f) :
    Computable (reTest f) := by
  have hseg := computable_reSeg hf
  have hnew := computable_reNew hf
  have hu1 : Computable (fun n : ℕ => n.unpair.1) := (Primrec.fst.comp Primrec.unpair).to_comp
  have hu2 : Computable (fun n : ℕ => n.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
  exact Computable.cond (hnew.comp hu1 hu2)
    (Computable.option_some.comp (hseg.comp hu1 hu2)) (Computable.const none)

/-- The series `∑ₙ (n+1) 2^{-n}` converges. -/
lemma tsum_succ_mul_inv_two_pow_ne_top :
    (∑' N : ℕ, ((N : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ N) ≠ ∞ := by
  have hsummable : Summable (fun N : ℕ => ((N : ℝ≥0) + 1) * (2 : ℝ≥0)⁻¹ ^ N) := by
    rw [← NNReal.summable_coe]
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * ((2 : ℝ)⁻¹) ^ n) := by
      apply summable_pow_mul_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs]
      norm_num
    have h2 : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) := by
      apply summable_geometric_of_lt_one <;> norm_num
    refine (h1.add h2).congr fun n => ?_
    push_cast
    ring
  have hne := (ENNReal.tsum_coe_ne_top_iff_summable).2 hsummable
  have hcast : ∀ N : ℕ, ((((N : ℝ≥0) + 1) * (2 : ℝ≥0)⁻¹ ^ N : ℝ≥0) : ℝ≥0∞)
      = ((N : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ N := by
    intro N
    push_cast
    ring
  rw [tsum_congr hcast] at hne
  exact hne

/-- Each emitted cylinder of the test has uniform measure `2^{-N}` at a new stage and is empty
otherwise. -/
lemma reTest_term (f : ℕ → Option ℕ) (N t : ℕ) :
    (reTest f (Nat.pair N t)).elim 0 (cantorMass uniformMeasure)
      = if reNew f N t = true then (2 : ℝ≥0∞)⁻¹ ^ N else 0 := by
  simp only [reTest, Nat.unpair_pair]
  cases h : reNew f N t
  · simp
  · simp [cantorMass_uniformMeasure]

/-- The cylinders emitted for the window of size `N` have total uniform measure at most
`(N + 1) 2^{-N}`. -/
lemma reTest_tsum_inner_le (f : ℕ → Option ℕ) (N : ℕ) :
    (∑' t, (reTest f (Nat.pair N t)).elim 0 (cantorMass uniformMeasure))
      ≤ ((N : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ N := by
  have hfin := reNew_finite f N
  have hzero : ∀ t ∉ hfin.toFinset,
      (reTest f (Nat.pair N t)).elim 0 (cantorMass uniformMeasure) = 0 := by
    intro t ht
    rw [reTest_term]
    have hnot : reNew f N t ≠ true := fun h => ht (by simpa using h)
    simp [hnot]
  rw [tsum_eq_sum hzero]
  have hsum : ∑ t ∈ hfin.toFinset,
      (reTest f (Nat.pair N t)).elim 0 (cantorMass uniformMeasure)
      = ∑ _t ∈ hfin.toFinset, (2 : ℝ≥0∞)⁻¹ ^ N := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have hnew : reNew f N t = true := by simpa using ht
    rw [reTest_term, if_pos hnew]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  gcongr
  have hcard := reNew_card_le f N
  rw [Finset.card_range] at hcard
  calc ((hfin.toFinset.card : ℝ≥0∞)) ≤ ((N + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast hcard
    _ = (N : ℝ≥0∞) + 1 := by push_cast; ring

/-- The test built from an enumeration has finite total uniform measure. -/
lemma reTest_tsum_lt_top (f : ℕ → Option ℕ) :
    (∑' n, (reTest f n).elim 0 (cantorMass uniformMeasure)) < ∞ := by
  set F : ℕ → ℝ≥0∞ := fun n => (reTest f n).elim 0 (cantorMass uniformMeasure) with hF
  have h1 : ∑' (p : ℕ × ℕ), F (Nat.pair p.1 p.2) = ∑' n, F n :=
    Nat.pairEquiv.tsum_eq F
  have h2 : ∑' (p : ℕ × ℕ), F (Nat.pair p.1 p.2) = ∑' N, ∑' t, F (Nat.pair N t) :=
    ENNReal.tsum_prod (f := fun N t => F (Nat.pair N t))
  have h3 : ∑' N, ∑' t, F (Nat.pair N t) ≤ ∑' N : ℕ, ((N : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ N :=
    ENNReal.tsum_le_tsum (fun N => reTest_tsum_inner_le f N)
  rw [← h1, h2]
  exact lt_of_le_of_lt h3 (lt_of_le_of_ne le_top tsum_succ_mul_inv_two_pow_ne_top)

/-! ### The test covers the characteristic sequence infinitely often -/

variable {f : ℕ → Option ℕ} {x : CantorSeq}

/-- Every bit set in the approximation is a one of the characteristic sequence. -/
lemma reBit_imp_of_charSeq (hx : ∀ n, x n = true ↔ ∃ i, f i = some n) (t i : ℕ)
    (h : reBit f t i = true) : x i = true := by
  obtain ⟨j, -, hj⟩ := (reBit_true_iff f t i).1 h
  exact (hx i).2 ⟨j, hj⟩

/-- The stagewise count never exceeds the true number of ones in the prefix. -/
lemma reCnt_le_bitCnt (hx : ∀ n, x n = true ↔ ∃ i, f i = some n) (N t : ℕ) :
    reCnt f N t ≤ bitCnt x N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [reCnt_succ, bitCnt_succ]
    have hbit : (if reBit f t N then 1 else 0) ≤ (if x N then 1 else 0) := by
      by_cases hb : reBit f t N = true
      · rw [if_pos hb, if_pos (reBit_imp_of_charSeq hx t N hb)]
      · rw [if_neg hb]; positivity
    omega

/-- Once the counts agree, the approximation agrees with the characteristic sequence on the whole
window. -/
lemma reBit_eq_of_reCnt_eq (hx : ∀ n, x n = true ↔ ∃ i, f i = some n) (N t : ℕ)
    (heq : reCnt f N t = bitCnt x N) : ∀ i < N, reBit f t i = x i := by
  induction N with
  | zero => intro i hi; omega
  | succ N ih =>
    rw [reCnt_succ, bitCnt_succ] at heq
    have hle := reCnt_le_bitCnt (x := x) hx N t
    have hbit : (if reBit f t N then 1 else 0) ≤ (if x N then 1 else 0) := by
      by_cases hb : reBit f t N = true
      · rw [if_pos hb, if_pos (reBit_imp_of_charSeq hx t N hb)]
      · rw [if_neg hb]; positivity
    have hN : reCnt f N t = bitCnt x N := by omega
    have hlast : reBit f t N = x N := by
      have hsame : (if reBit f t N then (1 : ℕ) else 0) = (if x N then 1 else 0) := by omega
      by_cases hb : reBit f t N = true
      · have hxN : x N = true := reBit_imp_of_charSeq hx t N hb
        rw [hb, hxN]
      · have hbf : reBit f t N = false := by simpa using hb
        rw [hbf] at hsame ⊢
        by_cases hxN : x N = true
        · rw [hxN] at hsame; simp at hsame
        · have hxf : x N = false := by simpa using hxN
          rw [hxf]
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact ih hN i h
    · exact h ▸ hlast

/-- Agreement of the approximation on a window forces agreement of the counts. -/
lemma reCnt_eq_of_reBit_eq (N t : ℕ) (h : ∀ i < N, reBit f t i = x i) :
    reCnt f N t = bitCnt x N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [reCnt_succ, bitCnt_succ, ih (fun i hi => h i (by omega)), h N (by omega)]

/-- For every window there is a stage at which the count has caught up. -/
lemma exists_stage_reCnt_eq (hx : ∀ n, x n = true ↔ ∃ i, f i = some n) (N : ℕ) :
    ∃ t, reCnt f N t = bitCnt x N := by
  have key : ∀ N : ℕ, ∃ t, ∀ i < N, x i = true → reBit f t i = true := by
    intro N
    induction N with
    | zero => exact ⟨0, by omega⟩
    | succ N ih =>
      obtain ⟨t, ht⟩ := ih
      by_cases hxN : x N = true
      · obtain ⟨j, hj⟩ := (hx N).1 hxN
        refine ⟨max t (j + 1), ?_⟩
        intro i hi hxi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact reBit_mono f (le_max_left _ _) (ht i h hxi)
        · refine reBit_mono f (le_max_right t (j + 1)) ?_
          rw [reBit_true_iff]
          exact ⟨j, by omega, h ▸ hj⟩
      · refine ⟨t, ?_⟩
        intro i hi hxi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact ht i h hxi
        · exact absurd (h ▸ hxi) hxN
  obtain ⟨t, ht⟩ := key N
  refine ⟨t, reCnt_eq_of_reBit_eq N t ?_⟩
  intro i hi
  by_cases hb : reBit f t i = true
  · rw [hb, reBit_imp_of_charSeq hx t i hb]
  · have hbf : reBit f t i = false := by simpa using hb
    have hxi : x i ≠ true := fun hxi => hb (ht i hi hxi)
    rw [hbf, (by simpa using hxi : x i = false)]

/-- When the approximation agrees on a window, its initial segment is the prefix of the
characteristic sequence. -/
lemma reSeg_eq_cantorPrefix (N t : ℕ) (h : ∀ i < N, reBit f t i = x i) :
    reSeg f N t = cantorPrefix x N := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < N := by simpa using h1
    have hget := reSeg_getElem? f N t i hi
    rw [List.getElem?_eq_getElem h1, Option.some.injEq] at hget
    rw [hget, cantorPrefix_getElem, h i hi]

/-- Every prefix of the characteristic sequence of a computably enumerable set is emitted by the
test, so that sequence fails it. -/
lemma reTest_hits (hx : ∀ n, x n = true ↔ ∃ i, f i = some n) (N : ℕ) :
    ∃ t, reTest f (Nat.pair N t) = some (cantorPrefix x N) := by
  classical
  have hex := exists_stage_reCnt_eq hx N
  refine ⟨Nat.find hex, ?_⟩
  have hspec : reCnt f N (Nat.find hex) = bitCnt x N := Nat.find_spec hex
  have hseg : reSeg f N (Nat.find hex) = cantorPrefix x N :=
    reSeg_eq_cantorPrefix N (Nat.find hex) (reBit_eq_of_reCnt_eq hx N _ hspec)
  have hnew : reNew f N (Nat.find hex) = true := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨s, hs⟩ : ∃ s, Nat.find hex = s + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hne : reCnt f N s ≠ bitCnt x N := Nat.find_min hex (by omega)
      rw [hs, reNew_succ_true_iff, ← hs, hspec]
      exact fun h => hne h.symm
  simp only [reTest, Nat.unpair_pair, hnew, cond_true, hseg]

/-- **SUV Theorem 36.** The characteristic sequence of a computably enumerable set of
naturals is not Martin-Löf random with respect to the uniform measure. -/
theorem not_isMartinLofRandom_of_reChar (hf : Computable f)
    (hx : ∀ n, x n = true ↔ ∃ i, f i = some n) :
    ¬ IsMartinLofRandom uniformMeasure x := by
  classical
  refine not_isMartinLofRandom_of_solovay_test isComputableMeasure_uniform x (reTest f)
    (computable_reTest hf) (reTest_tsum_lt_top f) ?_
  choose T hT using fun N => reTest_hits hx N
  refine Set.infinite_of_injective_forall_mem (f := fun N => Nat.pair N (T N)) ?_ ?_
  · intro N1 N2 h
    have h' := congrArg Nat.unpair h
    simp only [Nat.unpair_pair, Prod.mk.injEq] at h'
    exact h'.1
  · intro N
    simp only [Set.mem_ofPred_eq, hT N, Option.elim_some]
    exact mem_cantorCylinder_cantorPrefix x N

end Kolmogorov
