import KolmogorovMathlib.AlgorithmicRandomness.BlockMap
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveLaws
import KolmogorovMathlib.AlgorithmicRandomness.JumpRandom
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof

/-!
# Computable injective subsequences (SUV Chapter 3, Problem 82)

If `f : ℕ → ℕ` is computable and injective and `x` is Martin-Löf random with
respect to the uniform measure on Cantor space, then the selected subsequence
`n ↦ x (f n)` is again uniformly Martin-Löf random.

The proof uses the Solovay-test characterisation of ML-randomness.  Given a
Solovay test `g` for the selected sequence, we pull each of its cylinders back
along `f`.  The pullback of `cantorCylinder s` is the set of `x` with
`x (f k) = s[k]` for all `k < s.length`, a set determined by the coordinates
below `selectBound f s.length`, hence a finite disjoint union of cylinders of
that common length.  Injectivity of `f` makes the total uniform mass of that
union exactly `2 ^ (-s.length)`, i.e. the mass of the original cylinder, so the
pulled-back test is again a Solovay test, and it hits `x` whenever the original
test hits the selected sequence.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- The subsequence of `x` selected by the index function `f`. -/
def selectSeq (f : ℕ → ℕ) (x : CantorSeq) : CantorSeq := fun n => x (f n)

/-- The subsequence selected by `f` has `n`-th bit `x (f n)`. -/
@[simp] lemma selectSeq_apply (f : ℕ → ℕ) (x : CantorSeq) (n : ℕ) :
    selectSeq f x n = x (f n) := rfl

/-- A bound strictly above `f 0, …, f (L - 1)`. -/
def selectBound (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 => max (selectBound f L) (f L + 1)

/-- Every index `f k` with `k < L` is below the bound `selectBound f L`, so a length-`L` initial
segment of the selected subsequence is determined by that many bits of the source. -/
lemma lt_selectBound (f : ℕ → ℕ) : ∀ {k L : ℕ}, k < L → f k < selectBound f L := by
  intro k L
  induction L with
  | zero => intro h; omega
  | succ L ih =>
      intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
      · exact lt_of_lt_of_le (ih h') (le_max_left _ _)
      · subst h'; exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

/-- `selectCompat f s y L` tests whether the bits of `y` at the positions
`f 0, …, f (L - 1)` agree with the first `L` bits of `s`. -/
def selectCompat (f : ℕ → ℕ) (s y : BitString) : ℕ → Bool
  | 0 => true
  | k + 1 => selectCompat f s y k && (y[f k]? == s[k]?)

/-- The compatibility test succeeds exactly when `y` agrees with `s` at the first `L` selected
positions. -/
lemma selectCompat_iff (f : ℕ → ℕ) (s y : BitString) (L : ℕ) :
    selectCompat f s y L = true ↔ ∀ k, k < L → y[f k]? = s[k]? := by
  induction L with
  | zero => simp [selectCompat]
  | succ L ih =>
      simp only [selectCompat, Bool.and_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hk'
        · exact h1 k hk'
        · subst hk'; exact h2
      · intro h
        exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h L (Nat.lt_succ_self _)⟩

/-- Membership in the pullback of a cylinder is decided by the length-`selectBound`
prefix. -/
lemma selectCompat_cantorPrefix_iff (f : ℕ → ℕ) (s : BitString) (x : CantorSeq) :
    selectCompat f s (cantorPrefix x (selectBound f s.length)) s.length = true ↔
      selectSeq f x ∈ cantorCylinder s := by
  rw [selectCompat_iff]
  constructor
  · intro h k hk
    have hfk : f k < selectBound f s.length := lt_selectBound f hk
    have hlen : f k < (cantorPrefix x (selectBound f s.length)).length := by
      simpa using hfk
    have := h k hk
    rw [List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hk] at this
    simpa using this
  · intro h k hk
    have hfk : f k < selectBound f s.length := lt_selectBound f hk
    have hlen : f k < (cantorPrefix x (selectBound f s.length)).length := by
      simpa using hfk
    rw [List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hk]
    have := h k hk
    simpa using this

private lemma bernoulliHalf_singleton (b : Bool) :
    ProbabilityTheory.bernoulliMeasure true false
        ⟨(1/2 : NNReal), by norm_num, by norm_num⟩ {b} = 2⁻¹ := by
  have hhalf : ((1/2 : NNReal) : ℝ≥0∞) = 2⁻¹ := by
    rw [show ((1/2 : NNReal) : ℝ≥0∞) = ((1 : ℝ≥0∞) / 2) from
      ENNReal.coe_div (by norm_num), div_eq_mul_inv, one_mul]
  cases b
  · have hcoe : unitInterval.toNNReal
        (unitInterval.symm ⟨(1/2 : NNReal), by norm_num, by norm_num⟩) = 1/2 := by
      ext
      rw [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
      norm_num
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem _
        (measurableSet_singleton _) (by simp) rfl, hcoe, hhalf]
  · have hcoe : unitInterval.toNNReal
        ⟨(1/2 : NNReal), by norm_num, by norm_num⟩ = 1/2 := rfl
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _
        (measurableSet_singleton _) rfl (by simp), hcoe, hhalf]

/-- The pullback of a cylinder along an injective index function has the same
uniform measure as the cylinder itself. -/
theorem uniformMeasure_selectSeq_preimage {f : ℕ → ℕ} (hf : Function.Injective f)
    (s : BitString) :
    uniformMeasure {x : CantorSeq | selectSeq f x ∈ cantorCylinder s}
      = cantorMass uniformMeasure s := by
  classical
  rw [cantorMass_uniformMeasure]
  set L := s.length with hL
  set S : Finset ℕ := (Finset.range L).image f with hS
  set t : ℕ → Set Bool := fun m => {b | ∀ k, (h : k < L) → f k = m → s[k] = b} with ht
  have hset : {x : CantorSeq | selectSeq f x ∈ cantorCylinder s} = Set.pi ↑S t := by
    ext x
    constructor
    · intro h m _
      simp only [ht, Set.mem_ofPred_eq]
      intro k' hk' hkk'
      have hxk : x (f k') = s[k'] := h k' hk'
      rw [hkk'] at hxk
      exact hxk.symm
    · intro h k hk
      have hmem : f k ∈ S := by
        simp only [hS, Finset.mem_image, Finset.mem_range]
        exact ⟨k, hk, rfl⟩
      have hxk := h (f k) hmem
      simp only [ht, Set.mem_ofPred_eq] at hxk
      exact (hxk k hk rfl).symm
  rw [hset]
  have hpi : uniformMeasure (Set.pi ↑S t)
      = ∏ i ∈ S, ProbabilityTheory.bernoulliMeasure true false
          ⟨(1/2 : NNReal), by norm_num, by norm_num⟩ (t i) := by
    change Measure.infinitePi
        (fun _ : ℕ => ProbabilityTheory.bernoulliMeasure true false
          ⟨(1/2 : NNReal), by norm_num, by norm_num⟩)
        (Set.pi ↑S t) = _
    exact Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete)
  rw [hpi]
  have hterm : ∀ m ∈ S, ProbabilityTheory.bernoulliMeasure true false
        ⟨(1/2 : NNReal), by norm_num, by norm_num⟩ (t m)
      = (2 : ℝ≥0∞)⁻¹ := by
    intro m hm
    simp only [hS, Finset.mem_image, Finset.mem_range] at hm
    obtain ⟨k0, hk0, rfl⟩ := hm
    have hsing : t (f k0) = {s[k0]} := by
      ext b
      simp only [ht, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      refine ⟨fun h => (h k0 hk0 rfl).symm, ?_⟩
      rintro rfl k hk hfk
      have hkk : k = k0 := hf hfk
      subst hkk
      rfl
    rw [hsing, bernoulliHalf_singleton]
  rw [Finset.prod_congr rfl hterm, Finset.prod_const,
    Finset.card_image_of_injective _ hf, Finset.card_range]

/-- The pullback of a cylinder along `f` is measurable. -/
lemma measurableSet_selectSeq_preimage (f : ℕ → ℕ) (s : BitString) :
    MeasurableSet {x : CantorSeq | selectSeq f x ∈ cantorCylinder s} := by
  classical
  set N := selectBound f s.length with hN
  set F : BitString → ℝ≥0∞ :=
    fun y => if selectCompat f s y s.length then 1 else 0 with hF
  have hpre : {x : CantorSeq | selectSeq f x ∈ cantorCylinder s}
      = (fun w => F (cantorPrefix w N)) ⁻¹' {1} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, hF]
    rw [← selectCompat_cantorPrefix_iff f s w]
    cases selectCompat f s (cantorPrefix w N) s.length <;> simp
  rw [hpre]
  exact measurable_comp_cantorPrefix N F (measurableSet_singleton 1)

/-- The masses of the length-`selectBound` cylinders making up the pullback of a
cylinder add up to the mass of the cylinder. -/
theorem sum_levelFinset_selectCompat {f : ℕ → ℕ} (hf : Function.Injective f)
    (s : BitString) :
    ∑ y ∈ levelFinset (selectBound f s.length),
        (if selectCompat f s y s.length then cantorMass uniformMeasure y else 0)
      = cantorMass uniformMeasure s := by
  classical
  set N := selectBound f s.length with hN
  set A := {x : CantorSeq | selectSeq f x ∈ cantorCylinder s} with hA
  set F : BitString → ℝ≥0∞ :=
    fun y => if selectCompat f s y s.length then 1 else 0 with hF
  have hind : (fun w => F (cantorPrefix w N)) = A.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext w
    by_cases hw : w ∈ A
    · have hc : selectCompat f s (cantorPrefix w N) s.length = true :=
        (selectCompat_cantorPrefix_iff f s w).2 hw
      simp [hF, hc, Set.indicator_of_mem hw]
    · have hc : selectCompat f s (cantorPrefix w N) s.length ≠ true := fun hc =>
        hw ((selectCompat_cantorPrefix_iff f s w).1 hc)
      simp [hF, hc, Set.indicator_of_notMem hw]
  have hint : ∫⁻ w, F (cantorPrefix w N) ∂uniformMeasure = uniformMeasure A := by
    rw [hind, lintegral_indicator_const (measurableSet_selectSeq_preimage f s) 1, one_mul]
  rw [← uniformMeasure_selectSeq_preimage hf s, ← hint,
    lintegral_comp_cantorPrefix uniformMeasure N F]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hc : selectCompat f s y s.length <;> simp [hF, hc]

/-- The `m`-th cylinder of the pullback of `cantorCylinder s` along `f`. -/
def selectPullOne (f : ℕ → ℕ) (s : BitString) (m : ℕ) : Option BitString :=
  ((levelList (selectBound f s.length))[m]?).bind
    (fun y => if selectCompat f s y s.length then some y else none)

/-- The pullback along `f` of a Solovay test `g`. -/
def selectPullTest (f : ℕ → ℕ) (g : ℕ → Option BitString) (n : ℕ) : Option BitString :=
  (g n.unpair.1).bind (fun s => selectPullOne f s n.unpair.2)

/-- For an injective selection function, the cylinders pulled back from `s` have total uniform
measure equal to the uniform measure of the cylinder of `s`. -/
lemma tsum_selectPullOne {f : ℕ → ℕ} (hf : Function.Injective f) (s : BitString) :
    (∑' m, (selectPullOne f s m).elim 0 (cantorMass uniformMeasure))
      = cantorMass uniformMeasure s := by
  classical
  set N := selectBound f s.length with hN
  set h : BitString → ℝ≥0∞ :=
    fun y => if selectCompat f s y s.length then cantorMass uniformMeasure y else 0 with hh
  have hpt : ∀ m, (selectPullOne f s m).elim 0 (cantorMass uniformMeasure)
      = ((levelList N)[m]?).elim 0 h := by
    intro m
    unfold selectPullOne
    cases (levelList N)[m]? with
    | none => simp
    | some y => by_cases hc : selectCompat f s y s.length <;> simp [hh, hc]
  rw [tsum_congr hpt, tsum_list_getElem?_elim, ← sum_levelFinset_eq_sum_levelList]
  exact sum_levelFinset_selectCompat hf s

/-- Pulling an enumerated family of cylinders back along an injective selection function
preserves its total uniform measure. -/
lemma tsum_selectPullTest {f : ℕ → ℕ} (hf : Function.Injective f)
    (g : ℕ → Option BitString) :
    (∑' n, (selectPullTest f g n).elim 0 (cantorMass uniformMeasure))
      = ∑' i, (g i).elim 0 (cantorMass uniformMeasure) := by
  classical
  rw [← (Nat.pairEquiv).tsum_eq
    (fun n => (selectPullTest f g n).elim 0 (cantorMass uniformMeasure))]
  have hstep : ∑' c : ℕ × ℕ,
        (selectPullTest f g (Nat.pairEquiv c)).elim 0 (cantorMass uniformMeasure)
      = ∑' c : ℕ × ℕ,
        (g c.1).elim 0 (fun s => (selectPullOne f s c.2).elim 0 (cantorMass uniformMeasure)) := by
    refine tsum_congr fun c => ?_
    obtain ⟨i, m⟩ := c
    simp only [selectPullTest, Nat.pairEquiv_apply, Function.uncurry_apply_pair,
      Nat.unpair_pair]
    cases g i with
    | none => simp
    | some s => simp
  rw [hstep]
  refine Eq.trans (ENNReal.tsum_prod
    (f := fun i m => (g i).elim 0
      (fun s => (selectPullOne f s m).elim 0 (cantorMass uniformMeasure)))) ?_
  refine tsum_congr fun i => ?_
  cases g i with
  | none => simp
  | some s => simpa using tsum_selectPullOne hf s

/-- The bound on source indices needed for `L` selected positions is computable. -/
lemma computable_selectBound {α : Type*} [Primcodable α] {f : ℕ → ℕ} (hf : Computable f)
    {L : α → ℕ} (hL : Computable L) :
    Computable fun a => selectBound f (L a) := by
  have hstep : Computable₂ (fun (_ : α) (q : ℕ × ℕ) => max q.2 (f q.1 + 1)) := by
    have h1 : Computable (fun r : α × (ℕ × ℕ) => r.2.2) := Computable.snd.comp Computable.snd
    have h2 : Computable (fun r : α × (ℕ × ℕ) => f r.2.1 + 1) :=
      Primrec.succ.to_comp.comp (hf.comp (Computable.fst.comp Computable.snd))
    exact (Primrec.nat_max.to_comp.comp h1 h2).to₂
  refine (Computable.nat_rec hL (Computable.const 0) hstep).of_eq fun a => ?_
  generalize L a = m
  induction m with
  | zero => rfl
  | succ m ih => simp [selectBound, ← ih, Nat.max_comm]

/-- The compatibility test between a target string and a source string is computable in all of
its arguments. -/
lemma computable_selectCompat {α : Type*} [Primcodable α] {f : ℕ → ℕ} (hf : Computable f)
    {s y : α → BitString} (hs : Computable s) (hy : Computable y)
    {L : α → ℕ} (hL : Computable L) :
    Computable fun a => selectCompat f (s a) (y a) (L a) := by
  have hstep : Computable₂ (fun (a : α) (q : ℕ × Bool) =>
      q.2 && ((y a)[f q.1]? == (s a)[q.1]?)) := by
    have hprev : Computable (fun r : α × (ℕ × Bool) => r.2.2) :=
      Computable.snd.comp Computable.snd
    have hk : Computable (fun r : α × (ℕ × Bool) => r.2.1) :=
      Computable.fst.comp Computable.snd
    have hya : Computable (fun r : α × (ℕ × Bool) => (y r.1)[f r.2.1]?) :=
      Primrec.list_getElem?.to_comp.comp (hy.comp Computable.fst) (hf.comp hk)
    have hsa : Computable (fun r : α × (ℕ × Bool) => (s r.1)[r.2.1]?) :=
      Primrec.list_getElem?.to_comp.comp (hs.comp Computable.fst) hk
    have heq : Computable (fun r : α × (ℕ × Bool) => ((y r.1)[f r.2.1]? == (s r.1)[r.2.1]?)) :=
      (Primrec.dom_finite (fun p : Option Bool × Option Bool => (p.1 == p.2))).to_comp.comp
        (Computable.pair hya hsa)
    exact ((Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp.comp hprev heq).to₂
  refine (Computable.nat_rec hL (Computable.const true) hstep).of_eq fun a => ?_
  generalize L a = m
  induction m with
  | zero => rfl
  | succ m ih => simp [selectCompat, ← ih]

/-- The pullback of a computable enumeration along a computable selection function is
computable. -/
lemma computable_selectPullTest {f : ℕ → ℕ} (hf : Computable f)
    {g : ℕ → Option BitString} (hg : Computable g) :
    Computable (selectPullTest f g) := by
  have hbody : Computable₂ (fun (n : ℕ) (s : BitString) => selectPullOne f s n.unpair.2) := by
    have hn : Computable (fun a : ℕ × BitString => a.1) := Computable.fst
    have hs : Computable (fun a : ℕ × BitString => a.2) := Computable.snd
    have hlen : Computable (fun a : ℕ × BitString => (a.2 : BitString).length) :=
      Primrec.list_length.to_comp.comp hs
    have hN : Computable (fun a : ℕ × BitString => selectBound f a.2.length) :=
      computable_selectBound hf hlen
    have hlist : Computable (fun a : ℕ × BitString => levelList (selectBound f a.2.length)) :=
      primrec_levelList.to_comp.comp hN
    have hidx : Computable (fun a : ℕ × BitString => a.1.unpair.2) :=
      (Primrec.snd.comp Primrec.unpair).to_comp.comp hn
    have hopt : Computable (fun a : ℕ × BitString =>
        (levelList (selectBound f a.2.length))[a.1.unpair.2]?) :=
      Primrec.list_getElem?.to_comp.comp hlist hidx
    have hcompat : Computable (fun r : (ℕ × BitString) × BitString =>
        selectCompat f r.1.2 r.2 r.1.2.length) :=
      computable_selectCompat hf (hs.comp Computable.fst) Computable.snd
        (hlen.comp Computable.fst)
    have hinner : Computable₂ (fun (a : ℕ × BitString) (y : BitString) =>
        if selectCompat f a.2 y a.2.length then some y else none) := by
      refine (Computable.cond hcompat (Computable.option_some.comp Computable.snd)
        (Computable.const none)).to₂.of_eq ?_
      rintro ⟨a, y⟩
      cases h : selectCompat f a.2 y a.2.length <;> simp [h]
    exact (Computable.option_bind hopt hinner).to₂
  have hga : Computable (fun n : ℕ => g n.unpair.1) :=
    hg.comp ((Primrec.fst.comp Primrec.unpair).to_comp)
  exact Computable.option_bind hga hbody

/-- If the original test hits the selected sequence at stage `i`, then the pulled
back test hits `x` at some stage paired with `i`. -/
lemma exists_mem_selectPullOne {f : ℕ → ℕ} {s : BitString} {x : CantorSeq}
    (h : selectSeq f x ∈ cantorCylinder s) :
    ∃ m, x ∈ (selectPullOne f s m).elim ∅ cantorCylinder := by
  classical
  set N := selectBound f s.length with hN
  set y := cantorPrefix x N with hy
  have hc : selectCompat f s y s.length = true :=
    (selectCompat_cantorPrefix_iff f s x).2 h
  have hmem : y ∈ levelList N := mem_levelList.2 (by simp [hy])
  obtain ⟨m, hm, hget⟩ := List.getElem_of_mem hmem
  refine ⟨m, ?_⟩
  have hopt : (levelList N)[m]? = some y := by
    rw [List.getElem?_eq_getElem hm, hget]
  rw [selectPullOne, ← hN, hopt]
  simp only [Option.bind_some, hc, ite_true, Option.elim_some]
  change IsCantorPrefix y x
  rw [isCantorPrefix_iff_cantorPrefix_eq]
  simp [hy]

/-- **SUV Chapter 3, Problem 82.** If `f` is computable and injective, then the
subsequence `n ↦ x (f n)` of a uniformly ML-random sequence `x` is uniformly
ML-random. -/
theorem isMartinLofRandom_uniform_selectSeq {f : ℕ → ℕ} (hfc : Computable f)
    (hf : Function.Injective f) {x : CantorSeq}
    (hx : IsMartinLofRandom uniformMeasure x) :
    IsMartinLofRandom uniformMeasure (selectSeq f x) := by
  classical
  by_contra hnot
  rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_uniform] at hnot
  obtain ⟨g, hgc, hgsum, hginf⟩ := hnot
  have hxnot : ¬ IsMartinLofRandom uniformMeasure x := by
    rw [not_isMartinLofRandom_iff_solovay_test isComputableMeasure_uniform]
    refine ⟨selectPullTest f g, computable_selectPullTest hfc hgc, ?_, ?_⟩
    · rw [tsum_selectPullTest hf g]; exact hgsum
    · -- each stage `i` at which `g` hits the selected sequence yields a stage
      -- `Nat.pair i m` at which the pulled back test hits `x`
      have hchoice : ∀ i ∈ {i | selectSeq f x ∈ (g i).elim ∅ cantorCylinder},
          ∃ m, x ∈ (selectPullTest f g (Nat.pair i m)).elim ∅ cantorCylinder := by
        intro i hi
        simp only [Set.mem_ofPred_eq] at hi
        cases hgi : g i with
        | none => rw [hgi] at hi; simp at hi
        | some s =>
            rw [hgi] at hi
            simp only [Option.elim_some] at hi
            obtain ⟨m, hm⟩ := exists_mem_selectPullOne hi
            refine ⟨m, ?_⟩
            simpa [selectPullTest, hgi] using hm
      choose! pick hpick using hchoice
      refine Set.Infinite.mono (s := (fun i => Nat.pair i (pick i)) ''
        {i | selectSeq f x ∈ (g i).elim ∅ cantorCylinder}) ?_ ?_
      · rintro n ⟨i, hi, rfl⟩
        exact hpick i hi
      · refine Set.Infinite.image ?_ hginf
        intro a _ b _ hab
        exact (Nat.pair_eq_pair.1 hab).1
  exact hxnot hx

end Kolmogorov
