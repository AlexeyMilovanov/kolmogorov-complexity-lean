import KolmogorovMathlib.AlgorithmicRandomness.EffectiveNull

/-!
# Multiplicity sets of a computable sequence of intervals

Given a computable sequence of intervals `f : ℕ → Option BitString` (an interval
being a cylinder `Ω_s`, with `none` standing for the empty set), we build for
each `N` the *multiplicity set*

`M_N = {x | x is covered by at least N of the intervals}`,

show that it is (uniformly) effectively open, and prove the Markov bound
`N * μ (M_N) ≤ ∑' i, μ (Ω_{f i})`.

This is the combinatorial core of the "if" direction of the Solovay criterion
(SUV Theorem 31).
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ### A primitive recursive prefix test on bit strings -/

/-- One step of the prefix test: consume the bit `b` from the (optional) remaining
suffix `st`. -/
def bitPrefixDrop (st : Option BitString) (b : Bool) : Option BitString :=
  st.bind (fun l => if l.head? = some b then some l.tail else none)

/-- `bitPrefixCheck s t` decides whether `s` is a prefix of `t`. -/
def bitPrefixCheck (s t : BitString) : Bool :=
  (s.foldl bitPrefixDrop (some t)).isSome

/-- Once the prefix-matching fold has failed it stays failed. -/
lemma foldl_bitPrefixDrop_none (s : BitString) : s.foldl bitPrefixDrop none = none := by
  induction s with
  | nil => rfl
  | cons b s ih => simpa [bitPrefixDrop] using ih

/-- The boolean prefix test is correct: it succeeds exactly when `s` is a prefix of `t`. -/
lemma bitPrefixCheck_iff (s t : BitString) : bitPrefixCheck s t = true ↔ s <+: t := by
  induction s generalizing t with
  | nil => simp [bitPrefixCheck]
  | cons b s ih =>
    cases t with
    | nil => simp [bitPrefixCheck, bitPrefixDrop, List.foldl, foldl_bitPrefixDrop_none]
    | cons c t =>
      by_cases hbc : c = b
      · subst hbc
        simp only [bitPrefixCheck, List.foldl_cons, bitPrefixDrop, Option.bind_some,
          List.head?_cons, List.tail_cons, if_pos]
        rw [show (List.foldl bitPrefixDrop (some t) s).isSome = bitPrefixCheck s t from rfl]
        simp [ih t]
      · have hne : (List.head? (c :: t)) ≠ some b := by simp [hbc]
        simp only [bitPrefixCheck, List.foldl_cons, bitPrefixDrop, Option.bind_some, if_neg hne,
          foldl_bitPrefixDrop_none, Option.isSome_none]
        simp only [Bool.false_eq_true, false_iff]
        intro h
        exact hbc (by simpa using (List.cons_prefix_cons.mp h).1.symm)

/-- The boolean prefix test is primitive recursive in both arguments. -/
theorem primrec₂_bitPrefixCheck : Primrec₂ bitPrefixCheck := by
  have hstep : Primrec₂ (fun (_ : BitString × BitString) (q : Option BitString × Bool) =>
      bitPrefixDrop q.1 q.2) := by
    have h1 : Primrec₂ (fun (q : Option BitString × Bool) (l : BitString) =>
        if l.head? = some q.2 then some l.tail else none) := by
      apply Primrec.ite _ (Primrec.option_some.comp (Primrec.list_tail.comp Primrec.snd))
        (Primrec.const none)
      exact Primrec.eq.comp (Primrec.list_head?.comp Primrec.snd)
        (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst))
    have h2 : Primrec₂ bitPrefixDrop := Primrec.option_bind Primrec.fst h1
    exact h2.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hfold := Primrec.list_foldl (f := fun p : BitString × BitString => p.1)
    (g := fun p : BitString × BitString => some p.2)
    Primrec.fst (Primrec.option_some.comp Primrec.snd) hstep
  exact Primrec.option_isSome.comp hfold

/-! ### Counting how many intervals cover a cylinder -/

/-- `coverBit f s i` is true when the `i`-th interval contains the cylinder `Ω_s`,
i.e. when `f i = some t` with `t` a prefix of `s`. -/
def coverBit (f : ℕ → Option BitString) (s : BitString) (i : ℕ) : Bool :=
  ((f i).map (fun t => bitPrefixCheck t s)).getD false

/-- The `i`-th covering bit of `s` is set exactly when the enumeration emits at index `i` a
string that is a prefix of `s`. -/
lemma coverBit_eq_true_iff (f : ℕ → Option BitString) (s : BitString) (i : ℕ) :
    coverBit f s i = true ↔ ∃ t, f i = some t ∧ t <+: s := by
  unfold coverBit
  cases hfi : f i with
  | none => simp
  | some t =>
    simp only [Option.map_some, Option.getD_some, bitPrefixCheck_iff]
    constructor
    · intro h; exact ⟨t, rfl, h⟩
    · rintro ⟨t', ht', hpre⟩
      rw [Option.some_inj] at ht'
      exact ht' ▸ hpre

/-- `natCount c j` counts the indices `i < j` with `c i = true`. -/
def natCount (c : ℕ → Bool) : ℕ → ℕ :=
  fun j => Nat.rec 0 (fun y IH => IH + (bif c y then 1 else 0)) j

/-- The bounded count of a boolean sequence is the cardinality of the set of indices below the
bound at which it holds. -/
lemma natCount_eq_card (c : ℕ → Bool) (j : ℕ) :
    natCount c j = ((Finset.range j).filter (fun i => c i = true)).card := by
  induction j with
  | zero => simp [natCount]
  | succ j ih =>
    have hsucc : natCount c (j + 1) = natCount c j + (bif c j then 1 else 0) := rfl
    rw [hsucc, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hb : c j = true
    · rw [if_pos hb, Finset.card_insert_of_notMem (by simp), hb]
      simp
    · have hb' : c j = false := by simpa using hb
      rw [if_neg hb, hb']
      simp

/-- The bounded count vanishes exactly when the predicate fails below the bound. -/
lemma natCount_eq_zero_iff (c : ℕ → Bool) (j : ℕ) :
    natCount c j = 0 ↔ ∀ i < j, c i = false := by
  rw [natCount_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i hi
    simpa using h (Finset.mem_range.2 hi)
  · intro h i hi
    simp [h i (Finset.mem_range.1 hi)]

/-- The bounded count of a computable boolean family is computable. -/
lemma computable_natCount {α : Type*} [Primcodable α] {C : α → ℕ → Bool}
    (hC : Computable (fun q : α × ℕ => C q.1 q.2)) :
    Computable (fun q : α × ℕ => natCount (C q.1) q.2) := by
  have hstep : Computable₂ (fun (q : α × ℕ) (p : ℕ × ℕ) =>
      p.2 + (bif C q.1 p.1 then 1 else 0)) := by
    have hb : Computable (fun r : (α × ℕ) × (ℕ × ℕ) => C r.1.1 r.2.1) :=
      hC.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))
    have hcc : Computable (fun r : (α × ℕ) × (ℕ × ℕ) =>
        bif C r.1.1 r.2.1 then 1 else 0) :=
      Computable.cond hb (Computable.const 1) (Computable.const 0)
    exact Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd) hcc
  exact Computable.nat_rec Computable.snd (Computable.const 0) hstep

/-- `coverCount f s j` is the number of indices `i < j` whose interval contains
the cylinder `Ω_s`. -/
def coverCount (f : ℕ → Option BitString) (s : BitString) : ℕ → ℕ :=
  natCount (coverBit f s)

/-- The covering count of `s` below `j` is the number of indices at which the enumeration covers
`s`. -/
lemma coverCount_eq_card (f : ℕ → Option BitString) (s : BitString) (j : ℕ) :
    coverCount f s j = ((Finset.range j).filter (fun i => coverBit f s i = true)).card :=
  natCount_eq_card _ j

/-- The covering count vanishes exactly when no index below the bound covers the string. -/
lemma coverCount_eq_zero_iff (f : ℕ → Option BitString) (s : BitString) (j : ℕ) :
    coverCount f s j = 0 ↔ ∀ i < j, coverBit f s i = false :=
  natCount_eq_zero_iff _ j

/-- Uniform computability of `coverBit`, for a computable family of interval
sequences and a computable choice of string. -/
lemma computable_coverBit_param {α : Type*} [Primcodable α] {F : α → ℕ → Option BitString}
    {S : α → BitString} (hF : Computable (fun q : α × ℕ => F q.1 q.2))
    (hS : Computable S) :
    Computable (fun q : α × ℕ => coverBit (F q.1) (S q.1) q.2) := by
  have hmap : Computable (fun q : α × ℕ =>
      (F q.1 q.2).map (fun t => bitPrefixCheck t (S q.1))) := by
    refine Computable.option_map hF ?_
    exact primrec₂_bitPrefixCheck.to_comp.comp Computable.snd
      (hS.comp (Computable.fst.comp Computable.fst))
  exact Computable.option_getD hmap (Computable.const false)

/-- The covering count is computable uniformly in a parameter. -/
lemma computable_coverCount_param {α : Type*} [Primcodable α] {F : α → ℕ → Option BitString}
    {S : α → BitString} (hF : Computable (fun q : α × ℕ => F q.1 q.2))
    (hS : Computable S) :
    Computable (fun q : α × ℕ => coverCount (F q.1) (S q.1) q.2) :=
  computable_natCount (C := fun a i => coverBit (F a) (S a) i)
    (computable_coverBit_param hF hS)

/-- The covering bit of a computable enumeration is computable. -/
lemma computable_coverBit {f : ℕ → Option BitString} (hf : Computable f) :
    Computable (fun q : BitString × ℕ => coverBit f q.1 q.2) :=
  computable_coverBit_param (F := fun _ : BitString => f) (S := id)
    (hf.comp Computable.snd) Computable.id

/-- The covering count of a computable enumeration is computable. -/
lemma computable_coverCount {f : ℕ → Option BitString} (hf : Computable f) :
    Computable (fun q : BitString × ℕ => coverCount f q.1 q.2) :=
  computable_coverCount_param (F := fun _ : BitString => f) (S := id)
    (hf.comp Computable.snd) Computable.id

/-! ### The multiplicity sets -/

/-- The set of points covered by the `i`-th interval of `f`. -/
def coverSet (f : ℕ → Option BitString) (i : ℕ) : Set CantorSeq :=
  (f i).elim ∅ cantorCylinder

/-- Each set of an enumeration is measurable. -/
lemma measurableSet_coverSet (f : ℕ → Option BitString) (i : ℕ) :
    MeasurableSet (coverSet f i) := by
  unfold coverSet
  cases f i with
  | none => simp
  | some t => simpa using measurableSet_cantorCylinder t

/-- The measure of the `i`-th enumerated set is the mass of the cylinder it names, and zero when
nothing is emitted. -/
lemma measure_coverSet (μ : Measure CantorSeq) (f : ℕ → Option BitString) (i : ℕ) :
    μ (coverSet f i) = (f i).elim 0 (cantorMass μ) := by
  unfold coverSet
  cases f i with
  | none => simp
  | some t => simp [cantorMass]

/-- The counting function: how many intervals cover a given point. -/
noncomputable def coverMultiplicity (f : ℕ → Option BitString) (x : CantorSeq) : ℝ≥0∞ :=
  ∑' i, (coverSet f i).indicator 1 x

/-- The covering multiplicity, counting how many enumerated sets contain a point, is
measurable. -/
lemma measurable_coverMultiplicity (f : ℕ → Option BitString) :
    Measurable (coverMultiplicity f) :=
  Measurable.tsum fun i =>
    measurable_one.indicator (measurableSet_coverSet f i)

/-- The integral of the covering multiplicity is the total measure of the enumerated sets counted
with repetition. -/
lemma lintegral_coverMultiplicity (μ : Measure CantorSeq) (f : ℕ → Option BitString) :
    ∫⁻ x, coverMultiplicity f x ∂μ = ∑' i, μ (coverSet f i) := by
  unfold coverMultiplicity
  rw [lintegral_tsum fun i =>
    (measurable_one.indicator (measurableSet_coverSet f i)).aemeasurable]
  exact tsum_congr fun i => lintegral_indicator_one (measurableSet_coverSet f i)

/-- Markov's inequality for the counting function. -/
lemma markov_coverMultiplicity (μ : Measure CantorSeq) (f : ℕ → Option BitString) (N : ℕ) :
    (N : ℝ≥0∞) * μ {x | (N : ℝ≥0∞) ≤ coverMultiplicity f x} ≤ ∑' i, μ (coverSet f i) := by
  rw [← lintegral_coverMultiplicity μ f]
  exact mul_meas_ge_le_lintegral₀ (measurable_coverMultiplicity f).aemeasurable _

/-- If a cylinder `Ω_s` is contained in at least `N` of the intervals, then every
point of `Ω_s` has multiplicity at least `N`. -/
lemma le_coverMultiplicity_of_coverCount {f : ℕ → Option BitString} {s : BitString}
    {j N : ℕ} (hN : N ≤ coverCount f s j) {x : CantorSeq} (hx : x ∈ cantorCylinder s) :
    (N : ℝ≥0∞) ≤ coverMultiplicity f x := by
  set S := (Finset.range j).filter (fun i => coverBit f s i = true) with hS
  have hcard : N ≤ S.card := by rw [← coverCount_eq_card]; exact hN
  have hmem : ∀ i ∈ S, x ∈ coverSet f i := by
    intro i hi
    have hb : coverBit f s i = true := (Finset.mem_filter.mp hi).2
    unfold coverBit at hb
    cases hfi : f i with
    | none => rw [hfi] at hb; simp at hb
    | some t =>
      rw [hfi] at hb
      simp only [Option.map_some, Option.getD_some] at hb
      have hpre : t <+: s := (bitPrefixCheck_iff t s).mp hb
      have : cantorCylinder s ⊆ cantorCylinder t := cantorCylinder_subset_of_prefix hpre
      simpa [coverSet, hfi] using this hx
  calc (N : ℝ≥0∞) ≤ (S.card : ℝ≥0∞) := by exact_mod_cast hcard
    _ = ∑ _i ∈ S, (1 : ℝ≥0∞) := by simp
    _ ≤ ∑ i ∈ S, (coverSet f i).indicator 1 x := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Set.indicator_of_mem (hmem i hi)]
        simp
    _ ≤ ∑' i, (coverSet f i).indicator 1 x := ENNReal.sum_le_tsum S
    _ = coverMultiplicity f x := rfl

/-! ### The effectively open multiplicity sets -/

/-- The enumeration of the intervals making up the `m`-th multiplicity set:
we enumerate pairs `(j, s)` and keep the cylinder `Ω_s` when at least `N m` of the
first `j` intervals contain it. -/
def cylEnum (cnt : BitString → ℕ → ℕ) (N : ℕ → ℕ) (m i : ℕ) : Option BitString :=
  (Encodable.decode₂ BitString (Nat.unpair i).2).bind fun s =>
    bif decide (N m ≤ cnt s (Nat.unpair i).1) then some s else none

/-- The enumeration used for the `m`-th multiplicity set of `f`. -/
def multiplicityEnum (f : ℕ → Option BitString) (N : ℕ → ℕ) : ℕ → ℕ → Option BitString :=
  cylEnum (coverCount f) N

/-- The order relation on naturals is computable as a boolean-valued function. -/
lemma computable₂_decide_le : Computable₂ (fun a b : ℕ => decide (a ≤ b)) := by
  have heq : (fun a b : ℕ => decide (a ≤ b)) = (fun a b : ℕ => a - b == 0) := by
    funext a b
    by_cases h : a ≤ b
    · simp [h, Nat.sub_eq_zero_of_le h]
    · have hne : a - b ≠ 0 := by omega
      simp [h, hne]
  rw [heq]
  exact (Primrec₂.to_comp Primrec.beq).comp
    ((Primrec₂.to_comp Primrec.nat_sub).comp Computable.fst Computable.snd)
    (Computable.const 0)

/-- The enumeration of cylinders whose covering count reaches the threshold is computable. -/
lemma computable₂_cylEnum {cnt : BitString → ℕ → ℕ}
    (hcnt : Computable (fun q : BitString × ℕ => cnt q.1 q.2))
    {N : ℕ → ℕ} (hN : Computable N) : Computable₂ (cylEnum cnt N) := by
  have hdec : Computable (fun p : ℕ × ℕ => Encodable.decode₂ BitString (Nat.unpair p.2).2) :=
    (Primrec.decode₂.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  refine Computable.option_bind hdec ?_
  have hcount : Computable (fun r : (ℕ × ℕ) × BitString =>
      cnt r.2 (Nat.unpair r.1.2).1) :=
    hcnt.comp (Computable.pair Computable.snd
      ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))).to_comp))
  have hNm : Computable (fun r : (ℕ × ℕ) × BitString => N r.1.1) :=
    hN.comp (Computable.fst.comp Computable.fst)
  have hcond : Computable (fun r : (ℕ × ℕ) × BitString =>
      decide (N r.1.1 ≤ cnt r.2 (Nat.unpair r.1.2).1)) :=
    computable₂_decide_le.comp hNm hcount
  exact Computable.cond hcond (Computable.option_some.comp Computable.snd)
    (Computable.const none)

/-- The enumeration of the high-multiplicity sets is computable. -/
lemma computable₂_multiplicityEnum {f : ℕ → Option BitString} (hf : Computable f)
    {N : ℕ → ℕ} (hN : Computable N) : Computable₂ (multiplicityEnum f N) :=
  computable₂_cylEnum (computable_coverCount hf) hN

/-- The `m`-th multiplicity set, as an effectively open set. -/
def multiplicitySet (f : ℕ → Option BitString) (N : ℕ → ℕ) (m : ℕ) : Set CantorSeq :=
  ⋃ i, (multiplicityEnum f N m i).elim ∅ cantorCylinder

/-- The high-multiplicity sets of a computable enumeration form a uniformly effectively open
family. -/
lemma isUniformlyEffectiveOpen_multiplicitySet {f : ℕ → Option BitString} (hf : Computable f)
    {N : ℕ → ℕ} (hN : Computable N) :
    IsUniformlyEffectiveOpen (multiplicitySet f N) :=
  ⟨multiplicityEnum f N, computable₂_multiplicityEnum hf hN, fun _ => rfl⟩

/-- The `m`-th high-multiplicity set consists of points covered at least `N m` times. -/
lemma multiplicitySet_subset {f : ℕ → Option BitString} {N : ℕ → ℕ} (m : ℕ) :
    multiplicitySet f N m ⊆ {x | (N m : ℝ≥0∞) ≤ coverMultiplicity f x} := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  unfold multiplicityEnum cylEnum at hi
  cases hd : Encodable.decode₂ BitString (Nat.unpair i).2 with
  | none => rw [hd] at hi; simp at hi
  | some s =>
    rw [hd] at hi
    simp only [Option.bind_some] at hi
    cases hc : decide (N m ≤ coverCount f s (Nat.unpair i).1) with
    | false => rw [hc] at hi; simp at hi
    | true =>
      rw [hc] at hi
      simp only [cond_true, Option.elim_some] at hi
      exact le_coverMultiplicity_of_coverCount (of_decide_eq_true hc) hi

/-- A point of a cylinder whose covering count reaches the threshold lies in the corresponding
high-multiplicity set. -/
lemma mem_multiplicitySet {f : ℕ → Option BitString} {N : ℕ → ℕ} {m : ℕ} {s : BitString}
    {j : ℕ} (hj : N m ≤ coverCount f s j) {x : CantorSeq} (hx : x ∈ cantorCylinder s) :
    x ∈ multiplicitySet f N m := by
  refine Set.mem_iUnion.2 ⟨Nat.pair j (Encodable.encode s), ?_⟩
  unfold multiplicityEnum cylEnum
  rw [Nat.unpair_pair, Encodable.encodek₂]
  simp only [Option.bind_some]
  rw [decide_eq_true hj]
  simpa using hx

end Kolmogorov
