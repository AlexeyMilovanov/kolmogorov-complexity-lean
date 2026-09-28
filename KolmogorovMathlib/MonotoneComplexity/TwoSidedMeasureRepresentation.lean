import KolmogorovMathlib.MonotoneComplexity.MeasureRepresentation
import KolmogorovMathlib.MonotoneComplexity.FloorSelectorObstruction

/-!
# The two-sided reading of Theorem 77(b)

`FloorSelectorObstruction.lean` shows that an exactly additive
lower-semicomputable continuous semimeasure need *not* be representable by a
measure carrying a computable dyadic **floor** selector.

This file proves the statement that does hold, and which matches the notion of
computable real used elsewhere in the project (`IsComputableENNReal`): the
cylinder masses are uniformly computable in the two-sided (Cauchy) sense.

The key point is that exactness turns a lower approximation into a two-sided
one: for every node `x`,

  `a x + ∑_{i < |x|} a (sibNode x i) = 1`,

where `sibNode x i` is the sibling of the length-`(i+1)` prefix of `x`.  Hence a
lower approximation of the (finitely many) off-path siblings yields an *upper*
approximation of `a x`, and an unbounded search for a stage at which the two
meet within `2^{-s}` produces the required computable approximation.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- A measure on Cantor space is *two-sided computable* if its cylinder masses
admit a uniformly computable sequence of dyadic approximations, the `s`-th being
accurate to within `2^{-s}`.  This is the uniform form of `IsComputableENNReal`. -/
def IsTwoSidedComputableMeasure (μ : Measure CantorSeq) : Prop :=
  ∃ c : BitString → ℕ → ℕ, Computable₂ c ∧ ∀ x s,
    cantorMass μ x ≤ dyadicValue (c x s) s + dyadicValue 1 s ∧
      dyadicValue (c x s) s ≤ cantorMass μ x + dyadicValue 1 s

/-- A two-sided computable measure has computable cylinder masses. -/
lemma IsTwoSidedComputableMeasure.isComputableENNReal_mass {μ : Measure CantorSeq}
    (h : IsTwoSidedComputableMeasure μ) (x : BitString) :
    IsComputableENNReal (cantorMass μ x) := by
  obtain ⟨c, hcomp, hbound⟩ := h
  exact ⟨fun s => c x s, fun s => hbound x s,
    hcomp.comp (Computable.const x) Computable.id⟩

/-! ### Off-path siblings -/

/-- The sibling of the length-`(i+1)` prefix of `x`: the prefix of length `i`
extended by the negation of the `i`-th bit of `x`. -/
def sibNode (x : BitString) (i : ℕ) : BitString :=
  x.take i ++ [!(x.getD i false)]

/-- Appending a bit does not change the earlier off-path siblings. -/
lemma sibNode_append_of_lt {x : BitString} {b : Bool} {i : ℕ} (h : i < x.length) :
    sibNode (x ++ [b]) i = sibNode x i := by
  unfold sibNode
  have h1 : (x ++ [b]).take i = x.take i := List.take_append_of_le_length (le_of_lt h)
  have h2 : (x ++ [b]).getD i false = x.getD i false := by
    simp [List.getD, List.getElem?_append_left h]
  rw [h1, h2]

/-- The new off-path sibling created by appending a bit is the string with that bit flipped. -/
lemma sibNode_append_self (x : BitString) (b : Bool) :
    sibNode (x ++ [b]) x.length = x ++ [!b] := by
  unfold sibNode
  have h1 : (x ++ [b]).take x.length = x := by simp
  have h2 : (x ++ [b]).getD x.length false = b := by simp [List.getD]
  rw [h1, h2]

/-- The list of masses of the off-path siblings of `x`. -/
def sibMasses (a : BitString → ℝ≥0∞) (x : BitString) : List ℝ≥0∞ :=
  (List.range x.length).map (fun i => a (sibNode x i))

/-- Appending a bit appends the mass of the new off-path sibling. -/
lemma sibMasses_append (a : BitString → ℝ≥0∞) (x : BitString) (b : Bool) :
    sibMasses a (x ++ [b]) = sibMasses a x ++ [a (x ++ [!b])] := by
  unfold sibMasses
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · exact List.map_congr_left (fun i hi => by
      rw [sibNode_append_of_lt (List.mem_range.mp hi)])
  · simp [sibNode_append_self]

/-- **Exactness in additive form.**  The mass of a node plus the masses of all
its off-path siblings is the total mass `1`. -/
lemma mass_add_sibMasses_sum {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    (hadd : ∀ x, a x = a (x ++ [false]) + a (x ++ [true])) (x : BitString) :
    a x + (sibMasses a x).sum = 1 := by
  induction x using List.reverseRecOn with
  | nil => simpa [sibMasses] using ha.1
  | append_singleton y b ih =>
      rw [sibMasses_append, List.sum_append, List.sum_singleton]
      have hchild : a (y ++ [b]) + a (y ++ [!b]) = a y := by
        cases b
        · simpa using (hadd y).symm
        · rw [add_comm]
          simpa using (hadd y).symm
      have hre : a (y ++ [b]) + ((sibMasses a y).sum + a (y ++ [!b]))
          = (a (y ++ [b]) + a (y ++ [!b])) + (sibMasses a y).sum := by ring
      rw [hre, hchild]
      exact ih

/-! ### Dyadic bookkeeping -/

/-- The dyadic value of a list sum is the sum of the dyadic values. -/
lemma dyadicValue_list_sum (l : List ℕ) (t : ℕ) :
    dyadicValue l.sum t = (l.map (fun n => dyadicValue n t)).sum := by
  induction l with
  | nil => simp [dyadicValue]
  | cons n l ih => simp [dyadicValue_add, ih]

/-- At a fixed precision, a strictly smaller dyadic value comes from a strictly smaller
numerator. -/
lemma lt_of_dyadicValue_lt {n m u : ℕ} (h : dyadicValue n u < dyadicValue m u) : n < m := by
  by_contra hc
  exact absurd (dyadicValue_le _ _ u (Nat.le_of_not_lt hc)) (not_le.mpr h)

/-- A stagewise non-decreasing family has non-decreasing dyadic list sums. -/
lemma dv_listSum_mono {f : ℕ → ℕ → ℕ}
    (hmono : ∀ i t, dyadicValue (f i t) t ≤ dyadicValue (f i (t + 1)) (t + 1))
    (l : List ℕ) (t : ℕ) :
    dyadicValue ((l.map (fun i => f i t)).sum) t
      ≤ dyadicValue ((l.map (fun i => f i (t + 1))).sum) (t + 1) := by
  rw [dyadicValue_list_sum, dyadicValue_list_sum, List.map_map, List.map_map]
  exact List.sum_le_sum (fun i _ => hmono i t)

/-- The limit of the dyadic list sums is the list sum of the limits. -/
lemma iSup_dv_listSum {f : ℕ → ℕ → ℕ}
    (hmono : ∀ i t, dyadicValue (f i t) t ≤ dyadicValue (f i (t + 1)) (t + 1))
    (l : List ℕ) :
    ⨆ t, dyadicValue ((l.map (fun i => f i t)).sum) t
      = (l.map (fun i => ⨆ t, dyadicValue (f i t) t)).sum := by
  induction l with
  | nil => simp [dyadicValue]
  | cons i l ih =>
      have hmono1 : Monotone (fun t => dyadicValue (f i t) t) :=
        monotone_nat_of_le_succ (fun t => hmono i t)
      have hmono2 : Monotone (fun t => dyadicValue ((l.map (fun j => f j t)).sum) t) :=
        monotone_nat_of_le_succ (fun t => dv_listSum_mono hmono l t)
      have hkey := ENNReal.iSup_add_iSup_of_monotone hmono1 hmono2
      simp only [List.map_cons, List.sum_cons]
      rw [← ih, hkey]
      exact iSup_congr (fun t => dyadicValue_add _ _ _)

/-! ### The two-sided approximation -/

/-- The stage-`t` lower approximation of the total mass of the off-path siblings
of `x`, as a dyadic numerator at scale `t`. -/
def sibSum (L : ℕ → BitString → ℕ) (t : ℕ) (x : BitString) : ℕ :=
  ((List.range x.length).map (fun i => L t (sibNode x i))).sum

/-- The stage-`t` *upper* approximation of `a x`, as a dyadic numerator at
scale `t`. -/
def upperNum (L : ℕ → BitString → ℕ) (t : ℕ) (x : BitString) : ℕ :=
  2 ^ t - sibSum L t x

/-- The search predicate: at stage `t` the lower and upper approximations of
`a x` are within `2^{-s}` of each other. -/
def approxClose (L : ℕ → BitString → ℕ) (x : BitString) (s t : ℕ) : Bool :=
  decide (upperNum L t x * 2 ^ s ≤ L t x * 2 ^ s + 2 ^ t)

/-- The first stage at which the lower and upper approximations of `a x` are
within `2^{-s}`. -/
noncomputable def searchStage (L : ℕ → BitString → ℕ) (x : BitString) (s : ℕ) : ℕ :=
  sInf {t | approxClose L x s t = true}

/-- The two-sided approximation: the dyadic ceiling, at scale `s`, of the lower
approximation reached at stage `searchStage L x s`. -/
noncomputable def approxNum (L : ℕ → BitString → ℕ) (x : BitString) (s : ℕ) : ℕ :=
  (L (searchStage L x s) x * 2 ^ s + (2 ^ searchStage L x s - 1))
    / 2 ^ searchStage L x s

section Approx

variable {a : BitString → ℝ≥0∞} {L : ℕ → BitString → ℕ}

/-- The stage approximation of the sibling mass never exceeds the true sibling mass. -/
lemma dyadicValue_sibSum_le (hle : ∀ t x, dyadicValue (L t x) t ≤ a x) (t : ℕ)
    (x : BitString) :
    dyadicValue (sibSum L t x) t ≤ (sibMasses a x).sum := by
  unfold sibSum sibMasses
  rw [dyadicValue_list_sum, List.map_map]
  exact List.sum_le_sum (fun i _ => hle t (sibNode x i))

/-- For an exactly additive semimeasure, the sibling sum at stage `t` stays below `2 ^ t`. -/
lemma sibSum_le_two_pow (ha : IsContinuousTreeSemimeasure a)
    (hadd : ∀ x, a x = a (x ++ [false]) + a (x ++ [true]))
    (hle : ∀ t x, dyadicValue (L t x) t ≤ a x) (t : ℕ) (x : BitString) :
    sibSum L t x ≤ 2 ^ t := by
  refine le_two_pow_of_dyadicValue_le_one ?_
  refine (dyadicValue_sibSum_le hle t x).trans ?_
  exact (mass_add_sibMasses_sum ha hadd x) ▸ le_add_self

/-- The upper approximation built from the siblings really is an upper bound for the mass. -/
lemma le_dyadicValue_upperNum (ha : IsContinuousTreeSemimeasure a)
    (hadd : ∀ x, a x = a (x ++ [false]) + a (x ++ [true]))
    (hle : ∀ t x, dyadicValue (L t x) t ≤ a x) (t : ℕ) (x : BitString) :
    a x ≤ dyadicValue (upperNum L t x) t := by
  have hS : sibSum L t x ≤ 2 ^ t := sibSum_le_two_pow ha hadd hle t x
  have hsplit : dyadicValue (upperNum L t x) t + dyadicValue (sibSum L t x) t = 1 := by
    rw [← dyadicValue_add]
    have hu : upperNum L t x + sibSum L t x = 2 ^ t := by
      unfold upperNum; omega
    rw [hu, dyadicValue_two_pow_self]
  have hne : dyadicValue (sibSum L t x) t ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by simp)
  refine (ENNReal.add_le_add_iff_right hne).mp ?_
  rw [hsplit]
  calc a x + dyadicValue (sibSum L t x) t ≤ a x + (sibMasses a x).sum :=
        add_le_add le_rfl (dyadicValue_sibSum_le hle t x)
    _ = 1 := mass_add_sibMasses_sum ha hadd x

/-- The search terminates: the lower approximations of `a x` and of the sibling
masses jointly exhaust the total mass `1`. -/
lemma exists_approxClose (ha : IsContinuousTreeSemimeasure a)
    (hadd : ∀ x, a x = a (x ++ [false]) + a (x ++ [true]))
    (hmono : ∀ t x, dyadicValue (L t x) t ≤ dyadicValue (L (t + 1) x) (t + 1))
    (hsup : ∀ x, ⨆ t, dyadicValue (L t x) t = a x) (x : BitString) (s : ℕ) :
    ∃ t, approxClose L x s t = true := by
  have hle : ∀ t y, dyadicValue (L t y) t ≤ a y := by
    intro t y
    rw [← hsup y]
    exact le_iSup (fun t => dyadicValue (L t y) t) t
  have hsupS : ⨆ t, dyadicValue (sibSum L t x) t = (sibMasses a x).sum := by
    have h := iSup_dv_listSum (f := fun i t => L t (sibNode x i))
      (fun i t => hmono t (sibNode x i)) (List.range x.length)
    unfold sibSum sibMasses
    rw [h]
    exact congrArg List.sum (List.map_congr_left (fun i _ => hsup (sibNode x i)))
  have hmono1 : Monotone (fun t => dyadicValue (L t x) t) :=
    monotone_nat_of_le_succ (fun t => hmono t x)
  have hmono2 : Monotone (fun t => dyadicValue (sibSum L t x) t) :=
    monotone_nat_of_le_succ (fun t =>
      dv_listSum_mono (f := fun i t => L t (sibNode x i))
        (fun i t => hmono t (sibNode x i)) (List.range x.length) t)
  have htot : ⨆ t, dyadicValue (L t x + sibSum L t x) t = 1 := by
    have hkey := ENNReal.iSup_add_iSup_of_monotone hmono1 hmono2
    have hsplit : ⨆ t, dyadicValue (L t x + sibSum L t x) t
        = (⨆ t, dyadicValue (L t x) t) + ⨆ t, dyadicValue (sibSum L t x) t := by
      rw [hkey]
      exact iSup_congr (fun t => dyadicValue_add _ _ _)
    rw [hsplit, hsup, hsupS]
    exact mass_add_sibMasses_sum ha hadd x
  have hlt1 : dyadicValue (2 ^ s - 1) s < 1 := by
    have hpos : (0 : ℕ) < 2 ^ s := pow_pos (by norm_num) _
    rw [← dyadicValue_two_pow_self s]
    exact dyadicValue_lt_of_lt _ (by omega)
  rw [← htot] at hlt1
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hlt1
  have hnat : (2 ^ s - 1) * 2 ^ t < (L t x + sibSum L t x) * 2 ^ s := by
    refine lt_of_dyadicValue_lt (u := s + t) ?_
    rw [← dyadicValue_scale (2 ^ s - 1) s t]
    have h2 : dyadicValue ((L t x + sibSum L t x) * 2 ^ s) (s + t)
        = dyadicValue (L t x + sibSum L t x) t := by
      rw [Nat.add_comm s t, ← dyadicValue_scale]
    rw [h2]
    exact ht
  have hS : sibSum L t x ≤ 2 ^ t := sibSum_le_two_pow ha hadd hle t x
  refine ⟨t, ?_⟩
  have e1 : (2 ^ s - 1) * 2 ^ t = 2 ^ s * 2 ^ t - 2 ^ t := by rw [Nat.sub_mul, one_mul]
  have e2 : (L t x + sibSum L t x) * 2 ^ s = L t x * 2 ^ s + sibSum L t x * 2 ^ s := by
    rw [Nat.add_mul]
  have e3 : upperNum L t x * 2 ^ s = 2 ^ t * 2 ^ s - sibSum L t x * 2 ^ s := by
    rw [upperNum, Nat.sub_mul]
  have e4 : sibSum L t x * 2 ^ s ≤ 2 ^ t * 2 ^ s := Nat.mul_le_mul_right _ hS
  have e5 : 2 ^ s * 2 ^ t = 2 ^ t * 2 ^ s := Nat.mul_comm _ _
  rw [e1, e5, e2] at hnat
  simp only [approxClose, decide_eq_true_eq]
  omega

/-! ### Correctness of the approximation -/

/-- If the two approximations ever come within `2 ^ -s`, they do so at the stage found by the
search. -/
lemma approxClose_searchStage {x : BitString} {s : ℕ} (hex : ∃ t, approxClose L x s t = true) :
    approxClose L x s (searchStage L x s) = true :=
  Nat.sInf_mem hex

/-- Comparison of dyadic values at different precisions, through the cross-multiplied numerators. -/
lemma dyadicValue_le_cross {n m u v : ℕ} (h : n * 2 ^ v ≤ m * 2 ^ u) :
    dyadicValue n u ≤ dyadicValue m v := by
  rw [dyadicValue_scale n u v, dyadicValue_scale m v u, Nat.add_comm v u]
  exact dyadicValue_le _ _ _ h

/-- Adding `2 ^ -s` to a dyadic value, written as a single dyadic value at precision `t + s`. -/
lemma dyadicValue_add_one_eq (l t s : ℕ) :
    dyadicValue l t + dyadicValue 1 s = dyadicValue (l * 2 ^ s + 2 ^ t) (t + s) := by
  rw [dyadicValue_add, ← dyadicValue_scale l t s]
  congr 1
  rw [dyadicValue_scale 1 s t, one_mul, Nat.add_comm s t]

/-- When the search predicate fires, the upper approximation is within `2 ^ -s` of the lower one. -/
lemma dyadicValue_le_of_approxClose {x : BitString} {s t : ℕ}
    (hc : approxClose L x s t = true) :
    dyadicValue (upperNum L t x) t ≤ dyadicValue (L t x) t + dyadicValue 1 s := by
  simp only [approxClose, decide_eq_true_eq] at hc
  rw [dyadicValue_add_one_eq, dyadicValue_scale (upperNum L t x) t s]
  exact dyadicValue_le _ _ _ hc

/-- The two-sided approximation is at least the lower approximation at the stage found. -/
lemma dyadicValue_approxNum_lower {x : BitString} {s : ℕ} :
    dyadicValue (L (searchStage L x s) x) (searchStage L x s)
      ≤ dyadicValue (approxNum L x s) s := by
  set t := searchStage L x s with ht
  have hQ : 0 < 2 ^ t := pow_pos (by norm_num) _
  refine dyadicValue_le_cross ?_
  have h1 : (L t x * 2 ^ s + (2 ^ t - 1)) / 2 ^ t * 2 ^ t
      + (L t x * 2 ^ s + (2 ^ t - 1)) % 2 ^ t = L t x * 2 ^ s + (2 ^ t - 1) :=
    Nat.div_add_mod' _ _
  have h2 : (L t x * 2 ^ s + (2 ^ t - 1)) % 2 ^ t < 2 ^ t := Nat.mod_lt _ hQ
  simp only [approxNum, ← ht]
  omega

/-- The two-sided approximation exceeds the lower approximation by at most `2 ^ -s`. -/
lemma dyadicValue_approxNum_upper {x : BitString} {s : ℕ} :
    dyadicValue (approxNum L x s) s
      ≤ dyadicValue (L (searchStage L x s) x) (searchStage L x s) + dyadicValue 1 s := by
  set t := searchStage L x s with ht
  rw [dyadicValue_add_one_eq, Nat.add_comm t s, dyadicValue_scale (approxNum L x s) s t]
  refine dyadicValue_le _ _ _ ?_
  have hQ : 0 < 2 ^ t := pow_pos (by norm_num) _
  have hA : (L t x * 2 ^ s + (2 ^ t - 1)) / 2 ^ t * 2 ^ t
      ≤ L t x * 2 ^ s + (2 ^ t - 1) := Nat.div_mul_le_self _ _
  simp only [approxNum, ← ht]
  omega

/-- The two-sided approximation is within `2 ^ -s` of the true mass on both sides. -/
lemma approxNum_bounds (ha : IsContinuousTreeSemimeasure a)
    (hadd : ∀ x, a x = a (x ++ [false]) + a (x ++ [true]))
    (hmono : ∀ t x, dyadicValue (L t x) t ≤ dyadicValue (L (t + 1) x) (t + 1))
    (hsup : ∀ x, ⨆ t, dyadicValue (L t x) t = a x) (x : BitString) (s : ℕ) :
    a x ≤ dyadicValue (approxNum L x s) s + dyadicValue 1 s ∧
      dyadicValue (approxNum L x s) s ≤ a x + dyadicValue 1 s := by
  have hle : ∀ t y, dyadicValue (L t y) t ≤ a y := by
    intro t y
    rw [← hsup y]
    exact le_iSup (fun t => dyadicValue (L t y) t) t
  have hclose := approxClose_searchStage (exists_approxClose ha hadd hmono hsup x s)
  have hstep := dyadicValue_le_of_approxClose hclose
  constructor
  · calc a x ≤ dyadicValue (upperNum L (searchStage L x s) x) (searchStage L x s) :=
          le_dyadicValue_upperNum ha hadd hle _ x
      _ ≤ dyadicValue (L (searchStage L x s) x) (searchStage L x s) + dyadicValue 1 s :=
          hstep
      _ ≤ dyadicValue (approxNum L x s) s + dyadicValue 1 s :=
          add_le_add dyadicValue_approxNum_lower le_rfl
  · exact dyadicValue_approxNum_upper.trans (add_le_add (hle _ x) le_rfl)

/-! ### Computability of the approximation -/

/-- The off-path sibling of a given index is primitive recursive. -/
lemma primrec_sibNode : Primrec (fun p : BitString × ℕ => sibNode p.1 p.2) := by
  unfold sibNode
  have hb : Primrec (fun p : BitString × ℕ => !(p.1.getD p.2 false)) :=
    (Primrec.dom_bool _).comp ((Primrec.list_getD false).comp Primrec.fst Primrec.snd)
  exact Primrec.list_append.comp
    (Primrec.list_take.comp Primrec.fst Primrec.snd)
    (Primrec.list_cons.comp hb (Primrec.const []))

/-- Comparison of naturals is primitive recursive. -/
lemma primrec_decide_nat_le : Primrec (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
  obtain ⟨inst, h⟩ := Primrec.nat_le
  exact h.of_eq (fun p => by rw [Subsingleton.elim (inst p) (Nat.decLe p.1 p.2)])

/-- The recursive accumulation computes the sum over the range. -/
lemma natRec_sum_eq (f : ℕ → ℕ) (n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc + f i) n)
      = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      change (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc + f i) n) + f n = _
      rw [ih, List.range_succ, List.map_append]
      simp

/-- The sibling sum, written as a plain recursion. -/
lemma sibSum_eq_natRec (t : ℕ) (x : BitString) :
    sibSum L t x
      = Nat.rec (motive := fun _ => ℕ) 0
          (fun i acc => acc + L t (sibNode x i)) x.length := by
  rw [natRec_sum_eq]
  rfl

/-- The sibling sum of a computable approximation is computable. -/
lemma computable_sibSum (hL : Computable₂ L) :
    Computable (fun q : (BitString × ℕ) × ℕ => sibSum L q.2 q.1.1) := by
  have hsib : Computable (fun r : ((BitString × ℕ) × ℕ) × (ℕ × ℕ) =>
      sibNode r.1.1.1 r.2.1) :=
    Computable₂.comp primrec_sibNode.to_comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.fst.comp Computable.snd)
  have hstep : Computable₂ (fun (q : (BitString × ℕ) × ℕ) (r : ℕ × ℕ) =>
      r.2 + L q.2 (sibNode q.1.1 r.1)) :=
    Computable₂.comp Primrec.nat_add.to_comp (Computable.snd.comp Computable.snd)
      (Computable₂.comp hL (Computable.snd.comp Computable.fst) hsib)
  have hrec := Computable.nat_rec (f := fun q : (BitString × ℕ) × ℕ => q.1.1.length)
    (g := fun _ : (BitString × ℕ) × ℕ => (0 : ℕ))
    (Computable.list_length.comp (Computable.fst.comp Computable.fst))
    (Computable.const 0) hstep
  exact hrec.of_eq (fun q => (sibSum_eq_natRec q.2 q.1.1).symm)

/-- The search predicate is computable. -/
lemma computable_approxClose (hL : Computable₂ L) :
    Computable₂ (fun (p : BitString × ℕ) (t : ℕ) => approxClose L p.1 p.2 t) := by
  have hpowT : Computable (fun q : (BitString × ℕ) × ℕ => 2 ^ q.2) :=
    primrec_two_pow_aux.to_comp.comp Computable.snd
  have hpowS : Computable (fun q : (BitString × ℕ) × ℕ => 2 ^ q.1.2) :=
    primrec_two_pow_aux.to_comp.comp (Computable.snd.comp Computable.fst)
  have hupper : Computable (fun q : (BitString × ℕ) × ℕ => 2 ^ q.2 - sibSum L q.2 q.1.1) :=
    Computable₂.comp Primrec.nat_sub.to_comp hpowT (computable_sibSum hL)
  have hlhs : Computable (fun q : (BitString × ℕ) × ℕ =>
      (2 ^ q.2 - sibSum L q.2 q.1.1) * 2 ^ q.1.2) :=
    Computable₂.comp Primrec.nat_mul.to_comp hupper hpowS
  have hLv : Computable (fun q : (BitString × ℕ) × ℕ => L q.2 q.1.1) :=
    Computable₂.comp hL Computable.snd (Computable.fst.comp Computable.fst)
  have hrhs : Computable (fun q : (BitString × ℕ) × ℕ =>
      L q.2 q.1.1 * 2 ^ q.1.2 + 2 ^ q.2) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable₂.comp Primrec.nat_mul.to_comp hLv hpowS) hpowT
  have hdecle : Computable₂ (fun m n : ℕ => decide (m ≤ n)) :=
    Computable₂.mk primrec_decide_nat_le.to_comp
  have hfin := Computable₂.comp hdecle hlhs hrhs
  change Computable (fun q : (BitString × ℕ) × ℕ => approxClose L q.1.1 q.1.2 q.2)
  exact hfin.of_eq (fun _ => rfl)

/-- When the search always succeeds, the stage it finds is computable. -/
lemma computable_searchStage (hL : Computable₂ L)
    (hex : ∀ x s, ∃ t, approxClose L x s t = true) :
    Computable (fun p : BitString × ℕ => searchStage L p.1 p.2) := by
  have hpart : Partrec (fun p : BitString × ℕ =>
      Nat.rfind (fun t => (Part.some (approxClose L p.1 p.2 t)))) :=
    Partrec.rfind (computable_approxClose hL).partrec₂
  refine Partrec.of_eq_tot hpart (fun p => ?_)
  rw [Nat.mem_rfind]
  constructor
  · simpa [searchStage] using Nat.sInf_mem (hex p.1 p.2)
  · intro m hm
    have hnm : m ∉ {t | approxClose L p.1 p.2 t = true} :=
      Nat.notMem_of_lt_sInf (by simpa [searchStage] using hm)
    simp only [Set.mem_setOf_eq, Bool.not_eq_true] at hnm
    simp [hnm]

/-- When the search always succeeds, the two-sided approximation is computable. -/
lemma computable_approxNum (hL : Computable₂ L)
    (hex : ∀ x s, ∃ t, approxClose L x s t = true) :
    Computable₂ (approxNum L) := by
  have ht : Computable (fun p : BitString × ℕ => searchStage L p.1 p.2) :=
    computable_searchStage hL hex
  have hQ : Computable (fun p : BitString × ℕ => 2 ^ searchStage L p.1 p.2) :=
    primrec_two_pow_aux.to_comp.comp ht
  have hP : Computable (fun p : BitString × ℕ => 2 ^ p.2) :=
    primrec_two_pow_aux.to_comp.comp Computable.snd
  have hLv : Computable (fun p : BitString × ℕ => L (searchStage L p.1 p.2) p.1) :=
    Computable₂.comp hL ht Computable.fst
  have hnum : Computable (fun p : BitString × ℕ =>
      L (searchStage L p.1 p.2) p.1 * 2 ^ p.2 + (2 ^ searchStage L p.1 p.2 - 1)) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable₂.comp Primrec.nat_mul.to_comp hLv hP)
      (Computable₂.comp Primrec.nat_sub.to_comp hQ (Computable.const 1))
  have hdiv : Computable₂ (fun m n : ℕ => m / n) := Primrec.nat_div.to_comp
  have hfin : Computable (fun p : BitString × ℕ =>
      (L (searchStage L p.1 p.2) p.1 * 2 ^ p.2 + (2 ^ searchStage L p.1 p.2 - 1))
        / 2 ^ searchStage L p.1 p.2) :=
    Computable₂.comp hdiv hnum hQ
  change Computable (fun p : BitString × ℕ => approxNum L p.1 p.2)
  exact hfin.of_eq (fun _ => rfl)

end Approx

/-! ### The theorem -/

/-- **Theorem 77(b), two-sided form.**  Every exactly additive
lower-semicomputable continuous semimeasure is the cylinder-mass function of a
measure on Cantor space whose masses are uniformly computable in the two-sided
sense. -/
theorem exists_isTwoSidedComputableMeasure_of_isLowerSemicomputableContinuousSemimeasure
    {a : BitString → ℝ≥0∞} (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (h_exact : ∀ x, a x = a (x ++ [false]) + a (x ++ [true])) :
    ∃ μ : Measure CantorSeq, IsTwoSidedComputableMeasure μ ∧ ∀ x, cantorMass μ x = a x := by
  obtain ⟨μ, hμ⟩ := exists_measure_cantorSeq_of_isContinuousTreeSemimeasure_of_exact ha.1 h_exact
  use μ
  refine ⟨?_, hμ⟩
  obtain ⟨L, hmono, hsup, hL⟩ := ha.2
  -- specialise the (context-indexed) lower approximation to the empty context
  set L' : ℕ → BitString → ℕ := fun t x => L t x []
  have hmono' : ∀ t x, dyadicValue (L' t x) t ≤ dyadicValue (L' (t + 1) x) (t + 1) :=
    fun t x => hmono t x []
  have hsup' : ∀ x, ⨆ t, dyadicValue (L' t x) t = a x := fun x => hsup x []
  have hpack : Computable (fun q : ℕ × BitString => (q.1, q.2, ([] : BitString))) :=
    Computable.fst.pair (Computable.snd.pair (Computable.const []))
  have hLcomp : Computable₂ L' := (hL.comp hpack).of_eq (fun _ => rfl)
  refine ⟨approxNum L', computable_approxNum hLcomp ?_, ?_⟩
  · intro x s
    exact exists_approxClose ha.1 h_exact hmono' hsup' x s
  · intro x s
    rw [hμ x]
    exact approxNum_bounds ha.1 h_exact hmono' hsup' x s

/-- Two-sided computability of the masses is exactly the shared faithful notion
`IsComputableMeasure`; the two definitions differ only in the order of the
window inequalities. -/
lemma IsTwoSidedComputableMeasure.isComputableMeasure {μ : Measure CantorSeq}
    (h : IsTwoSidedComputableMeasure μ) : IsComputableMeasure μ := by
  obtain ⟨c, hcomp, hbound⟩ := h
  exact ⟨c, hcomp, fun x s => ⟨(hbound x s).2, (hbound x s).1⟩⟩

/-- A computable measure is two-sided computable: its cylinder masses can be approximated from
both sides. -/
lemma IsComputableMeasure.isTwoSidedComputableMeasure {μ : Measure CantorSeq}
    (h : IsComputableMeasure μ) : IsTwoSidedComputableMeasure μ := by
  obtain ⟨c, hcomp, hbound⟩ := h
  exact ⟨c, hcomp, fun x s => ⟨(hbound x s).2, (hbound x s).1⟩⟩

/-- **SUV Theorem 77(b).**  Every exactly additive lower-semicomputable
continuous semimeasure is the cylinder-mass function of a computable measure on
Cantor space.  `IsComputableMeasure` is the faithful two-sided notion; the
floor-selector strengthening is refuted in `FloorSelectorObstruction.lean`. -/
theorem exists_isComputableMeasure_of_isLowerSemicomputableContinuousSemimeasure
    {a : BitString → ℝ≥0∞} (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (h_exact : ∀ x, a x = a (x ++ [false]) + a (x ++ [true])) :
    ∃ μ : Measure CantorSeq, IsComputableMeasure μ ∧ ∀ x, cantorMass μ x = a x := by
  obtain ⟨μ, hμ, hmass⟩ :=
    exists_isTwoSidedComputableMeasure_of_isLowerSemicomputableContinuousSemimeasure ha h_exact
  exact ⟨μ, hμ.isComputableMeasure, hmass⟩

end Kolmogorov
