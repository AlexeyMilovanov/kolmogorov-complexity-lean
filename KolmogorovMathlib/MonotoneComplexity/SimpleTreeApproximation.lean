import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Foundation.PrimrecExtras

namespace Kolmogorov

open scoped ENNReal

/-! ### Computable fixed-width binary words

The bottom-up closure evaluator below indexes a complete binary level by natural
numbers.  `simpleApproxBits k i` is the length-`k`, big-endian word formed from
the low `k` bits of `i`.  In particular, doubling an index appends `false`, and
doubling and adding one appends `true`.  The explicit padding is important: the
identities hold even when `i` has more than `k` bits. -/

/-- The length-`k` big-endian word formed from the low `k` bits of `i`, used to index a complete
binary level. -/
def simpleApproxBits (k i : ℕ) : BitString :=
  ((Nat.bits i ++ List.replicate k false).take k).reverse

/-- The word of width zero is empty. -/
@[simp] lemma simpleApproxBits_zero (i : ℕ) : simpleApproxBits 0 i = [] := by
  simp [simpleApproxBits]

private lemma take_append_false_padding_succ (l : BitString) (k : ℕ) :
    (l ++ List.replicate (k + 1) false).take k =
      (l ++ List.replicate k false).take k := by
  rw [List.take_append, List.take_append]
  by_cases h : k ≤ l.length
  · simp [h]
  · have hlt : l.length < k := Nat.lt_of_not_ge h
    simp only [List.replicate_succ']
    rw [List.take_append_of_le_length (by simp)]

/-- Doubling an index appends a zero bit to its word. -/
lemma simpleApproxBits_left (k i : ℕ) :
    simpleApproxBits (k + 1) (2 * i) = simpleApproxBits k i ++ [false] := by
  by_cases hi : i = 0
  · subst i
    simp [simpleApproxBits, Nat.zero_bits, List.replicate_succ]
  · rw [simpleApproxBits, Nat.bit0_bits i hi, simpleApproxBits]
    simp only [List.cons_append, List.take_succ_cons, List.reverse_cons]
    rw [take_append_false_padding_succ]

/-- Doubling an index and adding one appends a one bit to its word. -/
lemma simpleApproxBits_right (k i : ℕ) :
    simpleApproxBits (k + 1) (2 * i + 1) = simpleApproxBits k i ++ [true] := by
  rw [simpleApproxBits, Nat.bit1_bits, simpleApproxBits]
  simp only [List.cons_append, List.take_succ_cons, List.reverse_cons]
  rw [take_append_false_padding_succ]

/-- The indexing word is primitive recursive in the width and the index. -/
lemma primrec_simpleApproxBits :
    Primrec (fun p : ℕ × ℕ => simpleApproxBits p.1 p.2) := by
  unfold simpleApproxBits
  exact Primrec.list_reverse.comp
    (Primrec.list_take.comp
      (Primrec.list_append.comp (primrec_natBits.comp Primrec.snd)
        (Primrec.list_replicate.comp Primrec.fst (Primrec.const false)))
      Primrec.fst)

/-- The indexing word is computable in the width and the index. -/
lemma computable_simpleApproxBits :
    Computable (fun p : ℕ × ℕ => simpleApproxBits p.1 p.2) :=
  primrec_simpleApproxBits.to_comp

/-- `simpleApproxBits k i` is a word of length exactly `k`: the explicit padding
by `k` copies of `false` guarantees that the truncation to `k` bits never runs
out of digits. -/
@[simp] lemma simpleApproxBits_length (k i : ℕ) :
    (simpleApproxBits k i).length = k := by
  simp [simpleApproxBits]

/-- Peeling off the least significant bit: the last letter of
`simpleApproxBits (k + 1) i` records the parity of `i`, and the preceding block
is the width-`k` word of `i / 2`. -/
lemma simpleApproxBits_succ (k i : ℕ) :
    simpleApproxBits (k + 1) i =
      simpleApproxBits k (i / 2) ++ [decide (i % 2 = 1)] := by
  obtain ⟨m, hm⟩ : ∃ m, i / 2 = m := ⟨i / 2, rfl⟩
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have hi : i = 2 * m := by omega
    subst hi
    rw [simpleApproxBits_left, hm]
    simp [h]
  · have hi : i = 2 * m + 1 := by omega
    subst hi
    rw [simpleApproxBits_right, hm]
    simp [h]

/-- On the range `[0, 2 ^ k)` the width-`k` binary encoding is injective. -/
lemma simpleApproxBits_injective_of_lt_two_pow {k i j : ℕ}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k)
    (h : simpleApproxBits k i = simpleApproxBits k j) :
    i = j := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at hi hj
    omega
  | succ k ih =>
    rw [simpleApproxBits_succ, simpleApproxBits_succ] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    have hd : i / 2 = j / 2 := ih (by omega) (by omega) h1
    have h2' : (i % 2 = 1) ↔ (j % 2 = 1) := by simpa using h2
    omega

private lemma getD_range_map {α : Type*} (n : ℕ) (f : ℕ → α) (i : ℕ)
    (fallback : α) (h : i < n) :
    ((List.range n).map f).getD i fallback = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-- Mapping a computable two-argument function over `List.range (n a)` is computable in `a`. -/
lemma computable_range_map {α β : Type*} [Primcodable α] [Primcodable β]
    (n : α → ℕ) (g : α → ℕ → β) (hn : Computable n)
    (hg : Computable (fun q : α × ℕ => g q.1 q.2)) :
    Computable (fun a => (List.range (n a)).map (g a)) := by
  have hstep : Computable₂ (fun (a : α) (q : ℕ × List β) => q.2 ++ [g a q.1]) := by
    have hg' : Computable (fun q : α × (ℕ × List β) => g q.1 q.2.1) :=
      hg.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
    exact (Computable.list_concat.comp (Computable.snd.comp Computable.snd) hg').to₂
  exact (Computable.nat_rec hn (Computable.const []) hstep).of_eq fun a => by
    induction n a with
    | zero => rfl
    | succ n ih => simp [List.range_succ, ih]

/-- A simple approximation of a tree semimeasure: a computable stagewise numerator that is exact
at the root, supermultiplicative over children, vanishes below the stage frontier, has
non-decreasing dyadic values, and converges to the semimeasure. -/
def IsSimpleTreeApproximation (a : BitString → ℝ≥0∞) (q : ℕ → BitString → ℕ) : Prop :=
  (∀ s, q s [] = 2 ^ s) ∧
  (∀ s x, q s (x ++ [false]) + q s (x ++ [true]) ≤ q s x) ∧
  (∀ s x, s < x.length → q s x = 0) ∧
  (∀ s x, dyadicValue (q s x) s ≤ dyadicValue (q (s + 1) x) (s + 1)) ∧
  (∀ x, ⨆ s, dyadicValue (q s x) s = a x) ∧
  Computable (fun p : ℕ × BitString => q p.1 p.2)

/-- The bottom-up closure of a raw approximation at depth budget `d`: the raw value at a node,
raised to the sum of the closures of its two children. -/
def simpleApproxClosure (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) : ℕ → BitString → ℕ
  | 0, x => approx s x []
  | d + 1, x => max (approx s x [])
      (simpleApproxClosure approx s d (x ++ [false]) + simpleApproxClosure approx s d (x ++ [true]))

-- We define `simpleApprox` as a standalone `def` for the recursive construction.
-- It takes the raw approximation `approx s x []` from `ha.2` and closes it bottom-up.
/-- The simple approximation built from a raw one: zero below the stage frontier, `2 ^ s` at the
root, and the bottom-up closure elsewhere. -/
def simpleApprox (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString) : ℕ :=
  if x.length > s then 0
  else if x = [] then 2 ^ s
  else simpleApproxClosure approx s (s - x.length) x

section Lemmas

variable (a : BitString → ℝ≥0∞) (approx : ℕ → BitString → BitString → ℕ)
variable (H_mono : ∀ s out ctx,
  dyadicValue (approx s out ctx) s ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
variable (H_sup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = a out)
variable (ha : IsContinuousTreeSemimeasure a)

/-- The dyadic value is monotone in its numerator. -/
lemma dyadicValue_le (n m s : ℕ) (h : n ≤ m) : dyadicValue n s ≤ dyadicValue m s :=
  dyadicValue_mono_num h s

/-- The dyadic value of a maximum is the maximum of the dyadic values. -/
lemma dyadicValue_max (n m s : ℕ) :
    dyadicValue (max n m) s = max (dyadicValue n s) (dyadicValue m s) :=
  (monotone_dyadicValue_num s).map_max

/-- At the root the raw approximation never exceeds the full stage mass `2 ^ s`. -/
lemma approx_root_le (a : BitString → ℝ≥0∞) (approx : ℕ → BitString → BitString → ℕ)
    (H_sup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = a out)
    (ha : IsContinuousTreeSemimeasure a) (s : ℕ) : approx s [] [] ≤ 2 ^ s := by
  have h1 : dyadicValue (approx s [] []) s ≤ a [] := by
    have h_sup : ⨆ s, dyadicValue (approx s [] []) s = a [] := H_sup [] []
    rw [← h_sup]
    exact le_iSup (fun s => dyadicValue (approx s [] []) s) s
  have h2 : a [] = 1 := ha.1
  rw [h2] at h1
  unfold dyadicValue at h1
  have h3 : (approx s [] [] : ℝ≥0∞) ≤ 1 * (2 : ℝ≥0∞) ^ s := by
    exact (ENNReal.div_le_iff_le_mul (Or.inl (by simp)) (Or.inr (by simp))).mp h1
  rw [one_mul] at h3
  exact_mod_cast h3

/-- The simple approximation carries the full stage mass at the root. -/
lemma simpleApprox_root (s : ℕ) : simpleApprox approx s [] = 2 ^ s := by
  unfold simpleApprox
  split_ifs with h1 h2
  · simp at h1
  · rfl
  · exact False.elim (h2 rfl)

/-- The simple approximation vanishes at nodes longer than the stage. -/
lemma simpleApprox_vanishes_below_frontier (s : ℕ) (x : BitString) (h : s < x.length) :
    simpleApprox approx s x = 0 := by
  unfold simpleApprox
  split_ifs with h1
  · rfl
  · omega

/-- The closure never falls below the raw approximation. -/
lemma simpleApproxClosure_ge_raw (s d : ℕ) (x : BitString) :
    approx s x [] ≤ simpleApproxClosure approx s d x := by
  cases d
  · rfl
  · exact Nat.le_max_left _ _

/-- Above the stage frontier the simple approximation dominates the raw one. -/
lemma simpleApprox_raw_le (a : BitString → ℝ≥0∞) (approx : ℕ → BitString → BitString → ℕ)
    (H_sup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = a out)
    (ha : IsContinuousTreeSemimeasure a) (s : ℕ) (x : BitString) (hx : x.length ≤ s) :
    approx s x [] ≤ simpleApprox approx s x := by
  unfold simpleApprox
  split_ifs with h1 h2
  · omega
  · rw [h2]
    exact approx_root_le a approx H_sup ha s
  · exact simpleApproxClosure_ge_raw approx s _ x

/-- The closure is supermultiplicative: the two children at budget `d` fit into the parent at
budget `d + 1`. -/
lemma simpleApproxClosure_coherent (s d : ℕ) (x : BitString) :
    simpleApproxClosure approx s d (x ++ [false]) + simpleApproxClosure approx s d (x ++ [true])
      ≤ simpleApproxClosure approx s (d + 1) x := by
  exact Nat.le_max_right _ _

/-- The closure never exceeds the semimeasure it approximates. -/
lemma simpleApproxClosure_le_target (a : BitString → ℝ≥0∞) (approx : ℕ → BitString → BitString → ℕ)
    (H_sup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = a out)
    (ha : IsContinuousTreeSemimeasure a) (s d : ℕ) (x : BitString) (hx : s - x.length = d) :
    dyadicValue (simpleApproxClosure approx s d x) s ≤ a x := by
  induction d generalizing x with
  | zero =>
    have h_sup : ⨆ s, dyadicValue (approx s x []) s = a x := H_sup x []
    rw [← h_sup]
    exact le_iSup (fun s => dyadicValue (approx s x []) s) s
  | succ d ih =>
    rw [simpleApproxClosure, dyadicValue_max]
    apply max_le
    · have h_sup : ⨆ s, dyadicValue (approx s x []) s = a x := H_sup x []
      rw [← h_sup]
      exact le_iSup (fun s => dyadicValue (approx s x []) s) s
    · rw [dyadicValue_add (simpleApproxClosure approx s d (x ++ [false]))
        (simpleApproxClosure approx s d (x ++ [true])) s]
      have ih1 := ih (x ++ [false])
        (by simp only [List.length_append, List.length_singleton]; omega)
      have ih2 := ih (x ++ [true]) (by simp only [List.length_append, List.length_singleton]; omega)
      have step1 : dyadicValue (simpleApproxClosure approx s d (x ++ [false])) s
          + dyadicValue (simpleApproxClosure approx s d (x ++ [true])) s
          ≤ a (x ++ [false]) + a (x ++ [true]) := add_le_add (α := ℝ≥0∞) ih1 ih2
      have step2 : a (x ++ [false]) + a (x ++ [true]) ≤ a x := ha.2 x
      exact le_trans step1 step2

/-- The simple approximation never exceeds the semimeasure it approximates. -/
lemma simpleApprox_le_target (a : BitString → ℝ≥0∞) (approx : ℕ → BitString → BitString → ℕ)
    (H_sup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = a out)
    (ha : IsContinuousTreeSemimeasure a) (s : ℕ) (x : BitString) :
    dyadicValue (simpleApprox approx s x) s ≤ a x := by
  unfold simpleApprox
  split_ifs with h1 h2
  · have h0 : dyadicValue 0 s = 0 := by simp [dyadicValue]
    rw [h0]
    exact zero_le _
  · rw [h2]
    have h_root : dyadicValue (2 ^ s) s = 1 := by
      unfold dyadicValue
      have h4 : ((2 ^ s : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ s := by simp
      rw [h4]
      exact ENNReal.div_self (by simp) (by simp)
    rw [h_root]
    exact le_of_eq ha.1.symm
  · exact simpleApproxClosure_le_target a approx H_sup ha s _ x rfl

/-- The dyadic value of `2 ^ s` at precision `s` is one. -/
lemma dyadicValue_two_pow_self (s : ℕ) : dyadicValue (2 ^ s) s = 1 :=
  dyadicValue_two_pow_eq_one s

/-- A numerator with dyadic value at most one is at most `2 ^ s`. -/
lemma le_two_pow_of_dyadicValue_le_one {n s : ℕ} (h : dyadicValue n s ≤ 1) : n ≤ 2 ^ s := by
  unfold dyadicValue at h
  have h3 : (n : ℝ≥0∞) ≤ 1 * (2 : ℝ≥0∞) ^ s :=
    (ENNReal.div_le_iff_le_mul (Or.inl (by simp)) (Or.inr (by simp))).mp h
  rw [one_mul] at h3
  exact_mod_cast h3

/-- Away from the root and above the frontier, `simpleApprox` is the closure value. -/
lemma simpleApprox_eq_closure (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString)
    (hne : x ≠ []) (hx : x.length ≤ s) :
    simpleApprox approx s x = simpleApproxClosure approx s (s - x.length) x := by
  unfold simpleApprox
  rw [if_neg (by omega), if_neg hne]

/-- The closure value is monotone in the depth budget. -/
lemma simpleApproxClosure_mono_depth (approx : ℕ → BitString → BitString → ℕ) (s d : ℕ)
    (x : BitString) :
    simpleApproxClosure approx s d x ≤ simpleApproxClosure approx s (d + 1) x := by
  induction d generalizing x with
  | zero => exact Nat.le_max_left _ _
  | succ d ih =>
    rw [simpleApproxClosure, simpleApproxClosure]
    exact max_le_max le_rfl (Nat.add_le_add (ih _) (ih _))

/-- The closure is monotone in its depth budget. -/
lemma simpleApproxClosure_mono_depth_le (approx : ℕ → BitString → BitString → ℕ) (s : ℕ)
    {d e : ℕ} (hde : d ≤ e) (x : BitString) :
    simpleApproxClosure approx s d x ≤ simpleApproxClosure approx s e x := by
  induction e, hde using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (simpleApproxClosure_mono_depth approx s n x)

/-- Stage monotonicity transfers from the raw approximation to the closure. -/
lemma simpleApproxClosure_stage_mono (approx : ℕ → BitString → BitString → ℕ)
    (H_mono : ∀ s out ctx,
      dyadicValue (approx s out ctx) s ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (s d : ℕ) (x : BitString) :
    dyadicValue (simpleApproxClosure approx s d x) s ≤
      dyadicValue (simpleApproxClosure approx (s + 1) d x) (s + 1) := by
  induction d generalizing x with
  | zero => exact H_mono s x []
  | succ d ih =>
    rw [simpleApproxClosure, simpleApproxClosure, dyadicValue_max, dyadicValue_max]
    refine max_le (le_trans (H_mono s x []) (le_max_left _ _)) ?_
    rw [dyadicValue_add, dyadicValue_add]
    exact le_trans (add_le_add (ih _) (ih _)) (le_max_right _ _)

/-- Stage values of the raw approximation are monotone along `≤`. -/
lemma approx_dyadic_mono_le (approx : ℕ → BitString → BitString → ℕ)
    (H_mono : ∀ s out ctx,
      dyadicValue (approx s out ctx) s ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (out ctx : BitString) {s t : ℕ} (h : s ≤ t) :
    dyadicValue (approx s out ctx) s ≤ dyadicValue (approx t out ctx) t := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (H_mono n out ctx)

/-- The simple approximation is supermultiplicative over the two children. -/
lemma simpleApprox_coherent (a : BitString → ℝ≥0∞) (approx : ℕ → BitString → BitString → ℕ)
    (H_sup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = a out)
    (ha : IsContinuousTreeSemimeasure a) (s : ℕ) (x : BitString) :
    simpleApprox approx s (x ++ [false]) + simpleApprox approx s (x ++ [true])
      ≤ simpleApprox approx s x := by
  have hlenf : (x ++ [false]).length = x.length + 1 := by simp
  have hlent : (x ++ [true]).length = x.length + 1 := by simp
  have hnef : x ++ [false] ≠ [] := by simp
  have hnet : x ++ [true] ≠ [] := by simp
  by_cases hlen : s < x.length + 1
  · have hf : simpleApprox approx s (x ++ [false]) = 0 :=
      simpleApprox_vanishes_below_frontier approx s _ (by omega)
    have ht : simpleApprox approx s (x ++ [true]) = 0 :=
      simpleApprox_vanishes_below_frontier approx s _ (by omega)
    simp [hf, ht]
  · push_neg at hlen
    have hcf : simpleApprox approx s (x ++ [false])
        = simpleApproxClosure approx s (s - (x.length + 1)) (x ++ [false]) := by
      rw [simpleApprox_eq_closure approx s _ hnef (by omega), hlenf]
    have hct : simpleApprox approx s (x ++ [true])
        = simpleApproxClosure approx s (s - (x.length + 1)) (x ++ [true]) := by
      rw [simpleApprox_eq_closure approx s _ hnet (by omega), hlent]
    rw [hcf, hct]
    by_cases hx : x = []
    · subst hx
      have hroot : simpleApprox approx s ([] : BitString) = 2 ^ s := simpleApprox_root approx s
      rw [hroot]
      set d := s - (([] : BitString).length + 1) with hd
      have hbf : dyadicValue (simpleApproxClosure approx s d ([] ++ [false])) s
          ≤ a ([] ++ [false]) :=
        simpleApproxClosure_le_target a approx H_sup ha s d _ (by simp [hd])
      have hbt : dyadicValue (simpleApproxClosure approx s d ([] ++ [true])) s ≤ a ([] ++ [true]) :=
        simpleApproxClosure_le_target a approx H_sup ha s d _ (by simp [hd])
      have hsum : dyadicValue (simpleApproxClosure approx s d ([] ++ [false])
          + simpleApproxClosure approx s d ([] ++ [true])) s ≤ 1 := by
        rw [dyadicValue_add]
        refine le_trans (add_le_add (α := ℝ≥0∞) hbf hbt) ?_
        refine le_trans (ha.2 []) ?_
        exact le_of_eq ha.1
      exact le_two_pow_of_dyadicValue_le_one hsum
    · rw [simpleApprox_eq_closure approx s x hx (by omega)]
      have hd : s - x.length = (s - (x.length + 1)) + 1 := by omega
      rw [hd]
      exact simpleApproxClosure_coherent approx s _ x

/-- The dyadic values of the simple approximation are non-decreasing in the stage. -/
lemma simpleApprox_stage_mono (approx : ℕ → BitString → BitString → ℕ)
    (H_mono : ∀ s out ctx,
      dyadicValue (approx s out ctx) s ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (s : ℕ) (x : BitString) :
    dyadicValue (simpleApprox approx s x) s ≤
      dyadicValue (simpleApprox approx (s + 1) x) (s + 1) := by
  by_cases hlen : s < x.length
  · rw [simpleApprox_vanishes_below_frontier approx s x hlen, dyadicValue_zero]
    exact zero_le _
  · push_neg at hlen
    by_cases hx : x = []
    · subst hx
      rw [simpleApprox_root approx s, simpleApprox_root approx (s + 1),
        dyadicValue_two_pow_self, dyadicValue_two_pow_self]
    · rw [simpleApprox_eq_closure approx s x hx hlen,
        simpleApprox_eq_closure approx (s + 1) x hx (by omega)]
      refine le_trans (simpleApproxClosure_stage_mono approx H_mono s (s - x.length) x) ?_
      exact dyadicValue_le _ _ _
        (simpleApproxClosure_mono_depth_le approx (s + 1) (by omega) x)

/-- The simple approximation converges to the same semimeasure as the raw one. -/
lemma iSup_simpleApprox_eq (a : BitString → ℝ≥0∞) (approx : ℕ → BitString → BitString → ℕ)
    (H_mono : ∀ s out ctx,
      dyadicValue (approx s out ctx) s ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (H_sup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = a out)
    (ha : IsContinuousTreeSemimeasure a) (x : BitString) :
    ⨆ s, dyadicValue (simpleApprox approx s x) s = a x := by
  refine le_antisymm (iSup_le fun s => simpleApprox_le_target a approx H_sup ha s x) ?_
  rw [← H_sup x []]
  refine iSup_le fun s => ?_
  set t := max s x.length with hts
  have h1 : dyadicValue (approx s x []) s ≤ dyadicValue (approx t x []) t :=
    approx_dyadic_mono_le approx H_mono x [] (le_max_left _ _)
  have h2 : dyadicValue (approx t x []) t ≤ dyadicValue (simpleApprox approx t x) t :=
    dyadicValue_le _ _ _ (simpleApprox_raw_le a approx H_sup ha t x (le_max_right _ _))
  exact le_trans (le_trans h1 h2) (le_iSup (fun t => dyadicValue (simpleApprox approx t x) t) t)

end Lemmas

/-- At every stage, the dyadic values of a simple approximation form a
continuous tree semimeasure. -/
theorem IsSimpleTreeApproximation.stage_isContinuousTreeSemimeasure
    {a : BitString → ℝ≥0∞} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (s : ℕ) :
    IsContinuousTreeSemimeasure (fun x => dyadicValue (q s x) s) := by
  constructor
  · change dyadicValue (q s []) s = 1
    rw [hq.1 s, dyadicValue_two_pow_self]
  · intro x
    rw [← dyadicValue_add]
    exact dyadicValue_le _ _ _ (hq.2.1 s x)

/-- A simple approximation has finite support at every stage. -/
theorem IsSimpleTreeApproximation.finite_support
    {a : BitString → ℝ≥0∞} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (s : ℕ) :
    Set.Finite {x | q s x ≠ 0} := by
  refine ((boundedPrograms s).toFinset.finite_toSet).subset ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  change x ∈ (boundedPrograms s).toFinset
  apply List.mem_toFinset.mpr
  apply (mem_boundedPrograms_iff x s).mpr
  by_contra hlen
  exact hx (hq.2.2.1 s x (Nat.lt_of_not_ge hlen))

/-! ### A bottom-up, level-by-level evaluation of `simpleApproxClosure`

`simpleApproxClosure` is a binary-tree recursion: the value at `x` with depth
budget `d + 1` needs the values at the two children with budget `d`.  To evaluate
it by a `Nat.rec` loop (the shape `Computable.nat_rec` supports) we compute whole
levels of the tree at once, bottom-up: `closureLevel approx s x d j` is the list
of the `2 ^ (d - j)` values `simpleApproxClosure approx s j (x ++ y)`, indexed by
the binary expansions `y = simpleApproxBits (d - j) i`.  One level step is
`levelStep`. -/

/-- One bottom-up level step: from the list of values of the children level,
compute the list of values of the parent level (of length `2 ^ k`). -/
def levelStep (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString) (k : ℕ)
  (prev : List ℕ) : List ℕ :=
  (List.range (2 ^ k)).map (fun i =>
    max (approx s (x ++ simpleApproxBits k i) [])
      (prev.getD (2 * i) 0 + prev.getD (2 * i + 1) 0))

/-- `closureLevel approx s x d j` is the list of stage-`s` closure values with
depth budget `j`, over all descendants of `x` at depth `d - j`. -/
def closureLevel (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString) (d : ℕ) :
    ℕ → List ℕ
  | 0 => levelStep approx s x d []
  | j + 1 => levelStep approx s x (d - (j + 1)) (closureLevel approx s x d j)

/-- The level list holds the closure values with budget `j` over all descendants at depth
`d - j`. -/
lemma closureLevel_eq (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString) (d : ℕ) :
    ∀ j, j ≤ d → closureLevel approx s x d j
      = (List.range (2 ^ (d - j))).map
          (fun i => simpleApproxClosure approx s j (x ++ simpleApproxBits (d - j) i)) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [closureLevel, levelStep, simpleApproxClosure]
  | succ j ih =>
    intro hj
    have hk : d - j = (d - (j + 1)) + 1 := by omega
    rw [closureLevel, ih (by omega), hk]
    set k := d - (j + 1) with hkdef
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i < 2 ^ k := by simpa using hi
    have hle : 2 * i + 1 < 2 ^ (k + 1) := by
      have : 2 * i + 2 ≤ 2 * 2 ^ k := by omega
      simpa [pow_succ, Nat.mul_comm] using by omega
    have hleft := getD_range_map (2 ^ (k + 1))
      (fun m => simpleApproxClosure approx s j (x ++ simpleApproxBits (k + 1) m))
      (2 * i) 0 (by omega)
    have hright := getD_range_map (2 ^ (k + 1))
      (fun m => simpleApproxClosure approx s j (x ++ simpleApproxBits (k + 1) m))
      (2 * i + 1) 0 hle
    rw [hleft, hright]
    simp only [simpleApproxBits_left, simpleApproxBits_right, ← List.append_assoc]
    rfl

/-- At full budget the level list holds a single entry, the closure at the node itself. -/
lemma closureLevel_getD (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString)
    (d : ℕ) : (closureLevel approx s x d d).getD 0 0 = simpleApproxClosure approx s d x := by
  rw [closureLevel_eq approx s x d d le_rfl]
  simp

/-- The level list, written as a plain recursion, which is the shape the computability proof
consumes. -/
lemma closureLevel_rec (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString)
    (d j : ℕ) :
    closureLevel approx s x d j
      = Nat.rec (motive := fun _ => List ℕ) (levelStep approx s x d [])
          (fun y IH => levelStep approx s x (d - (y + 1)) IH) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [closureLevel, ih]

/-- `simpleApprox` written with `cond` on decidable tests: the form used in the
computability proof. -/
lemma simpleApprox_eq_cond (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString) :
    simpleApprox approx s x =
      cond (decide (s < x.length)) 0
        (cond (decide (x.length = 0)) (2 ^ s)
          ((closureLevel approx s x (s - x.length) (s - x.length)).getD 0 0)) := by
  unfold simpleApprox
  by_cases h1 : s < x.length
  · simp [h1]
  · by_cases h2 : x = []
    · subst h2; simp
    · have h3 : x.length ≠ 0 := by simpa [List.length_eq_zero_iff] using h2
      simp only [gt_iff_lt, if_neg h1, if_neg h2, decide_eq_false_iff_not.mpr h1,
        decide_eq_false_iff_not.mpr h3, Bool.cond_false]
      exact (closureLevel_getD approx s x (s - x.length)).symm

/-! ### Computability of `simpleApprox`

The `Computable` combinators are elaborated by unfolding `Primcodable` instances,
which is very expensive on deeply nested product types and on the concrete
definitions above; the parameters `(s, k, x)` are therefore packed into a single
natural-number code, and the definitions are made locally irreducible (all facts
about them that are still needed are already available as lemmas). -/

attribute [local irreducible] simpleApproxBits levelStep closureLevel simpleApprox

open Encodable

/-- Code for the parameter triple `(s, k, x)`. -/
def paramCode (s k : ℕ) (x : BitString) : ℕ := Nat.pair (Nat.pair s k) (encode x)
/-- The stage component of a parameter code. -/
def paramS (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair c).1).1
/-- The depth component of a parameter code. -/
def paramK (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair c).1).2
/-- The node component of a parameter code. -/
def paramX (c : ℕ) : BitString := ((decode (α := BitString) (Nat.unpair c).2)).getD []
/-- Replace the `k` component of a parameter code. -/
def paramRecode (c k : ℕ) : ℕ := Nat.pair (Nat.pair (paramS c) k) (Nat.unpair c).2

/-- The stage read back from a parameter code is the stage it was built from. -/
@[simp] lemma paramS_code (s k : ℕ) (x : BitString) : paramS (paramCode s k x) = s := by
  simp [paramS, paramCode]
/-- The depth read back from a parameter code is the depth it was built from. -/
@[simp] lemma paramK_code (s k : ℕ) (x : BitString) : paramK (paramCode s k x) = k := by
  simp [paramK, paramCode]
/-- The node read back from a parameter code is the node it was built from. -/
@[simp] lemma paramX_code (s k : ℕ) (x : BitString) : paramX (paramCode s k x) = x := by
  simp [paramX, paramCode]
/-- Replacing the depth leaves the stage unchanged. -/
@[simp] lemma paramS_recode (c k : ℕ) : paramS (paramRecode c k) = paramS c := by
  simp [paramS, paramRecode]
/-- Replacing the depth installs the new depth. -/
@[simp] lemma paramK_recode (c k : ℕ) : paramK (paramRecode c k) = k := by
  simp [paramK, paramRecode]
/-- Replacing the depth leaves the node unchanged. -/
@[simp] lemma paramX_recode (c k : ℕ) : paramX (paramRecode c k) = paramX c := by
  simp [paramX, paramRecode]

/-- The stage component of a parameter code is computable. -/
lemma computable_paramS : Computable paramS :=
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp
/-- The depth component of a parameter code is computable. -/
lemma computable_paramK : Computable paramK :=
  (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp
/-- The node component of a parameter code is computable. -/
lemma computable_paramX : Computable paramX :=
  Computable.option_getD (Computable.decode.comp (Primrec.snd.comp Primrec.unpair).to_comp)
    (Computable.const [])
/-- Replacing the depth in a parameter code is computable. -/
lemma computable_paramRecode : Computable (fun p : ℕ × ℕ => paramRecode p.1 p.2) :=
  Primrec₂.natPair.to_comp.comp
    (Primrec₂.natPair.to_comp.comp (computable_paramS.comp Computable.fst) Computable.snd)
    ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst)

/-- Building a parameter code is computable. -/
lemma computable_paramCode :
    Computable (fun q : (ℕ × ℕ) × BitString => paramCode q.1.1 q.1.2 q.2) :=
  Primrec₂.natPair.to_comp.comp
    (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst))
    (Primrec.encode.to_comp.comp Computable.snd)

attribute [local irreducible] paramS paramK paramX paramRecode paramCode

/-- The raw approximation, read at the descendant indexed by a parameter code, is computable. -/
lemma computable_approxC (approx : ℕ → BitString → BitString → ℕ)
    (h_comp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun q : ℕ × ℕ =>
      approx (paramS q.1) (paramX q.1 ++ simpleApproxBits (paramK q.1) q.2) []) := by
  have hbi : Computable (fun q : ℕ × ℕ => simpleApproxBits (paramK q.1) q.2) :=
    computable_simpleApproxBits.comp
      (Computable.pair (computable_paramK.comp Computable.fst) Computable.snd)
  exact h_comp.comp (Computable.pair (computable_paramS.comp Computable.fst)
    (Computable.pair
      (Computable.list_append.comp (computable_paramX.comp Computable.fst) hbi)
      (Computable.const [])))

/-- One level step of the closure evaluator is computable. -/
lemma computable_levelStepC (approx : ℕ → BitString → BitString → ℕ)
    (h_comp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun q : ℕ × List ℕ =>
      levelStep approx (paramS q.1) (paramX q.1) (paramK q.1) q.2) := by
  have hc : Computable (fun p : (ℕ × List ℕ) × ℕ => p.1.1) := Computable.fst.comp Computable.fst
  have hprev : Computable (fun p : (ℕ × List ℕ) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hi : Computable (fun p : (ℕ × List ℕ) × ℕ => p.2) := Computable.snd
  have hmain : Computable (fun q : ℕ × List ℕ =>
      (List.range (2 ^ paramK q.1)).map (fun i =>
        max (approx (paramS q.1) (paramX q.1 ++ simpleApproxBits (paramK q.1) i) [])
          (q.2.getD (2 * i) 0 + q.2.getD (2 * i + 1) 0))) := by
    refine computable_range_map _ _ ?_ ?_
    · exact primrec_two_pow_aux.to_comp.comp (computable_paramK.comp Computable.fst)
    · have hbi : Computable (fun p : (ℕ × List ℕ) × ℕ =>
          simpleApproxBits (paramK p.1.1) p.2) :=
        computable_simpleApproxBits.comp
          (Computable.pair (computable_paramK.comp hc) hi)
      have happrox : Computable (fun p : (ℕ × List ℕ) × ℕ =>
          approx (paramS p.1.1)
            (paramX p.1.1 ++ simpleApproxBits (paramK p.1.1) p.2) []) :=
        h_comp.comp (Computable.pair (computable_paramS.comp hc)
          (Computable.pair
            (Computable.list_append.comp (computable_paramX.comp hc) hbi)
            (Computable.const [])))
      have h2i : Computable (fun p : (ℕ × List ℕ) × ℕ => 2 * p.2) :=
        Primrec.nat_mul.to_comp.comp (Computable.const 2) hi
      have hgetD : Computable₂ (fun (l : List ℕ) (n : ℕ) => l.getD n 0) :=
        (Primrec.list_getD (0 : ℕ)).to_comp
      have hsum : Computable (fun p : (ℕ × List ℕ) × ℕ =>
          p.1.2.getD (2 * p.2) 0 + p.1.2.getD (2 * p.2 + 1) 0) :=
        Primrec.nat_add.to_comp.comp (hgetD.comp hprev h2i)
          (hgetD.comp hprev (Computable.succ.comp h2i))
      exact Primrec.nat_max.to_comp.comp happrox hsum
  exact hmain.of_eq (fun q => by rw [levelStep])

/-- The level list of the closure evaluator is computable. -/
lemma computable_closureLevelC (approx : ℕ → BitString → BitString → ℕ)
    (h_comp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun a : ℕ × ℕ =>
      closureLevel approx (paramS a.1) (paramX a.1) (paramK a.1) a.2) := by
  have hstepC := computable_levelStepC approx h_comp
  have hbase : Computable (fun a : ℕ × ℕ =>
      levelStep approx (paramS a.1) (paramX a.1) (paramK a.1) []) :=
    hstepC.comp (Computable.pair Computable.fst (Computable.const []))
  have hstep : Computable (fun q : (ℕ × ℕ) × (ℕ × List ℕ) =>
      levelStep approx (paramS q.1.1) (paramX q.1.1) (paramK q.1.1 - (q.2.1 + 1)) q.2.2) := by
    have hcode : Computable (fun q : (ℕ × ℕ) × (ℕ × List ℕ) =>
        paramRecode q.1.1 (paramK q.1.1 - (q.2.1 + 1))) :=
      computable_paramRecode.comp (Computable.pair
        (Computable.fst.comp Computable.fst)
        (Primrec.nat_sub.to_comp.comp
          (computable_paramK.comp (Computable.fst.comp Computable.fst))
          (Computable.succ.comp (Computable.fst.comp Computable.snd))))
    exact (hstepC.comp (Computable.pair hcode
      (Computable.snd.comp Computable.snd))).of_eq (fun q => by simp)
  exact (Computable.nat_rec Computable.snd hbase hstep.to₂).of_eq
    (fun a => (closureLevel_rec approx (paramS a.1) (paramX a.1) (paramK a.1) a.2).symm)

/-- The simple approximation of a computable raw approximation is computable. -/
lemma computable_simpleApprox (approx : ℕ → BitString → BitString → ℕ)
    (h_comp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString => simpleApprox approx p.1 p.2) := by
  have hlen : Computable (fun p : ℕ × BitString => p.2.length) :=
    Computable.list_length.comp Computable.snd
  have hd : Computable (fun p : ℕ × BitString => p.1 - p.2.length) :=
    Primrec.nat_sub.to_comp.comp Computable.fst hlen
  have hcode : Computable (fun p : ℕ × BitString =>
      paramCode p.1 (p.1 - p.2.length) p.2) :=
    computable_paramCode.comp (Computable.pair (Computable.pair Computable.fst hd)
      Computable.snd)
  have hlevel : Computable (fun p : ℕ × BitString =>
      closureLevel approx p.1 p.2 (p.1 - p.2.length) (p.1 - p.2.length)) :=
    ((computable_closureLevelC approx h_comp).comp
      (Computable.pair hcode hd)).of_eq (fun p => by simp)
  have hval : Computable (fun p : ℕ × BitString =>
      (closureLevel approx p.1 p.2 (p.1 - p.2.length) (p.1 - p.2.length)).getD 0 0) :=
    (Primrec.list_getD (0 : ℕ)).to_comp.comp hlevel (Computable.const 0)
  have hc1 : Computable (fun p : ℕ × BitString => decide (p.1 < p.2.length)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.fst hlen
  have hc2 : Computable (fun p : ℕ × BitString => decide (p.2.length = 0)) :=
    (PrimrecRel.decide (Primrec.eq (α := ℕ))).to_comp.comp hlen (Computable.const 0)
  have hpow : Computable (fun p : ℕ × BitString => 2 ^ p.1) :=
    primrec_two_pow_aux.to_comp.comp Computable.fst
  exact (Computable.cond hc1 (Computable.const 0)
    (Computable.cond hc2 hpow hval)).of_eq
    (fun p => (simpleApprox_eq_cond approx p.1 p.2).symm)


/-- Every lower-semicomputable continuous tree semimeasure admits a *simple tree
approximation*: a computable, stagewise-monotone family of integer numerators
that is coherent under the tree-semimeasure inequality and converges to `a`.

The hypothesis `h1 : a [] = 1` is part of `IsContinuousTreeSemimeasure`, so it is
logically redundant; retaining it makes the source normalization used by this
construction explicit. -/
theorem exists_simpleTreeApproximation {a : BitString → ℝ≥0∞}
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (h1 : a [] = 1) :
    ∃ q, IsSimpleTreeApproximation a q := by
  obtain ⟨hcont, approx, H_mono, H_sup, h_comp⟩ := ha
  have hcont' : IsContinuousTreeSemimeasure a := ⟨h1, hcont.2⟩
  exact ⟨simpleApprox approx, simpleApprox_root approx,
    fun s x => simpleApprox_coherent a approx H_sup hcont' s x,
    fun s x hx => simpleApprox_vanishes_below_frontier approx s x hx,
    fun s x => simpleApprox_stage_mono approx H_mono s x,
    fun x => iSup_simpleApprox_eq a approx H_mono H_sup hcont' x,
    computable_simpleApprox approx h_comp⟩

end Kolmogorov
