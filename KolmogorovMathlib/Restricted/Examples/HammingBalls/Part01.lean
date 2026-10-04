import KolmogorovMathlib.Restricted.GreedyCover
import Mathlib.Data.Nat.Choose.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.Restricted.Family
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Logic.Equiv.Fintype

/-!
# Hamming distance and the volume of Hamming balls
Defines Hamming distance on bitstrings and proves its metric laws at a fixed length. It also
computes the sizes and covering degrees of Hamming spheres and balls, supplying the finite
combinatorics used by the greedy-cover construction.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Hamming distance between two bitstrings. Useful mostly for strings of the same length. -/
def hammingDist (x y : BitString) : ℕ :=
  ((x.zip y).filter (fun (a, b) => a ≠ b)).length

/-- A string is at Hamming distance `0` from itself. -/
theorem hammingDist_self (x : BitString) : hammingDist x x = 0 := by
  unfold hammingDist
  have hfilter : ((x.zip x).filter (fun (a, b) => a ≠ b)) = [] := by
    induction x with
    | nil => rfl
    | cons b xs ih =>
        rw [List.zip_cons_cons, List.filter_cons_of_neg]
        · exact ih
        · simp
  rw [hfilter]
  rfl

/-- The Hamming distance is bounded by the length of the second argument. -/
theorem hammingDist_le_right_length (x y : BitString) :
    hammingDist x y ≤ y.length := by
  unfold hammingDist
  calc
    ((x.zip y).filter (fun (a, b) => a ≠ b)).length ≤ (x.zip y).length :=
      List.length_filter_le _ _
    _ = min x.length y.length := List.length_zip
    _ ≤ y.length := Nat.min_le_right _ _

/-- The Hamming distance of two strings with a leading bit each is the distance of the tails plus
one if the leading bits differ. -/
theorem hammingDist_cons (b c : Bool) (xs ys : BitString) :
    hammingDist (b :: xs) (c :: ys) = (if b = c then 0 else 1) + hammingDist xs ys := by
  unfold hammingDist
  rw [List.zip_cons_cons]
  by_cases h : b = c
  · rw [List.filter_cons_of_neg, ite_eq_left h]
    · simp
    · simp [h]
  · rw [List.filter_cons_of_pos, ite_eq_right h]
    · simp [List.length_cons]; ring
    · simp [h]

/-- The Hamming distance is symmetric. -/
theorem hammingDist_comm (x y : BitString) : hammingDist x y = hammingDist y x := by
  unfold hammingDist
  rw [← List.zip_swap y x, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro a _
  rcases a with ⟨p, q⟩
  simp only [Function.comp_apply, Prod.swap_prod_mk, ne_eq, decide_not, eq_comm]

/-- Triangle inequality for Hamming distance on equal-length bitstrings. -/
theorem hammingDist_triangle_of_eq_length (x y z : BitString)
    (hxy : x.length = y.length) (hyz : y.length = z.length) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  induction x generalizing y z with
  | nil =>
      cases y with
      | nil =>
          cases z with
          | nil => simp [hammingDist]
          | cons c zs => simp at hyz
      | cons b ys => simp at hxy
  | cons a xs ih =>
      cases y with
      | nil => simp at hxy
      | cons b ys =>
          cases z with
          | nil => simp at hyz
          | cons c zs =>
              simp only [List.length_cons] at hxy hyz
              have hxy' : xs.length = ys.length := Nat.succ.inj hxy
              have hyz' : ys.length = zs.length := Nat.succ.inj hyz
              have ih' := ih ys zs hxy' hyz'
              rw [hammingDist_cons, hammingDist_cons, hammingDist_cons]
              have hbit :
                  (if a = c then 0 else 1) ≤
                    (if a = b then 0 else 1) + (if b = c then 0 else 1) := by
                cases a <;> cases b <;> cases c <;> decide
              omega

/-- `hammingBall n x r` is the set of all strings of length `n` at Hamming distance `≤ r` from
`x`. -/
def hammingBall (n : ℕ) (x : BitString) (r : ℕ) : Finset BitString :=
  (stringsOfLength n).filter (fun y => hammingDist x y ≤ r)

/-- The Hamming ball is the finite set obtained by filtering all strings of length `n` by the
distance condition. -/
theorem hammingBall_eq_toFinset (n : ℕ) (x : BitString) (r : ℕ) :
    hammingBall n x r = ((allStrings n).filter (fun y =>
        decide (hammingDist x y ≤ r))).toFinset := by
  unfold hammingBall stringsOfLength
  rw [List.toFinset_filter]
  apply Finset.filter_congr
  intro y _
  simp

/-- The Hamming family consists of all Hamming balls. -/
def hammingFamilyMem (A : Finset BitString) : Prop :=
  ∃ n x r, x.length = n ∧ A = hammingBall n x r

/-- A member of the Hamming-ball family is non-empty, since it contains its own centre. -/
theorem hammingFamilyMem_nonempty {A : Finset BitString} (h : hammingFamilyMem A) : A.Nonempty := by
  rcases h with ⟨n, x, r, hlen, rfl⟩
  refine ⟨x, ?_⟩
  rw [hammingBall, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [mem_stringsOfLength]
    exact hlen
  · simp [hammingDist_self]

/-- The volume of a Hamming ball of radius `r` in `{0,1}^n`. -/
def hammingVol (n r : ℕ) : ℕ :=
  (Finset.range (r + 1)).sum (fun s => Nat.choose n s)

/-
Pascal-style recurrence for Hamming volumes.
-/
theorem hammingVol_succ (n r : ℕ) :
    hammingVol (n + 1) (r + 1) = hammingVol n (r + 1) + hammingVol n r := by
  unfold hammingVol;
  induction r <;> simp_all [ Nat.choose_succ_succ, Finset.sum_range_succ' ]
  · ring
  · simp_all [ Finset.sum_add_distrib ] ; linarith

/-
Ball cardinality as a binomial sum.
-/
theorem hammingBall_card (n : ℕ) (x : BitString) (r : ℕ) (hx : x.length = n) :
    (hammingBall n x r).card = hammingVol n r := by
  subst hx;
  induction x generalizing r <;> simp_all only [List.length_nil, hammingVol, List.length_cons];
  · unfold hammingBall;
    unfold hammingDist; simp +decide [ Finset.sum_range_succ' ] ;
  · rename_i k hk ih; rcases r with ( _ | r ) <;> simp_all only [Finset.sum_range_succ',
      Nat.choose_zero_right, zero_add, Finset.range_one, Finset.sum_singleton,
      Nat.choose_succ_succ, Nat.succ_eq_add_one, Nat.choose_one_right] ;
    · refine Finset.card_eq_one.mpr ?_;
      use k :: hk; ext; simp only [hammingBall, nonpos_iff_eq_zero, Finset.mem_filter,
        Finset.mem_singleton];
      constructor <;> intro h <;>
        simp_all only [stringsOfLength, List.mem_toFinset, mem_allStrings, List.length_cons,
          hammingDist_self, and_self];
      have h_eq : ∀ {x y : BitString}, x.length = y.length → hammingDist x y = 0 → x = y := by
        intros x y hxy h; induction x generalizing y <;> induction y <;> simp_all [ hammingDist ] ;
        grind;
      exact h_eq ( by simp [ h.1 ] ) h.2 ▸ rfl;
    · -- Let's simplify the goal using the definition of `hammingBall`.
      have h_simp : hammingBall (hk.length + 1) (k :: hk) (r + 1) = Finset.image (fun y =>
          k :: y) (hammingBall hk.length hk (r + 1)) ∪ Finset.image (fun y => (!k) :: y)
            (hammingBall hk.length hk r) := by
        ext y; simp only [hammingBall, Finset.mem_filter, Finset.mem_union, Finset.mem_image];
        rcases y with ( _ | ⟨ b, y ⟩ ) <;> simp_all only [stringsOfLength, List.mem_toFinset,
            mem_allStrings, List.length_nil, Nat.right_eq_add, Nat.add_eq_zero_iff,
            List.length_eq_zero_iff, one_ne_zero, and_false, false_and, reduceCtorEq, exists_const,
            or_self, List.length_cons, Nat.add_right_cancel_iff, List.cons.injEq,
            exists_eq_right_right, Bool.not_eq_eq_eq_not];
        cases k <;> cases b <;> simp_all only [hammingDist_cons, ↓reduceIte, zero_add, and_true,
            Bool.not_false, Bool.false_eq_true, and_false, or_false, Bool.not_true, false_or,
            and_congr_right_iff, Bool.true_eq_false]; all_goals exact fun _ =>
            ⟨ fun h => by linarith, fun h => by linarith ⟩;
      rw [ h_simp, Finset.card_union_of_disjoint ];
      · rw [ Finset.card_image_of_injective,
          Finset.card_image_of_injective ] <;> simp_all [ Function.Injective ];
        simp +arith [ Finset.sum_add_distrib, Finset.sum_range_succ' ];
      · norm_num [ Finset.disjoint_left ]

/-- Full-cube stress test. -/
theorem hammingFamily_fullCube (n : ℕ) : hammingFamilyMem (stringsOfLength n) := by
  use n, List.replicate n false, n
  refine ⟨by simp, ?_⟩
  ext y
  simp only [hammingBall, Finset.mem_filter, iff_self_and]
  intro h
  have hylen : y.length = n := (mem_stringsOfLength n y).mp h
  simpa [hylen] using hammingDist_le_right_length (List.replicate n false) y

/-- Radius-growth polynomial bound for Hamming volumes. -/
theorem hammingVol_growth (n r : ℕ) :
    hammingVol n (r + 1) ≤ (n + 1) * hammingVol n r := by
  have hterm : Nat.choose n (r + 1) ≤ n * hammingVol n r := by
    have hchoose_le_vol : Nat.choose n r ≤ hammingVol n r := by
      unfold hammingVol
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_self r))
    calc
      Nat.choose n (r + 1) ≤ Nat.choose n (r + 1) * (r + 1) :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos r)
      _ = Nat.choose n r * (n - r) := Nat.choose_succ_right_eq n r
      _ ≤ Nat.choose n r * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ hammingVol n r * n := Nat.mul_le_mul_right _ hchoose_le_vol
      _ = n * hammingVol n r := Nat.mul_comm _ _
  unfold hammingVol
  rw [Finset.sum_range_succ, Nat.add_one_mul]
  calc
    (∑ x ∈ Finset.range (r + 1), Nat.choose n x) + Nat.choose n (r + 1)
        ≤ (∑ x ∈ Finset.range (r + 1), Nat.choose n x) +
            n * (∑ s ∈ Finset.range (r + 1), Nat.choose n s) := by
          exact Nat.add_le_add_left hterm _
    _ = n * (∑ s ∈ Finset.range (r + 1), Nat.choose n s) +
          ∑ s ∈ Finset.range (r + 1), Nat.choose n s := by omega

/-- Hamming volume is monotone in the radius. -/
theorem hammingVol_mono {n r s : ℕ} (hrs : r ≤ s) :
    hammingVol n r ≤ hammingVol n s := by
  unfold hammingVol
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hrs))

/-- Hamming volumes are nonzero. -/
theorem hammingVol_pos (n r : ℕ) : 0 < hammingVol n r := by
  have hge : 1 ≤ hammingVol n r := by
    unfold hammingVol
    calc
      1 = Nat.choose n 0 := by simp
      _ ≤ (Finset.range (r + 1)).sum (fun s => Nat.choose n s) :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (Nat.succ_pos r))
  omega

/-- Ceiling-division upper bound in the concrete `(a + b - 1) / b` form. -/
lemma add_pred_div_le_of_le_mul {a b q : ℕ} (hb : 0 < b) (h : a ≤ b * q) :
    (a + b - 1) / b ≤ q := by
  rw [Nat.div_le_iff_le_mul_add_pred hb]
  omega

/-- Ceiling-division lower bound in the concrete `(a + b - 1) / b` form. -/
lemma le_mul_add_pred_div {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    a ≤ ((a + b - 1) / b) * b := by
  set q := (a + b - 1) / b
  have hlt : a + b - 1 < (q + 1) * b := by
    have hq : q < q + 1 := Nat.lt_succ_self q
    simpa [q] using (Nat.div_lt_iff_lt_mul hb).mp hq
  rw [Nat.add_one_mul] at hlt
  omega

/-- The ball volume grows strictly with the radius below `min s n`. -/
lemma hammingVol_lt_of_lt_min (n r s : ℕ) (h : r < min s n) :
    hammingVol n r < hammingVol n (min s n) := by
  unfold hammingVol
  have h_split : Finset.range (min s n + 1) =
      Finset.range (r + 1) ∪ Finset.Ico (r + 1) (min s n + 1) := by
    ext a
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h_split, Finset.sum_union]
  · have h_pos : 0 < ∑ x ∈ Finset.Ico (r + 1) (min s n + 1), Nat.choose n x := by
      refine Finset.sum_pos ?_ ?_
      · intro i hi
        have hi2 : i ≤ n := by
          have h1 : i < min s n + 1 := (Finset.mem_Ico.mp hi).2
          omega
        exact Nat.choose_pos hi2
      · rw [Finset.nonempty_Ico]
        omega
    omega
  · apply Finset.disjoint_left.mpr
    intro a ha1 ha2
    rw [Finset.mem_range] at ha1
    rw [Finset.mem_Ico] at ha2
    omega

/-- Below the ambient dimension the ball volume is strictly increasing in the radius. -/
lemma hammingVol_lt_of_lt_of_lt_n {n r s : ℕ} (hrs : r < s) (hrn : r < n) :
    hammingVol n r < hammingVol n s := by
  have hmin : r < min s n := lt_min hrs hrn
  exact lt_of_lt_of_le (hammingVol_lt_of_lt_min n r s hmin)
    (hammingVol_mono (n := n) (Nat.min_le_left s n))

/-- A radius whose ball has at most `c` points is at most a radius `r < n` whose ball has at
least `c` points. -/
lemma hammingRadius_le_of_volume_le {n r r_c c : ℕ}
    (h_rc_vol : hammingVol n r_c ≤ c) (h_r_bound : c ≤ hammingVol n r)
    (hrn : r < n) :
    r_c ≤ r := by
  by_contra hnot
  have hrrc : r < r_c := Nat.lt_of_not_ge hnot
  have hlt : hammingVol n r < hammingVol n r_c :=
    hammingVol_lt_of_lt_of_lt_n hrrc hrn
  exact (not_lt_of_ge (le_trans h_rc_vol h_r_bound)) hlt

/-
Probabilistic covering and counting lemma.
-/
theorem hamming_probabilistic_cover (n r c : ℕ) (hc : 0 < c) (hcn : c ≤ hammingVol n r) :
    ∃ 𝒞 : List BitString,
      (∀ x ∈ 𝒞, x.length = n) ∧
      (∀ y ∈ stringsOfLength n, ∃ x ∈ 𝒞, hammingDist x y ≤ r) ∧
      𝒞.length * c ≤ (n + 1) * (stringsOfLength n).card := by
  convert greedy_cover_indexed ( stringsOfLength n ) ( stringsOfLength n ) ( fun x =>
      ( stringsOfLength n ).filter fun y => hammingDist x y ≤ r ) c hc ?_ using 1;
  · constructor <;> intro h;
    · convert greedy_cover_indexed ( stringsOfLength n ) ( stringsOfLength n ) ( fun x =>
        ( stringsOfLength n ).filter fun y => hammingDist x y ≤ r ) c hc ?_ using 1;
      intro x hx; rw [ show { b ∈ stringsOfLength n | x ∈ { y ∈ stringsOfLength n
          | hammingDist b y ≤ r } } =
            ( stringsOfLength n ).filter ( fun y => hammingDist x y ≤ r ) from ?_ ] ;
      · simpa [hammingBall] using
          (show c ≤ (hammingBall n x r).card by
            simpa [hammingBall_card n x r ((mem_stringsOfLength n x).1 hx)] using hcn)
      · ext y; simp [hammingDist_comm];
        grind;
    · obtain ⟨ C, hC₁, hC₂, hC₃ ⟩ := h; use C.toList; simp_all only [Finset.subset_iff,
        Finset.mem_biUnion, Finset.mem_filter, true_and, Finset.mem_toList, implies_true,
        Finset.length_toList];
      refine ⟨ fun x hx => ?_, ?_ ⟩;
      · exact mem_stringsOfLength n x |>.1 ( hC₁ hx );
      · convert hC₃ using 1;
        rw [ card_stringsOfLength, Nat.log2_two_pow ] ; ring;
  · intro x hx;
    convert hcn using 1;
    convert hammingBall_card n x r ( mem_stringsOfLength n x |>.1 hx ) using 1;
    congr 1 with y ; simp only [Finset.mem_filter, hammingDist_comm];
    unfold hammingBall; aesop;

/-- The covering overhead `(n + 1) ^ 7` of the Hamming-ball family. -/
def hammingOverhead (n : ℕ) : ℕ := (n + 1)^7

/-- The overhead `(n + 1) ^ 7` of the Hamming-ball family is positive. -/
theorem hammingOverhead_pos (n : ℕ) : 0 < hammingOverhead n := by
  unfold hammingOverhead
  positivity

/-- Canonical uniform code for the Hamming ball described by a pair-coded
center/radius parameter. -/
noncomputable def hammingBallCode (w : BitString) : BitString :=
  let x := decodeFirst w
  let r := decodeNatCode (decodeSecond w)
  canonicalUniformCodeOfList (canonicalFinsetList (hammingBall x.length x r))

/-- Stage `t` of the Hamming enumeration. -/
noncomputable def hammingEnum (t : ℕ) : List BitString :=
  (boundedPrograms t).map hammingBallCode

/-- Auxiliary recursion identity for `List.zip` of bitstrings, expressing it as a
structural recursion suitable for a primitive-recursion proof. -/
theorem bitZip_rec_aux (n : ℕ) (y : List Bool) :
    ∀ s : List Bool, s.length ≤ n →
      s.rec ([] : List (Bool × Bool))
        (fun b l IH => ((y[n - (l.length + 1)]?).map (fun c => (b, c) :: IH)).getD [])
      = s.zip (y.drop (n - s.length)) := by
  intro s
  induction s with
  | nil => intro _; simp
  | cons a xs ih =>
    intro hlen; simp only [List.length_cons] at hlen
    have ih' := ih (by omega); simp only; rw [ih']
    have hd : n - xs.length = (n - (xs.length + 1)) + 1 := by omega
    rcases hget : y[n - (xs.length + 1)]? with _ | c
    · have hdrop : y.drop (n - (xs.length + 1)) = [] := by
        rw [List.drop_eq_nil_iff]; rw [List.getElem?_eq_none_iff] at hget; omega
      simp only [List.length_cons, Option.map_none, Option.getD_none, hdrop, List.zip_nil_right]
    · obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hget
      have hc : y.drop (n - (xs.length + 1)) = c :: y.drop (n - xs.length) := by
        rw [List.drop_eq_getElem_cons hlt, hval, ← hd]
      simp only [List.length_cons, Option.map_some, Option.getD_some, hc, List.zip_cons_cons]

open Primrec in
/-- Zipping two bitstrings is a primitive recursive binary operation. -/
theorem bitZip_primrec : Primrec₂ (fun (x y : List Bool) => x.zip y) := by
  change Primrec (fun p : List Bool × List Bool => p.1.zip p.2)
  have hh : Primrec₂ (fun (a : List Bool × List Bool)
      (p : Bool × List Bool × List (Bool × Bool)) =>
        ((a.2[a.1.length - (p.2.1.length + 1)]?).map (fun c => (p.1, c) :: p.2.2)).getD []) := by
    change Primrec (fun w : (List Bool × List Bool) × (Bool × List Bool × List (Bool × Bool)) =>
      ((w.1.2[w.1.1.length - (w.2.2.1.length + 1)]?).map (fun c => (w.2.1, c) :: w.2.2.2)).getD [])
    apply option_getD.comp _ (const [])
    apply option_map _ _
    · exact list_getElem?.comp (snd.comp fst)
        (nat_sub.comp (list_length.comp (fst.comp fst))
          (succ.comp (list_length.comp (fst.comp (snd.comp snd)))))
    · exact list_cons.comp (Primrec.pair (fst.comp (snd.comp fst)) snd)
        (snd.comp (snd.comp (snd.comp fst)))
  refine (Primrec.list_rec Primrec.fst (Primrec.const []) hh).of_eq ?_
  intro p
  have := bitZip_rec_aux p.1.length p.2 p.1 (le_refl _)
  simp only [Nat.sub_self, List.drop_zero] at this
  rw [← this]

open Primrec in
/-- Hamming distance is a primitive recursive binary function of bitstrings. -/
theorem hammingDist_primrec :
    Primrec₂ (fun (x y : BitString) => hammingDist x y) := by
  change Primrec (fun p : BitString × BitString =>
      ((p.1.zip p.2).filter (fun q => decide (q.1 ≠ q.2))).length)
  apply Primrec.comp Primrec.list_length
  apply list_filter_primrec bitZip_primrec
  have h : Primrec (fun w : (BitString × BitString) × (Bool × Bool) =>
      !(w.2.1 == w.2.2)) :=
    Primrec.not.comp (Primrec.beq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))
  refine h.of_eq (fun w => ?_)
  obtain ⟨_, a, b⟩ := w
  cases a <;> cases b <;> rfl

open Primrec in
/-- The canonical Hamming-ball code is primitive recursive. -/
theorem hammingBallCode_primrec : Primrec hammingBallCode := by
  have hpr : Primrec (fun w => canonicalUniformCodeOfList (canonicalFinsetList
      (((allStrings (decodeFirst w).length).filter
        (fun y =>
            decide (hammingDist (decodeFirst w) y ≤
              decodeNatCode (decodeSecond w)))).toFinset))) := by
    apply canonicalUniformCodeOfList_primrec.comp
    apply canonicalFinsetList_toFinset_primrec.comp
    apply list_filter_primrec
    · exact allStrings_primrec.comp (Primrec.list_length.comp decodeFirst_primrec)
    · exact Primrec.nat_le.decide.comp
        (hammingDist_primrec.comp (decodeFirst_primrec.comp Primrec.fst) Primrec.snd)
        (decodeNatCode_primrec.comp (decodeSecond_primrec.comp Primrec.fst))
  refine hpr.of_eq (fun w => ?_)
  simp only [hammingBallCode, hammingBall_eq_toFinset]

/-- The stage enumeration of codes of Hamming balls is computable. -/
theorem hammingEnum_computable : Computable hammingEnum := by
  unfold hammingEnum
  exact (Primrec.list_map primrec_boundedPrograms
    ((hammingBallCode_primrec.comp Primrec.snd).to₂)).to_comp

/-- Each stage of the enumeration of Hamming-ball codes is a prefix of the next. -/
theorem hammingEnum_mono (t : ℕ) : hammingEnum t <+: hammingEnum (t + 1) := by
  unfold hammingEnum
  rw [boundedPrograms_succ, List.map_append]
  exact List.prefix_append _ _

/-- Every code listed by the enumeration is the canonical uniform code of a Hamming ball. -/
theorem hammingEnum_sound (t : ℕ) : ∀ w ∈ hammingEnum t,
    ∃ (S : Finset BitString) (hS : S.Nonempty),
      hammingFamilyMem S ∧ w = (codedUniformOn S hS).code := by
  intro w hw
  unfold hammingEnum at hw
  rw [List.mem_map] at hw
  rcases hw with ⟨v, _hv, rfl⟩
  let x := decodeFirst v
  let r := decodeNatCode (decodeSecond v)
  let S := hammingBall x.length x r
  have hmem : hammingFamilyMem S := ⟨x.length, x, r, rfl, rfl⟩
  have hS : S.Nonempty := hammingFamilyMem_nonempty hmem
  refine ⟨S, hS, hmem, ?_⟩
  unfold hammingBallCode
  dsimp [x, r, S]
  exact canonicalUniformCodeOfList_canonicalFinsetList S hS

/-- Every Hamming ball has its canonical uniform code listed at some stage. -/
theorem hammingEnum_complete (S : Finset BitString) (hS : S.Nonempty) (hmem : hammingFamilyMem S) :
    ∃ t, (codedUniformOn S hS).code ∈ hammingEnum t := by
  rcases hmem with ⟨n, x, r, hxlen, hS_eq⟩
  refine ⟨(pairCode x (natCode r)).length, ?_⟩
  unfold hammingEnum
  rw [List.mem_map]
  refine ⟨pairCode x (natCode r), ?_, ?_⟩
  · exact (mem_boundedPrograms_iff _ _).mpr le_rfl
  · have hball_eq : hammingBall x.length x r = S := by
      rw [hxlen, ← hS_eq]
    simpa [hammingBallCode, decodeFirst_pairCode, decodeSecond_pairCode,
      decodeNatCode_natCode, hball_eq] using
      (canonicalUniformCodeOfList_canonicalFinsetList S hS)

/-- The radius-zero Hamming volume is one. -/
theorem hammingVol_zero (n : ℕ) : hammingVol n 0 = 1 := by
  simp [hammingVol]

/-- Radius `n` already covers the full `n`-cube. -/
theorem hammingVol_self (n : ℕ) : hammingVol n n = 2 ^ n := by
  have hcard := hammingBall_card n (List.replicate n false) n (by simp)
  have hball : hammingBall n (List.replicate n false) n = stringsOfLength n := by
    ext y
    constructor
    · intro hy
      rw [hammingBall, Finset.mem_filter] at hy
      exact hy.1
    · intro hy
      rw [hammingBall, Finset.mem_filter]
      refine ⟨hy, ?_⟩
      have hylen : y.length = n := (mem_stringsOfLength n y).mp hy
      simpa [hylen] using hammingDist_le_right_length (List.replicate n false) y
  rw [hball, card_stringsOfLength] at hcard
  exact hcard.symm

/-- Bounding the Hamming volume by the total number of strings. -/
theorem hammingVol_le_two_pow (n r : ℕ) : hammingVol n r ≤ 2 ^ n := by
  have hcard := hammingBall_card n (List.replicate n false) r (by simp)
  rw [← hcard, ← card_stringsOfLength n]
  exact Finset.card_le_card (by
    intro x hx
    rw [hammingBall, Finset.mem_filter] at hx
    exact hx.1)

/-- For any target size `c` bounded by the full cube, there is a radius `r_c`
whose volume is `≤ c` but at least `c / (n+1)`. -/
theorem exists_hamming_radius_for_volume (n c : ℕ) (hc : 0 < c) (hc_le : c ≤ 2 ^ n) :
    ∃ r_c : ℕ, hammingVol n r_c ≤ c ∧
      c ≤ (n + 1) * hammingVol n r_c ∧ c ≤ hammingVol n (r_c + 1) := by
  have h_exists : ∃ r, c ≤ hammingVol n r := by
    refine ⟨n, ?_⟩
    rw [hammingVol_self]
    exact hc_le
  set r0 := Nat.find h_exists with hr0_def
  have hr0_spec : c ≤ hammingVol n r0 := by
    rw [hr0_def]
    exact Nat.find_spec h_exists
  cases h0 : r0 with
  | zero =>
      have hr0_spec0 : c ≤ hammingVol n 0 := by
        simpa [h0] using hr0_spec
      refine ⟨0, ?_, ?_⟩
      · rw [hammingVol_zero]
        exact hc
      · refine ⟨?_, ?_⟩
        · rw [hammingVol_zero] at hr0_spec0 ⊢
          omega
        · exact le_trans hr0_spec0 (hammingVol_mono (n := n) (Nat.le_succ 0))
  | succ s =>
      have hr0_spec_succ : c ≤ hammingVol n (s + 1) := by
        simpa [h0] using hr0_spec
      have hs_lt_find : s < Nat.find h_exists := by
        change s < r0
        rw [h0]
        exact Nat.lt_succ_self s
      have hnot : ¬ c ≤ hammingVol n s :=
        Nat.find_min h_exists hs_lt_find
      refine ⟨s, ?_, ?_, ?_⟩
      · exact Nat.le_of_lt (Nat.lt_of_not_ge hnot)
      · exact le_trans hr0_spec_succ (hammingVol_growth n s)
      · exact hr0_spec_succ

/-- `hammingSphere n x s` is the set of all strings of length `n` at exact Hamming distance `s`
from `x`. -/
def hammingSphere (n : ℕ) (x : BitString) (s : ℕ) : Finset BitString :=
  (stringsOfLength n).filter (fun y => hammingDist x y = s)

/-- A sphere of radius `s ≤ r` is contained in the ball of radius `r`. -/
lemma hammingSphere_subset_hammingBall (n : ℕ) (z : BitString) (s r : ℕ) (hs : s ≤ r) :
    hammingSphere n z s ⊆ hammingBall n z r := by
  intro y hy
  rw [hammingSphere, Finset.mem_filter] at hy
  rw [hammingBall, Finset.mem_filter]
  exact ⟨hy.1, by simpa [hy.2] using hs⟩

/-- A ball is the disjoint union of the spheres of radius at most `r`. -/
lemma sum_hammingSphere_card (n : ℕ) (z : BitString) (r : ℕ) :
    ∑ s ∈ Finset.range (r + 1), (hammingSphere n z s).card = (hammingBall n z r).card := by
  classical
  have hdisj : (↑(Finset.range (r + 1)) : Set ℕ).PairwiseDisjoint
      (fun s => hammingSphere n z s) := by
    intro s hs t ht hst
    rw [Finset.mem_coe, Finset.mem_range] at hs ht
    apply Finset.disjoint_left.mpr
    intro y hys hyt
    simp [hammingSphere] at hys hyt
    have hst_eq : s = t := by omega
    exact hst hst_eq
  calc
    ∑ s ∈ Finset.range (r + 1), (hammingSphere n z s).card
        = ((Finset.range (r + 1)).biUnion (fun s => hammingSphere n z s)).card :=
          (Finset.card_biUnion hdisj).symm
    _ = (hammingBall n z r).card := by
      congr 1
      ext y
      constructor
      · intro hy
        rw [Finset.mem_biUnion] at hy
        rcases hy with ⟨s, hs, hys⟩
        rw [Finset.mem_range] at hs
        rw [hammingSphere, Finset.mem_filter] at hys
        rw [hammingBall, Finset.mem_filter]
        exact ⟨hys.1, by omega⟩
      · intro hy
        rw [hammingBall, Finset.mem_filter] at hy
        rw [Finset.mem_biUnion]
        exact ⟨hammingDist z y, Finset.mem_range.mpr (Nat.lt_succ_of_le hy.2),
          by rw [hammingSphere, Finset.mem_filter]; exact ⟨hy.1, rfl⟩⟩

/-- Summing sphere sizes up to `min r n` already gives the whole ball, since spheres of radius
above `n` are empty. -/
lemma sum_hammingSphere_card_min (n : ℕ) (z : BitString) (r : ℕ) :
    ∑ s ∈ Finset.range (min r n + 1), (hammingSphere n z s).card =
      (hammingBall n z r).card := by
  classical
  have hdisj : (↑(Finset.range (min r n + 1)) : Set ℕ).PairwiseDisjoint
      (fun s => hammingSphere n z s) := by
    intro s hs t ht hst
    rw [Finset.mem_coe, Finset.mem_range] at hs ht
    apply Finset.disjoint_left.mpr
    intro y hys hyt
    simp only [hammingSphere, Finset.mem_filter] at hys hyt
    exact hst (hys.2.symm.trans hyt.2)
  calc
    ∑ s ∈ Finset.range (min r n + 1), (hammingSphere n z s).card
        = ((Finset.range (min r n + 1)).biUnion (fun s => hammingSphere n z s)).card :=
          (Finset.card_biUnion hdisj).symm
    _ = (hammingBall n z r).card := by
      congr 1
      ext y
      constructor
      · intro hy
        rw [Finset.mem_biUnion] at hy
        rcases hy with ⟨s, hs, hys⟩
        rw [Finset.mem_range] at hs
        rw [hammingSphere, Finset.mem_filter] at hys
        rw [hammingBall, Finset.mem_filter]
        exact ⟨hys.1, by omega⟩
      · intro hy
        rw [hammingBall, Finset.mem_filter] at hy
        rw [Finset.mem_biUnion]
        refine ⟨hammingDist z y, ?_, ?_⟩
        · have hylen : y.length = n := (mem_stringsOfLength n y).mp hy.1
          have hdistn : hammingDist z y ≤ n := by
            simpa [hylen] using hammingDist_le_right_length z y
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_min.mpr ⟨hy.2, hdistn⟩))
        · rw [hammingSphere, Finset.mem_filter]
          exact ⟨hy.1, rfl⟩

/-- The Hamming sphere of radius `s` around a length-`n` string has exactly
`Nat.choose n s` elements. -/
lemma hammingSphere_card (n : ℕ) (z : BitString) (s : ℕ) (hz : z.length = n) :
    (hammingSphere n z s).card = Nat.choose n s := by
  induction s with
  | zero =>
    convert hammingBall_card n z 0 hz using 1
    · congr 1
      ext y
      simp [hammingSphere, hammingBall]
    · simp [hammingVol_zero]
  | succ s ih =>
    have h_sum : ∀ r, ∑ s ∈ Finset.range (r + 1),
        (hammingSphere n z s).card = ∑ s ∈ Finset.range (r + 1), Nat.choose n s := by
      intro r
      have := sum_hammingSphere_card n z r
      have := hammingBall_card n z r hz
      have := hammingVol
      simp_all [ hammingVol ];
    have := h_sum ( s + 1 ) ; have := h_sum s; simp_all [ Finset.sum_range_succ ] ;

/-- Some sphere around `z` of radius at most `n` carries at least a `1 / (n + 1)` fraction of the
ball of radius `r_c` around `y`. -/
lemma exists_good_center_shell (n : ℕ) (z y : BitString) (r_c : ℕ)
    (_hz : z.length = n) (hy : y.length = n) :
    ∃ k ≤ n, ((hammingSphere n z k).filter (fun x => hammingDist x y ≤ r_c)).card * (n + 1) ≥
      hammingVol n r_c := by
  classical
  let A : ℕ → Finset BitString :=
    fun k => (hammingSphere n z k).filter (fun x => hammingDist x y ≤ r_c)
  have hdisj : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint A := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    have hda : hammingDist z x = a := by
      have hxa' := (Finset.mem_filter.mp hxa).1
      exact (Finset.mem_filter.mp hxa').2
    have hdb : hammingDist z x = b := by
      have hxb' := (Finset.mem_filter.mp hxb).1
      exact (Finset.mem_filter.mp hxb').2
    exact hab (hda.symm.trans hdb)
  have hsum :
      (∑ k ∈ Finset.range (n + 1), (A k).card) = hammingVol n r_c := by
    calc
      (∑ k ∈ Finset.range (n + 1), (A k).card)
          = ((Finset.range (n + 1)).biUnion A).card :=
            (Finset.card_biUnion hdisj).symm
      _ = (hammingBall n y r_c).card := by
        congr 1
        ext x
        constructor
        · intro hx
          rw [Finset.mem_biUnion] at hx
          rcases hx with ⟨k, _hk, hxA⟩
          rw [hammingBall, Finset.mem_filter]
          have hxS := (Finset.mem_filter.mp hxA).1
          have hxlen : x ∈ stringsOfLength n := (Finset.mem_filter.mp hxS).1
          have hdist : hammingDist y x ≤ r_c := by
            simpa [hammingDist_comm] using (Finset.mem_filter.mp hxA).2
          exact ⟨hxlen, hdist⟩
        · intro hx
          rw [hammingBall, Finset.mem_filter] at hx
          rw [Finset.mem_biUnion]
          refine ⟨hammingDist z x, ?_, ?_⟩
          · have hxlen : x.length = n := (mem_stringsOfLength n x).mp hx.1
            exact Finset.mem_range.mpr
              (Nat.lt_succ_of_le (by simpa [hxlen] using hammingDist_le_right_length z x))
          · rw [Finset.mem_filter]
            refine ⟨?_, ?_⟩
            · rw [hammingSphere, Finset.mem_filter]
              exact ⟨hx.1, rfl⟩
            · simpa [hammingDist_comm] using hx.2
      _ = hammingVol n r_c := hammingBall_card n y r_c hy
  have hne : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨k, hk_mem, hk_max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun k => (A k).card) hne
  refine ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hk_mem), ?_⟩
  calc
    hammingVol n r_c = ∑ k ∈ Finset.range (n + 1), (A k).card := hsum.symm
    _ ≤ (Finset.range (n + 1)).card * (A k).card :=
        Finset.sum_le_card_nsmul _ _ _ (fun i hi => hk_max i hi)
    _ = (n + 1) * (A k).card := by rw [Finset.card_range]
    _ = (A k).card * (n + 1) := Nat.mul_comm _ _

/-- A sphere in `{0,1}^n` has at most `2 ^ n` elements, so its binary logarithm is at most `n`. -/
lemma log2_card_hammingSphere_le (n : ℕ) (z : BitString) (s : ℕ) (_hz : z.length = n) :
    Nat.log2 (hammingSphere n z s).card ≤ n := by
  classical
  have hsub : hammingSphere n z s ⊆ stringsOfLength n := by
    intro x hx
    rw [hammingSphere, Finset.mem_filter] at hx
    exact hx.1
  have hcard : (hammingSphere n z s).card ≤ 2 ^ n := by
    rw [← card_stringsOfLength n]
    exact Finset.card_le_card hsub
  by_cases hzero : (hammingSphere n z s).card = 0
  · simp [hzero]
  · have hltpow : (hammingSphere n z s).card < 2 ^ (n + 1) :=
      lt_of_le_of_lt hcard (Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
    have hloglt : Nat.log 2 (hammingSphere n z s).card < n + 1 :=
      Nat.log_lt_of_lt_pow hzero hltpow
    rw [Nat.log2_eq_log_two]
    omega

/-- Every point of a sphere around `z` has at least `hammingVol n r_c / (n + 1) ^ 4` neighbours
within distance `r_c` in the annulus of radii `s ± r_c` around `z`. -/
lemma hammingSphere_annulus_degree (n : ℕ) (z : BitString) (s r_c : ℕ) (hz : z.length = n)
    (y : BitString) (hy : y ∈ hammingSphere n z s) :
    hammingVol n r_c ≤ (n + 1)^4 *
      ((stringsOfLength n).filter (fun b =>
         s - r_c ≤ hammingDist z b ∧ hammingDist z b ≤ s + r_c ∧
         hammingDist b y ≤ r_c)).card := by
  classical
  rw [hammingSphere, Finset.mem_filter] at hy
  have hylen : y.length = n := (mem_stringsOfLength n y).mp hy.1
  have hzy : hammingDist z y = s := hy.2
  let D : Finset BitString := (stringsOfLength n).filter (fun b =>
    s - r_c ≤ hammingDist z b ∧ hammingDist z b ≤ s + r_c ∧
    hammingDist b y ≤ r_c)
  have hsub : hammingBall n y r_c ⊆ D := by
    intro b hb
    rw [hammingBall, Finset.mem_filter] at hb
    have hblen : b.length = n := (mem_stringsOfLength n b).mp hb.1
    have hby : hammingDist b y ≤ r_c := by
      simpa [hammingDist_comm] using hb.2
    have hupper : hammingDist z b ≤ s + r_c := by
      have htri := hammingDist_triangle_of_eq_length z y b
        (by rw [hz, hylen]) (by rw [hylen, hblen])
      calc
        hammingDist z b ≤ hammingDist z y + hammingDist y b := htri
        _ ≤ s + r_c := by
          rw [hzy]
          omega
    have hlower : s - r_c ≤ hammingDist z b := by
      have htri := hammingDist_triangle_of_eq_length z b y
        (by rw [hz, hblen]) (by rw [hblen, hylen])
      have hle : s ≤ hammingDist z b + r_c := by
        rw [← hzy]
        exact le_trans htri (Nat.add_le_add_left hby _)
      omega
    rw [Finset.mem_filter]
    exact ⟨hb.1, hlower, hupper, hby⟩
  have hcard : hammingVol n r_c ≤ D.card := by
    rw [← hammingBall_card n y r_c hylen]
    exact Finset.card_le_card hsub
  calc
    hammingVol n r_c ≤ D.card := hcard
    _ ≤ (n + 1)^4 * D.card := Nat.le_mul_of_pos_left _ (by positivity)

/-- An annulus of strings of length `n` has at most `2 ^ n` elements. -/
lemma hammingSphere_annulus_card_le (n : ℕ) (z : BitString) (s r_c : ℕ) (_hz : z.length = n) :
    ((stringsOfLength n).filter (fun b =>
       s - r_c ≤ hammingDist z b ∧ hammingDist z b ≤ s + r_c)).card ≤
    2 ^ n := by
  classical
  rw [← card_stringsOfLength n]
  exact Finset.card_le_card (by
    intro b hb
    exact (Finset.mem_filter.mp hb).1)

/-- For equal-length strings, Hamming distance is the number of differing
coordinates. -/
lemma hammingDist_eq_filter_card (n : ℕ) (x y : BitString)
    (hx : x.length = n) (hy : y.length = n) :
    hammingDist x y =
      (Finset.filter (fun i => x[i]! ≠ y[i]!) (Finset.range n)).card := by
  have h_zip : List.zip x y = List.map (fun i => (x[i]!, y[i]!)) (List.range n) := by
    refine List.ext_get (by simp only [List.length_zip, hx, hy, min_self, List.length_map,
        List.length_range]) (fun i h1 h2 => ?_)
    subst hx
    simp_all only [List.get_eq_getElem, List.getElem_zip, List.getElem!_eq_getElem?_getD,
        Bool.default_bool,
      List.getElem_map, List.getElem_range, Prod.mk.injEq]
    simp_all only [List.length_map, List.length_range, getElem?_pos, Option.getD_some, and_self]
  unfold hammingDist
  simp only [h_zip, Finset.filter]
  norm_num [Multiset.range]
  rw [List.filter_map]
  subst hx
  simp_all only [List.getElem!_eq_getElem?_getD, Bool.default_bool, List.length_map]
  rfl

/-
Geodesic-interval degree bound.  If `x` lies on the sphere of radius `s`
around `z` and `r_c ≤ s`, then at least `Nat.choose s r_c` strings `b` on the
sphere of radius `s - r_c` around `z` are within Hamming distance `r_c` of `x`.
(These are exactly the points that lie on a geodesic between `z` and `x` at
distance `s - r_c` from `z`; each corresponds to a choice of `r_c` of the `s`
coordinates where `x` differs from `z`.)
-/
lemma hammingSphere_cover_degree (n : ℕ) (z x : BitString) (s r_c : ℕ)
    (hz : z.length = n) (hx : x ∈ hammingSphere n z s) (hrc : r_c ≤ s) :
    Nat.choose s r_c ≤
      ((hammingSphere n z (s - r_c)).filter (fun b => hammingDist b x ≤ r_c)).card := by
  -- By definition of $D$, we know that $|D| = s$.
  have hx_length : x.length = n :=
    mem_stringsOfLength n x |>.1 (Finset.mem_filter.mp hx |>.1)
  have hD_card : (Finset.filter (fun i => z[i]! ≠ x[i]!) (Finset.range n)).card = s := by
    rw [← hammingDist_eq_filter_card n z x hz hx_length]
    exact Finset.mem_filter.mp hx |>.2
  -- For each $R \subseteq D$ with $|R| = r_c$, define the center $b_R := (List.range n).map (fun i
  -- => if i ∈ R then z[i]! else x[i]!)$.
  have h_center : ∀ R ⊆ Finset.filter (fun i =>
      z[i]! ≠ x[i]!) (Finset.range n), R.card = r_c →
        (List.range n).map (fun i => if i ∈ R then z[i]! else x[i]!) ∈ hammingSphere n z (s - r_c) ∧
        hammingDist ((List.range n).map (fun i => if i ∈ R then z[i]! else x[i]!)) x ≤ r_c := by
    intro R hR_sub hR_card
    have h_center_hamming : hammingDist ((List.range n).map (fun i =>
        if i ∈ R then z[i]! else x[i]!)) z = s - r_c := by
      have h_center_hamming : hammingDist ((List.range n).map (fun i =>
          if i ∈ R then z[i]! else x[i]!)) z =
            (Finset.filter (fun i => (List.map (fun i => if i ∈ R then z[i]! else x[i]!)
              (List.range n))[i]! ≠ z[i]!) (Finset.range n)).card := by
        have h_center_hamming : ∀ (u v : BitString), u.length = n → v.length = n →
            hammingDist u v = (Finset.filter (fun i => u[i]! ≠ v[i]!) (Finset.range n)).card :=
          hammingDist_eq_filter_card n
        grind +qlia;
      have h_center_hamming : Finset.filter (fun i => (List.map (fun i =>
          if i ∈ R then z[i]! else x[i]!) (List.range n))[i]! ≠ z[i]!) (Finset.range n) =
            Finset.filter (fun i => z[i]! ≠ x[i]!) (Finset.range n) \ R := by
        grind;
      grind
    have h_center_hamming_x : hammingDist ((List.range n).map (fun i =>
        if i ∈ R then z[i]! else x[i]!)) x = r_c := by
      convert hR_card using 1;
      have h_center_hamming_x : ∀ (u v : BitString), u.length = n → v.length = n →
          hammingDist u v = (Finset.filter (fun i => u[i]! ≠ v[i]!) (Finset.range n)).card :=
        hammingDist_eq_filter_card n
      convert h_center_hamming_x _ _ _ _ using 2;
      · grind +extAll;
      · simp [ List.length_range ];
      · exact mem_stringsOfLength n x |>.1 ( Finset.mem_filter.mp hx |>.1 )
    exact ⟨by
    simp_all only [hammingSphere, Finset.mem_filter, List.getElem!_eq_getElem?_getD,
        Bool.default_bool, ne_eq];
    exact ⟨ by exact mem_stringsOfLength n _ |>.2 <| by simp [ List.length_map,
        List.length_range ], by rw [ ← h_center_hamming, hammingDist_comm ] ⟩, by
      exact h_center_hamming_x.le⟩;
  refine le_trans ?_ ( Finset.card_le_card <| show Finset.image ( fun R : Finset ℕ =>
      List.map ( fun i => if i ∈ R then z[i]! else x[i]! ) ( List.range n ) )
        ( Finset.powersetCard r_c
            ( Finset.filter ( fun i => z[i]! ≠ x[i]! ) ( Finset.range n ) ) ) ⊆
        Finset.filter ( fun b => hammingDist b x ≤ r_c )
          ( hammingSphere n z ( s - r_c ) ) from ?_ );
  · rw [ Finset.card_image_of_injOn, Finset.card_powersetCard, hD_card ];
    intro R hR R' hR' h_eq; simp_all [ Finset.ext_iff ] ;
    grind;
  · grind +splitImp

/-
Hamming distance to the bitwise complement: for equal-length strings,
`hammingDist (z.map not) y = z.length - hammingDist z y`.
-/
lemma hammingDist_map_not (z y : BitString) (h : z.length = y.length) :
    hammingDist (z.map (fun b => !b)) y = z.length - hammingDist z y := by
  induction z generalizing y with
  | nil => cases y <;> trivial
  | cons a z ih =>
    cases y <;> simp_all only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff,
        List.length_eq_zero_iff, one_ne_zero, and_false, Nat.add_right_cancel_iff, List.map_cons,
        hammingDist_cons, Bool.not_eq_eq_eq_not, implies_true];
    split_ifs <;> simp_all +arith only [Bool.eq_not_self, Bool.not_eq_eq_eq_not, not_false_eq_true,
        zero_add, Nat.reduceSubDiff, Bool.not_eq_not];
    rw [ Nat.sub_add_comm ];
    exact hammingDist_le_right_length _ _

/-
Balanced self-cover degree bound.  If `x` lies on the sphere of radius `s`
around `z`, then at least `Nat.choose s k * Nat.choose (n - s) k` strings `b` on
the *same* sphere of radius `s` around `z` are within Hamming distance `2 * k`
of `x` (obtained by flipping `k` of the `s` coordinates where `x` differs from
`z` and `k` of the `n - s` coordinates where `x` agrees with `z`).
-/
lemma hammingSphere_self_degree (n : ℕ) (z x : BitString) (s k : ℕ)
    (hz : z.length = n) (hx : x ∈ hammingSphere n z s) (hks : k ≤ s) (hkn : k ≤ n - s) :
    Nat.choose s k * Nat.choose (n - s) k ≤
      ((hammingSphere n z s).filter (fun b => hammingDist b x ≤ 2 * k)).card := by
  -- By definition of $D$ and $E$, we know that $|D| = s$ and $|E| = n - s$.
  set D := Finset.filter (fun i => z[i]! ≠ x[i]!) (Finset.range n)
  set E := Finset.filter (fun i => z[i]! = x[i]!) (Finset.range n)
  have hx_length : x.length = n :=
    mem_stringsOfLength n x |>.1 (Finset.mem_filter.mp hx |>.1)
  have hD_card : D.card = s := by
    rw [← hammingDist_eq_filter_card n z x hz hx_length]
    exact Finset.mem_filter.mp hx |>.2
  have hE_card : E.card = n - s := by
    have hED : E = Finset.range n \ D := by
      ext i
      simp only [E, D, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
      constructor
      · rintro ⟨hi, heq⟩
        exact ⟨hi, fun hne => hne.2 heq⟩
      · rintro ⟨hi, hnot⟩
        exact ⟨hi, not_not.mp fun heq => hnot ⟨hi, heq⟩⟩
    rw [hED, Finset.card_sdiff]
    rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _), Finset.card_range, hD_card]
  have hDE : Disjoint D E := by
    refine Finset.disjoint_left.mpr fun i hiD hiE => ?_
    simp only [D, E, Finset.mem_filter] at hiD hiE
    exact hiD.2 hiE.2
  -- For any $(A, B) \in \text{powersetCard } k D \times \text{powersetCard } k E$, let $b =
  -- \text{map } (\lambda i \mapsto \text{if } i \in A \cup B \text{ then } !x[i]! \text{ else }
  -- x[i]!)$.
  have h_image : ∀ A ∈ Finset.powersetCard k D, ∀ B ∈ Finset.powersetCard k E,
    let b := (List.range n).map (fun i => if i ∈ A ∪ B then !x[i]! else x[i]!);
    b ∈ hammingSphere n z s ∧ hammingDist b x ≤ 2 * k := by
      intros A hA B hB
      let b := (List.range n).map (fun i => if i ∈ A ∪ B then !x[i]! else x[i]!)
      have hb_length : b.length = n := by
        simp [b]
      have hA_sub := (Finset.mem_powersetCard.mp hA).1
      have hA_card := (Finset.mem_powersetCard.mp hA).2
      have hB_sub := (Finset.mem_powersetCard.mp hB).1
      have hB_card := (Finset.mem_powersetCard.mp hB).2
      have hAB : Disjoint A B := hDE.mono hA_sub hB_sub
      have hb_hammingDist : hammingDist b x = 2 * k := by
        have hfilter : Finset.filter (fun i => b[i]! ≠ x[i]!) (Finset.range n) = A ∪ B := by
          grind
        rw [hammingDist_eq_filter_card n b x hb_length hx_length, hfilter,
          Finset.card_union_of_disjoint hAB, hA_card, hB_card, two_mul]
      have hb_hammingDist_z : hammingDist z b = s := by
        have hfilterz : Finset.filter (fun i => z[i]! ≠ b[i]!) (Finset.range n) = D \ A ∪ B := by
          ext i; simp only [List.getElem!_eq_getElem?_getD, Bool.default_bool, Finset.mem_union,
              List.getElem?_map, ne_eq, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, b,
              D];
          by_cases hi : i < n <;> by_cases hi' : i ∈ A <;> by_cases hi'' : i ∈ B <;> simp only [hi,
              List.length_range, getElem?_pos, List.getElem_range, Option.map_some, hi', hi'',
              or_self, ↓reduceIte, Option.getD_some, Bool.not_eq_not, true_and, not_true_eq_false,
              and_false, or_true, iff_true, or_false, iff_false, not_false_eq_true, and_true,
              getElem?_neg, Option.map_none, Option.getD_none, Bool.not_eq_false, false_and,
              and_self];
          · grind;
          · simpa using (Finset.mem_filter.mp (hA_sub hi')).2
          · simpa using (Finset.mem_filter.mp (hB_sub hi'')).2
          · exact hi (Finset.mem_range.mp (Finset.mem_filter.mp (hA_sub hi')).1)
          · exact hi (Finset.mem_range.mp (Finset.mem_filter.mp (hB_sub hi'')).1)
        have hdisj : Disjoint (D \ A) B := hDE.mono Finset.sdiff_subset hB_sub
        rw [hammingDist_eq_filter_card n z b hz hb_length, hfilterz,
          Finset.card_union_of_disjoint hdisj, Finset.card_sdiff,
          Finset.inter_eq_left.mpr hA_sub, hD_card, hA_card, hB_card]
        omega
      have hb_in_hammingSphere : b ∈ hammingSphere n z s := by
        exact Finset.mem_filter.mpr ⟨ by exact mem_stringsOfLength n b |>.2 hb_length,
            hb_hammingDist_z ⟩
      exact ⟨hb_in_hammingSphere, by linarith⟩;
  have h_image_card : Finset.card (Finset.image (fun (p : Finset ℕ × Finset ℕ) =>
      (List.range n).map (fun i => if i ∈ p.1 ∪ p.2 then !x[i]! else x[i]!))
        (Finset.powersetCard k D ×ˢ Finset.powersetCard k E)) =
        Nat.choose s k * Nat.choose (n - s) k := by
    rw [ Finset.card_image_of_injOn, Finset.card_product, Finset.card_powersetCard,
        Finset.card_powersetCard, hD_card, hE_card ];
    intro p hp q hq h_eq; simp_all only [Finset.mem_powersetCard, Finset.mem_union,
        List.getElem!_eq_getElem?_getD, Bool.default_bool, and_imp, Finset.coe_product,
        Set.mem_prod, SetLike.mem_coe, List.map_inj_left, List.mem_range, getElem?_pos,
        Option.getD_some];
    -- Since $p$ and $q$ are subsets of $D$ and $E$ respectively, and $D$ and $E$ are disjoint, we
    -- have $p.1 = q.1$ and $p.2 = q.2$.
    have h_eq1 : p.1 = q.1 := by
      grind
    have h_eq2 : p.2 = q.2 := by
      grind
    exact Prod.ext h_eq1 h_eq2;
  by_cases hk : k ≤ n - s
  · exact h_image_card ▸ Finset.card_le_card (Finset.image_subset_iff.mpr fun p hp => by
      rcases Finset.mem_product.mp hp with ⟨hpA, hpB⟩
      exact Finset.mem_filter.mpr (h_image p.1 hpA p.2 hpB))
  · exact (hk hkn).elim

end Kolmogorov
