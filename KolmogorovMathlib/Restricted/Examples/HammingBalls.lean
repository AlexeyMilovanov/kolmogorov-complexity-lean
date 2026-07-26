/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.Family
import KolmogorovMathlib.Restricted.GreedyCover
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Logic.Equiv.Fintype

/-!
# Example: the family of Hamming balls

This file develops the Hamming-ball description family: `hammingBall n x r` is
the set of length-`n` bitstrings within Hamming distance `r` of `x`, and
`hammingVol n r` is its cardinality, computed as a partial sum of binomial
coefficients (`hammingBall_card`, `hammingSphere_card`).

The combinatorial core is a probabilistic covering argument
(`hamming_probabilistic_cover`) built on Vandermonde's identity, which yields
covers of the required size for every ball and hence the polynomial-overhead
property of the Hamming family.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Hamming distance between two bitstrings. Useful mostly for strings of the same length. -/
def hammingDist (x y : BitString) : ℕ :=
  ((x.zip y).filter (fun (a, b) => a ≠ b)).length

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

theorem hammingDist_le_right_length (x y : BitString) :
    hammingDist x y ≤ y.length := by
  unfold hammingDist
  calc
    ((x.zip y).filter (fun (a, b) => a ≠ b)).length ≤ (x.zip y).length :=
      List.length_filter_le _ _
    _ = min x.length y.length := List.length_zip
    _ ≤ y.length := Nat.min_le_right _ _

theorem hammingDist_cons (b c : Bool) (xs ys : BitString) :
    hammingDist (b :: xs) (c :: ys) = (if b = c then 0 else 1) + hammingDist xs ys := by
  unfold hammingDist
  rw [List.zip_cons_cons]
  by_cases h : b = c
  · rw [List.filter_cons_of_neg, if_pos h]
    · simp
    · simp [h]
  · rw [List.filter_cons_of_pos, if_neg h]
    · simp [List.length_cons]; ring
    · simp [h]

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

theorem hammingFamilyMem_nonempty {A : Finset BitString} (h : hammingFamilyMem A) : A.Nonempty := by
  rcases h with ⟨n, x, r, hlen, rfl⟩
  refine ⟨x, ?_⟩
  rw [hammingBall, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [memStringsOfLength]
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
Honest leaf: ball cardinality as binomial sum.
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
  have hylen : y.length = n := (memStringsOfLength n y).mp h
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
          ∑ s ∈ Finset.range (r + 1), Nat.choose n s := by
          omega

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

lemma hammingVol_lt_of_lt_min (n r s : ℕ) (h : r < min s n) :
    hammingVol n r < hammingVol n (min s n) := by
  unfold hammingVol
  have h_split :
      Finset.range (min s n + 1) =
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

lemma hammingVol_lt_of_lt_of_lt_n {n r s : ℕ} (hrs : r < s) (hrn : r < n) :
    hammingVol n r < hammingVol n s := by
  have hmin : r < min s n := lt_min hrs hrn
  exact lt_of_lt_of_le (hammingVol_lt_of_lt_min n r s hmin)
    (hammingVol_mono (n := n) (Nat.min_le_left s n))

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
Honest leaf: probabilistic covering/counting lemma.
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
      · convert hcn using 1;
        convert hammingBall_card n x r ( memStringsOfLength n x |>.1 hx ) using 1;
        rfl
      · ext y; simp [hammingDist_comm];
        grind;
    · obtain ⟨ C, hC₁, hC₂, hC₃ ⟩ := h; use C.toList; simp_all only [Finset.subset_iff,
        Finset.mem_biUnion, Finset.mem_filter, true_and, Finset.mem_toList, implies_true,
        Finset.length_toList];
      refine ⟨ fun x hx => ?_, ?_ ⟩;
      · exact memStringsOfLength n x |>.1 ( hC₁ hx );
      · convert hC₃ using 1;
        rw [ cardStringsOfLength, Nat.log2_two_pow ] ; ring;
  · intro x hx;
    convert hcn using 1;
    convert hammingBall_card n x r ( memStringsOfLength n x |>.1 hx ) using 1;
    congr 1 with y ; simp only [Finset.mem_filter, hammingDist_comm];
    unfold hammingBall; aesop;

/-- The overhead for Hamming balls. -/
def hammingOverhead (n : ℕ) : ℕ := (n + 1)^7

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

theorem hammingEnum_computable : Computable hammingEnum := by
  unfold hammingEnum
  exact (Primrec.list_map primrec_boundedPrograms
    ((hammingBallCode_primrec.comp Primrec.snd).to₂)).to_comp

theorem hammingEnum_mono (t : ℕ) : hammingEnum t <+: hammingEnum (t + 1) := by
  unfold hammingEnum
  rw [boundedPrograms_succ, List.map_append]
  exact List.prefix_append _ _

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
      have hylen : y.length = n := (memStringsOfLength n y).mp hy
      simpa [hylen] using hammingDist_le_right_length (List.replicate n false) y
  rw [hball, cardStringsOfLength] at hcard
  exact hcard.symm

/-- Bounding the Hamming volume by the total number of strings. -/
theorem hammingVol_le_two_pow (n r : ℕ) : hammingVol n r ≤ 2 ^ n := by
  have hcard := hammingBall_card n (List.replicate n false) r (by simp)
  rw [← hcard, ← cardStringsOfLength n]
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

lemma hammingSphere_subset_hammingBall (n : ℕ) (z : BitString) (s r : ℕ) (hs : s ≤ r) :
    hammingSphere n z s ⊆ hammingBall n z r := by
  intro y hy
  rw [hammingSphere, Finset.mem_filter] at hy
  rw [hammingBall, Finset.mem_filter]
  exact ⟨hy.1, by simpa [hy.2] using hs⟩

lemma sum_hammingSphere_card (n : ℕ) (z : BitString) (r : ℕ) :
    ∑ s ∈ Finset.range (r + 1), (hammingSphere n z s).card = (hammingBall n z r).card := by
  classical
  have hdisj : (↑(Finset.range (r + 1)) : Set ℕ).PairwiseDisjoint
      (fun s => hammingSphere n z s) := by
    intro s hs t ht hst
    rw [Finset.mem_coe, Finset.mem_range] at hs ht
    apply Finset.disjoint_left.mpr
    intro y hys hyt
    simp only [hammingSphere, Finset.mem_filter] at hys hyt
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
        · have hylen : y.length = n := (memStringsOfLength n y).mp hy.1
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
    calc
      (hammingSphere n z 0).card = (hammingBall n z 0).card := by
        congr 1
        ext y
        simp only [hammingSphere, hammingBall, Finset.mem_filter, nonpos_iff_eq_zero]
      _ = hammingVol n 0 := hammingBall_card n z 0 hz
      _ = Nat.choose n 0 := by
        norm_num [hammingVol]
  | succ s ih =>
    have h_sum : ∀ r, ∑ s ∈ Finset.range (r + 1),
        (hammingSphere n z s).card = ∑ s ∈ Finset.range (r + 1), Nat.choose n s := by
      intro r
      have := sum_hammingSphere_card n z r
      have := hammingBall_card n z r hz
      have := hammingVol
      simp_all [ hammingVol ];
    have := h_sum ( s + 1 ) ; have := h_sum s; simp_all [ Finset.sum_range_succ ] ;

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
          · have hxlen : x.length = n := (memStringsOfLength n x).mp hx.1
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

lemma log2_card_hammingSphere_le (n : ℕ) (z : BitString) (s : ℕ) (_hz : z.length = n) :
    Nat.log2 (hammingSphere n z s).card ≤ n := by
  classical
  have hsub : hammingSphere n z s ⊆ stringsOfLength n := by
    intro x hx
    rw [hammingSphere, Finset.mem_filter] at hx
    exact hx.1
  have hcard : (hammingSphere n z s).card ≤ 2 ^ n := by
    rw [← cardStringsOfLength n]
    exact Finset.card_le_card hsub
  by_cases hzero : (hammingSphere n z s).card = 0
  · simp [hzero]
  · have hltpow : (hammingSphere n z s).card < 2 ^ (n + 1) :=
      lt_of_le_of_lt hcard (Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
    have hloglt : Nat.log 2 (hammingSphere n z s).card < n + 1 :=
      Nat.log_lt_of_lt_pow hzero hltpow
    rw [Nat.log2_eq_log_two]
    omega

lemma hammingSphere_annulus_degree (n : ℕ) (z : BitString) (s r_c : ℕ) (hz : z.length = n)
    (y : BitString) (hy : y ∈ hammingSphere n z s) :
    hammingVol n r_c ≤ (n + 1)^4 *
      ((stringsOfLength n).filter (fun b =>
         s - r_c ≤ hammingDist z b ∧ hammingDist z b ≤ s + r_c ∧
         hammingDist b y ≤ r_c)).card := by
  classical
  rw [hammingSphere, Finset.mem_filter] at hy
  have hylen : y.length = n := (memStringsOfLength n y).mp hy.1
  have hzy : hammingDist z y = s := hy.2
  let D : Finset BitString := (stringsOfLength n).filter (fun b =>
    s - r_c ≤ hammingDist z b ∧ hammingDist z b ≤ s + r_c ∧
    hammingDist b y ≤ r_c)
  have hsub : hammingBall n y r_c ⊆ D := by
    intro b hb
    rw [hammingBall, Finset.mem_filter] at hb
    have hblen : b.length = n := (memStringsOfLength n b).mp hb.1
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

lemma hammingSphere_annulus_card_le (n : ℕ) (z : BitString) (s r_c : ℕ) (_hz : z.length = n) :
    ((stringsOfLength n).filter (fun b =>
       s - r_c ≤ hammingDist z b ∧ hammingDist z b ≤ s + r_c)).card ≤
    2 ^ n := by
  classical
  rw [← cardStringsOfLength n]
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
    memStringsOfLength n x |>.1 (Finset.mem_filter.mp hx |>.1)
  have hD_card : (Finset.filter (fun i => z[i]! ≠ x[i]!) (Finset.range n)).card = s := by
    rw [← hammingDist_eq_filter_card n z x hz hx_length]
    exact Finset.mem_filter.mp hx |>.2
  -- For each $R \subseteq D$ with $|R| = r_c$, define the center $b_R := (List.range n).map (fun i
  -- => if i ∈ R then z[i]! else x[i]!)$.
  have h_center : ∀ R ⊆ Finset.filter (fun i =>
      z[i]! ≠ x[i]!) (Finset.range n), R.card = r_c →
        (List.range n).map (fun i => if i ∈ R then z[i]! else x[i]!) ∈
          hammingSphere n z (s - r_c) ∧
        hammingDist ((List.range n).map
          (fun i => if i ∈ R then z[i]! else x[i]!)) x ≤ r_c := by
    intro R hR_sub hR_card
    have h_center_hamming : hammingDist ((List.range n).map (fun i =>
        if i ∈ R then z[i]! else x[i]!)) z = s - r_c := by
      have h_center_hamming : hammingDist ((List.range n).map (fun i =>
          if i ∈ R then z[i]! else x[i]!)) z =
            (Finset.filter (fun i => (List.map (fun i => if i ∈ R then z[i]! else x[i]!)
              (List.range n))[i]! ≠ z[i]!) (Finset.range n)).card := by
        have h_center_hamming :
            ∀ (u v : BitString), u.length = n → v.length = n →
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
      have h_center_hamming_x :
          ∀ (u v : BitString), u.length = n → v.length = n →
            hammingDist u v = (Finset.filter (fun i => u[i]! ≠ v[i]!) (Finset.range n)).card :=
        hammingDist_eq_filter_card n
      convert h_center_hamming_x _ _ _ _ using 2;
      · grind +extAll;
      · simp [ List.length_range ];
      · exact memStringsOfLength n x |>.1 ( Finset.mem_filter.mp hx |>.1 )
    exact ⟨by
    simp_all only [hammingSphere, Finset.mem_filter, List.getElem!_eq_getElem?_getD,
        Bool.default_bool, ne_eq];
    exact ⟨ by exact memStringsOfLength n _ |>.2 <| by simp [ List.length_map,
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
    split_ifs <;> simp_all +arith only [Bool.eq_not_self, Bool.not_eq_eq_eq_not,
        not_false_eq_true, zero_add, Nat.reduceSubDiff, Bool.not_eq_not];
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
    memStringsOfLength n x |>.1 (Finset.mem_filter.mp hx |>.1)
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
          by_cases hi : i < n <;> by_cases hi' : i ∈ A <;> by_cases hi'' : i ∈ B <;>
            simp only [hi, List.length_range, getElem?_pos, List.getElem_range, Option.map_some,
              hi', hi'', or_self, ↓reduceIte, Option.getD_some, Bool.not_eq_not, true_and,
              not_true_eq_false, and_false, or_true, iff_true, or_false, iff_false,
              not_false_eq_true, and_true, getElem?_neg, Option.map_none, Option.getD_none,
              Bool.not_eq_false, false_and, and_self];
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
        exact Finset.mem_filter.mpr ⟨ by exact memStringsOfLength n b |>.2 hb_length,
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

/-!
### Sphere-wise Hamming cover

This is Proposition 26's actual proof architecture.  For `r > n / 2`, cover
the whole cube using `hamming_probabilistic_cover`.  Otherwise decompose
`hammingBall n z r` into the spheres of radii `a <= r`.  A sphere with
`a <= r_c` is covered by the single ball centered at `z`.  For
`r_c < a <= n / 2`, choose a distance `f` such that a polynomial fraction of
the radius-`r_c` sphere around a center at distance `f` from `z` lies in the
target radius-`a` sphere.  The choice of `f` is the random-order/prefix-flip
argument from the paper: for every set of `r_c` flipped coordinates, the path
obtained by toggling coordinates one at a time goes from weight `r_c` to
`n - r_c` and therefore hits weight `a`; pigeonhole over the `n + 1` times.

The sphere incidence graph is regular under coordinate permutations.  Apply
`greedy_cover_indexed` on the selected center sphere and then concatenate the
at most `n + 1` shell covers.  Ball/sphere cardinality differs by at most an
`n + 1` factor, so the public `(n + 1)^7` budget has ample slack.

In particular, centers are not required to belong to the original ball.
-/

/-- Flips the bits of `x` at the indices in `S`. -/
def flipPositions (n : ℕ) (x : BitString) (S : Finset ℕ) : BitString :=
  List.ofFn (fun (i : Fin n) => if i.val ∈ S then !x[i.val]! else x[i.val]!)

theorem flipPositions_length (n : ℕ) (x : BitString) (S : Finset ℕ) :
    (flipPositions n x S).length = n := by
  simp [flipPositions]

theorem hammingDist_flipPositions (n : ℕ) (x : BitString) (S : Finset ℕ) (hx : x.length = n)
    (hS : ∀ i ∈ S, i < n) :
    hammingDist x (flipPositions n x S) = S.card := by
  rw [hammingDist_eq_filter_card n x (flipPositions n x S) hx (flipPositions_length n x S)]
  congr 1
  ext i
  by_cases hi : i < n
  · by_cases hmem : i ∈ S
    · simp [flipPositions, hi, hmem]
    · simp [flipPositions, hi, hmem]
  · have hnotmem : i ∉ S := fun h => hi (hS i h)
    simp [hi, hnotmem]

theorem flipPositions_inj (n : ℕ) (S : Finset ℕ) :
    ∀ x y : BitString,
        x.length = n → y.length = n → flipPositions n x S = flipPositions n y S → x = y := by
  intro x y hx hy hflip
  apply List.ext_get (by rw [hx, hy])
  intro i hi_x hi_y
  have hi_n : i < n := by simpa [hx] using hi_x
  have hget := congrArg (fun l : BitString => l[i]!) hflip
  simp only [flipPositions, List.getElem!_eq_getElem?_getD, Bool.default_bool, List.length_ofFn,
      hi_n, getElem!_pos, List.getElem_ofFn, List.getElem?_eq_getElem hi_x, Option.getD_some,
      List.getElem?_eq_getElem hi_y] at hget
  by_cases hmem : i ∈ S
  · simp [hmem] at hget
    cases x[i] <;> cases y[i] <;> simp_all
  · simp only [hmem, ↓reduceIte] at hget
    exact hget

lemma prefix_flip_path_hits (n : ℕ) (z x : BitString) (r_c a : ℕ)
    (hz : z.length = n) (hx : x.length = n)
    (hr : hammingDist z x = r_c) (ha1 : r_c < a) (ha2 : a ≤ n / 2) :
    ∃ t ≤ n, hammingDist z (flipPositions n x (Finset.range t)) = a := by
  classical
  let d : ℕ → ℕ := fun t => hammingDist z (flipPositions n x (Finset.range t))
  have hflip_zero : flipPositions n x (Finset.range 0) = x := by
    refine List.ext_get ?_ ?_
    · simp [flipPositions, hx]
    · intro i hi_flip hi_x
      have hi_n : i < n := by simpa [flipPositions] using hi_flip
      simp [flipPositions, List.getElem?_eq_getElem hi_x]
  have hd0 : d 0 = r_c := by
    change hammingDist z (flipPositions n x (Finset.range 0)) = r_c
    rw [hflip_zero, hr]
  have hflip_all : flipPositions n x (Finset.range n) = x.map (fun b => !b) := by
    refine List.ext_get ?_ ?_
    · simp [flipPositions, hx]
    · intro i hi_flip hi_map
      have hi_n : i < n := by simpa [flipPositions] using hi_flip
      have hi_x : i < x.length := by simpa using hi_map
      simp [flipPositions, List.getElem?_eq_getElem hi_x]
  have hdn : d n = n - r_c := by
    simp only [d, hflip_all]
    rw [hammingDist_comm z (x.map fun b => !b)]
    rw [hammingDist_map_not x z (by rw [hx, hz])]
    rw [hx, hammingDist_comm x z, hr]
  have ha_le_dn : a ≤ d n := by
    rw [hdn]
    have h2a : 2 * a ≤ n := by
      nlinarith [Nat.mul_le_mul_left 2 ha2, Nat.div_mul_le_self n 2]
    omega
  have hstep : ∀ t : ℕ, d (t + 1) ≤ d t + 1 := by
    intro t
    have hsucc :
        hammingDist (flipPositions n x (Finset.range t))
            (flipPositions n x (Finset.range (t + 1))) ≤ 1 := by
      rw [hammingDist_eq_filter_card n (flipPositions n x (Finset.range t))
        (flipPositions n x (Finset.range (t + 1)))
        (flipPositions_length n x (Finset.range t))
        (flipPositions_length n x (Finset.range (t + 1)))]
      have hsub :
          (Finset.filter (fun i =>
            (flipPositions n x (Finset.range t))[i]! ≠
              (flipPositions n x (Finset.range (t + 1)))[i]!) (Finset.range n)) ⊆
            ({t} : Finset ℕ) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        by_contra hit
        rw [Finset.mem_singleton] at hit
        have hin : i < n := Finset.mem_range.mp hi.1
        have hsame :
            (if i ∈ Finset.range t then !x[i]! else x[i]!) =
              (if i ∈ Finset.range (t + 1) then !x[i]! else x[i]!) := by
          by_cases hit' : i < t
          · have hi_t : i ∈ Finset.range t := Finset.mem_range.mpr hit'
            have hi_succ : i ∈ Finset.range (t + 1) :=
              Finset.mem_range.mpr (Nat.lt_trans hit' (Nat.lt_succ_self t))
            simp [hi_t, hi_succ]
          · have hi_t : i ∉ Finset.range t := by
              rw [Finset.mem_range]
              exact hit'
            have hi_succ : i ∉ Finset.range (t + 1) := by
              rw [Finset.mem_range]
              omega
            simp [hi_t, hi_succ]
        have hvals :
            (flipPositions n x (Finset.range t))[i]! =
              (flipPositions n x (Finset.range (t + 1)))[i]! := by
          simpa [flipPositions, hin] using hsame
        exact hi.2 hvals
      calc
        (Finset.filter (fun i =>
            (flipPositions n x (Finset.range t))[i]! ≠
              (flipPositions n x (Finset.range (t + 1)))[i]!) (Finset.range n)).card
            ≤ ({t} : Finset ℕ).card := Finset.card_le_card hsub
        _ ≤ 1 := by simp
    have htri := hammingDist_triangle_of_eq_length z
      (flipPositions n x (Finset.range t))
      (flipPositions n x (Finset.range (t + 1)))
      (by rw [hz, flipPositions_length])
      (by rw [flipPositions_length, flipPositions_length])
    dsimp [d]
    omega
  let P : ℕ → Prop := fun t => t ≤ n ∧ a ≤ d t
  have hex : ∃ t, P t := ⟨n, le_rfl, ha_le_dn⟩
  let t0 := Nat.find hex
  have ht0_spec : P t0 := Nat.find_spec hex
  have ht0_ne_zero : t0 ≠ 0 := by
    intro ht0_zero
    have : a ≤ r_c := by
      have h := ht0_spec.2
      rwa [ht0_zero, hd0] at h
    omega
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero ht0_ne_zero
  have ht0_eq : Nat.find hex = s + 1 := by
    simpa [t0] using hs
  have ht0_eq' : t0 = s + 1 := by
    simpa [t0] using ht0_eq
  have hnot_prev : ¬ P s := Nat.find_min hex (by
    rw [ht0_eq]
    exact Nat.lt_succ_self s)
  have ht0_le_n : s + 1 ≤ n := by
    simpa [ht0_eq'] using ht0_spec.1
  have ha_le_succ : a ≤ d (s + 1) := by
    simpa [ht0_eq'] using ht0_spec.2
  have hs_le_n : s ≤ n := by omega
  have hds_lt : d s < a := by
    have hnot : ¬ a ≤ d s := fun h => hnot_prev ⟨hs_le_n, h⟩
    omega
  have hdsucc_le : d (s + 1) ≤ a := by
    have := hstep s
    omega
  exact ⟨s + 1, ht0_le_n, le_antisymm hdsucc_le ha_le_succ⟩

lemma flipPositions_comm_dist (n : ℕ) (z x : BitString) (S : Finset ℕ)
    (hz : z.length = n) (hx : x.length = n) :
    hammingDist (flipPositions n z S) (flipPositions n x S) = hammingDist z x := by
  rw [hammingDist_eq_filter_card n (flipPositions n z S) (flipPositions n x S)
      (flipPositions_length n z S) (flipPositions_length n x S),
    hammingDist_eq_filter_card n z x hz hx]
  congr 1
  ext i
  by_cases hi : i < n
  · by_cases hmem : i ∈ S <;> simp [flipPositions, hi, hmem]
  · simp [hi]

theorem exists_dense_hamming_center_shell (n : ℕ) (z : BitString) (r_c a : ℕ)
    (hz : z.length = n) (ha1 : r_c < a) (ha2 : a ≤ n / 2) :
    ∃ f ≤ n, ∃ (c : BitString), c ∈ hammingSphere n z f ∧
      (hammingSphere n z r_c).card ≤
        (n + 1) * ((hammingSphere n c r_c).filter (fun y => y ∈ hammingSphere n z a)).card := by
  classical
  let R := hammingSphere n z r_c
  let center : ℕ → BitString := fun t => flipPositions n z (Finset.range t)
  let Y : ℕ → Finset BitString :=
    fun t => (hammingSphere n (center t) r_c).filter (fun y => y ∈ hammingSphere n z a)
  have hx_len : ∀ p : {x // x ∈ R}, (p : BitString).length = n := by
    intro p
    exact (memStringsOfLength n p.1).mp (Finset.mem_filter.mp p.2).1
  have hx_dist : ∀ p : {x // x ∈ R}, hammingDist z (p : BitString) = r_c := by
    intro p
    exact (Finset.mem_filter.mp p.2).2
  have hhit : ∀ p : {x // x ∈ R},
      ∃ t ≤ n, hammingDist z (flipPositions n (p : BitString) (Finset.range t)) = a := by
    intro p
    exact prefix_flip_path_hits n z p.1 r_c a hz (hx_len p) (hx_dist p) ha1 ha2
  let τ : {x // x ∈ R} → ℕ := fun p => Classical.choose (hhit p)
  have hτ_le : ∀ p : {x // x ∈ R}, τ p ≤ n := by
    intro p
    exact (Classical.choose_spec (hhit p)).1
  have hτ_hit : ∀ p : {x // x ∈ R},
      hammingDist z (flipPositions n (p : BitString) (Finset.range (τ p))) = a := by
    intro p
    exact (Classical.choose_spec (hhit p)).2
  let imagePoint : {x // x ∈ R} → BitString :=
    fun p => flipPositions n (p : BitString) (Finset.range (τ p))
  let embed : {x // x ∈ R} → Sigma (fun _ : ℕ => BitString) :=
    fun p => ⟨τ p, imagePoint p⟩
  have hmaps : Set.MapsTo embed (↑R.attach) (↑((Finset.range (n + 1)).sigma Y)) := by
    intro p _hp
    rw [Finset.mem_coe, Finset.mem_sigma]
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hτ_le p)), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [hammingSphere, Finset.mem_filter]
      refine ⟨(memStringsOfLength n (imagePoint p)).mpr (flipPositions_length n p.1
          (Finset.range (τ p))), ?_⟩
      have hcomm := flipPositions_comm_dist n z p.1 (Finset.range (τ p)) hz (hx_len p)
      simpa [center, imagePoint, hx_dist p] using hcomm
    · rw [hammingSphere, Finset.mem_filter]
      exact ⟨(memStringsOfLength n (imagePoint p)).mpr (flipPositions_length n p.1
          (Finset.range (τ p))),
        hτ_hit p⟩
  have hinj : Set.InjOn embed (↑R.attach) := by
    intro p _hp q _hq heq
    have hpair := Sigma.mk.inj_iff.mp heq
    have ht : τ p = τ q := hpair.1
    have hy : imagePoint p = imagePoint q := eq_of_heq hpair.2
    have hflip :
        flipPositions n p.1 (Finset.range (τ p)) =
          flipPositions n q.1 (Finset.range (τ p)) := by
      simpa [imagePoint, ht] using hy
    exact Subtype.ext (flipPositions_inj n (Finset.range (τ p)) p.1 q.1
      (hx_len p) (hx_len q) hflip)
  have hR_le_sum : R.card ≤ ∑ t ∈ Finset.range (n + 1), (Y t).card := by
    calc
      R.card = R.attach.card := Finset.card_attach.symm
      _ ≤ ((Finset.range (n + 1)).sigma Y).card :=
          Finset.card_le_card_of_injOn embed hmaps hinj
      _ = ∑ t ∈ Finset.range (n + 1), (Y t).card := Finset.card_sigma _ _
  have hne : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨t0, ht0_mem, ht0_max⟩ :=
    Finset.exists_max_image (Finset.range (n + 1)) (fun t => (Y t).card) hne
  have hsum_le : (∑ t ∈ Finset.range (n + 1), (Y t).card) ≤
      (n + 1) * (Y t0).card := by
    calc
      (∑ t ∈ Finset.range (n + 1), (Y t).card)
          ≤ (Finset.range (n + 1)).card * (Y t0).card :=
            Finset.sum_le_card_nsmul _ _ _ (fun t ht => ht0_max t ht)
      _ = (n + 1) * (Y t0).card := by rw [Finset.card_range]
  refine ⟨t0, Nat.le_of_lt_succ (Finset.mem_range.mp ht0_mem), center t0, ?_, ?_⟩
  · rw [hammingSphere, Finset.mem_filter]
    refine ⟨(memStringsOfLength n (center t0)).mpr (flipPositions_length n z (Finset.range t0)), ?_⟩
    have hsupport : ∀ i ∈ Finset.range t0, i < n := by
      intro i hi
      have hit : i < t0 := Finset.mem_range.mp hi
      have ht0n : t0 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp ht0_mem)
      omega
    rw [hammingDist_flipPositions n z (Finset.range t0) hz hsupport, Finset.card_range]
  · exact le_trans hR_le_sum hsum_le

/-- Encode a string by the coordinates on which it differs from a fixed base string. -/
def differenceMask (n : ℕ) (z y : BitString) : Finset (Fin n) :=
  Finset.univ.filter (fun i => z[i.val]! ≠ y[i.val]!)

/-- Reconstruct the string with the prescribed difference mask from a base string. -/
def stringOfDifferenceMask (n : ℕ) (z : BitString) (S : Finset (Fin n)) : BitString :=
  List.ofFn (fun i => if i ∈ S then !z[i.val]! else z[i.val]!)

lemma differenceMask_stringOfDifferenceMask (n : ℕ) (z : BitString)
    (S : Finset (Fin n)) :
    differenceMask n z (stringOfDifferenceMask n z S) = S := by
      ext i; simp [differenceMask, stringOfDifferenceMask]

lemma stringOfDifferenceMask_differenceMask (n : ℕ) (z y : BitString)
    (hz : z.length = n) (hy : y.length = n) :
    stringOfDifferenceMask n z (differenceMask n z y) = y := by
      refine List.ext_get ?_ ?_ <;> simp_all [ stringOfDifferenceMask, differenceMask ];
      grind

lemma hammingDist_stringOfDifferenceMask (n : ℕ) (z : BitString)
    (S T : Finset (Fin n)) :
    hammingDist (stringOfDifferenceMask n z S) (stringOfDifferenceMask n z T) =
      (S \ T).card + (T \ S).card := by
        -- By definition of `stringOfDifferenceMask`, the difference mask of
        -- `stringOfDifferenceMask n z S` and `stringOfDifferenceMask n z T` is
        -- `S \ T ∪ T \ S`.
        have h_diff_mask : differenceMask n (stringOfDifferenceMask n z S)
            (stringOfDifferenceMask n z T) = S \ T ∪ T \ S := by
          ext i; simp [differenceMask, stringOfDifferenceMask];
          grind;
        convert congr_arg Finset.card h_diff_mask using 1;
        · convert hammingDist_eq_filter_card n _ _ _ _ using 2;
          · refine Finset.card_bij ( fun i _ => (i : ℕ) ) ?_ ?_ ?_
            · intro a ha
              simp only [differenceMask, Finset.mem_filter, Finset.mem_univ, true_and] at ha
              exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.isLt, ha⟩
            · exact fun a₁ _ a₂ _ h => Fin.val_injective h
            · intro b hb
              rw [Finset.mem_filter, Finset.mem_range] at hb
              refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
              simp only [differenceMask, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hb.2
          · unfold stringOfDifferenceMask; aesop;
          · unfold stringOfDifferenceMask; aesop;
        · rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hxS hxT =>
            by aesop ) ]

lemma finset_symmetricDifference_card_map_perm {α : Type} [DecidableEq α]
    (σ : Equiv.Perm α) (S T : Finset α) :
    ((Finset.map σ.toEmbedding S) \ (Finset.map σ.toEmbedding T)).card +
        ((Finset.map σ.toEmbedding T) \ (Finset.map σ.toEmbedding S)).card =
      (S \ T).card + (T \ S).card := by
        rw [ show ( Finset.map ( Equiv.toEmbedding σ ) S \ Finset.map ( Equiv.toEmbedding σ )
            T ) = Finset.map ( Equiv.toEmbedding σ ) ( S \ T ) from ?_,
          show ( Finset.map ( Equiv.toEmbedding σ ) T \ Finset.map ( Equiv.toEmbedding σ ) S ) =
            Finset.map ( Equiv.toEmbedding σ ) ( T \ S ) from ?_ ];
        · rw [ Finset.card_map, Finset.card_map ];
        · ext; simp [Finset.mem_sdiff];
        · ext; simp [Finset.mem_sdiff]

lemma differenceMask_card_eq_hammingDist (n : ℕ) (z y : BitString)
    (hz : z.length = n) (hy : y.length = n) :
    (differenceMask n z y).card = hammingDist z y := by
      rw [hammingDist_eq_filter_card n z y hz hy]
      unfold differenceMask
      rw [Finset.card_filter, Finset.card_filter, Finset.sum_range]

lemma mask_incidence_regular (n r_c f a : ℕ) :
    ∀ D1 : Finset (Fin n), D1.card = f →
    ∀ D2 : Finset (Fin n), D2.card = f →
      (Finset.univ.filter (fun Y : Finset (Fin n) =>
        Y.card = a ∧ (D1 \ Y).card + (Y \ D1).card = r_c)).card =
      (Finset.univ.filter (fun Y : Finset (Fin n) =>
        Y.card = a ∧ (D2 \ Y).card + (Y \ D2).card = r_c)).card := by
          intros D1 hD1 D2 hD2
          obtain ⟨σ, hσ⟩ : ∃ σ : Fin n ≃ Fin n, Finset.map σ.toEmbedding D1 = D2 := by
            obtain ⟨σ, hσ⟩ : ∃ σ : {x // x ∈ D1} ≃ {x // x ∈ D2}, True := by
              exact ⟨ Fintype.equivOfCardEq <| by aesop, trivial ⟩;
            refine ⟨ Equiv.extendSubtype σ, ?_ ⟩;
            ext x; simp [Equiv.extendSubtype];
            by_cases hx : x ∈ D2 <;> simp [ hx, Equiv.subtypeCongr ];
            grind +qlia;
          rw [ Finset.card_filter, Finset.card_filter ];
          apply Finset.sum_bij (fun Y _ => Finset.map σ.toEmbedding Y);
          · simp;
          · exact fun a₁ _ a₂ _ h => Finset.map_injective σ.toEmbedding h;
          · exact fun b _ => ⟨ Finset.map σ.symm.toEmbedding b, Finset.mem_univ _, by aesop ⟩;
          · simp [ ← hσ, finset_symmetricDifference_card_map_perm ]

lemma filtered_hammingSphere_card_eq_mask_count
    (n r_c a : ℕ) (z c : BitString) (hz : z.length = n) (hc : c.length = n) :
    ((hammingSphere n c r_c).filter (fun y => y ∈ hammingSphere n z a)).card =
      (Finset.univ.filter (fun Y : Finset (Fin n) =>
        Y.card = a ∧ ((differenceMask n z c) \ Y).card +
          (Y \ (differenceMask n z c)).card = r_c)).card := by
            refine Finset.card_bij ( fun y hy => differenceMask n z y ) ?_ ?_ ?_;
            · simp only [hammingSphere, Finset.mem_filter, Finset.mem_univ, true_and, and_imp];
              intro y hy₁ hy₂ hy₃ hy₄;
              rw [ ← hy₂, ← hy₄, ← hammingDist_stringOfDifferenceMask ];
              exact ⟨ differenceMask_card_eq_hammingDist n z y hz
                  ( by simpa [ stringsOfLength ] using memStringsOfLength n y |>.1 hy₃ ),
                by rw [ stringOfDifferenceMask_differenceMask n z c hz hc,
                  stringOfDifferenceMask_differenceMask n z y hz
                    ( by simpa [ stringsOfLength ] using memStringsOfLength n y |>.1 hy₃ ) ] ⟩;
            · intro y₁ hy₁ y₂ hy₂ h; have :=
                stringOfDifferenceMask_differenceMask n z y₁
              have := stringOfDifferenceMask_differenceMask n z y₂
              simp_all [ Finset.ext_iff ] ;
              simp_all [differenceMask];
              simp_all [ hammingSphere ];
              simp_all [ memStringsOfLength ];
            · intro Y hy; use stringOfDifferenceMask n z Y; simp_all only [Finset.mem_filter,
                Finset.mem_univ, true_and, hammingSphere, exists_prop];
              have h_dist : hammingDist c (stringOfDifferenceMask n z Y) = (differenceMask n z
                  c \ Y).card + (Y \ differenceMask n z c).card := by
                convert hammingDist_stringOfDifferenceMask n z ( differenceMask n z c ) Y using 1;
                rw [ stringOfDifferenceMask_differenceMask n z c hz hc ];
              have h_dist_z : hammingDist z (stringOfDifferenceMask n z Y) = Y.card := by
                convert hammingDist_stringOfDifferenceMask n z ∅ Y using 1;
                · unfold stringOfDifferenceMask; aesop;
                · simp;
              simp_all only [stringsOfLength, List.mem_toFinset, mem_allStrings, and_true,
                and_self];
              exact ⟨ by rw [ stringOfDifferenceMask ] ; simp [ hz ],
                  differenceMask_stringOfDifferenceMask n z Y ⟩

theorem hammingSphere_incidence_regular (n r_c f a : ℕ) (z : BitString) (hz : z.length = n) :
    ∀ c1 ∈ hammingSphere n z f, ∀ c2 ∈ hammingSphere n z f,
      ((hammingSphere n c1 r_c).filter (fun y => y ∈ hammingSphere n z a)).card =
      ((hammingSphere n c2 r_c).filter (fun y => y ∈ hammingSphere n z a)).card := by
        intros c1 hc1 c2 hc2;
        rw [filtered_hammingSphere_card_eq_mask_count n r_c a z c1,
          filtered_hammingSphere_card_eq_mask_count n r_c a z c2]
        · convert mask_incidence_regular n r_c f a ( differenceMask n z c1 ) ( by
          rw [differenceMask_card_eq_hammingDist];
          · exact Finset.mem_filter.mp hc1 |>.2;
          · exact hz;
          · exact Finset.mem_filter.mp hc1 |>.1 |> fun h =>
              by simpa [ hz ] using memStringsOfLength n c1 |>.1 h; ) ( differenceMask n z c2 ) ( by
          convert differenceMask_card_eq_hammingDist n z c2 hz _ |> Eq.trans
              <| Finset.mem_filter.mp hc2 |>.2;
          exact Finset.mem_filter.mp hc2 |>.1 |> fun h =>
              by simpa using memStringsOfLength n c2 |>.1 h; ) using 1
        · grind +splitImp
        · exact Finset.mem_filter.mp hc2 |>.1 |> fun h =>
            by simpa using memStringsOfLength n c2 |>.1 h;
        · exact hz;
        · exact Finset.mem_filter.mp hc1 |>.1 |> fun h =>
            by simpa [hz] using memStringsOfLength n c1 |>.1 h

theorem hammingSphere_cover_centers (n : ℕ) (z : BitString) (r_c a : ℕ) (hz : z.length = n)
    (ha1 : r_c < a) (ha2 : a ≤ n / 2) :
    ∃ 𝒞_centers : Finset BitString,
      (∀ x ∈ 𝒞_centers, x.length = n) ∧
      (∀ y ∈ hammingSphere n z a, ∃ x ∈ 𝒞_centers, hammingDist x y ≤ r_c) ∧
      𝒞_centers.card * (hammingSphere n z r_c).card ≤ (n + 1) * (n + 1) * (hammingSphere n z
          a).card := by
  classical
  obtain ⟨f, _hfn, c0, hc0S, hdense0⟩ :=
    exists_dense_hamming_center_shell n z r_c a hz ha1 ha2
  let S := hammingSphere n z f
  let T := hammingSphere n z a
  let R := hammingSphere n z r_c
  let cover : BitString → Finset BitString :=
    fun x => T.filter (fun y => hammingDist x y = r_c)
  let m := (cover c0).card
  have hc0_len : c0.length = n :=
    (memStringsOfLength n c0).mp (Finset.mem_filter.mp hc0S).1
  have hcover_eq : ∀ x, cover x = (hammingSphere n x r_c).filter (fun y => y ∈ T) := by
    intro x
    ext y
    simp [cover, T, hammingSphere]
    tauto
  have hdense_m : R.card ≤ (n + 1) * m := by
    simpa [R, m, hcover_eq c0] using hdense0
  have hRpos : 0 < R.card := by
    have hrcn : r_c ≤ n := by omega
    dsimp [R]
    rw [hammingSphere_card n z r_c hz]
    exact Nat.choose_pos hrcn
  have hm_pos : 0 < m := by
    by_contra hnot
    have hm0 : m = 0 := by omega
    have : R.card ≤ 0 := by simpa [hm0] using hdense_m
    omega
  have hTpos : 0 < T.card := by
    have han : a ≤ n := by omega
    dsimp [T]
    rw [hammingSphere_card n z a hz]
    exact Nat.choose_pos han
  obtain ⟨y0, hy0T⟩ := Finset.card_pos.mp hTpos
  let q := ((hammingSphere n y0 r_c).filter (fun x => x ∈ S)).card
  have hrow : ∀ x ∈ S, (cover x).card = m := by
    intro x hxS
    have hreg := hammingSphere_incidence_regular n r_c f a z hz x hxS c0 hc0S
    change (cover x).card = (cover c0).card
    rw [hcover_eq x, hcover_eq c0]
    exact hreg
  have hcol : ∀ y ∈ T, ((hammingSphere n y r_c).filter (fun x => x ∈ S)).card = q := by
    intro y hyT
    have hreg := hammingSphere_incidence_regular n r_c a f z hz y hyT y0 hy0T
    simpa [q, S, hammingDist_comm] using hreg
  have hinc_filter : ∀ y ∈ T, (S.filter (fun x => y ∈ cover x)).card = q := by
    intro y hyT
    calc
      (S.filter (fun x => y ∈ cover x)).card
          = ((hammingSphere n y r_c).filter (fun x => x ∈ S)).card := by
              congr 1
              ext x
              constructor
              · intro hx
                rw [Finset.mem_filter] at hx ⊢
                rcases hx with ⟨hxS, hycov⟩
                have hx_len : x.length = n :=
                  (memStringsOfLength n x).mp (Finset.mem_filter.mp hxS).1
                refine ⟨?_, hxS⟩
                rw [hammingSphere, Finset.mem_filter]
                exact ⟨(memStringsOfLength n x).mpr hx_len,
                  by simpa [cover, hammingDist_comm] using (Finset.mem_filter.mp hycov).2⟩
              · intro hx
                rw [Finset.mem_filter] at hx ⊢
                rcases hx with ⟨hysphere, hxS⟩
                refine ⟨hxS, ?_⟩
                change y ∈ T.filter (fun y => hammingDist x y = r_c)
                rw [Finset.mem_filter]
                exact ⟨hyT, by simpa [hammingDist_comm] using (Finset.mem_filter.mp hysphere).2⟩
      _ = q := hcol y hyT
  have hq_pos : 0 < q := by
    obtain ⟨y1, hy1cover⟩ := Finset.card_pos.mp hm_pos
    have hy1T : y1 ∈ T := (Finset.mem_filter.mp hy1cover).1
    have hc0_y1 : c0 ∈ (hammingSphere n y1 r_c).filter (fun x => x ∈ S) := by
      rw [Finset.mem_filter]
      refine ⟨?_, hc0S⟩
      rw [hammingSphere, Finset.mem_filter]
      have hdist : hammingDist c0 y1 = r_c := (Finset.mem_filter.mp hy1cover).2
      exact ⟨(memStringsOfLength n c0).mpr hc0_len,
        by simpa [hammingDist_comm] using hdist⟩
    have hcol_y1 : ((hammingSphere n y1 r_c).filter (fun x => x ∈ S)).card = q :=
      hcol y1 hy1T
    rw [← hcol_y1]
    exact Finset.card_pos.mpr ⟨c0, hc0_y1⟩
  obtain ⟨C, hCS, hCcov, hCbound⟩ :=
    greedy_cover_indexed T S cover q hq_pos (fun y hy => by rw [hinc_filter y hy])
  refine ⟨C, ?_, ?_, ?_⟩
  · intro x hxC
    exact (memStringsOfLength n x).mp (Finset.mem_filter.mp (hCS hxC)).1
  · intro y hyT
    have hycov := hCcov hyT
    rw [Finset.mem_biUnion] at hycov
    obtain ⟨x, hxC, hycover⟩ := hycov
    refine ⟨x, hxC, ?_⟩
    exact le_of_eq (Finset.mem_filter.mp hycover).2
  · have hdouble : S.card * m = T.card * q := by
      calc
        S.card * m = ∑ x ∈ S, m := by rw [Finset.sum_const, smul_eq_mul]
        _ = ∑ x ∈ S, (cover x).card := by
              apply Finset.sum_congr rfl
              intro x hxS
              rw [hrow x hxS]
        _ = ∑ x ∈ S, ∑ y ∈ T, (if hammingDist x y = r_c then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro x _hxS
              rw [show cover x = T.filter (fun y => hammingDist x y = r_c) from rfl]
              rw [Finset.card_filter]
        _ = ∑ y ∈ T, ∑ x ∈ S, (if hammingDist x y = r_c then 1 else 0) := by
              rw [Finset.sum_comm]
        _ = ∑ y ∈ T, (S.filter (fun x => y ∈ cover x)).card := by
              apply Finset.sum_congr rfl
              intro y hyT
              rw [Finset.card_filter]
              apply Finset.sum_congr rfl
              intro x _hxS
              by_cases hxy : hammingDist x y = r_c
              · simp [cover, hyT, hxy]
              · simp [cover, hyT, hammingDist_comm]
        _ = ∑ y ∈ T, q := by
              apply Finset.sum_congr rfl
              intro y hyT
              rw [hinc_filter y hyT]
        _ = T.card * q := by rw [Finset.sum_const, smul_eq_mul]
    have hlog : Nat.log2 T.card ≤ n := log2_card_hammingSphere_le n z a hz
    have hCq : C.card * q ≤ S.card * (n + 1) := by
      calc C.card * q ≤ S.card * (Nat.log2 T.card + 1) := hCbound
        _ ≤ S.card * (n + 1) := Nat.mul_le_mul_left _ (by omega)
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨c0, hc0S⟩
    have hCm : C.card * m ≤ T.card * (n + 1) := by
      exact Nat.le_of_mul_le_mul_left (c := S.card) (by
        calc S.card * (C.card * m) = C.card * (S.card * m) := by ring
          _ = C.card * (T.card * q) := by rw [hdouble]
          _ = T.card * (C.card * q) := by ring
          _ ≤ T.card * (S.card * (n + 1)) := Nat.mul_le_mul_left _ hCq
          _ = S.card * (T.card * (n + 1)) := by ring) hSpos
    calc
      C.card * R.card ≤ C.card * ((n + 1) * m) := Nat.mul_le_mul_left _ hdense_m
      _ = (n + 1) * (C.card * m) := by ring
      _ ≤ (n + 1) * (T.card * (n + 1)) := Nat.mul_le_mul_left _ hCm
      _ = (n + 1) * (n + 1) * T.card := by ring

lemma hammingVol_le_mul_hammingSphere_card_of_le_half
    (n s : ℕ) (z : BitString) (hz : z.length = n) (hs : s ≤ n / 2) :
    hammingVol n s ≤ (n + 1) * (hammingSphere n z s).card := by
      -- By definition of `hammingVol`, we have `hammingVol n s = ∑ i ∈ Finset.range (s + 1),
      -- Nat.choose n i`.
      have h_hammingVol : hammingVol n s = ∑ i ∈ Finset.range (s + 1), Nat.choose n i := by
        rfl;
      rw [ h_hammingVol, hammingSphere_card n z s hz ];
      refine le_trans ( Finset.sum_le_sum fun i hi =>
          show Nat.choose n i ≤ Nat.choose n s from ?_ ) ?_;
      · have h_choose_mono : ∀ {i j : ℕ}, i ≤ j → j ≤ n / 2 → Nat.choose n i ≤ Nat.choose n j := by
          intros i j hij hjn; induction hij <;> simp_all only [Finset.mem_range,
              Order.lt_add_one_iff, le_refl, Nat.le_eq, Nat.succ_eq_add_one, Order.add_one_le_iff];
          exact le_trans ( by solve_by_elim [ Nat.le_of_lt ] )
              ( Nat.choose_le_succ_of_lt_half_left ( by omega ) );
        exact h_choose_mono ( Finset.mem_range_succ_iff.mp hi ) hs;
      · simp +arith only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm];
        exact Nat.mul_le_mul_left _ ( by omega )

lemma stringsOfLength_card_le_mul_hammingBall_card_of_half_lt
    (n r : ℕ) (z : BitString) (hz : z.length = n) (hr : n / 2 < r) :
    (stringsOfLength n).card ≤ (n + 1) * (hammingBall n z r).card := by
      have h_cube_card : (stringsOfLength n).card = ∑ i ∈ Finset.range (n + 1), Nat.choose n i := by
        rw [ cardStringsOfLength, Nat.sum_range_choose ];
      rw [ h_cube_card, mul_comm ];
      refine le_trans ?_ ( Nat.mul_le_mul_right (k :=
          n + 1) <| show ( hammingBall n z r |> Finset.card ) ≥ ( n.choose ( n / 2 ) ) from ?_ );
      · exact le_trans ( Finset.sum_le_sum fun _ _ =>
          Nat.choose_le_middle _ _ ) ( by simp [ mul_comm ] );
      · rw [ hammingBall_card ];
        · exact Finset.single_le_sum ( fun x _ =>
            Nat.zero_le ( Nat.choose n x ) ) ( Finset.mem_range.mpr ( by linarith ) );
        · exact hz

lemma hammingBall_cover_centers_of_le_half
    (n : ℕ) (z : BitString) (r c r_c : ℕ)
    (hz : z.length = n) (hc : 0 < c)
    (hr : r ≤ n / 2) (hrc : r_c ≤ r)
    (h_r_bound : c ≤ hammingVol n r)
    (h_rc_bound : c ≤ (n + 1) * hammingVol n r_c) :
    ∃ 𝒞_centers : List BitString,
      (∀ x ∈ 𝒞_centers, x.length = n) ∧
      (∀ y ∈ hammingBall n z r, ∃ x ∈ 𝒞_centers,
        hammingDist x y ≤ r_c) ∧
      𝒞_centers.length * c ≤ (n + 1)^5 * (hammingBall n z r).card := by
  have hc_and_bound : 0 < c ∧ c ≤ hammingVol n r := ⟨hc, h_r_bound⟩
  by_cases h_cases : r_c < r
  · let I := Finset.Icc (r_c + 1) r
    have h_a_rc : ∀ a ∈ I, r_c < a := fun a ha => by
      rw [Finset.mem_Icc] at ha
      exact ha.1
    have h_a_n : ∀ a ∈ I, a ≤ n / 2 := fun a ha => by
      rw [Finset.mem_Icc] at ha
      exact le_trans ha.2 hr
    have hrc_half : r_c ≤ n / 2 := hrc.trans hr
    let f : ℕ → Finset BitString := fun a =>
      if ha : a ∈ I then
        Classical.choose (hammingSphere_cover_centers n z r_c a hz (h_a_rc a ha) (h_a_n a ha))
      else ∅
    have hf_spec : ∀ a ∈ I,
        (∀ x ∈ f a, x.length = n) ∧
        (∀ y ∈ hammingSphere n z a, ∃ x ∈ f a, hammingDist x y ≤ r_c) ∧
        (f a).card * (hammingSphere n z r_c).card ≤ (n + 1)^2 * (hammingSphere n z a).card := by
      intro a ha
      simp only [f, dif_pos ha]
      have :=
          Classical.choose_spec (hammingSphere_cover_centers n z r_c a hz
            (h_a_rc a ha) (h_a_n a ha))
      refine ⟨this.1, this.2.1, ?_⟩
      calc
        _ ≤ (n + 1) * (n + 1) * (hammingSphere n z a).card := this.2.2
        _ = (n + 1)^2 * (hammingSphere n z a).card := by ring
    have hf_card : ∀ a ∈ I, (f a).card * c ≤ (n + 1)^4 * (hammingSphere n z a).card := by
      intro a ha
      have h1 := (hf_spec a ha).2.2
      have h2 : hammingVol n r_c ≤ (n + 1) * (hammingSphere n z r_c).card :=
        hammingVol_le_mul_hammingSphere_card_of_le_half n r_c z hz hrc_half
      have h3 : c ≤ (n + 1)^2 * (hammingSphere n z r_c).card := by
        calc
          c ≤ (n + 1) * hammingVol n r_c := h_rc_bound
          _ ≤ (n + 1) * ((n + 1) * (hammingSphere n z r_c).card) := Nat.mul_le_mul_left _ h2
          _ = (n + 1)^2 * (hammingSphere n z r_c).card := by ring
      calc
        (f a).card * c ≤ (f a).card * ((n + 1)^2 * (hammingSphere n z r_c).card) :=
            Nat.mul_le_mul_left _ h3
        _ = (n + 1)^2 * ((f a).card * (hammingSphere n z r_c).card) := by ring
        _ ≤ (n + 1)^2 * ((n + 1)^2 * (hammingSphere n z a).card) := Nat.mul_le_mul_left _ h1
        _ = (n + 1)^4 * (hammingSphere n z a).card := by ring
    let 𝒞_centers := I.biUnion f
    have hC_len : ∀ x ∈ 𝒞_centers, x.length = n := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      rcases hx with ⟨a, ha, hxa⟩
      exact (hf_spec a ha).1 x hxa
    have hC_cov : ∀ y ∈ (stringsOfLength n).filter (fun y =>
        r_c < hammingDist z y ∧ hammingDist z y ≤ r), ∃ x ∈ 𝒞_centers,
          hammingDist x y ≤ r_c := by
      intro y hy
      rw [Finset.mem_filter] at hy
      have hd := hy.2
      have ha : hammingDist z y ∈ I := by
        rw [Finset.mem_Icc]
        exact ⟨hd.1, hd.2⟩
      have hy_sphere : y ∈ hammingSphere n z (hammingDist z y) := by
        rw [hammingSphere, Finset.mem_filter]
        exact ⟨hy.1, rfl⟩
      obtain ⟨x, hx_f, hx_dist⟩ := (hf_spec (hammingDist z y) ha).2.1 y hy_sphere
      refine ⟨x, ?_, hx_dist⟩
      rw [Finset.mem_biUnion]
      exact ⟨hammingDist z y, ha, hx_f⟩
    have hC_card : 𝒞_centers.card * c ≤ (n + 1)^4 * (hammingBall n z r).card := by
      calc
        𝒞_centers.card * c ≤ (∑ a ∈ I, (f a).card) * c :=
            Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ a ∈ I, (f a).card * c := Finset.sum_mul _ _ _
        _ ≤ ∑ a ∈ I, (n + 1)^4 * (hammingSphere n z a).card :=
            Finset.sum_le_sum (fun a ha => hf_card a ha)
        _ = (n + 1)^4 * ∑ a ∈ I, (hammingSphere n z a).card := (Finset.mul_sum _ _ _).symm
        _ ≤ (n + 1)^4 * ∑ a ∈ Finset.range (r + 1), (hammingSphere n z a).card :=
            Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (fun a ha => by
          rw [Finset.mem_Icc] at ha
          rw [Finset.mem_range]
          exact Nat.lt_succ_of_le ha.2))
        _ = (n + 1)^4 * (hammingBall n z r).card := by rw [sum_hammingSphere_card]
    refine ⟨𝒞_centers.toList ++ [z], ?_, ?_, ?_⟩
    · intro x hx
      rw [List.mem_append] at hx
      cases hx with
      | inl hx => exact hC_len x (Finset.mem_toList.mp hx)
      | inr hx =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]
        exact hz
    · intro y hy
      by_cases hdist : hammingDist z y ≤ r_c
      · refine ⟨z, List.mem_append.mpr (Or.inr (List.mem_singleton_self z)), hdist⟩
      · rw [not_le] at hdist
        have hy_filter : y ∈ (stringsOfLength n).filter (fun y =>
            r_c < hammingDist z y ∧ hammingDist z y ≤ r) := by
          rw [Finset.mem_filter]
          rw [hammingBall, Finset.mem_filter] at hy
          exact ⟨hy.1, hdist, hy.2⟩
        obtain ⟨x, hxC, hx_dist⟩ := hC_cov y hy_filter
        have hxC' : x ∈ 𝒞_centers.toList := by exact Finset.mem_toList.mpr hxC
        exact ⟨x, List.mem_append.mpr (Or.inl hxC'), hx_dist⟩
    · calc
        (𝒞_centers.toList ++ [z]).length * c = (𝒞_centers.card + 1) * c := by simp
        _ = 𝒞_centers.card * c + c := by ring
        _ ≤ (n + 1)^4 * (hammingBall n z r).card + c := Nat.add_le_add_right hC_card c
        _ ≤ (n + 1)^4 * (hammingBall n z r).card + (n + 1)^4 * (hammingBall n z r).card := by
          refine Nat.add_le_add_left ?_ _
          calc
            c ≤ hammingVol n r := hc_and_bound.2
            _ = (hammingBall n z r).card := (hammingBall_card n z r hz).symm
            _ = 1 * (hammingBall n z r).card := (one_mul _).symm
            _ ≤ (n + 1)^4 * (hammingBall n z r).card := Nat.mul_le_mul_right _ (by
              have hpos : 1 ≤ n + 1 := by omega
              exact Nat.one_le_pow 4 (n + 1) hpos)
        _ = 2 * ((n + 1)^4 * (hammingBall n z r).card) := by ring
        _ ≤ (n + 1) * ((n + 1)^4 * (hammingBall n z r).card) := Nat.mul_le_mul_right _ (by
          have : 2 ≤ n + 1 := by omega
          exact this)
        _ = (n + 1)^5 * (hammingBall n z r).card := by ring
  · refine ⟨[z], ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]
      exact hz
    · intro y hy
      refine ⟨z, by simp, ?_⟩
      rw [hammingBall, Finset.mem_filter] at hy
      linarith
    · calc
        [z].length * c = c := by simp
        _ ≤ hammingVol n r := hc_and_bound.2
        _ = (hammingBall n z r).card := (hammingBall_card n z r hz).symm
        _ = 1 * (hammingBall n z r).card := (one_mul _).symm
        _ ≤ (n + 1)^5 * (hammingBall n z r).card := Nat.mul_le_mul_right _ (by
          have hpos : 1 ≤ n + 1 := Nat.le_add_left 1 n
          exact Nat.one_le_pow 5 (n + 1) hpos)

/-- Cover a Hamming ball by Hamming balls of the largest radius whose volume
does not exceed `c`.  The public statement is unchanged; its proof must use
the sphere-wise construction above, not a lower bound on
`B(z,r) \cap B(y,r_c)` for every boundary point `y`. -/
theorem hammingBall_cover_centers (n : ℕ) (z : BitString) (r c r_c : ℕ)
    (hz : z.length = n) (hc : 0 < c)
    (h_r_bound : c ≤ hammingVol n r)
    (h_rc_vol : hammingVol n r_c ≤ c) (h_rc_next : c ≤ hammingVol n (r_c + 1))
    (h_rc_bound : c ≤ (n + 1) * hammingVol n r_c) :
    ∃ 𝒞_centers : List BitString,
      (∀ x ∈ 𝒞_centers, x.length = n) ∧
      (∀ y ∈ hammingBall n z r, ∃ x ∈ 𝒞_centers, hammingDist x y ≤ r_c) ∧
      𝒞_centers.length * c ≤ (n + 1)^7 * (hammingBall n z r).card := by
  by_cases hn : n = 0
  · have hz0 : z = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    subst z
    subst n
    refine ⟨[[]], by simp, ?_, ?_⟩
    · intro y hy
      have hylen : y.length = 0 :=
        (memStringsOfLength 0 y).mp (Finset.mem_filter.mp hy).1
      have hy0 : y = [] := List.eq_nil_of_length_eq_zero hylen
      subst y
      simp [hammingDist]
    · have hvol : hammingVol 0 r = 1 := by
        have hle := hammingVol_le_two_pow 0 r
        have hpos := hammingVol_pos 0 r
        norm_num at hle ⊢
        omega
      have hc1 : c = 1 := by omega
      subst c
      have hmem : [] ∈ hammingBall 0 [] r := by
        simp [hammingBall, stringsOfLength, hammingDist]
      exact Finset.card_pos.mpr ⟨[], hmem⟩
  · by_cases hr : r ≤ n / 2
    · have hrn : r < n := by omega
      have hrc : r_c ≤ r :=
        hammingRadius_le_of_volume_le h_rc_vol h_r_bound hrn
      obtain ⟨C, hClen, hCcov, hCcard⟩ :=
        hammingBall_cover_centers_of_le_half n z r c r_c hz hc hr hrc
          h_r_bound h_rc_bound
      refine ⟨C, hClen, hCcov, hCcard.trans ?_⟩
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))
    · have hrhalf : n / 2 < r := by omega
      obtain ⟨C, hClen, hCcov, hCcard⟩ :=
        hamming_probabilistic_cover n r_c (hammingVol n r_c)
          (hammingVol_pos n r_c) le_rfl
      refine ⟨C, hClen, ?_, ?_⟩
      · intro y hy
        exact hCcov y (Finset.mem_filter.mp hy).1
      · have hcube :=
          stringsOfLength_card_le_mul_hammingBall_card_of_half_lt n r z hz hrhalf
        calc
          C.length * c ≤ C.length * ((n + 1) * hammingVol n r_c) :=
            Nat.mul_le_mul_left _ h_rc_bound
          _ = (n + 1) * (C.length * hammingVol n r_c) := by ring
          _ ≤ (n + 1) * ((n + 1) * (stringsOfLength n).card) :=
            Nat.mul_le_mul_left _ hCcard
          _ ≤ (n + 1) * ((n + 1) * ((n + 1) *
              (hammingBall n z r).card)) := by
            gcongr
          _ = (n + 1)^3 * (hammingBall n z r).card := by ring
          _ ≤ (n + 1)^7 * (hammingBall n z r).card :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))

/-- Condition (3) covering theorem using the probabilistic covering lemma. -/
theorem hammingFamily_cover {A : Finset BitString} (hA : hammingFamilyMem A)
    (n c : ℕ) (hc : 0 < c) (hcA : c ≤ A.card) :
    ∃ 𝒞 : List (Finset BitString),
      (∀ B ∈ 𝒞, hammingFamilyMem B ∧ B.card ≤ c) ∧
      (∀ x ∈ A, x.length = n → ∃ B ∈ 𝒞, x ∈ B) ∧
      𝒞.length * c ≤ hammingOverhead n * A.card := by
  by_cases hc_eq : A.card ≤ c
  · use [A]
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      simp only [List.mem_singleton] at hB
      subst hB
      exact ⟨hA, hc_eq⟩
    · intro x hxA _
      exact ⟨A, by simp, hxA⟩
    · have hc_eq_exact : c = A.card := le_antisymm hcA hc_eq
      have h_oh : 1 ≤ hammingOverhead n := hammingOverhead_pos n
      calc
        [A].length * c = 1 * A.card := by rw [List.length_singleton, hc_eq_exact]
        _ ≤ hammingOverhead n * A.card := Nat.mul_le_mul_right A.card h_oh
  · rcases hA with ⟨m, z, r, hzlen, hA_eq⟩
    by_cases hmn : m = n
    · have h_c_le : c ≤ 2^n := by
        refine le_trans hcA ?_
        rw [hmn] at hA_eq hzlen
        rw [hA_eq, hammingBall_card n z r hzlen]
        exact hammingVol_le_two_pow n r
      have hzlen' : z.length = n := by rw [← hmn]; exact hzlen
      obtain ⟨r_c, h_vol_le, h_vol_bound, h_vol_next⟩ :=
        exists_hamming_radius_for_volume n c hc h_c_le
      have hA_eq' : A = hammingBall n z r := by rw [← hmn, hA_eq]
      have h_r_bound : c < hammingVol n r := by
        have : c < A.card := lt_of_not_ge hc_eq
        rwa [hA_eq', hammingBall_card n z r hzlen'] at this
      obtain ⟨centers, h_centers_len, h_cover, h_count⟩ :=
        hammingBall_cover_centers n z r c r_c hzlen' hc
          (le_of_lt h_r_bound) h_vol_le h_vol_next h_vol_bound
      use centers.map (fun x => hammingBall n x r_c)
      refine ⟨?_, ?_, ?_⟩
      · intro B hB
        rw [List.mem_map] at hB
        rcases hB with ⟨x, hx_mem, rfl⟩
        refine ⟨⟨n, x, r_c, h_centers_len x hx_mem, rfl⟩, ?_⟩
        rw [hammingBall_card n x r_c (h_centers_len x hx_mem)]
        exact h_vol_le
      · intro x hxA hxlen
        rw [hA_eq'] at hxA
        obtain ⟨y, hy_mem, h_dist⟩ := h_cover x hxA
        refine ⟨hammingBall n y r_c, ?_, ?_⟩
        · rw [List.mem_map]
          exact ⟨y, hy_mem, rfl⟩
        · rw [hammingBall, Finset.mem_filter]
          refine ⟨(memStringsOfLength n x).mpr hxlen, h_dist⟩
      · rw [List.length_map]
        unfold hammingOverhead
        have : A.card = (hammingBall n z r).card := by rw [hA_eq']
        rw [this]
        exact h_count
    · use []
      refine ⟨by simp, ?_, by simp⟩
      intro x hxA hxlen
      rw [hA_eq, hammingBall, Finset.mem_filter] at hxA
      have hx_m : x.length = m := (memStringsOfLength m x).mp hxA.1
      omega

/-- The Hamming family instance. -/
noncomputable def hammingFamily : DescriptionFamily where
  mem := hammingFamilyMem
  nonempty_of_mem := @hammingFamilyMem_nonempty
  enumeration := {
    enum := hammingEnum
    computable := hammingEnum_computable
    mono := hammingEnum_mono
    sound := hammingEnum_sound
    complete := hammingEnum_complete
  }
  fullCube := hammingFamily_fullCube
  overhead := hammingOverhead
  overhead_pos := hammingOverhead_pos
  cover := @hammingFamily_cover

lemma hammingFamily_hasPolynomialOverhead : hammingFamily.HasPolynomialOverhead := by
  refine ⟨1, 7, by decide, ?_⟩
  intro n
  simp [hammingFamily, hammingOverhead]

end Kolmogorov
