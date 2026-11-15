/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubsequences.RestrictionBounds

/-!
# Valid Assignments

Valid partial assignments for sets of restrictions, and the direct proof of Muchnik and Semenov
for forbidden subsequences.  A partial assignment on a finite set `I` of cells is *valid* if it
violates no restriction of a given set `R`; `validCount R I` is the number of valid assignments.

Main declarations:
* `IsValidAssignment`, `validCount`: valid assignments on `I` and their number `c(I)`;
* `exists_threshold_validCount`: if `R` is `α`-bounded and all its restrictions are large enough,
  then adding a cell multiplies `c(I)` by at least `2 ^ β` for `α < β < 1`;
* the two-dimensional application, in which one fills a grid avoiding forbidden rectangles.

This formalizes the direct combinatorial proof from the chapter on forbidden subsequences in the
book of Shen, Uspensky and Vereshchagin, *Kolmogorov complexity and algorithmic randomness*.
-/

namespace Kolmogorov.Applications

/-! ### The direct proof of Muchnik and Semenov -/

/-- A partial assignment on `I` is a function `I → Bool`, one of the `2^|I|` assignments.  It is
*valid* if no restriction `(F, X)` with `F ⊆ I` is violated by it. -/
def IsValidAssignment (R : Set Restriction) (I : Finset ℕ) (a : I → Bool) : Prop :=
  ∀ r ∈ R, ∀ h : r.indices ⊆ I,
    (r.indices.sort (· ≤ ·)).attach.map (fun i =>
      a ⟨i.1, h ((Finset.mem_sort (· ≤ ·)).1 i.2)⟩) ≠ r.values

open Classical in
/-- **SUV p. 250.**  The number `c(I)` of valid partial assignments on `I`.  One has `c(∅) = 1`
provided `R` has no empty restriction, as in the book's sufficiently-large-size setting.
Without that condition an empty restriction forbids even the empty assignment. -/
noncomputable def validCount (R : Set Restriction) (I : Finset ℕ) : ℕ :=
  (Finset.univ.filter (IsValidAssignment R I)).card


/-- Step 1 of the proof of `exists_threshold_validCount`: Bound the infinite sum. -/
private lemma exists_threshold_validCount_series_bound {α β : ℝ} (hαβ : α < β) (hβ : β < 1) :
    ∃ N : ℕ, 0 < N ∧ ∀ M : ℕ, (∑ k ∈ Finset.Ico (N - 1) (M + 1), (2 : ℝ) ^ (α * (k + 1) - β * k)) ≤
        2 - (2 : ℝ) ^ β := by
  set q : ℝ := (2 : ℝ) ^ (α - β) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hε : 0 < 2 - (2 : ℝ) ^ β := by
    have : (2 : ℝ) ^ β < (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hβ
    rw [Real.rpow_one] at this
    linarith
  have hA : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have h1q : 0 < 1 - q := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < (2 - (2 : ℝ) ^ β) * (1 - q) / (2 : ℝ) ^ α by positivity) hq1
  refine ⟨n + 1, Nat.succ_pos n, fun M => ?_⟩
  have hterm : ∀ k : ℕ, (2 : ℝ) ^ (α * ((k : ℝ) + 1) - β * k) = (2 : ℝ) ^ α * q ^ k := by
    intro k
    have h1 : α * ((k : ℝ) + 1) - β * k = α + (α - β) * k := by ring
    rw [h1, Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_natCast]
  simp only [hterm]
  rw [← Finset.mul_sum]
  have hg := geom_sum_Ico_le_of_lt_one (m := n + 1 - 1) (n := M + 1) hq0.le hq1
  have hn' : q ^ (n + 1 - 1) < (2 - (2 : ℝ) ^ β) * (1 - q) / (2 : ℝ) ^ α := by
    simpa using hn
  calc (2 : ℝ) ^ α * ∑ k ∈ Finset.Ico (n + 1 - 1) (M + 1), q ^ k
      ≤ (2 : ℝ) ^ α * (q ^ (n + 1 - 1) / (1 - q)) :=
        mul_le_mul_of_nonneg_left hg hA.le
    _ ≤ 2 - (2 : ℝ) ^ β := by
        rw [← mul_div_assoc, div_le_iff₀ h1q]
        rw [lt_div_iff₀ hA] at hn'
        nlinarith

/-- The total extension of an assignment on `J` by `false` outside `J`. -/
private def exists_threshold_validCount_lost_bound_tot (J : Finset ℕ) (a : J → Bool) :
    ℕ → Bool :=
  fun j => if h : j ∈ J then a ⟨j, h⟩ else false

/-- The extension of an assignment on `I` by the value `b` at `i`. -/
private def exists_threshold_validCount_lost_bound_ext {I : Finset ℕ} (i : ℕ)
    (a : I → Bool) (b : Bool) : ↥(insert i I) → Bool :=
  fun j => if h : j.1 ∈ I then a ⟨j.1, h⟩ else b

/-- The restriction of an assignment to a subset. -/
private def exists_threshold_validCount_lost_bound_res {I J : Finset ℕ} (h : J ⊆ I)
    (a : I → Bool) : J → Bool :=
  fun j => a ⟨j.1, h j.2⟩

private lemma exists_threshold_validCount_lost_bound_tot_ext {I : Finset ℕ} {i : ℕ}
    (hi : i ∉ I) (a : I → Bool) (b : Bool) :
    exists_threshold_validCount_lost_bound_tot (insert i I)
        (exists_threshold_validCount_lost_bound_ext i a b) =
      Function.update (exists_threshold_validCount_lost_bound_tot I a) i b := by
  funext j
  unfold exists_threshold_validCount_lost_bound_tot
    exists_threshold_validCount_lost_bound_ext
  by_cases hji : j = i
  · subst hji
    simp [hi]
  · by_cases hj : j ∈ I
    · simp [hji, hj]
    · simp [hji, hj]

private lemma exists_threshold_validCount_lost_bound_valid_iff {R : Set Restriction}
    {J : Finset ℕ} (a : J → Bool) :
    IsValidAssignment R J a ↔
      ∀ r ∈ R, r.indices ⊆ J →
        restrictBits (exists_threshold_validCount_lost_bound_tot J a) r.indices ≠
          r.values := by
  have key : ∀ (r : Restriction) (h : r.indices ⊆ J),
      (r.indices.sort (· ≤ ·)).attach.map (fun i =>
        a ⟨i.1, h ((Finset.mem_sort (· ≤ ·)).1 i.2)⟩) =
        restrictBits (exists_threshold_validCount_lost_bound_tot J a) r.indices := by
    intro r h
    unfold restrictBits
    rw [← List.attach_map_val (l := r.indices.sort (· ≤ ·))
      (f := exists_threshold_validCount_lost_bound_tot J a)]
    apply List.map_congr_left
    intro x _
    simp [exists_threshold_validCount_lost_bound_tot,
      h ((Finset.mem_sort (· ≤ ·)).1 x.2)]
  unfold IsValidAssignment
  constructor
  · intro h r hr hrJ
    rw [← key r hrJ]
    exact h r hr hrJ
  · intro h r hr hrJ
    rw [key r hrJ]
    exact h r hr hrJ

private lemma exists_threshold_validCount_lost_bound_tot_res {I J : Finset ℕ} (h : J ⊆ I)
    (a : I → Bool) {j : ℕ} (hj : j ∈ J) :
    exists_threshold_validCount_lost_bound_tot J
        (exists_threshold_validCount_lost_bound_res h a) j =
      exists_threshold_validCount_lost_bound_tot I a j := by
  simp [exists_threshold_validCount_lost_bound_tot,
    exists_threshold_validCount_lost_bound_res, hj, h hj]

private lemma exists_threshold_validCount_lost_bound_res_valid {R : Set Restriction}
    {I J : Finset ℕ} (h : J ⊆ I) {a : I → Bool} (ha : IsValidAssignment R I a) :
    IsValidAssignment R J (exists_threshold_validCount_lost_bound_res h a) := by
  rw [exists_threshold_validCount_lost_bound_valid_iff] at ha ⊢
  intro r hr hrJ heq
  apply ha r hr (hrJ.trans h)
  rw [← heq]
  symm
  rw [exists_not_forbidden_restrictBits_eq_iff]
  intro j hj
  exact exists_threshold_validCount_lost_bound_tot_res h a (hrJ hj)

open Classical in
private lemma exists_threshold_validCount_lost_bound_bound_r {R : Set Restriction}
    {I : Finset ℕ} {i : ℕ} (hi : i ∉ I) {r : Restriction} (hir : i ∈ r.indices) :
    ((Finset.univ.filter (IsValidAssignment R I) ×ˢ (Finset.univ : Finset Bool)).filter
      (fun p => restrictBits (exists_threshold_validCount_lost_bound_tot (insert i I)
        (exists_threshold_validCount_lost_bound_ext i p.1 p.2)) r.indices =
          r.values)).card ≤ validCount R (I \ (r.indices \ {i})) := by
  unfold validCount
  have hsub : I \ (r.indices \ {i}) ⊆ I := Finset.sdiff_subset
  apply Finset.card_le_card_of_injOn
    (fun p => exists_threshold_validCount_lost_bound_res hsub p.1)
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, and_true, true_and] at hp ⊢
    exact exists_threshold_validCount_lost_bound_res_valid hsub hp.1
  · intro p hp p' hp' hpp'
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, and_true, true_and] at hp hp'
    obtain ⟨_, hpf⟩ := hp
    obtain ⟨_, hpf'⟩ := hp'
    have hpp'' : exists_threshold_validCount_lost_bound_res hsub p.1 =
        exists_threshold_validCount_lost_bound_res hsub p'.1 := hpp'
    have hw := exists_not_forbidden_restrictBits_eq_iff.1 (hpf.trans hpf'.symm)
    simp only [exists_threshold_validCount_lost_bound_tot_ext hi] at hw
    have hbool : p.2 = p'.2 := by
      have := hw i hir
      simpa using this
    have ha : p.1 = p'.1 := by
      funext ⟨j, hj⟩
      by_cases hjK : j ∈ r.indices \ {i}
      · have hjr : j ∈ r.indices := (Finset.mem_sdiff.1 hjK).1
        have hji : j ≠ i := by simpa using (Finset.mem_sdiff.1 hjK).2
        have := hw j hjr
        simpa [Function.update_apply, hji,
          exists_threshold_validCount_lost_bound_tot, hj] using this
      · have hjD : j ∈ I \ (r.indices \ {i}) := Finset.mem_sdiff.2 ⟨hj, hjK⟩
        have := congrFun hpp'' ⟨j, hjD⟩
        simpa [exists_threshold_validCount_lost_bound_res] using this
    exact Prod.ext ha hbool

private lemma exists_threshold_validCount_lost_bound_finite (R : Set Restriction)
    (i n : ℕ) (K : Finset ℕ) :
    ({r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} : Set Restriction).Finite := by
  apply Set.Finite.of_finite_image (f := Restriction.values)
  · apply (List.finite_length_eq Bool n).subset
    rintro l ⟨r, ⟨_, hrn, _⟩, rfl⟩
    exact hrn
  · rintro r ⟨_, _, hir, hrK⟩ r' ⟨_, _, hir', hrK'⟩ hv
    have hind : r.indices = r'.indices := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [hir, hir']
      · have h1 := Finset.ext_iff.1 hrK j
        have h2 := Finset.ext_iff.1 hrK' j
        simp only [Finset.mem_sdiff, Finset.mem_singleton, hji, not_false_eq_true, and_true]
          at h1 h2
        rw [h1, h2]
    cases r
    cases r'
    simp only at hind hv
    subst hind
    subst hv
    rfl

open Classical in
private lemma exists_threshold_validCount_lost_bound_nat {R : Set Restriction}
    {I : Finset ℕ} {i : ℕ} (hi : i ∉ I) (N : ℕ) (h_size : ∀ r ∈ R, N ≤ r.size) :
    validCount R I * 2 ≤ validCount R (insert i I) +
      ∑ n ∈ Finset.Ico N (I.card + 2),
        ∑ K ∈ (Finset.powerset I).filter (fun K => K.card = n - 1),
          ({r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} :
            Set Restriction).ncard * validCount R (I \ K) := by
  have hfin := exists_threshold_validCount_lost_bound_finite R i
  set P : Finset ((I → Bool) × Bool) :=
    Finset.univ.filter (IsValidAssignment R I) ×ˢ (Finset.univ : Finset Bool) with hP
  have hPcard : P.card = validCount R I * 2 := by
    rw [hP, Finset.card_product, Finset.card_univ, Fintype.card_bool]
    rfl
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := P) (fun p => IsValidAssignment R (insert i I)
      (exists_threshold_validCount_lost_bound_ext i p.1 p.2))
  -- good part
  have hgood : (P.filter (fun p => IsValidAssignment R (insert i I)
      (exists_threshold_validCount_lost_bound_ext i p.1 p.2))).card ≤
        validCount R (insert i I) := by
    unfold validCount
    apply Finset.card_le_card_of_injOn
      (fun p => exists_threshold_validCount_lost_bound_ext i p.1 p.2)
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ,
        true_and] at hp ⊢
      exact hp.2
    · intro p hp p' hp' hpp'
      have hpp'' : exists_threshold_validCount_lost_bound_ext i p.1 p.2 =
          exists_threshold_validCount_lost_bound_ext i p'.1 p'.2 := hpp'
      have hbool : p.2 = p'.2 := by
        have := congrFun hpp'' ⟨i, Finset.mem_insert_self i I⟩
        simpa [exists_threshold_validCount_lost_bound_ext, hi] using this
      have ha : p.1 = p'.1 := by
        funext ⟨j, hj⟩
        have := congrFun hpp'' ⟨j, Finset.mem_insert_of_mem hj⟩
        simpa [exists_threshold_validCount_lost_bound_ext, hj] using this
      exact Prod.ext ha hbool
  -- bad part
  have hbad : (P.filter (fun p => ¬ IsValidAssignment R (insert i I)
      (exists_threshold_validCount_lost_bound_ext i p.1 p.2))).card ≤
      ∑ n ∈ Finset.Ico N (I.card + 2),
        ∑ K ∈ (Finset.powerset I).filter (fun K => K.card = n - 1),
          ({r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} :
            Set Restriction).ncard * validCount R (I \ K) := by
    have hsub : P.filter (fun p => ¬ IsValidAssignment R (insert i I)
        (exists_threshold_validCount_lost_bound_ext i p.1 p.2)) ⊆
        (Finset.Ico N (I.card + 2)).biUnion (fun n =>
          ((Finset.powerset I).filter (fun K => K.card = n - 1)).biUnion (fun K =>
            (hfin n K).toFinset.biUnion (fun r =>
              P.filter (fun p => restrictBits
                (exists_threshold_validCount_lost_bound_tot (insert i I)
                  (exists_threshold_validCount_lost_bound_ext i p.1 p.2)) r.indices =
                    r.values)))) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpP, hpn⟩ := hp
      have hpa : IsValidAssignment R I p.1 := by
        rw [hP, Finset.mem_product, Finset.mem_filter] at hpP
        exact hpP.1.2
      rw [exists_threshold_validCount_lost_bound_valid_iff] at hpn
      push Not at hpn
      obtain ⟨r, hr, hrI, heq⟩ := hpn
      have hir : i ∈ r.indices := by
        by_contra hir
        have hrI' : r.indices ⊆ I := by
          intro j hj
          rcases Finset.mem_insert.1 (hrI hj) with h | h
          · exact absurd (h ▸ hj) hir
          · exact h
        rw [exists_threshold_validCount_lost_bound_valid_iff] at hpa
        apply hpa r hr hrI'
        rw [← heq]
        symm
        rw [exists_not_forbidden_restrictBits_eq_iff]
        intro j hj
        have hji : j ≠ i := fun h => hir (h ▸ hj)
        simp [exists_threshold_validCount_lost_bound_tot_ext hi,
          hji]
      have hKI : r.indices \ {i} ⊆ I := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_sdiff.1 hj
        rcases Finset.mem_insert.1 (hrI hj1) with h | h
        · exact absurd (by simpa using h) (by simpa using hj2)
        · exact h
      have hcard : r.size = r.indices.card := r.length_eq
      have hKcard : (r.indices \ {i}).card = r.size - 1 := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hir, hcard]
      have hle : r.indices.card ≤ I.card + 1 := by
        calc r.indices.card ≤ (insert i I).card := Finset.card_le_card hrI
          _ ≤ I.card + 1 := Finset.card_insert_le _ _
      refine Finset.mem_biUnion.2 ⟨r.size, Finset.mem_Ico.2 ⟨h_size r hr, by omega⟩,
        Finset.mem_biUnion.2 ⟨r.indices \ {i}, Finset.mem_filter.2
          ⟨Finset.mem_powerset.2 hKI, hKcard⟩, Finset.mem_biUnion.2 ⟨r,
          (hfin _ _).mem_toFinset.2 ⟨hr, rfl, hir, rfl⟩, Finset.mem_filter.2 ⟨hpP, heq⟩⟩⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun n _ => Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun K hK => Finset.card_biUnion_le.trans ?_)))
    have hKsub := Finset.mem_powerset.1 (Finset.mem_filter.1 hK).1
    calc ∑ r ∈ (hfin n K).toFinset, (P.filter (fun p => restrictBits
            (exists_threshold_validCount_lost_bound_tot (insert i I)
              (exists_threshold_validCount_lost_bound_ext i p.1 p.2)) r.indices =
                r.values)).card
        ≤ ∑ r ∈ (hfin n K).toFinset, validCount R (I \ K) := by
          apply Finset.sum_le_sum
          intro r hr
          obtain ⟨_, _, hir, hrK⟩ := (hfin n K).mem_toFinset.1 hr
          have := exists_threshold_validCount_lost_bound_bound_r (R := R) hi hir
          rw [hrK] at this
          exact this
      _ = ({r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} :
            Set Restriction).ncard * validCount R (I \ K) := by
          rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card _ (hfin n K)]
  omega

/-- Step 2 of the proof of `exists_threshold_validCount`: Bound the number of lost
assignments by summing over the sizes of the sets `K`. -/
private lemma exists_threshold_validCount_lost_bound {R : Set Restriction} {I : Finset ℕ} {i :
    ℕ} (hi : i ∉ I)
    (N : ℕ) (h_size : ∀ r ∈ R, N ≤ r.size) :
    (validCount R I : ℝ) * 2 - validCount R (insert i I) ≤
      ∑ n ∈ Finset.Ico N (I.card + 2),
        ∑ K ∈ (Finset.powerset I).filter (fun K => K.card = n - 1),
          (( {r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} : Set Restriction).ncard :
              ℝ) *
            validCount R (I \ K) := by
  have h := exists_threshold_validCount_lost_bound_nat hi N h_size
  have h' : ((validCount R I * 2 : ℕ) : ℝ) ≤ ((validCount R (insert i I) +
      ∑ n ∈ Finset.Ico N (I.card + 2),
        ∑ K ∈ (Finset.powerset I).filter (fun K => K.card = n - 1),
          ({r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} :
            Set Restriction).ncard * validCount R (I \ K) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- Step 3 of the proof of `exists_threshold_validCount`: Rearrange the sum and apply the
induction hypothesis. -/
private lemma exists_threshold_validCount_sum_rearrange {R : Set Restriction} {α β : ℝ} {I :
    Finset ℕ} {i : ℕ}
    (hR : IsBoundedRestrictions α R)
    (n : ℕ) (hn : 0 < n)
    (h_ind : ∀ J ⊆ I, (2 : ℝ) ^ (β * J.card) * (validCount R (I \ J) : ℝ) ≤ validCount R I) :
    ∑ K ∈ (Finset.powerset I).filter (fun K => K.card = n - 1),
          (( {r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} : Set Restriction).ncard :
              ℝ) *
            validCount R (I \ K) ≤ (2 : ℝ) ^ (α * n) * ((validCount R I : ℝ) / (2 : ℝ) ^ (β * (n -
                1))) := by
  classical
  obtain ⟨hfin, hcard⟩ := hR i n hn
  set X : ℝ := (validCount R I : ℝ) / (2 : ℝ) ^ (β * (n - 1)) with hX
  have hX0 : 0 ≤ X := by positivity
  have hterm : ∀ K ∈ (Finset.powerset I).filter (fun K => K.card = n - 1),
      (( {r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} : Set Restriction).ncard : ℝ) *
        validCount R (I \ K) ≤
      (( {r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} : Set Restriction).ncard : ℝ) *
          X := by
    intro K hK
    rw [Finset.mem_filter, Finset.mem_powerset] at hK
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h := h_ind K hK.1
    rw [hK.2] at h
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at h
    rw [hX, le_div_iff₀ (by positivity)]
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hX0
  refine le_trans ?_ hcard
  set T := hfin.toFinset with hT
  have hset : ∀ K : Finset ℕ,
      ({r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} : Set Restriction).ncard =
        (T.filter (fun r => r.indices \ {i} = K)).card := by
    intro K
    rw [← Set.ncard_coe_finset]
    congr 1
    ext r
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, hT, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hrR, h1, h2, h3⟩
      exact ⟨⟨hrR, h1, h2⟩, by rw [h3]⟩
    · rintro ⟨⟨hrR, h1, h2⟩, h3⟩
      refine ⟨hrR, h1, h2, ?_⟩
      rw [h3]
  have hsum : (∑ K ∈ (Finset.powerset I).filter (fun K => K.card = n - 1),
      (({r ∈ R | r.size = n ∧ i ∈ r.indices ∧ r.indices \ {i} = ↑K} : Set Restriction).ncard : ℝ)) =
      ((∑ K ∈ (Finset.powerset I).filter (fun K => K.card = n - 1),
        (T.filter (fun r => r.indices \ {i} = K)).card : ℕ) : ℝ) := by
    push_cast
    exact Finset.sum_congr rfl (fun K _ => by rw [hset])
  rw [hsum]
  have h1 := Finset.sum_card_fiberwise_eq_card_filter
    (s := T) (t := (Finset.powerset I).filter (fun K => K.card = n - 1))
    (g := fun r : Restriction => r.indices \ {i})
  have h2 : (T.filter (fun r => r.indices \ {i} ∈ (Finset.powerset I).filter (fun K => K.card = n -
      1))).card ≤ T.card :=
    Finset.card_filter_le _ _
  have h3 : ((T.card : ℕ) : ℝ) = (({r ∈ R | r.size = n ∧ i ∈ r.indices} : Set Restriction).ncard :
      ℝ) := by
    rw [hT, ← Set.ncard_eq_toFinset_card _ hfin]
  rw [← h3]
  exact_mod_cast h1.trans_le h2

/-- Step 4 of the proof of `exists_threshold_validCount`: Combine the previous two steps
to get a bound on the lost assignments in terms of the sum from step 1. -/
private lemma exists_threshold_validCount_step4_lost_bound {R : Set Restriction} {α β : ℝ} {I :
    Finset ℕ} {i : ℕ} (hi : i ∉ I)
    (hR : IsBoundedRestrictions α R)
    (N : ℕ) (hN_pos : 0 < N) (h_size : ∀ r ∈ R, N ≤ r.size)
    (h_ind : ∀ J ⊆ I, (2 : ℝ) ^ (β * J.card) * (validCount R (I \ J) : ℝ) ≤ validCount R I) :
    (validCount R I : ℝ) * 2 - validCount R (insert i I) ≤
      ∑ n ∈ Finset.Ico N (I.card + 2),
        (2 : ℝ) ^ (α * n) * ((validCount R I : ℝ) / (2 : ℝ) ^ (β * (n - 1))) :=
  (exists_threshold_validCount_lost_bound hi N h_size).trans
    (Finset.sum_le_sum fun n hn =>
      exists_threshold_validCount_sum_rearrange hR n
        (lt_of_lt_of_le hN_pos (Finset.mem_Ico.1 hn).1) h_ind)

/-- Step 5 of the proof of `exists_threshold_validCount`: Perform the induction step using
the bound on the sum. -/
private lemma exists_threshold_validCount_induction {α β : ℝ}
    (N : ℕ) (hN_pos : 0 < N)
    (hN : ∀ M : ℕ, (∑ k ∈ Finset.Ico (N - 1) (M + 1), (2 : ℝ) ^ (α * (k + 1) - β * k)) ≤ 2 - (2 : ℝ)
        ^ β)
    (R : Set Restriction) (hR : IsBoundedRestrictions α R) (h_size : ∀ r ∈ R, N ≤ r.size)
    (I : Finset ℕ) (h_ind : ∀ J ⊆ I, (2 : ℝ) ^ (β * J.card) * (validCount R (I \ J) : ℝ) ≤
        validCount R I)
    (i : ℕ) (hi : i ∉ I) :
    (2 : ℝ) ^ β * validCount R I ≤ validCount R (insert i I) := by
  have h4 := exists_threshold_validCount_step4_lost_bound hi hR N hN_pos h_size h_ind
  have hc : (0 : ℝ) ≤ validCount R I := Nat.cast_nonneg _
  have hshift : (∑ n ∈ Finset.Ico N (I.card + 2),
        (2 : ℝ) ^ (α * n) * ((validCount R I : ℝ) / (2 : ℝ) ^ (β * (n - 1)))) =
      (validCount R I : ℝ) * ∑ k ∈ Finset.Ico (N - 1) (I.card + 1),
        (2 : ℝ) ^ (α * (k + 1) - β * k) := by
    have h1 : Finset.Ico N (I.card + 2) = Finset.Ico (N - 1 + 1) (I.card + 1 + 1) := by
      congr 1
      omega
    rw [h1, ← Finset.sum_Ico_add' (fun n : ℕ => (2 : ℝ) ^ (α * n) *
      ((validCount R I : ℝ) / (2 : ℝ) ^ (β * ((n : ℝ) - 1)))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [add_sub_cancel_right, Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    ring
  have hsum := hN I.card
  have := mul_le_mul_of_nonneg_left hsum hc
  rw [hshift] at h4
  nlinarith

/-- Step 6 of the proof of `exists_threshold_validCount`: Prove the strong induction
hypothesis for all subsets `J ⊆ I`. -/
private lemma exists_threshold_validCount_strong_induction {α β : ℝ}
    (N : ℕ) (hN_pos : 0 < N)
    (hN : ∀ M : ℕ, (∑ k ∈ Finset.Ico (N - 1) (M + 1), (2 : ℝ) ^ (α * (k + 1) - β * k)) ≤ 2 - (2 : ℝ)
        ^ β)
    (R : Set Restriction) (hR : IsBoundedRestrictions α R) (h_size : ∀ r ∈ R, N ≤ r.size)
    (I : Finset ℕ) :
    ∀ J ⊆ I, (2 : ℝ) ^ (β * J.card) * (validCount R (I \ J) : ℝ) ≤ validCount R I := by
  suffices h : ∀ m : ℕ, ∀ I : Finset ℕ, I.card = m → ∀ J ⊆ I,
      (2 : ℝ) ^ (β * J.card) * (validCount R (I \ J) : ℝ) ≤ validCount R I from h _ I rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro I hI J hJ
    rcases J.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
    · simp
    · have hjI : j ∈ I := hJ hj
      have hcard : (I.erase j).card < m := by
        rw [← hI]; exact Finset.card_erase_lt_of_mem hjI
      have hind : ∀ J' ⊆ I.erase j, (2 : ℝ) ^ (β * J'.card) * (validCount R ((I.erase j) \ J') : ℝ)
          ≤ validCount R (I.erase j) := fun J' hJ' => ih _ hcard (I.erase j) rfl J' hJ'
      have h1 := exists_threshold_validCount_induction N hN_pos hN R hR h_size
        (I.erase j) hind j (Finset.notMem_erase j I)
      rw [Finset.insert_erase hjI] at h1
      have h2 := hind (J.erase j) (Finset.erase_subset_erase j hJ)
      have hs : (I.erase j) \ J.erase j = I \ J := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hx⟩, hx2⟩
          refine ⟨hx, fun hxJ => ?_⟩
          by_cases hxj : x = j
          · exact (by subst hxj; tauto : False)
          · exact hx2 ⟨hxj, hxJ⟩
        · rintro ⟨hx, hxJ⟩
          have : x ≠ j := fun h => hxJ (h ▸ hj)
          exact ⟨⟨this, hx⟩, fun h => hxJ h.2⟩
      rw [hs] at h2
      have hc : ((J.erase j).card : ℝ) + 1 = J.card := by
        exact_mod_cast Finset.card_erase_add_one hj
      have hpow : (2 : ℝ) ^ (β * J.card) = (2 : ℝ) ^ β * (2 : ℝ) ^ (β * (J.erase j).card) := by
        rw [← Real.rpow_add (by norm_num), ← hc]; congr 1; ring
      rw [hpow, mul_assoc]
      calc (2 : ℝ) ^ β * ((2 : ℝ) ^ (β * ((J.erase j).card : ℝ)) * (validCount R (I \ J) : ℝ))
          ≤ (2 : ℝ) ^ β * validCount R (I.erase j) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ validCount R I := h1

/-- **SUV p. 250 (Muchnik, Semenov).**  For `α < β < 1` there is `N` such that for every `R` with
the bound of Theorem 161 and only restrictions of size at least `N`, adding a point to a set
multiplies the number of valid assignments at least by `2^β`.  In particular
`c(I) ≥ 2^{β|I|} > 0`. -/
theorem exists_threshold_validCount {α β : ℝ} (_hα : 0 < α) (hαβ : α < β) (hβ : β < 1) :
    ∃ N : ℕ, ∀ R : Set Restriction, IsBoundedRestrictions α R → (∀ r ∈ R, N ≤ r.size) →
      ∀ (I : Finset ℕ) (i : ℕ), i ∉ I →
        (2 : ℝ) ^ β * validCount R I ≤ validCount R (insert i I) := by
  obtain ⟨N, hN_pos, hN⟩ := exists_threshold_validCount_series_bound hαβ hβ
  refine ⟨N, fun R hR h_size I i hi => ?_⟩
  exact exists_threshold_validCount_induction N hN_pos hN R hR h_size I (fun J hJ =>
      exists_threshold_validCount_strong_induction N hN_pos hN R hR h_size I J hJ) i
      hi

/-! ### Two dimensions -/

/-- A rectangle of the infinite cell paper: its corner, height and width. -/
structure CellRect where
  /-- The first coordinate of the corner. -/
  x : ℤ
  /-- The second coordinate of the corner. -/
  y : ℤ
  /-- The number of rows. -/
  h : ℕ
  /-- The number of columns. -/
  w : ℕ

/-- The content of a rectangle under a filling of the paper. -/
def CellRect.content (r : CellRect) (f : ℤ × ℤ → Bool) : Fin r.h × Fin r.w → Bool :=
  fun p => f (r.x + (p.1 : ℕ), r.y + (p.2 : ℕ))

private def exists_filling_avoiding_rectangles_gridEquiv : ℤ × ℤ ≃ ℕ :=
  Denumerable.eqv _

private def exists_filling_avoiding_rectangles_restrictCellRect (r : CellRect) (s : Fin r.h × Fin
    r.w → Bool) : Restriction := {
  indices := (Finset.univ (α := Fin r.h × Fin r.w)).image (fun p =>
      exists_filling_avoiding_rectangles_gridEquiv (r.x + p.1, r.y + p.2))
  values := ((Finset.univ (α := Fin r.h × Fin r.w)).image (fun p =>
      exists_filling_avoiding_rectangles_gridEquiv (r.x + p.1, r.y + p.2))).sort (· ≤ ·) |>.map (fun
      i =>
    let p : ℤ × ℤ := exists_filling_avoiding_rectangles_gridEquiv.symm i
    let px := p.1 - r.x
    let py := p.2 - r.y
    if hx : 0 ≤ px ∧ px.toNat < r.h ∧ 0 ≤ py ∧ py.toNat < r.w then
      s ⟨⟨px.toNat, hx.2.1⟩, ⟨py.toNat, hx.2.2.2⟩⟩
    else
      false
  )
  length_eq := by
    dsimp
    rw [List.length_map, Finset.length_sort]
}

private def exists_filling_avoiding_rectangles_R_set (forbidden : (r : CellRect) → Set (Fin r.h ×
    Fin r.w → Bool)) : Set Restriction :=
  ⋃ r : CellRect, exists_filling_avoiding_rectangles_restrictCellRect r '' forbidden r


/-- Step 1a of the proof of exists_filling_avoiding_rectangles: The number of rectangles
of area `n` containing a given point is at most `n^2`. -/
private theorem exists_filling_avoiding_rectangles_cellRects (n : ℕ) (hn : 0 < n) (p : ℤ × ℤ)
    :
  ({r : CellRect | r.h * r.w = n ∧ 0 ≤ p.1 - r.x ∧ (p.1 - r.x).toNat < r.h ∧ 0 ≤ p.2 - r.y ∧ (p.2 -
      r.y).toNat < r.w} : Set CellRect).Finite ∧
  ({r : CellRect | r.h * r.w = n ∧ 0 ≤ p.1 - r.x ∧ (p.1 - r.x).toNat < r.h ∧ 0 ≤ p.2 - r.y ∧ (p.2 -
      r.y).toNat < r.w} : Set CellRect).ncard ≤ n^2 := by
  set S : Set CellRect := {r : CellRect | r.h * r.w = n ∧ 0 ≤ p.1 - r.x ∧ (p.1 - r.x).toNat < r.h ∧
      0 ≤ p.2 - r.y ∧ (p.2 - r.y).toNat < r.w} with hS
  let φ : CellRect → (Σ _ : ℕ, ℕ × ℕ) := fun r => ⟨r.h, (p.1 - r.x).toNat, (p.2 - r.y).toNat⟩
  have hinj : Set.InjOn φ S := by
    intro r hr r' hr' h
    obtain ⟨h1, h2, h3, h4, h5⟩ := hr
    obtain ⟨h1', h2', h3', h4', h5'⟩ := hr'
    have hh : r.h = r'.h := congrArg Sigma.fst h
    have hsnd : (p.1 - r.x).toNat = (p.1 - r'.x).toNat ∧ (p.2 - r.y).toNat = (p.2 - r'.y).toNat :=
        by
      have := Sigma.mk.inj_iff.mp h
      simpa [φ] using this.2
    have hpos : 0 < r.h := by
      rcases Nat.eq_zero_or_pos r.h with h0 | h0
      · rw [h0] at h1; omega
      · exact h0
    have hw : r.w = r'.w := by
      rw [← hh] at h1'
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h1'.symm)
    obtain ⟨hx, hy⟩ := hsnd
    cases r; cases r'
    simp only [CellRect.mk.injEq] at *
    refine ⟨by omega, by omega, hh, hw⟩
  let T : Finset (Σ _ : ℕ, ℕ × ℕ) := n.divisors.sigma (fun d => Finset.range d ×ˢ Finset.range (n /
      d))
  have hmaps : Set.MapsTo φ S (T : Set (Σ _ : ℕ, ℕ × ℕ)) := by
    intro r hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hr
    have hpos : 0 < r.h := by
      rcases Nat.eq_zero_or_pos r.h with h0 | h0
      · rw [h0] at h1; omega
      · exact h0
    have hdiv : n / r.h = r.w := by
      rw [← h1]; exact Nat.mul_div_cancel_left _ hpos
    simp only [T, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Nat.mem_divisors,
      Finset.mem_product, Finset.mem_range, φ, hdiv]
    refine ⟨⟨⟨r.w, h1.symm⟩, by omega⟩, h3, h5⟩
  have hfin : S.Finite := Set.Finite.of_finite_image ((Finset.finite_toSet T).subset (by
      rintro _ ⟨r, hr, rfl⟩; exact hmaps hr)) hinj
  refine ⟨hfin, ?_⟩
  have h1 : S.ncard ≤ (T : Set (Σ _ : ℕ, ℕ × ℕ)).ncard :=
    Set.ncard_le_ncard_of_injOn φ hmaps hinj (Finset.finite_toSet T)
  rw [Set.ncard_coe_finset] at h1
  have h2 : T.card = ∑ d ∈ n.divisors, d * (n / d) := by
    simp [T, Finset.card_sigma]
  have h3 : ∑ d ∈ n.divisors, d * (n / d) = ∑ _d ∈ n.divisors, n :=
    Finset.sum_congr rfl (fun d hd => Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd))
  rw [h3, Finset.sum_const, smul_eq_mul] at h2
  calc S.ncard ≤ T.card := h1
    _ = n.divisors.card * n := h2
    _ ≤ n * n := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)
    _ = n ^ 2 := by ring

/-- Step 1b of the proof of exists_filling_avoiding_rectangles: Analytic threshold for the
density bound. -/
private theorem exists_filling_avoiding_rectangles_analytic {α : ℝ} (hα : α < 1) :
  ∃ n0 : ℕ, ∀ n ≥ n0, (n^2 : ℝ) * (2 : ℝ) ^ (α * n) ≤ (2 : ℝ) ^ (((α + 1) / 2) * n) := by
  have hc : 0 < (1 - α) / 2 := by linarith
  have hρ : 1 < (2 : ℝ) ^ ((1 - α) / 2) := Real.one_lt_rpow (by norm_num) hc
  have hT := tendsto_pow_const_div_const_pow_of_one_lt 2 hρ
  have hev := (hT.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨n0, fun n hn => ?_⟩
  have h1 := hn0 n hn
  have hpos : 0 < ((2 : ℝ) ^ ((1 - α) / 2)) ^ n := pow_pos (by linarith) n
  rw [div_lt_one hpos] at h1
  have h2 : ((2 : ℝ) ^ ((1 - α) / 2)) ^ n = (2 : ℝ) ^ ((1 - α) / 2 * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ (((α + 1) / 2) * n) = (2 : ℝ) ^ ((1 - α) / 2 * n) * (2 : ℝ) ^ (α * n) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1; ring
  rw [h3]
  exact mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg (by norm_num) _)

/-- Step 0 of the proof of `exists_filling_avoiding_rectangles_isBounded`: local
copy of the size identity. -/
private theorem exists_filling_avoiding_rectangles_isBounded_size (r : CellRect) (s : Fin r.h
    × Fin r.w → Bool) :
    (exists_filling_avoiding_rectangles_restrictCellRect r s).size = r.h * r.w := by
  have h := (exists_filling_avoiding_rectangles_restrictCellRect r s).length_eq
  unfold Restriction.size
  rw [h]
  change ((Finset.univ (α := Fin r.h × Fin r.w)).image (fun p =>
      exists_filling_avoiding_rectangles_gridEquiv (r.x + p.1, r.y + p.2))).card = _
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    have := exists_filling_avoiding_rectangles_gridEquiv.injective hab
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    have h1' : (a.1 : ℕ) = b.1 := by exact_mod_cast (add_left_cancel h1)
    have h2' : (a.2 : ℕ) = b.2 := by exact_mod_cast (add_left_cancel h2)
    exact Prod.ext (Fin.ext h1') (Fin.ext h2')

/-- Step 1c of the proof of exists_filling_avoiding_rectangles: The truncated set of
restrictions satisfies the bound condition. -/
private theorem exists_filling_avoiding_rectangles_isBounded {α : ℝ}
  (forbidden : (r : CellRect) → Set (Fin r.h × Fin r.w → Bool))
  (hbound : ∀ r, ((forbidden r).ncard : ℝ) ≤ (2 : ℝ) ^ (α * (r.h * r.w : ℕ))) (n0 : ℕ)
  (hn0 : ∀ n ≥ n0, ((n : ℝ) ^ 2) * (2 : ℝ) ^ (α * n) ≤ (2 : ℝ) ^ (((α + 1) / 2) * n)) :
  IsBoundedRestrictions ((α + 1) / 2) {rho ∈ exists_filling_avoiding_rectangles_R_set forbidden | n0
      ≤ rho.size} := by
  intro i n hn
  set p : ℤ × ℤ := exists_filling_avoiding_rectangles_gridEquiv.symm i with hp
  set Rc : Set CellRect := {r : CellRect | r.h * r.w = n ∧ 0 ≤ p.1 - r.x ∧ (p.1 - r.x).toNat < r.h ∧
      0 ≤ p.2 - r.y ∧ (p.2 - r.y).toNat < r.w} with hRc
  obtain ⟨hfin, hcard⟩ := exists_filling_avoiding_rectangles_cellRects n hn p
  rw [← hRc] at hfin hcard
  by_cases hn0' : n < n0
  · have hE : {r ∈ {rho ∈ exists_filling_avoiding_rectangles_R_set forbidden | n0 ≤ rho.size} |
      r.size = n ∧ i ∈ r.indices} = ∅ := by
      ext rho
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, h1⟩, h2, _⟩
      omega
    rw [hE]
    refine ⟨Set.finite_empty, ?_⟩
    simp only [Set.ncard_empty, Nat.cast_zero]
    positivity
  have hn0'': n0 ≤ n := not_lt.mp hn0'
  have hsub : {r ∈ {rho ∈ exists_filling_avoiding_rectangles_R_set forbidden | n0 ≤ rho.size} |
      r.size = n ∧ i ∈ r.indices} ⊆
      ⋃ r ∈ Rc, exists_filling_avoiding_rectangles_restrictCellRect r '' forbidden r := by
    rintro rho ⟨⟨hR, _⟩, hsz, hi⟩
    unfold exists_filling_avoiding_rectangles_R_set at hR
    rw [Set.mem_iUnion] at hR
    obtain ⟨r, s, hs, rfl⟩ := hR
    have hsize := exists_filling_avoiding_rectangles_isBounded_size r s
    rw [hsize] at hsz
    have hi' : i ∈ (Finset.univ (α := Fin r.h × Fin r.w)).image (fun q =>
        exists_filling_avoiding_rectangles_gridEquiv (r.x + q.1, r.y + q.2)) := hi
    rw [Finset.mem_image] at hi'
    obtain ⟨q, _, hq⟩ := hi'
    have hpq : p = (r.x + q.1, r.y + q.2) := by
      rw [hp, ← hq, Equiv.symm_apply_apply]
    have h1 : p.1 = r.x + q.1 := by rw [hpq]
    have h2 : p.2 = r.y + q.2 := by rw [hpq]
    have q1 := q.1.2
    have q2 := q.2.2
    refine Set.mem_biUnion (x := r) ?_ ⟨s, hs, rfl⟩
    refine ⟨hsz, by omega, by omega, by omega, by omega⟩
  have hfinU : (⋃ r ∈ Rc, exists_filling_avoiding_rectangles_restrictCellRect r '' forbidden
      r).Finite :=
    Set.Finite.biUnion hfin (fun r _ => (Set.toFinite (forbidden r)).image _)
  refine ⟨hfinU.subset hsub, ?_⟩
  calc (({r ∈ {rho ∈ exists_filling_avoiding_rectangles_R_set forbidden | n0 ≤ rho.size} | r.size =
      n ∧ i ∈ r.indices} : Set Restriction).ncard : ℝ)
      ≤ ((⋃ r ∈ Rc, exists_filling_avoiding_rectangles_restrictCellRect r '' forbidden r).ncard : ℝ)
          := by
        exact_mod_cast Set.ncard_le_ncard hsub hfinU
    _ ≤ ((∑ r ∈ hfin.toFinset, (exists_filling_avoiding_rectangles_restrictCellRect r '' forbidden
        r).ncard : ℕ) : ℝ) := by
        have := Finset.set_ncard_biUnion_le hfin.toFinset (fun r =>
            exists_filling_avoiding_rectangles_restrictCellRect r '' forbidden r)
        simp only [Set.Finite.mem_toFinset] at this
        exact_mod_cast this
    _ ≤ ((∑ r ∈ hfin.toFinset, (forbidden r).ncard : ℕ) : ℝ) := by
        exact_mod_cast Finset.sum_le_sum (fun r _ => Set.ncard_image_le (Set.toFinite _))
    _ ≤ ∑ r ∈ hfin.toFinset, (2 : ℝ) ^ (α * n) := by
        push_cast
        refine Finset.sum_le_sum (fun r hr => ?_)
        have hr' : r ∈ Rc := hfin.mem_toFinset.mp hr
        have := hbound r
        have hhw : ((r.h * r.w : ℕ) : ℝ) = n := by rw [hr'.1]
        rw [hhw] at this
        exact this
    _ = (hfin.toFinset.card : ℝ) * (2 : ℝ) ^ (α * n) := by simp
    _ ≤ ((n ^ 2 : ℕ) : ℝ) * (2 : ℝ) ^ (α * n) := by
        have h1 : hfin.toFinset.card ≤ n ^ 2 := by
          rw [← Set.ncard_eq_toFinset_card Rc hfin]; exact hcard
        gcongr
    _ ≤ (2 : ℝ) ^ (((α + 1) / 2) * n) := by
        have := hn0 n hn0''
        simpa using this

/-- Step 2 of the proof of exists_filling_avoiding_rectangles: If a sequence w avoids a
restriction, then the corresponding paper filling f avoids the original forbidden set. -/
private theorem exists_filling_avoiding_rectangles_not_forbids (r : CellRect)
    (s : Fin r.h × Fin r.w → Bool) (f : ℤ × ℤ → Bool) :
    ¬ (exists_filling_avoiding_rectangles_restrictCellRect r s).Forbids (fun n => f
        (exists_filling_avoiding_rectangles_gridEquiv.symm n)) →
    r.content f ≠ s := by
  intro hn hc
  apply hn
  subst hc
  unfold Restriction.Forbids restrictBits exists_filling_avoiding_rectangles_restrictCellRect
  apply List.map_congr_left
  intro i hi
  rw [Finset.mem_sort, Finset.mem_image] at hi
  obtain ⟨p, -, rfl⟩ := hi
  simp [CellRect.content]

/-- Step 3 of the proof of exists_filling_avoiding_rectangles: The size of the restriction
is exactly the area of the rectangle. -/
private theorem exists_filling_avoiding_rectangles_size_eq (r : CellRect) (s : Fin r.h × Fin
    r.w → Bool) :
    (exists_filling_avoiding_rectangles_restrictCellRect r s).size = r.h * r.w := by
  have h1 : (exists_filling_avoiding_rectangles_restrictCellRect r s).size =
      (exists_filling_avoiding_rectangles_restrictCellRect r s).indices.card :=
    (exists_filling_avoiding_rectangles_restrictCellRect r s).length_eq
  rw [h1]
  change ((Finset.univ (α := Fin r.h × Fin r.w)).image
    (fun p => exists_filling_avoiding_rectangles_gridEquiv (r.x + p.1, r.y + p.2))).card = _
  rw [Finset.card_image_of_injective]
  · simp
  · intro p q hpq
    have h2 := exists_filling_avoiding_rectangles_gridEquiv.injective hpq
    simp only [Prod.mk.injEq] at h2
    obtain ⟨h3, h4⟩ := h2
    have h5 : (p.1 : ℕ) = q.1 := by exact_mod_cast (add_left_cancel h3)
    have h6 : (p.2 : ℕ) = q.2 := by exact_mod_cast (add_left_cancel h4)
    exact Prod.ext (Fin.ext h5) (Fin.ext h6)

/-- **SUV Problem 251, p. 248.**  A two-dimensional Theorem 157: if for every rectangle of area `k`
at most `2^{αk}` combinations of its cells are forbidden, for some `α < 1`, then the infinite paper
can be filled so that no rectangle of large enough area has a forbidden content. -/
theorem exists_filling_avoiding_rectangles {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (forbidden : (r : CellRect) → Set (Fin r.h × Fin r.w → Bool))
    (hbound : ∀ r, ((forbidden r).ncard : ℝ) ≤ (2 : ℝ) ^ (α * (r.h * r.w : ℕ))) :
    ∃ (N : ℕ) (f : ℤ × ℤ → Bool), ∀ r : CellRect, N ≤ r.h * r.w → r.content f ∉ forbidden r := by
  have hα0_prime : 0 < (α + 1) / 2 := by linarith
  have hα1_prime : (α + 1) / 2 < 1 := by linarith
  have h_analytic := exists_filling_avoiding_rectangles_analytic hα1
  obtain ⟨n0, hn0⟩ := h_analytic
  have hR := exists_filling_avoiding_rectangles_isBounded forbidden hbound n0 hn0
  obtain ⟨N, w, hw⟩ := exists_not_forbidden hα0_prime hα1_prime hR
  let f : ℤ × ℤ → Bool := fun p => w (exists_filling_avoiding_rectangles_gridEquiv p)
  use (max (N + 1) n0), f
  intro r hr h_in
  have h_size := exists_filling_avoiding_rectangles_size_eq r (r.content f)
  have hw_r := hw (exists_filling_avoiding_rectangles_restrictCellRect r (r.content f))
  have h_mem : exists_filling_avoiding_rectangles_restrictCellRect r (r.content f) ∈ {rho ∈
      exists_filling_avoiding_rectangles_R_set forbidden | n0 ≤ rho.size} := by
    simp only [Set.mem_sep_iff]
    constructor
    · unfold exists_filling_avoiding_rectangles_R_set
      rw [Set.mem_iUnion]
      use r
      rw [Set.mem_image]
      exact ⟨r.content f, h_in, rfl⟩
    · rw [h_size]
      exact le_trans (le_max_right (N + 1) n0) hr
  have h_lt : N < (exists_filling_avoiding_rectangles_restrictCellRect r (r.content f)).size := by
    rw [h_size]
    have hr' : N + 1 ≤ r.h * r.w := le_trans (le_max_left (N + 1) n0) hr
    exact Nat.lt_of_succ_le hr'
  have hw_not_forbids := hw_r h_mem h_lt
  have hw_not_forbids_f : ¬(exists_filling_avoiding_rectangles_restrictCellRect r (r.content
      f)).Forbids (fun n => f (exists_filling_avoiding_rectangles_gridEquiv.symm n)) := by
    intro h_f
    apply hw_not_forbids
    unfold Restriction.Forbids restrictBits at *
    rw [←h_f]
    congr
    ext n
    dsimp [f]
    rw [Equiv.apply_symm_apply]
  have h_ne : r.content f ≠ r.content f := exists_filling_avoiding_rectangles_not_forbids r
      (r.content f) f hw_not_forbids_f
  exact h_ne rfl

end Kolmogorov.Applications
