import KolmogorovMathlib.InformationInequalities.AlmostUniform
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The decomposition lemmas of Section 10.9

SUV Section 10.9, pp. 333–336.

Every finite set `A ⊆ Y_1 × ⋯ × Y_n` is a union of polylogarithmically many (in `|A|`) parts
that are `c`-uniform.  The partition version of Alon, Newman, Shen, Tardos and Vereshchagin
(`exists_cUniform_partition_const`) takes a partition of minimal total weight; the cover
version (`exists_cUniform_cover`) has a uniformity constant polynomial in `log |A|`.  Applied
to a valid entropy inequality, the partition shows that every finite set is a union of
polylogarithmically many parts on which the corresponding product inequality holds up to a
polylogarithmic factor (`exists_union_decomposition_of_holdsForEntropies`).

As in the rest of the chapter, polylogarithmic factors are written `(2 + log₂ |A|)^d`, which
agrees with the book's `(log |A|)^d` up to a change of `d` as soon as `|A| ≥ 4`.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}
section PartitionsOfFinsets

variable {α : Type*}

/-- `P` is a partition of `A` into non-empty, pairwise disjoint parts. -/
private def IsPartitionOf (A : Finset α) (P : Finset (Finset α)) : Prop :=
  (∀ S ∈ P, S.Nonempty) ∧ (∀ S ∈ P, ∀ T ∈ P, S ≠ T → Disjoint S T) ∧
    ∀ a, a ∈ A ↔ ∃ S ∈ P, a ∈ S

/-- Among the partitions of a finite set there is one of minimal total weight. -/
private lemma exists_isPartitionOf_min (A : Finset α) (W : Finset (Finset α) → ℝ) :
    ∃ P, IsPartitionOf A P ∧ ∀ Q, IsPartitionOf A Q → W P ≤ W Q := by
  classical
  set F := A.powerset.powerset.filter (IsPartitionOf A) with hF
  have hmem : ∀ Q, IsPartitionOf A Q → Q ∈ F := by
    intro Q hQ
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 fun S hS => ?_, hQ⟩
    exact Finset.mem_powerset.2 fun a ha => (hQ.2.2 a).2 ⟨S, hS, ha⟩
  have hsing : IsPartitionOf A (A.image fun a => {a}) := by
    refine ⟨?_, ?_, ?_⟩
    · intro S hS
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hS
      exact Finset.singleton_nonempty a
    · intro S hS T hT hST
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hS
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hT
      exact Finset.disjoint_singleton.2 fun h => hST (h ▸ rfl)
    · intro a
      constructor
      · intro ha
        exact ⟨{a}, Finset.mem_image_of_mem _ ha, Finset.mem_singleton_self a⟩
      · rintro ⟨S, hS, haS⟩
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hS
        rw [Finset.mem_singleton.1 haS]
        exact hb
  obtain ⟨P, hP, hmin⟩ := Finset.exists_min_image F W ⟨_, hmem _ hsing⟩
  exact ⟨P, (Finset.mem_filter.1 hP).2, fun Q hQ => hmin Q (hmem Q hQ)⟩

/-- **Splitting a part.**  Replacing a part `S₁ ∪ S₂` of a partition by the two non-empty
disjoint pieces `S₁`, `S₂` gives a partition, and any additive weight changes accordingly. -/
private lemma isPartitionOf_split [DecidableEq α] {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPartitionOf A P) {S₁ S₂ : Finset α} (hU : S₁ ∪ S₂ ∈ P) (hd : Disjoint S₁ S₂)
    (h₁ : S₁.Nonempty) (h₂ : S₂.Nonempty) :
    IsPartitionOf A (insert S₁ (insert S₂ (P.erase (S₁ ∪ S₂)))) ∧
      ∀ f : Finset α → ℝ, ∑ S ∈ insert S₁ (insert S₂ (P.erase (S₁ ∪ S₂))), f S =
        ∑ S ∈ P, f S - f (S₁ ∪ S₂) + f S₁ + f S₂ := by
  obtain ⟨hne, hdisj, hcov⟩ := hP
  -- a part of `P` other than `S₁ ∪ S₂` is disjoint from both pieces
  have hout : ∀ X ∈ P.erase (S₁ ∪ S₂), Disjoint S₁ X ∧ Disjoint S₂ X := by
    intro X hX
    obtain ⟨hX1, hX2⟩ := Finset.mem_erase.1 hX
    have h := hdisj _ hU X hX2 (Ne.symm hX1)
    exact ⟨Finset.disjoint_of_subset_left Finset.subset_union_left h,
      Finset.disjoint_of_subset_left Finset.subset_union_right h⟩
  have hn1 : S₁ ∉ P.erase (S₁ ∪ S₂) := fun h =>
    Finset.not_disjoint_iff_nonempty_inter.2 (by rw [Finset.inter_self]; exact h₁) (hout _ h).1
  have hn2 : S₂ ∉ P.erase (S₁ ∪ S₂) := fun h =>
    Finset.not_disjoint_iff_nonempty_inter.2 (by rw [Finset.inter_self]; exact h₂) (hout _ h).2
  have h12 : S₁ ≠ S₂ := fun h =>
    Finset.not_disjoint_iff_nonempty_inter.2 (by rw [h, Finset.inter_self]; exact h₂) hd
  have hn1' : S₁ ∉ insert S₂ (P.erase (S₁ ∪ S₂)) := by
    rw [Finset.mem_insert]; rintro (h | h)
    · exact h12 h
    · exact hn1 h
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro X hX
    rcases Finset.mem_insert.1 hX with rfl | hX
    · exact h₁
    rcases Finset.mem_insert.1 hX with rfl | hX
    · exact h₂
    · exact hne X (Finset.mem_of_mem_erase hX)
  · intro X hX Z hZ hXZ
    rcases Finset.mem_insert.1 hX with rfl | hX <;> rcases Finset.mem_insert.1 hZ with rfl | hZ
    · exact absurd rfl hXZ
    · rcases Finset.mem_insert.1 hZ with rfl | hZ
      · exact hd
      · exact (hout Z hZ).1
    · rcases Finset.mem_insert.1 hX with rfl | hX
      · exact hd.symm
      · exact (hout X hX).1.symm
    · rcases Finset.mem_insert.1 hX with rfl | hX <;> rcases Finset.mem_insert.1 hZ with rfl | hZ
      · exact absurd rfl hXZ
      · exact (hout Z hZ).2
      · exact (hout X hX).2.symm
      · exact hdisj X (Finset.mem_of_mem_erase hX) Z (Finset.mem_of_mem_erase hZ) hXZ
  · intro a
    rw [hcov a]
    constructor
    · rintro ⟨X, hX, haX⟩
      by_cases hXU : X = S₁ ∪ S₂
      · subst hXU
        rcases Finset.mem_union.1 haX with h | h
        · exact ⟨S₁, Finset.mem_insert_self _ _, h⟩
        · exact ⟨S₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
      · exact ⟨X, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.2 ⟨hXU, hX⟩)), haX⟩
    · rintro ⟨X, hX, haX⟩
      rcases Finset.mem_insert.1 hX with rfl | hX
      · exact ⟨_, hU, Finset.mem_union_left _ haX⟩
      rcases Finset.mem_insert.1 hX with rfl | hX
      · exact ⟨_, hU, Finset.mem_union_right _ haX⟩
      · exact ⟨X, Finset.mem_of_mem_erase hX, haX⟩
  · intro f
    rw [Finset.sum_insert hn1', Finset.sum_insert hn2, ← Finset.sum_erase_add P f hU]
    ring

/-- **Merging two parts.**  Replacing two distinct parts `S`, `T` of a partition by their
union gives a partition, and any additive weight changes accordingly. -/
private lemma isPartitionOf_merge [DecidableEq α] {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPartitionOf A P) {S T : Finset α} (hS : S ∈ P) (hT : T ∈ P) (hST : S ≠ T) :
    IsPartitionOf A (insert (S ∪ T) ((P.erase S).erase T)) ∧
      ∀ f : Finset α → ℝ, ∑ X ∈ insert (S ∪ T) ((P.erase S).erase T), f X =
        ∑ X ∈ P, f X - f S - f T + f (S ∪ T) := by
  obtain ⟨hne, hdisj, hcov⟩ := hP
  have hmem : ∀ X, X ∈ (P.erase S).erase T ↔ X ≠ T ∧ X ≠ S ∧ X ∈ P := by
    intro X; simp only [Finset.mem_erase]
  have hout : ∀ X ∈ (P.erase S).erase T, Disjoint (S ∪ T) X := by
    intro X hX
    obtain ⟨hXT, hXS, hX⟩ := (hmem X).1 hX
    exact Finset.disjoint_union_left.2 ⟨hdisj S hS X hX (Ne.symm hXS),
      hdisj T hT X hX (Ne.symm hXT)⟩
  have hnU : S ∪ T ∉ (P.erase S).erase T := by
    intro h
    have := hout _ h
    rw [disjoint_self, Finset.bot_eq_empty, ← Finset.not_nonempty_iff_eq_empty] at this
    exact this ((hne S hS).mono Finset.subset_union_left)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro X hX
    rcases Finset.mem_insert.1 hX with rfl | hX
    · exact (hne S hS).mono Finset.subset_union_left
    · exact hne X ((hmem X).1 hX).2.2
  · intro X hX Z hZ hXZ
    rcases Finset.mem_insert.1 hX with rfl | hX <;> rcases Finset.mem_insert.1 hZ with rfl | hZ
    · exact absurd rfl hXZ
    · exact hout Z hZ
    · exact (hout X hX).symm
    · exact hdisj X ((hmem X).1 hX).2.2 Z ((hmem Z).1 hZ).2.2 hXZ
  · intro a
    rw [hcov a]
    constructor
    · rintro ⟨X, hX, haX⟩
      by_cases hXS : X = S
      · subst hXS; exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_union_left _ haX⟩
      by_cases hXT : X = T
      · subst hXT; exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_union_right _ haX⟩
      exact ⟨X, Finset.mem_insert_of_mem ((hmem X).2 ⟨hXT, hXS, hX⟩), haX⟩
    · rintro ⟨X, hX, haX⟩
      rcases Finset.mem_insert.1 hX with rfl | hX
      · rcases Finset.mem_union.1 haX with h | h
        · exact ⟨S, hS, h⟩
        · exact ⟨T, hT, h⟩
      · exact ⟨X, ((hmem X).1 hX).2.2, haX⟩
  · intro f
    have hTS : T ∈ P.erase S := Finset.mem_erase.2 ⟨Ne.symm hST, hT⟩
    rw [Finset.sum_insert hnU, ← Finset.sum_erase_add P f hS,
      ← Finset.sum_erase_add (P.erase S) f hTS]
    ring

end PartitionsOfFinsets

section Partition

variable {Y : Fin n → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]

private lemma one_le_maxSection_of_nonempty {S : Finset (∀ i, Y i)} (hS : S.Nonempty)
    (J I : Finset (Fin n)) : 1 ≤ maxSection S J I := by
  obtain ⟨a, ha⟩ := hS
  refine le_trans ?_ (Finset.le_sup (f := fun p : (i : I) → Y i.val =>
    (sectionOver S J I p).card) (Finset.mem_univ (restrictTo I a)))
  refine Finset.card_pos.2 ⟨restrictTo J a, ?_⟩
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨ha, rfl⟩)

private lemma maxSection_le_card (S : Finset (∀ i, Y i)) (J I : Finset (Fin n)) :
    maxSection S J I ≤ S.card :=
  Finset.sup_le fun _ _ => Finset.card_image_le.trans (Finset.card_filter_le _ _)

private lemma maxSection_mono {S T : Finset (∀ i, Y i)} (h : S ⊆ T) (J I : Finset (Fin n)) :
    maxSection S J I ≤ maxSection T J I :=
  Finset.sup_mono_fun fun _ _ =>
    Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset_filter _ h))

private lemma maxSection_union_le_add (S T : Finset (∀ i, Y i)) (J I : Finset (Fin n)) :
    maxSection (S ∪ T) J I ≤ maxSection S J I + maxSection T J I := by
  refine Finset.sup_le fun p _ => ?_
  have h : sectionOver (S ∪ T) J I p = sectionOver S J I p ∪ sectionOver T J I p := by
    simp only [sectionOver, Finset.filter_union, Finset.image_union]
  rw [h]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (Finset.le_sup (f := fun p => (sectionOver S J I p).card) (Finset.mem_univ p))
    (Finset.le_sup (f := fun p => (sectionOver T J I p).card) (Finset.mem_univ p)))

omit [∀ i, Fintype (Y i)] in
/-- The sections over the points of the `E`-projection add up to (at most) the size of the
projection onto `E ∪ {j}`. -/
private lemma sum_sectionOver_le_projCard (S : Finset (∀ i, Y i)) (j : Fin n)
    (E : Finset (Fin n)) :
    ∑ v ∈ proj S E, (sectionOver S {j} E v).card ≤ projCard S (insert j E) := by
  set k : (∀ i, Y i) → ((i : E) → Y i.val) × ((i : ({j} : Finset (Fin n))) → Y i.val) :=
    fun a => (restrictTo E a, restrictTo {j} a) with hk
  have hsum : (S.image k).card = ∑ v ∈ proj S E, (sectionOver S {j} E v).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := proj S E)]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [sectionOver]
      refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hp, hpv⟩ := Finset.mem_filter.1 hp
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨ha, hpv⟩)
      · intro p hp q hq hpq
        exact Prod.ext ((Finset.mem_filter.1 hp).2.trans (Finset.mem_filter.1 hq).2.symm) hpq
      · intro w hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
        obtain ⟨ha, hav⟩ := Finset.mem_filter.1 ha
        exact ⟨k a, Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ ha, hav⟩, rfl⟩
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ ha)
  have hfac : S.image k = (proj S (insert j E)).image (fun r =>
      ((fun i => r ⟨i.val, Finset.mem_insert_of_mem i.2⟩ : (i : E) → Y i.val),
        (fun i => r ⟨i.val, by rw [Finset.mem_singleton.1 i.2]; exact Finset.mem_insert_self _ _⟩ :
          (i : ({j} : Finset (Fin n))) → Y i.val))) := by
    rw [proj, Finset.image_image]
    rfl
  rw [← hsum, hfac, projCard]
  exact Finset.card_image_le


/-- The sum of the logarithms of all maximal section sizes `m_S(J | I)` of a part `S`. -/
private noncomputable def partLogSum (S : Finset (∀ i, Y i)) : ℝ :=
  ∑ P : Finset (Fin n) × Finset (Fin n), Real.log (maxSection S P.1 P.2)

/-- The weight of a part `S`: `|S| · (∑_{J,I} log m_S(J | I) − D log |S|)`. -/
private noncomputable def partWeight (D : ℝ) (S : Finset (∀ i, Y i)) : ℝ :=
  S.card * (partLogSum S - D * Real.log S.card)

/-- The entropy bound `(a+b) log (a+b) − a log a − b log b ≤ a + b` (natural logarithms). -/
private lemma mul_log_add_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b ≤ a + b := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos (add_pos ha hb) ha)
  have h2 := Real.log_le_sub_one_of_pos (div_pos (add_pos ha hb) hb)
  rw [Real.log_div (add_pos ha hb).ne' ha.ne'] at h1
  rw [Real.log_div (add_pos ha hb).ne' hb.ne'] at h2
  have e1 : a * ((a + b) / a - 1) = b := by field_simp; ring
  have e2 : b * ((a + b) / b - 1) = a := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le, mul_le_mul_of_nonneg_left h2 hb.le]

/-- Passing to a non-empty subpart `T ⊆ S` whose parameter `P₀` drops by a factor more than
`e^D` lowers the log-sum by more than `D`. -/
private lemma lt_partLogSum_sub_of_subset {S T : Finset (∀ i, Y i)} (hT : T.Nonempty)
    (hTS : T ⊆ S) (D : ℝ) (J I : Finset (Fin n))
    (h : Real.exp D * maxSection T J I < maxSection S J I) :
    D < partLogSum S - partLogSum T := by
  have hpos : ∀ P : Finset (Fin n) × Finset (Fin n), (0 : ℝ) < maxSection T P.1 P.2 :=
    fun P => Nat.cast_pos.2 (one_le_maxSection_of_nonempty hT P.1 P.2)
  have hterm : ∀ P : Finset (Fin n) × Finset (Fin n),
      0 ≤ Real.log (maxSection S P.1 P.2) - Real.log (maxSection T P.1 P.2) := fun P =>
    sub_nonneg.2 (Real.log_le_log (hpos P) (Nat.cast_le.2 (maxSection_mono hTS P.1 P.2)))
  have hone : D < Real.log (maxSection S J I) - Real.log (maxSection T J I) := by
    have := Real.log_lt_log (mul_pos (Real.exp_pos D) (hpos (J, I))) h
    rw [Real.log_mul (Real.exp_pos D).ne' (hpos (J, I)).ne', Real.log_exp] at this
    linarith
  have hle := Finset.single_le_sum (s := Finset.univ) (fun P _ => hterm P)
    (Finset.mem_univ (J, I))
  rw [partLogSum, partLogSum, ← Finset.sum_sub_distrib]
  exact hone.trans_le hle

/-- **Splitting lowers the weight.**  If both halves of a split lower the log-sum by more
than `D`, the total weight decreases: the entropy loss `D (|S| log |S| − ∑ |Sᵢ| log |Sᵢ|)` is
at most `D |S|`. -/
private lemma partWeight_add_lt_of_split {S₁ S₂ : Finset (∀ i, Y i)} (h₁ : S₁.Nonempty)
    (h₂ : S₂.Nonempty) (hd : Disjoint S₁ S₂) {D : ℝ} (hD : 0 ≤ D)
    (g₁ : D < partLogSum (S₁ ∪ S₂) - partLogSum S₁)
    (g₂ : D < partLogSum (S₁ ∪ S₂) - partLogSum S₂) :
    partWeight D S₁ + partWeight D S₂ < partWeight D (S₁ ∪ S₂) := by
  have ha : (0 : ℝ) < S₁.card := by exact_mod_cast h₁.card_pos
  have hb : (0 : ℝ) < S₂.card := by exact_mod_cast h₂.card_pos
  have hc : ((S₁ ∪ S₂).card : ℝ) = S₁.card + S₂.card := by
    rw [Finset.card_union_of_disjoint hd]; push_cast; ring
  have hent := mul_log_add_sub_le ha hb
  simp only [partWeight, hc]
  nlinarith [mul_lt_mul_of_pos_left g₁ ha, mul_lt_mul_of_pos_left g₂ hb,
    mul_le_mul_of_nonneg_left hent hD]

/-- **Splitting a non-uniform part at the geometric mean.**  If the maximal `j`-section over
the `E`-projection exceeds the average one, `m_S(E ∪ {j}) / m_S(E)`, by a factor more than
`e^{2D}`, then cutting `S` at the geometric mean `τ` of the two produces two non-empty parts:
the small-section part has `m(j | E) ≤ τ`, the large-section part has `m(E) ≤ m_S(E ∪ {j})/τ`,
and both lower the log-sum by more than `D`. -/
private lemma exists_split_of_ratio {S : Finset (∀ i, Y i)} (hS : S.Nonempty) {D : ℝ}
    (hD : 0 ≤ D) (j : Fin n) (E : Finset (Fin n))
    (h : Real.exp (2 * D) * projCard S (insert j E) < maxSection S {j} E * projCard S E) :
    ∃ S₁ S₂ : Finset (∀ i, Y i), S₁.Nonempty ∧ S₂.Nonempty ∧ Disjoint S₁ S₂ ∧
      S₁ ∪ S₂ = S ∧ D < partLogSum S - partLogSum S₁ ∧ D < partLogSum S - partLogSum S₂ := by
  set M : ℝ := (maxSection S {j} E : ℝ) with hM
  set π₀ : ℝ := (projCard S E : ℝ) with hπ₀
  set π₁ : ℝ := (projCard S (insert j E) : ℝ) with hπ₁
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; exact_mod_cast one_le_maxSection_of_nonempty hS {j} E
  have hπ₀1 : (1 : ℝ) ≤ π₀ := by
    rw [hπ₀, ← maxSection_empty]; exact_mod_cast one_le_maxSection_of_nonempty hS E ∅
  have hπ₁1 : (1 : ℝ) ≤ π₁ := by
    rw [hπ₁, ← maxSection_empty]
    exact_mod_cast one_le_maxSection_of_nonempty hS (insert j E) ∅
  have he1 : 1 ≤ Real.exp D := Real.one_le_exp hD
  have he2 : Real.exp (2 * D) = Real.exp D ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  set τ : ℝ := Real.sqrt (M * π₁ / π₀) with hτ
  have hτpos : 0 < τ := Real.sqrt_pos.2 (by positivity)
  have hτsq : τ ^ 2 = M * π₁ / π₀ := Real.sq_sqrt (by positivity)
  -- the two key inequalities `e^D τ < M` and `e^D π₁ < π₀ τ`
  have key₁ : Real.exp D * τ < M := by
    refine lt_of_pow_lt_pow_left₀ 2 (by linarith) ?_
    rw [mul_pow, hτsq, ← he2]
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  have key₂ : Real.exp D * π₁ < π₀ * τ := by
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    rw [mul_pow, mul_pow, hτsq, ← he2]
    have : π₀ ^ 2 * (M * π₁ / π₀) = π₀ * M * π₁ := by field_simp
    rw [this]
    nlinarith
  set t : ((i : E) → Y i.val) → ℕ := fun v => (sectionOver S {j} E v).card with ht
  set S₁ := S.filter fun a => (t (restrictTo E a) : ℝ) ≤ τ with hS₁
  set S₂ := S.filter fun a => ¬ (t (restrictTo E a) : ℝ) ≤ τ with hS₂
  have hunion : S₁ ∪ S₂ = S := Finset.filter_union_filter_not_eq _ _
  have hdisj : Disjoint S₁ S₂ := Finset.disjoint_filter_filter_not _ _ _
  -- the small-section part: all its `j`-sections over `E` have at most `τ` points
  have hsmall : (maxSection S₁ {j} E : ℝ) ≤ τ := by
    have : maxSection S₁ {j} E ≤ ⌊τ⌋₊ := by
      refine Finset.sup_le fun p _ => ?_
      rcases (sectionOver S₁ {j} E p).eq_empty_or_nonempty with he | he
      · rw [he, Finset.card_empty]; exact Nat.zero_le _
      · obtain ⟨w, hw⟩ := he
        obtain ⟨a, ha, -⟩ := Finset.mem_image.1 hw
        obtain ⟨ha, hap⟩ := Finset.mem_filter.1 ha
        have hat := (Finset.mem_filter.1 ha).2
        rw [hap] at hat
        refine Nat.le_floor (le_trans (Nat.cast_le.2 ?_) hat)
        exact Finset.card_le_card (Finset.image_subset_image
          (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))
    exact (Nat.cast_le.2 this).trans (Nat.floor_le hτpos.le)
  -- the large-section part: its `E`-projection has fewer than `π₁ / τ` points
  have hlarge : (projCard S₂ E : ℝ) * τ ≤ π₁ := by
    have hsub : proj S₂ E ⊆ proj S E :=
      Finset.image_subset_image (Finset.filter_subset _ _)
    have hbig : ∀ v ∈ proj S₂ E, τ ≤ (t v : ℝ) := by
      intro v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
      exact (not_le.1 (Finset.mem_filter.1 ha).2).le
    calc (projCard S₂ E : ℝ) * τ = ∑ _v ∈ proj S₂ E, τ := by
          rw [Finset.sum_const, nsmul_eq_mul, projCard]
      _ ≤ ∑ v ∈ proj S₂ E, (t v : ℝ) := Finset.sum_le_sum hbig
      _ ≤ ∑ v ∈ proj S E, (t v : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
      _ ≤ π₁ := by
          rw [hπ₁, ht]; exact_mod_cast sum_sectionOver_le_projCard S j E
  have hlarge' : Real.exp D * projCard S₂ E < π₀ := by
    have : Real.exp D * projCard S₂ E * τ < π₀ * τ := by
      calc Real.exp D * projCard S₂ E * τ = Real.exp D * (projCard S₂ E * τ) := by ring
        _ ≤ Real.exp D * π₁ := mul_le_mul_of_nonneg_left hlarge (Real.exp_pos D).le
        _ < π₀ * τ := key₂
    exact lt_of_mul_lt_mul_right this hτpos.le
  have hsmall' : Real.exp D * maxSection S₁ {j} E < M :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsmall (Real.exp_pos D).le) key₁
  have hne₁ : S₁.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h₁
    rw [h₁, Finset.empty_union] at hunion
    rw [hunion] at hlarge'
    nlinarith
  have hne₂ : S₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h₂
    rw [h₂, Finset.union_empty] at hunion
    rw [hunion] at hsmall'
    nlinarith
  refine ⟨S₁, S₂, hne₁, hne₂, hdisj, hunion, ?_, ?_⟩
  · exact lt_partLogSum_sub_of_subset hne₁ (hunion ▸ Finset.subset_union_left) D {j} E hsmall'
  · refine lt_partLogSum_sub_of_subset hne₂ (hunion ▸ Finset.subset_union_right) D E ∅ ?_
    rw [maxSection_empty, maxSection_empty]
    exact hlarge'

/-- **The ratio criterion for `c`-uniformity.**  If, for every ordering `σ` and every step `k`,
the maximal section `m(σ k | earlier)` exceeds the average one
`m(earlier ∪ {σ k}) / m(earlier)` at most by the factor `C`, then the chain bound telescopes
and `S` is `C^n`-uniform. -/
private lemma isCUniform_of_ratio {S : Finset (∀ i, Y i)} (hS : S.Nonempty) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ (σ : Equiv.Perm (Fin n)) (k : Fin n),
      (maxSection S {σ k} (earlierIndices σ k) : ℝ) * projCard S (earlierIndices σ k) ≤
        C * projCard S (insert (σ k) (earlierIndices σ k))) :
    IsCUniform (C ^ n) S := by
  intro σ
  let T : ℕ → Finset (Fin n) := fun j => (Finset.univ.filter fun k : Fin n => k.val < j).image σ
  have claim : ∀ j, j ≤ n → ∏ k ∈ Finset.univ.filter (fun k : Fin n => k.val < j),
      (maxSection S {σ k} (earlierIndices σ k) : ℝ) ≤ C ^ j * projCard S (T j) := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : T 0 = ∅ := by simp [T]
      have hf : (Finset.univ.filter fun k : Fin n => k.val < 0) = ∅ := by simp
      rw [hf, h0, Finset.prod_empty, projCard_empty hS]; simp
    | succ j ih =>
      intro hj
      set k : Fin n := ⟨j, hj⟩ with hk
      have hfil : (Finset.univ.filter fun k : Fin n => k.val < j + 1) =
          insert k (Finset.univ.filter fun k : Fin n => k.val < j) := by
        ext i; simp [k, Fin.ext_iff]; omega
      have hnot : k ∉ Finset.univ.filter fun k : Fin n => k.val < j := by simp [k]
      have hE : earlierIndices σ k = T j := by
        simp only [earlierIndices, T]
        congr 1
      have hT : T (j + 1) = insert (σ k) (T j) := by
        simp only [T]; rw [hfil, Finset.image_insert]
      rw [hfil, Finset.prod_insert hnot, hT]
      have ih' := ih (by omega)
      have hk' := h σ k
      rw [hE] at hk'
      have hM0 : (0 : ℝ) ≤ maxSection S {σ k} (earlierIndices σ k) := Nat.cast_nonneg _
      calc (maxSection S {σ k} (earlierIndices σ k) : ℝ) *
            ∏ k ∈ Finset.univ.filter (fun k : Fin n => k.val < j),
              (maxSection S {σ k} (earlierIndices σ k) : ℝ)
          ≤ (maxSection S {σ k} (earlierIndices σ k) : ℝ) * (C ^ j * projCard S (T j)) :=
            mul_le_mul_of_nonneg_left ih' hM0
        _ = C ^ j * ((maxSection S {σ k} (T j) : ℝ) * projCard S (T j)) := by rw [hE]; ring
        _ ≤ C ^ j * (C * projCard S (insert (σ k) (T j))) :=
            mul_le_mul_of_nonneg_left hk' (pow_nonneg hC j)
        _ = C ^ (j + 1) * projCard S (insert (σ k) (T j)) := by ring
  have hn := claim n le_rfl
  have hf : (Finset.univ.filter fun k : Fin n => k.val < n) = Finset.univ := by
    ext i; simp
  have hTn : T n = Finset.univ := by
    simp only [T]; rw [hf]; exact Finset.image_univ_equiv σ
  rw [hf, hTn, projCard_univ] at hn
  unfold chainBound
  push_cast
  exact hn

/-- Two positive integers with the same binary logarithm differ by a factor less than `2`. -/
private lemma lt_two_mul_of_log_eq {a b : ℕ} (ha : a ≠ 0) (h : Nat.log 2 a = Nat.log 2 b) :
    b < 2 * a := by
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b
  have h2 := Nat.pow_log_le_self 2 ha
  rw [← h, pow_succ] at h1
  linarith

/-- Merging `T` into `S` lowers the per-element weight of `S` when the parameters of the
union are at most three times those of `S` and the union is more than `3/2` times larger. -/
private lemma perElement_union_lt {S T : Finset (∀ i, Y i)} (hS : S.Nonempty)
    (hpar : ∀ J I, maxSection (S ∪ T) J I ≤ 3 * maxSection S J I)
    (hcard : 3 * S.card < 2 * (S ∪ T).card) :
    partLogSum (S ∪ T) -
        3 * (Fintype.card (Finset (Fin n) × Finset (Fin n)) : ℝ) * Real.log (S ∪ T).card <
      partLogSum S -
        3 * (Fintype.card (Finset (Fin n) × Finset (Fin n)) : ℝ) * Real.log S.card := by
  set K : ℝ := (Fintype.card (Finset (Fin n) × Finset (Fin n)) : ℝ) with hK
  have hKpos : 0 < K := by rw [hK]; exact_mod_cast Fintype.card_pos
  have hU : (S ∪ T).Nonempty := hS.mono Finset.subset_union_left
  have h1 : partLogSum (S ∪ T) ≤ K * Real.log 3 + partLogSum S := by
    have hle : ∀ P : Finset (Fin n) × Finset (Fin n), Real.log (maxSection (S ∪ T) P.1 P.2) ≤
        Real.log 3 + Real.log (maxSection S P.1 P.2) := by
      intro P
      have hp : (0 : ℝ) < maxSection (S ∪ T) P.1 P.2 :=
        Nat.cast_pos.2 (one_le_maxSection_of_nonempty hU P.1 P.2)
      have hq : (0 : ℝ) < maxSection S P.1 P.2 :=
        Nat.cast_pos.2 (one_le_maxSection_of_nonempty hS P.1 P.2)
      rw [← Real.log_mul (by norm_num) hq.ne']
      exact Real.log_le_log hp (by exact_mod_cast hpar P.1 P.2)
    have := Finset.sum_le_sum (s := Finset.univ) fun P _ => hle P
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    exact this
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have h2 : Real.log (3 / 2) + Real.log S.card < Real.log (S ∪ T).card := by
    rw [← Real.log_mul (by norm_num) hSpos.ne']
    refine Real.log_lt_log (by positivity) ?_
    have : (3 : ℝ) * S.card < 2 * (S ∪ T).card := by exact_mod_cast hcard
    linarith
  have h3 : Real.log 3 ≤ 3 * Real.log (3 / 2) := by
    have e : (3 : ℝ) * Real.log (3 / 2) = Real.log ((3 / 2) ^ 3) := by
      rw [Real.log_pow]; norm_num
    rw [e]; exact Real.log_le_log (by norm_num) (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left h3 hKpos.le, mul_lt_mul_of_pos_left h2 hKpos]

/-- **Merging lowers the weight.**  Two disjoint non-empty parts whose sizes and parameters
all have the same binary logarithm can be merged with a gain, for the weight constant
`D = 3 · #{(J, I)}`. -/
private lemma partWeight_union_lt {S T : Finset (∀ i, Y i)} (hS : S.Nonempty)
    (hT : T.Nonempty) (hST : Disjoint S T) (hcard : Nat.log 2 S.card = Nat.log 2 T.card)
    (hpar : ∀ J I, Nat.log 2 (maxSection S J I) = Nat.log 2 (maxSection T J I)) :
    partWeight (3 * (Fintype.card (Finset (Fin n) × Finset (Fin n)) : ℝ)) (S ∪ T) <
      partWeight (3 * (Fintype.card (Finset (Fin n) × Finset (Fin n)) : ℝ)) S +
        partWeight (3 * (Fintype.card (Finset (Fin n) × Finset (Fin n)) : ℝ)) T := by
  have hTS := lt_two_mul_of_log_eq hS.card_pos.ne' hcard
  have hST' := lt_two_mul_of_log_eq hT.card_pos.ne' hcard.symm
  have hU : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hST
  have hparS : ∀ J I, maxSection (S ∪ T) J I ≤ 3 * maxSection S J I := by
    intro J I
    have := lt_two_mul_of_log_eq
      (Nat.one_le_iff_ne_zero.1 (one_le_maxSection_of_nonempty hS J I)) (hpar J I)
    have := maxSection_union_le_add S T J I
    omega
  have hparT : ∀ J I, maxSection (T ∪ S) J I ≤ 3 * maxSection T J I := by
    intro J I
    have := lt_two_mul_of_log_eq (Nat.one_le_iff_ne_zero.1 (one_le_maxSection_of_nonempty hT J I))
      (hpar J I).symm
    have := maxSection_union_le_add T S J I
    omega
  have gS := perElement_union_lt hS hparS (by omega)
  have gT := perElement_union_lt hT hparT (by rw [Finset.union_comm, hU]; omega)
  rw [Finset.union_comm T S] at gT
  rw [hU, Nat.cast_add] at gS gT
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  simp only [partWeight, hU, Nat.cast_add]
  nlinarith [mul_lt_mul_of_pos_left gS hSpos, mul_lt_mul_of_pos_left gT hTpos]

/-- **Every part of a minimal-weight partition is `e^{2Dn}`-uniform**: otherwise the ratio
criterion fails at some step, and splitting that part at the geometric mean lowers the total
weight. -/
private lemma isCUniform_of_minimal {A : Finset (∀ i, Y i)} {P : Finset (Finset (∀ i, Y i))}
    {D : ℝ} (hD : 0 ≤ D) (hP : IsPartitionOf A P)
    (hmin : ∀ Q, IsPartitionOf A Q →
      ∑ S ∈ P, partWeight D S ≤ ∑ S ∈ Q, partWeight D S)
    {S : Finset (∀ i, Y i)} (hS : S ∈ P) : IsCUniform (Real.exp (2 * D) ^ n) S := by
  refine isCUniform_of_ratio (hP.1 S hS) (Real.exp_pos _).le fun σ k => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨S₁, S₂, h₁, h₂, hd, rfl, g₁, g₂⟩ :=
    exists_split_of_ratio (hP.1 _ hS) hD (σ k) (earlierIndices σ k) hlt
  have hw := partWeight_add_lt_of_split h₁ h₂ hd hD g₁ g₂
  obtain ⟨hQ, hsum⟩ := isPartitionOf_split hP hS hd h₁ h₂
  have := hmin _ hQ
  rw [hsum] at this
  linarith

/-- **A minimal-weight partition has few parts**: two distinct parts cannot have the same
binary logarithms of their sizes and of all their parameters (merging them would lower the
weight), and these logarithms range over `0, …, ⌊log₂ |A|⌋`. -/
private lemma card_le_of_minimal {A : Finset (∀ i, Y i)} {P : Finset (Finset (∀ i, Y i))}
    (hP : IsPartitionOf A P)
    (hmin : ∀ Q, IsPartitionOf A Q →
      ∑ S ∈ P, partWeight (3 * (Fintype.card (Finset (Fin n) × Finset (Fin n)) : ℝ)) S ≤
        ∑ S ∈ Q, partWeight (3 * (Fintype.card (Finset (Fin n) × Finset (Fin n)) : ℝ)) S) :
    P.card ≤ (Nat.log 2 A.card + 1) ^ (Fintype.card (Finset (Fin n) × Finset (Fin n)) + 1) := by
  classical
  set L := Nat.log 2 A.card with hL
  let key : Finset (∀ i, Y i) → ℕ × (Finset (Fin n) × Finset (Fin n) → ℕ) :=
    fun S => (Nat.log 2 S.card, fun P => Nat.log 2 (maxSection S P.1 P.2))
  have hsub : ∀ S ∈ P, S ⊆ A := fun S hS a ha => (hP.2.2 a).2 ⟨S, hS, ha⟩
  let box : Finset (ℕ × (Finset (Fin n) × Finset (Fin n) → ℕ)) :=
    Finset.range (L + 1) ×ˢ Fintype.piFinset fun _ => Finset.range (L + 1)
  have hmaps : Set.MapsTo key P box := by
    intro S hS
    have hcard : S.card ≤ A.card := Finset.card_le_card (hsub S hS)
    simp only [box, Finset.mem_coe, Finset.mem_product, Finset.mem_range,
      Fintype.mem_piFinset, key]
    refine ⟨Nat.lt_succ_of_le (Nat.log_mono_right hcard), fun P => ?_⟩
    exact Nat.lt_succ_of_le (Nat.log_mono_right ((maxSection_le_card S _ _).trans hcard))
  have hinj : Set.InjOn key P := by
    intro S hS T hT hkey
    by_contra hne
    simp only [key, Prod.mk.injEq] at hkey
    obtain ⟨hcard, hpar⟩ := hkey
    have hw := partWeight_union_lt (hP.1 S hS) (hP.1 T hT) (hP.2.1 S hS T hT hne) hcard
      fun J I => congrFun hpar (J, I)
    obtain ⟨hQ, hsum⟩ := isPartitionOf_merge hP hS hT hne
    have := hmin _ hQ
    rw [hsum] at this
    linarith
  have := Finset.card_le_card_of_injOn key hmaps hinj
  rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_range,
    Finset.card_univ, ← pow_succ'] at this
  exact this

end Partition

/-- The combinatorial decomposition of Alon, Newman, Shen, Tardos and Vereshchagin: every
finite set `A ⊆ Y_1 × ⋯ × Y_n` can be **partitioned** into at most `(2 + log₂ |A|)^d` disjoint
parts, each of which is `c`-uniform with a constant `c` that depends only on `n`, not on `A`.
The book writes "polynomially many in `log |A|`" parts; the `2` in `(2 + log₂ |A|)^d` is a
repair of the degenerate small-alphabet case (`(log |A|)^d ≤ 1` for `|A| ≤ 2`), equivalent to
the printed polynomial up to a change of `d` for `|A| ≥ 4`; see the module docstring.  The
book only sketches the argument (a minimal-weight partition, with weight
`∑_{A,B} log m_X(B | A) − d log |X|`) and refers to its reference [3] for the details.
SUV Section 10.9, pp. 334–336 (unnumbered). -/
theorem exists_cUniform_partition_const :
    ∃ (c : ℝ) (d : ℕ), ∀ (Y : Fin n → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
      (A : Finset (∀ i, Y i)),
      ∃ (m : ℕ) (B : Fin m → Finset (∀ i, Y i)),
        (m : ℝ) ≤ (2 + Real.logb 2 A.card) ^ d ∧
          (∀ k l, k ≠ l → Disjoint (B k) (B l)) ∧ A = Finset.univ.biUnion B ∧
          ∀ k, IsCUniform c (B k) := by
  set K : ℕ := Fintype.card (Finset (Fin n) × Finset (Fin n)) with hK
  refine ⟨Real.exp (2 * (3 * K)) ^ n, K + 1, fun Y _ _ A => ?_⟩
  obtain ⟨P, hP, hmin⟩ := exists_isPartitionOf_min A
    fun Q => ∑ S ∈ Q, partWeight (3 * (K : ℝ)) S
  have hD : (0 : ℝ) ≤ 3 * K := by positivity
  refine ⟨P.card, fun k => (P.equivFin.symm k).1, ?_, ?_, ?_, ?_⟩
  · have hcard := card_le_of_minimal hP hmin
    have hlog : ((Nat.log 2 A.card + 1 : ℕ) : ℝ) ≤ 2 + Real.logb 2 A.card := by
      have h1 := Real.natLog_le_logb A.card 2
      push_cast at h1 ⊢
      linarith
    calc (P.card : ℝ) ≤ ((Nat.log 2 A.card + 1) ^ (K + 1) : ℕ) := by exact_mod_cast hcard
      _ = ((Nat.log 2 A.card + 1 : ℕ) : ℝ) ^ (K + 1) := by push_cast; ring
      _ ≤ (2 + Real.logb 2 A.card) ^ (K + 1) := pow_le_pow_left₀ (by positivity) hlog _
  · intro k l hkl
    have hne : (P.equivFin.symm k).1 ≠ (P.equivFin.symm l).1 := fun h =>
      hkl (P.equivFin.symm.injective (Subtype.ext h))
    exact hP.2.1 _ (P.equivFin.symm k).2 _ (P.equivFin.symm l).2 hne
  · ext a
    rw [hP.2.2 a, Finset.mem_biUnion]
    constructor
    · rintro ⟨S, hS, haS⟩
      exact ⟨P.equivFin ⟨S, hS⟩, Finset.mem_univ _, by simpa using haS⟩
    · rintro ⟨k, -, hak⟩
      exact ⟨_, (P.equivFin.symm k).2, hak⟩
  · intro k
    exact isCUniform_of_minimal hD hP hmin (P.equivFin.symm k).2


/-- Relativized typization produces polynomially many types, all uniformly controlled by a
constant depending only on the number of coordinates. -/
private lemma exists_typization_candidate :
    ∃ q d : ℕ, ∀ (Y : Fin n → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
      (A : Finset (∀ i, Y i)), ∃ (m : ℕ) (B : Fin m → Finset (∀ i, Y i)),
        (m : ℝ) ≤ (2 + Real.logb 2 A.card) ^ d ∧ A = Finset.univ.biUnion B ∧
          ∀ k, IsCUniform ((2 : ℝ) ^ q) (B k) := by
  obtain ⟨c, d, hc⟩ := exists_cUniform_partition_const (n := n)
  have ⟨q, hq⟩ : ∃ q : ℕ, c ≤ (2 : ℝ) ^ q := by
    obtain ⟨q, hq⟩ := exists_nat_gt c
    refine ⟨q, ?_⟩
    calc c ≤ q := hq.le
      _ ≤ (2 : ℝ) ^ q := by exact_mod_cast Nat.lt_two_pow_self.le
  refine ⟨q, d, fun Y _ _ A => ?_⟩
  obtain ⟨m, B, h1, h2, h3, h4⟩ := hc Y A
  refine ⟨m, B, h1, h3, fun k => ?_⟩
  have hU := h4 k
  intro σ
  calc (chainBound (B k) σ : ℝ) ≤ c * (B k).card := hU σ
    _ ≤ ((2 : ℝ) ^ q) * (B k).card := by gcongr

/-- A fixed power-of-two uniformity loss and a polynomial cover bound can be absorbed into
one exponent because the repaired logarithmic parameter is at least two. -/
private lemma exists_cUniform_exponent_of_candidate (q d : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    ∃ e : ℕ, e = q + d ∧ x ^ d ≤ x ^ e ∧ (2 : ℝ) ^ q ≤ x ^ e := by
  refine ⟨q + d, rfl, pow_le_pow_right₀ (by linarith) (by omega), ?_⟩
  exact (pow_le_pow_left₀ (by norm_num) hx q).trans
    (pow_le_pow_right₀ (by linarith) (by omega))

/-- **The decomposition lemma of Section 10.9.**  Every finite set `A ⊆ Y_1 × ⋯ × Y_n` is the
union of polynomially many (in `log |A|`) parts, each of which is `c`-uniform for some `c`
polynomial in `log |A|`; the parts need not be disjoint.  Here both polynomials are
`(2 + log₂ |A|)^d` for a constant `d` depending on `n` only — the `2` is a repair of the
degenerate small-alphabet case (`(log |A|)^d ≤ 1` for `|A| ≤ 2`), equivalent to the printed
polynomial up to a change of `d` for `|A| ≥ 4`; see the module docstring.  The book's proof
relativises the typization trick of Theorem 211 to the condition `A`.
SUV Lemma, p. 333. -/
theorem exists_cUniform_cover :
    ∃ d : ℕ, ∀ (Y : Fin n → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
      (A : Finset (∀ i, Y i)),
      ∃ (m : ℕ) (B : Fin m → Finset (∀ i, Y i)),
        (m : ℝ) ≤ (2 + Real.logb 2 A.card) ^ d ∧ A = Finset.univ.biUnion B ∧
          ∀ k, IsCUniform ((2 + Real.logb 2 A.card) ^ d) (B k) := by
  obtain ⟨q, d, hcand⟩ := exists_typization_candidate (n := n)
  refine ⟨q + d, fun Y _ _ A => ?_⟩
  obtain ⟨m, B, hm, hcover, hU⟩ := hcand Y A
  have hlog : 0 ≤ Real.logb 2 A.card := by
    by_cases hA : A.card = 0
    · simp [hA, Real.logb]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast A.card.pos_of_ne_zero hA)
  obtain ⟨e, he, hcount, huniform⟩ := exists_cUniform_exponent_of_candidate q d (by linarith :
    (2 : ℝ) ≤ 2 + Real.logb 2 A.card)
  subst e
  refine ⟨m, B, hm.trans hcount, hcover, fun k σ => (hU k σ).trans ?_⟩
  exact mul_le_mul_of_nonneg_right huniform (Nat.cast_nonneg _)

/-- Recoding coordinates injectively preserves projection cardinalities. -/
private lemma projCard_image_coordwise {Y Z : Fin n → Type} [∀ i, DecidableEq (Y i)]
    [∀ i, DecidableEq (Z i)] (g : ∀ i, Z i → Y i) (hg : ∀ i, Function.Injective (g i))
    (B : Finset (∀ i, Z i)) (I : Finset (Fin n)) :
    projCard (B.image fun b i => g i (b i)) I = projCard B I := by
  unfold projCard proj
  rw [Finset.image_image]
  have h : (restrictTo I ∘ fun b i => g i (b i)) =
      (fun p (i : I) => g i.val (p i)) ∘ restrictTo (X := Z) I := rfl
  rw [h, ← Finset.image_image, Finset.card_image_of_injective]
  intro p q hpq
  funext i
  exact hg i.val (congrFun hpq i)

/-- The projection product `∏_I m_B(I)^{f_I}` of a non-empty set is `2` raised to the value of
`f` on the log-sizes of the projections of `B`. -/
theorem prod_projCard_rpow_eq_two_rpow {Y : Fin n → Type} [∀ i, DecidableEq (Y i)]
    (f : LinearForm n) {B : Finset (∀ i, Y i)} (hB : B.Nonempty) :
    ∏ I ∈ nonemptyParts n, (projCard B I : ℝ) ^ f I = (2 : ℝ) ^ f.evalLogSize B := by
  rw [LinearForm.evalLogSize, Real.rpow_sum_of_pos (by norm_num)]
  refine Finset.prod_congr rfl fun I _ => ?_
  have hp : (0 : ℝ) < projCard B I := by
    exact_mod_cast Finset.card_pos.2 (hB.image _)
  rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hp]

/-- The empty set satisfies the projection-product bound with right side one. -/
private lemma prod_projCard_rpow_empty_le_one {Y : Fin n → Type} [∀ i, DecidableEq (Y i)]
    (f : LinearForm n) :
    ∏ I ∈ nonemptyParts n, (projCard (∅ : Finset (∀ i, Y i)) I : ℝ) ^ f I ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => by positivity)
    (fun I _ => by simpa [projCard, proj] using Real.zero_rpow_le_one (f I))

/-- **Entropy inequality ⟹ union decomposition** (the direction of SUV Theorem 214 that goes
through entropies).  If the linear inequality `f` holds for entropies, then every finite set `A`
is the union of at most `(2 + log₂ |A|)^d` parts, each satisfying the product inequality
`∏_I m(I)^{f_I} ≤ (2 + log₂ |A|)^d` for its own projections: a minimal-weight partition into
`c`-uniform parts does it, by the almost-uniform estimate.  SUV Theorem 214, p. 333. -/
theorem exists_union_decomposition_of_holdsForEntropies (f : LinearForm n)
    (hf : HoldsForEntropies f) :
    ∃ d : ℕ, ∀ (Y : Fin n → Type) [∀ i, DecidableEq (Y i)] (A : Finset (∀ i, Y i)),
        ∃ (m : ℕ) (B : Fin m → Finset (∀ i, Y i)),
          (m : ℝ) ≤ (2 + Real.logb 2 A.card) ^ d ∧ A = Finset.univ.biUnion B ∧
          ∀ k, ∏ I ∈ nonemptyParts n, (projCard (B k) I : ℝ) ^ f I
            ≤ (2 + Real.logb 2 A.card) ^ d := by
  obtain ⟨c, d0, hpart⟩ := exists_cUniform_partition_const (n := n)
  set S : ℝ := ∑ I ∈ nonemptyParts n, |f I|
  refine ⟨d0 + ⌈S * Real.logb 2 c⌉₊, fun Y _ A => ?_⟩
  let Y' : Fin n → Type := fun i => {y // y ∈ A.image fun a => a i}
  let : ∀ i, Fintype (Y' i) := fun i => inferInstanceAs (Fintype {y // _})
  let : ∀ i, DecidableEq (Y' i) := fun i => inferInstanceAs (DecidableEq {y // _})
  let ψ : (∀ i, Y' i) → ∀ i, Y i := fun b i => (b i).val
  have hψ : ∀ i, Function.Injective (fun y : Y' i => y.val) :=
    fun i => Subtype.val_injective
  let A' : Finset (∀ i, Y' i) :=
    A.attach.image fun a i => ⟨a.1 i, Finset.mem_image_of_mem _ a.2⟩
  have hA' : A'.image ψ = A := by
    ext a
    simp only [A', ψ, Finset.image_image, Finset.mem_image, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.2
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  have hcardA : A'.card = A.card := by
    refine le_antisymm (Finset.card_image_le.trans (by simp)) ?_
    conv_lhs => rw [← hA']
    exact Finset.card_image_le
  obtain ⟨m, B', hm, -, hunion, hunif⟩ := hpart Y' A'
  have hL : (0 : ℝ) ≤ Real.logb 2 A.card := by
    rcases Nat.eq_zero_or_pos A.card with h | h
    · simp [h]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)
  have hbase : (1 : ℝ) ≤ 2 + Real.logb 2 A.card := by linarith
  refine ⟨m, fun k => (B' k).image ψ, ?_, ?_, fun k => ?_⟩
  · rw [← hcardA]
    exact hm.trans (pow_le_pow_right₀ (by rw [hcardA]; exact hbase) (by omega))
  · rw [← hA', hunion]
    ext a
    simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨b, ⟨l, hl⟩, rfl⟩
      exact ⟨l, b, hl, rfl⟩
    · rintro ⟨l, b, hl, rfl⟩
      exact ⟨b, ⟨l, hl⟩, rfl⟩
  · have hproj : ∀ I, projCard ((B' k).image ψ) I = projCard (B' k) I := fun I =>
      projCard_image_coordwise (fun i (y : Y' i) => y.val) hψ (B' k) I
    simp only [hproj]
    rcases (B' k).eq_empty_or_nonempty with hk | hk
    · rw [hk]
      exact (prod_projCard_rpow_empty_le_one f).trans (one_le_pow₀ hbase)
    rw [prod_projCard_rpow_eq_two_rpow f hk]
    have hE := evalLogSize_le_of_isCUniform f hf (B' k) hk (hunif k)
    calc
      (2 : ℝ) ^ f.evalLogSize (B' k) ≤
          (2 : ℝ) ^ ((d0 + ⌈S * Real.logb 2 c⌉₊ : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        refine hE.trans ?_
        have := Nat.le_ceil (S * Real.logb 2 c)
        push_cast
        linarith [(Nat.cast_nonneg d0 : (0 : ℝ) ≤ d0)]
      _ = (2 : ℝ) ^ (d0 + ⌈S * Real.logb 2 c⌉₊) := Real.rpow_natCast _ _
      _ ≤ (2 + Real.logb 2 A.card) ^ (d0 + ⌈S * Real.logb 2 c⌉₊) :=
        pow_le_pow_left₀ (by norm_num) (by linarith) _

end Kolmogorov
