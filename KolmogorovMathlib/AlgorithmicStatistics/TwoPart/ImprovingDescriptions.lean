import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.NonStochastic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-!
# Improving Descriptions (Phase D infrastructure)

This module builds the decoder and counting infrastructure for the
improving descriptions theorem (P-IMP). It defines the finite universe
of descriptions and sets up the counting facts.
-/

/-- A model code `c` represents a canonical uniform distribution if the model
it decodes to is exactly the canonical `codedUniformOn` its own support. -/
def isCanonicalUniformCode (c : BitString) : Prop :=
  let P := probModelOfCode c
  ∃ h : P.support.Nonempty, c = (codedUniformOn P.support h).code

noncomputable instance (c : BitString) : Decidable (isCanonicalUniformCode c) :=
  Classical.propDecidable _

/-- The finite universe of sets whose canonical uniform distribution has
plain prefix complexity `≤ i`. -/
noncomputable def descriptionsWithComplexityLe (U : Map) (i : ℕ) : Finset (Finset BitString) :=
  (modelsWithComplexityLe U i).biUnion (fun c =>
    if isCanonicalUniformCode c
    then { (probModelOfCode c).support }
    else ∅)

/-- A set with canonical uniform-code complexity `≤ i` appears in the finite
description universe.  The converse is deliberately not stated: the Section 2
enumerator `modelsWithComplexityLe` uses a dummy output for non-halting
programs, so raw membership in that image does not by itself provide a real
program for the code. -/
theorem mem_descriptionsWithComplexityLe_of_complexity {U : Map} {i : ℕ} {S : Finset BitString}
    (hS : S.Nonempty) (hcomp : setComplexity U S hS ≤ (i : ENat)) :
    S ∈ descriptionsWithComplexityLe U i := by
  unfold descriptionsWithComplexityLe
  simp only [Finset.mem_biUnion]
  have hc_mem := code_mem_modelsWithComplexityLe U (codedUniformOn S hS) i hcomp
  refine ⟨(codedUniformOn S hS).code, hc_mem, ?_⟩
  have h_prob := codedUniformOn_isProbability S hS
  have h_prob_eq := probModelOfCode_eq h_prob
  have h_supp : (probModelOfCode (codedUniformOn S hS).code).support = S := by
    rw [h_prob_eq]
    exact codedUniformOn_support S hS
  split
  · rw [h_supp]
    exact Finset.mem_singleton.mpr rfl
  · rename_i h_not_canon
    apply False.elim
    apply h_not_canon
    have hS_ne' : (probModelOfCode (codedUniformOn S hS).code).support.Nonempty := by
      rw [h_supp]
      exact hS
    refine ⟨hS_ne', ?_⟩
    exact codedUniformOn_code_congr hS hS_ne' h_supp.symm

/-
Gate E2 helper: Any set in the description universe of complexity bound `i`
actually has canonical uniform-code complexity `≤ i + O(1)`.

Proof idea: membership in `descriptionsWithComplexityLe U i` gives a coded model
whose support is exactly `S` and whose code has complexity `≤ i`; convert that code
to the canonical uniform code of `S` by a computable support-normalization map,
paying only the optimal-machine invariance constant.
-/
theorem setComplexity_le_of_mem_descriptionsWithComplexityLe (U : Map) :
    ∃ c : ℕ, ∀ (i : ℕ) (S : Finset BitString) (hS : S.Nonempty),
      S ∈ descriptionsWithComplexityLe U i →
      setComplexity U S hS ≤ (i + c : ENat) := by
  use 0; intros i S hS h_mem; exact (by
  have h_code : ∃ c : BitString, c ∈ modelsWithComplexityLe U i ∧ isCanonicalUniformCode c ∧ S =
      (probModelOfCode c).support := by
    unfold descriptionsWithComplexityLe at h_mem; aesop;
  obtain ⟨c, hc_mem, hc_canonical, hc_support⟩ := h_code
  have hc_eq : c = (codedUniformOn S hS).code := by
    convert hc_canonical.choose_spec using 1;
    exact hc_support ▸ rfl
  have h_complexity : KPPlain U c ≤ i := by
    have h_code : ∃ p : BitString, p ∈ boundedPrograms i ∧ modelCodeOfProgram U p = c := by
      exact List.mem_toFinset.mp ( Finset.mem_image.mp hc_mem |> Classical.choose_spec |> And.left )
        |> fun h => ⟨ _, h, Finset.mem_image.mp hc_mem |> Classical.choose_spec |> And.right ⟩
    obtain ⟨ p, hp_mem, hp_eq ⟩ := h_code
    have h_produces : produces U p [] c := by
      unfold modelCodeOfProgram at hp_eq;
      split_ifs at hp_eq;
      · exact ⟨ by assumption, hp_eq ⟩;
      · subst hp_eq; simp only [codedUniformOn] at hc_eq
        cases h : canonicalFinsetList S with
        | nil =>
          have h1 : S.card = 0 := by rw [← length_canonicalFinsetList S, h, List.length_nil]
          have h2 : 0 < S.card := Finset.card_pos.mpr hS
          omega
        | cons hd tl =>
          revert hc_eq
          rw [h]
          intro hc_eq
          cases hc_eq
    have h_complexity : KPPlain U c ≤ (programLength p : ENat) := by
      exact KPPlain_eq_KP U c ▸ KP_le_programLength_of_produces h_produces
    have h_bound : (programLength p : ENat) ≤ i := by
      exact_mod_cast mem_boundedPrograms_iff p i |>.1 hp_mem
    exact le_trans h_complexity h_bound
  have h_setComplexity : setComplexity U S hS = KPPlain U c := by
    exact hc_eq ▸ rfl
  rw [h_setComplexity]
  exact h_complexity.trans (by norm_num))

/-
The number of descriptions in the universe of complexity `≤ i` is bounded.
-/
theorem card_descriptionsWithComplexityLe (U : Map) (i : ℕ) :
    (descriptionsWithComplexityLe U i).card ≤ 2 ^ (i + 1) := by
  refine le_trans ?_ ( card_modelsWithComplexityLe U i );
  exact Finset.card_biUnion_le.trans ( Finset.sum_le_card_nsmul _ _ _ fun x hx => by aesop )
    |> le_trans <| by norm_num

/-- The subset of descriptions of size `≤ 2 ^ j`. -/
noncomputable def descriptionsWithComplexityLeAndSizeLe (U : Map) (i j : ℕ) : Finset
    (Finset BitString) :=
  (descriptionsWithComplexityLe U i).filter (fun S => S.card ≤ 2 ^ j)

theorem card_descriptionsWithComplexityLeAndSizeLe (U : Map) (i j : ℕ) :
    (descriptionsWithComplexityLeAndSizeLe U i j).card ≤ 2 ^ (i + 1) := by
  unfold descriptionsWithComplexityLeAndSizeLe
  exact le_trans (Finset.card_filter_le _ _) (card_descriptionsWithComplexityLe U i)

/-- The finite enumeration of model codes is monotone in the complexity bound:
allowing longer programs can only add codes. -/
theorem modelsWithComplexityLe_subset_of_le (U : Map) {i i' : ℕ} (h : i ≤ i') :
    modelsWithComplexityLe U i ⊆ modelsWithComplexityLe U i' := by
  unfold modelsWithComplexityLe
  refine Finset.image_subset_image ?_
  intro p hp
  rw [List.mem_toFinset] at hp ⊢
  exact (mem_boundedPrograms_iff _ _).mpr (((mem_boundedPrograms_iff _ _).mp hp).trans h)

/-- The description universe is monotone in the complexity bound. -/
theorem descriptionsWithComplexityLe_subset_of_le (U : Map) {i i' : ℕ} (h : i ≤ i') :
    descriptionsWithComplexityLe U i ⊆ descriptionsWithComplexityLe U i' := by
  unfold descriptionsWithComplexityLe
  exact Finset.biUnion_subset_biUnion_of_subset_left _ (modelsWithComplexityLe_subset_of_le U h)

/-- The size-restricted description universe is monotone in the complexity bound `i`. -/
theorem descriptionsWithComplexityLeAndSizeLe_subset_of_le_left (U : Map) (j : ℕ) {i i' : ℕ}
    (h : i ≤ i') :
    descriptionsWithComplexityLeAndSizeLe U i j ⊆ descriptionsWithComplexityLeAndSizeLe U i' j := by
  unfold descriptionsWithComplexityLeAndSizeLe
  exact Finset.filter_subset_filter _ (descriptionsWithComplexityLe_subset_of_le U h)

/-- The size-restricted description universe is monotone in the size bound `j`. -/
theorem descriptionsWithComplexityLeAndSizeLe_subset_of_le_right (U : Map) (i : ℕ) {j j' : ℕ}
    (h : j ≤ j') :
    descriptionsWithComplexityLeAndSizeLe U i j ⊆ descriptionsWithComplexityLeAndSizeLe U i j' := by
  unfold descriptionsWithComplexityLeAndSizeLe
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, hS.2.trans (Nat.pow_le_pow_right (by decide) h)⟩

/-- `ManyIJDescriptions U x i j k` means that `x` is contained in at least `2^k` distinct
`finset` models from the valid universe of `(i*j)`-descriptions. -/
noncomputable def ManyIJDescriptions (U : Map) (x : BitString) (i j k : ℕ) : Prop :=
  2 ^ k ≤ ((descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S)).card

/-- Parameter-log-slack form of the size-improvement half of the
improving-descriptions proposition.  The explicit length parameter records the
string length, while the slack argument `n + i + j` honestly pays for encoding
the visible description parameters.

Architectural note: in the standard Section 3 organization this is a corollary,
not the main theorem.  The primary improving-descriptions statement should be
`ManyIJDescriptions -> (i - k, j) + O(log n)` (`ImprovingDescriptionsComplexityLogSlack`
below).  The `(i, j - k)` form should then be obtained from that stronger
statement by the ordinary portion/description-shift lemma, rather than by proving
an independent selector theorem. -/
def ImprovingDescriptionsSizeLogSlack (U : Map) : Prop :=
  ∃ c : ℕ, ∀ x n i j k,
    x.length = n →
    ManyIJDescriptions U x i j k →
    k ≤ j →
    InDescriptionProfile U x (i + logSlack c (n + i + j)) (j - k + logSlack c (n + i + j))

/-- Parameter-log-slack form of the complexity-improvement half of the
improving-descriptions proposition.  This is the main standard statement:
from many `(i,j)` descriptions of `x`, produce an `(i-k,j)` description with
visible logarithmic slack.  The size-improvement form should be downstream of
this statement, not a separate foundational obligation. -/
def ImprovingDescriptionsComplexityLogSlack (U : Map) : Prop :=
  ∃ c : ℕ, ∀ x n i j k,
    x.length = n →
    ManyIJDescriptions U x i j k →
    k ≤ i →
    InDescriptionProfile U x (i - k + logSlack c (n + i + j)) (j + logSlack c (n + i + j))

/-- Having `2^k` descriptions is monotone (downward) in the count exponent `k`:
if `x` has at least `2^k` distinct `(i,j)`-descriptions and `k' ≤ k`, then it has
at least `2^{k'}` of them. -/
theorem ManyIJDescriptions.mono_k {U : Map} {x : BitString} {i j k k' : ℕ}
    (h : k' ≤ k) (hmany : ManyIJDescriptions U x i j k) : ManyIJDescriptions U x i j k' := by
  unfold ManyIJDescriptions at *
  exact le_trans (Nat.pow_le_pow_right (by norm_num) h) hmany

/-- Having `2^k` descriptions is monotone (upward) in the complexity bound `i`:
enlarging the complexity budget can only add descriptions. -/
theorem ManyIJDescriptions.mono_i {U : Map} {x : BitString} {i i' j k : ℕ}
    (h : i ≤ i') (hmany : ManyIJDescriptions U x i j k) : ManyIJDescriptions U x i' j k := by
  unfold ManyIJDescriptions at *
  refine hmany.trans (Finset.card_le_card ?_)
  exact Finset.filter_subset_filter _
    (descriptionsWithComplexityLeAndSizeLe_subset_of_le_left U j h)

/-- Having `2^k` descriptions is monotone (upward) in the size bound `j`:
enlarging the size budget can only add descriptions. -/
theorem ManyIJDescriptions.mono_j {U : Map} {x : BitString} {i j j' k : ℕ}
    (h : j ≤ j') (hmany : ManyIJDescriptions U x i j k) : ManyIJDescriptions U x i j' k := by
  unfold ManyIJDescriptions at *
  refine hmany.trans (Finset.card_le_card ?_)
  exact Finset.filter_subset_filter _
    (descriptionsWithComplexityLeAndSizeLe_subset_of_le_right U i h)

/-- The **rich elements** of the `(i,j)`-description universe: those points that
belong to at least `2^k` distinct `(i,j)`-descriptions.  This is the combinatorial
ingredient of the half-rich trick: every element with many descriptions is rich
(`mem_richDescriptionElements_of_many`), and the double-counting bound
`card_richDescriptionElements_mul_le` shows there cannot be too many rich
elements. -/
noncomputable def richDescriptionElements (U : Map) (i j k : ℕ) : Finset BitString :=
  ((descriptionsWithComplexityLeAndSizeLe U i j).biUnion id).filter
    (fun y => 2 ^ k ≤ ((descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => y ∈ S)).card)

/-
An element with at least `2^k` descriptions is a rich element.
-/
theorem mem_richDescriptionElements_of_many (U : Map) (x : BitString) (i j k : ℕ)
    (h : ManyIJDescriptions U x i j k) :
    x ∈ richDescriptionElements U i j k := by
  refine Finset.mem_filter.mpr ⟨?_, h⟩
  unfold ManyIJDescriptions at h
  have hpos : 0 < ((descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S)).card :=
    lt_of_lt_of_le (by positivity) h
  obtain ⟨S, hS⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hS
  exact Finset.mem_biUnion.mpr ⟨S, hS.1, hS.2⟩

/-- Converse of `mem_richDescriptionElements_of_many`: a rich element of the
`(i,j)`-description universe necessarily has at least `2^k` distinct
`(i,j)`-descriptions.  This is the filter projection in the definition of
`richDescriptionElements`. -/
theorem manyIJDescriptions_of_mem_richDescriptionElements (U : Map) (x : BitString) (i j k : ℕ)
    (h : x ∈ richDescriptionElements U i j k) :
    ManyIJDescriptions U x i j k :=
  (Finset.mem_filter.mp h).2

/-- Being a rich element of the `(i,j)`-description universe is exactly having
many descriptions: it combines `mem_richDescriptionElements_of_many` with its
converse `manyIJDescriptions_of_mem_richDescriptionElements`. -/
theorem mem_richDescriptionElements_iff_many (U : Map) (x : BitString) (i j k : ℕ) :
    x ∈ richDescriptionElements U i j k ↔ ManyIJDescriptions U x i j k :=
  ⟨manyIJDescriptions_of_mem_richDescriptionElements U x i j k,
    mem_richDescriptionElements_of_many U x i j k⟩

/--
**Double-counting bound for rich elements.**  The number of `2^k`-rich
elements, multiplied by `2^k`, is at most the total incidence count of the
description universe, which is at most `2^(i+1) * 2 ^ j` (there are at most
`2^(i+1)` descriptions, each of size at most `2 ^ j`).  Hence the rich set is a
small description of any of its members.
-/
theorem card_richDescriptionElements_mul_le (U : Map) (i j k : ℕ) :
    (richDescriptionElements U i j k).card * 2 ^ k ≤ 2 ^ (i + 1) * 2 ^ j := by
  -- Let `R := richDescriptionElements U i j k` and `F := descriptionsWithComplexityLeAndSizeLe U i
  --   j`.
  set R := richDescriptionElements U i j k
  set F := descriptionsWithComplexityLeAndSizeLe U i j;
  -- By definition of `richDescriptionElements`, we have `R.card * 2^k ≤ ∑ S ∈ F, (R.filter (fun y
  --   => y ∈ S)).card`.
  have h_card_le_sum : R.card * 2 ^ k ≤ ∑ S ∈ F, (R.filter (fun y => y ∈ S)).card := by
    have h_card_le_sum : ∀ y ∈ R, (2 : ℕ) ^ k ≤ ∑ S ∈ F, if y ∈ S then 1 else 0 := by
      simp only [Finset.sum_boole, Nat.cast_id] at *
      exact fun y hy => Finset.mem_filter.mp hy |>.2;
    calc R.card * 2 ^ k
        = ∑ _y ∈ R, 2 ^ k := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ y ∈ R, ∑ S ∈ F, if y ∈ S then 1 else 0 := Finset.sum_le_sum h_card_le_sum
      _ = ∑ S ∈ F, ∑ y ∈ R, if y ∈ S then 1 else 0 := Finset.sum_comm
      _ = ∑ S ∈ F, (R.filter (fun y => y ∈ S)).card := by simp only [Finset.card_filter]
  refine le_trans h_card_le_sum ?_;
  refine le_trans ( Finset.sum_le_sum fun S hS =>
    show Finset.card ( Finset.filter ( fun y => y ∈ S ) R ) ≤ 2 ^ j from ?_ ) ?_;
  · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( Finset.mem_filter.mp hS |>.2 );
  · norm_num [ mul_comm ];
    rw [ mul_comm ] ; gcongr ; exact card_descriptionsWithComplexityLeAndSizeLe U i j

/-- **Cardinality corollary of the double-counting bound.**  A `2^k`-rich set of
the `(i,j)`-description universe has at most `2^(i+1+j-k)` elements.  This is the
direct cardinality control fed into the half-rich trick: it follows from
`card_richDescriptionElements_mul_le` by dividing through by `2^k` (using
truncated subtraction so the bound holds unconditionally, including the
degenerate range `k > i+1+j` where the rich set is empty or a singleton). -/
theorem card_richDescriptionElements_le (U : Map) (i j k : ℕ) :
    (richDescriptionElements U i j k).card ≤ 2 ^ (i + 1 + j - k) := by
  have h := card_richDescriptionElements_mul_le U i j k
  rw [← pow_add] at h
  rcases le_or_gt k (i + 1 + j) with hk | hk
  · have hh : (richDescriptionElements U i j k).card * 2 ^ k ≤ 2 ^ (i + 1 + j - k) * 2 ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]; exact h
    exact Nat.le_of_mul_le_mul_right hh (by positivity)
  · have hsub : i + 1 + j - k = 0 := Nat.sub_eq_zero_of_le (le_of_lt hk)
    have hlt : 2 ^ (i + 1 + j) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hk
    rw [hsub, pow_zero]
    have hmul : (richDescriptionElements U i j k).card * 2 ^ k < 1 * 2 ^ k := by
      rw [one_mul]; exact lt_of_le_of_lt h hlt
    have := Nat.lt_of_mul_lt_mul_right hmul
    omega

/-- Faithful logarithmic-slack target for the size-improvement half.

The proof must use the snapshot/stopping-index selector bridge.  In particular,
one must not replace the hard selector step by a bound saying the abstract rich
set has complexity `O(log (i+j+k))`: producing the `U`-relative rich set also
pays for the stabilized enumeration data, and the visible-parameter slack
`logSlack c (n+i+j)` is the intended place to account for the remaining
parameter coding. -/
theorem card_descriptionsContaining_le (U : Map) (x : BitString) (i j : ℕ) :
    ((descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S)).card ≤ 2 ^ (i + 1) := by
  exact (Finset.card_filter_le _ _).trans (card_descriptionsWithComplexityLeAndSizeLe U i j)

/-- The count exponent of a many-descriptions hypothesis is bounded by `i + 1`:
since `x` has at most `2^(i+1)` distinct `(i,j)`-descriptions
(`card_descriptionsContaining_le`), `2^k ≤ 2^(i+1)` forces `k ≤ i + 1`.  This is
the structural fact that lets the size-improvement corollary handle the
otherwise-uncovered range `i < k` (only `k = i + 1` occurs). -/
theorem ManyIJDescriptions.le_succ {U : Map} {x : BitString} {i j k : ℕ}
    (h : ManyIJDescriptions U x i j k) : k ≤ i + 1 := by
  unfold ManyIJDescriptions at h
  have hc := card_descriptionsContaining_le U x i j
  have h2 : (2 : ℕ) ^ k ≤ 2 ^ (i + 1) := le_trans h hc
  by_contra hcon
  push Not at hcon
  exact absurd h2 (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) hcon))

/-- **Membership in the description universe of `x`.**  A nonempty set `A`
containing `x`, whose canonical uniform code has set-complexity `≤ i` and whose
size is `≤ 2^j`, is one of the `(i,j)`-descriptions of `x`, i.e. it belongs to
`(descriptionsWithComplexityLeAndSizeLe U i j).filter (· ∋ x)`.  This is the
membership step feeding the gap-counting bound
`description_count_of_conditional_complexity_gap`: the actual model `A` is one of
the finitely many descriptions whose rank then bounds `KP (code | x*)`. -/
theorem mem_descriptionsContaining_of_complexity {U : Map} {A : Finset BitString}
    (hA : A.Nonempty) {x : BitString} {i j : ℕ} (hxA : x ∈ A)
    (hcomp : setComplexity U A hA ≤ (i : ENat)) (hsize : A.card ≤ 2 ^ j) :
    A ∈ (descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S) := by
  rw [Finset.mem_filter]
  refine ⟨?_, hxA⟩
  rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
  exact ⟨mem_descriptionsWithComplexityLe_of_complexity hA hcomp, hsize⟩

-- Combinatorial core for the half-rich trick (size half)
def appearsAtLeast (L : List (Finset BitString)) (t : ℕ) : Finset BitString :=
  (L.toFinset.biUnion id).filter (fun x => 2 ^ t ≤ L.countP (fun S => x ∈ S))

theorem halfRich_card_le (L : List (Finset BitString)) (t j : ℕ)
    (h_size : ∀ S ∈ L, S.card ≤ 2 ^ j) :
    (appearsAtLeast L t).card * 2 ^ t ≤ L.length * 2 ^ j := by
  -- For each x in R, the sum of indicator variables in L is at least 2^t.
  have h_indicator_x : ∀ x ∈ appearsAtLeast L t, 2^t ≤ List.countP (fun S => x ∈ S) L := by
    unfold appearsAtLeast; aesop;
  have h_indicator_x_sum : ∑ x ∈ appearsAtLeast L t, List.countP (fun S => x ∈ S) L ≤ ∑ S ∈
      L.toFinset, (List.count S L) * S.card := by
    have h_indicator_x_sum : ∀ x ∈ appearsAtLeast L t, List.countP (fun S => x ∈ S) L = ∑ S ∈
        L.toFinset, (if x ∈ S then List.count S L else 0) := by
      simp only [List.countP_eq_length_filter, Finset.sum_ite, Finset.sum_const_zero, add_zero]
      intro x hx; rw [ ← Multiset.coe_card ] ; rw [ ← Multiset.toFinset_sum_count_eq ] ;
      refine Finset.sum_bij ( fun y _ => y ) ?_ ?_ ?_ ?_ <;> aesop;
    rw [ Finset.sum_congr rfl h_indicator_x_sum, Finset.sum_comm ];
    simp only [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, ge_iff_le, mul_comm]
    exact Finset.sum_le_sum fun x hx =>
      Nat.mul_le_mul_right _ ( Finset.card_le_card fun y hy => by aesop );
  have h_indicator_x_sum : ∑ S ∈ L.toFinset, (List.count S L) * S.card ≤ ∑ S ∈ L.toFinset,
      (List.count S L) * 2 ^ j := by
    exact Finset.sum_le_sum fun x hx =>
      Nat.mul_le_mul_left _ ( h_size x <| List.mem_toFinset.mp hx );
  have h_indicator_x_sum : ∑ S ∈ L.toFinset, (List.count S L) * 2 ^ j = L.length * 2 ^ j := by
    rw [ ← Finset.sum_mul _ _ _, List.sum_toFinset_count_eq_length ];
  exact le_trans ( by simpa using Finset.sum_le_sum h_indicator_x ) ( by linarith )

theorem halfRich_portion_count_le (L : List (Finset BitString)) (k j : ℕ)
    (h_size : ∀ S ∈ L, S.card ≤ 2 ^ j) :
    (appearsAtLeast L (k - 1)).card / 2 ^ j ≤ L.length / 2 ^ (k - 1) := by
  -- From `halfRich_card_le`: `R * 2^(k-1) ≤ N * 2^j`, where `R` is the number of
  -- half-rich portions and `N = L.length`.  Floor division is monotone, so this
  -- cross-multiplied bound yields `R / 2^j ≤ N / 2^(k-1)`.
  have hcard := halfRich_card_le L (k - 1) j h_size
  set R := (appearsAtLeast L (k - 1)).card with hR
  set N := L.length with hN
  rw [Nat.le_div_iff_mul_le (by positivity)]
  refine le_of_mul_le_mul_right ?_ (show (0 : ℕ) < 2 ^ j by positivity)
  calc R / 2 ^ j * 2 ^ (k - 1) * 2 ^ j
      = R / 2 ^ j * 2 ^ j * 2 ^ (k - 1) := by ring
    _ ≤ R * 2 ^ (k - 1) := by
        gcongr
        exact Nat.div_mul_le_self R (2 ^ j)
    _ ≤ N * 2 ^ j := hcard

end Kolmogorov
