import KolmogorovMathlib.MonotoneComplexity.ProbabilisticGenerator
import KolmogorovMathlib.MonotoneComplexity.NestedAllocation
import KolmogorovMathlib.MonotoneComplexity.PrefixStream
import KolmogorovMathlib.MonotoneComplexity.StreamTopology
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Every lower semicomputable continuous semimeasure comes from a probabilistic generator

The converse to the fact that a generator induces a semimeasure:
`exists_probabilisticGenerator_generatedTreeSemimeasure_eq` produces, for each lower
semicomputable continuous tree semimeasure, a probabilistic generator whose output distribution
is exactly it. The generator is read off a computable nested allocation:
`allocationLowerGraph` maps a random sequence to the strings the allocation assigns to its
prefixes, `allocationPrefixSet` collects the outputs — nonempty, prefix-closed and linearly
ordered, so it determines a stream — and `generatedTreeSemimeasure_allocation_eq` identifies the
resulting masses with the limit of the stage masses.
-/

namespace Kolmogorov

open Set MeasureTheory ENNReal BitStream

section AllocationGenerator

variable {q : ℕ → BitString → ℕ} (A : EffectiveNestedTreeAllocation q)

/-- The graph of the stream map realised by an allocation: `p` is mapped to an extension of `y`. -/
def allocationLowerGraph (p y : BitString) : Prop :=
  p ∈ (A.stage p.length).atoms y

/-- The graph of the allocation stream map is recursively enumerable. -/
lemma allocationLowerGraph_re :
    IsRE fun z : BitString × BitString => allocationLowerGraph A z.1 z.2 := by
  let check : BitString × BitString → Bool := fun z => decide (z.1 ∈ (A.stage z.1.length).atoms z.2)
  have h_iff : ∀ z, check z = true ↔ allocationLowerGraph A z.1 z.2 := by
    intro z
    dsimp [check, allocationLowerGraph]
    exact decide_eq_true_iff
  have h_comp : Computable check := by
    have h1 : Computable (fun z : BitString × BitString => ((z.1.length, z.2), z.1)) :=
      Computable.pair (Computable.pair
        (Computable.list_length.comp Computable.fst) Computable.snd) Computable.fst
    exact A.mem_computable.comp h1
  exact isRE_of_computable_bool _ check h_iff h_comp

/-- The strings the allocation outputs on the random sequence `w`. -/
def allocationPrefixSet (w : CantorSeq) : Set BitString :=
  {y | ∃ p, IsCantorPrefix p w ∧ allocationLowerGraph A p y}

/-- The empty string is always output. -/
lemma allocationPrefixSet_nonempty (w : CantorSeq) :
  [] ∈ allocationPrefixSet A w := by
  use []
  constructor
  · intro i hi; exfalso; apply Nat.not_lt_zero i hi
  · dsimp [allocationLowerGraph]
    exact (A.stage 0).atoms_root [] rfl

/-- An atom allocated to an extension is allocated to the prefix as well. -/
lemma atoms_prefix {s : ℕ} (u x : BitString) (p : BitString)
  (h : p ∈ (A.stage s).atoms (x ++ u)) : p ∈ (A.stage s).atoms x := by
  induction u using List.reverseRecOn generalizing x with
  | nil => simpa using h
  | append_singleton xs b ih =>
    rw [← List.append_assoc] at h
    have h1 := (A.stage s).atoms_child _ _ _ h
    exact ih _ h1

/-- The output set is closed under prefixes. -/
lemma allocationPrefixSet_downward (w : CantorSeq) {x y : BitString}
  (hxy : x <+: y) (hy : y ∈ allocationPrefixSet A w) : x ∈ allocationPrefixSet A w := by
  rcases hy with ⟨p, hpw, hpy⟩
  use p, hpw
  dsimp [allocationLowerGraph] at hpy ⊢
  rcases hxy with ⟨u, rfl⟩
  exact atoms_prefix A _ _ _ hpy

/-- Two incomparable strings diverge at a common prefix, one continuing with each bit. -/
lemma divergence_of_not_prefix {x y : BitString} (h : ¬(x <+: y ∨ y <+: x)) :
    ∃ c b, c ++ [b] <+: x ∧ c ++ [!b] <+: y := by
  induction x generalizing y with
  | nil =>
    have : [] <+: y := ⟨y, rfl⟩
    exact False.elim (h (Or.inl this))
  | cons hx tx ih =>
    rcases y with _|⟨hy, ty⟩
    · have : [] <+: hx :: tx := ⟨hx :: tx, rfl⟩
      exact False.elim (h (Or.inr this))
    · by_cases h_eq : hx = hy
      · subst h_eq
        have h' : ¬(tx <+: ty ∨ ty <+: tx) := by
          intro contra
          rcases contra with ⟨u, rfl⟩ | ⟨u, rfl⟩
          · exact h (Or.inl ⟨u, rfl⟩)
          · exact h (Or.inr ⟨u, rfl⟩)
        rcases ih h' with ⟨c, b, ⟨ux, rfl⟩, ⟨uy, rfl⟩⟩
        exact ⟨hx :: c, b, ⟨ux, rfl⟩, ⟨uy, rfl⟩⟩
      · have : hy = !hx := by cases hx <;> cases hy <;> simp_all
        subst this
        exact ⟨[], hx, ⟨tx, rfl⟩, ⟨ty, rfl⟩⟩

/-- Two strings sharing an allocated atom are comparable. -/
lemma atoms_disjoint_prefix {s : ℕ} {x y : BitString} {p : BitString}
  (hx : p ∈ (A.stage s).atoms x) (hy : p ∈ (A.stage s).atoms y) : x <+: y ∨ y <+: x := by
  by_contra contra
  rcases divergence_of_not_prefix contra with ⟨c, b, ⟨ux, hux⟩, ⟨uy, huy⟩⟩
  have hx2 : p ∈ (A.stage s).atoms (c ++ [b]) := by
    have : c ++ [b] ++ ux = x := hux
    subst this
    exact atoms_prefix A _ _ _ hx
  have hy2 : p ∈ (A.stage s).atoms (c ++ [!b]) := by
    have : c ++ [!b] ++ uy = y := huy
    subst this
    exact atoms_prefix A _ _ _ hy
  cases b
  · have h_disj := (A.stage s).atoms_disjoint c p hx2
    simp only [Bool.not_false] at hy2
    exact h_disj hy2
  · simp only [Bool.not_true] at hy2
    have h_disj := (A.stage s).atoms_disjoint c p hy2
    exact h_disj hx2

/-- A prefix of `q` no longer than `n` is a prefix of the first `n` entries of `q`. -/
lemma isPrefix_take {α} (p q : List α) (hpq : p <+: q) (n : ℕ) (h : p.length ≤ n) :
    p <+: q.take n := by
  rcases hpq with ⟨u, rfl⟩
  have : (p ++ u).take n = p ++ u.take (n - p.length) := by
    rw [List.take_append]
    have : p.take n = p := List.take_of_length_le h
    rw [this]
  rw [this]
  exact List.prefix_append p _

/-- Dropping all but the last entry of a list leaves that entry alone. -/
lemma drop_eq_singleton {α} (L : List α) (n : ℕ) (h : L.length = n + 1) :
  L.drop n = [L[n]'(by omega)] := by
  have hlen : (L.drop n).length = 1 := by
    rw [List.length_drop, h]
    omega
  have H : (L.drop n)[0]'(by omega) = L[n + 0]'(by omega) := by
    rw [List.getElem_drop]
  have H2 : L[n + 0]'(by omega) = L[n]'(by omega) := by rfl
  rw [H2] at H
  apply List.ext_get
  · rw [hlen, List.length_singleton]
  · intro i hi1 hi2
    have : i = 0 := by omega
    subst this
    exact H

/-- Every extension of an allocated atom is itself allocated at the corresponding later stage. -/
lemma atom_extension_mem {s k : ℕ} {x : BitString} {p : BitString}
  (hp : p ∈ (A.stage s).atoms x) {q : BitString} (hpq : p <+: q)
  (hlen : q.length = s + k) : q ∈ (A.stage (s + k)).atoms x := by
  induction k generalizing s p q with
  | zero =>
    have heq : q = p := by
      have h1 : p.length = s := (A.stage s).atoms_length x p hp
      have h2 : q.length = s := hlen
      rcases hpq with ⟨u, rfl⟩
      have : p.length + u.length = s := by
        rw [← List.length_append, h2]
      have : u.length = 0 := by omega
      have : u = [] := List.length_eq_zero_iff.mp this
      subst this
      simp
    subst heq
    exact hp
  | succ k ih =>
    set q' := q.take (s + k)
    have hq'len : q'.length = s + k := by
      rw [List.length_take, hlen]
      exact Nat.min_eq_left (by omega)
    have hplen : p.length = s := (A.stage s).atoms_length x p hp
    have hpq' : p <+: q' := isPrefix_take p q hpq (s + k) (by omega)
    have h1 := ih hp hpq' hq'len
    have H := List.take_append_drop (s + k) q
    have hdrop := drop_eq_singleton q (s + k) hlen
    rw [hdrop] at H
    have hq_eq : q = q' ++ [q[s + k]'(by omega)] := H.symm
    rw [hq_eq]
    have hp_refine : q' ++ [q[s + k]'(by omega)] ∈ refineAtoms ((A.stage (s + k)).atoms x) := by
      rw [refineAtoms_mem]
      exact ⟨q', h1, _, rfl⟩
    exact A.refines (s + k) x _ hp_refine

/-- Two prefixes of the same sequence are comparable. -/
lemma isCantorPrefix_chain (w : CantorSeq) (x y : BitString)
    (hx : IsCantorPrefix x w) (hy : IsCantorPrefix y w) : x <+: y ∨ y <+: x := by
  rcases le_total x.length y.length with hlen | hlen
  · left
    apply isPrefix_of_getElem_eq hlen
    intro i hi
    have h1 := hx i hi
    have h2 := hy i (lt_of_lt_of_le hi hlen)
    rw [← h1, ← h2]
  · right
    apply isPrefix_of_getElem_eq hlen
    intro i hi
    have h1 := hy i hi
    have h2 := hx i (lt_of_lt_of_le hi hlen)
    rw [← h1, ← h2]

/-- The output set on a fixed random sequence is a chain. -/
lemma allocationPrefixSet_chain (w : CantorSeq) {x y : BitString}
  (hx : x ∈ allocationPrefixSet A w) (hy : y ∈ allocationPrefixSet A w) : x <+: y ∨ y <+: x := by
  dsimp [allocationPrefixSet, allocationLowerGraph] at hx hy
  rcases hx with ⟨px, hpw, hpx⟩
  rcases hy with ⟨py, hpyw, hpy⟩
  rcases isCantorPrefix_chain w px py hpw hpyw with hpx_py | hpy_px
  · have h_px_len : px.length = px.length := rfl
    have h_py_len : py.length = px.length + (py.length - px.length) := by
      have h1 : px.length ≤ py.length := by
        rcases hpx_py with ⟨u, rfl⟩
        rw [List.length_append]
        omega
      omega
    have hpx_ext := atom_extension_mem A hpx hpx_py h_py_len
    have hpy' : py ∈ (A.stage (px.length + (py.length - px.length))).atoms y := by
      have h_eq : px.length + (py.length - px.length) = py.length := by omega
      rw [h_eq]
      exact hpy
    exact atoms_disjoint_prefix A hpx_ext hpy'
  · have h_py_len : py.length = py.length := rfl
    have h_px_len : px.length = py.length + (px.length - py.length) := by
      have h1 : py.length ≤ px.length := by
        rcases hpy_px with ⟨u, rfl⟩
        rw [List.length_append]
        omega
      omega
    have hpy_ext := atom_extension_mem A hpy hpy_px h_px_len
    have hpx' : px ∈ (A.stage (py.length + (px.length - py.length))).atoms x := by
      have h_eq : py.length + (px.length - py.length) = px.length := by omega
      rw [h_eq]
      exact hpx
    exact atoms_disjoint_prefix A hpx' hpy_ext

/-- The output set on a fixed random sequence describes a stream. -/
lemma allocationPrefixSet_isStreamPrefixSet (w : CantorSeq) :
  IsStreamPrefixSet (allocationPrefixSet A w) :=
  ⟨allocationPrefixSet_nonempty A w, fun hxy hy => allocationPrefixSet_downward A w hxy hy,
    fun hx hy => allocationPrefixSet_chain A w hx hy⟩

/-- The stream the allocation outputs on the random sequence `w`. -/
noncomputable def allocationGeneratorOutput (w : CantorSeq) : BitStream :=
  BitStream.ofPrefixSet (allocationPrefixSet A w) (allocationPrefixSet_isStreamPrefixSet A w)

/-- The probabilistic generator built from an allocation. -/
noncomputable def allocationGenerator : ProbabilisticGenerator where
  output := allocationGeneratorOutput A
  lowerGraph := allocationLowerGraph A
  lowerGraph_re := allocationLowerGraph_re A
  lowerGraph_sound := by
    intro p y hp w hw
    have hw_pref : IsCantorPrefix p w := hw
    have hy : y ∈ allocationPrefixSet A w := ⟨p, hw_pref, hp⟩
    have H := BitStream.finite_le_ofPrefixSet_iff (allocationPrefixSet_isStreamPrefixSet A w) y
    exact H.mpr hy
  lowerGraph_complete := by
    intro w y hw
    have H := BitStream.finite_le_ofPrefixSet_iff (allocationPrefixSet_isStreamPrefixSet A w) y
    have hy : y ∈ allocationPrefixSet A w := H.mp hw
    exact hy

/-- The random sequences that make the allocation output an extension of `x` by stage `s`. -/
def allocationStageOpen (x : BitString) (s : ℕ) : Set CantorSeq :=
  ⋃ p ∈ (A.stage s).atoms x, cantorCylinder p

/-- The open set of the allocation graph at `x` is the union of its stage sets. -/
lemma cantorOpen_allocation_eq_iUnion (x : BitString) :
  cantorOpen (allocationLowerGraph A) x = ⋃ s, allocationStageOpen A x s := by
  ext w
  simp only [cantorOpen, mem_iUnion, allocationStageOpen, exists_prop]
  constructor
  · rintro ⟨p, hp, hw⟩
    exact ⟨p.length, p, hp, hw⟩
  · rintro ⟨s, p, hp, hw⟩
    have hlen : p.length = s := (A.stage s).atoms_length x p hp
    subst hlen
    exact ⟨p, hp, hw⟩

/-- The measure of the stage set at `x` is the stage numerator of `x`, in units of `2 ^ -s`. -/
lemma uniformMeasure_allocationStage (x : BitString) (s : ℕ) :
  uniformMeasure (allocationStageOpen A x s) = dyadicValue (q s x) s := by
  have H : allocationStageOpen A x s = ⋃ p ∈ ((A.stage s).atoms x).toFinset, cantorCylinder p := by
    ext w
    simp [allocationStageOpen]
  rw [H]
  have H_disj : Set.PairwiseDisjoint (((A.stage s).atoms x).toFinset : Set BitString)
      cantorCylinder := by
    intro p1 hp1 p2 hp2 hneq
    simp only [Finset.mem_coe, List.mem_toFinset] at hp1 hp2
    rw [Function.onFun, Set.disjoint_iff]
    intro w hw
    have hw1 : IsCantorPrefix p1 w := hw.1
    have hw2 : IsCantorPrefix p2 w := hw.2
    have Hlen : p1.length = p2.length := by
      have h1 := (A.stage s).atoms_length x p1 hp1
      have h2 := (A.stage s).atoms_length x p2 hp2
      omega
    have Heq : p1 = p2 := by
      apply List.ext_get Hlen
      intro i hi1 hi2
      have h1 := hw1 i hi1
      have h2 := hw2 i hi2
      have hget1 : List.get p1 ⟨i, hi1⟩ = p1[i] := rfl
      have hget2 : List.get p2 ⟨i, hi2⟩ = p2[i] := rfl
      rw [hget1, hget2, ← h1, ← h2]
    exact hneq Heq
  rw [MeasureTheory.measure_biUnion_finset H_disj]
  · have H2 : (∑ p ∈ ((A.stage s).atoms x).toFinset, uniformMeasure (cantorCylinder p)) =
      ∑ p ∈ ((A.stage s).atoms x).toFinset, (2 : ENNReal)⁻¹ ^ s := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [uniformMeasure_cantorCylinder p]
      have : p.length = s := by
        apply (A.stage s).atoms_length x p
        simp only [List.mem_toFinset] at hp
        exact hp
      rw [this]
    rw [H2]
    rw [Finset.sum_const, nsmul_eq_mul]
    unfold dyadicValue
    have H3 : (((A.stage s).atoms x).toFinset).card = q s x := by
      have h_nodup : ((A.stage s).atoms x).Nodup := (A.stage s).atoms_nodup x
      have h_card : (((A.stage s).atoms x).toFinset).card = ((A.stage s).atoms x).length :=
        List.toFinset_card_of_nodup h_nodup
      rw [h_card]
      exact (A.stage s).atoms_card x
    rw [H3]
    rw [div_eq_mul_inv, ENNReal.inv_pow]
  · intro p hp
    exact measurableSet_cantorCylinder p

/-- Every prefix of a sequence extends to a prefix by one of the two bits. -/
lemma isCantorPrefix_append_cases (p : BitString) (w : CantorSeq)
    (hpw : IsCantorPrefix p w) :
    IsCantorPrefix (p ++ [false]) w ∨ IsCantorPrefix (p ++ [true]) w := by
  cases h : w p.length
  · left
    intro i hi
    have h1 : i < p.length + 1 := by simpa using hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h2 | h2
    · have h3 := hpw i h2
      simp [List.getElem_append_left, h2, h3]
    · subst h2
      simp [h]
  · right
    intro i hi
    have h1 : i < p.length + 1 := by simpa using hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h2 | h2
    · have h3 := hpw i h2
      simp [List.getElem_append_left, h2, h3]
    · subst h2
      simp [h]

/-- The stage sets grow with the stage. -/
lemma allocationStage_mono (x : BitString) : Monotone (allocationStageOpen A x) := by
  apply monotone_nat_of_le_succ
  intro s w hw
  dsimp [allocationStageOpen] at hw ⊢
  simp only [mem_iUnion, exists_prop] at hw ⊢
  rcases hw with ⟨p, hp, hpw⟩
  rcases isCantorPrefix_append_cases p w hpw with h0 | h1
  · use p ++ [false]
    have hp0 : p ++ [false] ∈ refineAtoms ((A.stage s).atoms x) := by
      rw [refineAtoms_mem]
      exact ⟨p, hp, false, rfl⟩
    exact ⟨A.refines s x _ hp0, h0⟩
  · use p ++ [true]
    have hp1 : p ++ [true] ∈ refineAtoms ((A.stage s).atoms x) := by
      rw [refineAtoms_mem]
      exact ⟨p, hp, true, rfl⟩
    exact ⟨A.refines s x _ hp1, h1⟩

/-- The semimeasure generated by the allocation generator is the limit of the stage numerators. -/
lemma generatedTreeSemimeasure_allocation_eq (x : BitString) :
  generatedTreeSemimeasure (allocationGenerator A) x = ⨆ s, dyadicValue (q s x) s := by
  unfold generatedTreeSemimeasure
  have h_eq1 : (allocationGenerator A).output ⁻¹' bitStreamCylinder x =
      cantorOpen (allocationLowerGraph A) x := by
    ext w
    simp only [Set.mem_preimage]
    have h1 : (allocationGenerator A).output w = BitStream.ofPrefixSet (allocationPrefixSet A w)
        (allocationPrefixSet_isStreamPrefixSet A w) := rfl
    have h2 : (allocationGenerator A).output w ∈ bitStreamCylinder x ↔
        .finite x ≤ (allocationGenerator A).output w := Iff.rfl
    have h3 : .finite x ≤ BitStream.ofPrefixSet (allocationPrefixSet A w)
        (allocationPrefixSet_isStreamPrefixSet A w) ↔
        x ∈ allocationPrefixSet A w := BitStream.finite_le_ofPrefixSet_iff _ x
    have h4 : x ∈ allocationPrefixSet A w ↔ w ∈ cantorOpen (allocationLowerGraph A) x := by
      simp only [allocationPrefixSet, cantorOpen, cantorCylinder, mem_setOf_eq, mem_iUnion,
        exists_prop]
      tauto
    rw [h2, h1, h3, h4]
  rw [h_eq1]
  rw [cantorOpen_allocation_eq_iUnion A x]
  have h_mono : Monotone (fun s => allocationStageOpen A x s) := allocationStage_mono A x
  have h_sup_eval := h_mono.measure_iUnion (μ := uniformMeasure)
  have h_dyad : ∀ s, dyadicValue (q s x) s = uniformMeasure (allocationStageOpen A x s) := by
    intro s
    exact (uniformMeasure_allocationStage A x s).symm
  simp_rw [h_dyad]
  exact h_sup_eval

end AllocationGenerator

/-- Every lower semicomputable continuous semimeasure is generated by a probabilistic generator. -/
theorem exists_probabilisticGenerator_generatedTreeSemimeasure_eq
    {a : BitString → ℝ≥0∞} (ha : IsLowerSemicomputableContinuousSemimeasure a) :
    ∃ G : ProbabilisticGenerator, ∀ x, generatedTreeSemimeasure G x = a x := by
  have h1 : a [] = 1 := ha.1.1
  obtain ⟨q, hq⟩ := exists_simpleTreeApproximation ha h1
  obtain ⟨A⟩ := exists_effectiveNestedTreeAllocation hq
  use allocationGenerator A
  intro x
  rw [generatedTreeSemimeasure_allocation_eq A x]
  exact hq.2.2.2.2.1 x

end Kolmogorov
