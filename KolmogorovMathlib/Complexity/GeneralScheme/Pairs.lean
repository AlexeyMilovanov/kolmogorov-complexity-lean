import KolmogorovMathlib.Complexity.GeneralScheme.Decision
import KolmogorovMathlib.Complexity.GeneralScheme.DecisionBasic
import KolmogorovMathlib.AlgorithmicRandomness.Measure
import KolmogorovMathlib.MonotoneComplexity.REClosure

/-!
# Complexities of pairs (SUV Problems 198, 199)

SUV Problem 198 (printed p. 198) asks how to define monotone complexity, a priori probability
and decision complexity for pairs of strings. In each case "define" means: there is an optimal
description mode. A computable continuous map into `Σ × Σ` is a pair of computable continuous
maps into `Σ`, and the complexity of a pair `⟨x, y⟩` is the least length of a description whose
two outputs start with `x` and `y`. A probabilistic machine with two output tapes is a pair of
computable stream maps applied to the same random sequence.
Problem 199 bounds the decision complexity of a pair by `l(x) + l(y) + O(1)`.
-/

open scoped ENNReal

namespace Kolmogorov

namespace GeneralScheme

/-- Decision complexity of a pair with respect to a pair of decision decompressors
(a computable continuous map `ℕ⊥ → Σ × Σ`): the least length of `p` such that `M₁(p)` starts
with `x` and `M₂(p)` starts with `y`. -/
noncomputable def pairKROf (M₁ M₂ : DecisionDecompressor) (x y : BitString) : ℕ∞ :=
  sInf {l : ℕ∞ | ∃ p, M₁.rel p x ∧ M₂.rel p y ∧ l = p.length}

/-- An optimal pair of decision decompressors for pairs. -/
def IsOptimalPairDecision (M₁ M₂ : DecisionDecompressor) : Prop :=
  ∀ N₁ N₂ : DecisionDecompressor, ∃ c : ℕ, ∀ x y, pairKROf M₁ M₂ x y ≤ pairKROf N₁ N₂ x y + c

/-- Monotone complexity of a pair with respect to a pair of stream maps (a continuous map
`Σ → Σ × Σ`): the least length of `p` whose two outputs start with `x` and `y`. -/
noncomputable def pairKMOf (D₁ D₂ : BitStream → BitStream) (x y : BitString) : ℕ∞ :=
  sInf {l : ℕ∞ | ∃ p, monotoneProduces D₁ p x ∧ monotoneProduces D₂ p y ∧ l = p.length}

/-- An optimal pair of monotone decompressors for pairs. -/
def IsOptimalPairMonotone (D₁ D₂ : BitStream → BitStream) : Prop :=
  IsComputableStreamMap D₁ ∧ IsComputableStreamMap D₂ ∧
    ∀ E₁ E₂, IsComputableStreamMap E₁ → IsComputableStreamMap E₂ →
      ∃ c : ℕ, ∀ x y, pairKMOf D₁ D₂ x y ≤ pairKMOf E₁ E₂ x y + c

private lemma exists_isOptimalPairMonotone_sInf_le_sInf_add {S T : Set ℕ∞} {c : ℕ}
    (h : ∀ l ∈ T, ∃ k ∈ S, k ≤ l + (c : ℕ∞)) :
    sInf S ≤ sInf T + (c : ℕ∞) := by
  by_cases hT : T = ∅
  · rw [hT, sInf_empty, top_add]
    exact le_top
  · have hT_nonempty : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hT
    have h_min := csInf_mem hT_nonempty
    rcases h (sInf T) h_min with ⟨k, hk, hk_le⟩
    exact le_trans (sInf_le hk) hk_le

/-- **SUV Problem 198 (a) (Section 6.2, printed p. 198).** Monotone complexity of pairs is well
defined: there is an optimal computable continuous map `Σ → Σ × Σ`.

Proof idea: as for Theorem 84 (`exists_optimalMonotoneDecompressor`). Enumerate pairs of
computable stream maps and prefix the index in self-delimiting form. -/
theorem exists_isOptimalPairMonotone : ∃ D₁ D₂, IsOptimalPairMonotone D₁ D₂ := by
  obtain ⟨U, hU_RE, hU_LG, hU_comp⟩ := exists_universal_computableStreamMap_lowerGraphs
  have hU₁ : IsRE (fun p : ℕ × (BitString × BitString) =>
      U p.1.unpair.1 p.2.1 p.2.2) :=
    IsRE.comp_computable hU_RE
      (g := fun p : ℕ × (BitString × BitString) => (p.1.unpair.1, p.2))
      (Computable.pair (Computable.fst.comp (Computable.unpair.comp Computable.fst))
        Computable.snd)
  have hU₂ : IsRE (fun p : ℕ × (BitString × BitString) =>
      U p.1.unpair.2 p.2.1 p.2.2) :=
    IsRE.comp_computable hU_RE
      (g := fun p : ℕ × (BitString × BitString) => (p.1.unpair.2, p.2))
      (Computable.pair (Computable.snd.comp (Computable.unpair.comp Computable.fst))
        Computable.snd)
  let U₁ : ℕ → BitString → BitString → Prop := fun i => U i.unpair.1
  let U₂ : ℕ → BitString → BitString → Prop := fun i => U i.unpair.2
  have hLG₁ : ∀ i, IsStreamLowerGraph (U₁ i) := fun i => hU_LG _
  have hLG₂ : ∀ i, IsStreamLowerGraph (U₂ i) := fun i => hU_LG _
  let D₁ := streamMapOfLowerGraph (taggedStreamLowerGraph U₁)
    (taggedStreamLowerGraph_isStreamLowerGraph U₁ hLG₁)
  let D₂ := streamMapOfLowerGraph (taggedStreamLowerGraph U₂)
    (taggedStreamLowerGraph_isStreamLowerGraph U₂ hLG₂)
  refine ⟨D₁, D₂, ⟨streamMapOfLowerGraph_isContinuousStreamMap _, ?_⟩,
    ⟨streamMapOfLowerGraph_isContinuousStreamMap _, ?_⟩, ?_⟩
  · refine IsRE.of_iff (taggedStreamLowerGraph_isRE (U := U₁) hU₁) ?_
    intro p
    exact (streamMapOfLowerGraph_finite_spec _ p.1 p.2).symm
  · refine IsRE.of_iff (taggedStreamLowerGraph_isRE (U := U₂) hU₂) ?_
    intro p
    exact (streamMapOfLowerGraph_finite_spec _ p.1 p.2).symm
  · intro E₁ E₂ hE₁ hE₂
    obtain ⟨a, ha⟩ := hU_comp E₁ hE₁
    obtain ⟨b, hb⟩ := hU_comp E₂ hE₂
    refine ⟨(natCode (Nat.pair a b)).length, fun x y => ?_⟩
    unfold pairKMOf
    refine exists_isOptimalPairMonotone_sInf_le_sInf_add ?_
    rintro l ⟨p, hp₁, hp₂, rfl⟩
    refine ⟨(natCode (Nat.pair a b) ++ p).length, ⟨natCode (Nat.pair a b) ++ p, ?_, ?_, rfl⟩, ?_⟩
    · have h1 : U a p x := (ha p x).mpr hp₁
      change BitStream.finite x ≤ D₁ (.finite _)
      rw [streamMapOfLowerGraph_finite_spec]
      exact Or.inr ⟨Nat.pair a b, p, rfl, by simpa [U₁] using h1⟩
    · have h1 : U b p y := (hb p y).mpr hp₂
      change BitStream.finite y ≤ D₂ (.finite _)
      rw [streamMapOfLowerGraph_finite_spec]
      exact Or.inr ⟨Nat.pair a b, p, rfl, by simpa [U₂] using h1⟩
    · rw [List.length_append]
      push_cast
      rw [add_comm]

/-- A priori probability of a pair with respect to a probabilistic machine with two output tapes.
The machine is a pair of stream maps `D₁, D₂` applied to the same random sequence `ω`, and the
value is the uniform measure of the set of `ω` on which the first output starts with `x` and the
second output starts with `y`. -/
noncomputable def pairAPrioriOf (D₁ D₂ : BitStream → BitStream) (x y : BitString) : ℝ≥0∞ :=
  uniformMeasure
    {ω | BitStream.finite x ≤ D₁ (.infinite ω) ∧ BitStream.finite y ≤ D₂ (.infinite ω)}

/-- An optimal probabilistic machine with two output tapes: the a priori probability of pairs it
defines is maximal up to a constant factor. -/
def IsOptimalPairAPriori (D₁ D₂ : BitStream → BitStream) : Prop :=
  IsComputableStreamMap D₁ ∧ IsComputableStreamMap D₂ ∧
    ∀ E₁ E₂, IsComputableStreamMap E₁ → IsComputableStreamMap E₂ →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ x y, c * pairAPrioriOf E₁ E₂ x y ≤ pairAPrioriOf D₁ D₂ x y

/-- The tail of a sequence after dropping `n` bits. -/
private def exists_isOptimalPairAPriori_tail (n : ℕ) (ω : CantorSeq) : CantorSeq :=
  fun k => ω (n + k)

private lemma exists_isOptimalPairAPriori_measurable_tail (n : ℕ) :
    Measurable (exists_isOptimalPairAPriori_tail n) :=
  Measurable.of_eval (fun k => measurable_pi_apply (n + k))

private lemma exists_isOptimalPairAPriori_cyl_inter_tail (a x : BitString) :
    cantorCylinder a ∩ exists_isOptimalPairAPriori_tail a.length ⁻¹' cantorCylinder x =
      cantorCylinder (a ++ x) := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, cantorCylinder, Set.mem_ofPred_eq,
    IsCantorPrefix, exists_isOptimalPairAPriori_tail, List.length_append]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    by_cases hia : i < a.length
    · rw [List.getElem_append_left hia]; exact h1 i hia
    · rw [List.getElem_append_right (by omega)]
      have := h2 (i - a.length) (by omega)
      rw [show a.length + (i - a.length) = i by omega] at this
      exact this
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by omega)
      rwa [List.getElem_append_left hi] at this
    · have := h (a.length + i) (by omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa using this

open MeasureTheory in
private lemma exists_isOptimalPairAPriori_shift (a : BitString) {S : Set CantorSeq}
    (hS : MeasurableSet S) :
    uniformMeasure (cantorCylinder a ∩ exists_isOptimalPairAPriori_tail a.length ⁻¹' S) =
      (2 : ℝ≥0∞)⁻¹ ^ a.length * uniformMeasure S := by
  set ν : Measure CantorSeq := (2 : ℝ≥0∞) ^ a.length •
    (uniformMeasure.restrict (cantorCylinder a)).map (exists_isOptimalPairAPriori_tail a.length)
    with hν
  have hmeas := exists_isOptimalPairAPriori_measurable_tail a.length
  have happly : ∀ T : Set CantorSeq, MeasurableSet T →
      ν T = (2 : ℝ≥0∞) ^ a.length *
        uniformMeasure (cantorCylinder a ∩ exists_isOptimalPairAPriori_tail a.length ⁻¹' T) := by
    intro T hT
    rw [hν, Measure.smul_apply, Measure.map_apply hmeas hT,
      Measure.restrict_apply (hmeas hT), Set.inter_comm, smul_eq_mul]
  have h2 : (2 : ℝ≥0∞) ^ a.length * (2 : ℝ≥0∞)⁻¹ ^ a.length = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have hprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [happly _ MeasurableSet.univ]
    simp only [Set.preimage_univ, Set.inter_univ]
    rw [← cantorMass, cantorMass_uniformMeasure, h2]
  have hmass : ∀ x, cantorMass ν x = cantorMass uniformMeasure x := by
    intro x
    unfold cantorMass
    rw [happly _ (measurableSet_cantorCylinder x),
      exists_isOptimalPairAPriori_cyl_inter_tail, uniformMeasure_cantorCylinder,
      uniformMeasure_cantorCylinder, List.length_append, pow_add, ← mul_assoc, h2, one_mul]
  have heq : ν = uniformMeasure := cantorMeasure_unique ν uniformMeasure hmass
  have := happly S hS
  rw [heq] at this
  rw [this, ← mul_assoc, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ a.length) ((2 : ℝ≥0∞) ^ a.length), h2, one_mul]

/-- **SUV Problem 198 (b) (Section 6.2, printed p. 198).** The a priori probability of pairs is
well defined. Some probabilistic machine with two output tapes, on which bits are printed
sequentially, maximizes the probability that the outputs start with `x` and `y`, up to a
constant factor, among all such machines.

Proof idea: the universal probabilistic machine. It first reads from the random bits a
self-delimiting code `ẑ` of an index `z` (probability `2 ^ (-l(ẑ))`) and then runs the `z`-th pair
of computable stream maps on the remaining bits. The uniform measure is shift-invariant, so the
constant is `2 ^ (-l(ẑ))`. The enumeration of the computable stream maps is the one of
Theorem 84 (`exists_optimalMonotoneDecompressor`). -/
theorem exists_isOptimalPairAPriori : ∃ D₁ D₂, IsOptimalPairAPriori D₁ D₂ := by
  obtain ⟨U, hURE, hULG, hUcomp⟩ := exists_universal_computableStreamMap_lowerGraphs
  have hcomp : ∀ sel : ℕ → ℕ, Computable sel → ∀ D : BitStream → BitStream,
      D = streamMapOfLowerGraph (taggedStreamLowerGraph (fun z => U (sel z)))
        (taggedStreamLowerGraph_isStreamLowerGraph _ (fun z => hULG _)) →
      IsComputableStreamMap D := by
    intro sel hsel D hD
    subst hD
    refine ⟨streamMapOfLowerGraph_isContinuousStreamMap _, ?_⟩
    have hRE : IsRE (fun p : ℕ × (BitString × BitString) => U (sel p.1) p.2.1 p.2.2) :=
      IsRE.comp_computable hURE
        (Computable.pair (hsel.comp Computable.fst) Computable.snd)
    exact IsRE.of_iff (taggedStreamLowerGraph_isRE hRE) (fun p =>
      (streamMapOfLowerGraph_finite_spec _ p.1 p.2).symm)
  have hsel₁ : Computable (fun z : ℕ => (Nat.unpair z).1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp
  have hsel₂ : Computable (fun z : ℕ => (Nat.unpair z).2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp
  refine ⟨streamMapOfLowerGraph (taggedStreamLowerGraph (fun z => U (Nat.unpair z).1))
      (taggedStreamLowerGraph_isStreamLowerGraph _ (fun z => hULG _)),
    streamMapOfLowerGraph (taggedStreamLowerGraph (fun z => U (Nat.unpair z).2))
      (taggedStreamLowerGraph_isStreamLowerGraph _ (fun z => hULG _)),
    hcomp _ hsel₁ _ rfl, hcomp _ hsel₂ _ rfl, ?_⟩
  intro E₁ E₂ hE₁ hE₂
  obtain ⟨i, hi⟩ := hUcomp E₁ hE₁
  obtain ⟨j, hj⟩ := hUcomp E₂ hE₂
  have key : ∀ (E : BitStream → BitStream), IsComputableStreamMap E → ∀ k : ℕ,
      (∀ x y, U k x y ↔ streamLowerGraph E x y) → ∀ x ω,
      BitStream.finite x ≤ E (.infinite ω) ↔ ∃ n, U k (cantorPrefix ω n) x := by
    intro E hE k hk x ω
    rw [continuousStreamMap_finite_le_infinite_iff E hE.1]
    exact exists_congr (fun n => (hk _ _).symm)
  refine ⟨(2 : ℝ≥0∞)⁻¹ ^ (natCode (Nat.pair i j)).length,
    (ENNReal.pow_pos (by norm_num) _).ne', ENNReal.pow_ne_top (by norm_num), ?_⟩
  intro x y
  unfold pairAPrioriOf
  have hmeas : ∀ (k : ℕ) (x : BitString),
      MeasurableSet {ω : CantorSeq | ∃ n, U k (cantorPrefix ω n) x} := by
    intro k x
    have : {ω : CantorSeq | ∃ n, U k (cantorPrefix ω n) x} =
        ⋃ p ∈ {p : BitString | U k p x}, cantorCylinder p := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨_, hn, (isCantorPrefix_iff_cantorPrefix_eq _ ω).2 (by simp)⟩
      · rintro ⟨p, hp, hc⟩
        exact ⟨p.length, by rwa [(isCantorPrefix_iff_cantorPrefix_eq p ω).1 hc]⟩
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) (fun p _ => measurableSet_cantorCylinder p)
  have hSE : MeasurableSet {ω : CantorSeq | BitStream.finite x ≤ E₁ (.infinite ω) ∧
      BitStream.finite y ≤ E₂ (.infinite ω)} := by
    have : {ω : CantorSeq | BitStream.finite x ≤ E₁ (.infinite ω) ∧
        BitStream.finite y ≤ E₂ (.infinite ω)} =
        {ω | ∃ n, U i (cantorPrefix ω n) x} ∩ {ω | ∃ n, U j (cantorPrefix ω n) y} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, key E₁ hE₁ i hi, key E₂ hE₂ j hj]
    rw [this]
    exact (hmeas i x).inter (hmeas j y)
  rw [← exists_isOptimalPairAPriori_shift _ hSE]
  refine MeasureTheory.measure_mono ?_
  rintro ω ⟨hcyl, htail⟩
  have hpre : ∀ n, cantorPrefix ω ((natCode (Nat.pair i j)).length + n) =
      natCode (Nat.pair i j) ++
        cantorPrefix (exists_isOptimalPairAPriori_tail (natCode (Nat.pair i j)).length ω) n := by
    intro n
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      rw [cantorPrefix_getElem]
      by_cases hk : k < (natCode (Nat.pair i j)).length
      · rw [List.getElem_append_left hk]
        exact hcyl k hk
      · rw [List.getElem_append_right (by omega), cantorPrefix_getElem]
        simp only [exists_isOptimalPairAPriori_tail]
        congr 1
        omega
  rcases htail with ⟨h1, h2⟩
  obtain ⟨n₁, hn₁⟩ := (key E₁ hE₁ i hi x _).1 h1
  obtain ⟨n₂, hn₂⟩ := (key E₂ hE₂ j hj y _).1 h2
  refine ⟨?_, ?_⟩
  · rw [streamMapOfLowerGraph_infinite_spec]
    refine ⟨(natCode (Nat.pair i j)).length + n₁, ?_⟩
    rw [hpre]
    exact Or.inr ⟨Nat.pair i j, _, rfl, by simpa [Nat.unpair_pair] using hn₁⟩
  · rw [streamMapOfLowerGraph_infinite_spec]
    refine ⟨(natCode (Nat.pair i j)).length + n₂, ?_⟩
    rw [hpre]
    exact Or.inr ⟨Nat.pair i j, _, rfl, by simpa [Nat.unpair_pair] using hn₂⟩

/-- One step of the token decoder: the state is the pending first bit of a token (if any) and
the output collected so far for the channel `c`. A token is a pair of bits `a b`: the channel
is `a` and the payload is `b`. -/
private def exists_isOptimalPairDecision_projStep (c : Bool) :
    Option Bool × BitString → Bool → Option Bool × BitString
  | (none, acc), b => (some b, acc)
  | (some a, acc), b => (none, if a = c then acc ++ [b] else acc)

/-- The channel `c` of a bit string read as a sequence of two-bit tokens (an incomplete last
token is ignored). -/
private def exists_isOptimalPairDecision_proj (c : Bool) (z : BitString) : BitString :=
  (z.foldl (exists_isOptimalPairDecision_projStep c) (none, [])).2

private lemma exists_isOptimalPairDecision_proj_computable (c : Bool) :
    Computable (exists_isOptimalPairDecision_proj c) := by
  unfold exists_isOptimalPairDecision_proj
  refine Primrec.to_comp ?_
  refine Primrec.snd.comp ?_
  have hstep : Primrec₂ (fun (_ : BitString) (sb : (Option Bool × BitString) × Bool) =>
      exists_isOptimalPairDecision_projStep c sb.1 sb.2) := by
    have hacc : Primrec (fun q : BitString × ((Option Bool × BitString) × Bool) => q.2.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hb : Primrec (fun q : BitString × ((Option Bool × BitString) × Bool) => q.2.2) :=
      Primrec.snd.comp Primrec.snd
    have ho : Primrec (fun q : BitString × ((Option Bool × BitString) × Bool) => q.2.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    refine Primrec.of_eq (f := fun (q : BitString × ((Option Bool × BitString) × Bool)) =>
      (Option.casesOn q.2.1.1 (some q.2.2, q.2.1.2)
        (fun a => (none, bif (a == c) then q.2.1.2 ++ [q.2.2] else q.2.1.2)) :
          Option Bool × BitString)) ?_ ?_
    · refine Primrec.option_casesOn ho (Primrec.pair (Primrec.option_some.comp hb) hacc) ?_
      refine Primrec.pair (Primrec.const none) ?_
      refine Primrec.cond ?_ ?_ (hacc.comp Primrec.fst)
      · exact Primrec.beq.comp Primrec.snd (Primrec.const c)
      · exact Primrec.list_append.comp (hacc.comp Primrec.fst)
          (Primrec.list_cons.comp (hb.comp Primrec.fst) (Primrec.const []))
    · intro q
      obtain ⟨_, ⟨o, acc⟩, b⟩ := q
      cases o <;> simp [exists_isOptimalPairDecision_projStep]
  exact Primrec.list_foldl Primrec.id (Primrec.const (none, [])) hstep

private lemma exists_isOptimalPairDecision_foldl_snd_prefix (c : Bool) :
    ∀ (w : BitString) (s : Option Bool × BitString),
      s.2 <+: (w.foldl (exists_isOptimalPairDecision_projStep c) s).2 := by
  intro w
  induction w with
  | nil => intro s; exact List.prefix_refl _
  | cons b w ih =>
    intro s
    refine List.IsPrefix.trans ?_ (ih _)
    obtain ⟨o, acc⟩ := s
    cases o with
    | none => exact List.prefix_refl _
    | some a =>
      simp only [exists_isOptimalPairDecision_projStep]
      split_ifs
      · exact List.prefix_append _ _
      · exact List.prefix_refl _

private lemma exists_isOptimalPairDecision_proj_mono (c : Bool) {z z' : BitString}
    (h : z <+: z') :
    exists_isOptimalPairDecision_proj c z <+: exists_isOptimalPairDecision_proj c z' := by
  obtain ⟨w, rfl⟩ := h
  unfold exists_isOptimalPairDecision_proj
  rw [List.foldl_append]
  exact exists_isOptimalPairDecision_foldl_snd_prefix c w _

/-- Step 1 of the proof of `exists_isOptimalPairDecision`: from a decision decompressor
`R` read as printing a sequence of two-bit tokens (`a b`: channel `a`, payload bit `b`), obtain a
pair of decision decompressors `M₁, M₂` whose outputs on `p` are the channel `false`, respectively
`true`, of the output of `R` on `p`: `M_i.rel p x ↔ ∃ z, R.rel p z ∧ x <+: proj c z`. -/
private theorem exists_isOptimalPairDecision_split (R : DecisionDecompressor) :
    ∃ M₁ M₂ : DecisionDecompressor,
      (∀ p x, M₁.rel p x ↔ ∃ z, R.rel p z ∧ x <+: exists_isOptimalPairDecision_proj false z) ∧
      (∀ p x, M₂.rel p x ↔ ∃ z, R.rel p z ∧ x <+: exists_isOptimalPairDecision_proj true z) := by
  have key : ∀ c : Bool, ∃ M : DecisionDecompressor,
      ∀ p x, M.rel p x ↔ ∃ z, R.rel p z ∧ x <+: exists_isOptimalPairDecision_proj c z := by
    intro c
    refine ⟨{ rel := fun p x => ∃ z, R.rel p z ∧ x <+: exists_isOptimalPairDecision_proj c z
              re := ?_
              nil_mem := fun p => ⟨[], R.nil_mem p, List.nil_prefix⟩
              prefix_closed := ?_
              regular := ?_ }, fun _ _ => Iff.rfl⟩
    · have hcomp : Computable (fun r : (BitString × BitString) × BitString =>
          decide (r.1.2 = (exists_isOptimalPairDecision_proj c r.2).take r.1.2.length)) := by
        have htake : Computable (fun r : (BitString × BitString) × BitString =>
            (exists_isOptimalPairDecision_proj c r.2).take r.1.2.length) :=
          (Primrec.list_take.to_comp).comp
            (Computable.list_length.comp (Computable.snd.comp Computable.fst))
            ((exists_isOptimalPairDecision_proj_computable c).comp Computable.snd)
        exact (Primrec.eq.decide.to_comp).comp (Computable.snd.comp Computable.fst) htake
      have h1 : IsRE (fun r : (BitString × BitString) × BitString =>
          (decide (r.1.2 = (exists_isOptimalPairDecision_proj c r.2).take r.1.2.length)) = true ∧
            R.rel r.1.1 r.2) :=
        IsRE.and_computable (R := fun r : (BitString × BitString) × BitString =>
          R.rel r.1.1 r.2) (R.re.comp_computable (g := fun r : (BitString × BitString) ×
            BitString => (r.1.1, r.2))
          (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)) hcomp
      refine (IsRE.exists_encodable (R := fun (q : BitString × BitString) (z : BitString) =>
        R.rel q.1 z ∧ q.2 <+: exists_isOptimalPairDecision_proj c z)
        (h1.of_iff fun r => ?_))
      rw [decide_eq_true_iff, List.prefix_iff_eq_take]
      exact and_comm
    · rintro p x x' ⟨z, hz, hx⟩ h
      exact ⟨z, hz, h.trans hx⟩
    · rintro p₁ x₁ p₂ x₂ ⟨z₁, hz₁, hx₁⟩ ⟨z₂, hz₂, hx₂⟩ hp
      have hp' : p₁ = p₂ := hp
      subst hp'
      rcases R.regular hz₁ hz₂ (StrRel.holds_refl _ _) with h | h
      · have hm := exists_isOptimalPairDecision_proj_mono c h
        have hx₁' : x₁ <+: exists_isOptimalPairDecision_proj c z₂ := List.IsPrefix.trans hx₁ hm
        rcases le_total x₁.length x₂.length with hl | hl
        · exact Or.inl (List.prefix_of_prefix_length_le hx₁' hx₂ hl)
        · exact Or.inr (List.prefix_of_prefix_length_le hx₂ hx₁' hl)
      · have hm := exists_isOptimalPairDecision_proj_mono c h
        have hx₂' : x₂ <+: exists_isOptimalPairDecision_proj c z₁ := List.IsPrefix.trans hx₂ hm
        rcases le_total x₁.length x₂.length with hl | hl
        · exact Or.inl (List.prefix_of_prefix_length_le hx₁ hx₂' hl)
        · exact Or.inr (List.prefix_of_prefix_length_le hx₂' hx₁ hl)
  obtain ⟨M₁, h₁⟩ := key false
  obtain ⟨M₂, h₂⟩ := key true
  exact ⟨M₁, M₂, h₁, h₂⟩

/-- Step 2 helper: the string of two-bit tokens `c b₀ c b₁ …` carrying the bits `bs` on the
channel `c`. -/
private def exists_isOptimalPairDecision_merge_tok (c : Bool) (bs : BitString) : BitString :=
  bs.flatMap (fun b => [c, b])

private lemma exists_isOptimalPairDecision_merge_foldl_tok (c c' : Bool)
    (bs acc : BitString) :
    (exists_isOptimalPairDecision_merge_tok c bs).foldl
        (exists_isOptimalPairDecision_projStep c') (none, acc) =
      (none, if c = c' then acc ++ bs else acc) := by
  induction bs generalizing acc with
  | nil => simp [exists_isOptimalPairDecision_merge_tok]
  | cons b bs ih =>
    have : exists_isOptimalPairDecision_merge_tok c (b :: bs) =
        [c, b] ++ exists_isOptimalPairDecision_merge_tok c bs := by
      simp [exists_isOptimalPairDecision_merge_tok]
    rw [this, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, exists_isOptimalPairDecision_projStep]
    by_cases h : c = c'
    · subst h
      simp only [ite_true]
      rw [ih]
      simp
    · simp only [h, ite_false]
      rw [ih]
      simp [h]

/-- Step 2 helper: the token decoder is in the state "no pending bit" after every channel. -/
private def exists_isOptimalPairDecision_merge_Inv (Z : BitString) : Prop :=
  ∀ c', (Z.foldl (exists_isOptimalPairDecision_projStep c') (none, [])).1 = none

private lemma exists_isOptimalPairDecision_merge_inv_append_tok (c : Bool)
    (Z bs : BitString) (hZ : exists_isOptimalPairDecision_merge_Inv Z) :
    exists_isOptimalPairDecision_merge_Inv
        (Z ++ exists_isOptimalPairDecision_merge_tok c bs) ∧
      ∀ c', exists_isOptimalPairDecision_proj c'
          (Z ++ exists_isOptimalPairDecision_merge_tok c bs) =
        if c = c' then exists_isOptimalPairDecision_proj c' Z ++ bs
        else exists_isOptimalPairDecision_proj c' Z := by
  have key : ∀ c', (Z ++ exists_isOptimalPairDecision_merge_tok c bs).foldl
      (exists_isOptimalPairDecision_projStep c') (none, []) =
      (none, if c = c' then exists_isOptimalPairDecision_proj c' Z ++ bs
        else exists_isOptimalPairDecision_proj c' Z) := by
    intro c'
    have h : Z.foldl (exists_isOptimalPairDecision_projStep c') (none, []) =
        (none, exists_isOptimalPairDecision_proj c' Z) := Prod.ext (hZ c') rfl
    rw [List.foldl_append, h, exists_isOptimalPairDecision_merge_foldl_tok]
  refine ⟨fun c' => ?_, fun c' => ?_⟩
  · rw [key c']
  · unfold exists_isOptimalPairDecision_proj
    rw [key c']
    rfl

private lemma exists_isOptimalPairDecision_merge_ext (N : DecisionDecompressor)
    {p u x : BitString} (hu : N.rel p u) (hx : N.rel p x) :
    N.rel p (u ++ x.drop u.length) ∧ x <+: u ++ x.drop u.length := by
  rcases N.regular hu hx (StrRel.holds_refl .eq p) with h | h
  · obtain ⟨w, rfl⟩ := h
    rw [List.drop_left]
    exact ⟨hx, List.prefix_refl _⟩
  · rw [List.drop_eq_nil_of_le h.length_le, List.append_nil]
    exact ⟨hu, h⟩

/-- Step 2 helper: at stage `t` look at the candidate string `x₀` with code `idx t`; if the stage
approximation `chk` confirms it for `p`, append the tokens for the new bits of `x₀` on the
channel `c`. -/
private def exists_isOptimalPairDecision_merge_stepC (c : Bool) (idx : ℕ → ℕ)
    (chk : BitString × BitString → ℕ → Bool) (p : BitString) (t : ℕ) (Z : BitString) :
    BitString :=
  bif chk (p, (Encodable.decode (α := BitString) (idx t)).getD []) t then
    Z ++ exists_isOptimalPairDecision_merge_tok c
      (((Encodable.decode (α := BitString) (idx t)).getD []).drop
        (exists_isOptimalPairDecision_proj c Z).length)
  else Z

private lemma exists_isOptimalPairDecision_merge_stepC_prefix (c : Bool) (idx : ℕ → ℕ)
    (chk : BitString × BitString → ℕ → Bool) (p : BitString) (t : ℕ) (Z : BitString) :
    Z <+: exists_isOptimalPairDecision_merge_stepC c idx chk p t Z := by
  unfold exists_isOptimalPairDecision_merge_stepC
  cases chk (p, (Encodable.decode (α := BitString) (idx t)).getD []) t
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

private lemma exists_isOptimalPairDecision_merge_stepC_spec (N : DecisionDecompressor)
    (c : Bool) (idx : ℕ → ℕ)
    (chk : BitString × BitString → ℕ → Bool) (p : BitString) (t : ℕ) (Z : BitString)
    (hsound : ∀ x s, chk (p, x) s = true → N.rel p x)
    (hZ : exists_isOptimalPairDecision_merge_Inv Z)
    (hN : N.rel p (exists_isOptimalPairDecision_proj c Z)) :
    exists_isOptimalPairDecision_merge_Inv
        (exists_isOptimalPairDecision_merge_stepC c idx chk p t Z) ∧
      N.rel p (exists_isOptimalPairDecision_proj c
        (exists_isOptimalPairDecision_merge_stepC c idx chk p t Z)) ∧
      (∀ c', c' ≠ c → exists_isOptimalPairDecision_proj c'
          (exists_isOptimalPairDecision_merge_stepC c idx chk p t Z) =
        exists_isOptimalPairDecision_proj c' Z) ∧
      (∀ x, (Encodable.decode (α := BitString) (idx t)).getD [] = x → chk (p, x) t = true →
        x <+: exists_isOptimalPairDecision_proj c
          (exists_isOptimalPairDecision_merge_stepC c idx chk p t Z)) := by
  unfold exists_isOptimalPairDecision_merge_stepC
  cases h : chk (p, (Encodable.decode (α := BitString) (idx t)).getD []) t
  · refine ⟨hZ, hN, fun _ _ => rfl, ?_⟩
    intro x hx hc
    rw [← hx, h] at hc
    exact absurd hc (by simp)
  · simp only [Bool.cond_true]
    obtain ⟨hI, hp⟩ := exists_isOptimalPairDecision_merge_inv_append_tok c Z
      (((Encodable.decode (α := BitString) (idx t)).getD []).drop
        (exists_isOptimalPairDecision_proj c Z).length) hZ
    obtain ⟨h1, h2⟩ := exists_isOptimalPairDecision_merge_ext N hN (hsound _ _ h)
    refine ⟨hI, ?_, ?_, ?_⟩
    · rw [hp c, ite_eq_left rfl]; exact h1
    · intro c' hc'
      rw [hp c', ite_eq_right (Ne.symm hc')]
    · intro x hx _
      rw [hp c, ite_eq_left rfl, ← hx]; exact h2

/-- Step 2 helper: one stage of the merged machine. -/
private def exists_isOptimalPairDecision_merge_stepZ
    (chk₁ chk₂ : BitString × BitString → ℕ → Bool) (p : BitString) (t : ℕ)
    (Z : BitString) : BitString :=
  exists_isOptimalPairDecision_merge_stepC true (fun t => t.unpair.2) chk₂ p t
    (exists_isOptimalPairDecision_merge_stepC false (fun t => t.unpair.1) chk₁ p t Z)

/-- Step 2 helper: the stage-`s` string of tokens printed on `p`. -/
private def exists_isOptimalPairDecision_merge_Z
    (chk₁ chk₂ : BitString × BitString → ℕ → Bool) (p : BitString) (s : ℕ) :
    BitString :=
  Nat.rec [] (fun s Z => exists_isOptimalPairDecision_merge_stepZ chk₁ chk₂ p s Z) s

private lemma exists_isOptimalPairDecision_merge_stepZ_prefix
    (chk₁ chk₂ : BitString × BitString → ℕ → Bool) (p : BitString)
    (t : ℕ) (Z : BitString) :
    Z <+: exists_isOptimalPairDecision_merge_stepZ chk₁ chk₂ p t Z :=
  (exists_isOptimalPairDecision_merge_stepC_prefix _ _ _ _ _ _).trans
    (exists_isOptimalPairDecision_merge_stepC_prefix _ _ _ _ _ _)

private lemma exists_isOptimalPairDecision_merge_Z_mono
    (chk₁ chk₂ : BitString × BitString → ℕ → Bool) (p : BitString)
    {s t : ℕ} (h : s ≤ t) :
    exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p s <+:
      exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p t := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
    exact ih.trans (exists_isOptimalPairDecision_merge_stepZ_prefix chk₁ chk₂ p t _)

private lemma exists_isOptimalPairDecision_merge_stepZ_spec (N₁ N₂ : DecisionDecompressor)
    (chk₁ chk₂ : BitString × BitString → ℕ → Bool) (p : BitString) (t : ℕ) (Z : BitString)
    (h₁ : ∀ x s, chk₁ (p, x) s = true → N₁.rel p x)
    (h₂ : ∀ x s, chk₂ (p, x) s = true → N₂.rel p x)
    (hZ : exists_isOptimalPairDecision_merge_Inv Z)
    (hN₁ : N₁.rel p (exists_isOptimalPairDecision_proj false Z))
    (hN₂ : N₂.rel p (exists_isOptimalPairDecision_proj true Z)) :
    exists_isOptimalPairDecision_merge_Inv
        (exists_isOptimalPairDecision_merge_stepZ chk₁ chk₂ p t Z) ∧
      N₁.rel p (exists_isOptimalPairDecision_proj false
        (exists_isOptimalPairDecision_merge_stepZ chk₁ chk₂ p t Z)) ∧
      N₂.rel p (exists_isOptimalPairDecision_proj true
        (exists_isOptimalPairDecision_merge_stepZ chk₁ chk₂ p t Z)) ∧
      (∀ x, x = (Encodable.decode (α := BitString) t.unpair.1).getD [] →
        chk₁ (p, x) t = true →
          x <+: exists_isOptimalPairDecision_proj false
            (exists_isOptimalPairDecision_merge_stepZ chk₁ chk₂ p t Z)) ∧
      (∀ y, y = (Encodable.decode (α := BitString) t.unpair.2).getD [] →
        chk₂ (p, y) t = true →
          y <+: exists_isOptimalPairDecision_proj true
            (exists_isOptimalPairDecision_merge_stepZ chk₁ chk₂ p t Z)) := by
  obtain ⟨hI1, hA1, hB1, hC1⟩ := exists_isOptimalPairDecision_merge_stepC_spec N₁ false
    (fun t => t.unpair.1) chk₁ p t Z h₁ hZ hN₁
  have hN₂' : N₂.rel p (exists_isOptimalPairDecision_proj true
      (exists_isOptimalPairDecision_merge_stepC false (fun t => t.unpair.1) chk₁ p t Z)) := by
    rw [hB1 true (by decide)]; exact hN₂
  obtain ⟨hI2, hA2, hB2, hC2⟩ := exists_isOptimalPairDecision_merge_stepC_spec N₂ true
    (fun t => t.unpair.2) chk₂ p t _ h₂ hI1 hN₂'
  have hpre := exists_isOptimalPairDecision_proj_mono false
    (exists_isOptimalPairDecision_merge_stepC_prefix true (fun t => t.unpair.2) chk₂ p t
      (exists_isOptimalPairDecision_merge_stepC false (fun t => t.unpair.1) chk₁ p t Z))
  have e2 := hB2 false (by decide)
  refine ⟨hI2, ?_, hA2, ?_, fun y hy hc => hC2 y hy.symm hc⟩
  · unfold exists_isOptimalPairDecision_merge_stepZ; rw [e2]; exact hA1
  · intro x hx hc
    unfold exists_isOptimalPairDecision_merge_stepZ
    exact (hC1 x hx.symm hc).trans hpre

private lemma exists_isOptimalPairDecision_merge_Z_inv (N₁ N₂ : DecisionDecompressor)
    (chk₁ chk₂ : BitString × BitString → ℕ → Bool) (p : BitString)
    (h₁ : ∀ x s, chk₁ (p, x) s = true → N₁.rel p x)
    (h₂ : ∀ x s, chk₂ (p, x) s = true → N₂.rel p x) (s : ℕ) :
    exists_isOptimalPairDecision_merge_Inv
        (exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p s) ∧
      N₁.rel p (exists_isOptimalPairDecision_proj false
        (exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p s)) ∧
      N₂.rel p (exists_isOptimalPairDecision_proj true
        (exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p s)) := by
  induction s with
  | zero => exact ⟨fun _ => rfl, N₁.nil_mem p, N₂.nil_mem p⟩
  | succ s ih =>
    obtain ⟨a, b, c⟩ := ih
    obtain ⟨a', b', c', -⟩ :=
      exists_isOptimalPairDecision_merge_stepZ_spec N₁ N₂ chk₁ chk₂ p s _ h₁ h₂ a b c
    exact ⟨a', b', c'⟩

private lemma exists_isOptimalPairDecision_merge_Z_complete (N₁ N₂ : DecisionDecompressor)
    (chk₁ chk₂ : BitString × BitString → ℕ → Bool) (p x y : BitString)
    (h₁ : ∀ x s, chk₁ (p, x) s = true → N₁.rel p x)
    (h₂ : ∀ x s, chk₂ (p, x) s = true → N₂.rel p x)
    (e₁ : ∀ x, N₁.rel p x → ∃ s, chk₁ (p, x) s = true)
    (e₂ : ∀ x, N₂.rel p x → ∃ s, chk₂ (p, x) s = true)
    (m₁ : ∀ a s t, s ≤ t → chk₁ a s = true → chk₁ a t = true)
    (m₂ : ∀ a s t, s ≤ t → chk₂ a s = true → chk₂ a t = true)
    (hx : N₁.rel p x) (hy : N₂.rel p y) :
    ∃ s, x <+: exists_isOptimalPairDecision_proj false
        (exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p s) ∧
      y <+: exists_isOptimalPairDecision_proj true
        (exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p s) := by
  obtain ⟨s₁, hs₁⟩ := e₁ x hx
  obtain ⟨s₂, hs₂⟩ := e₂ y hy
  set t₁ := Nat.pair (Encodable.encode x) s₁ with ht₁
  set t₂ := Nat.pair s₂ (Encodable.encode y) with ht₂
  have hc₁ : chk₁ (p, x) t₁ = true := m₁ _ _ _ (Nat.right_le_pair _ _) hs₁
  have hc₂ : chk₂ (p, y) t₂ = true := m₂ _ _ _ (Nat.left_le_pair _ _) hs₂
  have hd₁ : x = (Encodable.decode (α := BitString) t₁.unpair.1).getD [] := by
    simp [ht₁]
  have hd₂ : y = (Encodable.decode (α := BitString) t₂.unpair.2).getD [] := by
    simp [ht₂]
  obtain ⟨a₁, b₁, c₁⟩ := exists_isOptimalPairDecision_merge_Z_inv N₁ N₂ chk₁ chk₂ p h₁ h₂ t₁
  obtain ⟨a₂, b₂, c₂⟩ := exists_isOptimalPairDecision_merge_Z_inv N₁ N₂ chk₁ chk₂ p h₁ h₂ t₂
  obtain ⟨-, -, -, hX, -⟩ :=
    exists_isOptimalPairDecision_merge_stepZ_spec N₁ N₂ chk₁ chk₂ p t₁ _ h₁ h₂ a₁ b₁ c₁
  obtain ⟨-, -, -, -, hY⟩ :=
    exists_isOptimalPairDecision_merge_stepZ_spec N₁ N₂ chk₁ chk₂ p t₂ _ h₁ h₂ a₂ b₂ c₂
  have hX' : x <+: exists_isOptimalPairDecision_proj false
      (exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p (t₁ + 1)) := hX x hd₁ hc₁
  have hY' : y <+: exists_isOptimalPairDecision_proj true
      (exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p (t₂ + 1)) := hY y hd₂ hc₂
  refine ⟨max (t₁ + 1) (t₂ + 1), ?_, ?_⟩
  · exact hX'.trans (exists_isOptimalPairDecision_proj_mono false
      (exists_isOptimalPairDecision_merge_Z_mono chk₁ chk₂ p (le_max_left _ _)))
  · exact hY'.trans (exists_isOptimalPairDecision_proj_mono true
      (exists_isOptimalPairDecision_merge_Z_mono chk₁ chk₂ p (le_max_right _ _)))

private lemma exists_isOptimalPairDecision_merge_tok_computable (c : Bool) :
    Computable (exists_isOptimalPairDecision_merge_tok c) := by
  unfold exists_isOptimalPairDecision_merge_tok
  refine Primrec.to_comp ?_
  exact Primrec.list_flatMap Primrec.id
    (Primrec.list_cons.comp (Primrec.const c)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

private lemma exists_isOptimalPairDecision_merge_stepC_computable (c : Bool)
    (idx : ℕ → ℕ)
    (chk : BitString × BitString → ℕ → Bool) (hidx : Computable idx)
    (hchk : Computable₂ chk) :
    Computable (fun w : (BitString × ℕ) × BitString =>
      exists_isOptimalPairDecision_merge_stepC c idx chk w.1.1 w.1.2 w.2) := by
  have hp : Computable (fun w : (BitString × ℕ) × BitString => w.1.1) :=
    Computable.fst.comp Computable.fst
  have ht : Computable (fun w : (BitString × ℕ) × BitString => w.1.2) :=
    Computable.snd.comp Computable.fst
  have hZ : Computable (fun w : (BitString × ℕ) × BitString => w.2) := Computable.snd
  have hx : Computable (fun w : (BitString × ℕ) × BitString =>
      (Encodable.decode (α := BitString) (idx w.1.2)).getD []) :=
    Computable.option_getD (Computable.decode.comp (hidx.comp ht)) (Computable.const [])
  have hc : Computable (fun w : (BitString × ℕ) × BitString =>
      chk (w.1.1, (Encodable.decode (α := BitString) (idx w.1.2)).getD []) w.1.2) :=
    hchk.comp (Computable.pair hp hx) ht
  have happ : Computable (fun w : (BitString × ℕ) × BitString =>
      w.2 ++ exists_isOptimalPairDecision_merge_tok c
        (((Encodable.decode (α := BitString) (idx w.1.2)).getD []).drop
          (exists_isOptimalPairDecision_proj c w.2).length)) :=
    Computable.list_append.comp hZ
      ((exists_isOptimalPairDecision_merge_tok_computable c).comp
        ((Primrec.list_drop.to_comp).comp
          (Computable.list_length.comp
            ((exists_isOptimalPairDecision_proj_computable c).comp hZ))
          hx))
  exact Computable.cond hc happ hZ

private lemma exists_isOptimalPairDecision_merge_Z_computable
    (chk₁ chk₂ : BitString × BitString → ℕ → Bool)
    (h₁ : Computable₂ chk₁) (h₂ : Computable₂ chk₂) :
    Computable (fun q : BitString × ℕ =>
      exists_isOptimalPairDecision_merge_Z chk₁ chk₂ q.1 q.2) := by
  have hidx1 : Computable (fun t : ℕ => t.unpair.1) :=
    Computable.fst.comp Computable.unpair
  have hidx2 : Computable (fun t : ℕ => t.unpair.2) :=
    Computable.snd.comp Computable.unpair
  have hstep : Computable₂ (fun (q : BitString × ℕ) (u : ℕ × BitString) =>
      exists_isOptimalPairDecision_merge_stepZ chk₁ chk₂ q.1 u.1 u.2) := by
    have hq : Computable (fun r : (BitString × ℕ) × (ℕ × BitString) => r.1.1) :=
      Computable.fst.comp Computable.fst
    have ht : Computable (fun r : (BitString × ℕ) × (ℕ × BitString) => r.2.1) :=
      Computable.fst.comp Computable.snd
    have hu : Computable (fun r : (BitString × ℕ) × (ℕ × BitString) => r.2.2) :=
      Computable.snd.comp Computable.snd
    have hg : Computable (fun r : (BitString × ℕ) × (ℕ × BitString) => ((r.1.1, r.2.1), r.2.2)) :=
      Computable.pair (Computable.pair hq ht) hu
    have hA := (exists_isOptimalPairDecision_merge_stepC_computable false
        (fun t : ℕ => t.unpair.1) chk₁ hidx1 h₁).comp hg
    have hg' := Computable.pair (Computable.pair hq ht) hA
    have hB := (exists_isOptimalPairDecision_merge_stepC_computable true
      (fun t : ℕ => t.unpair.2) chk₂ hidx2 h₂).comp hg'
    change Computable (fun r : (BitString × ℕ) × (ℕ × BitString) =>
      exists_isOptimalPairDecision_merge_stepZ chk₁ chk₂ r.1.1 r.2.1 r.2.2)
    exact hB.of_eq (fun r => rfl)
  exact Computable.nat_rec Computable.snd (Computable.const []) hstep

/-- Step 2 of the proof of `exists_isOptimalPairDecision`: for every pair of decision
decompressors `N₁, N₂` there is a decision decompressor `S` printing a sequence of two-bit tokens
(channel bit, payload bit; see `exists_isOptimalPairDecision_proj`) such that whenever
`N₁.rel p x` and `N₂.rel p y`, some string `z` printed by `S` on `p` has channel `false` starting
with `x` and channel `true` starting with `y`. (Run both machines in stages; at stage `s` print
the tokens for the bits of the longest outputs of `N₁`, `N₂` on `p` found within `s` steps. This
output depends only on `p`, so the printed strings are pairwise compatible.) -/
private theorem exists_isOptimalPairDecision_merge (N₁ N₂ : DecisionDecompressor) :
    ∃ S : DecisionDecompressor, ∀ p x y, N₁.rel p x → N₂.rel p y →
      ∃ z, S.rel p z ∧ x <+: exists_isOptimalPairDecision_proj false z ∧
        y <+: exists_isOptimalPairDecision_proj true z := by
  obtain ⟨chk₁, hc₁, hm₁, hi₁⟩ := N₁.re.exists_stageApprox
  obtain ⟨chk₂, hc₂, hm₂, hi₂⟩ := N₂.re.exists_stageApprox
  have hs₁ : ∀ p x s, chk₁ (p, x) s = true → N₁.rel p x :=
    fun p x s h => (hi₁ (p, x)).2 ⟨s, h⟩
  have hs₂ : ∀ p x s, chk₂ (p, x) s = true → N₂.rel p x :=
    fun p x s h => (hi₂ (p, x)).2 ⟨s, h⟩
  have hZc := exists_isOptimalPairDecision_merge_Z_computable chk₁ chk₂ hc₁ hc₂
  refine ⟨{ rel := fun p z => ∃ s, z <+: exists_isOptimalPairDecision_merge_Z chk₁ chk₂ p s
            re := ?_
            nil_mem := fun p => ⟨0, List.nil_prefix⟩
            prefix_closed := fun p z z' ⟨s, h⟩ h' => ⟨s, h'.trans h⟩
            regular := ?_ }, ?_⟩
  · have hcomp : Computable (fun r : (BitString × BitString) × ℕ =>
        decide (r.1.2 = (exists_isOptimalPairDecision_merge_Z chk₁ chk₂ r.1.1 r.2).take
          r.1.2.length)) := by
      have htake : Computable (fun r : (BitString × BitString) × ℕ =>
          (exists_isOptimalPairDecision_merge_Z chk₁ chk₂ r.1.1 r.2).take
            r.1.2.length) :=
        (Primrec.list_take.to_comp).comp
          (Computable.list_length.comp (Computable.snd.comp Computable.fst))
          (hZc.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd))
      exact (Primrec.eq.decide.to_comp).comp (Computable.snd.comp Computable.fst) htake
    exact IsRE.exists_encodable (R := fun (q : BitString × BitString) (s : ℕ) =>
      q.2 <+: exists_isOptimalPairDecision_merge_Z chk₁ chk₂ q.1 s)
      (isRE_of_computable_bool _ _ (fun r => by
        rw [decide_eq_true_iff, List.prefix_iff_eq_take]) hcomp)
  · rintro p₁ z₁ p₂ z₂ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ hp
    have hp' : p₁ = p₂ := hp
    subst hp'
    rcases le_total s₁ s₂ with h | h
    · have h₁' := h₁.trans (exists_isOptimalPairDecision_merge_Z_mono chk₁ chk₂ p₁ h)
      rcases le_total z₁.length z₂.length with hl | hl
      · exact Or.inl (List.prefix_of_prefix_length_le h₁' h₂ hl)
      · exact Or.inr (List.prefix_of_prefix_length_le h₂ h₁' hl)
    · have h₂' := h₂.trans (exists_isOptimalPairDecision_merge_Z_mono chk₁ chk₂ p₁ h)
      rcases le_total z₁.length z₂.length with hl | hl
      · exact Or.inl (List.prefix_of_prefix_length_le h₁ h₂' hl)
      · exact Or.inr (List.prefix_of_prefix_length_le h₂' h₁ hl)
  · intro p x y hx hy
    obtain ⟨s, hxs, hys⟩ := exists_isOptimalPairDecision_merge_Z_complete N₁ N₂ chk₁ chk₂
      p x y (fun x s h => hs₁ p x s h) (fun x s h => hs₂ p x s h)
      (fun x hx => (hi₁ (p, x)).1 hx) (fun x hx => (hi₂ (p, x)).1 hx)
      (fun a s t hst h => hm₁ a s t hst h) (fun a s t hst h => hm₂ a s t hst h) hx hy
    exact ⟨_, ⟨s, List.prefix_refl _⟩, hxs, hys⟩

/-- **SUV Problem 198 (c) (Section 6.2, printed p. 198).** Decision complexity of pairs is well
defined: there is an optimal computable continuous map `ℕ⊥ → Σ × Σ`.

Proof idea: as for Problem 192 (`exists_optimal_decisionDecompressor`), with pairs. -/
theorem exists_isOptimalPairDecision : ∃ M₁ M₂, IsOptimalPairDecision M₁ M₂ := by
  obtain ⟨R, hR⟩ := exists_optimal_decisionDecompressor
  obtain ⟨M₁, M₂, h₁, h₂⟩ := exists_isOptimalPairDecision_split R
  refine ⟨M₁, M₂, fun N₁ N₂ => ?_⟩
  obtain ⟨S, hS⟩ := exists_isOptimalPairDecision_merge N₁ N₂
  obtain ⟨c, hc⟩ := hR S
  refine ⟨c, fun x y => ?_⟩
  by_cases htop : pairKROf N₁ N₂ x y = ⊤
  · rw [htop]; simp
  have hne : {l : ℕ∞ | ∃ p, N₁.rel p x ∧ N₂.rel p y ∧ l = p.length}.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    exact htop (by unfold pairKROf; rw [hempty]; exact sInf_empty)
  obtain ⟨p, hp1, hp2, hpl⟩ : ∃ p, N₁.rel p x ∧ N₂.rel p y ∧ pairKROf N₁ N₂ x y = p.length := by
    obtain ⟨l, hl, hmin⟩ := (wellFounded_lt (α := ℕ∞)).has_min _ hne
    obtain ⟨p, hp1, hp2, rfl⟩ := hl
    refine ⟨p, hp1, hp2, le_antisymm (sInf_le ⟨p, hp1, hp2, rfl⟩) (le_sInf fun l' hl' => ?_)⟩
    exact not_lt.mp (hmin l' hl')
  obtain ⟨z, hSz, hxz, hyz⟩ := hS p x y hp1 hp2
  have h3 : KROf R z ≤ p.length + c :=
    (hc z).trans (by
      gcongr
      exact modeComplexity_le_length hSz)
  have hne' : {l : ℕ∞ | ∃ q, R.rel q z ∧ l = q.length}.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have : KROf R z = ⊤ := by unfold KROf modeComplexity; rw [hempty]; exact sInf_empty
    rw [this] at h3
    simp at h3
  obtain ⟨q, hq, hql⟩ : ∃ q, R.rel q z ∧ KROf R z = q.length := by
    obtain ⟨l, hl, hmin⟩ := (wellFounded_lt (α := ℕ∞)).has_min _ hne'
    obtain ⟨q, hq, rfl⟩ := hl
    refine ⟨q, hq, le_antisymm (sInf_le ⟨q, hq, rfl⟩) (le_sInf fun l' hl' => ?_)⟩
    exact not_lt.mp (hmin l' hl')
  calc pairKROf M₁ M₂ x y ≤ q.length :=
        sInf_le ⟨q, (h₁ q x).2 ⟨z, hq, hxz⟩, (h₂ q y).2 ⟨z, hq, hyz⟩, rfl⟩
    _ = KROf R z := hql.symm
    _ ≤ p.length + c := h3
    _ = pairKROf N₁ N₂ x y + c := by rw [hpl]

/-- The decompressor printing the string `f p` on input `p`, for a computable `f`. -/
private def exists_const_pairKROf_le_length_add_length_mk (f : BitString → BitString)
    (hf : Computable f) : DecisionDecompressor where
  rel p x := x <+: f p
  re := by
    refine isRE_of_computable_bool _
      (fun q : BitString × BitString => decide ((f q.1).take q.2.length = q.2)) ?_ ?_
    · intro q
      rw [decide_eq_true_iff, List.prefix_iff_eq_take]
      exact eq_comm
    · have htake : Computable (fun q : BitString × BitString => (f q.1).take q.2.length) :=
        (Primrec.list_take.to_comp).comp
          (Computable.list_length.comp Computable.snd) (hf.comp Computable.fst)
      exact (Primrec.eq.decide.to_comp).comp htake Computable.snd
  nil_mem p := List.nil_prefix
  prefix_closed _ _ _ h h' := h'.trans h
  regular := by
    intro p₁ x₁ p₂ x₂ h₁ h₂ hp
    simp only [StrRel.Holds] at hp ⊢
    subst hp
    rcases le_total x₁.length x₂.length with h | h
    · exact Or.inl (List.prefix_of_prefix_length_le h₁ h₂ h)
    · exact Or.inr (List.prefix_of_prefix_length_le h₂ h₁ h)

/-- **SUV Problem 199 (Section 6.2, printed p. 198).** The decision complexity of a pair
`⟨x, y⟩` is at most `l(x) + l(y) + O(1)`.

Proof idea (book's hint): the string `z` describes the pair `⟨z, z^R⟩`, where `z^R` is `z`
reversed. Take `z = x ++ y.reverse`. -/
theorem exists_const_pairKROf_le_length_add_length {M₁ M₂ : DecisionDecompressor}
    (hM : IsOptimalPairDecision M₁ M₂) :
    ∃ c : ℕ, ∀ x y, pairKROf M₁ M₂ x y ≤ x.length + y.length + c := by
  obtain ⟨c, hc⟩ := hM
    (exists_const_pairKROf_le_length_add_length_mk id Computable.id)
    (exists_const_pairKROf_le_length_add_length_mk List.reverse Primrec.list_reverse.to_comp)
  refine ⟨c, fun x y => (hc x y).trans ?_⟩
  gcongr
  unfold pairKROf
  have hmem : ((x ++ y.reverse).length : ℕ∞) ∈
      {l : ℕ∞ | ∃ p, (exists_const_pairKROf_le_length_add_length_mk id Computable.id).rel p x ∧
        (exists_const_pairKROf_le_length_add_length_mk List.reverse
          Primrec.list_reverse.to_comp).rel p y ∧ l = p.length} := by
    refine ⟨x ++ y.reverse, ?_, ?_, rfl⟩
    · exact List.prefix_append _ _
    · change y <+: (x ++ y.reverse).reverse
      simp
  refine (sInf_le hmem).trans ?_
  simp

end GeneralScheme

end Kolmogorov
