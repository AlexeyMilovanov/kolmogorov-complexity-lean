import KolmogorovMathlib.Complexity.GeneralScheme.Decision
import KolmogorovMathlib.AlgorithmicRandomness.Measure
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.CylinderMass

/-!
# Enumeration complexity and enumeration a priori probability (SUV Section 6.4.2)

SUV printed pp. 208–209 discuss Solovay's enumeration problems. `KE(S)` is the least length of an
input on which a fixed optimal enumeration algorithm enumerates exactly `S`. `m(S)` is the
probability that an optimal probabilistic enumeration algorithm enumerates exactly `S`.
Problem 209 is the theorem of de Leeuw, Moore, Shannon and Shapiro: `m(S) > 0` iff `S` is
enumerable.

An enumeration algorithm with input is an enumerable relation `rel p k` ("on input `p`, `k` is
printed"). A probabilistic one is an enumerable relation `rel u k` ("after reading the random
bits `u`, `k` has been printed") that is monotone in `u`. Its output on the random sequence `ω`
is `{k | ∃ n, rel (ω ↾ n) k}`, and probabilities refer to the uniform measure.

The quantitative comparisons of `KE` and `-log m` on printed p. 209 are cited (Solovay,
Vereshchagin) or open, and are not stated.
-/

open scoped ENNReal

namespace Kolmogorov

namespace GeneralScheme

/-- An enumeration algorithm with input: on input `p` it enumerates `{k | rel p k}`. -/
structure EnumDecompressor where
  /-- `rel p k`: on input `p` the algorithm prints `k`. -/
  rel : BitString → ℕ → Prop
  /-- The algorithm is effective: the relation is enumerable. -/
  re : IsRE (fun q : BitString × ℕ => rel q.1 q.2)

/-- `KE_E(S)`: the least length of an input on which `E` enumerates exactly `S` (`⊤` if there is
none). -/
noncomputable def KEOf (E : EnumDecompressor) (S : Set ℕ) : ℕ∞ :=
  sInf {l : ℕ∞ | ∃ p, {k | E.rel p k} = S ∧ l = p.length}

/-- An optimal enumeration algorithm: `KE` minimal up to an additive constant. -/
def EnumDecompressor.IsOptimal (E : EnumDecompressor) : Prop :=
  ∀ E' : EnumDecompressor, ∃ c : ℕ, ∀ S, KEOf E S ≤ KEOf E' S + c

/-- A probabilistic enumeration algorithm. -/
structure ProbEnumerator where
  /-- `rel u k`: after reading the random bits `u`, the algorithm has printed `k`. -/
  rel : BitString → ℕ → Prop
  /-- The algorithm is effective. -/
  re : IsRE (fun q : BitString × ℕ => rel q.1 q.2)
  /-- Printed elements stay printed when more random bits are read. -/
  mono : ∀ ⦃u v k⦄, rel u k → u <+: v → rel v k

/-- The set enumerated by `W` on the random sequence `ω`. -/
def ProbEnumerator.output (W : ProbEnumerator) (ω : CantorSeq) : Set ℕ :=
  {k | ∃ n, W.rel (cantorPrefix ω n) k}

/-- `m_W(S)`: the probability that `W` enumerates exactly `S`. -/
noncomputable def ProbEnumerator.prob (W : ProbEnumerator) (S : Set ℕ) : ℝ≥0∞ :=
  uniformMeasure {ω | W.output ω = S}

/-- An optimal probabilistic enumeration algorithm: `m` maximal up to a constant factor. -/
def ProbEnumerator.IsOptimal (W : ProbEnumerator) : Prop :=
  ∀ W' : ProbEnumerator, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ S, c * W'.prob S ≤ W.prob S

/-- **SUV Section 6.4.2 (printed p. 208), unnumbered.** An optimal enumeration algorithm
exists.

Proof idea: the universal construction. Let `E(ẑ p)` enumerate what the `z`-th enumerable
relation enumerates on input `p`, with `ẑ` a self-delimiting code of `z`. Then
`KE_E(S) ≤ KE_{E_z}(S) + l(ẑ)`. -/
theorem exists_optimal_enumDecompressor : ∃ E : EnumDecompressor, E.IsOptimal := by
  classical
  -- the universal enumerable relation
  let U : ℕ × (BitString × ℕ) → Prop := fun a =>
    (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code a.1) (Encodable.encode a.2)).Dom
  have hU : IsRE U := by
    refine ⟨fun a => (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code a.1)
      (Encodable.encode a.2)).map (fun _ => ()), ?_, fun a => by simp [U]⟩
    have h1 : Partrec (fun a : ℕ × (BitString × ℕ) =>
        Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code a.1) (Encodable.encode a.2)) :=
      Nat.Partrec.Code.eval_part.comp
        ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst)
        (Computable.encode.comp Computable.snd)
    exact h1.map (Computable.const ()).to₂
  -- splitting an input into the unary code of `z` and the program
  have hsplit : Computable (fun q : BitString × ℕ =>
      ((q.1.takeWhile id).length, ((q.1.dropWhile id).tail, q.2))) := by
    have h1 : Primrec (fun q : BitString × ℕ => (q.1.takeWhile id).length) :=
      Primrec.list_length.comp
        ((Primrec.list_takeWhile (p := id) Primrec.id).comp Primrec.fst)
    have h2 : Primrec (fun q : BitString × ℕ => (q.1.dropWhile id).tail) :=
      Primrec.list_tail.comp
        ((Primrec.list_dropWhile (p := id) Primrec.id).comp Primrec.fst)
    exact (h1.pair (h2.pair Primrec.snd)).to_comp
  let E : EnumDecompressor :=
    { rel := fun q k => U ((q.takeWhile id).length, ((q.dropWhile id).tail, k))
      re := hU.comp_computable (g := fun q : BitString × ℕ =>
        ((q.1.takeWhile id).length, ((q.1.dropWhile id).tail, q.2))) hsplit }
  have hcode : ∀ (z : ℕ) (p : BitString) (k : ℕ),
      E.rel (List.replicate z true ++ false :: p) k ↔ U (z, (p, k)) := by
    intro z p k
    have h1 : (List.replicate z true ++ false :: p).takeWhile id = List.replicate z true := by
      induction z with
      | zero => simp
      | succ n _ => simp [List.replicate_succ]
    have h2 : (List.replicate z true ++ false :: p).dropWhile id = false :: p := by
      induction z with
      | zero => simp
      | succ n _ => simp [List.replicate_succ]
    simp [E, h1, h2]
  refine ⟨E, fun E' => ?_⟩
  obtain ⟨g, hg, hgdom⟩ := E'.re
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  refine ⟨Encodable.encode c + 1, fun S => ?_⟩
  have hdom : ∀ p k, U (Encodable.encode c, (p, k)) ↔ E'.rel p k := by
    intro p k
    have : (c.eval (Encodable.encode (p, k))).Dom ↔ (g (p, k)).Dom := by
      rw [hc]; simp
    simpa [U, Denumerable.ofNat_encode, hgdom (p, k)] using this
  by_cases htop : KEOf E' S = ⊤
  · simp [htop]
  have hne : {l : ℕ∞ | ∃ p, {k | E'.rel p k} = S ∧ l = p.length}.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    exact htop (by simp [KEOf, hempty])
  obtain ⟨p, hp, hlen⟩ := csInf_mem hne
  have hle : KEOf E S ≤ ((List.replicate (Encodable.encode c) true ++ false :: p).length : ℕ∞) := by
    refine sInf_le ⟨_, ?_, rfl⟩
    rw [← hp]
    ext k
    simp only [Set.mem_ofPred_eq]
    rw [hcode, hdom]
  have hKE : KEOf E' S = (p.length : ℕ∞) := hlen
  rw [hKE]
  refine hle.trans (le_of_eq ?_)
  simp only [List.length_append, List.length_replicate, List.length_cons]
  push_cast
  ring

/-- **SUV Section 6.4.2 (printed p. 208), unnumbered.** `KE(S)` is finite iff `S` is
enumerable.

Proof idea: `→` — `S = {k | E.rel p k}` is a section of an enumerable relation. `←` — the
algorithm that ignores its input and enumerates `S` gives `KE_{E'}(S) = 0`, and optimality
gives `KE_E(S) ≤ c`. -/
theorem KEOf_ne_top_iff {E : EnumDecompressor} (hE : E.IsOptimal) (S : Set ℕ) :
    KEOf E S ≠ ⊤ ↔ IsEnumerableSet S := by
  constructor
  · intro h
    have hne : {l : ℕ∞ | ∃ p, {k | E.rel p k} = S ∧ l = p.length}.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      exact h (by simp [KEOf, hempty])
    obtain ⟨l, p, hp, -⟩ := hne
    have hre : IsRE (fun k : ℕ => E.rel p k) :=
      E.re.comp_computable (g := fun k : ℕ => (p, k))
        (Computable.pair (Computable.const p) Computable.id)
    rw [← hp]
    exact hre
  · intro hS
    let E' : EnumDecompressor :=
      { rel := fun _ k => k ∈ S
        re := IsRE.comp_computable (g := fun q : BitString × ℕ => q.2) hS Computable.snd }
    obtain ⟨c, hc⟩ := hE E'
    have h0 : KEOf E' S ≤ 0 := by
      refine sInf_le ⟨[], ?_, by simp⟩
      ext k; rfl
    have : KEOf E S ≤ (c : ℕ∞) := by
      calc KEOf E S ≤ KEOf E' S + c := hc S
        _ ≤ 0 + c := by gcongr
        _ = c := zero_add _
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top c) this

/-- Universal enumeration of recursively enumerable predicates on any `Primcodable` type. -/
private lemma exists_optimal_probEnumerator_universal {α : Type*} [Primcodable α] :
    ∃ V : ℕ → α → Prop, IsRE (fun p : ℕ × α => V p.1 p.2) ∧
      ∀ R : α → Prop, IsRE R → ∃ i, ∀ a, V i a ↔ R a := by
  refine ⟨fun i a => ∃ k, (Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode i)
    (Encodable.encode a)).isSome, ?_, ?_⟩
  · have hcomp : Computable (fun p : (ℕ × α) × ℕ =>
        (Nat.Partrec.Code.evaln p.2 (Nat.Partrec.Code.ofNatCode p.1.1)
          (Encodable.encode p.1.2)).isSome) := by
      let f : (ℕ × Nat.Partrec.Code) × ℕ → Option ℕ :=
        fun p => Nat.Partrec.Code.evaln p.1.1 p.1.2 p.2
      have h_f : Computable f := Primrec.to_comp Nat.Partrec.Code.primrec_evaln
      have h_g : Computable (fun p : (ℕ × α) × ℕ =>
          ((p.2, Denumerable.ofNat Nat.Partrec.Code p.1.1), Encodable.encode p.1.2)) :=
        Computable.pair (Computable.pair Computable.snd
          ((Computable.ofNat Nat.Partrec.Code).comp (Computable.fst.comp Computable.fst)))
          (Computable.encode.comp (Computable.snd.comp Computable.fst))
      have h := (Primrec.to_comp Primrec.option_isSome).comp (h_f.comp h_g)
      exact Computable.of_eq h (fun p => by
        simp only [f]
        rw [Nat.Partrec.Code.ofNatCode_eq])
    have hre : IsRE (fun p : (ℕ × α) × ℕ =>
        (Nat.Partrec.Code.evaln p.2 (Nat.Partrec.Code.ofNatCode p.1.1)
          (Encodable.encode p.1.2)).isSome = true) := by
      have h := IsRE.and_computable (IsRE_true (α := (ℕ × α) × ℕ)) hcomp
      exact IsRE.of_iff h (fun p => by simp)
    exact IsRE.exists_encodable
      (R := fun (a : ℕ × α) (k : ℕ) => (Nat.Partrec.Code.evaln k
        (Nat.Partrec.Code.ofNatCode a.1) (Encodable.encode a.2)).isSome = true) hre
  · intro R hR
    obtain ⟨f, hf_partrec, hf_dom⟩ := hR
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf_partrec
    refine ⟨Encodable.encode c, fun a => ?_⟩
    have heq : Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c := by
      rw [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.ofNat_encode]
    change (∃ k, (Nat.Partrec.Code.evaln k
      (Nat.Partrec.Code.ofNatCode (Encodable.encode c)) (Encodable.encode a)).isSome) ↔ R a
    rw [heq, ← hf_dom a]
    exact (partrecCodeDom f c hc a).symm

/-- The probabilistic enumerator built from a uniform family `V`: after reading `natCode i`
followed by `p` and some more bits, it prints `k` whenever `V i (p, k)`. -/
private def exists_optimal_probEnumerator_rel (V : ℕ → BitString × ℕ → Prop)
    (u : BitString) (k : ℕ) : Prop :=
  ∃ x : ℕ × BitString × BitString, u = natCode x.1 ++ x.2.1 ++ x.2.2 ∧ V x.1 (x.2.1, k)

private lemma exists_optimal_probEnumerator_rel_re (V : ℕ → BitString × ℕ → Prop)
    (hV : IsRE (fun p : ℕ × (BitString × ℕ) => V p.1 p.2)) :
    IsRE (fun q : BitString × ℕ => exists_optimal_probEnumerator_rel V q.1 q.2) := by
  have h_pred : Computable (fun p : (BitString × ℕ) × (ℕ × BitString × BitString) =>
      decide (p.1.1 = natCode p.2.1 ++ p.2.2.1 ++ p.2.2.2)) := by
    apply Primrec.to_comp
    have h_primrec_pred : PrimrecPred
        (fun p : (BitString × ℕ) × (ℕ × BitString × BitString) =>
          p.1.1 = natCode p.2.1 ++ p.2.2.1 ++ p.2.2.2) :=
      (Primrec.eq (α := BitString)).comp
        (Primrec.fst.comp (Primrec.fst (α := BitString × ℕ) (β := ℕ × BitString × BitString)))
        (Primrec.list_append.comp
          (Primrec.list_append.comp
            (primrec_natCode.comp (Primrec.fst.comp
              (Primrec.snd (α := BitString × ℕ) (β := ℕ × BitString × BitString))))
            (Primrec.fst.comp (Primrec.snd.comp
              (Primrec.snd (α := BitString × ℕ) (β := ℕ × BitString × BitString)))))
          (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd (α := BitString × ℕ) (β := ℕ × BitString × BitString)))))
    rcases h_primrec_pred with ⟨_, hp⟩
    exact hp.of_eq (by intro p; congr)
  have h_V_comp : Computable (fun p : (BitString × ℕ) × (ℕ × BitString × BitString) =>
      (p.2.1, (p.2.2.1, p.1.2))) :=
    Computable.pair (Computable.fst.comp Computable.snd)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.snd))
        (Computable.snd.comp Computable.fst))
  have h1 := hV.comp_computable h_V_comp
  have h2 := IsRE.and_computable h1 h_pred
  have h3 := IsRE.exists_encodable
    (R := fun (q : BitString × ℕ) (x : ℕ × BitString × BitString) =>
      decide (q.1 = natCode x.1 ++ x.2.1 ++ x.2.2) = true ∧ V x.1 (x.2.1, q.2)) h2
  refine IsRE.of_iff h3 (fun q => ?_)
  unfold exists_optimal_probEnumerator_rel
  simp only [decide_eq_true_eq]

private lemma exists_optimal_probEnumerator_rel_mono (V : ℕ → BitString × ℕ → Prop)
    {u v : BitString} {k : ℕ} (h : exists_optimal_probEnumerator_rel V u k) (huv : u <+: v) :
    exists_optimal_probEnumerator_rel V v k := by
  obtain ⟨x, hx, hV⟩ := h
  obtain ⟨t, rfl⟩ := huv
  exact ⟨(x.1, x.2.1, x.2.2 ++ t), by rw [hx]; simp, hV⟩

/-- The tail of a sequence after dropping `n` bits. -/
private def exists_optimal_probEnumerator_tail (n : ℕ) (ω : CantorSeq) : CantorSeq :=
  fun k => ω (n + k)

private lemma exists_optimal_probEnumerator_measurable_tail (n : ℕ) :
    Measurable (exists_optimal_probEnumerator_tail n) :=
  Measurable.of_eval (fun k => measurable_pi_apply (n + k))

private lemma exists_optimal_probEnumerator_cyl_inter_tail (a x : BitString) :
    cantorCylinder a ∩ exists_optimal_probEnumerator_tail a.length ⁻¹' cantorCylinder x =
      cantorCylinder (a ++ x) := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, cantorCylinder, Set.mem_ofPred_eq,
    IsCantorPrefix, exists_optimal_probEnumerator_tail, List.length_append]
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
private lemma exists_optimal_probEnumerator_shift (a : BitString) {S : Set CantorSeq}
    (hS : MeasurableSet S) :
    uniformMeasure (cantorCylinder a ∩ exists_optimal_probEnumerator_tail a.length ⁻¹' S) =
      (2 : ℝ≥0∞)⁻¹ ^ a.length * uniformMeasure S := by
  set ν : Measure CantorSeq := (2 : ℝ≥0∞) ^ a.length •
    (uniformMeasure.restrict (cantorCylinder a)).map (exists_optimal_probEnumerator_tail a.length)
    with hν
  have hmeas := exists_optimal_probEnumerator_measurable_tail a.length
  have happly : ∀ T : Set CantorSeq, MeasurableSet T →
      ν T = (2 : ℝ≥0∞) ^ a.length *
        uniformMeasure (cantorCylinder a ∩ exists_optimal_probEnumerator_tail a.length ⁻¹' T) := by
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
      exists_optimal_probEnumerator_cyl_inter_tail, uniformMeasure_cantorCylinder,
      uniformMeasure_cantorCylinder, List.length_append, pow_add, ← mul_assoc, h2, one_mul]
  have heq : ν = uniformMeasure := cantorMeasure_unique ν uniformMeasure hmass
  have := happly S hS
  rw [heq] at this
  rw [this, ← mul_assoc, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ a.length) ((2 : ℝ≥0∞) ^ a.length), h2, one_mul]

private lemma exists_optimal_probEnumerator_measurable_output (W : ProbEnumerator) (S : Set ℕ) :
    MeasurableSet {ω : CantorSeq | W.output ω = S} := by
  have hk : ∀ k : ℕ, MeasurableSet {ω : CantorSeq | ∃ n, W.rel (cantorPrefix ω n) k} := by
    intro k
    have : {ω : CantorSeq | ∃ n, W.rel (cantorPrefix ω n) k} =
        ⋃ p ∈ {p : BitString | W.rel p k}, cantorCylinder p := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨_, hn, (isCantorPrefix_iff_cantorPrefix_eq _ ω).2 (by simp)⟩
      · rintro ⟨p, hp, hc⟩
        exact ⟨p.length, by rwa [(isCantorPrefix_iff_cantorPrefix_eq p ω).1 hc]⟩
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) (fun p _ => measurableSet_cantorCylinder p)
  have : {ω : CantorSeq | W.output ω = S} =
      ⋂ k : ℕ, {ω : CantorSeq | (∃ n, W.rel (cantorPrefix ω n) k) ↔ k ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.ext_iff, ProbEnumerator.output]
  rw [this]
  refine MeasurableSet.iInter fun k => ?_
  by_cases hkS : k ∈ S
  · have e : {ω : CantorSeq | (∃ n, W.rel (cantorPrefix ω n) k) ↔ k ∈ S} =
        {ω : CantorSeq | ∃ n, W.rel (cantorPrefix ω n) k} := by
      ext ω; simp [hkS]
    rw [e]; exact hk k
  · have e : {ω : CantorSeq | (∃ n, W.rel (cantorPrefix ω n) k) ↔ k ∈ S} =
        {ω : CantorSeq | ∃ n, W.rel (cantorPrefix ω n) k}ᶜ := by
      ext ω; simp [hkS]
    rw [e]; exact (hk k).compl

/-- **SUV Section 6.4.2 (printed p. 209), unnumbered.** An optimal probabilistic enumeration
algorithm exists.

Proof idea: choose the index `z` of a probabilistic algorithm with probability `2 ^ (-2 l(z) - 2)`
from the random bits (self-delimiting code), then run algorithm `z` on the remaining bits. -/
theorem exists_optimal_probEnumerator : ∃ W : ProbEnumerator, W.IsOptimal := by
  obtain ⟨V, hVre, hVcomp⟩ := exists_optimal_probEnumerator_universal (α := BitString × ℕ)
  refine ⟨⟨exists_optimal_probEnumerator_rel V, exists_optimal_probEnumerator_rel_re V hVre,
    fun u v k h huv => exists_optimal_probEnumerator_rel_mono V h huv⟩, ?_⟩
  intro W'
  obtain ⟨i, hi⟩ := hVcomp (fun q : BitString × ℕ => W'.rel q.1 q.2) W'.re
  refine ⟨(2 : ℝ≥0∞)⁻¹ ^ (natCode i).length, (ENNReal.pow_pos (by norm_num) _), fun S => ?_⟩
  unfold ProbEnumerator.prob
  rw [← exists_optimal_probEnumerator_shift _
    (exists_optimal_probEnumerator_measurable_output W' S)]
  refine MeasureTheory.measure_mono ?_
  rintro ω ⟨hcyl, htail⟩
  have hpre : ∀ n, cantorPrefix ω ((natCode i).length + n) =
      natCode i ++ cantorPrefix (exists_optimal_probEnumerator_tail (natCode i).length ω) n := by
    intro n
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      rw [cantorPrefix_getElem]
      by_cases hk : k < (natCode i).length
      · rw [List.getElem_append_left hk]
        exact hcyl k hk
      · rw [List.getElem_append_right (by omega), cantorPrefix_getElem]
        simp only [exists_optimal_probEnumerator_tail]
        congr 1
        omega
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at htail ⊢
  rw [← htail]
  ext k
  simp only [ProbEnumerator.output, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, x, hx, hV⟩
    have hpfx : IsCantorPrefix (natCode x.1) ω := by
      rw [isCantorPrefix_iff_cantorPrefix_eq]
      have h1 : natCode x.1 <+: cantorPrefix ω n := by
        rw [hx, List.append_assoc]; exact List.prefix_append _ _
      obtain ⟨t, ht⟩ := h1
      have hlen : (natCode x.1).length ≤ n := by
        have := congrArg List.length ht
        simp only [cantorPrefix_length, List.length_append] at this; omega
      rw [← cantorPrefix_take ω _ n hlen, ← ht]
      simp
    have hi' : cantorPrefix ω (natCode i).length = natCode i :=
      (isCantorPrefix_iff_cantorPrefix_eq _ ω).1 hcyl
    have hj' : cantorPrefix ω (natCode x.1).length = natCode x.1 :=
      (isCantorPrefix_iff_cantorPrefix_eq _ ω).1 hpfx
    have hxi : x.1 = i := by
      rcases le_total (natCode i).length (natCode x.1).length with hle | hle
      · have := cantorPrefix_mono ω hle
        rw [hi', hj'] at this
        exact (natCode_prefix_iff.1 this).symm
      · have := cantorPrefix_mono ω hle
        rw [hi', hj'] at this
        exact natCode_prefix_iff.1 this
    obtain ⟨x1, x2, x3⟩ := x
    simp only at hxi hx hV
    subst hxi
    have hlen : (natCode x1).length ≤ n := by
      have := congrArg List.length hx
      simp only [cantorPrefix_length, List.length_append] at this; omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlen
    have hh := hpre m
    rw [hx, List.append_assoc] at hh
    have hh2 := List.append_cancel_left hh
    refine ⟨m, ?_⟩
    have := (hi (x2, k)).1 hV
    refine W'.mono this ?_
    rw [← hh2]
    exact List.prefix_append _ _
  · rintro ⟨n, hn⟩
    refine ⟨(natCode i).length + n, (i, cantorPrefix (exists_optimal_probEnumerator_tail
      (natCode i).length ω) n, []), ?_, (hi _).2 hn⟩
    rw [hpre]
    simp

/-- The set of sequences whose length-`m` prefix satisfies `p` is the union of the cylinders of
the length-`m` strings satisfying `p`. -/
private lemma isEnumerableSet_of_prob_pos_aux0 (p : BitString → Bool) (m : ℕ) :
    {ω : CantorSeq | p (cantorPrefix ω m) = true} =
      ⋃ v ∈ ((exactLengthPrograms m).filter p).toFinset, cantorCylinder v := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, List.mem_toFinset, List.mem_filter, exists_prop]
  constructor
  · intro h
    refine ⟨cantorPrefix ω m, ⟨?_, h⟩, ?_⟩
    · have := mem_exactLengthPrograms_self (cantorPrefix ω m)
      simpa using this
    · exact (isCantorPrefix_iff_cantorPrefix_eq _ ω).2 (by simp)
  · rintro ⟨v, ⟨hv, hp⟩, hc⟩
    have hlen := exactLengthPrograms_length_eq m v hv
    have := (isCantorPrefix_iff_cantorPrefix_eq _ ω).1 hc
    rw [hlen] at this
    rw [this]
    simpa using hp

private lemma isEnumerableSet_of_prob_pos_measurableSet (p : BitString → Bool) (m : ℕ) :
    MeasurableSet {ω : CantorSeq | p (cantorPrefix ω m) = true} := by
  rw [isEnumerableSet_of_prob_pos_aux0]
  exact Finset.measurableSet_biUnion _ fun v _ => measurableSet_cantorCylinder v

/-- Step 1: measure of a prefix-determined event. -/
private lemma isEnumerableSet_of_prob_pos_blockMeasure (p : BitString → Bool) (m : ℕ) :
    uniformMeasure {ω : CantorSeq | p (cantorPrefix ω m) = true} =
      (((exactLengthPrograms m).filter p).length : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m := by
  rw [isEnumerableSet_of_prob_pos_aux0, MeasureTheory.measure_biUnion_finset]
  · have hlen : ∀ v ∈ ((exactLengthPrograms m).filter p).toFinset,
        uniformMeasure (cantorCylinder v) = (2 : ℝ≥0∞)⁻¹ ^ m := by
      intro v hv
      rw [uniformMeasure_cantorCylinder,
        exactLengthPrograms_length_eq m v (List.mem_filter.1 (List.mem_toFinset.1 hv)).1]
    rw [Finset.sum_congr rfl hlen, Finset.sum_const, nsmul_eq_mul,
      List.toFinset_card_of_nodup ((exactLengthPrograms_nodup m).filter p)]
  · intro v hv v' hv' hne
    have h1 := exactLengthPrograms_length_eq m v (List.mem_filter.1 (List.mem_toFinset.1 hv)).1
    have h2 := exactLengthPrograms_length_eq m v' (List.mem_filter.1 (List.mem_toFinset.1 hv')).1
    refine cantorCylinder_disjoint_of_incompatible (fun hp => hne ?_) (fun hp => hne ?_)
    · exact List.IsPrefix.eq_of_length hp (h1.trans h2.symm)
    · exact (List.IsPrefix.eq_of_length hp (h2.trans h1.symm)).symm
  · exact fun v _ => measurableSet_cantorCylinder v

/-- Step 2: density. -/
private lemma isEnumerableSet_of_prob_pos_density {A : Set CantorSeq}
    (hA : MeasurableSet A) (h : 0 < uniformMeasure A) :
    ∃ u : BitString,
      uniformMeasure (cantorCylinder u) < 2 * uniformMeasure (A ∩ cantorCylinder u) := by
  classical
  have hfin : uniformMeasure A ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have hlt : uniformMeasure A < 2 * uniformMeasure A := by
    rw [two_mul]; exact ENNReal.lt_add_right hfin h.ne'
  obtain ⟨U, hAU, hUo, hUlt⟩ := Set.exists_isOpen_lt_of_lt A (2 * uniformMeasure A) hlt
  let C : Set BitString := {u | cantorCylinder u ⊆ U}
  let M : Set BitString := {u | u ∈ C ∧ ∀ j < u.length, u.take j ∉ C}
  have hdisj : M.PairwiseDisjoint cantorCylinder := by
    intro u hu u' hu' hne
    have key : ∀ u u' : BitString, u ∈ M → u' ∈ M → u ≠ u' → ¬ u <+: u' := by
      intro u u' hu hu' hne hp
      have hlen : u.length < u'.length := by
        rcases Nat.lt_or_ge u.length u'.length with h1 | h1
        · exact h1
        · exact absurd (List.IsPrefix.eq_of_length hp (le_antisymm hp.length_le h1)) hne
      apply hu'.2 u.length hlen
      rw [← List.prefix_iff_eq_take.1 hp]
      exact hu.1
    exact cantorCylinder_disjoint_of_incompatible (key u u' hu hu' hne)
      (key u' u hu' hu (Ne.symm hne))
  have hcover : U = ⋃ u ∈ M, cantorCylinder u := by
    apply Set.Subset.antisymm
    · intro ω hω
      obtain ⟨_, ⟨x, rfl⟩, hωx, hxU⟩ :=
        isTopologicalBasis_cantorCylinders.exists_subset_of_mem_open hω hUo
      have hex : ∃ n, cantorPrefix ω n ∈ C := by
        refine ⟨x.length, ?_⟩
        have := (isCantorPrefix_iff_cantorPrefix_eq x ω).1 hωx
        change cantorCylinder _ ⊆ U
        rw [this]; exact hxU
      refine Set.mem_iUnion₂.2 ⟨cantorPrefix ω (Nat.find hex), ⟨Nat.find_spec hex, ?_⟩, ?_⟩
      · intro j hj hjC
        rw [cantorPrefix_length] at hj
        rw [cantorPrefix_take ω j _ hj.le] at hjC
        exact Nat.find_min hex hj hjC
      · exact (isCantorPrefix_iff_cantorPrefix_eq _ ω).2 (by simp)
    · intro ω hω
      obtain ⟨u, hu, hωu⟩ := Set.mem_iUnion₂.1 hω
      exact hu.1 hωu
  by_contra hcon
  push Not at hcon
  have hμU : uniformMeasure U = ∑' u : M, uniformMeasure (cantorCylinder u) := by
    conv_lhs => rw [hcover]
    exact MeasureTheory.measure_biUnion (Set.to_countable _) hdisj
      (fun u _ => measurableSet_cantorCylinder u)
  have hμA : uniformMeasure A = ∑' u : M, uniformMeasure (A ∩ cantorCylinder u) := by
    have : A = ⋃ u ∈ M, A ∩ cantorCylinder u := by
      ext ω
      simp only [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
      constructor
      · intro hω
        obtain ⟨u, hu, hωu⟩ := Set.mem_iUnion₂.1 (hcover ▸ hAU hω : ω ∈ ⋃ u ∈ M, cantorCylinder u)
        exact ⟨u, hu, hω, hωu⟩
      · rintro ⟨u, _, hω, _⟩; exact hω
    conv_lhs => rw [this]
    exact MeasureTheory.measure_biUnion (Set.to_countable _)
      (fun u hu u' hu' hne => (hdisj hu hu' hne).mono Set.inter_subset_right
        Set.inter_subset_right)
      (fun u _ => hA.inter (measurableSet_cantorCylinder u))
  have : 2 * uniformMeasure A ≤ uniformMeasure U := by
    rw [hμU, hμA, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun u => hcon u
  exact absurd hUlt (not_lt.2 this)

/-- The prefix-determined predicate used for the stage approximation. -/
private def isEnumerableSet_of_prob_pos_pred (chk : BitString × ℕ → ℕ → Bool)
    (u : BitString) (k m : ℕ) (v : BitString) : Bool :=
  decide (u <+: v) && (List.range (m + 1)).any (fun n => chk (v.take n, k) m)

/-- The enumerable condition. -/
private def isEnumerableSet_of_prob_pos_cond (chk : BitString × ℕ → ℕ → Bool)
    (u : BitString) (k : ℕ) : Prop :=
  ∃ m : ℕ, 2 ^ m < (((exactLengthPrograms m).filter
      (isEnumerableSet_of_prob_pos_pred chk u k m)).length) * 2 ^ (u.length + 1)

/-- Step 3: the condition is RE. -/
private lemma isEnumerableSet_of_prob_pos_re (chk : BitString × ℕ → ℕ → Bool)
    (hchk : Computable₂ chk) (u : BitString) :
    IsRE (fun k : ℕ => isEnumerableSet_of_prob_pos_cond chk u k) := by
  classical
  have hex : Computable (fun q : ℕ × ℕ => exactLengthPrograms q.2) :=
    primrec_exactLengthPrograms.to_comp.comp Computable.snd
  have hpre : Computable₂ (fun (_ : ℕ × ℕ) (v : BitString) => decide (u <+: v)) := by
    have h : Computable (fun v : BitString => decide (v.take u.length = u)) :=
      (primrec_decideEq.comp (Primrec.list_take.comp (Primrec.const u.length) Primrec.id)
        (Primrec.const u)).to_comp
    refine (h.comp Computable.snd).to₂.of_eq ?_
    intro a
    simp [List.prefix_iff_eq_take, eq_comm]
  have hany : Computable₂ (fun (q : ℕ × ℕ) (v : BitString) =>
      (List.range (q.2 + 1)).any (fun n => chk (v.take n, q.1) q.2)) := by
    have hrange : Computable (fun a : (ℕ × ℕ) × BitString => List.range (a.1.2 + 1)) :=
      (Primrec.list_range.to_comp.comp
        (Primrec.succ.to_comp.comp (Computable.snd.comp Computable.fst)))
    have hp : Computable₂ (fun (a : (ℕ × ℕ) × BitString) (n : ℕ) =>
        chk (a.2.take n, a.1.1) a.1.2) := by
      have htake : Computable (fun x : ((ℕ × ℕ) × BitString) × ℕ => x.1.2.take x.2) :=
        (Primrec.list_take.to_comp.comp Computable.snd (Computable.snd.comp Computable.fst))
      have harg : Computable (fun x : ((ℕ × ℕ) × BitString) × ℕ =>
          ((x.1.2.take x.2, x.1.1.1), x.1.1.2)) :=
        Computable.pair
          (Computable.pair htake (Computable.fst.comp (Computable.fst.comp Computable.fst)))
          (Computable.snd.comp (Computable.fst.comp Computable.fst))
      have h := Computable.comp (f := fun p : (BitString × ℕ) × ℕ => chk p.1 p.2) hchk harg
      exact h
    exact computable_list_any (f := fun a : (ℕ × ℕ) × BitString => List.range (a.1.2 + 1))
      (p := fun (a : (ℕ × ℕ) × BitString) (n : ℕ) => chk (a.2.take n, a.1.1) a.1.2) hrange hp
  have hpred : Computable₂ (fun (q : ℕ × ℕ) (v : BitString) =>
      isEnumerableSet_of_prob_pos_pred chk u q.1 q.2 v) := by
    refine (Primrec.and.to_comp.comp hpre hany).of_eq (fun p => ?_)
    simp [isEnumerableSet_of_prob_pos_pred]
  have hfilt := computable_list_filter hex hpred
  have hlen := Computable.list_length.comp hfilt
  have hmul := Primrec.nat_mul.to_comp.comp hlen (Computable.const (2 ^ (u.length + 1)))
  obtain ⟨_, hltp⟩ := (Primrec.nat_lt : PrimrecRel (fun a b : ℕ => a < b))
  have hlt := hltp.to_comp.comp (Computable.pair (Computable.list_length.comp hex) hmul)
  have hRE := isRE_of_computable_bool
    (fun p : ℕ × ℕ => 2 ^ p.2 < (((exactLengthPrograms p.2).filter
      (isEnumerableSet_of_prob_pos_pred chk u p.1 p.2)).length) * 2 ^ (u.length + 1))
    (fun q : ℕ × ℕ => decide ((exactLengthPrograms q.2).length <
      (((exactLengthPrograms q.2).filter
        (isEnumerableSet_of_prob_pos_pred chk u q.1 q.2)).length) * 2 ^ (u.length + 1)))
    (fun a => by simp [length_exactLengthPrograms])
    (hlt.of_eq (fun q => by simp))
  exact IsRE.exists_encodable
    (R := fun (k m : ℕ) => 2 ^ m < (((exactLengthPrograms m).filter
      (isEnumerableSet_of_prob_pos_pred chk u k m)).length) * 2 ^ (u.length + 1)) hRE

private lemma isEnumerableSet_of_prob_pos_arith (c m l : ℕ) :
    2 ^ m < c * 2 ^ (l + 1) ↔
      (2 : ℝ≥0∞)⁻¹ ^ l < 2 * ((c : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hpos : (0 : ℝ≥0∞) < 2 ^ (l + 1) * 2 ^ m := ENNReal.mul_pos (by positivity) (by positivity)
  have hfin : (2 : ℝ≥0∞) ^ (l + 1) * 2 ^ m ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top h2t) (ENNReal.pow_ne_top h2t)
  have e1 : (2 : ℝ≥0∞)⁻¹ ^ l * (2 ^ (l + 1) * 2 ^ m) = 2 * 2 ^ m := by
    have : (2 : ℝ≥0∞)⁻¹ ^ l * 2 ^ l = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel h2 h2t, one_pow]
    calc (2 : ℝ≥0∞)⁻¹ ^ l * (2 ^ (l + 1) * 2 ^ m)
        = ((2 : ℝ≥0∞)⁻¹ ^ l * 2 ^ l) * 2 * 2 ^ m := by ring
      _ = 2 * 2 ^ m := by rw [this]; ring
  have e2 : 2 * ((c : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m) * (2 ^ (l + 1) * 2 ^ m) =
      2 * (c * 2 ^ (l + 1)) := by
    have : (2 : ℝ≥0∞)⁻¹ ^ m * 2 ^ m = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel h2 h2t, one_pow]
    calc 2 * ((c : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m) * (2 ^ (l + 1) * 2 ^ m)
        = 2 * (c * 2 ^ (l + 1)) * ((2 : ℝ≥0∞)⁻¹ ^ m * 2 ^ m) := by ring
      _ = 2 * (c * 2 ^ (l + 1)) := by rw [this]; ring
  have hcancel : ∀ (a x y : ℝ≥0∞), a ≠ 0 → a ≠ ⊤ → (a * x < a * y ↔ x < y) := by
    intro a x y h0 hT
    constructor
    · intro h
      by_contra hn
      exact absurd h (not_lt.2 (mul_le_mul_right (not_lt.1 hn) a))
    · intro h
      exact ENNReal.mul_lt_mul_right h0 hT h
  have hc : (2 ^ m < c * 2 ^ (l + 1)) ↔ ((2 : ℝ≥0∞) ^ m < c * 2 ^ (l + 1)) := by
    rw [← Nat.cast_lt (α := ℝ≥0∞)]; push_cast; rfl
  rw [hc]
  have step := hcancel (2 ^ (l + 1) * 2 ^ m) ((2 : ℝ≥0∞)⁻¹ ^ l)
    (2 * ((c : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m)) hpos.ne' hfin
  rw [mul_comm _ ((2 : ℝ≥0∞)⁻¹ ^ l), e1,
    mul_comm _ (2 * ((c : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m)), e2, hcancel _ _ _ h2 h2t] at step
  exact step

/-- Membership in the stage-`m` event. -/
private lemma isEnumerableSet_of_prob_pos_mem_F (chk : BitString × ℕ → ℕ → Bool)
    (u : BitString) (k m : ℕ) (ω : CantorSeq) :
    ω ∈ {ω : CantorSeq | isEnumerableSet_of_prob_pos_pred chk u k m (cantorPrefix ω m) = true} ↔
      u <+: cantorPrefix ω m ∧ ∃ n, n ≤ m ∧ chk (cantorPrefix ω n, k) m = true := by
  simp only [Set.mem_ofPred_eq, isEnumerableSet_of_prob_pos_pred, Bool.and_eq_true,
    decide_eq_true_eq, List.any_eq_true, List.mem_range, Nat.lt_succ_iff]
  refine and_congr_right fun _ => exists_congr fun n => and_congr_right fun hn => ?_
  rw [cantorPrefix_take ω n m hn]

/-- A string `u` is a prefix of the length-`m` prefix of `ω` iff `ω` extends `u` and `u` is
short enough. -/
private lemma isEnumerableSet_of_prob_pos_pre (u : BitString) (m : ℕ) (ω : CantorSeq) :
    u <+: cantorPrefix ω m ↔ ω ∈ cantorCylinder u ∧ u.length ≤ m := by
  constructor
  · intro h
    have hl : u.length ≤ m := by simpa using h.length_le
    refine ⟨(isCantorPrefix_iff_cantorPrefix_eq u ω).2 ?_, hl⟩
    rw [List.prefix_iff_eq_take] at h
    rw [← cantorPrefix_take ω u.length m hl, ← h]
  · rintro ⟨hc, hl⟩
    have := (isCantorPrefix_iff_cantorPrefix_eq u ω).1 hc
    rw [← this]
    exact cantorPrefix_mono ω hl

/-- **SUV Problem 209 (Section 6.4.2, printed p. 209), main direction (de Leeuw–Moore–Shannon–
Shapiro).** If a probabilistic enumeration algorithm enumerates exactly `S` with positive
probability, then `S` is enumerable.

Proof idea (book's hint): if `{ω | W.output ω = S}` has positive measure, there is an interval
`Σ_u` where this set has relative measure `> 1/2`. Then `k ∈ S` iff the random extensions of `u`
print `k` with probability `> 1/2`, which is an enumerable condition. -/
theorem isEnumerableSet_of_prob_pos (W : ProbEnumerator) {S : Set ℕ} (h : 0 < W.prob S) :
    IsEnumerableSet S := by
  classical
  obtain ⟨chk, hchk, hmono, hiff⟩ := W.re.exists_stageApprox
  have hmeasK : ∀ k, MeasurableSet {ω : CantorSeq | k ∈ W.output ω} := by
    intro k
    have : {ω : CantorSeq | k ∈ W.output ω} =
        ⋃ n, {ω : CantorSeq | decide (W.rel (cantorPrefix ω n) k) = true} := by
      ext ω; simp [ProbEnumerator.output]
    rw [this]
    exact MeasurableSet.iUnion fun n =>
      isEnumerableSet_of_prob_pos_measurableSet (fun v => decide (W.rel v k)) n
  have hmeasA : MeasurableSet {ω : CantorSeq | W.output ω = S} := by
    have : {ω : CantorSeq | W.output ω = S} = ⋂ k, {ω : CantorSeq | k ∈ W.output ω ↔ k ∈ S} := by
      ext ω; simp [Set.ext_iff]
    rw [this]
    refine MeasurableSet.iInter fun k => ?_
    by_cases hk : k ∈ S
    · simpa [hk] using hmeasK k
    · convert (hmeasK k).compl using 1
      ext ω; simp [hk]
  obtain ⟨u, hu⟩ := isEnumerableSet_of_prob_pos_density hmeasA h
  have step3 := isEnumerableSet_of_prob_pos_re chk hchk u
  have key : ∀ k, k ∈ S ↔ isEnumerableSet_of_prob_pos_cond chk u k := by
    intro k
    set F : ℕ → Set CantorSeq := fun m =>
      {ω | isEnumerableSet_of_prob_pos_pred chk u k m (cantorPrefix ω m) = true} with hF
    have hFmeas : ∀ m, MeasurableSet (F m) := fun m =>
      isEnumerableSet_of_prob_pos_measurableSet _ m
    have hcond : isEnumerableSet_of_prob_pos_cond chk u k ↔
        ∃ m, uniformMeasure (cantorCylinder u) < 2 * uniformMeasure (F m) := by
      unfold isEnumerableSet_of_prob_pos_cond
      refine exists_congr fun m => ?_
      rw [hF, isEnumerableSet_of_prob_pos_blockMeasure, uniformMeasure_cantorCylinder]
      exact isEnumerableSet_of_prob_pos_arith _ _ _
    have hF1 : ∀ m, F m ⊆ cantorCylinder u ∩ {ω | k ∈ W.output ω} := by
      intro m ω hω
      obtain ⟨hpre, n, hn, hc⟩ := (isEnumerableSet_of_prob_pos_mem_F chk u k m ω).1 hω
      exact ⟨((isEnumerableSet_of_prob_pos_pre u m ω).1 hpre).1,
        n, (hiff (cantorPrefix ω n, k)).2 ⟨m, hc⟩⟩
    have hF2 : cantorCylinder u ∩ {ω | k ∈ W.output ω} ⊆ ⋃ m, F m := by
      rintro ω ⟨hcyl, n, hn⟩
      obtain ⟨s, hs⟩ := (hiff (cantorPrefix ω n, k)).1 hn
      refine Set.mem_iUnion.2 ⟨max (max n s) u.length, ?_⟩
      refine (isEnumerableSet_of_prob_pos_mem_F chk u k _ ω).2 ⟨?_, n, ?_, ?_⟩
      · exact (isEnumerableSet_of_prob_pos_pre u _ ω).2 ⟨hcyl, le_max_right _ _⟩
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact hmono _ s _ ((le_max_right _ _).trans (le_max_left _ _)) hs
    have hFmono : Monotone F := by
      intro m m' hmm ω hω
      obtain ⟨hpre, n, hn, hc⟩ := (isEnumerableSet_of_prob_pos_mem_F chk u k m ω).1 hω
      obtain ⟨hcyl, hlen⟩ := (isEnumerableSet_of_prob_pos_pre u m ω).1 hpre
      exact (isEnumerableSet_of_prob_pos_mem_F chk u k m' ω).2
        ⟨(isEnumerableSet_of_prob_pos_pre u m' ω).2 ⟨hcyl, hlen.trans hmm⟩, n, hn.trans hmm,
          hmono _ m m' hmm hc⟩
    rw [hcond]
    constructor
    · intro hk
      have hsub : {ω | W.output ω = S} ∩ cantorCylinder u ⊆ ⋃ m, F m := by
        intro ω ⟨hω, hc⟩
        exact hF2 ⟨hc, by simp only [Set.mem_ofPred_eq]; rw [hω]; exact hk⟩
      have h1 : uniformMeasure (cantorCylinder u) < 2 * uniformMeasure (⋃ m, F m) :=
        hu.trans_le (by gcongr)
      rw [hFmono.measure_iUnion, ENNReal.mul_iSup] at h1
      exact lt_iSup_iff.1 h1
    · rintro ⟨m, hm⟩
      by_contra hk
      have hdisj : Disjoint ({ω | W.output ω = S} ∩ cantorCylinder u) (F m) := by
        rw [Set.disjoint_left]
        intro ω ⟨hω, _⟩ hF'
        exact hk (by have := (hF1 m hF').2; simp only [Set.mem_ofPred_eq] at this; rwa [hω] at this)
      have hsum : uniformMeasure (F m) + uniformMeasure ({ω | W.output ω = S} ∩ cantorCylinder u)
          ≤ uniformMeasure (cantorCylinder u) := by
        rw [add_comm, ← MeasureTheory.measure_union hdisj (hFmeas m)]
        refine MeasureTheory.measure_mono ?_
        rintro ω (⟨_, hc⟩ | hω)
        · exact hc
        · exact (hF1 m hω).1
      have h2 := ENNReal.add_lt_add hm hu
      have h3 : 2 * uniformMeasure (F m) +
          2 * uniformMeasure ({ω | W.output ω = S} ∩ cantorCylinder u) ≤
          uniformMeasure (cantorCylinder u) + uniformMeasure (cantorCylinder u) := by
        rw [← mul_add, ← two_mul]; gcongr
      exact absurd (h2.trans_le h3) (lt_irrefl _)
  exact (step3.of_iff (fun k => (key k).symm))

/-- **SUV Problem 209 (Section 6.4.2, printed p. 209).** For an optimal probabilistic
enumeration algorithm, `m(S) > 0` iff `S` is enumerable.

Proof idea: `→` is `isEnumerableSet_of_prob_pos`. `←`: an enumerable `S` is enumerated with
probability `1` by the algorithm that ignores its random bits, and optimality transfers a
positive probability. -/
theorem prob_pos_iff_isEnumerableSet {W : ProbEnumerator} (hW : W.IsOptimal) (S : Set ℕ) :
    0 < W.prob S ↔ IsEnumerableSet S := by
  refine ⟨isEnumerableSet_of_prob_pos W, fun hS => ?_⟩
  let W' : ProbEnumerator :=
    { rel := fun _ k => k ∈ S
      re := IsRE.comp_computable (g := fun q : BitString × ℕ => q.2) hS Computable.snd
      mono := fun _ _ _ h _ => h }
  obtain ⟨c, hc, hcS⟩ := hW W'
  have h1 : W'.prob S = 1 := by
    unfold ProbEnumerator.prob
    have : {ω | W'.output ω = S} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      ext k
      simp [ProbEnumerator.output, W']
    rw [this]
    exact MeasureTheory.measure_univ
  have := hcS S
  rw [h1, mul_one] at this
  exact lt_of_lt_of_le hc this

end GeneralScheme

end Kolmogorov
