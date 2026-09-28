import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.SubSemimeasureDomination

/-!
# Mixtures of branch measures

A probabilistic algorithm that first draws an index `i` with probability `w i` and then prints
the bits of a computable sequence `α i` realises the continuous semimeasure

`branchMixture w α u = ∑' i, w i * branchMeasure (α i) u`,

the mass of which sits on the branches `α i`.  This module collects what such a mixture
satisfies — its root value, the child inequality, lower semicomputability — and the root patch
that turns a sub-normalised mixture into a genuine continuous tree semimeasure, whose only use
is to feed it to the maximality of `universalContinuousSemimeasure`.  Both halves of the note
enter the a priori probability through `exists_const_le_universalContinuousSemimeasure`.

The weights of the mixture are read off a bit string through `decodeIndex`, a computable
**surjective** decoding whose right inverse is the computable key `indexKey i = natCode
(Encodable.encode i)`.  Surjectivity is what makes a hypothesis about `indexWeight w` a
hypothesis about every single weight `w i`, which is what the lower-semicomputability theorem
of the mixture needs.

The maximality invoked by `exists_const_le_universalContinuousSemimeasure` is SUV Chapter 5,
§5.2, Theorem 78, p. 135; the mixture construction itself is the note's.

Source: the note `apriori-atoms.md`, sections "Почему m(x) ≤ C f(x)" and "Почему обратная
оценка неверна"; SUV Chapter 5, §5.2.
-/

open scoped ENNReal

namespace Kolmogorov

/-! ### Reading the weights of an index type off a bit string -/

/-- The key of an index: the unary self-delimiting code `1^q0` of the number `q` that the
`Encodable` structure of the index type attaches to it.  Every index has a key and the key is
computable from the index, so a property of the weights read at keys is a property of every
weight.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
def indexKey {ι : Type} [Encodable ι] (i : ι) : BitString := natCode (Encodable.encode i)

/-- The index a bit string codes: the string is read as the unary code of a number, that number
is decoded to an index, and the index is accepted only if the string is its key.  Together with
`indexKey` this is a computable surjective decoding of the index type — unlike
`Encodable.decode ∘ Encodable.encode`, which composes the encoder of `BitString` with the
decoder of the index type and therefore misses the indices whose code is not the code of any
bit string.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
def decodeIndex (ι : Type) [Encodable ι] (x : BitString) : Option ι :=
  (Encodable.decode (α := ι) (CodedFiniteDistribution.decodeNatCode x)).bind
    fun i => if indexKey i = x then some i else none

/-- A bit string codes an index exactly when it is the key of that index. -/
@[simp] theorem decodeIndex_eq_some_iff {ι : Type} [Encodable ι] {x : BitString} {i : ι} :
    decodeIndex ι x = some i ↔ indexKey i = x := by
  constructor
  · intro h
    rw [decodeIndex, Option.bind_eq_some_iff] at h
    obtain ⟨j, _, hj⟩ := h
    by_cases hkey : indexKey j = x
    · rw [if_pos hkey] at hj
      rw [← Option.some_inj.mp hj]
      exact hkey
    · rw [if_neg hkey] at hj
      exact absurd hj (by simp)
  · intro h
    subst h
    rw [decodeIndex, indexKey, CodedFiniteDistribution.decodeNatCode_natCode,
      Encodable.encodek]
    simp [indexKey]

/-- The index decoding is computable. -/
theorem computable_decodeIndex (ι : Type) [Primcodable ι] : Computable (decodeIndex ι) := by
  have hkey : Computable (fun i : ι => indexKey i) :=
    primrec_natCode.to_comp.comp Computable.encode
  have hdec : Computable (fun x : BitString =>
      Encodable.decode (α := ι) (CodedFiniteDistribution.decodeNatCode x)) :=
    Computable.decode.comp CodedFiniteDistribution.decodeNatCode_primrec.to_comp
  have hpred : Computable (fun p : BitString × ι => decide (indexKey p.2 = p.1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp (hkey.comp Computable.snd) Computable.fst
  have hfilter : Computable₂ (fun (x : BitString) (i : ι) =>
      if indexKey i = x then some i else none) :=
    (Computable.cond hpred (Computable.option_some.comp Computable.snd)
      (Computable.const none)).of_eq (fun p => by by_cases h : indexKey p.2 = p.1 <;> simp [h])
  exact hdec.option_bind hfilter

/-- The weights of an encodable index type, read as a function of a bit string: the string is
decoded to an index, and a string that codes no index gets weight `0`.  This is the shape in
which the library's `IsLSC` interface can speak about the weights of a mixture.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
noncomputable def indexWeight {ι : Type} [Encodable ι] (w : ι → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  (decodeIndex ι x).elim 0 w

/-- **The reading of the weights at the key of an index is the weight of that index.**  This is
what turns a hypothesis about `indexWeight w` into a hypothesis about every weight `w i`. -/
@[simp] theorem indexWeight_indexKey {ι : Type} [Encodable ι] (w : ι → ℝ≥0∞) (i : ι) :
    indexWeight w (indexKey i) = w i := by
  rw [indexWeight, show decodeIndex ι (indexKey i) = some i from decodeIndex_eq_some_iff.mpr rfl]
  rfl

/-- **Lower semicomputability is inherited along a computable partial decoding of bit strings**,
the value `0` being given to the strings that decode to nothing.  This is how the weight
hypothesis of `branchMixture_isLSC` is met by a lower semicomputable family indexed by bit
strings.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
theorem isLSC_option_elim {v : BitString → ℝ≥0∞} (hv : IsLSC fun x _ => v x)
    {φ : BitString → Option BitString} (hφ : Computable φ) :
    IsLSC fun x (_ : BitString) => (φ x).elim 0 v := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hv
  refine ⟨fun s x ctx => (φ x).elim 0 fun y => approx s y ctx, ?_, ?_, ?_⟩
  · intro s x ctx
    cases h : φ x with
    | none => simp [h, dyadicValue]
    | some y => simpa [h] using hmono s y ctx
  · intro x ctx
    cases h : φ x with
    | none => simp [h, dyadicValue]
    | some y => simpa [h] using hsup y ctx
  · have ho : Computable (fun p : ℕ × BitString × BitString => φ p.2.1) :=
      hφ.comp (Computable.fst.comp Computable.snd)
    have hg : Computable₂ (fun (p : ℕ × BitString × BitString) (y : BitString) =>
        approx p.1 y p.2.2) :=
      hcomp.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair Computable.snd
          (Computable.snd.comp (Computable.snd.comp Computable.fst))))
    exact (Computable.option_casesOn ho (Computable.const 0) hg).of_eq
      (fun p => by cases h : φ p.2.1 <;> simp [h])

/-- The mixture of the branch measures of the sequences `α i` with weights `w i`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
noncomputable def branchMixture {ι : Type} (w : ι → ℝ≥0∞) (α : ι → CantorSeq)
    (u : BitString) : ℝ≥0∞ :=
  ∑' i, w i * branchMeasure (α i) u

/-- At the root the mixture carries the total weight. -/
theorem branchMixture_root {ι : Type} (w : ι → ℝ≥0∞) (α : ι → CantorSeq) :
    branchMixture w α [] = ∑' i, w i := by
  refine tsum_congr fun i => ?_
  simp [branchMeasure, cantorPrefix]

/-- A string on the branch `α i` carries at least the weight of `i`. -/
theorem le_branchMixture {ι : Type} (w : ι → ℝ≥0∞) (α : ι → CantorSeq) (i : ι)
    {u : BitString} (h : cantorPrefix (α i) u.length = u) :
    w i ≤ branchMixture w α u := by
  have h1 : w i * branchMeasure (α i) u = w i := by rw [branchMeasure, if_pos h, mul_one]
  rw [← h1]
  exact ENNReal.le_tsum i

/-- The two children of a node carry together at most the mass of the node. -/
theorem branchMixture_child_le {ι : Type} (w : ι → ℝ≥0∞) (α : ι → CantorSeq) (u : BitString) :
    branchMixture w α (u ++ [false]) + branchMixture w α (u ++ [true]) ≤ branchMixture w α u := by
  have key : ∀ i : ι, w i * branchMeasure (α i) (u ++ [false]) +
      w i * branchMeasure (α i) (u ++ [true]) ≤ w i * branchMeasure (α i) u := by
    intro i
    rw [← mul_add]
    gcongr
    exact (branchMeasure_isContinuousTreeSemimeasure (α i)).2 u
  calc branchMixture w α (u ++ [false]) + branchMixture w α (u ++ [true])
      = ∑' i : ι, (w i * branchMeasure (α i) (u ++ [false]) +
          w i * branchMeasure (α i) (u ++ [true])) := (ENNReal.tsum_add).symm
    _ ≤ ∑' i : ι, w i * branchMeasure (α i) u := ENNReal.tsum_le_tsum key

private theorem tsum_decode₂_elim {ι : Type} [Encodable ι] (F : ι → ℝ≥0∞) :
    (∑' n : ℕ, (Encodable.decode₂ ι n).elim 0 F) = ∑' i, F i := by
  let e := Encodable.equivRangeEncode ι
  have he := e.tsum_eq (fun j => F (e.symm j))
  simp only [Equiv.symm_apply_apply] at he
  calc
    (∑' n : ℕ, (Encodable.decode₂ ι n).elim 0 F) =
        ∑' n : ℕ, (Set.range (@Encodable.encode ι _)).indicator
          (fun n => (Encodable.decode₂ ι n).elim 0 F) n := by
      refine tsum_congr fun n => ?_
      by_cases hn : n ∈ Set.range (@Encodable.encode ι _)
      · simp [Set.indicator_of_mem hn]
      · simp only [Set.indicator, hn, ↓reduceIte]
        have hnone : Encodable.decode₂ ι n = none := by
          apply Option.eq_none_iff_forall_not_mem.mpr
          intro i hi
          exact hn ⟨i, Encodable.mem_decode₂.mp hi⟩
        simp [hnone]
    _ = ∑' j : Set.range (@Encodable.encode ι _),
        (Encodable.decode₂ ι j.1).elim 0 F :=
      (tsum_subtype (Set.range (@Encodable.encode ι _))
        (fun n => (Encodable.decode₂ ι n).elim 0 F)).symm
    _ = ∑' j : Set.range (@Encodable.encode ι _), F (e.symm j) := by
      refine tsum_congr fun j => ?_
      have henc : Encodable.encode (e.symm j) = j.1 := by
        change (e (e.symm j)).1 = j.1
        exact congr_arg Subtype.val (e.apply_symm_apply j)
      rw [Encodable.decode₂_eq_some.mpr henc]
      rfl
    _ = ∑' i, F i := he.symm

private theorem computable_cantorPrefix_family {ι : Type} [Primcodable ι]
    (α : ι → CantorSeq) (hα : Computable₂ fun (i : ι) (k : ℕ) => α i k) :
    Computable fun p : ι × ℕ => cantorPrefix (α p.1) p.2 := by
  have hstep : Computable (fun p : (ι × ℕ) × (ℕ × BitString) =>
      p.2.2 ++ [α p.1.1 p.2.1]) :=
    Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hα.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))
  have hrec := Computable.nat_rec (f := fun p : ι × ℕ => p.2)
    (g := fun _ => ([] : BitString))
    (h := fun p : ι × ℕ => fun q : ℕ × BitString => q.2 ++ [α p.1 q.1])
    Computable.snd (Computable.const []) hstep.to₂
  apply hrec.of_eq
  intro p
  change Nat.rec ([] : BitString) (fun k acc => acc ++ [α p.1 k]) p.2 =
    cantorPrefix (α p.1) p.2
  induction p.2 with
  | zero => rfl
  | succ n ih =>
      change Nat.rec ([] : BitString) (fun k acc => acc ++ [α p.1 k]) n ++ [α p.1 n] =
        cantorPrefix (α p.1) (n + 1)
      rw [ih, cantorPrefix_succ]

/-- **The mixture of a uniformly computable family of branches with lower semicomputable
weights is lower semicomputable.**  Enumerating the weights from below and the sequences by
longer and longer prefixes gives a computable monotone dyadic approximation of the mixture.
The weight hypothesis reaches every index `i`, because `indexWeight w (indexKey i) = w i`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
theorem branchMixture_isLSC {ι : Type} [Primcodable ι] (w : ι → ℝ≥0∞) (α : ι → CantorSeq)
    (hw : IsLSC fun x _ => indexWeight w x)
    (hα : Computable₂ fun (i : ι) (k : ℕ) => α i k) :
    IsLSC fun u _ => branchMixture w α u := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hw
  let b : ℕ → BitString → ℝ≥0∞ := fun n u =>
    (Encodable.decode₂ ι n).elim 0 fun i => w i * branchMeasure (α i) u
  let A : ℕ → ℕ → BitString → ℕ := fun n s u =>
    (Encodable.decode₂ ι n).elim 0 fun i =>
      if cantorPrefix (α i) u.length = u then approx s (indexKey i) [] else 0
  have hA_mono : ∀ n s u,
      dyadicValue (A n s u) s ≤ dyadicValue (A n (s + 1) u) (s + 1) := by
    intro n s u
    cases hdec : Encodable.decode₂ ι n with
    | none => simp [A, hdec, dyadicValue_zero]
    | some i =>
        by_cases hp : cantorPrefix (α i) u.length = u
        · simpa [A, hdec, hp] using hmono s (indexKey i) []
        · simp [A, hdec, hp, dyadicValue_zero]
  have hA_sup : ∀ n u, ⨆ s, dyadicValue (A n s u) s = b n u := by
    intro n u
    cases hdec : Encodable.decode₂ ι n with
    | none => simp [A, b, hdec, dyadicValue_zero]
    | some i =>
        by_cases hp : cantorPrefix (α i) u.length = u
        · simp [A, b, hdec, hp, branchMeasure, hsup, indexWeight_indexKey]
        · simp [A, b, hdec, hp, branchMeasure, dyadicValue_zero]
  have hA_comp : Computable fun p : ℕ × ℕ × BitString => A p.1 p.2.1 p.2.2 := by
    have hdecode : Computable fun p : ℕ × ℕ × BitString =>
        Encodable.decode₂ ι p.1 :=
      Primrec.decode₂.to_comp.comp Computable.fst
    have hkey : Computable fun q : (ℕ × ℕ × BitString) × ι => indexKey q.2 :=
      primrec_natCode.to_comp.comp (Computable.encode.comp Computable.snd)
    have hstage : Computable fun q : (ℕ × ℕ × BitString) × ι => q.1.2.1 :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hargs : Computable fun q : (ℕ × ℕ × BitString) × ι =>
        (q.1.2.1, indexKey q.2, ([] : BitString)) :=
      hstage.pair (hkey.pair (Computable.const []))
    have happ : Computable fun q : (ℕ × ℕ × BitString) × ι =>
        approx q.1.2.1 (indexKey q.2) [] :=
      Computable.comp
        (f := fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)
        (g := fun q : (ℕ × ℕ × BitString) × ι =>
          (q.1.2.1, indexKey q.2, ([] : BitString))) hcomp hargs
    have hlength : Computable fun q : (ℕ × ℕ × BitString) × ι =>
        q.1.2.2.length :=
      (Primrec.list_length.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to_comp
    have hprefixArgs : Computable fun q : (ℕ × ℕ × BitString) × ι =>
        (q.2, q.1.2.2.length) :=
      Computable.snd.pair hlength
    have hprefix : Computable fun q : (ℕ × ℕ × BitString) × ι =>
        cantorPrefix (α q.2) q.1.2.2.length :=
      Computable.comp
        (f := fun p : ι × ℕ => cantorPrefix (α p.1) p.2)
        (g := fun q : (ℕ × ℕ × BitString) × ι => (q.2, q.1.2.2.length))
        (computable_cantorPrefix_family α hα) hprefixArgs
    have hout : Computable fun q : (ℕ × ℕ × BitString) × ι => q.1.2.2 :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have heq : Computable fun q : (ℕ × ℕ × BitString) × ι =>
        decide (cantorPrefix (α q.2) q.1.2.2.length = q.1.2.2) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp hprefix hout
    have hbranch : Computable fun q : (ℕ × ℕ × BitString) × ι =>
        if cantorPrefix (α q.2) q.1.2.2.length = q.1.2.2 then
          approx q.1.2.1 (indexKey q.2) [] else 0 :=
      (Computable.cond heq happ (Computable.const 0)).of_eq fun q => by
        by_cases h : cantorPrefix (α q.2) q.1.2.2.length = q.1.2.2 <;> simp [h]
    exact (Computable.option_casesOn hdecode (Computable.const 0) hbranch.to₂).of_eq
      fun p => by cases h : Encodable.decode₂ ι p.1 <;> simp [A, h]
  have hlsc := isLSC_tsum_nsmul_of_uniform (wt := fun _ => 1) (A := A)
    (Computable.const 1) hA_mono hA_sup hA_comp
  have hsum : ∀ u, (∑' n, ((1 : ℕ) : ℝ≥0∞) * b n u) = branchMixture w α u := by
    intro u
    simp only [Nat.cast_one, one_mul]
    rw [show (∑' n, b n u) = ∑' i, w i * branchMeasure (α i) u from ?_]
    · rfl
    · exact tsum_decode₂_elim fun i => w i * branchMeasure (α i) u
  simpa only [hsum] using hlsc

/-- The mass function `a` with its root value raised to `1`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
noncomputable def patchRoot (a : BitString → ℝ≥0∞) : BitString → ℝ≥0∞ :=
  fun u => if u = [] then 1 else a u

/-- Away from the root the patch changes nothing. -/
theorem patchRoot_of_ne {a : BitString → ℝ≥0∞} {u : BitString} (h : u ≠ []) :
    patchRoot a u = a u := if_neg h

/-- The patch only increases the mass, as long as the root mass was at most one. -/
theorem le_patchRoot {a : BitString → ℝ≥0∞} (hroot : a [] ≤ 1) (u : BitString) :
    a u ≤ patchRoot a u := by
  by_cases h : u = []
  · subst h
    simpa [patchRoot] using hroot
  · rw [patchRoot_of_ne h]

/-- Raising the root value to `1` preserves lower semicomputability. -/
theorem patchRoot_isLSC {a : BitString → ℝ≥0∞} (hlsc : IsLSC fun u _ => a u) :
    IsLSC fun u _ => patchRoot a u := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hlsc
  refine ⟨fun s out ctx => if out = [] then 2 ^ s else approx s out ctx, ?_, ?_, ?_⟩
  · intro s out ctx
    by_cases h : out = []
    · simp [h, dyadicValue_two_pow_self]
    · simpa [h] using hmono s out ctx
  · intro out ctx
    by_cases h : out = []
    · simp [h, patchRoot, dyadicValue_two_pow_self]
    · simpa [h, patchRoot_of_ne h] using hsup out ctx
  · have hpred : Computable (fun p : ℕ × BitString × BitString =>
        decide (p.2.1 = [])) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.const [])
    have hpow : Computable (fun p : ℕ × BitString × BitString => 2 ^ p.1) :=
      primrec_two_pow_aux.to_comp.comp Computable.fst
    exact (Computable.cond hpred hpow hcomp).of_eq
      (fun p => by by_cases h : p.2.1 = [] <;> simp [h])

/-- A sub-normalised, lower semicomputable mass function with the child inequality becomes a
lower semicomputable continuous tree semimeasure once its root value is raised to `1`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
theorem patchRoot_isLowerSemicomputableContinuousSemimeasure {a : BitString → ℝ≥0∞}
    (hroot : a [] ≤ 1) (hchild : ∀ u, a (u ++ [false]) + a (u ++ [true]) ≤ a u)
    (hlsc : IsLSC fun u _ => a u) :
    IsLowerSemicomputableContinuousSemimeasure (patchRoot a) := by
  refine ⟨⟨by simp [patchRoot], fun u => ?_⟩, patchRoot_isLSC hlsc⟩
  have hf : u ++ [false] ≠ [] := by simp
  have ht : u ++ [true] ≠ [] := by simp
  rw [patchRoot_of_ne hf, patchRoot_of_ne ht]
  refine le_trans (hchild u) ?_
  exact le_patchRoot hroot u

/-- **Every sub-normalised lower semicomputable mass function with the child inequality is
dominated by the a priori probability.**  This is the single place where the maximality of
`universalContinuousSemimeasure` is used; both halves of the note apply it.

Source: the note `apriori-atoms.md`, sections "Почему m(x) ≤ C f(x)" and "Почему обратная
оценка неверна"; SUV Chapter 5, §5.2. -/
theorem exists_const_le_universalContinuousSemimeasure {a : BitString → ℝ≥0∞}
    (hroot : a [] ≤ 1) (hchild : ∀ u, a (u ++ [false]) + a (u ++ [true]) ≤ a u)
    (hlsc : IsLSC fun u _ => a u) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ u, c * a u ≤ universalContinuousSemimeasure u := by
  obtain ⟨c, hc_top, hc⟩ := universalContinuousSemimeasure_isMaximal (patchRoot a)
    (patchRoot_isLowerSemicomputableContinuousSemimeasure hroot hchild hlsc)
  have hne : (c + 1) ≠ 0 := by simp
  have hne_top : (c + 1) ≠ ⊤ := by simp [hc_top]
  refine ⟨(c + 1)⁻¹, ENNReal.inv_ne_zero.mpr hne_top, ENNReal.inv_ne_top.mpr hne, fun u => ?_⟩
  have h1 : a u ≤ (c + 1) * universalContinuousSemimeasure u := by
    refine le_trans (le_trans (le_patchRoot hroot u) (hc u)) ?_
    gcongr
    exact le_self_add
  calc (c + 1)⁻¹ * a u ≤ (c + 1)⁻¹ * ((c + 1) * universalContinuousSemimeasure u) := by
        gcongr
    _ = universalContinuousSemimeasure u := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne hne_top, one_mul]

end Kolmogorov
