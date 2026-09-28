/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Stream
import KolmogorovMathlib.MonotoneComplexity.PrefixStream
import KolmogorovMathlib.AlgorithmicRandomness.Cantor
import KolmogorovMathlib.Foundation.RecursivelyEnumerable

/-!
# Continuous maps on finite-or-infinite streams

This module provides the stable interface for continuous maps `BitStream → BitStream`
and their lower graphs.
-/

namespace Kolmogorov

/-- A stream map is continuous when it is monotone and its value on an infinite stream is the
least upper bound of its values on the finite prefixes. -/
def IsContinuousStreamMap (f : BitStream → BitStream) : Prop :=
  Monotone f ∧ ∀ w : CantorSeq, ∀ y : BitStream,
    (∀ n, f (.finite (cantorPrefix w n)) ≤ y) → f (.infinite w) ≤ y

/-- The lower graph of a stream map: the finite outputs it already produces on a finite input. -/
def streamLowerGraph (f : BitStream → BitStream) (x y : BitString) : Prop :=
  BitStream.finite y ≤ f (.finite x)

/-- A stream map is computable when it is continuous and its lower graph is recursively
enumerable. -/
def IsComputableStreamMap (f : BitStream → BitStream) : Prop :=
  IsContinuousStreamMap f ∧
    IsRE fun p : BitString × BitString => streamLowerGraph f p.1 p.2

/-- The axioms of a lower graph: it contains the empty output, is closed downwards in the output,
upwards in the input, and has comparable outputs at a fixed input. -/
def IsStreamLowerGraph (R : BitString → BitString → Prop) : Prop :=
  (∀ x, R x []) ∧
  (∀ x y y', R x y → y' <+: y → R x y') ∧
  (∀ x x' y, R x y → x <+: x' → R x' y) ∧
  (∀ x y y', R x y → R x y' → y <+: y' ∨ y' <+: y)

/-- Comparable inputs give comparable outputs. -/
lemma IsStreamLowerGraph.output_compatible_of_input_compatible {R}
    (hR : IsStreamLowerGraph R) {x₁ x₂ y₁ y₂ : BitString}
    (hx : x₁ <+: x₂ ∨ x₂ <+: x₁) (hy₁ : R x₁ y₁) (hy₂ : R x₂ y₂) :
    y₁ <+: y₂ ∨ y₂ <+: y₁ := by
  rcases hx with hx | hx
  · exact hR.2.2.2 x₂ y₁ y₂ (hR.2.2.1 x₁ x₂ y₁ hy₁ hx) hy₂
  · exact hR.2.2.2 x₁ y₁ y₂ hy₁ (hR.2.2.1 x₂ x₁ y₂ hy₂ hx)

/-- Taking the first `|a|` entries of a string with prefix `a` returns `a`. -/
lemma isPrefix_of_isPrefix_take {a c : BitString} (ha : a <+: c) : c.take a.length = a := by
  rcases ha with ⟨l, rfl⟩
  exact List.take_left

/-- Two prefixes of a common string are comparable. -/
lemma isPrefix_or_isPrefix_of_isPrefix {a b c : BitString} (ha : a <+: c) (hb : b <+: c) :
    a <+: b ∨ b <+: a := by
  rcases le_total a.length b.length with hlen | hlen
  · left
    have H1 : c.take b.length = b := isPrefix_of_isPrefix_take hb
    have H2 : c.take a.length = a := isPrefix_of_isPrefix_take ha
    have H3 : (c.take b.length).take a.length = c.take (min a.length b.length) :=
      by rw [List.take_take]
    rw [min_eq_left hlen] at H3
    rw [H1] at H3
    rw [H3.symm] at H2
    nth_rw 1 [← H2]
    exact List.take_prefix _ _
  · right
    have H1 : c.take a.length = a := isPrefix_of_isPrefix_take ha
    have H2 : c.take b.length = b := isPrefix_of_isPrefix_take hb
    have H3 : (c.take a.length).take b.length = c.take (min b.length a.length) :=
      by rw [List.take_take]
    rw [min_eq_left hlen] at H3
    rw [H1] at H3
    rw [H3.symm] at H2
    nth_rw 1 [← H2]
    exact List.take_prefix _ _

/-- The lower graph of a monotone stream map satisfies the lower-graph axioms. -/
lemma continuousStreamMap_lowerGraph_isStreamLowerGraph {f : BitStream → BitStream}
    (hf : Monotone f) :
    IsStreamLowerGraph (streamLowerGraph f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact BitStream.nil_le _
  · intro x y y' hy hle
    dsimp [streamLowerGraph] at hy ⊢
    exact le_trans hle hy
  · intro x x' y hy hle
    dsimp [streamLowerGraph] at hy ⊢
    exact le_trans hy (hf hle)
  · intro x y y' hy hy'
    dsimp [streamLowerGraph] at hy hy'
    cases hfx : f (.finite x) with
    | finite z =>
      rw [hfx] at hy hy'
      exact isPrefix_or_isPrefix_of_isPrefix hy hy'
    | infinite w =>
      rw [hfx] at hy hy'
      have hy1 : y <+: cantorPrefix w (max y.length y'.length) := by
        have hy_eq : cantorPrefix w y.length = y :=
          (isCantorPrefix_iff_cantorPrefix_eq y w).1 hy
        nth_rw 1 [← hy_eq]
        exact cantorPrefix_mono w (le_max_left y.length y'.length)
      have hy2 : y' <+: cantorPrefix w (max y.length y'.length) := by
        have hy'_eq : cantorPrefix w y'.length = y' :=
          (isCantorPrefix_iff_cantorPrefix_eq y' w).1 hy'
        nth_rw 1 [← hy'_eq]
        exact cantorPrefix_mono w (le_max_right y.length y'.length)
      exact isPrefix_or_isPrefix_of_isPrefix hy1 hy2

/-- The outputs of a lower graph at a finite input form a prefix set. -/
lemma IsStreamLowerGraph.finiteSection_isStreamPrefixSet {R} (hR : IsStreamLowerGraph R)
    (x : BitString) :
    IsStreamPrefixSet (R x) :=
  ⟨hR.1 x, fun {u v} hle hv => hR.2.1 x v u hv hle, fun {u v} hu hv => hR.2.2.2 x u v hu hv⟩

/-- The outputs of a lower graph at some finite prefix of an infinite input. -/
def infiniteSection (R : BitString → BitString → Prop) (w : CantorSeq) : Set BitString :=
  { y | ∃ n, R (cantorPrefix w n) y }

/-- The outputs of a lower graph at an infinite input form a prefix set. -/
lemma IsStreamLowerGraph.infiniteSection_isStreamPrefixSet {R} (hR : IsStreamLowerGraph R)
    (w : CantorSeq) :
    IsStreamPrefixSet (infiniteSection R w) := by
  constructor
  · exact ⟨0, hR.1 _⟩
  · constructor
    · intro u v hle ⟨n, hn⟩
      exact ⟨n, hR.2.1 _ _ _ hn hle⟩
    · intro u v ⟨n, hn⟩ ⟨m, hm⟩
      let k := max n m
      have hk1 : n ≤ k := le_max_left n m
      have hk2 : m ≤ k := le_max_right n m
      have h1 := hR.2.2.1 _ _ _ hn (cantorPrefix_mono w hk1)
      have h2 := hR.2.2.1 _ _ _ hm (cantorPrefix_mono w hk2)
      exact hR.2.2.2 _ _ _ h1 h2

/-- The stream map determined by a lower graph. -/
noncomputable def streamMapOfLowerGraph (R : BitString → BitString → Prop)
    (hR : IsStreamLowerGraph R) :
    BitStream → BitStream
  | .finite x => BitStream.ofPrefixSet (R x)
      (hR.finiteSection_isStreamPrefixSet x)
  | .infinite w => BitStream.ofPrefixSet (infiniteSection R w)
      (hR.infiniteSection_isStreamPrefixSet w)

/-- On a finite input the map produces exactly the outputs of the graph. -/
lemma streamMapOfLowerGraph_finite_spec {R} (hR : IsStreamLowerGraph R) (x y : BitString) :
    BitStream.finite y ≤ streamMapOfLowerGraph R hR (.finite x) ↔ R x y := by
  dsimp [streamMapOfLowerGraph]
  exact BitStream.finite_le_ofPrefixSet_iff (hR.finiteSection_isStreamPrefixSet x) y

/-- On an infinite input the map produces the outputs of the graph at the finite prefixes. -/
lemma streamMapOfLowerGraph_infinite_spec {R} (hR : IsStreamLowerGraph R) (w : CantorSeq)
    (y : BitString) :
    BitStream.finite y ≤ streamMapOfLowerGraph R hR (.infinite w) ↔
      ∃ n, R (cantorPrefix w n) y := by
  dsimp [streamMapOfLowerGraph]
  exact BitStream.finite_le_ofPrefixSet_iff (hR.infiniteSection_isStreamPrefixSet w) y

/-- One stream extends another exactly when it produces all of its finite prefixes. -/
lemma BitStream.le_iff_forall_finite_le {a b : BitStream} :
    a ≤ b ↔ ∀ y : BitString, BitStream.finite y ≤ a → BitStream.finite y ≤ b := by
  constructor
  · intro hab y hya
    exact le_trans hya hab
  · intro h
    cases a with
    | finite x =>
      have H := h x (le_refl _)
      exact H
    | infinite w =>
      cases b with
      | finite z =>
        have H : ∀ n, (cantorPrefix w n).length ≤ z.length := by
          intro n
          have H1 : BitStream.finite (cantorPrefix w n) ≤ .infinite w := by
            intro i hi
            have hi2 : i < n := by simpa [cantorPrefix_length] using hi
            simp [cantorPrefix_getElem _ _ _ hi]
          have H2 : BitStream.finite (cantorPrefix w n) ≤ .finite z := h _ H1
          exact H2.length_le
        have H_len := H (z.length + 1)
        simp only [cantorPrefix_length] at H_len
        omega
      | infinite v =>
        have hw : w = v := by
          ext n
          have H1 : BitStream.finite (cantorPrefix w (n + 1)) ≤ .infinite w := by
            intro i hi
            have hi2 : i < n + 1 := by simpa [cantorPrefix_length] using hi
            simp [cantorPrefix_getElem _ _ _ hi]
          have H2 : BitStream.finite (cantorPrefix w (n + 1)) ≤ .infinite v := h _ H1
          have H3 : w n = v n := by
            have hw_get := cantorPrefix_getElem w (n + 1) n (by simp)
            have hv_get := H2 n (by simp)
            exact hw_get.symm.trans hv_get.symm
          exact H3
        exact hw ▸ le_refl _

/-- Two streams with the same finite prefixes are equal. -/
lemma BitStream.eq_of_forall_finite_le_iff (s t : BitStream)
    (h : ∀ y : BitString, BitStream.finite y ≤ s ↔ BitStream.finite y ≤ t) : s = t := by
  apply le_antisymm
  · exact le_iff_forall_finite_le.2 (fun y hy => (h y).1 hy)
  · exact le_iff_forall_finite_le.2 (fun y hy => (h y).2 hy)

/-- The map determined by a lower graph is monotone. -/
lemma streamMapOfLowerGraph_mono {R} (hR : IsStreamLowerGraph R) :
    Monotone (streamMapOfLowerGraph R hR) := by
  intro s t hst
  rw [BitStream.le_iff_forall_finite_le]
  intro y hy
  cases s with
  | finite x =>
    rw [streamMapOfLowerGraph_finite_spec] at hy
    cases t with
    | finite z =>
      rw [streamMapOfLowerGraph_finite_spec]
      exact hR.2.2.1 x z y hy hst
    | infinite w =>
      rw [streamMapOfLowerGraph_infinite_spec]
      have h1 : cantorPrefix w x.length = x := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hst
      exact ⟨x.length, by rwa [h1]⟩
  | infinite w =>
    rw [streamMapOfLowerGraph_infinite_spec] at hy
    cases t with
    | finite z => exact False.elim hst
    | infinite v =>
      change w = v at hst
      rw [hst] at hy
      rw [streamMapOfLowerGraph_infinite_spec]
      exact hy

/-- The map determined by a lower graph is continuous. -/
lemma streamMapOfLowerGraph_isContinuousStreamMap {R} (hR : IsStreamLowerGraph R) :
    IsContinuousStreamMap (streamMapOfLowerGraph R hR) := by
  constructor
  · exact streamMapOfLowerGraph_mono hR
  · intro w y hy
    rw [BitStream.le_iff_forall_finite_le]
    intro u hu
    rw [streamMapOfLowerGraph_infinite_spec] at hu
    rcases hu with ⟨n, hn⟩
    have hy2 := hy n
    rw [BitStream.le_iff_forall_finite_le] at hy2
    have hy3 := hy2 u
    rw [streamMapOfLowerGraph_finite_spec] at hy3
    exact hy3 hn

/-- A continuous map produces a finite output on an infinite input exactly when it does so on some
finite prefix. -/
lemma continuousStreamMap_finite_le_infinite_iff (f : BitStream → BitStream)
    (hf : IsContinuousStreamMap f)
    (w : CantorSeq) (y : BitString) :
    BitStream.finite y ≤ f (.infinite w) ↔
      ∃ n, BitStream.finite y ≤ f (.finite (cantorPrefix w n)) := by
  let R := streamLowerGraph f
  have hR : IsStreamLowerGraph R := continuousStreamMap_lowerGraph_isStreamLowerGraph hf.1
  have H1 : ∀ n, f (.finite (cantorPrefix w n)) ≤
      streamMapOfLowerGraph R hR (.infinite w) := by
    intro n
    rw [BitStream.le_iff_forall_finite_le]
    intro u hu
    rw [streamMapOfLowerGraph_infinite_spec]
    exact ⟨n, hu⟩
  have H2 : f (.infinite w) ≤ streamMapOfLowerGraph R hR (.infinite w) := hf.2 w _ H1
  have H3 : streamMapOfLowerGraph R hR (.infinite w) ≤ f (.infinite w) := by
    rw [BitStream.le_iff_forall_finite_le]
    intro u hu
    rw [streamMapOfLowerGraph_infinite_spec] at hu
    rcases hu with ⟨n, hn⟩
    have H3_1 : BitStream.finite (cantorPrefix w n) ≤ .infinite w := by
      intro i hi
      have hi2 : i < n := by simpa [cantorPrefix_length] using hi
      simp [cantorPrefix_getElem _ _ _ hi]
    exact le_trans hn (hf.1 H3_1)
  have H_eq : f (.infinite w) = streamMapOfLowerGraph R hR (.infinite w) :=
    le_antisymm H2 H3
  rw [H_eq, streamMapOfLowerGraph_infinite_spec]
  rfl

/-- Two continuous stream maps with the same lower graph are equal. -/
lemma continuousStreamMap_ext_of_lowerGraph_eq {f g : BitStream → BitStream}
    (hf : IsContinuousStreamMap f) (hg : IsContinuousStreamMap g)
    (h : ∀ x y, streamLowerGraph f x y ↔ streamLowerGraph g x y) : f = g := by
  funext s
  apply BitStream.eq_of_forall_finite_le_iff
  intro y
  cases s with
  | finite x => exact h x y
  | infinite w =>
    rw [continuousStreamMap_finite_le_infinite_iff f hf]
    rw [continuousStreamMap_finite_le_infinite_iff g hg]
    constructor
    · intro ⟨n, hn⟩
      exact ⟨n, (h _ _).1 hn⟩
    · intro ⟨n, hn⟩
      exact ⟨n, (h _ _).2 hn⟩

/-- Rebuilding a continuous map from its lower graph returns the map. -/
theorem streamMapOfLowerGraph_streamLowerGraph_eq (f : BitStream → BitStream)
    (hf : IsContinuousStreamMap f) :
    streamMapOfLowerGraph (streamLowerGraph f)
      (continuousStreamMap_lowerGraph_isStreamLowerGraph hf.1) = f := by
  apply continuousStreamMap_ext_of_lowerGraph_eq
    (streamMapOfLowerGraph_isContinuousStreamMap
      (continuousStreamMap_lowerGraph_isStreamLowerGraph hf.1)) hf
  intro x y
  change BitStream.finite y ≤ streamMapOfLowerGraph (streamLowerGraph f)
    (continuousStreamMap_lowerGraph_isStreamLowerGraph hf.1) (.finite x) ↔
      BitStream.finite y ≤ f (.finite x)
  rw [streamMapOfLowerGraph_finite_spec]
  rfl

/-- Every lower graph is the lower graph of exactly one continuous stream map. -/
theorem existsUnique_continuousStreamMap_of_isStreamLowerGraph (R : BitString → BitString → Prop)
    (hR : IsStreamLowerGraph R) :
    ∃! f : BitStream → BitStream, IsContinuousStreamMap f ∧
      ∀ x y, streamLowerGraph f x y ↔ R x y := by
  use streamMapOfLowerGraph R hR
  constructor
  · constructor
    · exact streamMapOfLowerGraph_isContinuousStreamMap hR
    · intro x y
      exact streamMapOfLowerGraph_finite_spec hR x y
  · intro g ⟨hg_cont, hg_eq⟩
    symm
    apply continuousStreamMap_ext_of_lowerGraph_eq
      (streamMapOfLowerGraph_isContinuousStreamMap hR) hg_cont
    intro x y
    dsimp [streamLowerGraph]; rw [streamMapOfLowerGraph_finite_spec hR x y]
    exact (hg_eq x y).symm

end Kolmogorov
