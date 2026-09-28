/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import Mathlib.Order.BourbakiWitt
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity

/-!
# Basic bounds for monotone complexity (SUV Theorem 85, parts (a) and (c))

This file records two elementary properties of the monotone complexity `KMOf`:

* monotonicity along the prefix order (`KMOf_mono_of_prefix`);
* the length bound `KM(x) ≤ l(x) + O(1)` for an optimal monotone decompressor
  (`exists_const_KMOf_le_length`), obtained by comparing with the identity
  stream map, which is shown to be a computable stream map
  (`isComputableStreamMap_id`).
-/

namespace Kolmogorov

/-- The identity map on streams is continuous. -/
lemma isContinuousStreamMap_id : IsContinuousStreamMap (id : BitStream → BitStream) := by
  refine ⟨monotone_id, ?_⟩
  intro w y hy
  rw [BitStream.le_iff_forall_finite_le]
  intro u hu
  have hu' : cantorPrefix w u.length = u := (isCantorPrefix_iff_cantorPrefix_eq u w).1 hu
  have := hy u.length
  rwa [hu'] at this

/-- The lower graph of the identity stream map is the prefix relation. -/
lemma streamLowerGraph_id (x y : BitString) :
    streamLowerGraph (id : BitStream → BitStream) x y ↔ y <+: x :=
  Iff.rfl

/-- The identity map on streams is a computable stream map. -/
lemma isComputableStreamMap_id : IsComputableStreamMap (id : BitStream → BitStream) := by
  refine ⟨isContinuousStreamMap_id, ?_⟩
  have hcomp : Computable
      (fun p : BitString × BitString => decide (p.1.take p.2.length = p.2)) := by
    apply Primrec.to_comp
    have h : PrimrecPred (fun p : BitString × BitString => p.1.take p.2.length = p.2) :=
      (Primrec.eq (α := BitString)).comp
        (Primrec.list_take.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))
        Primrec.snd
    rcases h with ⟨_, hp⟩
    exact hp.of_eq (by intro p; congr)
  refine isRE_of_computable_bool _ _ (fun p => ?_) hcomp
  rw [decide_eq_true_iff, streamLowerGraph_id, List.prefix_iff_eq_take, eq_comm]

/-- Monotone complexity is monotone along the prefix order. -/
lemma KMOf_mono_of_prefix (D : BitStream → BitStream) {x y : BitString} (h : x <+: y) :
    KMOf D x ≤ KMOf D y := by
  apply sInf_le_sInf
  rintro l ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  exact le_trans (show BitStream.finite x ≤ BitStream.finite y from h) hp

/-- Each string is produced by itself under the identity decompressor. -/
lemma KMOf_id_le_length (x : BitString) :
    KMOf (id : BitStream → BitStream) x ≤ (x.length : ℕ∞) :=
  KMOf_le_length_of_monotoneProduces (le_refl (BitStream.finite x))

/-- **SUV Theorem 85(c)**: for an optimal monotone decompressor `D` there is a constant `c`
with `KM_D(x) ≤ l(x) + c` for every `x`. -/
theorem exists_const_KMOf_le_length {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℕ, ∀ x : BitString, KMOf D x ≤ (x.length : ℕ∞) + c := by
  obtain ⟨c, hc⟩ := hD.2 _ isComputableStreamMap_id
  exact ⟨c, fun x => le_trans (hc x) (add_le_add (KMOf_id_le_length x) le_rfl)⟩

/-- `KM_D(x) < n` holds exactly when some program shorter than `n` monotonically produces `x`. -/
lemma KMOf_lt_iff (D : BitStream → BitStream) (x : BitString) (n : ℕ∞) :
    KMOf D x < n ↔ ∃ p : BitString, monotoneProduces D p x ∧ (p.length : ℕ∞) < n := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hle : n ≤ KMOf D x := by
      apply le_sInf
      rintro l ⟨p, hp, rfl⟩
      exact hc p hp
    exact absurd h (not_lt.mpr hle)
  · rintro ⟨p, hp, hlt⟩
    exact lt_of_le_of_lt (KMOf_le_length_of_monotoneProduces hp) hlt

/-- **SUV Theorem 85(b)**: monotone complexity is upper semicomputable, i.e. the strict
upper graph `{(x, n) | KM_D(x) < n}` is recursively enumerable for every computable
decompressor `D`. -/
theorem KMOf_isRE_lt {D : BitStream → BitStream} (hD : IsComputableStreamMap D) :
    IsRE (fun q : BitString × ℕ => KMOf D q.1 < (q.2 : ℕ∞)) := by
  have hgraph : IsRE (fun p : BitString × BitString => streamLowerGraph D p.1 p.2) := hD.2
  have hswap : Computable (fun pr : (BitString × ℕ) × BitString => (pr.2, pr.1.1)) :=
    Computable.pair Computable.snd (Computable.fst.comp Computable.fst)
  have hRE1 : IsRE (fun pr : (BitString × ℕ) × BitString =>
      streamLowerGraph D pr.2 pr.1.1) := hgraph.comp_computable hswap
  have hbool : Computable (fun pr : (BitString × ℕ) × BitString =>
      decide (pr.2.length < pr.1.2)) := by
    apply Primrec.to_comp
    have h : PrimrecPred (fun pr : (BitString × ℕ) × BitString => pr.2.length < pr.1.2) :=
      Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)
    rcases h with ⟨_, hp⟩
    exact hp.of_eq (by intro pr; congr)
  have hRE2 : IsRE (fun pr : (BitString × ℕ) × BitString =>
      streamLowerGraph D pr.2 pr.1.1 ∧ pr.2.length < pr.1.2) :=
    IsRE.of_iff (IsRE.and_computable hRE1 hbool) (fun pr => by
      rw [decide_eq_true_iff, and_comm])
  have hex := IsRE.exists_encodable
    (R := fun a : BitString × ℕ => fun b : BitString =>
      streamLowerGraph D b a.1 ∧ b.length < a.2) hRE2
  refine IsRE.of_iff hex (fun q => ?_)
  rw [KMOf_lt_iff]
  constructor
  · rintro ⟨p, hp, hlen⟩
    exact ⟨p, hp, by exact_mod_cast hlen⟩
  · rintro ⟨p, hp, hlen⟩
    exact ⟨p, hp, by exact_mod_cast hlen⟩

/-- Monotone complexity relative to an optimal decompressor is always finite. -/
lemma KMOf_ne_top_of_isOptimal {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) (x : BitString) : KMOf D x ≠ ⊤ := by
  obtain ⟨c, hc⟩ := exists_const_KMOf_le_length hD
  exact ne_top_of_le_natCast_add (hc x)



/-- Composition of continuous stream maps preserves continuity. -/
lemma isContinuousStreamMap_comp {f g : BitStream → BitStream}
    (hf : IsContinuousStreamMap f) (hg : IsContinuousStreamMap g) :
    IsContinuousStreamMap (f ∘ g) := by
  constructor
  · exact hf.1.comp hg.1
  · intro w y hy
    -- hy : ∀ n, f (g (.finite (cantorPrefix w n))) ≤ y
    -- Goal: f (g (.infinite w)) ≤ y
    cases hgw : g (.infinite w) with
    | finite z =>
      -- g(.infinite w) = .finite z
      -- .finite z ≤ g(.infinite w), so by continuity of g there exists k with
      -- .finite z ≤ g(.finite (cantorPrefix w k))
      have hle : BitStream.finite z ≤ g (.infinite w) := le_of_eq hgw.symm
      rw [continuousStreamMap_finite_le_infinite_iff g hg] at hle
      obtain ⟨k, hk⟩ := hle
      -- f(.finite z) ≤ f(g(.finite (cantorPrefix w k))) ≤ y
      rw [Function.comp_apply, hgw]
      exact le_trans (hf.1 hk) (hy k)
    | infinite v =>
      -- g(.infinite w) = .infinite v
      -- By f's continuity: suffices to show ∀ m, f(.finite (cantorPrefix v m)) ≤ y
      rw [Function.comp_apply, hgw]
      apply hf.2
      intro m
      -- .finite (cantorPrefix v m) ≤ .infinite v = g(.infinite w)
      have hle : BitStream.finite (cantorPrefix v m) ≤ g (.infinite w) := by
        rw [hgw]; intro i hi
        simp [cantorPrefix_getElem _ _ _ hi]
      rw [continuousStreamMap_finite_le_infinite_iff g hg] at hle
      obtain ⟨k, hk⟩ := hle
      exact le_trans (hf.1 hk) (hy k)

/-- The lower graph of a composition is the relational composition of the lower graphs. -/
lemma streamLowerGraph_comp_iff {f g : BitStream → BitStream}
    (hf : IsContinuousStreamMap f) (p y : BitString) :
    streamLowerGraph (f ∘ g) p y ↔
      ∃ z : BitString, streamLowerGraph g p z ∧ streamLowerGraph f z y := by
  simp only [streamLowerGraph, Function.comp_apply]
  constructor
  · intro h
    cases hgp : g (.finite p) with
    | finite z =>
      rw [hgp] at h
      exact ⟨z, le_refl _, h⟩
    | infinite v =>
      rw [hgp] at h
      rw [continuousStreamMap_finite_le_infinite_iff f hf] at h
      obtain ⟨m, hm⟩ := h
      refine ⟨cantorPrefix v m, ?_, hm⟩
      intro i hi
      simp [cantorPrefix_getElem _ _ _ hi]
  · rintro ⟨z, hgz, hfz⟩
    exact le_trans hfz (hf.1 hgz)

/-- The lower graph of a composition of computable stream maps is RE. -/
lemma isRE_streamLowerGraph_comp {f g : BitStream → BitStream}
    (hf : IsComputableStreamMap f) (hg : IsComputableStreamMap g) :
    IsRE (fun p : BitString × BitString => streamLowerGraph (f ∘ g) p.1 p.2) := by
  have h_iff := streamLowerGraph_comp_iff (g := g) hf.1
  -- Step 1: Show ((p,y), z) ↦ streamLowerGraph g p z ∧ streamLowerGraph f z y
  -- is RE, using Partrec.bind to combine two RE predicates
  obtain ⟨fg, hfg_partrec, hfg_dom⟩ := hg.2
  obtain ⟨ff, hff_partrec, hff_dom⟩ := hf.2
  -- Build: fun ((p,y), z) ↦ (fg (p, z)).bind (fun _ => ff (z, y))
  -- whose domain is (fg (p,z)).Dom ∧ (ff (z,y)).Dom
  have h_fg_lifted : Partrec (fun q : (BitString × BitString) × BitString =>
      fg (q.1.1, q.2)) := by
    have hc : Computable (fun q : (BitString × BitString) × BitString => (q.1.1, q.2)) :=
      Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
    exact hfg_partrec.comp hc
  have h_ff_lifted : Partrec (fun q : (BitString × BitString) × BitString =>
      ff (q.2, q.1.2)) := by
    have hc : Computable (fun q : (BitString × BitString) × BitString => (q.2, q.1.2)) :=
      Computable.pair Computable.snd (Computable.snd.comp Computable.fst)
    exact hff_partrec.comp hc
  -- Conjunction via bind: Dom(fg(p,z).bind(ff(z,y))) = Dom(fg(p,z)) ∧ Dom(ff(z,y))
  have h_joint_partrec : Partrec (fun q : (BitString × BitString) × BitString =>
      (fg (q.1.1, q.2)).bind (fun _ => ff (q.2, q.1.2))) :=
    h_fg_lifted.bind (h_ff_lifted.comp Computable.fst).to₂
  have h_joint_dom : ∀ q : (BitString × BitString) × BitString,
      ((fg (q.1.1, q.2)).bind (fun _ => ff (q.2, q.1.2))).Dom ↔
        (streamLowerGraph g q.1.1 q.2 ∧ streamLowerGraph f q.2 q.1.2) := by
    intro ⟨⟨p, y⟩, z⟩
    simp only [Part.bind_dom]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hfg_dom (p, z)).mp h1, (hff_dom (z, y)).mp h2⟩
    · rintro ⟨hg_mem, hf_mem⟩
      exact ⟨(hfg_dom (p, z)).mpr hg_mem, (hff_dom (z, y)).mpr hf_mem⟩
  have h_joint_re : IsRE (fun q : (BitString × BitString) × BitString =>
      streamLowerGraph g q.1.1 q.2 ∧ streamLowerGraph f q.2 q.1.2) :=
    ⟨_, h_joint_partrec, h_joint_dom⟩
  -- Step 2: Existentially quantify z using IsRE.exists_encodable
  have h_exists_re : IsRE (fun py : BitString × BitString =>
      ∃ z : BitString, streamLowerGraph g py.1 z ∧ streamLowerGraph f z py.2) :=
    IsRE.exists_encodable h_joint_re
  -- Step 3: Use the iff to conclude
  exact IsRE.of_iff h_exists_re (fun py => (h_iff py.1 py.2).symm)

/-- Composition of computable stream maps is a computable stream map. -/
lemma isComputableStreamMap_comp {f g : BitStream → BitStream}
    (hf : IsComputableStreamMap f) (hg : IsComputableStreamMap g) :
    IsComputableStreamMap (f ∘ g) :=
  ⟨isContinuousStreamMap_comp hf.1 hg.1, isRE_streamLowerGraph_comp hf hg⟩

/-- If `f` is monotone and `streamLowerGraph f x y` and `monotoneProduces D p x`,
then `monotoneProduces (f ∘ D) p y`. -/
lemma monotoneProduces_comp_of_streamLowerGraph {f D : BitStream → BitStream}
    (hf_mono : Monotone f) {p x y : BitString}
    (hfxy : streamLowerGraph f x y) (hDpx : monotoneProduces D p x) :
    monotoneProduces (f ∘ D) p y := by
  change BitStream.finite y ≤ (f ∘ D) (.finite p)
  exact le_trans hfxy (hf_mono hDpx)

/-- **SUV Theorem 85(g)**: composition with a computable stream map increases monotone
complexity by at most a constant. -/
theorem exists_const_KMOf_le_comp {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) :
    ∃ c : ℕ, ∀ x y : BitString, streamLowerGraph f x y → KMOf D y ≤ KMOf D x + c := by
  -- f ∘ D is a computable stream map
  have hfD : IsComputableStreamMap (f ∘ D) := isComputableStreamMap_comp hf hD.1
  -- By optimality of D, there exists c with KMOf D z ≤ KMOf (f ∘ D) z + c for all z
  obtain ⟨c, hc⟩ := hD.2 (f ∘ D) hfD
  use c
  intro x y hfxy
  -- hfxy : streamLowerGraph f x y, i.e., .finite y ≤ f (.finite x)
  -- Every program witnessing KMOf D x also witnesses KMOf (f ∘ D) y
  have hKM : KMOf (f ∘ D) y ≤ KMOf D x := by
    apply sInf_le_sInf
    rintro l ⟨p, hp, rfl⟩
    exact ⟨p, monotoneProduces_comp_of_streamLowerGraph hf.1.1 hfxy hp, rfl⟩
  -- Combine: KMOf D y ≤ KMOf (f ∘ D) y + c ≤ KMOf D x + c
  exact le_trans (hc y) (add_le_add hKM le_rfl)

end Kolmogorov
