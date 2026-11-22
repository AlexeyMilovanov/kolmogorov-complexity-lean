/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.CommonInformation.Counting
import Mathlib.Algebra.Order.Chebyshev
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools

/-!
# Finite Stage Selection

This module formalizes the effective greedy selection of finite sets from uniformly enumerable
bunches. It proves the enumeration of bunches and constructs a separated partial enumeration in
which every input set is retained or has a large intersection with a retained set, following
Lemma 5 and its appendix argument in Muchnik and Romashchenko's paper on relativization stability.
-/

namespace Kolmogorov.Relativization

/-! ## Enumeration of bunches -/

/-- The relation
"some program shorter than `b` maps the condition `x` to `y`" is recursively enumerable. -/
private theorem lemma5_short_program_re (D : Map)
    (hD : Partrec D) :
    IsRE (fun q : ℕ × BitString × BitString =>
      ∃ p : BitString, p.length < q.1 ∧ q.2.2 ∈ D (p, q.2.1)) := by
  have hg := Partrec.graphIsRe D hD
  have hgc : Computable (fun r : (ℕ × BitString × BitString) × BitString =>
      ((r.2, r.1.2.1), r.1.2.2)) :=
    Computable.pair
      (Computable.pair Computable.snd
        (Computable.fst.comp (Computable.snd.comp Computable.fst)))
      (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have h1 := hg.comp_computable hgc
  have hlt : Computable (fun r : (ℕ × BitString × BitString) × BitString =>
      decide (r.2.length < r.1.1)) :=
    (PrimrecRel.comp Primrec.nat_lt (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).decide.to_comp
  have h2 := h1.and_computable hlt
  have h3 : IsRE (fun r : (ℕ × BitString × BitString) × BitString =>
      r.2.length < r.1.1 ∧ r.1.2.2 ∈ D (r.2, r.1.2.1)) :=
    h2.of_iff (fun r => by simp)
  exact IsRE.exists_encodable
    (R := fun (q : ℕ × BitString × BitString) (p : BitString) =>
      p.length < q.1 ∧ q.2.2 ∈ D (p, q.2.1)) h3

/-- For a monotone family of
boolean tests that holds for each member of a finite list at some stage holds for all members
of the list at one common stage. -/
theorem lemma5_common_stage {ι : Type*}
    (f : ι → ℕ → Bool) (hmono : ∀ i s t, s ≤ t → f i s = true → f i t = true) :
    ∀ l : List ι, (∀ i ∈ l, ∃ s, f i s = true) → ∃ s, ∀ i ∈ l, f i s = true := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons a l ih =>
    intro h
    obtain ⟨s₁, hs₁⟩ := h a (by simp)
    obtain ⟨s₂, hs₂⟩ := ih (fun i hi => h i (by simp [hi]))
    refine ⟨max s₁ s₂, ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hmono _ _ _ (le_max_left _ _) hs₁
    · exact hmono _ _ _ (le_max_right _ _) (hs₂ i hi)

/-- A double universal
quantification over a computable list of strings, of a computable boolean test, is computable. -/
private theorem lemma5_computable_all2 {α : Type} [Primcodable α]
    (L : α → List BitString) (hL : Computable L) (h : α → BitString → BitString → Bool)
    (hh : Computable (fun u : (α × BitString) × BitString => h u.1.1 u.1.2 u.2)) :
    Computable (fun a => (L a).all fun x₁ => (L a).all fun x₂ => h a x₁ x₂) := by
  have hall : ∀ {γ : Type} [Primcodable γ] (f : γ → List BitString) (p : γ → BitString → Bool),
      Computable f → Computable₂ p → Computable (fun c => (f c).all (p c)) := by
    intro γ _ f p hf hp
    have hnot : Computable₂ fun (c : γ) (b : BitString) => !p c b :=
      Primrec.not.to_comp.comp hp
    exact (Primrec.not.to_comp.comp (computable_list_any hf hnot)).of_eq fun c => by
      simp [List.all_eq_not_any_not]
  have hinner : Computable₂ (fun (a : α) (x₁ : BitString) => (L a).all fun x₂ => h a x₁ x₂) :=
    hall (fun u : α × BitString => L u.1) (fun u x₂ => h u.1 u.2 x₂)
      (hL.comp Computable.fst) hh
  exact hall L (fun a x₁ => (L a).all fun x₂ => h a x₁ x₂) hL hinner

/-- The set of tuples
`(α, β, γ, w)` such that `w` is the code of a finite set `X` with `2 ^ α` elements, all pairs
`(x₁, x₂) ∈ X²` have short programs (`< β`) giving `x₁` from `x₂`, and all `x ∈ X` have short
programs (`< γ`) giving `x` from the empty condition, is recursively enumerable. -/
private theorem lemma5_certificate_re (D : Map)
    (hD : Partrec D) :
    IsRE (fun q : ℕ × ℕ × ℕ × BitString =>
      finsetListCode (decodeListCode q.2.2.2).toFinset = q.2.2.2 ∧
      (decodeListCode q.2.2.2).toFinset.card = 2 ^ q.1 ∧
      (∀ x₁ ∈ decodeListCode q.2.2.2, ∀ x₂ ∈ decodeListCode q.2.2.2,
        ∃ p : BitString, p.length < q.2.1 ∧ x₁ ∈ D (p, x₂)) ∧
      (∀ x ∈ decodeListCode q.2.2.2,
        ∃ p : BitString, p.length < q.2.2.1 ∧ x ∈ D (p, []))) := by
  obtain ⟨chk, hchk, hmono, hiff⟩ :=
    (lemma5_short_program_re D hD).exists_stageApprox
  let big : (ℕ × ℕ × ℕ × BitString) × ℕ → Bool := fun r =>
    ((decodeListCode r.1.2.2.2).all fun x₁ => (decodeListCode r.1.2.2.2).all fun x₂ =>
        chk (r.1.2.1, x₂, x₁) r.2) &&
      ((decodeListCode r.1.2.2.2).all fun x => chk (r.1.2.2.1, [], x) r.2)
  have hL : Computable (fun r : (ℕ × ℕ × ℕ × BitString) × ℕ => decodeListCode r.1.2.2.2) :=
    decodeListCode_primrec.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hbig : Computable big := by
    have h1 := lemma5_computable_all2
      (fun r : (ℕ × ℕ × ℕ × BitString) × ℕ => decodeListCode r.1.2.2.2) hL
      (fun r x₁ x₂ => chk (r.1.2.1, x₂, x₁) r.2) (by
        exact hchk.comp
          (Computable.pair
            (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp
              Computable.fst))))
            (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)))
          (Computable.snd.comp (Computable.fst.comp Computable.fst)))
    have h2 : Computable (fun r : (ℕ × ℕ × ℕ × BitString) × ℕ =>
        (decodeListCode r.1.2.2.2).all fun x => chk (r.1.2.2.1, [], x) r.2) := by
      have hnot : Computable₂ fun (r : (ℕ × ℕ × ℕ × BitString) × ℕ) (x : BitString) =>
          !chk (r.1.2.2.1, [], x) r.2 := by
        refine Primrec.not.to_comp.comp (hchk.comp
          (Computable.pair
            (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
              (Computable.fst.comp Computable.fst))))
            (Computable.pair (Computable.const []) Computable.snd))
          (Computable.snd.comp (Computable.fst)))
      exact (Primrec.not.to_comp.comp (computable_list_any hL hnot)).of_eq fun r => by
        simp [List.all_eq_not_any_not]
    exact (Primrec.and.to_comp.comp h1 h2).of_eq fun r => rfl
  have hcore : ∀ q : ℕ × ℕ × ℕ × BitString, (∃ s, big (q, s) = true) ↔
      ((∀ x₁ ∈ decodeListCode q.2.2.2, ∀ x₂ ∈ decodeListCode q.2.2.2,
        ∃ p : BitString, p.length < q.2.1 ∧ x₁ ∈ D (p, x₂)) ∧
      (∀ x ∈ decodeListCode q.2.2.2,
        ∃ p : BitString, p.length < q.2.2.1 ∧ x ∈ D (p, []))) := by
    intro q
    constructor
    · rintro ⟨s, hs⟩
      simp only [big, Bool.and_eq_true, List.all_eq_true] at hs
      obtain ⟨hs1, hs2⟩ := hs
      refine ⟨fun x₁ hx₁ x₂ hx₂ => ?_, fun x hx => ?_⟩
      · exact (hiff (q.2.1, x₂, x₁)).2 ⟨s, hs1 x₁ hx₁ x₂ hx₂⟩
      · exact (hiff (q.2.2.1, [], x)).2 ⟨s, hs2 x hx⟩
    · rintro ⟨H1, H2⟩
      obtain ⟨s1, hs1⟩ := lemma5_common_stage
        (fun x₁ s => (decodeListCode q.2.2.2).all fun x₂ => chk (q.2.1, x₂, x₁) s)
        (fun x₁ s t hst h => by
          simp only [List.all_eq_true] at h ⊢
          exact fun x₂ hx₂ => hmono _ _ _ hst (h x₂ hx₂))
        (decodeListCode q.2.2.2) (fun x₁ hx₁ => by
          obtain ⟨s, hs⟩ := lemma5_common_stage
            (fun x₂ s => chk (q.2.1, x₂, x₁) s)
            (fun x₂ s t hst h => hmono _ _ _ hst h) (decodeListCode q.2.2.2)
            (fun x₂ hx₂ => (hiff (q.2.1, x₂, x₁)).1 (H1 x₁ hx₁ x₂ hx₂))
          exact ⟨s, by simpa [List.all_eq_true] using hs⟩)
      obtain ⟨s2, hs2⟩ := lemma5_common_stage
        (fun x s => chk (q.2.2.1, [], x) s)
        (fun x s t hst h => hmono _ _ _ hst h) (decodeListCode q.2.2.2)
        (fun x hx => (hiff (q.2.2.1, [], x)).1 (H2 x hx))
      refine ⟨max s1 s2, ?_⟩
      simp only [big, Bool.and_eq_true, List.all_eq_true]
      refine ⟨fun x₁ hx₁ x₂ hx₂ => ?_, fun x hx => ?_⟩
      · have h := hs1 x₁ hx₁
        simp only [List.all_eq_true] at h
        exact hmono _ _ _ (le_max_left _ _) (h x₂ hx₂)
      · exact hmono _ _ _ (le_max_right _ _) (hs2 x hx)
  have hp : Computable (fun q : ℕ × ℕ × ℕ × BitString =>
      decide (finsetListCode (decodeListCode q.2.2.2).toFinset = q.2.2.2) &&
      decide ((decodeListCode q.2.2.2).toFinset.card = 2 ^ q.1)) := by
    have hw : Primrec (fun q : ℕ × ℕ × ℕ × BitString => q.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hlist : Primrec (fun q : ℕ × ℕ × ℕ × BitString =>
        canonicalFinsetList (decodeListCode q.2.2.2).toFinset) :=
      canonicalFinsetList_toFinset_primrec.comp (decodeListCode_primrec.comp hw)
    have e1 : Primrec (fun q : ℕ × ℕ × ℕ × BitString =>
        decide (finsetListCode (decodeListCode q.2.2.2).toFinset = q.2.2.2)) :=
      (PrimrecRel.comp Primrec.eq (listCode_primrec.comp hlist) hw).decide
    have e2 : Primrec (fun q : ℕ × ℕ × ℕ × BitString =>
        decide ((decodeListCode q.2.2.2).toFinset.card = 2 ^ q.1)) := by
      have hpow : Primrec₂ (fun (a b : ℕ) => a ^ b) :=
        Primrec.nat_iff.mpr Nat.Primrec.pow
      have := (PrimrecRel.comp Primrec.eq (Primrec.list_length.comp hlist)
        (hpow.comp (Primrec.const 2) Primrec.fst)).decide
      exact this.of_eq fun q => by simp
    exact (Primrec.and.comp e1 e2).to_comp
  have hRE : IsRE (fun q : ℕ × ℕ × ℕ × BitString => ∃ s, big (q, s) = true) :=
    IsRE.exists_encodable (R := fun q s => big (q, s) = true)
      (isRE_of_computable_bool (fun r : (ℕ × ℕ × ℕ × BitString) × ℕ => big r = true) big
        (fun _ => Iff.rfl) hbig)
  refine (hRE.and_computable hp).of_iff (fun q => ?_)
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hcore q]
  tauto

/-- Bunches can be enumerated uniformly, as in Lemma 5. A partial
recursive `E` outputs only codes `finsetListCode X` of `(α, β, γ)`-bunches `X`, and every
`(α, β, γ)`-bunch has its code output at some index.  (Membership in a bunch is
recursively enumerable, uniformly in `(α, β, γ, X)`, since `K(y | x) < β` and `K(x) < γ` are
witnessed by short programs of the partial recursive `D`; dovetail over all finite sets.) -/
theorem lemma5_enumerate_bunches (D : Map) (hD : isOptimalConditional D) :
    ∃ E : ℕ × ℕ × ℕ × ℕ →. BitString, Partrec E ∧
      (∀ α β γ i s, s ∈ E (α, β, γ, i) →
        ∃ X : Finset BitString, s = finsetListCode X ∧ IsBunch D α β γ X) ∧
      (∀ α β γ (X : Finset BitString), IsBunch D α β γ X →
        ∃ i, finsetListCode X ∈ E (α, β, γ, i)) := by
  obtain ⟨f, hf, hdom⟩ := lemma5_certificate_re D hD.1
  refine ⟨fun q => (↑(Encodable.decode (α := BitString) q.2.2.2) : Part BitString).bind
    (fun w => (f (q.1, q.2.1, q.2.2.1, w)).map (fun _ => w)), ?_, ?_, ?_⟩
  · refine Partrec.bind (Computable.ofOption
      (Computable.decode.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))) ?_
    refine Partrec.map (hf.comp ?_) ?_
    · exact Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
          (Computable.pair
            (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
            Computable.snd))
    · exact (Computable.snd.comp Computable.fst).to₂
  · intro α β γ i s hs
    obtain ⟨w, hw, u, hu, rfl⟩ : ∃ w ∈ (↑(Encodable.decode (α := BitString) i) : Part BitString),
        ∃ u ∈ f (α, β, γ, w), w = s := by
      simpa [Part.mem_bind_iff, Part.mem_map_iff] using hs
    have hdomw : (f (α, β, γ, w)).Dom := Part.dom_iff_mem.mpr ⟨u, hu⟩
    obtain ⟨hcode, hcard, hcond, hplain⟩ := (hdom (α, β, γ, w)).mp hdomw
    refine ⟨(decodeListCode w).toFinset, hcode.symm, hcard, ?_, ?_⟩
    · intro x₁ hx₁ x₂ hx₂
      obtain ⟨p, hpLen, hpOut⟩ := hcond x₁ (by simpa using hx₁) x₂ (by simpa using hx₂)
      have hK := (condK_le_iff D x₁ x₂ p.length).2 ⟨p, le_rfl, hpOut⟩
      have hNat : natCondK D x₁ x₂ ≤ p.length := ENat.toNat_le_of_le_natCast hK
      exact lt_of_le_of_lt hNat hpLen
    · intro x hx
      obtain ⟨p, hpLen, hpOut⟩ := hplain x (by simpa using hx)
      have hK := (condK_le_iff D x [] p.length).2 ⟨p, le_rfl, hpOut⟩
      have hNat : natK D x ≤ p.length := ENat.toNat_le_of_le_natCast hK
      exact lt_of_le_of_lt hNat hpLen
  · intro α β γ X hX
    obtain ⟨hcard, hcond, hplain⟩ := hX
    have hcond' : ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∃ p : BitString, p.length < β ∧ x₁ ∈ D (p, x₂) := by
      intro x₁ hx₁ x₂ hx₂
      have hlt : natCondK D x₁ x₂ < β := hcond x₁ hx₁ x₂ hx₂
      have hfinite : condK D x₁ x₂ ≠ ⊤ := by
        obtain ⟨cCond, hcCond⟩ := condK_le_plainK D hD
        obtain ⟨cLen, hcLen⟩ := plainK_le_length D hD
        apply ne_top_of_le_natCast_add
        calc condK D x₁ x₂ ≤ plainK D x₁ + (cCond : ℕ∞) := hcCond x₁ x₂
          _ ≤ (x₁.length : ℕ∞) + (cLen : ℕ∞) + (cCond : ℕ∞) := by
            gcongr
            exact hcLen x₁
      have hToNat := ENat.natCast_toNat hfinite
      have hNatLe : natCondK D x₁ x₂ ≤ β - 1 := by omega
      have hKLe : condK D x₁ x₂ ≤ ((β - 1 : ℕ) : ℕ∞) := by
        rw [← hToNat]
        exact_mod_cast hNatLe
      obtain ⟨p, hpLen, hpOut⟩ := (condK_le_iff D x₁ x₂ (β - 1)).1 hKLe
      have hβ : 0 < β := by omega
      have hpLen' : p.length ≤ β - 1 := by simpa [programLength] using hpLen
      exact ⟨p, by omega, hpOut⟩
    have hplain' : ∀ x ∈ X, ∃ p : BitString, p.length < γ ∧ x ∈ D (p, []) := by
      intro x hx
      have hlt : natK D x < γ := hplain x hx
      have hfinite : plainK D x ≠ ⊤ := by
        obtain ⟨cLen, hcLen⟩ := plainK_le_length D hD
        apply ne_top_of_le_natCast_add
        exact hcLen x
      have hToNat := ENat.natCast_toNat hfinite
      have hNatLe : natK D x ≤ γ - 1 := by omega
      have hKLe : plainK D x ≤ ((γ - 1 : ℕ) : ℕ∞) := by
        rw [← hToNat]
        exact_mod_cast hNatLe
      obtain ⟨p, hpLen, hpOut⟩ := (condK_le_iff D x [] (γ - 1)).1 hKLe
      have hγ : 0 < γ := by omega
      have hpLen' : p.length ≤ γ - 1 := by simpa [programLength] using hpLen
      exact ⟨p, by omega, hpOut⟩
    have hcert : finsetListCode (decodeListCode (finsetListCode X)).toFinset =
          finsetListCode X ∧
        (decodeListCode (finsetListCode X)).toFinset.card = 2 ^ α ∧
        (∀ x₁ ∈ decodeListCode (finsetListCode X), ∀ x₂ ∈ decodeListCode (finsetListCode X),
          ∃ p : BitString, p.length < β ∧ x₁ ∈ D (p, x₂)) ∧
        (∀ x ∈ decodeListCode (finsetListCode X),
          ∃ p : BitString, p.length < γ ∧ x ∈ D (p, [])) := by
      have hdl : decodeListCode (finsetListCode X) = canonicalFinsetList X :=
        decodeListCode_listCode _
      rw [hdl, canonicalFinsetList_toFinset]
      refine ⟨rfl, hcard, fun x₁ hx₁ x₂ hx₂ => hcond' x₁ (by simpa using hx₁) x₂
        (by simpa using hx₂), fun x hx => hplain' x (by simpa using hx)⟩
    have hd : (f (α, β, γ, finsetListCode X)).Dom := (hdom (α, β, γ, finsetListCode X)).mpr hcert
    refine ⟨Encodable.encode (finsetListCode X), ?_⟩
    simp only [Part.mem_bind_iff, Part.mem_map_iff]
    exact ⟨finsetListCode X, by simp, (f (α, β, γ, finsetListCode X)).get hd,
      Part.get_mem hd, rfl⟩

private def lemma5_finite_stages_overlapCount
    (l₁ l₂ : List BitString) : ℕ :=
  (canonicalFinsetList l₁.toFinset).countP (fun s => decide (s ∈ l₂))

private def lemma5_finite_stages_candidate
    (c : Nat.Partrec.Code) (p : ℕ × ℕ × ℕ) (k : ℕ) : Option (List BitString) :=
  (Nat.Partrec.Code.evaln (k.unpair.2 + 1) c
    (Encodable.encode (p.1, p.2.1, p.2.2, k.unpair.1))).bind fun n =>
      (Encodable.decode (α := BitString) n).map decodeListCode

private def lemma5_finite_stages_accepts
    (p : ℕ × ℕ × ℕ) (c : ℕ) (l : List BitString) (L : List (List BitString)) : Bool :=
  L.all fun l' => decide
    (lemma5_finite_stages_overlapCount
      l l' * 2 ^ (p.2.1 + c) < 2 ^ (2 * p.1))

private def lemma5_finite_stages_stageStep
    (code : Nat.Partrec.Code) (c : ℕ) (p : (ℕ × ℕ × ℕ) × ℕ)
    (L : List (List BitString)) : List (List BitString) :=
  match lemma5_finite_stages_candidate
      code p.1 p.2 with
  | none => L
  | some l =>
    if lemma5_finite_stages_accepts
        p.1 c l L then L ++ [l] else L

private def lemma5_finite_stages_stages
    (code : Nat.Partrec.Code) (c : ℕ) (p : ℕ × ℕ × ℕ) (n : ℕ) : List (List BitString) :=
  Nat.rec [] (fun k L =>
    lemma5_finite_stages_stageStep
      code c (p, k) L) n

private theorem lemma5_finite_stages_overlapCount_eq (l₁ l₂ : List BitString) :
    lemma5_finite_stages_overlapCount l₁ l₂
        = (l₁.toFinset ∩ l₂.toFinset).card := by
  unfold lemma5_finite_stages_overlapCount
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((canonicalFinsetList_nodup _).filter _)]
  congr 1
  ext s
  simp

private theorem lemma5_finite_stages_overlapCount_primrec :
    Primrec (fun q : List BitString × List BitString => lemma5_finite_stages_overlapCount q.1 q.2)
        := by
  have hmem : PrimrecRel (fun (l : List BitString) s => s ∈ l) :=
    PrimrecRel.of_eq (Primrec.eq.exists_mem_list) (fun l s => by simp)
  exact list_countP_primrec (canonicalFinsetList_toFinset_primrec.comp Primrec.fst)
    ((hmem.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).decide)

private theorem lemma5_finite_stages_candidate_computable (code : Nat.Partrec.Code) :
    Computable (fun q : (ℕ × ℕ × ℕ) × ℕ => lemma5_finite_stages_candidate code q.1 q.2) := by
  have htime : Computable (fun q : (ℕ × ℕ × ℕ) × ℕ => q.2.unpair.2 + 1) :=
    (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  have hargs : Computable (fun q : (ℕ × ℕ × ℕ) × ℕ =>
      (q.1.1, q.1.2.1, q.1.2.2, q.2.unpair.1)) :=
    Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.pair (Computable.snd.comp (Computable.snd.comp Computable.fst))
          (Computable.fst.comp (Computable.unpair.comp Computable.snd))))
  have hraw := (evalnCoreComputable code).comp
    (Computable.pair htime (Computable.encode.comp hargs))
  have hdecode : Computable₂ (fun (_ : (ℕ × ℕ × ℕ) × ℕ) (n : ℕ) =>
      (Encodable.decode (α := BitString) n).map decodeListCode) :=
    (Computable.option_map (Computable.decode.comp Computable.snd)
      (decodeListCode_primrec.to_comp.comp Computable.snd).to₂).to₂
  exact Computable.option_bind hraw hdecode

private theorem lemma5_finite_stages_accepts_primrec (c : ℕ) :
    Primrec (fun q : ((ℕ × ℕ × ℕ) × List BitString) × List (List BitString) =>
      lemma5_finite_stages_accepts q.1.1 c
          q.1.2 q.2) := by
  have hpow : Primrec₂ (fun (a b : ℕ) => a ^ b) :=
    Primrec.nat_iff.mpr Nat.Primrec.pow
  apply list_all_primrec Primrec.snd
  have hp : Primrec (fun q : (((ℕ × ℕ × ℕ) × List BitString) ×
      List (List BitString)) × List BitString => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hl : Primrec (fun q : (((ℕ × ℕ × ℕ) × List BitString) ×
      List (List BitString)) × List BitString => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  exact (PrimrecRel.comp Primrec.nat_lt
    (Primrec.nat_mul.comp (lemma5_finite_stages_overlapCount_primrec.comp (Primrec.pair hl
        Primrec.snd))
      (hpow.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp hp)) (Primrec.const c))))
    (hpow.comp (Primrec.const 2)
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp hp)))).decide

private theorem lemma5_finite_stages_stageStep_computable (code : Nat.Partrec.Code) (c : ℕ) :
    Computable (fun q : ((ℕ × ℕ × ℕ) × ℕ) × List (List BitString) =>
      lemma5_finite_stages_stageStep code c
          q.1 q.2) := by
  have hc : Computable (fun q : ((ℕ × ℕ × ℕ) × ℕ) × List (List BitString) =>
      lemma5_finite_stages_candidate code q.1.1 q.1.2) :=
    ((lemma5_finite_stages_candidate_computable code).comp Computable.fst).of_eq fun q => rfl
  have hsome : Computable₂ (fun (q : ((ℕ × ℕ × ℕ) × ℕ) × List (List BitString))
      (l : List BitString) =>
      if lemma5_finite_stages_accepts q.1.1
          c l q.2 then q.2 ++ [l] else q.2) := by
    have hargs : Computable (fun r : (((ℕ × ℕ × ℕ) × ℕ) × List (List BitString)) ×
        List BitString => ((r.1.1.1, r.2), r.1.2)) :=
      Computable.pair
        (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd)
        (Computable.snd.comp Computable.fst)
    have ha : Computable (fun r : (((ℕ × ℕ × ℕ) × ℕ) × List (List BitString)) ×
        List BitString => lemma5_finite_stages_accepts r.1.1.1 c r.2 r.1.2) :=
      ((lemma5_finite_stages_accepts_primrec c).to_comp.comp hargs).of_eq fun r => rfl
    have happ : Computable (fun r : (((ℕ × ℕ × ℕ) × ℕ) × List (List BitString)) ×
        List BitString => r.1.2 ++ [r.2]) :=
      Primrec.list_append.to_comp.comp (Computable.snd.comp Computable.fst)
        (Computable.list_cons.comp Computable.snd (Computable.const []))
    have hif : Computable (fun r : (((ℕ × ℕ × ℕ) × ℕ) × List (List BitString)) ×
        List BitString =>
        if lemma5_finite_stages_accepts r.1.1.1 c r.2 r.1.2 then r.1.2 ++ [r.2] else r.1.2) :=
      (Computable.cond ha happ (Computable.snd.comp Computable.fst)).of_eq fun r => by
        cases h : lemma5_finite_stages_accepts r.1.1.1 c r.2 r.1.2 <;> simp
    exact hif.to₂
  exact (Computable.option_casesOn hc Computable.snd hsome).of_eq fun q => by
    unfold lemma5_finite_stages_stageStep
    cases lemma5_finite_stages_candidate code q.1.1 q.1.2 <;> rfl

/-- Bounded
evaluation and the finite greedy update are primitive recursive, so the stage recursion is
computable. -/
private theorem lemma5_stages_computable
    (code : Nat.Partrec.Code) (c : ℕ) :
    Computable (fun q : (ℕ × ℕ × ℕ) × ℕ =>
      lemma5_finite_stages_stages
        code c q.1 q.2) := by
  have hargs : Computable (fun q : ((ℕ × ℕ × ℕ) × ℕ) ×
      (ℕ × List (List BitString)) => ((q.1.1, q.2.1), q.2.2)) :=
    Computable.pair
      (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)) (Computable.snd.comp Computable.snd)
  have hstep : Computable₂ (fun (q : (ℕ × ℕ × ℕ) × ℕ)
      (u : ℕ × List (List BitString)) => lemma5_finite_stages_stageStep code c (q.1, u.1) u.2) :=
    ((lemma5_finite_stages_stageStep_computable code c).comp hargs).to₂
  exact Computable.nat_rec Computable.snd (Computable.const []) hstep

/-- One greedy
update either leaves the current list intact or appends one candidate. -/
private theorem lemma5_step_cases
    (code : Nat.Partrec.Code) (c : ℕ) (p : (ℕ × ℕ × ℕ) × ℕ)
    (L : List (List BitString)) :
    lemma5_finite_stages_stageStep
        code c p L = L ∨
      ∃ l, lemma5_finite_stages_stageStep
        code c p L = L ++ [l] := by
  unfold lemma5_finite_stages_stageStep
  cases h : lemma5_finite_stages_candidate
      code p.1 p.2 with
  | none => simp
  | some l =>
    cases ha : lemma5_finite_stages_accepts
        p.1 c l L <;> simp [ha]

/-- A single stage
cannot shorten the retained list. -/
private theorem lemma5_finite_stages_step_length
    (code : Nat.Partrec.Code) (c : ℕ) (p : (ℕ × ℕ × ℕ) × ℕ)
    (L : List (List BitString)) :
    L.length ≤
      (lemma5_finite_stages_stageStep
        code c p L).length := by
  rcases lemma5_step_cases
      code c p L with h | ⟨l, h⟩
  · rw [h]
  · rw [h]
    simp

/-- Appending a
candidate preserves all earlier positions. -/
private theorem lemma5_finite_stages_step_get
    (code : Nat.Partrec.Code) (c : ℕ) (p : (ℕ × ℕ × ℕ) × ℕ)
    (L : List (List BitString)) (i : ℕ) (hi : i < L.length) :
    (lemma5_finite_stages_stageStep
      code c p L)[i]? = L[i]? := by
  rcases lemma5_step_cases
      code c p L with h | ⟨l, h⟩
  · rw [h]
  · rw [h]
    exact List.getElem?_append_left hi

/-- Induction over
the stage number gives monotonicity of stage lengths. -/
private theorem lemma5_stage_length
    (code : Nat.Partrec.Code) (c : ℕ) (p : ℕ × ℕ × ℕ) :
    ∀ m n, m ≤ n →
      (lemma5_finite_stages_stages
        code c p m).length ≤
      (lemma5_finite_stages_stages
        code c p n).length := by
  intro m n hmn
  induction n with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => omega
  | succ n ih =>
    by_cases hm : m ≤ n
    · have hrec := ih hm
      change (lemma5_finite_stages_stages
          code c p m).length ≤
        (lemma5_finite_stages_stageStep
          code c (p, n)
          (lemma5_finite_stages_stages
            code c p n)).length
      exact hrec.trans (lemma5_finite_stages_step_length
        code c (p, n) _)
    · have hm' : m = n + 1 := by omega
      subst m
      exact Nat.le_refl _

/-- Induction over
the stage number shows that an existing position never changes. -/
private theorem lemma5_stage_stable
    (code : Nat.Partrec.Code) (c : ℕ) (p : ℕ × ℕ × ℕ) :
    ∀ m n i, m ≤ n →
      i < (lemma5_finite_stages_stages
        code c p m).length →
      (lemma5_finite_stages_stages
        code c p n)[i]? =
      (lemma5_finite_stages_stages
        code c p m)[i]? := by
  intro m n i hmn hi
  induction n with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => omega
  | succ n ih =>
    by_cases hm : m ≤ n
    · have hrec := ih hm
      have hlen := lemma5_stage_length
        code c p m n hm
      change (lemma5_finite_stages_stageStep
          code c (p, n)
          (lemma5_finite_stages_stages
            code c p n))[i]? = _
      rw [lemma5_finite_stages_step_get
        code c (p, n) _ i (lt_of_lt_of_le hi hlen)]
      exact hrec
    · have hm' : m = n + 1 := by omega
      subst m
      rfl

/-- Combine the
length and position induction facts into the two stage monotonicity clauses. -/
private theorem lemma5_stage_monotone
    (code : Nat.Partrec.Code) (c : ℕ) :
    (∀ α β γ m n, m ≤ n →
      (lemma5_finite_stages_stages
        code c (α, β, γ) m).length ≤
      (lemma5_finite_stages_stages
        code c (α, β, γ) n).length) ∧
    (∀ α β γ m n i, m ≤ n →
      i < (lemma5_finite_stages_stages
        code c (α, β, γ) m).length →
      (lemma5_finite_stages_stages
        code c (α, β, γ) n)[i]? =
      (lemma5_finite_stages_stages
        code c (α, β, γ) m)[i]?) := by
  constructor
  · intro α β γ m n hmn
    exact lemma5_stage_length
      code c (α, β, γ) m n hmn
  · intro α β γ m n i hmn hi
    exact lemma5_stage_stable
      code c (α, β, γ) m n i hmn hi

/-- A successful
bounded evaluation is an actual input output, hence decodes to
its canonical finite-set list. The code-soundness hypothesis is in the direction from code to E. -/
private theorem lemma5_candidate_sound
    (P : ℕ → ℕ → ℕ → Finset BitString → Prop)
    (E : ℕ × ℕ × ℕ × ℕ →. BitString)
    (hSound : ∀ α β γ i s, s ∈ E (α, β, γ, i) →
      ∃ X : Finset BitString, s = finsetListCode X ∧ P α β γ X)
    (code : Nat.Partrec.Code)
    (hInput : ∀ α β γ i v, v ∈ code.eval (Encodable.encode (α, β, γ, i)) →
      ∃ s ∈ E (α, β, γ, i), v = Encodable.encode s)
    (p : ℕ × ℕ × ℕ) (k : ℕ) (l : List BitString)
    (hl : lemma5_finite_stages_candidate
        code p k = some l) :
    ∃ X : Finset BitString, l = canonicalFinsetList X ∧ P p.1 p.2.1 p.2.2 X := by
  unfold lemma5_finite_stages_candidate at hl
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hl
  obtain ⟨v, hv, s, hs, hsl⟩ := hl
  obtain ⟨s', hs', hvs⟩ := hInput p.1 p.2.1 p.2.2 k.unpair.1 v
    (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv))
  have hss : s' = s := by simpa [hvs] using hs
  subst s'
  obtain ⟨X, hX, hP⟩ := hSound p.1 p.2.1 p.2.2 k.unpair.1 s hs'
  refine ⟨X, ?_, hP⟩
  rw [← hsl, hX]
  exact decodeListCode_listCode _

/-- Induction on
the finite stage shows that each retained list codes a sound input set, remains in canonical list
form, and is separated from every other retained entry. -/
private theorem lemma5_stage_invariants
    (P : ℕ → ℕ → ℕ → Finset BitString → Prop)
    (E : ℕ × ℕ × ℕ × ℕ →. BitString)
    (hSound : ∀ α β γ i s, s ∈ E (α, β, γ, i) →
      ∃ X : Finset BitString, s = finsetListCode X ∧ P α β γ X)
    (code : Nat.Partrec.Code) (c : ℕ)
    (hInput : ∀ α β γ i v, v ∈ code.eval (Encodable.encode (α, β, γ, i)) →
      ∃ s ∈ E (α, β, γ, i), v = Encodable.encode s) :
    (∀ α β γ n (l : List BitString),
      l ∈ lemma5_finite_stages_stages
        code c (α, β, γ) n → P α β γ l.toFinset) ∧
    (∀ α β γ n (l : List BitString),
      l ∈ lemma5_finite_stages_stages
        code c (α, β, γ) n → l = canonicalFinsetList l.toFinset) ∧
    (∀ α β γ n (i j : ℕ) (l₁ l₂ : List BitString), i ≠ j →
      (lemma5_finite_stages_stages
        code c (α, β, γ) n)[i]? = some l₁ →
      (lemma5_finite_stages_stages
        code c (α, β, γ) n)[j]? = some l₂ →
      (l₁.toFinset ∩ l₂.toFinset).card * 2 ^ (β + c) < 2 ^ (2 * α)) := by
  have hInv : ∀ (p : ℕ × ℕ × ℕ) n,
      (∀ l ∈ lemma5_finite_stages_stages
          code c p n, P p.1 p.2.1 p.2.2 l.toFinset) ∧
      (∀ l ∈ lemma5_finite_stages_stages
          code c p n, l = canonicalFinsetList l.toFinset) ∧
      (lemma5_finite_stages_stages code c p
          n).Pairwise (fun l₁ l₂ =>
        (l₁.toFinset ∩ l₂.toFinset).card * 2 ^ (p.2.1 + c) < 2 ^ (2 * p.1)) := by
    intro p n
    induction n with
    | zero => simp [lemma5_finite_stages_stages]
    | succ n ih =>
      change (∀ l ∈ lemma5_finite_stages_stageStep code c (p, n) (lemma5_finite_stages_stages code c
          p n), _) ∧
        (∀ l ∈ lemma5_finite_stages_stageStep code c (p, n) (lemma5_finite_stages_stages code c p
            n), _) ∧
        (lemma5_finite_stages_stageStep code c (p, n) (lemma5_finite_stages_stages code c p
            n)).Pairwise _
      unfold lemma5_finite_stages_stageStep
      cases hc : lemma5_finite_stages_candidate code p n with
      | none => simpa using ih
      | some l =>
        obtain ⟨X, hX, hPX⟩ := lemma5_candidate_sound P E hSound code hInput p n l hc
        by_cases ha : lemma5_finite_stages_accepts p c l (lemma5_finite_stages_stages code c p n) =
            true
        · simp only [ha, ↓reduceIte]
          have hlP : P p.1 p.2.1 p.2.2 l.toFinset := by simpa [hX] using hPX
          have hlCanon : l = canonicalFinsetList l.toFinset := by simp [hX]
          refine ⟨?_, ?_, ?_⟩
          · intro l' hl'
            rcases List.mem_append.mp hl' with hold | hnew
            · exact ih.1 l' hold
            · simpa only [List.mem_singleton.mp hnew] using hlP
          · intro l' hl'
            rcases List.mem_append.mp hl' with hold | hnew
            · exact ih.2.1 l' hold
            · simpa only [List.mem_singleton.mp hnew] using hlCanon
          · rw [List.pairwise_append]
            refine ⟨ih.2.2, by simp, ?_⟩
            intro l' hl' l'' hl''
            have heq : l'' = l := List.mem_singleton.mp hl''
            subst l''
            have htest := List.all_eq_true.mp ha l' hl'
            have htest' : (l.toFinset ∩ l'.toFinset).card * 2 ^ (p.2.1 + c) <
                2 ^ (2 * p.1) := by
              simpa [lemma5_finite_stages_overlapCount_eq] using htest
            simpa only [Finset.inter_comm] using htest'
        · simp only [ha]
          exact ih
  refine ⟨?_, ?_, ?_⟩
  · intro α β γ n l hl
    exact (hInv (α, β, γ) n).1 l hl
  · intro α β γ n l hl
    exact (hInv (α, β, γ) n).2.1 l hl
  · intro α β γ n i j l₁ l₂ hij hi hj
    obtain ⟨hi', hiEq⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', hjEq⟩ := List.getElem?_eq_some_iff.mp hj
    have hpw := (hInv (α, β, γ) n).2.2
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · simpa only [hiEq, hjEq] using hpw.rel_getElem_of_lt hi' hj' hij'
    · have h := hpw.rel_getElem_of_lt hj' hi' hji'
      simpa only [hiEq, hjEq, Finset.inter_comm] using h

/-- Process the
dovetailed evaluation stage at which a given input output appears; the candidate is then retained
or fails a separation check against an already retained entry. -/
private theorem lemma5_eventual_decision
    (E : ℕ × ℕ × ℕ × ℕ →. BitString)
    (code : Nat.Partrec.Code) (c : ℕ)
    (hOutput : ∀ α β γ i s, s ∈ E (α, β, γ, i) →
      Encodable.encode s ∈ code.eval (Encodable.encode (α, β, γ, i))) :
    ∀ α β γ i (X : Finset BitString), finsetListCode X ∈ E (α, β, γ, i) →
      ∃ n,
        (∃ l : List BitString,
          l ∈ lemma5_finite_stages_stages
            code c (α, β, γ) n ∧ X = l.toFinset) ∨
        (∃ l : List BitString,
          l ∈ lemma5_finite_stages_stages
            code c (α, β, γ) n ∧
            2 ^ (2 * α) ≤ (X ∩ l.toFinset).card * 2 ^ (β + c)) := by
  intro α β γ i X hX
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hOutput α β γ i _ hX)
  have ht' := Nat.Partrec.Code.evaln_mono (Nat.le_succ t) ht
  let k := Nat.pair i t
  have hc : lemma5_finite_stages_candidate
      code (α, β, γ) k = some (canonicalFinsetList X) := by
    unfold lemma5_finite_stages_candidate
    have heval := Option.mem_def.mp ht'
    simp only [k, Nat.unpair_pair, heval, Option.bind_some, Encodable.encodek,
      Option.map_some, finsetListCode, decodeListCode_listCode]
  let L := lemma5_finite_stages_stages code
      c (α, β, γ) k
  by_cases ha :
      lemma5_finite_stages_accepts (α, β,
      γ) c (canonicalFinsetList X) L = true
  · refine ⟨k + 1, Or.inl ⟨canonicalFinsetList X, ?_, by simp⟩⟩
    change canonicalFinsetList X ∈ lemma5_finite_stages_stageStep code c ((α, β, γ), k) L
    simp [lemma5_finite_stages_stageStep, hc, ha]
  · have hreject : ∃ l ∈ L,
        2 ^ (2 * α) ≤ (X ∩ l.toFinset).card * 2 ^ (β + c) := by
      by_contra h
      apply ha
      apply List.all_eq_true.mpr
      intro l hl
      apply decide_eq_true
      rw [lemma5_finite_stages_overlapCount_eq, canonicalFinsetList_toFinset]
      exact Nat.lt_of_not_ge (fun hle => h ⟨l, hl, hle⟩)
    obtain ⟨l, hl, hlarge⟩ := hreject
    exact ⟨k, Or.inr ⟨l, hl, hlarge⟩⟩


/-- Dovetail the input enumeration and
build finite stages of the greedy list. Each stage extends the previous one, and every input
output is eventually retained or rejected by a retained set. -/
private theorem lemma5_finite_stages
    (P : ℕ → ℕ → ℕ → Finset BitString → Prop)
    (E : ℕ × ℕ × ℕ × ℕ →. BitString) (hE : Partrec E)
    (hSound : ∀ α β γ i s, s ∈ E (α, β, γ, i) →
      ∃ X : Finset BitString, s = finsetListCode X ∧ P α β γ X)
    (c : ℕ) :
    ∃ L : ℕ × ℕ × ℕ × ℕ → List (List BitString),
      Computable L ∧
      (∀ α β γ m n, m ≤ n →
        (L (α, β, γ, m)).length ≤ (L (α, β, γ, n)).length) ∧
      (∀ α β γ m n i, m ≤ n → i < (L (α, β, γ, m)).length →
        (L (α, β, γ, n))[i]? = (L (α, β, γ, m))[i]?) ∧
      (∀ α β γ n (l : List BitString), l ∈ L (α, β, γ, n) →
        P α β γ l.toFinset) ∧
      (∀ α β γ n (i j : ℕ) (l₁ l₂ : List BitString), i ≠ j →
        (L (α, β, γ, n))[i]? = some l₁ → (L (α, β, γ, n))[j]? = some l₂ →
        (l₁.toFinset ∩ l₂.toFinset).card * 2 ^ (β + c) < 2 ^ (2 * α)) ∧
      (∀ α β γ i (X : Finset BitString), finsetListCode X ∈ E (α, β, γ, i) →
        ∃ n,
          (∃ l : List BitString, l ∈ L (α, β, γ, n) ∧ X = l.toFinset) ∨
          (∃ l : List BitString, l ∈ L (α, β, γ, n) ∧
            2 ^ (2 * α) ≤ (X ∩ l.toFinset).card * 2 ^ (β + c))) := by
  classical
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hE
  let L : ℕ × ℕ × ℕ × ℕ → List (List BitString) := fun q =>
    lemma5_finite_stages_stages
      code c (q.1, q.2.1, q.2.2.1) q.2.2.2
  have hL : Computable L := by
    have hparams : Computable (fun q : ℕ × ℕ × ℕ × ℕ =>
        (q.1, q.2.1, q.2.2.1)) :=
      Computable.pair Computable.fst (Computable.pair
        (Computable.fst.comp Computable.snd)
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    have hargs : Computable (fun q : ℕ × ℕ × ℕ × ℕ =>
        ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
      Computable.pair hparams (Computable.snd.comp (Computable.snd.comp Computable.snd))
    exact ((lemma5_stages_computable
      code c).comp hargs).of_eq fun q => rfl
  have hOutput : ∀ α β γ i s, s ∈ E (α, β, γ, i) →
      Encodable.encode s ∈ code.eval (Encodable.encode (α, β, γ, i)) := by
    intro α β γ i s hs
    rw [hcode]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    exact Part.mem_map_iff Encodable.encode |>.mpr ⟨s, hs, rfl⟩
  obtain ⟨hStageP, hCanonical, hStageSeparated⟩ :=
    lemma5_stage_invariants
      P E hSound code c (by
        intro α β γ i v hv
        rw [hcode] at hv
        simp only [Encodable.encodek, Part.coe_some, Part.bind_some] at hv
        obtain ⟨s, hs, hvs⟩ := Part.mem_map_iff Encodable.encode |>.mp hv
        exact ⟨s, hs, hvs.symm⟩)
  have hMonotone :=
    lemma5_stage_monotone
      code c
  have hDecision :=
    lemma5_eventual_decision
      E code c hOutput
  refine ⟨L, hL, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β γ m n hmn
    exact hMonotone.1 α β γ m n hmn
  · intro α β γ m n i hmn hi
    exact hMonotone.2 α β γ m n i hmn hi
  · intro α β γ n l hl
    exact hStageP α β γ n l hl
  · intro α β γ n i j l₁ l₂ hij hi hj
    exact hStageSeparated α β γ n i j l₁ l₂ hij hi hj
  · intro α β γ i X hX
    exact hDecision α β γ i X hX

/-- Turn a computable sequence of
finite lists with stable positions into a partial recursive stream of their entries. -/
private theorem lemma5_stream_from_stages
    (L : ℕ × ℕ × ℕ × ℕ → List (List BitString))
    (hL : Computable L)
    (hStable : ∀ α β γ m n i, m ≤ n → i < (L (α, β, γ, m)).length →
      (L (α, β, γ, n))[i]? = (L (α, β, γ, m))[i]?) :
    ∃ F : ℕ × ℕ × ℕ × ℕ →. BitString,
      ∃ U : ℕ → ℕ → ℕ → ℕ → Finset BitString,
        Partrec F ∧
        (∀ α β γ i, (F (α, β, γ, i)).Dom ↔
          ∃ n, i < (L (α, β, γ, n)).length) ∧
        (∀ α β γ i, (F (α, β, γ, i)).Dom →
          ∃ n, ∃ l : List BitString, i < (L (α, β, γ, n)).length ∧
            (L (α, β, γ, n))[i]? = some l ∧ U α β γ i = l.toFinset) ∧
        (∀ α β γ i, (F (α, β, γ, i)).Dom →
          ∀ s, s ∈ F (α, β, γ, i) → s = finsetListCode (U α β γ i)) ∧
        (∀ α β γ n (l : List BitString), l ∈ L (α, β, γ, n) →
          ∃ i, (F (α, β, γ, i)).Dom ∧ U α β γ i = l.toFinset) := by
  classical
  let probe : (ℕ × ℕ × ℕ × ℕ) × ℕ → Option BitString := fun p =>
    ((L (p.1.1, p.1.2.1, p.1.2.2.1, p.2))[p.1.2.2.2]?).map
      (fun l => finsetListCode l.toFinset)
  let F : ℕ × ℕ × ℕ × ℕ →. BitString := fun q => Nat.rfindOpt (fun n => probe (q, n))
  let U : ℕ → ℕ → ℕ → ℕ → Finset BitString := fun α β γ i =>
    if h : ∃ l, ∃ n, (L (α, β, γ, n))[i]? = some l then
      (Classical.choose h).toFinset
    else ∅
  have hcode : Computable (fun l : List BitString => finsetListCode l.toFinset) := by
    unfold finsetListCode
    exact (listCode_primrec.comp canonicalFinsetList_toFinset_primrec).to_comp
  have hprobeComp : Computable probe := by
    have hparams : Computable (fun p : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
        (p.1.1, p.1.2.1, p.1.2.2.1, p.2)) := by
      exact Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
          (Computable.pair
            (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
            Computable.snd))
    have hlist : Computable (fun p : (ℕ × ℕ × ℕ × ℕ) × ℕ => L
        (p.1.1, p.1.2.1, p.1.2.2.1, p.2)) := hL.comp hparams
    have hindex : Computable (fun p : (ℕ × ℕ × ℕ × ℕ) × ℕ => p.1.2.2.2) :=
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to_comp
    have hget : Computable (fun p : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
        (L (p.1.1, p.1.2.1, p.1.2.2.1, p.2))[p.1.2.2.2]?) :=
      Computable.list_getElem?.comp hlist hindex
    have hcodePair : Computable₂ (fun (_ : (ℕ × ℕ × ℕ × ℕ) × ℕ)
        (l : List BitString) => finsetListCode l.toFinset) :=
      (hcode.comp Computable.snd).to₂
    exact Computable.option_map hget hcodePair
  have hprobe : Computable₂ (fun q n => probe (q, n)) := hprobeComp.to₂
  have hF : Partrec F := by
    exact Partrec.rfindOpt hprobe
  have hDom : ∀ α β γ i, (F (α, β, γ, i)).Dom ↔
      ∃ n, i < (L (α, β, γ, n)).length := by
    intro α β γ i
    change (Nat.rfindOpt (fun n => probe ((α, β, γ, i), n))).Dom ↔ _
    rw [Nat.rfindOpt_dom]
    constructor
    · rintro ⟨n, s, hs⟩
      change s ∈ ((L (α, β, γ, n))[i]?).map (fun l => finsetListCode l.toFinset) at hs
      rw [Option.mem_def, Option.map_eq_some_iff] at hs
      obtain ⟨l, hget, _⟩ := hs
      exact ⟨n, (List.getElem?_eq_some_iff.mp hget).choose⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, finsetListCode ((L (α, β, γ, n))[i].toFinset), ?_⟩
      change ((L (α, β, γ, n))[i]?).map (fun l => finsetListCode l.toFinset) =
        some (finsetListCode ((L (α, β, γ, n))[i].toFinset))
      simp [List.getElem?_eq_getElem hn]
  have hUentry : ∀ α β γ i n (l : List BitString),
      (L (α, β, γ, n))[i]? = some l → U α β γ i = l.toFinset := by
    intro α β γ i n l hget
    let hw : ∃ l', ∃ m, (L (α, β, γ, m))[i]? = some l' := ⟨l, n, hget⟩
    obtain ⟨m, hm⟩ := Classical.choose_spec hw
    let l' : List BitString := Classical.choose hw
    have hboundM : i < (L (α, β, γ, m)).length :=
      (List.getElem?_eq_some_iff.mp hm).choose
    have hboundN : i < (L (α, β, γ, n)).length :=
      (List.getElem?_eq_some_iff.mp hget).choose
    let k := max m n
    have hleft := hStable α β γ m k i (le_max_left _ _) hboundM
    have hright := hStable α β γ n k i (le_max_right _ _) hboundN
    have heq : l' = l := by
      have hsome : some l' = some l := by
        calc
          some l' = (L (α, β, γ, k))[i]? := by rw [hleft, hm]
          _ = some l := by rw [hright, hget]
      exact Option.some.inj hsome
    change (if h : ∃ l', ∃ n, (L (α, β, γ, n))[i]? = some l' then
      (Classical.choose h).toFinset else ∅) = l.toFinset
    rw [dite_eq_left hw]
    exact congrArg List.toFinset heq
  have hFmem : ∀ α β γ i s, s ∈ F (α, β, γ, i) →
      ∃ n l, (L (α, β, γ, n))[i]? = some l ∧ s = finsetListCode l.toFinset := by
    intro α β γ i s hs
    change s ∈ Nat.rfindOpt (fun n => probe ((α, β, γ, i), n)) at hs
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hs
    change s ∈ ((L (α, β, γ, n))[i]?).map (fun l => finsetListCode l.toFinset) at hn
    cases hget : (L (α, β, γ, n))[i]? with
    | none => simp [hget] at hn
    | some l =>
      refine ⟨n, l, hget, ?_⟩
      have hcodeEq : finsetListCode l.toFinset = s := by
        simpa [hget, Option.mem_def] using hn
      exact hcodeEq.symm
  refine ⟨F, U, hF, hDom, ?_, ?_, ?_⟩
  · intro α β γ i hi
    obtain ⟨s, hs⟩ := Part.dom_iff_mem.mp hi
    obtain ⟨n, l, hget, _⟩ := hFmem α β γ i s hs
    exact ⟨n, l, (List.getElem?_eq_some_iff.mp hget).choose, hget,
      hUentry α β γ i n l hget⟩
  · intro α β γ i hi s hs
    obtain ⟨n, l, hget, hcode⟩ := hFmem α β γ i s hs
    exact hcode.trans (congrArg finsetListCode (hUentry α β γ i n l hget).symm)
  · intro α β γ n l hl
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.1 hl
    exact ⟨i, (hDom α β γ i).2 ⟨n, (List.getElem?_eq_some_iff.mp hget).choose⟩,
      hUentry α β γ i n l hget⟩

/-- The effective selection argument of Lemma 5 dovetails the given partial
enumeration and greedily retain an output when it is separated from all earlier retained sets.
The resulting stream has an initial-segment domain and separated members; every enumerated set
was either retained or rejected for having a large intersection with a retained set. -/
theorem lemma5_effective_selection
    (P : ℕ → ℕ → ℕ → Finset BitString → Prop)
    (E : ℕ × ℕ × ℕ × ℕ →. BitString) (hE : Partrec E)
    (hSound : ∀ α β γ i s, s ∈ E (α, β, γ, i) →
      ∃ X : Finset BitString, s = finsetListCode X ∧ P α β γ X)
    (c : ℕ)
    (_hSelf : ∀ α β γ (X : Finset BitString), P α β γ X →
      2 ^ (2 * α) ≤ X.card * 2 ^ (β + c)) :
    ∃ F : ℕ × ℕ × ℕ × ℕ →. BitString,
      ∃ U : ℕ → ℕ → ℕ → ℕ → Finset BitString,
      Partrec F ∧
      (∀ α β γ i, (F (α, β, γ, i)).Dom →
        ∀ j, j < i → (F (α, β, γ, j)).Dom) ∧
      (∀ α β γ i, (F (α, β, γ, i)).Dom →
        P α β γ (U α β γ i) ∧
        ∀ s, s ∈ F (α, β, γ, i) → s = finsetListCode (U α β γ i)) ∧
      (∀ α β γ i j, i ≠ j → (F (α, β, γ, i)).Dom → (F (α, β, γ, j)).Dom →
        (U α β γ i ∩ U α β γ j).card * 2 ^ (β + c) < 2 ^ (2 * α)) ∧
      (∀ α β γ i (X : Finset BitString), finsetListCode X ∈ E (α, β, γ, i) →
        (∃ j, (F (α, β, γ, j)).Dom ∧ X = U α β γ j) ∨
        (∃ j, (F (α, β, γ, j)).Dom ∧
          2 ^ (2 * α) ≤ (X ∩ U α β γ j).card * 2 ^ (β + c))) := by
  classical
  obtain ⟨L, hL, hLength, hStable, hStageP, hStageSeparated, hStageDecision⟩ :=
    lemma5_finite_stages
      P E hE hSound c
  obtain ⟨F, U, hF, hDom, hUstage, hCode, hEvery⟩ :=
    lemma5_stream_from_stages
      L hL hStable
  refine ⟨F, U, hF, ?_, ?_, ?_, ?_⟩
  · intro α β γ i hi j hji
    rcases (hDom α β γ i).mp hi with ⟨n, hn⟩
    exact (hDom α β γ j).2 ⟨n, lt_trans hji hn⟩
  · intro α β γ i hi
    obtain ⟨n, l, hin, hget, hUi⟩ := hUstage α β γ i hi
    have hl : l ∈ L (α, β, γ, n) := List.mem_iff_getElem?.2 ⟨i, hget⟩
    have hP' : P α β γ (U α β γ i) := by
      rw [hUi]
      exact hStageP α β γ n l hl
    refine ⟨hP', ?_⟩
    intro s hs
    exact hCode α β γ i hi s hs
  · intro α β γ i j hij hi hj
    obtain ⟨n₁, l₁, hi₁, hget₁, hUi⟩ := hUstage α β γ i hi
    obtain ⟨n₂, l₂, hj₂, hget₂, hUj⟩ := hUstage α β γ j hj
    let n := max n₁ n₂
    have hget₁' : (L (α, β, γ, n))[i]? = some l₁ := by
      rw [hStable α β γ n₁ n i (le_max_left _ _) hi₁, hget₁]
    have hget₂' : (L (α, β, γ, n))[j]? = some l₂ := by
      rw [hStable α β γ n₂ n j (le_max_right _ _) hj₂, hget₂]
    rw [hUi, hUj]
    exact hStageSeparated α β γ n i j l₁ l₂ hij hget₁' hget₂'
  · intro α β γ i X hX
    obtain ⟨n, hdecision⟩ := hStageDecision α β γ i X hX
    rcases hdecision with ⟨l, hl, hXl⟩ | ⟨l, hl, hlarge⟩
    · obtain ⟨j, hj, hUj⟩ := hEvery α β γ n l hl
      left
      exact ⟨j, hj, hXl.trans hUj.symm⟩
    · obtain ⟨j, hj, hUj⟩ := hEvery α β γ n l hl
      right
      refine ⟨j, hj, ?_⟩
      simpa [hUj] using hlarge

end Kolmogorov.Relativization
