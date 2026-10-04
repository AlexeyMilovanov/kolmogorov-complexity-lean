/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Multisource.ConditionalEncoding
import KolmogorovMathlib.Combinatorics.Bipartite
import KolmogorovMathlib.Multisource.Requests
import KolmogorovMathlib.CommonInformation.ConditionalCounting


/-!
# Muchnik's theorem: conditional codes

Muchnik's theorem is the algorithmic counterpart of the Slepian–Wolf theorem: a message of
length `C(A|B) + O(log n)` that is simple given `A` alone suffices for a decoder that knows
`B` to reconstruct `A`.  The proof uses the expander-like graph of
`exists_expanding_bipartiteGraph`.

The request of Figure 40 is `muchnikRequest`, with the cut giving its condition `C(A|B) ≤ k`
(part of Problem 327).

Complexity is plain `C`; the conditions `B, X` are joined by `pairCode`.

SUV Section 12.3, pp. 370–373.
-/

namespace Kolmogorov

private def IsMuchnikCode (D : Map) (A B X : BitString) (c n : ℕ) : Prop :=
  (X.length : ℕ∞) ≤ condK D A B + (logSlack c n : ℕ∞) ∧
    condK D X A ≤ (logSlack c n : ℕ∞) ∧
    condK D A (pairCode B X) ≤ (logSlack c n : ℕ∞)

private theorem exists_shortest_description_of_plainK_le
    (D : Map) {A : BitString} {n : ℕ} (hA : plainK D A ≤ (n : ℕ∞)) :
    ∃ P : BitString, produces D P [] A ∧ P.length ≤ n ∧
      (P.length : ℕ∞) = plainK D A := by
  have hfinite : plainK D A ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hA
  obtain ⟨P, hP, hPmin⟩ :=
    exists_program_of_KP_ne_top (M := D) (x := A) (y := []) hfinite
  refine ⟨P, hP, ?_, hPmin⟩
  exact_mod_cast hPmin.trans_le hA

private noncomputable def muchnikFingerprints
    (E : Map) (m q : ℕ) (A : BitString) : Finset BitString := by
  classical
  exact (allStrings m).toFinset.filter fun X => condK E X A ≤ (q : ℕ∞)

private noncomputable def muchnikCandidates
    (D E : Map) (a m q : ℕ) (B X : BitString) : Finset BitString := by
  classical
  exact (allStrings a).toFinset.filter fun Z =>
    condK D Z B ≤ (m : ℕ∞) ∧ X ∈ muchnikFingerprints E m q Z

open Finset

private def fromBoolVec {n : ℕ} (v : BoolVec n) : BitString := List.ofFn v

private def toBoolVec {n : ℕ} (v : BitString)
    (h : v.length = n) : BoolVec n :=
  fun i => v.get (i.cast h.symm)

private def mapGraph {a m : ℕ} (g : Finset (BoolVec a × BoolVec m)) :
    Finset (BitString × BitString) :=
  g.image fun e => (fromBoolVec e.1, fromBoolVec e.2)

private lemma fromBoolVec_length {n : ℕ} (v : BoolVec n) : (fromBoolVec v).length = n := by
  simp [fromBoolVec]

private lemma toBoolVec_fromBoolVec {n : ℕ} (v : BoolVec n) :
    toBoolVec (fromBoolVec v) (fromBoolVec_length v) = v := by
  ext i
  simp only [fromBoolVec, toBoolVec, List.get_eq_getElem, List.getElem_ofFn]
  rfl

private lemma fromBoolVec_toBoolVec {n : ℕ} (v : BitString) (h : v.length = n) :
    fromBoolVec (toBoolVec v h) = v := by
  apply List.ext_get
  · simp [fromBoolVec, h]
  · intro i h1 h2
    simp [fromBoolVec, toBoolVec]

private lemma mapGraph_property_1 {a m : ℕ} (g : Finset (BoolVec a × BoolVec m)) :
    ∀ e ∈ mapGraph g, e.1.length = a ∧ e.2.length = m := by
  intro e he
  rw [mapGraph, Finset.mem_image] at he
  obtain ⟨e', _, he_eq⟩ := he
  rw [← he_eq]
  simp [fromBoolVec_length]

private lemma mapGraph_neighbors {a m : ℕ} (g : Finset (BoolVec a × BoolVec m))
    {A : BitString} (he1 : A.length = a) :
    neighbors (mapGraph g) A =
      (neighbors g (toBoolVec A he1)).image (fun v => fromBoolVec v) := by
  ext X
  simp only [neighbors, mapGraph, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨e, ⟨⟨e', he'_g, he'_eq⟩, he_fst_eq_A⟩, he_snd_eq_X⟩
    have he_eq_fst : fromBoolVec e'.1 = e.1 := congrArg Prod.fst he'_eq
    have he_eq_snd : fromBoolVec e'.2 = e.2 := congrArg Prod.snd he'_eq
    have h1' : e'.1 = toBoolVec A he1 := by
      ext i
      have h3 : toBoolVec (fromBoolVec e'.1) (fromBoolVec_length e'.1) = e'.1 :=
        toBoolVec_fromBoolVec e'.1
      rw [← h3]
      dsimp [toBoolVec]
      congr 1
      rw [he_eq_fst, he_fst_eq_A]
    refine ⟨e'.2, ⟨e', ⟨he'_g, h1'⟩, rfl⟩, ?_⟩
    rw [he_eq_snd, he_snd_eq_X]
  · rintro ⟨X', ⟨e_var, ⟨he'g, h_fst_eq⟩, h_snd_eq⟩, hX_eq⟩
    refine ⟨(fromBoolVec e_var.1, fromBoolVec e_var.2), ⟨⟨e_var, he'g, rfl⟩, ?_⟩, ?_⟩
    · rw [h_fst_eq, fromBoolVec_toBoolVec A he1]
    · rw [h_snd_eq, hX_eq]

private lemma mapGraph_degree {a m : ℕ} (g : Finset (BoolVec a × BoolVec m))
    {A : BitString} (he1 : A.length = a) :
    leftDegree (mapGraph g) A = leftDegree g (toBoolVec A he1) := by
  rw [leftDegree, leftDegree, mapGraph_neighbors g he1]
  rw [Finset.card_image_of_injective]
  intro x y hxy
  have h_eq : toBoolVec (fromBoolVec x) (fromBoolVec_length x) =
      toBoolVec (fromBoolVec y) (fromBoolVec_length y) := by
    congr 1
  rw [toBoolVec_fromBoolVec, toBoolVec_fromBoolVec] at h_eq
  exact h_eq

private lemma mapGraph_neighborSet {a m : ℕ} (g : Finset (BoolVec a × BoolVec m))
    (T : Finset BitString) (hT : ∀ A ∈ T, A.length = a) :
    neighborSet (mapGraph g) T =
      (neighborSet g (T.attach.image (fun A => toBoolVec A.1 (hT A.1 A.2)))).image
        (fun v => fromBoolVec v) := by
  ext X
  simp only [neighborSet, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨A, hA, hX⟩
    have he1 : A.length = a := hT A hA
    rw [mapGraph_neighbors g he1] at hX
    rw [Finset.mem_image] at hX
    obtain ⟨X', hX', hX_eq⟩ := hX
    refine ⟨X', ⟨toBoolVec A he1, ⟨⟨A, hA⟩, Finset.mem_attach _ _, rfl⟩, hX'⟩, hX_eq⟩
  · rintro ⟨X', hX', h_eq⟩
    obtain ⟨A_vec, ⟨⟨A, hA⟩, _, hA_eq⟩, hX'2⟩ := hX'
    refine ⟨A, hA, ?_⟩
    have he1 : A.length = a := hT A hA
    rw [mapGraph_neighbors g he1]
    rw [Finset.mem_image]
    refine ⟨X', ?_, h_eq⟩
    rw [← hA_eq] at hX'2
    exact hX'2

private def IsMuchnikGraph (g : Finset (BitString × BitString)) (a m : ℕ) : Prop :=
  (∀ e ∈ g, e.1.length = a ∧ e.2.length = m) ∧
    (∀ A : BitString, A.length = a →
      (neighbors g A).Nonempty ∧ leftDegree g A ≤ a + m + 2) ∧
    ∀ T : Finset BitString, T.Nonempty →
      (∀ A ∈ T, A.length = a) → T.card ≤ 2 ^ (m - 1) →
      T.card < (neighborSet g T).card

/- The finite graph supplied by the probabilistic lemma, transported from fixed-length
vectors to the repository's `BitString` representation. -/
private theorem exists_muchnik_graph_on_strings (a m : ℕ) (hm : 0 < m) (hma : m ≤ a) :
    ∃ g : Finset (BitString × BitString), IsMuchnikGraph g a m := by
  obtain ⟨g0, hg0_deg, hg0_exp⟩ := exists_expanding_bipartiteGraph a m hm hma
  refine ⟨mapGraph g0, ?_, ?_, ?_⟩
  · exact mapGraph_property_1 g0
  · intro A hA
    have h_deg := hg0_deg (toBoolVec A hA)
    rw [mapGraph_degree g0 hA]
    refine ⟨?_, h_deg⟩
    have h_exp := hg0_exp {toBoolVec A hA} (Finset.singleton_nonempty _) (by
      rw [Finset.card_singleton]
      exact Nat.one_le_two_pow
    )
    have hd1 : 1 < (neighborSet g0 {toBoolVec A hA}).card := h_exp
    have hd2 : neighborSet g0 {toBoolVec A hA} = neighbors g0 (toBoolVec A hA) := by
      ext y
      simp [neighborSet, neighbors]
    rw [hd2] at hd1
    have h_pos : 0 < (neighbors g0 (toBoolVec A hA)).card := by omega
    rw [Finset.card_pos] at h_pos
    rw [mapGraph_neighbors g0 hA]
    exact Finset.Nonempty.image h_pos _
  · intro T hT1 hT2 hT3
    rw [mapGraph_neighborSet g0 T hT2]
    have h_card_eq : T.card = (T.attach.image (fun A => toBoolVec A.1 (hT2 A.1 A.2))).card
        := by
      rw [Finset.card_image_of_injective]
      · rw [Finset.card_attach]
      · intro ⟨A, hA⟩ ⟨B, hB⟩ h_eq
        have hA_len := hT2 A hA
        have hB_len := hT2 B hB
        have : fromBoolVec (toBoolVec A hA_len) = fromBoolVec (toBoolVec B hB_len) := by
          congr 1
        rw [fromBoolVec_toBoolVec, fromBoolVec_toBoolVec] at this
        exact Subtype.ext this
    rw [Finset.card_image_of_injective]
    · have h_exp := hg0_exp (T.attach.image (fun A => toBoolVec A.1 (hT2 A.1 A.2)))
      rw [← h_card_eq] at h_exp
      apply h_exp
      · obtain ⟨A, hA⟩ := hT1
        exact ⟨toBoolVec A (hT2 A hA),
          Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach _ _, rfl⟩⟩
      · exact hT3
    · intro x y hxy
      have h_eq : toBoolVec (fromBoolVec x) (fromBoolVec_length x) =
          toBoolVec (fromBoolVec y) (fromBoolVec_length y) := by
        congr 1
      rw [toBoolVec_fromBoolVec, toBoolVec_fromBoolVec] at h_eq
      exact h_eq

private theorem muchnik_allStrings_primrec : Primrec allStrings := by
  have h : Primrec (fun n : ℕ => Nat.rec (motive := fun _ => List BitString) [[]]
      (fun _ l => l.map (List.cons false) ++ l.map (List.cons true)) n) :=
    Primrec.nat_rec' Primrec.id (Primrec.const [[]])
      (Primrec.list_append.comp
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂)
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂)).to₂
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only [allStrings, ← ih]

section
variable {α β : Type*} [Primcodable α] [Primcodable β]

private theorem muchnik_primrec_all {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).all (p a) := by
  refine (Primrec.list_foldr (h := fun a q => p a q.1 && q.2) hf (Primrec.const true)
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons x l ih => simp [ih]

private theorem muchnik_primrec_any {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).any (p a) := by
  refine (Primrec.list_foldr (h := fun a q => p a q.1 || q.2) hf (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons x l ih => simp [ih]

private theorem muchnik_primrec_countP {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).countP (p a) := by
  refine (Primrec.list_foldr (h := fun a q => cond (p a q.1) (q.2 + 1) q.2) hf
    (Primrec.const 0)
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons x l ih =>
    simp at ih
    cases h : p a x <;> simp [ih, h]

private theorem muchnik_primrec_find? {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).find? (p a) := by
  refine (Primrec.list_foldr (h := fun a q => cond (p a q.1) (some q.1) q.2) hf
    (Primrec.const none)
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons x l ih =>
    simp at ih
    cases h : p a x <;> simp [ih, h]

end

private def muchnikListSubsets {α : Type} (l : List α) : List (List α) :=
  l.foldr (fun x acc => acc ++ acc.map (x :: ·)) [[]]

private theorem muchnik_primrec_listSubsets {α : Type} [Primcodable α] :
    Primrec (muchnikListSubsets (α := α)) :=
  Primrec.list_foldr (h := fun _ q => q.2 ++ q.2.map (q.1 :: ·)) Primrec.id
    (Primrec.const [[]])
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd).to₂))

private theorem muchnik_sublist_of_mem_listSubsets {α : Type} {l s : List α}
    (h : s ∈ muchnikListSubsets l) : s.Sublist l := by
  induction l generalizing s with
  | nil => simp_all [muchnikListSubsets]
  | cons x l ih =>
    simp only [muchnikListSubsets, List.foldr_cons, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨t, ht, rfl⟩
    · exact (ih h).cons x
    · exact (ih ht).cons_cons x

private theorem muchnik_filter_mem_listSubsets {α : Type} (p : α → Bool) (l : List α) :
    l.filter p ∈ muchnikListSubsets l := by
  induction l with
  | nil => simp [muchnikListSubsets]
  | cons x l ih =>
    simp only [muchnikListSubsets, List.foldr_cons, List.mem_append, List.mem_map] at ih ⊢
    cases h : p x
    · simp [h, ih]
    · right; exact ⟨_, ih, by simp [h]⟩


private def muchnikPairs (a m : ℕ) : List (BitString × BitString) :=
  (allStrings a).flatMap fun A => (allStrings m).map fun X => (A, X)

private def muchnikCheck (a m : ℕ) (s : List (BitString × BitString)) : Bool :=
  (allStrings a).all (fun A => decide (0 < s.countP (fun e => decide (e.1 = A))) &&
      decide (s.countP (fun e => decide (e.1 = A)) ≤ a + m + 2)) &&
    (muchnikListSubsets (allStrings a)).all (fun T => decide (T.length = 0) ||
      decide ((allStrings (m - 1)).length < T.length) ||
      decide (T.length < (allStrings m).countP
        (fun Y => T.any fun A => s.any (fun e => decide (e = (A, Y))))))

private theorem muchnik_primrec_pairs :
    Primrec fun am : ℕ × ℕ => muchnikPairs am.1 am.2 :=
  Primrec.list_flatMap (muchnik_allStrings_primrec.comp Primrec.fst)
    (Primrec.list_map (muchnik_allStrings_primrec.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂

private theorem muchnik_primrec_check :
    Primrec fun c : (ℕ × ℕ) × List (BitString × BitString) =>
      muchnikCheck c.1.1 c.1.2 c.2 := by
  have hcnt : Primrec fun q : ((ℕ × ℕ) × List (BitString × BitString)) × BitString =>
      q.1.2.countP (fun e => decide (e.1 = q.2)) :=
    muchnik_primrec_countP (Primrec.snd.comp Primrec.fst)
      (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).to₂
  have hdeg : Primrec fun q : ((ℕ × ℕ) × List (BitString × BitString)) × BitString =>
      decide (0 < q.1.2.countP (fun e => decide (e.1 = q.2))) &&
        decide (q.1.2.countP (fun e => decide (e.1 = q.2)) ≤ q.1.1.1 + q.1.1.2 + 2) :=
    Primrec.and.comp (Primrec.nat_lt.decide.comp (Primrec.const 0) hcnt)
      (Primrec.nat_le.decide.comp hcnt
        (Primrec.nat_add.comp (Primrec.nat_add.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 2)))
  have hmem : Primrec fun r : (((((ℕ × ℕ) × List (BitString × BitString)) ×
      List BitString) × BitString) × BitString) =>
      r.1.1.1.2.any (fun e => decide (e = (r.2, r.1.2))) :=
    muchnik_primrec_any (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.eq.decide.comp Primrec.snd
        (Primrec.pair (Primrec.snd.comp Primrec.fst)
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).to₂
  have hanyT : Primrec fun q : (((ℕ × ℕ) × List (BitString × BitString)) ×
      List BitString) × BitString =>
      q.1.2.any (fun A => q.1.1.2.any (fun e => decide (e = (A, q.2)))) :=
    muchnik_primrec_any (Primrec.snd.comp Primrec.fst) hmem.to₂
  have hcntY : Primrec fun p : ((ℕ × ℕ) × List (BitString × BitString)) × List BitString =>
      (allStrings p.1.1.2).countP
        (fun Y => p.2.any fun A => p.1.2.any (fun e => decide (e = (A, Y)))) :=
    muchnik_primrec_countP
      (muchnik_allStrings_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      hanyT.to₂
  have hT : Primrec fun p : ((ℕ × ℕ) × List (BitString × BitString)) × List BitString =>
      decide (p.2.length = 0) || decide ((allStrings (p.1.1.2 - 1)).length < p.2.length) ||
        decide (p.2.length < (allStrings p.1.1.2).countP
          (fun Y => p.2.any fun A => p.1.2.any (fun e => decide (e = (A, Y))))) :=
    Primrec.or.comp (Primrec.or.comp
      (Primrec.eq.decide.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0))
      (Primrec.nat_lt.decide.comp
        (Primrec.list_length.comp (muchnik_allStrings_primrec.comp
          (Primrec.nat_sub.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.const 1))))
        (Primrec.list_length.comp Primrec.snd)))
      (Primrec.nat_lt.decide.comp (Primrec.list_length.comp Primrec.snd) hcntY)
  exact Primrec.and.comp
    (muchnik_primrec_all (muchnik_allStrings_primrec.comp (Primrec.fst.comp Primrec.fst))
      hdeg.to₂)
    (muchnik_primrec_all (muchnik_primrec_listSubsets.comp
      (muchnik_allStrings_primrec.comp (Primrec.fst.comp Primrec.fst))) hT.to₂)

private def muchnikGraphList (a m : ℕ) : List (BitString × BitString) :=
  ((muchnikListSubsets (muchnikPairs a m)).find? (muchnikCheck a m)).getD []

private theorem muchnik_primrec_graphList :
    Primrec fun am : ℕ × ℕ => muchnikGraphList am.1 am.2 :=
  Primrec.option_getD.comp (muchnik_primrec_find? (muchnik_primrec_listSubsets.comp
    muchnik_primrec_pairs) muchnik_primrec_check.to₂) (Primrec.const [])


private theorem muchnik_mem_pairs {a m : ℕ} {e : BitString × BitString} :
    e ∈ muchnikPairs a m ↔ e.1.length = a ∧ e.2.length = m := by
  obtain ⟨A, X⟩ := e
  simp [muchnikPairs]

private theorem muchnik_pairs_nodup (a m : ℕ) : (muchnikPairs a m).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun A _ => (allStrings_nodup m).map fun X Y h => by
    simpa using h, ?_⟩
  refine (allStrings_nodup a).imp fun {A B} hAB => ?_
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro _ ⟨X, _, rfl⟩ ⟨Y, _, h⟩
  exact hAB (congrArg Prod.fst h).symm

private theorem muchnik_leftDegree_toFinset {s : List (BitString × BitString)}
    (hs : s.Nodup) (A : BitString) :
    leftDegree s.toFinset A = s.countP (fun e => decide (e.1 = A)) := by
  unfold leftDegree neighbors
  rw [Finset.card_image_of_injOn, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hs.filter _)]
  · congr 1
    ext e
    simp
  · intro e he f hf hef
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at he hf
    exact Prod.ext (he.2.trans hf.2.symm) hef

private theorem muchnik_neighborSet_card {m : ℕ} {s : List (BitString × BitString)}
    (hs : ∀ e ∈ s, e.2.length = m) (T : List BitString) :
    (neighborSet s.toFinset T.toFinset).card = (allStrings m).countP
      (fun Y => T.any fun A => s.any fun e => decide (e = (A, Y))) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    ((allStrings_nodup m).filter _)]
  congr 1
  ext Y
  simp only [neighborSet, neighbors, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_image,
    Finset.mem_filter, List.mem_filter, mem_allStrings, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨A, hA, e, ⟨he, rfl⟩, rfl⟩
    exact ⟨hs e he, _, hA, e, he, rfl⟩
  · rintro ⟨-, A, hA, e, he, rfl⟩
    exact ⟨A, hA, (A, Y), ⟨he, rfl⟩, rfl⟩


private theorem muchnik_check_iff {a m : ℕ} {s : List (BitString × BitString)}
    (hs : s.Sublist (muchnikPairs a m)) :
    muchnikCheck a m s = true ↔ IsMuchnikGraph s.toFinset a m := by
  have hnd : s.Nodup := (muchnik_pairs_nodup a m).sublist hs
  have hlen : ∀ e ∈ s, e.1.length = a ∧ e.2.length = m := fun e he =>
    muchnik_mem_pairs.1 (hs.subset he)
  have hcard : ∀ A, (neighbors s.toFinset A).card = s.countP (fun e => decide (e.1 = A)) :=
    muchnik_leftDegree_toFinset hnd
  have hnb : ∀ T : List BitString, (neighborSet s.toFinset T.toFinset).card =
      (allStrings m).countP (fun Y => T.any fun A => s.any fun e => decide (e = (A, Y))) :=
    muchnik_neighborSet_card fun e he => (hlen e he).2
  simp only [muchnikCheck, Bool.and_eq_true, List.all_eq_true, mem_allStrings,
    Bool.or_eq_true, decide_eq_true_eq, length_allStrings]
  constructor
  · rintro ⟨hdeg, hexp⟩
    refine ⟨fun e he => hlen e (List.mem_toFinset.1 he), fun A hA => ?_, ?_⟩
    · rw [leftDegree, ← Finset.card_pos, hcard]
      exact hdeg A hA
    · intro T hTne hTa hTc
      set Tl := (allStrings a).filter fun A => decide (A ∈ T) with hTl
      have hTl_eq : Tl.toFinset = T := by
        ext A
        simp only [hTl, List.mem_toFinset, List.mem_filter, mem_allStrings,
          decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨hTa A h, h⟩⟩
      have hTl_len : Tl.length = T.card := by
        rw [← hTl_eq, List.toFinset_card_of_nodup ((allStrings_nodup a).filter _)]
      have h := hexp Tl (muchnik_filter_mem_listSubsets _ _)
      rw [hTl_len, ← hnb, hTl_eq] at h
      rcases h with (h | h) | h
      · exact absurd h (Finset.card_pos.2 hTne).ne'
      · omega
      · exact h
  · rintro ⟨-, hdeg, hexp⟩
    refine ⟨fun A hA => ?_, fun T hT => ?_⟩
    · rw [← hcard, Finset.card_pos]
      exact ⟨(hdeg A hA).1, (hdeg A hA).2⟩
    · have hTs := muchnik_sublist_of_mem_listSubsets hT
      have hTnd : T.Nodup := (allStrings_nodup a).sublist hTs
      by_cases h0 : T.length = 0
      · exact Or.inl (Or.inl h0)
      by_cases h1 : 2 ^ (m - 1) < T.length
      · exact Or.inl (Or.inr h1)
      right
      have hc : T.toFinset.card = T.length := List.toFinset_card_of_nodup hTnd
      rw [← hnb, ← hc]
      refine hexp T.toFinset ?_ (fun A hA => ?_) (by omega)
      · rw [← Finset.card_pos]; omega
      · exact (mem_allStrings a A).1 (hTs.subset (List.mem_toFinset.1 hA))

/- The source's "generate all graphs until a suitable one is found", done on lists: the first
sublist of all edges passing the decidable test `muchnikCheck` is a computable function of
the sizes, it has no repetitions, and its underlying finite set is a Muchnik graph. -/
private theorem exists_computable_muchnik_graph_lists
    (hExists : ∀ (a m : ℕ), 0 < m → m ≤ a →
      ∃ g : Finset (BitString × BitString), IsMuchnikGraph g a m) :
    ∃ L : ℕ → ℕ → List (BitString × BitString),
      Computable (fun am : ℕ × ℕ => L am.1 am.2) ∧
        ∀ (a m : ℕ), 0 < m → m ≤ a → (L a m).Nodup ∧ IsMuchnikGraph (L a m).toFinset a m := by
  refine ⟨muchnikGraphList, muchnik_primrec_graphList.to_comp, fun a m hm hma => ?_⟩
  obtain ⟨g, hg⟩ := hExists a m hm hma
  set s0 := (muchnikPairs a m).filter fun e => decide (e ∈ g) with hs0
  have hs0sub : s0.Sublist (muchnikPairs a m) := List.filter_sublist
  have hs0g : s0.toFinset = g := by
    ext e
    simp only [hs0, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨muchnik_mem_pairs.2 (hg.1 e h), h⟩⟩
  have hs0chk : muchnikCheck a m s0 = true := (muchnik_check_iff hs0sub).2 (hs0g ▸ hg)
  obtain ⟨s, hs⟩ : ∃ s, (muchnikListSubsets (muchnikPairs a m)).find?
      (muchnikCheck a m) = some s := by
    rcases h : (muchnikListSubsets (muchnikPairs a m)).find? (muchnikCheck a m) with _ | s
    · exact absurd hs0chk (by
        simpa using List.find?_eq_none.1 h s0 (muchnik_filter_mem_listSubsets _ _))
    · exact ⟨s, rfl⟩
  have hsub := muchnik_sublist_of_mem_listSubsets (List.mem_of_find?_eq_some hs)
  have hval : muchnikGraphList a m = s := by simp [muchnikGraphList, hs]
  rw [hval]
  exact ⟨(muchnik_pairs_nodup a m).sublist hsub,
    (muchnik_check_iff hsub).1 (List.find?_some hs)⟩

/- Enumerate finite edge lists in a fixed computable order and take the first duplicate-free
list whose underlying finset has the required property (using `[]` outside `0 < m ≤ a`).
All quantifiers in `IsMuchnikGraph` reduce to the finite sets of strings of lengths `a` and
`m`, so the test is decidable; `hExists` proves that the search terminates on valid inputs. -/
private theorem exists_computable_muchnik_graph_family
    (hExists : ∀ (a m : ℕ), 0 < m → m ≤ a →
      ∃ g : Finset (BitString × BitString), IsMuchnikGraph g a m) :
    ∃ G : ℕ → ℕ → List (BitString × BitString),
      Computable (fun am : ℕ × ℕ => G am.1 am.2) ∧
        ∀ (a m : ℕ), 0 < m → m ≤ a →
          (G a m).Nodup ∧ IsMuchnikGraph (G a m).toFinset a m :=
  exists_computable_muchnik_graph_lists hExists

/-!
Blueprint for the graph-family decompressor:
1. List the neighbours of `A` in the computable edge list `G |A| m`.
2. Let a program be `pairCode (bits m) (bits i)` and return neighbour number `i`.
3. Prove the resulting partial map computable separately from graph combinatorics.
4. Soundness follows because the decoder rejects `m = 0` and `|A| < m`.
5. Completeness uses the neighbour's index and degree bound `a + m + 2`.
6. Bound the header and index by `logSlack 4 n`, then identify the two finsets.
-/

/-- The computable list used by the graph decoder; its order is inherited from `G`. -/
private def muchnikGraphNeighborList
    (G : ℕ → ℕ → List (BitString × BitString))
    (a m : ℕ) (A : BitString) : List BitString :=
  (G a m).filterMap fun e => if e.1 = A then some e.2 else none

/-- Decode a self-delimiting value of `m` and an ordinal in `G |A| m`.
The validity guard prevents malformed size parameters from creating fingerprints. -/
private def muchnikGraphDecoder
    (G : ℕ → ℕ → List (BitString × BitString)) : Map := fun pr =>
  let m := bitsToNat (decodeFirst pr.1)
  let i := bitsToNat (decodeSecond pr.1)
  Part.ofOption <| if 0 < m ∧ m ≤ pr.2.length then
    (muchnikGraphNeighborList G pr.2.length m pr.2)[i]?
  else none

/-- Filtering the edge list gives exactly the finset-level neighbourhood.
This is a direct membership calculation and does not use the graph
axioms. -/
private theorem muchnikGraphNeighborList_toFinset
    (G : ℕ → ℕ → List (BitString × BitString)) (a m : ℕ) (A : BitString) :
    (muchnikGraphNeighborList G a m A).toFinset = neighbors (G a m).toFinset A := by
  ext X
  simp [muchnikGraphNeighborList, neighbors]

/-- Filtering a list of edges by its left endpoint is primitive recursive in the list and the
endpoint. -/
private theorem primrec_filter_neighbors :
    Primrec (fun q : List (BitString × BitString) × BitString =>
      q.1.filterMap fun e => if e.1 = q.2 then some e.2 else none) := by
  refine Primrec.listFilterMap Primrec.fst ?_
  exact (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.fst))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)).to₂

/-- The neighbour list of `A` in `G a m` is computable in `(a, m, A)`. -/
private theorem muchnikGraphNeighborList_computable
    (G : ℕ → ℕ → List (BitString × BitString))
    (hGcomp : Computable (fun am : ℕ × ℕ => G am.1 am.2)) :
    Computable (fun p : (ℕ × ℕ) × BitString =>
      muchnikGraphNeighborList G p.1.1 p.1.2 p.2) :=
  (primrec_filter_neighbors.to_comp.comp
    ((hGcomp.comp Computable.fst).pair Computable.snd)).of_eq fun _ => rfl

/-- The decoder is partial recursive because `G`, filtering, guarded indexing, and the
two standard tuple decoders are computable. -/
private theorem muchnikGraphDecoder_isDecompressor
    (G : ℕ → ℕ → List (BitString × BitString))
    (hGcomp : Computable (fun am : ℕ × ℕ => G am.1 am.2)) :
    isDecompressor (muchnikGraphDecoder G) := by
  have hm : Computable (fun pr : BitString × BitString => bitsToNat (decodeFirst pr.1)) :=
    bitsToNat_computable.comp (decodeFirst_computable.comp Computable.fst)
  have hi : Computable (fun pr : BitString × BitString => bitsToNat (decodeSecond pr.1)) :=
    bitsToNat_computable.comp (decodeSecond_computable.comp Computable.fst)
  have hlen : Computable (fun pr : BitString × BitString => pr.2.length) :=
    Primrec.list_length.to_comp.comp Computable.snd
  have hL : Computable (fun pr : BitString × BitString =>
      muchnikGraphNeighborList G pr.2.length (bitsToNat (decodeFirst pr.1)) pr.2) :=
    (muchnikGraphNeighborList_computable G hGcomp).comp ((hlen.pair hm).pair Computable.snd)
  have hT : Computable (fun pr : BitString × BitString =>
      ((bitsToNat (decodeFirst pr.1), pr.2.length),
        (muchnikGraphNeighborList G pr.2.length (bitsToNat (decodeFirst pr.1)) pr.2,
          bitsToNat (decodeSecond pr.1)))) :=
    (hm.pair hlen).pair (hL.pair hi)
  have hF : Primrec (fun t : (ℕ × ℕ) × (List BitString × ℕ) =>
      if 0 < t.1.1 ∧ t.1.1 ≤ t.1.2 then t.2.1[t.2.2]? else none) := by
    refine Primrec.ite ?_ (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
    exact (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.fst.comp Primrec.fst)).and
      (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
  exact (Computable.ofOption (hF.to_comp.comp hT)).of_eq fun pr => rfl

/-- Every listed neighbour has its list index as a decoding program, and conversely every
successful valid decoding is a listed neighbour.  The statement also covers empty lists. -/
private theorem muchnikGraphDecoder_programs
    (G : ℕ → ℕ → List (BitString × BitString))
    (a m : ℕ) (A X : BitString) (hm : 0 < m) (hma : m ≤ a) (hA : A.length = a) :
    X ∈ neighbors (G a m).toFinset A ↔
      ∃ i < (muchnikGraphNeighborList G a m A).length,
        produces (muchnikGraphDecoder G)
          (pairCode (Nat.bits m) (Nat.bits i)) A X := by
  rw [← muchnikGraphNeighborList_toFinset, List.mem_toFinset, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hget⟩
    refine ⟨i, hi, ?_⟩
    simp only [produces, muchnikGraphDecoder, decodeFirst_pairCode, decodeSecond_pairCode,
      bitsToNat_bits, hA]
    rw [ite_eq_left ⟨hm, hma⟩, Part.mem_ofOption, Option.mem_def, List.getElem?_eq_some_iff]
    exact ⟨hi, hget⟩
  · rintro ⟨i, -, hp⟩
    simp only [produces, muchnikGraphDecoder, decodeFirst_pairCode, decodeSecond_pairCode,
      bitsToNat_bits, hA] at hp
    rw [ite_eq_left ⟨hm, hma⟩, Part.mem_ofOption, Option.mem_def, List.getElem?_eq_some_iff] at hp
    obtain ⟨hlt, hget⟩ := hp
    exact ⟨i, hlt, hget⟩

/-- With a duplicate-free edge list, the neighbour list of a valid left vertex has no
repetitions, so its length is the left degree, bounded by `a + m + 2`. -/
private theorem muchnikGraphNeighborList_length_le
    (G : ℕ → ℕ → List (BitString × BitString))
    (hG : ∀ (a m : ℕ), 0 < m → m ≤ a →
      (G a m).Nodup ∧ IsMuchnikGraph (G a m).toFinset a m)
    (a m : ℕ) (A : BitString) (hm : 0 < m) (hma : m ≤ a) (hA : A.length = a) :
    (muchnikGraphNeighborList G a m A).length ≤ a + m + 2 := by
  obtain ⟨hnd, hg⟩ := hG a m hm hma
  have hnd' : (muchnikGraphNeighborList G a m A).Nodup := by
    refine List.Nodup.filterMap ?_ hnd
    intro e e' b hb hb'
    split_ifs at hb hb' with h1 h2 <;>
      simp only [Option.mem_def, Option.some.injEq, reduceCtorEq] at hb hb'
    exact Prod.ext (h1.trans h2.symm) (hb.trans hb'.symm)
  rw [← List.toFinset_card_of_nodup hnd', muchnikGraphNeighborList_toFinset]
  exact (hg.2.1 A hA).2

/-- The program `pairCode (bits m) (bits i)` fits into `logSlack 4 n` when `m ≤ n` and the
index is below the degree bound `a + m + 2 ≤ 3n + 2`. -/
private theorem muchnikGraph_program_length_le
    (n a m i : ℕ) (hm : 0 < m) (hma : m ≤ a) (han : a ≤ n) (hi : i < a + m + 2) :
    (pairCode (Nat.bits m) (Nat.bits i)).length ≤ logSlack 4 n := by
  have hmn : (Nat.bits m).length ≤ (Nat.bits n).length := length_natBits_mono (by omega)
  have hin : (Nat.bits i).length ≤ (Nat.bits n).length + 2 := by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le, pow_add]
    have := Nat.lt_size_self n
    omega
  rw [length_pairCode, logSlack]
  omega

/-- The degree bound gives enough address bits, while `m ≤ a ≤ n` pays for the header;
the constant `4` also handles `n = 0`, which is vacuous because `m > 0`. -/
private theorem muchnikGraphDecoder_fingerprints
    (G : ℕ → ℕ → List (BitString × BitString))
    (hG : ∀ (a m : ℕ), 0 < m → m ≤ a →
      (G a m).Nodup ∧ IsMuchnikGraph (G a m).toFinset a m)
    (n a m : ℕ) (A : BitString) (hm : 0 < m) (hma : m ≤ a)
    (han : a ≤ n) (hA : A.length = a) :
    muchnikFingerprints (muchnikGraphDecoder G) m (logSlack 4 n) A =
      neighbors (G a m).toFinset A := by
  classical
  have hnb : ∀ {g : Finset (BitString × BitString)} {Z X : BitString},
      X ∈ neighbors g Z → (Z, X) ∈ g := by
    intro g Z X h
    simp only [neighbors, Finset.mem_image, Finset.mem_filter] at h
    obtain ⟨e, ⟨he, rfl⟩, rfl⟩ := h
    exact he
  ext X
  simp only [muchnikFingerprints, Finset.mem_filter, List.mem_toFinset, mem_allStrings]
  constructor
  · rintro ⟨hXm, hX⟩
    obtain ⟨p, -, hp⟩ := (condK_le_iff _ X A _).1 hX
    simp only [produces, muchnikGraphDecoder, hA] at hp
    split_ifs at hp with hguard
    · rw [Part.mem_ofOption, Option.mem_def, List.getElem?_eq_some_iff] at hp
      obtain ⟨hlt, hget⟩ := hp
      have hmem := List.getElem_mem hlt
      rw [hget, ← List.mem_toFinset, muchnikGraphNeighborList_toFinset] at hmem
      have hlen := hG a _ hguard.1 hguard.2
      have hX' := (hlen.2.1 (A, X) (hnb hmem)).2
      rw [hXm] at hX'
      rw [← hX'] at hmem
      exact hmem
    · simp at hp
  · intro hX
    have hXm := ((hG a m hm hma).2.1 (A, X) (hnb hX)).2
    refine ⟨hXm, ?_⟩
    rw [← muchnikGraphNeighborList_toFinset, List.mem_toFinset, List.mem_iff_getElem] at hX
    obtain ⟨i, hi, hget⟩ := hX
    have hprod : produces (muchnikGraphDecoder G) (pairCode (Nat.bits m) (Nat.bits i)) A X := by
      simp only [produces, muchnikGraphDecoder, decodeFirst_pairCode, decodeSecond_pairCode,
        bitsToNat_bits, hA]
      rw [ite_eq_left ⟨hm, hma⟩, Part.mem_ofOption, Option.mem_def,
        List.getElem?_eq_some_iff]
      exact ⟨hi, hget⟩
    refine (condK_le_iff _ X A _).2 ⟨_, ?_, hprod⟩
    exact muchnikGraph_program_length_le n a m i hm hma han
      (lt_of_lt_of_le hi (muchnikGraphNeighborList_length_le G hG a m A hm hma hA))

private theorem exists_decompressor_for_muchnik_graph_family
    (G : ℕ → ℕ → List (BitString × BitString))
    (hGcomp : Computable (fun am : ℕ × ℕ => G am.1 am.2))
    (hG : ∀ (a m : ℕ), 0 < m → m ≤ a →
      (G a m).Nodup ∧ IsMuchnikGraph (G a m).toFinset a m) :
    ∃ cGraph : ℕ, 3 ≤ cGraph ∧ ∃ E : Map, isDecompressor E ∧
      ∀ (n a m : ℕ) (A : BitString), 0 < m → m ≤ a → a ≤ n → A.length = a →
        muchnikFingerprints E m (logSlack cGraph n) A = neighbors (G a m).toFinset A := by
  refine ⟨4, by omega, muchnikGraphDecoder G,
    muchnikGraphDecoder_isDecompressor G hGcomp, ?_⟩
  exact muchnikGraphDecoder_fingerprints G hG

section MuchnikBadEnumeration

private theorem muchnik_mem_neighbors_iff {g : Finset (BitString × BitString)} {Z X : BitString} :
    X ∈ neighbors g Z ↔ (Z, X) ∈ g := by
  simp only [neighbors, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨e, ⟨he, rfl⟩, rfl⟩
    exact he
  · intro h
    exact ⟨(Z, X), ⟨h, rfl⟩, rfl⟩

/- Double counting: every right vertex with more than `thr` neighbours in `SF` carries more
than `thr` edges from `SF`, and `SF` emits at most `|SF| (a + m + 2)` edges. -/
private theorem muchnik_bad_right_card_mul_le {g : Finset (BitString × BitString)} {a m : ℕ}
    (hg : IsMuchnikGraph g a m) (SF : Finset BitString) (hSF : ∀ Z ∈ SF, Z.length = a)
    (thr : ℕ) :
    ((allStrings m).toFinset.filter
        (fun X => thr < (SF.filter fun Z => (Z, X) ∈ g).card)).card * (thr + 1) ≤
      SF.card * (a + m + 2) := by
  classical
  set BR := (allStrings m).toFinset.filter
    (fun X => thr < (SF.filter fun Z => (Z, X) ∈ g).card)
  calc BR.card * (thr + 1) = ∑ _X ∈ BR, (thr + 1) := by simp
    _ ≤ ∑ X ∈ BR, (SF.filter fun Z => (Z, X) ∈ g).card := by
      apply Finset.sum_le_sum
      intro X hX
      exact (Finset.mem_filter.1 hX).2
    _ = ∑ X ∈ BR, ∑ Z ∈ SF, if (Z, X) ∈ g then 1 else 0 := by
      simp only [Finset.card_filter]
    _ = ∑ Z ∈ SF, ∑ X ∈ BR, if (Z, X) ∈ g then 1 else 0 := Finset.sum_comm
    _ = ∑ Z ∈ SF, (BR.filter fun X => (Z, X) ∈ g).card := by
      simp only [Finset.card_filter]
    _ ≤ ∑ Z ∈ SF, (a + m + 2) := by
      apply Finset.sum_le_sum
      intro Z hZ
      refine le_trans (Finset.card_le_card ?_) (hg.2.1 Z (hSF Z hZ)).2
      intro X hX
      exact muchnik_mem_neighbors_iff.2 (Finset.mem_filter.1 hX).2
    _ = SF.card * (a + m + 2) := by simp

/- Expansion: a set of left vertices whose neighbours all lie in a set `R` of at most
`2^(m-1)` right vertices is no larger than `R`. -/
private theorem muchnik_card_le_of_neighbors_subset {g : Finset (BitString × BitString)}
    {a m : ℕ} (hg : IsMuchnikGraph g a m) (T R : Finset BitString)
    (hT : ∀ Z ∈ T, Z.length = a) (hTR : ∀ Z ∈ T, neighbors g Z ⊆ R)
    (hR : R.card ≤ 2 ^ (m - 1)) : T.card ≤ R.card := by
  by_contra hlt
  push Not at hlt
  obtain ⟨T', hT'T, hT'card⟩ :=
    Finset.exists_subset_card_eq (s := T) (n := min T.card (2 ^ (m - 1))) (min_le_left _ _)
  have hpos : 0 < 2 ^ (m - 1) := Nat.two_pow_pos _
  have hne : T'.Nonempty := by
    rw [← Finset.card_pos, hT'card]
    omega
  have hexp := hg.2.2 T' hne (fun Z hZ => hT Z (hT'T hZ)) (by omega)
  have hsub : neighborSet g T' ⊆ R := by
    intro X hX
    simp only [neighborSet, Finset.mem_biUnion] at hX
    obtain ⟨Z, hZ, hX⟩ := hX
    exact hTR Z (hT'T hZ) hX
  have := Finset.card_le_card hsub
  omega

/- The book's count of bad left vertices: those all of whose neighbours are bad number at
most `|SF| (a + m + 2) / (thr + 1)` once the threshold is large enough for the bad right
vertices to fit into the expansion range. -/
private theorem muchnik_bad_left_card_mul_le {g : Finset (BitString × BitString)} {a m : ℕ}
    (hg : IsMuchnikGraph g a m) (SF : Finset BitString) (hSF : ∀ Z ∈ SF, Z.length = a)
    (thr : ℕ) (hthr : SF.card * (a + m + 2) ≤ (thr + 1) * 2 ^ (m - 1)) :
    ((allStrings a).toFinset.filter (fun Z => ∀ X ∈ neighbors g Z,
        thr < (SF.filter fun Z' => (Z', X) ∈ g).card)).card * (thr + 1) ≤
      SF.card * (a + m + 2) := by
  classical
  have hBR := muchnik_bad_right_card_mul_le hg SF hSF thr
  set BR := (allStrings m).toFinset.filter
    (fun X => thr < (SF.filter fun Z => (Z, X) ∈ g).card)
  have hBRle : BR.card ≤ 2 ^ (m - 1) := by
    have h := hBR.trans hthr
    rw [mul_comm (thr + 1)] at h
    exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos thr)
  refine le_trans (Nat.mul_le_mul_right _ ?_) hBR
  refine muchnik_card_le_of_neighbors_subset hg _ BR (fun Z hZ => ?_) (fun Z hZ X hX => ?_) hBRle
  · have := (Finset.mem_filter.1 hZ).1
    simpa using this
  · have hZ' := (Finset.mem_filter.1 hZ).2 X hX
    have hlen := (hg.1 _ (muchnik_mem_neighbors_iff.1 hX)).2
    simp only [BR, Finset.mem_filter, List.mem_toFinset, mem_allStrings]
    exact ⟨hlen, hZ'⟩


open Nat.Partrec (Code)

/- One bounded run of the conditional decompressor, decoded as a bit string. -/
private def muchnikRunOut (c : Code) (t : ℕ) (p B : BitString) : Option BitString :=
  (Code.evaln t c (Encodable.encode (p, B))).bind fun r => (Encodable.decode r : Option BitString)

/- The strings produced from `B` within `t` steps by programs of length at most `m`. -/
private def muchnikSnapshot (c : Code) (m t : ℕ) (B : BitString) : List BitString :=
  (boundedPrograms m).filterMap fun p => muchnikRunOut c t p B

/- The number of `a`-bit strings of `S` that are left neighbours of `X` in `g`. -/
private def muchnikLoad (g : List (BitString × BitString)) (a : ℕ) (S : List BitString)
    (X : BitString) : ℕ :=
  (allStrings a).countP fun Z =>
    S.any (fun Y => decide (Y = Z)) && g.any (fun e => decide (e = (Z, X)))

/- The `a`-bit left vertices all of whose neighbours have load above `thr`. -/
private def muchnikBadLeft (g : List (BitString × BitString)) (a : ℕ) (S : List BitString)
    (thr : ℕ) : List BitString :=
  (allStrings a).filterMap fun Z =>
    bif g.all (fun e => !decide (e.1 = Z) || decide (thr < muchnikLoad g a S e.2))
    then some Z else none

/- Accumulated stage lists of bad left vertices, in order of first appearance. -/
private def muchnikBadHistory (g : List (BitString × BitString)) (c : Code) (a m thr : ℕ)
    (B : BitString) (s : ℕ) : List BitString :=
  ((List.range (s + 1)).flatMap fun t =>
    muchnikBadLeft g a (muchnikSnapshot c m t B) thr).eraseDups

private theorem muchnikLoad_primrec :
    Primrec fun x : ((List (BitString × BitString) × ℕ) × List BitString) × BitString =>
      muchnikLoad x.1.1.1 x.1.1.2 x.1.2 x.2 := by
  unfold muchnikLoad
  have hS : Primrec fun y : (((List (BitString × BitString) × ℕ) × List BitString) ×
      BitString) × BitString => y.1.1.2.any (fun Y => decide (Y = y.2)) :=
    muchnik_primrec_any (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.eq.decide.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  have hg : Primrec fun y : (((List (BitString × BitString) × ℕ) × List BitString) ×
      BitString) × BitString => y.1.1.1.1.any (fun e => decide (e = (y.2, y.1.2))) :=
    muchnik_primrec_any (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.eq.decide.comp Primrec.snd
        (Primrec.pair (Primrec.snd.comp Primrec.fst)
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).to₂
  exact muchnik_primrec_countP
    (muchnik_allStrings_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.and.comp hS hg).to₂

private theorem muchnikBadLeft_primrec :
    Primrec fun x : ((List (BitString × BitString) × ℕ) × List BitString) × ℕ =>
      muchnikBadLeft x.1.1.1 x.1.1.2 x.1.2 x.2 := by
  unfold muchnikBadLeft
  have hload : Primrec fun y : ((((List (BitString × BitString) × ℕ) × List BitString) × ℕ) ×
      BitString) × (BitString × BitString) =>
      muchnikLoad y.1.1.1.1.1 y.1.1.1.1.2 y.1.1.1.2 y.2.2 :=
    (muchnikLoad_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl
  have hbody : Primrec fun y : ((((List (BitString × BitString) × ℕ) × List BitString) × ℕ) ×
      BitString) × (BitString × BitString) =>
      !decide (y.2.1 = y.1.2) || decide (y.1.1.2 < muchnikLoad y.1.1.1.1.1 y.1.1.1.1.2
        y.1.1.1.2 y.2.2) :=
    Primrec.or.comp
      (Primrec.not.comp (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)))
      (Primrec.nat_lt.decide.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) hload)
  have hall : Primrec fun y : (((List (BitString × BitString) × ℕ) × List BitString) × ℕ) ×
      BitString => y.1.1.1.1.all fun e => !decide (e.1 = y.2) ||
        decide (y.1.2 < muchnikLoad y.1.1.1.1 y.1.1.1.2 y.1.1.2 e.2) :=
    muchnik_primrec_all (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      hbody.to₂
  exact Primrec.listFilterMap
    (muchnik_allStrings_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.cond hall (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂

private theorem muchnikSnapshot_primrec (c : Code) :
    Primrec fun x : (ℕ × ℕ) × BitString => muchnikSnapshot c x.1.1 x.1.2 x.2 := by
  apply Primrec.listFilterMap (primrec_boundedPrograms.comp (Primrec.fst.comp Primrec.fst))
  apply Primrec.option_bind
  · exact (evaln_primrec c).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))
  · exact Primrec.decode.comp Primrec.snd

private theorem muchnikBadHistory_primrec (c : Code) :
    Primrec fun x : (((List (BitString × BitString) × ℕ) × ℕ × ℕ) × BitString) × ℕ =>
      muchnikBadHistory x.1.1.1.1 c x.1.1.1.2 x.1.1.2.1 x.1.1.2.2 x.1.2 x.2 := by
  unfold muchnikBadHistory
  have hsnap : Primrec fun y : ((((List (BitString × BitString) × ℕ) × ℕ × ℕ) × BitString) ×
      ℕ) × ℕ => muchnikSnapshot c y.1.1.1.2.1 y.2 y.1.1.2 :=
    ((muchnikSnapshot_primrec c).comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
        Primrec.fst)))) Primrec.snd) (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).of_eq
      fun _ => rfl
  have hstage : Primrec fun y : ((((List (BitString × BitString) × ℕ) × ℕ × ℕ) × BitString) ×
      ℕ) × ℕ => muchnikBadLeft y.1.1.1.1.1 y.1.1.1.1.2 (muchnikSnapshot c y.1.1.1.2.1 y.2 y.1.1.2)
        y.1.1.1.2.2 :=
    (muchnikBadLeft_primrec.comp (Primrec.pair (Primrec.pair (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
      hsnap)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
        Primrec.fst)))))).of_eq fun _ => rfl
  exact CodedFiniteDistribution.eraseDups_bitstring_primrec.comp (Primrec.list_flatMap
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) hstage.to₂)


/- Stages are accumulated, so the history at an earlier stage is a prefix of every later
history and first-appearance ordinals are stable. -/
private theorem muchnikBadHistory_prefix (g : List (BitString × BitString)) (c : Code)
    (a m thr : ℕ) (B : BitString) {s s' : ℕ} (hss : s ≤ s') :
    muchnikBadHistory g c a m thr B s <+: muchnikBadHistory g c a m thr B s' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hss
  have hrange : List.range (s + d + 1) =
      List.range (s + 1) ++ (List.range d).map (s + 1 + ·) := by
    rw [show s + d + 1 = (s + 1) + d by omega]
    exact List.range_add
  rw [muchnikBadHistory, muchnikBadHistory, hrange,
    List.flatMap_append, List.eraseDups_append]
  exact List.prefix_append _ _

/- The fixed width slack: the decoder reads the threshold exponent as this number minus the
length of the index field. -/
private def muchnikWidthSlack (a m : ℕ) : ℕ := m + 1 + (Nat.bits (a + m + 2)).length

/- The decoder of bad left vertices: it reads `a`, `m` and a fixed-width index from the
program, recovers the threshold from the index width, and waits until the accumulated
enumeration of bad left vertices given `B` is long enough. -/
private def muchnikBadDecoder (G : ℕ → ℕ → List (BitString × BitString)) (c : Code) : Map :=
  fun q =>
    let a := bitsToNat (decodeFirst q.1)
    let m := bitsToNat (decodeFirst (decodeSecond q.1))
    let z := decodeSecond (decodeSecond q.1)
    let thr := 2 ^ (muchnikWidthSlack a m - z.length)
    (Nat.rfind fun s => Part.some (decide (bitsToNat z <
        (muchnikBadHistory (G a m) c a m thr q.2 s).length))).bind fun s =>
      Part.some ((muchnikBadHistory (G a m) c a m thr q.2 s).getD (bitsToNat z) [])

private theorem muchnikBadDecoder_partrec (G : ℕ → ℕ → List (BitString × BitString))
    (hGcomp : Computable (fun am : ℕ × ℕ => G am.1 am.2)) (c : Code) :
    Partrec (muchnikBadDecoder G c) := by
  have hA : Computable fun P : BitString => bitsToNat (decodeFirst P) :=
    bitsToNat_computable.comp decodeFirst_computable
  have hM : Computable fun P : BitString => bitsToNat (decodeFirst (decodeSecond P)) :=
    bitsToNat_computable.comp (decodeFirst_computable.comp decodeSecond_computable)
  have hZ : Computable fun P : BitString => decodeSecond (decodeSecond P) :=
    decodeSecond_computable.comp decodeSecond_computable
  have hW : Computable fun P : BitString => muchnikWidthSlack (bitsToNat (decodeFirst P))
      (bitsToNat (decodeFirst (decodeSecond P))) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp hM (Computable.const 1))
      (Computable.list_length.comp (natBits_computable.comp
        (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp hA hM)
          (Computable.const 2))))
  have hT : Computable fun P : BitString => 2 ^ (muchnikWidthSlack (bitsToNat (decodeFirst P))
      (bitsToNat (decodeFirst (decodeSecond P))) - (decodeSecond (decodeSecond P)).length) :=
    Computable.pow2.comp (Primrec.nat_sub.to_comp.comp hW (Computable.list_length.comp hZ))
  have hG : Computable fun P : BitString =>
      G (bitsToNat (decodeFirst P)) (bitsToNat (decodeFirst (decodeSecond P))) :=
    hGcomp.comp (Computable.pair hA hM)
  have hH : Computable fun p : (BitString × BitString) × ℕ =>
      muchnikBadHistory (G (bitsToNat (decodeFirst p.1.1))
        (bitsToNat (decodeFirst (decodeSecond p.1.1)))) c (bitsToNat (decodeFirst p.1.1))
        (bitsToNat (decodeFirst (decodeSecond p.1.1)))
        (2 ^ (muchnikWidthSlack (bitsToNat (decodeFirst p.1.1))
          (bitsToNat (decodeFirst (decodeSecond p.1.1))) -
            (decodeSecond (decodeSecond p.1.1)).length)) p.1.2 p.2 := by
    have h1 : Computable fun p : (BitString × BitString) × ℕ => p.1.1 :=
      Computable.fst.comp Computable.fst
    exact ((muchnikBadHistory_primrec c).to_comp.comp (Computable.pair (Computable.pair
      (Computable.pair (Computable.pair (hG.comp h1) (hA.comp h1))
        (Computable.pair (hM.comp h1) (hT.comp h1)))
      (Computable.snd.comp Computable.fst)) Computable.snd)).of_eq fun _ => rfl
  have hI : Computable fun p : (BitString × BitString) × ℕ =>
      bitsToNat (decodeSecond (decodeSecond p.1.1)) :=
    bitsToNat_computable.comp (hZ.comp (Computable.fst.comp Computable.fst))
  have hcheck : Computable₂ fun (q : BitString × BitString) (s : ℕ) =>
      decide (bitsToNat (decodeSecond (decodeSecond q.1)) <
        (muchnikBadHistory (G (bitsToNat (decodeFirst q.1))
        (bitsToNat (decodeFirst (decodeSecond q.1)))) c (bitsToNat (decodeFirst q.1))
        (bitsToNat (decodeFirst (decodeSecond q.1)))
        (2 ^ (muchnikWidthSlack (bitsToNat (decodeFirst q.1))
          (bitsToNat (decodeFirst (decodeSecond q.1))) -
            (decodeSecond (decodeSecond q.1)).length)) q.2 s).length) :=
    (Primrec.nat_lt.decide.to_comp.comp hI (Computable.list_length.comp hH)).to₂
  have hpost : Computable₂ fun (q : BitString × BitString) (s : ℕ) =>
      (muchnikBadHistory (G (bitsToNat (decodeFirst q.1))
        (bitsToNat (decodeFirst (decodeSecond q.1)))) c (bitsToNat (decodeFirst q.1))
        (bitsToNat (decodeFirst (decodeSecond q.1)))
        (2 ^ (muchnikWidthSlack (bitsToNat (decodeFirst q.1))
          (bitsToNat (decodeFirst (decodeSecond q.1))) -
            (decodeSecond (decodeSecond q.1)).length)) q.2 s).getD
        (bitsToNat (decodeSecond (decodeSecond q.1))) [] :=
    ((Primrec.list_getD []).to_comp.comp hH hI).to₂
  exact Partrec.bind (Partrec.rfind hcheck.partrec₂) hpost.partrec₂

/- The decoder returns the entry of the enumeration of bad left vertices whose ordinal is
written in the index field, as soon as some stage has listed that many entries. -/
private theorem muchnikBadDecoder_eval (G : ℕ → ℕ → List (BitString × BitString))
    (c : Code) (a m s : ℕ) (z B : BitString)
    (hk : bitsToNat z < (muchnikBadHistory (G a m) c a m
      (2 ^ (muchnikWidthSlack a m - z.length)) B s).length) :
    (muchnikBadHistory (G a m) c a m (2 ^ (muchnikWidthSlack a m - z.length)) B s).getD
        (bitsToNat z) [] ∈
      muchnikBadDecoder G c (pairCode (Nat.bits a) (pairCode (Nat.bits m) z), B) := by
  set H := fun s => muchnikBadHistory (G a m) c a m
    (2 ^ (muchnikWidthSlack a m - z.length)) B s with hH
  have hdec : muchnikBadDecoder G c (pairCode (Nat.bits a) (pairCode (Nat.bits m) z), B) =
      (Nat.rfind fun s => Part.some (decide (bitsToNat z < (H s).length))).bind fun s =>
        Part.some ((H s).getD (bitsToNat z) []) := by
    simp only [muchnikBadDecoder, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
      hH]
  rw [hdec, Part.mem_bind_iff]
  let hex : ∃ t, bitsToNat z < (H t).length := ⟨s, hk⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · refine Nat.mem_rfind.2 ⟨by simpa using Nat.find_spec hex, fun hk' => ?_⟩
    have := Nat.find_min hex hk'
    simpa using this
  · have h0 : bitsToNat z < (H (Nat.find hex)).length := Nat.find_spec hex
    have hle : Nat.find hex ≤ s := Nat.find_le hk
    obtain ⟨r, hr⟩ := muchnikBadHistory_prefix (G a m) c a m
      (2 ^ (muchnikWidthSlack a m - z.length)) B hle
    have hr' : H (Nat.find hex) ++ r = H s := hr
    change (H s).getD (bitsToNat z) [] ∈ _
    rw [← hr', List.getD_append _ _ _ _ h0]
    exact Part.mem_some _


/- Every string in a snapshot has a program of length at most `m` given `B`. -/
private theorem muchnikSnapshot_sound {c : Code} {D : Map} (hc : IsCodeFor c D)
    {m t : ℕ} {B Z : BitString} (hZ : Z ∈ muchnikSnapshot c m t B) :
    condK D Z B ≤ (m : ℕ∞) := by
  rw [muchnikSnapshot, List.mem_filterMap] at hZ
  obtain ⟨p, hp, hrun⟩ := hZ
  refine (condK_le_iff D Z B m).2 ⟨p, (mem_boundedPrograms_iff p m).1 hp, ?_⟩
  unfold muchnikRunOut at hrun
  rw [Option.bind_eq_some_iff] at hrun
  obtain ⟨r, hr, hdec⟩ := hrun
  have heval := Nat.Partrec.Code.evaln_sound hr
  unfold IsCodeFor at hc
  aesop

/- Snapshots grow with the number of steps. -/
private theorem muchnikSnapshot_mono (c : Code) {m t t' : ℕ} (htt' : t ≤ t')
    {B Z : BitString} (hZ : Z ∈ muchnikSnapshot c m t B) : Z ∈ muchnikSnapshot c m t' B := by
  rw [muchnikSnapshot, List.mem_filterMap] at hZ ⊢
  obtain ⟨p, hp, hrun⟩ := hZ
  refine ⟨p, hp, ?_⟩
  unfold muchnikRunOut at hrun ⊢
  rw [Option.bind_eq_some_iff] at hrun ⊢
  obtain ⟨r, hr, hdec⟩ := hrun
  exact ⟨r, Nat.Partrec.Code.evaln_mono htt' hr, hdec⟩

/- A single string of complexity at most `m` given `B` appears at some stage. -/
private theorem muchnikSnapshot_complete_one {c : Code} {D : Map} (hc : IsCodeFor c D)
    {m : ℕ} {B Z : BitString} (hZ : condK D Z B ≤ (m : ℕ∞)) :
    ∃ t, Z ∈ muchnikSnapshot c m t B := by
  obtain ⟨p, hp, hprod⟩ := (condK_le_iff D Z B m).1 hZ
  obtain ⟨t, ht⟩ : ∃ t, Encodable.encode Z ∈ Code.evaln t c (Encodable.encode (p, B)) := by
    have hEval : Encodable.encode Z ∈ c.eval (Encodable.encode (p, B)) := by
      simp_all +decide [produces, IsCodeFor]
    exact Code.evaln_complete.mp hEval
  refine ⟨t, ?_⟩
  rw [muchnikSnapshot, List.mem_filterMap]
  refine ⟨p, (mem_boundedPrograms_iff p m).2 hp, ?_⟩
  simp only [muchnikRunOut, Option.bind_eq_some_iff]
  exact ⟨_, ht, Encodable.encodek Z⟩

/- Since there are finitely many `a`-bit strings, one stage contains all of those of
complexity at most `m` given `B`. -/
private theorem muchnikSnapshot_complete {c : Code} {D : Map} (hc : IsCodeFor c D)
    (a m : ℕ) (B : BitString) :
    ∃ T, ∀ Z : BitString, Z.length = a → condK D Z B ≤ (m : ℕ∞) →
      Z ∈ muchnikSnapshot c m T B := by
  suffices h : ∀ l : List BitString, ∃ T, ∀ Z ∈ l, condK D Z B ≤ (m : ℕ∞) →
      Z ∈ muchnikSnapshot c m T B by
    obtain ⟨T, hT⟩ := h (allStrings a)
    exact ⟨T, fun Z hZ hK => hT Z ((mem_allStrings a Z).2 hZ) hK⟩
  intro l
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons Y l ih =>
    obtain ⟨T, hT⟩ := ih
    by_cases hY : condK D Y B ≤ (m : ℕ∞)
    · obtain ⟨t, ht⟩ := muchnikSnapshot_complete_one hc hY
      refine ⟨max T t, fun Z hZ hK => ?_⟩
      rcases List.mem_cons.1 hZ with rfl | hZ
      · exact muchnikSnapshot_mono c (le_max_right _ _) ht
      · exact muchnikSnapshot_mono c (le_max_left _ _) (hT Z hZ hK)
    · refine ⟨T, fun Z hZ hK => ?_⟩
      rcases List.mem_cons.1 hZ with rfl | hZ
      · exact absurd hK hY
      · exact hT Z hZ hK

/- The load computed by the decoder is the number of left neighbours of `X` among the
`a`-bit members of `S`. -/
private theorem muchnikLoad_eq_card (g : List (BitString × BitString)) (a : ℕ)
    (S : List BitString) (X : BitString) :
    muchnikLoad g a S X = (((allStrings a).toFinset.filter fun Z => Z ∈ S).filter
      fun Z => (Z, X) ∈ g.toFinset).card := by
  classical
  rw [muchnikLoad, List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    ((allStrings_nodup a).filter _)]
  congr 1
  ext Z
  simp [Finset.mem_filter, and_assoc]

/- Membership in a stage list of bad left vertices. -/
private theorem mem_muchnikBadLeft {g : List (BitString × BitString)} {a : ℕ}
    {S : List BitString} {thr : ℕ} {Z : BitString} :
    Z ∈ muchnikBadLeft g a S thr ↔
      Z.length = a ∧ ∀ X ∈ neighbors g.toFinset Z, thr < muchnikLoad g a S X := by
  rw [muchnikBadLeft, List.mem_filterMap]
  constructor
  · rintro ⟨Y, hY, hb⟩
    cases h : g.all (fun e => !decide (e.1 = Y) || decide (thr < muchnikLoad g a S e.2)) <;>
      simp only [h, Bool.cond_false, Bool.cond_true, reduceCtorEq, Option.some.injEq] at hb
    subst hb
    refine ⟨(mem_allStrings a Y).1 hY, fun X hX => ?_⟩
    rw [List.all_eq_true] at h
    have := h (Y, X) (List.mem_toFinset.1 (muchnik_mem_neighbors_iff.1 hX))
    simpa using this
  · rintro ⟨hZ, hX⟩
    refine ⟨Z, (mem_allStrings a Z).2 hZ, ?_⟩
    have h : g.all (fun e => !decide (e.1 = Z) || decide (thr < muchnikLoad g a S e.2)) =
        true := by
      rw [List.all_eq_true]
      rintro ⟨Y, X⟩ he
      by_cases hYZ : Y = Z
      · subst hYZ
        simpa using hX X (muchnik_mem_neighbors_iff.2 (List.mem_toFinset.2 he))
      · simp [hYZ]
    simp [h]

/- Padding with high-order zero bits does not change the value of a binary numeral. -/
private theorem muchnik_bitsToNat_append_replicate_false (l : List Bool) (k : ℕ) :
    bitsToNat (l ++ List.replicate k false) = bitsToNat l := by
  have h0 : bitsToNat (List.replicate k false) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [bitsToNat, List.replicate_succ, List.foldr_cons] at ih ⊢
      simp [ih]
  unfold bitsToNat
  rw [List.foldr_append]
  unfold bitsToNat at h0
  rw [h0]


/- The book's argument: if every neighbour of `A` had more than `2^K` candidates, `A` would be
one of the few bad left vertices, which the decoder enumerates given `B`; its ordinal and the
two size parameters would then describe `A` given `B` in fewer than `m` bits. -/
private theorem muchnik_exists_light_fingerprint
    (D : Map) (hD : isOptimalConditional D)
    (G : ℕ → ℕ → List (BitString × BitString))
    (hGcomp : Computable (fun am : ℕ × ℕ => G am.1 am.2))
    (hG : ∀ (a m : ℕ), 0 < m → m ≤ a →
      (G a m).Nodup ∧ IsMuchnikGraph (G a m).toFinset a m) :
    ∃ cBad : ℕ, ∀ (n a m : ℕ) (A B : BitString),
      0 < m → m ≤ a → a ≤ n → A.length = a → condK D A B = (m : ℕ∞) →
      ∃ X ∈ neighbors (G a m).toFinset A,
        (((allStrings a).toFinset.filter fun Z => condK D Z B ≤ (m : ℕ∞)).filter
          fun Z => (Z, X) ∈ (G a m).toFinset).card ≤ 2 ^ logSlack cBad n := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Code, IsCodeFor c D := Nat.Partrec.Code.exists_code.mp hD.1
  obtain ⟨cF, hcF⟩ := hD.2 (muchnikBadDecoder G c) (muchnikBadDecoder_partrec G hGcomp c)
  refine ⟨cF + 13, fun n a m A B hm hma han hA hAB => ?_⟩
  set K := logSlack (cF + 13) n with hK
  set s := (Nat.bits n).length with hs
  have hKs : 13 * s + 13 + cF ≤ K := by
    simp only [hK, logSlack]
    nlinarith
  have hgr := (hG a m hm hma).2
  obtain ⟨T, hT⟩ := muchnikSnapshot_complete hc a m B
  set g := G a m with hg
  set SF := (allStrings a).toFinset.filter fun Z => condK D Z B ≤ (m : ℕ∞) with hSF
  have hSFlen : ∀ Z ∈ SF, Z.length = a := fun Z hZ => by
    simpa using (Finset.mem_filter.1 hZ).1
  have hSFT : ((allStrings a).toFinset.filter fun Z => Z ∈ muchnikSnapshot c m T B) = SF := by
    ext Z
    simp only [hSF, Finset.mem_filter, List.mem_toFinset, mem_allStrings]
    exact ⟨fun h => ⟨h.1, muchnikSnapshot_sound hc h.2⟩, fun h => ⟨h.1, hT Z h.1 h.2⟩⟩
  have hSFcard : SF.card < 2 ^ (m + 1) := by
    calc SF.card ≤ (muchnikSnapshot c m T B).toFinset.card := Finset.card_le_card (by
          intro Z hZ
          rw [← hSFT] at hZ
          simpa using (Finset.mem_filter.1 hZ).2)
      _ ≤ (muchnikSnapshot c m T B).length := List.toFinset_card_le _
      _ ≤ (boundedPrograms m).length := List.length_filterMap_le _ _
      _ < 2 ^ (m + 1) := length_boundedPrograms_lt m
  by_contra hbad
  push Not at hbad
  by_cases hKm : m < K
  · obtain ⟨X, hX⟩ := (hgr.2.1 A hA).1
    have h1 := hbad X hX
    have h2 : (SF.filter fun Z => (Z, X) ∈ g.toFinset).card ≤ SF.card :=
      Finset.card_filter_le _ _
    have h3 : 2 ^ (m + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hKm
    omega
  push Not at hKm
  set L := (Nat.bits (a + m + 2)).length with hL
  have hLlt : a + m + 2 < 2 ^ L := by
    rw [hL, Nat.size_eq_bits_len]
    exact Nat.lt_size_self _
  have hLs : L ≤ s + 2 := by
    rw [hL, hs, Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le]
    have := Nat.lt_size_self n
    rw [pow_add]
    omega
  set thr := 2 ^ K with hthr
  have hthrbound : SF.card * (a + m + 2) ≤ (thr + 1) * 2 ^ (m - 1) := by
    calc SF.card * (a + m + 2) ≤ 2 ^ (m + 1) * 2 ^ L :=
          Nat.mul_le_mul hSFcard.le hLlt.le
      _ = 2 ^ (L + 2) * 2 ^ (m - 1) := by
          rw [← pow_add, ← pow_add, show m + 1 + L = L + 2 + (m - 1) by omega]
      _ ≤ 2 ^ K * 2 ^ (m - 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ (thr + 1) * 2 ^ (m - 1) := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hBL := muchnik_bad_left_card_mul_le hgr SF hSFlen thr hthrbound
  set BL := (allStrings a).toFinset.filter (fun Z => ∀ X ∈ neighbors g.toFinset Z,
    thr < (SF.filter fun Z' => (Z', X) ∈ g.toFinset).card) with hBLdef
  set w := m + 1 + L - K with hw
  have hBLw : BL.card < 2 ^ w := by
    have h1 : SF.card * (a + m + 2) < 2 ^ (m + 1) * 2 ^ L :=
      Nat.mul_lt_mul_of_lt_of_le hSFcard hLlt.le (by omega)
    have h2 : 2 ^ (m + 1) * 2 ^ L = 2 ^ w * thr := by
      rw [hthr, ← pow_add, ← pow_add, show m + 1 + L = w + K by omega]
    have h3 : BL.card * thr < 2 ^ w * thr := by
      calc BL.card * thr ≤ BL.card * (thr + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ < 2 ^ w * thr := by omega
    exact Nat.lt_of_mul_lt_mul_right (a := thr) h3
  have hload : ∀ t X, muchnikLoad g a (muchnikSnapshot c m t B) X ≤
      (SF.filter fun Z => (Z, X) ∈ g.toFinset).card := by
    intro t X
    rw [muchnikLoad_eq_card]
    apply Finset.card_le_card
    intro Z hZ
    simp only [hSF, Finset.mem_filter] at hZ ⊢
    exact ⟨⟨hZ.1.1, muchnikSnapshot_sound hc hZ.1.2⟩, hZ.2⟩
  have hloadT : ∀ X, muchnikLoad g a (muchnikSnapshot c m T B) X =
      (SF.filter fun Z => (Z, X) ∈ g.toFinset).card := by
    intro X
    rw [muchnikLoad_eq_card, hSFT]
  set H := muchnikBadHistory g c a m thr B T with hH
  have hHsub : ∀ Z ∈ H, Z ∈ BL := by
    intro Z hZ
    rw [hH, muchnikBadHistory, mem_eraseDups_list, List.mem_flatMap] at hZ
    obtain ⟨t, -, hZt⟩ := hZ
    obtain ⟨hZa, hZX⟩ := mem_muchnikBadLeft.1 hZt
    rw [hBLdef, Finset.mem_filter, List.mem_toFinset, mem_allStrings]
    exact ⟨hZa, fun X hX => lt_of_lt_of_le (hZX X hX) (hload t X)⟩
  have hAH : A ∈ H := by
    rw [hH, muchnikBadHistory, mem_eraseDups_list, List.mem_flatMap]
    refine ⟨T, List.mem_range.2 (Nat.lt_succ_self T),
      mem_muchnikBadLeft.2 ⟨hA, fun X hX => ?_⟩⟩
    rw [hloadT]
    exact hbad X hX
  have hHlen : H.length ≤ BL.card := by
    have hnd : H.Nodup := nodup_eraseDups_list _
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card (fun Z hZ => hHsub Z (List.mem_toFinset.1 hZ))
  set i := H.idxOf A with hi_def
  have hi : i < H.length := List.idxOf_lt_length_of_mem hAH
  have hiw : i < 2 ^ w := by omega
  have hbits : (Nat.bits i).length ≤ w := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.2 hiw
  set z := Nat.bits i ++ List.replicate (w - (Nat.bits i).length) false with hz
  have hzlen : z.length = w := by
    simp only [hz, List.length_append, List.length_replicate]
    omega
  have hzval : bitsToNat z = i := by
    rw [hz, muchnik_bitsToNat_append_replicate_false, bitsToNat_bits]
  have hthrz : 2 ^ (muchnikWidthSlack a m - z.length) = thr := by
    rw [hzlen, muchnikWidthSlack, ← hL, hthr, show m + 1 + L - w = K by omega]
  have heval := muchnikBadDecoder_eval G c a m T z B (by
    rw [hthrz, hzval]
    exact hi)
  rw [hthrz, hzval] at heval
  have hget : H.getD i [] = A := by
    rw [List.getD_eq_getElem _ [] hi, List.getElem_idxOf hi]
  have hFK : condK (muchnikBadDecoder G c) A B ≤
      ((pairCode (Nat.bits a) (pairCode (Nat.bits m) z)).length : ℕ∞) :=
    (condK_le_iff _ _ _ _).2 ⟨_, le_rfl, by
      rw [← hget]
      exact heval⟩
  have hDK := (hcF A B).trans (add_le_add_left hFK _)
  rw [hAB] at hDK
  have hba : (Nat.bits a).length ≤ s := length_natBits_mono han
  have hbm : (Nat.bits m).length ≤ s := length_natBits_mono (hma.trans han)
  have hlenP : (pairCode (Nat.bits a) (pairCode (Nat.bits m) z)).length =
      (Nat.bits a).length + 1 + (Nat.bits a).length +
        ((Nat.bits m).length + 1 + (Nat.bits m).length + w) := by
    rw [length_pairCode, length_pairCode, hzlen]
  have hfin : m ≤ (pairCode (Nat.bits a) (pairCode (Nat.bits m) z)).length + cF := by
    exact_mod_cast hDK
  have hwK : w + K = m + 1 + L := by omega
  clear_value w L K s
  omega

end MuchnikBadEnumeration

/- The book's counting step (SUV Section 12.3).  Call a right vertex `X` bad when it has more than
`2^K` candidates, `K = logSlack (cGraph + cBad) n`; there are fewer than `2^(m+1) · (a+m+2) / 2^K`
of them.  A left vertex all of whose neighbours are bad lies in a set that the expansion of the
graph keeps at most as large as the set of bad right vertices; since the graph family is
computable, that set is enumerable given `B` and `a, m, K`, so its members have complexity less
than `m` given `B`.  Hence `A` has a good neighbour.  The fingerprints must be the neighbours
of the computable graph: for an arbitrary decompressor they are only enumerable and "all
neighbours are bad" is not enumerable. -/
private theorem exists_sparse_muchnik_fingerprint
    (D : Map) (hD : isOptimalConditional D) (E : Map)
    (G : ℕ → ℕ → List (BitString × BitString))
    (hGcomp : Computable (fun am : ℕ × ℕ => G am.1 am.2))
    (hG : ∀ (a m : ℕ), 0 < m → m ≤ a →
      (G a m).Nodup ∧ IsMuchnikGraph (G a m).toFinset a m) :
    ∃ cBad : ℕ, ∀ (cGraph n a m : ℕ) (A B : BitString),
      0 < m → m ≤ a → a ≤ n → A.length = a →
      condK D A B = (m : ℕ∞) →
      (∀ Z : BitString, Z.length = a →
        muchnikFingerprints E m (logSlack cGraph n) Z = neighbors (G a m).toFinset Z) →
      ∃ X ∈ muchnikFingerprints E m (logSlack cGraph n) A,
        (muchnikCandidates D E a m (logSlack cGraph n) B X).card ≤
          2 ^ logSlack (cGraph + cBad) n := by
  classical
  obtain ⟨cBad, hcBad⟩ := muchnik_exists_light_fingerprint D hD G hGcomp hG
  refine ⟨cBad, fun cGraph n a m A B hm hma han hA hAB hfp => ?_⟩
  obtain ⟨X, hX, hcard⟩ := hcBad n a m A B hm hma han hA hAB
  refine ⟨X, by rw [hfp A hA]; exact hX, ?_⟩
  have hcand : muchnikCandidates D E a m (logSlack cGraph n) B X =
      ((allStrings a).toFinset.filter fun Z => condK D Z B ≤ (m : ℕ∞)).filter
        fun Z => (Z, X) ∈ (G a m).toFinset := by
    ext Z
    simp only [muchnikCandidates, Finset.mem_filter, List.mem_toFinset, mem_allStrings]
    constructor
    · rintro ⟨hZ, hK, hXZ⟩
      rw [hfp Z hZ] at hXZ
      exact ⟨⟨hZ, hK⟩, List.mem_toFinset.1 (muchnik_mem_neighbors_iff.1 hXZ)⟩
    · rintro ⟨⟨hZ, hK⟩, hXZ⟩
      refine ⟨hZ, hK, ?_⟩
      rw [hfp Z hZ]
      exact muchnik_mem_neighbors_iff.2 (List.mem_toFinset.2 hXZ)
  rw [hcand]
  refine hcard.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  exact logSlack_mono_left (Nat.le_add_left cBad cGraph) n

/-!
Blueprint for the candidate-stage enumerator:
1. Choose numeric `Partrec.Code`s for `D` and `E`.
2. At stage `s`, scan `allStrings a` in its fixed computable order.
3. Keep `Z` when a program of length at most `m` produces `Z` from `B`, and a
   program of length at most `logSlack cGraph n` produces `X` from `Z` by stage `s`.
4. Also require `|X| = m`; `|Z| = a` follows from the scan domain.
5. Prove computability with explicit snapshot/filter compositions.
6. `evaln_sound` gives soundness; completeness takes the maximum of two halt stages.
-/

/-- A finite simultaneous snapshot of the two bounded computations defining a candidate. -/
private def muchnikCandidateStage
    (cD cE : Nat.Partrec.Code) (cGraph n a m : ℕ)
    (B X : BitString) (s : ℕ) : List BitString :=
  (allStrings a).filter fun Z =>
    decide (X.length = m ∧
      Z ∈ conditionalOutputSnapshot cD B m s ∧
      X ∈ conditionalOutputSnapshot cE Z (logSlack cGraph n) s)

/-- Membership of a bitstring in a finite list of bitstrings is primitive recursive. -/
private theorem muchnik_bitString_mem_primrec :
    PrimrecRel fun (Z : BitString) (L : List BitString) => Z ∈ L :=
  (PrimrecRel.exists_mem_list (R := fun (a b : BitString) => a = b) Primrec.eq).swap.of_eq
    fun Z L => by simp

/-- The logarithmic slack `c * |bits n| + c` is primitive recursive in `c` and `n`. -/
private theorem muchnik_logSlack_primrec : Primrec₂ logSlack := by
  unfold logSlack
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp Primrec.fst
    (Primrec.list_length.comp (primrec_natBits.comp Primrec.snd))) Primrec.fst

/-- The seven-argument stage map is computable: all projections are explicit, and the
only nontrivial components are the two primitive-recursive output snapshots. -/
private theorem muchnikCandidateStage_computable (cD cE : Nat.Partrec.Code) :
    Computable (fun p :
      ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
        muchnikCandidateStage cD cE p.1 p.2.1 p.2.2.1 p.2.2.2.1
          p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  have hX : Primrec fun q : (ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ)))))) ×
      BitString => q.1.2.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  have hs : Primrec fun q : (ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ)))))) ×
      BitString => q.1.2.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  have hm : Primrec fun q : (ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ)))))) ×
      BitString => q.1.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hB : Primrec fun q : (ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ)))))) ×
      BitString => q.1.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))))
  have hslack : Primrec fun q : (ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ)))))) ×
      BitString => logSlack q.1.1 q.1.2.1 :=
    muchnik_logSlack_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hsnapD := (conditionalOutputSnapshot_primrec cD).comp
    (Primrec.pair (Primrec.pair hB hm) hs)
  have hsnapE := (conditionalOutputSnapshot_primrec cE).comp
    (Primrec.pair (Primrec.pair Primrec.snd hslack) hs)
  have hpred : PrimrecRel fun (p : ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))))
      (Z : BitString) => p.2.2.2.2.2.1.length = p.2.2.2.1 ∧
        Z ∈ conditionalOutputSnapshot cD p.2.2.2.2.1 p.2.2.2.1 p.2.2.2.2.2.2 ∧
        p.2.2.2.2.2.1 ∈ conditionalOutputSnapshot cE Z (logSlack p.1 p.2.1)
          p.2.2.2.2.2.2 :=
    (Primrec.eq.comp (Primrec.list_length.comp hX) hm).and
      ((muchnik_bitString_mem_primrec.comp Primrec.snd hsnapD).and
        (muchnik_bitString_mem_primrec.comp hX hsnapE))
  have hall : Primrec fun p : ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
      allStrings p.2.2.1 :=
    muchnik_allStrings_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  refine (Primrec.listFilterMap hall (Primrec.ite hpred (Primrec.option_some.comp Primrec.snd)
    (Primrec.const none)).to₂).to_comp.of_eq fun p => ?_
  simp only [muchnikCandidateStage, ← List.filterMap_eq_filter]
  congr 1
  funext Z
  simp [Option.guard]

/-- Every stage output has the advertised left length, including when `a = 0`, because
the outer enumeration is literally `allStrings a`. -/
private theorem muchnikCandidateStage_output_length
    (cD cE : Nat.Partrec.Code) (cGraph n a m : ℕ) (B X Z : BitString) (s : ℕ)
    (hZ : Z ∈ muchnikCandidateStage cD cE cGraph n a m B X s) :
    Z.length = a := by
  unfold muchnikCandidateStage at hZ
  exact (mem_allStrings a Z).1 (List.mem_filter.1 hZ).1

/-- Snapshot soundness for both machine codes turns every retained string into a semantic
candidate; the explicit `|X| = m` guard supplies membership in `allStrings m`. -/
private theorem muchnikCandidateStage_sound
    (D E : Map) (cD cE : Nat.Partrec.Code)
    (hcD : cD.eval = fun q => (Part.ofOption (Encodable.decode q)).bind
      (fun x => Part.map Encodable.encode (D x)))
    (hcE : cE.eval = fun q => (Part.ofOption (Encodable.decode q)).bind
      (fun x => Part.map Encodable.encode (E x)))
    (cGraph n a m : ℕ) (B X Z : BitString) (s : ℕ)
    (hZ : Z ∈ muchnikCandidateStage cD cE cGraph n a m B X s) :
    Z ∈ muchnikCandidates D E a m (logSlack cGraph n) B X := by
  unfold muchnikCandidateStage at hZ
  rw [List.mem_filter] at hZ
  have hZ1 := hZ.1
  rw [mem_allStrings] at hZ1
  have hZ2 := of_decide_eq_true hZ.2
  have hX_len := hZ2.1
  have hZ_snap := hZ2.2.1
  have hX_snap := hZ2.2.2
  unfold conditionalOutputSnapshot at hZ_snap hX_snap
  rw [List.mem_filterMap] at hZ_snap hX_snap
  obtain ⟨p, hp, hZ_run⟩ := hZ_snap
  obtain ⟨q, hq, hX_run⟩ := hX_snap
  rw [mem_boundedPrograms_iff] at hp hq
  have hcD_code : IsCodeFor cD D := hcD
  have hcE_code : IsCodeFor cE E := hcE
  have hp_prod := conditionalRunOut_sound hcD_code hZ_run
  have hq_prod := conditionalRunOut_sound hcE_code hX_run
  unfold muchnikCandidates
  rw [Finset.mem_filter]
  refine ⟨List.mem_toFinset.mpr hZ.1, ?_⟩
  constructor
  · rw [condK_le_iff]
    exact ⟨p, hp, hp_prod⟩
  · unfold muchnikFingerprints
    rw [Finset.mem_filter]
    refine ⟨List.mem_toFinset.mpr ((mem_allStrings m X).mpr hX_len), ?_⟩
    rw [condK_le_iff]
    exact ⟨q, hq, hq_prod⟩

/-- Two producing programs witnessing candidate membership halt at finite stages; their
maximum is a stage at which the filter contains `Z`.  Empty candidate fibres are vacuous. -/
private theorem muchnikCandidateStage_complete
    (D E : Map) (cD cE : Nat.Partrec.Code)
    (hcD : cD.eval = fun q => (Part.ofOption (Encodable.decode q)).bind
      (fun x => Part.map Encodable.encode (D x)))
    (hcE : cE.eval = fun q => (Part.ofOption (Encodable.decode q)).bind
      (fun x => Part.map Encodable.encode (E x)))
    (cGraph n a m : ℕ) (B X Z : BitString)
    (hZ : Z ∈ muchnikCandidates D E a m (logSlack cGraph n) B X) :
    ∃ s : ℕ, Z ∈ muchnikCandidateStage cD cE cGraph n a m B X s := by
  unfold muchnikCandidates at hZ
  rw [Finset.mem_filter] at hZ
  have hZ_len := (mem_allStrings a Z).mp (List.mem_toFinset.mp hZ.1)
  have hZ_cond := hZ.2.1
  have hX_fing := hZ.2.2
  unfold muchnikFingerprints at hX_fing
  rw [Finset.mem_filter] at hX_fing
  have hX_len := (mem_allStrings m X).mp (List.mem_toFinset.mp hX_fing.1)
  have hX_cond := hX_fing.2
  rw [condK_le_iff] at hZ_cond hX_cond
  obtain ⟨p, hp, hZ_prod⟩ := hZ_cond
  obtain ⟨q, hq, hX_prod⟩ := hX_cond
  have hcD_code : IsCodeFor cD D := hcD
  have hcE_code : IsCodeFor cE E := hcE
  obtain ⟨s_D, hs_D⟩ := conditionalRunOut_complete hcD_code hZ_prod
  obtain ⟨s_E, hs_E⟩ := conditionalRunOut_complete hcE_code hX_prod
  let s := max s_D s_E
  refine ⟨s, ?_⟩
  unfold muchnikCandidateStage
  rw [List.mem_filter]
  refine ⟨(mem_allStrings a Z).mpr hZ_len, ?_⟩
  apply decide_eq_true
  refine ⟨hX_len, ?_, ?_⟩
  · apply mem_conditionalOutputSnapshot_of_run hp
    exact conditionalRunOut_mono cD (le_max_left s_D s_E) hs_D
  · apply mem_conditionalOutputSnapshot_of_run hq
    exact conditionalRunOut_mono cE (le_max_right s_D s_E) hs_E

private theorem exists_muchnik_candidate_stage_enumerator
    (D E : Map) (hD : isDecompressor D) (hE : isDecompressor E) :
    ∃ S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString,
      Computable (fun p :
        ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
          S p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
            p.2.2.2.2.2.1 p.2.2.2.2.2.2) ∧
        ∀ (cGraph n a m : ℕ) (B X : BitString),
          (∀ (s : ℕ) (Z : BitString), Z ∈ S cGraph n a m B X s →
            Z ∈ muchnikCandidates D E a m (logSlack cGraph n) B X) ∧
          ∀ Z ∈ muchnikCandidates D E a m (logSlack cGraph n) B X,
            ∃ s : ℕ, Z ∈ S cGraph n a m B X s := by
  obtain ⟨cD, hcD⟩ := Nat.Partrec.Code.exists_code.mp hD
  obtain ⟨cE, hcE⟩ := Nat.Partrec.Code.exists_code.mp hE
  refine ⟨muchnikCandidateStage cD cE, muchnikCandidateStage_computable cD cE, ?_⟩
  intro cGraph n a m B X
  exact ⟨fun s Z hZ => muchnikCandidateStage_sound D E cD cE hcD hcE
      cGraph n a m B X Z s hZ,
    fun Z hZ => muchnikCandidateStage_complete D E cD cE hcD hcE
      cGraph n a m B X Z hZ⟩

/- The duplicate-free history of the stage enumeration, ordered by first
appearance.  Accumulating the stages is necessary because the hypotheses on
`S` do not require the individual stage lists to be monotone. -/
private def muchnikCandidateHistory
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (cGraph n a m : ℕ) (B X : BitString) (s : ℕ) : List BitString :=
  ((List.range (s + 1)).flatMap fun t => S cGraph n a m B X t).eraseDups

/- An output present at one stage occurs in the accumulated history through
that stage. -/
private theorem mem_muchnikCandidateHistory_of_mem_stage
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    {cGraph n a m s : ℕ} {A B X : BitString}
    (hA : A ∈ S cGraph n a m B X s) :
    A ∈ muchnikCandidateHistory S cGraph n a m B X s := by
  rw [muchnikCandidateHistory, mem_eraseDups_list, List.mem_flatMap]
  exact ⟨s, by simp, hA⟩

/- The history has no repetitions, so its length is the number of candidates
that have appeared by that stage. -/
private theorem muchnikCandidateHistory_nodup
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (cGraph n a m : ℕ) (B X : BitString) (s : ℕ) :
    (muchnikCandidateHistory S cGraph n a m B X s).Nodup := by
  exact nodup_eraseDups_list _

/- Once assigned, first-appearance ordinals are stable: the history at an
earlier stage is a prefix of the history at every later stage. -/
private theorem muchnikCandidateHistory_prefix
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (cGraph n a m : ℕ) (B X : BitString) {s s' : ℕ} (hss : s ≤ s') :
    muchnikCandidateHistory S cGraph n a m B X s <+:
      muchnikCandidateHistory S cGraph n a m B X s' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hss
  have hrange : List.range (s + d + 1) =
      List.range (s + 1) ++ (List.range d).map (s + 1 + ·) := by
    rw [show s + d + 1 = (s + 1) + d by omega]
    exact List.range_add
  rw [muchnikCandidateHistory, muchnikCandidateHistory, hrange,
    List.flatMap_append, List.eraseDups_append]
  exact List.prefix_append _ _

/- Completeness supplies a stage containing `A`; soundness and the fibre-cardinality
bound then show that its first-appearance ordinal fits in the prescribed address
space. -/
private theorem exists_bounded_muchnik_candidate_rank
    (D E : Map)
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (hS : ∀ (cGraph n a m : ℕ) (B X : BitString),
      (∀ (s : ℕ) (Z : BitString), Z ∈ S cGraph n a m B X s →
        Z ∈ muchnikCandidates D E a m (logSlack cGraph n) B X) ∧
      ∀ Z ∈ muchnikCandidates D E a m (logSlack cGraph n) B X,
        ∃ s : ℕ, Z ∈ S cGraph n a m B X s)
    (cGraph n a m q : ℕ) (A B X : BitString)
    (hA : A ∈ muchnikCandidates D E a m (logSlack cGraph n) B X)
    (hcard : (muchnikCandidates D E a m (logSlack cGraph n) B X).card ≤ 2 ^ q) :
    ∃ i s : ℕ, i < 2 ^ q ∧
      i < (muchnikCandidateHistory S cGraph n a m B X s).length ∧
      (muchnikCandidateHistory S cGraph n a m B X s).getD i [] = A := by
  obtain ⟨s, hAs⟩ := (hS cGraph n a m B X).2 A hA
  have hAhistory : A ∈ muchnikCandidateHistory S cGraph n a m B X s :=
    mem_muchnikCandidateHistory_of_mem_stage S hAs
  let L := muchnikCandidateHistory S cGraph n a m B X s
  let i := L.idxOf A
  have hi : i < L.length := List.idxOf_lt_length_of_mem hAhistory
  have hsubset : L.toFinset ⊆
      muchnikCandidates D E a m (logSlack cGraph n) B X := by
    intro Z hZ
    rw [List.mem_toFinset] at hZ
    change Z ∈ muchnikCandidateHistory S cGraph n a m B X s at hZ
    rw [muchnikCandidateHistory, mem_eraseDups_list, List.mem_flatMap] at hZ
    obtain ⟨t, _, hZt⟩ := hZ
    exact (hS cGraph n a m B X).1 t Z hZt
  have hlength : L.length ≤
      (muchnikCandidates D E a m (logSlack cGraph n) B X).card := by
    rw [← List.toFinset_card_of_nodup
      (muchnikCandidateHistory_nodup S cGraph n a m B X s)]
    exact Finset.card_le_card hsubset
  refine ⟨i, s, lt_of_lt_of_le hi (hlength.trans hcard), hi, ?_⟩
  rw [List.getD_eq_getElem _ [] hi, List.getElem_idxOf hi]

/-!
Blueprint for the candidate-rank decoder (sound restatement):
1. Assume every string in a history for parameter `a` actually has length `a`.
2. Use a tagged program: tag `false` carries four self-delimiting parameters and rank `i`;
   tag `true` carries the desired output literally.
3. The rank decoder searches for the first history long enough and returns entry `i`.
4. Prove partial recursiveness separately from the size calculation.
5. If `cGraph ≤ n`, all four header values are at most `n`, so the rank branch costs
   `logSlack cBudget n + logSlack 9 n`.
6. If `n < cGraph ≤ cBudget`, the length invariant gives `|A| = a ≤ n`, and the literal
   branch fits inside `logSlack cBudget n`.  This also covers `n = a = m = 0`.
-/

/-- The untagged payload containing the four size parameters and the binary ordinal. -/
private def muchnikRankPayload
    (cGraph n a m i : ℕ) : BitString :=
  pairCode (Nat.bits cGraph) <|
    pairCode (Nat.bits n) <|
      pairCode (Nat.bits a) <|
        pairCode (Nat.bits m) (Nat.bits i)

/-- The ordinary rank program uses tag `false`; tag `true` is reserved for literals. -/
private def muchnikRankProgram
    (cGraph n a m i : ℕ) : BitString :=
  false :: muchnikRankPayload cGraph n a m i

/-- A literal fallback makes large `cGraph` harmless once outputs are known to have length `a`. -/
private def muchnikLiteralProgram (A : BitString) : BitString := true :: A

/-- Search the accumulated history determined by the decoded header and the condition `(B,X)`.
Malformed rank programs merely decode some numeric header and may diverge. -/
private def muchnikRankDecoder
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString) : Map := fun pr =>
  if pr.1.headD false then Part.some pr.1.tail else
    let w₀ := pr.1.tail
    let cGraph := bitsToNat (decodeFirst w₀)
    let w₁ := decodeSecond w₀
    let n := bitsToNat (decodeFirst w₁)
    let w₂ := decodeSecond w₁
    let a := bitsToNat (decodeFirst w₂)
    let w₃ := decodeSecond w₂
    let m := bitsToNat (decodeFirst w₃)
    let i := bitsToNat (decodeSecond w₃)
    let B := decodeFirst pr.2
    let X := decodeSecond pr.2
    (Nat.rfind fun s => Part.some <|
      decide (i < (muchnikCandidateHistory S cGraph n a m B X s).length)).bind
      fun s => Part.some <|
        (muchnikCandidateHistory S cGraph n a m B X s).getD i []

/-- The accumulated stage history is computable in all seven parameters: the union of the
first `s + 1` stages is built by primitive recursion on `s`, and `eraseDups` is primitive
recursive. -/
private theorem muchnikCandidateHistory_computable
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (hScomp : Computable (fun p :
      ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
        S p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
          p.2.2.2.2.2.1 p.2.2.2.2.2.2)) :
    Computable (fun p :
      ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
        muchnikCandidateHistory S p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
          p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  let F : ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) → ℕ → List BitString :=
    fun p t => S p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 t
  have hrepl : Primrec (fun q : (ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ)))))) × ℕ =>
      (q.1.1, q.1.2.1, q.1.2.2.1, q.1.2.2.2.1, q.1.2.2.2.2.1, q.1.2.2.2.2.2.1, q.2)) := by
    have h1 := Primrec.snd.comp (α := (ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ)))))) × ℕ)
      Primrec.fst
    have h2 := Primrec.snd.comp h1
    have h3 := Primrec.snd.comp h2
    have h4 := Primrec.snd.comp h3
    have h5 := Primrec.snd.comp h4
    exact (Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp h1).pair
      ((Primrec.fst.comp h2).pair ((Primrec.fst.comp h3).pair ((Primrec.fst.comp h4).pair
        ((Primrec.fst.comp h5).pair Primrec.snd)))))
  have hF : Computable₂ F := (hScomp.comp hrepl.to_comp).to₂
  have hs : Computable (fun p : ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
      p.2.2.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have hg : Computable (fun p : ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
      F p 0) := hF.comp Computable.id (Computable.const 0)
  have hh : Computable₂ (fun (p : ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))))
      (q : ℕ × List BitString) => q.2 ++ F p (q.1 + 1)) :=
    (Computable.list_append.comp (Computable.snd.comp Computable.snd)
      (hF.comp Computable.fst (Computable.succ.comp (Computable.fst.comp Computable.snd)))).to₂
  have hrec := Computable.nat_rec hs hg hh
  have hacc : ∀ p : ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))), ∀ s : ℕ,
      (List.range (s + 1)).flatMap (F p) =
        Nat.rec (motive := fun _ => List BitString) (F p 0)
          (fun y IH => IH ++ F p (y + 1)) s := by
    intro p s
    induction s with
    | zero => simp
    | succ s ih => rw [List.range_succ, List.flatMap_append, ih]; simp
  refine ((CodedFiniteDistribution.eraseDups_bitstring_primrec).to_comp.comp hrec).of_eq
    fun p => ?_
  simp only [muchnikCandidateHistory]
  rw [← hacc]

/-- Computability of `S` lifts through the history, tuple parsing, bounded list lookup, and
unbounded search for the first sufficiently long history. -/
private theorem muchnikRankDecoder_isDecompressor
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (hScomp : Computable (fun p :
      ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
        S p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
          p.2.2.2.2.2.1 p.2.2.2.2.2.2)) :
    isDecompressor (muchnikRankDecoder S) := by
  have hH := muchnikCandidateHistory_computable S hScomp
  have hw₀ : Computable (fun pr : BitString × BitString => pr.1.tail) :=
    Primrec.list_tail.to_comp.comp Computable.fst
  have hw₁ := decodeSecond_computable.comp hw₀
  have hw₂ := decodeSecond_computable.comp hw₁
  have hw₃ := decodeSecond_computable.comp hw₂
  have hnum : ∀ {f : BitString × BitString → BitString}, Computable f →
      Computable (fun pr => bitsToNat (decodeFirst (f pr))) :=
    fun hf => bitsToNat_computable.comp (decodeFirst_computable.comp hf)
  let P : BitString × BitString → ℕ × (ℕ × (ℕ × (ℕ × (BitString × BitString)))) := fun pr =>
    (bitsToNat (decodeFirst pr.1.tail),
      bitsToNat (decodeFirst (decodeSecond pr.1.tail)),
      bitsToNat (decodeFirst (decodeSecond (decodeSecond pr.1.tail))),
      bitsToNat (decodeFirst (decodeSecond (decodeSecond (decodeSecond pr.1.tail)))),
      decodeFirst pr.2, decodeSecond pr.2)
  have hP : Computable P :=
    (hnum hw₀).pair ((hnum hw₁).pair ((hnum hw₂).pair ((hnum hw₃).pair
      ((decodeFirst_computable.comp Computable.snd).pair
        (decodeSecond_computable.comp Computable.snd)))))
  have happ : Primrec (fun q : (ℕ × (ℕ × (ℕ × (ℕ × (BitString × BitString))))) × ℕ =>
      (q.1.1, q.1.2.1, q.1.2.2.1, q.1.2.2.2.1, q.1.2.2.2.2.1, q.1.2.2.2.2.2, q.2)) := by
    have h1 := Primrec.snd.comp (α := (ℕ × (ℕ × (ℕ × (ℕ × (BitString × BitString))))) × ℕ)
      Primrec.fst
    have h2 := Primrec.snd.comp h1
    have h3 := Primrec.snd.comp h2
    have h4 := Primrec.snd.comp h3
    exact (Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp h1).pair
      ((Primrec.fst.comp h2).pair ((Primrec.fst.comp h3).pair ((Primrec.fst.comp h4).pair
        ((Primrec.snd.comp h4).pair Primrec.snd)))))
  let L : (BitString × BitString) → ℕ → List BitString := fun pr s =>
    muchnikCandidateHistory S (P pr).1 (P pr).2.1 (P pr).2.2.1 (P pr).2.2.2.1
      (P pr).2.2.2.2.1 (P pr).2.2.2.2.2 s
  have hL : Computable₂ L :=
    (hH.comp (happ.to_comp.comp ((hP.comp Computable.fst).pair Computable.snd))).to₂
  have hidx : Computable (fun pr : BitString × BitString =>
      bitsToNat (decodeSecond (decodeSecond (decodeSecond (decodeSecond pr.1.tail))))) :=
    bitsToNat_computable.comp (decodeSecond_computable.comp hw₃)
  have hfind : Partrec (fun pr : BitString × BitString => Nat.rfind fun s => Part.some <|
      decide (bitsToNat (decodeSecond (decodeSecond (decodeSecond (decodeSecond pr.1.tail))))
        < (L pr s).length)) :=
    Partrec.rfind (Computable₂.partrec₂ (Primrec.nat_lt.decide.to_comp.comp
      (hidx.comp Computable.fst) (Primrec.list_length.to_comp.comp hL)).to₂)
  have hget : Computable₂ (fun (pr : BitString × BitString) (s : ℕ) =>
      (L pr s).getD (bitsToNat (decodeSecond (decodeSecond (decodeSecond
        (decodeSecond pr.1.tail))))) []) :=
    ((Primrec.list_getD []).to_comp.comp
      (hL.comp Computable.fst Computable.snd) (hidx.comp Computable.fst)).to₂
  have hbind := Partrec.bind hfind hget.partrec₂
  have hc : Computable (fun pr : BitString × BitString => pr.1.headD false) :=
    ((Primrec.option_getD.comp Primrec.list_head? (Primrec.const false)).to_comp.comp
      Computable.fst).of_eq fun pr => by cases pr.1 <;> rfl
  refine (Partrec.cond hc (Primrec.list_tail.to_comp.comp Computable.fst).partrec hbind).of_eq
    fun pr => ?_
  simp only [muchnikRankDecoder]
  cases pr.1.headD false <;> rfl

/-- A valid ordinal program returns the corresponding history entry.  No monotonicity of
individual stage lists is needed because `muchnikCandidateHistory` is prefix-monotone. -/
private theorem muchnikRankDecoder_rank_produces
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (cGraph n a m i s : ℕ) (A B X : BitString)
    (hi : i < (muchnikCandidateHistory S cGraph n a m B X s).length)
    (hget : (muchnikCandidateHistory S cGraph n a m B X s).getD i [] = A) :
    produces (muchnikRankDecoder S) (muchnikRankProgram cGraph n a m i)
      (pairCode B X) A := by
  obtain ⟨t, ht, hts⟩ := Nat.rfind_min' (p := fun t =>
    decide (i < (muchnikCandidateHistory S cGraph n a m B X t).length))
    (by simpa using hi)
  have hprefix := muchnikCandidateHistory_prefix S cGraph n a m B X hts
  have htlen : i < (muchnikCandidateHistory S cGraph n a m B X t).length := by
    apply of_decide_eq_true
    simpa using Nat.rfind_spec ht
  have htget : (muchnikCandidateHistory S cGraph n a m B X t).getD i [] = A := by
    rw [List.getD_eq_getElem _ [] hi] at hget
    rw [List.getD_eq_getElem _ [] htlen]
    exact (hprefix.getElem htlen).trans hget
  change A ∈ muchnikRankDecoder S
    (muchnikRankProgram cGraph n a m i, pairCode B X)
  simp only [muchnikRankDecoder, muchnikRankProgram, muchnikRankPayload, List.headD_cons,
    Bool.false_eq_true, ite_false, List.tail_cons, decodeFirst_pairCode,
    decodeSecond_pairCode, bitsToNat_bits, Part.mem_bind_iff, Part.mem_some_iff]
  exact ⟨t, ht, htget.symm⟩

/-- The tagged literal branch returns its payload for every condition. -/
private theorem muchnikRankDecoder_literal_produces
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (A B X : BitString) :
    produces (muchnikRankDecoder S) (muchnikLiteralProgram A) (pairCode B X) A := by
  change A ∈ muchnikRankDecoder S (muchnikLiteralProgram A, pairCode B X)
  simp [muchnikRankDecoder, muchnikLiteralProgram]

private theorem bits_length_le_of_lt_pow_two_muchnik {m k : ℕ} (h : m < 2 ^ k) :
    (Nat.bits m).length ≤ k := by
  have hsize : Nat.size m ≤ k := Nat.size_le.mpr h
  rwa [← Nat.size_eq_bits_len] at hsize

/-- Below `2^q`, the ordinal uses at most `q` bits.  When `cGraph ≤ n`, the four
self-delimiting header fields and tag fit in `logSlack 9 n`, including `n = 0`. -/
private theorem muchnikRankProgram_length_le
    (cGraph cBudget n a m i : ℕ)
    (hcgn : cGraph ≤ n) (hma : m ≤ a) (han : a ≤ n)
    (hi : i < 2 ^ logSlack cBudget n) :
    (muchnikRankProgram cGraph n a m i).length ≤
      logSlack cBudget n + logSlack 9 n := by
  dsimp [muchnikRankProgram, muchnikRankPayload]
  simp only [length_pairCode, add_left_comm, add_comm]
  have h1 : (Nat.bits i).length ≤ logSlack cBudget n := bits_length_le_of_lt_pow_two_muchnik hi
  have hs : Nat.size n = (Nat.bits n).length := by rw [Nat.size_eq_bits_len]
  have hn : n < 2 ^ (Nat.bits n).length := hs ▸ Nat.lt_size_self n
  have hc : (Nat.bits cGraph).length ≤ (Nat.bits n).length := by
    apply bits_length_le_of_lt_pow_two_muchnik
    omega
  have ha : (Nat.bits a).length ≤ (Nat.bits n).length := by
    apply bits_length_le_of_lt_pow_two_muchnik
    omega
  have hm : (Nat.bits m).length ≤ (Nat.bits n).length := by
    apply bits_length_le_of_lt_pow_two_muchnik
    omega
  dsimp [logSlack]
  have h2 : logSlack cBudget n = cBudget * (Nat.bits n).length + cBudget := rfl
  rw [h2] at h1
  omega

/-- If `cGraph` exceeds `n`, then `cBudget ≥ cGraph` already pays for a literal `a`-bit
output.  The asserted history-length invariant is exactly what rules out the counterexample. -/
private theorem muchnikLiteralProgram_length_le
    (cGraph cBudget n a : ℕ) (A : BitString)
    (hgc : cGraph ≤ cBudget) (hcgn : n < cGraph) (han : a ≤ n) (hA : A.length = a) :
    (muchnikLiteralProgram A).length ≤
      logSlack cBudget n + logSlack 9 n := by
  simp only [muchnikLiteralProgram, List.length_cons, hA, logSlack]
  omega

private theorem exists_decoder_for_muchnik_candidate_ranks
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (hScomp : Computable (fun p :
      ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
        S p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
          p.2.2.2.2.2.1 p.2.2.2.2.2.2))
    (hSlen : ∀ (cGraph n a m : ℕ) (B X : BitString) (s : ℕ) (Z : BitString),
      Z ∈ muchnikCandidateHistory S cGraph n a m B X s → Z.length = a) :
    ∃ cEnum : ℕ, ∃ F : Map, isDecompressor F ∧
      ∀ (cGraph cBudget n a m i s : ℕ) (A B X : BitString),
        cGraph ≤ cBudget → m ≤ a → a ≤ n → i < 2 ^ logSlack cBudget n →
        i < (muchnikCandidateHistory S cGraph n a m B X s).length →
        (muchnikCandidateHistory S cGraph n a m B X s).getD i [] = A →
        ∃ P : BitString,
          P.length ≤ logSlack cBudget n + logSlack cEnum n ∧
          produces F P (pairCode B X) A := by
  refine ⟨9, muchnikRankDecoder S, muchnikRankDecoder_isDecompressor S hScomp, ?_⟩
  intro cGraph cBudget n a m i s A B X hgc hma han hi hiHistory hget
  by_cases hcgn : cGraph ≤ n
  · exact ⟨muchnikRankProgram cGraph n a m i,
      muchnikRankProgram_length_le cGraph cBudget n a m i hcgn hma han hi,
      muchnikRankDecoder_rank_produces S cGraph n a m i s A B X hiHistory hget⟩
  · have hmem : A ∈ muchnikCandidateHistory S cGraph n a m B X s := by
      rw [List.getD_eq_getElem _ [] hiHistory] at hget
      rw [← hget]
      exact List.getElem_mem hiHistory
    have hA : A.length = a := hSlen cGraph n a m B X s A hmem
    exact ⟨muchnikLiteralProgram A,
      muchnikLiteralProgram_length_le cGraph cBudget n a A hgc
        (Nat.lt_of_not_ge hcgn) han hA,
      muchnikRankDecoder_literal_produces S A B X⟩

/-- Sound stage outputs have length `a`; flattening stages and removing duplicates preserves
that invariant in every accumulated candidate history. -/
private theorem muchnikCandidateHistory_output_length
    (D E : Map)
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (hS : ∀ (cGraph n a m : ℕ) (B X : BitString),
      ∀ (s : ℕ) (Z : BitString), Z ∈ S cGraph n a m B X s →
        Z ∈ muchnikCandidates D E a m (logSlack cGraph n) B X)
    (cGraph n a m : ℕ) (B X : BitString) (s : ℕ) (Z : BitString)
    (hZ : Z ∈ muchnikCandidateHistory S cGraph n a m B X s) :
    Z.length = a := by
  rw [muchnikCandidateHistory, mem_eraseDups_list, List.mem_flatMap] at hZ
  obtain ⟨t, -, hZt⟩ := hZ
  have hcand := hS cGraph n a m B X t Z hZt
  exact (mem_allStrings a Z).1 (List.mem_toFinset.1 (Finset.mem_filter.1 hcand).1)

/- Number the distinct strings as they first appear in the finite stage approximations.
If a fibre has at most `2^q` members, its ordinal uses at most `q` bits; the remaining
self-delimiting size parameters cost one fixed logarithmic slack. -/
private theorem exists_muchnik_candidate_rank_decoder
    (D E : Map)
    (S : ℕ → ℕ → ℕ → ℕ → BitString → BitString → ℕ → List BitString)
    (hScomp : Computable (fun p :
      ℕ × (ℕ × (ℕ × (ℕ × (BitString × (BitString × ℕ))))) =>
        S p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
          p.2.2.2.2.2.1 p.2.2.2.2.2.2))
    (hS : ∀ (cGraph n a m : ℕ) (B X : BitString),
      (∀ (s : ℕ) (Z : BitString), Z ∈ S cGraph n a m B X s →
        Z ∈ muchnikCandidates D E a m (logSlack cGraph n) B X) ∧
      ∀ Z ∈ muchnikCandidates D E a m (logSlack cGraph n) B X,
        ∃ s : ℕ, Z ∈ S cGraph n a m B X s) :
    ∃ cEnum : ℕ, ∃ F : Map, isDecompressor F ∧
      ∀ (cGraph cBad n a m : ℕ) (A B X : BitString),
        m ≤ a → a ≤ n →
        A ∈ muchnikCandidates D E a m (logSlack cGraph n) B X →
        (muchnikCandidates D E a m (logSlack cGraph n) B X).card ≤
          2 ^ logSlack (cGraph + cBad) n →
        ∃ P : BitString,
          P.length ≤ logSlack (cGraph + cBad) n + logSlack cEnum n ∧
          produces F P (pairCode B X) A := by
  obtain ⟨cEnum, F, hF, hDecode⟩ :=
    exists_decoder_for_muchnik_candidate_ranks S hScomp
      (muchnikCandidateHistory_output_length D E S (fun cGraph n a m B X =>
        (hS cGraph n a m B X).1))
  refine ⟨cEnum, F, hF, ?_⟩
  intro cGraph cBad n a m A B X hma han hA hcard
  obtain ⟨i, s, hi, hiHistory, hget⟩ :=
    exists_bounded_muchnik_candidate_rank D E S hS cGraph n a m
      (logSlack (cGraph + cBad) n) A B X hA hcard
  exact hDecode cGraph (cGraph + cBad) n a m i s A B X (by omega)
    hma han hi hiHistory hget

/- Dovetail the two machines on all short programs, retain each new `a`-bit
candidate the first time it appears, and describe `A` by its ordinal. -/
private theorem exists_muchnik_candidate_enumerator
    (D E : Map) (hD : isDecompressor D) (hE : isDecompressor E) :
    ∃ cEnum : ℕ, ∃ F : Map, isDecompressor F ∧
      ∀ (cGraph cBad n a m : ℕ) (A B X : BitString),
        m ≤ a → a ≤ n →
        A ∈ muchnikCandidates D E a m (logSlack cGraph n) B X →
        (muchnikCandidates D E a m (logSlack cGraph n) B X).card ≤
          2 ^ logSlack (cGraph + cBad) n →
        ∃ P : BitString,
          P.length ≤ logSlack (cGraph + cBad + cEnum) n ∧
          produces F P (pairCode B X) A := by
  obtain ⟨S, hScomp, hS⟩ :=
    exists_muchnik_candidate_stage_enumerator D E hD hE
  obtain ⟨cEnum, F, hF, hRank⟩ :=
    exists_muchnik_candidate_rank_decoder D E S hScomp hS
  refine ⟨cEnum, F, hF, ?_⟩
  intro cGraph cBad n a m A B X hma han hmem hcard
  obtain ⟨P, hPlen, hP⟩ := hRank cGraph cBad n a m A B X hma han hmem hcard
  refine ⟨P, ?_, hP⟩
  rw [logSlack_add_constants]
  exact hPlen

/- The fixed simulation overhead can be charged to the logarithmic coefficient.
This is the final numerical step in passing from the enumeration machine to `D`. -/
private theorem muchnik_decode_overhead_le
    (cGraph cBad cEnum cSim n : ℕ) :
    (logSlack (cGraph + cBad + cEnum) n : ℕ∞) + (cSim : ℕ∞) ≤
      (logSlack (cGraph + cBad + (cEnum + cSim)) n : ℕ∞) := by
  exact_mod_cast (show logSlack (cGraph + cBad + cEnum) n + cSim ≤
    logSlack (cGraph + cBad + (cEnum + cSim)) n by
      simp only [logSlack, Nat.add_mul]
      omega)

private theorem condK_recover_of_sparse_muchnik_fingerprint
    (D : Map) (hD : isOptimalConditional D) (E : Map) (hE : isDecompressor E) :
    ∃ cDecode : ℕ, ∀ (cGraph cBad n a m : ℕ) (A B X : BitString),
      m ≤ a → a ≤ n → A.length = a → condK D A B = (m : ℕ∞) →
      X ∈ muchnikFingerprints E m (logSlack cGraph n) A →
      (muchnikCandidates D E a m (logSlack cGraph n) B X).card ≤
        2 ^ logSlack (cGraph + cBad) n →
      condK D A (pairCode B X) ≤
        (logSlack (cGraph + cBad + cDecode) n : ℕ∞) := by
  obtain ⟨cEnum, F, hF, hEnum⟩ :=
    exists_muchnik_candidate_enumerator D E hD.1 hE
  obtain ⟨cSim, hSim⟩ := hD.2 F hF
  refine ⟨cEnum + cSim, ?_⟩
  intro cGraph cBad n a m A B X hma han hA hAB hX hcard
  have hmem : A ∈ muchnikCandidates D E a m (logSlack cGraph n) B X := by
    simp only [muchnikCandidates, Finset.mem_filter, List.mem_toFinset, mem_allStrings]
    exact ⟨hA, hAB.le, hX⟩
  obtain ⟨P, hPlen, hP⟩ := hEnum cGraph cBad n a m A B X hma han hmem hcard
  have hEnumK : condK F A (pairCode B X) ≤
      (logSlack (cGraph + cBad + cEnum) n : ℕ∞) := by
    apply (condK_le_iff F A (pairCode B X) _).2
    exact ⟨P, hPlen, hP⟩
  calc
    condK D A (pairCode B X) ≤
        condK F A (pairCode B X) + (cSim : ℕ∞) := hSim A (pairCode B X)
    _ ≤ (logSlack (cGraph + cBad + cEnum) n : ℕ∞) + (cSim : ℕ∞) := by
      gcongr
    _ ≤ (logSlack (cGraph + cBad + (cEnum + cSim)) n : ℕ∞) :=
      muchnik_decode_overhead_le cGraph cBad cEnum cSim n

private theorem exists_muchnik_fingerprint_boundary
    (D : Map) (hD : isOptimalConditional D) :
    ∃ cBoundary : ℕ, ∀ (n m : ℕ) (A B : BitString), A.length ≤ n →
      condK D A B = (m : ℕ∞) → (m = 0 ∨ A.length < m) →
      ∃ X : BitString, IsMuchnikCode D A B X cBoundary n := by
  obtain ⟨cSelf, hSelf⟩ := condK_self D hD
  let ELeft : Map := fun pr => D (pr.1, decodeFirst pr.2)
  have hELeft : isDecompressor ELeft :=
    Partrec.comp hD.1 (Computable.fst.pair (decodeFirst_computable.comp Computable.snd))
  obtain ⟨cLeft, hLeft⟩ := hD.2 ELeft hELeft
  let ERight : Map := fun pr => D (pr.1, decodeSecond pr.2)
  have hERight : isDecompressor ERight :=
    Partrec.comp hD.1 (Computable.fst.pair (decodeSecond_computable.comp Computable.snd))
  obtain ⟨cRight, hRight⟩ := hD.2 ERight hERight
  obtain ⟨cPlain, hPlain⟩ := plainK_le_length D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  let c := cSelf + cLeft + cRight + cPlain + cCond
  refine ⟨c, fun n m A B _ hm hboundary => ?_⟩
  rcases hboundary with rfl | hmA
  · refine ⟨[], ?_, ?_, ?_⟩
    · simp
    · calc
        condK D [] A ≤ plainK D [] + (cCond : ℕ∞) := hCond [] A
        _ ≤ (cPlain : ℕ∞) + (cCond : ℕ∞) := by
          gcongr
          simpa using hPlain ([] : BitString)
        _ ≤ (logSlack c n : ℕ∞) := by
          exact_mod_cast (show cPlain + cCond ≤ logSlack c n by
            dsimp [c, logSlack]
            omega)
    · calc
        condK D A (pairCode B []) ≤ condK ELeft A (pairCode B []) + (cLeft : ℕ∞) :=
          hLeft A (pairCode B [])
        _ = condK D A B + (cLeft : ℕ∞) := by
          congr 1
          have hset : candidateLengths ELeft A (pairCode B []) =
              candidateLengths D A B := by
            ext k
            constructor
            · rintro ⟨p, hp, rfl⟩
              change A ∈ D (p, decodeFirst (pairCode B [])) at hp
              rw [decodeFirst_pairCode] at hp
              exact ⟨p, hp, rfl⟩
            · rintro ⟨p, hp, rfl⟩
              refine ⟨p, ?_, rfl⟩
              change A ∈ D (p, decodeFirst (pairCode B []))
              rw [decodeFirst_pairCode]
              exact hp
          unfold condK
          rw [hset]
        _ = (cLeft : ℕ∞) := by rw [hm]; simp
        _ ≤ (logSlack c n : ℕ∞) := by
          exact_mod_cast (show cLeft ≤ logSlack c n by
            dsimp [c, logSlack]
            omega)
  · refine ⟨A, ?_, ?_, ?_⟩
    · rw [hm]
      exact_mod_cast (show A.length ≤ m + logSlack c n by omega)
    · exact (hSelf A).trans (by
        exact_mod_cast (show cSelf ≤ logSlack c n by
          dsimp [c, logSlack]
          omega))
    · calc
        condK D A (pairCode B A) ≤ condK ERight A (pairCode B A) + (cRight : ℕ∞) :=
          hRight A (pairCode B A)
        _ = condK D A A + (cRight : ℕ∞) := by
          congr 1
          have hset : candidateLengths ERight A (pairCode B A) =
              candidateLengths D A A := by
            ext k
            constructor
            · rintro ⟨p, hp, rfl⟩
              change A ∈ D (p, decodeSecond (pairCode B A)) at hp
              rw [decodeSecond_pairCode] at hp
              exact ⟨p, hp, rfl⟩
            · rintro ⟨p, hp, rfl⟩
              refine ⟨p, ?_, rfl⟩
              change A ∈ D (p, decodeSecond (pairCode B A))
              rw [decodeSecond_pairCode]
              exact hp
          unfold condK
          rw [hset]
        _ ≤ (cSelf : ℕ∞) + (cRight : ℕ∞) := by gcongr; exact hSelf A
        _ ≤ (logSlack c n : ℕ∞) := by
          exact_mod_cast (show cSelf + cRight ≤ logSlack c n by
            dsimp [c, logSlack]
            omega)

private theorem exists_muchnik_fingerprint_of_length
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n : ℕ) (A B : BitString), A.length ≤ n →
      ∃ X : BitString, IsMuchnikCode D A B X c n := by
  have hExists : ∀ (a m : ℕ), 0 < m → m ≤ a →
      ∃ g : Finset (BitString × BitString), IsMuchnikGraph g a m :=
    fun a m hm hma => exists_muchnik_graph_on_strings a m hm hma
  obtain ⟨G, hGcomp, hG⟩ := exists_computable_muchnik_graph_family hExists
  obtain ⟨cGraph, -, E, hE, hfp⟩ :=
    exists_decompressor_for_muchnik_graph_family G hGcomp hG
  obtain ⟨cBad, hBad⟩ := exists_sparse_muchnik_fingerprint D hD E G hGcomp hG
  obtain ⟨cDecode, hDecode⟩ :=
    condK_recover_of_sparse_muchnik_fingerprint D hD E hE
  obtain ⟨cSim, hSim⟩ := hD.2 E hE
  obtain ⟨cBoundary, hBoundary⟩ := exists_muchnik_fingerprint_boundary D hD
  let c := cGraph + cBad + cDecode + cSim + cBoundary
  refine ⟨c, fun n A B hAn => ?_⟩
  obtain ⟨m, hm⟩ := exists_plainConditionalComplexityValue D hD A B
  by_cases hcore : 0 < m ∧ m ≤ A.length
  · obtain ⟨hmPos, hmA⟩ := hcore
    obtain ⟨X, hX, hcard⟩ := hBad cGraph n A.length m A B hmPos hmA hAn rfl hm
      fun Z hZ => hfp n A.length m Z hmPos hmA hAn hZ
    have hXlen : X.length = m := by
      exact (mem_allStrings m X).mp (List.mem_toFinset.mp (Finset.mem_filter.mp hX).1)
    have hXE : condK E X A ≤ (logSlack cGraph n : ℕ∞) :=
      (Finset.mem_filter.mp hX).2
    have hRecover := hDecode cGraph cBad n A.length m A B X hmA hAn rfl hm hX hcard
    refine ⟨X, ?_, ?_, ?_⟩
    · rw [hXlen, hm]
      exact le_add_right le_rfl
    · calc
        condK D X A ≤ condK E X A + (cSim : ℕ∞) := hSim X A
        _ ≤ (logSlack cGraph n : ℕ∞) + (cSim : ℕ∞) := by gcongr
        _ ≤ (logSlack c n : ℕ∞) := by
          exact_mod_cast (show logSlack cGraph n + cSim ≤ logSlack c n by
            dsimp [c]
            simp only [logSlack, Nat.add_mul]
            omega)
    · exact hRecover.trans (by
        exact_mod_cast (show logSlack (cGraph + cBad + cDecode) n ≤ logSlack c n by
          exact logSlack_mono_left (by dsimp [c]; omega) n))
  · have hboundary : m = 0 ∨ A.length < m := by omega
    obtain ⟨X, hX⟩ := hBoundary n m A B hAn hm hboundary
    refine ⟨X, ?_⟩
    rcases hX with ⟨hLen, hSimple, hRecover⟩
    refine ⟨hLen.trans ?_, hSimple.trans ?_, hRecover.trans ?_⟩
    · gcongr
      exact_mod_cast logSlack_mono_left (by dsimp [c]; omega) n
    · exact_mod_cast logSlack_mono_left (by dsimp [c]; omega) n
    · exact_mod_cast logSlack_mono_left (by dsimp [c]; omega) n

private theorem h_ap (D : Map) (hD : isOptimalConditional D) : ∃ c : ℕ, ∀ A P cStr : BitString,
    produces D P [] A →
    condK D A cStr ≤ condK D P cStr + (c : ℕ∞) := by
  let E : Map := fun pr => (D pr).bind (fun P => D (P, []))
  have hE : isDecompressor E := by
    apply Partrec.bind hD.1
    exact Partrec.comp hD.1 (Computable.snd.pair (Computable.const []))
  obtain ⟨C, hC⟩ := hD.2 E hE
  refine ⟨C, fun A P cStr hP => ?_⟩
  have hleq : condK E A cStr ≤ condK D P cStr := by
    by_cases hinf : condK D P cStr = ⊤
    · rw [hinf]; exact le_top
    · have hd : ∃ k : ℕ, condK D P cStr = k :=
        ⟨(condK D P cStr).toNat, (ENat.natCast_toNat hinf).symm⟩
      rcases hd with ⟨k, hk⟩
      have H : condK D P cStr ≤ ↑k := hk.le
      obtain ⟨p, hp_le, hp_prod⟩ := (condK_le_iff D P cStr k).mp H
      have H2 : condK E A cStr ≤ ↑k := by
        apply (condK_le_iff E A cStr k).mpr
        refine ⟨p, hp_le, ?_⟩
        change A ∈ (D (p, cStr)).bind (fun P => D (P, []))
        rw [Part.mem_bind_iff]
        exact ⟨P, hp_prod, hP⟩
      rw [hk]
      exact H2
  calc condK D A cStr ≤ condK E A cStr + C := hC A cStr
       _ ≤ condK D P cStr + C := add_le_add hleq (le_refl _)

private theorem h_pa (D : Map) (hD : isOptimalConditional D) : ∃ c : ℕ, ∀ A P : BitString,
    produces D P [] A → (P.length : ℕ∞) = plainK D A →
    condK D P A ≤ (logSlack c P.length : ℕ∞) := by
  obtain ⟨C2, hC2⟩ := condK_conditionalShortestDescription_le_log_length D hD
  let E : Map := fun pr => D (pr.1, pairCode pr.2 [])
  have hE : isDecompressor E := by
    have harg : Primrec (fun pr : BitString × BitString =>
        (pr.1, pairCode pr.2 [])) :=
      Primrec.fst.pair
        (CodedFiniteDistribution.pairCode_primrec.comp
          Primrec.snd (Primrec.const []))
    exact (Partrec.comp hD.1 harg.to_comp).of_eq (fun _ => rfl)
  obtain ⟨C3, hC3⟩ := hD.2 E hE
  refine ⟨C2 + C3, fun A P hP hPmin => ?_⟩
  have hl1 : condK D P (pairCode A []) ≤ (logSlack C2 P.length : ℕ∞) := by
    have hplain : plainK D A = condK D A [] := rfl
    have hPmin_rw : (P.length : ℕ∞) = condK D A [] := by rw [← hplain, ← hPmin]
    exact hC2 A [] P hP hPmin_rw
  have hleq : condK E P A ≤ condK D P (pairCode A []) := by
    by_cases hinf : condK D P (pairCode A []) = ⊤
    · rw [hinf]; exact le_top
    · have hd : ∃ k : ℕ, condK D P (pairCode A []) = k :=
        ⟨(condK D P (pairCode A [])).toNat, (ENat.natCast_toNat hinf).symm⟩
      rcases hd with ⟨k, hk⟩
      have H : condK D P (pairCode A []) ≤ ↑k := hk.le
      obtain ⟨p, hp_le, hp_prod⟩ := (condK_le_iff D P (pairCode A []) k).mp H
      have H2 : condK E P A ≤ ↑k := by
        apply (condK_le_iff E P A k).mpr
        refine ⟨p, hp_le, ?_⟩
        change P ∈ D (p, pairCode A [])
        exact hp_prod
      rw [hk]
      exact H2
  have t4 : (logSlack C2 P.length : ℕ∞) + (C3 : ℕ∞) ≤ (logSlack (C2 + C3) P.length : ℕ∞) := by
    have hs : logSlack C2 P.length + C3 ≤ logSlack (C2 + C3) P.length := by
      have heq : logSlack C2 P.length + logSlack C3 P.length = logSlack (C2 + C3) P.length :=
        (logSlack_add_constants C2 C3 P.length).symm
      have hleq2 : C3 ≤ logSlack C3 P.length := Nat.le_add_left C3 (C3 * (P.length).bits.length)
      calc logSlack C2 P.length + C3 ≤ logSlack C2 P.length + logSlack C3 P.length :=
             Nat.add_le_add_left hleq2 _
           _ = logSlack (C2 + C3) P.length := heq
    have hrw : (logSlack C2 P.length : ℕ∞) + (C3 : ℕ∞)
        = ((logSlack C2 P.length + C3 : ℕ) : ENat) := rfl
    rw [hrw]
    exact WithTop.coe_le_coe.mpr hs
  calc condK D P A ≤ condK E P A + (C3 : ℕ∞) := hC3 P A
       _ ≤ condK D P (pairCode A []) + (C3 : ℕ∞) := by
         exact add_le_add hleq (le_refl _)
       _ ≤ (logSlack C2 P.length : ℕ∞) + (C3 : ℕ∞) := by
         exact add_le_add hl1 (le_refl _)
       _ ≤ (logSlack (C2 + C3) P.length : ℕ∞) := t4

private theorem condK_trans_small_second_le (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x y z : BitString) (a b : ℕ),
      condK D y x ≤ (a : ℕ∞) → condK D z y ≤ (b : ℕ∞) →
      condK D z x ≤ ((a + 2 * b + c : ℕ) : ℕ∞) := by
  let E : Map := fun pr =>
    (D (decodeSecond pr.1, pr.2)).bind fun y => D (decodeFirst pr.1, y)
  have hFirst : Partrec (fun pr : BitString × BitString =>
      D (decodeSecond pr.1, pr.2)) :=
    Partrec.comp hD.1
      ((decodeSecond_computable.comp Computable.fst).pair Computable.snd)
  have hSecond : Partrec (fun q : (BitString × BitString) × BitString =>
      D (decodeFirst q.1.1, q.2)) :=
    Partrec.comp hD.1
      ((decodeFirst_computable.comp (Computable.fst.comp Computable.fst)).pair
        Computable.snd)
  have hE : isDecompressor E := Partrec.bind hFirst hSecond
  obtain ⟨c, hc⟩ := hD.2 E hE
  refine ⟨c + 1, fun x y z a b hxy hyz => ?_⟩
  obtain ⟨p, hpLen, hp⟩ := (condK_le_iff D y x a).mp hxy
  obtain ⟨q, hqLen, hq⟩ := (condK_le_iff D z y b).mp hyz
  change p.length ≤ a at hpLen
  change q.length ≤ b at hqLen
  have hProd : produces E (pairCode q p) x z := by
    change z ∈ (D (decodeSecond (pairCode q p), x)).bind fun y =>
      D (decodeFirst (pairCode q p), y)
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    exact Part.mem_bind_iff.mpr ⟨y, hp, hq⟩
  calc
    condK D z x ≤ condK E z x + (c : ℕ∞) := hc z x
    _ ≤ ((pairCode q p).length : ℕ∞) + (c : ℕ∞) := by
      gcongr
      exact sInf_le ⟨pairCode q p, hProd, rfl⟩
    _ ≤ ((a + 2 * b + (c + 1) : ℕ) : ℕ∞) := by
      rw [length_pairCode, ← Nat.cast_add]
      exact_mod_cast (show q.length + 1 + q.length + p.length + c ≤
        a + 2 * b + (c + 1) by omega)

private theorem muchnik_fingerprint_transfer_from_shortest_description
    (D : Map) (hD : isOptimalConditional D) :
    ∃ cTransfer : ℕ, ∀ (cGraph n : ℕ) (A B P X : BitString),
      produces D P [] A → (P.length : ℕ∞) = plainK D A → P.length ≤ n →
      IsMuchnikCode D P B X cGraph n →
      IsMuchnikCode D A B X (cGraph + cTransfer) n := by
  obtain ⟨cAP, hAP⟩ := h_ap D hD
  obtain ⟨cPA, hPA⟩ := h_pa D hD
  obtain ⟨cTrans, hTrans⟩ := condK_trans_visible_le D hD
  obtain ⟨cSmall, hSmall⟩ := condK_trans_small_second_le D hD
  let EId : Map := fun pr => Part.some pr.1
  have hEId : isDecompressor EId := Computable.fst.partrec
  obtain ⟨cId, hId⟩ := hD.2 EId hEId
  refine ⟨2 * cPA + cTrans + cSmall + cAP, ?_⟩
  intro cGraph n A B P X hP hPmin hPn hCode
  rcases hCode with ⟨hLen, hSimple, hRecover⟩
  have hPA' : condK D P A ≤ (logSlack cPA n : ℕ∞) :=
    (hPA A P hP hPmin).trans (by
      exact_mod_cast logSlack_mono_right cPA hPn)
  have hPB : condK D P B ≤
      condK D A B + (logSlack (2 * cPA + cSmall) n : ℕ∞) := by
    have hFinite : condK D A B ≠ ⊤ := by
      apply ne_top_of_le_ne_top (ENat.natCast_ne_top (A.length + cId))
      calc
        condK D A B ≤ condK EId A B + (cId : ℕ∞) := hId A B
        _ ≤ (A.length : ℕ∞) + (cId : ℕ∞) := by
          gcongr
          exact sInf_le ⟨A, Part.mem_some A, rfl⟩
        _ = ((A.length + cId : ℕ) : ℕ∞) := rfl
    let a := (condK D A B).toNat
    have ha : condK D A B = (a : ℕ∞) := (ENat.natCast_toNat hFinite).symm
    have hComp := hSmall B A P a (logSlack cPA n) ha.le hPA'
    rw [ha]
    calc
      (a : ℕ∞) + (logSlack (2 * cPA + cSmall) n : ℕ∞) =
          ((a + logSlack (2 * cPA + cSmall) n : ℕ) : ℕ∞) := rfl
      _ ≥ ((a + 2 * logSlack cPA n + cSmall : ℕ) : ℕ∞) := by
        exact_mod_cast (show a + 2 * logSlack cPA n + cSmall ≤
          a + logSlack (2 * cPA + cSmall) n by
            simp only [logSlack, Nat.add_mul, Nat.mul_assoc]
            omega)
      _ ≥ condK D P B := hComp
  refine ⟨?_, ?_, ?_⟩
  · calc
      (X.length : ℕ∞) ≤
          condK D P B + (logSlack cGraph n : ℕ∞) := hLen
      _ ≤ condK D A B +
          (logSlack (cGraph + (2 * cPA + cTrans + cSmall + cAP)) n : ℕ∞) := by
        calc
          condK D P B + (logSlack cGraph n : ℕ∞) ≤
              (condK D A B + (logSlack (2 * cPA + cSmall) n : ℕ∞)) +
                (logSlack cGraph n : ℕ∞) := by gcongr
          _ = condK D A B + ((logSlack (2 * cPA + cSmall) n : ℕ∞) +
                (logSlack cGraph n : ℕ∞)) := add_assoc _ _ _
          _ ≤ condK D A B +
              (logSlack (cGraph + (2 * cPA + cTrans + cSmall + cAP)) n : ℕ∞) := by
            gcongr
            exact_mod_cast (show logSlack (2 * cPA + cSmall) n + logSlack cGraph n ≤
              logSlack (cGraph + (2 * cPA + cTrans + cSmall + cAP)) n by
                simp only [logSlack, Nat.add_mul, Nat.mul_assoc]
                omega)
  · have hComp := hTrans A P X (logSlack cPA n) (logSlack cGraph n) hPA' hSimple
    exact hComp.trans (by
      exact_mod_cast (show 2 * logSlack cPA n + logSlack cGraph n + cTrans ≤
        logSlack (cGraph + (2 * cPA + cTrans + cSmall + cAP)) n by
          simp only [logSlack, Nat.add_mul, Nat.mul_assoc]
          omega))
  · calc
      condK D A (pairCode B X) ≤ condK D P (pairCode B X) + (cAP : ℕ∞) :=
        hAP A P (pairCode B X) hP
      _ ≤ (logSlack cGraph n : ℕ∞) + (cAP : ℕ∞) := by gcongr
      _ ≤ (logSlack (cGraph + (2 * cPA + cTrans + cSmall + cAP)) n : ℕ∞) := by
        exact_mod_cast (show logSlack cGraph n + cAP ≤
          logSlack (cGraph + (2 * cPA + cTrans + cSmall + cAP)) n by
            simp only [logSlack, Nat.add_mul, Nat.mul_assoc]
            omega)

private theorem exists_muchnik_fingerprint_of_complexity_left
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n : ℕ) (A B : BitString), plainK D A ≤ (n : ℕ∞) →
      ∃ X : BitString, IsMuchnikCode D A B X c n := by
  obtain ⟨cGraph, hGraph⟩ := exists_muchnik_fingerprint_of_length D hD
  obtain ⟨cTransfer, hTransfer⟩ :=
    muchnik_fingerprint_transfer_from_shortest_description D hD
  refine ⟨cGraph + cTransfer, ?_⟩
  intro n A B hA
  obtain ⟨P, hP, hP_le, hPmin⟩ := exists_shortest_description_of_plainK_le D hA
  obtain ⟨X, hX⟩ := hGraph n P B hP_le
  exact ⟨X, hTransfer cGraph n A B P X hP hPmin hP_le hX⟩

/-- Muchnik's theorem: for strings `A` and `B` of complexity at most `n` there is a string `X`
of length at most `C(A|B) + O(log n)` with `C(X|A) = O(log n)` and `C(A|B,X) = O(log n)`.  The
constant does not depend on `n`, `A`, `B`.

SUV Theorem 229, p. 370. -/
theorem exists_muchnikCode (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n : ℕ) (A B : BitString),
      plainK D A ≤ (n : ℕ∞) → plainK D B ≤ (n : ℕ∞) →
      ∃ X : BitString,
        (X.length : ℕ∞) ≤ condK D A B + (logSlack c n : ℕ∞) ∧
        condK D X A ≤ (logSlack c n : ℕ∞) ∧
        condK D A (pairCode B X) ≤ (logSlack c n : ℕ∞) := by
  obtain ⟨c, hc⟩ := exists_muchnik_fingerprint_of_complexity_left D hD
  refine ⟨c, fun n A B hA _ => ?_⟩
  simpa only [IsMuchnikCode] using hc n A B hA

/-- The proof of Muchnik's theorem never uses the bound on the complexity of `B`: the same
conclusion holds under the hypothesis on `A` alone.

SUV Problem 319, p. 373. -/
theorem exists_muchnikCode_of_complexity_left (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n : ℕ) (A B : BitString), plainK D A ≤ (n : ℕ∞) →
      ∃ X : BitString,
        (X.length : ℕ∞) ≤ condK D A B + (logSlack c n : ℕ∞) ∧
        condK D X A ≤ (logSlack c n : ℕ∞) ∧
        condK D A (pairCode B X) ≤ (logSlack c n : ℕ∞) := by
  simpa only [IsMuchnikCode] using
    exists_muchnik_fingerprint_of_complexity_left D hD

/-- The request of SUV Figure 40 on three nodes: `0` holds `A`, `1` holds `B`, the channel
`0 → 2` has capacity `k`, the channel `1 → 2` is unlimited, and `2` must produce `A`.  Unlike
Figure 39, the encoder does not see `B`.

SUV Figure 40, p. 369. -/
def muchnikRequest (A B : BitString) (k : ℕ) : InformationRequest (Fin 3) where
  edges := {(0, 2), (1, 2)}
  rank v := if v.val ≤ 1 then 0 else 1
  rank_lt := by decide +kernel
  capacity e := if e = (0, 2) then (k : ℕ∞) else ⊤
  input v := if v = 0 then some A else if v = 1 then some B else none
  output v := if v = 2 then some A else none

/-- The cut of SUV Figure 40 that contains the node of `B` and the decoder: only the channel of
capacity `k` enters it, its input is `B` and its output is `A`, which gives the necessary
condition `C(A|B) ≤ k` of Muchnik's theorem.

SUV Problem 327, p. 384. -/
theorem muchnikRequest_cut (A B : BitString) (k : ℕ) :
    (muchnikRequest A B k).cutCapacity {1, 2} = (k : ℕ∞) ∧
      (muchnikRequest A B k).cutInputs {1, 2} = [B] ∧
      (muchnikRequest A B k).cutOutputs {1, 2} = [A] := by
  have hs : ({1, 2} : Finset (Fin 3)).sort (· ≤ ·) = [1, 2] := by
    rw [Finset.sort_insert]
    · simp
    · simp
    · simp
  have he : (muchnikRequest A B k).cutEdges {1, 2} = {(0, 2)} := by
    ext e
    rcases e with ⟨u, v⟩
    simp [InformationRequest.cutEdges, muchnikRequest, Prod.ext_iff]
    aesop
  rw [InformationRequest.cutCapacity, he, InformationRequest.cutInputs,
    InformationRequest.cutOutputs, hs]
  simp [muchnikRequest]

end Kolmogorov
