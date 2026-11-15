import KolmogorovMathlib.Complexity.GeneralScheme.DecisionBasic
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity

/-!
# Minimality

Minimality of the optimal decision complexity `KROf` among upper semicomputable functions in the
general scheme of decision complexities: `KROf_le_of_isUpperSemicomputable` bounds `KROf` above
by any upper semicomputable function satisfying the counting condition, up to an additive
constant.  The private lemmas build, from a computable enumeration of certificates `k x < m`, a
decision decompressor on descriptions of each length.  The module also compares `KROf` with the
a priori complexity (`exists_const_KROf_le_KA`) and identifies the range of `KROf` with the range
of the complexity of continuous decision maps (`range_KROf_eq_range_contDecisionMap_complexity`).
It belongs to the part of the book by Shen, Uspensky and Vereshchagin on the general scheme for
the definition of complexities.
-/

namespace Kolmogorov
namespace GeneralScheme

/-- Step 1 of the proof of `KROf_le_of_isUpperSemicomputable`: an upper semicomputable
`k` has a computable enumeration `e` of "certificates" `(x, m)` with `k x < m`, in which every
fact `k x < n` is witnessed by some `(x, m)` with `m ≤ n` (take `e s` from a dovetailed search of
a stage approximation of the enumerable upper graph `{(x, n) | k x < n}`). -/
private theorem KROf_le_of_isUpperSemicomputable_enumeration
    (k : BitString → ℕ∞) (hk : IsUpperSemicomputable k) :
    ∃ e : ℕ → Option (BitString × ℕ), Computable e ∧
      (∀ (s : ℕ) (x : BitString) (m : ℕ), e s = some (x, m) → k x < m) ∧
      (∀ (x : BitString) (n : ℕ), k x < n → ∃ (s m : ℕ), m ≤ n ∧ e s = some (x, m)) := by
  obtain ⟨chk, hchk, -, hiff⟩ := IsRE.exists_stageApprox hk
  let e : ℕ → Option (BitString × ℕ) := fun s =>
    (Encodable.decode (α := BitString × ℕ) (Nat.unpair s).1).bind
      (fun a => bif chk a (Nat.unpair s).2 then some a else none)
  have he : Computable e := by
    refine Computable.option_bind
      (Computable.decode.comp (Computable.fst.comp Computable.unpair)) ?_
    refine Computable.cond ?_ (Computable.option_some.comp Computable.snd) (Computable.const none)
    exact hchk.comp (Computable.snd) (Computable.snd.comp (Computable.unpair.comp Computable.fst))
  refine ⟨e, he, ?_, ?_⟩
  · intro s x m hs
    simp only [e] at hs
    cases hd : Encodable.decode (α := BitString × ℕ) (Nat.unpair s).1 with
    | none => simp [hd] at hs
    | some a =>
      rw [hd] at hs
      cases hc : chk a (Nat.unpair s).2 with
      | false => simp [hc] at hs
      | true =>
        have hs' : a = (x, m) := by simpa [hc] using hs
        subst hs'
        exact (hiff (x, m)).mpr ⟨_, hc⟩
  · intro x n hxn
    obtain ⟨t, ht⟩ := (hiff (x, n)).mp hxn
    refine ⟨Nat.pair (Encodable.encode (x, n)) t, n, le_rfl, ?_⟩
    simp [e, ht]

private def KROf_le_of_isUpperSemicomputable_labelling_step (N : ℕ) (st : List (BitString ×
    BitString)) (x : BitString) :
    List (BitString × BitString) :=
  if st.any (fun q => x.isPrefixOf q.1) then st
  else if st.any (fun q => q.1.isPrefixOf x) then
    st.map (fun q => if q.1.isPrefixOf x then (x, q.2) else q)
  else match (bitStringsOfLength N).find? (fun p => !(decide (p ∈ st.map Prod.snd))) with
    | some p => st ++ [(x, p)]
    | none => st

private def KROf_le_of_isUpperSemicomputable_labelling_F (N : ℕ) (l : List BitString) : List
    (BitString × BitString) :=
  l.foldl (KROf_le_of_isUpperSemicomputable_labelling_step N) []

private def KROf_le_of_isUpperSemicomputable_labelling_Inv (N : ℕ) (l : List BitString) (st :
    List (BitString × BitString)) : Prop :=
  (∀ q ∈ st, q.2.length = N ∧ q.1 ∈ l) ∧ (st.map Prod.snd).Nodup ∧
    (∀ q ∈ st, ∀ q' ∈ st, q.1 <+: q'.1 → q = q')

private lemma KROf_le_of_isUpperSemicomputable_labelling_nodup_bits : ∀ s, (bitStringsOfLength
    s).Nodup
  | 0 => by simp [bitStringsOfLength]
  | s + 1 => by
    have ih := KROf_le_of_isUpperSemicomputable_labelling_nodup_bits s
    simp only [bitStringsOfLength]
    rw [List.nodup_append]
    refine ⟨ih.map (fun a b h => by simpa using h), ih.map (fun a b h => by simpa using h), ?_⟩
    intro a ha b hb hab
    simp only [List.mem_map] at ha hb
    obtain ⟨a', _, rfl⟩ := ha
    obtain ⟨b', _, rfl⟩ := hb
    simp at hab

private lemma KROf_le_of_isUpperSemicomputable_labelling_step_inv (N : ℕ) (l : List BitString)
    (st : List (BitString × BitString))
    (x : BitString) (h : KROf_le_of_isUpperSemicomputable_labelling_Inv N l st) :
        KROf_le_of_isUpperSemicomputable_labelling_Inv N (l ++ [x])
        (KROf_le_of_isUpperSemicomputable_labelling_step N st x) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold KROf_le_of_isUpperSemicomputable_labelling_step
  by_cases hA : st.any (fun q => x.isPrefixOf q.1) = true
  · rw [ite_eq_left hA]
    exact ⟨fun q hq => ⟨(h1 q hq).1, List.mem_append_left _ (h1 q hq).2⟩, h2, h3⟩
  · rw [ite_eq_right hA]
    have hA' : ∀ q ∈ st, ¬ x <+: q.1 := by
      intro q hq hp
      apply hA
      rw [List.any_eq_true]
      exact ⟨q, hq, by simpa [List.isPrefixOf_iff_prefix] using hp⟩
    by_cases hB : st.any (fun q => q.1.isPrefixOf x) = true
    · rw [ite_eq_left hB]
      obtain ⟨q0, hq0, hq0x⟩ := List.any_eq_true.mp hB
      have hq0x : q0.1 <+: x := by simpa [List.isPrefixOf_iff_prefix] using hq0x
      have huniq : ∀ q ∈ st, q.1 <+: x → q = q0 := by
        intro q hq hqx
        rcases le_total q.1.length q0.1.length with hle | hle
        · exact h3 q hq q0 hq0 (List.prefix_of_prefix_length_le hqx hq0x hle)
        · exact (h3 q0 hq0 q hq (List.prefix_of_prefix_length_le hq0x hqx hle)).symm
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
        by_cases hrx : r.1.isPrefixOf x = true
        · simp only [hrx, ite_true]
          exact ⟨(h1 r hr).1, List.mem_append_right _ (by simp)⟩
        · simp only [hrx]
          exact ⟨(h1 r hr).1, List.mem_append_left _ (h1 r hr).2⟩
      · rw [List.map_map]
        convert h2 using 2
        funext r
        by_cases hrx : r.1 <+: x <;> simp [hrx]
      · intro q hq q' hq' hqq'
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
        obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hq'
        by_cases hrx : r.1.isPrefixOf x = true <;> by_cases hrx' : r'.1.isPrefixOf x = true
        · simp only [hrx, hrx', ite_true]
          have e1 := huniq r hr (by simpa [List.isPrefixOf_iff_prefix] using hrx)
          have e2 := huniq r' hr' (by simpa [List.isPrefixOf_iff_prefix] using hrx')
          rw [e1, e2]
        · simp only [hrx, hrx', ite_true] at hqq'
          exact absurd hqq' (hA' r' hr')
        · simp only [hrx, hrx', ite_true] at hqq'
          exact absurd hqq' (by simpa [List.isPrefixOf_iff_prefix] using hrx)
        · simp only [hrx, hrx'] at hqq' ⊢
          exact h3 r hr r' hr' hqq'
    · rw [ite_eq_right hB]
      have hB' : ∀ q ∈ st, ¬ q.1 <+: x := by
        intro q hq hp
        apply hB
        rw [List.any_eq_true]
        exact ⟨q, hq, by simpa [List.isPrefixOf_iff_prefix] using hp⟩
      cases hf : (bitStringsOfLength N).find? (fun p => !(decide (p ∈ st.map Prod.snd))) with
      | none =>
        exact ⟨fun q hq => ⟨(h1 q hq).1, List.mem_append_left _ (h1 q hq).2⟩, h2, h3⟩
      | some p =>
        have hp1 := List.mem_of_find?_eq_some hf
        have hp2 := List.find?_some hf
        have hpN : p.length = N := length_of_mem_bitStringsOfLength hp1
        have hp3 : p ∉ st.map Prod.snd := by simpa using hp2
        refine ⟨?_, ?_, ?_⟩
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact ⟨(h1 q hq).1, List.mem_append_left _ (h1 q hq).2⟩
          · rw [List.mem_singleton] at hq
            subst hq
            exact ⟨hpN, List.mem_append_right _ (by simp)⟩
        · rw [List.map_append, List.nodup_append]
          refine ⟨h2, by simp, ?_⟩
          intro a ha b hb
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          rintro rfl
          exact hp3 (hb ▸ ha)
        · intro q hq q' hq' hqq'
          rcases List.mem_append.mp hq with hq | hq <;>
            rcases List.mem_append.mp hq' with hq' | hq'
          · exact h3 q hq q' hq' hqq'
          · rw [List.mem_singleton] at hq'
            subst hq'
            exact absurd hqq' (hB' q hq)
          · rw [List.mem_singleton] at hq
            subst hq
            exact absurd hqq' (hA' q' hq')
          · rw [List.mem_singleton] at hq hq'
            rw [hq, hq']

private lemma KROf_le_of_isUpperSemicomputable_labelling_F_inv (N : ℕ) : ∀ l,
    KROf_le_of_isUpperSemicomputable_labelling_Inv N l
    (KROf_le_of_isUpperSemicomputable_labelling_F N l) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => exact ⟨by simp [KROf_le_of_isUpperSemicomputable_labelling_F], by simp
      [KROf_le_of_isUpperSemicomputable_labelling_F], by simp
      [KROf_le_of_isUpperSemicomputable_labelling_F]⟩
  | append_singleton l x ih =>
    have : KROf_le_of_isUpperSemicomputable_labelling_F N (l ++ [x]) =
        KROf_le_of_isUpperSemicomputable_labelling_step N
        (KROf_le_of_isUpperSemicomputable_labelling_F N l) x := by simp
        [KROf_le_of_isUpperSemicomputable_labelling_F]
    rw [this]
    exact KROf_le_of_isUpperSemicomputable_labelling_step_inv N l _ x ih

private lemma KROf_le_of_isUpperSemicomputable_labelling_step_persist (N : ℕ) (st : List
    (BitString × BitString)) (x : BitString)
    (q : BitString × BitString) (hq : q ∈ st) :
    ∃ q' ∈ KROf_le_of_isUpperSemicomputable_labelling_step N st x, q'.2 = q.2 ∧ q.1 <+: q'.1
        := by
  unfold KROf_le_of_isUpperSemicomputable_labelling_step
  by_cases hA : st.any (fun q => x.isPrefixOf q.1) = true
  · rw [ite_eq_left hA]; exact ⟨q, hq, rfl, List.prefix_refl _⟩
  · rw [ite_eq_right hA]
    by_cases hB : st.any (fun q => q.1.isPrefixOf x) = true
    · rw [ite_eq_left hB]
      by_cases hqx : q.1.isPrefixOf x = true
      · exact ⟨(x, q.2), List.mem_map.mpr ⟨q, hq, by simp [hqx]⟩, rfl,
          by simpa [List.isPrefixOf_iff_prefix] using hqx⟩
      · exact ⟨q, List.mem_map.mpr ⟨q, hq, by simp [hqx]⟩, rfl, List.prefix_refl _⟩
    · rw [ite_eq_right hB]
      cases hf : (bitStringsOfLength N).find? (fun p => !(decide (p ∈ st.map Prod.snd))) with
      | none => exact ⟨q, hq, rfl, List.prefix_refl _⟩
      | some p => exact ⟨q, List.mem_append_left _ hq, rfl, List.prefix_refl _⟩

private lemma KROf_le_of_isUpperSemicomputable_labelling_step_cover (N : ℕ) (l : List
    BitString) (st : List (BitString × BitString))
    (x : BitString) (h : KROf_le_of_isUpperSemicomputable_labelling_Inv N l st)
    (hS : ∀ S : Set BitString, S ⊆ {y | y ∈ l ++ [x]} → IsPrefixFree S → S.encard ≤ (2 : ℕ∞) ^ N)
    (hc : ∀ y ∈ l, ∃ q ∈ st, y <+: q.1) :
    ∀ y ∈ l ++ [x], ∃ q ∈ KROf_le_of_isUpperSemicomputable_labelling_step N st x, y <+: q.1 :=
        by
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨q, hq, hyq⟩ := hc y hy
    obtain ⟨q', hq', -, hqq'⟩ := KROf_le_of_isUpperSemicomputable_labelling_step_persist N st
        x q hq
    exact ⟨q', hq', hyq.trans hqq'⟩
  rw [List.mem_singleton] at hy
  subst hy
  obtain ⟨h1, h2, h3⟩ := h
  unfold KROf_le_of_isUpperSemicomputable_labelling_step
  by_cases hA : st.any (fun q => y.isPrefixOf q.1) = true
  · rw [ite_eq_left hA]
    obtain ⟨q, hq, hqx⟩ := List.any_eq_true.mp hA
    exact ⟨q, hq, by simpa [List.isPrefixOf_iff_prefix] using hqx⟩
  · rw [ite_eq_right hA]
    have hA' : ∀ q ∈ st, ¬ y <+: q.1 := by
      intro q hq hp
      apply hA
      rw [List.any_eq_true]
      exact ⟨q, hq, by simpa [List.isPrefixOf_iff_prefix] using hp⟩
    by_cases hB : st.any (fun q => q.1.isPrefixOf y) = true
    · rw [ite_eq_left hB]
      obtain ⟨q0, hq0, hq0x⟩ := List.any_eq_true.mp hB
      exact ⟨(y, q0.2), List.mem_map.mpr ⟨q0, hq0, by simp [hq0x]⟩, List.prefix_refl _⟩
    · rw [ite_eq_right hB]
      have hB' : ∀ q ∈ st, ¬ q.1 <+: y := by
        intro q hq hp
        apply hB
        rw [List.any_eq_true]
        exact ⟨q, hq, by simpa [List.isPrefixOf_iff_prefix] using hp⟩
      cases hf : (bitStringsOfLength N).find? (fun p => !(decide (p ∈ st.map Prod.snd))) with
      | some p => exact ⟨(y, p), List.mem_append_right _ (by simp), List.prefix_refl _⟩
      | none =>
        exfalso
        have hall : ∀ p ∈ bitStringsOfLength N, p ∈ st.map Prod.snd := by
          intro p hp
          have := List.find?_eq_none.mp hf p hp
          simpa using this
        have hsub : (bitStringsOfLength N).Subperm (st.map Prod.snd) :=
          (KROf_le_of_isUpperSemicomputable_labelling_nodup_bits N).subperm hall
        have hlen : 2 ^ N ≤ st.length := by
          have := hsub.length_le
          rwa [length_bitStringsOfLength, List.length_map] at this
        have hnd : st.Nodup := List.Nodup.of_map _ h2
        have hinj : Set.InjOn Prod.fst (st.toFinset : Set (BitString × BitString)) := by
          intro q hq q' hq' he
          exact h3 q (by simpa using hq) q' (by simpa using hq') (by rw [he])
        have hnot : y ∉ st.toFinset.image Prod.fst := by
          intro hm
          obtain ⟨q, hq, hqy⟩ := Finset.mem_image.mp hm
          exact hA' q (by simpa using hq) (by rw [hqy])
        let S : Finset BitString := insert y (st.toFinset.image Prod.fst)
        have hcard : S.card = st.length + 1 := by
          rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj,
            List.toFinset_card_of_nodup hnd]
        have hsubS : (S : Set BitString) ⊆ {z | z ∈ l ++ [y]} := by
          intro z hz
          simp only [S, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
            Finset.mem_image, List.mem_toFinset] at hz
          rcases hz with rfl | ⟨q, hq, rfl⟩
          · simp
          · exact List.mem_append_left _ (h1 q hq).2
        have hpf : IsPrefixFree (S : Set BitString) := by
          intro a ha b hb hab
          simp only [S, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
            Finset.mem_image, List.mem_toFinset] at ha hb
          rcases ha with rfl | ⟨q, hq, rfl⟩ <;> rcases hb with rfl | ⟨q', hq', rfl⟩
          · rfl
          · exact absurd hab (hA' q' hq')
          · exact absurd hab (hB' q hq)
          · rw [h3 q hq q' hq' hab]
        have := hS _ hsubS hpf
        rw [Set.encard_coe_eq_coe_finsetCard, hcard] at this
        have h' : st.length + 1 ≤ 2 ^ N := by exact_mod_cast this
        omega

private lemma KROf_le_of_isUpperSemicomputable_labelling_primrec_bits : Primrec
    bitStringsOfLength := by
  have h : bitStringsOfLength = fun s => Nat.rec [[]]
      (fun _ IH => IH.map (fun x => false :: x) ++ IH.map (fun x => true :: x)) s := by
    funext s
    induction s with
    | zero => rfl
    | succ s ih =>
      dsimp [bitStringsOfLength]
      rw [ih]
  rw [h]
  apply Primrec.nat_rec₁
  apply Primrec.list_append.comp
  · apply Primrec.list_map Primrec₂.right
    apply Primrec.list_cons.comp (Primrec.const false) Primrec₂.right
  · apply Primrec.list_map Primrec₂.right
    apply Primrec.list_cons.comp (Primrec.const true) Primrec₂.right

private lemma KROf_le_of_isUpperSemicomputable_step2_labelling_find?_eq_getElem?_findIdx {α : Type*}
    (p : α → Bool) (l : List α) :
    l.find? p = l[l.findIdx p]? := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.findIdx_cons, List.find?_cons]
    by_cases h : p a <;> simp [h, ih]

private lemma KROf_le_of_isUpperSemicomputable_step2_labelling_primrec_find? {α β : Type*}
    [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) :=
  (Primrec.list_getElem?.comp hf (Primrec.list_findIdx hf hp)).of_eq fun a =>
    (KROf_le_of_isUpperSemicomputable_step2_labelling_find?_eq_getElem?_findIdx (p a) (f a)).symm

private lemma KROf_le_of_isUpperSemicomputable_labelling_primrec_isPrefixOf : Primrec₂ (fun l1
    l2 : BitString => l1.isPrefixOf l2) := by
  have htake : Primrec (fun p : BitString × BitString => p.2.take p.1.length) :=
    Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd
  have hrel : PrimrecPred (fun p : BitString × BitString => p.2.take p.1.length = p.1) :=
    PrimrecRel.comp Primrec.eq htake Primrec.fst
  exact (Primrec.ite hrel (Primrec.const true) (Primrec.const false)).of_eq fun p => by
    dsimp only
    by_cases h : p.2.take p.1.length = p.1
    · have : p.1 <+: p.2 := by rw [List.prefix_iff_eq_take]; exact h.symm
      simp [h, List.isPrefixOf_iff_prefix, this]
    · have : ¬ p.1 <+: p.2 := by rw [List.prefix_iff_eq_take]; exact fun h' => h h'.symm
      have h2 : p.1.isPrefixOf p.2 = false := by
        rw [Bool.eq_false_iff]; intro hh; exact this (List.isPrefixOf_iff_prefix.mp hh)
      simp [h, h2]

private lemma KROf_le_of_isUpperSemicomputable_labelling_primrec_step :
    Primrec (fun t : ℕ × List (BitString × BitString) × BitString =>
      KROf_le_of_isUpperSemicomputable_labelling_step t.1 t.2.1 t.2.2) := by
  have hN : Primrec (fun t : ℕ × List (BitString × BitString) × BitString => t.1) := Primrec.fst
  have hst : Primrec (fun t : ℕ × List (BitString × BitString) × BitString => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun t : ℕ × List (BitString × BitString) × BitString => t.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hpre := KROf_le_of_isUpperSemicomputable_labelling_primrec_isPrefixOf
  have hA : Primrec (fun t : ℕ × List (BitString × BitString) × BitString =>
      t.2.1.any (fun q => t.2.2.isPrefixOf q.1)) :=
    list_any_primrec hst (hpre.comp (hx.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
  have hB : Primrec (fun t : ℕ × List (BitString × BitString) × BitString =>
      t.2.1.any (fun q => q.1.isPrefixOf t.2.2)) :=
    list_any_primrec hst (hpre.comp (Primrec.fst.comp Primrec.snd) (hx.comp Primrec.fst))
  have hmap : Primrec (fun t : ℕ × List (BitString × BitString) × BitString =>
      t.2.1.map (fun q => if q.1.isPrefixOf t.2.2 then (t.2.2, q.2) else q)) :=
    Primrec.list_map hst
      (Primrec.cond (hpre.comp (Primrec.fst.comp Primrec.snd) (hx.comp Primrec.fst))
        (Primrec.pair (hx.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)) Primrec.snd).to₂
        |>.of_eq fun t => by
          simp only [Bool.cond_eq_ite]
  have hmem : Primrec₂ (fun (t : ℕ × List (BitString × BitString) × BitString) (p : BitString) =>
      !(decide (p ∈ t.2.1.map Prod.snd))) :=
    (Primrec.not.comp (listMemDecide_primrec.comp Primrec.snd
      (Primrec.list_map (hst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd).to₂))).of_eq
      fun p => by congr
  have hfind : Primrec (fun t : ℕ × List (BitString × BitString) × BitString =>
      (bitStringsOfLength t.1).find? (fun p => !(decide (p ∈ t.2.1.map Prod.snd)))) :=
    KROf_le_of_isUpperSemicomputable_step2_labelling_primrec_find?
        (KROf_le_of_isUpperSemicomputable_labelling_primrec_bits.comp hN) hmem
  have hcase : Primrec (fun t : ℕ × List (BitString × BitString) × BitString =>
      match (bitStringsOfLength t.1).find? (fun p => !(decide (p ∈ t.2.1.map Prod.snd))) with
      | some p => t.2.1 ++ [(t.2.2, p)]
      | none => t.2.1) := by
    have hg : Primrec₂ (fun (t : ℕ × List (BitString × BitString) × BitString) (p : BitString) =>
        t.2.1 ++ [(t.2.2, p)]) :=
      (Primrec.list_append.comp (hst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.pair (hx.comp Primrec.fst) Primrec.snd)
          (Primrec.const []))).to₂
    refine (Primrec.option_casesOn hfind hst hg).of_eq fun t => ?_
    cases (bitStringsOfLength t.1).find? (fun p => !(decide (p ∈ t.2.1.map Prod.snd))) <;> rfl
  refine (Primrec.cond hA hst (Primrec.cond hB hmap hcase)).of_eq fun t => ?_
  simp only [KROf_le_of_isUpperSemicomputable_labelling_step, Bool.cond_eq_ite]

private lemma KROf_le_of_isUpperSemicomputable_labelling_computable : Computable₂
    KROf_le_of_isUpperSemicomputable_labelling_F := by
  have h0 : Computable (fun t : (ℕ × List BitString) × (List (BitString × BitString) × BitString) =>
      KROf_le_of_isUpperSemicomputable_labelling_step t.1.1 t.2.1 t.2.2) :=
    Computable.comp (g := fun t : (ℕ × List BitString) × (List (BitString × BitString) × BitString)
        =>
        ((t.1.1, t.2) : ℕ × List (BitString × BitString) × BitString))
      KROf_le_of_isUpperSemicomputable_labelling_primrec_step.to_comp
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have h : Computable₂ (fun (p : ℕ × List BitString) (sb : List (BitString × BitString) × BitString)
      =>
      KROf_le_of_isUpperSemicomputable_labelling_step p.1 sb.1 sb.2) := h0
  have hl : Computable (fun p : ℕ × List BitString => p.2) := Computable.snd
  have hg : Computable (fun _ : ℕ × List BitString => ([] : List (BitString × BitString))) :=
    Computable.const _
  have key := Computable.list_foldl (α := ℕ × List BitString) (β := BitString)
    (σ := List (BitString × BitString)) hl hg h
  exact key

private lemma KROf_le_of_isUpperSemicomputable_labelling_F_snoc (N : ℕ) (l : List BitString)
    (x : BitString) :
    KROf_le_of_isUpperSemicomputable_labelling_F N (l ++ [x]) =
        KROf_le_of_isUpperSemicomputable_labelling_step N
        (KROf_le_of_isUpperSemicomputable_labelling_F N l) x := by
  simp [KROf_le_of_isUpperSemicomputable_labelling_F]

/-- Step 2 of the proof of `KROf_le_of_isUpperSemicomputable`: the online labelling of
the growing tree of strings (the book's "leaves carry labels of length `n`").  There is a
computable function `F N l` which, for the list `l` of strings enumerated so far, returns a list of
pairs `(leaf, label)`: the labels have length `N` and are pairwise different; the leaves are
elements of `l`; each pair persists when one more string `x` is enumerated, the label being passed
to an extension of the leaf; and if every prefix-free set of elements of `l` has at most `2 ^ N`
elements, every element of `l` is a prefix of some leaf. (Algorithm: a new `x` that is a prefix of a
leaf changes nothing; if it extends a leaf, it replaces it with the same label; otherwise it gets
the first label of length `N` not in use, and is dropped if there is none.) -/
private theorem KROf_le_of_isUpperSemicomputable_labelling :
    ∃ F : ℕ → List BitString → List (BitString × BitString), Computable₂ F ∧
      (∀ N l, ∀ q ∈ F N l, q.2.length = N ∧ q.1 ∈ l) ∧
      (∀ N l, ((F N l).map Prod.snd).Nodup) ∧
      (∀ N l x, ∀ q ∈ F N l, ∃ q' ∈ F N (l ++ [x]), q'.2 = q.2 ∧ q.1 <+: q'.1) ∧
      (∀ N l, (∀ S : Set BitString, S ⊆ {y | y ∈ l} → IsPrefixFree S →
          S.encard ≤ (2 : ℕ∞) ^ N) → ∀ y ∈ l, ∃ q ∈ F N l, y <+: q.1) := by
  refine ⟨KROf_le_of_isUpperSemicomputable_labelling_F,
      KROf_le_of_isUpperSemicomputable_labelling_computable, fun N l q hq =>
      (KROf_le_of_isUpperSemicomputable_labelling_F_inv N l).1 q hq,
    fun N l => (KROf_le_of_isUpperSemicomputable_labelling_F_inv N l).2.1, fun N l x q hq =>
        ?_, fun N l => ?_⟩
  · rw [KROf_le_of_isUpperSemicomputable_labelling_F_snoc]
    exact KROf_le_of_isUpperSemicomputable_labelling_step_persist N _ x q hq
  · induction l using List.reverseRecOn with
    | nil => intro _ y hy; simp at hy
    | append_singleton l x ih =>
      intro hS
      rw [KROf_le_of_isUpperSemicomputable_labelling_F_snoc]
      refine KROf_le_of_isUpperSemicomputable_labelling_step_cover N l _ x
          (KROf_le_of_isUpperSemicomputable_labelling_F_inv N l) hS (ih fun S hsub hpf => hS S
          ?_ hpf)
      intro y hy
      exact List.mem_append_left _ (hsub hy)

/-- The list of strings certified by `e` before stage `s` with threshold `N` (`m + m₀ ≤ N`). -/
private def KROf_le_of_isUpperSemicomputable_assemble_L
    (e : ℕ → Option (BitString × ℕ)) (m₀ N : ℕ) : ℕ → List BitString
  | 0 => []
  | s + 1 => KROf_le_of_isUpperSemicomputable_assemble_L e m₀ N s ++
      (match e s with
        | some (y, m) => if m + m₀ ≤ N then [y] else []
        | none => [])

private lemma KROf_le_of_isUpperSemicomputable_assemble_mem_L
    (e : ℕ → Option (BitString × ℕ)) (m₀ N s : ℕ) (y : BitString) :
    y ∈ KROf_le_of_isUpperSemicomputable_assemble_L e m₀ N s ↔
      ∃ i < s, ∃ m, e i = some (y, m) ∧ m + m₀ ≤ N := by
  induction s with
  | zero => simp [KROf_le_of_isUpperSemicomputable_assemble_L]
  | succ s ih =>
    simp only [KROf_le_of_isUpperSemicomputable_assemble_L, List.mem_append, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · rcases hes : e s with _ | ⟨y', m⟩
        · simp [hes] at h
        · simp only [hes] at h
          split_ifs at h with hm
          · simp only [List.mem_singleton] at h
            subst h
            exact ⟨s, by omega, m, hes, hm⟩
          · simp at h
    · rintro ⟨i, hi, m, hm, hle⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, m, hm, hle⟩
      · right
        simp [hm, hle]

private lemma KROf_le_of_isUpperSemicomputable_assemble_L_append
    (e : ℕ → Option (BitString × ℕ)) (m₀ N s t : ℕ) :
    ∃ ex, KROf_le_of_isUpperSemicomputable_assemble_L e m₀ N (s + t) =
      KROf_le_of_isUpperSemicomputable_assemble_L e m₀ N s ++ ex := by
  induction t with
  | zero => exact ⟨[], by simp⟩
  | succ t ih =>
    obtain ⟨ex, h⟩ := ih
    refine ⟨ex ++ (match e (s + t) with
        | some (y, m) => if m + m₀ ≤ N then [y] else []
        | none => []), ?_⟩
    rw [← Nat.add_assoc]
    simp only [KROf_le_of_isUpperSemicomputable_assemble_L, h, List.append_assoc]

private lemma KROf_le_of_isUpperSemicomputable_assemble_F_iter
    (F : ℕ → List BitString → List (BitString × BitString))
    (hF3 : ∀ N l x, ∀ q ∈ F N l, ∃ q' ∈ F N (l ++ [x]), q'.2 = q.2 ∧ q.1 <+: q'.1)
    (N : ℕ) (ex : List BitString) :
    ∀ (l : List BitString), ∀ q ∈ F N l, ∃ q' ∈ F N (l ++ ex), q'.2 = q.2 ∧ q.1 <+: q'.1 := by
  induction ex with
  | nil => intro l q hq; exact ⟨q, by simpa using hq, rfl, List.prefix_rfl⟩
  | cons x ex ih =>
    intro l q hq
    obtain ⟨q', hq', h2, h1⟩ := hF3 N l x q hq
    obtain ⟨q'', hq'', h2', h1'⟩ := ih (l ++ [x]) q' hq'
    refine ⟨q'', by simpa using hq'', h2'.trans h2, h1.trans h1'⟩

private lemma KROf_le_of_isUpperSemicomputable_assemble_L_computable
    (e : ℕ → Option (BitString × ℕ)) (he : Computable e) (m₀ : ℕ) :
    Computable₂ (fun N s => KROf_le_of_isUpperSemicomputable_assemble_L e m₀ N s) := by
  have hstep : Computable (fun a : (ℕ × ℕ) × (ℕ × List BitString) =>
      (match e a.2.1 with
        | some (y, m) => if m + m₀ ≤ a.1.1 then [y] else []
        | none => [] : List BitString)) := by
    have ho : Computable (fun a : (ℕ × ℕ) × (ℕ × List BitString) => e a.2.1) :=
      he.comp (Computable.fst.comp Computable.snd)
    have hg : Computable₂ (fun (a : (ℕ × ℕ) × (ℕ × List BitString)) (ym : BitString × ℕ) =>
        (if ym.2 + m₀ ≤ a.1.1 then [ym.1] else [] : List BitString)) := by
      have hle : PrimrecPred (fun w : ((ℕ × ℕ) × (ℕ × List BitString)) × (BitString × ℕ) =>
          w.2.2 + m₀ ≤ w.1.1.1) :=
        Primrec.nat_le.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.const m₀)) (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      have hc : Computable (fun w : ((ℕ × ℕ) × (ℕ × List BitString)) × (BitString × ℕ) =>
          decide (w.2.2 + m₀ ≤ w.1.1.1)) := hle.decide.to_comp
      have hsing : Computable (fun w : ((ℕ × ℕ) × (ℕ × List BitString)) × (BitString × ℕ) =>
          ([w.2.1] : List BitString)) :=
        Computable.list_cons.comp (Computable.fst.comp Computable.snd) (Computable.const [])
      refine (Computable.cond hc hsing (Computable.const [])).of_eq fun w => ?_
      by_cases h : w.2.2 + m₀ ≤ w.1.1.1 <;> simp [h]
    have := Computable.option_casesOn ho (Computable.const ([] : List BitString)) hg
    refine this.of_eq fun a => ?_
    rcases e a.2.1 with _ | ⟨y, m⟩ <;> rfl
  have hrec := Computable.nat_rec (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ => ([] : List BitString))
    (h := fun (p : ℕ × ℕ) (r : ℕ × List BitString) =>
      r.2 ++ (match e r.1 with
        | some (y, m) => if m + m₀ ≤ p.1 then [y] else []
        | none => [] : List BitString))
    Computable.snd (Computable.const []) (Computable.list_append.comp
      (Computable.snd.comp Computable.snd) hstep)
  refine hrec.of_eq fun p => ?_
  obtain ⟨N, s⟩ := p
  dsimp only
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [KROf_le_of_isUpperSemicomputable_assemble_L]
    rw [← ih]

/-- Step 3 of the proof of `KROf_le_of_isUpperSemicomputable`: given the enumeration `e`
of step 1 and the labelling `F` of step 2, the decision decompressor `M` is: `M.rel p x` iff `x`
is empty or, for some stage `s`, `x` is a prefix of a leaf labelled `p` in
`F |p| (the strings `y` with `(y, m) = e i`, `i < s`, `m + m₀ ≤ |p|`)`, where `2 ^ m₀ ≥ c`.  It
is enumerable, prefix closed, regular (by persistence and injectivity of labels), and a string with
`k x < n` has a description of length `n + m₀` (the strings with `k < n` have at most
`c * 2 ^ n ≤ 2 ^ (n + m₀)` pairwise incompatible elements).  Hence `KR_M(x) ≤ k x + m₀ + 1`. -/
private theorem KROf_le_of_isUpperSemicomputable_assemble
    (k : BitString → ℕ∞) (c : ℕ)
    (hcard : ∀ n : ℕ, ∀ S : Set BitString, IsPrefixFree S → (∀ x ∈ S, k x < n) →
      S.encard ≤ (c : ℕ∞) * 2 ^ n)
    (e : ℕ → Option (BitString × ℕ)) (he : Computable e)
    (he1 : ∀ (s : ℕ) (x : BitString) (m : ℕ), e s = some (x, m) → k x < m)
    (he2 : ∀ (x : BitString) (n : ℕ), k x < n → ∃ (s m : ℕ), m ≤ n ∧ e s = some (x, m))
    (F : ℕ → List BitString → List (BitString × BitString)) (hF : Computable₂ F)
    (hF1 : ∀ N l, ∀ q ∈ F N l, q.2.length = N ∧ q.1 ∈ l)
    (hF2 : ∀ N l, ((F N l).map Prod.snd).Nodup)
    (hF3 : ∀ N l x, ∀ q ∈ F N l, ∃ q' ∈ F N (l ++ [x]), q'.2 = q.2 ∧ q.1 <+: q'.1)
    (hF4 : ∀ N l, (∀ S : Set BitString, S ⊆ {y | y ∈ l} → IsPrefixFree S →
          S.encard ≤ (2 : ℕ∞) ^ N) → ∀ y ∈ l, ∃ q ∈ F N l, y <+: q.1) :
    ∃ (M : DecisionDecompressor) (d : ℕ), ∀ x, KROf M x ≤ k x + d := by
  classical
  -- `m₀ = c` works: `c ≤ 2 ^ c`
  have hL := KROf_le_of_isUpperSemicomputable_assemble_L_computable e he c
  have hmemL := KROf_le_of_isUpperSemicomputable_assemble_mem_L e c
  -- persistence of leaves along stages
  have hpers : ∀ (N s₁ s₂ : ℕ), s₁ ≤ s₂ → ∀ q₁ ∈ F N
      (KROf_le_of_isUpperSemicomputable_assemble_L e c N s₁),
      ∀ q₂ ∈ F N (KROf_le_of_isUpperSemicomputable_assemble_L e c N s₂),
      q₁.2 = q₂.2 → q₁.1 <+: q₂.1 := by
    intro N s₁ s₂ hs q₁ hq₁ q₂ hq₂ hq
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
    obtain ⟨ex, hex⟩ := KROf_le_of_isUpperSemicomputable_assemble_L_append e c N s₁ t
    obtain ⟨q', hq', h2, h1⟩ := KROf_le_of_isUpperSemicomputable_assemble_F_iter F hF3 N ex
      _ q₁ hq₁
    rw [← hex] at hq'
    have : q' = q₂ :=
      List.inj_on_of_nodup_map (hF2 N _) hq' hq₂ (h2.trans hq)
    exact this ▸ h1
  -- enumerability
  have hre : IsRE (fun q : BitString × BitString => q.2 = [] ∨ ∃ s : ℕ, ∃ w ∈ F q.1.length
      (KROf_le_of_isUpperSemicomputable_assemble_L e c q.1.length s),
        w.2 = q.1 ∧ q.2 <+: w.1) := by
    have hpc : PrimrecPred (fun w : ((BitString × BitString) × ℕ) × (BitString × BitString) =>
        w.2.2 = w.1.1.1 ∧ w.1.1.2 = w.2.1.take w.1.1.2.length) :=
      PrimrecPred.and
        (Primrec.eq.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.list_take.comp
            (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.fst.comp Primrec.snd)))
    have hR1 : IsRE (fun w : ((BitString × BitString) × ℕ) × (BitString × BitString) =>
        w.2.2 = w.1.1.1 ∧ w.1.1.2 <+: w.2.1) :=
      isRE_of_computable_bool _ (fun w => decide (w.2.2 = w.1.1.1 ∧
        w.1.1.2 = w.2.1.take w.1.1.2.length))
        (fun w => by simp [List.prefix_iff_eq_take])
        hpc.decide.to_comp
    have hlen : Computable (fun a : (BitString × BitString) × ℕ => a.1.1.length) :=
      Computable.list_length.comp (Computable.fst.comp Computable.fst)
    have hbound : Computable (fun a : (BitString × BitString) × ℕ =>
        F a.1.1.length (KROf_le_of_isUpperSemicomputable_assemble_L e c a.1.1.length a.2)) :=
      (show Computable (fun p : ℕ × List BitString => F p.1 p.2) from hF).comp
        (Computable.pair hlen
          ((show Computable (fun p : ℕ × ℕ =>
            KROf_le_of_isUpperSemicomputable_assemble_L e c p.1 p.2) from hL).comp
            (Computable.pair hlen Computable.snd)))
    have hR2 := IsRE.existsInList
      (R := fun (a : (BitString × BitString) × ℕ) (w : BitString × BitString) =>
        w.2 = a.1.1 ∧ a.1.2 <+: w.1) hR1 _ hbound
    have hR3 := IsRE.exists_encodable
      (R := fun (a : BitString × BitString) (s : ℕ) => ∃ w ∈ F a.1.length
        (KROf_le_of_isUpperSemicomputable_assemble_L e c a.1.length s),
        w.2 = a.1 ∧ a.2 <+: w.1) hR2
    exact isRE_nil.or hR3
  let M : DecisionDecompressor :=
    { rel := fun p x => x = [] ∨ ∃ s : ℕ, ∃ w ∈ F p.length
        (KROf_le_of_isUpperSemicomputable_assemble_L e c p.length s),
          w.2 = p ∧ x <+: w.1
      re := hre
      nil_mem := fun p => Or.inl rfl
      prefix_closed := by
        intro p x x' hx hx'
        rcases hx with rfl | ⟨s, w, hw, hw2, hxw⟩
        · exact Or.inl (List.prefix_nil.mp hx')
        · exact Or.inr ⟨s, w, hw, hw2, hx'.trans hxw⟩
      regular := by
        intro p₁ x₁ p₂ x₂ h1 h2 hp
        have hp' : p₁ = p₂ := hp
        subst hp'
        change x₁ <+: x₂ ∨ x₂ <+: x₁
        rcases h1 with rfl | ⟨s₁, w₁, hw₁, hw₁2, hx₁⟩
        · exact Or.inl (List.nil_prefix)
        rcases h2 with rfl | ⟨s₂, w₂, hw₂, hw₂2, hx₂⟩
        · exact Or.inr (List.nil_prefix)
        rcases le_total s₁ s₂ with hs | hs
        · have := hpers _ s₁ s₂ hs w₁ hw₁ w₂ hw₂ (hw₁2.trans hw₂2.symm)
          exact List.prefix_or_prefix_of_prefix (hx₁.trans this) hx₂
        · have := hpers _ s₂ s₁ hs w₂ hw₂ w₁ hw₁ (hw₂2.trans hw₁2.symm)
          exact List.prefix_or_prefix_of_prefix hx₁ (hx₂.trans this) }
  refine ⟨M, c + 1, fun x => ?_⟩
  by_cases hx : k x = ⊤
  · rw [hx]; simp
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hx
  have hkn : k x < ((j + 1 : ℕ) : ℕ∞) := by
    rw [← hj]; exact_mod_cast Nat.lt_succ_self j
  obtain ⟨s, m, hm, hes⟩ := he2 x (j + 1) hkn
  set N := j + 1 + c with hN
  have hxl : x ∈ KROf_le_of_isUpperSemicomputable_assemble_L e c N (s + 1) :=
    (hmemL N (s + 1) x).mpr ⟨s, Nat.lt_succ_self s, m, hes, by omega⟩
  have hpf : ∀ S : Set BitString, S ⊆ {y | y ∈
      KROf_le_of_isUpperSemicomputable_assemble_L e c N (s + 1)} → IsPrefixFree S →
      S.encard ≤ (2 : ℕ∞) ^ N := by
    intro S hS hSpf
    have hk : ∀ y ∈ S, k y < ((j + 1 : ℕ) : ℕ∞) := by
      intro y hy
      obtain ⟨i, -, m', hi, hle⟩ := (hmemL N (s + 1) y).mp (hS hy)
      refine (he1 i y m' hi).trans_le ?_
      exact_mod_cast (by omega : m' ≤ j + 1)
    refine (hcard (j + 1) S hSpf hk).trans ?_
    have hc2 : (c : ℕ∞) ≤ 2 ^ c := by exact_mod_cast (Nat.lt_two_pow_self (n := c)).le
    calc (c : ℕ∞) * 2 ^ (j + 1) ≤ 2 ^ c * 2 ^ (j + 1) := by gcongr
      _ = 2 ^ N := by rw [hN, ← pow_add]; ring_nf
  obtain ⟨w, hw, hxw⟩ := hF4 N _ hpf x hxl
  have hlen : w.2.length = N := (hF1 N _ w hw).1
  have hrel : M.rel w.2 x :=
    Or.inr ⟨s + 1, w, by rw [hlen]; exact hw, rfl, hxw⟩
  have hle : KROf M x ≤ (N : ℕ∞) := by
    have h : KROf M x ≤ (w.2.length : ℕ∞) := by
      unfold KROf modeComplexity
      exact sInf_le ⟨w.2, hrel, rfl⟩
    rw [hlen] at h
    exact h
  rw [← hj]
  refine hle.trans (le_of_eq ?_)
  rw [hN]; push_cast; ring

/-- **SUV Theorem 127 (l) (Section 6.1, printed p. 195).** `KR` is the smallest, up to an
additive constant, upper semicomputable function `k` such that every prefix-free set of strings
`x` with `k(x) < n` has `O(2 ^ n)` elements: then `KR(x) ≤ k(x) + O(1)`.

Proof idea (the book's main argument): after adding a constant, at most `2 ^ n` pairwise
incompatible strings have `k(x) < n`. For each `n`, follow the growing tree of strings with
`k(x) < n`. Its leaves carry labels of length `n`, a leaf that is extended passes its label to
its extension, and a new branch gets a fresh label. Each label moves along one branch, which
defines a decision decompressor on descriptions of length `n`. -/
theorem KROf_le_of_isUpperSemicomputable {R : DecisionDecompressor} (hR : R.IsOptimal)
    (k : BitString → ℕ∞) (hk : IsUpperSemicomputable k)
    (hcard : ∃ c : ℕ, ∀ n : ℕ, ∀ S : Set BitString, IsPrefixFree S → (∀ x ∈ S, k x < n) →
      S.encard ≤ (c : ℕ∞) * 2 ^ n) :
    ∃ c : ℕ, ∀ x, KROf R x ≤ k x + c := by
  obtain ⟨c, hc⟩ := hcard
  obtain ⟨e, he, he1, he2⟩ := KROf_le_of_isUpperSemicomputable_enumeration k hk
  obtain ⟨F, hF, hF1, hF2, hF3, hF4⟩ := KROf_le_of_isUpperSemicomputable_labelling
  obtain ⟨M, d, hM⟩ := KROf_le_of_isUpperSemicomputable_assemble k c hc e he he1 he2 F hF
    hF1 hF2 hF3 hF4
  obtain ⟨c', hc'⟩ := hR M
  refine ⟨d + c', fun x => ?_⟩
  calc KROf R x ≤ KROf M x + c' := hc' x
    _ ≤ k x + d + c' := add_le_add (hM x) le_rfl
    _ = k x + ((d + c' : ℕ) : ℕ∞) := by push_cast; ring

private lemma exists_const_KROf_le_KA_a_le_one (x : BitString) :
    universalContinuousSemimeasure x ≤ 1 := by
  have ha := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have := ha.antitone_of_prefix (List.nil_prefix (l := x))
  rwa [ha.1] at this

private lemma exists_const_KROf_le_KA_KA_nonneg (x : BitString) : 0 ≤ KA x := by
  have ha := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have hpos : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos (universalContinuousSemimeasure_pos x).ne' (ha.ne_top x)
  have hle : (universalContinuousSemimeasure x).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (exists_const_KROf_le_KA_a_le_one x)
    simpa using this
  unfold KA
  have := Real.logb_nonpos (b := 2) (by norm_num) hpos.le hle
  linarith

private lemma exists_const_KROf_le_KA_KA_lt_iff (x : BitString) (m : ℕ) :
    KA x < m ↔ (2 : ENNReal)⁻¹ ^ m < universalContinuousSemimeasure x := by
  have ha := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have hpos : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos (universalContinuousSemimeasure_pos x).ne' (ha.ne_top x)
  have hpow_top : (2 : ENNReal)⁻¹ ^ m ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [← ENNReal.toReal_lt_toReal hpow_top (ha.ne_top x)]
  have hpow_real : ((2 : ENNReal)⁻¹ ^ m).toReal = (2 : ℝ)⁻¹ ^ m := by simp
  rw [hpow_real]
  unfold KA
  have h2 : Real.logb 2 ((2 : ℝ)⁻¹ ^ m) = -(m : ℝ) := by
    unfold Real.logb
    rw [Real.log_pow, Real.log_inv]
    have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  have := Real.logb_lt_logb_iff (b := 2) (x := (2 : ℝ)⁻¹ ^ m)
    (y := (universalContinuousSemimeasure x).toReal) (by norm_num) (by positivity) hpos
  rw [h2] at this
  rw [← this]
  constructor <;> intro h <;> linarith

private lemma exists_const_KROf_le_KA_inv_two_pow_lt_dyadicValue_iff (j m s : ℕ) :
    (2 : ENNReal)⁻¹ ^ j < dyadicValue m s ↔ 2 ^ s < m * 2 ^ j := by
  rw [dyadicValue, ← ENNReal.inv_pow,
    ENNReal.lt_div_iff_mul_lt (Or.inl (by simp)) (Or.inl (by simp))]
  rw [show ((2 : ENNReal) ^ j)⁻¹ * 2 ^ s = (2 : ENNReal) ^ s / 2 ^ j by
    rw [ENNReal.div_eq_inv_mul]]
  rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))]
  constructor
  · intro h
    have : ((2 ^ s : ℕ) : ENNReal) < ((m * 2 ^ j : ℕ) : ENNReal) := by push_cast; exact h
    exact_mod_cast this
  · intro h
    have : ((2 ^ s : ℕ) : ENNReal) < ((m * 2 ^ j : ℕ) : ENNReal) := by exact_mod_cast h
    push_cast at this
    exact this

private lemma exists_const_KROf_le_KA_floor_lt_iff (x : BitString) (n : ℕ) :
    (((⌊KA x⌋₊ + 1 : ℕ) : ℕ∞) < (n : ℕ∞)) ↔
      (2 : ENNReal)⁻¹ ^ (n - 1) < universalContinuousSemimeasure x := by
  rw [Nat.cast_lt]
  cases n with
  | zero =>
    simp only [Nat.not_lt_zero, false_iff, not_lt]
    simpa using exists_const_KROf_le_KA_a_le_one x
  | succ m =>
    rw [Nat.add_sub_cancel, ← exists_const_KROf_le_KA_KA_lt_iff,
      ← Nat.floor_lt (exists_const_KROf_le_KA_KA_nonneg x)]
    omega

private lemma exists_const_KROf_le_KA_isUpperSemicomputable :
    IsUpperSemicomputable (fun x : BitString => (((⌊KA x⌋₊ + 1 : ℕ) : ℕ∞))) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
  have hsup' : ∀ x : BitString, (⨆ s, dyadicValue (approx s x []) s) =
      universalContinuousSemimeasure x := fun x => hsup x []
  have hiff : ∀ q : BitString × ℕ,
      ((((⌊KA q.1⌋₊ + 1 : ℕ) : ℕ∞)) < (q.2 : ℕ∞)) ↔
        ∃ s, 2 ^ s < approx s q.1 [] * 2 ^ (q.2 - 1) := by
    intro q
    rw [exists_const_KROf_le_KA_floor_lt_iff]
    constructor
    · intro h
      rw [← hsup' q.1] at h
      obtain ⟨s, hs⟩ := lt_iSup_iff.mp h
      exact ⟨s, (exists_const_KROf_le_KA_inv_two_pow_lt_dyadicValue_iff _ _ s).mp hs⟩
    · rintro ⟨s, hs⟩
      have hds := (exists_const_KROf_le_KA_inv_two_pow_lt_dyadicValue_iff (q.2 - 1) _ s).mpr hs
      refine lt_of_lt_of_le hds ?_
      rw [← hsup' q.1]
      exact le_iSup (fun s => dyadicValue (approx s q.1 []) s) s
  have hmul : Computable₂ (fun x y : ℕ => x * y) := Primrec₂.to_comp Primrec.nat_mul
  have hltb : Computable₂ (fun x y : ℕ => decide (x < y)) :=
    Primrec₂.to_comp (PrimrecPred.decide Primrec.nat_lt)
  have hpow : Computable fun n : ℕ => 2 ^ n := Primrec.to_comp primrec_two_pow_aux
  have hpred : Computable fun n : ℕ => n - 1 := Primrec.to_comp (Primrec.pred)
  have hA : Computable fun p : (BitString × ℕ) × ℕ => approx p.2 p.1.1 [] :=
    hcomp.comp (Computable.snd.pair
      ((Computable.fst.comp Computable.fst).pair (Computable.const [])))
  have hcheck : Computable fun p : (BitString × ℕ) × ℕ =>
      decide (2 ^ p.2 < approx p.2 p.1.1 [] * 2 ^ (p.1.2 - 1)) :=
    hltb.comp (hpow.comp Computable.snd)
      (hmul.comp hA (hpow.comp (hpred.comp (Computable.snd.comp Computable.fst))))
  have hRE : IsRE fun p : (BitString × ℕ) × ℕ => 2 ^ p.2 < approx p.2 p.1.1 [] * 2 ^ (p.1.2 - 1) :=
    isRE_of_computable_bool _ _ (fun _ => decide_eq_true_iff) hcheck
  have := IsRE.exists_encodable (R := fun (q : BitString × ℕ) (s : ℕ) =>
    2 ^ s < approx s q.1 [] * 2 ^ (q.2 - 1)) hRE
  exact IsRE.of_iff this (fun q => (hiff q).symm)

private lemma exists_const_KROf_le_KA_card (n : ℕ) (S : Set BitString) (hS : IsPrefixFree S)
    (h : ∀ x ∈ S, (((⌊KA x⌋₊ + 1 : ℕ) : ℕ∞)) < (n : ℕ∞)) :
    S.encard ≤ ((1 : ℕ) : ℕ∞) * 2 ^ n := by
  have ha := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have hsum := ha.tsum_antichain_le S (fun y hy z hz hyz => hS hy hz hyz)
  have hε : ∀ x : S, (2 : ENNReal)⁻¹ ^ (n - 1) < universalContinuousSemimeasure x :=
    fun x => (exists_const_KROf_le_KA_floor_lt_iff x n).mp (h x x.2)
  have h1 : ∑' _ : S, (2 : ENNReal)⁻¹ ^ (n - 1) ≤ 1 :=
    le_trans (ENNReal.tsum_le_tsum fun x => (hε x).le) hsum
  rw [ENNReal.tsum_const] at h1
  have h2 : (ENat.card S : ENNReal) ≤ ((2 : ENNReal)⁻¹ ^ (n - 1))⁻¹ :=
    ENNReal.le_inv_iff_mul_le.mpr h1
  rw [ENNReal.inv_pow, inv_inv] at h2
  have h3 : (ENat.card S : ENNReal) ≤ ((((1 : ℕ) : ℕ∞) * 2 ^ n : ℕ∞) : ENNReal) := by
    refine h2.trans ?_
    simp only [Nat.cast_one, one_mul, ENat.toENNReal_pow, ENat.toENNReal_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
  exact ENat.toENNReal_le.mp h3

/-- **SUV Theorem 127 (m) (Section 6.1, printed p. 195).** `KR(x) ≤ KA(x) + O(1)`. `KA` is the
library's real-valued a priori complexity. The `toNat` is harmless because `KROf R x` is finite
(`KROf_ne_top`).

Proof idea: for pairwise incompatible `xᵢ`, `∑ 2 ^ (-KA(xᵢ)) ≤ 1` (the cylinders are disjoint),
so fewer than `2 ^ n` of them have `KA(xᵢ) < n`. Apply (l) to `⌈KA⌉`, which is upper
semicomputable. -/
theorem exists_const_KROf_le_KA {R : DecisionDecompressor} (hR : R.IsOptimal) :
    ∃ c : ℝ, ∀ x, ((KROf R x).toNat : ℝ) ≤ KA x + c := by
  obtain ⟨c, hc⟩ := KROf_le_of_isUpperSemicomputable hR
    (fun x : BitString => (((⌊KA x⌋₊ + 1 : ℕ) : ℕ∞)))
    exists_const_KROf_le_KA_isUpperSemicomputable
    ⟨1, fun n S hS h => exists_const_KROf_le_KA_card n S hS h⟩
  refine ⟨1 + c, fun x => ?_⟩
  have h1 := hc x
  have h2 : (KROf R x).toNat ≤ ⌊KA x⌋₊ + 1 + c := by
    have h3 : KROf R x ≤ ((⌊KA x⌋₊ + 1 + c : ℕ) : ℕ∞) := by
      refine h1.trans (le_of_eq ?_)
      push_cast; rfl
    exact ENat.toNat_le_of_le_natCast h3
  have h4 : (⌊KA x⌋₊ : ℝ) ≤ KA x := Nat.floor_le (exists_const_KROf_le_KA_KA_nonneg x)
  have h5 : ((KROf R x).toNat : ℝ) ≤ ((⌊KA x⌋₊ + 1 + c : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h5
  linarith

/-- **SUV Problem 193 (Section 6.1, printed p. 194).** Computable continuous maps `ℕ⊥ → Σ` differ
from decision machines: they may map `⊥` to a nonempty string. This does not matter for
complexity. The two classes define exactly the same complexity functions.

In this representation the claim is close to definitional, because `⊥` is not a description.
The content is that dropping the `⊥` row (resp. adding the row `⊥ ↦ []`) preserves
computability and the decompressor axioms.

Proof idea: a decision decompressor is a continuous map with value `[]` at `⊥`. Conversely, the
`⊥` row of a continuous map contributes no descriptions, so dropping it gives a decision
decompressor with the same complexity. -/
theorem range_KROf_eq_range_contDecisionMap_complexity :
    Set.range KROf = Set.range ContDecisionMap.complexity := by
  classical
  ext f
  constructor
  · rintro ⟨M, rfl⟩
    let F : ContDecisionMap :=
      { rel := fun a x => x = [] ∨ (a.isSome = true ∧ M.rel (a.getD []) x)
        re := by
          have hN : IsRE (fun q : Option BitString × BitString => q.2 = []) :=
            isRE_of_computable_bool _ (fun q => decide (q.2 = [])) (fun q => by simp)
              (Primrec.to_comp (PrimrecPred.decide
                (Primrec.eq.comp (Primrec.snd) (Primrec.const []))))
          have hM : IsRE (fun q : Option BitString × BitString => M.rel (q.1.getD []) q.2) :=
            M.re.comp_computable
              (g := fun q : Option BitString × BitString => (q.1.getD [], q.2))
              (Computable.pair
                (Computable.option_getD Computable.fst (Computable.const []))
                Computable.snd)
          exact hN.or (hM.and_computable
            (p := fun q : Option BitString × BitString => q.1.isSome)
            (Primrec.option_isSome.to_comp.comp Computable.fst))
        nil_mem := fun a => Or.inl rfl
        prefix_closed := by
          rintro a x x' (rfl | ⟨ha, hx⟩) hx'
          · exact Or.inl (List.prefix_nil.mp hx')
          · exact Or.inr ⟨ha, M.prefix_closed hx hx'⟩
        compatible := by
          rintro a x₁ x₂ (rfl | ⟨ha, h₁⟩) (rfl | ⟨ha', h₂⟩)
          · exact Or.inl (List.prefix_refl _)
          · exact Or.inl List.nil_prefix
          · exact Or.inr List.nil_prefix
          · exact M.regular h₁ h₂ rfl
        bot_le := by
          rintro x (rfl | ⟨h, -⟩) p
          · exact Or.inl rfl
          · simp at h }
    refine ⟨F, ?_⟩
    symm
    funext x
    unfold ContDecisionMap.complexity KROf modeComplexity
    congr 1
    ext l
    simp only [F, Option.isSome_some, Option.getD_some, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, Or.inr hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      rcases hp with rfl | hp
      · exact ⟨p, M.nil_mem p, rfl⟩
      · exact ⟨p, hp, rfl⟩
  · rintro ⟨F, rfl⟩
    let M : DecisionDecompressor :=
      { rel := fun p x => F.rel (some p) x
        re := F.re.comp_computable
          (g := fun q : BitString × BitString => (some q.1, q.2))
          (Computable.pair (Computable.option_some.comp Computable.fst) Computable.snd)
        nil_mem := fun p => F.nil_mem _
        prefix_closed := fun p x x' h h' => F.prefix_closed h h'
        regular := fun p₁ x₁ p₂ x₂ h₁ h₂ hp => by
          have : p₁ = p₂ := hp
          subst this
          exact F.compatible h₁ h₂ }
    exact ⟨M, rfl⟩

end GeneralScheme

end Kolmogorov
