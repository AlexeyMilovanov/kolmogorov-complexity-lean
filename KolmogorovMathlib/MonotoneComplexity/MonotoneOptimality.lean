/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.MonotoneComplexity.EffectiveOpenBridge
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.MonotoneComplexity.StreamMapEnumeration
import KolmogorovMathlib.Prefix.Encoding

/-!
# Optimal monotone decompressor (KM)
-/

namespace Kolmogorov

/-- The decompressor `D`, run on the program `p`, has already output a stream extending `x`. -/
def monotoneProduces (D : BitStream → BitStream) (p x : BitString) : Prop :=
  BitStream.finite x ≤ D (BitStream.finite p)

/-- The monotone complexity of `x` relative to the decompressor `D`: the least length of a program
on which `D` outputs a stream extending `x`. -/
noncomputable def KMOf (D : BitStream → BitStream) (x : BitString) : ℕ∞ :=
  sInf { l : ℕ∞ | ∃ p : BitString, monotoneProduces D p x ∧ l = p.length }

/-- A computable monotone decompressor that beats every other computable one up to an additive
constant. -/
def IsOptimalMonotoneDecompressor (D : BitStream → BitStream) : Prop :=
  IsComputableStreamMap D ∧
    ∀ D', IsComputableStreamMap D' → ∃ c : ℕ, ∀ x, KMOf D x ≤ KMOf D' x + c

/-- The lower graph obtained by prefixing each program with a self-delimiting index selecting one
row
of the family `U`; this is the graph of the universal monotone decompressor. -/
def taggedStreamLowerGraph (U : ℕ → BitString → BitString → Prop) (x y : BitString) : Prop :=
  y = [] ∨ ∃ i p, x = natCode i ++ p ∧ U i p y

/-- Tagging a family of stream lower graphs yields a stream lower graph. -/
lemma taggedStreamLowerGraph_isStreamLowerGraph (U : ℕ → BitString → BitString → Prop)
    (hU : ∀ i, IsStreamLowerGraph (U i)) :
    IsStreamLowerGraph (taggedStreamLowerGraph U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact Or.inl rfl
  · intro x y y' hy hy'
    rcases hy with rfl | ⟨i, p, rfl, hU_y⟩
    · have : y' = [] := by
        rcases hy' with ⟨s, hs⟩
        have hlen : (y' ++ s).length = 0 := by rw [hs, List.length_nil]
        rw [List.length_append] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      rw [this]
      exact Or.inl rfl
    · right
      use i, p, rfl
      exact (hU i).2.1 p y y' hU_y hy'
  · intro x x' y hy hx
    rcases hy with rfl | ⟨i, p, rfl, hU_y⟩
    · exact Or.inl rfl
    · right
      rcases hx with ⟨s, hs⟩
      use i, p ++ s
      constructor
      · rw [← hs, List.append_assoc]
      · exact (hU i).2.2.1 p (p ++ s) y hU_y (List.prefix_append p s)
  · intro x y y' hy hy'
    rcases hy with rfl | ⟨i, p, rfl, hU_y⟩
    · exact Or.inl List.nil_prefix
    · rcases hy' with rfl | ⟨j, q, hx, hU_y'⟩
      · exact Or.inr List.nil_prefix
      · have ⟨hij, hpq⟩ := natCode_append_inj hx.symm
        subst hij
        subst hpq
        exact (hU j).2.2.2 q y y' hU_y hU_y'

/-- On a program tagged with index `i` the tagged graph outputs exactly what row `i` outputs, plus
the empty string. -/
lemma taggedStreamLowerGraph_natCode_append_iff (U : ℕ → BitString → BitString → Prop)
    (_hU : ∀ i, IsStreamLowerGraph (U i)) (i : ℕ) (p y : BitString) :
    taggedStreamLowerGraph U (natCode i ++ p) y ↔ y = [] ∨ U i p y := by
  dsimp [taggedStreamLowerGraph]
  constructor
  · intro h
    rcases h with rfl | ⟨j, q, hx, hU_y⟩
    · exact Or.inl rfl
    · have ⟨hij, hpq⟩ := natCode_append_inj hx
      subst hij
      subst hpq
      exact Or.inr hU_y
  · intro h
    rcases h with rfl | hU_y
    · exact Or.inl rfl
    · right; use i, p, rfl

private lemma IsRE_of_computable_pred {α : Type*} [Primcodable α] {p : α → Prop} [DecidablePred p]
    (hp : Computable (fun a => decide (p a))) : IsRE p := by
  have h := IsRE.and_computable (p := fun a => decide (p a)) IsRE_true hp
  have h_iff : ∀ a, (decide (p a) = true ∧ True) ↔ (p a) := by
    intro a; exact Iff.trans (and_iff_left trivial) decide_eq_true_iff
  exact @IsRE.of_iff _ _ (fun a => decide (p a) = true ∧ True) p h h_iff

private def isEmptyBool : List Bool → Bool
| [] => true
| _ => false

private lemma isEmptyBool_computable : Computable isEmptyBool := by
  have hp : Primrec isEmptyBool := by
    have h := Primrec.list_casesOn (Primrec.id (α := List Bool)) (Primrec.const true)
      (Primrec₂.const false)
    exact h.of_eq (by intro l; cases l <;> rfl)
  exact Primrec.to_comp hp

/-- The set of pairs whose second component is the empty string is recursively enumerable. -/
lemma isRE_nil : IsRE (fun p : BitString × BitString => p.2 = []) := by
  have hp : Computable (fun p : BitString × BitString => isEmptyBool p.2) :=
    isEmptyBool_computable.comp Computable.snd
  have h := IsRE_of_computable_pred (p := fun p : BitString × BitString => p.2 = []) (by
    have heq : ∀ p : BitString × BitString, isEmptyBool p.2 = decide (p.2 = []) := by
      intro p; cases p.2 <;> rfl
    exact hp.of_eq heq)
  exact h

private lemma isRE_tagged_right {U : ℕ → BitString → BitString → Prop}
    (hU : IsRE (fun p : ℕ × (BitString × BitString) => U p.1 p.2.1 p.2.2)) :
    IsRE (fun p : BitString × BitString => ∃ i q, p.1 = natCode i ++ q ∧ U i q p.2) := by
  have h_pred : Computable (fun p : (BitString × BitString) × (ℕ × BitString) =>
      decide (p.1.1 = natCode p.2.1 ++ p.2.2)) := by
    apply Primrec.to_comp
    have h_primrec_pred : PrimrecPred (fun p : (BitString × BitString) × (ℕ × BitString) =>
      p.1.1 = natCode p.2.1 ++ p.2.2) :=
      (Primrec.eq (α := BitString)).comp
        (Primrec.fst.comp (Primrec.fst (α := BitString × BitString) (β := ℕ × BitString)))
        (Primrec.list_append.comp
          (primrec_natCode.comp (Primrec.fst.comp
            (Primrec.snd (α := BitString × BitString) (β := ℕ × BitString))))
          (Primrec.snd.comp (Primrec.snd (α := BitString × BitString) (β := ℕ × BitString))))
    rcases h_primrec_pred with ⟨_, hp⟩
    exact hp.of_eq (by intro p; congr)
  
  have h_U_comp : Computable (fun p : (BitString × BitString) × (ℕ × BitString) =>
      (p.2.1, (p.2.2, p.1.2))) := by
    apply Computable.pair
    · exact Computable.fst.comp Computable.snd
    · apply Computable.pair
      · exact Computable.snd.comp Computable.snd
      · exact Computable.snd.comp Computable.fst
  have hRE2 := IsRE.comp_computable hU h_U_comp
  have hRE_and :=
    IsRE.and_computable (p := fun p => decide (p.1.1 = natCode p.2.1 ++ p.2.2)) hRE2 h_pred
  
  have h_iff : ∀ p : (BitString × BitString) × (ℕ × BitString),
      ((decide (p.1.1 = natCode p.2.1 ++ p.2.2)) = true ∧ U p.2.1 p.2.2 p.1.2)
      ↔ (p.1.1 = natCode p.2.1 ++ p.2.2 ∧ U p.2.1 p.2.2 p.1.2) := by
    intro p; rw [decide_eq_true_iff]
  
  have hRE_and' : IsRE (fun p : (BitString × BitString) × (ℕ × BitString) =>
      p.1.1 = natCode p.2.1 ++ p.2.2 ∧ U p.2.1 p.2.2 p.1.2) := IsRE.of_iff hRE_and h_iff
  
  have hRE_exists := IsRE.exists_encodable
    (R := fun a : BitString × BitString => fun b : ℕ × BitString =>
      a.1 = natCode b.1 ++ b.2 ∧ U b.1 b.2 a.2) hRE_and'
  
  have h_iff2 : ∀ p : BitString × BitString,
      (∃ c : ℕ × BitString, p.1 = natCode c.1 ++ c.2 ∧ U c.1 c.2 p.2) ↔
      (∃ i q, p.1 = natCode i ++ q ∧ U i q p.2) := by
    intro p; constructor
    · rintro ⟨⟨i, q⟩, h⟩; exact ⟨i, q, h⟩
    · rintro ⟨i, q, h⟩; exact ⟨(i, q), h⟩
  exact IsRE.of_iff hRE_exists h_iff2

/-- Tagging a uniformly recursively enumerable family of graphs gives a recursively enumerable
graph. -/
lemma taggedStreamLowerGraph_isRE {U : ℕ → BitString → BitString → Prop}
    (hU : IsRE (fun p : ℕ × (BitString × BitString) => U p.1 p.2.1 p.2.2)) :
    IsRE (fun p : BitString × BitString => taggedStreamLowerGraph U p.1 p.2) := by
  dsimp [taggedStreamLowerGraph]
  apply IsRE.or
  · exact isRE_nil
  · exact isRE_tagged_right hU

private lemma sInf_le_sInf_add {S T : Set ℕ∞} {c : ℕ}
    (h : ∀ l ∈ T, ∃ k ∈ S, k ≤ l + (c : ℕ∞)) :
    sInf S ≤ sInf T + (c : ℕ∞) := by
  by_cases hT : T = ∅
  · rw [hT, sInf_empty, top_add]
    exact le_top
  · have hT_nonempty : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hT
    have h_min := csInf_mem hT_nonempty
    rcases h (sInf T) h_min with ⟨k, hk, hk_le⟩
    exact le_trans (sInf_le hk) hk_le

/-- Any program producing `x` bounds the monotone complexity of `x` by its length. -/
lemma KMOf_le_length_of_monotoneProduces {D : BitStream → BitStream} {p x : BitString}
    (h : monotoneProduces D p x) : KMOf D x ≤ p.length := by
  apply sInf_le
  exact ⟨p, h, rfl⟩

/-- If `D` simulates `D'` on programs tagged with `c`, then `D` beats `D'` up to the length of that
tag. -/
lemma KMOf_tagged_le_add {D D' : BitStream → BitStream} {c : ℕ} {x : BitString}
    (h : ∀ p, monotoneProduces D' p x → monotoneProduces D (natCode c ++ p) x) :
    KMOf D x ≤ KMOf D' x + (natCode c).length := by
  dsimp [KMOf]
  apply sInf_le_sInf_add
  intro l hl
  rcases hl with ⟨p, hp, rfl⟩
  use (natCode c ++ p).length
  constructor
  · exact ⟨natCode c ++ p, h p hp, rfl⟩
  · rw [List.length_append]
    have : ((natCode c).length : ℕ∞) + (p.length : ℕ∞) =
        (p.length : ℕ∞) + ((natCode c).length : ℕ∞) := add_comm _ _
    exact le_of_eq this

/-- An optimal monotone decompressor exists, so monotone complexity `KM` is well defined up to an
additive constant. -/
theorem exists_optimalMonotoneDecompressor :
    ∃ D, IsOptimalMonotoneDecompressor D := by
  obtain ⟨U, hU_RE, hU_LG, hU_comp⟩ := exists_universal_computableStreamMap_lowerGraphs
  let D := streamMapOfLowerGraph (taggedStreamLowerGraph U)
    (taggedStreamLowerGraph_isStreamLowerGraph U hU_LG)
  use D
  constructor
  · constructor
    · exact streamMapOfLowerGraph_isContinuousStreamMap _
    · have hRE := taggedStreamLowerGraph_isRE hU_RE
      apply IsRE.of_iff hRE
      intro p
      exact (streamMapOfLowerGraph_finite_spec _ p.1 p.2).symm
  · intro D' hD'
    obtain ⟨i, hi⟩ := hU_comp D' hD'
    use (natCode i).length
    intro x
    apply KMOf_tagged_le_add
    intro p hp
    -- hp : monotoneProduces D' p x
    -- which means .finite x ≤ D' (.finite p)
    -- this is streamLowerGraph D' p x
    have hl1 : streamLowerGraph D' p x := hp
    -- by hi, U i p x
    have hl2 : U i p x := (hi p x).mpr hl1
    -- so taggedStreamLowerGraph U (natCode i ++ p) x is true
    have hl3 : taggedStreamLowerGraph U (natCode i ++ p) x := Or.inr ⟨i, p, rfl, hl2⟩
    -- which means monotoneProduces D (natCode i ++ p) x
    have hl4 : BitStream.finite x ≤ D (.finite (natCode i ++ p)) := by
      rwa [streamMapOfLowerGraph_finite_spec]
    exact hl4

end Kolmogorov
