/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.Family

/-!
# Masks
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- A mask is a list of Option Bool, where `none` acts as a wildcard '*'. -/
abbrev Mask := List (Option Bool)

/-- `maskSet m` is the set of strings of the same length as `m` that match `m` on all `some`
    positions. -/
def maskSet (m : Mask) : Finset BitString :=
  (stringsOfLength m.length).filter (fun x => ∀ i, i < m.length → ∀ b,
      m[i]? = some (some b) → x[i]? = some b)

/-- The mask family consists of all sets `maskSet m` for some mask `m`. -/
def maskFamilyMem (A : Finset BitString) : Prop :=
  ∃ m : Mask, A = maskSet m

theorem maskFamilyMem_nonempty {A : Finset BitString} (h : maskFamilyMem A) : A.Nonempty :=
  by
    rcases h with ⟨m, rfl⟩
    refine ⟨m.map (fun b => b.getD false), ?_⟩
    rw [maskSet, Finset.mem_filter]
    constructor
    · rw [memStringsOfLength, List.length_map]
    · intro i hi b hfixed
      rw [List.getElem?_map]
      rw [hfixed]
      rfl

/-- The overhead for masks is a constant 2. -/
def maskOverhead (_n : ℕ) : ℕ := 2

theorem maskOverhead_pos (n : ℕ) : 0 < maskOverhead n := by
  simp [maskOverhead]

theorem maskFamily_fullCube (n : ℕ) : maskFamilyMem (stringsOfLength n) :=
  by
    refine ⟨List.replicate n none, ?_⟩
    ext x
    constructor
    · intro hx
      rw [maskSet, Finset.mem_filter]
      refine ⟨by simpa using hx, ?_⟩
      intro i hi b hfixed
      have hi' : i < n := by simpa using hi
      rw [List.getElem?_replicate_of_lt hi'] at hfixed
      cases hfixed
    · intro hx
      rw [maskSet] at hx
      simpa using (Finset.mem_filter.mp hx).1

/-- Characterization of membership in `maskSet` (the `i < m.length` bound is
redundant, since `m[i]? = some (some b)` already forces `i < m.length`). -/
theorem mem_maskSet (m : Mask) (x : BitString) :
    x ∈ maskSet m ↔ x.length = m.length ∧
      ∀ (i : ℕ) (b : Bool), m[i]? = some (some b) → x[i]? = some b := by
  rw [maskSet, Finset.mem_filter, memStringsOfLength]
  constructor
  · rintro ⟨hlen, h⟩
    refine ⟨hlen, fun i b hb => ?_⟩
    have hi : i < m.length := by
      by_contra hi
      simp [List.getElem?_eq_none (by omega : m.length ≤ i)] at hb
    exact h i hi b hb
  · rintro ⟨hlen, h⟩
    exact ⟨hlen, fun i _ b hb => h i b hb⟩

/-
Cons-characterization of `maskSet` membership.
-/
theorem mem_maskSet_cons (o : Option Bool) (t : Mask) (y : BitString) :
    y ∈ maskSet (o :: t) ↔
      ∃ yh yt, y = yh :: yt ∧ (∀ b, o = some b → yh = b) ∧ yt ∈ maskSet t := by
  rw [mem_maskSet]
  cases y with
  | nil =>
    simp only [List.length_nil, List.length_cons, Nat.zero_ne_add_one, false_and, false_iff]
    rintro ⟨yh, yt, h, _⟩
    contradiction
  | cons yh yt =>
    simp only [List.length_cons, add_right_cancel_iff]
    constructor
    · rintro ⟨hlen, hmatch⟩
      refine ⟨yh, yt, rfl, ?_, ?_⟩
      · intro b hob
        have h0 : (o :: t)[0]? = some (some b) := congrArg Option.some hob
        exact Option.some.inj (hmatch 0 b h0)
      · rw [mem_maskSet]
        refine ⟨hlen, fun i b hb => ?_⟩
        exact hmatch (i + 1) b hb
    · rintro ⟨yh', yt', h, ho, hyt⟩
      injection h with hyh hyt'
      subst hyh hyt'
      rw [mem_maskSet] at hyt
      refine ⟨hyt.1, fun i b hb => ?_⟩
      cases i with
      | zero =>
        have hob : o = some b := Option.some.inj hb
        exact congrArg Option.some (ho b hob)
      | succ i =>
        exact hyt.2 i b hb

/-- The number of wildcard (`none`) positions in a mask. -/
def maskWild : Mask → ℕ
  | [] => 0
  | none :: t => maskWild t + 1
  | some _ :: t => maskWild t

/-
The cardinality of a mask set is `2 ^ (number of wildcards)`.
-/
theorem mask_card (m : Mask) : (maskSet m).card = 2 ^ maskWild m := by
  induction m with
  | nil =>
    unfold maskSet maskWild stringsOfLength
    rfl
  | cons o t ih =>
    cases o with
    | none =>
      unfold maskWild
      have H_disj : Disjoint (Finset.image (List.cons false) (maskSet t))
          (Finset.image (List.cons true) (maskSet t)) := by
        simp only [Finset.disjoint_left, Finset.mem_image, not_exists, not_and]
        rintro _ ⟨x, _, rfl⟩ y _ h_eq
        cases h_eq
      have H_eq : maskSet (none :: t) =
          Finset.image (List.cons false) (maskSet t) ∪
            Finset.image (List.cons true) (maskSet t) := by
        ext y
        rw [mem_maskSet_cons, Finset.mem_union, Finset.mem_image, Finset.mem_image]
        constructor
        · rintro ⟨yh, yt, rfl, _, hyt⟩
          cases yh
          · left; exact ⟨yt, hyt, rfl⟩
          · right; exact ⟨yt, hyt, rfl⟩
        · rintro (⟨yt, hyt, rfl⟩ | ⟨yt, hyt, rfl⟩)
          · exact ⟨false, yt, rfl, fun b hb => by contradiction, hyt⟩
          · exact ⟨true, yt, rfl, fun b hb => by contradiction, hyt⟩
      rw [H_eq, Finset.card_union_of_disjoint H_disj]
      have H_inj_false : Function.Injective (List.cons false) := fun x y h => by injection h
      have H_inj_true : Function.Injective (List.cons true) := fun x y h => by injection h
      rw [Finset.card_image_of_injective _ H_inj_false,
        Finset.card_image_of_injective _ H_inj_true]
      rw [ih, Nat.pow_succ']
      ring
    | some b =>
      unfold maskWild
      have H_eq : maskSet (some b :: t) = Finset.image (List.cons b) (maskSet t) := by
        ext y
        rw [mem_maskSet_cons, Finset.mem_image]
        constructor
        · rintro ⟨yh, yt, rfl, hyh, hyt⟩
          have hyh' : yh = b := hyh b rfl
          subst hyh'
          exact ⟨yt, hyt, rfl⟩
        · rintro ⟨yt, hyt, rfl⟩
          exact ⟨b, yt, rfl, fun b' hb' => Option.some.inj hb', hyt⟩
      rw [H_eq]
      have H_inj : Function.Injective (List.cons b) := fun x y h => by injection h
      rw [Finset.card_image_of_injective _ H_inj, ih]

/-- `fixWildcards m keep` lists all masks refining `m` that leave the leftmost
`keep` wildcards free and fix (to both values) all remaining wildcards. -/
def fixWildcards : Mask → ℕ → List Mask
  | [], _ => [[]]
  | some b :: t, keep => (fixWildcards t keep).map (fun m' => some b :: m')
  | none :: t, keep =>
      match keep with
      | k + 1 => (fixWildcards t k).map (fun m' => none :: m')
      | 0 => (fixWildcards t 0).map (fun m' => some false :: m') ++
             (fixWildcards t 0).map (fun m' => some true :: m')

theorem fixWildcards_length (m : Mask) (keep : ℕ) :
    (fixWildcards m keep).length = 2 ^ (maskWild m - keep) := by
  induction m generalizing keep with
  | nil => simp [fixWildcards, maskWild]
  | cons o t ih =>
    cases o with
    | some b => simpa [fixWildcards, maskWild, List.length_map] using ih keep
    | none =>
      cases keep with
      | zero =>
          simp only [fixWildcards, List.length_append, List.length_map, maskWild, Nat.sub_zero,
            ih 0, Nat.pow_succ']
          ring
      | succ k =>
          simpa [fixWildcards, maskWild, List.length_map, Nat.succ_sub_succ] using ih k

theorem fixWildcards_maskWild (m : Mask) (keep : ℕ) :
    ∀ m' ∈ fixWildcards m keep, maskWild m' = min keep (maskWild m) := by
  induction m generalizing keep with
  | nil =>
    intro m' hm'
    simp only [fixWildcards, List.mem_singleton] at hm'
    subst hm'
    simp [maskWild]
  | cons o t ih =>
    cases o with
    | some b =>
      intro m' hm'
      simp only [fixWildcards, List.mem_map] at hm'
      obtain ⟨a, ha, rfl⟩ := hm'
      simp only [maskWild]
      exact ih keep a ha
    | none =>
      cases keep with
      | succ k =>
        intro m' hm'
        simp only [fixWildcards, List.mem_map] at hm'
        obtain ⟨a, ha, rfl⟩ := hm'
        simp only [maskWild]
        rw [ih k a ha]
        omega
      | zero =>
        intro m' hm'
        simp only [fixWildcards, List.mem_append, List.mem_map] at hm'
        rcases hm' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
          · simp only [maskWild]
            rw [ih 0 a ha]
            omega

theorem fixWildcards_cover (m : Mask) (keep : ℕ) :
    ∀ x ∈ maskSet m, ∃ m' ∈ fixWildcards m keep, x ∈ maskSet m' := by
  induction m generalizing keep with
  | nil =>
      intro x hx
      rw [mem_maskSet] at hx
      have : x = [] := List.eq_nil_of_length_eq_zero hx.1
      subst x
      exact ⟨[], by simp [fixWildcards], by rw [mem_maskSet]; simp⟩
  | cons o t ih =>
      intro x hx
      rw [mem_maskSet_cons] at hx
      rcases hx with ⟨xh, xt, rfl, hhead, htail⟩
      cases o with
      | some b =>
          obtain ⟨m', hm', hxm'⟩ := ih keep xt htail
          refine ⟨some b :: m', ?_, ?_⟩
          · simp [fixWildcards, hm']
          · rw [mem_maskSet_cons]
            exact ⟨xh, xt, rfl, fun b' hb' => hhead b' hb', hxm'⟩
      | none =>
          cases keep with
          | succ keep =>
              obtain ⟨m', hm', hxm'⟩ := ih keep xt htail
              refine ⟨none :: m', ?_, ?_⟩
              · simp [fixWildcards, hm']
              · rw [mem_maskSet_cons]
                exact ⟨xh, xt, rfl, by simp, hxm'⟩
          | zero =>
              obtain ⟨m', hm', hxm'⟩ := ih 0 xt htail
              refine ⟨some xh :: m', ?_, ?_⟩
              · cases xh <;> simp [fixWildcards, hm']
              · rw [mem_maskSet_cons]
                exact ⟨xh, xt, rfl, fun b hb => Option.some.inj hb, hxm'⟩

/-
Split a mask set into pieces of cardinality `2 ^ keep`.
-/
theorem mask_cover_pieces (m : Mask) (keep : ℕ) (hkeep : keep ≤ maskWild m) :
    ∃ 𝒞 : List (Finset BitString),
      (∀ B ∈ 𝒞, maskFamilyMem B ∧ B.card = 2 ^ keep) ∧
      (∀ x ∈ maskSet m, ∃ B ∈ 𝒞, x ∈ B) ∧
      𝒞.length = 2 ^ (maskWild m - keep) := by
  refine ⟨(fixWildcards m keep).map maskSet, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hB
    refine ⟨⟨m', rfl⟩, ?_⟩
    rw [mask_card, fixWildcards_maskWild m keep m' hm', min_eq_left hkeep]
  · intro x hx
    obtain ⟨m', hm', hm''⟩ := fixWildcards_cover m keep x hx
    refine ⟨maskSet m', ?_, hm''⟩
    simp only [List.mem_map]
    exact ⟨m', hm', rfl⟩
  · rw [List.length_map, fixWildcards_length]

/-- All strings matching a mask `m`, as an explicit list. -/
def maskList : Mask → List BitString
  | [] => [[]]
  | some b :: t => (maskList t).map (fun x => b :: x)
  | none :: t =>
      (maskList t).map (fun x => false :: x) ++ (maskList t).map (fun x => true :: x)

theorem maskList_toFinset (m : Mask) : (maskList m).toFinset = maskSet m := by
  ext y
  rw [List.mem_toFinset]
  induction m generalizing y with
  | nil =>
    rw [mem_maskSet]
    constructor
    · intro hy
      simp only [maskList, List.mem_singleton] at hy
      subst hy
      exact ⟨rfl, fun i b hb => by simp at hb⟩
    · rintro ⟨hlen, -⟩
      simp only [maskList, List.mem_singleton]
      exact List.eq_nil_of_length_eq_zero (by simpa using hlen)
  | cons o t ih =>
    cases o with
    | some b =>
      simp only [maskList, List.mem_map, mem_maskSet_cons]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨b, x, rfl, fun _ hc => Option.some.inj hc, (ih x).mp hx⟩
      · rintro ⟨yh, yt, rfl, hyh, hyt⟩
        exact ⟨yt, (ih yt).mpr hyt, by rw [hyh b rfl]⟩
    | none =>
      simp only [maskList, List.mem_append, List.mem_map, mem_maskSet_cons]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨false, x, rfl, (fun _ hc => by contradiction), (ih x).mp hx⟩
        · exact ⟨true, x, rfl, (fun _ hc => by contradiction), (ih x).mp hx⟩
      · rintro ⟨yh, yt, rfl, -, hyt⟩
        cases yh
        · exact Or.inl ⟨yt, (ih yt).mpr hyt, rfl⟩
        · exact Or.inr ⟨yt, (ih yt).mpr hyt, rfl⟩

/-- Decode a bitstring into an `Option Bool` (empty ↦ wildcard `none`). -/
def decodeOptionBool (w : BitString) : Option Bool :=
  match w with
  | [] => none
  | b :: _ => some b

/-- Encode an `Option Bool` as a bitstring (`none ↦ []`, `some b ↦ [b]`). -/
def encodeOptionBool : Option Bool → BitString
  | none => []
  | some b => [b]

/-- Decode a bitstring into a mask via the list-of-codes decoder. -/
def decodeMask (w : BitString) : Mask := (decodeListCode w).map decodeOptionBool

/-- Encode a mask into a bitstring. -/
def encodeMask (m : Mask) : BitString := listCode (m.map encodeOptionBool)

theorem decodeMask_encodeMask (m : Mask) : decodeMask (encodeMask m) = m := by
  unfold decodeMask encodeMask
  rw [decodeListCode_listCode]
  induction m with
  | nil => rfl
  | cons h t ih =>
    rw [List.map_cons, List.map_cons]
    have ih' : (t.map encodeOptionBool).map decodeOptionBool = t := ih
    rw [ih']
    cases h <;> rfl

theorem maskSet_nonempty (m : Mask) : (maskSet m).Nonempty :=
  maskFamilyMem_nonempty ⟨m, rfl⟩

theorem decodeOptionBool_primrec : Primrec decodeOptionBool := by
  refine .of_eq (f := fun w => if w = [] then none else some ( w.head! )) ?_ ?_;
  · convert Primrec.list_head? using 1;
    exact funext fun x => by cases x <;> rfl;
  · intro n; cases n <;> rfl;

theorem decodeMask_primrec : Primrec decodeMask :=
  (Primrec.list_map decodeListCode_primrec
    (Primrec.to₂ (decodeOptionBool_primrec.comp Primrec.snd))).of_eq fun _ => rfl

theorem maskList_primrec : Primrec maskList := by
  have hstep : Primrec₂ (fun (_ : Mask) (p : Option Bool × List BitString) =>
      Option.casesOn (motive := fun _ => List BitString) p.1
        (p.2.map (fun x => false :: x) ++ p.2.map (fun x => true :: x))
        (fun b => p.2.map (fun x => b :: x))) :=
    Primrec.option_casesOn (Primrec.fst.comp Primrec.snd)
      (Primrec.list_append.comp
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          ((Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂))
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          ((Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂)))
      (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        ((Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)).to₂
  refine (Primrec.list_foldr Primrec.id (Primrec.const [[]]) hstep).of_eq (fun m => ?_)
  induction m with
  | nil => rfl
  | cons o t ih =>
      simp only [id_eq, List.foldr_cons] at ih ⊢
      rw [ih]; cases o <;> rfl

/-- Canonical uniform code of `maskSet (decodeMask w)`. -/
noncomputable def maskCode (w : BitString) : BitString :=
  canonicalUniformCodeOfList (canonicalFinsetList (maskList (decodeMask w)).toFinset)

theorem maskCode_primrec : Primrec maskCode :=
  (canonicalUniformCodeOfList_primrec.comp
    (canonicalFinsetList_toFinset_primrec.comp
      (maskList_primrec.comp decodeMask_primrec))).of_eq fun _ => rfl

theorem maskCode_eq_code (w : BitString) :
    maskCode w = (codedUniformOn (maskSet (decodeMask w)) (maskSet_nonempty _)).code := by
  unfold maskCode
  generalize h_eq : (maskList (decodeMask w)).toFinset = S
  have hS_eq : S = maskSet (decodeMask w) := by
    rw [← h_eq]
    exact maskList_toFinset (decodeMask w)
  subst hS_eq
  exact canonicalUniformCodeOfList_canonicalFinsetList (maskSet (decodeMask w))
    (maskSet_nonempty (decodeMask w))

/-- Stage `t` of the mask enumeration. -/
noncomputable def maskEnum (t : ℕ) : List BitString := (boundedPrograms t).map maskCode

theorem maskEnum_computable : Computable maskEnum := by
  unfold maskEnum
  exact (Primrec.list_map primrec_boundedPrograms
    ((maskCode_primrec.comp Primrec.snd).to₂)).to_comp

theorem maskEnum_mono (t : ℕ) : maskEnum t <+: maskEnum (t + 1) := by
  simp only [maskEnum]
  rw [boundedPrograms_succ]
  simp only [List.map_append, List.prefix_append]

theorem maskEnum_sound (t : ℕ) : ∀ w ∈ maskEnum t,
    ∃ (S : Finset BitString) (hS : S.Nonempty),
      maskFamilyMem S ∧ w = (codedUniformOn S hS).code := by
        intro w hw
        unfold maskEnum at hw
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        exact ⟨_, maskSet_nonempty _, ⟨_, rfl⟩, maskCode_eq_code _⟩

theorem maskEnum_complete : ∀ (S : Finset BitString) (hS : S.Nonempty),
    maskFamilyMem S → ∃ t, (codedUniformOn S hS).code ∈ maskEnum t := by
  intro S hS hS'
  obtain ⟨m, hm⟩ := hS'
  subst hm
  use (encodeMask m).length
  unfold maskEnum
  have H_mem : encodeMask m ∈ boundedPrograms (encodeMask m).length :=
    (mem_boundedPrograms_iff _ _).mpr le_rfl
  have H_code : maskCode (encodeMask m) = (codedUniformOn (maskSet m) hS).code := by
    rw [maskCode_eq_code, decodeMask_encodeMask]
  exact H_code ▸ List.mem_map_of_mem H_mem

/-- The mask family enumeration is computable and complete. -/
noncomputable def maskFamilyEnumeration : FamilyEnumeration maskFamilyMem where
  enum := maskEnum
  computable := maskEnum_computable
  mono := maskEnum_mono
  sound := maskEnum_sound
  complete := maskEnum_complete

/-
The mask family covering property.
-/
theorem maskFamily_cover {A : Finset BitString} (hA : maskFamilyMem A) (n c : ℕ)
    (hc_pos : 0 < c) (hc_le : c ≤ A.card) :
  ∃ 𝒞 : List (Finset BitString),
    (∀ B ∈ 𝒞, maskFamilyMem B ∧ B.card ≤ c) ∧
    (∀ x ∈ A, x.length = n → ∃ B ∈ 𝒞, x ∈ B) ∧
    𝒞.length * c ≤ maskOverhead n * A.card :=
  by
    obtain ⟨m, hm⟩ : ∃ m : Mask, A = maskSet m := hA
    by_cases hn : n = m.length
    · have hA_card : A.card = 2 ^ maskWild m := by
        rw [hm, mask_card]
      obtain ⟨r, hr⟩ : ∃ r : ℕ, 2 ^ r ≤ c ∧ c < 2 ^ (r + 1) ∧ r ≤ maskWild m := by
        refine ⟨Nat.log 2 c, Nat.pow_le_of_le_log (by linarith) (by linarith),
          Nat.lt_pow_of_log_lt (by linarith) (by linarith), Nat.le_trans
            (Nat.log_mono_right hc_le) (by rw [hA_card, Nat.log_pow (by linarith)])⟩
      obtain ⟨𝒞, h𝒞1, h𝒞2, h𝒞3⟩ := mask_cover_pieces m r hr.2.2
      refine ⟨𝒞, ?_, ?_, ?_⟩
      · intro B hB
        obtain ⟨hB1, hB2⟩ := h𝒞1 B hB
        exact ⟨hB1, by rw [hB2]; exact hr.1⟩
      · intro x hx hx_len
        rw [hm] at hx
        exact h𝒞2 x hx
      · rw [hA_card, h𝒞3, maskOverhead]
        have H2 : 2 ^ (maskWild m - r) * c ≤ 2 ^ (maskWild m - r) * 2 ^ (r + 1) :=
          Nat.mul_le_mul_left _ hr.2.1.le
        have H3 : 2 ^ (maskWild m - r) * 2 ^ (r + 1) = 2 * 2 ^ maskWild m := by
          rw [← pow_add]
          have h_pow : maskWild m - r + (r + 1) = maskWild m + 1 := by omega
          rw [h_pow, pow_add, pow_one, mul_comm]
        rw [← H3]
        exact H2
    · refine ⟨[], by simp, ?_, by simp [maskOverhead]⟩
      intro x hx hx_len
      rw [hm, mem_maskSet] at hx
      have hx_len' : x.length = m.length := hx.1
      omega

/-- The description family of masks. -/
noncomputable def maskFamily : DescriptionFamily where
  mem := maskFamilyMem
  nonempty_of_mem := maskFamilyMem_nonempty
  enumeration := maskFamilyEnumeration
  fullCube := maskFamily_fullCube
  overhead := maskOverhead
  overhead_pos := maskOverhead_pos
  cover := maskFamily_cover

theorem maskFamily_hasPolynomialOverhead : maskFamily.HasPolynomialOverhead := by
  refine ⟨2, 0, by decide, ?_⟩
  intro n
  simp [maskFamily, maskOverhead]

end Kolmogorov
