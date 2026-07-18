import KolmogorovMathlib.Restricted.Family

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
  constructor;
  · intro hy;
    rcases y with ( _ | ⟨ yh, yt ⟩ ) <;> simp_all +decide [ maskSet ];
    · exact absurd hy.1 ( by simp +decide [ stringsOfLength ] );
    · refine ⟨ ?_, ?_, ?_ ⟩;
      · specialize hy ; have := hy.2 0 ; aesop;
      · unfold stringsOfLength at *; aesop;
      · grind;
  · rintro ⟨ yh, yt, rfl, hyh, hyt ⟩;
    rw [ mem_maskSet ] at *;
    grind

/-- The number of wildcard (`none`) positions in a mask. -/
def maskWild : Mask → ℕ
  | [] => 0
  | none :: t => maskWild t + 1
  | some _ :: t => maskWild t

/-
The cardinality of a mask set is `2 ^ (number of wildcards)`.
-/
theorem mask_card (m : Mask) : (maskSet m).card = 2 ^ maskWild m := by
  induction m <;> simp +decide [ *, maskSet ] at *;
  rename_i k hk ih; rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', maskWild ] ;
  · rw [ show stringsOfLength ( hk.length + 1 ) = ( stringsOfLength hk.length ).image ( fun x =>
        false :: x ) ∪ ( stringsOfLength hk.length ).image ( fun x =>
            true :: x ) from ?_, Finset.filter_union ];
    · rw [ Finset.card_union_of_disjoint ];
      · rw [ Finset.card_filter, Finset.card_filter ];
        rw [ Finset.sum_image, Finset.sum_image ] <;> simp +decide [ two_mul ];
        congr! 1;
        · convert ih using 2;
          grind;
        · convert ih using 2;
          grind;
      · rw [ Finset.disjoint_left ] ; aesop;
    · ext x; simp [stringsOfLength];
      cases x <;> aesop;
  · convert ih using 1;
    refine Finset.card_bij ( fun x hx => x.tail ) ?_ ?_ ?_ <;> simp_all +decide [ stringsOfLength ];
    · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ ha₅
      rcases a₁ with ( _ | ⟨ x, a₁ ⟩ ) <;> rcases a₂ with ( _ | ⟨ y, a₂ ⟩ ) <;> simp_all +decide ;
      · cases ha₁;
      · cases ha₃;
      · specialize ha₂ 0 ; specialize ha₄ 0 ; aesop;
    · intro b hb hb'; use false :: b; simp_all +decide;
      grind;
  · convert ih using 1;
    refine Finset.card_bij ( fun x hx => x.tail ) ?_ ?_ ?_ <;> simp_all +decide [ stringsOfLength ];
    · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h
      rcases a₁ with ( _ | ⟨ x, a₁ ⟩ ) <;> rcases a₂ with ( _ | ⟨ y, a₂ ⟩ ) <;> simp_all +decide ;
      · cases ha₁;
      · cases ha₃;
      · specialize ha₂ 0 ; specialize ha₄ 0 ; aesop;
    · intro b hb hb'; use b.cons true; simp_all +decide;
      grind

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
  have h_maskWild : ∀ m : Mask, maskWild m = List.countP (fun x => x = none) m := by
    intro m; induction m <;> simp +arith +decide [ *, List.countP_cons ] ;
    rename_i k hk ih; cases k <;> simp +decide [ *, maskWild ] ;
  induction m generalizing keep <;> simp_all +decide [ List.countP_cons ];
  · cases keep <;> rfl;
  · cases ‹Option Bool› <;> simp_all +decide [ fixWildcards ];
    rcases keep with ( _ | keep ) <;> simp_all +decide [ Nat.pow_succ' ];
    ring

theorem fixWildcards_maskWild (m : Mask) (keep : ℕ) :
    ∀ m' ∈ fixWildcards m keep, maskWild m' = min keep (maskWild m) := by
  induction m generalizing keep;
  · cases keep <;> simp +decide [ fixWildcards ];
    exact Nat.zero_le _;
  · rename_i m hm ih;
    cases m <;> simp_all +decide [ fixWildcards ];
    · rcases keep with ( _ | keep ) <;> simp +decide [ * ];
      · rintro m' ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ maskWild ]
        all_goals rw [ ih 0 a ha, min_eq_left ] ; norm_num;
      · intro a ha; specialize ih keep a ha; simp_all +decide [ maskWild ] ;
    · intro a ha; specialize ih keep a ha; simp_all +decide [ maskWild ] ;

theorem fixWildcards_cover (m : Mask) (keep : ℕ) :
    ∀ x ∈ maskSet m, ∃ m' ∈ fixWildcards m keep, x ∈ maskSet m' := by
  induction m generalizing keep <;> simp_all +decide [ maskSet ];
  · unfold fixWildcards; aesop;
  · cases ‹Option Bool› <;> simp_all +decide [ stringsOfLength ];
    · rename_i k hk;
      rcases keep with ( _ | keep ) <;> simp_all +decide [ fixWildcards ];
      · intro x hx hx'; specialize hk 0 ( x.tail ) ; simp_all +decide [ List.length_tail ] ;
        rcases hk with ⟨ m', hm', hm'', hm''' ⟩
        use if x[0]? = some false then some false :: m' else some true :: m' ; simp_all +decide;
        grind;
      · intro x hx hx'; specialize hk keep ( x.tail ) ; simp_all +decide;
        grind;
    · rename_i k hk;
      intro x hx hx'; specialize hk keep ( x.tail ) ; simp_all +decide;
      obtain ⟨ m', hm', hm'' ⟩ := hk; use some k :: m'; simp_all +decide [ fixWildcards ] ;
      grind

/-
Split a mask set into pieces of cardinality `2 ^ keep`.
-/
theorem mask_cover_pieces (m : Mask) (keep : ℕ) (hkeep : keep ≤ maskWild m) :
    ∃ 𝒞 : List (Finset BitString),
      (∀ B ∈ 𝒞, maskFamilyMem B ∧ B.card = 2 ^ keep) ∧
      (∀ x ∈ maskSet m, ∃ B ∈ 𝒞, x ∈ B) ∧
      𝒞.length = 2 ^ (maskWild m - keep) := by
  refine ⟨ ( fixWildcards m keep ).map maskSet, ?_, ?_, ?_ ⟩;
  · simp +zetaDelta at *;
    exact fun x hx =>
        ⟨ ⟨ x, rfl ⟩, by rw [ mask_card, fixWildcards_maskWild m keep x hx, min_eq_left hkeep ] ⟩;
  · intro x hx; obtain ⟨ m', hm', hm'' ⟩ := fixWildcards_cover m keep x hx; use maskSet m'; aesop;
  · rw [ List.length_map, fixWildcards_length ]

/-- All strings matching a mask `m`, as an explicit list. -/
def maskList : Mask → List BitString
  | [] => [[]]
  | some b :: t => (maskList t).map (fun x => b :: x)
  | none :: t => (maskList t).map (fun x => false :: x) ++ (maskList t).map (fun x => true :: x)

theorem maskList_toFinset (m : Mask) : (maskList m).toFinset = maskSet m := by
  unfold maskSet;
  induction m <;> simp_all +decide [ stringsOfLength ];
  rename_i k hk ih; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.ext_iff ] ;
  · intro a; rw
      [ show maskList ( none :: hk ) = ( maskList hk ).map ( fun x => false :: x ) ++ ( maskList hk
            ).map ( fun x =>
                true :: x ) from rfl ] ; simp +decide [ List.mem_append, List.mem_map ] ;
    constructor <;> intro h;
    · grind;
    · rcases a with ( _ | ⟨ b, a ⟩ ) <;> simp_all +decide [ List.length ];
      grind;
  · intro a; specialize ih ( a.tail )
    rcases a with ( _ | ⟨ x, a ⟩ ) <;> simp_all +decide [ maskList ] ;
    constructor <;> intro h <;> rcases h with ⟨ h₁, h₂ ⟩ <;> simp_all +decide;
    · grind;
    · exact ⟨ fun i hi => by simpa using h₂ ( i + 1 ) ( by linarith ),
        by simpa using h₂ 0 ( by linarith ) |>.1 rfl ⟩;
  · intro a; specialize ih ( a.tail )
    rcases a with ( _ | ⟨ b, a ⟩ ) <;> simp_all +decide [ List.length ] ;
    · cases hk <;> simp_all +decide [ maskList ];
    · rw [ show maskList ( some true :: hk ) = ( maskList hk ).map ( fun x => true :: x ) from rfl
          ] ; simp +decide [ List.mem_map, ih ] ;
      constructor <;> intro h <;> rcases h with ⟨ h₁, h₂ ⟩ <;> simp_all +decide;
      · grind;
      · exact ⟨ fun i hi => by simpa using h₂ ( i + 1 ) ( by linarith ),
          by simpa using h₂ 0 ( by linarith ) |>.2 rfl ⟩

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
  unfold decodeMask encodeMask;
  rw [ decodeListCode_listCode ];
  induction m <;> simp_all +decide;
  rename_i k hk ih; cases k <;> rfl;

theorem maskSet_nonempty (m : Mask) : (maskSet m).Nonempty :=
  maskFamilyMem_nonempty ⟨m, rfl⟩

theorem decodeOptionBool_primrec : Primrec decodeOptionBool := by
  refine .of_eq (f := fun w => if w = [] then none else some ( w.head! )) ?_ ?_;
  · convert Primrec.list_head? using 1;
    exact funext fun x => by cases x <;> rfl;
  · intro n; cases n <;> rfl;

theorem decodeMask_primrec : Primrec decodeMask := by
  convert Primrec.list_map decodeListCode_primrec
      (decodeOptionBool_primrec.comp (Primrec.snd) |> Primrec.to₂) using 1

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

theorem maskCode_primrec : Primrec maskCode := by
  convert Primrec.comp ( canonicalUniformCodeOfList_primrec )
      ( Primrec.comp ( canonicalFinsetList_toFinset_primrec ) ( maskList_primrec.comp (
            decodeMask_primrec ) ) ) using 1

theorem maskCode_eq_code (w : BitString) :
    maskCode w = (codedUniformOn (maskSet (decodeMask w)) (maskSet_nonempty _)).code := by
      convert canonicalUniformCodeOfList_canonicalFinsetList _ _ using 1;
      congr! 2;
      · exact Eq.symm ( maskList_toFinset _ );
      · exact maskList_toFinset ( decodeMask w ) ▸ maskSet_nonempty _

/-- Stage `t` of the mask enumeration. -/
noncomputable def maskEnum (t : ℕ) : List BitString := (boundedPrograms t).map maskCode

theorem maskEnum_computable : Computable maskEnum := by
  unfold maskEnum
  exact (Primrec.list_map primrec_boundedPrograms ((maskCode_primrec.comp Primrec.snd).to₂)).to_comp

theorem maskEnum_mono (t : ℕ) : maskEnum t <+: maskEnum (t + 1) := by
  -- By definition of `maskEnum`, we know that `maskEnum t = (boundedPrograms t).map maskCode`.
  simp [maskEnum];
  rw [ boundedPrograms_succ ];
  simp +decide [ List.map_append ]

theorem maskEnum_sound (t : ℕ) : ∀ w ∈ maskEnum t,
    ∃ (S : Finset BitString) (hS : S.Nonempty),
      maskFamilyMem S ∧ w = (codedUniformOn S hS).code := by
        intros w hw
        obtain ⟨v, hv⟩ : ∃ v, w = maskCode v ∧ v ∈ boundedPrograms t := by
          unfold maskEnum at hw; aesop;
        exact ⟨ _, maskSet_nonempty _, ⟨ _, rfl ⟩, hv.1.trans ( maskCode_eq_code _ ) ⟩

theorem maskEnum_complete : ∀ (S : Finset BitString) (hS : S.Nonempty),
    maskFamilyMem S → ∃ t, (codedUniformOn S hS).code ∈ maskEnum t := by
      intro S hS hS';
      obtain ⟨ m, rfl ⟩ := hS';
      use (encodeMask m).length;
      convert List.mem_map.mpr ⟨ encodeMask m, ?_, ?_ ⟩;
      · exact ( mem_boundedPrograms_iff _ _ ).mpr le_rfl;
      · rw [ maskCode_eq_code, decodeMask_encodeMask ]

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
theorem maskFamily_cover {A : Finset BitString} (hA : maskFamilyMem A) (n c : ℕ) (hc_pos : 0 < c)
    (hc_le : c ≤ A.card) :
  ∃ 𝒞 : List (Finset BitString),
    (∀ B ∈ 𝒞, maskFamilyMem B ∧ B.card ≤ c) ∧
    (∀ x ∈ A, x.length = n → ∃ B ∈ 𝒞, x ∈ B) ∧
    𝒞.length * c ≤ maskOverhead n * A.card :=
  by
    by_cases hn : n = (hA.choose).length;
    · obtain ⟨m, hm⟩ : ∃ m : Mask, A = maskSet m := hA
      have hA_card : A.card = 2 ^ maskWild m := by
        rw [ hm, mask_card ];
      obtain ⟨r, hr⟩ : ∃ r : ℕ, 2 ^ r ≤ c ∧ c < 2 ^ (r + 1) ∧ r ≤ maskWild m := by
        exact ⟨ Nat.log 2 c, Nat.pow_le_of_le_log ( by linarith ) ( by linarith ),
            Nat.lt_pow_of_log_lt ( by linarith ) ( by linarith ), Nat.le_trans
                ( Nat.log_mono_right hc_le ) ( by rw [ hA_card, Nat.log_pow ( by linarith ) ] ) ⟩;
      obtain ⟨𝒞, h𝒞⟩ := mask_cover_pieces m r hr.2.2;
      refine ⟨ 𝒞, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ maskOverhead ];
      convert Nat.mul_le_mul_left ( 2 ^ ( maskWild m - r ) ) hr.2.1.le using 1 ; ring;
      rw [ ← pow_add, Nat.sub_add_cancel hr.2.2 ];
    · use [];
      grind +suggestions

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
