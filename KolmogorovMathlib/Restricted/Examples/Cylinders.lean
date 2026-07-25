/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.Family

/-!
# Cylinders
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- `cylinder n u` is the set of all strings of length `n` that have `u` as a prefix. -/
def cylinder (n : ℕ) (u : List Bool) : Finset BitString :=
  (stringsOfLength n).filter (fun x => u <+: x)

/-- The cylinder family consists of all nonempty cylinders `cylinder n u` where `u` is a prefix of
length `≤ n`. -/
def cylinderFamilyMem (A : Finset BitString) : Prop :=
  ∃ n u, u.length ≤ n ∧ A = cylinder n u

theorem cylinderFamilyMem_nonempty {A : Finset BitString} (h : cylinderFamilyMem A) : A.Nonempty :=
  by
    rcases h with ⟨n, u, hlen, rfl⟩
    refine ⟨u ++ List.replicate (n - u.length) false, ?_⟩
    rw [cylinder, Finset.mem_filter]
    constructor
    · rw [memStringsOfLength, List.length_append, List.length_replicate]
      omega
    · exact List.prefix_append _ _

theorem mem_cylinder (n : ℕ) (u : List Bool) (x : BitString) :
    x ∈ cylinder n u ↔ x.length = n ∧ u <+: x := by
  simp [cylinder, Finset.mem_filter, memStringsOfLength]

/-
The cardinality of a cylinder with prefix `u` of length `≤ n` is `2 ^ (n - u.length)`.
-/
theorem cylinder_card (n : ℕ) (u : List Bool) (h : u.length ≤ n) :
    (cylinder n u).card = 2 ^ (n - u.length) := by
      rw [ show cylinder n u = Finset.image ( fun v => u ++ v ) ( stringsOfLength ( n - u.length )
                                                                  ) from ?_,
                                                                      Finset.card_image_of_injOn,
                                                                          cardStringsOfLength ];
      · exact fun x hx y hy hxy => by simpa using hxy;
      · ext x; simp [cylinder, stringsOfLength];
        constructor <;> intro hx;
        · obtain ⟨ a, rfl ⟩ := hx.2; use a; aesop;
        · grind +qlia

/-- The overhead for cylinders is a constant 2. -/
def cylinderOverhead (_n : ℕ) : ℕ := 2

theorem cylinderOverhead_pos (n : ℕ) : 0 < cylinderOverhead n := by
  simp [cylinderOverhead]

theorem cylinderFamily_fullCube (n : ℕ) : cylinderFamilyMem (stringsOfLength n) :=
  by
    refine ⟨n, [], by simp, ?_⟩
    ext x
    simp [cylinder]

/-
A prefix cube is exactly a cylinder (with prefix `p` and total length `p.length + m`).
-/
theorem prefixCubeSet_eq_cylinder (p : BitString) (m : ℕ) :
    prefixCubeSet p m = cylinder (p.length + m) p := by
      ext x
      simp [prefixCubeSet, cylinder];
      constructor;
      · rintro ⟨ a, rfl, rfl ⟩ ; simp +decide [ stringsOfLength ] ;
      · rintro ⟨ hx₁, hx₂ ⟩;
        obtain ⟨ a, rfl ⟩ := hx₂;
        simp_all +decide [ stringsOfLength ]

/-- Stage `t` of the cylinder enumeration: emit `prefixCubeCode w` for every
`w` of length `≤ t`. -/
noncomputable def cylinderEnum (t : ℕ) : List BitString :=
  (boundedPrograms t).map prefixCubeCode

theorem cylinderEnum_computable : Computable cylinderEnum := by
  have hlist : Primrec (fun w : BitString =>
      (allStrings (CodedFiniteDistribution.decodeNatCode (decodeSecond w))).map
        (fun s => decodeFirst w ++ s)) :=
    Primrec.list_map
      (allStrings_primrec.comp
        (CodedFiniteDistribution.decodeNatCode_primrec.comp decodeSecond_primrec))
      (Primrec.list_append.comp (decodeFirst_primrec'.comp Primrec.fst) Primrec.snd)
  have hfin : Primrec (fun w : BitString =>
      canonicalFinsetList (prefixCubeSet (decodeFirst w)
        (CodedFiniteDistribution.decodeNatCode (decodeSecond w)))) := by
    have := canonicalFinsetList_toFinset_primrec.comp hlist
    simpa [prefixCubeSet] using this
  have hpc : Primrec prefixCubeCode := by
    unfold prefixCubeCode
    exact canonicalUniformCodeOfList_primrec.comp hfin
  unfold cylinderEnum
  exact (Primrec.list_map primrec_boundedPrograms ((hpc.comp Primrec.snd).to₂)).to_comp

theorem cylinderEnum_mono (t : ℕ) : cylinderEnum t <+: cylinderEnum (t + 1) := by
  unfold cylinderEnum; simp +decide [ boundedPrograms_succ ] ;

theorem cylinderEnum_sound (t : ℕ) : ∀ w ∈ cylinderEnum t,
    ∃ (S : Finset BitString) (hS : S.Nonempty),
      cylinderFamilyMem S ∧ w = (codedUniformOn S hS).code := by
        intro w hw;
        obtain ⟨ v, hv, rfl ⟩ := List.mem_map.mp hw;
        use prefixCubeSet (decodeFirst v) (decodeNatCode (decodeSecond v));
        exact ⟨ prefixCubeSet_nonempty _ _, by rw [ prefixCubeSet_eq_cylinder ] ; exact ⟨ _, _,
                                                                                          by simp,
            rfl ⟩, by rw [ prefixCubeCode
                           ] ; exact canonicalUniformCodeOfList_canonicalFinsetList _ _ ⟩

theorem cylinderEnum_complete : ∀ (S : Finset BitString) (hS : S.Nonempty),
    cylinderFamilyMem S → ∃ t, (codedUniformOn S hS).code ∈ cylinderEnum t := by
      intro S hS h_mem
      obtain ⟨n, u, hu⟩ := h_mem
      obtain ⟨m, hm⟩ : ∃ m, n = u.length + m := by
        exact Nat.exists_eq_add_of_le hu.1
      have hS_eq : S = prefixCubeSet u m := by
        rw [ hu.2, prefixCubeSet_eq_cylinder, hm ]
      use (pairCode u (natCode m)).length
      simp [cylinderEnum, hS_eq];
      refine ⟨ pairCode u ( natCode m ), ?_, ?_ ⟩;
      · exact ( mem_boundedPrograms_iff _ _ ).mpr ( by simp +arith +decide [ *, length_pairCode,
                                                                             length_natCode ] );
      · rw [ prefixCubeCode, decodeFirst_pairCode, decodeSecond_pairCode, decodeNatCode_natCode ];
        exact canonicalUniformCodeOfList_canonicalFinsetList _ _

/-- The cylinder family enumeration is computable and complete. -/
noncomputable def cylinderFamilyEnumeration : FamilyEnumeration cylinderFamilyMem where
  enum := cylinderEnum
  computable := cylinderEnum_computable
  mono := cylinderEnum_mono
  sound := cylinderEnum_sound
  complete := cylinderEnum_complete

/-
Splitting a cylinder `cylinder n u` into the cylinders obtained by extending
`u` to every possible prefix of length `k` (with `u.length ≤ k ≤ n`): there are
`2 ^ (k - u.length)` such pieces, each a cylinder of cardinality `2 ^ (n - k)`,
and together they cover `cylinder n u`.
-/
theorem cylinder_cover_pieces (n : ℕ) (u : List Bool) (k : ℕ)
    (hu : u.length ≤ k) (hk : k ≤ n) :
    ∃ 𝒞 : List (Finset BitString),
      (∀ B ∈ 𝒞, cylinderFamilyMem B ∧ B.card = 2 ^ (n - k)) ∧
      (∀ x ∈ cylinder n u, ∃ B ∈ 𝒞, x ∈ B) ∧
      𝒞.length = 2 ^ (k - u.length) := by
        refine
            ⟨ ( stringsOfLength ( k - u.length ) |> Finset.toList |> List.map ( fun v => cylinder n
                                                                                ( u ++ v )
                                                                                    ) ), ?_, ?_, ?_ ⟩
                                                                                        <;>
                                                                                          simp +decide [ * ];
        · intro v hv; rw [ cylinder_card ] ;
          · have := memStringsOfLength ( k - u.length ) v; simp_all +decide [ List.length_append ] ;
            exact ⟨ n, u ++ v, by simp +decide [ hv, hu, hk ], rfl ⟩;
          · grind +suggestions;
        · intro x hx; use x.drop u.length |>.take ( k - u.length ) ; simp_all +decide [ cylinder ] ;
          rcases hx.2 with ⟨ y, rfl ⟩ ; simp_all +decide [ stringsOfLength ];
          exact ⟨ by linarith, List.take_prefix _ _ ⟩;
        · exact cardStringsOfLength _

/-
The cylinder family covering property.
-/
theorem cylinderFamily_cover {A : Finset BitString} (hA : cylinderFamilyMem A) (n c : ℕ)
    (hc_pos : 0 < c) (hc_le : c ≤ A.card) :
  ∃ 𝒞 : List (Finset BitString),
    (∀ B ∈ 𝒞, cylinderFamilyMem B ∧ B.card ≤ c) ∧
    (∀ x ∈ A, x.length = n → ∃ B ∈ 𝒞, x ∈ B) ∧
    𝒞.length * c ≤ cylinderOverhead n * A.card :=
  by
    obtain ⟨N, u, hu, rfl⟩ : ∃ N u, u.length ≤ N ∧ A = cylinder N u := by
      exact hA;
    by_cases hn : n = N;
    · obtain ⟨r, hr⟩ : ∃ r : ℕ, 2^r ≤ c ∧ c < 2^(r+1) := by
        exact ⟨ Nat.log 2 c, Nat.pow_le_of_le_log ( by linarith ) ( by linarith ),
                Nat.lt_pow_of_log_lt ( by linarith ) ( by linarith ) ⟩;
      have hr_le : r ≤ n - u.length := by
        have hr_le : 2^r ≤ 2^(n - u.length) := by
          exact le_trans hr.1
              ( hc_le.trans ( by rw [ cylinder_card _ _ ( by linarith ) ] ; aesop ) );
        rwa [ pow_le_pow_iff_right₀ ( by decide ) ] at hr_le;
      obtain ⟨𝒞, h𝒞⟩ := cylinder_cover_pieces n u (n - r) (by
      omega) (by
      exact Nat.sub_le _ _);
      refine ⟨ 𝒞, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ Nat.sub_sub ];
      · grind;
      · have := cylinder_card N u hu; simp_all +decide [ cylinderOverhead ] ;
        rw [ show N - u.length = ( N - ( r + u.length ) ) + r by omega ] ; ring_nf at *
        nlinarith [ pow_pos ( zero_lt_two' ℕ ) r, pow_succ' ( 2 : ℕ ) r ] ;
    · refine ⟨ [ ], ?_, ?_, ?_ ⟩ <;> simp +decide;
      intro x hx; rw [ mem_cylinder ] at hx; aesop;

/-- The description family of cylinders. -/
noncomputable def cylinderFamily : DescriptionFamily where
  mem := cylinderFamilyMem
  nonempty_of_mem := cylinderFamilyMem_nonempty
  enumeration := cylinderFamilyEnumeration
  fullCube := cylinderFamily_fullCube
  overhead := cylinderOverhead
  overhead_pos := cylinderOverhead_pos
  cover := cylinderFamily_cover

theorem cylinderFamily_hasPolynomialOverhead :
    cylinderFamily.HasPolynomialOverhead := by
  refine ⟨2, 0, by decide, ?_⟩
  intro n
  simp [cylinderFamily, cylinderOverhead]

end Kolmogorov
