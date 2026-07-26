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
      rw [show cylinder n u = Finset.image (fun v => u ++ v) (stringsOfLength (n - u.length))
        from ?_, Finset.card_image_of_injOn, cardStringsOfLength]
      · exact fun x _ y _ hxy => by simpa using hxy
      · ext x
        simp only [cylinder, stringsOfLength, Finset.mem_filter, List.mem_toFinset,
          mem_allStrings, Finset.mem_image]
        constructor
        · intro hx
          have hx_len := hx.1
          obtain ⟨a, rfl⟩ := hx.2
          refine ⟨a, ?_, rfl⟩
          rw [List.length_append] at hx_len
          omega
        · intro hx
          obtain ⟨a, ha, rfl⟩ := hx
          refine ⟨?_, a, rfl⟩
          rw [List.length_append, ha]
          omega

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
      simp only [prefixCubeSet, List.mem_toFinset, List.mem_map, mem_allStrings, cylinder,
        Finset.mem_filter]
      constructor
      · rintro ⟨a, rfl, rfl⟩
        simp only [stringsOfLength, List.mem_toFinset, mem_allStrings, List.length_append,
          List.prefix_append, and_self]
      · rintro ⟨hx₁, a, rfl⟩
        refine ⟨a, ?_, rfl⟩
        revert hx₁
        simp only [stringsOfLength, List.mem_toFinset, mem_allStrings, List.length_append,
          add_right_inj, imp_self]

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
  unfold cylinderEnum
  rw [boundedPrograms_succ]
  simp only [List.map_append, List.prefix_append]

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
      simp only [cylinderEnum, length_pairCode, length_natCode, hS_eq, List.mem_map]
      refine ⟨pairCode u (natCode m), ?_, ?_⟩
      · exact (mem_boundedPrograms_iff _ _).mpr (by rw [length_pairCode, length_natCode])
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
        refine ⟨(stringsOfLength (k - u.length)).toList.map (fun v => cylinder n (u ++ v)),
          ?_, ?_, ?_⟩
        · intro B hB
          simp only [List.mem_map, Finset.mem_toList] at hB
          rcases hB with ⟨v, hv, rfl⟩
          have hlen_v : v.length = k - u.length := (memStringsOfLength _ _).mp hv
          have h_len : (u ++ v).length ≤ n := by
            rw [List.length_append, hlen_v]
            omega
          refine ⟨⟨n, u ++ v, h_len, rfl⟩, ?_⟩
          rw [cylinder_card n (u ++ v) h_len]
          congr 1
          rw [List.length_append, hlen_v]
          omega
        · intro x hx
          rw [mem_cylinder] at hx
          have hx_len : x.length = n := hx.1
          obtain ⟨y, rfl⟩ := hx.2
          simp only [List.mem_map, Finset.mem_toList]
          refine ⟨cylinder n (u ++ y.take (k - u.length)), ⟨y.take (k - u.length), ?_, rfl⟩, ?_⟩
          · rw [memStringsOfLength, List.length_take]
            have h_len : (u ++ y).length = n := hx_len
            rw [List.length_append] at h_len
            omega
          · rw [mem_cylinder]
            refine ⟨hx_len, ?_⟩
            have h_eq : u ++ y.take (k - u.length) ++ y.drop (k - u.length) = u ++ y := by
              rw [List.append_assoc, List.take_append_drop]
            exact ⟨y.drop (k - u.length), h_eq⟩
        · simp only [List.length_map, Finset.length_toList]
          exact cardStringsOfLength _

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
    by_cases hn : n = N
    · subst hn
      obtain ⟨r, hr⟩ : ∃ r : ℕ, 2^r ≤ c ∧ c < 2^(r+1) := by
        exact ⟨Nat.log 2 c, Nat.pow_le_of_le_log (by linarith) (by linarith),
          Nat.lt_pow_of_log_lt (by linarith) (by linarith)⟩
      have hr_le : r ≤ n - u.length := by
        have hr_le : 2^r ≤ 2^(n - u.length) := by
          refine le_trans hr.1 (hc_le.trans ?_)
          rw [cylinder_card n u hu]
        rwa [pow_le_pow_iff_right₀ (by decide)] at hr_le
      obtain ⟨𝒞, h𝒞1, h𝒞2, h𝒞3⟩ := cylinder_cover_pieces n u (n - r) (by omega) (by omega)
      refine ⟨𝒞, ?_, ?_, ?_⟩
      · intro B hB
        obtain ⟨hB1, hB2⟩ := h𝒞1 B hB
        refine ⟨hB1, ?_⟩
        rw [hB2]
        have h_pow : n - (n - r) = r := by omega
        rw [h_pow]
        exact hr.1
      · intro x hx hx_len
        exact h𝒞2 x hx
      · have hA_card : (cylinder n u).card = 2 ^ (n - u.length) := by
          rw [cylinder_card n u hu]
        rw [hA_card, h𝒞3, cylinderOverhead]
        have h1 : 2 ^ (n - r - u.length) * c ≤ 2 ^ (n - r - u.length) * 2 ^ (r + 1) :=
          Nat.mul_le_mul_left _ hr.2.le
        have h2 : 2 ^ (n - r - u.length) * 2 ^ (r + 1) = 2 * 2 ^ (n - u.length) := by
          rw [← pow_add]
          have h_pow_eq : n - r - u.length + (r + 1) = n - u.length + 1 := by omega
          rw [h_pow_eq, pow_add, pow_one, mul_comm]
        exact h1.trans (by rw [h2])
    · refine ⟨[], by simp, ?_, by simp [cylinderOverhead]⟩
      intro x hx hx_len
      rw [mem_cylinder] at hx
      have hx_len' : x.length = N := hx.1
      omega

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
