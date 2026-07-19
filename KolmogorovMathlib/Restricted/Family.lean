import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.Encoding.Tuples

/-!
# M1: description families and the restricted profile

Plan reference: `PLAN_RESTRICTED_TYPE.md`, milestone M1. This file is owned by
the `M1_description_family` proof-loop section.

VS40 §6 conditions on a family 𝒜 of finite sets of strings:
(1) enumerability, (2) full cubes `𝔹ⁿ ∈ 𝒜`, (3) polynomial covering. The
covering overhead is an EXPLICIT function `overhead : ℕ → ℕ` (not "some
polynomial"): downstream slack is `logSlack` of it, so polynomial growth only
matters where a final `O(log n)` is claimed.
-/

namespace Kolmogorov

/-- Condition (1): a staged computable enumeration of the canonical codes of
the family members — sound (everything enumerated is a member's code) and
complete (every member's code eventually appears). -/
structure FamilyEnumeration (mem : Finset BitString → Prop) where
  enum : ℕ → List BitString
  computable : Computable enum
  mono : ∀ t, enum t <+: enum (t + 1)
  sound : ∀ t, ∀ w ∈ enum t, ∃ (S : Finset BitString) (hS : S.Nonempty),
    mem S ∧ w = (codedUniformOn S hS).code
  complete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S →
    ∃ t, (codedUniformOn S hS).code ∈ enum t

/-- A *pre*-description family: only condition (1) (an enumerable membership
predicate whose members are nonempty).  The effective-selection and
description-counting machinery only needs this much; the full
`DescriptionFamily` (conditions (1)–(3)) coerces into it. -/
structure PreDescriptionFamily where
  mem : Finset BitString → Prop
  nonempty_of_mem : ∀ {S : Finset BitString}, mem S → S.Nonempty
  enumeration : FamilyEnumeration mem

/-- A description family in the sense of VS40 §6 (conditions (1)–(3)). -/
structure DescriptionFamily where
  mem : Finset BitString → Prop
  nonempty_of_mem : ∀ {S : Finset BitString}, mem S → S.Nonempty
  /-- Condition (1). -/
  enumeration : FamilyEnumeration mem
  /-- Condition (2). -/
  fullCube : ∀ n : ℕ, mem (stringsOfLength n)
  /-- Covering overhead of condition (3); "polynomial" is a separate mixin. -/
  overhead : ℕ → ℕ
  overhead_pos : ∀ n, 0 < overhead n
  /-- Condition (3): the `n`-bit part of a member `A` is covered by members
  of cardinality ≤ `c`, with at most `overhead n · #A / c` covering sets
  (stated multiplicatively: `count · c ≤ overhead n · #A`). -/
  cover : ∀ {A : Finset BitString}, mem A → ∀ (n c : ℕ), 0 < c → c ≤ A.card →
    ∃ 𝒞 : List (Finset BitString),
      (∀ B ∈ 𝒞, mem B ∧ B.card ≤ c) ∧
      (∀ x ∈ A, x.length = n → ∃ B ∈ 𝒞, x ∈ B) ∧
      𝒞.length * c ≤ overhead n * A.card

/-- The polynomial overhead condition (used in M7). -/
def DescriptionFamily.HasPolynomialOverhead (𝒜 : DescriptionFamily) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ n, 𝒜.overhead n ≤ C * (n + 1) ^ d

/-- A polynomial covering overhead contributes only logarithmically many bits. -/
theorem DescriptionFamily.overhead_bits_le_logSlack (𝒜 : DescriptionFamily)
    (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_over : ℕ, ∀ n, (Nat.bits (𝒜.overhead n)).length ≤ logSlack c_over n := by
  rcases hPoly with ⟨C, d, hC, hbound⟩
  obtain ⟨c_over, hover⟩ := polynomialOverhead_bits_le_logSlack C d hC
  exact ⟨c_over, fun n =>
    (length_natBits_mono (hbound n)).trans (hover n)⟩

/-- Forget conditions (2)–(3), keeping only the enumerable membership data. -/
def DescriptionFamily.toPre (𝒜 : DescriptionFamily) : PreDescriptionFamily where
  mem := 𝒜.mem
  nonempty_of_mem := 𝒜.nonempty_of_mem
  enumeration := 𝒜.enumeration

instance : Coe DescriptionFamily PreDescriptionFamily := ⟨DescriptionFamily.toPre⟩

@[simp] theorem DescriptionFamily.toPre_mem (𝒜 : DescriptionFamily) :
    (𝒜.toPre).mem = 𝒜.mem := rfl

@[simp] theorem DescriptionFamily.toPre_enumeration (𝒜 : DescriptionFamily) :
    (𝒜.toPre).enumeration = 𝒜.enumeration := rfl

/-- Restricted `(i,j)`-description: an ordinary `(i,j)`-description that
belongs to the family. -/
noncomputable def IsIJDescriptionIn (𝒜 : DescriptionFamily) (U : Map)
    (x : BitString) (S : Finset BitString) (hS : S.Nonempty) (i j : ℕ) : Prop :=
  𝒜.mem S ∧ IsIJDescription U x S hS i j

/-- The restricted description profile `P_x^𝒜`. -/
noncomputable def InDescriptionProfileIn (𝒜 : DescriptionFamily) (U : Map)
    (x : BitString) (i j : ℕ) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty), IsIJDescriptionIn 𝒜 U x S hS i j

/-- The restricted profile is contained in the unrestricted one, `P_x^𝒜 ⊆ P_x`:
forgetting the family-membership condition turns a restricted `(i,j)`-description
into an ordinary `(i,j)`-description. -/
theorem inDescriptionProfileIn_imp_inDescriptionProfile {𝒜 : DescriptionFamily}
    {U : Map} {x : BitString} {i j : ℕ}
    (h : InDescriptionProfileIn 𝒜 U x i j) : InDescriptionProfile U x i j := by
  rcases h with ⟨S, hS, _hmem, hdesc⟩
  exact ⟨S, hS, hdesc⟩

/-! ### The full family -/

/-- Normalize an arbitrary decoded list into a nonempty canonical list.  Empty
decoded inputs are sent to the singleton `{[]}`; nonempty inputs are replaced by
the canonical sorted enumeration of their underlying finite set. -/
noncomputable def fullFamilyCanonicalList (w : BitString) : List BitString :=
  match decodeListCode w with
  | [] => [[]]
  | _ :: _ => canonicalFinsetList (decodeListCode w).toFinset

theorem fullFamilyCanonicalList_primrec : Primrec fullFamilyCanonicalList := by
  unfold fullFamilyCanonicalList
  have hcons : Primrec (fun p : BitString × List BitString =>
      canonicalFinsetList (p.1 :: p.2).toFinset) := by
    convert canonicalFinsetList_toFinset_primrec.comp
      (Primrec.list_cons.comp Primrec.fst Primrec.snd) using 1
  exact (Primrec.list_casesOn (decodeListCode_primrec.comp Primrec.id)
    (Primrec.const [[]]) ((hcons.comp Primrec.snd).to₂)).of_eq (fun w => by
    cases h : decodeListCode w <;> simp [h])

/-- Stage `t` of the full-family enumeration: decode every bitstring of length
at most `t` as a list, normalize it to a nonempty canonical finite-set list, and
emit the corresponding canonical uniform code. -/
noncomputable def fullFamilyEnum (t : ℕ) : List BitString :=
  (boundedPrograms t).map fun w =>
    canonicalUniformCodeOfList (fullFamilyCanonicalList w)

theorem fullFamilyEnum_computable : Computable fullFamilyEnum := by
  unfold fullFamilyEnum
  exact (Primrec.list_map primrec_boundedPrograms
    ((canonicalUniformCodeOfList_primrec.comp
      (fullFamilyCanonicalList_primrec.comp Primrec.snd)).to₂)).to_comp

theorem fullFamilyEnum_mono (t : ℕ) :
    fullFamilyEnum t <+: fullFamilyEnum (t + 1) := by
  unfold fullFamilyEnum
  rw [boundedPrograms_succ, List.map_append]
  exact (boundedPrograms t).map (fun w =>
    canonicalUniformCodeOfList (fullFamilyCanonicalList w)) |>.prefix_append _

theorem fullFamilyCanonicalList_nonempty (w : BitString) :
    ∃ x, x ∈ fullFamilyCanonicalList w := by
  unfold fullFamilyCanonicalList
  cases h : decodeListCode w with
  | nil => exact ⟨[], by simp⟩
  | cons x xs => exact ⟨x, by simp⟩

theorem fullFamilyCanonicalList_is_canonical (w : BitString) :
    canonicalFinsetList (fullFamilyCanonicalList w).toFinset =
      fullFamilyCanonicalList w := by
  unfold fullFamilyCanonicalList
  cases h : decodeListCode w with
  | nil =>
      unfold canonicalFinsetList
      simp
  | cons x xs =>
      simp

theorem InDescriptionProfileIn.mono_i {𝒜 : DescriptionFamily} {U : Map}
    {x : BitString} {i i' j : ℕ} (h : i ≤ i')
    (hp : InDescriptionProfileIn 𝒜 U x i j) :
    InDescriptionProfileIn 𝒜 U x i' j := by
  rcases hp with ⟨S, hS, hmem, hdesc⟩
  exact ⟨S, hS, hmem, hdesc.mono_i h⟩

theorem InDescriptionProfileIn.mono_j {𝒜 : DescriptionFamily} {U : Map}
    {x : BitString} {i j j' : ℕ} (h : j ≤ j')
    (hp : InDescriptionProfileIn 𝒜 U x i j) :
    InDescriptionProfileIn 𝒜 U x i j' := by
  rcases hp with ⟨S, hS, hmem, hdesc⟩
  exact ⟨S, hS, hmem, hdesc.mono_j h⟩

/-- Full family chunk cover helper. -/
lemma fullFamily_chunk_cover (A : Finset BitString) (n c : ℕ) (hc_pos : 0 < c) (hc_le : c ≤ A.card)
    :
    ∃ 𝒞 : List (Finset BitString),
      (∀ B ∈ 𝒞, B.Nonempty ∧ B.card ≤ c) ∧
      (∀ x ∈ A, x.length = n → ∃ B ∈ 𝒞, x ∈ B) ∧
      𝒞.length * c ≤ 3 * A.card := by
  classical
  let T : Finset BitString := A.filter fun x => x.length = n
  let L : List BitString := canonicalFinsetList T
  let q : ℕ := (L.length + c - 1) / c
  let cover : List (Finset BitString) :=
    (List.range q).map fun k => ((L.drop (k * c)).take c).toFinset
  refine ⟨cover, ?_, ?_, ?_⟩
  · intro B hB
    rw [List.mem_map] at hB
    rcases hB with ⟨k, hk, rfl⟩
    have hkq : k < q := List.mem_range.mp hk
    have hkdiv : k < (L.length + c - 1) / c := by simpa [q] using hkq
    have hstart0 : k * c < (L.length + c - 1) - (c - 1) :=
      (Nat.lt_div_iff_mul_lt hc_pos).mp hkdiv
    have hcancel : (L.length + c - 1) - (c - 1) = L.length := by omega
    have hstart : k * c < L.length := by simpa [hcancel] using hstart0
    have hdrop : 0 < (L.drop (k * c)).length := by
      rw [List.length_drop]
      omega
    have hchunk : 0 < ((L.drop (k * c)).take c).length := by
      rw [List.length_take]
      exact lt_min hc_pos hdrop
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos hchunk)
    refine ⟨⟨x, List.mem_toFinset.mpr hx⟩, ?_⟩
    exact (List.toFinset_card_le _).trans (by simp)
  · intro x hxA hxlen
    have hxT : x ∈ T := by simp [T, hxA, hxlen]
    have hxL : x ∈ L := by simpa [L] using (mem_canonicalFinsetList.mpr hxT)
    obtain ⟨p, hp, hpx⟩ := List.mem_iff_getElem.mp hxL
    let k := p / c
    have hkc : k * c ≤ p := by
      simpa [k, Nat.mul_comm] using Nat.div_mul_le_self p c
    have hrem : p - k * c < c := by
      have hmod := Nat.mod_lt p hc_pos
      have hdecomp : p / c * c + p % c = p := by
        simpa [Nat.mul_comm] using Nat.div_add_mod p c
      dsimp [k]
      omega
    have hstart : k * c < L.length := lt_of_le_of_lt hkc hp
    have hkdiv : k < (L.length + c - 1) / c := by
      apply (Nat.lt_div_iff_mul_lt hc_pos).mpr
      have hcancel : (L.length + c - 1) - (c - 1) = L.length := by omega
      simpa [hcancel] using hstart
    refine ⟨((L.drop (k * c)).take c).toFinset, ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨k, List.mem_range.mpr (by simpa [q] using hkdiv), rfl⟩
    · rw [List.mem_toFinset, List.mem_iff_getElem]
      have hdecomp : k * c + (p - k * c) = p := by omega
      have htail : p - k * c < L.length - k * c := by omega
      have hidx : p - k * c < ((L.drop (k * c)).take c).length := by
        rw [List.length_take, List.length_drop]
        exact lt_min hrem htail
      refine ⟨p - k * c, hidx, ?_⟩
      rw [List.getElem_take, List.getElem_drop]
      simpa only [hdecomp] using hpx
  · rw [List.length_map, List.length_range]
    have hqmul : q * c ≤ L.length + c - 1 := by
      dsimp [q]
      exact Nat.div_mul_le_self _ _
    have hLle : L.length ≤ A.card := by
      dsimp [L]
      rw [length_canonicalFinsetList]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    omega

/-- The unrestricted case as an instance: the family of ALL nonempty finite
sets. (Enumeration: enumerate all canonical uniform codes.) -/
noncomputable def fullFamily : DescriptionFamily := by
  refine
    { mem := fun S => S.Nonempty
      nonempty_of_mem := fun h => h
      enumeration := ?_
      fullCube := ?_
      overhead := fun _ => 3
      overhead_pos := ?_
      cover := ?_ }
  · refine
      { enum := fullFamilyEnum
        computable := fullFamilyEnum_computable
        mono := fullFamilyEnum_mono
        sound := ?_
        complete := ?_ }
    · intro t w hw
      unfold fullFamilyEnum at hw
      rw [List.mem_map] at hw
      rcases hw with ⟨v, hv, rfl⟩
      let S : Finset BitString := (fullFamilyCanonicalList v).toFinset
      have hS : S.Nonempty := by
        rcases fullFamilyCanonicalList_nonempty v with ⟨x, hx⟩
        exact ⟨x, by simpa [S] using hx⟩
      refine ⟨S, hS, hS, ?_⟩
      calc
        canonicalUniformCodeOfList (fullFamilyCanonicalList v)
            = canonicalUniformCodeOfList (canonicalFinsetList S) := by
                rw [fullFamilyCanonicalList_is_canonical v]
        _ = (codedUniformOn S hS).code :=
                canonicalUniformCodeOfList_canonicalFinsetList S hS
    · intro S hS hmem
      refine ⟨(listCode (canonicalFinsetList S)).length, ?_⟩
      unfold fullFamilyEnum
      rw [List.mem_map]
      refine ⟨listCode (canonicalFinsetList S), ?_, ?_⟩
      · exact (mem_boundedPrograms_iff _ _).mpr le_rfl
      · have hne : canonicalFinsetList S ≠ [] := by
          intro hnil
          have hcard : S.card = 0 := by
            rw [← length_canonicalFinsetList S, hnil]
            rfl
          exact (Finset.card_pos.mpr hS).ne' hcard
        unfold fullFamilyCanonicalList
        rw [decodeListCode_listCode]
        cases hcanon : canonicalFinsetList S with
        | nil => exact False.elim (hne hcanon)
        | cons x xs =>
            have hfin : (x :: xs).toFinset = S := by
              rw [← hcanon, canonicalFinsetList_toFinset]
            rw [hfin]
            exact canonicalUniformCodeOfList_canonicalFinsetList S hS
  · intro n
    exact codedStringsOfLength_nonempty n
  · intro n
    exact by decide
  · intro A hA n c hc_pos hc_le
    exact fullFamily_chunk_cover A n c hc_pos hc_le

/-- The full family has constant covering overhead after chunking. -/
theorem fullFamily_hasPolynomialOverhead : fullFamily.HasPolynomialOverhead := by
  refine ⟨3, 0, by decide, ?_⟩
  intro n
  simp [fullFamily]

/-- Sanity (mandatory before building on M1): the restricted profile for
`fullFamily` is the unrestricted profile. -/
theorem inDescriptionProfileIn_fullFamily_iff (U : Map) (x : BitString)
    (i j : ℕ) :
    InDescriptionProfileIn fullFamily U x i j ↔ InDescriptionProfile U x i j := by
  constructor
  · rintro ⟨S, hS, _hmem, hdesc⟩
    exact ⟨S, hS, hdesc⟩
  · rintro ⟨S, hS, hdesc⟩
    exact ⟨S, hS, hS, hdesc⟩

/-- Derived from (2)+(3): every singleton over `𝔹ⁿ` belongs to the family
(needed for the `(K(x)+O(1), 0)` profile point in M2). -/
theorem DescriptionFamily.singleton_mem (𝒜 : DescriptionFamily)
    (x : BitString) : 𝒜.mem {x} := by
  have hcube : 𝒜.mem (stringsOfLength x.length) := 𝒜.fullCube x.length
  obtain ⟨𝒞, hsmall, hcover, _hbound⟩ :=
    𝒜.cover hcube x.length 1 (by decide) (by
      rw [cardStringsOfLength]
      exact Nat.succ_le_of_lt (pow_pos (by decide) x.length))
  have hx_cube : x ∈ stringsOfLength x.length := (memStringsOfLength x.length x).mpr rfl
  obtain ⟨B, hB𝒞, hxB⟩ := hcover x hx_cube rfl
  rcases hsmall B hB𝒞 with ⟨hBmem, hBcard⟩
  have hB_eq : B = {x} := by
    exact Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hxB, fun y hy => (Finset.card_le_one.mp hBcard) y hy x hxB⟩
  simpa [hB_eq] using hBmem

end Kolmogorov
