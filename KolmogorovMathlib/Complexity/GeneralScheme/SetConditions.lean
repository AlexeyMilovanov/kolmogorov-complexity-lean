import KolmogorovMathlib.Complexity.GeneralScheme.OracleDefs
import KolmogorovMathlib.Prefix.StableDecompressors

/-!
# Complexity with a set as condition: definitions and basic facts (SUV Section 6.4.2)

SUV Section 6.4.2 (printed p. 203) defines `C(x ‖ A)`: the complexity of obtaining `x` from an
arbitrary element of a set `A`. `C_D(x ‖ A)` is the least length of a `p` with `D(p, y) = x` for
every `y ∈ A`. The prefix versions `K(x ‖ A)` (prefix-stable decompressors) and `K'(x ‖ A)`
(prefix-free decompressors) are defined on printed pp. 207–208. `atLeast n` is the set of (the
strings of) the integers `≥ n`. Numbers are coded by `Nat.bits`, as in the library's conditions
`condK U x (Nat.bits n)`.

This module contains SUV Problem 206 and the unnumbered facts of printed p. 204.
-/

namespace Kolmogorov

namespace GeneralScheme

open Nat.Partrec (Code)

/-- `C_D(x ‖ A)`: the least length of a program `p` with `D(p, y) = x` for every `y ∈ A`. -/
noncomputable def setCondK (D : Map) (x : BitString) (A : Set BitString) : ℕ∞ :=
  sInf {l : ℕ∞ | ∃ p, (∀ y ∈ A, produces D p y x) ∧ l = p.length}

/-- An optimal decompressor for set conditions (plain version). -/
def IsOptimalSetCond (U : Map) : Prop :=
  isDecompressor U ∧ ∀ D, isDecompressor D → ∃ c : ℕ, ∀ x A, setCondK U x A ≤ setCondK D x A + c

/-- An optimal prefix-stable decompressor for set conditions: `K(x ‖ A)` (printed p. 207). -/
def IsOptimalPrefixStableSetCond (U : Map) : Prop :=
  IsPrefixStableDecompressor U ∧
    ∀ D, IsPrefixStableDecompressor D → ∃ c : ℕ, ∀ x A, setCondK U x A ≤ setCondK D x A + c

/-- An optimal prefix-free decompressor for set conditions: `K'(x ‖ A)` (printed p. 207). -/
def IsOptimalPrefixFreeSetCond (U : Map) : Prop :=
  IsPrefixDecompressor U ∧
    ∀ D, IsPrefixDecompressor D → ∃ c : ℕ, ∀ x A, setCondK U x A ≤ setCondK D x A + c

/-- The first definition of `C(x ‖ A)` (printed p. 204): the least plain complexity of a program
(a `Nat.Partrec.Code`, text `Nat.bits e`) that maps every element of `A` to `x`. This is the
same convention as `programComplexity` (Exercise 28). -/
noncomputable def setProgramComplexity (U : Map) (x : BitString) (A : Set BitString) : ℕ∞ :=
  ⨅ (e : ℕ)
    (_ : ∀ y ∈ A, Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y)),
    plainK U (Nat.bits e)

/-- The set of (the strings `Nat.bits m` of) the integers `m ≥ n`. -/
def atLeast (n : ℕ) : Set BitString :=
  Nat.bits '' Set.Ici n

/-- **SUV Section 6.4.2 (printed p. 204), unnumbered.** `C_D(x ‖ A)` can only decrease when `A`
becomes smaller: a program that works for every element of `B` works for every element of
`A ⊆ B`. -/
theorem setCondK_mono (D : Map) (x : BitString) {A B : Set BitString} (h : A ⊆ B) :
    setCondK D x A ≤ setCondK D x B :=
  sInf_le_sInf fun _ ⟨p, hp, hl⟩ => ⟨p, fun y hy => hp y (h hy), hl⟩

/-- **SUV Section 6.4.2 (printed p. 204), unnumbered.** `C(x ‖ ≥ n)` is a non-increasing
function of `n`: the sets `atLeast n` decrease (`setCondK_mono`). Hence its limit is its
infimum (used in Theorems 131 and 134). -/
theorem antitone_setCondK_atLeast (D : Map) (x : BitString) :
    Antitone fun n => setCondK D x (atLeast n) :=
  fun _ _ h => setCondK_mono D x (Set.image_mono (Set.Ici_subset_Ici.2 h))

/-- **SUV Problem 206 (Section 6.4.2, printed p. 204), part 1.** There is an optimal decompressor
for set conditions.

Proof idea: the universal decompressor `U(ẑ p, y) = D_z(p, y)` works for all sets at once,
because "`D_z(p, y) = x` for all `y ∈ A`" transfers to `ẑ p`. -/
theorem exists_isOptimalSetCond : ∃ U, IsOptimalSetCond U := by
  refine ⟨universalDecompressor, isDecompressor_universalDecompressor, fun D hD => ?_⟩
  obtain ⟨code, hc⟩ := exists_code_of_isDecompressor D hD
  refine ⟨(unaryPrefix (Encodable.encode code)).length, fun x A => ?_⟩
  apply sInfLeSInfAdd
  rintro len_p ⟨p, hp_out, rfl⟩
  refine ⟨((unaryPrefix (Encodable.encode code) ++ p).length : ENat), ?_, ?_⟩
  · refine ⟨unaryPrefix (Encodable.encode code) ++ p, fun y hy => ?_, rfl⟩
    change x ∈ universalDecompressor _
    rw [universal_simulation, hc]
    exact hp_out y hy
  · rw [List.length_append]
    push_cast
    rw [add_comm]

/-- Auxiliary decompressor for the target: run `V(p, [])` to get a program `e`, then run the code
`e` on the condition. -/
private def exists_const_setCondK_eq_setProgramComplexity_D1 (V : Map) : Map := fun (p, y) =>
  (V (p, [])).bind fun b =>
    ((Denumerable.ofNat Code (decodeBits b)).eval (Encodable.encode y)).bind fun val =>
      Part.ofOption (Encodable.decode (α := BitString) val)

private lemma exists_const_setCondK_eq_setProgramComplexity_D1_partrec {V : Map}
    (hV : isDecompressor V) :
    isDecompressor (exists_const_setCondK_eq_setProgramComplexity_D1 V) := by
  have hV_app : Partrec (fun (py : BitString × BitString) => V (py.1, [])) :=
    Partrec.comp hV (Computable.pair Computable.fst (Computable.const []))
  have h_c : Computable (fun (p : (BitString × BitString) × BitString) =>
      Denumerable.ofNat Code (decodeBits p.2)) :=
    (Computable.ofNat Code).comp (decodeBits_computable.comp Computable.snd)
  have h_y : Computable (fun (p : (BitString × BitString) × BitString) =>
      Encodable.encode p.1.2) :=
    Computable.encode.comp (Computable.snd.comp Computable.fst)
  have h_pair : Computable (fun (p : (BitString × BitString) × BitString) =>
      (Denumerable.ofNat Code (decodeBits p.2), Encodable.encode p.1.2)) :=
    Computable.pair h_c h_y
  have h_eval : Partrec (fun (p : (BitString × BitString) × BitString) =>
      Code.eval (Denumerable.ofNat Code (decodeBits p.2)) (Encodable.encode p.1.2)) :=
    Partrec.comp Code.eval_part h_pair
  have h_dec : Computable (fun (p : ((BitString × BitString) × BitString) × ℕ) =>
      Encodable.decode (α := BitString) p.2) :=
    Computable.decode.comp Computable.snd
  have h_opt : Partrec (fun (p : ((BitString × BitString) × BitString) × ℕ) =>
      Part.ofOption (Encodable.decode (α := BitString) p.2)) :=
    Computable.ofOption h_dec
  have h_step2 : Partrec (fun (p : (BitString × BitString) × BitString) =>
      (Code.eval (Denumerable.ofNat Code (decodeBits p.2)) (Encodable.encode p.1.2)).bind
        (fun val => Part.ofOption (Encodable.decode (α := BitString) val))) :=
    Partrec.bind h_eval h_opt
  exact Partrec.bind hV_app h_step2

private lemma exists_const_setCondK_eq_setProgramComplexity_D1_eval {V : Map} {x y : BitString}
    {e : ℕ} {p : BitString} (hp : Nat.bits e ∈ V (p, []))
    (he : Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y)) :
    produces (exists_const_setCondK_eq_setProgramComplexity_D1 V) p y x := by
  dsimp [produces, exists_const_setCondK_eq_setProgramComplexity_D1]
  rw [Part.mem_bind_iff]
  refine ⟨Nat.bits e, hp, ?_⟩
  rw [decodeBits_natBits]
  rw [Part.mem_bind_iff]
  refine ⟨Encodable.encode x, he, ?_⟩
  rw [Part.mem_ofOption]
  exact Encodable.encodek x

/-- Step 1: `C_D1(x ‖ A) ≤` the first definition. -/
private lemma exists_const_setCondK_eq_setProgramComplexity_D1_le {V : Map} (x : BitString)
    (A : Set BitString) :
    setCondK (exists_const_setCondK_eq_setProgramComplexity_D1 V) x A ≤
      setProgramComplexity V x A := by
  unfold setProgramComplexity
  refine le_iInf₂ fun e he => ?_
  unfold plainK condK
  refine le_sInf ?_
  rintro n ⟨p, hp, rfl⟩
  exact sInf_le ⟨p, fun y hy =>
    exists_const_setCondK_eq_setProgramComplexity_D1_eval hp (he y hy), rfl⟩

private def exists_const_setCondK_eq_setProgramComplexity_H (U : Map) : ℕ →. ℕ := fun m =>
  (Part.ofOption (Encodable.decode (α := BitString × ℕ) m)).bind fun pn =>
    (Part.ofOption (Encodable.decode (α := BitString) pn.2)).bind fun y =>
      (U (pn.1, y)).map Encodable.encode

private lemma exists_const_setCondK_eq_setProgramComplexity_H_partrec {U : Map}
    (hU : Partrec U) : Partrec (exists_const_setCondK_eq_setProgramComplexity_H U) := by
  have h_dec : Computable (fun m => Encodable.decode (α := BitString × ℕ) m) :=
    Computable.decode
  have h_opt : Partrec (fun m => Part.ofOption (Encodable.decode (α := BitString × ℕ) m)) :=
    Computable.ofOption h_dec
  have h_H : Partrec (fun (p : ℕ × (BitString × ℕ)) =>
      (Part.ofOption (Encodable.decode (α := BitString) p.2.2)).bind fun y =>
        (U (p.2.1, y)).map Encodable.encode) := by
    have h_dec' : Computable (fun (p : ℕ × (BitString × ℕ)) =>
        Encodable.decode (α := BitString) p.2.2) :=
      Computable.decode.comp (Computable.snd.comp Computable.snd)
    have h_opt' : Partrec (fun (p : ℕ × (BitString × ℕ)) =>
        Part.ofOption (Encodable.decode (α := BitString) p.2.2)) :=
      Computable.ofOption h_dec'
    refine Partrec.bind h_opt' ?_
    have h_pair : Computable (fun (p : (ℕ × (BitString × ℕ)) × BitString) => (p.1.2.1, p.2)) :=
      Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst)) Computable.snd
    have h_U_app : Partrec (fun (p : (ℕ × (BitString × ℕ)) × BitString) =>
        U (p.1.2.1, p.2)) := Partrec.comp hU h_pair
    exact Partrec.map h_U_app (Computable.encode.comp Computable.snd)
  exact Partrec.bind h_opt h_H

private def exists_const_setCondK_eq_setProgramComplexity_F (cH : Code) (p : BitString) : ℕ :=
  Encodable.encode (cH.curry (Encodable.encode p))

private lemma exists_const_setCondK_eq_setProgramComplexity_F_computable (cH : Code) :
    Computable (exists_const_setCondK_eq_setProgramComplexity_F cH) := by
  have h1 : Computable (fun p : BitString => Encodable.encode p) := Computable.encode
  have h2 : Computable (fun p : BitString => cH.curry (Encodable.encode p)) :=
    (Primrec₂.to_comp Code.primrec₂_curry).comp (Computable.const cH) h1
  exact Computable.encode.comp h2

private lemma exists_const_setCondK_eq_setProgramComplexity_F_eval {U : Map} {cH : Code}
    (hcH : Code.eval cH = exists_const_setCondK_eq_setProgramComplexity_H U) (p x y : BitString)
    (h_prod : x ∈ U (p, y)) :
    Encodable.encode x ∈
      (Denumerable.ofNat Code (exists_const_setCondK_eq_setProgramComplexity_F cH p)).eval
        (Encodable.encode y) := by
  dsimp [exists_const_setCondK_eq_setProgramComplexity_F]
  rw [Denumerable.ofNat_encode, Code.eval_curry, hcH]
  dsimp [exists_const_setCondK_eq_setProgramComplexity_H]
  refine Part.mem_bind_iff.mpr ⟨(p, Encodable.encode y), ?_, ?_⟩
  · rw [Part.mem_ofOption]
    exact show Encodable.decode (α := BitString × ℕ)
          (Nat.pair (Encodable.encode p) (Encodable.encode y)) =
        some (p, Encodable.encode y) by simp
  · rw [Part.mem_bind_iff]
    refine ⟨y, ?_, ?_⟩
    · rw [Part.mem_ofOption]
      exact Encodable.encodek y
    · rw [Part.mem_map_iff]
      exact ⟨x, h_prod, rfl⟩

/-- Step 2: the first definition is at most `C_U(x ‖ A)` plus a constant. -/
private lemma exists_const_setCondK_eq_setProgramComplexity_le {U : Map}
    (hU : isDecompressor U) {V : Map} (hV : isOptimalConditional V) :
    ∃ k : ℕ, ∀ x A, setProgramComplexity V x A ≤ setCondK U x A + (k : ℕ∞) := by
  obtain ⟨cH, hcH⟩ := Code.exists_code.mp
    (Partrec.nat_iff.mp (exists_const_setCondK_eq_setProgramComplexity_H_partrec hU))
  obtain ⟨c_map, hc_map⟩ := plainK_map_le V hV
    (fun p => Nat.bits (exists_const_setCondK_eq_setProgramComplexity_F cH p))
    (natBits_computable.comp (exists_const_setCondK_eq_setProgramComplexity_F_computable cH))
  obtain ⟨c_len, hc_len⟩ := plainK_le_length V hV
  refine ⟨c_len + c_map, fun x A => ?_⟩
  by_cases hne : {l : ℕ∞ | ∃ p, (∀ y ∈ A, produces U p y x) ∧ l = p.length}.Nonempty
  · obtain ⟨p, hp, hl⟩ := csInf_mem hne
    have hmem : setCondK U x A = (p.length : ℕ∞) := hl.symm ▸ rfl
    have hprog : setProgramComplexity V x A ≤
        plainK V (Nat.bits (exists_const_setCondK_eq_setProgramComplexity_F cH p)) :=
      iInf₂_le (exists_const_setCondK_eq_setProgramComplexity_F cH p) fun y hy =>
        exists_const_setCondK_eq_setProgramComplexity_F_eval hcH p x y (hp y hy)
    refine hprog.trans ?_
    calc plainK V (Nat.bits (exists_const_setCondK_eq_setProgramComplexity_F cH p))
        ≤ plainK V p + (c_map : ℕ∞) := hc_map p
      _ ≤ ((programLength p : ℕ∞) + (c_len : ℕ∞)) + (c_map : ℕ∞) := by gcongr; exact hc_len p
      _ = setCondK U x A + ((c_len + c_map : ℕ) : ℕ∞) := by
        rw [hmem]; push_cast; simp [add_assoc]
  · have : setCondK U x A = ⊤ := by
      unfold setCondK
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact sInf_empty
    rw [this]; simp

/-- **SUV Problem 206 (Section 6.4.2, printed p. 204), part 2.** For an optimal `U`, `C_U(x ‖ A)`
coincides up to `O(1)` with the first definition: the least complexity of a program that maps
every element of `A` to `x`.

Proof idea: as for Exercise 28 (`condK_eq_min_program_complexity`), uniformly in `A`. A
description `p` gives the program "run `U(p, ·)`", whose complexity is `≤ l(p) + O(1)`.
Conversely the decompressor "decompress a program and run it" gives the other direction. -/
theorem exists_const_setCondK_eq_setProgramComplexity {U : Map} (hU : IsOptimalSetCond U)
    {V : Map} (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x A,
      setCondK U x A ≤ setProgramComplexity V x A + c ∧
        setProgramComplexity V x A ≤ setCondK U x A + c := by
  obtain ⟨k1, hk1⟩ := hU.2 _ (exists_const_setCondK_eq_setProgramComplexity_D1_partrec hV.1)
  obtain ⟨k2, hk2⟩ := exists_const_setCondK_eq_setProgramComplexity_le hU.1 hV
  refine ⟨max k1 k2, fun x A => ⟨?_, ?_⟩⟩
  · calc setCondK U x A
        ≤ setCondK (exists_const_setCondK_eq_setProgramComplexity_D1 V) x A + (k1 : ℕ∞) :=
          hk1 x A
      _ ≤ setProgramComplexity V x A + (max k1 k2 : ℕ) := by
        gcongr
        · exact exists_const_setCondK_eq_setProgramComplexity_D1_le x A
        · exact_mod_cast le_max_left k1 k2
  · calc setProgramComplexity V x A ≤ setCondK U x A + (k2 : ℕ∞) := hk2 x A
      _ ≤ setCondK U x A + (max k1 k2 : ℕ) := by
        gcongr
        exact_mod_cast le_max_right k1 k2

/-- **SUV Section 6.4.2 (printed p. 204), unnumbered.** For a singleton `A = {a}`, `C(x ‖ A)` is
the conditional complexity `C(x | a)` up to `O(1)` (compare Problem 28). -/
theorem exists_const_setCondK_singleton_eq_condK {U : Map} (hU : IsOptimalSetCond U) {V : Map}
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x a, setCondK U x {a} ≤ condK V x a + c ∧ condK V x a ≤ setCondK U x {a} + c := by
  obtain ⟨c₁, hc₁⟩ := hU.2 V hV.1
  obtain ⟨c₂, hc₂⟩ := hV.2 U hU.1
  have h₁ : ∀ x a, setCondK V x {a} ≤ condK V x a := fun x a =>
    sInf_le_sInf fun _ ⟨p, hp, hn⟩ =>
      ⟨p, fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hp, hn.symm⟩
  have h₂ : ∀ x a, condK U x a ≤ setCondK U x {a} := fun x a =>
    sInf_le_sInf fun _ ⟨p, hp, hn⟩ => ⟨p, hp a (Set.mem_singleton a), hn.symm⟩
  have hc₁' : (c₁ : ℕ∞) ≤ ((max c₁ c₂ : ℕ) : ℕ∞) := by exact_mod_cast le_max_left c₁ c₂
  have hc₂' : (c₂ : ℕ∞) ≤ ((max c₁ c₂ : ℕ) : ℕ∞) := by exact_mod_cast le_max_right c₁ c₂
  exact ⟨max c₁ c₂, fun x a =>
    ⟨(hc₁ x {a}).trans (add_le_add (h₁ x a) hc₁'), (hc₂ x a).trans (add_le_add (h₂ x a) hc₂')⟩⟩

/-- **SUV Section 6.4.2 (printed p. 204), unnumbered.** `C(x ‖ A) ≤ C(x) + O(1)` for every set
`A`. A decompressor that ignores the condition works for every `A`. -/
theorem exists_const_setCondK_le_plainK {U : Map} (hU : IsOptimalSetCond U) {V : Map}
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x A, setCondK U x A ≤ plainK V x + c := by
  let D : Map := fun q => V (q.1, [])
  have hD : isDecompressor D := hV.1.comp (Computable.fst.pair (Computable.const []))
  obtain ⟨c, hc⟩ := hU.2 D hD
  refine ⟨c, fun x A => (hc x A).trans (add_le_add ?_ le_rfl)⟩
  exact sInf_le_sInf fun _ ⟨p, hp, hn⟩ => ⟨p, fun _ _ => hp, hn.symm⟩

/-- **SUV Section 6.4.2 (printed p. 204), unnumbered.** For the empty set, `C(x ‖ ∅)` is `0`
(the book says `O(1)`). Every decompressor maps every element of `∅` to `x`. -/
theorem setCondK_empty (D : Map) (x : BitString) : setCondK D x ∅ = 0 :=
  le_antisymm (sInf_le ⟨[], fun _ hy => absurd hy (Set.notMem_empty _), by simp⟩) zero_le

end GeneralScheme

end Kolmogorov
