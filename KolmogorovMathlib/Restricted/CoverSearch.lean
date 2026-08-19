import KolmogorovMathlib.Restricted.Family
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile

/-!
# M2(a3): the explicit computable cover-search decoder

This file provides the genuinely computable core behind
`exists_coverSelector` (in `BasicProfile.lean`): an explicit partial-recursive
function `coverSelectorFun 𝒜` that, given the pair code of a family member `A`
and a short address `z`, recomputes a good cover of the length-`n` part of `A`
by canonical family-enumeration search and returns the code of the addressed
covering member.

The two isolated obligations are:
* `coverSelectorFun_partrec` — the search is partial recursive;
* `coverSelectorFun_getD_mem` — the value produced by the search on the least
  valid address (the membership interface used by `exists_coverSelector`).

All correctness / termination / length bookkeeping lives in `BasicProfile.lean`,
where the combinatorial cover existence (`exists_family_cover`) is available.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Decode a canonical uniform code back to its underlying list of points
(`canonicalFinsetList` of the coded set, for a genuine code). -/
def decodeCoverCodeList (w : BitString) : List BitString :=
  (decodeDistributionData w).map CodedDistributionEntry.point

theorem decodeCoverCodeList_code (S : Finset BitString) (hS : S.Nonempty) :
    decodeCoverCodeList (codedUniformOn S hS).code = canonicalFinsetList S := by
  unfold decodeCoverCodeList
  exact dataPoints_codedUniformOn S hS

/-- Decode the address `p` into an enumeration stage together with a candidate
list of member codes.  Both are extracted through the standard `Encodable`
instance on `ℕ × List BitString`. -/
def coverDecode (p : ℕ) : ℕ × List BitString :=
  (Encodable.decode (α := ℕ × List BitString) p).getD (0, [])

/-- Validity of the candidate cover addressed by `p` for the target
`{ y ∈ A | y.length = n }`, where `A = decodeCoverCodeList Acode`,
`c = max 1 (#A / 2^k)`, and the length budget is `q0 * 2^(k+1)`.  Every candidate
code must appear in the addressed enumeration stage (so soundness applies), the
cover must be small and short, and it must cover the target.  All bounds are
computed by the decoder from `Acode`, `n`, `k`, `q0`. -/
def coverValidBool (𝒜 : DescriptionFamily) (Acode : BitString) (n k q0 : ℕ) (p : ℕ) :
    Bool :=
  let Alist := decodeCoverCodeList Acode
  let c := max 1 (Alist.dedup.length / 2 ^ k)
  let target := Alist.filter (fun y => decide (y.length = n))
  let stage := (coverDecode p).1
  let cover := (coverDecode p).2
  (cover.all (fun w => decide (w ∈ 𝒜.enumeration.enum stage))) &&
    (decide (cover.length ≤ q0 * 2 ^ (k + 1))) &&
    (cover.all (fun w => decide ((decodeCoverCodeList w).dedup.length ≤ c))) &&
    (target.all (fun y => cover.any (fun w => decide (y ∈ decodeCoverCodeList w))))

/-- The self-delimiting address for the selector: `n`, `k`, `q0` are stored with
logarithmic (`Nat.bits`) framing via `pairCode`, followed by the fixed-length
`s`-bit index `idx`.  The decoder recovers `idx = bitsToNat` of the last block. -/
def coverAddress (n k q0 idx s : ℕ) : BitString :=
  pairCode (Nat.bits n)
    (pairCode (Nat.bits k) (pairCode (Nat.bits q0) (chunkAddress idx s)))

/-- The partial-recursive cover selector for family `𝒜`.  It decodes the pair
code into `A`'s code and the address `z`, reads `n, k, q0, idx` from `z`, searches
for the least valid candidate cover, and returns the `idx`-th code of it. -/
def coverSelectorFun (𝒜 : DescriptionFamily) : BitString →. BitString := fun t =>
  let Acode := decodeFirst t
  let z := decodeSecond t
  let n := bitsToNat (decodeFirst z)
  let z1 := decodeSecond z
  let k := bitsToNat (decodeFirst z1)
  let z2 := decodeSecond z1
  let q0 := bitsToNat (decodeFirst z2)
  let idx := bitsToNat (decodeSecond z2)
  (Nat.rfind (fun p => Part.some (coverValidBool 𝒜 Acode n k q0 p))).bind
    (fun p => Part.some ((coverDecode p).2.getD idx []))

/-- `List.all` with an outer-parameter predicate, as a `Primrec` combinator
(derived from the in-scope `list_any_primrec`). -/
theorem coverSearch_list_all_primrec {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).all (p a)) := by
  have heq : (fun a => (f a).all (p a))
      = (fun a => (f a).foldr (fun b acc => p a b && acc) true) := by
    funext a; induction f a with
    | nil => rfl
    | cons b t ih => simp [List.all_cons, ih]
  rw [heq]
  have hstep : Primrec₂ (fun (a : α) (q : β × Bool) => p a q.1 && q.2) :=
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const true) hstep

theorem decodeCoverCodeList_primrec : Primrec decodeCoverCodeList := by
  unfold decodeCoverCodeList
  exact Primrec.list_map decodeDistributionData_primrec
    (entry_point_primrec.comp Primrec.snd).to₂

theorem coverDecode_primrec : Primrec coverDecode := by
  unfold coverDecode
  exact Primrec.option_getD.comp Primrec.decode (Primrec.const (0, []))

/-
The validity predicate is computable in all its arguments (the only
non-primitive-recursive ingredient is the family enumeration, which is
computable).
-/
theorem coverValidBool_computable (𝒜 : DescriptionFamily) :
    Computable (fun a : BitString × ℕ × ℕ × ℕ × ℕ =>
      coverValidBool 𝒜 a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) := by
  have andC {α} [Primcodable α] {f g : α → Bool} (hf : Computable f) (hg : Computable g) :
      Computable (fun a => f a && g a) :=
    (Computable.cond hf hg (Computable.const false)).of_eq fun a => by cases f a <;> rfl
  have h_enum : Computable
      (fun a : BitString × ℕ × ℕ × ℕ × ℕ =>
        (coverDecode a.2.2.2.2).2.all
          (fun w => w ∈ 𝒜.enumeration.enum (coverDecode a.2.2.2.2).1)) := by
    have h_primrec : Primrec
        (fun (a : List BitString × List BitString) => a.1.all (fun w => decide (w ∈ a.2))) := by
      exact (@coverSearch_list_all_primrec (List BitString × List BitString) BitString _ _
        (fun a => a.1) (fun a w => decide (w ∈ a.2)) Primrec.fst
        (bitString_mem_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).of_eq fun _ => rfl
    have h_comp : Computable
        (fun (a : BitString × ℕ × ℕ × ℕ × ℕ) => let Acode := a.1; let n := a.2.1; let k := a.2.2.1;
            let q0 := a.2.2.2.1; let p := a.2.2.2.2
            ((coverDecode p).2, 𝒜.enumeration.enum (coverDecode p).1)) := by
      apply Computable.pair;
      · apply Computable.snd.comp;
        exact Computable.comp coverDecode_primrec.to_comp
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
      · exact Computable.comp 𝒜.enumeration.computable
          (Computable.fst.comp (coverDecode_primrec.to_comp.comp
            (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))))
    exact (Computable.comp h_primrec.to_comp h_comp).of_eq (fun _ => rfl)
  have h_len : Computable
      (fun a : BitString × ℕ × ℕ × ℕ × ℕ =>
        decide ((coverDecode a.2.2.2.2).2.length ≤ a.2.2.2.1 * 2 ^ (a.2.2.1 + 1))) := by
    exact (Primrec.to_comp (PrimrecPred.decide (Primrec.nat_le.comp
      (Primrec.list_length.comp (coverDecode_primrec.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        |> Primrec.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (twoPow_primrec.comp (Primrec.succ.comp (Primrec.fst.comp
          (Primrec.snd.comp Primrec.snd)))))))).of_eq fun _ => rfl
  have h_size : Computable
      (fun a : BitString × ℕ × ℕ × ℕ × ℕ =>
        (coverDecode a.2.2.2.2).2.all
          (fun w => (decodeCoverCodeList w).dedup.length ≤
            1 ⊔ (decodeCoverCodeList a.1).dedup.length / 2 ^ a.2.2.1)) := by
    have h_primrec : Primrec
        (fun (a : BitString × ℕ × ℕ × ℕ × ℕ) => let Acode := a.1; let n := a.2.1; let k := a.2.2.1;
            let q0 := a.2.2.2.1; let p := a.2.2.2.2
            max 1 ((decodeCoverCodeList Acode).dedup.length / 2 ^ k)) := by
      have h_len_dedup : Primrec
          (fun (a : BitString × ℕ × ℕ × ℕ × ℕ) => let Acode := a.1; let n := a.2.1; let k :=
              a.2.2.1; let q0 := a.2.2.2.1; let p := a.2.2.2.2
              (decodeCoverCodeList Acode).dedup.length) := by
        exact (Primrec.comp ( Primrec.list_length )
          ( dedup_primrec.comp
            ( decodeCoverCodeList_primrec.comp ( Primrec.fst ) ) )).of_eq fun _ => rfl
      exact (Primrec.nat_max.comp ( Primrec.const 1 )
        ( Primrec.nat_div.comp ( h_len_dedup ) ( twoPow_primrec.comp
          ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) ) )).of_eq fun _ => rfl
    exact (@coverSearch_list_all_primrec (BitString × ℕ × ℕ × ℕ × ℕ) BitString _ _
      (fun a => (coverDecode a.2.2.2.2).2)
      (fun a w => decide ((decodeCoverCodeList w).dedup.length ≤
        max 1 ((decodeCoverCodeList a.1).dedup.length / 2 ^ a.2.2.1)))
      (Primrec.snd.comp (coverDecode_primrec.comp
        (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp Primrec.snd)))))
      (PrimrecPred.decide <| Primrec.nat_le.comp
        (dedup_primrec.comp (decodeCoverCodeList_primrec.comp Primrec.snd)
          |> Primrec.comp Primrec.list_length)
        (h_primrec.comp Primrec.fst))).to_comp.of_eq fun _ => rfl
  have h_target : Computable
      (fun a : BitString × ℕ × ℕ × ℕ × ℕ =>
        (decodeCoverCodeList a.1).filter (fun y => y.length = a.2.1) |>.all
          (fun y => (coverDecode a.2.2.2.2).2.any (fun w => y ∈ decodeCoverCodeList w))) := by
    have h_any : Primrec₂
        (fun (a : BitString × ℕ × ℕ × ℕ × ℕ) (y : BitString) =>
          (coverDecode a.2.2.2.2).2.any (fun w => y ∈ decodeCoverCodeList w)) := by
      exact (@Kolmogorov.list_any_primrec ((BitString × ℕ × ℕ × ℕ × ℕ) × BitString) BitString _ _
        (fun a => (coverDecode a.1.2.2.2.2).2) (fun a w => decide (a.2 ∈ decodeCoverCodeList w))
        (Primrec.snd.comp (coverDecode_primrec) |> Primrec.comp <|
          Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
          Primrec.snd.comp <| Primrec.fst)
        (bitString_mem_primrec.comp (Primrec.snd.comp Primrec.fst)
          (decodeCoverCodeList_primrec.comp Primrec.snd))).of_eq fun _ => rfl
    have h_filter : Primrec
        (fun (a : BitString × ℕ × ℕ × ℕ × ℕ) => (decodeCoverCodeList a.1).filter (fun y => y.length
                                                                                   = a.2.1)) := by
      exact (@Kolmogorov.list_filter_primrec (BitString × ℕ × ℕ × ℕ × ℕ) BitString _ _
        (fun a => decodeCoverCodeList a.1) (fun a y => decide (y.length = a.2.1))
        (decodeCoverCodeList_primrec.comp Primrec.fst)
        (PrimrecPred.decide (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))).of_eq fun _ => rfl
    have h_primrec : Primrec
        (fun (a : BitString × ℕ × ℕ × ℕ × ℕ) =>
          (List.filter (fun y => decide (List.length y = a.2.1)) (decodeCoverCodeList a.1)).all
            (fun y => (coverDecode a.2.2.2.2).2.any
              (fun w => decide (y ∈ decodeCoverCodeList w)))) := by
      exact (@coverSearch_list_all_primrec (BitString × ℕ × ℕ × ℕ × ℕ) BitString _ _
        (fun a => (List.filter (fun y => decide (List.length y = a.2.1)) (decodeCoverCodeList a.1)))
        (fun a y => (coverDecode a.2.2.2.2).2.any (fun w => decide (y ∈ decodeCoverCodeList w)))
        h_filter h_any).of_eq fun _ => rfl
    exact h_primrec.to_comp;
  exact (andC (andC (andC h_enum h_len) h_size) h_target).of_eq fun _ => by
    unfold coverValidBool; rfl

private lemma coverSelectorSearchInput_computable : Computable
    (fun p : BitString × ℕ =>
      (decodeFirst p.1,
        bitsToNat (decodeFirst (decodeSecond p.1)),
        bitsToNat (decodeFirst (decodeSecond (decodeSecond p.1))),
        bitsToNat (decodeFirst (decodeSecond (decodeSecond (decodeSecond p.1)))),
        p.2)) := by
  exact Computable.pair (decodeFirst_computable.comp Computable.fst)
    (Computable.pair
      (bitsToNat_computable.comp
        (decodeFirst_computable.comp (decodeSecond_computable.comp Computable.fst)))
      (Computable.pair
        (bitsToNat_computable.comp
          (decodeFirst_computable.comp
            (decodeSecond_computable.comp
              (decodeSecond_computable.comp Computable.fst))))
        (Computable.pair
          (bitsToNat_computable.comp
            (decodeFirst_computable.comp
              (decodeSecond_computable.comp
                (decodeSecond_computable.comp
                  (decodeSecond_computable.comp Computable.fst)))))
          Computable.snd)))

/-
**Computability core.** The cover selector is partial recursive.
-/
theorem coverSelectorFun_partrec (𝒜 : DescriptionFamily) :
    Partrec (coverSelectorFun 𝒜) := by
  refine Partrec.bind ?_ ?_;
  · refine Partrec.rfind ?_;
    exact Partrec.to₂ (Partrec.of_eq ((coverValidBool_computable 𝒜).comp
      coverSelectorSearchInput_computable |>.partrec) (by intro p; rfl))
  · refine Computable.option_getD ?_ ?_;
    · refine Computable.list_getElem?.comp ?_ ?_;
      · exact Computable.snd.comp ( coverDecode_primrec.to_comp.comp Computable.snd );
      · exact Computable.comp ( bitsToNat_primrec.to_comp )
          ( decodeSecond_primrec.to_comp.comp ( decodeSecond_primrec.to_comp.comp
                                                ( decodeSecond_primrec.to_comp.comp
                                                    ( decodeSecond_primrec.to_comp.comp
                                                        ( Computable.fst ) ) ) ) );
    · exact Computable.const []

/-
**Membership interface.** On the pair code of `Acode` with the address of the
least valid candidate `p`, the selector produces the `idx`-th code of the found
cover.
-/
theorem coverSelectorFun_getD_mem (𝒜 : DescriptionFamily) (Acode : BitString)
    (n k q0 idx s : ℕ) (p : ℕ)
    (hp : coverValidBool 𝒜 Acode n k q0 p = true)
    (hleast : ∀ m, m < p → coverValidBool 𝒜 Acode n k q0 m = false) :
    (coverDecode p).2.getD idx [] ∈
      coverSelectorFun 𝒜 (pairCode Acode (coverAddress n k q0 idx s)) := by
  unfold coverSelectorFun;
  simp_all +decide [ decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
                     bitsToNat_chunkAddress, coverAddress ];
  exact ⟨p, Nat.mem_rfind.mpr ⟨Part.mem_some_iff.mpr hp.symm,
    fun {m} hm => Part.mem_some_iff.mpr (hleast m hm).symm⟩, rfl⟩

end Kolmogorov
