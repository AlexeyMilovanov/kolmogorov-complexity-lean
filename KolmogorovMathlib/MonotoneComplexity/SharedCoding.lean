/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.MonotoneComplexity.PlainPrefixDips
import KolmogorovMathlib.Prefix.Properties

/-!
# The canonical coding API shared by the Chapter 5 clusters C10-C12

Shen-Uspensky-Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness*
identifies natural numbers, pairs, rationals and finite sets with binary strings
without comment ("the index set is immaterial up to a computable bijection").
Four different ad hoc identifications were in use (`Nat.bits`,
`Encodable.encode`, `Nat.pair`, raw `Finset` encodings).  `Nat.bits` is not onto
`BitString`, so the `ℕ`-indexed semimeasure hierarchy cannot be transported
along it; the encodings are unified here, with computable-invariance lemmas.

This module is the single home of that identification:

* `natBitStringEquiv : ℕ ≃ BitString` is a *bijection* with both directions
  primitive recursive.  `natToBitString n` is the binary expansion of `n + 1`
  with its leading `1` removed, so every string is hit exactly once.
* `KPNat U n = KPPlain U (natToBitString n)` is the prefix complexity of a
  natural number (SUV p. 165, `K(i) = -log m(i)`); it is used by C11 and by the
  `Nat.bits`-based statements of C10.
* `finsetCode`, `natPairCode`, `ratBitCode` are the canonical codings of finite
  sets of naturals (SUV p. 149), of pairs (SUV p. 167) and of rationals
  (SUV p. 171); each is the canonical bijection applied to the canonical
  `ℕ`-valued encoding of the object.
* `tsum_comp_natToBitString` is the transport used to move an `ℕ`-indexed
  semimeasure to a `BitString`-indexed one and back.

## Coding invariance

`exists_const_KPPlain_code_invariant` is the general statement "two computable
injective codings of `ℕ` give the same prefix complexity up to `O(1)`".  It is an
honest leaf: the repository's transform lemma `KPPlain_map_le` needs a *total*
computable map `BitString → BitString`, while inverting an arbitrary computable
injection is only partial computable.  Everything actually used is proved from
the *decodable* case `exists_const_KPPlain_comp_le`, which does follow from
`KPPlain_map_le`; in particular the change of coding performed by this module
(`Nat.bits n` to `natToBitString n`) costs only `O(1)`, which is
`exists_const_KPNat_natBits_equiv`.

Uses of `natCode` and `Nat.bits` outside the Chapter 5 skeleton are deliberately
left untouched.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The canonical computable bijection `ℕ ≃ BitString` -/

/-- Every nonzero natural number has a binary expansion whose leading (last) bit
is `1`; `Nat.bits` is little-endian, so the expansion ends with `true`. -/
theorem exists_natBits_eq_append_true :
    ∀ m : ℕ, m ≠ 0 → ∃ u : BitString, Nat.bits m = u ++ [true] := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.even_or_odd m with he | ho
    · obtain ⟨k, hk⟩ := he
      have hk0 : k ≠ 0 := by omega
      have hm2 : m = 2 * k := by omega
      obtain ⟨u, hu⟩ := ih k (by omega) hk0
      exact ⟨false :: u, by rw [hm2, Nat.bit0_bits k hk0, hu, List.cons_append]⟩
    · obtain ⟨k, hk⟩ := ho
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · exact ⟨[], by rw [hk]; simp⟩
      · obtain ⟨u, hu⟩ := ih k (by omega) (by omega)
        exact ⟨true :: u, by rw [hk, Nat.bit1_bits k, hu, List.cons_append]⟩

/-- Restoring the leading bit of a nonzero natural number's binary expansion. -/
theorem dropLast_natBits_append_true {m : ℕ} (hm : m ≠ 0) :
    (Nat.bits m).dropLast ++ [true] = Nat.bits m := by
  obtain ⟨u, hu⟩ := exists_natBits_eq_append_true m hm
  rw [hu, List.dropLast_concat]

/-- **The canonical code of a natural number.** `natToBitString n` is the binary
expansion of `n + 1` with its leading `1` removed.  Unlike `Nat.bits`, this is a
bijection onto `BitString` (SUV treats `ℕ` and `Ξ` as identified). -/
def natToBitString (n : ℕ) : BitString := (Nat.bits (n + 1)).dropLast

/-- The inverse of `natToBitString`: restore the leading `1` and subtract one. -/
def bitStringToNat (x : BitString) : ℕ := decodeBits (x ++ [true]) - 1

/-- Decoding the string of a number returns the number. -/
@[simp] theorem bitStringToNat_natToBitString (n : ℕ) :
    bitStringToNat (natToBitString n) = n := by
  have h : (Nat.bits (n + 1)).dropLast ++ [true] = Nat.bits (n + 1) :=
    dropLast_natBits_append_true (Nat.succ_ne_zero n)
  simp [bitStringToNat, natToBitString, h]

/-- Encoding the number of a string returns the string. -/
@[simp] theorem natToBitString_bitStringToNat (x : BitString) :
    natToBitString (bitStringToNat x) = x := by
  have hb : Nat.bits (decodeBits (x ++ [true])) = x ++ [true] :=
    natBits_decodeBits_append_true x
  have hne : decodeBits (x ++ [true]) ≠ 0 := by
    intro h
    rw [h] at hb
    simp [Nat.zero_bits] at hb
  have hsucc : decodeBits (x ++ [true]) - 1 + 1 = decodeBits (x ++ [true]) :=
    Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hne)
  simp [natToBitString, bitStringToNat, hsucc, hb]

/-- **The canonical computable bijection `ℕ ≃ BitString`**: the identification of
the index sets `ℕ` and `Ξ` used silently throughout SUV Sections 5.6-5.9.  Both directions are
primitive recursive. -/
def natBitStringEquiv : ℕ ≃ BitString where
  toFun := natToBitString
  invFun := bitStringToNat
  left_inv := bitStringToNat_natToBitString
  right_inv := natToBitString_bitStringToNat

/-- The equivalence between naturals and strings acts by the encoding. -/
@[simp] theorem natBitStringEquiv_apply (n : ℕ) : natBitStringEquiv n = natToBitString n := rfl

/-- The inverse equivalence acts by the decoding. -/
@[simp] theorem natBitStringEquiv_symm_apply (x : BitString) :
    natBitStringEquiv.symm x = bitStringToNat x := rfl

/-- Distinct numbers get distinct strings. -/
theorem natToBitString_injective : Function.Injective natToBitString :=
  natBitStringEquiv.injective

/-- Every string is the code of a number. -/
theorem natToBitString_surjective : Function.Surjective natToBitString :=
  natBitStringEquiv.surjective

/-- Distinct strings decode to distinct numbers. -/
theorem bitStringToNat_injective : Function.Injective bitStringToNat :=
  natBitStringEquiv.symm.injective

/-- `natToBitString` is primitive recursive. -/
theorem primrec_natToBitString : Primrec natToBitString := by
  have H : natToBitString = fun n : ℕ => (Nat.bits (n + 1)).reverse.tail.reverse := by
    funext n
    simp [natToBitString, List.dropLast_eq_take]
  rw [H]
  exact Primrec.list_reverse.comp
    (Primrec.list_tail.comp (Primrec.list_reverse.comp (primrec_natBits.comp Primrec.succ)))

/-- `bitStringToNat` is primitive recursive. -/
theorem primrec_bitStringToNat : Primrec bitStringToNat := by
  have happ : Primrec (fun x : BitString => x ++ [true]) :=
    Primrec.list_append.comp Primrec.id (Primrec.const [true])
  exact Primrec.nat_sub.comp (primrec_decodeBits.comp happ) (Primrec.const 1)

/-- The encoding of a number as a string is computable. -/
theorem computable_natToBitString : Computable natToBitString := primrec_natToBitString.to_comp

/-- The decoding of a string as a number is computable. -/
theorem computable_bitStringToNat : Computable bitStringToNat := primrec_bitStringToNat.to_comp

/-- **Transport of `ℕ`-indexed sums to `BitString`-indexed sums**: the sum of a nonnegative function
over `BitString` is the sum of its pullback
over `ℕ`.  This is what a transported semimeasure needs: total mass, and hence
the semimeasure inequality, is preserved. -/
theorem tsum_comp_natToBitString (f : BitString → ℝ≥0∞) :
    ∑' n : ℕ, f (natToBitString n) = ∑' x : BitString, f x :=
  natBitStringEquiv.tsum_eq f

/-- The `BitString`-indexed form of `tsum_comp_natToBitString`. -/
theorem tsum_comp_bitStringToNat (g : ℕ → ℝ≥0∞) :
    ∑' x : BitString, g (bitStringToNat x) = ∑' n : ℕ, g n :=
  natBitStringEquiv.symm.tsum_eq g

/-! ### Prefix complexity of a natural number -/

/-- **Prefix complexity of a natural number**, `K(n)` in the book's notation
(SUV p. 165: "prefix complexity `K(i) = -log m(i)`").  The natural number is
coded by the canonical bijection `natToBitString`. -/
noncomputable def KPNat (U : Map) (n : ℕ) : ENat := KPPlain U (natToBitString n)

/-- The prefix complexity of a number is that of its string code. -/
theorem KPNat_def (U : Map) (n : ℕ) : KPNat U n = KPPlain U (natToBitString n) := rfl

/-! ### Coding invariance -/

/-- **Coding invariance, decodable case.**  If the coding `e₂` has a total
computable left inverse `d`, then re-coding by any computable `e₁` costs `O(1)`.
This is the repository's transform lemma `KPPlain_map_le` applied to `e₁ ∘ d`. -/
theorem exists_const_KPPlain_comp_le (U : Map) (hU : IsOptimalPrefixConditional U)
    {e₁ e₂ : ℕ → BitString} {d : BitString → ℕ} (he₁ : Computable e₁) (hd : Computable d)
    (hde : ∀ n, d (e₂ n) = n) :
    ∃ c : ℕ, ∀ n, KPPlain U (e₁ n) ≤ KPPlain U (e₂ n) + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU (fun x => e₁ (d x)) (he₁.comp hd)
  refine ⟨c, fun n => ?_⟩
  simpa [hde n] using hc (e₂ n)

/-- **Coding invariance.**  Any two computable injective codings of
the natural numbers by binary strings give prefix complexities that differ by an
additive `O(1)`. -/
theorem exists_const_KPPlain_code_invariant (U : Map) (hU : IsOptimalPrefixConditional U)
    {e₁ e₂ : ℕ → BitString} (he₁ : Computable e₁) (he₂ : Computable e₂)
    (_hi₁ : Function.Injective e₁) (hi₂ : Function.Injective e₂) :
    ∃ c : ℕ, ∀ n, KPPlain U (e₁ n) ≤ KPPlain U (e₂ n) + (c : ENat) := by
  classical
  -- the partial decoding `x ↦ e₁ (e₂⁻¹ x)`
  have hf : Partrec (fun x : BitString =>
      (Nat.rfind fun n => Part.some (decide (e₂ n = x))).map e₁) := by
    have hpred : Computable₂ (fun (x : BitString) (n : ℕ) => decide (e₂ n = x)) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp (he₂.comp Computable.snd) Computable.fst
    have hrf : Partrec (fun x : BitString =>
        Nat.rfind fun n => Part.some (decide (e₂ n = x))) := Partrec.rfind hpred
    exact hrf.map (he₁.comp Computable.snd).to₂
  obtain ⟨c, hc⟩ := KPPlain_partrec_map_le U hU _ hf
  refine ⟨c, fun n => ?_⟩
  -- injectivity of `e₂` makes the search return exactly `n` on the input `e₂ n`
  have hn : n ∈ Nat.rfind fun k => Part.some (decide (e₂ k = e₂ n)) := by
    apply Nat.mem_rfind.2
    refine ⟨by simp, ?_⟩
    intro m hm
    have hne : e₂ m ≠ e₂ n := fun h => absurd (hi₂ h) (Nat.ne_of_lt hm)
    simp [hne]
  exact hc (e₂ n) (e₁ n) (Part.mem_map e₁ hn)

/-- Any computable coding of `ℕ` is at least as good as the canonical one, up to
`O(1)`: the canonical coding is computably decodable. -/
theorem exists_const_KPPlain_le_KPNat (U : Map) (hU : IsOptimalPrefixConditional U)
    {e : ℕ → BitString} (he : Computable e) :
    ∃ c : ℕ, ∀ n, KPPlain U (e n) ≤ KPNat U n + (c : ENat) :=
  exists_const_KPPlain_comp_le U hU he computable_bitStringToNat bitStringToNat_natToBitString

/-- Conversely, the canonical coding is at least as good as any computably
*decodable* coding. -/
theorem exists_const_KPNat_le_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U)
    {e : ℕ → BitString} {d : BitString → ℕ} (hd : Computable d) (hde : ∀ n, d (e n) = n) :
    ∃ c : ℕ, ∀ n, KPNat U n ≤ KPPlain U (e n) + (c : ENat) :=
  exists_const_KPPlain_comp_le U hU computable_natToBitString hd hde

/-- **The re-coding performed by this module costs `O(1)`.**  The skeleton used
`KPPlain U (Nat.bits n)`; the canonical `KPNat U n` differs from it by at most an
additive constant, in both directions.  Hence no Chapter 5 statement changes its
mathematical content when `Nat.bits` is replaced by `natToBitString`. -/
theorem exists_const_KPNat_natBits_equiv (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, (∀ n, KPNat U n ≤ KPPlain U (Nat.bits n) + (c : ENat)) ∧
      (∀ n, KPPlain U (Nat.bits n) ≤ KPNat U n + (c : ENat)) := by
  obtain ⟨c₁, h₁⟩ :=
    exists_const_KPNat_le_KPPlain U hU (e := Nat.bits) decodeBits_computable decodeBits_natBits
  obtain ⟨c₂, h₂⟩ := exists_const_KPPlain_le_KPNat U hU (e := Nat.bits) natBits_computable
  have hc₁ : ((c₁ : ℕ) : ENat) ≤ ((max c₁ c₂ : ℕ) : ENat) := by
    exact_mod_cast le_max_left c₁ c₂
  have hc₂ : ((c₂ : ℕ) : ENat) ≤ ((max c₁ c₂ : ℕ) : ENat) := by
    exact_mod_cast le_max_right c₁ c₂
  exact ⟨max c₁ c₂, fun n => (h₁ n).trans (add_le_add (le_refl _) hc₁),
    fun n => (h₂ n).trans (add_le_add (le_refl _) hc₂)⟩

/-! ### Canonical codings of the objects used by C10-C12 -/

/-- **SUV p. 149.** The canonical binary code of a finite set of indices, used as
the first component of the pair `(F, w(F))`.  It is the canonical bijection
applied to the canonical `Encodable` code of the finite set. -/
def finsetCode (F : Finset ℕ) : BitString := natToBitString (Encodable.encode F)

/-- Distinct finite sets of strings get distinct codes. -/
theorem finsetCode_injective : Function.Injective finsetCode :=
  fun _ _ h => Encodable.encode_injective (natToBitString_injective h)

/-- **SUV p. 167.** The canonical binary code of a pair of natural numbers: the
canonical bijection applied to Cantor's pairing function `Nat.pair`. -/
def natPairCode (i j : ℕ) : BitString := natToBitString (Nat.pair i j)

/-- The self-delimiting code of a pair of naturals is primitive recursive in both arguments. -/
theorem primrec_natPairCode : Primrec₂ natPairCode :=
  primrec_natToBitString.comp Primrec₂.natPair

/-- The self-delimiting code of a pair of naturals is computable in both arguments. -/
theorem computable_natPairCode : Computable₂ natPairCode := primrec_natPairCode.to_comp

/-- Distinct pairs of naturals receive distinct codes. -/
theorem natPairCode_injective : Function.Injective (fun p : ℕ × ℕ => natPairCode p.1 p.2) := by
  intro p q h
  have h' : Nat.pair p.1 p.2 = Nat.pair q.1 q.2 := natToBitString_injective h
  have := congrArg Nat.unpair h'
  simpa [Nat.unpair_pair, Prod.ext_iff] using this

/-- **SUV p. 171.** The canonical binary code of a rational number: the canonical
bijection applied to the repository's canonical `ℕ`-code of a rational,
`ratCode q = ⟨num, den⟩`.  (Mathlib carries two different `Encodable ℚ`
structures — the plain one and the `Denumerable`-derived one underlying
`Primcodable ℚ` — whose codes differ; `ratCode` is the repository's computable
choice, see `AlgorithmicRandomness/RatComputable.lean`.) -/
def ratBitCode (q : ℚ) : BitString := natToBitString (ratCode q)

/-- The bit encoding of a rational number is computable. -/
theorem computable_ratBitCode : Computable ratBitCode :=
  computable_natToBitString.comp computable_ratCode

/-- Distinct rationals receive distinct bit encodings. -/
theorem ratBitCode_injective : Function.Injective ratBitCode := by
  intro q r h
  have h' : ratCode q = ratCode r := natToBitString_injective h
  have h2 := congrArg Nat.unpair h'
  simp only [ratCode, Nat.unpair_pair, Prod.mk.injEq] at h2
  exact Rat.ext (Encodable.encode_injective h2.1) h2.2

/-! ### Coding invariance for the three derived codings -/

/-- Coding invariance for finite sets of naturals: replacing `finsetCode` by any
computable injective coding of the `Encodable` codes changes prefix complexity by
at most an additive constant. -/
theorem exists_const_KPPlain_finsetCode_invariant (U : Map) (hU : IsOptimalPrefixConditional U)
    {e : ℕ → BitString} (he : Computable e) (hi : Function.Injective e) :
    ∃ c : ℕ, ∀ F : Finset ℕ,
      KPPlain U (finsetCode F) ≤ KPPlain U (e (Encodable.encode F)) + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    exists_const_KPPlain_code_invariant U hU computable_natToBitString he
      natToBitString_injective hi
  exact ⟨c, fun F => hc (Encodable.encode F)⟩

/-- Coding invariance for pairs of naturals. -/
theorem exists_const_KPPlain_natPairCode_invariant (U : Map) (hU : IsOptimalPrefixConditional U)
    {e : ℕ → BitString} (he : Computable e) (hi : Function.Injective e) :
    ∃ c : ℕ, ∀ i j : ℕ,
      KPPlain U (natPairCode i j) ≤ KPPlain U (e (Nat.pair i j)) + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    exists_const_KPPlain_code_invariant U hU computable_natToBitString he
      natToBitString_injective hi
  exact ⟨c, fun i j => hc (Nat.pair i j)⟩

/-- Coding invariance for rationals. -/
theorem exists_const_KPPlain_ratBitCode_invariant (U : Map) (hU : IsOptimalPrefixConditional U)
    {e : ℕ → BitString} (he : Computable e) (hi : Function.Injective e) :
    ∃ c : ℕ, ∀ q : ℚ,
      KPPlain U (ratBitCode q) ≤ KPPlain U (e (ratCode q)) + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    exists_const_KPPlain_code_invariant U hU computable_natToBitString he
      natToBitString_injective hi
  exact ⟨c, fun q => hc (ratCode q)⟩

end Kolmogorov
