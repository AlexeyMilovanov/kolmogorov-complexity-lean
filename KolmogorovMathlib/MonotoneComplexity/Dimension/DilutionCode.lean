/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.Dilution
import KolmogorovMathlib.MonotoneComplexity.SharedCoding
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# Coded dilution: two-part descriptions of the dilution of a sequence

This module supplies the *coding* half of SUV Problem 170 (§5.8, p. 175).  Two
ingredients are needed and both are stated here once and for all.

* A **self-delimiting code** `selfCode t = 1^m 0 b₁⋯b_m` (with `b₁⋯b_m` the
  canonical code `natToBitString t` of `t`) together with its parser
  `selfHead`/`selfRest`, and the resulting **uniform coded-map bound**

  `exists_const_plainK_codedMap_le`:
  `C(F t x) ≤ C(x) + 2·l(natToBitString t) + 1 + O(1)`

  for a fixed computable family `F : ℕ → BitString → BitString`, with one
  constant uniform in the parameter `t` *and* the argument `x`.  This is the
  standard "the parameter costs its self-delimiting code" lemma; the decompressor
  is "parse the header, run the optimal machine on the rest, apply `F` to the
  result".

* The **inverse** of `dilExpand`: `dilExtract p q n x` reads off the bits of `x`
  at the free places below `n`, and `dilExtract_dilExpand` says it recovers the
  payload.  Together with `dilExpand` this makes the dilution a coded bijection
  between payloads and diluted prefixes, so the coded-map bound applies in both
  directions -- which is exactly what a *two-sided* complexity estimate for the
  dilution of a random sequence needs.

The parameter is packed as `dilPack n p q = ⟨n, ⟨p, q⟩⟩` (iterated `Nat.pair`),
and `dilDecodeCoded`/`dilExtractCoded` are the two coded families.
-/

namespace Kolmogorov

/-! ## A self-delimiting code for a natural number -/

/-- The self-delimiting code of `t`: `1^m 0 b₁⋯b_m`, where `b₁⋯b_m` is the
canonical code `natToBitString t` and `m` is its length. -/
def selfCode (t : ℕ) : BitString :=
  List.replicate (natToBitString t).length true ++ false :: natToBitString t

/-- The length of the unary header of a bit string: its number of leading `1`s. -/
def selfLen (z : BitString) : ℕ := (z.takeWhile id).length

/-- The number coded by the self-delimiting header of `z`. -/
def selfHead (z : BitString) : ℕ :=
  bitStringToNat ((z.drop (selfLen z + 1)).take (selfLen z))

/-- The part of `z` that follows its self-delimiting header. -/
def selfRest (z : BitString) : BitString := (z.drop (selfLen z + 1)).drop (selfLen z)

/-- The self-delimiting code of `t` has length `2 |bits t| + 1`. -/
lemma selfCode_length (t : ℕ) :
    (selfCode t).length = 2 * (natToBitString t).length + 1 := by
  simp only [selfCode, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- The leading block of `true`s of `List.replicate m true ++ false :: y` is
`List.replicate m true`. -/
lemma takeWhile_id_replicate (m : ℕ) (y : BitString) :
    (List.replicate m true ++ false :: y).takeWhile id = List.replicate m true := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hcons : (List.replicate (m + 1) true ++ false :: y)
          = true :: (List.replicate m true ++ false :: y) := by
        simp [List.replicate_succ]
      rw [hcons, List.takeWhile_cons]
      simp [ih, List.replicate_succ]

private lemma selfCode_append_split (t : ℕ) (y : BitString) :
    selfCode t ++ y
      = (List.replicate (natToBitString t).length true ++ [false])
        ++ (natToBitString t ++ y) := by
  simp [selfCode]

/-- The unary header of a self-delimiting code records the width of the payload. -/
@[simp] lemma selfLen_selfCode_append (t : ℕ) (y : BitString) :
    selfLen (selfCode t ++ y) = (natToBitString t).length := by
  have h : selfCode t ++ y
      = List.replicate (natToBitString t).length true ++ false :: (natToBitString t ++ y) := by
    simp [selfCode]
  rw [selfLen, h, takeWhile_id_replicate]
  simp

private lemma drop_selfCode_append (t : ℕ) (y : BitString) :
    (selfCode t ++ y).drop ((natToBitString t).length + 1) = natToBitString t ++ y := by
  rw [selfCode_append_split]
  exact List.drop_left' (by simp)

/-- Decoding the header of a self-delimiting code returns the number it codes. -/
@[simp] lemma selfHead_selfCode_append (t : ℕ) (y : BitString) :
    selfHead (selfCode t ++ y) = t := by
  rw [selfHead, selfLen_selfCode_append, drop_selfCode_append]
  rw [List.take_left' rfl, bitStringToNat_natToBitString]

/-- Dropping the self-delimiting header returns the appended tail. -/
@[simp] lemma selfRest_selfCode_append (t : ℕ) (y : BitString) :
    selfRest (selfCode t ++ y) = y := by
  rw [selfRest, selfLen_selfCode_append, drop_selfCode_append]
  exact List.drop_left' rfl

/-- The header length is primitive recursive. -/
lemma primrec_selfLen : Primrec selfLen :=
  Primrec.list_length.comp (Primrec.list_takeWhile (p := fun b : Bool => b) Primrec.id)

private lemma primrec_selfDrop : Primrec (fun z : BitString => z.drop (selfLen z + 1)) :=
  Primrec.list_drop.comp (Primrec.succ.comp primrec_selfLen) Primrec.id

/-- The number coded by the header is primitive recursive. -/
lemma primrec_selfHead : Primrec selfHead :=
  primrec_bitStringToNat.comp (Primrec.list_take.comp primrec_selfLen primrec_selfDrop)

/-- The tail after the header is primitive recursive. -/
lemma primrec_selfRest : Primrec selfRest :=
  Primrec.list_drop.comp primrec_selfLen primrec_selfDrop

/-! ## The uniform coded-map bound -/

/-- **The parameter costs only its self-delimiting code.**  For a computable
family `F : ℕ → BitString → BitString` there is a *single* constant `c` with

`C(F t x) ≤ C(x) + 2·l(natToBitString t) + 1 + c` for all `t` and all `x`.

The decompressor is "parse the self-delimiting header of the program, run the
optimal machine on the rest, and apply `F` with the parsed parameter". -/
theorem exists_const_plainK_codedMap_le (V : Map) (hV : isOptimalConditional V)
    {F : ℕ → BitString → BitString} (hF : Computable₂ F) :
    ∃ c : ℕ, ∀ (t : ℕ) (x : BitString),
      plainK V (F t x)
        ≤ plainK V x + ((2 * (natToBitString t).length + 1 + c : ℕ) : ENat) := by
  classical
  set D : Map := fun z => (V (selfRest z.1, [])).map (fun u => F (selfHead z.1) u) with hDdef
  have hDp : isDecompressor D := by
    have h1 : Partrec (fun z : BitString × BitString => V (selfRest z.1, [])) :=
      hV.1.comp (Computable.pair (primrec_selfRest.to_comp.comp Computable.fst)
        (Computable.const []))
    have h2 : Computable₂ (fun (z : BitString × BitString) (u : BitString) =>
        F (selfHead z.1) u) :=
      hF.comp (primrec_selfHead.to_comp.comp (Computable.fst.comp Computable.fst))
        Computable.snd
    exact Partrec.map h1 h2
  obtain ⟨c, hc⟩ := hV.2 D hDp
  refine ⟨c, fun t x => ?_⟩
  have hfin : plainK V x ≠ ⊤ := by
    obtain ⟨c₀, hc₀⟩ := plainK_le_length V hV
    refine ne_top_of_le_ne_top ?_ (hc₀ x)
    exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top _⟩
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hfin
  have hxle : condK V x [] ≤ (N : ENat) := hN.ge
  obtain ⟨p, hplen, hprod⟩ := (condK_le_iff V x [] N).1 hxle
  have hprod' : produces D (selfCode t ++ p) [] (F t x) := by
    change F t x ∈ D (selfCode t ++ p, [])
    simp only [hDdef, selfRest_selfCode_append, selfHead_selfCode_append]
    exact Part.mem_map _ hprod
  have hDle : condK D (F t x) []
      ≤ ((2 * (natToBitString t).length + 1 + N : ℕ) : ENat) := by
    refine (condK_le_iff D (F t x) [] _).2 ⟨selfCode t ++ p, ?_, hprod'⟩
    have hlen : (selfCode t ++ p).length
        = 2 * (natToBitString t).length + 1 + p.length := by
      rw [List.length_append, selfCode_length]
    have hpl : p.length ≤ N := hplen
    change (selfCode t ++ p).length ≤ 2 * (natToBitString t).length + 1 + N
    omega
  calc plainK V (F t x) = condK V (F t x) [] := rfl
    _ ≤ condK D (F t x) [] + (c : ENat) := hc _ _
    _ ≤ ((2 * (natToBitString t).length + 1 + N : ℕ) : ENat) + (c : ENat) := by gcongr
    _ = plainK V x + ((2 * (natToBitString t).length + 1 + c : ℕ) : ENat) := by
        rw [← hN]; push_cast; ring

/-! ## The inverse of `dilExpand` -/

/-- The payload carried by a string of length `n`: its bits at the free places. -/
def dilExtract (p q n : ℕ) (x : BitString) : BitString :=
  (List.range n).flatMap (fun i => if dilSel p q i then [x.getD i false] else [])

/-- Each position of a diluted string carries the next payload bit at a selected position and
zero elsewhere. -/
lemma getD_dilExpand {p q n i : ℕ} (hi : i < n) (y : BitString) :
    (dilExpand p q n y).getD i false
      = if dilSel p q i then y.getD (dilCount p q i) false else false := by
  have hlen : i < (dilExpand p q n y).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ hlen]
  simp [dilExpand]

/-- Reading the payload positions off `range n` is the same as reading the
payload indices off `range (dilCount p q n)`. -/
lemma flatMap_dilSel_eq (p q : ℕ) (hq : 0 < q) (hpq : p ≤ q) (y : BitString) :
    ∀ n : ℕ,
      (List.range n).flatMap
          (fun i => if dilSel p q i then [y.getD (dilCount p q i) false] else [])
        = (List.range (dilCount p q n)).map (fun j => y.getD j false) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      by_cases hsel : dilSel p q n = true
      · have hstep : dilCount p q (n + 1) = dilCount p q n + 1 := of_decide_eq_true hsel
        rw [hstep, List.range_succ, List.map_append]
        simp [hsel]
      · simp only [Bool.not_eq_true] at hsel
        have hdec : decide (dilCount p q (n + 1) = dilCount p q n + 1) = false := hsel
        have hne : dilCount p q (n + 1) ≠ dilCount p q n + 1 := of_decide_eq_false hdec
        have hstep : dilCount p q (n + 1) = dilCount p q n :=
          (dilCount_succ_cases p q n hq hpq).resolve_right hne
        rw [hstep]
        simp [hsel]

/-- Reading a string off at all its positions returns the string. -/
lemma map_getD_range_length (y : BitString) :
    (List.range y.length).map (fun j => y.getD j false) = y := by
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  have hi : i < y.length := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem _ _ hi

/-- `dilExtract` inverts `dilExpand` on payloads of the right length. -/
theorem dilExtract_dilExpand (p q : ℕ) (hq : 0 < q) (hpq : p ≤ q) (n : ℕ) (y : BitString)
    (hy : y.length = dilCount p q n) : dilExtract p q n (dilExpand p q n y) = y := by
  have hstep : dilExtract p q n (dilExpand p q n y)
      = (List.range n).flatMap
          (fun i => if dilSel p q i then [y.getD (dilCount p q i) false] else []) := by
    rw [dilExtract]
    refine List.flatMap_congr (fun i hi => ?_)
    have hin : i < n := by simpa using hi
    by_cases hsel : dilSel p q i = true
    · rw [if_pos hsel, if_pos hsel, getD_dilExpand hin y, if_pos hsel]
    · simp only [Bool.not_eq_true] at hsel
      rw [if_neg (by simp [hsel]), if_neg (by simp [hsel])]
  rw [hstep, flatMap_dilSel_eq p q hq hpq y n, ← hy, map_getD_range_length]

/-! ## The two coded families -/

/-- The parameter `(n, p, q)` packed into one natural number. -/
def dilPack (n p q : ℕ) : ℕ := Nat.pair n (Nat.pair p q)

/-- The length component of a packed parameter. -/
def dilN (t : ℕ) : ℕ := t.unpair.1

/-- The numerator component of a packed parameter. -/
def dilP (t : ℕ) : ℕ := t.unpair.2.unpair.1

/-- The denominator component of a packed parameter. -/
def dilQ (t : ℕ) : ℕ := t.unpair.2.unpair.2

/-- The length component read back from a packed parameter. -/
@[simp] lemma dilN_dilPack (n p q : ℕ) : dilN (dilPack n p q) = n := by
  simp [dilN, dilPack]

/-- The numerator component read back from a packed parameter. -/
@[simp] lemma dilP_dilPack (n p q : ℕ) : dilP (dilPack n p q) = p := by
  simp [dilP, dilPack]

/-- The denominator component read back from a packed parameter. -/
@[simp] lemma dilQ_dilPack (n p q : ℕ) : dilQ (dilPack n p q) = q := by
  simp [dilQ, dilPack]

/-- The length component of a packed parameter is primitive recursive. -/
lemma primrec_dilN : Primrec dilN := Primrec.fst.comp Primrec.unpair

/-- The numerator component of a packed parameter is primitive recursive. -/
lemma primrec_dilP : Primrec dilP :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

/-- The denominator component of a packed parameter is primitive recursive. -/
lemma primrec_dilQ : Primrec dilQ :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

/-- The coded expansion family: `t = ⟨n, ⟨p, q⟩⟩` expands a payload to length `n`. -/
def dilDecodeCoded (t : ℕ) (y : BitString) : BitString := dilExpand (dilP t) (dilQ t) (dilN t) y

/-- The coded extraction family, inverse to `dilDecodeCoded`. -/
def dilExtractCoded (t : ℕ) (x : BitString) : BitString := dilExtract (dilP t) (dilQ t) (dilN t) x

/-- The coded expansion at a packed parameter is the expansion with those parameters. -/
@[simp] lemma dilDecodeCoded_dilPack (n p q : ℕ) (y : BitString) :
    dilDecodeCoded (dilPack n p q) y = dilExpand p q n y := by
  simp [dilDecodeCoded]

/-- The coded extraction at a packed parameter is the extraction with those parameters. -/
@[simp] lemma dilExtractCoded_dilPack (n p q : ℕ) (x : BitString) :
    dilExtractCoded (dilPack n p q) x = dilExtract p q n x := by
  simp [dilExtractCoded]

/-- `⌈p·n/q⌉` is primitive recursive in all three arguments. -/
lemma primrec_dilCount₃ : Primrec (fun t : (ℕ × ℕ) × ℕ => dilCount t.1.1 t.1.2 t.2) :=
  Primrec.nat_div.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)))
    (Primrec.snd.comp Primrec.fst)

/-- The free-place marker is primitive recursive in all three arguments. -/
lemma primrec_dilSel₃ : Primrec (fun t : (ℕ × ℕ) × ℕ => dilSel t.1.1 t.1.2 t.2) := by
  have h1 : Primrec (fun t : (ℕ × ℕ) × ℕ => dilCount t.1.1 t.1.2 (t.2 + 1)) :=
    primrec_dilCount₃.comp (Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd))
  have h2 : Primrec (fun t : (ℕ × ℕ) × ℕ => dilCount t.1.1 t.1.2 t.2 + 1) :=
    Primrec.succ.comp primrec_dilCount₃
  exact (PrimrecRel.comp Primrec.eq h1 h2).decide

private lemma primrec_argPQ : Primrec (fun r : (ℕ × BitString) × ℕ =>
    ((dilP r.1.1, dilQ r.1.1), r.2)) :=
  Primrec.pair (Primrec.pair (primrec_dilP.comp (Primrec.fst.comp Primrec.fst))
    (primrec_dilQ.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd

private lemma primrec_selPQ : Primrec (fun r : (ℕ × BitString) × ℕ =>
    dilSel (dilP r.1.1) (dilQ r.1.1) r.2) :=
  (primrec_dilSel₃.comp primrec_argPQ).of_eq (fun _ => rfl)

private lemma primrec_cntPQ : Primrec (fun r : (ℕ × BitString) × ℕ =>
    dilCount (dilP r.1.1) (dilQ r.1.1) r.2) :=
  (primrec_dilCount₃.comp primrec_argPQ).of_eq (fun _ => rfl)

private lemma primrec_rangeN : Primrec (fun a : ℕ × BitString => List.range (dilN a.1)) :=
  Primrec.list_range.comp (primrec_dilN.comp Primrec.fst)

/-- The coded expansion is primitive recursive. -/
lemma primrec_dilDecodeCoded : Primrec (fun a : ℕ × BitString => dilDecodeCoded a.1 a.2) := by
  have hget : Primrec (fun r : (ℕ × BitString) × ℕ =>
      r.1.2.getD (dilCount (dilP r.1.1) (dilQ r.1.1) r.2) false) :=
    (Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst) primrec_cntPQ
  have hbody : Primrec₂ (fun (a : ℕ × BitString) (i : ℕ) =>
      if dilSel (dilP a.1) (dilQ a.1) i then
        a.2.getD (dilCount (dilP a.1) (dilQ a.1) i) false else false) := by
    refine (Primrec.cond primrec_selPQ hget (Primrec.const false)).of_eq (fun r => ?_)
    by_cases h : dilSel (dilP r.1.1) (dilQ r.1.1) r.2 = true <;> simp [h]
  exact (Primrec.list_map primrec_rangeN hbody).of_eq (fun a => rfl)

/-- The coded extraction is primitive recursive. -/
lemma primrec_dilExtractCoded : Primrec (fun a : ℕ × BitString => dilExtractCoded a.1 a.2) := by
  have hget : Primrec (fun r : (ℕ × BitString) × ℕ => [r.1.2.getD r.2 false]) :=
    Primrec.list_cons.comp ((Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst)
      Primrec.snd) (Primrec.const [])
  have hbody : Primrec₂ (fun (a : ℕ × BitString) (i : ℕ) =>
      if dilSel (dilP a.1) (dilQ a.1) i then [a.2.getD i false] else ([] : BitString)) := by
    refine (Primrec.cond primrec_selPQ hget (Primrec.const [])).of_eq (fun r => ?_)
    by_cases h : dilSel (dilP r.1.1) (dilQ r.1.1) r.2 = true <;> simp [h]
  exact (Primrec.list_flatMap primrec_rangeN hbody).of_eq (fun a => rfl)

/-- The coded expansion is computable in the parameter and the payload. -/
lemma computable₂_dilDecodeCoded : Computable₂ dilDecodeCoded :=
  primrec_dilDecodeCoded.to_comp.to₂

/-- The coded extraction is computable in the parameter and the string. -/
lemma computable₂_dilExtractCoded : Computable₂ dilExtractCoded :=
  primrec_dilExtractCoded.to_comp.to₂

end Kolmogorov
