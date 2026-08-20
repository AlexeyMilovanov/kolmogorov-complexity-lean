import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Decoder
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Support
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Uniform

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/- Keep the nested encodings opaque while composing the reconstruction decoder
with the computable program rearrangements below. -/
attribute [local irreducible] Primcodable.prod Primcodable.list

/-! ### A coefficient-one framing of the reconstruction program

`lemma4Decoder` parses its program as the balanced pair
`pairCode (pairCode pD pQ) (pairCode (Nat.bits m) (Nat.bits r))`.  Since
`pairCode x y = natCode x.length ++ x ++ y` doubles its *first* component, that
layout charges four copies of the set-description program `pD`.  A right-nested
layout instead charges a single copy of its *last* component, so composing the
decoder with the computable rearrangement `lemma4Rearrange` below lets the
program be presented flat, as
`pairCode pQ (pairCode (Nat.bits m) (pairCode (Nat.bits r) pD))`, of length
`|pD| + 2|pQ| + 2|bits m| + 2|bits r| + 3`.  This yields coefficient one on
`plainSetComplexity`, which is the coefficient that matters downstream (the two
logarithmic terms are absorbed by the public `logSlack`). -/
def lemma4Rearrange (z : BitString) : BitString :=
  pairCode
    (pairCode (decodeSecond (decodeSecond (decodeSecond z))) (decodeFirst z))
    (pairCode (decodeFirst (decodeSecond z))
      (decodeFirst (decodeSecond (decodeSecond z))))

theorem lemma4Rearrange_primrec : Primrec lemma4Rearrange := by
  have hs2 : Primrec (fun z : BitString => decodeSecond (decodeSecond z)) :=
    decodeSecond_primrec.comp decodeSecond_primrec
  have hs3 : Primrec (fun z : BitString =>
      decodeSecond (decodeSecond (decodeSecond z))) :=
    decodeSecond_primrec.comp hs2
  exact pairCode_primrec.comp
    (pairCode_primrec.comp hs3 decodeFirst_primrec)
    (pairCode_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)
      (decodeFirst_primrec.comp hs2))

/-- The rearrangement turns the flat program layout into the nested layout
consumed by `lemma4Decoder`. -/
theorem lemma4Rearrange_flat (pD pQ mb rb : BitString) :
    lemma4Rearrange (pairCode pQ (pairCode mb (pairCode rb pD))) =
      pairCode (pairCode pD pQ) (pairCode mb rb) := by
  unfold lemma4Rearrange
  simp only [decodeFirst_pairCode, decodeSecond_pairCode]

/-- Length of the flat reconstruction program: coefficient one on the
set-description program `pD`. -/
theorem length_lemma4FlatInput (pD pQ mb rb : BitString) :
    (pairCode pQ (pairCode mb (pairCode rb pD))).length =
      pD.length + 2 * pQ.length + 2 * mb.length + 2 * rb.length + 3 := by
  simp only [length_pairCode]
  ring

/-- Reconstruction of `omegaCount q m` from a covering set `D`, the enumerator
code `q`, the bound `m`, and the outstanding-output count `r`, charging the set
description with coefficient one.  The stage `t` must be the *minimal* covering
stage; see the note on `plainKNat_omegaCount_le_of_stage_cover`. -/
theorem plainKNat_omegaCount_le_of_stage_cover_flat
    (V : Map) (hV : isOptimalConditional V) :
  ∃ c, ∀ q m D (hD : D.Nonempty) t,
    (∀ z ∈ D, z ∈ boundedOutputStage q m t) →
    (∀ t', t' < t → ¬ (∀ z ∈ D, z ∈ boundedOutputStage q m t')) →
    let r := omegaCount q m - (boundedOutputStage q m t).length
    plainKNat V (omegaCount q m) ≤
      plainSetComplexity V D hD +
        2 * plainK V (standardEnumeratorCode q) +
        2 * ((Nat.bits m).length : ENat) +
        2 * ((Nat.bits r).length : ENat) +
        (c : ENat) := by
  have hDecoder : Partrec (fun z : BitString =>
      lemma4Decoder V (lemma4Rearrange z, [])) :=
    (lemma4Decoder_partrec V hV.1).comp
      (Computable.pair lemma4Rearrange_primrec.to_comp (Computable.const []))
  obtain ⟨cMap, hMap⟩ :=
    plainK_partrec_map_le V hV
      (fun z : BitString => lemma4Decoder V (lemma4Rearrange z, [])) hDecoder
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  let c := 3 + cLen + cMap
  refine ⟨c, ?_⟩
  intro q m D hD t hcover hmin
  dsimp only
  have hDfinite : plainK V (codedUniformOn D hD).code ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top
        ((codedUniformOn D hD).code.length + cLen)))
      (hLen (codedUniformOn D hD).code)
  obtain ⟨pD, hpD, hpDLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := (codedUniformOn D hD).code) (y := []) hDfinite
  have hQfinite : plainK V (standardEnumeratorCode q) ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top
        ((standardEnumeratorCode q).length + cLen)))
      (hLen (standardEnumeratorCode q))
  obtain ⟨pQ, hpQ, hpQLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := standardEnumeratorCode q) (y := []) hQfinite
  let r := omegaCount q m - (boundedOutputStage q m t).length
  let input := pairCode pQ (pairCode (Nat.bits m) (pairCode (Nat.bits r) pD))
  have hstageLength :
      (boundedOutputStage q m t).length ≤ omegaCount q m := by
    unfold omegaCount
    exact (boundedOutputStage_prefix_completed q m t).length_le
  have heval : Nat.bits (omegaCount q m) ∈
      lemma4Decoder V (lemma4Rearrange input, []) := by
    have h := lemma4Decoder_eval V q m D hD t r pD pQ hpD hpQ hcover hmin
    rw [show lemma4Rearrange input =
        pairCode (pairCode pD pQ) (pairCode (Nat.bits m) (Nat.bits r)) from
      lemma4Rearrange_flat _ _ _ _]
    simpa only [r, Nat.add_sub_of_le hstageLength] using h
  have hinputLength : input.length =
      pD.length + 2 * pQ.length +
        2 * (Nat.bits m).length + 2 * (Nat.bits r).length + 3 :=
    length_lemma4FlatInput pD pQ (Nat.bits m) (Nat.bits r)
  have hpDLengthEq : (pD.length : ENat) = plainSetComplexity V D hD := by
    simpa only [plainSetComplexity] using hpDLength
  have hpQLengthEq : (pQ.length : ENat) =
      plainK V (standardEnumeratorCode q) := hpQLength
  calc
    plainKNat V (omegaCount q m)
        ≤ plainK V input + (cMap : ENat) := hMap input _ heval
    _ ≤ ((input.length : ENat) + (cLen : ENat)) + (cMap : ENat) := by
      gcongr
      exact hLen input
    _ = plainSetComplexity V D hD +
          2 * plainK V (standardEnumeratorCode q) +
          2 * ((Nat.bits m).length : ENat) +
          2 * ((Nat.bits r).length : ENat) + (c : ENat) := by
      rw [hinputLength]
      push_cast
      rw [hpDLengthEq, hpQLengthEq]
      dsimp [c]
      push_cast
      ac_rfl

/-- Uniform reconstruction of `omegaCount q m` from a covering set `D`, the code
`q`, the bound `m`, and the outstanding-output count `r`.

**Correctness note (Opus, iter 53).** `t` must be the *minimal* stage covering
`D` (hypothesis `hmin` below), matching the source: "run the program `q` until it
prints all elements from `D`". Without minimality the leaf is *false*: for a
fixed `(q, m)` the value `omegaCount q m` is not computable (one can never know
that `q` has finished enumerating the complexity-`≤ m` strings), so a decoder
receiving only `(D, q, m, r)` cannot recover it unless `r` is the remainder at the
decoder's own canonical stage — the first stage covering `D`, found by `Nat.rfind`.
For a non-minimal covering `t` the decoder would output
`(firstCoveringLength) + r < omegaCount q m`. The `< 2^(j+1)` bound from
`boundedOutputStage_remainder_lt_two_pow_succ_of_mem_standardBlock` holds for this
minimal stage as well, so downstream (`lemma_4`) is unaffected.

**Accounting note (Codex/Aristotle, iter 53).** The decoder's program is framed
flat as `pairCode pQ (pairCode (Nat.bits m) (pairCode (Nat.bits r) pD))` (see
`lemma4Rearrange`), whose literal length is
`|pD| + 2|pQ| + 2|bits m| + 2|bits r| + 3`.  This gives coefficient one on
`plainSetComplexity`, which is the coefficient that must be preserved for the
public assembly; the two logarithmic terms carry a factor `c` and are absorbed
downstream by `logSlack c n`.  Coefficient one on *all three* of
`plainSetComplexity`, `|bits m|` and `|bits r|` simultaneously (the shape
originally conjectured for this leaf, recorded below) is not obtainable from a
self-delimiting framing: concatenating three independent components with only
`O(1)` overhead would require the boundaries to be free.  The statement was
therefore restated with a factor `c` on the two logarithmic terms; nothing
downstream is weakened.

Original conjectured shape (not proved, kept for the record):
```
    plainKNat V (omegaCount q m) ≤
      plainSetComplexity V D hD +
        (c : ENat) * plainK V (standardEnumeratorCode q) +
        ((Nat.bits m).length : ENat) +
        ((Nat.bits r).length : ENat) +
        (c : ENat)
```
-/
theorem plainKNat_omegaCount_le_of_stage_cover
    (V : Map) (hV : isOptimalConditional V) :
  ∃ c, ∀ q m D (hD : D.Nonempty) t,
    (∀ z ∈ D, z ∈ boundedOutputStage q m t) →
    (∀ t', t' < t → ¬ (∀ z ∈ D, z ∈ boundedOutputStage q m t')) →
    let r := omegaCount q m - (boundedOutputStage q m t).length
    plainKNat V (omegaCount q m) ≤
      plainSetComplexity V D hD +
        (c : ENat) * plainK V (standardEnumeratorCode q) +
        (c : ENat) * ((Nat.bits m).length : ENat) +
        (c : ENat) * ((Nat.bits r).length : ENat) +
        (c : ENat) := by
  obtain ⟨c, hc⟩ := plainKNat_omegaCount_le_of_stage_cover_flat V hV
  refine ⟨max 2 c, ?_⟩
  intro q m D hD t hcover hmin
  dsimp only
  have h := hc q m D hD t hcover hmin
  dsimp only at h
  refine h.trans ?_
  have h2 : (2 : ENat) ≤ max 2 c := le_max_left _ _
  have hcc : c ≤ max 2 c := le_max_right _ _
  gcongr

/-! ### A width-parameterised framing of the reconstruction program

For the public assembly the remainder `r` must be charged with coefficient
exactly one *in bits of its width*, not `O(log r)` with a constant factor: the
width is `j + 1` for a standard block of log-cardinality `j`, and the `j` has to
cancel against the `m - j` upper bound for the block itself.  We therefore write
`r` in a fixed-width field of `width` bits, announce `width` self-delimitingly
(that costs only `O(log width) = O(log m)`), and place the set-description
program last so that it, too, is charged with coefficient one. -/
def lemma4WidthRearrange (z : BitString) : BitString :=
  pairCode
    (pairCode
      ((decodeSecond (decodeSecond (decodeSecond z))).drop
        (bitsToNat (decodeFirst (decodeSecond (decodeSecond z)))))
      (decodeFirst z))
    (pairCode (decodeFirst (decodeSecond z))
      (Nat.bits (decodeFixedWidthNatCode
        ((decodeSecond (decodeSecond (decodeSecond z))).take
          (bitsToNat (decodeFirst (decodeSecond (decodeSecond z))))))))

theorem lemma4WidthRearrange_primrec : Primrec lemma4WidthRearrange := by
  have hs2 : Primrec (fun z : BitString => decodeSecond (decodeSecond z)) :=
    decodeSecond_primrec.comp decodeSecond_primrec
  have hrest : Primrec (fun z : BitString =>
      decodeSecond (decodeSecond (decodeSecond z))) :=
    decodeSecond_primrec.comp hs2
  have hwidth : Primrec (fun z : BitString =>
      bitsToNat (decodeFirst (decodeSecond (decodeSecond z)))) :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp hs2)
  have hdrop : Primrec (fun z : BitString =>
      (decodeSecond (decodeSecond (decodeSecond z))).drop
        (bitsToNat (decodeFirst (decodeSecond (decodeSecond z))))) :=
    Primrec.list_drop.comp hrest hwidth
  have htake : Primrec (fun z : BitString =>
      (decodeSecond (decodeSecond (decodeSecond z))).take
        (bitsToNat (decodeFirst (decodeSecond (decodeSecond z))))) :=
    Primrec.list_take.comp hrest hwidth
  have hr : Primrec (fun z : BitString =>
      Nat.bits (decodeFixedWidthNatCode
        ((decodeSecond (decodeSecond (decodeSecond z))).take
          (bitsToNat (decodeFirst (decodeSecond (decodeSecond z))))))) :=
    primrecNatBits.comp (decodeFixedWidthNatCode_primrec.comp htake)
  exact pairCode_primrec.comp
    (pairCode_primrec.comp hdrop decodeFirst_primrec)
    (pairCode_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec) hr)

/-- The width-parameterised rearrangement turns the flat program layout into the
nested layout consumed by `lemma4Decoder`. -/
theorem lemma4WidthRearrange_flat (pD pQ mb : BitString) (r width : ℕ)
    (hr : r < 2 ^ width) :
    lemma4WidthRearrange
        (pairCode pQ (pairCode mb (pairCode (Nat.bits width)
          (fixedWidthNatCode r width ++ pD)))) =
      pairCode (pairCode pD pQ) (pairCode mb (Nat.bits r)) := by
  have hlen : (fixedWidthNatCode r width).length = width :=
    fixedWidthNatCode_length hr
  have htake : (fixedWidthNatCode r width ++ pD).take width =
      fixedWidthNatCode r width := List.take_left' hlen
  have hdrop : (fixedWidthNatCode r width ++ pD).drop width = pD :=
    List.drop_left' hlen
  unfold lemma4WidthRearrange
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
    htake, hdrop, decodeFixedWidthNatCode_encode]

/-- Length of the width-parameterised reconstruction program: coefficient one on
both the set-description program `pD` and the remainder field `width`. -/
theorem length_lemma4WidthInput (pD pQ mb : BitString) (r width : ℕ)
    (hr : r < 2 ^ width) :
    (pairCode pQ (pairCode mb (pairCode (Nat.bits width)
        (fixedWidthNatCode r width ++ pD)))).length =
      pD.length + width + 2 * pQ.length + 2 * mb.length +
        2 * (Nat.bits width).length + 3 := by
  simp only [length_pairCode, List.length_append, fixedWidthNatCode_length hr]
  ring

/-- Reconstruction of `omegaCount q m` from a covering set `D`, the enumerator
code `q`, the bound `m`, and the outstanding-output count `r`, where `r` is
transmitted in a fixed-width field of `width` bits.  Both the set description
and the width are charged with coefficient one; only the logarithmic terms carry
a constant factor.  As in `plainKNat_omegaCount_le_of_stage_cover`, `t` must be
the *minimal* covering stage. -/
theorem plainKNat_omegaCount_le_of_stage_cover_width
    (V : Map) (hV : isOptimalConditional V) :
  ∃ c : Nat, ∀ (q : Nat.Partrec.Code) (m : ℕ) (D : Finset BitString)
      (hD : D.Nonempty) (t width : ℕ),
    (∀ z ∈ D, z ∈ boundedOutputStage q m t) →
    (∀ t', t' < t → ¬ (∀ z ∈ D, z ∈ boundedOutputStage q m t')) →
    omegaCount q m - (boundedOutputStage q m t).length < 2 ^ width →
    plainKNat V (omegaCount q m) ≤
      plainSetComplexity V D hD + (width : ENat) +
        2 * plainK V (standardEnumeratorCode q) +
        2 * ((Nat.bits m).length : ENat) +
        2 * ((Nat.bits width).length : ENat) +
        (c : ENat) := by
  have hDecoder : Partrec (fun z : BitString =>
      lemma4Decoder V (lemma4WidthRearrange z, [])) :=
    (lemma4Decoder_partrec V hV.1).comp
      (Computable.pair lemma4WidthRearrange_primrec.to_comp
        (Computable.const []))
  obtain ⟨cMap, hMap⟩ :=
    plainK_partrec_map_le V hV
      (fun z : BitString => lemma4Decoder V (lemma4WidthRearrange z, []))
      hDecoder
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  refine ⟨3 + cLen + cMap, ?_⟩
  intro q m D hD t width hcover hmin hr
  have hDfinite : plainK V (codedUniformOn D hD).code ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top
        ((codedUniformOn D hD).code.length + cLen)))
      (hLen (codedUniformOn D hD).code)
  obtain ⟨pD, hpD, hpDLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := (codedUniformOn D hD).code) (y := []) hDfinite
  have hQfinite : plainK V (standardEnumeratorCode q) ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top
        ((standardEnumeratorCode q).length + cLen)))
      (hLen (standardEnumeratorCode q))
  obtain ⟨pQ, hpQ, hpQLength⟩ :=
    exists_program_of_KP_ne_top
      (M := V) (x := standardEnumeratorCode q) (y := []) hQfinite
  set r := omegaCount q m - (boundedOutputStage q m t).length with hrdef
  set input := pairCode pQ (pairCode (Nat.bits m) (pairCode (Nat.bits width)
    (fixedWidthNatCode r width ++ pD))) with hinput
  have hstageLength :
      (boundedOutputStage q m t).length ≤ omegaCount q m := by
    unfold omegaCount
    exact (boundedOutputStage_prefix_completed q m t).length_le
  have heval : Nat.bits (omegaCount q m) ∈
      lemma4Decoder V (lemma4WidthRearrange input, []) := by
    have h := lemma4Decoder_eval V q m D hD t r pD pQ hpD hpQ hcover hmin
    rw [hinput, lemma4WidthRearrange_flat pD pQ (Nat.bits m) r width hr]
    simpa only [hrdef, Nat.add_sub_of_le hstageLength] using h
  have hinputLength : input.length =
      pD.length + width + 2 * pQ.length +
        2 * (Nat.bits m).length + 2 * (Nat.bits width).length + 3 :=
    length_lemma4WidthInput pD pQ (Nat.bits m) r width hr
  have hpDLengthEq : (pD.length : ENat) = plainSetComplexity V D hD := by
    simpa only [plainSetComplexity] using hpDLength
  have hpQLengthEq : (pQ.length : ENat) =
      plainK V (standardEnumeratorCode q) := hpQLength
  calc
    plainKNat V (omegaCount q m)
        ≤ plainK V input + (cMap : ENat) := hMap input _ heval
    _ ≤ ((input.length : ENat) + (cLen : ENat)) + (cMap : ENat) := by
      gcongr
      exact hLen input
    _ = plainSetComplexity V D hD + (width : ENat) +
          2 * plainK V (standardEnumeratorCode q) +
          2 * ((Nat.bits m).length : ENat) +
          2 * ((Nat.bits width).length : ENat) +
          ((3 + cLen + cMap : ℕ) : ENat) := by
      rw [hinputLength]
      push_cast
      rw [hpDLengthEq, hpQLengthEq]
      ring

/-- **VS40 Lemma 4.**  For a standard model `B = standardBlock q m j []` and any
data string `y`, either the model is cheap to describe outright, or the residual
`m - |y|` is small, up to `O(C(q) + log n)`.

The proof follows the source.  A shortest *total* program for the model code,
given `y`, is turned into a total program for the model's canonical element `b`;
running that program over the whole cube of strings of length `|y|` produces a
finite set `D ∋ b` of at most `2^|y|` strings whose plain complexity is bounded
by the program length.  If some element of `D` is complex (`C(z) > m`), the
two-part description of that element via `D` forces `m - |y|` to be small.
Otherwise every element of `D` is enumerated by `q` below the bound `m`, and the
first stage covering `D` together with the remainder counter reconstructs
`Ω_m`; comparing with the lower bound on `C(Ω_m)` and the upper bound
`C(B) ≤ m - j + O(C(q) + log m)` for standard blocks bounds `C(B)` itself. -/
theorem lemma_4
    (V T : Map)
    (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    Lemma4Statement V T := by
  classical
  obtain ⟨c₁, hHead⟩ := totalCondK_headI_le_totalCondK_code T hT
  obtain ⟨c₂, hCube⟩ := exists_plain_fullCube_image_of_total_program V T hV hT
  obtain ⟨c₃, hMem⟩ := plainK_mem_le_of_plainSetComplexity_le V hV
  obtain ⟨c₄, hRecon⟩ := plainKNat_omegaCount_le_of_stage_cover_width V hV
  obtain ⟨c₅, hLower⟩ := plainKNat_omegaCount_lower_uniform V hV
  obtain ⟨c₆, hUpper⟩ := plainK_standardBlock_upper_uniform V hV
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  refine ⟨c₁ + c₂ + c₃ + c₄ + c₅ + c₆ +
    2 * (Nat.bits (c₁ + c₂ + 2)).length + 10, ?_⟩
  set c := c₁ + c₂ + c₃ + c₄ + c₅ + c₆ +
    2 * (Nat.bits (c₁ + c₂ + 2)).length + 10 with hcdef
  intro q hq m j y hB n hn
  set B := standardBlock q m j [] with hBdef
  set S := (codedUniformOn B hB).code with hSdef
  set K := (Nat.bits n).length with hKdef
  have hLn : y.length ≤ n := by rw [hn]; exact le_max_left _ _
  have hmn : m ≤ n := by rw [hn]; exact le_max_right _ _
  have hBL : (Nat.bits y.length).length ≤ K := length_natBits_mono hLn
  have hBm : (Nat.bits m).length ≤ K := length_natBits_mono hmn
  -- the enumerator's plain complexity is finite
  have hQfinite : plainK V (standardEnumeratorCode q) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by exact_mod_cast (ENat.coe_ne_top
        ((standardEnumeratorCode q).length + cLen)))
      (hLen (standardEnumeratorCode q))
  obtain ⟨Qv, hQv⟩ := ENat.ne_top_iff_exists.mp hQfinite
  -- an infinite total conditional complexity makes the bound trivial
  rcases eq_or_ne (totalCondK T S y) ⊤ with hNtop | hNtop
  · simp [hNtop]
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hNtop
  by_cases hmN : m ≤ N
  · refine le_trans (min_le_right _ _) ?_
    have h1 : ((m - y.length : ℕ) : ENat) ≤ (N : ENat) := by
      exact_mod_cast le_trans (Nat.sub_le _ _) hmN
    rw [hN] at h1
    exact h1.trans (le_trans le_self_add le_self_add)
  push_neg at hmN
  have hNn : N ≤ n := le_trans (le_of_lt hmN) hmn
  -- a short total program for the canonical element of the model
  have hbB : (canonicalFinsetList B).headI ∈ B := headI_mem_canonicalFinsetList hB
  set b := (canonicalFinsetList B).headI with hbdef
  have hbtotal : totalCondK T b y ≤ ((N + c₁ : ℕ) : ENat) := by
    have h := hHead B hB y
    rw [← hSdef, ← hN] at h
    push_cast
    exact h
  obtain ⟨p, hptot, hplen, hpprod⟩ := (totalCondK_le_iff T b y (N + c₁)).mp hbtotal
  obtain ⟨D, hD, hbD, hDcard, hDcx⟩ := hCube p y b hptot hpprod
  set a := N + c₁ + logSlack c₂ y.length with hadef
  have hDa : plainSetComplexity V D hD ≤ (a : ENat) := by
    refine hDcx.trans ?_
    have hle : programLength p + logSlack c₂ y.length ≤ a := by
      rw [hadef]; omega
    calc ((programLength p : ENat) + (logSlack c₂ y.length : ENat))
        = ((programLength p + logSlack c₂ y.length : ℕ) : ENat) := by push_cast; ring
      _ ≤ (a : ENat) := by exact_mod_cast hle
  by_cases hcase : ∀ z ∈ D, plainK V z ≤ (m : ENat)
  · -- Case B: the whole cube image is enumerated below the bound `m`
    have hsub : ∀ z ∈ D, z ∈ completedBoundedOutput q m := fun z hz =>
      (mem_completedBoundedOutput_iff_plainK_le hq m z).mpr (hcase z hz)
    obtain ⟨t, hcover, hmint⟩ := exists_minimal_boundedOutputStage_cover q m D hsub
    have hrem : omegaCount q m - (boundedOutputStage q m t).length < 2 ^ (j + 1) :=
      boundedOutputStage_remainder_lt_two_pow_succ_of_mem_standardBlock
        q m j t b hbB (hcover b hbD)
    have hjm : j ≤ m := standardBlock_exponent_le q m j b hbB
    have hBj : (Nat.bits (j + 1)).length ≤ K + 1 :=
      le_trans (length_natBits_mono (Nat.succ_le_succ (le_trans hjm hmn)))
        (length_natBits_succ_le n)
    have hK1 : plainKNat V (omegaCount q m) ≤
        ((a + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
          2 * (Nat.bits (j + 1)).length + c₄ : ℕ) : ENat) := by
      refine (hRecon q m D hD t (j + 1) hcover hmint hrem).trans ?_
      rw [← hQv]
      push_cast
      gcongr
    have hmB : m ≤ a + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
        2 * (Nat.bits (j + 1)).length + c₄ + c₅ * Qv + logSlack c₅ m := by
      have hstep : plainKNat V (omegaCount q m) +
          (c₅ : ENat) * plainK V (standardEnumeratorCode q) +
          ((logSlack c₅ m : ℕ) : ENat) ≤
          ((a + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
            2 * (Nat.bits (j + 1)).length + c₄ : ℕ) : ENat) +
          (c₅ : ENat) * plainK V (standardEnumeratorCode q) +
          ((logSlack c₅ m : ℕ) : ENat) := by gcongr
      have h1 := (hLower q hq m).trans hstep
      rw [← hQv] at h1
      have h2 : ((a + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
          2 * (Nat.bits (j + 1)).length + c₄ : ℕ) : ENat) +
          (c₅ : ENat) * (Qv : ENat) + ((logSlack c₅ m : ℕ) : ENat) =
          ((a + (j + 1) + 2 * Qv + 2 * (Nat.bits m).length +
            2 * (Nat.bits (j + 1)).length + c₄ + c₅ * Qv +
            logSlack c₅ m : ℕ) : ENat) := by push_cast; ring
      rw [h2] at h1
      exact_mod_cast h1
    -- the standard block is cheap given the residual `m - j`
    have hbB' : b ∈ standardBlock q m j b := hbB
    have hup := hUpper q m j b hbB'
    dsimp only at hup
    have hupS : plainK V S ≤ (((m - j) + c₆ * Qv + logSlack c₆ m : ℕ) : ENat) := by
      refine (le_of_eq (rfl : plainK V S = _)).trans (hup.trans (le_of_eq ?_))
      rw [← hQv]
      push_cast
      ring
    -- arithmetic: the residual is bounded by `N` plus the logarithmic slack
    have harith : (m - j) + c₆ * Qv + logSlack c₆ m ≤ N + c * Qv + logSlack c n := by
      have hX : m - j ≤ a + 1 + 2 * Qv + c₅ * Qv + 2 * (Nat.bits m).length +
          2 * (Nat.bits (j + 1)).length + c₄ + logSlack c₅ m := by
        refine Nat.sub_le_iff_le_add.mpr (hmB.trans (le_of_eq ?_))
        ring
      calc (m - j) + c₆ * Qv + logSlack c₆ m
          ≤ (a + 1 + 2 * Qv + c₅ * Qv + 2 * (Nat.bits m).length +
              2 * (Nat.bits (j + 1)).length + c₄ + logSlack c₅ m) +
              c₆ * Qv + logSlack c₆ m := by gcongr
        _ = N + c₁ + (c₂ * (Nat.bits y.length).length + c₂) + 1 + 2 * Qv +
              c₅ * Qv + 2 * (Nat.bits m).length +
              2 * (Nat.bits (j + 1)).length + c₄ +
              (c₅ * (Nat.bits m).length + c₅) + c₆ * Qv +
              (c₆ * (Nat.bits m).length + c₆) := by
            simp only [hadef, logSlack]
        _ ≤ N + c₁ + (c₂ * K + c₂) + 1 + 2 * Qv + c₅ * Qv + 2 * K +
              2 * (K + 1) + c₄ + (c₅ * K + c₅) + c₆ * Qv + (c₆ * K + c₆) := by
            gcongr
        _ = N + (2 + c₅ + c₆) * Qv +
              ((c₂ + 4 + c₅ + c₆) * K + (c₁ + c₂ + 3 + c₄ + c₅ + c₆)) := by ring
        _ ≤ N + c * Qv + (c * K + c) := by gcongr <;> omega
        _ = N + c * Qv + logSlack c n := by simp only [logSlack, hKdef]
    refine le_trans (min_le_left _ _) ?_
    calc plainK V S
        ≤ (((m - j) + c₆ * Qv + logSlack c₆ m : ℕ) : ENat) := hupS
      _ ≤ ((N + c * Qv + logSlack c n : ℕ) : ENat) := by exact_mod_cast harith
      _ = totalCondK T S y + (c : ENat) * plainK V (standardEnumeratorCode q) +
            (logSlack c n : ENat) := by
          rw [← hN, ← hQv]; push_cast; ring
  · -- Case A: some element of the cube image is complex
    push_neg at hcase
    obtain ⟨z, hzD, hz⟩ := hcase
    have hzle := hMem D hD z a hzD hDa
    have hmnat : m < a + finiteSetLogCard D + 2 * (Nat.bits a).length + c₃ := by
      exact_mod_cast lt_of_lt_of_le hz hzle
    have hcard : finiteSetLogCard D ≤ y.length :=
      (finiteSetLogCard_le_iff D y.length).mpr hDcard
    have habits : (Nat.bits a).length ≤ K + (Nat.bits (c₁ + c₂ + 2)).length + 2 := by
      refine bits_length_le_of_le_add_mul (c₁ + c₂) n a ?_
      calc a = N + c₁ + (c₂ * (Nat.bits y.length).length + c₂) := by
            simp only [hadef, logSlack]
        _ ≤ n + c₁ + (c₂ * K + c₂) := by gcongr
        _ ≤ n + (c₁ + c₂) * K + (c₁ + c₂) := by
            have : c₂ * K ≤ (c₁ + c₂) * K := Nat.mul_le_mul_right _ (by omega)
            omega
    have harith : m - y.length ≤ N + logSlack c n := by
      refine Nat.sub_le_iff_le_add.mpr ?_
      have hstep : a + 2 * (Nat.bits a).length + c₃ ≤ N + logSlack c n := by
        calc a + 2 * (Nat.bits a).length + c₃
            = N + c₁ + (c₂ * (Nat.bits y.length).length + c₂) +
                2 * (Nat.bits a).length + c₃ := by simp only [hadef, logSlack]
          _ ≤ N + c₁ + (c₂ * K + c₂) +
                2 * (K + (Nat.bits (c₁ + c₂ + 2)).length + 2) + c₃ := by gcongr
          _ = N + ((c₂ + 2) * K +
                (c₁ + c₂ + 2 * (Nat.bits (c₁ + c₂ + 2)).length + 4 + c₃)) := by ring
          _ ≤ N + (c * K + c) := by gcongr <;> omega
          _ = N + logSlack c n := by simp only [logSlack, hKdef]
      omega
    refine le_trans (min_le_right _ _) ?_
    calc ((m - y.length : ℕ) : ENat)
        ≤ ((N + logSlack c n : ℕ) : ENat) := by exact_mod_cast harith
      _ = (N : ENat) + (logSlack c n : ENat) := by push_cast; ring
      _ = totalCondK T S y + (logSlack c n : ENat) := by rw [hN]
      _ ≤ totalCondK T S y + (c : ENat) * plainK V (standardEnumeratorCode q) +
            (logSlack c n : ENat) := by
          gcongr
          exact le_self_add

end Kolmogorov
