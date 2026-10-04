/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.CommonInformation.Definitions
import KolmogorovMathlib.CommonInformation.PlainSymmetry
import KolmogorovMathlib.CommonInformation.OverlapExtraction
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Multisource.Requests
import KolmogorovMathlib.CommonInformation.WorstCaseRegion
import Mathlib.Data.Nat.Dist

/-!
# Minimal sufficient statistics: two channels of bounded capacity

The request of SUV Figure 49: the encoder of `A` knows `B` as well and sends at most `p` bits
down the left channel, while the right channel carries at most `q` bits computed from `B`
alone; the output node must produce `A`.  Fulfilling it amounts to choosing a string `B'`
("some part of the information in `B`") of length at most `q` that is simple given `B` and
satisfies `C(A|B') ≤ p`, so the feasible pairs `(p, q)` are the profile of the pair `⟨A, B⟩`;
this is the algorithmic counterpart of a minimal sufficient statistic.

The cut-flow conditions `C(A) ≤ p + q` and `C(A|B) ≤ p` are necessary (Problem 331).  They are
sufficient for pairs with extractable common information (Problem 332, stated with the
Chapter 11 predicates `ExtractableCommonInformationWithin` and `MutualInformationWithin`,
together with the book's example of overlapping substrings), while Theorem 237 exhibits a pair
whose profile is as small as it can be: the region `G` that is feasible for *all* pairs with
the same complexities.

`G` is read off the dark grey region of Figure 51 together with the text of p. 391:
`G = {(p,q) : p ≥ 2n} ∪ {(p,q) : p ≥ n and p + q ≥ 3n}`.  Neighbourhoods are taken in the
maximum metric on `ℕ × ℕ` (`Nat.dist` in each coordinate); the book leaves the norm
unspecified, all of them being equivalent up to the constants that `O(·)` absorbs.

Complexity is plain `C`.

SUV Section 12.12, pp. 390–399.
-/

namespace Kolmogorov

/-- The request of SUV Figure 49 on three nodes: `0` holds `A`, `1` holds `B` and reaches `0`
through an unlimited channel, the channel `0 → 2` has capacity `p`, the channel `1 → 2` has
capacity `q`, and the output node `2` must produce `A`.

SUV Figure 49, p. 390. -/
def boundedChannelsRequest (A B : BitString) (p q : ℕ) : InformationRequest (Fin 3) where
  edges := {(1, 0), (0, 2), (1, 2)}
  rank v := if v.val = 1 then 0 else if v.val = 0 then 1 else 2
  rank_lt := by decide +kernel
  capacity e := if e = (0, 2) then (p : ℕ∞) else if e = (1, 2) then (q : ℕ∞) else ⊤
  input v := if v = 0 then some A else if v = 1 then some B else none
  output v := if v = 2 then some A else none

/-- The cut containing only the output node: both bounded channels enter it, it has no input
node inside and `A` as its output, so the cut-flow condition it gives is `C(A) ≤ p + q`.

SUV Problem 331, p. 391. -/
theorem boundedChannelsRequest_output_cut (A B : BitString) (p q : ℕ) :
    (boundedChannelsRequest A B p q).cutCapacity {2} = ((p + q : ℕ) : ℕ∞) ∧
      (boundedChannelsRequest A B p q).cutInputs {2} = [] ∧
      (boundedChannelsRequest A B p q).cutOutputs {2} = [A] := by
  have hs : ({2} : Finset (Fin 3)).sort (· ≤ ·) = [2] := by simp
  have he : (boundedChannelsRequest A B p q).cutEdges {2} = {(0, 2), (1, 2)} := by
    ext e
    rcases e with ⟨u, v⟩
    simp [InformationRequest.cutEdges, boundedChannelsRequest, Prod.ext_iff]
    aesop
  rw [InformationRequest.cutCapacity, he, InformationRequest.cutInputs,
    InformationRequest.cutOutputs, hs]
  simp [boundedChannelsRequest]

/-- The cut containing the output node and the input node of `B`: only the channel of capacity
`p` enters it and `B` is an input inside it, so the cut-flow condition it gives is
`C(A|B) ≤ p`.

SUV Problem 331, p. 391. -/
theorem boundedChannelsRequest_conditional_cut (A B : BitString) (p q : ℕ) :
    (boundedChannelsRequest A B p q).cutCapacity {1, 2} = (p : ℕ∞) ∧
      (boundedChannelsRequest A B p q).cutInputs {1, 2} = [B] ∧
      (boundedChannelsRequest A B p q).cutOutputs {1, 2} = [A] := by
  have hs : ({1, 2} : Finset (Fin 3)).sort (· ≤ ·) = [1, 2] := by
    rw [Finset.sort_insert]
    · simp
    · simp
    · simp
  have he : (boundedChannelsRequest A B p q).cutEdges {1, 2} = {(0, 2)} := by
    ext e
    rcases e with ⟨u, v⟩
    simp [InformationRequest.cutEdges, boundedChannelsRequest, Prod.ext_iff]
    aesop
  rw [InformationRequest.cutCapacity, he, InformationRequest.cutInputs,
    InformationRequest.cutOutputs, hs]
  simp [boundedChannelsRequest]

/-- The pair `(p, q)` is feasible for `⟨A, B⟩` with precision `ε`: some `B'` of length at most
`q` is simple given `B` and leaves at most `p` bits of `A` to be sent, up to `ε`.  This is
what fulfilling `boundedChannelsRequest` amounts to, the left channel carrying a shortest
description of `A` given `B'`.

SUV Section 12.12, p. 391. -/
def IsTwoChannelFeasible (D : Map) (A B : BitString) (p q ε : ℕ) : Prop :=
  ∃ B' : BitString, B'.length ≤ q ∧ condK D B' B ≤ (ε : ℕ∞) ∧
    condK D A B' ≤ (p : ℕ∞) + (ε : ℕ∞)

private theorem IsTwoChannelFeasible.mono_slack {D : Map} {A B : BitString}
    {p q ε ε' : ℕ} (h : IsTwoChannelFeasible D A B p q ε) (hε : ε ≤ ε') :
    IsTwoChannelFeasible D A B p q ε' := by
  obtain ⟨B', hlen, hsimple, hrecover⟩ := h
  refine ⟨B', hlen, hsimple.trans ?_, hrecover.trans ?_⟩
  · exact_mod_cast hε
  · gcongr

/-- The region `G` of SUV Figure 51: the pairs `(p, q)` with `p ≥ 2n`, together with the pairs
with `p ≥ n` and `p + q ≥ 3n`.  For strings with `C(A) = C(B) = 2n` and `C(A,B) = 3n` every
pair in `G` is feasible, whatever the strings are.

SUV Section 12.12, pp. 391–392 (Figure 51). -/
def alwaysFeasibleRegion (n : ℕ) : Set (ℕ × ℕ) :=
  {pq | 2 * n ≤ pq.1} ∪ {pq | n ≤ pq.1 ∧ 3 * n ≤ pq.1 + pq.2}

private theorem isTwoChannelFeasible_of_large_left_capacity (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n p q : ℕ) (A B : BitString),
      plainK D A ≤ ((2 * n : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      2 * n ≤ p → IsTwoChannelFeasible D A B p q (logSlack c n) := by
  obtain ⟨cEmpty, hEmpty⟩ := condK_comp D hD (fun _ => []) (Computable.const [])
  refine ⟨c₀ + cEmpty, fun n p q A B hA hp => ?_⟩
  refine ⟨[], by simp, ?_, ?_⟩
  · exact (hEmpty B).trans (by
      exact_mod_cast show cEmpty ≤ logSlack (c₀ + cEmpty) n by
        simp only [logSlack]
        omega)
  · change plainK D A ≤ (p : ℕ∞) + (logSlack (c₀ + cEmpty) n : ℕ∞)
    exact hA.trans (by
      exact_mod_cast show 2 * n + logSlack c₀ n ≤
          p + logSlack (c₀ + cEmpty) n by
        rw [logSlack_add_constants]
        omega)

/-- Swapping the two halves of a pair code changes plain complexity by at most a constant:
the swap is a computable map of the code. -/
private theorem plainK_pairCode_swap_le (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x y : BitString,
      plainK D (pairCode y x) ≤ plainK D (pairCode x y) + (c : ℕ∞) := by
  let swap : BitString → BitString := fun w => pairCode (decodeSecond w) (decodeFirst w)
  have hEq : swap = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun w : BitString => (decodeSecond w, decodeFirst w)) := by
    funext w
    rfl
  have hSwap : Computable swap := by
    rw [hEq]
    exact pairCode_computable.comp (decodeSecond_computable.pair decodeFirst_computable)
  obtain ⟨c, hc⟩ := plainK_map_le D hD swap hSwap
  refine ⟨c, fun x y => ?_⟩
  simpa [swap, decodeFirst_pairCode, decodeSecond_pairCode] using hc (pairCode x y)

private theorem condK_le_of_complexity_profile (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (A B : BitString),
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D B + (logSlack c₀ n : ℕ∞) →
      plainK D (pairCode A B) ≤
        ((3 * n : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      condK D A B ≤ (n : ℕ∞) + (logSlack c n : ℕ∞) := by
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_lower_values D hD
  obtain ⟨cSwap, hSwap⟩ := plainK_pairCode_swap_le D hD
  obtain ⟨cAbs, hAbs⟩ := logSlack_absorb_of_le_linear cChain (3 + c₀) (c₀ + cSwap + 1)
  refine ⟨c₀ + c₀ + cAbs + cSwap, fun n A B hB hAB => ?_⟩
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD B
  obtain ⟨kAB, hkAB⟩ := exists_plainComplexityValue D hD (pairCode A B)
  obtain ⟨kBA, hkBA⟩ := exists_plainComplexityValue D hD (pairCode B A)
  obtain ⟨kA, hkA⟩ := exists_plainConditionalComplexityValue D hD A B
  have hChainInst : kB + kA ≤ kBA + logSlack cChain (kBA + 1) :=
    hChain B A kB kA kBA hkB hkA hkBA
  have hkB' : plainK D B = (kB : ℕ∞) := hkB
  have hkAB' : plainK D (pairCode A B) = (kAB : ℕ∞) := hkAB
  have hkBA' : plainK D (pairCode B A) = (kBA : ℕ∞) := hkBA
  have hkA' : condK D A B = (kA : ℕ∞) := hkA
  have hSwapInst : kBA ≤ kAB + cSwap := by
    have h := hSwap A B
    rw [hkBA', hkAB'] at h
    exact_mod_cast h
  have hBNat : 2 * n ≤ kB + logSlack c₀ n := by
    rw [hkB'] at hB
    exact_mod_cast hB
  have hABNat : kAB ≤ 3 * n + logSlack c₀ n := by
    rw [hkAB'] at hAB
    exact_mod_cast hAB
  have hLinear : logSlack c₀ n ≤ c₀ * n + c₀ := logSlack_le_self_linear c₀ n
  have hAbsInst : logSlack cChain (kBA + 1) ≤ logSlack cAbs n := by
    apply hAbs
    nlinarith
  have hConst : cSwap ≤ logSlack cSwap n := by
    unfold logSlack
    omega
  have hTotal : kA ≤ n + logSlack (c₀ + c₀ + cAbs + cSwap) n := by
    rw [logSlack_add_constants, logSlack_add_constants, logSlack_add_constants]
    omega
  rw [hkA']
  exact_mod_cast hTotal

/-- A prefix of `p` of a given length is simple given `p`: the program is the binary
notation of the length. -/
private theorem condK_take_given_self_le (D : Map) (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ (p : BitString) (q : ℕ),
      condK D (p.take q) p ≤ (((Nat.bits q).length + C : ℕ) : ℕ∞) := by
  let T : Map := fun pr => Part.some (pr.2.take (bitsToNat pr.1))
  have hT : isDecompressor T :=
    Computable.partrec
      (Primrec.list_take.comp (bitsToNat_primrec.comp Primrec.fst) Primrec.snd).to_comp
  obtain ⟨C, hC⟩ := hD.2 T hT
  refine ⟨C, fun p q => ?_⟩
  calc
    condK D (p.take q) p ≤ condK T (p.take q) p + (C : ℕ∞) := hC _ _
    _ ≤ ((Nat.bits q).length : ℕ∞) + (C : ℕ∞) := by
      gcongr
      apply sInf_le
      refine ⟨Nat.bits q, ?_, rfl⟩
      simp [T, produces, bitsToNat_bits]
    _ = (((Nat.bits q).length + C : ℕ) : ℕ∞) := by push_cast; rfl

/-- The first `q` bits of a shortest description `p` of `B` are logarithmically simple given
`B`: the shortest description itself is (`condK_shortestDescription_le`), and truncating it
costs `O(log q)`, which is `O(log C(B))` unless the truncation is trivial. -/
private theorem condK_truncated_shortestDescription_le (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (B p : BitString) (q k : ℕ),
      HasPlainComplexityValue D B k → produces D p [] B → p.length = k →
      condK D (p.take q) B ≤ (logSlack c (k + 1) : ℕ∞) := by
  obtain ⟨cShort, hShort⟩ := condK_shortestDescription_le D hD
  obtain ⟨cTake, hTake⟩ := condK_take_given_self_le D hD
  obtain ⟨cTrans, hTrans⟩ := condK_trans_visible_le D hD
  refine ⟨2 * cShort + 1 + cTake + cTrans, fun B p q k hk hp hpLen => ?_⟩
  have hShortInst := hShort B p k hk hp hpLen
  by_cases hq : p.length ≤ q
  · rw [List.take_of_length_le hq]
    exact hShortInst.trans (by
      exact_mod_cast logSlack_mono_left (by omega) (k + 1))
  · have hTransInst := hTrans B p (p.take q) (logSlack cShort (k + 1))
      ((Nat.bits q).length + cTake) hShortInst (hTake p q)
    refine hTransInst.trans ?_
    have hqk : (Nat.bits q).length ≤ (Nat.bits (k + 1)).length :=
      length_natBits_mono (by omega)
    have hArith : 2 * logSlack cShort (k + 1) + ((Nat.bits q).length + cTake) + cTrans ≤
        logSlack (2 * cShort + 1 + cTake + cTrans) (k + 1) := by
      unfold logSlack
      nlinarith
    exact_mod_cast hArith

/-- The decoder behind `condK_given_truncated_description_le`: the condition is a truncated
description `B'` of `B`, the program is the pair of the length of the full description and
the concatenation of the deleted suffix with a program for `A` given `B`.  The decoder cuts
the suffix off (its length is the recorded length minus `|B'|`), rebuilds `B` from the whole
description and runs the remaining program on `B`. -/
private def truncatedDescriptionDecoder (V : Map) : Map := fun pr =>
  (V (pr.2 ++ (decodeSecond pr.1).take (bitsToNat (decodeFirst pr.1) - pr.2.length), [])).bind
    fun B => V ((decodeSecond pr.1).drop (bitsToNat (decodeFirst pr.1) - pr.2.length), B)

private theorem truncatedDescriptionDecoder_isDecompressor (V : Map) (hV : isDecompressor V) :
    isDecompressor (truncatedDescriptionDecoder V) := by
  have hCut : Computable (fun pr : BitString × BitString =>
      bitsToNat (decodeFirst pr.1) - pr.2.length) :=
    Primrec.nat_sub.to_comp.comp
      (bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst))
      (Computable.list_length.comp Computable.snd)
  have hTail : Computable (fun pr : BitString × BitString => decodeSecond pr.1) :=
    decodeSecond_computable.comp Computable.fst
  have hFirst : Partrec (fun pr : BitString × BitString =>
      V (pr.2 ++ (decodeSecond pr.1).take (bitsToNat (decodeFirst pr.1) - pr.2.length), [])) :=
    Partrec.comp hV
      ((Computable.list_append.comp Computable.snd
        (Primrec.list_take.to_comp.comp hCut hTail)).pair (Computable.const []))
  have hSecond : Partrec (fun q : (BitString × BitString) × BitString =>
      V ((decodeSecond q.1.1).drop (bitsToNat (decodeFirst q.1.1) - q.1.2.length), q.2)) :=
    Partrec.comp hV
      ((Primrec.list_drop.to_comp.comp (hCut.comp Computable.fst)
        (hTail.comp Computable.fst)).pair Computable.snd)
  exact Partrec.bind hFirst hSecond

private theorem condK_given_truncated_description_le (D : Map)
    (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ (A B p : BitString) (q : ℕ), produces D p [] B →
      condK D A (p.take q) ≤ condK D A B + ((p.drop q).length : ℕ∞) +
        ((2 * (Nat.bits p.length).length + C : ℕ) : ℕ∞) := by
  obtain ⟨cD, hcD⟩ := hD.2 _ (truncatedDescriptionDecoder_isDecompressor D hD.1)
  refine ⟨cD + 1, fun A B p q hp => ?_⟩
  by_cases hAB : condK D A B = ⊤
  · rw [hAB, top_add, top_add]
    exact le_top
  obtain ⟨r, hr, hrLen⟩ := exists_program_of_KP_ne_top (M := D) (x := A) (y := B) hAB
  have hrLen' : (r.length : ℕ∞) = condK D A B := hrLen
  have hCut : p.length - (p.take q).length = (p.drop q).length := by
    rw [List.length_take, List.length_drop]
    omega
  have hProd : produces (truncatedDescriptionDecoder D)
      (pairCode (Nat.bits p.length) (p.drop q ++ r)) (p.take q) A := by
    unfold produces truncatedDescriptionDecoder
    rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits, hCut, List.take_left,
      List.drop_left, List.take_append_drop]
    exact Part.mem_bind_iff.mpr ⟨B, hp, hr⟩
  have hLen : (pairCode (Nat.bits p.length) (p.drop q ++ r)).length + cD ≤
      r.length + (p.drop q).length + (2 * (Nat.bits p.length).length + (cD + 1)) := by
    rw [length_pairCode, List.length_append]
    omega
  calc
    condK D A (p.take q) ≤ condK (truncatedDescriptionDecoder D) A (p.take q) + (cD : ℕ∞) :=
      hcD _ _
    _ ≤ ((pairCode (Nat.bits p.length) (p.drop q ++ r)).length : ℕ∞) + (cD : ℕ∞) := by
      gcongr
      exact sInf_le ⟨_, hProd, rfl⟩
    _ ≤ condK D A B + ((p.drop q).length : ℕ∞) +
        ((2 * (Nat.bits p.length).length + (cD + 1) : ℕ) : ℕ∞) := by
      rw [← hrLen']
      exact_mod_cast hLen

private theorem exists_truncated_description (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n q : ℕ) (A B : BitString),
      plainK D B ≤ ((2 * n : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      ∃ B' : BitString, B'.length ≤ q ∧
        condK D B' B ≤ (logSlack c n : ℕ∞) ∧
        condK D A B' ≤ condK D A B + ((2 * n - q : ℕ) : ℕ∞) +
          (logSlack c n : ℕ∞) := by
  obtain ⟨cShort, hShort⟩ := condK_truncated_shortestDescription_le D hD
  obtain ⟨cRec, hRec⟩ := condK_given_truncated_description_le D hD
  obtain ⟨cAbs, hAbs⟩ :=
    logSlack_absorb_of_le_linear (cShort + (2 + cRec)) (2 + c₀) (c₀ + 1)
  refine ⟨c₀ + cAbs, fun n q A B hB => ?_⟩
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD B
  have hkB' : plainK D B = (kB : ℕ∞) := hkB
  have hfinite : plainK D B ≠ ⊤ := by
    rw [hkB']
    exact ENat.natCast_ne_top _
  obtain ⟨p, hp, hpLen⟩ :=
    exists_program_of_KP_ne_top (M := D) (x := B) (y := []) hfinite
  have hpLen' : (p.length : ℕ∞) = plainK D B := hpLen
  have hpLenNat : p.length = kB := by
    rw [hkB'] at hpLen'
    exact_mod_cast hpLen'
  have hBNat : kB ≤ 2 * n + logSlack c₀ n := by
    rw [hkB'] at hB
    exact_mod_cast hB
  have hLinear : logSlack c₀ n ≤ c₀ * n + c₀ := logSlack_le_self_linear c₀ n
  have hAbsInst : logSlack (cShort + (2 + cRec)) (kB + 1) ≤ logSlack cAbs n := by
    apply hAbs
    nlinarith
  rw [logSlack_add_constants cShort (2 + cRec)] at hAbsInst
  refine ⟨p.take q, List.length_take_le q p, ?_, ?_⟩
  · refine (hShort B p q kB hkB hp hpLenNat).trans ?_
    exact_mod_cast show logSlack cShort (kB + 1) ≤ logSlack (c₀ + cAbs) n by
      rw [logSlack_add_constants]
      omega
  · have hDrop : (p.drop q).length = kB - q := by
      rw [List.length_drop, hpLenNat]
    have hBitsMono : (Nat.bits kB).length ≤ (Nat.bits (kB + 1)).length :=
      length_natBits_mono (Nat.le_succ kB)
    have hHeader : 2 * (Nat.bits kB).length + cRec ≤ logSlack (2 + cRec) (kB + 1) := by
      unfold logSlack
      have h2 : 2 * (Nat.bits (kB + 1)).length ≤ (2 + cRec) * (Nat.bits (kB + 1)).length :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hNat : (p.drop q).length + (2 * (Nat.bits p.length).length + cRec) ≤
        (2 * n - q) + logSlack (c₀ + cAbs) n := by
      rw [hDrop, hpLenNat, logSlack_add_constants]
      omega
    calc
      condK D A (p.take q) ≤ condK D A B + ((p.drop q).length : ℕ∞) +
          ((2 * (Nat.bits p.length).length + cRec : ℕ) : ℕ∞) := hRec A B p q hp
      _ = condK D A B +
          (((p.drop q).length + (2 * (Nat.bits p.length).length + cRec) : ℕ) : ℕ∞) := by
        simp only [Nat.cast_add, add_assoc]
      _ ≤ condK D A B + (((2 * n - q) + logSlack (c₀ + cAbs) n : ℕ) : ℕ∞) := by
        gcongr
      _ = condK D A B + ((2 * n - q : ℕ) : ℕ∞) + (logSlack (c₀ + cAbs) n : ℕ∞) := by
        simp only [Nat.cast_add, add_assoc]

private theorem isTwoChannelFeasible_of_diagonal_capacity (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n p q : ℕ) (A B : BitString),
      plainK D B ≤ ((2 * n : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D B + (logSlack c₀ n : ℕ∞) →
      plainK D (pairCode A B) ≤
        ((3 * n : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      n ≤ p → 3 * n ≤ p + q →
      IsTwoChannelFeasible D A B p q (logSlack c n) := by
  obtain ⟨cChain, hChain⟩ := condK_le_of_complexity_profile D hD c₀
  obtain ⟨cTrunc, hTrunc⟩ := exists_truncated_description D hD c₀
  refine ⟨cChain + cTrunc, fun n p q A B hB hB' hAB hp hpq => ?_⟩
  obtain ⟨B', hB'len, hB'B, hAB'⟩ := hTrunc n q A B hB
  refine ⟨B', hB'len, ?_, ?_⟩
  · exact hB'B.trans (by
      exact_mod_cast logSlack_mono_left (Nat.le_add_left cTrunc cChain) n)
  · calc
      condK D A B' ≤ condK D A B + ((2 * n - q : ℕ) : ℕ∞) +
          (logSlack cTrunc n : ℕ∞) := hAB'
      _ ≤ ((n : ℕ∞) + (logSlack cChain n : ℕ∞)) +
          ((2 * n - q : ℕ) : ℕ∞) + (logSlack cTrunc n : ℕ∞) := by
        gcongr
        exact hChain n A B hB' hAB
      _ = ((n + (2 * n - q) : ℕ) : ℕ∞) +
          (logSlack (cChain + cTrunc) n : ℕ∞) := by
        rw [logSlack_add_constants]
        push_cast
        ac_rfl
      _ ≤ (p : ℕ∞) + (logSlack (cChain + cTrunc) n : ℕ∞) := by
        gcongr
        exact_mod_cast show n + (2 * n - q) ≤ p by omega

/-- Every pair in `G` is feasible for every pair of strings with `C(A) = C(B) = 2n` and
`C(A,B) = 3n` up to `O(log n)`: send `A` itself, or `B` itself, or `B` with `k` bits deleted.
The three complexities are fixed by two-sided bounds with slack `logSlack c₀ n`, in the form of
Theorem 237 (`exists_pair_with_minimal_profile`).

SUV Section 12.12, pp. 391–392 (unnumbered claim about the dark grey region of Figure 51). -/
theorem isTwoChannelFeasible_of_mem_alwaysFeasibleRegion (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n p q : ℕ) (A B : BitString),
      plainK D A ≤ ((2 * n : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D A + (logSlack c₀ n : ℕ∞) →
      plainK D B ≤ ((2 * n : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D B + (logSlack c₀ n : ℕ∞) →
      ((3 * n : ℕ) : ℕ∞) ≤ plainK D (pairCode A B) + (logSlack c₀ n : ℕ∞) →
      plainK D (pairCode A B) ≤ ((3 * n : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      (p, q) ∈ alwaysFeasibleRegion n →
      IsTwoChannelFeasible D A B p q (logSlack c n) := by
  obtain ⟨cLeft, hLeft⟩ := isTwoChannelFeasible_of_large_left_capacity D hD c₀
  obtain ⟨cDiag, hDiag⟩ := isTwoChannelFeasible_of_diagonal_capacity D hD c₀
  refine ⟨cLeft + cDiag, ?_⟩
  intro n p q A B hA _ hB hB' _ hAB hpq
  rcases hpq with hp | ⟨hp, hpq⟩
  · exact IsTwoChannelFeasible.mono_slack (hLeft n p q A B hA hp)
      (logSlack_mono_left (Nat.le_add_right cLeft cDiag) n)
  · exact IsTwoChannelFeasible.mono_slack (hDiag n p q A B hB hB' hAB hp hpq)
      (logSlack_mono_left (Nat.le_add_left cDiag cLeft) n)

/-- Extracting all the mutual information into `z` makes conditioning on `z` as useful for
recovering `A` as conditioning on `B`.  The first inequality is the corresponding information
balance between `z` and the part of `A` left after `z` is known. -/
private theorem extractableCommonInformation_conditional_bounds (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n m : ℕ) (A B z : BitString),
      plainK D A ≤ (n : ℕ∞) → plainK D B ≤ (n : ℕ∞) →
      MutualInformationWithin D A B m (logSlack c₀ n) →
      ExtractableCommonInformationWithin D A B z m (logSlack c₀ n) →
      plainK D z + condK D A z ≤ plainK D A + (logSlack c n : ℕ∞) ∧
      condK D A z ≤ condK D A B + (logSlack c n : ℕ∞) := by
  obtain ⟨cCrude, hCrude⟩ := pairPlainK_twoStage_crude_values D hD
  obtain ⟨cUpper, hUpper⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cLower, hLower⟩ := pairPlainK_chain_lower_values D hD
  obtain ⟨cSwap, hSwap⟩ := pairPlainK_swap_le D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cAbsAZ, hAbsAZ⟩ :=
    logSlack_absorb_of_le_linear (cUpper + cLower) (2 + c₀)
      (c₀ + cCrude + cSwap + 3)
  obtain ⟨cAbsBA, hAbsBA⟩ :=
    logSlack_absorb_of_le_linear cUpper 3 (cCond + cCrude + 2)
  let cFirst := c₀ + cAbsAZ + cSwap
  let cSecond := 2 * c₀ + cAbsBA + cSwap
  refine ⟨cFirst + cSecond, fun n m A B z hA hB hMI hExtract => ?_⟩
  obtain ⟨kA, hkA⟩ := exists_plainComplexityValue D hD A
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD B
  obtain ⟨kz, hkz⟩ := exists_plainComplexityValue D hD z
  obtain ⟨kzA, hkzA⟩ := exists_plainConditionalComplexityValue D hD z A
  obtain ⟨kAz, hkAz⟩ := exists_plainConditionalComplexityValue D hD A z
  obtain ⟨kAB, hkAB⟩ := exists_plainComplexityValue D hD (pairCode A B)
  obtain ⟨kABc, hkABc⟩ := exists_plainConditionalComplexityValue D hD A B
  obtain ⟨kAZ, hkAZ, hkAZCrude⟩ := hCrude A z kA kzA hkA hkzA
  obtain ⟨kZA, hkZA⟩ := exists_plainComplexityValue D hD (pairCode z A)
  obtain ⟨kBA, hkBA, hkBACrude⟩ := hCrude B A kB kABc hkB hkABc
  have hkAN : kA ≤ n := by rw [hkA] at hA; exact_mod_cast hA
  have hkBN : kB ≤ n := by rw [hkB] at hB; exact_mod_cast hB
  have hkzA_le : kzA ≤ logSlack c₀ n := by
    have h := hExtract.1
    rw [hkzA] at h
    exact_mod_cast h
  have hkABc_le : kABc ≤ kA + cCond := by
    have h := hCond A B
    rw [hkABc, hkA] at h
    exact_mod_cast h
  have hkZA_swap : kZA ≤ kAZ + cSwap := by
    have h := hSwap A z
    change plainK D (pairCode z A) ≤ plainK D (pairCode A z) + (cSwap : ℕ∞) at h
    rw [hkZA, hkAZ] at h
    exact_mod_cast h
  have hkAB_swap : kAB ≤ kBA + cSwap := by
    have h := hSwap B A
    change plainK D (pairCode A B) ≤ plainK D (pairCode B A) + (cSwap : ℕ∞) at h
    rw [hkAB, hkBA] at h
    exact_mod_cast h
  have hAZLinear : kAZ + 1 ≤
      (2 + c₀) * n + (c₀ + cCrude + cSwap + 3) := by
    have hLinear := logSlack_le_self_linear c₀ n
    nlinarith
  have hZALinear : kZA + 1 ≤
      (2 + c₀) * n + (c₀ + cCrude + cSwap + 3) := by
    have hLinear := logSlack_le_self_linear c₀ n
    calc
      kZA + 1 ≤ kAZ + cSwap + 1 := by omega
      _ ≤ (2 * kA + 1 + kzA + cCrude) + cSwap + 1 := by omega
      _ ≤ (2 + c₀) * n + (c₀ + cCrude + cSwap + 3) := by
        nlinarith
  have hAZLogs : logSlack cUpper (kAZ + 1) + logSlack cLower (kZA + 1) ≤
      logSlack cAbsAZ n := by
    calc
      logSlack cUpper (kAZ + 1) + logSlack cLower (kZA + 1) ≤
          logSlack cUpper ((2 + c₀) * n + (c₀ + cCrude + cSwap + 3)) +
            logSlack cLower ((2 + c₀) * n + (c₀ + cCrude + cSwap + 3)) := by
        exact Nat.add_le_add
          (logSlack_mono_right cUpper hAZLinear)
          (logSlack_mono_right cLower hZALinear)
      _ = logSlack (cUpper + cLower)
          ((2 + c₀) * n + (c₀ + cCrude + cSwap + 3)) := by
        rw [logSlack_add_const]
      _ ≤ logSlack cAbsAZ n := hAbsAZ n _ (by omega)
  have hBalanceNat : kz + kAz ≤ kA + logSlack cFirst n := by
    have hUp := hUpper A z kA kzA kAZ hkA hkzA hkAZ
    have hLow := hLower z A kz kAz kZA hkz hkAz hkZA
    have hConst : cSwap ≤ logSlack cSwap n := by unfold logSlack; omega
    dsimp only [cFirst]
    rw [logSlack_add_constants, logSlack_add_constants]
    omega
  have hBALinear : kBA + 1 ≤ 3 * n + (cCond + cCrude + 2) := by omega
  have hBALog : logSlack cUpper (kBA + 1) ≤ logSlack cAbsBA n :=
    hAbsBA n _ hBALinear
  have hAFromBZNat : kA ≤ kABc + kz + logSlack cSecond n := by
    have hUp := hUpper B A kB kABc kBA hkB hkABc hkBA
    have hMINat : kA + kB ≤ kAB + m + logSlack c₀ n := by
      have h := hMI.2
      rw [pairPlainK, hkA, hkB, hkAB] at h
      exact_mod_cast h
    have hmz : m ≤ kz + logSlack c₀ n := by
      have h := hExtract.2.2.2
      rw [hkz] at h
      exact_mod_cast h
    have hConst : cSwap ≤ logSlack cSwap n := by unfold logSlack; omega
    dsimp only [cSecond]
    rw [logSlack_add_constants, logSlack_add_constants]
    have hTwice : 2 * logSlack c₀ n = logSlack (2 * c₀) n :=
      logSlack_nsmul 2 c₀ n
    rw [← hTwice]
    omega
  have hCondNat : kAz ≤ kABc + logSlack (cFirst + cSecond) n := by
    rw [logSlack_add_constants]
    omega
  constructor
  · rw [hkz, hkAz, hkA]
    exact_mod_cast hBalanceNat.trans (by
      gcongr
      exact logSlack_mono_left (Nat.le_add_right cFirst cSecond) n)
  · rw [hkAz, hkABc]
    exact_mod_cast hCondNat

/-- For strings with extractable common information the cut-flow conditions `C(A) ≤ p + q`
and `C(A|B) ≤ p` are also sufficient.  "Extractable common information" is the library's
notion (SUV Chapter 11): a string `z` that is `O(log n)`-simple given `A` and given `B` and
whose complexity is the mutual information `m = C(A) + C(B) - C(A,B)`, both up to `O(log n)`
(`ExtractableCommonInformationWithin` and `MutualInformationWithin`); `n` bounds the
complexities of `A` and `B`.

SUV Problem 332, p. 391. -/
theorem isTwoChannelFeasible_of_extractableCommonInformation (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n m p q : ℕ) (A B z : BitString),
      plainK D A ≤ (n : ℕ∞) → plainK D B ≤ (n : ℕ∞) →
      MutualInformationWithin D A B m (logSlack c₀ n) →
      ExtractableCommonInformationWithin D A B z m (logSlack c₀ n) →
      plainK D A ≤ ((p + q : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      condK D A B ≤ (p : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      IsTwoChannelFeasible D A B p q (logSlack c n) := by
  obtain ⟨cBounds, hBounds⟩ :=
    extractableCommonInformation_conditional_bounds D hD c₀
  obtain ⟨cShort, hShort⟩ := condK_truncated_shortestDescription_le D hD
  obtain ⟨cRec, hRec⟩ := condK_given_truncated_description_le D hD
  obtain ⟨cTrans, hTrans⟩ := condK_trans_visible_le D hD
  obtain ⟨cShortAbs, hShortAbs⟩ :=
    logSlack_absorb_of_le_linear cShort (2 + 2 * c₀) (2 * c₀ + 1)
  obtain ⟨cHeaderAbs, hHeaderAbs⟩ :=
    logSlack_absorb_of_le_linear (2 + cRec) (2 + 2 * c₀) (2 * c₀ + 1)
  let cSimple := 2 * c₀ + cShortAbs + cTrans
  let cRecover := cBounds + c₀ + cHeaderAbs
  refine ⟨cSimple + cRecover, ?_⟩
  intro n m p q A B z hA hB hMI hExtract hCutTotal hCutCond
  obtain ⟨kA, hkA⟩ := exists_plainComplexityValue D hD A
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD B
  obtain ⟨kAB, hkAB⟩ := exists_plainComplexityValue D hD (pairCode A B)
  obtain ⟨kz, hkz⟩ := exists_plainComplexityValue D hD z
  obtain ⟨kAz, hkAz⟩ := exists_plainConditionalComplexityValue D hD A z
  obtain ⟨kABc, hkABc⟩ := exists_plainConditionalComplexityValue D hD A B
  have hkAN : kA ≤ n := by rw [hkA] at hA; exact_mod_cast hA
  have hkBN : kB ≤ n := by rw [hkB] at hB; exact_mod_cast hB
  have hmN : m ≤ 2 * n + logSlack c₀ n := by
    have h := hMI.1
    rw [pairPlainK, hkAB, hkA, hkB] at h
    have hNat : kAB + m ≤ kA + kB + logSlack c₀ n := by exact_mod_cast h
    omega
  have hkzM : kz ≤ m + logSlack c₀ n := by
    have h := hExtract.2.2.1
    rw [hkz] at h
    exact_mod_cast h
  have hkzLinear : kz + 1 ≤
      (2 + 2 * c₀) * n + (2 * c₀ + 1) := by
    have hLinear := logSlack_le_self_linear c₀ n
    nlinarith
  have hShortFold : logSlack cShort (kz + 1) ≤ logSlack cShortAbs n :=
    hShortAbs n _ hkzLinear
  have hHeaderRaw : 2 * (Nat.bits kz).length + cRec ≤
      logSlack (2 + cRec) (kz + 1) := by
    have hBits : (Nat.bits kz).length ≤ (Nat.bits (kz + 1)).length :=
      length_natBits_mono (Nat.le_succ kz)
    unfold logSlack
    nlinarith
  have hHeaderFold : 2 * (Nat.bits kz).length + cRec ≤
      logSlack cHeaderAbs n :=
    hHeaderRaw.trans (hHeaderAbs n _ hkzLinear)
  have hfinite : plainK D z ≠ ⊤ := by rw [hkz]; exact ENat.natCast_ne_top _
  obtain ⟨r, hr, hrLen⟩ :=
    exists_program_of_KP_ne_top (M := D) (x := z) (y := []) hfinite
  have hrLenNat : r.length = kz := by
    change (r.length : ℕ∞) = plainK D z at hrLen
    rw [hkz] at hrLen
    exact_mod_cast hrLen
  have hPrefixZ : condK D (r.take q) z ≤ (logSlack cShort (kz + 1) : ℕ∞) :=
    hShort z r q kz hkz hr hrLenNat
  have hZB : condK D z B ≤ (logSlack c₀ n : ℕ∞) := hExtract.2.1
  have hSimpleRaw := hTrans B z (r.take q) (logSlack c₀ n)
    (logSlack cShort (kz + 1)) hZB hPrefixZ
  have hSimple : condK D (r.take q) B ≤ (logSlack cSimple n : ℕ∞) := by
    refine hSimpleRaw.trans ?_
    exact_mod_cast show 2 * logSlack c₀ n + logSlack cShort (kz + 1) + cTrans ≤
        logSlack cSimple n by
      dsimp only [cSimple]
      rw [logSlack_add_constants, logSlack_add_constants]
      have hConst : cTrans ≤ logSlack cTrans n := by unfold logSlack; omega
      have hTwice : 2 * logSlack c₀ n = logSlack (2 * c₀) n :=
        logSlack_nsmul 2 c₀ n
      rw [hTwice]
      omega
  obtain ⟨hBalance, hCond⟩ := hBounds n m A B z hA hB hMI hExtract
  have hBalanceNat : kz + kAz ≤ kA + logSlack cBounds n := by
    rw [hkz, hkAz, hkA] at hBalance
    exact_mod_cast hBalance
  have hCondNat : kAz ≤ kABc + logSlack cBounds n := by
    rw [hkAz, hkABc] at hCond
    exact_mod_cast hCond
  have hCutTotalNat : kA ≤ p + q + logSlack c₀ n := by
    rw [hkA] at hCutTotal
    exact_mod_cast hCutTotal
  have hCutCondNat : kABc ≤ p + logSlack c₀ n := by
    rw [hkABc] at hCutCond
    exact_mod_cast hCutCond
  have hDrop : (r.drop q).length = kz - q := by
    rw [List.length_drop, hrLenNat]
  have hRecoverRaw := hRec A z r q hr
  have hRecoverNat : kAz + (kz - q) + (2 * (Nat.bits kz).length + cRec) ≤
      p + logSlack cRecover n := by
    dsimp only [cRecover]
    rw [logSlack_add_constants, logSlack_add_constants]
    by_cases hq : q ≤ kz
    · omega
    · have hkzq : kz - q = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [hkzq]
      omega
  refine ⟨r.take q, List.length_take_le q r, ?_, ?_⟩
  · exact hSimple.trans (by
      exact_mod_cast logSlack_mono_left (Nat.le_add_right cSimple cRecover) n)
  · refine hRecoverRaw.trans ?_
    rw [hrLenNat, hDrop, hkAz]
    exact_mod_cast hRecoverNat.trans (by
      gcongr
      exact logSlack_mono_left (Nat.le_add_left cRecover cSimple) n)

/-- Decoder for `plainK_reconstruct_from_pairCode_le`: the program pairs the length `k` with a
description of `pairCode A B`; running it recovers the pair and glues `A` to the tail `B.drop k`,
so the concatenation `A ++ B.drop k` is described. -/
private def pairReconstructDecoder (V : Map) : Map := fun pr =>
  (V (decodeSecond pr.1, [])).bind fun ab =>
    Part.some (decodeFirst ab ++ (decodeSecond ab).drop (bitsToNat (decodeFirst pr.1)))

private theorem pairReconstructDecoder_isDecompressor (V : Map) (hV : isDecompressor V) :
    isDecompressor (pairReconstructDecoder V) := by
  have hInner : Partrec (fun pr : BitString × BitString => V (decodeSecond pr.1, [])) :=
    Partrec.comp hV ((decodeSecond_computable.comp Computable.fst).pair (Computable.const []))
  have hOuter : Partrec (fun q : (BitString × BitString) × BitString =>
      Part.some (decodeFirst q.2 ++ (decodeSecond q.2).drop (bitsToNat (decodeFirst q.1.1)))) :=
    Computable.partrec (Computable.list_append.comp
      (decodeFirst_computable.comp Computable.snd)
      (Primrec.list_drop.to_comp.comp
        (bitsToNat_primrec.to_comp.comp
          (decodeFirst_computable.comp (Computable.fst.comp Computable.fst)))
        (decodeSecond_computable.comp Computable.snd)))
  exact Partrec.bind hInner hOuter

/-- Reconstruction bound: `A ++ B.drop k` costs at most the complexity of the pair `⟨A, B⟩` plus
the logarithmic cost of the gluing offset `k`. -/
private theorem plainK_reconstruct_from_pairCode_le (D : Map) (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ (A B : BitString) (k : ℕ),
      plainK D (A ++ B.drop k) ≤
        plainK D (pairCode A B) + ((2 * (Nat.bits k).length + C : ℕ) : ℕ∞) := by
  obtain ⟨cD, hcD⟩ := hD.2 _ (pairReconstructDecoder_isDecompressor D hD.1)
  refine ⟨cD + 1, fun A B k => ?_⟩
  by_cases hAB : plainK D (pairCode A B) = ⊤
  · rw [hAB, top_add]; exact le_top
  obtain ⟨s, hs, hsLen⟩ :=
    exists_program_of_KP_ne_top (M := D) (x := pairCode A B) (y := []) hAB
  have hsLen' : (s.length : ℕ∞) = plainK D (pairCode A B) := hsLen
  have hProd : produces (pairReconstructDecoder D)
      (pairCode (Nat.bits k) s) [] (A ++ B.drop k) := by
    unfold produces pairReconstructDecoder
    rw [decodeSecond_pairCode]
    refine Part.mem_bind_iff.mpr ⟨pairCode A B, hs, ?_⟩
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits, Part.mem_some_iff]
  have hLen : (pairCode (Nat.bits k) s).length + cD ≤
      s.length + (2 * (Nat.bits k).length + (cD + 1)) := by
    rw [length_pairCode]; omega
  calc
    plainK D (A ++ B.drop k) = condK D (A ++ B.drop k) [] := rfl
    _ ≤ condK (pairReconstructDecoder D) (A ++ B.drop k) [] + (cD : ℕ∞) := hcD _ _
    _ ≤ ((pairCode (Nat.bits k) s).length : ℕ∞) + (cD : ℕ∞) := by
        gcongr; exact sInf_le ⟨_, hProd, rfl⟩
    _ ≤ plainK D (pairCode A B) + ((2 * (Nat.bits k).length + (cD + 1) : ℕ) : ℕ∞) := by
        rw [← hsLen']; exact_mod_cast hLen

/-- Decoder for `condK_slice_reconstruct_le`: the program records the left block length and the
left ++ right blocks; the condition supplies the middle block, recovered by splicing it in. -/
private def sliceReconstructDecoder : Map := fun pr =>
  Part.some ((decodeSecond pr.1).take (bitsToNat (decodeFirst pr.1)) ++ pr.2 ++
    (decodeSecond pr.1).drop (bitsToNat (decodeFirst pr.1)))

private theorem sliceReconstructDecoder_isDecompressor :
    isDecompressor sliceReconstructDecoder := by
  have hi : Computable (fun pr : BitString × BitString => bitsToNat (decodeFirst pr.1)) :=
    bitsToNat_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst)
  have hr : Computable (fun pr : BitString × BitString => decodeSecond pr.1) :=
    decodeSecond_computable.comp Computable.fst
  exact Computable.partrec (Computable.list_append.comp
    (Computable.list_append.comp (Primrec.list_take.to_comp.comp hi hr) Computable.snd)
    (Primrec.list_drop.to_comp.comp hi hr))

/-- Splicing bound: `pre ++ cond ++ suf` costs, given `cond`, at most the literal lengths of the
two outer blocks plus the logarithmic cost of the left length. -/
private theorem condK_slice_reconstruct_le (D : Map) (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ (cond pre suf : BitString),
      condK D (pre ++ cond ++ suf) cond ≤
        ((2 * (Nat.bits pre.length).length + 1 + pre.length + suf.length + C : ℕ) : ℕ∞) := by
  obtain ⟨cD, hcD⟩ := hD.2 _ sliceReconstructDecoder_isDecompressor
  refine ⟨cD + 1, fun cond pre suf => ?_⟩
  have hProd : produces sliceReconstructDecoder
      (pairCode (Nat.bits pre.length) (pre ++ suf)) cond (pre ++ cond ++ suf) := by
    unfold produces sliceReconstructDecoder
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
      List.take_left, List.drop_left, Part.mem_some_iff]
  have hLen : (pairCode (Nat.bits pre.length) (pre ++ suf)).length + cD ≤
      2 * (Nat.bits pre.length).length + 1 + pre.length + suf.length + (cD + 1) := by
    rw [length_pairCode, List.length_append]; omega
  calc
    condK D (pre ++ cond ++ suf) cond
        ≤ condK sliceReconstructDecoder (pre ++ cond ++ suf) cond + (cD : ℕ∞) := hcD _ _
    _ ≤ ((pairCode (Nat.bits pre.length) (pre ++ suf)).length : ℕ∞) + (cD : ℕ∞) := by
        gcongr; exact sInf_le ⟨_, hProd, rfl⟩
    _ ≤ ((2 * (Nat.bits pre.length).length + 1 + pre.length + suf.length + (cD + 1) : ℕ) :
          ℕ∞) := by
        exact_mod_cast hLen

/-- A prefix of an incompressible string is incompressible: `C(W[:j]) ≥ j - O(log n)`.  The rest
`W[j:]` is supplied literally, so `C(W) ≤ C(W[:j]) + (n - j) + O(log)`, and `C(W) ≥ n`. -/
private theorem plainK_take_ge (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n j : ℕ) (W : BitString), W.length = n → (n : ℕ∞) ≤ plainK D W →
      j ≤ n → (j : ℕ∞) ≤ plainK D (W.take j) + (logSlack c n : ℕ∞) := by
  obtain ⟨cThree, hThree⟩ := plainK_threeBlock_le D hD
  obtain ⟨cAbs, hAbs⟩ := logSlack_absorb_of_le_linear cThree 1 1
  refine ⟨cAbs, fun n j W hW hWK hj => ?_⟩
  obtain ⟨kA, hkA⟩ := exists_plainComplexityValue D hD (W.take j)
  have h := hThree [] (W.take j) (W.drop j)
  simp only [List.nil_append, List.take_append_drop, List.length_nil, List.length_drop] at h
  rw [hkA] at h
  have hnat : n ≤ kA + (0 + (W.length - j) + logSlack cThree (W.length + 1)) := by
    exact_mod_cast hWK.trans h
  rw [hW] at hnat
  have hA : logSlack cThree (n + 1) ≤ logSlack cAbs n := hAbs n _ (by omega)
  rw [hkA]
  exact_mod_cast (show j ≤ kA + logSlack cAbs n by omega)

/-- The part of the prefix outside the suffix is incompressible even given the suffix:
`C(W[:j] | W[i:]) ≥ i - O(log n)`.  Together `⟨W[i:], W[:j]⟩` reconstructs `W`, and the chain
rule bounds `C(W) ≤ C(W[i:]) + C(W[:j] | W[i:]) + O(log)` with `C(W[i:]) ≤ (n - i) + O(1)`. -/
private theorem condK_outside_ge (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n i j : ℕ) (W : BitString), W.length = n → (n : ℕ∞) ≤ plainK D W →
      i ≤ j → j ≤ n →
      (i : ℕ∞) ≤ condK D (W.take j) (W.drop i) + (logSlack c n : ℕ∞) := by
  obtain ⟨cRec, hRec⟩ := plainK_reconstruct_from_pairCode_le D hD
  obtain ⟨cSwap, hSwap⟩ := plainK_pairCode_swap_le D hD
  obtain ⟨cCh, hCh⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  obtain ⟨cAbs, hAbs⟩ := logSlack_absorb_of_le_linear cCh 3 (2 + cLen)
  refine ⟨2 + cAbs + cRec + cSwap + cLen, fun n i j W hW hWK hij hjn => ?_⟩
  obtain ⟨kW, hkW⟩ := exists_plainComplexityValue D hD W
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD (W.drop i)
  obtain ⟨kAB, hkAB⟩ := exists_plainConditionalComplexityValue D hD (W.take j) (W.drop i)
  obtain ⟨kBA, hkBA⟩ := exists_plainComplexityValue D hD (pairCode (W.drop i) (W.take j))
  have hWeq : (W.take j) ++ (W.drop i).drop (j - i) = W := by
    rw [List.drop_drop, Nat.add_sub_cancel' hij, List.take_append_drop]
  have hR := hRec (W.take j) (W.drop i) (j - i)
  rw [hWeq, hkW] at hR
  have hSw := hSwap (W.drop i) (W.take j)
  rw [hkBA] at hSw
  have hRn : kW ≤ kBA + cSwap + (2 * (Nat.bits (j - i)).length + cRec) := by
    have h : (kW : ℕ∞) ≤ (kBA : ℕ∞) + (cSwap : ℕ∞)
        + ((2 * (Nat.bits (j - i)).length + cRec : ℕ) : ℕ∞) := by
      refine hR.trans ?_; gcongr
    exact_mod_cast h
  have hChn : kBA ≤ kB + kAB + logSlack cCh (kBA + 1) :=
    hCh (W.drop i) (W.take j) kB kAB kBA hkB hkAB hkBA
  have hBn : kB ≤ (n - i) + cLen := by
    have h := hLen (W.drop i); rw [hkB] at h
    simp only [programLength, List.length_drop, hW] at h
    exact_mod_cast h
  have hBAn : kBA + 1 ≤ 3 * n + (2 + cLen) := by
    have h := hLen (pairCode (W.drop i) (W.take j)); rw [hkBA] at h
    simp only [programLength, length_pairCode, List.length_drop, List.length_take, hW] at h
    have hk : kBA ≤ ((n - i) + 1 + (n - i) + min j n) + cLen := by exact_mod_cast h
    omega
  have hAbsI : logSlack cCh (kBA + 1) ≤ logSlack cAbs n := hAbs n _ hBAn
  have hnn : n ≤ kW := by exact_mod_cast (hkW ▸ hWK)
  have hfold : logSlack cAbs n + cSwap + 2 * (Nat.bits (j - i)).length + cRec + cLen
      ≤ logSlack (2 + cAbs + cRec + cSwap + cLen) n := by
    rw [logSlack_add_constants, logSlack_add_constants, logSlack_add_constants,
      logSlack_add_constants]
    have hb : (Nat.bits (j - i)).length ≤ (Nat.bits n).length := length_natBits_mono (by omega)
    have e1 : cSwap ≤ logSlack cSwap n := by unfold logSlack; omega
    have e2 : cRec ≤ logSlack cRec n := by unfold logSlack; omega
    have e3 : cLen ≤ logSlack cLen n := by unfold logSlack; omega
    have e4 : 2 * (Nat.bits (j - i)).length ≤ logSlack 2 n := by unfold logSlack; omega
    omega
  rw [hkAB]
  exact_mod_cast
    (show i ≤ kAB + logSlack (2 + cAbs + cRec + cSwap + cLen) n by
      have hin : i ≤ n := le_trans hij hjn
      omega)

/-- The example of Problem 332: for overlapping substrings of an incompressible string the
cut-flow conditions are sufficient.  `A` is a prefix and `B` a suffix of an incompressible
`W`, overlapping when `i < j`, and every `(p, q)` satisfying the two cut-flow conditions is
feasible.  The general claim is `isTwoChannelFeasible_of_extractableCommonInformation`.

SUV Problem 332, p. 391 (the example in parentheses). -/
theorem isTwoChannelFeasible_overlappingSubstrings_example (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n i j p q : ℕ) (W : BitString),
      W.length = n → (n : ℕ∞) ≤ plainK D W → i ≤ j → j ≤ n →
      plainK D (W.take j) ≤ ((p + q : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      condK D (W.take j) (W.drop i) ≤ (p : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      IsTwoChannelFeasible D (W.take j) (W.drop i) p q (logSlack c n) := by
  obtain ⟨cLow, hLow⟩ := plainK_take_ge D hD
  obtain ⟨cOut, hOut⟩ := condK_outside_ge D hD
  obtain ⟨cSl, hSl⟩ := condK_slice_reconstruct_le D hD
  obtain ⟨cTk, hTk⟩ := condK_take_given_self_le D hD
  refine ⟨c₀ + cLow + cOut + cSl + cTk + 3, fun n i j p q W hW hWK hij hjn hCutT hCutC => ?_⟩
  set C := c₀ + cLow + cOut + cSl + cTk + 3 with hC
  set t := min q (j - i) with ht
  have hit : i + t ≤ j := by omega
  have htn : t ≤ n := by omega
  have hjq : j ≤ p + q + logSlack c₀ n + logSlack cLow n := by
    have h : (j : ℕ∞) ≤ (((p + q : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞)) + (logSlack cLow n : ℕ∞) := by
      refine (hLow n j W hW hWK hjn).trans ?_; gcongr
    exact_mod_cast h
  have hiq : i ≤ p + logSlack c₀ n + logSlack cOut n := by
    have h : (i : ℕ∞) ≤ ((p : ℕ∞) + (logSlack c₀ n : ℕ∞)) + (logSlack cOut n : ℕ∞) := by
      refine (hOut n i j W hW hWK hij hjn).trans ?_; gcongr
    exact_mod_cast h
  have hjt : j - t ≤ p + logSlack c₀ n + logSlack cLow n + logSlack cOut n := by omega
  have hCexp : logSlack C n = logSlack c₀ n + logSlack cLow n + logSlack cOut n
      + logSlack cSl n + logSlack cTk n + logSlack 3 n := by
    rw [hC, logSlack_add_constants, logSlack_add_constants, logSlack_add_constants,
      logSlack_add_constants, logSlack_add_constants]
  refine ⟨(W.drop i).take t, ?_, ?_, ?_⟩
  · rw [List.length_take, List.length_drop, hW]; omega
  · refine (hTk (W.drop i) t).trans ?_
    rw [hCexp]
    have hb : (Nat.bits t).length ≤ (Nat.bits n).length := length_natBits_mono htn
    have e1 : (Nat.bits t).length ≤ logSlack 3 n := by unfold logSlack; omega
    have e2 : cTk ≤ logSlack cTk n := by unfold logSlack; omega
    exact_mod_cast (show (Nat.bits t).length + cTk
      ≤ logSlack c₀ n + logSlack cLow n + logSlack cOut n + logSlack cSl n
        + logSlack cTk n + logSlack 3 n by omega)
  · have hEq : (W.take i) ++ ((W.drop i).take t) ++ ((W.take j).drop (i + t)) = W.take j := by
      have h1 : (W.take i) ++ ((W.drop i).take t) = W.take (i + t) := by
        rw [List.take_add]
      have h2 : W.take (i + t) = (W.take j).take (i + t) := by
        rw [List.take_take, min_eq_left hit]
      rw [h1, h2, List.take_append_drop]
    have hS := hSl ((W.drop i).take t) (W.take i) ((W.take j).drop (i + t))
    rw [hEq] at hS
    refine hS.trans ?_
    have hLi : (W.take i).length = i := by rw [List.length_take, hW]; omega
    have hLt : ((W.take j).drop (i + t)).length = j - (i + t) := by
      rw [List.length_drop, List.length_take, hW]; omega
    rw [hLi, hLt, hCexp]
    have hbi : (Nat.bits i).length ≤ (Nat.bits n).length := length_natBits_mono (by omega)
    have f1 : 2 * (Nat.bits i).length + 1 ≤ logSlack 3 n := by unfold logSlack; omega
    have f2 : cSl ≤ logSlack cSl n := by unfold logSlack; omega
    exact_mod_cast (show 2 * (Nat.bits i).length + 1 + i + (j - (i + t)) + cSl
      ≤ p + (logSlack c₀ n + logSlack cLow n + logSlack cOut n + logSlack cSl n
        + logSlack cTk n + logSlack 3 n) by omega)

/-- A pair whose second component has complexity at most `2n` while the pair has complexity at
least `3n` (both up to `logSlack c₀ n`) leaves at least `n` bits of the first component given
the second, up to a logarithmic slack: the easy half of symmetry of information
`C(B,A) ≤ C(B) + C(A|B) + O(log)`, the pair being short. -/
private theorem le_condK_of_complexity_profile (D : Map) (hD : isOptimalConditional D)
    (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (A B : BitString), A.length ≤ 2 * n + 2 → B.length ≤ 2 * n + 2 →
      plainK D B ≤ ((2 * n : ℕ) : ℕ∞) + (logSlack c₀ n : ℕ∞) →
      ((3 * n : ℕ) : ℕ∞) ≤ plainK D (pairCode A B) + (logSlack c₀ n : ℕ∞) →
      (n : ℕ∞) ≤ condK D A B + (logSlack c n : ℕ∞) := by
  obtain ⟨cU, hU⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cS, hS⟩ := plainK_pairCode_swap_le D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  obtain ⟨cAbs, hAbs⟩ := logSlack_absorb_of_le_linear cU 6 (8 + cLen)
  refine ⟨c₀ + c₀ + cAbs + cS, fun n A B hA hB hBK hABK => ?_⟩
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD B
  obtain ⟨kA, hkA⟩ := exists_plainConditionalComplexityValue D hD A B
  obtain ⟨kAB, hkAB⟩ := exists_plainComplexityValue D hD (pairCode A B)
  obtain ⟨kBA, hkBA⟩ := exists_plainComplexityValue D hD (pairCode B A)
  have hUp := hU B A kB kA kBA hkB hkA hkBA
  have hkB' : plainK D B = (kB : ℕ∞) := hkB
  have hkA' : condK D A B = (kA : ℕ∞) := hkA
  have hkAB' : plainK D (pairCode A B) = (kAB : ℕ∞) := hkAB
  have hkBA' : plainK D (pairCode B A) = (kBA : ℕ∞) := hkBA
  have hSw : kAB ≤ kBA + cS := by
    have h := hS B A
    rw [hkAB', hkBA'] at h
    exact_mod_cast h
  have hBA_len : kBA ≤ 2 * B.length + 1 + A.length + cLen := by
    have h := hLen (pairCode B A)
    rw [hkBA', programLength, length_pairCode] at h
    have h' : kBA ≤ B.length + 1 + B.length + A.length + cLen := by exact_mod_cast h
    omega
  have hAbsInst : logSlack cU (kBA + 1) ≤ logSlack cAbs n := hAbs n _ (by omega)
  have hBN : kB ≤ 2 * n + logSlack c₀ n := by
    rw [hkB'] at hBK
    exact_mod_cast hBK
  have hABN : 3 * n ≤ kAB + logSlack c₀ n := by
    rw [hkAB'] at hABK
    exact_mod_cast hABK
  have hConst : cS ≤ logSlack cS n := by
    unfold logSlack
    omega
  have hTotal : n ≤ kA + logSlack (c₀ + c₀ + cAbs + cS) n := by
    rw [logSlack_add_constants, logSlack_add_constants, logSlack_add_constants]
    omega
  rw [hkA']
  exact_mod_cast hTotal

/-- Symmetry of information for short strings, in the direction used in Theorem 237:
`C(z) + C(B|z) ≤ C(z,B) ≤ C(B) + C(z|B)` up to `O(log n)` when `z` and `B` have length
`O(n)`. -/
private theorem plainK_add_condK_le_of_short (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n : ℕ) (z B : BitString), z.length ≤ 3 * n → B.length ≤ 2 * n + 2 →
      plainK D z + condK D B z ≤ plainK D B + condK D z B + (logSlack c n : ℕ∞) := by
  obtain ⟨cL, hL⟩ := pairPlainK_chain_lower_values D hD
  obtain ⟨cU, hU⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cS, hS⟩ := plainK_pairCode_swap_le D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  obtain ⟨cAbs, hAbs⟩ := logSlack_absorb_of_le_linear (cL + cU) 8 (8 + cLen)
  refine ⟨cAbs + cAbs + cS, fun n z B hz hB => ?_⟩
  obtain ⟨kz, hkz⟩ := exists_plainComplexityValue D hD z
  obtain ⟨kB, hkB⟩ := exists_plainComplexityValue D hD B
  obtain ⟨kBz, hkBz⟩ := exists_plainConditionalComplexityValue D hD B z
  obtain ⟨kzB, hkzB⟩ := exists_plainConditionalComplexityValue D hD z B
  obtain ⟨kpzB, hkpzB⟩ := exists_plainComplexityValue D hD (pairCode z B)
  obtain ⟨kpBz, hkpBz⟩ := exists_plainComplexityValue D hD (pairCode B z)
  have hLo := hL z B kz kBz kpzB hkz hkBz hkpzB
  have hUp := hU B z kB kzB kpBz hkB hkzB hkpBz
  have hkpzB' : plainK D (pairCode z B) = (kpzB : ℕ∞) := hkpzB
  have hkpBz' : plainK D (pairCode B z) = (kpBz : ℕ∞) := hkpBz
  have hSw : kpzB ≤ kpBz + cS := by
    have h := hS B z
    rw [hkpzB', hkpBz'] at h
    exact_mod_cast h
  have hzB_len : kpzB ≤ z.length + 1 + z.length + B.length + cLen := by
    have h := hLen (pairCode z B)
    rw [hkpzB', programLength, length_pairCode] at h
    exact_mod_cast h
  have hBz_len : kpBz ≤ B.length + 1 + B.length + z.length + cLen := by
    have h := hLen (pairCode B z)
    rw [hkpBz', programLength, length_pairCode] at h
    exact_mod_cast h
  have hAbs₁ : logSlack cL (kpzB + 1) ≤ logSlack cAbs n :=
    (logSlack_mono_left (Nat.le_add_right cL cU) _).trans (hAbs n _ (by omega))
  have hAbs₂ : logSlack cU (kpBz + 1) ≤ logSlack cAbs n :=
    (logSlack_mono_left (Nat.le_add_left cU cL) _).trans (hAbs n _ (by omega))
  have hConst : cS ≤ logSlack cS n := by
    unfold logSlack
    omega
  have hTotal : kz + kBz ≤ kB + kzB + logSlack (cAbs + cAbs + cS) n := by
    rw [logSlack_add_constants, logSlack_add_constants]
    omega
  rw [show plainK D z = (kz : ℕ∞) from hkz, show condK D B z = (kBz : ℕ∞) from hkBz,
    show plainK D B = (kB : ℕ∞) from hkB, show condK D z B = (kzB : ℕ∞) from hkzB]
  exact_mod_cast hTotal

/-- Theorem 237: for every `n` there are strings `A`, `B` of complexity `2n + O(log n)` with
`C(A,B) = 3n + O(log n)` whose profile is as small as possible — for every `B'` the pair
`⟨C(A|B'), l(B')⟩` lies in the `O(log n + C(B'|B))`-neighbourhood of `G`.  So the profile of a
pair is not determined by the complexities of its components.

The neighbourhood is taken coordinatewise in `Nat.dist`; the book does not fix a norm.

SUV Theorem 237, p. 392. -/
theorem exists_pair_with_minimal_profile (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ A B : BitString,
      plainK D A ≤ ((2 * n : ℕ) : ℕ∞) + (logSlack c n : ℕ∞) ∧
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D A + (logSlack c n : ℕ∞) ∧
      plainK D B ≤ ((2 * n : ℕ) : ℕ∞) + (logSlack c n : ℕ∞) ∧
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D B + (logSlack c n : ℕ∞) ∧
      plainK D (pairCode A B) ≤ ((3 * n : ℕ) : ℕ∞) + (logSlack c n : ℕ∞) ∧
      ((3 * n : ℕ) : ℕ∞) ≤ plainK D (pairCode A B) + (logSlack c n : ℕ∞) ∧
      ∀ B' : BitString, ∃ pq ∈ alwaysFeasibleRegion n,
        Nat.dist (condK D A B').toNat pq.1 ≤ logSlack c n + c * (condK D B' B).toNat + c ∧
        Nat.dist B'.length pq.2 ≤ logSlack c n + c * (condK D B' B).toNat + c := by
  obtain ⟨cM, hM⟩ := muchnik_worst_case_region D hD
  obtain ⟨c₁, h₁⟩ := le_condK_of_complexity_profile D hD cM
  obtain ⟨c₂, h₂⟩ := plainK_add_condK_le_of_short D hD
  obtain ⟨cT, hT⟩ := condK_trans_visible_le D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  set K₀ := cM + c₁ + c₂ + cT + cLen with hK₀
  refine ⟨8 * K₀ + 2, fun n => ?_⟩
  obtain ⟨A, B, kx, ky, kxy, hAl, hBl, hkx, hky, hkxy, hcx, hcy, hcxy, -, hTri⟩ := hM n
  have hkx' : plainK D A = (kx : ℕ∞) := hkx
  have hky' : plainK D B = (ky : ℕ∞) := hky
  have hkxy' : plainK D (pairCode A B) = (kxy : ℕ∞) := hkxy
  have hW : logSlack (8 * K₀ + 2) n = 8 * logSlack K₀ n + logSlack 2 n := by
    unfold logSlack
    ring
  have hM₀ : logSlack cM n ≤ logSlack K₀ n := logSlack_mono_left (by omega) n
  have h₁₀ : logSlack c₁ n ≤ logSlack K₀ n := logSlack_mono_left (by omega) n
  have h₂₀ : logSlack c₂ n ≤ logSlack K₀ n := logSlack_mono_left (by omega) n
  have hK₀c : cT + cLen ≤ logSlack K₀ n := by
    unfold logSlack
    omega
  have hw : logSlack cM n ≤ logSlack (8 * K₀ + 2) n := by omega
  unfold NatCloseWithin at hcx hcy hcxy
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_, fun B' => ?_⟩
  · rw [hkx']
    exact_mod_cast (show kx ≤ 2 * n + logSlack (8 * K₀ + 2) n by omega)
  · rw [hkx']
    exact_mod_cast (show 2 * n ≤ kx + logSlack (8 * K₀ + 2) n by omega)
  · rw [hky']
    exact_mod_cast (show ky ≤ 2 * n + logSlack (8 * K₀ + 2) n by omega)
  · rw [hky']
    exact_mod_cast (show 2 * n ≤ ky + logSlack (8 * K₀ + 2) n by omega)
  · rw [hkxy']
    exact_mod_cast (show kxy ≤ 3 * n + logSlack (8 * K₀ + 2) n by omega)
  · rw [hkxy']
    exact_mod_cast (show 3 * n ≤ kxy + logSlack (8 * K₀ + 2) n by omega)
  obtain ⟨kp, hkp⟩ := exists_plainConditionalComplexityValue D hD A B'
  obtain ⟨kr, hkr⟩ := exists_plainConditionalComplexityValue D hD B' B
  have hkp' : condK D A B' = (kp : ℕ∞) := hkp
  have hkr' : condK D B' B = (kr : ℕ∞) := hkr
  rw [hkp', hkr', ENat.toNat_natCast, ENat.toNat_natCast]
  set s := logSlack (8 * K₀ + 2) n + (8 * K₀ + 2) * kr + (8 * K₀ + 2) with hs
  have hcr : 2 * kr ≤ (8 * K₀ + 2) * kr := Nat.mul_le_mul_right _ (by omega)
  refine ⟨(kp + s, B'.length + s), ?_, by unfold Nat.dist; omega, by unfold Nat.dist; omega⟩
  simp only [alwaysFeasibleRegion, Set.mem_union, Set.mem_ofPred_eq]
  -- the lower bound `C(A|B') ≥ n - O(log n + C(B'|B))`
  obtain ⟨kab, hkab⟩ := exists_plainConditionalComplexityValue D hD A B
  have hkab' : condK D A B = (kab : ℕ∞) := hkab
  have hBK : plainK D B ≤ ((2 * n : ℕ) : ℕ∞) + (logSlack cM n : ℕ∞) := by
    rw [hky']
    exact_mod_cast hcy.1
  have hABK : ((3 * n : ℕ) : ℕ∞) ≤ plainK D (pairCode A B) + (logSlack cM n : ℕ∞) := by
    rw [hkxy']
    exact_mod_cast hcxy.2
  have hF₀ : n ≤ kab + logSlack c₁ n := by
    have h := h₁ n A B hAl.le hBl.le hBK hABK
    rw [hkab'] at h
    exact_mod_cast h
  have hTr : kab ≤ 2 * kr + kp + cT := by
    have h := hT B B' A kr kp hkr'.le hkp'.le
    rw [hkab'] at h
    exact_mod_cast h
  by_cases hr : n ≤ kr
  · left
    omega
  by_cases hq : 3 * n ≤ B'.length
  · right
    omega
  obtain ⟨kz, hkz⟩ := exists_plainComplexityValue D hD B'
  obtain ⟨kBz, hkBz⟩ := exists_plainConditionalComplexityValue D hD B B'
  have hkz' : plainK D B' = (kz : ℕ∞) := hkz
  have hkBz' : condK D B B' = (kBz : ℕ∞) := hkBz
  have hSym : kz + kBz ≤ ky + kr + logSlack c₂ n := by
    have h := h₂ n B' B (by omega) hBl.le
    rw [hkz', hkBz', hky', hkr'] at h
    exact_mod_cast h
  have hzLen : kz ≤ B'.length + cLen := by
    have h := hLen B'
    rw [hkz'] at h
    exact_mod_cast h
  rcases hTri B' with h | h | h
  · rw [hkz', hkp'] at h
    have h' : 3 * n ≤ kz + kp + logSlack cM n := by exact_mod_cast h
    right
    omega
  · rw [hkz', hkBz'] at h
    have h' : 3 * n ≤ kz + kBz + logSlack cM n := by exact_mod_cast h
    left
    omega
  · rw [hkz', hkp', hkBz'] at h
    have h' : 4 * n ≤ kz + kp + kBz + logSlack cM n := by exact_mod_cast h
    left
    omega

end Kolmogorov
