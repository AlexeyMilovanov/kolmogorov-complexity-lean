/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Complexity.KolmogorovLevin.LogarithmicGap
import KolmogorovMathlib.Encoding.Tuples

/-!
# The fingerprint ladder

Tools for the impossibility of universal fingerprints in SUV Section 12.7: recoding a
condition through a computable map that reads a string parameter, and the *ladder* of
Problem 326 — the conditions "prefix of `A` of length `m`, together with the `i`-bit prefixes
of the `d` fingerprints" — with the three estimates that let one climb it: a rung is as
helpful as the prefix of `A` it contains; a rung with longer fingerprint prefixes and a
shorter prefix of `A` loses at most the missing bits; and `C(A)` is bounded by a rung together
with one fingerprint.

Complexity is plain `C`.

SUV Section 12.7, p. 383 (the remark after Theorem 235 and Problem 326).
-/

namespace Kolmogorov

open CodedFiniteDistribution

/-- Recoding the condition through a computable map that also reads a string parameter `w`
costs the length of `w` plus `O(log |w|)` bits: `C(x | y) ≤ C(x | f w y) + |w| + O(log |w|)`.
The program is the length of `w` in binary, then `w`, then a program for `x` given `f w y`. -/
theorem condK_le_condK_cond_map_add_length (D : Map) (hD : isOptimalConditional D)
    (f : BitString → BitString → BitString) (hf : Primrec₂ f) :
    ∃ c : ℕ, ∀ x y w : BitString,
      condK D x y ≤ condK D x (f w y) + (w.length : ℕ∞) + (logSlack c w.length : ℕ∞) := by
  let D' : Map := fun pr =>
    D ((decodeSecond pr.1).drop (bitsToNat (decodeFirst pr.1)),
      f ((decodeSecond pr.1).take (bitsToNat (decodeFirst pr.1))) pr.2)
  have hD' : isDecompressor D' := by
    refine hD.1.comp (Computable.pair ?_ ?_)
    · exact (Primrec.list_drop.comp
        (bitsToNat_primrec.comp (decodeFirst_primrec.comp Primrec.fst))
        (decodeSecond_primrec.comp Primrec.fst)).to_comp
    · exact (hf.comp (Primrec.list_take.comp
        (bitsToNat_primrec.comp (decodeFirst_primrec.comp Primrec.fst))
        (decodeSecond_primrec.comp Primrec.fst)) Primrec.snd).to_comp
  obtain ⟨c, hc⟩ := hD.2 D' hD'
  refine ⟨c + 2, fun x y w => ?_⟩
  rcases eq_or_ne (condK D x (f w y)) ⊤ with htop | htop
  · rw [htop, top_add, top_add]
    exact le_top
  obtain ⟨r, hr, hrlen⟩ := exists_program_of_KP_ne_top (M := D) (x := x) (y := f w y) htop
  have hrlen' : (programLength r : ℕ∞) = condK D x (f w y) := hrlen
  have hmem : x ∈ D' (pairCode (Nat.bits w.length) (w ++ r), y) := by
    simp only [D', decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
      List.drop_left, List.take_left]
    exact hr
  have h1 : condK D' x y ≤ ((pairCode (Nat.bits w.length) (w ++ r)).length : ℕ∞) :=
    (condK_le_iff D' _ _ _).2 ⟨_, le_rfl, hmem⟩
  rw [← hrlen']
  calc condK D x y ≤ condK D' x y + (c : ℕ∞) := hc _ _
    _ ≤ ((pairCode (Nat.bits w.length) (w ++ r)).length : ℕ∞) + (c : ℕ∞) := by gcongr
    _ ≤ (programLength r : ℕ∞) + (w.length : ℕ∞) + (logSlack (c + 2) w.length : ℕ∞) := by
      rw [length_pairCode, List.length_append]
      simp only [logSlack, programLength]
      norm_cast
      nlinarith [Nat.zero_le (Nat.bits w.length).length]

/-- The conditions of the ladder of SUV Problem 326: the prefix of `A` of length `m` together
with the list of the `i`-bit prefixes of the `d` fingerprints. -/
def fingerprintLadder {d : ℕ} (A : BitString) (X : Fin d → BitString) (i m : ℕ) :
    BitString :=
  pairCode (A.take m) (listCode (List.ofFn fun j => (X j).take i))

/-- The self-delimiting code of a list of strings of length at most `b` has length at most
`2 b + 1` times the number of strings. -/
theorem length_listCode_le (L : List BitString) (b : ℕ) (hL : ∀ x ∈ L, x.length ≤ b) :
    (listCode L).length ≤ L.length * (2 * b + 1) := by
  induction L with
  | nil => simp
  | cons x l ih =>
    rw [length_listCode_cons, List.length_cons]
    have hx := hL x (List.mem_cons_self ..)
    have := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    nlinarith

/-- Binary numerals of larger numbers are not shorter. -/
theorem length_bits_mono {a b : ℕ} (h : a ≤ b) :
    (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size h

/-- A rung of the ladder is at least as helpful as the prefix of `A` it contains: the rest of
`A` restores `A` from it. -/
theorem condK_fingerprintLadder_le_condK_self {d : ℕ} (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A : BitString) (X : Fin d → BitString) (i m : ℕ),
      condK D A (fingerprintLadder A X i m) ≤
        condK D A A + ((A.drop m).length : ℕ∞) + (logSlack c (A.drop m).length : ℕ∞) := by
  obtain ⟨c, hc⟩ := condK_le_condK_cond_map_add_length D hD (fun w y => decodeFirst y ++ w)
    (Primrec.list_append.comp (decodeFirst_primrec.comp Primrec.snd) Primrec.fst)
  refine ⟨c, fun A X i m => ?_⟩
  simpa only [fingerprintLadder, decodeFirst_pairCode, List.take_append_drop] using
    hc A (fingerprintLadder A X i m) (A.drop m)

/-- Climbing the ladder: if the `j`-th fingerprint restores `A` from the rung `(i, m)`, then
the rung `(i', m')` with longer fingerprint prefixes and a shorter prefix of `A` is worse by at
most `(m - m') + |X_j| - i'` bits plus `O(log)`: the missing bits of `A`, the tail of `X_j` and
the numbers `j`, `i`, `m - m'` rebuild the pair `(X_j, rung (i, m))` from the new rung. -/
theorem condK_fingerprintLadder_le_condK_pair_fingerprintLadder {d : ℕ} (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A : BitString) (X : Fin d → BitString) (j : Fin d) (i i' m m' : ℕ),
      i ≤ i' → m' ≤ m → m ≤ A.length →
      condK D A (fingerprintLadder A X i' m') ≤
        condK D A (pairCode (X j) (fingerprintLadder A X i m)) + ((m - m' : ℕ) : ℕ∞) +
          (((X j).drop i').length : ℕ∞) +
          (logSlack c (3 * (d + i + m + (X j).length) + 3) : ℕ∞) := by
  obtain ⟨c, hc⟩ := condK_le_condK_cond_map_add_length D hD (fun w y =>
      pairCode ((decodeListCode (decodeSecond y)).getD (bitsToNat (decodeFirst w)) [] ++
          (decodeSecond (decodeSecond (decodeSecond w))).drop
            (bitsToNat (decodeFirst (decodeSecond (decodeSecond w)))))
        (pairCode (decodeFirst y ++ (decodeSecond (decodeSecond (decodeSecond w))).take
            (bitsToNat (decodeFirst (decodeSecond (decodeSecond w)))))
          (listCode ((decodeListCode (decodeSecond y)).map fun s =>
            s.take (bitsToNat (decodeFirst (decodeSecond w)))))))
    (by
      have hL : Primrec fun p : BitString × BitString => decodeListCode (decodeSecond p.2) :=
        decodeListCode_primrec.comp (decodeSecond_primrec.comp Primrec.snd)
      have hj : Primrec fun p : BitString × BitString => bitsToNat (decodeFirst p.1) :=
        bitsToNat_primrec.comp (decodeFirst_primrec.comp Primrec.fst)
      have hi : Primrec fun p : BitString × BitString =>
          bitsToNat (decodeFirst (decodeSecond p.1)) :=
        bitsToNat_primrec.comp (decodeFirst_primrec.comp (decodeSecond_primrec.comp Primrec.fst))
      have hk : Primrec fun p : BitString × BitString =>
          bitsToNat (decodeFirst (decodeSecond (decodeSecond p.1))) :=
        bitsToNat_primrec.comp (decodeFirst_primrec.comp
          (decodeSecond_primrec.comp (decodeSecond_primrec.comp Primrec.fst)))
      have hr : Primrec fun p : BitString × BitString =>
          decodeSecond (decodeSecond (decodeSecond p.1)) :=
        decodeSecond_primrec.comp (decodeSecond_primrec.comp
          (decodeSecond_primrec.comp Primrec.fst))
      exact pairCode_primrec.comp
        (Primrec.list_append.comp ((Primrec.list_getD []).comp hL hj)
          (Primrec.list_drop.comp hk hr))
        (pairCode_primrec.comp
          (Primrec.list_append.comp (decodeFirst_primrec.comp Primrec.snd)
            (Primrec.list_take.comp hk hr))
          (listCode_primrec.comp (Primrec.list_map hL
            (Primrec.list_take.comp (hi.comp Primrec.fst) Primrec.snd)))))
  refine ⟨c + 6, fun A X j i i' m m' hii hmm hmA => ?_⟩
  set w := pairCode (Nat.bits j) (pairCode (Nat.bits i)
    (pairCode (Nat.bits (m - m')) ((A.drop m').take (m - m') ++ (X j).drop i'))) with hw
  have hlenA : ((A.drop m').take (m - m')).length = m - m' := by
    rw [List.length_take, List.length_drop]; omega
  have hget : (List.ofFn fun j' => (X j').take i').getD (j : ℕ) [] = (X j).take i' := by
    rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getElem_ofFn]
  have hA' : A.take m' ++ (A.drop m').take (m - m') = A.take m := by
    rw [← List.take_add, Nat.add_sub_of_le hmm]
  have hlist : (List.ofFn fun j' => (X j').take i').map (fun s => s.take i) =
      List.ofFn fun j' => (X j').take i := by
    rw [List.map_ofFn]
    congr 1
    funext j'
    simp [Function.comp, List.take_take, min_eq_left hii]
  have h := hc A (fingerprintLadder A X i' m') w
  simp only [hw, fingerprintLadder, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
    decodeListCode_listCode, List.take_left' hlenA, List.drop_left' hlenA, hget, hA', hlist,
    List.take_append_drop] at h
  have hwlen : w.length = 2 * (Nat.bits j).length + 2 * (Nat.bits i).length +
      2 * (Nat.bits (m - m')).length + 3 + (m - m') + ((X j).drop i').length := by
    simp only [hw, length_pairCode, List.length_append, hlenA]; ring
  set M := 3 * (d + i + m + (X j).length) + 3 with hM
  have hwM : w.length ≤ M := by
    have h1 := length_natBits_le (j : ℕ)
    have h2 := length_natBits_le i
    have h3 := length_natBits_le (m - m')
    have h4 : ((X j).drop i').length ≤ (X j).length := by rw [List.length_drop]; omega
    have h5 : (j : ℕ) < d := j.isLt
    omega
  have hbound : w.length + logSlack c w.length ≤
      (m - m') + ((X j).drop i').length + logSlack (c + 6) M := by
    have h1 := length_bits_mono (show (j : ℕ) ≤ M by have := j.isLt; omega)
    have h2 := length_bits_mono (show i ≤ M by omega)
    have h3 := length_bits_mono (show m - m' ≤ M by omega)
    have h4 := length_bits_mono hwM
    have h5 : c * (Nat.bits w.length).length ≤ c * (Nat.bits M).length :=
      Nat.mul_le_mul_left c h4
    simp only [logSlack]
    nlinarith
  calc condK D A (fingerprintLadder A X i' m')
      ≤ condK D A (pairCode (X j) (fingerprintLadder A X i m)) + (w.length : ℕ∞) +
          (logSlack c w.length : ℕ∞) := h
    _ = condK D A (pairCode (X j) (fingerprintLadder A X i m)) +
          ((w.length + logSlack c w.length : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ condK D A (pairCode (X j) (fingerprintLadder A X i m)) +
          (((m - m') + ((X j).drop i').length + logSlack (c + 6) M : ℕ) : ℕ∞) :=
        add_le_add le_rfl (Nat.cast_le.2 hbound)
    _ = _ := by push_cast; ring

/-- Bounding the complexity of `A` by a rung and a fingerprint:
`C(A) ≤ C(A | X_j, rung (i, m)) + |X_j| + m + d (2 i + 1) + O(log)`, the middle terms being
the length of the fingerprint, of the prefix of `A` and of the coded prefixes. -/
theorem plainK_le_condK_pair_fingerprintLadder {d : ℕ} (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (A : BitString) (X : Fin d → BitString) (j : Fin d) (i m : ℕ), m ≤ A.length →
      plainK D A ≤ condK D A (pairCode (X j) (fingerprintLadder A X i m)) +
        (((X j).length + m + d * (2 * i + 1) : ℕ) : ℕ∞) +
        (logSlack c (3 * ((X j).length + m + d * (2 * i + 1)) + 2) : ℕ∞) := by
  obtain ⟨c, hc⟩ := condK_le_condK_cond_map_add_length D hD (fun w _ =>
      pairCode ((decodeSecond (decodeSecond w)).take (bitsToNat (decodeFirst w)))
        (pairCode (((decodeSecond (decodeSecond w)).drop (bitsToNat (decodeFirst w))).take
            (bitsToNat (decodeFirst (decodeSecond w))))
          (((decodeSecond (decodeSecond w)).drop (bitsToNat (decodeFirst w))).drop
            (bitsToNat (decodeFirst (decodeSecond w))))))
    (by
      have hr : Primrec fun p : BitString × BitString => decodeSecond (decodeSecond p.1) :=
        decodeSecond_primrec.comp (decodeSecond_primrec.comp Primrec.fst)
      have ha : Primrec fun p : BitString × BitString => bitsToNat (decodeFirst p.1) :=
        bitsToNat_primrec.comp (decodeFirst_primrec.comp Primrec.fst)
      have hb : Primrec fun p : BitString × BitString =>
          bitsToNat (decodeFirst (decodeSecond p.1)) :=
        bitsToNat_primrec.comp (decodeFirst_primrec.comp (decodeSecond_primrec.comp Primrec.fst))
      have hs := Primrec.list_drop.comp ha hr
      exact pairCode_primrec.comp (Primrec.list_take.comp ha hr)
        (pairCode_primrec.comp (Primrec.list_take.comp hb hs) (Primrec.list_drop.comp hb hs)))
  refine ⟨c + 4, fun A X j i m hmA => ?_⟩
  simp only [fingerprintLadder]
  set L := listCode (List.ofFn fun j' => (X j').take i) with hL
  set w := pairCode (Nat.bits (X j).length) (pairCode (Nat.bits m) (X j ++ (A.take m ++ L)))
    with hw
  have hmlen : (A.take m).length = m := by rw [List.length_take]; omega
  have hLlen : L.length ≤ d * (2 * i + 1) := by
    have := length_listCode_le (List.ofFn fun j' => (X j').take i) i (fun x hx => by
      obtain ⟨j', rfl⟩ := List.mem_ofFn.1 hx
      exact List.length_take_le _ _)
    simpa [List.length_ofFn] using this
  have h := hc A [] w
  simp only [hw, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits, List.take_left,
    List.drop_left, List.take_left' hmlen, List.drop_left' hmlen] at h
  have hwlen : w.length = 2 * (Nat.bits (X j).length).length + 2 * (Nat.bits m).length + 2 +
      (X j).length + m + L.length := by
    simp only [hw, length_pairCode, List.length_append, hmlen]; ring
  set M := 3 * ((X j).length + m + d * (2 * i + 1)) + 2 with hM
  have hwM : w.length ≤ M := by
    have h1 := length_natBits_le (X j).length
    have h2 := length_natBits_le m
    omega
  have hbound : w.length + logSlack c w.length ≤
      ((X j).length + m + d * (2 * i + 1)) + logSlack (c + 4) M := by
    have h1 := length_bits_mono (show (X j).length ≤ M by omega)
    have h2 := length_bits_mono (show m ≤ M by omega)
    have h4 := length_bits_mono hwM
    have h5 : c * (Nat.bits w.length).length ≤ c * (Nat.bits M).length :=
      Nat.mul_le_mul_left c h4
    simp only [logSlack]
    nlinarith
  calc plainK D A = condK D A [] := rfl
    _ ≤ condK D A (pairCode (X j) (pairCode (A.take m) L)) + (w.length : ℕ∞) +
          (logSlack c w.length : ℕ∞) := h
    _ = condK D A (pairCode (X j) (pairCode (A.take m) L)) +
          ((w.length + logSlack c w.length : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ condK D A (pairCode (X j) (pairCode (A.take m) L)) +
          ((((X j).length + m + d * (2 * i + 1)) + logSlack (c + 4) M : ℕ) : ℕ∞) :=
        add_le_add le_rfl (Nat.cast_le.2 hbound)
    _ = _ := by push_cast; ring

end Kolmogorov
