/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.VilleExample.CountableFamilies

/-!
# Mises Church Example

Ville's example: a Mises-Church random sequence each prefix of which has at least as many zeros
as ones.  The main declarations are `exists_isMisesChurchRandom_zerosDominate` (Theorem 172 of
Shen, Uspensky and Vereshchagin) and its strict variant
`exists_isMisesChurchRandom_zerosStrictlyDominate`, obtained by prepending a zero.  The proof
combines the countability of the decidable selection rules with the balanced sequences constructed
for countable families of selection rules.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- The set of decidable sets of bit strings is countable. -/
private lemma exists_isMisesChurchRandom_zerosDominate_decidableSets_countable :
    ({R : Set BitString | IsDecidableSet R}).Countable := by
  have H1 : {R : Set BitString | IsDecidableSet R} ⊆ (fun (c : Nat.Partrec.Code) => 
      {x : BitString | ∃ n, c.eval (Encodable.encode x) = Part.some n ∧ n = Encodable.encode true})
          '' Set.univ := by
    intro R hR
    obtain ⟨f, hf, hfR⟩ := hR
    unfold Computable at hf
    unfold Partrec at hf
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
    use c
    refine ⟨Set.mem_univ c, ?_⟩
    ext x
    change (∃ n, c.eval (Encodable.encode x) = Part.some n ∧ n = Encodable.encode true) ↔ x ∈ R
    constructor
    · rintro ⟨n, hn1, hn2⟩
      apply (hfR x).mp
      have h3 : c.eval (Encodable.encode x) = Part.some (Encodable.encode (f x)) := by
        rw [hc]
        simp
      rw [h3] at hn1
      have hn1' : Encodable.encode (f x) = n := Part.some_inj.1 hn1
      rw [hn2] at hn1'
      exact Encodable.encode_injective hn1'
    · intro (hx : x ∈ R)
      have h1 : f x = true := (hfR x).mpr hx
      have h2 : c.eval (Encodable.encode x) = Part.some (Encodable.encode (f x)) := by
        rw [hc]
        simp
      rw [h1] at h2
      exact ⟨Encodable.encode true, h2, rfl⟩
  exact Set.Countable.mono H1 (Set.Countable.image Set.countable_univ _)

/-- **SUV Theorem 172 (Ville's example), p. 269.**  There is a Mises-Church random sequence each
prefix of which has at least as many zeros as ones. -/
theorem exists_isMisesChurchRandom_zerosDominate :
    ∃ w, IsMisesChurchRandom w ∧ ZerosDominate w := by
  have hUniv : IsDecidableSet (Set.univ : Set BitString) :=
    ⟨fun _ => true, Computable.const true, by simp⟩
  let D : Set (Set BitString) := {R | IsDecidableSet R}
  have hD : D.Countable := exists_isMisesChurchRandom_zerosDominate_decidableSets_countable
  obtain ⟨R, hRange⟩ := hD.exists_eq_range ⟨Set.univ, hUniv⟩
  obtain ⟨w, hbal, hzero⟩ := exists_countable_family_balanced R
  refine ⟨w, ?_, hzero⟩
  intro S hS
  have hSrange : S ∈ Set.range R := by
    rw [← hRange]
    exact hS
  obtain ⟨i, rfl⟩ := hSrange
  exact hbal i

private def exists_isMisesChurchRandom_zerosStrictlyDominate_prependFalse (w : CantorSeq) :
    CantorSeq
  | 0 => false
  | n + 1 => w n

/-- Step 1 of the proof of
exists_isMisesChurchRandom_zerosStrictlyDominate_MisesChurch: prepending false preserves
IsMisesChurchRandom. -/
private theorem exists_isMisesChurchRandom_zerosStrictlyDominate_selectedAux
    (R : Set BitString) (a : Bool) (pre x : BitString) :
    selectedAux R (a :: pre) x =
      selectedAux {y : BitString | a :: y ∈ R} pre x := by
  induction x generalizing pre with
  | nil => rfl
  | cons b x ih =>
    simp [selectedAux, ih]

open Classical in
/-- Step 2 of the proof of
exists_isMisesChurchRandom_zerosStrictlyDominate_MisesChurch: prepending false preserves
IsMisesChurchRandom. -/
private theorem exists_isMisesChurchRandom_zerosStrictlyDominate_selectChain
    (R : Set BitString) (w : CantorSeq) (t : ℕ) :
    selectChain R
        (exists_isMisesChurchRandom_zerosStrictlyDominate_prependFalse w) (t + 1) =
      (if [] ∈ R then [false] else []) ++
        selectChain {y : BitString | false :: y ∈ R} w t := by
  dsimp [selectChain, selectedBits]
  have h1 : cantorPrefix (exists_isMisesChurchRandom_zerosStrictlyDominate_prependFalse w) (t + 1) =
      false :: cantorPrefix w t := by
    change List.ofFn _ = _
    rw [List.ofFn_succ]
    rfl
  rw [h1]
  rw [selectedAux, List.nil_append]
  exact congrArg _
    (exists_isMisesChurchRandom_zerosStrictlyDominate_selectedAux R false [] (cantorPrefix w t))

/-- If the shifted terms of the chain `d` are the terms of the chain `c` with `s` in front, then
the stream of `d` is the stream of `c` with `s` in front. -/
private lemma exists_isMisesChurchRandom_zerosStrictlyDominate_selectStream_chain
    (c d : ℕ → BitString) (hc : ∀ t, c t <+: c (t + 1)) (hd : ∀ t, d t <+: d (t + 1))
    (s : BitString) (h : ∀ t, d (t + 1) = s ++ c t) :
    streamOfChain d hd = BitStream.prepend s (streamOfChain c hc) := by
  have hmemC : ∀ y, BitStream.finite y ≤ streamOfChain c hc ↔ ∃ t, y <+: c t := fun y =>
    BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet hc) y
  have hmemD : ∀ y, BitStream.finite y ≤ streamOfChain d hd ↔ ∃ t, y <+: d t := fun y =>
    BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet hd) y
  have hct : ∀ t, BitStream.finite (s ++ c t) ≤ BitStream.prepend s (streamOfChain c hc) :=
    fun t => BitStream.prepend_mono s ((hmemC (c t)).2 ⟨t, List.prefix_rfl⟩)
  apply BitStream.eq_of_forall_finite_le_iff
  intro y
  rw [hmemD]
  constructor
  · rintro ⟨t, hyt⟩
    have h1 : y <+: s ++ c t := by
      rw [← h t]
      exact hyt.trans (hd t)
    exact le_trans (show BitStream.finite y ≤ BitStream.finite (s ++ c t) from h1) (hct t)
  · intro hy
    suffices hex : ∃ t, y <+: s ++ c t by
      obtain ⟨t, ht⟩ := hex
      exact ⟨t + 1, by rw [h t]; exact ht⟩
    cases hS : streamOfChain c hc with
    | finite m =>
      rw [hS] at hy
      obtain ⟨t, hmt⟩ := (hmemC m).1 (le_of_eq hS.symm)
      exact ⟨t, (show y <+: s ++ m from hy).trans ((List.prefix_append_right_inj s).2 hmt)⟩
    | infinite u =>
      rw [hS] at hy
      have hu : BitStream.finite (cantorPrefix u y.length) ≤ streamOfChain c hc := by
        rw [hS]
        exact (isCantorPrefix_iff_cantorPrefix_eq (cantorPrefix u y.length) u).2 (by simp)
      obtain ⟨t, ht⟩ := (hmemC _).1 hu
      have h2 := hct t
      rw [hS] at h2
      have hy' : IsCantorPrefix y (prependCantor s u) := hy
      have h2' : IsCantorPrefix (s ++ c t) (prependCantor s u) := h2
      have hlen : y.length ≤ (s ++ c t).length := by
        have := ht.length_le
        simp only [cantorPrefix_length, List.length_append] at this ⊢
        omega
      refine ⟨t, ?_⟩
      have key := cantorPrefix_mono (prependCantor s u) hlen
      rwa [(isCantorPrefix_iff_cantorPrefix_eq _ _).1 hy',
        (isCantorPrefix_iff_cantorPrefix_eq _ _).1 h2'] at key

open Classical in
/-- Step 3 of the proof of
exists_isMisesChurchRandom_zerosStrictlyDominate_MisesChurch: prepending false preserves
IsMisesChurchRandom. -/
private theorem exists_isMisesChurchRandom_zerosStrictlyDominate_selectStream
    (R : Set BitString) (w : CantorSeq) :
    selectStream R
        (exists_isMisesChurchRandom_zerosStrictlyDominate_prependFalse w) =
      BitStream.prepend (if [] ∈ R then [false] else [])
        (selectStream {y : BitString | false :: y ∈ R} w) := by
  exact exists_isMisesChurchRandom_zerosStrictlyDominate_selectStream_chain
    (selectChain {y : BitString | false :: y ∈ R} w)
    (selectChain R (exists_isMisesChurchRandom_zerosStrictlyDominate_prependFalse w))
    (selectChain_prefix _ _) (selectChain_prefix _ _) _
    (exists_isMisesChurchRandom_zerosStrictlyDominate_selectChain R w)

/-- Step 4 of the proof of
exists_isMisesChurchRandom_zerosStrictlyDominate_MisesChurch: prepending false preserves
IsMisesChurchRandom. -/
private theorem exists_isMisesChurchRandom_zerosStrictlyDominate_prependCantor
    (p : ℝ) (s : BitString) (w : CantorSeq)
    (hw : HasLimitFreq p w) :
    HasLimitFreq p (prependCantor s w) := by
  dsimp [HasLimitFreq] at *
  have h1 : ∀ n, cantorPrefix (prependCantor s w) (n + s.length) = s ++ cantorPrefix w n := by
    intro n
    apply List.ext_get
    · simp; omega
    · intro i h1 h2
      change (cantorPrefix (prependCantor s w) (n + s.length))[i] = (s ++ cantorPrefix w n)[i]
      have H := cantorPrefix_getElem (prependCantor s w) (n + s.length) i h1
      rw [H]
      dsimp [prependCantor]
      split_ifs with hi
      · have H2 : (s ++ cantorPrefix w n)[i] = s[i] := by
          apply List.getElem_append_left
        rw [H2]
      · have hi2 : s.length ≤ i := by omega
        have hi3 : i - s.length < (cantorPrefix w n).length := by
          simp only [cantorPrefix_length] at h1 ⊢; omega
        have H2 : (s ++ cantorPrefix w n)[i] = (cantorPrefix w n)[i - s.length]'hi3 := by
          apply List.getElem_append_right hi2
        rw [H2]
        have H3 := cantorPrefix_getElem w n (i - s.length) hi3
        rw [H3]
  set c := s.length
  have h2 : ∀ n > 0, (freqOne (prependCantor s w) (n + c) : ℝ) =
      (s.count true : ℝ) / (n + c) + (freqOne w n : ℝ) * (n / (n + c)) := by
    intro n hn
    dsimp [freqOne]
    rw [h1 n]
    rw [List.count_append]
    push_cast
    have hn2 : (n : ℝ) ≠ 0 := by positivity
    calc
      _ = ((s.count true : ℝ) + (cantorPrefix w n).count true) / (n + c) := by rfl
      _ = (s.count true : ℝ) / (n + c) + ((cantorPrefix w n).count true : ℝ) / (n + c) := by ring
      _ = (s.count true : ℝ) / (n + c) + ((cantorPrefix w n).count true : ℝ) / n * (n / (n + c)) :=
          by
        congr 1
        have h3 : (cantorPrefix w n).count true / (n + c : ℝ) = (cantorPrefix w n).count true *
            (n + c : ℝ)⁻¹ := by rfl
        have h4 : ((cantorPrefix w n).count true : ℝ) / n * (n / (n + c)) =
            ((cantorPrefix w n).count true : ℝ) * (n : ℝ)⁻¹ * n * (n + c : ℝ)⁻¹ := by ring
        rw [h3, h4]
        have h5 : ((cantorPrefix w n).count true : ℝ) * (n : ℝ)⁻¹ * n * (n + c : ℝ)⁻¹ =
            ((cantorPrefix w n).count true : ℝ) * ((n : ℝ)⁻¹ * n) * (n + c : ℝ)⁻¹ := by ring
        rw [h5, inv_mul_cancel₀ hn2]
        ring
  apply (tendsto_add_atTop_iff_nat c).1
  have hinv : Tendsto (fun n : ℕ => ((n + c : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add] using
      (tendsto_add_atTop_iff_nat c).2 tendsto_inv_atTop_nhds_zero_nat
  have hterm1 : Tendsto (fun n : ℕ => (s.count true : ℝ) / (n + c)) atTop (𝓝 0) := by
    have h_c : (fun (n : ℕ) => (s.count true : ℝ) / (n + c : ℝ)) = fun (n : ℕ) =>
      (s.count true : ℝ) * ((n + c : ℕ) : ℝ)⁻¹ := by
      ext n; simp only [Nat.cast_add, div_eq_inv_mul]; ring
    rw [h_c]
    have h_zero : (0 : ℝ) = (s.count true : ℝ) * 0 := by ring
    rw [h_zero]
    exact Tendsto.const_mul (↑(List.count true s)) hinv
  have hterm2 : Tendsto (fun n : ℕ => (freqOne w n : ℝ) * (n / (n + c))) atTop (𝓝 p) := by
    have h_p : p = p * 1 := by ring
    rw [h_p]
    apply Tendsto.mul
    · exact hw
    · apply tendsto_natCast_div_add_atTop (c : ℝ)
  have h3 : Tendsto (fun (n : ℕ) => (s.count true : ℝ) / (n + c) + (freqOne w n : ℝ) *
                                      (n / (n + c))) atTop (𝓝 p) := by
    have h_p : p = 0 + p := by ring
    rw [h_p]
    exact Tendsto.add hterm1 hterm2
  have h_split : (fun n => (freqOne (prependCantor s w) (n + c) : ℝ)) =ᶠ[atTop]
      (fun n => (s.count true : ℝ) / (n + c) + (freqOne w n : ℝ) * (n / (n + c))) := by
    apply eventually_atTop.mpr
    use 1
    intro n hn
    exact h2 n hn
  exact (tendsto_congr' h_split).mpr h3

/-- Step 5 of the proof of
exists_isMisesChurchRandom_zerosStrictlyDominate_MisesChurch: prepending false preserves
IsMisesChurchRandom. -/
private theorem exists_isMisesChurchRandom_zerosStrictlyDominate_FiniteOrFreq
    (p : ℝ) (s : BitString) (u : BitStream)
    (hu : FiniteOrFreq p u) :
    FiniteOrFreq p (BitStream.prepend s u) := by
  cases u
  · exact trivial
  · dsimp [FiniteOrFreq, BitStream.prepend] at *
    exact exists_isMisesChurchRandom_zerosStrictlyDominate_prependCantor p s
        _ hu

/-- Step 6 of the proof of
exists_isMisesChurchRandom_zerosStrictlyDominate_MisesChurch: prepending false preserves
IsMisesChurchRandom. -/
private theorem exists_isMisesChurchRandom_zerosStrictlyDominate_isDecidableSet_preimage
    (R : Set BitString) (a : Bool) (hR : IsDecidableSet R) :
    IsDecidableSet {y : BitString | a :: y ∈ R} := by
  rcases hR with ⟨f, hf, hspec⟩
  exact ⟨fun y => f (a :: y),
    hf.comp (Computable.list_cons.comp (Computable.const a) Computable.id),
    fun y => hspec (a :: y)⟩

open Classical in
/-- Step 1 of the proof of exists_isMisesChurchRandom_zerosStrictlyDominate: prepending
false preserves IsMisesChurchRandom. -/
private lemma exists_isMisesChurchRandom_zerosStrictlyDominate_MisesChurch (w : CantorSeq)
    (hw : IsMisesChurchRandom w) :
    IsMisesChurchRandom (exists_isMisesChurchRandom_zerosStrictlyDominate_prependFalse w) := by
  intro R hR
  rw [exists_isMisesChurchRandom_zerosStrictlyDominate_selectStream]
  apply exists_isMisesChurchRandom_zerosStrictlyDominate_FiniteOrFreq
  apply hw
  exact exists_isMisesChurchRandom_zerosStrictlyDominate_isDecidableSet_preimage R false hR

/-- Step 2 of the proof of exists_isMisesChurchRandom_zerosStrictlyDominate: prepending
false to a sequence where zeros dominate yields one where zeros strictly dominate. -/
private lemma exists_isMisesChurchRandom_zerosStrictlyDominate_ZerosStrictlyDominate
    (w : CantorSeq) (hw : ZerosDominate w) :
    ZerosStrictlyDominate (exists_isMisesChurchRandom_zerosStrictlyDominate_prependFalse w) := by
  intro n hn
  cases n with
  | zero => contradiction
  | succ m =>
    have hw_m := hw m
    unfold onesCount zerosCount at hw_m ⊢
    unfold cantorPrefix at hw_m ⊢
    rw [List.ofFn_succ]
    change List.count true (false :: List.ofFn (fun i : Fin m => w i.val)) < List.count false
        (false :: List.ofFn (fun i : Fin m => w i.val))
    rw [List.count_cons, List.count_cons]
    simp
    omega

/-- **SUV p. 269, after Theorem 172.**  The strict version, obtained by starting with one more bit.
The book writes "first bit `1`"; the first bit has to be `0` for the zeros to lead, which is what is
stated here. -/
theorem exists_isMisesChurchRandom_zerosStrictlyDominate :
    ∃ w, IsMisesChurchRandom w ∧ ZerosStrictlyDominate w := by
  obtain ⟨w, hw, hz⟩ := exists_isMisesChurchRandom_zerosDominate
  exact ⟨exists_isMisesChurchRandom_zerosStrictlyDominate_prependFalse w,
      exists_isMisesChurchRandom_zerosStrictlyDominate_MisesChurch w hw,
      exists_isMisesChurchRandom_zerosStrictlyDominate_ZerosStrictlyDominate w hz⟩

end Kolmogorov.FrequencyGames
