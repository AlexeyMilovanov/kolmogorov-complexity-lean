import KolmogorovMathlib.CommonInformation.FixedHistogramRank
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Fibre complexity with the histogram carried by the program

`condK_fixedHistogramWord_given_projection_le` bounds the complexity of a
fixed-histogram word given *both* its first-coordinate projection *and* the
histogram table.  For the fixed-frequency argument the histogram must not sit
in the condition: only the projection may.  This file pays for the histogram
inside the program instead.

The decoder reads the two alphabet sizes `m`, `n` and the `m * n` histogram
entries from a self-delimiting parameter block at the front of the program,
rebuilds the numeric histogram table in lexicographic order, and then selects
the required word from the fibre over the projection by a fixed-width rank.
The resulting bound is

`K(w | w₁) ≤ log₂ ∏_a M(f(a, ·)) + 2 log₂ m + 2 log₂ n + 2 ∑_{ab} log₂ f(ab) + m n + O(1)`.
-/

namespace Kolmogorov

open Finset

noncomputable section

/-! ### Permutation invariance of the numeric enumerations -/

theorem allWordsFrom_perm {A : Type*} {s t : List A} (h : s.Perm t) (k : ℕ) :
    (allWordsFrom s k).Perm (allWordsFrom t k) := by
  induction k with
  | zero => exact List.Perm.refl _
  | succ k ih =>
      change (s.flatMap fun a => (allWordsFrom s k).map (a :: ·)).Perm
        (t.flatMap fun a => (allWordsFrom t k).map (a :: ·))
      exact h.flatMap fun a _ => ih.map _

theorem numericFixedHistogramWords_perm {T₁ T₂ : List (ℕ × ℕ)} (h : T₁.Perm T₂) :
    (numericFixedHistogramWords T₁).Perm (numericFixedHistogramWords T₂) := by
  have hpred : (fun w : List ℕ => decide (∀ e ∈ T₁, w.count e.1 = e.2)) =
      fun w : List ℕ => decide (∀ e ∈ T₂, w.count e.1 = e.2) := by
    funext w
    refine decide_eq_decide.mpr ⟨fun hw e he => hw e (h.mem_iff.mpr he),
      fun hw e he => hw e (h.mem_iff.mp he)⟩
  unfold numericFixedHistogramWords
  rw [hpred, (h.map Prod.snd).sum_eq]
  exact (allWordsFrom_perm (h.map Prod.fst) _).filter _

theorem numericFixedHistogramFiberWords_perm (projection : List ℕ)
    {T₁ T₂ : List (ℕ × ℕ)} (h : T₁.Perm T₂) :
    (numericFixedHistogramFiberWords projection T₁).Perm
      (numericFixedHistogramFiberWords projection T₂) :=
  (numericFixedHistogramWords_perm h).filter _

/-! ### The lexicographic product histogram table -/

/-- The histogram table of `f : Fin m × Fin n → ℕ`, listed in the flat
lexicographic order used by the parameter block of the decoder. -/
def prodHistogramTable (m n : ℕ) (f : Fin m × Fin n → ℕ) : List (ℕ × ℕ) :=
  List.ofFn fun j : Fin (m * n) =>
    (FiniteLetterCode.encode (finProdFinEquiv.symm j), f (finProdFinEquiv.symm j))

theorem prodHistogramTable_perm (m n : ℕ) (f : Fin m × Fin n → ℕ) :
    (prodHistogramTable m n f).Perm
      ((univ : Finset (Fin m × Fin n)).toList.map
        fun ab => (FiniteLetterCode.encode ab, f ab)) := by
  have hnodup : (List.ofFn (fun j : Fin (m * n) => finProdFinEquiv.symm j)).Nodup :=
    List.nodup_ofFn.mpr (Equiv.injective _)
  have htoFinset :
      (List.ofFn (fun j : Fin (m * n) => finProdFinEquiv.symm j)).toFinset =
        (univ : Finset (Fin m × Fin n)).toList.toFinset := by
    ext ab
    simp only [List.mem_toFinset, List.mem_ofFn, Finset.mem_toList, Finset.mem_univ,
      iff_true]
    exact ⟨finProdFinEquiv ab, by simp⟩
  have hperm := List.perm_of_nodup_nodup_toFinset_eq hnodup
    (Finset.nodup_toList _) htoFinset
  have hmap : prodHistogramTable m n f =
      (List.ofFn fun j : Fin (m * n) => finProdFinEquiv.symm j).map
        (fun ab => (FiniteLetterCode.encode ab, f ab)) := by
    rw [List.map_ofFn]
    rfl
  rw [hmap]
  exact hperm.map _

/-! ### The decoder -/

/-- Re-tag a flat parameter block as a product histogram table. -/
def prodTableOfTagged (n : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l.map fun e => (Nat.pair (e.1 / n) (e.1 % n), e.2)

/-- The parser state after reading the whole parameter block of a program. -/
def prodParamState (p : BitString) : (List (ℕ × ℕ) × BitString) × ℕ :=
  peelIter (bitsToNat (decodeFirst p) * bitsToNat (decodeFirst (decodeSecond p)))
    ((([] : List (ℕ × ℕ)), decodeSecond (decodeSecond p)), 0)

/-- The product histogram table carried by the parameter block of a program. -/
def prodParamTable (p : BitString) : List (ℕ × ℕ) :=
  prodTableOfTagged (bitsToNat (decodeFirst (decodeSecond p))) (prodParamState p).1.1

/-- The decoder of this file: the program carries the two alphabet sizes, the
histogram entries and a fixed-width rank; the condition carries only the
first-coordinate projection of the word. -/
def fixedHistogramProdLiftDecoder : Map := fun pr =>
  Part.some
    (((numericFixedHistogramFiberWords (decodeFiniteWordCode pr.2)
        (prodParamTable pr.1)).map numericWordCode).getD
      (decodeFixedWidthNatCode (prodParamState pr.1).1.2) [])

theorem prodTableOfTagged_primrec :
    Primrec (fun p : ℕ × List (ℕ × ℕ) => prodTableOfTagged p.1 p.2) := by
  unfold prodTableOfTagged
  refine Primrec.list_map Primrec.snd ?_
  have hn : Primrec (fun r : (ℕ × List (ℕ × ℕ)) × (ℕ × ℕ) => r.1.1) :=
    Primrec.fst.comp Primrec.fst
  have he1 : Primrec (fun r : (ℕ × List (ℕ × ℕ)) × (ℕ × ℕ) => r.2.1) :=
    Primrec.fst.comp Primrec.snd
  have he2 : Primrec (fun r : (ℕ × List (ℕ × ℕ)) × (ℕ × ℕ) => r.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (Primrec.pair
    (Primrec₂.natPair.comp (Primrec.nat_div.comp he1 hn) (Primrec.nat_mod.comp he1 hn))
    he2).to₂

theorem prodParamState_primrec : Primrec prodParamState := by
  have hm : Primrec (fun p : BitString => bitsToNat (decodeFirst p)) :=
    bitsToNat_primrec.comp CodedFiniteDistribution.decodeFirst_primrec
  have hrest : Primrec (fun p : BitString => decodeSecond p) :=
    CodedFiniteDistribution.decodeSecond_primrec
  have hn : Primrec (fun p : BitString => bitsToNat (decodeFirst (decodeSecond p))) :=
    bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp hrest)
  have hcount : Primrec (fun p : BitString =>
      bitsToNat (decodeFirst p) * bitsToNat (decodeFirst (decodeSecond p))) :=
    Primrec.nat_mul.comp hm hn
  unfold prodParamState
  refine Primrec.nat_rec' (α := BitString) (β := (List (ℕ × ℕ) × BitString) × ℕ)
    (h := fun _ q => peelStep q.2) hcount
    (Primrec.pair (Primrec.pair (Primrec.const ([] : List (ℕ × ℕ)))
      (CodedFiniteDistribution.decodeSecond_primrec.comp hrest)) (Primrec.const 0))
    ?_
  exact (peelStep_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂

theorem prodParamTable_primrec : Primrec prodParamTable := by
  have hn : Primrec (fun p : BitString => bitsToNat (decodeFirst (decodeSecond p))) :=
    bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp
      CodedFiniteDistribution.decodeSecond_primrec)
  exact prodTableOfTagged_primrec.comp
    (Primrec.pair hn (Primrec.fst.comp (Primrec.fst.comp prodParamState_primrec)))

theorem fixedHistogramProdLiftDecoder_isDecompressor :
    isDecompressor fixedHistogramProdLiftDecoder := by
  have hlist : Primrec (fun pr : BitString × BitString =>
      (numericFixedHistogramFiberWords (decodeFiniteWordCode pr.2)
        (prodParamTable pr.1)).map numericWordCode) :=
    Primrec.list_map
      (numericFixedHistogramFiberWords_primrec.comp
        (Primrec.pair (decodeFiniteWordCode_primrec.comp Primrec.snd)
          (prodParamTable_primrec.comp Primrec.fst)))
      (numericWordCode_primrec.comp Primrec.snd).to₂
  have hidx : Primrec (fun pr : BitString × BitString =>
      decodeFixedWidthNatCode (prodParamState pr.1).1.2) :=
    decodeFixedWidthNatCode_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp (prodParamState_primrec.comp Primrec.fst)))
  exact (((Primrec.list_getD ([] : BitString)).comp hlist hidx).to_comp).partrec

/-! ### Fibre lemmas for an arbitrary letter code

The corresponding lemmas of `FixedHistogramRank` are stated for the letter code
that a finite type carries by default.  The alphabets `Fin m` and `Fin m × Fin n`
carry explicit executable codes instead, so the fibre lemmas are repeated here
with the letter codes as parameters. -/

section GeneralLetterCode

variable {A B : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A]
  [Fintype B] [DecidableEq B] [FiniteLetterCode B]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem map_encode_unpair_fst_gen (v : List (A × B)) :
    (v.map FiniteLetterCode.encode).map (fun code : ℕ => code.unpair.1) =
      (v.map Prod.fst).map (FiniteLetterCode.encode : A → ℕ) := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left ?_
  rintro ⟨a, b⟩ -
  simp [finiteLetterCode_encode_prod]

theorem mem_numericFiber_gen (f : A × B → ℕ) (w_A : List A) (w' : List ℕ) :
    w' ∈ numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode)
        (Finset.univ.toList.map (fun ab : A × B => (FiniteLetterCode.encode ab, f ab))) ↔
      ∃ v : List (A × B), ((∀ i, v.count i = f i) ∧ v.map Prod.fst = w_A) ∧
        w' = v.map FiniteLetterCode.encode := by
  rw [numericFixedHistogramFiberWords, List.mem_filter,
    mem_numericFixedHistogramWords_general]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hproj⟩
    rw [map_encode_unpair_fst_gen] at hproj
    exact ⟨v, ⟨hv, List.map_injective_iff.mpr FiniteLetterCode.injective hproj⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hmap⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, by rw [map_encode_unpair_fst_gen, hmap]⟩

omit [DecidableEq A] [DecidableEq B] in
theorem numericFiber_nodup_gen (f : A × B → ℕ) (w_A : List A) :
    (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode)
      (Finset.univ.toList.map
        (fun ab : A × B => (FiniteLetterCode.encode ab, f ab)))).Nodup :=
  (numericGeneral_nodup f).filter _

omit [DecidableEq B] in
theorem length_numericFiber_gen (f : A × B → ℕ) (w_A : List A)
    (hmargin : ∀ a, w_A.count a = ∑ b, f (a, b)) :
    (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode)
      (Finset.univ.toList.map
        (fun ab : A × B => (FiniteLetterCode.encode ab, f ab)))).length =
      ∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b)) := by
  classical
  have hmapnodup :
      ((fixedHistogramFiberWords w_A f).map
        (fun v => v.map (FiniteLetterCode.encode : A × B → ℕ))).Nodup :=
    (fixedHistogramLiftWords_nodup w_A f).map (by
      intro u v huv
      exact List.map_injective_iff.mpr FiniteLetterCode.injective huv)
  have htoFinset :
      (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode)
        (Finset.univ.toList.map
          (fun ab : A × B => (FiniteLetterCode.encode ab, f ab)))).toFinset =
        ((fixedHistogramFiberWords w_A f).map
          (fun v => v.map (FiniteLetterCode.encode : A × B → ℕ))).toFinset := by
    ext w'
    simp only [List.mem_toFinset, mem_numericFiber_gen, List.mem_map,
      mem_fixedHistogramLiftWords]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
  rw [← List.toFinset_card_of_nodup (numericFiber_nodup_gen f w_A), htoFinset,
    List.toFinset_card_of_nodup hmapnodup, List.length_map,
    length_fixedHistogramFiberWords w_A f hmargin]

end GeneralLetterCode

theorem prodTableOfTagged_taggedFrom (m n : ℕ) (f : Fin m × Fin n → ℕ) :
    prodTableOfTagged n
        (taggedFrom 0 (List.ofFn fun j : Fin (m * n) => f (finProdFinEquiv.symm j))) =
      prodHistogramTable m n f := by
  rw [taggedFrom_ofFn, prodTableOfTagged, List.map_map, prodHistogramTable,
    List.ofFn_eq_map]
  refine List.map_congr_left ?_
  intro j _
  have hcode : FiniteLetterCode.encode (finProdFinEquiv.symm j) =
      Nat.pair (j.val / n) (j.val % n) := rfl
  simp only [Function.comp_apply, hcode]
  rfl

theorem sum_natsCode_lengths (m n : ℕ) (f : Fin m × Fin n → ℕ) :
    (((List.ofFn fun j : Fin (m * n) => f (finProdFinEquiv.symm j)).map
        fun x => 2 * Nat.size x + 1).sum) = 2 * (∑ ab, Nat.size (f ab)) + m * n := by
  rw [List.map_ofFn, List.sum_ofFn]
  have hsum : ∑ j : Fin (m * n),
      ((fun x => 2 * Nat.size x + 1) ∘ fun j : Fin (m * n) => f (finProdFinEquiv.symm j)) j =
      ∑ j : Fin (m * n), (2 * Nat.size (f (finProdFinEquiv.symm j)) + 1) := rfl
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hequiv : ∑ j : Fin (m * n), Nat.size (f (finProdFinEquiv.symm j)) =
      ∑ ab, Nat.size (f ab) :=
    Fintype.sum_equiv finProdFinEquiv.symm _ _ fun _ => rfl
  rw [hequiv]
  simp

theorem fixedHistogramProdLiftDecoder_recovers
    (m n : ℕ) (f : Fin m × Fin n → ℕ) (w : List (Fin m × Fin n))
    (hw : ∀ ab, w.count ab = f ab) :
    ∃ p, p.length ≤
        Nat.size (∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b))) +
          2 * Nat.size m + 2 * Nat.size n + 2 * (∑ ab, Nat.size (f ab)) + m * n + 2 ∧
      produces fixedHistogramProdLiftDecoder p
        (finiteWordCode (w.map Prod.fst)) (finiteWordCode w) := by
  classical
  set w_A := w.map Prod.fst with hw_A
  have hmargin : ∀ a, w_A.count a = ∑ b, f (a, b) := by
    intro a
    rw [hw_A, count_map_fst_eq_sum]
    exact Finset.sum_congr rfl fun b _ => hw (a, b)
  set T1 := (univ : Finset (Fin m × Fin n)).toList.map
    (fun ab => (FiniteLetterCode.encode ab, f ab)) with hT1
  set T2 := prodHistogramTable m n f with hT2
  have hperm : T2.Perm T1 := prodHistogramTable_perm m n f
  have hfperm :
      (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode) T2).Perm
        (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode) T1) :=
    numericFixedHistogramFiberWords_perm _ hperm
  set L := (numericFixedHistogramFiberWords (w_A.map FiniteLetterCode.encode) T2).map
    numericWordCode with hL
  have hmem : finiteWordCode w ∈ L := by
    rw [hL, List.mem_map]
    refine ⟨w.map FiniteLetterCode.encode, hfperm.mem_iff.mpr ?_, rfl⟩
    rw [hT1]
    exact (mem_numericFiber_gen f w_A _).mpr ⟨w, ⟨hw, rfl⟩, rfl⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hlenL : L.length = ∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b)) := by
    rw [hL, List.length_map, hfperm.length_eq, hT1,
      length_numericFiber_gen f w_A hmargin]
  set width := Nat.size (∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b))) with hwidth
  have hi_lt : i < 2 ^ width := by
    have h1 : i < ∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b)) := by
      rw [← hlenL]; exact hi
    exact lt_trans h1 (Nat.lt_size_self _)
  set xs := List.ofFn fun j : Fin (m * n) => f (finProdFinEquiv.symm j) with hxs
  set tail := fixedWidthNatCode i width with htail
  set p : BitString := pairCode (Nat.bits m) (pairCode (Nat.bits n) (natsCode xs tail))
    with hp
  have hplen : p.length =
      width + 2 * Nat.size m + 2 * Nat.size n + 2 * (∑ ab, Nat.size (f ab)) + m * n + 2 := by
    rw [hp, length_pairCode, length_pairCode, length_natsCode, hxs, sum_natsCode_lengths,
      htail, fixedWidthNatCode_length hi_lt, Nat.size_eq_bits_len, Nat.size_eq_bits_len]
    omega
  refine ⟨p, le_of_eq hplen, ?_⟩
  have hlen_xs : xs.length = m * n := by rw [hxs, List.length_ofFn]
  have hstate : prodParamState p = ((taggedFrom 0 xs, tail), 0 + xs.length) := by
    have h := peelIter_natsCode xs [] 0 tail
    unfold prodParamState
    rw [hp]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    rw [← hlen_xs]
    simpa using h
  have htable : prodParamTable p = T2 := by
    unfold prodParamTable
    rw [hstate, hp]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    rw [hT2, hxs]
    exact prodTableOfTagged_taggedFrom m n f
  change finiteWordCode w ∈ fixedHistogramProdLiftDecoder (p, finiteWordCode w_A)
  unfold fixedHistogramProdLiftDecoder
  rw [Part.mem_some_iff, htable, hstate]
  simp only [decodeFiniteWordCode_finiteWordCode, htail, decodeFixedWidthNatCode_encode]
  rw [← hL, List.getD_eq_getElem _ _ hi, hget]

/-- **Fibre complexity with the histogram in the program.** -/
theorem condK_fixedHistogramWord_given_projection_le_add_params
    (U : Map) (hU : isOptimalConditional U) :
    ∃ C : ℕ, ∀ m n (f : Fin m × Fin n → ℕ) (w : List (Fin m × Fin n)),
      (∀ ab, w.count ab = f ab) →
      condK U (finiteWordCode w) (finiteWordCode (w.map Prod.fst)) ≤
        ((Nat.size (∏ a ∈ Finset.univ,
            Nat.multinomial Finset.univ (fun b => f (a, b))) +
          2 * Nat.size m + 2 * Nat.size n +
          2 * (∑ ab, Nat.size (f ab)) + m * n + C : ℕ) : ENat) := by
  obtain ⟨c, hc⟩ :=
    hU.2 fixedHistogramProdLiftDecoder fixedHistogramProdLiftDecoder_isDecompressor
  refine ⟨c + 2, fun m n f w hw => ?_⟩
  obtain ⟨p, hplen, hprod⟩ := fixedHistogramProdLiftDecoder_recovers m n f w hw
  set y := finiteWordCode (w.map Prod.fst) with hy
  have hD : condK fixedHistogramProdLiftDecoder (finiteWordCode w) y ≤ (p.length : ENat) :=
    sInf_le ⟨p, hprod, rfl⟩
  calc
    condK U (finiteWordCode w) y ≤
        condK fixedHistogramProdLiftDecoder (finiteWordCode w) y + (c : ENat) := hc _ _
    _ ≤ (p.length : ENat) + (c : ENat) := by gcongr
    _ ≤ ((Nat.size (∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b))) +
          2 * Nat.size m + 2 * Nat.size n + 2 * (∑ ab, Nat.size (f ab)) + m * n + 2 + c : ℕ)
            : ENat) := by
        exact_mod_cast Nat.add_le_add_right hplen c
    _ = ((Nat.size (∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b))) +
          2 * Nat.size m + 2 * Nat.size n + 2 * (∑ ab, Nat.size (f ab)) + m * n + (c + 2) : ℕ)
            : ENat) := by
        norm_cast
        omega

end

end Kolmogorov
