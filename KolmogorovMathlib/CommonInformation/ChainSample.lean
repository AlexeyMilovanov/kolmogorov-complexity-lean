import KolmogorovMathlib.CommonInformation.ChainFibre
import KolmogorovMathlib.CommonInformation.MaximalSampleFibre
import KolmogorovMathlib.CommonInformation.ChainWitness
import KolmogorovMathlib.CommonInformation.FixedHistogramRank
import KolmogorovMathlib.CommonInformation.FixedHistogramProjectionParams
import KolmogorovMathlib.CommonInformation.PlainCoding

/-!
# One maximal sample of a conditional-independence chain

This file develops the "single maximally complex full-chain sample" layer for
SUV Exercise 316 (strategy Iteration 2).  A `ChainDist` with rational atoms and
`Q ∣ N` has an exact natural-number histogram `chainHistogram`; a sample word
`W : List (Fin (2*k+2) → Bool)` *realises* that histogram when every atom `v`
occurs exactly `chainHistogram D hQ N v` times.

The key discipline (see the strategy risks) is that **every** projection profile
must refer to the *same* maximal sample `W`.  The projection primitives
`chainWordAt`/`chainPairAt`/`chainTripleAt` and the structure
`IsMaximalChainSample` fix that sample once and for all.

The count lemmas below convert the atom-level realisation hypothesis into the
one-, two-, and three-coordinate empirical counts, matching
`chainHistogram1`/`chainHistogram2`/`chainHistogram3`.  They all follow from one
general list identity, `count_map_eq_sum_count`.
-/

namespace Kolmogorov
open Finset

/-- The `j`-th coordinate projection of a chain sample, as a plain bit word. -/
def chainWordAt {k : ℕ} (W : List (Fin (2 * k + 2) → Bool)) (j : Fin (2 * k + 2)) :
    List Bool :=
  W.map (· j)

/-- The paired coordinate code of a chain sample (coding primitive for later
projection-complexity bounds; the empirical *joint count* is
`chainWordAt_pair_count`, phrased on the aligned projection instead). -/
def chainPairAt {k : ℕ} (W : List (Fin (2 * k + 2) → Bool)) (i j : Fin (2 * k + 2)) :
    List Bool :=
  pairCode (chainWordAt W i) (chainWordAt W j)

/-- The tripled coordinate code of a chain sample. -/
def chainTripleAt {k : ℕ} (W : List (Fin (2 * k + 2) → Bool)) (i j l : Fin (2 * k + 2)) :
    List Bool :=
  pairCode (chainPairAt W i j) (chainWordAt W l)

/-- Explicit numbering of the aligned two-bit projection alphabet. -/
def chainPairAlphabetEquiv : Bool × Bool ≃ Fin 4 :=
  (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans finProdFinEquiv

/-- Explicit numbering of the aligned three-bit projection alphabet. -/
def chainTripleAlphabetEquiv : (Bool × Bool) × Bool ≃ Fin 8 :=
  (Equiv.prodCongr chainPairAlphabetEquiv finTwoEquiv.symm).trans finProdFinEquiv

/-- The explicit binary-numbering equivalence for full chain atoms. -/
def chainAlphabetEquiv {k : ℕ} :
    (Fin (2 * k + 2) → Bool) ≃ Fin (2 ^ (2 * k + 2)) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Full chain atoms are numbered by their explicit binary value. -/
instance chainAlphabetCode {k : ℕ} : FiniteLetterCode (Fin (2 * k + 2) → Bool) where
  encode v := (@chainAlphabetEquiv k v).val
  injective := by
    intro a b hab
    apply (@chainAlphabetEquiv k).injective
    exact Fin.ext hab

/-- Reindexing a numeric chain word preserves its list of letter codes. -/
theorem chainAlphabet_encode_reindex {k : ℕ} (w_m : List (Fin (2 ^ (2 * k + 2)))) :
    (w_m.map (@chainAlphabetEquiv k).symm).map FiniteLetterCode.encode =
      w_m.map FiniteLetterCode.encode := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  dsimp [FiniteLetterCode.encode]
  rw [Equiv.apply_symm_apply]

/-- One maximally complex sample of the chain's full joint type.

* `counts` : `W` realises the exact `N`-sample histogram of the chain;
* `value`  : the coded full word has an exact finite plain-complexity value `kW`;
* `maximal`: `W` is (within one bit) as complex as the multinomial type-log
  allows, i.e. it is a maximal-complexity representative of its type. -/
structure IsMaximalChainSample {k : ℕ} (V : Map) (D : ChainDist k) {Q : ℕ}
    (hQ : D.RationalAtoms Q) (N : ℕ) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ) : Prop where
  counts  : ∀ v, W.count v = chainHistogram D hQ N v
  value   : HasPlainComplexityValue V (finiteWordCode W) kW
  maximal : (histogramTypeLog (chainHistogram D hQ N) : ENat) ≤ (kW : ENat) + 1

/-- A chain sample realizing the exact histogram has the requested sample
length. -/
theorem IsMaximalChainSample.length_eq {k Q N kW : ℕ} {V : Map}
    {D : ChainDist k} {hQ : D.RationalAtoms Q}
    {W : List (Fin (2 * k + 2) → Bool)}
    (h : IsMaximalChainSample V D hQ N W kW) (hdiv : Q ∣ N) : W.length = N := by
  rw [length_eq_sum_count_fintype]
  calc
    ∑ v, W.count v = ∑ v, chainHistogram D hQ N v :=
      Finset.sum_congr rfl (fun v _ => h.counts v)
    _ = N := chainHistogram_total D hQ N hdiv

/-- If every entry of a finite histogram is bounded by `N`, the sum of their
binary sizes is bounded by the alphabet cardinality times `Nat.size N`. -/
theorem sum_size_le_card_mul_size {ι : Type*} [Fintype ι]
    (f : ι → ℕ) (N : ℕ) (h : ∀ i, f i ≤ N) :
    ∑ i, Nat.size (f i) ≤ Fintype.card ι * Nat.size N := by
  calc
    ∑ i, Nat.size (f i) ≤ ∑ _i : ι, Nat.size N :=
      Finset.sum_le_sum (fun i _ => Nat.size_le_size (h i))
    _ = Fintype.card ι * Nat.size N := by simp

/-- Every atom count in an exact chain histogram is bounded by the sample
length. -/
theorem chainHistogram_entry_le {k Q N : ℕ} (D : ChainDist k)
    (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N)
    (v : Fin (2 * k + 2) → Bool) : chainHistogram D hQ N v ≤ N := by
  calc
    chainHistogram D hQ N v ≤ ∑ u, chainHistogram D hQ N u := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    _ = N := chainHistogram_total D hQ N _hdiv

/-- The total parameter-table size for a full chain histogram is logarithmic
in `N`, with a coefficient depending only on the chain length. -/
theorem sum_size_chainHistogram_le {k Q N : ℕ} (D : ChainDist k)
    (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N) :
    ∑ v, Nat.size (chainHistogram D hQ N v) ≤
      2 ^ (2 * k + 2) * Nat.size N := by
  calc
    ∑ v, Nat.size (chainHistogram D hQ N v) ≤
        Fintype.card (Fin (2 * k + 2) → Bool) * Nat.size N :=
      sum_size_le_card_mul_size _ _ (chainHistogram_entry_le D hQ _hdiv)
    _ = 2 ^ (2 * k + 2) * Nat.size N := by simp

/-- General projected-count identity: counting the target `b` among the
`f`-images of a list equals the total multiplicity of atoms mapping to `b`.
Stated over an ambient `BEq`/`LawfulBEq` on the target type so the `List.count`
instance matches product targets (`Bool × Bool`, `(Bool × Bool) × Bool`). -/
theorem count_map_eq_sum_count {α β : Type*} [Fintype α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β]
    (W : List α) (f : α → β) (b : β) :
    (W.map f).count b = ∑ v : α, if f v = b then W.count v else 0 := by
  induction W with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.count_cons, ih]
    have hexpand : ∀ v : α, (if f v = b then (a :: t).count v else 0)
        = (if f v = b then t.count v else 0)
          + (if v = a then (if f a = b then 1 else 0) else 0) := by
      intro v
      rw [List.count_cons]
      by_cases hv : v = a
      · subst hv; by_cases hfa : f v = b <;> simp [hfa]
      · simp [hv, Ne.symm hv]
    rw [Finset.sum_congr rfl (fun v _ => hexpand v), Finset.sum_add_distrib,
        Finset.sum_ite_eq' univ a (fun _ => if f a = b then 1 else 0)]
    simp [beq_iff_eq]

/-- Selecting one maximally complex sample of the full chain type.

The sample realises the exact histogram, has an exact plain-complexity value,
and is within one bit of the multinomial type-log.  Existence combines the
histogram realisability (total mass `N` when `Q ∣ N`) with the incompressibility
enumeration `exists_fixedHistogramWord_condK_gt`. -/
theorem exists_maximal_chainSample {k : ℕ} (V : Map) (hV : isOptimalConditional V)
    (D : ChainDist k) {Q : ℕ} (hQ : D.RationalAtoms Q) (N : ℕ) (_hdiv : Q ∣ N) :
    ∃ W kW, IsMaximalChainSample V D hQ N W kW := by
  let f := chainHistogram D hQ N
  let m := 2 ^ (2 * k + 2)
  let e := @chainAlphabetEquiv k
  let f_m : Fin m → ℕ := f ∘ e.symm
  have hpos : 0 < Nat.multinomial Finset.univ f := by
    have hspec := (Nat.multinomial_spec Finset.univ f).symm
    have hfact := Nat.factorial_pos (∑ x, f x)
    rw [hspec] at hfact
    cases Nat.eq_zero_or_pos (Nat.multinomial Finset.univ f) with
    | inl h0 => rw [h0, mul_zero] at hfact; contradiction
    | inr hp => exact hp
  by_cases h_multi : 2 ≤ Nat.multinomial Finset.univ f
  · let k_val := (histogramTypeLog f) - 2
    have hcard_m : 2 ^ (k_val + 1) ≤ Nat.multinomial Finset.univ f_m := by
      have he : Nat.multinomial Finset.univ f_m = Nat.multinomial Finset.univ f := by
        exact multinomial_comp_equiv e.symm f
      rw [he]
      have h1 : k_val + 1 = (histogramTypeLog f) - 1 := by
        have hlog : 2 ≤ histogramTypeLog f := by
          unfold histogramTypeLog
          have h5 := Nat.size_pos.mpr hpos
          have : ¬ (Nat.multinomial Finset.univ f < 2 ^ 1) := by intro h; omega
          have h6 := mt Nat.size_le.mp this
          omega
        omega
      rw [h1]
      unfold histogramTypeLog
      exact size_pred_pow_le h_multi
    obtain ⟨w_m, hw_m_count, hw_m_K⟩ :=
      exists_fixedHistogramWord_condK_gt V [] m f_m k_val hcard_m
    let W := w_m.map e.symm
    have hw_count : ∀ v, W.count v = f v := by
      intro v
      have hmap := List.count_map_of_injective w_m e.symm e.symm.injective (e v)
      rw [Equiv.symm_apply_apply] at hmap
      have h_eq_f : f_m (e v) = f v := by
        dsimp [f_m]
        rw [Equiv.symm_apply_apply]
      rw [hmap, hw_m_count (e v), h_eq_f]
    have heq : finiteWordCode W = finiteWordCode w_m := by
      unfold finiteWordCode
      congr 2
      exact chainAlphabet_encode_reindex w_m
    obtain ⟨c, hc⟩ := plainK_fixedHistogramWord_le_size_multinomial_add_params V hV
    have h_bound2 := hc m f_m w_m hw_m_count
    have hfin : plainK V (finiteWordCode w_m) ≠ ⊤ := by
      exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h_bound2
    obtain ⟨kW, hkW⟩ : ∃ kW : ℕ,
        (kW : ENat) = plainK V (finiteWordCode w_m) := by
      exact ENat.ne_top_iff_exists.mp hfin
    refine ⟨W, kW, hw_count, ?_, ?_⟩
    · dsimp [HasPlainComplexityValue]
      rw [heq]
      exact hkW.symm
    · have hk_val : (k_val : ENat) < (kW : ENat) := by
        rw [hkW]
        exact hw_m_K
      have h_le : k_val + 1 ≤ kW := by
        have hk_val2 : k_val < kW := ENat.coe_lt_coe.mp hk_val
        omega
      have h_log : histogramTypeLog f ≤ kW + 1 := by
        have hlog : 2 ≤ histogramTypeLog f := by
          unfold histogramTypeLog
          have h5 := Nat.size_pos.mpr hpos
          have : ¬ (Nat.multinomial Finset.univ f < 2 ^ 1) := by intro h; omega
          have h6 := mt Nat.size_le.mp this
          omega
        omega
      exact ENat.coe_le_coe.mpr h_log
  · have h_multi_eq : Nat.multinomial Finset.univ f = 1 := by omega
    have he : Nat.multinomial Finset.univ f_m = Nat.multinomial Finset.univ f := by
      exact multinomial_comp_equiv e.symm f
    have h_len : (fixedHistogramWords f_m).length = 1 := by
      rw [length_fixedHistogramWords f_m]
      omega
    have h_not_empty : (fixedHistogramWords f_m) ≠ [] := by
      intro h_nil
      rw [h_nil] at h_len
      contradiction
    let w_m := (fixedHistogramWords f_m).head h_not_empty
    have hw_m_mem : w_m ∈ fixedHistogramWords f_m := List.head_mem h_not_empty
    have hw_m_count : ∀ i, w_m.count i = f_m i := by
      have := (mem_fixedHistogramWords f_m w_m).mp hw_m_mem
      exact this.2
    let W := w_m.map e.symm
    have hw_count : ∀ v, W.count v = f v := by
      intro v
      have hmap := List.count_map_of_injective w_m e.symm e.symm.injective (e v)
      rw [Equiv.symm_apply_apply] at hmap
      have h_eq_f : f_m (e v) = f v := by
        dsimp [f_m]
        rw [Equiv.symm_apply_apply]
      rw [hmap, hw_m_count (e v), h_eq_f]
    have heq : finiteWordCode W = finiteWordCode w_m := by
      unfold finiteWordCode
      congr 2
      exact chainAlphabet_encode_reindex w_m
    obtain ⟨c, hc⟩ := plainK_fixedHistogramWord_le_size_multinomial_add_params V hV
    have h_bound2 := hc m f_m w_m hw_m_count
    have hfin : plainK V (finiteWordCode w_m) ≠ ⊤ := by
      exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h_bound2
    obtain ⟨kW, hkW⟩ : ∃ kW : ℕ,
        (kW : ENat) = plainK V (finiteWordCode w_m) := by
      exact ENat.ne_top_iff_exists.mp hfin
    refine ⟨W, kW, hw_count, ?_, ?_⟩
    · dsimp [HasPlainComplexityValue]
      rw [heq]
      exact hkW.symm
    · have h_log : histogramTypeLog f = 1 := by
        unfold histogramTypeLog
        have h_size : Nat.size (Nat.multinomial Finset.univ f) = 1 := by
          rw [h_multi_eq]
          rfl
        rw [h_size]
      rw [h_log]
      have : (1 : ENat) ≤ (kW : ENat) + 1 := by
        exact le_add_self
      exact this

/-- Single-coordinate empirical count of a maximal sample equals the exact
one-coordinate histogram. -/
theorem chainWordAt_count {k Q N : ℕ} {D : ChainDist k} {hQ : D.RationalAtoms Q}
    {W : List (Fin (2 * k + 2) → Bool)}
    (h : ∀ v, W.count v = chainHistogram D hQ N v) (j : Fin (2 * k + 2)) (b : Bool) :
    (chainWordAt W j).count b = chainHistogram1 D hQ N j b := by
  rw [chainWordAt, count_map_eq_sum_count]
  unfold chainHistogram1 chainMarginal
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [h v]
  by_cases hb : v j = b <;> simp [hb]

/-- Two-coordinate empirical joint count of a maximal sample (on the aligned
projection `v ↦ (v i, v j)`) equals the exact two-coordinate histogram. -/
theorem chainWordAt_pair_count {k Q N : ℕ} {D : ChainDist k} {hQ : D.RationalAtoms Q}
    {W : List (Fin (2 * k + 2) → Bool)}
    (h : ∀ v, W.count v = chainHistogram D hQ N v) (i j : Fin (2 * k + 2)) (a b : Bool) :
    (W.map (fun v => (v i, v j))).count (a, b) = chainHistogram2 D hQ N i j a b := by
  rw [count_map_eq_sum_count W (fun v => (v i, v j)) (a, b)]
  unfold chainHistogram2 chainMarginal
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [h v]
  by_cases hi : v i = a <;> by_cases hj : v j = b <;> simp [hi, hj, Prod.ext_iff]

/-- Three-coordinate empirical joint count of a maximal sample (on the aligned
projection `v ↦ ((v i, v j), v l)`) equals the exact three-coordinate
histogram. -/
theorem chainWordAt_triple_count {k Q N : ℕ} {D : ChainDist k} {hQ : D.RationalAtoms Q}
    {W : List (Fin (2 * k + 2) → Bool)}
    (h : ∀ v, W.count v = chainHistogram D hQ N v) (i j l : Fin (2 * k + 2)) (a b c : Bool) :
    (W.map (fun v => ((v i, v j), v l))).count ((a, b), c) =
      chainHistogram3 D hQ N i j l a b c := by
  rw [count_map_eq_sum_count W (fun v => ((v i, v j), v l)) ((a, b), c)]
  unfold chainHistogram3 chainMarginal
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [h v]
  by_cases hi : v i = a <;> by_cases hj : v j = b <;> by_cases hl : v l = c <;>
    simp [hi, hj, hl, Prod.ext_iff]

/-! ### Single-coordinate complexity profile -/

/-- Every coordinate of an exact chain sample has plain complexity at most its
binary type-log plus a uniform logarithmic parameter cost.  This is the easy
rank-decoding half of the one-coordinate profile; it does not use maximality
beyond obtaining the exact sample length and counts. -/
theorem chain_single_projection_plainK_upper
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ j : Fin (2 * k + 2),
        plainK V (chainWordAt W j) ≤
          ((histogramTypeLog (fun b => chainHistogram1 D hQ N j b) +
            logSlack C (N + 1) : ℕ) : ENat) := by
  obtain ⟨c, hc⟩ := plainK_fixedWeight_le_size_choose_add_length V hV
  refine ⟨4 + c, fun D Q N hQ hdiv W kW hsample j => ?_⟩
  let f : Bool → ℕ := fun b => chainHistogram1 D hQ N j b
  have hlen : (chainWordAt W j).length = N := by
    rw [chainWordAt, List.length_map]
    exact hsample.length_eq hdiv
  have hcount : (chainWordAt W j).count true = f true :=
    chainWordAt_count hsample.counts j true
  have hsum : f true + f false = N := by
    dsimp [f]
    rw [← chainWordAt_count hsample.counts j true,
      ← chainWordAt_count hsample.counts j false]
    have hcountsum := length_eq_sum_count_fintype (chainWordAt W j)
    rw [Fintype.sum_bool] at hcountsum
    omega
  have htype : histogramTypeLog f = Nat.size (N.choose (f true)) := by
    unfold histogramTypeLog
    rw [show (Finset.univ : Finset Bool) = {true, false} by decide,
      Nat.binomial_eq_choose (by decide : true ≠ false), hsum]
  have hslack : 4 * Nat.size N + c ≤ logSlack (4 + c) (N + 1) := by
    have hsize : Nat.size N ≤ Nat.size (N + 1) :=
      Nat.size_le_size (Nat.le_succ N)
    calc
      4 * Nat.size N + c ≤ 4 * Nat.size (N + 1) + c := by omega
      _ ≤ (4 + c) * Nat.size (N + 1) + (4 + c) := by
        nlinarith [Nat.zero_le (Nat.size (N + 1))]
      _ = logSlack (4 + c) (N + 1) := by
        unfold logSlack
        rw [Nat.size_eq_bits_len]
  calc
    plainK V (chainWordAt W j) ≤
        ((Nat.size (N.choose (f true)) + 4 * Nat.size N + c : ℕ) : ENat) :=
      hc N (f true) (chainWordAt W j) hlen hcount
    _ ≤ ((Nat.size (N.choose (f true)) + logSlack (4 + c) (N + 1) : ℕ) : ENat) := by
      exact_mod_cast (by omega :
        Nat.size (N.choose (f true)) + 4 * Nat.size N + c ≤
          Nat.size (N.choose (f true)) + logSlack (4 + c) (N + 1))
    _ = ((histogramTypeLog f + logSlack (4 + c) (N + 1) : ℕ) : ENat) := by
      rw [htype]

/-! ### Fibre decomposition of one maximal sample -/

/-- The binary type-log of the full chain histogram is linear in the sample
length: a word of length `N` over an alphabet of size `2 ^ (2 * k + 2)` has at
most `(2 * k + 2) * N + 1` bits of type index. -/
theorem chainHistogram_multinomial_size_le {k Q N : ℕ} (D : ChainDist k)
    (hQ : D.RationalAtoms Q) (hdiv : Q ∣ N) :
    Nat.size (Nat.multinomial univ (chainHistogram D hQ N)) ≤ (2 * k + 2) * N + 1 := by
  classical
  set e := @chainAlphabetEquiv k with he
  set f_m : Fin (2 ^ (2 * k + 2)) → ℕ := chainHistogram D hQ N ∘ e.symm with hfm
  have hmul : Nat.multinomial univ f_m = Nat.multinomial univ (chainHistogram D hQ N) :=
    multinomial_comp_equiv e.symm _
  have hsum : ∑ i, f_m i = N := by
    have hcomp := Equiv.sum_comp e.symm (chainHistogram D hQ N)
    rw [hfm]
    simpa [Function.comp] using hcomp.trans (chainHistogram_total D hQ N hdiv)
  have hle : Nat.multinomial univ (chainHistogram D hQ N) ≤ (2 ^ (2 * k + 2)) ^ N := by
    rw [← hmul, ← hsum]
    exact multinomial_le_pow_card_fin f_m
  calc Nat.size (Nat.multinomial univ (chainHistogram D hQ N))
      ≤ Nat.size ((2 ^ (2 * k + 2)) ^ N) := Nat.size_le_size hle
    _ = (2 * k + 2) * N + 1 := by rw [← pow_mul, Nat.size_pow]

/-- The chain alphabet code is the numeric code of the explicit binary
numbering, so the two word codes literally agree. -/
theorem finiteWordCode_chain_eq {k : ℕ} (W : List (Fin (2 * k + 2) → Bool)) :
    finiteWordCode W = finiteWordCode (W.map (@chainAlphabetEquiv k)) := by
  unfold finiteWordCode
  congr 2
  rw [List.map_map]
  rfl

/-- Transport of the exact histogram along the binary numbering. -/
theorem chainSample_count_map_equiv {k Q N : ℕ} {D : ChainDist k} {hQ : D.RationalAtoms Q}
    {W : List (Fin (2 * k + 2) → Bool)}
    (hcount : ∀ v, W.count v = chainHistogram D hQ N v)
    (i : Fin (2 ^ (2 * k + 2))) :
    (W.map (@chainAlphabetEquiv k)).count i =
      (chainHistogram D hQ N ∘ (@chainAlphabetEquiv k).symm) i := by
  classical
  set e := @chainAlphabetEquiv k
  have h := List.count_map_of_injective W e e.injective (e.symm i)
  rw [Equiv.apply_symm_apply] at h
  rw [h, hcount]
  rfl

/-- Any exact chain sample has plain complexity linear in the sample length,
with a logarithmic correction whose coefficient depends only on `k`. -/
theorem plainK_chainSample_le (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ c : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N)
      (W : List (Fin (2 * k + 2) → Bool)),
      (∀ v, W.count v = chainHistogram D hQ N v) →
      plainK V (finiteWordCode W) ≤
        (((2 * k + 2) * N + c * Nat.size (N + 1) + c : ℕ) : ENat) := by
  classical
  obtain ⟨c, hc⟩ := plainK_fixedHistogramWord_le_size_multinomial_add_params V hV
  set m := 2 ^ (2 * k + 2) with hm
  refine ⟨2 * m + 1 + 2 * Nat.size m + m + c, fun D Q N hQ hdiv W hcount => ?_⟩
  set e := @chainAlphabetEquiv k with he
  set f_m : Fin m → ℕ := chainHistogram D hQ N ∘ e.symm with hfm
  have hcounts : ∀ i, (W.map e).count i = f_m i := chainSample_count_map_equiv hcount
  have hbound := hc m f_m (W.map e) hcounts
  rw [← finiteWordCode_chain_eq W] at hbound
  have hmul : Nat.multinomial univ f_m = Nat.multinomial univ (chainHistogram D hQ N) :=
    multinomial_comp_equiv e.symm _
  have hsize : Nat.size (Nat.multinomial univ f_m) ≤ (2 * k + 2) * N + 1 := by
    rw [hmul]
    exact chainHistogram_multinomial_size_le D hQ hdiv
  have hsum : ∑ i, Nat.size (f_m i) ≤ m * Nat.size N := by
    have h1 : ∑ i, Nat.size (f_m i) = ∑ v, Nat.size (chainHistogram D hQ N v) :=
      Equiv.sum_comp e.symm (fun v => Nat.size (chainHistogram D hQ N v))
    rw [h1]
    exact sum_size_chainHistogram_le D hQ hdiv
  have hsizeN : Nat.size N ≤ Nat.size (N + 1) := Nat.size_le_size (Nat.le_succ N)
  have hfinal :
      Nat.size (Nat.multinomial univ f_m) + 2 * Nat.size m + 2 * (∑ i, Nat.size (f_m i)) +
          m + c ≤
        (2 * k + 2) * N + (2 * m + 1 + 2 * Nat.size m + m + c) * Nat.size (N + 1) +
          (2 * m + 1 + 2 * Nat.size m + m + c) := by
    have h2 : 2 * (∑ i, Nat.size (f_m i)) ≤ 2 * m * Nat.size (N + 1) := by
      calc 2 * (∑ i, Nat.size (f_m i)) ≤ 2 * (m * Nat.size N) := by omega
        _ ≤ 2 * m * Nat.size (N + 1) := by
            rw [mul_assoc]
            exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left m hsizeN)
    have h3 : 2 * m * Nat.size (N + 1) ≤
        (2 * m + 1 + 2 * Nat.size m + m + c) * Nat.size (N + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  calc plainK V (finiteWordCode W)
      ≤ (Nat.size (Nat.multinomial univ f_m) : ENat) + 2 * Nat.size m +
          2 * (∑ i, Nat.size (f_m i)) + m + c := hbound
    _ = ((Nat.size (Nat.multinomial univ f_m) + 2 * Nat.size m +
          2 * (∑ i, Nat.size (f_m i)) + m + c : ℕ) : ENat) := by push_cast; ring
    _ ≤ (((2 * k + 2) * N + (2 * m + 1 + 2 * Nat.size m + m + c) * Nat.size (N + 1) +
          (2 * m + 1 + 2 * Nat.size m + m + c) : ℕ) : ENat) := by exact_mod_cast hfinal

/-- The chain alphabet split at coordinate `j`: the `j`-th bit together with an
(arbitrary but fixed) numbering of the remaining coordinates. -/
noncomputable def chainSplitEquiv (k : ℕ) (j : Fin (2 * k + 2)) :
    (Fin (2 * k + 2) → Bool) ≃ Fin 2 × Fin (2 ^ (2 * k + 1)) :=
  (Equiv.piSplitAt j (fun _ => Bool)).trans
    (Equiv.prodCongr finTwoEquiv.symm (Fintype.equivFinOfCardEq (by simp)))

@[simp]
theorem chainSplitEquiv_fst (k : ℕ) (j : Fin (2 * k + 2)) (v : Fin (2 * k + 2) → Bool) :
    (chainSplitEquiv k j v).1 = finTwoEquiv.symm (v j) := rfl

theorem chainSplitEquiv_symm_j (k : ℕ) (j : Fin (2 * k + 2)) (a : Fin 2)
    (b : Fin (2 ^ (2 * k + 1))) :
    (chainSplitEquiv k j).symm (a, b) j = finTwoEquiv a := by
  have h := chainSplitEquiv_fst k j ((chainSplitEquiv k j).symm (a, b))
  rw [Equiv.apply_symm_apply] at h
  simpa using congrArg finTwoEquiv h.symm

/-- Summing the split histogram over the fibre coordinate recovers the exact
one-coordinate histogram. -/
theorem chain_fibre_marginal {k Q N : ℕ} (D : ChainDist k) (hQ : D.RationalAtoms Q)
    (j : Fin (2 * k + 2)) (a : Fin 2) :
    ∑ b, chainHistogram D hQ N ((chainSplitEquiv k j).symm (a, b)) =
      chainHistogram1 D hQ N j (finTwoEquiv a) := by
  classical
  unfold chainHistogram1 chainMarginal
  rw [← Equiv.sum_comp (chainSplitEquiv k j).symm
    (fun v => if (v j == finTwoEquiv a) = true then chainHistogram D hQ N v else 0)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chainSplitEquiv_symm_j]
    simp
  · intro a' _ hne
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chainSplitEquiv_symm_j]
    have hne' : finTwoEquiv a' ≠ finTwoEquiv a := fun h => hne (finTwoEquiv.injective h)
    simp [hne']
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The split word code is the numeric code of the split letter code. -/
theorem chainSplit_wordCode_eq {k : ℕ} (j : Fin (2 * k + 2))
    (W : List (Fin (2 * k + 2) → Bool)) :
    finiteWordCode (W.map (chainSplitEquiv k j)) =
      numericWordCode (W.map (fun v => FiniteLetterCode.encode (chainSplitEquiv k j v))) := by
  unfold finiteWordCode numericWordCode
  rw [List.map_map]
  rfl

/-- The first-coordinate projection of the split word is the numeric code of the
raw bit word at coordinate `j`. -/
theorem chainSplit_projCode_eq {k : ℕ} (j : Fin (2 * k + 2))
    (W : List (Fin (2 * k + 2) → Bool)) :
    finiteWordCode ((W.map (chainSplitEquiv k j)).map Prod.fst) =
      numericWordCode ((chainWordAt W j).map (fun b => if b then 1 else 0)) := by
  unfold finiteWordCode numericWordCode chainWordAt
  rw [List.map_map, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left (fun v _ => ?_)
  simp only [Function.comp_apply, chainSplitEquiv_fst]
  cases v j <;> simp <;> rfl

/-- The chain word code is the numeric code of the chain letter code. -/
theorem chainWordCode_eq {k : ℕ} (W : List (Fin (2 * k + 2) → Bool)) :
    finiteWordCode W = numericWordCode (W.map FiniteLetterCode.encode) := rfl

/-- Fibre factorisation of the full chain type count at coordinate `j`: the
full multinomial splits as the one-coordinate multinomial times the product of
the per-letter fibre multinomials. -/
theorem chainHistogram_multinomial_split {k Q N : ℕ} (D : ChainDist k)
    (hQ : D.RationalAtoms Q) (j : Fin (2 * k + 2)) :
    Nat.multinomial univ (chainHistogram D hQ N) =
      Nat.multinomial univ (fun b : Bool => chainHistogram1 D hQ N j b) *
        ∏ a : Fin 2, Nat.multinomial univ
          (fun b : Fin (2 ^ (2 * k + 1)) =>
            chainHistogram D hQ N ((chainSplitEquiv k j).symm (a, b))) := by
  classical
  set f : Fin 2 × Fin (2 ^ (2 * k + 1)) → ℕ :=
    fun ab => chainHistogram D hQ N ((chainSplitEquiv k j).symm ab) with hf
  have hEq : Nat.multinomial univ f = Nat.multinomial univ (chainHistogram D hQ N) :=
    multinomial_comp_equiv (chainSplitEquiv k j).symm (chainHistogram D hQ N)
  have hmarg : (fun a : Fin 2 => ∑ b, f (a, b)) =
      (fun b : Bool => chainHistogram1 D hQ N j b) ∘ finTwoEquiv := by
    funext a
    exact chain_fibre_marginal D hQ j a
  have hbin : Nat.multinomial univ (fun a : Fin 2 => ∑ b, f (a, b)) =
      Nat.multinomial univ (fun b : Bool => chainHistogram1 D hQ N j b) := by
    rw [hmarg]
    exact multinomial_comp_equiv finTwoEquiv _
  rw [← hEq, multinomial_fiber_factorization_left f, hbin]

/-- The split parameter table has the same total binary size as the full chain
histogram. -/
theorem sum_size_chainSplit_le {k Q N : ℕ} (D : ChainDist k) (hQ : D.RationalAtoms Q)
    (hdiv : Q ∣ N) (j : Fin (2 * k + 2)) :
    ∑ ab : Fin 2 × Fin (2 ^ (2 * k + 1)),
        Nat.size (chainHistogram D hQ N ((chainSplitEquiv k j).symm ab)) ≤
      2 ^ (2 * k + 2) * Nat.size N := by
  have h : ∑ ab : Fin 2 × Fin (2 ^ (2 * k + 1)),
      Nat.size (chainHistogram D hQ N ((chainSplitEquiv k j).symm ab)) =
      ∑ v, Nat.size (chainHistogram D hQ N v) :=
    Equiv.sum_comp (chainSplitEquiv k j).symm
      (fun v => Nat.size (chainHistogram D hQ N v))
  rw [h]
  exact sum_size_chainHistogram_le D hQ hdiv

/-- Fixed-coordinate form of the lower profile: with the coordinate `j` fixed
in advance, maximality of the full chain sample forces the `j`-th projection to
retain its binary type-log, up to a logarithmic loss. -/
theorem chain_single_projection_plainK_lower_at
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) (j : Fin (2 * k + 2)) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
        (histogramTypeLog (fun b => chainHistogram1 D hQ N j b) : ENat) ≤
          plainK V (chainWordAt W j) + (logSlack C (N + 1) : ENat) := by
  classical
  obtain ⟨cProj, hProj⟩ := condK_fixedHistogramWord_given_projection_le_add_params V hV
  have hc1inj : Function.Injective
      (fun v : Fin (2 * k + 2) → Bool => FiniteLetterCode.encode (chainSplitEquiv k j v)) := by
    intro a b hab
    exact (chainSplitEquiv k j).injective (FiniteLetterCode.injective hab)
  obtain ⟨cOut, hOut⟩ := condK_numericWord_recode_le V hV _
    (FiniteLetterCode.encode : (Fin (2 * k + 2) → Bool) → ℕ) hc1inj
  obtain ⟨cCond, hCond⟩ := condK_boolWord_cond_le V hV
  obtain ⟨cPair, hPair⟩ := plainK_pairCode_boolProj_le V hV
    (FiniteLetterCode.encode : (Fin (2 * k + 2) → Bool) → ℕ) FiniteLetterCode.injective
    (fun v => v j)
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values V hV
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le V hV
  obtain ⟨cCode, hCode⟩ := plainK_chainSample_le V hV k
  set gamma := (2 * k + 2) + cCode + cCode + cPair + 1 with hgamma
  refine ⟨2 * 2 ^ (2 * k + 2) + cChain +
    (2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) + 2 * 2 ^ (2 * k + 1) + cProj +
      cOut + cCond + cRight + 2 + cChain * Nat.size gamma + cChain),
    fun D Q N hQ hdiv W kW hsample => ?_⟩
  set C := 2 * 2 ^ (2 * k + 2) + cChain +
    (2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) + 2 * 2 ^ (2 * k + 1) + cProj +
      cOut + cCond + cRight + 2 + cChain * Nat.size gamma + cChain) with hC
  set x := chainWordAt W j with hx
  set y := finiteWordCode W with hy
  set f : Fin 2 × Fin (2 ^ (2 * k + 1)) → ℕ :=
    fun ab => chainHistogram D hQ N ((chainSplitEquiv k j).symm ab) with hf
  set w := W.map (chainSplitEquiv k j) with hw
  have hwcount : ∀ ab, w.count ab = f ab := by
    intro ab
    have h := List.count_map_of_injective W (chainSplitEquiv k j)
      (chainSplitEquiv k j).injective ((chainSplitEquiv k j).symm ab)
    rw [Equiv.apply_symm_apply] at h
    rw [hw, h, hsample.counts]
  have h1 := hProj 2 (2 ^ (2 * k + 1)) f w hwcount
  have h2 := hOut W (finiteWordCode (w.map Prod.fst))
  have h3 := hCond x y
  rw [← chainSplit_wordCode_eq j W, ← chainWordCode_eq W, ← hw, ← hy] at h2
  rw [← chainSplit_projCode_eq j W, ← hw] at h3
  set SP := Nat.size (∏ a, Nat.multinomial univ (fun b => f (a, b))) with hSP
  set PARAM := 2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) +
      2 * (∑ ab, Nat.size (f ab)) + 2 * 2 ^ (2 * k + 1) + cProj with hPARAM
  have hcondy : condK V y x ≤ ((SP + PARAM + cOut + cCond : ℕ) : ENat) := by
    calc condK V y x ≤ condK V y (finiteWordCode (w.map Prod.fst)) + (cCond : ENat) := h3
      _ ≤ (condK V (finiteWordCode w) (finiteWordCode (w.map Prod.fst)) + (cOut : ENat))
            + (cCond : ENat) := by gcongr
      _ ≤ (((SP + PARAM : ℕ) : ENat) + (cOut : ENat)) + (cCond : ENat) := by
            gcongr
            refine le_trans h1 (le_of_eq ?_)
            norm_cast
            rw [hPARAM]
            ring
      _ = ((SP + PARAM + cOut + cCond : ℕ) : ENat) := by push_cast; ring
  obtain ⟨kx, hkx⟩ := exists_plainComplexityValue V hV x
  obtain ⟨kyx, hkyx⟩ := exists_plainConditionalComplexityValue V hV y x
  obtain ⟨kxy, hkxy⟩ := exists_plainComplexityValue V hV (pairCode x y)
  have hkyx_le : kyx ≤ SP + PARAM + cOut + cCond := by
    have hcast : (kyx : ENat) ≤ ((SP + PARAM + cOut + cCond : ℕ) : ENat) := by
      rw [← hkyx]; exact hcondy
    exact_mod_cast hcast
  have hchain : kxy ≤ kx + kyx + logSlack cChain (kxy + 1) :=
    hChain x y kx kyx kxy hkx hkyx hkxy
  have hkW_le : kW ≤ kxy + cRight := by
    have h := hRight x y
    rw [hsample.value, pairPlainK, hkxy] at h
    exact_mod_cast h
  have hkxy_le : kxy ≤ kW + cPair := by
    have h := hPair W
    rw [← chainWordCode_eq W, ← hy] at h
    have hxx : W.map (fun v => v j) = x := rfl
    rw [hxx, hkxy, hsample.value] at h
    exact_mod_cast h
  have hkW_up : kW ≤ (2 * k + 2) * N + cCode * Nat.size (N + 1) + cCode := by
    have h := hCode D Q N hQ hdiv W hsample.counts
    rw [← hy, hsample.value] at h
    exact_mod_cast h
  have hmax : Nat.size (Nat.multinomial univ (chainHistogram D hQ N)) ≤ kW + 1 := by
    have h := hsample.maximal
    unfold histogramTypeLog at h
    exact_mod_cast h
  -- the fibre factorisation of the full type count
  set S := Nat.size (N + 1) with hS
  set binom := Nat.multinomial univ (fun b : Bool => chainHistogram1 D hQ N j b) with hbinom
  have hsplit : Nat.multinomial univ (chainHistogram D hQ N) =
      binom * ∏ a, Nat.multinomial univ (fun b => f (a, b)) :=
    chainHistogram_multinomial_split D hQ j
  have hbinpos : 1 ≤ binom := Nat.multinomial_pos _ _
  have hprodpos : 1 ≤ ∏ a, Nat.multinomial univ (fun b => f (a, b)) :=
    Finset.prod_pos (fun a _ => Nat.multinomial_pos _ _)
  have hsizes : Nat.size binom + SP ≤
      Nat.size (binom * ∏ a, Nat.multinomial univ (fun b => f (a, b))) + 1 := by
    rw [hSP]
    exact size_add_size_le_size_mul_succ hbinpos hprodpos
  rw [← hsplit] at hsizes
  have hkey : Nat.size binom + SP ≤ kW + 2 := by omega
  -- parameter table size
  have hsumf : ∑ ab, Nat.size (f ab) ≤ 2 ^ (2 * k + 2) * Nat.size N :=
    sum_size_chainSplit_le D hQ hdiv j
  have hsizeN : Nat.size N ≤ S := Nat.size_le_size (Nat.le_succ N)
  have hPARAMb : PARAM ≤ 2 * 2 ^ (2 * k + 2) * S +
      (2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) + 2 * 2 ^ (2 * k + 1) + cProj) := by
    have h1 : 2 * (∑ ab, Nat.size (f ab)) ≤ 2 * 2 ^ (2 * k + 2) * S := by
      calc 2 * (∑ ab, Nat.size (f ab)) ≤ 2 * (2 ^ (2 * k + 2) * Nat.size N) := by omega
        _ ≤ 2 * 2 ^ (2 * k + 2) * S := by
            rw [mul_assoc]
            exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hsizeN)
    rw [hPARAM]
    omega
  -- the pair complexity is linear in the sample length
  have hkxy1 : kxy + 1 ≤ gamma * (N + 1) := by
    have hSN : S ≤ N + 1 := size_le_self (N + 1)
    have hcc : cCode * S ≤ cCode * (N + 1) := Nat.mul_le_mul_left _ hSN
    have hexp : gamma * (N + 1) =
        (2 * k + 2) * (N + 1) + cCode * (N + 1) + cCode * (N + 1) + cPair * (N + 1) +
          (N + 1) := by
      rw [hgamma]; ring
    have h1 : (2 * k + 2) * N ≤ (2 * k + 2) * (N + 1) :=
      Nat.mul_le_mul_left _ (Nat.le_succ N)
    have h2 : cCode ≤ cCode * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : cPair ≤ cPair * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hlogb : logSlack cChain (kxy + 1) ≤ cChain * (Nat.size gamma + S) + cChain := by
    have hsize1 : Nat.size (kxy + 1) ≤ Nat.size gamma + S := by
      calc Nat.size (kxy + 1) ≤ Nat.size (gamma * (N + 1)) := Nat.size_le_size hkxy1
        _ ≤ Nat.size gamma + Nat.size (N + 1) := size_mul_le _ _
        _ = Nat.size gamma + S := by rw [hS]
    unfold logSlack
    rw [Nat.size_eq_bits_len]
    have := Nat.mul_le_mul_left cChain hsize1
    omega
  -- assembling the two-sided count
  have hchainfinal : Nat.size binom ≤ kx +
      ((2 * 2 ^ (2 * k + 2) + cChain) * S +
        (2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) + 2 * 2 ^ (2 * k + 1) + cProj +
          cOut + cCond + cRight + 2 + cChain * Nat.size gamma + cChain)) := by
    have hdistrib : (2 * 2 ^ (2 * k + 2) + cChain) * S =
        2 * 2 ^ (2 * k + 2) * S + cChain * S := by ring
    have hcs : cChain * (Nat.size gamma + S) = cChain * Nat.size gamma + cChain * S := by ring
    omega
  have hCbound :
      (2 * 2 ^ (2 * k + 2) + cChain) * S +
        (2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) + 2 * 2 ^ (2 * k + 1) + cProj +
          cOut + cCond + cRight + 2 + cChain * Nat.size gamma + cChain) ≤ C * S + C := by
    have h1 : (2 * 2 ^ (2 * k + 2) + cChain) * S ≤ C * S :=
      Nat.mul_le_mul_right _ (by rw [hC]; omega)
    have h2 : 2 * Nat.size 2 + 2 * Nat.size (2 ^ (2 * k + 1)) + 2 * 2 ^ (2 * k + 1) + cProj +
        cOut + cCond + cRight + 2 + cChain * Nat.size gamma + cChain ≤ C := by
      rw [hC]; omega
    omega
  have hgoalNat :
      histogramTypeLog (fun b => chainHistogram1 D hQ N j b) ≤ kx + logSlack C (N + 1) := by
    have hlog : logSlack C (N + 1) = C * S + C := by
      unfold logSlack
      rw [hS, Nat.size_eq_bits_len]
    rw [hlog]
    have : histogramTypeLog (fun b => chainHistogram1 D hQ N j b) = Nat.size binom := by
      rw [hbinom]
      rfl
    omega
  rw [hkx]
  exact_mod_cast hgoalNat

/-- Maximality of the full chain sample forces every coordinate to retain its
binary type-log, up to a uniform logarithmic loss.  Unlike the upper bound, this
is the fibre-incompressibility direction and uses the *same* maximal sample `W`;
choosing a fresh maximal marginal word would not prove it. -/
theorem chain_single_projection_plainK_lower
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ j : Fin (2 * k + 2),
        (histogramTypeLog (fun b => chainHistogram1 D hQ N j b) : ENat) ≤
          plainK V (chainWordAt W j) + (logSlack C (N + 1) : ENat) := by
  choose Cf hCf using fun j : Fin (2 * k + 2) =>
    chain_single_projection_plainK_lower_at V hV k j
  refine ⟨Finset.univ.sup Cf, fun D Q N hQ hdiv W kW hsample j => ?_⟩
  refine le_trans (hCf j D Q N hQ hdiv W kW hsample) ?_
  gcongr
  exact_mod_cast logSlack_mono_left (Finset.le_sup (Finset.mem_univ j)) (N + 1)

/-- The exact one-coordinate projection profile of one maximal full-chain
sample.  The exact value belongs to the raw binary coordinate word used by SUV
Exercise 316, not merely to an independently selected word of the same type. -/
theorem chain_single_projection_complexity_close
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ j : Fin (2 * k + 2), ∃ kj : ℕ,
        HasPlainComplexityValue V (chainWordAt W j) kj ∧
        histogramTypeLog (fun b => chainHistogram1 D hQ N j b) ≤
          kj + logSlack C (N + 1) ∧
        kj ≤ histogramTypeLog (fun b => chainHistogram1 D hQ N j b) +
          logSlack C (N + 1) := by
  obtain ⟨cUpper, hUpper⟩ := chain_single_projection_plainK_upper V hV k
  obtain ⟨cLower, hLower⟩ := chain_single_projection_plainK_lower V hV k
  refine ⟨cUpper + cLower, fun D Q N hQ hdiv W kW hsample j => ?_⟩
  obtain ⟨kj, hkj⟩ := exists_plainComplexityValue V hV (chainWordAt W j)
  refine ⟨kj, hkj, ?_, ?_⟩
  · have h := hLower D Q N hQ hdiv W kW hsample j
    rw [hkj] at h
    have hNat :
        histogramTypeLog (fun b => chainHistogram1 D hQ N j b) ≤
          kj + logSlack cLower (N + 1) := by
      exact_mod_cast h
    exact hNat.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_add_left cLower cUpper) (N + 1)) kj)
  · have h := hUpper D Q N hQ hdiv W kW hsample j
    rw [hkj] at h
    have hNat :
        kj ≤ histogramTypeLog (fun b => chainHistogram1 D hQ N j b) +
          logSlack cUpper (N + 1) := by
      exact_mod_cast h
    exact hNat.trans (Nat.add_le_add_left
        (logSlack_mono_left (Nat.le_add_right cUpper cLower) (N + 1))
      (histogramTypeLog (fun b => chainHistogram1 D hQ N j b)))

/-- The easy rank-decoding half of the two-coordinate projection profile. -/
theorem chain_pair_projection_plainK_upper
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ i j : Fin (2 * k + 2),
        plainK V (pairCode (chainWordAt W i) (chainWordAt W j)) ≤
          ((histogramTypeLog (fun p : Bool × Bool =>
              chainHistogram2 D hQ N i j p.1 p.2) +
            logSlack C (N + 1) : ℕ) : ENat) := by
  obtain ⟨cRank, hRank⟩ :=
    plainK_fixedHistogramWord_le_size_multinomial_add_params V hV
  let e : Bool × Bool ≃ Fin 4 := chainPairAlphabetEquiv
  obtain ⟨cRecode, hRecode⟩ := plainK_pairCode_two_boolProjections_le V hV
    (fun p : Bool × Bool => (e p).val)
    (fun _ _ h => e.injective (Fin.ext h)) Prod.fst Prod.snd
  refine ⟨8 + (2 * Nat.size 4 + 4 + cRank + cRecode), ?_⟩
  intro D Q N hQ hdiv W kW hsample i j
  let f : Bool × Bool → ℕ := fun p => chainHistogram2 D hQ N i j p.1 p.2
  let w : List (Bool × Bool) := W.map fun v => (v i, v j)
  let f4 : Fin 4 → ℕ := f ∘ e.symm
  let w4 : List (Fin 4) := w.map e
  have hwcount : ∀ q, w4.count q = f4 q := by
    intro q
    have hmap := List.count_map_of_injective w e e.injective (e.symm q)
    rw [Equiv.apply_symm_apply] at hmap
    dsimp [w4]
    rw [hmap]
    exact chainWordAt_pair_count hsample.counts i j (e.symm q).1 (e.symm q).2
  have hwlen : w.length = N := by
    dsimp [w]
    rw [List.length_map]
    exact hsample.length_eq hdiv
  have hsum : ∑ q, Nat.size (f4 q) ≤ 4 * Nat.size (N + 1) := by
    calc
      ∑ q, Nat.size (f4 q) ≤ Fintype.card (Fin 4) * Nat.size (N + 1) :=
        sum_size_le_card_mul_size f4 (N + 1) (fun q => by
          rw [← hwcount q]
          calc
            w4.count q ≤ w4.length := List.count_le_length
            _ = N := by simp [w4, hwlen]
            _ ≤ N + 1 := Nat.le_succ N)
      _ = 4 * Nat.size (N + 1) := by simp
  have htype : histogramTypeLog f4 = histogramTypeLog f := by
    unfold histogramTypeLog
    rw [show Nat.multinomial Finset.univ f4 = Nat.multinomial Finset.univ f by
      exact multinomial_comp_equiv e.symm f]
  have hcode : finiteWordCode w4 =
      numericWordCode (w.map fun p => (e p).val) := by
    rw [finiteWordCode_eq_numericWordCode]
    dsimp [w4]
    apply congrArg numericWordCode
    rw [List.map_map]
    exact List.map_congr_left (fun _ _ => rfl)
  have hrecode : plainK V (pairCode (chainWordAt W i) (chainWordAt W j)) ≤
      plainK V (finiteWordCode w4) + (cRecode : ENat) := by
    rw [hcode]
    simpa [w, chainWordAt, List.map_map] using hRecode w
  have hrank := hRank 4 f4 w4 hwcount
  have hslack : 2 * (∑ q, Nat.size (f4 q)) + 2 * Nat.size 4 + 4 + cRank +
      cRecode ≤ logSlack (8 + (2 * Nat.size 4 + 4 + cRank + cRecode)) (N + 1) := by
    unfold logSlack
    rw [Nat.size_eq_bits_len]
    have hpos : 1 ≤ Nat.size (N + 1) := Nat.size_pos.mpr (by omega)
    nlinarith
  calc
    plainK V (pairCode (chainWordAt W i) (chainWordAt W j))
        ≤ plainK V (finiteWordCode w4) + (cRecode : ENat) := hrecode
    _ ≤ ((Nat.size (Nat.multinomial Finset.univ f4) + 2 * Nat.size 4 +
          2 * (∑ q, Nat.size (f4 q)) + 4 + cRank + cRecode : ℕ) : ENat) := by
      calc
        plainK V (finiteWordCode w4) + (cRecode : ENat)
            ≤ ((Nat.size (Nat.multinomial Finset.univ f4) : ENat) +
                2 * Nat.size 4 + 2 * (∑ q, Nat.size (f4 q)) + 4 + cRank) +
                (cRecode : ENat) := add_le_add hrank le_rfl
        _ = _ := by push_cast; ring
    _ ≤ ((histogramTypeLog f +
          logSlack (8 + (2 * Nat.size 4 + 4 + cRank + cRecode)) (N + 1) : ℕ) :
          ENat) := by
      exact_mod_cast (by rw [← htype]; unfold histogramTypeLog; omega)

/-- Fixed-coordinates form of the two-coordinate lower profile.  The pair of
coordinates is fixed in advance, so the fibre argument of
`maximalSample_projection_typeLog_le` applies to the aligned projection
`v ↦ (v i, v j)`; this also covers the degenerate case `i = j`, where the
projection has empty fibres. -/
theorem chain_pair_projection_plainK_lower_at
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) (i j : Fin (2 * k + 2)) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
        (histogramTypeLog (fun p : Bool × Bool =>
            chainHistogram2 D hQ N i j p.1 p.2) : ENat) ≤
          plainK V (pairCode (chainWordAt W i) (chainWordAt W j)) +
            (logSlack C (N + 1) : ENat) := by
  classical
  set e : Bool × Bool ≃ Fin 4 := chainPairAlphabetEquiv with he
  set pi : (Fin (2 * k + 2) → Bool) → Fin 4 := fun v => e (v i, v j) with hpi
  set proj : List (Fin (2 * k + 2) → Bool) → BitString :=
    fun W => pairCode (chainWordAt W i) (chainWordAt W j) with hproj
  obtain ⟨c₁, hc₁⟩ := condK_cond_pairCode_two_boolWords_le V hV
    (fun v : Fin (2 * k + 2) → Bool => v i) (fun v => v j)
    (fun p : Bool × Bool => (e p).val)
  obtain ⟨c₂, hc₂⟩ := plainK_pairCode_two_boolProjections_self_le V hV
    (FiniteLetterCode.encode : (Fin (2 * k + 2) → Bool) → ℕ)
    FiniteLetterCode.injective (fun v => v i) (fun v => v j)
  obtain ⟨cCode, hCode⟩ := plainK_chainSample_le V hV k
  have h₁ : ∀ (W : List (Fin (2 * k + 2) → Bool)) (z : BitString),
      condK V z (proj W) ≤ condK V z (finiteWordCode (W.map pi)) + (c₁ : ENat) := by
    intro W z
    have hword : finiteWordCode (W.map pi) =
        numericWordCode (W.map (fun v => (e (v i, v j)).val)) := by
      rw [finiteWordCode_eq_numericWordCode, List.map_map]
      rfl
    rw [hword]
    exact hc₁ W z
  have h₂ : ∀ W : List (Fin (2 * k + 2) → Bool),
      plainK V (pairCode (proj W) (finiteWordCode W)) ≤
        plainK V (finiteWordCode W) + (c₂ : ENat) := by
    intro W
    exact hc₂ W
  obtain ⟨C, hC⟩ := maximalSample_projection_typeLog_le V hV 4 pi proj c₁ c₂
    ((2 * k + 2) + cCode) h₁ h₂
  refine ⟨C, fun D Q N hQ hdiv W kW hsample => ?_⟩
  have hkW : kW ≤ ((2 * k + 2) + cCode) * N +
      ((2 * k + 2) + cCode) * Nat.size (N + 1) + ((2 * k + 2) + cCode) := by
    have h := hCode D Q N hQ hdiv W hsample.counts
    rw [hsample.value] at h
    have hnat : kW ≤ (2 * k + 2) * N + cCode * Nat.size (N + 1) + cCode := by
      exact_mod_cast h
    have h1 : (2 * k + 2) * N ≤ ((2 * k + 2) + cCode) * N :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : cCode * Nat.size (N + 1) ≤ ((2 * k + 2) + cCode) * Nat.size (N + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hmain := hC N (chainHistogram D hQ N) W kW hsample.counts
    (chainHistogram_total D hQ N hdiv) hsample.value hsample.maximal hkW
  have hpush : (fun a : Fin 4 =>
      ∑ v ∈ Finset.univ.filter (fun v => pi v = a), chainHistogram D hQ N v) =
      (fun p : Bool × Bool => chainHistogram2 D hQ N i j p.1 p.2) ∘ e.symm := by
    funext a
    rw [Finset.sum_filter]
    change ∑ v, (if pi v = a then chainHistogram D hQ N v else 0) =
      chainHistogram2 D hQ N i j (e.symm a).1 (e.symm a).2
    unfold chainHistogram2 chainMarginal
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hkey : (pi v = a) ↔ ((v i, v j) = e.symm a) := by
      rw [hpi]
      exact (Equiv.eq_symm_apply e).symm
    by_cases hb : (v i, v j) = e.symm a
    · have h1 : v i = (e.symm a).1 := congrArg Prod.fst hb
      have h2 : v j = (e.symm a).2 := congrArg Prod.snd hb
      simp [hkey.mpr hb, h1, h2]
    · have hne : ¬ (pi v = a) := fun h => hb (hkey.mp h)
      have hor : ¬ (v i = (e.symm a).1 ∧ v j = (e.symm a).2) := by
        intro ⟨h1, h2⟩
        exact hb (Prod.ext h1 h2)
      simp only [hne, if_false]
      by_cases h1 : v i = (e.symm a).1 <;> by_cases h2 : v j = (e.symm a).2 <;>
        simp_all
  have htype : histogramTypeLog (fun a : Fin 4 =>
      ∑ v ∈ Finset.univ.filter (fun v => pi v = a), chainHistogram D hQ N v) =
      histogramTypeLog (fun p : Bool × Bool =>
        chainHistogram2 D hQ N i j p.1 p.2) := by
    unfold histogramTypeLog
    rw [hpush]
    exact congrArg Nat.size (multinomial_comp_equiv e.symm _)
  rw [← htype]
  exact hmain

/-- The hard fibre-incompressibility half of the two-coordinate projection
profile. It must use maximality of the same full sample `W`. -/
theorem chain_pair_projection_plainK_lower
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ i j : Fin (2 * k + 2),
        (histogramTypeLog (fun p : Bool × Bool =>
            chainHistogram2 D hQ N i j p.1 p.2) : ENat) ≤
          plainK V (pairCode (chainWordAt W i) (chainWordAt W j)) +
            (logSlack C (N + 1) : ENat) := by
  classical
  choose Cf hCf using fun q : Fin (2 * k + 2) × Fin (2 * k + 2) =>
    chain_pair_projection_plainK_lower_at V hV k q.1 q.2
  refine ⟨Finset.univ.sup Cf, fun D Q N hQ hdiv W kW hsample i j => ?_⟩
  refine le_trans (hCf (i, j) D Q N hQ hdiv W kW hsample) ?_
  gcongr
  exact_mod_cast logSlack_mono_left (Finset.le_sup (Finset.mem_univ (i, j))) (N + 1)

theorem chain_pair_projection_complexity_close
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ i j : Fin (2 * k + 2), ∃ k_ij : ℕ,
        HasPlainComplexityValue V (pairCode (chainWordAt W i) (chainWordAt W j)) k_ij ∧
        histogramTypeLog (fun (p : Bool × Bool) => chainHistogram2 D hQ N i j p.1 p.2) ≤
          k_ij + logSlack C (N + 1) ∧
        k_ij ≤ histogramTypeLog (fun (p : Bool × Bool) => chainHistogram2 D hQ N i j p.1 p.2) +
          logSlack C (N + 1) := by
  obtain ⟨cUpper, hUpper⟩ := chain_pair_projection_plainK_upper V hV k
  obtain ⟨cLower, hLower⟩ := chain_pair_projection_plainK_lower V hV k
  refine ⟨cUpper + cLower, fun D Q N hQ hdiv W kW hsample i j => ?_⟩
  obtain ⟨kij, hkij⟩ := exists_plainComplexityValue V hV
    (pairCode (chainWordAt W i) (chainWordAt W j))
  refine ⟨kij, hkij, ?_, ?_⟩
  · have h := hLower D Q N hQ hdiv W kW hsample i j
    rw [hkij] at h
    have hNat :
        histogramTypeLog (fun p : Bool × Bool =>
            chainHistogram2 D hQ N i j p.1 p.2) ≤
          kij + logSlack cLower (N + 1) := by
      exact_mod_cast h
    exact hNat.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_add_left cLower cUpper) (N + 1)) kij)
  · have h := hUpper D Q N hQ hdiv W kW hsample i j
    rw [hkij] at h
    have hNat :
        kij ≤ histogramTypeLog (fun p : Bool × Bool =>
            chainHistogram2 D hQ N i j p.1 p.2) +
          logSlack cUpper (N + 1) := by
      exact_mod_cast h
    exact hNat.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_add_right cUpper cLower) (N + 1))
      (histogramTypeLog (fun p : Bool × Bool =>
        chainHistogram2 D hQ N i j p.1 p.2)))

/-- The easy rank-decoding half of the three-coordinate projection profile. -/
theorem chain_triple_projection_plainK_upper
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ i j l : Fin (2 * k + 2),
        plainK V (pairCode (chainPairAt W i j) (chainWordAt W l)) ≤
          ((histogramTypeLog (fun p : (Bool × Bool) × Bool =>
              chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) +
            logSlack C (N + 1) : ℕ) : ENat) := by
  obtain ⟨cRank, hRank⟩ :=
    plainK_fixedHistogramWord_le_size_multinomial_add_params V hV
  let e : (Bool × Bool) × Bool ≃ Fin 8 := chainTripleAlphabetEquiv
  obtain ⟨cRecode, hRecode⟩ := plainK_pairCode_three_boolProjections_le V hV
    (fun p : (Bool × Bool) × Bool => (e p).val)
    (fun _ _ h => e.injective (Fin.ext h))
    (fun p => p.1.1) (fun p => p.1.2) Prod.snd
  refine ⟨16 + (2 * Nat.size 8 + 8 + cRank + cRecode), ?_⟩
  intro D Q N hQ hdiv W kW hsample i j l
  let f : (Bool × Bool) × Bool → ℕ := fun p =>
    chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2
  let w : List ((Bool × Bool) × Bool) := W.map fun v => ((v i, v j), v l)
  let f8 : Fin 8 → ℕ := f ∘ e.symm
  let w8 : List (Fin 8) := w.map e
  have hwcount : ∀ q, w8.count q = f8 q := by
    intro q
    have hmap := List.count_map_of_injective w e e.injective (e.symm q)
    rw [Equiv.apply_symm_apply] at hmap
    dsimp [w8]
    rw [hmap]
    exact chainWordAt_triple_count hsample.counts i j l
      (e.symm q).1.1 (e.symm q).1.2 (e.symm q).2
  have hwlen : w.length = N := by
    dsimp [w]
    rw [List.length_map]
    exact hsample.length_eq hdiv
  have hsum : ∑ q, Nat.size (f8 q) ≤ 8 * Nat.size (N + 1) := by
    calc
      ∑ q, Nat.size (f8 q) ≤ Fintype.card (Fin 8) * Nat.size (N + 1) :=
        sum_size_le_card_mul_size f8 (N + 1) (fun q => by
          rw [← hwcount q]
          calc
            w8.count q ≤ w8.length := List.count_le_length
            _ = N := by simp [w8, hwlen]
            _ ≤ N + 1 := Nat.le_succ N)
      _ = 8 * Nat.size (N + 1) := by simp
  have htype : histogramTypeLog f8 = histogramTypeLog f := by
    unfold histogramTypeLog
    rw [show Nat.multinomial Finset.univ f8 = Nat.multinomial Finset.univ f by
      exact multinomial_comp_equiv e.symm f]
  have hcode : finiteWordCode w8 =
      numericWordCode (w.map fun p => (e p).val) := by
    rw [finiteWordCode_eq_numericWordCode]
    dsimp [w8]
    apply congrArg numericWordCode
    rw [List.map_map]
    exact List.map_congr_left (fun _ _ => rfl)
  have hrecode : plainK V (pairCode (chainPairAt W i j) (chainWordAt W l)) ≤
      plainK V (finiteWordCode w8) + (cRecode : ENat) := by
    rw [hcode]
    simpa [w, chainPairAt, chainWordAt, List.map_map] using hRecode w
  have hrank := hRank 8 f8 w8 hwcount
  have hslack : 2 * (∑ q, Nat.size (f8 q)) + 2 * Nat.size 8 + 8 + cRank +
      cRecode ≤ logSlack (16 + (2 * Nat.size 8 + 8 + cRank + cRecode))
        (N + 1) := by
    unfold logSlack
    rw [Nat.size_eq_bits_len]
    have hpos : 1 ≤ Nat.size (N + 1) := Nat.size_pos.mpr (by omega)
    nlinarith
  calc
    plainK V (pairCode (chainPairAt W i j) (chainWordAt W l))
        ≤ plainK V (finiteWordCode w8) + (cRecode : ENat) := hrecode
    _ ≤ ((Nat.size (Nat.multinomial Finset.univ f8) + 2 * Nat.size 8 +
          2 * (∑ q, Nat.size (f8 q)) + 8 + cRank + cRecode : ℕ) : ENat) := by
      calc
        plainK V (finiteWordCode w8) + (cRecode : ENat)
            ≤ ((Nat.size (Nat.multinomial Finset.univ f8) : ENat) +
                2 * Nat.size 8 + 2 * (∑ q, Nat.size (f8 q)) + 8 + cRank) +
                (cRecode : ENat) := add_le_add hrank le_rfl
        _ = _ := by push_cast; ring
    _ ≤ ((histogramTypeLog f +
          logSlack (16 + (2 * Nat.size 8 + 8 + cRank + cRecode)) (N + 1) : ℕ) :
          ENat) := by
      exact_mod_cast (by rw [← htype]; unfold histogramTypeLog; omega)

/-- Fixed-coordinates form of the three-coordinate lower profile. -/
theorem chain_triple_projection_plainK_lower_at
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) (i j l : Fin (2 * k + 2)) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
        (histogramTypeLog (fun p : (Bool × Bool) × Bool =>
            chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) : ENat) ≤
          plainK V (pairCode (chainPairAt W i j) (chainWordAt W l)) +
            (logSlack C (N + 1) : ENat) := by
  classical
  set e : (Bool × Bool) × Bool ≃ Fin 8 := chainTripleAlphabetEquiv with he
  set pi : (Fin (2 * k + 2) → Bool) → Fin 8 :=
    fun v => e ((v i, v j), v l) with hpi
  set proj : List (Fin (2 * k + 2) → Bool) → BitString :=
    fun W => pairCode (chainPairAt W i j) (chainWordAt W l) with hproj
  obtain ⟨c₁, hc₁⟩ := condK_cond_pairCode_three_boolWords_le V hV
    (fun v : Fin (2 * k + 2) → Bool => v i) (fun v => v j) (fun v => v l)
    (fun p : (Bool × Bool) × Bool => (e p).val)
  obtain ⟨c₂, hc₂⟩ := plainK_pairCode_three_boolProjections_self_le V hV
    (FiniteLetterCode.encode : (Fin (2 * k + 2) → Bool) → ℕ)
    FiniteLetterCode.injective (fun v => v i) (fun v => v j) (fun v => v l)
  obtain ⟨cCode, hCode⟩ := plainK_chainSample_le V hV k
  have h₁ : ∀ (W : List (Fin (2 * k + 2) → Bool)) (z : BitString),
      condK V z (proj W) ≤ condK V z (finiteWordCode (W.map pi)) + (c₁ : ENat) := by
    intro W z
    have hword : finiteWordCode (W.map pi) =
        numericWordCode (W.map (fun v => (e ((v i, v j), v l)).val)) := by
      rw [finiteWordCode_eq_numericWordCode, List.map_map]
      rfl
    rw [hword]
    exact hc₁ W z
  have h₂ : ∀ W : List (Fin (2 * k + 2) → Bool),
      plainK V (pairCode (proj W) (finiteWordCode W)) ≤
        plainK V (finiteWordCode W) + (c₂ : ENat) := by
    intro W
    exact hc₂ W
  obtain ⟨C, hC⟩ := maximalSample_projection_typeLog_le V hV 8 pi proj c₁ c₂
    ((2 * k + 2) + cCode) h₁ h₂
  refine ⟨C, fun D Q N hQ hdiv W kW hsample => ?_⟩
  have hkW : kW ≤ ((2 * k + 2) + cCode) * N +
      ((2 * k + 2) + cCode) * Nat.size (N + 1) + ((2 * k + 2) + cCode) := by
    have h := hCode D Q N hQ hdiv W hsample.counts
    rw [hsample.value] at h
    have hnat : kW ≤ (2 * k + 2) * N + cCode * Nat.size (N + 1) + cCode := by
      exact_mod_cast h
    have h1 : (2 * k + 2) * N ≤ ((2 * k + 2) + cCode) * N :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : cCode * Nat.size (N + 1) ≤ ((2 * k + 2) + cCode) * Nat.size (N + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hmain := hC N (chainHistogram D hQ N) W kW hsample.counts
    (chainHistogram_total D hQ N hdiv) hsample.value hsample.maximal hkW
  have hpush : (fun a : Fin 8 =>
      ∑ v ∈ Finset.univ.filter (fun v => pi v = a), chainHistogram D hQ N v) =
      (fun p : (Bool × Bool) × Bool =>
        chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) ∘ e.symm := by
    funext a
    rw [Finset.sum_filter]
    change ∑ v, (if pi v = a then chainHistogram D hQ N v else 0) =
      chainHistogram3 D hQ N i j l (e.symm a).1.1 (e.symm a).1.2 (e.symm a).2
    unfold chainHistogram3 chainMarginal
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hkey : (pi v = a) ↔ (((v i, v j), v l) = e.symm a) := by
      rw [hpi]
      exact (Equiv.eq_symm_apply e).symm
    by_cases hb : ((v i, v j), v l) = e.symm a
    · have h1 : v i = (e.symm a).1.1 := congrArg (fun p => p.1.1) hb
      have h2 : v j = (e.symm a).1.2 := congrArg (fun p => p.1.2) hb
      have h3 : v l = (e.symm a).2 := congrArg Prod.snd hb
      simp [hkey.mpr hb, h1, h2, h3]
    · have hne : ¬ (pi v = a) := fun h => hb (hkey.mp h)
      have hcond : ¬ ((((v i == (e.symm a).1.1) && (v j == (e.symm a).1.2)) &&
          (v l == (e.symm a).2)) = true) := by
        intro hc
        rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
          beq_iff_eq] at hc
        exact hb (Prod.ext (Prod.ext hc.1.1 hc.1.2) hc.2)
      rw [if_neg hne, if_neg hcond]
  have htype : histogramTypeLog (fun a : Fin 8 =>
      ∑ v ∈ Finset.univ.filter (fun v => pi v = a), chainHistogram D hQ N v) =
      histogramTypeLog (fun p : (Bool × Bool) × Bool =>
        chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) := by
    unfold histogramTypeLog
    rw [hpush]
    exact congrArg Nat.size (multinomial_comp_equiv e.symm _)
  rw [← htype]
  exact hmain

/-- The hard fibre-incompressibility half of the three-coordinate projection
profile. It must use maximality of the same full sample `W`. -/
theorem chain_triple_projection_plainK_lower
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ i j l : Fin (2 * k + 2),
        (histogramTypeLog (fun p : (Bool × Bool) × Bool =>
            chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) : ENat) ≤
          plainK V (pairCode (chainPairAt W i j) (chainWordAt W l)) +
            (logSlack C (N + 1) : ENat) := by
  classical
  choose Cf hCf using
    fun q : (Fin (2 * k + 2) × Fin (2 * k + 2)) × Fin (2 * k + 2) =>
      chain_triple_projection_plainK_lower_at V hV k q.1.1 q.1.2 q.2
  refine ⟨Finset.univ.sup Cf, fun D Q N hQ hdiv W kW hsample i j l => ?_⟩
  refine le_trans (hCf ((i, j), l) D Q N hQ hdiv W kW hsample) ?_
  gcongr
  exact_mod_cast logSlack_mono_left
    (Finset.le_sup (Finset.mem_univ ((i, j), l))) (N + 1)

theorem chain_triple_projection_complexity_close
    (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q)
      (_hdiv : Q ∣ N) (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ i j l : Fin (2 * k + 2), ∃ k_ijl : ℕ,
        HasPlainComplexityValue V (pairCode (chainPairAt W i j) (chainWordAt W l)) k_ijl ∧
        histogramTypeLog (fun (p : (Bool × Bool) × Bool) =>
            chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) ≤
          k_ijl + logSlack C (N + 1) ∧
        k_ijl ≤ histogramTypeLog (fun (p : (Bool × Bool) × Bool) =>
            chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) +
          logSlack C (N + 1) := by
  obtain ⟨cUpper, hUpper⟩ := chain_triple_projection_plainK_upper V hV k
  obtain ⟨cLower, hLower⟩ := chain_triple_projection_plainK_lower V hV k
  refine ⟨cUpper + cLower, fun D Q N hQ hdiv W kW hsample i j l => ?_⟩
  obtain ⟨kijl, hkijl⟩ := exists_plainComplexityValue V hV
    (pairCode (chainPairAt W i j) (chainWordAt W l))
  refine ⟨kijl, hkijl, ?_, ?_⟩
  · have h := hLower D Q N hQ hdiv W kW hsample i j l
    rw [hkijl] at h
    have hNat :
        histogramTypeLog (fun p : (Bool × Bool) × Bool =>
            chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) ≤
          kijl + logSlack cLower (N + 1) := by
      exact_mod_cast h
    exact hNat.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_add_left cLower cUpper) (N + 1)) kijl)
  · have h := hUpper D Q N hQ hdiv W kW hsample i j l
    rw [hkijl] at h
    have hNat :
        kijl ≤ histogramTypeLog (fun p : (Bool × Bool) × Bool =>
            chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) +
          logSlack cUpper (N + 1) := by
      exact_mod_cast h
    exact hNat.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_add_right cUpper cLower) (N + 1))
      (histogramTypeLog (fun p : (Bool × Bool) × Bool =>
        chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2)))

theorem logSlack_le_linear (C N : ℕ) : logSlack C (N + 1) ≤ C * N + 2 * C := by
  unfold logSlack
  rw [Nat.size_eq_bits_len]
  have h1 : Nat.size (N + 1) ≤ N + 1 := by
    apply Nat.size_le.mpr
    apply Nat.lt_two_pow_self
  calc C * Nat.size (N + 1) + C
    ≤ C * (N + 1) + C := Nat.add_le_add_right (Nat.mul_le_mul_left C h1) C
    _ = C * N + C + C := by ring
    _ = C * N + 2 * C := by ring

theorem chain_projection_value_le_linear_N (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ A B : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N)
      (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ (j : Fin (2 * k + 2)) (kj : ℕ),
        HasPlainComplexityValue V (chainWordAt W j) kj → kj ≤ A * N + B := by
  obtain ⟨C, hC⟩ := chain_single_projection_complexity_close V hV k
  refine ⟨C + 1, 2 * C + 1, fun D Q N hQ hdiv W kW hsample j kj hkj => ?_⟩
  obtain ⟨kj', hkj', _, hUpper⟩ := hC D Q N hQ hdiv W kW hsample j
  have heq : kj = kj' := by
    have h1 : (kj : ENat) = (kj' : ENat) := hkj.symm.trans hkj'
    exact_mod_cast h1
  rw [heq]
  have hsum : chainHistogram1 D hQ N j true + chainHistogram1 D hQ N j false = N := by
    rw [← chainWordAt_count hsample.counts j true,
        ← chainWordAt_count hsample.counts j false]
    have hcountsum := length_eq_sum_count_fintype (chainWordAt W j)
    rw [Fintype.sum_bool] at hcountsum
    have hlen : (chainWordAt W j).length = N := by
      rw [chainWordAt, List.length_map]
      exact hsample.length_eq hdiv
    rw [hlen] at hcountsum
    omega
  have htype : histogramTypeLog (fun b => chainHistogram1 D hQ N j b) =
      Nat.size (N.choose (chainHistogram1 D hQ N j true)) := by
    unfold histogramTypeLog
    rw [show (Finset.univ : Finset Bool) = {true, false} by decide,
        Nat.binomial_eq_choose (by decide : true ≠ false), hsum]
  have hsize1 : Nat.size (N.choose (chainHistogram1 D hQ N j true)) ≤ N + 1 := by
    apply Nat.size_le.mpr
    calc
      N.choose (chainHistogram1 D hQ N j true) ≤ 2 ^ N :=
        Nat.choose_le_two_pow N (chainHistogram1 D hQ N j true)
      _ < 2 ^ (N + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self N)
  calc kj' ≤ histogramTypeLog (fun b => chainHistogram1 D hQ N j b) + logSlack C (N + 1) := hUpper
    _ = Nat.size (N.choose (chainHistogram1 D hQ N j true)) + logSlack C (N + 1) := by rw [htype]
    _ ≤ (N + 1) + logSlack C (N + 1) := Nat.add_le_add_right hsize1 _
    _ ≤ (N + 1) + (C * N + 2 * C) := Nat.add_le_add_left (logSlack_le_linear C N) _
    _ = (C + 1) * N + (2 * C + 1) := by ring

end Kolmogorov
