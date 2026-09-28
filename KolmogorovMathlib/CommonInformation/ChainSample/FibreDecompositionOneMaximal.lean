import KolmogorovMathlib.CommonInformation.ChainFibre
import KolmogorovMathlib.CommonInformation.MaximalSampleFibre
import KolmogorovMathlib.CommonInformation.ChainWitness
import KolmogorovMathlib.CommonInformation.FixedHistogramRank
import KolmogorovMathlib.CommonInformation.FixedHistogramProjectionParams
import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.CommonInformation.ChainSample.Part01

/-!
# Projection complexity of a maximal chain sample: pairs and triples

For a maximally complex sample of the chain's joint type, the complexity of a projection is
exactly the logarithm of the number of samples with that projection.  This module proves the
two- and three-coordinate cases: `chain_pair_projection_complexity_close` and
`chain_triple_projection_complexity_close`.

Each is an upper bound by rank decoding (`chain_triple_projection_plainK_upper`) and a lower
bound by incompressibility of the fibre (`chain_triple_projection_plainK_lower`, with its
fixed-coordinate form).  `chain_projection_value_le_linear_N` and `logSlack_le_linear` bound
the quantities involved linearly in the sample size.  The one-coordinate case is in
`ChainSample/Part01`.
-/

namespace Kolmogorov
open Finset

/-- In a maximal chain sample the complexity of the pair of two coordinate words equals the
logarithm of the size of the corresponding two-dimensional type class, up to a logarithmic
slack. -/
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

/-- In a maximal chain sample the complexity of a triple of coordinate words equals the logarithm
of the size of the corresponding three-dimensional type class, up to a logarithmic slack. -/
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

/-- The logarithmic slack is bounded by a linear function of its argument. -/
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

/-- Each coordinate word of a maximal chain sample has complexity linear in the sample size. -/
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
