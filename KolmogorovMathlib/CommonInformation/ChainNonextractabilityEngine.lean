import KolmogorovMathlib.CommonInformation.ChainSample
import KolmogorovMathlib.CommonInformation.ConditionalIndependenceChains
import KolmogorovMathlib.CommonInformation.ConditionalIndependence
import KolmogorovMathlib.CommonInformation.PlainSymmetry

/-!
# Engine layer for the iterated non-extractability bound

This file collects the reusable pieces behind
`chain_sample_iterated_nonextractability` (SUV Exercise 316, iteration 3):

* pure arithmetic showing that a linear function of the *binary size* of a
  number is eventually dominated by the number itself
  (`linear_le_two_pow`, `exists_size_linear_threshold`);
* the plain-complexity swap of a canonical pair code
  (`plainK_swap_value_le`);
* linear-in-`N` bounds on the type-logs of the two- and three-coordinate
  projections of a chain sample, hence on their plain complexities
  (`chain_pair_value_le_linear_N`, `chain_triple_value_le_linear_N`);
* the conversion of the histogram-level conditional-independence defects of
  `ChainHistogram.lean` into *complexity* defects on one maximal sample
  (`chain_link_condK_defect`, `chain_top_plainK_defect`).
-/

namespace Kolmogorov
open Finset

/-! ### Linear functions are eventually dominated by powers of two -/

/-- A linear function of `s` is bounded by `2 ^ s` once `s` is large. -/
theorem linear_le_two_pow (c e s : ℕ) (hs : 4 * (c + e + 1) ≤ s) : c * s + e ≤ 2 ^ s := by
  set x := 2 * (c + e + 1) with hx
  have hxs : 2 * x ≤ s := by omega
  have h1 : x < 2 ^ x := Nat.lt_two_pow_self
  have h2 : s - x < 2 ^ (s - x) := Nat.lt_two_pow_self
  have hsplit : (2 : ℕ) ^ s = 2 ^ x * 2 ^ (s - x) := by
    rw [← pow_add]; congr 1; omega
  have hge : x * (s - x) ≤ 2 ^ s := by
    rw [hsplit]
    exact Nat.mul_le_mul h1.le h2.le
  have hkey : (c + e + 1) * s ≤ x * (s - x) := by
    have hd : s ≤ 2 * (s - x) := by omega
    calc (c + e + 1) * s ≤ (c + e + 1) * (2 * (s - x)) := Nat.mul_le_mul_left _ hd
      _ = x * (s - x) := by rw [hx]; ring
  have hlin : c * s + e ≤ (c + e + 1) * s := by
    have hs1 : 1 ≤ s := by omega
    nlinarith
  omega

/-- Beyond an explicit threshold, `d · size n + e ≤ n`. -/
theorem exists_size_linear_threshold (d e : ℕ) :
    ∃ T : ℕ, ∀ n : ℕ, T ≤ n → d * Nat.size n + e ≤ n := by
  refine ⟨2 ^ (4 * (d + (d + e) + 1)), fun n hn => ?_⟩
  set S0 := 4 * (d + (d + e) + 1) with hS0
  have hsize : S0 + 1 ≤ Nat.size n := by
    have h := Nat.size_le_size hn
    simpa [Nat.size_pow] using h
  obtain ⟨t, ht'⟩ : ∃ t, Nat.size n = t + 1 := ⟨Nat.size n - 1, by omega⟩
  have hlow : 2 ^ t ≤ n := by
    by_contra hcon
    push_neg at hcon
    have h := Nat.size_le.mpr hcon
    omega
  have hkey : d * t + (d + e) ≤ 2 ^ t :=
    linear_le_two_pow d (d + e) t (by omega)
  have hds : d * Nat.size n + e = d * t + (d + e) := by
    rw [ht']; ring
  omega

/-! ### Swapping the components of a plain pair code -/

/-- Plain complexity is invariant under swapping the two halves of a canonical
pair code, up to a uniform additive constant. -/
theorem plainK_swap_value_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x y : BitString) (kxy kyx : ℕ),
      HasPlainComplexityValue V (pairCode x y) kxy →
      HasPlainComplexityValue V (pairCode y x) kyx →
      kyx ≤ kxy + c := by
  obtain ⟨c, hc⟩ := condK_swapPairCode_le V hV
  refine ⟨c, fun x y kxy kyx hxy hyx => ?_⟩
  have h := hc x y []
  unfold HasPlainComplexityValue plainK at hxy hyx
  rw [hxy, hyx] at h
  exact_mod_cast h

/-! ### Linear bounds on projection type-logs -/

/-- A histogram on an alphabet with `m` letters has multinomial coefficient at
most `m ^ (total mass)`. -/
theorem multinomial_le_pow_card_of_equiv {α : Type*} [Fintype α]
    {m : ℕ} (e : α ≃ Fin m) (f : α → ℕ) :
    Nat.multinomial univ f ≤ m ^ (∑ a, f a) := by
  classical
  have hmul : Nat.multinomial univ (f ∘ e.symm) = Nat.multinomial univ f :=
    multinomial_comp_equiv e.symm f
  have hsum : ∑ i, (f ∘ e.symm) i = ∑ a, f a := Equiv.sum_comp e.symm f
  calc Nat.multinomial univ f = Nat.multinomial univ (f ∘ e.symm) := hmul.symm
    _ ≤ m ^ (∑ i, (f ∘ e.symm) i) := multinomial_le_pow_card_fin _
    _ = m ^ (∑ a, f a) := by rw [hsum]

/-- The two-coordinate type-log of a length-`N` sample is at most `2 N + 1`. -/
theorem histogramTypeLog_pair_le {f : Bool × Bool → ℕ} {n : ℕ} (hsum : ∑ p, f p = n) :
    histogramTypeLog f ≤ 2 * n + 1 := by
  unfold histogramTypeLog
  have hle : Nat.multinomial univ f ≤ 4 ^ n := by
    have h := multinomial_le_pow_card_of_equiv chainPairAlphabetEquiv f
    rwa [hsum] at h
  calc Nat.size (Nat.multinomial univ f) ≤ Nat.size (4 ^ n) := Nat.size_le_size hle
    _ = 2 * n + 1 := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, Nat.size_pow]

/-- The three-coordinate type-log of a length-`N` sample is at most `3 N + 1`. -/
theorem histogramTypeLog_triple_le {f : (Bool × Bool) × Bool → ℕ} {n : ℕ}
    (hsum : ∑ p, f p = n) :
    histogramTypeLog f ≤ 3 * n + 1 := by
  unfold histogramTypeLog
  have hle : Nat.multinomial univ f ≤ 8 ^ n := by
    have h := multinomial_le_pow_card_of_equiv chainTripleAlphabetEquiv f
    rwa [hsum] at h
  calc Nat.size (Nat.multinomial univ f) ≤ Nat.size (8 ^ n) := Nat.size_le_size hle
    _ = 3 * n + 1 := by
        rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_mul, Nat.size_pow]

/-! ### Total mass of the projected histograms -/

/-- Total count over the two-bit product alphabet equals the list length.
Stated for the `BEq` instance used by `chainWordAt_pair_count`. -/
private theorem sum_count_prod_eq_length (L : List (Bool × Bool)) :
    ∑ p : Bool × Bool, L.count p = L.length := by
  rw [length_eq_sum_count_fintype]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [List.count]
  exact List.countP_congr (fun x _ => by simp only [beq_iff_eq])

/-- Total count over the three-bit product alphabet equals the list length. -/
private theorem sum_count_triple_eq_length (L : List ((Bool × Bool) × Bool)) :
    ∑ p : (Bool × Bool) × Bool, L.count p = L.length := by
  rw [length_eq_sum_count_fintype]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [List.count]
  exact List.countP_congr (fun x _ => by simp only [beq_iff_eq])

/-- The two-coordinate histogram of a maximal sample has total mass `N`. -/
theorem chainHistogram2_sum_eq {k Q N : ℕ} {D : ChainDist k} {hQ : D.RationalAtoms Q}
    {W : List (Fin (2 * k + 2) → Bool)} {kW : ℕ} {V : Map}
    (hsample : IsMaximalChainSample V D hQ N W kW) (hdiv : Q ∣ N)
    (i j : Fin (2 * k + 2)) :
    ∑ p : Bool × Bool, chainHistogram2 D hQ N i j p.1 p.2 = N := by
  have hlen : (W.map (fun v => (v i, v j))).length = N := by
    rw [List.length_map]
    exact hsample.length_eq hdiv
  have hstep : ∑ p : Bool × Bool, chainHistogram2 D hQ N i j p.1 p.2
      = ∑ p : Bool × Bool, (W.map (fun v => (v i, v j))).count p :=
    Finset.sum_congr rfl
      (fun p _ => (chainWordAt_pair_count hsample.counts i j p.1 p.2).symm)
  exact hstep.trans ((sum_count_prod_eq_length _).trans hlen)

/-- The three-coordinate histogram of a maximal sample has total mass `N`. -/
theorem chainHistogram3_sum_eq {k Q N : ℕ} {D : ChainDist k} {hQ : D.RationalAtoms Q}
    {W : List (Fin (2 * k + 2) → Bool)} {kW : ℕ} {V : Map}
    (hsample : IsMaximalChainSample V D hQ N W kW) (hdiv : Q ∣ N)
    (i j l : Fin (2 * k + 2)) :
    ∑ p : (Bool × Bool) × Bool, chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2 = N := by
  have hlen : (W.map (fun v => ((v i, v j), v l))).length = N := by
    rw [List.length_map]
    exact hsample.length_eq hdiv
  have hstep : ∑ p : (Bool × Bool) × Bool, chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2
      = ∑ p : (Bool × Bool) × Bool, (W.map (fun v => ((v i, v j), v l))).count p :=
    Finset.sum_congr rfl
      (fun p _ => (chainWordAt_triple_count hsample.counts i j l p.1.1 p.1.2 p.2).symm)
  exact hstep.trans ((sum_count_triple_eq_length _).trans hlen)

/-! ### Linear bounds on projection complexities -/

/-- Two-coordinate projection complexities of a maximal sample are linear in
the sample length. -/
theorem chain_pair_value_le_linear_N (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ A B : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N)
      (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ (i j : Fin (2 * k + 2)) (kij : ℕ),
        HasPlainComplexityValue V (pairCode (chainWordAt W i) (chainWordAt W j)) kij →
        kij ≤ A * N + B := by
  obtain ⟨C, hC⟩ := chain_pair_projection_complexity_close V hV k
  refine ⟨C + 2, 2 * C + 1, fun D Q N hQ hdiv W kW hsample i j kij hkij => ?_⟩
  obtain ⟨kij', hkij', _, hUpper⟩ := hC D Q N hQ hdiv W kW hsample i j
  have heq : kij = kij' := by
    have h1 : (kij : ENat) = (kij' : ENat) := hkij.symm.trans hkij'
    exact_mod_cast h1
  have htype : histogramTypeLog (fun p : Bool × Bool =>
      chainHistogram2 D hQ N i j p.1 p.2) ≤ 2 * N + 1 :=
    histogramTypeLog_pair_le (chainHistogram2_sum_eq hsample hdiv i j)
  have hlog := logSlack_le_linear C N
  calc kij = kij' := heq
    _ ≤ histogramTypeLog (fun p : Bool × Bool =>
          chainHistogram2 D hQ N i j p.1 p.2) + logSlack C (N + 1) := hUpper
    _ ≤ (2 * N + 1) + (C * N + 2 * C) := Nat.add_le_add htype hlog
    _ = (C + 2) * N + (2 * C + 1) := by ring

/-- Three-coordinate projection complexities of a maximal sample are linear in
the sample length. -/
theorem chain_triple_value_le_linear_N (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ A B : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N)
      (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ (i j l : Fin (2 * k + 2)) (kijl : ℕ),
        HasPlainComplexityValue V
          (pairCode (chainPairAt W i j) (chainWordAt W l)) kijl →
        kijl ≤ A * N + B := by
  obtain ⟨C, hC⟩ := chain_triple_projection_complexity_close V hV k
  refine ⟨C + 3, 2 * C + 1, fun D Q N hQ hdiv W kW hsample i j l kijl hkijl => ?_⟩
  obtain ⟨kijl', hkijl', _, hUpper⟩ := hC D Q N hQ hdiv W kW hsample i j l
  have heq : kijl = kijl' := by
    have h1 : (kijl : ENat) = (kijl' : ENat) := hkijl.symm.trans hkijl'
    exact_mod_cast h1
  have htype : histogramTypeLog (fun p : (Bool × Bool) × Bool =>
      chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) ≤ 3 * N + 1 :=
    histogramTypeLog_triple_le (chainHistogram3_sum_eq hsample hdiv i j l)
  have hlog := logSlack_le_linear C N
  calc kijl = kijl' := heq
    _ ≤ histogramTypeLog (fun p : (Bool × Bool) × Bool =>
          chainHistogram3 D hQ N i j l p.1.1 p.1.2 p.2) + logSlack C (N + 1) := hUpper
    _ ≤ (3 * N + 1) + (C * N + 2 * C) := Nat.add_le_add htype hlog
    _ = (C + 3) * N + (2 * C + 1) := by ring

/-! ### Complexity form of the top independence defect -/

/-- **Top independence, complexity form.**  If two coordinates of the chain are
independent, then on one maximal sample their projections have (almost)
additive plain complexity. -/
theorem chain_top_plainK_defect (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N)
      (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ (A B : Fin (2 * k + 2)), D.IndepCoords A B →
      ∀ (ka kb kab : ℕ),
        HasPlainComplexityValue V (chainWordAt W A) ka →
        HasPlainComplexityValue V (chainWordAt W B) kb →
        HasPlainComplexityValue V (pairCode (chainWordAt W A) (chainWordAt W B)) kab →
        ka + kb ≤ kab + logSlack C (N + 1) := by
  obtain ⟨c1, h1⟩ := chain_single_projection_complexity_close V hV k
  obtain ⟨c2, h2⟩ := chain_pair_projection_complexity_close V hV k
  refine ⟨2 * c1 + c2 + 4, ?_⟩
  intro D Q N hQ hdiv W kW hsample A B hindep ka kb kab hka hkb hkab
  obtain ⟨ka', hka', _, hkaUp⟩ := h1 D Q N hQ hdiv W kW hsample A
  obtain ⟨kb', hkb', _, hkbUp⟩ := h1 D Q N hQ hdiv W kW hsample B
  obtain ⟨kab', hkab', hkabLow, _⟩ := h2 D Q N hQ hdiv W kW hsample A B
  have ea : ka = ka' := by
    have h : (ka : ENat) = (ka' : ENat) := hka.symm.trans hka'
    exact_mod_cast h
  have eb : kb = kb' := by
    have h : (kb : ENat) = (kb' : ENat) := hkb.symm.trans hkb'
    exact_mod_cast h
  have eab : kab = kab' := by
    have h : (kab : ENat) = (kab' : ENat) := hkab.symm.trans hkab'
    exact_mod_cast h
  have hdef : histogramTypeLog (fun a => chainHistogram1 D hQ N A a) +
      histogramTypeLog (fun b => chainHistogram1 D hQ N B b) ≤
      histogramTypeLog (fun p : Bool × Bool => chainHistogram2 D hQ N A B p.1 p.2) +
        4 * Nat.size (N + 1) + 1 :=
    chain_top_mutualInformation_defect D hQ N hdiv A B hindep
  have hsizefold : 4 * Nat.size (N + 1) + 1 ≤ logSlack 4 (N + 1) := by
    unfold logSlack
    rw [Nat.size_eq_bits_len]
    omega
  have hfold : logSlack c1 (N + 1) + logSlack c1 (N + 1) + logSlack c2 (N + 1) +
      logSlack 4 (N + 1) = logSlack (2 * c1 + c2 + 4) (N + 1) := by
    unfold logSlack; ring
  omega

/-! ### Complexity form of the per-link conditional-independence defect -/

/-- **Conditional independence at a link, complexity form.**  If `A` and `B` are
conditionally independent given `Wc`, then on one maximal sample the projections
satisfy `C(a | w) + C(b | w) ≤ C(a, b | w) + O(log N)`. -/
theorem chain_link_condK_defect (V : Map) (hV : isOptimalConditional V) (k : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N)
      (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ (A B Wc : Fin (2 * k + 2)), D.CondIndepCoords A B Wc →
      ∀ (kaw kbw kabw : ℕ),
        HasPlainConditionalComplexityValue V (chainWordAt W A) (chainWordAt W Wc) kaw →
        HasPlainConditionalComplexityValue V (chainWordAt W B) (chainWordAt W Wc) kbw →
        HasPlainConditionalComplexityValue V
          (pairCode (chainWordAt W A) (chainWordAt W B)) (chainWordAt W Wc) kabw →
        kaw + kbw ≤ kabw + logSlack C (N + 1) := by
  obtain ⟨cSoI, hSoI⟩ := pairPlainK_symmetryOfInformation_values V hV
  obtain ⟨cSwap, hSwap⟩ := plainK_swap_value_le V hV
  obtain ⟨c1, h1⟩ := chain_single_projection_complexity_close V hV k
  obtain ⟨c2, h2⟩ := chain_pair_projection_complexity_close V hV k
  obtain ⟨c3, h3⟩ := chain_triple_projection_complexity_close V hV k
  obtain ⟨A2, B2, hLin2⟩ := chain_pair_value_le_linear_N V hV k
  obtain ⟨A3, B3, hLin3⟩ := chain_triple_value_le_linear_N V hV k
  set Amax := A2 + A3 + 1 with hAmax
  set Bmax := B2 + B3 + cSwap + 1 with hBmax
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cSoI Amax Bmax
  refine ⟨3 * cFold + 2 * c2 + c1 + c3 + 8 + 3 * cSwap, ?_⟩
  intro D Q N hQ hdiv W kW hsample A B Wc hcond kaw kbw kabw hkaw hkbw hkabw
  set a := chainWordAt W A with ha
  set b := chainWordAt W B with hb
  set w := chainWordAt W Wc with hw
  -- exact plain values of the auxiliary codes
  obtain ⟨kw, hkw⟩ := exists_plainComplexityValue V hV w
  obtain ⟨kwa, hkwa⟩ := exists_plainComplexityValue V hV (pairCode w a)
  obtain ⟨kwb, hkwb⟩ := exists_plainComplexityValue V hV (pairCode w b)
  obtain ⟨kwab, hkwab⟩ := exists_plainComplexityValue V hV (pairCode w (pairCode a b))
  obtain ⟨kaw2, hkaw2⟩ := exists_plainComplexityValue V hV (pairCode a w)
  obtain ⟨kbw2, hkbw2⟩ := exists_plainComplexityValue V hV (pairCode b w)
  obtain ⟨kabw2, hkabw2⟩ := exists_plainComplexityValue V hV (pairCode (pairCode a b) w)
  -- symmetry of information
  have hS1 := (hSoI w a kw kaw kwa hkw hkaw hkwa).2
  have hS2 := (hSoI w b kw kbw kwb hkw hkbw hkwb).2
  have hS3 := (hSoI w (pairCode a b) kw kabw kwab hkw hkabw hkwab).1
  -- swaps
  have hsw1 : kwa ≤ kaw2 + cSwap := hSwap a w kaw2 kwa hkaw2 hkwa
  have hsw2 : kwb ≤ kbw2 + cSwap := hSwap b w kbw2 kwb hkbw2 hkwb
  have hsw3 : kabw2 ≤ kwab + cSwap :=
    hSwap w (pairCode a b) kwab kabw2 hkwab hkabw2
  have hsw4 : kwab ≤ kabw2 + cSwap :=
    hSwap (pairCode a b) w kabw2 kwab hkabw2 hkwab
  -- closeness of complexities and type-logs
  obtain ⟨u2, hu2, _, hu2Up⟩ := h2 D Q N hQ hdiv W kW hsample A Wc
  obtain ⟨v2, hv2, _, hv2Up⟩ := h2 D Q N hQ hdiv W kW hsample B Wc
  obtain ⟨u1, hu1, hu1Low, _⟩ := h1 D Q N hQ hdiv W kW hsample Wc
  obtain ⟨u3, hu3, hu3Low, _⟩ := h3 D Q N hQ hdiv W kW hsample A B Wc
  have eu2 : kaw2 = u2 := by
    have h : (kaw2 : ENat) = (u2 : ENat) := hkaw2.symm.trans hu2
    exact_mod_cast h
  have ev2 : kbw2 = v2 := by
    have h : (kbw2 : ENat) = (v2 : ENat) := hkbw2.symm.trans hv2
    exact_mod_cast h
  have eu1 : kw = u1 := by
    have h : (kw : ENat) = (u1 : ENat) := hkw.symm.trans hu1
    exact_mod_cast h
  have eu3 : kabw2 = u3 := by
    have h : (kabw2 : ENat) = (u3 : ENat) := hkabw2.symm.trans hu3
    exact_mod_cast h
  -- the histogram-level defect
  have hdef : histogramTypeLog (fun p : Bool × Bool =>
        chainHistogram2 D hQ N A Wc p.1 p.2) +
      histogramTypeLog (fun p : Bool × Bool => chainHistogram2 D hQ N B Wc p.1 p.2) ≤
      histogramTypeLog (fun c => chainHistogram1 D hQ N Wc c) +
        histogramTypeLog (fun p : (Bool × Bool) × Bool =>
          chainHistogram3 D hQ N A B Wc p.1.1 p.1.2 p.2) +
        8 * Nat.size (N + 1) + 1 :=
    chain_link_mutualInformation_defect D hQ N hdiv A B Wc hcond
  -- linear bounds, to fold the symmetry-of-information slacks
  have hlin_wa : kwa ≤ A2 * N + B2 := hLin2 D Q N hQ hdiv W kW hsample Wc A kwa hkwa
  have hlin_wb : kwb ≤ A2 * N + B2 := hLin2 D Q N hQ hdiv W kW hsample Wc B kwb hkwb
  have hlin_abw : kabw2 ≤ A3 * N + B3 :=
    hLin3 D Q N hQ hdiv W kW hsample A B Wc kabw2 hkabw2
  have hfold_of : ∀ m : ℕ, m + 1 ≤ Amax * (N + 1) + Bmax →
      logSlack cSoI (m + 1) ≤ logSlack cFold (N + 1) := by
    intro m hm
    exact (logSlack_mono_right cSoI hm).trans (hFold (N + 1))
  have hbound_wa : kwa + 1 ≤ Amax * (N + 1) + Bmax := by
    have : A2 * N + B2 + 1 ≤ Amax * (N + 1) + Bmax := by
      have h1' : A2 * N ≤ Amax * (N + 1) := by
        calc A2 * N ≤ A2 * (N + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ Amax * (N + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  have hbound_wb : kwb + 1 ≤ Amax * (N + 1) + Bmax := by
    have : A2 * N + B2 + 1 ≤ Amax * (N + 1) + Bmax := by
      have h1' : A2 * N ≤ Amax * (N + 1) := by
        calc A2 * N ≤ A2 * (N + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ Amax * (N + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  have hbound_wab : kwab + 1 ≤ Amax * (N + 1) + Bmax := by
    have h1' : A3 * N ≤ Amax * (N + 1) := by
      calc A3 * N ≤ A3 * (N + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ Amax * (N + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hS1' := hfold_of kwa hbound_wa
  have hS2' := hfold_of kwb hbound_wb
  have hS3' := hfold_of kwab hbound_wab
  have hsizefold : 8 * Nat.size (N + 1) + 1 ≤ logSlack 8 (N + 1) := by
    unfold logSlack
    rw [Nat.size_eq_bits_len]
    omega
  have hswapfold : 3 * cSwap ≤ logSlack (3 * cSwap) (N + 1) := by
    unfold logSlack
    omega
  have hfold : logSlack cFold (N + 1) + logSlack cFold (N + 1) + logSlack cFold (N + 1) +
      logSlack c2 (N + 1) + logSlack c2 (N + 1) + logSlack c1 (N + 1) +
      logSlack c3 (N + 1) + logSlack 8 (N + 1) + logSlack (3 * cSwap) (N + 1) =
      logSlack (3 * cFold + 2 * c2 + c1 + c3 + 8 + 3 * cSwap) (N + 1) := by
    unfold logSlack; ring
  omega

/-! ### The regime of very complex `z` -/

/-- `logSlack c n` is bounded by a linear function of `n`. -/
theorem logSlack_le_self_linear (c n : ℕ) : logSlack c n ≤ c * n + c := by
  unfold logSlack
  rw [Nat.size_eq_bits_len]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left c (size_le_self n)) c

/-- **Conditional decomposition of plain complexity.**
`C(z) ≤ C(z | x) + C(x) + O(log (C(x) + C(z)))`. -/
theorem plainK_le_cond_add_of_value (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x z : BitString) (kz kzx kx : ℕ),
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V z x kzx →
      HasPlainComplexityValue V x kx →
      kz ≤ kzx + kx + logSlack c (kx + kz + 1) := by
  obtain ⟨cDrop, hDrop⟩ := condK_drop_left V hV
  obtain ⟨cSoI, hSoI⟩ := pairPlainK_symmetryOfInformation_values V hV
  obtain ⟨cP, hP⟩ := condK_pair_le_add V hV
  obtain ⟨C1, hC1⟩ := logSlack_linear_bound cSoI (1 + cP) (cP + 1)
  refine ⟨C1 + cDrop, fun x z kz kzx kx hkz hkzx hkx => ?_⟩
  obtain ⟨kxz, hkxz⟩ := exists_plainComplexityValue V hV (pairCode x z)
  -- projecting the pair back onto `z`
  have hdrop : kz ≤ kxz + cDrop :=
    hDrop x z [] kxz kz (hasCondValue_nil_of_hasPlainValue hkxz)
      (hasCondValue_nil_of_hasPlainValue hkz)
  -- symmetry of information
  have hsoi := (hSoI x z kx kzx kxz hkx hkzx hkxz).1
  -- crude upper bound on the pair complexity
  have hpair : kxz ≤ kx + kz + logSlack cP (kx + kz + 1) := by
    have h := hP x z [] kx kz (hasCondValue_nil_of_hasPlainValue hkx)
      (hasCondValue_nil_of_hasPlainValue hkz)
    have hval : plainK V (pairCode x z) = (kxz : ENat) := hkxz
    unfold plainK at hval
    rw [hval] at h
    exact_mod_cast h
  have hcrude : kxz + 1 ≤ (1 + cP) * (kx + kz + 1) + (cP + 1) := by
    have hlin := logSlack_le_self_linear cP (kx + kz + 1)
    nlinarith [hpair, hlin]
  have hslack : logSlack cSoI (kxz + 1) ≤ logSlack C1 (kx + kz + 1) :=
    (logSlack_mono_right cSoI hcrude).trans (hC1 (kx + kz + 1))
  have hfold : logSlack C1 (kx + kz + 1) + cDrop ≤ logSlack (C1 + cDrop) (kx + kz + 1) := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits (kx + kz + 1)).length)]
  omega

/-- **Large-complexity regime.**  If `C(z)` exceeds a fixed threshold plus four
times `C(x) + C(y)`, then `C(z) ≤ C(z | x) + C(z | y)` outright. -/
theorem large_complexity_case (V : Map) (hV : isOptimalConditional V) :
    ∃ E : ℕ, ∀ (x y z : BitString) (kz kzx kzy kx ky : ℕ),
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V z x kzx →
      HasPlainConditionalComplexityValue V z y kzy →
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V y ky →
      E + 4 * (kx + ky) ≤ kz →
      kz ≤ kzx + kzy := by
  obtain ⟨c, hc⟩ := plainK_le_cond_add_of_value V hV
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound c 2 1
  obtain ⟨T1, hT1⟩ := exists_size_linear_threshold (4 * C2) (4 * C2)
  refine ⟨T1, fun x y z kz kzx kzy kx ky hkz hkzx hkzy hkx hky hbig => ?_⟩
  have hx := hc x z kz kzx kx hkz hkzx hkx
  have hy := hc y z kz kzy ky hkz hkzy hky
  have hbx : kx + kz + 1 ≤ 2 * kz + 1 := by omega
  have hby : ky + kz + 1 ≤ 2 * kz + 1 := by omega
  have hsx : logSlack c (kx + kz + 1) ≤ logSlack C2 kz :=
    (logSlack_mono_right c hbx).trans (hC2 kz)
  have hsy : logSlack c (ky + kz + 1) ≤ logSlack C2 kz :=
    (logSlack_mono_right c hby).trans (hC2 kz)
  have hval : logSlack C2 kz = C2 * Nat.size kz + C2 := by
    unfold logSlack; rw [Nat.size_eq_bits_len]
  have hthr : 4 * C2 * Nat.size kz + 4 * C2 ≤ kz := hT1 kz (by omega)
  have hthr' : 4 * (C2 * Nat.size kz) + 4 * C2 ≤ kz := by
    rw [← Nat.mul_assoc]; exact hthr
  omega

/-! ### Value-form helpers for condition monotonicity -/

/-- Value form of `condK ≤ plainK + O(1)`. -/
theorem condK_le_plain_value (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x s : BitString) (kxs kx : ℕ),
      HasPlainConditionalComplexityValue V x s kxs →
      HasPlainComplexityValue V x kx → kxs ≤ kx + c := by
  obtain ⟨c, hc⟩ := condKLePlainK V hV
  refine ⟨c, fun x s kxs kx h1 h2 => ?_⟩
  have h := hc x s
  unfold HasPlainConditionalComplexityValue at h1
  unfold HasPlainComplexityValue at h2
  rw [h1, h2] at h
  exact_mod_cast h

/-- Value form of `C(x | pairCode s t) ≤ C(x | s) + O(1)`. -/
theorem condK_condPair_left_value (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x s t : BitString) (kxst kxs : ℕ),
      HasPlainConditionalComplexityValue V x (pairCode s t) kxst →
      HasPlainConditionalComplexityValue V x s kxs → kxst ≤ kxs + c := by
  obtain ⟨c, hc⟩ := condK_condPair_left_le V hV
  refine ⟨c, fun x s t kxst kxs h1 h2 => ?_⟩
  have h := hc x s t
  unfold HasPlainConditionalComplexityValue at h1 h2
  rw [h1, h2] at h
  exact_mod_cast h

/-! ### The per-link and top complexity steps -/

/-- **Per-link step.**  At a conditionally independent link of the chain, the
conditional complexity of an arbitrary `z` given the upper coordinate is at most
the sum of its conditional complexities given the two lower coordinates. -/
theorem chain_link_condK_step (V : Map) (hV : isOptimalConditional V) (k : ℕ)
    (Az Bz : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N)
      (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ (A B Wc : Fin (2 * k + 2)), D.CondIndepCoords A B Wc →
      ∀ (z : BitString) (kz kza kzb kzw : ℕ),
        HasPlainComplexityValue V z kz → kz ≤ Az * N + Bz →
        HasPlainConditionalComplexityValue V z (chainWordAt W A) kza →
        HasPlainConditionalComplexityValue V z (chainWordAt W B) kzb →
        HasPlainConditionalComplexityValue V z (chainWordAt W Wc) kzw →
        kzw ≤ kza + kzb + logSlack C (N + 1) := by
  obtain ⟨Cb, hbase⟩ := base_conditional_mutualInformation_inequality V hV
  obtain ⟨Cd, hdefect⟩ := chain_link_condK_defect V hV k
  obtain ⟨cmono, hmono⟩ := condK_condPair_left_value V hV
  obtain ⟨c0, hc0⟩ := condK_le_plain_value V hV
  obtain ⟨A1, B1, hLin1⟩ := chain_projection_value_le_linear_N V hV k
  obtain ⟨A2, B2, hLin2⟩ := chain_pair_value_le_linear_N V hV k
  set Amax := 3 * Az + A2 + 2 * A1 with hAmax
  set Bmax := 3 * (Bz + c0) + (B2 + c0) + 2 * (B1 + c0) + 1 with hBmax
  obtain ⟨Cfold, hCfold⟩ := logSlack_linear_bound Cb Amax Bmax
  refine ⟨Cd + Cfold + 2 * cmono, ?_⟩
  intro D Q N hQ hdiv W kW hsample A B Wc hcond z kz kza kzb kzw hkz hkzlin hkza hkzb hkzw
  set a := chainWordAt W A with ha
  set b := chainWordAt W B with hb
  set w := chainWordAt W Wc with hw
  obtain ⟨kabw, hkabw⟩ :=
    exists_plainConditionalComplexityValue V hV (pairCode a b) w
  obtain ⟨kaw, hkaw⟩ := exists_plainConditionalComplexityValue V hV a w
  obtain ⟨kbw, hkbw⟩ := exists_plainConditionalComplexityValue V hV b w
  obtain ⟨kzaw, hkzaw⟩ :=
    exists_plainConditionalComplexityValue V hV z (pairCode a w)
  obtain ⟨kzbw, hkzbw⟩ :=
    exists_plainConditionalComplexityValue V hV z (pairCode b w)
  have hb1 := hbase z a b w kzw kabw kzaw kzbw kaw kbw hkzw hkabw hkzaw hkzbw hkaw hkbw
  have hdef := hdefect D Q N hQ hdiv W kW hsample A B Wc hcond kaw kbw kabw hkaw hkbw hkabw
  have hm1 : kzaw ≤ kza + cmono := hmono z a w kzaw kza hkzaw hkza
  have hm2 : kzbw ≤ kzb + cmono := hmono z b w kzbw kzb hkzbw hkzb
  -- linear bounds on all the values entering the base slack
  obtain ⟨ka, hka⟩ := exists_plainComplexityValue V hV a
  obtain ⟨kb, hkb⟩ := exists_plainComplexityValue V hV b
  obtain ⟨kab, hkab⟩ := exists_plainComplexityValue V hV (pairCode a b)
  have hlin_a : ka ≤ A1 * N + B1 := hLin1 D Q N hQ hdiv W kW hsample A ka hka
  have hlin_b : kb ≤ A1 * N + B1 := hLin1 D Q N hQ hdiv W kW hsample B kb hkb
  have hlin_ab : kab ≤ A2 * N + B2 := hLin2 D Q N hQ hdiv W kW hsample A B kab hkab
  have hz1 : kzw ≤ kz + c0 := hc0 z w kzw kz hkzw hkz
  have hz2 : kzaw ≤ kz + c0 := hc0 z (pairCode a w) kzaw kz hkzaw hkz
  have hz3 : kzbw ≤ kz + c0 := hc0 z (pairCode b w) kzbw kz hkzbw hkz
  have hab1 : kabw ≤ kab + c0 := hc0 (pairCode a b) w kabw kab hkabw hkab
  have haw1 : kaw ≤ ka + c0 := hc0 a w kaw ka hkaw hka
  have hbw1 : kbw ≤ kb + c0 := hc0 b w kbw kb hkbw hkb
  have hT : kzw + kabw + kzaw + kzbw + kaw + kbw + 1 ≤ Amax * (N + 1) + Bmax := by
    have hstep : kzw + kabw + kzaw + kzbw + kaw + kbw + 1 ≤
        (Az * N + (Bz + c0)) + (A2 * N + (B2 + c0)) + (Az * N + (Bz + c0)) +
          (Az * N + (Bz + c0)) + (A1 * N + (B1 + c0)) + (A1 * N + (B1 + c0)) + 1 := by
      gcongr <;> omega
    have hring : (Az * N + (Bz + c0)) + (A2 * N + (B2 + c0)) + (Az * N + (Bz + c0)) +
        (Az * N + (Bz + c0)) + (A1 * N + (B1 + c0)) + (A1 * N + (B1 + c0)) + 1
        = Amax * N + Bmax := by
      rw [hAmax, hBmax]; ring
    have hmono' : Amax * N + Bmax ≤ Amax * (N + 1) + Bmax :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    omega
  have hslack : logSlack Cb (kzw + kabw + kzaw + kzbw + kaw + kbw + 1)
      ≤ logSlack Cfold (N + 1) :=
    (logSlack_mono_right Cb hT).trans (hCfold (N + 1))
  have hmonofold : 2 * cmono ≤ logSlack (2 * cmono) (N + 1) := by
    unfold logSlack; omega
  have hfold : logSlack Cd (N + 1) + logSlack Cfold (N + 1) +
      logSlack (2 * cmono) (N + 1) = logSlack (Cd + Cfold + 2 * cmono) (N + 1) := by
    unfold logSlack; ring
  omega

/-- **Top step.**  At the independent top of the chain, the plain complexity of
an arbitrary `z` is at most the sum of its conditional complexities given the
two top coordinates. -/
theorem chain_top_condK_step (V : Map) (hV : isOptimalConditional V) (k : ℕ)
    (Az Bz : ℕ) :
    ∃ C : ℕ, ∀ (D : ChainDist k) (Q N : ℕ) (hQ : D.RationalAtoms Q) (_hdiv : Q ∣ N)
      (W : List (Fin (2 * k + 2) → Bool)) (kW : ℕ),
      IsMaximalChainSample V D hQ N W kW →
      ∀ (A B : Fin (2 * k + 2)), D.IndepCoords A B →
      ∀ (z : BitString) (kz kza kzb : ℕ),
        HasPlainComplexityValue V z kz → kz ≤ Az * N + Bz →
        HasPlainConditionalComplexityValue V z (chainWordAt W A) kza →
        HasPlainConditionalComplexityValue V z (chainWordAt W B) kzb →
        kz ≤ kza + kzb + logSlack C (N + 1) := by
  obtain ⟨Cb, hbase⟩ := base_conditional_mutualInformation_inequality V hV
  obtain ⟨Ct, htop⟩ := chain_top_plainK_defect V hV k
  obtain ⟨cmono, hmono⟩ := condK_condPair_left_value V hV
  obtain ⟨c0, hc0⟩ := condK_le_plain_value V hV
  obtain ⟨A1, B1, hLin1⟩ := chain_projection_value_le_linear_N V hV k
  obtain ⟨A2, B2, hLin2⟩ := chain_pair_value_le_linear_N V hV k
  set Amax := 3 * Az + A2 + 2 * A1 with hAmax
  set Bmax := 3 * (Bz + c0) + (B2 + c0) + 2 * (B1 + c0) + 1 with hBmax
  obtain ⟨Cfold, hCfold⟩ := logSlack_linear_bound Cb Amax Bmax
  refine ⟨Ct + Cfold + 2 * cmono, ?_⟩
  intro D Q N hQ hdiv W kW hsample A B hindep z kz kza kzb hkz hkzlin hkza hkzb
  set a := chainWordAt W A with ha
  set b := chainWordAt W B with hb
  obtain ⟨ka, hka⟩ := exists_plainComplexityValue V hV a
  obtain ⟨kb, hkb⟩ := exists_plainComplexityValue V hV b
  obtain ⟨kab, hkab⟩ := exists_plainComplexityValue V hV (pairCode a b)
  obtain ⟨kzaNil, hkzaNil⟩ :=
    exists_plainConditionalComplexityValue V hV z (pairCode a [])
  obtain ⟨kzbNil, hkzbNil⟩ :=
    exists_plainConditionalComplexityValue V hV z (pairCode b [])
  have hb1 := hbase z a b [] kz kab kzaNil kzbNil ka kb
    (hasCondValue_nil_of_hasPlainValue hkz) (hasCondValue_nil_of_hasPlainValue hkab)
    hkzaNil hkzbNil
    (hasCondValue_nil_of_hasPlainValue hka) (hasCondValue_nil_of_hasPlainValue hkb)
  have hdef := htop D Q N hQ hdiv W kW hsample A B hindep ka kb kab hka hkb hkab
  have hm1 : kzaNil ≤ kza + cmono := hmono z a [] kzaNil kza hkzaNil hkza
  have hm2 : kzbNil ≤ kzb + cmono := hmono z b [] kzbNil kzb hkzbNil hkzb
  have hlin_a : ka ≤ A1 * N + B1 := hLin1 D Q N hQ hdiv W kW hsample A ka hka
  have hlin_b : kb ≤ A1 * N + B1 := hLin1 D Q N hQ hdiv W kW hsample B kb hkb
  have hlin_ab : kab ≤ A2 * N + B2 := hLin2 D Q N hQ hdiv W kW hsample A B kab hkab
  have hz2 : kzaNil ≤ kz + c0 := hc0 z (pairCode a []) kzaNil kz hkzaNil hkz
  have hz3 : kzbNil ≤ kz + c0 := hc0 z (pairCode b []) kzbNil kz hkzbNil hkz
  have hT : kz + kab + kzaNil + kzbNil + ka + kb + 1 ≤ Amax * (N + 1) + Bmax := by
    have hstep : kz + kab + kzaNil + kzbNil + ka + kb + 1 ≤
        (Az * N + (Bz + c0)) + (A2 * N + (B2 + c0)) + (Az * N + (Bz + c0)) +
          (Az * N + (Bz + c0)) + (A1 * N + (B1 + c0)) + (A1 * N + (B1 + c0)) + 1 := by
      gcongr <;> omega
    have hring : (Az * N + (Bz + c0)) + (A2 * N + (B2 + c0)) + (Az * N + (Bz + c0)) +
        (Az * N + (Bz + c0)) + (A1 * N + (B1 + c0)) + (A1 * N + (B1 + c0)) + 1
        = Amax * N + Bmax := by
      rw [hAmax, hBmax]; ring
    have hmono' : Amax * N + Bmax ≤ Amax * (N + 1) + Bmax :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    omega
  have hslack : logSlack Cb (kz + kab + kzaNil + kzbNil + ka + kb + 1)
      ≤ logSlack Cfold (N + 1) :=
    (logSlack_mono_right Cb hT).trans (hCfold (N + 1))
  have hmonofold : 2 * cmono ≤ logSlack (2 * cmono) (N + 1) := by
    unfold logSlack; omega
  have hfold : logSlack Ct (N + 1) + logSlack Cfold (N + 1) +
      logSlack (2 * cmono) (N + 1) = logSlack (Ct + Cfold + 2 * cmono) (N + 1) := by
    unfold logSlack; ring
  omega

end Kolmogorov
