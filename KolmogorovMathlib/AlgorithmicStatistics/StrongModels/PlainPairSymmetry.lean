import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainSymmetry

/-!
# Pair form of plain symmetry of information

VS40 §7 repeatedly uses the Kolmogorov–Levin lower direction in the shape

`C(x) + C(y | x) ≤ C(x, y) + O(log N)`

for the canonical pair code `pairCode x y`, whenever `C(x)` and `C(x, y)` are
bounded by the budget `N`.  This module bridges the already formalized *prefix*
lower chain `KPPair_chain_lower` to ordinary plain complexity:

* `C(x) ≤ K(x) + O(1)` and `C(y | x) ≤ K(y | x) + O(1)`
  (`plainK_le_KPPlain`, `condK_le_KP`);
* `K(y | x) ≤ K(y | (x, K(x))) + K(K(x)) + O(1)`
  (`KP_cond_remove_short_info`), where the extra term is `O(log N)` by
  `KPPlain_natCode_le_log`;
* `K(x) + K(y | (x, K(x))) ≤ K(x, y) + O(1)` (`KPPair_chain_lower`);
* `K(x, y) ≤ C(x, y) + O(log N)` (`KP_le_condK_of_logSlack_budget`).
-/

namespace Kolmogorov

/-- **Pair symmetry of information, lower direction, for ordinary plain
complexity.**  `C(x) + C(y | x) ≤ C(x, y) + O(log N)` whenever both `C(x)` and
`C(x, y)` are at most the budget `N`. -/
theorem plainK_add_condK_le_plainK_pair
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : Nat, ∀ (x y : BitString) (N : Nat),
      plainK V x ≤ (N : ENat) →
      plainK V (pairCode x y) ≤ (N : ENat) →
      plainK V x + condK V y x ≤
        plainK V (pairCode x y) + (logSlack C N : ENat) := by
  obtain ⟨cB, hB⟩ := KP_le_condK_of_logSlack_budget V U hV hU
  obtain ⟨c1, h1⟩ := condK_le_KP V U hV hU.isPrefixDecompressor
  obtain ⟨cRem, hRem⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cNat, hNat⟩ := KPPlain_natCode_le_log U hU
  obtain ⟨cLow, hLow⟩ := KPPair_chain_lower U hU
  obtain ⟨cLin, hLin⟩ := logSlack_linear_bound 2 (cB + 1) cB
  refine ⟨cB + cLin + (cLow + cNat + cRem + 2 * c1), ?_⟩
  intro x y N hxN hxyN
  obtain ⟨kx, hkx⟩ : ∃ k : Nat, plainK V x = (k : ENat) :=
    ⟨(plainK V x).toNat, (ENat.natCast_toNat (condK_ne_top_of_optimal V hV x [])).symm⟩
  obtain ⟨kxy, hkxy⟩ : ∃ k : Nat, plainK V (pairCode x y) = (k : ENat) :=
    ⟨(plainK V (pairCode x y)).toNat,
      (ENat.natCast_toNat (condK_ne_top_of_optimal V hV (pairCode x y) [])).symm⟩
  have hkxN : kx ≤ N := by rw [hkx] at hxN; exact_mod_cast hxN
  have hkxyN : kxy ≤ N := by rw [hkxy] at hxyN; exact_mod_cast hxyN
  -- The prefix complexity of `x` is finite and bounded by `N + O(log N)`.
  have hKPx : KPPlain U x ≤ ((kx + logSlack cB N : Nat) : ENat) :=
    hB x [] kx N hkx hkxN
  have hKPxTop : KPPlain U x ≠ ⊤ := by
    intro htop
    rw [htop] at hKPx
    exact ENat.natCast_ne_top _ (top_le_iff.mp hKPx)
  set p : Nat := (KPPlain U x).toNat with hpdef
  have hpval : (p : ENat) = KPPlain U x := ENat.natCast_toNat hKPxTop
  have hpvalue : HasPrefixComplexityValue U x p := hpval
  have hple : p ≤ kx + logSlack cB N := by
    have hcast : (p : ENat) ≤ ((kx + logSlack cB N : Nat) : ENat) := by
      rw [hpval]; exact hKPx
    exact_mod_cast hcast
  -- Prefix complexity of the pair, bounded by the plain complexity of the pair.
  have hKPpair : KPPair U x y ≤ ((kxy + logSlack cB N : Nat) : ENat) :=
    hB (pairCode x y) [] kxy N hkxy hkxyN
  -- Removing the complexity field from the condition.
  have hremove :
      KP U y x ≤
        KP U y (prefixComplexityContext x p) + KPPlain U (natCode p)
          + (cRem : ENat) := hRem y x (natCode p)
  have hchain :
      KPPlain U x + KP U y (prefixComplexityContext x p)
        ≤ KPPair U x y + (cLow : ENat) := hLow x y p hpvalue
  -- The complexity of the length field is logarithmic in the budget.
  have hfield :
      KPPlain U (natCode p) ≤ ((2 * (Nat.bits p).length + cNat : Nat) : ENat) := by
    refine (hNat p).trans ?_
    push_cast
    exact le_rfl
  -- Numeric bookkeeping for the logarithmic terms.
  have hMbound : p ≤ (cB + 1) * N + cB := by
    have hlen := length_natBits_le_self N
    have hmul : cB * (Nat.bits N).length ≤ cB * N := Nat.mul_le_mul_left _ hlen
    have hls : logSlack cB N = cB * (Nat.bits N).length + cB := rfl
    nlinarith [hple, hkxN]
  have hlogp : 2 * (Nat.bits p).length + 2 ≤ logSlack cLin N := by
    have hmono : logSlack 2 p ≤ logSlack 2 ((cB + 1) * N + cB) :=
      logSlack_mono_right 2 hMbound
    have hlin := hLin N
    have hls : logSlack 2 p = 2 * (Nat.bits p).length + 2 := rfl
    omega
  have hfinal :
      kxy + logSlack cB N + cLow + (2 * (Nat.bits p).length + cNat)
          + (cRem + 2 * c1)
        ≤ kxy + logSlack (cB + cLin + (cLow + cNat + cRem + 2 * c1)) N := by
    have hsum :
        logSlack cB N + logSlack cLin N
          + (cLow + cNat + cRem + 2 * c1)
          ≤ logSlack (cB + cLin + (cLow + cNat + cRem + 2 * c1)) N := by
      rw [logSlack_add_const]
      exact logSlack_add_const_le (cB + cLin) (cLow + cNat + cRem + 2 * c1) N
    omega
  calc
    plainK V x + condK V y x
        ≤ (KPPlain U x + (c1 : ENat)) + (KP U y x + (c1 : ENat)) := by
          gcongr
          · exact h1 x []
          · exact h1 y x
    _ ≤ (KPPlain U x + (c1 : ENat)) +
          ((KP U y (prefixComplexityContext x p) + KPPlain U (natCode p)
            + (cRem : ENat)) + (c1 : ENat)) := by
          gcongr
    _ = (KPPlain U x + KP U y (prefixComplexityContext x p)) +
          (KPPlain U (natCode p) + ((cRem + 2 * c1 : Nat) : ENat)) := by
          push_cast
          ring
    _ ≤ (KPPair U x y + (cLow : ENat)) +
          (((2 * (Nat.bits p).length + cNat : Nat) : ENat)
            + ((cRem + 2 * c1 : Nat) : ENat)) := by
          gcongr
    _ ≤ (((kxy + logSlack cB N : Nat) : ENat) + (cLow : ENat)) +
          (((2 * (Nat.bits p).length + cNat : Nat) : ENat)
            + ((cRem + 2 * c1 : Nat) : ENat)) := by
          gcongr
    _ = ((kxy + logSlack cB N + cLow + (2 * (Nat.bits p).length + cNat)
            + (cRem + 2 * c1) : Nat) : ENat) := by
          push_cast
          ring
    _ ≤ ((kxy + logSlack (cB + cLin + (cLow + cNat + cRem + 2 * c1)) N : Nat) : ENat) := by
          exact_mod_cast hfinal
    _ = plainK V (pairCode x y)
          + (logSlack (cB + cLin + (cLow + cNat + cRem + 2 * c1)) N : ENat) := by
          rw [hkxy]
          push_cast
          ring

/-- Consumer form for VS40 `rem:add-noise`: if the noise string `y` is
conditionally random given `x` up to loss `epsilon`, then the plain complexity
of the canonical pair is at least `C(x) + |y|`, up to `epsilon` and a
logarithmic term in `|x| + |y|`. -/
theorem plainK_pair_ge_plainK_add_length_of_random
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon kx kxy : Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      kx + y.length ≤
        kxy + epsilon + logSlack c (x.length + y.length) := by
  obtain ⟨C, hC⟩ := plainK_add_condK_le_plainK_pair V U hV hU
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound C 2 (1 + cLen)
  refine ⟨cFold, ?_⟩
  intro x y epsilon kx kxy hkx hkxy hrandom
  set n := x.length + y.length with hn
  set N := 2 * n + (1 + cLen) with hN
  have hxN : plainK V x ≤ (N : ENat) := by
    refine (hLen x).trans ?_
    have hb : x.length + cLen ≤ N := by
      simp only [hN, hn]
      omega
    exact_mod_cast hb
  have hxyN : plainK V (pairCode x y) ≤ (N : ENat) := by
    refine (hLen (pairCode x y)).trans ?_
    have hlen : (pairCode x y).length + cLen ≤ N := by
      rw [length_pairCode]
      simp only [hN, hn]
      omega
    exact_mod_cast hlen
  obtain ⟨s, hs⟩ : ∃ k : Nat, condK V y x = (k : ENat) :=
    ⟨(condK V y x).toNat, (ENat.natCast_toNat (condK_ne_top_of_optimal V hV y x)).symm⟩
  have hys : y.length ≤ s + epsilon := by
    rw [hs] at hrandom
    exact_mod_cast hrandom
  have hsoi := hC x y N hxN hxyN
  rw [hkx, hkxy, hs] at hsoi
  have hsoiNat : kx + s ≤ kxy + logSlack C N := by
    exact_mod_cast hsoi
  have hslack : logSlack C N ≤ logSlack cFold n := hFold n
  omega

end Kolmogorov
