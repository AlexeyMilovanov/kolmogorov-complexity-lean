/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealCantor

/-!
# The Levin–Schnorr step of SUV p. 170

SUV p. 170 finishes the proof of Theorem 114 with: "knowing the `k`-bit prefix of `α` one
can effectively find a partial sum exceeding it, and that index lies beyond the modulus of
convergence at precision `2^{-k}`; so `K((α)_k) ≥ k - O(1)` and we can use the
Levin–Schnorr theorem without any changes."

This module carries that out.  The two ingredients that were missing are

* `KPPlain_partrec_le` — a **partial** computable map does not increase prefix complexity
  by more than `O(1)` (the library only had the total version `KPPlain_map_le`); the
  search "least `i` with `aᵢ` above the left endpoint of the cell" is genuinely partial;
* `exists_cantorReal_eq` (`Omega/NullRealCantor.lean`) — a binary expansion whose partial
  values stay *strictly* below the value, so that the search always converges.

The conclusion is transported to the reals by Problem 158
(`isMartinLofRandomReal_iff_isMartinLofRandom_cantorReal`).
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ### Partial computable maps and prefix complexity -/

/-- **A partial computable map does not increase conditional prefix complexity by more
than a constant.**  The machine `D (p, y) = f (U (p, y))` is a prefix decompressor because
its domain is contained in that of `U`. -/
theorem KP_partrec_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ (x z y : BitString), z ∈ f x → KP U z y ≤ KP U x y + (c : ENat) := by
  let D : Map := fun pair => (U pair).bind f
  have hD_decomp : isDecompressor D :=
    Partrec.bind hU.isDecompressor (hf.comp Computable.snd)
  have hD_prefix : IsPrefixMachine D := by
    intro y p hp q hq hpre
    have hdom : ∀ s : BitString, (D (s, y)).Dom → (U (s, y)).Dom := by
      intro s hs
      obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 hs
      obtain ⟨v, hv, _⟩ := Part.mem_bind_iff.1 hz
      exact Part.dom_iff_mem.2 ⟨v, hv⟩
    exact hU.isPrefixMachine y (hdom p hp) (hdom q hq) hpre
  have hD : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c, hc⟩ := hU.invariance hD
  refine ⟨c, fun x z y hz => ?_⟩
  refine le_trans (hc z y) ?_
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, hp, rfl⟩
  exact ⟨p, Part.mem_bind_iff.2 ⟨x, hp, hz⟩, rfl⟩

/-- The plain form of `KP_partrec_le`. -/
theorem KPPlain_partrec_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ (x z : BitString), z ∈ f x → KPPlain U z ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := KP_partrec_le U hU f hf
  exact ⟨c, fun x z hz => hc x z [] hz⟩

/-! ### The search for an index beyond the modulus -/

/-- The partial search "least index `i` with `bᵢ` strictly above the left endpoint of the
dyadic cell of `x`", shifted by one so that its value is a strict upper bound for a
modulus. -/
noncomputable def modulusIndex (b : ℕ → ℚ) (x : BitString) : Part BitString :=
  (Nat.rfind (show ℕ →. Bool from fun i => Part.some (decide (dyLeft x < b i)))).map
    (fun i => natToBitString (i + 1))

/-- The modulus index of a computable approximation is partial recursive. -/
theorem partrec_modulusIndex {b : ℕ → ℚ} (hb : Computable b) :
    Partrec (modulusIndex b) := by
  have hpred : Computable₂ (fun (x : BitString) (i : ℕ) => decide (dyLeft x < b i)) :=
    computable₂_ratLt.comp (computable_dyLeft.comp Computable.fst) (hb.comp Computable.snd)
  have hrf : Partrec (fun x : BitString =>
      Nat.rfind (show ℕ →. Bool from fun i =>
      Part.some (decide (dyLeft x < b i)))) := Partrec.rfind hpred
  exact hrf.map ((computable_natToBitString.comp
    (Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1))).to₂)

/-! ### The Levin–Schnorr step -/

/-- **SUV Theorem 114 (p. 170), the Levin–Schnorr step.**  Let `b` be a computable,
non-decreasing sequence of rationals converging to `β ∈ (0,1]` from below.  If for some
constant `c` every index that is strictly beyond *some* `2^{-k}`-modulus has prefix
complexity at least `k - c`, then `β` is Martin-Löf random. -/
theorem isMartinLofRandomReal_of_modulus_bound {U : Map} (hU : IsOptimalPrefixConditional U)
    {b : ℕ → ℚ} (hb : Computable b) (hbmono : Monotone b) {β : ℝ}
    (h0 : 0 < β) (h1 : β ≤ 1) (hle : ∀ n, ((b n : ℚ) : ℝ) ≤ β)
    (hlim : Filter.Tendsto (fun n => ((b n : ℚ) : ℝ)) Filter.atTop (nhds β))
    (h : ∃ c : ℕ, ∀ (k i : ℕ),
      (∃ N : ℕ, N < i ∧ ∀ j, N < j → |β - ((b j : ℚ) : ℝ)| < ((2 : ℝ)⁻¹) ^ k) →
        (k : ℕ∞) ≤ KPNat U i + (c : ℕ∞)) :
    IsMartinLofRandomReal β := by
  classical
  obtain ⟨c, hc⟩ := h
  obtain ⟨c₁, hc₁⟩ := KPPlain_partrec_le U hU (modulusIndex b) (partrec_modulusIndex hb)
  obtain ⟨w, hw, hstrict⟩ := exists_cantorReal_eq h0 h1
  rw [← hw, isMartinLofRandomReal_iff_isMartinLofRandom_cantorReal,
    isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix hU]
  refine ⟨c₁ + c, fun n => ?_⟩
  have hxlt : ((dyLeft (cantorPrefix w n) : ℚ) : ℝ) < β := hstrict n
  -- the search converges, because the left endpoint of the cell is strictly below `β`
  obtain ⟨j0, hj0⟩ := Metric.tendsto_atTop.1 hlim
    (β - ((dyLeft (cantorPrefix w n) : ℚ) : ℝ)) (by linarith)
  have hj0' : ((dyLeft (cantorPrefix w n) : ℚ) : ℝ) < ((b j0 : ℚ) : ℝ) := by
    have hd := hj0 j0 le_rfl
    rw [Real.dist_eq, abs_lt] at hd
    linarith [hd.1]
  have hdom : (Nat.rfind (show ℕ →. Bool from fun i => Part.some
      (decide (dyLeft (cantorPrefix w n) < b i)))).Dom := by
    rw [Nat.rfind_dom]
    refine ⟨j0, ?_, fun {m} _ => trivial⟩
    have hq : dyLeft (cantorPrefix w n) < b j0 := by exact_mod_cast hj0'
    simp only [Part.mem_some_iff]
    exact (decide_eq_true hq).symm
  set i : ℕ := (Nat.rfind (show ℕ →. Bool from fun k => Part.some
      (decide (dyLeft (cantorPrefix w n) < b k)))).get hdom with hi
  have himem : i ∈ Nat.rfind (show ℕ →. Bool from fun k =>
      Part.some (decide (dyLeft (cantorPrefix w n) < b k))) :=
    Part.get_mem hdom
  have hispec : ((dyLeft (cantorPrefix w n) : ℚ) : ℝ) < ((b i : ℚ) : ℝ) := by
    have hs := Nat.rfind_spec himem
    simp only [Part.mem_some_iff] at hs
    have hq : dyLeft (cantorPrefix w n) < b i := of_decide_eq_true hs.symm
    exact_mod_cast hq
  -- `β` is within `2^{-n}` of the left endpoint of the cell
  have hbound : β ≤ ((dyLeft (cantorPrefix w n) : ℚ) : ℝ) + ((2 : ℝ)⁻¹) ^ n := by
    have hmem := cantorReal_mem_binaryClosedInterval w n
    rw [binaryClosedInterval_eq_Icc_dy, Set.mem_Icc, hw] at hmem
    have hd := dyRight_sub_dyLeft (cantorPrefix w n)
    rw [cantorPrefix_length] at hd
    linarith [hmem.2]
  -- hence `i` is a `2^{-n}`-modulus and `i + 1` lies beyond it
  have hmod : ∀ jj, i < jj → |β - ((b jj : ℚ) : ℝ)| < ((2 : ℝ)⁻¹) ^ n := by
    intro jj hjj
    have hmo : ((b i : ℚ) : ℝ) ≤ ((b jj : ℚ) : ℝ) := by exact_mod_cast hbmono hjj.le
    have hup := hle jj
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hkey := hc n (i + 1) ⟨i, lt_add_one i, hmod⟩
  have hmemf : natToBitString (i + 1) ∈ modulusIndex b (cantorPrefix w n) := by
    rw [modulusIndex]
    exact Part.mem_map _ himem
  have hcomp := hc₁ (cantorPrefix w n) (natToBitString (i + 1)) hmemf
  rw [← KPNat_def] at hcomp
  calc (n : ℕ∞) ≤ KPNat U (i + 1) + (c : ℕ∞) := hkey
    _ ≤ (KPPlain U (cantorPrefix w n) + (c₁ : ℕ∞)) + (c : ℕ∞) := by gcongr
    _ = KPPlain U (cantorPrefix w n) + ((c₁ + c : ℕ) : ℕ∞) := by
        push_cast
        ring

end Kolmogorov
