import KolmogorovMathlib.StrongMerging.Lower.MovingSphereGame

/-!
# The sharp lower bound: the moving-sphere reservoir

Blueprint node L23 (`movingSphereReservoir`) of the formalization of `sublinear-merging.tex`
(paper: Lemma `lem:ham-reservoir`, lines ~1370-1505; blueprint: "L22--L23", lines ~4784-4806).

The generic reservoir theorem: for an optimal plain machine `V` and a fixed header exponent `B`,
there is one coding constant `c` such that for all parameters `M, R, K, S, τ, ℓ, δ, h` bounded by
`(M + 2)^B`, with `0 < R`, `2R < M`, `h ≥ 1` and the four game inequalities
(`ReservoirInequalities`), there are a center `z` of length `M` and a set `W ⊆ S_z` with
`8 |W| ≥ 7 N` (`ReservoirOutcome`) such that

* `C(z) ≤ K - log₂ N + c m` (`eq:ham-center-code`), `m = ⌈log₂ (M + 2)⌉`;
* `K ≤ C(u) ≤ K + c m` for `u ∈ W` (`eq:ham-endpoint-code`);
* no point of `W` lies in a cell `Q` of an exact partition program of length at most `S` with
  `|Q| ≥ 2^ℓ` and `C(Q) + log₂ |Q| ≤ K + τ` (`eq:ham-forbidden-cell`).

The final reservoir is selected noncomputably; it is not claimed to have a short description.

This module also provides the **index codes in computable families** used for the endpoint upper
bound here and for the edge upper bound of node L27: a member `x` of a computable list
`fam ps y` (numeric parameters `ps` polynomially bounded in `n`) has
`C(x | y) ≤ log₂ |fam ps y| + O(log n)` (`condC_le_of_mem_family`), hence
`C(x) ≤ C(y) + log₂ |fam ps y| + O(log n)` (`plainC_le_of_mem_family`), with the sphere list
`sphereList R z` as the first instance (`sphere_index_upper`).
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### The outcome of the reservoir lemma -/

/-- **The conclusions of the moving-sphere reservoir lemma** (`lem:ham-reservoir`) for a center
`z` and a reservoir `W`, with the coding constant `c` and `m = ⌈log₂ (M + 2)⌉` (`headerLog M`):
`|z| = M`, `W ⊆ S_z = hammingSphere M z R`, `8 |W| ≥ 7 N` with `N = (M choose R)`,
`C(z) ≤ K - log₂ N + c m`, `K ≤ C(u) ≤ K + c m` on `W`, and the avoidance of every large
low-score cell of every exact partition program of length at most `S`. -/
structure ReservoirOutcome (V : Map) (M R K S τ ℓ c : ℕ) (z : BitString) (W : Finset BitString) :
    Prop where
  /-- The center is an `M`-word. -/
  center_length : z.length = M
  /-- The reservoir lies in the sphere of radius `R` around the center. -/
  subset_sphere : W ⊆ hammingSphere M z R
  /-- The reservoir is dense: `8 |W| ≥ 7 N`. -/
  dense : 7 * M.choose R ≤ 8 * W.card
  /-- The center code (`eq:ham-center-code`): `C(z) ≤ K - log₂ N + c m`. -/
  center_code : plainC V z ≤ K - Real.logb 2 (M.choose R) + c * headerLog M
  /-- The endpoint lower bound (`eq:ham-endpoint-code`): `K ≤ C(u)` on `W`. -/
  endpoint_lower : ∀ u ∈ W, (K : ℝ) ≤ plainC V u
  /-- The endpoint upper bound (`eq:ham-endpoint-code`): `C(u) ≤ K + c m` on `W`. -/
  endpoint_upper : ∀ u ∈ W, plainC V u ≤ K + c * headerLog M
  /-- Avoidance (`eq:ham-forbidden-cell`): no point of `W` lies in a cell `Q` of an exact
  partition program of length at most `S` with `|Q| ≥ 2^ℓ` and `C(Q) + log₂ |Q| ≤ K + τ`. -/
  avoid : ∀ p : BitString, p.length ≤ S → IsCubePartitionProgram M p → ∀ u ∈ W,
    ∀ Q : Finset BitString, produces universalDecompressor p u (canonicalFiniteSetCode Q) →
      2 ^ ℓ ≤ Q.card → setC V Q + Real.logb 2 Q.card ≤ K + τ → False

/-- The reservoir outcome is monotone in the coding constant. -/
theorem ReservoirOutcome.mono {V : Map} {M R K S τ ℓ c c' : ℕ} {z : BitString}
    {W : Finset BitString} (h : ReservoirOutcome V M R K S τ ℓ c z W) (hc : c ≤ c') :
    ReservoirOutcome V M R K S τ ℓ c' z W := by
  have hm : (c : ℝ) * headerLog M ≤ c' * headerLog M :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)
  exact ⟨h.center_length, h.subset_sphere, h.dense, h.center_code.trans (by linarith),
    h.endpoint_lower, fun u hu => (h.endpoint_upper u hu).trans (by linarith), h.avoid⟩

/-! ### Index codes in computable families -/

/-- **The family index decoder**: read an occurrence packet `occurrencePacket ps i` (node L22's
packet format: parameter fields, then the raw index) and print the `i`-th member of `fam ps y`,
where `y` is the condition. -/
def familyIndexDecoder (fam : List ℕ → BitString → List BitString) : Map := fun pr =>
  ((fam (parseOccurrence pr.1).1 pr.2)[(parseOccurrence pr.1).2]? : Part BitString)

/-- The family index decoder is partial recursive for a computable family. -/
theorem familyIndexDecoder_partrec (fam : List ℕ → BitString → List BitString)
    (hfam : Computable₂ fam) : isDecompressor (familyIndexDecoder fam) := by
  have hp : Computable fun pr : BitString × BitString => parseOccurrence pr.1 :=
    parseOccurrence_computable.comp Computable.fst
  exact Computable.ofOption (Computable.list_getElem?.comp
    (hfam.comp (Computable.fst.comp hp) Computable.snd) (Computable.snd.comp hp))

/-- **Conditional index code in a computable family.**  Let `fam ps y` be a computable list of
strings, indexed by a list `ps` of numeric parameters and a condition `y`.  Fix a header exponent
`B` and a number `k` of parameters.  Then there is a constant `c` such that every member `x` of
`fam ps y`, for `ps` of at most `k` entries each at most `(n + 2)^B`, has
`C(x | y) ≤ log₂ |fam ps y| + c ⌈log₂ (n + 2)⌉`: the decoder `familyIndexDecoder` reads the
occurrence packet of `ps` and the index of `x` (`length_occurrencePacket_le`, node L22). -/
theorem condC_le_of_mem_family (V : Map) (hV : isOptimalConditional V)
    (fam : List ℕ → BitString → List BitString) (hfam : Computable₂ fam) (B k : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (ps : List ℕ) (y x : BitString), ps.length ≤ k →
      (∀ q ∈ ps, q ≤ (n + 2) ^ B) → x ∈ fam ps y →
        condC V x y ≤ Real.logb 2 (fam ps y).length + c * headerLog n := by
  obtain ⟨c₀, hc₀⟩ := condC_le_of_decoder V hV (familyIndexDecoder fam)
    (familyIndexDecoder_partrec fam hfam)
  obtain ⟨c₁, hc₁⟩ := length_occurrencePacket_le B k
  refine ⟨c₀ + c₁, fun n ps y x hk hps hx => ?_⟩
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have hprod : x ∈ familyIndexDecoder fam (occurrencePacket ps i, y) := by
    simp only [familyIndexDecoder, parseOccurrence_occurrencePacket,
      List.getElem?_eq_getElem hi, hix, Part.mem_ofOption, Option.mem_def]
  have h1 := hc₀ (occurrencePacket ps i) y x hprod
  have h2 := hc₁ n ps i hk hps
  have hlen : (i : ℝ) + 1 ≤ (fam ps y).length := by exact_mod_cast hi
  have h3 : Real.logb 2 ((i : ℝ) + 1) ≤ Real.logb 2 (fam ps y).length :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) hlen
  have hm : (1 : ℝ) ≤ headerLog n := by exact_mod_cast one_le_headerLog n
  have hc0m : (c₀ : ℝ) ≤ c₀ * headerLog n := by nlinarith [Nat.cast_nonneg (α := ℝ) c₀]
  push_cast
  linarith

/-- **Base-plus-index code in a computable family**: under the hypotheses of
`condC_le_of_mem_family`, if moreover `|y| ≤ n` and `|x| ≤ a n`, then
`C(x) ≤ C(y) + log₂ |fam ps y| + c ⌈log₂ (n + 2)⌉`.  The chain rule `upperComplexityChain_trans`
(with the empty condition) costs `O(log (C(y) + C(x | y) + 2)) = O(log n)`. -/
theorem plainC_le_of_mem_family (V : Map) (hV : isOptimalConditional V)
    (fam : List ℕ → BitString → List BitString) (hfam : Computable₂ fam) (B k a : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (ps : List ℕ) (y x : BitString), ps.length ≤ k →
      (∀ q ∈ ps, q ≤ (n + 2) ^ B) → y.length ≤ n → x.length ≤ a * n → x ∈ fam ps y →
        plainC V x ≤ plainC V y + Real.logb 2 (fam ps y).length + c * headerLog n := by
  obtain ⟨c₁, h₁⟩ := condC_le_of_mem_family V hV fam hfam B k
  obtain ⟨c₂, h₂⟩ := upperComplexityChain_trans V hV
  obtain ⟨blit, hlit⟩ := plainC_le_length_add V hV
  obtain ⟨c₃, h₃⟩ := condC_le_plainC_add V hV
  obtain ⟨c₄, h₄⟩ := logb_linear_le_headerLog (a + 1) (2 * blit + c₃)
  refine ⟨c₁ + c₂ * c₄, fun n ps y x hk hps hy hx hmem => ?_⟩
  have hc : plainC V x ≤ plainC V y + condC V x y +
      c₂ * Real.logb 2 (plainC V y + condC V x y + 2) := h₂ x y []
  have hxy := h₁ n ps y x hk hps hmem
  have hyn : (y.length : ℝ) ≤ n := by exact_mod_cast hy
  have hxn : (x.length : ℝ) ≤ a * n := by exact_mod_cast hx
  have hyb : plainC V y ≤ n + blit := by linarith [hlit y]
  have hxb : condC V x y ≤ a * n + blit + c₃ := by linarith [h₃ x y, hlit x]
  have hpos : 0 < plainC V y + condC V x y + 2 := by
    linarith [plainC_nonneg V y, condC_nonneg V x y]
  have harg : plainC V y + condC V x y + 2 ≤
      ((a + 1 : ℕ) : ℝ) * n + ((2 * blit + c₃ : ℕ) : ℝ) + 2 := by
    push_cast
    linarith
  have hlog : Real.logb 2 (plainC V y + condC V x y + 2) ≤ c₄ * headerLog n :=
    (Real.logb_le_logb_of_le one_lt_two hpos harg).trans (h₄ n)
  have hc2 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) c₂)
  push_cast
  linarith

/-! ### The sphere index code -/

/-- **Sphere index code**: every point `u` of the sphere `S_z` of radius `R ≤ M` around an
`M`-word `z` has `C(u) ≤ C(z) + log₂ (M choose R) + c ⌈log₂ (M + 2)⌉` (describe the center, then
the index of `u` in the full sphere; paper line 1500, `eq:ham-endpoint-code`). -/
theorem sphere_index_upper (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (M R : ℕ) (z u : BitString), z.length = M → R ≤ M →
      u ∈ hammingSphere M z R →
        plainC V u ≤ plainC V z + Real.logb 2 (M.choose R) + c * headerLog M := by
  obtain ⟨c, hc⟩ := plainC_le_of_mem_family V hV (fun ps y => sphereList (ps.getD 0 0) y)
    sphereFamily_computable 1 1 1
  refine ⟨c, fun M R z u hz hR hu => ?_⟩
  have hmem : u ∈ sphereList R z := (mem_sphereList_iff R z u).2 (by rw [hz]; exact hu)
  have hulen : u.length = M := ((mem_hammingSphere_iff_diffSet hz).1 hu).1
  have h : plainC V u ≤ plainC V z + Real.logb 2 (sphereList R z).length + c * headerLog M :=
    hc M [R] z u (by simp)
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; simp only [pow_one]; omega)
      hz.le (by rw [hulen]; omega) hmem
  rwa [length_sphereList, hz] at h

/-! ### L23: the generic reservoir theorem -/

/-- **Log bound for an ordinal below the choice count**: if `(j + 1) N ≤ 32 · 2^K` with `N > 0`
then `log₂ (j + 1) ≤ K + 5 - log₂ N`.

Reference: paper lines 1482-1490 ("`K - log N + O(1)` bits"); blueprint L22. -/
theorem logb_succ_le_of_mul_le {j N K : ℕ} (hN : 0 < N) (h : (j + 1) * N ≤ 32 * 2 ^ K) :
    Real.logb 2 ((j : ℝ) + 1) ≤ K + 5 - Real.logb 2 N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hnat : (j + 1) * N ≤ 2 ^ (K + 5) := by
    have e : 2 ^ (K + 5) = 32 * 2 ^ K := by ring
    rw [e]
    exact h
  have hcast : ((j : ℝ) + 1) * N ≤ (2 : ℝ) ^ (K + 5) := by exact_mod_cast hnat
  have hlog := Real.logb_le_logb_of_le one_lt_two (mul_pos hj hNr) hcast
  rw [Real.logb_mul hj.ne' hNr.ne', Real.logb_pow, Real.logb_self_eq_one one_lt_two] at hlog
  push_cast at hlog
  linarith

/-- **Every emitted center has a short description** (`eq:ham-center-code`): with the header
exponent `B` fixed, there is `c` such that every center emitted by the Hamming game along its event
history has `C(z) ≤ K - log₂ N + c m`.  The center occurrence code (node L22) applied to the
computable prefix-monotone stream `hammingEmit` gives `C(z) ≤ log₂ (j + 1) + c m` for its ordinal
`j`, and the choice count (node L20) gives `(j + 1) N ≤ 32 · 2^K`. -/
theorem emitted_center_code (V : Map) (hV : isOptimalConditional V) (cV cT : Nat.Partrec.Code)
    (B : ℕ) :
    ∃ c : ℕ, ∀ M R K S τ ℓ δ h : ℕ, (∀ q ∈ [M, R, K, S, τ, ℓ, δ, h], q ≤ (M + 2) ^ B) →
      GameHyp (hammingGame M R ℓ δ) K τ S (heavyTheta M R ℓ δ h) → R ≤ M →
      ∀ (s : ℕ) (z : BitString), z ∈ emittedCenters (hammingGame M R ℓ δ)
          (eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ) s) →
        plainC V z ≤ K - Real.logb 2 (M.choose R) + c * headerLog M := by
  obtain ⟨c, hc⟩ := centerOccurrenceCode V hV (hammingEmit cV cT)
    (hammingEmit_computable cV cT) (hammingEmit_mono cV cT) B 8
  refine ⟨c + 5, fun M R K S τ ℓ δ h hps hG hRM s z hz => ?_⟩
  obtain ⟨j, hj, hjz⟩ := List.getElem_of_mem hz
  have hcount := reservoirChoiceCount hG _ (hammingHistory_valid cV cT M R K S τ ℓ δ s)
  have hget : (hammingEmit cV cT [M, R, K, S, τ, ℓ, δ, h] s)[j]? = some z := by
    rw [hammingEmit_eq, List.getElem?_eq_getElem hj, hjz]
  have h1 := hc M [M, R, K, S, τ, ℓ, δ, h] (by simp) hps s j z hget
  have hN : 0 < M.choose R := Nat.choose_pos hRM
  have hmul : (j + 1) * M.choose R ≤ 32 * 2 ^ K := by
    have hc' : M.choose R * (emittedCenters (hammingGame M R ℓ δ)
        (eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ) s)).length ≤
        32 * 2 ^ K := hcount
    calc (j + 1) * M.choose R ≤ (emittedCenters (hammingGame M R ℓ δ)
          (eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ) s)).length *
            M.choose R := Nat.mul_le_mul_right _ hj
      _ ≤ 32 * 2 ^ K := by rw [Nat.mul_comm]; exact hc'
  have h2 := logb_succ_le_of_mul_le hN hmul
  have hm : (1 : ℝ) ≤ headerLog M := by exact_mod_cast one_le_headerLog M
  push_cast
  linarith

/-- **Moving-sphere reservoir** (blueprint node L23, the generic reservoir theorem).  For an
optimal plain machine `V` and a header exponent `B` (fixed before the parameters) there is a
coding constant `c` such that for all parameters `M, R, K, S, τ, ℓ, δ, h ≤ (M + 2)^B` with
`0 < R`, `2R < M`, `h ≥ 1` and the four game inequalities there are a center `z` and a reservoir
`W` with all the conclusions `ReservoirOutcome` of Lemma `lem:ham-reservoir`.

Proof: run the Hamming instance of the generic game (`hammingGame`, `hammingSources`, valid by
`hammingGameHyp`) to its noncomputable final stage (`reservoirStabilizes`, node L21); the final
center and live reservoir are `z, W`.  The center code is `emitted_center_code` (L22 + L20); the
endpoint lower bound is the completeness of point events (`point_event_of_plainC_lt`); the upper
bound is the sphere index code (`sphere_index_upper`); avoidance combines the completeness of set
and table events (`set_event_of_score_le`, `table_event_of_partition`) with the final avoidance
clause of `reservoirStabilizes`. -/
theorem movingSphereReservoir (V : Map) (hV : isOptimalConditional V) (B : ℕ) :
    ∃ c : ℕ, ∀ M R K S τ ℓ δ h : ℕ, 0 < R → 2 * R < M → 1 ≤ h →
      (∀ q ∈ [M, R, K, S, τ, ℓ, δ, h], q ≤ (M + 2) ^ B) →
      ReservoirInequalities M R K S τ ℓ δ h →
      ∃ (z : BitString) (W : Finset BitString), ReservoirOutcome V M R K S τ ℓ c z W := by
  obtain ⟨cV, hcV⟩ := exists_isCodeFor_of_isDecompressor hV.1
  obtain ⟨cT, hcT⟩ := exists_isCodeFor_of_isDecompressor isDecompressor_universalDecompressor
  obtain ⟨c₁, hc₁⟩ := emitted_center_code V hV cV cT B
  obtain ⟨c₂, hc₂⟩ := sphere_index_upper V hV
  refine ⟨c₁ + c₂, fun M R K S τ ℓ δ h hR h2R hh hps hineq => ?_⟩
  have hG : GameHyp (hammingGame M R ℓ δ) K τ S (heavyTheta M R ℓ δ h) :=
    hammingGameHyp hR h2R hh hineq
  obtain ⟨s₀, -, -, hzc, hzem, -, hWsub, hWdense, hpt, hcell⟩ :=
    reservoirStabilizes hG (eventHistory (hammingGame M R ℓ δ) K τ (hammingSources cV cT K S τ))
      (fun s => eventHistory_prefix _ _ _ _ (Nat.le_succ s))
      (hammingHistory_valid cV cT M R K S τ ℓ δ)
  generalize (run (hammingGame M R ℓ δ) (eventHistory (hammingGame M R ℓ δ) K τ
    (hammingSources cV cT K S τ) s₀)).live = W at hWsub hWdense hpt hcell
  generalize (run (hammingGame M R ℓ δ) (eventHistory (hammingGame M R ℓ δ) K τ
    (hammingSources cV cT K S τ) s₀)).center = z at hzc hzem hWsub
  have hzM : z.length = M := (mem_allStrings M z).1 hzc
  have hWS : W ⊆ hammingSphere M z R := by
    rw [← hzM]
    exact hWsub
  have hRM : R ≤ M := by omega
  have hcz : plainC V z ≤ K - Real.logb 2 (M.choose R) + c₁ * headerLog M :=
    hc₁ M R K S τ ℓ δ h hps hG hRM s₀ z hzem
  have hm0 : (0 : ℝ) ≤ headerLog M := Nat.cast_nonneg _
  have hc2m : (0 : ℝ) ≤ c₂ * headerLog M := mul_nonneg (Nat.cast_nonneg _) hm0
  have hlen : ∀ u ∈ W, u.length = M := fun u hu =>
    ((mem_hammingSphere_iff_diffSet hzM).1 (hWS hu)).1
  refine ⟨z, W, ⟨hzM, hWS, hWdense, ?_, ?_, ?_, ?_⟩⟩
  · push_cast
    linarith
  · intro u hu
    by_contra hlt
    obtain ⟨t, ht⟩ := point_event_of_plainC_lt hV hcV cT M R K S τ ℓ δ (hlen u hu)
      (not_le.mp hlt)
    exact hpt t u ht hu
  · intro u hu
    have h1 := hc₂ M R z u hzM hRM (hWS hu)
    push_cast
    linarith
  · intro p hpS hp u hu Q hQ hQℓ hscore
    obtain ⟨Q', hQ'prod, hQ'mem, hQ'all⟩ := hp u (hlen u hu)
    have hQQ' : Q = Q' := canonicalFiniteSetCode_injective (Part.mem_unique hQ hQ'prod)
    subst hQQ'
    obtain ⟨t₁, i, ht₁⟩ := set_event_of_score_le hV hcV cT M R K S τ ℓ δ
      (fun y hy => (hQ'all y hy).1) hQℓ hscore
    obtain ⟨t₂, P, ht₂, hPcells⟩ := table_event_of_partition hcT cV M R K S τ ℓ δ hpS hp
    exact Finset.disjoint_left.mp (hcell t₁ t₂ Q i P ht₁ ht₂ (hPcells u (hlen u hu) Q hQ))
      hQ'mem hu

end Kolmogorov.StrongMerging.Lower
