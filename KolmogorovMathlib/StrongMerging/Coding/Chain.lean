import KolmogorovMathlib.StrongMerging.Coding.Programs
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.CommonInformation.ConditionalIndependence.Part01
import KolmogorovMathlib.CommonInformation.Intermediate
import KolmogorovMathlib.Complexity.PairComplexity.ConditionalMinimality

/-!
# Strong merging, coding foundation III: chain rules (U03, L02)

* **U03, `UpperComplexityChain`** (`sublinear-merging.tex`, appendix "Coding lemmas", item 3).
  Real-valued plain chain rules `C(u) + C(v | u) ≤ C(u, v) + c log₂ (C(u, v) + 2)` and
  `C(u, v) ≤ C(u) + C(v | u) + c log₂ (C(u, v) + 2)`, with the error in the joint complexity
  (never in the length of a possibly enormous model code), and the submodularity
  `C(z) + C(a, b) ≤ C(a, z) + C(b, z) + c log₂ (N + 2)`.  They are instances of the library's
  `condK_pairCode_chain_lower_values`, `condK_pairCode_chain_upper_values` and
  `condK_pairCode_submodularity_values` at the empty external condition, which need only plain
  optimality; the context `pairCode u []` is translated to `u` by constant-cost adapters.
* **L02, `plainCodingInterface`.**  The same definitions instantiated for the lower bound:
  finiteness and attainment of complexities, counting of short descriptions, the lower chain rule
  at bounded joint complexity, and the bridge between the concatenation `u ++ v` of two equal
  halves and the pair code `pairCode u v`.

Joint complexity is `pairC V u v = C(pairCode u v)` and mutual information is the signed real
`mutualInfo V u v = C(u) + C(v) - C(u, v)`.
-/

namespace Kolmogorov.StrongMerging

/-- The joint plain complexity `C(u, v) = C(pairCode u v)`, as a real number. -/
noncomputable def pairC (V : Map) (u v : BitString) : ℝ :=
  plainC V (pairCode u v)

/-- The signed plain mutual information `I(u : v) = C(u) + C(v) - C(u, v)`, as a real number; it
may be slightly negative and is never truncated. -/
noncomputable def mutualInfo (V : Map) (u v : BitString) : ℝ :=
  plainC V u + plainC V v - pairC V u v

/-- `pairC` is nonnegative. -/
theorem pairC_nonneg (V : Map) (u v : BitString) : 0 ≤ pairC V u v :=
  plainC_nonneg V _

/-! ### Value adapters and arithmetic leaves -/

/-- For an optimal `V`, `condK V u v` has its natural value as an exact complexity value. -/
theorem hasValue_condK_toNat (V : Map) (hV : isOptimalConditional V) (u v : BitString) :
    HasPlainConditionalComplexityValue V u v (condK V u v).toNat := by
  unfold HasPlainConditionalComplexityValue
  exact (ENat.natCast_toNat (condK_ne_top_of_optimal V hV u v)).symm

/-- **Context adapter, one direction**: `C(v | pairCode u []) ≤ C(v | u) + c`. -/
theorem condC_pairCode_nil_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, condC V v (pairCode u []) ≤ condC V v u + c := by
  obtain ⟨c, hc⟩ := condK_cond_map_le V hV decodeFirst decodeFirst_computable
  refine ⟨c, fun u v => ?_⟩
  have h := hc v (pairCode u [])
  rw [decodeFirst_pairCode] at h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (condK_ne_top_of_optimal V hV v u)
  have h1 : condK V v (pairCode u []) ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have h2 : condC V v u = k := by rw [condC, ← hk, ENat.toNat_natCast]
  rw [h2]
  unfold condC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **Context adapter, other direction**: `C(v | u) ≤ C(v | pairCode u []) + c`. -/
theorem condC_le_condC_pairCode_nil (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, condC V v u ≤ condC V v (pairCode u []) + c := by
  obtain ⟨c, hc⟩ := condK_cond_map_le V hV (fun w => pairCode w [])
    (pairCode_computable.comp (Computable.id.pair (Computable.const [])))
  refine ⟨c, fun u v => ?_⟩
  have h := hc v u
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (condK_ne_top_of_optimal V hV v (pairCode u []))
  have h1 : condK V v u ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have h2 : condC V v (pairCode u []) = k := by rw [condC, ← hk, ENat.toNat_natCast]
  rw [h2]
  unfold condC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- `1 ≤ log₂ (t + 2)` for `t ≥ 0`. -/
theorem one_le_logb_add_two {t : ℝ} (ht : 0 ≤ t) : 1 ≤ Real.logb 2 (t + 2) := by
  rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]
  linarith

/-- The library's logarithmic slack at `k + 1` is at most `3 c log₂ (k + 2)`. -/
theorem logSlack_succ_le_logb (c k : ℕ) :
    (logSlack c (k + 1) : ℝ) ≤ 3 * c * Real.logb 2 ((k : ℝ) + 2) := by
  have h1 := bits_length_le_logb_add_one (m := k + 1) (by omega)
  have h2 : Real.logb 2 ((k + 1 : ℕ) : ℝ) ≤ Real.logb 2 ((k : ℝ) + 2) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by push_cast; linarith)
  have hL := one_le_logb_add_two (Nat.cast_nonneg (α := ℝ) k)
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have h3 : ((Nat.bits (k + 1)).length : ℝ) + 1 ≤ 3 * Real.logb 2 ((k : ℝ) + 2) := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  unfold logSlack
  push_cast
  linarith

/-- Monotonicity of `log₂ (· + 2)` on `[0, ∞)`. -/
theorem logb_add_two_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.logb 2 (s + 2) ≤ Real.logb 2 (t + 2) :=
  Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)

/-- `log₂ (s + 2) ≤ log₂ m + log₂ (N + 2)` when `0 ≤ s ≤ m N` and `m ≥ 1`. -/
theorem logb_add_two_le_of_le_mul {m : ℕ} (hm : 1 ≤ m) {s N : ℝ} (hs : 0 ≤ s) (hN : 0 ≤ N)
    (h : s ≤ m * N) : Real.logb 2 (s + 2) ≤ Real.logb 2 m + Real.logb 2 (N + 2) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : s + 2 ≤ m * (N + 2) := by nlinarith
  calc Real.logb 2 (s + 2) ≤ Real.logb 2 (m * (N + 2)) :=
        Real.logb_le_logb_of_le one_lt_two (by linarith) h1
    _ = Real.logb 2 m + Real.logb 2 (N + 2) :=
        Real.logb_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith))

/-- `log₂ (s + 2) ≤ 3 log₂ (N + 2)` when `0 ≤ s ≤ 4 N`. -/
theorem logb_add_two_le_three_mul {s N : ℝ} (hs : 0 ≤ s) (hN : 0 ≤ N) (h : s ≤ 4 * N) :
    Real.logb 2 (s + 2) ≤ 3 * Real.logb 2 (N + 2) := by
  have h1 : s + 2 ≤ (N + 2) ^ 3 := by nlinarith [sq_nonneg N, mul_nonneg hN (sq_nonneg N)]
  calc Real.logb 2 (s + 2) ≤ Real.logb 2 ((N + 2) ^ 3) :=
        Real.logb_le_logb_of_le one_lt_two (by linarith) h1
    _ = 3 * Real.logb 2 (N + 2) := by
        rw [Real.logb_pow]
        norm_num

/-! ### U03: the chain rules -/

/-- **Node U03, `UpperComplexityChain`, lower direction**:
`C(u) + C(v | u) ≤ C(u, v) + c log₂ (C(u, v) + 2)`. -/
theorem upperComplexityChain_lower (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString,
      plainC V u + condC V v u ≤ pairC V u v + c * Real.logb 2 (pairC V u v + 2) := by
  obtain ⟨c₀, h₀⟩ := condK_pairCode_chain_lower_values V hV
  obtain ⟨ca, ha⟩ := condC_le_condC_pairCode_nil V hV
  refine ⟨3 * c₀ + ca, fun u v => ?_⟩
  have hmain := h₀ u v [] _ _ _ (hasValue_condK_toNat V hV u [])
    (hasValue_condK_toNat V hV v (pairCode u [])) (hasValue_condK_toNat V hV (pairCode u v) [])
  have e1 : ((condK V u []).toNat : ℝ) = plainC V u := rfl
  have e2 : ((condK V v (pairCode u [])).toNat : ℝ) = condC V v (pairCode u []) := rfl
  have e3 : ((condK V (pairCode u v) []).toNat : ℝ) = pairC V u v := rfl
  have hreal := (Nat.cast_le (α := ℝ)).2 hmain
  push_cast at hreal
  rw [e1, e2, e3] at hreal
  have hslack := logSlack_succ_le_logb c₀ (condK V (pairCode u v) []).toNat
  rw [e3] at hslack
  have hL := one_le_logb_add_two (pairC_nonneg V u v)
  have hcaL : (ca : ℝ) ≤ ca * Real.logb 2 (pairC V u v + 2) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hL
  have hca := ha u v
  push_cast
  linarith

/-- **Node U03, `UpperComplexityChain`, upper direction**:
`C(u, v) ≤ C(u) + C(v | u) + c log₂ (C(u, v) + 2)`. -/
theorem upperComplexityChain_upper (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString,
      pairC V u v ≤ plainC V u + condC V v u + c * Real.logb 2 (pairC V u v + 2) := by
  obtain ⟨c₀, h₀⟩ := condK_pairCode_chain_upper_values V hV
  obtain ⟨ca, ha⟩ := condC_pairCode_nil_le V hV
  refine ⟨3 * c₀ + ca, fun u v => ?_⟩
  have hmain := h₀ u v [] _ _ _ (hasValue_condK_toNat V hV u [])
    (hasValue_condK_toNat V hV v (pairCode u [])) (hasValue_condK_toNat V hV (pairCode u v) [])
  have e1 : ((condK V u []).toNat : ℝ) = plainC V u := rfl
  have e2 : ((condK V v (pairCode u [])).toNat : ℝ) = condC V v (pairCode u []) := rfl
  have e3 : ((condK V (pairCode u v) []).toNat : ℝ) = pairC V u v := rfl
  have hreal := (Nat.cast_le (α := ℝ)).2 hmain
  push_cast at hreal
  rw [e1, e2, e3] at hreal
  have hslack := logSlack_succ_le_logb c₀ (condK V (pairCode u v) []).toNat
  rw [e3] at hslack
  have hL := one_le_logb_add_two (pairC_nonneg V u v)
  have hcaL : (ca : ℝ) ≤ ca * Real.logb 2 (pairC V u v + 2) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hL
  have hca := ha u v
  push_cast
  linarith

/-- **Node U03, transitivity form**: `C(u | w) ≤ C(v | w) + C(u | v) +
c log₂ (C(v | w) + C(u | v) + 2)`; with `w = []` it bounds `C(u) ≤ C(v) + C(u | v) + …`, which
bounds the complexity of a model `u` reached from `v` by a short program. -/
theorem upperComplexityChain_trans (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v w : BitString, condC V u w ≤
      condC V v w + condC V u v + c * Real.logb 2 (condC V v w + condC V u v + 2) := by
  obtain ⟨c₀, h₀⟩ := condK_chain_upper_values V hV
  refine ⟨3 * c₀, fun u v w => ?_⟩
  have hmain := h₀ w u v _ _ _ (hasValue_condK_toNat V hV v w) (hasValue_condK_toNat V hV u v)
    (hasValue_condK_toNat V hV u w)
  have e1 : ((condK V v w).toNat : ℝ) = condC V v w := rfl
  have e2 : ((condK V u v).toNat : ℝ) = condC V u v := rfl
  have e3 : ((condK V u w).toNat : ℝ) = condC V u w := rfl
  have hreal := (Nat.cast_le (α := ℝ)).2 hmain
  push_cast at hreal
  rw [e1, e2, e3] at hreal
  have hslack := logSlack_succ_le_logb c₀ ((condK V v w).toNat + (condK V u v).toNat)
  push_cast at hslack
  rw [e1, e2] at hslack
  push_cast
  linarith

/-- **Submodularity** (node U03, used by U05): if `C(z), C(a, b), C(a, z), C(b, z) ≤ N` then
`C(z) + C(a, b) ≤ C(a, z) + C(b, z) + c log₂ (N + 2)`. -/
theorem upperSubmodularity (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (N : ℝ) (a b z : BitString), plainC V z ≤ N → pairC V a b ≤ N →
      pairC V a z ≤ N → pairC V b z ≤ N →
        plainC V z + pairC V a b ≤ pairC V a z + pairC V b z + c * Real.logb 2 (N + 2) := by
  obtain ⟨C, hC⟩ := condK_pairCode_submodularity_values V hV
  refine ⟨9 * C, fun N a b z hz hab haz hbz => ?_⟩
  have hmain := hC a b z [] _ _ _ _ (hasValue_condK_toNat V hV z [])
    (hasValue_condK_toNat V hV (pairCode a b) []) (hasValue_condK_toNat V hV (pairCode a z) [])
    (hasValue_condK_toNat V hV (pairCode b z) [])
  have e1 : ((condK V z []).toNat : ℝ) = plainC V z := rfl
  have e2 : ((condK V (pairCode a b) []).toNat : ℝ) = pairC V a b := rfl
  have e3 : ((condK V (pairCode a z) []).toNat : ℝ) = pairC V a z := rfl
  have e4 : ((condK V (pairCode b z) []).toNat : ℝ) = pairC V b z := rfl
  have hreal := (Nat.cast_le (α := ℝ)).2 hmain
  push_cast at hreal
  rw [e1, e2, e3, e4] at hreal
  have hslack := logSlack_succ_le_logb C ((condK V z []).toNat +
    (condK V (pairCode a b) []).toNat + (condK V (pairCode a z) []).toNat +
    (condK V (pairCode b z) []).toNat)
  have hN : 0 ≤ N := (plainC_nonneg V z).trans hz
  have hsN : (((condK V z []).toNat + (condK V (pairCode a b) []).toNat +
      (condK V (pairCode a z) []).toNat + (condK V (pairCode b z) []).toNat : ℕ) : ℝ) ≤
        4 * N := by
    push_cast
    rw [e1, e2, e3, e4]
    linarith
  have hlog := logb_add_two_le_three_mul (Nat.cast_nonneg _) hN hsN
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have h1 := mul_le_mul_of_nonneg_left hlog hC0
  push_cast
  linarith

/-! ### Projections, swap and a crude joint bound -/

/-- **Left projection**: `C(u) ≤ C(u, v) + c`. -/
theorem plainC_le_pairC_left (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, plainC V u ≤ pairC V u v + c := by
  obtain ⟨c, hc⟩ := plainK_map_le V hV decodeFirst decodeFirst_computable
  refine ⟨c, fun u v => ?_⟩
  have h := hc (pairCode u v)
  rw [decodeFirst_pairCode] at h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV (pairCode u v))
  have h1 : plainK V u ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have h2 : pairC V u v = k := by rw [pairC, plainC, ← hk, ENat.toNat_natCast]
  rw [h2]
  unfold plainC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **Right projection**: `C(v) ≤ C(u, v) + c`. -/
theorem plainC_le_pairC_right (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, plainC V v ≤ pairC V u v + c := by
  obtain ⟨c, hc⟩ := plainK_map_le V hV decodeSecond decodeSecond_computable
  refine ⟨c, fun u v => ?_⟩
  have h := hc (pairCode u v)
  rw [decodeSecond_pairCode] at h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV (pairCode u v))
  have h1 : plainK V v ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have h2 : pairC V u v = k := by rw [pairC, plainC, ← hk, ENat.toNat_natCast]
  rw [h2]
  unfold plainC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **Crude joint bound**: `C(u, v) ≤ 3 C(u) + C(v) + c`. -/
theorem pairC_le_crude (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, pairC V u v ≤ 3 * plainC V u + plainC V v + c := by
  obtain ⟨k, hk⟩ := plainK_pair_le_add_two_log_add_condK V hV
  obtain ⟨c', hc'⟩ := condC_le_plainC_add V hV
  refine ⟨k + c', fun u v => ?_⟩
  have h := hk u v
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV u)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (condK_ne_top_of_optimal V hV v u)
  have hcv : cVal V u = a := by
    unfold cVal
    rw [← ha, ENat.toNat_natCast]
  rw [← ha, ← hb, hcv] at h
  have h' : (cPair V u v).toNat ≤ a + b + (2 * Nat.log 2 a + k) :=
    toNat_le_of_le_natCast (by exact_mod_cast h)
  have hlog : (Nat.log 2 a : ℝ) ≤ a := by exact_mod_cast Nat.log_le_self 2 a
  have e1 : plainC V u = a := by rw [plainC, ← ha, ENat.toNat_natCast]
  have e2 : condC V v u = b := by rw [condC, ← hb, ENat.toNat_natCast]
  have h2 := hc' v u
  rw [e2] at h2
  have e3 : pairC V u v = ((cPair V u v).toNat : ℝ) := rfl
  have h'' : ((cPair V u v).toNat : ℝ) ≤ a + b + (2 * (Nat.log 2 a : ℝ) + k) := by
    exact_mod_cast h'
  rw [e3, e1]
  push_cast
  linarith

/-! ### L02: the plain coding interface -/

namespace Lower

/-- **Attainment** (node L02): an optimal machine has a program of length exactly `C(u | v)`
producing `u` from `v`. -/
theorem exists_program_of_condC (V : Map) (hV : isOptimalConditional V) (u v : BitString) :
    ∃ p : BitString, produces V p v u ∧ (p.length : ℝ) = condC V u v := by
  obtain ⟨p, hp, hlen⟩ := (hasValue_condK_toNat V hV u v).exists_program
  exact ⟨p, hp, by rw [hlen]; rfl⟩

/-- **Counting** (node L02): fewer than `2 ^ k` strings have `C(· | y) < k`. -/
theorem card_lt_two_pow_of_condC_lt (V : Map) (hV : isOptimalConditional V) (y : BitString)
    (k : ℕ) (S : Finset BitString) (hS : ∀ u ∈ S, condC V u y < k) : S.card < 2 ^ k := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    rcases S.eq_empty_or_nonempty with hS0 | ⟨u, hu⟩
    · simp [hS0]
    · have h1 := hS u hu
      have h2 := condC_nonneg V u y
      push_cast at h1
      linarith
  · have hprog : ∀ u ∈ S, ∃ p : BitString, produces V p y u ∧ p.length < k := by
      intro u hu
      obtain ⟨p, hp, hlen⟩ := exists_program_of_condC V hV u y
      refine ⟨p, hp, ?_⟩
      have h1 := hS u hu
      rw [← hlen] at h1
      exact_mod_cast h1
    choose! f hf using hprog
    have hinj : Set.InjOn f S := by
      intro u hu v hv huv
      have h1 := (hf u hu).1
      have h2 := (hf v hv).1
      rw [huv] at h1
      exact Part.mem_unique h1 h2
    have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
    have hsub : S.image f ⊆ (boundedPrograms (k - 1)).toFinset := by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hp
      rw [List.mem_toFinset, mem_boundedPrograms_iff]
      have := (hf u hu).2
      omega
    have h1 := Finset.card_le_card hsub
    have h2 := List.toFinset_card_le (boundedPrograms (k - 1))
    have h3 := length_boundedPrograms_succ_eq (k - 1)
    have h4 : k - 1 + 1 = k := by omega
    rw [h4] at h3
    generalize 2 ^ k = P at h3 ⊢
    omega

/-- **Lower chain rule at bounded joint complexity** (node L02): if `C(u, v) ≤ N` then
`C(u, v) ≥ C(u) + C(v | u) - c log₂ (N + 2)`. -/
theorem pairC_ge_of_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (N : ℝ) (u v : BitString), pairC V u v ≤ N →
      plainC V u + condC V v u - c * Real.logb 2 (N + 2) ≤ pairC V u v := by
  obtain ⟨c, hc⟩ := upperComplexityChain_lower V hV
  refine ⟨c, fun N u v hN => ?_⟩
  have h := hc u v
  have hmono := logb_add_two_mono (pairC_nonneg V u v) hN
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  nlinarith

/-- **Concatenation to pair** (node L02, bridge B6): for equal halves,
`C(u, v) ≤ C(u ++ v) + c`. -/
theorem pairC_le_plainC_append (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, u.length = v.length → pairC V u v ≤ plainC V (u ++ v) + c := by
  have hhalf : Computable (fun w : BitString => w.length / 2) :=
    (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)).to_comp
  have hf : Computable (fun w : BitString =>
      pairCode (w.take (w.length / 2)) (w.drop (w.length / 2))) :=
    pairCode_computable.comp ((Primrec.list_take.to_comp.comp hhalf Computable.id).pair
      (Primrec.list_drop.to_comp.comp hhalf Computable.id))
  obtain ⟨c, hc⟩ := plainK_map_le V hV _ hf
  refine ⟨c, fun u v huv => ?_⟩
  have h := hc (u ++ v)
  have hsplit : (u ++ v).length / 2 = u.length := by
    rw [List.length_append, ← huv]
    omega
  simp only [hsplit, List.take_left, List.drop_left] at h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV (u ++ v))
  have h1 : plainK V (pairCode u v) ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have h2 : plainC V (u ++ v) = k := by rw [plainC, ← hk, ENat.toNat_natCast]
  rw [h2]
  change plainC V (pairCode u v) ≤ _
  unfold plainC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **Pair to concatenation** (node L02, bridge B6): `C(u ++ v) ≤ C(u, v) + c`. -/
theorem plainC_append_le_pairC (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, plainC V (u ++ v) ≤ pairC V u v + c := by
  obtain ⟨c, hc⟩ := plainK_map_le V hV (fun w => decodeFirst w ++ decodeSecond w)
    ((Primrec.list_append.to_comp).comp decodeFirst_computable decodeSecond_computable)
  refine ⟨c, fun u v => ?_⟩
  have h := hc (pairCode u v)
  simp only [decodeFirst_pairCode, decodeSecond_pairCode] at h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV (pairCode u v))
  have h1 : plainK V (u ++ v) ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have h2 : pairC V u v = k := by rw [pairC, plainC, ← hk, ENat.toNat_natCast]
  rw [h2]
  unfold plainC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **Node L02, `plainCodingInterface`.**  Over the exact U00 definitions (`plainC`, `condC`,
`pairC` at the same optimal plain machine `V`): finiteness and attainment of conditional
complexities, the counting bound, both chain rules with logarithmic error in the joint
complexity, and the concatenation/pair bridges. -/
theorem plainCodingInterface (V : Map) (hV : isOptimalConditional V) :
    (∀ u v : BitString, condK V u v ≠ ⊤) ∧
      (∀ u v : BitString, ∃ p : BitString, produces V p v u ∧ (p.length : ℝ) = condC V u v) ∧
      (∀ (y : BitString) (k : ℕ) (S : Finset BitString), (∀ u ∈ S, condC V u y < k) →
        S.card < 2 ^ k) ∧
      (∃ c : ℕ, ∀ (N : ℝ) (u v : BitString), pairC V u v ≤ N →
        plainC V u + condC V v u - c * Real.logb 2 (N + 2) ≤ pairC V u v) ∧
      (∃ c : ℕ, ∀ u v : BitString,
        pairC V u v ≤ plainC V u + condC V v u + c * Real.logb 2 (pairC V u v + 2)) ∧
      (∃ c : ℕ, ∀ u v : BitString, u.length = v.length → pairC V u v ≤ plainC V (u ++ v) + c) ∧
      (∃ c : ℕ, ∀ u v : BitString, plainC V (u ++ v) ≤ pairC V u v + c) :=
  ⟨condK_ne_top_of_optimal V hV, exists_program_of_condC V hV, card_lt_two_pow_of_condC_lt V hV,
    pairC_ge_of_le V hV, upperComplexityChain_upper V hV, pairC_le_plainC_append V hV,
    plainC_append_le_pairC V hV⟩

end Lower

end Kolmogorov.StrongMerging
