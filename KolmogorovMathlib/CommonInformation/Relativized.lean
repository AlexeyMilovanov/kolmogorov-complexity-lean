import KolmogorovMathlib.CommonInformation.IncidenceWitnessSelector
import KolmogorovMathlib.CommonInformation.WorstCase
import KolmogorovMathlib.Prefix.TwoStage

/-!
# Exercise 313: relativized (conditional-`u`) non-extractability

SUV Exercise 313 asks for the analogue of the oracle remark on p. 361 with an
additional *condition string* `u` (of unlimited complexity) in place of the
oracle: for every `u` there is a pair `x, y` of **unconditional** complexity
`2n` and **unconditional** mutual information `n` such that no `z` extracts the
common information *relative to `u`* — i.e. there is no `z` with `C(z | u)`,
`C(x | z, u)`, `C(y | z, u)` all below `1.1 n`.

The relativized complexity `C(· | u)` is modelled by

```
relativizedMap V u (p, y) := V (p, pairCode y u)
```

so that `condK (relativizedMap V u) x y = condK V x (pairCode y u)`, i.e. the
condition of every query carries `u` alongside its ordinary context.  The
`relativizedMap V u` is a genuine optimal decompressor
(`isOptimalConditional_relativizedMap`), so its region is a genuine relativized
common-information region.

The mathematical content is the union bound of the source:
*even a very powerful condition still defines only combinatorial rectangles that
cover a negligible fraction of the incidence edges, and it remains to select an
uncovered (and unconditionally non-simple) edge.*  This is
`exists_incidentEdge_highComplexity_and_uncovered`: among the
`concretePrime n ^ 3 > 2 ^ {3n}` incident edges, at most `2 ^ {3n-1}` are
`u`-covered (the no-4-cycle density bound, valid for **any** map) and at most
`2 ^ {3n-1}` are unconditionally compressible, so some edge is simultaneously
unconditionally high-complexity and `u`-uncovered.  Gluing with the
unconditional Exercise 309 profile and the region → covered-pair bridge yields
Exercise 313.
-/

namespace Kolmogorov

-- `incidentCommonWitnessPairsLe (relativizedMap V u) …` is a `noncomputable`
-- `Finset` whose unfolding reaches `progToOut (relativizedMap V u)`; letting
-- `isDefEq` unfold it while `relativizedMap` is a concrete lambda causes runaway
-- `whnf`.  Making it locally irreducible forces congruence-based unification
-- (which only ever assigns the map/threshold arguments), so the region and
-- covered-pair `Finset`s compare in constant time in this module.
attribute [local irreducible] incidentCommonWitnessPairsLe

/-- The `u`-relativized decompressor: every query carries the condition `u`
alongside its ordinary context. -/
noncomputable def relativizedMap (V : Map) (u : BitString) : Map :=
  fun ⟨p, y⟩ => V (p, pairCode y u)

/-- The candidate program sets coincide, so `condK` of the relativized map is
`condK` of `V` with `u` appended to the condition. -/
theorem condK_relativizedMap (V : Map) (u x y : BitString) :
    condK (relativizedMap V u) x y = condK V x (pairCode y u) := rfl

/-- Applying the relativized map is running `V` on a `u`-extended context. -/
theorem relativizedMap_apply (V : Map) (u p y : BitString) :
    relativizedMap V u (p, y) = V (p, pairCode y u) := rfl

/-- The relativized map is a decompressor whenever `V` is. -/
theorem isDecompressor_relativizedMap (V : Map) (hV : isDecompressor V) (u : BitString) :
    isDecompressor (relativizedMap V u) := by
  -- No type annotations: matching the `.comp` result against an annotated
  -- `Computable (fun py => pairCode py.2 u)` forces `whnf` to unfold `pairCode`.
  have hcomp := Computable.pair (Computable.fst (α := BitString) (β := BitString))
    (pairCode_computable.comp (Computable.snd.pair (Computable.const u)))
  have hpr := Partrec.comp hV hcomp
  exact hpr.of_eq (fun py => by rcases py with ⟨p, y⟩; rfl)

/-- **Faithfulness certificate.** `relativizedMap V u` is itself an optimal
conditional decompressor, so `condK (relativizedMap V u)` is a genuine
relativized complexity (well-defined up to an additive constant).  Optimality is
uniform: the strip decompressor `(p, w) ↦ V (p, decodeFirst w)` discards the
`u`-part of any context, so adding `u` to a condition cannot increase complexity
by more than a constant. -/
theorem condK_extend_condition_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y u : BitString,
      condK V x (pairCode y u) ≤ condK V x y + (c : ENat) := by
  have hStripComp := Computable.pair (Computable.fst (α := BitString) (β := BitString))
    (decodeFirst_computable.comp Computable.snd)
  have hStrip : isDecompressor (fun pw : BitString × BitString => V (pw.1, decodeFirst pw.2)) :=
    Partrec.comp hV.1 hStripComp
  obtain ⟨c1, hc1⟩ := hV.2 _ hStrip
  refine ⟨c1, fun x y u => ?_⟩
  have hStripEq :
      condK (fun pw : BitString × BitString => V (pw.1, decodeFirst pw.2)) x (pairCode y u)
        = condK V x y := by
    have hset :
        candidateLengths (fun pw : BitString × BitString => V (pw.1, decodeFirst pw.2))
            x (pairCode y u) = candidateLengths V x y := by
      unfold candidateLengths produces
      ext m
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, by simpa only [decodeFirst_pairCode] using hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, by simpa only [decodeFirst_pairCode] using hp, rfl⟩
    unfold condK
    rw [hset]
  calc
    condK V x (pairCode y u)
        ≤ condK (fun pw : BitString × BitString => V (pw.1, decodeFirst pw.2))
            x (pairCode y u) + (c1 : ENat) := hc1 x (pairCode y u)
    _ = condK V x y + (c1 : ENat) := by rw [hStripEq]

theorem condK_extend_condition_values (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y u kxy kxyu, HasPlainConditionalComplexityValue V x y kxy →
      HasPlainConditionalComplexityValue V x (pairCode y u) kxyu → kxyu ≤ kxy + c := by
  obtain ⟨c, hc⟩ := condK_extend_condition_le V hV
  refine ⟨c, fun x y u kxy kxyu hxy hxyu => ?_⟩
  have h := hc x y u
  rw [hxy, hxyu] at h
  exact_mod_cast h

theorem isOptimalConditional_relativizedMap
    (V : Map) (hV : isOptimalConditional V) (u : BitString) :
    isOptimalConditional (relativizedMap V u) := by
  refine ⟨isDecompressor_relativizedMap V hV.1 u, fun D hD => ?_⟩
  obtain ⟨c1, hc1⟩ := condK_extend_condition_le V hV
  obtain ⟨c2, hc2⟩ := hV.2 D hD
  refine ⟨c1 + c2, fun x y => ?_⟩
  rw [condK_relativizedMap]
  calc
    condK V x (pairCode y u)
        ≤ condK V x y + (c1 : ENat) := hc1 x y u
    _ ≤ (condK D x y + (c2 : ENat)) + (c1 : ENat) := by gcongr; exact hc2 x y
    _ = condK D x y + ((c1 + c2 : ℕ) : ENat) := by push_cast; ring

/-- **Generic counting core** (with the covered set `covered` kept *abstract*):
among the `concretePrime n ^ 3 > 2 ^ {3n}` incident edges, if `covered` has fewer
than `2 ^ {3n-1}` elements, then some incident edge is both unconditionally
high-complexity and avoids `covered`.  Keeping `covered` opaque is essential:
otherwise the `Finset` comparisons below make `isDefEq` unfold
`incidentCommonWitnessPairsLe (relativizedMap V u)` down to the noncomputable
`progToOut`, which times out. -/
theorem exists_incident_uncompressible_uncovered {n : Nat} (hn : 64 ≤ n)
    (V : Map) (hV : isOptimalConditional V)
    (covered : Finset (BitString × BitString))
    (hcov : covered.card < 2 ^ (3 * n - 1)) :
    ∃ (e : ConcreteIncidentEdge n) (kxy : Nat),
      HasPlainComplexityValue V
        (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2)) kxy ∧
      3 * n ≤ kxy + 1 ∧
      (concretePointCode n e.1.1, concreteLineCode n e.1.2) ∉ covered := by
  classical
  set comp := compressibleWords V [] (3 * n - 2) with hcomp
  set badCovered := covered.image (fun p => pairCode p.1 p.2) with hbc
  set L := (concreteIncidentPairCodes n).toFinset with hLdef
  have hLcard : L.card = concretePrime n ^ 3 := by
    rw [hLdef, List.toFinset_card_of_nodup (concreteIncidentPairCodes_nodup n),
      concreteIncidentPairCodes_length]
  have hcompCard : comp.card < 2 ^ (3 * n - 1) := by
    rw [hcomp]
    have h := cardCompressibleWordsLt V [] (3 * n - 2)
    rwa [show 3 * n - 2 + 1 = 3 * n - 1 by omega] at h
  have hcovCard : badCovered.card < 2 ^ (3 * n - 1) :=
    lt_of_le_of_lt Finset.card_image_le hcov
  have hprime : 2 ^ (3 * n) < concretePrime n ^ 3 := by
    rw [show 2 ^ (3 * n) = (2 ^ n) ^ 3 by rw [← pow_mul]; congr 1; omega]
    exact Nat.pow_lt_pow_left (concretePrime_lower n) (by omega)
  have hdouble : 2 ^ (3 * n - 1) + 2 ^ (3 * n - 1) = 2 ^ (3 * n) := by
    have hval : 2 ^ (3 * n) = 2 ^ (3 * n - 1) * 2 := by
      conv_lhs => rw [show 3 * n = (3 * n - 1) + 1 by omega]
      rw [pow_succ]
    omega
  have hbadCard : (comp ∪ badCovered).card < L.card := by
    calc (comp ∪ badCovered).card
        ≤ comp.card + badCovered.card := Finset.card_union_le _ _
      _ < 2 ^ (3 * n - 1) + 2 ^ (3 * n - 1) := by omega
      _ = 2 ^ (3 * n) := hdouble
      _ < concretePrime n ^ 3 := hprime
      _ = L.card := hLcard.symm
  have hnsub : ¬ L ⊆ comp ∪ badCovered := fun hs =>
    absurd (Finset.card_le_card hs) (not_le.mpr hbadCard)
  obtain ⟨w, hwL, hwBad⟩ := Finset.not_subset.mp hnsub
  rw [Finset.mem_union, not_or, hcomp, hbc] at hwBad
  rw [hLdef, List.mem_toFinset] at hwL
  obtain ⟨e, rfl⟩ := (concreteIncidentPairCodes_mem_iff n w).mp hwL
  obtain ⟨kxy, hkxy⟩ := exists_plainComplexityValue V hV
    (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2))
  refine ⟨e, kxy, hkxy, ?_, ?_⟩
  · -- High complexity: not compressible at level `3n - 2`, so `kxy ≥ 3n - 1`.
    by_contra hlt
    push_neg at hlt
    apply hwBad.1
    rw [mem_compressibleWords_iff]
    change plainK V (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2))
      ≤ ((3 * n - 2 : Nat) : ENat)
    rw [hkxy]
    exact_mod_cast (show kxy ≤ 3 * n - 2 by omega)
  · -- Uncovered: the pair's code is not among the (abstract) covered codes.
    intro hmem
    apply hwBad.2
    rw [Finset.mem_image]
    exact ⟨(concretePointCode n e.1.1, concreteLineCode n e.1.2), hmem, rfl⟩

theorem exists_incidentEdge_highComplexity_and_uncovered
    (V : Map) (hV : isOptimalConditional V) :
    ∃ N, ∀ n, N ≤ n → ∀ u,
      ∃ (e : ConcreteIncidentEdge n) (kxy : Nat),
        HasPlainComplexityValue V
          (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2)) kxy ∧
        3 * n ≤ kxy + 1 ∧
        (concretePointCode n e.1.1, concreteLineCode n e.1.2) ∉
          incidentCommonWitnessPairsLe (relativizedMap V u) n
            (muchnikThreshold n - 1) (muchnikThreshold n - 1) (muchnikThreshold n - 1) := by
  refine ⟨64, fun n hn u => ?_⟩
  have hcov : (incidentCommonWitnessPairsLe (relativizedMap V u) n
      (muchnikThreshold n - 1) (muchnikThreshold n - 1) (muchnikThreshold n - 1)).card
        < 2 ^ (3 * n - 1) :=
    lt_of_lt_of_le (muchnikThreshold_incidentCommonWitness_card_lt_gap hn)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact exists_incident_uncompressible_uncovered hn V hV _ hcov

/-- Generic region → uncovered bridge, stated with **opaque** `V, x, y` so that
its (single) application never forces the elaborator to reduce the concrete
field codes or the `relativizedMap` lambda: if the symmetric `1.1 n` threshold
were in the region of `(x, y)`, then `(x, y)` would be a covered incident pair. -/
theorem region_excluded_of_uncovered {V : Map} {n : Nat} {x y : BitString}
    (hn : 0 < muchnikThreshold n) (hinc : concreteIncidentCodeRel n x y)
    (huncov : (x, y) ∉ incidentCommonWitnessPairsLe V n
      (muchnikThreshold n - 1) (muchnikThreshold n - 1) (muchnikThreshold n - 1)) :
    (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
      CommonInformationRegion V x y := fun hregion =>
  huncov (mem_incidentCommonWitnessPairsLe_of_mem_region hn hn hn hinc hregion)

/-- **Exercise 313.**  The relativized (condition-`u`) analogue of Theorem 223 /
`exists_incidence_muchnik_counterexample`: for every condition string `u` there
is an incident edge `(x, y)` of **unconditional** complexity `2n`, pair
complexity `3n`, and mutual information `n`, such that the relativized region of
`(x, y)` excludes the symmetric `1.1 n` threshold — no `z` is simultaneously
simple given `u`, and simple for `x` and for `y` given `u`.

The unconditional profile is `exercise_309_incident_edge_profile`; the region
exclusion comes from the union bound
`exists_incidentEdge_highComplexity_and_uncovered` and the region → covered-pair
bridge `mem_incidentCommonWitnessPairsLe_of_mem_region` applied to
`relativizedMap V u`. -/
theorem exercise_313_relativized_obstruction
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C N, ∀ n, N ≤ n → ∀ u,
      ∃ (e : ConcreteIncidentEdge n) (kx ky kxy : Nat),
        let x := concretePointCode n e.1.1
        let y := concreteLineCode n e.1.2
        x.length = 2 * (n + 1) ∧
        y.length = 2 * (n + 1) ∧
        HasPlainComplexityValue V (pairCode x y) kxy ∧
        HasPlainComplexityValue V x kx ∧
        HasPlainComplexityValue V y ky ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        MutualInformationWithin V x y n (logSlack C n) ∧
        (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
          CommonInformationRegion (relativizedMap V u) x y := by
  obtain ⟨Cprofile, hprofile⟩ := exercise_309_incident_edge_profile V hV 1
  obtain ⟨Nunc, hunc⟩ := exists_incidentEdge_highComplexity_and_uncovered V hV
  refine ⟨Cprofile, max Nunc 1, ?_⟩
  intro n hn u
  have hNunc : Nunc ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨e, kxy, hkxy, hHigh, hUncov⟩ := hunc n hNunc u
  have hHigh' : 3 * n ≤ kxy + logSlack 1 n := by
    have hpos : 1 ≤ logSlack 1 n := by unfold logSlack; omega
    omega
  obtain ⟨kx, ky, hkx, hky, hkxClose, hkyClose, hkxyClose, hmi⟩ :=
    hprofile n e kxy hkxy hHigh'
  -- Region exclusion via the region → covered-pair bridge, contradicting uncovered.
  -- Proved with fully explicit codes so no `let`-vs-explicit `whnf` on concrete field terms.
  have htPos : 0 < muchnikThreshold n := (muchnik_lt_threshold_iff 0 n).mpr (by omega)
  have hinc : concreteIncidentCodeRel n
      (concretePointCode n e.1.1) (concreteLineCode n e.1.2) :=
    concreteIncidentCodeRel_iff_exists_edge.mpr ⟨e, rfl, rfl⟩
  have hexcl : (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
      CommonInformationRegion (relativizedMap V u)
        (concretePointCode n e.1.1) (concreteLineCode n e.1.2) :=
    region_excluded_of_uncovered htPos hinc hUncov
  refine ⟨e, kx, ky, kxy, concretePointCode_length n e.1.1,
    concreteLineCode_length n e.1.2, hkxy, hkx, hky,
    hkxyClose, hkxClose, hkyClose, hmi, hexcl⟩

end Kolmogorov
