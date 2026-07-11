# Conditional Prefix Symmetry of Information — DONE

**Status: formalized.** This file used to be the TODO for the conditional
staged symmetry of information. The theorem is now fully proved in
`KolmogorovMathlib/Prefix/ConditionalSymmetry.lean`:

```lean
theorem KPCondPair_symmetryOfInformation_staged (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ cUpper : Nat, ∃ cLower : Nat,
      ∀ x y z : BitString, ∀ kx : Nat,
        HasCondPrefixComplexityValue U x z kx →
          KPCondPair U x y z
              ≤ KP U x z + KP U y (prefixCondComplexityContext z x kx) + (cUpper : ENat) ∧
          KP U x z + KP U y (prefixCondComplexityContext z x kx)
              ≤ KPCondPair U x y z + (cLower : ENat)
```

i.e. `K(x,y | z) = K(x | z) + K(y | z, x, K(x|z)) + O(1)`, with the external
condition `z` and a natural witness `kx` for `K(x|z)` — exactly the statement
this document originally requested (up to renaming of the letters).

Supporting pieces, all in the same file / `Prefix/CondTwoStage.lean`:

- upper direction: relativized two-stage builder
  (`KPCondPair_chain_upper_of_prefix_decompressor`, `KPCondPair_chain_upper`);
- lower direction: sections of the conditional a priori semimeasure
  (`section_coding_bound` → `KPCondPair_chain_lower`);
- the unconditional staged SOI is recovered at the empty condition
  (`KPPair_chain_lower`, `KPPair_symmetryOfInformation_staged`);
- `KP_cond_remove_short_info` (remove a short known string from the
  condition), already consumed by `TwoPart/PaperTheorems.lean`.

## Follow-up refactor: done

`KP_le_prefixComplexityContext_add_logSlack` in
`AlgorithmicStatistics/TwoPart/GapCounting.lean` (the index-drop chain rule)
is now proved as a direct corollary of `KP_cond_remove_short_info` at
`z := natCode i`; its two former ad hoc helper lemmas were removed. The other
chain-shaped proofs in `GapCounting.lean`/`DescriptionShift.lean`
(`descriptionShift_complexity`, the reconstruction bounds) already compose the
pair/SOI primitives directly and need no changes.
