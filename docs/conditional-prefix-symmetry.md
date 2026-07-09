# Conditional Prefix Symmetry of Information

This development note records an important general theorem that is not yet
formalized in the project.  The current prefix-complexity infrastructure proves the unconditional
staged symmetry of information for pairs:

```text
K(x,z) = K(z) + K(x | z, K(z)) + O(1)
```

in Lean as the two-sided theorem `KPPair_symmetryOfInformation_staged`, using
`KPPair`, `KPPlain`, `HasPrefixComplexityValue`, and
`prefixComplexityContext`.

The next general theorem should be the corresponding conditional version, with
an external condition `y`:

```text
K(x,z | y) = K(z | y) + K(x | z, K(z | y), y) + O(1).
```

A faithful Lean shape should use a natural witness `kzy` for the finite value
of `KP U z y`, just as the unconditional theorem uses a witness for `KPPlain U
z`.  Schematically:

```lean
def conditionalPrefixComplexityContext
    (z : BitString) (kzy : Nat) (y : BitString) : BitString :=
  -- code the triple (z, kzy, y), for example by nested pairCode/natCode
  pairCode z (pairCode (natCode kzy) y)

def HasConditionalPrefixComplexityValue
    (U : Map) (z y : BitString) (kzy : Nat) : Prop :=
  (kzy : ENat) = KP U z y

theorem KP_pair_cond_symmetryOfInformation_staged
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    Exists fun cUpper : Nat => Exists fun cLower : Nat =>
      forall x z y : BitString, forall kzy : Nat,
        HasConditionalPrefixComplexityValue U z y kzy ->
          KP U (pairCode x z) y
            <= KP U z y
               + KP U x (conditionalPrefixComplexityContext z kzy y)
               + (cUpper : ENat) /\
          KP U z y
               + KP U x (conditionalPrefixComplexityContext z kzy y)
            <= KP U (pairCode x z) y + (cLower : ENat)
```

The exact order of the pair `(x,z)` and the context `(z,kzy,y)` can be adjusted
to match downstream use, but the theorem should retain the external condition
`y` and the witness for `K(z | y)`.  A version with `K(z)` instead of `K(z|y)`
is strictly weaker and is not the desired statement.

## Expected proof route

1. Generalize the existing two-stage pair builder so that the first-stage
   program is run under an external condition `y` rather than under `[]`.
2. Prove the conditional upper direction by composing:
   a program for `z` from `y`, and then a program for `x` from the encoded
   context `(z, K(z|y), y)`.
3. Generalize the lower direction `KPPair_chain_lower_of_conditional_coding` to
   sections of the conditional a priori semimeasure at fixed external condition
   `y`.
4. Package the two inequalities as a staged theorem, following the structure of
   `KPPair_symmetryOfInformation_staged`.

## Why this matters

This conditional symmetry theorem should become a central reusable ingredient
for algorithmic statistics. Several current ad hoc chain-rule and gap-counting
arguments should become direct corollaries, or at least substantially shorter,
once this theorem is available.
