# Formalization of Algorithmic Information Theory in Lean 4

## Overview
This project provides a machine-checked formalization of the foundations of Algorithmic Information Theory (AIT), centered around Kolmogorov Complexity, using the Lean 4 theorem prover. 

In standard literature, proofs in AIT often rely on informal appeals to the Church-Turing thesis and asymptotic bounds (big-O notation). This repository bridges the gap between abstract computability theory and information theory by explicitly constructing universal decompressors, tracking additive constants, and rigorously proving the uncomputability of information content.

Built on top of Mathlib's computability theory (`Mathlib.Computability.Partrec`), this project formalizes the definitions of both **plain** ($K(x)$) and **conditional** ($K(x|y)$) Kolmogorov complexity, treating abstract maps and computable decompressors as partial recursive functions.

## Key Formalizations
The project formalizes the following core components of Algorithmic Information Theory:

1. **The Universal Decompressor and The Invariance Theorem (Kolmogorov-Solomonoff-Chaitin):**
   
   Construction of a Conditional Universal Decompressor using a unary prefix-coding scheme. The project includes a formal proof of its optimality: the capability to simulate any other computable decompressor with a strictly bounded additive penalty to the program length. This establishes the invariance of Kolmogorov complexity up to an additive constant.

2. **Fundamental Information Inequalities:**
   Proofs of the basic bounds of information theory, including:
   * $K(x) \le |x| + c$ (A string's complexity is bounded by its literal length).
   * $K(x|x) \le c$ (Conditioning on the string itself reduces complexity to a constant).
   * $K(f(x)) \le K(x) + c_f$ (Applying a computable function cannot increase complexity).

3. **Incompressibility and The Pigeonhole Principle:**
   
   Formalization of the combinatorics of bit strings. By proving that there are exactly $2^n$ strings of length $n$, but only $2^n - 1$ programs shorter than $n$, the project demonstrates that for any length $n$, there exists at least one algorithmically incompressible string.

4. **The Uncomputability Theorem (Berry's Paradox):**
   The primary result of the project. A formal proof that the plain Kolmogorov complexity function is uncomputable. The proof models Berry's Paradox by creating a computable search algorithm that looks for complex strings, deriving a mathematical contradiction between the logarithmic length of the search parameter and the exponential complexity of the generated string.

## Architectural Choices
* **Extended Naturals (`ENat`):** Complexity is defined as the infimum (`sInf`) of the set of valid program lengths. By operating in `ENat` (Naturals with a $\top$ element), the theory handles non-terminating programs and empty sets natively.
* **Bijective Base-2 Numeration (Dyadic Encoding):** To translate complexity between binary strings and natural numbers without the "leading zeros" problem, the project implements a computable bijection (`ℕ ≃ List Bool`) using dyadic numeration.
* **Monadic Computability (`Part`):** Maps (and computable decompressors) are modeled using Lean's `Part` monad (partial functions), allowing for standard handling of halting/non-halting computations and integration with Mathlib's `Partrec` API.

---

## Project Structure

The repository is organized into three main directories, reflecting a bottom-up approach to formalizing the theory:

```text
KolmogorovMathlib/
├── Foundation/
│   ├── ListPrimrec.lean
│   ├── UnboundedSearch.lean
│   └── DyadicEquiv.lean
├── Core/
│   ├── Basic.lean
│   ├── UniversalDecompressor.lean
│   └── Invariance.lean
└── Complexity/
    ├── Properties.lean
    ├── Incompressibility.lean
    ├── NatComplexity.lean
    └── Uncomputability.lean
```

## File-by-File Documentation: Foundation

The `Foundation/` directory contains the mathematical and algorithmic prerequisites needed to build the core theory. These files extend Lean 4's Mathlib with custom computability proofs, search operators, and string encodings.

### 1. `Foundation/ListPrimrec.lean`
**Purpose:** Bootstrapping low-level primitive recursive operations for boolean lists.

To construct a Universal Decompressor, we need to manipulate the input tape (represented as a `List Bool`). While Mathlib provides standard list operations, their underlying definitions are sometimes not structurally optimized for computability proofs. This file introduces custom, strict-recursive list operations that interface seamlessly with Mathlib's `Primrec` combinators.

**Key Components:**
* `prefixLen`: Computes the number of consecutive `true`s at the start of a boolean list. This is the core parser for our unary prefix coding. It is defined using strict `List.recOn` to perfectly match the `Primrec.list_rec` combinator.
* `listDrop`: Drops the first $n$ elements from a list. It is defined using strict `Nat.rec` to smoothly align with the `Primrec₂` class (functions of two variables).
* **Computability Proofs:** The file provides exact, combinator-based proofs (`Primrec.prefixLen`, `Primrec₂.listDrop`) ensuring these functions can be executed by our theoretical decompressors.

---

### 2. `Foundation/UnboundedSearch.lean`
**Purpose:** Formalizing the $\mu$-operator (Unbounded Search) and the "Computability Bridge".

A recurring challenge in formalizing computability is bridging the gap between a logical proof of existence (`∃ n, P n`) and the algorithmic process of finding that `n`. This file mathematically proves that if a property is computable and guaranteed to exist, the linear search for its first occurrence is a valid, computable partial recursive function.

**Key Components:**
* `Computable.unboundedSearch`: The master lemma of the file. It takes a decidable, computable predicate $P(k, n)$ and a proof that $\forall k, \exists n, P(k, n)$, and proves that the mapping $k \mapsto \min \{n \mid P(k, n)\}$ (implemented via `Nat.find`) is `Computable`. It uses `Partrec.rfind` to construct the actual search.
* `Computable.inverse`: A corollary proving that if a computable function $f$ is surjective, its exact inverse is also computable.
* `Computable.searchCore`: Extends the search to inequalities, proving that finding the first $n$ where $f(n) > g(k)$ is computable. This is the exact lemma required later to formalize Berry's Paradox algorithm.
* `Computable.listInverse`: Proves that the inverse of a computable bijection between `List Bool` and `ℕ` is also computable.

---

### 3. `Foundation/DyadicEquiv.lean`
**Purpose:** Establishing a bijective mapping between natural numbers and binary strings.


Standard binary representation is not a true bijection because of the "leading zeros" problem (e.g., the strings `[true]`, `[false, true]`, and `[false, false, true]` all map to the number $1$). To rigorously define the Kolmogorov complexity of a natural number, we need a 1-to-1 mapping. This file implements **Dyadic Numeration** (bijective base-2).

**Key Components:**
* `bitsToNat` & `natToBits`: The decoding and encoding functions. `bitsToNat` parses `[] ↦ 0`, `[false] ↦ 1`, `[true] ↦ 2`, etc.
* `dyadicEquiv`: The formal equivalence `ℕ ≃ List Bool`, supported by the `@[simp]` lemmas `bitsToNat_natToBits` and `natToBits_bitsToNat` which prove mutual inversion.
* `bounds_bitsToNat` & `length_natToBits_le`: Establishes the fundamental exponential bounds of the encoding: $2^{|s|} \le \text{val}(s) + 1 < 2^{|s|+1}$. This proves that the length of the string representation grows strictly logarithmically relative to the number, a fact heavily utilized in the final uncomputability proof.
* **Computability:** Using the theorems from `UnboundedSearch.lean`, the file rigorously proves that both `bitsToNat` and `natToBits` are `Computable`.

## File-by-File Documentation: Core

The `Core/` directory represents the semantic heart of the project. It defines the central concepts of Algorithmic Information Theory (AIT), constructs the Universal Decompressor, and culminates in the formal proof of the Invariance Theorem.

### 4. `Core/Basic.lean`
**Purpose:** Establishing the foundational ontology for Kolmogorov complexity.

This file translates the abstract mathematical concepts of AIT into rigorous Lean 4 types. By defining abstract maps and computable decompressors as partial recursive functions and utilizing the Extended Naturals (`ENat`), it creates a framework where non-terminating programs and uncomputable values are handled elegantly without logical paradoxes.

**Key Components:**
* `Map`: Defined as `BitString × BitString →. BitString`. The use of the `Part` monad (`→.`) perfectly encapsulates the fact that abstract execution might not halt.
* `produces`: Formalizes the relationship "map $D$ outputs $x$ given program $p$ and context $y$" using the monadic membership operator (`x ∈ D (p, y)`).
* `condK` & `plainK`: Defines conditional and plain Kolmogorov complexity as the infimum (`sInf`) of the set of valid program lengths. If the set is empty (no program produces the string), the complexity naturally evaluates to $\top$ (infinity) in `ENat`.
* `isOptimalConditional`: Defines the concept of universality. A map is optimal if it is computable (`isDecompressor`) and can simulate any other computable decompressor with at most a constant additive overhead to the program length.

---

### 5. `Core/UniversalDecompressor.lean`
**Purpose:** Constructing the Conditional Universal Decompressor.

To prove that an optimal decompressor exists, one must be explicitly constructed. This file builds a Universal Decompressor $U$ that multiplexes an infinite number of computable algorithms onto a single tape using a prefix-free encoding. It bridges the gap between a human-readable definition and a strict mathematical combinator required for computability proofs.

**Key Components:**
* `unaryPrefix`: Implements unary prefix coding ($n$ is encoded as $n$ `true`s followed by a `false`). This allows the universal decompressor to read the index of the target decompressor, know exactly where the index ends, and treat the rest of the tape as the program.
* `universalDecompressor` & `universalDecompressorCombinator`: Defines the map in two ways. The first is readable and utilizes `match` statements; the second uses strict monadic binds (`Part.bind`). The `universalDecompressor_eq_combinator` lemma proves they are identical.
* `isDecompressor_universalDecompressor`: The heavy-lifting proof of the file. By meticulously composing `Partrec` (partial recursive) combinators, it proves that the Universal Decompressor is itself fully computable.

---

### 6. `Core/Invariance.lean`
**Purpose:** Formalizing the Kolmogorov-Solomonoff-Chaitin Invariance Theorem.

This is the foundational theorem of Algorithmic Information Theory. It proves that the choice of programming language or decompressor does not matter up to an additive constant. Because we have an optimal universal decompressor, complexity is an objective mathematical property of the string itself.

**Key Components:**
* `exists_code_of_isDecompressor`: Connects our abstract definition of computable maps with Mathlib's Gödel numbering (`Nat.Partrec.Code`). It proves that every computable decompressor has a numerical code whose evaluation perfectly mirrors the decompressor's behavior.
* `sInf_le_sInf_add`: A critical lattice-theoretic lemma proving that if every element in set $A$ has a counterpart in set $B$ that is at most $c$ larger, then $\inf(A) \le \inf(B) + c$.
* `exists_isOptimalConditional`: The main theorem. It proves that the `universalDecompressor` satisfies the `isOptimalConditional` predicate. It explicitly constructs the proof by showing that to simulate any decompressor $D$, $U$ simply prepends the unary prefix of $D$'s Gödel number to the program. The length overhead $c$ is exactly the length of this prefix, which is a constant independent of the string being compressed.

## File-by-File Documentation: Complexity

The `Complexity/` directory contains the high-level theorems and applications of Algorithmic Information Theory. Having established the foundational ontology and the optimal Universal Decompressor in `Core/`, these files formalize the mathematical behavior of information, culminating in the proof of uncomputability.

### 7. `Complexity/Properties.lean`
**Purpose:** Establishing the fundamental information inequalities.

This file proves the basic laws of algorithmic information processing. It shows how complexity behaves under composition, self-reference, and the application of computable functions. By relying on the optimality of the Universal Decompressor $U$, the proofs abstract away the underlying decompressor mechanics into clean, algebraic bounds.

**Key Components:**
* `condK_eq_top_iff`: A boundary API lemma proving that $K(x|y) = \top$ (infinity) if and only if no program can compute $x$ from $y$.
* `plainK_le_length`: Proves that $K(x) \le |x| + c$. A string can always be "compressed" by simply writing it out literally; the constant $c$ accounts for the length of the "print" program.
* `condK_self` & `condK_le_plainK`: Proves that knowing the answer reduces complexity to a constant ($K(x|x) \le c$), and that additional context can never increase complexity ($K(x|y) \le K(x) + c$).
* `plainK_map_le`: The Information Processing Inequality. Proves that for any computable function $f$, $K(f(x)) \le K(x) + c_f$. Computable deterministic processes cannot generate new algorithmic information.

---

### 8. `Complexity/Incompressibility.lean`
**Purpose:** Formalizing the combinatorics of binary strings and the Pigeonhole Principle.

This file bridges combinatorics and computability. It formally counts the number of available programs and the number of distinct bit strings to prove that data compression has strict mathematical limits. This is the mechanism that powers Chaitin's Incompleteness Theorem.

**Key Components:**
* `programsLe` & `length_programsLe_add_one`: Generates the binary tree of all programs up to length $k$ and proves there are exactly $2^{k+1} - 1$ such programs.
* `compressibleWords` & `card_compressibleWords_lt`: Proves that a map can generate strictly fewer than $2^{k+1}$ strings of complexity $\le k$.
* `stringsOfLength`: Formally constructs the set of all bit strings of length $n$ and proves its cardinality is exactly $2^n$ (`card_stringsOfLength`).
* `exists_incompressible_string`: The central theorem. By applying the Pigeonhole Principle (comparing the cardinalities of `stringsOfLength` and `compressibleWords`), it proves by contradiction that for any length $n$, there exists at least one string whose Kolmogorov complexity is strictly greater than or equal to $n$.

---

### 9. `Complexity/NatComplexity.lean`
**Purpose:** Lifting Kolmogorov complexity from binary strings to Natural Numbers.

While decompressors natively operate on bit strings, mathematical paradoxes (like Berry's Paradox) are traditionally formulated using Natural Numbers. This file seamlessly lifts the theory to $\mathbb{N}$ using the dyadic bijection formalized in the `Foundation/` directory.

**Key Components:**
* `plainKNat` & `condKNat`: Defines the complexity of a natural number $n$ as the complexity of its dyadic string encoding `natToBits(n)`.
* `exists_plainKNat_gt`: A direct corollary of string incompressibility, proving that there exist natural numbers of arbitrarily high complexity.
* `plainKNat_le_length`: Establishes the logarithmic upper bound for numbers: $K(n) \le |n| + c \approx \log_2(n) + c$. This bound is the specific inequality needed to trigger Berry's Paradox.
* `plainKNat_invariance`: A Universality theorem proving that if we were to use any other computable encoding for natural numbers, the complexity would change by at most an additive constant.

---

### 10. `Complexity/Uncomputability.lean`
**Purpose:** The formal proof of the uncomputability of Kolmogorov Complexity (Berry's Paradox).


This is the culminating file of the project. It formally proves that no algorithm (or computable map) can compute the plain Kolmogorov complexity function. The proof rigorously models a computational version of Berry's Paradox: *"Find the smallest number whose complexity is greater than $2^k$"*. 

**Key Components:**
* `growth_lemma`: A purely arithmetic lemma proving that for any constant $c$, the exponential function $2^k$ will eventually strictly dominate the logarithmic length of $k$ plus the constant ($|k| + c < 2^k$).
* `Computable.find_complex`: The implementation of Berry's algorithm. It proves that **if** the complexity function were computable, the unbounded search for a complex string using the $\mu$-operator (`Nat.find`) would also be strictly computable.
* `plainKNat_find_complex_le`: Because Berry's algorithm would be computable, the complexity of the number it outputs is strictly bounded by the length of its input $k$ plus a constant overhead $c$.
* `not_computable_plainKNat`: The final contradiction. The output of Berry's algorithm is defined to have complexity $> 2^k$. However, its computability guarantees its complexity is $\le |k| + c$. Because $|k| + c < 2^k$, we derive $2^k < 2^k$. This contradiction formally destroys the assumption that Kolmogorov complexity is computable.