# Formalization of Algorithmic Information Theory in Lean 4

## Overview
This project provides a machine-checked formalization of the foundations of Algorithmic Information Theory (AIT), centered around Kolmogorov Complexity, using the Lean 4 theorem prover.

In standard literature, proofs in AIT often rely on informal appeals to the Church-Turing thesis and asymptotic bounds (big-O notation). This repository bridges the gap between abstract computability theory and information theory by explicitly constructing universal decompressors, tracking additive constants, and rigorously proving the uncomputability of information content and Chaitin's Incompleteness Theorem.

Built on top of Mathlib's computability theory (`Mathlib.Computability.Partrec`), this project formalizes the definitions of both plain ($K(x)$) and conditional ($K(x|y)$) Kolmogorov complexity, treating abstract maps and computable decompressors as partial recursive functions.

## Key Formalizations
The project formalizes the following core components of Algorithmic Information Theory:

### The Universal Decompressor and The Invariance Theorem (Kolmogorov-Solomonoff-Chaitin):
Construction of a Conditional Universal Decompressor using a unary prefix-coding scheme. The project includes a formal proof of its optimality: the capability to simulate any other computable decompressor with a strictly bounded additive penalty to the program length. This establishes the invariance of Kolmogorov complexity up to an additive constant.

### Fundamental Information Inequalities:
Proofs of the basic bounds of information theory, including:
* $K(x) \le |x| + c$ (A string's complexity is bounded by its literal length).
* $K(x|x) \le c$ (Conditioning on the string itself reduces complexity to a constant).
* $K(f(x)) \le K(x) + c_f$ (Applying a computable function cannot increase complexity).

### Incompressibility and The Pigeonhole Principle:
Formalization of the combinatorics of bit strings. By proving that there are exactly $2^n$ strings of length $n$, but only $2^n - 1$ programs shorter than $n$, the project demonstrates that for any length $n$, there exists at least one algorithmically incompressible string.

### The Uncomputability Theorem (Berry's Paradox):
A formal proof that the plain Kolmogorov complexity function is uncomputable. The proof models Berry's Paradox by creating a computable search algorithm that looks for complex strings, deriving a mathematical contradiction between the logarithmic length of the search parameter and the exponential complexity of the generated string.

### Chaitin's Incompleteness Theorem:
A rigorous information-theoretic equivalent to Gödel's First Incompleteness Theorem. The project proves that any sound, computably enumerable formal system can only prove statements of the form "$K(x) > L$" up to a specific constant $L \le c$, which is determined by the complexity of the formal system itself. 

## Architectural Choices
* **Extended Naturals (ENat):** Complexity is defined as the infimum (`sInf`) of the set of valid program lengths. By operating in `ENat` (Naturals with a $\top$ element), the theory handles non-terminating programs and empty sets natively.
* **Standard Binary Encoding (Nat.bits):** Rather than relying on custom artificial bijections, the project leverages Lean's native binary representation of natural numbers. By rigorously proving the injectivity and computability of `Nat.bits` (and its left-inverse), the theory seamlessly lifts from bit strings to natural numbers.
* **Monadic Computability (Part):** Maps (and computable decompressors) are modeled using Lean's `Part` monad (partial functions), allowing for standard handling of halting/non-halting computations and integration with Mathlib's `Partrec` API.
* **Mathlib Standards:** The codebase strictly adheres to Lean 4 and Mathlib naming conventions (`lowerCamelCase` for theorems, `UpperCamelCase` for structures), ensuring maximal compatibility and idiomatic proof styles.

## Project Structure
The repository is organized into three main directories, reflecting a bottom-up approach to formalizing the theory:

```text
KolmogorovMathlib/
├── Foundation/
│   ├── NatEncoding.lean
│   ├── RecursivelyEnumerable.lean
│   └── UnboundedSearch.lean
├── Core/
│   ├── Basic.lean
│   ├── UniversalDecompressor.lean
│   └── Invariance.lean
└── Complexity/
    ├── Properties.lean
    ├── Incompressibility.lean
    ├── NatComplexity.lean
    ├── Uncomputability.lean
    ├── Chaitin.lean
    └── ChaitinCorollaries.lean
---

## File-by-File Documentation: Foundation
The `Foundation/` directory contains the mathematical and algorithmic prerequisites needed to build the core theory. These files extend Lean 4's Mathlib with custom computability proofs, search operators, and string encodings.

### 1. Foundation/NatEncoding.lean
**Purpose:** Establishing the foundational mapping between natural numbers and bit strings.
To rigorously define the Kolmogorov complexity of a natural number and trigger Berry's paradox, we must map numbers to strings. This file formally proves that Lean's standard canonical binary representation (`Nat.bits`) is structurally sound for Algorithmic Information Theory.
* **Key Components:**
    * `decodeBits`: A custom left-inverse to `Nat.bits` that evaluates a little-endian bit string back to a natural number.
    * `natBitsInjective`: The critical proof that `Nat.bits` is strictly injective, ensuring no two distinct numbers share the same binary representation.
    * `length_natBits_le`: Establishes the bounds of the binary string ($|bits(n)| \le n$), crucial for the logarithmic growth bounds used in Berry's Paradox.

### 2. Foundation/RecursivelyEnumerable.lean
**Purpose:** Formalizing Computably Enumerable (RE) and co-RE sets.
This module establishes the abstract definitions of RE and co-RE sets, along with their closure properties. 
* **Key Components:**
    * `IsRE` / `IsCoRE`: Defines relations based on the domain of partial recursive functions.
    * `IsRE.existsInList`: A master lemma for bounded existential search over RE sets, proven via dovetailing over a candidate list.
    * `boundedPrograms`: A computable generator for finite lists of bitstrings, essential for search algorithms.

### 3. Foundation/UnboundedSearch.lean
**Purpose:** Formalizing the $\mu$-operator (Unbounded Search) and the "Computability Bridge".
A recurring challenge in formalizing computability is bridging the gap between a logical proof of existence ($\exists n, P(n)$) and the algorithmic process of finding that $n$. This file mathematically proves that if a property is computable and guaranteed to exist, the linear search for its first occurrence is a valid computable function.
* **Key Components:**
    * `Computable.unboundedSearch`: The master lemma of the file. It takes a decidable, computable predicate $P(k, n)$ and a proof of existence, and proves that the mapping $k \mapsto \min \{n \mid P(k, n)\}$ (implemented via `Nat.find`) is `Computable`.

---

## File-by-File Documentation: Core
The `Core/` directory represents the semantic heart of the project. It defines the central concepts of AIT, constructs the Universal Decompressor, and culminates in the formal proof of the Invariance Theorem.

### 4. Core/Basic.lean
**Purpose:** Establishing the foundational ontology for Kolmogorov complexity.
This file translates the abstract mathematical concepts of AIT into rigorous Lean 4 types.
* **Key Components:**
    * `Map`: Defined as `BitString × BitString →. BitString`. The use of the `Part` monad (`→.`) encapsulates the fact that abstract execution might not halt.
    * `produces`: Formalizes the relationship "map $D$ outputs $x$ given program $p$ and context $y$".
    * `condK` & `plainK`: Defines conditional and plain Kolmogorov complexity as the infimum (`sInf`) of the set of valid program lengths.
    * `isOptimalConditional`: Defines universality. A map is optimal if it can simulate any other computable decompressor with at most a constant additive overhead.

### 5. Core/UniversalDecompressor.lean
**Purpose:** Constructing the Conditional Universal Decompressor.
This file builds a Universal Decompressor $U$ that multiplexes an infinite number of computable algorithms onto a single tape using a prefix-free encoding.
* **Key Components:**
    * `unaryPrefix`: Implements unary prefix coding ($n$ is encoded as $n$ trues followed by a false).
    * `universalDecompressor`: Defines the map that parses the prefix to find the simulated machine's index, and then simulates it on the rest of the tape.
    * `isDecompressorUniversalDecompressor`: The heavy-lifting proof of the file, proving that the Universal Decompressor is itself fully computable (partial recursive).

### 6. Core/Invariance.lean
**Purpose:** Formalizing the Kolmogorov-Solomonoff-Chaitin Invariance Theorem.
This foundational theorem proves that the choice of programming language or decompressor does not matter up to an additive constant.
* **Key Components:**
    * `existsCodeOfIsDecompressor`: Connects our abstract definition of computable maps with Mathlib's Gödel numbering (`Nat.Partrec.Code`).
    * `sInfLeSInfAdd`: A lattice-theoretic lemma bridging constant additions with infimums.
    * `existsIsOptimalConditional`: The main theorem. It proves that the `universalDecompressor` satisfies the `isOptimalConditional` predicate, establishing the invariance of complexity.

---

## File-by-File Documentation: Complexity
The `Complexity/` directory contains the high-level theorems and applications of Algorithmic Information Theory, culminating in uncomputability and Chaitin's theorem.

### 7. Complexity/Properties.lean
**Purpose:** Establishing the fundamental information inequalities and topological properties.
* **Key Components:**
    * `plainKLeLength`, `condKSelf`, `condKLePlainK`: Core bounds of algorithmic information.
    * `plainKMapLe`: The Information Processing Inequality. Computable deterministic processes cannot generate new algorithmic information.
    * `condKLeIsRe` & `plainKGtIsCore`: Proves that the set of strings with complexity $\le N$ is Computably Enumerable (RE), and complexity $> N$ is co-RE.

### 8. Complexity/Incompressibility.lean
**Purpose:** Formalizing the combinatorics of binary strings and the Pigeonhole Principle.
* **Key Components:**
    * `programsLe`: Generates the binary tree of all programs up to length $k$.
    * `compressibleWords` & `stringsOfLength`: Formalizes subsets of strings based on their complexity bounds and literal lengths.
    * `existsIncompressibleString`: The central theorem proving by contradiction (via the Pigeonhole Principle) that for any length $n$, there exists at least one string whose Kolmogorov complexity is strictly $\ge n$.

### 9. Complexity/NatComplexity.lean
**Purpose:** Lifting Kolmogorov complexity from binary strings to Natural Numbers.
* **Key Components:**
    * `plainKNat` & `condKNat`: Defines the complexity of a natural number $n$ as the complexity of its canonical binary string `Nat.bits n`.
    * `existsPlainKNatGt`: Proves that there exist natural numbers of arbitrarily high complexity.
    * `plainKNatInvariance`: A Universality theorem proving that alternative computable encodings for natural numbers only change the complexity by at most an additive constant.

### 10. Complexity/Uncomputability.lean
**Purpose:** The formal proof of the uncomputability of Kolmogorov Complexity (Berry's Paradox).
* **Key Components:**
    * `growthLemma`: An arithmetic lemma proving that $2^k$ strictly dominates logarithmic length $|k| + c$.
    * `noComputableUnboundedLowerBound`: A generalized uncomputability theorem. Proves that there is no computable, unbounded lower bound for `plainK`. If one existed, we could compute Berry's algorithm and reach a contradiction where an output's complexity is both $> 2^k$ and $\le |k| + c$.
    * `notComputablePlainKNat`: The direct corollary establishing that $K(x)$ is not a computable function.

### 11. Complexity/Chaitin.lean
**Purpose:** Formalizing Chaitin's Incompleteness Theorem.
* **Key Components:**
    * `FormalSystem`: A structure defining an abstract formal system capable of expressing complexity bounds, requiring a computable enumerator of its theorems.
    * `chaitinBound`: Proves that for any such sound formal system, there exists a constant $c$ representing its "information limit".
    * `chaitinIncompleteness`: The main theorem. Proves that there exist true statements of the form "$K(x) > L$" that the system cannot prove, serving as an information-theoretic equivalent to Gödel's First Incompleteness Theorem.

### 12. Complexity/ChaitinCorollaries.lean
**Purpose:** Generalizing Chaitin's Theorem.
* **Key Components:**
    * `Expresses`: An interface asserting that a general system can soundly express and parse a specific relation.
    * `chaitinGeneralized`: Proves that any sufficiently strong formal system—specifically, one that can express all co-RE (co-computably enumerable) relations—is subject to information-theoretic incompleteness.    