# KolmogorovMathlib: Formalization of Algorithmic Information Theory in Lean 4

This project provides a rigorous mathematical formalization of the foundations of algorithmic information theory (Kolmogorov complexity) using the Lean 4 theorem prover.

The primary goal of this project is to prove the Kolmogorov-Solomonoff Theorem on the existence of an optimal universal Turing machine, and to formalize the basic properties of conditional and plain complexity based on the computability of Partial Recursive Functions (`Partrec`).

## 🏗 Project Architecture

The project is built following strict modularity standards (in the spirit of Mathlib), where the "engineering" construction of objects is strictly separated from abstract proofs:

1. **`Basic.lean`** — Fundamental types, complexity definitions, and optimality predicates.
2. **`ListComputability.lean`** — Low-level utilities and computability proofs for lists.
3. **`UniversalConstruction.lean`** — Algorithmic implementation (construction) of the Universal Machine and the proof of its computability.
4. **`UniversalProof.lean`** — The mathematical proof of the Kolmogorov-Solomonoff Theorem.
5. **`BasicProperties.lean`** — The API of the library: elegant proofs of theorems that use the optimal machine as a black box.

---

## 📂 Detailed File Description

### 1. `Basic.lean`
This file lays the mathematical foundation of the theory.

* **`BitString`**: An alias for `List Bool`, representing binary strings.
* **`Machine`**: The signature of a Turing machine (decompressor). Defined as a partial function from a pair (program, context) to a string: `BitString × BitString →. BitString`.
* **`program_length`**: A function to measure the length of a program. Left as an abstraction to allow a seamless transition to a prefix-free metric in the future.
* **`is_decompressor`**: A predicate asserting that a machine `D` is a computable partial recursive function (`Partrec`).
* **`produces`**: The predicate $D(p, y) = x$. It asserts that program `p` with context `y` outputs `x`.
* **`candidate_lengths`**: The set of lengths of all programs that successfully generate `x` given `y`.
* **`conditional_K`**: Conditional Kolmogorov complexity $K(x|y)$. Defined as the infimum (`sInf`) of the `candidate_lengths` set. Returns an extended natural number (`ENat`).
* **`plain_K`**: Plain (unconditional) complexity $K(x)$. Defined as $K(x|\epsilon)$ (where the context is the empty list `[]`).
* **`is_optimal_conditional`**: The core predicate. A machine $U$ is optimal if it is computable and, for any other computable machine $D$, there exists a constant $c$ such that $K_U(x|y) \le K_D(x|y) + c$.

### 2. `ListComputability.lean`
Contains primitive recursive functions for manipulating bit tapes. Provides a strictly typed foundation for building machines.

* **`prefix_len`**: Calculates the number of consecutive `true`s at the beginning of a string (reads the unary prefix).
* **`prefix_len_primrec`**: Proof that `prefix_len` is primitive recursive.
* **`list_drop`**: Drops $n$ elements from the beginning of a list.
* **`list_drop_primrec`**: Proof that `list_drop` is a computable function of two arguments (`Primrec₂`).

### 3. `UniversalConstruction.lean`
The "factory" for producing the Universal Machine. There are no infimums or abstract complexities here; it contains strictly algorithms.

* **`unary_prefix`**: Generates a string of $n$ ones followed by a zero. Used to encode the index of the simulated machine.
* **`universal_machine`**: The interpreter. It reads the prefix, decodes it into a machine code (`Nat.Partrec.Code`), and runs this code on the remaining bits and the context `y`.
* **`universal_machine_combinator`**: A strict combinator-friendly version of the interpreter (used for proofs).
* **`universal_simulation`**: The simulation lemma. Proves that $U(\text{prefix}(D) ++ p, y) = D(p, y)$.
* **`U_nat`**: A numerical version of the machine operating on Gödel numbers (to prove `Partrec`).
* **`universal_is_decompressor`**: The key theorem of the file. Proves that the constructed machine is indeed computable (`is_decompressor`).

### 4. `UniversalProof.lean`
The mathematical bridge between the algorithmic implementation and infimums over sets.

* **`exists_code_for_machine`**: A lemma connecting any abstract computable `Machine` to its Gödel number (`Code`).
* **`sInf_le_sInf_add_const`**: A lattice theory lemma. If for every element in set $S_2$ there is an element in $S_1$ that is smaller by at most a constant $c$, then the infimum of $S_1$ is less than or equal to the infimum of $S_2$ plus $c$.
* **`exists_optimal_conditional_machine`**: **The Kolmogorov-Solomonoff Theorem**. Proves the existence of a machine satisfying the `is_optimal_conditional` predicate by providing the constructed `universal_machine` as a witness.

### 5. `BasicProperties.lean`
The API layer. This file only imports the abstract definitions (`Basic.lean`) and proves theorems about the optimal machine treating it as a "black box".

* **`plain_complexity_le_length`**: Proves that the complexity of a string is bounded by its length: 
  $$K(x) \le |x| + c$$
  *Proof sketch:* The target machine $D$ is defined as the identity function `id_machine` that returns the program itself. The optimality of $U$ automatically provides the required constant $c$.