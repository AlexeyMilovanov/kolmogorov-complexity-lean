/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Tuples.Basic
import KolmogorovMathlib.CommonInformation.PlainSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.PairComplexity
/-!
# The chain rule for tuples of strings
SUV Section 10.1, p. 317.
The chain rule for an `n`-tuple, with logarithmic precision (`tuple_chain_rule`):
`C(x_1, …, x_n) = C(x_1) + C(x_2 | x_1) + ⋯ + C(x_n | x_1, …, x_{n-1}) + O(log N)`, proved by
adjoining the components in increasing index order and applying the binary chain bounds at
every step.  `lowerIndices i` is the set of conditions of the `i`-th term.
All complexities in this file are **plain** complexities with respect to an explicit
decompressor `D`, quantified by `isOptimalConditional D`.  The one-term inequalities of
Theorem 204, which the chain rule proves, are in `Complexity/Tuples/OneTerm.lean`, and their
prefix version (Problem 284) is in `Complexity/Tuples/PrefixOneTerm.lean`.
-/
namespace Kolmogorov
open Finset
variable {n : ℕ}
/-- The indices strictly below `i`, in the natural ordering of `Fin n`: the conditions that
the `i`-th term of the chain rule carries.  SUV Section 10.1, p. 317. -/
def lowerIndices (i : Fin n) : Finset (Fin n) := Finset.univ.filter fun j => j < i
private lemma length_listCode_le (l : List BitString) (N : ℕ)
    (h : ∀ x ∈ l, x.length ≤ N) :
    (listCode l).length ≤ l.length * (2 * N + 1) := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [length_listCode_cons, List.length_cons]
      have hx := h x List.mem_cons_self
      have hl : ∀ y ∈ l, y.length ≤ N := fun y hy => h y (List.mem_cons_of_mem x hy)
      nlinarith [ih hl]
private lemma tupleCode_length_le {m : ℕ} (x : Fin m → BitString) (N : ℕ)
    (h : tupleMaxLength x ≤ N) :
    (tupleCode x).length ≤ m * (2 * N + 1) := by
  unfold tupleCode
  have hcode := length_listCode_le (List.ofFn x) N (by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact (length_le_tupleMaxLength x i).trans h)
  simpa using hcode
private def appendLastCode (w : BitString) : BitString :=
  listCode (decodeListCode (decodeFirst w) ++ decodeListCode (decodeSecond w))
private lemma appendLastCode_computable : Computable appendLastCode := by
  have hfirst : Computable (fun w => decodeListCode (decodeFirst w)) :=
    decodeListCode_computable.comp decodeFirst_computable
  have hsecond : Computable (fun w => decodeListCode (decodeSecond w)) :=
    decodeListCode_computable.comp decodeSecond_computable
  exact listCode_computable.comp (Computable₂.comp Primrec.list_append.to_comp hfirst hsecond)
@[simp] private lemma appendLastCode_pair (x : Fin (n + 1) → BitString) :
    appendLastCode
        (pairCode (tupleCode (fun i : Fin n => x i.castSucc))
          (listCode [x (Fin.last n)])) = tupleCode x := by
  unfold appendLastCode tupleCode
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeListCode_listCode,
    decodeListCode_listCode, List.ofFn_succ']
  rw [List.concat_eq_append]
private lemma lowerIndices_last :
    lowerIndices (Fin.last n) = Finset.univ.map Fin.castSuccEmb := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [lowerIndices]
  · simp [lowerIndices]
private lemma lowerIndices_castSucc (i : Fin n) :
    lowerIndices i.castSucc = (lowerIndices i).map Fin.castSuccEmb := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · apply iff_of_false
    · simpa only [lowerIndices, Finset.mem_filter, Finset.mem_univ, true_and] using
        (not_lt_of_ge (Fin.le_last i.castSucc))
    · simp only [Finset.mem_map, Fin.coe_castSuccEmb, Fin.castSucc_ne_last,
        and_false, exists_false, not_false_eq_true]
  · simp [lowerIndices]
private lemma subtupleCode_map_castSucc (x : Fin (n + 1) → BitString)
    (S : Finset (Fin n)) :
    subtupleCode x (S.map Fin.castSuccEmb) =
      subtupleCode (fun i : Fin n => x i.castSucc) S := by
  unfold subtupleCode
  have hmono : StrictMonoOn (Fin.castSucc : Fin n → Fin (n + 1)) S :=
    fun _ _ _ _ hij => Fin.strictMono_castSucc hij
  rw [← hmono.map_finsetSort]
  simp [Function.comp_def]
@[simp] private lemma tupleCondK_castSucc (D : Map) (x : Fin (n + 1) → BitString)
    (i : Fin n) :
    tupleCondK D x {i.castSucc} (lowerIndices i.castSucc) =
      tupleCondK D (fun j : Fin n => x j.castSucc) {i} (lowerIndices i) := by
  unfold tupleCondK
  rw [lowerIndices_castSucc, subtupleCode_map_castSucc]
  have hsingle := subtupleCode_map_castSucc x ({i} : Finset (Fin n))
  simp only [Finset.map_singleton] at hsingle
  change subtupleCode x {i.castSucc} = _ at hsingle
  rw [hsingle]
@[simp] private lemma tupleCondK_last (D : Map) (x : Fin (n + 1) → BitString) :
    tupleCondK D x {Fin.last n} (lowerIndices (Fin.last n)) =
      condK D (listCode [x (Fin.last n)])
        (tupleCode (fun i : Fin n => x i.castSucc)) := by
  unfold tupleCondK
  rw [lowerIndices_last, subtupleCode_map_castSucc, subtupleCode_univ]
  simp [subtupleCode]
private def TupleChainUpper (D : Map) (n : ℕ) : Prop :=
  ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
    ((tuplePlainK D x Finset.univ).toNat : ℝ)
        - ∑ i : Fin n, ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ)
      ≤ (logSlack c N : ℝ)
private def TupleChainLower (D : Map) (n : ℕ) : Prop :=
  ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
    (∑ i : Fin n, ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ))
        - ((tuplePlainK D x Finset.univ).toNat : ℝ)
      ≤ (logSlack c N : ℝ)
/- The empty tuple is the base case of the upper chain bound.  Its code is the empty string,
whose complexity is bounded by the constant supplied by optimality. -/
private lemma tupleChainUpper_zero (D : Map) (hD : isOptimalConditional D) :
    TupleChainUpper D 0 := by
  obtain ⟨c, hc⟩ := plainK_le_length D hD
  refine ⟨c, fun N x _ => ?_⟩
  have hcomplexity : (plainK D []).toNat ≤ c := by
    have h := ENat.toNat_le_toNat (hc [])
    simpa using h
  simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_zero, sub_zero]
  have htuple : tuplePlainK D x Finset.univ = plainK D [] := by
    simp [tuplePlainK, subtupleCode]
  rw [htuple]
  exact_mod_cast hcomplexity.trans (Nat.le_add_left c (c * (Nat.bits N).length))
/- Adjoining the last coordinate is the induction step for the upper chain bound.  Apply the
binary upper chain inequality and absorb its error together with the induction error. -/
private lemma tupleChainUpper_succ (D : Map) (hD : isOptimalConditional D) (n : ℕ)
    (hchain : TupleChainUpper D n) : TupleChainUpper D (n + 1) := by
  obtain ⟨cOld, hOld⟩ := hchain
  obtain ⟨cPair, hPair⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD appendLastCode appendLastCode_computable
  obtain ⟨cLiteral, hLiteral⟩ := plainK_le_length D hD
  obtain ⟨cFold, hFold⟩ :=
    logSlack_absorb_of_le_linear cPair (4 * n + 2) (2 * n + cLiteral + 3)
  refine ⟨cOld + cFold + cMap, fun N x hx => ?_⟩
  let headTuple : Fin n → BitString := fun i => x i.castSucc
  let lastCode := listCode [x (Fin.last n)]
  let pair := pairCode (tupleCode headTuple) lastCode
  have hprefixMax : tupleMaxLength headTuple ≤ N := by
    apply Finset.sup_le
    intro i _
    exact (length_le_tupleMaxLength x i.castSucc).trans hx
  obtain ⟨kPrefix, hkPrefix⟩ := exists_plainComplexityValue D hD (tupleCode headTuple)
  obtain ⟨kLast, hkLast⟩ :=
    exists_plainConditionalComplexityValue D hD lastCode (tupleCode headTuple)
  obtain ⟨kPair, hkPair⟩ := exists_plainComplexityValue D hD pair
  have hpairChain :
      kPair ≤ kPrefix + kLast + logSlack cPair (kPair + 1) := by
    exact hPair (tupleCode headTuple) lastCode kPrefix kLast kPair hkPrefix hkLast hkPair
  have hprefixNat :
      (tuplePlainK D headTuple Finset.univ).toNat = kPrefix := by
    unfold tuplePlainK
    rw [subtupleCode_univ, hkPrefix]
    simp
  have hlastNat :
      (tupleCondK D x {Fin.last n} (lowerIndices (Fin.last n))).toNat = kLast := by
    rw [tupleCondK_last]
    change (condK D lastCode (tupleCode headTuple)).toNat = kLast
    rw [hkLast]
    simp
  have hind := hOld N headTuple hprefixMax
  rw [hprefixNat] at hind
  have hsum :
      (∑ i : Fin (n + 1),
          ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ)) =
        (∑ i : Fin n,
          ((tupleCondK D headTuple {i} (lowerIndices i)).toNat : ℝ)) +
        ((tupleCondK D x {Fin.last n} (lowerIndices (Fin.last n))).toNat : ℝ) := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [headTuple]
  have htuplePair :
      (tuplePlainK D x Finset.univ).toNat ≤ kPair + cMap := by
    have h := hMap pair
    have hdecode : appendLastCode pair = tupleCode x := by
      dsimp only [pair, headTuple, lastCode]
      exact appendLastCode_pair x
    rw [hdecode, hkPair] at h
    have hnat := ENat.toNat_le_toNat h
      (WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top kPair, ENat.natCast_ne_top cMap⟩)
    rw [ENat.toNat_add (ENat.natCast_ne_top kPair) (ENat.natCast_ne_top cMap),
      ENat.toNat_natCast, ENat.toNat_natCast] at hnat
    simpa [tuplePlainK, subtupleCode_univ] using hnat
  have hprefixLength : (tupleCode headTuple).length ≤ n * (2 * N + 1) :=
    tupleCode_length_le headTuple N hprefixMax
  have hlastLength : (x (Fin.last n)).length ≤ N :=
    (length_le_tupleMaxLength x (Fin.last n)).trans hx
  have hpairLength :
      pair.length ≤ (4 * n + 2) * N + (2 * n + 2) := by
    dsimp [pair, lastCode]
    rw [length_pairCode, length_pairCode]
    simp only [List.length_nil, add_zero]
    nlinarith
  have hkPairLength : kPair ≤ pair.length + cLiteral := by
    have h := hLiteral pair
    rw [hkPair] at h
    exact_mod_cast h
  have hkPairLinear :
      kPair + 1 ≤ (4 * n + 2) * N + (2 * n + cLiteral + 3) := by
    omega
  have hfolded : logSlack cPair (kPair + 1) ≤ logSlack cFold N :=
    hFold N (kPair + 1) hkPairLinear
  have hcombined :
      logSlack cOld N + logSlack cFold N + cMap ≤
        logSlack (cOld + cFold + cMap) N := by
    calc
      logSlack cOld N + logSlack cFold N + cMap =
          logSlack (cOld + cFold) N + cMap := by rw [logSlack_add_const]
      _ ≤ logSlack (cOld + cFold + cMap) N :=
        logSlack_add_nat_le (cOld + cFold) cMap N
  have hpairChainReal :
      (kPair : ℝ) ≤ kPrefix + kLast + logSlack cPair (kPair + 1) := by
    exact_mod_cast hpairChain
  have htuplePairReal :
      ((tuplePlainK D x Finset.univ).toNat : ℝ) ≤ kPair + cMap := by
    exact_mod_cast htuplePair
  have hfoldedReal :
      (logSlack cPair (kPair + 1) : ℝ) ≤ logSlack cFold N := by
    exact_mod_cast hfolded
  have hcombinedReal :
      (logSlack cOld N : ℝ) + logSlack cFold N + cMap ≤
        logSlack (cOld + cFold + cMap) N := by
    exact_mod_cast hcombined
  rw [hsum, hlastNat]
  linarith
/- The reverse chain bound is immediate for the empty tuple because its left-hand side is
non-positive. -/
private lemma tupleChainLower_zero (D : Map) : TupleChainLower D 0 := by
  refine ⟨0, fun N x _ => ?_⟩
  simp [logSlack]
/- The map inverse to `appendLastCode`: it splits a tuple code into the prefix tuple and the
last coordinate, repackaged as a nested pair.  It is used, in the reverse direction of the
upper step, to bound the pair code's complexity by the whole tuple's. -/
private def splitLastCode (w : BitString) : BitString :=
  pairCode (listCode (decodeListCode w).reverse.tail.reverse)
    (listCode [(decodeListCode w).reverse.headI])
private lemma splitLastCode_computable : Computable splitLastCode := by
  have hrev : Computable (fun w => (decodeListCode w).reverse) :=
    Primrec.list_reverse.to_comp.comp decodeListCode_computable
  have hfirst : Computable (fun w => listCode (decodeListCode w).reverse.tail.reverse) :=
    listCode_computable.comp
      (Primrec.list_reverse.to_comp.comp (Primrec.list_tail.to_comp.comp hrev))
  have hsecond : Computable (fun w => listCode [(decodeListCode w).reverse.headI]) :=
    listCode_computable.comp
      (Computable₂.comp Primrec.list_cons.to_comp
        (Primrec.list_headI.to_comp.comp hrev) (Computable.const []))
  exact Computable₂.comp pairCode_computable hfirst hsecond
@[simp] private lemma splitLastCode_pair (x : Fin (n + 1) → BitString) :
    splitLastCode (tupleCode x) =
      pairCode (tupleCode (fun i : Fin n => x i.castSucc))
        (listCode [x (Fin.last n)]) := by
  unfold splitLastCode tupleCode
  rw [decodeListCode_listCode, List.ofFn_succ', List.concat_eq_append]
  simp [List.reverse_append]
/- Adjoining the last coordinate is the induction step for the lower chain bound.  Apply the
binary lower chain inequality and absorb its error together with the induction error. -/
private lemma tupleChainLower_succ (D : Map) (hD : isOptimalConditional D) (n : ℕ)
    (hchain : TupleChainLower D n) : TupleChainLower D (n + 1) := by
  obtain ⟨cOld, hOld⟩ := hchain
  obtain ⟨cPair, hPair⟩ := pairPlainK_chain_lower_values D hD
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD splitLastCode splitLastCode_computable
  obtain ⟨cLiteral, hLiteral⟩ := plainK_le_length D hD
  obtain ⟨cFold, hFold⟩ :=
    logSlack_absorb_of_le_linear cPair (4 * n + 2) (2 * n + cLiteral + 3)
  refine ⟨cOld + cFold + cMap, fun N x hx => ?_⟩
  let headTuple : Fin n → BitString := fun i => x i.castSucc
  let lastCode := listCode [x (Fin.last n)]
  let pair := pairCode (tupleCode headTuple) lastCode
  have hprefixMax : tupleMaxLength headTuple ≤ N := by
    apply Finset.sup_le
    intro i _
    exact (length_le_tupleMaxLength x i.castSucc).trans hx
  obtain ⟨kPrefix, hkPrefix⟩ := exists_plainComplexityValue D hD (tupleCode headTuple)
  obtain ⟨kLast, hkLast⟩ :=
    exists_plainConditionalComplexityValue D hD lastCode (tupleCode headTuple)
  obtain ⟨kPair, hkPair⟩ := exists_plainComplexityValue D hD pair
  have hpairChain :
      kPrefix + kLast ≤ kPair + logSlack cPair (kPair + 1) := by
    exact hPair (tupleCode headTuple) lastCode kPrefix kLast kPair hkPrefix hkLast hkPair
  have hprefixNat :
      (tuplePlainK D headTuple Finset.univ).toNat = kPrefix := by
    unfold tuplePlainK
    rw [subtupleCode_univ, hkPrefix]
    simp
  have hlastNat :
      (tupleCondK D x {Fin.last n} (lowerIndices (Fin.last n))).toNat = kLast := by
    rw [tupleCondK_last]
    change (condK D lastCode (tupleCode headTuple)).toNat = kLast
    rw [hkLast]
    simp
  have hind := hOld N headTuple hprefixMax
  rw [hprefixNat] at hind
  have hsum :
      (∑ i : Fin (n + 1),
          ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ)) =
        (∑ i : Fin n,
          ((tupleCondK D headTuple {i} (lowerIndices i)).toNat : ℝ)) +
        ((tupleCondK D x {Fin.last n} (lowerIndices (Fin.last n))).toNat : ℝ) := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [headTuple]
  have htuplePair :
      kPair ≤ (tuplePlainK D x Finset.univ).toNat + cMap := by
    have h := hMap (tupleCode x)
    have hsplit : splitLastCode (tupleCode x) = pair := by
      dsimp only [pair, headTuple, lastCode]
      exact splitLastCode_pair x
    rw [hsplit, hkPair] at h
    have hfin : plainK D (tupleCode x) ≠ ⊤ := plainK_ne_top D hD _
    have hnat := ENat.toNat_le_toNat h
      (WithTop.add_ne_top.mpr ⟨hfin, ENat.natCast_ne_top _⟩)
    rw [ENat.toNat_add hfin (ENat.natCast_ne_top _)] at hnat
    simpa [tuplePlainK, subtupleCode_univ] using hnat
  have hprefixLength : (tupleCode headTuple).length ≤ n * (2 * N + 1) :=
    tupleCode_length_le headTuple N hprefixMax
  have hlastLength : (x (Fin.last n)).length ≤ N :=
    (length_le_tupleMaxLength x (Fin.last n)).trans hx
  have hpairLength :
      pair.length ≤ (4 * n + 2) * N + (2 * n + 2) := by
    dsimp [pair, lastCode]
    rw [length_pairCode, length_pairCode]
    simp only [List.length_nil, add_zero]
    nlinarith
  have hkPairLength : kPair ≤ pair.length + cLiteral := by
    have h := hLiteral pair
    rw [hkPair] at h
    exact_mod_cast h
  have hkPairLinear :
      kPair + 1 ≤ (4 * n + 2) * N + (2 * n + cLiteral + 3) := by
    omega
  have hfolded : logSlack cPair (kPair + 1) ≤ logSlack cFold N :=
    hFold N (kPair + 1) hkPairLinear
  have hcombined :
      logSlack cOld N + logSlack cFold N + cMap ≤
        logSlack (cOld + cFold + cMap) N := by
    calc
      logSlack cOld N + logSlack cFold N + cMap =
          logSlack (cOld + cFold) N + cMap := by rw [logSlack_add_const]
      _ ≤ logSlack (cOld + cFold + cMap) N :=
        logSlack_add_nat_le (cOld + cFold) cMap N
  have hpairChainReal :
      (kPrefix : ℝ) + kLast ≤ kPair + logSlack cPair (kPair + 1) := by
    exact_mod_cast hpairChain
  have htuplePairReal :
      (kPair : ℝ) ≤ ((tuplePlainK D x Finset.univ).toNat : ℝ) + cMap := by
    exact_mod_cast htuplePair
  have hfoldedReal :
      (logSlack cPair (kPair + 1) : ℝ) ≤ logSlack cFold N := by
    exact_mod_cast hfolded
  have hcombinedReal :
      (logSlack cOld N : ℝ) + logSlack cFold N + cMap ≤
        logSlack (cOld + cFold + cMap) N := by
    exact_mod_cast hcombined
  rw [hsum, hlastNat]
  linarith
/- The forward half of the tuple chain rule.  It is obtained by adjoining the components in
increasing index order and applying the upper binary chain bound at every step. -/
private lemma tuple_chain_rule_upper (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
      ((tuplePlainK D x Finset.univ).toNat : ℝ)
          - ∑ i : Fin n, ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ)
        ≤ (logSlack c N : ℝ) := by
  change TupleChainUpper D n
  induction n with
  | zero => exact tupleChainUpper_zero D hD
  | succ n ih => simpa [Nat.succ_eq_add_one] using tupleChainUpper_succ D hD n ih
/- The reverse half of the tuple chain rule.  Iterating the lower binary chain bound in the
same increasing index order makes the intermediate prefix-complexity terms telescope. -/
private lemma tuple_chain_rule_lower (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
      (∑ i : Fin n, ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ))
          - ((tuplePlainK D x Finset.univ).toNat : ℝ)
        ≤ (logSlack c N : ℝ) := by
  change TupleChainLower D n
  induction n with
  | zero => exact tupleChainLower_zero D
  | succ n ih => simpa [Nat.succ_eq_add_one] using tupleChainLower_succ D hD n ih
/-- The **chain rule for an `n`-tuple of strings**, with logarithmic precision:
`C(x_1, …, x_n) = C(x_1) + C(x_2 | x_1) + ⋯ + C(x_n | x_1, …, x_{n-1}) + O(log N)`
for tuples all of whose components have length at most `N`.  The constant depends on `n`.
SUV Section 10.1, p. 317. -/
theorem tuple_chain_rule (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
      |((tuplePlainK D x Finset.univ).toNat : ℝ)
          - ∑ i : Fin n, ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ)|
        ≤ (logSlack c N : ℝ) := by
  obtain ⟨cUpper, hUpper⟩ := tuple_chain_rule_upper D hD
  obtain ⟨cLower, hLower⟩ := tuple_chain_rule_lower D hD
  refine ⟨max cUpper cLower, fun N x hx => ?_⟩
  rw [abs_le]
  constructor
  · have hSlack : (logSlack cLower N : ℝ) ≤ logSlack (max cUpper cLower) N := by
      exact_mod_cast logSlack_mono_left (le_max_right cUpper cLower) N
    linarith [hLower N x hx]
  · exact (hUpper N x hx).trans (by
      exact_mod_cast logSlack_mono_left (le_max_left cUpper cLower) N)
end Kolmogorov
