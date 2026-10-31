/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Encoding
import KolmogorovMathlib.RandomStrings.Plain.Enumeration
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity
import KolmogorovMathlib.RandomStrings.Plain.Markers
import KolmogorovMathlib.RandomStrings.Plain.PrefixInterface
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Log

/-!
# Towers, the finite crossing and the total structural proxy

This module contains the number-theoretic and combinatorial part of the structural proxy
construction.

* The tower sequence `tower`, the range `TowerRange n q` of targets attached to a tower
  parameter `n`, the computable function `towerFloor` recovering `n` from any target `q` in that
  range (`tower_floor_spec`, `tower_floor_eq`), and the separation of the range from the next
  tower number (`tower_range_separation`).
* The finite crossing lemma (Blueprint node `key:crossing`): for a table of exact complexities
  `α j = K(Y_j | n)` and `β j = K(Y_j, α j | q)` with `Y_j = (q, j)`, adjacent values of `β`
  differ by a uniform constant (`structural_proxy_crossing`), and for large `q` the last index
  `j_*` with `j_* ≤ β j_*` exists, is below `q`, and satisfies `β j_* < j_* + 1 + c`
  (`structural_proxy_crossing_finite`, `structural_proxy_crossing_common`).
* The total computable proxy (Blueprint node `key:proxy`): the bounded tables
  `boundedProxyAlpha` and `boundedProxyBeta`, the proxy `computeStructuralProxy` returning
  `(q, j_*)` on valid candidate records, the derived values `structuralProxyAlpha`,
  `structuralProxyBeta`, `structuralProxyDelta`, the carrier `proxyCarrier`, and the
  specification `StructuralProxySpec` collecting the length, exactness and carrier properties.

The files `StructuralProxy.Symmetry` and the later modules of the structural proxy chapter use
these definitions to prove the carrier identity and the constant-precision symmetry transfer
(Blueprint node `key:symmetry`).
-/

namespace Kolmogorov.Milovanov

/-- The fixed tower sequence, starting at one. Blueprint node `key:proxy`. -/
def tower : ℕ → ℕ
  | 0 => 1
  | i + 1 => 2 ^ tower i

/-- Membership in the fixed tower sequence. Blueprint node `key:proxy`. -/
def IsTower (n : ℕ) : Prop := ∃ i : ℕ, tower i = n

/-- The integer upper bound on target complexity and input length.
Blueprint node `key:proxy`. On tower parameters the base-two logarithm is exact. -/
def towerRangeBound (n : ℕ) : ℕ := n ^ Nat.log2 n

/-- The half-open target range at a tower parameter. Blueprint node `key:proxy`. -/
def TowerRange (n q : ℕ) : Prop := n ≤ q ∧ q < towerRangeBound n

/-- Bounded iteration of the tower successor, stopping before exceeding `q`.
Blueprint node `key:proxy`. The fuel decreases structurally. -/
private def towerFloorLoop (q : ℕ) : ℕ → ℕ → ℕ
  | 0, current => current
  | fuel + 1, current =>
    let next := 2 ^ current
    if next ≤ q then towerFloorLoop q fuel next else current

/-- The largest tower number at most `q`, with zero as the default when `q = 0`.
Blueprint node `key:proxy`. At most `q` successor tests are made. -/
def towerFloor (q : ℕ) : ℕ :=
  if q = 0 then 0 else towerFloorLoop q q 1

/-- One step of the tower search: move from `c` to `2 ^ c` as long as this stays below `q`. -/
private def towerNext (q c : ℕ) : ℕ := if 2 ^ c ≤ q then 2 ^ c else c

private lemma towerFloorLoop_eq_iterate (q fuel current : ℕ) :
    towerFloorLoop q fuel current = (towerNext q)^[fuel] current := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    by_cases h : 2 ^ current ≤ q
    · simp only [towerNext, h, ↓reduceIte, ← ih, towerFloorLoop]
    · have hfix : towerNext q current = current := by simp only [towerNext, h, ↓reduceIte]
      rw [hfix, Function.iterate_fixed hfix]
      simp only [towerFloorLoop, h, ↓reduceIte]

private lemma towerNext_primrec₂ : Primrec₂ towerNext := by
  have h_pow2 : Primrec (fun c : ℕ ↦ 2 ^ c) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  have h_le : PrimrecPred (fun p : ℕ × ℕ ↦ 2 ^ p.2 ≤ p.1) :=
    PrimrecRel.comp Primrec.nat_le (h_pow2.comp Primrec.snd) Primrec.fst
  have h_cond : Primrec (fun p : ℕ × ℕ ↦ bif decide (2 ^ p.2 ≤ p.1) then 2 ^ p.2 else p.2) :=
    Primrec.cond (PrimrecPred.decide h_le) (h_pow2.comp Primrec.snd) Primrec.snd
  exact Primrec.of_eq h_cond fun p ↦ Bool.cond_decide (2 ^ p.2 ≤ p.1) (2 ^ p.2) p.2

private lemma towerFloor_primrec : Primrec towerFloor := by
  have h_iter : Primrec (fun q : ℕ ↦ (towerNext q)^[q] 1) :=
    Primrec.nat_iterate Primrec.id (Primrec.const 1) towerNext_primrec₂
  have h_dec : Primrec (fun q : ℕ ↦ decide (q = 0)) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const 0))
  have h_cond : Primrec (fun q : ℕ ↦ bif decide (q = 0) then 0 else (towerNext q)^[q] 1) :=
    Primrec.cond h_dec (Primrec.const 0) h_iter
  refine Primrec.of_eq h_cond fun q ↦ ?_
  rw [Bool.cond_decide, towerFloor, towerFloorLoop_eq_iterate]

/-- Tower predecessor recovery is a total computable function.
Blueprint node `key:proxy`. -/
theorem tower_floor_computable : Computable towerFloor :=
  Primrec.to_comp towerFloor_primrec

/-- Consecutive tower numbers increase. -/
theorem tower_lt_tower_add_one (n : ℕ) : tower n < tower (n + 1) := Nat.lt_two_pow_self

/-- Tower numbers are strictly increasing in their indices. -/
theorem strictMono_tower : StrictMono tower :=
  strictMono_nat_of_lt_succ tower_lt_tower_add_one

/-- Tower numbers are monotone in their indices. -/
theorem tower_le_tower {n m : ℕ} (h : n ≤ m) : tower n ≤ tower m :=
  strictMono_tower.monotone h

/-- The tower sequence dominates its index. -/
theorem le_tower : ∀ i : ℕ, i ≤ tower i
  | 0 => Nat.zero_le _
  | i + 1 => (Nat.succ_le_succ (le_tower i)).trans (Nat.lt_two_pow_self (n := tower i))

private lemma add_one_le_tower : ∀ i, i + 1 ≤ tower i
  | 0 => by decide
  | i + 1 => Nat.lt_of_le_of_lt (add_one_le_tower i) Nat.lt_two_pow_self

/-- The invariant of the bounded tower search: after `fuel` more steps from a tower number
`current ≤ q`, the result is the greatest tower number at most `q`. -/
private lemma towerFloorLoop_spec (q fuel current : ℕ)
    (h_current : IsTower current) (h_bound : current ≤ q)
    (h_fuel : ∃ i, tower i = current ∧ ∀ j, tower j ≤ q → j ≤ i + fuel) :
    IsTower (towerFloorLoop q fuel current) ∧ towerFloorLoop q fuel current ≤ q ∧
    ∀ n : ℕ, IsTower n → n ≤ q → n ≤ towerFloorLoop q fuel current := by
  induction fuel generalizing current with
  | zero =>
    obtain ⟨i, hi, hmax⟩ := h_fuel
    refine ⟨h_current, h_bound, ?_⟩
    rintro n ⟨j, rfl⟩ hn_le
    rw [← hi]
    exact strictMono_tower.monotone (hmax j hn_le)
  | succ fuel ih =>
    obtain ⟨i, hi, hmax⟩ := h_fuel
    dsimp only [towerFloorLoop]
    split_ifs with h_le
    · refine ih (2 ^ current) ⟨i + 1, by rw [← hi]; rfl⟩ h_le ⟨i + 1, by rw [← hi]; rfl, ?_⟩
      intro j hj
      have := hmax j hj
      omega
    · refine ⟨h_current, h_bound, ?_⟩
      rintro n ⟨j, rfl⟩ hn_le
      have hj_le_i : j ≤ i := by
        by_contra h_not
        refine h_le ?_
        rw [← hi]
        exact le_trans (strictMono_tower.monotone (by omega : i + 1 ≤ j)) hn_le
      rw [← hi]
      exact strictMono_tower.monotone hj_le_i

/-- The bounded tower iteration returns the greatest tower number below a positive input.
Blueprint node `key:proxy`. -/
theorem tower_floor_spec (q : ℕ) (hq : 0 < q) :
    IsTower (towerFloor q) ∧ towerFloor q ≤ q ∧
      ∀ n : ℕ, IsTower n → n ≤ q → n ≤ towerFloor q := by
  simp only [towerFloor, hq.ne', ↓reduceIte]
  refine towerFloorLoop_spec q q 1 ⟨0, rfl⟩ hq ⟨0, rfl, fun j hj ↦ ?_⟩
  have := add_one_le_tower j
  omega

private lemma mul_self_lt_two_pow {x : ℕ} (hx : 5 ≤ x) : x * x < 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h1 : 2 * k + 1 ≤ k * k := by nlinarith
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    have h3 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    omega

/-- The prescribed tower range lies strictly below the next tower number.
Blueprint node `key:proxy`. The lower cutoff is independent of later padding constants. -/
theorem tower_range_separation (n : ℕ) (hn : 32 ≤ n) (ht : IsTower n) :
    towerRangeBound n < extensionScale n := by
  dsimp [towerRangeBound, extensionScale]
  rcases ht with ⟨i, rfl⟩
  cases i with
  | zero =>
    revert hn
    decide
  | succ i =>
    have h_n : tower (i + 1) = 2 ^ tower i := rfl
    rw [h_n, Nat.log2_two_pow, ← Nat.pow_mul]
    apply Nat.pow_lt_pow_right (by decide)
    have h3 : 2 ^ 5 ≤ 2 ^ tower i := hn
    have h2 : 5 ≤ tower i := (Nat.pow_le_pow_iff_right (by decide)).mp h3
    exact mul_self_lt_two_pow h2

/-- Between two tower numbers the larger one is at least two to the power of the smaller. -/
private theorem two_pow_le_of_isTower_lt {n n' : ℕ} (ht : IsTower n) (ht' : IsTower n')
    (h : n < n') : 2 ^ n ≤ n' := by
  rcases ht with ⟨i, rfl⟩
  rcases ht' with ⟨j, rfl⟩
  exact strictMono_tower.monotone (strictMono_tower.lt_iff_lt.mp h : i + 1 ≤ j)

/-- A target in the prescribed range determines its tower parameter: `towerFloor q = n` whenever
`n ≥ 32` is a tower number and `q` lies in `TowerRange n`. Blueprint node `key:proxy`. -/
theorem tower_floor_eq (n q : ℕ) (hn : 32 ≤ n) (ht : IsTower n)
    (hq : TowerRange n q) : towerFloor q = n := by
  have hq_pos : 0 < q := lt_of_lt_of_le (by omega) hq.1
  obtain ⟨hf_tower, hf_le, hf_max⟩ := tower_floor_spec q hq_pos
  rcases eq_or_lt_of_le (hf_max n ht hq.1) with rfl | h_lt
  · rfl
  · have h2 : 2 ^ n ≤ towerFloor q := two_pow_le_of_isTower_lt ht hf_tower h_lt
    have h7 : towerRangeBound n < extensionScale n := tower_range_separation n hn ht
    have h8 : extensionScale n = 2 ^ n := rfl
    have h12 : 2 ^ n ≤ q := le_trans h2 hf_le
    have h10 := hq.2
    omega

/-- The binary numeric pair `Y_j = (q,j)`. Blueprint node `key:crossing`. -/
def proxyPair (q j : ℕ) : BitString := pairCode (bits q) (bits j)

/-- A finite table of exact complexity values, specified without totalizing `ENat`.
Blueprint node `key:crossing`. Only indices at most `q` are constrained. -/
def ExactProxyTable (B : Base) (n q : ℕ) (α β : ℕ → ℕ) : Prop :=
  ∀ j ≤ q, KP B.D (proxyPair q j) (bits n) = (α j : ENat) ∧
    KP B.D (pairCode (proxyPair q j) (bits (α j))) (bits q) = (β j : ENat)

/-- The finite set of crossing indices for any natural-valued table.
Blueprint node `key:crossing`. -/
def proxyCrossingIndices (q : ℕ) (β : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (q + 1)).filter (fun j ↦ j ≤ β j)

/-- The maximum crossing index, computed by a finite supremum with default zero.
Blueprint node `key:crossing`. The crossing set always contains that default. -/
def proxyCrossingIndex (q : ℕ) (β : ℕ → ℕ) : ℕ :=
  (proxyCrossingIndices q β).sup id

/-- Zero is a crossing index for every natural-valued table, including bounded false candidates.
Blueprint node `key:crossing`. -/
theorem zero_mem_proxy_crossing_indices (q : ℕ) (β : ℕ → ℕ) :
    0 ∈ proxyCrossingIndices q β := by
  simp [proxyCrossingIndices]

/-- The natural number written in binary in the second component of a code, zero if malformed. -/
def decodeSecondNat (w : BitString) : ℕ := (Milovanov.decodeNat (decodeSecond w)).getD 0

/-- Reading the numeric second component of a code is computable. -/
lemma decodeSecondNat_computable : Computable decodeSecondNat :=
  Computable.option_getD (bits_computable.2.comp decodeSecond_computable) (Computable.const 0)

@[simp] private lemma decodeSecondNat_pairCode_bits (x : BitString) (a : ℕ) :
    decodeSecondNat (pairCode x (bits a)) = a := by
  simp [decodeSecondNat, decodeSecond_pairCode, decodeNat_bits]

/-- Replaces the numeric second component `j` of a pair code by `j + 1`. -/
private def proxyPairSucc (w : BitString) : BitString :=
  pairCode (decodeFirst w) (bits (decodeSecondNat w + 1))

/-- Replaces the numeric second component `j` of a pair code by `j - 1`. -/
private def proxyPairPred (w : BitString) : BitString :=
  pairCode (decodeFirst w) (bits (decodeSecondNat w - 1))

private lemma proxyPairSucc_computable : Computable proxyPairSucc := by
  have h_nat : Computable (fun w : BitString ↦ decodeSecondNat w + 1) :=
    Computable.of_eq (Computable.succ.comp decodeSecondNat_computable) fun w ↦ rfl
  have h_pair : Computable (fun w : BitString ↦
      (decodeFirst w, bits (decodeSecondNat w + 1))) :=
    decodeFirst_computable.pair (bits_computable.1.comp h_nat)
  exact Computable.of_eq (pairCode_computable.comp h_pair) fun w ↦ rfl

private lemma proxyPairPred_computable : Computable proxyPairPred := by
  have h_nat : Computable (fun w : BitString ↦ decodeSecondNat w - 1) :=
    Computable.of_eq (Computable.pred.comp decodeSecondNat_computable) fun w ↦ rfl
  have h_pair : Computable (fun w : BitString ↦
      (decodeFirst w, bits (decodeSecondNat w - 1))) :=
    decodeFirst_computable.pair (bits_computable.1.comp h_nat)
  exact Computable.of_eq (pairCode_computable.comp h_pair) fun w ↦ rfl

private lemma proxyPairSucc_proxyPair (q j : ℕ) :
    proxyPairSucc (proxyPair q j) = proxyPair q (j + 1) := by
  simp [proxyPairSucc, proxyPair, decodeFirst_pairCode]

private lemma proxyPairPred_proxyPair_succ (q j : ℕ) :
    proxyPairPred (proxyPair q (j + 1)) = proxyPair q j := by
  simp [proxyPairPred, proxyPair, decodeFirst_pairCode]

/-- Adjacent exact values `K(Y_j | n)` differ by a uniform constant, because `(q, j)` and
`(q, j + 1)` are computable from each other by fixed maps. -/
private theorem abs_alpha_succ_sub_le (B : Base) :
    ∃ cAlpha : ℕ, ∀ n q j : ℕ, ∀ α β : ℕ → ℕ,
      ExactProxyTable B n q α β → j < q → |(α (j + 1) : ℤ) - α j| ≤ (cAlpha : ℤ) := by
  obtain ⟨c1, hc1⟩ := literal_and_tuple_code_interface_prefix_map B _ proxyPairSucc_computable
  obtain ⟨c2, hc2⟩ := literal_and_tuple_code_interface_prefix_map B _ proxyPairPred_computable
  refine ⟨c1 + c2, fun n q j α β h_exact h_j ↦ ?_⟩
  have H1 := hc1 (proxyPair q j) (bits n)
  have H2 := hc2 (proxyPair q (j + 1)) (bits n)
  rw [proxyPairSucc_proxyPair, (h_exact j h_j.le).1, (h_exact (j + 1) h_j).1] at H1
  rw [proxyPairPred_proxyPair_succ, (h_exact j h_j.le).1, (h_exact (j + 1) h_j).1] at H2
  have h_c1 : α (j + 1) ≤ α j + c1 := ENat.natCast_le_natCast.mp H1
  have h_c2 : α j ≤ α (j + 1) + c2 := ENat.natCast_le_natCast.mp H2
  rw [abs_le]
  constructor <;> omega

/-- Shifts a natural number by a signed offset, truncating at zero. -/
private def shiftNat (d : ℤ) (a : ℕ) : ℕ :=
  if 0 ≤ d then a + d.toNat else a - (-d).toNat

private lemma shiftNat_computable (d : ℤ) : Computable (shiftNat d) := by
  unfold shiftNat
  split_ifs
  · exact Primrec.to_comp (Primrec.nat_add.comp Primrec.id (Primrec.const d.toNat))
  · exact Primrec.to_comp (Primrec.nat_sub.comp Primrec.id (Primrec.const (-d).toNat))

private lemma shiftNat_sub (a b : ℕ) : shiftNat ((b : ℤ) - a) a = b := by
  unfold shiftNat
  split_ifs <;> omega

/-- Moves the pair `Y_j` of a code `(Y_j, α)` to a neighbour by `move` and shifts the number
`α` by `d`. -/
private def proxyShiftMap (move : BitString → BitString) (d : ℤ) (w : BitString) : BitString :=
  pairCode (move (decodeFirst w)) (bits (shiftNat d (decodeSecondNat w)))

private lemma proxyShiftMap_computable {move : BitString → BitString} (hmove : Computable move)
    (d : ℤ) : Computable (proxyShiftMap move d) :=
  pairCode_computable.comp
    ((hmove.comp decodeFirst_computable).pair
      (bits_computable.1.comp ((shiftNat_computable d).comp decodeSecondNat_computable)))

private lemma proxyShiftMap_succ (q j a b : ℕ) :
    proxyShiftMap proxyPairSucc ((b : ℤ) - a) (pairCode (proxyPair q j) (bits a)) =
      pairCode (proxyPair q (j + 1)) (bits b) := by
  simp [proxyShiftMap, decodeFirst_pairCode, proxyPairSucc_proxyPair, shiftNat_sub]

private lemma proxyShiftMap_pred (q j a b : ℕ) :
    proxyShiftMap proxyPairPred ((b : ℤ) - a) (pairCode (proxyPair q (j + 1)) (bits a)) =
      pairCode (proxyPair q j) (bits b) := by
  simp [proxyShiftMap, decodeFirst_pairCode, proxyPairPred_proxyPair_succ, shiftNat_sub]

/-- Adjacent exact values `K(Y_j, α_j | q)` differ by a uniform constant, because
`(Y_{j+1}, α_{j+1})` is computed from `(Y_j, α_j)` by one of finitely many signed offsets. -/
private theorem abs_beta_succ_sub_le (B : Base) (cAlpha : ℕ) :
    ∃ cBeta : ℕ, ∀ n q j : ℕ, ∀ α β : ℕ → ℕ,
      ExactProxyTable B n q α β → j < q →
      |(α (j + 1) : ℤ) - α j| ≤ (cAlpha : ℤ) →
      |(β (j + 1) : ℤ) - β j| ≤ (cBeta : ℤ) := by
  choose eSucc hSucc using fun d : ℤ ↦ literal_and_tuple_code_interface_prefix_map B _
    (proxyShiftMap_computable proxyPairSucc_computable d)
  choose ePred hPred using fun d : ℤ ↦ literal_and_tuple_code_interface_prefix_map B _
    (proxyShiftMap_computable proxyPairPred_computable d)
  refine ⟨∑ d ∈ Finset.Icc (-(cAlpha : ℤ)) cAlpha, (eSucc d + ePred d), ?_⟩
  intro n q j α β h_exact h_j h_alpha
  have h_mem : ∀ d : ℤ, |d| ≤ cAlpha → eSucc d + ePred d ≤
      ∑ d ∈ Finset.Icc (-(cAlpha : ℤ)) cAlpha, (eSucc d + ePred d) := fun d hd ↦
    Finset.single_le_sum (f := fun d ↦ eSucc d + ePred d) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_Icc.mpr (abs_le.mp hd))
  have h_alpha' : |(α j : ℤ) - α (j + 1)| ≤ cAlpha := by rwa [abs_sub_comm]
  have H1 := hSucc ((α (j + 1) : ℤ) - α j) (pairCode (proxyPair q j) (bits (α j))) (bits q)
  have H2 := hPred ((α j : ℤ) - α (j + 1)) (pairCode (proxyPair q (j + 1)) (bits (α (j + 1))))
    (bits q)
  rw [proxyShiftMap_succ, (h_exact j h_j.le).2, (h_exact (j + 1) h_j).2] at H1
  rw [proxyShiftMap_pred, (h_exact j h_j.le).2, (h_exact (j + 1) h_j).2] at H2
  have h_c1 : β (j + 1) ≤ β j + eSucc ((α (j + 1) : ℤ) - α j) := ENat.natCast_le_natCast.mp H1
  have h_c2 : β j ≤ β (j + 1) + ePred ((α j : ℤ) - α (j + 1)) := ENat.natCast_le_natCast.mp H2
  have h_s := h_mem _ h_alpha
  have h_p := h_mem _ h_alpha'
  rw [abs_le]
  constructor <;> omega

/-- Exact adjacent beta values differ by a uniform integer constant.
Blueprint node `key:crossing`. The chapter's tower range is retained. -/
theorem structural_proxy_crossing (B : Base) :
    ∃ cBeta n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, IsTower n → ∀ q : ℕ, TowerRange n q →
      ∀ α β : ℕ → ℕ, ExactProxyTable B n q α β →
        ∀ j < q, |(β (j + 1) : ℤ) - β j| ≤ (cBeta : ℤ) := by
  obtain ⟨cAlpha, hcAlpha⟩ := abs_alpha_succ_sub_le B
  obtain ⟨cBeta, hcBeta⟩ := abs_beta_succ_sub_le B cAlpha
  refine ⟨cBeta, 32, le_rfl, fun n _ _ q _ α β h j hj ↦ ?_⟩
  exact hcBeta n q j α β h hj (hcAlpha n q j α β h hj)

private lemma mem_proxyCrossingIndices {q j : ℕ} {β : ℕ → ℕ} :
    j ∈ proxyCrossingIndices q β ↔ j ≤ q ∧ j ≤ β j := by
  simp only [proxyCrossingIndices, Finset.mem_filter, Finset.mem_range]
  omega

private lemma proxyCrossingIndex_mem (q : ℕ) (β : ℕ → ℕ) :
    proxyCrossingIndex q β ∈ proxyCrossingIndices q β := by
  obtain ⟨j, hj, hj_eq⟩ := Finset.exists_mem_eq_sup (proxyCrossingIndices q β)
    ⟨0, zero_mem_proxy_crossing_indices q β⟩ id
  rw [proxyCrossingIndex, hj_eq]
  exact hj

private lemma le_proxyCrossingIndex {q j : ℕ} {β : ℕ → ℕ} (hj : j ∈ proxyCrossingIndices q β) :
    j ≤ proxyCrossingIndex q β :=
  Finset.le_sup (f := id) hj

/-- The literal complexity of the endpoint pair: `K(Y_q, α_q | q)` is linear in `|bits q|`. -/
private theorem beta_endpoint_le (B : Base) {n q : ℕ} {α β : ℕ → ℕ}
    (hExact : ExactProxyTable B n q α β) :
    β q ≤ 45 * (bits q).length + 37 + 4 * B.cD := by
  obtain ⟨hAlpha, hBeta⟩ := hExact q le_rfl
  have hBoundAlpha := literal_and_tuple_code_interface B (proxyPair q q) (bits n)
  have hBoundBeta :=
    literal_and_tuple_code_interface B (pairCode (proxyPair q q) (bits (α q))) (bits q)
  rw [hAlpha] at hBoundAlpha
  rw [hBeta] at hBoundBeta
  have hAlphaNat : α q ≤ literalBound B (proxyPair q q) := by exact_mod_cast hBoundAlpha
  have hBetaNat : β q ≤ literalBound B (pairCode (proxyPair q q) (bits (α q))) := by
    exact_mod_cast hBoundBeta
  have hLenYq : (proxyPair q q).length = 3 * (bits q).length + 1 := by
    rw [proxyPair, length_pairCode]
    omega
  have hLenBetaCode : (pairCode (proxyPair q q) (bits (α q))).length =
      2 * (proxyPair q q).length + 1 + (bits (α q)).length := by
    rw [length_pairCode]
    omega
  have hLenAlphaBits : (bits (α q)).length ≤ α q + 1 := length_bits_le (α q)
  have hLogAlpha : Nat.clog 2 ((proxyPair q q).length + 2) ≤ (proxyPair q q).length + 2 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hLogBeta : Nat.clog 2 ((pairCode (proxyPair q q) (bits (α q))).length + 2) ≤
      (pairCode (proxyPair q q) (bits (α q))).length + 2 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  dsimp [literalBound] at hAlphaNat hBetaNat
  omega

private lemma linear_lt_two_pow (t : ℕ) (ht : 20 ≤ t) : 46 * t + 25 < 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    omega

/-- For large targets the endpoint `q` is not a crossing index, since `β q` is logarithmic
in `q`. -/
private theorem not_mem_proxyCrossingIndices_of_large (B : Base) :
    ∃ q₀ : ℕ, ∀ n q α β, q ≥ q₀ → TowerRange n q → ExactProxyTable B n q α β →
      q ∉ proxyCrossingIndices q β := by
  set C := 37 + 4 * B.cD with hC
  refine ⟨2 ^ (C + 20), fun n q α β hq _ hExact hmem ↦ ?_⟩
  have hqpos : 0 < q := lt_of_lt_of_le (Nat.two_pow_pos _) hq
  have hsize : C + 20 < Nat.size q := by
    by_contra! hcontra
    have h_pow_mono : 2 ^ Nat.size q ≤ 2 ^ (C + 20) := Nat.pow_le_pow_right (by decide) hcontra
    have h_lt : q < 2 ^ Nat.size q := Nat.lt_size_self q
    omega
  obtain ⟨s, hs⟩ : ∃ s, Nat.size q = s + 1 := ⟨Nat.size q - 1, by omega⟩
  have hq_lower : 2 ^ s ≤ q := Nat.lt_size.mp (by omega)
  have h_bits : (bits q).length ≤ s + 1 := by
    have hc : q < 2 ^ (s + 1) := hs ▸ Nat.lt_size_self q
    exact length_bits_le_of_lt hc
  have h_beta := beta_endpoint_le B hExact
  have h_pow := linear_lt_two_pow s (by omega)
  have h_le := (mem_proxyCrossingIndices.mp hmem).2
  omega

/-- If the last crossing index is below the endpoint, the adjacent-difference bound gives
`β j_* < j_* + 1 + cBeta`. -/
private theorem beta_proxyCrossingIndex_lt (cBeta q : ℕ) (β : ℕ → ℕ)
    (hdiff : ∀ j < q, |(β (j + 1) : ℤ) - β j| ≤ (cBeta : ℤ))
    (hqnotin : q ∉ proxyCrossingIndices q β) :
    β (proxyCrossingIndex q β) < proxyCrossingIndex q β + 1 + cBeta := by
  have hmem := mem_proxyCrossingIndices.mp (proxyCrossingIndex_mem q β)
  have hlt : proxyCrossingIndex q β < q := by
    refine lt_of_le_of_ne hmem.1 fun h ↦ hqnotin ?_
    have := proxyCrossingIndex_mem q β
    rwa [h] at this
  have hnext : ¬ (proxyCrossingIndex q β + 1 ≤ β (proxyCrossingIndex q β + 1)) := fun h ↦ by
    have := le_proxyCrossingIndex (mem_proxyCrossingIndices.mpr ⟨hlt, h⟩)
    omega
  have h_abs := abs_le.mp (hdiff _ hlt)
  omega

/-- For sufficiently large targets the last crossing is strictly before the endpoint.
Blueprint node `key:crossing`. Its beta value is within the explicit adjacent-difference loss. -/
theorem structural_proxy_crossing_finite (B : Base) :
    ∃ cBeta n₀ q₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, IsTower n →
      ∀ q ≥ q₀, TowerRange n q → ∀ α β : ℕ → ℕ, ExactProxyTable B n q α β →
        (proxyCrossingIndices q β).Nonempty ∧ q ∉ proxyCrossingIndices q β ∧
        proxyCrossingIndex q β ≤ β (proxyCrossingIndex q β) ∧
        β (proxyCrossingIndex q β) < proxyCrossingIndex q β + 1 + cBeta := by
  obtain ⟨cBeta, n₀, hn₀, hdiff⟩ := structural_proxy_crossing B
  obtain ⟨q₀, hq₀⟩ := not_mem_proxyCrossingIndices_of_large B
  refine ⟨cBeta, n₀, q₀, hn₀, fun n hn hnTower q hq hnq α β hExact ↦ ?_⟩
  have hqnotin := hq₀ n q α β hq hnq hExact
  exact ⟨⟨_, proxyCrossingIndex_mem q β⟩, hqnotin,
    (mem_proxyCrossingIndices.mp (proxyCrossingIndex_mem q β)).2,
    beta_proxyCrossingIndex_lt cBeta q β (hdiff n hn hnTower q hnq α β hExact) hqnotin⟩

/-- The same adjacent-difference constant controls the finite crossing at every large target.
Blueprint node `key:crossing`. All exact table entries are explicit finite witnesses. -/
theorem structural_proxy_crossing_common (B : Base) :
    ∃ cBeta n₀ q₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, IsTower n →
      ∀ q : ℕ, TowerRange n q → ∀ α β : ℕ → ℕ, ExactProxyTable B n q α β →
        (∀ j < q, |(β (j + 1) : ℤ) - β j| ≤ (cBeta : ℤ)) ∧
        (q₀ ≤ q → (proxyCrossingIndices q β).Nonempty ∧ q ∉ proxyCrossingIndices q β ∧
          proxyCrossingIndex q β ≤ β (proxyCrossingIndex q β) ∧
          β (proxyCrossingIndex q β) < proxyCrossingIndex q β + 1 + cBeta) := by
  obtain ⟨cBeta1, n1, h1, h2⟩ := structural_proxy_crossing B
  obtain ⟨cBeta2, n2, q2, h3, h4⟩ := structural_proxy_crossing_finite B
  refine ⟨max cBeta1 cBeta2, max n1 n2, q2, le_trans h1 (le_max_left _ _), ?_⟩
  intro n hn ht q hq α β htab
  refine ⟨fun j hj ↦ le_trans (h2 n (le_trans (le_max_left _ _) hn) ht q hq α β htab j hj)
    (Nat.cast_le.mpr (le_max_left _ _)), fun hq2 ↦ ?_⟩
  obtain ⟨h7a, h7b, h7c, h7d⟩ := h4 n (le_trans (le_max_right _ _) hn) ht q hq2 hq α β htab
  exact ⟨h7a, h7b, h7c, by omega⟩

/-- The bounded value of `K(Y_j | n)` at a candidate's verified timestamp.
Blueprint node `key:proxy`. The frozen literal default handles malformed records. -/
def boundedProxyAlpha (B : Base) (n : ℕ) (candidate : Candidate) (q j : ℕ) : ℕ :=
  candidatePrefixComplexity B n candidate (proxyPair q j) (bits n)

/-- The bounded value of `K(Y_j, α̂_j | q)` on the same candidate snapshot.
Blueprint node `key:proxy`. The natural alpha field uses `bits`. -/
def boundedProxyBeta (B : Base) (n : ℕ) (candidate : Candidate) (q j : ℕ) : ℕ :=
  candidatePrefixComplexity B n candidate
    (pairCode (proxyPair q j) (bits (boundedProxyAlpha B n candidate q j))) (bits q)

/-- The largest bounded crossing index `j_* ≤ q`.
Blueprint node `key:proxy`. This finite computation is total for every candidate record. -/
def structuralProxyIndex (B : Base) (n : ℕ) (candidate : Candidate) (q : ℕ) : ℕ :=
  proxyCrossingIndex q (boundedProxyBeta B n candidate q)

/-- The total candidate proxy, returning `(q,j_*)` on valid records and `[]` otherwise.
Blueprint node `key:proxy`. Only bounded prefix computations are used. -/
def computeStructuralProxy (B : Base) (n : ℕ) (candidate : Candidate) (q : ℕ) : BitString :=
  if validCandidate B n candidate then proxyPair q (structuralProxyIndex B n candidate q)
  else []

/-- The bounded alpha value of the chosen proxy. Blueprint node `key:proxy`. -/
def structuralProxyAlpha (B : Base) (n : ℕ) (candidate : Candidate) (q : ℕ) : ℕ :=
  candidatePrefixComplexity B n candidate (computeStructuralProxy B n candidate q) (bits n)

/-- The bounded beta value of the chosen proxy and its bounded alpha.
Blueprint node `key:proxy`. -/
def structuralProxyBeta (B : Base) (n : ℕ) (candidate : Candidate) (q : ℕ) : ℕ :=
  candidatePrefixComplexity B n candidate
    (pairCode (computeStructuralProxy B n candidate q)
      (bits (structuralProxyAlpha B n candidate q))) (bits q)

/-- The signed correction `Δ̂ = β̂ - α̂`, with no truncated subtraction.
Blueprint node `key:proxy`. -/
def structuralProxyDelta (B : Base) (n : ℕ) (candidate : Candidate) (q : ℕ) : ℤ :=
  (structuralProxyBeta B n candidate q : ℤ) - structuralProxyAlpha B n candidate q

/-- The carrier `(q̃,α,β)` uses the frozen triple code and binary natural fields.
Blueprint node `key:proxy`. -/
def proxyCarrier (proxy : BitString) (α β : ℕ) : BitString := triple proxy α (bits β)

/-- The base `(x,q̃,α)` for the upper-scale future volume, before attaching its extension.
Blueprint node `key:symmetry`. The association is `pairCode (pairCode x q̃) (bits α)`. -/
def proxyBase (x proxy : BitString) (α : ℕ) : BitString :=
  pairCode (pairCode x proxy) (bits α)

/-- The full proxy specification with common length and carrier constants.
Blueprint node `key:proxy`. Exactness identifies all computed numbers with `ENat` complexities. -/
def StructuralProxySpec (B : Base) (cLen cCar n : ℕ) (candidate : Candidate) (q : ℕ) : Prop :=
  let proxy := computeStructuralProxy B n candidate q
  let α := structuralProxyAlpha B n candidate q
  let β := structuralProxyBeta B n candidate q
  proxy.length ≤ cLen * Nat.log2 (q + 2) + cLen ∧
  decodeNat (decodeFirst proxy) = some q ∧
  ExactProxyTable B n q (boundedProxyAlpha B n candidate q) (boundedProxyBeta B n candidate q) ∧
  KP B.D proxy (bits n) = (α : ENat) ∧
  KP B.D (pairCode proxy (bits α)) (bits q) = (β : ENat) ∧
  ∀ k : ℕ, KP B.D (proxyCarrier proxy α β) (bits n) = (k : ENat) →
    |(k : ℤ) - α| ≤ (cCar : ℤ)

end Kolmogorov.Milovanov
