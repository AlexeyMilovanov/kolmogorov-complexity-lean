/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Native.Adapters

/-!
# The effective native referee

For a native tuple `θ = (c, e, e₀, flag)` this file defines the finite referee
`native_counting_referee` that computes the cumulative complexity count
`|{x : C_U(x) ≤ m}|` from an oracle table.  The referee is a finite decision tree
(a `QueryTree`) that reads, in a fixed order, the finitely many oracle coordinates
`nativeCoordinateList` which the universal raw-word table can inspect.  At each leaf it runs
a binary search over `[0, 2 ^ (m + 1))`, deciding every threshold `k` with the clocked
bounded-acceptance test `nativeRefereeTest` of the tuple's machine `c`.

The main result is `native_referee_effective_interface` (blueprint node
`native:referee-interface`):

* the encoded tree and the leaf values are computable uniformly in the tuple, the padding and
  the size parameter, using only the finite transition table of the machine;
* every string inspected by the tree has length at most the polynomial `nativeTupleBound θ`,
  and every variable coordinate retained by the construction has length and threshold within the
  corresponding polynomial bounds.

Further results are the binary-search theorems `native_binary_search_terminates` and
`native_binary_search_correct` (blueprint node `native:correct-referee`) and the clock bound
`native_referee_test_clock_le`.  The theorem `native_tuple_bound_polynomial` supplies the
polynomial query bound required by the generic admissibility lemma of the diagonal construction;
the clocked deciders and the family of referees build on this file.
-/

namespace Kolmogorov.Milovanov

open RandomStrings

/-- The native tuple `(c,e,e₀,flag)`, with an actual finite-state repository machine.
Blueprint node `native:referee` (supporting definition). -/
abbrev NativeTuple := OTMCode × ℕ × ℕ × NativeOracleFlag

/-- Primitive input data for uniformly computing a native tuple's finite referee.
Blueprint node `native:referee` (supporting definition). -/
abbrev NativeTupleCode := ℕ × ℕ × ℕ × NativeOracleFlag

/-- Serialize the finite transition table and the three remaining tuple fields.
Blueprint node `native:family` (supporting definition). -/
def encodeNativeTuple (θ : NativeTuple) : NativeTupleCode :=
  (encodeCode θ.1, θ.2)

/-- Total decoding of native tuple data using the existing explicit OTM decoder.
Blueprint node `native:family` (supporting definition). -/
def decodeNativeTuple (code : NativeTupleCode) : NativeTuple :=
  (decodeCode code.1, code.2)

/-- Every actual tuple is recovered exactly from its explicit finite code.
Blueprint node `native:family` (supporting lemma). -/
theorem decode_encode_native_tuple (θ : NativeTuple) :
    decodeNativeTuple (encodeNativeTuple θ) = θ := by
  simp [decodeNativeTuple, encodeNativeTuple, decodeCode_encodeCode]

/-- The tuple's polynomial target-length bound, independent of construction padding.
Blueprint node `native:referee` (supporting definition). -/
def nativeTupleBound (θ : NativeTuple) (m : ℕ) : ℕ :=
  clock θ.2.1 (nativeLiteralFactor θ.2.2.1 * (m + 1))

/-- The repository clock has precisely the polynomial shape used in the blueprint.
Blueprint node `native:referee` (supporting lemma). -/
theorem native_tuple_bound_eq (θ : NativeTuple) (m : ℕ) :
    nativeTupleBound θ m =
      (nativeLiteralFactor θ.2.2.1 * (m + 1)) ^ θ.2.1 + θ.2.1 := rfl

/-- The native polynomial fits exactly the stage-3 majorant convention.
Blueprint node `native:referee-interface` (supporting lemma). -/
theorem native_tuple_bound_polynomial (θ : NativeTuple) :
    PolynomialQueryBound (nativeTupleBound θ) := by
  refine ⟨nativeLiteralFactor θ.2.2.1 ^ θ.2.1, θ.2.1, fun m => ?_⟩
  rw [native_tuple_bound_eq, mul_pow]

/-- Materialize all raw answers determined by a coordinate table on the universal domain.
Blueprint node `native:referee` (supporting definition). -/
def nativeRefereeRawTable (θ : NativeTuple) (cU m : ℕ)
    (table : NativeCoordinateTable) : NativeRawTable :=
  (nativeRawWords (nativeTupleBound θ m)).map (fun z =>
    (z, native_oracle_answer_adapters cU θ.2.2.2 table z))

/-- One threshold test, evaluated at `clock e |g e₀ m k|`, never at the universal table bound.
Blueprint node `native:referee` (supporting definition). -/
def nativeRefereeTest (θ : NativeTuple) (cU m : ℕ) (table : NativeCoordinateTable)
    (k : ℕ) : Bool :=
  nativeClockedAcceptance θ.1 θ.2.1 (nativeTupleBound θ m)
    (nativeRefereeRawTable θ cU m table) (nativeThresholdInstance θ.2.2.1 m k)

/-- Binary search with an explicit test budget; each nonterminal step halves the interval.
Blueprint node `native:referee` (supporting definition). The returned pair retains both bounds. -/
def nativeBinarySearchState (test : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, lo, hi => (lo, hi)
  | fuel + 1, lo, hi =>
    if hi - lo ≤ 1 then (lo, hi)
    else
      let k := (lo + hi) / 2
      if test k then nativeBinarySearchState test fuel k hi
      else nativeBinarySearchState test fuel lo k

/-- A leaf's numeric output after at most `m + 1` tests on `[0,2^(m+1))`.
Blueprint node `native:referee` (supporting definition). -/
def nativeRefereeLeaf (θ : NativeTuple) (cU m : ℕ) (table : NativeCoordinateTable) : ℕ :=
  (nativeBinarySearchState (nativeRefereeTest θ cU m table) (m + 1) 0 (2 ^ (m + 1))).1

/-- Read every coordinate in order, placing the computed table output at each leaf.
Blueprint node `native:referee` (supporting definition). Both branches are built explicitly. -/
def nativeTableTree (output : NativeCoordinateTable → ℕ) :
    List Coordinate → NativeCoordinateTable → QueryTree
  | [], table => .leaf (output table)
  | q :: rest, table => .node q
      (nativeTableTree output rest ((q, false) :: table))
      (nativeTableTree output rest ((q, true) :: table))

/-- The full finite natural-leaf referee for one tuple and padding, in the stage-3 type.
Blueprint node `native:referee`. Its literal constant is exactly `d + cV`. -/
def native_counting_referee (cV : ℕ) (θ : NativeTuple) (d m : ℕ) : QueryTree :=
  nativeTableTree (nativeRefereeLeaf θ (d + cV) m)
    (nativeCoordinateList (d + cV) θ.2.2.2 (nativeTupleBound θ m)) []

/-- A binary search with enough fuel for the initial width reaches a unit interval inside the
initial one, whatever the Boolean answers of `test` are. -/
private lemma nativeBinarySearchState_unit_interval (test : ℕ → Bool) (fuel lo hi : ℕ)
    (hwidth : hi - lo ≤ 2 ^ fuel) (hlt : lo < hi) :
    (nativeBinarySearchState test fuel lo hi).2 = (nativeBinarySearchState test fuel lo hi).1 + 1 ∧
      lo ≤ (nativeBinarySearchState test fuel lo hi).1 ∧
      (nativeBinarySearchState test fuel lo hi).2 ≤ hi := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [nativeBinarySearchState]
    simp only [pow_zero] at hwidth
    omega
  | succ fuel ih =>
    simp only [nativeBinarySearchState]
    split_ifs with hunit htest
    · omega
    · have := ih ((lo + hi) / 2) hi (by rw [pow_succ] at hwidth; omega) (by omega)
      omega
    · have := ih lo ((lo + hi) / 2) (by rw [pow_succ] at hwidth; omega) (by omega)
      omega

/-- The search on `[0,2^(m+1))` with budget `m + 1` ends in an interval of width one, even for
arbitrary inconsistent Boolean answers.
Blueprint node `native:referee-interface` (supporting lemma). -/
theorem native_binary_search_terminates (test : ℕ → Bool) (m : ℕ) :
    let result := nativeBinarySearchState test (m + 1) 0 (2 ^ (m + 1))
    result.2 = result.1 + 1 ∧ result.1 < 2 ^ (m + 1) := by
  have h := nativeBinarySearchState_unit_interval test (m + 1) 0 (2 ^ (m + 1))
    (by rw [Nat.sub_zero]) (by positivity)
  exact ⟨h.1, by omega⟩

/-- If a threshold test is correct on the open interval `(lo, hi)` for a count `K ∈ [lo, hi)`,
then a search with enough fuel for the width returns `K`. -/
private lemma nativeBinarySearchState_fst_eq (test : ℕ → Bool) {fuel lo hi K : ℕ}
    (hlo : lo ≤ K) (hhi : K < hi) (hwidth : hi - lo ≤ 2 ^ fuel)
    (htest : ∀ k, lo < k → k < hi → (test k = true ↔ k ≤ K)) :
    (nativeBinarySearchState test fuel lo hi).1 = K := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [nativeBinarySearchState]
    simp only [pow_zero] at hwidth
    omega
  | succ fuel ih =>
    simp only [nativeBinarySearchState]
    split_ifs with hunit htk
    · omega
    · have hk := (htest _ (by omega) (by omega)).1 htk
      exact ih hk hhi (by rw [pow_succ] at hwidth; omega)
        (fun k hk₁ hk₂ ↦ htest k (by omega) hk₂)
    · have hk : ¬ (lo + hi) / 2 ≤ K := fun h ↦ htk ((htest _ (by omega) (by omega)).2 h)
      exact ih hlo (by omega) (by rw [pow_succ] at hwidth; omega)
        (fun k hk₁ hk₂ ↦ htest k hk₁ (by omega))

/-- Threshold answers for any count in the half-open interval return exactly that count.
Blueprint node `native:correct-referee` (supporting lemma). Zero is included. -/
theorem native_binary_search_correct (test : ℕ → Bool) (m K : ℕ)
    (hK : K < 2 ^ (m + 1))
    (htest : ∀ k, k < 2 ^ (m + 1) → (test k = true ↔ k ≤ K)) :
    (nativeBinarySearchState test (m + 1) 0 (2 ^ (m + 1))).1 = K :=
  nativeBinarySearchState_fst_eq test K.zero_le hK (by rw [Nat.sub_zero])
    fun k _ hk ↦ htest k hk

/-- Every possible threshold test's own cutoff fits the universal raw table.
Blueprint node `native:referee-interface` (supporting lemma). -/
theorem native_referee_test_clock_le (θ : NativeTuple) (m k : ℕ)
    (hk : k < 2 ^ (m + 1)) :
    clock θ.2.1 (nativeThresholdInstance θ.2.2.1 m k).length ≤ nativeTupleBound θ m := by
  have hlen := (literal_threshold_instance_length.1 θ.2.2.1).2 m k hk
  exact Nat.add_le_add_right (Nat.pow_le_pow_left hlen θ.2.1) θ.2.1

/-- One binary-search transition; terminal intervals remain fixed. -/
private def binarySearchStep (test : ℕ → Bool) (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 - s.1 ≤ 1 then s
  else if test ((s.1 + s.2) / 2) then ((s.1 + s.2) / 2, s.2)
  else (s.1, (s.1 + s.2) / 2)

/-- Iterating the transition does not move a terminal interval. -/
private lemma binarySearchStep_iterate_of_le_one (test : ℕ → Bool) (lo hi : ℕ)
    (h : hi - lo ≤ 1) (n : ℕ) : (binarySearchStep test)^[n] (lo, hi) = (lo, hi) := by
  apply Function.iterate_fixed
  simp [binarySearchStep, h]

/-- The fuel-bounded search is an iteration of its one-step transition. -/
private lemma nativeBinarySearchState_eq_iterate (test : ℕ → Bool) (n lo hi : ℕ) :
    nativeBinarySearchState test n lo hi = (binarySearchStep test)^[n] (lo, hi) := by
  induction n generalizing lo hi with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [nativeBinarySearchState, binarySearchStep]
    split_ifs with h1 h2
    · rw [binarySearchStep_iterate_of_le_one test lo hi h1 n]
    · exact ih ((lo + hi) / 2) hi
    · exact ih lo ((lo + hi) / 2)

/-- Binary search is computable uniformly in a computable test, fuel and initial interval. -/
private lemma computable_nativeBinarySearchState {α : Type*} [Primcodable α]
    (test : α → ℕ → Bool) (n lo hi : α → ℕ)
    (htest : Computable (fun p : α × ℕ => test p.1 p.2))
    (hn : Computable n) (hlo : Computable lo) (hhi : Computable hi) :
    Computable (fun a => nativeBinarySearchState (test a) (n a) (lo a) (hi a)) := by
  have hl : Computable (fun p : α × (ℕ × (ℕ × ℕ)) => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hh : Computable (fun p : α × (ℕ × (ℕ × ℕ)) => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hmid : Computable (fun p : α × (ℕ × (ℕ × ℕ)) => (p.2.2.1 + p.2.2.2) / 2) :=
    Primrec.nat_div.to_comp.comp (Primrec.nat_add.to_comp.comp hl hh) (Computable.const 2)
  have hstop : Computable (fun p : α × (ℕ × (ℕ × ℕ)) => decide (p.2.2.2 - p.2.2.1 ≤ 1)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp
      (Primrec.nat_sub.to_comp.comp hh hl) (Computable.const 1)
  have htest' : Computable (fun p : α × (ℕ × (ℕ × ℕ)) => test p.1 ((p.2.2.1 + p.2.2.2) / 2)) :=
    htest.comp (Computable.fst.pair hmid)
  have hstep : Computable₂ (fun (a : α) (p : ℕ × (ℕ × ℕ)) => binarySearchStep (test a) p.2) := by
    have hupdate := Computable.cond htest' (hmid.pair hh) (hl.pair hmid)
    have h := Computable.cond hstop (Computable.snd.comp Computable.snd) hupdate
    refine h.of_eq (fun p ↦ ?_)
    by_cases hs : p.2.2.2 - p.2.2.1 ≤ 1 <;>
      by_cases ht : test p.1 ((p.2.2.1 + p.2.2.2) / 2) <;> simp [binarySearchStep, hs, ht]
  have hrec := Computable.nat_rec hn (hlo.pair hhi) hstep
  refine hrec.of_eq (fun a ↦ ?_)
  rw [nativeBinarySearchState_eq_iterate]
  change Nat.rec (lo a, hi a) (fun _ s ↦ binarySearchStep (test a) s) (n a) =
    (binarySearchStep (test a))^[n a] (lo a, hi a)
  generalize n a = fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply']
    exact congrArg (binarySearchStep (test a)) ih

/-- The universal clock is computable in the exponent, the literal index and the size. -/
private lemma computable_clock_literal {P : Type*} [Primcodable P] (e e₀ m : P → ℕ)
    (he : Computable e) (he₀ : Computable e₀) (hm : Computable m) :
    Computable (fun p ↦ clock (e p) (nativeLiteralFactor (e₀ p) * (m p + 1))) :=
  clock_computable.comp he (Primrec.nat_mul.to_comp.comp
    (literal_threshold_instance_length.2.1.comp he₀)
    (Primrec.nat_add.to_comp.comp hm (Computable.const 1)))

/-- The raw answers of the adapters on the universal domain are computable in the table. -/
private lemma computable_raw_answer_table {P : Type*} [Primcodable P] {cU T : P → ℕ}
    {flag : P → NativeOracleFlag} {table : P → NativeCoordinateTable}
    (hcU : Computable cU) (hT : Computable T) (hflag : Computable flag)
    (htable : Computable table) :
    Computable (fun p ↦ (nativeRawWords (T p)).map
      (fun z ↦ (z, native_oracle_answer_adapters (cU p) (flag p) (table p) z))) := by
  have ha : Computable₂ (fun p z ↦ native_oracle_answer_adapters (cU p) (flag p) (table p) z) :=
    native_oracle_adapters_computable.1.comp
      ((hcU.comp Computable.fst).pair ((hflag.comp Computable.fst).pair
        ((htable.comp Computable.fst).pair Computable.snd)))
  exact Computable.list_map (native_raw_words_spec.1.comp hT) (Computable.snd.pair ha)

/-- Decoding a machine from its code preserves its Boolean bounded verdict, which is
computable in the code. -/
private lemma computable_nativeClockedAcceptance_decodeCode {P : Type*} [Primcodable P]
    {q e T : P → ℕ} {table : P → NativeRawTable} {z : P → BitString}
    (hq : Computable q) (he : Computable e) (hT : Computable T) (htable : Computable table)
    (hz : Computable z) :
    Computable (fun p ↦
      nativeClockedAcceptance (decodeCode (q p)) (e p) (T p) (table p) (z p)) := by
  have h := native_clocked_acceptance_computable.comp
    (hq.pair (he.pair (hT.pair (htable.pair hz))))
  refine h.of_eq (fun p ↦ ?_)
  dsimp only [nativeClockedAcceptance, nativeClockedAcceptanceCode]
  apply Bool.eq_iff_iff.mpr
  simp only [clockedOutcomeT_iff, decodeCode_encodeCode]

/-- The threshold test is computable in the tuple code, the padding, the size and the table. -/
private lemma computable₂_nativeRefereeTest {P : Type*} [Primcodable P]
    {tuple : P → NativeTupleCode} {cU m : P → ℕ} {table : P → NativeCoordinateTable}
    (htuple : Computable tuple) (hcU : Computable cU) (hm : Computable m)
    (htable : Computable table) :
    Computable₂ (fun p k ↦ nativeRefereeTest (decodeNativeTuple (tuple p))
      (cU p) (m p) (table p) k) := by
  have htuple' : Computable (fun p : P × ℕ ↦ tuple p.1) := htuple.comp Computable.fst
  have hq : Computable (fun p : P × ℕ ↦ (tuple p.1).1) := Computable.fst.comp htuple'
  have herest : Computable (fun p : P × ℕ ↦ (tuple p.1).2) := Computable.snd.comp htuple'
  have he : Computable (fun p : P × ℕ ↦ (tuple p.1).2.1) := Computable.fst.comp herest
  have he₀rest : Computable (fun p : P × ℕ ↦ (tuple p.1).2.2) := Computable.snd.comp herest
  have he₀ : Computable (fun p : P × ℕ ↦ (tuple p.1).2.2.1) := Computable.fst.comp he₀rest
  have hflag : Computable (fun p : P × ℕ ↦ (tuple p.1).2.2.2) := Computable.snd.comp he₀rest
  have hm' : Computable (fun p : P × ℕ ↦ m p.1) := hm.comp Computable.fst
  have hT := computable_clock_literal _ _ _ he he₀ hm'
  have hraw := computable_raw_answer_table (hcU.comp Computable.fst) hT hflag
    (htable.comp Computable.fst)
  have hparams : Computable (fun p : P × ℕ ↦ ((tuple p.1).2.2.1, m p.1, p.2)) :=
    he₀.pair (hm'.pair Computable.snd)
  have hz : Computable (fun p : P × ℕ ↦ nativeThresholdInstance (tuple p.1).2.2.1 (m p.1) p.2) :=
    (Computable.comp literal_threshold_instance_length.2.2 hparams).of_eq (fun _ ↦ rfl)
  exact Computable₂.mk
    ((computable_nativeClockedAcceptance_decodeCode hq he hT hraw hz).of_eq (fun p ↦ rfl))

/-- The leaf value of the referee is computable in the tuple code, the padding, the size and the
table. -/
private lemma computable_nativeRefereeLeaf {P : Type*} [Primcodable P]
    {tuple : P → NativeTupleCode} {cU m : P → ℕ} {table : P → NativeCoordinateTable}
    (htuple : Computable tuple) (hcU : Computable cU) (hm : Computable m)
    (htable : Computable table) :
    Computable (fun p ↦
      nativeRefereeLeaf (decodeNativeTuple (tuple p)) (cU p) (m p) (table p)) := by
  have hn : Computable (fun p ↦ m p + 1) :=
    Primrec.nat_add.to_comp.comp hm (Computable.const 1)
  have hhi : Computable (fun p ↦ 2 ^ (m p + 1)) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp.comp (Computable.const 2) hn
  exact (Computable.fst.comp (computable_nativeBinarySearchState
    (fun p k ↦ nativeRefereeTest (decodeNativeTuple (tuple p)) (cU p) (m p) (table p) k)
    _ _ _ (computable₂_nativeRefereeTest htuple hcU hm htable) hn
    (Computable.const 0) hhi)).of_eq fun p ↦ rfl

/-- Expand a pending table into its two children and postfix node label. -/
private def tableLevelItem (c : Coordinate) :
    NativeCoordinateTable ⊕ Coordinate → List (NativeCoordinateTable ⊕ Coordinate)
  | .inl t => [.inl ((c, false) :: t), .inl ((c, true) :: t), .inr c]
  | .inr q => [.inr q]

/-- Expand all pending tables once for each inspected coordinate. -/
private def tableLevels (cs : List Coordinate) : List (NativeCoordinateTable ⊕ Coordinate) :=
  cs.foldl (fun L c ↦ L.flatMap (tableLevelItem c)) [.inl []]

/-- Replace pending tables by their leaf outputs, preserving emitted node labels. -/
private def tableFinalItem (out : NativeCoordinateTable → ℕ) :
    NativeCoordinateTable ⊕ Coordinate → ℕ ⊕ Coordinate
  | .inl t => .inl (out t)
  | .inr q => .inr q

/-- The full postfix expansion of an item through the remaining coordinates. -/
private def tableExpandItem (out : NativeCoordinateTable → ℕ) (cs : List Coordinate) :
    NativeCoordinateTable ⊕ Coordinate → QueryTree.Code
  | .inl t => (nativeTableTree out cs t).encode
  | .inr q => [.inr q]

/-- Level expansion followed by leaf evaluation equals full postfix expansion. -/
private lemma map_foldl_tableLevelItem (out : NativeCoordinateTable → ℕ) (cs : List Coordinate)
    (L : List (NativeCoordinateTable ⊕ Coordinate)) :
    (cs.foldl (fun L c ↦ L.flatMap (tableLevelItem c)) L).map (tableFinalItem out) =
      L.flatMap (tableExpandItem out cs) := by
  induction cs generalizing L with
  | nil =>
    dsimp
    induction L with
    | nil => rfl
    | cons head tail ih =>
      rw [List.map_cons, List.flatMap_cons, ih]
      cases head <;> rfl
  | cons c cs ih =>
    rw [List.foldl_cons, ih, List.flatMap_assoc]
    congr 1
    funext it
    cases it with
    | inl t =>
      simp [tableExpandItem, nativeTableTree, QueryTree.encode, tableLevelItem]
    | inr q =>
      simp [tableExpandItem, tableLevelItem]

/-- The one-step expansion of a pending table is primitive recursive. -/
private lemma primrec₂_tableLevelItem :
    Primrec₂ (fun (c : Coordinate) (it : NativeCoordinateTable ⊕ Coordinate) ↦
      tableLevelItem c it) := by
  have hfalse : Primrec₂ (fun (p : Coordinate × (NativeCoordinateTable ⊕ Coordinate))
      (t : NativeCoordinateTable) ↦
        (Sum.inl ((p.1, false) :: t) : NativeCoordinateTable ⊕ Coordinate)) :=
    Primrec.sumInl.comp (Primrec.list_cons.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.const false)) Primrec.snd)
  have htrue : Primrec₂ (fun (p : Coordinate × (NativeCoordinateTable ⊕ Coordinate))
      (t : NativeCoordinateTable) ↦
        (Sum.inl ((p.1, true) :: t) : NativeCoordinateTable ⊕ Coordinate)) :=
    Primrec.sumInl.comp (Primrec.list_cons.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.const true)) Primrec.snd)
  have hinl : Primrec₂ (fun (p : Coordinate × (NativeCoordinateTable ⊕ Coordinate))
      (t : NativeCoordinateTable) ↦
        [Sum.inl ((p.1, false) :: t), Sum.inl ((p.1, true) :: t), Sum.inr p.1]) :=
    Primrec.list_cons.comp hfalse (Primrec.list_cons.comp htrue
      (Primrec.list_cons.comp (Primrec.sumInr.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.const [])))
  have hinr : Primrec₂ (fun (_ : Coordinate × (NativeCoordinateTable ⊕ Coordinate))
      (q : Coordinate) ↦ ([Sum.inr q] : List (NativeCoordinateTable ⊕ Coordinate))) :=
    Primrec.list_cons.comp (Primrec.sumInr.comp Primrec.snd) (Primrec.const [])
  exact Primrec.of_eq (Primrec.sumCasesOn Primrec.snd hinl hinr)
    (by rintro ⟨c, t | q⟩ <;> rfl)

/-- The pending tables after all levels are computable in the coordinate list. -/
private lemma primrec_tableLevels : Primrec tableLevels := by
  have hflat : Primrec (fun p : List (NativeCoordinateTable ⊕ Coordinate) × Coordinate ↦
      p.1.flatMap (tableLevelItem p.2)) :=
    Primrec.list_flatMap Primrec.fst
      (primrec₂_tableLevelItem.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_foldl Primrec.id (Primrec.const [Sum.inl []]) (hflat.comp Primrec.snd).to₂

/-- Computable coordinate lists and table outputs give computable complete tree codes. -/
private lemma computable_nativeTableTree_encode {σ : Type*} [Primcodable σ]
    (out : σ → NativeCoordinateTable → ℕ) (coords : σ → List Coordinate)
    (hout : Computable₂ out) (hcoords : Computable coords) :
    Computable (fun s ↦ (nativeTableTree (out s) (coords s) []).encode) := by
  have heq : ∀ s, (nativeTableTree (out s) (coords s) []).encode =
      (tableLevels (coords s)).map (tableFinalItem (out s)) := by
    intro s
    have h := map_foldl_tableLevelItem (out s) (coords s) [Sum.inl []]
    simpa [tableLevels, tableExpandItem] using h.symm
  have hfinal : Computable₂ (fun (s : σ) (it : NativeCoordinateTable ⊕ Coordinate) ↦
      tableFinalItem (out s) it) := by
    have hinl : Computable₂ (fun (p : σ × (NativeCoordinateTable ⊕ Coordinate))
        (t : NativeCoordinateTable) ↦ (Sum.inl (out p.1 t) : ℕ ⊕ Coordinate)) :=
      Computable.sumInl.comp (hout.comp (Computable.fst.comp Computable.fst) Computable.snd)
    have hinr : Computable₂ (fun (_ : σ × (NativeCoordinateTable ⊕ Coordinate))
        (q : Coordinate) ↦ (Sum.inr q : ℕ ⊕ Coordinate)) :=
      Computable.sumInr.comp Computable.snd
    exact Computable.of_eq (Computable.sumCasesOn Computable.snd hinl hinr)
      (by rintro ⟨s, t | q⟩ <;> rfl)
  exact Computable.of_eq
    (Computable.list_map (primrec_tableLevels.to_comp.comp hcoords) hfinal)
    (fun s ↦ (heq s).symm)

/-- The encoded referee tree is computable uniformly in the tuple code, the padding and the
size parameter. -/
private lemma computable_native_counting_referee_encode (cV : ℕ) :
    Computable (fun input : NativeTupleCode × ℕ × ℕ ↦
      (native_counting_referee cV (decodeNativeTuple input.1) input.2.1 input.2.2).encode) := by
  have hout : Computable₂ (fun (s : NativeTupleCode × ℕ × ℕ) (t : NativeCoordinateTable) ↦
      nativeRefereeLeaf (decodeNativeTuple s.1) (s.2.1 + cV) s.2.2 t) := by
    have htuple : Computable
        (fun p : (NativeTupleCode × ℕ × ℕ) × NativeCoordinateTable ↦ p.1.1) :=
      Computable.fst.comp Computable.fst
    have hcU : Computable
        (fun p : (NativeTupleCode × ℕ × ℕ) × NativeCoordinateTable ↦ p.1.2.1 + cV) :=
      Primrec.nat_add.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.const cV)
    have hm : Computable
        (fun p : (NativeTupleCode × ℕ × ℕ) × NativeCoordinateTable ↦ p.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    exact computable_nativeRefereeLeaf htuple hcU hm Computable.snd
  have hcU : Computable (fun s : NativeTupleCode × ℕ × ℕ ↦ s.2.1 + cV) :=
    Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const cV)
  have hflag : Computable (fun s : NativeTupleCode × ℕ × ℕ ↦ s.1.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have he₀ : Computable (fun s : NativeTupleCode × ℕ × ℕ ↦ s.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have he : Computable (fun s : NativeTupleCode × ℕ × ℕ ↦ s.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hm : Computable (fun s : NativeTupleCode × ℕ × ℕ ↦ s.2.2) :=
    Computable.snd.comp Computable.snd
  have hbound := computable_clock_literal _ _ _ he he₀ hm
  have hcoords := native_oracle_adapters_computable.2.comp (hcU.pair (hflag.pair hbound))
  exact computable_nativeTableTree_encode
    (fun (s : NativeTupleCode × ℕ × ℕ) t ↦
      nativeRefereeLeaf (decodeNativeTuple s.1) (s.2.1 + cV) s.2.2 t)
    (fun s ↦ nativeCoordinateList (s.2.1 + cV) s.1.2.2.2
      (clock s.1.2.1 (nativeLiteralFactor s.1.2.2.1 * (s.2.2 + 1))))
    hout hcoords

/-- Every query of the referee tree is one of the inspected coordinates. -/
private lemma mem_nativeCoordinateList_of_mem_queries (cV : ℕ) (θ : NativeTuple) (d m : ℕ)
    (q : Coordinate) (hq : q ∈ (native_counting_referee cV θ d m).queries) :
    q ∈ nativeCoordinateList (d + cV) θ.2.2.2 (nativeTupleBound θ m) := by
  unfold native_counting_referee at hq
  generalize nativeCoordinateList (d + cV) θ.2.2.2 (nativeTupleBound θ m) = cs at hq ⊢
  generalize nativeRefereeLeaf θ (d + cV) m = output at hq
  generalize (List.nil : NativeCoordinateTable) = table at hq
  induction cs generalizing table with
  | nil => simp [nativeTableTree, QueryTree.queries] at hq
  | cons c cs ih =>
    simp only [nativeTableTree, QueryTree.queries, List.mem_cons, List.mem_append] at hq ⊢
    rcases hq with rfl | hq | hq
    · exact Or.inl rfl
    · exact Or.inr (ih _ hq)
    · exact Or.inr (ih _ hq)

/-- A coordinate inspected for a raw word is no longer than that word. -/
private lemma length_le_of_nativeInspectedCoordinate {cU : ℕ} {flag : NativeOracleFlag}
    {z : BitString} {q : Coordinate} (h : nativeInspectedCoordinate cU flag z = some q) :
    q.1.length ≤ z.length := by
  cases hr : nativeRawCoordinate flag z with
  | none => simp [nativeInspectedCoordinate, hr] at h
  | some q' =>
    simp only [nativeInspectedCoordinate, hr] at h
    change (if q'.2 < q'.1.length + cU then some q' else none) = some q at h
    split_ifs at h
    obtain rfl := Option.some.inj h
    cases flag with
    | cumulative =>
      have hlen := target_length_le_encF q'.1 q'.2
      rw [(decodeQuery_eq_some_iff z q').mp hr] at hlen
      exact hlen
    | random =>
      simp only [nativeRawCoordinate] at hr
      split_ifs at hr
      rw [← Option.some.inj hr]

/-- Every coordinate in the inspected list is bounded in length by the tuple's polynomial. -/
private lemma length_le_nativeTupleBound_of_mem_nativeCoordinateList (θ : NativeTuple)
    (cU m : ℕ) (q : Coordinate) (hq : q ∈ nativeCoordinateList cU θ.2.2.2 (nativeTupleBound θ m)) :
    q.1.length ≤ nativeTupleBound θ m := by
  obtain ⟨z, hz, hzq⟩ := ((native_coordinate_list_spec cU _ θ.2.2.2).2.1 q).mp hq
  exact (length_le_of_nativeInspectedCoordinate hzq).trans hz

/-- The queries of the referee tree, and its coordinates retained by the downward closure at
thresholds `r ≥ m + 1`, are bounded by the tuple's polynomial and by the padding. -/
private lemma coordinate_bounds_of_mem_finite_referee_coordinates (cV : ℕ) (θ : NativeTuple)
    (d m : ℕ) (q : Coordinate)
    (hq : q ∈ finite_referee_coordinates (d + cV) m (native_counting_referee cV θ d m)) :
    q.1.length ≤ nativeTupleBound θ m ∧ m + 1 ≤ q.2 ∧
      q.2 ≤ nativeTupleBound θ m + (d + cV) := by
  obtain ⟨x, r⟩ := q
  obtain ⟨k, hk_tree, hk_bound, h_mr, hr_k⟩ :=
    (mem_finite_referee_coordinates (d + cV) m (native_counting_referee cV θ d m) x r).mp hq
  have hk_len : x.length ≤ nativeTupleBound θ m :=
    length_le_nativeTupleBound_of_mem_nativeCoordinateList θ (d + cV) m (x, k)
      (mem_nativeCoordinateList_of_mem_queries cV θ d m _ hk_tree)
  exact ⟨hk_len, h_mr, by omega⟩

/-- Uniformly effective finite trees and leaves, with bounds on full and retained coordinates.
Blueprint node `native:referee-interface`. Computability uses finite transition-table inputs;
the bounds cover every branch and every downward-retained threshold. -/
theorem native_referee_effective_interface (cV : ℕ) :
    Computable (fun input : NativeTupleCode × ℕ × ℕ =>
      (native_counting_referee cV (decodeNativeTuple input.1) input.2.1 input.2.2).encode) ∧
    Computable (fun input : NativeTupleCode × ℕ × ℕ × NativeCoordinateTable =>
      nativeRefereeLeaf (decodeNativeTuple input.1) (input.2.1 + cV)
        input.2.2.1 input.2.2.2) ∧
    ∀ θ d m,
      (∀ q ∈ (native_counting_referee cV θ d m).queries,
        q.1.length ≤ nativeTupleBound θ m) ∧
      ∀ q ∈ finite_referee_coordinates (d + cV) m (native_counting_referee cV θ d m),
        q.1.length ≤ nativeTupleBound θ m ∧ m + 1 ≤ q.2 ∧
          q.2 ≤ nativeTupleBound θ m + (d + cV) := by
  have hcU : Computable
      (fun input : NativeTupleCode × ℕ × ℕ × NativeCoordinateTable ↦ input.2.1 + cV) :=
    Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const cV)
  have hm : Computable
      (fun input : NativeTupleCode × ℕ × ℕ × NativeCoordinateTable ↦ input.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have htable : Computable
      (fun input : NativeTupleCode × ℕ × ℕ × NativeCoordinateTable ↦ input.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  refine ⟨computable_native_counting_referee_encode cV,
    computable_nativeRefereeLeaf Computable.fst hcU hm htable,
    fun θ d m ↦ ⟨fun q hq ↦
      length_le_nativeTupleBound_of_mem_nativeCoordinateList θ (d + cV) m q
        (mem_nativeCoordinateList_of_mem_queries cV θ d m q hq),
      coordinate_bounds_of_mem_finite_referee_coordinates cV θ d m⟩⟩

end Kolmogorov.Milovanov
