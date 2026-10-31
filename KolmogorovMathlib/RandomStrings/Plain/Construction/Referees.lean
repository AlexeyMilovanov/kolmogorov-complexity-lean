/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Conditional
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice

/-!
# Finite referees, admissible levels, and retained coordinates

Referees are finite binary trees (`QueryTree`) of oracle queries with natural leaves. Their
explicit postfix codes use only existing primitive encodings; computability assertions concern
these codes. The abstract `RefereeFamily` exposes no OTM implementation or directive-machine
behavior, and its polynomial bound measures target lengths, not tree size or construction time.

The module defines the preprocessing of a referee against the cumulative complexity oracle
(blueprint node `constr:tree`): queries at high thresholds are answered positively
(`QueryTree.normalize`, `refereeOutput`), and `referee_preprocessing_correct` shows that this
preserves the output on the actual oracle. It proves `referee_preprocessing_computable`, that
normalized trees and their finite retained coordinate sets (`finite_referee_coordinates`) are
computable from codes. It also defines the level parameters `levelScale`, `levelInput`, and
`levelRangeBound`, the admissibility predicate `admissible_clocked_occurrence`
(`constr:admissible`), shows that every referee has arbitrarily late admissible occurrences
(`constr:late`), and proves that every retained coordinate lies in the Key Lemma's range
(`constr:range`). The construction and the price computation of the later modules consume
these coordinates through `coordinatePriceTable` and `coordinateBaseCounters`.
-/

namespace Kolmogorov.Milovanov

/-- A cumulative-oracle coordinate: a target string and a natural complexity threshold. -/
abbrev Coordinate := BitString × ℕ

/-- A finite binary oracle-query tree with natural-valued leaves. -/
inductive QueryTree where
  /-- Termination with the indicated natural output. -/
  | leaf (out : ℕ)
  /-- Inspect a coordinate and follow the negative or positive branch. -/
  | node (query : Coordinate) (no yes : QueryTree)
  deriving DecidableEq, Repr

/-- Evaluate a referee against any total Boolean coordinate oracle. -/
def QueryTree.eval (answer : Coordinate → Bool) : QueryTree → ℕ
  | .leaf out => out
  | .node query no yes => if answer query then yes.eval answer else no.eval answer

/-- Every query in the entire tree, including branches not taken in a particular run. -/
def QueryTree.queries : QueryTree → List Coordinate
  | .leaf _ => []
  | .node query no yes => query :: (no.queries ++ yes.queries)

/-- Agreement on the entire finite tree implies agreement of the referee outputs. -/
theorem QueryTree.eval_eq_of_agree (tree : QueryTree) (a b : Coordinate → Bool)
    (h : ∀ query ∈ tree.queries, a query = b query) : tree.eval a = tree.eval b := by
  induction tree with
  | leaf out => rfl
  | node query no yes ihno ihyes =>
    have hq := h query (by simp [QueryTree.queries])
    simp only [QueryTree.eval, hq]
    split
    · apply ihyes
      intro q hmem
      exact h q (by simp [QueryTree.queries, hmem])
    · apply ihno
      intro q hmem
      exact h q (by simp [QueryTree.queries, hmem])

/-- A postfix tree code; leaves carry naturals and binary nodes carry coordinates. -/
abbrev QueryTree.Code := List (ℕ ⊕ Coordinate)

/-- Serialize both children before their binary node, preserving negative/positive order. -/
def QueryTree.encode : QueryTree → QueryTree.Code
  | .leaf out => [.inl out]
  | .node query no yes => no.encode ++ yes.encode ++ [.inr query]

/-- One stack-machine instruction for decoding a postfix referee code. -/
private def QueryTree.decodeStep (stack : List QueryTree) : ℕ ⊕ Coordinate → List QueryTree
  | .inl out => .leaf out :: stack
  | .inr query =>
    match stack with
    | yes :: no :: rest => .node query no yes :: rest
    | _ => []

/-- Decode a canonical tree code, rejecting malformed instruction sequences. -/
def QueryTree.decode (code : QueryTree.Code) : Option QueryTree :=
  match code.foldl QueryTree.decodeStep [] with
  | [tree] => if tree.encode = code then some tree else none
  | _ => none

/-- Executing a tree's code pushes that tree onto any existing decoding stack. -/
private theorem QueryTree.fold_encode (tree : QueryTree) (stack : List QueryTree) :
    tree.encode.foldl QueryTree.decodeStep stack = tree :: stack := by
  induction tree generalizing stack with
  | leaf out => rfl
  | node query no yes ihno ihyes =>
    simp [QueryTree.encode, List.foldl_append, ihno, ihyes, QueryTree.decodeStep]

/-- Every finite referee is recovered from its explicit code. -/
theorem QueryTree.decode_encode (tree : QueryTree) :
    QueryTree.decode tree.encode = some tree := by
  simp [QueryTree.decode, QueryTree.fold_encode]

/-- Replace universally true literal queries by their positive branches.
Blueprint node `constr:tree`. This also removes queries inside the discarded branches. -/
def QueryTree.normalize (cU : ℕ) : QueryTree → QueryTree
  | .leaf out => .leaf out
  | .node query no yes =>
    if query.1.length + cU ≤ query.2 then yes.normalize cU
    else .node query (no.normalize cU) (yes.normalize cU)

/-- Answer high thresholds positively, even if the finite stage table has no witness.
Blueprint node `constr:tree`. Raw malformed words are handled by the later native adapters. -/
def normalizedAnswer (cU : ℕ) (answer : Coordinate → Bool) (query : Coordinate) : Bool :=
  decide (query.1.length + cU ≤ query.2) || answer query

/-- Normalized referee evaluation on an arbitrary Boolean coordinate oracle.
Blueprint node `constr:tree`. -/
def refereeOutput (cU : ℕ) (tree : QueryTree) (answer : Coordinate → Bool) : ℕ :=
  tree.eval (normalizedAnswer cU answer)

/-- Tree preprocessing implements exactly the fixed high-threshold answer rule.
Blueprint node `constr:tree`. -/
theorem QueryTree.eval_normalize (cU : ℕ) (tree : QueryTree) (answer : Coordinate → Bool) :
    (tree.normalize cU).eval answer = refereeOutput cU tree answer := by
  induction tree with
  | leaf out => rfl
  | node query no yes ihno ihyes =>
    by_cases h : query.1.length + cU ≤ query.2
    · simpa [QueryTree.normalize, refereeOutput, QueryTree.eval, normalizedAnswer, h] using ihyes
    · simp only [refereeOutput] at ihno ihyes
      simp [QueryTree.normalize, refereeOutput, QueryTree.eval, normalizedAnswer, h, ihno, ihyes]

/-- Set-valued oracles have a semantic Boolean characteristic function. -/
noncomputable def coordinateOracleAnswer (A : Set Coordinate) (query : Coordinate) : Bool :=
  @decide (query ∈ A) (Classical.propDecidable _)

/-- The actual cumulative coordinate oracle, using the frozen empty-condition complexity. -/
def actualCoordinateOracle (U : Map) : Set Coordinate := {query | Simple U query.1 query.2}

/-- Normalized output on a coordinate set; only this semantic adapter is noncomputable.
Blueprint node `constr:tree`. -/
noncomputable def refereeSetOutput (cU : ℕ) (tree : QueryTree) (A : Set Coordinate) : ℕ :=
  refereeOutput cU tree (coordinateOracleAnswer A)

/-- Output on the actual cumulative oracle for an arbitrary directive branch.
Blueprint node `constr:tree`. Computability of that branch is unnecessary here. -/
noncomputable def refereeActualOutput (B : Base) (literal : PlainLiteral B) (d : ℕ)
    (G : BitString →. BitString) (tree : QueryTree) : ℕ :=
  refereeSetOutput (constructedLiteralConstant literal d) tree
    (actualCoordinateOracle (constructed_conditional_machine B d G))

/-- Preprocessing preserves the actual referee output, and is an explicit tree operation.
Blueprint node `constr:tree`. -/
theorem referee_preprocessing_correct (B : Base) (literal : PlainLiteral B) (d : ℕ)
    (hd : 1 ≤ d) (G : BitString →. BitString) (tree : QueryTree) :
    refereeActualOutput B literal d G tree =
      tree.eval (coordinateOracleAnswer
        (actualCoordinateOracle (constructed_conditional_machine B d G))) ∧
    ∀ answer, (tree.normalize (constructedLiteralConstant literal d)).eval answer =
      refereeOutput (constructedLiteralConstant literal d) tree answer := by
  refine ⟨?_, fun answer => tree.eval_normalize _ answer⟩
  apply QueryTree.eval_eq_of_agree
  intro query _
  by_cases h : query.1.length + constructedLiteralConstant literal d ≤ query.2
  · have hx : Simple (constructed_conditional_machine B d G) query.1 query.2 :=
      (constructed_machine_literal_bound B literal d hd G query.1).trans
        (by exact_mod_cast h)
    simp [normalizedAnswer, h, coordinateOracleAnswer, actualCoordinateOracle, hx]
  · simp [normalizedAnswer, h]

/-- The explicit polynomial majorant needed for late admissible occurrences. -/
def PolynomialQueryBound (p : ℕ → ℕ) : Prop :=
  ∃ a e : ℕ, ∀ m : ℕ, p m ≤ a * (m + 1) ^ e + e

/-- The abstract effective family later instantiated by the native finite-table referees.
Blueprint node `constr:admissible`. Indices start at one; index zero is unused.
The bound is independent of padding, while the tree may use `d + cV` for normalization. -/
structure RefereeFamily where
  /-- The tree at padding, occurrence index, and input parameter. -/
  tree : ℕ → ℕ → ℕ → QueryTree
  /-- Target-length bounds at an occurrence and input, independent of padding. -/
  bound : ℕ → ℕ → ℕ
  /-- Uniform computability of the entire tree, including every leaf output. -/
  tree_computable : Computable (fun input : ℕ × ℕ × ℕ =>
    (tree input.1 input.2.1 input.2.2).encode)
  /-- Effective bounds make admissibility a finite test in the construction. -/
  bound_computable : Computable (fun input : ℕ × ℕ => bound input.1 input.2)
  /-- Every queried target on every branch respects the same polynomial bound. -/
  query_bound : ∀ d l m, 1 ≤ l → ∀ query ∈ (tree d l m).queries,
    query.1.length ≤ bound l m
  /-- One fixed polynomial majorizes each occurrence's query-bound function. -/
  polynomial : ∀ l, 1 ≤ l → PolynomialQueryBound (bound l)
  /-- The same tree function and the same bound recur at unbounded positive indices. -/
  repeats : ∀ d l, 1 ≤ l → ∀ index, ∃ later, index < later ∧ 1 ≤ later ∧
    tree d later = tree d l ∧ bound later = bound l

/-- The lower endpoint `a_(2l-1)` of the level's ownership interval. -/
def levelLower (l : ℕ) : ℕ := tower (2 * l - 1)

/-- The marker scale `n_l = a_(2l)`. -/
def levelScale (l : ℕ) : ℕ := tower (2 * l)

/-- The upper endpoint `N_l = a_(2l+1)`. -/
def levelUpper (l : ℕ) : ℕ := tower (2 * l + 1)

/-- The input and small-description budget `m_l = n_l + d`. -/
def levelInput (d l : ℕ) : ℕ := levelScale l + d

/-- The Key Lemma's strict target bound `b_l = n_l ^ log₂ n_l`. -/
def levelRangeBound (l : ℕ) : ℕ := towerRangeBound (levelScale l)

/-- The upper endpoint is exactly the exponential extension scale. -/
theorem level_upper_eq (l : ℕ) : levelUpper l = 2 ^ levelScale l := rfl

/-- Positive levels satisfying the fixed threshold and polynomial query separation.
Blueprint node `constr:admissible`. `n₀` and `cV` are inputs chosen before `d`. -/
def admissible_clocked_occurrence (family : RefereeFamily) (cV n₀ d l : ℕ) : Prop :=
  1 ≤ l ∧ max (max 32 (d ^ 2)) n₀ ≤ levelScale l ∧
    family.bound l (levelInput d l) + (d + cV) < levelRangeBound l

/-- Admissibility is decidable from the supplied bound and numerical parameters. -/
instance (family : RefereeFamily) (cV n₀ d l : ℕ) :
    Decidable (admissible_clocked_occurrence family cV n₀ d l) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A polynomial in `N` with fixed shift and constants is eventually below `N ^ log₂ N`. -/
private lemma exists_polynomial_lt_pow_log2 (a e d cV : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, a * (N + d + 1) ^ e + e + d + cV < N ^ Nat.log2 N := by
  refine ⟨max (2 ^ (e + 1)) (a * 2 ^ e + e + d + cV + 1), fun N hN ↦ ?_⟩
  have h1 : 2 ^ (e + 1) ≤ N := (le_max_left _ _).trans hN
  have h3 : a * 2 ^ e + e + d + cV + 1 ≤ N := (le_max_right _ _).trans hN
  have hN_pos : 0 < N := by omega
  have he_le_log : e + 1 ≤ Nat.log2 N := (Nat.le_log2 hN_pos.ne').mpr h1
  have hpow_log : N ^ (e + 1) ≤ N ^ Nat.log2 N := Nat.pow_le_pow_right hN_pos he_le_log
  have hNd : N + d + 1 ≤ 2 * N := by omega
  have hNe : 0 < N ^ e := Nat.pow_pos hN_pos
  have hmul : a * (N + d + 1) ^ e ≤ a * 2 ^ e * N ^ e :=
    calc a * (N + d + 1) ^ e ≤ a * (2 * N) ^ e :=
          Nat.mul_le_mul_left a (Nat.pow_le_pow_left hNd e)
      _ = a * 2 ^ e * N ^ e := by rw [Nat.mul_pow, Nat.mul_assoc]
  have hconst : e + d + cV ≤ (e + d + cV) * N ^ e := Nat.le_mul_of_pos_right _ hNe
  calc a * (N + d + 1) ^ e + e + d + cV
      = a * (N + d + 1) ^ e + (e + d + cV) := by omega
    _ ≤ a * 2 ^ e * N ^ e + (e + d + cV) * N ^ e := Nat.add_le_add hmul hconst
    _ = (a * 2 ^ e + e + d + cV) * N ^ e := by rw [← Nat.add_mul]; congr 1; omega
    _ < N * N ^ e := Nat.mul_lt_mul_of_pos_right (by omega) hNe
    _ = N ^ (e + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    _ ≤ N ^ Nat.log2 N := hpow_log

/-- Every fixed polynomial is eventually dominated on the fixed tower sequence.
Blueprint node `constr:late`. The threshold may depend on `p`, `d`, and `cV`. -/
theorem polynomial_below_tower_range (p : ℕ → ℕ) (hp : PolynomialQueryBound p)
    (d cV : ℕ) : ∃ index₀ : ℕ, ∀ i ≥ index₀,
      p (tower i + d) + d + cV < towerRangeBound (tower i) := by
  obtain ⟨a, e, hp_bound⟩ := hp
  obtain ⟨N₀, hN₀⟩ := exists_polynomial_lt_pow_log2 a e d cV
  refine ⟨N₀, fun i hi ↦ ?_⟩
  have hlt := hN₀ (tower i) (hi.trans (le_tower i))
  have hpi := hp_bound (tower i + d)
  unfold towerRangeBound
  exact lt_of_le_of_lt (by omega) hlt

/-- A fixed referee-and-bound pair has admissible occurrences beyond every index.
Blueprint node `constr:late`. The original pair is fixed before padding is quantified. -/
theorem clocked_machine_has_late_admissible_occurrence (family : RefereeFamily)
    (cV n₀ l : ℕ) (hn₀ : 32 ≤ n₀) (hl : 1 ≤ l) : ∀ d : ℕ, 1 ≤ d → ∀ index : ℕ,
    ∃ later : ℕ, index < later ∧
      family.tree d later = family.tree d l ∧ family.bound later = family.bound l ∧
      admissible_clocked_occurrence family cV n₀ d later := by
  intro d _ index
  obtain ⟨index₀, h_poly⟩ :=
    polynomial_below_tower_range (family.bound l) (family.polynomial l hl) d cV
  obtain ⟨later, h_gt, h1, htree, hbound⟩ :=
    family.repeats d l hl (max index (max index₀ (max (d ^ 2) n₀)))
  have hindex : index < later := lt_of_le_of_lt (le_max_left _ _) h_gt
  have hindex₀ : index₀ < later :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) h_gt
  have hd2 : d ^ 2 < later :=
    lt_of_le_of_lt ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) h_gt
  have hn : n₀ < later :=
    lt_of_le_of_lt ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) h_gt
  refine ⟨later, hindex, htree, hbound, h1, ?_, ?_⟩
  · exact (max_le (max_le (by omega) hd2.le) hn.le).trans
      ((by omega : later ≤ 2 * later).trans (le_tower _))
  · unfold levelInput levelRangeBound levelScale
    rw [hbound]
    have := h_poly (2 * later) (by omega)
    omega

/-- A duplicate-free finite list of every retained coordinate, in deterministic order.
Blueprint node `constr:tree`. Downward closure stops at `m + 1`. -/
def retainedCoordinateList (cU m : ℕ) (tree : QueryTree) : List Coordinate :=
  (tree.queries.flatMap (fun query =>
    if query.2 < query.1.length + cU then
      ((List.range (query.2 + 1)).filter (fun r => decide (m + 1 ≤ r))).map
        (fun r => (query.1, r))
    else [])).eraseDups

/-- The finite coordinate set of the full referee tree.
Blueprint node `constr:tree`. Queries at thresholds at most `m` create no coordinates. -/
def finite_referee_coordinates (cU m : ℕ) (tree : QueryTree) : Finset Coordinate :=
  (retainedCoordinateList cU m tree).toFinset

/-- Membership records the original nontrivial query and the retained threshold interval.
Blueprint node `constr:tree`. -/
theorem mem_finite_referee_coordinates (cU m : ℕ) (tree : QueryTree) (x : BitString)
    (r : ℕ) : (x, r) ∈ finite_referee_coordinates cU m tree ↔
      ∃ k : ℕ, (x, k) ∈ tree.queries ∧ k < x.length + cU ∧ m + 1 ≤ r ∧ r ≤ k := by
  simp only [finite_referee_coordinates, List.mem_toFinset, retainedCoordinateList,
    List.mem_eraseDups, List.mem_flatMap]
  constructor
  · rintro ⟨⟨y, k⟩, hq, hr⟩
    split_ifs at hr with hnontrivial
    · simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
        Prod.mk.injEq] at hr
      obtain ⟨s, ⟨hsk, hms⟩, hy, hsr⟩ := hr
      subst y s
      exact ⟨k, hq, hnontrivial, hms, by omega⟩
    · simp at hr
  · rintro ⟨k, hq, hnontrivial, hmr, hrk⟩
    refine ⟨(x, k), hq, ?_⟩
    simp only [hnontrivial, ite_true, List.mem_map]
    refine ⟨r, ?_, rfl⟩
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, hmr⟩

/-- Stack entry of the code-level referee decoder: a decoded tree's code, the code of its
normalization, and its query list. -/
private abbrev RefereeStackEntry :=
  QueryTree.Code × QueryTree.Code × List Coordinate

/-- The stack entry of a decoded tree. -/
private def stackEntry (cU : ℕ) (t : QueryTree) :
    RefereeStackEntry :=
  (t.encode, (t.normalize cU).encode, t.queries)

/-- The stack entry of a binary node, built from the entries of its two children. -/
private def nodeEntry (cU : ℕ) (query : Coordinate)
    (no yes : RefereeStackEntry) :
    RefereeStackEntry :=
  (no.1 ++ yes.1 ++ [.inr query],
    if query.1.length + cU ≤ query.2 then yes.2.1 else no.2.1 ++ yes.2.1 ++ [.inr query],
    query :: (no.2.2 ++ yes.2.2))

/-- `QueryTree.decodeStep`, run directly on the entries. -/
private def codeStep (cU : ℕ)
    (stack : List RefereeStackEntry) :
    ℕ ⊕ Coordinate → List RefereeStackEntry
  | .inl out => ([.inl out], [.inl out], []) :: stack
  | .inr query =>
    if 2 ≤ stack.length then
      nodeEntry cU query
        (stack.getD 1 default) (stack.getD 0 default) :: stack.drop 2
    else []

/-- Each code-level step preserves the entries of the semantic decoder stack. -/
private theorem map_decodeStep_eq_codeStep (cU : ℕ)
    (stack : List QueryTree) (i : ℕ ⊕ Coordinate) :
    (QueryTree.decodeStep stack i).map (stackEntry cU) =
      codeStep cU
        (stack.map (stackEntry cU)) i := by
  cases i with
  | inl out =>
    simp [QueryTree.decodeStep, codeStep,
      stackEntry, QueryTree.encode, QueryTree.normalize, QueryTree.queries]
  | inr query =>
    rcases stack with _ | ⟨yes, _ | ⟨no, rest⟩⟩
    · rfl
    · rfl
    · by_cases h : query.1.length + cU ≤ query.2 <;>
        simp [QueryTree.decodeStep, codeStep,
          nodeEntry, stackEntry,
          QueryTree.encode, QueryTree.normalize, QueryTree.queries, h]

private theorem map_foldl_decodeStep (cU : ℕ)
    (code : QueryTree.Code) (stack : List QueryTree) :
    (code.foldl QueryTree.decodeStep stack).map (stackEntry cU) =
      code.foldl (codeStep cU)
        (stack.map (stackEntry cU)) := by
  induction code generalizing stack with
  | nil => rfl
  | cons i code ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, map_decodeStep_eq_codeStep]

/-- Normalized code and query list of the decoded referee (the constant-zero tree if invalid). -/
private def codeRun (cU : ℕ) (code : QueryTree.Code) :
    QueryTree.Code × List Coordinate :=
  let stack := code.foldl (codeStep cU) []
  if stack.length = 1 ∧ stack.headI.1 = code then (stack.headI.2.1, stack.headI.2.2)
  else ([.inl 0], [])

/-- The code-level machine uses exactly the canonical-code check of `QueryTree.decode`. -/
private theorem codeRun_eq (cU : ℕ) (code : QueryTree.Code) :
    codeRun cU code =
      ((((QueryTree.decode code).getD (.leaf 0)).normalize cU).encode,
      ((QueryTree.decode code).getD (.leaf 0)).queries) := by
  have h := map_foldl_decodeStep cU code []
  rw [List.map_nil] at h
  unfold codeRun QueryTree.decode
  rw [← h]
  rcases hf : code.foldl QueryTree.decodeStep [] with _ | ⟨t, _ | ⟨u, ts⟩⟩
  · simp [QueryTree.normalize, QueryTree.encode, QueryTree.queries]
  · by_cases hc : t.encode = code
    · simp [hc, stackEntry]
    · simp [hc, stackEntry,
        QueryTree.normalize, QueryTree.encode, QueryTree.queries]
  · simp [QueryTree.normalize, QueryTree.encode, QueryTree.queries]

private theorem primrec_nodeEntry :
    Primrec (fun x : ℕ × Coordinate ×
        RefereeStackEntry × RefereeStackEntry =>
      nodeEntry x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hcU : Primrec (fun x : ℕ × Coordinate ×
      RefereeStackEntry × RefereeStackEntry =>
      x.1) := Primrec.fst
  have hq : Primrec (fun x : ℕ × Coordinate ×
      RefereeStackEntry × RefereeStackEntry =>
      x.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hno : Primrec (fun x : ℕ × Coordinate ×
      RefereeStackEntry × RefereeStackEntry =>
      x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hyes : Primrec (fun x : ℕ × Coordinate ×
      RefereeStackEntry × RefereeStackEntry =>
      x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hinr : Primrec (fun x : ℕ × Coordinate ×
      RefereeStackEntry × RefereeStackEntry =>
      ([Sum.inr x.2.1] : QueryTree.Code)) :=
    Primrec.list_cons.comp (Primrec.sumInr.comp hq) (Primrec.const [])
  have hcond : PrimrecPred (fun x : ℕ × Coordinate ×
      RefereeStackEntry × RefereeStackEntry =>
      x.2.1.1.length + x.1 ≤ x.2.1.2) :=
    Primrec.nat_le.comp (Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp hq)) hcU)
      (Primrec.snd.comp hq)
  have hno1 := Primrec.fst.comp hno
  have hno2 := Primrec.fst.comp (Primrec.snd.comp hno)
  have hno3 := Primrec.snd.comp (Primrec.snd.comp hno)
  have hyes1 := Primrec.fst.comp hyes
  have hyes2 := Primrec.fst.comp (Primrec.snd.comp hyes)
  have hyes3 := Primrec.snd.comp (Primrec.snd.comp hyes)
  have h1 := Primrec.list_append.comp (Primrec.list_append.comp hno1 hyes1) hinr
  have h2 := Primrec.ite hcond hyes2
    (Primrec.list_append.comp (Primrec.list_append.comp hno2 hyes2) hinr)
  have h3 := Primrec.list_cons.comp hq (Primrec.list_append.comp hno3 hyes3)
  exact Primrec.pair h1 (Primrec.pair h2 h3)

private theorem primrec_codeStep :
    Primrec (fun q : ℕ × List RefereeStackEntry × (ℕ ⊕ Coordinate) =>
      codeStep q.1 q.2.1 q.2.2) := by
  have hcU : Primrec (fun q : ℕ × List RefereeStackEntry ×
      (ℕ ⊕ Coordinate) => q.1) := Primrec.fst
  have hstack : Primrec (fun q : ℕ × List RefereeStackEntry ×
      (ℕ ⊕ Coordinate) => q.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun q : ℕ × List RefereeStackEntry ×
      (ℕ ⊕ Coordinate) => q.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hinl : Primrec₂ (fun
      (q : ℕ × List RefereeStackEntry × (ℕ ⊕ Coordinate)) (out : ℕ) =>
      (([Sum.inl out], [Sum.inl out], []) : RefereeStackEntry) :: q.2.1) := by
    have hout : Primrec (fun p :
        (ℕ × List RefereeStackEntry × (ℕ ⊕ Coordinate)) × ℕ =>
        ([Sum.inl p.2] : QueryTree.Code)) :=
      Primrec.list_cons.comp (Primrec.sumInl.comp Primrec.snd) (Primrec.const [])
    exact Primrec.list_cons.comp (Primrec.pair hout (Primrec.pair hout (Primrec.const [])))
      (hstack.comp Primrec.fst)
  have hinr : Primrec₂ (fun
      (q : ℕ × List RefereeStackEntry × (ℕ ⊕ Coordinate))
      (query : Coordinate) =>
      if 2 ≤ q.2.1.length then
        nodeEntry q.1 query
          (q.2.1.getD 1 default) (q.2.1.getD 0 default) :: q.2.1.drop 2
      else []) := by
    have hs : Primrec (fun p :
        (ℕ × List RefereeStackEntry × (ℕ ⊕ Coordinate)) × Coordinate =>
        p.1.2.1) := hstack.comp Primrec.fst
    have hno : Primrec (fun p :
        (ℕ × List RefereeStackEntry × (ℕ ⊕ Coordinate)) × Coordinate =>
        p.1.2.1.getD 1 default) := (Primrec.list_getD default).comp hs (Primrec.const 1)
    have hyes : Primrec (fun p :
        (ℕ × List RefereeStackEntry × (ℕ ⊕ Coordinate)) × Coordinate =>
        p.1.2.1.getD 0 default) := (Primrec.list_getD default).comp hs (Primrec.const 0)
    have hnode := primrec_nodeEntry.comp
      (Primrec.pair (hcU.comp Primrec.fst) (Primrec.pair Primrec.snd (Primrec.pair hno hyes)))
    exact Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) (Primrec.list_length.comp hs))
      (Primrec.list_cons.comp hnode (Primrec.list_drop.comp (Primrec.const 2) hs))
      (Primrec.const [])
  exact (Primrec.sumCasesOn hi hinl hinr).of_eq (fun q => by
    rcases q with ⟨cU, stack, i | query⟩ <;> rfl)

private theorem primrec_codeRun :
    Primrec (fun a : ℕ × QueryTree.Code => codeRun a.1 a.2) := by
  have hfold : Primrec (fun a : ℕ × QueryTree.Code =>
      a.2.foldl (codeStep a.1) []) := by
    have hstep : Primrec₂ (fun (a : ℕ × QueryTree.Code)
        (p : List RefereeStackEntry × (ℕ ⊕ Coordinate)) =>
        codeStep a.1 p.1 p.2) :=
      primrec_codeStep.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_foldl Primrec.snd (Primrec.const []) hstep
  have hhead : Primrec (fun a : ℕ × QueryTree.Code =>
      (a.2.foldl (codeStep a.1) []).headI) :=
    Primrec.list_headI.comp hfold
  have hcond : PrimrecPred (fun a : ℕ × QueryTree.Code =>
      (a.2.foldl (codeStep a.1) []).length = 1 ∧
        (a.2.foldl (codeStep a.1) []).headI.1 = a.2) :=
    PrimrecPred.and (Primrec.eq.comp (Primrec.list_length.comp hfold) (Primrec.const 1))
      (Primrec.eq.comp (Primrec.fst.comp hhead) Primrec.snd)
  exact Primrec.ite hcond
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp hhead))
      (Primrec.snd.comp (Primrec.snd.comp hhead)))
    (Primrec.const ([Sum.inl 0], []))

private theorem primrec_retainedCoordinatesList :
    Primrec (fun p : ℕ × ℕ × List Coordinate =>
      (p.2.2.flatMap (fun query =>
        if query.2 < query.1.length + p.1 then
          ((List.range (query.2 + 1)).filter (fun r => decide (p.2.1 + 1 ≤ r))).map
            (fun r => (query.1, r))
        else [])).eraseDups) := by
  refine primrec_eraseDups.comp
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) ?_)
  have hlen : Primrec (fun x : (ℕ × ℕ × List Coordinate) × Coordinate => x.2.1.length + x.1.1) :=
    Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp Primrec.fst)
  have hcond : PrimrecPred (fun x : (ℕ × ℕ × List Coordinate) × Coordinate =>
      x.2.2 < x.2.1.length + x.1.1) :=
    Primrec.nat_lt.comp (Primrec.snd.comp Primrec.snd) hlen
  have hrange : Primrec (fun x : (ℕ × ℕ × List Coordinate) × Coordinate =>
      List.range (x.2.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
  have hfilter : Primrec (fun x : (ℕ × ℕ × List Coordinate) × Coordinate =>
      (List.range (x.2.2 + 1)).filter (fun r => decide (x.1.2.1 + 1 ≤ r))) :=
    Primrec.list_filter hrange
      ((Primrec.nat_le.comp (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst)))) Primrec.snd).decide)
  have hmap : Primrec (fun x : (ℕ × ℕ × List Coordinate) × Coordinate =>
      ((List.range (x.2.2 + 1)).filter (fun r => decide (x.1.2.1 + 1 ≤ r))).map
        (fun r => (x.2.1, r))) :=
    Primrec.list_map hfilter
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  exact Primrec.ite hcond hmap (Primrec.const [])

/-- Decoding and normalizing are computed by one code-level stack machine, which also returns
the preorder list of queries. -/
private theorem computable_decode_normalize_queries :
    Computable (fun input : ℕ × QueryTree.Code =>
      ((((QueryTree.decode input.2).getD (.leaf 0)).normalize input.1).encode,
        ((QueryTree.decode input.2).getD (.leaf 0)).queries)) := by
  have h := primrec_codeRun.to_comp
  exact h.of_eq (fun input => codeRun_eq input.1 input.2)

/-- The retained coordinates are computable from the cutoff data and the list of queries. -/
private theorem computable_retainedCoordinates :
    Computable (fun p : ℕ × ℕ × List Coordinate =>
      (p.2.2.flatMap (fun query =>
        if query.2 < query.1.length + p.1 then
          ((List.range (query.2 + 1)).filter (fun r => decide (p.2.1 + 1 ≤ r))).map
            (fun r => (query.1, r))
        else [])).eraseDups) :=
  primrec_retainedCoordinatesList.to_comp

/-- Normalized trees and coordinate lists are computable from explicit referee codes.
Blueprint node `constr:tree`. Invalid codes use the constant-zero referee. -/
theorem referee_preprocessing_computable :
    Computable (fun input : ℕ × ℕ × QueryTree.Code =>
      let tree := (QueryTree.decode input.2.2).getD (.leaf 0)
      ((tree.normalize input.1).encode, retainedCoordinateList input.1 input.2.1 tree)) := by
  have hargs : Computable (fun input : ℕ × ℕ × QueryTree.Code => (input.1, input.2.2)) :=
    Computable.fst.pair (Computable.snd.comp Computable.snd)
  have hM := computable_decode_normalize_queries.comp hargs
  have hargs2 : Computable (fun input : ℕ × ℕ × QueryTree.Code =>
      (input.1, input.2.1, ((QueryTree.decode input.2.2).getD (.leaf 0)).queries)) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp hM))
  have hR := computable_retainedCoordinates.comp hargs2
  exact (Computable.fst.comp hM).pair hR

/-- Retention is downward closed within the variable interval, not below `m + 1`.
Blueprint node `constr:tree`. -/
theorem retained_coordinates_downward_closed (cU m : ℕ) (tree : QueryTree)
    (x : BitString) (r s : ℕ) (hr : (x, r) ∈ finite_referee_coordinates cU m tree)
    (hs : m + 1 ≤ s) (hsr : s ≤ r) : (x, s) ∈ finite_referee_coordinates cU m tree := by
  obtain ⟨k, hk, hnontrivial, _, hrk⟩ :=
    (mem_finite_referee_coordinates cU m tree x r).mp hr
  exact (mem_finite_referee_coordinates cU m tree x s).mpr
    ⟨k, hk, hnontrivial, hs, hsr.trans hrk⟩

/-- Every retained coordinate satisfies all three ranges needed by the construction.
Blueprint node `constr:range`. The natural subtraction `r - d` is safe above `m + 1`. -/
theorem retained_coordinates_within_key_lemma_range (family : RefereeFamily)
    (cV n₀ d l : ℕ) (_hn₀ : 32 ≤ n₀) (_hd : 1 ≤ d)
    (ha : admissible_clocked_occurrence family cV n₀ d l)
    (x : BitString) (r : ℕ)
    (hr : (x, r) ∈ finite_referee_coordinates (d + cV) (levelInput d l)
      (family.tree d l (levelInput d l))) :
    (x.length ≤ family.bound l (levelInput d l) ∧
      family.bound l (levelInput d l) < levelRangeBound l) ∧
    (levelScale l ≤ r - d ∧ r - d < levelRangeBound l) ∧
    (r < levelRangeBound l ∧ levelRangeBound l < levelUpper l) := by
  obtain ⟨k, hk, hnontrivial, hlow, hhigh⟩ :=
    (mem_finite_referee_coordinates _ _ _ x r).mp hr
  have hlen := family.query_bound d l (levelInput d l) ha.1 (x, k) hk
  change x.length ≤ family.bound l (levelInput d l) at hlen
  have hsep : levelRangeBound l < levelUpper l :=
    tower_range_separation (levelScale l) (by have := ha.2.1; omega) ⟨2 * l, rfl⟩
  have hadm := ha.2.2
  dsimp [levelInput] at hlow
  exact ⟨⟨hlen, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, hsep⟩⟩

/-- Compute all coordinate prices with the frozen algorithm and explicit constants.
The list order is the game's coordinate order; malformed candidates keep the stage-2 defaults. -/
def coordinatePriceTable (B : Base) (lam n₀ n d : ℕ) (candidate : Candidate)
    (coordinates : List Coordinate) : List ℕ :=
  coordinates.eraseDups.map (fun query =>
    compute_extension_price B lam n₀ n candidate query.1 (query.2 - d))

/-- The base-machine contributions to initial counters, using the frozen past extension count.
Later phase initialization also includes backed directive outputs; this is only the `V` part. -/
def coordinateBaseCounters (B : Base) (n d : ℕ) (candidate : Candidate)
    (coordinates : List Coordinate) : List ℕ :=
  coordinates.eraseDups.map (fun query =>
    pastExtensionCount B n candidate n (triple query.1 (query.2 - d) candidate.1))

end Kolmogorov.Milovanov
