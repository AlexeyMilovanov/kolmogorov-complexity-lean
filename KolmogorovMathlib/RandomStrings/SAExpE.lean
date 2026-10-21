/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.SAExp
import KolmogorovMathlib.RandomStrings.Clocks
import KolmogorovMathlib.RandomStrings.Instances

/-!
# `EXP^R_{sa,poly} ⊆ EXP` modulo the evaluator (the exponential-time strictly sub-adaptive case)

The exponential-time analogue of `AFG/SAExp.lean`: oracle machines running in time `2 ^ p(|x|)`
that are *strictly* sub-adaptive within that time bound and whose queries have *polynomial* length
`≤ q(|x|)` (`ExpTimeStrictSAPoly`).  As a clocked coded machine `(c, e)` with the exponential clock
`clkE e n = 2 ^ (n ^ e + e)` (`AFG/Clocks.lean`) such a machine satisfies `StrictSAPolyOn c e x`:
strict sub-adaptivity within `clkE e |x|` steps, and every possible query within `clkE e |x|`
steps has length at most `clock e |x| = |x| ^ e + e` (the clock polynomial of the same index is a
convenient common bound: `exists_clockedE_strictSAPoly` picks `e` with `p + q ≤ clock e`).

* `StrictSAPolyOn`, `ExpTimeStrictSAPoly`, `exists_clockedE_strictSAPoly`;
* `StrictSAPolyDecider`: the specification of a decision procedure for `StrictSAPolyOn` on
  machine codes, `Family.strictSAEOf D` the family (clock `clkE`) given one;
* `strictlySAB`/`strictlySAB_iff`: the `T`-parametrised history test (copy of
  `strictlySubAdaptiveB` with `queryListCodeT m T x` and `T` in place of `queryListCode m e x` and
  `clock e |x|`), `queryLenB`: the length test, `strictSAPolyB` (primitive recursive): the
  decider, `Family.strictSAE := Family.strictSAEOf strictSAPolyDecider`;
* `exists_pathData_of_stagesT`, `exists_pathData_of_strictT`: the address structure of the game
  for an arbitrary time bound `T` (copies of the `clock` versions in `AFG/PathDataSA.lean`);
* `valKRaw_gameOfT_of_strictSAPoly`: the key recursion computes the value of the game at
  `T = clkE e |x|`, with the precision `gameN` (valid because the queries have length
  `≤ clock e |x|`) and the fuel `2 ^ (clock e |x| + 1)` (all queries lie in
  `strsUpTo (clock e |x|)`);
* `valKLangE`: the language of that recursion (the target of the evaluator);
* `dec_inter_expTimeStrictSAPoly_RA_subset_EXP_of_eval`: the final theorem, given the evaluator
  (`valKLangE ∈ EXP`); `…_of_decider`: the same for any decider.
-/

namespace Kolmogorov.RandomStrings

/-! ### The class and its clocked form -/

/-- The clocked coded machine `(c, e)` with the exponential clock is strictly sub-adaptive on `x`
within `clkE e |x|` steps, and its possible queries within that time have length at most
`clock e |x|` (polynomial query length; the clock polynomial `n ^ e + e` of the same index is
used as the bound). -/
def StrictSAPolyOn (c : OTMCode) (e : ℕ) (x : BitString) : Prop :=
  StrictlySA c.toOTM x (clkE e x.length) ∧
    ∀ z ∈ querySet c.toOTM x (clkE e x.length), z.length ≤ clock e x.length

/-- `EXP^B_{ssa,poly}`: the sets decided with the oracle `B` by an oracle machine which, for a
polynomial `p`, halts within `2 ^ p(|x|)` steps under every oracle, is strictly sub-adaptive on
every input within that time bound, and, for a polynomial `q`, only asks strings of length at most
`q(|x|)`. -/
def ExpTimeStrictSAPoly (B : Set BitString) : Set (Set BitString) :=
  {A | ∃ (M : OTM) (p q : Polynomial ℕ),
    (∀ (B' : Set BitString) (x : BitString), ∃ t ≤ 2 ^ p.eval x.length, Halted M (run M B' x t)) ∧
    (∀ x : BitString, StrictlySA M x (2 ^ p.eval x.length)) ∧
    (∀ (B' : Set BitString) (x z : BitString) (t : ℕ), askedAt M (run M B' x t) = some z →
      z.length ≤ q.eval x.length) ∧
    ∀ x : BitString, x ∈ A ↔ Accepts M B x}

/-- Any set in `EXP^B_{ssa,poly}` is decided by a `clkE`-clocked coded machine with oracle `B`
which satisfies `StrictSAPolyOn` on every input. -/
theorem exists_clockedE_strictSAPoly (B A : Set BitString) (h : A ∈ ExpTimeStrictSAPoly B) :
    ∃ (c : OTMCode) (e : ℕ), (∀ x, StrictSAPolyOn c e x) ∧ ClockedDecidesW clkE c e B A := by
  obtain ⟨M, p, q, hp, hsa, hq, hA⟩ := h
  obtain ⟨e, he⟩ := exists_clock_ge (p + q)
  have hpe : ∀ n, 2 ^ p.eval n ≤ clkE e n := fun n => by
    have h1 := he n
    rw [Polynomial.eval_add] at h1
    unfold clock at h1
    change 2 ^ p.eval n ≤ 2 ^ (n ^ e + e)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqe : ∀ n, q.eval n ≤ clock e n := fun n => by
    have h1 := he n
    rw [Polynomial.eval_add] at h1
    omega
  have hH : ∀ (B' : Set BitString) (x : BitString), Halted M (run M B' x (2 ^ p.eval x.length)) :=
    fun B' x => by
      obtain ⟨t, ht, hh⟩ := hp B' x
      rw [run_of_halted_le M B' x ht hh]
      exact hh
  refine ⟨M.code, e, fun x => ⟨((hsa x).mono_of_halted fun B' => hH B' x).code,
    fun z hz => ?_⟩, fun x => ?_⟩
  · obtain ⟨⟨B', s⟩, -, hs⟩ := exists_ask_of_mem_querySet hz
    simp only [OTM.run_code, OTM.askedAt_code] at hs
    exact (hq B' x z s hs).trans (hqe _)
  · rw [hA x]
    obtain ⟨t, ht, hh⟩ := hp B x
    constructor
    · intro hacc
      have h1 := (accepts_iff_of_halted M B x t hh).1 hacc
      exact ⟨t, ht.trans (hpe _), by rw [OTM.run_code, OTM.code_accept_iff]; exact h1⟩
    · rintro ⟨s, -, h'⟩
      rw [OTM.run_code, OTM.code_accept_iff] at h'
      exact ⟨s, h'⟩

/-! ### The family -/

/-- The specification of a decision procedure for `StrictSAPolyOn` on machine codes: the
`T`-parametrised version of `strictlySubAdaptiveB` (at `T = clkE e |x|`, built with
`queryListCodeT`) conjoined with the length test `∀ z ∈ queryListCodeT m (clkE e |x|) x,
|z| ≤ clock e |x|`; constructed below as `strictSAPolyDecider`. -/
structure StrictSAPolyDecider where
  /-- The decision procedure on machine codes `m` (`decodeCode m`). -/
  B : ℕ → ℕ → BitString → Bool
  B_iff : ∀ (m e : ℕ) (x : BitString), B m e x = true ↔ StrictSAPolyOn (decodeCode m) e x
  B_computable : Computable fun p : ℕ × ℕ × BitString => B p.1 p.2.1 p.2.2

/-- The family of exponentially clocked (`clkE`), strictly sub-adaptive machines with polynomial
query length, given a decider for `StrictSAPolyOn` (`Family.strictSAE` below uses
`strictSAPolyDecider`). -/
@[instance_reducible] def Family.strictSAEOf (D : StrictSAPolyDecider) : Family :=
  ⟨StrictSAPolyOn, D.B, D.B_iff, D.B_computable, clkE, clkE_computable⟩

/-! ### The address structure for an arbitrary time bound -/

/-- **The address structure of the game `gameOfT`.** Let `Q₁` be a finite set of strings queried
on every run of `c` on `x` within `Tc` steps (`hS1`), such that any two asks of the same string
`z ∉ Q₁` happen at the same step and the two oracles agree on all queries made before it (`hS2`).
Then `gameOfT c Tc x h ε X` has a `PathData` structure with strings in play `X`, possible queries
`querySet c.toOTM x Tc`, the outcome of the game, and, at the position `S`, the run
`queries c.toOTM (oracleOf h S) x Tc`. -/
theorem exists_pathData_of_stagesT (c : OTMCode) (Tc : ℕ) (x : BitString) (h : BitString → ℕ)
    (ε : ℝ)
    (X : Finset BitString) (hX : X ⊆ querySet c.toOTM x (Tc)) (Q₁ : Finset BitString)
    (hS1 : ∀ B : Set BitString, Q₁ ⊆ queries c.toOTM B x (Tc))
    (hS2 : ∀ (B B' : Set BitString) (t t' : ℕ) (z : BitString), t < Tc →
      t' < Tc → askedAt c.toOTM (run c.toOTM B x t) = some z →
      askedAt c.toOTM (run c.toOTM B' x t') = some z → z ∉ Q₁ →
      t = t' ∧ ∀ w ∈ queries c.toOTM B x t, (w ∈ B ↔ w ∈ B')) :
    ∃ D : PathData, D.X = X ∧ D.U = querySet c.toOTM x (Tc) ∧
      D.out = (gameOfT c Tc x h ε X).outcome ∧
      ∀ S, D.P S = queries c.toOTM (oracleOf h S) x (Tc) := by
  classical
  set M := c.toOTM with hM
  -- `agree`
  have hagree : ∀ S₁ S₂ : Finset BitString,
      (∀ z ∈ queries M (oracleOf h S₁) x Tc, (z ∈ S₁ ↔ z ∈ S₂)) →
      queries M (oracleOf h S₂) x Tc = queries M (oracleOf h S₁) x Tc ∧
        (gameOfT c Tc x h ε X).outcome S₂ = (gameOfT c Tc x h ε X).outcome S₁ := by
    intro S₁ S₂ hS
    have hag : ∀ z ∈ queries M (oracleOf h S₁) x Tc,
        (z ∈ oracleOf h S₁ ↔ z ∈ oracleOf h S₂) := by
      intro z hz
      simp only [oracleOf, Set.mem_ofPred_eq]
      rw [hS z hz]
    refine ⟨(queries_eq_of_agree M _ _ x Tc hag).symm, ?_⟩
    have hrun : ∀ t ≤ Tc, run M (oracleOf h S₁) x t = run M (oracleOf h S₂) x t :=
      fun t ht => run_eq_of_agree M _ _ x t fun z hz => hag z (queries_mono M _ x ht hz)
    have hiff :
        ClockedAcceptsT c Tc (oracleOf h S₂) x ↔ ClockedAcceptsT c Tc (oracleOf h S₁) x := by
      unfold ClockedAcceptsT
      constructor
      · rintro ⟨t, ht, h'⟩; exact ⟨t, ht, by rw [hrun t ht]; exact h'⟩
      · rintro ⟨t, ht, h'⟩; exact ⟨t, ht, by rw [← hrun t ht]; exact h'⟩
    simp only [gameOfT]
    exact decide_eq_decide.2 hiff
  -- `mem_P`
  have hmemP : ∀ z ∈ querySet M x Tc, ∀ S : Finset BitString,
      z ∈ queries M (oracleOf h S) x Tc ↔ ∀ p ∈ saAddr M x Tc Q₁ z,
        (decide (p.1.length ≤ h p.1) && !decide (p.1 ∈ S)) = p.2 := by
    intro z hzU S
    by_cases hzQ : z ∈ Q₁
    · rw [saAddr_of_mem hzQ]
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, iff_true]
      exact hS1 _ hzQ
    · obtain ⟨htz, hasz⟩ := askNode_spec hzU
      constructor
      · intro hzP p hp
        rw [mem_saAddr_of_not_mem hzQ] at hp
        obtain ⟨t', ht', hz'⟩ := (mem_queries M _ x Tc z).1 hzP
        obtain ⟨-, hag⟩ := hS2 _ _ _ _ z htz ht' hasz hz' hzQ
        rw [Bool.eq_iff_iff, ans_oracleOf_iff, hp.2]
        exact (hag p.1 hp.1).symm
      · intro hall
        have hag : ∀ w ∈ queries M (askNode M x Tc z).1 x (askNode M x Tc z).2,
            (w ∈ (askNode M x Tc z).1 ↔ w ∈ oracleOf h S) := by
          intro w hw
          have hp : (w, decide (w ∈ (askNode M x Tc z).1)) ∈ saAddr M x Tc Q₁ z :=
            (mem_saAddr_of_not_mem hzQ).2 ⟨hw, by simp⟩
          have := hall _ hp
          rw [Bool.eq_iff_iff, ans_oracleOf_iff] at this
          simp only [decide_eq_true_eq] at this
          exact this.symm
        have hrun := run_eq_of_agree M _ _ x _ hag
        rw [hrun] at hasz
        exact (mem_queries M _ x Tc z).2 ⟨_, htz, hasz⟩
  -- `addr_sub`
  have haddr : ∀ z ∈ querySet M x Tc, ∀ p ∈ saAddr M x Tc Q₁ z,
      p.1 ∈ querySet M x Tc ∧ saAddr M x Tc Q₁ p.1 ⊆ saAddr M x Tc Q₁ z := by
    intro z hzU p hp
    by_cases hzQ : z ∈ Q₁
    · rw [saAddr_of_mem hzQ] at hp
      simp at hp
    · obtain ⟨htz, hasz⟩ := askNode_spec hzU
      rw [mem_saAddr_of_not_mem hzQ] at hp
      obtain ⟨hw, -⟩ := hp
      obtain ⟨sw, hsw, hasw⟩ := (mem_queries M _ x _ p.1).1 hw
      have hwU : p.1 ∈ querySet M x Tc := mem_querySet_of_askedAt (hsw.trans htz) hasw
      refine ⟨hwU, fun q hq => ?_⟩
      by_cases hwQ : p.1 ∈ Q₁
      · rw [saAddr_of_mem hwQ] at hq
        simp at hq
      · obtain ⟨htw, hasw'⟩ := askNode_spec hwU
        rw [mem_saAddr_of_not_mem hwQ] at hq
        obtain ⟨hq1, hq2⟩ := hq
        obtain ⟨heq, hag⟩ := hS2 _ _ _ _ p.1 htw (hsw.trans htz) hasw' hasw hwQ
        have hqe := queries_eq_of_agree M _ _ x _ hag
        rw [mem_saAddr_of_not_mem hzQ]
        refine ⟨?_, ?_⟩
        · have h1 : q.1 ∈ queries M (askNode M x Tc z).1 x (askNode M x Tc p.1).2 := by
            rw [← hqe]; exact hq1
          rw [heq] at h1
          exact queries_mono M _ x hsw.le h1
        · rw [hq2]
          exact hag q.1 hq1
  refine ⟨{ U := querySet M x Tc
            X := X
            base := fun w => decide (w.length ≤ h w)
            P := fun S => queries M (oracleOf h S) x Tc
            out := (gameOfT c Tc x h ε X).outcome
            addr := saAddr M x Tc Q₁
            X_sub := hX
            P_sub := fun S => queries_subset_querySet M _ x Tc
            agree := hagree
            mem_P := hmemP
            addr_sub := haddr }, rfl, rfl, rfl, fun _ => rfl⟩


/-- The address structure of a machine that is strictly sub-adaptive within the time bound `T`
(the `T`-version of `exists_pathData_of_strict`). -/
theorem exists_pathData_of_strictT (c : OTMCode) (T : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (hX : X ⊆ querySet c.toOTM x T) (hsa : StrictlySA c.toOTM x T) :
    ∃ D : PathData, D.X = X ∧ D.U = querySet c.toOTM x T ∧
      D.out = (gameOfT c T x h ε X).outcome ∧
      ∀ S, D.P S = queries c.toOTM (oracleOf h S) x T := by
  obtain ⟨k, -, -, hS1, -, -, hS2, -⟩ := SubAdaptive.exists_boundary hsa.subAdaptive
  refine exists_pathData_of_stagesT c T x h ε X hX (stage1Set c.toOTM x T k) hS1 ?_
  intro B B' t t' z ht ht' hz hz' hQ
  obtain ⟨hans, -, -⟩ := hS2 B B' t t' z ht ht' hz hz' hQ
  exact (answers_eq_iff hz hz').1 hans

/-! ### The key recursion at the exponential clock -/

/-- The flip costs of the game `gameOfT` (any time bound `Tm`) are the multiples
`costNum … / 2 ^ gameN` for strings of length at most `clock e |x|`. -/
theorem gameOfT_flipCost_eq (c : OTMCode) (e Tm : ℕ) (T : Table) (m : ℕ) (X : Finset BitString)
    (x z : BitString) (hlen : z.length ≤ clock e x.length) :
    flipCost (gameOfT c Tm x T.fn ((2 : ℝ)⁻¹ ^ m) X) z =
      (costNum (gameN e T m x.length) (T.fn z) z.length : ℝ) / 2 ^ gameN e T m x.length := by
  have hT : T.fn z ≤ 2 * z.length + 6 + T.dom.sup T.value := by
    unfold Table.fn
    split_ifs with h
    · have := Finset.le_sup (f := T.value) h; omega
    · omega
  change max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ T.fn z) = _
  rw [max_sub_eq_div (gameN e T m x.length) (z.length - 1) (T.fn z) (by unfold gameN; omega)
    (by unfold gameN; omega)]
  rfl

/-- The budget of the game `gameOfT` is `2 ^ (gameN - m) / 2 ^ gameN`. -/
theorem gameOfT_eps_eq (c : OTMCode) (e Tm : ℕ) (T : Table) (m : ℕ) (x : BitString)
    (X : Finset BitString) :
    (gameOfT c Tm x T.fn ((2 : ℝ)⁻¹ ^ m) X).ε =
      ((2 ^ (gameN e T m x.length - m) : ℕ) : ℝ) / 2 ^ gameN e T m x.length := by
  change (2 : ℝ)⁻¹ ^ m = _
  push_cast
  rw [two_pow_sub_div_two_pow _ _ (by unfold gameN; omega)]

/-- **The key recursion computes the value of the game at the exponential clock** for a machine
with `StrictSAPolyOn`: precision `gameN` (the queries have length `≤ clock e |x|`) and fuel
`2 ^ (clock e |x| + 1)` (the queries lie in `strsUpTo (clock e |x|)`). -/
theorem valKRaw_gameOfT_of_strictSAPoly (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ)
    (Y : Finset BitString) (x : BitString) (hsa : StrictSAPolyOn c e x) :
    valKRaw (querySet c.toOTM x (clkE e x.length) \ Y)
        (fun S => queries c.toOTM (oracleOf T.fn S) x (clkE e x.length))
        (gameOfT c (clkE e x.length) x T.fn ((2 : ℝ)⁻¹ ^ m)
          (querySet c.toOTM x (clkE e x.length) \ Y)).outcome
        (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
        (2 ^ (gameN e T m x.length - m)) (2 ^ (clock e x.length + 1)) =
      val (gameOfT c (clkE e x.length) x T.fn ((2 : ℝ)⁻¹ ^ m)
        (querySet c.toOTM x (clkE e x.length) \ Y)) := by
  obtain ⟨D, hDX, -, hDout, hDP⟩ := exists_pathData_of_strictT c (clkE e x.length) x T.fn
    ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clkE e x.length) \ Y) Finset.sdiff_subset hsa.1
  have hsub : querySet c.toOTM x (clkE e x.length) \ Y ⊆ strsUpTo (clock e x.length) :=
    fun z hz => mem_strsUpTo (hsa.2 z (Finset.mem_sdiff.1 hz).1)
  exact D.valKRaw_eq_val hDX hDP (fun S => by rw [hDout]) _ (gameN e T m x.length) _ _ _ rfl rfl
    (fun z hz => gameOfT_flipCost_eq c e _ T m _ x z
      (hsa.2 z (Finset.mem_sdiff.1 (show z ∈ querySet c.toOTM x (clkE e x.length) \ Y from hz)).1))
    (gameOfT_eps_eq c e _ T m x _)
    ((Finset.card_le_card hsub).trans (card_strsUpTo_lt _).le)

/-- The language of the key recursion at the exponential clock: the target of the evaluator
(`valKLang` with the time bound `clkE e |x|` in place of `clock e |x|`; the precision `gameN` and
the fuel `2 ^ (clock e |x| + 1)` stay polynomial resp. singly exponential thanks to the polynomial
query length). -/
def valKLangE (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) : Set BitString :=
  {x | valKRaw (querySet c.toOTM x (clkE e x.length) \ Y)
      (fun S => queries c.toOTM (oracleOf T.fn S) x (clkE e x.length))
      (gameOfT c (clkE e x.length) x T.fn ((2 : ℝ)⁻¹ ^ m)
        (querySet c.toOTM x (clkE e x.length) \ Y)).outcome
      (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
      (2 ^ (gameN e T m x.length - m)) (2 ^ (clock e x.length + 1)) = true}

/-- **`hgame` for `EXP` and the exponentially clocked strictly sub-adaptive machines with
polynomial query length, given the evaluator.** -/
theorem gameValue_mem_EXP_of_strictSAPoly
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLangE c e T m Y ∈ EXP)
    (c : OTMCode) (e : ℕ) (Z : Finset BitString) (hΦ : ∀ x, x ∉ Z → StrictSAPolyOn c e x)
    (T : Table) (m : ℕ) (Y : Finset BitString) :
    {x : BitString | val (gameOfT c (clkE e x.length) x T.fn ((2 : ℝ)⁻¹ ^ m)
      (querySet c.toOTM x (clkE e x.length) \ Y)) = true} ∈ EXP :=
  EXP_of_eventually_eq _ _ (hprog c e T m Y) Z fun x hx => by
    change _ = true ↔ _ = true
    rw [valKRaw_gameOfT_of_strictSAPoly c e T m Y x (hΦ x hx)]

/-- **`EXP^R_{ssa,poly} ⊆ EXP`, given the evaluator, for any decider of `StrictSAPolyOn`**: a
decidable set that is, for every universal a priori complexity `K`, decided with the oracle `R_K`
by an exponential-time strictly sub-adaptive machine with polynomial query length lies in `EXP`. -/
theorem dec_inter_expTimeStrictSAPoly_RA_subset_EXP_of_eval_of_decider (D : StrictSAPolyDecider)
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLangE c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ ExpTimeStrictSAPoly (RA K)) :
    A ∈ EXP := by
  let _ := Family.strictSAEOf D
  exact general EXP EXP_of_eventually_eq'
    (fun c e Z hZ T m Y => gameValue_mem_EXP_of_strictSAPoly hprog c e Z hZ T m Y) A hA
    fun K hKU => exists_clockedE_strictSAPoly _ _ (hK K hKU)

/-! ### Deciding `StrictSAPolyOn`: the decider for an arbitrary time bound -/

/-- Every oracle agrees on the possible queries with a finite oracle given by a sublist of
`queryListCodeT m T x`. -/
theorem exists_allSub_agreeT (m T : ℕ) (x : BitString) (B : Set BitString) :
    ∃ L ∈ allSub (queryListCodeT m T x),
      ∀ z ∈ querySet (decodeCode m).toOTM x (T), (z ∈ B ↔ z ∈ {w | w ∈ L}) := by
  classical
  obtain ⟨L, hL, hLT⟩ := exists_allSub (queryListCodeT m T x)
    ((queryListCodeT m T x).toFinset.filter fun z => z ∈ B)
    fun z hz => List.mem_toFinset.1 (Finset.mem_filter.1 hz).1
  refine ⟨L, hL, fun z hz => ?_⟩
  rw [querySet_eq_toFinsetT] at hz
  change z ∈ B ↔ z ∈ L
  rw [← List.mem_toFinset (l := L), hLT, Finset.mem_filter]
  exact ⟨fun hB => ⟨hz, hB⟩, fun h' => h'.2⟩

/-- The asks within the clock made after at least `k` earlier asks, under the finite oracles
`L ⊆ queryListCodeT m T x`: pairs (answers received before the ask, asked string). -/
def askNodesT (m T : ℕ) (x : BitString) (k : ℕ) : List (List Bool × BitString) :=
  (allSub (queryListCodeT m T x)).flatMap fun L => (List.range (T)).flatMap fun t =>
    bif decide (k ≤ (queriesC m L x t).length) && askB m (runC m L x t) then
      [(answersC m L x t, (runC m L x t).buf)] else []

/-- A pair `p` lies in `askNodesT m T x k` iff for some finite oracle
`L ∈ allSub (queryListCodeT m T x)` and some step `t < T` with at least `k` earlier queries,
`decodeCode m` asks at step `t` and `p` is the pair (answers received so far, asked string). -/
theorem mem_askNodesT (m T : ℕ) (x : BitString) (k : ℕ) (p : List Bool × BitString) :
    p ∈ askNodesT m T x k ↔ ∃ L ∈ allSub (queryListCodeT m T x), ∃ t < T,
      k ≤ (queriesC m L x t).length ∧ askB m (runC m L x t) = true ∧
        (answersC m L x t, (runC m L x t).buf) = p := by
  simp only [askNodesT, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨L, hL, t, ht, hc⟩
    cases hb : (decide (k ≤ (queriesC m L x t).length) && askB m (runC m L x t))
    · rw [hb] at hc
      simp at hc
    · rw [hb] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [Bool.cond_true, List.mem_singleton] at hc
      exact ⟨L, hL, t, ht, hb.1, hb.2, hc.symm⟩
  · rintro ⟨L, hL, t, ht, hk, ha, rfl⟩
    refine ⟨L, hL, t, ht, ?_⟩
    rw [decide_eq_true hk, ha]
    simp

/-- Every ask node is an ask after at least `k` earlier asks, with its answer history. -/
theorem askNodesT_sound {m T : ℕ} {x : BitString} {k : ℕ} {p : List Bool × BitString}
    (hp : p ∈ askNodesT m T x k) :
    ∃ (B : Set BitString) (t : ℕ), t < T ∧
      k ≤ (queryList (decodeCode m).toOTM B x t).length ∧
      askedAt (decodeCode m).toOTM (run (decodeCode m).toOTM B x t) = some p.2 ∧
      answers (decodeCode m).toOTM B x t = p.1 := by
  obtain ⟨L, -, t, ht, hk, ha, rfl⟩ := (mem_askNodesT m T x k p).1 hp
  refine ⟨{w | w ∈ L}, t, ht, by rwa [← queriesC_eq_queryList], ?_,
    (answersC_eq_answers m L x t).symm⟩
  rw [askedAt_eq_of_rep m _ _ (runC_represents m L x t), ha]
  rfl

/-- Every ask within the clock after at least `k` earlier asks is an ask node, with its answer
history. -/
theorem askNodesT_complete {m T : ℕ} {x : BitString} {k : ℕ} {B : Set BitString} {t : ℕ}
    {z : BitString}
    (ht : t < T) (hk : k ≤ (queryList (decodeCode m).toOTM B x t).length)
    (hz : askedAt (decodeCode m).toOTM (run (decodeCode m).toOTM B x t) = some z) :
    (answers (decodeCode m).toOTM B x t, z) ∈ askNodesT m T x k := by
  obtain ⟨L, hL, hag⟩ := exists_allSub_agreeT m T x B
  have hrun := run_eq_of_agree_querySet _ B {w | w ∈ L} x _ hag ht.le
  have hql := queryList_eq_of_agree_querySet _ B {w | w ∈ L} x _ hag ht.le
  have hans := answers_eq_of_agree_querySet _ B {w | w ∈ L} x _ hag ht.le
  have hask := askedAt_eq_of_rep m _ _ (runC_represents m L x t)
  rw [← hrun, hz] at hask
  cases ha : askB m (runC m L x t)
  · rw [ha] at hask
    simp at hask
  · rw [ha] at hask
    simp only [Bool.cond_true, Option.some.injEq] at hask
    refine (mem_askNodesT m T x k _).2 ⟨L, hL, t, ht, ?_, ha, ?_⟩
    · rw [queriesC_eq_queryList, ← hql]
      exact hk
    · rw [answersC_eq_answers, ← hans, hask]

/-- The history test with boundary `k`: two ask nodes (after at least `k` earlier asks) with the
same string have the same answer history. -/
def stage2BT (m T : ℕ) (x : BitString) (k : ℕ) : Bool :=
  allB (askNodesT m T x k) fun p => allB (askNodesT m T x k) fun p' =>
    !decide (p.2 = p'.2) || decide (p.1 = p'.1)

/-- The history test `stage2BT m T x k` holds iff any two asks of `decodeCode m` on `x` within
`T` steps, under arbitrary oracles and each made after at least `k` earlier queries, that follow
different answer histories ask different strings. -/
theorem stage2BT_iff (m T : ℕ) (x : BitString) (k : ℕ) :
    stage2BT m T x k = true ↔ ∀ (B B' : Set BitString) (t t' : ℕ) (z z' : BitString),
      t < T → t' < T →
      k ≤ (queryList (decodeCode m).toOTM B x t).length →
      k ≤ (queryList (decodeCode m).toOTM B' x t').length →
      askedAt (decodeCode m).toOTM (run (decodeCode m).toOTM B x t) = some z →
      askedAt (decodeCode m).toOTM (run (decodeCode m).toOTM B' x t') = some z' →
      answers (decodeCode m).toOTM B x t ≠ answers (decodeCode m).toOTM B' x t' → z ≠ z' := by
  unfold stage2BT
  simp only [allB_iff, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq]
  constructor
  · intro h B B' t t' z z' ht ht' hk hk' hz hz' hne hzz
    rcases h _ (askNodesT_complete ht hk hz) _ (askNodesT_complete ht' hk' hz') with hb | ha
    · exact hb hzz
    · exact hne ha
  · intro h p hp p' hp'
    obtain ⟨B, t, ht, hk, hz, h1⟩ := askNodesT_sound hp
    obtain ⟨B', t', ht', hk', hz', h1'⟩ := askNodesT_sound hp'
    rw [← h1, ← h1']
    by_cases ha : answers (decodeCode m).toOTM B x t = answers (decodeCode m).toOTM B' x t'
    · exact Or.inr ha
    · exact Or.inl (h B B' t t' _ _ ht ht' hk hk' hz hz' ha)

/-- Decision procedure for the strict sub-adaptivity of the coded machine `decodeCode m` on `x`
within `T` steps: the history test with boundary `0`. -/
def strictlySAB (m T : ℕ) (x : BitString) : Bool := stage2BT m T x 0

/-- `strictlySAB m T x` holds iff the machine `decodeCode m` is strictly sub-adaptive on `x`
within `T` steps (`StrictlySA`). -/
theorem strictlySAB_iff (m T : ℕ) (x : BitString) :
    strictlySAB m T x = true ↔ StrictlySA (decodeCode m).toOTM x T := by
  rw [strictlySAB, stage2BT_iff]
  unfold StrictlySA
  constructor
  · intro h B B' t t' z z' ht ht' hz hz' hne
    exact h B B' t t' z z' ht ht' (Nat.zero_le _) (Nat.zero_le _) hz hz' hne
  · intro h B B' t t' z z' ht ht' _ _ hz hz' hne
    exact h B B' t t' z z' ht ht' hz hz' hne

attribute [local irreducible] answersC queriesC runC askB allSub queryListCodeT in
/-- `askNodesT m T x k` is a primitive recursive function of `((m, T, x), k)`. -/
theorem askNodesT_primrec :
    Primrec fun a : (ℕ × ℕ × BitString) × ℕ => askNodesT a.1.1 a.1.2.1 a.1.2.2 a.2 := by
  have hT : Primrec fun a : (ℕ × ℕ × BitString) × ℕ => a.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hQ : Primrec fun a : (ℕ × ℕ × BitString) × ℕ =>
      allSub (queryListCodeT a.1.1 a.1.2.1 a.1.2.2) :=
    allSub_primrec.comp (queryListCodeT_primrec.comp Primrec.fst)
  have harg : Primrec fun r : (((ℕ × ℕ × BitString) × ℕ) × List BitString) × ℕ =>
      (r.1.1.1.1, r.1.2, r.1.1.1.2.2, r.2) :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      ((Primrec.snd.comp Primrec.fst).pair
        ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst)))).pair Primrec.snd))
  have hm : Primrec fun r : (((ℕ × ℕ × BitString) × ℕ) × List BitString) × ℕ => r.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hk : Primrec fun r : (((ℕ × ℕ × BitString) × ℕ) × List BitString) × ℕ => r.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hrun := runC_primrec.comp harg
  have hlen := Primrec.list_length.comp (queriesC_primrec.comp harg)
  have hnode := (answersC_primrec.comp harg).pair (CC.primrec_buf.comp hrun)
  have hinner := Primrec.cond (Primrec.and.comp (Primrec.nat_le.decide.comp hk hlen)
    (askB_primrec.comp hm hrun)) (Primrec.list_cons.comp hnode (Primrec.const []))
    (Primrec.const [])
  have hrange : Primrec fun p : ((ℕ × ℕ × BitString) × ℕ) × List BitString =>
      List.range p.1.1.2.1 :=
    Primrec.list_range.comp (hT.comp Primrec.fst)
  have hmid := Primrec.list_flatMap hrange hinner.to₂
  exact (Primrec.list_flatMap hQ hmid.to₂).of_eq fun _ => rfl

attribute [local irreducible] askNodesT in
/-- `stage2BT m T x k` is a primitive recursive function of `((m, T, x), k)`. -/
theorem stage2BT_primrec :
    Primrec fun a : (ℕ × ℕ × BitString) × ℕ => stage2BT a.1.1 a.1.2.1 a.1.2.2 a.2 := by
  have hL := askNodesT_primrec
  have hF : Primrec₂ fun (p p' : List Bool × BitString) =>
      (!decide (p.2 = p'.2) || decide (p.1 = p'.1)) :=
    (Primrec.or.comp (Primrec.not.comp (Primrec.eq.decide.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))) (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))).to₂
  have hin : Primrec fun b : ((ℕ × ℕ × BitString) × ℕ) × (List Bool × BitString) =>
      allB (askNodesT b.1.1.1 b.1.1.2.1 b.1.1.2.2 b.1.2) fun p' =>
        !decide (b.2.2 = p'.2) || decide (b.2.1 = p'.1) :=
    (Primrec.list_foldr
      (f := fun b : ((ℕ × ℕ × BitString) × ℕ) × (List Bool × BitString) =>
        askNodesT b.1.1.1 b.1.1.2.1 b.1.1.2.2 b.1.2)
      (g := fun _ => true)
      (h := fun b q => (!decide (b.2.2 = q.1.2) || decide (b.2.1 = q.1.1)) && q.2)
      (hL.comp Primrec.fst) (Primrec.const true)
      (Primrec.and.comp (hF.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  exact (Primrec.list_foldr
    (f := fun a : (ℕ × ℕ × BitString) × ℕ => askNodesT a.1.1 a.1.2.1 a.1.2.2 a.2)
    (g := fun _ => true)
    (h := fun a q => (allB (askNodesT a.1.1 a.1.2.1 a.1.2.2 a.2) fun p' =>
      !decide (q.1.2 = p'.2) || decide (q.1.1 = p'.1)) && q.2) hL (Primrec.const true)
    (Primrec.and.comp (hin.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

attribute [local irreducible] stage2BT in
/-- `strictlySAB m T x` is a primitive recursive function of `(m, T, x)`. -/
theorem strictlySAB_primrec :
    Primrec fun p : ℕ × ℕ × BitString => strictlySAB p.1 p.2.1 p.2.2 :=
  (stage2BT_primrec.comp (Primrec.id.pair (Primrec.const 0))).of_eq fun _ => rfl

/-- The length test: every possible query of `decodeCode m` on `x` within `T` steps has length at
most `n`. -/
def queryLenB (m T n : ℕ) (x : BitString) : Bool :=
  allB (queryListCodeT m T x) fun z => decide (z.length ≤ n)

/-- `queryLenB m T n x` holds iff every possible query of `decodeCode m` on `x` within `T` steps
has length at most `n`. -/
theorem queryLenB_iff (m T n : ℕ) (x : BitString) :
    queryLenB m T n x = true ↔ ∀ z ∈ querySet (decodeCode m).toOTM x T, z.length ≤ n := by
  unfold queryLenB
  simp only [allB_iff, decide_eq_true_eq, querySet_eq_toFinsetT, List.mem_toFinset]

attribute [local irreducible] queryListCodeT in
/-- `queryLenB m T n x` is a primitive recursive function of `(m, T, n, x)`. -/
theorem queryLenB_primrec :
    Primrec fun p : ℕ × ℕ × ℕ × BitString => queryLenB p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hl : Primrec fun p : ℕ × ℕ × ℕ × BitString => queryListCodeT p.1 p.2.1 p.2.2.2 :=
    queryListCodeT_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.list_foldr (f := fun p : ℕ × ℕ × ℕ × BitString => queryListCodeT p.1 p.2.1 p.2.2.2)
    (g := fun _ => true)
    (h := fun p q => decide (q.1.length ≤ p.2.2.1) && q.2) hl (Primrec.const true)
    (Primrec.and.comp (Primrec.nat_le.decide.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- **The decision procedure for `StrictSAPolyOn`** on machine codes. -/
def strictSAPolyB (m e : ℕ) (x : BitString) : Bool :=
  strictlySAB m (clkE e x.length) x && queryLenB m (clkE e x.length) (clock e x.length) x

/-- `strictSAPolyB m e x` holds iff the coded machine `decodeCode m` satisfies `StrictSAPolyOn`
at clock index `e` on `x`: it is strictly sub-adaptive within `clkE e |x|` steps and all its
possible queries have length at most `clock e |x|`. -/
theorem strictSAPolyB_iff (m e : ℕ) (x : BitString) :
    strictSAPolyB m e x = true ↔ StrictSAPolyOn (decodeCode m) e x := by
  rw [strictSAPolyB, Bool.and_eq_true, strictlySAB_iff, queryLenB_iff]
  rfl

attribute [local irreducible] strictlySAB queryLenB clkE clock in
/-- `strictSAPolyB m e x` is a primitive recursive function of `(m, e, x)`. -/
theorem strictSAPolyB_primrec :
    Primrec fun p : ℕ × ℕ × BitString => strictSAPolyB p.1 p.2.1 p.2.2 := by
  have hn : Primrec fun p : ℕ × ℕ × BitString => p.2.2.length :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
  have hT : Primrec fun p : ℕ × ℕ × BitString => clkE p.2.1 p.2.2.length :=
    clkE_primrec.comp (Primrec.fst.comp Primrec.snd) hn
  have hc : Primrec fun p : ℕ × ℕ × BitString => clock p.2.1 p.2.2.length :=
    clock_primrec.comp (Primrec.fst.comp Primrec.snd) hn
  exact (Primrec.and.comp
    (strictlySAB_primrec.comp (Primrec.fst.pair (hT.pair (Primrec.snd.comp Primrec.snd))))
    (queryLenB_primrec.comp (Primrec.fst.pair (hT.pair (hc.pair
      (Primrec.snd.comp Primrec.snd)))))).of_eq fun _ => rfl

/-- The decider for `StrictSAPolyOn`. -/
def strictSAPolyDecider : StrictSAPolyDecider :=
  ⟨strictSAPolyB, strictSAPolyB_iff, strictSAPolyB_primrec.to_comp⟩

/-- **The family `Family.strictSAE`**: exponentially clocked (`clkE`), strictly sub-adaptive
machines with polynomial query length, with the decider `strictSAPolyB`. -/
@[instance_reducible] def Family.strictSAE : Family := Family.strictSAEOf strictSAPolyDecider

/-- **`EXP^R_{ssa,poly} ⊆ EXP`, given the evaluator** (the exponential-time strictly sub-adaptive
case with polynomial query length): a decidable set that is, for every universal a priori
complexity `K`, decided with the oracle `R_K` by an exponential-time strictly sub-adaptive machine
with polynomial query length lies in `EXP`, provided the key-recursion languages `valKLangE` are
in `EXP`. -/
theorem dec_inter_expTimeStrictSAPoly_RA_subset_EXP_of_eval
    (hprog : ∀ (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString),
      valKLangE c e T m Y ∈ EXP)
    (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hK : ∀ K : AprioriComplexity, K.Universal → A ∈ ExpTimeStrictSAPoly (RA K)) :
    A ∈ EXP := by
  let _ := Family.strictSAE
  exact general EXP EXP_of_eventually_eq'
    (fun c e Z hZ T m Y => gameValue_mem_EXP_of_strictSAPoly hprog c e Z hZ T m Y) A hA
    fun K hKU => exists_clockedE_strictSAPoly _ _ (hK K hKU)

end Kolmogorov.RandomStrings
