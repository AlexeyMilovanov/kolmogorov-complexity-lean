/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.PathGame
import KolmogorovMathlib.RandomStrings.SubAdaptive

/-!
# The address structure of a sub-adaptive clocked machine

For a clocked machine `(c, e)` that is sub-adaptive on `x` (`SubAdaptiveOn`, history nodes, the
stage boundary being the `k`-th ask), the game `G_{e,x}` has an address structure
(`exists_pathData`): the strings of the stage-1 set `Q₁` get the empty address (they lie on every
run); every other possible query `z` gets the answer history of one of its asks (it is asked
at a single node of the reduction tree).  With `PathData.valKRaw_eq_val` this gives
`valKRaw_gameOf_of_subAdaptive`: the key recursion computes the value of the game.

* `exists_pathData_of_stages`: the construction from the assumptions only;
* `exists_pathData`, `exists_pathData_of_strict`: the instances for `SubAdaptiveOn` and
  `StrictlySubAdaptiveOn`;
* `valKRaw_gameOf_of_subAdaptive`: the value of `G_{e,x}` is the raw key recursion over the
  strings in play, the run map `S ↦ queries c.toOTM (oracleOf T.fn S) x (clock e |x|)` and the
  outcome of the game.
-/

namespace Kolmogorov.RandomStrings

/-- A possible query is asked at some time `< T` under some oracle. -/
theorem exists_ask_of_mem_querySet {M : OTM} {x : BitString} {T : ℕ} {z : BitString}
    (hz : z ∈ querySet M x T) :
    ∃ p : Set BitString × ℕ, p.2 < T ∧ askedAt M (run M p.1 x p.2) = some z := by
  rw [mem_querySet_iff_queryAll] at hz
  obtain ⟨B, hB⟩ := hz
  obtain ⟨s, hs, hz⟩ := (mem_queries M B x T z).1 hB
  exact ⟨(B, s), hs, hz⟩

/-- A query asked at a time `< T` is a possible query. -/
theorem mem_querySet_of_askedAt {M : OTM} {x : BitString} {T : ℕ} {B : Set BitString} {t : ℕ}
    {z : BitString} (ht : t < T) (hz : askedAt M (run M B x t) = some z) : z ∈ querySet M x T := by
  rw [mem_querySet_iff_queryAll]
  exact ⟨B, (mem_queries M B x T z).2 ⟨t, ht, hz⟩⟩

/-- The queries under one oracle are possible queries. -/
theorem queries_subset_querySet (M : OTM) (B : Set BitString) (x : BitString) (T : ℕ) :
    queries M B x T ⊆ querySet M x T := fun z hz => by
  obtain ⟨s, hs, hz⟩ := (mem_queries M B x T z).1 hz
  exact mem_querySet_of_askedAt hs hz

open Classical in
/-- A chosen ask of `z` within `T` steps: an oracle and a time. -/
noncomputable def askNode (M : OTM) (x : BitString) (T : ℕ) (z : BitString) : Set BitString × ℕ :=
  if h : ∃ p : Set BitString × ℕ, p.2 < T ∧ askedAt M (run M p.1 x p.2) = some z then
    Classical.choose h else (∅, 0)

/-- The chosen node specifies an oracle and a time bounded by `T` where the machine `M` running
on `x` asks the query `z`. -/
theorem askNode_spec {M : OTM} {x : BitString} {T : ℕ} {z : BitString} (hz : z ∈ querySet M x T) :
    (askNode M x T z).2 < T ∧
      askedAt M (run M (askNode M x T z).1 x (askNode M x T z).2) = some z := by
  have h := exists_ask_of_mem_querySet hz
  unfold askNode
  rw [dite_eq_left h]
  exact Classical.choose_spec h

open Classical in
/-- The address of `z` for the stage-1 set `Q₁`: empty on `Q₁`; otherwise the earlier queries of
the chosen ask of `z`, with their answers. -/
noncomputable def saAddr (M : OTM) (x : BitString) (T : ℕ) (Q₁ : Finset BitString) (z : BitString) :
    Finset (BitString × Bool) :=
  if z ∈ Q₁ then ∅ else
    (queries M (askNode M x T z).1 x (askNode M x T z).2).image
      fun w => (w, decide (w ∈ (askNode M x T z).1))

/-- The address of `z` relative to the stage-1 set `Q₁` is empty if `z` is in `Q₁`. -/
theorem saAddr_of_mem {M : OTM} {x : BitString} {T : ℕ} {Q₁ : Finset BitString}
    {z : BitString} (hz : z ∈ Q₁) : saAddr M x T Q₁ z = ∅ := by
  unfold saAddr; rw [ite_eq_left hz]

/-- The membership characterization for the address of `z` relative to the stage-1 set `Q₁` when
`z` is not in `Q₁`. -/
theorem mem_saAddr_of_not_mem {M : OTM} {x : BitString} {T : ℕ} {Q₁ : Finset BitString}
    {z : BitString} (hz : z ∉ Q₁) {p : BitString × Bool} :
    p ∈ saAddr M x T Q₁ z ↔ p.1 ∈ queries M (askNode M x T z).1 x (askNode M x T z).2 ∧
      (p.2 = true ↔ p.1 ∈ (askNode M x T z).1) := by
  classical
  unfold saAddr
  rw [ite_eq_right hz, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, by simp⟩
  · rintro ⟨hw, hb⟩
    refine ⟨p.1, hw, ?_⟩
    obtain ⟨w, b⟩ := p
    simp only at hb ⊢
    cases b <;> simp_all

/-- The answer to `w` at the position `S` of the game. -/
theorem ans_oracleOf_iff (h : BitString → ℕ) (S : Finset BitString) (w : BitString) :
    (decide (w.length ≤ h w) && !decide (w ∈ S)) = true ↔ w ∈ oracleOf h S := by
  simp [oracleOf]

/-- **The address structure**: if a set `Q₁` lies on every run
and every possible query outside `Q₁` is asked at a single node of the reduction tree, the game
`G_{e,x}` has an address structure. -/
theorem exists_pathData_of_stages (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (hX : X ⊆ querySet c.toOTM x (clock e x.length)) (Q₁ : Finset BitString)
    (hS1 : ∀ B : Set BitString, Q₁ ⊆ queries c.toOTM B x (clock e x.length))
    (hS2 : ∀ (B B' : Set BitString) (t t' : ℕ) (z : BitString), t < clock e x.length →
      t' < clock e x.length → askedAt c.toOTM (run c.toOTM B x t) = some z →
      askedAt c.toOTM (run c.toOTM B' x t') = some z → z ∉ Q₁ →
      t = t' ∧ ∀ w ∈ queries c.toOTM B x t, (w ∈ B ↔ w ∈ B')) :
    ∃ D : PathData, D.X = X ∧ D.U = querySet c.toOTM x (clock e x.length) ∧
      D.out = (gameOf c e x h ε X).outcome ∧
      ∀ S, D.P S = queries c.toOTM (oracleOf h S) x (clock e x.length) := by
  classical
  set M := c.toOTM with hM
  set Tc := clock e x.length with hTc
  -- `agree`
  have hagree : ∀ S₁ S₂ : Finset BitString,
      (∀ z ∈ queries M (oracleOf h S₁) x Tc, (z ∈ S₁ ↔ z ∈ S₂)) →
      queries M (oracleOf h S₂) x Tc = queries M (oracleOf h S₁) x Tc ∧
        (gameOf c e x h ε X).outcome S₂ = (gameOf c e x h ε X).outcome S₁ := by
    intro S₁ S₂ hS
    have hag : ∀ z ∈ queries M (oracleOf h S₁) x Tc,
        (z ∈ oracleOf h S₁ ↔ z ∈ oracleOf h S₂) := by
      intro z hz
      simp only [oracleOf, Set.mem_ofPred_eq]
      rw [hS z hz]
    refine ⟨(queries_eq_of_agree M _ _ x Tc hag).symm, ?_⟩
    have hrun : ∀ t ≤ Tc, run M (oracleOf h S₁) x t = run M (oracleOf h S₂) x t :=
      fun t ht => run_eq_of_agree M _ _ x t fun z hz => hag z (queries_mono M _ x ht hz)
    have hiff : ClockedAccepts c e (oracleOf h S₂) x ↔ ClockedAccepts c e (oracleOf h S₁) x := by
      unfold ClockedAccepts
      constructor
      · rintro ⟨t, ht, h'⟩; exact ⟨t, ht, by rw [hrun t ht]; exact h'⟩
      · rintro ⟨t, ht, h'⟩; exact ⟨t, ht, by rw [← hrun t ht]; exact h'⟩
    simp only [gameOf]
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
            out := (gameOf c e x h ε X).outcome
            addr := saAddr M x Tc Q₁
            X_sub := hX
            P_sub := fun S => queries_subset_querySet M _ x Tc
            agree := hagree
            mem_P := hmemP
            addr_sub := haddr }, rfl, rfl, rfl, fun _ => rfl⟩

/-- **The address structure of a sub-adaptive clocked machine**. -/
theorem exists_pathData (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (hX : X ⊆ querySet c.toOTM x (clock e x.length))
    (hsa : SubAdaptiveOn c e x) :
    ∃ D : PathData, D.X = X ∧ D.U = querySet c.toOTM x (clock e x.length) ∧
      D.out = (gameOf c e x h ε X).outcome ∧
      ∀ S, D.P S = queries c.toOTM (oracleOf h S) x (clock e x.length) := by
  obtain ⟨k, -, -, hS1, -, -, hS2, -⟩ := SubAdaptive.exists_boundary hsa
  refine exists_pathData_of_stages c e x h ε X hX (stage1Set c.toOTM x (clock e x.length) k)
    hS1 ?_
  intro B B' t t' z ht ht' hz hz' hQ
  obtain ⟨hans, -, -⟩ := hS2 B B' t t' z ht ht' hz hz' hQ
  exact (answers_eq_iff hz hz').1 hans

/-- The address structure of a strictly sub-adaptive clocked machine. -/
theorem exists_pathData_of_strict (c : OTMCode) (e : ℕ) (x : BitString) (h : BitString → ℕ) (ε : ℝ)
    (X : Finset BitString) (hX : X ⊆ querySet c.toOTM x (clock e x.length))
    (hsa : StrictlySubAdaptiveOn c e x) :
    ∃ D : PathData, D.X = X ∧ D.U = querySet c.toOTM x (clock e x.length) ∧
      D.out = (gameOf c e x h ε X).outcome ∧
      ∀ S, D.P S = queries c.toOTM (oracleOf h S) x (clock e x.length) :=
  exists_pathData c e x h ε X hX hsa.subAdaptiveOn

/-- **The key recursion computes the value of `G_{e,x}` for a sub-adaptive machine**:
the raw recursion over the strings in play, the runs
`S ↦ queries c.toOTM (oracleOf T.fn S) x (clock e |x|)` and the outcome of the game, with the
cost numerators `costNum` at the precision `gameN` and any fuel `F ≥ |X|`. -/
theorem valKRaw_gameOf_of_subAdaptive (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ)
    (Y : Finset BitString) (x : BitString) (hsa : SubAdaptiveOn c e x) (F : ℕ)
    (hF : (querySet c.toOTM x (clock e x.length) \ Y).card ≤ F) :
    valKRaw (querySet c.toOTM x (clock e x.length) \ Y)
        (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
        (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)).outcome
        (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
        (2 ^ (gameN e T m x.length - m)) F =
      val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)) := by
  obtain ⟨D, hDX, -, hDout, hDP⟩ := exists_pathData c e x T.fn ((2 : ℝ)⁻¹ ^ m)
    (querySet c.toOTM x (clock e x.length) \ Y) Finset.sdiff_subset hsa
  exact D.valKRaw_eq_val hDX hDP (fun S => by rw [hDout]) _ (gameN e T m x.length) _ _ F rfl rfl
    (fun z hz => gameOf_flipCost_eq c e T m Y x z hz) (gameOf_eps_eq c e T m x _) hF

/-- `valKRaw_gameOf_of_subAdaptive` with the fuel `2 ^ (clock e |x| + 1)` of the evaluator. -/
theorem valKRaw_gameOf_of_subAdaptive_clock (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ)
    (Y : Finset BitString) (x : BitString) (hsa : SubAdaptiveOn c e x) :
    valKRaw (querySet c.toOTM x (clock e x.length) \ Y)
        (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
        (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)).outcome
        (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
        (2 ^ (gameN e T m x.length - m)) (2 ^ (clock e x.length + 1)) =
      val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m) (querySet c.toOTM x (clock e x.length) \ Y)) :=
  valKRaw_gameOf_of_subAdaptive c e T m Y x hsa _
    ((Finset.card_le_card Finset.sdiff_subset).trans (card_querySet_lt _ _ _).le)

/-- **Keys of `G_{e,x}` are small**: the target of a key move lies on its own run,
so it has at most `clock e |x|` elements, each of length `≤ clock e |x|`. -/
theorem keyMoveRaw_gameOf_small {c : OTMCode} {e : ℕ} {x : BitString} {h : BitString → ℕ}
    {X K K' : Finset BitString}
    (hK : KeyMoveRaw X (fun S => queries c.toOTM (oracleOf h S) x (clock e x.length)) K K') :
    K'.card ≤ clock e x.length ∧ ∀ z ∈ K', z.length ≤ clock e x.length := by
  obtain ⟨-, h2, -⟩ := hK
  refine ⟨(Finset.card_le_card h2).trans (card_queries_le _ _ _ _), fun z hz => ?_⟩
  obtain ⟨s, hs, hz'⟩ := (mem_queries _ _ x _ z).1 (h2 hz)
  exact (length_le_of_askedAt _ _ x s z hz').trans hs.le

end Kolmogorov.RandomStrings
