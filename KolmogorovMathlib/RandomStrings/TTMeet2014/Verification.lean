/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Bounded
import KolmogorovMathlib.RandomStrings.TTMeet2014.Effectivity.StateTwin

/-!
# Verification of the construction: Lemma 4.3 (§4.4 of the paper)

## Hypotheses

* `Input.Valid`: both approximations are computable, the opponent's approximation is monotone, and
  the opponent's total spending in true measure is at most `1/32` (`opp_budget`).
* `Approximates I X`: `X_s` converges to `X`.

## Effectivity

The three effectivity theorems below are proved in the Mathlib-only modules
`Effectivity/GameTable.lean` (the value of a game is computable) and
`Effectivity/StateTwin.lean` (a list twin of the construction state, tracked against
`Construction.lean`); see `docs/random_strings_tt_meet_2014.md`, section 8.
`computablePred_of_agreed`, hence `lemma_4_3` and `no_common_reduction`, uses
`agreedBit_computable`.  `realizingF_re` in `Realization.lean` uses `oursB_computable`.
`forces_computable` records the effectivity of the game value in terms of `Arena.Forces`; the other
two use the list form `forcesB_computable` directly, inside `StateTwin.lean`.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

/-! ## Effectivity -/

section Effectivity

variable {I : Input}

/-- **Effectivity of the game.**  The value of a game is computable from its finite description:
tables, unit, target, position and budgets. -/
theorem forces_computable :
    Computable fun p : (List TTable × ℕ) × List (List Bool) × List Str × ℕ × ℕ =>
      decide (Arena.Forces ⟨p.1.1, p.1.2⟩ p.2.1.toFinset p.2.2.1.toFinset p.2.2.2.1 p.2.2.2.2) := by
  exact forcesB_computable

/-- **Effectivity of the construction, output.**  What we enumerate is computable. -/
theorem oursB_computable (hI : I.Valid) (j : Fin 3) :
    Computable fun p : ℕ × Str => oursB I j p.1 p.2 := by
  exact oursB_computable' hI j

/-- **Effectivity of the construction, agreement.**  The agreed value is computable. -/
theorem agreedBit_computable (hI : I.Valid) :
    Computable fun p : ℕ × ℕ × ℕ => agreedBit I p.1 p.2.1 p.2.2 := by
  exact agreedBit_computable' hI

end Effectivity

/-! ## A game that never stops wins -/

section Invariants

variable (I : Input)

/-- **A game that never stops wins.**  If a play of `R_i` runs forever then, the board being finite,
the moves stop, and by the game invariant the final outcomes are on target.  The targets are chosen
so that no vector lies in all of them, so two boards disagree on some table: clause (i) of the
requirement. -/
theorem permanent_disagreement {i : ℕ} (hI : I.Valid) (h : Permanent I i) :
    ∃ k s t j j', tableAt i k s = some t ∧
      ¬ (t.Accepts (finalR I j) ↔ t.Accepts (finalR I j')) := by
  obtain ⟨s₀, start, hperm⟩ := h
  obtain ⟨pl₀, hpl₀, hstart₀⟩ := hperm s₀ le_rfl
  -- From `s₀` on the play keeps its arena, and the boards and targets of its games.
  have hshape : ∀ s ≥ s₀, ∃ pl, (rsAt I s i).play = some pl ∧ pl.start = start ∧
      pl.arena = pl₀.arena ∧ (pl.games.map fun g => (g.board, g.target)) =
        pl₀.games.map fun g => (g.board, g.target) := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact ⟨pl₀, hpl₀, hstart₀, rfl, rfl⟩
    | succ s hle ih =>
      obtain ⟨pl, hpl, hst, har, hmap⟩ := ih
      obtain ⟨pl', hpl', hst'⟩ := hperm (s + 1) (by omega)
      by_cases hi : i = (Nat.unpair s).1
      · subst hi
        obtain ⟨hres, hl⟩ := visit_of_permanent hI hpl hpl' (by rw [hst, hst'])
        refine ⟨pl', hpl', hst', ?_⟩
        obtain ⟨c, hc, -, -⟩ := (reqWF_rsAt I s _).play pl hpl
        have heq := play_after_limit hres hc hpl hl
        rw [hpl'] at heq
        cases heq
        refine ⟨har, ?_⟩
        rw [← hmap]
        simp only [List.map_map]
        rfl
      · rw [rsAt_succ_of_ne I hi]
        exact ⟨pl, hpl, hst, har, hmap⟩
  obtain ⟨s₁, hs₁, hstable⟩ := exists_stable_position hI pl₀.arena s₀
  -- A late visit.
  obtain ⟨s, hs, hsi⟩ := exists_stage_ge i s₁
  obtain ⟨pl, hpl, hst, har, hmap⟩ := hshape s (hs₁.trans hs)
  obtain ⟨pl', hpl', hst', -, -⟩ := hshape (s + 1) (by omega)
  subst hsi
  obtain ⟨hres, hl⟩ := visit_of_permanent hI hpl hpl' (by rw [hst, hst'])
  have hstable' : ∀ t ≥ s₁, ∀ j, (stateAt I t).position I pl.arena t j =
      (stateAt I s₁).position I pl.arena s₁ j := by
    rw [har]
    exact hstable
  have hon : ∀ g ∈ pl.games,
      pl.arena.value ((stateAt I s₁).position I pl.arena s₁ g.board) ∈ g.target :=
    fun g hg => (target_of_stable hI hs hstable' hres hpl hl hg).2
  by_contra hcon
  -- All values agree, so one vector is on target in all games.
  have hagree : ∀ j j', pl.arena.value ((stateAt I s₁).position I pl.arena s₁ j) =
      pl.arena.value ((stateAt I s₁).position I pl.arena s₁ j') := by
    intro j j'
    refine List.map_congr_left fun tt htt => ?_
    rw [value_stable_eq hI (fun t ht => hstable' t ht j) htt,
      value_stable_eq hI (fun t ht => hstable' t ht j') htt]
    by_contra hne
    apply hcon
    obtain ⟨c, hc, ha, -⟩ := (reqWF_rsAt I s _).play pl hpl
    have htt' : tt ∈ (rsAt I s (Nat.unpair s).1).tables := by
      rw [ha] at htt
      exact htt
    obtain ⟨k, hk⟩ := mem_tablesUpTo (reqWF_rsAt I s _).tables tt htt'
    refine ⟨k, s, tt, j, j', hk, fun hiff => hne ?_⟩
    exact Bool.eq_iff_iff.2 hiff
  refine (run_invariant hI s _).incompat pl hpl
    ⟨pl.arena.value ((stateAt I s₁).position I pl.arena s₁ 0), fun g hg => ?_⟩
  rw [hagree 0 g.board]
  exact hon g hg

end Invariants

/-! ## Lemma 4.3: finite injury -/

section FiniteInjury

variable {I : Input} {X : Set Str}

/-- A hit is monotone in the stage of the opponent's approximation. -/
theorem pendingHit_mono (hI : I.Valid) {rs : ReqState} {t t' : ℕ} (ht : t ≤ t')
    (h : pendingHit I rs t = true) : pendingHit I rs t' = true := by
  simp only [pendingHit, decide_eq_true_eq] at h ⊢
  obtain ⟨τ, hτ⟩ := h
  refine ⟨τ, ?_⟩
  simp only [mem_filter, Bool.and_eq_true] at hτ ⊢
  exact ⟨hτ.1, hI.opp_mono ht hτ.2.1, hτ.2.2⟩

/-- A uniform bound on the last actions of finitely many requirements. -/
theorem exists_bound_of_stops {i : ℕ} (h : ∀ m < i, StopsActing I m) :
    ∃ S, ∀ m < i, ∀ s, (rsAt I s m).lastActed ≤ S := by
  induction i with
  | zero => exact ⟨0, fun m hm => absurd hm (by omega)⟩
  | succ i ih =>
    obtain ⟨S, hS⟩ := ih fun m hm => h m (by omega)
    obtain ⟨S', hS'⟩ := h i (by omega)
    refine ⟨max S S', fun m hm s => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hlt | rfl
    · exact (hS m hlt s).trans (le_max_left _ _)
    · exact (hS' s).trans (le_max_right _ _)

/-- **Lemma 4.3, first step.**  When the higher-priority requirements have stopped acting, `ε_i`
settles: Case 1 applies only finitely often. -/
theorem eps_settles (hI : I.Valid) {i : ℕ} (h : ∀ m < i, StopsActing I m) :
    ∃ s₀ c, NoReset I i s₀ ∧ ∀ s ≥ s₀, (rsAt I s i).c = some c := by
  obtain ⟨S, hS⟩ := exists_bound_of_stops h
  -- A stage of `R_i` after the first one and after the last action above it.
  let v := Nat.pair i (max (S + 1) (Nat.pair i 0 + 1))
  have hvi : (Nat.unpair v).1 = i := by simp [v]
  have hvS : S < v := by
    have h1 : max (S + 1) (Nat.pair i 0 + 1) ≤ v := Nat.right_le_pair _ _
    have h2 : S + 1 ≤ max (S + 1) (Nat.pair i 0 + 1) := le_max_left _ _
    omega
  have hv0 : Nat.pair i 0 < v := by
    have h1 : max (S + 1) (Nat.pair i 0 + 1) ≤ v := Nat.right_le_pair _ _
    have h2 : Nat.pair i 0 + 1 ≤ max (S + 1) (Nat.pair i 0 + 1) := le_max_right _ _
    omega
  have hsome : ∀ s ≥ v + 1, (rsAt I s i).c.isSome = true := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      have := c_isSome_after_visit I v
      rwa [hvi] at this
    | succ s hle ih =>
      by_cases hi : i = (Nat.unpair s).1
      · subst hi
        exact c_isSome_after_visit I s
      · rwa [rsAt_succ_of_ne I hi]
  have hno : NoReset I i (v + 1) := by
    intro s hs hsi
    simp only [mustReset, Bool.or_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false,
      List.mem_range]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro he
      have : s = Nat.pair i 0 := by
        have := Nat.pair_unpair s
        rw [hsi, he] at this
        exact this.symm
      omega
    · have := hsome s hs
      change (rsAt I s i).c.isNone = false
      rw [Option.isNone_eq_false_iff]
      exact this
    · intro m hm hbad
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hbad
      rcases hbad with hact | hhit
      · have h1 : (rsAt I (v + 1) i).lastVisit ≤ (rsAt I s i).lastVisit := lastVisit_mono I i hs
        have h2 : (rsAt I (v + 1) i).lastVisit = v + 1 := by
          have := lastVisit_self I v
          rwa [hvi] at this
        have h3 := hS m hm s
        change (rsAt I s i).lastVisit < (rsAt I s m).lastActed at hact
        omega
      · -- The next stage of `R_m` would be an action.
        classical
        have hex : ∃ u, s ≤ u ∧ (Nat.unpair u).1 = m := by
          obtain ⟨u, hu, hum⟩ := exists_stage_ge m s
          exact ⟨u, hu, hum⟩
        let u := Nat.find hex
        have hu := Nat.find_spec hex
        have hmin : ∀ s'', s ≤ s'' → s'' < u → (Nat.unpair s'').1 ≠ m := fun s'' h1 h2 h3 =>
          Nat.find_min hex h2 ⟨h1, h3⟩
        have hconst := rsAt_const I hu.1 hmin
        have hhit' : pendingHit I (rsAt I u m) (u + 1) = true := by
          rw [hconst]
          exact pendingHit_mono hI (by have := hu.1; omega) hhit
        have hact := lastActed_of_hit I (s := u) (by rw [hu.2]; exact hhit')
        rw [hu.2] at hact
        have hb := hS m hm (u + 1)
        have := hu.1
        omega
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hsome (v + 1) le_rfl)
  refine ⟨v + 1, c, hno, fun s hs => ?_⟩
  induction s, hs using Nat.le_induction with
  | base => exact hc
  | succ s hle ih =>
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      rw [rsAt_succ_self]
      change (stepCore I (stateAt I s)).1.c = _
      have hr := hno s hle rfl
      have hr' : mustReset I (stateAt I s) (Nat.unpair (stateAt I s).stage).1
          (Nat.unpair (stateAt I s).stage).2 ((stateAt I s).stage + 1) = false := by
        rw [stage_stateAt]
        exact hr
      rw [stepCore_c_of_no_reset hr', stage_stateAt]
      exact ih
    · rw [rsAt_succ_of_ne I hi]
      exact ih

/-- **Comparison with `X_s`.**  A new bit is examined only when the agreed value agrees with `X_t`
on the old bits. -/
theorem extension_matches {s i : ℕ} {bl : Baseline}
    (hgrow : (rsAt I s i).tables.length < (rsAt I (s + 1) i).tables.length)
    (hbl : (rsAt I (s + 1) i).baseline = some bl) :
    xPrefix I (s + 1) (rsAt I s i).tables.length = bl.σ.take (rsAt I s i).tables.length := by
  by_cases hi : i = (Nat.unpair s).1
  · subst hi
    have hw := (reqWF_rsAt I s (Nat.unpair s).1).mono (Nat.le_succ s)
    rw [rsAt_succ_self] at hgrow hbl
    have h := stepCore_extension (I := I) (st := stateAt I s)
      (by rw [stage_stateAt]; exact hw) (by rw [stage_stateAt]; exact hgrow)
      (by exact hbl)
    rw [stage_stateAt] at h
    exact h
  · rw [rsAt_succ_of_ne I hi] at hgrow
    exact absurd hgrow (lt_irrefl _)

/-- A game running forever means that the number of bits is bounded. -/
theorem not_permanent_of_unbounded {i : ℕ} (hu : Unbounded I i) : ¬ Permanent I i := by
  intro hp
  obtain ⟨s₀, hs⟩ := tables_const_of_permanent I hp
  obtain ⟨s, hs'⟩ := hu ((rsAt I s₀ i).tables.length + 1)
  rcases le_total s s₀ with hle | hle
  · have := (tables_prefix I i hle).length_le
    omega
  · rw [hs s hle] at hs'
    omega

/-- **The first `σ` after the protected stage is correct.**  If the examined bits are unbounded, the
agreed values converge, and to `X`: the proof uses `agreed_nested` and compares with `X_s` at the
late stages at which new bits are examined (`extension_matches`). -/
theorem agreed_value_correct (hI : I.Valid) (hX : Approximates I X) {i s₀ c : ℕ}
    (hno : NoReset I i s₀) (hc : ∀ s ≥ s₀, (rsAt I s i).c = some c) (hu : Unbounded I i) :
    ∃ s₂, (∀ s ≥ s₂, ∀ k b, agreedBit I i s k = some b → (b = true ↔ strOf k ∈ X)) ∧
      ∀ k, ∃ s ≥ s₂, (agreedBit I i s k).isSome = true := by
  have hnp := not_permanent_of_unbounded hu
  obtain ⟨s₂, hs₂, hprot⟩ := (exists_protected_or_permanent hI hno hc).resolve_left hnp
  obtain ⟨hsome, hnest⟩ := agreed_nested hI hno hc hs₂ hprot hnp
  -- Every length is reached at or after any given stage.
  have hlate : ∀ m N : ℕ, ∃ s ≥ m, N ≤ (rsAt I s i).tables.length := by
    intro m N
    obtain ⟨s, hs⟩ := hu N
    refine ⟨max m s, le_max_left _ _, hs.trans ?_⟩
    exact (tables_prefix I i (le_max_right m s)).length_le
  refine ⟨s₂, fun s hs k b hb => ?_, fun k => ?_⟩
  · -- Compare at a late stage that adds a bit above `k`.
    obtain ⟨bl₁, hbl₁, hb₁⟩ := Option.bind_eq_some_iff.1 hb
    obtain ⟨s_x, hs_x⟩ := hX (strOf k)
    set m := max s s_x with hm
    set N := max (rsAt I m i).tables.length (k + 1) + 1 with hN
    obtain ⟨sL, -, hlen⟩ := hlate m N
    classical
    have hex : ∃ u, N ≤ (rsAt I u i).tables.length := ⟨sL, hlen⟩
    let u := Nat.find hex
    have hu' : N ≤ (rsAt I u i).tables.length := Nat.find_spec hex
    have hu0 : u ≠ 0 := by
      intro h0
      have h1 : (rsAt I 0 i).tables.length = 0 := rfl
      rw [show u = 0 from h0, h1] at hu'
      omega
    obtain ⟨u', huu⟩ := Nat.exists_eq_succ_of_ne_zero hu0
    have hmin : (rsAt I u' i).tables.length < N := by
      by_contra hcon
      exact Nat.find_min hex (show u' < u by omega) (not_lt.1 hcon)
    have huN : (rsAt I (u' + 1) i).tables.length = N ∧ (rsAt I u' i).tables.length + 1 = N := by
      have h2 : N ≤ (rsAt I (u' + 1) i).tables.length := by
        have : u = u' + 1 := huu
        rw [← this]
        exact hu'
      rcases tables_step I u' i with h3 | ⟨tbl, h3⟩
      · rw [h3] at h2
        omega
      · rw [h3, List.length_append, List.length_singleton] at h2 ⊢
        omega
    have hmu : m ≤ u' := by
      by_contra hcon
      have h4 := (tables_prefix I i (show u' + 1 ≤ m by omega)).length_le
      have h5 : (rsAt I m i).tables.length + 1 ≤ N := by
        simp only [hN]
        exact Nat.add_le_add_right (le_max_left _ _) 1
      omega
    have hsu : s ≤ u' + 1 := by
      have : s ≤ m := le_max_left _ _
      omega
    have hs2u : s₂ ≤ u' + 1 := hs.trans hsu
    obtain ⟨bl₂, hbl₂⟩ := Option.isSome_iff_exists.1 (hsome (u' + 1) hs2u)
    have hgrow : (rsAt I u' i).tables.length < (rsAt I (u' + 1) i).tables.length := by
      omega
    have hmatch := extension_matches (I := I) hgrow hbl₂
    have hpre := hnest s (u' + 1) bl₁ bl₂ hs hsu hbl₁ hbl₂
    have hk : k < (rsAt I u' i).tables.length := by
      have h6 : k + 1 ≤ max (rsAt I m i).tables.length (k + 1) := le_max_right _ _
      omega
    have hb₂ : bl₂.σ[k]? = some b := by
      obtain ⟨tl, htl⟩ := hpre
      have hlt : k < bl₁.σ.length := by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hb₁
        exact hlt
      rw [← htl, List.getElem?_append_left hlt]
      exact hb₁
    have hval : I.X (u' + 1) (strOf k) = b := by
      have h7 := congrArg (fun l => l[k]?) hmatch
      simp only [xPrefix] at h7
      rw [List.getElem?_map, List.getElem?_range hk, List.getElem?_take_of_lt hk, hb₂] at h7
      simpa using h7
    have hxs : s_x ≤ u' + 1 := by
      have : s_x ≤ m := le_max_right _ _
      omega
    rw [← hval]
    exact hs_x (u' + 1) hxs
  · obtain ⟨s, hs, hlen⟩ := hlate s₂ (k + 1)
    refine ⟨s, hs, ?_⟩
    obtain ⟨bl, hbl⟩ := Option.isSome_iff_exists.1 (hsome s hs)
    have hl := baseline_length I hbl
    have hk : k < bl.σ.length := by omega
    change (((stateAt I s).req i).baseline.bind fun bl => bl.σ[k]?).isSome = true
    have hbl' : ((stateAt I s).req i).baseline = some bl := hbl
    rw [hbl', Option.bind_some, List.getElem?_eq_getElem hk]
    rfl

/-- **Computability from the agreement (end of the proof of Lemma 4.3).**  To decide `x ∈ X`, run
the construction past `s₂` until the bit of `x` is agreed on. -/
theorem computablePred_of_agreed (hI : I.Valid) {i s₂ : ℕ}
    (h : (∀ s ≥ s₂, ∀ k b, agreedBit I i s k = some b → (b = true ↔ strOf k ∈ X)) ∧
      ∀ k, ∃ s ≥ s₂, (agreedBit I i s k).isSome = true) :
    ComputablePred fun x => x ∈ X := by
  classical
  obtain ⟨hcorrect, hex⟩ := h
  have hcomp := agreedBit_computable hI
  have hg : Computable fun p : Str × ℕ => agreedBit I i (s₂ + p.2) (Encodable.encode p.1) :=
    hcomp.comp ((Computable.const i).pair
      ((Primrec.nat_add.to_comp.comp (Computable.const s₂) Computable.snd).pair
        (Computable.encode.comp Computable.fst)))
  have hsearch : Partrec fun x : Str =>
      Nat.rfind fun n => Part.some (agreedBit I i (s₂ + n) (Encodable.encode x)).isSome := by
    refine Partrec.rfind ?_
    exact (Computable.to₂ (Primrec.option_isSome.to_comp.comp hg)).partrec₂
  have hread : Partrec fun x : Str =>
      (Nat.rfind fun n => Part.some (agreedBit I i (s₂ + n) (Encodable.encode x)).isSome).map
        fun n => (agreedBit I i (s₂ + n) (Encodable.encode x)).getD false := by
    refine hsearch.map ?_
    have hg' : Computable fun p : Str × ℕ =>
        (agreedBit I i (s₂ + p.2) (Encodable.encode p.1)).getD false :=
      Primrec.option_getD.to_comp.comp hg (Computable.const false)
    exact hg'.to₂
  have htot : ∀ x : Str, decide (x ∈ X) ∈
      (Nat.rfind fun n => Part.some (agreedBit I i (s₂ + n) (Encodable.encode x)).isSome).map
        fun n => (agreedBit I i (s₂ + n) (Encodable.encode x)).getD false := by
    intro x
    obtain ⟨s, hs, hsome⟩ := hex (Encodable.encode x)
    have hm : (fun n => (agreedBit I i (s₂ + n) (Encodable.encode x)).isSome) (s - s₂) = true := by
      simp only [show s₂ + (s - s₂) = s by omega]
      exact hsome
    obtain ⟨n, hn, -⟩ := Nat.rfind_min'
      (p := fun n => (agreedBit I i (s₂ + n) (Encodable.encode x)).isSome) hm
    refine (Part.mem_map_iff _).2 ⟨n, hn, ?_⟩
    have hspec : true ∈ Part.some (agreedBit I i (s₂ + n) (Encodable.encode x)).isSome :=
      Nat.rfind_spec hn
    have hisSome : (agreedBit I i (s₂ + n) (Encodable.encode x)).isSome = true :=
      (Part.mem_some_iff.1 hspec).symm
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hisSome
    have hval := hcorrect (s₂ + n) (Nat.le_add_right _ _) _ b hb
    rw [strOf_encode] at hval
    rw [hb, Option.getD_some]
    cases b
    · simp only [Bool.false_eq_true, false_iff] at hval
      simp [hval]
    · simp only [true_iff] at hval
      simp [hval]
  exact ComputablePred.computable_iff.2 ⟨fun x => decide (x ∈ X), hread.of_eq_tot htot, by
    funext x
    simp⟩

/-- **Lemma 4.3.**  Every requirement `R_i` eventually stops acting and is satisfied. -/
theorem lemma_4_3 (hI : I.Valid) (hX : Approximates I X) (hnc : ¬ ComputablePred fun x => x ∈ X) :
    ∀ i, StopsActing I i ∧ ReqSatisfied I X i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    obtain ⟨s₀, c, hno, hc⟩ := eps_settles hI fun m hm => (ih m hm).1
    have hbounded : ∃ N, ∀ s, (rsAt I s i).tables.length ≤ N := by
      by_contra hcon
      have hu : Unbounded I i := by
        intro N
        by_contra hN
        exact hcon ⟨N, fun s => by
          by_contra hs
          exact hN ⟨s, by omega⟩⟩
      exact hnc (computablePred_of_agreed hI (agreed_value_correct hI hX hno hc hu).choose_spec)
    obtain ⟨N, hN⟩ := hbounded
    refine ⟨stopsActing_of_bounded hI hno hc hN, ?_⟩
    by_cases hp : Permanent I i
    · exact Or.inr (Or.inl (permanent_disagreement I hI hp))
    · rcases satisfied_of_bounded hI hX hno hc hN hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- **No common reduction.**  No single total computable generator computes `X` from all three final
oracles. -/
theorem no_common_reduction (hI : I.Valid) (hX : Approximates I X)
    (hnc : ¬ ComputablePred fun x => x ∈ X) :
    ¬ ∃ g : Str → TTable, Computable g ∧ ∀ j, IsTTReduction g X (finalR I j) := by
  rintro ⟨g, hg, hgj⟩
  obtain ⟨i, hi⟩ := exists_index hg
  rcases (lemma_4_3 hI hX hnc i).2 with hnt | ⟨k, s, t, j, j', ht, hne⟩ | ⟨k, s, t, j, ht, hne⟩
  · refine hnt fun k => ?_
    obtain ⟨s, hs⟩ := (hi k).1
    exact ⟨s, _, hs⟩
  · have htg := (hi k).2 s t ht
    subst htg
    exact hne (((hgj j _).symm).trans (hgj j' _))
  · have htg := (hi k).2 s t ht
    subst htg
    exact hne (hgj j _)

end FiniteInjury

end Kolmogorov.RandomStrings.TTMeet
