/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestTrace

/-!
# Agreement of phase records with dummy allocations

A dictionary indexed by level and candidate records the dummy chosen at phase initialization.
Every active or archived phase and every allocated dummy agrees with this dictionary.
Per-level bounds on candidate timestamps ensure that initialization always inserts a fresh key.
The resulting agreement theorem supplies the phase-separation classification with the output
of any dummy allocation bearing a given phase identity, for blueprint node `constr:separation`.
-/

namespace Kolmogorov.Milovanov

/-- All phase identities have bounded timestamps; active records, archived records, and
allocated dummies agree with the same dictionary of dummy outputs. -/
private abbrev DummyRecordInvariant (b : ℕ → ℕ) (D : ℕ × Candidate → Option BitString)
    (s : FighterState) : Prop :=
  (∀ p ∈ s.active, p.candidate.2 ≤ b p.level ∧ D (p.level, p.candidate) = p.dummy) ∧
  (∀ e ∈ s.ended, e.1.candidate.2 ≤ b e.1.level ∧
    D (e.1.level, e.1.candidate) = e.1.dummy) ∧
  ∀ a ∈ s.allocated, a.candidate.2 ≤ b a.level ∧
    (a.kind = .dummy → D (a.level, a.candidate) = some a.output)

namespace DummyRecordInvariant

variable {P : FighterParams} {d : ℕ}

private lemma mono {b b' : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    {s : FighterState} (hb : ∀ j, b j ≤ b' j) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b' D s := by
  exact ⟨fun p hp ↦ ⟨(hs.1 p hp).1.trans (hb _), (hs.1 p hp).2⟩,
    fun e he ↦ ⟨(hs.2.1 e he).1.trans (hb _), (hs.2.1 e he).2⟩,
    fun a ha ↦ ⟨(hs.2.2 a ha).1.trans (hb _), (hs.2.2 a ha).2⟩⟩

private lemma of_activeAt {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    {s : FighterState} {j : ℕ} {p : FighterPhase}
    (hs : DummyRecordInvariant b D s) (hp : s.activeAt d j = some p) :
    p.candidate.2 ≤ b p.level ∧ D (p.level, p.candidate) = p.dummy :=
  hs.1 p (List.mem_of_find?_eq_some hp)

private lemma putPhase {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (s : FighterState) (p : FighterPhase) (hs : DummyRecordInvariant b D s)
    (hp : p.candidate.2 ≤ b p.level ∧ D (p.level, p.candidate) = p.dummy) :
    DummyRecordInvariant b D (s.putPhase d p) := by
  refine ⟨?_, hs.2⟩
  intro next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp
  · exact hs.1 next (List.mem_filter.mp hn).1

private lemma cancel {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (j cause : ℕ) (reason : PhaseEnd) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · rename_i p hp
    refine ⟨fun q hq ↦ hs.1 q (List.mem_filter.mp hq).1, ?_, hs.2.2⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hs.2.1 e he
    · obtain rfl := List.mem_singleton.mp he
      exact of_activeAt (d := d) (p := p) hs hp

private lemma abortAbove {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (j : ℕ) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D (fighterAbortAbove d j s) := by
  unfold fighterAbortAbove
  apply List.foldlRecOn _ _ hs
  intro t ht p _
  split
  · exact cancel (d := d) _ _ _ _ ht
  · exact ht

private lemma allocate {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (j : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) (hs : DummyRecordInvariant b D s)
    (hout : ∀ p, s.activeAt d j = some p → kind = .dummy → p.dummy = some out) :
    DummyRecordInvariant b D (fighterAllocate d j kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · rename_i p hp
    have hvalid := of_activeAt (d := d) hs hp
    have hlevel : p.level = j := beq_iff_eq.mp
      (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hp)
    cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact cancel (d := d) _ _ _ _ hs
    | some input =>
      apply abortAbove (d := d)
      refine ⟨hs.1, hs.2.1, ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hs.2.2 a ha
      · obtain rfl := List.mem_singleton.mp ha
        refine ⟨by simpa only [hlevel] using hvalid.1, ?_⟩
        intro hk
        simpa only [hlevel] using hvalid.2.trans (hout p hp hk)

private lemma payoff {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l : ℕ) (q : Coordinate) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := allocate (d := d) l .payoff q.2 q.1 s hs (by intro p hp hk; cases hk)
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · refine ⟨?_, ha.2⟩
          intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha.1 old hold
    · exact hs

private lemma fulfillReady {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l : ℕ) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact List.foldlRecOn _ _ hs (fun t ht q _ ↦ payoff (d := d) (P := P) l q t ht)

private lemma fuelUnit {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l : ℕ) (q : Coordinate) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt (d := d) hs hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := allocate (d := d) l .fuel (levelUpper l + d) out (s.putPhase d charged)
        (putPhase (d := d) s charged hs hq) (by intro p hp hk; cases hk)
      change DummyRecordInvariant b D
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
          | (next, success) => if success then
            fighterFulfillReady P d l
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact fulfillReady (d := d) (P := P) l _ (putPhase (d := d) next _ ha hq)
    · exact hs

private lemma fuelUnits {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (fuelUnit (d := d) (P := P) l q s hs)

private lemma dummy {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l : ℕ) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt (d := d) hs hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := allocate (d := d) l .dummy (levelInput d l) output s hs (by
          intro p hp' _
          have heq : p = phase := Option.some.inj (hp'.symm.trans hp)
          simpa only [heq] using hout)
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact putPhase (d := d) next _ ha hq

private lemma opponent {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l : ℕ) (e : ProgramEvent) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt (d := d) hs hp
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact cancel (d := d) _ _ _ _ hs
        · exact fulfillReady (d := d) (P := P) l _ (putPhase (d := d) s _ hs hq)

private lemma startPhase {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (j : ℕ) (c : Candidate) (s : FighterState) (hs : DummyRecordInvariant b D s)
    (hfresh : b j < c.2) :
    ∃ D', DummyRecordInvariant (Function.update b j c.2) D' (fighterStartPhase P d j c s) := by
  let waiting := fighterAbortAbove d j (fighterCancel d j .replaced j s)
  let p := fighter_construction P d j c waiting
  let D' := Function.update D (j, c) p.dummy
  have hw : DummyRecordInvariant b D waiting :=
    abortAbove (d := d) j _ (cancel (d := d) j j .replaced s hs)
  have hne (level : ℕ) (candidate : Candidate) (hbound : candidate.2 ≤ b level) :
      (level, candidate) ≠ (j, c) := by
    intro heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    omega
  have hd : DummyRecordInvariant b D' waiting := by
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      have hq' := hw.1 q hq
      exact ⟨hq'.1, by simpa only [D', Function.update_of_ne (hne _ _ hq'.1)] using hq'.2⟩
    · intro e he
      have he' := hw.2.1 e he
      exact ⟨he'.1, by simpa only [D', Function.update_of_ne (hne _ _ he'.1)] using he'.2⟩
    · intro a ha
      have ha' := hw.2.2 a ha
      exact ⟨ha'.1, by simpa only [D', Function.update_of_ne (hne _ _ ha'.1)] using ha'.2⟩
  have hb : ∀ k, b k ≤ (Function.update b j c.2) k := by
    intro k
    by_cases hk : k = j
    · subst k
      simpa only [Function.update_self] using hfresh.le
    · simp only [Function.update_of_ne hk]
      exact le_rfl
  refine ⟨D', ?_⟩
  change DummyRecordInvariant (Function.update b j c.2) D' (waiting.putPhase d p)
  apply putPhase (d := d) _ _ (mono hb hd)
  constructor
  · simp [p, fighter_construction, FighterPhase.fundRequests]
  · simp [p, D', fighter_construction, FighterPhase.fundRequests]

private lemma flushBuffer {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l : ℕ) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hq := of_activeAt (d := d) hs hp
    simp only [bind, Option.bind_some]
    split
    · exact putPhase (d := d) s _ hs hq
    · exact hs

private lemma strategyMove {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l : ℕ) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D ((fighterStrategyMove P d l s).getD s) := by
  unfold fighterStrategyMove
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact hs
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : DummyRecordInvariant b D next := by
            apply List.foldlRecOn _ _ hs
            intro t ht qi _
            exact fuelUnits (d := d) (P := P) l qi.1 (move[qi.2]?.getD 0) t ht
          change DummyRecordInvariant b D ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            have hq := of_activeAt (d := d) (p := live) hn hlive
            exact putPhase (d := d) next _ hn hq
        · exact hs
    · exact hs

private lemma levelAction {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l : ℕ) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact dummy (d := d) l s hs
    · split
      · exact payoff (d := d) (P := P) l _ s hs
      · cases hf : fighterFlushBuffer d l s with
        | none => exact strategyMove (d := d) (P := P) l s hs
        | some next =>
          have h := flushBuffer (d := d) l s hs
          simpa only [hf, Option.getD_some] using h

private lemma closure {b : ℕ → ℕ} {D : ℕ × Candidate → Option BitString}
    (l fuel : ℕ) (s : FighterState) (hs : DummyRecordInvariant b D s) :
    DummyRecordInvariant b D (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := levelAction (d := d) (P := P) l s hs
      simp only [ha, Option.getD_some] at hn
      exact ih next hn

private lemma processLevel (time j : ℕ) (event : Option TimedEvent)
    (hevent : ∀ e, event = some e → e.1 = time)
    (b : ℕ → ℕ) (D : ℕ × Candidate → Option BitString)
    (s : FighterState) (hs : DummyRecordInvariant b D s) (hfresh : b j < time) :
    ∃ D', DummyRecordInvariant (Function.update b j time) D'
      (fighterProcessLevel P d j event s) := by
  have hb : ∀ k, b k ≤ (Function.update b j time) k := by
    intro k
    by_cases hk : k = j
    · subst k
      simpa only [Function.update_self] using hfresh.le
    · simp only [Function.update_of_ne hk]
      exact le_rfl
  unfold fighterProcessLevel fighterCloseLevel
  cases event with
  | none =>
    exact ⟨D, closure (d := d) (P := P) j _ _ (mono hb (fulfillReady (d := d) (P := P) j s hs))⟩
  | some e =>
    dsimp only
    split
    · obtain ⟨D', hn⟩ := startPhase (d := d) (P := P) j (e.2.2.1, e.1) _
        (fulfillReady (d := d) (P := P) j s hs)
        (by simpa only [hevent e rfl] using hfresh)
      refine ⟨D', ?_⟩
      simpa only [hevent e rfl] using closure (d := d) (P := P) j _ _ hn
    · exact ⟨D, closure (d := d) (P := P) j _ _
        (mono hb (opponent (d := d) (P := P) j _ _
          (fulfillReady (d := d) (P := P) j s hs)))⟩

private lemma processLevels (time : ℕ) (event : Option TimedEvent)
    (hevent : ∀ e, event = some e → e.1 = time) (levels : List ℕ) :
    ∀ (b : ℕ → ℕ) (D : ℕ × Candidate → Option BitString) (s : FighterState),
      levels.Nodup → (∀ k, b k ≤ time) → (∀ k ∈ levels, b k < time) → DummyRecordInvariant b D s →
      ∃ b' D', (∀ k, b' k ≤ time) ∧
        DummyRecordInvariant b' D'
          (levels.foldl (fun s j ↦ fighterProcessLevel P d j event s) s) := by
  induction levels with
  | nil => intro b D s _ hb _ hs; exact ⟨b, D, hb, hs⟩
  | cons j levels ih =>
    intro b D s hn hb hf hs
    obtain ⟨D', hnext⟩ := processLevel (d := d) (P := P) time j event hevent b D s hs
      (hf j List.mem_cons_self)
    have hb' : ∀ k, (Function.update b j time) k ≤ time := by
      intro k
      by_cases hk : k = j
      · subst k; simp only [Function.update_self]; exact le_rfl
      · simpa only [Function.update_of_ne hk] using hb k
    have hf' : ∀ k ∈ levels, (Function.update b j time) k < time := by
      intro k hk
      have hne : k ≠ j := by
        intro heq
        exact (List.nodup_cons.mp hn).1 (heq ▸ hk)
      simpa only [Function.update_of_ne hne] using hf k (List.mem_cons_of_mem j hk)
    exact ih _ D' _ (List.nodup_cons.mp hn).2 hb' hf' hnext

private lemma exists_dictionary (time : ℕ) :
    ∃ D, DummyRecordInvariant (fun _ ↦ time) D (fighterState P d time) := by
  induction time with
  | zero => exact ⟨fun _ ↦ none, by simp [DummyRecordInvariant, fighterState, initialFighterState]⟩
  | succ time ih =>
    obtain ⟨D, hprev⟩ := ih
    change ∃ D, DummyRecordInvariant (fun _ ↦ time + 1) D
      (fighter_actions P d (time + 1) (fighterState P d time))
    unfold fighter_actions
    split
    · exact ⟨fun _ ↦ none, by simp [DummyRecordInvariant, initialFighterState]⟩
    · let current := { fighterState P d time with
        tick := time + 1, schedule := masterState P.B (time + 1) }
      let event := eventAt P.B (time + 1)
      let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
      let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
      have hevent : ∀ e, event = some e → e.1 = time + 1 := by
        intro e he
        exact (canonical_enumeration_spec_sound P.B he).1
      have hn : (levels.mergeSort (· ≤ ·)).Nodup := by
        rw [List.nodup_mergeSort]
        exact nodup_eraseDups_list _
      obtain ⟨b', D', hb', hnext⟩ := processLevels (d := d) (P := P) (time + 1) event hevent
        (levels.mergeSort (· ≤ ·)) (fun _ ↦ time) D current hn (by intro k; omega)
        (by intro k hk; omega) hprev
      exact ⟨D', mono hb' hnext⟩

end DummyRecordInvariant

/-- At a completed tick, every active or archived phase agrees with every allocated dummy
having the same level and candidate. -/
lemma dummy_eq_of_mem_record {P : FighterParams} {d tick : ℕ} {phase : FighterPhase}
    (hphase : phase ∈ (fighterState P d tick).active ∨
      ∃ e ∈ (fighterState P d tick).ended, e.1 = phase)
    {a : AllocatedDirective} (ha : a ∈ (fighterState P d tick).allocated)
    (hkind : a.kind = .dummy) (hsame : a.level = phase.level)
    (hcandidate : a.candidate = phase.candidate) :
    phase.dummy = some a.output := by
  obtain ⟨D, hs⟩ := DummyRecordInvariant.exists_dictionary (P := P) (d := d) tick
  have hp : D (phase.level, phase.candidate) = phase.dummy := by
    rcases hphase with hp | ⟨e, he, rfl⟩
    · exact (hs.1 phase hp).2
    · exact (hs.2.1 e he).2
  have hout := (hs.2.2 a ha).2 hkind
  rw [hsame, hcandidate] at hout
  exact hp.symm.trans hout

end Kolmogorov.Milovanov
