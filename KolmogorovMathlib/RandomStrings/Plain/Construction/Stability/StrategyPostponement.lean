/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting
import KolmogorovMathlib.RandomStrings.Plain.Construction.Actions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective
import KolmogorovMathlib.RandomStrings.Plain.Construction.Referees
import KolmogorovMathlib.RandomStrings.Plain.Construction.State
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.AllocationOccupancy
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame
import KolmogorovMathlib.RandomStrings.Plain.Markers
import Mathlib.Data.Nat.Sqrt

/-!
# Postponing a payoff does not hide a fighter failure

In the stability analysis of the fighter strategy, a failed controlled response must survive one
preceding level action (a dummy request or the payoff of a ready request).  The proof compares
the state `s` in which the action was performed immediately with the state `t` in which it is
postponed.

* `prepaidRequests s t r` collects the requests of target `r` that are already fulfilled in the
  postponed run `t` but not yet in the immediate run `s`.
* `postponedComparison d l s t` states that, apart from the pending requests and the dummy flag,
  the local phase data of the two runs agree, every extra fulfillment of `t` is backed by one
  extra occupied input of its target length, and any further occupied input only reduces the
  free capacity of `t`.  It is preserved by dummy requests, payoffs, ready folds and fuel units
  (`postponedComparison_dummy`, `postponedComparison_fulfillReady`,
  `postponedComparison_fuelUnits_fold`).
* `failed_response_survives_level_action` is the resulting theorem, used by `StrategyClosure`.

The allocator facts used here live in `AllocationOccupancy`.
-/

namespace Kolmogorov.Milovanov

/-- The finite set of requests of target `r` already fulfilled in the postponed run but still
unfulfilled in the immediate run. -/
private def prepaidRequests (s t : FighterState) (r : ℕ) : Finset Coordinate :=
  (t.fulfilled.toFinset \ s.fulfilled.toFinset).filter (fun q ↦ q.2 = r)

/-- The postponed run has the same local phase data except pending requests and the dummy flag.
Each additional fulfillment is backed by one additional occupied input of its target length;
any further occupied inputs only reduce available capacity. An already failed postponed run
needs no comparison. -/
private def postponedComparison (d l : ℕ) (s t : FighterState) : Prop :=
  t.failed = true ∨
    s.failed = false ∧ t.failed = false ∧ s.tick = t.tick ∧
      ∃ p pending issued,
        s.activeAt d l = some p ∧
        t.activeAt d l = some { p with pending := pending, dummyIssued := issued } ∧
        s.fulfilled.toFinset ⊆ t.fulfilled.toFinset ∧
        p.pending.toFinset ∪ s.fulfilled.toFinset =
          pending.toFinset ∪ t.fulfilled.toFinset ∧
        ∀ r, (occupiedInputs s r).card + (prepaidRequests s t r).card ≤
          (occupiedInputs t r).card

/-- Payoffs, their ready fold, and individual fuel units preserve an already set failure
flag. -/
private lemma failed_persists_payoff_fulfillReady_fuelUnit (P : FighterParams) (d l : ℕ) :
    (∀ q s, s.failed = true → (fighterPayoff P d l q s).failed = true) ∧
    (∀ s, s.failed = true → (fighterFulfillReady P d l s).failed = true) ∧
    (∀ q s, s.failed = true → (fighterFuelUnit P d l q s).failed = true) := by
  have hpay (q : Coordinate) (s : FighterState) (hs : s.failed = true) :
      (fighterPayoff P d l q s).failed = true := by
    unfold fighterPayoff
    split
    · exact hs
    · split
      · have ha := fighterAllocate_failed_of_failed d l q.2 .payoff q.1 s hs
        cases he : fighterAllocate d l .payoff q.2 q.1 s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> exact ha
      · exact hs
  have hfulfill (s : FighterState) (hs : s.failed = true) :
      (fighterFulfillReady P d l s).failed = true := by
    have hfold (qs : List Coordinate) (s : FighterState) (hs : s.failed = true) :
        (qs.foldl (fun s q ↦ fighterPayoff P d l q s) s).failed = true := by
      induction qs generalizing s with
      | nil => exact hs
      | cons q qs ih => exact ih _ (hpay q s hs)
    unfold fighterFulfillReady
    split
    · exact hs
    · exact hfold _ _ hs
  refine ⟨hpay, hfulfill, ?_⟩
  intro q s hs
  unfold fighterFuelUnit
  split
  · exact hs
  · split
    · rename_i p hp henabled
      let charged := { p with controlledRemaining := p.controlledRemaining - 1 }
      let index := fighterFreshString d (p.indices[(p.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) p.candidate.1) index
      have ha := fighterAllocate_failed_of_failed d l (levelUpper l + d) .fuel out
        (s.putPhase d charged) hs
      change (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
        | (next, success) => if success then fighterFulfillReady P d l
            (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
          else next).failed = true
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact hfulfill _ ha
    · exact hs

/-- An additional fulfillment in the postponed run adds exactly one prepaid request at its
target. -/
private lemma card_prepaidRequests_append_postponed
    (s t u : FighterState) (q : Coordinate)
    (hf : u.fulfilled = t.fulfilled ++ [q])
    (hsub : s.fulfilled.toFinset ⊆ t.fulfilled.toFinset)
    (hq : q ∉ t.fulfilled) (r : ℕ) :
    (prepaidRequests s u r).card =
      (prepaidRequests s t r).card + if q.2 = r then 1 else 0 := by
  have hqs : q ∉ s.fulfilled := fun h ↦ hq (List.mem_toFinset.mp (hsub (by simpa using h)))
  have hnot : q ∉ prepaidRequests s t r := by simp [prepaidRequests, hq]
  have heq : prepaidRequests s u r =
      if q.2 = r then insert q (prepaidRequests s t r) else prepaidRequests s t r := by
    ext x
    by_cases h : q.2 = r <;> simp [prepaidRequests, hf, h] <;> aesop
  rw [heq]
  split
  · rw [Finset.card_insert_of_notMem hnot]
  · simp

/-- Fulfilling an already prepaid request in the immediate run removes precisely its one unit of
credit. -/
private lemma card_prepaidRequests_append_immediate
    (s t u : FighterState) (q : Coordinate)
    (hf : u.fulfilled = s.fulfilled ++ [q])
    (hq : q ∈ t.fulfilled) (hqs : q ∉ s.fulfilled) (r : ℕ) :
    (prepaidRequests u t r).card + (if q.2 = r then 1 else 0) =
      (prepaidRequests s t r).card := by
  have heq : prepaidRequests u t r = (prepaidRequests s t r).erase q := by
    ext x
    simp [prepaidRequests, hf]
    aesop
  rw [heq]
  by_cases h : q.2 = r
  · have hmem : q ∈ prepaidRequests s t r := by simp [prepaidRequests, hq, hqs, h]
    simpa only [h, ite_true] using Finset.card_erase_add_one hmem
  · have hnot : q ∉ prepaidRequests s t r := by simp [prepaidRequests, h]
    simp [h, hnot]

/-- Recording a pending payoff and filtering that pair from the pending list preserves the union
of pending and fulfilled pairs. -/
private lemma pending_union_filter_append
    (pending fulfilled : List Coordinate) (q : Coordinate)
    (hq : q ∈ pending) :
    (pending.filter (· != q)).toFinset ∪ (fulfilled ++ [q]).toFinset =
      pending.toFinset ∪ fulfilled.toFinset := by
  ext x
  by_cases hx : x = q <;> simp [hx, hq]

/-- Every active state compares to itself, including states whose failure flag is already
set. -/
private lemma postponedComparison_refl
    (d l : ℕ) (s : FighterState) (p : FighterPhase)
    (hp : s.activeAt d l = some p) : postponedComparison d l s s := by
  cases hf : s.failed with
  | true => exact Or.inl hf
  | false =>
    right
    refine ⟨hf, hf, rfl, p, p.pending, p.dummyIssued, hp, hp, Finset.Subset.refl _, rfl, ?_⟩
    intro r
    simp [prepaidRequests]

/-- A payoff in the postponed run preserves comparison: its occupied input pays for the new
fulfillment credit. -/
private lemma postponedComparison_payoff_postponed
    (P : FighterParams) (d l : ℕ) (s t : FighterState)
    (hrel : postponedComparison d l s t) (q : Coordinate) :
    postponedComparison d l s (fighterPayoff P d l q t) := by
  rcases hrel with htf | ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩
  · exact Or.inl ((failed_persists_payoff_fulfillReady_fuelUnit P d l).1 q t htf)
  · simp only [fighterPayoff, htp]
    by_cases henabled : q ∈ pending ∧ q ∉ t.fulfilled ∧ fighterSafe P d t.tick q = true
    · rw [ite_eq_left henabled]
      have ha := fighterAllocate_spec d l q.2 .payoff q.1 t
        { p with pending := pending, dummyIssued := issued } htp
      cases he : fighterAllocate d l .payoff q.2 q.1 t with
      | mk u success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact Or.inl (ha.1 rfl).1
        · obtain ⟨input, hlen, hfresh, halloc, hutick, huf, hufailed, hup⟩ := ha.2 rfl
          let v : FighterState :=
            { u with
              fulfilled := u.fulfilled ++ [q]
              active := u.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) }
          have hvp : v.activeAt d l =
              some { p with pending := pending.filter (· != q), dummyIssued := issued } := by
            simp only [v, FighterState.activeAt, List.find?_map]
            change (u.activeAt d l).map _ = _
            rw [hup]
            rfl
          right
          refine ⟨hsf, hufailed.trans htf, htick.trans hutick.symm,
            p, pending.filter (· != q), issued, hsp, hvp, ?_, ?_, ?_⟩
          · intro x hx
            change x ∈ (u.fulfilled ++ [q]).toFinset
            rw [huf]
            exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (hsub hx)))
          · change _ = _ ∪ (u.fulfilled ++ [q]).toFinset
            rw [huf, pending_union_filter_append pending t.fulfilled q henabled.1]
            exact hpend
          · intro r
            have hoc := card_occupiedInputs_append t v
              ⟨l, p.candidate, t.tick, .payoff, q.2, input, q.1⟩ halloc hfresh r
            have hcr := card_prepaidRequests_append_postponed s t v q
              (by change u.fulfilled ++ [q] = _; rw [huf]) hsub henabled.2.1 r
            simp only [hlen] at hoc
            change (occupiedInputs s r).card + (prepaidRequests s v r).card ≤
              (occupiedInputs v r).card
            rw [hoc, hcr]
            have hc := hcount r
            omega
    · rw [ite_eq_right henabled]
      exact Or.inr ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩

/-- Once the postponed run has no safe unfulfilled pending requests, every enabled immediate
payoff is prepaid. Its credit guarantees a positive target and a free input, and successful
payment consumes exactly that credit. -/
private lemma postponedComparison_payoff_immediate
    (P : FighterParams) (d l : ℕ) (s t : FighterState)
    (hrel : postponedComparison d l s t)
    (hquiet : ∀ p, t.activeAt d l = some p → ∀ q ∈ p.pending,
      q ∈ t.fulfilled ∨ fighterSafe P d t.tick q = false) (q : Coordinate) :
    postponedComparison d l (fighterPayoff P d l q s) t := by
  rcases hrel with htf | ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩
  · exact Or.inl htf
  · simp only [fighterPayoff, hsp]
    by_cases henabled : q ∈ p.pending ∧ q ∉ s.fulfilled ∧ fighterSafe P d s.tick q = true
    · rw [ite_eq_left henabled]
      have hqt : q ∈ t.fulfilled := by
        have hmem : q ∈ pending.toFinset ∪ t.fulfilled.toFinset := by
          rw [← hpend]
          exact Finset.mem_union_left _ (by simpa using henabled.1)
        rcases Finset.mem_union.mp hmem with hmem | hmem
        · rcases hquiet _ htp q (List.mem_toFinset.mp hmem) with h | h
          · exact h
          · rw [← htick, henabled.2.2] at h
            cases h
        · exact List.mem_toFinset.mp hmem
      have hcredit : q ∈ prepaidRequests s t q.2 := by
        simp [prepaidRequests, hqt, henabled.2.1]
      have hcreditpos := Finset.card_pos.mpr ⟨q, hcredit⟩
      have hc := hcount q.2
      have hocpos : 0 < (occupiedInputs t q.2).card := by omega
      obtain ⟨input, hinput⟩ := Finset.card_pos.mp hocpos
      have hlen := (Finset.mem_filter.mp hinput).2
      have hr : 0 < q.2 := by omega
      have hpool := Finset.card_le_card (occupiedInputs_subset_fighterInputs d q.2 t hr)
      have hsuccess := fighterAllocate_success_of_card_lt d l q.2 .payoff q.1 s p hsp hr
        (by omega)
      have ha := (fighterAllocate_spec d l q.2 .payoff q.1 s p hsp).2 hsuccess
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk u success =>
        rw [he] at hsuccess ha
        cases success
        · cases hsuccess
        · simp only [ite_true]
          obtain ⟨input, hlen, hfresh, halloc, hutick, huf, hufailed, hup⟩ := ha
          let v : FighterState :=
            { u with
              fulfilled := u.fulfilled ++ [q]
              active := u.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) }
          have hvp : v.activeAt d l = some { p with pending := p.pending.filter (· != q) } := by
            simp only [v, FighterState.activeAt, List.find?_map]
            change (u.activeAt d l).map _ = _
            rw [hup]
            rfl
          right
          refine ⟨hufailed.trans hsf, htf, hutick.trans htick,
            { p with pending := p.pending.filter (· != q) }, pending, issued, hvp, htp,
            ?_, ?_, ?_⟩
          · intro x hx
            change x ∈ (u.fulfilled ++ [q]).toFinset at hx
            rw [huf] at hx
            rcases List.mem_append.mp (List.mem_toFinset.mp hx) with h | h
            · exact hsub (List.mem_toFinset.mpr h)
            · have hxq := List.mem_singleton.mp h
              subst x
              exact List.mem_toFinset.mpr hqt
          · change (p.pending.filter (· != q)).toFinset ∪ (u.fulfilled ++ [q]).toFinset = _
            rw [huf, pending_union_filter_append p.pending s.fulfilled q henabled.1]
            exact hpend
          · intro r
            have hoc := card_occupiedInputs_append s v
              ⟨l, p.candidate, s.tick, .payoff, q.2, input, q.1⟩ halloc hfresh r
            have hcr := card_prepaidRequests_append_immediate s t v q
              (by change u.fulfilled ++ [q] = _; rw [huf]) hqt henabled.2.1 r
            simp only [hlen] at hoc
            change (occupiedInputs v r).card + (prepaidRequests v t r).card ≤
              (occupiedInputs t r).card
            rw [hoc]
            have hc := hcount r
            omega
    · rw [ite_eq_right henabled]
      exact Or.inr ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩

/-- A payoff preserves the tick, enlarges the fulfilled set, and only removes pending requests
from any surviving issuing phase. The serviced pair is then fulfilled or unsafe whenever it
remains pending. -/
private lemma fighterPayoff_frame
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState) :
    let t := fighterPayoff P d l q s
    t.tick = s.tick ∧ s.fulfilled.toFinset ⊆ t.fulfilled.toFinset ∧
      (∀ live, t.activeAt d l = some live →
        ∃ old, s.activeAt d l = some old ∧ live.pending ⊆ old.pending) ∧
      (∀ live, t.activeAt d l = some live → q ∈ live.pending →
        q ∈ t.fulfilled ∨ fighterSafe P d t.tick q = false) := by
  cases hp : s.activeAt d l with
  | none =>
    simp [fighterPayoff, hp]
  | some p =>
    simp only [fighterPayoff, hp]
    by_cases henabled : q ∈ p.pending ∧ q ∉ s.fulfilled ∧ fighterSafe P d s.tick q = true
    · rw [ite_eq_left henabled]
      have ha := fighterAllocate_spec d l q.2 .payoff q.1 s p hp
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk u success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · obtain ⟨_, hnone, htick, hf⟩ := ha.1 rfl
          exact ⟨htick, hf ▸ Finset.Subset.refl _, by simp [hnone], by simp [hnone]⟩
        · obtain ⟨_, _, _, _, htick, hf, _, hup⟩ := ha.2 rfl
          let v : FighterState :=
            { u with
              fulfilled := u.fulfilled ++ [q]
              active := u.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) }
          have hvp : v.activeAt d l = some { p with pending := p.pending.filter (· != q) } := by
            simp only [v, FighterState.activeAt, List.find?_map]
            change (u.activeAt d l).map _ = _
            rw [hup]
            rfl
          refine ⟨htick, ?_, ?_, ?_⟩
          · intro x hx
            rw [hf]
            exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hx))
          · intro live hlive
            change v.activeAt d l = some live at hlive
            have hleq := Option.some.inj (hlive.symm.trans hvp)
            subst live
            exact ⟨p, rfl, fun x hx ↦ (List.mem_filter.mp hx).1⟩
          · intro live hlive hq
            exact Or.inl (by simp)
    · rw [ite_eq_right henabled]
      refine ⟨rfl, Finset.Subset.refl _, ?_, ?_⟩
      · intro live hlive
        exact ⟨live, hp.symm.trans hlive, List.Subset.refl _⟩
      · intro live hlive hq
        have hleq := Option.some.inj (hlive.symm.trans hp)
        subst live
        by_cases hqf : q ∈ s.fulfilled
        · exact Or.inl hqf
        · right
          cases hs : fighterSafe P d s.tick q with
          | false => rfl
          | true => exact False.elim (henabled ⟨hq, hqf, hs⟩)

/-- After the ready-payoff fold, every request still pending in the issuing phase is already
fulfilled or unsafe. -/
private lemma fighterFulfillReady_quiescent (P : FighterParams) (d l : ℕ) (s : FighterState) :
    ∀ p, (fighterFulfillReady P d l s).activeAt d l = some p → ∀ q ∈ p.pending,
      q ∈ (fighterFulfillReady P d l s).fulfilled ∨
        fighterSafe P d (fighterFulfillReady P d l s).tick q = false := by
  have hfold (qs : List Coordinate) (s : FighterState) :
      let t := qs.foldl (fun s q ↦ fighterPayoff P d l q s) s
      t.tick = s.tick ∧ s.fulfilled.toFinset ⊆ t.fulfilled.toFinset ∧
        ∀ live, t.activeAt d l = some live → ∃ old, s.activeAt d l = some old ∧
          live.pending ⊆ old.pending ∧ ∀ q ∈ qs, q ∈ live.pending →
            q ∈ t.fulfilled ∨ fighterSafe P d t.tick q = false := by
    induction qs generalizing s with
    | nil =>
      refine ⟨rfl, Finset.Subset.refl _, ?_⟩
      intro live hlive
      exact ⟨live, hlive, List.Subset.refl _, by simp⟩
    | cons q qs ih =>
      let mid := fighterPayoff P d l q s
      have hm := fighterPayoff_frame P d l q s
      have hi := ih mid
      refine ⟨hi.1.trans hm.1, hm.2.1.trans hi.2.1, ?_⟩
      intro live hlive
      obtain ⟨p, hp, hsub, hclosed⟩ := hi.2.2 live hlive
      obtain ⟨old, hold, hsub'⟩ := hm.2.2.1 p hp
      refine ⟨old, hold, (fun x hx ↦ hsub' (hsub hx)), ?_⟩
      intro x hx hxpend
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases hm.2.2.2 p hp (hsub hxpend) with h | h
        · exact Or.inl (List.mem_toFinset.mp (hi.2.1 (List.mem_toFinset.mpr h)))
        · right
          change fighterSafe P d (qs.foldl (fun s q ↦ fighterPayoff P d l q s) mid).tick x = false
          rw [hi.1]
          exact h
      · exact hclosed x hx hxpend
  cases hp : s.activeAt d l with
  | none => simp [fighterFulfillReady, hp]
  | some p =>
    simp only [fighterFulfillReady, hp]
    intro live hlive q hq
    obtain ⟨old, hold, hsub, hclosed⟩ := (hfold p.pending s).2.2 live hlive
    have hpeq := Option.some.inj (hold.symm.trans hp)
    subst old
    exact hclosed q (hsub hq) hq

/-- Process the postponed ready fold first, accumulating credits, then process the immediate
fold using those credits. The two completed ready folds preserve comparison independently of
pending-list order and duplicates. -/
private lemma postponedComparison_fulfillReady
    (P : FighterParams) (d l : ℕ) (s t : FighterState)
    (hrel : postponedComparison d l s t) :
    postponedComparison d l (fighterFulfillReady P d l s) (fighterFulfillReady P d l t) := by
  rcases hrel with htf | ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩
  · exact Or.inl ((failed_persists_payoff_fulfillReady_fuelUnit P d l).2.1 t htf)
  · have hr : postponedComparison d l s (fighterFulfillReady P d l t) := by
      simp only [fighterFulfillReady, htp]
      have hfold (qs : List Coordinate) (u : FighterState) (hu : postponedComparison d l s u) :
          postponedComparison d l s (qs.foldl (fun s q ↦ fighterPayoff P d l q s) u) := by
        induction qs generalizing u with
        | nil => exact hu
        | cons q qs ih => exact ih _ (postponedComparison_payoff_postponed P d l s u hu q)
      exact hfold pending t
        (Or.inr ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩)
    have hquiet := fighterFulfillReady_quiescent P d l t
    simp only [fighterFulfillReady, hsp]
    have hfold (qs : List Coordinate) (u : FighterState)
        (hu : postponedComparison d l u (fighterFulfillReady P d l t)) :
        postponedComparison d l (qs.foldl (fun s q ↦ fighterPayoff P d l q s) u)
          (fighterFulfillReady P d l t) := by
      induction qs generalizing u with
      | nil => exact hu
      | cons q qs ih =>
        exact ih _ (postponedComparison_payoff_immediate P d l _ _ hu hquiet q)
    exact hfold p.pending s hr

/-- Funding the same retained coordinates preserves equality of the unions of pending and
fulfilled requests. -/
private lemma fundRequests_union_eq
    (d : ℕ) (p : FighterPhase) (pending : List Coordinate)
    (issued : Bool) (fs ft : List Coordinate)
    (hpend : p.pending.toFinset ∪ fs.toFinset = pending.toFinset ∪ ft.toFinset) :
    (p.fundRequests d fs).pending.toFinset ∪ fs.toFinset =
      (({ p with pending := pending, dummyIssued := issued }).fundRequests d ft).pending.toFinset ∪
        ft.toFinset := by
  let funded := (p.game d).coordinates.filter (fun q ↦
    decide ((p.game d).price q ≤ (p.indicesAt d q).card))
  change (((p.pending ++ funded).filter (fun q ↦ decide (q ∉ fs))).eraseDups).toFinset ∪
      fs.toFinset =
    (((pending ++ funded).filter (fun q ↦ decide (q ∉ ft))).eraseDups).toFinset ∪ ft.toFinset
  ext q
  have hq := Finset.ext_iff.mp hpend q
  simp only [Finset.mem_union, List.mem_toFinset] at hq
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_eraseDups, List.mem_filter,
    List.mem_append, decide_eq_true_eq]
  tauto

/-- One designated fuel unit preserves comparison. Both runs make the same index insertion and
budget charge; successful fuel allocations increase the same length occupancy, and the
ready-fold comparison handles the immediate payoffs. -/
private lemma postponedComparison_fuelUnit
    (P : FighterParams) (d l : ℕ) (s t : FighterState)
    (hrel : postponedComparison d l s t) (q : Coordinate) :
    postponedComparison d l (fighterFuelUnit P d l q s) (fighterFuelUnit P d l q t) := by
  rcases hrel with htf | ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩
  · exact Or.inl ((failed_persists_payoff_fulfillReady_fuelUnit P d l).2.2 q t htf)
  · have hlevel : p.level = l :=
      beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hsp)
    have hgame : ({ p with pending := pending, dummyIssued := issued }.game d) = p.game d := rfl
    simp only [fighterFuelUnit, hsp, htp, hgame]
    by_cases henabled : q ∈ (p.game d).coordinates ∧ 0 < p.controlledRemaining
    · rw [ite_eq_left henabled, ite_eq_left henabled]
      let charged := { p with controlledRemaining := p.controlledRemaining - 1 }
      let charged' := { p with
        pending := pending
        dummyIssued := issued
        controlledRemaining := p.controlledRemaining - 1 }
      let index := fighterFreshString d (p.indices[(p.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) p.candidate.1) index
      have hsp' : (s.putPhase d charged).activeAt d l = some charged :=
        FighterState.activeAt_putPhase d l s charged hlevel
      have htp' : (t.putPhase d charged').activeAt d l = some charged' :=
        FighterState.activeAt_putPhase d l t charged' hlevel
      change postponedComparison d l
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
          | (next, success) => if success then fighterFulfillReady P d l
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next)
        (match fighterAllocate d l .fuel (levelUpper l + d) out (t.putPhase d charged') with
          | (next, success) => if success then fighterFulfillReady P d l
              (next.putPhase d ((charged'.insertIndex d q index).fundRequests d next.fulfilled))
            else next)
      have hat := fighterAllocate_spec d l (levelUpper l + d) .fuel out (t.putPhase d charged')
        charged' htp'
      cases htalloc : fighterAllocate d l .fuel (levelUpper l + d) out (t.putPhase d charged') with
      | mk ut bt =>
        rw [htalloc] at hat
        cases bt <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact Or.inl (hat.1 rfl).1
        · have hmono : (occupiedInputs (s.putPhase d charged) (levelUpper l + d)).card ≤
              (occupiedInputs (t.putPhase d charged') (levelUpper l + d)).card := by
            change (occupiedInputs s (levelUpper l + d)).card ≤
              (occupiedInputs t (levelUpper l + d)).card
            have hc := hcount (levelUpper l + d)
            omega
          have htsuccess :
              (fighterAllocate d l .fuel (levelUpper l + d) out
                (t.putPhase d charged')).2 = true := by
            rw [htalloc]
          have hssuccess := fighterAllocate_success_of_card_le d l (levelUpper l + d) .fuel .fuel
            out out (s.putPhase d charged) (t.putPhase d charged') charged charged' hsp' htp'
            hmono htsuccess
          have has := (fighterAllocate_spec d l (levelUpper l + d) .fuel out
            (s.putPhase d charged) charged hsp').2 hssuccess
          cases hsalloc : fighterAllocate d l .fuel (levelUpper l + d) out
              (s.putPhase d charged) with
          | mk us bs =>
            rw [hsalloc] at has hssuccess
            cases bs
            · cases hssuccess
            · simp only [ite_true]
              obtain ⟨inputS, hlenS, hfreshS, hallocS, htickS, hfS, hfailedS, _⟩ := has
              obtain ⟨inputT, hlenT, hfreshT, hallocT, htickT, hfT, hfailedT, _⟩ := hat.2 rfl
              let ps := (charged.insertIndex d q index).fundRequests d us.fulfilled
              let pt := (charged'.insertIndex d q index).fundRequests d ut.fulfilled
              let ss := us.putPhase d ps
              let tt := ut.putPhase d pt
              have hps : ps.level = l := hlevel
              have hpt : pt.level = l := hlevel
              have hcore : pt = { ps with pending := pt.pending, dummyIssued := issued } := rfl
              change postponedComparison d l (fighterFulfillReady P d l ss)
                (fighterFulfillReady P d l tt)
              apply postponedComparison_fulfillReady
              right
              refine ⟨hfailedS.trans hsf, hfailedT.trans htf,
                htickS.trans (htick.trans htickT.symm), ps, pt.pending, issued,
                FighterState.activeAt_putPhase d l us ps hps, ?_, ?_, ?_, ?_⟩
              · rw [← hcore]
                exact FighterState.activeAt_putPhase d l ut pt hpt
              · change us.fulfilled.toFinset ⊆ ut.fulfilled.toFinset
                rw [hfS, hfT]
                exact hsub
              · change ps.pending.toFinset ∪ us.fulfilled.toFinset =
                  pt.pending.toFinset ∪ ut.fulfilled.toFinset
                dsimp only [ps, pt]
                rw [hfS, hfT]
                exact fundRequests_union_eq d (charged.insertIndex d q index) pending issued
                  s.fulfilled t.fulfilled hpend
              · intro r
                have hocS := card_occupiedInputs_append s ss
                  ⟨l, p.candidate, s.tick, .fuel, levelUpper l + d, inputS, out⟩
                  hallocS hfreshS r
                have hocT := card_occupiedInputs_append t tt
                  ⟨l, p.candidate, t.tick, .fuel, levelUpper l + d, inputT, out⟩
                  hallocT hfreshT r
                simp only [hlenS] at hocS
                simp only [hlenT] at hocT
                have hcr : prepaidRequests ss tt r = prepaidRequests s t r := by
                  change (ut.fulfilled.toFinset \ us.fulfilled.toFinset).filter
                    (fun q ↦ q.2 = r) = _
                  rw [hfS, hfT]
                  rfl
                change (occupiedInputs ss r).card + (prepaidRequests ss tt r).card ≤
                  (occupiedInputs tt r).card
                rw [hocS, hocT, hcr]
                have hc := hcount r
                omega
    · rw [ite_eq_right henabled, ite_eq_right henabled]
      exact Or.inr ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩

/-- A preceding dummy either fails or only adds an occupied input and changes the dummy-issued
flag, so the original state compares to its dummy result. -/
private lemma postponedComparison_dummy
    (d l : ℕ) (s : FighterState) (p : FighterPhase)
    (hp : s.activeAt d l = some p) : postponedComparison d l s (fighterDummy d l s) := by
  have hrefl := postponedComparison_refl d l s p hp
  have hlevel : p.level = l :=
    beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
  simp only [fighterDummy, hp]
  cases hdummy : p.dummy with
  | none => exact hrefl
  | some out =>
    cases hi : p.dummyIssued <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · have ha := fighterAllocate_spec d l (levelInput d l) .dummy out s p hp
      cases he : fighterAllocate d l .dummy (levelInput d l) out s with
      | mk u success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact Or.inl (ha.1 rfl).1
        · obtain ⟨input, hlen, hfresh, halloc, hutick, huf, hufailed, _⟩ := ha.2 rfl
          cases hsf : s.failed with
          | true => exact Or.inl (hufailed.trans hsf)
          | false =>
            right
            refine ⟨hsf, hufailed.trans hsf, hutick.symm,
              p, p.pending, true, hp,
              (by simpa only [hdummy] using
                FighterState.activeAt_putPhase d l u { p with dummyIssued := true } hlevel),
              ?_, ?_, ?_⟩
            · change s.fulfilled.toFinset ⊆ u.fulfilled.toFinset
              rw [huf]
            · change _ = _ ∪ u.fulfilled.toFinset
              rw [huf]
            · intro r
              let t := u.putPhase d { p with dummyIssued := true }
              have hoc := card_occupiedInputs_append s t
                ⟨l, p.candidate, s.tick, .dummy, levelInput d l, input, out⟩ halloc hfresh r
              have hcr : prepaidRequests s t r = ∅ := by
                change (u.fulfilled.toFinset \ s.fulfilled.toFinset).filter (fun q ↦ q.2 = r) = ∅
                rw [huf]
                simp
              change (occupiedInputs s r).card + (prepaidRequests s t r).card ≤
                (occupiedInputs t r).card
              rw [hcr, Finset.card_empty, Nat.add_zero, hoc]
              omega
    · exact hrefl

/-- Induction over fuel counts and the coordinate fold lifts the single-unit comparison to any
fixed move vector. -/
private lemma postponedComparison_fuelUnits_fold
    (P : FighterParams) (d l : ℕ) (coords : List Coordinate)
    (move : List ℕ) (s t : FighterState) (hrel : postponedComparison d l s t) :
    postponedComparison d l
      (coords.zipIdx.foldl (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) s)
      (coords.zipIdx.foldl (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) t) := by
  have hunits (q : Coordinate) (count : ℕ) (s t : FighterState)
      (hrel : postponedComparison d l s t) :
      postponedComparison d l (fighterFuelUnits P d l q count s)
        (fighterFuelUnits P d l q count t) := by
    induction count generalizing s t with
    | zero => exact hrel
    | succ count ih => exact ih _ _ (postponedComparison_fuelUnit P d l s t hrel q)
  have hfold (xs : List (Coordinate × ℕ)) (s t : FighterState)
      (hrel : postponedComparison d l s t) :
      postponedComparison d l
        (xs.foldl (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) s)
        (xs.foldl (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) t) := by
    induction xs generalizing s t with
    | nil => exact hrel
    | cons qi xs ih => exact ih _ _ (hunits qi.1 (move[qi.2]?.getD 0) s t hrel)
  exact hfold _ s t hrel

/-- Comparable states enable the same selected controlled move. Batch comparison transfers
failure to the postponed response; installing the official child preserves that failure
flag. -/
private lemma failed_strategyMove_of_postponedComparison
    (P : FighterParams) (d l : ℕ) (s t response : FighterState)
    (hrel : postponedComparison d l s t)
    (hresponse : fighterStrategyMove P d l s = some response)
    (hfailed : response.failed = true) :
    t.failed = true ∨ ∃ response',
      fighterStrategyMove P d l t = some response' ∧ response'.failed = true := by
  rcases hrel with htf | ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩
  · exact Or.inl htf
  · simp only [fighterStrategyMove, hsp, bind, Option.bind] at hresponse
    by_cases hcond : p.predicateHolds d = false ∧ p.buffer.sum = 0 ∧
        (p.game d).activePlayer (p.official d) = p.controlledPlayer
    · rw [ite_eq_left hcond] at hresponse
      cases hm : (p.game d).strategy (p.official d) with
      | none => simp only [hm] at hresponse; contradiction
      | some move =>
        simp only [hm] at hresponse
        by_cases hlegal : (p.game d).LegalMove (p.official d) move ∧
            move.sum ≤ p.controlledRemaining
        · rw [ite_eq_left hlegal] at hresponse
          let bs := (p.game d).coordinates.zipIdx.foldl
            (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          let bt := (p.game d).coordinates.zipIdx.foldl
            (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) t
          change (match bs.activeAt d l with
            | none => some bs
            | some live => some (bs.putPhase d
                { live with officialCode := ((p.game d).afterMove (p.official d) move).encode })) =
              some response at hresponse
          have hbs : bs.failed = true := by
            cases hb : bs.activeAt d l with
            | none =>
              simp only [hb, Option.some.injEq] at hresponse
              exact hresponse ▸ hfailed
            | some live =>
              simp only [hb, Option.some.injEq] at hresponse
              rw [← hresponse] at hfailed
              exact hfailed
          have hcomp := postponedComparison_fuelUnits_fold P d l (p.game d).coordinates move s t
            (Or.inr ⟨hsf, htf, htick, p, pending, issued, hsp, htp, hsub, hpend, hcount⟩)
          have hbt : bt.failed = true := by
            rcases hcomp with h | ⟨h, _⟩
            · exact h
            · change bs.failed = false at h
              rw [hbs] at h
              cases h
          have htformula : fighterStrategyMove P d l t =
              match bt.activeAt d l with
              | none => some bt
              | some live => some (bt.putPhase d
                  { live with
                    officialCode := ((p.game d).afterMove (p.official d) move).encode }) := by
            simp only [fighterStrategyMove, htp, bind, Option.bind]
            change (if p.predicateHolds d = false ∧ p.buffer.sum = 0 ∧
                (p.game d).activePlayer (p.official d) = p.controlledPlayer then
              ((p.game d).strategy (p.official d)).bind (fun m ↦
                if (p.game d).LegalMove (p.official d) m ∧ m.sum ≤ p.controlledRemaining then
                  let next := (p.game d).coordinates.zipIdx.foldl
                    (fun s (q, i) ↦ fighterFuelUnits P d l q (m[i]?.getD 0) s) t
                  match next.activeAt d l with
                  | none => some next
                  | some live => some (next.putPhase d
                      { live with officialCode := ((p.game d).afterMove (p.official d) m).encode })
                else none)
              else none) = _
            rw [ite_eq_left hcond, hm]
            simp only [Option.bind_some]
            rw [ite_eq_left hlegal]
          right
          cases hb : bt.activeAt d l with
          | none => exact ⟨bt, by rw [htformula, hb], hbt⟩
          | some live =>
            exact ⟨bt.putPhase d
              { live with officialCode := ((p.game d).afterMove (p.official d) move).encode },
              by rw [htformula, hb], hbt⟩
        · rw [ite_eq_right hlegal] at hresponse
          contradiction
    · rw [ite_eq_right hcond] at hresponse
      contradiction

/-- An enabled controlled response is on the controlled player's turn, which excludes the
buffer-flush branch. -/
private lemma fighterFlushBuffer_eq_none_of_strategyMove
    (P : FighterParams) (d l : ℕ) (s response : FighterState)
    (hresponse : fighterStrategyMove P d l s = some response) :
    fighterFlushBuffer d l s = none := by
  cases hp : s.activeAt d l with
  | none => simp [fighterFlushBuffer, hp]
  | some p =>
    have hcond : p.predicateHolds d = false ∧ p.buffer.sum = 0 ∧
        (p.game d).activePlayer (p.official d) = p.controlledPlayer := by
      by_contra h
      simp [fighterStrategyMove, hp, h] at hresponse
    simp [fighterFlushBuffer, hp, hcond.2.2]

/-- A failed enabled response remains a failed enabled response after one preceding action,
unless that action itself sets the failure flag. For dummy and ready-payoff actions,
compare the same fuel requests and immediate payoffs: earlier fulfillment removes only
its own later request, and allocation never frees an input. In the strategy branch the
returned state already carries the failure. -/
lemma failed_response_survives_level_action
    (P : FighterParams) (d l : ℕ) (state response next : FighterState)
    (hresponse : fighterStrategyMove P d l state = some response)
    (hfailed : response.failed = true)
    (hnext : fighterLevelAction P d l state = some next) :
    next.failed = true ∨ ∃ response',
      fighterStrategyMove P d l next = some response' ∧ response'.failed = true := by
  cases hp : state.activeAt d l with
  | none => simp [fighterStrategyMove, hp] at hresponse
  | some p =>
    have hflush := fighterFlushBuffer_eq_none_of_strategyMove P d l state response hresponse
    simp only [fighterLevelAction, hp, bind, Option.bind] at hnext
    by_cases hdummy : (p.dummy.isSome && !p.dummyIssued) = true
    · rw [ite_eq_left hdummy] at hnext
      have heq := Option.some.inj hnext
      subst next
      exact failed_strategyMove_of_postponedComparison P d l state (fighterDummy d l state)
        response (postponedComparison_dummy d l state p hp) hresponse hfailed
    · rw [ite_eq_right hdummy] at hnext
      cases hpay : p.pending.find? (fun q ↦ decide (q ∉ state.fulfilled) &&
          fighterSafe P d state.tick q) with
      | some q =>
        simp only [hpay, Option.some.injEq] at hnext
        subst next
        exact failed_strategyMove_of_postponedComparison P d l state
          (fighterPayoff P d l q state) response
          (postponedComparison_payoff_postponed P d l state state
            (postponedComparison_refl d l state p hp) q) hresponse hfailed
      | none =>
        simp only [hpay, hflush] at hnext
        have heq := Option.some.inj (hresponse.symm.trans hnext)
        exact Or.inl (heq ▸ hfailed)

end Kolmogorov.Milovanov
