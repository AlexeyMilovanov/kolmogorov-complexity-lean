/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace

/-!
# Time-bounded stack programs and the class `EXP`

This file adds step counts to the simulation of stack programs by one-tape machines
(`StackSim.simOTM`, Expspace.lean) and derives the time-bounded counterparts of the space results:

* `Prog.TimeBounded P p`: `P` halts on every input `x` within `2 ^ p(|x|)` steps, all its
  configurations up to then having space `≤ 2 ^ p(|x|)`;
* `StackSim.ReachN M H n c c'`: the counted version of `StackSim.Reach` (at most `n` steps);
* counted versions of the sweep lemmas (`blockRN`, …, `sweepHomeN`): one macro step of the
  simulation (one instruction of `P`) takes at most `2 * (space + k) + 5` machine steps
  (`StackSim.macroStepN`);
* `Prog.exists_sim_time`: the simulating machine halts within `C * (t + 1) * (S + 1)` steps when
  `P` halts at time `t` in space `S`;
* `Prog.lang_mem_EXP`: the language of a time-bounded stack program is in `EXP`;
* `EXP_modify_one`, `EXP_of_eventually_eq` (and `EXP_of_eventually_eq'`, in the argument order of
  the closure hypothesis of `general`): `EXP` is closed under finite modifications;
* `EXP_subset_EXPSPACE`, `polyTimeOracle_empty_subset_EXP`;
* `Prog.space_run_le` (space after `s` steps is at most `|x| + s`), `Prog.timeBounded_of_time`,
  `Prog.lang_mem_EXP_of_time`: a time bound alone puts the language of a stack program in `EXP`.

The simulating machine `StackSim.simOTM P` is the one of Expspace.lean, unchanged.
-/

namespace Kolmogorov.RandomStrings

/-- `P` halts on every input `x` within `2 ^ p(|x|)` steps, and all configurations up to the
halting time have space `≤ 2 ^ p(|x|)`. -/
def Prog.TimeBounded (P : Prog) (p : Polynomial ℕ) : Prop :=
  ∀ x : BitString, ∃ t ≤ 2 ^ p.eval x.length, P.Halted (P.run x t) ∧
    ∀ s ≤ t, (P.run x s).space ≤ 2 ^ p.eval x.length

namespace StackSim

/-! #### Counted runs with bounded head positions -/

/-- `ReachN M H n c c'`: the machine `M` (oracle `∅`) goes from `c` to `c'` in at most `n` steps,
every configuration on the way (both ends included) having its head in `[-1, H]`. -/
inductive ReachN (M : OTM) (H : ℤ) : ℕ → Config M → Config M → Prop
  | refl (n : ℕ) (c : Config M) : -1 ≤ c.head → c.head ≤ H → ReachN M H n c c
  | next (n : ℕ) (c c' : Config M) : -1 ≤ c.head → c.head ≤ H →
      ReachN M H n (step M ∅ c) c' → ReachN M H (n + 1) c c'

/-- A larger step budget is allowed. -/
theorem ReachN.mono {M : OTM} {H : ℤ} {n m : ℕ} {c c' : Config M} (h : ReachN M H n c c')
    (hnm : n ≤ m) : ReachN M H m c c' := by
  induction h generalizing m with
  | refl n c hl hh => exact ReachN.refl m c hl hh
  | next n c c' hl hh _ ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact ReachN.next m' c c' hl hh (ih (by omega))

/-- Counted chains compose, adding the step budgets. -/
theorem ReachN.trans {M : OTM} {H : ℤ} {n₁ n₂ : ℕ} {c₁ c₂ c₃ : Config M}
    (h₁ : ReachN M H n₁ c₁ c₂) (h₂ : ReachN M H n₂ c₂ c₃) : ReachN M H (n₁ + n₂) c₁ c₃ := by
  induction h₁ with
  | refl n c _ _ => exact h₂.mono (by omega)
  | next n c c' hl hh _ ih =>
    have := ReachN.next _ c c₃ hl hh (ih h₂)
    rwa [show n + n₂ + 1 = n + 1 + n₂ by omega] at this

/-- A counted chain is a stretch of the run of length at most the budget, all of whose heads lie
in `[-1, H]`. -/
theorem ReachN.iterate {M : OTM} {H : ℤ} {n : ℕ} {c c' : Config M} (h : ReachN M H n c c') :
    ∃ d ≤ n, (step M ∅)^[d] c = c' ∧
      ∀ e ≤ d, -1 ≤ ((step M ∅)^[e] c).head ∧ ((step M ∅)^[e] c).head ≤ H := by
  induction h with
  | refl n c hl hh =>
    refine ⟨0, Nat.zero_le _, rfl, fun e he => ?_⟩
    obtain rfl : e = 0 := by omega
    exact ⟨hl, hh⟩
  | next n c c' hl hh _ ih =>
    obtain ⟨d, hdn, hd, hb⟩ := ih
    refine ⟨d + 1, by omega, by rw [Function.iterate_succ_apply]; exact hd, fun e he => ?_⟩
    rcases e with _ | e
    · exact ⟨hl, hh⟩
    · rw [Function.iterate_succ_apply]; exact hb e (by omega)

variable (P : Prog)

/-- One step of the simulating machine inside a counted chain. -/
theorem reachN_step {H : ℤ} {n : ℕ} {q q' : SimQ P.code.length P.k} {τ : ℤ → Sym} {h : ℤ}
    {a : Sym} {mv : Move} {c' : Config (simOTM P)} (hq : q ≠ .acc ∧ q ≠ .rej)
    (hδ : simδ P q (τ h) = .step q' a mv) (hl : -1 ≤ h) (hh : h ≤ H)
    (hr : ReachN (simOTM P) H n ⟨q', Function.update τ h a, moveHead mv h, []⟩ c') :
    ReachN (simOTM P) H (n + 1) ⟨q, τ, h, []⟩ c' := by
  refine ReachN.next _ _ _ hl hh ?_
  have hc : ¬ Halted (simOTM P) ⟨q, τ, h, []⟩ := by
    rintro (h1 | h1)
    · exact hq.1 h1
    · exact hq.2 h1
  rw [step_eq' (simOTM P) ⟨q, τ, h, []⟩ hc hδ]
  exact hr

/-- A counted chain may be empty: a configuration with empty query buffer and head in `[-1, H]`
reaches itself within any number `n` of steps. -/
theorem reflN_at {M : OTM} {H : ℤ} (n : ℕ) (q : M.Q) (τ : ℤ → Sym) (h : ℤ) (hl : -1 ≤ h)
    (hh : h ≤ H) : ReachN M H n ⟨q, τ, h, []⟩ ⟨q, τ, h, []⟩ := ReachN.refl _ _ hl hh

/-- A counted chain may start with a step that moves the head right: if `simOTM P` in state `q`
reading `τ h` writes `a`, enters `q'` and moves right, then `c'` is reachable from
`⟨q, τ, h, []⟩` within `n + 1` steps as soon as it is reachable within `n` steps from the
resulting configuration. -/
theorem reachN_right {H : ℤ} {n : ℕ} {q q' : SimQ P.code.length P.k} {τ : ℤ → Sym} {h : ℤ}
    {a : Sym} {c' : Config (simOTM P)} (hq : q ≠ .acc ∧ q ≠ .rej)
    (hδ : simδ P q (τ h) = .step q' a .right) (hl : -1 ≤ h) (hh : h ≤ H)
    (hr : ReachN (simOTM P) H n ⟨q', Function.update τ h a, h + 1, []⟩ c') :
    ReachN (simOTM P) H (n + 1) ⟨q, τ, h, []⟩ c' := reachN_step P hq hδ hl hh hr

/-- A counted chain may start with a step that moves the head left: if `simOTM P` in state `q`
reading `τ h` writes `a`, enters `q'` and moves left, then `c'` is reachable from
`⟨q, τ, h, []⟩` within `n + 1` steps as soon as it is reachable within `n` steps from the
resulting configuration. -/
theorem reachN_left {H : ℤ} {n : ℕ} {q q' : SimQ P.code.length P.k} {τ : ℤ → Sym} {h : ℤ}
    {a : Sym} {c' : Config (simOTM P)} (hq : q ≠ .acc ∧ q ≠ .rej)
    (hδ : simδ P q (τ h) = .step q' a .left) (hl : -1 ≤ h) (hh : h ≤ H)
    (hr : ReachN (simOTM P) H n ⟨q', Function.update τ h a, h - 1, []⟩ c') :
    ReachN (simOTM P) H (n + 1) ⟨q, τ, h, []⟩ c' := reachN_step P hq hδ hl hh hr

/-! #### Counted sweeps -/

/-- A state that walks right over bits without changing them (counted `blockR`). -/
theorem blockRN {H : ℤ} (q : SimQ P.code.length P.k) (hq : q ≠ .acc ∧ q ≠ .rej)
    (hδ : ∀ b : Bool, simδ P q (some b) = .step q (some b) .right) :
    ∀ (s : BitString) (pre post L : List Sym) (h h' : ℤ), L = pre ++ (s.map some ++ post) →
      h = pre.length → h' = h + s.length → h' ≤ H →
      ReachN (simOTM P) H s.length ⟨q, render L, h, []⟩ ⟨q, render L, h', []⟩
  | [], pre, post, L, h, h', _, hh, hh', hH => by
    have : h' = h := by simpa using hh'
    subst this
    exact reflN_at _ _ _ _ (by omega) hH
  | b :: s, pre, post, L, h, h', hL, hh, hh', hH => by
    have hL' : L = pre ++ some b :: (s.map some ++ post) := by rw [hL]; rfl
    have hread : render L h = some b := render_at hL' hh
    have hs : (((b :: s).length : ℕ) : ℤ) = s.length + 1 := by simp
    refine (reachN_right P (n := s.length) hq (by rw [hread]; exact hδ b) (by omega) (by omega)
      ?_).mono (by simp)
    rw [update_same hread]
    exact blockRN q hq hδ s (pre ++ [some b]) post L (h + 1) h' (by rw [hL']; simp)
      (by simp [hh]) (by omega) hH

/-- Pushing: the carry sweep over bits shifts them one cell to the right (counted). -/
theorem carryBitsN {H : ℤ} (pc : Fin P.code.length) (j : ℕ) (hj : j < P.k) :
    ∀ (s : BitString) (c : Sym) (pre post L : List Sym) (h h' : ℤ),
      L = pre ++ (s.map some ++ post) → h = pre.length → h' = h + s.length → h' ≤ H →
      ∃ w c', c :: s.map some = w ++ [c'] ∧
        ReachN (simOTM P) H s.length ⟨rS P pc j (.carry c), render L, h, []⟩
          ⟨rS P pc j (.carry c'), render (pre ++ (w ++ post)), h', []⟩
  | [], c, pre, post, L, h, h', hL, hh, hh', hH => by
    refine ⟨[], c, rfl, ?_⟩
    have : h' = h := by simpa using hh'
    subst this hL
    simp only [List.map_nil, List.nil_append]
    exact reflN_at _ _ _ _ (by omega) hH
  | b :: s, c, pre, post, L, h, h', hL, hh, hh', hH => by
    have hL' : L = pre ++ some b :: (s.map some ++ post) := by rw [hL]; rfl
    have hread : render L h = some b := render_at hL' hh
    have hs : (((b :: s).length : ℕ) : ℤ) = s.length + 1 := by simp
    obtain ⟨w, c', hw, hr⟩ := carryBitsN pc j hj s (some b) (pre ++ [c]) post
      (pre ++ c :: (s.map some ++ post)) (h + 1) h' (by simp) (by simp [hh]) (by omega) hH
    refine ⟨c :: w, c', by simp [hw], ?_⟩
    refine (reachN_right P (n := s.length) (rS_ne P pc j hj.le _)
      (by rw [hread]; exact δ_carry_some P pc j hj c b) (by omega) (by omega) ?_).mono (by simp)
    rw [update_at c hL' hh]
    have e : pre ++ [c] ++ (w ++ post) = pre ++ (c :: w ++ post) := by simp
    rw [e] at hr
    exact hr

/-- The leftward sweep without deletion over `u.reverse`, counting blanks down (counted). -/
theorem plainSweepN {H : ℤ} (pc : Fin P.code.length) (o : Sym) (j : ℕ) :
    ∀ (u : List Sym) (n : ℕ) (pre post L : List Sym) (h : ℤ), L = pre ++ (u.reverse ++ post) →
      n = j + u.count none → n ≤ P.k → h + 1 = pre.length + u.length → h ≤ H →
      ReachN (simOTM P) H u.length ⟨lS P pc o n none, render L, h, []⟩
        ⟨lS P pc o j none, render L, (pre.length : ℤ) - 1, []⟩
  | [], n, pre, post, L, h, _, hn, _, hh, hH => by
    have hn' : n = j := by simpa using hn
    have : h = (pre.length : ℤ) - 1 := by simp at hh; omega
    subst hn' this
    exact reflN_at _ _ _ _ (by omega) hH
  | a :: u, n, pre, post, L, h, hL, hn, hk, hh, hH => by
    have hL' : L = (pre ++ u.reverse) ++ a :: post := by rw [hL]; simp
    have hh2 : h = ((pre ++ u.reverse).length : ℤ) := by simp at hh ⊢; omega
    have hread : render L h = a := render_at hL' hh2
    have hrec := plainSweepN (H := H) pc o j u (j + u.count none) pre (a :: post) L (h - 1)
      (by rw [hL]; simp) rfl (by cases a <;> simp at hn <;> omega) (by simp at hh; omega)
      (by omega)
    cases a with
    | none =>
      rw [List.count_cons_self, ← add_assoc] at hn
      subst hn
      refine (reachN_left P (n := u.length) (lS_ne P pc o _ hk _)
        (by rw [hread]; exact δ_plain_none P pc o _ hk) (by omega) hH ?_).mono (by simp)
      rw [update_same hread]
      exact hrec
    | some b =>
      rw [List.count_cons_of_ne (by simp)] at hn
      subst hn
      refine (reachN_left P (n := u.length) (lS_ne P pc o _ hk _)
        (by rw [hread]; exact δ_plain_some P pc o _ hk b) (by omega) hH ?_).mono (by simp)
      rw [update_same hread]
      exact hrec

/-- Popping: the leftward carry sweep over `u.reverse` shifts it one cell to the left
(counted). -/
theorem delSweepN {H : ℤ} (pc : Fin P.code.length) (o : Sym) (j : ℕ)
    (hjr : ireg (instrAt P pc) ≤ j) :
    ∀ (u : List Sym) (n : ℕ) (c : Sym) (pre post L : List Sym) (h : ℤ),
      L = pre ++ (u.reverse ++ post) → n = j + u.count none → n ≤ P.k →
      h + 1 = pre.length + u.length → h ≤ H →
      ∃ w c', u.reverse ++ [c] = c' :: w ∧
        ReachN (simOTM P) H u.length ⟨lS P pc o n (some c), render L, h, []⟩
          ⟨lS P pc o j (some c'), render (pre ++ (w ++ post)), (pre.length : ℤ) - 1, []⟩
  | [], n, c, pre, post, L, h, hL, hn, _, hh, hH => by
    refine ⟨[], c, rfl, ?_⟩
    have hn' : n = j := by simpa using hn
    have : h = (pre.length : ℤ) - 1 := by simp at hh; omega
    subst hn' this hL
    simp only [List.reverse_nil, List.nil_append]
    exact reflN_at _ _ _ _ (by omega) hH
  | a :: u, n, c, pre, post, L, h, hL, hn, hk, hh, hH => by
    have hL' : L = (pre ++ u.reverse) ++ a :: post := by rw [hL]; simp
    have hh2 : h = ((pre ++ u.reverse).length : ℤ) := by simp at hh ⊢; omega
    have hread : render L h = a := render_at hL' hh2
    obtain ⟨w, c', hw, hr⟩ := delSweepN (H := H) pc o j hjr u (j + u.count none) a pre
      (c :: post) ((pre ++ u.reverse) ++ c :: post) (h - 1) (by simp) rfl
      (by cases a <;> simp at hn <;> omega) (by simp at hh; omega) (by omega)
    refine ⟨w ++ [c], c', by rw [List.reverse_cons, hw]; rfl, ?_⟩
    have e : pre ++ (w ++ c :: post) = pre ++ (w ++ [c] ++ post) := by simp
    rw [e] at hr
    cases a with
    | none =>
      rw [List.count_cons_self, ← add_assoc] at hn
      subst hn
      refine (reachN_left P (n := u.length) (lS_ne P pc o _ hk _)
        (by rw [hread]; exact δ_del_none P pc o _ hk (by omega) c) (by omega) hH ?_).mono
        (by simp)
      rw [update_at c hL' hh2]
      exact hr
    | some b =>
      rw [List.count_cons_of_ne (by simp)] at hn
      subst hn
      refine (reachN_left P (n := u.length) (lS_ne P pc o _ hk _)
        (by rw [hread]; exact δ_del_some P pc o _ hk c b) (by omega) hH ?_).mono (by simp)
      rw [update_at c hL' hh2]
      exact hr

/-- Navigation over whole blocks before the active stack (counted). -/
theorem navUnitsN {H : ℤ} (pc : Fin P.code.length) (hr : ireg (instrAt P pc) ≤ P.k) :
    ∀ (A : List BitString) (j : ℕ) (pre post L : List Sym) (h h' : ℤ),
      L = pre ++ (encT A ++ post) → j + A.length ≤ ireg (instrAt P pc) → h = pre.length →
      h' = h + (encT A).length → h' ≤ H →
      ReachN (simOTM P) H (encT A).length ⟨rS P pc j .nav, render L, h, []⟩
        ⟨rS P pc (j + A.length) .nav, render L, h', []⟩
  | [], j, pre, post, L, h, h', _, _, hh, hh', hH => by
    have : h' = h := by simpa [encT] using hh'
    subst this
    simp only [List.length_nil, add_zero]
    exact reflN_at _ _ _ _ (by omega) hH
  | s :: A, j, pre, post, L, h, h', hL, hA, hh, hh', hH => by
    have hlen := length_encT_cons_int s A
    have hlenN := length_encT_cons s A
    have hA' : j + 1 + A.length ≤ ireg (instrAt P pc) := by simp at hA; omega
    have hjr : j ≠ ireg (instrAt P pc) := by omega
    have hjk : j + 1 ≤ P.k := by omega
    have hL1 : L = pre ++ (s.map some ++ (none :: (encT A ++ post))) := by rw [hL]; simp [encT]
    have hb := blockRN P (H := H) (rS P pc j .nav) (rS_ne P pc j (by omega) _)
      (fun b => δ_nav_some P pc j (by omega) hjr b) s pre (none :: (encT A ++ post)) L h
      (h + s.length) hL1 hh rfl (by omega)
    have hL2 : L = (pre ++ s.map some) ++ none :: (encT A ++ post) := by rw [hL1]; simp
    have hh2 : h + s.length = ((pre ++ s.map some).length : ℤ) := by simp [hh]
    have hread : render L (h + s.length) = none := render_at hL2 hh2
    refine (hb.trans (reachN_right P (n := (encT A).length) (rS_ne P pc j (by omega) _)
      (by rw [hread]; exact δ_nav_none P pc j hjk hjr) (by omega) (by omega) ?_)).mono
      (by omega)
    rw [update_same hread]
    have := navUnitsN (H := H) pc hr A (j + 1) (pre ++ (s.map some ++ [none])) post L
      (h + s.length + 1) h'
      (by rw [hL]; simp [encT]) hA' (by simp [hh]; omega) (by omega) hH
    rw [show j + (s :: A).length = j + 1 + A.length by simp; omega]
    exact this

/-- After reading the top `o`: walk to the end of the encoding and turn (counted). -/
theorem doneUnitsN {H : ℤ} (pc : Fin P.code.length) (o : Sym) :
    ∀ (B : List BitString) (j : ℕ) (pre post L : List Sym) (h h' : ℤ), B ≠ [] →
      j + B.length = P.k → L = pre ++ (encT B ++ post) → h = pre.length →
      h' = h + (encT B).length → h' ≤ H →
      ReachN (simOTM P) H (encT B).length ⟨rS P pc j (.done o), render L, h, []⟩
        ⟨.turn pc o, render L, h', []⟩
  | [], _, _, _, _, _, _, hB, _, _, _, _, _ => absurd rfl hB
  | s :: B, j, pre, post, L, h, h', _, hjB, hL, hh, hh', hH => by
    have hlen := length_encT_cons_int s B
    have hlenN := length_encT_cons s B
    have hjk : j < P.k := by simp at hjB; omega
    have hL1 : L = pre ++ (s.map some ++ (none :: (encT B ++ post))) := by rw [hL]; simp [encT]
    have hb := blockRN P (H := H) (rS P pc j (.done o)) (rS_ne P pc j hjk.le _)
      (fun b => δ_done_some P pc j hjk.le o b) s pre (none :: (encT B ++ post)) L h
      (h + s.length) hL1 hh rfl (by omega)
    refine (hb.trans (n₂ := (encT B).length + 1) ?_).mono (by omega)
    have hL2 : L = (pre ++ s.map some) ++ none :: (encT B ++ post) := by rw [hL1]; simp
    have hh2 : h + s.length = ((pre ++ s.map some).length : ℤ) := by simp [hh]
    have hread : render L (h + s.length) = none := render_at hL2 hh2
    rcases eq_or_ne B [] with hB | hB
    · subst hB
      have hj1 : j + 1 = P.k := by simpa using hjB
      have h0 : (encT ([] : List BitString)).length = 0 := rfl
      refine reachN_right P (rS_ne P pc j hjk.le _)
        (by rw [hread]; exact δ_done_turn P pc j hj1 o) (by omega) (by omega) ?_
      rw [update_same hread]
      obtain rfl : h' = h + s.length + 1 := by omega
      exact reflN_at _ _ _ _ (by omega) hH
    · have hBl : 0 < B.length := List.length_pos_of_ne_nil hB
      have hj1 : j + 1 < P.k := by simp at hjB; omega
      refine reachN_right P (rS_ne P pc j hjk.le _)
        (by rw [hread]; exact δ_done_none P pc j hj1 o) (by omega) (by omega) ?_
      rw [update_same hread]
      exact doneUnitsN (H := H) pc o B (j + 1) (pre ++ (s.map some ++ [none])) post L
        (h + s.length + 1) h'
        hB (by simp at hjB; omega) (by rw [hL]; simp [encT]) (by simp [hh]; omega)
        (by omega) hH

/-- Pushing over whole blocks: the encoding is shifted one cell to the right (counted). -/
theorem carryUnitsN {H : ℤ} (pc : Fin P.code.length) :
    ∀ (B : List BitString) (j : ℕ) (c : Sym) (pre post L : List Sym) (h h' : ℤ),
      j + B.length ≤ P.k → L = pre ++ (encT B ++ post) → h = pre.length →
      h' = h + (encT B).length → h' ≤ H →
      ∃ w c', c :: encT B = w ++ [c'] ∧
        ReachN (simOTM P) H (encT B).length ⟨rS P pc j (.carry c), render L, h, []⟩
          ⟨rS P pc (j + B.length) (.carry c'), render (pre ++ (w ++ post)), h', []⟩
  | [], j, c, pre, post, L, h, h', _, hL, hh, hh', hH => by
    refine ⟨[], c, rfl, ?_⟩
    have : h' = h := by simpa [encT] using hh'
    subst this hL
    simp only [List.length_nil, add_zero, encT, List.nil_append]
    exact reflN_at _ _ _ _ (by omega) hH
  | s :: B, j, c, pre, post, L, h, h', hjB, hL, hh, hh', hH => by
    have hlen := length_encT_cons_int s B
    have hlenN := length_encT_cons s B
    have hjk : j < P.k := by simp at hjB; omega
    have hL1 : L = pre ++ (s.map some ++ (none :: (encT B ++ post))) := by rw [hL]; simp [encT]
    obtain ⟨w₁, c₁, hw₁, hr₁⟩ :=
      carryBitsN P (H := H) pc j hjk s c pre (none :: (encT B ++ post)) L h
      (h + s.length) hL1 hh rfl (by omega)
    have hw₁len : w₁.length = s.length := by
      have := congrArg List.length hw₁; simp at this; omega
    have hL2 : pre ++ (w₁ ++ none :: (encT B ++ post)) = (pre ++ w₁) ++ none :: (encT B ++ post) :=
      by simp
    have hh2 : h + s.length = ((pre ++ w₁).length : ℤ) := by simp [hh, hw₁len]
    have hread : render (pre ++ (w₁ ++ none :: (encT B ++ post))) (h + s.length) = none :=
      render_at hL2 hh2
    obtain ⟨w₂, c₂, hw₂, hr₂⟩ := carryUnitsN (H := H) pc B (j + 1) none (pre ++ w₁ ++ [c₁]) post
      ((pre ++ w₁) ++ c₁ :: (encT B ++ post)) (h + s.length + 1) h' (by simp at hjB; omega)
      (by simp) (by simp [hh, hw₁len]; omega) (by omega) hH
    refine ⟨w₁ ++ [c₁] ++ w₂, c₂, ?_, (hr₁.trans (reachN_right P (n := (encT B).length)
      (rS_ne P pc j hjk.le _) (by rw [hread]; exact δ_carry_none P pc j hjk c₁) (by omega)
      (by omega) ?_)).mono (by omega)⟩
    · change c :: (s.map some ++ none :: encT B) = _
      rw [← List.cons_append, hw₁, hw₂]
      simp
    · rw [update_at c₁ hL2 hh2]
      have e1 : j + (s :: B).length = j + 1 + B.length := by simp; omega
      have e2 : pre ++ w₁ ++ [c₁] ++ (w₂ ++ post) = pre ++ (w₁ ++ [c₁] ++ w₂ ++ post) := by simp
      rw [e1, ← e2]
      exact hr₂

/-- From the start of an instruction to the active stack's block, switching mode there
(counted). -/
theorem navSwitchN {H : ℤ} (pc : Fin P.code.length) (A : List BitString) (rest L : List Sym)
    (a : Sym) (hL : L = encT A ++ a :: rest) (hA : A.length = ireg (instrAt P pc))
    (hr : ireg (instrAt P pc) ≤ P.k) (hH : ((encT A).length : ℤ) ≤ H) :
    ReachN (simOTM P) H ((encT A).length + 1) ⟨rS P pc 0 .nav, render L, 0, []⟩
      ⟨rS P pc A.length (switchMode (instrAt P pc) a), render L, (encT A).length, []⟩ := by
  have h1 := navUnitsN P (H := H) pc hr A 0 [] (a :: rest) L 0 (encT A).length (by simp [hL])
    (by omega)
    (by simp) (by simp) hH
  rw [zero_add] at h1
  refine h1.trans ?_
  have hread : render L (encT A).length = a := render_at hL rfl
  refine reachN_step P (rS_ne P pc _ (by omega) _)
    (by rw [hread]; exact δ_nav_sw P pc _ (by omega) hA a) (by omega) hH ?_
  rw [update_same hread]
  simp only [moveHead]
  exact reflN_at _ _ _ _ (by omega) hH

/-- `test`/`pop`: from the start of the instruction to the turn, then one step left
(counted). -/
theorem navDoneTurnN {H : ℤ} (pc : Fin P.code.length) (A : List BitString) (s : BitString)
    (B : List BitString) (L : List Sym) (hL : L = encT (A ++ s :: B))
    (hA : A.length = ireg (instrAt P pc)) (hK : (A ++ s :: B).length = P.k)
    (hsw : switchMode (instrAt P pc) s.head? = .done s.head?)
    (hH : ((encT (A ++ s :: B)).length : ℤ) ≤ H) :
    ReachN (simOTM P) H ((encT (A ++ s :: B)).length + 2) ⟨rS P pc 0 .nav, render L, 0, []⟩
      ⟨lS P pc s.head? P.k (delMode (instrAt P pc) s.head?), render L,
        ((encT (A ++ s :: B)).length : ℤ) - 1, []⟩ := by
  have hlenAB : ((encT (A ++ s :: B)).length : ℤ) = (encT A).length + (encT (s :: B)).length := by
    rw [encT_append]; simp
  have hlenABN : (encT (A ++ s :: B)).length = (encT A).length + (encT (s :: B)).length := by
    rw [encT_append]; simp
  have hlen := length_encT_cons_int s B
  have hL' : L = encT A ++ s.head? :: (encT (s :: B)).tail := by
    rw [hL, encT_append, ← encT_cons]
  have hKl : A.length + 1 + B.length = P.k := by simp at hK; omega
  have h1 := navSwitchN P (H := H) pc A _ L s.head? hL' hA (by omega) (by omega)
  rw [hsw] at h1
  have h2 := doneUnitsN P (H := H) pc s.head? (s :: B) A.length (encT A) [] L (encT A).length
    ((encT (A ++ s :: B)).length) (by simp) (by simp; omega) (by simp [hL, encT_append]) rfl
    (by omega) hH
  refine ((h1.trans h2).trans (n₂ := 1) ?_).mono (by omega)
  refine reachN_left P (by simp) (δ_turn P pc s.head? _) (by omega) hH ?_
  rw [update_read]
  exact reflN_at _ _ _ _ (by omega) (by omega)

/-- The leftward sweep over a whole encoding (no deletion) and the step back to cell `0`
(counted). -/
theorem sweepHomeN {H : ℤ} (pc : Fin P.code.length) (o : Sym) (l : List BitString)
    (post L : List Sym) (n : ℕ) (h : ℤ) (hL : L = encT l ++ post) (hn : n = l.length)
    (hl : l.length ≤ P.k) (hh : h + 1 = (encT l).length) (hH : h ≤ H) (hH0 : 0 ≤ H) :
    ReachN (simOTM P) H ((encT l).length + 1) ⟨lS P pc o n none, render L, h, []⟩
      ⟨entry P (nextPC (instrAt P pc) o), render L, 0, []⟩ := by
  have h1 := plainSweepN P (H := H) pc o 0 (encT l).reverse n [] post L h (by simp [hL])
    (by simp [hn, count_encT]) (by omega) (by simp; omega) hH
  simp only [List.length_nil, Nat.cast_zero, zero_sub, List.length_reverse] at h1
  refine h1.trans ?_
  have hread : render L (-1) = none := render_neg_one L
  refine reachN_right P (lS_ne P pc o 0 (Nat.zero_le _) _)
    (by rw [hread]; exact δ_plain_home P pc o) (le_refl _) (by omega) ?_
  rw [update_same hread, show (-1 : ℤ) + 1 = 0 by norm_num]
  exact reflN_at _ _ _ _ (by norm_num) hH0

/-! #### Counted macro steps -/

/-- Macro step for `push r b n` (counted): navigate, shift right inserting `b`, turn, sweep
home. -/
theorem macro_pushN {H : ℤ} (c : PConfig P) (hpc : c.pc < P.code.length) (r : Fin P.k) (b : Bool)
    (n : ℕ) (hi : P.code[c.pc] = .push r b n) (hH : (c.space : ℤ) + P.k + 1 ≤ H) :
    ReachN (simOTM P) H (2 * (c.space + P.k) + 5) (repr P c) (repr P (P.step c)) := by
  have hI : instrAt P ⟨c.pc, hpc⟩ = .push r b n := hi
  have hstep : P.step c = ⟨n, Function.update c.regs r (b :: c.regs r)⟩ := by
    unfold Prog.step; rw [List.getElem?_eq_getElem hpc, hi]
  have hentry : entry P c.pc = rS P ⟨c.pc, hpc⟩ 0 .nav :=
    entry_eq_rS P c.pc hpc (by rw [hi]; simp) (by rw [hi]; simp)
  obtain ⟨A, B, hsplit, hAlen, hupd⟩ := decomp P c r
  have hm := length_encT_ofFn P c
  have hKl : A.length + 1 + B.length = P.k := by
    have := congrArg List.length hsplit; simp at this; omega
  have hlenAB : ((encT (List.ofFn c.regs)).length : ℤ) =
      (encT A).length + (encT (c.regs r :: B)).length := by
    rw [hsplit, encT_append]; simp
  have hlen := length_encT_cons_int (c.regs r) B
  have hsw : switchMode (instrAt P ⟨c.pc, hpc⟩) (c.regs r).head? = .carry (some b) := by
    rw [hI]; rfl
  have hdel : delMode (instrAt P ⟨c.pc, hpc⟩) none = none := by rw [hI]; rfl
  have hnext : nextPC (instrAt P ⟨c.pc, hpc⟩) none = n := by rw [hI]; rfl
  unfold repr
  rw [hentry, hstep]
  dsimp only
  rw [hupd]
  have hL0 : encT (List.ofFn c.regs) =
      encT A ++ (c.regs r).head? :: (encT (c.regs r :: B)).tail := by
    rw [hsplit, encT_append, ← encT_cons]
  have h1 := navSwitchN P (H := H) ⟨c.pc, hpc⟩ A _ _ _ hL0 (by rw [hI]; exact hAlen)
    (by rw [hI]; change (r : ℕ) ≤ P.k; omega) (by omega)
  rw [hsw] at h1
  obtain ⟨w, c', hw, h2⟩ := carryUnitsN P (H := H) ⟨c.pc, hpc⟩ (c.regs r :: B) A.length (some b)
    (encT A) [] (encT (List.ofFn c.regs)) (encT A).length
    ((encT A).length + (encT (c.regs r :: B)).length) (by simp; omega)
    (by rw [hsplit, encT_append]; simp) rfl rfl (by omega)
  rw [show A.length + (c.regs r :: B).length = P.k by simp; omega] at h2
  have hwlen : w.length = (encT (c.regs r :: B)).length := by
    have := congrArg List.length hw; simp at this; omega
  have hm' : ((encT A).length : ℤ) + (encT (c.regs r :: B)).length =
      ((encT A ++ (w ++ [])).length : ℤ) := by simp [hwlen]
  have hnew : encT A ++ (w ++ []) ++ [c'] = encT (A ++ (b :: c.regs r) :: B) := by
    rw [List.append_nil, List.append_assoc, ← hw, ← encT_cons_cons, ← encT_append]
  have hnewlen : ((encT (A ++ (b :: c.regs r) :: B)).length : ℤ) =
      (encT A ++ (w ++ [])).length + 1 := by
    rw [← hnew]; simp; omega
  have hX : ((encT A ++ (w ++ [])).length : ℤ) =
      (encT A).length + (encT (c.regs r :: B)).length := by simp [hwlen]
  have hmZ : ((encT (List.ofFn c.regs)).length : ℤ) = c.space + P.k := by
    rw [hm]; push_cast; ring
  have hXH : ((encT A ++ (w ++ [])).length : ℤ) + 1 ≤ H := by omega
  refine ((h1.trans h2).trans (n₂ := (encT (A ++ (b :: c.regs r) :: B)).length + 3) ?_).mono
    (by omega)
  rw [← hX]
  refine reachN_right P (n := (encT (A ++ (b :: c.regs r) :: B)).length + 2)
    (rS_ne P _ _ le_rfl _) (δ_carry_end P ⟨c.pc, hpc⟩ c' _) (by omega) (by omega) ?_
  rw [update_render_length, hnew]
  refine reachN_left P (n := (encT (A ++ (b :: c.regs r) :: B)).length + 1) (by simp)
    (δ_turn P ⟨c.pc, hpc⟩ none _) (by omega) hXH ?_
  rw [update_read, hdel]
  have h3 := sweepHomeN P (H := H) ⟨c.pc, hpc⟩ none (A ++ (b :: c.regs r) :: B) []
    (encT (A ++ (b :: c.regs r) :: B)) P.k ((encT A ++ (w ++ [])).length + 1 - 1) (by simp)
    (by simp; omega) (by simp; omega) (by omega) (by omega) (by omega)
  rw [hnext] at h3
  exact h3

/-- Macro step for `test` (counted): navigate, read the top, sweep to the end, turn, sweep
home. -/
theorem macro_testN {H : ℤ} (c : PConfig P) (hpc : c.pc < P.code.length) (r : Fin P.k)
    (i0 i1 i2 : ℕ) (hi : P.code[c.pc] = .test r i0 i1 i2) (hH : (c.space : ℤ) + P.k + 1 ≤ H) :
    ReachN (simOTM P) H (2 * (c.space + P.k) + 5) (repr P c) (repr P (P.step c)) := by
  have hI : instrAt P ⟨c.pc, hpc⟩ = .test r i0 i1 i2 := hi
  have hstep : P.step c = ⟨nextPC (instrAt P ⟨c.pc, hpc⟩) (c.regs r).head?, c.regs⟩ := by
    rw [hI]
    simp only [Prog.step, List.getElem?_eq_getElem hpc, hi]
    congr 1
    rcases c.regs r with _ | ⟨_ | _, _⟩ <;> rfl
  have hentry := entry_eq_rS P c.pc hpc (by rw [hi]; simp) (by rw [hi]; simp)
  obtain ⟨A, B, hsplit, hAlen, -⟩ := decomp P c r
  have hm := length_encT_ofFn P c
  have hKl : (A ++ c.regs r :: B).length = P.k := by rw [← hsplit]; simp
  have hEq : (encT (A ++ c.regs r :: B)).length = (encT (List.ofFn c.regs)).length := by
    rw [hsplit]
  have hdel : delMode (instrAt P ⟨c.pc, hpc⟩) (c.regs r).head? = none := by rw [hI]; rfl
  unfold repr
  rw [hentry, hstep]
  dsimp only
  have h1 := navDoneTurnN P (H := H) ⟨c.pc, hpc⟩ A (c.regs r) B (encT (List.ofFn c.regs))
    (by rw [hsplit]) (by rw [hI]; exact hAlen) hKl (by rw [hI]; rfl) (by rw [← hsplit]; omega)
  rw [hdel] at h1
  refine (h1.trans (n₂ := (encT (List.ofFn c.regs)).length + 1) ?_).mono (by omega)
  exact sweepHomeN P (H := H) ⟨c.pc, hpc⟩ (c.regs r).head? (List.ofFn c.regs) []
    (encT (List.ofFn c.regs)) P.k _ (by simp) (by simp) (by simp) (by rw [hsplit]; simp)
    (by rw [← hsplit]; omega) (by omega)

/-- Macro step for `pop` (counted): as `test`, deleting the top on the way back if it exists. -/
theorem macro_popN {H : ℤ} (c : PConfig P) (hpc : c.pc < P.code.length) (r : Fin P.k) (n : ℕ)
    (hi : P.code[c.pc] = .pop r n) (hH : (c.space : ℤ) + P.k + 1 ≤ H) :
    ReachN (simOTM P) H (2 * (c.space + P.k) + 5) (repr P c) (repr P (P.step c)) := by
  have hI : instrAt P ⟨c.pc, hpc⟩ = .pop r n := hi
  have hstep : P.step c = ⟨n, Function.update c.regs r (c.regs r).tail⟩ := by
    unfold Prog.step; rw [List.getElem?_eq_getElem hpc, hi]
  have hentry := entry_eq_rS P c.pc hpc (by rw [hi]; simp) (by rw [hi]; simp)
  obtain ⟨A, B, hsplit, hAlen, hupd⟩ := decomp P c r
  have hm := length_encT_ofFn P c
  unfold repr
  rw [hentry, hstep]
  dsimp only
  rw [hupd]
  generalize hs : c.regs r = s at hsplit ⊢
  have hKl : (A ++ s :: B).length = P.k := by rw [← hsplit]; simp
  have hEq : (encT (A ++ s :: B)).length = (encT (List.ofFn c.regs)).length := by rw [hsplit]
  have h1 := navDoneTurnN P (H := H) ⟨c.pc, hpc⟩ A s B (encT (List.ofFn c.regs))
    (by rw [hsplit]) (by rw [hI]; exact hAlen) hKl (by rw [hI]; rfl) (by rw [← hsplit]; omega)
  refine (h1.trans (n₂ := (encT (List.ofFn c.regs)).length + 3) ?_).mono (by omega)
  cases s with
  | nil =>
    have hdel : delMode (instrAt P ⟨c.pc, hpc⟩) ([] : BitString).head? = none := by rw [hI]; rfl
    have hnext : nextPC (instrAt P ⟨c.pc, hpc⟩) ([] : BitString).head? = n := by rw [hI]; rfl
    rw [hdel]
    have h3 := sweepHomeN P (H := H) ⟨c.pc, hpc⟩ ([] : BitString).head? (A ++ [] :: B) []
      (encT (List.ofFn c.regs)) P.k (((encT (A ++ [] :: B)).length : ℤ) - 1)
      (by rw [hsplit]; simp) (by simp at hKl ⊢; omega) (by simp at hKl ⊢; omega)
      (by simp) (by rw [← hsplit]; omega) (by omega)
    rw [hnext] at h3
    have e : encT (A ++ ([] : BitString).tail :: B) = encT (List.ofFn c.regs) := by rw [hsplit]; rfl
    rw [e]
    exact h3.mono (by omega)
  | cons t s' =>
    have hdel : delMode (instrAt P ⟨c.pc, hpc⟩) (t :: s').head? = some none := by rw [hI]; rfl
    have hnext : nextPC (instrAt P ⟨c.pc, hpc⟩) (some t) = n := by rw [hI]; rfl
    rw [hdel]
    have hlenAB : ((encT (A ++ (t :: s') :: B)).length : ℤ) =
        (encT A).length + (encT ((t :: s') :: B)).length := by rw [encT_append]; simp
    obtain ⟨w, c'', hw, h2⟩ := delSweepN P (H := H) ⟨c.pc, hpc⟩ (t :: s').head? A.length
      (by rw [hI]; change (r : ℕ) ≤ A.length; omega) (encT ((t :: s') :: B)).reverse P.k none
      (encT A) [] (encT (List.ofFn c.regs)) ((encT (A ++ (t :: s') :: B)).length - 1)
      (by rw [hsplit, encT_append]; simp)
      (by rw [List.count_reverse, count_encT]; simp at hKl ⊢; omega) le_rfl
      (by rw [List.length_reverse]; omega) (by rw [← hsplit]; omega)
    rw [List.reverse_reverse, encT_cons_cons] at hw
    simp only [List.cons_append, List.cons.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hf : ((encT (List.ofFn c.regs)).length : ℤ) =
        (encT A).length + (encT ((t :: s') :: B)).length := by rw [hsplit, encT_append]; simp
    refine (h2.trans (n₂ := (encT A).length + 2) ?_).mono
      (by simp only [List.length_reverse]; omega)
    have hread : render (encT A ++ (encT (s' :: B) ++ [none] ++ [])) ((encT A).length - 1) =
        none := render_before_encT A _
    have hAk : A.length ≤ P.k := by simp at hKl; omega
    have hδ := δ_del_stop P ⟨c.pc, hpc⟩ (t :: s').head? A.length hAk (by rw [hI]; exact hAlen)
      (some t)
    refine reachN_step P (n := (encT A).length + 1)
      (lS_ne P ⟨c.pc, hpc⟩ (t :: s').head? A.length hAk (some (some t)))
      (by rw [hread]; exact hδ) (by omega) (by omega) ?_
    rw [update_same hread]
    have h3 := sweepHomeN P (H := H) ⟨c.pc, hpc⟩ (some t) A (encT (s' :: B) ++ [none] ++ [])
      (encT A ++ (encT (s' :: B) ++ [none] ++ [])) A.length ((encT A).length - 1) rfl rfl
      (by simp at hKl; omega) (by ring) (by omega) (by omega)
    rw [hnext] at h3
    have htape : render (encT A ++ (encT (s' :: B) ++ [none] ++ [])) =
        render (encT (A ++ (t :: s').tail :: B)) := by
      rw [List.append_nil, ← List.append_assoc, render_append_none, encT_append]; rfl
    rw [← htape]
    exact h3

/-- **Counted macro step.**  One instruction of `P` is simulated in at most
`2 * (space + k) + 5` steps, all heads staying in `[-1, H]`. -/
theorem macroStepN (c : PConfig P) (hnh : ¬ P.Halted c) (H : ℤ)
    (hH : (c.space : ℤ) + P.k + 1 ≤ H) :
    ReachN (simOTM P) H (2 * (c.space + P.k) + 5) (repr P c) (repr P (P.step c)) := by
  unfold Prog.Halted at hnh
  simp only [not_or] at hnh
  obtain ⟨h1, h2, h3⟩ := hnh
  have hpc : c.pc < P.code.length := by
    by_contra hc; exact h3 (List.getElem?_eq_none (by omega))
  rw [List.getElem?_eq_getElem hpc] at h1 h2
  cases hi : P.code[c.pc] with
  | push r b n => exact macro_pushN P c hpc r b n hi hH
  | pop r n => exact macro_popN P c hpc r n hi hH
  | test r i0 i1 i2 => exact macro_testN P c hpc r i0 i1 i2 hi hH
  | accept => exact absurd (by rw [hi]) h1
  | reject => exact absurd (by rw [hi]) h2

/-- **Counted global simulation.**  The configuration of `P` at time `s` is represented at some
time `T ≤ s * (2 * (S + k) + 5)`, all heads so far lying in `[-1, S + k + 1]`. -/
theorem globalN (hK : 0 < P.k) (x : BitString) (S : ℕ) :
    ∀ s : ℕ, (∀ s' ≤ s, (P.run x s').space ≤ S) →
      ∃ T, T ≤ s * (2 * (S + P.k) + 5) ∧ run (simOTM P) ∅ x T = repr P (P.run x s) ∧
        ∀ e ≤ T, -1 ≤ (run (simOTM P) ∅ x e).head ∧
          (run (simOTM P) ∅ x e).head ≤ (S : ℤ) + P.k + 1
  | 0, _ => ⟨0, Nat.zero_le _, init_repr P hK x, fun e he => by
      obtain rfl : e = 0 := by omega
      rw [init_repr P hK x]
      exact ⟨by simp [repr], by simp [repr]; omega⟩⟩
  | s + 1, hs => by
    obtain ⟨T, hTle, hT, hb⟩ := globalN hK x S s (fun s' hs' => hs s' (by omega))
    by_cases hh : P.Halted (P.run x s)
    · refine ⟨T, hTle.trans (Nat.mul_le_mul (by omega) le_rfl), ?_, hb⟩
      change _ = repr P (P.step (P.run x s))
      rw [P.step_of_halted _ hh]; exact hT
    · have hsp := hs s (by omega)
      obtain ⟨d, hdle, hd, hdb⟩ :=
        (macroStepN P (P.run x s) hh ((S : ℤ) + P.k + 1) (by omega)).iterate
      refine ⟨T + d, ?_, ?_, fun e he => ?_⟩
      · rw [add_mul, one_mul]; omega
      · rw [run_add, hT]; exact hd
      · rcases Nat.lt_or_ge e T with h | h
        · exact hb e h.le
        · obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le h
          rw [run_add, hT]; exact hdb e' (by omega)

end StackSim

/-- **Simulation with a time bound.**  Every stack program is simulated by a one-tape oracle-free
machine with linear space overhead and time overhead `O((space + k) · t)`: if `P` halts on `x` at
time `t` with all configurations up to then of space `≤ S`, the machine halts on `x` within
`C * (t + 1) * (S + 1)` steps having scanned at most `C * (S + 1)` cells, and accepts iff `P` is
accepting at time `t`.  The machine is `StackSim.simOTM P` and `C = 2 * P.k + 5`. -/
theorem Prog.exists_sim_time (P : Prog) : ∃ (M : OTM) (C : ℕ), ∀ (x : BitString) (t S : ℕ),
    P.Halted (P.run x t) → (∀ s ≤ t, (P.run x s).space ≤ S) →
    ∃ u, u ≤ C * (t + 1) * (S + 1) ∧
      Kolmogorov.RandomStrings.Halted M (Kolmogorov.RandomStrings.run M ∅ x u) ∧
      (visited M ∅ x u).card ≤ C * (S + 1) ∧
      (Accepts M ∅ x ↔ P.Accepting (P.run x t)) := by
  refine ⟨StackSim.simOTM P, 2 * P.k + 5, fun x t S ht hsp => ?_⟩
  rcases Nat.eq_zero_or_pos P.k with hK | hK
  · obtain ⟨hM, hcard, hacc⟩ := StackSim.exists_sim_zero P hK x t
    exact ⟨0, Nat.zero_le _, hM, hcard.trans (by rw [hK]; omega), hacc⟩
  · obtain ⟨T, hTle, hT, hb⟩ := StackSim.globalN P hK x S t hsp
    have hHalt : Kolmogorov.RandomStrings.Halted (StackSim.simOTM P)
        (Kolmogorov.RandomStrings.run (StackSim.simOTM P) ∅ x T) := by
      rw [hT]; exact StackSim.halted_entry P _ ht
    refine ⟨T, hTle.trans ?_, hHalt, ?_, ?_⟩
    · have h1 : 2 * (S + P.k) + 5 ≤ (2 * P.k + 5) * (S + 1) := by nlinarith
      calc t * (2 * (S + P.k) + 5) ≤ t * ((2 * P.k + 5) * (S + 1)) := Nat.mul_le_mul le_rfl h1
        _ ≤ (t + 1) * ((2 * P.k + 5) * (S + 1)) := Nat.mul_le_mul (by omega) le_rfl
        _ = (2 * P.k + 5) * (t + 1) * (S + 1) := by ring
    · calc (visited (StackSim.simOTM P) ∅ x T).card
          ≤ (Finset.Icc (-1 : ℤ) ((S : ℤ) + P.k + 1)).card := by
            apply Finset.card_le_card
            intro z hz
            simp only [visited, Finset.mem_image, Finset.mem_range] at hz
            obtain ⟨e, he, rfl⟩ := hz
            exact Finset.mem_Icc.2 (hb e (by omega))
        _ ≤ (2 * P.k + 5) * (S + 1) := by
            rw [Int.card_Icc]
            have : ((S : ℤ) + P.k + 1 + 1 - -1).toNat = S + P.k + 3 := by omega
            rw [this]; nlinarith [Nat.zero_le (P.k * S)]
    · rw [accepts_iff_of_halted _ ∅ x T hHalt, hT]
      exact StackSim.entry_acc_iff P _

/-- Arithmetic: `C (2^P + 1)^2 ≤ 2^(P + P + C + 2)`. -/
theorem mul_sq_two_pow_le (C P : ℕ) : C * (2 ^ P + 1) * (2 ^ P + 1) ≤ 2 ^ (P + P + (C + 2)) := by
  have h1 : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
  have h2 : 2 ^ P + 1 ≤ 2 * 2 ^ P := by have := Nat.one_le_two_pow (n := P); omega
  have h3 : 2 ^ (P + P + (C + 2)) = 2 ^ C * (2 * 2 ^ P) * (2 * 2 ^ P) := by
    rw [pow_add, pow_add, pow_add]; ring
  rw [h3]
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h2

/-- A stack program halting within `2 ^ p(n)` steps (and space) decides a set in `EXP`: the
simulating one-tape machine halts within `C (2^p(n) + 1)^2 ≤ 2 ^ (2 p(n) + C + 2)` steps. -/
theorem Prog.lang_mem_EXP (P : Prog) (p : Polynomial ℕ) (hP : P.TimeBounded p) :
    P.Lang ∈ EXP := by
  obtain ⟨M, C, hM⟩ := P.exists_sim_time
  refine ⟨M, p + p + Polynomial.C (C + 2), fun x => ?_, fun x => ?_⟩
  · obtain ⟨t, ht, hh, hsp⟩ := hP x
    obtain ⟨u, hu, hhu, -, -⟩ := hM x t _ hh hsp
    refine ⟨u, hu.trans ?_, hhu⟩
    rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_C]
    calc C * (t + 1) * (2 ^ p.eval x.length + 1)
        ≤ C * (2 ^ p.eval x.length + 1) * (2 ^ p.eval x.length + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) le_rfl
      _ ≤ _ := mul_sq_two_pow_le C _
  · obtain ⟨t, -, hh, hsp⟩ := hP x
    obtain ⟨u, -, -, -, hacc⟩ := hM x t _ hh hsp
    rw [P.mem_lang_iff_of_halted x t hh, hacc]

/-! ### `EXP` is closed under finite modifications -/

/-- The modified machine on a string `x ≠ z` reaches `M.start` at cell `0` within `2 |z| + 2`
steps. -/
theorem modOTM_prefix_time (M : OTM) (z : BitString) (b : Bool) (x : BitString) (hxz : x ≠ z) :
    ∃ t0, t0 ≤ 2 * z.length + 2 ∧ run (modOTM M z b) ∅ x t0 = modEmbed M z b (init M x) := by
  obtain ⟨i, hi, hne, hagree⟩ := exists_mismatch x z hxz
  have h1 := mod_run_mismatch M z b ∅ x i hi hagree hne
  have h2 := mod_run_back M z b ∅ x (i + 1) i hi h1 i le_rfl
  have h3 := mod_run_start M z b ∅ x (i + 1 + i) ⟨i - i, by omega⟩ (by simp) _ (by simp) h2
  exact ⟨i + 1 + i + 1, by omega, h3⟩

/-- Halting time of the modified machine: if `M` halts on `x` at time `t`, then `modOTM M z b`
halts on `x` within `t + 2 |z| + 3` steps. -/
theorem modOTM_spec_time (M : OTM) (z : BitString) (b : Bool) (x : BitString) (t : ℕ)
    (ht : Halted M (run M ∅ x t)) :
    ∃ u, u ≤ t + 2 * z.length + 3 ∧ Halted (modOTM M z b) (run (modOTM M z b) ∅ x u) ∧
      (Accepts (modOTM M z b) ∅ x ↔ if x = z then b = true else Accepts M ∅ x) := by
  classical
  by_cases hxz : x = z
  · rw [hxz]
    obtain ⟨hh, -, ha⟩ := modOTM_spec_self M z b
    exact ⟨z.length + 1, by omega, hh, by rw [ite_eq_left rfl]; exact ha⟩
  · obtain ⟨t0, ht0, h0⟩ := modOTM_prefix_time M z b x hxz
    have hex : ∃ t, Halted M (run M ∅ x t) := ⟨t, ht⟩
    have hts_h : Halted M (run M ∅ x (Nat.find hex)) := Nat.find_spec hex
    have hts_le : Nat.find hex ≤ t := Nat.find_min' hex ht
    have hnh : ∀ t' < Nat.find hex, ¬ Halted M (run M ∅ x t') := fun t' h => Nat.find_min hex h
    have hsim := mod_run_sim M z b x t0 h0
    have hrun : run (modOTM M z b) ∅ x (t0 + Nat.find hex) =
        modEmbed M z b (run M ∅ x (Nat.find hex)) := hsim _ hnh
    have hfin : run (modOTM M z b) ∅ x (t0 + Nat.find hex + 1) =
        ⟨Sum.inr (Sum.inr (Sum.inr (decide ((run M ∅ x (Nat.find hex)).q = M.accept)))),
          (run M ∅ x (Nat.find hex)).tape, (run M ∅ x (Nat.find hex)).head,
          (run M ∅ x (Nat.find hex)).buf⟩ := by
      change step _ ∅ (run _ ∅ x (t0 + Nat.find hex)) = _
      rw [hrun]
      by_cases ha : (run M ∅ x (Nat.find hex)).q = M.accept
      · rw [mod_step_embed_accept M z b ∅ _ ha]; simp [ha]
      · rw [mod_step_embed_reject M z b ∅ _ ha (hts_h.resolve_left ha)]; simp [ha]
    have hhalt : Halted (modOTM M z b) (run (modOTM M z b) ∅ x (t0 + Nat.find hex + 1)) := by
      rw [hfin]; exact mod_halted_fin M z b _ _ _ _
    refine ⟨t0 + Nat.find hex + 1, by omega, hhalt, ?_⟩
    rw [ite_eq_right hxz, accepts_iff_of_halted _ _ _ _ hhalt, hfin,
      accepts_iff_of_halted M ∅ x _ hts_h]
    simp [modOTM]

/-- Changing a set at a single string does not leave `EXP`: compare the input with the
hardwired string `z`, answer directly on `z`, and otherwise run the machine for `A`; the extra
time is at most `2 |z| + 3` steps. -/
theorem EXP_modify_one (A A' : Set BitString) (hA : A ∈ EXP) (z : BitString)
    (h : ∀ x, x ≠ z → (x ∈ A' ↔ x ∈ A)) : A' ∈ EXP := by
  classical
  obtain ⟨M, p, hM, hAM⟩ := hA
  refine ⟨modOTM M z (decide (z ∈ A')), p + Polynomial.C (2 * z.length + 2 + 1), fun x => ?_,
    fun x => ?_⟩
  · obtain ⟨t, ht, hh⟩ := hM x
    obtain ⟨u, hu, hhu, -⟩ := modOTM_spec_time M z (decide (z ∈ A')) x t hh
    refine ⟨u, hu.trans ?_, hhu⟩
    rw [Polynomial.eval_add, Polynomial.eval_C]
    calc t + 2 * z.length + 3 ≤ 2 * z.length + 2 + 1 + 2 ^ p.eval x.length := by omega
      _ ≤ _ := add_two_pow_le _ _
  · obtain ⟨t, -, ht⟩ := hM x
    obtain ⟨u, -, -, hacc⟩ := modOTM_spec_time M z (decide (z ∈ A')) x t ht
    rw [hacc]
    by_cases hxz : x = z
    · subst hxz; simp
    · rw [ite_eq_right hxz, h x hxz, hAM x]

/-- Finite modifications do not leave `EXP`: if `A` agrees with an `EXP` set on all strings
beyond a finite set, then `A ∈ EXP`. -/
theorem EXP_of_eventually_eq (A B : Set BitString) (hB : B ∈ EXP) (Z : Finset BitString)
    (h : ∀ x, x ∉ Z → (x ∈ A ↔ x ∈ B)) : A ∈ EXP := by
  classical
  induction Z using Finset.induction_on generalizing A with
  | empty =>
    have hAB : A = B := Set.ext fun x => h x (Finset.notMem_empty x)
    rw [hAB]; exact hB
  | @insert z Z hz ih =>
    let A' : Set BitString := {x | if x = z then x ∈ B else x ∈ A}
    have hA' : A' ∈ EXP := ih A' fun x hx => by
      by_cases hxz : x = z
      · simp [A', hxz]
      · simp only [A', Set.mem_ofPred_eq, ite_eq_right hxz]
        exact h x (by simp [hxz, hx])
    exact EXP_modify_one A' A hA' z fun x hxz => by simp [A', hxz]

/-- `EXP_of_eventually_eq` with the arguments in the order of the closure hypothesis `hclosed`
of `general`. -/
theorem EXP_of_eventually_eq' (A B : Set BitString) (Z : Finset BitString) (hB : B ∈ EXP)
    (h : ∀ x, x ∉ Z → (x ∈ A ↔ x ∈ B)) : A ∈ EXP :=
  EXP_of_eventually_eq A B hB Z h

/-! ### Simple inclusions -/

/-- `EXP ⊆ EXPSPACE`: in `t ≤ 2 ^ p(n)` steps at most `t + 1 ≤ 2 ^ (p(n) + 1)` cells are scanned. -/
theorem EXP_subset_EXPSPACE : EXP ⊆ EXPSPACE := by
  rintro A ⟨M, p, hM, hA⟩
  refine ⟨M, p + 1, fun x => ?_, hA⟩
  obtain ⟨t, ht, hh⟩ := hM x
  refine ⟨t, hh, (visited_card_le M ∅ x t).trans ?_⟩
  rw [Polynomial.eval_add, Polynomial.eval_one, pow_succ]
  have := Nat.one_le_two_pow (n := p.eval x.length)
  omega

/-- `P ⊆ EXP`: a machine halting within `p(n)` steps halts within `2 ^ p(n)` steps. -/
theorem polyTimeOracle_empty_subset_EXP : PolyTimeOracle ∅ ⊆ EXP := by
  rintro A ⟨M, p, hp, hA⟩
  refine ⟨M, p, fun x => ?_, hA⟩
  obtain ⟨t, ht, hh⟩ := hp x
  exact ⟨t, ht.trans Nat.lt_two_pow_self.le, hh⟩

/-! ### A time bound alone suffices -/

/-- One step of a stack program adds at most one bit. -/
theorem Prog.space_step_le (P : Prog) (c : PConfig P) : (P.step c).space ≤ c.space + 1 := by
  unfold Prog.step
  split
  · next r b n _ =>
    change Stacks.space (Function.update c.regs r (b :: c.regs r)) ≤ c.space + 1
    rw [Stacks.space_update_cons]; rfl
  · next r n _ =>
    change Stacks.space (Function.update c.regs r (c.regs r).tail) ≤ c.space + 1
    exact (Stacks.space_update_tail_le c.regs r).trans (Nat.le_succ _)
  · exact Nat.le_succ _
  · exact Nat.le_succ _

/-- The initial configuration has space `|x|` (or `0` if there are no stacks). -/
theorem Prog.space_init_le (P : Prog) (x : BitString) : (P.init x).space ≤ x.length := by
  change ∑ r : Fin P.k, ((if r.val = 0 then x else []) : BitString).length ≤ x.length
  generalize P.k = k
  cases k with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_succ]
    simp

/-- The space after `s` steps is at most `|x| + s`. -/
theorem Prog.space_run_le (P : Prog) (x : BitString) (s : ℕ) :
    (P.run x s).space ≤ x.length + s := by
  induction s with
  | zero => exact P.space_init_le x
  | succ s ih => exact (P.space_step_le _).trans (by omega)

/-- A stack program halting within `2 ^ p(|x|)` steps is `TimeBounded` by `p + X + 1` (its space
never exceeds `|x| + 2 ^ p(|x|)`). -/
theorem Prog.timeBounded_of_time (P : Prog) (p : Polynomial ℕ)
    (h : ∀ x : BitString, ∃ t ≤ 2 ^ p.eval x.length, P.Halted (P.run x t)) :
    P.TimeBounded (p + Polynomial.X + 1) := by
  intro x
  obtain ⟨t, ht, hh⟩ := h x
  have he : (p + Polynomial.X + 1).eval x.length = p.eval x.length + (x.length + 1) := by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]; ring
  have hb : x.length + 2 ^ p.eval x.length ≤ 2 ^ (p + Polynomial.X + 1).eval x.length := by
    rw [he]; have := add_two_pow_le x.length (p.eval x.length); omega
  refine ⟨t, by omega, hh, fun s hs => (P.space_run_le x s).trans (by omega)⟩

/-- A stack program halting within `2 ^ p(|x|)` steps decides a set in `EXP`. -/
theorem Prog.lang_mem_EXP_of_time (P : Prog) (p : Polynomial ℕ)
    (h : ∀ x : BitString, ∃ t ≤ 2 ^ p.eval x.length, P.Halted (P.run x t)) : P.Lang ∈ EXP :=
  P.lang_mem_EXP _ (P.timeBounded_of_time p h)

end Kolmogorov.RandomStrings
