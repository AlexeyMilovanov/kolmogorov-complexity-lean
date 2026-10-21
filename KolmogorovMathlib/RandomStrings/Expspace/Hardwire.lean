/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.Stmt

/-!
# Hardwiring one string into a machine

The modified machine `modOTM M z b`, which answers `b` on the input `z` and behaves as `M`
elsewhere, its correctness `modOTM_spec`, and the closure of `EXPSPACE` under finite modifications
(`EXPSPACE_modify_one`, `EXPSPACE_of_eventually_eq`).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-! ### Hardwiring one string into a machine -/

/-- The input tape on input `x`. -/
def tapeOf (x : BitString) : ℤ → Sym := fun i => if 0 ≤ i then x[i.toNat]? else none

/-- States of the modified machine: the states of `M`, comparison states `cmp i`, return states
`back j` (`i, j ≤ |z|`), and fresh halting states `fin true` (accept), `fin false` (reject). -/
abbrev ModQ (M : OTM) (n : ℕ) : Type := M.Q ⊕ (Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Bool))

open Classical in
/-- The transitions of the modified machine. -/
noncomputable def modδ (M : OTM) (z : BitString) (b : Bool) :
    ModQ M z.length → Sym → Act (ModQ M z.length)
  | Sum.inl q, s =>
      if q = M.accept then .step (Sum.inr (Sum.inr (Sum.inr true))) s .stay
      else if q = M.reject then .step (Sum.inr (Sum.inr (Sum.inr false))) s .stay
      else (M.δ q s).map Sum.inl
  | Sum.inr (Sum.inl i), s =>
      if s = z[i.val]? then
        (if h : i.val < z.length then .step (Sum.inr (Sum.inl ⟨i.val + 1, by omega⟩)) s .right
          else .step (Sum.inr (Sum.inr (Sum.inr b))) s .stay)
      else .step (Sum.inr (Sum.inr (Sum.inl i))) s .stay
  | Sum.inr (Sum.inr (Sum.inl j)), s =>
      if h : j.val = 0 then .step (Sum.inl M.start) s .stay
      else .step (Sum.inr (Sum.inr (Sum.inl ⟨j.val - 1, by have := j.isLt; omega⟩))) s .left
  | Sum.inr (Sum.inr (Sum.inr v)), s => .step (Sum.inr (Sum.inr (Sum.inr v))) s .stay

/-- The modified machine: compare the input with `z`; on `z` answer `b`; otherwise return the head
to cell `0` and run `M`, halting in a fresh state one step after `M` halts. -/
noncomputable def modOTM (M : OTM) (z : BitString) (b : Bool) : OTM where
  Q := ModQ M z.length
  fin := inferInstance
  start := Sum.inr (Sum.inl 0)
  accept := Sum.inr (Sum.inr (Sum.inr true))
  reject := Sum.inr (Sum.inr (Sum.inr false))
  δ := modδ M z b

/-- In the comparison state `cmp i`, on a symbol `s` equal to `z[i]?` the modified machine
moves right to `cmp (i + 1)` (or, when `i = |z|`, stays and enters `fin b`); on any other symbol
it goes to the return state `back i` without moving. -/
theorem modOTM_δ_cmp (M : OTM) (z : BitString) (b : Bool) (i : Fin (z.length + 1)) (s : Sym) :
    (modOTM M z b).δ (Sum.inr (Sum.inl i)) s =
      if s = z[i.val]? then
        (if h : i.val < z.length then .step (Sum.inr (Sum.inl ⟨i.val + 1, by omega⟩)) s .right
          else .step (Sum.inr (Sum.inr (Sum.inr b))) s .stay)
      else .step (Sum.inr (Sum.inr (Sum.inl i))) s .stay := rfl

/-- In the return state `back j` the modified machine moves left to `back (j - 1)`; in `back 0`
it enters the start state of `M` without moving. -/
theorem modOTM_δ_back (M : OTM) (z : BitString) (b : Bool) (j : Fin (z.length + 1)) (s : Sym) :
    (modOTM M z b).δ (Sum.inr (Sum.inr (Sum.inl j))) s =
      if _h : j.val = 0 then .step (Sum.inl M.start) s .stay
      else .step (Sum.inr (Sum.inr (Sum.inl ⟨j.val - 1, by have := j.isLt; omega⟩))) s .left :=
  rfl

open Classical in
/-- On a state `q` of `M` the modified machine takes the action `M.δ q s`, with next states
embedded by `Sum.inl`; only at `M.accept` and `M.reject` it instead enters the fresh halting
states `fin true` and `fin false`, without moving. -/
theorem modOTM_δ_inl (M : OTM) (z : BitString) (b : Bool) (q : M.Q) (s : Sym) :
    (modOTM M z b).δ (Sum.inl q) s =
      if q = M.accept then .step (Sum.inr (Sum.inr (Sum.inr true))) s .stay
      else if q = M.reject then .step (Sum.inr (Sum.inr (Sum.inr false))) s .stay
      else (M.δ q s).map Sum.inl := rfl

/-- One `step` action, unfolded. -/
theorem step_eq_of_δ (M : OTM) (B : Set BitString) (c : Config M) (hc : ¬ Halted M c) {q' : M.Q}
    {a : Sym} {m : Move} (h : M.δ c.q (c.tape c.head) = .step q' a m) :
    step M B c = ⟨q', Function.update c.tape c.head a, moveHead m c.head, c.buf⟩ := by
  unfold step
  rw [ite_eq_right hc, h]

/-- At a cell `i : ℕ` the input tape `tapeOf x` holds `x[i]?`, the bit of `x` at position `i`
(blank past the end of `x`). -/
theorem tapeOf_natCast (x : BitString) (i : ℕ) : tapeOf x (i : ℤ) = x[i]? := by
  simp [tapeOf]

/-- Comparison phase: while `x` agrees with `z`, the machine walks right in state `cmp i`. -/
theorem mod_run_cmp (M : OTM) (z : BitString) (b : Bool) (B : Set BitString) (x : BitString) :
    ∀ (i : ℕ) (hi : i < z.length + 1), (∀ j < i, x[j]? = z[j]?) →
      run (modOTM M z b) B x i = ⟨Sum.inr (Sum.inl ⟨i, hi⟩), tapeOf x, i, []⟩ := by
  intro i
  induction i with
  | zero => intro hi _; rfl
  | succ i ih =>
    intro hi hx
    have ih' := ih (by omega) (fun j hj => hx j (by omega))
    change step _ B (run _ B x i) = _
    rw [ih']
    have hcell : tapeOf x (i : ℤ) = z[i]? := by rw [tapeOf_natCast]; exact hx i (by omega)
    rw [step_eq_of_δ _ _ _ (by simp [Halted, modOTM]) (q' := Sum.inr (Sum.inl ⟨i + 1, hi⟩))
      (a := tapeOf x i) (m := .right)]
    · simp [moveHead, Function.update_eq_self]
    · change (modOTM M z b).δ (Sum.inr (Sum.inl ⟨i, by omega⟩)) (tapeOf x i) = _
      rw [modOTM_δ_cmp, ite_eq_left (by simpa using hcell),
        dite_eq_left (show i < z.length by omega)]

/-- A mismatch at cell `i` sends the machine to the return state `back i`. -/
theorem mod_run_mismatch (M : OTM) (z : BitString) (b : Bool) (B : Set BitString) (x : BitString)
    (i : ℕ) (hi : i < z.length + 1) (hx : ∀ j < i, x[j]? = z[j]?) (hne : x[i]? ≠ z[i]?) :
    run (modOTM M z b) B x (i + 1) = ⟨Sum.inr (Sum.inr (Sum.inl ⟨i, hi⟩)), tapeOf x, i, []⟩ := by
  change step _ B (run _ B x i) = _
  rw [mod_run_cmp M z b B x i hi hx]
  have hcell : ¬ tapeOf x (i : ℤ) = z[i]? := by rw [tapeOf_natCast]; exact hne
  rw [step_eq_of_δ _ _ _ (by simp [Halted, modOTM]) (q' := Sum.inr (Sum.inr (Sum.inl ⟨i, hi⟩)))
    (a := tapeOf x i) (m := .stay)]
  · simp [moveHead, Function.update_eq_self]
  · change (modOTM M z b).δ (Sum.inr (Sum.inl ⟨i, hi⟩)) (tapeOf x i) = _
    rw [modOTM_δ_cmp, ite_eq_right (by simpa using hcell)]

/-- On `z` itself the comparison succeeds and the machine halts in `fin b`. -/
theorem mod_run_match (M : OTM) (z : BitString) (b : Bool) (B : Set BitString) :
    run (modOTM M z b) B z (z.length + 1) =
      ⟨Sum.inr (Sum.inr (Sum.inr b)), tapeOf z, z.length, []⟩ := by
  change step _ B (run _ B z z.length) = _
  rw [mod_run_cmp M z b B z z.length (by omega) (fun _ _ => rfl)]
  have hcell : tapeOf z (z.length : ℤ) = z[z.length]? := tapeOf_natCast z _
  rw [step_eq_of_δ _ _ _ (by simp [Halted, modOTM]) (q' := Sum.inr (Sum.inr (Sum.inr b)))
    (a := tapeOf z z.length) (m := .stay)]
  · simp [moveHead, Function.update_eq_self]
  · change (modOTM M z b).δ (Sum.inr (Sum.inl ⟨z.length, by omega⟩)) (tapeOf z z.length) = _
    rw [modOTM_δ_cmp, ite_eq_left (by simpa using hcell), dite_eq_right (lt_irrefl z.length)]

/-- Return phase: from `back j` at cell `j`, the head walks back to cell `0`. -/
theorem mod_run_back (M : OTM) (z : BitString) (b : Bool) (B : Set BitString) (x : BitString)
    (t j : ℕ) (hj : j < z.length + 1)
    (h : run (modOTM M z b) B x t = ⟨Sum.inr (Sum.inr (Sum.inl ⟨j, hj⟩)), tapeOf x, j, []⟩) :
    ∀ k (hk : k ≤ j), run (modOTM M z b) B x (t + k) =
      ⟨Sum.inr (Sum.inr (Sum.inl ⟨j - k, by omega⟩)), tapeOf x, ((j - k : ℕ) : ℤ), []⟩ := by
  intro k
  induction k with
  | zero => intro _; simpa using h
  | succ k ih =>
    intro hk
    change step _ B (run _ B x (t + k)) = _
    rw [ih (by omega)]
    rw [step_eq_of_δ _ _ _ (by simp [Halted, modOTM])
      (q' := Sum.inr (Sum.inr (Sum.inl ⟨j - (k + 1), by omega⟩)))
      (a := tapeOf x ((j - k : ℕ) : ℤ)) (m := .left)]
    · have hh : ((j - k : ℕ) : ℤ) - 1 = ((j - (k + 1) : ℕ) : ℤ) := by omega
      simp only [moveHead, Function.update_eq_self, hh]
    · change (modOTM M z b).δ (Sum.inr (Sum.inr (Sum.inl ⟨j - k, by omega⟩)))
        (tapeOf x ((j - k : ℕ) : ℤ)) = _
      rw [modOTM_δ_back, dite_eq_right (by simp only; omega)]
      congr 3

/-- Leaving the return phase: from `back 0` at cell `0` the machine enters `M.start`. -/
theorem mod_run_start (M : OTM) (z : BitString) (b : Bool) (B : Set BitString) (x : BitString)
    (t : ℕ) (j : Fin (z.length + 1)) (hj : j.val = 0) (hd : ℤ) (hhd : hd = 0)
    (h : run (modOTM M z b) B x t = ⟨Sum.inr (Sum.inr (Sum.inl j)), tapeOf x, hd, []⟩) :
    run (modOTM M z b) B x (t + 1) = ⟨Sum.inl M.start, tapeOf x, 0, []⟩ := by
  subst hhd
  change step _ B (run _ B x t) = _
  rw [h]
  rw [step_eq_of_δ _ _ _ (by simp [Halted, modOTM]) (q' := Sum.inl M.start)
    (a := tapeOf x 0) (m := .stay)]
  · simp [moveHead, Function.update_eq_self]
  · change (modOTM M z b).δ (Sum.inr (Sum.inr (Sum.inl j))) (tapeOf x 0) = _
    rw [modOTM_δ_back, dite_eq_left hj]

/-- Embedding of the configurations of `M`. -/
def modEmbed (M : OTM) (z : BitString) (b : Bool) (c : Config M) : Config (modOTM M z b) :=
  ⟨Sum.inl c.q, c.tape, c.head, c.buf⟩

/-- A step of the modified machine on an embedded configuration of `M` that has not halted mimics a
step of `M`. -/
theorem mod_step_embed (M : OTM) (z : BitString) (b : Bool) (B : Set BitString) (c : Config M)
    (hc : ¬ Halted M c) :
    step (modOTM M z b) B (modEmbed M z b c) = modEmbed M z b (step M B c) := by
  have hc' : ¬ Halted (modOTM M z b) (modEmbed M z b c) := by
    simp [Halted, modOTM, modEmbed]
  have hacc : c.q ≠ M.accept := fun h => hc (Or.inl h)
  have hrej : c.q ≠ M.reject := fun h => hc (Or.inr h)
  have hδ : (modOTM M z b).δ (modEmbed M z b c).q
      ((modEmbed M z b c).tape (modEmbed M z b c).head) =
        (M.δ c.q (c.tape c.head)).map Sum.inl := by
    change (modOTM M z b).δ (Sum.inl c.q) (c.tape c.head) = _
    rw [modOTM_δ_inl, ite_eq_right hacc, ite_eq_right hrej]
  unfold step
  rw [ite_eq_right hc', ite_eq_right hc, hδ]
  cases M.δ c.q (c.tape c.head) with
  | step q' a m => rfl
  | push q' b' => rfl
  | ask qyes qno => by_cases hb : c.buf ∈ B <;> simp [hb, Act.map, modEmbed]

/-- From the embedding of a configuration of `M` in its accept state, the modified machine steps
to `fin true`, keeping the tape, head and query buffer. -/
theorem mod_step_embed_accept (M : OTM) (z : BitString) (b : Bool) (B : Set BitString)
    (c : Config M) (ha : c.q = M.accept) :
    step (modOTM M z b) B (modEmbed M z b c) =
      ⟨Sum.inr (Sum.inr (Sum.inr true)), c.tape, c.head, c.buf⟩ := by
  have hc' : ¬ Halted (modOTM M z b) (modEmbed M z b c) := by
    simp [Halted, modOTM, modEmbed]
  rw [step_eq_of_δ _ _ _ hc' (q' := Sum.inr (Sum.inr (Sum.inr true))) (a := c.tape c.head)
    (m := .stay)]
  · simp [moveHead, modEmbed, Function.update_eq_self]
  · change (modOTM M z b).δ (Sum.inl c.q) (c.tape c.head) = _
    rw [modOTM_δ_inl, ite_eq_left ha]
    rfl

/-- From the embedding of a configuration of `M` that is in its reject state but not its accept
state, the modified machine steps to `fin false`, keeping the tape, head and query buffer. -/
theorem mod_step_embed_reject (M : OTM) (z : BitString) (b : Bool) (B : Set BitString)
    (c : Config M) (ha : c.q ≠ M.accept) (hr : c.q = M.reject) :
    step (modOTM M z b) B (modEmbed M z b c) =
      ⟨Sum.inr (Sum.inr (Sum.inr false)), c.tape, c.head, c.buf⟩ := by
  have hc' : ¬ Halted (modOTM M z b) (modEmbed M z b c) := by
    simp [Halted, modOTM, modEmbed]
  rw [step_eq_of_δ _ _ _ hc' (q' := Sum.inr (Sum.inr (Sum.inr false))) (a := c.tape c.head)
    (m := .stay)]
  · simp [moveHead, modEmbed, Function.update_eq_self]
  · change (modOTM M z b).δ (Sum.inl c.q) (c.tape c.head) = _
    rw [modOTM_δ_inl, ite_eq_right ha, ite_eq_left hr]
    rfl

/-- Simulation phase: after entering `M.start` at time `t0`, the modified machine follows `M`
as long as `M` has not halted. -/
theorem mod_run_sim (M : OTM) (z : BitString) (b : Bool) (x : BitString) (t0 : ℕ)
    (h0 : run (modOTM M z b) ∅ x t0 = modEmbed M z b (init M x)) :
    ∀ t, (∀ t' < t, ¬ Halted M (run M ∅ x t')) →
      run (modOTM M z b) ∅ x (t0 + t) = modEmbed M z b (run M ∅ x t) := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t ih =>
    intro hnh
    change step _ ∅ (run _ ∅ x (t0 + t)) = modEmbed M z b (step M ∅ (run M ∅ x t))
    rw [ih fun t' ht' => hnh t' (by omega)]
    exact mod_step_embed M z b ∅ _ (hnh t (by omega))

/-- Two strings agreeing on the cells `0, …, |z|` are equal. -/
theorem exists_mismatch (x z : BitString) (h : x ≠ z) :
    ∃ i, i < z.length + 1 ∧ x[i]? ≠ z[i]? ∧ ∀ j < i, x[j]? = z[j]? := by
  classical
  have hex : ∃ i, i < z.length + 1 ∧ x[i]? ≠ z[i]? := by
    by_contra hne
    push Not at hne
    apply h
    apply List.ext_getElem?
    intro n
    rcases Nat.lt_or_ge n (z.length + 1) with hn | hn
    · exact hne n hn
    · have hz : z[z.length]? = none := by simp
      have hx : x[z.length]? = none := by rw [hne z.length (by omega)]; exact hz
      rw [List.getElem?_eq_none_iff] at hx
      rw [List.getElem?_eq_none_iff.2 (by omega), List.getElem?_eq_none_iff.2 (by omega)]
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj => ?_⟩
  have := Nat.find_min hex hj
  push Not at this
  exact this (by have := (Nat.find_spec hex).1; omega)

/-- The fresh halting states are halting. -/
theorem mod_halted_fin (M : OTM) (z : BitString) (b : Bool) (d : Bool) (tp : ℤ → Sym) (hd : ℤ)
    (bf : BitString) : Halted (modOTM M z b) ⟨Sum.inr (Sum.inr (Sum.inr d)), tp, hd, bf⟩ := by
  cases d
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The cells `0, …, |z|` form a set of `|z| + 1` cells. -/
theorem card_Icc_zero_length (z : BitString) :
    (Finset.Icc (0 : ℤ) z.length).card = z.length + 1 := by
  rw [Int.card_Icc]; omega

/-- `visited` is monotone in the time bound. -/
theorem visited_mono (M : OTM) (B : Set BitString) (x : BitString) {s t : ℕ} (h : s ≤ t) :
    visited M B x s ⊆ visited M B x t := by
  intro p hp
  simp only [visited, Finset.mem_image, Finset.mem_range] at hp ⊢
  obtain ⟨r, hr, rfl⟩ := hp
  exact ⟨r, by omega, rfl⟩

/-- The modified machine on the hardwired string itself. -/
theorem modOTM_spec_self (M : OTM) (z : BitString) (b : Bool) :
    Halted (modOTM M z b) (run (modOTM M z b) ∅ z (z.length + 1)) ∧
      (visited (modOTM M z b) ∅ z (z.length + 1)).card ≤ z.length + 1 ∧
      (Accepts (modOTM M z b) ∅ z ↔ b = true) := by
  have hh : Halted (modOTM M z b) (run (modOTM M z b) ∅ z (z.length + 1)) := by
    rw [mod_run_match]; exact mod_halted_fin M z b b _ _ _
  refine ⟨hh, ?_, ?_⟩
  · have hsub : visited (modOTM M z b) ∅ z (z.length + 1) ⊆ Finset.Icc (0 : ℤ) z.length := by
      intro p hp
      simp only [visited, Finset.mem_image, Finset.mem_range] at hp
      obtain ⟨s, hs, rfl⟩ := hp
      rcases Nat.lt_or_ge s (z.length + 1) with hs' | hs'
      · rw [mod_run_cmp M z b ∅ z s hs' (fun _ _ => rfl)]
        simp only [Finset.mem_Icc]
        omega
      · have : s = z.length + 1 := by omega
        subst this
        rw [mod_run_match]
        simp only [Finset.mem_Icc]
        omega
    exact (Finset.card_le_card hsub).trans (card_Icc_zero_length z).le
  · rw [accepts_iff_of_halted _ _ _ _ hh, mod_run_match]
    cases b <;> simp [modOTM]

/-- The modified machine on a string `x ≠ z`: it reaches `M.start` at cell `0` at time
`t0 = 2 i + 2` (mismatch at cell `i`), having scanned only cells in `[0, |z|]`. -/
theorem modOTM_prefix (M : OTM) (z : BitString) (b : Bool) (x : BitString) (hxz : x ≠ z) :
    ∃ t0, run (modOTM M z b) ∅ x t0 = modEmbed M z b (init M x) ∧
      ∀ s < t0, (run (modOTM M z b) ∅ x s).head ∈ Finset.Icc (0 : ℤ) z.length := by
  obtain ⟨i, hi, hne, hagree⟩ := exists_mismatch x z hxz
  have h1 := mod_run_mismatch M z b ∅ x i hi hagree hne
  have h2 := mod_run_back M z b ∅ x (i + 1) i hi h1 i le_rfl
  have h3 := mod_run_start M z b ∅ x (i + 1 + i) ⟨i - i, by omega⟩ (by simp) _ (by simp) h2
  refine ⟨i + 1 + i + 1, h3, fun s hs => ?_⟩
  by_cases c1 : s ≤ i
  · rw [mod_run_cmp M z b ∅ x s (by omega) (fun j hj => hagree j (by omega))]
    simp only [Finset.mem_Icc]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, s = i + 1 + k := ⟨s - (i + 1), by omega⟩
    rw [mod_run_back M z b ∅ x (i + 1) i hi h1 k (by omega)]
    simp only [Finset.mem_Icc]
    omega

/-- Behaviour of the modified machine on any input. -/
theorem modOTM_spec (M : OTM) (z : BitString) (b : Bool) (x : BitString) (t : ℕ)
    (ht : Halted M (run M ∅ x t)) :
    ∃ u, Halted (modOTM M z b) (run (modOTM M z b) ∅ x u) ∧
      (visited (modOTM M z b) ∅ x u).card ≤ z.length + 1 + (visited M ∅ x t).card ∧
      (Accepts (modOTM M z b) ∅ x ↔ if x = z then b = true else Accepts M ∅ x) := by
  classical
  by_cases hxz : x = z
  · rw [hxz]
    obtain ⟨hh, hc, ha⟩ := modOTM_spec_self M z b
    exact ⟨z.length + 1, hh, hc.trans (Nat.le_add_right _ _), by rw [ite_eq_left rfl]; exact ha⟩
  · obtain ⟨t0, h0, hpre⟩ := modOTM_prefix M z b x hxz
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
    refine ⟨t0 + Nat.find hex + 1, hhalt, ?_, ?_⟩
    · have hsub : visited (modOTM M z b) ∅ x (t0 + Nat.find hex + 1) ⊆
          Finset.Icc (0 : ℤ) z.length ∪ visited M ∅ x (Nat.find hex) := by
        intro p hp
        simp only [visited, Finset.mem_image, Finset.mem_range] at hp
        obtain ⟨s, hs, rfl⟩ := hp
        rw [Finset.mem_union]
        by_cases c1 : s < t0
        · exact Or.inl (hpre s c1)
        · right
          by_cases c2 : s ≤ t0 + Nat.find hex
          · obtain ⟨s', rfl⟩ : ∃ s', s = t0 + s' := ⟨s - t0, by omega⟩
            rw [hsim s' (fun t'' h => hnh t'' (by omega))]
            exact Finset.mem_image.2 ⟨s', Finset.mem_range.2 (by omega), rfl⟩
          · have : s = t0 + Nat.find hex + 1 := by omega
            subst this
            rw [hfin]
            exact Finset.mem_image.2 ⟨Nat.find hex, Finset.mem_range.2 (by omega), rfl⟩
      calc (visited (modOTM M z b) ∅ x (t0 + Nat.find hex + 1)).card
          ≤ (Finset.Icc (0 : ℤ) z.length ∪ visited M ∅ x (Nat.find hex)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.Icc (0 : ℤ) z.length).card + (visited M ∅ x (Nat.find hex)).card :=
            Finset.card_union_le _ _
        _ ≤ z.length + 1 + (visited M ∅ x t).card := by
            rw [card_Icc_zero_length]
            exact Nat.add_le_add_left (Finset.card_le_card (visited_mono M ∅ x hts_le)) _
    · rw [ite_eq_right hxz, accepts_iff_of_halted _ _ _ _ hhalt, hfin,
        accepts_iff_of_halted M ∅ x _ hts_h]
      simp [modOTM]

/-- Arithmetic: `a + 1 + 2^P ≤ 2^(P + (a + 1))`. -/
theorem add_two_pow_le (a P : ℕ) : a + 1 + 2 ^ P ≤ 2 ^ (P + (a + 1)) := by
  have h1 : a + 1 < 2 ^ (a + 1) := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ P := Nat.one_le_two_pow
  rw [pow_add]
  nlinarith

/-- Changing a set at a single string does not leave `EXPSPACE`: compare the input with the
hardwired string `z` (`|z| + 1` comparison states and `|z| + 1` return states), answer directly on
`z`, and otherwise run the machine for `A`; the extra space is `|z| + 1` cells. -/
theorem EXPSPACE_modify_one (A A' : Set BitString) (hA : A ∈ EXPSPACE) (z : BitString)
    (h : ∀ x, x ≠ z → (x ∈ A' ↔ x ∈ A)) : A' ∈ EXPSPACE := by
  classical
  obtain ⟨M, p, hM, hAM⟩ := hA
  refine ⟨modOTM M z (decide (z ∈ A')), p + Polynomial.C (z.length + 1), fun x => ?_,
    fun x => ?_⟩
  · obtain ⟨t, ht, hcard⟩ := hM x
    obtain ⟨u, hu, hcu, -⟩ := modOTM_spec M z (decide (z ∈ A')) x t ht
    refine ⟨u, hu, hcu.trans ?_⟩
    rw [Polynomial.eval_add, Polynomial.eval_C]
    exact (Nat.add_le_add_left hcard _).trans (add_two_pow_le _ _)
  · obtain ⟨t, ht, -⟩ := hM x
    obtain ⟨u, -, -, hacc⟩ := modOTM_spec M z (decide (z ∈ A')) x t ht
    rw [hacc]
    by_cases hxz : x = z
    · subst hxz; simp
    · rw [ite_eq_right hxz, h x hxz, hAM x]

/-- Finite modifications do not leave `EXPSPACE`: if `A` agrees with an `EXPSPACE` set on all
strings beyond a finite set, then `A ∈ EXPSPACE`. -/
theorem EXPSPACE_of_eventually_eq (A B : Set BitString) (hB : B ∈ EXPSPACE) (Z : Finset BitString)
    (h : ∀ x, x ∉ Z → (x ∈ A ↔ x ∈ B)) : A ∈ EXPSPACE := by
  classical
  induction Z using Finset.induction_on generalizing A with
  | empty =>
    have hAB : A = B := Set.ext fun x => h x (Finset.notMem_empty x)
    rw [hAB]; exact hB
  | @insert z Z hz ih =>
    let A' : Set BitString := {x | if x = z then x ∈ B else x ∈ A}
    have hA' : A' ∈ EXPSPACE := ih A' fun x hx => by
      by_cases hxz : x = z
      · simp [A', hxz]
      · simp only [A', Set.mem_ofPred_eq, ite_eq_right hxz]
        exact h x (by simp [hxz, hx])
    exact EXPSPACE_modify_one A' A hA' z fun x hxz => by simp [A', hxz]

end Kolmogorov.RandomStrings
