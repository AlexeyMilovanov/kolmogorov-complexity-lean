/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.StackProg

/-!
# Simulating a stack program by a one-tape machine

The encoding of the stacks on the tape (`StackSim.encT`), the sweeps that simulate one
instruction, and the representation invariant they preserve.  The section ends with
`Prog.exists_sim` (linear-space simulation by an oracle-free one-tape machine) and
`Prog.lang_mem_EXPSPACE` (a stack program within space `2 ^ p(n)` decides an `EXPSPACE` language).

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace StackSim

variable (P : Prog)

/-! #### The encoding -/

/-- The encoding of a concatenation of lists of stacks is the concatenation of the encodings. -/
theorem encT_append (l₁ l₂ : List BitString) :
    encT (l₁ ++ l₂) = encT l₁ ++ encT l₂ := by
  induction l₁ with
  | nil => rfl
  | cons s l ih => simp [encT, ih]

/-- The encoding of `s :: l` has the length of `s`, plus one blank, plus the length of `encT l`. -/
theorem length_encT_cons (s : BitString) (l : List BitString) :
    (encT (s :: l)).length = s.length + 1 + (encT l).length := by
  simp [encT]; ring

/-- The length of `encT l` is the total length of the stacks in `l` plus one blank per stack. -/
theorem length_encT (l : List BitString) :
    (encT l).length = (l.map List.length).sum + l.length := by
  induction l with
  | nil => rfl
  | cons s l ih => rw [length_encT_cons, ih]; simp; ring

/-- A stack written as the cells `some b` contains no blank cell. -/
theorem count_map_some (s : BitString) : (s.map some).count none = 0 :=
  List.count_eq_zero.2 (by simp)

/-- The encoding `encT l` contains exactly one blank cell for each stack of `l`. -/
theorem count_encT (l : List BitString) : (encT l).count none = l.length := by
  induction l with
  | nil => rfl
  | cons s l ih => simp [encT, List.count_append, count_map_some, ih]

/-- If the first stack is `b :: s`, the encoding starts with the cell `some b`, followed by the
encoding of the list whose first stack is `s`. -/
theorem encT_cons_cons (b : Bool) (s : BitString) (l : List BitString) :
    encT ((b :: s) :: l) = some b :: encT (s :: l) := rfl

/-- The first cell of `encT (s :: l)` is the top bit `s.head?` of `s`, blank if `s` is empty. -/
theorem encT_cons (s : BitString) (l : List BitString) :
    encT (s :: l) = s.head? :: (encT (s :: l)).tail := by
  cases s <;> rfl

/-- The encoding of a nonempty list of stacks ends with a blank cell. -/
theorem encT_last (A : List BitString) (hA : A ≠ []) : ∃ pre, encT A = pre ++ [none] := by
  induction A with
  | nil => exact absurd rfl hA
  | cons s A ih =>
    rcases eq_or_ne A [] with h | h
    · subst h; exact ⟨s.map some, rfl⟩
    · obtain ⟨pre, hpre⟩ := ih h
      exact ⟨s.map some ++ none :: pre, by simp [encT, hpre]⟩

/-- On a tape holding `encT A` followed by `rest`, the last cell of the encoding is blank (for
`A = []` this is the cell `-1`). -/
theorem render_before_encT (A : List BitString) (rest : List Sym) :
    render (encT A ++ rest) ((encT A).length - 1 : ℤ) = none := by
  rcases eq_or_ne A [] with h | h
  · subst h
    simp only [encT, List.nil_append, List.length_nil, Nat.cast_zero, zero_sub]
    exact render_neg_one rest
  · obtain ⟨pre, hpre⟩ := encT_last A h
    rw [hpre]
    have : ((pre ++ [none]).length - 1 : ℤ) = pre.length := by simp
    rw [this]
    simpa using render_mid pre rest none

/-- Listing the stacks of a register file updated at `r` with `v` is setting the entry `r` of the
list of the original stacks to `v`. -/
theorem ofFn_update {K : ℕ} (regs : Fin K → BitString) (r : Fin K) (v : BitString) :
    List.ofFn (Function.update regs r v) = (List.ofFn regs).set r v := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_ofFn, List.getElem_set, List.getElem_ofFn]
  by_cases h : (r : ℕ) = i
  · subst h; simp
  · rw [ite_eq_right h, Function.update_of_ne]
    intro h'; apply h; rw [← h']

/-- A list splits at an index `r` into its first `r` elements, the element at `r`, and the rest. -/
theorem split_at (l : List BitString) (r : ℕ) (hr : r < l.length) :
    l = l.take r ++ l[r] :: l.drop (r + 1) := by
  conv_lhs => rw [← List.take_append_drop r l]
  rw [List.drop_eq_getElem_cons hr]

/-- Setting the entry `r` of a list to `v` yields its first `r` elements, then `v`, then the
elements after the entry `r`. -/
theorem set_split (l : List BitString) (r : ℕ) (hr : r < l.length) (v : BitString) :
    l.set r v = l.take r ++ v :: l.drop (r + 1) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hr]

/-- The encoding of the stacks of a configuration `c` has length `c.space + P.k`: the total length
of the stacks, plus one blank per stack. -/
theorem length_encT_ofFn (c : PConfig P) : (encT (List.ofFn c.regs)).length = c.space + P.k := by
  rw [length_encT, PConfig.space, List.map_ofFn, List.sum_ofFn, List.length_ofFn]; rfl

/-- A configuration with an empty buffer whose head lies in `[-1, H]` reaches itself. -/
theorem refl_at {M : OTM} {H : ℤ} (q : M.Q) (τ : ℤ → Sym) (h : ℤ) (hl : -1 ≤ h)
    (hh : h ≤ H) :
    Reach M H ⟨q, τ, h, []⟩ ⟨q, τ, h, []⟩ := Reach.refl _ hl hh

/-- A `Reach` chain can start with one step of `simOTM P` that writes `a`, enters `q'` and moves
the head one cell to the right. -/
theorem reach_right {H : ℤ} {q q' : SimQ P.code.length P.k} {τ : ℤ → Sym} {h : ℤ} {a : Sym}
    {c' : Config (simOTM P)} (hq : q ≠ .acc ∧ q ≠ .rej)
    (hδ : simδ P q (τ h) = .step q' a .right) (hl : -1 ≤ h) (hh : h ≤ H)
    (hr : Reach (simOTM P) H ⟨q', Function.update τ h a, h + 1, []⟩ c') :
    Reach (simOTM P) H ⟨q, τ, h, []⟩ c' := reach_step P hq hδ hl hh hr

/-- A `Reach` chain can start with one step of `simOTM P` that writes `a`, enters `q'` and moves
the head one cell to the left. -/
theorem reach_left {H : ℤ} {q q' : SimQ P.code.length P.k} {τ : ℤ → Sym} {h : ℤ} {a : Sym}
    {c' : Config (simOTM P)} (hq : q ≠ .acc ∧ q ≠ .rej)
    (hδ : simδ P q (τ h) = .step q' a .left) (hl : -1 ≤ h) (hh : h ≤ H)
    (hr : Reach (simOTM P) H ⟨q', Function.update τ h a, h - 1, []⟩ c') :
    Reach (simOTM P) H ⟨q, τ, h, []⟩ c' := reach_step P hq hδ hl hh hr

/-- Writing at a cell of a rendered tape the symbol it already holds changes nothing. -/
theorem update_same {L : List Sym} {h : ℤ} {a : Sym} (hr : render L h = a) :
    Function.update (render L) h a = render L :=
  Function.update_eq_self_iff.2 hr.symm

/-- For a counter `j ≤ P.k`, `rS P pc j m` is the rightward-sweep state `R pc j m`. -/
theorem rS_eq (pc : Fin P.code.length) (j : ℕ) (hj : j ≤ P.k) (m : RMode) :
    rS P pc j m = .R pc ⟨j, Nat.lt_succ_of_le hj⟩ m := dite_eq_left hj

/-- For a counter `j ≤ P.k`, `lS P pc o j d` is the leftward-sweep state `Lf pc o j d`. -/
theorem lS_eq (pc : Fin P.code.length) (o : Sym) (j : ℕ) (hj : j ≤ P.k) (d : Option Sym) :
    lS P pc o j d = .Lf pc o ⟨j, Nat.lt_succ_of_le hj⟩ d := dite_eq_left hj

/-- For a counter `j ≤ P.k`, the state `rS P pc j m` is neither accepting nor rejecting. -/
theorem rS_ne (pc : Fin P.code.length) (j : ℕ) (hj : j ≤ P.k) (m : RMode) :
    rS P pc j m ≠ .acc ∧ rS P pc j m ≠ .rej := by
  rw [rS_eq P pc j hj]; exact ⟨by simp, by simp⟩

/-- For a counter `j ≤ P.k`, the state `lS P pc o j d` is neither accepting nor rejecting. -/
theorem lS_ne (pc : Fin P.code.length) (o : Sym) (j : ℕ) (hj : j ≤ P.k) (d : Option Sym) :
    lS P pc o j d ≠ .acc ∧ lS P pc o j d ≠ .rej := by
  rw [lS_eq P pc o j hj]; exact ⟨by simp, by simp⟩

section δlemmas
variable (pc : Fin P.code.length)

/-- While looking for the active stack, at a counter other than its index, a bit is passed over
unchanged and the head moves right. -/
theorem δ_nav_some (j : ℕ) (hj : j ≤ P.k) (hr : j ≠ ireg (instrAt P pc)) (b : Bool) :
    simδ P (rS P pc j .nav) (some b) = .step (rS P pc j .nav) (some b) .right := by
  rw [rS_eq P pc j hj]; simp [simδ, hr]

/-- While looking for the active stack, at a counter other than its index, a blank is passed over
unchanged, the counter is incremented, and the head moves right. -/
theorem δ_nav_none (j : ℕ) (hj : j + 1 ≤ P.k) (hr : j ≠ ireg (instrAt P pc)) :
    simδ P (rS P pc j .nav) none = .step (rS P pc (j + 1) .nav) none .right := by
  rw [rS_eq P pc j (by omega)]; simp [simδ, hr]

/-- At the index of the active stack the head stays: the sweep switches to the mode that the
instruction prescribes for the scanned symbol `a`. -/
theorem δ_nav_sw (j : ℕ) (hj : j ≤ P.k) (hr : j = ireg (instrAt P pc)) (a : Sym) :
    simδ P (rS P pc j .nav) a = .step (rS P pc j (switchMode (instrAt P pc) a)) a .stay := by
  subst hr; simp only [rS_eq P pc _ hj]; simp [simδ]

/-- After the top has been read, a bit is passed over unchanged and the head moves right. -/
theorem δ_done_some (j : ℕ) (hj : j ≤ P.k) (o : Sym) (b : Bool) :
    simδ P (rS P pc j (.done o)) (some b) = .step (rS P pc j (.done o)) (some b) .right := by
  rw [rS_eq P pc j hj]; simp [simδ]

/-- After the top has been read, a blank other than the last one is passed over, the counter is
incremented, and the head moves right. -/
theorem δ_done_none (j : ℕ) (hj : j + 1 < P.k) (o : Sym) :
    simδ P (rS P pc j (.done o)) none = .step (rS P pc (j + 1) (.done o)) none .right := by
  rw [rS_eq P pc j (by omega)]; simp [simδ, show j + 1 ≠ P.k by omega]

/-- After the top has been read, the last blank ends the sweep: the machine enters the turn state
for `o` and the head moves right. -/
theorem δ_done_turn (j : ℕ) (hj : j + 1 = P.k) (o : Sym) :
    simδ P (rS P pc j (.done o)) none = .step (.turn pc o) none .right := by
  rw [rS_eq P pc j (by omega)]; simp [simδ, hj]

/-- When pushing, a bit is replaced by the carried symbol `c`, the bit becomes the carried symbol,
and the head moves right. -/
theorem δ_carry_some (j : ℕ) (hj : j < P.k) (c : Sym) (b : Bool) :
    simδ P (rS P pc j (.carry c)) (some b) = .step (rS P pc j (.carry (some b))) c .right := by
  simp only [rS_eq P pc j hj.le]; simp [simδ, hj.ne]

/-- When pushing, a blank is replaced by the carried symbol `c`, the counter is incremented, the
carried symbol becomes a blank, and the head moves right. -/
theorem δ_carry_none (j : ℕ) (hj : j < P.k) (c : Sym) :
    simδ P (rS P pc j (.carry c)) none = .step (rS P pc (j + 1) (.carry none)) c .right := by
  rw [rS_eq P pc j hj.le]; simp [simδ, hj.ne]

/-- When pushing, at the counter `P.k` past the last stack the carried symbol `c` is written, the
machine enters the turn state, and the head moves right. -/
theorem δ_carry_end (c a : Sym) :
    simδ P (rS P pc P.k (.carry c)) a = .step (.turn pc none) c .right := by
  rw [rS_eq P pc P.k le_rfl]; simp [simδ]

/-- The turn state rewrites the scanned symbol `a` and starts the leftward sweep at the counter
`P.k`, deleting iff the instruction pops a nonempty stack, and the head moves left. -/
theorem δ_turn (o a : Sym) :
    simδ P (.turn pc o) a = .step (lS P pc o P.k (delMode (instrAt P pc) o)) a .left := rfl

/-- In the leftward sweep without deletion, a bit is passed over unchanged and the head moves
left. -/
theorem δ_plain_some (o : Sym) (j : ℕ) (hj : j ≤ P.k) (b : Bool) :
    simδ P (lS P pc o j none) (some b) = .step (lS P pc o j none) (some b) .left := by
  rw [lS_eq P pc o j hj]; simp [simδ]

/-- In the leftward sweep without deletion, a blank is passed over unchanged, the counter is
decremented, and the head moves left. -/
theorem δ_plain_none (o : Sym) (j : ℕ) (hj : j + 1 ≤ P.k) :
    simδ P (lS P pc o (j + 1) none) none = .step (lS P pc o j none) none .left := by
  rw [lS_eq P pc o (j + 1) hj]; simp [simδ]

/-- A blank met at the counter `0` ends the leftward sweep without deletion: the machine enters
the state of the next instruction and the head moves right. -/
theorem δ_plain_home (o : Sym) :
    simδ P (lS P pc o 0 none) none = .step (entry P (nextPC (instrAt P pc) o)) none .right := by
  rw [lS_eq P pc o 0 (Nat.zero_le _)]; simp [simδ]

/-- When deleting, a bit is replaced by the carried symbol `c`, the bit becomes the carried
symbol, and the head moves left. -/
theorem δ_del_some (o : Sym) (j : ℕ) (hj : j ≤ P.k) (c : Sym) (b : Bool) :
    simδ P (lS P pc o j (some c)) (some b) = .step (lS P pc o j (some (some b))) c .left := by
  simp only [lS_eq P pc o j hj]; simp [simδ]

/-- When deleting, above the index of the active stack, a blank is replaced by the carried symbol
`c`, the carried symbol becomes a blank, the counter is decremented, and the head moves left. -/
theorem δ_del_none (o : Sym) (j : ℕ) (hj : j + 1 ≤ P.k) (hr : ireg (instrAt P pc) ≤ j)
    (c : Sym) :
    simδ P (lS P pc o (j + 1) (some c)) none = .step (lS P pc o j (some none)) c .left := by
  rw [lS_eq P pc o (j + 1) hj]; simp [simδ, show j + 1 ≠ ireg (instrAt P pc) by omega]

/-- When deleting, a blank at the index of the active stack ends the deletion: the sweep goes on
without deletion and the head stays. -/
theorem δ_del_stop (o : Sym) (j : ℕ) (hj : j ≤ P.k) (hr : j = ireg (instrAt P pc)) (c : Sym) :
    simδ P (lS P pc o j (some c)) none = .step (lS P pc o j none) none .stay := by
  subst hr; simp only [lS_eq P pc o _ hj]; simp [simδ]

end δlemmas

/-- A state that walks right over bits without changing them. -/
theorem blockR {H : ℤ} (q : SimQ P.code.length P.k) (hq : q ≠ .acc ∧ q ≠ .rej)
    (hδ : ∀ b : Bool, simδ P q (some b) = .step q (some b) .right) :
    ∀ (s : BitString) (pre post L : List Sym) (h h' : ℤ), L = pre ++ (s.map some ++ post) →
      h = pre.length → h' = h + s.length → h' ≤ H →
      Reach (simOTM P) H ⟨q, render L, h, []⟩ ⟨q, render L, h', []⟩
  | [], pre, post, L, h, h', _, hh, hh', hH => by
    have : h' = h := by simpa using hh'
    subst this
    exact refl_at _ _ _ (by omega) hH
  | b :: s, pre, post, L, h, h', hL, hh, hh', hH => by
    have hL' : L = pre ++ some b :: (s.map some ++ post) := by rw [hL]; rfl
    have hread : render L h = some b := render_at hL' hh
    have hs : (((b :: s).length : ℕ) : ℤ) = s.length + 1 := by simp
    refine reach_right P hq (by rw [hread]; exact hδ b) (by omega) (by omega) ?_
    rw [update_same hread]
    exact blockR q hq hδ s (pre ++ [some b]) post L (h + 1) h' (by rw [hL']; simp)
      (by simp [hh]) (by omega) hH

/-- Pushing: the carry sweep over bits shifts them one cell to the right. -/
theorem carryBits {H : ℤ} (pc : Fin P.code.length) (j : ℕ) (hj : j < P.k) :
    ∀ (s : BitString) (c : Sym) (pre post L : List Sym) (h h' : ℤ),
      L = pre ++ (s.map some ++ post) → h = pre.length → h' = h + s.length → h' ≤ H →
      ∃ w c', c :: s.map some = w ++ [c'] ∧
        Reach (simOTM P) H ⟨rS P pc j (.carry c), render L, h, []⟩
          ⟨rS P pc j (.carry c'), render (pre ++ (w ++ post)), h', []⟩
  | [], c, pre, post, L, h, h', hL, hh, hh', hH => by
    refine ⟨[], c, rfl, ?_⟩
    have : h' = h := by simpa using hh'
    subst this hL
    simp only [List.map_nil, List.nil_append]
    exact refl_at _ _ _ (by omega) hH
  | b :: s, c, pre, post, L, h, h', hL, hh, hh', hH => by
    have hL' : L = pre ++ some b :: (s.map some ++ post) := by rw [hL]; rfl
    have hread : render L h = some b := render_at hL' hh
    have hs : (((b :: s).length : ℕ) : ℤ) = s.length + 1 := by simp
    obtain ⟨w, c', hw, hr⟩ := carryBits pc j hj s (some b) (pre ++ [c]) post
      (pre ++ c :: (s.map some ++ post)) (h + 1) h' (by simp) (by simp [hh]) (by omega) hH
    refine ⟨c :: w, c', by simp [hw], ?_⟩
    refine reach_right P (rS_ne P pc j hj.le _) (by rw [hread]; exact δ_carry_some P pc j hj c b)
      (by omega) (by omega) ?_
    rw [update_at c hL' hh]
    have e : pre ++ [c] ++ (w ++ post) = pre ++ (c :: w ++ post) := by simp
    rw [e] at hr
    exact hr

/-- The leftward sweep without deletion over `u.reverse`, counting blanks down. -/
theorem plainSweep {H : ℤ} (pc : Fin P.code.length) (o : Sym) (j : ℕ) :
    ∀ (u : List Sym) (n : ℕ) (pre post L : List Sym) (h : ℤ),
      L = pre ++ (u.reverse ++ post) → n = j + u.count none → n ≤ P.k →
      h + 1 = pre.length + u.length → h ≤ H →
      Reach (simOTM P) H ⟨lS P pc o n none, render L, h, []⟩
        ⟨lS P pc o j none, render L, (pre.length : ℤ) - 1, []⟩
  | [], n, pre, post, L, h, _, hn, _, hh, hH => by
    have hn' : n = j := by simpa using hn
    have : h = (pre.length : ℤ) - 1 := by simp at hh; omega
    subst hn' this
    exact refl_at _ _ _ (by omega) hH
  | a :: u, n, pre, post, L, h, hL, hn, hk, hh, hH => by
    have hL' : L = (pre ++ u.reverse) ++ a :: post := by rw [hL]; simp
    have hh2 : h = ((pre ++ u.reverse).length : ℤ) := by simp at hh ⊢; omega
    have hread : render L h = a := render_at hL' hh2
    have hrec := plainSweep (H := H) pc o j u (j + u.count none) pre (a :: post) L (h - 1)
      (by rw [hL]; simp) rfl (by cases a <;> simp at hn <;> omega) (by simp at hh; omega)
      (by omega)
    cases a with
    | none =>
      rw [List.count_cons_self, ← add_assoc] at hn
      subst hn
      refine reach_left P (lS_ne P pc o _ hk _) (by rw [hread]; exact δ_plain_none P pc o _ hk)
        (by omega) hH ?_
      rw [update_same hread]
      exact hrec
    | some b =>
      rw [List.count_cons_of_ne (by simp)] at hn
      subst hn
      refine reach_left P (lS_ne P pc o _ hk _) (by rw [hread]; exact δ_plain_some P pc o _ hk b)
        (by omega) hH ?_
      rw [update_same hread]
      exact hrec

/-- Popping: the leftward carry sweep over `u.reverse` shifts it one cell to the left. -/
theorem delSweep {H : ℤ} (pc : Fin P.code.length) (o : Sym) (j : ℕ)
    (hjr : ireg (instrAt P pc) ≤ j) :
    ∀ (u : List Sym) (n : ℕ) (c : Sym) (pre post L : List Sym) (h : ℤ),
      L = pre ++ (u.reverse ++ post) → n = j + u.count none → n ≤ P.k →
      h + 1 = pre.length + u.length → h ≤ H →
      ∃ w c', u.reverse ++ [c] = c' :: w ∧
        Reach (simOTM P) H ⟨lS P pc o n (some c), render L, h, []⟩
          ⟨lS P pc o j (some c'), render (pre ++ (w ++ post)), (pre.length : ℤ) - 1, []⟩
  | [], n, c, pre, post, L, h, hL, hn, _, hh, hH => by
    refine ⟨[], c, rfl, ?_⟩
    have hn' : n = j := by simpa using hn
    have : h = (pre.length : ℤ) - 1 := by simp at hh; omega
    subst hn' this hL
    simp only [List.reverse_nil, List.nil_append]
    exact refl_at _ _ _ (by omega) hH
  | a :: u, n, c, pre, post, L, h, hL, hn, hk, hh, hH => by
    have hL' : L = (pre ++ u.reverse) ++ a :: post := by rw [hL]; simp
    have hh2 : h = ((pre ++ u.reverse).length : ℤ) := by simp at hh ⊢; omega
    have hread : render L h = a := render_at hL' hh2
    obtain ⟨w, c', hw, hr⟩ := delSweep (H := H) pc o j hjr u (j + u.count none) a pre
      (c :: post) ((pre ++ u.reverse) ++ c :: post) (h - 1) (by simp) rfl
      (by cases a <;> simp at hn <;> omega) (by simp at hh; omega) (by omega)
    refine ⟨w ++ [c], c', by rw [List.reverse_cons, hw]; rfl, ?_⟩
    have e : pre ++ (w ++ c :: post) = pre ++ (w ++ [c] ++ post) := by simp
    rw [e] at hr
    cases a with
    | none =>
      rw [List.count_cons_self, ← add_assoc] at hn
      subst hn
      refine reach_left P (lS_ne P pc o _ hk _)
        (by rw [hread]; exact δ_del_none P pc o _ hk (by omega) c) (by omega) hH ?_
      rw [update_at c hL' hh2]
      exact hr
    | some b =>
      rw [List.count_cons_of_ne (by simp)] at hn
      subst hn
      refine reach_left P (lS_ne P pc o _ hk _)
        (by rw [hread]; exact δ_del_some P pc o _ hk c b) (by omega) hH ?_
      rw [update_at c hL' hh2]
      exact hr

/-- The length of `encT (s :: l)`, as an integer, is the length of `s`, plus one, plus the length
of `encT l`. -/
theorem length_encT_cons_int (s : BitString) (l : List BitString) :
    ((encT (s :: l)).length : ℤ) = s.length + 1 + (encT l).length := by
  rw [length_encT_cons]; push_cast; ring

/-- Navigation over whole blocks before the active stack. -/
theorem navUnits {H : ℤ} (pc : Fin P.code.length) (hr : ireg (instrAt P pc) ≤ P.k) :
    ∀ (A : List BitString) (j : ℕ) (pre post L : List Sym) (h h' : ℤ),
      L = pre ++ (encT A ++ post) → j + A.length ≤ ireg (instrAt P pc) → h = pre.length →
      h' = h + (encT A).length → h' ≤ H →
      Reach (simOTM P) H ⟨rS P pc j .nav, render L, h, []⟩
        ⟨rS P pc (j + A.length) .nav, render L, h', []⟩
  | [], j, pre, post, L, h, h', _, _, hh, hh', hH => by
    have : h' = h := by simpa [encT] using hh'
    subst this
    simp only [List.length_nil, add_zero]
    exact refl_at _ _ _ (by omega) hH
  | s :: A, j, pre, post, L, h, h', hL, hA, hh, hh', hH => by
    have hlen := length_encT_cons_int s A
    have hA' : j + 1 + A.length ≤ ireg (instrAt P pc) := by simp at hA; omega
    have hjr : j ≠ ireg (instrAt P pc) := by omega
    have hjk : j + 1 ≤ P.k := by omega
    have hL1 : L = pre ++ (s.map some ++ (none :: (encT A ++ post))) := by rw [hL]; simp [encT]
    have hb := blockR P (H := H) (rS P pc j .nav) (rS_ne P pc j (by omega) _)
      (fun b => δ_nav_some P pc j (by omega) hjr b) s pre (none :: (encT A ++ post)) L h
      (h + s.length) hL1 hh rfl (by omega)
    refine hb.trans ?_
    have hL2 : L = (pre ++ s.map some) ++ none :: (encT A ++ post) := by rw [hL1]; simp
    have hh2 : h + s.length = ((pre ++ s.map some).length : ℤ) := by simp [hh]
    have hread : render L (h + s.length) = none := render_at hL2 hh2
    refine reach_right P (rS_ne P pc j (by omega) _)
      (by rw [hread]; exact δ_nav_none P pc j hjk hjr) (by omega) (by omega) ?_
    rw [update_same hread]
    have := navUnits (H := H) pc hr A (j + 1) (pre ++ (s.map some ++ [none])) post L
      (h + s.length + 1) h'
      (by rw [hL]; simp [encT]) hA' (by simp [hh]; omega) (by omega) hH
    rw [show j + (s :: A).length = j + 1 + A.length by simp; omega]
    exact this

/-- After reading the top `o`: walk to the end of the encoding and turn. -/
theorem doneUnits {H : ℤ} (pc : Fin P.code.length) (o : Sym) :
    ∀ (B : List BitString) (j : ℕ) (pre post L : List Sym) (h h' : ℤ), B ≠ [] →
      j + B.length = P.k → L = pre ++ (encT B ++ post) → h = pre.length →
      h' = h + (encT B).length → h' ≤ H →
      Reach (simOTM P) H ⟨rS P pc j (.done o), render L, h, []⟩
        ⟨.turn pc o, render L, h', []⟩
  | [], _, _, _, _, _, _, hB, _, _, _, _, _ => absurd rfl hB
  | s :: B, j, pre, post, L, h, h', _, hjB, hL, hh, hh', hH => by
    have hlen := length_encT_cons_int s B
    have hjk : j < P.k := by simp at hjB; omega
    have hL1 : L = pre ++ (s.map some ++ (none :: (encT B ++ post))) := by rw [hL]; simp [encT]
    have hb := blockR P (H := H) (rS P pc j (.done o)) (rS_ne P pc j hjk.le _)
      (fun b => δ_done_some P pc j hjk.le o b) s pre (none :: (encT B ++ post)) L h
      (h + s.length) hL1 hh rfl (by omega)
    refine hb.trans ?_
    have hL2 : L = (pre ++ s.map some) ++ none :: (encT B ++ post) := by rw [hL1]; simp
    have hh2 : h + s.length = ((pre ++ s.map some).length : ℤ) := by simp [hh]
    have hread : render L (h + s.length) = none := render_at hL2 hh2
    rcases eq_or_ne B [] with hB | hB
    · subst hB
      have hj1 : j + 1 = P.k := by simpa using hjB
      have h0 : (encT ([] : List BitString)).length = 0 := rfl
      refine reach_right P (rS_ne P pc j hjk.le _)
        (by rw [hread]; exact δ_done_turn P pc j hj1 o) (by omega) (by omega) ?_
      rw [update_same hread]
      obtain rfl : h' = h + s.length + 1 := by omega
      exact refl_at _ _ _ (by omega) hH
    · have hBl : 0 < B.length := List.length_pos_of_ne_nil hB
      have hj1 : j + 1 < P.k := by simp at hjB; omega
      refine reach_right P (rS_ne P pc j hjk.le _)
        (by rw [hread]; exact δ_done_none P pc j hj1 o) (by omega) (by omega) ?_
      rw [update_same hread]
      exact doneUnits (H := H) pc o B (j + 1) (pre ++ (s.map some ++ [none])) post L
        (h + s.length + 1) h'
        hB (by simp at hjB; omega) (by rw [hL]; simp [encT]) (by simp [hh]; omega)
        (by omega) hH

/-- Pushing over whole blocks: the encoding is shifted one cell to the right. -/
theorem carryUnits {H : ℤ} (pc : Fin P.code.length) :
    ∀ (B : List BitString) (j : ℕ) (c : Sym) (pre post L : List Sym) (h h' : ℤ),
      j + B.length ≤ P.k → L = pre ++ (encT B ++ post) → h = pre.length →
      h' = h + (encT B).length → h' ≤ H →
      ∃ w c', c :: encT B = w ++ [c'] ∧
        Reach (simOTM P) H ⟨rS P pc j (.carry c), render L, h, []⟩
          ⟨rS P pc (j + B.length) (.carry c'), render (pre ++ (w ++ post)), h', []⟩
  | [], j, c, pre, post, L, h, h', _, hL, hh, hh', hH => by
    refine ⟨[], c, rfl, ?_⟩
    have : h' = h := by simpa [encT] using hh'
    subst this hL
    simp only [List.length_nil, add_zero, encT, List.nil_append]
    exact refl_at _ _ _ (by omega) hH
  | s :: B, j, c, pre, post, L, h, h', hjB, hL, hh, hh', hH => by
    have hlen := length_encT_cons_int s B
    have hjk : j < P.k := by simp at hjB; omega
    have hL1 : L = pre ++ (s.map some ++ (none :: (encT B ++ post))) := by rw [hL]; simp [encT]
    obtain ⟨w₁, c₁, hw₁, hr₁⟩ :=
      carryBits P (H := H) pc j hjk s c pre (none :: (encT B ++ post)) L h
      (h + s.length) hL1 hh rfl (by omega)
    have hw₁len : w₁.length = s.length := by
      have := congrArg List.length hw₁; simp at this; omega
    have hL2 : pre ++ (w₁ ++ none :: (encT B ++ post)) =
        (pre ++ w₁) ++ none :: (encT B ++ post) := by simp
    have hh2 : h + s.length = ((pre ++ w₁).length : ℤ) := by simp [hh, hw₁len]
    have hread : render (pre ++ (w₁ ++ none :: (encT B ++ post))) (h + s.length) = none :=
      render_at hL2 hh2
    obtain ⟨w₂, c₂, hw₂, hr₂⟩ :=
      carryUnits (H := H) pc B (j + 1) none (pre ++ w₁ ++ [c₁]) post
        ((pre ++ w₁) ++ c₁ :: (encT B ++ post)) (h + s.length + 1) h'
        (by simp at hjB; omega) (by simp) (by simp [hh, hw₁len]; omega) (by omega) hH
    refine ⟨w₁ ++ [c₁] ++ w₂, c₂, ?_, hr₁.trans ?_⟩
    · change c :: (s.map some ++ none :: encT B) = _
      rw [← List.cons_append, hw₁, hw₂]
      simp
    · refine reach_right P (rS_ne P pc j hjk.le _)
        (by rw [hread]; exact δ_carry_none P pc j hjk c₁) (by omega) (by omega) ?_
      rw [update_at c₁ hL2 hh2]
      have e1 : j + (s :: B).length = j + 1 + B.length := by simp; omega
      have e2 : pre ++ w₁ ++ [c₁] ++ (w₂ ++ post) =
          pre ++ (w₁ ++ [c₁] ++ w₂ ++ post) := by simp
      rw [e1, ← e2]
      exact hr₂

/-- From the start of an instruction to the active stack's block, switching mode there. -/
theorem navSwitch {H : ℤ} (pc : Fin P.code.length) (A : List BitString) (rest L : List Sym)
    (a : Sym) (hL : L = encT A ++ a :: rest) (hA : A.length = ireg (instrAt P pc))
    (hr : ireg (instrAt P pc) ≤ P.k) (hH : ((encT A).length : ℤ) ≤ H) :
    Reach (simOTM P) H ⟨rS P pc 0 .nav, render L, 0, []⟩
      ⟨rS P pc A.length (switchMode (instrAt P pc) a), render L, (encT A).length, []⟩ := by
  have h1 := navUnits P (H := H) pc hr A 0 [] (a :: rest) L 0 (encT A).length (by simp [hL])
    (by omega)
    (by simp) (by simp) hH
  rw [zero_add] at h1
  refine h1.trans ?_
  have hread : render L (encT A).length = a := render_at hL rfl
  refine reach_step P (rS_ne P pc _ (by omega) _)
    (by rw [hread]; exact δ_nav_sw P pc _ (by omega) hA a) (by omega) hH ?_
  rw [update_same hread]
  simp only [moveHead]
  exact refl_at _ _ _ (by omega) hH

/-- `test`/`pop`: from the start of the instruction to the turn, then one step left. -/
theorem navDoneTurn {H : ℤ} (pc : Fin P.code.length) (A : List BitString) (s : BitString)
    (B : List BitString) (L : List Sym) (hL : L = encT (A ++ s :: B))
    (hA : A.length = ireg (instrAt P pc)) (hK : (A ++ s :: B).length = P.k)
    (hsw : switchMode (instrAt P pc) s.head? = .done s.head?)
    (hH : ((encT (A ++ s :: B)).length : ℤ) ≤ H) :
    Reach (simOTM P) H ⟨rS P pc 0 .nav, render L, 0, []⟩
      ⟨lS P pc s.head? P.k (delMode (instrAt P pc) s.head?), render L,
        ((encT (A ++ s :: B)).length : ℤ) - 1, []⟩ := by
  have hlenAB : ((encT (A ++ s :: B)).length : ℤ) = (encT A).length + (encT (s :: B)).length := by
    rw [encT_append]; simp
  have hlen := length_encT_cons_int s B
  have hL' : L = encT A ++ s.head? :: (encT (s :: B)).tail := by
    rw [hL, encT_append, ← encT_cons]
  have hKl : A.length + 1 + B.length = P.k := by simp at hK; omega
  have h1 := navSwitch P (H := H) pc A _ L s.head? hL' hA (by omega) (by omega)
  rw [hsw] at h1
  refine h1.trans ?_
  have h2 := doneUnits P (H := H) pc s.head? (s :: B) A.length (encT A) [] L (encT A).length
    ((encT (A ++ s :: B)).length) (by simp) (by simp; omega) (by simp [hL, encT_append]) rfl
    (by omega) hH
  refine h2.trans ?_
  refine reach_left P (by simp) (δ_turn P pc s.head? _) (by omega) hH ?_
  rw [update_read]
  exact refl_at _ _ _ (by omega) (by omega)

/-- The leftward sweep over a whole encoding (no deletion) and the step back to cell `0`. -/
theorem sweepHome {H : ℤ} (pc : Fin P.code.length) (o : Sym) (l : List BitString)
    (post L : List Sym) (n : ℕ) (h : ℤ) (hL : L = encT l ++ post) (hn : n = l.length)
    (hl : l.length ≤ P.k) (hh : h + 1 = (encT l).length) (hH : h ≤ H) (hH0 : 0 ≤ H) :
    Reach (simOTM P) H ⟨lS P pc o n none, render L, h, []⟩
      ⟨entry P (nextPC (instrAt P pc) o), render L, 0, []⟩ := by
  have h1 := plainSweep P (H := H) pc o 0 (encT l).reverse n [] post L h (by simp [hL])
    (by simp [hn, count_encT]) (by omega) (by simp; omega) hH
  simp only [List.length_nil, Nat.cast_zero, zero_sub] at h1
  refine h1.trans ?_
  have hread : render L (-1) = none := render_neg_one L
  refine reach_right P (lS_ne P pc o 0 (Nat.zero_le _) _)
    (by rw [hread]; exact δ_plain_home P pc o) (le_refl _) (by omega) ?_
  rw [update_same hread, show (-1 : ℤ) + 1 = 0 by norm_num]
  exact refl_at _ _ _ (by norm_num) hH0

/-- Setting the entry at the index `A.length` of `A ++ x :: B` to `v` replaces `x` by `v`. -/
theorem set_mid {α : Type*} (A B : List α) (x v : α) :
    (A ++ x :: B).set A.length v = A ++ v :: B := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [ih]

/-- The stacks of a configuration `c` split around the stack `r` as `A ++ c.regs r :: B` with
`A.length = r`, and updating the stack `r` to `v` gives `A ++ v :: B`. -/
theorem decomp (c : PConfig P) (r : Fin P.k) :
    ∃ A B : List BitString, List.ofFn c.regs = A ++ c.regs r :: B ∧ A.length = r ∧
      ∀ v, List.ofFn (Function.update c.regs r v) = A ++ v :: B := by
  refine ⟨(List.ofFn c.regs).take r, (List.ofFn c.regs).drop (r + 1), ?_, by simp, fun v => ?_⟩
  · have := split_at (List.ofFn c.regs) r (by simp)
    rw [List.getElem_ofFn] at this
    exact this
  · rw [ofFn_update, set_split _ _ (by simp)]

/-- At an instruction other than `accept` and `reject`, the entry state is the rightward sweep in
navigation mode with the counter `0`. -/
theorem entry_eq_rS (pc : ℕ) (hpc : pc < P.code.length) (hi : P.code[pc] ≠ .accept)
    (hi' : P.code[pc] ≠ .reject) : entry P pc = rS P ⟨pc, hpc⟩ 0 .nav := by
  unfold entry
  rw [dite_eq_left hpc]
  split
  · next h => exact absurd h hi
  · next h => exact absurd h hi'
  · rfl

/-- Macro step for `push r b n`: navigate, shift right inserting `b`, turn, sweep home. -/
theorem macro_push {H : ℤ} (c : PConfig P) (hpc : c.pc < P.code.length) (r : Fin P.k) (b : Bool)
    (n : ℕ) (hi : P.code[c.pc] = .push r b n) (hH : (c.space : ℤ) + P.k + 1 ≤ H) :
    Reach (simOTM P) H (repr P c) (repr P (P.step c)) := by
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
  have h1 := navSwitch P (H := H) ⟨c.pc, hpc⟩ A _ _ _ hL0 (by rw [hI]; exact hAlen)
    (by rw [hI]; change (r : ℕ) ≤ P.k; omega) (by omega)
  rw [hsw] at h1
  obtain ⟨w, c', hw, h2⟩ := carryUnits P (H := H) ⟨c.pc, hpc⟩ (c.regs r :: B) A.length
    (some b) (encT A) [] (encT (List.ofFn c.regs)) (encT A).length
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
  have hXH : ((encT A ++ (w ++ [])).length : ℤ) + 1 ≤ H := by
    have : ((encT (List.ofFn c.regs)).length : ℤ) = c.space + P.k := by rw [hm]; push_cast; ring
    omega
  refine h1.trans (h2.trans ?_)
  rw [← hX]
  refine reach_right P (rS_ne P _ _ le_rfl _) (δ_carry_end P ⟨c.pc, hpc⟩ c' _) (by omega)
    (by omega) ?_
  rw [update_render_length, hnew]
  refine reach_left P (by simp) (δ_turn P ⟨c.pc, hpc⟩ none _) (by omega) hXH ?_
  rw [update_read, hdel]
  have h3 := sweepHome P (H := H) ⟨c.pc, hpc⟩ none (A ++ (b :: c.regs r) :: B) []
    (encT (A ++ (b :: c.regs r) :: B)) P.k ((encT A ++ (w ++ [])).length + 1 - 1) (by simp)
    (by simp; omega) (by simp; omega) (by omega) (by omega) (by omega)
  rw [hnext] at h3
  exact h3

/-- Macro step for `test`: navigate, read the top, sweep to the end, turn, sweep home. -/
theorem macro_test {H : ℤ} (c : PConfig P) (hpc : c.pc < P.code.length) (r : Fin P.k)
    (i0 i1 i2 : ℕ) (hi : P.code[c.pc] = .test r i0 i1 i2) (hH : (c.space : ℤ) + P.k + 1 ≤ H) :
    Reach (simOTM P) H (repr P c) (repr P (P.step c)) := by
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
  have hdel : delMode (instrAt P ⟨c.pc, hpc⟩) (c.regs r).head? = none := by rw [hI]; rfl
  unfold repr
  rw [hentry, hstep]
  dsimp only
  have h1 := navDoneTurn P (H := H) ⟨c.pc, hpc⟩ A (c.regs r) B (encT (List.ofFn c.regs))
    (by rw [hsplit]) (by rw [hI]; exact hAlen) hKl (by rw [hI]; rfl) (by rw [← hsplit]; omega)
  rw [hdel] at h1
  refine h1.trans ?_
  exact sweepHome P (H := H) ⟨c.pc, hpc⟩ (c.regs r).head? (List.ofFn c.regs) []
    (encT (List.ofFn c.regs)) P.k _ (by simp) (by simp) (by simp) (by rw [hsplit]; simp)
    (by rw [← hsplit]; omega) (by omega)

/-- Macro step for `pop`: as `test`, deleting the top on the way back if it exists. -/
theorem macro_pop {H : ℤ} (c : PConfig P) (hpc : c.pc < P.code.length) (r : Fin P.k) (n : ℕ)
    (hi : P.code[c.pc] = .pop r n) (hH : (c.space : ℤ) + P.k + 1 ≤ H) :
    Reach (simOTM P) H (repr P c) (repr P (P.step c)) := by
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
  have h1 := navDoneTurn P (H := H) ⟨c.pc, hpc⟩ A s B (encT (List.ofFn c.regs))
    (by rw [hsplit]) (by rw [hI]; exact hAlen) hKl (by rw [hI]; rfl) (by rw [← hsplit]; omega)
  refine h1.trans ?_
  cases s with
  | nil =>
    have hdel : delMode (instrAt P ⟨c.pc, hpc⟩) ([] : BitString).head? = none := by rw [hI]; rfl
    have hnext : nextPC (instrAt P ⟨c.pc, hpc⟩) ([] : BitString).head? = n := by rw [hI]; rfl
    rw [hdel]
    have h3 := sweepHome P (H := H) ⟨c.pc, hpc⟩ ([] : BitString).head? (A ++ [] :: B) []
      (encT (List.ofFn c.regs)) P.k (((encT (A ++ [] :: B)).length : ℤ) - 1)
      (by rw [hsplit]; simp) (by simp at hKl ⊢; omega) (by simp at hKl ⊢; omega)
      (by simp) (by rw [← hsplit]; omega) (by omega)
    rw [hnext] at h3
    have e : encT (A ++ ([] : BitString).tail :: B) = encT (List.ofFn c.regs) := by rw [hsplit]; rfl
    rw [e]
    exact h3
  | cons t s' =>
    have hdel : delMode (instrAt P ⟨c.pc, hpc⟩) (t :: s').head? = some none := by rw [hI]; rfl
    have hnext : nextPC (instrAt P ⟨c.pc, hpc⟩) (some t) = n := by rw [hI]; rfl
    rw [hdel] at h1 ⊢
    have hlenAB : ((encT (A ++ (t :: s') :: B)).length : ℤ) =
        (encT A).length + (encT ((t :: s') :: B)).length := by rw [encT_append]; simp
    obtain ⟨w, c'', hw, h2⟩ := delSweep P (H := H) ⟨c.pc, hpc⟩ (t :: s').head? A.length
      (by rw [hI]; change (r : ℕ) ≤ A.length; omega) (encT ((t :: s') :: B)).reverse P.k none
      (encT A) [] (encT (List.ofFn c.regs)) ((encT (A ++ (t :: s') :: B)).length - 1)
      (by rw [hsplit, encT_append]; simp)
      (by rw [List.count_reverse, count_encT]; simp at hKl ⊢; omega) le_rfl
      (by rw [List.length_reverse]; omega) (by rw [← hsplit]; omega)
    rw [List.reverse_reverse, encT_cons_cons] at hw
    simp only [List.cons_append, List.cons.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine h2.trans ?_
    have hf : ((encT (List.ofFn c.regs)).length : ℤ) =
        (encT A).length + (encT ((t :: s') :: B)).length := by rw [hsplit, encT_append]; simp
    have hread : render (encT A ++ (encT (s' :: B) ++ [none] ++ [])) ((encT A).length - 1) =
        none := render_before_encT A _
    have hAk : A.length ≤ P.k := by simp at hKl; omega
    have hδ := δ_del_stop P ⟨c.pc, hpc⟩ (t :: s').head? A.length hAk (by rw [hI]; exact hAlen)
      (some t)
    refine reach_step P (lS_ne P ⟨c.pc, hpc⟩ (t :: s').head? A.length hAk (some (some t)))
      (by rw [hread]; exact hδ) (by omega) (by omega) ?_
    rw [update_same hread]
    have h3 := sweepHome P (H := H) ⟨c.pc, hpc⟩ (some t) A (encT (s' :: B) ++ [none] ++ [])
      (encT A ++ (encT (s' :: B) ++ [none] ++ [])) A.length ((encT A).length - 1) rfl rfl
      (by simp at hKl; omega) (by ring) (by omega) (by omega)
    rw [hnext] at h3
    have htape : render (encT A ++ (encT (s' :: B) ++ [none] ++ [])) =
        render (encT (A ++ (t :: s').tail :: B)) := by
      rw [List.append_nil, ← List.append_assoc, render_append_none, encT_append]; rfl
    rw [← htape]
    exact h3

/-- **Macro step.**  One instruction of `P` is simulated, all heads staying in `[-1, H]`. -/
theorem macroStep (c : PConfig P) (hnh : ¬ P.Halted c) (H : ℤ)
    (hH : (c.space : ℤ) + P.k + 1 ≤ H) :
    Reach (simOTM P) H (repr P c) (repr P (P.step c)) := by
  unfold Prog.Halted at hnh
  simp only [not_or] at hnh
  obtain ⟨h1, h2, h3⟩ := hnh
  have hpc : c.pc < P.code.length := by
    by_contra hc; exact h3 (List.getElem?_eq_none (by omega))
  rw [List.getElem?_eq_getElem hpc] at h1 h2
  cases hi : P.code[c.pc] with
  | push r b n => exact macro_push P c hpc r b n hi hH
  | pop r n => exact macro_pop P c hpc r n hi hH
  | test r i0 i1 i2 => exact macro_test P c hpc r i0 i1 i2 hi hH
  | accept => exact absurd (by rw [hi]) h1
  | reject => exact absurd (by rw [hi]) h2

/-- The entry state is accepting iff the instruction is `accept`. -/
theorem entry_acc_iff (pc : ℕ) : entry P pc = .acc ↔ P.code[pc]? = some .accept := by
  unfold entry
  split_ifs with h
  · rw [List.getElem?_eq_getElem h]
    cases hi : P.code[pc] <;> simp [rS]
  · simp [List.getElem?_eq_none (show P.code.length ≤ pc by omega)]

/-- At a halted program configuration the entry state is halting. -/
theorem halted_entry (c : PConfig P) (h : P.Halted c) :
    entry P c.pc = .acc ∨ entry P c.pc = .rej := by
  unfold Prog.Halted at h
  unfold entry
  split_ifs with hpc
  · rw [List.getElem?_eq_getElem hpc] at h
    rcases h with h | h | h
    · simp at h; simp [h]
    · simp at h; simp [h]
    · simp at h
  · right; rfl

/-- The initial stacks of `P`, as a list, are the input `x` followed by `P.k - 1` empty stacks. -/
theorem ofFn_init (hK : 0 < P.k) (x : BitString) :
    List.ofFn (P.init x).regs = x :: List.replicate (P.k - 1) [] := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  rw [List.getElem_ofFn]
  rcases i with _ | i
  · simp [Prog.init]
  · simp [Prog.init]

/-- The encoding of `m` empty stacks is `m` blank cells. -/
theorem encT_replicate (m : ℕ) : encT (List.replicate m []) = List.replicate m none := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, encT, ih]

/-- The tape holding the input `x` followed by blanks has the bits of `x` from cell `0` on and
blank cells elsewhere. -/
theorem render_init (x : BitString) (m : ℕ) :
    render (x.map some ++ none :: List.replicate m none) =
      fun i => if 0 ≤ i then x[i.toNat]? else none := by
  funext i
  unfold render
  split_ifs with h0
  · rw [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i.toNat x.length with h | h
    · rw [List.getElem?_append_left (by simpa using h), List.getElem?_map,
        List.getElem?_eq_getElem h]
      rfl
    · rw [List.getElem?_append_right (by simpa using h), List.getElem?_eq_none h,
        ← List.replicate_succ, List.getElem?_replicate]
      split_ifs <;> rfl
  · rfl

/-- The initial configuration of the machine represents the initial program configuration. -/
theorem init_repr (hK : 0 < P.k) (x : BitString) : run (simOTM P) ∅ x 0 = repr P (P.init x) := by
  change init (simOTM P) x = repr P (P.init x)
  unfold init repr
  rw [ofFn_init P hK x]
  congr 1
  rw [encT, encT_replicate, render_init]

/-- **Global simulation.**  Every configuration of the run of `P` is represented at some time,
all heads so far lying in `[-1, S + k + 1]`. -/
theorem global (hK : 0 < P.k) (x : BitString) (S : ℕ) :
    ∀ s : ℕ, (∀ s' ≤ s, (P.run x s').space ≤ S) →
      ∃ T, run (simOTM P) ∅ x T = repr P (P.run x s) ∧
        ∀ e ≤ T, -1 ≤ (run (simOTM P) ∅ x e).head ∧
          (run (simOTM P) ∅ x e).head ≤ (S : ℤ) + P.k + 1
  | 0, _ => ⟨0, init_repr P hK x, fun e he => by
      obtain rfl : e = 0 := by omega
      rw [init_repr P hK x]
      exact ⟨by simp [repr], by simp [repr]; omega⟩⟩
  | s + 1, hs => by
    obtain ⟨T, hT, hb⟩ := global hK x S s (fun s' hs' => hs s' (by omega))
    by_cases hh : P.Halted (P.run x s)
    · refine ⟨T, ?_, hb⟩
      change _ = repr P (P.step (P.run x s))
      rw [P.step_of_halted _ hh]; exact hT
    · have hsp := hs s (by omega)
      obtain ⟨d, hd, hdb⟩ :=
        (macroStep P (P.run x s) hh ((S : ℤ) + P.k + 1) (by omega)).iterate
      refine ⟨T + d, ?_, fun e he => ?_⟩
      · rw [run_add, hT]; exact hd
      · rcases Nat.lt_or_ge e T with h | h
        · exact hb e h.le
        · obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le h
          rw [run_add, hT]; exact hdb e' (by omega)

/-- With no stacks the program halts at once, and so does the machine. -/
theorem exists_sim_zero (hK : P.k = 0) (x : BitString) (t : ℕ) :
    Halted (simOTM P) (run (simOTM P) ∅ x 0) ∧ (visited (simOTM P) ∅ x 0).card ≤ 1 ∧
      (Accepts (simOTM P) ∅ x ↔ P.Accepting (P.run x t)) := by
  have hhalt : P.Halted (P.init x) := by
    unfold Prog.Halted
    rcases h : P.code[(P.init x).pc]? with _ | i
    · right; right; rfl
    · cases i with
      | push r _ _ => exact absurd r.isLt (by omega)
      | pop r _ => exact absurd r.isLt (by omega)
      | test r _ _ _ => exact absurd r.isLt (by omega)
      | accept => left; rfl
      | reject => right; left; rfl
  have hrun : P.run x t = P.init x := P.run_of_halted_le x (Nat.zero_le t) hhalt
  have hM : Halted (simOTM P) (run (simOTM P) ∅ x 0) := halted_entry P (P.init x) hhalt
  refine ⟨hM, visited_card_le _ _ _ 0, ?_⟩
  rw [accepts_iff_of_halted _ ∅ x 0 hM, hrun]
  exact entry_acc_iff P 0

end StackSim

/-- **Linear-space simulation of a stack program.**  Every stack program `P` is simulated by a
one-tape oracle-free machine with linear space overhead: there are a machine `M` and a constant
`C` such that, whenever `P` halts on `x` at time `t` and all configurations of `P` up to time `t`
have space `≤ S`, the machine `M` (oracle `∅`) halts on `x` at some time `u` having scanned at
most `C * (S + 1)` cells, and `M` accepts `x` iff `P` is accepting at time `t`.

The machine is `StackSim.simOTM P`: the stacks lie on the tape as the blocks of `StackSim.encT`,
each instruction is simulated by a rightward and a leftward sweep (`StackSim.macroStep`), and the
head never leaves `[-1, S + k + 1]`. -/
theorem Prog.exists_sim (P : Prog) : ∃ (M : OTM) (C : ℕ), ∀ (x : BitString) (t S : ℕ),
    P.Halted (P.run x t) → (∀ s ≤ t, (P.run x s).space ≤ S) →
    ∃ u, Kolmogorov.RandomStrings.Halted M (Kolmogorov.RandomStrings.run M ∅ x u) ∧
      (visited M ∅ x u).card ≤ C * (S + 1) ∧
      (Accepts M ∅ x ↔ P.Accepting (P.run x t)) := by
  refine ⟨StackSim.simOTM P, P.k + 3, fun x t S ht hsp => ?_⟩
  rcases Nat.eq_zero_or_pos P.k with hK | hK
  · obtain ⟨hM, hcard, hacc⟩ := StackSim.exists_sim_zero P hK x t
    exact ⟨0, hM, hcard.trans (by rw [hK]; omega), hacc⟩
  · obtain ⟨T, hT, hb⟩ := StackSim.global P hK x S t hsp
    have hHalt : Kolmogorov.RandomStrings.Halted (StackSim.simOTM P)
        (Kolmogorov.RandomStrings.run (StackSim.simOTM P) ∅ x T) := by
      rw [hT]; exact StackSim.halted_entry P _ ht
    refine ⟨T, hHalt, ?_, ?_⟩
    · calc (visited (StackSim.simOTM P) ∅ x T).card
          ≤ (Finset.Icc (-1 : ℤ) ((S : ℤ) + P.k + 1)).card := by
            apply Finset.card_le_card
            intro z hz
            simp only [visited, Finset.mem_image, Finset.mem_range] at hz
            obtain ⟨e, he, rfl⟩ := hz
            exact Finset.mem_Icc.2 (hb e (by omega))
        _ ≤ (P.k + 3) * (S + 1) := by
            rw [Int.card_Icc]
            have : ((S : ℤ) + P.k + 1 + 1 - -1).toNat = S + P.k + 3 := by omega
            rw [this]; nlinarith [Nat.zero_le (P.k * S)]
    · rw [accepts_iff_of_halted _ ∅ x T hHalt, hT]
      exact StackSim.entry_acc_iff P _

/-- Arithmetic: `C (2^P + 1) ≤ 2^(P + C + 1)`. -/
theorem mul_two_pow_add_one_le (C P : ℕ) : C * (2 ^ P + 1) ≤ 2 ^ (P + (C + 1)) := by
  have h1 : C < 2 ^ C := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ P := Nat.one_le_two_pow
  have h3 : 2 ^ (P + (C + 1)) = 2 ^ P * 2 ^ C * 2 := by rw [pow_add, pow_succ]; ring
  rw [h3]
  nlinarith

/-- A stack program that halts on every input `x` within space `2 ^ p(|x|)` decides a language in
`EXPSPACE`: by `Prog.exists_sim` it is simulated by an oracle-free one-tape machine scanning at
most `2 ^ (p(|x|) + C + 1)` cells, for a constant `C`. -/
theorem Prog.lang_mem_EXPSPACE (P : Prog) (p : Polynomial ℕ) (hP : P.SpaceBounded p) :
    P.Lang ∈ EXPSPACE := by
  obtain ⟨M, C, hM⟩ := P.exists_sim
  refine ⟨M, p + Polynomial.C (C + 1), fun x => ?_, fun x => ?_⟩
  · obtain ⟨t, ht, hsp⟩ := hP x
    obtain ⟨u, hu, hcard, -⟩ := hM x t _ ht hsp
    refine ⟨u, hu, hcard.trans ?_⟩
    rw [Polynomial.eval_add, Polynomial.eval_C]
    exact mul_two_pow_add_one_le C _
  · obtain ⟨t, ht, hsp⟩ := hP x
    obtain ⟨u, -, -, hacc⟩ := hM x t _ ht hsp
    rw [P.mem_lang_iff_of_halted x t ht, hacc]

end Kolmogorov.RandomStrings
