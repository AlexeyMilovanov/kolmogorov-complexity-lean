/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.StmtTime
import KolmogorovMathlib.RandomStrings.StackTime

/-!
# Step budgets of structured stack programs, time from space, and `PSPACE ⊆ EXP`

Built on the step-counted semantics `ExecT`/`ExecLe` of `KolmogorovMathlib.RandomStrings.StmtTime`
and on `KolmogorovMathlib.RandomStrings.StackTime`:

* `Stmt.mem_EXP`, `Stmt.mem_EXP_of_execLe`: a statement deciding `Φ` within fewer than
  `2 ^ p(|x|)` steps and space `2 ^ p(|x|)` decides a set in `EXP`;
* configuration counting: `Prog.first_halt_le` (a halting run within space `S` halts by time
  `L * 2 ^ ((S + 1) * k)`), `Prog.lang_mem_EXP_of_polySpace` (polynomial-space stack programs are
  in `EXP`), `ExecT.time_le_of_space`, `Exec.execLe_of_space` (every execution within space `S` of a
  statement `s` takes fewer than `(s.size + 3) * 2 ^ ((S + 1) * k)` steps);
* consuming statements (`Stmt.MustPop`, `Stmt.depth`, `Stmt.Consuming`): if every loop pops its
  tested stack on every path and never pushes on it, any execution within space `S` takes at most
  `s.size * (S + 1) ^ s.depth` steps (`Exec.execLe_of_consuming`); certificates that the basic
  routines of `Expspace` are consuming (`consuming_clear`, …, `consuming_memTest`); invariance
  under renaming;
* `PSPACE_subset_EXP` (configuration counting for machines: `halts_within_of_visited`).
-/

namespace Kolmogorov.RandomStrings
/-- **Statements deciding in exponential time.**  A statement that, on every input `x`, decides
`Φ x` on its output stack within fewer than `2 ^ p(|x|)` steps and space `2 ^ p(|x|)` decides a set
in `EXP`. -/
theorem Stmt.mem_EXP {k : ℕ} (s : Stmt k) (out : Fin k) (p : Polynomial ℕ)
    (Φ : BitString → Prop)
    (h : ∀ x : BitString, ∃ σ' T, ExecT s (Stacks.input k x) σ' (2 ^ p.eval x.length) T ∧
      T < 2 ^ p.eval x.length ∧ ((σ' out).head? = some true ↔ Φ x)) :
    {x | Φ x} ∈ EXP := by
  have hP : (s.toProg out).TimeBounded p := fun x => by
    obtain ⟨σ', T, hσ', hT, -⟩ := h x
    obtain ⟨ht, hsp, -⟩ := s.toProg_spec_time out x σ' _ T hσ'
    exact ⟨T + 1, hT, ht, hsp⟩
  have hset : (s.toProg out).Lang = {x | Φ x} := Set.ext fun x => by
    obtain ⟨σ', T, hσ', -, hΦ⟩ := h x
    obtain ⟨ht, -, hacc⟩ := s.toProg_spec_time out x σ' _ T hσ'
    rw [Set.mem_ofPred_eq, Prog.mem_lang_iff_of_halted _ x _ ht, hacc, hΦ]
  rw [← hset]
  exact (s.toProg out).lang_mem_EXP p hP

/-- **Statements deciding within a step budget.**  The form of `Stmt.mem_EXP` with the time bound
stated by `ExecLe`: if on every input `x` the statement `s` decides `Φ x` on its output stack
within space `2 ^ p(|x|)` and at most `2 ^ p(|x|) - 1` steps, then `{x | Φ x} ∈ EXP`. -/
theorem Stmt.mem_EXP_of_execLe {k : ℕ} (s : Stmt k) (out : Fin k) (p : Polynomial ℕ)
    (Φ : BitString → Prop)
    (h : ∀ x : BitString, ∃ σ', ExecLe s (Stacks.input k x) σ' (2 ^ p.eval x.length)
      (2 ^ p.eval x.length - 1) ∧ ((σ' out).head? = some true ↔ Φ x)) :
    {x | Φ x} ∈ EXP := by
  refine s.mem_EXP out p Φ fun x => ?_
  obtain ⟨σ', ⟨T, hT, hσ'⟩, hΦ⟩ := h x
  have := Nat.one_le_two_pow (n := p.eval x.length)
  exact ⟨σ', T, hσ', by omega, hΦ⟩

/-! #### Time from space: counting configurations -/

/-- The strings of length at most `n`. -/
def strsLe : ℕ → Finset BitString
  | 0 => {[]}
  | n + 1 => insert [] ((strsLe n).image (List.cons true) ∪ (strsLe n).image (List.cons false))

/-- A string belongs to `strsLe n` exactly when its length is at most `n`. -/
theorem mem_strsLe : ∀ (n : ℕ) (l : BitString), l ∈ strsLe n ↔ l.length ≤ n
  | 0, l => by cases l <;> simp [strsLe]
  | n + 1, [] => by simp [strsLe]
  | n + 1, b :: l => by
    have := mem_strsLe n l
    cases b <;> simp [strsLe, this]

/-- There are fewer than `2 ^ (n + 1)` strings of length at most `n`:
`(strsLe n).card + 1 ≤ 2 ^ (n + 1)`. -/
theorem card_strsLe : ∀ n : ℕ, (strsLe n).card + 1 ≤ 2 ^ (n + 1)
  | 0 => by simp [strsLe]
  | n + 1 => by
    have ih := card_strsLe n
    have h1 := Finset.card_insert_le ([] : BitString)
      ((strsLe n).image (List.cons true) ∪ (strsLe n).image (List.cons false))
    have h2 := Finset.card_union_le ((strsLe n).image (List.cons true))
      ((strsLe n).image (List.cons false))
    have h3 := Finset.card_image_le (s := strsLe n) (f := List.cons true)
    have h4 := Finset.card_image_le (s := strsLe n) (f := List.cons false)
    have e : strsLe (n + 1) =
        insert [] ((strsLe n).image (List.cons true) ∪ (strsLe n).image (List.cons false)) := rfl
    rw [e, pow_succ]
    omega

/-- Stacks all of whose contents have length at most `S`. -/
def stacksLe (k S : ℕ) : Finset (Stacks k) := Fintype.piFinset fun _ => strsLe S

/-- Stacks `σ` belong to `stacksLe k S` exactly when each of their stacks has length `≤ S`. -/
theorem mem_stacksLe {k S : ℕ} (σ : Stacks k) :
    σ ∈ stacksLe k S ↔ ∀ r, (σ r).length ≤ S := by
  simp [stacksLe, Fintype.mem_piFinset, mem_strsLe]

/-- There are at most `2 ^ ((S + 1) * k)` contents of `k` stacks all of length at most `S`. -/
theorem card_stacksLe (k S : ℕ) : (stacksLe k S).card ≤ 2 ^ ((S + 1) * k) := by
  rw [stacksLe, Fintype.card_piFinset]
  calc ∏ _r : Fin k, (strsLe S).card ≤ ∏ _r : Fin k, 2 ^ (S + 1) :=
        Finset.prod_le_prod (fun _ _ => by have := card_strsLe S; omega)
    _ = 2 ^ ((S + 1) * k) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]

/-- Every stack of a configuration `c` is at most as long as the total space `c.space`, the sum
of the lengths of all its stacks. -/
theorem PConfig.length_le_space {P : Prog} (c : PConfig P) (r : Fin P.k) :
    (c.regs r).length ≤ c.space :=
  Finset.single_le_sum (f := fun r => (c.regs r).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ r)

/-- **Configuration counting.**  If the run of `P` from `c₀` halts at time `t` with all
configurations up to then of space `≤ S`, then it halts by time `L * 2 ^ ((S + 1) * k)`
(`L` instructions, `k` stacks): before the first halting time the configurations are pairwise
distinct, have a program counter `< L`, and stacks of length `≤ S`. -/
theorem Prog.first_halt_le (P : Prog) (c₀ : PConfig P) (t S : ℕ)
    (ht : P.Halted (P.step^[t] c₀)) (hS : ∀ m ≤ t, (P.step^[m] c₀).space ≤ S) :
    ∃ t₀ ≤ t, t₀ ≤ P.code.length * 2 ^ ((S + 1) * P.k) ∧
      P.Halted (P.step^[t₀] c₀) := by
  classical
  have hex : ∃ n, P.Halted (P.step^[n] c₀) := ⟨t, ht⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬ P.Halted (P.step^[m] c₀) := fun m hm => Nat.find_min hex hm
  have hle : Nat.find hex ≤ t := Nat.find_min' hex ht
  generalize Nat.find hex = t₀ at hspec hmin hle
  refine ⟨t₀, hle, ?_, hspec⟩
  have key : ∀ i j, i < j → j < t₀ → P.step^[i] c₀ = P.step^[j] c₀ → False := by
    intro i j hij hj e
    have e₀ : t₀ = (t₀ - j) + j := by omega
    have h1 : P.step^[t₀] c₀ = P.step^[(t₀ - j) + i] c₀ := by
      calc P.step^[t₀] c₀ = P.step^[(t₀ - j) + j] c₀ := by rw [← e₀]
        _ = P.step^[(t₀ - j) + i] c₀ := by
          rw [Function.iterate_add_apply, ← e, ← Function.iterate_add_apply]
    exact hmin ((t₀ - j) + i) (by omega) (by rw [← h1]; exact hspec)
  let f : ℕ → ℕ × Stacks P.k := fun m => ((P.step^[m] c₀).pc, (P.step^[m] c₀).regs)
  have hinj : Set.InjOn f (Finset.range t₀) := by
    intro i hi j hj hfij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have e : P.step^[i] c₀ = P.step^[j] c₀ := by
      simp only [f, Prod.mk.injEq] at hfij
      cases hci : P.step^[i] c₀
      cases hcj : P.step^[j] c₀
      rw [hci, hcj] at hfij
      simp only at hfij
      rw [hfij.1, hfij.2]
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key i j h hj e
    · exact key j i h hi e.symm
  have hsub : (Finset.range t₀).image f ⊆ Finset.range P.code.length ×ˢ stacksLe P.k S := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hz
    have hm' : m < t₀ := Finset.mem_range.1 hm
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, (mem_stacksLe _).2 fun r => ?_⟩
    · change (P.step^[m] c₀).pc < P.code.length
      by_contra hL
      exact hmin m hm' (Or.inr (Or.inr (List.getElem?_eq_none (by omega))))
    · exact (PConfig.length_le_space _ r).trans (hS m (by omega))
  calc t₀ = ((Finset.range t₀).image f).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ (Finset.range P.code.length ×ˢ stacksLe P.k S).card := Finset.card_le_card hsub
    _ = P.code.length * (stacksLe P.k S).card := by rw [Finset.card_product, Finset.card_range]
    _ ≤ P.code.length * 2 ^ ((S + 1) * P.k) := Nat.mul_le_mul_left _ (card_stacksLe _ _)

/-- A stack program halting on every input within *polynomial* space `p(|x|)` is `TimeBounded`
(configuration counting: it halts within `L * 2 ^ ((p(|x|) + 1) * k)` steps). -/
theorem Prog.timeBounded_of_polySpace (P : Prog) (p : Polynomial ℕ)
    (h : ∀ x : BitString, ∃ t, P.Halted (P.run x t) ∧
      ∀ s ≤ t, (P.run x s).space ≤ p.eval x.length) :
    P.TimeBounded (Polynomial.C P.code.length + Polynomial.C (P.k + 1) * (p + 1)) := by
  intro x
  obtain ⟨t, ht, hsp⟩ := h x
  rw [Prog.run_eq_iterate] at ht
  obtain ⟨t₀, ht₀, hbound, hh⟩ := P.first_halt_le (P.init x) t (p.eval x.length) ht
    (fun m hm => by rw [← Prog.run_eq_iterate]; exact hsp m hm)
  have he : (Polynomial.C P.code.length + Polynomial.C (P.k + 1) * (p + 1)).eval x.length =
      P.code.length + (P.k + 1) * (p.eval x.length + 1) := by
    simp
  rw [he]
  have hL : P.code.length ≤ 2 ^ P.code.length := Nat.lt_two_pow_self.le
  have hk : (p.eval x.length + 1) * P.k ≤ (P.k + 1) * (p.eval x.length + 1) := by nlinarith
  have hS : p.eval x.length ≤ (P.k + 1) * (p.eval x.length + 1) := by nlinarith
  have h1 : P.code.length * 2 ^ ((p.eval x.length + 1) * P.k) ≤
      2 ^ (P.code.length + (P.k + 1) * (p.eval x.length + 1)) := by
    rw [pow_add]; exact Nat.mul_le_mul hL (Nat.pow_le_pow_right (by norm_num) hk)
  have h2 : p.eval x.length ≤ 2 ^ (P.code.length + (P.k + 1) * (p.eval x.length + 1)) := by
    have h3 : p.eval x.length < 2 ^ p.eval x.length := Nat.lt_two_pow_self
    have h4 : 2 ^ p.eval x.length ≤ 2 ^ (P.code.length + (P.k + 1) * (p.eval x.length + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨t₀, hbound.trans h1, by rw [Prog.run_eq_iterate]; exact hh,
    fun s hs => (hsp s (by omega)).trans h2⟩

/-- **Polynomial-space stack programs decide sets in `EXP`.** -/
theorem Prog.lang_mem_EXP_of_polySpace (P : Prog) (p : Polynomial ℕ)
    (h : ∀ x : BitString, ∃ t, P.Halted (P.run x t) ∧
      ∀ s ≤ t, (P.run x s).space ≤ p.eval x.length) :
    P.Lang ∈ EXP :=
  P.lang_mem_EXP _ (P.timeBounded_of_polySpace p h)

/-- With no stacks, a statement takes no steps. -/
theorem ExecT.eq_zero_of_fin_zero {s : Stmt 0} {σ σ' : Stacks 0} {S T : ℕ}
    (h : ExecT s σ σ' S T) : T = 0 := by
  induction h with
  | skip _ => rfl
  | seq _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | _ => exact Fin.elim0 ‹Fin 0›

/-- **Time from space for statements.**  An execution of `s` within space `S` takes fewer than
`(s.size + 3) * 2 ^ ((S + 1) * k)` steps (count the configurations of `s.toProg`). -/
theorem ExecT.time_le_of_space {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S T : ℕ}
    (h : ExecT s σ σ' S T) : T + 1 ≤ (s.size + 3) * 2 ^ ((S + 1) * k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [h.eq_zero_of_fin_zero]
    simp
  · obtain ⟨out⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have hcode : (s.toProg out).CodeAt 0 (s.compile 0) := fun i hi => by
      rw [Nat.zero_add]
      exact s.progCode_left out i (hi.trans_eq (Stmt.length_compile s 0))
    obtain ⟨hn, hsp⟩ := ExecT.reachesIn (P := s.toProg out) h 0 hcode
    rw [Nat.zero_add] at hn
    have hσ' : σ'.space ≤ S := h.toExec.space_le.2
    have e0 : (s.toProg out).code[s.size]? =
        some (Stmt.testInstr out (fun o => o == some true) (s.size + 1) (s.size + 2)) := by
      have := s.progCode_right out 0
      rw [Nat.add_zero] at this
      exact this
    have hlast := Prog.step_mk_test (P := s.toProg out) (σ := σ') e0
    have hrun : (s.toProg out).step^[T + 1] ⟨0, σ⟩ =
        ⟨if (σ' out).head? == some true then s.size + 1 else s.size + 2, σ'⟩ := by
      rw [Function.iterate_succ_apply', hn]; exact hlast
    have hacc : (s.toProg out).code[s.size + 1]? = some .accept := s.progCode_right out 1
    have hrej : (s.toProg out).code[s.size + 2]? = some .reject := s.progCode_right out 2
    have hhalt : (s.toProg out).Halted ((s.toProg out).step^[T + 1] ⟨0, σ⟩) := by
      rw [hrun]
      by_cases ht : (σ' out).head? = some true
      · left; simp [ht, hacc]
      · right; left; simp [ht, hrej]
    have hnh : ¬ (s.toProg out).Halted ((s.toProg out).step^[T] ⟨0, σ⟩) := by
      rw [hn]
      change ¬ ((s.toProg out).code[s.size]? = some .accept ∨
        (s.toProg out).code[s.size]? = some .reject ∨ (s.toProg out).code[s.size]? = none)
      rw [e0]
      rintro (h | h | h) <;> cases h
    obtain ⟨t₀, ht₀, hbound, hh⟩ := (s.toProg out).first_halt_le ⟨0, σ⟩ (T + 1) S hhalt
      (fun m hm => by
        rcases Nat.lt_or_ge m (T + 1) with hlt | hge
        · exact hsp m (by omega)
        · rw [show m = T + 1 by omega, hrun]; exact hσ')
    have ht₀' : t₀ = T + 1 := by
      by_contra hne
      apply hnh
      have e : T = (T - t₀) + t₀ := by omega
      rw [e, Function.iterate_add_apply,
        Function.iterate_fixed ((s.toProg out).step_of_halted _ hh)]
      exact hh
    have hL : (s.toProg out).code.length = s.size + 3 := by
      simp [Stmt.toProg, Stmt.progCode, Stmt.length_compile]
    calc T + 1 = t₀ := ht₀'.symm
      _ ≤ (s.toProg out).code.length * 2 ^ ((S + 1) * (s.toProg out).k) := hbound
      _ = (s.size + 3) * 2 ^ ((S + 1) * k) := by rw [hL]; rfl

/-- Any terminating execution within space `S` stays within the step budget
`(s.size + 3) * 2 ^ ((S + 1) * k)`. -/
theorem Exec.execLe_of_space {k : ℕ} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ}
    (h : Exec s σ σ' S) : ExecLe s σ σ' S ((s.size + 3) * 2 ^ ((S + 1) * k)) := by
  obtain ⟨T, hT⟩ := h.exists_execT
  exact ⟨T, by have := hT.time_le_of_space; omega, hT⟩

/-! #### Loops that consume their tested stack -/

/-- Every execution path of `s` pops stack `r` (loops are not counted). -/
def Stmt.MustPop {k : ℕ} (r : Fin k) : Stmt k → Prop
  | .skip => False
  | .push _ _ => False
  | .pop r' => r' = r
  | .seq s₁ s₂ => s₁.MustPop r ∨ s₂.MustPop r
  | .ite _ _ s₁ s₂ => s₁.MustPop r ∧ s₂.MustPop r
  | .loop _ _ _ => False

/-- A statement that never pushes `r` and pops it on every path shortens a nonempty `r`. -/
theorem Exec.length_lt_of_mustPop {k : ℕ} {r : Fin k} {s : Stmt k} {σ σ' : Stacks k} {S : ℕ}
    (h : Exec s σ σ' S) (hs : s.NoPush r) (hp : s.MustPop r) (hne : σ r ≠ []) :
    (σ' r).length < (σ r).length := by
  induction h with
  | skip _ => simp [Stmt.MustPop] at hp
  | push _ => simp [Stmt.MustPop] at hp
  | @pop r' σ S _ =>
    simp only [Stmt.MustPop] at hp
    subst hp
    rw [Function.update_self, List.length_tail]
    have : 0 < (σ r').length := List.length_pos_of_ne_nil hne
    omega
  | @seq s₁ s₂ σ σ₁ σ₂ S h₁ h₂ ih₁ ih₂ =>
    simp only [Stmt.NoPush, Stmt.MustPop] at hs hp
    have l₁ := h₁.length_le_of_noPush hs.1
    have l₂ := h₂.length_le_of_noPush hs.2
    rcases hp with hp | hp
    · exact lt_of_le_of_lt l₂ (ih₁ hs.1 hp hne)
    · rcases Nat.lt_or_ge (σ₁ r).length (σ r).length with hlt | hge
      · exact lt_of_le_of_lt l₂ hlt
      · have hne₁ : σ₁ r ≠ [] := by
          intro he
          apply hne
          apply List.eq_nil_of_length_eq_zero
          rw [he, List.length_nil] at hge
          omega
        exact lt_of_lt_of_le (ih₂ hs.2 hp hne₁) (by omega)
  | iteT _ _ ih =>
    simp only [Stmt.NoPush, Stmt.MustPop] at hs hp
    exact ih hs.1 hp.1 hne
  | iteF _ _ ih =>
    simp only [Stmt.NoPush, Stmt.MustPop] at hs hp
    exact ih hs.2 hp.2 hne
  | loopT _ _ _ _ _ => simp [Stmt.MustPop] at hp
  | loopF _ _ => simp [Stmt.MustPop] at hp

/-- **Loops consuming their tested stack.**  If the condition of `loop r cond body` implies that
`r` is nonempty, and the loop-free body never pushes `r` and pops it on every path, then every
execution of the loop from `σ` takes at most `|σ r| * (body.size + 2) + 1` steps. -/
theorem Exec.execLe_loop_of_pop {k : ℕ} {r : Fin k} {cond : Option Bool → Bool} {body : Stmt k}
    (hcond : ∀ o, cond o = true → o.isSome = true) (hlf : body.LoopFree) (hnp : body.NoPush r)
    (hmp : body.MustPop r) {σ σ' : Stacks k} {S : ℕ} (h : Exec (.loop r cond body) σ σ' S) :
    ExecLe (.loop r cond body) σ σ' S ((σ r).length * (body.size + 2) + 1) := by
  refine ExecLe.loop_of_exec (fun _ => True) (fun σ => (σ r).length) S body.size
    (fun σ₁ σ₂ _ hc hb => ⟨hb.execLe_of_loopFree hlf, trivial, ?_⟩) σ σ' trivial h
  refine hb.length_lt_of_mustPop hnp hmp fun he => ?_
  have := hcond _ hc
  rw [he] at this
  simp at this

/-- Loop nesting depth. -/
def Stmt.depth {k : ℕ} : Stmt k → ℕ
  | .skip => 0
  | .push _ _ => 0
  | .pop _ => 0
  | .seq s₁ s₂ => max s₁.depth s₂.depth
  | .ite _ _ s₁ s₂ => max s₁.depth s₂.depth
  | .loop _ _ b => b.depth + 1

/-- Every loop of `s` consumes its tested stack: the condition implies that the stack is
nonempty, and the body never pushes on it and pops it on every path. -/
def Stmt.Consuming {k : ℕ} : Stmt k → Prop
  | .skip => True
  | .push _ _ => True
  | .pop _ => True
  | .seq s₁ s₂ => s₁.Consuming ∧ s₂.Consuming
  | .ite _ _ s₁ s₂ => s₁.Consuming ∧ s₂.Consuming
  | .loop r cond b => (∀ o, cond o = true → o.isSome = true) ∧ b.NoPush r ∧ b.MustPop r ∧
      b.Consuming

/-- Arithmetic of the loop budget: for `L ≤ S` and `1 ≤ P`, the cost `L * (b * P + 2) + 1` of
`L` iterations (each a body of at most `b * P` steps plus two steps for the test) and a last
test is at most `(b + 2) * (S + 1) ^ 0 * (P * (S + 1))`. -/
theorem consuming_loop_budget {L S b P : ℕ} (hL : L ≤ S) (hP : 1 ≤ P) :
    L * (b * P + 2) + 1 ≤ (b + 2) * (S + 1) ^ 0 * (P * (S + 1)) := by
  have h1 : L * (b * P + 2) ≤ S * (b * P + 2) := Nat.mul_le_mul_right _ hL
  have h3 : S ≤ P * S := Nat.le_mul_of_pos_left S hP
  have e1 : (b + 2) * (S + 1) ^ 0 * (P * (S + 1)) = S * (b * P) + b * P + 2 * (P * S) + 2 * P := by
    ring
  have e2 : S * (b * P + 2) = S * (b * P) + 2 * S := by ring
  omega

/-- **Consuming statements run in time polynomial in their space**: an execution of a
consuming statement within space `S` takes at most `s.size * (S + 1) ^ s.depth` steps. -/
theorem Exec.execLe_of_consuming {k : ℕ} :
    ∀ {s : Stmt k}, s.Consuming → ∀ {σ σ' : Stacks k} {S : ℕ}, Exec s σ σ' S →
      ExecLe s σ σ' S (s.size * (S + 1) ^ s.depth)
  | .skip, _, _, _, _, h => (h.execLe_of_loopFree trivial).mono_time (by simp [Stmt.size])
  | .push _ _, _, _, _, _, h =>
    (h.execLe_of_loopFree trivial).mono_time (by simp [Stmt.size, Stmt.depth])
  | .pop _, _, _, _, _, h =>
    (h.execLe_of_loopFree trivial).mono_time (by simp [Stmt.size, Stmt.depth])
  | .seq s₁ s₂, hs, σ, σ', S, h => by
    obtain ⟨σ₁, h₁, h₂⟩ := Exec.seq_iff.1 h
    have e₁ := Exec.execLe_of_consuming hs.1 h₁
    have e₂ := Exec.execLe_of_consuming hs.2 h₂
    refine (ExecLe.seq e₁ e₂).mono_time ?_
    have p₁ : (S + 1) ^ s₁.depth ≤ (S + 1) ^ (max s₁.depth s₂.depth) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have p₂ : (S + 1) ^ s₂.depth ≤ (S + 1) ^ (max s₁.depth s₂.depth) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    simp only [Stmt.size, Stmt.depth, add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ p₁) (Nat.mul_le_mul_left _ p₂)
  | .ite r cond s₁ s₂, hs, σ, σ', S, h => by
    have p₁ : (S + 1) ^ s₁.depth ≤ (S + 1) ^ (max s₁.depth s₂.depth) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have p₂ : (S + 1) ^ s₂.depth ≤ (S + 1) ^ (max s₁.depth s₂.depth) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have p₀ : 1 ≤ (S + 1) ^ (max s₁.depth s₂.depth) := Nat.one_le_pow _ _ (by omega)
    simp only [Stmt.size, Stmt.depth]
    cases h with
    | iteT hc h₁ =>
      refine (ExecLe.iteT hc (Exec.execLe_of_consuming hs.1 h₁)).mono_time ?_
      have := Nat.mul_le_mul_left s₁.size p₁
      nlinarith
    | iteF hc h₂ =>
      refine (ExecLe.iteF hc (Exec.execLe_of_consuming hs.2 h₂)).mono_time ?_
      have := Nat.mul_le_mul_left s₂.size p₂
      nlinarith
  | .loop r cond b, hs, σ, σ', S, h => by
    obtain ⟨hcond, hnp, hmp, hb⟩ := hs
    have hloop := ExecLe.loop_of_exec (r := r) (cond := cond) (body := b) (fun _ => True)
      (fun σ => (σ r).length) S (b.size * (S + 1) ^ b.depth)
      (fun σ₁ σ₂ _ hc hx => ⟨Exec.execLe_of_consuming hb hx, trivial,
        hx.length_lt_of_mustPop hnp hmp fun he => by
          have := hcond _ hc
          rw [he] at this
          simp at this⟩) σ σ' trivial h
    refine hloop.mono_time ?_
    have hL : (σ r).length ≤ S := (QEnum.length_le_space σ r).trans h.space_le.1
    have hP : 1 ≤ (S + 1) ^ b.depth := Nat.one_le_pow _ _ (by omega)
    have := consuming_loop_budget (b := b.size) hL hP
    simp only [Stmt.size, Stmt.depth, pow_succ]
    simpa [pow_zero, mul_one, mul_assoc] using this

/-! #### The basic routines are consuming

Hence (`Exec.execLe_of_consuming`) each of them, executed within space `S`, takes at most
`size * (S + 1) ^ depth` steps; `depth = 1` for all of them except `memTest` (`depth = 2`). -/

namespace Stmt

variable {k : ℕ}

/-- `clear r` is consuming: its only loop tests `r` and pops it at every step. -/
theorem consuming_clear (r : Fin k) : (clear r).Consuming := by
  simp [clear, Stmt.Consuming, Stmt.NoPush, Stmt.MustPop]

/-- `moveAll r r'` is consuming for distinct stacks `r ≠ r'`: its loop pops `r` at every step and
pushes only on `r'`. -/
theorem consuming_moveAll {r r' : Fin k} (h : r ≠ r') : (moveAll r r').Consuming := by
  simp [moveAll, moveBit, caseBit, Stmt.Consuming, Stmt.NoPush, Stmt.MustPop, Ne.symm h]

/-- `copy r r' t` is consuming when the work stack `t` differs from `r` and `r'`: the loop of
`moveAll r t` pops `r`, and the loop copying `t` back pops `t` and pushes only on `r` and `r'`. -/
theorem consuming_copy {r r' t : Fin k} (hrt : r ≠ t) (hr't : r' ≠ t) :
    (copy r r' t).Consuming := by
  refine ⟨consuming_moveAll hrt, ?_⟩
  simp [dupStep, caseBit, seqs, Stmt.Consuming, Stmt.NoPush, Stmt.MustPop, hrt, hr't]

/-- `addInto A B Cy R` is consuming when `A` differs from the carry stack `Cy` and the result
stack `R`: the addition loop pops `A` at every step and pushes only on `Cy` and `R`, and the
routines `clear Cy` and `moveAll R A` after it are consuming. -/
theorem consuming_addInto {A B Cy R : Fin k} (hAC : A ≠ Cy) (hAR : A ≠ R) :
    (addInto A B Cy R).Consuming := by
  simp only [addInto, seqs, Stmt.Consuming, true_and, and_true]
  refine ⟨⟨fun _ h => h, ?_, ?_, ?_⟩, consuming_clear Cy, consuming_moveAll (Ne.symm hAR)⟩
  · simp [addStep, caseBit, seqs, Stmt.NoPush, Ne.symm hAC, Ne.symm hAR]
  · simp [addStep, caseBit, seqs, Stmt.MustPop]
  · simp [addStep, caseBit, seqs, Stmt.Consuming]

/-- `cmpInto A B F` is consuming when `A ≠ F`: the comparison loop pops `A` at every step and
pushes only on `F`. -/
theorem consuming_cmpInto {A B F : Fin k} (hAF : A ≠ F) : (cmpInto A B F).Consuming := by
  simp only [cmpInto, seqs, Stmt.Consuming, true_and, and_true]
  refine ⟨fun _ h => h, ?_, ?_, ?_⟩
  · simp [cmpStep, caseBit, seqs, Stmt.NoPush, Ne.symm hAF]
  · simp [cmpStep, caseBit, seqs, Stmt.MustPop]
  · simp [cmpStep, caseBit, seqs, Stmt.Consuming]

/-- `eqTest A B tA tB F` is consuming when `A` differs from `tA`, `tB` and `F`, and `B` differs
from `tB`: its loop pops `A` at every step without pushing on it, and the routines restoring `A`
and `B` afterwards are `moveAll`s between distinct stacks. -/
theorem consuming_eqTest {A B tA tB F : Fin k} (h2 : A ≠ tA) (h3 : A ≠ tB) (h4 : A ≠ F)
    (h6 : B ≠ tB) :
    (eqTest A B tA tB F).Consuming := by
  simp only [eqTest, seqs, Stmt.Consuming, true_and, and_true]
  refine ⟨⟨fun _ h => h, ?_, ?_, ?_⟩, ⟨trivial, trivial⟩, consuming_moveAll h6,
    consuming_moveAll (Ne.symm h2), consuming_moveAll (Ne.symm h6)⟩
  · simp [eqStep, caseBit, moveBit, clearFlag, Stmt.NoPush, Ne.symm h2, Ne.symm h3, Ne.symm h4]
  · simp [eqStep, caseBit, moveBit, Stmt.MustPop]
  · simp [eqStep, caseBit, moveBit, clearFlag, Stmt.Consuming]

/-- The condition `isTrue` holds only of a nonempty stack: `isTrue o = true` implies
`o.isSome = true` for the top `o` of a stack. -/
theorem isTrue_imp_isSome : ∀ o : Option Bool, isTrue o = true → o.isSome = true := by
  intro o h; cases o <;> simp_all [isTrue]

/-- `incr A t C` is consuming when `A ≠ t`: its loop over the trailing ones of `A` pops `A` at
every step and pushes only on `t`, and its last step is `moveAll t A`. -/
theorem consuming_incr {A t C : Fin k} (hAt : A ≠ t) : (incr A t C).Consuming := by
  simp only [incr, seqs, Stmt.Consuming, Stmt.NoPush, ne_eq, Ne.symm hAt, not_false_eq_true,
    and_self, Stmt.MustPop, or_false, and_true, consuming_moveAll (Ne.symm hAt)]
  exact isTrue_imp_isSome

/-- `decodeOne Lst W Tmp` is consuming when the stack `Lst` holding the coded list differs from
`W` and `Tmp`: its loop pops `Lst` at every step and pushes only on `W` and `Tmp`. -/
theorem consuming_decodeOne {Lst W Tmp : Fin k} (h1 : Lst ≠ W) (h2 : Lst ≠ Tmp) :
    (decodeOne Lst W Tmp).Consuming := by
  simp only [decodeOne, decodeBody, moveBit, caseBit, Stmt.Consuming, Stmt.NoPush, ne_eq,
    Ne.symm h2, not_false_eq_true, and_self, Ne.symm h1, Stmt.MustPop, or_false, or_self,
    and_true]
  exact isTrue_imp_isSome

end Stmt

/-- The membership test `Stmt.memTest` is consuming: its loop over the coded list on stack `1`,
like the loops of the routines it calls, pops the stack it tests and never pushes on it. -/
theorem Stmt.consuming_memTest : Stmt.memTest.Consuming := by
  simp only [Stmt.memTest, Stmt.seqs, Stmt.Consuming, true_and, and_true]
  refine ⟨⟨fun _ h => h, ?_, ?_, ?_⟩, Stmt.consuming_moveAll (by decide)⟩
  · simp [Stmt.memStep, Stmt.seqs, Stmt.decodeOne, Stmt.decodeBody, Stmt.moveAll, Stmt.moveBit,
      Stmt.caseBit, Stmt.eqTest, Stmt.eqStep, Stmt.clearFlag, Stmt.setFlag, Stmt.clear,
      Stmt.NoPush]
  · simp [Stmt.memStep, Stmt.seqs, Stmt.decodeOne, Stmt.moveBit, Stmt.caseBit, Stmt.MustPop]
  · simp only [Stmt.memStep, Stmt.seqs, Stmt.Consuming, and_true]
    refine ⟨Stmt.consuming_decodeOne (by decide) (by decide), Stmt.consuming_moveAll (by decide),
      Stmt.consuming_eqTest (by decide) (by decide) (by decide) (by decide), ?_, trivial,
      Stmt.consuming_clear 4⟩
    simp [Stmt.caseBit, Stmt.setFlag, Stmt.Consuming]

/-- The loops of the membership test `Stmt.memTest` are nested to depth `2`. -/
theorem Stmt.depth_memTest : Stmt.memTest.depth = 2 := rfl

/-- The compiled membership test `Stmt.memTest` consists of `142` instructions. -/
theorem Stmt.size_memTest : Stmt.memTest.size = 142 := rfl

/-- Any execution of the membership test `memTest` within space `S` takes at most
`142 * (S + 1) ^ 2` steps. -/
theorem Stmt.execLe_memTest_of_exec {σ σ' : Stacks 9} {S : ℕ} (h : Exec Stmt.memTest σ σ' S) :
    ExecLe Stmt.memTest σ σ' S (142 * (S + 1) ^ 2) := by
  have := h.execLe_of_consuming Stmt.consuming_memTest
  rwa [Stmt.depth_memTest, Stmt.size_memTest] at this

/-- Any execution of `eqTest` within space `S` takes at most `size * (S + 1)` steps. -/
theorem Stmt.execLe_eqTest_of_exec {k : ℕ} {A B tA tB F : Fin k} (h2 : A ≠ tA) (h3 : A ≠ tB)
    (h4 : A ≠ F) (h6 : B ≠ tB) {σ σ' : Stacks k} {S : ℕ}
    (h : Exec (Stmt.eqTest A B tA tB F) σ σ' S) :
    ExecLe (Stmt.eqTest A B tA tB F) σ σ' S ((Stmt.eqTest A B tA tB F).size * (S + 1)) := by
  have := h.execLe_of_consuming (Stmt.consuming_eqTest h2 h3 h4 h6)
  have hd : (Stmt.eqTest A B tA tB F).depth = 1 := rfl
  rwa [hd, pow_one] at this

/-! #### Composing consuming statements -/

namespace Stmt

variable {k k' : ℕ}

/-- Renaming the stacks of a statement does not change its loop nesting depth. -/
theorem depth_rename (f : Fin k → Fin k') (s : Stmt k) : (s.rename f).depth = s.depth := by
  induction s with
  | skip => rfl
  | push => rfl
  | pop => rfl
  | seq s₁ s₂ ih₁ ih₂ => simp only [rename, depth, ih₁, ih₂]
  | ite r c s₁ s₂ ih₁ ih₂ => simp only [rename, depth, ih₁, ih₂]
  | loop r c b ih => simp only [rename, depth, ih]

/-- A statement is loop-free after renaming its stacks exactly when it is loop-free before. -/
theorem loopFree_rename (f : Fin k → Fin k') (s : Stmt k) :
    (s.rename f).LoopFree ↔ s.LoopFree := by
  induction s with
  | skip => exact Iff.rfl
  | push => exact Iff.rfl
  | pop => exact Iff.rfl
  | seq s₁ s₂ ih₁ ih₂ => simp only [rename, LoopFree, ih₁, ih₂]
  | ite r c s₁ s₂ ih₁ ih₂ => simp only [rename, LoopFree, ih₁, ih₂]
  | loop r c b ih => exact Iff.rfl

/-- Along an injective renaming `f`, the renamed statement `s.rename f` never pushes on `f r`
exactly when `s` never pushes on `r`. -/
theorem noPush_rename_iff {f : Fin k → Fin k'} (hf : Function.Injective f) (r : Fin k)
    (s : Stmt k) : (s.rename f).NoPush (f r) ↔ s.NoPush r := by
  induction s with
  | skip => exact Iff.rfl
  | push r' b => exact hf.ne_iff
  | pop => exact Iff.rfl
  | seq s₁ s₂ ih₁ ih₂ => simp only [rename, NoPush, ih₁, ih₂]
  | ite r' c s₁ s₂ ih₁ ih₂ => simp only [rename, NoPush, ih₁, ih₂]
  | loop r' c b ih => simp only [rename, NoPush, ih]

/-- Along an injective renaming `f`, every path of `s.rename f` pops `f r` exactly when every
path of `s` pops `r`. -/
theorem mustPop_rename {f : Fin k → Fin k'} (hf : Function.Injective f) (r : Fin k) (s : Stmt k) :
    (s.rename f).MustPop (f r) ↔ s.MustPop r := by
  induction s with
  | skip => exact Iff.rfl
  | push => exact Iff.rfl
  | pop r' => exact hf.eq_iff
  | seq s₁ s₂ ih₁ ih₂ => simp only [rename, MustPop, ih₁, ih₂]
  | ite r' c s₁ s₂ ih₁ ih₂ => simp only [rename, MustPop, ih₁, ih₂]
  | loop r' c b ih => exact Iff.rfl

/-- Inlining along an injective renaming preserves being consuming. -/
theorem consuming_rename {f : Fin k → Fin k'} (hf : Function.Injective f) (s : Stmt k) :
    (s.rename f).Consuming ↔ s.Consuming := by
  induction s with
  | skip => exact Iff.rfl
  | push => exact Iff.rfl
  | pop => exact Iff.rfl
  | seq s₁ s₂ ih₁ ih₂ => simp only [rename, Consuming, ih₁, ih₂]
  | ite r c s₁ s₂ ih₁ ih₂ => simp only [rename, Consuming, ih₁, ih₂]
  | loop r c b ih =>
    simp only [rename, Consuming, ih, noPush_rename_iff hf, mustPop_rename hf]

/-- A sequential composition `seqs l` is consuming when every statement of the list `l` is. -/
theorem consuming_seqs (l : List (Stmt k)) (h : ∀ s ∈ l, s.Consuming) : (seqs l).Consuming := by
  induction l with
  | nil => trivial
  | cons s l ih =>
    exact ⟨h s (List.mem_cons_self ..), ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')⟩

/-- `caseBit r s` is consuming when both of its branches `s true` and `s false` are. -/
theorem consuming_caseBit (r : Fin k) (s : Bool → Stmt k) (h₁ : (s true).Consuming)
    (h₂ : (s false).Consuming) : (caseBit r s).Consuming := ⟨h₁, h₂⟩

end Stmt

/-! ### `PSPACE ⊆ EXP`: configuration counting for machines -/

/-- The configuration with the query buffer erased. -/
def eraseBuf {M : OTM} (c : Config M) : Config M := ⟨c.q, c.tape, c.head, []⟩

/-- With oracle `∅` the query buffer does not influence state, tape and head. -/
theorem eraseBuf_step (M : OTM) (c : Config M) :
    eraseBuf (step M ∅ c) = eraseBuf (step M ∅ (eraseBuf c)) := by
  change eraseBuf (step M ∅ c) = eraseBuf (step M ∅ ⟨c.q, c.tape, c.head, []⟩)
  by_cases hc : Halted M c
  · have hc' : Halted M ⟨c.q, c.tape, c.head, []⟩ := hc
    rw [step_of_halted M ∅ c hc, step_of_halted M ∅ _ hc']; rfl
  · have hc' : ¬ Halted M ⟨c.q, c.tape, c.head, []⟩ := hc
    unfold step
    rw [ite_eq_right hc, ite_eq_right hc']
    dsimp only
    cases M.δ c.q (c.tape c.head) <;> simp [eraseBuf]

/-- If the runs of `M` on `x` with oracle `∅` agree up to the query buffer at times `i` and `j`,
they agree up to the query buffer at times `i + n` and `j + n` for every `n`. -/
theorem eraseBuf_run_add (M : OTM) (x : BitString) (i j : ℕ)
    (h : eraseBuf (run M ∅ x i) = eraseBuf (run M ∅ x j)) :
    ∀ n, eraseBuf (run M ∅ x (i + n)) = eraseBuf (run M ∅ x (j + n))
  | 0 => h
  | n + 1 => by
    change eraseBuf (step M ∅ (run M ∅ x (i + n))) = eraseBuf (step M ∅ (run M ∅ x (j + n)))
    rw [eraseBuf_step M (run M ∅ x (i + n)), eraseBuf_run_add M x i j h n,
      ← eraseBuf_step M (run M ∅ x (j + n))]

/-- A cell that the head has not visited keeps its initial content. -/
theorem tape_run_of_not_visited (M : OTM) (x : BitString) (i : ℤ) :
    ∀ m, (∀ s < m, (run M ∅ x s).head ≠ i) → (run M ∅ x m).tape i = (init M x).tape i
  | 0, _ => rfl
  | m + 1, h => by
    have ih := tape_run_of_not_visited M x i m (fun s hs => h s (by omega))
    have hne : (run M ∅ x m).head ≠ i := h m (by omega)
    change (step M ∅ (run M ∅ x m)).tape i = _
    by_cases hc : Halted M (run M ∅ x m)
    · rw [step_of_halted M ∅ _ hc]; exact ih
    · unfold step
      rw [ite_eq_right hc]
      split
      · dsimp only; rw [Function.update_of_ne (Ne.symm hne)]; exact ih
      · exact ih
      · exact ih

/-- For all natural numbers `a` and `s`, `a * s * 3 ^ s ≤ 2 ^ (a + 3 * s)`. -/
theorem card_mul_pow_le (a s : ℕ) : a * s * 3 ^ s ≤ 2 ^ (a + 3 * s) := by
  have h1 : a ≤ 2 ^ a := Nat.lt_two_pow_self.le
  have h2 : s ≤ 2 ^ s := Nat.lt_two_pow_self.le
  have h3 : 3 ^ s ≤ 4 ^ s := Nat.pow_le_pow_left (by norm_num) s
  have h4 : (4 : ℕ) ^ s = 2 ^ (2 * s) := by rw [pow_mul]; norm_num
  have h5 : 2 ^ (a + 3 * s) = 2 ^ a * 2 ^ s * 2 ^ (2 * s) := by
    rw [← pow_add, ← pow_add]; ring_nf
  rw [h5]
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (h3.trans h4.le)

/-- **Configuration counting for machines** (oracle `∅`): a machine that halts on `x` at time
`t` having visited the cells `V` halts by time `|Q| * |V| * 3 ^ |V|`. -/
theorem halts_within_of_visited (M : OTM) (x : BitString) (t : ℕ)
    (ht : Halted M (run M ∅ x t)) :
    ∃ t₀ ≤ t,
      t₀ ≤ Fintype.card M.Q * (visited M ∅ x t).card * 3 ^ (visited M ∅ x t).card ∧
      Halted M (run M ∅ x t₀) := by
  classical
  have hex : ∃ n, Halted M (run M ∅ x n) := ⟨t, ht⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬ Halted M (run M ∅ x m) := fun m hm => Nat.find_min hex hm
  have hle : Nat.find hex ≤ t := Nat.find_min' hex ht
  generalize Nat.find hex = t₀ at hspec hmin hle
  refine ⟨t₀, hle, ?_, hspec⟩
  generalize hV : visited M ∅ x t = V
  have key : ∀ i j, i < j → j < t₀ →
      eraseBuf (run M ∅ x i) = eraseBuf (run M ∅ x j) → False := by
    intro i j hij hj e
    have h1 := eraseBuf_run_add M x i j e (t₀ - j)
    rw [show j + (t₀ - j) = t₀ by omega] at h1
    apply hmin (i + (t₀ - j)) (by omega)
    have hq := congrArg Config.q h1
    simp only [eraseBuf] at hq
    unfold Halted; rw [hq]; exact hspec
  have hhead : ∀ m ≤ t, (run M ∅ x m).head ∈ V := fun m hm => by
    rw [← hV]; exact Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩
  have htape : ∀ m ≤ t, ∀ i ∉ V, (run M ∅ x m).tape i = (init M x).tape i :=
    fun m hm i hi => tape_run_of_not_visited M x i m fun s hs he => hi (he ▸ hhead s (by omega))
  let f : ℕ → M.Q × ℤ × (V → Sym) := fun m =>
    ((run M ∅ x m).q, (run M ∅ x m).head, fun v => (run M ∅ x m).tape v)
  have hinj : Set.InjOn f (Finset.range t₀) := by
    intro i hi j hj hfij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only [f, Prod.mk.injEq] at hfij
    obtain ⟨hq, hh, ht'⟩ := hfij
    have htp : (run M ∅ x i).tape = (run M ∅ x j).tape := by
      funext z
      by_cases hz : z ∈ V
      · exact congrFun ht' ⟨z, hz⟩
      · rw [htape i (by omega) z hz, htape j (by omega) z hz]
    have e : eraseBuf (run M ∅ x i) = eraseBuf (run M ∅ x j) := by
      unfold eraseBuf; rw [hq, hh, htp]
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key i j h hj e
    · exact key j i h hi e.symm
  have hsub : (Finset.range t₀).image f ⊆
      (Finset.univ : Finset M.Q) ×ˢ V ×ˢ (Finset.univ : Finset (V → Sym)) := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hz
    simp only [Finset.mem_product, Finset.mem_univ, true_and, and_true]
    exact hhead m (by have := Finset.mem_range.1 hm; omega)
  calc t₀ = ((Finset.range t₀).image f).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ ((Finset.univ : Finset M.Q) ×ˢ V ×ˢ (Finset.univ : Finset (V → Sym))).card :=
        Finset.card_le_card hsub
    _ = Fintype.card M.Q * V.card * 3 ^ V.card := by
        simp [Finset.card_product, mul_assoc]

/-- **`PSPACE ⊆ EXP`.**  A set decided by a machine that visits at most `p(|x|)` cells is decided
by the same machine within `2 ^ (|Q| + 3 * p(|x|))` steps (`|Q|` is the number of states), since
the machine cannot repeat a configuration before it halts. -/
theorem PSPACE_subset_EXP : PSPACE ⊆ EXP := by
  rintro A ⟨M, p, hM, hA⟩
  refine ⟨M, Polynomial.C (Fintype.card M.Q) + Polynomial.C 3 * p, fun x => ?_, hA⟩
  obtain ⟨t, ht, hcard⟩ := hM x
  obtain ⟨t₀, -, hb, hh⟩ := halts_within_of_visited M x t ht
  refine ⟨t₀, hb.trans ?_, hh⟩
  have he : (Polynomial.C (Fintype.card M.Q) + Polynomial.C 3 * p).eval x.length =
      Fintype.card M.Q + 3 * p.eval x.length := by simp
  rw [he]
  calc Fintype.card M.Q * (visited M ∅ x t).card * 3 ^ (visited M ∅ x t).card
      ≤ Fintype.card M.Q * p.eval x.length * 3 ^ p.eval x.length :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hcard) (Nat.pow_le_pow_right (by norm_num) hcard)
    _ ≤ _ := card_mul_pow_le _ _

/-! ### End-to-end criteria for `EXP` -/

/-- **Statements running in time polynomial in their space, within exponential space, decide
sets in `EXP`.**  The hypothesis `htime` is a step bound `c * (S + 1) ^ d` valid for every
execution of `s` within space `S`; for a consuming statement it holds with `c = s.size` and
`d = s.depth` (`Exec.execLe_of_consuming`). -/
theorem Stmt.mem_EXP_of_polyTimeInSpace {k : ℕ} (s : Stmt k) (out : Fin k) (p : Polynomial ℕ)
    (c d : ℕ) (Φ : BitString → Prop)
    (htime : ∀ (σ σ' : Stacks k) (S : ℕ),
      Exec s σ σ' S → ExecLe s σ σ' S (c * (S + 1) ^ d))
    (h : ∀ x : BitString, ∃ σ', Exec s (Stacks.input k x) σ' (2 ^ p.eval x.length) ∧
      ((σ' out).head? = some true ↔ Φ x)) :
    {x | Φ x} ∈ EXP := by
  refine s.mem_EXP out (Polynomial.C c + (p + 1) * Polynomial.C (d + 1)) Φ fun x => ?_
  obtain ⟨σ', hσ', hΦ⟩ := h x
  obtain ⟨T, hT, hT'⟩ := htime _ _ _ hσ'
  have he : (Polynomial.C c + (p + 1) * Polynomial.C (d + 1)).eval x.length =
      c + (p.eval x.length + 1) * (d + 1) := by simp
  rw [he]
  have h1 : 2 ^ p.eval x.length + 1 ≤ 2 ^ (p.eval x.length + 1) := by
    rw [pow_succ]; have := Nat.one_le_two_pow (n := p.eval x.length); omega
  have h2 : (2 ^ p.eval x.length + 1) ^ d ≤ 2 ^ ((p.eval x.length + 1) * (d + 1)) :=
    calc (2 ^ p.eval x.length + 1) ^ d ≤ (2 ^ (p.eval x.length + 1)) ^ d :=
          Nat.pow_le_pow_left h1 d
      _ = 2 ^ ((p.eval x.length + 1) * d) := by rw [← pow_mul]
      _ ≤ 2 ^ ((p.eval x.length + 1) * (d + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ d))
  have h3 : c < 2 ^ c := Nat.lt_two_pow_self
  have h4 : 1 ≤ 2 ^ ((p.eval x.length + 1) * (d + 1)) := Nat.one_le_two_pow
  have h5 : T < 2 ^ (c + (p.eval x.length + 1) * (d + 1)) := by
    rw [pow_add]
    calc T ≤ c * (2 ^ p.eval x.length + 1) ^ d := hT
      _ ≤ c * 2 ^ ((p.eval x.length + 1) * (d + 1)) := Nat.mul_le_mul_left _ h2
      _ < 2 ^ c * 2 ^ ((p.eval x.length + 1) * (d + 1)) := Nat.mul_lt_mul_of_pos_right h3 h4
  have h6 : 2 ^ p.eval x.length ≤ 2 ^ (c + (p.eval x.length + 1) * (d + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  exact ⟨σ', T, hT'.mono h6, h5, hΦ⟩

/-- **Consuming statements deciding within exponential space decide sets in `EXP`.** -/
theorem Stmt.mem_EXP_of_consuming {k : ℕ} (s : Stmt k) (hs : s.Consuming) (out : Fin k)
    (p : Polynomial ℕ) (Φ : BitString → Prop)
    (h : ∀ x : BitString, ∃ σ', Exec s (Stacks.input k x) σ' (2 ^ p.eval x.length) ∧
      ((σ' out).head? = some true ↔ Φ x)) :
    {x | Φ x} ∈ EXP :=
  s.mem_EXP_of_polyTimeInSpace out p s.size s.depth Φ
    (fun _ _ _ hx => hx.execLe_of_consuming hs) h

end Kolmogorov.RandomStrings
