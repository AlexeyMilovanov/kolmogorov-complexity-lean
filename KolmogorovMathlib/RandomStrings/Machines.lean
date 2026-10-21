/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Basic

/-!
# Codes of oracle machines, clocks, and the queries made under all oracles

* `OTMCode`: machines with state set `Fin k`; every `OTM` is behaviourally equivalent to one.
* `clock e n = n ^ e + e`: the clock put on the `e`-th machine in the enumeration of all
  polynomial-time oracle machines (`ClockedAccepts`, `ClockedDecides`).
* `queryAll M x T`: the strings that `M` can query on input `x` within `T` steps under *some*
  oracle; the verdict of a clocked machine depends only on the oracle's restriction to this set.
-/

namespace Kolmogorov.RandomStrings

/-- A machine with states `Fin k`, a finite object. -/
structure OTMCode where
  k : ℕ
  start : Fin k
  accept : Fin k
  reject : Fin k
  δ : Fin k → Sym → Act (Fin k)

/-- The machine coded by `c`. -/
def OTMCode.toOTM (c : OTMCode) : OTM :=
  { Q := Fin c.k, fin := inferInstance, start := c.start, accept := c.accept,
    reject := c.reject, δ := c.δ }

/-- Numbering of head movements. -/
def Move.toNat : Move → ℕ
  | .left => 0
  | .stay => 1
  | .right => 2

/-- The numbering of head movements is injective. -/
theorem Move.toNat_injective : Function.Injective Move.toNat := by
  intro a b h
  cases a <;> cases b <;> simp_all [Move.toNat]

instance : Countable Move := Move.toNat_injective.countable

/-- Encoding of actions as a sum of products. -/
def Act.encode {Q : Type} : Act Q → (Q × Sym × Move) ⊕ (Q × Bool) ⊕ (Q × Q)
  | .step q a m => Sum.inl (q, a, m)
  | .push q b => Sum.inr (Sum.inl (q, b))
  | .ask q₁ q₂ => Sum.inr (Sum.inr (q₁, q₂))

/-- The encoding of actions is injective. -/
theorem Act.encode_injective {Q : Type} : Function.Injective (@Act.encode Q) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Act.encode]

instance {Q : Type} [Countable Q] : Countable (Act Q) := Act.encode_injective.countable

/-- Encoding of codes as dependent tuples. -/
def OTMCode.encode (c : OTMCode) :
    Σ k : ℕ, Fin k × Fin k × Fin k × (Fin k → Sym → Act (Fin k)) :=
  ⟨c.k, c.start, c.accept, c.reject, c.δ⟩

/-- The encoding of codes is injective. -/
theorem OTMCode.encode_injective : Function.Injective OTMCode.encode := by
  rintro ⟨k, s, a, r, d⟩ ⟨k', s', a', r', d'⟩ h
  simp only [OTMCode.encode, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- There are countably many codes. -/
theorem OTMCode.countable : Countable OTMCode := OTMCode.encode_injective.countable

instance : Countable OTMCode := OTMCode.countable

instance : Nonempty OTMCode := ⟨⟨1, 0, 0, 0, fun _ _ => .ask 0 0⟩⟩

/-- Relabelling the states of an action along a map. -/
def Act.map {Q Q' : Type} (f : Q → Q') : Act Q → Act Q'
  | .step q a m => .step (f q) a m
  | .push q b => .push (f q) b
  | .ask q₁ q₂ => .ask (f q₁) (f q₂)

/-- The code of `M`: its states numbered by `Fintype.equivFin`. -/
noncomputable def OTM.code (M : OTM) : OTMCode where
  k := Fintype.card M.Q
  start := Fintype.equivFin M.Q M.start
  accept := Fintype.equivFin M.Q M.accept
  reject := Fintype.equivFin M.Q M.reject
  δ := fun i a => (M.δ ((Fintype.equivFin M.Q).symm i) a).map (Fintype.equivFin M.Q)

/-- Transport of a configuration of `M` to its code. -/
noncomputable def OTM.codeConfig (M : OTM) (c : Config M) : Config M.code.toOTM :=
  ⟨Fintype.equivFin M.Q c.q, c.tape, c.head, c.buf⟩

/-- The transported configuration of a machine is halted if and only if the original configuration
is halted. -/
theorem OTM.code_halted_iff (M : OTM) (c : Config M) :
    Halted M.code.toOTM (M.codeConfig c) ↔ Halted M c := by
  simp [Halted, OTM.codeConfig, OTM.code, OTMCode.toOTM]

/-- The transition function of the code machine evaluates to the relabelled action of the original
machine. -/
theorem OTM.code_δ (M : OTM) (c : Config M) :
    M.code.toOTM.δ (M.codeConfig c).q ((M.codeConfig c).tape (M.codeConfig c).head) =
      (M.δ c.q (c.tape c.head)).map (Fintype.equivFin M.Q) := by
  simp [OTM.code, OTMCode.toOTM, OTM.codeConfig]

/-- Stepwise simulation: the code makes the relabelled step. -/
theorem OTM.step_code (M : OTM) (B : Set BitString) (c : Config M) :
    step M.code.toOTM B (M.codeConfig c) = M.codeConfig (step M B c) := by
  by_cases hc : Halted M c
  · rw [step_of_halted _ _ _ hc, step_of_halted _ _ _ ((M.code_halted_iff c).2 hc)]
  · have hc' : ¬ Halted M.code.toOTM (M.codeConfig c) := fun h => hc ((M.code_halted_iff c).1 h)
    unfold step
    rw [ite_eq_right hc, ite_eq_right hc', OTM.code_δ]
    cases M.δ c.q (c.tape c.head) with
    | step q' a m => rfl
    | push q' b => rfl
    | ask qyes qno =>
      by_cases hb : c.buf ∈ B <;> simp [hb, Act.map, OTM.codeConfig]

/-- The run of the code is the transported run. -/
theorem OTM.run_code (M : OTM) (B : Set BitString) (x : BitString) (t : ℕ) :
    run M.code.toOTM B x t = M.codeConfig (run M B x t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run, run, ih, OTM.step_code]

/-- The code asks the same strings. -/
theorem OTM.askedAt_code (M : OTM) (c : Config M) :
    askedAt M.code.toOTM (M.codeConfig c) = askedAt M c := by
  unfold askedAt
  by_cases hc : Halted M c
  · rw [ite_eq_left hc, ite_eq_left ((M.code_halted_iff c).2 hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((M.code_halted_iff c).1 h)), OTM.code_δ]
    cases M.δ c.q (c.tape c.head) <;> rfl

/-- Every machine is behaviourally equivalent to a coded machine (relabel the states by
`Fintype.equivFin`): halting, acceptance and head position agree at every time. -/
theorem exists_code (M : OTM) : ∃ c : OTMCode, ∀ (B : Set BitString) (x : BitString) (t : ℕ),
    (Halted M (run M B x t) ↔ Halted c.toOTM (run c.toOTM B x t)) ∧
    ((run M B x t).q = M.accept ↔ (run c.toOTM B x t).q = c.toOTM.accept) ∧
    (run M B x t).head = (run c.toOTM B x t).head ∧
    askedAt M (run M B x t) = askedAt c.toOTM (run c.toOTM B x t) := by
  refine ⟨M.code, fun B x t => ?_⟩
  rw [OTM.run_code]
  refine ⟨(M.code_halted_iff _).symm, ?_, rfl, (M.askedAt_code _).symm⟩
  simp [OTM.codeConfig, OTM.code, OTMCode.toOTM]

/-- The clock `n ^ e + e`. -/
def clock (e n : ℕ) : ℕ := n ^ e + e

/-- Acceptance within the clock. -/
def ClockedAccepts (c : OTMCode) (e : ℕ) (B : Set BitString) (x : BitString) : Prop :=
  ∃ t ≤ clock e x.length, (run c.toOTM B x t).q = c.toOTM.accept

/-- The clocked machine `(c, e)` with oracle `B` decides `A`. -/
def ClockedDecides (c : OTMCode) (e : ℕ) (B A : Set BitString) : Prop :=
  ∀ x, x ∈ A ↔ ClockedAccepts c e B x

/-- A polynomial with natural coefficients is bounded by the sum of its coefficients times the
top power, plus the sum of coefficients. -/
theorem eval_le_eval_one_mul (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree + p.eval 1 := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range (x := 1)]
  simp only [one_pow, mul_one]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (0 : ℕ) ^ i ≤ 1 := by rcases i with _ | i <;> simp
    have := Nat.mul_le_mul_left (p.coeff i) h0
    rw [mul_one] at this
    exact this.trans (Nat.le_add_left _ _)
  · have : n ^ i ≤ n ^ p.natDegree := Nat.pow_le_pow_right hn hi'
    nlinarith

/-- Every polynomial is dominated by some clock, at every length. -/
theorem exists_clock_ge (p : Polynomial ℕ) : ∃ e, ∀ n, p.eval n ≤ clock e n := by
  refine ⟨p.natDegree + 2 * p.eval 1 + 1, fun n => ?_⟩
  have h1 := eval_le_eval_one_mul p n
  unfold clock
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hd : n ^ p.natDegree ≤ 1 := pow_le_one₀ (Nat.zero_le _) (by omega)
    have : p.eval 1 * n ^ p.natDegree ≤ p.eval 1 := by
      calc p.eval 1 * n ^ p.natDegree ≤ p.eval 1 * 1 := Nat.mul_le_mul_left _ hd
        _ = p.eval 1 := mul_one _
    omega
  · have hd : 1 ≤ n ^ p.natDegree := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 * p.eval 1 + 1 < 2 ^ (2 * p.eval 1 + 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ (2 * p.eval 1 + 1) ≤ n ^ (2 * p.eval 1 + 1) := Nat.pow_le_pow_left hn _
    have h4 : n ^ (p.natDegree + 2 * p.eval 1 + 1) = n ^ p.natDegree * n ^ (2 * p.eval 1 + 1) := by
      rw [← pow_add]; ring_nf
    rw [h4]
    nlinarith

/-- Any set in `P^B` is decided by a clocked coded machine with oracle `B`. -/
theorem exists_clocked_of_polyTime (B A : Set BitString) (h : A ∈ PolyTimeOracle B) :
    ∃ (c : OTMCode) (e : ℕ), ClockedDecides c e B A := by
  obtain ⟨M, p, hp, hA⟩ := h
  obtain ⟨c, hc⟩ := exists_code M
  obtain ⟨e, he⟩ := exists_clock_ge p
  refine ⟨c, e, fun x => ?_⟩
  obtain ⟨t, ht, hh⟩ := hp x
  rw [hA x]
  constructor
  · intro hacc
    have h1 := (accepts_iff_of_halted M B x t hh).1 hacc
    exact ⟨t, ht.trans (he _), (hc B x t).2.1.1 h1⟩
  · rintro ⟨s, -, h'⟩
    exact ⟨s, (hc B x s).2.1.2 h'⟩

/-- An enumeration of all clocked machines. -/
theorem exists_enum : ∃ γ : ℕ → OTMCode × ℕ, Function.Surjective γ :=
  exists_surjective_nat _

/-- The strings that `M` can query on input `x` within `T` steps, under some oracle. -/
def queryAll (M : OTM) (x : BitString) (T : ℕ) : Set BitString :=
  {z | ∃ B : Set BitString, z ∈ queries M B x T}

/-- Only finitely many strings can be queried within `T` steps: the computation tree has at
most `2 ^ T` branches, each with at most `T` queries. -/
theorem queryAll_finite (M : OTM) (x : BitString) (T : ℕ) : (queryAll M x T).Finite := by
  refine (List.finite_length_le Bool T).subset fun z hz => ?_
  obtain ⟨B, hB⟩ := hz
  obtain ⟨s, hs, hz⟩ := (mem_queries M B x T z).1 hB
  exact (length_le_of_askedAt M B x s z hz).trans hs.le

/-- Queried strings are short. -/
theorem length_le_of_mem_queryAll (M : OTM) (x : BitString) (T : ℕ) (z : BitString)
    (hz : z ∈ queryAll M x T) : z.length ≤ T := by
  obtain ⟨B, hB⟩ := hz
  obtain ⟨s, hs, hz⟩ := (mem_queries M B x T z).1 hB
  exact (length_le_of_askedAt M B x s z hz).trans hs.le

/-- The (finite) set of possible queries. -/
noncomputable def querySet (M : OTM) (x : BitString) (T : ℕ) : Finset BitString :=
  (queryAll_finite M x T).toFinset

/-- The clocked verdict depends only on the oracle's restriction to the possible queries. -/
theorem clockedAccepts_iff_of_agree (c : OTMCode) (e : ℕ) (B B' : Set BitString) (x : BitString)
    (h : ∀ z ∈ querySet c.toOTM x (clock e x.length), (z ∈ B ↔ z ∈ B')) :
    ClockedAccepts c e B x ↔ ClockedAccepts c e B' x := by
  have hrun : ∀ t ≤ clock e x.length, run c.toOTM B x t = run c.toOTM B' x t := by
    intro t ht
    apply run_eq_of_agree
    intro z hz
    apply h
    rw [querySet, Set.Finite.mem_toFinset]
    exact ⟨B, queries_mono _ _ _ ht hz⟩
  unfold ClockedAccepts
  constructor
  · rintro ⟨t, ht, h'⟩
    exact ⟨t, ht, by rw [← hrun t ht]; exact h'⟩
  · rintro ⟨t, ht, h'⟩
    exact ⟨t, ht, by rw [hrun t ht]; exact h'⟩

end Kolmogorov.RandomStrings
