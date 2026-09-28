import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Primitive recursiveness of the binary logarithm

`Nat.log 2` is computed by repeated halving.  We implement that iteration as a
primitive recursive loop and identify its result with `Nat.log2`, hence with
`Nat.log 2`.
-/

namespace Kolmogorov

namespace NatLog

/-- One halving step of the binary-logarithm loop. -/
def log2Step (p : Nat × Nat) : Nat × Nat :=
  if p.1 < 2 then p else (p.1 / 2, p.2 + 1)

/-- `k`-fold iteration of `log2Step`. -/
def log2Iter (k : Nat) (p : Nat × Nat) : Nat × Nat :=
  Nat.rec p (fun _ IH => log2Step IH) k

/-- Iterating the halving step zero times leaves the state unchanged. -/
lemma log2Iter_zero (p : Nat × Nat) : log2Iter 0 p = p := rfl

/-- One more iteration of the halving step applies the step to the previous state. -/
lemma log2Iter_succ (k : Nat) (p : Nat × Nat) :
    log2Iter (k + 1) p = log2Step (log2Iter k p) := rfl

/-- One more iteration of the halving step may equivalently be taken at the start. -/
lemma log2Iter_succ' (k : Nat) (p : Nat × Nat) :
    log2Iter (k + 1) p = log2Iter k (log2Step p) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [log2Iter_succ, ih, log2Iter_succ]

/-- A natural number with binary logarithm zero is smaller than two. -/
lemma lt_two_of_log2_eq_zero (n : Nat) (h : Nat.log2 n = 0) : n < 2 := by
  by_contra hc
  rw [Nat.log2_eq_log_two, Nat.log_of_one_lt_of_le one_lt_two (Nat.not_lt.mp hc)] at h
  omega

/-- For `n ≥ 2` the binary logarithm satisfies the halving recurrence
`log₂ n = log₂ (n / 2) + 1`. -/
lemma log2_eq_succ (n : Nat) (h : 2 ≤ n) : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two, Nat.log_of_one_lt_of_le one_lt_two h]

/-- After at least `log₂ n` halving steps the state has been reduced below two and the counter
has been increased by exactly `log₂ n`. -/
lemma log2Iter_spec : ∀ (k n acc : Nat), Nat.log2 n ≤ k →
    (log2Iter k (n, acc)).1 < 2 ∧ (log2Iter k (n, acc)).2 = acc + Nat.log2 n := by
  intro k
  induction k with
  | zero =>
      intro n acc h
      have h0 : Nat.log2 n = 0 := Nat.le_zero.mp h
      exact ⟨lt_two_of_log2_eq_zero n h0, by simp [log2Iter, h0]⟩
  | succ k ih =>
      intro n acc h
      by_cases hn : n < 2
      · have h0 : Nat.log2 n = 0 := by
          rw [Nat.log2_eq_log_two, Nat.log_of_lt hn]
        have hstep : log2Step (n, acc) = (n, acc) := by
          rw [log2Step]; exact if_pos hn
        rw [log2Iter_succ', hstep]
        exact ih n acc (by omega)
      · have h2 : 2 ≤ n := Nat.not_lt.mp hn
        have hs := log2_eq_succ n h2
        have hstep : log2Step (n, acc) = (n / 2, acc + 1) := by
          rw [log2Step]; exact if_neg hn
        rw [log2Iter_succ', hstep]
        have hIH := ih (n / 2) (acc + 1) (by omega)
        exact ⟨hIH.1, by rw [hIH.2]; omega⟩

/-- Running the halving loop `n` times on `(n, 0)` computes `log₂ n`. -/
lemma log2Iter_eq_log2 (n : Nat) : (log2Iter n (n, 0)).2 = Nat.log2 n := by
  rw [(log2Iter_spec n n 0 (Nat.log2_le_self n)).2, Nat.zero_add]

/-- The single halving step of the binary-logarithm loop is primitive recursive. -/
lemma log2Step_primrec : Primrec log2Step := by
  refine Primrec.ite (Primrec.nat_lt.comp Primrec.fst (Primrec.const 2)) Primrec.id ?_
  exact Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))
    (Primrec.succ.comp Primrec.snd)

/-- The binary logarithm `Nat.log2` is primitive recursive. -/
lemma nat_log2_primrec : Primrec Nat.log2 := by
  have hg : Primrec₂ (fun (_ : Nat) (q : Nat × (Nat × Nat)) => log2Step q.2) :=
    (log2Step_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂
  have hf : Primrec (fun a : Nat => ((a, 0) : Nat × Nat)) :=
    Primrec.pair Primrec.id (Primrec.const 0)
  have hiter : Primrec (fun n : Nat => log2Iter n (n, 0)) :=
    ((Primrec.nat_rec hf hg).comp Primrec.id Primrec.id).of_eq (fun _ => rfl)
  exact (Primrec.snd.comp hiter).of_eq log2Iter_eq_log2

end NatLog

/-- The base-two logarithm on `ℕ` is primitive recursive. -/
lemma primrec_natLogTwo : Primrec (fun n : ℕ => Nat.log 2 n) :=
  NatLog.nat_log2_primrec.of_eq (fun n => (Nat.log2_eq_log_two (n := n)))

/-- The base-two logarithm on `ℕ` is computable. -/
lemma computable_natLogTwo : Computable (fun n : ℕ => Nat.log 2 n) :=
  primrec_natLogTwo.to_comp

end Kolmogorov
