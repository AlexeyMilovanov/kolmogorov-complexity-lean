import KolmogorovMathlib.AlgorithmicRandomness.EffectiveLaws
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof

/-!
# Randomness is a tail property

`IsFiniteEdit` is reachability by finitely many elementary edits of a sequence — changing,
inserting or deleting a bit, packaged as `IsOneEdit` — and `HasCommonTail` says two sequences
agree after a finite shift on each side.

`isMartinLofRandom_uniform_of_isFiniteEdit` states that Martin-Löf randomness for the uniform
measure survives any finite edit.  It comes from
`isMartinLofRandom_uniform_of_hasCommonTail`, that randomness depends only on the tail, which
in turn rests on the two one-sided statements `isMartinLofRandom_uniform_drop` and
`isMartinLofRandom_uniform_prepend`, with `eq_prependCantor_cantorPrefix` splitting a sequence
into a prefix and a shift.
-/

namespace Kolmogorov
open MeasureTheory Measure

/-- Two sequences have a common tail when they agree after some finite shift on each side. -/
def HasCommonTail (x y : CantorSeq) : Prop := ∃ k l, ∀ n, x (n + k) = y (n + l)

/-- One elementary edit of a sequence: changing a bit, inserting a bit, or deleting a bit at a
given position. -/
inductive IsOneEdit : CantorSeq → CantorSeq → Prop
  | change (x : CantorSeq) (i : ℕ) (b : Bool) :
      IsOneEdit x (fun n => if n = i then b else x n)
  | insert (x : CantorSeq) (i : ℕ) (b : Bool) :
      IsOneEdit x (fun n => if n < i then x n else if n = i then b else x (n - 1))
  | delete (x : CantorSeq) (i : ℕ) :
      IsOneEdit x (fun n => if n < i then x n else x (n + 1))

/-- Reachability by finitely many elementary edits (change, insertion, deletion). -/
def IsFiniteEdit : CantorSeq → CantorSeq → Prop := Relation.ReflTransGen IsOneEdit

/-- Dropping a finite prefix of a Martin-Löf random sequence leaves it random for the uniform
measure. -/
lemma isMartinLofRandom_uniform_drop {x : CantorSeq} {k : ℕ}
    (hx : IsMartinLofRandom uniformMeasure x) :
    IsMartinLofRandom uniformMeasure (fun n => x (n + k)) := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    have h : (fun n => x (n + (k + 1))) = fun n => (fun m => x (m + k)) (n + 1) := by
      funext n
      congr 1
      omega
    rw [h]
    exact isMartinLofRandom_tail_of_isMartinLofRandom_uniform ih

/-- Prepending `b :: s` puts `b` at position zero and shifts the sequence `prependCantor s z`
one place to the right. -/
lemma prependCantor_cons_eq (b : Bool) (s : List Bool) (z : CantorSeq) :
    prependCantor (b :: s) z = fun n => if n = 0 then b else prependCantor s z (n - 1) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [prependCantor, Nat.succ_ne_zero, ite_false, List.length_cons, List.getElem_cons_succ]
    have h1 : n + 1 < s.length + 1 ↔ n < s.length := by omega
    have h2 : n + 1 - 1 = n := by omega
    have h3 : n + 1 - (s.length + 1) = n - s.length := by omega
    simp only [h1, h2, h3]

/-- Prepending a finite string to a Martin-Löf random sequence leaves it random for the uniform
measure. -/
lemma isMartinLofRandom_uniform_prepend {z : CantorSeq} {s : List Bool}
    (hz : IsMartinLofRandom uniformMeasure z) :
    IsMartinLofRandom uniformMeasure (prependCantor s z) := by
  induction s with
  | nil =>
    simp only [prependCantor_nil, hz]
  | cons b s ih =>
    rw [prependCantor_cons_eq]
    exact isMartinLofRandom_cons_of_isMartinLofRandom_uniform b ih

/-- Every sequence is its length-`l` prefix followed by its `l`-shift. -/
theorem eq_prependCantor_cantorPrefix (y : CantorSeq) (l : ℕ) :
    y = prependCantor (cantorPrefix y l) (fun n => y (n + l)) := by
  funext n
  simp only [prependCantor, cantorPrefix_length, cantorPrefix_getElem]
  rcases lt_or_ge n l with h | h
  · rw [dif_pos h]
  · rw [dif_neg (not_lt.mpr h)]
    congr 1
    omega

/-- Martin-Löf randomness for the uniform measure depends only on the tail of a sequence. -/
lemma isMartinLofRandom_uniform_of_hasCommonTail {x y : CantorSeq} (h : HasCommonTail x y)
    (hx : IsMartinLofRandom uniformMeasure x) : IsMartinLofRandom uniformMeasure y := by
  rcases h with ⟨k, l, h⟩
  have hx_drop := isMartinLofRandom_uniform_drop hx (k := k)
  have hy_drop : IsMartinLofRandom uniformMeasure (fun n => y (n + l)) := by
    have h_eq : (fun n => x (n + k)) = fun n => y (n + l) := funext h
    rwa [← h_eq]
  have hy_prep := isMartinLofRandom_uniform_prepend hy_drop (s := cantorPrefix y l)
  rw [← eq_prependCantor_cantorPrefix y l] at hy_prep
  exact hy_prep

/-- Every sequence has a common tail with itself. -/
lemma HasCommonTail.refl (x : CantorSeq) : HasCommonTail x x := by
  use 0, 0
  intro n
  rfl

/-- Having a common tail is a transitive relation. -/
lemma HasCommonTail.trans {x y z : CantorSeq} (h1 : HasCommonTail x y) (h2 : HasCommonTail y z) :
    HasCommonTail x z := by
  rcases h1 with ⟨k1, l1, h1⟩
  rcases h2 with ⟨k2, l2, h2⟩
  use k1 + k2, l1 + l2
  intro n
  have hx : x (n + (k1 + k2)) = x (n + k2 + k1) := by congr 1; omega
  have hy : y (n + k2 + l1) = y (n + l1 + k2) := by congr 1; omega
  have hz : z (n + (l1 + l2)) = z (n + l1 + l2) := by congr 1; omega
  rw [hx, h1 (n + k2), hy, h2 (n + l1)]
  congr 1
  omega

/-- One elementary edit does not change the tail of a sequence. -/
lemma IsOneEdit.hasCommonTail {x y : CantorSeq} (h : IsOneEdit x y) : HasCommonTail x y := by
  cases h
  case change i b =>
    use i + 1, i + 1
    intro n
    dsimp
    have h_neq : n + (i + 1) ≠ i := by omega
    simp [h_neq]
  case insert i b =>
    use i, i + 1
    intro n
    dsimp
    have h1 : ¬(n + (i + 1) < i) := by omega
    have h2 : n + (i + 1) ≠ i := by omega
    simp [h1, h2]
  case delete i =>
    use i + 1, i
    intro n
    dsimp
    have h1 : ¬(n + i < i) := by omega
    simp only [h1, ↓reduceIte]
    have h_eq : n + (i + 1) = n + i + 1 := by omega
    rw [h_eq]

/-- Martin-Löf randomness for the uniform measure is preserved by finitely many bit changes,
insertions and deletions. -/
theorem isMartinLofRandom_uniform_of_isFiniteEdit {x y : CantorSeq} (h : IsFiniteEdit x y)
    (hx : IsMartinLofRandom uniformMeasure x) :
    IsMartinLofRandom uniformMeasure y := by
  induction h with
  | refl => exact hx
  | tail _ h_step ih =>
    have h_tail := IsOneEdit.hasCommonTail h_step
    exact isMartinLofRandom_uniform_of_hasCommonTail h_tail ih
end Kolmogorov
