



/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.DyadicEnumeration
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.MonotoneLimits
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Infra
import KolmogorovMathlib.MonotoneComplexity.SharedCoding
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.DecidableLengths

/-!
# SUV Theorem 96: a computable summable `f` that rejects every non-random sequence

> **Theorem 96.**  There exists a total computable function `f : ℕ → ℕ` such that
> `∑ₙ 2^(-f(n)) < ∞` and having the following property: if for some sequence `ω` and some `c`
> the inequality `C((ω)ₙ | n) ⩾ n − f(n) − c` holds for all `n`, then `ω` is ML-random with
> respect to the uniform measure.  — SUV p. 152

## The construction

The source (pp. 152-154) starts from a cover of the largest effectively null set of total
measure at most `2^(-3c)`, replaces every interval of the cover by *all its extensions of one
fixed larger length* so that the lengths occurring in the enumeration only increase, and reads
off the resulting length distribution.  This module carries that out.

The enumeration of the universal Martin-Löf test is first *disjointified* (`disjEnum`), so that
the masses of its intervals **sum** to the measure of their union (`tsum_measure_disjEnum`),
and then *totalised* by inserting a junk interval `0^(d+s+1)` at the stages where it produces
nothing (`coverStr`).  The `s`-th interval `x_s` of level `d` is then padded to a level
`L_d(s)` (`coverLen`) chosen by the recursion

* `L_d(0) = |x_0|`, `B_d(0) = 0`,
* `B_d(s+1) = B_d(s) + 2^(L_d(s) − |x_s|)`,
* `L_d(s+1) = max (L_d(s) + 1) (|x_{s+1}| + B_d(s+1))`,

i.e. the levels are made *strictly increasing* and large enough that the running total `B_d(s)`
of the number of padded strings produced so far fits into `L_d(s) − |x_s|` bits (`n < 2^n`).
Because the levels are strictly increasing, the level-`n` slice of the padded cover is either
empty or consists of *all* extensions of a single string `x_s` to length `n`, which makes the
induced length distribution computable — this is the source's "we may assume without loss of
generality that the length of the intervals in the enumeration of `F_c` can only increase".

The exponent of the theorem is
`f(n) = min_{c ≤ n} (|x^{(3c)}_s| − 2c)` over the levels `n = L_{3c}(s)` that occur
(and `n + c` when level `n` does not occur at level `3c`).  This is the source's
`2^(-f(n)) = ∑_c 2^(-f_c(n))` with the sum replaced by its largest term; the bound
`∑ₙ 2^(-f(n)) ≤ ∑_c ∑ₙ 2^(-f_c(n)) < ∞` is obtained either way.  The `2c` shift is the source's
"we decrease `f` by `2c`": the cover of measure `2^(-3c)` produces a function whose series is
bounded by `2^(-c)`, which leaves `c` bits of slack for the self-delimiting code of `c` inside
the program.

Because the padded block of a stage is indexed by a *number* rather than by the pair
`(stage, tail)`, the description works without knowing `n`, which is the source's passage from
Theorem 96 to Theorem 97 ("describe a string of `F_c` by its ordinal number in the entire set
`F_c`", p. 154); the two theorems are therefore obtained here from one and the same
decompressor.

## Main results

* `unaryParse` — the decoder of the self-delimiting program format `1^c 0 t`;
* `coverStr`, `coverLen`, `coverBase`, `coverIdx`, `coverFind` — the padded cover;
* `coverExponent` — the function `f` of Theorem 96, and `computable_coverExponent`.
-/

namespace Kolmogorov

open MeasureTheory Set

open scoped ENNReal

/-! ### The self-delimiting program format `1^c 0 t` -/

/-- Decoding of the program format `1^c 0 t`: the number of leading `true` bits, and the rest
of the string after the terminating `false`. -/
def unaryParse : BitString → ℕ × BitString := fun p =>
  List.recOn p (0, ([] : BitString))
    (fun b l ih => bif b then (ih.1 + 1, ih.2) else (0, l))

/-- Parsing the empty program gives count zero and empty rest. -/
@[simp] lemma unaryParse_nil : unaryParse [] = (0, []) := rfl

/-- A leading one increases the parsed count by one. -/
@[simp] lemma unaryParse_cons_true (l : BitString) :
    unaryParse (true :: l) = ((unaryParse l).1 + 1, (unaryParse l).2) := rfl

/-- A leading zero terminates the count and leaves the rest of the string. -/
@[simp] lemma unaryParse_cons_false (l : BitString) : unaryParse (false :: l) = (0, l) := rfl

/-- `1^c 0 t` decodes to `(c, t)`. -/
lemma unaryParse_code (c : ℕ) (t : BitString) :
    unaryParse (List.replicate c true ++ false :: t) = (c, t) := by
  induction c with
  | zero => simp
  | succ c ih => simp [List.replicate_succ, ih]

/-- The program `1^c 0 t` has length `c + 1 + t.length`:
`(List.replicate c true ++ false :: t).length = c + 1 + t.length`. -/
lemma length_unaryCode (c : ℕ) (t : BitString) :
    (List.replicate c true ++ false :: t).length = c + 1 + t.length := by
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Parsing the program format `1^c 0 t` is primitive recursive. -/
lemma primrec_unaryParse : Primrec unaryParse := by
  have hstep : Primrec₂ (fun (_ : BitString) (q : Bool × BitString × (ℕ × BitString)) =>
      bif q.1 then (q.2.2.1 + 1, q.2.2.2) else (0, q.2.1)) := by
    have hb : Primrec (fun p : BitString × (Bool × BitString × (ℕ × BitString)) => p.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hih : Primrec (fun p : BitString × (Bool × BitString × (ℕ × BitString)) => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hl : Primrec (fun p : BitString × (Bool × BitString × (ℕ × BitString))
        => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    exact (Primrec.cond hb
      (Primrec.pair (Primrec.succ.comp (Primrec.fst.comp hih)) (Primrec.snd.comp hih))
      (Primrec.pair (Primrec.const 0) hl)).to₂
  exact Primrec.list_rec Primrec.id (Primrec.const _) hstep

/-- Parsing the program format `1^c 0 t` is computable. -/
lemma computable_unaryParse : Computable unaryParse := primrec_unaryParse.to_comp

/-! ### The totalised, padded cover -/

/-- The junk interval inserted at the stages where the enumeration produces nothing.  Its
length exceeds `d`, and the junk masses of level `d` sum to `2^(-d)`. -/
def coverJunk (d s : ℕ) : BitString := List.replicate (d + s + 1) false

/-- The junk interval inserted at stage `s` of level `d` has length `d + s + 1`. -/
@[simp] lemma length_coverJunk (d s : ℕ) : (coverJunk d s).length = d + s + 1 := by
  simp [coverJunk]

/-- The totalised enumeration of the level-`d` intervals. -/
def coverStr (E : ℕ → ℕ → Option BitString) (d s : ℕ) : BitString :=
  (E d s).getD (coverJunk d s)

/-- One step of the padding recursion: from the level and running total at stage `t` to the
level and running total at stage `t + 1`. -/
def coverStep (E : ℕ → ℕ → Option BitString) (d t : ℕ) (lb : ℕ × ℕ) : ℕ × ℕ :=
  (max (lb.1 + 1) ((coverStr E d (t + 1)).length +
      (lb.2 + 2 ^ (lb.1 - (coverStr E d t).length))),
    lb.2 + 2 ^ (lb.1 - (coverStr E d t).length))

/-- The pair `(L_d(s), B_d(s))`: the level to which the `s`-th interval of level `d` is padded,
and the number of padded strings produced by the earlier stages. -/
def coverState (E : ℕ → ℕ → Option BitString) (d s : ℕ) : ℕ × ℕ :=
  Nat.rec ((coverStr E d 0).length, 0) (fun t ih => coverStep E d t ih) s

/-- The level to which the `s`-th interval of level `d` is padded. -/
def coverLen (E : ℕ → ℕ → Option BitString) (d s : ℕ) : ℕ := (coverState E d s).1

/-- The number of padded strings produced by the stages before `s`. -/
def coverBase (E : ℕ → ℕ → Option BitString) (d s : ℕ) : ℕ := (coverState E d s).2

/-- The padding recursion starts at the length of the first interval. -/
@[simp] lemma coverLen_zero (E : ℕ → ℕ → Option BitString) (d : ℕ) :
    coverLen E d 0 = (coverStr E d 0).length := rfl

/-- No padded strings have been produced before the first stage. -/
@[simp] lemma coverBase_zero (E : ℕ → ℕ → Option BitString) (d : ℕ) : coverBase E d 0 = 0 := rfl

/-- The running total grows by the number of extensions produced at the current stage. -/
lemma coverBase_succ (E : ℕ → ℕ → Option BitString) (d s : ℕ) :
    coverBase E d (s + 1) =
      coverBase E d s + 2 ^ (coverLen E d s - (coverStr E d s).length) := rfl

/-- The next padding level is large enough both to increase strictly and to make room for the
running total. -/
lemma coverLen_succ (E : ℕ → ℕ → Option BitString) (d s : ℕ) :
    coverLen E d (s + 1) =
      max (coverLen E d s + 1)
        ((coverStr E d (s + 1)).length + coverBase E d (s + 1)) := rfl

/-! ### Elementary properties of the padding -/

variable {E : ℕ → ℕ → Option BitString}

/-- An interval is never longer than the level it is padded to. -/
lemma length_coverStr_le_coverLen (d s : ℕ) : (coverStr E d s).length ≤ coverLen E d s := by
  cases s with
  | zero => simp
  | succ s => rw [coverLen_succ]; exact le_trans (Nat.le_add_right _ _) (le_max_right _ _)

/-- The padding levels increase strictly from stage to stage. -/
lemma coverLen_lt_succ (d s : ℕ) : coverLen E d s < coverLen E d (s + 1) := by
  rw [coverLen_succ]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

/-- The padding levels are strictly monotone in the stage. -/
lemma coverLen_strictMono (d : ℕ) : StrictMono (coverLen E d) :=
  strictMono_nat_of_lt_succ (fun s => coverLen_lt_succ d s)

/-- Distinct stages get distinct padding levels. -/
lemma coverLen_injective (d : ℕ) : Function.Injective (coverLen E d) :=
  (coverLen_strictMono (E := E) d).injective

/-- The padding level of stage `s` is at least `s`. -/
lemma le_coverLen (d s : ℕ) : s ≤ coverLen E d s :=
  (coverLen_strictMono (E := E) d).le_apply

/-- Every stage produces at least one padded string. -/
lemma coverBase_lt_succ (d s : ℕ) : coverBase E d s < coverBase E d (s + 1) := by
  rw [coverBase_succ]
  exact Nat.lt_add_of_pos_right (pow_pos (by norm_num) _)

/-- The running total is strictly monotone in the stage. -/
lemma coverBase_strictMono (d : ℕ) : StrictMono (coverBase E d) :=
  strictMono_nat_of_lt_succ (fun s => coverBase_lt_succ d s)

/-- The running total at stage `s` is at least `s`. -/
lemma le_coverBase (d s : ℕ) : s ≤ coverBase E d s :=
  (coverBase_strictMono (E := E) d).le_apply

/-- The running total of padded strings fits into the number of padding bits. -/
lemma coverBase_lt_two_pow (d s : ℕ) :
    coverBase E d s < 2 ^ (coverLen E d s - (coverStr E d s).length) := by
  cases s with
  | zero => simp
  | succ s =>
      have hsize : (coverStr E d (s + 1)).length + coverBase E d (s + 1)
          ≤ coverLen E d (s + 1) := by
        rw [coverLen_succ]; exact le_max_right _ _
      have hle : coverBase E d (s + 1)
          ≤ coverLen E d (s + 1) - (coverStr E d (s + 1)).length := by omega
      exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hle)

/-! ### Locating a level and locating an index -/

/-- Downward scan for the stage whose padded level is `n`. -/
def coverIdxAux (E : ℕ → ℕ → Option BitString) (d n : ℕ) : ℕ → Option ℕ :=
  fun k => Nat.rec none (fun t ih => bif coverLen E d t == n then some t else ih) k

/-- The stage whose padded level is `n`, if there is one. -/
def coverIdx (E : ℕ → ℕ → Option BitString) (d n : ℕ) : Option ℕ := coverIdxAux E d n (n + 1)

/-- The downward scan for a stage of given padding level starts empty. -/
@[simp] lemma coverIdxAux_zero (d n : ℕ) : coverIdxAux E d n 0 = none := rfl

/-- One step of the downward scan tests the current stage and otherwise continues. -/
lemma coverIdxAux_succ (d n k : ℕ) :
    coverIdxAux E d n (k + 1) =
      bif coverLen E d k == n then some k else coverIdxAux E d n k := rfl

/-- The scan stops at a stage whose padding level is the target. -/
lemma coverIdxAux_succ_pos (d n k : ℕ) (hk : coverLen E d k = n) :
    coverIdxAux E d n (k + 1) = some k := by
  rw [coverIdxAux_succ, hk]
  simp

/-- The scan skips a stage whose padding level is not the target. -/
lemma coverIdxAux_succ_neg (d n k : ℕ) (hk : ¬ coverLen E d k = n) :
    coverIdxAux E d n (k + 1) = coverIdxAux E d n k := by
  rw [coverIdxAux_succ, beq_eq_false_iff_ne.mpr hk]
  rfl

/-- A stage returned by the scan does have the target padding level. -/
lemma coverIdxAux_eq_some (d n : ℕ) : ∀ (k s : ℕ), coverIdxAux E d n k = some s →
    coverLen E d s = n := by
  intro k
  induction k with
  | zero => intro s h; exact absurd h (by simp)
  | succ k ih =>
      intro s h
      by_cases hk : coverLen E d k = n
      · rw [coverIdxAux_succ_pos d n k hk, Option.some_inj] at h
        rw [← h]
        exact hk
      · exact ih s (by rwa [coverIdxAux_succ_neg d n k hk] at h)

/-- The scan succeeds whenever a stage below its bound has the target padding level. -/
lemma coverIdxAux_isSome (d n : ℕ) : ∀ (k s : ℕ), s < k → coverLen E d s = n →
    (coverIdxAux E d n k).isSome := by
  intro k
  induction k with
  | zero => intro s hs; exact absurd hs (Nat.not_lt_zero s)
  | succ k ih =>
      intro s hs hval
      by_cases hk : coverLen E d k = n
      · rw [coverIdxAux_succ_pos d n k hk]
        rfl
      · rw [coverIdxAux_succ_neg d n k hk]
        have hsk : s < k := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
          · exact h
          · exact absurd (h ▸ hval) hk
        exact ih s hsk hval

/-- The stage found for a level does have that padding level. -/
lemma coverIdx_eq_some (d n s : ℕ) (h : coverIdx E d n = some s) : coverLen E d s = n :=
  coverIdxAux_eq_some d n (n + 1) s h

/-- Every stage is found from its own padding level. -/
lemma coverIdx_of_coverLen (d s : ℕ) : coverIdx E d (coverLen E d s) = some s := by
  have hlt : s < coverLen E d s + 1 := Nat.lt_succ_of_le (le_coverLen d s)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
    (coverIdxAux_isSome (E := E) d (coverLen E d s) (coverLen E d s + 1) s hlt rfl)
  have hval : coverLen E d t = coverLen E d s :=
    coverIdxAux_eq_some d (coverLen E d s) (coverLen E d s + 1) t ht
  rw [coverIdx, ht, coverLen_injective (E := E) d hval]

/-- Downward scan for the stage whose block of padded strings contains the index `m`. -/
def coverFindAux (E : ℕ → ℕ → Option BitString) (d m : ℕ) : ℕ → ℕ :=
  fun k => Nat.rec 0 (fun t ih => bif decide (m < coverBase E d (t + 1)) then ih else t + 1) k

/-- The stage whose block of padded strings contains the index `m`. -/
def coverFind (E : ℕ → ℕ → Option BitString) (d m : ℕ) : ℕ := coverFindAux E d m m

/-- The block search runs the downward scan from its own argument. -/
lemma coverFind_def (d m : ℕ) : coverFind E d m = coverFindAux E d m m := rfl

/-- The block scan starts at stage zero. -/
@[simp] lemma coverFindAux_zero (d m : ℕ) : coverFindAux E d m 0 = 0 := rfl

/-- One step of the block scan keeps the stage whose block starts no later than the index. -/
lemma coverFindAux_succ (d m k : ℕ) :
    coverFindAux E d m (k + 1) =
      bif decide (m < coverBase E d (k + 1)) then coverFindAux E d m k else k + 1 := rfl

/-- The block scan stops at a stage whose block starts at or before the index. -/
lemma coverFindAux_succ_pos (d m k : ℕ) (hk : coverBase E d (k + 1) ≤ m) :
    coverFindAux E d m (k + 1) = k + 1 := by
  rw [coverFindAux_succ, decide_eq_false (by omega : ¬ m < coverBase E d (k + 1))]
  rfl

/-- The block scan continues past a stage whose block starts after the index. -/
lemma coverFindAux_succ_neg (d m k : ℕ) (hk : ¬ coverBase E d (k + 1) ≤ m) :
    coverFindAux E d m (k + 1) = coverFindAux E d m k := by
  rw [coverFindAux_succ, decide_eq_true (by omega : m < coverBase E d (k + 1))]
  rfl

/-- The stage found by the block scan starts no later than the index, and either is the scan's
bound or is followed by a stage starting after the index. -/
lemma coverFindAux_spec (d m : ℕ) : ∀ k : ℕ,
    coverBase E d (coverFindAux E d m k) ≤ m ∧
      (coverFindAux E d m k = k ∨ m < coverBase E d (coverFindAux E d m k + 1)) := by
  intro k
  induction k with
  | zero => exact ⟨by simp, Or.inl rfl⟩
  | succ k ih =>
      by_cases hk : coverBase E d (k + 1) ≤ m
      · have heq := coverFindAux_succ_pos (E := E) d m k hk
        exact ⟨by rw [heq]; exact hk, Or.inl heq⟩
      · have heq := coverFindAux_succ_neg (E := E) d m k hk
        refine ⟨by rw [heq]; exact ih.1, Or.inr ?_⟩
        rw [heq]
        rcases ih.2 with h | h
        · rw [h]; omega
        · exact h

/-- The block containing an index starts no later than that index. -/
lemma coverBase_coverFind_le (d m : ℕ) : coverBase E d (coverFind E d m) ≤ m :=
  (coverFindAux_spec (E := E) d m m).1

/-- The block after the one containing an index starts strictly later. -/
lemma lt_coverBase_coverFind_succ (d m : ℕ) : m < coverBase E d (coverFind E d m + 1) := by
  rcases (coverFindAux_spec (E := E) d m m).2 with h | h
  · have hle : coverBase E d (coverFind E d m) ≤ m := coverBase_coverFind_le d m
    have hge : m ≤ coverBase E d m := le_coverBase d m
    have hstep := coverBase_lt_succ (E := E) d m
    have hfm : coverFind E d m = m := h
    rw [hfm] at hle ⊢
    omega
  · exact h

/-! ### The exponent `f` of Theorem 96 -/

/-- The candidate exponent contributed at level `n` by the cover of measure `2^(-3c)`. -/
def coverCand (E : ℕ → ℕ → Option BitString) (n c : ℕ) : ℕ :=
  ((coverIdx E (3 * c) n).map (fun s => (coverStr E (3 * c) s).length - 2 * c)).getD (n + c)

/-- The running minimum of the candidate exponents. -/
def coverMin (E : ℕ → ℕ → Option BitString) (n : ℕ) : ℕ → ℕ :=
  fun k => Nat.rec (coverCand E n 0) (fun t ih => min (coverCand E n (t + 1)) ih) k

/-- The function `f` of SUV Theorem 96 (p. 152): the least candidate exponent `coverCand E n c` over
the levels `c ≤ n`. -/
def coverExponent (E : ℕ → ℕ → Option BitString) (n : ℕ) : ℕ := coverMin E n n

/-- The running minimum of the candidate exponents is at most each candidate it has passed. -/
lemma coverMin_le (n : ℕ) : ∀ (k c : ℕ), c ≤ k → coverMin E n k ≤ coverCand E n c := by
  intro k
  induction k with
  | zero => intro c hc; rw [Nat.le_zero.mp hc]; exact le_refl _
  | succ k ih =>
      intro c hc
      have hstep : coverMin E n (k + 1) = min (coverCand E n (k + 1)) (coverMin E n k) := rfl
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hc) with h | h
      · rw [hstep]
        exact le_trans (min_le_right _ _) (ih c (Nat.lt_succ_iff.mp h))
      · rw [hstep, h]
        exact min_le_left _ _

/-- The exponent `f n` is at most every candidate contributed by a level `c ≤ n`. -/
lemma coverExponent_le (n c : ℕ) (hc : c ≤ n) : coverExponent E n ≤ coverCand E n c :=
  coverMin_le n n c hc

/-- The running minimum is attained by one of the candidates it ranges over. -/
lemma exists_coverMin_eq (n : ℕ) : ∀ k : ℕ, ∃ c ≤ k, coverMin E n k = coverCand E n c := by
  intro k
  induction k with
  | zero => exact ⟨0, le_refl _, rfl⟩
  | succ k ih =>
      obtain ⟨c, hc, hval⟩ := ih
      have hstep : coverMin E n (k + 1) = min (coverCand E n (k + 1)) (coverMin E n k) := rfl
      rcases le_total (coverCand E n (k + 1)) (coverMin E n k) with h | h
      · exact ⟨k + 1, le_refl _, by rw [hstep, min_eq_left h]⟩
      · exact ⟨c, le_trans hc (Nat.le_succ k), by rw [hstep, min_eq_right h, hval]⟩

/-- The exponent `f n` is attained by one of the candidates. -/
lemma exists_coverExponent_eq (n : ℕ) : ∃ c, coverExponent E n = coverCand E n c := by
  obtain ⟨c, -, hval⟩ := exists_coverMin_eq (E := E) n n
  exact ⟨c, hval⟩

/-! ### Computability of the construction -/

/-- The step of the downward search, with the ambient type abstract.  Elaborating the `bif`
against a concrete ambient that mentions the `Nat.rec`-defined `coverBase` makes the unifier
unfold that recursion; keeping the statement free of it avoids the blow-up. -/
lemma computable_searchStep {α : Type} [Primcodable α] {B M I J : α → ℕ} (hB : Computable B)
    (hM : Computable M) (hI : Computable I) (hJ : Computable J) :
    Computable fun a : α => bif decide (M a < B a) then J a else I a + 1 :=
  Computable.cond (primrec_decide_nat_lt.to_comp.comp (Computable.pair hM hB)) hJ
    (Primrec.nat_add.to_comp.comp hI (Computable.const 1))

section Computability

variable (hE : Computable₂ E)

include hE

/-- The totalised enumeration is computable in the level and the stage. -/
lemma computable_coverStr : Computable₂ (coverStr E) := by
  have hlen : Computable fun p : ℕ × ℕ => p.1 + p.2 + 1 :=
    Primrec.to_comp (Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd))
  have hjunk : Computable fun p : ℕ × ℕ => coverJunk p.1 p.2 :=
    (Primrec.list_replicate.to_comp).comp hlen (Computable.const false)
  exact (Primrec.option_getD.to_comp).comp (hE.comp Computable.fst Computable.snd) hjunk

/-- The padding level together with the running total is computable in the level and the stage. -/
lemma computable_coverState : Computable₂ (coverState E) := by
  have hstr : Computable₂ (coverStr E) := computable_coverStr hE
  have hg : Computable fun p : ℕ × ℕ => (((coverStr E p.1 0).length : ℕ), (0 : ℕ)) :=
    Computable.pair
      (Computable.list_length.comp (hstr.comp Computable.fst (Computable.const 0)))
      (Computable.const 0)
  have hd : Computable fun q : (ℕ × ℕ) × ℕ × ℕ × ℕ => q.1.1 :=
    Computable.fst.comp Computable.fst
  have ht : Computable fun q : (ℕ × ℕ) × ℕ × ℕ × ℕ => q.2.1 :=
    Computable.fst.comp Computable.snd
  have ht1 : Computable fun q : (ℕ × ℕ) × ℕ × ℕ × ℕ => q.2.1 + 1 :=
    Primrec.nat_add.to_comp.comp ht (Computable.const 1)
  have hl : Computable fun q : (ℕ × ℕ) × ℕ × ℕ × ℕ => q.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hb : Computable fun q : (ℕ × ℕ) × ℕ × ℕ × ℕ => q.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ha : Computable fun q : (ℕ × ℕ) × ℕ × ℕ × ℕ => (coverStr E q.1.1 q.2.1).length :=
    Computable.list_length.comp (hstr.comp hd ht)
  have ha' : Computable fun q : (ℕ × ℕ) × ℕ × ℕ × ℕ =>
      (coverStr E q.1.1 (q.2.1 + 1)).length :=
    Computable.list_length.comp (hstr.comp hd ht1)
  have hbb : Computable fun q : (ℕ × ℕ) × ℕ × ℕ × ℕ =>
      q.2.2.2 + 2 ^ (q.2.2.1 - (coverStr E q.1.1 q.2.1).length) :=
    Primrec.nat_add.to_comp.comp hb
      (primrec_two_pow_aux.to_comp.comp (Primrec.nat_sub.to_comp.comp hl ha))
  have hres : Computable₂ fun (p : ℕ × ℕ) (q : ℕ × ℕ × ℕ) => coverStep E p.1 q.1 q.2 :=
    Computable.pair
      (Primrec.nat_max.to_comp.comp
        (Primrec.nat_add.to_comp.comp hl (Computable.const 1))
        (Primrec.nat_add.to_comp.comp ha' hbb))
      hbb
  exact Computable.nat_rec Computable.snd hg hres

/-- The padding level is computable. -/
lemma computable_coverLen : Computable₂ (coverLen E) :=
  Computable.fst.comp (computable_coverState hE)

/-- The running total is computable. -/
lemma computable_coverBase : Computable₂ (coverBase E) :=
  Computable.snd.comp (computable_coverState hE)

/-- The stage of a given padding level is computable. -/
lemma computable_coverIdx : Computable₂ (coverIdx E) := by
  have hlen : Computable fun q : (ℕ × ℕ) × ℕ × Option ℕ => coverLen E q.1.1 q.2.1 :=
    (computable_coverLen hE).comp (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd)
  have hn : Computable fun q : (ℕ × ℕ) × ℕ × Option ℕ => q.1.2 :=
    Computable.snd.comp Computable.fst
  have hcond : Computable fun q : (ℕ × ℕ) × ℕ × Option ℕ =>
      (coverLen E q.1.1 q.2.1 == q.1.2) := Primrec.beq.to_comp.comp hlen hn
  have hstep : Computable₂ fun (p : ℕ × ℕ) (q : ℕ × Option ℕ) =>
      bif coverLen E p.1 q.1 == p.2 then some q.1 else q.2 :=
    Computable.cond hcond (Computable.option_some.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  have hidx : Computable fun p : ℕ × ℕ => p.2 + 1 :=
    Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1)
  exact Computable.nat_rec hidx (Computable.const none) hstep

/-- The stage whose block contains a given index is computable. -/
lemma computable_coverFind : Computable₂ (coverFind E) := by
  have hbase : Computable fun q : (ℕ × ℕ) × ℕ × ℕ => coverBase E q.1.1 (q.2.1 + 1) :=
    (computable_coverBase hE).comp (Computable.fst.comp Computable.fst)
      (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 1))
  have hm : Computable fun q : (ℕ × ℕ) × ℕ × ℕ => q.1.2 := Computable.snd.comp Computable.fst
  have hstep : Computable₂ fun (p : ℕ × ℕ) (q : ℕ × ℕ) =>
      bif decide (p.2 < coverBase E p.1 (q.1 + 1)) then q.2 else q.1 + 1 :=
    computable_searchStep hbase hm (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)
  exact Computable.nat_rec Computable.snd (Computable.const 0) hstep

/-- The candidate exponents are computable. -/
lemma computable_coverCand : Computable₂ (coverCand E) := by
  have hd : Computable fun p : ℕ × ℕ => 3 * p.2 :=
    Primrec.nat_mul.to_comp.comp (Computable.const 3) Computable.snd
  have hidx : Computable fun p : ℕ × ℕ => coverIdx E (3 * p.2) p.1 :=
    (computable_coverIdx hE).comp hd Computable.fst
  have hval : Computable₂ fun (p : ℕ × ℕ) (s : ℕ) => (coverStr E (3 * p.2) s).length - 2 * p.2 :=
    Primrec.nat_sub.to_comp.comp
      (Computable.list_length.comp
        ((computable_coverStr hE).comp (hd.comp Computable.fst) Computable.snd))
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.snd.comp Computable.fst))
  have hdef : Computable fun p : ℕ × ℕ => p.1 + p.2 :=
    Primrec.nat_add.to_comp.comp Computable.fst Computable.snd
  exact (Primrec.option_getD.to_comp).comp (Computable.option_map hidx hval) hdef

/-- The running minimum of the candidate exponents is computable. -/
lemma computable_coverMin : Computable₂ (coverMin E) := by
  have hcc : Computable₂ (coverCand E) := computable_coverCand hE
  have hn : Computable fun q : (ℕ × ℕ) × ℕ × ℕ => q.1.1 := Computable.fst.comp Computable.fst
  have ht1 : Computable fun q : (ℕ × ℕ) × ℕ × ℕ => q.2.1 + 1 :=
    Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 1)
  have hcand : Computable fun q : (ℕ × ℕ) × ℕ × ℕ => coverCand E q.1.1 (q.2.1 + 1) :=
    hcc.comp hn ht1
  have hstep : Computable₂ fun (p : ℕ × ℕ) (q : ℕ × ℕ) =>
      min (coverCand E p.1 (q.1 + 1)) q.2 :=
    Primrec.nat_min.to_comp.comp hcand (Computable.snd.comp Computable.snd)
  have hzero : Computable fun p : ℕ × ℕ => coverCand E p.1 0 :=
    hcc.comp Computable.fst (Computable.const 0)
  exact Computable.nat_rec Computable.snd hzero hstep

/-- The exponent `f` of Theorem 96 is total computable. -/
lemma computable_coverExponent : Computable (coverExponent E) :=
  ((computable_coverMin hE).comp Computable.id Computable.id).of_eq fun _ => rfl

end Computability

/-! ### Arithmetic of the dyadic weights -/

/-- The truncated subtraction in the exponent only helps. -/
lemma inv_two_pow_sub_le (a k : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ (a - k) ≤ (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ a := by
  have hcancel : (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ k = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  rcases le_total k a with hk | hk
  · have hsplit : (2 : ℝ≥0∞)⁻¹ ^ a = (2 : ℝ≥0∞)⁻¹ ^ (a - k) * (2 : ℝ≥0∞)⁻¹ ^ k := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, ← mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ k), mul_assoc, hcancel, mul_one]
  · have h0 : a - k = 0 := by omega
    have hmono : (2 : ℝ≥0∞) ^ a ≤ (2 : ℝ≥0∞) ^ k := pow_le_pow_right₀ (by norm_num) hk
    have hone : (2 : ℝ≥0∞) ^ a * (2 : ℝ≥0∞)⁻¹ ^ a = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    rw [h0, pow_zero, ← hone]
    gcongr

/-- `∑ₙ 2^(-(n+c)) = 2·2^(-c)`. -/
lemma tsum_inv_two_pow_add_right (c : ℕ) :
    (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + c)) = 2 * (2 : ℝ≥0∞)⁻¹ ^ c := by
  have hterm : ∀ n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + c) = 2 * (2 : ℝ≥0∞)⁻¹ ^ (c + n + 1) := by
    intro n
    rw [show c + n + 1 = (n + c) + 1 by omega, pow_succ, ← mul_assoc,
      mul_comm (2 : ℝ≥0∞) ((2 : ℝ≥0∞)⁻¹ ^ (n + c)), mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, tsum_inv_two_pow_shift c]

/-- `∑ₙ 2^(-n) = 2`. -/
lemma tsum_inv_two_pow_self : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n) = 2 := by
  have h := tsum_inv_two_pow_add_right 0
  simp only [Nat.add_zero, pow_zero, mul_one] at h
  exact h

end Kolmogorov
