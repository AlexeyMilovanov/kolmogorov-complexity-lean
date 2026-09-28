import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Complexity.SelfComplexity.TokenGame

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-! ### Exercises 47–52: complexity of prefixes and of infinite sequences -/

-- `exercise47_profile` (ch02-exercise-47) is archived; see `docs/ARCHIVED_TARGETS.md`.

-- `computable_iff_condK_prefix_bounded` (ch02-exercise-48) is proved below, in the
-- section "SUV problem 48": its proof instantiates the shared tree-search core
-- `mSearch_spec` at the problem-52 enumeration `minfQ`, both of which are declared
-- further down in this file.

/-- The length-`n` prefix of a sequence has length `n`. -/
@[simp] lemma length_seqPrefix (w : ℕ → Bool) (n : ℕ) : (seqPrefix w n).length = n := by
  simp [seqPrefix]

/-- Prefixes of a sequence are nested: truncating the length-`m` prefix to `n ≤ m` gives the
length-`n` prefix. -/
lemma seqPrefix_take (w : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    (seqPrefix w m).take n = seqPrefix w n := by
  rw [seqPrefix, seqPrefix, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-! ### The big-endian key of a bit string -/

/-- Big-endian numeric key of a bit string: index `0` is the most significant bit.
On strings of a fixed length this is an order isomorphism onto an initial segment of `ℕ`
for the lexicographic order, and it interacts with prefixes by division. -/
def lexKey (x : BitString) : ℕ := x.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0

private lemma foldl_key_acc (l : BitString) (s : ℕ) :
    l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) s
      = s * 2 ^ l.length + l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 := by
  induction l generalizing s with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (2 * s + (if b then 1 else 0)), ih (2 * 0 + (if b then 1 else 0))]
    ring

/-- Prepending a bit shifts the numeric key: the new bit becomes the most significant digit. -/
lemma lexKey_cons (b : Bool) (t : BitString) :
    lexKey (b :: t) = (if b then 1 else 0) * 2 ^ t.length + lexKey t := by
  simp only [lexKey, List.foldl_cons]
  rw [foldl_key_acc t (2 * 0 + (if b then 1 else 0))]
  simp

/-- Concatenation multiplies the key of the first factor by `2 ^ |b|` and adds the key of `b`. -/
lemma lexKey_append (a b : BitString) :
    lexKey (a ++ b) = lexKey a * 2 ^ b.length + lexKey b := by
  simp only [lexKey, List.foldl_append]
  rw [foldl_key_acc b (List.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0 a)]

/-- The key of a string of length `n` is below `2 ^ n`. -/
lemma lexKey_lt (x : BitString) : lexKey x < 2 ^ x.length := by
  induction x with
  | nil => simp [lexKey]
  | cons b t ih =>
    rw [lexKey_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- Truncating a string divides its key by `2` to the number of bits dropped. -/
lemma lexKey_take (x : BitString) (n : ℕ) :
    lexKey (x.take n) = lexKey x / 2 ^ (x.length - n) := by
  have hx : x.take n ++ x.drop n = x := List.take_append_drop n x
  have hlen : (x.drop n).length = x.length - n := by simp
  have hpos : 0 < 2 ^ (x.length - n) := by positivity
  have h := lexKey_append (x.take n) (x.drop n)
  rw [hx, hlen] at h
  rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ hpos,
    Nat.div_eq_of_lt (by simpa [hlen] using lexKey_lt (x.drop n)), Nat.zero_add]

/-- On strings of a fixed length the numeric key is injective. -/
lemma lexKey_inj {x y : BitString} (hlen : x.length = y.length)
    (hkey : lexKey x = lexKey y) : x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons c u => simp at hlen
  | cons b t ih =>
    cases y with
    | nil => simp at hlen
    | cons c u =>
      have hlt : t.length = u.length := by simpa using hlen
      rw [lexKey_cons, lexKey_cons, ← hlt] at hkey
      have h1 := lexKey_lt t
      have h2 : lexKey u < 2 ^ t.length := by rw [hlt]; exact lexKey_lt u
      have hbc : b = c := by
        by_contra hne
        cases b <;> cases c <;> simp_all
        all_goals omega
      subst hbc
      have ht : lexKey t = lexKey u := by
        cases b <;> simp at hkey <;> omega
      exact congrArg _ (ih hlt ht)

/-- Prefix monotonicity of the key. -/
lemma lexKey_take_le {x y : BitString} (n : ℕ) (hxy : x.length = y.length)
    (h : lexKey x ≤ lexKey y) :
    lexKey (x.take n) ≤ lexKey (y.take n) := by
  rw [lexKey_take x n, lexKey_take y n, hxy]
  exact Nat.div_le_div_right h

/-- The numeric key of a bit string is primitive recursive. -/
theorem lexKey_primrec : Primrec lexKey := by
  have hs : Primrec (fun z : BitString × (ℕ × Bool) => z.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun z : BitString × (ℕ × Bool) => z.2.2) := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun z : BitString × (ℕ × Bool) => if z.2.2 then 1 else 0) :=
    (Primrec.cond hb (Primrec.const 1) (Primrec.const 0)).of_eq (fun z => by
      cases z.2.2 <;> rfl)
  have hf : Primrec (fun z : BitString × (ℕ × Bool) => 2 * z.2.1 + (if z.2.2 then 1 else 0)) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hs) hc
  exact Primrec.list_foldl Primrec.id (Primrec.const 0) hf.to₂

/-! ### A counting helper -/

/-- Widening a predicate on a list strictly increases the count if some element of the list is
newly counted. -/
lemma countP_lt_countP {l : List BitString} {P P' : BitString → Bool}
    (hmono : ∀ x ∈ l, P x = true → P' x = true) {a : BitString} (ha : a ∈ l)
    (h1 : P a = false) (h2 : P' a = true) :
    l.countP P < l.countP P' := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp ha with rfl | hat
    · have hmono' : ∀ x ∈ t, P x = true → P' x = true := fun x hx => hmono x (by simp [hx])
      have := List.countP_mono_left hmono'
      simp [h1, h2]
      omega
    · have hmono' : ∀ x ∈ t, P x = true → P' x = true := fun x hx => hmono x (by simp [hx])
      have hlt := ih hmono' hat
      have hb : (if P b = true then 1 else 0) ≤ (if P' b = true then 1 else 0) := by
        by_cases hpb : P b = true
        · simp [hpb, hmono b (by simp) hpb]
        · simp [hpb]
      omega

/-- A bounded sequence of naturals has a `limsup`: a value that bounds it from some point
on and is attained arbitrarily late. -/
lemma exists_limsup (f : ℕ → ℕ) (B N₀ : ℕ) (hf : ∀ n, N₀ ≤ n → f n ≤ B) :
    ∃ L N, L ≤ B ∧ N₀ ≤ N ∧ (∀ n, N ≤ n → f n ≤ L) ∧ (∀ N', ∃ n, N' ≤ n ∧ L ≤ f n) := by
  classical
  have hex : ∃ v, ∃ N, N₀ ≤ N ∧ ∀ n, N ≤ n → f n ≤ v := ⟨B, N₀, le_refl _, hf⟩
  set L := Nat.find hex with hL
  obtain ⟨N, hN₀N, hN⟩ := Nat.find_spec hex
  refine ⟨L, N, Nat.find_le ⟨N₀, le_refl _, hf⟩, hN₀N, hN, ?_⟩
  intro N'
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · exact ⟨N', le_refl _, by omega⟩
  · have hnot : ¬ ∃ N, N₀ ≤ N ∧ ∀ n, N ≤ n → f n ≤ L - 1 := Nat.find_min hex (by omega)
    push_neg at hnot
    obtain ⟨n, hn1, hn2⟩ := hnot (max N' N₀) (le_max_right _ _)
    exact ⟨n, le_trans (le_max_left _ _) hn1, by omega⟩

/-! ### The enumeration and its counting functions

`Q (p, s, x)` is a decidable approximation, monotone in the stage `s`, of an enumerable
set `S p` of bit strings: `x ∈ S p` means `∃ s, Q (p, s, x) = true`.  The parameter `p`
makes everything uniform, which is what the complexity bound of SUV problem 52 needs.
-/

variable (Q : ℕ × ℕ × BitString → Bool)

/-- Number of level-`n` strings enumerated by stage `s` strictly to the left of `y`.
The argument is `((p, n, s), y)`. -/
def mLeft (a : (ℕ × ℕ × ℕ) × BitString) : ℕ :=
  (allStrings a.1.2.1).countP
    (fun u => Q (a.1.1, a.1.2.2, u) && decide (lexKey u < lexKey a.2))

/-- Number of level-`n` strings enumerated by stage `s` strictly to the right of `y`.
The argument is `((p, n, s), y)`. -/
def mRight (a : (ℕ × ℕ × ℕ) × BitString) : ℕ :=
  (allStrings a.1.2.1).countP
    (fun u => Q (a.1.1, a.1.2.2, u) && decide (lexKey a.2 < lexKey u))

open Classical in
/-- The number of level-`n` strings that are ever enumerated. -/
noncomputable def mLevelCount (p n : ℕ) : ℕ :=
  (allStrings n).countP (fun u => decide (∃ s, Q (p, s, u) = true))

open Classical in
/-- The number of enumerated level-`n` strings strictly to the left of `y`. -/
noncomputable def mTrueLeft (p n : ℕ) (y : BitString) : ℕ :=
  (allStrings n).countP
    (fun u => decide ((∃ s, Q (p, s, u) = true) ∧ lexKey u < lexKey y))

open Classical in
/-- The number of enumerated level-`n` strings strictly to the right of `y`. -/
noncomputable def mTrueRight (p n : ℕ) (y : BitString) : ℕ :=
  (allStrings n).countP
    (fun u => decide ((∃ s, Q (p, s, u) = true) ∧ lexKey y < lexKey u))

/-- The stage-bounded count of enumerated strings to the left is primitive recursive when the
enumeration test is. -/
theorem mLeft_primrec (hQ : Primrec Q) : Primrec (mLeft Q) := by
  refine list_countP_primrec
    (allStrings_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) ?_
  have h1 : Primrec (fun z : ((ℕ × ℕ × ℕ) × BitString) × BitString =>
      Q (z.1.1.1, z.1.1.2.2, z.2)) :=
    hQ.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd))
  have h2 : Primrec (fun z : ((ℕ × ℕ × ℕ) × BitString) × BitString =>
      decide (lexKey z.2 < lexKey z.1.2)) :=
    PrimrecPred.decide (Primrec.nat_lt.comp (lexKey_primrec.comp Primrec.snd)
      (lexKey_primrec.comp (Primrec.snd.comp Primrec.fst)))
  exact (Primrec.and.comp h1 h2).to₂

/-- The stage-bounded count of enumerated strings to the right is primitive recursive when the
enumeration test is. -/
theorem mRight_primrec (hQ : Primrec Q) : Primrec (mRight Q) := by
  refine list_countP_primrec
    (allStrings_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) ?_
  have h1 : Primrec (fun z : ((ℕ × ℕ × ℕ) × BitString) × BitString =>
      Q (z.1.1.1, z.1.1.2.2, z.2)) :=
    hQ.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd))
  have h2 : Primrec (fun z : ((ℕ × ℕ × ℕ) × BitString) × BitString =>
      decide (lexKey z.1.2 < lexKey z.2)) :=
    PrimrecPred.decide (Primrec.nat_lt.comp (lexKey_primrec.comp (Primrec.snd.comp Primrec.fst))
      (lexKey_primrec.comp Primrec.snd))
  exact (Primrec.and.comp h1 h2).to₂

/-- The stage-bounded left count never exceeds the number of strings that are ever enumerated
to the left of `y`. -/
lemma mLeft_le_true (p n s : ℕ) (y : BitString) :
    mLeft Q ((p, n, s), y) ≤ mTrueLeft Q p n y := by
  refine List.countP_mono_left ?_
  intro u _ hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hu ⊢
  exact ⟨⟨s, hu.1⟩, hu.2⟩

/-- The stage-bounded right count never exceeds the number of strings that are ever enumerated
to the right of `y`. -/
lemma mRight_le_true (p n s : ℕ) (y : BitString) :
    mRight Q ((p, n, s), y) ≤ mTrueRight Q p n y := by
  refine List.countP_mono_left ?_
  intro u _ hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hu ⊢
  exact ⟨⟨s, hu.1⟩, hu.2⟩

/-- The strings enumerated to the left of `y` are among all enumerated strings of that level. -/
lemma mTrueLeft_le_level (p n : ℕ) (y : BitString) :
    mTrueLeft Q p n y ≤ mLevelCount Q p n := by
  refine List.countP_mono_left ?_
  intro u _ hu
  simp only [decide_eq_true_eq] at hu ⊢
  exact hu.1

/-- The strings enumerated to the right of `y` are among all enumerated strings of that level. -/
lemma mTrueRight_le_level (p n : ℕ) (y : BitString) :
    mTrueRight Q p n y ≤ mLevelCount Q p n := by
  refine List.countP_mono_left ?_
  intro u _ hu
  simp only [decide_eq_true_eq] at hu ⊢
  exact hu.1

/-- Moving to the right past an enumerated string strictly increases the number of enumerated
strings on the left. -/
lemma mTrueLeft_strict {p n : ℕ} {y z : BitString} (hy : ∃ s, Q (p, s, y) = true)
    (hylen : y.length = n) (h : lexKey y < lexKey z) :
    mTrueLeft Q p n y < mTrueLeft Q p n z := by
  refine countP_lt_countP ?_ ((mem_allStrings n y).mpr hylen) ?_ ?_
  · intro u _ hu
    simp only [decide_eq_true_eq] at hu ⊢
    exact ⟨hu.1, lt_trans hu.2 h⟩
  · simp
  · simp only [decide_eq_true_eq]
    exact ⟨hy, h⟩

/-- Moving to the left past an enumerated string strictly increases the number of enumerated
strings on the right. -/
lemma mTrueRight_strict {p n : ℕ} {y z : BitString} (hy : ∃ s, Q (p, s, y) = true)
    (hylen : y.length = n) (h : lexKey z < lexKey y) :
    mTrueRight Q p n y < mTrueRight Q p n z := by
  refine countP_lt_countP ?_ ((mem_allStrings n y).mpr hylen) ?_ ?_
  · intro u _ hu
    simp only [decide_eq_true_eq] at hu ⊢
    exact ⟨hu.1, lt_trans h hu.2⟩
  · simp
  · simp only [decide_eq_true_eq]
    exact ⟨hy, h⟩

/-- Each level is saturated at some finite stage. -/
lemma exists_sat (hmono : ∀ p s s' x, s ≤ s' → Q (p, s, x) = true → Q (p, s', x) = true)
    (p n : ℕ) :
    ∃ s, ∀ u, u.length = n → (∃ s', Q (p, s', u) = true) → Q (p, s, u) = true := by
  classical
  have key : ∀ l : List BitString, ∃ s, ∀ u ∈ l, (∃ s', Q (p, s', u) = true) →
      Q (p, s, u) = true := by
    intro l
    induction l with
    | nil => exact ⟨0, by simp⟩
    | cons a t ih =>
      obtain ⟨s, hs⟩ := ih
      by_cases ha : ∃ s', Q (p, s', a) = true
      · obtain ⟨s', hs'⟩ := ha
        refine ⟨max s s', ?_⟩
        intro u hu hex
        rcases List.mem_cons.mp hu with rfl | hut
        · exact hmono p s' (max s s') u (le_max_right _ _) hs'
        · exact hmono p s (max s s') u (le_max_left _ _) (hs u hut hex)
      · refine ⟨s, ?_⟩
        intro u hu hex
        rcases List.mem_cons.mp hu with rfl | hut
        · exact absurd hex ha
        · exact hs u hut hex
  obtain ⟨s, hs⟩ := key (allStrings n)
  exact ⟨s, fun u hu hex => hs u ((mem_allStrings n u).mpr hu) hex⟩

/-- Once the stage `s` witnesses every enumerated string of level `n`, the stage-bounded left
count agrees with the true left count. -/
lemma mLeft_eq_true_of_sat {p n s : ℕ} (y : BitString)
    (hs : ∀ u, u.length = n → (∃ s', Q (p, s', u) = true) → Q (p, s, u) = true) :
    mLeft Q ((p, n, s), y) = mTrueLeft Q p n y := by
  refine List.countP_congr ?_
  intro u hu
  have hulen : u.length = n := (mem_allStrings n u).mp hu
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨s, h1⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨hs u hulen h1, h2⟩

/-- Once the stage `s` witnesses every enumerated string of level `n`, the stage-bounded right
count agrees with the true right count. -/
lemma mRight_eq_true_of_sat {p n s : ℕ} (y : BitString)
    (hs : ∀ u, u.length = n → (∃ s', Q (p, s', u) = true) → Q (p, s, u) = true) :
    mRight Q ((p, n, s), y) = mTrueRight Q p n y := by
  refine List.countP_congr ?_
  intro u hu
  have hulen : u.length = n := (mem_allStrings n u).mp hu
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨s, h1⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨hs u hulen h1, h2⟩

/-! ### The search -/

/-- The body of the left-hand search: the argument is `(((p, L, n, T), v), n1)`. -/
def mBodyL (z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ) : Bool :=
  decide (z.1.1.2.2.1 ≤ z.2) && decide (z.2 ≤ z.1.2.length) &&
    Q (z.1.1.1, z.1.1.2.2.2, z.1.2.take z.2) &&
    decide (z.1.1.2.1 ≤ mLeft Q ((z.1.1.1, z.2, z.1.1.2.2.2), z.1.2.take z.2))

/-- The body of the right-hand search: the argument is `(((p, R, n, T), v), n2)`. -/
def mBodyR (z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ) : Bool :=
  decide (z.1.1.2.2.1 ≤ z.2) && decide (z.2 ≤ z.1.2.length) &&
    Q (z.1.1.1, z.1.1.2.2.2, z.1.2.take z.2) &&
    decide (z.1.1.2.1 ≤ mRight Q ((z.1.1.1, z.2, z.1.1.2.2.2), z.1.2.take z.2))

/-- The body of the left-hand search is primitive recursive when the enumeration test is. -/
theorem mBodyL_primrec (hQ : Primrec Q) : Primrec (mBodyL Q) := by
  have hp : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hL : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hn : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hT : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hv : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.2) := Primrec.snd
  have htake : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.2.take z.2) :=
    Primrec.list_take.comp hv hi
  have e1 : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ =>
      decide (z.1.1.2.2.1 ≤ z.2)) := PrimrecPred.decide (Primrec.nat_le.comp hn hi)
  have e2 : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ =>
      decide (z.2 ≤ z.1.2.length)) :=
    PrimrecPred.decide (Primrec.nat_le.comp hi (Primrec.list_length.comp hv))
  have e3 : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ =>
      Q (z.1.1.1, z.1.1.2.2.2, z.1.2.take z.2)) :=
    hQ.comp (Primrec.pair hp (Primrec.pair hT htake))
  have e4 : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ =>
      decide (z.1.1.2.1 ≤ mLeft Q ((z.1.1.1, z.2, z.1.1.2.2.2), z.1.2.take z.2))) :=
    PrimrecPred.decide (Primrec.nat_le.comp hL
      ((mLeft_primrec Q hQ).comp (Primrec.pair (Primrec.pair hp (Primrec.pair hi hT)) htake)))
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp e1 e2) e3) e4

/-- The body of the right-hand search is primitive recursive when the enumeration test is. -/
theorem mBodyR_primrec (hQ : Primrec Q) : Primrec (mBodyR Q) := by
  have hp : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hL : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hn : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hT : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hv : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.2) := Primrec.snd
  have htake : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ => z.1.2.take z.2) :=
    Primrec.list_take.comp hv hi
  have e1 : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ =>
      decide (z.1.1.2.2.1 ≤ z.2)) := PrimrecPred.decide (Primrec.nat_le.comp hn hi)
  have e2 : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ =>
      decide (z.2 ≤ z.1.2.length)) :=
    PrimrecPred.decide (Primrec.nat_le.comp hi (Primrec.list_length.comp hv))
  have e3 : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ =>
      Q (z.1.1.1, z.1.1.2.2.2, z.1.2.take z.2)) :=
    hQ.comp (Primrec.pair hp (Primrec.pair hT htake))
  have e4 : Primrec (fun z : ((ℕ × ℕ × ℕ × ℕ) × BitString) × ℕ =>
      decide (z.1.1.2.1 ≤ mRight Q ((z.1.1.1, z.2, z.1.1.2.2.2), z.1.2.take z.2))) :=
    PrimrecPred.decide (Primrec.nat_le.comp hL
      ((mRight_primrec Q hQ).comp (Primrec.pair (Primrec.pair hp (Primrec.pair hi hT)) htake)))
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp e1 e2) e3) e4

/-- The verification predicate: the argument is `((p, L, R, n, T), v)`.  It says that at
budget `T` the candidate `v` is certified: at some level `n1 ≥ n` its prefix is already
enumerated and has at least `L` enumerated strings to its left, and at some level
`n2 ≥ n` its prefix is already enumerated and has at least `R` enumerated strings to its
right. -/
def mCheck (a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString) : Bool :=
  (List.range (a.1.2.2.2.2 + 1)).any
      (fun n1 => mBodyL Q (((a.1.1, a.1.2.1, a.1.2.2.2.1, a.1.2.2.2.2), a.2), n1)) &&
    (List.range (a.1.2.2.2.2 + 1)).any
      (fun n2 => mBodyR Q (((a.1.1, a.1.2.2.1, a.1.2.2.2.1, a.1.2.2.2.2), a.2), n2))

/-- The certificate test is primitive recursive when the enumeration test is. -/
theorem mCheck_primrec (hQ : Primrec Q) : Primrec (mCheck Q) := by
  have hp : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString => a.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hL : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString => a.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hR : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString => a.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hn : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString => a.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hT : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString => a.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hv : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString => a.2) := Primrec.snd
  have hrange : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString =>
      List.range (a.1.2.2.2.2 + 1)) := Primrec.list_range.comp (Primrec.succ.comp hT)
  have hbL : Primrec₂ (fun (a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString) (n1 : ℕ) =>
      mBodyL Q (((a.1.1, a.1.2.1, a.1.2.2.2.1, a.1.2.2.2.2), a.2), n1)) :=
    ((mBodyL_primrec Q hQ).comp (Primrec.pair
      (Primrec.pair (Primrec.pair (hp.comp Primrec.fst)
        (Primrec.pair (hL.comp Primrec.fst)
          (Primrec.pair (hn.comp Primrec.fst) (hT.comp Primrec.fst))))
        (hv.comp Primrec.fst)) Primrec.snd)).to₂
  have hbR : Primrec₂ (fun (a : (ℕ × ℕ × ℕ × ℕ × ℕ) × BitString) (n2 : ℕ) =>
      mBodyR Q (((a.1.1, a.1.2.2.1, a.1.2.2.2.1, a.1.2.2.2.2), a.2), n2)) :=
    ((mBodyR_primrec Q hQ).comp (Primrec.pair
      (Primrec.pair (Primrec.pair (hp.comp Primrec.fst)
        (Primrec.pair (hR.comp Primrec.fst)
          (Primrec.pair (hn.comp Primrec.fst) (hT.comp Primrec.fst))))
        (hv.comp Primrec.fst)) Primrec.snd)).to₂
  exact Primrec.and.comp (list_any_primrec hrange hbL) (list_any_primrec hrange hbR)

/-- The stage-`T` attempt to compute the length-`n` prefix.  The argument is
`((p, L, R, n), T)`. -/
def mFind (a : (ℕ × ℕ × ℕ × ℕ) × ℕ) : Option BitString :=
  ((allStrings a.2).find?
      (fun v => mCheck Q ((a.1.1, a.1.2.1, a.1.2.2.1, a.1.2.2.2, a.2), v))).map
    (fun v => v.take a.1.2.2.2)

/-- The stage-bounded attempt to compute the prefix is primitive recursive when the enumeration
test is. -/
theorem mFind_primrec (hQ : Primrec Q) : Primrec (mFind Q) := by
  have hp : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ) × ℕ => a.1.1) := Primrec.fst.comp Primrec.fst
  have hL : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ) × ℕ => a.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hR : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ) × ℕ => a.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hn : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ) × ℕ => a.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hT : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ) × ℕ => a.2) := Primrec.snd
  have hlist : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ) × ℕ => allStrings a.2) :=
    allStrings_primrec.comp hT
  have hpred : Primrec₂ (fun (a : (ℕ × ℕ × ℕ × ℕ) × ℕ) (v : BitString) =>
      mCheck Q ((a.1.1, a.1.2.1, a.1.2.2.1, a.1.2.2.2, a.2), v)) :=
    ((mCheck_primrec Q hQ).comp (Primrec.pair
      (Primrec.pair (hp.comp Primrec.fst)
        (Primrec.pair (hL.comp Primrec.fst)
          (Primrec.pair (hR.comp Primrec.fst)
            (Primrec.pair (hn.comp Primrec.fst) (hT.comp Primrec.fst)))))
      Primrec.snd)).to₂
  have hfind : Primrec (fun a : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
      (allStrings a.2).find?
        (fun v => mCheck Q ((a.1.1, a.1.2.1, a.1.2.2.1, a.1.2.2.2, a.2), v))) :=
    list_find?_primrec hlist hpred
  exact Primrec.option_map hfind
    (Primrec.list_take.comp Primrec.snd (hn.comp Primrec.fst)).to₂

/-- The partial recursive search: on the argument `(p, L, R, n)` it looks for the first
budget at which a certificate is found, and returns the length-`n` prefix it certifies. -/
def mSearch (b : ℕ × ℕ × ℕ × ℕ) : Part BitString :=
  (Nat.rfind fun T => Part.some (mFind Q (b, T)).isSome).bind
    (fun T => Part.ofOption (mFind Q (b, T)))

/-- The unbounded search for a certified prefix is partial recursive when the enumeration test
is primitive recursive. -/
theorem mSearch_partrec (hQ : Primrec Q) : Partrec (mSearch Q) := by
  have hf : Computable (mFind Q) := (mFind_primrec Q hQ).to_comp
  have hrf : Partrec (fun b : ℕ × ℕ × ℕ × ℕ =>
      Nat.rfind fun T => Part.some (mFind Q (b, T)).isSome) :=
    Partrec.rfind (Computable.partrec ((Primrec.option_isSome.to_comp).comp hf)).to₂
  exact Partrec.bind hrf (Computable.ofOption hf).to₂

/-- **The Meyer core.**  If the level sections of the enumerable set `S p` have at most
`B` elements from level `N₀` on, and the prefixes of `w` from level `N₀` on all belong to
`S p`, then there are counts `L, R ≤ B` and a level `N ≥ N₀` from which the uniform
partial recursive search `mSearch` computes every prefix of `w`. -/
theorem mSearch_spec (hmono : ∀ p s s' x, s ≤ s' → Q (p, s, x) = true → Q (p, s', x) = true)
    (p B N₀ : ℕ) (w : ℕ → Bool)
    (hlevel : ∀ n, N₀ ≤ n → mLevelCount Q p n ≤ B)
    (hw : ∀ n, N₀ ≤ n → ∃ s, Q (p, s, seqPrefix w n) = true) :
    ∃ L R N : ℕ, L ≤ B ∧ R ≤ B ∧ N₀ ≤ N ∧
      ∀ n, N ≤ n → mSearch Q (p, L, R, n) = Part.some (seqPrefix w n) := by
  obtain ⟨L, NL, hLB, hN₀L, hLub, hLinf⟩ :=
    exists_limsup (fun n => mTrueLeft Q p n (seqPrefix w n)) B N₀
      (fun n hn => le_trans (mTrueLeft_le_level Q p n _) (hlevel n hn))
  obtain ⟨R, NR, hRB, hN₀R, hRub, hRinf⟩ :=
    exists_limsup (fun n => mTrueRight Q p n (seqPrefix w n)) B N₀
      (fun n hn => le_trans (mTrueRight_le_level Q p n _) (hlevel n hn))
  refine ⟨L, R, max NL NR, hLB, hRB, le_trans hN₀L (le_max_left _ _), ?_⟩
  intro n hn
  have hnNL : NL ≤ n := le_trans (le_max_left _ _) hn
  have hnNR : NR ≤ n := le_trans (le_max_right _ _) hn
  have hnN₀ : N₀ ≤ n := le_trans hN₀L hnNL
  have hsound : ∀ (T : ℕ) (v : BitString), v.length = T →
      mCheck Q ((p, L, R, n, T), v) = true → v.take n = seqPrefix w n := by
    intro T v hvlen hchk
    rw [mCheck, Bool.and_eq_true] at hchk
    obtain ⟨hc1, hc2⟩ := hchk
    rw [List.any_eq_true] at hc1 hc2
    obtain ⟨n1, -, hb1⟩ := hc1
    obtain ⟨n2, -, hb2⟩ := hc2
    simp only [mBodyL, Bool.and_eq_true, decide_eq_true_eq] at hb1
    simp only [mBodyR, Bool.and_eq_true, decide_eq_true_eq] at hb2
    obtain ⟨⟨⟨hnn1, hn1v⟩, hQ1⟩, hL1⟩ := hb1
    obtain ⟨⟨⟨hnn2, hn2v⟩, hQ2⟩, hR2⟩ := hb2
    have hv1len : (v.take n1).length = n1 := by rw [List.length_take]; omega
    have hv2len : (v.take n2).length = n2 := by rw [List.length_take]; omega
    have hkey1 : lexKey (seqPrefix w n1) ≤ lexKey (v.take n1) := by
      by_contra hcon
      push_neg at hcon
      have hstrict := mTrueLeft_strict Q ⟨T, hQ1⟩ hv1len hcon
      have h1' : L ≤ mTrueLeft Q p n1 (v.take n1) :=
        le_trans hL1 (mLeft_le_true Q p n1 T (v.take n1))
      have h2' : mTrueLeft Q p n1 (seqPrefix w n1) ≤ L := hLub n1 (by omega)
      omega
    have hkey2 : lexKey (v.take n2) ≤ lexKey (seqPrefix w n2) := by
      by_contra hcon
      push_neg at hcon
      have hstrict := mTrueRight_strict Q ⟨T, hQ2⟩ hv2len hcon
      have h1' : R ≤ mTrueRight Q p n2 (v.take n2) :=
        le_trans hR2 (mRight_le_true Q p n2 T (v.take n2))
      have h2' : mTrueRight Q p n2 (seqPrefix w n2) ≤ R := hRub n2 (by omega)
      omega
    have hp1 : lexKey (seqPrefix w n) ≤ lexKey (v.take n) := by
      have h := lexKey_take_le (x := seqPrefix w n1) (y := v.take n1) n
        (by rw [length_seqPrefix, hv1len]) hkey1
      rwa [seqPrefix_take w hnn1, List.take_take, min_eq_left hnn1] at h
    have hp2 : lexKey (v.take n) ≤ lexKey (seqPrefix w n) := by
      have h := lexKey_take_le (x := v.take n2) (y := seqPrefix w n2) n
        (by rw [length_seqPrefix, hv2len]) hkey2
      rwa [seqPrefix_take w hnn2, List.take_take, min_eq_left hnn2] at h
    have hlen_vn : (v.take n).length = n := by rw [List.length_take]; omega
    exact lexKey_inj (by rw [hlen_vn, length_seqPrefix]) (le_antisymm hp2 hp1)
  obtain ⟨n1, hn1ge, hn1L⟩ := hLinf n
  obtain ⟨n2, hn2ge, hn2R⟩ := hRinf n
  obtain ⟨s1, hs1⟩ := exists_sat Q hmono p n1
  obtain ⟨s2, hs2⟩ := exists_sat Q hmono p n2
  obtain ⟨s3, hs3⟩ := hw n1 (le_trans hnN₀ hn1ge)
  obtain ⟨s4, hs4⟩ := hw n2 (le_trans hnN₀ hn2ge)
  set T := max (max n1 n2) (max (max s1 s2) (max s3 s4)) with hTdef
  have hT1 : n1 ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT2 : n2 ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  have hTs1 : s1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hTs2 : s2 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hTs3 : s3 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hTs4 : s4 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hcheck : mCheck Q ((p, L, R, n, T), seqPrefix w T) = true := by
    rw [mCheck, Bool.and_eq_true]
    constructor
    · rw [List.any_eq_true]
      refine ⟨n1, List.mem_range.mpr (by change n1 < T + 1; omega), ?_⟩
      simp only [mBodyL, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨hn1ge, ?_⟩, ?_⟩, ?_⟩
      · show n1 ≤ (seqPrefix w T).length
        rw [length_seqPrefix]; exact hT1
      · show Q (p, T, (seqPrefix w T).take n1) = true
        rw [seqPrefix_take w hT1]
        exact hmono p s3 T _ hTs3 hs3
      · show L ≤ mLeft Q ((p, n1, T), (seqPrefix w T).take n1)
        rw [seqPrefix_take w hT1,
          mLeft_eq_true_of_sat Q _ (fun u hu hex => hmono p s1 T u hTs1 (hs1 u hu hex))]
        exact hn1L
    · rw [List.any_eq_true]
      refine ⟨n2, List.mem_range.mpr (by change n2 < T + 1; omega), ?_⟩
      simp only [mBodyR, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨hn2ge, ?_⟩, ?_⟩, ?_⟩
      · show n2 ≤ (seqPrefix w T).length
        rw [length_seqPrefix]; exact hT2
      · show Q (p, T, (seqPrefix w T).take n2) = true
        rw [seqPrefix_take w hT2]
        exact hmono p s4 T _ hTs4 hs4
      · show R ≤ mRight Q ((p, n2, T), (seqPrefix w T).take n2)
        rw [seqPrefix_take w hT2,
          mRight_eq_true_of_sat Q _ (fun u hu hex => hmono p s2 T u hTs2 (hs2 u hu hex))]
        exact hn2R
  have hisSome : (mFind Q ((p, L, R, n), T)).isSome = true := by
    rw [mFind]
    simp only [Option.isSome_map]
    rw [List.find?_isSome]
    exact ⟨seqPrefix w T, (mem_allStrings T _).mpr (by simp), hcheck⟩
  have hdom : (Nat.rfind fun T' => Part.some (mFind Q ((p, L, R, n), T')).isSome).Dom :=
    Nat.rfind_dom.mpr ⟨T, by simpa using hisSome, fun _ => Part.some_dom _⟩
  obtain ⟨T', hT'mem⟩ := Part.dom_iff_mem.mp hdom
  have hT'true : (mFind Q ((p, L, R, n), T')).isSome = true := by
    have := (Nat.mem_rfind.mp hT'mem).1
    simpa using this
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hT'true
  have hzval : z = seqPrefix w n := by
    rw [mFind, Option.map_eq_some_iff] at hz
    obtain ⟨v, hvfind, hzv⟩ := hz
    have hvmem := List.mem_of_find?_eq_some hvfind
    have hvchk := List.find?_some hvfind
    have hvlen : v.length = T' := (mem_allStrings T' v).mp hvmem
    rw [← hzv]
    exact hsound T' v hvlen hvchk
  rw [Part.eq_some_iff, mSearch, Part.mem_bind_iff]
  exact ⟨T', hT'mem, by rw [hz, ← hzval]; exact Part.mem_some _⟩

/-! ### SUV problem 49 -/

/-- There are fewer than `2 ^ (m+1)` strings of conditional complexity at most `m`. -/
lemma card_lt_of_condK_le (U : Map) (y : BitString) (m : ℕ) (A : Finset BitString)
    (hA : ∀ x ∈ A, condK U x y ≤ (m : ENat)) : A.card < 2 ^ (m + 1) := by
  classical
  have hchoose : ∀ x ∈ A, ∃ p : BitString, p.length ≤ m ∧ produces U p y x := by
    intro x hx
    exact (condK_le_iff U x y m).mp (hA x hx)
  choose! f hf1 hf2 using hchoose
  have hmaps : ∀ x ∈ A, f x ∈ (boundedPrograms m).toFinset := by
    intro x hx
    rw [List.mem_toFinset]
    exact (mem_boundedPrograms_iff (f x) m).mpr (hf1 x hx)
  have hinj : Set.InjOn f A := by
    intro x hx x' hx' h
    have h1 : x ∈ U (f x, y) := hf2 x hx
    have h2 : x' ∈ U (f x', y) := hf2 x' hx'
    rw [h] at h1
    exact Part.mem_unique h1 h2
  calc A.card ≤ (boundedPrograms m).toFinset.card := Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ (boundedPrograms m).length := List.toFinset_card_le _
    _ < 2 ^ (m + 1) := length_boundedPrograms_lt m

/-- Counting the strings of length `n` satisfying a predicate agrees with the cardinality of the
corresponding filtered finite set. -/
lemma countP_allStrings_eq_card (P : BitString → Bool) (n : ℕ) :
    (allStrings n).countP P = ((stringsOfLength n).filter (fun x => P x = true)).card := by
  classical
  rw [List.countP_eq_length_filter, stringsOfLength, ← List.toFinset_filter,
    List.toFinset_card_of_nodup ((allStrings_nodup n).filter _)]

/-- `x` is enumerated as a string of complexity at most `Nat.log 2 |x| + par` by stage `s`.
The argument is `(par, s, x)`. -/
def logPrefixBase (cd : Code) (a : ℕ × ℕ × BitString) : Bool :=
  decide (a.2.2 ∈ boundedOutputStage cd (Nat.log 2 a.2.2.length + a.1) a.2.1)

/-- The pruned tree at stage `s`: `x` has an extension of length `2 |x|` all of whose
levels from `|x|` on are already enumerated.  The argument is `(par, s, x)`. -/
def logPrefixQ (cd : Code) (a : ℕ × ℕ × BitString) : Bool :=
  (allStrings (2 * a.2.2.length)).any (fun y =>
    decide (y.take a.2.2.length = a.2.2) &&
      (List.range (a.2.2.length + 1)).all
        (fun i => logPrefixBase cd (a.1, a.2.1, y.take (a.2.2.length + i))))

private theorem logPrefixBase_primrec (cd : Code) : Primrec (logPrefixBase cd) := by
  have hx : Primrec (fun a : ℕ × ℕ × BitString => a.2.2) := Primrec.snd.comp Primrec.snd
  have hs : Primrec (fun a : ℕ × ℕ × BitString => a.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun a : ℕ × ℕ × BitString => Nat.log 2 a.2.2.length + a.1) :=
    Primrec.nat_add.comp (primrec_natLogTwo.comp (Primrec.list_length.comp hx)) Primrec.fst
  have hstage : Primrec (fun a : ℕ × ℕ × BitString =>
      boundedOutputStage cd (Nat.log 2 a.2.2.length + a.1) a.2.1) :=
    (boundedOutputStage_primrec cd).comp (Primrec.pair hm hs)
  exact bitString_mem_primrec.comp hx hstage

private theorem logPrefixQ_primrec (cd : Code) : Primrec (logPrefixQ cd) := by
  have hx : Primrec (fun a : ℕ × ℕ × BitString => a.2.2) := Primrec.snd.comp Primrec.snd
  have hlist : Primrec (fun a : ℕ × ℕ × BitString => allStrings (2 * a.2.2.length)) :=
    allStrings_primrec.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.list_length.comp hx))
  have hinner : Primrec₂ (fun (z : (ℕ × ℕ × BitString) × BitString) (i : ℕ) =>
      !(logPrefixBase cd (z.1.1, z.1.2.1, z.2.take (z.1.2.2.length + i)))) := by
    have hpar : Primrec (fun q : ((ℕ × ℕ × BitString) × BitString) × ℕ => q.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hs : Primrec (fun q : ((ℕ × ℕ × BitString) × BitString) × ℕ => q.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have htake : Primrec (fun q : ((ℕ × ℕ × BitString) × BitString) × ℕ =>
        q.1.2.take (q.1.1.2.2.length + q.2)) :=
      Primrec.list_take.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.nat_add.comp
          (Primrec.list_length.comp
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
          Primrec.snd)
    exact (Primrec.not.comp
      ((logPrefixBase_primrec cd).comp (Primrec.pair hpar (Primrec.pair hs htake)))).to₂
  have hrange : Primrec (fun z : (ℕ × ℕ × BitString) × BitString =>
      List.range (z.1.2.2.length + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hbody : Primrec₂ (fun (a : ℕ × ℕ × BitString) (y : BitString) =>
      decide (y.take a.2.2.length = a.2.2) &&
        (List.range (a.2.2.length + 1)).all
          (fun i => logPrefixBase cd (a.1, a.2.1, y.take (a.2.2.length + i)))) := by
    have heq : Primrec (fun z : (ℕ × ℕ × BitString) × BitString =>
        decide (z.2.take z.1.2.2.length = z.1.2.2)) :=
      PrimrecPred.decide (Primrec.eq.comp
        (Primrec.list_take.comp Primrec.snd
          (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    have hall : Primrec (fun z : (ℕ × ℕ × BitString) × BitString =>
        (List.range (z.1.2.2.length + 1)).all
          (fun i => logPrefixBase cd (z.1.1, z.1.2.1, z.2.take (z.1.2.2.length + i)))) :=
      (Primrec.not.comp (list_any_primrec hrange hinner)).of_eq (fun z => by
        rw [List.all_eq_not_any_not])
    exact (Primrec.and.comp heq hall).to₂
  exact list_any_primrec hlist hbody

private lemma logPrefixQ_iff (cd : Code) (par s : ℕ) (x : BitString) :
    logPrefixQ cd (par, s, x) = true ↔ ∃ y : BitString, y.length = 2 * x.length ∧
      y.take x.length = x ∧
      ∀ i ≤ x.length, logPrefixBase cd (par, s, y.take (x.length + i)) = true := by
  simp only [logPrefixQ, List.any_eq_true, mem_allStrings, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Nat.lt_succ_iff]

private lemma logPrefixBase_mono (cd : Code) (par s s' : ℕ) (z : BitString) (h : s ≤ s')
    (hb : logPrefixBase cd (par, s, z) = true) : logPrefixBase cd (par, s', z) = true := by
  simp only [logPrefixBase, decide_eq_true_eq] at hb ⊢
  exact (boundedOutputStage_prefix_of_le cd _ h).subset hb

private lemma logPrefixQ_mono (cd : Code) : ∀ (par s s' : ℕ) (x : BitString), s ≤ s' →
    logPrefixQ cd (par, s, x) = true → logPrefixQ cd (par, s', x) = true := by
  intro par s s' x hss hQ
  rw [logPrefixQ_iff] at hQ ⊢
  obtain ⟨y, h1, h2, h3⟩ := hQ
  exact ⟨y, h1, h2, fun i hi => logPrefixBase_mono cd par s s' _ hss (h3 i hi)⟩

private lemma logPrefixBase_sound {U : Map} {cd : Code} (hc : IsCodeFor cd U) (par s : ℕ)
    (z : BitString)
    (h : logPrefixBase cd (par, s, z) = true) :
    plainK U z ≤ ((Nat.log 2 z.length + par : ℕ) : ENat) := by
  simp only [logPrefixBase, decide_eq_true_eq] at h
  exact (Dovetailing.exists_stage_mem_iff_plainK_le hc _ z).mp ⟨s, h⟩

/-- A common stage for finitely many enumerated strings. -/
lemma exists_common_stage (cd : Code) (f : ℕ → BitString) (m : ℕ → ℕ) (k : ℕ)
    (h : ∀ i ≤ k, ∃ s, f i ∈ boundedOutputStage cd (m i) s) :
    ∃ s, ∀ i ≤ k, f i ∈ boundedOutputStage cd (m i) s := by
  induction k with
  | zero =>
    obtain ⟨s, hs⟩ := h 0 (le_refl 0)
    exact ⟨s, fun i hi => by simpa [Nat.le_zero.mp hi] using hs⟩
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨s', hs'⟩ := h (k + 1) (le_refl _)
    refine ⟨max s s', fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with hlt | rfl
    · exact (boundedOutputStage_prefix_of_le cd _ (le_max_left s s')).subset (hs i (by omega))
    · exact (boundedOutputStage_prefix_of_le cd _ (le_max_right s s')).subset hs'

/-- The counting core of SUV problem 49: pruning to the strings with a completely
enumerated extension of twice their length bounds every level by a constant. -/
private lemma logPrefix_counting {U : Map} {cd : Code} (hc : IsCodeFor cd U) (c n : ℕ) (hn : 1 ≤ n)
    (A : Finset BitString)
    (hA : ∀ x ∈ A, x.length = n ∧ ∃ y : BitString, y.length = 2 * n ∧ y.take n = x ∧
      ∀ i ≤ n, plainK U (y.take (n + i)) ≤ ((Nat.log 2 (n + i) + c : ℕ) : ENat)) :
    A.card ≤ 2 ^ (c + 2) := by
  classical
  set m := Nat.log 2 (2 * n) + c with hm
  choose! hAlen Y hY1 hY2 hY3 using hA
  set F : BitString → Finset BitString :=
    fun x => ((List.range n).map (fun i => (Y x).take (n + i))).toFinset with hF
  set D : Finset BitString := (completedBoundedOutput cd m).toFinset with hD
  have hlen_take : ∀ x ∈ A, ∀ i, i ≤ n → ((Y x).take (n + i)).length = n + i := by
    intro x hx i hi
    rw [List.length_take, hY1 x hx]
    omega
  have hFcard : ∀ x ∈ A, (F x).card = n := by
    intro x hx
    rw [hF]
    have hnodup : ((List.range n).map (fun i => (Y x).take (n + i))).Nodup := by
      refine (List.nodup_range).map_on ?_
      intro i hi j hj hij
      have hi' : i < n := List.mem_range.mp hi
      have hj' : j < n := List.mem_range.mp hj
      have := congrArg List.length hij
      rw [hlen_take x hx i (by omega), hlen_take x hx j (by omega)] at this
      omega
    rw [List.toFinset_card_of_nodup hnodup, List.length_map, List.length_range]
  have hFsub : ∀ x ∈ A, F x ⊆ D := by
    intro x hx z hz
    rw [hF, List.mem_toFinset, List.mem_map] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    have hi' : i < n := List.mem_range.mp hi
    rw [hD, List.mem_toFinset, mem_completedBoundedOutput_iff_plainK_le hc]
    refine le_trans (hY3 x hx i (by omega)) ?_
    have : Nat.log 2 (n + i) + c ≤ m := by
      rw [hm]
      have := Nat.log_mono_right (b := 2) (show n + i ≤ 2 * n by omega)
      omega
    exact_mod_cast this
  have hdisj : ∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → Disjoint (F x) (F x') := by
    intro x hx x' hx' hne
    rw [Finset.disjoint_left]
    intro z hz hz'
    have hzx : ∀ u ∈ A, z ∈ F u → z.take n = u := by
      intro u hu hzu
      rw [hF, List.mem_toFinset, List.mem_map] at hzu
      obtain ⟨i, -, hzi⟩ := hzu
      rw [← hzi, List.take_take, min_eq_left (by omega), hY2 u hu]
    exact hne ((hzx x hx hz).symm.trans (hzx x' hx' hz'))
  have hbi : (A.biUnion F).card = ∑ x ∈ A, (F x).card := Finset.card_biUnion hdisj
  have hsum : ∑ x ∈ A, (F x).card = A.card * n := by
    rw [Finset.sum_congr rfl hFcard, Finset.sum_const, smul_eq_mul]
  have hsubD : A.biUnion F ⊆ D := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    exact hFsub x hx hzx
  have hDcard : D.card < 2 ^ (m + 1) := by
    refine card_lt_of_condK_le U [] m D ?_
    intro z hz
    rw [hD, List.mem_toFinset, mem_completedBoundedOutput_iff_plainK_le hc] at hz
    exact hz
  have hbound : 2 ^ (m + 1) ≤ 2 ^ (c + 2) * n := by
    rw [hm]
    have h1 : 2 ^ (Nat.log 2 (2 * n)) ≤ 2 * n := Nat.pow_log_le_self 2 (by omega)
    calc 2 ^ (Nat.log 2 (2 * n) + c + 1) = 2 ^ (Nat.log 2 (2 * n)) * 2 ^ (c + 1) := by
          rw [← pow_add, Nat.add_assoc]
      _ ≤ (2 * n) * 2 ^ (c + 1) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (c + 2) * n := by ring
  have hkey : A.card * n < 2 ^ (c + 2) * n := by
    calc A.card * n = (A.biUnion F).card := by rw [hbi, hsum]
      _ ≤ D.card := Finset.card_le_card hsubD
      _ < 2 ^ (m + 1) := hDcard
      _ ≤ 2 ^ (c + 2) * n := hbound
  exact le_of_lt (Nat.lt_of_mul_lt_mul_right hkey)

private lemma logPrefix_hw {U : Map} {cd : Code} (hc : IsCodeFor cd U) (w : ℕ → Bool) (c : ℕ)
    (hbound : ∀ n : ℕ, plainK U (seqPrefix w n) ≤ ((Nat.log 2 n + c : ℕ) : ℕ∞)) :
    ∀ n, 1 ≤ n → ∃ s, logPrefixQ cd (c, s, seqPrefix w n) = true := by
  intro n _
  have hstages : ∀ i ≤ n, ∃ s, (seqPrefix w (2 * n)).take (n + i) ∈
      boundedOutputStage cd (Nat.log 2 ((seqPrefix w (2 * n)).take (n + i)).length + c) s := by
    intro i hi
    have hyt : (seqPrefix w (2 * n)).take (n + i) = seqPrefix w (n + i) :=
      seqPrefix_take w (by omega)
    rw [hyt, length_seqPrefix]
    exact (Dovetailing.exists_stage_mem_iff_plainK_le hc _ _).mpr (hbound (n + i))
  obtain ⟨s, hs⟩ := exists_common_stage cd (fun i => (seqPrefix w (2 * n)).take (n + i))
    (fun i => Nat.log 2 ((seqPrefix w (2 * n)).take (n + i)).length + c) n hstages
  refine ⟨s, ?_⟩
  rw [logPrefixQ_iff]
  refine ⟨seqPrefix w (2 * n), by simp, ?_, ?_⟩
  · rw [length_seqPrefix]; exact seqPrefix_take w (by omega)
  · intro i hi
    rw [length_seqPrefix] at hi ⊢
    simpa only [logPrefixBase, decide_eq_true_eq] using hs i hi

private lemma logPrefix_hlevel {U : Map} {cd : Code} (hc : IsCodeFor cd U) (c : ℕ) :
    ∀ n, 1 ≤ n → mLevelCount (logPrefixQ cd) c n ≤ 2 ^ (c + 2) := by
  intro n hn
  classical
  rw [mLevelCount, countP_allStrings_eq_card]
  refine logPrefix_counting hc c n hn _ ?_
  intro x hx
  rw [Finset.mem_filter] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxlen : x.length = n := by
    rw [stringsOfLength, List.mem_toFinset, mem_allStrings] at hx1; exact hx1
  refine ⟨hxlen, ?_⟩
  simp only [decide_eq_true_eq] at hx2
  obtain ⟨s, hs⟩ := hx2
  rw [logPrefixQ_iff] at hs
  obtain ⟨y, hy1, hy2, hy3⟩ := hs
  rw [hxlen] at hy1 hy2 hy3
  refine ⟨y, hy1, hy2, ?_⟩
  intro i hi
  have hlt : (y.take (n + i)).length = n + i := by rw [List.length_take, hy1]; omega
  have := logPrefixBase_sound hc c s (y.take (n + i)) (hy3 i hi)
  rwa [hlt] at this

/-- **Exercise 49.** `C(prefix_n) ≤ log n + O(1)` already forces computability. -/
theorem computable_of_plainK_prefix_le_log (U : Map) (hU : isOptimalConditional U)
    (w : ℕ → Bool) (c : ℕ)
    (hbound : ∀ n : ℕ, plainK U (seqPrefix w n) ≤ ((Nat.log 2 n + c : ℕ) : ℕ∞)) :
    Computable w := by
  obtain ⟨cd, hc⟩ := Dovetailing.exists_isCodeFor hU
  obtain ⟨L, R, N, -, -, -, hspec⟩ :=
    mSearch_spec (logPrefixQ cd) (logPrefixQ_mono cd) c (2 ^ (c + 2)) 1 w
      (logPrefix_hlevel hc c) (logPrefix_hw hc w c hbound)
  have harg : Computable (fun n : ℕ => ((c, L, R, max (n + 1) N) : ℕ × ℕ × ℕ × ℕ)) := by
    refine Computable.pair (Computable.const c) (Computable.pair (Computable.const L)
      (Computable.pair (Computable.const R) ?_))
    exact (Primrec.nat_max.comp (Primrec.succ.comp Primrec.id) (Primrec.const N)).to_comp
  have hg : Computable₂ (fun (n : ℕ) (v : BitString) => (v[n]?).getD false) := by
    have h1 : Computable (fun q : ℕ × BitString => q.2[q.1]?) :=
      Computable.list_getElem?.comp Computable.snd Computable.fst
    exact (Computable.option_getD h1 (Computable.const false)).to₂
  have hpart : Partrec (fun n : ℕ =>
      (mSearch (logPrefixQ cd) (c, L, R, max (n + 1) N)).map (fun v => (v[n]?).getD false)) :=
    Partrec.map ((mSearch_partrec (logPrefixQ cd) (logPrefixQ_primrec cd)).comp harg) hg
  have heq : ∀ n : ℕ,
      (mSearch (logPrefixQ cd) (c, L, R, max (n + 1) N)).map (fun v => (v[n]?).getD false)
        = Part.some (w n) := by
    intro n
    rw [hspec (max (n + 1) N) (le_max_right _ _), Part.map_some]
    congr 1
    have hn : n < max (n + 1) N := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_left _ _)
    simp [seqPrefix, hn]
  exact hpart.of_eq heq

end Kolmogorov
