import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerHardRegime
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerLengthScale
import Mathlib.Tactic.Ring

open Kolmogorov
open CodedFiniteDistribution

/-- Inductive construction of all bit strings of length at most n. -/
def allStringsUpTo : ℕ → List BitString
  | 0 => allStrings 0
  | n + 1 => allStringsUpTo n ++ allStrings (n + 1)

@[simp]
lemma mem_allStringsUpTo (n : ℕ) (s : BitString) : s ∈ allStringsUpTo n ↔ s.length ≤ n := by
  induction n with
  | zero => simp [allStringsUpTo]
  | succ n ih =>
    simp [allStringsUpTo, ih]
    omega

lemma allStringsUpTo_nodup (n : ℕ) : (allStringsUpTo n).Nodup := by
  induction n with
  | zero => exact allStrings_nodup 0
  | succ n ih =>
    rw [allStringsUpTo]
    apply List.nodup_append.mpr
    refine ⟨ih, allStrings_nodup (n + 1), ?_⟩
    intro x h1 y h2 heq
    rw [mem_allStringsUpTo] at h1
    rw [mem_allStrings] at h2
    subst y
    omega

@[simp]
lemma length_allStringsUpTo (n : ℕ) : (allStringsUpTo n).length = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero =>
    rw [allStringsUpTo, length_allStrings]
    rfl
  | succ n ih =>
    rw [allStringsUpTo, List.length_append, ih, length_allStrings]
    have h : 2 ^ (n + 2) = 2 ^ (n + 1) + 2 ^ (n + 1) := by ring
    have h2 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    omega

def stringsOfLengthLe (n : ℕ) : Finset BitString :=
  (allStringsUpTo n).toFinset

@[simp]
lemma memStringsOfLengthLe (n : ℕ) (s : BitString) : s ∈ stringsOfLengthLe n ↔ s.length ≤ n := by
  rw [stringsOfLengthLe, List.mem_toFinset, mem_allStringsUpTo]

lemma stringsOfLengthLe_nonempty (n : ℕ) : (stringsOfLengthLe n).Nonempty := by
  use []
  simp

lemma cardStringsOfLengthLe_le (n : ℕ) : (stringsOfLengthLe n).card ≤ 2 ^ (n + 1) := by
  rw [stringsOfLengthLe, List.toFinset_card_of_nodup (allStringsUpTo_nodup n)]
  rw [length_allStringsUpTo]
  have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  omega

theorem allStringsUpTo_primrec : Primrec allStringsUpTo := by
  convert Primrec.nat_rec' _ _ _ using 1
  rotate_left
  · exact fun n => n
  · exact fun n => allStrings 0
  · exact fun n p => p.2 ++ allStrings (p.1 + 1)
  · exact Primrec.id
  · exact Primrec.const (allStrings 0)
  · apply Primrec₂.comp
    · exact Primrec.list_append
    · exact Primrec.snd.comp Primrec.snd
    · apply Primrec.comp allStrings_primrec
      apply Primrec.comp Primrec.succ
      apply Primrec.comp Primrec.fst
      exact Primrec.snd
  · funext l; induction l <;> simp [*, allStringsUpTo]

theorem plainSetComplexity_ball_le_KPPlain_natCode
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      plainSetComplexity V (stringsOfLengthLe n) (stringsOfLengthLe_nonempty n)
        ≤ KPPlain U (natCode n) + (c : ENat) := by
  obtain ⟨c₁, hc₁⟩ := KPPlain_map_le U hU
    (fun w => canonicalUniformCodeOfList
      (canonicalFinsetList (stringsOfLengthLe (decodeNatCode w)))) (by
        exact canonicalUniformCodeOfList_computable.comp
          ((canonicalFinsetList_toFinset_primrec.comp
            (allStringsUpTo_primrec.comp decodeNatCode_primrec)).to_comp.of_eq fun a => rfl))
  obtain ⟨cBridge, hcBridge⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  refine ⟨c₁ + cBridge, fun n => ?_⟩
  have hcode : canonicalUniformCodeOfList (canonicalFinsetList (stringsOfLengthLe n))
      = (codedUniformOn (stringsOfLengthLe n) (stringsOfLengthLe_nonempty n)).code :=
    canonicalUniformCodeOfList_canonicalFinsetList _ (stringsOfLengthLe_nonempty n)
  have hmap := hc₁ (natCode n)
  rw [decodeNatCode_natCode, hcode] at hmap
  unfold plainSetComplexity
  calc plainK V (codedUniformOn (stringsOfLengthLe n) (stringsOfLengthLe_nonempty n)).code
      ≤ KPPlain U (codedUniformOn (stringsOfLengthLe n)
          (stringsOfLengthLe_nonempty n)).code + (cBridge : ENat) := hcBridge _
    _ ≤ (KPPlain U (natCode n) + (c₁ : ENat)) + (cBridge : ENat) := by gcongr
    _ = KPPlain U (natCode n) + ((c₁ + cBridge : ℕ) : ENat) := by push_cast; ring

theorem inPlainDescriptionProfile_ball
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : BitString) (m : ℕ),
      x.length ≤ n → KPPlain U (natCode n) ≤ (m : ENat) →
      InPlainDescriptionProfile V x (m + c) (n + 1) := by
  obtain ⟨c, hc⟩ := plainSetComplexity_ball_le_KPPlain_natCode V U hV hU
  refine ⟨c, fun n x m hlen hm => ?_⟩
  refine ⟨stringsOfLengthLe n, stringsOfLengthLe_nonempty n, ?_, ?_, ?_⟩
  · exact (memStringsOfLengthLe _ _).mpr hlen
  · calc plainSetComplexity V (stringsOfLengthLe n) (stringsOfLengthLe_nonempty n)
      ≤ KPPlain U (natCode n) + c := hc n
    _ ≤ (m : ENat) + c := by gcongr
  · exact cardStringsOfLengthLe_le n

/-- **The budgeted plain corner from a ball model.**  If `x` fits inside the ball
`stringsOfLengthLe n` (all strings of length `≤ n`) for some `n ≥ l(x)` whose
address is simple (`K(n) ≤ m ≤ alpha`) and whose size coordinate `n + 1` still
fits the two-part budget (`n + 1 + m ≤ kx + beta`), then the exact budget-scale
plain corner holds with slack `logSlack c baseBudget` — with **no** bound on the
length of `x`.

Unlike `budgeted_plain_corner_of_simple_length`, the model here is the ball at a
*free* radius `n ≥ l(x)` rather than the exact cube at `l(x)`.  The size
coordinate is therefore `n + 1` instead of `l(x)`, but `n` may be rounded up to a
value whose address complexity `K(n)` is far below `K(l(x))`.  That extra freedom
is what the rounded-length corner exploits to lower the `alpha` demand; the
`n := l(x)` instance recovers a ball analogue of the simple-length corner.

The address hypothesis is stated abstractly through `KPPlain U (natCode n) ≤ m`,
so this leaf is independent of how `m` bounds `K(n)`; no hypothesis on
`plainK V x` is needed, since the corner is driven entirely by the ball address
and the two-part budget. -/
theorem budgeted_plain_corner_of_ball_length
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta n m : ℕ),
      x.length ≤ n →
      KPPlain U (natCode n) ≤ (m : ENat) →
      m ≤ alpha →
      n + 1 + m ≤ kx + beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨cBall, hBall⟩ := inPlainDescriptionProfile_ball V U hV hU
  refine ⟨cBall, fun x kx baseBudget alpha beta n m hlen hm hma hsum => ?_⟩
  have hc : cBall ≤ logSlack cBall baseBudget := by
    unfold logSlack; exact Nat.le_add_left _ _
  exact ⟨m + cBall, n + 1, hBall n x m hlen hm, by omega, by omega⟩

/-- **Rounding a length up to a multiple of a power of two.**  For any target
length `l` and exponent `t`, the ceiling multiple `n = q · 2^t` of `2^t` above
`l` satisfies `l ≤ n < l + 2^t` and `q ≤ l / 2^t + 1`.  This is the pure
arithmetic core of the rounded-length corner: choosing `2^t` close to the
two-part slack `S = kx + beta - l(x)` yields a radius `n ≥ l(x)` within the
budget whose quotient `q ≤ l(x) / 2^t + 1 ≈ l(x)/S` has small binary length, so
the ball address `K(n) ≤ K(q) + K(t) + O(1) ≈ 2·log(l(x)/S) + O(log t)` drops far
below the exact-length demand `K(l(x)) ≈ 2·log l(x)`. -/
theorem exists_rounded_multiple (l t : ℕ) :
    ∃ q : ℕ, l ≤ q * 2 ^ t ∧ q * 2 ^ t < l + 2 ^ t ∧ q ≤ l / 2 ^ t + 1 := by
  have hbpos : 0 < 2 ^ t := pow_pos (by norm_num) t
  refine ⟨(l + 2 ^ t - 1) / 2 ^ t, ?_, ?_, ?_⟩
  · rw [Nat.mul_comm]
    have hdm := Nat.div_add_mod (l + 2 ^ t - 1) (2 ^ t)
    have hmod : (l + 2 ^ t - 1) % 2 ^ t < 2 ^ t := Nat.mod_lt _ hbpos
    omega
  · rw [Nat.mul_comm]
    have hdm := Nat.div_add_mod (l + 2 ^ t - 1) (2 ^ t)
    have hmod : (l + 2 ^ t - 1) % 2 ^ t < 2 ^ t := Nat.mod_lt _ hbpos
    omega
  · calc (l + 2 ^ t - 1) / 2 ^ t ≤ (l + 2 ^ t) / 2 ^ t :=
          Nat.div_le_div_right (by omega)
      _ = l / 2 ^ t + 1 := Nat.add_div_right l hbpos
