import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.CommonInformation.ConditionalIndependence
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.ConditionalComplexity.AverageBounds

/-!
# Token game: board machinery

Exercise 45, part C: counting and shifting on the game board, and the upper bound
`C(C(x) | x) ≤ log |x| + O(1)`.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-! ### Exercise 45, part C: counting and shifting -/

/-! ### Exercise 45, the upper bound `C(C(x) | x) ≤ log |x| + O(1)` -/

/-- For `n ≥ 1` the binary size of `n` is `⌊log₂ n⌋ + 1`. -/
private lemma game_size_eq_log_succ {n : ℕ} (hn : 0 < n) :
    Nat.size n = Nat.log 2 n + 1 := by
  have h1 : Nat.size n ≤ Nat.log 2 n + 1 := by
    rw [Nat.size_le]
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : ¬ (Nat.size n ≤ Nat.log 2 n) := by
    rw [Nat.size_le]
    exact Nat.not_lt.mpr (Nat.pow_log_le_self 2 hn.ne')
  omega

/-- Adding a constant to `n` costs at most a constant number of extra bits. -/
private lemma game_size_bound (n c₀ v : ℕ) (hv : v ≤ n + c₀) :
    Nat.size v ≤ Nat.log 2 n + c₀ + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hmono : Nat.size v ≤ Nat.size c₀ := Nat.size_le_size (by omega)
    have hc : Nat.size c₀ ≤ c₀ := Nat.size_le.mpr Nat.lt_two_pow_self
    have hlog : Nat.log 2 0 = 0 := Nat.log_zero_right 2
    omega
  · have hmul : n + c₀ ≤ n * 2 ^ c₀ := by
      calc n + c₀ ≤ n + n * c₀ := Nat.add_le_add_left (Nat.le_mul_of_pos_left c₀ hn) n
        _ = n * (c₀ + 1) := by ring
        _ ≤ n * 2 ^ c₀ := Nat.mul_le_mul (le_refl n) Nat.lt_two_pow_self
    have hsz : Nat.size (n * 2 ^ c₀) ≤ Nat.size n + c₀ := by
      rw [Nat.size_le, pow_add]
      exact mul_lt_mul_of_pos_right (Nat.lt_size_self n) (by positivity)
    have hchain : Nat.size v ≤ Nat.size n + c₀ :=
      le_trans (Nat.size_le_size (le_trans hv hmul)) hsz
    rw [game_size_eq_log_succ hn] at hchain
    omega

/-- **Exercise 45, upper half.**  `C(x)` is a number of at most `log |x| + O(1)` bits, and
given `x` its length is known, so `C(C(x) | x) ≤ log |x| + O(1)` for every `x`. -/
theorem condK_cVal_le_log_length (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x : BitString,
      condK U (Nat.bits (cVal U x)) x ≤ ((Nat.log 2 x.length + c : ℕ) : ℕ∞) := by
  obtain ⟨c₀, hc₀⟩ := plainK_le_length U hU
  have hv : ∀ x : BitString, cVal U x ≤ x.length + c₀ := by
    intro x
    have h1 : plainK U x = ((cVal U x : ℕ) : ℕ∞) := condK_eq_condCVal hU x []
    have h2 : ((cVal U x : ℕ) : ℕ∞) ≤ ((x.length : ℕ) : ℕ∞) + ((c₀ : ℕ) : ℕ∞) := by
      rw [← h1]; exact hc₀ x
    exact_mod_cast h2
  have hg : Partrec fun q : BitString × BitString =>
      (fun (_ : BitString) (p : BitString) =>
        (Part.some (Nat.bits (decodeFixedWidthNatCode p)) :
          Part BitString)) q.1 q.2 :=
    ((primrec_natBits.comp
        (bitsToNat_primrec.comp
          (Primrec.list_reverse.comp Primrec.snd))).to_comp).partrec
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le U hU
    (fun (_ : BitString) (p : BitString) =>
      (Part.some (Nat.bits (decodeFixedWidthNatCode p)) : Part BitString)) hg
  refine ⟨c₀ + 1 + C, fun x => ?_⟩
  have hp : (fixedWidthNatCode (cVal U x) (Nat.size (cVal U x))).length
      = Nat.size (cVal U x) :=
    fixedWidthNatCode_length (Nat.lt_size_self (cVal U x))
  have hmem : Nat.bits (cVal U x) ∈
      (fun (_ : BitString) (p : BitString) =>
        (Part.some (Nat.bits (decodeFixedWidthNatCode p)) : Part BitString))
        x (fixedWidthNatCode (cVal U x) (Nat.size (cVal U x))) := by
    simp [decodeFixedWidthNatCode_encode]
  have hle := hC x (fixedWidthNatCode (cVal U x) (Nat.size (cVal U x)))
    (Nat.bits (cVal U x)) hmem
  rw [hp] at hle
  refine le_trans hle ?_
  have harith : Nat.size (cVal U x) + C ≤ Nat.log 2 x.length + (c₀ + 1 + C) := by
    have := game_size_bound x.length c₀ (cVal U x) (hv x)
    omega
  calc ((Nat.size (cVal U x) : ℕ) : ℕ∞) + ((C : ℕ) : ℕ∞)
      = ((Nat.size (cVal U x) + C : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ ((Nat.log 2 x.length + (c₀ + 1 + C) : ℕ) : ℕ∞) := by exact_mod_cast harith


/-! ### D1. Monotonicity -/

/-! ### D2. Soundness and completeness of the two black approximations -/

/-! ### D3. Blackened cells of a column, and the row bound -/

/-- The blackened rows of column `x` of board `n` at stage `T`. -/
def gameBlk (c : Code) (n : ℕ) (x : BitString) (T : ℕ) : List ℕ :=
  (List.range n).filter (fun r => gameBlack c n x r T)

/-! ### D4. White never runs out of columns -/

/-! ### D5. Once a token outlives its own complexity, White never moves again -/

/-! ### D6. The process stabilises -/

/-! ### D7. The winning token on each board -/

/-! ### D8. The row enumeration -/

/-- The stage-`T` tokens of row `i` are exactly the strings occupying row `i` on some board
`n < 2 * i + 1` at stage `T`. -/
lemma mem_gameTokens (c : Code) (i T : ℕ) (x : BitString) :
    x ∈ gameTokens c i T ↔
      ∃ n, n < 2 * i + 1 ∧ gameRow c n T = i ∧ gameStr c n T = x := by
  unfold gameTokens
  rw [List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨n, hn, hval⟩
    refine ⟨n, List.mem_range.mp hn, ?_, ?_⟩ <;>
      · by_cases hr : gameRow c n T = i
        · simp only [hr, ite_true] at hval
          first
          | exact hr
          | exact Option.some_inj.mp hval
        · simp only [hr, ite_false] at hval
          exact absurd hval (by simp)
  · rintro ⟨n, hn, hr, hs⟩
    exact ⟨n, List.mem_range.mpr hn, by simp [hr, hs]⟩

/-- Every string in the stage-`T` row enumeration is a token of that row at some earlier stage. -/
lemma mem_gameRowEnum (c : Code) (i : ℕ) : ∀ (T : ℕ) {x : BitString},
    x ∈ gameRowEnum c i T → ∃ T', T' < T ∧ x ∈ gameTokens c i T' := by
  intro T
  induction T with
  | zero => intro x hx; simp [gameRowEnum] at hx
  | succ T ih =>
    intro x hx
    rw [gameRowEnum, List.mem_append] at hx
    rcases hx with h | h
    · obtain ⟨T', hT', hmem⟩ := ih h
      exact ⟨T', by omega, hmem⟩
    · rw [List.mem_filter] at h
      exact ⟨T, by omega, h.1⟩

/-! ### D9. The row enumeration has at most `2 ^ (i + 2)` entries -/

/-- At most `2 ^ (m + 1) - 1` strings have conditional complexity at most `m`. -/
private theorem game_card_condK_le {U : Map} (m : ℕ) (z : BitString) (l : List BitString)
    (hnd : l.Nodup) (hle : ∀ x ∈ l, condK U x z ≤ (m : ℕ∞)) :
    l.length + 1 ≤ 2 ^ (m + 1) := by
  classical
  have hex : ∀ x ∈ l, ∃ p, programLength p ≤ m ∧ produces U p z x := by
    intro x hx
    exact (condK_le_iff U x z m).mp (hle x hx)
  choose! f hf1 hf2 using hex
  have hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
    intro x hx y hy hxy
    have h1 : x ∈ U (f x, z) := hf2 x hx
    have h2 : y ∈ U (f x, z) := by rw [hxy]; exact hf2 y hy
    exact Part.mem_unique h1 h2
  have hnodup : (l.map f).Nodup := List.Nodup.map_on hinj hnd
  have hsub : l.map f ⊆ boundedPrograms m := by
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact (mem_boundedPrograms_iff _ m).mpr (hf1 x hx)
  have hlen := (List.subperm_of_subset hnodup hsub).length_le
  rw [List.length_map] at hlen
  have hb := length_boundedPrograms_succ_eq m
  omega

private lemma gameDead_mono (c : Code) (x : BitString) (r : ℕ) {T T' : ℕ} (h : T ≤ T')
    (hd : gameDead c x r T = true) : gameDead c x r T' = true := by
  unfold gameDead at hd ⊢
  rw [Bool.and_eq_true] at hd ⊢
  exact ⟨hd.1, hitAt_mono c (r - 1) h x [] hd.2⟩

private lemma gameBlack_mono (c : Code) (n : ℕ) (x : BitString) (i : ℕ) {T T' : ℕ} (h : T ≤ T')
    (hb : gameBlack c n x i T = true) : gameBlack c n x i T' = true :=
  hitAt_mono c _ h _ _ hb

private lemma gameFree_subset (c : Code) (n : ℕ) (x : BitString) {T T' : ℕ} (h : T ≤ T')
    {r : ℕ} (hr : r ∈ gameFree c n x T') : r ∈ gameFree c n x T := by
  unfold gameFree at hr ⊢
  rw [List.mem_filter] at hr ⊢
  refine ⟨hr.1, ?_⟩
  have h2 := hr.2
  rw [Bool.not_eq_true'] at h2 ⊢
  by_contra hb
  rw [Bool.not_eq_false] at hb
  exact absurd (gameBlack_mono c n x r h hb) (by rw [h2]; simp)

private lemma gameTop_antitone (c : Code) (n : ℕ) (x : BitString) {T T' : ℕ} (h : T ≤ T') :
    gameTop c n x T' ≤ gameTop c n x T :=
  gameMax_mono (fun _ ha => gameFree_subset c n x h ha)

private lemma gameFree_mem_lt {c : Code} {n : ℕ} {x : BitString} {T r : ℕ}
    (hr : r ∈ gameFree c n x T) : r < n := by
  unfold gameFree at hr
  rw [List.mem_filter] at hr
  exact List.mem_range.mp hr.1

private lemma gameTop_le_pred (c : Code) (n : ℕ) (x : BitString) (T : ℕ) :
    gameTop c n x T ≤ n - 1 := by
  unfold gameTop
  rcases eq_or_ne (gameFree c n x T) [] with h | h
  · simp [h, gameMax]
  · have := gameFree_mem_lt (gameMax_mem h)
    omega

private lemma gameWCol_succ (c : Code) (n T : ℕ) :
    gameWCol c n (T + 1) = gameWCol c n T ∨ gameWCol c n (T + 1) = gameWCol c n T + 1 := by
  rw [gameWCol]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

private lemma gameWCol_mono (c : Code) (n : ℕ) {T T' : ℕ} (h : T ≤ T') :
    gameWCol c n T ≤ gameWCol c n T' := by
  induction T' with
  | zero =>
    have hT : T = 0 := Nat.le_zero.mp h
    subst hT; exact le_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge T (k + 1) with hk | hk
    · have h1 : T ≤ k := Nat.lt_succ_iff.mp hk
      have h2 := ih h1
      rcases gameWCol_succ c n k with hs | hs <;> omega
    · have hT : T = k + 1 := le_antisymm h hk
      subst hT; exact le_rfl

private lemma gameDead_sound {U : Map} {c : Code} (hc : IsCodeFor c U) {x : BitString} {r T : ℕ}
    (h : gameDead c x r T = true) : 0 < r ∧ plainK U x ≤ ((r - 1 : ℕ) : ℕ∞) := by
  unfold gameDead at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hr, hhit⟩ := h
  obtain ⟨p, hp, hrun⟩ := (hitAt_iff c (r - 1) T x []).mp hhit
  refine ⟨hr, ?_⟩
  have hprod : produces U p [] x := runOutC_sound hc hrun
  have hlen : p.length ≤ r - 1 := (mem_boundedPrograms_iff p (r - 1)).mp hp
  exact (condK_le_iff U x [] (r - 1)).mpr ⟨p, hlen, hprod⟩

private lemma gameDead_complete {U : Map} {c : Code} (hc : IsCodeFor c U) {x : BitString} {r : ℕ}
    (hr : 0 < r) (h : plainK U x ≤ ((r - 1 : ℕ) : ℕ∞)) : ∃ T, gameDead c x r T = true := by
  obtain ⟨p, hlen, hprod⟩ := (condK_le_iff U x [] (r - 1)).mp h
  obtain ⟨T, hT⟩ := runOutC_complete hc hprod
  refine ⟨T, ?_⟩
  unfold gameDead
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hr, (hitAt_iff c (r - 1) T x []).mpr ⟨p, ?_, hT⟩⟩
  exact (mem_boundedPrograms_iff p (r - 1)).mpr hlen

private lemma gameBlack_sound {U : Map} {c : Code} (hc : IsCodeFor c U) {n : ℕ} {x : BitString}
    {i T : ℕ} (h : gameBlack c n x i T = true) :
    condK U (Nat.bits i) x ≤ ((gameLog n - 2 : ℕ) : ℕ∞) := by
  unfold gameBlack at h
  obtain ⟨p, hp, hrun⟩ := (hitAt_iff c (gameLog n - 2) T (Nat.bits i) x).mp h
  exact (condK_le_iff U (Nat.bits i) x (gameLog n - 2)).mpr
    ⟨p, (mem_boundedPrograms_iff p _).mp hp, runOutC_sound hc hrun⟩

private lemma gameBlack_complete {U : Map} {c : Code} (hc : IsCodeFor c U) {n : ℕ} {x : BitString}
    {i : ℕ} (h : condK U (Nat.bits i) x ≤ ((gameLog n - 2 : ℕ) : ℕ∞)) :
    ∃ T, gameBlack c n x i T = true := by
  obtain ⟨p, hlen, hprod⟩ := (condK_le_iff U (Nat.bits i) x (gameLog n - 2)).mp h
  obtain ⟨T, hT⟩ := runOutC_complete hc hprod
  exact ⟨T, (hitAt_iff c (gameLog n - 2) T (Nat.bits i) x).mpr
    ⟨p, (mem_boundedPrograms_iff p _).mpr hlen, hT⟩⟩

private lemma game_filter_length_add {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases h : p a <;> simp [h] <;> omega

private lemma game_pow_log_le {n : ℕ} (hL : 2 ≤ gameLog n) : 2 ^ gameLog n ≤ n ∧ 4 ≤ n := by
  rw [gameLog_eq] at hL ⊢
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hL
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have h2 : (4 : ℕ) = 2 ^ 2 := by norm_num
  exact ⟨h1, by rw [h2]; exact le_trans (Nat.pow_le_pow_right (by norm_num) hL) h1⟩

private lemma gameBlk_add_free (c : Code) (n : ℕ) (x : BitString) (T : ℕ) :
    (gameBlk c n x T).length + (gameFree c n x T).length = n := by
  have h := game_filter_length_add (List.range n) (fun r => gameBlack c n x r T)
  simpa [gameBlk, gameFree, List.length_range] using h

private lemma game_black_count {U : Map} {c : Code} (hc : IsCodeFor c U) (n : ℕ) (x : BitString)
    (T : ℕ) (hL : 2 ≤ gameLog n) :
    (gameBlk c n x T).length + 1 ≤ 2 ^ (gameLog n - 1) := by
  have hnd : (gameBlk c n x T).Nodup := (List.nodup_range).filter _
  have hmapnd : ((gameBlk c n x T).map Nat.bits).Nodup := hnd.map natBits_injective
  have hle : ∀ y ∈ (gameBlk c n x T).map Nat.bits,
      condK U y x ≤ ((gameLog n - 2 : ℕ) : ℕ∞) := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [gameBlk, List.mem_filter] at hi
    exact gameBlack_sound hc hi.2
  have h := game_card_condK_le (gameLog n - 2) x _ hmapnd hle
  rw [List.length_map] at h
  have harith : gameLog n - 2 + 1 = gameLog n - 1 := by omega
  rwa [harith] at h

private lemma gameFree_ne_nil {U : Map} {c : Code} (hc : IsCodeFor c U) (n : ℕ) (x : BitString)
    (T : ℕ) (hL : 2 ≤ gameLog n) : gameFree c n x T ≠ [] := by
  intro h
  have h1 := game_black_count hc n x T hL
  have h2 := gameBlk_add_free c n x T
  rw [h] at h2
  simp only [List.length_nil, Nat.add_zero] at h2
  obtain ⟨hpow, hn4⟩ := game_pow_log_le hL
  have h3 : 2 ^ (gameLog n - 1) ≤ 2 ^ gameLog n :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private lemma gameTop_mem_free {U : Map} {c : Code} (hc : IsCodeFor c U) (n : ℕ) (x : BitString)
    (T : ℕ) (hL : 2 ≤ gameLog n) : gameTop c n x T ∈ gameFree c n x T :=
  gameMax_mem (gameFree_ne_nil hc n x T hL)

private lemma gameTop_not_black {U : Map} {c : Code} (hc : IsCodeFor c U) (n : ℕ) (x : BitString)
    (T : ℕ) (hL : 2 ≤ gameLog n) : gameBlack c n x (gameTop c n x T) T = false := by
  have h := gameTop_mem_free hc n x T hL
  rw [gameFree, List.mem_filter] at h
  have h2 := h.2
  rw [Bool.not_eq_true'] at h2
  exact h2

/-- On a board with `gameLog n ≥ 2`, the top blackened row of every column is at least `n / 2`:
`n ≤ 2 * gameTop c n x T`.  SUV Exercise 45. -/
lemma game_row_bound {U : Map} {c : Code} (hc : IsCodeFor c U) (n : ℕ) (x : BitString)
    (T : ℕ) (hL : 2 ≤ gameLog n) : n ≤ 2 * gameTop c n x T := by
  set M := gameTop c n x T with hM
  have hMlt : M < n := gameFree_mem_lt (gameTop_mem_free hc n x T hL)
  set A := (List.range (n - 1 - M)).map (fun k => M + 1 + k) with hA
  have hAnd : A.Nodup := (List.nodup_range).map (fun a b hab => by omega)
  have hsub : A ⊆ gameBlk c n x T := by
    intro r hr
    rw [hA, List.mem_map] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    have hklt : k < n - 1 - M := List.mem_range.mp hk
    rw [gameBlk, List.mem_filter]
    refine ⟨List.mem_range.mpr (by omega), ?_⟩
    by_contra hb
    rw [Bool.not_eq_true] at hb
    have hmem : M + 1 + k ∈ gameFree c n x T := by
      rw [gameFree, List.mem_filter]
      exact ⟨List.mem_range.mpr (by omega), by rw [hb]; rfl⟩
    have hle2 : M + 1 + k ≤ M := gameMax_le_of_mem hmem
    omega
  have hlen : A.length ≤ (gameBlk c n x T).length := (hAnd.subperm hsub).length_le
  rw [hA, List.length_map, List.length_range] at hlen
  have hcount := game_black_count hc n x T hL
  obtain ⟨hpow, hn4⟩ := game_pow_log_le hL
  have hsplit : 2 * 2 ^ (gameLog n - 1) = 2 ^ gameLog n := by
    rw [← pow_succ']
    congr 1
    omega
  omega

private lemma gameCol_mem (n j : ℕ) (hj : j < 2 ^ n) : gameCol n j ∈ allStrings n := by
  have hlen : j < (allStrings n).length := by rw [length_allStrings]; exact hj
  unfold gameCol
  rw [List.getD_eq_getElem _ _ hlen]
  exact List.getElem_mem hlen

private lemma gameCol_length (n j : ℕ) (hj : j < 2 ^ n) : (gameCol n j).length = n :=
  (mem_allStrings n _).mp (gameCol_mem n j hj)

private lemma gameCol_inj (n : ℕ) {j k : ℕ} (hj : j < 2 ^ n) (hk : k < 2 ^ n)
    (h : gameCol n j = gameCol n k) : j = k := by
  have hlj : j < (allStrings n).length := by rw [length_allStrings]; exact hj
  have hlk : k < (allStrings n).length := by rw [length_allStrings]; exact hk
  unfold gameCol at h
  rw [List.getD_eq_getElem _ _ hlj, List.getD_eq_getElem _ _ hlk] at h
  exact (List.Nodup.getElem_inj_iff (allStrings_nodup n)).mp h

private lemma gameWCol_bound {U : Map} {c : Code} (hc : IsCodeFor c U) (n T : ℕ) :
    gameWCol c n T < 2 ^ n ∧
      ∀ j < gameWCol c n T, plainK U (gameCol n j) ≤ ((n - 2 : ℕ) : ℕ∞) := by
  induction T with
  | zero =>
    refine ⟨Nat.two_pow_pos n, ?_⟩
    intro j hj
    simp only [gameWCol, Nat.not_lt_zero] at hj
  | succ T ih =>
    obtain ⟨hlt, hall⟩ := ih
    rw [gameWCol]
    split
    · rename_i hdead
      obtain ⟨hr0, hpk⟩ := gameDead_sound hc hdead
      have hrle := gameTop_le_pred c n (gameCol n (gameWCol c n T)) T
      have hn2 : 2 ≤ n := by omega
      have hnew : plainK U (gameCol n (gameWCol c n T)) ≤ ((n - 2 : ℕ) : ℕ∞) := by
        refine le_trans hpk ?_
        have : gameTop c n (gameCol n (gameWCol c n T)) T - 1 ≤ n - 2 := by omega
        exact_mod_cast this
      have hall' : ∀ j < gameWCol c n T + 1,
          plainK U (gameCol n j) ≤ ((n - 2 : ℕ) : ℕ∞) := by
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact hall j h
        · rw [h]; exact hnew
      refine ⟨?_, hall'⟩
      have hLnd : ((List.range (gameWCol c n T + 1)).map (gameCol n)).Nodup := by
        refine (List.nodup_range).map_on ?_
        intro a ha b hb hab
        have ha' : a < 2 ^ n := lt_of_lt_of_le (by
          have := List.mem_range.mp ha; omega) (by omega)
        have hb' : b < 2 ^ n := lt_of_lt_of_le (by
          have := List.mem_range.mp hb; omega) (by omega)
        exact gameCol_inj n ha' hb' hab
      have hmem : ∀ x ∈ (List.range (gameWCol c n T + 1)).map (gameCol n),
          condK U x [] ≤ (((n - 2 : ℕ)) : ℕ∞) := by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        exact hall' j (List.mem_range.mp hj)
      have hcard := game_card_condK_le (n - 2) [] _ hLnd hmem
      rw [List.length_map, List.length_range] at hcard
      have hpow : 2 ^ (n - 2 + 1) < 2 ^ n :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    · exact ⟨hlt, hall⟩

/-- The column White occupies on board `n` at stage `T` is one of the `2 ^ n` columns. -/
lemma gameWCol_lt {U : Map} {c : Code} (hc : IsCodeFor c U) (n T : ℕ) :
    gameWCol c n T < 2 ^ n := (gameWCol_bound hc n T).1

private lemma gameStr_length {U : Map} {c : Code} (hc : IsCodeFor c U) (n T : ℕ) :
    (gameStr c n T).length = n := gameCol_length n _ (gameWCol_lt hc n T)

private lemma gameWCol_stable {U : Map} {c : Code} (hc : IsCodeFor c U) (n T : ℕ)
    (h : ((gameRow c n T : ℕ) : ℕ∞) ≤ plainK U (gameStr c n T)) :
    ∀ T', T ≤ T' → gameWCol c n T' = gameWCol c n T := by
  intro T'
  induction T' with
  | zero => intro hT'; rw [Nat.le_zero.mp hT']
  | succ k ih =>
    intro hT'
    rcases Nat.lt_or_ge T (k + 1) with hk | hk
    · have hTk : T ≤ k := Nat.lt_succ_iff.mp hk
      have ihk : gameWCol c n k = gameWCol c n T := ih hTk
      have hstr : gameStr c n k = gameStr c n T := by rw [gameStr, ihk, gameStr]
      have hnotdead : gameDead c (gameStr c n k) (gameRow c n k) (k + 1) = false := by
        by_contra hd
        rw [Bool.not_eq_false] at hd
        obtain ⟨hr0, hpk⟩ := gameDead_sound hc hd
        rw [hstr] at hpk
        have htop : gameRow c n k ≤ gameRow c n T := by
          rw [gameRow, gameRow, hstr]
          exact gameTop_antitone c n (gameStr c n T) hTk
        have hchain : ((gameRow c n T : ℕ) : ℕ∞) ≤ (((gameRow c n k - 1 : ℕ)) : ℕ∞) :=
          le_trans h hpk
        have : gameRow c n T ≤ gameRow c n k - 1 := by exact_mod_cast hchain
        omega
      rw [gameWCol, ite_eq_right (by rw [show gameCol n (gameWCol c n k) = gameStr c n k from rfl,
        show gameTop c n (gameStr c n k) k = gameRow c n k from rfl, hnotdead]; simp), ihk]
    · rw [le_antisymm hT' hk]

private lemma game_exists_stable_col {U : Map} {c : Code} (hc : IsCodeFor c U) (n : ℕ) :
    ∃ T0 : ℕ, ∀ T, T0 ≤ T → gameWCol c n T = gameWCol c n T0 := by
  obtain ⟨T0, hT0⟩ : ∃ T0, ∀ T, gameWCol c n T ≤ gameWCol c n T0 := by
    obtain ⟨_, ⟨t0, rfl⟩, hmax⟩ :=
      Set.exists_max_image (Set.range fun T => gameWCol c n T) id
        (Set.finite_iff_bddAbove.mpr ⟨2 ^ n, Set.forall_mem_range.mpr
          (fun T => le_of_lt (gameWCol_lt hc n T))⟩) ⟨_, ⟨0, rfl⟩⟩
    exact ⟨t0, fun T => hmax _ ⟨T, rfl⟩⟩
  exact ⟨T0, fun T hT => le_antisymm (hT0 T) (gameWCol_mono c n hT)⟩

private lemma game_exists_stable_top (c : Code) (n : ℕ) (x : BitString) :
    ∃ T1 : ℕ, ∀ T, T1 ≤ T → gameTop c n x T = gameTop c n x T1 := by
  have hne : {v : ℕ | ∃ T, gameTop c n x T = v}.Nonempty := ⟨gameTop c n x 0, 0, rfl⟩
  obtain ⟨T1, hT1⟩ : sInf {v : ℕ | ∃ T, gameTop c n x T = v} ∈
      {v : ℕ | ∃ T, gameTop c n x T = v} := Nat.sInf_mem hne
  refine ⟨T1, fun T hT => le_antisymm (gameTop_antitone c n x hT) ?_⟩
  rw [hT1]
  exact Nat.sInf_le ⟨T, rfl⟩

/-- On each board `n` with `gameLog n ≥ 2` the game stabilises on a string `x` of length `n` and
a row `R` with `n ≤ 2 * R`, whose complexity is at least `R` while `R` itself cannot be
described from `x` in `gameLog n - 2` bits.  SUV Exercise 45, lower half. -/
theorem exists_game_winner {U : Map} {c : Code} (hc : IsCodeFor c U) (n : ℕ) (hL : 2 ≤ gameLog n) :
    ∃ (x : BitString) (R T0 : ℕ), x.length = n ∧ n ≤ 2 * R ∧
      ((R : ℕ) : ℕ∞) ≤ plainK U x ∧
      ¬ (condK U (Nat.bits R) x ≤ ((gameLog n - 2 : ℕ) : ℕ∞)) ∧
      (∀ T, T0 ≤ T → gameStr c n T = x ∧ gameRow c n T = R) := by
  obtain ⟨T0, hT0⟩ := game_exists_stable_col hc n
  obtain ⟨T1, hT1⟩ := game_exists_stable_top c n (gameCol n (gameWCol c n T0))
  refine ⟨gameCol n (gameWCol c n T0),
    gameTop c n (gameCol n (gameWCol c n T0)) (max T0 T1), max T0 T1,
    gameCol_length n _ (gameWCol_lt hc n T0), ?_, ?_, ?_, ?_⟩
  · exact game_row_bound hc n _ (max T0 T1) hL
  · -- the token is alive : no black token strictly below
    by_contra hlt
    rw [not_le] at hlt
    have hne : plainK U (gameCol n (gameWCol c n T0)) ≠ ⊤ := ne_top_of_lt hlt
    have hcoe : plainK U (gameCol n (gameWCol c n T0))
        = (((plainK U (gameCol n (gameWCol c n T0))).toNat : ℕ) : ℕ∞) :=
      (ENat.natCast_toNat hne).symm
    rw [hcoe] at hlt
    have hltn : (plainK U (gameCol n (gameWCol c n T0))).toNat <
        gameTop c n (gameCol n (gameWCol c n T0)) (max T0 T1) := by exact_mod_cast hlt
    obtain ⟨T, hT⟩ := gameDead_complete hc (r := gameTop c n (gameCol n (gameWCol c n T0))
      (max T0 T1)) (by omega) (by rw [hcoe]; exact_mod_cast (by omega :
        (plainK U (gameCol n (gameWCol c n T0))).toNat ≤
          gameTop c n (gameCol n (gameWCol c n T0)) (max T0 T1) - 1))
    -- but White never moved after `max T0 T1`
    set S := max (max T0 T1) T with hS
    have hcolS : gameWCol c n S = gameWCol c n T0 :=
      hT0 S (le_trans (le_max_left _ _) (le_max_left _ _))
    have hcolS1 : gameWCol c n (S + 1) = gameWCol c n T0 :=
      hT0 (S + 1) (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (Nat.le_succ S))
    have htopS : gameTop c n (gameCol n (gameWCol c n T0)) S
        = gameTop c n (gameCol n (gameWCol c n T0)) (max T0 T1) := by
      rw [hT1 S (le_trans (le_max_right _ _) (le_max_left _ _)),
        hT1 (max T0 T1) (le_max_right _ _)]
    have hdeadS : gameDead c (gameCol n (gameWCol c n T0))
        (gameTop c n (gameCol n (gameWCol c n T0)) (max T0 T1)) (S + 1) = true :=
      gameDead_mono c _ _ (le_trans (le_max_right (max T0 T1) T) (Nat.le_succ S)) hT
    have hmove : gameWCol c n (S + 1) = gameWCol c n S + 1 := by
      rw [gameWCol, hcolS, ite_eq_left (by rw [htopS]; exact hdeadS)]
    omega
  · -- the token is alive : the cell is not blackened
    intro hb
    obtain ⟨T, hT⟩ := gameBlack_complete (n := n) hc hb
    have hbig : gameBlack c n (gameCol n (gameWCol c n T0))
        (gameTop c n (gameCol n (gameWCol c n T0)) (max T0 T1)) (max (max T0 T1) T) = true :=
      gameBlack_mono c n _ _ (le_max_right (max T0 T1) T) hT
    have htopS : gameTop c n (gameCol n (gameWCol c n T0)) (max (max T0 T1) T)
        = gameTop c n (gameCol n (gameWCol c n T0)) (max T0 T1) := by
      rw [hT1 _ (le_trans (le_max_right _ _) (le_max_left _ _)),
        hT1 (max T0 T1) (le_max_right _ _)]
    have hfree := gameTop_not_black hc n (gameCol n (gameWCol c n T0)) (max (max T0 T1) T) hL
    rw [htopS, hbig] at hfree
    exact Bool.noConfusion hfree
  · intro T hT
    have h1 : gameWCol c n T = gameWCol c n T0 := hT0 T (le_trans (le_max_left _ _) hT)
    have hs : gameStr c n T = gameCol n (gameWCol c n T0) := by rw [gameStr, h1]
    refine ⟨hs, ?_⟩
    rw [gameRow, hs, hT1 T (le_trans (le_max_right _ _) hT),
      hT1 (max T0 T1) (le_max_right _ _)]

private lemma gameTokens_nodup (c : Code) (i T : ℕ) : (gameTokens c i T).Nodup :=
  List.nodup_dedup _

private lemma gameRowEnum_nodup (c : Code) (i T : ℕ) : (gameRowEnum c i T).Nodup := by
  induction T with
  | zero => simp [gameRowEnum]
  | succ T ih =>
    rw [gameRowEnum]
    refine List.nodup_append.mpr ⟨ih, (gameTokens_nodup c i T).filter _, ?_⟩
    intro a ha b hb
    rw [List.mem_filter] at hb
    have h2 := hb.2
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h2
    intro hab
    exact h2 (hab ▸ ha)

private lemma game_lt_to_le {v : ℕ∞} {i : ℕ} (h : v < (i : ℕ∞)) : v ≤ ((i - 1 : ℕ) : ℕ∞) := by
  have hne : v ≠ ⊤ := ne_top_of_lt h
  have hcoe : v = ((v.toNat : ℕ) : ℕ∞) := (ENat.natCast_toNat hne).symm
  rw [hcoe] at h ⊢
  have hlt : v.toNat < i := by exact_mod_cast h
  exact_mod_cast (by omega : v.toNat ≤ i - 1)

private lemma game_second_unique {U : Map} {c : Code} (hc : IsCodeFor c U) (n Tx Ty : ℕ)
    (hx : ((gameRow c n Tx : ℕ) : ℕ∞) ≤ plainK U (gameStr c n Tx))
    (hy : ((gameRow c n Ty : ℕ) : ℕ∞) ≤ plainK U (gameStr c n Ty)) :
    gameStr c n Tx = gameStr c n Ty := by
  rcases le_total Tx Ty with h | h
  · have hcol := gameWCol_stable hc n Tx hx Ty h
    rw [gameStr, gameStr, hcol]
  · have hcol := gameWCol_stable hc n Ty hy Tx h
    rw [gameStr, gameStr, hcol]

open Classical in
/-- Row `i` is enumerated by at most `2 ^ (i + 2)` strings, which is what makes each white token
describable in `i + 2` bits given the row. -/
theorem gameRowEnum_length {U : Map} {c : Code} (hc : IsCodeFor c U) (i T : ℕ) :
    (gameRowEnum c i T).length ≤ 2 ^ (i + 2) := by
  classical
  have hnd := gameRowEnum_nodup c i T
  have hsplit := game_filter_length_add (gameRowEnum c i T)
    (fun x => decide (plainK U x < (i : ℕ∞)))
  -- the compressible half
  have hlow : ((gameRowEnum c i T).filter
      (fun x => decide (plainK U x < (i : ℕ∞)))).length ≤ 2 ^ i := by
    rcases Nat.eq_zero_or_pos i with hi0 | hi
    · have hempty : (gameRowEnum c i T).filter
          (fun x => decide (plainK U x < (i : ℕ∞))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x _
        simp only [decide_eq_true_eq, hi0, Nat.cast_zero, not_lt]
        exact bot_le
      rw [hempty]
      simp
    · have hcond : ∀ x ∈ (gameRowEnum c i T).filter
          (fun x => decide (plainK U x < (i : ℕ∞))), condK U x [] ≤ (((i - 1 : ℕ)) : ℕ∞) := by
        intro x hx
        rw [List.mem_filter, decide_eq_true_eq] at hx
        exact game_lt_to_le hx.2
      have hcard := game_card_condK_le (i - 1) [] _ (hnd.filter _) hcond
      have hpow : i - 1 + 1 = i := by omega
      rw [hpow] at hcard
      omega
  -- the incompressible half
  have hhigh : ((gameRowEnum c i T).filter
      (fun x => !decide (plainK U x < (i : ℕ∞)))).length ≤ 2 * i + 1 := by
    set l2 := (gameRowEnum c i T).filter (fun x => !decide (plainK U x < (i : ℕ∞))) with hl2
    have hkey : ∀ x ∈ l2, ∃ Tx n, n < 2 * i + 1 ∧ gameRow c n Tx = i ∧
        gameStr c n Tx = x ∧ ((gameRow c n Tx : ℕ) : ℕ∞) ≤ plainK U (gameStr c n Tx) := by
      intro x hx
      rw [hl2, List.mem_filter] at hx
      obtain ⟨Tx, _, hmem⟩ := mem_gameRowEnum c i T hx.1
      obtain ⟨n, hn, hr, hs⟩ := (mem_gameTokens c i Tx x).mp hmem
      refine ⟨Tx, n, hn, hr, hs, ?_⟩
      rw [hr, hs]
      have h2 := hx.2
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at h2
      exact h2
    have hlenx : ∀ x ∈ l2, x.length < 2 * i + 1 := by
      intro x hx
      obtain ⟨Tx, n, hn, _, hs, _⟩ := hkey x hx
      rw [← hs, gameStr_length hc]
      exact hn
    have hinj : ∀ x ∈ l2, ∀ y ∈ l2, x.length = y.length → x = y := by
      intro x hx y hy hlen
      obtain ⟨Tx, nx, _, _, hsx, hax⟩ := hkey x hx
      obtain ⟨Ty, ny, _, _, hsy, hay⟩ := hkey y hy
      have hnx : nx = x.length := by rw [← hsx, gameStr_length hc]
      have hny : ny = y.length := by rw [← hsy, gameStr_length hc]
      have hnn : nx = ny := by rw [hnx, hny, hlen]
      subst hnn
      rw [← hsx, ← hsy]
      exact game_second_unique hc nx Tx Ty hax hay
    have hmapnd : (l2.map List.length).Nodup :=
      ((hnd.filter _).map_on hinj)
    have hsub : l2.map List.length ⊆ List.range (2 * i + 1) := by
      intro m hm
      rw [List.mem_map] at hm
      obtain ⟨x, hx, rfl⟩ := hm
      exact List.mem_range.mpr (hlenx x hx)
    have hle := (hmapnd.subperm hsub).length_le
    rw [List.length_map, List.length_range] at hle
    exact hle
  have h4 : 2 ^ (i + 2) = 4 * 2 ^ i := by ring
  have hi2 : i < 2 ^ i := Nat.lt_two_pow_self
  omega

end Kolmogorov
