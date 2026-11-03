/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Mean.Enumeration
import KolmogorovMathlib.Solomonoff.Domination.UniformFamily
import KolmogorovMathlib.Solomonoff.Domination.IndexedMeasures

/-!
# Prefix-free sanitation of pair-code requests

The existential family is required to be uniformly lower semicomputable even on invalid
numeric codes. Finite prefix-free budget tests sanitize the requests; valid pairs keep
the mean-tree value. No test for whether a numeric code is valid enters the interface.
Blueprint nodes: `exp:mean-sanitize`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-! ## Primitive recursive mass brackets -/

/-- A lower dyadic request rescaled to the current stage. -/
private def lowerBracketTerm (e s : ℕ) (x : BitString) (k : ℕ) : ℕ :=
  match measureIndexRequest e s k x with
  | some a => min (2^s) ((a - 1) * 2^(s - k))
  | none => 0

/-- An upper dyadic request rescaled to the current stage. -/
private def upperBracketTerm (e s : ℕ) (x : BitString) (k : ℕ) : ℕ :=
  match measureIndexRequest e s k x with
  | some a => min (2^s) ((a + 1) * 2^(s - k))
  | none => 2^s

/-- The maximum certified lower numerator at a stage. -/
private def lowerBracketNumerator (e s : ℕ) (x : BitString) : ℕ :=
  (List.range (s + 1)).foldl (fun acc k => max acc (lowerBracketTerm e s x k)) 0

/-- The minimum certified upper numerator at a stage. -/
private def upperBracketNumerator (e s : ℕ) (x : BitString) : ℕ :=
  (List.range (s + 1)).foldl (fun acc k => min acc (upperBracketTerm e s x k)) (2^s)

/-- Rescaling a dyadic numerator preserves its value. -/
private lemma dyadic_rescale {n k s : ℕ} (hk : k ≤ s) :
    dyadicValue (n * 2^(s - k)) s = dyadicValue n k := by
  have h := dyadicValue_two_pow_mul_add n k (s - k)
  rwa [Nat.add_sub_cancel' hk, mul_comm] at h

/-- A range maximum equals a fold over the same range. -/
private lemma range_fold_max {s n : ℕ} (f : ℕ → ℕ) :
    dyadicValue ((List.range n).foldl (fun acc k => max acc (f k)) 0) s =
    (Finset.range n).sup fun k => dyadicValue (f k) s := by
  induction n with
  | zero => simp [dyadicValue]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        (monotone_dyadicValue_num s).map_max, ih, Finset.range_add_one, Finset.sup_insert, sup_comm]

/-- A range minimum equals a fold over the same range. -/
private lemma range_fold_min {s n c : ℕ} (f : ℕ → ℕ) :
    dyadicValue ((List.range n).foldl (fun acc k => min acc (f k)) c) s =
    min (dyadicValue c s) ((Finset.range n).inf fun k => dyadicValue (f k) s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        (monotone_dyadicValue_num s).map_min, ih, Finset.range_add_one, Finset.inf_insert,
        min_assoc]
    exact congrArg _ (min_comm _ _)

/-- The bounded numeric measure request is primitive recursive. -/
private lemma request_primrec :
    Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => measureIndexRequest a.1.1 a.1.2.1 a.2 a.1.2.2) := by
  have h1 : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => a.1.2.1) := Primrec.fst.comp
      (Primrec.snd.comp Primrec.fst)
  have h2 : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => Denumerable.ofNat Nat.Partrec.Code a.1.1) :=
    (Primrec.ofNat _).comp (Primrec.fst.comp Primrec.fst)
  have h3 : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => Encodable.encode (a.1.2.2, a.2)) :=
    Primrec.encode.comp ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  exact Nat.Partrec.Code.primrec_evaln.comp ((h1.pair h2).pair h3)

/-- A rescaled bracket term is primitive recursive. -/
private lemma bracketTerm_primrec (c : ℕ → ℕ → ℕ) (hc : Primrec₂ c) (d : ℕ → ℕ) (hd : Primrec d) :
    Primrec (fun a : (ℕ × ℕ × BitString) × ℕ =>
      match measureIndexRequest a.1.1 a.1.2.1 a.2 a.1.2.2 with
      | some n => min (2^a.1.2.1) (c n 0 * 2^(a.1.2.1 - a.2))
      | none => d (2^a.1.2.1)) := by
  have hs : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => a.1.2.1) := Primrec.fst.comp
      (Primrec.snd.comp Primrec.fst)
  have hpow : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => 2^a.1.2.1) := primrec_two_pow_aux.comp hs
  have hk : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => a.2) := Primrec.snd
  have hk_sub : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => a.1.2.1 - a.2) :=
      Primrec.nat_sub.comp hs hk
  have hpow2 : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => 2^(a.1.2.1 - a.2)) :=
      primrec_two_pow_aux.comp hk_sub
  have hc_app : Primrec₂ (fun (a : (ℕ × ℕ × BitString) × ℕ) (n : ℕ) => c n 0) :=
    hc.comp (Primrec.snd (α := (ℕ × ℕ × BitString) × ℕ) (β := ℕ)) (Primrec.const 0)
  have hmul : Primrec₂ (fun (a : (ℕ × ℕ × BitString) × ℕ) (n : ℕ) => c n 0 * 2^(a.1.2.1 - a.2)) :=
    Primrec.nat_mul.comp hc_app (hpow2.comp (Primrec.fst (α := (ℕ × ℕ × BitString) × ℕ) (β := ℕ)))
  have hpow_fst : Primrec₂ (fun (a : (ℕ × ℕ × BitString) × ℕ) (n : ℕ) => 2^a.1.2.1) :=
    hpow.comp (Primrec.fst (α := (ℕ × ℕ × BitString) × ℕ) (β := ℕ))
  have hg : Primrec₂ (fun (a : (ℕ × ℕ × BitString) × ℕ) (n : ℕ) => min (2^a.1.2.1) (c n 0
      * 2^(a.1.2.1 - a.2))) :=
    Primrec.nat_min.comp hpow_fst hmul
  have h_none : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => d (2^a.1.2.1)) := hd.comp hpow
  exact Primrec.option_casesOn request_primrec h_none hg |>.of_eq fun a => by
    cases measureIndexRequest a.1.1 a.1.2.1 a.2 a.1.2.2 <;> rfl

/-- Lower bracket terms are primitive recursive. -/
private lemma lowerBracketTerm_primrec :
    Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => lowerBracketTerm a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  have hc : Primrec₂ (fun n (_ : ℕ) => n - 1) := Primrec.nat_sub.comp (Primrec.fst (α :=
      ℕ) (β := ℕ)) (Primrec.const 1)
  have hd : Primrec (fun (_ : ℕ) => 0) := Primrec.const 0
  exact (bracketTerm_primrec (fun n _ => n - 1) hc (fun _ => 0) hd).of_eq fun a => by
    unfold lowerBracketTerm; cases measureIndexRequest a.1.1 a.1.2.1 a.2 a.1.2.2 <;> rfl

/-- Upper bracket terms are primitive recursive. -/
private lemma upperBracketTerm_primrec :
    Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => upperBracketTerm a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  have hc : Primrec₂ (fun n (_ : ℕ) => n + 1) := Primrec.succ.comp (Primrec.fst (α := ℕ) (β := ℕ))
  have hd : Primrec (fun m : ℕ => m) := Primrec.id
  exact (bracketTerm_primrec (fun n _ => n + 1) hc (fun m : ℕ => m) hd).of_eq fun a => by
    unfold upperBracketTerm; cases measureIndexRequest a.1.1 a.1.2.1 a.2 a.1.2.2 <;> rfl

/-- Lower bracket numerators are primitive recursive. -/
private lemma lowerBracketNumerator_primrec :
    Primrec (fun p : ℕ × ℕ × BitString => lowerBracketNumerator p.1 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : ℕ × ℕ × BitString => List.range (p.2.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  have ht := lowerBracketTerm_primrec
  have h_acc : Primrec (fun (p : (ℕ × ℕ × BitString) × (ℕ × ℕ)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have h_term : Primrec (fun (p : (ℕ × ℕ × BitString) × (ℕ × ℕ)) => lowerBracketTerm p.1.1
      p.1.2.1 p.1.2.2 p.2.2) :=
    ht.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
  have hh : Primrec₂ (fun (p : ℕ × ℕ × BitString) (acc_k : ℕ × ℕ) => max acc_k.1
      (lowerBracketTerm p.1 p.2.1 p.2.2 acc_k.2)) :=
    Primrec.nat_max.comp h_acc h_term
  exact (Primrec.list_foldl hr (Primrec.const 0) hh).of_eq fun _ => rfl

/-- Upper bracket numerators are primitive recursive. -/
private lemma upperBracketNumerator_primrec :
    Primrec (fun p : ℕ × ℕ × BitString => upperBracketNumerator p.1 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : ℕ × ℕ × BitString => List.range (p.2.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  have ht := upperBracketTerm_primrec
  have h_acc : Primrec (fun (p : (ℕ × ℕ × BitString) × (ℕ × ℕ)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have h_term : Primrec (fun (p : (ℕ × ℕ × BitString) × (ℕ × ℕ)) => upperBracketTerm p.1.1
      p.1.2.1 p.1.2.2 p.2.2) :=
    ht.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
  have hh : Primrec₂ (fun (p : ℕ × ℕ × BitString) (acc_k : ℕ × ℕ) => min acc_k.1
      (upperBracketTerm p.1 p.2.1 p.2.2 acc_k.2)) :=
    Primrec.nat_min.comp h_acc h_term
  have hstart : Primrec (fun p : ℕ × ℕ × BitString => 2 ^ p.2.1) :=
    primrec_two_pow_aux.comp (Primrec.fst.comp Primrec.snd)
  exact (Primrec.list_foldl hr hstart hh).of_eq fun _ => rfl

/-- A lower mass bracket equals its dyadic numerator. -/
private lemma massLower_eq_dyadic (e s : ℕ) (x : BitString) :
    massLower e s x = dyadicValue (lowerBracketNumerator e s x) s := by
  unfold massLower lowerBracketNumerator
  rw [range_fold_max]
  apply Finset.sup_congr rfl
  intro k hk
  have hks : k ≤ s := by
    rw [Finset.mem_range] at hk
    exact Nat.lt_succ_iff.mp hk
  unfold lowerBracketTerm
  cases measureIndexRequest e s k x with
  | none => simp [dyadicValue]
  | some a =>
    change min 1 (dyadicValue (a - 1) k) = dyadicValue (min (2^s) ((a - 1) * 2^(s - k))) s
    rw [(monotone_dyadicValue_num s).map_min, dyadicValue_two_pow_self, dyadic_rescale hks]

/-- An upper mass bracket equals its dyadic numerator. -/
private lemma massUpper_eq_dyadic (e s : ℕ) (x : BitString) :
    massUpper e s x = dyadicValue (upperBracketNumerator e s x) s := by
  unfold massUpper upperBracketNumerator
  rw [range_fold_min, dyadicValue_two_pow_self, min_eq_right]
  · apply Finset.inf_congr rfl
    intro k hk
    have hks : k ≤ s := by
      rw [Finset.mem_range] at hk
      exact Nat.lt_succ_iff.mp hk
    unfold upperBracketTerm
    cases measureIndexRequest e s k x with
    | none => exact (dyadicValue_two_pow_self s).symm
    | some a =>
      change min 1 (dyadicValue (a + 1) k) = dyadicValue (min (2^s) ((a + 1) * 2^(s - k))) s
      rw [(monotone_dyadicValue_num s).map_min, dyadicValue_two_pow_self, dyadic_rescale hks]
  · apply (Finset.inf_le (Finset.mem_range.mpr (Nat.succ_pos s))).trans
    rw [← dyadicValue_two_pow_self s]
    apply dyadicValue_mono_num
    unfold upperBracketTerm
    cases measureIndexRequest e s 0 x with
    | none => exact le_rfl
    | some a => exact min_le_left _ _

/-- Every upper bracket term is positive. -/
private lemma upperBracketTerm_pos (e s : ℕ) (x : BitString) (k : ℕ) :
    0 < upperBracketTerm e s x k := by
  unfold upperBracketTerm
  cases measureIndexRequest e s k x with
  | none => exact Nat.two_pow_pos s
  | some a =>
    apply lt_min (Nat.two_pow_pos s)
    apply Nat.mul_pos (Nat.succ_pos a) (Nat.two_pow_pos _)

/-- Every upper bracket numerator is positive. -/
private lemma upperBracketNumerator_pos (e s : ℕ) (x : BitString) :
    0 < upperBracketNumerator e s x := by
  unfold upperBracketNumerator
  have hstart : 0 < (2^s : ℕ) := Nat.two_pow_pos s
  generalize (2^s : ℕ) = start at hstart ⊢
  generalize (List.range (s + 1)) = l
  induction l generalizing start with
  | nil => exact hstart
  | cons k ks ih =>
    apply ih
    exact lt_min hstart (upperBracketTerm_pos e s x k)

/-- Both mass brackets have primitive recursive numerators. -/
private lemma computable_mass_brackets :
    ∃ lo hi : ℕ → ℕ → BitString → ℕ,
      Primrec (fun p : ℕ × ℕ × BitString => lo p.1 p.2.1 p.2.2) ∧
      Primrec (fun p : ℕ × ℕ × BitString => hi p.1 p.2.1 p.2.2) ∧
      ∀ e s x, massLower e s x = dyadicValue (lo e s x) s ∧
               massUpper e s x = dyadicValue (hi e s x) s ∧
               0 < hi e s x := by
  exact ⟨lowerBracketNumerator, upperBracketNumerator,
    lowerBracketNumerator_primrec, upperBracketNumerator_primrec,
    fun e s x => ⟨massLower_eq_dyadic e s x,
                  massUpper_eq_dyadic e s x,
                  upperBracketNumerator_pos e s x⟩⟩

/-! ## Rational stage products -/

/-- The numerator of a gated stage mean conditional. -/
private def stageNumerator (lo hi : ℕ → ℕ → BitString → ℕ) (eP eQ s : ℕ) (y : BitString)
    (b : Bool) : ℕ :=
  min 1 (lo eP s y) * min 1 (lo eQ s y) * (lo eP s (y ++ [b]) * hi eQ s y + lo eQ s (y ++
      [b]) * hi eP s y)

/-- The denominator of a gated stage mean conditional. -/
private def stageDenominator (hi : ℕ → ℕ → BitString → ℕ) (eP eQ s : ℕ) (y : BitString) : ℕ :=
  2 * hi eP s y * hi eQ s y

/-- Update a prefix and the numerator and denominator of its stage product. -/
private def stageFoldStep (lo hi : ℕ → ℕ → BitString → ℕ) (eP eQ s : ℕ) (st : BitString ×
    ℕ × ℕ) (b : Bool) : BitString × ℕ × ℕ :=
  (st.1 ++ [b], st.2.1 * stageNumerator lo hi eP eQ s st.1 b, st.2.2 * stageDenominator hi
      eP eQ s st.1)

/-- The real value of a dyadic number is its rational value. -/
private lemma dyadicValue_toReal (n s : ℕ) :
    (dyadicValue n s).toReal = (n : ℝ) / 2^s := by
  simp [dyadicValue, ENNReal.toReal_div]

/-- A positive dyadic numerator has positive value. -/
private lemma dyadicValue_pos_of_pos (n s : ℕ) :
    0 < dyadicValue n s ↔ 0 < n := by
  simp [dyadicValue, pos_iff_ne_zero]

/-- A gated stage mean conditional equals a rational ratio. -/
private lemma meanStageFactor_eq_ratio
    (lo hi : ℕ → ℕ → BitString → ℕ)
    (hspec : ∀ e s x, massLower e s x = dyadicValue (lo e s x) s ∧
                      massUpper e s x = dyadicValue (hi e s x) s ∧
                      0 < hi e s x)
    (eP eQ s : ℕ) (y : BitString) (b : Bool) :
    meanStageFactor eP eQ s y b = (stageNumerator lo hi eP eQ s y b : ℝ) /
        stageDenominator hi eP eQ s y := by
  have hL := fun e s x => (hspec e s x).1
  have hU := fun e s x => (hspec e s x).2.1
  have hP_ne : (hi eP s y : ℝ) ≠ 0 := by exact_mod_cast (hspec eP s y).2.2.ne'
  have hQ_ne : (hi eQ s y : ℝ) ≠ 0 := by exact_mod_cast (hspec eQ s y).2.2.ne'
  unfold meanStageFactor conditionalLower stageNumerator stageDenominator
  simp only [hL, hU, dyadicValue_pos_of_pos, dyadicValue_toReal]
  by_cases h1 : 0 < lo eP s y
  · by_cases h2 : 0 < lo eQ s y
    · have m1 : min 1 (lo eP s y) = 1 := by omega
      have m2 : min 1 (lo eQ s y) = 1 := by omega
      simp only [h1, h2, and_self, ↓reduceIte, m1, m2]
      push_cast
      field_simp
    · have m2 : min 1 (lo eQ s y) = 0 := by omega
      simp [h2, m2]
  · have m1 : min 1 (lo eP s y) = 0 := by omega
    simp [h1, m1]

/-- The prefix component of the stage fold is the processed string. -/
private lemma stageFold_prefix
    (lo hi : ℕ → ℕ → BitString → ℕ) (eP eQ s : ℕ) (x : BitString) :
    (x.foldl (stageFoldStep lo hi eP eQ s) ([], 1, 1)).1 = x := by
  induction x using List.reverseRecOn with
  | nil => rfl
  | append_singleton x b ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [stageFoldStep, ih]

/-- The stage product equals the ratio stored by its fold. -/
private lemma meanStageProduct_eq_ratio
    (lo hi : ℕ → ℕ → BitString → ℕ)
    (hspec : ∀ e s x, massLower e s x = dyadicValue (lo e s x) s ∧
                      massUpper e s x = dyadicValue (hi e s x) s ∧
                      0 < hi e s x)
    (eP eQ s : ℕ) (x : BitString) :
    meanStageProduct eP eQ s x = ENNReal.ofReal (((x.foldl (stageFoldStep lo hi eP eQ s)
        ([], 1, 1)).2.1 : ℝ) / (x.foldl (stageFoldStep lo hi eP eQ s) ([], 1, 1)).2.2) := by
  induction x using List.reverseRecOn with
  | nil => simp [meanStageProduct]
  | append_singleton x b ih =>
    have hsplit : meanStageProduct eP eQ s (x ++ [b]) = meanStageProduct eP eQ s x *
        ENNReal.ofReal (meanStageFactor eP eQ s x b) := by
      unfold meanStageProduct
      rw [← Fin.prod_congr' _ (by simp : x.length + 1 = (x ++ [b]).length), Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        simp [List.take_append_of_le_length (Nat.le_of_lt i.isLt), List.getElem_append_left i.isLt]
      · simp
    rw [hsplit, ih, List.foldl_append, List.foldl_cons, List.foldl_nil,
        meanStageFactor_eq_ratio lo hi hspec, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [stageFoldStep, stageFold_prefix]
    push_cast
    rw [div_mul_div_comm]

/-- Floor division computes the rounded rational ratio. -/
private lemma rounded_ratio_floor (m n : ℕ) :
    ⌊(m : ℝ) / n⌋₊ = m / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.floor_eq_iff (by positivity), le_div_iff₀ (by exact_mod_cast hn), div_lt_iff₀
      (by exact_mod_cast hn)]
    constructor
    · exact_mod_cast Nat.div_mul_le_self m n
    · have h : m < m / n * n + n := Nat.lt_div_mul_add hn
      have e : ((m / n * n + n : ℕ) : ℝ) = ((m / n : ℕ) + 1) * n := by push_cast; ring
      rw [← e]
      exact_mod_cast h

/-- The stage product fold update is primitive recursive. -/
private lemma stageFoldStep_primrec
    (lo hi : ℕ → ℕ → BitString → ℕ)
    (hlo : Primrec (fun p : ℕ × ℕ × BitString => lo p.1 p.2.1 p.2.2))
    (hhi : Primrec (fun p : ℕ × ℕ × BitString => hi p.1 p.2.1 p.2.2)) :
    Primrec₂ (fun (a : ℕ × ℕ × BitString) (p : (BitString × ℕ × ℕ) × Bool) =>
      stageFoldStep lo hi a.1.unpair.1 a.1.unpair.2 a.2.1 p.1 p.2) := by
  have hP : Primrec (fun (r : (ℕ × ℕ × BitString) × (BitString × ℕ × ℕ) × Bool) =>
      r.1.1.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
  have hQ : Primrec (fun (r : (ℕ × ℕ × BitString) × (BitString × ℕ × ℕ) × Bool) =>
      r.1.1.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
  have hs : Primrec (fun (r : (ℕ × ℕ × BitString) × (BitString × ℕ × ℕ) × Bool) =>
      r.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hy : Primrec (fun (r : (ℕ × ℕ × BitString) × (BitString × ℕ × ℕ) × Bool) =>
      r.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun (r : (ℕ × ℕ × BitString) × (BitString × ℕ × ℕ) × Bool) => r.2.2)
      := Primrec.snd.comp Primrec.snd
  have hyb : Primrec (fun (r : (ℕ × ℕ × BitString) × (BitString × ℕ × ℕ) × Bool) =>
      r.2.1.1 ++ [r.2.2]) := Primrec.list_concat.comp hy hb
  have hlo_P_y := hlo.comp (hP.pair (hs.pair hy))
  have hlo_Q_y := hlo.comp (hQ.pair (hs.pair hy))
  have hlo_P_yb := hlo.comp (hP.pair (hs.pair hyb))
  have hhi_Q_y := hhi.comp (hQ.pair (hs.pair hy))
  have hlo_Q_yb := hlo.comp (hQ.pair (hs.pair hyb))
  have hhi_P_y := hhi.comp (hP.pair (hs.pair hy))
  have hmP := Primrec.nat_min.comp (Primrec.const 1) hlo_P_y
  have hmQ := Primrec.nat_min.comp (Primrec.const 1) hlo_Q_y
  have hsum := Primrec.nat_add.comp (Primrec.nat_mul.comp hlo_P_yb hhi_Q_y)
      (Primrec.nat_mul.comp hlo_Q_yb hhi_P_y)
  have hnum := Primrec.nat_mul.comp (Primrec.nat_mul.comp hmP hmQ) hsum
  have hden := Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) hhi_P_y) hhi_Q_y
  have hn1 : Primrec (fun (r : (ℕ × ℕ × BitString) × (BitString × ℕ × ℕ) × Bool) =>
      r.2.1.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hd1 : Primrec (fun (r : (ℕ × ℕ × BitString) × (BitString × ℕ × ℕ) × Bool) =>
      r.2.1.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  exact (hyb.pair ((Primrec.nat_mul.comp hn1 hnum).pair (Primrec.nat_mul.comp hd1
      hden))).of_eq fun _ => rfl

/-- Rounded stage products have primitive recursive numerators. -/
private lemma meanStageRounded_primrec
    (lo hi : ℕ → ℕ → BitString → ℕ)
    (hlo : Primrec (fun p : ℕ × ℕ × BitString => lo p.1 p.2.1 p.2.2))
    (hhi : Primrec (fun p : ℕ × ℕ × BitString => hi p.1 p.2.1 p.2.2))
    (hspec : ∀ e s x, massLower e s x = dyadicValue (lo e s x) s ∧
                      massUpper e s x = dyadicValue (hi e s x) s ∧
                      0 < hi e s x) :
    Computable (fun p : ℕ × ℕ × BitString =>
      ⌊(2 ^ p.2.1 : ℝ) * (meanStageProduct p.1.unpair.1 p.1.unpair.2 p.2.1 p.2.2).toReal⌋₊) := by
  have hst : Primrec (fun a : ℕ × ℕ × BitString => a.2.2.foldl (stageFoldStep lo hi
      a.1.unpair.1 a.1.unpair.2 a.2.1) ([], 1, 1)) :=
    (Primrec.list_foldl (Primrec.snd.comp Primrec.snd) (Primrec.const ([], 1, 1))
        (stageFoldStep_primrec lo hi hlo hhi)).of_eq fun _ => rfl
  have hN := Primrec.nat_div.comp (Primrec.nat_mul.comp (primrec_two_pow_aux.comp
      (Primrec.fst.comp Primrec.snd)) (Primrec.fst.comp (Primrec.snd.comp hst)))
      (Primrec.snd.comp (Primrec.snd.comp hst))
  refine hN.to_comp.of_eq fun p => ?_
  rw [meanStageProduct_eq_ratio lo hi hspec, ENNReal.toReal_ofReal (by positivity), ←
      rounded_ratio_floor]
  congr 1
  push_cast
  ring

/-! ## Uniform lower semicomputability -/

/-- Stage approximations form a uniformly lower semicomputable mean family. -/
private lemma raw_mean_family :
    ∃ ν_raw : ℕ → BitString → ℝ≥0∞,
      IsUniformlyLowerSemicomputableTreeFamily ν_raw ∧
      (∀ (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
          [IsProbabilityMeasure Q],
        ∀ eP eQ, IsComputableMeasureIndex P eP →
          IsComputableMeasureIndex Q eQ →
          ∀ x, ν_raw (Nat.pair eP eQ) x = meanTree P Q x) := by
  obtain ⟨lo, hi, hlo, hhi, hspec⟩ := computable_mass_brackets
  have hcomp := meanStageRounded_primrec lo hi hlo hhi hspec
  let b (e : ℕ) (s : ℕ) (x : BitString) (ctx : BitString) : ℕ :=
    ⌊(2 ^ s : ℝ) * (meanStageProduct e.unpair.1 e.unpair.2 s x).toReal⌋₊
  let approx (e : ℕ) (s : ℕ) (x : BitString) : ℕ := makeMono (b e) s x []
  let ν_raw : ℕ → BitString → ℝ≥0∞ := fun e x => ⨆ s, dyadicValue (approx e s x) s
  use ν_raw
  refine ⟨⟨approx, fun e s x => makeMono_mono (b e) s x [], fun e x => rfl, ?_⟩, ?_⟩
  · have h_b_comp : Computable (fun p : ℕ × ℕ × BitString × BitString =>
        b p.1 p.2.1 p.2.2.1 p.2.2.2) := by
      have hproj : Computable (fun p : ℕ × ℕ × BitString × BitString => (p.1, p.2.1, p.2.2.1)) :=
        Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
          (Computable.fst.comp (Computable.snd.comp Computable.snd)))
      exact (hcomp.comp hproj).of_eq (fun _ => rfl)
    have h_makeMono_comp : Computable (fun p : ℕ × ℕ × BitString × BitString =>
        makeMono (b p.1) p.2.1 p.2.2.1 p.2.2.2) := makeMono_computable_uniform b h_b_comp
    have hproj2 : Computable (fun p : ℕ × ℕ × BitString => (p.1, p.2.1, p.2.2, ([] : BitString))) :=
      Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        ((Computable.snd.comp Computable.snd).pair (Computable.const [])))
    exact (h_makeMono_comp.comp hproj2).of_eq (fun _ => rfl)
  · intro P Q hP hQ eP eQ heP heQ x
    dsimp [ν_raw, approx, b]
    rw [iSup_makeMono_eq_iSup]
    have H := exp_mean_lsc P Q eP eQ heP heQ x
    dsimp [meanStageRounded] at H
    rw [Nat.unpair_pair]
    exact (Eq.symm H.2.2.2).symm

/-! ## Prefix-free sanitation -/

/-- Sanitize the raw mean family while retaining valid indexed members. -/
private lemma sanitize_mean_family (ν_raw : ℕ → BitString → ℝ≥0∞)
    (h_lsc : IsUniformlyLowerSemicomputableTreeFamily ν_raw)
    (h_mean : ∀ (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
        [IsProbabilityMeasure Q],
        ∀ eP eQ, IsComputableMeasureIndex P eP →
          IsComputableMeasureIndex Q eQ →
          ∀ x, ν_raw (Nat.pair eP eQ) x = meanTree P Q x) :
    ∃ ν : ℕ → BitString → ℝ≥0∞,
      IsUniformlyLowerSemicomputableTreeFamily ν ∧
      (∀ (e : ℕ) (S : Finset BitString), IsPrefixFree (S : Set BitString) →
        ∑ x ∈ S, ν e x ≤ 1) ∧
      (∀ (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
          [IsProbabilityMeasure Q],
        ∀ eP eQ, IsComputableMeasureIndex P eP →
          IsComputableMeasureIndex Q eQ →
          ∀ x, ν (Nat.pair eP eQ) x = meanTree P Q x) := by
  rcases h_lsc with ⟨approx, h_mono, h_eq, h_comp⟩
  let approx' : ℕ → ℕ → BitString → BitString → ℕ := fun e s x ctx => approx e s x
  let r (e : ℕ) (s : ℕ) (x : BitString) : ℕ := treeSanitize (approx' e) s x
  have happrox : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      approx' p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    have hproj : Computable (fun p : ℕ × ℕ × BitString × BitString =>
        (p.1, p.2.1, p.2.2.1)) :=
      Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    exact (h_comp.comp hproj).of_eq (fun _ => rfl)
  have hr_comp : Computable (fun p : ℕ × ℕ × BitString => r p.1 p.2.1 p.2.2) := by
    exact computable_treeSanitize_uniform (b := approx') happrox
  have hr_mono : ∀ e s x,
      dyadicValue (r e s x) s ≤ dyadicValue (r e (s + 1) x) (s + 1) := by
    intro e s x
    exact treeSanitize_stage_mono (approx' e) (fun t out _ => h_mono e t out) s x
  let ν : ℕ → BitString → ℝ≥0∞ := fun e x => ⨆ s, dyadicValue (r e s x) s
  use ν
  refine ⟨⟨r, hr_mono, fun _ _ => rfl, hr_comp⟩, ?_, ?_⟩
  · intro e S h_free
    have hcomp_e : Computable (fun p : ℕ × BitString => r e p.1 p.2) :=
      (hr_comp.comp ((Computable.const e).pair Computable.id)).of_eq fun _ => rfl
    have hlsc : IsLowerSemicomputableContinuousSemimeasure (ν e) :=
      isLowerSemicomputableContinuousSemimeasure_iSup_of_stage
        (fun s => treeSanitize_root (approx' e) s)
        (fun s x => treeSanitize_coherent (approx' e) s x)
        (hr_mono e) hcomp_e
    exact IsContinuousTreeSemimeasure.sum_antichain_le hlsc.1 S h_free
  · intro P Q hP hQ eP eQ heP heQ x
    have ha := exp_mean_tree P Q
    have hsup : ∀ x, ⨆ s, dyadicValue (approx' (Nat.pair eP eQ) s x []) s = meanTree P Q x := by
      intro x
      dsimp [approx']
      rw [h_eq (Nat.pair eP eQ) x]
      exact h_mean P Q eP eQ heP heQ x
    have h_a_eq : ν (Nat.pair eP eQ) x = meanTree P Q x := by
      have h_eq2 : (fun x => ν (Nat.pair eP eQ) x) = meanTree P Q := by
        apply treeLSCEnum_eq_of_iSup_eq (meanTree P Q) (approx' (Nat.pair eP eQ))
          (fun s out _ => h_mono (Nat.pair eP eQ) s out)
        · exact fun x _ => hsup x
        · exact ha
        · intro s x_in
          exact treeSanitize_eq_simpleApprox_of_honest (meanTree P Q) (approx' (Nat.pair eP eQ))
            (fun x _ => hsup x) ha s x_in
      rw [← h_eq2]
    exact h_a_eq

/-- Uniform sanitation gives a budgeted family that agrees with the first-exit mean tree
on every valid pair of indices. Blueprint node `exp:mean-sanitize`. -/
theorem exp_mean_sanitize :
    ∃ ν : ℕ → BitString → ℝ≥0∞,
      IsUniformlyLowerSemicomputableTreeFamily ν ∧
      (∀ (e : ℕ) (S : Finset BitString), IsPrefixFree (S : Set BitString) →
        ∑ x ∈ S, ν e x ≤ 1) ∧
      (∀ (P Q : Measure CantorSeq) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
        ∀ eP eQ, IsComputableMeasureIndex P eP → IsComputableMeasureIndex Q eQ →
          ∀ x, ν (Nat.pair eP eQ) x = meanTree P Q x) := by
  obtain ⟨ν_raw, h_lsc, h_mean⟩ := raw_mean_family
  exact sanitize_mean_family ν_raw h_lsc h_mean

end Kolmogorov.MDLPrediction
