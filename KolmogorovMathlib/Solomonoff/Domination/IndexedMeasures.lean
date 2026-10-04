import KolmogorovMathlib.Solomonoff.Basic
import KolmogorovMathlib.Solomonoff.MeasureIndex
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.LSCApproximation
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure

/-!
# Uniformly sanitized semimeasures read off from measure indices

The first step of dominance through an index: every numerical program index `e` is turned,
uniformly in `e`, into a lower semicomputable continuous tree semimeasure `ν e`, which equals the
cylinder masses of `μ` whenever `e` really is an index of the computable probability measure `μ`
(`exists_uniform_indexed_continuousSemimeasure`).  At stage `s` the index is run with budget `s`
at every precision `k ≤ s`, each returned numerator is corrected by the one-unit error allowance,
and the largest certified lower bound is kept; the resulting family is then sanitized into tree
semimeasures.  Uniform lower semicomputability of a family is
`IsUniformlyLowerSemicomputableTreeFamily`.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- A family of tree masses is lower semicomputable uniformly in its numerical index. -/
def IsUniformlyLowerSemicomputableTreeFamily
    (ν : ℕ → BitString → ℝ≥0∞) : Prop :=
  ∃ q : ℕ → ℕ → BitString → ℕ,
    (∀ e s x, dyadicValue (q e s x) s ≤ dyadicValue (q e (s + 1) x) (s + 1)) ∧
    (∀ e x, ⨆ s, dyadicValue (q e s x) s = ν e x) ∧
    Computable (fun p : ℕ × ℕ × BitString => q p.1 p.2.1 p.2.2)

/-- At stage `s`, run index `e` with budget `s` at every precision `k ≤ s`, subtract the
one-unit error allowance from each returned numerator, rescale to denominator `2^s`, and retain
the largest certified lower bound. -/
@[irreducible] private def indexedMeasureLowerApprox (e s : ℕ) (x : BitString) : ℕ :=
  (Finset.range (s + 1)).sup fun k =>
    match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
        (Encodable.encode (x, k)) with
    | some a => (a - 1) * 2 ^ (s - k)
    | none => 0

/-- Increasing the evaluation budget and admitting one more precision cannot decrease the
corrected lower approximation. -/
private lemma indexedMeasureLowerApprox_mono (e s : ℕ) (x : BitString) :
    dyadicValue (indexedMeasureLowerApprox e s x) s ≤
      dyadicValue (indexedMeasureLowerApprox e (s + 1) x) (s + 1) := by
  rw [← dyadicValue_two_mul_succ]
  apply dyadicValue_mono_num
  rw [indexedMeasureLowerApprox, indexedMeasureLowerApprox]
  obtain ⟨k, hk, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (s + 1))
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ s)⟩ (fun k =>
      match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
          (Encodable.encode (x, k)) with
      | some a => (a - 1) * 2 ^ (s - k)
      | none => 0)
  rw [hsup]
  have hk_le : k ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hk_next : k ∈ Finset.range (s + 1 + 1) := by
    exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hk) (Nat.lt_succ_self _))
  cases heval : Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
      (Encodable.encode (x, k)) with
  | none => simp
  | some a =>
      have heval' : Nat.Partrec.Code.evaln (s + 1)
          (Denumerable.ofNat Nat.Partrec.Code e) (Encodable.encode (x, k)) = some a := by
        exact Nat.Partrec.Code.evaln_mono (Nat.le_succ s) heval
      have hexp : s + 1 - k = (s - k) + 1 := by omega
      have hle := Finset.le_sup (f := fun k =>
        match Nat.Partrec.Code.evaln (s + 1) (Denumerable.ofNat Nat.Partrec.Code e)
            (Encodable.encode (x, k)) with
        | some a => (a - 1) * 2 ^ (s + 1 - k)
        | none => 0) hk_next
      calc
        2 * ((a - 1) * 2 ^ (s - k)) = (a - 1) * 2 ^ (s + 1 - k) := by
          rw [hexp, pow_succ]
          ac_rfl
        _ ≤ _ := by simpa only [heval', Option.some.injEq] using hle

/-- An inequality valid up to every dyadic error remains valid when the error tends to zero. -/
private lemma le_of_le_add_dyadicValue_c (a b : ENNReal) (c : ℕ) :
    (∀ k, a ≤ b + dyadicValue c k) → a ≤ b := by
  intro h
  by_cases hb : b = ⊤
  · rw [hb]
    exact le_top
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hb'
    have hk_exists : ∃ k : ℕ, dyadicValue c k ≤ (ε : ENNReal) := by
      have hd : ∀ k : ℕ, dyadicValue c k = c * (2 : ENNReal)⁻¹ ^ k := by
        intro k
        simp only [dyadicValue]
        rw [div_eq_mul_inv, ENNReal.inv_pow]
      have htendsto_pow : Filter.Tendsto (fun k => (2 : ENNReal)⁻¹ ^ k) Filter.atTop (nhds 0) := by
        apply ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        simp only [ENNReal.inv_lt_one, ENNReal.one_lt_two]
      have htendsto : Filter.Tendsto
          (fun k => (c : ENNReal) * (2 : ENNReal)⁻¹ ^ k) Filter.atTop (nhds (c * 0)) := by
        apply ENNReal.Tendsto.const_mul htendsto_pow
        right
        exact ENNReal.coe_ne_top
      have hmul_zero : (c : ENNReal) * 0 = 0 := mul_zero _
      rw [hmul_zero] at htendsto
      have h_ev : ∀ᶠ k in Filter.atTop, (c : ENNReal) * (2 : ENNReal)⁻¹ ^ k < ε := by
        have ht : Set.Iio (ε : ENNReal) ∈ nhds 0 := by
          exact isOpen_Iio.mem_nhds (by exact ENNReal.coe_pos.mpr hε)
        exact htendsto ht
      rcases Filter.eventually_atTop.mp h_ev with ⟨k_0, hk_0⟩
      use k_0
      rw [hd]
      exact le_of_lt (hk_0 k_0 (le_refl _))
    rcases hk_exists with ⟨k, hk⟩
    have hk_add : b + dyadicValue c k ≤ b + (ε : ENNReal) := add_le_add (le_refl _) hk
    exact le_trans (h k) hk_add

private lemma dyadicValue_mul_pow_sub (a s k : ℕ) (hk : k ≤ s) :
    dyadicValue (a * 2 ^ (s - k)) s = dyadicValue a k := by
  have hd : dyadicValue (a * 2 ^ (s - k)) (k + (s - k)) = dyadicValue a k := by
    induction s - k with
    | zero => simp only [dyadicValue, pow_zero, mul_one, Nat.add_zero]
    | succ d ih =>
      have hm : a * 2 ^ (d + 1) = 2 * (a * 2 ^ d) := by
        rw [pow_succ]
        ac_rfl
      rw [hm, Nat.add_succ, dyadicValue_two_mul_succ]
      exact ih
  have hk_add : k + (s - k) = s := by omega
  rwa [hk_add] at hd

private lemma dyadicValue_sup_finset (S : Finset ℕ) (f : ℕ → ℕ) (s : ℕ) :
    dyadicValue (S.sup f) s = S.sup (fun k => dyadicValue (f k) s) := by
  induction S using Finset.induction_on with
  | empty =>
    have hz : dyadicValue 0 s = 0 := by simp [dyadicValue]
    exact hz
  | @insert a S' ha ih =>
    rw [Finset.sup_insert, Finset.sup_insert]
    have hd_max : ∀ a b s, dyadicValue (max a b) s = max (dyadicValue a s) (dyadicValue b s) := by
      intro a b s
      rcases le_total a b with h | h
      · rw [max_eq_right h]
        have hd : dyadicValue a s ≤ dyadicValue b s := dyadicValue_mono_num h s
        rw [max_eq_right hd]
      · rw [max_eq_left h]
        have hd : dyadicValue b s ≤ dyadicValue a s := dyadicValue_mono_num h s
        rw [max_eq_left hd]
    rw [hd_max, ih]

private lemma max_eq_add_sub (a b : ℕ) : max a b = a + (b - a) := by omega

private lemma foldl_max_eq_sup_range (n : ℕ) (f : ℕ → ℕ) :
    (Finset.range n).sup f = (List.range n).foldl (fun acc k => max acc (f k)) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.range_add_one, Finset.sup_insert, ih, List.range_succ, List.foldl_append]
    simp only [List.foldl_nil, List.foldl_cons, max_comm]

private lemma indexedMeasureLowerApprox_computable :
    Computable (fun p : ℕ × ℕ × BitString =>
      indexedMeasureLowerApprox p.1 p.2.1 p.2.2) := by
  have heq : (fun p : ℕ × ℕ × BitString =>
      indexedMeasureLowerApprox p.1 p.2.1 p.2.2) = (fun p : ℕ × ℕ × BitString =>
      (Finset.range (p.2.1 + 1)).sup fun k =>
        match Nat.Partrec.Code.evaln p.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1)
          (Encodable.encode (p.2.2, k)) with
        | some a => (a - 1) * 2 ^ (p.2.1 - k)
        | none => 0) := by
    funext p
    rw [indexedMeasureLowerApprox]
  rw [heq]
  have hevaln_args_1 : Primrec (fun (p : (ℕ × ℕ × BitString) × ℕ) => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hevaln_args_2 : Primrec (fun (p : (ℕ × ℕ × BitString) × ℕ) =>
      Denumerable.ofNat Nat.Partrec.Code p.1.1) :=
    (Primrec.ofNat _).comp (Primrec.fst.comp Primrec.fst)
  have hevaln_args_3 : Primrec (fun (p : (ℕ × ℕ × BitString) × ℕ) =>
      Encodable.encode (p.1.2.2, p.2)) :=
    Primrec.encode.comp (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have hevaln_args : Primrec (fun p : (ℕ × ℕ × BitString) × ℕ =>
    ((p.1.2.1, Denumerable.ofNat Nat.Partrec.Code p.1.1), Encodable.encode (p.1.2.2, p.2))) :=
    Primrec.pair (Primrec.pair hevaln_args_1 hevaln_args_2) hevaln_args_3
  have hevaln : Primrec (fun p : (ℕ × ℕ × BitString) × ℕ =>
      Nat.Partrec.Code.evaln p.1.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1.1)
        (Encodable.encode (p.1.2.2, p.2))) :=
    Nat.Partrec.Code.primrec_evaln.comp hevaln_args
  have hsome : Primrec₂ (fun (p : (ℕ × ℕ × BitString) × ℕ) (a : ℕ) =>
      (a - 1) * 2 ^ (p.1.2.1 - p.2)) := by
    have h1 : Primrec₂ (fun (p : (ℕ × ℕ × BitString) × ℕ) (a : ℕ) => a - 1) :=
      Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
    have h2_1 : Primrec (fun (p : (ℕ × ℕ × BitString) × ℕ) => p.1.2.1 - p.2) :=
      Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    have h2 : Primrec₂ (fun (p : (ℕ × ℕ × BitString) × ℕ) (a : ℕ) => 2 ^ (p.1.2.1 - p.2)) :=
      (Primrec₂.unpaired.mp (Primrec.nat_iff.mpr Nat.Primrec.pow)).comp (Primrec.const 2)
        (h2_1.comp Primrec.fst)
    exact Primrec.nat_mul.comp h1 h2
  have hnone : Primrec (fun (p : (ℕ × ℕ × BitString) × ℕ) => (0 : ℕ)) := Primrec.const 0
  have ho : Primrec (fun (p : (ℕ × ℕ × BitString) × ℕ) => Nat.Partrec.Code.evaln p.1.2.1
      (Denumerable.ofNat Nat.Partrec.Code p.1.1) (Encodable.encode (p.1.2.2, p.2))) := hevaln
  have hf : Primrec (fun (p : (ℕ × ℕ × BitString) × ℕ) => (0 : ℕ)) := hnone
  have hg : Primrec₂ (fun (p : (ℕ × ℕ × BitString) × ℕ) (a : ℕ) =>
      (a - 1) * 2 ^ (p.1.2.1 - p.2)) := hsome
  have hmatch' : Primrec (fun (p : (ℕ × ℕ × BitString) × ℕ) =>
      @Option.casesOn ℕ (fun _ => ℕ) (Nat.Partrec.Code.evaln p.1.2.1
          (Denumerable.ofNat Nat.Partrec.Code p.1.1)
          (Encodable.encode (p.1.2.2, p.2))) (0 : ℕ)
          (fun a => (a - 1) * 2 ^ (p.1.2.1 - p.2))) :=
    Primrec.option_casesOn ho hf hg
  have hmatch_eq : (fun (p : (ℕ × ℕ × BitString) × ℕ) => match Nat.Partrec.Code.evaln p.1.2.1
          (Denumerable.ofNat Nat.Partrec.Code p.1.1)
          (Encodable.encode (p.1.2.2, p.2)) with
          | some a => (a - 1) * 2 ^ (p.1.2.1 - p.2)
          | none => 0) =
      (fun (p : (ℕ × ℕ × BitString) × ℕ) => @Option.casesOn ℕ (fun _ => ℕ)
          (Nat.Partrec.Code.evaln p.1.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1.1)
          (Encodable.encode (p.1.2.2, p.2))) (0 : ℕ) (fun a => (a - 1) * 2 ^ (p.1.2.1 - p.2))) := by
    funext p; generalize (Nat.Partrec.Code.evaln p.1.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1.1)
      (Encodable.encode (p.1.2.2, p.2))) = opt; cases opt <;> rfl
  have hmatch : Primrec (fun (p : (ℕ × ℕ × BitString) × ℕ) =>
      match Nat.Partrec.Code.evaln p.1.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1.1)
          (Encodable.encode (p.1.2.2, p.2)) with
      | some a => (a - 1) * 2 ^ (p.1.2.1 - p.2)
      | none => 0) := hmatch_eq ▸ hmatch'
  have hl : Primrec (fun p : ℕ × ℕ × BitString => List.range (p.2.1 + 1)) :=
    Primrec.list_range.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
  have hz : Primrec (fun p : ℕ × ℕ × BitString => (0 : ℕ)) := Primrec.const 0
  have hh_inner_1 : Primrec (fun p : (ℕ × ℕ × BitString) × (ℕ × ℕ) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hh_inner_2 : Primrec (fun p : (ℕ × ℕ × BitString) × (ℕ × ℕ) =>
      match Nat.Partrec.Code.evaln p.1.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1.1)
          (Encodable.encode (p.1.2.2, p.2.2)) with
      | some a => (a - 1) * 2 ^ (p.1.2.1 - p.2.2)
      | none => 0) := hmatch.comp (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
  have hh : Primrec₂ (fun (p : ℕ × ℕ × BitString) (acc_k : ℕ × ℕ) =>
      max acc_k.1 (
        match Nat.Partrec.Code.evaln p.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1)
            (Encodable.encode (p.2.2, acc_k.2)) with
        | some a => (a - 1) * 2 ^ (p.2.1 - acc_k.2)
        | none => 0)) := by
    have max_comp : Primrec₂ (fun a b : ℕ => max a b) := by
      have max_eq : (fun a b : ℕ => max a b) = fun a b => a + (b - a) := by
        funext a b; exact max_eq_add_sub a b
      exact max_eq ▸ Primrec.nat_add.comp Primrec.fst (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
    exact Primrec₂.comp max_comp hh_inner_1 hh_inner_2
  have hfold : Primrec (fun p : ℕ × ℕ × BitString =>
      (List.range (p.2.1 + 1)).foldl (fun acc k => max acc (
        match Nat.Partrec.Code.evaln p.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1)
            (Encodable.encode (p.2.2, k)) with
        | some a => (a - 1) * 2 ^ (p.2.1 - k)
        | none => 0)) 0) := Primrec.list_foldl hl hz hh
  have heq' : (fun p : ℕ × ℕ × BitString =>
      (Finset.range (p.2.1 + 1)).sup fun k =>
        match Nat.Partrec.Code.evaln p.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1)
            (Encodable.encode (p.2.2, k)) with
        | some a => (a - 1) * 2 ^ (p.2.1 - k)
        | none => 0) =
      (fun p : ℕ × ℕ × BitString =>
      (List.range (p.2.1 + 1)).foldl (fun acc k => max acc (
        match Nat.Partrec.Code.evaln p.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1)
            (Encodable.encode (p.2.2, k)) with
        | some a => (a - 1) * 2 ^ (p.2.1 - k)
        | none => 0)) 0) := by funext p; exact foldl_max_eq_sup_range _ _
  exact Primrec.to_comp (heq' ▸ hfold)


/-- If `e` is an index of a probability measure, the corrected lower approximations converge
from below to every cylinder mass of that measure. -/
private lemma iSup_indexedMeasureLowerApprox_eq_cantorMass
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (e : ℕ)
    (he : IsComputableMeasureIndex μ e) (x : BitString) :
    ⨆ s, dyadicValue (indexedMeasureLowerApprox e s x) s = cantorMass μ x := by
  have heq : (fun s => dyadicValue (indexedMeasureLowerApprox e s x) s) =
      (fun s => dyadicValue ((Finset.range (s + 1)).sup fun k =>
    match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
        (Encodable.encode (x, k)) with
    | some a => (a - 1) * 2 ^ (s - k)
    | none => 0) s) := by
    funext s
    rw [indexedMeasureLowerApprox]
  rw [heq]
  apply le_antisymm
  · refine iSup_le ?_
    intro s
    have heval : ∀ k ≤ s, dyadicValue (
        match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
          (Encodable.encode (x, k)) with
        | some a => (a - 1) * 2 ^ (s - k)
        | none => 0) s ≤ cantorMass μ x := by
      intro k hk
      generalize hopt : Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
        (Encodable.encode (x, k)) = opt
      cases opt with
      | none =>
        have hzero : dyadicValue 0 s = 0 := by simp [dyadicValue]
        rw [hzero]
        exact zero_le
      | some a =>
        have heval_real : a ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval
            (Encodable.encode (x, k)) := by
          exact Nat.Partrec.Code.evaln_sound hopt
        have hbound := he x k
        rcases hbound with ⟨a_prime, ha_prime, hle, hge⟩
        have a_eq_a_prime : a = a_prime := Part.mem_unique heval_real ha_prime
        subst a_eq_a_prime
        rw [dyadicValue_mul_pow_sub _ _ _ hk]
        by_cases ha : a = 0
        · rw [ha]
          have hzero : dyadicValue (0 - 1) k = 0 := by simp [dyadicValue]
          rw [hzero]
          exact zero_le
        · have ha_ge : a ≥ 1 := by omega
          have hd : dyadicValue (a - 1) k + dyadicValue 1 k = dyadicValue a k := by
            rw [← dyadicValue_add]
            have hsub : a - 1 + 1 = a := by omega
            rw [hsub]
          have hle' : dyadicValue (a - 1) k + dyadicValue 1 k ≤
              cantorMass μ x + dyadicValue 1 k := by
            rw [hd]
            exact hle
          have hfin : dyadicValue 1 k ≠ ⊤ := by
            apply ENNReal.div_ne_top (by exact ENNReal.coe_ne_top) (by norm_num)
          exact ENNReal.le_of_add_le_add_right hfin hle'
    rw [dyadicValue_sup_finset]
    apply Finset.sup_le
    intro k hk
    have hle_s : k ≤ s := by
      rw [Finset.mem_range] at hk
      omega
    exact heval k hle_s
  · apply le_of_le_add_dyadicValue_c _ _ 2
    intro k
    rcases he x k with ⟨a, ha, hle, hge⟩
    have hevaln := Nat.Partrec.Code.evaln_complete.mp ha
    rcases hevaln with ⟨s_eval, heval⟩
    let s := max k s_eval
    have hs_ge_k : k ≤ s := le_max_left _ _
    have h_a_evaln : a ∈ Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
        (Encodable.encode (x, k)) := by
      exact @Nat.Partrec.Code.evaln_mono s_eval s _ _ _ (le_max_right _ _) heval
    have h_a_eq_some : Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
        (Encodable.encode (x, k)) = some a := by
      exact Option.mem_def.mp h_a_evaln
    have h_isup : dyadicValue (a - 1) k ≤ ⨆ s,
        dyadicValue ((Finset.range (s + 1)).sup fun k =>
          match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
              (Encodable.encode (x, k)) with
          | some a => (a - 1) * 2 ^ (s - k)
          | none => 0) s := by
      have hle_isup := @le_iSup _ _ _ (fun s => dyadicValue ((Finset.range (s + 1)).sup fun k =>
        match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
            (Encodable.encode (x, k)) with
        | some a => (a - 1) * 2 ^ (s - k)
        | none => 0) s) s
      have heq1 : dyadicValue ((Finset.range (s + 1)).sup fun k =>
        match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
            (Encodable.encode (x, k)) with
        | some a => (a - 1) * 2 ^ (s - k)
        | none => 0) s = (Finset.range (s + 1)).sup (fun k => dyadicValue (
        match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
            (Encodable.encode (x, k)) with
        | some a => (a - 1) * 2 ^ (s - k)
        | none => 0) s) := dyadicValue_sup_finset _ _ _
      rw [heq1] at hle_isup
      have hk_mem : k ∈ Finset.range (s + 1) := by
        rw [Finset.mem_range]
        omega
      have hle_sup := Finset.le_sup hk_mem (f := fun k => dyadicValue (
        match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
            (Encodable.encode (x, k)) with
        | some a => (a - 1) * 2 ^ (s - k)
        | none => 0) s)
      simp only [h_a_eq_some] at hle_sup
      rw [dyadicValue_mul_pow_sub _ _ _ hs_ge_k] at hle_sup
      exact le_trans hle_sup hle_isup
    have hd_bound : dyadicValue a k ≤ dyadicValue (a - 1) k + dyadicValue 1 k := by
      by_cases ha_0 : a = 0
      · rw [ha_0]
        have hz : dyadicValue 0 k = 0 := by simp [dyadicValue]
        rw [hz]
        exact zero_le
      · rw [← dyadicValue_add]
        have heq_add : a - 1 + 1 = a := by omega
        rw [heq_add]
    have h_two : dyadicValue 1 k + dyadicValue 1 k = dyadicValue 2 k := by
      rw [← dyadicValue_add]
    have h_add_isup : dyadicValue (a - 1) k + dyadicValue 2 k ≤
        (⨆ s, dyadicValue ((Finset.range (s + 1)).sup fun k =>
          match Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
              (Encodable.encode (x, k)) with
          | some a => (a - 1) * 2 ^ (s - k)
          | none => 0) s) + dyadicValue 2 k := add_le_add h_isup (le_refl _)
    have h_step1 : dyadicValue a k + dyadicValue 1 k ≤
        dyadicValue (a - 1) k + dyadicValue 1 k + dyadicValue 1 k :=
      add_le_add hd_bound (le_refl _)
    have h_step2 : dyadicValue (a - 1) k + dyadicValue 1 k + dyadicValue 1 k =
        dyadicValue (a - 1) k + dyadicValue 2 k := by
      rw [add_assoc, h_two]
    rw [h_step2] at h_step1
    exact le_trans hge (le_trans h_step1 h_add_isup)


/-- The uniform tree sanitizer turns any monotone family of lower approximations into continuous
semimeasures, and it leaves a component unchanged when that component already converges to a
continuous tree semimeasure. -/
private lemma exists_uniform_sanitized_continuousSemimeasure
    (q : ℕ → ℕ → BitString → ℕ)
    (hq_mono : ∀ e s x,
      dyadicValue (q e s x) s ≤ dyadicValue (q e (s + 1) x) (s + 1))
    (hq_comp : Computable (fun p : ℕ × ℕ × BitString => q p.1 p.2.1 p.2.2)) :
    ∃ ν : ℕ → BitString → ℝ≥0∞,
      (∀ e, IsContinuousTreeSemimeasure (ν e)) ∧
      IsUniformlyLowerSemicomputableTreeFamily ν ∧
      ∀ (a : BitString → ℝ≥0∞) (e : ℕ),
        IsContinuousTreeSemimeasure a →
        (∀ x, ⨆ s, dyadicValue (q e s x) s = a x) → ν e = a := by
  let approx : ℕ → ℕ → BitString → BitString → ℕ := fun e s x _ => q e s x
  let r : ℕ → ℕ → BitString → ℕ := fun e s x => treeSanitize (approx e) s x
  let ν : ℕ → BitString → ℝ≥0∞ := fun e x => ⨆ s, dyadicValue (r e s x) s
  have happrox : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      approx p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    have hproj : Computable (fun p : ℕ × ℕ × BitString × BitString =>
        (p.1, p.2.1, p.2.2.1)) :=
      Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    exact (hq_comp.comp hproj).of_eq (fun _ => rfl)
  have hr_comp : Computable (fun p : ℕ × ℕ × BitString => r p.1 p.2.1 p.2.2) := by
    exact computable_treeSanitize_uniform (b := approx) happrox
  have hr_mono : ∀ e s x,
      dyadicValue (r e s x) s ≤ dyadicValue (r e (s + 1) x) (s + 1) := by
    intro e s x
    exact treeSanitize_stage_mono (approx e) (fun t out _ => hq_mono e t out) s x
  use ν
  refine ⟨?_, ⟨r, hr_mono, fun _ _ => rfl, hr_comp⟩, ?_⟩
  · intro e
    have hcomp_e : Computable (fun p : ℕ × BitString => r e p.1 p.2) :=
      (hr_comp.comp ((Computable.const e).pair Computable.id)).of_eq fun _ => rfl
    exact (isLowerSemicomputableContinuousSemimeasure_iSup_of_stage
      (fun s => treeSanitize_root (approx e) s)
      (fun s x => treeSanitize_coherent (approx e) s x)
      (hr_mono e) hcomp_e).1
  · intro a e ha hsup
    apply treeLSCEnum_eq_of_iSup_eq a (approx e) (fun s out _ => hq_mono e s out)
      (fun x _ => hsup x) ha
    intro s x
    apply treeSanitize_eq_simpleApprox_of_honest a (approx e) (fun y _ => hsup y) ha

/-- Every program index can be sanitized uniformly into a lower-semicomputable continuous
semimeasure, without changing the cylinder masses when the program really indexes a probability
measure. This is the uniform index-sanitization step in the proof of dominance through an index. -/
lemma exists_uniform_indexed_continuousSemimeasure :
    ∃ ν : ℕ → BitString → ℝ≥0∞,
      (∀ e, IsContinuousTreeSemimeasure (ν e)) ∧
      IsUniformlyLowerSemicomputableTreeFamily ν ∧
      ∀ (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (e : ℕ),
        IsComputableMeasureIndex μ e → ν e = cantorMass μ := by
  obtain ⟨ν, hν_cont, hν_lsc, hν_eq⟩ :=
    exists_uniform_sanitized_continuousSemimeasure indexedMeasureLowerApprox
      indexedMeasureLowerApprox_mono indexedMeasureLowerApprox_computable
  exact ⟨ν, hν_cont, hν_lsc, fun μ _ e he =>
    hν_eq (cantorMass μ) e (isContinuousTreeSemimeasure_cantorMass μ)
      (iSup_indexedMeasureLowerApprox_eq_cantorMass μ e he)⟩

end Kolmogorov
