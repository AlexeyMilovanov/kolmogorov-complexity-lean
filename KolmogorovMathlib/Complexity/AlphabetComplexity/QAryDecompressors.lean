import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.LayeredDecompressors

/-!
# Four-letter descriptions

`plainK_fourLetterAlphabet_eq_half` (SUV Exercise 4): with a four-letter description alphabet
the complexity is exactly half the binary one, up to a constant.  The four-letter alphabet is
the case where the translation is lossless, since two bits make one letter.

`D_q` is the four-letter decompressor built from a binary one and `D_bin` the converse; their
computability rests on the primitive-recursive conversions `pairToFin4`, `fin4ToBits`,
`bitsToFin4List` and `fin4ListToBits`.  `enat_sInf_mem` is the `ℕ∞` fact that lets the two
infima be compared by exhibiting programs.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- The 4-ary decompressor constructed from a binary decompressor `U`. -/
def D_q (U : Map) : QMap 4 := fun (p, y) =>
  match p with
  | [] => Part.none
  | a :: rest =>
    let bits := fin4ListToBits rest
    if a = 0 then
      U (bits, y)
    else if a = 1 then
      U (bits.dropLast, y)
    else
      Part.none

/-- Packing a pair of bits into a letter of the four-letter alphabet is primitive recursive. -/
theorem pairToFin4_primrec : Primrec pairToFin4 := by
  have h : pairToFin4 =
      fun b => bif b.1 then (bif b.2 then 3 else 2) else (bif b.2 then 1 else 0) := by
    funext ⟨b1, b2⟩
    cases b1 <;> cases b2 <;> rfl
  rw [h]
  exact Primrec.cond Primrec.fst
    (Primrec.cond Primrec.snd (Primrec.const 3) (Primrec.const 2))
    (Primrec.cond Primrec.snd (Primrec.const 1) (Primrec.const 0))

/-- Unpacking a letter of the four-letter alphabet into two bits is primitive recursive. -/
theorem fin4ToBits_primrec : Primrec fin4ToBits := by
  have h : fin4ToBits = fun a =>
      bif a.val == 0 then [false, false]
      else bif a.val == 1 then [false, true]
      else bif a.val == 2 then [true, false]
      else [true, true] := by
    funext ⟨val, hv⟩
    interval_cases val <;> rfl
  rw [h]
  exact Primrec.cond
    (PrimrecPred.decide
      (Primrec.eq.comp (Primrec.fin_val.comp Primrec.id) (Primrec.const 0)))
    (Primrec.const [false, false])
    (Primrec.cond
      (PrimrecPred.decide
        (Primrec.eq.comp (Primrec.fin_val.comp Primrec.id) (Primrec.const 1)))
      (Primrec.const [false, true])
      (Primrec.cond
        (PrimrecPred.decide
          (Primrec.eq.comp (Primrec.fin_val.comp Primrec.id) (Primrec.const 2)))
        (Primrec.const [true, false])
        (Primrec.const [true, true])))

/-- One step of the fold that reads a bit string as a string over the four-letter alphabet
is primitive recursive. -/
theorem bitsToFin4FoldStep_primrec :
    Primrec (fun p : Bool × Option Bool × List (Fin 4) => bitsToFin4FoldStep p.1 p.2) := by
  have h_none : Primrec (fun (p : Bool × (Option Bool × List (Fin 4))) =>
      ((some p.1, p.2.2) : Option Bool × List (Fin 4))) :=
    Primrec.pair (Primrec.option_some.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have h_some : Primrec (fun (q : (Bool × (Option Bool × List (Fin 4))) × Bool) =>
      ((none, pairToFin4 (q.1.1, q.2) :: q.1.2.2) : Option Bool × List (Fin 4))) :=
    Primrec.pair (Primrec.const none)
      (Primrec.list_cons.comp
        (pairToFin4_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have h_cases := Primrec.option_casesOn (Primrec.fst.comp Primrec.snd) h_none h_some.to₂
  have h_eq : ∀ (p : Bool × Option Bool × List (Fin 4)),
      Option.casesOn p.2.1 (some p.1, p.2.2) (fun b => (none, pairToFin4 (p.1, b) :: p.2.2)) =
      bitsToFin4FoldStep p.1 p.2 := by
    rintro ⟨b, ⟨st1, st2⟩⟩
    cases st1 <;> rfl
  exact h_cases.of_eq h_eq

/-- Reading a bit string as a string over the four-letter alphabet is primitive recursive. -/
theorem bitsToFin4List_primrec : Primrec bitsToFin4List := by
  have hstep : Primrec₂ (fun (_ : BitString) (p : Bool × (Option Bool × List (Fin 4))) =>
      bitsToFin4FoldStep p.1 p.2) :=
    (bitsToFin4FoldStep_primrec.comp Primrec.snd).to₂
  have hfold := Primrec.list_foldr Primrec.id
    (Primrec.const ((none, []) : Option Bool × List (Fin 4))) hstep
  exact Primrec.snd.comp hfold

/-- Writing a string over the four-letter alphabet as a bit string is primitive recursive. -/
theorem fin4ListToBits_primrec : Primrec fin4ListToBits :=
  Primrec.list_flatMap Primrec.id (fin4ToBits_primrec.comp Primrec.snd)

/-- The binary decompressor built from a four-letter decompressor is partial computable. -/
theorem D_bin_partrec (D : QMap 4) (hD : Partrec D) : Partrec (D_bin D) := by
  have h_cond : Computable (fun (p : BitString × BitString) => p.1.length % 2 == 0) :=
    (PrimrecPred.decide (Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 2))
      (Primrec.const 0))).to_comp
  have h_then : Partrec (fun (p : BitString × BitString) => D (bitsToFin4List p.1, p.2)) :=
    Partrec.comp hD (Computable.pair
      (bitsToFin4List_primrec.to_comp.comp Computable.fst) Computable.snd)
  have h_else : Partrec (fun (_ : BitString × BitString) => (Part.none : Part BitString)) :=
    Partrec.none
  have h_eq : D_bin D =
      fun p => cond (p.1.length % 2 == 0) (D (bitsToFin4List p.1, p.2)) Part.none := by
    ext ⟨p, y⟩
    dsimp [D_bin]
    by_cases h : p.length % 2 = 0
    · have hc : (p.length % 2 == 0) = true := decide_eq_true h
      rw [if_pos h, hc]
      rfl
    · have hc : (p.length % 2 == 0) = false := decide_eq_false h
      rw [if_neg h, hc]
      rfl
  rw [h_eq]
  exact Partrec.cond h_cond h_then h_else

/-- Dropping the last bit of a bit string is primitive recursive. -/
theorem dropLast_primrec : Primrec (fun l : BitString => l.dropLast) := by
  have h : (fun l : BitString => l.dropLast) = fun l => l.take (l.length - 1) := by
    funext l; exact List.dropLast_eq_take
  rw [h]
  exact Primrec.list_take.comp
    (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)) Primrec.id

/-- The four-letter decompressor built from a binary decompressor is partial computable. -/
theorem D_q_partrec (U : Map) (hU : Partrec U) : Partrec (D_q U) := by
  have h_c_empty : Computable (fun (p : List (Fin 4) × BitString) => p.1.isEmpty) := by
    have h : (fun (p : List (Fin 4) × BitString) => p.1.isEmpty) =
        fun p => decide (p.1.length = 0) := by
      ext p; cases p.1 <;> rfl
    rw [h]
    exact (PrimrecPred.decide
      (Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 0))).to_comp
  have h_headD : Primrec (fun (p : List (Fin 4) × BitString) => p.1.headD (0 : Fin 4)) :=
    ((show Primrec (fun (q : Option (Fin 4) × Fin 4) => q.1.getD q.2)
      from Primrec.option_getD).comp
      (Primrec.pair (Primrec.list_head?.comp Primrec.fst)
        (Primrec.const (0 : Fin 4)))).of_eq
      (fun p => by cases p.1 <;> rfl)
  have h_c0 : Computable (fun (p : List (Fin 4) × BitString) => (p.1.headD 0).val == 0) :=
    (PrimrecPred.decide (Primrec.eq.comp (Primrec.fin_val.comp h_headD) (Primrec.const 0))).to_comp
  have h_c1 : Computable (fun (p : List (Fin 4) × BitString) => (p.1.headD 0).val == 1) :=
    (PrimrecPred.decide (Primrec.eq.comp (Primrec.fin_val.comp h_headD) (Primrec.const 1))).to_comp
  have h_tail : Computable (fun (p : List (Fin 4) × BitString) => p.1.tail) :=
    (Primrec.list_tail.comp Primrec.fst).to_comp
  have h_t0 : Partrec (fun (p : List (Fin 4) × BitString) => U (fin4ListToBits p.1.tail, p.2)) :=
    Partrec.comp hU (Computable.pair
      (fin4ListToBits_primrec.to_comp.comp h_tail)
      Computable.snd)
  have h_t1 : Partrec (fun (p : List (Fin 4) × BitString) =>
      U ((fin4ListToBits p.1.tail).dropLast, p.2)) :=
    Partrec.comp hU (Computable.pair
      (dropLast_primrec.to_comp.comp (fin4ListToBits_primrec.to_comp.comp h_tail))
      Computable.snd)
  have h_e : Partrec (fun (_ : List (Fin 4) × BitString) => (Part.none : Part BitString)) :=
    Partrec.none
  have h_body : Partrec (fun (p : List (Fin 4) × BitString) =>
      cond ((p.1.headD 0).val == 0) (U (fin4ListToBits p.1.tail, p.2))
        (cond ((p.1.headD 0).val == 1) (U ((fin4ListToBits p.1.tail).dropLast, p.2)) Part.none)) :=
    Partrec.cond h_c0 h_t0 (Partrec.cond h_c1 h_t1 h_e)
  have h_full := Partrec.cond h_c_empty h_e h_body
  have h_eq : D_q U = fun p => cond p.1.isEmpty Part.none
      (cond ((p.1.headD 0).val == 0) (U (fin4ListToBits p.1.tail, p.2))
        (cond ((p.1.headD 0).val == 1)
          (U ((fin4ListToBits p.1.tail).dropLast, p.2)) Part.none)) := by
    ext ⟨p, y⟩
    dsimp [D_q]
    cases p with
    | nil => rfl
    | cons a rest =>
      dsimp
      rcases a with ⟨val, hv⟩
      interval_cases val <;> rfl
  rw [h_eq]
  exact h_full

/-- A nonempty set of extended naturals not containing `⊤` attains its infimum. -/
theorem enat_sInf_mem {S : Set ℕ∞} (hS : S.Nonempty) (hTop : ⊤ ∉ S) : sInf S ∈ S := by
  classical
  have h_ne : sInf S ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hS
    have h_le : sInf S ≤ x := sInf_le hx
    intro h_top
    rw [h_top] at h_le
    have h_x_top : x = ⊤ := top_unique h_le
    subst h_x_top
    exact hTop hx
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h_ne
  have h_exists : ∃ m : ℕ, (m : ℕ∞) ∈ S := by
    obtain ⟨x, hx⟩ := hS
    by_cases hxTop : x = ⊤
    · exfalso; subst hxTop; exact hTop hx
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hxTop
      use m
      subst hm
      exact hx
  let m0 := Nat.find h_exists
  have hm0_in : (m0 : ℕ∞) ∈ S := Nat.find_spec h_exists
  have h_le_m0 : sInf S ≤ (m0 : ℕ∞) := sInf_le hm0_in
  have h_m0_le : (m0 : ℕ∞) ≤ sInf S := by
    apply le_sInf
    rintro y hy
    by_cases hyTop : y = ⊤
    · rw [hyTop]; exact le_top
    · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hyTop
      subst hk
      have hk_spec := Nat.find_min' h_exists hy
      exact WithTop.coe_le_coe.mpr hk_spec
  have h_eq : sInf S = (m0 : ℕ∞) := le_antisymm h_le_m0 h_m0_le
  rw [h_eq]
  exact hm0_in

/-- **Exercise 4.** With a four-letter description alphabet the complexity is half
the binary one, up to an additive constant. -/
theorem plainK_fourLetterAlphabet_eq_half (U : Map) (hU : isOptimalConditional U)
    (D : QMap 4) (hD : IsQOptimal D) :
    ∃ k : ℕ, ∀ x : BitString,
      2 * qPlainK D x ≤ plainK U x + (k : ℕ∞) ∧ plainK U x ≤ 2 * qPlainK D x + (k : ℕ∞) := by
  classical
  obtain ⟨c1, hc1⟩ := hD.2 (D_q U) (D_q_partrec U hU.1)
  obtain ⟨c2, hc2⟩ := hU.2 (D_bin D) (D_bin_partrec D hD.1)
  use 2 * c1 + 3 + c2
  intro x
  have h1 : 2 * qPlainK D x ≤ plainK U x + ((2 * c1 + 3 + c2 : ℕ) : ℕ∞) := by
    have hDq : qPlainK D x ≤ qCondK (D_q U) x [] + (c1 : ℕ∞) := hc1 x []
    have h2Dq : 2 * qPlainK D x ≤ 2 * qCondK (D_q U) x [] + 2 * (c1 : ℕ∞) := by
      calc 2 * qPlainK D x ≤ 2 * (qCondK (D_q U) x [] + (c1 : ℕ∞)) := mul_le_mul_right hDq 2
      _ = 2 * qCondK (D_q U) x [] + 2 * (c1 : ℕ∞) := mul_add 2 (qCondK (D_q U) x []) (c1 : ℕ∞)
    have h_qU : 2 * qCondK (D_q U) x [] ≤ plainK U x + 3 := by
      dsimp [plainK, condK, candidateLengths, produces, qCondK]
      let S := {n : ℕ∞ | ∃ p : BitString, x ∈ U (p, []) ∧ (programLength p : ℕ∞) = n}
      by_cases hS : S.Nonempty
      · have hTop : ⊤ ∉ S := by
          rintro ⟨p, hpx, hpTop⟩
          exact WithTop.coe_ne_top hpTop
        have hmem := enat_sInf_mem hS hTop
        dsimp [S] at hmem
        obtain ⟨p_opt, h_p_opt, h_len_eq⟩ := hmem
        by_cases h_even : p_opt.length % 2 = 0
        · let p_q : List (Fin 4) := 0 :: bitsToFin4List p_opt
          have h_in : x ∈ D_q U (p_q, []) := by
            change x ∈ (if (0 : Fin 4) = 0 then U (fin4ListToBits (bitsToFin4List p_opt), [])
              else if (0 : Fin 4) = 1 then U ((fin4ListToBits (bitsToFin4List p_opt)).dropLast, [])
              else Part.none)
            rw [if_pos rfl]
            have h_bits : fin4ListToBits (bitsToFin4List p_opt) = p_opt :=
              fin4ListToBits_bitsToFin4List_of_even p_opt h_even
            rw [h_bits]
            exact h_p_opt
          have h_pq_len : p_q.length = p_opt.length / 2 + 1 := by
            dsimp [p_q]
            rw [bitsToFin4List_length_of_even p_opt h_even]
          have h_le_pq : qCondK (D_q U) x [] ≤ (p_q.length : ℕ∞) := by
            apply sInf_le
            use p_q
          have h_2_pq : 2 * (p_q.length : ℕ∞) = (2 * p_q.length : ℕ) := by push_cast; rfl
          have h_pq_bound : 2 * p_q.length ≤ p_opt.length + 2 := by
            rw [h_pq_len]
            omega
          calc 2 * qCondK (D_q U) x [] ≤ 2 * (p_q.length : ℕ∞) := mul_le_mul_right h_le_pq 2
          _ = (2 * p_q.length : ℕ∞) := h_2_pq
          _ ≤ ((p_opt.length + 2 : ℕ) : ℕ∞) := WithTop.coe_le_coe.mpr h_pq_bound
          _ = (p_opt.length : ℕ∞) + 2 := by push_cast; rfl
          _ = sInf S + 2 := by rw [← h_len_eq]
          _ ≤ sInf S + 3 := add_le_add_right (by norm_num) (sInf S)
        · let p_opt' := p_opt ++ [false]
          have h_opt'_len : p_opt'.length = p_opt.length + 1 := by
            dsimp [p_opt']; rw [List.length_append]; rfl
          have h_opt'_even : p_opt'.length % 2 = 0 := by rw [h_opt'_len]; omega
          let p_q : List (Fin 4) := 1 :: bitsToFin4List p_opt'
          have h_in : x ∈ D_q U (p_q, []) := by
            change x ∈ (if (1 : Fin 4) = 0 then U (fin4ListToBits (bitsToFin4List p_opt'), [])
              else if (1 : Fin 4) = 1 then
                U ((fin4ListToBits (bitsToFin4List p_opt')).dropLast, [])
              else Part.none)
            have h01 : ¬(1 : Fin 4) = 0 := by decide
            rw [if_neg h01, if_pos rfl]
            have h_bits : fin4ListToBits (bitsToFin4List p_opt') = p_opt' :=
              fin4ListToBits_bitsToFin4List_of_even p_opt' h_opt'_even
            rw [h_bits]
            dsimp [p_opt']
            have h_drop : (p_opt ++ [false]).dropLast = p_opt := List.dropLast_concat
            rw [h_drop]
            exact h_p_opt
          have h_pq_len : p_q.length = (p_opt.length + 1) / 2 + 1 := by
            dsimp [p_q]
            rw [bitsToFin4List_length_of_even p_opt' h_opt'_even, h_opt'_len]
          have h_le_pq : qCondK (D_q U) x [] ≤ (p_q.length : ℕ∞) := by
            apply sInf_le
            use p_q
          have h_2_pq : 2 * (p_q.length : ℕ∞) = (2 * p_q.length : ℕ) := by push_cast; rfl
          have h_pq_bound : 2 * p_q.length ≤ p_opt.length + 3 := by
            rw [h_pq_len]
            omega
          calc 2 * qCondK (D_q U) x [] ≤ 2 * (p_q.length : ℕ∞) := mul_le_mul_right h_le_pq 2
          _ = (2 * p_q.length : ℕ∞) := h_2_pq
          _ ≤ ((p_opt.length + 3 : ℕ) : ℕ∞) := WithTop.coe_le_coe.mpr h_pq_bound
          _ = (p_opt.length : ℕ∞) + 3 := by push_cast; rfl
          _ = sInf S + 3 := by rw [← h_len_eq]
      · have h_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
        have h_inf : sInf S = ⊤ := by rw [h_empty]; exact sInf_empty
        rw [h_inf]
        exact le_top
    calc 2 * qPlainK D x ≤ 2 * qCondK (D_q U) x [] + 2 * (c1 : ℕ∞) := h2Dq
    _ ≤ plainK U x + 3 + 2 * (c1 : ℕ∞) := add_le_add_left h_qU _
    _ = plainK U x + (2 * (c1 : ℕ∞) + 3) := by rw [add_assoc, add_comm 3 (2 * (c1 : ℕ∞))]
    _ ≤ plainK U x + ((2 * c1 + 3 + c2 : ℕ) : ℕ∞) := by
      have h_le : 2 * (c1 : ℕ∞) + 3 ≤ ((2 * c1 + 3 + c2 : ℕ) : ℕ∞) := by
        have h_eq_cast : 2 * (c1 : ℕ∞) + 3 = ((2 * c1 + 3 : ℕ) : ℕ∞) := by push_cast; rfl
        rw [h_eq_cast]
        exact WithTop.coe_le_coe.mpr (by omega)
      exact add_le_add_right h_le (plainK U x)
  have h2 : plainK U x ≤ 2 * qPlainK D x + ((2 * c1 + 3 + c2 : ℕ) : ℕ∞) := by
    have hU_bin : condK U x [] ≤ condK (D_bin D) x [] + (c2 : ℕ∞) := hc2 x []
    have h_bin : condK (D_bin D) x [] ≤ 2 * qPlainK D x := by
      dsimp [qPlainK, qCondK]
      let S := {n : ℕ∞ | ∃ p : List (Fin 4), x ∈ D (p, []) ∧ (p.length : ℕ∞) = n}
      by_cases hS : S.Nonempty
      · have hTop : ⊤ ∉ S := by
          rintro ⟨p, hpx, hpTop⟩
          exact WithTop.coe_ne_top hpTop
        have hmem := enat_sInf_mem hS hTop
        dsimp [S] at hmem
        obtain ⟨p_opt, h_p_opt, h_len_eq⟩ := hmem
        let p_bin := fin4ListToBits p_opt
        have h_even : p_bin.length % 2 = 0 := by
          dsimp [p_bin]
          rw [fin4ListToBits_length]
          omega
        have h_in : x ∈ D_bin D (p_bin, []) := by
          dsimp [D_bin]
          rw [if_pos h_even]
          dsimp [p_bin]
          rw [bitsToFin4List_fin4ListToBits]
          exact h_p_opt
        have h_le_bin : condK (D_bin D) x [] ≤ (p_bin.length : ℕ∞) := by
          apply sInf_le
          use p_bin
        have h_bin_len : (p_bin.length : ℕ∞) = 2 * (p_opt.length : ℕ∞) := by
          dsimp [p_bin]
          rw [fin4ListToBits_length]
          push_cast
          rfl
        calc condK (D_bin D) x [] ≤ (p_bin.length : ℕ∞) := h_le_bin
        _ = 2 * (p_opt.length : ℕ∞) := h_bin_len
        _ = 2 * sInf S := by rw [← h_len_eq]
      · have h_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
        have h_inf : sInf S = ⊤ := by rw [h_empty]; exact sInf_empty
        rw [h_inf]
        exact le_top
    calc plainK U x ≤ condK (D_bin D) x [] + (c2 : ℕ∞) := hU_bin
    _ ≤ 2 * qPlainK D x + (c2 : ℕ∞) := add_le_add_left h_bin _
    _ ≤ 2 * qPlainK D x + ((2 * c1 + 3 + c2 : ℕ) : ℕ∞) := by
      have h_le : (c2 : ℕ∞) ≤ ((2 * c1 + 3 + c2 : ℕ) : ℕ∞) := WithTop.coe_le_coe.mpr (by omega)
      exact add_le_add_right h_le (2 * qPlainK D x)
  exact ⟨h1, h2⟩

end Kolmogorov
