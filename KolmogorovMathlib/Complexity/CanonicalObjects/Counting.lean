import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.BusyBeaver
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.Complexity.PairComplexity.Basic
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.MonotoneComplexity.Dimension.DilutionCode
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Reduce
import Mathlib.Data.Nat.Dist

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-! ### Exercises -/

private noncomputable def lipAddDecompressor (U : Map) : Map := fun pr =>
  (U (pr.1.drop ((pr.1.takeWhile id).length + 1), [])).bind
    (fun x => Part.some (Nat.bits (decodeBits x + (pr.1.takeWhile id).length)))

private lemma lipAddDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (lipAddDecompressor U) := by
  have h_drop : Computable (fun pr : BitString × BitString =>
      pr.1.drop ((pr.1.takeWhile id).length + 1)) := by
    have h_len : Primrec (fun pr : BitString × BitString =>
        (pr.1.takeWhile id).length) :=
      Primrec.list_length.comp ((Primrec.list_takeWhile Primrec.id).comp Primrec.fst)
    have h_add : Primrec (fun pr : BitString × BitString =>
        (pr.1.takeWhile id).length + 1) :=
      Primrec.nat_add.comp h_len (Primrec.const 1)
    exact (Primrec.list_drop.comp h_add Primrec.fst).to_comp
  have h_U : Partrec (fun pr : BitString × BitString =>
      U (pr.1.drop ((pr.1.takeWhile id).length + 1), [])) :=
    Partrec.comp hU (Computable.pair h_drop (Computable.const []))
  have h_g : Computable (fun (p : (BitString × BitString) × BitString) =>
      Nat.bits (decodeBits p.2 + (p.1.1.takeWhile id).length)) := by
    have h_dec : Primrec (fun (p : (BitString × BitString) × BitString) =>
        decodeBits p.2) :=
      primrec_decodeBits.comp Primrec.snd
    have h_len : Primrec (fun (p : (BitString × BitString) × BitString) =>
        (p.1.1.takeWhile id).length) :=
      Primrec.list_length.comp
        ((Primrec.list_takeWhile Primrec.id).comp (Primrec.fst.comp Primrec.fst))
    have h_add : Primrec (fun (p : (BitString × BitString) × BitString) =>
        decodeBits p.2 + (p.1.1.takeWhile id).length) :=
      Primrec.nat_add.comp h_dec h_len
    exact (primrec_natBits.comp h_add).to_comp
  exact Partrec.bind h_U (Partrec.some.comp h_g)

private lemma drop_replicate_true_false_append (d : ℕ) (p : BitString) :
    (List.replicate d true ++ false :: p).drop (d + 1) = p := by
  have h : List.replicate d true ++ false :: p = (List.replicate d true ++ [false]) ++ p := by simp
  rw [h]
  have hlen : (List.replicate d true ++ [false]).length = d + 1 := by simp
  rw [← hlen]
  exact List.drop_left

private noncomputable def lipSubDecompressor (U : Map) : Map := fun pr =>
  (U (pr.1.drop ((pr.1.takeWhile id).length + 1), [])).bind
    (fun x => Part.some (Nat.bits (decodeBits x - (pr.1.takeWhile id).length)))

private lemma lipSubDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (lipSubDecompressor U) := by
  have h_drop : Computable (fun pr : BitString × BitString =>
      pr.1.drop ((pr.1.takeWhile id).length + 1)) := by
    have h_len : Primrec (fun pr : BitString × BitString =>
        (pr.1.takeWhile id).length) :=
      Primrec.list_length.comp ((Primrec.list_takeWhile Primrec.id).comp Primrec.fst)
    have h_add : Primrec (fun pr : BitString × BitString =>
        (pr.1.takeWhile id).length + 1) :=
      Primrec.nat_add.comp h_len (Primrec.const 1)
    exact (Primrec.list_drop.comp h_add Primrec.fst).to_comp
  have h_U : Partrec (fun pr : BitString × BitString =>
      U (pr.1.drop ((pr.1.takeWhile id).length + 1), [])) :=
    Partrec.comp hU (Computable.pair h_drop (Computable.const []))
  have h_g : Computable (fun (p : (BitString × BitString) × BitString) =>
      Nat.bits (decodeBits p.2 - (p.1.1.takeWhile id).length)) := by
    have h_dec : Primrec (fun (p : (BitString × BitString) × BitString) =>
        decodeBits p.2) :=
      primrec_decodeBits.comp Primrec.snd
    have h_len : Primrec (fun (p : (BitString × BitString) × BitString) =>
        (p.1.1.takeWhile id).length) :=
      Primrec.list_length.comp
        ((Primrec.list_takeWhile Primrec.id).comp (Primrec.fst.comp Primrec.fst))
    have h_sub : Primrec (fun (p : (BitString × BitString) × BitString) =>
        decodeBits p.2 - (p.1.1.takeWhile id).length) :=
      Primrec.nat_sub.comp h_dec h_len
    exact (primrec_natBits.comp h_sub).to_comp
  exact Partrec.bind h_U (Partrec.some.comp h_g)

/-- The plain complexities of two numbers differ by at most their distance plus a constant. -/
theorem plainK_dist_le (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ m n : ℕ, plainKNat U m ≤ plainKNat U n + ((Nat.dist m n + k : ℕ) : ℕ∞) := by
  obtain ⟨c_add, hc_add⟩ := hU.2 (lipAddDecompressor U) (lipAddDecompressor_isDecompressor U hU.1)
  obtain ⟨c_sub, hc_sub⟩ := hU.2 (lipSubDecompressor U) (lipSubDecompressor_isDecompressor U hU.1)
  use max (1 + c_add) (1 + c_sub)
  intro m n
  unfold plainKNat
  rcases le_total n m with hle | hlt
  · set d := m - n
    have hmd : m = n + d := (Nat.add_sub_cancel' hle).symm
    have hdist : Nat.dist m n = d := Nat.dist_eq_sub_of_le_right hle
    rw [hdist]
    have h_bound : plainK U (Nat.bits m) ≤ plainK U (Nat.bits n) + ((d + 1 + c_add : ℕ) : ℕ∞) := by
      cases hK : plainK U (Nat.bits n) with
      | top => simp
      | coe N =>
        have hK_le : condK U (Nat.bits n) [] ≤ (N : ℕ∞) := hK.le
        rw [condK_le_iff] at hK_le
        obtain ⟨p, hp_len, hp_prod⟩ := hK_le
        set w := List.replicate d true ++ false :: p
        have hw_len : programLength w = d + 1 + programLength p := by
          simp [programLength, w, List.length_append]; omega
        have h_drop_eq : w.drop ((w.takeWhile id).length + 1) = p := by
          dsimp [w]
          rw [takeWhile_id_replicate, List.length_replicate,
            drop_replicate_true_false_append]
        have hw_prod : Nat.bits m ∈ lipAddDecompressor U (w, []) := by
          unfold lipAddDecompressor
          dsimp
          rw [h_drop_eq]
          refine Part.mem_bind hp_prod ?_
          dsimp [w]
          rw [takeWhile_id_replicate, List.length_replicate]
          rw [decodeBits_natBits, ← hmd]
          exact Part.mem_some _
        have h_lip_le : plainK (lipAddDecompressor U) (Nat.bits m) ≤ ((d + 1 + N : ℕ) : ℕ∞) := by
          change condK (lipAddDecompressor U) (Nat.bits m) [] ≤ ((d + 1 + N : ℕ) : ℕ∞)
          rw [condK_le_iff]
          exact ⟨w, by omega, hw_prod⟩
        have h_opt := hc_add (Nat.bits m) []
        calc plainK U (Nat.bits m)
          _ ≤ plainK (lipAddDecompressor U) (Nat.bits m) + (c_add : ℕ∞) := h_opt
          _ ≤ ((d + 1 + N : ℕ) : ℕ∞) + (c_add : ℕ∞) := by gcongr
          _ = (N : ℕ∞) + ((d + 1 + c_add : ℕ) : ℕ∞) := by push_cast; ring
    have h_le : d + 1 + c_add ≤ d + max (1 + c_add) (1 + c_sub) := by omega
    have h_le' : ((d + 1 + c_add : ℕ) : ℕ∞) ≤ ((d + max (1 + c_add) (1 + c_sub) : ℕ) : ℕ∞) := by
      exact_mod_cast h_le
    calc plainK U (Nat.bits m)
      _ ≤ plainK U (Nat.bits n) + ((d + 1 + c_add : ℕ) : ℕ∞) := h_bound
      _ ≤ plainK U (Nat.bits n) + ((d + max (1 + c_add) (1 + c_sub) : ℕ) : ℕ∞) :=
        add_le_add_right h_le' _
  · have hle : m ≤ n := hlt
    set d := n - m
    have hmd : m = n - d := (Nat.sub_sub_self hle).symm
    have hdist : Nat.dist m n = d := Nat.dist_eq_sub_of_le hle
    rw [hdist]
    have h_bound : plainK U (Nat.bits m) ≤ plainK U (Nat.bits n) + ((d + 1 + c_sub : ℕ) : ℕ∞) := by
      cases hK : plainK U (Nat.bits n) with
      | top => simp
      | coe N =>
        have hK_le : condK U (Nat.bits n) [] ≤ (N : ℕ∞) := hK.le
        rw [condK_le_iff] at hK_le
        obtain ⟨p, hp_len, hp_prod⟩ := hK_le
        set w := List.replicate d true ++ false :: p
        have hw_len : programLength w = d + 1 + programLength p := by
          simp [programLength, w, List.length_append]; omega
        have h_drop_eq : w.drop ((w.takeWhile id).length + 1) = p := by
          dsimp [w]
          rw [takeWhile_id_replicate, List.length_replicate,
            drop_replicate_true_false_append]
        have hw_prod : Nat.bits m ∈ lipSubDecompressor U (w, []) := by
          unfold lipSubDecompressor
          dsimp
          rw [h_drop_eq]
          refine Part.mem_bind hp_prod ?_
          dsimp [w]
          rw [takeWhile_id_replicate, List.length_replicate]
          rw [decodeBits_natBits, ← hmd]
          exact Part.mem_some _
        have h_lip_le : plainK (lipSubDecompressor U) (Nat.bits m) ≤ ((d + 1 + N : ℕ) : ℕ∞) := by
          change condK (lipSubDecompressor U) (Nat.bits m) [] ≤ ((d + 1 + N : ℕ) : ℕ∞)
          rw [condK_le_iff]
          exact ⟨w, by omega, hw_prod⟩
        have h_opt := hc_sub (Nat.bits m) []
        calc plainK U (Nat.bits m)
          _ ≤ plainK (lipSubDecompressor U) (Nat.bits m) + (c_sub : ℕ∞) := h_opt
          _ ≤ ((d + 1 + N : ℕ) : ℕ∞) + (c_sub : ℕ∞) := by gcongr
          _ = (N : ℕ∞) + ((d + 1 + c_sub : ℕ) : ℕ∞) := by push_cast; ring
    have h_le : d + 1 + c_sub ≤ d + max (1 + c_add) (1 + c_sub) := by omega
    have h_le' : ((d + 1 + c_sub : ℕ) : ℕ∞) ≤ ((d + max (1 + c_add) (1 + c_sub) : ℕ) : ℕ∞) := by
      exact_mod_cast h_le
    calc plainK U (Nat.bits m)
      _ ≤ plainK U (Nat.bits n) + ((d + 1 + c_sub : ℕ) : ℕ∞) := h_bound
      _ ≤ plainK U (Nat.bits n) + ((d + max (1 + c_add) (1 + c_sub) : ℕ) : ℕ∞) :=
        add_le_add_right h_le' _

private noncomputable def logAddDecompressor (U : Map) : Map := fun pr =>
  let L := (pr.1.takeWhile id).length
  let rest1 := pr.1.drop (L + 1)
  let x := rest1.take L
  let p := rest1.drop L
  (U (p, [])).bind
    (fun x_out => Part.some (Nat.bits (decodeBits x_out + decodeBits x)))

private lemma logAddDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (logAddDecompressor U) := by
  have h_L : Primrec (fun pr : BitString × BitString =>
      (pr.1.takeWhile id).length) :=
    Primrec.list_length.comp ((Primrec.list_takeWhile Primrec.id).comp Primrec.fst)
  have h_rest1 : Primrec (fun pr : BitString × BitString =>
      pr.1.drop ((pr.1.takeWhile id).length + 1)) :=
    Primrec.list_drop.comp (Primrec.nat_add.comp h_L (Primrec.const 1)) Primrec.fst
  have h_x : Primrec (fun pr : BitString × BitString =>
      (pr.1.drop ((pr.1.takeWhile id).length + 1)).take (pr.1.takeWhile id).length) :=
    Primrec.list_take.comp h_L h_rest1
  have h_p : Primrec (fun pr : BitString × BitString =>
      (pr.1.drop ((pr.1.takeWhile id).length + 1)).drop (pr.1.takeWhile id).length) :=
    Primrec.list_drop.comp h_L h_rest1
  have h_U : Partrec (fun pr : BitString × BitString =>
      U ((pr.1.drop ((pr.1.takeWhile id).length + 1)).drop (pr.1.takeWhile id).length, [])) :=
    Partrec.comp hU (Computable.pair h_p.to_comp (Computable.const []))
  have h_dec_x : Primrec (fun pr : BitString × BitString =>
      decodeBits ((pr.1.drop ((pr.1.takeWhile id).length + 1)).take (pr.1.takeWhile id).length)) :=
    primrec_decodeBits.comp h_x
  have h_g : Computable (fun (p_in : (BitString × BitString) × BitString) =>
      Nat.bits (decodeBits p_in.2 +
        decodeBits ((p_in.1.1.drop ((p_in.1.1.takeWhile id).length + 1)).take
          (p_in.1.1.takeWhile id).length))) := by
    have h_dec_out : Primrec (fun (p_in : (BitString × BitString) × BitString) =>
        decodeBits p_in.2) :=
      primrec_decodeBits.comp Primrec.snd
    have h_add : Primrec (fun (p_in : (BitString × BitString) × BitString) =>
        decodeBits p_in.2 +
        decodeBits ((p_in.1.1.drop ((p_in.1.1.takeWhile id).length + 1)).take
          (p_in.1.1.takeWhile id).length)) :=
      Primrec.nat_add.comp h_dec_out (h_dec_x.comp Primrec.fst)
    exact (primrec_natBits.comp h_add).to_comp
  exact Partrec.bind h_U (Partrec.some.comp h_g)

private noncomputable def logSubDecompressor (U : Map) : Map := fun pr =>
  let L := (pr.1.takeWhile id).length
  let rest1 := pr.1.drop (L + 1)
  let x := rest1.take L
  let p := rest1.drop L
  (U (p, [])).bind
    (fun x_out => Part.some (Nat.bits (decodeBits x_out - decodeBits x)))

private lemma logSubDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (logSubDecompressor U) := by
  have h_L : Primrec (fun pr : BitString × BitString =>
      (pr.1.takeWhile id).length) :=
    Primrec.list_length.comp ((Primrec.list_takeWhile Primrec.id).comp Primrec.fst)
  have h_rest1 : Primrec (fun pr : BitString × BitString =>
      pr.1.drop ((pr.1.takeWhile id).length + 1)) :=
    Primrec.list_drop.comp (Primrec.nat_add.comp h_L (Primrec.const 1)) Primrec.fst
  have h_x : Primrec (fun pr : BitString × BitString =>
      (pr.1.drop ((pr.1.takeWhile id).length + 1)).take (pr.1.takeWhile id).length) :=
    Primrec.list_take.comp h_L h_rest1
  have h_p : Primrec (fun pr : BitString × BitString =>
      (pr.1.drop ((pr.1.takeWhile id).length + 1)).drop (pr.1.takeWhile id).length) :=
    Primrec.list_drop.comp h_L h_rest1
  have h_U : Partrec (fun pr : BitString × BitString =>
      U ((pr.1.drop ((pr.1.takeWhile id).length + 1)).drop (pr.1.takeWhile id).length, [])) :=
    Partrec.comp hU (Computable.pair h_p.to_comp (Computable.const []))
  have h_dec_x : Primrec (fun pr : BitString × BitString =>
      decodeBits ((pr.1.drop ((pr.1.takeWhile id).length + 1)).take (pr.1.takeWhile id).length)) :=
    primrec_decodeBits.comp h_x
  have h_g : Computable (fun (p_in : (BitString × BitString) × BitString) =>
      Nat.bits (decodeBits p_in.2 -
        decodeBits ((p_in.1.1.drop ((p_in.1.1.takeWhile id).length + 1)).take
          (p_in.1.1.takeWhile id).length))) := by
    have h_dec_out : Primrec (fun (p_in : (BitString × BitString) × BitString) =>
        decodeBits p_in.2) :=
      primrec_decodeBits.comp Primrec.snd
    have h_sub : Primrec (fun (p_in : (BitString × BitString) × BitString) =>
        decodeBits p_in.2 -
        decodeBits ((p_in.1.1.drop ((p_in.1.1.takeWhile id).length + 1)).take
          (p_in.1.1.takeWhile id).length)) :=
      Primrec.nat_sub.comp h_dec_out (h_dec_x.comp Primrec.fst)
    exact (primrec_natBits.comp h_sub).to_comp
  exact Partrec.bind h_U (Partrec.some.comp h_g)

private lemma takeWhile_id_pairCode (x p : BitString) :
    ((pairCode x p).takeWhile id).length = x.length := by
  unfold pairCode natCode
  have h : List.replicate x.length true ++ [false] ++ x ++ p =
      List.replicate x.length true ++ false :: (x ++ p) := by simp
  rw [h, takeWhile_id_replicate, List.length_replicate]

private lemma drop_takeWhile_id_add_one_pairCode (x p : BitString) :
    (pairCode x p).drop (((pairCode x p).takeWhile id).length + 1) = x ++ p := by
  unfold pairCode natCode
  have h : List.replicate x.length true ++ [false] ++ x ++ p =
      List.replicate x.length true ++ false :: (x ++ p) := by simp
  rw [h, takeWhile_id_replicate, List.length_replicate]
  exact drop_replicate_true_false_append x.length (x ++ p)

/-- **Exercise 1, logarithmic form.** `|C(m) - C(n)| ≤ 2 log |m - n| + O(1)` for
`m ≠ n`. -/
theorem plainK_sub_plainK_le_two_log (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ m n : ℕ, m ≠ n →
      plainKNat U m ≤ plainKNat U n + ((2 * Nat.log 2 (Nat.dist m n) + k : ℕ) : ℕ∞) := by
  obtain ⟨c_add, hc_add⟩ := hU.2 (logAddDecompressor U) (logAddDecompressor_isDecompressor U hU.1)
  obtain ⟨c_sub, hc_sub⟩ := hU.2 (logSubDecompressor U) (logSubDecompressor_isDecompressor U hU.1)
  use max (3 + c_add) (3 + c_sub)
  intro m n hne
  unfold plainKNat
  rcases le_total n m with hle | hlt
  · have hgt : m > n := lt_of_le_of_ne hle (Ne.symm hne)
    set d := m - n
    have hdpos : d > 0 := by omega
    have hmd : m = n + d := (Nat.add_sub_cancel' hle).symm
    have hdist : Nat.dist m n = d := Nat.dist_eq_sub_of_le_right hle
    rw [hdist]
    have h_bound : plainK U (Nat.bits m) ≤
        plainK U (Nat.bits n) + ((2 * Nat.log 2 d + 3 + c_add : ℕ) : ℕ∞) := by
      cases hK : plainK U (Nat.bits n) with
      | top => simp
      | coe N =>
        have hK_le : condK U (Nat.bits n) [] ≤ (N : ℕ∞) := hK.le
        rw [condK_le_iff] at hK_le
        obtain ⟨p, hp_len, hp_prod⟩ := hK_le
        set x := Nat.bits d
        set w := pairCode x p
        have hw_len : programLength w ≤ programLength p + 2 * Nat.log 2 d + 3 := by
          dsimp [w, x, programLength]
          rw [length_pairCode]
          have hx_len := length_natBits_le_log d
          omega
        have h_rest1_eq : w.drop ((w.takeWhile id).length + 1) = x ++ p := by
          dsimp [w]
          exact drop_takeWhile_id_add_one_pairCode x p
        have h_x_eq : (w.drop ((w.takeWhile id).length + 1)).take (w.takeWhile id).length = x := by
          rw [h_rest1_eq]
          dsimp [w]
          rw [takeWhile_id_pairCode]
          exact List.take_left
        have h_p_eq : (w.drop ((w.takeWhile id).length + 1)).drop (w.takeWhile id).length = p := by
          rw [h_rest1_eq]
          dsimp [w]
          rw [takeWhile_id_pairCode]
          exact List.drop_left
        have hw_prod : Nat.bits m ∈ logAddDecompressor U (w, []) := by
          unfold logAddDecompressor
          dsimp
          rw [h_p_eq]
          refine Part.mem_bind hp_prod ?_
          rw [h_x_eq]
          rw [decodeBits_natBits, decodeBits_natBits, ← hmd]
          exact Part.mem_some _
        have h_log_le : plainK (logAddDecompressor U) (Nat.bits m) ≤
            ((N + 2 * Nat.log 2 d + 3 : ℕ) : ℕ∞) := by
          change condK (logAddDecompressor U) (Nat.bits m) [] ≤ ((N + 2 * Nat.log 2 d + 3 : ℕ) : ℕ∞)
          rw [condK_le_iff]
          exact ⟨w, by omega, hw_prod⟩
        have h_opt := hc_add (Nat.bits m) []
        calc plainK U (Nat.bits m)
          _ ≤ plainK (logAddDecompressor U) (Nat.bits m) + (c_add : ℕ∞) := h_opt
          _ ≤ ((N + 2 * Nat.log 2 d + 3 : ℕ) : ℕ∞) + (c_add : ℕ∞) := by gcongr
          _ = (N : ℕ∞) + ((2 * Nat.log 2 d + 3 + c_add : ℕ) : ℕ∞) := by push_cast; ring
    have h_le : 2 * Nat.log 2 d + 3 + c_add ≤ 2 * Nat.log 2 d + max (3 + c_add) (3 + c_sub) := by
      omega
    have h_le' : ((2 * Nat.log 2 d + 3 + c_add : ℕ) : ℕ∞) ≤
        ((2 * Nat.log 2 d + max (3 + c_add) (3 + c_sub) : ℕ) : ℕ∞) := by exact_mod_cast h_le
    calc plainK U (Nat.bits m)
      _ ≤ plainK U (Nat.bits n) + ((2 * Nat.log 2 d + 3 + c_add : ℕ) : ℕ∞) := h_bound
      _ ≤ plainK U (Nat.bits n) + ((2 * Nat.log 2 d + max (3 + c_add) (3 + c_sub) : ℕ) : ℕ∞) :=
        add_le_add_right h_le' _
  · have hle : m ≤ n := hlt
    have hgt : n > m := lt_of_le_of_ne hle hne
    set d := n - m
    have hdpos : d > 0 := by omega
    have hmd : m = n - d := (Nat.sub_sub_self hle).symm
    have hdist : Nat.dist m n = d := Nat.dist_eq_sub_of_le hle
    rw [hdist]
    have h_bound : plainK U (Nat.bits m) ≤
        plainK U (Nat.bits n) + ((2 * Nat.log 2 d + 3 + c_sub : ℕ) : ℕ∞) := by
      cases hK : plainK U (Nat.bits n) with
      | top => simp
      | coe N =>
        have hK_le : condK U (Nat.bits n) [] ≤ (N : ℕ∞) := hK.le
        rw [condK_le_iff] at hK_le
        obtain ⟨p, hp_len, hp_prod⟩ := hK_le
        set x := Nat.bits d
        set w := pairCode x p
        have hw_len : programLength w ≤ programLength p + 2 * Nat.log 2 d + 3 := by
          dsimp [w, x, programLength]
          rw [length_pairCode]
          have hx_len := length_natBits_le_log d
          omega
        have h_rest1_eq : w.drop ((w.takeWhile id).length + 1) = x ++ p := by
          dsimp [w]
          exact drop_takeWhile_id_add_one_pairCode x p
        have h_x_eq : (w.drop ((w.takeWhile id).length + 1)).take (w.takeWhile id).length = x := by
          rw [h_rest1_eq]
          dsimp [w]
          rw [takeWhile_id_pairCode]
          exact List.take_left
        have h_p_eq : (w.drop ((w.takeWhile id).length + 1)).drop (w.takeWhile id).length = p := by
          rw [h_rest1_eq]
          dsimp [w]
          rw [takeWhile_id_pairCode]
          exact List.drop_left
        have hw_prod : Nat.bits m ∈ logSubDecompressor U (w, []) := by
          unfold logSubDecompressor
          dsimp
          rw [h_p_eq]
          refine Part.mem_bind hp_prod ?_
          rw [h_x_eq]
          rw [decodeBits_natBits, decodeBits_natBits, ← hmd]
          exact Part.mem_some _
        have h_log_le : plainK (logSubDecompressor U) (Nat.bits m) ≤
            ((N + 2 * Nat.log 2 d + 3 : ℕ) : ℕ∞) := by
          change condK (logSubDecompressor U) (Nat.bits m) [] ≤ ((N + 2 * Nat.log 2 d + 3 : ℕ) : ℕ∞)
          rw [condK_le_iff]
          exact ⟨w, by omega, hw_prod⟩
        have h_opt := hc_sub (Nat.bits m) []
        calc plainK U (Nat.bits m)
          _ ≤ plainK (logSubDecompressor U) (Nat.bits m) + (c_sub : ℕ∞) := h_opt
          _ ≤ ((N + 2 * Nat.log 2 d + 3 : ℕ) : ℕ∞) + (c_sub : ℕ∞) := by gcongr
          _ = (N : ℕ∞) + ((2 * Nat.log 2 d + 3 + c_sub : ℕ) : ℕ∞) := by push_cast; ring
    have h_le : 2 * Nat.log 2 d + 3 + c_sub ≤ 2 * Nat.log 2 d + max (3 + c_add) (3 + c_sub) := by
      omega
    have h_le' : ((2 * Nat.log 2 d + 3 + c_sub : ℕ) : ℕ∞) ≤
        ((2 * Nat.log 2 d + max (3 + c_add) (3 + c_sub) : ℕ) : ℕ∞) := by exact_mod_cast h_le
    calc plainK U (Nat.bits m)
      _ ≤ plainK U (Nat.bits n) + ((2 * Nat.log 2 d + 3 + c_sub : ℕ) : ℕ∞) := h_bound
      _ ≤ plainK U (Nat.bits n) + ((2 * Nat.log 2 d + max (3 + c_add) (3 + c_sub) : ℕ) : ℕ∞) :=
        add_le_add_right h_le' _

open Classical in
private lemma plainK_lt_imp_exists_program (U : Map) (x : BitString) (n : ℕ)
    (h : plainK U x < (n : ℕ∞)) :
    ∃ p : BitString, p.length ≤ n - 1 ∧ x ∈ U (p, []) := by
  by_cases hn : n = 0
  · subst hn
    have : ¬ (plainK U x < (0 : ℕ∞)) := by simp
    contradiction
  · have h_le : plainK U x ≤ ((n - 1 : ℕ) : ℕ∞) := by
      cases hK : plainK U x
      · rw [hK] at h; contradiction
      · rename_i k
        have h1 : (k : ℕ∞) < (n : ℕ∞) := by
          have h_eq : plainK U x = (k : ℕ∞) := hK
          rwa [h_eq] at h
        have h2 : k < n := WithTop.coe_lt_coe.mp h1
        have h3 : k ≤ n - 1 := by omega
        exact_mod_cast h3
    exact (condK_le_iff U x [] (n - 1)).mp h_le

open Classical in
/-- **Exercise 2, first part.** The number of strings of complexity less than `n`
lies in `[2 ^ (n - c), 2 ^ n]` whenever `c ≤ n`. -/
theorem card_plainK_lt_mem_Icc (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, {x : BitString | plainK U x < (n : ℕ∞)}.Finite ∧
      (c ≤ n → 2 ^ (n - c) ≤ {x : BitString | plainK U x < (n : ℕ∞)}.ncard) ∧
      {x : BitString | plainK U x < (n : ℕ∞)}.ncard ≤ 2 ^ n := by
  obtain ⟨c, hc⟩ := plainK_le_length U hU
  use c + 1
  intro n
  by_cases hn : n = 0
  · subst hn
    have h_empty : {x : BitString | plainK U x < (0 : ℕ∞)} = ∅ := by
      ext x; simp
    have hfin : {x : BitString | plainK U x < ((0 : ℕ) : ℕ∞)}.Finite := by
      have : ((0 : ℕ) : ℕ∞) = 0 := rfl
      rw [this, h_empty]
      exact Set.finite_empty
    refine ⟨hfin, fun hcn => ?_, ?_⟩
    · omega
    · have : ((0 : ℕ) : ℕ∞) = 0 := rfl
      rw [this, h_empty, Set.ncard_empty]
      decide
  · set S := {x : BitString | plainK U x < (n : ℕ∞)}
    have h_prog : ∀ x ∈ S, ∃ p ∈ boundedPrograms (n - 1), x ∈ U (p, []) := by
      intro x hx
      obtain ⟨p, hp_len, hp_prod⟩ := plainK_lt_imp_exists_program U x n hx
      exact ⟨p, (mem_boundedPrograms_iff p (n - 1)).mpr hp_len, hp_prod⟩
    let progOf (x : BitString) : BitString :=
      if hx : x ∈ S then Classical.choose (h_prog x hx) else []
    have hprogOf_spec : ∀ x ∈ S, progOf x ∈ boundedPrograms (n - 1) ∧ x ∈ U (progOf x, []) := by
      intro x hx
      dsimp [progOf]
      rw [dif_pos hx]
      exact Classical.choose_spec (h_prog x hx)
    have hprogOf_inj : ∀ x ∈ S, ∀ y ∈ S, progOf x = progOf y → x = y := by
      intro x hx y hy heq
      have hx_spec := hprogOf_spec x hx
      have hy_spec := hprogOf_spec y hy
      rw [heq] at hx_spec
      have h1 : x ∈ U (progOf y, []) := hx_spec.2
      have h2 : y ∈ U (progOf y, []) := hy_spec.2
      exact Part.mem_unique h1 h2
    have hmaps : Set.MapsTo progOf S (boundedPrograms (n - 1)).toFinset := by
      intro x hx
      simp only [Finset.mem_coe, List.mem_toFinset]
      exact (hprogOf_spec x hx).1
    have hfin : S.Finite := Set.Finite.of_injOn hmaps hprogOf_inj (Finset.finite_toSet _)
    refine ⟨hfin, fun hcn => ?_, ?_⟩
    · set m := n - (c + 1)
      have hm : m + c < n := by omega
      have h_sub : {x : BitString | x.length = m} ⊆ S := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx
        change plainK U x < (n : ℕ∞)
        calc plainK U x
          _ ≤ (x.length : ℕ∞) + (c : ℕ∞) := hc x
          _ = (m + c : ℕ) := by push_cast; rw [hx]
          _ < (n : ℕ∞) := WithTop.coe_lt_coe.mpr hm
      have h_set_eq : {x : BitString | x.length = m} = (stringsOfLength m : Set BitString) := by
        ext x; simp [stringsOfLength]
      have hcard_len : {x : BitString | x.length = m}.ncard = 2 ^ m := by
        rw [h_set_eq, Set.ncard_coe_finset]
        exact card_stringsOfLength m
      rw [← hcard_len]
      exact Set.ncard_le_ncard h_sub hfin
    · have h_card_le : S.ncard ≤ (boundedPrograms (n - 1)).length := by
        rw [Set.ncard_eq_toFinset_card S hfin]
        have h_maps_finset : Set.MapsTo progOf hfin.toFinset
            (boundedPrograms (n - 1)).toFinset := by
          intro x hx
          have hxS : x ∈ S := hfin.mem_toFinset.mp hx
          simp only [Finset.mem_coe, List.mem_toFinset]
          exact (hprogOf_spec x hxS).1
        have h_inj_finset : Set.InjOn progOf hfin.toFinset := by
          intro x hx y hy heq
          have hxS : x ∈ S := hfin.mem_toFinset.mp hx
          have hyS : y ∈ S := hfin.mem_toFinset.mp hy
          exact hprogOf_inj x hxS y hyS heq
        have h_le_finset := Finset.card_le_card_of_injOn progOf h_maps_finset h_inj_finset
        have h_finset_card : (boundedPrograms (n - 1)).toFinset.card ≤
            (boundedPrograms (n - 1)).length :=
          List.toFinset_card_le _
        exact h_le_finset.trans h_finset_card
      have h_len : (boundedPrograms (n - 1)).length < 2 ^ n := by
        have h_sub : n - 1 + 1 = n := by omega
        have h_lt := length_boundedPrograms_lt (n - 1)
        rwa [h_sub] at h_lt
      omega

open Classical in
private lemma plainK_eq_imp_exists_exact_program (U : Map) (x : BitString) (n : ℕ)
    (h : plainK U x = (n : ℕ∞)) :
    ∃ p : BitString, p.length = n ∧ x ∈ U (p, []) := by
  have h_ne : plainK U x ≠ ⊤ := by rw [h]; exact WithTop.coe_ne_top
  unfold plainK condK candidateLengths at h_ne h
  have h_nonempty : {n_1 : ENat | ∃ p, x ∈ U (p, []) ∧ (p.length : ENat) = n_1}.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    rw [hc, sInf_empty] at h_ne
    contradiction
  have h_mem := csInf_mem h_nonempty
  rw [h] at h_mem
  obtain ⟨p, hp_prod, hp_len⟩ := h_mem
  refine ⟨p, ?_, hp_prod⟩
  exact WithTop.coe_inj.mp hp_len

private lemma mem_exactLengthPrograms_iff (p : BitString) (n : ℕ) :
    p ∈ exactLengthPrograms n ↔ p.length = n := by
  constructor
  · exact exactLengthPrograms_length_eq n p
  · intro h
    have h1 : p ∈ boundedPrograms n := (mem_boundedPrograms_iff p n).mpr (by omega)
    unfold boundedPrograms at h1
    simp only [List.mem_flatMap, List.mem_range] at h1
    obtain ⟨k, hk, hpk⟩ := h1
    have h2 := exactLengthPrograms_length_eq k p hpk
    rw [h] at h2
    subst h2
    exact hpk

open Classical in
/-- **Exercise 2, second part.** The number of strings of complexity exactly `n`
is at most `2 ^ n`. -/
theorem card_plainK_eq_le_pow (U : Map) (hU : isOptimalConditional U) (n : ℕ) :
    {x : BitString | plainK U x = (n : ℕ∞)}.Finite ∧
      {x : BitString | plainK U x = (n : ℕ∞)}.ncard ≤ 2 ^ n := by
  have _ := hU
  set S := {x : BitString | plainK U x = (n : ℕ∞)}
  have h_prog : ∀ x ∈ S, ∃ p ∈ exactLengthPrograms n, x ∈ U (p, []) := by
    intro x hx
    obtain ⟨p, hp_len, hp_prod⟩ := plainK_eq_imp_exists_exact_program U x n hx
    have hp_mem : p ∈ exactLengthPrograms n := (mem_exactLengthPrograms_iff p n).mpr hp_len
    exact ⟨p, hp_mem, hp_prod⟩
  let progOf (x : BitString) : BitString :=
    if hx : x ∈ S then Classical.choose (h_prog x hx) else []
  have hprogOf_spec : ∀ x ∈ S, progOf x ∈ exactLengthPrograms n ∧ x ∈ U (progOf x, []) := by
    intro x hx
    dsimp [progOf]
    rw [dif_pos hx]
    exact Classical.choose_spec (h_prog x hx)
  have hprogOf_inj : ∀ x ∈ S, ∀ y ∈ S, progOf x = progOf y → x = y := by
    intro x hx y hy heq
    have hx_spec := hprogOf_spec x hx
    have hy_spec := hprogOf_spec y hy
    rw [heq] at hx_spec
    have h1 : x ∈ U (progOf y, []) := hx_spec.2
    have h2 : y ∈ U (progOf y, []) := hy_spec.2
    exact Part.mem_unique h1 h2
  have hmaps : Set.MapsTo progOf S (exactLengthPrograms n).toFinset := by
    intro x hx
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact (hprogOf_spec x hx).1
  have hfin : S.Finite := Set.Finite.of_injOn hmaps hprogOf_inj (Finset.finite_toSet _)
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hfin]
  have h_maps_finset : Set.MapsTo progOf hfin.toFinset (exactLengthPrograms n).toFinset := by
    intro x hx
    have hxS : x ∈ S := hfin.mem_toFinset.mp hx
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact (hprogOf_spec x hxS).1
  have h_inj_finset : Set.InjOn progOf hfin.toFinset := by
    intro x hx y hy heq
    have hxS : x ∈ S := hfin.mem_toFinset.mp hx
    have hyS : y ∈ S := hfin.mem_toFinset.mp hy
    exact hprogOf_inj x hxS y hyS heq
  have h_le_finset := Finset.card_le_card_of_injOn progOf h_maps_finset h_inj_finset
  have h_finset_card : (exactLengthPrograms n).toFinset.card ≤ (exactLengthPrograms n).length :=
    List.toFinset_card_le _
  have h_exact_len : (exactLengthPrograms n).length = 2 ^ n := length_exactLengthPrograms n
  omega

end Kolmogorov

