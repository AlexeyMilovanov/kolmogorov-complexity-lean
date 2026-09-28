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
import KolmogorovMathlib.Complexity.CanonicalObjects.HubEdges
import KolmogorovMathlib.Complexity.GrowthEnumeration

/-!
# The canonical objects do not depend on the decompressor

`canonicalObject_equivalence_two_decompressors` (SUV Exercise 8): Theorem 15 still holds when
the nine objects are built from two different optimal decompressors — the objects of one are
reducible to the objects of the other.  The bridge is
`exists_partrec_busyBeaver_to_haltingList`, which recovers one machine's halting list from the
other's busy beaver, prepared by `evaln_busyBeaver_bound_spec`,
`rfind_evaln_isSome_partrec` and `filter_evaln_isSome_eq_haltingProgramsBounded`.

`busyBeaver_shift_ge_apply` (SUV Exercise 11) is the growth statement proved alongside: for
every partial computable `f`, `B(n + c) ≥ f (B n)` whenever the right-hand side is defined.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

private lemma partrec_bind_three (A1 : ℕ × BitString →. BitString) (hA1 : Partrec A1)
    (A_br : ℕ × BitString →. BitString) (hA_br : Partrec A_br)
    (A2 : ℕ × BitString →. BitString) (hA2 : Partrec A2) (k1 k_br : ℕ) :
    Partrec (fun p : ℕ × BitString =>
      (A1 p).bind (fun w1 =>
      (A_br (p.1 - k1, w1)).bind (fun w2 =>
      A2 (p.1 - k1 - k_br, w2)))) := by
  have h_sub1 : Computable (fun p : (ℕ × BitString) × BitString => p.1.1 - k1) :=
    (Primrec.to_comp Primrec.nat_sub).comp
      (Computable.pair (Computable.fst.comp Computable.fst) (Computable.const k1))
  have h_pair1 : Computable (fun p : (ℕ × BitString) × BitString => (p.1.1 - k1, p.2)) :=
    Computable.pair h_sub1 Computable.snd
  have hA_br_comp : Partrec (fun p : (ℕ × BitString) × BitString => A_br (p.1.1 - k1, p.2)) :=
    Partrec.comp hA_br h_pair1
  have h_sub2 : Computable (fun p : ((ℕ × BitString) × BitString) × BitString =>
      p.1.1.1 - k1 - k_br) :=
    (Primrec.to_comp Primrec.nat_sub).comp
      (Computable.pair
        ((Primrec.to_comp Primrec.nat_sub).comp
          (Computable.pair
            (Computable.fst.comp (Computable.fst.comp Computable.fst))
            (Computable.const k1)))
        (Computable.const k_br))
  have h_pair2 : Computable (fun p : ((ℕ × BitString) × BitString) × BitString =>
      (p.1.1.1 - k1 - k_br, p.2)) :=
    Computable.pair h_sub2 Computable.snd
  have hA2_comp : Partrec (fun p : ((ℕ × BitString) × BitString) × BitString =>
      A2 (p.1.1.1 - k1 - k_br, p.2)) :=
    Partrec.comp hA2 h_pair2
  have h_bind1 : Partrec (fun p : (ℕ × BitString) × BitString =>
      (A_br (p.1.1 - k1, p.2)).bind (fun w2 => A2 (p.1.1 - k1 - k_br, w2))) :=
    Partrec.bind hA_br_comp hA2_comp
  exact Partrec.bind hA1 h_bind1

private lemma filter_evaln_isSome_eq_haltingProgramsBounded (cV : Code) (m b0 : ℕ) (c_V : Code)
    (h1_spec : ∀ x : BitString, x.length ≤ m →
      ((Code.evaln (b0 + 1) c_V (Encodable.encode x)).isSome = true ↔
        (cV.eval (Encodable.encode (x, ([] : BitString)))).Dom)) :
    (boundedPrograms m).filter (fun x => (Code.evaln (b0 + 1) c_V (Encodable.encode x)).isSome) =
    haltingProgramsBounded cV m := by
  dsimp [haltingProgramsBounded]
  refine List.filter_congr (fun x hx => ?_)
  have hx_len : x.length ≤ m := (mem_boundedPrograms_iff x m).mp hx
  have h1_x := h1_spec x hx_len
  have h_evaln_dom : (cV.eval (Encodable.encode (x, ([] : BitString)))).Dom ↔
      ∃ s, haltsWithin cV s x = true := by
    dsimp [haltsWithin]
    constructor
    · intro hdom
      obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp hdom
      rw [Nat.Partrec.Code.eval_eq_rfindOpt] at hu
      obtain ⟨s, hs⟩ := Nat.rfindOpt_spec hu
      refine ⟨s, ?_⟩
      exact Option.isSome_iff_exists.mpr ⟨u, hs⟩
    · rintro ⟨s, hs⟩
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hs
      have h_sound := Nat.Partrec.Code.evaln_sound hu
      exact Part.dom_iff_mem.mpr ⟨u, h_sound⟩
  have h_max_spec := maxHaltingStage_spec cV m
  unfold countHalts at h_max_spec
  have h2_spec : haltsWithin cV (maxHaltingStage cV m) x = true ↔
      (cV.eval (Encodable.encode (x, ([] : BitString)))).Dom := by
    constructor
    · intro h_max
      exact h_evaln_dom.mpr ⟨maxHaltingStage cV m, h_max⟩
    · intro hdom
      obtain ⟨s, hs⟩ := h_evaln_dom.mp hdom
      by_contra hc
      rw [Bool.not_eq_true] at hc
      have h_lt : (boundedPrograms m).countP (haltsWithin cV (maxHaltingStage cV m)) <
          (boundedPrograms m).countP (haltsWithin cV (max (maxHaltingStage cV m) s)) := by
        have h_sub : ∀ p ∈ boundedPrograms m, haltsWithin cV (maxHaltingStage cV m) p = true →
            haltsWithin cV (max (maxHaltingStage cV m) s) p = true := by
          intro p _ hp
          exact haltsWithin_mono cV (le_max_left _ _) p hp
        have h_hs : haltsWithin cV (max (maxHaltingStage cV m) s) x = true :=
          haltsWithin_mono cV (le_max_right _ _) x hs
        exact countP_lt_of_witness hx hc h_hs h_sub
      have h_spec_s := h_max_spec (max (maxHaltingStage cV m) s)
      omega
  rw [Bool.eq_iff_iff]
  exact h1_x.trans h2_spec.symm

/-- Bounded natural outputs set is non-empty for sufficiently large bounds `n`. -/
private lemma exists_boundedNatOutputs_nonempty (U : Map) (hU : isOptimalConditional U) (cU : Code)
    (hcU : IsCodeFor cU U) :
    ∃ K0 : ℕ, ∀ n ≥ K0, (boundedNatOutputs cU n).Nonempty := by
  have h0 : plainKNat U 0 ≠ ⊤ := by
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    have h_top : (((Nat.bits 0).length + c : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
    intro h_inf
    have h_le := hc (Nat.bits 0)
    change plainK U (Nat.bits 0) = ⊤ at h_inf
    rw [h_inf] at h_le
    exact h_top (top_le_iff.mp h_le)
  obtain ⟨k0, hk0⟩ := WithTop.ne_top_iff_exists.mp h0
  refine ⟨k0, fun n hn => ⟨0, ?_⟩⟩
  rw [mem_boundedNatOutputs_iff_plainKNat_le hcU]
  rw [← hk0]
  exact Nat.cast_le.mpr hn

/-- Finding the first step at which code evaluation in `evaln` succeeds is partial recursive. -/
private lemma rfind_evaln_isSome_partrec (c_V : Code) :
    Partrec (fun x : BitString =>
      Nat.rfind (fun s => Part.some (Code.evaln s c_V (Encodable.encode x)).isSome)) := by
  have hpred : Primrec₂ (fun (x : BitString) (s : ℕ) =>
      (Code.evaln s c_V (Encodable.encode x)).isSome) := by
    have h1 : Primrec (fun q : BitString × ℕ => q.2) := Primrec.snd
    have h2 : Primrec (fun q : BitString × ℕ => Encodable.encode q.1) :=
      Primrec.encode.comp Primrec.fst
    have heval : Primrec (fun q : BitString × ℕ =>
        Code.evaln q.2 c_V (Encodable.encode q.1)) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (Primrec.pair (Primrec.pair h1 (Primrec.const c_V)) h2)
    exact (Primrec.option_isSome.comp heval).to₂
  exact Partrec.rfind hpred.to_comp.partrec₂

/-- Checking whether `c_V` halts within `decodeBits p.2 + 1` steps on `x` is primitive recursive
in `(p, x)`. -/
private lemma evaln_decodeBits_isSome_primrec2 (c_V : Code) :
    Primrec₂ (fun (p : ℕ × BitString) (x : BitString) =>
      (Code.evaln (decodeBits p.2 + 1) c_V (Encodable.encode x)).isSome) := by
  have h1 : Primrec (fun q : (ℕ × BitString) × BitString => decodeBits q.1.2 + 1) :=
    Primrec₂.comp Primrec.nat_add
      (primrec_decodeBits.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 1)
  have h2 : Primrec (fun q : (ℕ × BitString) × BitString => Encodable.encode q.2) :=
    Primrec.encode.comp Primrec.snd
  have heval : Primrec (fun q : (ℕ × BitString) × BitString =>
      Code.evaln (decodeBits q.1.2 + 1) c_V (Encodable.encode q.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair h1 (Primrec.const c_V)) h2)
  exact (Primrec.option_isSome.comp heval).to₂

/-- Halting of `c_V` bounded by Busy Beaver `b0 + 1` matches domain of `cV` for short strings. -/
private lemma evaln_busyBeaver_bound_spec (U V : Map) (cU cV c_V : Code)
    (hcU : IsCodeFor cU U) (hcV : IsCodeFor cV V)
    (hc_V : c_V.eval = fun n =>
      Part.bind (Part.ofOption (Encodable.decode n))
        (fun x => (V (x, ([] : BitString))).map Encodable.encode))
    (c_map c_len n b0 : ℕ)
    (hk13_le : c_len + c_map ≤ n)
    (hmap : ∀ x w, w ∈ (Nat.rfind (fun s =>
        Part.some (Code.evaln s c_V (Encodable.encode x)).isSome)).map Nat.bits →
      plainK U w ≤ plainK U x + (c_map : ℕ∞))
    (hlen : ∀ x, plainK U x ≤ ((x.length : ℕ∞) + (c_len : ℕ∞)))
    (hb0 : busyBeaver cU n = some b0)
    (x : BitString) (hx_sub : x.length ≤ n - (c_len + c_map)) :
    (Code.evaln (b0 + 1) c_V (Encodable.encode x)).isSome = true ↔
      (cV.eval (Encodable.encode (x, ([] : BitString)))).Dom := by
  have h_c_V_dom (y : BitString) : (c_V.eval (Encodable.encode y)).Dom ↔ (V (y, [])).Dom := by
    rw [hc_V]
    dsimp
    rw [Encodable.encodek]
    dsimp [Part.ofOption]
    rw [Part.bind_some]
    rfl
  have h_cV_dom (y : BitString) :
      (cV.eval (Encodable.encode (y, ([] : BitString)))).Dom ↔ (V (y, [])).Dom := by
    rw [hcV]
    dsimp
    have h1 : Encodable.encode (y, ([] : BitString)) = Nat.pair (Encodable.encode y) 0 := rfl
    rw [← h1]
    rw [Encodable.encodek]
    dsimp [Part.ofOption]
    rw [Part.bind_some]
    rfl
  have hc_V_dom (y : BitString) : (c_V.eval (Encodable.encode y)).Dom ↔
      (cV.eval (Encodable.encode (y, ([] : BitString)))).Dom :=
    (h_c_V_dom y).trans (h_cV_dom y).symm
  constructor
  · intro h_some
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h_some
    have h_sound := Nat.Partrec.Code.evaln_sound hu
    have h_c_V : (c_V.eval (Encodable.encode x)).Dom := Part.dom_iff_mem.mpr ⟨u, h_sound⟩
    exact (hc_V_dom x).mp h_c_V
  · intro hdom
    have h_c_V : (c_V.eval (Encodable.encode x)).Dom := (hc_V_dom x).mpr hdom
    obtain ⟨r_code, hr_code⟩ := Part.dom_iff_mem.mp h_c_V
    obtain ⟨s_code, hs_code⟩ := Nat.Partrec.Code.evaln_complete.mp hr_code
    have hrfind_dom : (Nat.rfind (fun s => Part.some
        (Code.evaln s c_V (Encodable.encode x)).isSome)).Dom := by
      rw [Nat.rfind_dom]
      refine ⟨s_code, ?_, fun _ => Part.some_dom _⟩
      rw [Part.mem_some_iff]
      exact (Option.isSome_iff_exists.mpr ⟨r_code, hs_code⟩).symm
    obtain ⟨s_x, hs_x⟩ := Part.dom_iff_mem.mp hrfind_dom
    have hs_x_mem : Nat.bits s_x ∈ (Nat.rfind (fun s =>
        Part.some (Code.evaln s c_V (Encodable.encode x)).isSome)).map Nat.bits := by
      dsimp
      simp only [Part.mem_map_iff]
      exact ⟨s_x, hs_x, rfl⟩
    have hs_x_spec := (Nat.mem_rfind).mp hs_x
    have hs_x_isSome : (Code.evaln s_x c_V (Encodable.encode x)).isSome = true := by
      have h1 := hs_x_spec.1
      simp only [Part.mem_some_iff] at h1
      exact h1.symm
    have hK_map := hmap x (Nat.bits s_x) hs_x_mem
    have hK_len := hlen x
    have hK_val : plainKNat U s_x ≤ ((n : ℕ) : ℕ∞) := by
      calc plainKNat U s_x = plainK U (Nat.bits s_x) := rfl
        _ ≤ plainK U x + (c_map : ℕ∞) := hK_map
        _ ≤ ((x.length : ℕ∞) + (c_len : ℕ∞)) + (c_map : ℕ∞) := by gcongr
        _ ≤ (((n - (c_len + c_map) : ℕ) : ℕ∞) + (c_len : ℕ∞)) + (c_map : ℕ∞) := by gcongr
        _ = (((n - (c_len + c_map) + (c_len + c_map) : ℕ) : ℕ∞)) := by
          push_cast
          ring
        _ ≤ ((n : ℕ) : ℕ∞) := by
          exact_mod_cast (by omega)
    have hmem_bounded : s_x ∈ boundedNatOutputs cU n :=
      (mem_boundedNatOutputs_iff_plainKNat_le hcU n s_x).mpr hK_val
    have hle_b := ((busyBeaver_some_iff cU n b0).mp hb0).2 s_x hmem_bounded
    have hs_x_le_t : s_x ≤ b0 + 1 := by omega
    obtain ⟨r_x, hr_x⟩ := Option.isSome_iff_exists.mp hs_x_isSome
    have ht_x : Code.evaln (b0 + 1) c_V (Encodable.encode x) = some r_x :=
      Nat.Partrec.Code.evaln_mono hs_x_le_t hr_x
    simp [ht_x]

private lemma exists_partrec_busyBeaver_to_haltingList (U V : Map) (hU : isOptimalConditional U)
    (hV : isOptimalConditional V) (cU cV : Code) (hcU : IsCodeFor cU U) (hcV : IsCodeFor cV V) :
    ∃ k : ℕ, ∃ A : ℕ × BitString →. BitString, Partrec A ∧
      ∀ n : ℕ, A (n, canonicalObject U cU 2 n) =
        Part.some (canonicalObject V cV 4 (n - k)) := by
  have hM : Partrec (fun x : BitString => V (x, [])) :=
    Partrec.comp hV.1 (Computable.pair Computable.id (Computable.const []))
  obtain ⟨c_V, hc_V⟩ := Nat.Partrec.Code.exists_code.mp hM
  have hfind_step := rfind_evaln_isSome_partrec c_V
  let f_V : BitString →. BitString := fun x =>
    (Nat.rfind (fun s => Part.some (Code.evaln s c_V (Encodable.encode x)).isSome)).map Nat.bits
  have hf_V : Partrec f_V := hfind_step.map (natBits_computable.comp Computable.snd).to₂
  obtain ⟨c_map, hmap⟩ := plainK_partrec_map_le U hU f_V hf_V
  obtain ⟨c_len, hlen⟩ := plainK_le_length U hU
  set k13 := c_len + c_map
  obtain ⟨K0, hK0⟩ := exists_boundedNatOutputs_nonempty U hU cU hcU
  set k_br := k13 + K0
  have h_evaln_check2 := evaln_decodeBits_isSome_primrec2 c_V
  let C0 := canonicalObject V cV 4 0
  let f_br : ℕ × BitString → BitString := fun p =>
    bif decide (p.1 < k_br) then C0
    else listCode ((boundedPrograms (p.1 - k_br)).filter
      (fun x => (Code.evaln (decodeBits p.2 + 1) c_V (Encodable.encode x)).isSome))
  have hf_br_comp : Computable f_br := by
    have h_cond : Primrec (fun p : ℕ × BitString => decide (p.1 < k_br)) :=
      PrimrecPred.decide (PrimrecRel.comp Primrec.nat_lt Primrec.fst (Primrec.const k_br))
    have h_sub_prim : Primrec (fun p : ℕ × BitString => p.1 - k_br) :=
      Primrec₂.comp Primrec.nat_sub Primrec.fst (Primrec.const k_br)
    have h_sub : Computable (fun p : ℕ × BitString => p.1 - k_br) := h_sub_prim.to_comp
    have h_filter : Computable (fun p : ℕ × BitString =>
        (boundedPrograms (p.1 - k_br)).filter
          (fun x => (Code.evaln (decodeBits p.2 + 1) c_V (Encodable.encode x)).isSome)) :=
      (list_filter_primrec (primrec_boundedPrograms.comp h_sub_prim) h_evaln_check2).to_comp
    have h_listCode : Computable (fun p : ℕ × BitString =>
        listCode ((boundedPrograms (p.1 - k_br)).filter
          (fun x => (Code.evaln (decodeBits p.2 + 1) c_V (Encodable.encode x)).isSome))) :=
      listCode_primrec.to_comp.comp h_filter
    exact Computable.cond h_cond.to_comp (Computable.const C0) h_listCode
  let A_br : ℕ × BitString →. BitString := fun p => Part.some (f_br p)
  have hA_br_part : Partrec A_br := hf_br_comp
  refine ⟨k_br, A_br, hA_br_part, fun n => ?_⟩
  dsimp [A_br, f_br]
  by_cases hn : n < k_br
  · rw [decide_eq_true hn]
    dsimp
    have h0 : n - k_br = 0 := by omega
    rw [h0]
  · rw [decide_eq_false hn]
    dsimp
    push_neg at hn
    set m := n - k_br
    have hn_K0 : n ≥ K0 := by dsimp [m, k_br] at *; omega
    obtain ⟨b0, hb0⟩ := busyBeaver_isSome_of_nonempty cU n (hK0 n hn_K0)
    have h_canon2 : canonicalObject U cU 2 n = natBits b0 := by
      dsimp [canonicalObject, objBusyBeaver]
      rw [hb0]
      rfl
    rw [h_canon2]
    dsimp [natBits]
    rw [decodeBits_natBits]
    have hk13_le : k13 ≤ n := by dsimp [k_br] at hn; omega
    have h1_spec : ∀ x : BitString, x.length ≤ m →
        ((Code.evaln (b0 + 1) c_V (Encodable.encode x)).isSome = true ↔
          (cV.eval (Encodable.encode (x, ([] : BitString)))).Dom) :=
      fun x hx => evaln_busyBeaver_bound_spec U V cU cV c_V hcU hcV hc_V
        c_map c_len n b0 hk13_le hmap hlen hb0 x
        (le_trans hx (show m ≤ n - k13 by dsimp [m, k_br] at *; omega))
    have h_filter_eq : (boundedPrograms m).filter
        (fun x => (Code.evaln (b0 + 1) c_V (Encodable.encode x)).isSome) =
        haltingProgramsBounded cV m :=
      filter_evaln_isSome_eq_haltingProgramsBounded cV m b0 c_V h1_spec
    have h_canon4 : canonicalObject V cV 4 m = listCode (haltingProgramsBounded cV m) := rfl
    rw [h_canon4, h_filter_eq]

/-- **Exercise 8.** Theorem 15 remains valid when the canonical objects are built
from two different optimal decompressors. -/
theorem canonicalObject_equivalence_two_decompressors
    (U V : Map) (hU : isOptimalConditional U) (hV : isOptimalConditional V)
    (cU cV : Code) (hcU : IsCodeFor cU U) (hcV : IsCodeFor cV V) :
    (∃ k : ℕ, ∀ i ≤ 8, ∀ n : ℕ,
        plainK U (canonicalObject V cV i n) ≤ ((n + k : ℕ) : ℕ∞) ∧
          (n : ℕ∞) ≤ plainK U (canonicalObject V cV i n) + (k : ℕ∞)) ∧
      (∀ i ≤ 8, ∀ j ≤ 8, ∃ k : ℕ, ∃ A : ℕ × BitString →. BitString, Partrec A ∧
        ∀ n : ℕ, A (n, canonicalObject U cU i n) =
          Part.some (canonicalObject V cV j (n - k))) := by
  obtain ⟨cU_to_V, hcU_to_V⟩ := hV.2 U hU.1
  obtain ⟨cV_to_U, hcV_to_U⟩ := hU.2 V hV.1
  have h_bound : ∃ k : ℕ, ∀ i ≤ 8, ∀ n : ℕ,
      plainK U (canonicalObject V cV i n) ≤ ((n + k : ℕ) : ℕ∞) ∧
        (n : ℕ∞) ≤ plainK U (canonicalObject V cV i n) + (k : ℕ∞) := by
    obtain ⟨kV, hkV⟩ := canonicalObject_complexity_eq V hV cV hcV
    refine ⟨kV + cV_to_U + cU_to_V, fun i hi n => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hkV i hi n
      have hU_le := hcV_to_U (canonicalObject V cV i n) []
      calc plainK U (canonicalObject V cV i n)
        _ ≤ plainK V (canonicalObject V cV i n) + (cV_to_U : ℕ∞) := hU_le
        _ ≤ ((n + kV : ℕ) : ℕ∞) + (cV_to_U : ℕ∞) := by gcongr
        _ = ((n + kV + cV_to_U : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ ((n + (kV + cV_to_U + cU_to_V) : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
    · obtain ⟨h1, h2⟩ := hkV i hi n
      have hV_le : plainK V (canonicalObject V cV i n) ≤
          plainK U (canonicalObject V cV i n) + (cU_to_V : ℕ∞) :=
        hcU_to_V (canonicalObject V cV i n) []
      have h_add : plainK V (canonicalObject V cV i n) + (kV : ℕ∞) ≤
          (plainK U (canonicalObject V cV i n) + (cU_to_V : ℕ∞)) + (kV : ℕ∞) := by gcongr
      calc (n : ℕ∞)
        _ ≤ plainK V (canonicalObject V cV i n) + (kV : ℕ∞) := h2
        _ ≤ (plainK U (canonicalObject V cV i n) + (cU_to_V : ℕ∞)) + (kV : ℕ∞) := h_add
        _ = plainK U (canonicalObject V cV i n) + ((kV + cU_to_V : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ plainK U (canonicalObject V cV i n) + ((kV + cV_to_U + cU_to_V : ℕ) : ℕ∞) := by
          gcongr
          omega
  have h_equiv : ∀ i ≤ 8, ∀ j ≤ 8, ∃ k : ℕ, ∃ A : ℕ × BitString →. BitString, Partrec A ∧
      ∀ n : ℕ, A (n, canonicalObject U cU i n) =
        Part.some (canonicalObject V cV j (n - k)) := by
    intro i hi j hj
    obtain ⟨k1, A1, hA1_part, hA1_eq⟩ :=
      canonicalObject_mutual_reduction U hU cU hcU i hi 2 (by decide)
    obtain ⟨k_br, A_br, hA_br_part, hA_br_eq⟩ :=
      exists_partrec_busyBeaver_to_haltingList U V hU hV cU cV hcU hcV
    obtain ⟨k2, A2, hA2_part, hA2_eq⟩ :=
      canonicalObject_mutual_reduction V hV cV hcV 4 (by decide) j hj
    let A : ℕ × BitString →. BitString := fun p =>
      (A1 p).bind (fun w1 =>
      (A_br (p.1 - k1, w1)).bind (fun w2 =>
      A2 (p.1 - k1 - k_br, w2)))
    have hA_part : Partrec A := partrec_bind_three A1 hA1_part A_br hA_br_part A2 hA2_part k1 k_br
    refine ⟨k1 + k_br + k2, A, hA_part, fun n => ?_⟩
    dsimp [A]
    rw [hA1_eq n]
    rw [Part.bind_some]
    rw [hA_br_eq (n - k1)]
    rw [Part.bind_some]
    have hA2 := hA2_eq (n - k1 - k_br)
    have h_sub : n - k1 - k_br - k2 = n - (k1 + k_br + k2) := by omega
    rw [h_sub] at hA2
    exact hA2
  exact ⟨h_bound, h_equiv⟩

-- `exercise09_relativized` (ch01-exercise-9) is archived; see `docs/ARCHIVED_TARGETS.md`.

-- `exercise10_query_bound` (ch01-exercise-10) is archived; see `docs/ARCHIVED_TARGETS.md`.

/-- **Exercise 11.** For every partial computable `f`, `B(n + c) ≥ f (B n)`
whenever `f (B n)` is defined. -/
theorem busyBeaver_shift_ge_apply (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U) (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ k : ℕ, ∀ (n b v : ℕ), busyBeaver c n = some b → v ∈ f b →
      ∃ b', busyBeaver c (n + k) = some b' ∧ v ≤ b' := by
  let g : BitString →. BitString := fun w => (f (bitsToNat w)).map Nat.bits
  have hg : Partrec g :=
    Partrec.map (hf.comp bitsToNat_computable) (natBits_computable.comp Computable.snd).to₂
  obtain ⟨k, hk⟩ := plainK_partrec_map_le U hU g hg
  refine ⟨k, fun n b v hb hv => ?_⟩
  have hbK : plainKNat U b ≤ (n : ENat) :=
    ((busyBeaver_some_iff_plainKNat hc n b).mp hb).1
  have hmem_g : Nat.bits v ∈ g (Nat.bits b) := by
    change Nat.bits v ∈ (f (bitsToNat (Nat.bits b))).map Nat.bits
    rw [bitsToNat_bits]
    exact Part.mem_map Nat.bits hv
  have hvK : plainKNat U v ≤ ((n + k : ℕ) : ENat) := by
    have hle := hk (Nat.bits b) (Nat.bits v) hmem_g
    change plainKNat U v ≤ plainKNat U b + (k : ENat) at hle
    calc plainKNat U v ≤ plainKNat U b + (k : ENat) := hle
      _ ≤ (n : ENat) + (k : ENat) := by gcongr
      _ = ((n + k : ℕ) : ENat) := by rw [Nat.cast_add]
  have hv_mem : v ∈ boundedNatOutputs c (n + k) :=
    (mem_boundedNatOutputs_iff_plainKNat_le hc (n + k) v).mpr hvK
  obtain ⟨b', hb'⟩ := busyBeaver_isSome_of_nonempty c (n + k) ⟨v, hv_mem⟩
  refine ⟨b', hb', ?_⟩
  exact ((busyBeaver_some_iff c (n + k) b').mp hb').2 v hv_mem

end Kolmogorov
