import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Complexity.InfiniteSequences.MonotoneGap

/-!
# Monotone versus plain complexity, and counting incompressible strings
`exists_monotone_lt_plainK` proves SUV Exercise 51; its conditional variant treats Problem 52.
`card_incompressible_mem_Icc` and `plainK_card_incompressible_ge` establish Exercise 53:
the count of incompressible strings is tightly bounded and is itself incompressible.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution
variable (Q : ℕ × ℕ × BitString → Bool)

/-- A prefix of `onesZerosSeq` past `bk m` is produced by `D_cond c0 K` on conditions `(m, n)`. -/
private lemma onesZerosSeq_prefix_mem_D_cond (c0 : Code) (K m n : ℕ)
    (hn : max (m + K) (boundedOutputCompletionTime c0 (m + K)) < n) :
    List.replicate (max (m + K) (boundedOutputCompletionTime c0 (m + K))) true ++
      List.replicate (n - max (m + K) (boundedOutputCompletionTime c0 (m + K))) false ∈
      D_cond c0 K (Nat.bits m, Nat.bits n) := by
  set bk_m := max (m + K) (boundedOutputCompletionTime c0 (m + K))
  have hnk : m + K < n := by
    have : m + K ≤ bk_m := le_max_left (m + K) _
    omega
  have hnT : boundedOutputCompletionTime c0 (m + K) ≤ n := by
    have : boundedOutputCompletionTime c0 (m + K) ≤ bk_m := le_max_right (m + K) _
    omega
  have hstage_eq : boundedOutputStage c0 (m + K) n = completedBoundedOutput c0 (m + K) :=
    boundedOutputStage_eq_completed_of_completion_le c0 (m + K) n hnT
  have hex : ∃ t, (boundedOutputStage c0 (m + K) t).length =
      (boundedOutputStage c0 (m + K) n).length :=
    ⟨n, rfl⟩
  have ht_spec : (boundedOutputStage c0 (m + K) (Nat.find hex)).length =
      (boundedOutputStage c0 (m + K) n).length :=
    Nat.find_spec hex
  have ht_comp : Nat.find hex = boundedOutputCompletionTime c0 (m + K) := by
    apply le_antisymm
    · have h_spec := boundedOutputCompletionTime_spec c0 (m + K)
      have h_eq_t : (boundedOutputStage c0 (m + K)
          (boundedOutputCompletionTime c0 (m + K))).length =
          (boundedOutputStage c0 (m + K) n).length := by
        rw [h_spec, ← hstage_eq]
      exact Nat.find_le h_eq_t
    · have h_len : (boundedOutputStage c0 (m + K) (Nat.find hex)).length =
          (completedBoundedOutput c0 (m + K)).length := by
        rw [ht_spec, hstage_eq]
      exact boundedOutputCompletionTime_le_complete_stage c0 (m + K) (Nat.find hex) h_len
  have ht_search : boundedOutputCompletionTime c0 (m + K) ∈ Nat.rfind (fun t => Part.some
      ((boundedOutputStage c0 (m + K) t).length ==
        (boundedOutputStage c0 (m + K) n).length)) := by
    rw [Nat.mem_rfind]
    refine ⟨by rw [← ht_comp, ht_spec]; simp, ?_⟩
    intro t ht
    have hne : (boundedOutputStage c0 (m + K) t).length ≠
        (boundedOutputStage c0 (m + K) n).length := by
      intro h_eq_len
      have h_le : Nat.find hex ≤ t := Nat.find_min' hex h_eq_len
      rw [ht_comp] at h_le
      omega
    simp [hne]
  unfold D_cond
  simp only [bitsToNat_bits]
  rw [Part.mem_map_iff]
  refine ⟨boundedOutputCompletionTime c0 (m + K), ht_search, ?_⟩
  unfold D_cond_fn
  simp only [bitsToNat_bits]
  have h_bk : max (m + K) (boundedOutputCompletionTime c0 (m + K)) = bk_m := rfl
  rw [h_bk]
  have h_not_le : ¬ (n ≤ bk_m) := by omega
  have h_dec : decide (n ≤ bk_m) = false := decide_eq_false h_not_le
  rw [h_dec]
  rfl

/-- Upper bound on the monotone complexity of `onesZerosSeq (bk m)`. -/
private lemma seqM_onesZerosSeq_le (U : Map) (c0 : Code) (K C_Dones C_Dcond : ℕ)
    (hD_ones : ∀ x y, condK U x y ≤ condK D_ones x y + (C_Dones : ℕ∞))
    (hD_cond : ∀ x y, condK U x y ≤ condK (D_cond c0 K) x y + (C_Dcond : ℕ∞))
    (m : ℕ) :
    seqM U (onesZerosSeq (max (m + K) (boundedOutputCompletionTime c0 (m + K)))) ≤
      (((C_Dones + C_Dcond + 2) * Nat.log 2 m + (C_Dones + C_Dcond + 2) : ℕ) : ℕ∞) := by
  set bk_m := max (m + K) (boundedOutputCompletionTime c0 (m + K))
  set c := C_Dones + C_Dcond + 2
  unfold seqM
  apply iSup_le
  intro n
  rw [seqPrefix_onesZeros]
  by_cases hnB : n ≤ bk_m
  · rw [if_pos hnB]
    have h1 := hD_ones (List.replicate n true) (Nat.bits n)
    have hDones_produces : List.replicate n true ∈ D_ones (Nat.bits n, Nat.bits n) := by
      unfold D_ones
      simp only [bitsToNat_bits, Part.mem_some_iff]
    have hDones_val : condK D_ones (List.replicate n true) (Nat.bits n) ≤ 0 := by
      unfold condK candidateLengths
      apply sInf_le
      refine ⟨[], hDones_produces, rfl⟩
    have h2 : condK U (List.replicate n true) (Nat.bits n) ≤ (C_Dones : ℕ∞) := by
      calc condK U (List.replicate n true) (Nat.bits n)
          ≤ condK D_ones (List.replicate n true) (Nat.bits n) + (C_Dones : ℕ∞) := h1
        _ ≤ 0 + (C_Dones : ℕ∞) := by gcongr
        _ = (C_Dones : ℕ∞) := by ring
    calc condK U (List.replicate n true) (Nat.bits n)
        ≤ (C_Dones : ℕ∞) := h2
      _ ≤ ((c * Nat.log 2 m + c : ℕ) : ℕ∞) := by
        exact_mod_cast (show C_Dones ≤ c * Nat.log 2 m + c by dsimp [c]; omega)
  · rw [if_neg hnB]
    push_neg at hnB
    have hDcond_produces := onesZerosSeq_prefix_mem_D_cond c0 K m n hnB
    have hDcond_val : condK (D_cond c0 K)
        (List.replicate bk_m true ++ List.replicate (n - bk_m) false) (Nat.bits n) ≤
        ((Nat.bits m).length : ℕ∞) := by
      unfold condK candidateLengths
      apply sInf_le
      refine ⟨Nat.bits m, hDcond_produces, rfl⟩
    have h_len_m : (Nat.bits m).length ≤ Nat.log 2 m + 1 :=
      length_natBits_lt_pow (Nat.lt_pow_succ_log_self (by decide) m)
    calc condK U (List.replicate bk_m true ++ List.replicate (n - bk_m) false) (Nat.bits n)
        ≤ condK (D_cond c0 K) (List.replicate bk_m true ++ List.replicate (n - bk_m) false)
          (Nat.bits n) + (C_Dcond : ℕ∞) := hD_cond _ _
      _ ≤ ((Nat.bits m).length : ℕ∞) + (C_Dcond : ℕ∞) := by gcongr
      _ ≤ ((c * Nat.log 2 m + c : ℕ) : ℕ∞) := by
        exact_mod_cast (by
          dsimp [c]
          have h_c1 : 1 ≤ C_Dones + C_Dcond + 2 := by omega
          have h_c2 : C_Dcond + 1 ≤ C_Dones + C_Dcond + 2 := by omega
          have h_m : 0 ≤ Nat.log 2 m := Nat.zero_le _
          nlinarith)

/-- A program `p` computing a sequence generator for `onesZerosSeq (bk m)` allows
`fExtract` to reconstruct `Nat.bits (bk m)`. -/
private lemma fExtract_mem_of_eval_onesZerosSeq (U : Map) (c0 : Code) (m K : ℕ) (e : ℕ)
    (p : BitString)
    (he_eval : ∀ n,
      Encodable.encode (seqPrefix
        (onesZerosSeq (max (m + K) (boundedOutputCompletionTime c0 (m + K)))) n) ∈
        (Denumerable.ofNat Code e).eval (Encodable.encode n))
    (hp_prod : Nat.bits e ∈ U (p, [])) :
    Nat.bits (max (m + K) (boundedOutputCompletionTime c0 (m + K))) ∈ fExtract U (p, []) := by
  set bk_m := max (m + K) (boundedOutputCompletionTime c0 (m + K))
  have h_prefix := he_eval (bk_m + 1)
  have h_seq_prefix : seqPrefix (onesZerosSeq bk_m) (bk_m + 1) =
      List.replicate bk_m true ++ [false] := by
    rw [seqPrefix_onesZeros]
    have h_not : ¬ (bk_m + 1 ≤ bk_m) := by omega
    simp [h_not]
  rw [h_seq_prefix] at h_prefix
  have h_false_mem : false ∈ List.replicate bk_m true ++ [false] := by simp
  have h_search : (bk_m + 1) ∈ Nat.rfind (fun n =>
      ((Denumerable.ofNat Code e).eval (Encodable.encode n)).bind (fun w_enc =>
        Part.ofOption ((Encodable.decode (α := BitString) w_enc).map (fun w =>
          decide (false ∈ w))))) := by
    rw [Nat.mem_rfind]
    constructor
    · rw [Part.mem_bind_iff]
      refine ⟨Encodable.encode (List.replicate bk_m true ++ [false]), h_prefix, ?_⟩
      rw [Part.mem_ofOption]
      simp [h_false_mem]
    · intro n hn
      have hn_prefix := he_eval n
      have hn_seq := seqPrefix_onesZeros bk_m n
      rw [hn_seq, if_pos (by omega)] at hn_prefix
      rw [Part.mem_bind_iff]
      refine ⟨Encodable.encode (List.replicate n true), hn_prefix, ?_⟩
      rw [Part.mem_ofOption]
      rw [Encodable.encodek]
      dsimp only [Option.map_some]
      simp [List.mem_replicate]
  have h_takewhile : (List.replicate bk_m true ++ [false]).takeWhile id =
      List.replicate bk_m true := by
    rw [List.takeWhile_append]
    simp
  unfold fExtract
  rw [Part.mem_bind_iff]
  refine ⟨Nat.bits e, hp_prod, ?_⟩
  unfold fExtractBody
  simp only [bitsToNat_bits]
  rw [Part.mem_bind_iff]
  refine ⟨bk_m + 1, h_search, ?_⟩
  rw [Part.mem_bind_iff]
  refine ⟨Encodable.encode (List.replicate bk_m true ++ [false]), h_prefix, ?_⟩
  rw [Part.mem_ofOption]
  simp [h_takewhile]

/-- Lower bound on the complexity of `onesZerosSeq (bk m)`. -/
private lemma seqC_onesZerosSeq_ge (U : Map) (c0 : Code) (C_ext : ℕ)
    (hC_ext : ∀ x y, condK U x y ≤ condK (fExtract U) x y + (C_ext : ℕ∞))
    (c_late : ℕ)
    (hc_late : ∀ q N : ℕ, q ≤ N → boundedOutputCompletionTime c0 q ≤ N →
      (q : ENat) < plainKNat U N + (c_late : ENat))
    (m : ℕ) :
    (m : ℕ∞) ≤ seqC U (onesZerosSeq (max (m + (C_ext + c_late + 1))
      (boundedOutputCompletionTime c0 (m + (C_ext + c_late + 1))))) := by
  set K := C_ext + c_late + 1
  set bk_m := max (m + K) (boundedOutputCompletionTime c0 (m + K))
  unfold seqC
  apply le_sInf
  rintro v ⟨e, he_eval, rfl⟩
  by_cases htop : plainKNat U e = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨Ke, hKe⟩ : ∃ Ke : ℕ, plainKNat U e = (Ke : ENat) :=
        ⟨(plainKNat U e).toNat, (ENat.coe_toNat htop).symm⟩
    have h_plain_e : condK U (Nat.bits e) [] = (Ke : ENat) := hKe
    have h_nonempty : (candidateLengths U (Nat.bits e) []).Nonempty := by
      by_contra h_empty
      have : condK U (Nat.bits e) [] = ⊤ := by
        unfold condK
        rw [Set.not_nonempty_iff_eq_empty.mp h_empty, sInf_empty]
      rw [h_plain_e] at this
      exact ENat.coe_ne_top Ke this
    have h_mem := csInf_mem h_nonempty
    unfold condK at h_plain_e
    rw [h_plain_e] at h_mem
    rcases h_mem with ⟨p, hp_prod, hp_len⟩
    have hp_len_nat : p.length = Ke := by exact_mod_cast hp_len
    have h_extract_produces := fExtract_mem_of_eval_onesZerosSeq U c0 m K e p he_eval hp_prod
    have h_fext_val : condK (fExtract U) (Nat.bits bk_m) [] ≤ (p.length : ℕ∞) := by
      unfold condK candidateLengths
      apply sInf_le
      refine ⟨p, h_extract_produces, rfl⟩
    have h1 := hC_ext (Nat.bits bk_m) []
    have h_plainK_bk : plainK U (Nat.bits bk_m) ≤ (Ke : ℕ∞) + (C_ext : ℕ∞) := by
      calc plainK U (Nat.bits bk_m)
          = condK U (Nat.bits bk_m) [] := rfl
        _ ≤ condK (fExtract U) (Nat.bits bk_m) [] + (C_ext : ℕ∞) := h1
        _ ≤ (p.length : ℕ∞) + (C_ext : ℕ∞) := by gcongr
        _ = (Ke : ℕ∞) + (C_ext : ℕ∞) := by rw [hp_len_nat]
    have h_late := hc_late (m + K) bk_m (le_max_left (m + K) _) (le_max_right (m + K) _)
    have h_plain_bk_val : plainK U (Nat.bits bk_m) = plainKNat U bk_m := rfl
    rw [h_plain_bk_val] at h_plainK_bk
    have h_chain : ((m + K : ℕ) : ENat) < (Ke : ENat) + ((c_late + C_ext : ℕ) : ENat) := by
      calc ((m + K : ℕ) : ENat)
          < plainKNat U bk_m + (c_late : ENat) := h_late
        _ ≤ ((Ke : ENat) + (C_ext : ENat)) + (c_late : ENat) := by gcongr
        _ = (Ke : ENat) + ((c_late + C_ext : ℕ) : ENat) := by push_cast; ring
    have h_chain_nat : m + K < Ke + (c_late + C_ext) := by exact_mod_cast h_chain
    have h_m_le : m ≤ Ke := by
      dsimp [K] at h_chain_nat
      omega
    rw [hKe]
    exact_mod_cast h_m_le

/-- **Exercise 51.** `M` can be much smaller than `C`. -/
theorem exists_monotone_lt_plainK (U : Map) (hU : isOptimalConditional U) :
    ∃ (x : ℕ → ℕ → Bool) (c : ℕ), ∀ m : ℕ, Computable (x m) ∧
      seqM U (x m) ≤ ((c * Nat.log 2 m + c : ℕ) : ℕ∞) ∧ (m : ℕ∞) ≤ seqC U (x m) := by
  obtain ⟨c0, hc0⟩ : ∃ c : Code, IsCodeFor c U := Nat.Partrec.Code.exists_code.mp hU.1
  obtain ⟨C_ext, hC_ext⟩ := hU.2 (fExtract U) (f_extract_partrec U hU.1)
  obtain ⟨c_late, hc_late⟩ := lateCutoff_complexity_implication U hU c0 hc0
  obtain ⟨C_Dones, hD_ones⟩ := hU.2 D_ones D_ones_partrec
  set K := C_ext + c_late + 1
  obtain ⟨C_Dcond, hD_cond⟩ := hU.2 (D_cond c0 K) (D_cond_partrec c0 K)
  set c := C_Dones + C_Dcond + 2
  set bk := fun m => max (m + K) (boundedOutputCompletionTime c0 (m + K))
  refine ⟨fun m => onesZerosSeq (bk m), c, fun m => ⟨?_, ?_, ?_⟩⟩
  · change Computable (onesZerosSeq (bk m))
    have hlt : PrimrecPred (fun i : ℕ => i < bk m) :=
      Primrec.nat_lt.comp Primrec.id (Primrec.const (bk m))
    exact (PrimrecPred.decide hlt).to_comp
  · exact seqM_onesZerosSeq_le U c0 K C_Dones C_Dcond hD_ones hD_cond m
  · exact seqC_onesZerosSeq_ge U c0 C_ext hC_ext c_late hc_late m

/-! ### SUV problem 52 -/

/-- Every value below `2 ^ k` is the key of a length-`k` string. -/
lemma exists_lexKey (k L : ℕ) (h : L < 2 ^ k) : ∃ x : BitString, x.length = k ∧ lexKey x = L := by
  induction k generalizing L with
  | zero =>
    refine ⟨[], rfl, ?_⟩
    simp only [pow_zero, Nat.lt_one_iff] at h
    simp [lexKey, h]
  | succ k ih =>
    rw [pow_succ] at h
    by_cases hb : 2 ^ k ≤ L
    · obtain ⟨t, ht1, ht2⟩ := ih (L - 2 ^ k) (by omega)
      refine ⟨true :: t, by simp [ht1], ?_⟩
      rw [lexKey_cons, ht1, ht2]
      simp
      omega
    · obtain ⟨t, ht1, ht2⟩ := ih L (by omega)
      refine ⟨false :: t, by simp [ht1], ?_⟩
      rw [lexKey_cons, ht1, ht2]
      simp

/-- Decoding of the parameter triple `(m, L, R)` from a bit string of length `2m+2`. -/
def minfDecode (str : BitString) : ℕ × ℕ × ℕ :=
  ((str.length - 2) / 2,
    lexKey (str.take ((str.length - 2) / 2 + 1)),
    lexKey (str.drop ((str.length - 2) / 2 + 1)))

private theorem minfDecode_computable : Computable minfDecode := by
  have hm : Primrec (fun str : BitString => (str.length - 2) / 2) :=
    Primrec.nat_div.comp
      (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 2)) (Primrec.const 2)
  have hm1 : Primrec (fun str : BitString => (str.length - 2) / 2 + 1) := Primrec.succ.comp hm
  exact (Primrec.pair hm (Primrec.pair
    (lexKey_primrec.comp (Primrec.list_take.comp Primrec.id hm1))
    (lexKey_primrec.comp (Primrec.list_drop.comp Primrec.id hm1)))).to_comp

private lemma minfDecode_encode (m L R : ℕ) (hL : L < 2 ^ (m + 1)) (hR : R < 2 ^ (m + 1)) :
    ∃ str : BitString, str.length = 2 * m + 2 ∧ minfDecode str = (m, L, R) := by
  obtain ⟨xL, hxL1, hxL2⟩ := exists_lexKey (m + 1) L hL
  obtain ⟨xR, hxR1, hxR2⟩ := exists_lexKey (m + 1) R hR
  have hlen : (xL ++ xR).length = 2 * m + 2 := by simp [hxL1, hxR1]; omega
  refine ⟨xL ++ xR, hlen, ?_⟩
  have hm : ((xL ++ xR).length - 2) / 2 = m := by rw [hlen]; omega
  rw [minfDecode, hm, ← hxL1]
  simp [hxL2, hxR2, hxL1]

/-- Stage predicate for conditional complexity: some program of length at most `m`
outputs `x` on input `|x|` within `s` steps.  The argument is `(m, s, x)`. -/
def minfQ (cd : Code) (a : ℕ × ℕ × BitString) : Bool :=
  (boundedPrograms a.1).any (fun p =>
    decide (Code.evaln a.2.1 cd
      (Encodable.encode ((p, Nat.bits a.2.2.length) : BitString × BitString))
        = some (Encodable.encode a.2.2)))

private theorem minfQ_primrec (cd : Code) : Primrec (minfQ cd) := by
  have hlist : Primrec (fun a : ℕ × ℕ × BitString => boundedPrograms a.1) :=
    primrec_boundedPrograms.comp Primrec.fst
  have hbody : Primrec₂ (fun (a : ℕ × ℕ × BitString) (p : BitString) =>
      decide (Code.evaln a.2.1 cd
        (Encodable.encode ((p, Nat.bits a.2.2.length) : BitString × BitString))
          = some (Encodable.encode a.2.2))) := by
    have hs : Primrec (fun z : (ℕ × ℕ × BitString) × BitString => z.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have harg : Primrec (fun z : (ℕ × ℕ × BitString) × BitString =>
        Encodable.encode ((z.2, Nat.bits z.1.2.2.length) : BitString × BitString)) :=
      Primrec.encode.comp (Primrec.pair Primrec.snd
        (primrec_natBits.comp (Primrec.list_length.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
    have heval : Primrec (fun z : (ℕ × ℕ × BitString) × BitString =>
        Code.evaln z.1.2.1 cd
          (Encodable.encode ((z.2, Nat.bits z.1.2.2.length) : BitString × BitString))) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (Primrec.pair (Primrec.pair hs (Primrec.const cd)) harg)
    have hrhs : Primrec (fun z : (ℕ × ℕ × BitString) × BitString =>
        some (Encodable.encode z.1.2.2)) :=
      Primrec.option_some.comp
        (Primrec.encode.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    exact (PrimrecPred.decide (Primrec.eq.comp heval hrhs)).to₂
  exact list_any_primrec hlist hbody

private lemma minfQ_mono (cd : Code) : ∀ (m s s' : ℕ) (x : BitString), s ≤ s' →
    minfQ cd (m, s, x) = true → minfQ cd (m, s', x) = true := by
  intro m s s' x hss h
  simp only [minfQ, List.any_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨p, hp, hev⟩ := h
  exact ⟨p, hp, Nat.Partrec.Code.evaln_mono hss hev⟩

private lemma minfQ_iff {U : Map} {cd : Code} (hc : IsCodeFor cd U) (m : ℕ) (x : BitString) :
    (∃ s, minfQ cd (m, s, x) = true) ↔ condK U x (Nat.bits x.length) ≤ (m : ENat) := by
  constructor
  · rintro ⟨s, hs⟩
    simp only [minfQ, List.any_eq_true, decide_eq_true_eq] at hs
    obtain ⟨p, hp, hev⟩ := hs
    have hsound := Nat.Partrec.Code.evaln_sound hev
    rw [hc] at hsound
    simp only [Encodable.encodek, Part.ofOption, Part.bind_some] at hsound
    rw [Part.mem_map_iff] at hsound
    obtain ⟨z, hz, hze⟩ := hsound
    have hzx : z = x := Encodable.encode_injective hze
    subst hzx
    exact (condK_le_iff U z (Nat.bits z.length) m).mpr
      ⟨p, (mem_boundedPrograms_iff p m).mp hp, hz⟩
  · intro h
    obtain ⟨p, hplen, hprod⟩ := (condK_le_iff U x (Nat.bits x.length) m).mp h
    have hmem : Encodable.encode x ∈ cd.eval
        (Encodable.encode ((p, Nat.bits x.length) : BitString × BitString)) := by
      rw [hc]
      simp only [Encodable.encodek, Part.ofOption, Part.bind_some]
      exact Part.mem_map _ hprod
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    refine ⟨s, ?_⟩
    simp only [minfQ, List.any_eq_true, decide_eq_true_eq]
    exact ⟨p, (mem_boundedPrograms_iff p m).mpr hplen, hs⟩

private lemma minf_hlevel {U : Map} {cd : Code} (hc : IsCodeFor cd U) (m : ℕ) (n : ℕ) :
    mLevelCount (minfQ cd) m n ≤ 2 ^ (m + 1) - 1 := by
  classical
  rw [mLevelCount, countP_allStrings_eq_card]
  have hcard := card_lt_of_condK_le U (Nat.bits n) m
    ((stringsOfLength n).filter (fun x => (decide (∃ s, minfQ cd (m, s, x) = true)) = true)) ?_
  · omega
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxlen : x.length = n := by
      rw [stringsOfLength, List.mem_toFinset, mem_allStrings] at hx1; exact hx1
    simp only [decide_eq_true_eq] at hx2
    have := (minfQ_iff hc m x).mp hx2
    rwa [hxlen] at this

/-- The uniform program: from a bit string encoding the triple `(m, L, R)` it produces the
index of a machine that computes the prefixes of the path. -/
private lemma minf_program (cd : Code) : ∃ prog : BitString → ℕ, Computable prog ∧
    ∀ (str : BitString) (n : ℕ),
      (Denumerable.ofNat Code (prog str)).eval n
        = (mSearch (minfQ cd) ((minfDecode str).1, (minfDecode str).2.1, (minfDecode str).2.2,
            n)).map Encodable.encode := by
  classical
  obtain ⟨sm, hsm_comp, hsm⟩ := Nat.Partrec.Code.smn
  have hstep1 : Computable (fun q : ℕ × BitString =>
      (((minfDecode q.2).1, (minfDecode q.2).2.1, (minfDecode q.2).2.2, q.1.unpair.2) :
        ℕ × ℕ × ℕ × ℕ)) := by
    have hdec : Computable (fun q : ℕ × BitString => minfDecode q.2) :=
      minfDecode_computable.comp Computable.snd
    exact Computable.pair (Computable.fst.comp hdec)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp hdec))
        (Computable.pair (Computable.snd.comp (Computable.snd.comp hdec))
          (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.fst))))
  have hstep3 : Partrec (fun q : ℕ × BitString =>
      (mSearch (minfQ cd) ((minfDecode q.2).1, (minfDecode q.2).2.1, (minfDecode q.2).2.2,
        q.1.unpair.2)).map Encodable.encode) :=
    Partrec.map ((mSearch_partrec (minfQ cd) (minfQ_primrec cd)).comp hstep1)
      (Computable.encode.comp Computable.snd).to₂
  have hG : Partrec (fun z : ℕ =>
      (Part.ofOption (Encodable.decode (α := BitString) z.unpair.1)).bind (fun str =>
        (mSearch (minfQ cd) ((minfDecode str).1, (minfDecode str).2.1, (minfDecode str).2.2,
          z.unpair.2)).map Encodable.encode)) := by
    refine Partrec.bind (Computable.ofOption
      (Computable.decode.comp (Computable.fst.comp Primrec.unpair.to_comp))) ?_
    exact hstep3.comp (Computable.pair Computable.fst Computable.snd)
  obtain ⟨cG, hcG⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hG)
  refine ⟨fun str => Encodable.encode (sm cG (Encodable.encode str)),
    Computable.encode.comp (hsm_comp.comp (Computable.const cG) Computable.encode), ?_⟩
  intro str n
  rw [Denumerable.ofNat_encode, hsm cG (Encodable.encode str) n, hcG]
  simp [Encodable.encodek]

/-- An `ℕ∞`-valued sequence whose `limsup` is at most `m` is eventually bounded by `m`. -/
lemma exists_threshold_of_limsup_le (f : ℕ → ℕ∞) (m : ℕ)
    (h : Filter.limsup f Filter.atTop ≤ (m : ℕ∞)) : ∃ N, ∀ n, N ≤ n → f n ≤ (m : ℕ∞) := by
  have h2 : Filter.limsup f Filter.atTop < ((m : ℕ∞) + 1) :=
    lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self m)
  have h3 := Filter.eventually_lt_of_limsup_lt h2
  rw [Filter.eventually_atTop] at h3
  obtain ⟨N, hN⟩ := h3
  exact ⟨N, fun n hn => Order.le_of_lt_succ (by simpa using hN n hn)⟩

/-- **Exercise 52.** `C^∞(x) ≤ 2 M_∞(x) + O(1)`. -/
theorem cinf_le_two_mul_minf (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ w : ℕ → Bool, seqCinf U w ≤ 2 * seqMinf U w + (c : ℕ∞) := by
  classical
  obtain ⟨cd, hc⟩ := Dovetailing.exists_isCodeFor hU
  obtain ⟨prog, hprog_comp, hprog⟩ := minf_program cd
  obtain ⟨c_len, hlen⟩ := plainK_le_length U hU
  obtain ⟨C_map, hCmap⟩ := plainK_partrec_map_le U hU
    (fun str => Part.some (Nat.bits (prog str)))
    (Partrec.some.comp (natBits_computable.comp hprog_comp))
  refine ⟨c_len + C_map + 2, fun w => ?_⟩
  rcases eq_or_ne (seqMinf U w) ⊤ with htop | hfin
  · rw [htop]
    simp
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    obtain ⟨N₀, hN₀⟩ := exists_threshold_of_limsup_le
      (fun n : ℕ => condK U (seqPrefix w n) (Nat.bits n)) m (le_of_eq hm.symm)
    have hw : ∀ n, N₀ ≤ n → ∃ s, minfQ cd (m, s, seqPrefix w n) = true := by
      intro n hn
      refine (minfQ_iff hc m (seqPrefix w n)).mpr ?_
      rw [length_seqPrefix]
      exact hN₀ n hn
    obtain ⟨L, R, N, hLB, hRB, hN₀N, hspec⟩ :=
      mSearch_spec (minfQ cd) (minfQ_mono cd) m (2 ^ (m + 1) - 1) N₀ w
        (fun n _ => minf_hlevel hc m n) hw
    have hpow : 0 < 2 ^ (m + 1) := by positivity
    obtain ⟨str, hstrlen, hstrdec⟩ := minfDecode_encode m L R (by omega) (by omega)
    have hmem : ∀ n, N ≤ n → Encodable.encode (seqPrefix w n) ∈
        (Denumerable.ofNat Code (prog str)).eval (Encodable.encode n) := by
      intro n hn
      rw [hprog str (Encodable.encode n), hstrdec]
      have hen : (Encodable.encode n) = n := rfl
      rw [hen, hspec n hn, Part.map_some]
      exact Part.mem_some _
    have hsInf : seqCinf U w ≤ plainKNat U (prog str) :=
      sInf_le ⟨prog str, N, hmem, rfl⟩
    have hle1 : plainK U (Nat.bits (prog str)) ≤ plainK U str + (C_map : ℕ∞) :=
      hCmap str (Nat.bits (prog str)) (Part.mem_some _)
    have hle2 : plainK U str ≤ ((2 * m + 2 : ℕ) : ℕ∞) + (c_len : ℕ∞) := by
      have := hlen str
      rwa [show programLength str = 2 * m + 2 from hstrlen] at this
    have hfinal : plainKNat U (prog str) ≤ ((2 * m + 2 + c_len + C_map : ℕ) : ℕ∞) := by
      calc plainKNat U (prog str) = plainK U (Nat.bits (prog str)) := rfl
        _ ≤ plainK U str + (C_map : ℕ∞) := hle1
        _ ≤ (((2 * m + 2 : ℕ) : ℕ∞) + (c_len : ℕ∞)) + (C_map : ℕ∞) := by gcongr
        _ = ((2 * m + 2 + c_len + C_map : ℕ) : ℕ∞) := by push_cast; ring
    refine le_trans hsInf (le_trans hfinal ?_)
    rw [← hm]
    push_cast
    ring_nf
    exact le_refl _

/-! ### SUV problem 48

The book proves problems 48, 49 and 52 by one and the same tree argument, which is
available here as the reusable core `mSearch_spec`.  Problem 48 is its cleanest
instance: `minfQ cd` enumerates exactly the strings whose conditional complexity given
their length is at most `c` — the enumerable subtree `S` of the book hint — and
`minf_hlevel` is the `O(1)` bound on its horizontal sections, so no pruning is needed. -/

/-- The prefixes of a computable sequence depend computably on their length. -/
lemma seqPrefix_computable {w : ℕ → Bool} (hw : Computable w) : Computable (seqPrefix w) := by
  have h : Computable (fun n : ℕ => List.map (fun i : ℕ => w i) (List.range n)) :=
    Computable.list_map Primrec.list_range.to_comp (hw.comp Computable.snd).to₂
  exact h.of_eq (fun _ => rfl)

/-- **Exercise 48.** A sequence is computable iff the conditional complexities of
its prefixes given their lengths are bounded. -/
theorem computable_iff_condK_prefix_bounded (U : Map) (hU : isOptimalConditional U)
    (w : ℕ → Bool) :
    Computable w ↔ ∃ c : ℕ, ∀ n : ℕ, condK U (seqPrefix w n) (Nat.bits n) ≤ (c : ℕ∞) := by
  constructor
  · -- A computable sequence: the decompressor that reads the length off the condition
    -- and prints the prefix needs no program at all.
    intro hw
    obtain ⟨C, hC⟩ := condK_partrec_cond_map_le U hU
      (fun y _ => Part.some (seqPrefix w (bitsToNat y)))
      (Partrec.some.comp ((seqPrefix_computable hw).comp
        (bitsToNat_primrec.to_comp.comp Computable.fst)))
    refine ⟨C, fun n => ?_⟩
    have hmem : seqPrefix w n ∈ Part.some (seqPrefix w (bitsToNat (Nat.bits n))) := by
      rw [bitsToNat_bits]
      exact Part.mem_some _
    simpa using hC (Nat.bits n) [] (seqPrefix w n) hmem
  · -- Bounded conditional complexity: the path lies in the enumerable set `minfQ cd`,
    -- whose levels have at most `2 ^ (c + 1) - 1` elements, so `mSearch_spec` applies.
    rintro ⟨c, hc⟩
    obtain ⟨cd, hcd⟩ := Dovetailing.exists_isCodeFor hU
    have hwQ : ∀ n : ℕ, 0 ≤ n → ∃ s, minfQ cd (c, s, seqPrefix w n) = true := by
      intro n _
      refine (minfQ_iff hcd c (seqPrefix w n)).mpr ?_
      rw [length_seqPrefix]
      exact hc n
    obtain ⟨L, R, N, -, -, -, hspec⟩ :=
      mSearch_spec (minfQ cd) (minfQ_mono cd) c (2 ^ (c + 1) - 1) 0 w
        (fun n _ => minf_hlevel hcd c n) hwQ
    have harg : Computable (fun n : ℕ => ((c, L, R, max (n + 1) N) : ℕ × ℕ × ℕ × ℕ)) := by
      refine Computable.pair (Computable.const c) (Computable.pair (Computable.const L)
        (Computable.pair (Computable.const R) ?_))
      exact (Primrec.nat_max.comp (Primrec.succ.comp Primrec.id) (Primrec.const N)).to_comp
    have hg : Computable₂ (fun (n : ℕ) (v : BitString) => (v[n]?).getD false) := by
      have h1 : Computable (fun q : ℕ × BitString => q.2[q.1]?) :=
        Computable.list_getElem?.comp Computable.snd Computable.fst
      exact (Computable.option_getD h1 (Computable.const false)).to₂
    have hpart : Partrec (fun n : ℕ =>
        (mSearch (minfQ cd) (c, L, R, max (n + 1) N)).map (fun v => (v[n]?).getD false)) :=
      Partrec.map ((mSearch_partrec (minfQ cd) (minfQ_primrec cd)).comp harg) hg
    have heq : ∀ n : ℕ,
        (mSearch (minfQ cd) (c, L, R, max (n + 1) N)).map (fun v => (v[n]?).getD false)
          = Part.some (w n) := by
      intro n
      rw [hspec (max (n + 1) N) (le_max_right _ _), Part.map_some]
      congr 1
      have hn : n < max (n + 1) N := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_left _ _)
      simp [seqPrefix, hn]
    exact hpart.of_eq heq

/-! ### Exercises 53–56: incompressible strings and deficiencies -/

/-! ### Machinery for Exercise 53(a) and 53(b): counting incompressible strings -/
/-! ### The finite set of incompressible strings -/

open Classical in
/-- The strings of length `n` of plain complexity at least `n`, as a finite set. -/
noncomputable def incompressibleFinset (U : Map) (n : ℕ) : Finset BitString :=
  (stringsOfLength n).filter (fun x => (n : ℕ∞) ≤ plainK U x)

/-! ### The zero-padding decompressor: many compressible strings -/

/-- Decompressor appending a run of zeros whose length is carried self-delimitingly
by the first component of the program. -/
def zeroPadDecoder : Map := fun pr =>
  Part.some (decodeSecond pr.1 ++ List.replicate (bitsToNat (decodeFirst pr.1)) false)

/-- The zero-padding map is a decompressor: appending a self-delimitingly described run
of zeros is a partial computable operation. -/
lemma zeroPadDecoder_isDecompressor : isDecompressor zeroPadDecoder := by
  have h : Computable (fun pr : BitString × BitString =>
      decodeSecond pr.1 ++ List.replicate (bitsToNat (decodeFirst pr.1)) false) := by
    refine (Primrec.list_append.comp (decodeSecond_primrec.comp Primrec.fst)
      (KraftChaitin.replicate_false_primrec.comp
        (bitsToNat_primrec.comp (decodeFirst_primrec.comp Primrec.fst)))).to_comp
  exact h.partrec

/-! ### The count-as-advice decompressor: few compressible strings -/

/-- Decompressor for Exercise 53(a): the program is `pairCode (bits c) w`, where `w` is a
fixed-width field of `n - c` bits holding the number `M` of incompressible strings of
length `n`.  The length `n = |w| + c` is recovered from the program itself, and the decoder
then dovetails until all `2 ^ n - M` compressible strings of length `n` have shown up; the
first length-`n` string missing from that list is incompressible. -/
noncomputable def countAdviceDecoder (code : Code) : Map := fun pr =>
  Dovetailing.missingSearch code
    ((decodeSecond pr.1).length + bitsToNat (decodeFirst pr.1) - 1,
      (decodeSecond pr.1).length + bitsToNat (decodeFirst pr.1),
      2 ^ ((decodeSecond pr.1).length + bitsToNat (decodeFirst pr.1)) -
        decodeFixedWidthNatCode (decodeSecond pr.1))

/-- The decompressor that takes the number of incompressible strings of length `n` as
advice is indeed a decompressor. -/
lemma countAdviceDecoder_isDecompressor (code : Code) :
    isDecompressor (countAdviceDecoder code) := by
  have hbody : Primrec (fun pr : BitString × BitString => decodeSecond pr.1) :=
    decodeSecond_primrec.comp Primrec.fst
  have hlen : Primrec (fun pr : BitString × BitString =>
      (decodeSecond pr.1).length + bitsToNat (decodeFirst pr.1)) :=
    Primrec.nat_add.comp (Primrec.list_length.comp hbody)
      (bitsToNat_primrec.comp (decodeFirst_primrec.comp Primrec.fst))
  have hdecode : Primrec decodeFixedWidthNatCode := bitsToNat_primrec.comp Primrec.list_reverse
  have hf : Computable (fun pr : BitString × BitString =>
      ((decodeSecond pr.1).length + bitsToNat (decodeFirst pr.1) - 1,
        (decodeSecond pr.1).length + bitsToNat (decodeFirst pr.1),
        2 ^ ((decodeSecond pr.1).length + bitsToNat (decodeFirst pr.1)) -
          decodeFixedWidthNatCode (decodeSecond pr.1))) :=
    (Primrec.pair (Primrec.nat_sub.comp hlen (Primrec.const 1))
      (Primrec.pair hlen
        (Primrec.nat_sub.comp (primrec_two_pow_aux.comp hlen)
          (hdecode.comp hbody)))).to_comp
  exact (Dovetailing.partrec_missingSearch code).comp hf

/-! ### Exercise 53(b): the count itself is incompressible -/

/-- Decompressor for Exercise 53(b): the program is `pairCode (bits t) p`, where `p` is a
`U`-program for the binary expansion of the number `M` of incompressible strings of length
`n`, and `t = n - |bits M|` is the (constantly bounded) correction needed to recover `n`. -/
noncomputable def countProgramDecoder (U : Map) (code : Code) : Map := fun pr =>
  (U (decodeSecond pr.1, [])).bind (fun w =>
    Dovetailing.missingSearch code
      (w.length + bitsToNat (decodeFirst pr.1) - 1,
        w.length + bitsToNat (decodeFirst pr.1),
        2 ^ (w.length + bitsToNat (decodeFirst pr.1)) - bitsToNat w))

/-- The decompressor that takes a `U`-program for the number of incompressible strings
of length `n` as advice is a decompressor whenever `U` is. -/
lemma countProgramDecoder_isDecompressor (U : Map) (hU : isDecompressor U) (code : Code) :
    isDecompressor (countProgramDecoder U code) := by
  have harg : Computable
      (fun pr : BitString × BitString => (decodeSecond pr.1, ([] : BitString))) :=
    Computable.pair (decodeSecond_primrec.comp Primrec.fst).to_comp (Computable.const _)
  have hlen : Primrec (fun q : (BitString × BitString) × BitString =>
      q.2.length + bitsToNat (decodeFirst q.1.1)) :=
    Primrec.nat_add.comp (Primrec.list_length.comp Primrec.snd)
      (bitsToNat_primrec.comp (decodeFirst_primrec.comp (Primrec.fst.comp Primrec.fst)))
  have hf : Computable (fun q : (BitString × BitString) × BitString =>
      (q.2.length + bitsToNat (decodeFirst q.1.1) - 1,
        q.2.length + bitsToNat (decodeFirst q.1.1),
        2 ^ (q.2.length + bitsToNat (decodeFirst q.1.1)) - bitsToNat q.2)) :=
    (Primrec.pair (Primrec.nat_sub.comp hlen (Primrec.const 1))
      (Primrec.pair hlen
        (Primrec.nat_sub.comp (primrec_two_pow_aux.comp hlen)
          (bitsToNat_primrec.comp Primrec.snd)))).to_comp
  exact Partrec.bind (hU.comp harg)
    (((Dovetailing.partrec_missingSearch code).comp hf).of_eq (fun _ => rfl))

private lemma mem_incompressibleFinset (U : Map) (n : ℕ) (x : BitString) :
    x ∈ incompressibleFinset U n ↔ x.length = n ∧ (n : ℕ∞) ≤ plainK U x := by
  classical
  unfold incompressibleFinset
  rw [Finset.mem_filter, mem_stringsOfLength]

private lemma incompressible_set_eq_coe (U : Map) (n : ℕ) :
    {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK U x} = ↑(incompressibleFinset U n) := by
  ext x
  simp [mem_incompressibleFinset]

private lemma enat_le_pred_iff (n : ℕ) (hn : 1 ≤ n) (a : ℕ∞) :
    a ≤ ((n - 1 : ℕ) : ℕ∞) ↔ ¬ ((n : ℕ∞) ≤ a) := by
  constructor
  · intro h hle
    have : ((n : ℕ) : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := hle.trans h
    have : n ≤ n - 1 := by exact_mod_cast this
    omega
  · intro h
    have hlt : a < (n : ℕ∞) := not_le.mp h
    have hne : a ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hk] at hlt ⊢
    have : k < n := by exact_mod_cast hlt
    exact_mod_cast Nat.le_pred_of_lt this

/-- The incompressible strings and the strings enumerated with complexity bound `n-1`
partition the strings of length `n`. -/
private lemma card_incompressibleFinset_add_sliceCount (U : Map) (c : Code) (hc : IsCodeFor c U)
    (n : ℕ) (hn : 1 ≤ n) :
    (incompressibleFinset U n).card + Dovetailing.sliceCount c (n - 1) n = 2 ^ n := by
  classical
  set G := (Dovetailing.completedLengthSlice c (n - 1) n).toFinset with hG
  have hnodup : (Dovetailing.completedLengthSlice c (n - 1) n).Nodup := by
    unfold Dovetailing.completedLengthSlice
    exact (boundedOutputStage_nodup c (n - 1) _).filter _
  have hGcard : G.card = Dovetailing.sliceCount c (n - 1) n := by
    rw [hG, List.toFinset_card_of_nodup hnodup, Dovetailing.sliceCount_eq_length]
  have hmemG : ∀ x, x ∈ G ↔ (x.length = n ∧ ¬ ((n : ℕ∞) ≤ plainK U x)) := by
    intro x
    rw [hG, List.mem_toFinset, Dovetailing.mem_completedLengthSlice_iff hc]
    rw [enat_le_pred_iff n hn]
    tauto
  have hGsub : G ⊆ stringsOfLength n := by
    intro x hx
    rw [mem_stringsOfLength]
    exact ((hmemG x).mp hx).1
  have hsplit : incompressibleFinset U n = stringsOfLength n \ G := by
    ext x
    rw [mem_incompressibleFinset, Finset.mem_sdiff, mem_stringsOfLength, hmemG]
    tauto
  have hcards := Finset.card_sdiff_add_card_eq_card hGsub
  rw [card_stringsOfLength, hGcard] at hcards
  rw [hsplit]
  omega

private lemma zeroPad_produces (k : ℕ) (y : BitString) :
    produces zeroPadDecoder (pairCode (Nat.bits k) y) [] (y ++ List.replicate k false) := by
  change _ ∈ zeroPadDecoder _
  unfold zeroPadDecoder
  simp [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

private lemma three_mul_add_lt_two_pow : ∀ C : ℕ, 3 * C + 11 < 2 ^ (C + 4) := by
  intro C
  induction C with
  | zero => norm_num
  | succ k ih =>
    have h : (2 : ℕ) ^ (k + 1 + 4) = 2 * 2 ^ (k + 4) := by ring
    omega

/-- A padding length large enough that padded strings are strictly compressible. -/
private lemma exists_pad_constant (C : ℕ) :
    ∃ c : ℕ, C + 1 ≤ c ∧ 2 * (Nat.bits c).length + 1 + C < c := by
  refine ⟨2 ^ (C + 4), ?_, ?_⟩
  · have h := three_mul_add_lt_two_pow C
    omega
  · have hsize : (Nat.bits (2 ^ (C + 4))).length = C + 5 := by
      rw [Nat.size_eq_bits_len, Nat.size_pow]
    rw [hsize]
    have h := three_mul_add_lt_two_pow C
    omega

/-- There are at least `2 ^ (n - c)` compressible strings of length `n`. -/
private lemma card_incompressibleFinset_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ n : ℕ, c ≤ n →
      2 ^ (n - c) + (incompressibleFinset U n).card ≤ 2 ^ n := by
  classical
  obtain ⟨C, hC⟩ := hU.2 zeroPadDecoder zeroPadDecoder_isDecompressor
  obtain ⟨c, hc1, hc2⟩ := exists_pad_constant C
  refine ⟨c, by omega, fun n hn => ?_⟩
  set L := (Nat.bits c).length with hL
  have hmaps : ∀ y ∈ stringsOfLength (n - c),
      y ++ List.replicate c false ∈ stringsOfLength n \ incompressibleFinset U n := by
    intro y hy
    rw [mem_stringsOfLength] at hy
    have hlen : (y ++ List.replicate c false).length = n := by
      rw [List.length_append, List.length_replicate, hy]
      omega
    have hprog : (pairCode (Nat.bits c) y).length = 2 * L + 1 + (n - c) := by
      rw [length_pairCode, hy, ← hL]
      ring
    have hle : plainK U (y ++ List.replicate c false) ≤ ((2 * L + 1 + (n - c) + C : ℕ) : ℕ∞) := by
      refine (hC (y ++ List.replicate c false) []).trans ?_
      have h2 : condK zeroPadDecoder (y ++ List.replicate c false) []
          ≤ ((2 * L + 1 + (n - c) : ℕ) : ℕ∞) := by
        refine sInf_le ⟨pairCode (Nat.bits c) y, zeroPad_produces c y, ?_⟩
        rw [show programLength (pairCode (Nat.bits c) y)
            = (pairCode (Nat.bits c) y).length from rfl, hprog]
      calc condK zeroPadDecoder (y ++ List.replicate c false) [] + (C : ℕ∞)
          ≤ ((2 * L + 1 + (n - c) : ℕ) : ℕ∞) + (C : ℕ∞) := by gcongr
        _ = ((2 * L + 1 + (n - c) + C : ℕ) : ℕ∞) := by push_cast; ring
    have hlt : 2 * L + 1 + (n - c) + C < n := by omega
    rw [Finset.mem_sdiff, mem_stringsOfLength, mem_incompressibleFinset]
    refine ⟨hlen, ?_⟩
    rintro ⟨-, hge⟩
    have : ((n : ℕ) : ℕ∞) ≤ ((2 * L + 1 + (n - c) + C : ℕ) : ℕ∞) := hge.trans hle
    have : n ≤ 2 * L + 1 + (n - c) + C := by exact_mod_cast this
    omega
  have hinj : Set.InjOn (fun y : BitString => y ++ List.replicate c false)
      ↑(stringsOfLength (n - c)) := by
    intro a _ b _ hab
    exact List.append_cancel_right hab
  have hcard : (stringsOfLength (n - c)).card
      ≤ (stringsOfLength n \ incompressibleFinset U n).card :=
    Finset.card_le_card_of_injOn (fun y : BitString => y ++ List.replicate c false)
      (fun y hy => hmaps y (by simpa using hy)) hinj
  rw [card_stringsOfLength] at hcard
  have hsub : incompressibleFinset U n ⊆ stringsOfLength n := by
    intro x hx
    rw [mem_stringsOfLength]
    exact ((mem_incompressibleFinset U n x).mp hx).1
  have hcards := Finset.card_sdiff_add_card_eq_card hsub
  rw [card_stringsOfLength] at hcards
  omega

private lemma countAdvice_produces (code : Code) (c n M : ℕ) (hc : c ≤ n)
    (hM : M < 2 ^ (n - c)) :
    produces (countAdviceDecoder code) (pairCode (Nat.bits c) (fixedWidthNatCode M (n - c))) []
      (Dovetailing.firstMissing code (n - 1) n
        (Dovetailing.sliceCount code (n - 1) n)) ∨
      2 ^ n - M ≠ Dovetailing.sliceCount code (n - 1) n := by
  by_cases hS : 2 ^ n - M = Dovetailing.sliceCount code (n - 1) n
  · left
    change _ ∈ countAdviceDecoder code _
    unfold countAdviceDecoder
    rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
      fixedWidthNatCode_length hM, decodeFixedWidthNatCode_encode]
    have hn : n - c + c = n := by omega
    rw [hn, hS]
    exact Dovetailing.firstMissing_mem_missingSearch code (n - 1) n
  · exact Or.inr hS

/-- At least `2 ^ (n - c)` strings of length `n` are incompressible. -/
private lemma card_incompressibleFinset_ge (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ n : ℕ, c ≤ n → 2 ^ (n - c) ≤ (incompressibleFinset U n).card := by
  classical
  obtain ⟨code, hcode⟩ := Dovetailing.exists_isCodeFor hU
  obtain ⟨C, hC⟩ := hU.2 (countAdviceDecoder code) (countAdviceDecoder_isDecompressor code)
  obtain ⟨c, hc1, hc2⟩ := exists_pad_constant C
  refine ⟨c, by omega, fun n hn => ?_⟩
  by_contra hlt
  push_neg at hlt
  set M := (incompressibleFinset U n).card with hM
  set L := (Nat.bits c).length with hL
  have hn1 : 1 ≤ n := by omega
  have hpart := card_incompressibleFinset_add_sliceCount U code hcode n hn1
  have hSeq : 2 ^ n - M = Dovetailing.sliceCount code (n - 1) n := by omega
  -- there is at least one incompressible string, so the slice is not everything
  have hMpos : 1 ≤ M := by
    obtain ⟨s, hs_len, hs_K⟩ := exists_incompressible_string U [] n
    have : s ∈ incompressibleFinset U n := (mem_incompressibleFinset U n s).mpr ⟨hs_len, hs_K⟩
    exact Finset.card_pos.mpr ⟨s, this⟩
  have hSlt : Dovetailing.sliceCount code (n - 1) n < 2 ^ n := by omega
  set x := Dovetailing.firstMissing code (n - 1) n (Dovetailing.sliceCount code (n - 1) n) with hx
  have hprod := (countAdvice_produces code c n M hn hlt).resolve_right (by rw [hSeq]; simp)
  have hproglen : (pairCode (Nat.bits c) (fixedWidthNatCode M (n - c))).length
      = 2 * L + 1 + (n - c) := by
    rw [length_pairCode, fixedWidthNatCode_length hlt, ← hL]
    ring
  have hle : plainK U x ≤ ((2 * L + 1 + (n - c) + C : ℕ) : ℕ∞) := by
    refine (hC x []).trans ?_
    have h2 : condK (countAdviceDecoder code) x [] ≤ ((2 * L + 1 + (n - c) : ℕ) : ℕ∞) := by
      refine sInf_le ⟨pairCode (Nat.bits c) (fixedWidthNatCode M (n - c)), hprod, ?_⟩
      rw [show programLength (pairCode (Nat.bits c) (fixedWidthNatCode M (n - c)))
        = (pairCode (Nat.bits c) (fixedWidthNatCode M (n - c))).length from rfl, hproglen]
    calc condK (countAdviceDecoder code) x [] + (C : ℕ∞)
        ≤ ((2 * L + 1 + (n - c) : ℕ) : ℕ∞) + (C : ℕ∞) := by gcongr
      _ = ((2 * L + 1 + (n - c) + C : ℕ) : ℕ∞) := by push_cast; ring
  have hgt : ((n - 1 : ℕ) : ℕ∞) < plainK U x :=
    Dovetailing.plainK_firstMissing_gt hcode rfl hSlt
  have hnat : n - 1 < 2 * L + 1 + (n - c) + C := by
    have : ((n - 1 : ℕ) : ℕ∞) < ((2 * L + 1 + (n - c) + C : ℕ) : ℕ∞) := lt_of_lt_of_le hgt hle
    exact_mod_cast this
  omega

private lemma countProgram_produces (U : Map) (code : Code) (t n M : ℕ) (p : BitString)
    (hp : Nat.bits M ∈ U (p, [])) (ht : (Nat.bits M).length + t = n)
    (hS : 2 ^ n - M = Dovetailing.sliceCount code (n - 1) n) :
    produces (countProgramDecoder U code) (pairCode (Nat.bits t) p) []
      (Dovetailing.firstMissing code (n - 1) n (Dovetailing.sliceCount code (n - 1) n)) := by
  change _ ∈ countProgramDecoder U code _
  unfold countProgramDecoder
  rw [Part.mem_bind_iff]
  refine ⟨Nat.bits M, by rwa [decodeSecond_pairCode], ?_⟩
  rw [decodeFirst_pairCode, bitsToNat_bits, ht, bitsToNat_bits, hS]
  exact Dovetailing.firstMissing_mem_missingSearch code (n - 1) n

/-- **Exercise 53(a).** The number of incompressible strings of length `n` lies
between `2 ^ (n - c)` and `2 ^ n - 2 ^ (n - c)`. -/
theorem card_incompressible_mem_Icc (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK U x}.Finite ∧
      2 ^ (n - c) ≤ {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK U x}.ncard ∧
      {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK U x}.ncard ≤ 2 ^ n - 2 ^ (n - c) := by
  obtain ⟨c1, hc1pos, hc1⟩ := card_incompressibleFinset_ge U hU
  obtain ⟨c2, hc2pos, hc2⟩ := card_incompressibleFinset_le U hU
  refine ⟨max c1 c2, fun n hn => ?_⟩
  have hncard : {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK U x}.ncard
      = (incompressibleFinset U n).card := by
    rw [incompressible_set_eq_coe, Set.ncard_coe_finset]
  have hfin : {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK U x}.Finite := by
    rw [incompressible_set_eq_coe]
    exact (incompressibleFinset U n).finite_toSet
  have hge := hc1 n (le_trans (le_max_left c1 c2) hn)
  have hle := hc2 n (le_trans (le_max_right c1 c2) hn)
  have hpow1 : 2 ^ (n - max c1 c2) ≤ 2 ^ (n - c1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpow2 : 2 ^ (n - max c1 c2) ≤ 2 ^ (n - c2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨hfin, ?_, ?_⟩
  · rw [hncard]; omega
  · rw [hncard]; omega

/-- **Exercise 53(b).** That cardinality itself has complexity `n - O(1)`. -/
theorem plainK_card_incompressible_ge (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      ((n : ℕ) : ℕ∞) ≤
        plainKNat U {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK U x}.ncard + (c : ℕ∞) := by
  classical
  obtain ⟨code, hcode⟩ := Dovetailing.exists_isCodeFor hU
  obtain ⟨C, hC⟩ := hU.2 (countProgramDecoder U code)
    (countProgramDecoder_isDecompressor U hU.1 code)
  obtain ⟨c0, hc0pos, hc0⟩ := card_incompressibleFinset_ge U hU
  obtain ⟨c1, hc1pos, hc1⟩ := card_incompressibleFinset_le U hU
  set K := 2 * (Nat.bits c0).length + 1 with hK
  refine ⟨c0 + c1 + K + C + 1, fun n => ?_⟩
  set c := c0 + c1 + K + C + 1 with hc
  by_cases hsmall : n ≤ c
  · calc ((n : ℕ) : ℕ∞) ≤ ((c : ℕ) : ℕ∞) := by exact_mod_cast hsmall
      _ ≤ plainKNat U {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK U x}.ncard + (c : ℕ∞) :=
        le_add_self
  push_neg at hsmall
  have hn0 : c0 ≤ n := by omega
  have hn1 : c1 ≤ n := by omega
  have hnpos : 1 ≤ n := by omega
  have hncard : {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK U x}.ncard
      = (incompressibleFinset U n).card := by
    rw [incompressible_set_eq_coe, Set.ncard_coe_finset]
  rw [hncard]
  set M := (incompressibleFinset U n).card with hM
  have hMge := hc0 n hn0
  have hMle := hc1 n hn1
  have hpow1 : 1 ≤ 2 ^ (n - c1) := Nat.one_le_two_pow
  have hMlt : M < 2 ^ n := by omega
  have hMpos : 1 ≤ M := by
    have : (1 : ℕ) ≤ 2 ^ (n - c0) := Nat.one_le_two_pow
    omega
  have hpart := card_incompressibleFinset_add_sliceCount U code hcode n hnpos
  have hS : 2 ^ n - M = Dovetailing.sliceCount code (n - 1) n := by omega
  have hSlt : Dovetailing.sliceCount code (n - 1) n < 2 ^ n := by omega
  -- the bit length of `M` is within `c0` of `n`
  have hsize_le : (Nat.bits M).length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hMlt
  have hsize_ge : n - c0 < (Nat.bits M).length := by
    rw [Nat.size_eq_bits_len]
    by_contra hcon
    push_neg at hcon
    have : M < 2 ^ (n - c0) := Nat.size_le.mp hcon
    omega
  set t := n - (Nat.bits M).length with ht_def
  have ht : (Nat.bits M).length + t = n := by omega
  have htc0 : t ≤ c0 := by omega
  -- a shortest program for `bits M`
  by_cases htop : plainKNat U M = ⊤
  · rw [htop]; simp
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp htop
  have hjK : plainK U (Nat.bits M) = (j : ℕ∞) := hj.symm
  obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U (Nat.bits M) [] j).mp (le_of_eq hjK)
  have hpl : programLength p = p.length := rfl
  set x := Dovetailing.firstMissing code (n - 1) n (Dovetailing.sliceCount code (n - 1) n) with hx
  have hprod := countProgram_produces U code t n M p hp_prod ht hS
  have hproglen : (pairCode (Nat.bits t) p).length ≤ K + j := by
    rw [length_pairCode]
    have := length_natBits_mono htc0
    omega
  have hle : plainK U x ≤ ((K + j + C : ℕ) : ℕ∞) := by
    refine (hC x []).trans ?_
    have h2 : condK (countProgramDecoder U code) x [] ≤ ((K + j : ℕ) : ℕ∞) := by
      refine le_trans (sInf_le ⟨pairCode (Nat.bits t) p, hprod, rfl⟩) ?_
      exact_mod_cast hproglen
    calc condK (countProgramDecoder U code) x [] + (C : ℕ∞)
        ≤ ((K + j : ℕ) : ℕ∞) + (C : ℕ∞) := by gcongr
      _ = ((K + j + C : ℕ) : ℕ∞) := by push_cast; ring
  have hgt : ((n - 1 : ℕ) : ℕ∞) < plainK U x :=
    Dovetailing.plainK_firstMissing_gt hcode rfl hSlt
  have hnat : n - 1 < K + j + C := by
    have : ((n - 1 : ℕ) : ℕ∞) < ((K + j + C : ℕ) : ℕ∞) := lt_of_lt_of_le hgt hle
    exact_mod_cast this
  have hfin : n ≤ j + c := by omega
  calc ((n : ℕ) : ℕ∞) ≤ ((j + c : ℕ) : ℕ∞) := by exact_mod_cast hfin
    _ = (j : ℕ∞) + (c : ℕ∞) := by push_cast; ring
    _ = plainKNat U M + (c : ℕ∞) := by rw [← hjK]; rfl

end Kolmogorov
