import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Complexity.InfiniteSequences.PrefixComplexity

/-!
# Four complexities of an infinite sequence

The complexity of an infinite binary sequence can be measured in four ways, all defined here:
`seqC` (the least complexity of a program computing every prefix from its index), `seqCinf`
(the same for all sufficiently long prefixes), `seqM` (the supremum of the conditional
complexities of the prefixes) and `seqMinf` (their limit superior).

The module establishes the gaps between them.  The witness is a sequence `1^B 0 0 …`, from
which the parameter `B` can be extracted from any generator program — that extraction is
`fExtractBody` and `fExtract`, partial computable by `f_extract_partrec`.  The counting side
is the `cinfGap*` family: `cinfGapPrograms`, `cinfGapHaltTime`, `cinfGapStage`,
`cinfGapOutputs` and `cinfGapOutputStage` produce, at a stage by which all short programs have
halted, a string of length `m` that none of them outputs.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution
variable (Q : ℕ × ℕ × BitString → Bool)

/-- `C(x)` for an infinite sequence: the minimal complexity of a program that,
given `n`, computes the `n`-bit prefix. -/
noncomputable def seqC (U : Map) (w : ℕ → Bool) : ℕ∞ :=
  sInf {v : ℕ∞ | ∃ e : ℕ, (∀ n : ℕ, Encodable.encode (seqPrefix w n) ∈
    (Denumerable.ofNat Code e).eval (Encodable.encode n)) ∧ plainKNat U e = v}

/-- `C^∞(x)`: the minimal complexity of a program computing the prefixes of `w`
for all sufficiently large lengths. -/
noncomputable def seqCinf (U : Map) (w : ℕ → Bool) : ℕ∞ :=
  sInf {v : ℕ∞ | ∃ e N : ℕ, (∀ n : ℕ, N ≤ n → Encodable.encode (seqPrefix w n) ∈
    (Denumerable.ofNat Code e).eval (Encodable.encode n)) ∧ plainKNat U e = v}

/-- `M(x) = sup_n C(x_0 … x_{n-1} | n)`. -/
noncomputable def seqM (U : Map) (w : ℕ → Bool) : ℕ∞ :=
  ⨆ n : ℕ, condK U (seqPrefix w n) (Nat.bits n)

/-- `M_∞(x) = limsup_n C(x_0 … x_{n-1} | n)`. -/
noncomputable def seqMinf (U : Map) (w : ℕ → Bool) : ℕ∞ :=
  Filter.limsup (fun n : ℕ => condK U (seqPrefix w n) (Nat.bits n)) Filter.atTop

/-- The programs of length strictly less than `m`. -/
def cinfGapPrograms (m : ℕ) : List BitString :=
  (boundedPrograms (m - 1)).filter (fun p => p.length < m)

private lemma cinfGapPrograms_length (m : ℕ) : (cinfGapPrograms m).length < 2^m := by
  dsimp [cinfGapPrograms]
  cases m with
  | zero => simp [boundedPrograms, exactLengthPrograms]
  | succ m =>
    refine lt_of_le_of_lt (List.length_filter_le _ _) ?_
    have h_lt := length_boundedPrograms_lt m
    exact h_lt

open Classical in
/-- The first step at which the machine `c` halts on the program `p` with condition `m`, and
`0` if it never halts. -/
noncomputable def cinfGapHaltTime (c : Code) (m : ℕ) (p : BitString) : ℕ :=
  if h : ∃ t, (Code.evaln t c (Encodable.encode (p, Nat.bits m))).isSome = true then
    Nat.find h
  else
    0

/-- The stage by which every halting program of length below `m` has halted on condition `m`. -/
noncomputable def cinfGapStage (c : Code) (m : ℕ) : ℕ :=
  ((cinfGapPrograms m).map (cinfGapHaltTime c m)).foldr max 0

/-- The outputs produced within `t` steps by the programs of length below `m` on condition `m`. -/
def cinfGapOutputs (c : Code) (m t : ℕ) : List BitString :=
  (cinfGapPrograms m).filterMap (fun p =>
    (Code.evaln t c (Encodable.encode (p, Nat.bits m))).bind (fun r => Encodable.decode r))

/-- The first string of length `m` not produced within `t` steps by any program shorter than
`m`; a string of complexity at least `m` once `t` is large enough. -/
def cinfGapOutputStage (c : Code) (m t : ℕ) : BitString :=
  ((allStrings m).find? (fun s => decide (s ∉ cinfGapOutputs c m t))).getD []

private lemma cinfGap_find_eq_some (c : Code) (m t : ℕ) :
    ∃ s, (allStrings m).find? (fun s => decide (s ∉ cinfGapOutputs c m t)) = some s := by
  have h_ex : ∃ s ∈ allStrings m, s ∉ cinfGapOutputs c m t := by
    by_contra! h_all
    have h_sub : (allStrings m).toFinset ⊆ (cinfGapOutputs c m t).toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      exact h_all x hx
    have h_card := Finset.card_le_card h_sub
    rw [List.toFinset_card_of_nodup (allStrings_nodup m)] at h_card
    have h_card2 : (cinfGapOutputs c m t).toFinset.card ≤ (cinfGapOutputs c m t).length :=
      List.toFinset_card_le _
    have h1 : (allStrings m).length = 2^m := length_allStrings m
    have h2 : (cinfGapOutputs c m t).length < 2^m := by
      dsimp [cinfGapOutputs]
      refine lt_of_le_of_lt (List.length_filterMap_le _ _) (cinfGapPrograms_length m)
    omega
  rcases h_ex with ⟨s, hs_mem, hs_not_mem⟩
  have h_pred : ∃ y ∈ allStrings m, (decide (y ∉ cinfGapOutputs c m t)) = true :=
    ⟨s, hs_mem, decide_eq_true hs_not_mem⟩
  exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr h_pred)

private lemma cinfGapOutputStage_spec (c : Code) (m t : ℕ) :
    cinfGapOutputStage c m t ∈ allStrings m ∧
    cinfGapOutputStage c m t ∉ cinfGapOutputs c m t := by
  obtain ⟨s, hs⟩ := cinfGap_find_eq_some c m t
  have hs_mem := List.mem_of_find?_eq_some hs
  have hs_pred := List.find?_some hs
  simp only [decide_eq_true_eq] at hs_pred
  dsimp [cinfGapOutputStage]
  rw [hs]
  simp [hs_mem, hs_pred]

private lemma cinfGapOutputStage_length (c : Code) (m t : ℕ) :
    (cinfGapOutputStage c m t).length = m := by
  have h := (cinfGapOutputStage_spec c m t).1
  exact (mem_allStrings m _).mp h

private lemma cinfGapOutputStage_not_mem (c : Code) (m t : ℕ) :
    cinfGapOutputStage c m t ∉ cinfGapOutputs c m t :=
  (cinfGapOutputStage_spec c m t).2

private lemma cinfGapHaltTime_le_T (c : Code) (m : ℕ) (p : BitString) (hp : p ∈ cinfGapPrograms m) :
    cinfGapHaltTime c m p ≤ cinfGapStage c m := by
  dsimp [cinfGapStage]
  have h_mem : cinfGapHaltTime c m p ∈ (cinfGapPrograms m).map (cinfGapHaltTime c m) :=
    List.mem_map_of_mem (f := cinfGapHaltTime c m) hp
  generalize (cinfGapPrograms m).map (cinfGapHaltTime c m) = L at h_mem
  induction h_mem with
  | head => exact le_max_left _ _
  | tail _ _ ih => exact le_trans ih (le_max_right _ _)

private lemma cinfGap_evaln_of_stage_le (c : Code) (m t : ℕ) (ht : cinfGapStage c m ≤ t)
    (p : BitString) (hp : p ∈ cinfGapPrograms m)
    (w : BitString) (hw : Encodable.encode w ∈ c.eval (Encodable.encode (p, Nat.bits m))) :
    Code.evaln t c (Encodable.encode (p, Nat.bits m)) = some (Encodable.encode w) := by
  obtain ⟨t0, ht0⟩ := Nat.Partrec.Code.evaln_complete.mp hw
  have h_ex : ∃ t, (Code.evaln t c (Encodable.encode (p, Nat.bits m))).isSome = true :=
    ⟨t0, Option.isSome_iff_exists.mpr ⟨Encodable.encode w, ht0⟩⟩
  have h_p_time : cinfGapHaltTime c m p = Nat.find h_ex := by
    unfold cinfGapHaltTime; dsimp; exact dif_pos h_ex
  have h_find_le : Nat.find h_ex ≤ t0 :=
    Nat.find_le (Option.isSome_iff_exists.mpr ⟨Encodable.encode w, ht0⟩)
  have h_ptime_le_T : cinfGapHaltTime c m p ≤ cinfGapStage c m := cinfGapHaltTime_le_T c m p hp
  have h_ptime_le_t : Nat.find h_ex ≤ t := h_p_time.symm ▸ le_trans h_ptime_le_T ht
  have h_find_spec := Nat.find_spec h_ex
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h_find_spec
  have hr_mono : r ∈ Code.evaln t0 c (Encodable.encode (p, Nat.bits m)) :=
    Nat.Partrec.Code.evaln_mono h_find_le hr
  rw [Option.mem_def] at ht0 hr_mono
  have hr_eq : r = Encodable.encode w := Option.some_injective _ (hr_mono.symm.trans ht0)
  subst hr_eq
  exact Option.mem_def.mp (Nat.Partrec.Code.evaln_mono h_ptime_le_t hr)

private lemma cinfGap_evaln_eq_of_stage_le (c : Code) (m t : ℕ) (ht : cinfGapStage c m ≤ t)
    (p : BitString) (hp : p ∈ cinfGapPrograms m) :
    Code.evaln t c (Encodable.encode (p, Nat.bits m)) =
    Code.evaln (cinfGapStage c m) c (Encodable.encode (p, Nat.bits m)) := by
  cases h_eval : Code.evaln (cinfGapStage c m) c (Encodable.encode (p, Nat.bits m)) with
  | none =>
    cases h_eval2 : Code.evaln t c (Encodable.encode (p, Nat.bits m)) with
    | none => rfl
    | some r =>
      have h_mem : r ∈ Code.evaln t c (Encodable.encode (p, Nat.bits m)) :=
        Option.mem_def.mpr h_eval2
      have h_sound : r ∈ c.eval (Encodable.encode (p, Nat.bits m)) :=
        Code.evaln_sound h_mem
      obtain ⟨t0, ht0⟩ := Nat.Partrec.Code.evaln_complete.mp h_sound
      have h_ex : ∃ t, (Code.evaln t c (Encodable.encode (p, Nat.bits m))).isSome = true :=
        ⟨t0, Option.isSome_iff_exists.mpr ⟨r, ht0⟩⟩
      have h_p_time : cinfGapHaltTime c m p = Nat.find h_ex := by
        unfold cinfGapHaltTime; dsimp; exact dif_pos h_ex
      have h_find_spec := Nat.find_spec h_ex
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp h_find_spec
      have h_ptime_le_T : cinfGapHaltTime c m p ≤ cinfGapStage c m := cinfGapHaltTime_le_T c m p hp
      have h_ptime_le_T' : Nat.find h_ex ≤ cinfGapStage c m := h_p_time ▸ h_ptime_le_T
      have hr_mono := Nat.Partrec.Code.evaln_mono h_ptime_le_T' hr'
      rw [Option.mem_def] at hr_mono
      rw [h_eval] at hr_mono
      contradiction
  | some r =>
    have h_mono := Nat.Partrec.Code.evaln_mono ht (Option.mem_def.mpr h_eval)
    rw [Option.mem_def] at h_mono
    rw [h_mono]

private lemma cinfGapOutputs_of_T_le (c : Code) (m t : ℕ) (ht : cinfGapStage c m ≤ t) :
    cinfGapOutputs c m t = cinfGapOutputs c m (cinfGapStage c m) := by
  dsimp [cinfGapOutputs, Encodable.encode]
  apply List.filterMap_congr
  intro p hp
  have h_eq := cinfGap_evaln_eq_of_stage_le c m t ht p hp
  dsimp [Encodable.encode] at h_eq
  rw [h_eq]

/-- The length-`m` string of conditional complexity at least `m` obtained at the stage by which
all short programs have halted. -/
noncomputable def cinfGapWord (c : Code) (m : ℕ) : BitString :=
  cinfGapOutputStage c m (cinfGapStage c m)

/-- The infinite sequence whose first `m` bits are `cinfGapWord c m` and which is zero after. -/
noncomputable def cinfGapSequence (c : Code) (m : ℕ) : ℕ → Bool :=
  fun i => (cinfGapWord c m).getD i false

private theorem cinfGapSequence_computable (c : Code) (m : ℕ) :
    Computable (cinfGapSequence c m) := by
  have h : cinfGapSequence c m = (fun i => (cinfGapWord c m).getD i false) := rfl
  rw [h]
  exact ((Primrec.list_getD false).comp (Primrec.const (cinfGapWord c m)) Primrec.id).to_comp

private theorem cinfGap_prefix_m (c0 : Code) (m : ℕ) :
    seqPrefix (cinfGapSequence c0 m) m = cinfGapWord c0 m := by
  have hlen : (cinfGapWord c0 m).length = m := cinfGapOutputStage_length c0 m (cinfGapStage c0 m)
  ext i
  by_cases hi : i < m
  · have h1 : (seqPrefix (cinfGapSequence c0 m) m)[i]? = some (cinfGapSequence c0 m i) := by
      simp [seqPrefix, hi]
    dsimp [cinfGapSequence] at h1
    rw [h1]
    have hi' : i < (cinfGapWord c0 m).length := hlen.symm ▸ hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    rfl
  · have h1 : (seqPrefix (cinfGapSequence c0 m) m)[i]? = none := by simp [seqPrefix, hi]
    have h2 : (cinfGapWord c0 m)[i]? = none := by
      rw [List.getElem?_eq_none]
      omega
    rw [h1, h2]

/-- The length-`n` prefix of the gap sequence for the parameter `m`, computed from the stage-`n`
approximation and padded with zeros beyond length `m`. -/
def cinfGapPrefix (c : Code) (pr : BitString × BitString) : BitString :=
  let m := bitsToNat pr.1
  let n := bitsToNat pr.2
  let y := cinfGapOutputStage c m n
  bif decide (n ≤ m) then y.take n
  else y ++ List.replicate (n - m) false

/-- The total decompressor computing prefixes of the gap sequence from `m` and the prefix length. -/
def cinfGapMap (c : Code) : Map := fun pr => Part.some (cinfGapPrefix c pr)

private theorem cinfGapPrefix_at_large (c0 : Code) (m n : ℕ) (hn : max m (cinfGapStage c0 m) ≤ n) :
    cinfGapPrefix c0 (Nat.bits m, Nat.bits n) = seqPrefix (cinfGapSequence c0 m) n := by
  dsimp [cinfGapPrefix]
  rw [bitsToNat_bits, bitsToNat_bits]
  have h_T_le : cinfGapStage c0 m ≤ n := le_trans (le_max_right m (cinfGapStage c0 m)) hn
  have h_m_le : m ≤ n := le_trans (le_max_left m (cinfGapStage c0 m)) hn
  have h_ym_eq : cinfGapOutputStage c0 m n = cinfGapWord c0 m := by
    dsimp [cinfGapOutputStage, cinfGapWord]
    rw [cinfGapOutputs_of_T_le c0 m n h_T_le]
  rw [h_ym_eq]
  have hlen : (cinfGapWord c0 m).length = m := cinfGapOutputStage_length c0 m (cinfGapStage c0 m)
  by_cases h_eq : n ≤ m
  · have h_nm : n = m := by omega
    subst h_nm
    have h_dec : decide (n ≤ n) = true := decide_eq_true (by omega)
    rw [h_dec]
    dsimp only [cond_true]
    rw [cinfGap_prefix_m c0 n]
    exact List.take_of_length_le (by rw [hlen])
  · have h_dec : decide (n ≤ m) = false := decide_eq_false h_eq
    rw [h_dec]
    simp only [cond_false]
    ext i
    by_cases hi : i < n
    · have h1 : (seqPrefix (cinfGapSequence c0 m) n)[i]? = some (cinfGapSequence c0 m i) := by
        simp [seqPrefix, hi]
      rw [h1]
      dsimp [cinfGapSequence]
      by_cases h_im : i < m
      · have h3 :
            (cinfGapWord c0 m ++ List.replicate (n - m) false)[i]? = (cinfGapWord c0 m)[i]? := by
          rw [List.getElem?_append_left]
          rw [hlen]
          exact h_im
        rw [h3]
        have hi' : i < (cinfGapWord c0 m).length := hlen.symm ▸ h_im
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
        rfl
      · have h3 : (cinfGapWord c0 m ++ List.replicate (n - m) false)[i]? =
            (List.replicate (n - m) false)[i - m]? := by
          rw [List.getElem?_append_right (by rw [hlen]; omega)]
          rw [hlen]
        rw [h3]
        have h_sub : i - m < n - m := by omega
        rw [List.getElem?_replicate]
        rw [if_pos h_sub]
        rw [List.getD_eq_getElem?_getD]
        have h_none : (cinfGapWord c0 m)[i]? = none := by
          rw [List.getElem?_eq_none]
          rw [hlen]
          omega
        rw [h_none]
        rfl
    · have h1 : (seqPrefix (cinfGapSequence c0 m) n)[i]? = none := by simp [seqPrefix, hi]
      have h2 : (cinfGapWord c0 m ++ List.replicate (n - m) false)[i]? = none := by
        rw [List.getElem?_append]
        have h1_not : ¬ i < (cinfGapWord c0 m).length := by rw [hlen]; omega
        have h2_not : ¬ i - (cinfGapWord c0 m).length < n - m := by rw [hlen]; omega
        simp [h1_not, h2_not]
      rw [h1, h2]

private theorem cinfGapPrograms_primrec : Primrec cinfGapPrograms := by
  have hm1 : Primrec (fun m : ℕ => m - 1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  have hbp : Primrec (fun m : ℕ => boundedPrograms (m - 1)) := primrec_boundedPrograms.comp hm1
  have hpred : Primrec₂ (fun (m : ℕ) (w : BitString) => decide (w.length < m)) :=
    PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst)
  exact list_filter_primrec hbp hpred

private theorem cinfGapOutputs_primrec (c : Code) :
    Primrec (fun p : ℕ × ℕ => cinfGapOutputs c p.1 p.2) := by
  have hpr : Primrec (fun p : ℕ × ℕ => cinfGapPrograms p.1) :=
    cinfGapPrograms_primrec.comp Primrec.fst
  have hcode : Primrec (fun q : (ℕ × ℕ) × BitString =>
      Code.evaln q.1.2 c (Encodable.encode (q.2, Nat.bits q.1.1))) := by
    have h1 : Primrec (fun q : (ℕ × ℕ) × BitString => q.1.2) := Primrec.snd.comp Primrec.fst
    have h2 : Primrec (fun q : (ℕ × ℕ) × BitString =>
        Encodable.encode (q.2, Nat.bits q.1.1)) :=
      Primrec.encode.comp
        (Primrec.pair Primrec.snd (primrec_natBits.comp (Primrec.fst.comp Primrec.fst)))
    exact Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair (Primrec.pair h1 (Primrec.const c)) h2)
  have hbind : Primrec (fun q : (ℕ × ℕ) × BitString =>
      (Code.evaln q.1.2 c (Encodable.encode (q.2, Nat.bits q.1.1))).bind
        (fun r => Encodable.decode (α := BitString) r)) :=
    Primrec.option_bind hcode (Primrec.decode.comp Primrec.snd).to₂
  exact Primrec.listFilterMap hpr hbind.to₂

private theorem cinfGapOutputStage_primrec (c : Code) :
    Primrec (fun p : ℕ × ℕ => cinfGapOutputStage c p.1 p.2) := by
  have hall : Primrec (fun p : ℕ × ℕ => allStrings p.1) :=
    allStrings_primrec.comp Primrec.fst
  have houts : Primrec (fun p : ℕ × ℕ => cinfGapOutputs c p.1 p.2) := cinfGapOutputs_primrec c
  have hmem := list_mem_decide_primrec.comp Primrec.snd (houts.comp Primrec.fst)
  have hpred : Primrec₂ (fun (p : ℕ × ℕ) (s : BitString) =>
      decide (s ∉ cinfGapOutputs c p.1 p.2)) :=
    (Primrec.not.comp hmem).to₂.of_eq (fun p s => by simp)
  have hfind : Primrec (fun p : ℕ × ℕ =>
      (allStrings p.1).find? (fun s => decide (s ∉ cinfGapOutputs c p.1 p.2))) :=
    list_find?_primrec hall hpred
  exact Primrec.option_getD.comp hfind (Primrec.const [])

private theorem cinfGapPrefix_primrec (c : Code) : Primrec (cinfGapPrefix c) := by
  have hm : Primrec (fun pr : BitString × BitString => bitsToNat pr.1) :=
    bitsToNat_primrec.comp Primrec.fst
  have hn : Primrec (fun pr : BitString × BitString => bitsToNat pr.2) :=
    bitsToNat_primrec.comp Primrec.snd
  have hym : Primrec (fun pr : BitString × BitString =>
      cinfGapOutputStage c (bitsToNat pr.1) (bitsToNat pr.2)) :=
    (cinfGapOutputStage_primrec c).comp (Primrec.pair hm hn)
  have hcond : Primrec (fun pr : BitString × BitString =>
      decide (bitsToNat pr.2 ≤ bitsToNat pr.1)) :=
    PrimrecPred.decide (Primrec.nat_le.comp hn hm)
  have htake : Primrec (fun pr : BitString × BitString =>
      (cinfGapOutputStage c (bitsToNat pr.1) (bitsToNat pr.2)).take (bitsToNat pr.2)) :=
    Primrec.list_take.comp hn hym
  have hsub : Primrec (fun pr : BitString × BitString =>
      bitsToNat pr.2 - bitsToNat pr.1) :=
    Primrec.nat_sub.comp hn hm
  have hrepl : Primrec (fun pr : BitString × BitString =>
      List.replicate (bitsToNat pr.2 - bitsToNat pr.1) false) :=
    Primrec.list_replicate.comp hsub (Primrec.const false)
  have happ : Primrec (fun pr : BitString × BitString =>
      cinfGapOutputStage c (bitsToNat pr.1) (bitsToNat pr.2) ++
        List.replicate (bitsToNat pr.2 - bitsToNat pr.1) false) :=
    Primrec.list_append.comp hym hrepl
  exact Primrec.cond hcond htake happ

private theorem cinfGapPrefix_computable (c : Code) : Computable (cinfGapPrefix c) :=
  (cinfGapPrefix_primrec c).to_comp

/-- The partial function that runs the decompressor `U` on a program with the binary
representation of `n` as condition and returns the code of its output. -/
def cinfGapHalting (U : Map) : (BitString × ℕ) →. ℕ := fun (p, n) =>
  (U (p, Nat.bits n)).map Encodable.encode

/-- The numeric form of the previous partial function, taking a coded program-condition pair. -/
def cinfGapHaltingNat (U : Map) : ℕ →. ℕ := fun m =>
  (Part.ofOption (Encodable.decode (α := BitString × ℕ) m)).bind (cinfGapHalting U)

private theorem cinfGapHaltingNat_partrec {U : Map} (hU : Partrec U) :
    Partrec (cinfGapHaltingNat U) := by
  have h_dec : Computable (fun m => Encodable.decode (α := BitString × ℕ) m) :=
    Computable.decode
  have h_opt : Partrec (fun m => Part.ofOption (Encodable.decode (α := BitString × ℕ) m)) :=
    Computable.ofOption h_dec
  have h_fst : Computable (fun (p : ℕ × (BitString × ℕ)) => p.2.1) :=
    Computable.fst.comp Computable.snd
  have h_snd : Computable (fun (p : ℕ × (BitString × ℕ)) => Nat.bits p.2.2) :=
    natBits_computable.comp (Computable.snd.comp Computable.snd)
  have h_pair : Computable (fun (p : ℕ × (BitString × ℕ)) => (p.2.1, Nat.bits p.2.2)) :=
    Computable.pair h_fst h_snd
  have h_U_app : Partrec (fun (p : ℕ × (BitString × ℕ)) => U (p.2.1, Nat.bits p.2.2)) :=
    Partrec.comp hU h_pair
  have h_H : Partrec (fun (p : ℕ × (BitString × ℕ)) => cinfGapHalting U p.2) :=
    Partrec.map h_U_app (Computable.encode.comp Computable.snd)
  exact Partrec.bind h_opt h_H

private def D1 (U : Map) : Map := fun (p, y) =>
  (U (p, [])).bind fun b =>
    let e := decodeBits b
    let c : Code := Denumerable.ofNat Code e
    (c.eval (Encodable.encode y)).bind fun val =>
      Part.ofOption (Encodable.decode (α := BitString) val)

private lemma D1_partrec {U : Map} (hU : isDecompressor U) : isDecompressor (D1 U) := by
  have hU_app : Partrec (fun (py : BitString × BitString) => U (py.1, [])) :=
    Partrec.comp hU (Computable.pair Computable.fst (Computable.const []))
  have h_c : Computable (fun (p : (BitString × BitString) × BitString) =>
      Denumerable.ofNat Code (decodeBits p.2)) :=
    (Computable.ofNat Code).comp (decodeBits_computable.comp Computable.snd)
  have h_y : Computable (fun (p : (BitString × BitString) × BitString) =>
      Encodable.encode p.1.2) :=
    Computable.encode.comp (Computable.snd.comp Computable.fst)
  have h_pair : Computable (fun (p : (BitString × BitString) × BitString) =>
      (Denumerable.ofNat Code (decodeBits p.2), Encodable.encode p.1.2)) :=
    Computable.pair h_c h_y
  have h_eval : Partrec (fun (p : (BitString × BitString) × BitString) =>
      Code.eval (Denumerable.ofNat Code (decodeBits p.2)) (Encodable.encode p.1.2)) :=
    Partrec.comp Code.eval_part h_pair
  have h_dec : Computable (fun (p : ((BitString × BitString) × BitString) × ℕ) =>
      Encodable.decode (α := BitString) p.2) :=
    Computable.decode.comp Computable.snd
  have h_opt : Partrec (fun (p : ((BitString × BitString) × BitString) × ℕ) =>
      Part.ofOption (Encodable.decode (α := BitString) p.2)) :=
    Computable.ofOption h_dec
  have h_step2 : Partrec (fun (p : (BitString × BitString) × BitString) =>
      (Code.eval (Denumerable.ofNat Code (decodeBits p.2)) (Encodable.encode p.1.2)).bind
        (fun val => Part.ofOption (Encodable.decode (α := BitString) val))) :=
    Partrec.bind h_eval h_opt
  exact Partrec.bind hU_app h_step2

private lemma D1_eval {U : Map} {x y : BitString} {e : ℕ} {p : BitString}
    (hp : Nat.bits e ∈ U (p, []))
    (he : Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y)) :
    produces (D1 U) p y x := by
  dsimp [produces, D1]
  rw [Part.mem_bind_iff]
  refine ⟨Nat.bits e, hp, ?_⟩
  rw [decodeBits_natBits]
  rw [Part.mem_bind_iff]
  refine ⟨Encodable.encode x, he, ?_⟩
  rw [Part.mem_ofOption]
  exact Encodable.encodek x

private def H_func (U : Map) : (BitString × ℕ) →. ℕ := fun (p, ny) =>
  (Part.ofOption (Encodable.decode (α := BitString) ny)).bind fun y =>
    (U (p, y)).map Encodable.encode

private def H_nat (U : Map) : ℕ →. ℕ := fun m =>
  (Part.ofOption (Encodable.decode (α := BitString × ℕ) m)).bind (H_func U)

private lemma H_nat_partrec {U : Map} (hU : Partrec U) : Partrec (H_nat U) := by
  have h_dec : Computable (fun m => Encodable.decode (α := BitString × ℕ) m) :=
    Computable.decode
  have h_opt : Partrec (fun m => Part.ofOption (Encodable.decode (α := BitString × ℕ) m)) :=
    Computable.ofOption h_dec
  have h_H : Partrec (fun (p : ℕ × (BitString × ℕ)) => H_func U p.2) :=
    Partrec.comp (by
      have h_dec' : Computable (fun (p : BitString × ℕ) => Encodable.decode (α := BitString) p.2) :=
        Computable.decode.comp Computable.snd
      have h_opt' : Partrec (fun (p : BitString × ℕ) =>
          Part.ofOption (Encodable.decode (α := BitString) p.2)) :=
        Computable.ofOption h_dec'
      refine Partrec.bind h_opt' ?_
      have h_pair : Computable (fun (p : (BitString × ℕ) × BitString) => (p.1.1, p.2)) :=
        Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
      have h_U_app : Partrec (fun (p : (BitString × ℕ) × BitString) => U (p.1.1, p.2)) :=
        Partrec.comp hU h_pair
      exact Partrec.map h_U_app (Computable.encode.comp Computable.snd)) Computable.snd
  exact Partrec.bind h_opt h_H

private def F_p (cH : Code) (p : BitString) : ℕ :=
  Encodable.encode (cH.curry (Encodable.encode p))

private lemma F_p_computable (cH : Code) : Computable (F_p cH) := by
  have h1 : Computable (fun p : BitString => Encodable.encode p) := Computable.encode
  have h2 : Computable (fun p : BitString => cH.curry (Encodable.encode p)) :=
    (Primrec₂.to_comp Code.primrec₂_curry).comp (Computable.const cH) h1
  exact Computable.encode.comp h2

private def fP (cH : Code) (p : BitString) : BitString :=
  Nat.bits (F_p cH p)

private lemma f_p_computable (cH : Code) : Computable (fP cH) :=
  natBits_computable.comp (F_p_computable cH)

private lemma eval_F_p {U : Map} {cH : Code} (hcH : Code.eval cH = H_nat U) (p x y : BitString)
    (h_prod : x ∈ U (p, y)) :
    Encodable.encode x ∈ (Denumerable.ofNat Code (F_p cH p)).eval (Encodable.encode y) := by
  dsimp [F_p]
  rw [Denumerable.ofNat_encode, Code.eval_curry, hcH]
  dsimp [H_nat]
  refine Part.mem_bind_iff.mpr ⟨(p, Encodable.encode y), ?_, ?_⟩
  · rw [Part.mem_ofOption]
    exact show Encodable.decode (α := BitString × ℕ)
          (Nat.pair (Encodable.encode p) (Encodable.encode y)) =
        some (p, Encodable.encode y) by simp
  · dsimp [H_func]
    rw [Part.mem_bind_iff]
    refine ⟨y, ?_, ?_⟩
    · rw [Part.mem_ofOption]
      exact Encodable.encodek y
    · rw [Part.mem_map_iff]
      exact ⟨x, h_prod, rfl⟩

private lemma condK_min_program_le (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString, condK U x y ≤ programComplexity U x y + (k : ℕ∞) := by
  obtain ⟨k1, hk1⟩ := hU.2 (D1 U) (D1_partrec hU.1)
  refine ⟨k1, fun x y => ?_⟩
  have h_le : condK (D1 U) x y ≤ programComplexity U x y := by
    dsimp [programComplexity]
    apply le_sInf
    rintro v ⟨e, he, rfl⟩
    dsimp [plainKNat, plainK, condK, candidateLengths]
    apply le_sInf
    rintro n ⟨p, hp, rfl⟩
    have h_prod : produces (D1 U) p y x := D1_eval hp he
    apply sInf_le
    exact ⟨p, h_prod, rfl⟩
  calc
    condK U x y ≤ condK (D1 U) x y + (k1 : ℕ∞) := hk1 x y
    _           ≤ programComplexity U x y + (k1 : ℕ∞) := by gcongr

private lemma le_condK_min_program (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString, programComplexity U x y ≤ condK U x y + (k : ℕ∞) := by
  obtain ⟨cH, hcH⟩ := Code.exists_code.mp (Partrec.nat_iff.mp (H_nat_partrec hU.1))
  obtain ⟨c_map, hc_map⟩ := plainK_map_le U hU (fP cH) (f_p_computable cH)
  obtain ⟨c_len, hc_len⟩ := plainK_le_length U hU
  refine ⟨c_len + c_map, fun x y => ?_⟩
  by_cases h_top : condK U x y = ⊤
  · rw [h_top]
    exact le_top
  · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp h_top
    have h_le_u : condK U x y ≤ (u : ℕ∞) := hu.symm.le
    rw [condK_le_iff] at h_le_u
    rcases h_le_u with ⟨p, hp_len, hp_prod⟩
    have h_eval := eval_F_p hcH p x y hp_prod
    have h_in_prog : programComplexity U x y ≤ plainKNat U (F_p cH p) := by
      dsimp [programComplexity]
      apply sInf_le
      exact ⟨F_p cH p, h_eval, rfl⟩
    have h_plain : plainKNat U (F_p cH p) = plainK U (fP cH p) := rfl
    rw [h_plain] at h_in_prog
    have h_map_bound := hc_map p
    have h_len_bound := hc_len p
    have h_total : plainK U (fP cH p) ≤ (programLength p : ℕ∞) +
        ((c_len + c_map : ℕ) : ℕ∞) := by
      calc
        plainK U (fP cH p) ≤ plainK U p + (c_map : ℕ∞) := h_map_bound
        _                   ≤ (programLength p : ℕ∞) + (c_len : ℕ∞) +
            (c_map : ℕ∞) := by gcongr
        _                   = (programLength p : ℕ∞) +
            ((c_len + c_map : ℕ) : ℕ∞) := by simp [add_assoc]
    have h_p_u : (programLength p : ℕ∞) ≤ (u : ℕ∞) := by exact_mod_cast hp_len
    have h2 : (programLength p : ℕ∞) + ((c_len + c_map : ℕ) : ℕ∞) ≤
        (u : ℕ∞) + ((c_len + c_map : ℕ) : ℕ∞) :=
      add_le_add_left h_p_u ((c_len + c_map : ℕ) : ℕ∞)
    exact le_trans h_in_prog (le_trans h_total (hu ▸ h2))

/-- **Exercise 28.** Conditional complexity is the minimal complexity of a
program mapping the condition to the string, up to an additive constant. -/
theorem condK_eq_min_program_complexity (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      condK U x y ≤ programComplexity U x y + (k : ℕ∞) ∧
        programComplexity U x y ≤ condK U x y + (k : ℕ∞) := by
  obtain ⟨k1, hk1⟩ := condK_min_program_le U hU
  obtain ⟨k2, hk2⟩ := le_condK_min_program U hU
  refine ⟨max k1 k2, fun x y => ⟨?_, ?_⟩⟩
  · calc
      condK U x y ≤ programComplexity U x y + (k1 : ℕ∞) := hk1 x y
      _           ≤ programComplexity U x y + (max k1 k2 : ℕ∞) := by
        gcongr
        exact Nat.cast_le.mpr (le_max_left k1 k2)
  · calc
      programComplexity U x y ≤ condK U x y + (k2 : ℕ∞) := hk2 x y
      _                       ≤ condK U x y + (max k1 k2 : ℕ∞) := by
        gcongr
        exact Nat.cast_le.mpr (le_max_right k1 k2)

/-- The code obtained from a program `p` computes, on input `n`, whatever the decompressor
outputs on `p` with condition `n`. -/
theorem eval_F_p_cinfGap {U : Map} {cH : Code} (hcH : Code.eval cH = cinfGapHaltingNat U)
    (p : BitString) (n : ℕ) (x : BitString) (h_prod : x ∈ U (p, Nat.bits n)) :
    Encodable.encode x ∈ (Denumerable.ofNat Code (F_p cH p)).eval (Encodable.encode n) := by
  dsimp [F_p]
  rw [Denumerable.ofNat_encode, Code.eval_curry, hcH]
  dsimp [cinfGapHaltingNat]
  refine Part.mem_bind_iff.mpr ⟨(p, n), by simp, ?_⟩
  · dsimp [cinfGapHalting]
    rw [Part.mem_map_iff]
    exact ⟨x, h_prod, rfl⟩

/-- **Exercise 50.** `C^∞` can be much smaller than `M`. -/
theorem exists_cinf_lt_monotone (U : Map) (hU : isOptimalConditional U) :
    ∃ (x : ℕ → ℕ → Bool) (c : ℕ), ∀ m : ℕ, Computable (x m) ∧
      seqCinf U (x m) ≤ ((c * Nat.log 2 m + c : ℕ) : ℕ∞) ∧ (m : ℕ∞) ≤ seqM U (x m) := by
  obtain ⟨c0, hc0⟩ : ∃ c : Code, IsCodeFor c U := Nat.Partrec.Code.exists_code.mp hU.1
  obtain ⟨c_len, hlen⟩ := plainK_le_length U hU
  have h_map_partrec : Partrec (cinfGapMap c0) :=
    (cinfGapPrefix_computable c0).partrec
  obtain ⟨cH, hcH⟩ :=
    Code.exists_code.mp (Partrec.nat_iff.mp (cinfGapHaltingNat_partrec h_map_partrec))
  obtain ⟨c_map, hc_map⟩ := plainK_map_le U hU (fP cH) (f_p_computable cH)
  set c := c_len + c_map + 5
  refine ⟨cinfGapSequence c0, c, fun m => ⟨cinfGapSequence_computable c0 m, ?_, ?_⟩⟩
  · -- Upper bound on C_inf
    unfold seqCinf
    have h_eval_all : ∀ n, max m (cinfGapStage c0 m) ≤ n →
        Encodable.encode (seqPrefix (cinfGapSequence c0 m) n) ∈
          (Denumerable.ofNat Code (F_p cH (Nat.bits m))).eval (Encodable.encode n) := by
      intro n hn
      have h_prefix := cinfGapPrefix_at_large c0 m n hn
      have h_prod :
          seqPrefix (cinfGapSequence c0 m) n ∈ cinfGapMap c0 (Nat.bits m, Nat.bits n) := by
        unfold cinfGapMap
        rw [h_prefix]
        exact Part.mem_some _
      exact eval_F_p_cinfGap hcH (Nat.bits m) n (seqPrefix (cinfGapSequence c0 m) n) h_prod
    have h_val : plainKNat U (F_p cH (Nat.bits m)) ≤ ((c * Nat.log 2 m + c : ℕ) : ℕ∞) := by
      have h1 := hc_map (Nat.bits m)
      have h3 := hlen (fP cH (Nat.bits m))
      dsimp [plainKNat, fP, programLength] at h1 h3 ⊢
      have h_len_bits : (Nat.bits m).length ≤ Nat.log 2 m + 1 := length_natBits_le_log m
      have h_sum : (Nat.bits m).length + c_len + c_map ≤ c * Nat.log 2 m + c := by
        dsimp [c]
        nlinarith
      have h_trans : plainK U (fP cH (Nat.bits m)) ≤
          (((Nat.bits m).length + c_len + c_map : ℕ) : ℕ∞) := by
        calc plainK U (fP cH (Nat.bits m))
          _ ≤ plainK U (Nat.bits m) + (c_map : ℕ∞) := h1
          _ ≤ ((Nat.bits m).length : ℕ∞) + (c_len : ℕ∞) + (c_map : ℕ∞) := by
            gcongr; exact hlen (Nat.bits m)
          _ = (((Nat.bits m).length + c_len + c_map : ℕ) : ℕ∞) := by push_cast; rfl
      exact le_trans h_trans (WithTop.coe_le_coe.mpr h_sum)
    have h_mem_S : plainKNat U (F_p cH (Nat.bits m)) ∈ {v : ℕ∞ | ∃ e N : ℕ,
        (∀ n : ℕ, N ≤ n → Encodable.encode (seqPrefix (cinfGapSequence c0 m) n) ∈
          (Denumerable.ofNat Code e).eval (Encodable.encode n)) ∧ plainKNat U e = v} :=
      ⟨F_p cH (Nat.bits m), max m (cinfGapStage c0 m), h_eval_all, rfl⟩
    exact (sInf_le h_mem_S).trans h_val
  · -- Lower bound on M
    unfold seqM
    have h_le : condK U (seqPrefix (cinfGapSequence c0 m) m) (Nat.bits m) ≤
        ⨆ n : ℕ, condK U (seqPrefix (cinfGapSequence c0 m) n) (Nat.bits n) :=
      le_iSup (fun n => condK U (seqPrefix (cinfGapSequence c0 m) n) (Nat.bits n)) m
    refine le_trans ?_ h_le
    rw [cinfGap_prefix_m c0 m]
    by_cases hm : m = 0
    · subst hm; exact zero_le
    · by_contra h_lt
      push Not at h_lt
      have h_lt' : condK U (cinfGapWord c0 m) (Nat.bits m) ≤ ((m - 1 : ℕ) : ℕ∞) := by
        cases hK : condK U (cinfGapWord c0 m) (Nat.bits m) with
        | top => rw [hK] at h_lt; contradiction
        | coe k =>
          rw [hK] at h_lt
          have hk : k < m := WithTop.coe_lt_coe.mp h_lt
          have hkm : k ≤ m - 1 := by omega
          exact_mod_cast hkm
      rw [condK_le_iff] at h_lt'
      rcases h_lt' with ⟨p, hp_len, hp_prod⟩
      unfold produces at hp_prod
      have h_eval : c0.eval (Encodable.encode (p, Nat.bits m)) =
          (Part.ofOption (Encodable.decode (Encodable.encode (p, Nat.bits m)))).bind
            (fun a => Part.map Encodable.encode (U a)) := by
        rw [hc0]
      have h_mem_eval : Encodable.encode (cinfGapWord c0 m) ∈
          c0.eval (Encodable.encode (p, Nat.bits m)) := by
        rw [h_eval, Part.mem_bind_iff]
        refine ⟨(p, Nat.bits m), by simp, ?_⟩
        rw [Part.mem_map_iff]
        exact ⟨cinfGapWord c0 m, hp_prod, rfl⟩
      have hp_bp : p ∈ cinfGapPrograms m := by
        dsimp [cinfGapPrograms]
        rw [List.mem_filter]
        refine ⟨(mem_boundedPrograms_iff p (m - 1)).mpr hp_len, ?_⟩
        dsimp [programLength] at hp_len
        exact decide_eq_true (by omega)
      have ht_eval := cinfGap_evaln_of_stage_le c0 m (cinfGapStage c0 m) (le_refl _) p hp_bp
        (cinfGapWord c0 m) h_mem_eval
      have h_in_outs : cinfGapWord c0 m ∈ cinfGapOutputs c0 m (cinfGapStage c0 m) := by
        dsimp [cinfGapOutputs]
        rw [List.mem_filterMap]
        refine ⟨p, hp_bp, ?_⟩
        have ht_eval' := ht_eval
        dsimp [Encodable.encode] at ht_eval'
        change ((Code.evaln (cinfGapStage c0 m) c0
          (Nat.pair (Encodable.encodeList p) (Encodable.encodeList m.bits))).bind
            fun r => Encodable.decode r) = some (cinfGapWord c0 m)
        rw [ht_eval']
        exact Encodable.encodek (cinfGapWord c0 m)
      have h_not_in := cinfGapOutputStage_not_mem c0 m (cinfGapStage c0 m)
      exact h_not_in h_in_outs

/-- Sequence $1^B 000…$ -/
def onesZerosSeq (B : ℕ) : ℕ → Bool := fun i => decide (i < B)

/-- The length-`n` prefix of the sequence `1^B 000…` is `n` ones for `n ≤ B` and `B` ones
followed by `n - B` zeros otherwise. -/
theorem seqPrefix_onesZeros (B n : ℕ) :
    seqPrefix (onesZerosSeq B) n =
      if n ≤ B then List.replicate n true
      else List.replicate B true ++ List.replicate (n - B) false := by
  ext i
  by_cases h : n ≤ B
  · rw [if_pos h]
    by_cases hi : i < n
    · have h1 : (seqPrefix (onesZerosSeq B) n)[i]? = some (decide (i < B)) := by
        simp [seqPrefix, onesZerosSeq, hi]
      have h2 : (List.replicate n true)[i]? = some true := by simp [hi]
      rw [h1, h2]
      have : i < B := by omega
      simp [this]
    · have h1 : (seqPrefix (onesZerosSeq B) n)[i]? = none := by
        simp [seqPrefix, hi]
      have h2 : (List.replicate n true)[i]? = none := by simp [hi]
      rw [h1, h2]
  · rw [if_neg h]
    by_cases hi : i < n
    · have h1 : (seqPrefix (onesZerosSeq B) n)[i]? = some (decide (i < B)) := by
        simp [seqPrefix, onesZerosSeq, hi]
      rw [h1]
      by_cases hiB : i < B
      · have h2 : (List.replicate B true ++ List.replicate (n - B) false)[i]? = some true := by
          rw [List.getElem?_append]
          simp [hiB]
        rw [h2]
        simp [hiB]
      · have h2 : (List.replicate B true ++ List.replicate (n - B) false)[i]? = some false := by
          rw [List.getElem?_append]
          have hnot : ¬ i < B := hiB
          have hlt : i - B < n - B := by omega
          simp [hnot, hlt]
        rw [h2]
        simp [hiB]
    · have h1 : (seqPrefix (onesZerosSeq B) n)[i]? = none := by
        simp [seqPrefix, hi]
      have h2 : (List.replicate B true ++ List.replicate (n - B) false)[i]? = none := by
        rw [List.getElem?_append]
        have hnot1 : ¬ i < B := by omega
        have hnot2 : ¬ i - B < n - B := by omega
        simp [hnot1, hnot2]
      rw [h1, h2]

/-- Conditional decompressor generating $1^n$ given $n$. -/
def D_ones : Map := fun pr => Part.some (List.replicate (bitsToNat pr.2) true)

/-- The decompressor producing `1^n` from the condition `n` is partial computable. -/
theorem D_ones_partrec : Partrec D_ones := by
  have h : Computable (fun pr : BitString × BitString => List.replicate (bitsToNat pr.2) true) :=
    (Primrec.list_replicate.comp (bitsToNat_primrec.comp Primrec.snd) (Primrec.const true)).to_comp
  exact h.partrec

/-- The output of the conditional decompressor once the enumeration has stabilised at stage `t`:
the prefix of `1^B 000…` for the threshold `B = max (m + K) t`. -/
def D_cond_fn (K : ℕ) (p : (BitString × BitString) × ℕ) : BitString :=
  bif decide (bitsToNat p.1.2 ≤ max (bitsToNat p.1.1 + K) p.2) then
    List.replicate (bitsToNat p.1.2) true
  else
    List.replicate (max (bitsToNat p.1.1 + K) p.2) true ++
      List.replicate (bitsToNat p.1.2 - max (bitsToNat p.1.1 + K) p.2) false

/-- Conditional decompressor that waits for the enumeration of outputs of length-bounded
programs to stabilise and then emits the corresponding prefix of `1^B 000…`. -/
noncomputable def D_cond (c : Code) (K : ℕ) : Map := fun pr =>
  let m := bitsToNat pr.1
  let n := bitsToNat pr.2
  let k := m + K
  let S := boundedOutputStage c k n
  let L := S.length
  (Nat.rfind (fun t => Part.some ((boundedOutputStage c k t).length == L))).map (fun t =>
    D_cond_fn K (pr, t))

/-- The stabilised output of the conditional decompressor is computable in its arguments. -/
theorem D_cond_fn_computable (K : ℕ) : Computable (D_cond_fn K) := by
  have hm : Primrec (fun p : (BitString × BitString) × ℕ => bitsToNat p.1.1) :=
    bitsToNat_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec (fun p : (BitString × BitString) × ℕ => bitsToNat p.1.2) :=
    bitsToNat_primrec.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : (BitString × BitString) × ℕ => bitsToNat p.1.1 + K) :=
    Primrec.nat_add.comp hm (Primrec.const K)
  have hB : Primrec (fun p : (BitString × BitString) × ℕ => max (bitsToNat p.1.1 + K) p.2) :=
    Primrec.nat_max.comp hk Primrec.snd
  have hcond : Primrec (fun p : (BitString × BitString) × ℕ =>
      decide (bitsToNat p.1.2 ≤ max (bitsToNat p.1.1 + K) p.2)) :=
    PrimrecPred.decide (Primrec.nat_le.comp hn hB)
  have hthen : Primrec (fun p : (BitString × BitString) × ℕ =>
      List.replicate (bitsToNat p.1.2) true) :=
    Primrec.list_replicate.comp hn (Primrec.const true)
  have helse1 : Primrec (fun p : (BitString × BitString) × ℕ =>
      List.replicate (max (bitsToNat p.1.1 + K) p.2) true) :=
    Primrec.list_replicate.comp hB (Primrec.const true)
  have helse2 : Primrec (fun p : (BitString × BitString) × ℕ =>
      List.replicate (bitsToNat p.1.2 - max (bitsToNat p.1.1 + K) p.2) false) :=
    Primrec.list_replicate.comp (Primrec.nat_sub.comp hn hB) (Primrec.const false)
  have helse : Primrec (fun p : (BitString × BitString) × ℕ =>
      List.replicate (max (bitsToNat p.1.1 + K) p.2) true ++
        List.replicate (bitsToNat p.1.2 - max (bitsToNat p.1.1 + K) p.2) false) :=
    Primrec.list_append.comp helse1 helse2
  exact (Primrec.cond hcond hthen helse).to_comp

/-- The conditional decompressor is partial computable. -/
theorem D_cond_partrec (c : Code) (K : ℕ) : Partrec (D_cond c K) := by
  have hm : Primrec (fun pr : BitString × BitString => bitsToNat pr.1) :=
    bitsToNat_primrec.comp Primrec.fst
  have hn : Primrec (fun pr : BitString × BitString => bitsToNat pr.2) :=
    bitsToNat_primrec.comp Primrec.snd
  have hk : Primrec (fun pr : BitString × BitString => bitsToNat pr.1 + K) :=
    Primrec.nat_add.comp hm (Primrec.const K)
  have hS : Primrec (fun pr : BitString × BitString =>
      boundedOutputStage c (bitsToNat pr.1 + K) (bitsToNat pr.2)) :=
    (boundedOutputStage_primrec c).comp (Primrec.pair hk hn)
  have hL : Primrec (fun pr : BitString × BitString =>
      (boundedOutputStage c (bitsToNat pr.1 + K) (bitsToNat pr.2)).length) :=
    Primrec.list_length.comp hS
  have hstage_t : Primrec (fun st : (BitString × BitString) × ℕ =>
      boundedOutputStage c (bitsToNat st.1.1 + K) st.2) :=
    (boundedOutputStage_primrec c).comp (Primrec.pair (hk.comp Primrec.fst) Primrec.snd)
  have hcheck : Computable₂ (fun (pr : BitString × BitString) (t : ℕ) =>
      (boundedOutputStage c (bitsToNat pr.1 + K) t).length ==
        (boundedOutputStage c (bitsToNat pr.1 + K) (bitsToNat pr.2)).length) :=
    (Primrec.beq.comp (Primrec.list_length.comp hstage_t) (hL.comp Primrec.fst)).to_comp.to₂
  have hrfind : Partrec (fun pr : BitString × BitString =>
      Nat.rfind (fun t => Part.some ((boundedOutputStage c (bitsToNat pr.1 + K) t).length ==
        (boundedOutputStage c (bitsToNat pr.1 + K) (bitsToNat pr.2)).length))) :=
    Partrec.rfind hcheck.partrec₂
  exact (hrfind.map (D_cond_fn_computable K).to₂).of_eq (fun pr => rfl)

/-- Extraction function to recover $B$ from program description `p` computing prefixes
of $1^B 000…$. -/
def fExtractBody : BitString →. BitString := fun e_bits =>
  let e := bitsToNat e_bits
  (Nat.rfind (fun n =>
    ((Denumerable.ofNat Code e).eval (Encodable.encode n)).bind (fun w_enc =>
      Part.ofOption ((Encodable.decode (α := BitString) w_enc).map (fun w =>
        decide (false ∈ w)))))).bind (fun n =>
    ((Denumerable.ofNat Code e).eval (Encodable.encode n)).bind (fun w_enc =>
      Part.ofOption ((Encodable.decode (α := BitString) w_enc).map (fun w =>
        Nat.bits (w.takeWhile id).length))))

/-- Recovering `B` from a program computing the prefixes of `1^B 000…` is partial computable. -/
theorem f_extract_body_partrec : Partrec fExtractBody := by
  have he : Computable (fun e_bits : BitString => bitsToNat e_bits) := bitsToNat_computable
  have hcode : Computable (fun e_bits : BitString => Denumerable.ofNat Code (bitsToNat e_bits)) :=
    (Computable.ofNat Code).comp he
  have h1 : Partrec (fun p : BitString × ℕ =>
      (Denumerable.ofNat Code (bitsToNat p.1)).eval (Encodable.encode p.2)) :=
    Nat.Partrec.Code.eval_part.comp (hcode.comp Computable.fst)
      (Computable.encode.comp Computable.snd)
  have hp_check : Primrec₂ (fun (_ : (BitString × ℕ) × ℕ) (w : BitString) => decide (false ∈ w)) :=
    (@list_mem_decide_primrec Bool _ _).comp (Primrec.const false) Primrec.snd
  have hpred_inner : Partrec₂ (fun (_ : BitString × ℕ) (w_enc : ℕ) =>
      Part.ofOption ((Encodable.decode (α := BitString) w_enc).map (fun w =>
        decide (false ∈ w)))) :=
    (Primrec.option_map (Primrec.decode.comp Primrec.snd) hp_check).to_comp.ofOption.to₂
  have hpred : Partrec (fun p : BitString × ℕ =>
      ((Denumerable.ofNat Code (bitsToNat p.1)).eval (Encodable.encode p.2)).bind (fun w_enc =>
        Part.ofOption ((Encodable.decode (α := BitString) w_enc).map (fun w =>
          decide (false ∈ w))))) :=
    Partrec.bind h1 hpred_inner
  have hrfind : Partrec (fun e_bits : BitString => Nat.rfind (fun n =>
      ((Denumerable.ofNat Code (bitsToNat e_bits)).eval (Encodable.encode n)).bind (fun w_enc =>
        Part.ofOption ((Encodable.decode (α := BitString) w_enc).map (fun w =>
          decide (false ∈ w)))))) :=
    Partrec.rfind hpred.to₂
  have htake : Primrec (fun w : BitString => w.takeWhile id) :=
    Primrec.list_takeWhile Primrec.id
  have hlen : Primrec (fun w : BitString => (w.takeWhile id).length) :=
    Primrec.list_length.comp htake
  have hbits : Primrec (fun w : BitString => Nat.bits (w.takeWhile id).length) :=
    primrec_natBits.comp hlen
  have hp_after : Primrec₂ (fun (_ : (BitString × ℕ) × ℕ) (w : BitString) =>
      Nat.bits (w.takeWhile id).length) :=
    (hbits.comp Primrec.snd).to₂
  have hafter_inner : Partrec₂ (fun (_ : BitString × ℕ) (w_enc : ℕ) =>
      Part.ofOption ((Encodable.decode (α := BitString) w_enc).map (fun w =>
        Nat.bits (w.takeWhile id).length))) :=
    (Primrec.option_map (Primrec.decode.comp Primrec.snd) hp_after).to_comp.ofOption.to₂
  have hafter : Partrec₂ (fun (e_bits : BitString) (n : ℕ) =>
      ((Denumerable.ofNat Code (bitsToNat e_bits)).eval (Encodable.encode n)).bind (fun w_enc =>
        Part.ofOption ((Encodable.decode (α := BitString) w_enc).map (fun w =>
          Nat.bits (w.takeWhile id).length)))) :=
    (Partrec.bind h1 hafter_inner).to₂
  unfold fExtractBody
  exact (Partrec.bind hrfind hafter).of_eq (fun e_bits => rfl)

/-- The decompressor that runs `U` and then extracts `B` from the program it outputs. -/
def fExtract (U : Map) : Map := fun pr =>
  (U pr).bind fExtractBody

/-- The extraction decompressor is partial computable whenever `U` is. -/
theorem f_extract_partrec (U : Map) (hU : Partrec U) : Partrec (fExtract U) :=
  Partrec.bind hU (f_extract_body_partrec.comp Computable.snd).to₂

end Kolmogorov
