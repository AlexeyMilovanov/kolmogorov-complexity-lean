import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Prefix.PrefixStableComplexity

/-!
# Blocking-read machines

Machines that read their input by *blocking reads*: `BlockingComputes` describes the
synchronous model in which the machine explicitly asks for the next input bit.  Such a
machine computes exactly the computable prefix-free partial functions
(`blockingRead_iff_computable_prefixFree`).

SUV Theorem 48, p. 111.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-! ### Machines with self-delimiting input: the blocking-read model -/

/-- A partial function on strings is *prefix free* if no two distinct strings of
its domain are comparable. -/
def IsPrefixFreeFun (f : BitString →. BitString) : Prop :=
  ∀ x y : BitString, (f x).Dom → (f y).Dom → x <+: y → x = y

/-- A *blocking-read machine*: having scanned exactly the bits `r` of its one-way
input tape, the machine either halts with an output (`some y`), or reads the next
input bit (`none`), or diverges (`act r` undefined).  `BlockingComputes act f`
says that `f` is the function computed by `act` in the prefix-free mode. -/
def BlockingComputes (act : BitString →. Option BitString) (f : BitString →. BitString) :
    Prop :=
  ∀ x y : BitString,
    y ∈ f x ↔
      (some y ∈ act x ∧
        ∀ r : BitString, r <+: x → r ≠ x → (none : Option BitString) ∈ act r)

noncomputable section

/-- The stagewise search for the action of the code `c` on the bits read so far: either an output,
or the request to read one more bit. -/
def actSearchOut (c : Code) (r : BitString) (n : ℕ) : Option (Option BitString) :=
  (Encodable.decode n.unpair.1 : Option BitString).bind fun x =>
    cond (decide (x.take r.length = r))
      ((Code.evaln n.unpair.2 c (Encodable.encode x)).bind fun e =>
        (Encodable.decode e : Option BitString).bind fun y =>
          cond (decide (r = x)) (some (some y)) (some none))
      none

/-- The action of a code as a partial function of the bits read so far. -/
def actMap (c : Code) : BitString →. Option BitString := fun r =>
  (Nat.rfind (fun n => Part.some (actSearchOut c r n).isSome)).bind fun n =>
    Part.ofOption (actSearchOut c r n)

/-- Decoding a natural into a bitstring is computable. -/
theorem decode_bitstring_computable :
    Computable (fun n : ℕ => (Encodable.decode n : Option BitString)) :=
  Computable.decode

/-- Equality of bitstrings is decidable computably. -/
theorem bitstring_eq_decide_computable :
    Computable (fun p : BitString × BitString => decide (p.1 = p.2)) := by
  have h_eq_primrec : Primrec (fun q : BitString × BitString => decide (q.1 = q.2)) := by
    convert Primrec.eq.comp Primrec.fst Primrec.snd using 1
    exact Iff.symm primrecPred_iff_primrec_decide
  exact Primrec.to_comp h_eq_primrec

/-- The test "the string read so far is a prefix of the candidate" is computable. -/
theorem actSearch_cond_computable :
    Computable (fun p : (BitString × ℕ) × BitString => decide (p.2.take p.1.1.length = p.1.1)) := by
  have h_len : Computable (fun p : (BitString × ℕ) × BitString => p.1.1.length) :=
    Computable.list_length.comp (Computable.fst.comp Computable.fst)
  have h_take : Computable (fun p : (BitString × ℕ) × BitString => p.2.take p.1.1.length) :=
    primrec_list_take.to_comp.comp Computable.snd h_len
  have h_pair :
      Computable (fun p : (BitString × ℕ) × BitString => (p.2.take p.1.1.length, p.1.1)) :=
    h_take.pair (Computable.fst.comp Computable.fst)
  convert bitstring_eq_decide_computable.comp h_pair using 1

/-- The bounded evaluation used by the search is computable. -/
theorem actSearch_evaln_computable (c : Code) :
    Computable (fun p : (BitString × ℕ) × BitString =>
      Code.evaln p.1.2.unpair.2 c (Encodable.encode p.2)) := by
  have h_evaln := evaln_fixed_computable c
  convert h_evaln.comp (Computable.pair
    (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst)))
    (Computable.encode.comp Computable.snd)) using 1

/-- The output-selection step of the search is computable. -/
theorem actSearch_map_out_computable :
    Computable (fun p : (((BitString × ℕ) × BitString) × ℕ) × BitString =>
      cond (decide (p.1.1.1.1 = p.1.1.2)) (some (some p.2)) (some none)) := by
  have h_eq : Computable (fun p : (((BitString × ℕ) × BitString) × ℕ) × BitString =>
      decide (p.1.1.1.1 = p.1.1.2)) := by
    convert bitstring_eq_decide_computable.comp
      ((Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
        (Computable.snd.comp (Computable.fst.comp Computable.fst))) using 1
  exact Computable.cond h_eq
    (Computable.option_some.comp (Computable.option_some.comp Computable.snd))
    (Computable.const (some none))

/-- The decoding step of the search is computable. -/
theorem actSearch_map_computable :
    Computable (fun p : ((BitString × ℕ) × BitString) × ℕ =>
      (Encodable.decode p.2 : Option BitString).bind (fun y =>
        cond (decide (p.1.1.1 = p.1.2)) (some (some y)) (some none))) := by
  have h_dec : Computable (fun p : ((BitString × ℕ) × BitString) × ℕ =>
      (Encodable.decode p.2 : Option BitString)) :=
    decode_bitstring_computable.comp Computable.snd
  exact Computable.option_bind h_dec actSearch_map_out_computable

/-- The composition of evaluation and output selection is computable. -/
theorem actSearch_then_computable (c : Code) :
    Computable (fun p : (BitString × ℕ) × BitString =>
      (Code.evaln p.1.2.unpair.2 c (Encodable.encode p.2)).bind fun e =>
        (Encodable.decode e : Option BitString).bind fun y =>
          cond (decide (p.1.1 = p.2)) (some (some y)) (some none)) := by
  exact Computable.option_bind (actSearch_evaln_computable c) actSearch_map_computable

/-- The guarded search step is computable. -/
theorem actSearch_if_computable (c : Code) :
    Computable (fun p : (BitString × ℕ) × BitString =>
      cond (decide (p.2.take p.1.1.length = p.1.1))
        ((Code.evaln p.1.2.unpair.2 c (Encodable.encode p.2)).bind fun e =>
          (Encodable.decode e : Option BitString).bind fun y =>
            cond (decide (p.1.1 = p.2)) (some (some y)) (some none))
        none) := by
  exact Computable.cond actSearch_cond_computable (actSearch_then_computable c)
    (Computable.const none)

/-- The stagewise action search is computable. -/
theorem actSearchOut_computable (c : Code) :
    Computable (fun p : BitString × ℕ => actSearchOut c p.1 p.2) := by
  have h_dec1 :
      Computable (fun p : BitString × ℕ => (Encodable.decode p.2.unpair.1 : Option BitString)) :=
    decode_bitstring_computable.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  exact Computable.option_bind h_dec1 (actSearch_if_computable c)

/-- The action of a code is partial computable. -/
theorem actMap_partrec (c : Code) :
    Partrec (actMap c) := by
  have h_out := actSearchOut_computable c
  have h_check : Computable (fun p : BitString × ℕ => (actSearchOut c p.1 p.2).isSome) :=
    (Primrec.to_comp Primrec.option_isSome).comp h_out
  unfold actMap
  exact Partrec.bind (Partrec.rfind (Computable.to₂ h_check).partrec₂)
    (Computable.ofOption h_out).to₂

/-- The check turning a "read one more bit" answer into success and an output into failure. -/
def checkStepOut (o : Option BitString) : Option Unit :=
  cond (decide (o = none)) (some ()) none

/-- One step of the check that the machine has not produced an output before the `k`-th bit. -/
def checkStep (act : BitString →. Option BitString) (x : BitString) (k : ℕ) : Part Unit :=
  (act (x.take k)).bind fun o => Part.ofOption (checkStepOut o)

/-- The check run over the first `n` prefixes of the input. -/
def runCheck (act : BitString →. Option BitString) (x : BitString) (n : ℕ) : Part Unit :=
  Nat.rec (Part.some ()) (fun k IH => IH.bind fun _ => checkStep act x k) n

/-- The check run over every proper prefix of the input. -/
def checkAll (act : BitString →. Option BitString) (x : BitString) : Part Unit :=
  runCheck act x x.length

/-- The function computed by a blocking-read machine: run the check over all proper prefixes and
then take the output on the whole input. -/
def fFromAct (act : BitString →. Option BitString) (x : BitString) : Part BitString :=
  (checkAll act x).bind fun _ =>
    (act x).bind fun o => (Part.ofOption o).bind fun o' => Part.ofOption (some o')

/-- The one-step check is computable. -/
theorem checkStepOut_computable : Computable checkStepOut := by
  have h_eq_primrec : Primrec (fun o : Option BitString => decide (o = none)) := by
    convert Primrec.eq.comp Primrec.id (Primrec.const none) using 1
    exact Iff.symm primrecPred_iff_primrec_decide
  exact Computable.cond (Primrec.to_comp h_eq_primrec) (Computable.const (some ()))
    (Computable.const none)

/-- The one-step check of a partial computable action is partial computable in the input and the
step. -/
theorem checkStep_partrec {act : BitString →. Option BitString} (hact : Partrec act) :
    Partrec₂ (fun (x : BitString) (k : ℕ) => checkStep act x k) := by
  have h_take : Computable₂ (fun (x : BitString) (k : ℕ) => x.take k) :=
    primrec_list_take.to_comp
  have h_act_take : Partrec (fun p : BitString × ℕ => act (p.1.take p.2)) :=
    hact.comp h_take
  have h_out : Partrec (fun p : (BitString × ℕ) × Option BitString =>
      Part.ofOption (checkStepOut p.2)) :=
    Computable.ofOption (checkStepOut_computable.comp Computable.snd)
  exact (Partrec.bind h_act_take h_out.to₂).to₂

/-- The check over all proper prefixes is partial computable. -/
theorem checkAll_partrec {act : BitString →. Option BitString} (hact : Partrec act) :
    Partrec (checkAll act) := by
  have h_step := checkStep_partrec hact
  have h_step' : Partrec₂ (fun (x : BitString) (p : ℕ × Unit) => checkStep act x p.1) :=
    h_step.comp Computable.fst (Computable.fst.comp Computable.snd)
  have h_init : Partrec (fun _x : BitString => Part.some ()) :=
    Computable.ofOption (Computable.const (some ()))
  unfold checkAll runCheck
  exact Partrec.nat_rec Computable.list_length h_init h_step'

/-- The function computed by a partial computable action is partial computable. -/
theorem fFromAct_partrec {act : BitString →. Option BitString} (hact : Partrec act) :
    Partrec (fFromAct act) := by
  have h_checkAll := checkAll_partrec hact
  have h_bind1 : Partrec (fun p : BitString × Option BitString => Part.ofOption p.2) :=
    Computable.ofOption Computable.snd
  have h_bind2 : Partrec (fun p : (BitString × Option BitString) × BitString =>
      Part.ofOption (some p.2)) :=
    Computable.ofOption (Computable.option_some.comp Computable.snd)
  have h_inner : Partrec (fun p : BitString × Option BitString =>
      (Part.ofOption p.2).bind fun o' => Part.ofOption (some o')) :=
    Partrec.bind h_bind1 h_bind2.to₂
  have h_act_x : Partrec (fun x : BitString =>
      (act x).bind fun o => (Part.ofOption o).bind fun o' => Part.ofOption (some o')) :=
    Partrec.bind hact h_inner.to₂
  unfold fFromAct
  exact Partrec.bind h_checkAll (h_act_x.comp Computable.fst).to₂

/-- A proper prefix is strictly shorter. -/
theorem prefix_length_lt {r x : BitString} (hr : r <+: x) (hne : r ≠ x) :
    r.length < x.length := by
  obtain ⟨s, hs⟩ := hr
  subst hs
  cases s with
  | nil => simp at hne
  | cons hd tl =>
    rw [List.length_append]
    dsimp
    omega

/-- The check over the first `n` prefixes succeeds exactly when the action asks for another bit at
each of them. -/
theorem runCheck_iff (act : BitString →. Option BitString) (x : BitString) (n : ℕ) :
    () ∈ runCheck act x n ↔ ∀ k < n, (none : Option BitString) ∈ act (x.take k) := by
  induction n with
  | zero =>
    rw [runCheck]; simp
  | succ n ih =>
    rw [runCheck]
    dsimp [Nat.rec]
    simp only [Part.mem_bind_iff]
    constructor
    · rintro ⟨u, hu, hstep⟩
      unfold checkStep at hstep
      rw [Part.mem_bind_iff] at hstep
      obtain ⟨o, ho, hout⟩ := hstep
      rw [Part.mem_ofOption] at hout
      dsimp [checkStepOut] at hout
      cases ho_none : o with
      | none =>
        rw [ho_none] at ho
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
        · exact ih.mp hu k hlt
        · exact ho
      | some y =>
        rw [ho_none] at hout
        rw [Option.mem_def] at hout
        contradiction
    · intro h_all
      refine ⟨(), ih.mpr (fun k hk => h_all k (Nat.lt_succ_of_lt hk)), ?_⟩
      unfold checkStep
      rw [Part.mem_bind_iff]
      have h_last := h_all n (Nat.lt_succ_self n)
      refine ⟨none, h_last, ?_⟩
      rw [Part.mem_ofOption]
      dsimp [checkStepOut]
      rfl

/-- The check over all proper prefixes succeeds exactly when the action asks for another bit at
each of them. -/
theorem mem_checkAll_iff {act : BitString →. Option BitString} {x : BitString} :
    () ∈ checkAll act x ↔ ∀ k < x.length, (none : Option BitString) ∈ act (x.take k) :=
  runCheck_iff act x x.length

/-- An action that blocks until the whole input is read computes `y` on `x` exactly when it asks
for another bit at every proper prefix and outputs `y` on `x` itself. -/
theorem mem_fFromAct_iff {act : BitString →. Option BitString} {f : BitString →. BitString}
    (hact : BlockingComputes act f) {x y : BitString} :
    y ∈ fFromAct act x ↔ y ∈ f x := by
  rw [hact x y]
  unfold fFromAct
  rw [Part.mem_bind_iff]
  constructor
  · rintro ⟨u, hu, h_act⟩
    rw [mem_checkAll_iff] at hu
    rw [Part.mem_bind_iff] at h_act
    obtain ⟨o, ho, h_rest⟩ := h_act
    rw [Part.mem_bind_iff] at h_rest
    obtain ⟨o', ho', h_final⟩ := h_rest
    cases o with
    | none => rw [Part.mem_ofOption] at ho'; contradiction
    | some y' =>
      rw [Part.mem_ofOption] at ho'
      injection ho' with hy_eq
      subst hy_eq
      rw [Part.mem_ofOption] at h_final
      rw [Option.mem_def] at h_final
      injection h_final with hy_eq2
      subst hy_eq2
      refine ⟨ho, ?_⟩
      intro r hr hne
      have hr_take := (isPrefix_of_isPrefix_take hr).symm
      have hr_len := prefix_length_lt hr hne
      rw [hr_take]
      exact hu r.length hr_len
  · rintro ⟨h_act, h_pre⟩
    refine ⟨(), mem_checkAll_iff.mpr ?_, ?_⟩
    · intro k hk
      have h_take_pre : x.take k <+: x := List.take_prefix k x
      have h_take_ne : x.take k ≠ x := by
        intro h_eq
        have := congr_arg List.length h_eq
        rw [List.length_take, min_eq_left (by omega)] at this
        omega
      exact h_pre (x.take k) h_take_pre h_take_ne
    · rw [Part.mem_bind_iff]
      refine ⟨some y, h_act, ?_⟩
      rw [Part.mem_bind_iff]
      refine ⟨y, Part.mem_some y, Part.mem_some y⟩

/-- For a partial recursive `f` with prefix-free domain, the action map of a code for `f`
answers `f x` on `x` itself and blocks on every proper prefix of `x`. -/
private lemma actMap_mem_and_blocks {f : BitString →. BitString} (hpf : IsPrefixFreeFun f)
    {c : Code}
    (hc : c.eval = fun n => (Part.ofOption (Encodable.decode (α := BitString) n)).bind
      fun a => Part.map Encodable.encode (f a))
    {x y : BitString} (hy : y ∈ f x) :
    some y ∈ actMap c x ∧
      ∀ r : BitString, r <+: x → r ≠ x → (none : Option BitString) ∈ actMap c r := by
  have h1 : Encodable.encode y ∈ c.eval (Encodable.encode x) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨x, by simp [Encodable.encodek], Part.mem_map Encodable.encode hy⟩
  obtain ⟨t1, ht1⟩ := Nat.Partrec.Code.evaln_complete.mp h1
  have ht1_some : Code.evaln t1 c (Encodable.encode x) = some (Encodable.encode y) :=
    Option.mem_def.mp ht1
  let n1 := Nat.pair (Encodable.encode x) t1
  have h_act1 : actSearchOut c x n1 = some (some y) := by
    unfold actSearchOut
    dsimp [n1]
    rw [Nat.unpair_pair, Encodable.encodek]
    dsimp
    have h_take_self : (x : BitString).take (x : BitString).length = (x : BitString) :=
      List.take_length
    have h_dec_self :
        decide ((x : BitString).take (x : BitString).length = (x : BitString)) = true :=
      decide_eq_true h_take_self
    have h_dec_eq : decide ((x : BitString) = (x : BitString)) = true := decide_eq_true rfl
    rw [h_dec_self, cond_true, ht1_some]
    dsimp
    rw [Encodable.encodek]
    dsimp
    rw [h_dec_eq, cond_true]
  have h_isSome : (actSearchOut c x n1).isSome = true := by
    rw [h_act1]; rfl
  have h_rfind : (Nat.rfind (fun n => Part.some (actSearchOut c x n).isSome)).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨n1, by rw [Part.mem_some_iff, h_isSome], fun {m} _ => Part.some_dom _⟩
  obtain ⟨n_min, hn_min⟩ := Part.dom_iff_mem.mp h_rfind
  have h_min_isSome : (actSearchOut c x n_min).isSome = true := by
    have h := (Nat.mem_rfind.mp hn_min).1
    rw [Part.mem_some_iff] at h
    exact h.symm
  obtain ⟨o_min, ho_min⟩ := Option.isSome_iff_exists.mp h_min_isSome
  have h_search_out : actSearchOut c x n_min = some o_min := ho_min
  unfold actSearchOut at h_search_out
  rw [Option.bind_eq_some_iff] at h_search_out
  obtain ⟨x_min, hx_dec, h_rest_min⟩ := h_search_out
  cases h_cond1 : decide (x_min.take x.length = x)
  · rw [h_cond1] at h_rest_min
    contradiction
  · rw [h_cond1] at h_rest_min
    rw [cond_true] at h_rest_min
    rw [Option.bind_eq_some_iff] at h_rest_min
    obtain ⟨e_min, he_eval, h_rest_min2⟩ := h_rest_min
    rw [Option.bind_eq_some_iff] at h_rest_min2
    obtain ⟨y_min, hy_dec, h_rest_min3⟩ := h_rest_min2
    have h_eval_sound := Nat.Partrec.Code.evaln_sound he_eval
    rw [hc, Part.mem_bind_iff] at h_eval_sound
    obtain ⟨x_in, hx_in, hy_in⟩ := h_eval_sound
    rw [Part.mem_ofOption] at hx_in
    have hx_in_eq : x_in = x_min := Option.some.inj (hx_in.symm.trans (Encodable.encodek x_min))
    rw [Part.mem_map_iff] at hy_in
    obtain ⟨y_in, hy_in_f, hy_enc⟩ := hy_in
    have hy_dec_eq : (Encodable.decode (Encodable.encode y_in) : Option BitString) =
        Encodable.decode e_min := by rw [hy_enc]
    rw [Encodable.encodek y_in, hy_dec] at hy_dec_eq
    have hy_in_eq : y_in = y_min := Option.some.inj hy_dec_eq
    have hx_dom : (f x).Dom := Part.dom_iff_mem.mpr ⟨y, hy⟩
    have hxmin_dom : (f x_min).Dom :=
      Part.dom_iff_mem.mpr ⟨y_min, hx_in_eq ▸ hy_in_eq ▸ hy_in_f⟩
    have h_take_pre : x_min.take x.length = x := of_decide_eq_true h_cond1
    have hx_pre_xmin : x <+: x_min := by
      rw [← h_take_pre]
      exact List.take_prefix _ _
    have h_eq_xx : x = x_min := hpf x x_min hx_dom hxmin_dom hx_pre_xmin
    have hy_in_f' : y_min ∈ f x := h_eq_xx ▸ hx_in_eq ▸ hy_in_eq ▸ hy_in_f
    have hy_min_eq : y_min = y := Part.mem_unique hy_in_f' hy
    have h_dec_cond2 : decide (x = x_min) = true := decide_eq_true h_eq_xx
    rw [h_dec_cond2, cond_true] at h_rest_min3
    have ho_min_eq : o_min = some y_min := Option.some.inj h_rest_min3.symm
    have h_act_map_x : some y ∈ actMap c x := by
      unfold actMap
      rw [Part.mem_bind_iff]
      refine ⟨n_min, hn_min, ?_⟩
      rw [Part.mem_ofOption, ho_min, ho_min_eq, hy_min_eq]
      rfl
    refine ⟨h_act_map_x, ?_⟩
    intro r hr hne
    let n_r := Nat.pair (Encodable.encode x) t1
    have h_act_r : actSearchOut c r n_r = some none := by
      unfold actSearchOut
      dsimp [n_r]
      rw [Nat.unpair_pair, Encodable.encodek]
      dsimp
      have hr_take : x.take r.length = r := isPrefix_of_isPrefix_take hr
      have h_dec1 : decide (x.take r.length = r) = true := decide_eq_true hr_take
      have h_ne_rx : r ≠ x := hne
      have h_dec2 : decide (r = x) = false := decide_eq_false h_ne_rx
      rw [h_dec1, cond_true, ht1_some]
      dsimp
      rw [Encodable.encodek]
      dsimp
      rw [h_dec2, cond_false]
    have h_isSome_r : (actSearchOut c r n_r).isSome = true := by
      rw [h_act_r]; rfl
    have h_rfind_r : (Nat.rfind (fun n => Part.some (actSearchOut c r n).isSome)).Dom := by
      rw [Nat.rfind_dom]
      exact ⟨n_r, by rw [Part.mem_some_iff, h_isSome_r], fun {m} _ => Part.some_dom _⟩
    obtain ⟨n_rmin, hn_rmin⟩ := Part.dom_iff_mem.mp h_rfind_r
    have h_rmin_isSome : (actSearchOut c r n_rmin).isSome = true := by
      have h := (Nat.mem_rfind.mp hn_rmin).1
      rw [Part.mem_some_iff] at h
      exact h.symm
    obtain ⟨o_rmin, ho_rmin⟩ := Option.isSome_iff_exists.mp h_rmin_isSome
    have h_search_r : actSearchOut c r n_rmin = some o_rmin := ho_rmin
    unfold actSearchOut at h_search_r
    rw [Option.bind_eq_some_iff] at h_search_r
    obtain ⟨x_rmin, hx_rdec, h_rrest⟩ := h_search_r
    cases h_rcond1 : decide (x_rmin.take r.length = r)
    · rw [h_rcond1] at h_rrest
      contradiction
    · rw [h_rcond1] at h_rrest
      rw [cond_true] at h_rrest
      rw [Option.bind_eq_some_iff] at h_rrest
      obtain ⟨e_rmin, he_reval, h_rrest2⟩ := h_rrest
      rw [Option.bind_eq_some_iff] at h_rrest2
      obtain ⟨y_rmin, hy_rdec, h_rrest3⟩ := h_rrest2
      cases h_rcond2 : decide (r = x_rmin)
      · rw [h_rcond2] at h_rrest3
        rw [cond_false] at h_rrest3
        injection h_rrest3 with ho_rmin_eq
        subst ho_rmin_eq
        unfold actMap
        rw [Part.mem_bind_iff]
        refine ⟨n_rmin, hn_rmin, ?_⟩
        rw [Part.mem_ofOption, ho_rmin]
        rfl
      · rw [h_rcond2] at h_rrest3
        have he_sound := Nat.Partrec.Code.evaln_sound he_reval
        rw [hc, Part.mem_bind_iff] at he_sound
        obtain ⟨x_in', hx_in', hy_in'⟩ := he_sound
        rw [Part.mem_ofOption] at hx_in'
        have hx_eq' : x_rmin = x_in' :=
          (Option.some.inj (hx_in'.symm.trans (Encodable.encodek x_rmin))).symm
        rw [Part.mem_map_iff] at hy_in'
        obtain ⟨y_in', hy_in_f', hy_enc'⟩ := hy_in'
        have hr_eq_xmin : r = x_rmin := of_decide_eq_true h_rcond2
        have hr_dom : (f r).Dom :=
          Part.dom_iff_mem.mpr ⟨y_in', hr_eq_xmin.symm ▸ hx_eq' ▸ hy_in_f'⟩
        have hx_dom' : (f x).Dom := Part.dom_iff_mem.mpr ⟨y, hy⟩
        have h_eq_rx : r = x := hpf r x hr_dom hx_dom' hr
        exact False.elim (hne h_eq_rx)

/-- If `f` is partial recursive and its domain is prefix free, then the action map read
off a code for `f` is partial recursive and computes `f` in the blocking-read sense:
it returns `f x` on `x` and blocks on every proper prefix of `x`. -/
private lemma blockingComputes_of_partrec_of_prefixFree {f : BitString →. BitString}
    (hf : Partrec f) (hpf : IsPrefixFreeFun f) :
    ∃ act : BitString →. Option BitString, Partrec act ∧ BlockingComputes act f := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨actMap c, actMap_partrec c, ?_⟩
  intro x y
  constructor
  · intro hy
    exact actMap_mem_and_blocks hpf hc hy
  · intro h_blocking
    have h_act_x : some y ∈ actMap c x := h_blocking.1
    unfold actMap at h_act_x
    rw [Part.mem_bind_iff] at h_act_x
    obtain ⟨n_min, hn_min, ho_min⟩ := h_act_x
    rw [Part.mem_ofOption] at ho_min
    have h_search_out : actSearchOut c x n_min = some (some y) := ho_min
    unfold actSearchOut at h_search_out
    rw [Option.bind_eq_some_iff] at h_search_out
    obtain ⟨x_min, hx_dec, h_rest_min⟩ := h_search_out
    cases h_cond1 : decide (x_min.take x.length = x)
    · rw [h_cond1] at h_rest_min
      contradiction
    · rw [h_cond1] at h_rest_min
      rw [cond_true] at h_rest_min
      rw [Option.bind_eq_some_iff] at h_rest_min
      obtain ⟨e_min, he_eval, h_rest_min2⟩ := h_rest_min
      rw [Option.bind_eq_some_iff] at h_rest_min2
      obtain ⟨y_min, hy_dec, h_rest_min3⟩ := h_rest_min2
      have h_eval_sound := Nat.Partrec.Code.evaln_sound he_eval
      rw [hc, Part.mem_bind_iff] at h_eval_sound
      obtain ⟨x_in, hx_in, hy_in⟩ := h_eval_sound
      rw [Part.mem_ofOption] at hx_in
      have hx_eq : x_min = x_in :=
        (Option.some.inj (hx_in.symm.trans (Encodable.encodek x_min))).symm
      rw [Part.mem_map_iff] at hy_in
      obtain ⟨y_in, hy_in_f, hy_enc⟩ := hy_in
      have hy_dec_eq : (Encodable.decode (Encodable.encode y_in) : Option BitString) =
          Encodable.decode e_min := by rw [hy_enc]
      rw [Encodable.encodek y_in, hy_dec] at hy_dec_eq
      have hy_eq : y_min = y_in := (Option.some.inj hy_dec_eq).symm
      cases h_cond2 : decide (x = x_min)
      · rw [h_cond2] at h_rest_min3
        rw [cond_false] at h_rest_min3
        cases h_rest_min3
      · rw [h_cond2] at h_rest_min3
        rw [cond_true] at h_rest_min3
        injection h_rest_min3 with hy_eq'
        have h_x_eq : x = x_min := of_decide_eq_true h_cond2
        injection hy_eq' with hy_min_y
        subst hy_min_y
        subst hy_eq
        subst hx_eq
        subst h_x_eq
        exact hy_in_f

/-- **Theorem 50.** The functions computed in the prefix-free (blocking-read)
mode are exactly the computable prefix-free functions. -/
theorem blockingRead_iff_computable_prefixFree (f : BitString →. BitString) :
    (Partrec f ∧ IsPrefixFreeFun f) ↔
      ∃ act : BitString →. Option BitString, Partrec act ∧ BlockingComputes act f := by
  constructor
  · rintro ⟨hf, hpf⟩
    exact blockingComputes_of_partrec_of_prefixFree hf hpf
  · rintro ⟨act, hact, hcomp⟩
    have h_eq : f = fFromAct act := by
      ext x y
      exact (mem_fFromAct_iff hcomp).symm
    refine ⟨h_eq.symm ▸ fFromAct_partrec hact, ?_⟩
    intro x y hx hy hpre
    obtain ⟨vx, hvx⟩ := Part.dom_iff_mem.mp hx
    obtain ⟨vy, hvy⟩ := Part.dom_iff_mem.mp hy
    rw [hcomp x vx] at hvx
    rw [hcomp y vy] at hvy
    by_contra hne
    have h_none := hvy.2 x hpre hne
    have h_some := hvx.1
    have h_eq_act := Part.mem_unique h_some h_none
    contradiction

end


end Kolmogorov
