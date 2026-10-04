/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
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
import KolmogorovMathlib.Prefix.BlockingReadMachines

/-!
# Machines with self-delimiting input

The asynchronous (robust) model of a machine reading a self-delimiting input: the program
actions, the step relation, and the proof that the partial functions computed in this model
are exactly the computable prefix-stable ones.

SUV Theorem 48, p. 111.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-! ### Machines with self-delimiting input: the asynchronous (robust) model -/

/-- One action of an asynchronous program: halt with an output, continue
computing in a new state, or take the oldest queued input bit (crashing if the
queue is empty) and branch on its value. -/
inductive NBAction where
  /-- Halt and output `y`. -/
  | halt (y : BitString) : NBAction
  /-- Continue in state `q` without touching the input queue. -/
  | cont (q : ℕ) : NBAction
  /-- Read the next queued bit and continue in state `q0` or `q1`. -/
  | read (q0 q1 : ℕ) : NBAction

/-- The sum encoding of `NBAction`, used to give it a `Primcodable` structure. -/
def NBAction.equivSum : NBAction ≃ (BitString ⊕ ℕ ⊕ (ℕ × ℕ)) where
  toFun
    | .halt y => Sum.inl y
    | .cont q => Sum.inr (Sum.inl q)
    | .read q0 q1 => Sum.inr (Sum.inr (q0, q1))
  invFun
    | Sum.inl y => .halt y
    | Sum.inr (Sum.inl q) => .cont q
    | Sum.inr (Sum.inr (q0, q1)) => .read q0 q1
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | ⟨_, _⟩) <;> rfl

instance : Primcodable NBAction := Primcodable.ofEquiv _ NBAction.equivSum

/-- The action taken by the program with code `c` in state `q`, where `avail`
tells whether the input queue is non-empty (the answer to `NextExists`).  If the
code diverges, the program hangs. -/
noncomputable def nbAct (c : Code) (q : ℕ) (avail : Bool) : Part NBAction :=
  (c.eval (Encodable.encode (q, avail))).bind fun n => Part.ofOption (Encodable.decode n)

/-- A *bit-arrival schedule* for an input of length `n`: `arr t` is the number of
input bits that have arrived by time `t`; all `n` bits eventually arrive. -/
def IsArrivalSchedule (arr : ℕ → ℕ) (n : ℕ) : Prop :=
  Monotone arr ∧ (∀ t, arr t ≤ n) ∧ ∃ t, arr t = n

/-- One step of an asynchronous run; a configuration `cfg` records the state and
the number of input bits already consumed. -/
def NBStep (c : Code) (x : BitString) (arr : ℕ → ℕ) (t : ℕ) (cfg cfg' : ℕ × ℕ) : Prop :=
  ∃ a ∈ nbAct c cfg.1 (decide (cfg.2 < arr t)),
    match a with
    | NBAction.halt _ => False
    | NBAction.cont q => cfg' = (q, cfg.2)
    | NBAction.read q0 q1 =>
        cfg.2 < arr t ∧ ∃ b, x[cfg.2]? = some b ∧ cfg' = ((if b then q1 else q0), cfg.2 + 1)

/-- The program `c` outputs `y` on input `x` delivered according to the schedule
`arr`. -/
def NBOutputs (c : Code) (x : BitString) (arr : ℕ → ℕ) (y : BitString) : Prop :=
  ∃ (T : ℕ) (cfg : ℕ → ℕ × ℕ), cfg 0 = (0, 0) ∧
    (∀ t < T, NBStep c x arr t (cfg t) (cfg (t + 1))) ∧
    NBAction.halt y ∈ nbAct c (cfg T).1 (decide ((cfg T).2 < arr T))

/-- A program is *robust* if its output depends on the input string only, and not
on the timing of the arrival of the input bits. -/
def IsRobustProgram (c : Code) : Prop :=
  ∀ x : BitString,
    (∀ arr, IsArrivalSchedule arr x.length → ∀ y, ¬ NBOutputs c x arr y) ∨
      ∃ y, ∀ arr, IsArrivalSchedule arr x.length → NBOutputs c x arr y

/-- The partial function computed by an asynchronous program. -/
def NBComputes (c : Code) (f : BitString →. BitString) : Prop :=
  ∀ x y : BitString,
    y ∈ f x ↔ ∀ arr, IsArrivalSchedule arr x.length → NBOutputs c x arr y

-- `theorem51_robust_prefixStable` (ch04-theorem-51) is archived; see `docs/ARCHIVED_TARGETS.md`.

-- `theorem51_prefixStable_robust` (ch04-theorem-51) is archived; see `docs/ARCHIVED_TARGETS.md`.

-- `exercise96_robustification` (ch04-exercise-96) is archived; see `docs/ARCHIVED_TARGETS.md`.

/-- The action of a code depends only on the partial function that code evaluates to. -/
lemma nbAct_eq_of_eval_eq {c1 c2 : Code} (h : Code.eval c1 = Code.eval c2) (q : ℕ) (avail : Bool) :
    nbAct c1 q avail = nbAct c2 q avail := by
  dsimp [nbAct]
  rw [h]

/-- The step relation depends only on the partial function the code evaluates to. -/
lemma NBStep_eq_of_eval_eq {c1 c2 : Code} (h : Code.eval c1 = Code.eval c2)
    (x : BitString) (arr : ℕ → ℕ) (t : ℕ) (cfg cfg' : ℕ × ℕ) :
    NBStep c1 x arr t cfg cfg' ↔ NBStep c2 x arr t cfg cfg' := by
  dsimp [NBStep]
  rw [nbAct_eq_of_eval_eq h]

/-- The output relation depends only on the partial function the code evaluates to. -/
lemma NBOutputs_eq_of_eval_eq {c1 c2 : Code} (h : Code.eval c1 = Code.eval c2)
    (x : BitString) (arr : ℕ → ℕ) (y : BitString) :
    NBOutputs c1 x arr y ↔ NBOutputs c2 x arr y := by
  dsimp [NBOutputs]
  simp_rw [nbAct_eq_of_eval_eq h, NBStep_eq_of_eval_eq h]

/-- Robustness depends only on the partial function the code evaluates to. -/
lemma IsRobustProgram_eq_of_eval_eq (cf cg : Code) (h : Code.eval cf = Code.eval cg) :
    cf ∈ {c | IsRobustProgram c} ↔ cg ∈ {c | IsRobustProgram c} := by
  change IsRobustProgram cf ↔ IsRobustProgram cg
  dsimp [IsRobustProgram]
  simp_rw [NBOutputs_eq_of_eval_eq h]

/-- There is a robust program. -/
lemma exists_robust_program : ∃ c : Code, IsRobustProgram c := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp Nat.Partrec.none
  use c
  intro x
  left
  intro arr _ y hout
  rcases hout with ⟨T, cfg, _, _, hhalt⟩
  dsimp [nbAct] at hhalt
  rw [hc] at hhalt
  rw [Part.bind_none] at hhalt
  exact Part.notMem_none _ hhalt

/-- There is a program that is not robust, so robustness is a nontrivial restriction. -/
lemma exists_non_robust_program : ∃ c : Code, ¬ IsRobustProgram c := by
  let n1 := Encodable.encode ((0 : ℕ), true)
  let n2 := Encodable.encode ((0 : ℕ), false)
  let v1 := Encodable.encode (NBAction.halt ([] : BitString))
  let v2 := Encodable.encode (NBAction.halt ([true] : BitString))
  let f2 : ℕ → ℕ := fun n => if n = n1 then v1 else v2
  have hf2_1 : f2 n1 = v1 := by
    change (if n1 = n1 then v1 else v2) = v1
    rw [ite_eq_left rfl]
  have hn12 : n1 ≠ n2 := by
    intro h
    have h' := Encodable.encode_inj.mp h
    cases h'
  have hf2_2 : f2 n2 = v2 := by
    change (if n2 = n1 then v1 else v2) = v2
    rw [ite_eq_right hn12.symm]
  have hf2_prim : Primrec f2 := by
    have hc : PrimrecPred (fun n => n = n1) :=
      Primrec.eq.comp Primrec.id (Primrec.const n1)
    exact Primrec.ite hc (Primrec.const v1) (Primrec.const v2)
  have hf2_partrec : Partrec (fun n => Part.some (f2 n)) := Partrec.some.comp hf2_prim.to_comp
  obtain ⟨c2, hc2⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf2_partrec)
  use c2
  intro hrob
  have hnb_true : nbAct c2 0 true = Part.some (NBAction.halt []) := by
    dsimp [nbAct]
    rw [hc2]
    change (Part.some (f2 n1)).bind (fun n => Part.ofOption (Encodable.decode n)) =
      Part.some (NBAction.halt [])
    rw [hf2_1, Part.bind_some]
    dsimp [v1]
    rw [Encodable.encodek]
    rfl
  have hnb_false : nbAct c2 0 false = Part.some (NBAction.halt [true]) := by
    dsimp [nbAct]
    rw [hc2]
    change (Part.some (f2 n2)).bind (fun n => Part.ofOption (Encodable.decode n)) =
      Part.some (NBAction.halt [true])
    rw [hf2_2, Part.bind_some]
    dsimp [v2]
    rw [Encodable.encodek]
    rfl
  let arr1 : ℕ → ℕ := fun _ => 1
  have harr1 : IsArrivalSchedule arr1 1 := ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, ⟨0, rfl⟩⟩
  let arr2 : ℕ → ℕ := fun t => if t = 0 then 0 else 1
  have harr2 : IsArrivalSchedule arr2 1 := by
    refine ⟨?_, ?_, ⟨1, rfl⟩⟩
    · intro a b hab
      dsimp [arr2]
      split_ifs <;> omega
    · intro t
      dsimp [arr2]
      split_ifs <;> omega
  have hout1 : NBOutputs c2 [false] arr1 [] := by
    refine ⟨0, fun _ => (0, 0), rfl, ?_, ?_⟩
    · intro t ht
      omega
    · change NBAction.halt [] ∈ nbAct c2 0 true
      rw [hnb_true]
      exact Part.mem_some _
  rcases hrob [false] with hdisj1 | ⟨y, hy⟩
  · exact hdisj1 arr1 harr1 [] hout1
  · have hy1 := hy arr1 harr1
    have hy2 := hy arr2 harr2
    by_cases hy_eq : y = []
    · subst hy_eq
      rcases hy2 with ⟨T, cfg, hcfg0, hstep, hhalt⟩
      cases T with
      | zero =>
        rw [hcfg0] at hhalt
        have hdec : decide ((0 : ℕ) < arr2 0) = false := rfl
        rw [hdec] at hhalt
        rw [hnb_false, Part.mem_some_iff] at hhalt
        cases hhalt
      | succ T' =>
        have hs := hstep 0 (Nat.succ_pos T')
        dsimp [NBStep] at hs
        rw [hcfg0] at hs
        have hdec : decide ((0 : ℕ) < arr2 0) = false := rfl
        rw [hdec] at hs
        rw [hnb_false] at hs
        rcases hs with ⟨a, ha, hmatch⟩
        have ha_eq : a = NBAction.halt [true] := Part.mem_unique ha (Part.mem_some _)
        subst ha_eq
        exact hmatch
    · rcases hy1 with ⟨T, cfg, hcfg0, hstep, hhalt⟩
      cases T with
      | zero =>
        rw [hcfg0] at hhalt
        have hdec : decide ((0 : ℕ) < arr1 0) = true := rfl
        rw [hdec] at hhalt
        rw [hnb_true] at hhalt
        have h_eq : NBAction.halt y = NBAction.halt [] :=
          Part.mem_unique hhalt (Part.mem_some _)
        injection h_eq with h_eq'
        exact hy_eq h_eq'
      | succ T' =>
        have hs := hstep 0 (Nat.succ_pos T')
        dsimp [NBStep] at hs
        rw [hcfg0] at hs
        have hdec : decide ((0 : ℕ) < arr1 0) = true := rfl
        rw [hdec] at hs
        rw [hnb_true] at hs
        rcases hs with ⟨a, ha, hmatch⟩
        have ha_eq : a = NBAction.halt [] := Part.mem_unique ha (Part.mem_some _)
        subst ha_eq
        exact hmatch

/-- **Exercise 97.** Robustness of asynchronous programs is undecidable. -/
theorem robustness_undecidable :
    ¬ ∃ d : Code → Bool, Computable d ∧ ∀ c, d c = true ↔ IsRobustProgram c := by
  intro h
  rcases h with ⟨d, hd_comp, hd_spec⟩
  have hpred : ComputablePred (fun c => c ∈ {c | IsRobustProgram c}) := by
    rw [ComputablePred.computable_iff]
    use d, hd_comp
    ext c
    exact (hd_spec c).symm
  have hrice := ComputablePred.rice₂ {c : Code | IsRobustProgram c} IsRobustProgram_eq_of_eval_eq
  rw [hrice] at hpred
  rcases hpred with h1 | h2
  · obtain ⟨c1, hc1⟩ := exists_robust_program
    have : c1 ∈ {c : Code | IsRobustProgram c} := hc1
    rw [h1] at this
    exact this
  · obtain ⟨c2, hc2⟩ := exists_non_robust_program
    have : c2 ∉ {c : Code | IsRobustProgram c} := hc2
    rw [h2] at this
    exact this trivial

/-! ### The prefix topology on finite and infinite sequences -/

/-- The space `Σ ∪ Ω` of all finite and infinite binary sequences. -/
abbrev SeqE := BitString ⊕ (ℕ → Bool)

/-- The length-`n` prefix of an infinite binary sequence. -/
def streamTake (w : ℕ → Bool) (n : ℕ) : BitString := (List.range n).map w

/-- `EExtends x z` says that the finite string `x` is a prefix of the finite or
infinite sequence `z`. -/
def EExtends (x : BitString) : SeqE → Prop
  | Sum.inl y => x <+: y
  | Sum.inr w => streamTake w x.length = x

/-- The base sequenceCylinder `Σ_x` of all finite and infinite extensions of `x`. -/
def sequenceCylinder (x : BitString) : Set SeqE := {z | EExtends x z}

/-- The prefix topology on `Σ ∪ Ω`, generated by the cylinders. -/
@[instance_reducible]
def eTopology : TopologicalSpace SeqE := TopologicalSpace.generateFrom (Set.range sequenceCylinder)

/-- The prefix of length `n` of an infinite sequence has length `n`. -/
lemma streamTake_length (w : ℕ → Bool) (n : ℕ) : (streamTake w n).length = n := by
  simp [streamTake]

/-- A finite string extends itself. -/
lemma EExtends_refl (x : BitString) : EExtends x (Sum.inl x) :=
  List.prefix_refl x

/-- An infinite sequence extends each of its finite prefixes. -/
lemma EExtends_streamTake (w : ℕ → Bool) (n : ℕ) : EExtends (streamTake w n) (Sum.inr w) := by
  dsimp [EExtends]
  rw [streamTake_length]

/-- A shorter prefix of an infinite sequence is a prefix of a longer one. -/
lemma streamTake_prefix_of_streamTake {w : ℕ → Bool} {n m : ℕ} (h : n ≤ m) :
    streamTake w n <+: streamTake w m := by
  dsimp [streamTake]
  have h1 : List.take n (List.range m) = List.range n :=
    List.take_range.trans (by rw [min_eq_left h])
  rw [← h1, List.map_take]
  exact List.take_prefix n _

/-- Extension composes with the prefix order on finite strings. -/
lemma EExtends_trans {x y : BitString} {z : SeqE} (h1 : x <+: y) (h2 : EExtends y z) :
    EExtends x z := by
  cases z with
  | inl y' =>
    dsimp [EExtends] at h2 ⊢
    exact h1.trans h2
  | inr w =>
    dsimp [EExtends] at h2 ⊢
    rcases h1 with ⟨k, rfl⟩
    rw [List.length_append] at h2
    have hsub : streamTake w x.length <+: streamTake w (x.length + k.length) :=
      streamTake_prefix_of_streamTake (Nat.le_add_right _ _)
    rw [h2] at hsub
    rcases hsub with ⟨t, ht⟩
    have ht2 : List.take x.length (streamTake w x.length ++ t) =
        List.take x.length (x ++ k) := by rw [ht]
    rw [List.take_left] at ht2
    have htl : List.take x.length (streamTake w x.length ++ t) = streamTake w x.length := by
      have hlen : x.length = (streamTake w x.length).length :=
        (streamTake_length w x.length).symm
      nth_rw 1 [hlen]
      exact List.take_left
    rw [htl] at ht2
    exact ht2

/-- A finite string belongs to its own cylinder. -/
lemma cylinder_mem (x : BitString) : Sum.inl x ∈ sequenceCylinder x :=
  EExtends_refl x

/-- A union of generated-open sets is generated open. -/
lemma isOpen_iUnion_of_isOpen {ι : Type*} {g : Set (Set SeqE)} {f : ι → Set SeqE}
    (h : ∀ i, TopologicalSpace.GenerateOpen g (f i)) :
    TopologicalSpace.GenerateOpen g (⋃ i, f i) := by
  rw [← Set.sUnion_range]
  refine TopologicalSpace.GenerateOpen.sUnion _ ?_
  rintro s ⟨i, rfl⟩
  exact h i

/-- **Theorem 52.** Characterization of the open subsets of the prefix
topology. -/
theorem prefixTopology_isOpen_iff (A : Set SeqE) :
    @IsOpen SeqE eTopology A ↔
      (∀ (x : BitString) (z : SeqE), Sum.inl x ∈ A → EExtends x z → z ∈ A) ∧
      (∀ w : ℕ → Bool, Sum.inr w ∈ A → ∃ n, Sum.inl (streamTake w n) ∈ A) := by
  constructor
  · intro hA
    change TopologicalSpace.GenerateOpen (Set.range sequenceCylinder) A at hA
    induction hA with
    | basic s hs =>
      rcases hs with ⟨x, rfl⟩
      refine ⟨?_, ?_⟩
      · intro x' z hx' hx'z
        dsimp [sequenceCylinder] at hx' ⊢
        exact EExtends_trans hx' hx'z
      · intro w hw
        dsimp [sequenceCylinder] at hw
        refine ⟨x.length, ?_⟩
        dsimp [sequenceCylinder]
        rw [hw]
        exact EExtends_refl x
    | univ =>
      refine ⟨fun _ _ _ _ => Set.mem_univ _, fun w _ => ⟨0, Set.mem_univ _⟩⟩
    | inter s t hs ht ihs iht =>
      refine ⟨?_, ?_⟩
      · intro x z hx hxz
        exact ⟨ihs.1 x z hx.1 hxz, iht.1 x z hx.2 hxz⟩
      · intro w hw
        rcases ihs.2 w hw.1 with ⟨n1, hn1⟩
        rcases iht.2 w hw.2 with ⟨n2, hn2⟩
        refine ⟨max n1 n2, ?_⟩
        have h1 : streamTake w n1 <+: streamTake w (max n1 n2) :=
          streamTake_prefix_of_streamTake (le_max_left n1 n2)
        have h2 : streamTake w n2 <+: streamTake w (max n1 n2) :=
          streamTake_prefix_of_streamTake (le_max_right n1 n2)
        exact ⟨ihs.1 (streamTake w n1) (Sum.inl (streamTake w (max n1 n2))) hn1 h1,
               iht.1 (streamTake w n2) (Sum.inl (streamTake w (max n1 n2))) hn2 h2⟩
    | sUnion S hS ih =>
      refine ⟨?_, ?_⟩
      · intro x z hx hxz
        rcases hx with ⟨s, hsS, hxs⟩
        exact ⟨s, hsS, (ih s hsS).1 x z hxs hxz⟩
      · intro w hw
        rcases hw with ⟨s, hsS, hws⟩
        rcases (ih s hsS).2 w hws with ⟨n, hn⟩
        exact ⟨n, ⟨s, hsS, hn⟩⟩
  · rintro ⟨h_ext, h_stream⟩
    have h_eq : A = ⋃ (x : BitString), ⋃ (_ : Sum.inl x ∈ A), sequenceCylinder x := by
      ext z
      simp only [Set.mem_iUnion]
      constructor
      · intro hz
        cases z with
        | inl x =>
          refine ⟨x, hz, cylinder_mem x⟩
        | inr w =>
          rcases h_stream w hz with ⟨n, hn⟩
          refine ⟨streamTake w n, hn, EExtends_streamTake w n⟩
      · rintro ⟨x, hxA, hz_cyl⟩
        exact h_ext x z hxA hz_cyl
    rw [h_eq]
    refine isOpen_iUnion_of_isOpen (fun x => ?_)
    by_cases hx : Sum.inl x ∈ A
    · have h_eq2 : (⋃ (_ : Sum.inl x ∈ A), sequenceCylinder x) = sequenceCylinder x := by
        ext z
        simp [hx]
      rw [h_eq2]
      exact TopologicalSpace.GenerateOpen.basic (sequenceCylinder x) ⟨x, rfl⟩
    · have h_eq2 : (⋃ (_ : Sum.inl x ∈ A), sequenceCylinder x) = ∅ := by
        ext z
        simp [hx]
      rw [h_eq2]
      have h_univ : (∅ : Set SeqE) = ⋃₀ (∅ : Set (Set SeqE)) := by simp
      rw [h_univ]
      exact TopologicalSpace.GenerateOpen.sUnion ∅ (by simp)

/-- The topology on `ℕ⊥ = ℕ ∪ {⊥}`: a set is open if it avoids `⊥` or is
everything. -/
@[instance_reducible]
def natBotTopology : TopologicalSpace (Option ℕ) where
  IsOpen s := (none ∉ s) ∨ s = Set.univ
  isOpen_univ := Or.inr rfl
  isOpen_inter := by
    rintro s t (hs | rfl) (ht | rfl)
    · exact Or.inl fun h => hs h.1
    · exact Or.inl fun h => hs h.1
    · exact Or.inl fun h => ht h.2
    · exact Or.inr (Set.univ_inter _)
  isOpen_sUnion := by
    intro S hS
    by_cases h : ∃ t ∈ S, t = Set.univ
    · obtain ⟨t, htS, rfl⟩ := h
      exact Or.inr (Set.eq_univ_of_univ_subset (Set.subset_sUnion_of_mem htS))
    · refine Or.inl ?_
      simp only [Set.mem_sUnion, not_exists, not_and]
      intro t htS hnt
      rcases hS t htS with h' | h'
      · exact h' hnt
      · exact h ⟨t, htS, h'⟩

/-- The order on `ℕ⊥`: `⊥` is below everything, and distinct numbers are
incomparable. -/
def natBotLe (a b : Option ℕ) : Prop := a = none ∨ a = b

/-- The cylinders form a basis of the topology on finite and infinite sequences. -/
theorem eTopology_isBasis :
    @TopologicalSpace.IsTopologicalBasis SeqE eTopology (Set.range sequenceCylinder) := by
  let : TopologicalSpace SeqE := eTopology
  refine TopologicalSpace.IsTopologicalBasis.mk ?_ ?_ rfl
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ z ⟨hx, hy⟩
    rcases z with z0 | w
    · change x <+: z0 at hx
      change y <+: z0 at hy
      rcases List.prefix_or_prefix_of_prefix hx hy with hxy | hyx
      · use sequenceCylinder y
        refine ⟨⟨y, rfl⟩, hy, ?_⟩
        rintro z' hz'
        exact ⟨EExtends_trans hxy hz', hz'⟩
      · use sequenceCylinder x
        refine ⟨⟨x, rfl⟩, hx, ?_⟩
        rintro z' hz'
        exact ⟨hz', EExtends_trans hyx hz'⟩
    · change streamTake w x.length = x at hx
      change streamTake w y.length = y at hy
      let m := max x.length y.length
      let u := streamTake w m
      use sequenceCylinder u
      have hxm : x.length ≤ m := le_max_left _ _
      have hym : y.length ≤ m := le_max_right _ _
      have hxu : x <+: u := by
        rw [← hx]
        exact streamTake_prefix_of_streamTake hxm
      have hyu : y <+: u := by
        rw [← hy]
        exact streamTake_prefix_of_streamTake hym
      refine ⟨⟨u, rfl⟩, ?_, ?_⟩
      · change streamTake w u.length = u
        rw [streamTake_length]
      · rintro z' hz'
        exact ⟨EExtends_trans hxu hz', EExtends_trans hyu hz'⟩
  · rw [Set.sUnion_eq_univ_iff]
    intro z
    exact ⟨sequenceCylinder [], ⟨[], rfl⟩, by
      cases z <;> simp [sequenceCylinder, EExtends, streamTake]⟩

/-- **Theorem 53.** Characterization of the continuous maps `Σ ∪ Ω → ℕ⊥`. -/
theorem prefixTopology_continuous_iff (F : SeqE → Option ℕ) :
    @Continuous SeqE (Option ℕ) eTopology natBotTopology F ↔
      (∀ (x : BitString) (z : SeqE), EExtends x z → natBotLe (F (Sum.inl x)) (F z)) ∧
      (∀ w : ℕ → Bool, F (Sum.inr w) ≠ none →
        ∃ n, F (Sum.inl (streamTake w n)) ≠ none) := by
  let : TopologicalSpace SeqE := eTopology
  let : TopologicalSpace (Option ℕ) := natBotTopology
  have hbasis := eTopology_isBasis
  constructor
  · intro hF
    constructor
    · intro x z hxz
      by_cases hFx : F (Sum.inl x) = none
      · rw [hFx]
        exact Or.inl rfl
      · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists.mp hFx
        have hn' : F (Sum.inl x) = some n := hn.symm
        have hopen : IsOpen ({some n} : Set (Option ℕ)) := Or.inl (by simp)
        have hpre : IsOpen (F ⁻¹' {some n}) := Continuous.isOpen_preimage hF _ hopen
        have hx_mem : Sum.inl x ∈ F ⁻¹' {some n} := by simp [hn']
        rw [hbasis.isOpen_iff] at hpre
        obtain ⟨_, ⟨y, rfl⟩, hx_cyl, hcyl_sub⟩ := hpre (Sum.inl x) hx_mem
        change y <+: x at hx_cyl
        have hz_cyl : z ∈ sequenceCylinder y := EExtends_trans hx_cyl hxz
        have hz_mem : z ∈ F ⁻¹' {some n} := hcyl_sub hz_cyl
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz_mem
        rw [hn', hz_mem]
        exact Or.inr rfl
    · intro w hw
      obtain ⟨n, hn⟩ := Option.ne_none_iff_exists.mp hw
      have hn' : F (Sum.inr w) = some n := hn.symm
      have hopen : IsOpen ({some n} : Set (Option ℕ)) := Or.inl (by simp)
      have hpre : IsOpen (F ⁻¹' {some n}) := Continuous.isOpen_preimage hF _ hopen
      have hw_mem : Sum.inr w ∈ F ⁻¹' {some n} := by simp [hn']
      rw [hbasis.isOpen_iff] at hpre
      obtain ⟨_, ⟨y, rfl⟩, hw_cyl, hcyl_sub⟩ := hpre (Sum.inr w) hw_mem
      change streamTake w y.length = y at hw_cyl
      use y.length
      have h_inl : Sum.inl (streamTake w y.length) ∈ sequenceCylinder y := by
        change EExtends y (Sum.inl (streamTake w y.length))
        change y <+: streamTake w y.length
        rw [hw_cyl]
      have h_inl_mem : Sum.inl (streamTake w y.length) ∈ F ⁻¹' {some n} := hcyl_sub h_inl
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h_inl_mem
      rw [h_inl_mem]
      exact Option.some_ne_none _
  · rintro ⟨h1, h2⟩
    rw [continuous_def]
    intro s hs
    rcases hs with hs_none | rfl
    · rw [hbasis.isOpen_iff]
      intro z hz
      have hz_ne : F z ≠ none := fun h => hs_none (h ▸ hz)
      obtain ⟨m, hm_eq⟩ := Option.ne_none_iff_exists.mp hz_ne
      have hm_some : F z = some m := hm_eq.symm
      rcases z with x | w
      · use sequenceCylinder x
        refine ⟨⟨x, rfl⟩, ⟨[], by simp⟩, ?_⟩
        rintro z' hz'
        have hle := h1 x z' hz'
        rw [hm_some] at hle
        rcases hle with hnone | hcase
        · contradiction
        · change F z' ∈ s
          rw [← hcase, ← hm_some]
          exact hz
      · obtain ⟨k, hk⟩ := h2 w (hm_some ▸ Option.some_ne_none m)
        obtain ⟨m', hm'_eq⟩ := Option.ne_none_iff_exists.mp hk
        have hm'_some : F (Sum.inl (streamTake w k)) = some m' := hm'_eq.symm
        have h_ext : EExtends (streamTake w k) (Sum.inr w) := by
          change streamTake w (streamTake w k).length = streamTake w k
          rw [streamTake_length]
        have hle := h1 (streamTake w k) (Sum.inr w) h_ext
        rcases hle with hnone | hcase
        · rw [hm'_some] at hnone
          contradiction
        · have hcase2 := hcase
          rw [hm'_some, hm_some] at hcase2
          have hmeq : m' = m := Option.some.inj hcase2
          subst hmeq
          let x := streamTake w k
          use sequenceCylinder x
          have hw_cyl : Sum.inr w ∈ sequenceCylinder x := h_ext
          refine ⟨⟨x, rfl⟩, hw_cyl, ?_⟩
          rintro z' hz'
          have hle' := h1 x z' hz'
          rw [hm'_some] at hle'
          rcases hle' with hnone' | hcase'
          · contradiction
          · change F z' ∈ s
            rw [← hcase', ← hm_some]
            exact hz
    · simp only [Set.preimage_univ]
      exact isOpen_univ

/-- The finite part `Γ_F` of the graph of a map `F : Σ ∪ Ω → ℕ⊥`. -/
def contGraph (F : SeqE → Option ℕ) : Set (BitString × ℕ) :=
  {p | F (Sum.inl p.1) = some p.2}

/-- The graph sets arising in Theorem 54: upward closed under extension of the
string, and single-valued. -/
def IsCompatibleGraph (A : Set (BitString × ℕ)) : Prop :=
  (∀ (x y : BitString) (n : ℕ), (x, n) ∈ A → x <+: y → (y, n) ∈ A) ∧
  (∀ (x : BitString) (n m : ℕ), (x, n) ∈ A → (x, m) ∈ A → n = m)

/-- A map into the naturals with a bottom element is continuous exactly when the preimage of each
value is open. -/
lemma continuous_natBotTopology_iff (F : SeqE → Option ℕ) :
    @Continuous SeqE (Option ℕ) eTopology natBotTopology F ↔
      ∀ m : ℕ, @IsOpen SeqE eTopology (F ⁻¹' {some m}) := by
  let instSeqE : TopologicalSpace SeqE := eTopology
  let instOpt : TopologicalSpace (Option ℕ) := natBotTopology
  constructor
  · intro h m
    have h_open : IsOpen ({some m} : Set (Option ℕ)) := Or.inl (by simp)
    exact h.isOpen_preimage {some m} h_open
  · intro h
    rw [continuous_def]
    intro s hs
    rcases hs with hnone | rfl
    · have : s = ⋃ (m : ℕ) (_ : some m ∈ s), {some m} := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_singleton_iff]
        constructor
        · intro hx
          cases x with
          | none => contradiction
          | some m => exact ⟨m, hx, rfl⟩
        · rintro ⟨m, hm, rfl⟩
          exact hm
      rw [this]
      have hpre : F ⁻¹' (⋃ (m : ℕ) (_ : some m ∈ s), {some m}) =
          ⋃ (m : ℕ) (_ : some m ∈ s), F ⁻¹' {some m} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
      rw [hpre]
      exact isOpen_biUnion fun m _ => h m
    · rw [Set.preimage_univ]
      exact isOpen_univ

/-- An open set containing a finite string contains every extension of it. -/
lemma isOpen_eTopology_extends {U : Set SeqE} (hU : @IsOpen SeqE eTopology U)
    {x : BitString} {z : SeqE} (hxz : EExtends x z) (hx : Sum.inl x ∈ U) : z ∈ U := by
  let instSeqE : TopologicalSpace SeqE := eTopology
  induction hU with
  | basic s hs =>
    rcases hs with ⟨w, rfl⟩
    have hw : EExtends w (Sum.inl x) := hx
    cases z with
    | inl y =>
      have h1 : w <+: x := hw
      have h2 : x <+: y := hxz
      exact h1.trans h2
    | inr v =>
      have h1 : w <+: x := hw
      have h2 : streamTake v x.length = x := hxz
      dsimp [sequenceCylinder, EExtends] at *
      have hlen : w.length ≤ x.length := h1.length_le
      have htake : (streamTake v x.length).take w.length = streamTake v w.length := by
        dsimp [streamTake]
        rw [← List.map_take, List.take_range, min_eq_left hlen]
      rcases h1 with ⟨t, rfl⟩
      rw [h2] at htake
      rw [List.take_left] at htake
      exact htake.symm
  | univ => exact Set.mem_univ z
  | inter s t hs ht ihs iht =>
    exact ⟨ihs hx.1, iht hx.2⟩
  | sUnion S hS ih =>
    rcases hx with ⟨s, hsS, hxs⟩
    exact ⟨s, hsS, ih s hsS hxs⟩

/-- An open set containing an infinite sequence contains one of its finite prefixes. -/
lemma isOpen_eTopology_stream {U : Set SeqE} (hU : @IsOpen SeqE eTopology U)
    {w : ℕ → Bool} (hw : Sum.inr w ∈ U) : ∃ n, Sum.inl (streamTake w n) ∈ U := by
  let instSeqE : TopologicalSpace SeqE := eTopology
  induction hU with
  | basic s hs =>
    rcases hs with ⟨x, rfl⟩
    have hx : streamTake w x.length = x := hw
    use x.length
    dsimp [sequenceCylinder, EExtends]
    rw [hx]
  | univ =>
    use 0
    exact Set.mem_univ _
  | inter s t hs ht ihs iht =>
    rcases ihs hw.1 with ⟨n1, hn1⟩
    rcases iht hw.2 with ⟨n2, hn2⟩
    use max n1 n2
    have h1 : streamTake w n1 <+: streamTake w (max n1 n2) := by
      dsimp [streamTake]
      have htake : List.take n1 (List.range (max n1 n2)) = List.range n1 := by
        rw [List.take_range, min_eq_left (le_max_left n1 n2)]
      rw [← htake, List.map_take]
      exact List.take_prefix _ _
    have h2 : streamTake w n2 <+: streamTake w (max n1 n2) := by
      dsimp [streamTake]
      have htake : List.take n2 (List.range (max n1 n2)) = List.range n2 := by
        rw [List.take_range, min_eq_left (le_max_right n1 n2)]
      rw [← htake, List.map_take]
      exact List.take_prefix _ _
    constructor
    · exact isOpen_eTopology_extends hs h1 hn1
    · exact isOpen_eTopology_extends ht h2 hn2
  | sUnion S hS ih =>
    rcases hw with ⟨s, hsS, hws⟩
    rcases ih s hsS hws with ⟨n, hn⟩
    exact ⟨n, s, hsS, hn⟩

open Classical in
/-- The partial function read off a graph: the value at a sequence is the first value the graph
assigns to one of its finite prefixes. -/
noncomputable def F_of_A (A : Set (BitString × ℕ)) : SeqE → Option ℕ
  | Sum.inl x => if h : ∃ n, (x, n) ∈ A then some (Nat.find h) else none
  | Sum.inr w => if h : ∃ k : ℕ, (streamTake w (Nat.unpair k).1, (Nat.unpair k).2) ∈ A
                 then some (Nat.unpair (Nat.find h)).2 else none

open Classical in
/-- On a finite string the function read off a compatible graph returns exactly the value the
graph assigns to that string. -/
lemma F_of_A_inl_eq_some (A : Set (BitString × ℕ)) (hA : IsCompatibleGraph A)
    (x : BitString) (m : ℕ) :
    F_of_A A (Sum.inl x) = some m ↔ (x, m) ∈ A := by
  dsimp [F_of_A]
  split_ifs with h
  · constructor
    · intro hEq
      injection hEq with hEq
      subst hEq
      exact Nat.find_spec h
    · intro hxm
      have hSpec := Nat.find_spec h
      have hEq := hA.2 x (Nat.find h) m hSpec hxm
      subst hEq
      rfl
  · constructor
    · intro hEq; contradiction
    · intro hxm
      exfalso
      exact h ⟨m, hxm⟩

open Classical in
/-- On an infinite sequence the function returns the value the graph assigns to one of its finite
prefixes. -/
lemma F_of_A_inr_eq_some (A : Set (BitString × ℕ)) (hA : IsCompatibleGraph A)
    (w : ℕ → Bool) (m : ℕ) :
    F_of_A A (Sum.inr w) = some m ↔ ∃ n, (streamTake w n, m) ∈ A := by
  dsimp [F_of_A]
  split_ifs with h
  · constructor
    · intro hEq
      injection hEq with hEq
      subst hEq
      have hSpec := Nat.find_spec h
      exact ⟨(Nat.unpair (Nat.find h)).1, hSpec⟩
    · rintro ⟨n, hnm⟩
      have hSpec := Nat.find_spec h
      set n0 := (Nat.unpair (Nat.find h)).1
      set m0 := (Nat.unpair (Nat.find h)).2
      have hm : m0 = m := by
        rcases le_total n n0 with hle | hle
        · have hpref : streamTake w n <+: streamTake w n0 := by
            dsimp [streamTake]
            have htake : List.take n (List.range n0) = List.range n := by
              rw [List.take_range, min_eq_left hle]
            rw [← htake, List.map_take]
            exact List.take_prefix _ _
          have hUp := hA.1 (streamTake w n) (streamTake w n0) m hnm hpref
          exact hA.2 (streamTake w n0) m0 m hSpec hUp
        · have hpref : streamTake w n0 <+: streamTake w n := by
            dsimp [streamTake]
            have htake : List.take n0 (List.range n) = List.range n0 := by
              rw [List.take_range, min_eq_left hle]
            rw [← htake, List.map_take]
            exact List.take_prefix _ _
          have hUp := hA.1 (streamTake w n0) (streamTake w n) m0 hSpec hpref
          exact hA.2 (streamTake w n) m0 m hUp hnm
      rw [hm]
  · constructor
    · intro hEq; contradiction
    · rintro ⟨n, hnm⟩
      exfalso
      have hk : (streamTake w (Nat.unpair (Nat.pair n m)).1,
          (Nat.unpair (Nat.pair n m)).2) ∈ A := by
        rw [Nat.unpair_pair]
        exact hnm
      exact h ⟨Nat.pair n m, hk⟩

open Classical in
/-- The function read off a compatible graph returns `m` at a sequence exactly when the graph
assigns `m` to a finite string that the sequence extends. -/
lemma F_of_A_eq_some (A : Set (BitString × ℕ)) (hA : IsCompatibleGraph A) (z : SeqE) (m : ℕ) :
    F_of_A A z = some m ↔ ∃ x, (x, m) ∈ A ∧ EExtends x z := by
  cases z with
  | inl y =>
    rw [F_of_A_inl_eq_some A hA]
    constructor
    · intro hym
      use y
      exact ⟨hym, ⟨[], by simp⟩⟩
    · rintro ⟨x, hxm, hxy⟩
      exact hA.1 x y m hxm hxy
  | inr w =>
    rw [F_of_A_inr_eq_some A hA]
    constructor
    · rintro ⟨n, hnm⟩
      use streamTake w n
      refine ⟨hnm, ?_⟩
      dsimp [EExtends, streamTake]
      rw [List.length_map, List.length_range]
    · rintro ⟨x, hxm, hxz⟩
      use x.length
      dsimp [EExtends] at hxz
      rw [hxz]
      exact hxm

end Kolmogorov
