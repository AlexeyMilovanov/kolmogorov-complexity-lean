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
import KolmogorovMathlib.Complexity.EnumerableFamilies.CountingBounds
import KolmogorovMathlib.Complexity.EnumerableFamilies.Enumeration.BlockComputability

/-!
# Blocks of an enumerated family

An enumerable family is processed level by level: each level `m` receives a *pool* of strings,
filled from the enumeration and then frozen.  `qUsed`, `qBlock` and `qStage` are the strings
allocated below a level, the block allocated to it, and the test that all pools up to it are
full; each is primitive recursive.

The combinatorics: `qUsed_succ` and `qStage_iff` unfold the two recursions, `qStage_le`,
`qStage_mono` and `enumV_list_length_mono` say fullness is monotone in the level and the
stage, and `pBlock_stable` says a full pool never changes again.  On top of them,
`decompressor2Check_fires` and `decompressor2Check_spec` describe the stage attempt of the
block decompressor, and the two `partrec` lemmas make the search for a successful stage
effective.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Deciding `w a ∉ l a` is primitive recursive. -/
private lemma notMem_decide_primrec {α : Type*} [Primcodable α] {l : α → List BitString}
    {w : α → BitString} (hl : Primrec l) (hw : Primrec w) :
    Primrec (fun a => decide (w a ∉ l a)) := by
  have h : Primrec (fun a => !decide (w a ∈ l a)) :=
    Primrec.not.comp (Primrec₂.comp bitString_mem_primrec hw hl)
  exact h.of_eq (fun a => by simp)

/-- The list of strings allocated to the levels below `m` is primitive recursive in `(m, s)`. -/
lemma qUsed_primrec (c_k : Code) (c₁ : ℕ) :
    Primrec (fun (p : ℕ × ℕ) => qUsed c_k c₁ p.1 p.2) := by
  have h_step : Primrec₂ (fun (p : ℕ × ℕ) (q : ℕ × List BitString) =>
      q.2 ++ ((pBlock c_k c₁ q.1 p.2).filter (fun z => decide (z ∉ q.2))).take (2 ^ q.1)) := by
    have h_acc : Primrec (fun (a : (ℕ × ℕ) × ℕ × List BitString) => a.2.2) :=
      Primrec.snd.comp Primrec.snd
    have h_n : Primrec (fun (a : (ℕ × ℕ) × ℕ × List BitString) => a.2.1) :=
      Primrec.fst.comp Primrec.snd
    have h_s : Primrec (fun (a : (ℕ × ℕ) × ℕ × List BitString) => a.1.2) :=
      Primrec.snd.comp Primrec.fst
    have h_pool : Primrec (fun (a : (ℕ × ℕ) × ℕ × List BitString) =>
        pBlock c_k c₁ a.2.1 a.1.2) :=
      (pBlock_primrec c_k c₁).comp (Primrec.pair h_n h_s)
    have h_pred : Primrec₂ (fun (a : (ℕ × ℕ) × ℕ × List BitString) (z : BitString) =>
        decide (z ∉ a.2.2)) :=
      notMem_decide_primrec (h_acc.comp Primrec.fst) Primrec.snd
    have h_filter := Primrec.list_filter h_pool h_pred
    have h_pow : Primrec (fun (a : (ℕ × ℕ) × ℕ × List BitString) => 2 ^ a.2.1) :=
      primrec_two_pow_aux.comp h_n
    exact Primrec₂.comp Primrec.list_append h_acc
      (Primrec₂.comp (f := fun (l : List BitString) (n : ℕ) => l.take n)
        (Primrec.list_take.comp Primrec.snd Primrec.fst) h_filter h_pow)
  have h_rec := Primrec.nat_rec' (f := fun p : ℕ × ℕ => p.1)
    (g := fun _ : ℕ × ℕ => ([] : List BitString)) Primrec.fst (Primrec.const []) h_step
  refine h_rec.of_eq ?_
  rintro ⟨m, s⟩
  dsimp
  induction m with
  | zero => rfl
  | succ m ih =>
    dsimp [qUsed]
    rw [← ih]

/-- The block allocated to level `m` at stage `s` is primitive recursive in `(m, s)`. -/
lemma qBlock_primrec (c_k : Code) (c₁ : ℕ) :
    Primrec (fun (p : ℕ × ℕ) => qBlock c_k c₁ p.1 p.2) := by
  have h_pred : Primrec₂ (fun (p : ℕ × ℕ) (z : BitString) =>
      decide (z ∉ qUsed c_k c₁ p.1 p.2)) :=
    notMem_decide_primrec ((qUsed_primrec c_k c₁).comp Primrec.fst) Primrec.snd
  have h_filter := Primrec.list_filter (pBlock_primrec c_k c₁) h_pred
  have h_pow : Primrec (fun (p : ℕ × ℕ) => 2 ^ p.1) := primrec_two_pow_aux.comp Primrec.fst
  exact Primrec₂.comp (f := fun (l : List BitString) (n : ℕ) => l.take n)
    (Primrec.list_take.comp Primrec.snd Primrec.fst) h_filter h_pow

/-- Fullness of all pools up to level `m` at stage `s` is primitive recursive in `(m, s)`. -/
lemma qStage_primrec (c_k : Code) (c₁ : ℕ) :
    Primrec (fun (p : ℕ × ℕ) => qStage c_k c₁ p.1 p.2) := by
  have h_range : Primrec (fun (p : ℕ × ℕ) => List.range (p.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have h_pred : Primrec₂ (fun (p : ℕ × ℕ) (m' : ℕ) =>
      decide ((enumVList c_k (m' + c₁ + 1) p.2).length < 2 ^ (m' + 1))) := by
    have h_lvl : Primrec (fun (a : (ℕ × ℕ) × ℕ) => a.2 + c₁ + 1) :=
      Primrec.succ.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const c₁))
    have h_list : Primrec (fun (a : (ℕ × ℕ) × ℕ) => enumVList c_k (a.2 + c₁ + 1) a.1.2) :=
      (enumV_list_primrec c_k).comp (Primrec.pair h_lvl (Primrec.snd.comp Primrec.fst))
    have h_len : Primrec (fun (a : (ℕ × ℕ) × ℕ) =>
        (enumVList c_k (a.2 + c₁ + 1) a.1.2).length) := Primrec.list_length.comp h_list
    have h_pow : Primrec (fun (a : (ℕ × ℕ) × ℕ) => 2 ^ (a.2 + 1)) :=
      primrec_two_pow_aux.comp (Primrec.succ.comp Primrec.snd)
    exact (PrimrecPred.decide Primrec.nat_lt).comp (Primrec.pair h_len h_pow)
  have h_len := Primrec.list_length.comp (Primrec.list_filter h_range h_pred)
  exact (PrimrecPred.decide Primrec.eq).comp (Primrec.pair h_len (Primrec.const 0))

/-- The strings allocated below level `m + 1` are those allocated below level `m`
together with the block of level `m`. -/
lemma qUsed_succ (c_k : Code) (c₁ : ℕ) (m s : ℕ) :
    qUsed c_k c₁ (m + 1) s = qUsed c_k c₁ m s ++ qBlock c_k c₁ m s := rfl

/-- All pools up to level `m` are full at stage `s` exactly when every level `m' ≤ m` has
enumerated at least `2 ^ (m' + 1)` strings by then. -/
lemma qStage_iff (c_k : Code) (c₁ m s : ℕ) :
    qStage c_k c₁ m s = true ↔
      ∀ m' ≤ m, 2 ^ (m' + 1) ≤ (enumVList c_k (m' + c₁ + 1) s).length := by
  unfold qStage
  simp only [decide_eq_true_eq, List.length_eq_zero_iff, List.filter_eq_nil_iff,
    List.mem_range, Nat.lt_succ_iff, not_lt]

/-- Fullness at level `m` implies fullness at every lower level. -/
lemma qStage_le (c_k : Code) (c₁ : ℕ) {m m' s : ℕ} (h : qStage c_k c₁ m s = true)
    (hm : m' ≤ m) : qStage c_k c₁ m' s = true :=
  (qStage_iff c_k c₁ m' s).mpr fun j hj => (qStage_iff c_k c₁ m s).mp h j (hj.trans hm)

/-- The enumeration of a set grows with the stage. -/
lemma enumV_list_length_mono (c_k : Code) (n : ℕ) {s s' : ℕ} (h : s ≤ s') :
    (enumVList c_k n s).length ≤ (enumVList c_k n s').length :=
  (enumV_list_prefix c_k n s s' h).length_le

/-- Fullness at a stage persists at every later stage. -/
lemma qStage_mono (c_k : Code) (c₁ : ℕ) {m s s' : ℕ} (h : qStage c_k c₁ m s = true)
    (hs : s ≤ s') : qStage c_k c₁ m s' = true :=
  (qStage_iff c_k c₁ m s').mpr fun j hj =>
    ((qStage_iff c_k c₁ m s).mp h j hj).trans (enumV_list_length_mono c_k _ hs)

private lemma take_eq_take_of_prefix' {α : Type*} {l1 l2 : List α} (h : l1 <+: l2) {j : ℕ}
    (hj : j ≤ l1.length) : l2.take j = l1.take j := by
  obtain ⟨r, rfl⟩ := h
  exact List.take_append_of_le_length hj

/-- Once the pool of level `m` is full it no longer changes. -/
lemma pBlock_stable (c_k : Code) (c₁ : ℕ) {m s s' : ℕ}
    (h : 2 ^ (m + 1) ≤ (enumVList c_k (m + c₁ + 1) s).length) (hs : s ≤ s') :
    pBlock c_k c₁ m s' = pBlock c_k c₁ m s :=
  take_eq_take_of_prefix' (enumV_list_prefix c_k (m + c₁ + 1) s s' hs) h

/-- Once all pools up to level `m` are full, neither the allocated strings nor the pool
of level `m` change. -/
lemma qUsed_stable (c_k : Code) (c₁ : ℕ) :
    ∀ (m s s' : ℕ), qStage c_k c₁ m s = true → s ≤ s' →
      qUsed c_k c₁ m s' = qUsed c_k c₁ m s ∧ pBlock c_k c₁ m s' = pBlock c_k c₁ m s := by
  intro m
  induction m with
  | zero =>
    intro s s' hst hss
    exact ⟨rfl, pBlock_stable c_k c₁ ((qStage_iff c_k c₁ 0 s).mp hst 0 le_rfl) hss⟩
  | succ m ih =>
    intro s s' hst hss
    obtain ⟨hU, hP⟩ := ih s s' (qStage_le c_k c₁ hst (Nat.le_succ m)) hss
    refine ⟨?_, pBlock_stable c_k c₁ ((qStage_iff c_k c₁ (m + 1) s).mp hst (m + 1) le_rfl) hss⟩
    have e : ∀ t : ℕ, qUsed c_k c₁ (m + 1) t
        = qUsed c_k c₁ m t ++ ((pBlock c_k c₁ m t).filter
            (fun z => decide (z ∉ qUsed c_k c₁ m t))).take (2 ^ m) := fun _ => rfl
    rw [e, e, hU, hP]

/-- Once all pools up to level `m` are full, the block of level `m` no longer changes. -/
lemma qBlock_stable (c_k : Code) (c₁ : ℕ) {m s s' : ℕ} (hst : qStage c_k c₁ m s = true)
    (hss : s ≤ s') : qBlock c_k c₁ m s' = qBlock c_k c₁ m s := by
  obtain ⟨hU, hP⟩ := qUsed_stable c_k c₁ m s s' hst hss
  unfold qBlock
  rw [hU, hP]

/-- A block of level `m` holds at most `2 ^ m` strings. -/
lemma qBlock_length_le (c_k : Code) (c₁ : ℕ) (m s : ℕ) :
    (qBlock c_k c₁ m s).length ≤ 2 ^ m := by
  unfold qBlock
  rw [List.length_take]
  exact min_le_left _ _

/-- Fewer than `2 ^ m` strings are allocated to the levels below `m`. -/
lemma qUsed_length_lt (c_k : Code) (c₁ : ℕ) (m s : ℕ) :
    (qUsed c_k c₁ m s).length + 1 ≤ 2 ^ m := by
  induction m with
  | zero => simp [qUsed]
  | succ m ih =>
    have hb := qBlock_length_le c_k c₁ m s
    have hpow : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
    rw [qUsed_succ, List.length_append]
    omega

/-- A pool lists no string twice. -/
lemma pBlock_nodup (c_k : Code) (c₁ : ℕ) (m s : ℕ) : (pBlock c_k c₁ m s).Nodup := by
  unfold pBlock
  exact (List.take_sublist _ _).nodup (enumV_list_nodup c_k (m + c₁ + 1) s)

/-- A block lists no string twice. -/
lemma qBlock_nodup (c_k : Code) (c₁ : ℕ) (m s : ℕ) : (qBlock c_k c₁ m s).Nodup := by
  unfold qBlock
  exact (List.take_sublist _ _).nodup (List.filter_sublist.nodup (pBlock_nodup c_k c₁ m s))

private lemma length_filter_add' {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases h : p a <;> simp [h] <;> omega

/-- Once all pools up to level `m` are full, the block of level `m` holds exactly `2 ^ m`
strings. -/
lemma qBlock_length (c_k : Code) (c₁ : ℕ) {m s : ℕ} (hst : qStage c_k c₁ m s = true) :
    (qBlock c_k c₁ m s).length = 2 ^ m := by
  have hlen : 2 ^ (m + 1) ≤ (enumVList c_k (m + c₁ + 1) s).length :=
    (qStage_iff c_k c₁ m s).mp hst m le_rfl
  have hP_len : (pBlock c_k c₁ m s).length = 2 ^ (m + 1) := by
    unfold pBlock
    rw [List.length_take]
    omega
  have hsplit := length_filter_add' (pBlock c_k c₁ m s)
    (fun z => decide (z ∉ qUsed c_k c₁ m s))
  have hbad : ((pBlock c_k c₁ m s).filter
      (fun z => !decide (z ∉ qUsed c_k c₁ m s))).length ≤ (qUsed c_k c₁ m s).length := by
    refine (List.subperm_of_subset ?_ ?_).length_le
    · exact List.filter_sublist.nodup (pBlock_nodup c_k c₁ m s)
    · intro x hx
      rw [List.mem_filter] at hx
      simpa using hx.2
  have hU := qUsed_length_lt c_k c₁ m s
  have hpow : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
  unfold qBlock
  rw [List.length_take]
  omega

/-- A string of the block of level `m` is not allocated to a lower level. -/
lemma qBlock_notMem_qUsed (c_k : Code) (c₁ : ℕ) (m s : ℕ) {z : BitString}
    (hz : z ∈ qBlock c_k c₁ m s) : z ∉ qUsed c_k c₁ m s := by
  unfold qBlock at hz
  have h := List.mem_of_mem_take hz
  rw [List.mem_filter] at h
  simpa using h.2

/-- The block of level `m` is taken from the pool of level `m`. -/
lemma qBlock_mem_pBlock (c_k : Code) (c₁ : ℕ) (m s : ℕ) {z : BitString}
    (hz : z ∈ qBlock c_k c₁ m s) : z ∈ pBlock c_k c₁ m s := by
  unfold qBlock at hz
  have h := List.mem_of_mem_take hz
  rw [List.mem_filter] at h
  exact h.1

/-- A string of the block of level `m` has been enumerated into the set of level
`m + c₁ + 1`. -/
lemma qBlock_mem_enumV (c_k : Code) (c₁ : ℕ) (m s : ℕ) {z : BitString}
    (hz : z ∈ qBlock c_k c₁ m s) : z ∈ enumVList c_k (m + c₁ + 1) s := by
  have h := qBlock_mem_pBlock c_k c₁ m s hz
  unfold pBlock at h
  exact List.mem_of_mem_take h

/-- A string of the block of level `m` counts as allocated at every higher level. -/
lemma qBlock_subset_qUsed (c_k : Code) (c₁ : ℕ) {m m' s : ℕ} {z : BitString}
    (hz : z ∈ qBlock c_k c₁ m s) (h : m < m') : z ∈ qUsed c_k c₁ m' s := by
  induction m' with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ m'' ih =>
    rw [qUsed_succ, List.mem_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h1 | h1
    · exact Or.inl (ih h1)
    · exact Or.inr (h1 ▸ hz)

/-- The blocks of different levels are disjoint, so a string determines its level. -/
lemma qBlock_level_unique (c_k : Code) (c₁ : ℕ) {m m' s : ℕ} {z : BitString}
    (hz : z ∈ qBlock c_k c₁ m s) (hz' : z ∈ qBlock c_k c₁ m' s) : m = m' := by
  rcases lt_trichotomy m m' with h | h | h
  · exact absurd (qBlock_subset_qUsed c_k c₁ hz h) (qBlock_notMem_qUsed c_k c₁ m' s hz')
  · exact h
  · exact absurd (qBlock_subset_qUsed c_k c₁ hz' h) (qBlock_notMem_qUsed c_k c₁ m s hz)

/-- The stage-`s` attempt of the block decompressor: if `s` codes a level `m` and a stage
`t` at which all pools up to `m` are full and the input lies in the block of level `m`,
the output is the string of length `m` with the same index in that block. -/
def decompressor2Check (c_k : Code) (c₁ : ℕ) (z : BitString) (s : ℕ) : Option BitString :=
  let m := s.unpair.1
  let t := s.unpair.2
  bif qStage c_k c₁ m t && decide (z ∈ qBlock c_k c₁ m t) then
    some ((exactLengthPrograms m).getD ((qBlock c_k c₁ m t).findIdx (fun x => x == z)) [])
  else none

/-- The block decompressor: it searches for a stage at which its input is recognised as an
element of a block and outputs the corresponding string of the block's length. -/
def decompressor2 (c_k : Code) (c₁ : ℕ) : BitString →. BitString := fun z =>
  (Nat.rfind (fun s => Part.some (decompressor2Check c_k c₁ z s).isSome)).bind
    (fun s => Part.ofOption (decompressor2Check c_k c₁ z s))

/-- The stage attempt of the block decompressor is computable. -/
lemma decompressor2Check_computable (c_k : Code) (c₁ : ℕ) :
    Computable (fun (p : BitString × ℕ) => decompressor2Check c_k c₁ p.1 p.2) := by
  have h_m : Primrec (fun (p : BitString × ℕ) => p.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have h_t : Primrec (fun (p : BitString × ℕ) => p.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have h_ms : Primrec (fun (p : BitString × ℕ) => (p.2.unpair.1, p.2.unpair.2)) :=
    Primrec.pair h_m h_t
  have h_stage : Primrec (fun (p : BitString × ℕ) =>
      qStage c_k c₁ p.2.unpair.1 p.2.unpair.2) := (qStage_primrec c_k c₁).comp h_ms
  have h_block : Primrec (fun (p : BitString × ℕ) =>
      qBlock c_k c₁ p.2.unpair.1 p.2.unpair.2) := (qBlock_primrec c_k c₁).comp h_ms
  have h_mem : Primrec (fun (p : BitString × ℕ) =>
      decide (p.1 ∈ qBlock c_k c₁ p.2.unpair.1 p.2.unpair.2)) :=
    Primrec₂.comp bitString_mem_primrec Primrec.fst h_block
  have h_and : Primrec (fun (ab : Bool × Bool) => ab.1 && ab.2) :=
    (Primrec.cond Primrec.fst Primrec.snd (Primrec.const false)).of_eq (by
      intro ⟨a, b⟩; cases a <;> cases b <;> rfl)
  have h_cond : Computable (fun (p : BitString × ℕ) =>
      qStage c_k c₁ p.2.unpair.1 p.2.unpair.2 &&
        decide (p.1 ∈ qBlock c_k c₁ p.2.unpair.1 p.2.unpair.2)) :=
    (h_and.comp (Primrec.pair h_stage h_mem)).to_comp
  have h_j : Primrec (fun (p : BitString × ℕ) =>
      (qBlock c_k c₁ p.2.unpair.1 p.2.unpair.2).findIdx (fun x => x == p.1)) := by
    have h2 : Primrec₂ (fun (p : BitString × ℕ) (x : BitString) => decide (x = p.1)) := by
      have h_eq : Primrec (fun (q : (BitString × ℕ) × BitString) => decide (q.2 = q.1.1)) :=
        (PrimrecPred.decide Primrec.eq).comp
          (Primrec.pair Primrec.snd (Primrec.fst.comp Primrec.fst))
      exact h_eq.to₂
    exact (Primrec.list_findIdx h_block h2).of_eq (by
      intro p; congr 1; ext x; by_cases h : x = p.1 <;> simp [h])
  have h_out : Computable (fun (p : BitString × ℕ) =>
      some ((exactLengthPrograms p.2.unpair.1).getD
        ((qBlock c_k c₁ p.2.unpair.1 p.2.unpair.2).findIdx (fun x => x == p.1)) [])) :=
    Computable.option_some.comp
      (Primrec₂.comp (f := fun (l : List BitString) (n : ℕ) => l.getD n [])
        (Primrec.list_getD []) (primrec_exactLengthPrograms.comp h_m) h_j).to_comp
  exact Computable.cond h_cond h_out (Computable.const none)

/-- Defining equation of `decompressor2Check`, stated before the definition is made
irreducible. -/
lemma decompressor2Check_def (c_k : Code) (c₁ : ℕ) (z : BitString) (s : ℕ) :
    decompressor2Check c_k c₁ z s =
      (bif qStage c_k c₁ s.unpair.1 s.unpair.2 &&
            decide (z ∈ qBlock c_k c₁ s.unpair.1 s.unpair.2) then
          some ((exactLengthPrograms s.unpair.1).getD
            ((qBlock c_k c₁ s.unpair.1 s.unpair.2).findIdx (fun x => x == z)) [])
        else none) := rfl

/-- At a stage coding a full level containing the input, the attempt succeeds with the
indexed string of that length. -/
lemma decompressor2Check_fires (c_k : Code) (c₁ : ℕ) (z : BitString) (m t : ℕ)
    (hst : qStage c_k c₁ m t = true) (hz : z ∈ qBlock c_k c₁ m t) :
    decompressor2Check c_k c₁ z (Nat.pair m t) =
      some ((exactLengthPrograms m).getD
        ((qBlock c_k c₁ m t).findIdx (fun x => x == z)) []) := by
  simp only [decompressor2Check_def, Nat.unpair_pair, hst, decide_eq_true hz, Bool.and_self,
    Bool.cond_true]

/-- A successful attempt certifies fullness, membership in the block, and identifies the
value. -/
lemma decompressor2Check_spec (c_k : Code) (c₁ : ℕ) (z : BitString) (s : ℕ) {y : BitString}
    (h : decompressor2Check c_k c₁ z s = some y) :
    qStage c_k c₁ s.unpair.1 s.unpair.2 = true ∧ z ∈ qBlock c_k c₁ s.unpair.1 s.unpair.2 ∧
      y = (exactLengthPrograms s.unpair.1).getD
        ((qBlock c_k c₁ s.unpair.1 s.unpair.2).findIdx (fun x => x == z)) [] := by
  rw [decompressor2Check_def] at h
  by_cases hb : qStage c_k c₁ s.unpair.1 s.unpair.2 = true ∧
      z ∈ qBlock c_k c₁ s.unpair.1 s.unpair.2
  · obtain ⟨h1, h2⟩ := hb
    refine ⟨h1, h2, ?_⟩
    rw [h1, decide_eq_true h2] at h
    simp only [Bool.and_self, Bool.cond_true, Option.some.injEq] at h
    exact h.symm
  · exfalso
    have hfalse : (qStage c_k c₁ s.unpair.1 s.unpair.2 &&
        decide (z ∈ qBlock c_k c₁ s.unpair.1 s.unpair.2)) = false := by
      rcases Bool.eq_false_or_eq_true (qStage c_k c₁ s.unpair.1 s.unpair.2) with h1 | h1
      · have h2 : z ∉ qBlock c_k c₁ s.unpair.1 s.unpair.2 := fun hmem => hb ⟨h1, hmem⟩
        simp [h1, h2]
      · simp [h1]
    rw [hfalse] at h
    simp at h

attribute [irreducible] decompressor2Check

/-- Success of the stage attempt is computable. -/
lemma decompressor2Check_isSome_computable (c_k : Code) (c₁ : ℕ) :
    Computable (fun (p : BitString × ℕ) => (decompressor2Check c_k c₁ p.1 p.2).isSome) :=
  Primrec.option_isSome.to_comp.comp (decompressor2Check_computable c_k c₁)

/-- The predicate driving the search for a successful stage is partial computable. -/
lemma decompressor2Check_rfind_p_partrec (c_k : Code) (c₁ : ℕ) :
    Partrec (fun (p : BitString × ℕ) => Part.some (decompressor2Check c_k c₁ p.1 p.2).isSome) :=
  Partrec.some.comp (decompressor2Check_isSome_computable c_k c₁)

end Kolmogorov
