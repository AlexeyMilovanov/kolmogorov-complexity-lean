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



namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-!
### The decompressor of Theorem 9

Fix the enumeration `enumVList c_k n ·` of `{x | k x < n}`.  For a level `m` put

* `pBlock m s` — the first `2 ^ (m + 1)` strings enumerated into `{x | k x < m + c₁ + 1}` by
  stage `s`; the calibration hypothesis guarantees that this pool eventually gets full;
* `qUsed m s` — the strings already allocated to the levels `< m`;
* `qBlock m s` — the first `2 ^ m` strings of `pBlock m s` that are still unallocated.

Since `|qUsed m s| < 2 ^ m` while `|pBlock m s| = 2 ^ (m + 1)`, the block `qBlock m s` has exactly
`2 ^ m` elements as soon as all pools up to level `m` are full (`qStage m s`), and the blocks of
different levels are disjoint.  Consequently "the `j`-th element of `qBlock m ·` ↦ the `j`-th
string of length `m`" is a *single-valued* partial computable function of its argument alone:
the level `m` is not supplied, it is recovered by searching for the block containing the input,
and disjointness makes that search unambiguous.  This is what makes `k y ≤ |y| + O(1)` provable
from the axioms. -/

/-! #### Computability of the block machinery -/

/-! #### Combinatorics of the blocks -/

/-- A string accepted by stage `s₀` first appears at some stage `s ≤ s₀`. -/
theorem firstAppearsAt_spec (c_V : Code) (n : ℕ) (x : BitString) (s_0 : ℕ)
    (hs0_eval : (Code.evaln s_0 c_V (Encodable.encode (n, x))).isSome = true)
    (hs0_len : x.length ≤ s_0) :
    ∃ s_first ≤ s_0, (Code.evaln s_first c_V (Encodable.encode (n, x))).isSome = true ∧
      (if s_first = 0 then true
       else !((Code.evaln (s_first - 1) c_V (Encodable.encode (n, x))).isSome &&
         decide (x.length ≤ s_first - 1))) = true ∧
      x.length ≤ s_first := by
  induction s_0 with
  | zero =>
    refine ⟨0, le_rfl, hs0_eval, rfl, hs0_len⟩
  | succ s' ih =>
    by_cases h_prev : (Code.evaln s' c_V (Encodable.encode (n, x))).isSome = true ∧ x.length ≤ s'
    · obtain ⟨sf, hsf_le, hsf_eval, hsf_spec, hsf_len⟩ := ih h_prev.1 h_prev.2
      exact ⟨sf, hsf_le.trans (Nat.le_succ s'), hsf_eval, hsf_spec, hsf_len⟩
    · refine ⟨s' + 1, le_rfl, hs0_eval, ?_, hs0_len⟩
      have h_f : ((Code.evaln s' c_V (Encodable.encode (n, x))).isSome &&
          decide (x.length ≤ s')) = false := by
        cases h_b : ((Code.evaln s' c_V (Encodable.encode (n, x))).isSome &&
            decide (x.length ≤ s'))
        · rfl
        · have h_and := (Bool.and_eq_true _ _).mp h_b
          have h1 : (Code.evaln s' c_V (Encodable.encode (n, x))).isSome = true := h_and.1
          have h2 : x.length ≤ s' := by simpa using h_and.2
          exact False.elim (h_prev ⟨h1, h2⟩)
      have h_succ_ne : s' + 1 ≠ 0 := Nat.succ_ne_zero s'
      simp only [h_succ_ne, if_false, Nat.add_sub_cancel]
      rw [h_f]
      rfl

private def firstAppearsAt (c_V : Code) (n : ℕ) (s : ℕ) (z : BitString) : Bool :=
  (Code.evaln s c_V (Encodable.encode (n, z))).isSome &&
  decide (z.length ≤ s) &&
  if s = 0 then true
  else !((Code.evaln (s - 1) c_V (Encodable.encode (n, z))).isSome &&
    decide (z.length ≤ s - 1))

/-- The strings that first appear at stage `s` in the enumeration of the `n`-th set
of the family enumerated by the code `c_V`. -/
def enumVStep (c_V : Code) (n : ℕ) (s : ℕ) : List BitString :=
  (((List.range (s + 1)).flatMap allStrings).filter (firstAppearsAt c_V n s)).dedup

private theorem enumV_step_def (c_V : Code) (n : ℕ) (s : ℕ) :
    enumVStep c_V n s =
      (((List.range (s + 1)).flatMap allStrings).filter (firstAppearsAt c_V n s)).dedup :=
  rfl

/-- The strings enumerated into the `n`-th set of the family coded by `c_V` up to
stage `s`, listed in the order in which they appear. -/
def enumVList (c_V : Code) (n : ℕ) : ℕ → List BitString
  | 0 => enumVStep c_V n 0
  | s + 1 => enumVList c_V n s ++ enumVStep c_V n (s + 1)

/-- Membership criterion for the stage-`s` layer of the enumeration. -/
theorem enumV_step_mem (c_V : Code) (n s : ℕ) (z : BitString)
    (hz_eval : (Code.evaln s c_V (Encodable.encode (n, z))).isSome = true)
    (hz_first : (if s = 0 then true
      else !((Code.evaln (s - 1) c_V (Encodable.encode (n, z))).isSome &&
        decide (z.length ≤ s - 1))) = true)
    (hz_len : z.length ≤ s) :
    z ∈ enumVStep c_V n s := by
  dsimp [enumVStep]
  rw [List.mem_dedup, List.mem_filter, List.mem_flatMap]
  have h_halt : firstAppearsAt c_V n s z = true := by
    dsimp [firstAppearsAt]
    have h_len_b : decide (z.length ≤ s) = true := decide_eq_true hz_len
    have hz_eval' : (Code.evaln s c_V (Nat.pair n (Encodable.encode z))).isSome = true :=
      hz_eval
    have hz_first' : (if s = 0 then true
      else !((Code.evaln (s - 1) c_V (Nat.pair n (Encodable.encode z))).isSome &&
        decide (z.length ≤ s - 1))) = true := hz_first
    rw [hz_eval', h_len_b, hz_first']
    rfl
  refine ⟨⟨z.length, List.mem_range.mpr (by omega), (mem_allStrings z.length z).mpr rfl⟩, h_halt⟩

private theorem firstAppearsAt_primrec (c_V : Code) :
    Primrec₂ (fun (p : ℕ × ℕ) (z : BitString) =>
      (Code.evaln p.2 c_V (Encodable.encode (p.1, z))).isSome &&
      decide (z.length ≤ p.2) &&
      if p.2 = 0 then true
      else !((Code.evaln (p.2 - 1) c_V (Encodable.encode (p.1, z))).isSome &&
        decide (z.length ≤ p.2 - 1))) := by
  have h_s : Primrec (fun q : (ℕ × ℕ) × BitString => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have h_n : Primrec (fun q : (ℕ × ℕ) × BitString => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have h_len : Primrec (fun q : (ℕ × ℕ) × BitString => q.2.length) :=
    Primrec.list_length.comp Primrec.snd
  obtain ⟨_, h_le_curr_p⟩ := Primrec.nat_le.comp h_len h_s
  have h_le_curr : Primrec (fun q : (ℕ × ℕ) × BitString => decide (q.2.length ≤ q.1.2)) :=
    h_le_curr_p
  have h_enc : Primrec (fun q : (ℕ × ℕ) × BitString =>
      Encodable.encode (q.1.1, q.2)) :=
    Primrec.encode.comp (Primrec.pair h_n Primrec.snd)
  have heval : Primrec (fun q : (ℕ × ℕ) × BitString =>
      Code.evaln q.1.2 c_V (Encodable.encode (q.1.1, q.2))) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair h_s (Primrec.const c_V)) h_enc)
  have h1_bif : Primrec (fun q : (ℕ × ℕ) × BitString =>
      bif (Code.evaln q.1.2 c_V (Encodable.encode (q.1.1, q.2))).isSome then
        decide (q.2.length ≤ q.1.2)
      else false) :=
    Primrec.cond (Primrec.option_isSome.comp heval) h_le_curr (Primrec.const false)
  have h1_eq : Primrec (fun q : (ℕ × ℕ) × BitString =>
      (Code.evaln q.1.2 c_V (Encodable.encode (q.1.1, q.2))).isSome &&
      decide (q.2.length ≤ q.1.2)) :=
    h1_bif.of_eq (by
      intro q
      cases (Code.evaln q.1.2 c_V (Encodable.encode (q.1.1, q.2))).isSome <;> rfl)
  have h_prev_s : Primrec (fun q : (ℕ × ℕ) × BitString => q.1.2 - 1) :=
    Primrec.nat_sub.comp h_s (Primrec.const 1)
  have h_prev_eval : Primrec (fun q : (ℕ × ℕ) × BitString =>
      Code.evaln (q.1.2 - 1) c_V (Encodable.encode (q.1.1, q.2))) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair h_prev_s (Primrec.const c_V)) h_enc)
  have h_prev_isSome : Primrec (fun q : (ℕ × ℕ) × BitString =>
      (Code.evaln (q.1.2 - 1) c_V (Encodable.encode (q.1.1, q.2))).isSome) :=
    Primrec.option_isSome.comp h_prev_eval
  obtain ⟨_, h_prev_le_p⟩ := Primrec.nat_le.comp h_len h_prev_s
  have h_prev_le : Primrec (fun q : (ℕ × ℕ) × BitString =>
    decide (q.2.length ≤ q.1.2 - 1)) := h_prev_le_p
  have h_prev_both : Primrec (fun q : (ℕ × ℕ) × BitString =>
      bif (Code.evaln (q.1.2 - 1) c_V (Encodable.encode (q.1.1, q.2))).isSome then
        !decide (q.2.length ≤ q.1.2 - 1)
      else true) :=
    Primrec.cond h_prev_isSome (Primrec.not.comp h_prev_le) (Primrec.const true)
  have h2 : Primrec (fun q : (ℕ × ℕ) × BitString =>
      if q.1.2 = 0 then true
      else !((Code.evaln (q.1.2 - 1) c_V (Encodable.encode (q.1.1, q.2))).isSome &&
        decide (q.2.length ≤ q.1.2 - 1))) := by
    obtain ⟨_, h_eq0_p⟩ := Primrec.eq.comp h_s (Primrec.const 0)
    have h_cond := Primrec.cond h_eq0_p (Primrec.const true) h_prev_both
    exact h_cond.of_eq (by
      intro ⟨⟨n, s⟩, z⟩
      dsimp
      by_cases h0 : s = 0 <;> simp [h0])
  have h_and := Primrec.cond h1_eq h2 (Primrec.const false)
  have h_and_eq : Primrec (fun q : (ℕ × ℕ) × BitString =>
      ((Code.evaln q.1.2 c_V (Encodable.encode (q.1.1, q.2))).isSome &&
        decide (q.2.length ≤ q.1.2)) &&
      if q.1.2 = 0 then true
      else !((Code.evaln (q.1.2 - 1) c_V (Encodable.encode (q.1.1, q.2))).isSome &&
        decide (q.2.length ≤ q.1.2 - 1))) :=
    h_and.of_eq (by
      intro q
      cases ((Code.evaln q.1.2 c_V (Encodable.encode (q.1.1, q.2))).isSome &&
        decide (q.2.length ≤ q.1.2)) <;> rfl)
  exact h_and_eq.to₂.of_eq (by intro p z; dsimp; congr)

private theorem enumV_step_primrec (c_V : Code) :
    Primrec (fun (p : ℕ × ℕ) => enumVStep c_V p.1 p.2) := by
  have h_range : Primrec (fun (p : ℕ × ℕ) => List.range (p.2 + 1)) :=
    Primrec.list_range.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have h_flatMap : Primrec (fun (p : ℕ × ℕ) =>
      (List.range (p.2 + 1)).flatMap allStrings) :=
    Primrec.list_flatMap h_range (allStrings_primrec.comp Primrec.snd).to₂
  have h_filt : Primrec (fun (p : ℕ × ℕ) =>
      ((List.range (p.2 + 1)).flatMap allStrings).filter (firstAppearsAt c_V p.1 p.2)) :=
    list_filter_primrec h_flatMap (firstAppearsAt_primrec c_V)
  exact dedup_primrec.comp h_filt

/-- The enumeration `(n, s) ↦ enumVList c_V n s` is primitive recursive. -/
theorem enumV_list_primrec (c_V : Code) :
    Primrec (fun (p : ℕ × ℕ) => enumVList c_V p.1 p.2) := by
  have h_step : Primrec (fun (p : (ℕ × ℕ) × List BitString) =>
      p.2 ++ enumVStep c_V p.1.1 (p.1.2 + 1)) := by
    have h_next_s : Primrec (fun (p : (ℕ × ℕ) × List BitString) => p.1.2 + 1) :=
      Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)
    have h_p_next : Primrec (fun (p : (ℕ × ℕ) × List BitString) =>
        (p.1.1, p.1.2 + 1)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst) h_next_s
    have h_enum_step : Primrec (fun (p : (ℕ × ℕ) × List BitString) =>
        enumVStep c_V p.1.1 (p.1.2 + 1)) :=
      (enumV_step_primrec c_V).comp h_p_next
    exact Primrec₂.comp Primrec.list_append Primrec.snd h_enum_step
  have h_zero : Primrec (fun (p : ℕ) => enumVStep c_V p 0) :=
    (enumV_step_primrec c_V).comp (Primrec.pair Primrec.id (Primrec.const 0))
  have h_rec := Primrec.nat_rec (f := fun p : ℕ => enumVStep c_V p 0)
    (g := fun (p : ℕ) (acc : ℕ × List BitString) => acc.2 ++ enumVStep c_V p (acc.1 + 1))
    (hf := h_zero)
    (hg := by
      have h_acc_p : Primrec (fun (q : ℕ × ℕ × List BitString) =>
          ((q.1, q.2.1), q.2.2)) :=
        Primrec.pair (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)
      exact h_step.comp h_acc_p)
  have h_eval : Primrec (fun (p : ℕ × ℕ) =>
      enumVList c_V p.1 p.2) := by
    have h_rec_comp := h_rec.comp Primrec.fst Primrec.snd
    exact h_rec_comp.of_eq (by
      intro ⟨n, s⟩
      dsimp
      induction s with
      | zero => rfl
      | succ s' ih =>
        dsimp [enumVList]
        rw [← ih])
  exact h_eval

/-- Every string enumerated into the `n`-th set really belongs to it. -/
theorem enumV_list_sub (V : ℕ → Set BitString) (c_V : Code)
    (f_V : ℕ × BitString →. Unit)
    (hc_V : c_V.eval = fun n => (Part.ofOption (Encodable.decode n)).bind
      (fun a => (f_V a).map Encodable.encode))
    (hf_V_dom : ∀ a, (f_V a).Dom ↔ a.2 ∈ V a.1)
    (n s : ℕ) :
    ∀ z ∈ enumVList c_V n s, z ∈ V n := by
  induction s with
  | zero =>
    intro z hz
    dsimp [enumVList] at hz
    rw [enumV_step_def] at hz
    rw [List.mem_dedup, List.mem_filter] at hz
    dsimp [firstAppearsAt] at hz
    have hz_isSome := (Bool.and_eq_true _ _).mp hz.2 |>.1
    have hz_eval := (Bool.and_eq_true _ _).mp hz_isSome |>.1
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hz_eval
    have h_sound := Nat.Partrec.Code.evaln_sound hr
    change r ∈ c_V.eval (Encodable.encode (n, z)) at h_sound
    rw [hc_V] at h_sound
    dsimp only at h_sound
    have h_dec : Encodable.decode (Encodable.encode (n, z)) = some (n, z) :=
      Encodable.encodek (n, z)
    rw [h_dec] at h_sound
    dsimp [Part.ofOption] at h_sound
    rw [Part.bind_some] at h_sound
    simp only [Part.mem_map_iff] at h_sound
    obtain ⟨u_unit, hf_z, _⟩ := h_sound
    exact (hf_V_dom (n, z)).mp (Part.dom_iff_mem.mpr ⟨u_unit, hf_z⟩)
  | succ s' ih =>
    intro z hz
    dsimp [enumVList] at hz
    rw [List.mem_append] at hz
    rcases hz with h_prev | h_step
    · exact ih z h_prev
    · rw [enumV_step_def] at h_step
      rw [List.mem_dedup, List.mem_filter] at h_step
      dsimp [firstAppearsAt] at h_step
      have hz_isSome := (Bool.and_eq_true _ _).mp h_step.2 |>.1
      have hz_eval := (Bool.and_eq_true _ _).mp hz_isSome |>.1
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hz_eval
      have h_sound := Nat.Partrec.Code.evaln_sound hr
      change r ∈ c_V.eval (Encodable.encode (n, z)) at h_sound
      rw [hc_V] at h_sound
      dsimp only at h_sound
      have h_dec : Encodable.decode (Encodable.encode (n, z)) = some (n, z) :=
        Encodable.encodek (n, z)
      rw [h_dec] at h_sound
      dsimp [Part.ofOption] at h_sound
      rw [Part.bind_some] at h_sound
      simp only [Part.mem_map_iff] at h_sound
      obtain ⟨u_unit, hf_z, _⟩ := h_sound
      exact (hf_V_dom (n, z)).mp (Part.dom_iff_mem.mpr ⟨u_unit, hf_z⟩)

private theorem enumV_list_evaln (c_V : Code) (n : ℕ) (s : ℕ) (z : BitString)
    (hz : z ∈ enumVList c_V n s) :
    (Code.evaln s c_V (Encodable.encode (n, z))).isSome = true ∧ z.length ≤ s := by
  induction s with
  | zero =>
    dsimp [enumVList] at hz
    rw [enumV_step_def] at hz
    rw [List.mem_dedup, List.mem_filter] at hz
    dsimp [firstAppearsAt] at hz
    have h1 := (Bool.and_eq_true _ _).mp hz.2 |>.1
    have h_and := (Bool.and_eq_true _ _).mp h1
    have h_len : z.length ≤ 0 := by
      rw [List.mem_flatMap] at hz
      obtain ⟨⟨lz, hlz_range, hlz_all⟩, _⟩ := hz
      rw [List.mem_singleton] at hlz_range
      subst hlz_range
      rw [mem_allStrings] at hlz_all
      exact le_of_eq hlz_all
    exact ⟨h_and.1, h_len⟩
  | succ s' ih =>
    dsimp [enumVList] at hz
    rw [List.mem_append] at hz
    rcases hz with h_prev | h_step
    · obtain ⟨h_ev, h_len⟩ := ih h_prev
      have h_ev_mono : (Code.evaln (s' + 1) c_V (Encodable.encode (n, z))).isSome = true := by
        obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h_ev
        have hr_mono := Nat.Partrec.Code.evaln_mono (Nat.le_succ s') hr
        exact Option.isSome_iff_exists.mpr ⟨r, hr_mono⟩
      exact ⟨h_ev_mono, h_len.trans (Nat.le_succ s')⟩
    · rw [enumV_step_def] at h_step
      rw [List.mem_dedup, List.mem_filter] at h_step
      dsimp [firstAppearsAt] at h_step
      have h1 := (Bool.and_eq_true _ _).mp h_step.2 |>.1
      have h_and := (Bool.and_eq_true _ _).mp h1
      have h_len : z.length ≤ s' + 1 := by
        rw [List.mem_flatMap] at h_step
        obtain ⟨⟨lz, hlz_range, hlz_all⟩, _⟩ := h_step
        rw [List.mem_range] at hlz_range
        rw [mem_allStrings] at hlz_all
        omega
      exact ⟨h_and.1, h_len⟩

/-- The enumeration lists no string twice. -/
theorem enumV_list_nodup (c_V : Code) (n : ℕ) (s : ℕ) :
    (enumVList c_V n s).Nodup := by
  induction s with
  | zero =>
    dsimp [enumVList]
    rw [enumV_step_def]
    exact List.nodup_dedup _
  | succ s' ih =>
    dsimp [enumVList]
    rw [List.nodup_append]
    refine ⟨ih, ?_, ?_⟩
    · rw [enumV_step_def]
      exact List.nodup_dedup _
    · intro z hz_list z2 hz_step h_eq
      subst h_eq
      rw [enumV_step_def] at hz_step
      rw [List.mem_dedup, List.mem_filter] at hz_step
      have h_not : ((Code.evaln s' c_V (Encodable.encode (n, z))).isSome &&
          decide (z.length ≤ s')) = false := by
        have h2 := (Bool.and_eq_true _ _).mp hz_step.2 |>.2
        have h_succ_ne : s' + 1 ≠ 0 := Nat.succ_ne_zero s'
        simp only [h_succ_ne, if_false, Nat.add_sub_cancel] at h2
        cases h_b : ((Code.evaln s' c_V (Encodable.encode (n, z))).isSome && decide (z.length ≤ s'))
        · rfl
        · rw [h_b] at h2; contradiction
      obtain ⟨h_ev, h_len⟩ := enumV_list_evaln c_V n s' z hz_list
      have h_both : ((Code.evaln s' c_V (Encodable.encode (n, z))).isSome &&
          decide (z.length ≤ s')) = true := by
        have h_len_b : decide (z.length ≤ s') = true := decide_eq_true h_len
        rw [h_ev, h_len_b]
        rfl
      rw [h_both] at h_not
      contradiction

/-- The stage-`s₁` enumeration is a prefix of the stage-`s₂` enumeration for `s₁ ≤ s₂`. -/
theorem enumV_list_prefix (c_V : Code) (n : ℕ) (s1 s2 : ℕ) (h : s1 ≤ s2) :
    enumVList c_V n s1 <+: enumVList c_V n s2 := by
  induction h with
  | refl => exact List.prefix_rfl
  | step h_le ih =>
    dsimp [enumVList]
    exact ih.trans (List.prefix_append _ _)

/-- A string appearing in the stage-`s_first` layer belongs to every later enumeration. -/
theorem enumV_list_mem (c_V : Code) (n : ℕ) (s_first : ℕ) (x : BitString)
    (hx_step : x ∈ enumVStep c_V n s_first) (s_0 : ℕ) (hs : s_first ≤ s_0) :
    x ∈ enumVList c_V n s_0 := by
  have h_pre := enumV_list_prefix c_V n s_first s_0 hs
  obtain ⟨r, hr⟩ := h_pre
  rw [← hr, List.mem_append]
  left
  cases s_first with
  | zero => exact hx_step
  | succ s' =>
    dsimp [enumVList]
    rw [List.mem_append]
    right
    exact hx_step

/-- In a duplicate-free list, searching for the `k`-th entry returns the index `k`. -/
theorem findIdx_getElem_eq {α : Type*} [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup)
    (k : ℕ) (hk : k < l.length) :
    l.findIdx (fun z => z == l[k]) = k := by
  have h_inj : Function.Injective (fun (i : Fin l.length) => l[i]) :=
    List.nodup_iff_injective_getElem.mp hl
  have h_find_lt : l.findIdx (fun z => z == l[k]) < l.length := by
    rw [List.findIdx_lt_length]
    exact ⟨l[k], List.getElem_mem hk, beq_self_eq_true _⟩
  have h_eq : l[l.findIdx (fun z => z == l[k])] = l[k] := by
    have h_get := List.findIdx_getElem (w := h_find_lt) (p := fun z => z == l[k])
    simp only [beq_iff_eq] at h_get
    exact h_get
  have h_fin_eq : (⟨l.findIdx (fun z => z == l[k]), h_find_lt⟩ : Fin l.length) = ⟨k, hk⟩ :=
    h_inj h_eq
  exact Fin.mk.inj h_fin_eq

private theorem getElem?_eq_of_prefix {α : Type*} {l1 l2 : List α} (h : l1 <+: l2) (k : ℕ)
    {x1 : α} (hk : l1[k]? = some x1) : l2[k]? = some x1 := by
  obtain ⟨r, rfl⟩ := h
  rw [List.getElem?_append_left]
  · exact hk
  · exact List.getElem?_eq_some_iff.mp hk |>.1

private def checkV (c_V : Code) (p : BitString) (s : ℕ) : Option BitString :=
  (enumVList c_V p.length s)[ (allStrings p.length).findIdx (fun x => x == p) ]?

private def decompressorV (c_V : Code) : Map := fun pr =>
  (Nat.rfind (fun s => Part.some (checkV c_V pr.1 s).isSome)).bind (fun s =>
    Part.ofOption (checkV c_V pr.1 s))

private theorem findIdx_simple_computable :
    Computable (fun (p : BitString × ℕ) =>
      (allStrings p.1.length).findIdx (fun x => x == p.1)) := by
  have h1 : Primrec (fun p : BitString × ℕ => allStrings p.1.length) :=
    allStrings_primrec.comp (Primrec.list_length.comp Primrec.fst)
  have h_p : Primrec (fun (q : (BitString × ℕ) × BitString) => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have h_x : Primrec (fun (q : (BitString × ℕ) × BitString) => q.2) :=
    Primrec.snd
  obtain ⟨_, h2_prim⟩ := Primrec.eq.comp h_x h_p
  have h2 : Primrec₂ (fun (p : BitString × ℕ) (x : BitString) => decide (x = p.1)) :=
    h2_prim.of_eq (by intro ⟨⟨p, n⟩, x⟩; dsimp; congr)
  have h_find := (Primrec.list_findIdx h1 h2).to_comp
  exact h_find.of_eq (by
    intro ⟨p, n⟩
    dsimp
    congr 1
    ext x
    by_cases h : x = p <;> simp [h])

private theorem enumV_list_computable (c_V : Code) :
    Computable (fun (p : BitString × ℕ) => enumVList c_V p.1.length p.2) :=
  (enumV_list_primrec c_V).comp (Primrec.pair (Primrec.list_length.comp Primrec.fst) Primrec.snd)
    |>.to_comp

private theorem checkV_computable (c_V : Code) :
    Computable (fun (pr : (BitString × BitString) × ℕ) => checkV c_V pr.1.1 pr.2) := by
  have h_pair : Computable (fun (p : BitString × ℕ) =>
      (enumVList c_V p.1.length p.2, (allStrings p.1.length).findIdx (fun x => x == p.1))) :=
    Computable.pair (enumV_list_computable c_V) findIdx_simple_computable
  have h_get : Computable (fun (p : BitString × ℕ) => checkV c_V p.1 p.2) :=
    (Computable.comp Computable.list_getElem? h_pair).of_eq (fun p => rfl)
  have h_drop : Computable (fun (pr : (BitString × BitString) × ℕ) => (pr.1.1, pr.2)) :=
    Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
  exact (Computable.comp h_get h_drop).of_eq (fun pr => rfl)

private theorem checkV_isSome_computable (c_V : Code) :
    Computable (fun (pr : (BitString × BitString) × ℕ) => (checkV c_V pr.1.1 pr.2).isSome) :=
  Primrec.option_isSome.to_comp.comp (checkV_computable c_V)

private theorem checkV_rfind_p_partrec (c_V : Code) :
    Partrec (fun (p : (BitString × BitString) × ℕ) => Part.some (checkV c_V p.1.1 p.2).isSome) :=
  Partrec.some.comp (checkV_isSome_computable c_V)

private theorem checkV_rfind_partrec (c_V : Code) :
    Partrec (fun (pr : BitString × BitString) =>
      Nat.rfind (fun s => Part.some (checkV c_V pr.1 s).isSome)) :=
  Partrec.rfind (checkV_rfind_p_partrec c_V).to₂

private theorem checkV_ofOpt_partrec (c_V : Code) :
    Partrec (fun (p : (BitString × BitString) × ℕ) => Part.ofOption (checkV c_V p.1.1 p.2)) :=
  Computable.ofOption (checkV_computable c_V)

private theorem decompressorV_isDecompressor (c_V : Code) :
    isDecompressor (decompressorV c_V) :=
  Partrec.bind (checkV_rfind_partrec c_V) (checkV_ofOpt_partrec c_V).to₂

/-- **Theorem 7(b).** Conversely, if `V` is an enumerable family with
`|V n| < 2 ^ n`, then all elements of `V n` have complexity less than `n + O(1)`. -/
theorem plainK_lt_of_mem_of_isEnumerableFamily_of_card_lt_two_pow (U : Map)
    (hU : isOptimalConditional U)
    (V : ℕ → Set BitString) (hV : IsEnumerableFamily V)
    (hfin : ∀ n, (V n).Finite) (hcard : ∀ n, (V n).ncard < 2 ^ n) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : BitString), x ∈ V n → plainK U x < ((n + c : ℕ) : ℕ∞) := by
  obtain ⟨f_V, hf_V_partrec, hf_V_dom⟩ := hV
  obtain ⟨c_V, hc_V⟩ := Nat.Partrec.Code.exists_code.mp hf_V_partrec
  have h_decomp := decompressorV_isDecompressor c_V
  obtain ⟨c_D, hc_D⟩ := hU.2 (decompressorV c_V) h_decomp
  use c_D + 1
  intro n x hx
  have hf_dom : (f_V (n, x)).Dom := (hf_V_dom (n, x)).mpr hx
  have h_eval_mem : ∃ r, r ∈ c_V.eval (Encodable.encode (n, x)) := by
    rw [hc_V]
    dsimp only
    obtain ⟨u, hx_f⟩ := Part.dom_iff_mem.mp hf_dom
    refine ⟨Encodable.encode u, ?_⟩
    have h_dec : Encodable.decode (Encodable.encode (n, x)) = some (n, x) :=
      Encodable.encodek (n, x)
    rw [h_dec]
    dsimp [Part.ofOption]
    rw [Part.bind_some]
    rw [Part.mem_map_iff]
    exact ⟨u, hx_f, rfl⟩
  obtain ⟨r_x, hr_x⟩ := h_eval_mem
  obtain ⟨s_x, hs_x⟩ := Nat.Partrec.Code.evaln_complete.mp hr_x
  let s_start := max s_x x.length
  have hs0_x : s_x ≤ s_start := le_max_left _ _
  have hs0_eval : (Code.evaln s_start c_V (Encodable.encode (n, x))).isSome = true := by
    have hr_s0 := Nat.Partrec.Code.evaln_mono hs0_x hs_x
    exact Option.isSome_iff_exists.mpr ⟨r_x, hr_s0⟩
  have hs0_len : x.length ≤ s_start := le_max_right _ _
  obtain ⟨s_first, hs_first_le, hs_first_halt, hs_first_spec, hs_first_len⟩ :=
    firstAppearsAt_spec c_V n x s_start hs0_eval hs0_len
  have h_in_step : x ∈ enumVStep c_V n s_first :=
    enumV_step_mem c_V n s_first x hs_first_halt hs_first_spec hs_first_len
  have h_in_enum : x ∈ enumVList c_V n s_start :=
    enumV_list_mem c_V n s_first x h_in_step s_start hs_first_le
  have h_enum_sub : ∀ z ∈ enumVList c_V n s_start, z ∈ V n :=
    enumV_list_sub V c_V f_V hc_V hf_V_dom n s_start
  have h_nodup : (enumVList c_V n s_start).Nodup := enumV_list_nodup c_V n s_start
  let k := (enumVList c_V n s_start).findIdx (fun z => z == x)
  have h_k_lt_card : k < (enumVList c_V n s_start).length := by
    dsimp [k]
    rw [List.findIdx_lt_length]
    exact ⟨x, h_in_enum, beq_self_eq_true x⟩
  have hk_lt : k < 2 ^ n := by
    have h_subset : (enumVList c_V n s_start).toFinset ⊆ (hfin n).toFinset := by
      intro z hz
      rw [List.mem_toFinset] at hz
      rw [Set.Finite.mem_toFinset (hfin n)]
      exact h_enum_sub z hz
    have h_le := Finset.card_le_card h_subset
    rw [List.toFinset_card_of_nodup h_nodup] at h_le
    have h_card_eq : (hfin n).toFinset.card = (V n).ncard :=
      (Set.ncard_eq_toFinset_card (V n) (hfin n)).symm
    rw [h_card_eq] at h_le
    have h_lt1 := hcard n
    dsimp [k] at h_k_lt_card ⊢
    omega
  have h_k_lt_all : k < (allStrings n).length := by
    rw [length_allStrings]
    exact hk_lt
  let p := (allStrings n)[k]'h_k_lt_all
  have hp_len : p.length = n := by
    dsimp [p]
    rw [← mem_allStrings]
    exact List.getElem_mem h_k_lt_all
  have hp_find : (allStrings p.length).findIdx (fun z => z == p) = k := by
    have hp_eq : p.length = n := hp_len
    have h_find_n : (allStrings n).findIdx (fun z => z == (allStrings n)[k]) = k :=
      findIdx_getElem_eq (allStrings_nodup n) k h_k_lt_all
    change List.findIdx (fun z => z == p) (allStrings p.length) = k
    have h_p_def : p = (allStrings n)[k] := rfl
    rw [hp_eq, h_p_def]
    exact h_find_n
  have h_idx_eq : (allStrings n).findIdx (fun x_1 => x_1 == p) = k := by
    have h_find_n := findIdx_getElem_eq (allStrings_nodup n) k h_k_lt_all
    exact h_find_n
  have h_check_s0 : checkV c_V p s_start = some x := by
    dsimp [checkV]
    rw [hp_len, h_idx_eq, List.getElem?_eq_getElem h_k_lt_card]
    have h_get_x := List.findIdx_getElem (w := h_k_lt_card) (p := fun z => z == x)
      (xs := enumVList c_V n s_start)
    simp only [beq_iff_eq] at h_get_x
    congr
  have h_rfind_dom : (Nat.rfind (fun s => Part.some (checkV c_V p s).isSome)).Dom := by
    let p_pred : ℕ →. Bool := fun s => Part.some (checkV c_V p s).isSome
    have h : (Nat.rfind p_pred).Dom := by
      rw [Nat.rfind_dom]
      refine ⟨s_start, ?_, fun _ => Part.some_dom _⟩
      rw [Part.mem_some_iff, h_check_s0]
      rfl
    exact h
  obtain ⟨s_find, hs_find⟩ := Part.dom_iff_mem.mp h_rfind_dom
  have hs_find_spec := Nat.mem_rfind.mp hs_find
  have hs_find_isSome : (checkV c_V p s_find).isSome = true := by
    have h1 := hs_find_spec.1
    simp only [Part.mem_some_iff] at h1
    exact h1.symm
  obtain ⟨x_find, hx_find⟩ := Option.isSome_iff_exists.mp hs_find_isSome
  have hs_find_le : s_find ≤ s_start := by
    by_contra h_gt
    rw [not_le] at h_gt
    have h_spec_find := hs_find_spec.2 (m := s_start) h_gt
    simp only [Part.mem_some_iff] at h_spec_find
    have h_check_s0_isSome : (checkV c_V p s_start).isSome = true := by
      rw [h_check_s0]
      rfl
    rw [h_check_s0_isSome] at h_spec_find
    contradiction
  have h_prefix := enumV_list_prefix c_V n s_find s_start hs_find_le
  have h_check_sfind : checkV c_V p s_find = some x_find := hx_find
  have h_getElem?_sfind : (enumVList c_V n s_find)[k]? = some x_find := by
    dsimp [checkV] at h_check_sfind
    rw [hp_len, h_idx_eq] at h_check_sfind
    exact h_check_sfind
  have h_getElem?_s0 : (enumVList c_V n s_start)[k]? = some x_find :=
    getElem?_eq_of_prefix h_prefix k h_getElem?_sfind
  have h_check_s0_get : (enumVList c_V n s_start)[k]? = some x := by
    dsimp [checkV] at h_check_s0
    rw [hp_len, h_idx_eq] at h_check_s0
    exact h_check_s0
  have hx_find_eq : x_find = x := by
    rw [h_check_s0_get] at h_getElem?_s0
    exact Option.some_injective _ h_getElem?_s0.symm
  cases hx_find_eq
  have h_decomp_mem : x ∈ decompressorV c_V (p, []) := by
    dsimp [decompressorV]
    simp only [Part.mem_bind_iff]
    refine ⟨s_find, hs_find, ?_⟩
    rw [h_check_sfind]
    exact Part.mem_some _
  have h_le_D : condK (decompressorV c_V) x [] ≤ (p.length : ℕ∞) := by
    rw [condK_le_iff]
    exact ⟨p, le_rfl, h_decomp_mem⟩
  have h_opt := hc_D x []
  dsimp [plainK]
  have h1 : condK U x [] ≤ (n : ℕ∞) + (c_D : ℕ∞) := by
    calc condK U x []
      _ ≤ condK (decompressorV c_V) x [] + (c_D : ℕ∞) := h_opt
      _ ≤ (p.length : ℕ∞) + (c_D : ℕ∞) := add_le_add_left h_le_D (c_D : ℕ∞)
      _ = (n : ℕ∞) + (c_D : ℕ∞) := by rw [hp_len]
  have h2 : (n : ℕ∞) + (c_D : ℕ∞) = ((n + c_D : ℕ) : ℕ∞) := by push_cast; rfl
  have h3 : ((n + c_D : ℕ) : ℕ∞) < ((n + (c_D + 1) : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self (n + c_D)
  rw [h2] at h1
  exact lt_of_le_of_lt h1 h3

/-- Stage-`s` pool of level `m`: the first `2 ^ (m + 1)` strings enumerated into
`{x | k x < m + c₁ + 1}`. -/
def pBlock (c_k : Code) (c₁ : ℕ) (m s : ℕ) : List BitString :=
  (enumVList c_k (m + c₁ + 1) s).take (2 ^ (m + 1))

/-- The strings allocated to the levels `< m` at stage `s`. -/
def qUsed (c_k : Code) (c₁ : ℕ) : ℕ → ℕ → List BitString
  | 0, _ => []
  | m + 1, s =>
      qUsed c_k c₁ m s ++
        ((pBlock c_k c₁ m s).filter (fun z => decide (z ∉ qUsed c_k c₁ m s))).take (2 ^ m)

/-- The block of (at most) `2 ^ m` strings allocated to level `m` at stage `s`. -/
def qBlock (c_k : Code) (c₁ : ℕ) (m s : ℕ) : List BitString :=
  ((pBlock c_k c₁ m s).filter (fun z => decide (z ∉ qUsed c_k c₁ m s))).take (2 ^ m)

/-- All pools up to level `m` are full at stage `s`. -/
def qStage (c_k : Code) (c₁ : ℕ) (m s : ℕ) : Bool :=
  decide (((List.range (m + 1)).filter
    (fun m' => decide ((enumVList c_k (m' + c₁ + 1) s).length < 2 ^ (m' + 1)))).length = 0)

/-- The stage-`s` pool of level `m` is primitive recursive in `(m, s)`. -/
lemma pBlock_primrec (c_k : Code) (c₁ : ℕ) :
    Primrec (fun (p : ℕ × ℕ) => pBlock c_k c₁ p.1 p.2) := by
  have h_lvl : Primrec (fun (p : ℕ × ℕ) => p.1 + c₁ + 1) :=
    Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const c₁))
  have h_list : Primrec (fun (p : ℕ × ℕ) => enumVList c_k (p.1 + c₁ + 1) p.2) :=
    (enumV_list_primrec c_k).comp (Primrec.pair h_lvl Primrec.snd)
  have h_pow : Primrec (fun (p : ℕ × ℕ) => 2 ^ (p.1 + 1)) :=
    primrec_two_pow_aux.comp (Primrec.succ.comp Primrec.fst)
  exact Primrec₂.comp (f := fun (n : ℕ) (l : List BitString) => l.take n)
    Primrec.list_take h_pow h_list

end Kolmogorov
