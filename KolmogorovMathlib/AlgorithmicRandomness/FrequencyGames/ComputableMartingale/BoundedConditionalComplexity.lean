/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.RandomnessBasics

/-!
# Bounded Conditional Complexity

For a total computable non-decreasing unbounded function `f`, there is a computably random
sequence whose prefixes `ω_0 … ω_{n-1}` have conditional complexity given `n` at most `f n + O(1)`
(Problem 268 of Shen, Uspensky and Vereshchagin, "Kolmogorov complexity and algorithmic
randomness").  The main declaration is `exists_isComputablyRandom_condK_le`; the construction
(true mask, threshold schedule, greedy potential, decoder) is carried out in private
declarations that come first.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology ComputableReals

/-! ### Private copy of the development of `exists_isComputablyRandom_condK_le_forall`

`exists_isComputablyRandom_condK_le_forall` (further below) is the uniform-in-`f` version of
Problem 268 and is proved by an auxiliary development that is declared after the theorem below, so
the theorem below cannot use it.  The development is therefore repeated verbatim, as private
declarations named `exists_isComputablyRandom_condK_le_dup_*`, and the theorem below is its
specialisation to the given `f`.  See the comment before `exists_isComputablyRandom_condK_le_forall`
for the construction (true mask, `θ`-schedule, greedy potential, decoder). -/

open Classical in
/-- The value at `j` of the `e`-th partial recursive function, `0` if it is undefined. -/
private noncomputable def exists_isComputablyRandom_condK_le_dup_ph (e j : ℕ) : ℕ :=
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) j).getOrElse 0

/-- The rational coded by the value `ph e (encode x)` (`0` if the value is not a code of a
rational). -/
private def exists_isComputablyRandom_condK_le_dup_evOf (ph : ℕ → ℕ → ℕ) (e : ℕ)
    (x : BitString) : ℚ :=
  (Encodable.decode (α := ℚ) (ph e (Encodable.encode x))).getD 0

/-- The `e`-th partial recursive function is total. -/
private def exists_isComputablyRandom_condK_le_dup_tot (e : ℕ) : Prop :=
  ∀ j, (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) j).Dom

open Classical in
/-- The true mask: bit `2e` says that the `e`-th partial recursive function is total, bit `2e+1`
that it is total and codes (through `evOf`) a fair capital for the uniform measure. -/
private noncomputable def exists_isComputablyRandom_condK_le_dup_mask (i : ℕ) : Bool :=
  if i % 2 = 0 then decide (exists_isComputablyRandom_condK_le_dup_tot (i / 2))
  else decide (exists_isComputablyRandom_condK_le_dup_tot (i / 2) ∧
    IsFairCapital uniformMeasure (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf
      exists_isComputablyRandom_condK_le_dup_ph (i / 2) x : ℚ) : ℝ)))

/-- `θ j = j + max { ph e j' | j' ≤ j, e < j', a (2e) }`: the stage at which the index `j` becomes
active.  It is strictly increasing and `j ≤ θ j`. -/
private def exists_isComputablyRandom_condK_le_dup_theta (a : ℕ → Bool) (ph : ℕ → ℕ → ℕ)
    (j : ℕ) : ℕ :=
  j + (Finset.range (j + 1)).sup (fun j' => (Finset.range j').sup
    (fun e => if a (2 * e) = true then ph e j' else 0))

/-- A natural number `k` with `1 + q ≤ 2^k` for every rational `q ≥ 0`. -/
private def exists_isComputablyRandom_condK_le_dup_shift (q : ℚ) : ℕ := Nat.size q.num.toNat

/-- The potential at stage `m` of the string `x`: the weighted sum, over the indices `e < c` that
are
active at stage `m` (`θ e ≤ m`) and flagged as capitals (`a (2e+1)`), of the capital `ev e x`, with
the weight `2^{-e}` normalised by the value of the capital at the activation prefix of `x`. -/
private def exists_isComputablyRandom_condK_le_dup_pot (a : ℕ → Bool) (ph : ℕ → ℕ → ℕ)
    (c m : ℕ) (x : BitString) : ℚ :=
  ∑ e ∈ (Finset.range c).filter (fun e =>
      exists_isComputablyRandom_condK_le_dup_theta a ph e ≤ m ∧ a (2 * e + 1) = true),
    (1 / 2 : ℚ) ^ (e + exists_isComputablyRandom_condK_le_dup_shift
        (exists_isComputablyRandom_condK_le_dup_evOf ph e
          (x.take (exists_isComputablyRandom_condK_le_dup_theta a ph e)))) *
      exists_isComputablyRandom_condK_le_dup_evOf ph e x

/-- The greedy bit: after the prefix `x` of length `m`, append the bit with the smaller stage `m+1`
potential (`false` on ties); the potential at stage `m+1` is taken over the indices `< cut (m+1)`.
-/
private def exists_isComputablyRandom_condK_le_dup_next (a : ℕ → Bool) (ph : ℕ → ℕ → ℕ)
    (cut : ℕ → ℕ) (m : ℕ) (x : BitString) : Bool :=
  decide (exists_isComputablyRandom_condK_le_dup_pot a ph (cut (m + 1)) (m + 1) (x ++ [true]) <
    exists_isComputablyRandom_condK_le_dup_pot a ph (cut (m + 1)) (m + 1) (x ++ [false]))

/-- The greedy prefix of length `m`. -/
private def exists_isComputablyRandom_condK_le_dup_run (a : ℕ → Bool) (ph : ℕ → ℕ → ℕ)
    (cut : ℕ → ℕ) : ℕ → BitString
  | 0 => []
  | m + 1 =>
    exists_isComputablyRandom_condK_le_dup_run a ph cut m ++
      [exists_isComputablyRandom_condK_le_dup_next a ph cut m
        (exists_isComputablyRandom_condK_le_dup_run a ph cut m)]

/-- The greedy sequence (the potential at stage `m` is taken over the indices `≤ m`, which is all
the active ones as `j ≤ θ j`). -/
private def exists_isComputablyRandom_condK_le_dup_seq (a : ℕ → Bool) (ph : ℕ → ℕ → ℕ) :
    CantorSeq := fun n =>
  exists_isComputablyRandom_condK_le_dup_next a ph (fun m => m + 1) n
    (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n)

/-- `K(n) = #{ j | θ j ≤ n }`, for the true mask. -/
private noncomputable def exists_isComputablyRandom_condK_le_dup_K (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun j =>
    exists_isComputablyRandom_condK_le_dup_theta exists_isComputablyRandom_condK_le_dup_mask
      exists_isComputablyRandom_condK_le_dup_ph j ≤ n)).card

/-- The advice for the length `n`: the first `2 K(n)` bits of the true mask. -/
private noncomputable def exists_isComputablyRandom_condK_le_dup_adv (n : ℕ) : BitString :=
  (List.range (2 * exists_isComputablyRandom_condK_le_dup_K n)).map
    exists_isComputablyRandom_condK_le_dup_mask

/-- The `s`-step approximation of `ph`. -/
private def exists_isComputablyRandom_condK_le_dup_phS (s e j : ℕ) : ℕ :=
  (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e) j).getD 0

/-- All bit strings of length at most `n`. -/
private def exists_isComputablyRandom_condK_le_dup_strings : ℕ → List BitString
  | 0 => [[]]
  | n + 1 => [] :: ((exists_isComputablyRandom_condK_le_dup_strings n).flatMap
      (fun x => [false :: x, true :: x]))

/-- The `s`-step computations needed by the simulation with advice `p` up to length `n` have all
halted. -/
private def exists_isComputablyRandom_condK_le_dup_good (s : ℕ) (p : BitString) (n : ℕ) : Bool :=
  (List.range (p.length / 2)).all (fun e =>
    (!(p.getD (2 * e) false) || (List.range (p.length / 2)).all (fun j =>
      (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e) j).isSome)) &&
    (!(p.getD (2 * e + 1) false) ||
      (exists_isComputablyRandom_condK_le_dup_strings n).all (fun x =>
        (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
          (Encodable.encode x)).isSome)))

/-- The simulation with `s` steps: from the advice `p` (its flags are `p.getD i false`, it covers
the
`p.length / 2` first indices) compute the greedy prefix of length `n`, if all the needed `s`-step
computations have halted. -/
private def exists_isComputablyRandom_condK_le_dup_sim (s : ℕ) (p : BitString) (n : ℕ) :
    Option BitString :=
  if exists_isComputablyRandom_condK_le_dup_good s p n = true then
    some (exists_isComputablyRandom_condK_le_dup_run (fun i => p.getD i false)
      (exists_isComputablyRandom_condK_le_dup_phS s) (fun m => min (p.length / 2) (m + 1)) n)
  else none

/-- Step 0 of the proof of `exists_isComputablyRandom_condK_le_dup`: the prefixes of the
greedy sequence are the greedy prefixes. -/
private lemma exists_isComputablyRandom_condK_le_dup_prefix (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (n : ℕ) :
    cantorPrefix (exists_isComputablyRandom_condK_le_dup_seq a ph) n =
      exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n := by
  induction n with
  | zero => simp [cantorPrefix, exists_isComputablyRandom_condK_le_dup_run]
  | succ n ih =>
    rw [cantorPrefix_succ, ih]
    rfl

/-- `θ` is strictly increasing: one step. -/
private lemma exists_isComputablyRandom_condK_le_dup_F1aux_theta_lt_succ (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (j : ℕ) :
    exists_isComputablyRandom_condK_le_dup_theta a ph j <
      exists_isComputablyRandom_condK_le_dup_theta a ph (j + 1) := by
  unfold exists_isComputablyRandom_condK_le_dup_theta
  have h : (Finset.range (j + 1)).sup (fun j' => (Finset.range j').sup
      (fun e => if a (2 * e) = true then ph e j' else 0)) ≤
      (Finset.range (j + 1 + 1)).sup (fun j' => (Finset.range j').sup
      (fun e => if a (2 * e) = true then ph e j' else 0)) :=
    Finset.sup_mono (Finset.range_mono (Nat.le_succ _))
  omega

/-- `θ` is strictly increasing. -/
private lemma exists_isComputablyRandom_condK_le_dup_F1aux_theta_strictMono (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) :
    StrictMono (exists_isComputablyRandom_condK_le_dup_theta a ph) :=
  strictMono_nat_of_lt_succ (exists_isComputablyRandom_condK_le_dup_F1aux_theta_lt_succ a ph)

/-- `θ j` dominates the flagged values `ph e j`, `e < j`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F1aux_ph_le_theta (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) {e j : ℕ} (hej : e < j) (he : a (2 * e) = true) :
    ph e j ≤ exists_isComputablyRandom_condK_le_dup_theta a ph j := by
  unfold exists_isComputablyRandom_condK_le_dup_theta
  have h1 : (Finset.range j).sup (fun e => if a (2 * e) = true then ph e j else 0) ≤
      (Finset.range (j + 1)).sup (fun j' => (Finset.range j').sup
        (fun e => if a (2 * e) = true then ph e j' else 0)) :=
    Finset.le_sup (f := fun j' => (Finset.range j').sup
        (fun e => if a (2 * e) = true then ph e j' else 0)) (Finset.self_mem_range_succ j)
  have h2 : (if a (2 * e) = true then ph e j else 0) ≤
      (Finset.range j).sup (fun e => if a (2 * e) = true then ph e j else 0) :=
    Finset.le_sup (f := fun e => if a (2 * e) = true then ph e j else 0) (Finset.mem_range.mpr hej)
  have h3 : (if a (2 * e) = true then ph e j else 0) = ph e j := by simp [he]
  rw [h3] at h2
  omega

/-- The least `n` with `j + 1 ≤ f n` is a computable function of `j`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F1aux_computable_find {f : ℕ → ℕ}
    (hf : Computable f) (hunb : ∀ B, ∃ n, B ≤ f n) :
    Computable (fun j => Nat.find (hunb (j + 1))) := by
  have hP : Computable (fun p : ℕ × ℕ => decide ((fun j n => j + 1 ≤ f n) p.1 p.2)) := by
    have h1 : Computable (fun p : ℕ × ℕ => p.1 + 1) :=
      Primrec.succ.to_comp.comp Computable.fst
    have h2 : Computable (fun p : ℕ × ℕ => f p.2) := hf.comp Computable.snd
    exact (PrimrecRel.decide Primrec.nat_le).to_comp.comp h1 h2
  exact Computable.natFind (P := fun j n => j + 1 ≤ f n) hP (fun j => hunb (j + 1))

/-- Step 1 of the proof of `exists_isComputablyRandom_condK_le_dup`: the schedule.  If the
bit sequence `a` flags, for every computable `g`, an index `e` computing `g` through `ph`, then
`#{ j ≤ n | θ j ≤ n } ≤ f n + c` for every computable monotone unbounded `f`. -/
private lemma exists_isComputablyRandom_condK_le_dup_schedule (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ)
    (hdom : ∀ g : ℕ → ℕ, Computable g → ∃ e, a (2 * e) = true ∧ ∀ j, ph e j = g j)
    {f : ℕ → ℕ} (hf : Computable f) (hmono : Monotone f) (hunb : ∀ B, ∃ n, B ≤ f n) :
    ∃ c : ℕ, ∀ n : ℕ, ((Finset.range (n + 1)).filter (fun j =>
      exists_isComputablyRandom_condK_le_dup_theta a ph j ≤ n)).card ≤ f n + c := by
  have hg : Computable (fun j => Nat.find (hunb (j + 1))) :=
    exists_isComputablyRandom_condK_le_dup_F1aux_computable_find hf hunb
  obtain ⟨e, he, hph⟩ := hdom (fun j => Nat.find (hunb (j + 1))) hg
  refine ⟨e + 1, fun n => ?_⟩
  have hmono_theta := exists_isComputablyRandom_condK_le_dup_F1aux_theta_strictMono a ph
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 = max (e + 1) (f n) := ⟨_, rfl⟩
  have hj1 : e + 1 ≤ j0 := by rw [hj0]; exact le_max_left _ _
  have hj2 : f n ≤ j0 := by rw [hj0]; exact le_max_right _ _
  have hj3 : j0 ≤ f n + (e + 1) := by rw [hj0]; exact max_le (by omega) (by omega)
  have hlt : n < exists_isComputablyRandom_condK_le_dup_theta a ph j0 := by
    have h1 := exists_isComputablyRandom_condK_le_dup_F1aux_ph_le_theta a ph
      (show e < j0 by omega) he
    rw [hph j0] at h1
    have h2 : n < Nat.find (hunb (j0 + 1)) := by
      by_contra hcon
      have hcon' : Nat.find (hunb (j0 + 1)) ≤ n := not_lt.mp hcon
      have hspec : j0 + 1 ≤ f (Nat.find (hunb (j0 + 1))) := Nat.find_spec (hunb (j0 + 1))
      have hm := hmono hcon'
      omega
    omega
  have hsub : (Finset.range (n + 1)).filter (fun j =>
      exists_isComputablyRandom_condK_le_dup_theta a ph j ≤ n) ⊆ Finset.range j0 := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_range]
    by_contra hcon
    have hcon' : j0 ≤ j := not_lt.mp hcon
    have := hmono_theta.monotone hcon'
    omega
  calc ((Finset.range (n + 1)).filter (fun j =>
      exists_isComputablyRandom_condK_le_dup_theta a ph j ≤ n)).card
      ≤ (Finset.range j0).card := Finset.card_le_card hsub
    _ = j0 := Finset.card_range _
    _ ≤ f n + (e + 1) := hj3

private lemma exists_isComputablyRandom_condK_le_dup_F2aux_tot_ph (F : ℕ → ℕ)
    (hF : Computable F) :
    ∃ e : ℕ, exists_isComputablyRandom_condK_le_dup_tot e ∧
      ∀ j, exists_isComputablyRandom_condK_le_dup_ph e j = F j := by
  have h1 : Partrec (fun n : ℕ => (F n : Part ℕ)) := hF.partrec
  have h2 : Nat.Partrec (fun n : ℕ => (F n : Part ℕ)) := Partrec.nat_iff.mp h1
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp h2
  have he : ∀ j, Nat.Partrec.Code.eval
      (Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)) j = Part.some (F j) := by
    intro j
    rw [Denumerable.ofNat_encode, hc]
    rfl
  refine ⟨Encodable.encode c, fun j => ?_, fun j => ?_⟩
  · rw [he j]
    exact Part.some_dom _
  · have hd : (Nat.Partrec.Code.eval
        (Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)) j).Dom := by
      rw [he j]
      exact Part.some_dom _
    have hmem : F j ∈ Nat.Partrec.Code.eval
        (Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)) j := by
      rw [he j]
      exact Part.mem_some _
    unfold exists_isComputablyRandom_condK_le_dup_ph
    unfold Part.getOrElse
    rw [dite_eq_left hd]
    exact Part.get_eq_of_mem hmem hd

/-- The even bits of the true mask. -/
private lemma exists_isComputablyRandom_condK_le_dup_F2aux_mask_even (e : ℕ) :
    exists_isComputablyRandom_condK_le_dup_mask (2 * e) = true ↔
      exists_isComputablyRandom_condK_le_dup_tot e := by
  classical
  unfold exists_isComputablyRandom_condK_le_dup_mask
  have h1 : (2 * e) % 2 = 0 := by omega
  have h2 : (2 * e) / 2 = e := by omega
  rw [ite_eq_left h1, h2]
  exact decide_eq_true_iff

/-- The odd bits of the true mask. -/
private lemma exists_isComputablyRandom_condK_le_dup_F2aux_mask_odd (e : ℕ) :
    exists_isComputablyRandom_condK_le_dup_mask (2 * e + 1) = true ↔
      (exists_isComputablyRandom_condK_le_dup_tot e ∧
        IsFairCapital uniformMeasure (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf
          exists_isComputablyRandom_condK_le_dup_ph e x : ℚ) : ℝ))) := by
  classical
  unfold exists_isComputablyRandom_condK_le_dup_mask
  have h1 : ¬ ((2 * e + 1) % 2 = 0) := by omega
  have h2 : (2 * e + 1) / 2 = e := by omega
  rw [ite_eq_right h1, h2]
  exact decide_eq_true_iff

/-- Step 2a of the proof of `exists_isComputablyRandom_condK_le_dup`: every computable
function is computed by an index flagged in the true mask. -/
private lemma exists_isComputablyRandom_condK_le_dup_cover_dom (g : ℕ → ℕ)
    (hg : Computable g) :
    ∃ e, exists_isComputablyRandom_condK_le_dup_mask (2 * e) = true ∧
      ∀ j, exists_isComputablyRandom_condK_le_dup_ph e j = g j := by
  obtain ⟨e, he1, he2⟩ := exists_isComputablyRandom_condK_le_dup_F2aux_tot_ph g hg
  exact ⟨e, (exists_isComputablyRandom_condK_le_dup_F2aux_mask_even e).mpr he1, he2⟩

/-- Step 2b of the proof of `exists_isComputablyRandom_condK_le_dup`: every computable
rational fair capital is coded by an index flagged as a capital in the true mask. -/
private lemma exists_isComputablyRandom_condK_le_dup_cover_mart (m : BitString → ℚ)
    (hm : Computable m) (hfair : IsFairCapital uniformMeasure (fun x => (m x : ℝ))) :
    ∃ e, exists_isComputablyRandom_condK_le_dup_mask (2 * e + 1) = true ∧
      ∀ x, exists_isComputablyRandom_condK_le_dup_evOf
        exists_isComputablyRandom_condK_le_dup_ph e x = m x := by
  classical
  set F : ℕ → ℕ := fun n =>
    ((Encodable.decode (α := BitString) n).map (fun x => Encodable.encode (m x))).getD 0
    with hFdef
  have hF : Computable F := by
    refine Computable.option_getD (Computable.option_map
      (Computable.decode : Computable (fun n : ℕ => Encodable.decode (α := BitString) n)) ?_)
      (Computable.const 0)
    have hsnd : Computable (fun p : ℕ × BitString => p.2) := Computable.snd
    have hm2 : Computable (fun p : ℕ × BitString => m p.2) := hm.comp hsnd
    -- `Encodable.encode` on `ℚ` is the structural code (`Rat.instEncodable`), not the one of
    -- `Primcodable ℚ`
    have hrat : Computable (fun q : ℚ => @Encodable.encode ℚ Rat.instEncodable q) :=
      ComputableReals.primrec_ratCode.to_comp
    change Computable (fun p : ℕ × BitString => @Encodable.encode ℚ Rat.instEncodable (m p.2))
    exact hrat.comp hm2
  have hFenc : ∀ x : BitString, F (Encodable.encode x) = Encodable.encode (m x) := by
    intro x
    simp [hFdef, Encodable.encodek]
  obtain ⟨e, he1, he2⟩ := exists_isComputablyRandom_condK_le_dup_F2aux_tot_ph F hF
  have hev : ∀ x, exists_isComputablyRandom_condK_le_dup_evOf
      exists_isComputablyRandom_condK_le_dup_ph e x = m x := by
    intro x
    unfold exists_isComputablyRandom_condK_le_dup_evOf
    rw [he2, hFenc, Encodable.encodek]
    rfl
  refine ⟨e, ?_, hev⟩
  rw [exists_isComputablyRandom_condK_le_dup_F2aux_mask_odd]
  refine ⟨he1, ?_⟩
  have hfun : (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf
      exists_isComputablyRandom_condK_le_dup_ph e x : ℚ) : ℝ)) = fun x => (m x : ℝ) := by
    funext x
    rw [hev x]
  rw [hfun]
  exact hfair

/-- The meaning of the flags of the true mask. -/
private lemma exists_isComputablyRandom_condK_le_dup_mask_spec (e : ℕ) :
    (exists_isComputablyRandom_condK_le_dup_mask (2 * e) = true →
      exists_isComputablyRandom_condK_le_dup_tot e) ∧
    (exists_isComputablyRandom_condK_le_dup_mask (2 * e + 1) = true →
      exists_isComputablyRandom_condK_le_dup_tot e ∧
      IsFairCapital uniformMeasure (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf
        exists_isComputablyRandom_condK_le_dup_ph e x : ℚ) : ℝ))) := by
  exact ⟨(exists_isComputablyRandom_condK_le_dup_F2aux_mask_even e).mp,
    (exists_isComputablyRandom_condK_le_dup_F2aux_mask_odd e).mp⟩

/-- (F3 aux) `j ≤ θ j`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_le_theta (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (j : ℕ) :
    j ≤ exists_isComputablyRandom_condK_le_dup_theta a ph j := by
  unfold exists_isComputablyRandom_condK_le_dup_theta
  exact Nat.le_add_right _ _

/-- (F3 aux) The greedy prefix of length `m` has length `m`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_length_run (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (cut : ℕ → ℕ) (m : ℕ) :
    (exists_isComputablyRandom_condK_le_dup_run a ph cut m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [exists_isComputablyRandom_condK_le_dup_run, List.length_append, ih,
      List.length_singleton]

/-- (F3 aux) The greedy prefixes are nested. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_take_run (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (cut : ℕ → ℕ) (k m : ℕ) (hkm : k ≤ m) :
    (exists_isComputablyRandom_condK_le_dup_run a ph cut m).take k =
      exists_isComputablyRandom_condK_le_dup_run a ph cut k := by
  induction m with
  | zero =>
    have : k = 0 := Nat.le_zero.mp hkm
    subst this
    rfl
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hk | hk
    · have hk' : k ≤ m := Nat.lt_succ_iff.mp hk
      simp only [exists_isComputablyRandom_condK_le_dup_run]
      rw [List.take_append_of_le_length
        (by rw [exists_isComputablyRandom_condK_le_dup_F3aux_length_run]; exact hk')]
      exact ih hk'
    · have hk2 : k = m + 1 := le_antisymm hkm hk
      subst hk2
      apply List.take_of_length_le
      rw [exists_isComputablyRandom_condK_le_dup_F3aux_length_run]

/-- (F3 aux) A rational fair capital for the uniform measure is non-negative and the average of its
two children. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_fair_rat {q : BitString → ℚ}
    (h : IsFairCapital uniformMeasure (fun x => ((q x : ℚ) : ℝ))) :
    (∀ x, 0 ≤ q x) ∧ ∀ x, q x = (q (x ++ [false]) + q (x ++ [true])) / 2 := by
  obtain ⟨h1, h2⟩ := (isFairCapital_uniform_iff _).mp h
  refine ⟨fun x => ?_, fun x => ?_⟩
  · exact_mod_cast h1 x
  · have := h2 x
    exact_mod_cast this

/-- (F3 aux) `q ≤ 2 ^ shift q` for `q ≥ 0`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_shift_bound (q : ℚ) (hq : 0 ≤ q) :
    q ≤ (2 : ℚ) ^ exists_isComputablyRandom_condK_le_dup_shift q := by
  unfold exists_isComputablyRandom_condK_le_dup_shift
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have h1 : q ≤ (q.num : ℚ) := by
    have hden : (1 : ℚ) ≤ q.den := by exact_mod_cast Rat.den_pos q
    calc q = q * 1 := by ring
      _ ≤ q * q.den := mul_le_mul_of_nonneg_left hden hq
      _ = q.num := Rat.mul_den_eq_num q
  have h2 : (q.num : ℚ) = ((q.num.toNat : ℕ) : ℚ) := by
    have : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum
    exact_mod_cast this.symm
  have h3 : q.num.toNat < 2 ^ Nat.size q.num.toNat := Nat.lt_size_self _
  calc q ≤ q.num := h1
    _ = ((q.num.toNat : ℕ) : ℚ) := h2
    _ ≤ (2 : ℚ) ^ Nat.size q.num.toNat := by exact_mod_cast h3.le

/-- (F3 aux) The activation bound: `2^{-(e + shift q)} q ≤ 2^{-e}` for `q ≥ 0`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_term_le (e : ℕ) (q : ℚ)
    (hq : 0 ≤ q) :
    (1 / 2 : ℚ) ^ (e + exists_isComputablyRandom_condK_le_dup_shift q) * q ≤ (1 / 2) ^ e := by
  have h := exists_isComputablyRandom_condK_le_dup_F3aux_shift_bound q hq
  set k := exists_isComputablyRandom_condK_le_dup_shift q with hk
  calc (1 / 2 : ℚ) ^ (e + k) * q ≤ (1 / 2 : ℚ) ^ (e + k) * 2 ^ k :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (1 / 2) ^ e := by
        rw [pow_add, mul_assoc, ← mul_pow]
        norm_num

/-- (F3 aux) The sum of the weights `2^{-e}` over any finite set is at most `2`... on `range n`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_geom (n : ℕ) :
    ∑ e ∈ Finset.range n, (1 / 2 : ℚ) ^ e = 2 - 2 * (1 / 2) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- (F3 aux) The term of the potential belonging to the index `e` at the string `y`. -/
private def exists_isComputablyRandom_condK_le_dup_F3aux_term (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (e : ℕ) (y : BitString) : ℚ :=
  (1 / 2 : ℚ) ^ (e + exists_isComputablyRandom_condK_le_dup_shift
      (exists_isComputablyRandom_condK_le_dup_evOf ph e
        (y.take (exists_isComputablyRandom_condK_le_dup_theta a ph e)))) *
    exists_isComputablyRandom_condK_le_dup_evOf ph e y

/-- (F3 aux) The indices active at stage `m` and flagged as capitals. -/
private def exists_isComputablyRandom_condK_le_dup_F3aux_act (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter (fun e =>
    exists_isComputablyRandom_condK_le_dup_theta a ph e ≤ m ∧ a (2 * e + 1) = true)

/-- (F3 aux) The indices that become active exactly at stage `m` and are flagged as capitals. -/
private def exists_isComputablyRandom_condK_le_dup_F3aux_new (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter (fun e =>
    exists_isComputablyRandom_condK_le_dup_theta a ph e = m ∧ a (2 * e + 1) = true)

/-- (F3 aux) The potential at stage `m` with the cut-off `m + 1` is the sum over the active set. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_pot_eq (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (m : ℕ) (y : BitString) :
    exists_isComputablyRandom_condK_le_dup_pot a ph (m + 1) m y =
      ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m,
        exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e y := rfl

/-- (F3 aux) Membership in the active set. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_mem_act (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (m e : ℕ) :
    e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m ↔
      exists_isComputablyRandom_condK_le_dup_theta a ph e ≤ m ∧ a (2 * e + 1) = true := by
  unfold exists_isComputablyRandom_condK_le_dup_F3aux_act
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have := exists_isComputablyRandom_condK_le_dup_F3aux_le_theta a ph e
    omega

/-- (F3 aux) Membership in the new set. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_mem_new (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (m e : ℕ) :
    e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_new a ph m ↔
      exists_isComputablyRandom_condK_le_dup_theta a ph e = m ∧ a (2 * e + 1) = true := by
  unfold exists_isComputablyRandom_condK_le_dup_F3aux_new
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have := exists_isComputablyRandom_condK_le_dup_F3aux_le_theta a ph e
    omega

/-- (F3 aux) The active set at stage `m + 1` is the active set at stage `m` plus the new indices. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_sum_split (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (m : ℕ) (f : ℕ → ℚ) :
    ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph (m + 1), f e =
      ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m, f e +
        ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_new a ph (m + 1), f e := by
  rw [← Finset.sum_union]
  · congr 1
    ext e
    rw [Finset.mem_union, exists_isComputablyRandom_condK_le_dup_F3aux_mem_act,
      exists_isComputablyRandom_condK_le_dup_F3aux_mem_act,
      exists_isComputablyRandom_condK_le_dup_F3aux_mem_new]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge m (exists_isComputablyRandom_condK_le_dup_theta a ph e) with h | h
      · exact Or.inr ⟨by omega, h2⟩
      · exact Or.inl ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h2⟩
  · rw [Finset.disjoint_left]
    intro e he he'
    rw [exists_isComputablyRandom_condK_le_dup_F3aux_mem_act] at he
    rw [exists_isComputablyRandom_condK_le_dup_F3aux_mem_new] at he'
    omega

/-- (F3 aux) The terms of the potential of a flagged capital are non-negative. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_term_nonneg (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ)
    (hfair : ∀ e, a (2 * e + 1) = true →
      IsFairCapital uniformMeasure
        (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf ph e x : ℚ) : ℝ)))
    (e : ℕ) (he : a (2 * e + 1) = true) (y : BitString) :
    0 ≤ exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e y := by
  unfold exists_isComputablyRandom_condK_le_dup_F3aux_term
  exact mul_nonneg (by positivity)
    ((exists_isComputablyRandom_condK_le_dup_F3aux_fair_rat (hfair e he)).1 y)

/-- (F3 aux) The greedy step: the potential at stage `m + 1` of the greedily extended prefix `x` is
at
most the potential at stage `m` of `x` plus the activation weights of the new indices. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_greedy (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ)
    (hfair : ∀ e, a (2 * e + 1) = true →
      IsFairCapital uniformMeasure
        (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf ph e x : ℚ) : ℝ)))
    (m : ℕ) (x : BitString) (hx : x.length = m) :
    ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph (m + 1),
        exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e
          (x ++ [exists_isComputablyRandom_condK_le_dup_next a ph (fun m => m + 1) m x]) ≤
      ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m,
        exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e x +
      ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_new a ph (m + 1),
        (1 / 2 : ℚ) ^ e := by
  have hnn : ∀ e, a (2 * e + 1) = true → ∀ y,
      0 ≤ exists_isComputablyRandom_condK_le_dup_evOf ph e y :=
    fun e he => (exists_isComputablyRandom_condK_le_dup_F3aux_fair_rat (hfair e he)).1
  have hfr : ∀ e, a (2 * e + 1) = true → ∀ y,
      exists_isComputablyRandom_condK_le_dup_evOf ph e y =
        (exists_isComputablyRandom_condK_le_dup_evOf ph e (y ++ [false]) +
          exists_isComputablyRandom_condK_le_dup_evOf ph e (y ++ [true])) / 2 :=
    fun e he => (exists_isComputablyRandom_condK_le_dup_F3aux_fair_rat (hfair e he)).2
  have hold : ∀ (c : Bool) (e : ℕ),
      e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m →
      exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [c]) =
        (1 / 2 : ℚ) ^ (e + exists_isComputablyRandom_condK_le_dup_shift
          (exists_isComputablyRandom_condK_le_dup_evOf ph e
            (x.take (exists_isComputablyRandom_condK_le_dup_theta a ph e)))) *
          exists_isComputablyRandom_condK_le_dup_evOf ph e (x ++ [c]) := by
    intro c e he
    have hth : exists_isComputablyRandom_condK_le_dup_theta a ph e ≤ m :=
      ((exists_isComputablyRandom_condK_le_dup_F3aux_mem_act a ph m e).mp he).1
    unfold exists_isComputablyRandom_condK_le_dup_F3aux_term
    rw [List.take_append_of_le_length (by rw [hx]; exact hth)]
  have hsplit : ∀ c : Bool,
      ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph (m + 1),
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [c]) =
        ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m,
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [c]) +
        ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_new a ph (m + 1),
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [c]) :=
    fun c => exists_isComputablyRandom_condK_le_dup_F3aux_sum_split a ph m
      (fun e => exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [c]))
  have hold_sum :
      ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m,
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [false]) +
        ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m,
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [true]) =
        2 * ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m,
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e x := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [hold false e he, hold true e he]
    have hfl : a (2 * e + 1) = true :=
      ((exists_isComputablyRandom_condK_le_dup_F3aux_mem_act a ph m e).mp he).2
    have h2 := hfr e hfl x
    unfold exists_isComputablyRandom_condK_le_dup_F3aux_term
    rw [h2]
    ring
  have hnew : ∀ c : Bool,
      ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_new a ph (m + 1),
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [c]) ≤
        ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_new a ph (m + 1),
          (1 / 2 : ℚ) ^ e := by
    intro c
    apply Finset.sum_le_sum
    intro e he
    obtain ⟨hth, hfl⟩ := (exists_isComputablyRandom_condK_le_dup_F3aux_mem_new a ph (m + 1) e).mp he
    unfold exists_isComputablyRandom_condK_le_dup_F3aux_term
    have htake : (x ++ [c]).take (exists_isComputablyRandom_condK_le_dup_theta a ph e) =
        x ++ [c] := by
      apply List.take_of_length_le
      simp [hx, hth]
    rw [htake]
    exact exists_isComputablyRandom_condK_le_dup_F3aux_term_le e _ (hnn e hfl _)
  have hnext : exists_isComputablyRandom_condK_le_dup_next a ph (fun m => m + 1) m x =
      decide (∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph (m + 1),
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [true]) <
        ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph (m + 1),
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [false])) := rfl
  rw [hnext]
  by_cases h : ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph (m + 1),
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [true]) <
        ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph (m + 1),
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e (x ++ [false])
  · rw [decide_eq_true h]
    have e1 := hsplit true
    have e2 := hsplit false
    have e4 := hnew true
    have e5 := hnew false
    linarith
  · rw [decide_eq_false h]
    have e1 := hsplit true
    have e2 := hsplit false
    have e4 := hnew true
    have e5 := hnew false
    have h' := not_lt.mp h
    linarith

/-- (F3 aux) The invariant: the potential of the greedy prefix is at most the total activation
weight
of the active indices. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_invariant (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ)
    (hfair : ∀ e, a (2 * e + 1) = true →
      IsFairCapital uniformMeasure
        (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf ph e x : ℚ) : ℝ)))
    (m : ℕ) :
    ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m,
        exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e
          (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m) ≤
      ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m, (1 / 2 : ℚ) ^ e := by
  induction m with
  | zero =>
    apply Finset.sum_le_sum
    intro e he
    obtain ⟨hth, hfl⟩ := (exists_isComputablyRandom_condK_le_dup_F3aux_mem_act a ph 0 e).mp he
    have h0 : exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) 0 = [] := rfl
    rw [h0]
    unfold exists_isComputablyRandom_condK_le_dup_F3aux_term
    rw [List.take_nil]
    exact exists_isComputablyRandom_condK_le_dup_F3aux_term_le e _
      ((exists_isComputablyRandom_condK_le_dup_F3aux_fair_rat (hfair e hfl)).1 _)
  | succ m ih =>
    have hlen := exists_isComputablyRandom_condK_le_dup_F3aux_length_run a ph (fun m => m + 1) m
    have hrun : exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) (m + 1) =
        exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m ++
          [exists_isComputablyRandom_condK_le_dup_next a ph (fun m => m + 1) m
            (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m)] := rfl
    rw [hrun]
    calc ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph (m + 1),
          exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e
            (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m ++
              [exists_isComputablyRandom_condK_le_dup_next a ph (fun m => m + 1) m
                (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m)])
        ≤ ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m,
            exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e
              (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m) +
          ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_new a ph (m + 1),
            (1 / 2 : ℚ) ^ e :=
          exists_isComputablyRandom_condK_le_dup_F3aux_greedy a ph hfair m _ hlen
      _ ≤ ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m, (1 / 2 : ℚ) ^ e +
          ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_new a ph (m + 1),
            (1 / 2 : ℚ) ^ e := by linarith
      _ = ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph (m + 1),
            (1 / 2 : ℚ) ^ e :=
          (exists_isComputablyRandom_condK_le_dup_F3aux_sum_split a ph m _).symm

/-- (F3 aux) The total activation weight is at most `2`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F3aux_sum_act_le (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (m : ℕ) :
    ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m, (1 / 2 : ℚ) ^ e ≤ 2 := by
  have hsub : exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m ⊆
      Finset.range (m + 1) := Finset.filter_subset _ _
  calc ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph m, (1 / 2 : ℚ) ^ e
      ≤ ∑ e ∈ Finset.range (m + 1), (1 / 2 : ℚ) ^ e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => by positivity)
    _ = 2 - 2 * (1 / 2) ^ (m + 1) := exists_isComputablyRandom_condK_le_dup_F3aux_geom (m + 1)
    _ ≤ 2 := by
        have : (0 : ℚ) ≤ 2 * (1 / 2) ^ (m + 1) := by positivity
        linarith

/-- Step 3 of the proof of `exists_isComputablyRandom_condK_le_dup`: the greedy
potential argument.  On the greedy sequence no capital flagged by `a` wins. -/
private lemma exists_isComputablyRandom_condK_le_dup_bounded (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ)
    (hfair : ∀ e, a (2 * e + 1) = true →
      IsFairCapital uniformMeasure (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf ph e x :
                                               ℚ) : ℝ))) :
    ∀ e, a (2 * e + 1) = true →
      ¬ Wins (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf ph e x : ℚ) : ℝ))
        (exists_isComputablyRandom_condK_le_dup_seq a ph) := by
  intro e0 he0 hw
  have hnn : ∀ y, 0 ≤ exists_isComputablyRandom_condK_le_dup_evOf ph e0 y :=
    (exists_isComputablyRandom_condK_le_dup_F3aux_fair_rat (hfair e0 he0)).1
  obtain ⟨th0, hth0⟩ : ∃ t, t = exists_isComputablyRandom_condK_le_dup_theta a ph e0 :=
    ⟨_, rfl⟩
  obtain ⟨k0, hk0⟩ : ∃ k, k = exists_isComputablyRandom_condK_le_dup_shift
      (exists_isComputablyRandom_condK_le_dup_evOf ph e0
        (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) th0)) := ⟨_, rfl⟩
  have key : ∀ n, exists_isComputablyRandom_condK_le_dup_evOf ph e0
      (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n) ≤
      2 ^ (e0 + k0 + 1) + ∑ m ∈ Finset.range th0,
        exists_isComputablyRandom_condK_le_dup_evOf ph e0
          (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m) := by
    intro n
    have hS : 0 ≤ ∑ m ∈ Finset.range th0, exists_isComputablyRandom_condK_le_dup_evOf ph e0
        (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m) :=
      Finset.sum_nonneg (fun m _ => hnn _)
    have hP : (0 : ℚ) ≤ 2 ^ (e0 + k0 + 1) := by positivity
    rcases Nat.lt_or_ge n th0 with hn | hn
    · have h1 : exists_isComputablyRandom_condK_le_dup_evOf ph e0
          (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n) ≤
          ∑ m ∈ Finset.range th0, exists_isComputablyRandom_condK_le_dup_evOf ph e0
            (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m) :=
        Finset.single_le_sum (f := fun m => exists_isComputablyRandom_condK_le_dup_evOf ph e0
          (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m))
          (fun m _ => hnn _) (Finset.mem_range.mpr hn)
      linarith
    · have hmem : e0 ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph n :=
        (exists_isComputablyRandom_condK_le_dup_F3aux_mem_act a ph n e0).mpr
          ⟨by rw [← hth0]; exact hn, he0⟩
      have h1 : exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e0
            (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n) ≤
          ∑ e ∈ exists_isComputablyRandom_condK_le_dup_F3aux_act a ph n,
            exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e
              (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n) :=
        Finset.single_le_sum
          (f := fun e => exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e
            (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n))
          (fun e he => exists_isComputablyRandom_condK_le_dup_F3aux_term_nonneg a ph hfair e
            ((exists_isComputablyRandom_condK_le_dup_F3aux_mem_act a ph n e).mp he).2 _) hmem
      have h2 := exists_isComputablyRandom_condK_le_dup_F3aux_invariant a ph hfair n
      have h3 := exists_isComputablyRandom_condK_le_dup_F3aux_sum_act_le a ph n
      have h4 : exists_isComputablyRandom_condK_le_dup_F3aux_term a ph e0
            (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n) =
          (1 / 2 : ℚ) ^ (e0 + k0) * exists_isComputablyRandom_condK_le_dup_evOf ph e0
            (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n) := by
        unfold exists_isComputablyRandom_condK_le_dup_F3aux_term
        rw [← hth0, exists_isComputablyRandom_condK_le_dup_F3aux_take_run a ph
          (fun m => m + 1) th0 n hn, ← hk0]
      have h5 : (1 / 2 : ℚ) ^ (e0 + k0) * exists_isComputablyRandom_condK_le_dup_evOf ph e0
          (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n) ≤ 2 := by
        rw [← h4]
        exact le_trans h1 (le_trans h2 h3)
      have hpos : (0 : ℚ) < 2 ^ (e0 + k0) := by positivity
      have h6 : exists_isComputablyRandom_condK_le_dup_evOf ph e0
          (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n) ≤
          2 ^ (e0 + k0 + 1) := by
        calc exists_isComputablyRandom_condK_le_dup_evOf ph e0
              (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n)
            = 2 ^ (e0 + k0) * ((1 / 2 : ℚ) ^ (e0 + k0) *
                exists_isComputablyRandom_condK_le_dup_evOf ph e0
                  (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) n)) := by
              rw [← mul_assoc, ← mul_pow]
              norm_num
          _ ≤ 2 ^ (e0 + k0) * 2 := mul_le_mul_of_nonneg_left h5 hpos.le
          _ = 2 ^ (e0 + k0 + 1) := by rw [pow_succ]
      linarith
  refine hw ⟨((2 ^ (e0 + k0 + 1) + ∑ m ∈ Finset.range th0,
    exists_isComputablyRandom_condK_le_dup_evOf ph e0
      (exists_isComputablyRandom_condK_le_dup_run a ph (fun m => m + 1) m) : ℚ) : ℝ), ?_⟩
  rintro _ ⟨n, rfl⟩
  change ((exists_isComputablyRandom_condK_le_dup_evOf ph e0
    (cantorPrefix (exists_isComputablyRandom_condK_le_dup_seq a ph) n) : ℚ) : ℝ) ≤ _
  rw [exists_isComputablyRandom_condK_le_dup_prefix a ph n]
  exact_mod_cast key n
/-- The greedy prefix of length `m` has length `m`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F4aux_run_length (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (cut : ℕ → ℕ) (m : ℕ) :
    (exists_isComputablyRandom_condK_le_dup_run a ph cut m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [exists_isComputablyRandom_condK_le_dup_run, ih]

/-- The potential does not depend on the cut-off as long as it contains all the active indices. -/
private lemma exists_isComputablyRandom_condK_le_dup_F4aux_pot_cut_congr (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (c c' m : ℕ) (x : BitString)
    (h : ∀ e, exists_isComputablyRandom_condK_le_dup_theta a ph e ≤ m → e < c ∧ e < c') :
    exists_isComputablyRandom_condK_le_dup_pot a ph c' m x =
      exists_isComputablyRandom_condK_le_dup_pot a ph c m x := by
  unfold exists_isComputablyRandom_condK_le_dup_pot
  have hfin : (Finset.range c').filter (fun e =>
        exists_isComputablyRandom_condK_le_dup_theta a ph e ≤ m ∧ a (2 * e + 1) = true) =
      (Finset.range c).filter (fun e =>
        exists_isComputablyRandom_condK_le_dup_theta a ph e ≤ m ∧ a (2 * e + 1) = true) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨(h e h1).1, h1, h2⟩
    · rintro ⟨_, h1, h2⟩
      exact ⟨(h e h1).2, h1, h2⟩
  rw [hfin]

/-- Step 4a of the proof of `exists_isComputablyRandom_condK_le_dup`: the greedy prefix
does not depend on the cut-off as long as the cut-offs contain all the active indices. -/
private lemma exists_isComputablyRandom_condK_le_dup_run_cut_congr (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (cut cut' : ℕ → ℕ) (n : ℕ)
    (h : ∀ m ≤ n, ∀ e, exists_isComputablyRandom_condK_le_dup_theta a ph e ≤ m →
      e < cut m ∧ e < cut' m) :
    exists_isComputablyRandom_condK_le_dup_run a ph cut' n =
      exists_isComputablyRandom_condK_le_dup_run a ph cut n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun m hm e he => h m (by omega) e he)
    have hpot : ∀ x : BitString,
        exists_isComputablyRandom_condK_le_dup_pot a ph (cut' (n + 1)) (n + 1) x =
          exists_isComputablyRandom_condK_le_dup_pot a ph (cut (n + 1)) (n + 1) x := fun x =>
      exists_isComputablyRandom_condK_le_dup_F4aux_pot_cut_congr a ph _ _ _ x
        (fun e he => h (n + 1) le_rfl e he)
    have hnext : ∀ x : BitString,
        exists_isComputablyRandom_condK_le_dup_next a ph cut' n x =
          exists_isComputablyRandom_condK_le_dup_next a ph cut n x := by
      intro x
      unfold exists_isComputablyRandom_condK_le_dup_next
      rw [hpot, hpot]
    change exists_isComputablyRandom_condK_le_dup_run a ph cut' n ++
        [exists_isComputablyRandom_condK_le_dup_next a ph cut' n
          (exists_isComputablyRandom_condK_le_dup_run a ph cut' n)] =
      exists_isComputablyRandom_condK_le_dup_run a ph cut n ++
        [exists_isComputablyRandom_condK_le_dup_next a ph cut n
          (exists_isComputablyRandom_condK_le_dup_run a ph cut n)]
    rw [ih', hnext]

/-- `θ e` only depends on the flags `a i`, `i < 2L`, and on the values `ph e' j'` for flagged
`e' < j' < L`, when `e < L`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F4aux_theta_congr (a a' : ℕ → Bool)
    (ph ph' : ℕ → ℕ → ℕ) (L e : ℕ) (he : e < L)
    (ha : ∀ i < 2 * L, a' i = a i)
    (hph : ∀ e j, e < j → j < L → a (2 * e) = true → ph' e j = ph e j) :
    exists_isComputablyRandom_condK_le_dup_theta a' ph' e =
      exists_isComputablyRandom_condK_le_dup_theta a ph e := by
  unfold exists_isComputablyRandom_condK_le_dup_theta
  congr 1
  apply Finset.sup_congr rfl
  intro j' hj'
  have hj'e : j' ≤ e := by simpa [Nat.lt_succ_iff] using hj'
  apply Finset.sup_congr rfl
  intro e' he'
  have he'j : e' < j' := Finset.mem_range.mp he'
  have h1 : a' (2 * e') = a (2 * e') := ha _ (by omega)
  rw [h1]
  by_cases hh : a (2 * e') = true
  · simp only [hh, ↓reduceIte]
    exact hph e' j' he'j (by omega) hh
  · simp [hh]

/-- The potential only depends on the flags `a i`, `i < 2L`, on the values `ph e j` for flagged
`e < j < L`, and on the values `ph e (encode x)` for flagged capitals `e < L` and strings `x` of
length `≤ N`, when the cut-off is `≤ L` and the string has length `≤ N`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F4aux_pot_congr (a a' : ℕ → Bool)
    (ph ph' : ℕ → ℕ → ℕ) (L N c m : ℕ) (y : BitString) (hc : c ≤ L) (hy : y.length ≤ N)
    (ha : ∀ i < 2 * L, a' i = a i)
    (hph : ∀ e j, e < j → j < L → a (2 * e) = true → ph' e j = ph e j)
    (hev : ∀ (e : ℕ) (x : BitString), e < L → a (2 * e + 1) = true → x.length ≤ N →
      ph' e (Encodable.encode x) = ph e (Encodable.encode x)) :
    exists_isComputablyRandom_condK_le_dup_pot a' ph' c m y =
      exists_isComputablyRandom_condK_le_dup_pot a ph c m y := by
  unfold exists_isComputablyRandom_condK_le_dup_pot
  have hfin : (Finset.range c).filter (fun e =>
        exists_isComputablyRandom_condK_le_dup_theta a' ph' e ≤ m ∧ a' (2 * e + 1) = true) =
      (Finset.range c).filter (fun e =>
        exists_isComputablyRandom_condK_le_dup_theta a ph e ≤ m ∧ a (2 * e + 1) = true) := by
    apply Finset.filter_congr
    intro e he
    have heL : e < L := lt_of_lt_of_le (Finset.mem_range.mp he) hc
    rw [exists_isComputablyRandom_condK_le_dup_F4aux_theta_congr a a' ph ph' L e heL ha hph,
      ha (2 * e + 1) (by omega)]
  rw [hfin]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Finset.mem_filter, Finset.mem_range] at he
  obtain ⟨hec, hθ, hflag⟩ := he
  have heL : e < L := lt_of_lt_of_le hec hc
  rw [exists_isComputablyRandom_condK_le_dup_F4aux_theta_congr a a' ph ph' L e heL ha hph]
  have h1 : exists_isComputablyRandom_condK_le_dup_evOf ph' e
        (y.take (exists_isComputablyRandom_condK_le_dup_theta a ph e)) =
      exists_isComputablyRandom_condK_le_dup_evOf ph e
        (y.take (exists_isComputablyRandom_condK_le_dup_theta a ph e)) := by
    unfold exists_isComputablyRandom_condK_le_dup_evOf
    rw [hev e (y.take (exists_isComputablyRandom_condK_le_dup_theta a ph e)) heL hflag
      (le_trans (List.length_take_le' _ _) hy)]
  have h2 : exists_isComputablyRandom_condK_le_dup_evOf ph' e y =
      exists_isComputablyRandom_condK_le_dup_evOf ph e y := by
    unfold exists_isComputablyRandom_condK_le_dup_evOf
    rw [hev e y heL hflag hy]
  rw [h1, h2]

/-- Step 4b of the proof of `exists_isComputablyRandom_condK_le_dup`: the greedy prefix
of length `n` with cut-offs `≤ L` only depends on the flags `a i`, `i < 2L`, on the values `ph e j`
for flagged `e < j < L`, and on the values `ph e (encode x)` for flagged capitals `e < L` and
strings
`x` of length `≤ n`. -/
private lemma exists_isComputablyRandom_condK_le_dup_run_congr (a a' : ℕ → Bool)
    (ph ph' : ℕ → ℕ → ℕ) (cut : ℕ → ℕ) (n L : ℕ) (hcut : ∀ m ≤ n, cut m ≤ L)
    (ha : ∀ i < 2 * L, a' i = a i)
    (hph : ∀ e j, e < j → j < L → a (2 * e) = true → ph' e j = ph e j)
    (hev : ∀ (e : ℕ) (x : BitString), e < L → a (2 * e + 1) = true → x.length ≤ n →
      ph' e (Encodable.encode x) = ph e (Encodable.encode x)) :
    exists_isComputablyRandom_condK_le_dup_run a' ph' cut n =
      exists_isComputablyRandom_condK_le_dup_run a ph cut n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun m hm => hcut m (by omega))
      (fun e x he hflag hx => hev e x he hflag (by omega))
    have hlen := exists_isComputablyRandom_condK_le_dup_F4aux_run_length a ph cut n
    have hnext : exists_isComputablyRandom_condK_le_dup_next a' ph' cut n
          (exists_isComputablyRandom_condK_le_dup_run a ph cut n) =
        exists_isComputablyRandom_condK_le_dup_next a ph cut n
          (exists_isComputablyRandom_condK_le_dup_run a ph cut n) := by
      unfold exists_isComputablyRandom_condK_le_dup_next
      have hb : ∀ b : Bool,
          exists_isComputablyRandom_condK_le_dup_pot a' ph' (cut (n + 1)) (n + 1)
              (exists_isComputablyRandom_condK_le_dup_run a ph cut n ++ [b]) =
            exists_isComputablyRandom_condK_le_dup_pot a ph (cut (n + 1)) (n + 1)
              (exists_isComputablyRandom_condK_le_dup_run a ph cut n ++ [b]) := by
        intro b
        exact exists_isComputablyRandom_condK_le_dup_F4aux_pot_congr a a' ph ph' L (n + 1)
          (cut (n + 1)) (n + 1) _ (hcut (n + 1) le_rfl) (by simp [hlen]) ha hph hev
      rw [hb true, hb false]
    change exists_isComputablyRandom_condK_le_dup_run a' ph' cut n ++
        [exists_isComputablyRandom_condK_le_dup_next a' ph' cut n
          (exists_isComputablyRandom_condK_le_dup_run a' ph' cut n)] =
      exists_isComputablyRandom_condK_le_dup_run a ph cut n ++
        [exists_isComputablyRandom_condK_le_dup_next a ph cut n
          (exists_isComputablyRandom_condK_le_dup_run a ph cut n)]
    rw [ih', hnext]

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_theta_succ (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (j : ℕ) :
    exists_isComputablyRandom_condK_le_dup_theta a ph j + 1 ≤
      exists_isComputablyRandom_condK_le_dup_theta a ph (j + 1) := by
  unfold exists_isComputablyRandom_condK_le_dup_theta
  have h : (Finset.range (j + 1)).sup (fun j' => (Finset.range j').sup
      (fun e => if a (2 * e) = true then ph e j' else 0)) ≤
      (Finset.range (j + 1 + 1)).sup (fun j' => (Finset.range j').sup
      (fun e => if a (2 * e) = true then ph e j' else 0)) :=
    Finset.sup_mono (Finset.range_mono (Nat.le_succ _))
  omega

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_le_theta (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (j : ℕ) :
    j ≤ exists_isComputablyRandom_condK_le_dup_theta a ph j := by
  unfold exists_isComputablyRandom_condK_le_dup_theta
  omega

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_theta_mono (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) :
    Monotone (exists_isComputablyRandom_condK_le_dup_theta a ph) :=
  monotone_nat_of_le_succ (fun j => by
    have := exists_isComputablyRandom_condK_le_dup_F5aux_theta_succ a ph j
    omega)

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_lt_K_of_theta_le (n e : ℕ)
    (h : exists_isComputablyRandom_condK_le_dup_theta
      exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph e
        ≤ n) :
    e < exists_isComputablyRandom_condK_le_dup_K n := by
  unfold exists_isComputablyRandom_condK_le_dup_K
  have hsub : Finset.range (e + 1) ⊆ (Finset.range (n + 1)).filter (fun j =>
      exists_isComputablyRandom_condK_le_dup_theta exists_isComputablyRandom_condK_le_dup_mask
        exists_isComputablyRandom_condK_le_dup_ph j ≤ n) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have := exists_isComputablyRandom_condK_le_dup_F5aux_le_theta
        exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph e
      omega
    · exact (exists_isComputablyRandom_condK_le_dup_F5aux_theta_mono
        exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph
        (by omega : j ≤ e)).trans h
  have := Finset.card_le_card hsub
  simp only [Finset.card_range] at this
  omega

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_mem_strings (n : ℕ) :
    ∀ x : BitString, x.length ≤ n → x ∈ exists_isComputablyRandom_condK_le_dup_strings n := by
  induction n with
  | zero =>
    intro x hx
    have : x = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp [exists_isComputablyRandom_condK_le_dup_strings]
  | succ n ih =>
    intro x hx
    cases x with
    | nil => simp [exists_isComputablyRandom_condK_le_dup_strings]
    | cons b x =>
      have ih' := ih x (by simpa using hx)
      simp only [exists_isComputablyRandom_condK_le_dup_strings, List.mem_cons,
        List.mem_flatMap]
      right
      refine ⟨x, ih', ?_⟩
      cases b <;> simp

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_adv_length (n : ℕ) :
    (exists_isComputablyRandom_condK_le_dup_adv n).length =
      2 * exists_isComputablyRandom_condK_le_dup_K n := by
  simp [exists_isComputablyRandom_condK_le_dup_adv]

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_adv_getD (n i : ℕ)
    (hi : i < 2 * exists_isComputablyRandom_condK_le_dup_K n) :
    (exists_isComputablyRandom_condK_le_dup_adv n).getD i false =
      exists_isComputablyRandom_condK_le_dup_mask i := by
  simp [exists_isComputablyRandom_condK_le_dup_adv, hi]

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_phS_eq (s e j : ℕ)
    (htot : exists_isComputablyRandom_condK_le_dup_tot e)
    (hs : (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e) j).isSome = true) :
    exists_isComputablyRandom_condK_le_dup_phS s e j =
      exists_isComputablyRandom_condK_le_dup_ph e j := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  have hmem : v ∈ Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) j :=
    Nat.Partrec.Code.evaln_sound (k := s) (Option.mem_def.mpr hv)
  have hdom := htot j
  unfold exists_isComputablyRandom_condK_le_dup_phS exists_isComputablyRandom_condK_le_dup_ph
  rw [hv, Option.getD_some]
  unfold Part.getOrElse
  simp only [hdom, ↓reduceDIte]
  exact (Part.get_eq_of_mem hmem hdom).symm

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_eventually_isSome (e q : ℕ)
    (htot : exists_isComputablyRandom_condK_le_dup_tot e) :
    ∀ᶠ s in Filter.atTop,
      (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e) q).isSome = true := by
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp (Part.get_mem (htot q))
  filter_upwards [Filter.eventually_ge_atTop k] with s hs
  have := Nat.Partrec.Code.evaln_mono hs hk
  rw [Option.mem_def] at this
  rw [this]
  rfl

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_good_iff (s : ℕ) (p : BitString)
    (n : ℕ) :
    exists_isComputablyRandom_condK_le_dup_good s p n = true ↔
      ∀ e < p.length / 2,
        (p.getD (2 * e) false = true → ∀ j < p.length / 2,
          (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e) j).isSome = true) ∧
        (p.getD (2 * e + 1) false = true →
          ∀ x ∈ exists_isComputablyRandom_condK_le_dup_strings n,
            (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
              (Encodable.encode x)).isSome = true) := by
  unfold exists_isComputablyRandom_condK_le_dup_good
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  refine forall_congr' (fun e => imp_congr_right (fun _ => and_congr ?_ ?_))
  · constructor
    · intro h hp j hj
      rcases h with h | h
      · rw [hp] at h; exact absurd h (by simp)
      · exact h j hj
    · intro h
      by_cases hp : p.getD (2 * e) false = true
      · exact Or.inr (fun j hj => h hp j hj)
      · exact Or.inl (by simpa using hp)
  · constructor
    · intro h hp x hx
      rcases h with h | h
      · rw [hp] at h; exact absurd h (by simp)
      · exact h x hx
    · intro h
      by_cases hp : p.getD (2 * e + 1) false = true
      · exact Or.inr (fun x hx => h hp x hx)
      · exact Or.inl (by simpa using hp)

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_exists_good (n : ℕ) :
    ∃ s, exists_isComputablyRandom_condK_le_dup_good s
      (exists_isComputablyRandom_condK_le_dup_adv n) n = true := by
  have hev : ∀ᶠ s in Filter.atTop,
      ∀ e ∈ Finset.range (exists_isComputablyRandom_condK_le_dup_K n),
        (exists_isComputablyRandom_condK_le_dup_mask (2 * e) = true →
          ∀ j ∈ Finset.range (exists_isComputablyRandom_condK_le_dup_K n),
            (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e) j).isSome = true) ∧
        (exists_isComputablyRandom_condK_le_dup_mask (2 * e + 1) = true →
          ∀ x ∈ (exists_isComputablyRandom_condK_le_dup_strings n).toFinset,
            (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e)
              (Encodable.encode x)).isSome = true) := by
    rw [Filter.eventually_all_finset]
    intro e _
    refine Filter.Eventually.and ?_ ?_
    · by_cases hf : exists_isComputablyRandom_condK_le_dup_mask (2 * e) = true
      · have ht := (exists_isComputablyRandom_condK_le_dup_mask_spec e).1 hf
        simp only [hf, true_implies]
        rw [Filter.eventually_all_finset]
        intro j _
        exact exists_isComputablyRandom_condK_le_dup_F5aux_eventually_isSome e j ht
      · exact Filter.Eventually.of_forall (fun s h => absurd h hf)
    · by_cases hf : exists_isComputablyRandom_condK_le_dup_mask (2 * e + 1) = true
      · have ht := ((exists_isComputablyRandom_condK_le_dup_mask_spec e).2 hf).1
        simp only [hf, true_implies]
        rw [Filter.eventually_all_finset]
        intro x _
        exact exists_isComputablyRandom_condK_le_dup_F5aux_eventually_isSome e _ ht
      · exact Filter.Eventually.of_forall (fun s h => absurd h hf)
  obtain ⟨s, hs⟩ := hev.exists
  refine ⟨s, ?_⟩
  have hL : (exists_isComputablyRandom_condK_le_dup_adv n).length / 2 =
      exists_isComputablyRandom_condK_le_dup_K n := by
    rw [exists_isComputablyRandom_condK_le_dup_F5aux_adv_length]
    omega
  rw [exists_isComputablyRandom_condK_le_dup_F5aux_good_iff, hL]
  intro e he
  have h1 := hs e (Finset.mem_range.mpr he)
  refine ⟨fun hp j hj => ?_, fun hp x hx => ?_⟩
  · rw [exists_isComputablyRandom_condK_le_dup_F5aux_adv_getD n (2 * e) (by omega)] at hp
    exact h1.1 hp j (Finset.mem_range.mpr hj)
  · rw [exists_isComputablyRandom_condK_le_dup_F5aux_adv_getD n (2 * e + 1) (by omega)] at hp
    exact h1.2 hp x (List.mem_toFinset.mpr hx)

private lemma exists_isComputablyRandom_condK_le_dup_F5aux_run_eq (n s : ℕ)
    (hg : exists_isComputablyRandom_condK_le_dup_good s
      (exists_isComputablyRandom_condK_le_dup_adv n) n = true) :
    exists_isComputablyRandom_condK_le_dup_run
        (fun i => (exists_isComputablyRandom_condK_le_dup_adv n).getD i false)
        (exists_isComputablyRandom_condK_le_dup_phS s)
        (fun m => min ((exists_isComputablyRandom_condK_le_dup_adv n).length / 2) (m + 1)) n =
      cantorPrefix (exists_isComputablyRandom_condK_le_dup_seq
        exists_isComputablyRandom_condK_le_dup_mask
        exists_isComputablyRandom_condK_le_dup_ph) n := by
  have hL : (exists_isComputablyRandom_condK_le_dup_adv n).length / 2 =
      exists_isComputablyRandom_condK_le_dup_K n := by
    rw [exists_isComputablyRandom_condK_le_dup_F5aux_adv_length]
    omega
  rw [exists_isComputablyRandom_condK_le_dup_F5aux_good_iff, hL] at hg
  rw [hL]
  have hph : ∀ e j, e < j → j < exists_isComputablyRandom_condK_le_dup_K n →
      exists_isComputablyRandom_condK_le_dup_mask (2 * e) = true →
      exists_isComputablyRandom_condK_le_dup_phS s e j =
        exists_isComputablyRandom_condK_le_dup_ph e j := by
    intro e j hej hj hm
    have heK : e < exists_isComputablyRandom_condK_le_dup_K n := by omega
    have h1 := (hg e heK).1
    rw [exists_isComputablyRandom_condK_le_dup_F5aux_adv_getD n (2 * e) (by omega)] at h1
    exact exists_isComputablyRandom_condK_le_dup_F5aux_phS_eq s e j
      ((exists_isComputablyRandom_condK_le_dup_mask_spec e).1 hm) (h1 hm j hj)
  have hev : ∀ (e : ℕ) (x : BitString), e < exists_isComputablyRandom_condK_le_dup_K n →
      exists_isComputablyRandom_condK_le_dup_mask (2 * e + 1) = true → x.length ≤ n →
      exists_isComputablyRandom_condK_le_dup_phS s e (Encodable.encode x) =
        exists_isComputablyRandom_condK_le_dup_ph e (Encodable.encode x) := by
    intro e x heK hm hx
    have h1 := (hg e heK).2
    rw [exists_isComputablyRandom_condK_le_dup_F5aux_adv_getD n (2 * e + 1) (by omega)] at h1
    exact exists_isComputablyRandom_condK_le_dup_F5aux_phS_eq s e _
      ((exists_isComputablyRandom_condK_le_dup_mask_spec e).2 hm).1
      (h1 hm x (exists_isComputablyRandom_condK_le_dup_F5aux_mem_strings n x hx))
  have h1 := exists_isComputablyRandom_condK_le_dup_run_congr
    exists_isComputablyRandom_condK_le_dup_mask
    (fun i => (exists_isComputablyRandom_condK_le_dup_adv n).getD i false)
    exists_isComputablyRandom_condK_le_dup_ph (exists_isComputablyRandom_condK_le_dup_phS s)
    (fun m => min (exists_isComputablyRandom_condK_le_dup_K n) (m + 1)) n
    (exists_isComputablyRandom_condK_le_dup_K n) (fun m _ => min_le_left _ _)
    (fun i hi => exists_isComputablyRandom_condK_le_dup_F5aux_adv_getD n i hi) hph hev
  have h2 := exists_isComputablyRandom_condK_le_dup_run_cut_congr
    exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph
    (fun m => m + 1) (fun m => min (exists_isComputablyRandom_condK_le_dup_K n) (m + 1)) n
    (fun m hm e he => by
      have hle := exists_isComputablyRandom_condK_le_dup_F5aux_le_theta
        exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph e
      exact ⟨by omega, lt_min
        (exists_isComputablyRandom_condK_le_dup_F5aux_lt_K_of_theta_le n e (he.trans hm))
        (by omega)⟩)
  rw [h1, h2, exists_isComputablyRandom_condK_le_dup_prefix]

/-- Step 5a of the proof of `exists_isComputablyRandom_condK_le_dup`: with the true
advice, the simulation halts for large `s` and every halting value is the true prefix. -/
private lemma exists_isComputablyRandom_condK_le_dup_sim_spec (n : ℕ) :
    (∃ s, exists_isComputablyRandom_condK_le_dup_sim s
        (exists_isComputablyRandom_condK_le_dup_adv n) n =
      some (cantorPrefix (exists_isComputablyRandom_condK_le_dup_seq
        exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph) n)) ∧
    ∀ s r, exists_isComputablyRandom_condK_le_dup_sim s
        (exists_isComputablyRandom_condK_le_dup_adv n) n = some r →
      r = cantorPrefix (exists_isComputablyRandom_condK_le_dup_seq
        exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph) n :=
            by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_isComputablyRandom_condK_le_dup_F5aux_exists_good n
    refine ⟨s, ?_⟩
    unfold exists_isComputablyRandom_condK_le_dup_sim
    simp only [hs, ↓reduceIte]
    rw [exists_isComputablyRandom_condK_le_dup_F5aux_run_eq n s hs]
  · intro s r h
    unfold exists_isComputablyRandom_condK_le_dup_sim at h
    by_cases hs : exists_isComputablyRandom_condK_le_dup_good s
        (exists_isComputablyRandom_condK_le_dup_adv n) n = true
    · simp only [hs, ↓reduceIte] at h
      exact (Option.some.inj h).symm.trans
        (exists_isComputablyRandom_condK_le_dup_F5aux_run_eq n s hs)
    · simp only [hs] at h
      exact absurd h (by simp)

/-- A supremum over `range k` is a primitive recursion on `k`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_sup_range_eq (g : ℕ → ℕ) (k : ℕ) :
    (Finset.range k).sup g = Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => max (g y) IH) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_add_one, Finset.sup_insert, ih]

/-- A supremum over `range (K b)` of a computable family is computable. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_sup_range_computable
    {β : Type} [Primcodable β] {G : β → ℕ → ℕ} {K : β → ℕ}
    (hG : Computable (fun q : β × ℕ => G q.1 q.2)) (hK : Computable K) :
    Computable (fun b : β => (Finset.range (K b)).sup (G b)) := by
  have hg : Computable (fun x : β × (ℕ × ℕ) => G x.1 x.2.1) :=
    hG.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
  have hh' : Computable (fun x : β × (ℕ × ℕ) => x.2.2) :=
    Computable.snd.comp Computable.snd
  have hh : Computable₂ (fun (b : β) (p : ℕ × ℕ) => max (G b p.1) p.2) :=
    Computable₂.comp (f := fun a b : ℕ => max a b) Primrec.nat_max.to_comp hg hh'
  have h := Computable.nat_rec (f := K) (g := fun _ : β => (0 : ℕ))
    (h := fun (b : β) (p : ℕ × ℕ) => max (G b p.1) p.2) hK (Computable.const 0) hh
  exact h.of_eq (fun b => (exists_isComputablyRandom_condK_le_dup_F6aux_sup_range_eq (G b)
                            (K b)).symm)

/-- `θ` is computable, with all the data given by computable functions of a parameter. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_theta_computable
    {β : Type} [Primcodable β] {A : β → ℕ → Bool} {PH : β → ℕ → ℕ → ℕ} {J : β → ℕ}
    (hA : Computable (fun q : β × ℕ => A q.1 q.2))
    (hPH : Computable (fun q : β × ℕ × ℕ => PH q.1 q.2.1 q.2.2)) (hJ : Computable J) :
    Computable (fun b : β =>
      exists_isComputablyRandom_condK_le_dup_theta (A b) (PH b) (J b)) := by
  have hc : Computable (fun q : (β × ℕ) × ℕ => A q.1.1 (2 * q.2)) :=
    hA.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable₂.comp (f := fun a b : ℕ => a * b) Primrec.nat_mul.to_comp
        (Computable.const 2) Computable.snd))
  have hf : Computable (fun q : (β × ℕ) × ℕ => PH q.1.1 q.2 q.1.2) :=
    hPH.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)))
  have hG : Computable (fun q : (β × ℕ) × ℕ =>
      (fun (r : β × ℕ) (e : ℕ) => if A r.1 (2 * e) = true then PH r.1 e r.2 else 0) q.1 q.2) :=
    (Computable.cond hc hf (Computable.const 0)).of_eq (fun q => Bool.cond_eq_ite _ _ _)
  have hinner : Computable (fun r : β × ℕ =>
      (Finset.range r.2).sup (fun e => if A r.1 (2 * e) = true then PH r.1 e r.2 else 0)) :=
    exists_isComputablyRandom_condK_le_dup_F6aux_sup_range_computable
      (β := β × ℕ) (G := fun (r : β × ℕ) (e : ℕ) => if A r.1 (2 * e) = true then PH r.1 e r.2 else
                                                      0)
      (K := fun r => r.2) hG Computable.snd
  have houter : Computable (fun b : β =>
      (Finset.range (J b + 1)).sup (fun j' => (Finset.range j').sup
        (fun e => if A b (2 * e) = true then PH b e j' else 0))) :=
    exists_isComputablyRandom_condK_le_dup_F6aux_sup_range_computable
      (β := β) (G := fun (b : β) (j' : ℕ) =>
        (Finset.range j').sup (fun e => if A b (2 * e) = true then PH b e j' else 0))
      (K := fun b => J b + 1) hinner
      (Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp hJ (Computable.const 1))
  exact Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp hJ houter

/-- Step 5b1 of the proof of `exists_isComputablyRandom_condK_le_dup`: `θ` is computable,
uniformly in computable data. -/
private lemma exists_isComputablyRandom_condK_le_dup_step5b1_theta_computable
    {α : Type} [Primcodable α] {A : α → ℕ → Bool} {PH : α → ℕ → ℕ → ℕ}
    (hA : Computable (fun q : α × ℕ => A q.1 q.2))
    (hPH : Computable (fun q : α × ℕ × ℕ => PH q.1 q.2.1 q.2.2)) :
    Computable (fun q : α × ℕ =>
      exists_isComputablyRandom_condK_le_dup_theta (A q.1) (PH q.1) q.2) := by
  refine exists_isComputablyRandom_condK_le_dup_F6aux_theta_computable
    (β := α × ℕ) (A := fun q => A q.1) (PH := fun q => PH q.1) (J := fun q => q.2) ?_ ?_
    Computable.snd
  · exact hA.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  · exact hPH.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)

/-- A filtered sum over `range c` is a primitive recursion on `c`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_sum_filter_eq (P : ℕ → Prop)
    [DecidablePred P] (g : ℕ → ℚ) (c : ℕ) :
    (∑ e ∈ (Finset.range c).filter P, g e) =
      Nat.rec (motive := fun _ => ℚ) 0
        (fun y IH => bif decide (P y) then IH + g y else IH) c := by
  rw [Finset.sum_filter]
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : P c <;> simp [h]

/-- A filtered sum over `range (K b)` of a computable family is computable. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_sum_filter_computable
    {β : Type} [Primcodable β] {P : β → ℕ → Prop} [∀ b, DecidablePred (P b)]
    {G : β → ℕ → ℚ} {K : β → ℕ}
    (hP : Computable (fun q : β × ℕ => decide (P q.1 q.2)))
    (hG : Computable (fun q : β × ℕ => G q.1 q.2)) (hK : Computable K) :
    Computable (fun b : β => ∑ e ∈ (Finset.range (K b)).filter (P b), G b e) := by
  have hproj : Computable (fun x : β × (ℕ × ℚ) => (x.1, x.2.1)) :=
    Computable.pair (f := fun x : β × (ℕ × ℚ) => x.1) (g := fun x : β × (ℕ × ℚ) => x.2.1)
      Computable.fst (Computable.fst.comp Computable.snd)
  have hc : Computable (fun x : β × (ℕ × ℚ) => decide (P x.1 x.2.1)) :=
    Computable.comp (f := fun q : β × ℕ => decide (P q.1 q.2))
      (g := fun x : β × (ℕ × ℚ) => (x.1, x.2.1)) hP hproj
  have hGx : Computable (fun x : β × (ℕ × ℚ) => G x.1 x.2.1) :=
    Computable.comp (f := fun q : β × ℕ => G q.1 q.2)
      (g := fun x : β × (ℕ × ℚ) => (x.1, x.2.1)) hG hproj
  have hg : Computable (fun x : β × (ℕ × ℚ) => x.2.2) := Computable.snd.comp Computable.snd
  have hf : Computable (fun x : β × (ℕ × ℚ) => x.2.2 + G x.1 x.2.1) :=
    Computable₂.comp (f := fun a b : ℚ => a + b) (g := fun x : β × (ℕ × ℚ) => x.2.2)
      (h := fun x : β × (ℕ × ℚ) => G x.1 x.2.1) computable₂_ratAdd hg hGx
  have hh : Computable₂ (fun (b : β) (p : ℕ × ℚ) =>
      bif decide (P b p.1) then p.2 + G b p.1 else p.2) :=
    Computable.cond (c := fun x : β × (ℕ × ℚ) => decide (P x.1 x.2.1))
      (f := fun x : β × (ℕ × ℚ) => x.2.2 + G x.1 x.2.1)
      (g := fun x : β × (ℕ × ℚ) => x.2.2) hc hf hg
  have h := Computable.nat_rec (f := K) (g := fun _ : β => (0 : ℚ))
    (h := fun (b : β) (p : ℕ × ℚ) => bif decide (P b p.1) then p.2 + G b p.1 else p.2)
    hK (Computable.const 0) hh
  exact h.of_eq (fun b =>
    (exists_isComputablyRandom_condK_le_dup_F6aux_sum_filter_eq (P b) (G b) (K b)).symm)

/-- `n ↦ (1/2)^n` is computable. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_halfpow_computable :
    Computable (fun n : ℕ => (1 / 2 : ℚ) ^ n) := by
  have hpow : Computable (fun n : ℕ => 2 ^ n) := comp_pow
  refine computable_of_num_den (N := fun _ => (1 : ℤ)) (D := fun n => 2 ^ n)
    (Computable.const 1) hpow (fun n => by positivity) (fun n => ?_)
  rw [one_div_pow]
  push_cast
  rfl

/-- The shift is computable. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_shift_computable :
    Computable exists_isComputablyRandom_condK_le_dup_shift :=
  computable_nat_size.comp (ComputableReals.primrec_intToNat.to_comp.comp computable_ratNum)

/-- The structural decoding of a rational (`Rat.instEncodable`) of a non-code is `none`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_decode_none (m : ℕ)
    (h : ¬ IsRatCode m) : (@Encodable.decode ℚ Rat.instEncodable m) = none := by
  unfold Rat.instEncodable
  rw [Encodable.decode_ofEquiv]
  simp only [Encodable.decode_sigma_val]
  have h1 : (Encodable.decode (Nat.unpair m).1 : Option ℤ) =
      some (Denumerable.ofNat ℤ (Nat.unpair m).1) := rfl
  rw [h1, Option.bind_some]
  have h2 : (Encodable.decode (Nat.unpair m).2 :
      Option {d : ℕ // 0 < d ∧ (Denumerable.ofNat ℤ (Nat.unpair m).1).natAbs.Coprime d}) = none :=
          by
    change (Encodable.decodeSubtype (Nat.unpair m).2) = none
    unfold Encodable.decodeSubtype
    have h3 : ¬ (0 < (Nat.unpair m).2 ∧
        (Denumerable.ofNat ℤ (Nat.unpair m).1).natAbs.Coprime (Nat.unpair m).2) := by
      rw [int_natAbs_ofNat]
      exact h
    change Option.bind (some (Nat.unpair m).2) _ = none
    rw [Option.bind_some, dite_eq_right h3]
  rw [h2]
  rfl

/-- The structural decoding of a rational with default `0` is `ratOfCode`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_decode_getD (m : ℕ) :
    (Encodable.decode (α := ℚ) m).getD 0 = ratOfCode m := by
  by_cases h : IsRatCode m
  · obtain ⟨q, hq⟩ := (mem_range_encodable_iff m).mpr h
    subst hq
    rw [Encodable.encodek, Option.getD_some]
    exact (ratOfCode_ratCode q).symm
  · have hz : ratOfCode m = 0 := by simp [ratOfCode, h]
    rw [hz, exists_isComputablyRandom_condK_le_dup_F6aux_decode_none m h]
    rfl

/-- `evOf` is computable, with all the data given by computable functions of a parameter. -/
private lemma exists_isComputablyRandom_condK_le_dup_F6aux_evOf_computable
    {β : Type} [Primcodable β] {PH : β → ℕ → ℕ → ℕ} {E : β → ℕ} {Y : β → BitString}
    (hPH : Computable (fun q : β × ℕ × ℕ => PH q.1 q.2.1 q.2.2))
    (hE : Computable E) (hY : Computable Y) :
    Computable (fun b : β =>
      exists_isComputablyRandom_condK_le_dup_evOf (PH b) (E b) (Y b)) := by
  have h1 : Computable (fun b : β => PH b (E b) (Encodable.encode (Y b))) :=
    hPH.comp (Computable.pair Computable.id (Computable.pair hE (Computable.encode.comp hY)))
  have h2 : Computable (fun b : β => ratOfCode (PH b (E b) (Encodable.encode (Y b)))) :=
    computable_ratOfCode.comp h1
  exact h2.of_eq (fun b =>
    (exists_isComputablyRandom_condK_le_dup_F6aux_decode_getD _).symm)

/-- Step 5b2 of the proof of `exists_isComputablyRandom_condK_le_dup`: the potential is
computable, uniformly in computable data. -/
private lemma exists_isComputablyRandom_condK_le_dup_step5b2_pot_computable
    {α : Type} [Primcodable α] {A : α → ℕ → Bool} {PH : α → ℕ → ℕ → ℕ}
    (hA : Computable (fun q : α × ℕ => A q.1 q.2))
    (hPH : Computable (fun q : α × ℕ × ℕ => PH q.1 q.2.1 q.2.2)) :
    Computable (fun q : α × ℕ × ℕ × BitString =>
      exists_isComputablyRandom_condK_le_dup_pot (A q.1) (PH q.1) q.2.1 q.2.2.1 q.2.2.2) := by
  -- `r = ((a, c, m, x), e)`: the context extended by the summation index `e`
  have hra : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ => r.1.1) :=
    Computable.fst.comp Computable.fst
  have hre : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ => r.2) := Computable.snd
  have hx : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ => r.1.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hm : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ => r.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hAe : Computable (fun q : ((α × ℕ × ℕ × BitString) × ℕ) × ℕ => A q.1.1.1 q.2) := by
    have hp : Computable (fun q : ((α × ℕ × ℕ × BitString) × ℕ) × ℕ => (q.1.1.1, q.2)) :=
      Computable.pair
        (f := fun q : ((α × ℕ × ℕ × BitString) × ℕ) × ℕ => q.1.1.1) (g := fun q => q.2)
        (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd
    exact Computable.comp (f := fun q : α × ℕ => A q.1 q.2)
      (g := fun q : ((α × ℕ × ℕ × BitString) × ℕ) × ℕ => (q.1.1.1, q.2)) hA hp
  have hPHe : Computable (fun q : ((α × ℕ × ℕ × BitString) × ℕ) × ℕ × ℕ =>
      PH q.1.1.1 q.2.1 q.2.2) := by
    have hp : Computable (fun q : ((α × ℕ × ℕ × BitString) × ℕ) × ℕ × ℕ => (q.1.1.1, q.2)) :=
      Computable.pair
        (f := fun q : ((α × ℕ × ℕ × BitString) × ℕ) × ℕ × ℕ => q.1.1.1) (g := fun q => q.2)
        (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd
    exact Computable.comp (f := fun q : α × ℕ × ℕ => PH q.1 q.2.1 q.2.2)
      (g := fun q : ((α × ℕ × ℕ × BitString) × ℕ) × ℕ × ℕ => (q.1.1.1, q.2)) hPH hp
  have hθ : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2) :=
    exists_isComputablyRandom_condK_le_dup_F6aux_theta_computable
      (β := (α × ℕ × ℕ × BitString) × ℕ) (A := fun r => A r.1.1) (PH := fun r => PH r.1.1)
      (J := fun r => r.2) hAe hPHe Computable.snd
  -- the predicate
  have hθle : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      decide (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2 ≤
        r.1.2.2.1)) :=
    Computable₂.comp (f := fun a b : ℕ => decide (a ≤ b))
      (g := fun r : (α × ℕ × ℕ × BitString) × ℕ =>
        exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2)
      (h := fun r : (α × ℕ × ℕ × BitString) × ℕ => r.1.2.2.1)
      Primrec.nat_le.decide.to_comp hθ hm
  have h2e1 : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ => 2 * r.2 + 1) :=
    Computable₂.comp (f := fun a b : ℕ => a + b)
      (g := fun r : (α × ℕ × ℕ × BitString) × ℕ => 2 * r.2) (h := fun _ => 1)
      Primrec.nat_add.to_comp
      (Computable₂.comp (f := fun a b : ℕ => a * b) (g := fun _ : (α × ℕ × ℕ × BitString) × ℕ => 2)
        (h := fun r => r.2) Primrec.nat_mul.to_comp (Computable.const 2) hre)
      (Computable.const 1)
  have hflag : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ => A r.1.1 (2 * r.2 + 1)) := by
    have hp : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ => (r.1.1, 2 * r.2 + 1)) :=
      Computable.pair (f := fun r : (α × ℕ × ℕ × BitString) × ℕ => r.1.1)
        (g := fun r => 2 * r.2 + 1) hra h2e1
    exact Computable.comp (f := fun q : α × ℕ => A q.1 q.2)
      (g := fun r : (α × ℕ × ℕ × BitString) × ℕ => (r.1.1, 2 * r.2 + 1)) hA hp
  have hP : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      decide (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2 ≤ r.1.2.2.1 ∧
        A r.1.1 (2 * r.2 + 1) = true)) :=
    (Computable₂.comp (f := fun a b : Bool => a && b)
      (g := fun r : (α × ℕ × ℕ × BitString) × ℕ =>
        decide (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2 ≤
          r.1.2.2.1))
      (h := fun r : (α × ℕ × ℕ × BitString) × ℕ => A r.1.1 (2 * r.2 + 1))
      (Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp hθle hflag).of_eq
      (fun r => by simp)
  -- the summand
  have hev : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2 r.1.2.2.2) :=
    exists_isComputablyRandom_condK_le_dup_F6aux_evOf_computable
      (β := (α × ℕ × ℕ × BitString) × ℕ) (PH := fun r => PH r.1.1) (E := fun r => r.2)
      (Y := fun r => r.1.2.2.2) hPHe hre hx
  have htake : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      r.1.2.2.2.take (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2)) :=
    Computable₂.comp (f := fun (n : ℕ) (l : BitString) => l.take n)
      (g := fun r : (α × ℕ × ℕ × BitString) × ℕ =>
        exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2)
      (h := fun r : (α × ℕ × ℕ × BitString) × ℕ => r.1.2.2.2)
      Primrec.list_take.to_comp hθ hx
  have hevt : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2
        (r.1.2.2.2.take
          (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2))) :=
    exists_isComputablyRandom_condK_le_dup_F6aux_evOf_computable
      (β := (α × ℕ × ℕ × BitString) × ℕ) (PH := fun r => PH r.1.1) (E := fun r => r.2)
      (Y := fun r => r.1.2.2.2.take
        (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2))
      hPHe hre htake
  have hsh : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      exists_isComputablyRandom_condK_le_dup_shift
        (exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2
          (r.1.2.2.2.take
            (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2)))) :=
    Computable.comp (f := exists_isComputablyRandom_condK_le_dup_shift)
      (g := fun r : (α × ℕ × ℕ × BitString) × ℕ =>
        exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2
          (r.1.2.2.2.take
            (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2)))
      exists_isComputablyRandom_condK_le_dup_F6aux_shift_computable hevt
  have hexp : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      r.2 + exists_isComputablyRandom_condK_le_dup_shift
        (exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2
          (r.1.2.2.2.take
            (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2)))) :=
    Computable₂.comp (f := fun a b : ℕ => a + b)
      (g := fun r : (α × ℕ × ℕ × BitString) × ℕ => r.2)
      (h := fun r : (α × ℕ × ℕ × BitString) × ℕ =>
        exists_isComputablyRandom_condK_le_dup_shift
          (exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2
            (r.1.2.2.2.take
              (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2))))
      Primrec.nat_add.to_comp hre hsh
  have hpw : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      (1 / 2 : ℚ) ^ (r.2 + exists_isComputablyRandom_condK_le_dup_shift
        (exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2
          (r.1.2.2.2.take
            (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2))))) :=
    Computable.comp (f := fun n : ℕ => (1 / 2 : ℚ) ^ n)
      (g := fun r : (α × ℕ × ℕ × BitString) × ℕ =>
        r.2 + exists_isComputablyRandom_condK_le_dup_shift
          (exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2
            (r.1.2.2.2.take
              (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2))))
      exists_isComputablyRandom_condK_le_dup_F6aux_halfpow_computable hexp
  have hG : Computable (fun r : (α × ℕ × ℕ × BitString) × ℕ =>
      (1 / 2 : ℚ) ^ (r.2 + exists_isComputablyRandom_condK_le_dup_shift
        (exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2
          (r.1.2.2.2.take
            (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2)))) *
        exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2 r.1.2.2.2) :=
    Computable₂.comp (f := fun a b : ℚ => a * b)
      (g := fun r : (α × ℕ × ℕ × BitString) × ℕ =>
        (1 / 2 : ℚ) ^ (r.2 + exists_isComputablyRandom_condK_le_dup_shift
          (exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2
            (r.1.2.2.2.take
              (exists_isComputablyRandom_condK_le_dup_theta (A r.1.1) (PH r.1.1) r.2)))))
      (h := fun r : (α × ℕ × ℕ × BitString) × ℕ =>
        exists_isComputablyRandom_condK_le_dup_evOf (PH r.1.1) r.2 r.1.2.2.2)
      computable₂_ratMul hpw hev
  exact exists_isComputablyRandom_condK_le_dup_F6aux_sum_filter_computable
    (β := α × ℕ × ℕ × BitString)
    (P := fun q e =>
      exists_isComputablyRandom_condK_le_dup_theta (A q.1) (PH q.1) e ≤ q.2.2.1 ∧
        A q.1 (2 * e + 1) = true)
    (G := fun q e =>
      (1 / 2 : ℚ) ^ (e + exists_isComputablyRandom_condK_le_dup_shift
        (exists_isComputablyRandom_condK_le_dup_evOf (PH q.1) e
          (q.2.2.2.take (exists_isComputablyRandom_condK_le_dup_theta (A q.1) (PH q.1) e)))) *
        exists_isComputablyRandom_condK_le_dup_evOf (PH q.1) e q.2.2.2)
    (K := fun q => q.2.1) hP hG (Computable.fst.comp Computable.snd)

/-- Strict comparison of rationals is computable (a `decide` form, reusable). -/
private lemma exists_isComputablyRandom_condK_le_dup_F7aux_ratLt :
    Computable₂ (fun a b : ℚ => decide (a < b)) :=
  (PrimrecRel.decide primrec_ratLt).to_comp

/-- The greedy prefix is the `Nat.rec` of its step function. -/
private lemma exists_isComputablyRandom_condK_le_dup_F7aux_run_eq_rec (a : ℕ → Bool)
    (ph : ℕ → ℕ → ℕ) (cut : ℕ → ℕ) (n : ℕ) :
    Nat.rec (motive := fun _ => BitString) []
      (fun y IH => IH ++ [exists_isComputablyRandom_condK_le_dup_next a ph cut y IH]) n =
      exists_isComputablyRandom_condK_le_dup_run a ph cut n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exists_isComputablyRandom_condK_le_dup_run, ← ih]

/-- Step 5b3 of the proof of `exists_isComputablyRandom_condK_le_dup`: the greedy prefix
is
computable, uniformly in computable data. -/
private lemma exists_isComputablyRandom_condK_le_dup_step5b3_run_computable
    {α : Type} [Primcodable α] {A : α → ℕ → Bool} {PH : α → ℕ → ℕ → ℕ} {CUT : α → ℕ → ℕ}
    (hA : Computable (fun q : α × ℕ => A q.1 q.2))
    (hPH : Computable (fun q : α × ℕ × ℕ => PH q.1 q.2.1 q.2.2))
    (hCUT : Computable (fun q : α × ℕ => CUT q.1 q.2)) :
    Computable (fun q : α × ℕ =>
      exists_isComputablyRandom_condK_le_dup_run (A q.1) (PH q.1) (CUT q.1) q.2) := by
  have hpar : Computable (fun r : (α × ℕ) × (ℕ × BitString) => r.1.1) :=
    Computable.fst.comp Computable.fst
  have hpar2 : Computable (fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ => s.1.1.1) :=
    Computable.comp (f := fun r : (α × ℕ) × (ℕ × BitString) => r.1.1)
      (g := fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ => s.1) hpar Computable.fst
  have hpar3 : Computable (fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ × ℕ => s.1.1.1) :=
    Computable.comp (f := fun r : (α × ℕ) × (ℕ × BitString) => r.1.1)
      (g := fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ × ℕ => s.1) hpar Computable.fst
  have hA' : Computable (fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ => A s.1.1.1 s.2) :=
    Computable.comp (f := fun q : α × ℕ => A q.1 q.2)
      (g := fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ => (s.1.1.1, s.2)) hA
      (Computable.pair hpar2 Computable.snd)
  have hs1 : Computable (fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ × ℕ => s.2.1) :=
    Computable.comp (f := fun p : ℕ × ℕ => p.1) (g := fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ ×
        ℕ => s.2)
      Computable.fst Computable.snd
  have hs2 : Computable (fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ × ℕ => s.2.2) :=
    Computable.comp (f := fun p : ℕ × ℕ => p.2) (g := fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ ×
        ℕ => s.2)
      Computable.snd Computable.snd
  have hPH' : Computable
      (fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ × ℕ => PH s.1.1.1 s.2.1 s.2.2) :=
    Computable.comp (f := fun q : α × ℕ × ℕ => PH q.1 q.2.1 q.2.2)
      (g := fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ × ℕ => (s.1.1.1, s.2.1, s.2.2)) hPH
      (Computable.pair hpar3 (Computable.pair hs1 hs2))
  have hpot := exists_isComputablyRandom_condK_le_dup_step5b2_pot_computable
    (α := (α × ℕ) × (ℕ × BitString)) (A := fun r => A r.1.1) (PH := fun r => PH r.1.1) hA' hPH'
  have hr1 : Computable (fun r : (α × ℕ) × (ℕ × BitString) => r.2.1) :=
    Computable.comp (f := fun p : ℕ × BitString => p.1)
      (g := fun r : (α × ℕ) × (ℕ × BitString) => r.2) Computable.fst Computable.snd
  have hr2 : Computable (fun r : (α × ℕ) × (ℕ × BitString) => r.2.2) :=
    Computable.comp (f := fun p : ℕ × BitString => p.2)
      (g := fun r : (α × ℕ) × (ℕ × BitString) => r.2) Computable.snd Computable.snd
  have hm : Computable (fun r : (α × ℕ) × (ℕ × BitString) => r.2.1 + 1) :=
    Computable.comp (f := Nat.succ) (g := fun r : (α × ℕ) × (ℕ × BitString) => r.2.1)
      Primrec.succ.to_comp hr1
  have hc : Computable (fun r : (α × ℕ) × (ℕ × BitString) => CUT r.1.1 (r.2.1 + 1)) :=
    Computable.comp (f := fun q : α × ℕ => CUT q.1 q.2)
      (g := fun r : (α × ℕ) × (ℕ × BitString) => (r.1.1, r.2.1 + 1)) hCUT
      (Computable.pair hpar hm)
  have hx : ∀ b : Bool, Computable (fun r : (α × ℕ) × (ℕ × BitString) => r.2.2 ++ [b]) :=
    fun b => Computable₂.comp (f := fun (l : BitString) (a : Bool) => l ++ [a])
      (g := fun r : (α × ℕ) × (ℕ × BitString) => r.2.2)
      (h := fun _ : (α × ℕ) × (ℕ × BitString) => b) Computable.list_concat hr2
      (Computable.const b)
  have hpotb : ∀ b : Bool, Computable (fun r : (α × ℕ) × (ℕ × BitString) =>
      exists_isComputablyRandom_condK_le_dup_pot (A r.1.1) (PH r.1.1) (CUT r.1.1 (r.2.1 + 1))
        (r.2.1 + 1) (r.2.2 ++ [b])) :=
    fun b => Computable.comp
      (f := fun s : ((α × ℕ) × (ℕ × BitString)) × ℕ × ℕ × BitString =>
        exists_isComputablyRandom_condK_le_dup_pot (A s.1.1.1) (PH s.1.1.1) s.2.1 s.2.2.1
          s.2.2.2)
      (g := fun r : (α × ℕ) × (ℕ × BitString) =>
        (r, CUT r.1.1 (r.2.1 + 1), r.2.1 + 1, r.2.2 ++ [b])) hpot
      (Computable.pair Computable.id (Computable.pair hc (Computable.pair hm (hx b))))
  have hnext : Computable (fun r : (α × ℕ) × (ℕ × BitString) =>
      exists_isComputablyRandom_condK_le_dup_next (A r.1.1) (PH r.1.1) (CUT r.1.1)
        r.2.1 r.2.2) :=
    (Computable₂.comp (f := fun a b : ℚ => decide (a < b))
      (g := fun r : (α × ℕ) × (ℕ × BitString) =>
        exists_isComputablyRandom_condK_le_dup_pot (A r.1.1) (PH r.1.1) (CUT r.1.1 (r.2.1 + 1))
          (r.2.1 + 1) (r.2.2 ++ [true]))
      (h := fun r : (α × ℕ) × (ℕ × BitString) =>
        exists_isComputablyRandom_condK_le_dup_pot (A r.1.1) (PH r.1.1) (CUT r.1.1 (r.2.1 + 1))
          (r.2.1 + 1) (r.2.2 ++ [false]))
      exists_isComputablyRandom_condK_le_dup_F7aux_ratLt (hpotb true) (hpotb false)).of_eq
      (fun r => rfl)
  have hh : Computable₂ (fun (q : α × ℕ) (p : ℕ × BitString) =>
      p.2 ++ [exists_isComputablyRandom_condK_le_dup_next (A q.1) (PH q.1) (CUT q.1)
        p.1 p.2]) :=
    Computable₂.comp (f := fun (l : BitString) (a : Bool) => l ++ [a])
      (g := fun r : (α × ℕ) × (ℕ × BitString) => r.2.2)
      (h := fun r : (α × ℕ) × (ℕ × BitString) =>
        exists_isComputablyRandom_condK_le_dup_next (A r.1.1) (PH r.1.1) (CUT r.1.1)
          r.2.1 r.2.2) Computable.list_concat hr2 hnext
  have hrec := Computable.nat_rec (f := fun q : α × ℕ => q.2)
    (g := fun _ : α × ℕ => ([] : BitString))
    (h := fun (q : α × ℕ) (p : ℕ × BitString) =>
      p.2 ++ [exists_isComputablyRandom_condK_le_dup_next (A q.1) (PH q.1) (CUT q.1)
        p.1 p.2])
    Computable.snd (Computable.const []) hh
  exact hrec.of_eq (fun q =>
    exists_isComputablyRandom_condK_le_dup_F7aux_run_eq_rec (A q.1) (PH q.1) (CUT q.1) q.2)

/-- Auxiliary (F8): the list of all bit strings of length `≤ n` is primitive recursive in `n`. -/
private lemma exists_isComputablyRandom_condK_le_dup_F8aux_strings_primrec :
    Primrec exists_isComputablyRandom_condK_le_dup_strings := by
  have hf : Primrec₂ (fun (_ : ℕ) (l : List BitString) =>
      ([] : BitString) :: l.flatMap (fun x => [false :: x, true :: x])) := by
    refine Primrec.list_cons.comp (Primrec.const []) ?_
    refine Primrec.list_flatMap Primrec.snd ?_
    refine Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.snd) ?_
    exact Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
      (Primrec.const [])
  have h := Primrec.nat_rec₁ (α := List BitString) [[]] hf
  refine h.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ n ih =>
    change ([] : BitString) :: (Nat.rec (motive := fun _ => List BitString) [[]]
        (fun (_ : ℕ) (l : List BitString) =>
          ([] : BitString) :: l.flatMap (fun x => [false :: x, true :: x])) n).flatMap
        (fun x => [false :: x, true :: x]) = _
    rw [ih]
    rfl

/-- Auxiliary (F8): `List.all` is primitive recursive. -/
private lemma exists_isComputablyRandom_condK_le_dup_F8aux_list_all {α β : Type}
    [Primcodable α] [Primcodable β] {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).all (p a)) := by
  refine (Primrec.list_foldr (h := fun a (q : β × Bool) => p a q.1 && q.2) hf
    (Primrec.const true) ?_).of_eq (fun a => ?_)
  · exact Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  · induction f a with
    | nil => rfl
    | cons b l ih =>
      simp only [List.foldr_cons, List.all_cons] at ih ⊢
      rw [ih]

/-- Auxiliary (F8): the `s`-step evaluation of the `e`-th code is primitive recursive. -/
private lemma exists_isComputablyRandom_condK_le_dup_F8aux_evaln_primrec {γ : Type}
    [Primcodable γ] {fs fe fj : γ → ℕ} (hs : Primrec fs) (he : Primrec fe) (hj : Primrec fj) :
    Primrec (fun c => Nat.Partrec.Code.evaln (fs c) (Denumerable.ofNat Nat.Partrec.Code (fe c))
      (fj c)) :=
  Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair hs ((Primrec.ofNat Nat.Partrec.Code).comp he)) hj)

/-- Auxiliary (F8): the halting test of the simulation is primitive recursive. -/
private lemma exists_isComputablyRandom_condK_le_dup_F8aux_good_primrec :
    Primrec (fun q : ℕ × BitString × ℕ =>
      exists_isComputablyRandom_condK_le_dup_good q.1 q.2.1 q.2.2) := by
  have hp : Primrec (fun q : ℕ × BitString × ℕ => q.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun q : ℕ × BitString × ℕ => q.2.2) := Primrec.snd.comp Primrec.snd
  have hL : Primrec (fun q : ℕ × BitString × ℕ => q.2.1.length / 2) :=
    Primrec.nat_div.comp (Primrec.list_length.comp hp) (Primrec.const 2)
  have hrange : Primrec (fun q : ℕ × BitString × ℕ => List.range (q.2.1.length / 2)) :=
    Primrec.list_range.comp hL
  have hstr : Primrec (fun q : ℕ × BitString × ℕ =>
      exists_isComputablyRandom_condK_le_dup_strings q.2.2) :=
    exists_isComputablyRandom_condK_le_dup_F8aux_strings_primrec.comp hn
  -- the part over `j`
  have hq : Primrec (fun r : (ℕ × BitString × ℕ) × ℕ => r.1) := Primrec.fst
  have hs1 : Primrec (fun t : ((ℕ × BitString × ℕ) × ℕ) × ℕ => t.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have he1 : Primrec (fun t : ((ℕ × BitString × ℕ) × ℕ) × ℕ => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hj1 : Primrec (fun t : ((ℕ × BitString × ℕ) × ℕ) × ℕ => t.2) := Primrec.snd
  have hjall : Primrec (fun r : (ℕ × BitString × ℕ) × ℕ =>
      (List.range (r.1.2.1.length / 2)).all (fun j =>
        (Nat.Partrec.Code.evaln r.1.1 (Denumerable.ofNat Nat.Partrec.Code r.2) j).isSome)) := by
    refine exists_isComputablyRandom_condK_le_dup_F8aux_list_all
      (f := fun r : (ℕ × BitString × ℕ) × ℕ => List.range (r.1.2.1.length / 2))
      (p := fun (r : (ℕ × BitString × ℕ) × ℕ) (j : ℕ) =>
        (Nat.Partrec.Code.evaln r.1.1 (Denumerable.ofNat Nat.Partrec.Code r.2) j).isSome)
      (hrange.comp hq) ?_
    exact Primrec.option_isSome.comp
      (exists_isComputablyRandom_condK_le_dup_F8aux_evaln_primrec hs1 he1 hj1)
  -- the part over `x`
  have hs2 : Primrec (fun t : ((ℕ × BitString × ℕ) × ℕ) × BitString => t.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have he2 : Primrec (fun t : ((ℕ × BitString × ℕ) × ℕ) × BitString => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hj2 : Primrec (fun t : ((ℕ × BitString × ℕ) × ℕ) × BitString => Encodable.encode t.2) :=
    Primrec.encode.comp Primrec.snd
  have hxall : Primrec (fun r : (ℕ × BitString × ℕ) × ℕ =>
      (exists_isComputablyRandom_condK_le_dup_strings r.1.2.2).all (fun x =>
        (Nat.Partrec.Code.evaln r.1.1 (Denumerable.ofNat Nat.Partrec.Code r.2)
          (Encodable.encode x)).isSome)) := by
    refine exists_isComputablyRandom_condK_le_dup_F8aux_list_all
      (f := fun r : (ℕ × BitString × ℕ) × ℕ =>
        exists_isComputablyRandom_condK_le_dup_strings r.1.2.2)
      (p := fun (r : (ℕ × BitString × ℕ) × ℕ) (x : BitString) =>
        (Nat.Partrec.Code.evaln r.1.1 (Denumerable.ofNat Nat.Partrec.Code r.2)
          (Encodable.encode x)).isSome)
      (hstr.comp hq) ?_
    exact Primrec.option_isSome.comp
      (exists_isComputablyRandom_condK_le_dup_F8aux_evaln_primrec hs2 he2 hj2)
  -- the flags
  have hflag0 : Primrec (fun r : (ℕ × BitString × ℕ) × ℕ => r.1.2.1.getD (2 * r.2) false) :=
    (Primrec.list_getD false).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
  have hflag1 : Primrec (fun r : (ℕ × BitString × ℕ) × ℕ => r.1.2.1.getD (2 * r.2 + 1) false) :=
    (Primrec.list_getD false).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))
  have hbody : Primrec (fun r : (ℕ × BitString × ℕ) × ℕ =>
      (!(r.1.2.1.getD (2 * r.2) false) || (List.range (r.1.2.1.length / 2)).all (fun j =>
        (Nat.Partrec.Code.evaln r.1.1 (Denumerable.ofNat Nat.Partrec.Code r.2) j).isSome)) &&
      (!(r.1.2.1.getD (2 * r.2 + 1) false) ||
        (exists_isComputablyRandom_condK_le_dup_strings r.1.2.2).all (fun x =>
          (Nat.Partrec.Code.evaln r.1.1 (Denumerable.ofNat Nat.Partrec.Code r.2)
            (Encodable.encode x)).isSome))) :=
    Primrec.and.comp (Primrec.or.comp (Primrec.not.comp hflag0) hjall)
      (Primrec.or.comp (Primrec.not.comp hflag1) hxall)
  exact exists_isComputablyRandom_condK_le_dup_F8aux_list_all
    (f := fun q : ℕ × BitString × ℕ => List.range (q.2.1.length / 2))
    (p := fun (q : ℕ × BitString × ℕ) (e : ℕ) =>
      (!(q.2.1.getD (2 * e) false) || (List.range (q.2.1.length / 2)).all (fun j =>
        (Nat.Partrec.Code.evaln q.1 (Denumerable.ofNat Nat.Partrec.Code e) j).isSome)) &&
      (!(q.2.1.getD (2 * e + 1) false) ||
        (exists_isComputablyRandom_condK_le_dup_strings q.2.2).all (fun x =>
          (Nat.Partrec.Code.evaln q.1 (Denumerable.ofNat Nat.Partrec.Code e)
            (Encodable.encode x)).isSome)))
    hrange hbody

/-- Step 5b4 of the proof of `exists_isComputablyRandom_condK_le_dup`: the halting test of
the simulation is computable. -/
private lemma exists_isComputablyRandom_condK_le_dup_step5b4_good_computable :
    Computable (fun q : ℕ × BitString × ℕ =>
      exists_isComputablyRandom_condK_le_dup_good q.1 q.2.1 q.2.2) :=
  exists_isComputablyRandom_condK_le_dup_F8aux_good_primrec.to_comp

/-- Step 5b of the proof of `exists_isComputablyRandom_condK_le_dup`: the simulation is a
total computable function of `(s, p, n)`. -/
private lemma exists_isComputablyRandom_condK_le_dup_sim_computable :
    Computable (fun q : ℕ × BitString × ℕ =>
      exists_isComputablyRandom_condK_le_dup_sim q.1 q.2.1 q.2.2) := by
  have hA : Computable (fun q : (ℕ × BitString) × ℕ => q.1.2.getD q.2 false) :=
    ((Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to_comp
  have hPH : Computable (fun q : (ℕ × BitString) × ℕ × ℕ =>
      exists_isComputablyRandom_condK_le_dup_phS q.1.1 q.2.1 q.2.2) := by
    have h : Primrec (fun q : (ℕ × BitString) × ℕ × ℕ =>
        (Nat.Partrec.Code.evaln q.1.1 (Denumerable.ofNat Nat.Partrec.Code q.2.1) q.2.2).getD 0) :=
      Primrec.option_getD.comp
        (exists_isComputablyRandom_condK_le_dup_F8aux_evaln_primrec
          (fs := fun q : (ℕ × BitString) × ℕ × ℕ => q.1.1)
          (fe := fun q : (ℕ × BitString) × ℕ × ℕ => q.2.1)
          (fj := fun q : (ℕ × BitString) × ℕ × ℕ => q.2.2)
          (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))
        (Primrec.const 0)
    exact h.to_comp
  have hCUT : Computable (fun q : (ℕ × BitString) × ℕ => min (q.1.2.length / 2) (q.2 + 1)) := by
    have h : Primrec (fun q : (ℕ × BitString) × ℕ => min (q.1.2.length / 2) (q.2 + 1)) :=
      Primrec.nat_min.comp
        (Primrec.nat_div.comp
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 2))
        (Primrec.succ.comp Primrec.snd)
    exact h.to_comp
  have h3 := exists_isComputablyRandom_condK_le_dup_step5b3_run_computable
    (α := ℕ × BitString) (A := fun q i => q.2.getD i false)
    (PH := fun q e j => exists_isComputablyRandom_condK_le_dup_phS q.1 e j)
    (CUT := fun q m => min (q.2.length / 2) (m + 1)) hA hPH hCUT
  have hmap : Computable (fun q : ℕ × BitString × ℕ => ((q.1, q.2.1), q.2.2)) :=
    Computable.pair (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  have hrun := h3.comp hmap
  have hsome := Computable.option_some.comp hrun
  have hcond := Computable.cond exists_isComputablyRandom_condK_le_dup_step5b4_good_computable
    hsome (Computable.const (none : Option BitString))
  refine hcond.of_eq (fun q => ?_)
  unfold exists_isComputablyRandom_condK_le_dup_sim
  cases h : exists_isComputablyRandom_condK_le_dup_good q.1 q.2.1 q.2.2 <;> simp

/-- The partial recursive decoder: search the number of steps. -/
private lemma exists_isComputablyRandom_condK_le_dup_decoder :
    ∃ g : BitString → BitString →. BitString,
      Partrec (fun q : BitString × BitString => g q.1 q.2) ∧
      ∀ n, cantorPrefix (exists_isComputablyRandom_condK_le_dup_seq
        exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph) n ∈
        g (natBits n) (exists_isComputablyRandom_condK_le_dup_adv n) := by
  refine ⟨fun y p => Nat.rfindOpt (fun s =>
    exists_isComputablyRandom_condK_le_dup_sim s p (decodeBits y)), ?_, ?_⟩
  · have h5 := exists_isComputablyRandom_condK_le_dup_sim_computable
    have hdb : Computable (fun r : (BitString × BitString) × ℕ => decodeBits r.1.1) :=
      decodeBits_computable.comp (Computable.fst.comp Computable.fst)
    have hp : Computable (fun r : (BitString × BitString) × ℕ => r.1.2) :=
      Computable.snd.comp Computable.fst
    have hcomp : Computable (fun r : (BitString × BitString) × ℕ =>
        (r.2, r.1.2, decodeBits r.1.1)) :=
      Computable.pair Computable.snd (Computable.pair hp hdb)
    have key : Computable (fun r : (BitString × BitString) × ℕ =>
        exists_isComputablyRandom_condK_le_dup_sim r.2 r.1.2 (decodeBits r.1.1)) :=
      Computable.comp (f := fun q : ℕ × BitString × ℕ =>
        exists_isComputablyRandom_condK_le_dup_sim q.1 q.2.1 q.2.2)
        (g := fun r : (BitString × BitString) × ℕ => (r.2, r.1.2, decodeBits r.1.1)) h5 hcomp
    exact Partrec.rfindOpt (f := fun (q : BitString × BitString) (s : ℕ) =>
      exists_isComputablyRandom_condK_le_dup_sim s q.2 (decodeBits q.1)) key
  · intro n
    obtain ⟨⟨s, hs⟩, hsound⟩ := exists_isComputablyRandom_condK_le_dup_sim_spec n
    have hdec : decodeBits (natBits n) = n := decodeBits_natBits n
    change _ ∈ Nat.rfindOpt (fun s => exists_isComputablyRandom_condK_le_dup_sim s
      (exists_isComputablyRandom_condK_le_dup_adv n) (decodeBits (natBits n)))
    rw [hdec]
    have hdom : (Nat.rfindOpt (fun s => exists_isComputablyRandom_condK_le_dup_sim s
        (exists_isComputablyRandom_condK_le_dup_adv n) n)).Dom :=
      Nat.rfindOpt_dom.2 ⟨s, _, Option.mem_def.mpr hs⟩
    obtain ⟨s', hs'⟩ := Nat.rfindOpt_spec (Part.get_mem hdom)
    have hval := hsound s' _ (Option.mem_def.mp hs')
    rw [← hval]
    exact Part.get_mem hdom

/-- An output of a partial recursive map costs at most the length of the program plus a constant. -/
private lemma exists_isComputablyRandom_condK_le_dup_condK_le (V : Map)
    (hV : isOptimalConditional V) (g : BitString → BitString →. BitString)
    (hg : Partrec (fun q : BitString × BitString => g q.1 q.2)) :
    ∃ C : ℕ, ∀ (y p w : BitString), w ∈ g y p → condK V w y ≤ (p.length : ℕ∞) + (C : ℕ∞) := by
  set D : Map := fun pr => g pr.2 pr.1 with hDdef
  have hD_decomp : isDecompressor D :=
    hg.comp (Computable.pair Computable.snd Computable.fst)
  obtain ⟨C, hC⟩ := hV.2 D hD_decomp
  refine ⟨C, fun y p w hw => ?_⟩
  have hprod : produces D p y w := by
    simp only [produces, hDdef]; exact hw
  calc condK V w y ≤ condK D w y + (C : ℕ∞) := hC w y
    _ ≤ (p.length : ℕ∞) + (C : ℕ∞) := by
      have : condK D w y ≤ (p.length : ℕ∞) :=
        sInf_le ⟨p, hprod, rfl⟩
      gcongr
/-- Step 1 of the backward proof hint of `isComputablyRandom_iff_rational`: Average with the
constant 1.
For a computable fair capital `m`, `(m+1)/2` is a computable fair capital `≥ 1/2` that wins wherever
`m` wins. -/
private lemma exists_isComputablyRandom_condK_le_dup_rr_avg
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (m : BitString → ℝ) (hm : IsComputableOnStrings m) (hfair : IsFairCapital π m) :
    IsComputableOnStrings (fun x => (m x + 1) / 2) ∧
    IsFairCapital π (fun x => (m x + 1) / 2) ∧
    (∀ x, 1 / 2 ≤ (m x + 1) / 2) ∧
    (∀ w, Wins m w → Wins (fun x => (m x + 1) / 2) w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq, hqerr⟩ := hm
    refine ⟨fun p => (q p + 1) / 2, ?_, ?_⟩
    · have h1 : Computable (fun p : BitString × ℕ => q p + 1) :=
        Computable₂.comp computable₂_ratAdd hq (Computable.const 1)
      exact computable_ratHalf.comp h1
    · intro x s
      have h := hqerr x s
      have h2 : (2:ℝ)⁻¹ ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h3 : (0:ℝ) ≤ (2:ℝ)⁻¹ ^ s := by positivity
      have h4 : |((q (x, s) : ℝ) + 1) / 2 - (m x + 1) / 2| = |(q (x, s) : ℝ) - m x| / 2 := by
        rw [show (((q (x, s) : ℝ) + 1) / 2 - (m x + 1) / 2) = ((q (x, s) : ℝ) - m x) / 2 by ring,
          abs_div]
        norm_num
      push_cast
      rw [h4]
      linarith
  · refine ⟨fun x => ?_, fun x => ?_⟩
    · have := hfair.nonneg x
      change 0 ≤ (m x + 1) / 2
      linarith
    · have h := hfair.fair x
      have hadd := massR_add (π := π) x
      change (m x + 1) / 2 * massR π x = (m (x ++ [false]) + 1) / 2 * massR π (x ++ [false]) +
        (m (x ++ [true]) + 1) / 2 * massR π (x ++ [true])
      linear_combination (1 / 2 : ℝ) * h + (1 / 2 : ℝ) * hadd
  · intro x
    have := hfair.nonneg x
    linarith
  · intro w hw hb
    apply hw
    obtain ⟨B, hB⟩ := hb
    refine ⟨2 * B - 1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 := hB ⟨n, rfl⟩
    simp only at h1 ⊢
    linarith

/-- division by a computable positive-valued function -/
private lemma exists_isComputablyRandom_condK_le_dup_rr_ic_div_pos {α : Type*} [Primcodable α]
    {f d : α → ℚ}
    (hf : Computable f) (hd : Computable d) (hdpos : ∀ a, 0 < d a) :
    Computable (fun a => f a / d a) := by
  have hnum : Computable (fun a => (f a).num * ((d a).den : ℤ)) :=
    Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp hf)
      (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp hd))
  have hden : Computable (fun a => (f a).den * (d a).num.toNat) :=
    Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp hf)
      (ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp hd))
  refine computable_of_num_den (f := fun a => f a / d a) hnum hden (fun a => ?_) (fun a => ?_)
  · exact Nat.mul_pos (f a).pos (by have := Rat.num_pos.2 (hdpos a); omega)
  · have h1 : ((f a).num : ℚ) = f a * ((f a).den : ℚ) := (Rat.mul_den_eq_num (f a)).symm
    have h2 : ((d a).num : ℚ) = d a * ((d a).den : ℚ) := (Rat.mul_den_eq_num (d a)).symm
    have h3 : (((d a).num.toNat : ℕ) : ℚ) = ((d a).num : ℚ) := by
      have hh : ((d a).num.toNat : ℤ) = (d a).num :=
        Int.toNat_of_nonneg (Rat.num_pos.2 (hdpos a)).le
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hh
    have hd1 : ((f a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (f a).den_nz
    have hd2 : ((d a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (d a).den_nz
    have hda : d a ≠ 0 := (hdpos a).ne'
    push_cast
    rw [h3, h1, h2]
    field_simp

private lemma exists_isComputablyRandom_condK_le_dup_rr_ic_half_pow : Computable
    (fun a : ℕ => (1 / 2 : ℚ) ^ a) := by
  refine computable_of_num_den (N := fun _ => (1 : ℤ)) (D := fun a : ℕ => 2 ^ a)
    (Computable.const _) comp_pow (fun a => by positivity) (fun a => ?_)
  push_cast
  rw [one_div_pow]

/-- Relative error of a quotient of approximations. -/
private lemma exists_isComputablyRandom_condK_le_dup_rr_ic_ratio_err (A B a b ρ0 ρ δ : ℝ)
    (hB : 1 / 2 ≤ B) (hA : 0 ≤ A) (hρ0 : 0 < ρ0)
    (hρ : ρ0 ≤ ρ) (hAB : A * ρ0 ≤ B * ρ) (hδ : δ ≤ 1 / 4) (ha : |a - A| ≤ δ) (hb : |b - B| ≤ δ) :
    |a * ρ0 / (b * ρ) - A * ρ0 / (B * ρ)| ≤ 8 * δ := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) ha
  have hb4 : 1 / 4 ≤ b := by linarith
  have hbpos : 0 < b := by linarith
  have hBpos : 0 < B := by linarith
  have hρpos : 0 < ρ := lt_of_lt_of_le hρ0 hρ
  have hden : 0 < ρ * b * B := by positivity
  have hrw : a * ρ0 / (b * ρ) - A * ρ0 / (B * ρ) = ρ0 * (a * B - A * b) / (ρ * b * B) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hden, div_le_iff₀ hden, abs_mul, abs_of_pos hρ0]
  have hnum : |a * B - A * b| ≤ δ * (B + A) := by
    rw [abs_le]
    constructor <;> nlinarith
  have hkey : ρ * B ≤ 4 * (ρ * b * B) := by
    nlinarith [mul_nonneg (mul_pos hρpos hBpos).le (show 0 ≤ 4 * b - 1 by linarith)]
  have h1 : ρ0 * B ≤ 4 * (ρ * b * B) := by
    have : ρ0 * B ≤ ρ * B := by gcongr
    linarith
  have h2 : A * ρ0 ≤ 4 * (ρ * b * B) := by
    have : B * ρ = ρ * B := by ring
    linarith
  calc ρ0 * |a * B - A * b| ≤ ρ0 * (δ * (B + A)) := by gcongr
    _ = δ * (ρ0 * B) + δ * (A * ρ0) := by ring
    _ ≤ δ * (4 * (ρ * b * B)) + δ * (4 * (ρ * b * B)) := by gcongr
    _ = 8 * δ * (ρ * b * B) := by ring

/-- The pointwise rational choice. -/
private lemma exists_isComputablyRandom_condK_le_dup_rr_ic_pointwise (q0 Q ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 4)
    (hQ : |Q - q0| ≤ ε / 4) :
    (1 - ε) * q0 ≤ (1 - ε) * Q + ε / 2 ∧
      (1 - ε) * (1 - q0) ≤ 1 - ((1 - ε) * Q + ε / 2) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hQ
  have h3 : 0 ≤ 1 - ε := by linarith
  constructor <;> nlinarith [mul_nonneg h3 (show 0 ≤ Q - q0 + ε / 4 by linarith),
    mul_nonneg h3 (show 0 ≤ ε / 4 - (Q - q0) by linarith)]

/-- Step 2a of the backward proof hint of `isComputablyRandom_iff_rational`: Computable rational
proportion rule with relative accuracy. -/
private lemma exists_isComputablyRandom_condK_le_dup_rr_prop
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : ∃ r : BitString → ℚ, Computable r ∧ ∀ x, 0 < r x ∧ massR π x = r x)
    (m : BitString → ℝ) (hm : IsComputableOnStrings m) (hfair : IsFairCapital π m) (hhalf : ∀ x, 1 /
        2 ≤ m x) :
    ∃ p : BitString × Bool → ℚ, Computable p ∧ ∀ x, p (x, false) + p (x, true) = 1 ∧
      ∀ b, (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * (m (x ++ [b]) * massR π (x ++ [b]) /
          (m x * massR π x)) ≤ (p (x, b) : ℝ) := by
  obtain ⟨r, hrc, hrpos⟩ := hπ
  obtain ⟨q, hqc, hq⟩ := hm
  let s : BitString → ℕ := fun x => x.length + 7
  let a : BitString → ℚ := fun x => q (x ++ [false], s x)
  let bb : BitString → ℚ := fun x => q (x, s x)
  let ε : BitString → ℚ := fun x => (1 / 2 : ℚ) ^ (x.length + 2)
  let D : BitString → ℚ := fun x => bb x * r x
  let Q : BitString → ℚ := fun x => (a x * r (x ++ [false])) / D x
  let P0 : BitString → ℚ := fun x => (1 - ε x) * Q x + ε x / 2
  have hmr : ∀ y, massR π y = (r y : ℝ) := fun y => (hrpos y).2
  have hrpos' : ∀ y, (0 : ℝ) < (r y : ℝ) := fun y => by exact_mod_cast (hrpos y).1
  have hδle : ∀ n : ℕ, (2 : ℝ)⁻¹ ^ (n + 7) ≤ 1 / 128 := by
    intro n
    have : (2 : ℝ)⁻¹ ^ (n + 7) ≤ (2 : ℝ)⁻¹ ^ 7 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    refine this.trans ?_
    norm_num
  have hbge : ∀ x, (1 : ℝ) / 4 ≤ (bb x : ℝ) := by
    intro x
    have h1 := hq x (s x)
    have h2 := hδle x.length
    have h3 := hhalf x
    obtain ⟨h4, _⟩ := abs_le.mp h1
    change (1 : ℝ) / 4 ≤ (q (x, x.length + 7) : ℝ)
    linarith
  have hDpos : ∀ x, 0 < D x := by
    intro x
    have h1 : (0 : ℝ) < (bb x : ℝ) := by linarith [hbge x]
    have h2 : (0 : ℚ) < bb x := by exact_mod_cast h1
    exact mul_pos h2 (hrpos x).1
  refine ⟨fun y => cond y.2 (1 - P0 y.1) (P0 y.1), ?_, ?_⟩
  · -- computability
    have hlen : Computable (fun x : BitString => x.length) := Computable.list_length
    have hs : Computable s := Primrec.nat_add.to_comp.comp hlen (Computable.const 7)
    have hcat : Computable (fun x : BitString => x ++ [false]) :=
      Computable.list_concat.comp Computable.id (Computable.const false)
    have ha : Computable a := hqc.comp (hcat.pair hs)
    have hbb : Computable bb := hqc.comp (Computable.id.pair hs)
    have hr0 : Computable (fun x : BitString => r (x ++ [false])) := hrc.comp hcat
    have hD : Computable D := Computable₂.comp computable₂_ratMul hbb hrc
    have hQ : Computable Q :=
      exists_isComputablyRandom_condK_le_dup_rr_ic_div_pos (Computable₂.comp computable₂_ratMul ha
          hr0) hD hDpos
    have hε : Computable ε :=
      exists_isComputablyRandom_condK_le_dup_rr_ic_half_pow.comp (Primrec.nat_add.to_comp.comp hlen
          (Computable.const 2))
    have hP0 : Computable P0 :=
      Computable₂.comp computable₂_ratAdd
        (Computable₂.comp computable₂_ratMul
          (Computable₂.comp computable₂_ratSub (Computable.const 1) hε) hQ)
        (computable_ratHalf.comp hε)
    have hP0' : Computable (fun y : BitString × Bool => P0 y.1) := hP0.comp Computable.fst
    exact Computable.cond Computable.snd
      (Computable₂.comp computable₂_ratSub (Computable.const 1) hP0') hP0'
  · intro x
    refine ⟨by simp, fun b => ?_⟩
    -- real facts at x
    have hadd := massR_add (π := π) x
    have hfx := hfair.fair x
    have hnn0 := hfair.nonneg (x ++ [false])
    have hnn1 := hfair.nonneg (x ++ [true])
    rw [hmr, hmr, hmr] at hfx hadd
    have hρ0 := hrpos' (x ++ [false])
    have hρ1 := hrpos' (x ++ [true])
    have hρ := hrpos' x
    have hB := hhalf x
    have hBpos : 0 < m x := by linarith
    -- approximation errors
    have hδ : (2 : ℝ)⁻¹ ^ (x.length + 7) ≤ 1 / 4 := (hδle x.length).trans (by norm_num)
    have herr := exists_isComputablyRandom_condK_le_dup_rr_ic_ratio_err (m (x ++ [false])) (m x)
        (a x : ℝ) (bb x : ℝ) (r (x ++ [false]) : ℝ)
      (r x : ℝ) ((2 : ℝ)⁻¹ ^ (x.length + 7)) hB hnn0 hρ0 (by linarith) (by nlinarith) hδ
      (hq (x ++ [false]) (s x)) (hq x (s x))
    have hεeq : (2 : ℝ)⁻¹ ^ (x.length + 2) / 4 = 8 * (2 : ℝ)⁻¹ ^ (x.length + 7) := by
      rw [show x.length + 7 = (x.length + 2) + 5 by ring, pow_add]
      norm_num
      ring
    have hε0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (x.length + 2) := by positivity
    have hε1 : (2 : ℝ)⁻¹ ^ (x.length + 2) ≤ 1 / 4 := by
      have : (2 : ℝ)⁻¹ ^ (x.length + 2) ≤ (2 : ℝ)⁻¹ ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      refine this.trans ?_
      norm_num
    set q0 : ℝ := m (x ++ [false]) * (r (x ++ [false]) : ℝ) / (m x * (r x : ℝ)) with hq0
    set q1 : ℝ := m (x ++ [true]) * (r (x ++ [true]) : ℝ) / (m x * (r x : ℝ)) with hq1
    have hsum : q0 + q1 = 1 := by
      rw [hq0, hq1, ← add_div, ← hfx]
      exact div_self (by positivity)
    have hQcast : (Q x : ℝ) = (a x : ℝ) * (r (x ++ [false]) : ℝ) / ((bb x : ℝ) * (r x : ℝ)) := by
      simp only [Q, D]
      push_cast
      rfl
    have hQerr : |(Q x : ℝ) - q0| ≤ (2 : ℝ)⁻¹ ^ (x.length + 2) / 4 := by
      rw [hQcast, hεeq]
      exact herr
    have hP0cast : (P0 x : ℝ) = (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * (Q x : ℝ) +
        (2 : ℝ)⁻¹ ^ (x.length + 2) / 2 := by
      simp only [P0, ε]
      push_cast
      ring
    obtain ⟨hpt1, hpt2⟩ := exists_isComputablyRandom_condK_le_dup_rr_ic_pointwise q0 (Q x : ℝ) _ hε0
        hε1 hQerr
    rw [← hP0cast] at hpt1 hpt2
    cases b
    · simp only [hmr]
      exact hpt1
    · simp only [hmr]
      have : (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * q1 ≤ (((1 - P0 x : ℚ)) : ℝ) := by
        push_cast
        have h1 : q1 = 1 - q0 := by linarith
        rw [h1]
        exact hpt2
      simpa using this

/-- Step 2b of the backward proof hint of `isComputablyRandom_iff_rational`: Computability of the
recursively defined M. -/
private lemma exists_isComputablyRandom_condK_le_dup_rr_M
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (r : BitString → ℚ) (hr : Computable r) (hpos : ∀ x, 0 < r x)
    (p : BitString × Bool → ℚ) (hp : Computable p) :
    ∃ M : BitString → ℚ, Computable M ∧ M [] = 1 ∧
      ∀ x b, M (x ++ [b]) = p (x, b) * M x * r x / r (x ++ [b]) := by
  let F : BitString → ℕ × ℚ → ℚ := fun x iv =>
    p (x.take iv.1, x.getD iv.1 false) * iv.2 * r (x.take iv.1) / r (x.take (iv.1 + 1))
  let Mseq : BitString → ℕ → ℚ := fun x n => Nat.rec (motive := fun _ => ℚ) 1
                                               (fun i v => F x (i, v)) n
  have hMsucc : ∀ x n, Mseq x (n + 1) = F x (n, Mseq x n) := fun x n => rfl
  have hF : Computable₂ F := by
    have hx : Computable (fun z : BitString × (ℕ × ℚ) => z.1) := Computable.fst
    have hi : Computable (fun z : BitString × (ℕ × ℚ) => z.2.1) :=
        Computable.fst.comp Computable.snd
    have hv : Computable (fun z : BitString × (ℕ × ℚ) => z.2.2) :=
        Computable.snd.comp Computable.snd
    have ht1 : Computable (fun z : BitString × (ℕ × ℚ) => z.1.take z.2.1) :=
      Computable₂.comp Primrec.list_take.to_comp hi hx
    have ht2 : Computable (fun z : BitString × (ℕ × ℚ) => z.1.getD z.2.1 false) :=
      Computable₂.comp (f := fun (l : BitString) (n : ℕ) => l.getD n false)
        (Primrec.list_getD false).to_comp hx hi
    have ht3 : Computable (fun z : BitString × (ℕ × ℚ) => z.1.take (z.2.1 + 1)) :=
      Computable₂.comp Primrec.list_take.to_comp (Primrec.succ.to_comp.comp hi) hx
    have hp1 : Computable (fun z : BitString × (ℕ × ℚ) => p (z.1.take z.2.1, z.1.getD z.2.1 false))
        :=
      hp.comp (ht1.pair ht2)
    have hr1 : Computable (fun z : BitString × (ℕ × ℚ) => r (z.1.take z.2.1)) := hr.comp ht1
    have hr3 : Computable (fun z : BitString × (ℕ × ℚ) => r (z.1.take (z.2.1 + 1))) := hr.comp ht3
    have hnum : Computable (fun z : BitString × (ℕ × ℚ) =>
        p (z.1.take z.2.1, z.1.getD z.2.1 false) * z.2.2 * r (z.1.take z.2.1)) :=
      Computable₂.comp computable₂_ratMul (Computable₂.comp computable₂_ratMul hp1 hv) hr1
    exact exists_isComputablyRandom_condK_le_dup_rr_ic_div_pos hnum hr3 (fun z => hpos _)
  refine ⟨fun x => Mseq x x.length, ?_, rfl, ?_⟩
  · exact Computable.nat_rec (f := fun x : BitString => x.length) (g := fun _ => (1 : ℚ))
      (h := fun x iv => F x iv) Computable.list_length (Computable.const 1) hF
  · intro x b
    have hagree : ∀ n, n ≤ x.length → Mseq (x ++ [b]) n = Mseq x n := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        rw [hMsucc, hMsucc, ih (by omega)]
        simp only [F]
        have e1 : (x ++ [b]).take n = x.take n := List.take_append_of_le_length (by omega)
        have e2 : (x ++ [b]).take (n + 1) = x.take (n + 1) :=
          List.take_append_of_le_length (by omega)
        have e3 : (x ++ [b]).getD n false = x.getD n false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show n < x.length by omega)]
        rw [e1, e2, e3]
    have hlen : (x ++ [b]).length = x.length + 1 := by simp
    change Mseq (x ++ [b]) (x ++ [b]).length = p (x, b) * Mseq x x.length * r x / r (x ++ [b])
    rw [hlen, hMsucc, hagree x.length le_rfl]
    simp only [F]
    have e1 : (x ++ [b]).take x.length = x := List.take_left
    have e2 : (x ++ [b]).take (x.length + 1) = x ++ [b] := by
      rw [List.take_of_length_le (by simp)]
    have e3 : (x ++ [b]).getD x.length false = b := by
      simp [List.getD_eq_getElem?_getD]
    rw [e1, e2, e3]

/-- Step 2c of the backward proof hint of `isComputablyRandom_iff_rational`: Induction giving
fairness and M x ≥ c * m x. -/
private lemma exists_isComputablyRandom_condK_le_dup_rr_ind
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (r : BitString → ℚ) (hr : ∀ x, 0 < r x ∧ massR π x = r x)
    (m : BitString → ℝ) (hhalf : ∀ x, 1 / 2 ≤ m x)
    (p : BitString × Bool → ℚ) (hps : ∀ x, p (x, false) + p (x, true) = 1)
    (hpb : ∀ x b, (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * (m (x ++ [b]) * massR π (x ++ [b]) /
        (m x * massR π x)) ≤ (p (x, b) : ℝ))
    (M : BitString → ℚ) (hM0 : M [] = 1) (hMrec : ∀ x b, M (x ++ [b]) = p (x, b) * M x * r x /
        r (x ++ [b])) :
    IsFairCapital π (fun x => (M x : ℝ)) ∧ ∃ c : ℝ, 0 < c ∧ ∀ x, c * m x ≤ (M x : ℝ) := by
  have hmpos : ∀ x, 0 < m x := fun x => lt_of_lt_of_le (by norm_num) (hhalf x)
  have hrpos : ∀ x, (0:ℝ) < (r x : ℝ) := fun x => by exact_mod_cast (hr x).1
  have hmass : ∀ x, massR π x = (r x : ℝ) := fun x => (hr x).2
  -- the product bound
  have hP : ∀ n : ℕ, 1 / 2 + (2:ℝ)⁻¹ ^ (n + 1) ≤ ∏ i ∈ Finset.range n, (1 - (2:ℝ)⁻¹ ^ (i + 2)) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.prod_range_succ]
      have hu0 : (0:ℝ) ≤ (2:ℝ)⁻¹ ^ (n + 1) := by positivity
      have hu1 : (2:ℝ)⁻¹ ^ (n + 1) ≤ 1 / 2 := by
        rw [pow_succ]
        have : (2:ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      have hpow2 : (2:ℝ)⁻¹ ^ (n + 1 + 1) = (2:ℝ)⁻¹ ^ (n + 1) / 2 := by
        rw [pow_succ (2:ℝ)⁻¹ (n + 1)]; ring
      rw [hpow2]
      have h1 : 0 ≤ 1 - (2:ℝ)⁻¹ ^ (n + 1) / 2 := by linarith
      have := mul_le_mul_of_nonneg_right ih h1
      nlinarith
  -- the key estimate
  have key : ∀ x : BitString,
      m x / m [] * ∏ i ∈ Finset.range x.length, (1 - (2:ℝ)⁻¹ ^ (i + 2)) ≤ (M x : ℝ) := by
    intro x
    induction x using List.reverseRecOn with
    | nil =>
      simp [hM0, div_self (hmpos []).ne']
    | append_singleton x b ih =>
      have hMx : (0:ℝ) ≤ (M x : ℝ) := by
        refine le_trans ?_ ih
        refine mul_nonneg (div_nonneg (hmpos x).le (hmpos []).le) ?_
        refine Finset.prod_nonneg fun i _ => ?_
        have : (2:ℝ)⁻¹ ^ (i + 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
      have hrec : (M (x ++ [b]) : ℝ) = (p (x, b) : ℝ) * (M x : ℝ) * (r x : ℝ) / (r (x ++ [b]) : ℝ)
          := by
        rw [hMrec]; push_cast; rfl
      have hq := hpb x b
      rw [hmass, hmass] at hq
      set ε : ℝ := (2:ℝ)⁻¹ ^ (x.length + 2) with hε
      set P : ℝ := ∏ i ∈ Finset.range x.length, (1 - (2:ℝ)⁻¹ ^ (i + 2)) with hPdef
      have hlen : (x ++ [b]).length = x.length + 1 := by simp
      rw [hlen, Finset.prod_range_succ, ← hPdef, ← hε, hrec]
      have hr1 := hrpos x
      have hr2 := hrpos (x ++ [b])
      have hm1 := hmpos x
      have hm2 := hmpos (x ++ [b])
      have hm0 := hmpos []
      have hq' : (1 - ε) * (m (x ++ [b]) * (r (x ++ [b]) : ℝ) / (m x * (r x : ℝ))) ≤
          (p (x, b) : ℝ) := hq
      have hfac : 0 ≤ (M x : ℝ) * (r x : ℝ) / (r (x ++ [b]) : ℝ) := by positivity
      calc m (x ++ [b]) / m [] * (P * (1 - ε))
          = ((1 - ε) * (m (x ++ [b]) * (r (x ++ [b]) : ℝ) / (m x * (r x : ℝ)))) *
              ((m x / m [] * P) * (r x : ℝ) / (r (x ++ [b]) : ℝ)) := by
            field_simp
        _ ≤ (p (x, b) : ℝ) * (M x : ℝ) * (r x : ℝ) / (r (x ++ [b]) : ℝ) := by
            have hA : (0:ℝ) ≤ (1 - ε) * (m (x ++ [b]) * (r (x ++ [b]) : ℝ) / (m x * (r x : ℝ))) :=
                by
              have : ε ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
              have : 0 ≤ 1 - ε := by linarith
              positivity
            have hB : ((m x / m [] * P) * (r x : ℝ) / (r (x ++ [b]) : ℝ)) ≤
                (M x : ℝ) * (r x : ℝ) / (r (x ++ [b]) : ℝ) := by
              gcongr
            calc _ ≤ (p (x, b) : ℝ) * ((m x / m [] * P) * (r x : ℝ) / (r (x ++ [b]) : ℝ)) := by
                  exact mul_le_mul_of_nonneg_right hq' (by
                    have : 0 ≤ P := by
                      refine Finset.prod_nonneg fun i _ => ?_
                      have : (2:ℝ)⁻¹ ^ (i + 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
                      linarith
                    positivity)
              _ ≤ (p (x, b) : ℝ) * ((M x : ℝ) * (r x : ℝ) / (r (x ++ [b]) : ℝ)) := by
                  refine mul_le_mul_of_nonneg_left hB ?_
                  exact le_trans hA hq'
              _ = _ := by ring
  have hMpos : ∀ x, 0 < (M x : ℝ) := by
    intro x
    have h1 := key x
    have h2 : 0 < m x / m [] * ∏ i ∈ Finset.range x.length, (1 - (2:ℝ)⁻¹ ^ (i + 2)) := by
      refine mul_pos (div_pos (hmpos x) (hmpos [])) ?_
      refine lt_of_lt_of_le (by positivity) (hP x.length)
    linarith
  refine ⟨⟨fun x => (hMpos x).le, fun x => ?_⟩, 1 / (2 * m []), by have := hmpos []; positivity,
      fun x => ?_⟩
  · have hrec : ∀ b, (M (x ++ [b]) : ℝ) * (r (x ++ [b]) : ℝ) = (p (x, b) : ℝ) * (M x : ℝ) *
      (r x : ℝ) := by
      intro b
      rw [hMrec]
      have := (hrpos (x ++ [b])).ne'
      push_cast
      field_simp
    have hps' : (p (x, false) : ℝ) + (p (x, true) : ℝ) = 1 := by exact_mod_cast hps x
    simp only [hmass]
    rw [hrec false, hrec true]
    linear_combination (-(M x : ℝ) * (r x : ℝ)) * hps'
  · have h1 := key x
    have h2 := hP x.length
    have hm0 := hmpos []
    have hmx := hmpos x
    calc 1 / (2 * m []) * m x = m x / m [] * (1 / 2) := by field_simp
      _ ≤ m x / m [] * ∏ i ∈ Finset.range x.length, (1 - (2:ℝ)⁻¹ ^ (i + 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : (0:ℝ) ≤ (2:ℝ)⁻¹ ^ (x.length + 1) := by positivity
          linarith
      _ ≤ _ := h1

/-- Step 2 of the proof of `isComputablyRandom_iff_rational`: Putting it all together for
the reverse direction. -/
private lemma exists_isComputablyRandom_condK_le_dup_rr_bwd
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : ∃ r : BitString → ℚ, Computable r ∧ ∀ x, 0 < r x ∧ massR π x = r x) (w : CantorSeq)
    (hrat : ∀ m : BitString → ℚ, Computable m →
      IsFairCapital π (fun x => (m x : ℝ)) → ¬ Wins (fun x => (m x : ℝ)) w) :
    IsComputablyRandom π w := by
  intro m hfair hm
  obtain ⟨r, hrc, hrpos⟩ := hπ
  have havg := exists_isComputablyRandom_condK_le_dup_rr_avg (π := π) m hm hfair
  obtain ⟨hm'_comp, hm'_fair, hm'_half, hm'_wins⟩ := havg
  have hprop := exists_isComputablyRandom_condK_le_dup_rr_prop (π := π) ⟨r, hrc, hrpos⟩
      (fun x => (m x + 1) / 2) hm'_comp hm'_fair hm'_half
  obtain ⟨p, hp_comp, hp_rest⟩ := hprop
  have hM := exists_isComputablyRandom_condK_le_dup_rr_M (π := π) r hrc (fun x => (hrpos x).1)
      p hp_comp
  obtain ⟨M, hM_comp, hM0, hMrec⟩ := hM
  have hind := exists_isComputablyRandom_condK_le_dup_rr_ind (π := π) r hrpos
      (fun x => (m x + 1) / 2) hm'_half p (fun x => (hp_rest x).1)
      (fun x b => (hp_rest x).2 b) M hM0 hMrec
  obtain ⟨hM_fair, c, hcpos, hc_le⟩ := hind
  intro hwins
  have hm'_wins_w := hm'_wins w hwins
  have hM_wins : Wins (fun x => (M x : ℝ)) w := by
    -- if m' wins, and c * m' <= M, then M wins
    intro hb
    obtain ⟨B, hB⟩ := hb
    apply hm'_wins_w
    refine ⟨B / c, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : (M (cantorPrefix w n) : ℝ) ≤ B := hB ⟨n, rfl⟩
    have h2 : c * ((m (cantorPrefix w n) + 1) / 2) ≤ (M (cantorPrefix w n) : ℝ) :=
      hc_le (cantorPrefix w n)
    change (m (cantorPrefix w n) + 1) / 2 ≤ B / c
    rw [le_div_iff₀ hcpos]
    linarith [mul_comm c ((m (cantorPrefix w n) + 1) / 2)]
  exact hrat M hM_comp hM_fair hM_wins

/-- Private copy of `exists_isComputablyRandom_condK_le_forall` (SUV p. 282, after Problem 268),
which is declared after `exists_isComputablyRandom_condK_le` and so cannot be used by it: one
computably random sequence satisfies the bound of Problem 268 for all computable non-decreasing
unbounded `f` simultaneously, with the constant depending on `f`. -/
private theorem exists_isComputablyRandom_condK_le_dup (V : Map) (hV : isOptimalConditional V) :
    ∃ w, IsComputablyRandom uniformMeasure w ∧ ∀ f : ℕ → ℕ, Computable f → Monotone f →
      (∀ B, ∃ n, B ≤ f n) → ∃ c : ℕ, ∀ n : ℕ,
        condK V (cantorPrefix w n) (natBits n) ≤ ((f n + c : ℕ) : ℕ∞) := by
  have hfairMask : ∀ e, exists_isComputablyRandom_condK_le_dup_mask (2 * e + 1) = true →
      IsFairCapital uniformMeasure (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf
        exists_isComputablyRandom_condK_le_dup_ph e x : ℚ) : ℝ)) :=
    fun e he => ((exists_isComputablyRandom_condK_le_dup_mask_spec e).2 he).2
  refine ⟨exists_isComputablyRandom_condK_le_dup_seq
    exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph,
    ?_, ?_⟩
  · have hrat : ∃ r : BitString → ℚ, Computable r ∧ ∀ x, 0 < r x ∧ massR uniformMeasure x = r x :=
      by
      refine ⟨fun x => (1 / 2) ^ x.length, ?_, fun x => ?_⟩
      · have hpow : Computable (fun n : ℕ => 2 ^ n) :=
          Primrec.to_comp primrec_two_pow_aux
        have h_den : Computable (fun x : BitString => 2 ^ x.length) :=
            hpow.comp Computable.list_length
        have h_num : Computable (fun x : BitString => (1 : ℤ)) := Computable.const 1
        apply computable_of_num_den h_num h_den
        · intro a
          positivity
        · intro a
          dsimp
          have h1 : ((1 / 2 : ℚ) ^ a.length) = 1 / ((2 : ℚ) ^ a.length) := one_div_pow 2 a.length
          rw [h1]
          push_cast
          rfl
      · constructor
        · positivity
        · rw [massR_uniformMeasure]
          dsimp
          push_cast
          norm_num
    refine exists_isComputablyRandom_condK_le_dup_rr_bwd hrat _ ?_
    intro m hm hfair
    obtain ⟨e, he, hem⟩ :=
      exists_isComputablyRandom_condK_le_dup_cover_mart m hm hfair
    have h3 := exists_isComputablyRandom_condK_le_dup_bounded
      exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph
      hfairMask e he
    have heq : (fun x => ((exists_isComputablyRandom_condK_le_dup_evOf
        exists_isComputablyRandom_condK_le_dup_ph e x : ℚ) : ℝ)) = fun x => (m x : ℝ) := by
      funext x
      rw [hem x]
    rwa [heq] at h3
  · intro f hf hmono hunb
    obtain ⟨g, hg, hgC⟩ := exists_isComputablyRandom_condK_le_dup_decoder
    obtain ⟨C, hC⟩ := exists_isComputablyRandom_condK_le_dup_condK_le V hV g hg
    have hf2 : Computable (fun n => f n / 2) :=
      (Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp.comp hf
    have hmono2 : Monotone (fun n => f n / 2) := fun a b hab => Nat.div_le_div_right (hmono hab)
    have hunb2 : ∀ B, ∃ n, B ≤ f n / 2 := by
      intro B
      obtain ⟨n, hn⟩ := hunb (2 * B)
      exact ⟨n, by omega⟩
    obtain ⟨c, hc⟩ := exists_isComputablyRandom_condK_le_dup_schedule
      exists_isComputablyRandom_condK_le_dup_mask exists_isComputablyRandom_condK_le_dup_ph
      (fun g hg => exists_isComputablyRandom_condK_le_dup_cover_dom g hg) hf2 hmono2 hunb2
    refine ⟨2 * c + C, fun n => ?_⟩
    have h1 := hC (natBits n) (exists_isComputablyRandom_condK_le_dup_adv n) _ (hgC n)
    have hlen : (exists_isComputablyRandom_condK_le_dup_adv n).length =
        2 * exists_isComputablyRandom_condK_le_dup_K n := by
      simp [exists_isComputablyRandom_condK_le_dup_adv]
    have hK : exists_isComputablyRandom_condK_le_dup_K n ≤ f n / 2 + c := hc n
    refine h1.trans ?_
    rw [hlen]
    have h2 : 2 * exists_isComputablyRandom_condK_le_dup_K n + C ≤ f n + (2 * c + C) := by
      omega
    exact_mod_cast h2

/-- **SUV Problem 268, p. 282.**  For total computable non-decreasing unbounded `f` there is a
computably random sequence `ω` with `C(ω_0 … ω_{n-1} | n) ≤ f(n) + O(1)` for all `n`. -/
theorem exists_isComputablyRandom_condK_le {f : ℕ → ℕ} (hf : Computable f) (hmono : Monotone f)
    (hunb : ∀ B, ∃ n, B ≤ f n) (V : Map) (hV : isOptimalConditional V) :
    ∃ w, IsComputablyRandom uniformMeasure w ∧ ∃ c : ℕ, ∀ n : ℕ,
      condK V (cantorPrefix w n) (natBits n) ≤ ((f n + c : ℕ) : ℕ∞) := by
  obtain ⟨w, hw, h⟩ := exists_isComputablyRandom_condK_le_dup V hV
  exact ⟨w, hw, h f hf hmono hunb⟩

end Kolmogorov.FrequencyGames
